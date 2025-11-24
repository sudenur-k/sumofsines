#include "driverlib.h"
#include "device.h"
#include "can.h"
#include <math.h>
#include "stdio.h"
#include <string.h>


//message id defines
#define TX_MSG_OBJ_ID1 1
#define RX_MSG_OBJ_ID1 2
#define TX_MSG_OBJ_ID2 3
#define RX_MSG_OBJ_ID2 4

//motor id defines
#define MOTOR_ID1      0x01
#define MOTOR_ID2     0x02


#define CAN_BITRATE   1000000  // 1 Mbps
#define PI 3.14159265359
volatile bool printPending = false;
char debugBuf[64];

//-----------------------------------------------
// ===== Sum-of-Sines (Motor1 için KONUM profili) =====
// Frekans ve faz dizileri
static const double freqs[13] = {0.10,0.15,0.55,0.95,1.15,1.55};
static const double posPH[13] = {1.7413,0.9611,0.9909,0.5468,0.9560,0.4083};

// Toplam konum tepe genliği (|p_des| ≤ P_AMP olacak şekilde ölçekleriz)
static const float P_AMP = 3.0f;   // rad cinsinden hedef tepe. P_MAX=±12.5, bu çok güvenli.

//static const double phase[13] = {1.7304, 2.2247, 0.9139, 1.6048, 2.8053, 2.8158, 0.3945, 0.6511, 0.1617, 1.3848, 0.0939, 1.4352, 2.0393};
//static const double velPH[13] = {0.2162,2.5980,0.0991,0.2986,2.9446,2.5794,2.8213,0.0693,1.4556,0.3746,1.0430,2.9469,2.6706};
//------------------------------------------------------------

// -----------------------------------------------------------------------------
// Motor komut/ölçüm yapısı
// - p_des, v_des, kp, kd, t_ff -> gönderilecek alanlar
// - txBytes[8] -> MIT formatında paketlenmiş 8 byte
// - txWords[4] -> CAN sürücüsünün 16-bit aktarımı için 8 byte'ın 4 word'e çevrilmiş hali
// - p_meas, v_meas, tff_meas -> geri dönüşten çözülen ölçümler
// -----------------------------------------------------------------------------
//motor variables struct
typedef struct {
    float p_des;
    float v_des;
    float kp;
    float kd;
    float t_ff;
    uint8_t txBytes[8];
    uint16_t txWords[4];
    float p_meas;
    float v_meas;
    float tff_meas;

} MotorCommand_t;

//motor başlangıç değerleri atama
MotorCommand_t motor1 = {.kp=40.0f, .kd=1.0f};
MotorCommand_t motor2 = {.kd=1.0f};

//ISR ready flag
volatile bool can_cmd_ready = false;
uint16_t rxMsgData[8];
#define CONTROL_FREQ_HZ 500.0f
//bu hatlar gereksiz gibi
volatile float p_hat;
volatile float v_hat;
volatile float i_hat;



const float P_MIN = -12.5f, P_MAX = 12.5f;
const float V_MIN = -38.2f, V_MAX = 38.2f;
const float KP_MIN = 0.0f, KP_MAX = 500.0f;
const float KD_MIN = 0.0f, KD_MAX = 5.0f;
const float T_MIN = -12.0f, T_MAX = 12.0f;



//phase accumulator for sin motor1
static float theta = 0.0f;             // Faz (radyan)
const float target_freq = 2.5f;        // Hedef frekans (Hz)
const float sample_freq = 500.0f;      // ISR frekansı (Hz)
const float amplitude = 1.0f;        // Genlik

//phase accumulator for cos motor2
static float theta_f=0.0f;
const float target_freq_f=2.0f;
const float sample_freq_f=500.0f;
const float F0 = 0.055f;
const float F1=0.045f;

//yazdırma işlemi flag ve değişkenleri
volatile bool printDataReady = false;
volatile float v_des_to_print = 0.0f;
volatile float v_meas_to_print = 0.0f;
volatile float tff_des_to_print=0.0f;
volatile float tff_meas_to_print=0.0f;

//for time stamp
static volatile uint32_t time_ms = 0;
static volatile uint32_t time_ms_to_print = 0;
//yazdırma sıklığının ayarlanması
//print tick
#define PRINT_INTERVAL_MS   2u
static const uint32_t printIntervalCount = (uint32_t) (CONTROL_FREQ_HZ
        * (PRINT_INTERVAL_MS / 1000.0f));
static volatile uint32_t printTick = 0;

//feedback tick
//200ms den sonra motor1 den aldığı hızı kaydedip göndermesi icin
#define FEEDBACK_INTERVAL_MS 200u
static const uint32_t feedbackCount =(uint32_t)(CONTROL_FREQ_HZ*(FEEDBACK_INTERVAL_MS/1000.0f));
static volatile uint32_t feedbackTick=0;
volatile bool feedback_flag = false;


//interrupt can receive
volatile bool newDataAvailable = false;

//**********************************************************************************
//yazdirma flagleri
static volatile uint16_t rx_flag = 1;
static volatile uint16_t flag_yazma =3; //1 ise rx değerleri 2 ise tx değerleri


float uint_to_float(int x_int, float x_min, float x_max, int bits)
{
    float span = x_max - x_min;
    float offset = x_min;
    return ((float) x_int) * span / ((float) ((1 << bits) - 1)) + offset;
}
// Quantize a float into an unsigned integer in [0..2^bitsâ€“1]
static uint32_t float_to_uint(float x, float x_min, float x_max, uint32_t bits)
{
    float span = x_max - x_min;
    float offset = x - x_min;
    uint32_t maxInt = (1u << bits) - 1u;
    return (uint32_t) ((offset * maxInt) / span + 0.5f);

}

static void uart_print(const char *str)
{
    while (*str)
    {
        SCI_writeCharBlockingFIFO(SCIA_BASE, (uint16_t) *str++);
    }
}

// -----------------------------------------------------------------------------
// MIT Formatı: p_des(16) v_des(12) kp(12) kd(12) t_ff(12) -> 8 byte paketleme
// (Büyük uçlu bit düzeni; Mini-Cheetah protokolüne uygun)
// -----------------------------------------------------------------------------
// Pack p_des, v_des, kp, kd, t_ff into txBytes[0..7] (big-endian)
static void pack_cmd(MotorCommand_t *cmd)
{
    // Clamp (sınırla) › yapı içinden al
    float p_des = fminf(fmaxf(P_MIN,  cmd->p_des), P_MAX);
    float v_des = fminf(fmaxf(V_MIN,  cmd->v_des), V_MAX);
    float kp    = fminf(fmaxf(KP_MIN, cmd->kp),    KP_MAX);
    float kd    = fminf(fmaxf(KD_MIN, cmd->kd),    KD_MAX);  // ? Burada düzeldi
    float t_ff  = fminf(fmaxf(T_MIN,  cmd->t_ff),  T_MAX);

    // Quantize
    uint32_t p_i  = float_to_uint(p_des, P_MIN,  P_MAX, 16);
    uint32_t v_i  = float_to_uint(v_des, V_MIN,  V_MAX, 12);
    uint32_t kp_i = float_to_uint(kp,    KP_MIN, KP_MAX, 12);
    uint32_t kd_i = float_to_uint(kd,    KD_MIN, KD_MAX, 12);
    uint32_t t_i  = float_to_uint(t_ff,  T_MIN,  T_MAX, 12);

    // Byte packle
    cmd->txBytes[0] = (p_i >> 8);
    cmd->txBytes[1] =  p_i       & 0xFF;
    cmd->txBytes[2] = (v_i >> 4);
    cmd->txBytes[3] = ((v_i & 0xF) << 4) | ((kp_i >> 8));
    cmd->txBytes[4] =  kp_i      & 0xFF;
    cmd->txBytes[5] = (kd_i >> 4);
    cmd->txBytes[6] = ((kd_i & 0xF) << 4) | ((t_i >> 8));
    cmd->txBytes[7] =  t_i       & 0xFF;
}
// -----------------------------------------------------------------------------
// Cihazdan gelen 8 byte cevabı çözme (v_meas ve tff_meas çıkarılıyor)
// DİKKAT: rxMsgData 16-bit kelimeler içerir; burada sadece alt 8 bit alınıyor.
// Eğer üst 8 bitlerde anlamlı veri varsa bu yaklaşım yeterli olmayabilir.
//datasheetden farkli eylulun yaaklasimi
// -----------------------------------------------------------------------------
void unpack_reply(uint16_t *rxMsgData)
{
    // 4x16bit word'den 8 byte'Ä± Ã§Ä±kar
    uint8_t b[8];
    b[0] = rxMsgData[0];
    b[1] = rxMsgData[1];
    b[2] = rxMsgData[2];
    b[3] = rxMsgData[3];
    b[4] = rxMsgData[4];
    b[5] = rxMsgData[5];
    b[6] = rxMsgData[6];
    b[7] = rxMsgData[7];


    //bu kısımda float olarak bastırmak icin eklemistim eylul hex olarak
    //bastiriyordu
    //bastirmak istedigim veriye gore degisiklik yapiyorum
    // Hız (12 bit › float): b[3] + üst 4 bit b[4]
    int v_int = (b[3] << 4) | (b[4] >> 4);
    motor1.v_meas = uint_to_float(v_int, V_MIN, V_MAX, 12);
    // Akım (12 bit › float): alt 4 bit b[4] + b[5]
    int tff_int = ((b[4] & 0xF) << 8) | b[5];
    motor1.tff_meas = uint_to_float(tff_int, T_MIN, T_MAX, 12);

}

// -----------------------------------------------------------------------------
// 8 byte'ı 4 adet 16-bit kelimeye çevir (CAN_sendMessage_16bit için)
// -----------------------------------------------------------------------------
// Convert 8 bytes in txBytes to four 16-bit words for CAN_sendMessage_16bit
static void prepare_txWords(MotorCommand_t *cmd)
{
    int idx;
    for(idx = 0; idx < 4; idx++)
    {
        cmd->txWords[idx] = (uint16_t)cmd->txBytes[2*idx] |
                ((uint16_t)cmd->txBytes[2*idx+1] << 8);
    }
}

// -----------------------------------------------------------------------------
// MIT enable sekansı: 0xFF..0xFC dizisini 5 kez 1 ms arayla gönder
// Motor kontrolcüyü MIT moduna alır
// -----------------------------------------------------------------------------
// Send MIT-enable sequence (0xFF…0xFC) five times at 1 ms intervals
static void send_mit_enable(uint16_t tx_obj_id)
{
    int i;
    uint8_t  enB[8] = {0xFF,0xFF,0xFF,0xFF, 0xFF,0xFF,0xFF,0xFC};
    uint16_t enW[4];

    for(i = 0; i < 4; i++)
        enW[i] = (uint16_t)enB[2*i] | ((uint16_t)enB[2*i+1] << 8);
    for(i = 0; i < 5; i++)
    {
        CAN_sendMessage_16bit(CANB_BASE, tx_obj_id, 8, enW);
        DEVICE_DELAY_US(1000);
    }
}

// Timer0 ISR: send control + MIT-enable every 2 ms
// Sadece flag setler!
__interrupt void cpuTimer0ISR(void)
{

    CPUTimer_clearOverflowFlag(CPUTIMER0_BASE);

    //sum of sines
    time_ms += 2;
    float t = (float)time_ms * 1e-3f;
    float t_sum = 0.0f;

    int i;
    for ( i = 0; i < 13; i++)
    {
        float omega = 2.0f * PI * (float)freqs[i];
        float ang   = omega * t + (float)posPH[i];
        float s = sinf(ang);

        t_sum += s/omega;

    }
    float scale = P_AMP / 13.0f;

    motor1.t_ff  =  2*t_sum;
//    //motor1 sin vermek icin phase accumulator
//    time_ms += 2;
//    theta += 2.0f * PI * (target_freq / sample_freq);
//    if (theta >= 2.0f * PI)
//    {
//        theta -= 2.0f * PI;
//    }
//    //motor1 tork
//
//    motor1.t_ff = 2+(amplitude * sinf(theta));

    //motor 2 cos hazirligi
    //feedback
    theta_f += 2.0f* PI* (target_freq_f/sample_freq_f);
    if(theta_f>= 2.0f*PI)
    {
        theta_f -= 2.0f* PI;
    }
    //200ms den sonra gondermeye basliyor
    if(++feedbackTick>=feedbackCount)
    {
        feedback_flag = true;
        motor2.t_ff=-(F0+F1*cosf(theta_f))*motor1.v_meas;
        pack_cmd(&motor2);
        prepare_txWords(&motor2);

    }

    pack_cmd(&motor1);
    prepare_txWords(&motor1);

    can_cmd_ready = true;

    //veri bastirmak icin atamalarin yapildigi bolum 20ms de bir bastırıyor
    if (++printTick >= printIntervalCount)
    {
        printTick = 0;
        v_des_to_print = motor1.v_des;
        v_meas_to_print= motor1.v_meas;
        tff_des_to_print=motor1.t_ff;
        tff_meas_to_print=motor1.tff_meas;
        time_ms_to_print = time_ms;
        printDataReady = true;
    }

    Interrupt_clearACKGroup(INTERRUPT_ACK_GROUP1);

}

// Configure GPIO: LED1 + CAN-B pins
static void initGPIO(void)
{

    // CAN-B TX (GPIO12)
    GPIO_setPinConfig(GPIO_12_CANTXB);
    GPIO_setPadConfig(12, GPIO_PIN_TYPE_STD);
    GPIO_setQualificationMode(12, GPIO_QUAL_ASYNC);

    // CAN-B RX (GPIO17)
    GPIO_setPinConfig(GPIO_17_CANRXB);
    GPIO_setPadConfig(17, GPIO_PIN_TYPE_PULLUP);
    GPIO_setQualificationMode(17, GPIO_QUAL_ASYNC);
}
// -----------------------------------------------------------------------------
// CAN modül başlatma (1 Mbps) ve mesaj objeleri
// - TX_MSG_OBJ_ID1 -> MOTOR_ID1'e gönderim
// - TX_MSG_OBJ_ID2 -> MOTOR_ID2'ye gönderim
// - RX_MSG_OBJ_ID2 -> MOTOR_ID2'den geri dönüş almak için RXTX_REMOTE
// NOT: RX_MSG_OBJ_ID1 yorum satırına alınmış durumda cunku ikisinden de ayni anda alamiyorum veri
//actigimda serial portta herhangi bir sey okuyamıyorum
// -----------------------------------------------------------------------------
// Initialize CAN module at 1 Mbps, ID=0x01, DLC=8
static void initCAN(void)
{
    CAN_initModule(CANB_BASE);
    CAN_setBitRate(CANB_BASE, DEVICE_SYSCLK_FREQ, CAN_BITRATE, 10);
    //motor1 tx ve rx object
    CAN_setupMessageObject(
    CANB_BASE,
                           TX_MSG_OBJ_ID1,
                           MOTOR_ID1,
                           CAN_MSG_FRAME_STD, CAN_MSG_OBJ_TYPE_TX, 0, // no mask
                           CAN_MSG_OBJ_NO_FLAGS, 8                  // DLC = 8
                           );

    CAN_setupMessageObject(
    CANB_BASE,
                           RX_MSG_OBJ_ID1,
                           MOTOR_ID1,
                           CAN_MSG_FRAME_STD, CAN_MSG_OBJ_TYPE_RXTX_REMOTE, 0, // no mask
                           CAN_MSG_OBJ_NO_FLAGS, 8                  // DLC = 8
                           );
    //motor2 tx ve rx object
        CAN_setupMessageObject(
                CANB_BASE,
                TX_MSG_OBJ_ID2,
                MOTOR_ID2,
                CAN_MSG_FRAME_STD,
                CAN_MSG_OBJ_TYPE_TX,
                0, CAN_MSG_OBJ_NO_FLAGS, 8
        );

//        CAN_setupMessageObject(
//                CANB_BASE,
//                RX_MSG_OBJ_ID2,
//                MOTOR_ID2,
//                CAN_MSG_FRAME_STD,
//                CAN_MSG_OBJ_TYPE_RXTX_REMOTE,
//                0, CAN_MSG_OBJ_NO_FLAGS, 8
//        );


    // For loop-back testing; remove for real motor connection
    //CAN_enableTestMode(CANB_BASE, CAN_TEST_LBACK);
    CAN_startModule(CANB_BASE);
}

// Initialize CPU Timer0 for 500 Hz interrupts
static void initTimer(void)
{
    CPUTimer_setPeriod(CPUTIMER0_BASE, DEVICE_SYSCLK_FREQ / 500);
    CPUTimer_setPreScaler(CPUTIMER0_BASE, 0);
    CPUTimer_reloadTimerCounter(CPUTIMER0_BASE);
    CPUTimer_enableInterrupt(CPUTIMER0_BASE);
    CPUTimer_startTimer(CPUTIMER0_BASE);
}

// Setup interrupts
static void initInterrupts(void)
{
    Interrupt_initModule();
    Interrupt_initVectorTable();
    Interrupt_register(INT_TIMER0, &cpuTimer0ISR);
    Interrupt_enable(INT_TIMER0);

    EINT;
    ERTM;
}

static void initSCI(void)
{
    //TX
    GPIO_setMasterCore(DEVICE_GPIO_PIN_SCITXDA, GPIO_CORE_CPU1);
    GPIO_setPinConfig(DEVICE_GPIO_CFG_SCITXDA);
    GPIO_setDirectionMode(DEVICE_GPIO_PIN_SCITXDA, GPIO_DIR_MODE_OUT);
    GPIO_setPadConfig(DEVICE_GPIO_PIN_SCITXDA, GPIO_PIN_TYPE_STD);
    GPIO_setQualificationMode(DEVICE_GPIO_PIN_SCITXDA, GPIO_QUAL_ASYNC);

    SCI_performSoftwareReset(SCIA_BASE);
    SCI_setConfig(SCIA_BASE, DEVICE_LSPCLK_FREQ, 115200, (SCI_CONFIG_WLEN_8 |
    SCI_CONFIG_STOP_ONE | SCI_CONFIG_PAR_NONE));
    SCI_resetChannels(SCIA_BASE);
    SCI_resetTxFIFO(SCIA_BASE);
    SCI_clearInterruptStatus(SCIA_BASE, SCI_INT_TXFF);
    SCI_enableFIFO(SCIA_BASE);
    SCI_enableModule(SCIA_BASE);
    SCI_performSoftwareReset(SCIA_BASE);
}
//yazdirma fonk
void data_print(void)
{
    if (printDataReady)
    {
        printDataReady = false; // Bayrağı indir
        if (flag_yazma == 1)
        {
            //rx verilerinin yazdırılması
            char buffer[64];
            float val = motor2.v_meas;
            int sign = (val < 0.0f) ? -1 : 1;
            val = fabsf(val);
            int whole = (int) val;
            int frac = (int) ((val - whole) * 1000 + 0.5f);  // round to nearest
            snprintf(buffer, sizeof(buffer), "%lu,%s%d.%03d\r\n",
                     (unsigned long) time_ms_to_print, (sign < 0) ? "-" : "",
                     whole, frac);
            uart_print(buffer);
        }
        if (flag_yazma == 2)
        {
            //tx datalarinin direkt olarak bastirilmasi
            char buffer[64];
            float val = motor1.t_ff;//v_des;
            int sign = (val < 0.0f) ? -1 : 1;
            val = fabsf(val);
            int whole = (int) val;
            int frac = (int) ((val - whole) * 1000 + 0.5f);  // round to nearest
            snprintf(buffer, sizeof(buffer), " %lu,%s%d.%03d\r\n",
                     (unsigned long) time_ms_to_print, (sign < 0) ? "-" : "",
                     whole, frac);
            uart_print(buffer);
        }
        if (flag_yazma==3)
        {
            //rx tx verilerinin aynı anda yazdırılması
            char buffer[64];
            //****************TX*******************
            //t_ff tx verisinin negatifse ayarlanmasi
            //motor1 e gönderilen tork
            float val_tff=tff_des_to_print;
            //işareti ayrı bir şekilde saklamak için
            int sign_tff=(val_tff<0.0f)? -1:1;
            val_tff=fabs(val_tff);
            int whole_tff=(int)val_tff;
            int frac_tff=(int)((val_tff-whole_tff)*1000 + 0.5f);
            //bu şekilde buffer a kaydederken whole ve frac kısımlarını ayrı ayrı buffer a
            //yazdırıyor
            //*****************RX*******************
            //motor2 den ölçülen hız
            float val_vmeas=v_meas_to_print;
            int sign_vmeas=(val_vmeas<0.0f)? -1:1;
            val_vmeas=fabs(val_vmeas);
            int whole_vmeas=(int)val_vmeas;
            int frac_vmeas=(int)((val_vmeas-whole_vmeas)*1000 + 0.5f);
            //*************format********************
            //<time_ms_print,sign_tff/whole_tff.frac_tff,sign_vmeas/whole_vmeas.frac_vmeas>
            //time,tx,rx
            snprintf(buffer, sizeof(buffer), "%lu,%s%d.%03d,%s%d.%03d\r\n",
                     (unsigned long)time_ms_to_print,(sign_tff<0) ? "-": " ",whole_tff,frac_tff,(sign_vmeas<0) ? "-":" ",whole_vmeas,frac_vmeas);
            uart_print(buffer);



        }
    }
}
// -----------------------------------------------------------------------------
// main: Donanım başlatmaları, MIT enable, ana döngü
// - ISR "can_cmd_ready" dediğinde burada CAN gönderimleri yapılır
// - feedback_flag true ise motor2 komutu da yollanır
// - RX mesajı okunur ve ölçümler çözümlenir
// - data_print() ile seri loglama yapılır
// -----------------------------------------------------------------------------
void main(void)
{
    Device_init();
    Device_initGPIO();
    initSCI();
    uart_print("Hello\r\n");  // init’ten hemen sonra bir kere deneyin
    initGPIO();
    initCAN();
    initTimer();
    initInterrupts();
    send_mit_enable(TX_MSG_OBJ_ID1);
    send_mit_enable(TX_MSG_OBJ_ID2);

    uart_print("\r\nMAIN START!\r\n");



    while (1)
    {
        if (can_cmd_ready)
        {
            //motor1 komutu
            CAN_sendMessage_16bit(CANB_BASE, TX_MSG_OBJ_ID1, 8, motor1.txWords);

            //200ms nin ardindan motor2 komutu gonderilmesi
            if(feedback_flag)
            {
                CAN_sendMessage_16bit(CANB_BASE, TX_MSG_OBJ_ID2, 8, motor2.txWords);
            }
            //motor2 den veri okunması
            //veri okumasinin hangi motordan olucagian gore msg object
            //degistiryorum ve okunmayacak verinin msg objectini yorum satirina alıyorum
            CAN_readMessage(CANB_BASE, RX_MSG_OBJ_ID1, rxMsgData);
            unpack_reply(rxMsgData);
            can_cmd_ready = false;

        }

        data_print();

    }
}
