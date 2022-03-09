/***************************************************************************//**
 * @file
 * @brief Core application logic.
 *******************************************************************************
 * # License
 * <b>Copyright 2020 Silicon Laboratories Inc. www.silabs.com</b>
 *******************************************************************************
 *
 * SPDX-License-Identifier: Zlib
 *
 * The licensor of this software is Silicon Laboratories Inc.
 *
 * This software is provided 'as-is', without any express or implied
 * warranty. In no event will the authors be held liable for any damages
 * arising from the use of this software.
 *
 * Permission is granted to anyone to use this software for any purpose,
 * including commercial applications, and to alter it and redistribute it
 * freely, subject to the following restrictions:
 *
 * 1. The origin of this software must not be misrepresented; you must not
 *    claim that you wrote the original software. If you use this software
 *    in a product, an acknowledgment in the product documentation would be
 *    appreciated but is not required.
 * 2. Altered source versions must be plainly marked as such, and must not be
 *    misrepresented as being the original software.
 * 3. This notice may not be removed or altered from any source distribution.
 *
 ******************************************************************************/
#include "em_common.h"
#include "app_assert.h"
#include "sl_bluetooth.h"
#include "gatt_db.h"
#include "app.h"
#include "app_log.h"
#include "em_gpio.h"
#include "em_prs.h"
#include "em_wdog.h"
#include "em_iadc.h"
#include "em_cmu.h"
#include "em_letimer.h"
#include "sl_power_manager.h"
#include "sl_sleeptimer.h"
#include "em_rmu.h"
#include "em_chip.h"
#include "em_usart.h"
#include "em_device.h"
#include "sleep.h"
#include "sl_bt_api.h"

#define D_HOLSTER_ARMOR   1 //0:TB-03, 1:HS-01, 2:AS-01

#if D_HOLSTER_ARMOR == 0
#define D_TB03 1
#elif D_HOLSTER_ARMOR == 1
  #define D_WDOG    1
  #define D_LETIMER 1
  #define D_PRS     1
#else D_HOLSTER_ARMOR == 2
  #define D_WDOG    0
  #define D_LETIMER 0
  #define D_PRS     0
#endif

//command list
uint8_t CmdGetPSData[10]  = "GET PSDATA";
uint8_t CmdSetPSData[10]  = "SET PSDATA";
uint8_t CmdGetSYSSN[9]    = "GET SYSSN";
uint8_t CmdSetSYSSN[9]    = "SET SYSSN";
uint8_t CmdGetMAC[7]      = "GET MAC";
uint8_t CmdGetGPI[7]      = "GET GPI";
uint8_t CmdSetGPO[7]      = "SET GPO";
uint8_t CmdTestModeOn[9]  = "SET TSMON";
uint8_t CmdTestModeOff[10]= "SET TSMOFF";
uint8_t CmdSetPSOffset[12]= "SET PSOFFSET";
uint8_t CmdSetUARTOff[11]= "SET UARTOFF";
uint8_t CmdGetUARTOff[11]= "GET UARTOFF";
uint8_t bFindHeader = 0;
uint8_t HeaderOffset = 0;
uint8_t bFindTailer = 0;
uint8_t TailerOffset = 0;
uint8_t bFindKeyChar = 0;
uint8_t KeyCharOffset = 0;
uint8_t bCmdMatch = 0;
uint8_t Index = 0;
uint8_t cmd_buffer[80], CmdStr[80], nvm_write[80];
bool boot = true;

/*#define gpin_7_for_pb3 0x80
#define gpin_6_for_pb2 0x40
#define gpin_5_for_pa8 0x20
#define gpin_4_for_pb0 0x10
#define gpin_3_for_pa7 0x08
#define gpin_2_for_pd2 0x04
#define gpin_1_for_pc1 0x02
#define gpin_0_for_pc0 0x01*/

#define gpin_0_for_pb3 0x01
#define gpin_1_for_pc4 0x02
#define gpin_2_for_pc6 0x04
#define gpin_3_for_pa7 0x08
#define gpin_4_for_pa8 0x10
#define gpin_5_for_pb0 0x20
#define gpin_6_for_pb2 0x40
#define gpin_7_for_pc1 0x80


//========= ADC =========
#define adcFreq   16000000
//static volatile int32_t sample;
//static volatile double singleResult; // Volts
// Raw IADC conversion result
static volatile IADC_Result_t sample;

// Result converted to volts
static volatile double singleResult;

volatile uint16_t millivolts, battvolts;
bool battery_full = false, configured = false;
//volatile uint8_t _ADC_CH=adcPosSelAPORT3YCH27;
volatile uint32_t ADC_CHN = (0xFF<<8);
//=======================

#define second 32768
#define milliseconds 328
uint8_t local_name_index = 1;
uint8_t GPIN4_HL_CNT = 0;
uint32_t read_current_gpin = 0;

uint8_t trigger_duration_is_on = 0;
uint8_t stop_BWCB2_is_on = 0;

uint8_t DSCADVDATA[32];
uint8_t B2_MAC_Addr[6];
uint8_t* advdata;
uint8array data;
bd_addr bwc_address;
uint32_t B2G_DeviceListInx = 0,B3G_DeviceListInx = 0;

uint8_t sleep_mode = 0, GPIN_wakeup = 0, coin_battery = 0;

uint8_t sniffer_mesh = 0x00;
#define sniffer_enable 0x01
uint16_t transmit_duration_buf = 0x001e;// default 30s transmit duration
uint8_t trig_delay_buf = 0x00;          // default trig delay
uint8_t gpin_andop_pins_buf = 0x60;     // default AND PIN are pin5,pin6
uint8_t gpin_stopcmd_pins_buf = 0x80;   // default STOP PIN is pin7
uint32_t B2NonRecCount = 0,B3NonRecCount = 0;
uint32_t PD2_ADC_Value, PA6_ADC_Value, PC6_ADC_Value;
uint8_t user_read_response_buf[10] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
uint8_t txpower_buf[2] = {0xFF, 0xDD};
int txpower = 0;
//const uint8_t * nvm_write;
size_t *  read_len;
sl_status_t ret;

uint8_t B2G_Device00[10] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
uint8_t B2G_Device01[10] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
uint8_t B2G_Device02[10] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
uint8_t B2G_Device03[10] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
uint8_t B2G_Device04[10] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
uint8_t B2G_Device05[10] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};

uint8_t B3G_Device[6][10] = {{0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00},
                       {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00},
               {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00},
               {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00},
               {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00},
               {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00}};


uint8_t groupName01[6] = {0x47, 0x65, 0x74, 0x61, 0x63, 0x31};//Getac1
uint8_t groupName02[6] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00};//
uint8_t groupName03[6] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00};//
uint8_t groupName04[6] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00};//
uint8_t groupName05[6] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00};//
uint8_t defaultgroupName[6] = {0x00, 0x00, 0x00, 0x00, 0x00, 0x00};//default empty
uint8_t b2_trigcmd[4] = {0x54, 0x72, 0x69, 0x67};// Trig
uint8_t b2_stopcmd[4] = {0x53, 0x74, 0x6F, 0x70};// Stop
uint8_t b2_mutecmd[4] = {0x4D, 0x75, 0x74, 0x65};// Mute
uint8_t b2_audiocmd[4] = {0x41, 0x75, 0x64, 0x69};// Audi
uint8_t b3_trigcmd[2] = {0x21, 0x00};// Trig /bit4-7 0010/bit0-3 0001
uint8_t b3_stopcmd[2] = {0x11, 0x00};// Stop /bit4-7 0001/bit0-3 0001

uint8_t cmd_buffer_len = 0, CmdLen = 0;
uint8_t test_mode = 0, plugout = 0, starttrig = 0, dcin = 0;
uint32_t  BTN_TIMER_CNT = 0;
uint8_t BWC_Ver = 2;

uint8_t b2_pkt_len, b3_pkt_len;
uint8_t pcsniffer_pkt_len;
uint8_t *pData;
sl_status_t sc;

int16_t *   set_power, set_min, set_max;

typedef struct {
    uint8_t flagsLen;     /* Length of the Flags field. */
    uint8_t flagsType;    /* Type of the Flags field. */
    uint8_t flags;        /* Flags field. */
    uint8_t groupLen;     /* Group name length */
    uint8_t groupType;    /* Group name type */
    uint8_t groupName[6]; /* Group name */
    uint8_t mandataLen;   /* Length of the Manufacturer Data field. */
    uint8_t mandataType;  /* Type of the Manufacturer Data field. */
    uint8_t compId[2];    /* Company ID field. */
    uint8_t reserved[12];
    uint8_t cmd[4];
  } AdvData;

AdvData bwcb2AdvData = {
    /* Flag bits - See Bluetooth 4.0 Core Specification , Volume 3, Appendix C, 18.1 for more details on flags. */
    2,        /* length  */
    0x01,     /* type */
    0x04 | 0x02,  /* Flags: LE General Discoverable Mode, BR/EDR is disabled. */
    0x7,      /* Group name length */
    0x9,      /* Group name type */
    {0x61, 0x61, 0x72, 0x6f, 0x6e, 0x00},//aaron
    0x13,     /* Length of the Manufacturer Data field. */
    0xFF,     /* Type of the Manufacturer Data field. */
    {0xFF, 0x02}, /* Company ID field. */
    {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00},
    {0x54, 0x72, 0x69, 0x67}// Trig
  };

typedef struct {
    uint8_t flagsLen;        /* Length of the Flags field. */
    uint8_t flagsType;       /* Type of the Flags field. */
    uint8_t flags;           /* Flags field. */
    uint8_t groupLen;        /* Group name length */
    uint8_t groupType;       /* Group name type */
    //uint8_t PackageVer[2];   /* Package Version */
    uint8_t groupName[6];    /* Group name */
    uint8_t mandataLen;      /* Length of the Manufacturer Data field. */
    uint8_t mandataType;     /* Type of the Manufacturer Data field. */
    uint8_t compId[2];       /* Company ID field. */
    uint8_t SourceType;      /* Source type. */
    uint8_t SourceID[2];     /* Source ID. */
    uint8_t DestinationID[2];/* Destination ID. */
    uint8_t UserID[2];       /* User ID. */
    uint8_t DevicStatus[2];  /* Device status. */
    uint8_t EventStatus[2];  /* Event status. */
    uint8_t TimeStamp[5];    /* Time stamp. */
  } AdvData2;

  // The advertising set handle allocated from Bluetooth stack.
  static uint8_t advertising_set_handle = 0xff;
  void set_non_connectable_b2_packet(void)
  {
      b2_pkt_len = sizeof(bwcb2AdvData);
      pData = (uint8_t*)(&bwcb2AdvData);

      /* Set 0 dBm Transmit Power */
      //gecko_cmd_system_set_tx_power(0);

      /* Set custom advertising data */
      sl_bt_advertiser_set_data(advertising_set_handle, 0, b2_pkt_len, pData);

      // Set advertising interval to 100ms.
      sc = sl_bt_advertiser_set_timing(
        advertising_set_handle,
        160, // min. adv. interval (milliseconds * 1.6)
        160, // max. adv. interval (milliseconds * 1.6)
        0,   // adv. duration
        0);  // max. num. adv. events
      app_assert_status(sc);
      // Start general advertising and enable connections.
      sc = sl_bt_advertiser_start(
        advertising_set_handle,
        sl_bt_advertiser_user_data,
        sl_bt_advertiser_scannable_non_connectable);
      app_assert_status(sc);
  }

AdvData2 bwcb3AdvData = {
    /* Flag bits - See Bluetooth 4.0 Core Specification , Volume 3, Appendix C, 18.1 for more details on flags. */
    2,        /* length  */
    0x01,     /* type */
    0x04 | 0x02,  /* Flags: LE General Discoverable Mode, BR/EDR is disabled. */
    0x7,      /* Group name length */
    0x9,      /* Group name type */
    {0x61, 0x61, 0x72, 0x6f, 0x6e, 0x00},//aaron
    //{0x01, 0x01},/* Package Version, Ver 2.0 */
    //{0x41, 0x4B, 0x43, 0x30},//AKC0
    0x13,     /* Length of the Manufacturer Data field. */
    0xFF,     /* Type of the Manufacturer Data field. */
    {0xFF, 0x02}, /* Company ID field. */
    0x20,   /* Source type, Holster */
    {0x03, 0x31}, /* Source ID. */ /* Bit16:Package Version, Ver 3.0 */
    {0x00, 0x32}, /* Destination ID. */
    {0x00, 0x00}, /* User ID. */
    {0x00, 0x00}, /* Device status. */
    {0x31, 0x31}, /* Event status, Trig */
    {0x00, 0x00, 0x00, 0x00, 0x00}/* Time stamp. */
  };

void set_non_connectable_b3_packet(void)
{
    b3_pkt_len = sizeof(bwcb3AdvData);
    pData = (uint8_t*)(&bwcb3AdvData);

    /* Set 0 dBm Transmit Power */
    //gecko_cmd_system_set_tx_power(0);

    /* Set custom advertising data */
    sl_bt_advertiser_set_data(advertising_set_handle, 0, b3_pkt_len, pData);

    // Set advertising interval to 100ms.
    sc = sl_bt_advertiser_set_timing(
      advertising_set_handle,
      160, // min. adv. interval (milliseconds * 1.6)
      160, // max. adv. interval (milliseconds * 1.6)
      0,   // adv. duration
      0);  // max. num. adv. events
    app_assert_status(sc);
    // Start general advertising and enable connections.
    sc = sl_bt_advertiser_start(
      advertising_set_handle,
      sl_bt_advertiser_user_data,
      sl_bt_advertiser_scannable_non_connectable);
    app_assert_status(sc);
}

void read_gpin_high_low_status()
{
  read_current_gpin = 0;

  //read gpio value gpin_3_for_pa7, gpin_4_for_pa8
  read_current_gpin = (read_current_gpin | (GPIO_PortInGet(gpioPortA)&0x0180)>>4);
  //printf("(GPIO_PortInGet(gpioPortA)&0x0180)>>4 = %X\r\n",(GPIO_PortInGet(gpioPortA)&0x0180)>>4);

  //read gpio value gpin_0_for_pb3, gpin_5_for_pb0, gpin_6_for_pb2
  read_current_gpin = (read_current_gpin | (GPIO_PortInGet(gpioPortB)&0x0008)>>3);
  read_current_gpin = (read_current_gpin | (GPIO_PortInGet(gpioPortB)&0x0001)<<5);
  read_current_gpin = (read_current_gpin | (GPIO_PortInGet(gpioPortB)&0x0004)<<4);
  //printf("(GPIO_PortInGet(gpioPortB)&0x0008)>>3 = %X\r\n",(GPIO_PortInGet(gpioPortB)&0x0008)>>3);
  //printf("(GPIO_PortInGet(gpioPortB)&0x0001)<<5 = %X\r\n",(GPIO_PortInGet(gpioPortB)&0x0001)<<5 );
  //printf("(GPIO_PortInGet(gpioPortB)&0x0004)<<4 = %X\r\n",(GPIO_PortInGet(gpioPortB)&0x0004)<<4 );

  //read gpio value gpin_1_for_pc4, gpin_2_for_pc6, gpin_7_for_pc1
  read_current_gpin = (read_current_gpin | (GPIO_PortInGet(gpioPortC)&0x0010)>>3);
  read_current_gpin = (read_current_gpin | (GPIO_PortInGet(gpioPortC)&0x0040)>>4);
  read_current_gpin = (read_current_gpin | (GPIO_PortInGet(gpioPortC)&0x0002)<<6);
  //printf("(GPIO_PortInGet(gpioPortC)&0x0001)<<1 = %X\r\n",(GPIO_PortInGet(gpioPortC)&0x0001)<<1);
  //printf("(GPIO_PortInGet(gpioPortC)&0x0002)<<6 = %X\r\n",(GPIO_PortInGet(gpioPortC)&0x0002)<<6);

    read_current_gpin = read_current_gpin ^ 0xFF;
  printf("read_current_gpin = %X\r\n",read_current_gpin);
}

void trigger_BWCS()
{
  //start advertising
  if(boot)
  {
      //**** do nothing when first time at boot ****//

      //stop advertising, default duration is 30sec
      sl_bt_system_set_soft_timer(second,13,1);
      sl_bt_system_set_soft_timer(2*second,3,1);

      starttrig = 1;
  }
  else
  {
      sl_bt_system_set_soft_timer(1*second,8,0);

      //blink led
      //sl_bt_system_set_soft_timer(1*second,9,0);
      red_led_on(1);

      //stop advertising, default duration is 30sec
      sl_bt_system_set_soft_timer(transmit_duration_buf*second,13,1);
      sl_bt_system_set_soft_timer((transmit_duration_buf+1)*second,3,1);

      starttrig = 1;
  }
}

void HS01_trigger_BWCS()
{
  printf("**** HS01_trigger_BWCS ****\r\n");
  if(boot)
  {
      local_name_index = 1;
      //remove_stopcmd_timer();

      //call advertising_trigcmd_to_BWCB2()
      //default broadcast duration is 30sec
      sl_bt_system_set_soft_timer(second,4,1);


      //set trigger identification flag = 1
      trigger_duration_is_on = 1;
      stop_BWCB2_is_on = 0;
  }
  else
  {
      local_name_index = 1;
      //remove_stopcmd_timer();

      //red led on
      //red_led_on(1);

      //drive the PC2 to High
      //GPIO_PortOutSet(gpioPortC, 0x0004);

      //call advertising_trigcmd_to_BWCB2()
      //default broadcast duration is 30sec
      sl_bt_system_set_soft_timer(second*transmit_duration_buf,4,1);


      //set trigger identification flag = 1
      trigger_duration_is_on = 1;
      stop_BWCB2_is_on = 0;

      //repeat timer #2 for group local name 1~5
      sl_bt_system_set_soft_timer(1*second,2,0);
   }
}

void TB03_trigger_BWCS()
{
  printf("**** TB03_trigger_BWCS ****\r\n");
  local_name_index = 1;
  //remove_stopcmd_timer();

  //red led on
  red_led_on(1);

  //drive the PC2 to High
  GPIO_PortOutSet(gpioPortC, 0x0004);

  //call advertising_trigcmd_to_BWCB2()
  //default broadcast duration is 30sec
  sl_bt_system_set_soft_timer(second*transmit_duration_buf,4,1);


  //set trigger identification flag = 1
  trigger_duration_is_on = 1;
  stop_BWCB2_is_on = 0;

  //repeat timer #2 for group local name 1~5
  sl_bt_system_set_soft_timer(1*second,2,0);
}

void stop_BWCB2()
{
  local_name_index = 1;
  remove_triggercmd_timer();

  //red led on
  red_led_on(1);

  //drive the PC2 to Low
  GPIO_PortOutClear(gpioPortC, 0x0004);

  //repeat timer #3 for group local name 1~5
  sl_bt_system_set_soft_timer(1*second,3,0);
  //call advertising_stopcmd_to_BWCB2()
  //fix the transmit_duration_buf bug in sleep mode
  if(sleep_mode == 1)
  {sl_bt_system_set_soft_timer(second*(transmit_duration_buf+4),6,1);}
  else
  //default broadcast duration is 30sec
  {sl_bt_system_set_soft_timer(second*transmit_duration_buf,6,1);}

  //set trigger identification flag = 1
  trigger_duration_is_on = 1;
  stop_BWCB2_is_on = 1;
}

void Suspend_GPIN()
{
  //disable all interrupt but ignition
  GPIO_IntConfig(gpioPortB,  3, false, false, false);      // GPIN0, fallingEdge, default trig
  GPIO_IntConfig(gpioPortC,  4, false, false, false);      // GPIN1, fallingEdge, default trig
  GPIO_IntConfig(gpioPortC,  6, false, false, false);      // GPIN2, fallingEdge, default trig
  GPIO_IntConfig(gpioPortA,  7, false, false, false);      // GPIN3, fallingEdge, default trig
  GPIO_IntConfig(gpioPortA,  8, false, false, false);      // GPIN4, fallingEdge, default trig
  GPIO_IntConfig(gpioPortB,  0, false, false, false);      // GPIN5, fallingEdge, default trig
  GPIO_IntConfig(gpioPortB,  2, false, false, false);      // GPIN6, fallingEdge, default trig
  GPIO_IntConfig(gpioPortC,  1, false, false, false);      // GPIN7, fallingEdge, default trig

  /* Configure PB1 as output, default OUT=0 green led on */
  GPIO_PinModeSet(gpioPortB, 1, gpioModePushPull, 0);
  /* Configure PB4 as output, default OUT=0 red led off */
  GPIO_PinModeSet(gpioPortB, 4, gpioModePushPull, 0);

  //IADC_disable(IADC0);

  //GPIO_PinModeSet(gpioPortA,  5, gpioModeInputPull, 0);// BTN-IN/Ignition wake-up (PA5), default trig
}

void Resume_GPIN()
{
  initGPIO();
  set_pcsniffer_advdata_packet();

  //Start sniffing B2 broadcasting packet
  sl_bt_system_set_soft_timer(1*second,5,0);

  /* Start Scanning for Advertising Messages */
  sl_bt_scanner_start(0x01,sl_bt_scanner_discover_observation);
}

void remove_triggercmd_timer()
{
  //call endpoint_send(uart_ep, 15, "RM SPCMD TMR+\r\n")
  sl_bt_system_set_soft_timer(0,2,0);//rep
  sl_bt_system_set_soft_timer(0,4,1);//once
}

void remove_stopcmd_timer()
{
  //call endpoint_send(uart_ep, 15, "RM SPCMD TMR+\r\n")
  sl_bt_system_set_soft_timer(0,3,0);//rep
  sl_bt_system_set_soft_timer(0,6,1);//once
  sl_bt_system_set_soft_timer(0,23,1);//auto stop
}

void remove_scheduled_timer()
{
  //gecko_cmd_hardware_set_soft_timer(0,0,0);
  //gecko_cmd_hardware_set_soft_timer(0,1,0);
  sl_bt_system_set_soft_timer(0,2,0);
  sl_bt_system_set_soft_timer(0,3,0);
  sl_bt_system_set_soft_timer(0,4,1);
  sl_bt_system_set_soft_timer(0,5,0);
  sl_bt_system_set_soft_timer(0,6,1);

  sl_bt_system_set_soft_timer(0,7,0);
  sl_bt_system_set_soft_timer(0,8,0);
  sl_bt_system_set_soft_timer(0,9,0);
  sl_bt_system_set_soft_timer(0,10,0);
  sl_bt_system_set_soft_timer(0,11,0);
  sl_bt_system_set_soft_timer(0,12,0);
  sl_bt_system_set_soft_timer(0,13,0);
  sl_bt_system_set_soft_timer(0,14,0);
  sl_bt_system_set_soft_timer(0,15,0);
  sl_bt_system_set_soft_timer(0,16,0);
  sl_bt_system_set_soft_timer(0,17,0);
  sl_bt_system_set_soft_timer(0,18,0);
  sl_bt_system_set_soft_timer(0,19,0);
  sl_bt_system_set_soft_timer(0,20,0);
  sl_bt_system_set_soft_timer(0,21,0);
  sl_bt_system_set_soft_timer(0,22,0);
  //gecko_cmd_hardware_set_soft_timer(0,24,0);
}

void stop_broadcasting_to_B2()
{
  trigger_duration_is_on = 0;
  remove_triggercmd_timer();
  remove_stopcmd_timer();

  //green led on
  green_led_on(1);

  //drive the PC2 to High
  //GPIO_PortOutSet(gpioPortC, 0x0004);
}

void stop_trigger_BWCS()
{
  //stop advertising timer
  sl_bt_system_set_soft_timer(0,8,0);
  if(!boot)
  {sl_bt_advertiser_stop(advertising_set_handle);}
  else
  {boot = false;}
  red_led_on(0);
  //set_pcsniffer_advdata_packet();
  //green_led_on(1);
  //stop blink led
  //sl_bt_system_set_soft_timer(0,9,0);

  //if(dcin == 0)
  //{gecko_cmd_le_gap_set_mode(le_gap_non_discoverable, le_gap_non_connectable);}
  //else
  {
    //Start advertising wait connecting after 0.5 second
    //sl_bt_system_set_soft_timer(0.5*second,1,1);

    //Get_Battery_Percentage
    //gecko_cmd_hardware_set_soft_timer(1*milliseconds,2,1);
    //gecko_cmd_hardware_set_soft_timer(10*milliseconds,11,1);
  }

  starttrig = 0;
}

void Store_MAC_to_B2_Devices_List()
{
  //if(check_B2_header() != 1)
  //  return;
  for(int i=0;i<6;i++)
  {
    if(check_MAC_in_B2_Devices_List(i) == 0)
    {
      if (i == 0)
      {
        strncpy(&B2G_Device00[6], &advdata[15], 2);
        B2G_Device00[8] = 0;
        return;
      }
      if (i == 1)
      {
        strncpy(&B2G_Device01[6], &advdata[15], 2);
        B2G_Device01[8] = 0;
        return;
      }
      if (i == 2)
      {
        strncpy(&B2G_Device02[6], &advdata[15], 2);
        B2G_Device02[8] = 0;
        return;
      }
      if (i == 3)
      {
        strncpy(&B2G_Device03[6], &advdata[15], 2);
        B2G_Device03[8] = 0;
        return;
      }
      if (i == 4)
      {
        strncpy(&B2G_Device04[6], &advdata[15], 2);
        B2G_Device04[8] = 0;
        return;
      }
      if (i == 5)
      {
        strncpy(&B2G_Device05[6], &advdata[15], 2);
        B2G_Device05[8] = 0;
        return;
      }
    }
  }
  if (B2G_DeviceListInx < 6)
  {
    if (B2G_DeviceListInx == 0)
    {
      strcpy(B2G_Device00, B2_MAC_Addr);
      strncpy(&B2G_Device00[6], &advdata[15], 2);
      B2G_DeviceListInx = B2G_DeviceListInx + 1;
      return;
    }
    if (B2G_DeviceListInx == 1)
    {
      strcpy(B2G_Device01, B2_MAC_Addr);
      strncpy(&B2G_Device01[6], &advdata[15], 2);
      B2G_DeviceListInx = B2G_DeviceListInx + 1;
      return;
    }
    if (B2G_DeviceListInx == 2)
    {
      strcpy(B2G_Device02, B2_MAC_Addr);
      strncpy(&B2G_Device02[6], &advdata[15], 2);
      B2G_DeviceListInx = B2G_DeviceListInx + 1;
      return;
    }
    if (B2G_DeviceListInx == 3)
    {
      strcpy(B2G_Device03, B2_MAC_Addr);
      strncpy(&B2G_Device03[6], &advdata[15], 2);
      B2G_DeviceListInx = B2G_DeviceListInx + 1;
      return;
    }
    if (B2G_DeviceListInx == 4)
    {
      strcpy(B2G_Device04, B2_MAC_Addr);
      strncpy(&B2G_Device04[6], &advdata[15], 2);
      B2G_DeviceListInx = B2G_DeviceListInx + 1;
      return;
    }
    if (B2G_DeviceListInx == 5)
    {
      strcpy(B2G_Device05, B2_MAC_Addr);
      strncpy(&B2G_Device05[6], &advdata[15], 2);
      B2G_DeviceListInx = B2G_DeviceListInx + 1;
      return;
    }
  }
}

void Store_MAC_to_B3_Devices_List()
{
  for(int i=0;i<6;i++)
  {
    if(check_MAC_in_B3_Devices_List(i) == 0)
    {
      strncpy(&B3G_Device[i][6], &advdata[15], 2);
      B3G_Device[i][8] = 0;
      return;
    }
  }
  if (B3G_DeviceListInx < 6)
  {
    for(int i=0;i<6;i++)
    {
      if(B3G_Device[i][9] == 0)
      {
          strcpy(&B3G_Device[i][0], B2_MAC_Addr);
          strncpy(&B3G_Device[i][6], &advdata[15], 2);
          B3G_Device[i][9] = 1;
          B3G_DeviceListInx++;
          return;
      }
    }
  }
}

void add_device_count()
{
  for(int i=0;i<6;i++)
  {B3G_Device[i][8]++;}



  B2G_Device00[8]++;
  B2G_Device01[8]++;
  B2G_Device02[8]++;
  B2G_Device03[8]++;
  B2G_Device04[8]++;
  B2G_Device05[8]++;
}

void check_device_count()
{
  for(int i=0;i<6;i++)
  {
      if(B3G_Device[i][8]>3)
      {
      memset(&B3G_Device[i][0], 0, 10);
      if(B3G_DeviceListInx>0)
      {B3G_DeviceListInx--;}
      }
  }


  if(B2G_Device00[8]>3)
  {
    memset(B2G_Device00, 0, 10);
    if(B2G_DeviceListInx>0)
    {B2G_DeviceListInx--;}
  }
  if(B2G_Device01[8]>3)
  {
    memset(B2G_Device01, 0, 10);
    if(B2G_DeviceListInx>0)
    {B2G_DeviceListInx--;}
  }
  if(B2G_Device02[8]>3)
  {
    memset(B2G_Device02, 0, 10);
    if(B2G_DeviceListInx>0)
    {B2G_DeviceListInx--;}
  }
  if(B2G_Device03[8]>3)
  {
    memset(B2G_Device03, 0, 10);
    if(B2G_DeviceListInx>0)
    {B2G_DeviceListInx--;}
  }
  if(B2G_Device04[8]>3)
  {
    memset(B2G_Device04, 0, 10);
    if(B2G_DeviceListInx>0)
    {B2G_DeviceListInx--;}
  }
  if(B2G_Device05[8]>3)
  {
    memset(B2G_Device05, 0, 10);
    if(B2G_DeviceListInx>0)
    {B2G_DeviceListInx--;}
  }
}

int check_B2_header()
{
  //if((DSCADVDATA[6] == 0x57 && DSCADVDATA[7] == 0x4B) || (DSCADVDATA[6] == 0x42 && DSCADVDATA[7] == 0x43))
  // Check BC or Getac
  if((DSCADVDATA[6] == 0x42 && DSCADVDATA[7] == 0x43) || (DSCADVDATA[8] == 0x47 && DSCADVDATA[9]== 0x65 && DSCADVDATA[10]== 0x74 && DSCADVDATA[11]== 0x61 && DSCADVDATA[12]== 0x63))
  {return 1;}
  else
  {return 0;}
}

int compare_GroupName(int group)
{
  if(compare_default_GroupName(group) == 0)
  {return 1;}

  if (group == 1)
  {return strncmp(DSCADVDATA, groupName01, 6);}
  if (group == 2)
  {return strncmp(DSCADVDATA, groupName02, 6);}
  if (group == 3)
  {return strncmp(DSCADVDATA, groupName03, 6);}
  if (group == 4)
  {return strncmp(DSCADVDATA, groupName04, 6);}
  if (group == 5)
  {return strncmp(DSCADVDATA, groupName05, 6);}
  return 1;
}

void start_detect(bool enable)
{
  if(enable)
  {
    //Start detect
#if D_LETIMER
    LETIMER_Enable(LETIMER0, enable);
#endif
  }
  else
  {
    //Stop detect
#if D_LETIMER
    // Disable LETIMER0
    LETIMER_Enable(LETIMER0, enable);
#endif
  }
}

void plugin_detect(bool enable)
{
  if(enable)
  {
      //Start detect
    GPIO_IntConfig(gpioPortB,  3, false, true, true);// PLUGOUT-Detect(PA3), default trig
  }
  else
  {
    //Stop detect
      GPIO_IntConfig(gpioPortB,  3, false, false, true);// PLUGOUT-Detect(PA3), disable
  }
}

#define MIN_TEST_NUMBER         (-35) // This is the minimum tx_power to start the sweep.
#define MAX_TEST_NUMBER         (80)   // This is the maximum tx_power to end the sweep.
static int16_t tx_set;
static int16_t tx_to_set = MIN_TEST_NUMBER;

void set_pcsniffer_advdata_packet(void)
{
    static struct {
      uint8_t flagsLen;     /* Length of the Flags field. */
      uint8_t flagsType;    /* Type of the Flags field. */
      uint8_t flags;        /* Flags field. */
      uint8_t groupLen;   /* Group name length */
      uint8_t groupType;    /* Group name type */
      uint8_t groupName[26];  /* Group name */
      //uint8_t mandataLen;   /* Length of the Manufacturer Data field. */
      //uint8_t mandataType;  /* Type of the Manufacturer Data field. */
      //uint8_t compId[2];    /* Company ID field. */
      //uint8_t reserved[12];
      //uint8_t cmd[4];
  }
  pcsnifferAdvData = {
    /* Flag bits - See Bluetooth 4.0 Core Specification , Volume 3, Appendix C, 18.1 for more details on flags. */
    2,        /* length  */
    0x01,     /* type */
    0x04 | 0x02,  /* Flags: LE General Discoverable Mode, BR/EDR is disabled. */
    0x1a,      /* Group name length */
    0x9,      /* Group name type */
#if D_HOLSTER_ARMOR == 0
    0x54, 0x42, 0x2d, 0x30, 0x33, 0x20, 0x39, 0x39, 0x39, 0x39,//TB-03 9999999999
#elif D_HOLSTER_ARMOR == 1
    0x48, 0x53, 0x2d, 0x30, 0x31, 0x20, 0x39, 0x39, 0x39, 0x39,//HS-01 9999999999
#else D_HOLSTER_ARMOR == 2
    0x41, 0x53, 0x2d, 0x30, 0x31, 0x20, 0x39, 0x39, 0x39, 0x39,//AS-01 9999999999
#endif
    0x39,     /* Length of the Manufacturer Data field. */
    0x39,     /* Type of the Manufacturer Data field. */
    0x39, 0x39, /* Company ID field. */
    0x39, 0x39, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
    //{0x00, 0x00, 0x00, 0x00}
  };
    pcsniffer_pkt_len = sizeof(pcsnifferAdvData);
    pData = (uint8_t*)(&pcsnifferAdvData);

    //nvm_write = "H123456";
    //memcpy(nvm_write, "H123456", strlen("H123456"));
    //ret = sl_bt_nvm_save(0x4002,strlen(nvm_write),nvm_write);

    ret = sl_bt_nvm_load(0x4002,10,&read_len,(uint8_t*)user_read_response_buf);
    printf("set_pcsniffer_advdata_packet ret = %d\r\n", ret);
    if (SL_STATUS_OK  == ret)
    {
      memset(&pcsnifferAdvData.groupName[6], 0, 10);
      memcpy(&pcsnifferAdvData.groupName[6], user_read_response_buf, strlen(user_read_response_buf));
    }
    printf("SYS_Serial_Number = %s, len = %d\r\n", pcsnifferAdvData.groupName, strlen(pcsnifferAdvData.groupName));
    /* Set -3.5 dBm Transmit Power */
    sc = sl_bt_system_set_tx_power (MIN_TEST_NUMBER, tx_to_set, NULL, &tx_set);
    if(sc == SL_STATUS_OK)
    {
      printf("**** set_tx_power(%03d) returns %03d ****\r\n", tx_to_set, tx_set);
    }
    //sl_bt_system_set_max_tx_power(0, set_power);

    // Create an advertising set.
    //sc = sl_bt_advertiser_create_set(&advertising_set_handle);
    //app_assert_status(sc);

    /* Set custom advertising data */
    //gecko_cmd_le_gap_set_adv_data(0, pcsniffer_pkt_len, pData);
    sl_bt_advertiser_set_data(advertising_set_handle, 0, pcsniffer_pkt_len, pData);

    // Set advertising interval to 100ms.
    sc = sl_bt_advertiser_set_timing(
      advertising_set_handle,
      160, // min. adv. interval (milliseconds * 1.6)
      160, // max. adv. interval (milliseconds * 1.6)
      0,   // adv. duration
      0);  // max. num. adv. events
    app_assert_status(sc);
    // Start general advertising and enable connections.
    sc = sl_bt_advertiser_start(
      advertising_set_handle,
      sl_bt_advertiser_user_data,
      sl_bt_advertiser_connectable_scannable);
    app_assert_status(sc);

    printf("**** set_pcsniffer_advdata_packet **** <---\r\n");
}

void GPIO_EVEN_IRQHandler(void)
{
  uint32_t valueInt;
    valueInt = GPIO_IntGet();
    printf("GPIO_EVEN_IRQHandler valueInt: %x\r\n",valueInt);
#if D_LETIMER
#else
    //printf("GPIO_EVEN_IRQHandler valueInt: %x\r\n",valueInt); // print message will take 4-5ms
#endif
    if(test_mode == 1)
    {
        GPIO_IntClear(GPIO_IntGet());  //Clear all interrupt
        return;
    }


#if D_TB03
    GPIN4_HL_CNT = 0;
    stop_broadcasting_to_B2();
#endif

    switch (valueInt)
    {
      case (0x10):
      /* Clear GPIO interrupt PIN1(portC pin 4) */
      if(!GPIO_PinInGet(gpioPortC, 4))
      {printf("****GPIN1 is low****\r\n");}
      else
      {printf("****GPIN1 is high****\r\n");}
      if ((gpin_stopcmd_pins_buf & gpin_1_for_pc4) == gpin_1_for_pc4)
      {
        stop_BWCB2();
        GPIO_IntClear(valueInt);
        return;
      }
      //detect "PRESS" gpin_1_for_pc4
      sl_bt_system_set_soft_timer(0.5*second,7,0);
      break;

      case (0x40):
      /* Clear GPIO interrupt PIN2(portC pin 6) */
      if(!GPIO_PinInGet(gpioPortC, 6))
      {printf("****GPIN2 is low****\r\n");}
      else
      {printf("****GPIN2 is high****\r\n");}
      if ((gpin_stopcmd_pins_buf & gpin_2_for_pc6) == gpin_2_for_pc6)
      {
        stop_BWCB2();
        GPIO_IntClear(valueInt);
        return;
      }
      //detect "PRESS" gpin_2_for_pc6
      sl_bt_system_set_soft_timer(0.5*second,11,0);
      break;

      case (0x100):
      /* Clear GPIO interrupt PIN4(portB pin 2) */
      if(!GPIO_PinInGet(gpioPortA, 8))
      {printf("****GPIN4 is low****\r\n");}
      else
      {printf("****GPIN4 is high****\r\n");}
      if ((gpin_stopcmd_pins_buf & gpin_4_for_pa8) == gpin_4_for_pa8)
      {
        stop_BWCB2();
        GPIO_IntClear(valueInt);
        return;
      }
      //detect "PRESS" gpin_4_for_pa8
      sl_bt_system_set_soft_timer(0.5*second,17,0);
      break;

      case (0x1):
      /* Clear GPIO interrupt PIN5(portB pin 0) */
      if(!GPIO_PinInGet(gpioPortB, 0))
      {printf("****GPIN5 is low****\r\n");}
      else
      {printf("****GPIN5 is high****\r\n");}
      if ((gpin_stopcmd_pins_buf & gpin_5_for_pb0) == gpin_5_for_pb0)
      {
        stop_BWCB2();
        GPIO_IntClear(valueInt);
        return;
      }
      //detect "PRESS" gpin_5_for_pb0
      sl_bt_system_set_soft_timer(0.5*second,15,0);
      break;

      case (0x4):
      /* Clear GPIO interrupt PIN6(portB pin 2) */
      if(!GPIO_PinInGet(gpioPortB, 2))
      {printf("****GPIN6 is low****\r\n");}
      else
      {printf("****GPIN6 is high****\r\n");}
      if ((gpin_stopcmd_pins_buf & gpin_6_for_pb2) == gpin_6_for_pb2)
      {
        stop_BWCB2();
        GPIO_IntClear(valueInt);
        return;
      }
      //detect "PRESS" gpin_6_for_pb2
      sl_bt_system_set_soft_timer(0.5*second,19,0);
      break;

      //case (0x100):
      /* Clear GPIO interrupt PIN5(portB pin 2) */
      /*if(!GPIO_PinInGet(gpioPortA, 8))
      {printf("****GPIN5 is low****\r\n");}
      else
      {printf("****GPIN5 is high****\r\n");}
      if ((gpin_stopcmd_pins_buf & gpin_5_for_pa8) == gpin_5_for_pa8)
      {
        stop_BWCB2();
        GPIO_IntClear(valueInt);
        return;
      }
      //detect "PRESS" gpin_5_for_pa8
      sl_bt_system_set_soft_timer(0.5*second,17,0);
      break;*/

      //case (0x4):
      /* Clear GPIO interrupt PIN6(portB pin 2) */
      /*if(!GPIO_PinInGet(gpioPortB, 2))
      {printf("****GPIN6 is low****\r\n");}
      else
      {printf("****GPIN6 is high****\r\n");}
      if ((gpin_stopcmd_pins_buf & gpin_6_for_pb2) == gpin_6_for_pb2)
      {
        stop_BWCB2();
        GPIO_IntClear(valueInt);
        return;
      }
      //detect "PRESS" gpin_6_for_pb2
      sl_bt_system_set_soft_timer(0.5*second,19,0);
      break;*/

      default:
      break;
    }

    {GPIO_IntClear(valueInt);}
}

void GPIO_ODD_IRQHandler(void)
{
  uint32_t valueInt;
  valueInt = GPIO_IntGet();

  printf("GPIO_ODD_IRQHandler valueInt: %x\r\n",valueInt);
  //{GPIO_IntClear(valueInt);}
  if(test_mode == 1)
  {
    GPIO_IntClear(GPIO_IntGet());  //Clear all interrupt
    return;
  }

#if D_TB03
  GPIN4_HL_CNT = 0;
  stop_broadcasting_to_B2();
#endif

  switch (valueInt)
  {
#if !D_TB03
    case (0x8):
          /* PLUG-IN detect */
          //if(plugout == 1 && starttrig == 0 && dcin == 0)
          {
            //flushLog();
            //initLog();
            printf("[WDOG]Plug in detect!!!\r\n");
            //gecko_cmd_le_gap_end_procedure();
          //gecko_cmd_hardware_set_soft_timer(0,2,0);
          //gecko_cmd_le_gap_set_mode(le_gap_non_discoverable, le_gap_non_connectable);

          //GPIO_PinModeSet(gpioPortC,  7, gpioModeDisabled, 0);
          //GPIO_PinModeSet(gpioPortC,  8, gpioModeDisabled, 0);

          //GPIO_PinModeSet(gpioPortD,  9, gpioModeDisabled, 0);
          //GPIO_PinModeSet(gpioPortD, 12, gpioModeDisabled, 0);

          /* DC-IN do not disable UART */
          //if(!GPIO_PinInGet(gpioPortF, 7))
          {
              //GPIO_PinModeSet(gpioPortF, 2, gpioModeDisabled, 1);
              //GPIO_PinModeSet(gpioPortF, 3, gpioModeDisabled, 1);
          }
#if D_WDOG
            plugin_detect(0);
            plugout = 0;
            sl_udelay_wait(100);
            WDOG_Enable(true);
            //GPIO_PinModeSet(gpioPortF, 2, gpioModeDisabled, 1);
            //GPIO_PinModeSet(gpioPortF, 3, gpioModeDisabled, 1);
            //EMU_EnterEM2(true);
#else
            trigger_BWCS();
#endif
          //GPIO_PinModeSet(gpioPortF, 2, gpioModeDisabled, 1);
          //GPIO_PinModeSet(gpioPortF, 3, gpioModeDisabled, 1);
              //EMU_EnterEM2(true);
          }
          GPIO_IntClear(valueInt);
          break;
#else
    case (0x8):
    /* Clear GPIO interrupt PIN7(portB pin 3) */
    if(!GPIO_PinInGet(gpioPortB, 3))
    {printf("****GPIN0 is low****\r\n");}
    else
    {printf("****GPIN0 is high****\r\n");}
    if ((gpin_stopcmd_pins_buf & gpin_0_for_pb3) == gpin_0_for_pb3)
    {
      stop_BWCB2();
      GPIO_IntClear(valueInt);
      return;
    }
    //detect "PRESS" gpin_0_for_pb3
    sl_bt_system_set_soft_timer(0.5*second,21,0);
    break;

     //case (0x2):
     /* Clear GPIO interrupt PIN1(portC pin 1) */
     /*if(!GPIO_PinInGet(gpioPortC, 1))
     {printf("****GPIN1 is low****\r\n");}
     else
     {printf("****GPIN1 is high****\r\n");}
     if ((gpin_stopcmd_pins_buf & gpin_1_for_pc1) == gpin_1_for_pc1)
     {
       stop_BWCB2();
       GPIO_IntClear(valueInt);
       return;
     }
     //detect "PRESS" gpin_1_for_pc1
     sl_bt_system_set_soft_timer(0.5*second,9,0);
     break;*/


     //case (0x8):
     /* Clear GPIO interrupt PIN4(portB pin 0) */
     /*if(!GPIO_PinInGet(gpioPortB, 0))
     {printf("****GPIN4 is low****\r\n");}
     else
     {printf("****GPIN4 is high****\r\n");}
     if ((gpin_stopcmd_pins_buf & gpin_5_for_pb0) == gpin_5_for_pb0)
     {
       stop_BWCB2();
       GPIO_IntClear(valueInt);
       return;
     }
     //detect "PRESS" gpin_5_for_pb0
     sl_bt_system_set_soft_timer(0.5*second,15,0);
     break;*/

     case (0x80):
     /* Clear GPIO interrupt PIN3(portA pin 7) */
     if(!GPIO_PinInGet(gpioPortA, 7))
     {printf("****GPIN3 is low****\r\n");}
     else
     {printf("****GPIN3 is high****\r\n");}
     if ((gpin_stopcmd_pins_buf & gpin_3_for_pa7) == gpin_3_for_pa7)
     {
       stop_BWCB2();
       GPIO_IntClear(valueInt);
       return;
     }
     //detect "PRESS" gpin_3_for_pa7
     sl_bt_system_set_soft_timer(0.5*second,13,0);
     break;

     case (0x2):
     /* Clear GPIO interrupt PIN7(portC pin 1) */
     if(!GPIO_PinInGet(gpioPortC, 1))
     {printf("****GPIN7 is low****\r\n");}
     else
     {printf("****GPIN7 is high****\r\n");}
     if ((gpin_stopcmd_pins_buf & gpin_7_for_pc1) == gpin_7_for_pc1)
     {
       stop_BWCB2();
       GPIO_IntClear(valueInt);
       return;
     }
     //detect "PRESS" gpin_7_for_pc1
     sl_bt_system_set_soft_timer(0.5*second,9,0);
     break;
#endif//#if !D_TB03

     case (0x20):
     /* Button Press detect */
     if(!GPIO_PinInGet(gpioPortA, 5))
     {
       //red_led_on(1);
       printf("****Button press****\r\n");
       //testLED(); //for ME test
       //struct gecko_msg_hardware_get_time_rsp_t* time = gecko_cmd_hardware_get_time();
       BTN_TIMER_CNT = 0;
       uint32_t time = sl_sleeptimer_get_tick_count();
       BTN_TIMER_CNT = time;
       //Button count each second
       //gecko_cmd_hardware_set_soft_timer(1*second,5,0);
       //printf("****Button press****\r\n");
     }
     else
     {
   #if !D_TB03
       //red_led_on(0);
       printf("****Button Release****\r\n");
       //green_red_yellow_led_off();
       //struct gecko_msg_hardware_get_time_rsp_t* time = gecko_cmd_hardware_get_time();
       uint32_t time = sl_sleeptimer_get_tick_count();
       BTN_TIMER_CNT = (time - BTN_TIMER_CNT)/second;
       //printf("****Button Release**** BTN_TIMER_CNT: %d, %d\r\n",BTN_TIMER_CNT, BTN_TIMER_CNT/second);
       sl_bt_system_set_soft_timer(1*milliseconds,55,1);
   #else
       //app_init();
       printf("****Wake up****\r\n");
       Resume_GPIN();
   #endif
     }
     break;

    default:
    break;

  }

    {GPIO_IntClear(valueInt);}
}

// Set CLK_ADC to 10 MHz
#define CLK_SRC_ADC_FREQ        20000000  // CLK_SRC_ADC
#define CLK_ADC_FREQ            10000000  // CLK_ADC - 10 MHz max in normal mode

/*
 * Specify the IADC input using the IADC_PosInput_t typedef.  This
 * must be paired with a corresponding macro definition that allocates
 * the corresponding ABUS to the IADC.  These are...
 *
 * GPIO->ABUSALLOC |= GPIO_ABUSALLOC_AEVEN0_ADC0
 * GPIO->ABUSALLOC |= GPIO_ABUSALLOC_AODD0_ADC0
 * GPIO->BBUSALLOC |= GPIO_BBUSALLOC_BEVEN0_ADC0
 * GPIO->BBUSALLOC |= GPIO_BBUSALLOC_BODD0_ADC0
 * GPIO->CDBUSALLOC |= GPIO_CDBUSALLOC_CDEVEN0_ADC0
 * GPIO->CDBUSALLOC |= GPIO_CDBUSALLOC_CDODD0_ADC0
 *
 * ...for port A, port B, and port C/D pins, even and odd, respectively.
 */
#define IADC_INPUT_0_PORT_PIN     iadcPosInputPortCPin6;

#define IADC_INPUT_0_BUS          CDBUSALLOC
#define IADC_INPUT_0_BUSALLOC     GPIO_CDBUSALLOC_CDEVEN0_ADC0
// Single input structure
IADC_Init_t init = IADC_INIT_DEFAULT;
IADC_AllConfigs_t initAllConfigs = IADC_ALLCONFIGS_DEFAULT;
IADC_InitSingle_t initSingle = IADC_INITSINGLE_DEFAULT;
IADC_SingleInput_t singleInput = IADC_SINGLEINPUT_DEFAULT;
/*******************************************************************************
 ***************************   GLOBAL VARIABLES   ******************************
 ******************************************************************************/

// Raw IADC conversion result
//static volatile IADC_Result_t sample;

// Result converted to volts
//static volatile double singleResult;

/**************************************************************************//**
 * @brief  IADC initialization
 *****************************************************************************/
void initIADC(void)
{
  // Declare initialization structures
  //IADC_Init_t init = IADC_INIT_DEFAULT;
  //IADC_AllConfigs_t initAllConfigs = IADC_ALLCONFIGS_DEFAULT;
  //IADC_InitSingle_t initSingle = IADC_INITSINGLE_DEFAULT;

  // Single input structure
  //IADC_SingleInput_t singleInput = IADC_SINGLEINPUT_DEFAULT;

  /*
   * Enable IADC0 and GPIO register clock.
   *
   * Note: On EFR32xG21 devices, CMU_ClockEnable() calls have no effect
   * as clocks are enabled/disabled on-demand in response to peripheral
   * requests.  Deleting such lines is safe on xG21 devices and will
   * reduce provide a small reduction in code size.
   */
  CMU_ClockEnable(cmuClock_IADC0, true);
  CMU_ClockEnable(cmuClock_GPIO, true);

  // Reset IADC to reset configuration in case it has been modified by
  // other code
  IADC_reset(IADC0);

  // Use the FSRC0 as the IADC clock so it can run in EM2
  CMU_ClockSelectSet(cmuClock_IADCCLK, cmuSelect_FSRCO);

  // Set the prescaler needed for the intended IADC clock frequency
  init.srcClkPrescale = IADC_calcSrcClkPrescale(IADC0, CLK_SRC_ADC_FREQ, 0);

  // Shutdown between conversions to reduce current
  //init.warmup = iadcWarmupNormal;
  // Modify init structs and initialize
  init.warmup = iadcWarmupKeepWarm;

  /*
   * Configuration 0 is used by both scan and single conversions by
   * default.  Use unbuffered AVDD as reference and specify the
   * AVDD supply voltage in mV.
   *
   * Resolution is not configurable directly but is based on the
   * selected oversampling ratio (osrHighSpeed), which defaults to
   * 2x and generates 12-bit results.
   */
#if !D_TB03
  initAllConfigs.configs[0].reference = iadcCfgReferenceInt1V2;
  initAllConfigs.configs[0].analogGain = iadcCfgAnalogGain0P5x;
  initAllConfigs.configs[0].vRef = 1210;
#else
  initAllConfigs.configs[0].reference = iadcCfgReferenceVddx;
  initAllConfigs.configs[0].vRef = 3300;
#endif
  //initAllConfigs.configs[0].osrHighSpeed = iadcCfgOsrHighSpeed2x;

  /*
   * CLK_SRC_ADC must be prescaled by some value greater than 1 to
   * derive the intended CLK_ADC frequency.
   *
   * Based on the default 2x oversampling rate (OSRHS)...
   *
   * conversion time = ((4 * OSRHS) + 2) / fCLK_ADC
   *
   * ...which results in a maximum sampling rate of 833 ksps with the
   * 2-clock input multiplexer switching time is included.
   */
  initAllConfigs.configs[0].adcClkPrescale = IADC_calcAdcClkPrescale(IADC0,
                                                                     CLK_ADC_FREQ,
                                                                     0,
                                                                     iadcCfgModeNormal,
                                                                     init.srcClkPrescale);

  /*
   * Specify the input channel.  When negInput = iadcNegInputGnd, the
   * conversion is single-ended.
   */
  singleInput.posInput   = IADC_INPUT_0_PORT_PIN;
  singleInput.negInput   = iadcNegInputGnd;

  // Allocate the analog bus for ADC0 inputs
  GPIO->IADC_INPUT_0_BUS |= IADC_INPUT_0_BUSALLOC;

  // Initialize IADC
  IADC_init(IADC0, &init, &initAllConfigs);

  // Initialize a single-channel conversion
  IADC_initSingle(IADC0, &initSingle, &singleInput);

  // Clear any previous interrupt flags
  //IADC_clearInt(IADC0, _IADC_IF_MASK);

  // Enable single-channel done interrupts
  //IADC_enableInt(IADC0, IADC_IEN_SINGLEDONE);

  // Enable IADC interrupts
  //NVIC_ClearPendingIRQ(IADC_IRQn);
  //NVIC_EnableIRQ(IADC_IRQn);
}

/**************************************************************************//**
 * @brief  IADC IRQ Handler
 *****************************************************************************/

void IADC_IRQHandler(void)
{
  printf("\r\n**** IADC_IRQHandler ****\r\n");
  // Read a result from the FIFO
  sample = IADC_pullSingleFifoResult(IADC0);

  /*
   * Calculate the voltage converted as follows:
   *
   * For single-ended conversions, the result can range from 0 to
   * +Vref, i.e., for Vref = AVDD = 3.30 V, 0xFFF represents the
   * full scale value of 3.30 V.
   */
  singleResult = sample.data * 3.3 / 0xFFF;

  /*
   * Clear the single conversion complete interrupt.  Reading FIFO
   * results does not do this automatically.
   */
  IADC_clearInt(IADC0, IADC_IF_SINGLEDONE);
}

/**************************************************************************//**
 * @brief  Initialize ADC function
 *****************************************************************************/
/*void initADC (void)
{
  // Enable ADC0 clock
  CMU_ClockEnable(cmuClock_ADC0, true);

  // Declare init structs
  ADC_Init_TypeDef init = ADC_INIT_DEFAULT;
  ADC_InitSingle_TypeDef initSingle = ADC_INITSINGLE_DEFAULT;

  // Modify init structs and initialize
  init.prescale = ADC_PrescaleCalc(adcFreq, 0); // Init to max ADC clock for Series 1

  initSingle.diff       = false;        // single ended
  initSingle.reference  = adcRef5V;    // internal 2.5V reference
  initSingle.resolution = adcRes12Bit;  // 12-bit resolution
  initSingle.acqTime    = adcAcqTime4;  // set acquisition time to meet minimum requirement

  // Select ADC input. See README for corresponding EXP header pin.
  initSingle.posSel = adcPosSelAPORT3XCH4;
  init.timebase = ADC_TimebaseCalc(0);

  ADC_Init(ADC0, &init);
  ADC_InitSingle(ADC0, &initSingle);
}*/

/**************************************************************************//**
 * @brief GPIO initialization
 *****************************************************************************/
void initGPIO(void)
{
    ////////////////////Set for output////////////////////
#if !D_TB03
  /* Configure PB1 as output, default OUT=0 green led off */
    GPIO_PinModeSet(gpioPortB, 1, gpioModePushPull, 1);
    /* Configure PB4 as output, default OUT=0 red led off */
    GPIO_PinModeSet(gpioPortB, 4, gpioModePushPull, 1);
#else
    /* Configure PB1 as output, default OUT=0 green led on */
      GPIO_PinModeSet(gpioPortB, 1, gpioModePushPull, 1);
      /* Configure PB4 as output, default OUT=0 red led off */
      GPIO_PinModeSet(gpioPortB, 4, gpioModePushPull, 0);
#endif

#if !D_TB03
    /* Configure PB2 (PWM) as output */
    GPIO_PinModeSet(gpioPortB, 2, gpioModePushPull, 1);
    /* Configure PD2 as output, default OUT=0 SENSOR_ENABLE off */
    //GPIO_PinModeSet(gpioPortD, 2, gpioModePushPull, 0);
#endif

    /* Init GPIO interrupt */
//////////////////////// Set for interrupt ////////////////////////
    GPIO_PinModeSet(gpioPortA,  5, gpioModeInputPullFilter, 1);// BTN-IN/Ignition wake-up (PA5), default trig
#if !D_TB03
    #if D_WDOG
        GPIO_PinModeSet(gpioPortB,  3, gpioModeInputPull, 1);// PLUGOUT-Detect(PA3), default trig
    #else
        GPIO_PinModeSet(gpioPortB,  3, gpioModeInput, 0);// PLUGOUT-Detect(PA3), default trig
    #endif
#else
    GPIO_PinModeSet(gpioPortD,  2, gpioModeInputPullFilter, 0);    // Coin ADC, input low
    GPIO_PinModeSet(gpioPortA,  6, gpioModeInputPullFilter, 0);    // Ignition ADC, input low


    GPIO_PinModeSet(gpioPortB,  3, gpioModeInputPullFilter, 1);    // GPIN0
    GPIO_PinModeSet(gpioPortC,  4, gpioModeInputPullFilter, 1);    // GPIN1
    GPIO_PinModeSet(gpioPortC,  6, gpioModeInputPullFilter, 1);    // GPIN2
    GPIO_PinModeSet(gpioPortA,  7, gpioModeInputPullFilter, 1);    // GPIN3
    GPIO_PinModeSet(gpioPortA,  8, gpioModeInputPullFilter, 1);    // GPIN4
    GPIO_PinModeSet(gpioPortB,  0, gpioModeInputPullFilter, 1);    // GPIN5
    GPIO_PinModeSet(gpioPortB,  2, gpioModeInputPullFilter, 1);    // GPIN6
    GPIO_PinModeSet(gpioPortC,  1, gpioModeInputPullFilter, 1);    // GPIN7, default stop

    /* Configure PC2 as output, default OUT=0 DOUT */
    GPIO_PinModeSet(gpioPortC,  2, gpioModePushPull, 0);
#endif

//////////////////////// Interrupt init ////////////////////////
#if !D_TB03
    //Set for BTN(Holster/Armor)
    GPIO_IntConfig(gpioPortA,  5, true, true, true);// BTN-IN/Ignition wake-up (PA5), default trig
    #if !D_WDOG
        GPIO_IntConfig(gpioPortB,  3, false, true, true);// PLUGOUT-Detect(PA3), default trig
    #endif
#else
    //Set for Ignition wake-up(TB03)
    GPIO_IntConfig(gpioPortA,  5, true, false, true);// wake up // ignition on, risingEdge


    GPIO_IntConfig(gpioPortB,  3, false, true, true);      // GPIN0, fallingEdge, default trig
    GPIO_IntConfig(gpioPortC,  4, false, true, true);      // GPIN1, fallingEdge, default trig
    GPIO_IntConfig(gpioPortC,  6, false, true, true);      // GPIN2, fallingEdge, default trig
    GPIO_IntConfig(gpioPortA,  7, false, true, true);      // GPIN3, fallingEdge, default trig
    GPIO_IntConfig(gpioPortA,  8, false, true, true);      // GPIN4, fallingEdge, default trig
    GPIO_IntConfig(gpioPortB,  0, false, true, true);      // GPIN5, fallingEdge, default trig
    GPIO_IntConfig(gpioPortB,  2, false, true, true);      // GPIN6, fallingEdge, default trig
    GPIO_IntConfig(gpioPortC,  1, false, true, true);      // GPIN7, fallingEdge, default trig
    //GPIO_ExtIntConfig(gpioPortC,  0, 0, false, true, true);// GPIN1, fallingEdge, default trig
    //GPIO_IntConfig(gpioPortC,  4, false, true, true);      // GPIN2, fallingEdge, default trig
    //GPIO_IntConfig(gpioPortC,  6, false, true, true);      // GPIN3, fallingEdge, default trig
    //GPIO_IntConfig(gpioPortA,  8, false, true, true);      // GPIN4, fallingEdge, default trig
    //GPIO_ExtIntConfig(gpioPortB,  0, 1, false, true, true);// GPIN5, fallingEdge, default trig
    //GPIO_IntConfig(gpioPortB,  2, false, true, true);      // GPIN6, fallingEdge, default trig
    //GPIO_ExtIntConfig(gpioPortB,  2, 0, false, true, true);// GPIN6, fallingEdge, default trig
    //GPIO_IntConfig(gpioPortC,  1, false, true, true);      // GPIN7, fallingEdge, default trig

    //GPIO_ExtIntConfig(gpioPortC,  0, 0, true, true, true);// GPIN0, fallingEdge, default trig
    //GPIO_IntConfig(gpioPortC,  1, false, true, true);      // GPIN1, fallingEdge, default trig
    //GPIO_IntConfig(gpioPortD,  2, false, true, true);      // GPIN2, fallingEdge, default trig
    //GPIO_IntConfig(gpioPortA,  7, false, true, true);      // GPIN3, fallingEdge, default trig
    //GPIO_ExtIntConfig(gpioPortB,  0, 3, false, true, true);// GPIN4, fallingEdge, default trig
    //GPIO_IntConfig(gpioPortA,  8, false, true, true);      // GPIN5, fallingEdge, default AND
    //GPIO_IntConfig(gpioPortB,  2, false, true, true);      // GPIN6, fallingEdge, default AND
    //GPIO_IntConfig(gpioPortB,  3, false, true, true);      // GPIN7, fallingEdge, default stop
#endif

    //GPIO_PinModeSet(gpioPortD,  2, gpioModeInputPull, 1);// PLUGOUT-Detect(PA3), default trig
    //GPIO_PinModeSet(gpioPortD,  2, gpioModeInputPull, 0);
    //GPIO_PinModeSet(gpioPortC,  6, gpioModeInputPull, 0);
    NVIC_ClearPendingIRQ(GPIO_EVEN_IRQn);
    NVIC_EnableIRQ(GPIO_EVEN_IRQn);
    NVIC_ClearPendingIRQ(GPIO_ODD_IRQn);
    NVIC_EnableIRQ(GPIO_ODD_IRQn);

    GPIO_IntClear(GPIO_IntGet());  //Clear all interrupt
}

#if D_LETIMER
/**************************************************************************//**
 * @brief
 *    CMU initialization
 *****************************************************************************/
void initCmu(void)
{
  // Enable clock to GPIO and LETIMER0
  CMU_ClockEnable(cmuClock_GPIO, true);
  CMU_ClockEnable(cmuClock_LETIMER0, true);
}

/**************************************************************************//**
 * @brief Clock initialization
 *****************************************************************************/
void initClock(void)
{
  CMU_LFXOInit_TypeDef lfxoInit = CMU_LFXOINIT_DEFAULT;

  // Select LFXO for the LETIMER
  CMU_LFXOInit(&lfxoInit);
  CMU_ClockSelectSet(cmuClock_EM23GRPACLK, cmuSelect_LFXO);
}

// Desired frequency in Hz
#define OUT_FREQ 1

// Duty cycle percentage
#define DUTY_CYCLE 0.2
//#define DUTY_CYCLE 30
/**************************************************************************//**
 * @brief LETIMER initialization
 *****************************************************************************/
void initLETIMER(void)
{
  LETIMER_Init_TypeDef letimerInit = LETIMER_INIT_DEFAULT;

  // Calculate the top value (frequency) based on clock source
  uint32_t topValue = CMU_ClockFreqGet(cmuClock_LETIMER0) / OUT_FREQ;

  // Reload top on underflow, PWM output, and run in free mode
  letimerInit.comp0Top = true;
  letimerInit.topValue = topValue;
  letimerInit.ufoa0 = letimerUFOAPwm;
  letimerInit.repMode = letimerRepeatFree;

  // Enable LETIMER0 output0 on PA6
  GPIO->LETIMERROUTE[0].ROUTEEN = GPIO_LETIMER_ROUTEEN_OUT0PEN;
  GPIO->LETIMERROUTE[0].OUT0ROUTE = \
      (gpioPortB << _GPIO_LETIMER_OUT0ROUTE_PORT_SHIFT) \
      | (2 << _GPIO_LETIMER_OUT0ROUTE_PIN_SHIFT);
  // Set COMP0 to control duty cycle
  LETIMER_CompareSet(LETIMER0, 0, topValue * DUTY_CYCLE / 100);

  // Initialize LETIMER
  LETIMER_Init(LETIMER0, &letimerInit);
}
#endif

#if D_PRS
#define PRS_BASE_CH   0
#define USE_AND       true
/**************************************************************************//**
 * @brief PRS initialization
 *****************************************************************************/
void initPrs(void)
{
  // Enable PRS clock
  CMU_ClockEnable(cmuClock_PRS, true);

  //PRS_SourceSignalSet(PRS_BASE_CH, PRS_CH_CTRL_SOURCESEL_PRSL, PRS_CH_CTRL_SIGSEL_PRSCH0, prsEdgeNeg);
  //PRS_SourceSignalSet(PRS_BASE_CH, PRS_CH_CTRL_SOURCESEL_GPIOL, PRS_CH_CTRL_SIGSEL_GPIOPIN3, prsEdgeOff);

  //PRS_SourceAsyncSignalSet(PRS_BASE_CH+1, PRS_ASYNC_CH_CTRL_SOURCESEL_GPIO, 2);  //POLL
  //PRS_SourceAsyncSignalSet(PRS_BASE_CH, PRS_ASYNC_CH_CTRL_SOURCESEL_GPIO, 8);      //STATUS

  /* Configure LETIMER0 to create PRS interrupt signal and watchdog to consume as feed */
  //ch1 letimer0
  //PRS_ConnectSignal(1, prsTypeAsync, prsSignalLETIMER0_CH0);
  // ch0 gpio input from holster
  PRS_ConnectSignal(0, prsTypeAsync, prsSignalGPIO_PIN3);
  //combine two prs channel
  //PRS_Combine(0, 1, prsLogic_A_XOR_B);
  // output prs to gpio
  //PRS_PinOutput(unsigned int ch, PRS_ChType_t type, GPIO_Port_TypeDef port, uint8_t pin)
//  PRS_ConnectConsumer(1, prsTypeAsync, prsConsumerWDOG0_SRC0);

  // Configure PRS logic
  //PRS_Combine(PRS_BASE_CH+1, PRS_BASE_CH, prsLogic_A_AND_B);

  // Configure PRS Logic
  //PRS->CH[0].CTRL |= PRS_CH_CTRL_INV ; // Channel 0 will AND with Channel 1
  // Route PRS output to PC10,check the logic AND
  //PRS_PinOutput(PRS_BASE_CH,prsTypeAsync, gpioPortA,8); //STATUS&POLL



  /* Configure LETIMER0 to create PRS interrupt signal and watchdog to consume as feed */
    //PRS_ConnectSignal(0, prsTypeAsync, prsSignalLETIMER0_CH0);
    PRS_ConnectConsumer(0, prsTypeAsync, prsConsumerWDOG0_SRC0);
}
#endif

#if D_WDOG
/* Defining the watchdog initialization data */
/*WDOG_Init_TypeDef init =
{
      false,                     /* Start watchdog when initialization is done. */ \
//      false,                    /* WDOG is not counting during debug halt. */     \
 //     true,                     /* WDOG counting when in EM2 */                   \
//      true,                     /* WDOG counting when in EM3 */                   \
 //     false,                    /* EM4 can be entered. */                         \
 //     false,                    /* Do not lock WDOG configuration. */             \
 //     wdogPeriod_2k,            /* Set longest possible timeout period. */        \
 //     wdogWarnDisable,          /* Disable warning interrupt. */                  \
 //     wdogIllegalWindowDisable, /* Disable illegal window interrupt. */           \
 //     true                     /* Do not disable reset. */                       \
};*/
/* ISR */
/******************************************************************************
 * @brief WDOG Interrupt Handler. Clears interrupt flag.
 *        The interrupt table is in assembly startup file startup_efm32.s
 *
 *****************************************************************************/
void WDOG0_IRQHandler(void)
{
  //initLog();
  WDOGn_IntClear(DEFAULT_WDOG, WDOG_IEN_TOUT);
  printf("\r\n**** WDOG0_IRQHandler ****\r\n");
  //struct gecko_msg_hardware_get_time_rsp_t* time = gecko_cmd_hardware_get_time();
  //printf("\r\nWDOG0_IRQHandler %d\r\n",  time->seconds);
  //last_RTCC_value = time->seconds;
  if(plugout == 0 && dcin == 0)
  {
    printf("\r\n[WDOG]Plug out detect!!!\r\n");
    WDOG_Enable(false);
    //trigger_BWCS();
    HS01_trigger_BWCS();
    start_detect(0);
    //plugin_detect(1);
    plugout = 1;
  }

}

void initWDOG(void)
{
  WDOG_Init_TypeDef initWDOG = WDOG_INIT_DEFAULT;

  CMU_ClockEnable(cmuClock_WDOG0, true);
  CMU_ClockSelectSet(cmuClock_WDOG0, cmuSelect_ULFRCO);

  initWDOG.enable = false;
  initWDOG.perSel = wdogPeriod_1k;
  initWDOG.em2Run = true;
  initWDOG.em3Run = true;
  initWDOG.resetDisable = true;       /* Disable watchdog reset the device when fired */

  /* Initializing watchdog with chosen settings */
  WDOGn_Init(DEFAULT_WDOG, &initWDOG);
  //WDOG_Init(&init);

  /* Enable watchdog timeout interrupt */
  WDOGn_IntEnable(DEFAULT_WDOG, WDOG_IEN_TOUT);
  NVIC_EnableIRQ(WDOG0_IRQn);

  /* PRS falling edge as clear source */
  /* PRS falling edge of channel 1 as WDOG PCH[0] PRS source */
  //WDOG0->PCH[0].PRSCTRL = WDOG_PCH_PRSCTRL_PRSSEL_PRSCH0;
  //while(DEFAULT_WDOG->SYNCBUSY & WDOG_SYNCBUSY_PCH0_PRSCTRL) ;

  /* Enable PRS clear for watchdog */
  //DEFAULT_WDOG->CTRL |= WDOG_CTRL_CLRSRC;
  //DEFAULT_WDOG->CFG |= WDOG_CFG_CLRSRC_PRSSRC0;
  //PRS_ConnectConsumer(0, prsTypeAsync, prsConsumerWDOG0_SRC0);
  DEFAULT_WDOG->CFG |= WDOG_CFG_CLRSRC;

  /* Start watchdog counter */
  WDOGn_Enable(DEFAULT_WDOG, true);
}
#endif

int compare_default_GroupName(int group)
{
  if (group == 1)
  {return strncmp(groupName01, defaultgroupName, 6);}
  if (group == 2)
  {return strncmp(groupName02, defaultgroupName, 6);}
  if (group == 3)
  {return strncmp(groupName03, defaultgroupName, 6);}
  if (group == 4)
  {return strncmp(groupName04, defaultgroupName, 6);}
  if (group == 5)
  {return strncmp(groupName05, defaultgroupName, 6);}
  return 1;
}

int check_MAC_in_B2_Devices_List(int device)
{
  if(device == 0)
  {return strncmp(B2G_Device00, B2_MAC_Addr, 6);}
  if(device == 1)
  {return strncmp(B2G_Device01, B2_MAC_Addr, 6);}
  if(device == 2)
  {return strncmp(B2G_Device02, B2_MAC_Addr, 6);}
  if(device == 3)
  {return strncmp(B2G_Device03, B2_MAC_Addr, 6);}
  if(device == 4)
  {return strncmp(B2G_Device04, B2_MAC_Addr, 6);}
  if(device == 5)
  {return strncmp(B2G_Device05, B2_MAC_Addr, 6);}
  return 1;
}

int check_MAC_in_B3_Devices_List(int device)
{return strncmp(&B3G_Device[device][0], B2_MAC_Addr, 6);}

int check_B2DeviceList_AllNonRec()
{
  if (B2G_Device00[6] == 0x31 && B2G_Device00[7] == 0x31)
    {return 1;}
    if (B2G_Device01[6] == 0x31 && B2G_Device01[7] == 0x31)
  {return 1;}
    if (B2G_Device02[6] == 0x31 && B2G_Device02[7] == 0x31)
    {return 1;}
    if (B2G_Device03[6] == 0x31 && B2G_Device03[7] == 0x31)
    {return 1;}
    if (B2G_Device04[6] == 0x31 && B2G_Device04[7] == 0x31)
    {return 1;}
    if (B2G_Device05[6] == 0x31 && B2G_Device05[7] == 0x31)
  {return 1;}
    return 0;
}

int check_B3DeviceList_AllNonRec()
{
  for(int i=0;i<6;i++)
  {
    //printf("B3G_Device[%d][6]: %x,B3G_Device[%d][7]: %x\r\n",i,B3G_Device[i][6],i,B3G_Device[i][7]);
    if (B3G_Device[i][6] == 0x31 && B3G_Device[i][7] == 0x31)
    {return 1;}
  }
  return 0;
}

void check_and_broadcast_to_B2S()
{
  //printf("OneIn: %d\r\n",check_B2DeviceList_AllNonRec());
  //printf("B2NRC: %d\r\n",B2NonRecCount);
  if (check_B2DeviceList_AllNonRec() == 1 && B2NonRecCount > 6)
  {
    printf("BCAST to other B2--->\r\n");
    //set trigger identification flag = 1
    //trigger_duration_is_on = 1;
    remove_stopcmd_timer();
    TB03_trigger_BWCS();
  }

  if (check_B2DeviceList_AllNonRec() == 1)
  {B2NonRecCount = 0;}
  else
  {B2NonRecCount++;}
}

void check_and_broadcast_to_B3S()
{
  printf("OneIn: %d\r\n",check_B3DeviceList_AllNonRec());
  printf("B3NRC: %d\r\n",B3NonRecCount);
  if (check_B3DeviceList_AllNonRec() == 1 && B3NonRecCount > 6)
  {
    printf("BCAST to other B2--->\r\n");
    //set trigger identification flag = 1
    //trigger_duration_is_on = 1;
    remove_stopcmd_timer();
    TB03_trigger_BWCS();
  }

  if (check_B3DeviceList_AllNonRec() == 1)
  {B3NonRecCount = 0;}
  else
  {B3NonRecCount++;}
}

void show_B2Device_List()
{
  for(int i=0;i<6;i++)
  {
      printf("B2G_Device_%d: ",i);
      for(int j=0;j<10;j++)
      {
        if(i==0)
        {printf("%x ",B2G_Device00[j]);}
        if(i==1)
        {printf("%x ",B2G_Device01[j]);}
        if(i==2)
        {printf("%x ",B2G_Device02[j]);}
        if(i==3)
        {printf("%x ",B2G_Device03[j]);}
        if(i==4)
        {printf("%x ",B2G_Device04[j]);}
        if(i==5)
        {printf("%x ",B2G_Device05[j]);}
      }
      printf("\r\n");
  }
}

void show_B3Device_List()
{
  for(int i=0;i<6;i++)
  {
      printf("B3G_Device[%d]: ",i);
      for(int j=0;j<10;j++)
      {printf("%x ",B3G_Device[i][j]);}
      printf("\r\n");
   }
}


void Init_Configuration_From_Flash()
{
  ret = sl_bt_nvm_load(0x4003,6,&read_len,(uint8_t*)user_read_response_buf);
  if (SL_STATUS_OK  == ret)
  {
      memset(groupName01, 0, 6);
      memcpy(groupName01, user_read_response_buf, strlen(user_read_response_buf));
  }

  ret = sl_bt_nvm_load(0x4004,6,&read_len,(uint8_t*)user_read_response_buf);
  if (SL_STATUS_OK  == ret)
  {
      memset(groupName02, 0, 6);
      memcpy(groupName02, user_read_response_buf, strlen(user_read_response_buf));
  }

  ret = sl_bt_nvm_load(0x4005,6,&read_len,(uint8_t*)user_read_response_buf);
  if (SL_STATUS_OK  == ret)
  {
      memset(groupName03, 0, 6);
      memcpy(groupName03, user_read_response_buf, strlen(user_read_response_buf));
  }

  ret = sl_bt_nvm_load(0x4006,6,&read_len,(uint8_t*)user_read_response_buf);
  if (SL_STATUS_OK  == ret)
  {
      memset(groupName04, 0, 6);
      memcpy(groupName04, user_read_response_buf, strlen(user_read_response_buf));
  }

  ret = sl_bt_nvm_load(0x4007,6,&read_len,(uint8_t*)user_read_response_buf);
  if (SL_STATUS_OK  == ret)
  {
      memset(groupName05, 0, 6);
      memcpy(groupName05, user_read_response_buf, strlen(user_read_response_buf));
  }

  ret = sl_bt_nvm_load(0x4008,6,&read_len,(uint8_t*)user_read_response_buf);
  if (SL_STATUS_OK  == ret)
  {
      txpower_buf[0] = user_read_response_buf[0];
      txpower_buf[1] = user_read_response_buf[1];
  }

  ret = sl_bt_nvm_load(0x4009,6,&read_len,(uint8_t*)user_read_response_buf);
  if (SL_STATUS_OK  == ret)
  {
      trig_delay_buf = user_read_response_buf[0];
  }

  ret = sl_bt_nvm_load(0x400a,10,&read_len,(uint8_t*)user_read_response_buf);
  if(SL_STATUS_OK == ret)
  {
    transmit_duration_buf = user_read_response_buf[0] << 8;
    transmit_duration_buf = transmit_duration_buf | user_read_response_buf[1];
  }

  ret = sl_bt_nvm_load(0x400c,6,&read_len,(uint8_t*)user_read_response_buf);
  if (SL_STATUS_OK  == ret)
  {
      gpin_andop_pins_buf = user_read_response_buf[0];
  }

  ret = sl_bt_nvm_load(0x400d,6,&read_len,(uint8_t*)user_read_response_buf);
  if (SL_STATUS_OK  == ret)
  {
      gpin_stopcmd_pins_buf = user_read_response_buf[0];
  }

  ret = sl_bt_nvm_load(0x400e,6,&read_len,(uint8_t*)user_read_response_buf);
  if (SL_STATUS_OK  == ret)
  {
      sniffer_mesh = user_read_response_buf[0];
  }
}

/**************************************************************************//**
 * Application Init.
 *****************************************************************************/
SL_WEAK void app_init(void)
{
  //sl_bt_nvm_save(0x400f,strlen("1"),"0");
  ret = sl_bt_nvm_load(0x400f,10,&read_len,(uint8_t*)user_read_response_buf);
  printf("**** app_init ENERGY = %s ****\r\n", user_read_response_buf);
  //if(0 == memcmp("1", user_read_response_buf, 1))
  if(1)
  {
      printf("**** UART Rx disable ****\r\n");
  }
  else
  {
      sl_iostream_usart_init_vcom(1);
      sl_bt_system_set_soft_timer(0.5*milliseconds,24,0);
  }

  /////////////////////////////////////////////////////////////////////////////
  // Put your additional application init code here!                         //
  // This is called once during start-up.                                    //
  /////////////////////////////////////////////////////////////////////////////
  //SLEEP_SleepBlockBegin(sleepEM2);

  app_iostream_usart_init();

  // Initializations
  initGPIO();

#if D_TB03
  initIADC();
#endif

#if D_LETIMER
  /* Initialize LETIMER */
  initCmu();
  initClock();
  initLETIMER();
  start_detect(1);
#endif


#if D_PRS
  initPrs();
#endif

#if D_WDOG
  initWDOG();
#endif

  //initUSART0();
  // Enable receive data valid interrupt
  //USART_IntEnable(USART1, USART_IEN_RXDATAV);

  Init_Configuration_From_Flash();
  //Read ADC each 60 seconds
  //sl_bt_system_set_soft_timer(3*second,2,0);
  //evaluate_wakeup(SL_POWER_MANAGER_EM0);

#if D_TB03
  //Start sniffing B2 broadcasting packet
  sl_bt_system_set_soft_timer(1*second,5,0);

  //sl_bt_system_set_soft_timer(0.5*milliseconds,24,0);
  //sl_bt_system_set_soft_timer(second,24,0);

  //IADC_command(IADC0, iadcCmdStartSingle);
  //sl_bt_system_set_soft_timer(1*second,1,0);
  /* Start Scanning for Advertising Messages */
  sl_bt_scanner_start(0x01,sl_bt_scanner_discover_observation);
#endif D_TB03
  //keep trigger for test
  //red led on
  //red_led_on(1);
  //repeat timer #2 for group local name 1~5
  //sl_bt_system_set_soft_timer(1*second,2,0);



}

/**************************************************************************//**
 * Application Process Action.
 *****************************************************************************/
SL_WEAK void app_process_action(void)
{
  /////////////////////////////////////////////////////////////////////////////
  // Put your additional application code here!                              //
  // This is called infinitely.                                              //
  // Do not call blocking functions from here!                               //
  /////////////////////////////////////////////////////////////////////////////
  app_iostream_usart_process_action(&cmd_buffer[0]);
}

bd_addr address;
/**************************************************************************//**
 * Bluetooth stack event handler.
 * This overrides the dummy weak implementation.
 *
 * @param[in] evt Event coming from the Bluetooth stack.
 *****************************************************************************/
void sl_bt_on_event(sl_bt_msg_t *evt)
{
  sl_status_t sc;
  uint8_t address_type;
  uint8_t system_id[8];

  switch (SL_BT_MSG_ID(evt->header)) {
    // -------------------------------
    // This event indicates the device has started and the radio is ready.
    // Do not call any stack command before receiving this boot event!
    case sl_bt_evt_system_boot_id:

      printf("**** sl_bt_evt_system_boot_id ****\r\n");
      // Extract unique ID from BT Address.
      sc = sl_bt_system_get_identity_address(&address, &address_type);
      printf("%02X:%02X:%02X:%02X:%02X:%02X\r\n",address.addr[5],address.addr[4],address.addr[3],address.addr[2],address.addr[1],address.addr[0]);
      app_assert_status(sc);

      // Pad and reverse unique ID to get System ID.
      system_id[0] = address.addr[5];
      system_id[1] = address.addr[4];
      system_id[2] = address.addr[3];
      system_id[3] = 0xFF;
      system_id[4] = 0xFE;
      system_id[5] = address.addr[2];
      system_id[6] = address.addr[1];
      system_id[7] = address.addr[0];

      sc = sl_bt_gatt_server_write_attribute_value(gattdb_system_id,
                                                   0,
                                                   sizeof(system_id),
                                                   system_id);
      app_assert_status(sc);

      // Create an advertising set.
      sc = sl_bt_advertiser_create_set(&advertising_set_handle);
      app_assert_status(sc);

      set_pcsniffer_advdata_packet();
#if !D_TB03
      sl_bt_system_set_soft_timer(60*second,23,1);
#endif
      break;

      /* Message Received, Handle It */
      case sl_bt_evt_scanner_scan_report_id :
        //printf("evt:gecko_evt_le_gap_scan_response_id\r\n");
        data = evt->data.evt_scanner_scan_report.data;
        advdata = evt->data.evt_scanner_scan_report.data.data;
        strcpy(data.data[0], advdata);
        bwc_address = evt->data.evt_scanner_scan_report.address;
        strncpy(DSCADVDATA, &advdata[19], 6);// group name
        strncpy(&DSCADVDATA[6], &advdata[5], 2);// BC
              strncpy(&DSCADVDATA[8], &advdata[25], 5);// Getac
        //57 4b 31 58 58 42 30 31 34 30

        //if(advdata[5] == 0x57 && advdata[6] == 0x4B&& advdata[7] == 0x31&& advdata[8] == 0x58&& advdata[9] == 0x58&& advdata[10] == 0x42&& advdata[11] == 0x30&& advdata[12] == 0x31&& advdata[13] == 0x34&& advdata[14] == 0x30)
        //{printf("%x %x %x %x %x %x : %x %x %x %x %x\r\n",advdata[19],advdata[20],advdata[21],advdata[22],advdata[23],advdata[24],advdata[25],advdata[26],advdata[27],advdata[28],advdata[29]);}
        strcpy(B2_MAC_Addr, bwc_address.addr);// MAC address

        // check header first
        if(check_B2_header() != 1 || advdata[0] == 0 || evt->data.evt_scanner_scan_report.data.len < 25)
        //if(check_B2_header() != 1)
          break;


        for(int i=1;i<10;i++)
        {
          if(compare_GroupName(i) == 0)
          {
            Store_MAC_to_B2_Devices_List();
            //Store_MAC_to_B3_Devices_List();
              //printf("****MAC = %x:%x:%x:%x:%x:%x", address.addr[0],address.addr[1],address.addr[2],address.addr[3],address.addr[4],address.addr[5]);
              //printf("****B2 = len=%d, %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x %x\r\n", evt->data.evt_le_gap_scan_response.data.len,advdata[0],advdata[1],advdata[2],advdata[3],advdata[4],advdata[5],advdata[6],advdata[7]
              //,advdata[8],advdata[9],advdata[10],advdata[11],advdata[12],advdata[13],advdata[14],advdata[15],advdata[16]
              //,advdata[17],advdata[18],advdata[19],advdata[20],advdata[21],advdata[22],advdata[23],advdata[24]
              //,advdata[25],advdata[26],advdata[27],advdata[28],advdata[29],advdata[30]);
            break;
          }
        }

        break;


    // -------------------------------
    // This event indicates that a new connection was opened.
    case sl_bt_evt_connection_opened_id:
      printf("**** sl_bt_evt_connection_opened_id ****\r\n");
      configured = false;
      break;

    // -------------------------------
    // This event indicates that a connection was closed.
    case sl_bt_evt_connection_closed_id:
      printf("**** sl_bt_evt_connection_closed_id ****\r\n");
      // Restart advertising after client has disconnected.
#if !D_TB03
      if (false == configured)
      {
          set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(60*second,23,1);
      }
#else
      set_pcsniffer_advdata_packet();
#endif
      /*sc = sl_bt_advertiser_start(
        advertising_set_handle,
        sl_bt_advertiser_general_discoverable,
        sl_bt_advertiser_connectable_scannable);
      app_assert_status(sc);*/
      break;

    case sl_bt_evt_gatt_server_attribute_value_id:
      //printf("gecko_evt_gatt_server_characteristic_status_id = %d\r\n", evt->data.evt_gatt_server_attribute_value.attribute);
      if (evt->data.evt_gatt_server_attribute_value.attribute == gattdb_tx_power)
      {
          printf("tx power is set to: = %2x%2x\r\n", evt->data.evt_gatt_server_attribute_value.value.data[0], evt->data.evt_gatt_server_attribute_value.value.data[1]);
          txpower_buf[0] = evt->data.evt_gatt_server_attribute_value.value.data[0];
          txpower_buf[1] = evt->data.evt_gatt_server_attribute_value.value.data[1];
          txpower = evt->data.evt_gatt_server_attribute_value.value.data[0] << 8;
          txpower = txpower | evt->data.evt_gatt_server_attribute_value.value.data[1];
          //adjust_bgm111_tx_power(txpower);
          sl_bt_nvm_save(0x4008,evt->data.evt_gatt_server_user_write_request.value.len,evt->data.evt_gatt_server_user_write_request.value.data);
          break;
      }
      break;

    ///////////////////////////////////////////////////////////////////////////
    // Add additional event handlers here as your application requires!      //
    ///////////////////////////////////////////////////////////////////////////
    case sl_bt_evt_gatt_server_user_read_request_id:

      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_get_tx_power)
      {
          ret = sl_bt_nvm_load(0x4008,10,&read_len,(uint8_t*)user_read_response_buf);
          if(SL_STATUS_OK == ret)
          {
            txpower_buf[0] = user_read_response_buf[0];
            txpower_buf[1] = user_read_response_buf[1];
          }
          // send back "success" response packet with value manually (GATT structure has `type="user"` set)
          sl_bt_gatt_server_send_user_read_response(
          evt->data.evt_gatt_server_user_read_request.connection,
          evt->data.evt_gatt_server_user_read_request.characteristic,
          SL_STATUS_OK, /* SUCCESS */
          0x02,
          txpower_buf,
          0 /* unused */);
          printf("user_read_request tx power is: = %2x%2x\r\n", txpower_buf[0], txpower_buf[1]);
          break;
      }
      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_SYS_Serial_Number)
      {
        ret = sl_bt_nvm_load(0x4002,10,&read_len,(uint8_t*)user_read_response_buf);
        if(SL_STATUS_OK != ret)
        {memcpy(user_read_response_buf, "9999999999", 10);}
        // send back "success" response packet with value manually (GATT structure has `type="user"` set)
        sl_bt_gatt_server_send_user_read_response(
        evt->data.evt_gatt_server_user_read_request.connection,
        evt->data.evt_gatt_server_user_read_request.characteristic,
        SL_STATUS_OK, /* SUCCESS */
        10,
        user_read_response_buf,
        0 /* unused */);
        printf("user_read_request SYS_Serial_Number = %s\r\n", user_read_response_buf);
        break;
      }
      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_sniffer_mesh)
      {
          ret = sl_bt_nvm_load(0x400e,10,&read_len,(uint8_t*)user_read_response_buf);
          if(SL_STATUS_OK == ret)
          {
              sniffer_mesh = user_read_response_buf[0];
          }
          else
          {
            memset(user_read_response_buf, 0, 10);
            memcpy(user_read_response_buf, &sniffer_mesh, 1);
          }
          sl_bt_gatt_server_send_user_read_response(
          evt->data.evt_gatt_server_user_read_request.connection,
          evt->data.evt_gatt_server_user_read_request.characteristic,
          SL_STATUS_OK, /* SUCCESS */
          0x01,
          user_read_response_buf,
          0 /* unused */);
          printf("user_read_request sniffer_mesh = %x\r\n", sniffer_mesh);
          break;
      }
      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_transmit_duration)
      {
        ret = sl_bt_nvm_load(0x400a,10,&read_len,(uint8_t*)user_read_response_buf);
        if(SL_STATUS_OK == ret)
        {
          transmit_duration_buf = user_read_response_buf[0] << 8;
          transmit_duration_buf = transmit_duration_buf | user_read_response_buf[1];
        }
        else
        {
          user_read_response_buf[0] = transmit_duration_buf >> 8 & 0xFF;
          user_read_response_buf[1] = transmit_duration_buf & 0xFF;
        }
        // send back "success" response packet with value manually (GATT structure has `type="user"` set)
        sl_bt_gatt_server_send_user_read_response(
        evt->data.evt_gatt_server_user_read_request.connection,
        evt->data.evt_gatt_server_user_read_request.characteristic,
        SL_STATUS_OK, /* SUCCESS */
        2,
        user_read_response_buf,
        0 /* unused */);
        printf("user_read_request transmit_duration_buf = %x\r\n", transmit_duration_buf);
        break;
      }
      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_trig_delay)
      {
        ret = sl_bt_nvm_load(0x4009,10,&read_len,(uint8_t*)user_read_response_buf);
        if(SL_STATUS_OK == ret)
        {
            trig_delay_buf = user_read_response_buf[0];
        }
        else
        {
          user_read_response_buf[0] = trig_delay_buf;
        }
        // send back "success" response packet with value manually (GATT structure has `type="user"` set)
        sl_bt_gatt_server_send_user_read_response(
        evt->data.evt_gatt_server_user_read_request.connection,
        evt->data.evt_gatt_server_user_read_request.characteristic,
        SL_STATUS_OK, /* SUCCESS */
        1,
        user_read_response_buf,
        0 /* unused */);
        printf("user_read_request trig_delay_buf = %x\r\n", trig_delay_buf);
        break;
      }
      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_gpin_andop_pins)
      {
          memset(user_read_response_buf, 0, 10);
          ret = sl_bt_nvm_load(0x400c,10,&read_len,(uint8_t*)user_read_response_buf);
          if(SL_STATUS_OK == ret)
          {
            gpin_andop_pins_buf = user_read_response_buf[0];
          }
          else
          {
          memset(user_read_response_buf, 0, 10);
          memcpy(user_read_response_buf, &gpin_andop_pins_buf, 1);
          }
        // send back "success" response packet with value manually (GATT structure has `type="user"` set)
          sl_bt_gatt_server_send_user_read_response(
          evt->data.evt_gatt_server_user_read_request.connection,
          evt->data.evt_gatt_server_user_read_request.characteristic,
          SL_STATUS_OK, /* SUCCESS */
          1,
          user_read_response_buf,
          0 /* unused */);
          printf("user_read_request gpin_andop_pins_buf = %x\r\n", gpin_andop_pins_buf);
          break;
      }
      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_gpin_stopcmd_pins)
      {
          memset(user_read_response_buf, 0, 10);
          ret = sl_bt_nvm_load(0x400d,10,&read_len,(uint8_t*)user_read_response_buf);
          if(SL_STATUS_OK == ret)
          {
            gpin_stopcmd_pins_buf = user_read_response_buf[0];
          }
          else
          {
          memset(user_read_response_buf, 0, 10);
          memcpy(user_read_response_buf, &gpin_stopcmd_pins_buf, 1);
          }
        // send back "success" response packet with value manually (GATT structure has `type="user"` set)
          sl_bt_gatt_server_send_user_read_response(
          evt->data.evt_gatt_server_user_read_request.connection,
          evt->data.evt_gatt_server_user_read_request.characteristic,
          SL_STATUS_OK, /* SUCCESS */
          1,
          user_read_response_buf,
          0 /* unused */);
          printf("user_read_request gpin_stopcmd_pins_buf = %x\r\n", gpin_stopcmd_pins_buf);
          break;
      }
      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_local_name_1)
      {
        memset(user_read_response_buf, 0, 10);
        ret = sl_bt_nvm_load(0x4003,6,&read_len,(uint8_t*)user_read_response_buf);
        if (SL_STATUS_OK  == ret)
        {
          memset(groupName01, 0, 6);
          memcpy(groupName01, user_read_response_buf, strlen(user_read_response_buf));
        }
        // send back "success" response packet with value manually (GATT structure has `type="user"` set)
        sl_bt_gatt_server_send_user_read_response(
        evt->data.evt_gatt_server_user_read_request.connection,
        evt->data.evt_gatt_server_user_read_request.characteristic,
        SL_STATUS_OK, /* SUCCESS */
        6,
        groupName01,
        0 /* unused */);
        printf("user_read_request groupName01 = %s, len = %d\r\n", groupName01, strlen(groupName01));
        break;
      }
      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_local_name_2)
      {
          memset(user_read_response_buf, 0, 10);
          ret = sl_bt_nvm_load(0x4004,6,&read_len,(uint8_t*)user_read_response_buf);
          if (SL_STATUS_OK  == ret)
          {
            memset(groupName02, 0, 6);
            memcpy(groupName02, user_read_response_buf, strlen(user_read_response_buf));
          }
          // send back "success" response packet with value manually (GATT structure has `type="user"` set)
          sl_bt_gatt_server_send_user_read_response(
          evt->data.evt_gatt_server_user_read_request.connection,
          evt->data.evt_gatt_server_user_read_request.characteristic,
          SL_STATUS_OK, /* SUCCESS */
          6,
          groupName02,
          0 /* unused */);
          printf("user_read_request groupName02 = %s, len = %d\r\n", groupName02, strlen(groupName02));
          break;
      }
      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_local_name_3)
      {
          memset(user_read_response_buf, 0, 10);
          ret = sl_bt_nvm_load(0x4005,6,&read_len,(uint8_t*)user_read_response_buf);
          if (SL_STATUS_OK  == ret)
          {
            memset(groupName03, 0, 6);
            memcpy(groupName03, user_read_response_buf, strlen(user_read_response_buf));
          }
          // send back "success" response packet with value manually (GATT structure has `type="user"` set)
          sl_bt_gatt_server_send_user_read_response(
          evt->data.evt_gatt_server_user_read_request.connection,
          evt->data.evt_gatt_server_user_read_request.characteristic,
          SL_STATUS_OK, /* SUCCESS */
          6,
          groupName03,
          0 /* unused */);
          printf("user_read_request groupName03 = %s, len = %d\r\n", groupName03, strlen(groupName03));
          break;
      }
      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_local_name_4)
      {
          memset(user_read_response_buf, 0, 10);
          ret = sl_bt_nvm_load(0x4006,6,&read_len,(uint8_t*)user_read_response_buf);
          if (SL_STATUS_OK  == ret)
          {
            memset(groupName04, 0, 6);
            memcpy(groupName04, user_read_response_buf, strlen(user_read_response_buf));
          }
          // send back "success" response packet with value manually (GATT structure has `type="user"` set)
          sl_bt_gatt_server_send_user_read_response(
          evt->data.evt_gatt_server_user_read_request.connection,
          evt->data.evt_gatt_server_user_read_request.characteristic,
          SL_STATUS_OK, /* SUCCESS */
          6,
          groupName04,
          0 /* unused */);
          printf("user_read_request groupName04 = %s, len = %d\r\n", groupName04, strlen(groupName04));
          break;
      }
      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_local_name_5)
      {
          memset(user_read_response_buf, 0, 10);
          ret = sl_bt_nvm_load(0x4007,6,&read_len,(uint8_t*)user_read_response_buf);
          if (SL_STATUS_OK  == ret)
          {
            memset(groupName05, 0, 6);
            memcpy(groupName05, user_read_response_buf, strlen(user_read_response_buf));
          }
          // send back "success" response packet with value manually (GATT structure has `type="user"` set)
          sl_bt_gatt_server_send_user_read_response(
          evt->data.evt_gatt_server_user_read_request.connection,
          evt->data.evt_gatt_server_user_read_request.characteristic,
          SL_STATUS_OK, /* SUCCESS */
          6,
          groupName05,
          0 /* unused */);
          printf("user_read_request groupName05 = %s, len = %d\r\n", groupName05, strlen(groupName05));
          break;
      }
      if (evt->data.evt_gatt_server_user_read_request.characteristic == gattdb_battery_voltage)
      {
        memset(user_read_response_buf, 0, 10);
        user_read_response_buf[0] = PD2_ADC_Value >> 8 & 0xFF;
        user_read_response_buf[1] = PD2_ADC_Value & 0xFF;
        // send back "success" response packet with value manually (GATT structure has `type="user"` set)
        sl_bt_gatt_server_send_user_read_response(
        evt->data.evt_gatt_server_user_read_request.connection,
        evt->data.evt_gatt_server_user_read_request.characteristic,
        SL_STATUS_OK, /* SUCCESS */
        2,
        user_read_response_buf,
        0 /* unused */);
        printf("user_read_request PC6_ADC_Value = %d\r\n", PD2_ADC_Value);
        break;
      }


    case sl_bt_evt_gatt_server_user_write_request_id:

      if (evt->data.evt_gatt_server_user_write_request.characteristic == gattdb_sniffer_mesh)
      {
          sl_bt_nvm_save(0x400e,evt->data.evt_gatt_server_user_write_request.value.len,evt->data.evt_gatt_server_user_write_request.value.data);
          sniffer_mesh = evt->data.evt_gatt_server_user_write_request.value.data[0];

          /* Send response to Write Request */
          sl_bt_gatt_server_send_user_write_response(
          evt->data.evt_gatt_server_user_write_request.connection,
          gattdb_sniffer_mesh,
          SL_STATUS_OK);
          printf("user_write_request sniffer_mesh = %x\r\n", sniffer_mesh);
          break;
      }
      if (evt->data.evt_gatt_server_user_write_request.characteristic == gattdb_transmit_duration)
      {
          sl_bt_nvm_save(0x400a,evt->data.evt_gatt_server_user_write_request.value.len,evt->data.evt_gatt_server_user_write_request.value.data);
          transmit_duration_buf = evt->data.evt_gatt_server_user_write_request.value.data[0] << 8;
          transmit_duration_buf = transmit_duration_buf | evt->data.evt_gatt_server_user_write_request.value.data[1];

          /* Send response to Write Request */
          sl_bt_gatt_server_send_user_write_response(
          evt->data.evt_gatt_server_user_write_request.connection,
          gattdb_transmit_duration,
          SL_STATUS_OK);
          printf("user_write_request transmit_duration_buf = %x\r\n", transmit_duration_buf);
          break;
      }
      if (evt->data.evt_gatt_server_user_write_request.characteristic == gattdb_trig_delay)
      {
          sl_bt_nvm_save(0x4009,evt->data.evt_gatt_server_user_write_request.value.len,evt->data.evt_gatt_server_user_write_request.value.data);
          trig_delay_buf = evt->data.evt_gatt_server_user_write_request.value.data[0];

          /* Send response to Write Request */
          sl_bt_gatt_server_send_user_write_response(
          evt->data.evt_gatt_server_user_write_request.connection,
          gattdb_trig_delay,
          SL_STATUS_OK);
          printf("user_write_request trig_delay_buf = %x\r\n", trig_delay_buf);
          break;
      }
      if (evt->data.evt_gatt_server_user_write_request.characteristic == gattdb_gpin_andop_pins)
      {
          sl_bt_nvm_save(0x400c,evt->data.evt_gatt_server_user_write_request.value.len,evt->data.evt_gatt_server_user_write_request.value.data);
          gpin_andop_pins_buf = evt->data.evt_gatt_server_user_write_request.value.data[0];

          /* Send response to Write Request */
          sl_bt_gatt_server_send_user_write_response(
          evt->data.evt_gatt_server_user_write_request.connection,
          gattdb_gpin_andop_pins,
          SL_STATUS_OK);
          printf("user_write_request gpin_andop_pins_buf = %x\r\n", gpin_andop_pins_buf);
          break;
      }
      if (evt->data.evt_gatt_server_user_write_request.characteristic == gattdb_gpin_stopcmd_pins)
      {
          sl_bt_nvm_save(0x400d,evt->data.evt_gatt_server_user_write_request.value.len,evt->data.evt_gatt_server_user_write_request.value.data);
          gpin_stopcmd_pins_buf = evt->data.evt_gatt_server_user_write_request.value.data[0];

          /* Send response to Write Request */
          sl_bt_gatt_server_send_user_write_response(
          evt->data.evt_gatt_server_user_write_request.connection,
          gattdb_gpin_stopcmd_pins,
          SL_STATUS_OK);
          printf("user_write_request gpin_stopcmd_pins_buf = %x\r\n", gpin_stopcmd_pins_buf);
          break;
      }
      if (evt->data.evt_gatt_server_user_write_request.characteristic == gattdb_local_name_1)
      {
        configured = true;
        sl_bt_nvm_save(0x4003,evt->data.evt_gatt_server_user_write_request.value.len,evt->data.evt_gatt_server_user_write_request.value.data);
        memset(groupName01, 0, 6);
        memcpy(groupName01, evt->data.evt_gatt_server_user_write_request.value.data, evt->data.evt_gatt_server_user_write_request.value.len);

        /* Send response to Write Request */
        sl_bt_gatt_server_send_user_write_response(
        evt->data.evt_gatt_server_user_write_request.connection,
        gattdb_local_name_1,
        SL_STATUS_OK);
        printf("user_write_request groupName01 = %s, len = %d\r\n", groupName01, sizeof(groupName01));
        sl_udelay_wait(100);
        break;
      }
      if (evt->data.evt_gatt_server_user_write_request.characteristic == gattdb_local_name_2)
      {
        configured = true;
        sl_bt_nvm_save(0x4004,evt->data.evt_gatt_server_user_write_request.value.len,evt->data.evt_gatt_server_user_write_request.value.data);
        memset(groupName02, 0, 6);
        memcpy(groupName02, evt->data.evt_gatt_server_user_write_request.value.data, evt->data.evt_gatt_server_user_write_request.value.len);

        /* Send response to Write Request */
        sl_bt_gatt_server_send_user_write_response(
        evt->data.evt_gatt_server_user_write_request.connection,
        gattdb_local_name_2,
        SL_STATUS_OK);
        printf("user_write_request groupName02 = %s, len = %d\r\n", groupName02, sizeof(groupName02));
        sl_udelay_wait(100);
        break;
      }
      if (evt->data.evt_gatt_server_user_write_request.characteristic == gattdb_local_name_3)
      {
        configured = true;
        sl_bt_nvm_save(0x4005,evt->data.evt_gatt_server_user_write_request.value.len,evt->data.evt_gatt_server_user_write_request.value.data);
        memset(groupName03, 0, 6);
        memcpy(groupName03, evt->data.evt_gatt_server_user_write_request.value.data, evt->data.evt_gatt_server_user_write_request.value.len);

        /* Send response to Write Request */
        sl_bt_gatt_server_send_user_write_response(
        evt->data.evt_gatt_server_user_write_request.connection,
        gattdb_local_name_3,
        SL_STATUS_OK);
        printf("user_write_request groupName03 = %s, len = %d\r\n", groupName03, sizeof(groupName03));
        sl_udelay_wait(100);
        break;
      }
      if (evt->data.evt_gatt_server_user_write_request.characteristic == gattdb_local_name_4)
      {
        configured = true;
        sl_bt_nvm_save(0x4006,evt->data.evt_gatt_server_user_write_request.value.len,evt->data.evt_gatt_server_user_write_request.value.data);
        memset(groupName04, 0, 6);
        memcpy(groupName04, evt->data.evt_gatt_server_user_write_request.value.data, evt->data.evt_gatt_server_user_write_request.value.len);

        /* Send response to Write Request */
        sl_bt_gatt_server_send_user_write_response(
        evt->data.evt_gatt_server_user_write_request.connection,
        gattdb_local_name_4,
        SL_STATUS_OK);
        printf("user_write_request groupName04 = %s, len = %d\r\n", groupName04, sizeof(groupName04));
        sl_udelay_wait(100);
        break;
      }
      if (evt->data.evt_gatt_server_user_write_request.characteristic == gattdb_local_name_5)
      {
        configured = true;
        sl_bt_nvm_save(0x4007,evt->data.evt_gatt_server_user_write_request.value.len,evt->data.evt_gatt_server_user_write_request.value.data);
        memset(groupName05, 0, 6);
        memcpy(groupName05, evt->data.evt_gatt_server_user_write_request.value.data, evt->data.evt_gatt_server_user_write_request.value.len);

        /* Send response to Write Request */
        sl_bt_gatt_server_send_user_write_response(
        evt->data.evt_gatt_server_user_write_request.connection,
        gattdb_local_name_5,
        SL_STATUS_OK);
        printf("user_write_request groupName05 = %s, len = %d\r\n", groupName05, sizeof(groupName05));
        sl_udelay_wait(100);
        break;
      }

    case sl_bt_evt_system_soft_timer_id:

      if (evt->data.evt_system_soft_timer.handle == 0)
      {
        printf("handle == 0\r\n");
        set_pcsniffer_advdata_packet();

        break;
      }

      if (evt->data.evt_system_soft_timer.handle == 1)
      {
          printf("handle == 1\r\n");
          singleInput.posInput   = iadcPosInputPortAPin6;
          singleInput.negInput   = iadcNegInputGnd;

          // Allocate the analog bus for ADC0 inputs
          GPIO->CDBUSALLOC |= GPIO_CDBUSALLOC_CDEVEN0_ADC0;

          // Initialize IADC
          IADC_init(IADC0, &init, &initAllConfigs);

          // Initialize a single-channel conversion
          IADC_initSingle(IADC0, &initSingle, &singleInput);

          // Start IADC conversion
          IADC_command(IADC0, iadcCmdStartSingle);

          // Wait for conversion to be complete
          while((IADC0->STATUS & (_IADC_STATUS_CONVERTING_MASK
                      | _IADC_STATUS_SINGLEFIFODV_MASK)) != IADC_STATUS_SINGLEFIFODV); //while combined status bits 8 & 6 don't equal 1 and 0 respectively

          // Get ADC result
          //sample = IADC_pullSingleFifoResult(IADC0).data;
          // Read a result from the FIFO
          sample = IADC_pullSingleFifoResult(IADC0);

          // Calculate input voltage:
          //  For differential inputs, the resultant range is from -Vref to +Vref, i.e.,
          //  for Vref = AVDD = 3.30V, 12 bits represents 6.60V full scale IADC range.
          battvolts = (sample.data *3300)/0xfff;
          printf("volts = %dmV\r\n",battvolts);

          singleInput.posInput   = iadcPosInputPortDPin2;
          singleInput.negInput   = iadcNegInputGnd;

          // Allocate the analog bus for ADC0 inputs
          GPIO->ABUSALLOC |= GPIO_ABUSALLOC_AEVEN0_ADC0;

          // Initialize IADC
          IADC_init(IADC0, &init, &initAllConfigs);

          // Initialize a single-channel conversion
          IADC_initSingle(IADC0, &initSingle, &singleInput);

          IADC_command(IADC0, iadcCmdStartSingle);
          // Wait for conversion to be complete
          while((IADC0->STATUS & (_IADC_STATUS_CONVERTING_MASK
                      | _IADC_STATUS_SINGLEFIFODV_MASK)) != IADC_STATUS_SINGLEFIFODV); //while combined status bits 8 & 6 don't equal 1 and 0 respectively
          sample = IADC_pullSingleFifoResult(IADC0);
          battvolts = (sample.data *3300)/0xfff;
          printf("volts = %dmV\r\n",battvolts);

        break;
      }

      if (evt->data.evt_system_soft_timer.handle == 2)
      {
          printf("***********handle == 2, %d***********\r\n", local_name_index);
#if D_TB03
        read_gpin_high_low_status();
        b3_trigcmd[1] = read_current_gpin;
#endif
        if (local_name_index == 1)
        {
          if(compare_default_GroupName(local_name_index) != 0)
          {
              memset(bwcb3AdvData.groupName, 0, 6);
              memcpy(bwcb3AdvData.groupName, groupName01, 6);
              memset(bwcb3AdvData.EventStatus, 0, 2);
              memcpy(bwcb3AdvData.EventStatus, b3_trigcmd, 2);
              set_non_connectable_b3_packet();
              local_name_index++;
              break;
          }
          else
          {local_name_index++;}
        }
        if (local_name_index == 2)
        {
          if(compare_default_GroupName(1) != 0)
          {
              memset(bwcb2AdvData.groupName, 0, 6);
              memcpy(bwcb2AdvData.groupName, groupName01, 6);
              memset(bwcb2AdvData.cmd, 0, 4);
              memcpy(bwcb2AdvData.cmd, b2_trigcmd, 4);
              //memcpy(bwcb2AdvData.cmd, mutecmd, 4);
              //memcpy(bwcb2AdvData.cmd, audiocmd, 4);
              set_non_connectable_b2_packet();
              local_name_index++;
              break;
          }
          else
          {local_name_index++;}
        }
        if (local_name_index == 3)
        {
          if(compare_default_GroupName(2) != 0)
          {
              memset(bwcb3AdvData.groupName, 0, 6);
              memcpy(bwcb3AdvData.groupName, groupName02, 6);
              memset(bwcb3AdvData.EventStatus, 0, 2);
              memcpy(bwcb3AdvData.EventStatus, b3_trigcmd, 2);
              set_non_connectable_b3_packet();
              local_name_index++;
              break;
          }
          else
          {local_name_index++;}
        }
        if (local_name_index == 4)
        {
          if(compare_default_GroupName(2) != 0)
          {
              memset(bwcb2AdvData.groupName, 0, 6);
              memcpy(bwcb2AdvData.groupName, groupName02, 6);
              memset(bwcb2AdvData.cmd, 0, 4);
              memcpy(bwcb2AdvData.cmd, b2_trigcmd, 4);
              set_non_connectable_b2_packet();
              local_name_index++;
              break;
          }
          else
          {local_name_index++;}
        }
        if (local_name_index == 5)
        {
          if(compare_default_GroupName(3) != 0)
          {
              memset(bwcb3AdvData.groupName, 0, 6);
              memcpy(bwcb3AdvData.groupName, groupName03, 6);
              memset(bwcb3AdvData.EventStatus, 0, 2);
              memcpy(bwcb3AdvData.EventStatus, b3_trigcmd, 2);
              set_non_connectable_b3_packet();
              local_name_index++;
              break;
          }
          else
          {local_name_index++;}
        }
        if (local_name_index == 6)
        {
          if(compare_default_GroupName(3) != 0)
          {
              memset(bwcb2AdvData.groupName, 0, 6);
              memcpy(bwcb2AdvData.groupName, groupName03, 6);
              memset(bwcb2AdvData.cmd, 0, 4);
              memcpy(bwcb2AdvData.cmd, b2_trigcmd, 4);
              set_non_connectable_b2_packet();
              local_name_index++;
              break;
          }
          else
          {local_name_index++;}
        }
        if (local_name_index == 7)
        {
          if(compare_default_GroupName(4) != 0)
          {
              memset(bwcb3AdvData.groupName, 0, 6);
              memcpy(bwcb3AdvData.groupName, groupName04, 6);
              memset(bwcb3AdvData.EventStatus, 0, 2);
              memcpy(bwcb3AdvData.EventStatus, b3_trigcmd, 2);
              set_non_connectable_b3_packet();
              local_name_index++;
              break;
          }
          else
          {local_name_index++;}
        }
        if (local_name_index == 8)
        {
          if(compare_default_GroupName(4)!= 0)
          {
              memset(bwcb2AdvData.groupName, 0, 6);
              memcpy(bwcb2AdvData.groupName, groupName04, 6);
              memset(bwcb2AdvData.cmd, 0, 4);
              memcpy(bwcb2AdvData.cmd, b2_trigcmd, 4);
              set_non_connectable_b2_packet();
              local_name_index++;
              break;
          }
          else
          {local_name_index++;}
        }
        if (local_name_index == 9)
        {
          if(compare_default_GroupName(5) != 0)
          {
              memset(bwcb3AdvData.groupName, 0, 6);
              memcpy(bwcb3AdvData.groupName, groupName05, 6);
              memset(bwcb3AdvData.EventStatus, 0, 2);
              memcpy(bwcb3AdvData.EventStatus, b3_trigcmd, 2);
              set_non_connectable_b3_packet();
              local_name_index++;
              break;
          }
          else
          {local_name_index++;}
        }
        if (local_name_index == 10)
        {
          if(compare_default_GroupName(5) != 0)
          {
              memset(bwcb2AdvData.groupName, 0, 6);
              memcpy(bwcb2AdvData.groupName, groupName05, 6);
              memset(bwcb2AdvData.cmd, 0, 4);
              memcpy(bwcb2AdvData.cmd, b2_trigcmd, 4);
              set_non_connectable_b2_packet();
              local_name_index=1;
              break;
          }
          else
          {local_name_index=1;}
        }
      }

      if (evt->data.evt_system_soft_timer.handle == 3)
      {
        printf("***********handle == 3, %d***********\r\n", local_name_index);
#if D_TB03
        read_gpin_high_low_status();
        b3_stopcmd[1] = read_current_gpin;
#endif
        if (local_name_index == 1)
        {
          if(compare_default_GroupName(local_name_index) != 0)
          {
              memset(bwcb3AdvData.groupName, 0, 6);
              memcpy(bwcb3AdvData.groupName, groupName01, 6);
              memset(bwcb3AdvData.EventStatus, 0, 2);
              memcpy(bwcb3AdvData.EventStatus, b3_stopcmd, 2);
              set_non_connectable_b3_packet();
              local_name_index++;
            break;
          }
          else
          {
              local_name_index++;
          }
        }
        if (local_name_index == 2)
        {
          if(compare_default_GroupName(1) != 0)
          {
              memset(bwcb2AdvData.groupName, 0, 6);
              memcpy(bwcb2AdvData.groupName, groupName01, 6);
              memset(bwcb2AdvData.cmd, 0, 4);
              memcpy(bwcb2AdvData.cmd, b2_stopcmd, 4);
              set_non_connectable_b2_packet();
              local_name_index++;
              break;
          }
          else
          {
              local_name_index++;
          }
        }
        if (local_name_index == 3)
        {
          if(compare_default_GroupName(2) != 0)
          {
              memset(bwcb3AdvData.groupName, 0, 6);
              memcpy(bwcb3AdvData.groupName, groupName02, 6);
              memset(bwcb3AdvData.EventStatus, 0, 2);
              memcpy(bwcb3AdvData.EventStatus, b3_stopcmd, 2);
              set_non_connectable_b3_packet();
              local_name_index++;
              break;
          }
          else
          {
              local_name_index++;
          }
        }
        if (local_name_index == 4)
        {
          if(compare_default_GroupName(2) != 0)
          {
              memset(bwcb2AdvData.groupName, 0, 6);
              memcpy(bwcb2AdvData.groupName, groupName02, 6);
              memset(bwcb2AdvData.cmd, 0, 4);
              memcpy(bwcb2AdvData.cmd, b2_stopcmd, 4);
              set_non_connectable_b2_packet();
              local_name_index++;
              break;
          }
          else
          {
              local_name_index++;
          }
        }
        if (local_name_index == 5)
        {
          if(compare_default_GroupName(3) != 0)
          {
              memset(bwcb3AdvData.groupName, 0, 6);
              memcpy(bwcb3AdvData.groupName, groupName03, 6);
              memset(bwcb3AdvData.EventStatus, 0, 2);
              memcpy(bwcb3AdvData.EventStatus, b3_stopcmd, 2);
              set_non_connectable_b3_packet();
              local_name_index++;
              break;
          }
          else
          {
              local_name_index++;
          }
        }
        if (local_name_index == 6)
        {
          if(compare_default_GroupName(3) != 0)
          {
              memset(bwcb2AdvData.groupName, 0, 6);
              memcpy(bwcb2AdvData.groupName, groupName03, 6);
              memset(bwcb2AdvData.cmd, 0, 4);
              memcpy(bwcb2AdvData.cmd, b2_stopcmd, 4);
              set_non_connectable_b2_packet();
              local_name_index++;
              break;
          }
          else
          {
              local_name_index++;
          }
        }
        if (local_name_index == 7)
        {
          if(compare_default_GroupName(4) != 0)
          {
              memset(bwcb3AdvData.groupName, 0, 6);
              memcpy(bwcb3AdvData.groupName, groupName04, 6);
              memset(bwcb3AdvData.EventStatus, 0, 2);
              memcpy(bwcb3AdvData.EventStatus, b3_stopcmd, 2);
              set_non_connectable_b3_packet();
              local_name_index++;
              break;
          }
          else
          {
              local_name_index++;
          }
        }
        if (local_name_index == 8)
        {
          if(compare_default_GroupName(4) != 0)
          {
              memset(bwcb2AdvData.groupName, 0, 6);
              memcpy(bwcb2AdvData.groupName, groupName04, 6);
              memset(bwcb2AdvData.cmd, 0, 4);
              memcpy(bwcb2AdvData.cmd, b2_stopcmd, 4);
              set_non_connectable_b2_packet();
              local_name_index++;
              break;
          }
          else
          {
              local_name_index++;
          }
        }
        if (local_name_index == 9)
        {
          if(compare_default_GroupName(5) != 0)
          {
              memset(bwcb3AdvData.groupName, 0, 6);
              memcpy(bwcb3AdvData.groupName, groupName05, 6);
              memset(bwcb3AdvData.EventStatus, 0, 2);
              memcpy(bwcb3AdvData.EventStatus, b3_stopcmd, 2);
              set_non_connectable_b3_packet();
              local_name_index++;
              break;
          }
          else
          {
              local_name_index++;
          }
        }
        if (local_name_index == 10)
        {
          if(compare_default_GroupName(5) != 0)
          {
              memset(bwcb2AdvData.groupName, 0, 6);
              memcpy(bwcb2AdvData.groupName, groupName05, 6);
              memset(bwcb2AdvData.cmd, 0, 4);
              memcpy(bwcb2AdvData.cmd, b2_stopcmd, 4);
              set_non_connectable_b2_packet();
              local_name_index=1;
              break;
          }
          else
          {local_name_index=1;}
        }
      }

      /*if (evt->data.evt_system_soft_timer.handle == 3)
      {
          printf("handle == 3\r\n");
          //stop trigger BWCS
          //stop_trigger_BWCS();
#if D_WDOG
          start_detect(1);
          plugin_detect(1);
#endif
          //DC-IN do not enter EM2
          //if(!GPIO_PinInGet(gpioPortF, 7))
          //GPIO_PinModeSet(gpioPortC,  7, gpioModeDisabled, 0);
          //GPIO_PinModeSet(gpioPortC,  8, gpioModeDisabled, 0);
          if(dcin == 0)
          {
            //GPIO_PinModeSet(gpioPortD,  9, gpioModeDisabled, 0);
            //GPIO_PinModeSet(gpioPortD, 12, gpioModeDisabled, 0);

            //GPIO_PinModeSet(gpioPortF, 2, gpioModeDisabled, 1);
            //GPIO_PinModeSet(gpioPortF, 3, gpioModeDisabled, 1);
            //{EMU_EnterEM2(true);}
           }
           //start_detect(1);
           break;
      }*/


      if (evt->data.evt_system_soft_timer.handle == 4)
      {

        printf("***********handle == 4***********\r\n");
        trigger_duration_is_on = 0;

        //remove handle = 2 timer
        sl_bt_system_set_soft_timer(0,2,0);

#if !D_TB03
        if(!boot)
        {sl_bt_advertiser_stop(advertising_set_handle);}
        else
        {boot = false;}
        //red led off
        //red_led_on(0);
#if D_WDOG
        start_detect(1);
        plugin_detect(1);
#endif
#else
        set_pcsniffer_advdata_packet();

        //green led on
        green_led_on(1);
#endif

        //drive the PC2 to Low
        GPIO_PortOutClear(gpioPortC, 0x0004);

        //GPIN wake up source make it into sleep mode again
        GPIN_wakeup = 0;
        break;
      }

      if (evt->data.evt_system_soft_timer.handle == 55)
      {
        printf("handle == 5, BTN_TIMER_CNT: %d\r\n", BTN_TIMER_CNT);
        if(BTN_TIMER_CNT>=1)
        {
          red_led_blink(5);
          set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(60*second,23,1);

          GetCoinVol();
        }
        break;
       }

      if (evt->data.evt_system_soft_timer.handle == 5)
      {
        //printf("***********handle == 5***********\r\n");
#if !D_TB03
        //read ADC PD2 for Coin battery
        singleInput.posInput   = iadcPosInputPortDPin2;
        singleInput.negInput   = iadcNegInputGnd;

        // Allocate the analog bus for ADC0 inputs
        GPIO->CDBUSALLOC |= GPIO_CDBUSALLOC_CDEVEN0_ADC0;

        // Initialize IADC
        IADC_init(IADC0, &init, &initAllConfigs);

        // Initialize a single-channel conversion
        IADC_initSingle(IADC0, &initSingle, &singleInput);

        // Start IADC conversion
        IADC_command(IADC0, iadcCmdStartSingle);

        // Wait for conversion to be complete
        while((IADC0->STATUS & (_IADC_STATUS_CONVERTING_MASK
                    | _IADC_STATUS_SINGLEFIFODV_MASK)) != IADC_STATUS_SINGLEFIFODV); //while combined status bits 8 & 6 don't equal 1 and 0 respectively

        // Get ADC result
        //sample = IADC_pullSingleFifoResult(IADC0).data;
        // Read a result from the FIFO
        sample = IADC_pullSingleFifoResult(IADC0);

        // Calculate input voltage:
        //  For differential inputs, the resultant range is from -Vref to +Vref, i.e.,
        //  for Vref = AVDD = 1.20V, 12 bits represents 3.3V/3 full scale IADC range.
        PC6_ADC_Value = (sample.data *1210*2*3)/0xfff;
        //PC6_ADC_Value = sample.data;
        printf("sample.data = %d,  volts = %dmV\r\n",sample.data,PC6_ADC_Value);
#else
        //updateCalendar();
        //read ADC PD2 for Coin battery
        singleInput.posInput   = iadcPosInputPortDPin2;
        singleInput.negInput   = iadcNegInputGnd;

        // Allocate the analog bus for ADC0 inputs
        GPIO->CDBUSALLOC |= GPIO_CDBUSALLOC_CDEVEN0_ADC0;

        // Initialize IADC
        IADC_init(IADC0, &init, &initAllConfigs);

        // Initialize a single-channel conversion
        IADC_initSingle(IADC0, &initSingle, &singleInput);

        // Start IADC conversion
        IADC_command(IADC0, iadcCmdStartSingle);

        // Wait for conversion to be complete
        while((IADC0->STATUS & (_IADC_STATUS_CONVERTING_MASK
                    | _IADC_STATUS_SINGLEFIFODV_MASK)) != IADC_STATUS_SINGLEFIFODV); //while combined status bits 8 & 6 don't equal 1 and 0 respectively

        // Get ADC result
        //sample = IADC_pullSingleFifoResult(IADC0).data;
        // Read a result from the FIFO
        sample = IADC_pullSingleFifoResult(IADC0);

        // Calculate input voltage:
        //  For differential inputs, the resultant range is from -Vref to +Vref, i.e.,
        //  for Vref = AVDD = 3.30V, 12 bits represents 6.60V full scale IADC range.
        PD2_ADC_Value = (sample.data *3300)/0xfff;
        printf("Coin volts = %dmV\r\n",PD2_ADC_Value);

        //read ADC PA6 for Ignition
        singleInput.posInput   = iadcPosInputPortAPin6;
        singleInput.negInput   = iadcNegInputGnd;

        // Allocate the analog bus for ADC0 inputs
        GPIO->ABUSALLOC |= GPIO_ABUSALLOC_AEVEN0_ADC0;

        // Initialize IADC
        IADC_init(IADC0, &init, &initAllConfigs);

        // Initialize a single-channel conversion
        IADC_initSingle(IADC0, &initSingle, &singleInput);

        // Start IADC conversion
        IADC_command(IADC0, iadcCmdStartSingle);

        // Wait for conversion to be complete
        while((IADC0->STATUS & (_IADC_STATUS_CONVERTING_MASK
                    | _IADC_STATUS_SINGLEFIFODV_MASK)) != IADC_STATUS_SINGLEFIFODV); //while combined status bits 8 & 6 don't equal 1 and 0 respectively

        // Get ADC result
        //sample = IADC_pullSingleFifoResult(IADC0).data;
        // Read a result from the FIFO
        sample = IADC_pullSingleFifoResult(IADC0);

        // Calculate input voltage:
        //  For differential inputs, the resultant range is from -Vref to +Vref, i.e.,
        //  for Vref = AVDD = 3.30V, 12 bits represents 6.60V full scale IADC range.
        PA6_ADC_Value = (sample.data *3300)/0xfff;
        printf("Ignition volts = %dmV\r\n",PA6_ADC_Value);


        if (PA6_ADC_Value < 0x1c2)
        {
          printf("***********IGN LOW+***********\r\n");
          //IADC_disable(IADC0);
          IADC0->EN_CLR = IADC_EN_EN;
          //enter EM2
          sl_bt_scanner_stop();
          //SLEEP_SleepBlockEnd(sleepEM2); // Enbale EM2
          remove_scheduled_timer();
          sl_bt_system_set_soft_timer(0,24,0);
          sl_bt_advertiser_stop(advertising_set_handle);
          sleep_mode = 1;
          Suspend_GPIN();
          //EMU_EnterEM2(true);
          printf("***********IGN LOW-***********\r\n");

        }

        //===============================
        //PA0_ADC_Value = ADC_DataSingleGet(ADC0);
        //PA0_ADC_Value = ADC_DataScanGet(ADC0);
        //RTCDRV_Trigger(100, NULL);
        //printf("***********PA0_ADC_Value = %d, %x***********\r\n",PA0_ADC_Value,PA0_ADC_Value);
        //call show_ADC_PA1() #for Ignition
        //gecko_cmd_hardware_read_adc(0, 1);*/
        if (trigger_duration_is_on == 0 && sniffer_mesh&sniffer_enable)
        {
          check_and_broadcast_to_B2S();
          //show_B2Device_List();
          //check_and_broadcast_to_B3S();
          //show_B3Device_List();
          add_device_count();
          check_device_count();
        }
        //EMU_EnterEM2(true);
        break;
        //break;
#endif
      }

      if (evt->data.evt_system_soft_timer.handle == 6)
      {
        printf("***********handle == 6***********\r\n");
        trigger_duration_is_on = 0;

        //remove handle = 3 timer
        sl_bt_system_set_soft_timer(0,3,0);

        set_pcsniffer_advdata_packet();

        //green led on
        green_led_on(1);

        //GPIN wake up source make it into sleep mode again
        GPIN_wakeup = 0;
        break;
      }
      // Holster/Armor use
      if (evt->data.evt_system_soft_timer.handle == 88)
      {
          //printf("handle == 88\r\n");
          //if((normal_mode%2) == 1)
          {
            if (BWC_Ver == 3)
          {
              memset(bwcb3AdvData.groupName, 0, 6);
              memcpy(bwcb3AdvData.groupName, groupName01, 6);
            memset(bwcb3AdvData.EventStatus, 0, 2);
              memcpy(bwcb3AdvData.EventStatus, b3_trigcmd, 2);
            set_non_connectable_b3_packet();
            BWC_Ver = 3;
            }
            else
            {
              memset(bwcb2AdvData.groupName, 0, 6);
              memcpy(bwcb2AdvData.groupName, groupName01, 6);
              memset(bwcb2AdvData.cmd, 0, 4);
              memcpy(bwcb2AdvData.cmd, b2_trigcmd, 4);
              set_non_connectable_b2_packet();
            BWC_Ver = 3;
          }
          }
        break;
      }


      if (evt->data.evt_system_soft_timer.handle == 7)
      {
        printf("handle == 7\r\n");
        // gpin_1_for_pc4
        GPIN4_HL_CNT++;
        if(!GPIO_PinInGet(gpioPortC, 4))
        {
          printf("****gpin_1_for_pc4 is low****\r\n");
          if(GPIN4_HL_CNT>trig_delay_buf*2)
          {
            if(gpin_andop_pins_buf & gpin_1_for_pc4)
            {
              read_gpin_high_low_status();
              if((read_current_gpin & gpin_andop_pins_buf) == gpin_andop_pins_buf)
              {
                //Start advertising
                TB03_trigger_BWCS();
              }
            }
            else
            {
              //Start advertising
              TB03_trigger_BWCS();
            }
            sl_bt_system_set_soft_timer(0,7,0);
            //detect "RELEASE" gpin_1_for_pc4
            sl_bt_system_set_soft_timer(0.5*second,8,0);
          }
        }
        else
        {
            printf("****gpin_1_for_pc4 is low****\r\n");
            set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,7,0);
          //GPIN wake up source make it into sleep mode again
          GPIN_wakeup = 0;
        }
        break;
      }
      if (evt->data.evt_system_soft_timer.handle == 8)
      {
        //printf("handle == 8\r\n");
        if(GPIO_PinInGet(gpioPortC, 4))
        {
          printf("****gpin_1_for_pc4 is high****\r\n");
          //Stop advertising
          sl_bt_system_set_soft_timer(0,2,0);
          if(stop_BWCB2_is_on == 0)
          {green_led_on(1);}

          set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,8,0);
          trigger_duration_is_on = 0;
        }
        break;
      }

      if (evt->data.evt_system_soft_timer.handle == 9)
      {
        printf("handle == 9\r\n");
        // gpin_7_for_pc1
        GPIN4_HL_CNT++;
        if(!GPIO_PinInGet(gpioPortC, 1))
        {
          printf("****gpin_7_for_pc1 is low****\r\n");
          if(GPIN4_HL_CNT>trig_delay_buf*2)
          {
            if(gpin_andop_pins_buf & gpin_7_for_pc1)
            {
              read_gpin_high_low_status();
              if((read_current_gpin & gpin_andop_pins_buf) == gpin_andop_pins_buf)
              {
                //Start advertising
                TB03_trigger_BWCS();
              }
            }
            else
            {
              //Start advertising
              TB03_trigger_BWCS();
            }
            sl_bt_system_set_soft_timer(0,9,0);
            //detect "RELEASE" gpin_7_for_pc1
            sl_bt_system_set_soft_timer(0.5*second,10,0);
          }
        }
        else
        {
          printf("****gpin_7_for_pc1 is low****\r\n");
          set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,9,0);
          //GPIN wake up source make it into sleep mode again
          GPIN_wakeup = 0;
        }
        break;
      }
      if (evt->data.evt_system_soft_timer.handle == 10)
      {
        //printf("handle == 10\r\n");
        if(GPIO_PinInGet(gpioPortC, 1))
        {
          printf("****gpin_7_for_pc1 is high****\r\n");
          //Stop advertising
          sl_bt_system_set_soft_timer(0,2,0);
          if(stop_BWCB2_is_on == 0)
          {green_led_on(1);}

          set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,10,0);
          trigger_duration_is_on = 0;
        }
        break;
      }

      if (evt->data.evt_system_soft_timer.handle == 11)
      {
        printf("handle == 11\r\n");
        // gpin_2_for_pc6
        GPIN4_HL_CNT++;
        if(!GPIO_PinInGet(gpioPortC, 6))
        {
          printf("****gpin_2_for_pc6 is low****\r\n");
          if(GPIN4_HL_CNT>trig_delay_buf*2)
          {
            if(gpin_andop_pins_buf & gpin_2_for_pc6)
            {
              read_gpin_high_low_status();
              if((read_current_gpin & gpin_andop_pins_buf) == gpin_andop_pins_buf)
              {
                //Start advertising
                TB03_trigger_BWCS();
              }
            }
            else
            {
              //Start advertising
              TB03_trigger_BWCS();
            }
            sl_bt_system_set_soft_timer(0,11,0);
            //detect "RELEASE" gpin_2_for_pc6
            sl_bt_system_set_soft_timer(0.5*second,12,0);
          }
        }
        else
        {
            printf("****gpin_2_for_pc6 is low****\r\n");
            set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,11,0);
          //GPIN wake up source make it into sleep mode again
          GPIN_wakeup = 0;
        }
        break;
      }
      if (evt->data.evt_system_soft_timer.handle == 12)
      {
        //printf("handle == 12\r\n");
        if(GPIO_PinInGet(gpioPortC, 6))
        {
          printf("****gpin_2_for_pc6 is high****\r\n");
          //Stop advertising
          sl_bt_system_set_soft_timer(0,2,0);
          if(stop_BWCB2_is_on == 0)
          {green_led_on(1);}

          set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,12,0);
          trigger_duration_is_on = 0;
        }
        break;
      }

      if (evt->data.evt_system_soft_timer.handle == 13)
      {
        printf("handle == 13\r\n");
        // gpin_3_for_pa7
        GPIN4_HL_CNT++;
        if(!GPIO_PinInGet(gpioPortA, 7))
        {
          printf("****gpin_3_for_pa7 is low****\r\n");
          if(GPIN4_HL_CNT>trig_delay_buf*2)
          {
            if(gpin_andop_pins_buf & gpin_3_for_pa7)
            {
              read_gpin_high_low_status();
              if((read_current_gpin & gpin_andop_pins_buf) == gpin_andop_pins_buf)
              {
                //Start advertising
                TB03_trigger_BWCS();
              }
            }
            else
            {
              //Start advertising
              TB03_trigger_BWCS();
            }
            sl_bt_system_set_soft_timer(0,13,0);
            //detect "RELEASE" gpin_3_for_pa7
            sl_bt_system_set_soft_timer(0.5*second,14,0);
          }
        }
        else
        {
            printf("****gpin_3_for_pa7 is high****\r\n");
            set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,13,0);
          //GPIN wake up source make it into sleep mode again
          GPIN_wakeup = 0;
        }
        break;
      }
      if (evt->data.evt_system_soft_timer.handle == 14)
      {
        //printf("handle == 14\r\n");
        //if(GPIO_PinInGet(gpioPortC, 0))
        if(GPIO_PinInGet(gpioPortA, 7))
        {
          printf("****gpin_3_for_pa7 is high****\r\n");
          //Stop advertising
          sl_bt_system_set_soft_timer(0,2,0);
          if(stop_BWCB2_is_on == 0)
          {green_led_on(1);}

          set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,14,0);
          trigger_duration_is_on = 0;
        }
        break;
      }

      if (evt->data.evt_system_soft_timer.handle == 15)
      {
        printf("handle == 15\r\n");
        // gpin_5_for_pb0
        GPIN4_HL_CNT++;
        if(!GPIO_PinInGet(gpioPortB, 0))
        {
          printf("****gpin_5_for_pb0 is low****\r\n");
          if(GPIN4_HL_CNT>trig_delay_buf*2)
          {
            if(gpin_andop_pins_buf & gpin_5_for_pb0)
            {
              read_gpin_high_low_status();
              if((read_current_gpin & gpin_andop_pins_buf) == gpin_andop_pins_buf)
              {
                //Start advertising
                TB03_trigger_BWCS();
              }
            }
            else
            {
              //Start advertising
              TB03_trigger_BWCS();
            }
            sl_bt_system_set_soft_timer(0,15,0);
            //detect "RELEASE" gpin_5_for_pb0
            sl_bt_system_set_soft_timer(0.5*second,16,0);
          }
        }
        else
        {
            printf("****gpin_5_for_pb0 is low****\r\n");
            set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,15,0);
          //GPIN wake up source make it into sleep mode again
          GPIN_wakeup = 0;
        }
        break;
      }
      if (evt->data.evt_system_soft_timer.handle == 16)
      {
        //printf("handle == 16\r\n");
        if(GPIO_PinInGet(gpioPortB, 0))
        {
          printf("****gpin_5_for_pb0 is high****\r\n");
          //Stop advertising
          sl_bt_system_set_soft_timer(0,2,0);
          if(stop_BWCB2_is_on == 0)
          {green_led_on(1);}

          set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,16,0);
          trigger_duration_is_on = 0;
        }
        break;
      }

      if (evt->data.evt_system_soft_timer.handle == 17)
      {
        printf("handle == 17\r\n");
        // gpin_4_for_pa8
        GPIN4_HL_CNT++;
        if(!GPIO_PinInGet(gpioPortA, 8))
        {
          printf("****gpin_4_for_pa8 is low****\r\n");
          if(GPIN4_HL_CNT>trig_delay_buf*2)
          {
            if(gpin_andop_pins_buf & gpin_4_for_pa8)
            {
              read_gpin_high_low_status();
              if((read_current_gpin & gpin_andop_pins_buf) == gpin_andop_pins_buf)
              {
                //Start advertising
                TB03_trigger_BWCS();
              }
            }
            else
            {
              //Start advertising
              TB03_trigger_BWCS();
            }
            sl_bt_system_set_soft_timer(0,17,0);
            //detect "RELEASE" gpin_4_for_pa8
            sl_bt_system_set_soft_timer(0.5*second,18,0);
          }
        }
        else
        {
            printf("****gpin_4_for_pa8 is low****\r\n");
            set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,17,0);
          //GPIN wake up source make it into sleep mode again
          GPIN_wakeup = 0;
        }
        break;
      }
      if (evt->data.evt_system_soft_timer.handle == 18)
      {
        //printf("handle == 18\r\n");
        if(GPIO_PinInGet(gpioPortA, 8))
        {
          printf("****gpin_4_for_pa8 is high****\r\n");
          //Stop advertising
          sl_bt_system_set_soft_timer(0,2,0);
          if(stop_BWCB2_is_on == 0)
          {green_led_on(1);}

          set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,18,0);
          trigger_duration_is_on = 0;
        }
        break;
      }

      if (evt->data.evt_system_soft_timer.handle == 19)
      {
        printf("handle == 19\r\n");
        // gpin_6_for_pb2
        GPIN4_HL_CNT++;
        if(!GPIO_PinInGet(gpioPortB, 2))
        {
          printf("****gpin_6_for_pb2 is low****\r\n");
          if(GPIN4_HL_CNT>trig_delay_buf*2)
          {
            if(gpin_andop_pins_buf & gpin_6_for_pb2)
            {
              read_gpin_high_low_status();
              if((read_current_gpin & gpin_andop_pins_buf) == gpin_andop_pins_buf)
              {
                //Start advertising
                TB03_trigger_BWCS();
              }
            }
            else
            {
              //Start advertising
              TB03_trigger_BWCS();
            }
            sl_bt_system_set_soft_timer(0,19,0);
            //detect "RELEASE" gpin_6_for_pb2
            sl_bt_system_set_soft_timer(0.5*second,20,0);
          }
        }
        else
        {
            printf("****gpin_6_for_pb2 is low****\r\n");
            set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,19,0);
          //GPIN wake up source make it into sleep mode again
          GPIN_wakeup = 0;
        }
        break;
      }
      if (evt->data.evt_system_soft_timer.handle == 20)
      {
        //printf("handle == 20\r\n");
        if(GPIO_PinInGet(gpioPortB, 2))
        {
          printf("****gpin_6_for_pb2 is high****\r\n");
          //Stop advertising
          sl_bt_system_set_soft_timer(0,2,0);
          if(stop_BWCB2_is_on == 0)
          {green_led_on(1);}

          set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,20,0);
          trigger_duration_is_on = 0;
        }
        break;
      }

      if (evt->data.evt_system_soft_timer.handle == 21)
      {
        printf("handle == 21\r\n");
        // gpin_0_for_pb3
        GPIN4_HL_CNT++;
        //if(!GPIO_PinInGet(gpioPortC, 0))
        if(!GPIO_PinInGet(gpioPortB, 3))
        {
          printf("****gpin_0_for_pb3 is low****\r\n");
          if(GPIN4_HL_CNT>trig_delay_buf*2)
          {
            if(gpin_andop_pins_buf & gpin_0_for_pb3)
            {
              read_gpin_high_low_status();
              if((read_current_gpin & gpin_andop_pins_buf) == gpin_andop_pins_buf)
              {
                //Start advertising
                TB03_trigger_BWCS();
              }
            }
            else
            {
              //Start advertising
              TB03_trigger_BWCS();
            }
            sl_bt_system_set_soft_timer(0,21,0);
            //detect "RELEASE" gpin_0_for_pb3
            sl_bt_system_set_soft_timer(0.5*second,22,0);
          }
        }
        else
        {
            printf("****gpin_0_for_pb3 is low****\r\n");
            set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,21,0);
          //GPIN wake up source make it into sleep mode again
          GPIN_wakeup = 0;
        }
        break;
      }
      if (evt->data.evt_system_soft_timer.handle == 22)
      {
        //printf("handle == 22\r\n");
        //if(GPIO_PinInGet(gpioPortC, 0))
        if(GPIO_PinInGet(gpioPortB, 3))
        {
          printf("****gpin_0_for_pb3 is high****\r\n");
          //Stop advertising
          sl_bt_system_set_soft_timer(0,2,0);
          if(stop_BWCB2_is_on == 0)
          {green_led_on(1);}

          set_pcsniffer_advdata_packet();
          sl_bt_system_set_soft_timer(0,22,0);
          trigger_duration_is_on = 0;
        }
        break;
      }
      /*if (evt->data.evt_system_soft_timer.handle == 9)
      {
          printf("handle == 9\r\n");
          {red_led_blink(1);}
        break;
      }

      if (evt->data.evt_system_soft_timer.handle == 13)
      {
          printf("handle == 13\r\n");
          //stop trigger BWCS
          stop_trigger_BWCS();
        break;
      }*/
      if (evt->data.evt_system_soft_timer.handle == 23)
      {
          printf("handle == 23\r\n");
          //stop advertising
          sl_bt_advertiser_stop(advertising_set_handle);
        break;
      }
      if (evt->data.evt_system_soft_timer.handle == 24)
      {
          //printf("***********handle == 24***********\r\n");
          //app_iostream_usart_process_action(&CmdStr[0]);
          //printf("\r\n**** command: %s, len: %d ,sizeof %d ****\r\n> ", cmd_buffer, strlen(cmd_buffer), sizeof(cmd_buffer));
          FindCmdTag();
          DoCommand();
          memset(cmd_buffer, 0, 80);
        break;
      }
    // -------------------------------
    // Default event handler.
    default:
      break;
  }
}

/***************************************************************************//**
* @brief
*   FindCmdTag
*******************************************************************************/
void FindCmdTag()
{
  bFindHeader = 0;
  HeaderOffset = 0;
  bFindTailer = 0;
  TailerOffset = 0;
  Index = 0;
  while( Index < strlen(cmd_buffer))
  {
    //Find character '<'
    if(cmd_buffer[Index] == '<' && bFindHeader == 0)
    {
      bFindHeader = 1;
      HeaderOffset = Index;
      //printf("bFindHeader = %d\r\n", Index);
    }
    //Find character '>'
    if(cmd_buffer[Index] == '>' && bFindTailer == 0)
    {
      bFindTailer = 1;
      TailerOffset = Index;
      //printf("TailerOffset = %d\r\n", Index);
    }
    Index++;
  }
}

/***************************************************************************//**
* @brief
*   DoCommand
*******************************************************************************/
void DoCommand()
{
  bFindKeyChar = 0;
  KeyCharOffset = 0;
  bCmdMatch = 0;
  Index = 0;

  if(bFindHeader == 1 && bFindTailer == 1)
  {
    CmdLen = TailerOffset - HeaderOffset - 1; //skip "<" and ">"
    memcpy(CmdStr, &cmd_buffer[HeaderOffset+1], CmdLen);
    //Do command here

    //SET TSMON
    if((!memcmp(CmdStr, CmdTestModeOn, 9)) && CmdLen == 9)
    {
      bCmdMatch = 1;
      printf("OK\r\n");
      test_mode = 1;
      //remove_scheduled_timer();
      //call advertising_to_PC_connectable()
      //green led on
      //call green_led_on(1)
    }

    //SET TSMOFF
    if((!memcmp(CmdStr, CmdTestModeOff, 10)) && CmdLen == 10)
    {
      bCmdMatch = 1;
      printf("OK\r\n");
      test_mode = 0;
    }

    //SET PSOFFSET 0:Serial Number 1:TX Power Calib Value
    if((!memcmp(CmdStr, CmdSetPSOffset, 12)))
    {
      bCmdMatch = 1;
      printf("OK\r\n");
    }

    //GET PSDATA
    if((!memcmp(CmdStr, CmdGetPSData, 10)) && CmdLen == 10)
    {
      //printf("********** GET PSDATA **********\r\n");
      bCmdMatch = 1;
      ret = sl_bt_nvm_load(0x4000,10,&read_len,(uint8_t*)user_read_response_buf);
      if (SL_STATUS_OK  == ret)
      {
        for(int i=0;i<read_len;i++)
        {printf("%c",user_read_response_buf[i]);}
        printf("\r\n");
      }
      else
        {printf("GET PSDATA : Fail\r\n");}
    }

    //SET PSDATA
    if((!memcmp(CmdStr, CmdSetPSData, 10)))
    {
      bCmdMatch = 1;
      Index = 0;
      //Find character '='
      while(Index < CmdLen)
      {
        if(CmdStr[Index] == '=')
        {
          bFindKeyChar = 1;
          KeyCharOffset = Index;
        }
        Index++;
      }

      if(bFindKeyChar == 1 && KeyCharOffset == 10)//SET PSDATA=, "=" must at offset 10
      {
        if((CmdLen-KeyCharOffset) > 0)
        {
          //SN len <= 10
          if((CmdLen-KeyCharOffset-1) <= 10)
          {
            bCmdMatch = 1;
            memcpy(nvm_write, &CmdStr[KeyCharOffset+1], (CmdLen-KeyCharOffset-1));
            //printf("nvm_write = %s, len = %d(%d)\r\n", nvm_write, strlen(nvm_write), (CmdLen-KeyCharOffset-1));
            ret = sl_bt_nvm_save(0x4000,strlen(nvm_write),nvm_write);
            if (SL_STATUS_OK  == ret)
            {printf("OK\r\n");}
            else
            {printf("Write PSData Fail\r\n");}
          }
        }
      }
    }

    //GET SYSSN
    if((!memcmp(CmdStr, CmdGetSYSSN, 9)) && CmdLen == 9)
    {
      //printf("********** GET SYS SN **********\r\n");
      bCmdMatch = 1;
      ret = sl_bt_nvm_load(0x4002,10,&read_len,(uint8_t*)user_read_response_buf);
      if (SL_STATUS_OK  == ret)
      {
        for(int i=0;i<read_len;i++)
        {printf("%c",user_read_response_buf[i]);}
        printf("\r\n");
      }
      else
      {printf("GET SYS SN : Fail\r\n");}
    }

    //SET SYSSN
    if((!memcmp(CmdStr, CmdSetSYSSN, 9)))
    {
      //printf("********** %s **********\r\n",CmdStr);
      bCmdMatch = 1;
      Index = 0;
      //Find character '='
      while(Index < CmdLen)
      {
        if(CmdStr[Index] == '=')
        {
          bFindKeyChar = 1;
          KeyCharOffset = Index;
        }
        Index++;
      }

      if(bFindKeyChar == 1 && KeyCharOffset == 9)//SET SYSSN=, "=" must at offset 9
      {
        if((CmdLen-KeyCharOffset) > 0)
        {
          //SN len <= 10
          //PS_Data.len = CmdLen-KeyCharOffset-1;
          //printf("********** CmdLen=%d, KeyCharOffset=%d **********\r\n",CmdLen,KeyCharOffset);
          if((CmdLen-KeyCharOffset-1) <= 10)
          {
            bCmdMatch = 1;
            memcpy(nvm_write, &CmdStr[KeyCharOffset+1], (CmdLen-KeyCharOffset-1));
            //printf("nvm_write = %s, len = %d\r\n", nvm_write, strlen(nvm_write));

            ret = sl_bt_nvm_save(0x4002,strlen(nvm_write),nvm_write);
            //struct gecko_msg_flash_ps_save_rsp_t * resp = gecko_cmd_flash_ps_save(0x4002, PS_Data.len, PS_Data.data);
            if (SL_STATUS_OK  == ret)
            {printf("OK\r\n");}
            else
            {printf("Write SYS SN Fail\r\n");}
          }
        }
      }
    }

    //GET MAC
    if((!memcmp(CmdStr, CmdGetMAC, 7)) && CmdLen == 7)
    {
      bCmdMatch = 1;
      printf("%02X:%02X:%02X:%02X:%02X:%02X\r\n",address.addr[5],address.addr[4],address.addr[3],address.addr[2],address.addr[1],address.addr[0]);
    }

    //GET GPI
    /*if((!memcmp(CmdStr, CmdGetGPI, 7)) && CmdLen == 7)
    {
      read_gpin_high_low_status();
      bCmdMatch = 1;
    }

    //SET GPO
    if((!memcmp(CmdStr, CmdSetGPO, 7)))
    {
      bCmdMatch = 1;
      Index = 0;
      //Find character '='
      while(Index < CmdLen)
      {
        if(CmdStr[Index] == '=')
        {
          bFindKeyChar = 1;
          KeyCharOffset = Index;
        }
        Index++;
      }

      if(bFindKeyChar == 1 && KeyCharOffset == 7)//SET GPO=, "=" must at offset 7
      {
         GPOVal = CmdStr[KeyCharOffset + 1] - 0x30; //0x30 is ascii '0'
         //Set GPO here
         if(GPOVal == 0)
         {
           //drive the PD15 to Low
           GPIO_PortOutClear(gpioPortD, 0x8000);
           printf("OK\r\n");
         }
         else if(GPOVal == 1)
         {
            //drive the PD15 to High
            GPIO_PortOutSet(gpioPortD, 0x8000);
            printf("OK\r\n");
         }
         else
         {printf("Invalid Value\r\n");}
       }
    }

    if(bCmdMatch == 0)
    {
      cmd_buffer_len = 0;
      printf("Unknown Command\r\n");
    }
    else
    {
      //cmd_buffer_len = 0;
      cmd_buffer_len = cmd_buffer_len - TailerOffset - 1;
    }*/

    //GET UARTOFF
    if((!memcmp(CmdStr, CmdGetUARTOff, 11)) && CmdLen == 11)
    {
      //printf("********** GET UART OFF **********\r\n");
      bCmdMatch = 1;
      ret = sl_bt_nvm_load(0x400f,10,&read_len,(uint8_t*)user_read_response_buf);
      if (SL_STATUS_OK  == ret)
      {
        for(int i=0;i<read_len;i++)
        {printf("%c",user_read_response_buf[i]);}
        printf("\r\n");
      }
      else
      {printf("GET UART OFF : Fail\r\n");}
    }

    //SET UARTOFF
    if((!memcmp(CmdStr, CmdSetUARTOff, 11)))
    {
      //printf("********** %s **********\r\n",CmdStr);
      bCmdMatch = 1;
      Index = 0;
      //Find character '='
      while(Index < CmdLen)
      {
        if(CmdStr[Index] == '=')
        {
          bFindKeyChar = 1;
          KeyCharOffset = Index;
        }
        Index++;
      }

      if(bFindKeyChar == 1 && KeyCharOffset == 11)//SET UARTOFF=, "=" must at offset 11
      {
        if((CmdLen-KeyCharOffset) > 0)
        {
          //printf("********** CmdLen=%d, KeyCharOffset=%d **********\r\n",CmdLen,KeyCharOffset);
          if((CmdLen-KeyCharOffset-1) <= 10)
          {
            bCmdMatch = 1;
            memcpy(nvm_write, &CmdStr[KeyCharOffset+1], (CmdLen-KeyCharOffset-1));
            //printf("nvm_write = %s, len = %d\r\n", nvm_write, strlen(nvm_write));

            ret = sl_bt_nvm_save(0x400f,strlen(nvm_write),nvm_write);
            if (SL_STATUS_OK  == ret)
            {printf("OK\r\n");}
            else
            {printf("Write SYS SN Fail\r\n");}
          }
        }
      }
    }


  }
}

/***************************************************************************//**
* @brief
*   GetCoinVol
*******************************************************************************/
void GetCoinVol()
{
    initIADC();

    //read ADC PD2 for Coin battery
    singleInput.posInput   = iadcPosInputPortDPin2;
    singleInput.negInput   = iadcNegInputGnd;

    // Allocate the analog bus for ADC0 inputs
    GPIO->CDBUSALLOC |= GPIO_CDBUSALLOC_CDEVEN0_ADC0;

    // Initialize IADC
    IADC_init(IADC0, &init, &initAllConfigs);

    // Initialize a single-channel conversion
    IADC_initSingle(IADC0, &initSingle, &singleInput);

    // Start IADC conversion
    IADC_command(IADC0, iadcCmdStartSingle);

    // Wait for conversion to be complete
    while((IADC0->STATUS & (_IADC_STATUS_CONVERTING_MASK
                | _IADC_STATUS_SINGLEFIFODV_MASK)) != IADC_STATUS_SINGLEFIFODV); //while combined status bits 8 & 6 don't equal 1 and 0 respectively

    // Get ADC result
    //sample = IADC_pullSingleFifoResult(IADC0).data;
    // Read a result from the FIFO
    sample = IADC_pullSingleFifoResult(IADC0);

    // Calculate input voltage:
    //  For differential inputs, the resultant range is from -Vref to +Vref, i.e.,
    //  for Vref = AVDD = 1.20V, 12 bits represents 3.3V/3 full scale IADC range.
    PD2_ADC_Value = (sample.data *1210*2*3)/0xfff;
    //PC6_ADC_Value = sample.data;
    printf("sample.data = %d,  volts = %dmV\r\n",sample.data,PD2_ADC_Value);

    //IADC_disable(IADC0);
    IADC0->EN_CLR = IADC_EN_EN;
}
void red_green_yellow_led_blink(times)
{
  green_red_yellow_led_off();
  for(int i = 0; i<times; i++)
  {
    red_led_blink(1);
    green_led_blink(1);
    yellow_led_blink(1);
  }
}

void red_green_led_blink(times)
{
  green_red_yellow_led_off();
  for(int i = 0; i<times; i++)
  {
    red_led_blink(1);
    green_led_blink(1);
  }
}

void green_led_blink(times)
{
  green_red_yellow_led_off();
  for(int i = 0; i<times; i++)
  {
    GPIO_PortOutClear(gpioPortC, 0x80);
    sl_udelay_wait(500000);
    //USTIMER_Delay(500000);
    GPIO_PortOutSet(gpioPortC, 0x80);
    sl_udelay_wait(500000);
  }
}

void red_led_blink(times)
{
  green_red_yellow_led_off();
  for(int i = 0; i<times; i++)
  {
    GPIO_PortOutClear(gpioPortB, 0x10);
    sl_udelay_wait(500000);
    GPIO_PortOutSet(gpioPortB, 0x10);
    sl_udelay_wait(500000);
  }
}

void yellow_led_blink(times)
{
  green_red_yellow_led_off();
  for(int i = 0; i<times; i++)
  {
    GPIO_PortOutClear(gpioPortC, 0x180);
    USTIMER_Delay(500000);
    GPIO_PortOutSet(gpioPortC, 0x180);
    USTIMER_Delay(500000);
  }
}

void green_led_on(turn_on)
{
  green_red_yellow_led_off();
  if(turn_on==0)
  {GPIO_PortOutSet(gpioPortB, 0x10);}
  else
  {GPIO_PortOutClear(gpioPortB, 0x10);}
}

void red_led_on(turn_on)
{
  green_red_yellow_led_off();
  if(turn_on==0)
  {GPIO_PortOutSet(gpioPortB, 0x2);}
  else
  {GPIO_PortOutClear(gpioPortB, 0x2);}
}

void yellow_led_on(turn_on)
{
  green_red_yellow_led_off();
  if(turn_on==0)
  {GPIO_PortOutSet(gpioPortC, 0x180);}
  else
  {GPIO_PortOutClear(gpioPortC, 0x180);}
}

void green_led_solid(times)
{
  green_red_yellow_led_off();
    green_led_on(1);
    //gecko_cmd_hardware_set_soft_timer(times*second,6,1);
}

void red_led_solid(times)
{
  green_red_yellow_led_off();
  red_led_on(1);
  //gecko_cmd_hardware_set_soft_timer(times*second,6,1);
}

void yellow_led_solid(times)
{
  green_red_yellow_led_off();
  yellow_led_on(1);
  //gecko_cmd_hardware_set_soft_timer(times*second,6,1);
}

void green_red_yellow_led_off()
{GPIO_PortOutSet(gpioPortB, 0x12);}

int testLEDcnt = 0;
void testLED()
{
  testLEDcnt = testLEDcnt%4;
  switch (testLEDcnt)
  {
    case (0):
    green_led_on(1);
        break;

    case (1):
    red_led_on(1);
        break;

    case (2):
    yellow_led_on(1);
            break;
    case (3):
    green_red_yellow_led_off();
            break;

  }
  testLEDcnt++;
}

