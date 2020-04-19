#include <vcl.h>
#include <stdlib.h>
#include <stdio.h>
#include <sys\stat.h>
#include <io.h>
#include <dos.h>
#include <fcntl.h>
#include <share.h>
#include <process.h>
#include <time.h>
 
#define  Process_Tsec
#include "NewTsec.h"
#define  Process_Ip
#include "ipfmt.h"

#include <share.h>
#include <math.h>
#include "sub.h"
#include "main.h"
#include "emg.h"
#include "log.hpp"

#pragma hdrstop

#define  sStableStockFileName   "StablStk.tbl"
#define  MAX_STKSTOP            200

extern EMG_STK_STOP    stEmgStkStopInfo[MAX_EMG_STOP];
extern EMG_STK_INFO_FMT emg_stk_info[MAX_EMG_STK];
long Index20[20]={0L,0L,0L,0L,0L,0L,0L,0L,0L,0L,0L,0L,0L,0L,0L,0L,0L,0L,0L,0L};

char tsec_buf[CIRCLE_BUF_SIZE];
char otc_buf[CIRCLE_BUF_SIZE];
unsigned char *mf4_file= "FIX_TSE.TXT";
unsigned char *mf3_file= "FIX_OTC.TXT";
unsigned char default_warr_file[50] = "warrbase.txt";
unsigned char default_bb_file[50] = "bbinfo.txt";
unsigned char default_bb_file_otc[50] = "bbinfo2.txt";
char mk_str[2][6]={"Tsec", "Otc"};
char Ip2_mk_str[2][6]={"IP2_1", "IP2_2"};
char tsec_time[8]="00000";
char tsec_buffer[50];
int  tsec_first_seq;       // 第一個收到的toyo碼，用來累計總共收到幾次商品基本資訊循環
                           // 雙線合併後，累加會重複計算，要改變作法
int  otc_first_seq;
int  tse_9999_sent_cnt;
int  pre_idx_time;
int  l1TsecEMNew;
int  l2TsecEMNew;
int  TsecEMNew_Count;
int  l1OtcEMNew;
int  l2OtcEMNew;
int  OtcEMNew_Count;
int  tsec_yes_flag;
int  otc_yes_flag;
int  tsec_class_total;
int  otc_class_total;
char   Bin9996Send[43];
char   sMsg[64];
int    otc_1min_idx_seq[MAX_CLASS];
int    tsec_index_seq;
int    tsec_unindex_seq;
int    simsci_index_seq;
int    tsec_index20_seq[MAX_CLASS];
int    iUpDownExtCheck[2][MAX_CLASS];
struct CHKSTOCK_FMT chkstock[50];
struct CHKCLASS_FMT chkclass[100];
int    chkstock_cnt=0;
int    chkclass_cnt=0;
int mis_open[2];

struct mem_9995  close2mem9995;
struct mem_9995  Otc_close2mem9995;
struct mem_9995  OtcClose9995;
struct mem_9995  TsecClose9995;

struct CCCC   *stock_ndx_data;
struct mem_9996  Mem1min9996;   // one-minute weighted index
struct mem_99961 Mem1min99961;  // one-minute exclusive index
struct FIXED_PRICE_TRADE {
    int Toyo;
    int Ok;
}FixedPriceTrade[2];

struct  STK_STOP   {
    int     toyo;
    int     stop_time;
    int     start_time;
}StkStopInfo[MAX_STKSTOP];

static stMarketNotch sVipMarketNotch;

extern struct CCCC       stock_ndx[2][max_TotalStockNo];
extern struct keep_price MemPrice[max_TotalStockNo];
extern struct AAAA       StockMem[max_TotalStockNo];
extern struct BOND *bond;  // v6.8.0
extern void TimeTo1MinPtr(int now, struct ONEMIN_TIME *onemin);
extern struct time dtime;
extern unsigned char last_pause_flag[max_TotalStockNo];
extern long last_pause_time[max_TotalStockNo];

struct _def_stock_pre StockPre[max_TotalStockNo];

int Cv2IndexTime15(char * src_bcd,int num)
{
    long sum, twse_time;

    twse_time =BCD_to_Long(src_bcd, num);
    twse_time = CutMrkTestTime(twse_time, MK_TSEC);
    if(twse_time >= 999999)
        return 9999;
    sum = (twse_time%100)?1:0;
    return   twse_time/100 +sum;
}

struct CCCC * SearchToyoNumberEx( char *stock, int market)
{
   int top=0, down=TotalStockNo-1;
   int x, i;

   do
     {
       x = (top+down) / 2;
       i = strncmp( stock_ndx[market - 1][x].stock, stock, 6 );
       if( i == 0 )
         {
           return( stock_ndx[market - 1]+x );
         }
       if( i < 0 )
           top = x+1;
       else
           down = x-1;
     } while( top <= down );

   return( NULL );
}

unsigned long BCD_to_Long(const char * src_bcd, int num = 1)
{
   unsigned long value=0;
   int  i;

   for (i=0 ;i<num;i++) {
     value=(value*10L)+( ((unsigned char)(*(src_bcd+i))) >>4);
     value=(value*10L)+(*(src_bcd+i)&0x0F);
   }
   return value;
}

__int64 BCD_to_int64(char * src_bcd,int num = 1)
{
   __int64 value=0;
   __int64 offset = 10;
   int  i;

   for (i=0 ;i<num;i++)
   {
     value=(value*offset)+( ((unsigned char)(*(src_bcd+i))) >>4);
     value=(value*offset)+(*(src_bcd+i)&0x0F);
   }
   return value;
}

int Sort_Tsec_Seq(const void *a ,const void *b)
{
   return  (*((struct CCCC **)a))->tsec_seq - (*((struct CCCC **)b))->tsec_seq;
}
int Sort_New_Market_Seq(int market)
{
   qsort( (void *)stock_tsec_seq[market - 1] , max_TotalStockNo ,sizeof(char *), Sort_Tsec_Seq);
   return 0;
}

// 一開機讀取 tsec.seq
void read_tsec_seq()
{
   char stock_name[10], stock_seq[6];
   FILE *stk_fs,*flog;
   int i;
   int seq;
   int top, down,x,y;

   if( (stk_fs=fopen("tsec.seq","r") )!=NULL ){
      memset(stock_name,0,6);
      while( fscanf(stk_fs,"%s %s",stock_name, stock_seq)>1 ){
          if(stock_name[4]=='\0'){
             stock_name[4]=' ';
          }
          stock_name[5]=' ';
          stock_name[6]='\0';
          if(stock_seq != NULL)
            seq=atoi(stock_seq);
          stock_ndx_data = SearchToyoNumberEx( stock_name,  MK_TSEC);
          if (stock_ndx_data != NULL){
             if((stock_ndx_data->tsec_seq<0) && (seq<0))  {
                sprintf(sMsg,"載入交易所Toyo碼錯誤: %s", stock_name);
                MemoMsg(sMsg) ;
             }   
             else if(seq>0)
                stock_ndx_data->tsec_seq=seq;
          }
      }
      fclose(stk_fs);
   }
   Sort_New_Market_Seq(MK_TSEC);
   flog=fopen("tsec_seq.bak","w");
   for(i=0;i<max_TotalStockNo;i++)
      fprintf(flog,"%6.6s  %04d\n", stock_ndx[0][i].stock, stock_ndx[0][i].tsec_seq);
   fclose(flog);
}

void read_otc_seq()
{
    char stock_name[10], stock_seq[6];
    FILE *stk_fs,*flog;
    int i;
    int seq;
    int top, down,x,y;

    if((stk_fs = fopen("otc.seq","r")) != NULL ){
        memset(stock_name,0,6);
        while( fscanf(stk_fs,"%s %s",stock_name, stock_seq)>1 ){
            if(stock_name[4]=='\0'){
                stock_name[4]=' ';
            }
          stock_name[5]=' ';
          stock_name[6]='\0';
          if(stock_seq != NULL)
             seq=atoi(stock_seq);
          stock_ndx_data = SearchToyoNumberEx( stock_name,  MK_OTC);
          if (stock_ndx_data!=NULL){
             if((stock_ndx_data->tsec_seq<0) && (seq<0))  {
                sprintf(sMsg,"載入交易所Toyo碼錯誤: %s", stock_name);
                MemoMsg(sMsg) ;
             }
             else if(seq>0)
                 stock_ndx_data->tsec_seq=seq;
          }
      }
      fclose(stk_fs);
   }
   Sort_New_Market_Seq(MK_OTC);
   flog=fopen("otc_seq.bak","w");
   for(i=0;i<max_TotalStockNo;i++)
      fprintf(flog,"%6.6s  %04d\n", stock_ndx[1][i].stock, stock_ndx[1][i].tsec_seq);
   fclose(flog);
}

void Initial_RT_WARR(void)
{
    FILE   *mf4_rec, *mf3_rec;
    struct ftime ftimep;
    struct date date;

    if (access(mf4_file,0)==0){
    // Compare date of file.
        mf4_rec=fopen(mf4_file,"rt");
        getftime(fileno(mf4_rec),&ftimep);
        fclose(mf4_rec);
        getdate(&date);
        if ( ((date.da_year-1980)!=(int)ftimep.ft_year) ||
              ((date.da_mon)!=(char)ftimep.ft_month)     ||
              ((date.da_day)!=(char)ftimep.ft_day))  {
                unlink(mf4_file);
                if (-1==wrt_mf4(mf4_file)){
                    MemoMsg("Can not open file XXX.mf4\n") ;
                }
        }
        else{ }
    }// if (access(mf4_fi..........
    else {
            // open
         if (-1==wrt_mf4(mf4_file)){
              MemoMsg("Can not open file XXX.mf4\n") ;
         }
    }
    tmp_copy (tsedir,tsefile,mf4_file);
    if (access(mf3_file,0)==0){
         // Compare date of file.
        mf3_rec=fopen(mf3_file,"rt");
        getftime(fileno(mf3_rec),&ftimep);
        fclose(mf3_rec);
        getdate(&date);
        if ( ((date.da_year-1980)!=(int)ftimep.ft_year) ||
              ((date.da_mon)!=(char)ftimep.ft_month)     ||
              ((date.da_day)!=(char)ftimep.ft_day))  {
                unlink(mf3_file);
            // open
                if (-1==wrt_mf3(mf3_file)){
                    MemoMsg("Can not open file XXX.mf3\n") ;
                }
        }
        else{ }
    }  /* if (access(mf3_fi...*/
    else {
            // open
        if (-1==wrt_mf3(mf3_file)){
              MemoMsg("Can not open file XXX.mf3\n") ;
        }
    }
    tmp_copy (otcdir,otcfile,mf3_file);
    rept[0] = 0 ;
    rept[1] = 0 ;
    max_rept_cycle = 2;
    memset(warr_info, 0x00, sizeof(struct WARR_INFO)*MAX_WARR_DEF*2) ;
}
int IsUpDownExtStk(int mkt, int clsType)
{
    if(( mkt >= 0 && mkt < 2) &&
        (clsType >= 0 && clsType < MAX_CLASS))
        return (!iUpDownExtCheck[mkt][clsType]);
    return 1;        
}
void ReadUpDownExtSetup(char *sFileName)
{
    FILE *temp_f1;
    char buf[80], *ptr;
    int mkt, clsType;

    for(int i=0; i<2; i++)
        for(int j=0; j<MAX_CLASS; j++)
            iUpDownExtCheck[i][j]=0;

    if ((temp_f1=fopen(sFileName,"r")) != NULL) {
        while (!feof(temp_f1))
        {
            fgets(buf, 80, temp_f1);
            if( (ptr = strtok(buf, " ,\r\n\t")) == NULL)
                continue;
            mkt = atoi(ptr);
            if( (ptr = strtok(NULL, " ,\r\n\t")) == NULL)
                continue;
            clsType = atoi(ptr);
            if(( mkt > 0 && mkt <= 2) &&
                (clsType >= 0 && clsType < MAX_CLASS))
            iUpDownExtCheck[mkt-1][clsType] =1;
        }
    fclose(temp_f1);
    }
}

void Initial_NEWTSEC(void)
{
    int i, j, k;
    FILE *fp;
    char buf[80], *ptr, stk_name[7];

    mis_open[0] = 0;
    mis_open[1] = 0;

    tsec_index_seq=SearchToyoNumber(TSEC_INDEX);
    if(!otc_index_seq) {
        otc_index_seq=SearchToyoNumber(SEQ_OTC_INDEX);
    }
    otc_index_seq_2 = 0;
    tsec_unindex_seq=SearchToyoNumber(TSEC_UNINDEX);
    simsci_index_seq=SearchToyoNumber(SIMSCI_INDEX);
    for (i=0; i<MAX_CLASS; i++) {
        tsec_index20_seq[ i ] = SearchToyoNumber(TSEC_INDEX20[i]);
    }
    for(j=0; j<2; j++) {
        for ( i=0 ; i<max_TotalStockNo ; i++ ) {
            *(stock_tsec_seq[j]+i)=stock_ndx[j]+i;
            (stock_ndx[j]+i)->tsec_seq =-1;
        }
    }
    if ( NowSystemHour >= 9) {
        if ( Application->MessageBox("載入Mis1(增股資料)", "警告", MB_OKCANCEL) == IDOK) {
            read_tsec_seq();
            read_otc_seq();
        }
    }
    tsec_first_seq = -1;
    otc_first_seq = -1;
    for (i=0; i<2; i++) {
       for(j=0; j<2; j++) {
           for(k=0; k<MAX_MIS; k++) {
               data_seq[i][j][k] = -1;
               data_seq_2[i][j][k] = -1;
           }
       }
    }

    data_seq[0][0][5] = 0;
    data_seq[1][0][5] = 0;
    data_seq[0][0][12] = 0;
    data_seq[1][0][12] = 0;
    data_seq[0][1][5] = 0;
    data_seq[1][1][5] = 0;
    data_seq[0][1][12] = 0;
    data_seq[1][1][12] = 0;

    data_seq_2[0][0][16] = 0;
    data_seq_2[1][1][16] = 0;

    igmp_check_cnt[0][0] = 0;
    igmp_check_cnt[0][1] = 0;
    igmp_check_cnt[1][0] = 0;
    igmp_check_cnt[1][1] = 0;
    igmp_check_cnt[2][0] = 0;
    igmp_check_cnt[2][1] = 0;
    fg_timeout = 0;
    fgErrMsg = 0;
    merge_dodata = 0;
    tsec_chk_err = 0;
    tsec_size = 0;
    tsec_tail = 0;
    tsec_head = 0;
    SetTime_flag=0;
    write_tsec_seq_flag = 0;
    tsec_yes_flag = RECV_NO;
    tsec_class_total = 0;
    tsec_update_fg = 0;
    otc_update_fg = 0;
//Otc Initial
    otc_yes_flag = RECV_NO;
    otc_class_total = 0;
    for (i=0; i<MAX_CLASS; i++) {
        otc_1min_idx_seq[i] = -1;
    }
    if ((fp=fopen("OTC1MIN.ini", "r")) == NULL)  {
        MemoMsg("錯誤!!  無法開啟 OTC1MIN.ini  !!");
        return;
    }
    fgets(buf, 80, fp);      // skip comment line
    while (!feof(fp)) {
        fgets(buf, 80, fp);
        ptr = strtok(buf, " ");
        i = atoi(ptr);
        ptr = strtok(NULL, " ");
        if (ptr != NULL) {
            strncpy(stk_name, ptr, 6);
            stk_name[5] = ' ';
            stk_name[6] = 0;
            otc_1min_idx_seq[i] = SearchToyoNumber(stk_name);
        }
    }
    fclose(fp);
    /* v6.7.00 */
    memset(&Otc9995.deal_amount, 0, sizeof(struct mem_9995));
    memset(&OtcClose9995.deal_amount, 0, sizeof(struct mem_9995));
    memset(&TsecTime_15.Mis2_7.time_ptr, 0, sizeof(struct MARKET_TIME_15));
    memset(&OtcTime_15.Mis2_7.time_ptr, 0, sizeof(struct MARKET_TIME_15));
    for(i=0; i<2; i++) {
        FixedPriceTrade[i].Toyo = -1;
        FixedPriceTrade[i].Ok = 0;
    }
    Initial_RT_WARR();
    ST_GetNotchTbl();
    PreAddStockCnt = 0;
    fur_Ready_open = 0;
    stkfur_Ready_Slow = 0;
    StkFurCycleOnCount = -1;
    fg_stk_close = 0;
    if( fg_WarrInfoNews) {
        nTsecWarrFast_fg = nOtcWarrFast_fg = -1;
        nTsecWarrUpdateOk_fg = nOtcWarrUpdateOk_fg = 0;
        Foreign_Total = 0;
        nTsecWarrCnt = 0;
        unlink(sTsecWarrInfNewsFN_1);
        unlink(sTsecWarrInfNewsFN_2);
        unlink(sTsecWarrInfNewsFN_3);
        unlink(sOtcWarrInfNewsFN);
        unlink(sForeignInfNewsFN);
    }        
}

int numeric (const void *a, const void *b)
{
   return *(int *)a-(*((struct CCCC **)b))->tsec_seq;
}

struct CCCC *Seq_to_Toyo(int seq, int market)
{
   struct CCCC **bbb;
   int    key;

   key=seq;
   if(market == MK_TSEC)
       bbb=(struct CCCC **)bsearch(&key,(void *)stock_tsec_seq[0], max_TotalStockNo,sizeof(struct CCCC *), numeric);
   else if(market == MK_OTC)
       bbb=(struct CCCC **)bsearch(&key,(void *)stock_tsec_seq[1], max_TotalStockNo,sizeof(struct CCCC *), numeric);


   if (bbb==0)
      return NULL;
   else
      return (*bbb);
}

int sGetNotchTbl(stNotchTable *pTable, FILE *fp)
{
  char buff[80];

  if ( fgets(buff, 80, fp) ) { // 取得 notch 的個數
    int nNotchCount;
    int  i;
    nNotchCount = pTable->mTotCount = atoi(buff);
    for (i=0; i<nNotchCount; i++) {
      stNotchFmt *p;
	    if (fgets(buff, 80, fp) == NULL) { return 0; }
	    if (buff[0] == '#') { i--; continue; }
      p=pTable->mTable+i;
	    p->ref_price = atol(strtok(buff, " ,\t\r\n"));
	    p->notch_unit = atol(strtok(NULL, " ,\t\r\n"));
    }
  }
  return 1;
}

static void sInitMarketNotch(void)
{
  int i;
  stNotchTable sDefNotchTable = {6,
    {{ 500L, 1L},  { 1500L,   5L},{      5000L,  10L},
     {15000L,50L}, {100000L,100L},{0x7fffffffL, 500L}}};

  for ( i=0; i<eMaxMarketNotch; i++ ) {
    stNotchTable *p=sVipMarketNotch.mMarket+i;
    memcpy(p, &sDefNotchTable, sizeof(sDefNotchTable));
  }
}

// 新版的讀取
void ST_GetNotchTbl(void)
{
  char szFName[50];
  int i;

  sInitMarketNotch();
  for ( i=0; i<eMaxMarketNotch; i++ ) {
    FILE *pFILE;
    sprintf(szFName, "notch%d.tbl", i);
    pFILE=fopen(szFName, "rt");
    if ( NULL==pFILE ) { break; }
    if ( !sGetNotchTbl(sVipMarketNotch.mMarket+i, pFILE) ) {
      printf("Read %s error!\n", szFName);
    }
    fclose(pFILE);
  }
}
// 將檔差轉成價格，依照市場別不同而用不同的 table
// nDownLimit: 跌停價，nNowPrice: 要轉的價格
long NotchToPrice(int nMarket, long nBasePrice, unsigned char nNotch)
{
  int  i;
  long ref_price;
  long  dis_notch, diff;
  stNotchTable *p=sVipMarketNotch.mMarket+nMarket;

  if ( (nBasePrice == 0L) || (nNotch == 0xff) ||
       (nMarket<0) || (nMarket>=eMaxMarketNotch) )
  { return(0L); }

  ref_price = nBasePrice;
  dis_notch = (long)nNotch;
  for (i=0; i<p->mTotCount && dis_notch>0L; i++) {
    if (ref_price < p->mTable[i].ref_price) {
      diff = (p->mTable[i].ref_price - ref_price) /
              p->mTable[i].notch_unit;
      if (dis_notch < diff)
      	break;
      else {
	      ref_price = p->mTable[i].ref_price;
	      dis_notch -= diff;
      }
    }
  }
  return(ref_price + p->mTable[i].notch_unit * dis_notch);

}

int stock_add_sort( const void *a, const void *b)
{
    if( ((struct AUTO_ADD_STK *)a)->mkt != ((struct AUTO_ADD_STK *)b)->mkt)
        return ((struct AUTO_ADD_STK *)a)->mkt - ((struct AUTO_ADD_STK *)b)->mkt;
   return( strcmp(((struct AUTO_ADD_STK *)a)->stock, ((struct AUTO_ADD_STK *)b)->stock));
}

int chk_class_type(char market, char *stk_no, int class_no)
{
  int  i, j, chk_len;
  char match_fg=1;

  if (market != 1 && market != 2)
    return(-1);

  for (i=0; i<chkstock_cnt; i++) {
    chk_len = strlen(chkstock[i].st_code);
    if (chk_len != strlen(stk_no))
      continue;
    match_fg = 1;
    for (j=0; j<chk_len && match_fg; j++) {
      if (chkstock[i].st_code[j]  == '?')
	;  // don't care
      else if (stk_no[j] >= chkstock[i].st_code[j] && stk_no[j] <= chkstock[i].end_code[j])
	;  // match
      else
	match_fg = 0;
    }
    if (match_fg)
      return(chkstock[i].ruso_class[market-1]);
  }

  for (i=0; i<chkclass_cnt; i++) {
    if (chkclass[i].mkt != market)
      continue;
    if (chkclass[i].tse_class == class_no)
      return(chkclass[i].ruso_class);
  }

  return(20);  // other class
}

void get_chkclass_tbl(char *fname)
{
  FILE *fp;
  char buf[128], *token_ptr;

  if ((fp=fopen(fname,"r")) == NULL) {
    sprintf(buf, "Open %s file error !!\n", fname);
    MemoMsg(buf);
    return;
  }
  while (fgets(buf, 128, fp)) {
    if (buf[0] == ';')   // comments
      continue;
    if ((token_ptr=strtok(buf, "= \t\r\n")) == NULL)
      continue;
    if (strcmpi(token_ptr, "STK") == 0) {
      if ((token_ptr=strtok(NULL, "= \t\r\n")) == NULL)
	continue;
      strcpy(chkstock[chkstock_cnt].st_code, token_ptr);
      if ((token_ptr=strtok(NULL, " \t\r\n")) == NULL)
	continue;
      strcpy(chkstock[chkstock_cnt].end_code, token_ptr);
      if ((token_ptr=strtok(NULL, " \t\r\n")) == NULL)
	continue;
      chkstock[chkstock_cnt].ruso_class[0] = atoi(token_ptr);
      if ((token_ptr=strtok(NULL, " \t\r\n")) == NULL)
	continue;
      chkstock[chkstock_cnt].ruso_class[1] = atoi(token_ptr);
      chkstock_cnt ++;
    }
    else if (strcmpi(token_ptr, "CLASS") == 0) {
      if ((token_ptr=strtok(NULL, "= \t\r\n")) == NULL)
	continue;
      chkclass[chkclass_cnt].mkt = atoi(token_ptr);
      if ((token_ptr=strtok(NULL, " \t\r\n")) == NULL)
	continue;
      chkclass[chkclass_cnt].tse_class = atoi(token_ptr);
      if ((token_ptr=strtok(NULL, " \t\r\n")) == NULL)
	continue;
      chkclass[chkclass_cnt].ruso_class = atoi(token_ptr);
      chkclass_cnt ++;
    }
  }
  fclose(fp);
}

void WriteAutoAddStock_V5(char *inf_filename)
{
    FILE  *temp_f1;
    char  buff[256];
    int   toyo, type;

    if((temp_f1=fopen(inf_filename, "w")) != NULL) {
        sprintf(buff, "ADD_DATE=%04d%02d%02d\n", NowSystemYear, NowSystemMonth, NowSystemDay);
        fputs(buff, temp_f1);
        sprintf(buff, "ADD_STK=%d\n", nAddStockCnt);
        fputs(buff, temp_f1);
        qsort((void *)AddStock, nAddStockCnt, sizeof(struct AUTO_ADD_STK), stock_add_sort);
        for(int i=0; i<nAddStockCnt; i++) {
            toyo = 3980 + i;
            type = chk_class_type(AddStock[i].mkt, AddStock[i].stock, atoi(AddStock[i].business));
            AddStock[i].toyo = toyo;
            memset(buff, 0, 256);
            sprintf(buff, "%-2d;%-6s;%-6s  ;%-50s;%10s;%05d;%02d  ;%d;%d;0;0;0;0;000000000000;00000000;99999999\n",
                AddStock[i].mkt, AddStock[i].stock, AddStock[i].chi_name,
                AddStock[i].eng_name, "", AddStock[i].toyo, type, (AddStock[i].mkt==MK_TSEC)?0:1,
                (NotchToPrice(AddStock[i].mkt, AddStock[i].dn_bound, AddStock[i].up_bound>254)?1:0));
            fputs(buff, temp_f1);
            StockMem[toyo].mkt = AddStock[i].mkt;
            StockMem[toyo].type = type;
            StockMem[toyo].y_close  = AddStock[i].y_close;
            StockMem[toyo].up_bound = AddStock[i].up_bound;
            StockMem[toyo].dn_bound = AddStock[i].dn_bound;
            strncpy(StockMem[toyo].stock_no, AddStock[i].stock, 6);
            strncpy(StockMem[toyo].chi_name, AddStock[i].chi_name, 6);
            strncpy( (stock_ndx[0]+TotalStockNo)->stock, AddStock[i].stock, 6 );
            (stock_ndx[0]+TotalStockNo)->ndx = toyo;
            (stock_ndx[0]+TotalStockNo)->bond_ptr = NULL;  // v6.8.0

            TotalStockNo++;
            qsort((void *)stock_ndx[0],TotalStockNo,sizeof(struct CCCC),stock_ndx_sort);
            MemTransferToNewMis1BinFmtAndSend( toyo );
        }
        fclose(temp_f1);
    }
    else {
        Logf("產生自動增股<Stk_Info.Add>檔案失敗!");
    }
}

void AddAutoAddStkList( char * line )
{
    FILE * pf = fopen( "auto_add_stk.log", "a+t" );
    if (pf==NULL) {
        return;
    }
    fprintf( pf, "%s\n", line );
    fclose( pf );
    gStat.auto_add_stk_update_cnt = 1;
}

void AutoAddStock_V8(const IP_FMT& prot, int market)
{
    char stock[10];
    char chi_name[10];
    char eng_name[50];
    char business[10];
    char buff[256], *p;
    int p_size, chi_RealPoint;

    if ( !strncmp(prot.tsec_mis1_v8.stock_no, "000000", 6)) { 
        return;
    }
    strncpy(stock, prot.tsec_mis1_v8.stock_no, 6);
    stock[6] = 0;
    for (int i=0; i<nAddStockCnt; i++) {
        if ( !strncmp(AddStock[i].stock, stock, 6)) {
            return;
        }
    }
    if (nAddStockCnt < MAX_ADD_STOCK)    {
        AddStock[nAddStockCnt].mkt = market;
        strncpy(stock, prot.tsec_mis1_v8.stock_no, 6);
        stock[6] = 0;
        for (chi_RealPoint =0; chi_RealPoint<16; chi_RealPoint++) {
            if(prot.tsec_mis1_v8.chi_name[chi_RealPoint] == 0x20 || prot.tsec_mis1_v8.chi_name[chi_RealPoint] == 0x00) {
                break;
            }
        }
        if (chi_RealPoint > 6) {
            strncpy(chi_name, prot.tsec_mis1_v8.stock_no, 6);
        }
        else {
            strncpy(chi_name, prot.tsec_mis1_v8.chi_name, 6);
        }
        strncpy(eng_name, prot.tsec_mis1_v8.chi_name, 16);
        chi_name[6] = 0;
        eng_name[16] = 0;
        while((p = strchr(chi_name, ' ')) != NULL) {
            p_size = 6 - (p - chi_name);
            memcpy(p, p+1, p_size);
        }

        strncpy(business, prot.tsec_mis1_v8.business, 2);
        business[2] = 0;
        strcpy(AddStock[nAddStockCnt].stock, stock);
        strcpy(AddStock[nAddStockCnt].chi_name, chi_name);
        strcpy(AddStock[nAddStockCnt].eng_name, eng_name);
        strcpy(AddStock[nAddStockCnt].business, business);
        if (market == MK_TSEC) {
            AddStock[nAddStockCnt].y_close = BCD_to_Long(prot.tsec_mis1_v8.y_close,  5)/100;
            AddStock[nAddStockCnt].up_bound= BCD_to_Long(prot.tsec_mis1_v8.up_bound, 5)/100;
            AddStock[nAddStockCnt].dn_bound= BCD_to_Long(prot.tsec_mis1_v8.dn_bound, 5)/100;
        }
        else {
            AddStock[nAddStockCnt].y_close = BCD_to_Long(prot.otc_mis1_v8.y_close,  5)/100;
            AddStock[nAddStockCnt].up_bound= BCD_to_Long(prot.otc_mis1_v8.up_bound, 5)/100;
            AddStock[nAddStockCnt].dn_bound= BCD_to_Long(prot.otc_mis1_v8.dn_bound, 5)/100;
        }
        sprintf(buff, "%2d:%2d;%6s;%8s",  nAddStockCnt, AddStock[nAddStockCnt].mkt, stock, chi_name);
        AddAutoAddStkList(buff);
        nAddStockCnt++;
    }
}

int WriteStkStopNewsFile(int re_chk_fg, int seq, int tmStop_time, int tmStart_time)
{
    int i, j, fg_WriteAll, nToyo;
    FILE  *temp_f1;
    time_t now;
    struct tm *pNow;
    char  buff[256], stock_id[10], stk_name[10];
    int  nCnt=0;

    time(&now);
    pNow = localtime(&now);

    if( re_chk_fg)  {
        for(i=0; i<nStkStopCnt; i++) {
            if(StkStopInfo[i].toyo == seq) {
                if( (StkStopInfo[i].stop_time == tmStop_time) && (StkStopInfo[i].start_time == tmStart_time)) {
                    return 0;
                }
                else {
                    StkStopInfo[i].stop_time = tmStop_time;
                    StkStopInfo[i].start_time = tmStart_time;
                    break;
                }
            }

        }
        if(i>= nStkStopCnt) {
            StkStopInfo[nStkStopCnt].toyo = seq;
            StkStopInfo[nStkStopCnt].stop_time = tmStop_time;
            StkStopInfo[nStkStopCnt].start_time = tmStart_time;
            nStkStopCnt++;
        }
    }
    for(i=0; i<max_TotalStockNo; i++) {
        if( StockMem[i].fg_war_stk & 0x03) {
            nCnt = 1;
            break;
        }
    }
    if( !nCnt && !nStkStopCnt && !nEmgStkStopCnt)
        return 0;
    if ((temp_f1=fopen(sStkStopNewsFullTempName,"w")) != NULL) {
        sprintf(buff, "股票交易狀態變更總表< 更新時間 %02d:%02d:%02d>\n",
                    pNow->tm_hour, pNow->tm_min, pNow->tm_sec);
        fputs(buff, temp_f1);
        fputs(sStkStopNewsHeadStr, temp_f1);
        fputs("\n                                  當  時 當  時 當  時 當  時 當  時\n", temp_f1);
          fputs("狀    態 時    間 股代   股  名   委買價 委賣價 成交價 漲跌點 成交量\n", temp_f1);
        fputs("===============================================================\n", temp_f1);
        for(i=0; i<max_TotalStockNo; i++) {
            if(StockMem[i].fg_war_stk & 0x01) {
                strncpy(stock_id, StockMem[i].stock_no, 6);
                stock_id[6]='\0';
                strncpy(stk_name, StockMem[i].chi_name, 6);
                stk_name[6]='\0';
                sprintf(buff, "異常推介 %02d:%02d:%02d %6s %-6s %7.2f%7.2f%7.2f%7.2f%8ld\n",
                        8, 0, 0,
                        stock_id, stk_name, StockMem[i].buy_price[0]/100.0, StockMem[i].sell_price[0]/100.0,
                        StockMem[i].deal_price/100.0,
                        (StockMem[i].deal_sheet)?(StockMem[i].deal_price-StockMem[i].y_close)/100.0:0.0,
                        StockMem[i].deal_sheet);
                fputs(buff, temp_f1);
            }
            if(StockMem[i].fg_war_stk & 0x02) {
                strncpy(stock_id, StockMem[i].stock_no, 6);
                stock_id[6]='\0';
                strncpy(stk_name, StockMem[i].chi_name, 6);
                stk_name[6]='\0';
                sprintf(buff, "特殊異常 %02d:%02d:%02d %6s %-6s %7.2f%7.2f%7.2f%7.2f%8ld\n",
                        8, 0, 0,
                        stock_id, stk_name, StockMem[i].buy_price[0]/100.0, StockMem[i].sell_price[0]/100.0,
                        StockMem[i].deal_price/100.0,
                        (StockMem[i].deal_sheet)?(StockMem[i].deal_price-StockMem[i].y_close)/100.0:0.0,
                        StockMem[i].deal_sheet);
                fputs(buff, temp_f1);
            }
        }
        for(i=0; i<nStkStopCnt; i++) {
                nToyo = StkStopInfo[i].toyo;
                strncpy(stock_id, StockMem[nToyo].stock_no, 6);
                stock_id[6]='\0';
                strncpy(stk_name, StockMem[nToyo].chi_name, 6);
                stk_name[6]='\0';
                sprintf(buff, "暫    停 %02d:%02d:%02d %6s %-6s %7.2f%7.2f%7.2f%7.2f%8ld\n",
                        StkStopInfo[i].stop_time /10000l, (StkStopInfo[i].stop_time /100l)%100l, StkStopInfo[i].stop_time %100l,
                        stock_id, stk_name, StockMem[nToyo].buy_price[0]/100.0, StockMem[nToyo].sell_price[0]/100.0,
                        StockMem[nToyo].deal_price/100.0,
                        (StockMem[nToyo].deal_sheet)?(StockMem[nToyo].deal_price-StockMem[nToyo].y_close)/100.0:0.0,
                        StockMem[nToyo].deal_sheet);
                fputs(buff, temp_f1);
                if(StkStopInfo[i].start_time != 999999) {
                    sprintf(buff, "恢    復 %02d:%02d:%02d %6s %-6s %7.2f%7.2f%7.2f%7.2f%8ld\n",
                        StkStopInfo[i].start_time /10000l, (StkStopInfo[i].start_time /100l)%100l, StkStopInfo[i].start_time %100l,
                        stock_id, stk_name, StockMem[nToyo].buy_price[0]/100.0, StockMem[nToyo].sell_price[0]/100.0,
                        StockMem[nToyo].deal_price/100.0,
                        (StockMem[nToyo].deal_sheet)?(StockMem[nToyo].deal_price-StockMem[nToyo].y_close)/100.0:0.0,
                        StockMem[nToyo].deal_sheet);
                    fputs(buff, temp_f1);
                }
        }
        fputs("===============================================================\n", temp_f1);
        fputs("\n狀    態 時    間 股代   股  名   當  時 當  時 當  時 當  時 當  時\n", temp_f1);
          fputs("                                  委買價 委賣價 成交價 漲跌點 成交量\n", temp_f1);
        for(i=0; i<nEmgStkStopCnt; i++) {
                nToyo = stEmgStkStopInfo[i].index;
                strncpy(stock_id, emg_stk_info[nToyo].stock_no, 6);
                stock_id[6]='\0';
                strncpy(stk_name, emg_stk_info[nToyo].stk_name_chi, 6);
                stk_name[6]='\0';
                sprintf(buff, "暫    停 %02d:%02d:%02d %6s %-6s %7.2f%7.2f%7.2f%7.2f%8ld\n",
                        stEmgStkStopInfo[i].stop_time /10000l, (stEmgStkStopInfo[i].stop_time /100l)%100l, stEmgStkStopInfo[i].stop_time %100l,
                        stock_id, stk_name, emg_stk_info[nToyo].buy.price/100.0, emg_stk_info[nToyo].sell.price/100.0,
                        emg_stk_info[nToyo].make/100.0,
                        (emg_stk_info[nToyo].vol)?(emg_stk_info[nToyo].make-emg_stk_info[nToyo].yes_avg_price)/100.0:0.0,
                        emg_stk_info[nToyo].vol);
                fputs(buff, temp_f1);
                if(StkStopInfo[i].start_time != 999999) {
                    sprintf(buff, "恢    復 %02d:%02d:%02d %6s %-6s %7.2f%7.2f%7.2f%7.2f%8ld\n",
                        stEmgStkStopInfo[i].start_time /10000l, (stEmgStkStopInfo[i].start_time /100l)%100l, stEmgStkStopInfo[i].start_time %100l,
                        stock_id, stk_name, emg_stk_info[nToyo].buy.price/100.0, emg_stk_info[nToyo].sell.price/100.0,
                        emg_stk_info[nToyo].make/100.0,
                        (emg_stk_info[nToyo].vol)?(emg_stk_info[nToyo].make-emg_stk_info[nToyo].yes_avg_price)/100.0:0.0,
                        emg_stk_info[nToyo].vol);
                    fputs(buff, temp_f1);
                }

        }
        fputs("狀態說明：\n", temp_f1);
        fputs("異常推介：有線電視理財節目異常推介個股\n", temp_f1);
        fputs("特殊異常：特殊異常證券\n", temp_f1);
        fputs("暫    停：交易所公告之暫停交易商品\n", temp_f1);
        fputs("恢    復：交易所公告之恢復交易商品\n", temp_f1);
        fclose(temp_f1);
        unlink(sStkStopNewsFullOutName);
        rename(sStkStopNewsFullTempName, sStkStopNewsFullOutName);
    }
    else
        fg_Write_Delay_err = 1;
    return 1;        
}

static int sCmpStk(const void *arg1, const void *arg2)
{
  struct AAAA *p1=(struct AAAA*)arg1;
  struct AAAA *p2=(struct AAAA*)arg2;

  return (p1->time-p2->time);
}

void WriteDelayCloseFile(void)
{
    int i, j, nCnt, nInx;
    FILE  *temp_f1;
    time_t now;
    struct tm *pNow;
    struct AAAA  *pStkDlyClose;
    char  buff[256], stock_id[11], stk_name[10], sStockTotle[128], *p;

    time(&now);
    pNow = localtime(&now);

    sStockTotle[0] = 0;
    nCnt =0;
    for(i=0; i<max_TotalStockNo; i++) {
        //86 權證不產生 以免太多資料
        if(((StockMem[i].warn_flag & BIT5) == BIT5) && (StockMem[i].type != 86)) {
            nCnt++;
            if(nCnt < 5)    {
                memset(stock_id, ' ', 10);
                strncpy(stock_id, StockMem[i].stock_no, 6);
                stock_id[10] = '\0';   // prevent access overrun, as reported by codeguard
                p = strchr(stock_id, ' ');
                *p=',';
                *(p+1)='\0';
                strcat(sStockTotle, stock_id);
            }
        }
    }
    if( !nCnt)  return;


    pStkDlyClose = (struct AAAA *)malloc(nCnt*sizeof(struct AAAA));
    if (pStkDlyClose==NULL) {
        return;
    }
    nInx =0;
    for(i=0; i<max_TotalStockNo; i++) {
        if(((StockMem[i].warn_flag & BIT5) == BIT5) && (StockMem[i].type != 86)) {
            memcpy((char *)&(pStkDlyClose[nInx]), (char *)&(StockMem[i]), sizeof(struct AAAA));
            nInx++;
            if(nCnt <= nInx)   break;
        }
    }
    qsort(pStkDlyClose, nCnt, sizeof(struct AAAA), sCmpStk);


    if ((temp_f1=fopen(sDelayCloseFullTempName,"w")) != NULL) {
        sprintf(buff, "延收股票(%3d檔 更新時間 %02d:%02d:%02d):%s\n",nCnt,  pNow->tm_hour,
                                                    pNow->tm_min, pNow->tm_sec, sStockTotle);
        fputs(buff, temp_f1);
        fputs("                                試撮合 試撮合 當  時 當  時\n", temp_f1);
        fputs("狀態 時    間 股代   股  名     委買價 委賣價 成交價 漲跌點\n", temp_f1);
        fputs("===========================================================\n", temp_f1);
        for(i=0; i<nCnt; i++) {
            if((pStkDlyClose[i].warn_flag & BIT5) == BIT5) {
                strncpy(stock_id, pStkDlyClose[i].stock_no, 6);
                stock_id[6]='\0';
                strncpy(stk_name, pStkDlyClose[i].chi_name, 6);
                stk_name[6]='\0';
                sprintf(buff, "延收 %02d:%02d:%02d %6s %-6s   %7.2f%7.2f%7.2f%7.2f\n",
                        pStkDlyClose[i].time /3600l, (pStkDlyClose[i].time /60l)%60l, pStkDlyClose[i].time %60l,
                        stock_id, stk_name, pStkDlyClose[i].buy_price[0]/100.0, pStkDlyClose[i].sell_price[0]/100.0,
                        pStkDlyClose[i].deal_price/100.0, (pStkDlyClose[i].deal_price-pStkDlyClose[i].y_close)/100.0);

                fputs(buff, temp_f1);
            }
        }
        fputs("===========================================================\n", temp_f1);
        fputs("狀態 時    間 股代   股  名     試撮合 試撮合 當  時 當  時\n", temp_f1);
        fputs("                                委買價 委賣價 成交價 漲跌點\n", temp_f1);

        fclose(temp_f1);
        unlink(sDelayCloseFullOutName);
        rename(sDelayCloseFullTempName, sDelayCloseFullOutName);
    }
    else {
        fg_Write_Delay_err = 1;
    }
    free(pStkDlyClose);
}

// 設定cycle的第一檔toyo
void ResetMainCycle(int market)
{
    switch(market)  {
        case MK_TSEC:
            if(!write_tsec_seq_flag && tsec_first_seq > 0) {
                tsec_first_seq = -1;
            }
            break;
        case MK_OTC:
            if(!write_otc_seq_flag && otc_first_seq > 0) {
                otc_first_seq = -1;
            }
            break;
    }
}

void WriteForeignInfNews_V6(char *sFileName)
{
    int         d_seq;
    FILE        *pfNewsLog;
    char        strLog[256];
    char        strSubLog[256];
    char        stock[10];
    char        chi_name[10];

    if((pfNewsLog = _fsopen(sFileName,"w",SH_DENYNO)) == NULL) {
        Logf("%s-檔案開啟失敗!!",sFileName);
        return;
    }
    fputs("境外商品來台上市股票交易單位、幣別與面額說明\n", pfNewsLog);
    fputs("股代   股名 交易單位股數  交易幣別   面額\n", pfNewsLog);
    for(int i=0; i<Foreign_Total && i<MAX_FOREIGN_INFO; i++)  {
        memcpy(stock, StockMem[Foreign_Inf[i].seq].stock_no, 6);
        stock[6] = 0;
        memcpy(chi_name, StockMem[Foreign_Inf[i].seq].chi_name, 6);
        chi_name[6] = 0;
        sprintf(strLog, "%-6s%-6s%12d   %3s       %s   \n",stock, chi_name, Foreign_Inf[i].unit_type, Foreign_Inf[i].money_type,
        (Foreign_Inf[i].non_10 == ' ')?"十元":"非十元");
        fputs(strLog, pfNewsLog);
    }
    fclose(pfNewsLog);
}

void WriteForeignInfNews(char *sFileName)
{
    int         d_seq;
    FILE        *pfNewsLog;
    char        strLog[256];
    char        strSubLog[256];
    char        stock[10];
    char        chi_name[10];

    if((pfNewsLog = _fsopen(sFileName,"a+",SH_DENYNO)) == NULL) {
        MemoMsg("%s-檔案開啟失敗!!",sFileName);
        return;
    }
    fputs("境外商品來台上市股票交易單位及幣別說明\n", pfNewsLog);
    fputs("股代   股名 交易單位股數  交易幣別    股代   股名 交易單位股數  交易幣別\n", pfNewsLog);
    for(int i=0; i<Foreign_Total && i<(MAX_FOREIGN_INFO-1); i +=2)  {
        memcpy(stock, StockMem[Foreign_Inf[i].seq].stock_no, 6);
        stock[6] = 0;
        memcpy(chi_name, StockMem[Foreign_Inf[i].seq].chi_name, 6);
        chi_name[6] = 0;
        sprintf(strLog, "%-6s%-6s%12d   %3s         ",stock, chi_name, Foreign_Inf[i].unit_type, Foreign_Inf[i].money_type);
        if((i+1)<Foreign_Total) {
            memcpy(stock, StockMem[Foreign_Inf[i+1].seq].stock_no, 6);
            stock[6] = 0;
            memcpy(chi_name, StockMem[Foreign_Inf[i+1].seq].chi_name, 6);
            chi_name[6] = 0;
            sprintf(strSubLog, "%-6s%-6s%12d   %3s    \n",stock, chi_name, Foreign_Inf[i+1].unit_type, Foreign_Inf[i+1].money_type);
            strcat(strLog, strSubLog);
        }
        fputs(strLog, pfNewsLog);
    }
    fclose(pfNewsLog);
}

int  CoverNewInxTimePtr(struct ONEMIN_TIME OldTime, struct TIME_15 *NewTime, int nAddPtr)
{

    if((OldTime.idx_time >= 9999) && (nAddPtr < 0))
        return 0;
    if((OldTime.idx_time >= 9999) && (nAddPtr == 0)) {
        NewTime->idx_time = 999999;
        NewTime->time_ptr = 1081;
        return 1;
    }

    NewTime->time_ptr = OldTime.time_ptr *4+nAddPtr;
    if(NewTime->time_ptr < 0)
        return 0;
    NewTime->idx_time = OldTime.idx_time;
    if(nAddPtr < 0)
       NewTime->idx_time = (NewTime->idx_time-1)*100 + (4+nAddPtr)*15;
    else
       NewTime->idx_time = NewTime->idx_time*100;
    if( NewTime->time_ptr > 1081)
      NewTime->time_ptr = 1081;
    return 1;
}

void IpMis1UpdateToMemAndSend_V8(const IP_FMT& prot, int market) {
	static int writeSymbolNewsFile = 1;
    long price_y, price_h, price_l, vol, nUnitType;
    int  seq, seq_tmp;
    int  stkopt5_seq;

    if (market == MK_TSEC) {
        if( !memcmp(prot.tsec_mis1_v8.spec_fg, "AL", 2) || !memcmp(prot.tsec_mis1_v8.spec_fg, "NE", 2)) {
            return;
        }
        if (prot.tsec_mis1_v8.stock_no[0]>='A' && prot.tsec_mis1_v8.stock_no[0]<='Z') {
            return;
        }
    }
    else if (market == MK_OTC){
        if( !memcmp(prot.otc_mis1_v8.spec_fg, "AL", 2) || !memcmp(prot.otc_mis1_v8.spec_fg, "NE", 2)) {
            return;
        }
        if (prot.otc_mis1_v8.stock_no[0]>='A' && prot.otc_mis1_v8.stock_no[0]<='Z') {
            return;
        }
    }
    seq = SearchToyoNumber( prot.tsec_mis1_v8.stock_no);
    if (seq <= 0) {
        AutoAddStock_V8(prot, market);
        return;
    }
    if (market == MK_TSEC) {
        if (tsec_first_seq == -1) {
            tsec_first_seq = seq;
        }
        else if(tsec_first_seq == seq) {
            if (vip_cycle.mis1_fg <= 3){
                vip_cycle.mis1_fg++;
            }
            if (!SetTime_flag) {
                start_cycle = 1;
            }
            if( !write_tsec_seq_flag) {
                write_tsec_seq_flag=1;
            }
        }
    }
    else if (market == MK_OTC) {
        if (otc_first_seq == -1) {
            otc_first_seq = seq;
        }
        else if ((otc_first_seq == seq) && !write_otc_seq_flag) {
            write_otc_seq_flag=1;
        }
    }

    if (writeSymbolNewsFile && write_tsec_seq_flag && write_otc_seq_flag)   {
        if ( fg_WarrInfoNews) {
            WriteForeignInfNews_V6(sForeignInfNewsFN);
            WriteStkStopNewsFile(0, 0, 0, 0);
        }
        if ( !fg_wBufInfo && fg_day_info)   {
            WriteTsecOtcBusInfo();
            WriteTsecOtcTodaySet();
        }
        if (nAddStockCnt) {
            if (nAddStockCnt != PreAddStockCnt) {
                char cmd_buf[128];
                WriteAutoAddStock_V5(ADD_STK_FNAME);
                sprintf(cmd_buf,"mkcrc %s 1",ADD_STK_FNAME);
                system(cmd_buf);
                //spawnl(P_NOWAIT, "mkcrc", ADD_STK_FNAME, "1");
                PreAddStockCnt = nAddStockCnt;
            }
        }
        writeSymbolNewsFile = 0;
    }

    if (market == MK_OTC) {
        if (prot.otc_mis1_v8.warrant.fg == 'Y') {
            StockMem[seq].warr_price = (long)BCD_to_Long(prot.otc_mis1_v8.warrant.price,  5)/100;
            StockMem[seq].y_deal_sheet = BCD_to_Long(prot.otc_mis1_v8.warrant.y_deal_sheet,  5);
            StockMem[seq].y_cancel_sheet = BCD_to_Long(prot.otc_mis1_v8.warrant.y_cancel_sheet,  5);
            StockMem[seq].total_shares = BCD_to_Long(prot.otc_mis1_v8.warrant.total_shares,  5);
            if ( fg_stkfur_trade || WarrNewMis1_fg)  //td
                StockMem[seq].use_rate = BCD_to_Long(prot.otc_mis1_v8.warrant.rate,  4);
            else
                StockMem[seq].use_rate = BCD_to_Long(prot.otc_mis1_v8.warrant.rate,  3);
        }
        StockMem[seq].day_trade_mark = prot.otc_mis1_v8.day_trade_mark; 	//可現股當沖註記
        StockMem[seq].remit_flat_Margin = prot.otc_mis1_v8.remit_flat_Margin; 	//可現股當沖註記
        StockMem[seq].remit_flat_Security = prot.otc_mis1_v8.remit_flat_Security; 	//可現股當沖註記

        memcpy(StockMem[seq].money_type, prot.otc_mis1_v8.money_type, 3);
        nUnitType = BCD_to_Long(prot.otc_mis1_v8.unit_type,  3);
        StockMem[seq].unit_type = nUnitType;
        if ( !write_otc_seq_flag && fg_WarrInfoNews)  {
            if (prot.otc_mis1_v8.war_sup_stk == 'Y')
                StockMem[seq].fg_war_stk |= 0x01;
            if (prot.otc_mis1_v8.spc_war_stk == 'Y')
                StockMem[seq].fg_war_stk |= 0x02;
            if ( memcmp(prot.otc_mis1_v8.money_type, "   ", 3) || nUnitType != 1000 || prot.otc_mis1_v8.non_10 != ' ')  {
                if (Foreign_Total<MAX_FOREIGN_INFO) {
                    Foreign_Inf[Foreign_Total].seq = seq;
                    Foreign_Inf[Foreign_Total].unit_type = nUnitType;
                    Foreign_Inf[Foreign_Total].non_10 = prot.otc_mis1_v8.non_10;
                    if( !memcmp(prot.otc_mis1_v8.money_type, "   ", 3)) {
                        memcpy(Foreign_Inf[Foreign_Total].money_type, "NTD", 3);
                    }
                    else {
                        memcpy(Foreign_Inf[Foreign_Total].money_type, prot.otc_mis1_v8.money_type, 3);
                    }
                    Foreign_Inf[Foreign_Total].money_type[3] = 0;
                    Foreign_Total++;
                }
                else {
                    Logf("err#1: Foreign_Total>=%d", MAX_FOREIGN_INFO);
                }
            }
        }
    }
    else {
        if (prot.tsec_mis1_v8.warrant.fg == 'Y')    {
            StockMem[seq].warr_price = (long)BCD_to_Long(prot.tsec_mis1_v8.warrant.price, 5);
            StockMem[seq].y_deal_sheet = BCD_to_Long(prot.tsec_mis1_v8.warrant.y_deal_sheet, 5);
            StockMem[seq].y_cancel_sheet = BCD_to_Long(prot.tsec_mis1_v8.warrant.y_cancel_sheet, 5);
            StockMem[seq].total_shares = BCD_to_Long(prot.tsec_mis1_v8.warrant.total_shares, 5);
            if( fg_stkfur_trade || WarrNewMis1_fg) {
                StockMem[seq].use_rate = BCD_to_Long(prot.tsec_mis1_v8.warrant.rate,  4);
            }
            else {
                StockMem[seq].use_rate = BCD_to_Long(prot.tsec_mis1_v8.warrant.rate,  3);
            }
        }
        StockMem[seq].day_trade_mark = prot.tsec_mis1_v8.day_trade_mark; 	//可現股當沖註記
        StockMem[seq].remit_flat_Margin = prot.tsec_mis1_v8.remit_flat_Margin; 	//可現股當沖註記
        StockMem[seq].remit_flat_Security = prot.tsec_mis1_v8.remit_flat_Security; 	//可現股當沖註記

        memcpy(StockMem[seq].money_type, prot.tsec_mis1_v8.foreign.money_type, 3);
        nUnitType = BCD_to_Long(prot.tsec_mis1_v8.foreign.unit_type,  3);
        StockMem[seq].unit_type = nUnitType;
        if ( !write_tsec_seq_flag && fg_WarrInfoNews )  {
            if (prot.tsec_mis1_v8.war_sup_stk == 'Y') {
                StockMem[seq].fg_war_stk |= 0x01;
            }
            if (prot.tsec_mis1_v8.spc_war_stk == 'Y') {
                StockMem[seq].fg_war_stk |= 0x02;
            }
            if ( memcmp(prot.tsec_mis1_v8.foreign.money_type, "   ", 3) || nUnitType != 1000 || prot.tsec_mis1_v8.non_10 != ' ' )  {
                if (Foreign_Total<MAX_FOREIGN_INFO) {
                    Foreign_Inf[Foreign_Total].seq = seq;
                    Foreign_Inf[Foreign_Total].unit_type = nUnitType;
                    Foreign_Inf[Foreign_Total].non_10 = prot.tsec_mis1_v8.non_10;
                    if( !memcmp(prot.tsec_mis1_v8.foreign.money_type, "   ", 3)) {
                        memcpy(Foreign_Inf[Foreign_Total].money_type, "NTD", 3);
                    }
                    else {
                        memcpy(Foreign_Inf[Foreign_Total].money_type, prot.tsec_mis1_v8.foreign.money_type, 3);
                    }
                    Foreign_Inf[Foreign_Total].money_type[3] = 0;
                    Foreign_Total++;
                }
                else {
                    Logf("err#2: Foreign_Total>=%d", MAX_FOREIGN_INFO);
                }
            }
        }
    }
    StockMem[seq].warn_flag &= 0xf0; // 警示股  && v6.8.0 89.6 limited stocks
    if (market == MK_OTC) {
        StockMem[seq].warn_flag |= (((uchar)BCD_to_Long(&prot.otc_mis1_v8.excep)) & 0x0f);
        price_y = BCD_to_Long(prot.otc_mis1_v8.y_close,  5)/100;
        price_h = BCD_to_Long(prot.otc_mis1_v8.up_bound, 5)/100;
        price_l = BCD_to_Long(prot.otc_mis1_v8.dn_bound, 5)/100;

        memcpy(StockMem[seq].business, prot.otc_mis1_v8.business, 2);
        memcpy(StockMem[seq].br, prot.otc_mis1_v8.br, 2);
        StockMem[seq].excep = BCD_to_Long(&prot.otc_mis1_v8.excep);
    }
    else {
        StockMem[seq].warn_flag |= (((uchar)BCD_to_Long(&prot.tsec_mis1_v8.excep)) & 0x0f);
        price_y = BCD_to_Long(prot.tsec_mis1_v8.y_close,  5)/100;
        price_h = BCD_to_Long(prot.tsec_mis1_v8.up_bound, 5)/100;
        price_l = BCD_to_Long(prot.tsec_mis1_v8.dn_bound, 5)/100;

        memcpy(StockMem[seq].business, prot.tsec_mis1_v8.business, 2);
        memcpy(StockMem[seq].br, prot.tsec_mis1_v8.br, 2);
        StockMem[seq].excep = BCD_to_Long(&prot.tsec_mis1_v8.excep);
    }
    if ( StockMem[seq].UpdateMis1Count <= 3 ) {
        if (price_y == 0 || price_h == 0 || price_l == 0)   {
            StockMem[seq].UpdateMis1Count = 0;
            return;
        }
        if ( StockMem[seq].y_close != price_y || StockMem[seq].up_bound != price_h || StockMem[seq].dn_bound != price_l )  {
            if ( price_y <= price_h && price_y >= price_l )  {
                StockMem[seq].y_close  = price_y;
                StockMem[seq].up_bound = price_h;
                StockMem[seq].dn_bound = price_l;
                StockMem[seq].UpdateMis1Count = 0;
                if ( (stkopt5_seq = CopyStkOptNew10Real(seq)) > 0) {
                    StockMem[stkopt5_seq].y_close  = price_y;
                    StockMem[stkopt5_seq].up_bound = price_h;
                    StockMem[stkopt5_seq].dn_bound = price_l;
                    StockMem[stkopt5_seq].Repl_Mis1_Count = 0;
                }
            }
        }
        else {
            StockMem[seq].UpdateMis1Count++;
        }
    }
    else {
        if ( StockMem[seq].y_close  != price_y || StockMem[seq].up_bound != price_h || StockMem[seq].dn_bound != price_l ) {
            if (StockMem[seq].Repl_Mis1_Count > 1) {
                StockMem[seq].y_close  = price_y;
                StockMem[seq].up_bound = price_h;
                StockMem[seq].dn_bound = price_l;
                StockMem[seq].Repl_Mis1_Count = 0;
                MemTransferToNewMis1BinFmtAndSend( seq );
                if ( (stkopt5_seq = CopyStkOptNew10Real(seq)) > 0) {
                    StockMem[stkopt5_seq].y_close  = price_y;
                    StockMem[stkopt5_seq].up_bound = price_h;
                    StockMem[stkopt5_seq].dn_bound = price_l;
                    StockMem[stkopt5_seq].Repl_Mis1_Count = 0;
                    MemTransferToNewMis1BinFmtAndSend( stkopt5_seq );
                }
            }
            else {
                StockMem[seq].Repl_Mis1_Count++;
            }
        }
    }
    if ( CommendTime < 900 ) {                  // before 9:00
        MemTransferToNewMis1BinFmtAndSend( seq );
        if( (stkopt5_seq = CopyStkOptNew10Real(seq)) > 0) {
            MemTransferToNewMis1BinFmtAndSend( stkopt5_seq );
        }
    }
}

void WriteCloseYes(void)
{
   int  fptr;
   FILE *flog;
   int i;
   long yday, up, down, tmp;

   fptr = open("tsec_cls.yes",O_CREAT| O_WRONLY | O_BINARY, S_IWRITE);
   write(fptr, &tsec_class_total, sizeof(int));
   write(fptr, &TsecClassIndex, INDEX_FSIZE * tsec_class_total);
   close(fptr);

   fptr = open("otc_cls.yes",O_CREAT| O_WRONLY | O_BINARY, S_IWRITE);
   write(fptr, &otc_class_total, sizeof(int));
   write(fptr, &OtcClassIndex, INDEX_FSIZE * otc_class_total);
   close(fptr);
}

void CheckMarketClose(struct MARKET_TIME *markTime)
{
    switch( markTime->close_trade) {
        case 0:
            if(markTime->fg_Mis2Close && markTime->fg_Mis4Close && (markTime->Mis3.idx_time  == 9999)) {
                markTime->close_trade = 1;
                if((TsecTime.close_trade == 1) && (OtcTime.close_trade == 1))
                    WriteCloseYes();
                    Write_TSEC_Yes_Close("cycle\\main_yes.dat");    //<-- probably a error, as not enclosed by if above
            }
            break;
        case 1:
            if((markTime->Mis2_7.idx_time == 9999) && (markTime->Mis4_8.idx_time == 9999) && ( !fg_Odd || markTime->fg_Mis13Close)) {
                markTime->close_trade = 2;
                markTime->IndexTime = 9999;
            }
            break;
        }
}

void CheckMarketClose_15(struct MARKET_TIME_15 *markTime)
{
    switch( markTime->close_trade) {
        case 0:
            if(markTime->fg_Mis2Close && markTime->fg_Mis4Close && (markTime->Mis3.idx_time  == 999999)) {
                markTime->close_trade = 1;
                if((TsecTime_15.close_trade == 1) && (OtcTime_15.close_trade == 1))
                    WriteCloseYes();
                    Write_TSEC_Yes_Close("cycle\\main_yes.dat"); //<-- probably a error, as not enclosed by if above
            }
            break;
        case 1:
            if((markTime->Mis2_7.idx_time == 999999) && (markTime->Mis4_8.idx_time == 999999) && ( !fg_Odd || markTime->fg_Mis13Close)) {
                    markTime->close_trade = 2;
                    markTime->IndexTime = 999999;
            }
            break;
        }
}

void CV2_MisTotalAmountSheetCount_15(const IP_FMT& prot, int fg_fixed_price_trade, int market)
{
    int   i;
    int    class_total;
    int    w_time;
    long   tmpLong;
    long   MisTime;
    struct MARKET_TIME_15 *markTime;
    struct MARKET_TIME_5 *markTime5;
    struct mem_9995 *closemem9995, *close2mem9995ptr, *mem9995;
    int    *MarketRealClassShareTime, pre_fg;
    int    offset_length;
    char   CheckSum;
    FILE   *mf4_rec;
    static int pmap[2]={0, 0};
    static int amap[2]={0, 0};

    if(market == MK_TSEC) {
        closemem9995 = &TsecClose9995;
        close2mem9995ptr = &close2mem9995;
        mem9995 = &Tsec9995;
        markTime5 = &TsecTime_5;
        markTime = &TsecTime_15;
        class_total = tsec_class_total;
        MarketRealClassShareTime =  &TsecRealClassShareTime;
    }
    else if(market == MK_OTC) {
        closemem9995 = &OtcClose9995;
        close2mem9995ptr = &Otc_close2mem9995;
        mem9995 = &Otc9995;
        markTime5 = &OtcTime_5;
        markTime = &OtcTime_15;
        class_total = otc_class_total;
        MarketRealClassShareTime =  &OtcRealClassShareTime;
    }
    else {
        return;
    }
    markTime5->IndexTime = CutMrkTestTime(BCD_to_Long( prot.mis2_v2.time, TIME_FSIZE), MK_TSEC);  // get time
    markTime->IndexTime = markTime5->IndexTime;
    if (market ==MK_TSEC) {
        mk_Tsec_Mis4_8_time = markTime->IndexTime;
    }
    else {
        mk_Otc_Mis4_8_time = markTime->IndexTime;
    }
    if ( fg_fixed_price_trade) {
        tmpLong = closemem9995->deal_amount + BCD_to_Long(prot.mis2_v2.deal_amount, 5);
        if (tmpLong > 429496) {
            tmpLong = mem9995->deal_amount;
        }
        if (tmpLong >= mem9995->deal_amount) {
            mem9995->deal_amount = tmpLong;
        }
        tmpLong = closemem9995->deal_sheet + BCD_to_Long(prot.mis2_v2.deal_sheet, LONG_SHEET_FSIZE);
        if (tmpLong >= mem9995->deal_sheet) {
            mem9995->deal_sheet = tmpLong;
        }
        tmpLong = closemem9995->deal_count + BCD_to_Long(prot.mis2_v2.deal_count, LONG_COUNT_FSIZE);

        if (tmpLong >= mem9995->deal_count) {
            mem9995->deal_count = tmpLong;
        }
        memcpy(close2mem9995ptr, mem9995, sizeof(struct mem_9995));

//定盤總成交張筆值
        if(!pmap[market -1]) {
            if ((mf4_rec=_fsopen(((market == MK_TSEC)?mf4_file:mf3_file),"rt+",SH_DENYNONE)) != NULL)  {
                fseek(mf4_rec,-1L,SEEK_END);
                fprintf(mf4_rec,"\n總成交%8lu百萬 %8lu張 %8lu筆\n\x1a"
                    ,mem9995->deal_amount, mem9995->deal_sheet, mem9995->deal_count);
                fclose(mf4_rec);
                if(market == MK_TSEC)
                    tmp_copy(tsedir,tsefile,mf4_file);
                else
                    tmp_copy(otcdir,otcfile,mf3_file);
                pmap[market -1] = 1;
            }
        }
// save to afternoon backup file
        if ((mf4_rec=fopen("aft_noon.sav","wt")) != NULL)  {
            fprintf(mf4_rec,"\n總成交%8lu百萬 %8lu張 %8lu筆\n\x1a",mem9995->deal_amount, mem9995->deal_sheet, mem9995->deal_count);
            fclose(mf4_rec);
        }
    }
    else {
        tmpLong = BCD_to_Long(prot.mis2_v2.deal_amount, 5);
        if (tmpLong > 429496) {
            tmpLong = mem9995->deal_amount;
        }
        if (tmpLong >= mem9995->deal_amount) {
            mem9995->deal_amount = tmpLong;
        }
        tmpLong = BCD_to_Long(prot.mis2_v2.deal_sheet, LONG_SHEET_FSIZE);
        if (tmpLong >= mem9995->deal_sheet) {
            mem9995->deal_sheet = tmpLong;
        }
        tmpLong = BCD_to_Long(prot.mis2_v2.deal_count, LONG_COUNT_FSIZE);
        if (tmpLong >= mem9995->deal_count) {
            mem9995->deal_count = tmpLong;
        }
        tmpLong = BCD_to_Long(prot.mis2_v2.fund_deal_amount, 5);
        if(tmpLong >= mem9995->fund_vol)
            mem9995->fund_vol = tmpLong;
        tmpLong = BCD_to_Long(prot.mis2_v2.fund_deal_sheet, LONG_SHEET_FSIZE);
        if(tmpLong >= mem9995->fund_sheet)
            mem9995->fund_sheet = tmpLong;
        tmpLong = BCD_to_Long(prot.mis2_v2.fund_deal_count, LONG_COUNT_FSIZE);
        if(tmpLong >= mem9995->fund_count)
            mem9995->fund_count = tmpLong;

        tmpLong = BCD_to_Long(prot.mis2_v2.stk_deal_amount, 5);
        if(tmpLong >= mem9995->stk_vol)
            mem9995->stk_vol = tmpLong;
        tmpLong = BCD_to_Long(prot.mis2_v2.stk_deal_sheet, LONG_SHEET_FSIZE);
        if(tmpLong >= mem9995->stk_sheet)
            mem9995->stk_sheet = tmpLong;
        tmpLong = BCD_to_Long(prot.mis2_v2.stk_deal_count, LONG_COUNT_FSIZE);
        if(tmpLong >= mem9995->stk_count)
            mem9995->stk_count = tmpLong;
        tmpLong = BCD_to_Long(prot.mis2_v2.warrb_deal_amount, 5);
        if(tmpLong >= mem9995->warrb_vol)
            mem9995->warrb_vol = tmpLong;
        tmpLong = BCD_to_Long(prot.mis2_v2.warrb_deal_sheet, LONG_SHEET_FSIZE);
        if(tmpLong >= mem9995->warrb_sheet)
            mem9995->warrb_sheet = tmpLong;
        tmpLong = BCD_to_Long(prot.mis2_v2.warrb_deal_count, LONG_COUNT_FSIZE);
        if(tmpLong >= mem9995->warrb_count)
            mem9995->warrb_count = tmpLong;
        tmpLong = BCD_to_Long(prot.mis2_v2.warrs_deal_amount, 5);
        if(tmpLong >= mem9995->warrs_vol)
            mem9995->warrs_vol = tmpLong;
        tmpLong = BCD_to_Long(prot.mis2_v2.warrs_deal_sheet, LONG_SHEET_FSIZE);
        if(tmpLong >= mem9995->warrs_sheet)
            mem9995->warrs_sheet = tmpLong;
        tmpLong = BCD_to_Long(prot.mis2_v2.warrs_deal_count, LONG_COUNT_FSIZE);
        if(tmpLong >= mem9995->warrs_count)
            mem9995->warrs_count = tmpLong;            

        if ( markTime->IndexTime == 999999) {
            memcpy(&closemem9995->deal_amount, &mem9995->deal_amount, 60);
            markTime->IndexTime = last_sec15_time;
            markTime->fg_Mis2Close = 1;
            if (!amap[market -1]) {
                if ((mf4_rec=_fsopen(((market == MK_TSEC)?mf4_file:mf3_file),"rt+",SH_DENYNONE))!= NULL)  {
                    /* find line 4 */
                    fseek(mf4_rec,0L,SEEK_SET);
                    for (i=0; i <4;i++) {
                        while(fgetc(mf4_rec)!='\n');
                    }
                    fseek(mf4_rec,0L,SEEK_CUR);
                    fprintf(mf4_rec,"上午總成交 %8lu百萬 %8lu張 %8lu筆",closemem9995->deal_amount, closemem9995->deal_sheet, closemem9995->deal_count);
                    fclose(mf4_rec);
                    if(market == MK_TSEC) {
                        tmp_copy(tsedir,tsefile,mf4_file);
                    }
                    else {
                        tmp_copy(otcdir,otcfile,mf3_file);
                    }
                    amap[market -1]=1;
                }              
            }
        }
    }
    TimeTo5SecPtr(markTime5->IndexTime, &(markTime5->Mis2_7));
    TimeTo15SecPtr(markTime->IndexTime, &(markTime->Mis2_7));
    CheckMarketClose_15(markTime);
   /* v6.7.00, check if need to add data of close 1 */
    if (markTime5->Mis2_7.idx_time > last_sec5_time) {  /* correct time&time ptr */
        markTime5->Mis2_7.time_ptr = max_sec5_ptr;
        if (markTime5->Mis2_7.idx_time < 999999 || !FixedPriceTrade[ market-1 ].Ok) {
            markTime5->Mis2_7.idx_time = max_sec5_ptr;
        }
    }
    if (markTime->Mis2_7.idx_time > last_sec15_time) {  /* correct time&time ptr */
        markTime->Mis2_7.time_ptr = max_sec15_ptr;
        if (markTime->Mis2_7.idx_time < 999999 || !FixedPriceTrade[ market-1 ].Ok) {
            markTime->Mis2_7.idx_time = max_sec15_ptr;
        }
    }
//5sec
    BINFMT bp;
    if (markTime5->Mis2_7.idx_time >= 90000) {  // after 9:00 send out 'w'
        memset(bp.buf, 0, sizeof(bp.buf));
        bp.i_cs_inx2.esc = ESC;
        bp.i_cs_inx2.mis = 0xe2;
        bp.i_cs_inx2.mkt = market;
        bp.i_cs_inx2.cnt = class_total;
        memcpy(&(bp.i_cs_inx2.ptr), &(markTime5->Mis2_7.time_ptr), 6);
        CheckSum=0;
        for ( i=0 ; i< BIN_IP_M_CLS_INX2_SIZE -1  ; i++ ) {
            CheckSum ^= bp.buf[i];
        }
        bp.buf[BIN_IP_M_CLS_INX2_SIZE-1] = CheckSum;
        if (markTime5->Mis2_7.idx_time == 90000) {
            offset_length = class_total * sizeof(long)*2 + sizeof(long) + 1;
            memset( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], 0x00, offset_length);
            CheckSum=0;
            for( i=0 ; i< offset_length -1  ; i++ ) {
                CheckSum ^= bp.buf[i + BIN_IP_M_CLS_INX2_SIZE];
            }
            bp.buf[BIN_IP_M_CLS_INX2_SIZE + offset_length -1] = CheckSum;
            CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_CLS_INX2_SIZE + offset_length, 0);
            return;
        }
        memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], &mem9995->deal_count, sizeof(long));

        if (*MarketRealClassShareTime != markTime5->Mis2_7.idx_time) {
            *MarketRealClassShareTime = markTime5->Mis2_7.idx_time;
            pre_fg = 0;
        }
        else if(fg_fixed_price_trade) {
            pre_fg = 0;
        }
        else {
            pre_fg = 1;
        }
        MakeRealClassSharesValue(market, pre_fg, &bp.buf[BIN_IP_M_CLS_INX2_SIZE+sizeof(long)], class_total);
        offset_length = class_total * sizeof(long)*2 + sizeof(long) + 1;
        CheckSum=0;
        for ( i=0 ; i< offset_length -1  ; i++ ) {
            CheckSum ^= bp.buf[i + BIN_IP_M_CLS_INX2_SIZE];
        }
        bp.buf[BIN_IP_M_CLS_INX2_SIZE + offset_length -1] = CheckSum;
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_CLS_INX2_SIZE + offset_length, 0);

        bp.i_mis2_deal.esc = ESC;
        bp.i_mis2_deal.mis = 0xe3;
        bp.i_mis2_deal.mkt = market;
        memcpy(&(bp.i_mis2_deal.time_ptr), &(markTime5->Mis2_7.time_ptr), 6);
        bp.i_mis2_deal.fund_vol = mem9995->fund_vol;
        bp.i_mis2_deal.fund_sheet = mem9995->fund_sheet;
        bp.i_mis2_deal.fund_count = mem9995->fund_count;
        bp.i_mis2_deal.stk_vol = mem9995->stk_vol;
        bp.i_mis2_deal.stk_sheet = mem9995->stk_sheet;
        bp.i_mis2_deal.stk_count = mem9995->stk_count;
        bp.i_mis2_deal.warrb_vol = mem9995->warrb_vol;
        bp.i_mis2_deal.warrb_sheet = mem9995->warrb_sheet;
        bp.i_mis2_deal.warrb_count = mem9995->warrb_count;
        bp.i_mis2_deal.warrs_vol = mem9995->warrs_vol;
        bp.i_mis2_deal.warrs_sheet = mem9995->warrs_sheet;
        bp.i_mis2_deal.warrs_count = mem9995->warrs_count;
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_MIS2_DEAL_SIZE - 1 );
    }
//15 sec

    if (markTime->Mis2_7.idx_time >= 90000) {  // after 9:00 send out 'w'
        memset(bp.buf, 0, sizeof(bp.buf));
        bp.i_cs_inx2.esc = ESC;
        bp.i_cs_inx2.mis = 0x74;
        bp.i_cs_inx2.mkt = market;
        bp.i_cs_inx2.cnt = class_total;
        memcpy(&(bp.i_cs_inx2.ptr), &(markTime->Mis2_7.time_ptr), 6);
        CheckSum=0;
        for ( i=0 ; i< BIN_IP_M_CLS_INX2_SIZE -1  ; i++ )
            CheckSum ^= bp.buf[i];
        bp.buf[BIN_IP_M_CLS_INX2_SIZE-1] = CheckSum;
        if (markTime->Mis2_7.idx_time == 90000) {
            offset_length = class_total * sizeof(long)*2 + sizeof(long) + 1;
            memset( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], 0x00, offset_length);
            CheckSum=0;
            for( i=0 ; i< offset_length -1  ; i++ )
                CheckSum ^= bp.buf[i + BIN_IP_M_CLS_INX2_SIZE];
            bp.buf[BIN_IP_M_CLS_INX2_SIZE + offset_length -1] = CheckSum;
            CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_CLS_INX2_SIZE + offset_length, 0);
            return;
        }
        memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], &mem9995->deal_count, sizeof(long));

        if (*MarketRealClassShareTime != markTime->Mis2_7.idx_time) {
            *MarketRealClassShareTime = markTime->Mis2_7.idx_time;
            pre_fg = 0;
        }
        else if(fg_fixed_price_trade) {
            pre_fg = 0;
        }
        else {
            pre_fg = 1;
        }
        MakeRealClassSharesValue(market, pre_fg, &bp.buf[BIN_IP_M_CLS_INX2_SIZE+sizeof(long)], class_total);
        offset_length = class_total * sizeof(long)*2 + sizeof(long) + 1;
        CheckSum=0;
        for( i=0 ; i< offset_length -1  ; i++ ) {
            CheckSum ^= bp.buf[i + BIN_IP_M_CLS_INX2_SIZE];
        }
        bp.buf[BIN_IP_M_CLS_INX2_SIZE + offset_length -1] = CheckSum;
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_CLS_INX2_SIZE + offset_length, 0);

        bp.i_mis2_deal.esc = ESC;
        bp.i_mis2_deal.mis = 0x76;
        bp.i_mis2_deal.mkt = market;
        memcpy(&(bp.i_mis2_deal.time_ptr), &(markTime->Mis2_7.time_ptr), 6);
        bp.i_mis2_deal.fund_vol = mem9995->fund_vol;
        bp.i_mis2_deal.fund_sheet = mem9995->fund_sheet;
        bp.i_mis2_deal.fund_count = mem9995->fund_count;
        bp.i_mis2_deal.stk_vol = mem9995->stk_vol;
        bp.i_mis2_deal.stk_sheet = mem9995->stk_sheet;
        bp.i_mis2_deal.stk_count = mem9995->stk_count;
        bp.i_mis2_deal.warrb_vol = mem9995->warrb_vol;
        bp.i_mis2_deal.warrb_sheet = mem9995->warrb_sheet;
        bp.i_mis2_deal.warrb_count = mem9995->warrb_count;
        bp.i_mis2_deal.warrs_vol = mem9995->warrs_vol;
        bp.i_mis2_deal.warrs_sheet = mem9995->warrs_sheet;
        bp.i_mis2_deal.warrs_count = mem9995->warrs_count;
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_MIS2_DEAL_SIZE - 1 );

        if (market == MK_TSEC) {
            send_15_sec_index(2);
        }
        else if(market == MK_OTC) {
            send_otc_15sec_index(2, 0);
        }
        if (markTime->IndexTime == 999999) {
            if ( !fg_fixed_price_trade) {
                SendMktStatus(market, 0x02, markTime->Mis2_7.idx_time/100);
            }
            else if( FixedPriceTrade[ market-1 ].Ok) {
                SendMktStatus(market, 0x04, markTime->Mis2_7.idx_time/100);
            }
        }
    }
}

int CV2_TsecMis4_15(const IP_FMT& prot, int fg_fixed_price_trade, int market)
{
    long temp;
    int  i;
    long tmp_time;
    char show_str[64];
    struct mem_99961 *mark99961;
    struct mem_99962 *mark99962;
    struct mem_99961 *closemark99961;
    struct mem_99962 *closemark99962;
    struct MARKET_TIME_15 *markTime;
    struct MARKET_TIME_5 *markTime5;
    struct IP_MIS4_INFO *ClsMis4Inf, *Mis4Inf;
    FILE   *mf4_rec;

    if (market ==MK_TSEC) {
        mark99961 = &Tsec99961;
        mark99962 = &Tsec99962;
        closemark99961 = &CloseTsec99961;
        closemark99962 = &CloseTsec99962;
        markTime5 = &TsecTime_5;
        markTime = &TsecTime_15;
        ClsMis4Inf = &ClsTsecMis4Inf;
        Mis4Inf = &TsecMis4Inf;
    }
    else if(market ==MK_OTC) {
        mark99961 = &Otc99961;
        closemark99961 = &CloseOtc99961;
        markTime5 = &OtcTime_5;
        markTime = &OtcTime_15;
        ClsMis4Inf = &ClsOtcMis4Inf;
        Mis4Inf = &OtcMis4Inf;
    }
    else {
        return 0;
    }
    markTime5->IndexTime = CutMrkTestTime(BCD_to_Long( prot.mis4_v2.time, TIME_FSIZE), MK_TSEC);  //  time get
    markTime->IndexTime = markTime5->IndexTime;
    if ( !fg_fixed_price_trade && (markTime->IndexTime == 999999)) {
        memcpy(&ClsMis4Inf->esc, &Mis4Inf->esc, sizeof(struct IP_MIS4_INFO));
        markTime->IndexTime = last_sec15_time;
        markTime->fg_Mis4Close = 1;
        markTime->IndexTime = 133100;
    }
    TimeTo5SecPtr(markTime5->IndexTime, &(markTime5->Mis4_8));
    TimeTo15SecPtr(markTime->IndexTime, &(markTime->Mis4_8));
    CheckMarketClose_15(markTime);
    mark99961->time_ptr=markTime->Mis4_8.time_ptr;
       // v6.7.00, check if need to add data of close 1
    if ( fg_fixed_price_trade) {  //fixed price trade
        mark99961->buy_count  = ClsMis4Inf->buy_count + BCD_to_Long( prot.mis4_v2.buy_count, COUNT_FSIZE);
        mark99961->sell_count = ClsMis4Inf->sell_count + BCD_to_Long( prot.mis4_v2.sell_count, COUNT_FSIZE);
        mark99961->buy_sheet  = ClsMis4Inf->buy_sheet + BCD_to_Long( prot.mis4_v2.buy_sheet , SHEET_FSIZE);
        mark99961->sell_sheet = ClsMis4Inf->sell_sheet + BCD_to_Long( prot.mis4_v2.sell_sheet, SHEET_FSIZE);

        if(markTime->IndexTime != 999999) {
          if ((mf4_rec=_fsopen(((market == MK_TSEC)?mf4_file:mf3_file),"rt+",SH_DENYNONE)) != NULL)  {
            fseek(mf4_rec,-1L,SEEK_END);   // to the beginning of file.
            fprintf(mf4_rec,"%02d:%02d   %10lu  %10lu  %10lu  %10lu\n\x1a"
                ,markTime->Mis4_8.idx_time/10000, (markTime->Mis4_8.idx_time%10000)/100, mark99961->buy_sheet, mark99961->buy_count,  mark99961->sell_sheet, mark99961->sell_count);
            fseek(mf4_rec,0L,SEEK_SET); // to the beginning of file.
            fprintf(mf4_rec,"■  %02d:%02d",markTime->Mis4_8.idx_time/10000, (markTime->Mis4_8.idx_time%10000)/100);
            fseek(mf4_rec,10L,SEEK_SET); // to the beginning of file.
            fprintf(mf4_rec,"%s定價買%8lu張%8lu筆 賣%8lu張%8lu筆",((market == MK_TSEC)?"市":"櫃")
                ,mark99961->buy_sheet, mark99961->buy_count,  mark99961->sell_sheet, mark99961->sell_count);
            fclose(mf4_rec);
            if(market == MK_TSEC)
                tmp_copy(tsedir,tsefile,mf4_file);
            else
                tmp_copy(otcdir,otcfile,mf3_file);

          }
        }
        if(markTime->IndexTime == 999999) {
            return 1;
        }
    }
    else {
        mark99961->buy_count  = BCD_to_Long( prot.mis4_v2.buy_count , COUNT_FSIZE);
        mark99961->sell_count = BCD_to_Long( prot.mis4_v2.sell_count, COUNT_FSIZE);
        mark99961->buy_sheet  = BCD_to_Long( prot.mis4_v2.buy_sheet , SHEET_FSIZE);
        mark99961->sell_sheet = BCD_to_Long( prot.mis4_v2.sell_sheet, SHEET_FSIZE);
    }
    if ( fg_fixed_price_trade ) {  // fixed price trade
        Mis4Inf->buy_count  = ClsMis4Inf->buy_count + BCD_to_Long( prot.tsec_mis4.buy_count, COUNT_FSIZE);
        Mis4Inf->sell_count = ClsMis4Inf->sell_count + BCD_to_Long( prot.tsec_mis4.sell_count, COUNT_FSIZE);
        Mis4Inf->buy_sheet  = ClsMis4Inf->buy_sheet + BCD_to_Long( prot.tsec_mis4.buy_sheet , SHEET_FSIZE);
        Mis4Inf->sell_sheet = ClsMis4Inf->sell_sheet + BCD_to_Long( prot.tsec_mis4.sell_sheet, SHEET_FSIZE);
        if(market ==MK_TSEC) {
            Mis4Inf->fund_buy_count = ClsMis4Inf->fund_buy_count + BCD_to_Long( prot.tsec_mis4.fund_buy_count , COUNT_FSIZE);
            Mis4Inf->fund_sell_count= ClsMis4Inf->fund_sell_count + BCD_to_Long( prot.tsec_mis4.fund_sell_count , COUNT_FSIZE);
            Mis4Inf->fund_buy_sheet = ClsMis4Inf->fund_buy_sheet + BCD_to_Long( prot.tsec_mis4.fund_buy_sheet , SHEET_FSIZE);
            Mis4Inf->fund_sell_sheet= ClsMis4Inf->fund_sell_sheet + BCD_to_Long( prot.tsec_mis4.fund_sell_sheet , SHEET_FSIZE);
            Mis4Inf->up_buy_count   = ClsMis4Inf->up_buy_count + BCD_to_Long( prot.tsec_mis4.up_buy_count , COUNT_FSIZE);
            Mis4Inf->up_sell_count  = ClsMis4Inf->up_sell_count + BCD_to_Long( prot.tsec_mis4.up_sell_count , COUNT_FSIZE);
            Mis4Inf->up_buy_sheet   = ClsMis4Inf->up_buy_sheet + BCD_to_Long( prot.tsec_mis4.up_buy_sheet , SHEET_FSIZE);
            Mis4Inf->up_sell_sheet  = ClsMis4Inf->up_sell_sheet + BCD_to_Long( prot.tsec_mis4.up_sell_sheet , SHEET_FSIZE);
            Mis4Inf->down_buy_count = ClsMis4Inf->down_buy_count + BCD_to_Long( prot.tsec_mis4.down_buy_count , COUNT_FSIZE);
            Mis4Inf->down_sell_count= ClsMis4Inf->down_sell_count + BCD_to_Long( prot.tsec_mis4.down_sell_count , COUNT_FSIZE);
            Mis4Inf->down_buy_sheet = ClsMis4Inf->down_buy_sheet + BCD_to_Long( prot.tsec_mis4.down_buy_sheet , SHEET_FSIZE);
            Mis4Inf->down_sell_sheet= ClsMis4Inf->down_sell_sheet + BCD_to_Long( prot.tsec_mis4.down_sell_sheet , SHEET_FSIZE);
            Mis4Inf->up_fund_buy_count   = ClsMis4Inf->up_fund_buy_count + BCD_to_Long( prot.tsec_mis4.up_fund_buy_count , COUNT_FSIZE);
            Mis4Inf->up_fund_sell_count  = ClsMis4Inf->up_fund_sell_count + BCD_to_Long( prot.tsec_mis4.up_fund_sell_count , COUNT_FSIZE);
            Mis4Inf->up_fund_buy_sheet   = ClsMis4Inf->up_fund_buy_sheet + BCD_to_Long( prot.tsec_mis4.up_fund_buy_sheet , SHEET_FSIZE);
            Mis4Inf->up_fund_sell_sheet  = ClsMis4Inf->up_fund_sell_sheet + BCD_to_Long( prot.tsec_mis4.up_fund_sell_sheet , SHEET_FSIZE);
            Mis4Inf->down_fund_buy_count = ClsMis4Inf->down_fund_buy_count + BCD_to_Long( prot.tsec_mis4.down_fund_buy_count , COUNT_FSIZE);
            Mis4Inf->down_fund_sell_count= ClsMis4Inf->down_fund_sell_count + BCD_to_Long( prot.tsec_mis4.down_fund_sell_count , COUNT_FSIZE);
            Mis4Inf->down_fund_buy_sheet = ClsMis4Inf->down_fund_buy_sheet + BCD_to_Long( prot.tsec_mis4.down_fund_buy_sheet , SHEET_FSIZE);
            Mis4Inf->down_fund_sell_sheet= ClsMis4Inf->down_fund_sell_sheet + BCD_to_Long( prot.tsec_mis4.down_fund_sell_sheet , SHEET_FSIZE);
        }
    }
    else {
        Mis4Inf->buy_count  = BCD_to_Long( prot.mis4_v2.buy_count , COUNT_FSIZE);
        Mis4Inf->sell_count = BCD_to_Long( prot.mis4_v2.sell_count, COUNT_FSIZE);
        Mis4Inf->buy_sheet  = BCD_to_Long( prot.mis4_v2.buy_sheet , SHEET_FSIZE);
        Mis4Inf->sell_sheet = BCD_to_Long( prot.mis4_v2.sell_sheet, SHEET_FSIZE);
        Mis4Inf->fund_buy_count = BCD_to_Long( prot.mis4_v2.fund_buy_count , COUNT_FSIZE);
        Mis4Inf->fund_sell_count= BCD_to_Long( prot.mis4_v2.fund_sell_count , COUNT_FSIZE);
        Mis4Inf->fund_buy_sheet = BCD_to_Long( prot.mis4_v2.fund_buy_sheet , SHEET_FSIZE);
        Mis4Inf->fund_sell_sheet= BCD_to_Long( prot.mis4_v2.fund_sell_sheet , SHEET_FSIZE);
        Mis4Inf->stk_buy_count  = BCD_to_Long( prot.mis4_v2.stk_buy_count , COUNT_FSIZE);
        Mis4Inf->stk_sell_count = BCD_to_Long( prot.mis4_v2.stk_sell_count, COUNT_FSIZE);
        Mis4Inf->stk_buy_sheet  = BCD_to_Long( prot.mis4_v2.stk_buy_sheet , SHEET_FSIZE);
        Mis4Inf->stk_sell_sheet = BCD_to_Long( prot.mis4_v2.stk_sell_sheet, SHEET_FSIZE);
        Mis4Inf->warrb_buy_count  = BCD_to_Long( prot.mis4_v2.warrb_buy_count , COUNT_FSIZE);
        Mis4Inf->warrb_sell_count = BCD_to_Long( prot.mis4_v2.warrb_sell_count, COUNT_FSIZE);
        Mis4Inf->warrb_buy_sheet  = BCD_to_Long( prot.mis4_v2.warrb_buy_sheet , SHEET_FSIZE);
        Mis4Inf->warrb_sell_sheet = BCD_to_Long( prot.mis4_v2.warrb_sell_sheet, SHEET_FSIZE);
        Mis4Inf->warrs_buy_count  = BCD_to_Long( prot.mis4_v2.warrs_buy_count , COUNT_FSIZE);
        Mis4Inf->warrs_sell_count = BCD_to_Long( prot.mis4_v2.warrs_sell_count, COUNT_FSIZE);
        Mis4Inf->warrs_buy_sheet  = BCD_to_Long( prot.mis4_v2.warrs_buy_sheet , SHEET_FSIZE);
        Mis4Inf->warrs_sell_sheet = BCD_to_Long( prot.mis4_v2.warrs_sell_sheet, SHEET_FSIZE);

        Mis4Inf->up_buy_count   = BCD_to_Long( prot.mis4_v2.up_buy_count , COUNT_FSIZE);
        Mis4Inf->up_sell_count  = BCD_to_Long( prot.mis4_v2.up_sell_count , COUNT_FSIZE);
        Mis4Inf->up_buy_sheet   = BCD_to_Long( prot.mis4_v2.up_buy_sheet , SHEET_FSIZE);
        Mis4Inf->up_sell_sheet  = BCD_to_Long( prot.mis4_v2.up_sell_sheet , SHEET_FSIZE);
        Mis4Inf->down_buy_count = BCD_to_Long( prot.mis4_v2.down_buy_count , COUNT_FSIZE);
        Mis4Inf->down_sell_count= BCD_to_Long( prot.mis4_v2.down_sell_count , COUNT_FSIZE);
        Mis4Inf->down_buy_sheet = BCD_to_Long( prot.mis4_v2.down_buy_sheet , SHEET_FSIZE);
        Mis4Inf->down_sell_sheet= BCD_to_Long( prot.mis4_v2.down_sell_sheet , SHEET_FSIZE);
        Mis4Inf->up_fund_buy_count   = BCD_to_Long( prot.mis4_v2.up_fund_buy_count , COUNT_FSIZE);
        Mis4Inf->up_fund_sell_count  = BCD_to_Long( prot.mis4_v2.up_fund_sell_count , COUNT_FSIZE);
        Mis4Inf->up_fund_buy_sheet   = BCD_to_Long( prot.mis4_v2.up_fund_buy_sheet , SHEET_FSIZE);
        Mis4Inf->up_fund_sell_sheet  = BCD_to_Long( prot.mis4_v2.up_fund_sell_sheet , SHEET_FSIZE);
        Mis4Inf->down_fund_buy_count = BCD_to_Long( prot.mis4_v2.down_fund_buy_count , COUNT_FSIZE);
        Mis4Inf->down_fund_sell_count= BCD_to_Long( prot.mis4_v2.down_fund_sell_count , COUNT_FSIZE);
        Mis4Inf->down_fund_buy_sheet = BCD_to_Long( prot.mis4_v2.down_fund_buy_sheet , SHEET_FSIZE);
        Mis4Inf->down_fund_sell_sheet= BCD_to_Long( prot.mis4_v2.down_fund_sell_sheet , SHEET_FSIZE);
        Mis4Inf->up_stk_buy_count   = BCD_to_Long( prot.mis4_v2.up_stk_buy_count , COUNT_FSIZE);
        Mis4Inf->up_stk_sell_count  = BCD_to_Long( prot.mis4_v2.up_stk_sell_count , COUNT_FSIZE);
        Mis4Inf->up_stk_buy_sheet   = BCD_to_Long( prot.mis4_v2.up_stk_buy_sheet , SHEET_FSIZE);
        Mis4Inf->up_stk_sell_sheet  = BCD_to_Long( prot.mis4_v2.up_stk_sell_sheet , SHEET_FSIZE);
        Mis4Inf->down_stk_buy_count = BCD_to_Long( prot.mis4_v2.down_stk_buy_count , COUNT_FSIZE);
        Mis4Inf->down_stk_sell_count= BCD_to_Long( prot.mis4_v2.down_stk_sell_count , COUNT_FSIZE);
        Mis4Inf->down_stk_buy_sheet = BCD_to_Long( prot.mis4_v2.down_stk_buy_sheet , SHEET_FSIZE);
        Mis4Inf->down_stk_sell_sheet= BCD_to_Long( prot.mis4_v2.down_stk_sell_sheet , SHEET_FSIZE);

        Mis4Inf->up_warrb_buy_count   = BCD_to_Long( prot.mis4_v2.up_warrb_buy_count , COUNT_FSIZE);
        Mis4Inf->up_warrb_sell_count  = BCD_to_Long( prot.mis4_v2.up_warrb_sell_count , COUNT_FSIZE);
        Mis4Inf->up_warrb_buy_sheet   = BCD_to_Long( prot.mis4_v2.up_warrb_buy_sheet , SHEET_FSIZE);
        Mis4Inf->up_warrb_sell_sheet  = BCD_to_Long( prot.mis4_v2.up_warrb_sell_sheet , SHEET_FSIZE);
        Mis4Inf->down_warrb_buy_count = BCD_to_Long( prot.mis4_v2.down_warrb_buy_count , COUNT_FSIZE);
        Mis4Inf->down_warrb_sell_count= BCD_to_Long( prot.mis4_v2.down_warrb_sell_count , COUNT_FSIZE);
        Mis4Inf->down_warrb_buy_sheet = BCD_to_Long( prot.mis4_v2.down_warrb_buy_sheet , SHEET_FSIZE);
        Mis4Inf->down_warrb_sell_sheet= BCD_to_Long( prot.mis4_v2.down_warrb_sell_sheet , SHEET_FSIZE);

        Mis4Inf->up_warrs_buy_count   = BCD_to_Long( prot.mis4_v2.up_warrs_buy_count , COUNT_FSIZE);
        Mis4Inf->up_warrs_sell_count  = BCD_to_Long( prot.mis4_v2.up_warrs_sell_count , COUNT_FSIZE);
        Mis4Inf->up_warrs_buy_sheet   = BCD_to_Long( prot.mis4_v2.up_warrs_buy_sheet , SHEET_FSIZE);
        Mis4Inf->up_warrs_sell_sheet  = BCD_to_Long( prot.mis4_v2.up_warrs_sell_sheet , SHEET_FSIZE);
        Mis4Inf->down_warrs_buy_count = BCD_to_Long( prot.mis4_v2.down_warrs_buy_count , COUNT_FSIZE);
        Mis4Inf->down_warrs_sell_count= BCD_to_Long( prot.mis4_v2.down_warrs_sell_count , COUNT_FSIZE);
        Mis4Inf->down_warrs_buy_sheet = BCD_to_Long( prot.mis4_v2.down_warrs_buy_sheet , SHEET_FSIZE);
        Mis4Inf->down_warrs_sell_sheet= BCD_to_Long( prot.mis4_v2.down_warrs_sell_sheet , SHEET_FSIZE);
    }
    // 送出各類基金資料
//5sec
    BINFMT bp;
    memset(bp.buf, 0, sizeof(bp.buf));
    bp.i_mis4_info.esc = ESC;
    bp.i_mis4_info.mis = 0xe1;
    bp.i_mis4_info.mkt = market;
    memcpy(&(bp.i_mis4_info.time_ptr), &(markTime5->Mis4_8.time_ptr), 6);
    memcpy(&(bp.i_mis4_info.buy_count), &(Mis4Inf->buy_count), sizeof(struct IP_MIS4_INFO)-10);
    CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_MIS4_INFO_SIZE - 1 );
//15sec
    memset(bp.buf, 0, sizeof(bp.buf));
    bp.i_mis4_info.esc = ESC;
    bp.i_mis4_info.mis = 0x73;
    bp.i_mis4_info.mkt = market;
    memcpy(&(bp.i_mis4_info.time_ptr), &(markTime->Mis4_8.time_ptr), 6);
    memcpy(&(bp.i_mis4_info.buy_count), &(Mis4Inf->buy_count), sizeof(struct IP_MIS4_INFO)-10);
    CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_MIS4_INFO_SIZE - 1 );

    if (fg_fixed_price_trade) {
        if ((market ==MK_TSEC) && (tsecA0_last_len > BIN_IP_M_CLS_INX2_SIZE)){
            CalCheckSumAndSendToMoxaCard( tsecA0_last_buf, tsecA0_last_len, 0);
        }
        else if(otcA0_last_len > BIN_IP_M_CLS_INX2_SIZE){
            CalCheckSumAndSendToMoxaCard( otcA0_last_buf, otcA0_last_len, 0);
        }
    }
    return 1;
}

void MakeRealSecIndexOffset(int market)
{
    if(  !TsecPowerBase || !OtcPowerBase)  return;

    switch(market) {
        case MK_TSEC:
            if( !TsecClassYesIndex[TOTAL_INDEX])    return;

            lTsecIndexOffset = TsecClassYesIndex[TOTAL_INDEX] - ((long)(fTsecPrevIndex*100/TsecPowerBase));
            break;
        case MK_OTC:
            if( !OtcClassYesIndex[TOTAL_INDEX])    return;

            lOtcIndexOffset = OtcClassYesIndex[TOTAL_INDEX] - ((long)(fOtcPrevIndex*100/OtcPowerBase));
            break;
        }
}

void ReCoverMis3Data(int market)
{
    if(market == MK_TSEC) {
       //清除原綜合及工業指
        if(TsecTime_15.IndexTime < 90000) {
            TsecClassYesIndex[3] = TsecClassYesIndex[4] = 0;
        }
        else {
            TsecClassIndex[3] = TsecClassIndex[4] = 0;
        }
    }
    else {
        if(OtcTime_15.IndexTime < 90000)  {
            OtcClassYesIndex[2] = OtcClassYesIndex[13];
            OtcClassYesIndex[3] = OtcClassYesIndex[4];
            OtcClassYesIndex[4] = OtcClassYesIndex[5];
            OtcClassYesIndex[5] = OtcClassYesIndex[6];
            OtcClassYesIndex[6] = OtcClassYesIndex[15];
            OtcClassYesIndex[7] = OtcClassYesIndex[8];
            OtcClassYesIndex[8] = OtcClassYesIndex[1];
            OtcClassYesIndex[9] = OtcClassYesIndex[10];
            OtcClassYesIndex[10] = OtcClassYesIndex[11];
            OtcClassYesIndex[11] = OtcClassYesIndex[12];
            OtcClassYesIndex[1] = OtcClassYesIndex[12] = 0;
        }
        else {
            OtcClassIndex[2] = OtcClassIndex[13];
            OtcClassIndex[3] = OtcClassIndex[4];
            OtcClassIndex[4] = OtcClassIndex[5];
            OtcClassIndex[5] = OtcClassIndex[6];
            OtcClassIndex[6] = OtcClassIndex[15];
            OtcClassIndex[7] = OtcClassIndex[8];
            OtcClassIndex[8] = OtcClassIndex[1];
            OtcClassIndex[9] = OtcClassIndex[10];
            OtcClassIndex[10] = OtcClassIndex[11];
            OtcClassIndex[11] = OtcClassIndex[12];
            OtcClassIndex[1] = OtcClassIndex[12] = 0;
        }
    }
}

struct MonitorLog {
	SYSTEMTIME localt;
	int feedt;
	int index;
	int difft;
	int startDiff;
};

void write_monitor_file( const IP_FMT& prot ) {
	static FILE * monitorfh = NULL;
    static MonitorLog monitorLog;
	GetLocalTime( &monitorLog.localt );
	int feedhhmmss = BCD_to_Long(prot.mis3_head.time, TIME_FSIZE);
    monitorLog.feedt = feedhhmmss/10000*3600000+((feedhhmmss%10000)/100)*60000+(feedhhmmss%100)*1000;
    if (monitorLog.feedt==0) {
        return;
    }
	monitorLog.index = BCD_to_Long(prot.mis3_head.index, INDEX_FSIZE);
    unsigned long localTick = monitorLog.localt.wHour*3600000+monitorLog.localt.wMinute*60000+monitorLog.localt.wSecond*1000+monitorLog.localt.wMilliseconds;

	char monitorline[256];
	int linesz;

	if (monitorfh==NULL) {
		monitorLog.difft = 0;
		monitorLog.startDiff = localTick-monitorLog.feedt;

		char monitorFn[256];
		sprintf( monitorFn, "88889-%04d%02d%02d-pos.dat", monitorLog.localt.wYear, monitorLog.localt.wMonth, monitorLog.localt.wDay );
		monitorfh = fopen( monitorFn, "a+t" );
		if (monitorfh!=NULL) {
			linesz = sprintf(monitorline, "================================================================================\n" );
			fwrite(monitorline, 1, linesz, monitorfh);
		}
	}
	if (monitorfh!=NULL) {
		monitorLog.difft = (localTick-monitorLog.feedt)-monitorLog.startDiff;
		linesz = sprintf( monitorline, "%02d:%02d:%02d.%03d,%02d:%02d:%02d,%d,%d\n",
			monitorLog.localt.wHour, monitorLog.localt.wMinute, monitorLog.localt.wSecond, monitorLog.localt.wMilliseconds,
			feedhhmmss/10000, (feedhhmmss%10000)/100, feedhhmmss%100,
			monitorLog.index, monitorLog.difft );
		fwrite( monitorline, 1, linesz, monitorfh );
		fflush( monitorfh );
	}
}

int TsecMis3_15(const IP_FMT& prot, int market)
{
    if (prot.mis3_head.head.market==1) {
    	write_monitor_file( prot );
    }
    int  i;
    int  fptr;
    int  class_total, yes_class_total, clss_length;
    long temp;
    struct MARKET_TIME_15 *markTime;
    struct MARKET_TIME_5 *markTime5;
    char  CheckSum=0;

    if(market == MK_TSEC) {
        markTime5 = &TsecTime_5;
        TsecTime_5.IndexTime =  (int) CutMrkTestTime(BCD_to_Long(prot.mis3_head.time, TIME_FSIZE), MK_TSEC);
        TimeTo5SecPtr(TsecTime_5.IndexTime, &TsecTime_5.Mis3);

        TsecTime_15.IndexTime = TsecTime_5.IndexTime;
        markTime = &TsecTime_15;
        TimeTo15SecPtr(TsecTime_15.IndexTime, &TsecTime_15.Mis3);
        class_total = (int) BCD_to_Long(&prot.mis3_head.total_class);
        if( !tsec_class_total) {
            if(gMisVer  && !fg_Richv710)
                tsec_class_total = 34;
            else
                tsec_class_total = class_total;
        }
        else if((tsec_class_total != class_total) && !(gMisVer  && !fg_Richv710))
            MemoMsg("集中市場分類指數Total錯誤!!");
        if(TsecTime_15.IndexTime >= 90000) {
            if(tsec_yes_flag == RECV_NO){ 
                tsec_yes_flag = RECV_YES;
                fptr = open( "tsec_cls.yes", O_RDONLY | O_BINARY );
                read(fptr, &yes_class_total, sizeof(int));
                read(fptr, &TsecClassYesIndex, INDEX_FSIZE*yes_class_total);
                close(fptr);
            }
        }
        else {
           tsec_yes_flag = RECV_YES;          // before 09:00 turn on computer
        }
        for(i=0 ; i < class_total; i++) {
            if((temp = BCD_to_Long(prot.mis3_head.index + i*INDEX_FSIZE, INDEX_FSIZE)) >= 0) {
                if(TsecTime_15.IndexTime <= 90000) {
                    if(i == TSEC_NOBANK_INDEX)
                        NoBankIndex=temp;
                    TsecClassYesIndex[i] = temp;
                }
                else {
                    if(TsecClassYesIndex[i] == 0l) {
                        if(i == TSEC_NOBANK_INDEX)
                            Mem1min99961.index = temp;
                        TsecClassIndex[i] = temp;
                    }
                    else {
                                if(i == TSEC_NOBANK_INDEX)
                                    Mem1min99961.index = temp;
                                TsecClassIndex[i] = temp;
                    }
                }
            }                
        }
    }
    else {

        markTime5 = &OtcTime_5;
        OtcTime_5.IndexTime =  (int) CutMrkTestTime(BCD_to_Long(prot.mis3_head.time, TIME_FSIZE), MK_TSEC);
        TimeTo5SecPtr(OtcTime_5.IndexTime, &OtcTime_5.Mis3);

        markTime = &OtcTime_15;
        OtcTime_15.IndexTime =  OtcTime_5.IndexTime;
        TimeTo15SecPtr(OtcTime_15.IndexTime, &OtcTime_15.Mis3);

        class_total = (int) BCD_to_Long(&prot.mis3_head.total_class);
        if( !otc_class_total)  {
            if(gMisVer && !fg_Richv710)
                otc_class_total = 13;
            else
                otc_class_total = class_total;
        }
        else if((otc_class_total != class_total) && !(gMisVer  && !fg_Richv710))
            MemoMsg("上櫃市場分類指數Total錯誤!!");
        if(OtcTime_15.IndexTime >= 90000) {
            if(otc_yes_flag == RECV_NO){ // 九點後才開 RT-DATA 需由 f9991_24.yes 讀入昨收
                otc_yes_flag = RECV_YES;
                fptr = open( "otc_cls.yes", O_RDONLY | O_BINARY );
                read(fptr, &yes_class_total, sizeof(int));
                read(fptr, &OtcClassYesIndex, INDEX_FSIZE*yes_class_total);
                close(fptr);
            }
        }
        else
           otc_yes_flag = RECV_YES;          // before 09:00 turn on computer
        for(i=0 ; i < class_total; i++) {
            if((temp = BCD_to_Long(prot.mis3_head.index + i*INDEX_FSIZE, INDEX_FSIZE)) >= 0) {
                if(OtcTime_15.IndexTime <= 90000)
                    OtcClassYesIndex[i] = temp;
                else {
                        OtcClassIndex[i] = temp;
                }
            }
        }
    }
    CheckMarketClose_15(markTime);
    if(gMisVer  && !fg_Richv710)  {
        ReCoverMis3Data(market);
        if(market == MK_TSEC)
            class_total = 34;
        else
            class_total = 13;
    }
// 5sec
    BINFMT bp;
    memset(bp.buf, 0, sizeof(bp.buf));
    bp.i_cs_inx2.esc = ESC;
    bp.i_cs_inx2.mis = 0xe0;
    bp.i_cs_inx2.mkt = market;
    bp.i_cs_inx2.cnt = class_total;
    if(market == MK_TSEC)  {
        memcpy(&(bp.i_cs_inx2.ptr), &(TsecTime_5.Mis3.time_ptr), 6);
        for( i=0 ; i< BIN_IP_M_CLS_INX2_SIZE -1  ; i++ )
            CheckSum ^= bp.buf[i];
        bp.buf[BIN_IP_M_CLS_INX2_SIZE-1] = CheckSum;
        clss_length = class_total * sizeof(long);
        if(TsecTime_15.IndexTime <= 90000)
            memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], (char *)&TsecClassYesIndex[0], clss_length);
        else
            memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], (char *)&TsecClassIndex[0], clss_length);
        CheckSum=0;
        clss_length++;
        for( i=0 ; i< clss_length -1  ; i++ )
            CheckSum ^= bp.buf[i + BIN_IP_M_CLS_INX2_SIZE];
        bp.buf[BIN_IP_M_CLS_INX2_SIZE + clss_length -1] = CheckSum;
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_CLS_INX2_SIZE + clss_length, 0);
    }
    else { //Otc
        memcpy(&(bp.i_cs_inx2.ptr), &(OtcTime_5.Mis3.time_ptr), 6);
        for ( i=0 ; i< BIN_IP_M_CLS_INX2_SIZE -1; i++ ) {
            CheckSum ^= bp.buf[i];
        }
        bp.buf[BIN_IP_M_CLS_INX2_SIZE-1] = CheckSum;
        clss_length = class_total * sizeof(long);
        if (OtcTime_15.IndexTime <= 90000) {
            memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], (char *)&OtcClassYesIndex[0], clss_length);
        }
        else {
            memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], (char *)&OtcClassIndex[0], clss_length);
        }
        CheckSum = 0;
        clss_length++;
        for ( i=0 ; i< clss_length-1; i++ ) {
            CheckSum ^= bp.buf[i + BIN_IP_M_CLS_INX2_SIZE];
        }
        bp.buf[BIN_IP_M_CLS_INX2_SIZE + clss_length -1] = CheckSum;
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_CLS_INX2_SIZE + clss_length, 0);
   }
// 15sec
    CheckSum=0;
    bp.i_cs_inx2.esc = ESC;
    bp.i_cs_inx2.mis = 0x72;
    bp.i_cs_inx2.mkt = market;
    bp.i_cs_inx2.cnt = class_total;
    if (market == MK_TSEC) {
        memcpy(&(bp.i_cs_inx2.ptr), &(TsecTime_15.Mis3.time_ptr), 6);
        for( i=0 ; i<BIN_IP_M_CLS_INX2_SIZE-1; i++ ) {
            CheckSum ^= bp.buf[i];
        }
        bp.buf[BIN_IP_M_CLS_INX2_SIZE-1] = CheckSum;
        clss_length = class_total * sizeof(long);
        if(TsecTime_15.IndexTime <= 90000) {
            memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], (char *)&TsecClassYesIndex[0], clss_length);
        }
        else {
            memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], (char *)&TsecClassIndex[0], clss_length);
        }
        CheckSum=0;
        clss_length++;
        for ( i=0 ; i< clss_length-1; i++ ) {
            CheckSum ^= bp.buf[i + BIN_IP_M_CLS_INX2_SIZE];
        }
        bp.buf[BIN_IP_M_CLS_INX2_SIZE + clss_length -1] = CheckSum;
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_CLS_INX2_SIZE + clss_length, 0);
        if(TsecTime_15.IndexTime == 999999) {
            tsecA0_last_len = BIN_IP_M_CLS_INX2_SIZE + clss_length;
            memcpy(tsecA0_last_buf, bp.buf, tsecA0_last_len);
        }
        send_15_sec_index(1);
        if((TsecTime_15.IndexTime != 999999) && (TsecTime_15.IndexTime >= 90000) && (TsecClearOneMinAmount != TsecTime_15.IndexTime)) {
           TsecClearOneMinAmount = TsecTime_15.IndexTime;
           ClearOneMinAmount(MK_TSEC, TsecClearOneMinAmount);
        }
    }
    else { //Otc
        memcpy(&(bp.i_cs_inx2.ptr), &(OtcTime_15.Mis3.time_ptr), 6);
        for( i=0 ; i< BIN_IP_M_CLS_INX2_SIZE -1; i++ ) {
            CheckSum ^= bp.buf[i];
        }
        bp.buf[BIN_IP_M_CLS_INX2_SIZE-1] = CheckSum;
        clss_length = class_total * sizeof(long);
        if(OtcTime_15.IndexTime <= 90000) {
            memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], (char *)&OtcClassYesIndex[0], clss_length);
        }
        else {
            memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], (char *)&OtcClassIndex[0], clss_length);
        }
        CheckSum=0;
        clss_length++;
        for( i=0 ; i< clss_length -1  ; i++ ) {
            CheckSum ^= bp.buf[i + BIN_IP_M_CLS_INX2_SIZE];
        }
        bp.buf[BIN_IP_M_CLS_INX2_SIZE + clss_length -1] = CheckSum;
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_CLS_INX2_SIZE + clss_length, 0);
        if (OtcTime_15.IndexTime == 999999) {
            otcA0_last_len = BIN_IP_M_CLS_INX2_SIZE + clss_length;
            memcpy(otcA0_last_buf, bp.buf, otcA0_last_len);
        }
        send_otc_15sec_index(1, 0);
        if ((OtcTime_15.IndexTime != 999999) && (OtcTime_15.IndexTime >= 90000) && (OtcClearOneMinAmount != OtcTime_15.IndexTime)) {
            OtcClearOneMinAmount = OtcTime_15.IndexTime;
            ClearOneMinAmount(MK_OTC, OtcClearOneMinAmount);
        }
    }
    return 1;
}

int Test15_TsecMis3(const IP_FMT& prot, int market, int nMdyInx, int nAddPtr)
{
    int  i;
    int  fptr;
    int  class_total, yes_class_total, clss_length;
    long temp;
    struct MARKET_TIME *markTime;
    struct TIME_15     tm15CovNew;
    char  CheckSum=0;

    if(market == MK_TSEC) {
        markTime = &TsecTime;
        TsecTime.IndexTime =  (int) CutMrkTestTime(BCD_to_Long(prot.mis3_head.time, TIME_NOW_SIZE)*100, MK_TSEC)/100;
        TimeTo1MinPtr(TsecTime.IndexTime, &TsecTime.Mis3);
        class_total = (int) BCD_to_Long(&prot.mis3_head.total_class);
        if( !tsec_class_total) {
            if(gMisVer  && !fg_Richv710)
                tsec_class_total = 34;
            else
                tsec_class_total = class_total;
        }
        else if((tsec_class_total != class_total) && !(gMisVer  && !fg_Richv710))
            MemoMsg("集中市場分類指數Total錯誤!!");
        if(TsecTime.IndexTime >= 900) {
            if(tsec_yes_flag == RECV_NO){ // 九點後才開 RT-DATA 需由 f9991_24.yes 讀入昨收
                tsec_yes_flag = RECV_YES;
                fptr = open( "tsec_cls.yes", O_RDONLY | O_BINARY );
                read(fptr, &yes_class_total, sizeof(int));
                read(fptr, &TsecClassYesIndex, INDEX_FSIZE*yes_class_total);
                close(fptr);
            }
        }
        else
           tsec_yes_flag = RECV_YES;          // before 09:00 turn on computer
        for(i=0 ; i < class_total; i++) {
            if((temp = BCD_to_Long(prot.mis3_head.index + i*INDEX_FSIZE, INDEX_FSIZE)) >= 0) {
                if(TsecTime.IndexTime < 900) {
                    if(i == TSEC_NOBANK_INDEX)
                        NoBankIndex=temp;
                    TsecClassYesIndex[i] = temp;
                }
                else {
                    if(TsecClassYesIndex[i] == 0l) {
                        if(i == TSEC_NOBANK_INDEX)
                            Mem1min99961.index = temp;
                        TsecClassIndex[i] = temp;
                    }
                    else {
                                if(i == TSEC_NOBANK_INDEX)
                                    Mem1min99961.index = temp;
                                TsecClassIndex[i] = temp + nMdyInx;
                    }
                }
            }
        }
    }
    else {
        markTime = &OtcTime;
        OtcTime.IndexTime =  (int) CutMrkTestTime(BCD_to_Long(prot.mis3_head.time, TIME_NOW_SIZE)*100, MK_TSEC)/100;
        TimeTo1MinPtr(OtcTime.IndexTime, &OtcTime.Mis3);
        class_total = (int) BCD_to_Long(&prot.mis3_head.total_class);
        if( !otc_class_total)  {
            if(gMisVer && !fg_Richv710)
                otc_class_total = 13;
            else
                otc_class_total = class_total;
        }
        else if((otc_class_total != class_total) && !(gMisVer  && !fg_Richv710))
            MemoMsg("上櫃市場分類指數Total錯誤!!");
        if(OtcTime.IndexTime >= 900) {
            if(otc_yes_flag == RECV_NO){ // 九點後才開 RT-DATA 需由 f9991_24.yes 讀入昨收
                otc_yes_flag = RECV_YES;
                fptr = open( "otc_cls.yes", O_RDONLY | O_BINARY );
                read(fptr, &yes_class_total, sizeof(int));
                read(fptr, &OtcClassYesIndex, INDEX_FSIZE*yes_class_total);
                close(fptr);
            }
        }
        else
           otc_yes_flag = RECV_YES;          // before 09:00 turn on computer
        for(i=0 ; i < class_total; i++) {
            if((temp = BCD_to_Long(prot.mis3_head.index + i*INDEX_FSIZE, INDEX_FSIZE)) >= 0) {
                if(OtcTime.IndexTime < 900)
                    OtcClassYesIndex[i] = temp;
                else {
                        OtcClassIndex[i] = temp + nMdyInx;
                }
            }
        }
    }
    CheckMarketClose(markTime);
    if(gMisVer  && !fg_Richv710)  {
        ReCoverMis3Data(market);
        if(market == MK_TSEC)
            class_total = 34;
        else
            class_total = 13;
    }
    BINFMT bp;
    memset(bp.buf, 0, sizeof(bp.buf));
    bp.i_cs_inx2.esc = ESC;
    bp.i_cs_inx2.mis = 0x72;
    bp.i_cs_inx2.mkt = market;
    bp.i_cs_inx2.cnt = class_total;
    if(market == MK_TSEC)  {
        if( !CoverNewInxTimePtr(TsecTime.Mis3, &tm15CovNew, nAddPtr))
            return 0;
        memcpy(&(bp.i_cs_inx2.ptr), &(tm15CovNew.time_ptr), 6);
        for( i=0 ; i< BIN_IP_M_CLS_INX2_SIZE -1  ; i++ )
            CheckSum ^= bp.buf[i];
        bp.buf[BIN_IP_M_CLS_INX2_SIZE-1] = CheckSum;
        clss_length = class_total * sizeof(long);
        if(TsecTime.IndexTime < 900)
            memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], (char *)&TsecClassYesIndex[0], clss_length);
        else
            memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], (char *)&TsecClassIndex[0], clss_length);
        CheckSum=0;
        clss_length++;
        for( i=0 ; i< clss_length -1  ; i++ )
            CheckSum ^= bp.buf[i + BIN_IP_M_CLS_INX2_SIZE];
        bp.buf[BIN_IP_M_CLS_INX2_SIZE + clss_length -1] = CheckSum;
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_CLS_INX2_SIZE + clss_length, 0);
        if(TsecTime.IndexTime == 9999) {
            tsecA0_last_len = BIN_IP_M_CLS_INX2_SIZE + clss_length;
            memcpy(tsecA0_last_buf, bp.buf, tsecA0_last_len);
        }
        send_one_min_index(1);
        if((TsecTime.IndexTime != 9999) && (TsecTime.IndexTime >= 900) && (TsecClearOneMinAmount != TsecTime.IndexTime)) {
           TsecClearOneMinAmount = TsecTime.IndexTime;
           ClearOneMinAmount(MK_TSEC, TsecClearOneMinAmount);
           }
    }
    else { //Otc
        if( !CoverNewInxTimePtr(OtcTime.Mis3, &tm15CovNew, nAddPtr))
            return 0;
        memcpy(&(bp.i_cs_inx2.ptr), &(tm15CovNew.time_ptr), 6);
        for( i=0 ; i< BIN_IP_M_CLS_INX2_SIZE -1  ; i++ )
            CheckSum ^= bp.buf[i];
        bp.buf[BIN_IP_M_CLS_INX2_SIZE-1] = CheckSum;
        clss_length = class_total * sizeof(long);
        if(OtcTime.IndexTime < 900)
            memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], (char *)&OtcClassYesIndex[0], clss_length);
        else
            memcpy( &bp.buf[BIN_IP_M_CLS_INX2_SIZE], (char *)&OtcClassIndex[0], clss_length);
        CheckSum=0;
        clss_length++;
        for( i=0 ; i< clss_length -1  ; i++ )
            CheckSum ^= bp.buf[i + BIN_IP_M_CLS_INX2_SIZE];
        bp.buf[BIN_IP_M_CLS_INX2_SIZE + clss_length -1] = CheckSum;
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_CLS_INX2_SIZE + clss_length, 0);
        if(OtcTime.IndexTime == 9999) {
            otcA0_last_len = BIN_IP_M_CLS_INX2_SIZE + clss_length;
            memcpy(otcA0_last_buf, bp.buf, otcA0_last_len);
        }
        send_otc_1min_index(1, 0);
        if((OtcTime.IndexTime != 9999) && (OtcTime.IndexTime >= 900) && (OtcClearOneMinAmount != OtcTime.IndexTime)) {
            OtcClearOneMinAmount = OtcTime.IndexTime;
            ClearOneMinAmount(MK_OTC, OtcClearOneMinAmount);
        }
   }
   return 1;
}

void saveBBinfo(void)
{
    FILE *fp;
    int  i, j, seq_no, bb_cnt;
    char tmp_buf[62], org_buf[62];

    if ( tsec_update_fg) {
        memset(tmp_buf, 0x20, 62);
        tmp_buf[60] = '\r';
        tmp_buf[61] = '\n';
        if (access(default_bb_file, 0) != 0) {
            if ((fp=_fsopen(default_bb_file, "wb", SH_DENYNONE)) != NULL) {
                fwrite("臺灣證券交易所緊急公告                                      \r\n", 62, 1, fp);
                fclose(fp);
            }
        }
        if ((fp=_fsopen(default_bb_file, "ab+", SH_DENYNONE)) != NULL) {
            for (i=0; i<TsecEMNew_Count; i++) {
                fwrite(TsecEM9997[i], 60, 1, fp);
                fwrite("\r\n", 2, 1, fp);
            }
            fclose(fp);
        }
        tmp_copy(bk_bbin_dir,bk_bbin_file,default_bb_file);
        tsec_update_fg = 0;
    }
    if ( otc_update_fg) {
        memset(tmp_buf, 0x20, 62);
        tmp_buf[60] = '\r';
        tmp_buf[61] = '\n';
        if (access(default_bb_file_otc, 0) != 0) {
            if ((fp=_fsopen(default_bb_file_otc, "wb", SH_DENYNONE)) != NULL) {
                fwrite("櫃檯買賣中心緊急公告                                      \r\n", 62, 1, fp);
                fclose(fp);
            }
        }
        if ((fp=_fsopen(default_bb_file_otc, "ab+", SH_DENYNONE)) != NULL) {
            for (i=0; i<OtcEMNew_Count; i++) {
                fwrite(OtcEM9997[i], 60, 1, fp);
                fwrite("\r\n", 2, 1, fp);
            }
            fclose(fp);
        }
        tmp_copy(bk_bbin_dir,bk_bbin_file_otc,default_bb_file_otc);
        otc_update_fg = 0;
    }
}

// Tsec Emergent Announcement Processing
void TsecEMNewsUpdateToMemAndSend(const IP_FMT& prot, int seq)
{
    int len,j;
    if (seq >= MAX_NEW) {
        return ;
    }

    BINFMT bp;
    if (seq == 1) {  // new cycle begins    
        l2TsecEMNew = l1TsecEMNew;
        l1TsecEMNew = TsecEMNew_Count;
        TsecEMNew_Count = 0;
        if (l1TsecEMNew < l2TsecEMNew) {  // need to reset some memory space
            // send out 0x36 to VIP for clearing EM memory
            memset(bp.buf, 0, sizeof(bp.buf));
            bp.f_new_9997.esc        = ESC;
            bp.f_new_9997.mis        = 'o';
            bp.f_new_9997.market     = 0x36; // TSEC EM clearing market code
            bp.f_new_9997.num = l1TsecEMNew;
            CalCheckSumAndSendToMoxaCard( bp.buf, BIN_NEW_9997_SIZE - 1);
            // reset memory
            for (j=l1TsecEMNew+1; j<=l2TsecEMNew; j++) {
                memset(TsecEM9997[j], 0, 60);
            }
      }
    }
    len=((int)BCD_to_Long(prot.mis5_head.head.length, LENGTH_FSIZE) - sizeof(iphd) - 4);
    if ( memcmp(TsecEM9997[seq], &prot.mis5_head.data, len)) {
        memset(TsecEM9997[seq], ' ', 60);
        memcpy(TsecEM9997[seq], &prot.mis5_head.data, len);
        memset(bp.buf, 0, sizeof(bp.buf));
        bp.f_new_9997.esc        = ESC;
        bp.f_new_9997.mis        = 'o';
        bp.f_new_9997.market     = 0x06; // TSEC emergent announcement market code
        memcpy(bp.f_new_9997.text, TsecEM9997[seq], 60);
        bp.f_new_9997.num = seq;
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_NEW_9997_SIZE - 1);
        tsec_update_fg = 1;
    }
    if (TsecEMNew_Count < seq) {
        TsecEMNew_Count = seq;
    }
}

// Otc Emergent Announcement Processing
void OtcEMNewsUpdateToMemAndSend(const IP_FMT& prot, int seq)
{
   int i,len,j;

    if (seq >= MAX_NEW) {
        return ;
    }
    BINFMT bp;
    if (seq == 1) { // new cycle begins
        l2OtcEMNew = l1OtcEMNew;
        l1OtcEMNew = OtcEMNew_Count;
        OtcEMNew_Count = 0;

        if (l1OtcEMNew < l2OtcEMNew) { // need to reset some memory space
            // send out 0x36 to VIP for clearing EM memory
            memset(bp.buf, 0, sizeof(bp.buf));
            bp.f_new_9997.esc        = ESC;
            bp.f_new_9997.mis        = 'o';
            bp.f_new_9997.market     = 0x37; // TSEC EM clearing market code
            bp.f_new_9997.num = l1OtcEMNew;
            CalCheckSumAndSendToMoxaCard( bp.buf, BIN_NEW_9997_SIZE - 1);
         
            // reset memory
            for (j=l1OtcEMNew+1; j<=l2OtcEMNew; j++)
                memset(OtcEM9997[j], 0, 60);
       }
    }
    len = ((int)BCD_to_Long(prot.mis5_head.head.length, LENGTH_FSIZE) - sizeof(iphd) - 4);
    if (memcmp(OtcEM9997[seq],&prot.mis5_head.data, len)) {
        memset(OtcEM9997[seq], ' ', 60);
        memcpy(OtcEM9997[seq],&prot.mis5_head.data, len);
        memset(bp.buf, 0, sizeof(bp.buf));
        bp.f_new_9997.esc        = ESC;
        bp.f_new_9997.mis        = 'o';
        bp.f_new_9997.market     = 0x07; // TSEC emergent announcement market code
        memcpy(bp.f_new_9997.text, OtcEM9997[seq], 60);
        bp.f_new_9997.num = seq;
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_NEW_9997_SIZE - 1);
        otc_update_fg = 1;
    }
    if (OtcEMNew_Count < seq) {
        OtcEMNew_Count = seq;
    }
}

void TsecNewsUpdateToMemAndSend(const IP_FMT& prot, int market)
{
   int seq,len;

   seq = (int)BCD_to_Long(prot.mis5_head.head.seq, 4);

    if ((BCD_to_Long(&prot.mis5_head.type) >= 90)) // &&(market == MK_TSEC))
    {
        if(market == MK_TSEC)
            TsecEMNewsUpdateToMemAndSend(prot, seq);
        else  if(market == MK_OTC)
            OtcEMNewsUpdateToMemAndSend(prot, seq);
       return;
    }
    if (seq >= MAX_NEW)
        return ;
    len=((int)BCD_to_Long(prot.mis5_head.head.length, LENGTH_FSIZE) - sizeof(iphd) - 4);
    BINFMT bp;
    if(market == MK_TSEC) {
        if (strncmp(Mem9997[seq],&prot.mis5_head.data, len)) {
            memset(Mem9997[seq], ' ', 60);
            memcpy(Mem9997[seq],&prot.mis5_head.data, len);
            memset(bp.buf, 0, sizeof(bp.buf));
            bp.f_new_9997.esc        = ESC;
            bp.f_new_9997.mis        = 'o';
            bp.f_new_9997.market     = MK_TSEC;        // TSEC market code
            memcpy(bp.f_new_9997.text, Mem9997[seq], 60);
            bp.f_new_9997.num = seq;
            CalCheckSumAndSendToMoxaCard( bp.buf, BIN_NEW_9997_SIZE - 1);
            if (New_Count < seq)
                New_Count = seq;
        }
    }
    else {
        if (strncmp(OTCMem9997[seq], &prot.mis5_head.data, len)) {
            memset(OTCMem9997[seq], ' ', 60);
            memcpy(OTCMem9997[seq], &prot.mis5_head.data, len);
            // send out 'o'
            memset(bp.buf, 0, sizeof(bp.buf));
            bp.f_new_9997.esc        = ESC;
            bp.f_new_9997.mis        = 'o';
            bp.f_new_9997.market     = MK_OTC;        // OTC market code
            memcpy(bp.f_new_9997.text, OTCMem9997[seq], 60);
            bp.f_new_9997.num = seq;
            CalCheckSumAndSendToMoxaCard( bp.buf, BIN_NEW_9997_SIZE - 1);
            if (OTCNew_Count < seq) {
               OTCNew_Count = seq;
            }
        }
    }
}

static long g_deal_sheet, g_deal_price, g_time_sheet;

int GetBCDMis2SubValue_V3(const IP_FMT& prot, char dataType, int seq)
{
    int  offset = 4;
    int  buy_num, sell_num;
    int  i;
    long price, sheet;

    g_deal_sheet = BCD_to_Long(prot.mis6_v3.deal_sheet, SHEET_FSIZE);
    if(dataType & _DEAL)  {
        g_deal_price = BCD_to_Long(prot.mis6_v3.deal_sheet+offset, PRICE_FSIZE);
        offset += PRICE_FSIZE;
        g_time_sheet = BCD_to_Long(prot.mis6_v3.deal_sheet+offset, SHEET_FSIZE);
        offset += SHEET_FSIZE;
    }
    else {
        g_deal_sheet = 0l;
        g_deal_price = 0l;
        g_time_sheet = 0l;
    }
    buy_num = ((dataType & _BUY_PRICE_SHEET) >> 4);
    for(i=0; i<MAX_BEST; i++) {
        if(buy_num > 0) {
            price  = BCD_to_Long(prot.mis6_v3.deal_sheet+offset ,PRICE_FSIZE);
            offset += PRICE_FSIZE;
            sheet  = BCD_to_Long(prot.mis6_v3.deal_sheet+offset ,SHEET_FSIZE);
            offset += SHEET_FSIZE;
            buy_num--;
        }
        else {
            price = 0l;
            sheet = 0l;
        }
        StockMem[seq].buy_price[i] = price;
        StockMem[seq].buy_sheet[i] = sheet;
    }

    sell_num = ((dataType & _SELL_PRICE_SHEET) >> 1);
    for(i=0; i<MAX_BEST; i++) {
        if(sell_num > 0) {
            price  = BCD_to_Long(prot.mis6_v3.deal_sheet+offset ,PRICE_FSIZE);
            offset += PRICE_FSIZE;
            sheet  = BCD_to_Long(prot.mis6_v3.deal_sheet+offset ,SHEET_FSIZE);
            offset += SHEET_FSIZE;
            sell_num--;
        }
        else {
            price = 0l;
            sheet = 0l;
        }
        StockMem[seq].sell_price[i] = price;
        StockMem[seq].sell_sheet[i] = sheet;
    }
    return 1;
}

int GetBCDMis2SubValue_V4(const IP_FMT& prot, char dataType, int seq)
{
    int  offset = 4;
    int  buy_num, sell_num;
    int  i;
    long price, sheet;

    g_deal_sheet = BCD_to_Long(prot.mis6_v3.deal_sheet, 4);
    if(dataType & _DEAL)  {
        g_deal_price = BCD_to_Long(prot.mis6_v3.deal_sheet+offset, 5)/100;
        offset += 5;
        g_time_sheet = BCD_to_Long(prot.mis6_v3.deal_sheet+offset, 4);
        offset += 4;
    }
    else {
        g_deal_sheet = 0l;
        g_deal_price = 0l;
        g_time_sheet = 0l;
    }
    buy_num = ((dataType & _BUY_PRICE_SHEET) >> 4);
    for (i=0; i<MAX_BEST; i++) {
        if (buy_num > 0) {
            price = BCD_to_Long(prot.mis6_v3.deal_sheet+offset, 5)/100;
            if (price==0) {
                price = 9999999;
            }
            offset += 5;
            sheet = BCD_to_Long(prot.mis6_v3.deal_sheet+offset, 4);
            offset += 4;
            buy_num--;
        }
        else {
            price = 0l;
            sheet = 0l;
        }
        StockMem[seq].buy_price[i] = price;
        StockMem[seq].buy_sheet[i] = sheet;
    }

    sell_num = ((dataType & _SELL_PRICE_SHEET) >> 1);
    for (i=0; i<MAX_BEST; i++) {
        if (sell_num > 0) {
            price = BCD_to_Long(prot.mis6_v3.deal_sheet+offset, 5)/100;
            if (price==0) {
                price = 9999999;
            }
            offset += 5;
            sheet = BCD_to_Long(prot.mis6_v3.deal_sheet+offset, 4);
            offset += 4;
            sell_num--;
        }
        else {
            price = 0l;
            sheet = 0l;
        }
        StockMem[seq].sell_price[i] = price;
        StockMem[seq].sell_sheet[i] = sheet;
    }
    return 1;
}

int read_mis20_v1_tail(const IP_FMT& prot, int seq) {
    int  offset = 0;
    int  buy_num, sell_num;
    int  i;
    long price, sheet;

    g_deal_sheet = BCD_to_Long(prot.mis20_v1.deal_sheet, 4);
    char dataType = prot.mis20_v1.field_fg;
    if (dataType & _DEAL)  {
        g_deal_price = BCD_to_Long(prot.mis20_v1.var_tail+offset, 5)/100;
        g_time_sheet = BCD_to_Long(prot.mis20_v1.var_tail+offset+5, 4);
        offset += 9;
    }
    else {
        g_deal_sheet = 0l;
        g_deal_price = 0l;
        g_time_sheet = 0l;
    }
    buy_num = ((dataType & _BUY_PRICE_SHEET) >> 4);
    for (i=0; i<MAX_BEST; i++) {
        if (buy_num > 0) {
            price = BCD_to_Long(prot.mis20_v1.var_tail+offset, 5)/100;
            sheet = BCD_to_Long(prot.mis20_v1.var_tail+offset+5, 4);
            offset += 9;
            buy_num--;
        }
        else {
            price = 0l;
            sheet = 0l;
        }
        StockMem[seq].buy_price[i] = price;
        StockMem[seq].buy_sheet[i] = sheet;
    }

    sell_num = ((dataType & _SELL_PRICE_SHEET) >> 1);
    for (i=0; i<MAX_BEST; i++) {
        if (sell_num > 0) {
            price = BCD_to_Long(prot.mis20_v1.var_tail+offset, 5)/100;
            sheet = BCD_to_Long(prot.mis20_v1.var_tail+offset+5, 4);
            offset += 9;
            sell_num--;
        }
        else {
            price = 0l;
            sheet = 0l;
        }
        StockMem[seq].sell_price[i] = price;
        StockMem[seq].sell_sheet[i] = sheet;
    }
    return 1;
}

int GetBCDMis2SubValue_V2(const IP_FMT& prot, char dataType, int seq)
{
    int  offset = 1;
    int  buy_num, sell_num;
    int  i, j;
    long price, sheet;

    if(dataType & _DEAL)  {
        g_deal_price = BCD_to_Long(&(prot.mis6_v2.up_down)+offset, PRICE_FSIZE);
        offset += PRICE_FSIZE;
        g_deal_sheet = BCD_to_Long(&(prot.mis6_v2.up_down)+offset, SHEET_FSIZE);
        offset += SHEET_FSIZE;
    }
    else {
        g_deal_sheet = 0l;
        g_deal_price = 0l;
    }
    buy_num = ((dataType & _BUY_PRICE_SHEET) >> 4);
    for(i=0; i<MAX_BEST; i++) {
        if(buy_num > 0) {
            price  = BCD_to_Long(&(prot.mis6_v2.up_down)+offset ,PRICE_FSIZE);
            offset += PRICE_FSIZE;
            sheet  = BCD_to_Long(&(prot.mis6_v2.up_down)+offset ,SHEET_FSIZE);
            offset += SHEET_FSIZE;
            buy_num--;
        }
        else {
            price = 0l;
            sheet = 0l;
        }
        StockMem[seq].buy_price[i] = price;
        StockMem[seq].buy_sheet[i] = sheet;
    }

    sell_num = ((dataType & _SELL_PRICE_SHEET) >> 1);
    for(i=0; i<MAX_BEST; i++) {
        if(sell_num > 0) {
            price  = BCD_to_Long(&(prot.mis6_v2.up_down)+offset ,PRICE_FSIZE);
            offset += PRICE_FSIZE;
            sheet  = BCD_to_Long(&(prot.mis6_v2.up_down)+offset ,SHEET_FSIZE);
            offset += SHEET_FSIZE;
            sell_num--;
        }
        else {
            price = 0l;
            sheet = 0l;
        }
        StockMem[seq].sell_price[i] = price;
        StockMem[seq].sell_sheet[i] = sheet;
    }
    return 1;
}

void IP_FixedPriceBuySellUpdateToMemAndSend_V2(const IP_FMT& prot, int seq)
{
    long buy_sheet, sell_sheet;
    int i, tmp_cnt;
    long tmp_time;

    if (seq<0) {
        return;
    }
    tmp_time = BCD_to_Long(prot.otc_mis10_v2.time, TIME_NOW_SIZE);
    buy_sheet = BCD_to_Long(prot.otc_mis10_v2.buy_sheet, SHEET_FSIZE);
    sell_sheet = BCD_to_Long(prot.otc_mis10_v2.sell_sheet, SHEET_FSIZE);
    if (tmp_time == 0L) // fixed price trade but without deal made
        return;
    StockMem[seq].buy_sheet[0] = buy_sheet;
    StockMem[seq].sell_sheet[0] = sell_sheet;
    for(i=1; i<MAX_BEST; i++) {
        StockMem[seq].buy_sheet[i] = 0;
        StockMem[seq].sell_sheet[i] = 0;
    }
    StockMem[seq].field_fg = _FIXED_PRICE_BUY_SELL;
    MemTransferToMis2BinFmtAndSendEx(seq, _FIXED_PRICE_BUY_SELL);
}

void IP_FixedPriceBuySellUpdateToMemAndSend_V3(const IP_FMT& prot, int seq) {
    long buy_sheet, sell_sheet;
    int i, tmp_cnt;
    long tmp_time;

    if (seq<0) {
        return;
    }
    tmp_time = BCD_to_Long(prot.otc_mis10_v3.time, TIME_NOW_SIZE);
    buy_sheet = BCD_to_Long(prot.otc_mis10_v3.buy_sheet, 4);
    sell_sheet = BCD_to_Long(prot.otc_mis10_v3.sell_sheet, 4);
    if (tmp_time == 0L) { // fixed price trade but without deal made
        return;
	}
    StockMem[seq].buy_sheet[0] = buy_sheet;
    StockMem[seq].sell_sheet[0] = sell_sheet;
    for(i=1; i<MAX_BEST; i++) {
        StockMem[seq].buy_sheet[i] = 0;
        StockMem[seq].sell_sheet[i] = 0;
    }
    StockMem[seq].field_fg = _FIXED_PRICE_BUY_SELL;
    MemTransferToMis2BinFmtAndSendEx(seq, _FIXED_PRICE_BUY_SELL);
}

void IP_FixedPriceTradeUpdateToMemAndSend_V2(IP_FMT& prot, int seq)
{
    long temp, t_sheet;
    int i, tmp_cnt, kind_id;
    long tmp_time;

    tmp_time = BCD_to_Long(prot.mis9_v2.time, TIME_NOW_SIZE);
    g_deal_price = BCD_to_Long(prot.mis9_v2.deal_price, PRICE_FSIZE);
    g_deal_sheet = BCD_to_Long(prot.mis9_v2.deal_sheet, SHEET_FSIZE);
    if (tmp_time == 0L) // fixed price trade but without deal made
        return;
    if (StockMem[seq].close1deal_sheet == 0) // set up close1deal_sheet
        StockMem[seq].close1deal_sheet = StockMem[seq].deal_sheet;
    g_deal_sheet += StockMem[seq].close1deal_sheet;

      // format time to be 13:31
    i = last_1min_time/100;
    prot.mis9_v2.time[0] = (i/10)*16+(i%10);  // 13:xx
    i = last_1min_time%100;
    prot.mis9_v2.time[1] = (i/10)*16+(i%10);  // xx:31
    StockMem[seq].time = CalTimetoTimeConvMinEx(BCD_to_Long(prot.mis9_v2.time, TIME_FSIZE));
    (MemPrice+seq)->tsec_deal = g_deal_price;
    StockMem[seq].deal_price = g_deal_price;
    t_sheet = g_deal_sheet - StockMem[seq].deal_sheet;
    StockMem[seq].price_amount = StockMem[seq].price_amount + ((double) (t_sheet * g_deal_price / nStkBaseValue));
    if((StockMem[seq].mkt == 1) && (StockMem[seq].type <= 80 && StockMem[seq].type > 0)){
        if(StockMem[seq].spec_fg & _T_NON_E_50) {
            TsecClass[TWIWAN_N50_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[TWIWAN_N50_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_EMP99) {
            TsecClass[TWIWAN_EMP99_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[TWIWAN_EMP99_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_50) {
            TsecClass[TWIWAN_50_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[TWIWAN_50_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_100) {
            TsecClass[TWIWAN_100_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[TWIWAN_100_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_101) {
            TsecClass[TWIWAN_101_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[TWIWAN_101_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_TEC) {
            TsecClass[TWIWAN_TEC_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[TWIWAN_TEC_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_TEI) {
            TsecClass[TWIWAN_TEI_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[TWIWAN_TEI_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_TDP) {
            TsecClass[TWIWAN_TDP_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[TWIWAN_TDP_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_FRMSA) {
            TsecClass[TWIWAN_FRMSA_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[TWIWAN_FRMSA_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TSEC_HC100) {
            TsecClass[TSEC_HC100_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[TSEC_HC100_CLASS].DealSheet += t_sheet;
        }
        TsecClass[StockMem[seq].type+13].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
        TsecClass[StockMem[seq].type+13].DealSheet += t_sheet;
    }
    else if(StockMem[seq].mkt == 2) {
        if(StockMem[seq].spec_fg & _T_OTC_50) {
            TsecClass[OTC_N50_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[OTC_N50_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _T_BOND_03) {
            TsecClass[OTC_BOND03_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[OTC_BOND03_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _T_OTC_GAME) {
            TsecClass[OTC_GAME_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[OTC_GAME_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _T_OTC_GTHD) {
            TsecClass[OTC_GTHD_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[OTC_GTHD_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _T_OTC_EMP88) {
            TsecClass[OTC_EMP88_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[OTC_EMP88_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _OTC_GTCI) {
            TsecClass[OTC_GTCI_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[OTC_GTCI_CLASS].DealSheet += t_sheet;
        }
        kind_id = OtcClassToKindIndex(StockMem[seq].type);
        if((kind_id >= 0) && (kind_id <= 40)) {
            OtcClass[kind_id].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            OtcClass[kind_id].DealSheet += t_sheet;
        }
    }
    if( g_deal_sheet > StockMem[seq].deal_sheet) { // && deal_sheet < 1000000L ) {
        StockMem[seq].deal_sheet = g_deal_sheet;
        StockMem[seq].field_fg |= _DEAL;
        MemTransferToMis2BinFmtAndSendEx(seq, StockMem[seq].field_fg);
        StockMem[seq].Mis2DealCount = 0;
    }
}

void IP_FixedPriceTradeUpdateToMemAndSend_V3(IP_FMT& prot, int seq)   //bm
{
    long t_sheet;
    int i;
    long tmp_time;

    tmp_time = BCD_to_Long(prot.mis9_v3.time, TIME_NOW_SIZE);   // 欄位長度是3，卻讀取2，確認是否有特殊原因
    g_deal_price = BCD_to_Long(prot.mis9_v3.deal_price, 5)/100;
    g_deal_sheet = BCD_to_Long(prot.mis9_v3.deal_sheet, 4);
    if (tmp_time == 0L) { // fixed price trade but without deal made
        return;
    }
    if (StockMem[seq].close1deal_sheet == 0) { // set up close1deal_sheet
        StockMem[seq].close1deal_sheet = StockMem[seq].deal_sheet;
    }
    g_deal_sheet += StockMem[seq].close1deal_sheet;

      // format time to be 13:31
    i = last_1min_time/100;
    prot.mis9_v3.time[0] = (i/10)*16+(i%10);  // 13:xx
    i = last_1min_time%100;
    prot.mis9_v3.time[1] = (i/10)*16+(i%10);  // xx:31
    StockMem[seq].time = CalTimetoTimeConvMinEx(BCD_to_Long(prot.mis9_v3.time, TIME_FSIZE));
    (MemPrice+seq)->tsec_deal = g_deal_price;
    StockMem[seq].deal_price = g_deal_price;
    t_sheet = g_deal_sheet - StockMem[seq].deal_sheet;
    StockMem[seq].price_amount = StockMem[seq].price_amount + ((double) (t_sheet * g_deal_price / nStkBaseValue));
    sum_to_indexes( seq, g_deal_price, t_sheet );
    if( g_deal_sheet > StockMem[seq].deal_sheet) { // && deal_sheet < 1000000L ) {
        StockMem[seq].deal_sheet = g_deal_sheet;
        StockMem[seq].field_fg |= _DEAL;
        MemTransferToMis2BinFmtAndSendEx(seq, StockMem[seq].field_fg);
        StockMem[seq].Mis2DealCount = 0;
    }
}

void IP_Mis2UpdateToMemAndSend_V3(const IP_FMT& prot, int seq)
{
    long temp, t_sheet;
    int i, tmp_cnt, kind_id;
    long tmp_time;

    //取出價量與買賣資訊 放入 deal_sheet, deal_price, time_sheet中
    if( !GetBCDMis2SubValue_V3(prot, prot.mis6_v3.field_fg, seq)) {
        return;
    }
    tmp_time = BCD_to_Long(prot.mis6_v3.time, TIME_FSIZE);
	gStat.last_mis_tick_time = tmp_time;
    if(tmp_time >= 133100)
        tmp_time = 133059;  //因應延後收盤機制..
    StockMem[seq].time = CalTimetoTimeConvMinEx(CutMrkTestTime(tmp_time, MK_TSEC));
    StockMem[seq].field_fg = prot.mis6_v3.field_fg;
    if(!(prot.mis6_v3.state & 0xE0))  { //非試算揭示
         if ( StockMem[seq].cmedj & 0x07) {
            (MemPrice+seq)->tsec_deal = StockMem[seq].prev_price;
            StockMem[seq].deal_price = StockMem[seq].prev_price;
            StockMem[seq].deal_sheet = StockMem[seq].prev_sheet;
         }
    }
    else {
         if( !(StockMem[seq].cmedj & 0x07)) {
             StockMem[seq].prev_price = StockMem[seq].deal_price;
             StockMem[seq].prev_sheet = StockMem[seq].deal_sheet;
         }
    }
    StockMem[seq].cmedj = prot.mis6_v3.state >> 5;
    if ( prot.mis6_v3.field_fg & _DEAL ) {
      (MemPrice+seq)->tsec_deal = g_deal_price;
      StockMem[seq].deal_price = g_deal_price;
      if(StockMem[seq].cmedj & 0x07) {
        StockMem[seq].deal_sheet = g_deal_sheet;
        if (mis_open[prot.mis6_v3.head.market-1] && NowSystemSec<(13*3600+24*60+50) && (prot.mis6_v3.state&0x40)==0) {
            return;
        }
      }
      else {
          mis_open[prot.mis6_v3.head.market-1] = 1;
        RefreshUpDownFg(seq);
        t_sheet = g_deal_sheet - StockMem[seq].deal_sheet;
        StockMem[seq].price_amount = StockMem[seq].price_amount + ((double) (t_sheet * g_deal_price / nStkBaseValue));
        if(StockMem[seq].mkt == 1 && (StockMem[seq].type <= 80 && StockMem[seq].type > 0)){
            if(StockMem[seq].spec_fg & _T_NON_E_50) {
                TsecClass[TWIWAN_N50_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_N50_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_EMP99) {
                TsecClass[TWIWAN_EMP99_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_EMP99_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_50) {
                TsecClass[TWIWAN_50_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_50_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_100) {
                TsecClass[TWIWAN_100_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_100_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_101) {
                TsecClass[TWIWAN_101_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_101_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_TEC) {
                TsecClass[TWIWAN_TEC_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_TEC_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_TEI) {
                TsecClass[TWIWAN_TEI_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_TEI_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_TDP) {
                TsecClass[TWIWAN_TDP_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_TDP_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_FRMSA) {
                TsecClass[TWIWAN_FRMSA_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_FRMSA_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TSEC_HC100) {
                TsecClass[TSEC_HC100_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TSEC_HC100_CLASS].DealSheet += t_sheet;
            }
                TsecClass[StockMem[seq].type+13].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[StockMem[seq].type+13].DealSheet += t_sheet;
        }
        else if(StockMem[seq].mkt == 2) {
            if(StockMem[seq].spec_fg & _T_OTC_50) {
                TsecClass[OTC_N50_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[OTC_N50_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _T_BOND_03) {
                TsecClass[OTC_BOND03_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[OTC_BOND03_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _T_OTC_GAME) {
                TsecClass[OTC_GAME_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[OTC_GAME_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _T_OTC_GTHD) {
                TsecClass[OTC_GTHD_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[OTC_GTHD_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _T_OTC_EMP88) {
                TsecClass[OTC_EMP88_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[OTC_EMP88_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _OTC_GTCI) {
                TsecClass[OTC_GTCI_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[OTC_GTCI_CLASS].DealSheet += t_sheet;
            }
            kind_id = OtcClassToKindIndex(StockMem[seq].type);
            if((kind_id >= 0) && (kind_id <= 40)) {
                OtcClass[kind_id].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                OtcClass[kind_id].DealSheet += t_sheet;
            }
        }
        if( g_deal_sheet > StockMem[seq].deal_sheet)
            StockMem[seq].index++;
        if( g_deal_sheet >= StockMem[seq].deal_sheet) {// && deal_sheet < 1000000L ) {
            StockMem[seq].deal_sheet = g_deal_sheet;
            StockMem[seq].Mis2DealCount = 0;
        }
        else {
            if( StockMem[seq].Mis2DealCount < 3 )
                StockMem[seq].Mis2DealCount++;
            else {
                StockMem[seq].deal_sheet = g_deal_sheet;
                StockMem[seq].Mis2DealCount = 0;
            }
        }
      }    
    }
    else {
        if ((StockMem[seq].cmedj & 0x07) && mis_open[prot.mis6_v3.head.market-1] && NowSystemSec<(13*3600+24*60+50) && (prot.mis6_v3.state&0x40)==0) {            
            char oldflag = StockMem[seq].warn_flag;
            StockMem[seq].warn_flag &= 0x1f;
            MemTransferToMis2BinFmtAndSendEx(seq, prot.mis6_v3.field_fg);
            StockMem[seq].warn_flag = oldflag;
            return;
        }        
    }
    MemTransferToMis2BinFmtAndSendEx(seq, prot.mis6_v3.field_fg);
}

// B.12 逐筆交易規格
void IP_Mis2UpdateToMemAndSend_V4(const IP_FMT& prot, int seq)
{
    long temp, t_sheet;
    int i, tmp_cnt, kind_id;
    long tmp_time;

    //取出價量與買賣資訊 放入 deal_sheet, deal_price, time_sheet中
    if( !GetBCDMis2SubValue_V4(prot, prot.mis6_v3.field_fg, seq)) {
        return;
    }        
    tmp_time = BCD_to_Long(prot.mis6_v3.time, TIME_FSIZE);
	gStat.last_mis_tick_time = tmp_time;
    if(tmp_time >= 133100)
        tmp_time = 133059;  //因應延後收盤機制..
    StockMem[seq].time = CalTimetoTimeConvMinEx(CutMrkTestTime(tmp_time, MK_TSEC));
    StockMem[seq].field_fg = prot.mis6_v3.field_fg;
    if(!(prot.mis6_v3.state & 0xE0))  { //非試算揭示
         if ( StockMem[seq].cmedj & 0x07) {
            (MemPrice+seq)->tsec_deal = StockMem[seq].prev_price;
            StockMem[seq].deal_price = StockMem[seq].prev_price;
            StockMem[seq].deal_sheet = StockMem[seq].prev_sheet;
         }
    }
    else {
         if( !(StockMem[seq].cmedj & 0x07)) {
             StockMem[seq].prev_price = StockMem[seq].deal_price;
             StockMem[seq].prev_sheet = StockMem[seq].deal_sheet;
         }
    }
	// bool remove_tick = false;
    StockMem[seq].cmedj = prot.mis6_v3.state >> 5;
    if ( prot.mis6_v3.field_fg & _DEAL ) {
      (MemPrice+seq)->tsec_deal = g_deal_price;
      StockMem[seq].deal_price = g_deal_price;
      if(StockMem[seq].cmedj & 0x07) {
        StockMem[seq].deal_sheet = g_deal_sheet;
        if (mis_open[prot.mis6_v3.head.market-1] && NowSystemSec<(13*3600+24*60+50) /*&& (prot.mis6_v3.state&0x40)==0*/) {
            //logf("0323: drop tick symbol=6%s, reason=sim tick", StockMem[seq],stock_no);
            //remove_tick = true;
			if (tmp_time<90200) {
				return;
			}
        }
      }
      else {
		  mis_open[prot.mis6_v3.head.market-1] = 1;
        RefreshUpDownFg(seq);
        t_sheet = g_deal_sheet - StockMem[seq].deal_sheet;
        StockMem[seq].price_amount = StockMem[seq].price_amount + ((double) (t_sheet * g_deal_price / nStkBaseValue));
        if(StockMem[seq].mkt == 1 && (StockMem[seq].type <= 80 && StockMem[seq].type > 0)){
            if(StockMem[seq].spec_fg & _T_NON_E_50) {
                TsecClass[TWIWAN_N50_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_N50_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_EMP99) {
                TsecClass[TWIWAN_EMP99_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_EMP99_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_50) {
                TsecClass[TWIWAN_50_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_50_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_100) {
                TsecClass[TWIWAN_100_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_100_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_101) {
                TsecClass[TWIWAN_101_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_101_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_TEC) {
                TsecClass[TWIWAN_TEC_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_TEC_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_TEI) {
                TsecClass[TWIWAN_TEI_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_TEI_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_TDP) {
                TsecClass[TWIWAN_TDP_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_TDP_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TWIWAN_FRMSA) {
                TsecClass[TWIWAN_FRMSA_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TWIWAN_FRMSA_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _TSEC_HC100) {
                TsecClass[TSEC_HC100_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[TSEC_HC100_CLASS].DealSheet += t_sheet;
            }
                TsecClass[StockMem[seq].type+13].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[StockMem[seq].type+13].DealSheet += t_sheet;
        }
        else if(StockMem[seq].mkt == 2) {
            if(StockMem[seq].spec_fg & _T_OTC_50) {
                TsecClass[OTC_N50_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[OTC_N50_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _T_BOND_03) {
                TsecClass[OTC_BOND03_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[OTC_BOND03_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _T_OTC_GAME) {
                TsecClass[OTC_GAME_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[OTC_GAME_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _T_OTC_GTHD) {
                TsecClass[OTC_GTHD_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[OTC_GTHD_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _T_OTC_EMP88) {
                TsecClass[OTC_EMP88_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[OTC_EMP88_CLASS].DealSheet += t_sheet;
            }
            if(StockMem[seq].spec_fg & _OTC_GTCI) {
                TsecClass[OTC_GTCI_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                TsecClass[OTC_GTCI_CLASS].DealSheet += t_sheet;
            }
            kind_id = OtcClassToKindIndex(StockMem[seq].type);
            if((kind_id >= 0) && (kind_id <= 40)) {
                OtcClass[kind_id].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
                OtcClass[kind_id].DealSheet += t_sheet;
            }
        }
        if( g_deal_sheet > StockMem[seq].deal_sheet)
            StockMem[seq].index++;
        if( g_deal_sheet >= StockMem[seq].deal_sheet) {// && deal_sheet < 1000000L ) {
            StockMem[seq].deal_sheet = g_deal_sheet;
            StockMem[seq].Mis2DealCount = 0;
        }
        else {
            if( StockMem[seq].Mis2DealCount < 3 )
                StockMem[seq].Mis2DealCount++;
            else {
                StockMem[seq].deal_sheet = g_deal_sheet;
                StockMem[seq].Mis2DealCount = 0;
            }
        }
      }    
    }
    // else {
        // if ((StockMem[seq].cmedj & 0x07) && mis_open[prot.mis6_v3.head.market-1] && NowSystemSec<(13*3600+24*60+50) && (prot.mis6_v3.state&0x40)==0) {
            // char oldflag = StockMem[seq].warn_flag;
            // StockMem[seq].warn_flag &= 0x1f;  //remove virtual flag
			// unsigned char old_pause_flag = StockMem[seq].updown_flag;
			// StockMem[seq].updown_flag &= 0xfc;
			// StockMem[seq].updown_flag |= last_pause_flag[seq];
            // MemTransferToMis2BinFmtAndSendEx(seq, prot.mis6_v3.field_fg);
            // StockMem[seq].warn_flag = oldflag;
			// StockMem[seq].updown_flag = old_pause_flag;
            // return;
        // }
    // }
	// if (remove_tick) {
        // if ((prot.mis6_v3.field_fg & 0x7e)==0) {
            // return;
        // }
            // char oldflag = StockMem[seq].warn_flag;
            // StockMem[seq].warn_flag &= 0x1f;  //remove virtual flag
			// unsigned char old_pause_flag = StockMem[seq].updown_flag;
			// StockMem[seq].updown_flag &= 0xfc;
			// StockMem[seq].updown_flag |= last_pause_flag[seq];
			// long oldtime = StockMem[seq].time;
			// StockMem[seq].time = last_pause_time[seq];
            // //Logf("0323: MemTransferToMis2_EXT_BinFmtEx_tick_removed, symbol=%6s, 0x%x", StockMem[seq].stock_no, prot.mis6_v3.field_fg );
		// MemTransferToMis2_EXT_BinFmtEx_tick_removed(seq, prot.mis6_v3.field_fg);
            // StockMem[seq].warn_flag = oldflag;
			// StockMem[seq].updown_flag = old_pause_flag;
			// StockMem[seq].time = oldtime;
	// }
	// else {
		MemTransferToMis2BinFmtAndSendEx(seq, prot.mis6_v3.field_fg);
	// }
}

void sum_to_indexes( int seq, long price, long t_sheet ) {
    if (StockMem[seq].mkt == 1 && (StockMem[seq].type <= 80 && StockMem[seq].type > 0)){
        if (StockMem[seq].spec_fg & _T_NON_E_50) {
            TsecClass[TWIWAN_N50_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[TWIWAN_N50_CLASS].DealSheet += t_sheet;
        }
        if (StockMem[seq].spec_fg & _TWIWAN_EMP99) {
            TsecClass[TWIWAN_EMP99_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[TWIWAN_EMP99_CLASS].DealSheet += t_sheet;
        }
        if (StockMem[seq].spec_fg & _TWIWAN_50) {
            TsecClass[TWIWAN_50_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[TWIWAN_50_CLASS].DealSheet += t_sheet;
        }
        if (StockMem[seq].spec_fg & _TWIWAN_100) {
            TsecClass[TWIWAN_100_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[TWIWAN_100_CLASS].DealSheet += t_sheet;
        }
        if (StockMem[seq].spec_fg & _TWIWAN_101) {
            TsecClass[TWIWAN_101_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[TWIWAN_101_CLASS].DealSheet += t_sheet;
        }
        if (StockMem[seq].spec_fg & _TWIWAN_TEC) {
            TsecClass[TWIWAN_TEC_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[TWIWAN_TEC_CLASS].DealSheet += t_sheet;
        }
        if (StockMem[seq].spec_fg & _TWIWAN_TEI) {
            TsecClass[TWIWAN_TEI_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[TWIWAN_TEI_CLASS].DealSheet += t_sheet;
        }
        if (StockMem[seq].spec_fg & _TWIWAN_TDP) {
            TsecClass[TWIWAN_TDP_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[TWIWAN_TDP_CLASS].DealSheet += t_sheet;
        }
        if (StockMem[seq].spec_fg & _TWIWAN_FRMSA) {
            TsecClass[TWIWAN_FRMSA_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[TWIWAN_FRMSA_CLASS].DealSheet += t_sheet;
        }
        if (StockMem[seq].spec_fg & _TSEC_HC100) {
            TsecClass[TSEC_HC100_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[TSEC_HC100_CLASS].DealSheet += t_sheet;
        }
        TsecClass[StockMem[seq].type+13].Val += ((double)(t_sheet * price / nStkBaseValue));
        TsecClass[StockMem[seq].type+13].DealSheet += t_sheet;
    }
    else if(StockMem[seq].mkt == 2) {
        if(StockMem[seq].spec_fg & _T_OTC_50) {
            TsecClass[OTC_N50_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[OTC_N50_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _T_BOND_03) {
            TsecClass[OTC_BOND03_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[OTC_BOND03_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _T_OTC_GAME) {
            TsecClass[OTC_GAME_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[OTC_GAME_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _T_OTC_GTHD) {
            TsecClass[OTC_GTHD_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[OTC_GTHD_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _T_OTC_EMP88) {
            TsecClass[OTC_EMP88_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[OTC_EMP88_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _OTC_GTCI) {
            TsecClass[OTC_GTCI_CLASS].Val += ((double)(t_sheet * price / nStkBaseValue));
            TsecClass[OTC_GTCI_CLASS].DealSheet += t_sheet;
        }
        int kind_id = OtcClassToKindIndex(StockMem[seq].type);
        if ((kind_id >= 0) && (kind_id <= 40)) {
            OtcClass[kind_id].Val += ((double)(t_sheet * price / nStkBaseValue));
            OtcClass[kind_id].DealSheet += t_sheet;
        }
    }

}

void on_mis20_v1(IP_FMT& prot) {
    int fg_WriteStable = 0;
    int fg_WriteDelayClose = 0;
    StartReceOtc = 1;
    fix_mis20_pre_total_volume(prot);            //修正盤前試撮合的總量,以便符合tick規格的定義
    int toyo_seq = SearchToyoNumber(prot.mis20_v1.stock_no);
    if (!fg_Open) {
        fg_Open =1;
    }
    if (toyo_seq <= 0) {
        return;
    }          
    if (prot.mis20_v1.up_down & 0x03) {  //瞬間價格趨勢
        fg_WriteStable = 1;
        StockMem[toyo_seq].updown_flag |= ((prot.mis20_v1.up_down & 0x03));
    }
    else {
        if (StockMem[toyo_seq].updown_flag & 0x03) {
            fg_WriteStable = 1;
            StockMem[toyo_seq].updown_flag &= ~(0x03);
        }
    }          
    if ((prot.mis20_v1.state & BIT7) == BIT7) {  //試算揭示             
        if ((prot.mis20_v1.state & BIT5) == BIT5) {  //試算後延後收盤               
            if( (StockMem[toyo_seq].warn_flag & BIT5) != BIT5) {     //之前的狀態非試算後延後收盤 起動新聞flag
                fg_WriteDelayClose = 1;
            }
        }
    }
    StockMem[toyo_seq].warn_flag = (prot.mis20_v1.state & 0xf0);

    if ( !read_mis20_v1_tail(prot, toyo_seq)) {
        return;
    }        
    long tmp_time = BCD_to_Long(prot.mis20_v1.time, TIME_FSIZE);
	gStat.last_mis_tick_time = tmp_time;
    if (tmp_time >= 133100) {
        tmp_time = 133059;  //因應延後收盤機制..
    }
    StockMem[toyo_seq].time = CalTimetoTimeConvMinEx(CutMrkTestTime(tmp_time, MK_TSEC));
    StockMem[toyo_seq].field_fg = prot.mis20_v1.field_fg;
    if (!(prot.mis20_v1.state & 0xE0)) { //非試算揭示, 一般tick
        if ( StockMem[toyo_seq].cmedj & 0x07) {   // 前一次是試搓合
            (MemPrice+toyo_seq)->tsec_deal = StockMem[toyo_seq].prev_price;
            StockMem[toyo_seq].deal_price = StockMem[toyo_seq].prev_price;
            StockMem[toyo_seq].deal_sheet = StockMem[toyo_seq].prev_sheet;
        }
    }
    else {  // 試搓合or延後開收盤
        if( !(StockMem[toyo_seq].cmedj & 0x07)) {  // 前一次是一般tick
            StockMem[toyo_seq].prev_price = StockMem[toyo_seq].deal_price;
            StockMem[toyo_seq].prev_sheet = StockMem[toyo_seq].deal_sheet;
        }
    }
    StockMem[toyo_seq].cmedj = prot.mis20_v1.state >> 5;
    if ( prot.mis20_v1.field_fg & _DEAL ) {
        (MemPrice+toyo_seq)->tsec_deal = g_deal_price;
        StockMem[toyo_seq].deal_price = g_deal_price;
        if(StockMem[toyo_seq].cmedj & 0x07) {
            StockMem[toyo_seq].deal_sheet = g_deal_sheet;
            if (mis_open[prot.mis6_v3.head.market-1] && NowSystemSec<(13*3600+24*60+50) && (prot.mis6_v3.state&0x40)==0) {
                return;
            }            
        }
        else {
            mis_open[prot.mis6_v3.head.market-1] = 1;
            RefreshUpDownFg(toyo_seq);
            long t_sheet = g_deal_sheet - StockMem[toyo_seq].deal_sheet;
            StockMem[toyo_seq].price_amount = StockMem[toyo_seq].price_amount + ((double) (t_sheet * g_deal_price / nStkBaseValue));
            sum_to_indexes( toyo_seq, g_deal_price, t_sheet );
            if ( g_deal_sheet > StockMem[toyo_seq].deal_sheet) {
                StockMem[toyo_seq].index++;
            }
            if ( g_deal_sheet >= StockMem[toyo_seq].deal_sheet) {
                StockMem[toyo_seq].deal_sheet = g_deal_sheet;
                StockMem[toyo_seq].Mis2DealCount = 0;
            }
            else {
                if ( StockMem[toyo_seq].Mis2DealCount < 3 ) {
                    StockMem[toyo_seq].Mis2DealCount++;
                }
                else {
                    StockMem[toyo_seq].deal_sheet = g_deal_sheet;
                    StockMem[toyo_seq].Mis2DealCount = 0;
                }
            }
        }    
    }
    else {
        if (mis_open[prot.mis6_v3.head.market-1] && NowSystemSec<(13*3600+24*60+50) && (prot.mis6_v3.state&0x40)==0) {            
            char oldflag = StockMem[toyo_seq].warn_flag;
            StockMem[toyo_seq].warn_flag &= 0x1f;
            MemTransferToMis2BinFmtAndSendEx(toyo_seq, prot.mis6_v3.field_fg);
            StockMem[toyo_seq].warn_flag = oldflag;
            return;
        }                
    }
    // if exchange not open and packet_open!=packet_last_price, send open tick first
    // if packet_high>mem_high and packet_high!=packet_last_price
    MemTransferToMis2BinFmtAndSendEx(toyo_seq, prot.mis20_v1.field_fg);
    if (fg_WriteStable && fg_stable_file) {
        WriteStableStockFile();
    }
    if (fg_WarrInfoNews && fg_WriteDelayClose) {
        WriteDelayCloseFile();
    }    
}

void MemTransferToMis2BinFmtAndSendEx(int seq, uchar field)
{
    MemTransferToMis2_EXT_BinFmtEx(seq, field);
}

void MemTransferToMis2_EXT_BinFmtEx(int seq, uchar field)
{
    int   i;
    char  CheckSum;
    char  *_ptr;
    int   offset;
    int   buy_num, sell_num;
    BINFMT bp;
    memset(bp.buf, 0, sizeof(bp.buf));
    bp.i_mis2.esc = ESC;
    bp.i_mis2.mis = 0xA4;
    bp.i_mis2.stock_no = seq;
    bp.i_mis2.fg.b.bit5 = ComparePrice(StockMem[seq].time) ? 1 : 0;
    bp.i_mis2.sec = comp_price;
    if ((StockMem[seq].warn_flag & BIT7)) {
        bp.i_mis2.fg.b.bit2 = 1;
        if(StockMem[seq].warn_flag & BIT6)
            bp.i_mis2.fg.b.bit1 = 1;
        if(StockMem[seq].warn_flag & BIT5)
            bp.i_mis2.fg.b.bit0 = 1;
    }
    else if (StockMem[seq].updown_flag & 0x02) {
        bp.i_mis2.fg.b.bit6 = 0;            /* Up */
        bp.i_mis2.fg.b.bit7 = 1;
    }
    else if (StockMem[seq].updown_flag & 0x01) {
        bp.i_mis2.fg.b.bit6 = 1;            /* Down */
        bp.i_mis2.fg.b.bit7 = 0;
    }
    else {
        bp.i_mis2.fg.b.bit6 = 0;            /* None */
        bp.i_mis2.fg.b.bit7 = 0;
    }
    if (field & _DEAL) {
        bp.i_mis2.fg.b.bit4 = 1;
    }
    else {
        bp.i_mis2.fg.b.bit4 = 0;
    }
    if ((field & _BS_UPDATE) && WarrNewMis1_fg) {
        bp.i_mis2.fg.b.bit3 = 1;
    }
    else {
        bp.i_mis2.fg.b.bit3 = 0;
    }
    _ptr = &bp.buf[BIN_IP_MIS2_SIZE];
    offset = 0;
    if (field & _DEAL)  {
        memcpy( _ptr+offset, &StockMem[seq].deal_price, 3 );
        offset += 3;
        memcpy( _ptr+offset, &StockMem[seq].deal_sheet, 3 );
        offset += 3;
    }
    if ( !(field & _BS_UPDATE))  {
        buy_num = ((field & _BUY_PRICE_SHEET) >> 4);
        for (i=0; i<buy_num; i++) {
            memcpy( _ptr+offset, &StockMem[seq].buy_price[i], 3 );
            offset += 3;
            memcpy( _ptr+offset, &StockMem[seq].buy_sheet[i], 3 );
            offset += 3;
        }
        sell_num = ((field & _SELL_PRICE_SHEET) >> 1);
        for (i=0; i<sell_num; i++) {
            memcpy( _ptr+offset, &StockMem[seq].sell_price[i], 3 );
            offset += 3;
            memcpy( _ptr+offset, &StockMem[seq].sell_sheet[i], 3 );
            offset += 3;
        }
        bp.i_mis2.field_fg.u = (buy_num << 4)|sell_num;
    }
    else if ( !WarrNewMis1_fg) {
        buy_num = ((StockMem[seq].field_fg & _BUY_PRICE_SHEET) >> 4);
        for (i=0; i<buy_num; i++) {
            memcpy( _ptr+offset, &StockMem[seq].buy_price[i], 3 );
            offset += 3;
            memcpy( _ptr+offset, &StockMem[seq].buy_sheet[i], 3 );
            offset += 3;
        }
        sell_num = ((StockMem[seq].field_fg & _SELL_PRICE_SHEET) >> 1);
        for (i=0; i<sell_num; i++) {
            memcpy( _ptr+offset, &StockMem[seq].sell_price[i], 3 );
            offset += 3;
            memcpy( _ptr+offset, &StockMem[seq].sell_sheet[i], 3 );
            offset += 3;
        }
        bp.i_mis2.field_fg.u = (buy_num << 4)|sell_num;
    }
    CheckSum = 0;
    for ( i=0 ; i< BIN_IP_MIS2_SIZE-1; i++ ) {
        CheckSum ^= bp.buf[i];
    }
    bp.buf[BIN_IP_MIS2_SIZE - 1] = CheckSum;
    offset++;
    CheckSum=0;
    for ( i=0 ; i< offset -1  ; i++ ) {
        CheckSum ^= bp.buf[i + BIN_IP_MIS2_SIZE];
    }
    bp.buf[BIN_IP_MIS2_SIZE + offset -1] = CheckSum;
    CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_MIS2_SIZE + offset, 0);
}

void MemTransferToMis2_EXT_BinFmtEx_tick_removed(int seq, uchar field)
{
    int   i;
    char  CheckSum;
    char  *_ptr;
    int   offset;
    int   buy_num, sell_num;
    BINFMT bp;
    memset(bp.buf, 0, sizeof(bp.buf));
    bp.i_mis2.esc = ESC;
    bp.i_mis2.mis = 0xA4;
    bp.i_mis2.stock_no = seq;
    bp.i_mis2.fg.b.bit5 = ComparePrice(StockMem[seq].time) ? 1 : 0;
    bp.i_mis2.sec = comp_price;
    if ((StockMem[seq].warn_flag & BIT7)) {
        bp.i_mis2.fg.b.bit2 = 1;
        if(StockMem[seq].warn_flag & BIT6)
            bp.i_mis2.fg.b.bit1 = 1;
        if(StockMem[seq].warn_flag & BIT5)
            bp.i_mis2.fg.b.bit0 = 1;
    }
    else if (StockMem[seq].updown_flag & 0x02) {
        bp.i_mis2.fg.b.bit6 = 0;            /* Up */
        bp.i_mis2.fg.b.bit7 = 1;
    }
    else if (StockMem[seq].updown_flag & 0x01) {
        bp.i_mis2.fg.b.bit6 = 1;            /* Down */
        bp.i_mis2.fg.b.bit7 = 0;
    }
    else {
        bp.i_mis2.fg.b.bit6 = 0;            /* None */
        bp.i_mis2.fg.b.bit7 = 0;
    }

	bp.i_mis2.fg.b.bit4 = 0;

	//Logf("0323: symbol=%6s, field=0x%x", StockMem[seq].stock_no, field);
    if (field & 0x7e) {
        bp.i_mis2.fg.b.bit3 = 0;
    }
    _ptr = &bp.buf[BIN_IP_MIS2_SIZE];
    offset = 0;

    if (field & 0x7e)  {
        buy_num = ((field & _BUY_PRICE_SHEET) >> 4);
        for (i=0; i<buy_num; i++) {
            memcpy( _ptr+offset, &StockMem[seq].buy_price[i], 3 );
            offset += 3;
            memcpy( _ptr+offset, &StockMem[seq].buy_sheet[i], 3 );
            offset += 3;
        }
        sell_num = ((field & _SELL_PRICE_SHEET) >> 1);
        for (i=0; i<sell_num; i++) {
            memcpy( _ptr+offset, &StockMem[seq].sell_price[i], 3 );
            offset += 3;
            memcpy( _ptr+offset, &StockMem[seq].sell_sheet[i], 3 );
            offset += 3;
        }
        bp.i_mis2.field_fg.u = (buy_num << 4)|sell_num;
		//Logf("MemTransferToMis2_EXT_BinFmtEx_tick_removed: bp.i_mis2.field_fg=0x%x", bp.i_mis2.field_fg.u );
    }
    CheckSum = 0;
    for ( i=0 ; i< BIN_IP_MIS2_SIZE-1; i++ ) {
        CheckSum ^= bp.buf[i];
    }
    bp.buf[BIN_IP_MIS2_SIZE - 1] = CheckSum;
    offset++;
    CheckSum=0;
    for ( i=0 ; i< offset -1  ; i++ ) {
        CheckSum ^= bp.buf[i + BIN_IP_MIS2_SIZE];
    }
    bp.buf[BIN_IP_MIS2_SIZE + offset -1] = CheckSum;
    CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_MIS2_SIZE + offset, 0);
}

int GetIndex(long idx_time)
{
    int idx;

    if(idx_time<900) return 0;

    idx=(idx_time-900)/5;
    return idx;
}

// 寫 sequence file to tsec.seq
void write_tsec_seq(int market)
{
    FILE *flog;
    int i;
    long yday,up,down,aaa;
    char msg[64];

    if(market == MK_TSEC)
        flog = fopen("tsec.seq","w");
    else if(market == MK_OTC)
        flog = fopen("otc.seq","w");
    for(i=0; i<max_TotalStockNo; i++){
        fprintf(flog,"%6.6s  %04d\n", stock_ndx[market - 1][i].stock,stock_ndx[market - 1][i].tsec_seq);
    }
    fclose(flog);
}
void send_otc_15sec_index(int type, int index)
{
    int w_time, i;
    long tmp;
    static int tick_cnt=0;

    if ((OtcTime_15.close_trade == 2) || (OtcTime_15.IndexTime > 133015)) {
        w_time = 48660;  // 13:31    kevin
        if(OtcTime_15.close_trade == 2) {
            if(tick_cnt <= 3)
                tick_cnt++;
            else
                return;
        }
    }
    else
        w_time = ((TsecTime_15.IndexTime/10000 * 60) + (TsecTime_15.IndexTime % 10000)/100) *60+TsecTime_15.IndexTime % 100;
    if (type == 1) {   /* send out all 30 indices */
        if (w_time < 32400) {
            if(otc_index_seq > 0) {
                tmp = OtcClassYesIndex[0];
                if(tmp > 0l) {
                    StockMem[otc_index_seq].y_close = tmp;
                    StockMem[otc_index_seq].up_bound = tmp*(100+UP_DOWN_BOUND)/100;
                    StockMem[otc_index_seq].dn_bound = tmp*(100-UP_DOWN_BOUND)/100;
                    MemTransferToNewMis1BinFmtAndSend(otc_index_seq);
                }
            }
        }
        for (i=0; i<otc_class_total; i++) {
            if (otc_1min_idx_seq[i] == -1)
                continue;
            if (w_time < 32400)  {// send out yesterday close
                tmp = OtcClassYesIndex[i];
                StockMem[otc_1min_idx_seq[i]].y_close = tmp;
                StockMem[otc_1min_idx_seq[i]].up_bound = tmp*(100+UP_DOWN_BOUND)/100;
                StockMem[otc_1min_idx_seq[i]].dn_bound = tmp*(100-UP_DOWN_BOUND)/100;
                if (StockMem[otc_1min_idx_seq[i]].y_close <= 0l)
                    continue;
                MemTransferToNewMis1BinFmtAndSend(otc_1min_idx_seq[i]);
            }
            else if (w_time != 32400) {// send out deal price
                tmp = OtcClassIndex[i];
                StockMem[otc_1min_idx_seq[i]].deal_price = tmp;
                StockMem[otc_1min_idx_seq[i]].deal_sheet = (i==0)?Otc9995.deal_amount:OtcClass[i].Val/nInxBaseValue;
                StockMem[otc_1min_idx_seq[i]].time = w_time;
                if (StockMem[otc_1min_idx_seq[i]].deal_price <= 0l)
                    continue;
                MemTransferToMis2BinFmtAndSendEx(otc_1min_idx_seq[i], _DEAL);
           }
        }
    } /* end of if type==1 */
    else if (type == 2) {  /* type==2, send out only "index" */
        if(( FixedPriceTrade[ 1 ].Ok)) {
            for (i=0; i<otc_class_total; i++) {
                if (otc_1min_idx_seq[i] == -1)
                    continue;
                tmp = OtcClassIndex[i];
                StockMem[otc_1min_idx_seq[i]].deal_price = tmp;
                StockMem[otc_1min_idx_seq[i]].deal_sheet = (i==0)?Otc9995.deal_amount:OtcClass[i].Val/nInxBaseValue;
                StockMem[otc_1min_idx_seq[i]].time = w_time;
                if (StockMem[otc_1min_idx_seq[i]].deal_price <= 0l)
                    continue;
                MemTransferToMis2BinFmtAndSendEx(otc_1min_idx_seq[i], _DEAL);
            }
        }
        if (otc_index_seq == -1)
            return;
        if (w_time < 32400)  {// send out yesterday close
            tmp = OtcClassYesIndex[0];
            StockMem[otc_index_seq].y_close = tmp;
            StockMem[otc_index_seq].up_bound = tmp*(100+UP_DOWN_BOUND)/100;
            StockMem[otc_index_seq].dn_bound = tmp*(100-UP_DOWN_BOUND)/100;
            MemTransferToNewMis1BinFmtAndSend(otc_index_seq);
        }
        else  if (w_time != 32400)  {// send out deal price
            tmp = OtcClassIndex[0];
            StockMem[otc_index_seq].deal_price = tmp;
            StockMem[otc_index_seq].deal_sheet = (index==0)?Otc9995.deal_amount:0;
            StockMem[otc_index_seq].time = w_time;
            MemTransferToMis2BinFmtAndSendEx(otc_index_seq, _DEAL);
        }
    } /* end of else if type==2 */
}
void send_otc_1min_index(int type, int index)
{
    int w_time, i;
    long tmp;
    static int tick_cnt=0;

    if ((OtcTime.close_trade == 2) || (OtcTime.IndexTime > 1331)) {
        w_time = 48660;  // 13:31    kevin
        if(OtcTime.close_trade == 2) {
            if(tick_cnt <= 3)
                tick_cnt++;
            else
                return;
        }
    }
    else
        w_time = ((OtcTime.IndexTime / 100*60) + OtcTime.IndexTime % 100) *60;

    if (type == 1) {   /* send out all 30 indices */
        if (w_time < 32400) {
            if(otc_index_seq > 0) {
                tmp = OtcClassYesIndex[0];
                if(tmp > 0l) {
                    StockMem[otc_index_seq].y_close = tmp;
                    StockMem[otc_index_seq].up_bound = tmp*(100+UP_DOWN_BOUND)/100;
                    StockMem[otc_index_seq].dn_bound = tmp*(100-UP_DOWN_BOUND)/100;
                    MemTransferToNewMis1BinFmtAndSend(otc_index_seq);
                }
            }
        }
        for (i=0; i<otc_class_total; i++) {
            if (otc_1min_idx_seq[i] == -1)
                continue;
            if (w_time < 32400)  {// send out yesterday close
                tmp = OtcClassYesIndex[i];
                StockMem[otc_1min_idx_seq[i]].y_close = tmp;
                StockMem[otc_1min_idx_seq[i]].up_bound = tmp*(100+UP_DOWN_BOUND)/100;
                StockMem[otc_1min_idx_seq[i]].dn_bound = tmp*(100-UP_DOWN_BOUND)/100;
                if (StockMem[otc_1min_idx_seq[i]].y_close <= 0l)
                    continue;
                MemTransferToNewMis1BinFmtAndSend(otc_1min_idx_seq[i]);
            }
            else if (w_time != 32400) {// send out deal price
                tmp = OtcClassIndex[i];
                StockMem[otc_1min_idx_seq[i]].deal_price = tmp;
                StockMem[otc_1min_idx_seq[i]].deal_sheet = (i==0)?Otc9995.deal_amount:OtcClass[i].Val/nInxBaseValue;
                StockMem[otc_1min_idx_seq[i]].time = w_time;
                if (StockMem[otc_1min_idx_seq[i]].deal_price <= 0l)
                    continue;
                MemTransferToMis2BinFmtAndSendEx(otc_1min_idx_seq[i], _DEAL);
           }
        }
    } /* end of if type==1 */
    else if (type == 2) {  /* type==2, send out only "index" */
        if(( FixedPriceTrade[ 1 ].Ok)) {
            for (i=0; i<otc_class_total; i++) {
                if (otc_1min_idx_seq[i] == -1)
                    continue;
                tmp = OtcClassIndex[i];
                StockMem[otc_1min_idx_seq[i]].deal_price = tmp;
                StockMem[otc_1min_idx_seq[i]].deal_sheet = (i==0)?Otc9995.deal_amount:OtcClass[i].Val/nInxBaseValue;
                StockMem[otc_1min_idx_seq[i]].time = w_time;
                if (StockMem[otc_1min_idx_seq[i]].deal_price <= 0l)
                    continue;
                MemTransferToMis2BinFmtAndSendEx(otc_1min_idx_seq[i], _DEAL);
            }
        }
        if (otc_index_seq == -1)
            return;
        if (w_time < 32400)  {// send out yesterday close
            tmp = OtcClassYesIndex[0];
            StockMem[otc_index_seq].y_close = tmp;
            StockMem[otc_index_seq].up_bound = tmp*(100+UP_DOWN_BOUND)/100;
            StockMem[otc_index_seq].dn_bound = tmp*(100-UP_DOWN_BOUND)/100;
            MemTransferToNewMis1BinFmtAndSend(otc_index_seq);
        }
        else  if (w_time != 32400)  {// send out deal price
            tmp = OtcClassIndex[0];
            StockMem[otc_index_seq].deal_price = tmp;
            StockMem[otc_index_seq].deal_sheet = (index==0)?Otc9995.deal_amount:0;
            StockMem[otc_index_seq].time = w_time;
            MemTransferToMis2BinFmtAndSendEx(otc_index_seq, _DEAL);
        }
    } /* end of else if type==2 */
}

void send_15_sec_index(int type)
{
    long w_time,i;
    static int tick_cnt=0;

    if (tsec_index_seq==-1)
        return ;
    if ((TsecTime_15.close_trade == 2) || (TsecTime_15.IndexTime > 133015)) {
        w_time = 48660;  // 13:31    kevin
        if(TsecTime_15.close_trade == 2) {
            if(tick_cnt <= 3)
                tick_cnt++;
            else
                return;
        }
    }
    else //if (IndexTime != 9999)
        w_time = ((TsecTime_15.IndexTime/10000 * 60) + (TsecTime_15.IndexTime % 10000)/100)*60+TsecTime_15.IndexTime % 100;
    if (w_time < 32400){
          StockMem[tsec_index_seq].y_close = TsecClassYesIndex[TOTAL_INDEX];
          StockMem[tsec_index_seq].up_bound = (TsecClassYesIndex[TOTAL_INDEX] * (100+UP_DOWN_BOUND) )/100;
          StockMem[tsec_index_seq].dn_bound = (TsecClassYesIndex[TOTAL_INDEX] * (100-UP_DOWN_BOUND) )/100;
          MemTransferToNewMis1BinFmtAndSend(tsec_index_seq );
          if (tsec_unindex_seq!=-1){
            StockMem[tsec_unindex_seq].y_close = TsecClassYesIndex[TSEC_NOBANK_INDEX];
            StockMem[tsec_unindex_seq].up_bound = (TsecClassYesIndex[TSEC_NOBANK_INDEX] * (100+UP_DOWN_BOUND) )/100;
            StockMem[tsec_unindex_seq].dn_bound = (TsecClassYesIndex[TSEC_NOBANK_INDEX] * (100-UP_DOWN_BOUND) )/100;
            MemTransferToNewMis1BinFmtAndSend(tsec_unindex_seq );
            }
          if (simsci_index_seq !=-1){
            StockMem[simsci_index_seq].y_close = TsecClassYesIndex[TSEC_NOELEC_INDEX];
            StockMem[simsci_index_seq].up_bound = (TsecClassYesIndex[TSEC_NOELEC_INDEX] * (100+UP_DOWN_BOUND) )/100;
            StockMem[simsci_index_seq].dn_bound = (TsecClassYesIndex[TSEC_NOELEC_INDEX] * (100-UP_DOWN_BOUND) )/100;
            MemTransferToNewMis1BinFmtAndSend(simsci_index_seq);
            }
          for(i=0; i < tsec_class_total; i++){
             if (tsec_index20_seq[i] <= 0)
                continue;
             if(gMisVer  && fg_Richv710)  {
                 StockMem[tsec_index20_seq[i]] .y_close = TsecClassYesIndex[TSEC_NEW_CLASS_INDEX + i];
                 StockMem[tsec_index20_seq[i]] .up_bound = (TsecClassYesIndex[TSEC_NEW_CLASS_INDEX + i]*(100+UP_DOWN_BOUND) )/100;
                 StockMem[tsec_index20_seq[i]] .dn_bound = (TsecClassYesIndex[TSEC_NEW_CLASS_INDEX + i]*(100-UP_DOWN_BOUND) )/100;
             }
             else {
                 StockMem[tsec_index20_seq[i]] .y_close = TsecClassYesIndex[TSEC_CLASS_20_INDEX + i];
                 StockMem[tsec_index20_seq[i]] .up_bound = (TsecClassYesIndex[TSEC_CLASS_20_INDEX + i]*(100+UP_DOWN_BOUND) )/100;
                 StockMem[tsec_index20_seq[i]] .dn_bound = (TsecClassYesIndex[TSEC_CLASS_20_INDEX + i]*(100-UP_DOWN_BOUND) )/100;
             }
             if (StockMem[tsec_index20_seq[i]].y_close <= 0l)
                continue;
             MemTransferToNewMis1BinFmtAndSend(tsec_index20_seq[i] );
             }
    }
//----------------- update today index and send -------------
    else if (w_time != 32400)  {
          if( !TsecClassIndex[TOTAL_INDEX])
                return;
          StockMem[tsec_index_seq].deal_price=TsecClassIndex[TOTAL_INDEX];
          StockMem[tsec_index_seq].deal_sheet=Tsec9995.deal_amount;
          StockMem[tsec_index_seq].time = w_time;
          MemTransferToMis2BinFmtAndSendEx(tsec_index_seq, _DEAL);
          if((type == 2) && ( !FixedPriceTrade[ 0 ].Ok)) return;
          if (tsec_unindex_seq!=-1){
             StockMem[tsec_unindex_seq].deal_price = TsecClassIndex[TSEC_NOBANK_INDEX];
             StockMem[tsec_unindex_seq].deal_sheet = TsecClass[1].Val/nInxBaseValue;
             StockMem[tsec_unindex_seq].time = w_time;
             MemTransferToMis2BinFmtAndSendEx(tsec_unindex_seq, _DEAL);
          }
          if (simsci_index_seq!=-1){
             StockMem[simsci_index_seq].deal_price = TsecClassIndex[TSEC_NOELEC_INDEX];
             StockMem[simsci_index_seq].deal_sheet = TsecClass[2].Val/nInxBaseValue;
             StockMem[simsci_index_seq].time = w_time;
             MemTransferToMis2BinFmtAndSendEx(simsci_index_seq, _DEAL);
          }
          for(i=0; i<tsec_class_total; i++){
              if (tsec_index20_seq[i] <= 0)
                 continue;
              if(gMisVer  && fg_Richv710)  {
                 StockMem[tsec_index20_seq[i]].deal_price=TsecClassIndex[TSEC_NEW_CLASS_INDEX + i];
                 if(i < 2) { // 化學&生技
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[i+34].Val/nInxBaseValue;
                 }
                 else if(i < 29) { //水泥到百貨
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[i+3].Val/nInxBaseValue;
                 }
                 else if(i < 30) { //其它指
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[i+4].Val/nInxBaseValue;
                 }
                 else if(i < 31) { //無金電
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[99].Val/nInxBaseValue;
                 }
                 else  { //油電至其它電
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[i+5].Val/nInxBaseValue;
                 }
              }
              else {
                 StockMem[tsec_index20_seq[i]].deal_price=TsecClassIndex[TSEC_CLASS_20_INDEX + i];
                 if(i>=18)
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[i+15].Val/nInxBaseValue;
                 else
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[i+14].Val/nInxBaseValue;
              }
              StockMem[tsec_index20_seq[i]].time = w_time;
              if (StockMem[tsec_index20_seq[i]].deal_price <= 0l)
                continue;
              MemTransferToMis2BinFmtAndSendEx(tsec_index20_seq[i], _DEAL);
          }
    }
}

void send_one_min_index(int type)
{
    long w_time,i;
    static int tick_cnt=0;

    if (tsec_index_seq==-1)
        return ;
    if ((TsecTime.close_trade == 2) || (TsecTime.IndexTime > 1331)) {
        w_time = 48660;  // 13:31    kevin
        if(TsecTime.close_trade == 2) {
            if(tick_cnt <= 3)
                tick_cnt++;
            else
                return;
        }
    }
    else //if (IndexTime != 9999)
        w_time = ((TsecTime.IndexTime/100 * 60) + TsecTime.IndexTime % 100) *60;
    if (w_time < 32400){
          StockMem[tsec_index_seq].y_close = TsecClassYesIndex[TOTAL_INDEX];
          StockMem[tsec_index_seq].up_bound = (TsecClassYesIndex[TOTAL_INDEX] * (100+UP_DOWN_BOUND) )/100;
          StockMem[tsec_index_seq].dn_bound = (TsecClassYesIndex[TOTAL_INDEX] * (100-UP_DOWN_BOUND) )/100;
          MemTransferToNewMis1BinFmtAndSend(tsec_index_seq );
          if (tsec_unindex_seq!=-1){
            StockMem[tsec_unindex_seq].y_close = TsecClassYesIndex[TSEC_NOBANK_INDEX];
            StockMem[tsec_unindex_seq].up_bound = (TsecClassYesIndex[TSEC_NOBANK_INDEX] * (100+UP_DOWN_BOUND) )/100;
            StockMem[tsec_unindex_seq].dn_bound = (TsecClassYesIndex[TSEC_NOBANK_INDEX] * (100-UP_DOWN_BOUND) )/100;
            MemTransferToNewMis1BinFmtAndSend(tsec_unindex_seq );
            }
          if (simsci_index_seq !=-1){
            StockMem[simsci_index_seq].y_close = TsecClassYesIndex[TSEC_NOELEC_INDEX];
            StockMem[simsci_index_seq].up_bound = (TsecClassYesIndex[TSEC_NOELEC_INDEX] * (100+UP_DOWN_BOUND) )/100;
            StockMem[simsci_index_seq].dn_bound = (TsecClassYesIndex[TSEC_NOELEC_INDEX] * (100-UP_DOWN_BOUND) )/100;
            MemTransferToNewMis1BinFmtAndSend(simsci_index_seq);
            }
          for(i=0; i < tsec_class_total; i++){
             if (tsec_index20_seq[i] <= 0)
                continue;
             if(gMisVer  && fg_Richv710)  {
                 StockMem[tsec_index20_seq[i]] .y_close = TsecClassYesIndex[TSEC_NEW_CLASS_INDEX + i];
                 StockMem[tsec_index20_seq[i]] .up_bound = (TsecClassYesIndex[TSEC_NEW_CLASS_INDEX + i]*(100+UP_DOWN_BOUND) )/100;
                 StockMem[tsec_index20_seq[i]] .dn_bound = (TsecClassYesIndex[TSEC_NEW_CLASS_INDEX + i]*(100-UP_DOWN_BOUND) )/100;
             }
             else {
                 StockMem[tsec_index20_seq[i]] .y_close = TsecClassYesIndex[TSEC_CLASS_20_INDEX + i];
                 StockMem[tsec_index20_seq[i]] .up_bound = (TsecClassYesIndex[TSEC_CLASS_20_INDEX + i]*(100+UP_DOWN_BOUND) )/100;
                 StockMem[tsec_index20_seq[i]] .dn_bound = (TsecClassYesIndex[TSEC_CLASS_20_INDEX + i]*(100-UP_DOWN_BOUND) )/100;
             }
             if (StockMem[tsec_index20_seq[i]].y_close <= 0l)
                continue;
             MemTransferToNewMis1BinFmtAndSend(tsec_index20_seq[i] );
             }
    }
//----------------- update today index and send -------------
    else if (w_time != 32400)  {
          if( !TsecClassIndex[TOTAL_INDEX])
                return;
          StockMem[tsec_index_seq].deal_price=TsecClassIndex[TOTAL_INDEX];
          StockMem[tsec_index_seq].deal_sheet=Tsec9995.deal_amount;
          StockMem[tsec_index_seq].time = w_time;
          MemTransferToMis2BinFmtAndSendEx(tsec_index_seq, _DEAL);
          if((type == 2) && ( !FixedPriceTrade[ 0 ].Ok)) return;
          if (tsec_unindex_seq!=-1){
             StockMem[tsec_unindex_seq].deal_price = TsecClassIndex[TSEC_NOBANK_INDEX];
             StockMem[tsec_unindex_seq].deal_sheet = TsecClass[1].Val/nInxBaseValue;
             StockMem[tsec_unindex_seq].time = w_time;
             MemTransferToMis2BinFmtAndSendEx(tsec_unindex_seq, _DEAL);
          }
          if (simsci_index_seq!=-1){
             StockMem[simsci_index_seq].deal_price = TsecClassIndex[TSEC_NOELEC_INDEX];
             StockMem[simsci_index_seq].deal_sheet = TsecClass[2].Val/nInxBaseValue;
             StockMem[simsci_index_seq].time = w_time;
             MemTransferToMis2BinFmtAndSendEx(simsci_index_seq, _DEAL);
          }
          for(i=0; i<tsec_class_total; i++){
              if (tsec_index20_seq[i] <= 0)
                 continue;
              if(gMisVer  && fg_Richv710)  {
                 StockMem[tsec_index20_seq[i]].deal_price=TsecClassIndex[TSEC_NEW_CLASS_INDEX + i];
                 if(i < 2) { // 化學&生技
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[i+34].Val/nInxBaseValue;
                 }
                 else if(i < 29) { //水泥到百貨
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[i+3].Val/nInxBaseValue;
                 }
                 else if(i < 30) { //其它指
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[i+4].Val/nInxBaseValue;
                 }
                 else if(i < 31) { //無金電
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[99].Val/nInxBaseValue;
                 }
                 else  { //油電至其它電
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[i+5].Val/nInxBaseValue;
                 }
              }
              else {
                 StockMem[tsec_index20_seq[i]].deal_price=TsecClassIndex[TSEC_CLASS_20_INDEX + i];
                 if(i>=18)
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[i+15].Val/nInxBaseValue;
                 else
                    StockMem[tsec_index20_seq[i]].deal_sheet = TsecClass[i+14].Val/nInxBaseValue;
              }
              StockMem[tsec_index20_seq[i]].time = w_time;
              if (StockMem[tsec_index20_seq[i]].deal_price <= 0l)
                continue;
              MemTransferToMis2BinFmtAndSendEx(tsec_index20_seq[i], _DEAL);
          }
    }
}

void MemTransferToETFMis1BinFmtAndSendV2( int seq )
{
    int  i;
    char  CheckSum;
    char  *_ptr;
    int   offset;
    int   buy_num, sell_num; 

    BINFMT bp;
    memset(bp.buf, 0, sizeof(bp.buf));

    bp.i_mis1_etf2.esc = ESC;
    bp.i_mis1_etf2.mis = 0xA3;
    bp.i_mis1_etf2.stock_no = seq;
    bp.i_mis1_etf2.fg_s = 0x00;
    bp.i_mis1_etf2.fg.u = 0x00;

    if( !StockMem[seq].type)
        bp.i_mis1_etf2.fg_s |= 0x40;
    else if( StockMem[seq].total_shares)
        bp.i_mis1_etf2.fg_s |= 0x80;

    if((StockMem[seq].warn_flag & BIT7)){
        bp.i_mis1_etf2.fg_s |= 0x04;
        if(StockMem[seq].warn_flag & BIT6)
            bp.i_mis1_etf2.fg_s |= 0x02;
        if(StockMem[seq].warn_flag & BIT5)
            bp.i_mis1_etf2.fg_s |= 0x01;
    }
    else if(StockMem[seq].updown_flag & 0x20) {
        bp.i_mis1_etf2.fg.b.bit1 = 0;            /* Up */
        bp.i_mis1_etf2.fg.b.bit2 = 1;
    }
    else if(StockMem[seq].updown_flag & 0x10) {
        bp.i_mis1_etf2.fg.b.bit1 = 1;            /* Down */
        bp.i_mis1_etf2.fg.b.bit2 = 0;
    }
    else if((StockMem[seq].updown_flag & 0x30) == 0x30) {
        bp.i_mis1_etf2.fg.b.bit1 = 1;
        bp.i_mis1_etf2.fg.b.bit2 = 1;
    }
    else {
        bp.i_mis1_etf2.fg.b.bit1 = 0;            /* None */
        bp.i_mis1_etf2.fg.b.bit2 = 0;
    }

    if(StockMem[seq].warn_flag & 0x01)
        bp.i_mis1_etf2.fg.b.bit7 = 1;
    if(StockMem[seq].warn_flag & 0x02)
        bp.i_mis1_etf2.fg.b.bit5 = 1;
    if(StockMem[seq].warn_flag & 0x04)
        bp.i_mis1_etf2.fg.b.bit6 = 1;

    bp.i_mis1_etf2.fg.b.bit0 = ComparePrice(StockMem[seq].time) ? 1 : 0;
    bp.i_mis1_etf2.sec = comp_price;
    bp.i_mis1_etf2.y_ptr = StockMem[seq].y_index;
    bp.i_mis1_etf2.y_close.Lint  = StockMem[seq].y_close % 65536L;
    bp.i_mis1_etf2.y_close.Hbyte = StockMem[seq].y_close / 65536L;
    bp.i_mis1_etf2.up_bound.Lint  = StockMem[seq].up_bound % 65536L;
    bp.i_mis1_etf2.up_bound.Hbyte = StockMem[seq].up_bound / 65536L;
    bp.i_mis1_etf2.dn_bound.Lint  = StockMem[seq].dn_bound % 65536L;
    bp.i_mis1_etf2.dn_bound.Hbyte = StockMem[seq].dn_bound / 65536L;
    bp.i_mis1_etf2.deal_price.Lint  = StockMem[seq].deal_price % 65536L;
    bp.i_mis1_etf2.deal_price.Hbyte = StockMem[seq].deal_price / 65536L;
    bp.i_mis1_etf2.deal_sheet.Lint  = StockMem[seq].deal_sheet % 65536L;
    bp.i_mis1_etf2.deal_sheet.Hbyte = StockMem[seq].deal_sheet / 65536L;
    bp.i_mis1_etf2.etf_yes.Lint  = StockMem[seq].etf_yes % 65536L;
    bp.i_mis1_etf2.etf_yes.Hbyte = StockMem[seq].etf_yes / 65536L;
    bp.i_mis1_etf2.etf_price.Lint  = StockMem[seq].etf_price % 65536L;
    bp.i_mis1_etf2.etf_price.Hbyte = StockMem[seq].etf_price / 65536L;
    bp.i_mis1_etf2.warr_price      = StockMem[seq].warr_price;
    bp.i_mis1_etf2.use_rate        = StockMem[seq].use_rate;
    memcpy((char *)&(bp.i_mis1_etf2.y_deal_sheet), (char *)&(StockMem[seq].y_deal_sheet), 4);
    memcpy((char *)&(bp.i_mis1_etf2.y_cancel_sheet), (char *)&(StockMem[seq].y_cancel_sheet), 4);
    memcpy((char *)&(bp.i_mis1_etf2.total_shares), (char *)&(StockMem[seq].total_shares), 4);
    memcpy((char *)&(bp.i_mis1_etf2.money_type), (char *)&(StockMem[seq].money_type), 3);
    bp.i_mis1_etf2.unit_type.Lint  = StockMem[seq].unit_type % 65536L;
    bp.i_mis1_etf2.unit_type.Hbyte = StockMem[seq].unit_type / 65536L;

    _ptr = &bp.buf[BIN_IP_MIS1_ETF2_SIZE];
    offset = 0;
    buy_num = ((StockMem[seq].field_fg & _BUY_PRICE_SHEET) >> 4);
    for(i=0; i<buy_num; i++) {
        memcpy( _ptr+offset, &StockMem[seq].buy_price[i], 3 );
        offset += 3;
        memcpy( _ptr+offset, &StockMem[seq].buy_sheet[i], 3 );
        offset += 3;
    }
    sell_num = ((StockMem[seq].field_fg & _SELL_PRICE_SHEET) >> 1);
    for(i=0; i<sell_num; i++) {
        memcpy( _ptr+offset, &StockMem[seq].sell_price[i], 3 );
        offset += 3;
        memcpy( _ptr+offset, &StockMem[seq].sell_sheet[i], 3 );
        offset += 3;
    }
    bp.i_mis1_etf2.field_fg.u = (buy_num << 4)|sell_num;
    CheckSum=0;
    for( i=0 ; i< BIN_IP_MIS1_ETF2_SIZE -1  ; i++ )
        CheckSum ^= bp.buf[i];
    bp.buf[BIN_IP_MIS1_ETF2_SIZE - 1] = CheckSum;
    if( offset) {
        offset++;
        CheckSum=0;
        for( i=0 ; i< offset -1  ; i++ )
            CheckSum ^= bp.buf[i + BIN_IP_MIS1_ETF2_SIZE];
        bp.buf[BIN_IP_MIS1_ETF2_SIZE + offset -1] = CheckSum;
    }
    CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_MIS1_ETF2_SIZE + offset, 0);
    if( (vip_cycle.mis1_fg <= 3) &&  pfCycleLog && fg_cycle_file)
        fwrite( bp.buf, 1, BIN_IP_MIS1_ETF2_SIZE + offset, pfCycleLog);
}

void MemTransferToMis1_EXT_BinFmtAndSendV2( int seq )
{
    int  i;
    char  CheckSum;
    char  *_ptr;
    int   offset;
    int   buy_num, sell_num; 
    BINFMT bp;
    memset(bp.buf, 0, sizeof(bp.buf));
    bp.i_mis1_ext2.esc = ESC;
    bp.i_mis1_ext2.mis = 0xA2;
    bp.i_mis1_ext2.stock_no = seq;
    bp.i_mis1_etf2.fg_s = 0x00;
    bp.i_mis1_etf2.fg.u = 0x00;

    if(StockMem[seq].fg)
         bp.i_mis1_ext2.fg_s |= 0x10;
    if(StockMem[seq].fgNear)
         bp.i_mis1_ext2.fg_s |= 0x20;

    if((StockMem[seq].warn_flag & BIT7)){
        bp.i_mis1_etf2.fg_s |= 0x04;
        if(StockMem[seq].warn_flag & BIT6)
            bp.i_mis1_etf2.fg_s |= 0x02;
        if(StockMem[seq].warn_flag & BIT5)
            bp.i_mis1_etf2.fg_s |= 0x01;
    }
    else if(StockMem[seq].updown_flag & 0x20) {
        bp.i_mis1_ext2.fg.b.bit1 = 0;            /* Up */
        bp.i_mis1_ext2.fg.b.bit2 = 1;
    }
    else if(StockMem[seq].updown_flag & 0x10) {
        bp.i_mis1_ext2.fg.b.bit1 = 1;            /* Down */
        bp.i_mis1_ext2.fg.b.bit2 = 0;
    }
    else if((StockMem[seq].updown_flag & 0x30) == 0x30) {
        bp.i_mis1_etf2.fg.b.bit1 = 1;
        bp.i_mis1_etf2.fg.b.bit2 = 1;
    }
    else {
        bp.i_mis1_ext2.fg.b.bit1 = 0;            /* None */
        bp.i_mis1_ext2.fg.b.bit2 = 0;
    }

    if(StockMem[seq].warn_flag & 0x01)
        bp.i_mis1_ext2.fg.b.bit7 = 1;
    if(StockMem[seq].warn_flag & 0x02)
        bp.i_mis1_ext2.fg.b.bit5 = 1;
    if(StockMem[seq].warn_flag & 0x04)
        bp.i_mis1_ext2.fg.b.bit6 = 1;

    bp.i_mis1_ext2.fg.b.bit0 = ComparePrice(StockMem[seq].time) ? 1 : 0;
    bp.i_mis1_ext2.sec = comp_price;
    bp.i_mis1_ext2.y_ptr = StockMem[seq].y_index;
    bp.i_mis1_ext2.y_close.Lint  = StockMem[seq].y_close % 65536L;
    bp.i_mis1_ext2.y_close.Hbyte = StockMem[seq].y_close / 65536L;
    bp.i_mis1_ext2.up_bound.Lint  = StockMem[seq].up_bound % 65536L;
    bp.i_mis1_ext2.up_bound.Hbyte = StockMem[seq].up_bound / 65536L;
    bp.i_mis1_ext2.dn_bound.Lint  = StockMem[seq].dn_bound % 65536L;
    bp.i_mis1_ext2.dn_bound.Hbyte = StockMem[seq].dn_bound / 65536L;
    bp.i_mis1_ext2.deal_price.Lint  = StockMem[seq].deal_price % 65536L;
    bp.i_mis1_ext2.deal_price.Hbyte = StockMem[seq].deal_price / 65536L;
    bp.i_mis1_ext2.deal_sheet.Lint  = StockMem[seq].deal_sheet % 65536L;
    bp.i_mis1_ext2.deal_sheet.Hbyte = StockMem[seq].deal_sheet / 65536L;
    memcpy((char *)&(bp.i_mis1_ext2.money_type), (char *)&(StockMem[seq].money_type), 3);
    bp.i_mis1_ext2.unit_type.Lint  = StockMem[seq].unit_type % 65536L;
    bp.i_mis1_ext2.unit_type.Hbyte = StockMem[seq].unit_type / 65536L;

    _ptr = &bp.buf[BIN_IP_MIS1_EXT2_SIZE];
    offset = 0;
    buy_num = ((StockMem[seq].field_fg & _BUY_PRICE_SHEET) >> 4);
    for(i=0; i<buy_num; i++) {
        memcpy( _ptr+offset, &StockMem[seq].buy_price[i], 3 );
        offset += 3;
        memcpy( _ptr+offset, &StockMem[seq].buy_sheet[i], 3 );
        offset += 3;
    }
    sell_num = ((StockMem[seq].field_fg & _SELL_PRICE_SHEET) >> 1);
    for(i=0; i<sell_num; i++) {
        memcpy( _ptr+offset, &StockMem[seq].sell_price[i], 3 );
        offset += 3;
        memcpy( _ptr+offset, &StockMem[seq].sell_sheet[i], 3 );
        offset += 3;
    }
    bp.i_mis1_ext2.field_fg.u = (buy_num << 4)|sell_num;
    CheckSum=0;
    for( i=0 ; i< BIN_IP_MIS1_EXT2_SIZE -1  ; i++ )
        CheckSum ^= bp.buf[i];
    bp.buf[BIN_IP_MIS1_EXT2_SIZE - 1] = CheckSum;
    if( offset) {
        offset++;
        CheckSum=0;
        for( i=0 ; i< offset -1  ; i++ )
            CheckSum ^= bp.buf[i + BIN_IP_MIS1_EXT2_SIZE];
        bp.buf[BIN_IP_MIS1_EXT2_SIZE + offset -1] = CheckSum;
    }
    CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_MIS1_EXT2_SIZE + offset, 0);
    if( (vip_cycle.mis1_fg <= 3) &&  pfCycleLog && fg_cycle_file)
        fwrite( bp.buf, 1, BIN_IP_MIS1_EXT2_SIZE + offset, pfCycleLog);
}

void MemTransferToETFMis1BinFmtAndSend( int seq )
{
    int  i;
    char  CheckSum;
    char  *_ptr;
    int   offset;
    int   buy_num, sell_num; 
    BINFMT bp;
    memset(bp.buf, 0, sizeof(bp.buf));

    bp.i_mis1_etf.esc = ESC;
    bp.i_mis1_etf.mis = 0xA7;
    bp.i_mis1_etf.stock_no = seq;
    if( !StockMem[seq].type)
        bp.i_mis1_etf.fg_s |= 0x40;
    else if( StockMem[seq].total_shares)
        bp.i_mis1_etf.fg_s |= 0x80;
    if(StockMem[seq].warn_flag & 0x01)
        bp.i_mis1_etf.fg.b.bit7 = 1;
    if(StockMem[seq].warn_flag & 0x02)
        bp.i_mis1_etf.fg.b.bit5 = 1;
    if(StockMem[seq].warn_flag & 0x04)
        bp.i_mis1_etf.fg.b.bit6 = 1;
    if(StockMem[seq].warn_flag & 0x20) {   //bug: should use updown_flag
        bp.i_mis1_etf.fg.b.bit1 = 0;            /* Up */
        bp.i_mis1_etf.fg.b.bit2 = 1;
    }
    else if(StockMem[seq].warn_flag & 0x10) {  //bug: should use updown_flag
        bp.i_mis1_etf.fg.b.bit1 = 1;            /* Down */
        bp.i_mis1_etf.fg.b.bit2 = 0;
    }
    else {
        bp.i_mis1_etf.fg.b.bit1 = 0;            /* None */
        bp.i_mis1_etf.fg.b.bit2 = 0;
    }
    bp.i_mis1_etf.fg.b.bit0 = ComparePrice(StockMem[seq].time) ? 1 : 0;
    bp.i_mis1_etf.sec = comp_price;
    bp.i_mis1_etf.y_close.Lint  = StockMem[seq].y_close % 65536L;
    bp.i_mis1_etf.y_close.Hbyte = StockMem[seq].y_close / 65536L;
    bp.i_mis1_etf.up_bound.Lint  = StockMem[seq].up_bound % 65536L;
    bp.i_mis1_etf.up_bound.Hbyte = StockMem[seq].up_bound / 65536L;
    bp.i_mis1_etf.dn_bound.Lint  = StockMem[seq].dn_bound % 65536L;
    bp.i_mis1_etf.dn_bound.Hbyte = StockMem[seq].dn_bound / 65536L;
    bp.i_mis1_etf.deal_price.Lint  = StockMem[seq].deal_price % 65536L;
    bp.i_mis1_etf.deal_price.Hbyte = StockMem[seq].deal_price / 65536L;
    bp.i_mis1_etf.deal_sheet.Lint  = StockMem[seq].deal_sheet % 65536L;
    bp.i_mis1_etf.deal_sheet.Hbyte = StockMem[seq].deal_sheet / 65536L;
    bp.i_mis1_etf.etf_yes.Lint  = StockMem[seq].etf_yes % 65536L;
    bp.i_mis1_etf.etf_yes.Hbyte = StockMem[seq].etf_yes / 65536L;
    bp.i_mis1_etf.etf_price.Lint  = StockMem[seq].etf_price % 65536L;
    bp.i_mis1_etf.etf_price.Hbyte = StockMem[seq].etf_price / 65536L;
    bp.i_mis1_etf.warr_price.Lint  = StockMem[seq].warr_price % 65536L;
    bp.i_mis1_etf.warr_price.Hbyte = StockMem[seq].warr_price / 65536L;
    bp.i_mis1_etf.use_rate.Lint  = StockMem[seq].use_rate % 65536L;
    bp.i_mis1_etf.use_rate.Hbyte = StockMem[seq].use_rate / 65536L;
    memcpy((char *)&(bp.i_mis1_etf.y_deal_sheet), (char *)&(StockMem[seq].y_deal_sheet), 4);
    memcpy((char *)&(bp.i_mis1_etf.y_cancel_sheet), (char *)&(StockMem[seq].y_cancel_sheet), 4);
    memcpy((char *)&(bp.i_mis1_etf.total_shares), (char *)&(StockMem[seq].total_shares), 4);

    _ptr = &bp.buf[BIN_IP_MIS1_ETF_SIZE];
    offset = 0;
    buy_num = ((StockMem[seq].field_fg & _BUY_PRICE_SHEET) >> 4);
    for(i=0; i<buy_num; i++) {
        memcpy( _ptr+offset, &StockMem[seq].buy_price[i], 3 );
        offset += 3;
        memcpy( _ptr+offset, &StockMem[seq].buy_sheet[i], 3 );
        offset += 3;
    }
    sell_num = ((StockMem[seq].field_fg & _SELL_PRICE_SHEET) >> 1);
    for(i=0; i<sell_num; i++) {
        memcpy( _ptr+offset, &StockMem[seq].sell_price[i], 3 );
        offset += 3;
        memcpy( _ptr+offset, &StockMem[seq].sell_sheet[i], 3 );
        offset += 3;
    }
    bp.i_mis1_etf.field_fg.u = (buy_num << 4)|sell_num;
    CheckSum=0;
    for( i=0 ; i< BIN_IP_MIS1_ETF_SIZE -1  ; i++ )
        CheckSum ^= bp.buf[i];
    bp.buf[BIN_IP_MIS1_ETF_SIZE - 1] = CheckSum;
    if( offset) {
        offset++;
        CheckSum=0;
        for( i=0 ; i< offset -1  ; i++ )
            CheckSum ^= bp.buf[i + BIN_IP_MIS1_ETF_SIZE];
        bp.buf[BIN_IP_MIS1_ETF_SIZE + offset -1] = CheckSum;
    }
    CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_MIS1_ETF_SIZE + offset, 0);
    if( (vip_cycle.mis1_fg <= 3) &&  pfCycleLog && fg_cycle_file)
        fwrite( bp.buf, 1, BIN_IP_MIS1_ETF_SIZE + offset, pfCycleLog);
}

void MemTransferToMis1_EXT_BinFmtAndSend( int seq )
{
    int  i;
    char  CheckSum;
    char  *_ptr;
    int   offset;
    int   buy_num, sell_num; 
    BINFMT bp;
    memset(bp.buf, 0, sizeof(bp.buf));
    bp.i_mis1_ext.esc = ESC;
    bp.i_mis1_ext.mis = 0xA2;
    bp.i_mis1_ext.stock_no = seq;
    if(StockMem[seq].fg)
         bp.i_mis1_ext.fg_s |= 0x10;
    if(StockMem[seq].fgNear)
         bp.i_mis1_ext.fg_s |= 0x20;
    if(StockMem[seq].warn_flag & 0x01)
        bp.i_mis1_ext.fg.b.bit7 = 1;
    if(StockMem[seq].warn_flag & 0x02)
        bp.i_mis1_ext.fg.b.bit5 = 1;
    if(StockMem[seq].warn_flag & 0x04)
        bp.i_mis1_ext.fg.b.bit6 = 1;
    if(StockMem[seq].warn_flag & 0x20) {
        bp.i_mis1_ext.fg.b.bit1 = 0;            /* Up */
        bp.i_mis1_ext.fg.b.bit2 = 1;
    }
    else if(StockMem[seq].warn_flag & 0x10) {
        bp.i_mis1_ext.fg.b.bit1 = 1;            /* Down */
        bp.i_mis1_ext.fg.b.bit2 = 0;
    }
    else {
        bp.i_mis1_ext.fg.b.bit1 = 0;            /* None */
        bp.i_mis1_ext.fg.b.bit2 = 0;
    }
    bp.i_mis1_ext.fg.b.bit0 = ComparePrice(StockMem[seq].time) ? 1 : 0;
    bp.i_mis1_ext.sec = comp_price;
    bp.i_mis1_ext.y_ptr = StockMem[seq].y_index;
    bp.i_mis1_ext.y_close.Lint  = StockMem[seq].y_close % 65536L;
    bp.i_mis1_ext.y_close.Hbyte = StockMem[seq].y_close / 65536L;
    bp.i_mis1_ext.up_bound.Lint  = StockMem[seq].up_bound % 65536L;
    bp.i_mis1_ext.up_bound.Hbyte = StockMem[seq].up_bound / 65536L;
    bp.i_mis1_ext.dn_bound.Lint  = StockMem[seq].dn_bound % 65536L;
    bp.i_mis1_ext.dn_bound.Hbyte = StockMem[seq].dn_bound / 65536L;
    bp.i_mis1_ext.deal_price.Lint  = StockMem[seq].deal_price % 65536L;
    bp.i_mis1_ext.deal_price.Hbyte = StockMem[seq].deal_price / 65536L;
    bp.i_mis1_ext.deal_sheet.Lint  = StockMem[seq].deal_sheet % 65536L;
    bp.i_mis1_ext.deal_sheet.Hbyte = StockMem[seq].deal_sheet / 65536L;

    _ptr = &bp.buf[BIN_IP_MIS1_EXT_SIZE];
    offset = 0;
    buy_num = ((StockMem[seq].field_fg & _BUY_PRICE_SHEET) >> 4);
    for(i=0; i<buy_num; i++) {
        memcpy( _ptr+offset, &StockMem[seq].buy_price[i], 3 );
        offset += 3;
        memcpy( _ptr+offset, &StockMem[seq].buy_sheet[i], 3 );
        offset += 3;
    }
    sell_num = ((StockMem[seq].field_fg & _SELL_PRICE_SHEET) >> 1);
    for(i=0; i<sell_num; i++) {
        memcpy( _ptr+offset, &StockMem[seq].sell_price[i], 3 );
        offset += 3;
        memcpy( _ptr+offset, &StockMem[seq].sell_sheet[i], 3 );
        offset += 3;
    }
    bp.i_mis1_ext.field_fg.u = (buy_num << 4)|sell_num;
    CheckSum=0;
    for( i=0 ; i< BIN_IP_MIS1_EXT_SIZE -1  ; i++ )
        CheckSum ^= bp.buf[i];
    bp.buf[BIN_IP_MIS1_EXT_SIZE - 1] = CheckSum;
    if( offset) {
        offset++;
        CheckSum=0;
        for( i=0 ; i< offset -1  ; i++ )
            CheckSum ^= bp.buf[i + BIN_IP_MIS1_EXT_SIZE];
        bp.buf[BIN_IP_MIS1_EXT_SIZE + offset -1] = CheckSum;
    }
    CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_MIS1_EXT_SIZE + offset, 0);
    if( (vip_cycle.mis1_fg <= 3) &&  pfCycleLog && fg_cycle_file)
        fwrite( bp.buf, 1, BIN_IP_MIS1_EXT_SIZE + offset, pfCycleLog);

}

// v6.8.0, 89.6 activated to replace MemTransferToMis1BinFmtAndSend
// because of limited stocks project, send out 'B'
void MemTransferToNewMis1BinFmtAndSend( int seq )
{
    int i;
    if((((StockMem[seq].mkt == 1) || (StockMem[seq].mkt == 2)) && !StockMem[seq].type) || StockMem[seq].total_shares) {
        MemTransferToETFMis1BinFmtAndSendV2(seq);
    }
    else {
        MemTransferToMis1_EXT_BinFmtAndSendV2(seq);
    }
}

// send set time
void Send9992AndDisplayTime(void)
{
    static unsigned char compare_flag=1;
    static Word time_temp = 71;
    int  i;
    long system_time_s,tsec_time_s;
    char Time9992_EXT[10]={ ESC, '0', '0', '0', '0', '0', '0', '0', '0 ', '0'};
    struct date today;

    getdate(&today);
    if ( !SetTime_flag ) {
        if ( compare_flag ) {
            system_time_s = NowSystemSec;
            tsec_time_s  =(long)(CommendTime/100)*3600l+(long)(CommendTime%100)*60l;
            if (( (tsec_time_s-system_time_s)>interleave) || ( (tsec_time_s-system_time_s)<(-1*interleave) )) {
                tsec_time_s+=SECOND;
                dtime.ti_hour=(unsigned char)(tsec_time_s/3600l);
                dtime.ti_min =(unsigned char)((tsec_time_s%3600l)/60l);
                dtime.ti_sec =(unsigned char)(tsec_time_s%60l);
                settime( &dtime );
            }
            compare_flag=0;
        }
        SetTime_flag=1;
    }
    if( NowSystemMin != time_temp ) {
        time_temp = NowSystemMin;
        Time9992_EXT[2] = NowSystemYear%100;
        Time9992_EXT[3] = NowSystemMonth;
        Time9992_EXT[4] = NowSystemDay;
        Time9992_EXT[5] = NowSystemHour;
        Time9992_EXT[6] = NowSystemMin;
        Time9992_EXT[7] = NowSystemSecc;
        for( i=0 ; i<3 ; i++) {
            CalCheckSumAndSendToMoxaCard( Time9992_EXT, 8 );
        }
    }
}

void SendCycleNew(void)
{
    static char mkt=0x01;        // 0x01: TSEC,   0x02: OTC
    static int  last=0;          // last PH new sent out
    BINFMT bp;
    memset(bp.buf, 0, sizeof(bp.buf));
    
    last++;
    if (mkt==0x01) {
        if (last <= New_Count) {
            bp.f_new_9997.esc        = ESC;
            bp.f_new_9997.mis        = 'o';
            bp.f_new_9997.market     = mkt;
            memcpy(bp.f_new_9997.text, Mem9997[last], 60);
            bp.f_new_9997.num = last;
            CalCheckSumAndSendToMoxaCard( bp.buf, BIN_NEW_9997_SIZE - 1);
        }
        if (last >= New_Count) {
            last = 0;
            mkt = 0x02;
        }
    }
    else if (mkt==0x02) {
        if (last <= OTCNew_Count) {
            bp.f_new_9997.esc        = ESC;
            bp.f_new_9997.mis        = 'o';
            bp.f_new_9997.market     = mkt;
            memcpy(bp.f_new_9997.text, OTCMem9997[last], 60);
            bp.f_new_9997.num = last;
            CalCheckSumAndSendToMoxaCard( bp.buf, BIN_NEW_9997_SIZE - 1);
        }
        if (last >= OTCNew_Count) {
            last = 0;
            mkt = 0x06;
        }
    }
    else if (mkt==0x06)  // TSEC emergent announcement
    {
        if (last <= TsecEMNew_Count) {
            bp.f_new_9997.esc        = ESC;
            bp.f_new_9997.mis        = 'o';
            bp.f_new_9997.market     = mkt;
            memcpy(bp.f_new_9997.text, TsecEM9997[last], 60);
            bp.f_new_9997.num = last;
            CalCheckSumAndSendToMoxaCard( bp.buf, BIN_NEW_9997_SIZE - 1);
        }
        if (last >= TsecEMNew_Count) {
            last = 0;
            mkt = 0x07;
        }
    }
    else if (mkt==0x07)  // OTC emergent announcement
    {
        if (last <= OtcEMNew_Count) {
            bp.f_new_9997.esc        = ESC;
            bp.f_new_9997.mis        = 'o';
            bp.f_new_9997.market     = mkt;
            memcpy(bp.f_new_9997.text, OtcEM9997[last], 60);
            bp.f_new_9997.num = last;
            CalCheckSumAndSendToMoxaCard( bp.buf, BIN_NEW_9997_SIZE - 1);
        }
        if (last >= OtcEMNew_Count) {
            last = 0;
            mkt = 0x01;
        }
    }
}

int  Write_TSEC_Yes_Close(char *filename)
{
    int    i,tsec_sq=-1;
    FILE * handle;
    struct CCCC   * stock_ndx_data;

    handle = _fsopen(filename,"w+b",SH_DENYRW);
    if (handle==NULL)   return -1;
    for ( i=0 ; i< max_TotalStockNo ; i++ ) {
        stock_ndx_data = SearchToyoNumberEx(StockMem[i].stock_no, MK_TSEC);
        if (stock_ndx_data != NULL)
            tsec_sq=stock_ndx_data->tsec_seq;

        sprintf(tsec_buffer,"%c%c%c%c%c%c %-8ld %-4d\x0d\x0a",
               StockMem[i].stock_no[0], StockMem[i].stock_no[1],
               StockMem[i].stock_no[2], StockMem[i].stock_no[3],
               StockMem[i].stock_no[4],StockMem[i].stock_no[5],
               StockMem[i].deal_price, tsec_sq);
        fwrite(tsec_buffer,sizeof(char),strlen(tsec_buffer),handle);
    }
    fclose(handle);
    return 0;
}

int  Read_TSEC_Yes_Close(char *filename)
{
    int i,seqx;
    FILE *handle;
    char *ptr;
    unsigned char stock_no[6];
    long  y_close;

    handle = _fsopen(filename,"rb",SH_DENYNO);
    if (handle==NULL)   return -1;
    for ( i=0 ; i<max_TotalStockNo ; i++)   {
        fgets(tsec_buffer,45,handle);
        if (feof(handle))   break;
        ptr=strtok(tsec_buffer," ");
        strcpy(stock_no,ptr);
        if (stock_no[4]<' ' || stock_no[4]>0x7f )
            stock_no[4]=' ';
        stock_no[5]=' ';

        seqx=SearchToyoNumber(stock_no);
        if (seqx==-1)   continue;
        if((ptr=strtok(NULL," ")) == NULL)   continue;
        y_close =atol(ptr);

        if((ptr=strtok(NULL," ")) == NULL)   continue;
        stock_ndx_data = SearchToyoNumberEx(StockMem[seqx].stock_no, MK_TSEC);
        if ((stock_ndx_data!=NULL) && (atol(ptr)!=0) )
            stock_ndx_data->tsec_seq=atol(ptr);

        if( !StockMem[seqx].y_close || !StockMem[seqx].up_bound || !StockMem[seqx].dn_bound) {
            StockMem[seqx].y_close  = y_close;
            StockMem[seqx].up_bound = (float)y_close * 1.07;
            StockMem[seqx].dn_bound = (float)y_close * 0.93;
        }
    }
    fclose(handle);
    return 0;
}
void WriteStableStockFile(void)
{
    int i, j;
    FILE  *temp_f1;
    time_t now;
    struct tm *pNow;
    char  buff[256], stock_id[10], stk_name[10];

    time(&now);
    pNow = localtime(&now);

    if ((temp_f1=fopen(sStableFullTempName,"w")) != NULL) {
        sprintf(buff, "■  %02d:%02d 集中市場價格穩定措施現況\n", pNow->tm_hour, pNow->tm_min);
        fputs(buff, temp_f1);
        for(i=0, j=0; i<max_TotalStockNo; i++) {
            if(StockMem[i].updown_flag & 0x03) {
                j++;
                if(j==1 || j==12)
                    fputs("代號   股  名  趨勢  時    間   成交價  累計量\n", temp_f1);
                else if((((j-12)%12)==0) && j>13)
                    fputs("代號   股  名  趨勢  時    間   成交價  累計量\n", temp_f1);
                strncpy(stock_id, StockMem[i].stock_no, 6);
                stock_id[6]='\0';
                strncpy(stk_name, StockMem[i].chi_name, 6);
                stk_name[6]='\0';
                sprintf(buff, "%6s %-6s  %4s  %02d:%02d:%02d %7.2f%8ld\n",
                    stock_id, stk_name, ((StockMem[i].warn_flag & 0x10)?"趨跌":"趨漲"),   //bug: should use updown_flag
                    StockMem[i].time /3600l, (StockMem[i].time /60l)%60l, StockMem[i].time %60l,
                    StockMem[i].deal_price/100.0, StockMem[i].deal_sheet);
                fputs(buff, temp_f1);
            }
        }
        fclose(temp_f1);
        unlink(sStableFullOutName);
        rename(sStableFullTempName, sStableFullOutName);
    }
    else
        fg_Write_Stable_err = 1;
}

void ReSendScatIndex(int market, long Money, long Sheet, long Count)
{
    struct ONEMIN_TIME scat_1min;
    int    i;
    int    class_total;
    int    offset_length;
    char   CheckSum;

    if((market != MK_TSEC) && (market != MK_OTC))
        return;
    scat_1min.idx_time = 1332;
    scat_1min.time_ptr = max_1min_ptr;
    if(market == MK_TSEC) {
        Tsec9995.deal_amount =  close2mem9995.deal_amount + Money;
        Tsec9995.deal_sheet =  close2mem9995.deal_sheet + Sheet;
        Tsec9995.deal_count = close2mem9995.deal_count + Count;
        class_total = tsec_class_total;
    }
    else if(market == MK_OTC) {
        Otc9995.deal_amount =  Otc_close2mem9995.deal_amount + Money;
        Otc9995.deal_sheet =  Otc_close2mem9995.deal_sheet + Sheet;
        Otc9995.deal_count = Otc_close2mem9995.deal_count + Count;
        class_total = otc_class_total;
    }
    BINFMT bp;
    memset(bp.buf, 0, sizeof(bp.buf));
    bp.i_cs_index.esc = ESC;
    bp.i_cs_index.mis = 0x7f;
    bp.i_cs_index.mkt = market;
    bp.i_cs_index.cnt = class_total;
    memcpy(&(bp.i_cs_index.ptr), &(scat_1min.time_ptr), 4);
    CheckSum=0;
    for( i=0 ; i< BIN_IP_M_CLS_INDEX_SIZE -1  ; i++ )
        CheckSum ^= bp.buf[i];
    bp.buf[BIN_IP_M_CLS_INDEX_SIZE-1] = CheckSum;
    memcpy( &bp.buf[BIN_IP_M_CLS_INDEX_SIZE], ((market == MK_TSEC)?&Tsec9995.deal_count:&Otc9995.deal_count), sizeof(long));
    MakeRealClassSharesValue(market, 0, &bp.buf[BIN_IP_M_CLS_INDEX_SIZE+sizeof(long)], class_total);
    offset_length = class_total * sizeof(long)*2 + sizeof(long) + 1;
    CheckSum=0;
    for( i=0 ; i< offset_length -1  ; i++ )
        CheckSum ^= bp.buf[i + BIN_IP_M_CLS_INDEX_SIZE];
    bp.buf[BIN_IP_M_CLS_INDEX_SIZE + offset_length -1] = CheckSum;
    CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_M_CLS_INDEX_SIZE + offset_length, 0);
}

void UpdateScatData(int market, int seq, long deal_sheet, long amount)
{
    int kind_id;
    
    if(deal_sheet < StockMem[seq].deal_sheet)
        return;
    if(market == MK_TSEC) {
        if((StockMem[seq].mkt == 1) && (StockMem[seq].type <= 80 && StockMem[seq].type > 0)){
            TsecClass[StockMem[seq].type+13].Val += ((double)(amount - StockMem[seq].price_amount));
            TsecClass[StockMem[seq].type+13].DealSheet += (deal_sheet - StockMem[seq].deal_sheet);
        }
    }
    else if(market == MK_OTC) {
        if(StockMem[seq].mkt == 2) {
            kind_id = OtcClassToKindIndex(StockMem[seq].type);
            if((kind_id >= 0) && (kind_id <= 40)) {
                OtcClass[kind_id].Val += ((double)(amount - StockMem[seq].price_amount));
                OtcClass[kind_id].DealSheet += (deal_sheet - StockMem[seq].deal_sheet);
            }
        }
    }
    if(deal_sheet > StockMem[seq].deal_sheet)   {
        StockMem[seq].time = CalTimetoTimeConvMinEx(133200);
        StockMem[seq].deal_sheet = deal_sheet;
        MemTransferToMis2BinFmtAndSendEx( seq , _DEAL);
    }
}

void NewTaiwanIndex(const IP_FMT& prot)
{
    int  stk_toyo, sheet_inx;
    long temp;
    char stkname[10];
    long tmp_time;

    memcpy(stkname, prot.tsec_mis10.index_seq, 6);
    stkname[6] = 0;

    if((stk_toyo = DidcNameto_Toyo(stkname, 6)) > 0) {
        tmp_time = CutMrkTestTime(BCD_to_Long(prot.tsec_mis10.time, TIME_FSIZE), MK_TSEC);
        if(tmp_time >= 999999) tmp_time = 133100;
        if((temp = BCD_to_Long(prot.tsec_mis10.index, INDEX_FSIZE)) > 0) {
            if (tmp_time <= 90000){
                StockMem[stk_toyo].y_close = temp;
                StockMem[stk_toyo].up_bound = (temp * (100+UP_DOWN_BOUND) )/100;
                StockMem[stk_toyo].dn_bound = (temp * (100-UP_DOWN_BOUND) )/100;
                MemTransferToNewMis1BinFmtAndSend( stk_toyo);
            }
            else{
                StockMem[stk_toyo].deal_price = temp;
                if((sheet_inx = GetDidcNameSheetInx(stkname, 6)) > 0)
                    StockMem[stk_toyo].deal_sheet = TsecClass[sheet_inx].Val/nInxBaseValue;
                else
                    StockMem[stk_toyo].deal_sheet = 0l;
                StockMem[stk_toyo].time = CalTimetoTimeConvMinEx(tmp_time);
                MemTransferToMis2BinFmtAndSendEx( stk_toyo, _DEAL);
            }
        }
    }
}

void NewOtcTaiIndex(const IP_FMT& prot)
{
    int  stk_toyo, sheet_inx, inx_cnt;
    long temp;
    char stkname[10];
    long tmp_time;

        memcpy(stkname, prot.otc_mis12.inx.index_seq, 6);
        stkname[6] = 0;
        if((stk_toyo = DidcNameto_Toyo(stkname, 6)) > 0) {
            tmp_time = CutMrkTestTime(BCD_to_Long(prot.otc_mis12.inx.time, TIME_FSIZE), MK_OTC);
            if(tmp_time >= 999999) tmp_time = 133100;
            if((temp = BCD_to_Long(prot.otc_mis12.inx.index, INDEX_FSIZE)) > 0) {
                if (tmp_time <= 90000){
                    StockMem[stk_toyo].y_close = temp;
                    StockMem[stk_toyo].up_bound = (temp * (100+UP_DOWN_BOUND) )/100;
                    StockMem[stk_toyo].dn_bound = (temp * (100-UP_DOWN_BOUND) )/100;
                    MemTransferToNewMis1BinFmtAndSend( stk_toyo);
                }
                else{
                    StockMem[stk_toyo].deal_price = temp;
                    if((sheet_inx = GetDidcNameSheetInx(stkname, 6)) > 0)
                        StockMem[stk_toyo].deal_sheet = TsecClass[sheet_inx].Val/nInxBaseValue;
                    else
                        StockMem[stk_toyo].deal_sheet = 0l;
                    StockMem[stk_toyo].time = CalTimetoTimeConvMinEx(tmp_time);
                    MemTransferToMis2BinFmtAndSendEx( stk_toyo, _DEAL);
                }
            }
        }
    //}
}

void StkStopRecoverStat(const IP_FMT& prot)
{
    int  seq;
    char stkname[10];
    long tmStart_time, tmStop_time;

    memcpy(stkname, prot.mis19.stock_no, 6);
    stkname[6] = 0;
    seq=SearchToyoNumber(stkname);

    if ( seq > 0) {
        tmStop_time = CutMrkTestTime(BCD_to_Long(prot.mis19.stop_time, TIME_FSIZE), MK_TSEC);
        tmStart_time = CutMrkTestTime(BCD_to_Long(prot.mis19.start_time, TIME_FSIZE), MK_TSEC);
        if ((tmStop_time >= 999999) && (tmStart_time >= 999999)) { 
            return;
        }
        BINFMT bp;
        bp.i_stk_stop.esc = ESC;
        bp.i_stk_stop.mis = 0x99;
        bp.i_stk_stop.stock_no = seq;
        bp.i_stk_stop.fg = 0x0;
        if(tmStop_time >= 999999)  {
            bp.i_stk_stop.stop_time = 0;
        }
        else {
            if( ComparePrice(CalTimetoTimeConvMinEx(tmStop_time))) {
                bp.i_stk_stop.fg |= 0x01;
            }
            bp.i_stk_stop.stop_time = comp_price;
        }
        if (tmStart_time >= 999999)  {
            bp.i_stk_stop.start_time = 0;
        } else {
            if( ComparePrice(CalTimetoTimeConvMinEx(tmStart_time))) {
                bp.i_stk_stop.fg |= 0x02;
            }
            bp.i_stk_stop.start_time = comp_price;
        }
        CalCheckSumAndSendToMoxaCard( bp.buf, BIN_IP_STK_STOP_SIZE - 1 );
        if( fg_WarrInfoNews)  {
            WriteStkStopNewsFile(1, seq, tmStop_time, tmStart_time);
        }
    }
}

void IP_ReCallLostTick(int seq, long r_time, long r_price, long r_sheet)
{
    long temp, t_sheet;
    int i, tmp_cnt, kind_id;
    long tmp_time;

    StockMem[seq].time = r_time;

    (MemPrice+seq)->tsec_deal = r_price;
    StockMem[seq].deal_price = r_price;
    RefreshUpDownFg(seq);
    t_sheet = r_sheet - StockMem[seq].deal_sheet;
    StockMem[seq].price_amount = StockMem[seq].price_amount + ((double) (t_sheet * r_price / nStkBaseValue));
    if(StockMem[seq].mkt == 1 && (StockMem[seq].type <= 80 && StockMem[seq].type > 0)){
        if(StockMem[seq].spec_fg & _T_NON_E_50) {
            TsecClass[TWIWAN_N50_CLASS].Val += ((double)(t_sheet * r_price / nStkBaseValue));
            TsecClass[TWIWAN_N50_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_EMP99) {
            TsecClass[TWIWAN_EMP99_CLASS].Val += ((double)(t_sheet * r_price / nStkBaseValue));
            TsecClass[TWIWAN_EMP99_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_50) {
            TsecClass[TWIWAN_50_CLASS].Val += ((double)(t_sheet * r_price / nStkBaseValue));
            TsecClass[TWIWAN_50_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_100) {
            TsecClass[TWIWAN_100_CLASS].Val += ((double)(t_sheet * r_price / nStkBaseValue));
            TsecClass[TWIWAN_100_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_101) {
            TsecClass[TWIWAN_101_CLASS].Val += ((double)(t_sheet * r_price / nStkBaseValue));
            TsecClass[TWIWAN_101_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_TEC) {
            TsecClass[TWIWAN_TEC_CLASS].Val += ((double)(t_sheet * r_price / nStkBaseValue));
            TsecClass[TWIWAN_TEC_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_TEI) {
            TsecClass[TWIWAN_TEI_CLASS].Val += ((double)(t_sheet * r_price / nStkBaseValue));
            TsecClass[TWIWAN_TEI_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_TDP) {
            TsecClass[TWIWAN_TDP_CLASS].Val += ((double)(t_sheet * r_price / nStkBaseValue));
            TsecClass[TWIWAN_TDP_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TWIWAN_FRMSA) {
            TsecClass[TWIWAN_FRMSA_CLASS].Val += ((double)(t_sheet * r_price / nStkBaseValue));
            TsecClass[TWIWAN_FRMSA_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _TSEC_HC100) {
            TsecClass[TSEC_HC100_CLASS].Val += ((double)(t_sheet * r_price / nStkBaseValue));
            TsecClass[TSEC_HC100_CLASS].DealSheet += t_sheet;
        }
        TsecClass[StockMem[seq].type+13].Val += ((double)(t_sheet * r_price / nStkBaseValue));
        TsecClass[StockMem[seq].type+13].DealSheet += t_sheet;
    }
    else if(StockMem[seq].mkt == 2) {
        if(StockMem[seq].spec_fg & _T_OTC_50) {
            TsecClass[OTC_N50_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[OTC_N50_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _T_BOND_03) {
            TsecClass[OTC_BOND03_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[OTC_BOND03_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _T_OTC_GAME) {
            TsecClass[OTC_GAME_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[OTC_GAME_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _T_OTC_GTHD) {
            TsecClass[OTC_GTHD_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[OTC_GTHD_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _T_OTC_EMP88) {
            TsecClass[OTC_EMP88_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[OTC_EMP88_CLASS].DealSheet += t_sheet;
        }
        if(StockMem[seq].spec_fg & _OTC_GTCI) {
            TsecClass[OTC_GTCI_CLASS].Val += ((double)(t_sheet * g_deal_price / nStkBaseValue));
            TsecClass[OTC_GTCI_CLASS].DealSheet += t_sheet;
        }
        kind_id = OtcClassToKindIndex(StockMem[seq].type);
        if((kind_id >= 0) && (kind_id <= 40)) {
            OtcClass[kind_id].Val += ((double)(t_sheet * r_price / nStkBaseValue));
            OtcClass[kind_id].DealSheet += t_sheet;
        }
    }
    StockMem[seq].deal_sheet = r_sheet;
    StockMem[seq].field_fg |= _DEAL;
    MemTransferToMis2BinFmtAndSendEx(seq, StockMem[seq].field_fg);
}

void SendStkMdfInfo(int seq, long time, long nOpen, long nHigh, long nLow, long nLast, long nSheet)
{
    BINFMT bp;
    memset(bp.buf, 0, sizeof(bp.buf));
    bp.i_misCycleExt.esc = ESC;
    bp.i_misCycleExt.mis = 0xAD;
    bp.i_misCycleExt.stock_no = seq;
    if(ComparePrice(time))
        bp.i_misCycleExt.fg |= 0x10;
    bp.i_misCycleExt.sec = comp_price;
    bp.i_misCycleExt.open.Lint  = nOpen % 65536L;
    bp.i_misCycleExt.open.Hbyte = nOpen / 65536L;
    bp.i_misCycleExt.high.Lint  = nHigh % 65536L;
    bp.i_misCycleExt.high.Hbyte = nHigh / 65536L;
    bp.i_misCycleExt.low.Lint  = nLow % 65536L;
    bp.i_misCycleExt.low.Hbyte = nLow / 65536L;
    bp.i_misCycleExt.last.Lint  = nLast % 65536L;
    bp.i_misCycleExt.last.Hbyte = nLast / 65536L;
    bp.i_misCycleExt.deal_sheet.Lint  = nSheet % 65536L;
    bp.i_misCycleExt.deal_sheet.Hbyte = nSheet / 65536L;
    CalCheckSumAndSendToMoxaCard( bp.buf, sizeof(struct IP_MIS12_EXT)-1 );
}

void IP_CycleStkInfo(IP_FMT& prot, int market) {
    long price_o, price_h, price_l, price_c, tm_sheet, tmp_time;
    int  seq, cycle_cnt, i;

    cycle_cnt = (int) BCD_to_Long(&prot.cycle_info.stk_cnt);
    if ((cycle_cnt <=0 ) || (cycle_cnt > MAX_STK_INFO_CYCLE)) { 
        return;
    }
    if(prot.cycle_info.head.ver==0x02) {
        for(int i=0; i<cycle_cnt; i++)  {
            stock_ndx_data = SearchToyoNumberEx( prot.cycle_info_v2.stk[i].stock_no, market);
            if (stock_ndx_data != NULL) {
                seq=stock_ndx_data->ndx;
                price_o = BCD_to_Long(prot.cycle_info_v2.stk[i].open,  PRICE_FSIZE);
                price_h = BCD_to_Long(prot.cycle_info_v2.stk[i].high, PRICE_FSIZE);
                price_l = BCD_to_Long(prot.cycle_info_v2.stk[i].low, PRICE_FSIZE);
                price_c = BCD_to_Long(prot.cycle_info_v2.stk[i].last, PRICE_FSIZE);
                tm_sheet = BCD_to_Long(prot.cycle_info_v2.stk[i].deal_sheet, SHEET_FSIZE);
                tmp_time = CalTimetoTimeConvMinEx(CutMrkTestTime(BCD_to_Long(prot.cycle_info_v2.stk[i].time, TIME_FSIZE), MK_TSEC));
                if((seq >=0) &&(seq < max_TotalStockNo)) {
                        if(tm_sheet > StockMem[seq].deal_sheet)
                            IP_ReCallLostTick(seq, tmp_time, price_c, tm_sheet);
                        SendStkMdfInfo(seq, tmp_time, price_o, price_h, price_l, price_c, tm_sheet);
                }
            }
        }
    }
    else if (prot.cycle_info.head.ver==3) {
        for (int i=0; i<cycle_cnt; i++)  {
            stock_ndx_data = SearchToyoNumberEx( prot.cycle_info_v3.stk[i].stock_no, market);
            if (stock_ndx_data != NULL) {
                seq=stock_ndx_data->ndx;
                price_o = BCD_to_Long(prot.cycle_info_v3.stk[i].open, 5)/100;
                price_h = BCD_to_Long(prot.cycle_info_v3.stk[i].high, 5)/100;
                price_l = BCD_to_Long(prot.cycle_info_v3.stk[i].low, 5)/100;
                price_c = BCD_to_Long(prot.cycle_info_v3.stk[i].last, 5)/100;
                tm_sheet = BCD_to_Long(prot.cycle_info_v3.stk[i].deal_sheet, 4);
                tmp_time = CalTimetoTimeConvMinEx(CutMrkTestTime(BCD_to_Long(prot.cycle_info_v3.stk[i].time, TIME_FSIZE), MK_TSEC));   // time lengh should be 6
                if ((seq >=0) &&(seq < max_TotalStockNo)) {
                    if (tm_sheet > StockMem[seq].deal_sheet) {
                        IP_ReCallLostTick(seq, tmp_time, price_c, tm_sheet);
                    }
                    SendStkMdfInfo(seq, tmp_time, price_o, price_h, price_l, price_c, tm_sheet);
                }
            }
        }
    }
    else {
        for(int i=0; i<cycle_cnt; i++)  {
            stock_ndx_data = SearchToyoNumberEx( prot.cycle_info.stk[i].stock_no, market);
            if (stock_ndx_data != NULL) {
                seq=stock_ndx_data->ndx;
                price_o = BCD_to_Long(prot.cycle_info.stk[i].open,  PRICE_FSIZE);
                price_h = BCD_to_Long(prot.cycle_info.stk[i].high, PRICE_FSIZE);
                price_l = BCD_to_Long(prot.cycle_info.stk[i].low, PRICE_FSIZE);
                price_c = BCD_to_Long(prot.cycle_info.stk[i].last, PRICE_FSIZE);
                tm_sheet = BCD_to_Long(prot.cycle_info.stk[i].deal_sheet, SHEET_FSIZE);
                tmp_time = CalTimetoTimeConvMinEx(CutMrkTestTime(BCD_to_Long(prot.cycle_info.stk[i].time, TIME_FSIZE), MK_TSEC));
                if((seq >=0) &&(seq < max_TotalStockNo)) {
                        if(tm_sheet > StockMem[seq].deal_sheet)
                            IP_ReCallLostTick(seq, tmp_time, price_c, tm_sheet);
                        SendStkMdfInfo(seq, tmp_time, price_o, price_h, price_l, price_c, tm_sheet);
                }
            }
        }
    }
}

void IP14_MktWarrInfoNews(const IP_FMT& prot, int &fast_fg, int &updateOk_fg, char *sFileName, char *sMktString)
{
    int         d_seq;
    FILE        *pfNewsLog;
    char        strLog[256];
    char        w_no[10];
    char        w_info[50];

    if( updateOk_fg)    return;
    d_seq = BCD_to_Long( prot.mis14.head.seq, SEQ_FSIZE);

    if((pfNewsLog = _fsopen(sFileName,"a+",SH_DENYNO)) == NULL) {
        Logf("%s-檔案開啟失敗!!",sFileName);
        return;
    }
    if(fast_fg < 0)
        fast_fg = d_seq;
    if(sMktString != NULL)
        fputs(sMktString, pfNewsLog);
    else if(fast_fg == d_seq)  {
        updateOk_fg = 1;
        fclose(pfNewsLog);
        sprintf(strLog, "%s-權證全稱列表新聞更新完畢!", sMktString);
        MemoMsg(strLog);
        return;
    }
    memcpy(w_no, prot.mis14.warr_no, 6);
    w_no[6]=0;
    memcpy(w_info, prot.mis14.warr_info, 40);
    w_info[40]=0;
    sprintf(strLog, "%-10s\"%s\"\n",w_no, w_info);
    fputs(strLog, pfNewsLog);
    fclose(pfNewsLog);
}

void IP13_StkOddInfo_V2(const IP_FMT& prot, int market)
{
    int    toyo_seq, time, source_time;
    long   d_price, b_price, s_price;
    struct MARKET_TIME_15 *markTime_15;

    source_time = BCD_to_Long(prot.mis13_v2.time, TIME_FSIZE);
    if ( !memcmp(prot.mis13_v2.stock_no, "000000", 6) && (source_time == 999999)) {
        if(market == MK_TSEC)   markTime_15 = &TsecTime_15;
        else if(market == MK_OTC)     markTime_15 = &OtcTime_15;
        else      return;
        markTime_15->fg_Mis13Close = 1;
        CheckMarketClose_15(markTime_15);
    }
    else {
        toyo_seq = SearchToyoNumber( prot.mis13_v2.stock_no);
        if(toyo_seq <= 0)     return;
        time = CalTimetoTimeConvMinEx(CutMrkTestTime(source_time, MK_TSEC));
        BINFMT bp;
        memset(bp.buf, 0, sizeof(bp.buf));
        bp.i_mis13.esc = ESC;
        bp.i_mis13.mis = 0xAE;
        bp.i_mis13.fg = 0x00;
        bp.i_mis13.stock_no = toyo_seq;
        if(ComparePrice(time))
            bp.i_mis13.fg |= 0x10;
        if( !StockMem[toyo_seq].type)
            bp.i_mis13.fg |= 0x20;
        bp.i_mis13.sec = comp_price;
        d_price = BCD_to_Long(prot.mis13_v2.deal_price, PRICE_FSIZE);
        b_price = BCD_to_Long(prot.mis13_v2.buy, PRICE_FSIZE);
        s_price = BCD_to_Long(prot.mis13_v2.sell, PRICE_FSIZE);
        bp.i_mis13.deal_price.Lint  = d_price % 65536L;
        bp.i_mis13.deal_price.Hbyte = d_price / 65536L;
        bp.i_mis13.buy.Lint  = b_price % 65536L;
        bp.i_mis13.buy.Hbyte = b_price / 65536L;
        bp.i_mis13.sell.Lint  = s_price % 65536L;
        bp.i_mis13.sell.Hbyte = s_price / 65536L;
        bp.i_mis13.deal_sheet = BCD_to_Long(prot.mis13_v2.deal_sheet, ODD_SHEET_FSIZE);
        CalCheckSumAndSendToMoxaCard( bp.buf, sizeof(struct IP_MIS13)-1 );
    }
}

void IP13_StkOddInfo_V3(const IP_FMT& prot, int market)
{
    int    toyo_seq, time, source_time;
    long   d_price, b_price, s_price;
    struct MARKET_TIME_15 *markTime_15;

    source_time = BCD_to_Long(prot.mis13_v3.time, TIME_FSIZE);
    if ( !memcmp(prot.mis13_v3.stock_no, "000000", 6) && (source_time == 999999)) {
        if (market == MK_TSEC) {
            markTime_15 = &TsecTime_15;
        }
        else if(market == MK_OTC) {
            markTime_15 = &OtcTime_15;
        }
        else {
            return;
        }
        markTime_15->fg_Mis13Close = 1;
        CheckMarketClose_15(markTime_15);
    }
    else {
        toyo_seq = SearchToyoNumber( prot.mis13_v3.stock_no);
        if (toyo_seq <= 0) {
            return;
        }
        time = CalTimetoTimeConvMinEx(CutMrkTestTime(source_time, MK_TSEC));
        BINFMT bp;
        memset(bp.buf, 0, sizeof(bp.buf));
        bp.i_mis13.esc = ESC;
        bp.i_mis13.mis = 0xAE;
        bp.i_mis13.fg = 0x00;
        bp.i_mis13.stock_no = toyo_seq;
        if (ComparePrice(time)) {
            bp.i_mis13.fg |= 0x10;
        }
        if ( !StockMem[toyo_seq].type) {
            bp.i_mis13.fg |= 0x20;
        }
        bp.i_mis13.sec = comp_price;
        d_price = BCD_to_Long(prot.mis13_v3.deal_price, 5)/100;
        b_price = BCD_to_Long(prot.mis13_v3.buy, 5)/100;
        s_price = BCD_to_Long(prot.mis13_v3.sell, 5)/100;
        bp.i_mis13.deal_price.Lint  = d_price % 65536L;
        bp.i_mis13.deal_price.Hbyte = d_price / 65536L;
        bp.i_mis13.buy.Lint  = b_price % 65536L;
        bp.i_mis13.buy.Hbyte = b_price / 65536L;
        bp.i_mis13.sell.Lint  = s_price % 65536L;
        bp.i_mis13.sell.Hbyte = s_price / 65536L;
        bp.i_mis13.deal_sheet = BCD_to_Long(prot.mis13_v3.deal_sheet, 6);
        CalCheckSumAndSendToMoxaCard( bp.buf, sizeof(struct IP_MIS13)-1 );
    }
}

void IP13_StkOddInfo(const IP_FMT& prot, int market)
{
    struct CCCC *stk_inx;
    int    toyo_seq, time, source_seq, source_time;
    long   d_price, b_price, s_price;
    struct MARKET_TIME *markTime;
    struct MARKET_TIME_15 *markTime_15;

    source_seq = (int)BCD_to_Long(prot.mis13.stock_seq, STK_SEQ_FSIZE);
    source_time = BCD_to_Long(prot.mis13.time, TIME_FSIZE);
    if( !source_seq && (source_time == 999999)) {
        if(market == MK_TSEC)   markTime_15 = &TsecTime_15;
        else if(market == MK_OTC)     markTime_15 = &OtcTime_15;
        else      return;
        markTime_15->fg_Mis13Close = 1;
        CheckMarketClose_15(markTime_15);
    }
    else {
        stk_inx=Seq_to_Toyo(source_seq, market);
        time = CalTimetoTimeConvMinEx(CutMrkTestTime(source_time, MK_TSEC));
        if(stk_inx == NULL)     return;
        toyo_seq=stk_inx->ndx;

        BINFMT bp;
        memset(bp.buf, 0, sizeof(bp.buf));
        bp.i_mis13.esc = ESC;
        bp.i_mis13.mis = 0xAE;
        bp.i_mis13.fg = 0x00;
        bp.i_mis13.stock_no = toyo_seq;
        if(ComparePrice(time))
            bp.i_mis13.fg |= 0x10;
        if( !StockMem[toyo_seq].type)
            bp.i_mis13.fg |= 0x20;
        bp.i_mis13.sec = comp_price;
        d_price = BCD_to_Long(prot.mis13.deal_price, PRICE_FSIZE);
        b_price = BCD_to_Long(prot.mis13.buy, PRICE_FSIZE);
        s_price = BCD_to_Long(prot.mis13.sell, PRICE_FSIZE);
        bp.i_mis13.deal_price.Lint  = d_price % 65536L;
        bp.i_mis13.deal_price.Hbyte = d_price / 65536L;
        bp.i_mis13.buy.Lint  = b_price % 65536L;
        bp.i_mis13.buy.Hbyte = b_price / 65536L;
        bp.i_mis13.sell.Lint  = s_price % 65536L;
        bp.i_mis13.sell.Hbyte = s_price / 65536L;
        bp.i_mis13.deal_sheet = BCD_to_Long(prot.mis13.deal_sheet, ODD_SHEET_FSIZE);
        CalCheckSumAndSendToMoxaCard( bp.buf, sizeof(struct IP_MIS13)-1 );
    }
}

void Long_to_BCD(long data, unsigned char *buffer, int num = 1)
{
    unsigned long c_value = (unsigned long)data;
    int i;
    for(i = num-1; i >= 0; i--) {
        unsigned long cut = c_value % 100L;
        buffer[i] = ((cut/10) << 4) + (cut%10);
        c_value = c_value / 100L;
    }
}

//修正盤前試撮合的總量,以便符合tick規格的定義
//交易所的是搓合單量，但是系統要處理總量 所以要修正交易所的格式
//將試撮合的量總和起來變總量,這樣才可以顯示tick
void fix_pre_total_volume(IP_FMT& prot, int toyo)
{
    if(!((unsigned char)(prot.mis6_v3.state) & 0x80))
        return;
    long pre_volume;
    int offset = SHEET_FSIZE;
    //有試算成交量
    if(((unsigned char)(prot.mis6_v3.field_fg)) & _DEAL) {
        pre_volume =  BCD_to_Long(prot.mis6_v3.deal_sheet+offset+PRICE_FSIZE, SHEET_FSIZE);
        StockPre[toyo].total_volume += pre_volume;
        Long_to_BCD(StockPre[toyo].total_volume, prot.mis6_v3.deal_sheet, SHEET_FSIZE);
    }
}

void fix_pre_total_volume_v4(IP_FMT& prot, int toyo)
{
    //非試算揭示
    if (!((unsigned char)(prot.mis6_v4.state) & 0x80)) {
        return;
    }
    long pre_volume;
    //有試算成交量
    if (((unsigned char)(prot.mis6_v4.field_fg)) & _DEAL) {
        pre_volume = BCD_to_Long(prot.mis6_v4.deal_sheet+4+5, 4);
        StockPre[toyo].total_volume += pre_volume;
        Long_to_BCD(StockPre[toyo].total_volume, prot.mis6_v4.deal_sheet, 4);
    }
}

void fix_mis20_pre_total_volume(IP_FMT& prot) {
    int toyo = SearchToyoNumber(prot.mis20_v1.stock_no);
    if (toyo <= 0) {
        return;
    }
    if ( !((prot.mis20_v1.state) & 0x80) ) {    //非試算揭示
        return;
    }
    long pre_volume;
    int offset = SHEET_FSIZE;
    if(((unsigned char)(prot.mis20_v1.field_fg)) & _DEAL) {    //有試算成交量
        pre_volume = BCD_to_Long(prot.mis20_v1.deal_sheet+4+5, 4);
        StockPre[toyo].total_volume += pre_volume;
        Long_to_BCD(StockPre[toyo].total_volume, prot.mis20_v1.deal_sheet, 4);
    }
}

int ProcTSE(IP_FMT& prot, int mis, int market, int lineID) {
    static int fmt1_lineID = -1;
    struct CCCC *stk;
    int toyo_seq, stkopt5_seq;
    int fg_WriteStable = 0;
    int fg_WriteDelayClose = 0;
    
    switch(mis) {
        case 1: //  個股今日參考價漲停跌停
            if (fmt1_lineID==-1) {
                fmt1_lineID = lineID;
            }
            else if (fmt1_lineID!=lineID) {
                break;
            }
            StartReceOtc=1;
            if (!fur_Ready_open)  {
                IpMis1UpdateToMemAndSend_V8(prot, market);
            }
            break;
        case 2: // 大盤成交張筆值
            StartReceOtc=1;
            gMis15Ver = 1;
            CV2_MisTotalAmountSheetCount_15(prot, 0, market);
            break;
        case 3: // 各類指數
            StartReceOtc=1;
            if(gMis15Ver < 0)    break;
            if( gMis15Ver)  {
                TsecMis3_15(prot, market);
            }
            else {
                Test15_TsecMis3(prot, market,-2000, -3);
                Test15_TsecMis3(prot, market, 5000, -2);
                Test15_TsecMis3(prot, market, 2000, -1);
                Test15_TsecMis3(prot, market, 0, 0);
            }
            break;
        case 4:
            StartReceOtc=1;
            gMis15Ver = 1;
            CV2_TsecMis4_15(prot, 0, market);
            break;
        case 5: // 消息
            StartReceOtc=1;
            TsecNewsUpdateToMemAndSend(prot, market);
            break;
        case 6: // buy price ,sell price ,deal price ,deal sheet
        case 17:
            StartReceOtc=1;
            toyo_seq = SearchToyoNumber(prot.mis6_v3.stock_no);
            if (!fg_Open) {
                fg_Open =1;
            }
            if (toyo_seq <= 0) {
                return 1;
            }
            if (prot.mis6_v3.head.ver==3) {  //修正盤前試撮合的總量,以便符合tick規格的定義
                fix_pre_total_volume(prot, toyo_seq);
            }
            else if (prot.mis6_v3.head.ver==4) {
                fix_pre_total_volume_v4(prot, toyo_seq);
            }
            if (prot.mis6_v3.up_down & 0x03) {  //瞬間價格趨勢
                fg_WriteStable = 1;
                StockMem[toyo_seq].updown_flag |= ((prot.mis6_v3.up_down & 0x03));
				last_pause_flag[toyo_seq] = prot.mis6_v3.up_down & 0x03;
				
				long tmp_time = BCD_to_Long(prot.mis6_v3.time, TIME_FSIZE);
				if(tmp_time >= 133100)
					tmp_time = 133059;  //因應延後收盤機制..
				last_pause_time[toyo_seq] = CalTimetoTimeConvMinEx(CutMrkTestTime(tmp_time, MK_TSEC));
            }
            else {
                if(StockMem[toyo_seq].updown_flag & 0x03) {
                    fg_WriteStable = 1;
                    StockMem[toyo_seq].updown_flag &= ~(0x03);
                }
            }
            if((prot.mis6_v3.state & BIT7) == BIT7) {  //試算揭示
                if((prot.mis6_v3.state & BIT5) == BIT5) {  //試算後延後收盤
                    if( (StockMem[toyo_seq].warn_flag & BIT5) != BIT5) {  //之前的狀態非試算後延後收盤 起動新聞flag
                        fg_WriteDelayClose = 1;
                    }
                }
            }
            StockMem[toyo_seq].warn_flag = (prot.mis6_v3.state & 0xf0);
            if (prot.mis6_v3.head.ver==3) {
                IP_Mis2UpdateToMemAndSend_V3(prot, toyo_seq);
            }
            else if (prot.mis6_v3.head.ver==4) {
                IP_Mis2UpdateToMemAndSend_V4(prot, toyo_seq);
            }
            #ifdef DBG_STK_TICK
                LogTraceStkTick(toyo_seq);
            #endif
            if(fg_WriteStable && fg_stable_file)
                WriteStableStockFile();
            if(fg_WarrInfoNews && fg_WriteDelayClose)
                WriteDelayCloseFile();
            break;
        case 7:
            CV2_MisTotalAmountSheetCount_15(prot, 1, market);
            break;
        case 8: // 買賣張筆
            CV2_TsecMis4_15(prot, 1, market);
            break;
        case 9:
            toyo_seq=SearchToyoNumber(prot.mis9_v2.stock_no);
            if(toyo_seq <= 0)    return 1;
            StockMem[toyo_seq].time = CalTimetoTimeConvMinEx(CutMrkTestTime(BCD_to_Long(prot.mis9_v2.time, 3), MK_TSEC));
            if(FixedPriceTrade[ market-1 ].Toyo < 0)
                FixedPriceTrade[ market-1 ].Toyo = toyo_seq;
            else if(FixedPriceTrade[ market-1 ].Toyo == toyo_seq)
                    FixedPriceTrade[ market-1 ].Ok = 1;
            if (prot.mis9_v2.head.ver==2) {
                IP_FixedPriceTradeUpdateToMemAndSend_V2(prot, toyo_seq);
            }
            else if (prot.mis9_v2.head.ver==3) {
                IP_FixedPriceTradeUpdateToMemAndSend_V3(prot, toyo_seq);
            }
            break;
        case 10:
            NewTaiwanIndex(prot);
            break;
        case 12:
        case 18:
            IP_CycleStkInfo(prot, market);
            break;
        case 13:
            if (prot.mis13.head.ver==0x02)
                IP13_StkOddInfo_V2(prot, market);
            else if (prot.mis13.head.ver==3) {
                IP13_StkOddInfo_V3(prot, market);
            }
            break;
        case 14:
            if( fg_WarrInfoNews) {
                nTsecWarrCnt++;
                if(nTsecWarrCnt > (nMaxWarrNewsCnt*2))
                    IP14_MktWarrInfoNews(prot, nTsecWarrFast_fg, nTsecWarrUpdateOk_fg, sTsecWarrInfNewsFN_3,
                                                        (((nTsecWarrCnt % nMaxWarrNewsCnt)==1)?"集中市場-權證全稱列表-3\n":NULL));
                else if(nTsecWarrCnt > nMaxWarrNewsCnt)
                    IP14_MktWarrInfoNews(prot, nTsecWarrFast_fg, nTsecWarrUpdateOk_fg, sTsecWarrInfNewsFN_2,
                                                        (((nTsecWarrCnt % nMaxWarrNewsCnt)==1)?"集中市場-權證全稱列表-2\n":NULL));
                else
                    IP14_MktWarrInfoNews(prot, nTsecWarrFast_fg, nTsecWarrUpdateOk_fg, sTsecWarrInfNewsFN_1,
                                                        (((nTsecWarrCnt % nMaxWarrNewsCnt)==1)?"集中市場-權證全稱列表-1\n":NULL));
            }
            break;        
        case 19:
            StkStopRecoverStat(prot);
            break;            
        case 20:
            on_mis20_v1(prot);
            break;
        case 15:
        case 16:
        case 21:
            break;
        default:
            return 0;
    }
    return 1;
}

int ProcOTC(IP_FMT& prot, int mis, int market, int lineID) {
    static int fmt1_lineID = -1;
    struct CCCC *stk;
    int toyo_seq, stkopt5_seq;
    int fg_WriteStable = 0;
    int fg_WriteDelayClose = 0;
    switch(mis) {
        case 1: //  個股今日參考價漲停跌停
            if (fmt1_lineID==-1) {
                fmt1_lineID = lineID;
            }
            else if (fmt1_lineID!=lineID) {
                break;
            }
            StartReceOtc=1;
            if (!fur_Ready_open)  {
                IpMis1UpdateToMemAndSend_V8(prot, market);
            }
            break;
        case 2: // 大盤成交張筆值
            StartReceOtc=1;
            gMis15Ver = 1;
            CV2_MisTotalAmountSheetCount_15(prot, 0, market);
            break;
        case 3: // 各類指數
            StartReceOtc=1;
            if(gMis15Ver < 0)    break;
            if( gMis15Ver)  {
                TsecMis3_15(prot, market);
            }
            else {
                Test15_TsecMis3(prot, market,-2000, -3);
                Test15_TsecMis3(prot, market, 5000, -2);
                Test15_TsecMis3(prot, market, 2000, -1);
                Test15_TsecMis3(prot, market, 0, 0);
            }
            break;
        case 4:
            StartReceOtc=1;
            gMis15Ver = 1;
            CV2_TsecMis4_15(prot, 0, market);
            break;
        case 5: // 消息
            StartReceOtc=1;
            TsecNewsUpdateToMemAndSend(prot, market);
            break;
        case 6: // buy price ,sell price ,deal price ,deal sheet
        case 17:
            StartReceOtc=1;
            toyo_seq = SearchToyoNumber(prot.mis6_v3.stock_no);
            if (!fg_Open) {
                fg_Open =1;
            }
            if (toyo_seq <= 0) {
                return 1;
            }
            if (prot.mis6_v3.head.ver==3) {  //修正盤前試撮合的總量,以便符合tick規格的定義
                fix_pre_total_volume(prot, toyo_seq);
            }
            else if (prot.mis6_v3.head.ver==4) {
                fix_pre_total_volume_v4(prot, toyo_seq);
            }
            if (prot.mis6_v3.up_down & 0x03) {  //瞬間價格趨勢
                fg_WriteStable = 1;
                StockMem[toyo_seq].updown_flag |= ((prot.mis6_v3.up_down & 0x03));
				last_pause_flag[toyo_seq] = prot.mis6_v3.up_down & 0x03;				
				
				long tmp_time = BCD_to_Long(prot.mis6_v3.time, TIME_FSIZE);
				if(tmp_time >= 133100)
					tmp_time = 133059;  //因應延後收盤機制..
				last_pause_time[toyo_seq] = CalTimetoTimeConvMinEx(CutMrkTestTime(tmp_time, MK_TSEC));				
            }
            else {
                if(StockMem[toyo_seq].updown_flag & 0x03) {
                    fg_WriteStable = 1;
                    StockMem[toyo_seq].updown_flag &= ~(0x03);
                }
            }
            if((prot.mis6_v3.state & BIT7) == BIT7) {  //試算揭示
                if((prot.mis6_v3.state & BIT5) == BIT5) {  //試算後延後收盤
                    if( (StockMem[toyo_seq].warn_flag & BIT5) != BIT5) {  //之前的狀態非試算後延後收盤 起動新聞flag
                        fg_WriteDelayClose = 1;
                    }
                }
            }
            StockMem[toyo_seq].warn_flag = (prot.mis6_v3.state & 0xf0);
            if (prot.mis6_v3.head.ver==3) {
                IP_Mis2UpdateToMemAndSend_V3(prot, toyo_seq);
            }
            else if (prot.mis6_v3.head.ver==4) {
                IP_Mis2UpdateToMemAndSend_V4(prot, toyo_seq);
            }            
            #ifdef DBG_STK_TICK
                LogTraceStkTick(toyo_seq);
            #endif
            if(fg_WriteStable && fg_stable_file)
                WriteStableStockFile();
            if(fg_WarrInfoNews && fg_WriteDelayClose)
                WriteDelayCloseFile();
            break;
        case 7:
            CV2_MisTotalAmountSheetCount_15(prot, 1, market);
            break;
        case 8: // 買賣張筆
            CV2_TsecMis4_15(prot, 1, market);
            break;
        case 9:
            toyo_seq=SearchToyoNumber(prot.mis9_v2.stock_no);
            if(toyo_seq <= 0)    return 1;
            StockMem[toyo_seq].time = CalTimetoTimeConvMinEx(CutMrkTestTime(BCD_to_Long(prot.mis9_v2.time, 3), MK_TSEC));
            if(FixedPriceTrade[ market-1 ].Toyo < 0)
                FixedPriceTrade[ market-1 ].Toyo = toyo_seq;
            else if(FixedPriceTrade[ market-1 ].Toyo == toyo_seq)
                    FixedPriceTrade[ market-1 ].Ok = 1;
            if (prot.mis9_v2.head.ver==2) {
                IP_FixedPriceTradeUpdateToMemAndSend_V2(prot, toyo_seq);
            }
            else if (prot.mis9_v2.head.ver==3) {
                IP_FixedPriceTradeUpdateToMemAndSend_V3(prot, toyo_seq);
            }
            break;
        case 10:
            if (fg_OtcFixBsData) {
                toyo_seq = SearchToyoNumber(prot.otc_mis10_v2.stock_no);					
                if (prot.otc_mis10_v2.head.ver==0x02) {
                    IP_FixedPriceBuySellUpdateToMemAndSend_V2(prot, toyo_seq);
                }
                else if (prot.otc_mis10_v2.head.ver==0x03) {
                    IP_FixedPriceBuySellUpdateToMemAndSend_V3(prot, toyo_seq);
                }
            }
            break;
        case 11:
            IP_CycleStkInfo(prot, market);
            break;
        case 12:
            NewOtcTaiIndex(prot);
            break;
        case 13:
            if (prot.mis13.head.ver==0x02)
                IP13_StkOddInfo_V2(prot, market);
            else if (prot.mis13.head.ver==3) {
                IP13_StkOddInfo_V3(prot, market);
            }
            break;
        case 14:
            if( fg_WarrInfoNews) {
                IP14_MktWarrInfoNews(prot, nOtcWarrFast_fg, nOtcWarrUpdateOk_fg, sOtcWarrInfNewsFN,
                        ((nOtcWarrFast_fg<0)?"櫃買中心-權證全稱列表\n":NULL));
            }
            break;
        case 18:
            IP_CycleStkInfo(prot, market);
            break;
        case 19:
            StkStopRecoverStat(prot);
            break;            
        case 20:
            on_mis20_v1(prot);
            break;
        case 15:
        case 16:
        case 21:
            break;
        default:
            return 0;
    }
    return 1;
}

int RcvMis(bool isMaster, bool hasSlave, int lineID) {
    LineInfo * pLi = &(gLI[lineID]);
    MTRingBuffer* ring = &(gLI[lineID].ring);
    int szOnEntry = ring->size();
    int startParseCnt = pLi->parsecnt;	
    iphd Current;
    long protSz, mkt, mis, newSeq, currseq;
    char dropbuf[256];
    while (true) {
        int escPos = ring->indexof(ESC);
        if (escPos>0) {
            size_t dropbufsz = min(256, escPos);
            ring->read( dropbuf, dropbufsz );
            ring->remove( escPos-dropbufsz );
            pLi->parsecnt += escPos;
            Logf("parse err mis, find esc, drop sz=%d", escPos);
            Logb(dropbuf, dropbufsz);
        }
        else if (escPos<0) {
            return SizeNotEnough;
        }
        if (ring->size()<IP_MIN_LEN) {
            return SizeNotEnough;
        }
        size_t peekSz = ring->peek( (char*)(&Current.esc), sizeof(iphd) );
        protSz = BCD_to_Long(Current.length, LENGTH_FSIZE);
        if (protSz >= MAX_IP_FMT_SIZE) {
            ++(pLi->prot_err_cnt);
            ring->read(dropbuf,1);
            pLi->parsecnt += 1;
            Logf("parse err mis, too long, drop sz=%d[%x], given sz=%d", 1, dropbuf[0], protSz);
            continue;
        }
        if ( ring->size()<protSz ) {
            return SizeNotEnough;
        }
        IP_FMT prot;
        ring->peek( (char*)&prot, protSz );
        char givenChksum = prot.buf[1];
        for ( int i=2; i<protSz-3; ++i ) {
            givenChksum ^= prot.buf[i];
        }
        if (givenChksum!=prot.buf[protSz-3]) {
            ++(pLi->prot_err_cnt);
            ring->read(dropbuf,1);
            Logf("parse err mis, chksum, drop sz=%d[%x]", 1, dropbuf[0]);
            pLi->parsecnt += 1;
            continue;
        }
        mkt = BCD_to_Long(&Current.market);
        mis = BCD_to_Long(&Current.mis);
        if ((mkt-1)<0 || (mkt-1)>=2 || (mis-1)<0 || (mis-1)>MAX_MIS) {
            ++(pLi->prot_err_cnt);
            ring->read(dropbuf,1);
            Logf("parse err mis, ilegal mkt=%d, mis=%d, drop sz=1[%x]", mkt, mis, dropbuf[0]);
            pLi->parsecnt += 1;
            continue;          
        }
        
        newSeq = BCD_to_Long( Current.seq, SEQ_FSIZE );
        if ( isMaster ) {
            if ( hasSlave ) {
                if (mis!=17 && mis!=6 && mis!=13) {
                    goto skip_check_leak_otc2;
                }
            }
            else {
                goto skip_check_leak_otc2;
            }
        }
        else {
            if (mis!=17 && mis!=6 && mis!=13) {
                continue;
            }
        }
        currseq = gTseSeq[mkt-1][mis-1];
        if ( (currseq+1)<newSeq ) {
            if ( pLi->BypassCount>4 ) {
                pLi->BypassCount = 0;
            }
            else {
                pLi->BypassCount += 1;
                return WaitForSeqno;
            }
        }
        else if ( currseq>=newSeq ) {
            pLi->BypassCount = 0;
            ring->remove(protSz);
            pLi->parsecnt += protSz;
            continue;
        }
        else {
            pLi->BypassCount = 0;
        }
    skip_check_leak_otc2:
        gTseSeq[mkt-1][mis-1] = newSeq;
        int procRes;
        if (mkt==MK_TSEC) {
            procRes = ProcTSE(prot, mis, mkt, lineID);
            gStat.tse_dodata = 1;
        }
        else if (mkt==MK_OTC) {
            procRes = ProcOTC(prot, mis, mkt, lineID);
            gStat.otc_dodata = 1;
        }
        if (!procRes) { //UnKnow Protocol
            ++(pLi->prot_err_cnt);
            ring->read(dropbuf,1);
            pLi->parsecnt += 1;
            Logf("parse err mis, unknown prot, drop sz=%d[%x]", 1, dropbuf[0]);
            continue;
        }
        else {
            ring->remove(protSz);
            pLi->parsecnt += protSz;
            market_chk[mkt-1].chk_clock = 0l;
        }
        if ((pLi->parsecnt-startParseCnt)>min(szOnEntry,1024*1024)) {
            return BufferSwitch;
        }
    }
}

int WriteTsecOtcBusInfo(void)
{
    FILE *handle;
    char  sBuf[128], StkName[8];
    char  TodayDate[10];

    handle = _fsopen("DAYINFO\\TSECODE.DAT", "w+b", SH_DENYRW);
    if (handle==NULL)   return -1;

    sprintf(TodayDate, "%04d%02d%02d", NowSystemYear, NowSystemMonth, NowSystemDay);
    for(int i=0;i<max_TotalStockNo;i++) {
        if(StockMem[i].mkt == MK_TSEC || StockMem[i].mkt == MK_OTC) {
            memcpy(StkName, StockMem[i].stock_no, 6);
            StkName[6]=0;
            sprintf(sBuf, "%s %6s %C%C %C%C %02d\x0d\x0a",
                TodayDate, StkName,
                StockMem[i].business[0], StockMem[i].business[1],
                StockMem[i].br[0], StockMem[i].br[1],
                StockMem[i].excep);
            fwrite(sBuf, sizeof(char), strlen(sBuf), handle);
        }
    }
    fclose(handle);
    fg_wBufInfo = 1;
    return 0;

}

int WriteTsecOtcTodaySet(void)
{
    FILE *handle;
    char  sBuf[128], StkName[8];
    char cmd_buf[128];

    handle = _fsopen("DAYINFO\\UD_STOP.DAT", "w+b", SH_DENYRW);
    if (handle==NULL)   return -1;

    sprintf(sBuf, "%04d%02d%02d\x0d\x0a", NowSystemYear, NowSystemMonth, NowSystemDay);
    fwrite(sBuf, sizeof(char), strlen(sBuf), handle);

    for(int i=0;i<max_TotalStockNo;i++) {
        if(StockMem[i].mkt == MK_TSEC || StockMem[i].mkt == MK_OTC) {
            memcpy(StkName, StockMem[i].stock_no, 6);
            StkName[6]=0;
            if(StockMem[i].y_close > 0)
                sprintf(sBuf, "%6s, %8d, %8d, %8d\x0d\x0a",
                    StkName,
                    StockMem[i].y_close, StockMem[i].up_bound,
                    StockMem[i].dn_bound);
            else
                sprintf(sBuf, "%6s,         ,         ,\x0d\x0a", StkName);

            fwrite(sBuf, sizeof(char), strlen(sBuf), handle);
        }
    }
    fclose(handle);
    fg_wBufInfo = 1;
    sprintf(cmd_buf,"mkcrc %s 1", "DAYINFO\\UD_STOP.DAT");
    system(cmd_buf);
	//int x = spawnl(P_NOWAIT, "mkcrc", "DAYINFO\\UD_STOP.DAT", "1");
    return 0;

}

int WriteTsecOtcTodayDealCnt(void)
{
    FILE *handle;
    char  sBuf[128], StkName[8];
    char  TodayDate[10];

    handle = _fsopen("TseClose.dat", "w+b", SH_DENYRW);
    if (handle==NULL)   return -1;

    for(int i=0;i<max_TotalStockNo;i++) {
        if(StockMem[i].mkt == MK_TSEC || StockMem[i].mkt == MK_OTC) {
            memcpy(StkName, StockMem[i].stock_no, 6);
            StkName[6]=0;
            sprintf(sBuf, "%6s %010ld\x0d\x0a", StkName, StockMem[i].index);
            fwrite(sBuf, sizeof(char), strlen(sBuf), handle);
        }
    }
    fclose(handle);
    return 0;
}

void ReadTsecOtcYesDealCnt()
{
    char stock_name[32], y_deal[32];
    FILE *stk_fs;
    int y_index, seq;

    if((stk_fs = fopen("TseClose.dat","r")) != NULL ){
        memset(stock_name,0,6);
        while( fscanf(stk_fs,"%s %s",stock_name, y_deal)>1 ){
            if(stock_name[4]=='\0'){
                stock_name[4]=' ';
            }
            stock_name[5]=' ';
            stock_name[6]='\0';
            if(y_deal != NULL)
                y_index=atoi(y_deal);
            seq = SearchToyoNumber( stock_name);
            if (seq > 0){
                StockMem[seq].y_index=y_index;
            }
        }
        fclose(stk_fs);
    }
}

#ifdef    DBG_STK_TICK

int read_dbg_stk_ini(char *filename)
{
   char key_buffer[20];
   char strTemp[64];
    int seq, i;
    dbg_trace_cnt = GetPrivateProfileInt( "dump_stock", "ds_count", 0, filename);
    if(dbg_trace_cnt>5)
        dbg_trace_cnt = 5;
    for(i=0; i<dbg_trace_cnt; i++) {
        sprintf(key_buffer, "ds_stock%d", i+1);
        GetPrivateProfileString("dump_stock", key_buffer, "", strTemp, 64, filename);
        strcpy(dbg_trace_stk[i].name, strTemp);
        if(strTemp[4] == 0) {
            strTemp[4] = ' ';
            strTemp[5] = ' ';
        }
        else if(strTemp[5] == 0)
            strTemp[5] = ' ';
        strTemp[6] = 0;

        if( (seq=SearchToyoNumber(strTemp)) > 0 )
            dbg_trace_stk[i].toyo =  seq;
        else
            return 0;
    }
    return 1;
}

int LogTraceStkTick(int seq)
{
    int     i;
    FILE    *pfStkDebugLog;
    char    sFilename[32], strTemp[1024], sMsgTime[16], sDealTime[16];
    TDateTime       dtLogDateTime;
    Word Hour, Min, Sec, MSec;
    for(i=0; i<dbg_trace_cnt; i++) {
        if(dbg_trace_stk[i].toyo ==  seq)   {
            sprintf(sFilename, "%s.txt", dbg_trace_stk[i].name);

            if((pfStkDebugLog = _fsopen(sFilename,"a+",SH_DENYNO)) == NULL) {
                return 0;
            }
            dtLogDateTime = Now();
            DecodeTime(dtLogDateTime, Hour, Min, Sec, MSec);
            sprintf(sMsgTime, "%02d:%02d:%02d.%03d", Hour, Min, Sec, MSec);
            sprintf(sDealTime,"%02d:%02d:%02d", StockMem[seq].time /3600l, (StockMem[seq].time /60l)%60l, StockMem[seq].time %60l);

            sprintf(strTemp, "%s,%ld,%s,%.2f,%ld,%.2f,%ld,%.2f,%ld,%.2f,%ld,%.2f,%ld,%.2f,%ld,%.2f,%ld,%.2f,%ld,%.2f,%ld,%.2f,%ld,%.2f,%ld\n",
                                sMsgTime, dbg_stk_seqNo, sDealTime, StockMem[seq].deal_price/100.0, StockMem[seq].deal_sheet,
 StockMem[seq].buy_price[0]/100.0, StockMem[seq].buy_sheet[0], StockMem[seq].buy_price[1]/100.0, StockMem[seq].buy_sheet[1],
 StockMem[seq].buy_price[2]/100.0, StockMem[seq].buy_sheet[2], StockMem[seq].buy_price[3]/100.0, StockMem[seq].buy_sheet[3],
 StockMem[seq].buy_price[4]/100.0, StockMem[seq].buy_sheet[4],

 StockMem[seq].sell_price[0]/100.0, StockMem[seq].sell_sheet[0], StockMem[seq].sell_price[1]/100.0, StockMem[seq].sell_sheet[1],
 StockMem[seq].sell_price[2]/100.0, StockMem[seq].sell_sheet[2], StockMem[seq].sell_price[3]/100.0, StockMem[seq].sell_sheet[3],
 StockMem[seq].sell_price[4]/100.0, StockMem[seq].sell_sheet[4]);
            fputs(strTemp, pfStkDebugLog);
            fclose(pfStkDebugLog);
            return 1;
        }
    }
    return 0;
}

#endif
#pragma package(smart_init)
