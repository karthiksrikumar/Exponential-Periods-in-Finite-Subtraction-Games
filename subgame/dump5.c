#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static unsigned long long period_pure(int m, u128 M, unsigned long long cap){
  u128 FULL=(((u128)1)<<m)-1, R=0; unsigned long long t=0;
  do { u128 nb=((R&M)==0); R=((R<<1)|nb)&FULL; t++; if(t>cap) return 0; } while(R!=0);
  return t;
}
int main(int argc,char**argv){
  int m0=atoi(argv[1]), m1=atoi(argv[2]); unsigned long long cap=strtoull(argv[3],0,10);
  for(int m=m0;m<=m1;m++) for(int a=1;2*a<m;a++) for(int b=a+1;2*b<m;b++){
      u128 M=((u128)1<<(a-1))|((u128)1<<(b-1))|((u128)1<<(m-b-1))|((u128)1<<(m-a-1))|((u128)1<<(m-1));
      printf("%d %d %d %llu\n",m,a,b,period_pure(m,M,cap));
  }
}
