// For each m in [m0,m1], all max-symmetric 5-move sets S={a,b,m-b,m-a,m}, 1<=a<b<m/2 (b!=m-b).
// Purely periodic (Flammenkamp Thm 12): period = first t>0 with state(t)==state(0)... careful: state(0)=initial R0=0
// Pure periodicity means the state sequence from R0 is purely periodic -> return to R0.
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
  for(int m=m0;m<=m1;m++){
    unsigned long long best=0; int ba=0,bb=0; int ncap=0;
    for(int a=1;2*a<m;a++) for(int b=a+1;2*b<m;b++){
      u128 M=((u128)1<<(a-1))|((u128)1<<(b-1))|((u128)1<<(m-b-1))|((u128)1<<(m-a-1))|((u128)1<<(m-1));
      unsigned long long p=period_pure(m,M,cap);
      if(p==0){ncap++; continue;}
      if(p>best){best=p;ba=a;bb=b;}
    }
    printf("m=%d best_period=%llu S={%d,%d,%d,%d,%d} capped=%d\n",m,best,ba,bb,m-bb,m-ba,m,ncap); fflush(stdout);
  }
}
