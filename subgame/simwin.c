// Fast subtraction-game simulator for sparse P-sets: w(n)=1 iff no P-position p in [n-maxS,n) with n-p in S.
// usage: simwin S.txt N out.bin
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); long long N=atoll(argv[2]);
  long long cap=1<<20, ns=0; long long *S=malloc(cap*sizeof(long long)); long long x, maxS=0;
  while(fscanf(f,"%lld",&x)==1){ if(ns==cap){cap*=2;S=realloc(S,cap*sizeof(long long));} S[ns++]=x; if(x>maxS)maxS=x; }
  fclose(f);
  unsigned char *inS=calloc(maxS+1,1); for(long long i=0;i<ns;i++) inS[S[i]]=1;
  unsigned char *w=malloc(N);
  long long *P=malloc(sizeof(long long)*(N/2+16)); long long head=0, tail=0; // P positions in increasing order; window [head,tail)
  for(long long n=0;n<N;n++){
    while(head<tail && P[head] < n-maxS) head++;
    int v=1;
    for(long long j=tail-1;j>=head;j--){ if(inS[n-P[j]]){v=0;break;} }
    w[n]=v; if(v) P[tail++]=n;
  }
  FILE*o=fopen(argv[3],"wb"); fwrite(w,1,N,o); fclose(o);
  printf("done N=%lld |S|=%lld maxS=%lld Pcount=%lld\n",N,ns,maxS,tail);
  return 0;
}
