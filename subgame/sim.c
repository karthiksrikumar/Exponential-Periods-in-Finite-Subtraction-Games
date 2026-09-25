// simulate subtraction game outcomes: w[n]=1 (P) iff all w[n-s]=0. Read S from file. Output packed bytes.
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); long long N=atoll(argv[2]); int S[20000],k=0; while(fscanf(f,"%d",&S[k])==1)k++; fclose(f);
  // sort S ascending
  for(int i=0;i<k;i++)for(int j=i+1;j<k;j++)if(S[j]<S[i]){int t=S[i];S[i]=S[j];S[j]=t;}
  unsigned char*w=calloc(N,1);
  for(long long n=0;n<N;n++){ int v=1; for(int i=0;i<k && S[i]<=n;i++) if(w[n-S[i]]){v=0;break;} w[n]=v; }
  FILE*o=fopen(argv[3],"wb"); fwrite(w,1,N,o); fclose(o); return 0;
}
