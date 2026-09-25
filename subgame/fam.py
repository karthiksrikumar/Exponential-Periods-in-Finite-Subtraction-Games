import math, collections
P={}
for line in open('p5.txt'):
    m,a,b,p=map(int,line.split()); P[(m,a,b)]=p
# families: (a,b) fixed ; (a, g=m-2b) fixed ; (c=m-2a? ...) ; also (b-a, m) combos via lines
def fam_eval(seq):
    # seq: list of (t, p); growth = slope of log2 p over t via least squares, and min p
    pts=[(t,math.log2(p)) for t,p in seq if p>0]
    if len(pts)<6: return None
    n=len(pts); mt=sum(t for t,_ in pts)/n; ml=sum(l for _,l in pts)/n
    sxx=sum((t-mt)**2 for t,_ in pts); sxy=sum((t-mt)*(l-ml) for t,l in pts)
    slope=sxy/sxx
    res=sum((l-ml-slope*(t-mt))**2 for t,l in pts)/n
    return slope,res,n
out=[]
# family type A: fixed a, fixed g=m-2b, vary m (with parity)
for a in range(1,20):
    for g in range(1,40):
        seq=[(m,P[(m,a,(m-g)//2)]) for m in range(5,67) if (m-g)%2==0 and (m,a,(m-g)//2) in P]
        r=fam_eval(seq)
        if r: out.append((r[0],r[1],'a=%d,g=m-2b=%d'%(a,g),seq[-3:]))
# type B: fixed a,b vary m
for a in range(1,20):
    for b in range(a+1,30):
        seq=[(m,P[(m,a,b)]) for m in range(5,67) if (m,a,b) in P]
        r=fam_eval(seq)
        if r: out.append((r[0],r[1],'a=%d,b=%d'%(a,b),seq[-3:]))
# type C: fixed d=b-a and g=m-2b, vary a  (m = 2b+g)
for d in range(1,30):
    for g in range(1,30):
        seq=[]
        for a in range(1,40):
            b=a+d; m=2*b+g
            if (m,a,b) in P: seq.append((a,P[(m,a,b)]))
        r=fam_eval(seq)
        if r: out.append((r[0],r[1],'d=b-a=%d,g=%d (vary a, m=2a+2d+g)'%(d,g),seq[-3:]))
out.sort(key=lambda x:-x[0])
for o in out[:40]: print('%.3f res=%.3f %s %s'%o)
