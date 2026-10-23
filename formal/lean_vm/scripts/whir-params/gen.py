exec(open('est.py').read())
from math import log2
S=2**40; N=2**22
def cd(a,b): return (a+b-1)//b
def sqrtcert(kappa,R):
  n=2**(kappa+R); D=2**kappa-1
  s=isqrt(D*S*S//n)
  while (s+1)**2*n<=D*S*S: s+=1
  while s*s*n>D*S*S: s-=1
  return s
def vals(c):
  k,R,e,s=c; n=2**(k+R); D=2**k-1
  thrHi=cd(((s+1)*N+e*S)*n,S*N); thrLo=cd((s*N+e*S)*n,S*N)
  listHi=S*N//(2*e*s)
  mHi=max(cd((s+1)*N,2*e*S),3)
  muHi=cd((2*mHi+1)*S,2*s)-1
  hHi=cd((2*mHi+1)**2*n,12*D)-1
  excNum=((max(2*muHi-1,0))*hHi+max(n-D-1,0)*muHi)*(thrLo-D)+(n-D)*(hHi+muHi+4*D*muHi*hHi)
  excHi=excNum//(thrLo-D)
  ok=(k+R<=64 and k>=1 and R>=1 and e>0 and s>0 and s*s*n<=D*S*S and D*S*S<=(s+1)**2*n and (s+1)*N+e*S<=S*N
      and ((s+1)*N+e*S)*n<=thrHi*S*N and (thrLo-1)*S*N<(s*N+e*S)*n and thrLo>=1 and S*N<(listHi+1)*2*e*s
      and (s+1)*N<=mHi*2*e*S and mHi>=3 and (2*mHi+1)*S<=2*(muHi+1)*s and (2*mHi+1)**2*n<=12*D*(hHi+1)
      and D<thrLo and excNum<(excHi+1)*(thrLo-D))
  return dict(n=n,thrHi=thrHi,listHi=listHi,excHi=excHi,ok=ok)
def foldb(c,l): v=vals(c); return 192-log2(2*v['listHi']+2**(l['fold']-1)*v['excHi'])
def queryb(c,l,nxt):
  v=vals(c); n=v['n']; t=l['t']
  y=(t+1)*vals(nxt)['listHi'] if nxt else t
  # 2^-17 (x^t/n^t + y/2^192)
  val=F(v['thrHi']-1,n)**t+F(y,2**192)
  return 17-log2(val.numerator)+log2(val.denominator)
def oodb(c,nxt): L=vals(nxt)['listHi']; return 192-log2(L*L*c[0])
def shapebits(mu,R,certs):
  lv=ladder(mu,R); bs=[]
  for i,l in enumerate(lv):
    nxt=certs[i+1] if i+1<len(lv) else None
    assert vals(certs[i])['ok']
    bs.append(min(foldb(certs[i],l),queryb(certs[i],l,nxt),*( [oodb(certs[i],nxt)] if nxt else [190])))
  return bs
def lvmin(l,k,R,e,nxtL):
  c=(k,R,e,sqrtcert(k,R)); v=vals(c)
  if not v['ok']: return -1
  fb=foldb(c,l)
  val=F(v['thrHi']-1,v['n'])**l['t']+F((l['t']+1)*nxtL,2**192)
  qb=17-log2(val.numerator)+log2(val.denominator)
  return min(fb,qb)
def best(l,nxtL=2**18):
  k,R=l['kappa'],l['R']
  lo,hi=1,N//4
  while hi-lo>1:
    m=(lo+hi)//2; c=(k,R,m,sqrtcert(k,R))
    fb=foldb(c,l); v=vals(c)
    val=F(v['thrHi']-1,v['n'])**l['t']+F((l['t']+1)*nxtL,2**192)
    qb=17-log2(val.numerator)+log2(val.denominator)
    if fb<qb: lo=m
    else: hi=m
  # local search around
  cands=range(max(1,lo-3),hi+4)
  return max(cands,key=lambda e:lvmin(l,k,R,e,nxtL))
table={}
worst=999
for R in range(1,5):
  for mu in range(15,29):
    lv=ladder(mu,R)
    certs=[]
    for l in lv:
      e=best(l); certs.append((l['kappa'],l['R'],e,sqrtcert(l['kappa'],l['R'])))
    bs=shapebits(mu,R,certs); worst=min(worst,min(bs))
    table[(mu,R)]=certs
    print(mu,R,'%.3f'%min(bs),' '.join('%.2f'%b for b in bs), 'L0=%.2f'%log2(vals(certs[0])['listHi']),flush=True)
print('worst',worst)
import json
json.dump({'%d,%d'%k:v for k,v in table.items()},open('table.json','w'))
