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
# Level 0 is the level the extractor list-decodes (`LeanVM.Extraction.johnsonThreshold`): its
# decoding cost falls with the slack (the Guruswami–Sudan multiplicity is about
# sqrt(rho)/(2 eta), the list at most 1/(2 eta sqrt(rho))), while a larger slack only hurts the
# query group, ((thrHi - 1)/n)^t 2^-17, and helps the fold group, eBatch and listMax. So level 0
# does not balance: it takes the largest slack whose checks all pass at 2^-128 (`chkLevels` at
# level 0 in `LeanVM.Protocol.Whir.Params.Check`, exact in integers below), the next level's
# certificate fixed. The soundness is unchanged: every group stays at most 2^-128, the query
# group at its limit. The query check and the agreement bound `agr` are monotone in the slack
# (`thrHi` does not decrease), so a bisection finds their largest slack; the remaining checks
# are then confirmed downwards. The checks are exact: in floating point the query group at (15, 2)
# rounds to 2^-128.0 one step of `thrHi` too far (e = 4097, where the exact check fails; 2049).
# Level 0's list bound is then at most 2049, at (15, 2) (at most 642 elsewhere): `shapeOK`'s 2^12.
def lvl0ok(l,c,nxt,B=128):
  k,R,e,s=c; v=vals(c); n=v['n']; t=l['t']; f=l['fold']
  fold=(2*v['listHi']+2**(f-1)*v['excHi'])*2**B<=2**192
  query=((v['thrHi']-1)**t*2**192+(t+1)*vals(nxt)['listHi']*n**t)*2**(B-17)<=n**t*2**192
  ood=vals(nxt)['listHi']**2*k*2**B<=2**192
  return v['ok'] and fold and query and ood
def best0(l,nxt,B=128):
  k,R=l['kappa'],l['R']; s=sqrtcert(k,R)
  def mono(e):
    v=vals((k,R,e,s)); n=v['n']; t=l['t']
    return ((s+1)*N+e*S<=S*N and
      ((v['thrHi']-1)**t*2**192+(t+1)*vals(nxt)['listHi']*n**t)*2**(B-17)<=n**t*2**192)
  lo,hi=1,N
  assert mono(lo) and not mono(hi)
  while hi-lo>1:
    m=(lo+hi)//2
    if mono(m): lo=m
    else: hi=m
  e=lo
  while not lvl0ok(l,(k,R,e,s),nxt,B): e-=1
  assert e>=1
  return e
table={}
worst=999
for R in range(1,5):
  for mu in range(15,29):
    lv=ladder(mu,R)
    certs=[]
    for l in lv:
      e=best(l); certs.append((l['kappa'],l['R'],e,sqrtcert(l['kappa'],l['R'])))
    l0=lv[0]; certs[0]=(l0['kappa'],l0['R'],best0(l0,certs[1]),certs[0][3])
    bs=shapebits(mu,R,certs); worst=min(worst,min(bs))
    table[(mu,R)]=certs
    print(mu,R,'%.3f'%min(bs),' '.join('%.2f'%b for b in bs), 'L0=%.2f'%log2(vals(certs[0])['listHi']),flush=True)
print('worst',worst)
import json
json.dump({'%d,%d'%k:v for k,v in table.items()},open('table.json','w'))
