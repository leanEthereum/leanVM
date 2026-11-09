from fractions import Fraction as F
from math import isqrt, log2, comb
QT=[
  [[222, 55], [223, 56, 30], [223, 56, 31], [223, 56, 32], [223, 56, 32], [223, 56, 32, 22],
   [223, 56, 32, 22], [224, 56, 32, 23], [224, 56, 32, 23], [224, 56, 32, 23, 17],
   [224, 56, 32, 23, 17], [224, 56, 32, 23, 18], [225, 56, 32, 23, 18], [225, 56, 32, 23, 18, 14]],
  [[111, 45], [112, 45, 27], [112, 45, 28], [112, 45, 28], [112, 45, 28], [112, 45, 28, 20],
   [112, 45, 28, 20], [112, 45, 28, 21], [112, 45, 28, 21], [112, 45, 28, 21, 16],
   [112, 45, 28, 21, 16], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16, 13]],
  [[75, 37], [75, 37, 24], [75, 37, 25], [75, 38, 25], [75, 38, 25], [75, 38, 25, 18],
   [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19, 15],
   [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15, 13]],
  [[56, 32], [56, 32, 22], [56, 32, 22], [56, 32, 23], [56, 32, 23], [56, 32, 23, 17],
   [56, 32, 23, 17], [56, 32, 23, 18], [56, 32, 23, 18], [56, 32, 23, 18, 14],
   [56, 32, 23, 18, 14], [56, 32, 23, 18, 14], [56, 32, 23, 18, 15], [56, 32, 23, 18, 15, 12]]]
def levelsFrom(fuel,rem,pf,pr,red):
  if fuel==0 or rem<=5: return []
  rate=pr+pf-red; fold=min(4,rem)
  return [(fold,rate)]+levelsFrom(fuel-1,rem-fold,fold,rate,1)
def ladder(mu,R):
  g=[(6,R)]+levelsFrom(mu,mu-6,6,R,3)
  q=QT[R-1][mu-15]; assert len(g)==len(q)
  out=[];pre=0
  for (f,r),t in zip(g,q):
    out.append(dict(fold=f,R=r,t=t,kappa=mu-pre-f)); pre+=f
  return out
def ceil(x): return -((-x.numerator)//x.denominator)
def floor(x): return x.numerator//x.denominator
SP=80
def quant(kappa,R,eta):
  n=2**(kappa+R); D=2**kappa-1; rho=F(D,n)
  S=2**SP; s0=isqrt(D*S*S//n)  # floor sqrt(D/n * S^2) approx
  while (s0+1)**2*n<=D*S*S: s0+=1
  while s0*s0*n>D*S*S: s0-=1
  lo=F(s0,S); hi=F(s0+1,S)
  Thi=ceil((hi+eta)*n); Tlo=floor((lo+eta)*n)+1  # Tlo-1 < (lo+eta)n
  Lhi=floor(1/(2*eta*lo))
  Mhi=max(ceil(hi/(2*eta)),3); t=Mhi+F(1,2)
  muhi=ceil(t/lo)-1; hhi=ceil(t*t/(3*rho))-1
  theta=F(n-D,Tlo-D)
  cnt=(2*muhi-1)*hhi+theta*(hhi+muhi+4*D*muhi*hhi)+(n-D-1)*muhi
  Ehi=floor(cnt)
  return dict(n=n,Thi=Thi,Lhi=Lhi,Ehi=Ehi)
def lg(x): return log2(x) if x>0 else -999
def bits(mu,R,etas):
  lv=ladder(mu,R); Q=[quant(l['kappa'],l['R'],e) for l,e in zip(lv,etas)]
  terms=[]
  for i,l in enumerate(lv):
    q=Q[i]
    terms.append(('fold',i,F(2*q['Lhi']+2**(l['fold']-1)*q['Ehi'],2**192)))
    p=F(q['Thi']-1,q['n'])**l['t']
    if i+1<len(lv):
      q1=Q[i+1]
      terms.append(('ood',i,F(comb(q1['Lhi'],2)*l['kappa'],2**192)))
      terms.append(('query',i,(p+F((l['t']+1)*q1['Lhi'],2**192))/2**17))
    else:
      terms.append(('query',i,(p+F(l['t'],2**192))/2**17)); terms.append(('tail',i,F(2,2**192)))
  return terms
