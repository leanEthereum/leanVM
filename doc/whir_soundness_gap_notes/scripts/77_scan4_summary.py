import sys
from collections import Counter
def load(fn):
    out=[]
    for l in open(fn):
        pat,rest=l.split(" | "); t=rest.split()
        out.append(dict(pat=pat,orbit=int(t[1]),w=int(t[3]),rU=int(t[5]),rC=int(t[7]),F=t[9],G=int(t[11]),nsub=int(t[13]),maxsub=int(t[14]),nl=int(t[16]),bal=int(t[18])))
    return out
for fn in sys.argv[1:]:
    R=load(fn)
    print(fn,"deficient orbits",len(R),"patterns",sum(r['orbit'] for r in R), "deficiencies",dict(Counter(r['rU']-r['rC'] for r in R)))
    c=Counter(); cp=Counter(); mw={}; mb={}
    for r in R:
        fam = ("I lift, flag subspace" if r['F']=="111" else "I lift, other subspace" if r['F']=="011" else "II common upper factor" if r['F']=="001" else
               ("III lifted 3-sublist + member" if r['nsub']>0 and r['nl']==0 else "IV.a non-lift 3-sublist + member" if r['nl']>0 else "IV.b no deficient sublist"))
        key=(fam, "genuine" if r['G'] else "collapsed")
        c[key]+=1; cp[key]+=r['orbit']; mw[key]=max(mw.get(key,0),r['w']); mb[key]=max(mb.get(key,0),r['bal'])
    for key in sorted(c): print("   %-34s %-9s orbits %5d patterns %7d  max weight %2d  max balanced agreement %d" % (key[0],key[1],c[key],cp[key],mw[key],mb[key]))
