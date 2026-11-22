#!/usr/bin/env python3
"""Check for 01-literature-attacks.md, Section 3.3, at dimension d = 6 (about 20 seconds).

Counts the height-two tree supports (two disjoint codimension-2 flats in different directions) that avoid a
padding set W of size n/8: W a codimension-3 subspace (DKTZ26 M_2), W spanning a codimension-2 subspace, and a
hill climb over all 8-subsets W. Also counts the affine codimension-2 flats avoiding a codimension-3 subspace.
"""
import random, itertools
d=6; N=1<<d
par=lambda v: bin(v).count("1")&1
# all height-2 tree supports as bitmasks
seen=set(); masks=set()
for a in range(1,N):
    for b in range(a+1,N):
        key=frozenset((a,b,a^b))
        if key in seen: continue
        seen.add(key)
        for e in range(1,N):
            if e in key: continue
            for c in (0,1):
                m=0
                for x in range(N):
                    if (par(a&x)&par(b&x))^par(e&x)^c: m|=1<<x
                masks.add(m)
masks=list(masks)
print("tree supports:",len(masks), "expected 56*[6;3]_2 =",56*1395)
def count(W):
    wm=0
    for x in W: wm|=1<<x
    return sum(1 for m in masks if m&wm==0)
Wsub=list(range(8))
print("W = codim-3 subspace:",count(Wsub),"M_2(6)=",28*(6*8-5))
G=list(range(16))
print("vanishing on codim-2 subspace G:",count(G),"formula 3*2^d-12 =",3*N-12)
# affine codim-2 flats avoiding the codim-3 subspace
flats=set()
for a in range(1,N):
    for b in range(a+1,N):
        for al in (0,1):
            for be in (0,1):
                flats.add(frozenset(x for x in range(N) if par(a&x)==al and par(b&x)==be))
print("affine codim-2 flats:",len(flats),"avoiding W:",sum(1 for F in flats if not (F&set(Wsub))),"formula 7*2^d-35 =",7*N-35)
# hill climb over 8-subsets W
rng=random.Random(5)
best_overall=0
for start in range(6):
    W=rng.sample(range(N),8) if start else [0,1,2,3,4,5,6,8]
    cur=count(W)
    for it in range(1500):
        i=rng.randrange(8); y=rng.randrange(N)
        if y in W: continue
        W2=W[:]; W2[i]=y
        c2=count(W2)
        if c2>=cur: W,cur=W2,c2
    best_overall=max(best_overall,cur)
    print("start",start,"final count",cur,sorted(W))
print("best over hill climbs:",best_overall)
