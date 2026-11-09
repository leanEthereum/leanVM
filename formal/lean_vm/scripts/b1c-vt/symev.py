import os, sys
# Library: verify_tables' body (vt_ir.txt from dump.py, or $VT_IR) parsed into atoms and definitions.
# First run: python3 -I dump.py ../../LeanVM/Guest/Data/Core00.lean vt_ir.txt (from this directory).
import re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
# The B1-c verify_tables modules, and verify_tables' body as `dump.py` writes it.
VT_LEAN = os.path.join(HERE, '..', '..', 'LeanVM', 'Guest', 'B1', 'Tables', 'Vt')
IRF = os.environ.get('VT_IR', os.path.join(HERE, 'vt_ir.txt'))
NAMES=[('block_selector_tab','vtBstNames'),('block_selector','vtBsNames'),('index_mle','vtImNames'),('padding_weight','vtPadNames'),('plus_one_run','plusOneRunNames')]
def load_ir():
    ir={}
    for line in open(IRF).read().splitlines():
        k,_,s=line.partition(': ')
        s=s.strip()
        if s.endswith(' ::'): s=s[:-3]
        for base,name in NAMES:
            s=re.sub(r'\("'+base+r'__L0"( :: "'+base+r'__L\d+")* :: \[\]\)', name, s)
            s=re.sub(r'\["'+base+r'__L0"(, "'+base+r'__L\d+")*\]', name, s)
        ir[int(k)]=s
    return ir
IR=load_ir()
def parse_atom(s):
    m=re.match(r'\.atom \(\.(\w+) (.*)\)$',s)
    if not m: return None
    op=m.group(1); rest=m.group(2)
    if op in ('add','mul'):
        a=re.findall(r'\(\.n (\d+)\)',rest); return (op,[int(x) for x in a])
    if op=='copy':
        a=re.findall(r'\(\.n (\d+)\)',rest); return (op,[int(x) for x in a])
    if op=='const':
        m2=re.match(r'\(\.n (\d+)\) \(word (\d+) (\d+) (\d+)\)',rest); return ('const',[int(m2.group(1)),(int(m2.group(2)),int(m2.group(3)),int(m2.group(4)))])
    if op=='load':
        m2=re.match(r'\(\.n (\d+)\) \(\.n (\d+)\) (\d+)',rest); return ('load',[int(m2.group(1)),int(m2.group(2)),int(m2.group(3))])
    return (op,rest)
def slice_text(lo,hi):
    return ',\n      '.join(IR[p] for p in range(lo,hi+1))
def pattern(lo,hi):
    return ', '.join(f'a{p}' for p in range(lo,hi+1))
def defs_in(ranges):
    d={}
    for lo,hi in ranges:
        for p in range(lo,hi+1):
            a=parse_atom(IR[p])
            if a is None: continue
            op,args=a
            if op in ('add','mul','copy'): d.setdefault(args[0],(p,op,args[1:]))
            elif op=='const': d.setdefault(args[0],(p,'const',args[1]))
            elif op=='load': d.setdefault(args[0],(p,'load',args[1:]))
    return d
def expr(v,d,leafmap,used,top=True):
    if v in leafmap: return leafmap[v]
    if v not in d: return f'σ (.n {v})'
    p,op,args=d[v]
    used.add(p)
    if op=='const':
        a,b,c=args
        return f'word {a} {b} {c}'
    if op=='load':
        base,off=args
        return f'L[{base},{off}]'
    if op=='copy': return expr(args[0],d,leafmap,used,False)
    l=expr(args[0],d,leafmap,used,False); r=expr(args[1],d,leafmap,used,False)
    return f'({l} {"+" if op=="add" else "*"} {r})'
def deps(v,d,acc):
    """positions of the defining atoms of v within d (loads included), recursively."""
    if v not in d: return acc
    p,op,args=d[v]
    if p in acc: return acc
    acc.add(p)
    if op in ('add','mul','copy'):
        for a in args: deps(a,d,acc)
    return acc
