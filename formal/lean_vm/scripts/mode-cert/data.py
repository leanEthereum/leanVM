"""The guest's compiled functions, hints, powers of `g` and jump table, read from the generated data."""
import re, glob, os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_VM = os.path.normpath(os.path.join(HERE, '..', '..'))
ROOT = os.path.join(LEAN_VM, 'LeanVM', 'Guest')
STATEMENT = os.path.normpath(os.path.join(LEAN_VM, '..', 'Statement'))


def load():
    ins_re=re.compile(r'\(\.(\w+) ([^()]*)\)')
    fns={}
    for b in sorted(glob.glob(ROOT+'/Pack/*/Bundle.lean')):
        pack=b.split('/')[-2]
        t=open(b).read()
        for blk in t.split('\nnamespace LeanVM.Guest.Fn.')[1:]:
            name=blk.split('\n',1)[0].strip().strip('«»')
            chunks={}
            for m in re.finditer(r'def (c\d+) : List OffsetInstruction := \[(.*?)\]\n', blk, re.S):
                body=m.group(2)
                L=[]
                for im in ins_re.finditer(body):
                    op=im.group(1); args=im.group(2).split()
                    L.append((op,args))
                chunks[m.group(1)]=L
            cm=re.search(r'def code : CompiledFunction :=\s*⟨"([^"]*)", (\d+), (\d+), \[([^\]]*)\]⟩', blk)
            nm,entry,cnt,cl=cm.group(1),int(cm.group(2)),int(cm.group(3)),cm.group(4)
            code=[]
            for c in cl.split(','):
                c=c.strip()
                if c: code+=chunks[c]
            assert len(code)==cnt,(nm,len(code),cnt)
            fns[nm]=dict(name=nm,entry=entry,count=cnt,code=code,pack=pack,ns=name)
    for b in sorted(glob.glob(ROOT+'/Pack/*/Sig.lean')):
        s=open(b).read()
        for m in re.finditer(r'def sig : Check.Sig :=\s*⟨"([^"]*)", (\d+), (\d+), (\d+),',s):
            fns[m.group(1)]['nargs']=int(m.group(3)); fns[m.group(1)]['nret']=int(m.group(4))
    # advice
    t=open(ROOT+'/Data/Advice.lean').read()
    s=t[t.index('"leanvm-advice'):].split('"')[1].replace('\\n','\n')
    toks=s.split()
    pos = [0]
    def tok():
        pos[0] += 1; return toks[pos[0]-1]
    assert tok()=='leanvm-advice'; tok(); tok(); mainFrame=int(tok()); tok()
    nh=int(tok())
    hints={}
    def dest():
        k=tok(); return (k,int(tok()))
    for _ in range(nh):
        pc=int(tok()); n=int(tok()); L=[]
        for _ in range(n):
            tag=tok()
            if tag=='fa': h=(tag,int(tok()))
            elif tag=='af': h=(tag,int(tok()),int(tok()),int(tok()),tok(),int(tok()))
            elif tag in('al','ad','ca'): h=(tag,int(tok()),int(tok()))
            elif tag=='aa':
                p=int(tok()); sl=int(tok()); n2=int(tok()); h=(tag,p,sl,[int(tok()) for _ in range(n2)])
            elif tag=='av': h=(tag,int(tok()),tok())
            elif tag=='ws': h=(tag,tok(),int(tok()),int(tok()))
            elif tag=='wh': h=(tag,tok(),int(tok()),int(tok()),int(tok()))
            elif tag=='lc': h=(tag,dest(),int(tok()),int(tok()),int(tok()))
            elif tag in('bd','be'): h=(tag,int(tok()),dest(),int(tok()))
            elif tag=='dd':
                h=(tag,int(tok()),dest(),int(tok()),int(tok()),int(tok()),int(tok()),tok())
            elif tag=='we': h=(tag,int(tok()),dest(),int(tok()),int(tok()),int(tok()),int(tok()))
            elif tag=='fl': h=(tag,int(tok()),int(tok()),int(tok()))
            elif tag=='iv': h=(tag,int(tok()),int(tok()))
            else: raise Exception(tag)
            L.append(h)
        hints[pc]=L
    g = open(os.path.join(ROOT, 'Data', 'Pows.lean')).read()
    pows = {int(k): int(e) for k, e in re.findall(r'\.node (\d+) (\d+)', g)}
    t = open(os.path.join(STATEMENT, 'Data', 'Bytecode00.lean')).read()
    blk = t[t.index('def f0c0'):]
    t0 = open(os.path.join(STATEMENT, 'Data', 'Bytecode.lean')).read()
    n0 = int(re.search(r'def f0 : CompiledFunction :=\s*⟨"[^"]*", \d+, (\d+)', t0).group(1))
    f0 = [(int(a), int(b)) for a, b, _ in re.findall(r'\.set (\d+) (\d+) (\d+)', blk)][:n0]
    jt = {s: pows.get(k) for s, k in f0}
    return dict(fns=fns, hints=hints, mainFrame=mainFrame, pows=pows, jt=jt)
