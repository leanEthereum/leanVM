import re,subprocess,difflib,sys,os
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
pat=re.compile(r'<<<<<<< HEAD\n(.*?)=======\n(.*?)>>>>>>> [^\n]*\n', re.S)
def show(stage,p): return subprocess.run(['git','show',f':{stage}:formal/rv64mc/{p}'],capture_output=True,text=True,cwd='../..').stdout
def merge3(b,o,t):
    sm=difflib.SequenceMatcher(None,b,o,autojunk=False); res=t
    for tag,i1,i2,j1,j2 in reversed(sm.get_opcodes()):
        if tag=='equal': continue
        for w in (60,120,200,30):
            ctx=b[max(0,i1-w):i1]
            if res.count(ctx)==1: break
        k=res.find(ctx); assert k>=0 and res.count(ctx)==1,('ctx',ctx)
        pos=k+len(ctx); old=b[i1:i2]
        assert res[pos:pos+len(old)]==old,('old',old,res[pos:pos+80])
        res=res[:pos]+o[j1:j2]+res[pos+len(old):]
    return res
def key(line): return re.sub(r'^\* ~~','* ',line)[:70]
for p in ['README.md','notes/total-status.md']:
    s=open(p).read()
    if '<<<<<<<' not in s: continue
    base=show(1,p); bl=base.splitlines(True)
    bitems={key(l):l for l in bl if l.startswith('* ')}
    def r(m):
        o,t=m.group(1),m.group(2)
        ol,tl=o.splitlines(True),t.splitlines(True)
        if o.startswith('| '):
            out=[]
            for a,b in zip(ol,tl):
                assert a.split('|')[2]==b.split('|')[2]
                out.append(b if ('yes' in b.split('|')[6] and 'yes' not in a.split('|')[6]) else a)
            return ''.join(out)
        def split(L):
            i=0
            while i<len(L) and L[i].startswith('* '): i+=1
            return L[:i],L[i:]
        if p.endswith('status.md') and (ol[0].startswith('* ') or tl[0].startswith('* ')):
            oi,orest=split(ol); ti,trest=split(tl)
            tk={key(l):l for l in ti}; out=[]
            for l in oi:
                k=key(l)
                if k in tk and k in bitems and tk[k]!=bitems[k] and l==bitems[k]: out.append(tk[k])
                else: out.append(l)
            ok={key(l) for l in oi}
            for l in ti:
                if key(l) not in ok and key(l) not in bitems: out.append(l)
            rest=orest if ''.join(orest)==''.join(trest) or not trest else (trest if not orest else orest+['\n']+trest)
            return ''.join(out)+''.join(rest)
        assert len(ol)==len(tl),(p,len(ol),len(tl),o[:200])
        out=[]
        for a,b in zip(ol,tl):
            cand=[x for x in bl if x[:40]==a[:40]]
            out.append(merge3(cand[0],a,b) if cand else (a if a==b else a+b))
        return ''.join(out)
    s=pat.sub(r,s); open(p,'w').write(s)
print('ok')
