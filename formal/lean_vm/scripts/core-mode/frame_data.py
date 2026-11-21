"""The frame walk's inputs, read from the generated data (`compiled.py`): each function's code, hints, executor facts
(`Check.Cert.facts` in its `Bundle`), callee frame signatures (the frame layout's) and table targets."""
import os, re, sys, glob, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)
import compiled as C  # noqa: E402

ROOT = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))


def sym(s):
    m = re.fullmatch(r'\(\.(gp|fpg) (\d+)\)', s.strip())
    if m: return (m.group(1), int(m.group(2)))
    assert s.strip() == '.zero', s
    return ('z',)


def facts():
    """`Check.Cert.facts` of each function: env, fpOne, arms, scaled."""
    out = {}; byns = {}
    for nsn, (_, blk) in C.bridge_data().bundle_blocks().items():
        name = C.bridge_data().code_of(blk)[0]
        byns[nsn] = name
        fm = re.search(r'facts := \{ env := \[(.*?)\], fpOne := (\w+), arms := \[(.*?)\],(?: armsT := \w+,)? '
                       r'scaled := \[(.*?)\] \}', blk)
        env = {int(o): sym(v) for o, v in re.findall(r'\((\d+), (\([^()]*\)|\.zero)\)', fm.group(1))}
        arms = {int(o): [int(x) for x in ts.split(',') if x.strip()]
                for o, ts in re.findall(r'\((\d+), \[([^\]]*)\]\)', fm.group(3))}
        out[name] = dict(env=env, fpOne=fm.group(2) == 'true', arms=arms,
                         scaled=[int(x) for x in fm.group(4).split(',') if x.strip()], armsT='armsT :=' in fm.group(0))
    # `main_loop2`'s arms in a trie (`Cells0.lean`)
    for c in glob.glob(ROOT + '/Pack/*/Cells0.lean'):
        t = open(c).read()
        m = re.search(r'def cert_armsT : Exec\.Trie \(List ℕ\) :=(.*?)(?:\n\n|\Z)', t, re.S)
        if not m: continue
        nm = re.search(r'namespace LeanVM\.Guest\.Fn\.«?([^»\n]*)»?', t).group(1)
        out[byns[nm]]['armsT_src'] = m.group(1)
    return out


def load():
    """The walks' inputs. Every function is on the core route, whose pairing gives its oracle (`O`) and whose own walk
    its residual divisors (`R`): both empty here."""
    return dict(C.code(), facts=facts(), O={}, R={})
