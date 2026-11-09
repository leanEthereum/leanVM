# usage: python3 -I genbtwin.py > ../../LeanVM/Guest/B1/Tables/VtC/BTwin.lean
# Replays the soundness's algebraic lemmas of the bus sides (stated on VtH) on VtP: the theorems of
# Vt/{PushFw,PushPad,PullTotal,PullSels,CountTotal}.lean, renamed vt_ -> vtP_, vtPullSels -> vtPPullSels.
import re, os
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../LeanVM/Guest/B1/Tables/Vt/')
files = ['PushFw', 'PushPad', 'PullTotal', 'PullSels', 'CountTotal']
out = []
for f in files:
    src = open(D + f + '.lean').read()
    body = src[src.index('@[expose] public section') + len('@[expose] public section'):src.rindex('end\nend LeanVM')]
    # split into top-level chunks starting at a line beginning a declaration-ish token
    lines = body.split('\n')
    chunks = []; cur = []
    for ln in lines:
        if re.match(r'(theorem|def|abbrev|set_option|/--|noncomputable def)\b', ln) and cur and not re.match(r'(set_option|/--)', cur[-1] if cur else ''):
            # start a new chunk unless the previous line was a set_option/doc prefix
            if not (cur and (cur[-1].startswith('set_option') or cur[-1].startswith('/--') or cur[-1].endswith('-/') and cur[-1].startswith('/--'))):
                chunks.append(cur); cur = []
        cur.append(ln)
    chunks.append(cur)
    for ch in chunks:
        txt = '\n'.join(ch).strip('\n')
        if not re.search(r'^theorem ', txt, re.M): continue
        if 'VtH' not in txt: continue
        txt = txt.replace('VtH rd σ', 'VtP rd σ')
        txt = re.sub(r'^theorem vt_', 'theorem vtP_', txt, flags=re.M)
        txt = re.sub(r'^theorem vtPullSels', 'theorem vtPPullSels', txt, flags=re.M)
        out.append(txt)
print('''/-
  LeanVM.Guest.B1.Tables.VtC.BTwin

  The soundness's algebra of the bus sides, replayed on `VtP` (generated:
  scripts/b1c-vt/genbtwin.py from Vt/{PushFw,PushPad,PullTotal,PullSels,CountTotal}.lean).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BBase
public import LeanVM.Guest.B1.Tables.Vt.AsmTotals

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section
''')
print('\n\n'.join(out))
print('''
end
end LeanVM.Guest.B1.Tables''')
