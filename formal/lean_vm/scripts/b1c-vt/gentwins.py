# usage: python3 -I gentwins.py  (from this directory; writes ../../LeanVM/Guest/B1/Tables/VtC/F{Forms0..5,Forms5a,Forms5b,Air}.lean)
# Twins of the soundness forms and air lemmas (Vt/FormsT*.lean, Vt/Air.lean) over the window `VtF`
# (VtC/FBase.lean) instead of `VtH`: the same proofs, theorem names suffixed `F`; the air total
# stops before the final check (it gives the guest's `air_acc`, the final check's left side); the
# pull sides take the pull blocks' selectors' copies (`Vt/PullSels.lean`, outside the window) as a
# hypothesis `hq`.
import re, os
here = os.path.dirname(os.path.abspath(__file__))
vt = os.path.join(here, '../../LeanVM/Guest/B1/Tables/Vt')
out = os.path.join(here, '../../LeanVM/Guest/B1/Tables/VtC')
files = [('FormsT0', 'FForms0'), ('FormsT1', 'FForms1'), ('FormsT2', 'FForms2'),
         ('FormsT3', 'FForms3'), ('FormsT4', 'FForms4'), ('FormsT5a', 'FForms5a'),
         ('FormsT5b', 'FForms5b'), ('FormsT5', 'FForms5'), ('Air', 'FAir')]
src = {a: open(os.path.join(vt, a + '.lean')).read() for a, _ in files}
pulls = open(os.path.join(vt, 'PullSels.lean')).read()
names = set(['vt_eval'])
for s in src.values(): names |= set(re.findall(r'^theorem (\w+)', s, re.M))
pat = re.compile(r'\b(' + '|'.join(sorted(names, key=len, reverse=True)) + r')\b')
deps = {'FForms5': ['FForms5a', 'FForms5b']}
for a, b in files:
    s = src[a]
    body = s[s.index('@[expose] public section'):]
    body = pat.sub(lambda m: m.group(1) + 'F', body)
    body = re.sub(r'\bVtH\b', 'VtF', body)
    if a == 'Air':
        old = body[body.index('/-- **The air check**'):body.index('\nend\nend')]
        m = re.search(r'  have a(\d+) := h\.atomAt \1 \(\.assertEq \(\.n (\d+)\) \(\.n (\d+)\)\)[^\n]*\n', old)
        an, acc, claim = m.group(1), m.group(2), m.group(3)
        new = old.replace(m.group(0), '')
        new = new.replace('the sumcheck\'s final claim is', 'the guest\'s `air_acc` is')
        new = new.replace(f'σ (.n {claim}) = σ', f'σ (.n {acc}) = σ', 1)
        new = new.replace(f' a{an}\n', '\n')
        new = new.replace(f'eq_neg_of_add_eq_zero_right a{an}, CharTwo.neg_eq, ', '')
        assert new != old and f'a{an}' not in new
        body = body.replace(old, new)
    # the pull side: the pull blocks' selectors are copies made outside the window
    for t in range(6):
        m = re.search(r'theorem vtPullSels%d \{rd : Reader\} \{σ : Val\} \(h : VtH rd σ\) :\n(.*?) := by' % t,
                      pulls, re.S)
        if f'rw [vtPullSels{t} h]' not in body: continue
        stmt = ' '.join(m.group(1).split())
        head = f'theorem vtSide1{t}F {{rd : Reader}} {{σ : Val}} (h : VtF rd σ)'
        assert head in body
        body = body.replace(head, head + f'\n    (hq : {stmt})')
        body = body.replace(f'rw [vtPullSels{t} h]', 'rw [hq]')
    imps = ['LeanVM.Guest.B1.Tables.VtC.FEvals', 'LeanVM.Guest.B1.Tables.Vt.' + a]
    imps += ['LeanVM.Guest.B1.Tables.VtC.' + d for d in deps.get(b, [])]
    head = f'''/-
  LeanVM.Guest.B1.Tables.VtC.{b}

  `Vt/{a}.lean` on the window `VtF` (generated: scripts/b1c-vt/gentwins.py).
-/

module

''' + ''.join(f'public import {i}\n' for i in imps) + '''
namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

'''
    open(os.path.join(out, b + '.lean'), 'w').write(head + body)
print(len(names))
