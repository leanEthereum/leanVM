"""Write B1/Opening/QueriesBody{0..3}.lean and `QueriesFns.lean`'s `oqFns_all` cases."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
D = os.path.join(sys.argv[1], 'LeanVM') + '/' + 'Guest/B1/Opening/'
sp = gen.oq_specs()

def shape(d):
    return '(⟨%d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, [%s]⟩ : OqShape)' % (
        d['odd'], d['base'], d['folds'], d['leaf'], d['depth'], d['cd'], d['mu'], d['vanish'], d['nhs'],
        d['hsb'], d['final'], ', '.join(map(str, d['vs'])))

HEAD = '''/-
  LeanVM.Guest.B1.Opening.%s

  %s
-/

module

%s

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section
'''
parts = [sp[k::4] for k in range(4)]
for k, part in enumerate(parts):
    out = [HEAD % ('QueriesBody%d' % k,
                   "The bodies of a quarter of `opening_queries`' specializations and of their loop helpers are\n  the templates (kernel evaluation).",
                   'public import LeanVM.Guest.B1.Opening.QueriesT')]
    for d in part:
        sh = shape(d)
        loopT = ('oqLoop1T %s.oq %d (oqWalkOf %s.oq) "%s"' % (sh, d['odd'], sh, d['loop'])) if d['base'] == 1 else \
                ('oqLoop0T %s.oq (oqWalkOf %s.oq) "%s"' % (sh, sh, d['loop']))
        out.append('''set_option maxRecDepth 100000 in
/-- `%s`. -/
theorem oqBody_%d : Data.core%d.body = oqMainT %s.oq %d (oqWalkOf %s.oq) "%s" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `%s`. -/
theorem oqLoopBody_%d : Data.core%d.body = %s :=
  stmtsEqb_sound (by decide +kernel)
''' % (d['name'], d['idx'], d['idx'], sh, d['odd'], sh, d['loop'], d['loop'], d['idx'], d['loopidx'], loopT))
    out.append('end\nend LeanVM.Guest.B1\n')
    open(D + 'QueriesBody%d.lean' % k, 'w').write('\n'.join(out))
# QueriesFns.lean: from `oqFns_` on, each entry of `openingQueriesLoops` (in `gen.oq_specs`' order)
# found with its walk, functions and bodies, one theorem each, and `oqFns_all`.
p = D + 'QueriesFns.lean'
s = open(p).read()
i = s.index('set_option maxRecDepth 100000 in\n/-- Entry ')
out = [s[:i].rstrip() + '\n']
for k, d in enumerate(sp):
    out.append('''set_option maxRecDepth 100000 in
/-- Entry %d, `%s`. -/
theorem oqFns_%d : OqFns (openingQueriesLoops.getD %d oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L%d_L%d, Data.core%d, Data.core%d,
    coreProgram_find?_at (j := %d) rfl, rfl, oqBody_%d,
    coreProgram_find?_at (j := %d) rfl, rfl, oqLoopBody_%d⟩
''' % (k, d['name'], d['idx'], k, d['depth'] - d['cd'], d['cd'], d['idx'], d['loopidx'], d['idx'], d['idx'],
       d['loopidx'], d['idx']))
out.append('''/-- **Every entry's functions are found with the templates' bodies.** -/
theorem oqFns_all : ∀ p ∈ openingQueriesLoops, OqFns p := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  rw [List.getElem_eq_getD oqNone]
  have hi' : i < %d := hi
  interval_cases i
  exacts [%s]

end
end LeanVM.Guest.B1
''' % (len(sp), ',\n    '.join(', '.join('oqFns_%d' % d['idx'] for d in sp[r:r + 7])
                                  for r in range(0, len(sp), 7))))
open(p, 'w').write('\n'.join(out))
