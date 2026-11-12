"""Write B1/Opening/QueriesBody{0..3}.lean, QueriesW{0..3}.lean, QueriesAllW.lean."""
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
    out = [HEAD % ('QueriesW%d' % k,
                   "A quarter of `opening_queries`' specializations, sound with their queries named.",
                   'public import LeanVM.Guest.B1.Opening.QueriesBody%d\npublic import LeanVM.Guest.B1.Opening.QueriesMainW\npublic import LeanVM.Guest.B1.Opening.WalkFns' % k)]
    for d in part:
        sh = shape(d)
        pd = d['depth'] - d['cd']
        hdr = '''set_option maxRecDepth 100000 in
/-- `%s` is sound with its queries named. -/
theorem oqSpecW_%d : opening_queries_sound_w_Spec "%s" "%s" %s :=
''' % (d['name'], d['idx'], d['name'], d['loop'], sh)
        common_tail = '''(by decide) (by decide) (by decide) (by decide) (wpFn_L%d_L%d)
    (Program.find?_of_indexOf? (j := %d) (by decide +kernel) rfl) rfl oqBody_%d
    (Program.find?_of_indexOf? (j := %d) (by decide +kernel) rfl) rfl oqLoopBody_%d
''' % (pd, d['cd'], d['idx'], d['idx'], d['loopidx'], d['idx'])
        if d['base'] == 1:
            body = '  oqMain1_sound_w (sh := %s) (by decide) (by decide) rfl rfl (by decide)\n    %s' % (sh, common_tail)
        else:
            body = '  oqMain0_sound_w (sh := %s) (by decide) (by decide) rfl rfl\n    %s' % (sh, common_tail)
        out.append(hdr + body)
    out.append('end\nend LeanVM.Guest.B1\n')
    open(D + 'QueriesW%d.lean' % k, 'w').write('\n'.join(out))

n = len(sp)
out = ['''/-
  LeanVM.Guest.B1.Opening.QueriesAllW

  Every deployed specialization of `opening_queries` is sound with its queries named.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesW0
public import LeanVM.Guest.B1.Opening.QueriesW1
public import LeanVM.Guest.B1.Opening.QueriesW2
public import LeanVM.Guest.B1.Opening.QueriesW3

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **Every deployed `opening_queries` is sound with its queries named.** -/
theorem opening_queries_all_sound_w : opening_queries_all_sound_w_Spec := by
  intro p hp
  simp only [openingQueriesLoops, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with %s
''' % ' | '.join(['rfl'] * n)]
for d in sp:
    out.append('  · exact oqSpecW_%d' % d['idx'])
out.append('\nend\nend LeanVM.Guest.B1\n')
open(D + 'QueriesAllW.lean', 'w').write('\n'.join(out))
