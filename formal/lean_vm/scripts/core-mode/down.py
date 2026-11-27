"""Writes `Guest/CoreMode/Gen/DownTab.lean` and `Down{k}.lean`: every family of facts carried to callees checked over
the whole program by ranges (`resgen.DOWN_RANGES`), one walk of each function's body (`Res.downW`,
`CoreMode/Fam/DownW.lean`): the carried and nonzero facts (`Res.carryG`, `Res.carryNzG`, their lists and witnesses
from `carry.py`), the exponent bounds (`CoreMode.carryExpB`, from `termcall.py`), and the callers' checks of
`termCallers`, `glCallers`, `monoCallers` and `anyLink`. Each range's module states each family's range theorem, which
the families' aggregates (`CarryOk`, `ExpCarry`, `TermCallers`, `GlCallers`, `MonoWalkOk`, `AnyLinkOk`) chain.
`--check` writes nothing and fails when a file differs.
Usage: python3 -I scripts/core-mode/down.py [--check]"""
import sys, os, glob

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import resgen
import carry
import carrywit
import termcall
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
import coredata  # noqa: E402

OUT = resgen.OUT

header = genfiles.header('core-mode/down.py')

# each family's range theorem: its name, the check of one function, the theorem of `DownW.lean` giving it
FAMS = [('carry', 'carryG', 'downW_carryG (D := downT) carriedT_ok'),
        ('carryNz', 'carryNzG', 'downW_carryNz (D := downT) carriedNzT_ok nzUpT_ok ownNzT_ok'),
        ('expCarry', 'CoreMode.carryExpB CoreMode.FnReg.expCarry', 'downW_carryExp (D := downT) expCarryT_ok'),
        ('termCallers', 'callersG termCallers', 'downW_term (D := downT) rfl'),
        ('glCallers', 'callersM glCallers', 'downW_gl (D := downT) rfl'),
        ('monoCallers', 'callersG monoCallers', 'downW_mono (D := downT) rfl'),
        ('anyCallers', 'callersB anyLink', 'downW_any (D := downT) rfl')]


def render():
    files = {}
    F, carried, up, own, kc = carry.lists()
    gbits, nzbits = carry.witnesses(F, carried, up, own, kc)
    expw, _ = termcall.exp_witness(termcall.carry_list())
    keys = coredata.keys(os.path.join(resgen.ROOT, 'Data'))
    names = carrywit.name_strings(os.path.join(resgen.ROOT, 'Data', 'NameStrings.lean'))
    mod = 'LeanVM.Guest.CoreMode.Gen.DownTab'
    t = [header(mod, 'The lists and tables of the facts carried to callees (`Res.DownT`).')]
    t.append('public import LeanVM.Guest.CoreMode.Fam.DownW\npublic import LeanVM.Guest.CoreMode.Gen.CarryTab\n'
             'public import LeanVM.Guest.CoreMode.Gen.ExpCarryTab\npublic import LeanVM.Guest.CoreMode.Fam.TermDefs\n'
             'public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.MonoDefs\n'
             'public import LeanVM.Guest.CoreMode.Gen.AnyLink\n\nnamespace LeanVM.Guest.Res\n\n@[expose] public section\n\n'
             '/-- **The lists and tables of the facts carried to callees.** -/\n'
             'noncomputable def downT : DownT :=\n'
             '  ⟨carriedT, carriedNzT, nzUpT, ownNzT, expCarryT, termCallers, glCallers, monoCallers, anyLink⟩\n\n'
             'end\n\nend LeanVM.Guest.Res\n')
    files[mod] = ''.join(t)
    for k, (a, m) in enumerate(resgen.down_ranges()):
        mod = 'LeanVM.Guest.CoreMode.Gen.Down%d' % k
        t = [header(mod, 'The facts carried to callees, every family, functions %d to %d.' % (a, a + m - 1))]
        t.append('public import LeanVM.Guest.CoreMode.Gen.DownTab\nmeta import LeanVM.Guest.Packed.NatLit\n\n'
                 'namespace LeanVM.Guest.Res\n\nopen LeanVM.Guest.Memory\n\n')
        for w, bits, what in (('gW', lambda j: gbits[names[keys[j]]], '`Bridge.spine` the carried facts\''),
                              ('nzW', lambda j: nzbits[names[keys[j]]], '`Memory.spineE` the nonzero facts\''),
                              ('expW', lambda j: expw[j], '`Memory.spineE` the exponent bounds\'')):
            items = [(j, bits(j)) for j in range(a, a + m) if bits(j)]
            t.append('/-- The sub-spines of %s searches use, by function index. -/\nnoncomputable def %s%d : NTree ℕ :=\n'
                     '  %s\n\n' % (what, w, a, carrywit.ntree(items, carrywit.hexbits)))
        t.append('/-- Every family\'s check, one walk of each function\'s body. -/\n'
                 'private theorem down_%d : RangeOk (fun j fn ↦ downW downT fn ⟨witAt gW%d j, witAt nzW%d j, '
                 'witAt expW%d j⟩) %d %d := by\n  unfold RangeOk; decide +kernel\n\npublic section\n\n' % (a, a, a, a, a, m))
        for name, chk, of in FAMS:
            t.append('theorem %s_%d : RangeOk (fun _ fn => %s fn) %d %d :=\n  RangeOk.imp (fun _ _ h ↦ %s h) down_%d\n\n'
                     % (name, a, chk, a, m, of, a))
        t.append('end\n\nend LeanVM.Guest.Res\n')
        files[mod] = ''.join(t)
    return {os.path.join(OUT, m.split('.')[-1] + '.lean'): v for m, v in files.items()}


def main(argv):
    files = render()
    bad = genfiles.sync(files, glob.glob(os.path.join(OUT, 'Down*.lean')), '--check' in argv)
    genfiles.fail_if_stale(bad, '--check' in argv)
    print('Down: %d files, %s' % (len(files), 'unchanged' if not bad else ('stale' if '--check' in argv else 'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
