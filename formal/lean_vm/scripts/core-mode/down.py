"""Writes the facts carried to callees, every family checked over the whole program in one walk of each function's
body (`Res.downH`, `CoreMode/Fam/DownDefs.lean`) at its hints (`carrywit.py`): the nonzero facts' lists
(`Gen/CarryNzList.lean`, derived by `carry.py`), the tables of the families' lists (`CarryTab.lean`, `ExpCarryTab.lean`,
`DownTab.lean`), each range's walk (`Down{k}.lean`, `resgen.DOWN_RANGES`), which imports only definitions, and each
family's range theorems (`DownOk.lean`): the carried and nonzero facts (`Res.carryG`, `Res.carryNzG`), the exponent
bounds (`CoreMode.carryExpB`, its list from `termcall.py`), and the callers' checks of `termCallers`, `glCallers`,
`monoCallers` and `anyLink`, which the families' aggregates (`CarryOk`, `ExpCarry`, `TermCallers`, `GlCallers`,
`MonoWalkOk`, `AnyLinkOk`) chain.
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
import packed  # noqa: E402

OUT = resgen.OUT

header = genfiles.header('core-mode/down.py')

# each family's range theorem: its name, the check of one function, the theorem of `ResDown.lean` giving it
FAMS = [('carry', 'carryG', 'downH_carryG (D := downT) (tabOk.all carriedT_ok)'),
        ('carryNz', 'carryNzG', 'downH_carryNz (D := downT) carriedNzT_ok (tabOk.all nzUpT_ok) ownNzT_ok'),
        ('expCarry', 'CoreMode.carryExpB CoreMode.FnReg.expCarry', 'downH_carryExp (D := downT) (tabOk.all expCarryT_ok)'),
        ('termCallers', 'callersG termCallers', 'downH_term (D := downT) termT_ok'),
        ('glCallers', 'callersM glCallers', 'downH_gl (D := downT) glT_ok'),
        ('monoCallers', 'callersG monoCallers', 'downH_mono (D := downT) monoT_ok'),
        ('anyCallers', 'callersB anyLink', 'downH_any (D := downT) anyT_ok rfl')]


def tables(carried, up, own, kc, exp_by):
    """`CarryNzList.lean`, `CarryTab.lean`, `ExpCarryTab.lean`."""
    files = {}
    mod = 'LeanVM.Guest.CoreMode.Gen.CarryNzList'
    t = [header(mod, 'The nonzero facts\' carried parameters, callee words and own values (`Res.carryNzG`).')]
    t.append('namespace LeanVM.Guest.Res\n\n@[expose] public section\n\n')
    t.append('/-- **The parameters carried nonzero in `K`**: callee, parameter position. -/\n'
             'def carriedNz : List (String × Nat) := [\n%s]\n\n' % ',\n'.join(
                 '  ("%s", %d)' % (f, p) for f in sorted(carried) for p in sorted(carried[f])))
    t.append('/-- **The callee words nonzero in `K`**: callee, position among its parameters then its returns. -/\n'
             'def nzUp : List (String × Nat) := [\n%s]\n\n' % ',\n'.join('  ("%s", %d)' % c for c in up))
    t.append('/-- **The own values pinned nonzero in `K`** by their function\'s body (`Res.ownChk`): function, value number. -/\n'
             'def ownNz : List (String × Nat) := [\n%s]\n\nend\n\nend LeanVM.Guest.Res\n' % ',\n'.join(
                 '  ("%s", %d)' % c for c in own))
    files[mod] = ''.join(t)
    mod = 'LeanVM.Guest.CoreMode.Gen.CarryTab'
    t = [header(mod, 'The tables of the carried and nonzero facts\' lists of names (`Res.tabOk`).')]
    t.append('public import LeanVM.Guest.CoreMode.Fam.DownDefs\n\nnamespace LeanVM.Guest.Res\n\n@[expose] public section\n\n')
    tabs = (('carriedT', 'carried', 'NTab (ℕ × Kd)', [(f, (p, k)) for f, p, k in kc], lambda c: '(%d, .%s)' % c),
            ('carriedNzT', 'carriedNz', 'NTab ℕ', [(f, p) for f in carried for p in carried[f]], str),
            ('nzUpT', 'nzUp', 'NTab ℕ', up, str), ('ownNzT', 'ownNz', 'NTab ℕ', own, str))
    for d, l, ty, es, val in tabs:
        t.append('/-- `%s` by its names\' codes. -/\nnoncomputable def %s : %s :=\n  %s\n\n' % (l, d, ty, packed.ntab(es, val)))
    t.append('end\n\npublic section\n\n')
    for d, l, _, _, _ in tabs:
        t.append('theorem %s_ok : tabOk %s %s id = true := by decide +kernel\n\n' % (d, l, d))
    t.append('end\n\nend LeanVM.Guest.Res\n')
    files[mod] = ''.join(t)
    mod = 'LeanVM.Guest.CoreMode.Gen.ExpCarryTab'
    t = [header(mod, 'The table of `CoreMode.FnReg.expCarry` (`Res.tabOk`).')]
    t.append('public import LeanVM.Guest.CoreMode.Fam.DownDefs\npublic import LeanVM.Guest.CoreMode.Gen.FnData\n\n'
             'namespace LeanVM.Guest.Res\n\n@[expose] public section\n\n'
             '/-- `CoreMode.FnReg.expCarry` by its names\' codes. -/\nnoncomputable def expCarryT : NTab (ℕ × ℕ × ℕ) :=\n  %s\n\n'
             'end\n\npublic section\n\ntheorem expCarryT_ok : tabOk CoreMode.FnReg.expCarry expCarryT id = true := by\n'
             '  decide +kernel\n\nend\n\nend LeanVM.Guest.Res\n'
             % packed.ntab([(f, c) for f, cs in exp_by.items() for c in cs], lambda c: '(%d, %d, %d)' % c))
    files[mod] = ''.join(t)
    return files


def render():
    F, carried, up, own, kc = carry.lists()
    gbits, nzbits = carrywit.carry_hints(F, carried, up, own, kc)
    expw, exp_by = carrywit.exp_hints(termcall.carry_list())
    keys = coredata.keys(os.path.join(resgen.ROOT, 'Data'))
    names = dict(coredata.name_strings(os.path.join(resgen.ROOT, 'Data'))[0])
    files = tables(carried, up, own, kc, exp_by)
    mod = 'LeanVM.Guest.CoreMode.Gen.DownTab'
    t = [header(mod, 'The tables of the facts carried to callees (`Res.DownT`).')]
    t.append('public import LeanVM.Guest.CoreMode.Gen.CarryTab\npublic import LeanVM.Guest.CoreMode.Gen.ExpCarryTab\n'
             'public import LeanVM.Guest.CoreMode.Fam.TermDefs\n'
             'public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.MonoDefs\n'
             'public import LeanVM.Guest.CoreMode.Gen.AnyLink\n\nnamespace LeanVM.Guest.Res\n\n@[expose] public section\n\n'
             '/-- `termCallers` by its names\' codes. -/\nnoncomputable def termT : NTab ℕ := .ofNamed encS termCallers\n\n'
             '/-- `glCallers` by its names\' codes. -/\n'
             'noncomputable def glT : NTab (List ℕ) := .ofNamed (fun cs : List String ↦ cs.map encS) glCallers\n\n'
             '/-- `monoCallers` by its names\' codes. -/\nnoncomputable def monoT : NTab ℕ := .ofNamed encS monoCallers\n\n'
             '/-- `anyLink`\'s callees by their names\' codes. -/\n'
             'noncomputable def anyT : NTab Unit := .ofNamed (fun _ ↦ ()) anyLink.fams\n\n'
             '/-- **The tables of the facts carried to callees**: the generator\'s, pinned to their lists by `tabOk`, and\n'
             'the callers\' short lists\' built from them by the kernel. -/\n'
             'noncomputable def downT : DownT :=\n'
             '  ⟨carriedT, carriedNzT, nzUpT, ownNzT, expCarryT, termT, glT, monoT, anyT, encS anyLink.oName⟩\n\n'
             'end\n\nend LeanVM.Guest.Res\n')
    files[mod] = ''.join(t)
    ok = [header('LeanVM.Guest.CoreMode.Gen.DownOk', 'Each family carried to callees, by range, from its walk.')]
    ok.append(''.join('public import LeanVM.Guest.CoreMode.Gen.Down%d\n' % k for k in range(len(resgen.DOWN_RANGES))))
    ok.append('public import LeanVM.Guest.CoreMode.Fam.ResDown\n\nnamespace LeanVM.Guest.Res\n\n'
              'open LeanVM.Guest.Memory\n\npublic section\n\n'
              '/-! The callers\' tables hold their lists. -/\n\n'
              'theorem termT_ok : tabIn termCallers termT encS = true := ofNamed_all _ _\n\n'
              'theorem glT_ok : tabIn glCallers glT (fun cs : List String ↦ cs.map encS) = true := ofNamed_all _ _\n\n'
              'theorem monoT_ok : tabIn monoCallers monoT encS = true := ofNamed_all _ _\n\n'
              'theorem anyT_ok : tabIn anyLink.fams anyT (fun _ ↦ ()) = true := ofNamed_all _ _\n\n')
    for k, (a, m) in enumerate(resgen.down_ranges()):
        mod = 'LeanVM.Guest.CoreMode.Gen.Down%d' % k
        t = [header(mod, 'The facts carried to callees, every family, functions %d to %d.' % (a, a + m - 1))]
        t.append('public import LeanVM.Guest.CoreMode.Gen.DownTab\nmeta import LeanVM.Guest.Packed.NatLit\n\n'
                 'namespace LeanVM.Guest.Res\n\nopen LeanVM.Guest.Memory\n\npublic section\n\n')
        for w, bits, what in (('gW', lambda j: gbits[names[keys[j]]], '`Bridge.spine` the carried facts\''),
                              ('nzW', lambda j: nzbits[names[keys[j]]], '`Memory.spineE` the nonzero facts\''),
                              ('expW', lambda j: expw[j], '`Memory.spineE` the exponent bounds\'')):
            items = [(j, bits(j)) for j in range(a, a + m) if bits(j)]
            t.append('/-- The sub-spines of %s searches use, by function index. -/\nnoncomputable def %s%d : NTree ℕ :=\n'
                     '  %s\n\n' % (what, w, a, packed.ntree(items, packed.bits)))
        t.append('/-- Every family\'s check, one walk of each function\'s body. -/\n'
                 'theorem down_%d : RangeOk (fun j fn ↦ downH downT fn ⟨witAt gW%d j, witAt nzW%d j, witAt expW%d j⟩) '
                 '%d %d := by\n  unfold RangeOk; decide +kernel\n\nend\n\nend LeanVM.Guest.Res\n' % (a, a, a, a, a, m))
        files[mod] = ''.join(t)
        for name, chk, of in FAMS:
            ok.append('theorem %s_%d : RangeOk (fun _ fn => %s fn) %d %d :=\n  RangeOk.imp (fun _ _ h ↦ %s h) down_%d\n\n'
                      % (name, a, chk, a, m, of, a))
    ok.append('end\n\nend LeanVM.Guest.Res\n')
    files['LeanVM.Guest.CoreMode.Gen.DownOk'] = ''.join(ok)
    return {os.path.join(OUT, m.split('.')[-1] + '.lean'): v for m, v in files.items()}


def main(argv):
    files = render()
    mine = [os.path.join(OUT, f) for f in ('CarryNzList.lean', 'CarryTab.lean', 'ExpCarryTab.lean')]
    bad = genfiles.sync(files, glob.glob(os.path.join(OUT, 'Down*.lean')) + [p for p in mine if os.path.exists(p)],
                        '--check' in argv)
    genfiles.fail_if_stale(bad, '--check' in argv)
    print('Down: %d files, %s' % (len(files), 'unchanged' if not bad else ('stale' if '--check' in argv else 'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
