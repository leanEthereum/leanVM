"""Writes `Guest/CoreMode/Gen/TermCallers{k}.lean` and `TermCallers.lean`: the callers' check of
`check_opening_terminal` and the `column_selector` specializations over the whole program by ranges
(`Res.termCallers`, `Res.callersG`), the ranges `resgen.RANGES`; and `GlCallers{k}.lean`, `GlCallers.lean`, of
`verify_bus_gkr`'s layers (`Res.glCallers`, `Res.callersM`); and `ExpCarry{k}.lean`, `ExpCarry.lean`, the call sites
carrying the listed parameters' exponent bounds (`CoreMode.FnReg.expCarry`, `CoreMode.carryExpB`), decided by the
witnessed check (`CoreMode.carryExpW`, `Fam/ExpCWit.lean`) over the table `ExpCarryTab.lean`.
`--check` writes nothing and fails when a file differs.
Usage: python3 -I scripts/core-mode/termcall.py [--check]"""
import sys, os, glob

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import resgen
import carrywit
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402

OUT = resgen.OUT


header = genfiles.header('core-mode/termcall.py')


# the checks: file stem, the theorems' name, the check of one function, its imports, its ranges
_TERM = 'LeanVM.Guest.CoreMode.Fam.CallersWit\npublic import LeanVM.Guest.CoreMode.Fam.TermDefs'
# a callers' check, its witnessed form (`Fam/CallersWit.lean`) and the theorem from it
WIT = {'callersG': ('callersGW', 'callersG_of_wit'), 'callersM': ('callersMW', 'callersM_of_wit')}
FAMS = [('TermCallers', 'termCallers', 'callersG termCallers', _TERM, resgen.RANGES),
        ('GlCallers', 'glCallers', 'callersM glCallers', _TERM, resgen.RANGES),
        ('ExpCarry', 'expCarry', 'CoreMode.carryExpB CoreMode.FnReg.expCarry',
         'LeanVM.Guest.CoreMode.Gen.ExpCarryTab', resgen.RANGES)]


def exp_witness(L):
    """`CoreMode.carryExpW`'s witnesses: by function index, the events of its spine (`Memory.spineE`) its call sites'
    constants are (`constExpS`); a site whose argument no constant of the spine pins is left to `armExpB`."""
    import carry, coredata
    F = carry.functions()
    names = carrywit.name_strings(os.path.join(resgen.ROOT, 'Data', 'NameStrings.lean'))
    keys = coredata.keys(os.path.join(resgen.ROOT, 'Data'))
    pows = carry.POWS()
    pow1 = lambda w: 0 if w == (1, 0) else (pows.get(w[0]) if w is not None and w[1] == 0 else None)
    by = {}
    for g, p, lo, hi in L:
        by.setdefault(names.get(g, g), []).append((p, lo, hi))
    out = {}
    C = carry.Check(F, {}, lambda g, i: False)
    for j, k in enumerate(keys):
        f = names[k]
        sp = carry.spine(F[f]['body'])
        sub = set()
        for g, args, _ in C.sites(f):
            for p, lo, hi in by.get(g, ()):
                if p < len(args):
                    sub.update(next(([i] for i, e in enumerate(sp) if e[0] == 'a' and e[1][0] == 'const' and
                                     e[1][1] == args[p] and pow1(e[1][2]) is not None and lo <= pow1(e[1][2]) < hi), []))
        out[j] = sub
    return out, by


def render():
    files = {}
    n = resgen.coreCount()
    wit, by = exp_witness(carry_list())
    mod = 'LeanVM.Guest.CoreMode.Gen.ExpCarryTab'
    t = [header(mod, 'The table of `CoreMode.FnReg.expCarry` (`Res.tabOk`).')]
    t.append('public import LeanVM.Guest.CoreMode.Fam.LinkDefs\npublic import LeanVM.Guest.CoreMode.Fam.ExpCWit\n'
             'public import LeanVM.Guest.CoreMode.Gen.FnData\n\nnamespace LeanVM.Guest.Res\n\n@[expose] public section\n\n'
             '/-- `CoreMode.FnReg.expCarry` by its names\' codes. -/\nnoncomputable def expCarryT : NTab (ℕ × ℕ × ℕ) :=\n  %s\n\n'
             'end\n\npublic section\n\ntheorem expCarryT_ok : tabOk CoreMode.FnReg.expCarry expCarryT id = true := by\n'
             '  decide +kernel\n\nend\n\nend LeanVM.Guest.Res\n'
             % carrywit.tab([(f, c) for f, cs in by.items() for c in cs], lambda c: '(%d, %d, %d)' % c))
    files[mod] = ''.join(t)
    for stem, lst, chk, imps, rs in FAMS:
        ranges = [(a, (n - a) if m is None else m) for a, m in rs]
        mods = []
        for k, (a, m) in enumerate(ranges):
            mod = 'LeanVM.Guest.CoreMode.Gen.%s%d' % (stem, k)
            t = [header(mod, 'The callers\' check of `%s`, functions %d to %d.' % (lst, a, a + m - 1))]
            if stem == 'ExpCarry':
                items = [(j, wit[j]) for j in range(a, a + m) if wit.get(j)]
                t.append('public import %s\nmeta import LeanVM.Guest.Packed.NatLit\n\n'
                         'namespace LeanVM.Guest.Res\n\nopen LeanVM.Guest.Memory\n\n'
                         '/-- The sub-spines of `CoreMode.carryExpW`, by function index. -/\n'
                         'noncomputable def expW%d : NTree ℕ :=\n  %s\n\npublic section\n\n'
                         'theorem %s_%d : RangeOk (fun _ fn => %s fn) %d %d :=\n'
                         '  RangeOk.imp (fun _ _ h ↦ CoreMode.carryExpB_of_wit expCarryT_ok h)\n'
                         '    (show RangeOk (fun j fn ↦ CoreMode.carryExpW expCarryT fn (witAt expW%d j)) %d %d by\n'
                         '      unfold RangeOk; decide +kernel)\n\nend\n\nend LeanVM.Guest.Res\n'
                         % (imps, a, carrywit.ntree(items, carrywit.hexbits), lst, a, chk, a, m, a, a, m))
            else:
                fw, of = WIT[chk.split()[0]]
                t.append('public import %s\n\n'
                         'namespace LeanVM.Guest.Res\n\nopen LeanVM.Guest.Memory\n\n'
                         'public section\n\ntheorem %s_%d : RangeOk (fun _ fn => %s fn) %d %d :=\n'
                         '  RangeOk.imp (fun _ _ h ↦ %s h)\n'
                         '    (show RangeOk (fun _ fn ↦ %s %s fn) %d %d by unfold RangeOk; decide +kernel)\n\n'
                         'end\n\nend LeanVM.Guest.Res\n' % (imps, lst, a, chk, a, m, of, fw, chk.split()[1], a, m))
            files[mod] = ''.join(t); mods.append(mod)
        mod = 'LeanVM.Guest.CoreMode.Gen.%s' % stem
        t = [header(mod, 'The callers\' check of `%s`, every function.' % lst)]
        t.append(''.join('public import %s\n' % m for m in mods))
        t.append('public import LeanVM.Guest.CoreMode.Fam.LinkDefs\n\nnamespace LeanVM.Guest.Res\n\n'
                 'open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory\n\npublic section\n\n')
        app = '%s_0' % lst
        for a, m in ranges[1:]: app = '(%s.append %s_%d)' % (app, lst, a)
        t.append('/-- **The callers\' check of `%s`, every function.** -/\n'
                 'theorem %s_all : ∀ fn ∈ coreProgram, %s fn = true := by\n'
                 '  have h := %s\n  exact rangeOk_all (by rw [coreProgram_length]; exact h)\n\nend\n\n'
                 'end LeanVM.Guest.Res\n' % (lst, lst, chk, app))
        files[mod] = ''.join(t)
    return {os.path.join(OUT, m.split('.')[-1] + '.lean'): v for m, v in files.items()}


def carry_list():
    """`CoreMode.FnReg.expCarry`: each function's `expCarry` (`CoreMode/Fn/<f>/Data.lean`)."""
    import re
    import fnrules
    out = []
    for p in sorted(glob.glob(os.path.join(fnrules.OWNDIR, '*', 'Data.lean'))):
        if re.search(r'^def expCarry\b', open(p, encoding='utf-8').read(), re.M):
            out += [tuple(x) for x in fnrules.lean_def(os.path.basename(os.path.dirname(p)), 'Data', 'expCarry')]
    return out


def main(argv):
    import callcres
    miss = callcres.carry_misses(carry_list())
    assert not miss, 'termcall: call sites not carrying their callees\' exponent bounds (`carryExpB`): %s' % miss[:8]
    files = render()
    bad = genfiles.sync(files, glob.glob(os.path.join(OUT, 'TermCallers*.lean')) +
                        glob.glob(os.path.join(OUT, 'GlCallers*.lean')) + glob.glob(os.path.join(OUT, 'ExpCarry*.lean')),
                        '--check' in argv)
    genfiles.fail_if_stale(bad, '--check' in argv)
    print('TermCallers, GlCallers, ExpCarry: %d files, %s' % (len(files), 'unchanged' if not bad else ('stale' if '--check' in argv else 'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
