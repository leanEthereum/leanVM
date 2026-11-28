"""Writes `Guest/CoreMode/Gen/TermCallers.lean`: the callers' check of `check_opening_terminal` and the
`column_selector` specializations over the whole program (`Res.termCallers`, `Res.callersG`); `GlCallers.lean`, of
`verify_bus_gkr`'s layers (`Res.glCallers`, `Res.callersM`); and `ExpCarry.lean`, the call sites carrying the listed
parameters' exponent bounds (`CoreMode.FnReg.expCarry`, `CoreMode.carryExpB`; its list `carry_list`, which `down.py`
writes as a table with its hints). Each from the ranges `down.py` checks (`Gen/DownOk.lean`, every family carried down
in one walk).
`--check` writes nothing and fails when a file differs.
Usage: python3 -I scripts/core-mode/termcall.py [--check]"""
import sys, os, glob

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import resgen
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402

OUT = resgen.OUT


header = genfiles.header('core-mode/termcall.py')


# the aggregates: file stem, the theorems' name, the check of one function
FAMS = [('TermCallers', 'termCallers', 'callersG termCallers'), ('GlCallers', 'glCallers', 'callersM glCallers'),
        ('ExpCarry', 'expCarry', 'CoreMode.carryExpB CoreMode.FnReg.expCarry')]


def render():
    files = {}
    ranges = resgen.down_ranges()
    for stem, lst, chk in FAMS:
        mod = 'LeanVM.Guest.CoreMode.Gen.%s' % stem
        t = [header(mod, 'The callers\' check of `%s`, every function.' % lst)]
        t.append(''.join('public import %s\n' % m for m in resgen.down_mods()))
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
    bad = genfiles.sync(files, (), '--check' in argv)
    genfiles.fail_if_stale(bad, '--check' in argv)
    print('TermCallers, GlCallers, ExpCarry: %d files, %s' % (len(files), 'unchanged' if not bad else ('stale' if '--check' in argv else 'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
