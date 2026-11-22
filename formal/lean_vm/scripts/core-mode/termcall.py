"""Writes `Guest/CoreMode/Gen/TermCallers{k}.lean` and `TermCallers.lean`: the callers' check of
`check_opening_terminal` and the `column_selector` specializations over the whole program by ranges
(`Res.termCallers`, `Res.callersG`), the ranges `resgen.RANGES`; and `GlCallers{k}.lean`, `GlCallers.lean`, of
`verify_bus_gkr`'s layers (`Res.glCallers`, `Res.callersM`).
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


# the checks: file stem, the list, the check, what it checks
FAMS = [('TermCallers', 'termCallers', 'callersG'), ('GlCallers', 'glCallers', 'callersM')]


def render():
    files = {}
    n = resgen.coreCount()
    ranges = [(a, (n - a) if m is None else m) for a, m in resgen.RANGES]
    for stem, lst, chk in FAMS:
        mods = []
        for k, (a, m) in enumerate(ranges):
            mod = 'LeanVM.Guest.CoreMode.Gen.%s%d' % (stem, k)
            t = [header(mod, 'The callers\' check of `%s`, functions %d to %d.' % (lst, a, a + m - 1))]
            t.append('public import LeanVM.Guest.CoreMode.Fam.LinkDefs\npublic import LeanVM.Guest.CoreMode.Fam.TermDefs\n\n'
                     'namespace LeanVM.Guest.Res\n\nopen LeanVM.Guest.Memory\n\n'
                     'public section\n\ntheorem %s_%d : RangeOk (fun _ fn => %s %s fn) %d %d := by\n'
                     '  unfold RangeOk; decide +kernel\n\nend\n\nend LeanVM.Guest.Res\n' % (lst, a, chk, lst, a, m))
            files[mod] = ''.join(t); mods.append(mod)
        mod = 'LeanVM.Guest.CoreMode.Gen.%s' % stem
        t = [header(mod, 'The callers\' check of `%s`, every function.' % lst)]
        t.append(''.join('public import %s\n' % m for m in mods))
        t.append('public import LeanVM.Guest.CoreMode.Fam.LinkDefs\n\nnamespace LeanVM.Guest.Res\n\n'
                 'open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory\n\npublic section\n\n')
        app = '%s_0' % lst
        for a, m in ranges[1:]: app = '(%s.append %s_%d)' % (app, lst, a)
        t.append('/-- **The callers\' check of `%s`, every function.** -/\n'
                 'theorem %s_all : ∀ fn ∈ coreProgram, %s %s fn = true := by\n'
                 '  have h := %s\n  exact rangeOk_all (by rw [coreProgram_length]; exact h)\n\nend\n\n'
                 'end LeanVM.Guest.Res\n' % (lst, lst, chk, lst, app))
        files[mod] = ''.join(t)
    return {os.path.join(OUT, m.split('.')[-1] + '.lean'): v for m, v in files.items()}


def main(argv):
    files = render(); bad = []
    bad = genfiles.sync(files, glob.glob(os.path.join(OUT, 'TermCallers*.lean')) +
                        glob.glob(os.path.join(OUT, 'GlCallers*.lean')), '--check' in argv)
    genfiles.fail_if_stale(bad, '--check' in argv)
    print('TermCallers, GlCallers: %d files, %s' % (len(files), 'unchanged' if not bad else ('stale' if '--check' in argv else 'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
