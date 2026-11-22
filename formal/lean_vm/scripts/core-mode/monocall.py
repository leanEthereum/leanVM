"""Writes `Guest/CoreMode/Gen/MonoCallers{k}.lean` and `MonoWalkOk.lean`: the callers' check of
`child_claim_list_mono` and its callees over the whole program by ranges (`Res.monoCallers`) and the gap walk's
other checks (`EndExec.MonoOk`, `mono_ok`), which the core route's `ml` family reads. `--check` writes nothing
and fails when a file differs.
Usage: python3 -I scripts/core-mode/monocall.py [--check]"""
import sys, os, glob

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import resgen
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402

OUT = resgen.OUT


header = genfiles.header('core-mode/monocall.py')


def render():
    files = {}
    n = resgen.coreCount()
    ranges = [(a, (n - a) if m is None else m) for a, m in resgen.RANGES]
    mods = []
    for k, (a, m) in enumerate(ranges):
        mod = 'LeanVM.Guest.CoreMode.Gen.MonoCallers%d' % k
        t = [header(mod, 'The callers\' check of `monoCallers`, functions %d to %d.' % (a, a + m - 1))]
        t.append('public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.MonoDefs\n\nnamespace LeanVM.Guest.Res\n\nopen LeanVM.Guest.Memory\n\n'
                 'public section\n\ntheorem monoCallers_%d : RangeOk (fun _ fn => callersG monoCallers fn) %d %d := by\n'
                 '  unfold RangeOk; decide +kernel\n\nend\n\nend LeanVM.Guest.Res\n' % (a, a, m))
        files[mod] = ''.join(t); mods.append(mod)
    mod = 'LeanVM.Guest.CoreMode.Gen.MonoWalkOk'
    t = [header(mod, 'The gap walk\'s checks.')]
    t.append(''.join('public import %s\n' % m for m in mods))
    t.append('public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.ResMR\n\n'
             'namespace LeanVM.Guest.EndExec\n\nopen LeanVM.Guest LeanVM.Guest.Res LeanVM.Guest.Memory\n\n'
             'public section\n\n')
    app = 'monoCallers_0'
    for a, m in ranges[1:]: app = '(%s.append monoCallers_%d)' % (app, a)
    t.append('/-- **The callers\' check of `monoCallers`, every function.** -/\n'
             'theorem monoCallers_all : RangeOk (fun _ fn => callersG monoCallers fn) 0 coreProgram.length := by\n'
             '  have h := %s\n  rw [coreProgram_length]\n  exact h\n\n' % app)
    t.append('/-- **The gap walk\'s checks.** -/\ntheorem mono_ok : MonoOk where\n'
             '  idx := by decide +kernel\n  origin := by decide +kernel\n  loop0 := by decide +kernel\n'
             '  loop1 := by decide +kernel\n  ml := by decide +kernel\n  digest := by decide +kernel\n'
             '  callers := rangeOk_all monoCallers_all\n\nend\n\nend LeanVM.Guest.EndExec\n')
    files[mod] = ''.join(t)
    return {os.path.join(OUT, m.split('.')[-1] + '.lean'): v for m, v in files.items()}


def main(argv):
    files = render()
    bad = genfiles.sync(files, glob.glob(os.path.join(OUT, 'MonoCallers*.lean')), '--check' in argv)
    genfiles.fail_if_stale(bad, '--check' in argv)
    print('MonoWalk: %d files, %s' % (len(files), 'unchanged' if not bad else ('stale' if '--check' in argv else 'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
