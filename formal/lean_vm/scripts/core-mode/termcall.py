"""Writes `Guest/CoreMode/Gen/ExpCarry{k}.lean` and `ExpCarry.lean`: the call sites carrying the listed parameters'
exponent bounds (`CoreMode.FnReg.expCarry`, `CoreMode.carryExpB`) over the whole program by ranges of `CHUNK`
functions; and `TermCallers{k}.lean`, `TermCallers.lean`: the callers' check of the callees whose facts are carried
(`Res.termCallers`, `Res.callersG`), the same way. `--check` writes nothing and fails when a file differs.
Usage: python3 -I scripts/core-mode/termcall.py [--check]"""
import sys, os, glob

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import resgen
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402

OUT = resgen.OUT
CHUNK = 40


header = genfiles.header('core-mode/termcall.py')


# the checks: file stem, the theorems' name, the check of one function, its imports
# Hotwire has no `check_opening_terminal` nor `verify_bus_gkr`: only the carried exponent bounds are checked.
FAMS = [('ExpCarry', 'expCarry', 'CoreMode.carryExpB CoreMode.FnReg.expCarry',
         'LeanVM.Guest.CoreMode.Fam.LinkDefs\npublic import LeanVM.Guest.CoreMode.Fam.ExpCDefs\n'
         'public import LeanVM.Guest.CoreMode.Gen.FnData'),
        ('TermCallers', 'termCallers', 'callersG termCallers',
         'LeanVM.Guest.CoreMode.Fam.LinkDefs\npublic import LeanVM.Guest.CoreMode.Fam.TermDefs\n'
         'public import LeanVM.Guest.CoreMode.Gen.FnData')]


def steps(name, chk, a, rs):
    """A tactic proof of `RangeOk chk a (Σ m)` from the ranges `rs = [(a, m), …]` (theorems `name % a`), appended one
    at a time, each step's type stated so the elaborator only adds literals."""
    out, n = '', rs[0][1]
    out += '  have h0 : RangeOk (fun _ fn => %s fn) %d %d := %s\n' % (chk, a, n, name % rs[0][0])
    for k, (b, m) in enumerate(rs[1:], 1):
        out += '  have h%d : RangeOk (fun _ fn => %s fn) %d %d := h%d.append %s\n' % (k, chk, a, n + m, k - 1, name % b)
        n += m
    return out + '  exact h%d\n' % (len(rs) - 1)


def render():
    files = {}
    n = resgen.coreCount()
    # ranges of `CHUNK` functions: the check compares callee names, too heavy for the kernel over `resgen.RANGES`
    ranges = [(a, min(CHUNK, n - a)) for a in range(0, n, CHUNK)]
    for stem, lst, chk, imps in FAMS:
        mods = []
        for k, (a, m) in enumerate(ranges):
            mod = 'LeanVM.Guest.CoreMode.Gen.%s%d' % (stem, k)
            t = [header(mod, 'The callers\' check of `%s`, functions %d to %d.' % (lst, a, a + m - 1))]
            # one theorem a function (the kernel's cache is a declaration's), then their ranges appended
            t.append('public import %s\n\nnamespace LeanVM.Guest.Res\n\nopen LeanVM.Guest.Memory\n\n'
                     'public section\n\n' % imps)
            for i in range(a, a + m):
                t.append('theorem %s_%d_%d : RangeOk (fun _ fn => %s fn) %d 1 := by\n'
                         '  unfold RangeOk; decide +kernel\n\n' % (lst, a, i, chk, i))
            t.append('set_option maxRecDepth 100000 in\nset_option maxHeartbeats 4000000 in\ntheorem %s_%d : RangeOk (fun _ fn => %s fn) %d %d := by\n' % (lst, a, chk, a, m))
            t.append(steps('%s_%d_%%d' % (lst, a), chk, a, [(i, 1) for i in range(a, a + m)]))
            t.append('\nend\n\nend LeanVM.Guest.Res\n')
            files[mod] = ''.join(t); mods.append(mod)
        mod = 'LeanVM.Guest.CoreMode.Gen.%s' % stem
        t = [header(mod, 'The callers\' check of `%s`, every function.' % lst)]
        t.append(''.join('public import %s\n' % m for m in mods))
        t.append('public import LeanVM.Guest.CoreMode.Fam.LinkDefs\n\nnamespace LeanVM.Guest.Res\n\n'
                 'open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory\n\npublic section\n\n')
        # the ranges appended one declaration a step, the bounds' sums by `decide` (not by unifying literals)
        t.append('theorem %s_app {chk : ℕ → Fn → Bool} {a n b m k : ℕ} (h1 : RangeOk chk a n) (h2 : RangeOk chk b m)\n'
                 '    (hb : b = a + n) (hk : k = n + m) : RangeOk chk a k := by\n  subst hb hk; exact h1.append h2\n\n' % lst)
        t.append('theorem %s_upto_0 : RangeOk (fun _ fn => %s fn) 0 %d := %s_0\n\n' % (lst, chk, ranges[0][1], lst))
        n_ = ranges[0][1]
        for k, (b_, m_) in enumerate(ranges[1:], 1):
            t.append('theorem %s_upto_%d : RangeOk (fun _ fn => %s fn) 0 %d :=\n  %s_app %s_upto_%d %s_%d (by decide) (by decide)\n\n'
                     % (lst, k, chk, n_ + m_, lst, lst, k - 1, lst, b_))
            n_ += m_
        t.append('set_option maxRecDepth 100000 in\n/-- **The callers\' check of `%s`, every function.** -/\n'
                 'theorem %s_all : ∀ fn ∈ coreProgram, %s fn = true :=\n'
                 '  rangeOk_all (by rw [coreProgram_length]; exact %s_upto_%d)\n\nend\n\nend LeanVM.Guest.Res\n'
                 % (lst, lst, chk, lst, len(ranges) - 1))
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
    bad = genfiles.sync(files, glob.glob(os.path.join(OUT, 'ExpCarry*.lean')) + glob.glob(os.path.join(OUT, 'TermCallers*.lean')),
                        '--check' in argv)
    genfiles.fail_if_stale(bad, '--check' in argv)
    print('ExpCarry, TermCallers: %d files, %s' % (len(files), 'unchanged' if not bad else ('stale' if '--check' in argv else 'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
