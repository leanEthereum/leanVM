"""Writes `Guest/CoreMode/Gen/CarryNzR{k}.lean` and `CarryNzAll.lean`: the nonzero facts' check (`Res.carryNzG`) over
the whole program by ranges, each a kernel check, and `Res.carryNzG_all`. Alone, without `carry.py`'s carried facts'
check (`carryG`), which `CarryOk.lean` pairs with it. Run after `carry.py` (`Gen/CarryNzList.lean`).
`--check` writes nothing and fails when a file differs.
Usage: python3 -I scripts/core-mode/carrynz.py [--check]"""
import sys, os, glob

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.append(os.path.join(HERE, '..'))
import genfiles  # noqa: E402
import resgen  # noqa: E402

# by ranges of functions, each a kernel check: a module's memory grows with its functions' checks, so the heavy ones
# (function `8`, functions `114` to `116` and `264` to `272`) stand alone; the last range runs to the end
RANGES = [(0, 8), (8, 1), (9, 6), (15, 2), (17, 18), (35, 3), (38, 55), (93, 21), (114, 1), (115, 1), (116, 1),
          (117, 38), (155, 99), (254, 6), (260, 2), (262, 2), (264, 1), (265, 1), (266, 1), (267, 1), (268, 1),
          (269, 1), (270, 1), (271, 1), (272, 1), (273, 2), (275, 127), (402, 140), (542, 34), (576, 40), (616, 39),
          (655, 42), (697, 40), (737, 41), (778, 40), (818, 41), (859, 43), (902, 42), (944, 40), (984, 47),
          (1031, 61), (1092, 42), (1134, 44), (1178, 45), (1223, 45), (1268, 41), (1309, 45), (1354, 56), (1410, 62),
          (1472, 64), (1536, None)]

OUT = resgen.OUT
header = genfiles.header('core-mode/carrynz.py')


def render():
    files = {}
    n = resgen.coreCount()
    ranges = [(a, (n - a) if m is None else m) for a, m in RANGES]
    assert sum(m for _, m in ranges) == n and all(m > 0 for _, m in ranges), ranges
    mods = []
    for k, (a, m) in enumerate(ranges):
        mod = 'LeanVM.Guest.CoreMode.Gen.CarryNzR%d' % k
        files[mod] = (header(mod, 'The nonzero facts\' check, functions %d to %d.' % (a, a + m - 1)) +
                      'public import LeanVM.Guest.CoreMode.Fam.CarryDefs\n\nnamespace LeanVM.Guest.Res\n\n'
                      'open LeanVM.Guest.Memory\n\npublic section\n\n'
                      'theorem carryNzR_%d : RangeOk (fun _ fn => carryNzG fn) %d %d := by\n'
                      '  unfold RangeOk; decide +kernel\n\nend\n\nend LeanVM.Guest.Res\n' % (a, a, m))
        mods.append(mod)
    mod = 'LeanVM.Guest.CoreMode.Gen.CarryNzAll'
    # adjacent ranges joined pairwise, each step's range written out, so no term nests deeply
    level, steps, k = [('carryNzR_%d' % a, a, m) for a, m in ranges], [], 0
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level) - 1, 2):
            (h1, a, m1), (h2, _, m2) = level[i], level[i + 1]
            steps.append('  have h%d : RangeOk (fun _ fn => carryNzG fn) %d %d := RangeOk.append (n := %d) (m := %d) %s %s\n'
                         % (k, a, m1 + m2, m1, m2, h1, h2))
            nxt.append(('h%d' % k, a, m1 + m2)); k += 1
        if len(level) % 2:
            nxt.append(level[-1])
        level = nxt
    app = level[0][0]
    files[mod] = (header(mod, 'The nonzero facts\' check, every function.') +
                  ''.join('public import %s\n' % m for m in mods) +
                  'public import LeanVM.Guest.CoreMode.Fam.LinkDefs\n\nnamespace LeanVM.Guest.Res\n\n'
                  'open LeanVM.Guest LeanVM.Guest.Memory\n\npublic section\n\n'
                  '/-- **The nonzero facts\' check, every function.** -/\n'
                  'theorem carryNzG_all : ∀ fn ∈ coreProgram, carryNzG fn = true := by\n' + ''.join(steps) +
                  '  have h := %s\n'
                  '  have h\' : RangeOk (fun _ fn => carryNzG fn) 0 coreProgram.length := by\n'
                  '    rw [coreProgram_length]; exact h\n'
                  '  exact rangeOk_all h\'\n\nend\n\nend LeanVM.Guest.Res\n' % app)
    return {os.path.join(OUT, m.split('.')[-1] + '.lean'): v for m, v in files.items()}


def main(argv):
    check = '--check' in argv
    files = render()
    bad = genfiles.sync(files, glob.glob(os.path.join(OUT, 'CarryNzR*.lean')) +
                        glob.glob(os.path.join(OUT, 'CarryNzAll.lean')), check)
    genfiles.fail_if_stale(bad, check)
    print('CarryNz: %d files, %s' % (len(files), 'unchanged' if not bad else ('stale' if check else 'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
