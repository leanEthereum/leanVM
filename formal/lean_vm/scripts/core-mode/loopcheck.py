"""Writes `Guest/CoreMode/Gen/LoopCheck*.lean`: the kernel's check of `Res.termChk` (`Guest/CoreMode/Fam/LoopDefs.lean`)
over the guest's core IR, by ranges of functions (`Memory.RangeOk`), each range at most `BUDGET`
bytes of core IR, a function with a pack of its own alone; a function the memory check splits by ranges of its statements
(`Memory/GuestMem/Fn{j}.lean`) is checked by the same ranges (`Res.entL_drop`). The functions' names
and order are `Memory/GuestCallees.lean`'s, their sizes their `Pack/*/Core*.lean` text.
`--check` writes nothing and fails when a file differs.
Usage: python3 -I scripts/core-mode/loopcheck.py [--check]"""
import sys, os, re, glob

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
sys.path.insert(0, HERE)
import compiled as C  # noqa: E402
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
OUT = os.path.join(ROOT, 'CoreMode', 'Gen')
# a range's core IR, at most this many bytes (the kernel's memory grows with it)
import windows  # noqa: E402
BUDGET = windows.RANGE_BUDGET
# a range, at most this many functions
MAXN = 150
# ranges per module
PERMOD = 1


def names():
    s = open(os.path.join(ROOT, 'Memory', 'GuestCallees.lean')).read()
    nm = {int(k): v for k, v in re.findall(r'\.node (\d+) \("([^"]+)"\)', s.split('def nameT')[0] + s)}
    n = max(nm) + 1
    assert all(j in nm for j in range(n))
    return [nm[j] for j in range(n)]


def sizes():
    """Each function's bytes of core IR; a function whose body a pack of its own splits over
    `Core*.lean`, all of them."""
    BD = C.BD
    sz = {}
    for p in BD.core_paths():
        t = BD.read_text(p)
        for blk in t.split('\nnamespace LeanVM.Guest.Fn.«')[1:]:
            m = re.search(r'name := "([^"]+)"', blk)
            if m: sz[m.group(1)] = sz.get(m.group(1), 0) + len(blk)
    for key in BD.own_packs():
        c = os.path.join(ROOT, 'Pack', key, 'Core.lean')
        if not os.path.exists(c): continue
        m = re.search(r'name := "([^"]+)"', BD.read_text(c))
        sz[m.group(1)] = sum(len(BD.read_text(f)) for f in glob.glob(os.path.join(ROOT, 'Pack', key, 'Core*.lean')))
    return sz


def alone():
    """The functions with a pack of their own (the heavy ones), each checked as a range of its own."""
    BD = C.BD
    blocks = BD.bundle_blocks()
    # a pack of its own holding its bundle too
    return {BD.code_of(blocks[key][1])[0] for key in BD.own_packs() if key in blocks and blocks[key][0] == key}


def splits():
    """Each function the memory check splits: its statement ranges `(a, n)` and the end."""
    out = {}
    for f in glob.glob(os.path.join(ROOT, 'Memory', 'GuestMem', 'Fn*.lean')):
        j = int(re.search(r'Fn(\d+)\.lean$', f).group(1))
        rs = set()
        for b in glob.glob(os.path.join(ROOT, 'Memory', 'GuestMem', 'Big%d_*.lean' % j)):
            rs |= {(int(a), int(n)) for a, n in re.findall(r'body\.drop (\d+)\)\.take (\d+)\)', open(b).read())}
        end = max(a + n for a, n in rs)
        out[j] = (sorted(rs), end)
    return out


header = genfiles.header('core-mode/loopcheck.py')


def rangeThm(a, n):
    return ('set_option maxRecDepth 100000 in\ntheorem termRange_%d : RangeOk (fun _ fn => termChk fn) %d %d := by\n'
            '  unfold RangeOk; decide +kernel\n\n') % (a, a, n)


def render():
    nm = names(); sz = sizes(); sp = splits(); al = alone(); N = len(nm)
    ranges = []; cur = None
    for j in range(N):
        if j in sp:
            if cur: ranges.append(cur); cur = None
            ranges.append(('fn', j)); continue
        w = sz.get(nm[j], 0)
        if nm[j] in al:
            if cur: ranges.append(cur); cur = None
            ranges.append(['rng', j, 1, w]); continue
        if cur and (cur[3] + w > BUDGET or cur[2] >= MAXN): ranges.append(cur); cur = None
        if not cur: cur = ['rng', j, 0, 0]
        cur[2] += 1; cur[3] += w
    if cur: ranges.append(cur)
    files = {}; mods = []
    plain = [r for r in ranges if r[0] == 'rng']
    for k in range(0, len(plain), PERMOD):
        mod = 'LeanVM.Guest.CoreMode.Gen.LoopCheck%d' % (k // PERMOD)
        t = [header(mod, 'Kernel checks of `Res.termChk` on ranges of the guest\'s functions.')]
        t.append('public import LeanVM.Guest.CoreMode.Fam.LoopDefs\n\nnamespace LeanVM.Guest.Res\n\n'
                 'open LeanVM.Guest.Core LeanVM.Guest.Memory\n\n@[expose] public section\n\n')
        for r in plain[k:k + PERMOD]: t.append(rangeThm(r[1], r[2]))
        t.append('end\n\nend LeanVM.Guest.Res\n')
        files[mod] = ''.join(t); mods.append(mod)
    for j, (rs, end) in sorted(sp.items()):
        parts = []
        for m in range(0, len(rs), 8):
            mod = 'LeanVM.Guest.CoreMode.Gen.LoopCheckBig%d_%d' % (j, m // 8)
            t = [header(mod, 'Kernel checks of `Res.entL` on ranges of function %d\'s statements.' % j)]
            t.append('public import LeanVM.Guest.CoreMode.Fam.LoopDefs\npublic import LeanVM.Guest.Memory.GuestMem.Data\n\n'
                     'namespace LeanVM.Guest.Res\n\nopen LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory\n\n'
                     '@[expose] public section\n\n')
            for a, n in rs[m:m + 8]:
                t.append(('set_option maxRecDepth 100000 in\ntheorem term%d_%d : entL Data.core%d.loop [] '
                          '(((bodyOf Data.core%d).drop %d).take %d) = true := by\n  decide +kernel\n\n') % (j, a, j, j, a, n))
            t.append('end\n\nend LeanVM.Guest.Res\n')
            files[mod] = ''.join(t); parts.append(mod)
        mod = 'LeanVM.Guest.CoreMode.Gen.LoopCheckFn%d' % j
        t = [header(mod, '`Res.termChk` of function %d, by ranges of its statements.' % j)]
        t.append(''.join('public import %s\n' % p for p in parts))
        t.append('\nnamespace LeanVM.Guest.Res\n\nopen LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory\n\n'
                 '@[expose] public section\n\nset_option maxRecDepth 100000 in\n'
                 'theorem termRange_%d : RangeOk (fun _ fn => termChk fn) %d 1 := by\n' % (j, j))
        t.append('  have h%d : entL Data.core%d.loop [] ((bodyOf Data.core%d).drop %d) = true :=\n'
                 '    entL_end (by decide +kernel)\n' % (end, j, j, end))
        nxt = end
        for a, n in reversed(rs):
            assert a + n == nxt, (j, a, n, nxt)
            t.append('  have h%d : entL Data.core%d.loop [] ((bodyOf Data.core%d).drop %d) = true :=\n'
                     '    entL_drop (n := %d) term%d_%d h%d\n' % (a, j, j, a, n, j, a, nxt))
            nxt = a
        assert nxt == 0
        t.append('  exact RangeOk.one (fn := Data.core%d) rfl (termChk_of (by decide +kernel) h0)\n\n'
                 'end\n\nend LeanVM.Guest.Res\n' % j)
        files[mod] = ''.join(t); mods.append(mod)
    # the assembly
    mod = 'LeanVM.Guest.CoreMode.Gen.LoopCheck'
    t = [header(mod, 'Every function of the guest passes `Res.termChk` (`termAll`).')]
    t.append(''.join('public import %s\n' % m for m in sorted(mods)))
    t.append('\nnamespace LeanVM.Guest.Res\n\nopen LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory\n\n'
             '@[expose] public section\n\nset_option maxRecDepth 100000 in\n'
             '/-- **Every function of the guest passes `termChk`.** -/\n'
             'theorem termAll : RangeOk (fun _ fn => termChk fn) 0 coreProgram.length := by\n')
    acc = None; k = 0
    for r in ranges:
        a, n = (r[1], r[2]) if r[0] == 'rng' else (r[1], 1)
        if acc is None:
            assert a == 0
            t.append('  have h%d : RangeOk (fun _ fn => termChk fn) 0 %d := termRange_%d\n' % (k, n, a))
        else:
            t.append('  have h%d : RangeOk (fun _ fn => termChk fn) 0 %d := h%d.append (m := %d) termRange_%d\n'
                     % (k, a + n, k - 1, n, a))
        acc = a + n; k += 1
    assert acc == N
    t.append('  rw [coreProgram_length]; exact h%d\n\nend\n\nend LeanVM.Guest.Res\n' % (k - 1))
    files[mod] = ''.join(t)
    return {os.path.join(OUT, m.split('.')[-1] + '.lean'): v for m, v in files.items()}


def main(argv):
    files = render()
    bad = genfiles.sync(files, glob.glob(os.path.join(OUT, 'LoopCheck*.lean')), '--check' in argv)
    genfiles.fail_if_stale(bad, '--check' in argv)
    print('LoopCheck: %d files, %s' % (len(files), 'unchanged' if not bad else ('stale' if '--check' in argv else 'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
