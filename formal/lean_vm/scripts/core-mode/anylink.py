"""Writes `Guest/CoreMode/Gen/AnyLink.lean`, `AnyCallers{k}.lean` and `AnyLinkOk.lean`: the callees of
`child_claim_list_any` that read its entries table (`Res.anyLink`: each callee with the positions of the
caller's entries parameter and bound quotient among its call's arguments), the callers' check over the whole
program by ranges, and the link's checks (`EndExec.LinkOk`, `anyLink_ok`). The callees are those every call
site of the caller passes both its entries parameter and its bound's quotient, read off its core IR
(`Pack/*/Core.lean`) alone: the core route's `glOk` links their caller's cells.
`--check` writes nothing and fails when a file differs.
Usage: python3 -I scripts/core-mode/anylink.py [--check]"""
import sys, os, re, glob

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.append(os.path.join(HERE, '..'))
import genfiles  # noqa: E402
import coreir
import resgen
import coredata

ROOT = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
OUT = os.path.join(ROOT, 'CoreMode', 'Gen')
# the caller: its stable name, its entries and bound parameters
import fnrules  # noqa: E402
ORIGIN, = fnrules.table('ANY_ORIGIN')
UE, UL = (fnrules.param(ORIGIN, p) for p in fnrules.table('ANY_PARAMS')[ORIGIN])
RANGES = resgen.RANGES


def names():
    """Each compiler name's stable name (`Data/NameStrings.lean`)."""
    return {c: s for s, c in coredata.name_strings(os.path.join(ROOT, 'Data'))[0]}


def sites(ss, out):
    """Every call site of a body, nested ones included: `(callee, args)`."""
    for s in ss:
        if s[0] == 'call': out.append((s[1], s[2]))
        elif s[0] == 'callIf': out.append((s[2], s[3]))
        elif s[0] == 'dispatch': out.extend((f, s[3]) for f in s[2])
        elif s[0] == 'ite': sites(s[2], out); sites(s[3], out)
        elif s[0] == 'match':
            for a in s[2]: sites(a, out)
    return out


def atoms(ss, out):
    for s in ss:
        if s[0] == 'a': out.append(s[1])
        elif s[0] == 'ite': atoms(s[2], out); atoms(s[3], out)
        elif s[0] == 'match':
            for a in s[2]: atoms(a, out)
    return out


def link():
    """The callees `(stable name, kE, kL)`, the bound quotient `w` and the constant `c`."""
    stable = names()
    params, body, _ = coreir.BD.core_fn(coreir.BD.core_texts()[ORIGIN])
    uE, uL = params[UE], params[UL]
    (w, c), = {(a[2], a[3]) for a in atoms(body, []) if a[0] == 'mul' and a[1] == uL}
    by = {}
    for f, args in sites(body, []): by.setdefault(f, []).append(args)
    fams = []
    for f in sorted(by, key=lambda f: stable.get(f, f)):
        if not all(uE in a and w in a for a in by[f]): continue
        ks = {(a.index(uE), a.index(w)) for a in by[f]}
        assert len(ks) == 1, (f, ks)
        fams.append((stable.get(f, f),) + ks.pop())
    return fams, w, c


header = genfiles.header('core-mode/anylink.py')


def render():
    fams, w, c = link(); files = {}
    n = resgen.coreCount()
    ranges = [(a, (n - a) if m is None else m) for a, m in RANGES]
    assert sum(m for _, m in ranges) == n
    mod = 'LeanVM.Guest.CoreMode.Gen.AnyLink'
    t = [header(mod, 'The callees reading `child_claim_list_any`\'s entries table.')]
    t.append('public import LeanVM.Guest.CoreMode.Fam.LinkDefs\n\nnamespace LeanVM.Guest.Res\n\nopen LeanVM.Guest LeanVM.Guest.Core\n\n'
             '@[expose] public section\n\n/-- **The callees reading `child_claim_list_any`\'s entries table.** -/\n'
             'noncomputable def anyLink : Link := ⟨[\n  %s],\n  fn_idx%% «%s», name%% «%s», .n %d, .n %d, .n %d, .n %d⟩\n\n'
             'end\n\nend LeanVM.Guest.Res\n' % (',\n  '.join('(name%% «%s», %d, %d)' % F for F in fams),
                                                ORIGIN, ORIGIN, UE, UL, w, c))
    files[mod] = ''.join(t)
    mods = []
    for k, (a, m) in enumerate(ranges):
        mod = 'LeanVM.Guest.CoreMode.Gen.AnyCallers%d' % k
        t = [header(mod, 'The callers\' check of `anyLink`, functions %d to %d.' % (a, a + m - 1))]
        t.append('public import LeanVM.Guest.CoreMode.Gen.AnyLink\n\nnamespace LeanVM.Guest.Res\n\nopen LeanVM.Guest.Memory\n\n'
                 'public section\n\ntheorem anyCallers_%d : RangeOk (fun _ fn => callersB anyLink fn) %d %d := by\n'
                 '  unfold RangeOk; decide +kernel\n\nend\n\nend LeanVM.Guest.Res\n' % (a, a, m))
        files[mod] = ''.join(t); mods.append(mod)
    mod = 'LeanVM.Guest.CoreMode.Gen.AnyLinkOk'
    t = [header(mod, '`anyLink`\'s checks.')]
    t.append(''.join('public import %s\n' % m for m in mods))
    t.append('public import LeanVM.Guest.CoreMode.Fam.ResA\n\n'
             'namespace LeanVM.Guest.EndExec\n\nopen LeanVM.Guest LeanVM.Guest.Res LeanVM.Guest.Memory\n\n'
             'public section\n\n')
    app = 'anyCallers_0'
    for a, m in ranges[1:]: app = '(%s.append anyCallers_%d)' % (app, a)
    t.append('/-- **The callers\' check of `anyLink`, every function.** -/\n'
             'theorem anyCallers_all : RangeOk (fun _ fn => callersB anyLink fn) 0 coreProgram.length := by\n'
             '  have h := %s\n  rw [coreProgram_length]\n  exact h\n\n' % app)
    t.append('/-- **`anyLink`\'s checks.** -/\n'
             'theorem anyLink_ok : LinkOk anyLink where\n'
             '  idx := by decide +kernel\n'
             '  origin := by decide +kernel\n'
             '  fams := List.all_eq_true.mp (show anyLink.fams.all calleeB = true by decide +kernel)\n'
             '  callers := rangeOk_all anyCallers_all\n'
             '  main := fun F hF ↦ of_decide_eq_true (List.all_eq_true.mp\n'
             '    (show anyLink.fams.all (fun F ↦ decide (F.1 ≠ "main")) = true by decide +kernel) F hF)\n\n'
             'end\n\nend LeanVM.Guest.EndExec\n')
    files[mod] = ''.join(t)
    return files


def path(mod):
    return os.path.join(ROOT, *mod.split('.')[2:]) + '.lean'


def main(argv):
    check = '--check' in argv
    files = {path(m): text for m, text in render().items()}
    stale = genfiles.sync(files, glob.glob(os.path.join(OUT, 'AnyCallers*.lean')), check)
    print('anylink: %d files, %d stale%s' % (len(files), len(stale), (': ' + ', '.join(stale)) if stale else ''))
    return 1 if check and stale else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
