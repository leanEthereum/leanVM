"""Writes `LeanVM/Guest/CoreMode/Gen/FnData.lean`, `FnFams.lean` and `FnSound.lean`: the registries of each function's
own routing facts and families, from its own modules `CoreMode/Fn/<f>/Data.lean`, `Fam.lean`, `Sound.lean` (namespace
`LeanVM.Guest.CoreMode.Own.<f>`). A kind is a list each function's module may define; its registry is their
concatenation, and its soundness (`<kind>_ok` in the function's `Sound.lean`, of each entry the kind's predicate) theirs.
The shared checks and theorems read the registries only, so no shared file names a function, and a guest edit to one
function changes that function's own modules at most (`formal/notes/core-mode.md`).
It also checks each rule file's `OWN` (`own_files`): the hand files a change to that function alone may change.
`--check` writes nothing and fails when a file differs.
Usage: python3 -I scripts/core-mode/fnreg.py [--check]"""
import ast, os, re, sys, glob
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
LV = os.path.normpath(os.path.join(HERE, '..', '..'))
RULES = os.path.join(HERE, 'fn')
GUEST = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
FN = os.path.join(GUEST, 'CoreMode', 'Fn')
OUT = os.path.join(GUEST, 'CoreMode', 'Gen')

# kind: (module, type, soundness predicate or None, what)
KINDS = {
    'expFacts': ('Data', 'List (String × ℕ × Option ℕ × ℕ)', 'EndExec.ExpOk',
                 'exponent facts at listed parameters: function, parameter, offset, bound (`Res.expFacts`)'),
    'dimFacts': ('Data', 'List (String × ℕ × ℕ × List (ℕ × ℕ))', 'EndExec.DimOk',
                 'dimension facts: function, base parameter, bound parameter, pairs (`Res.dimFacts`)'),
    'expVals': ('Data', 'List (String × ℕ × ℕ)', 'EndExec.ExpValOk',
                'exponent facts of values: function, value, bound (`CoreMode.expQ0`)'),
    'stLoops': ('Data', 'List (String × ℕ × ℕ × ℕ)', 'EndExec.StLoopOk',
                'the loops reading the proof stream past a cursor: `(name, D, v, S)` (`CoreMode.stLoops`)'),
    'nzs': ('Data', 'List (String × Core.V)', 'EndExec.NzOk',
            'the parameters whose nonzero values the core route\'s residuals are (`CoreMode.coreNzs`)'),
    'stCallers': ('Data', 'List (String × String)', None,
                  'the callees whose facts are carried, and their callers (`Res.termCallers`, `Res.callersG`)'),
    'mlLoops': ('Data', 'List (String × ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ))', 'EndExec.MlLoopOk',
                'the specializations of a ghost family over a caller\'s table: name, index, entry, first gap, the gaps\' '
                'stride, the parameter bounding the reads, the caller\'s cells linked (`CoreMode.mlK`)'),
    'cmLoops': ('Data', 'List (String × ℕ × ℕ × ℕ × ℕ × List ℕ)', 'EndExec.CmLoopOk',
                'the frame loops over a caller\'s table: name, claims a frame, entry, first gap, the gaps\' stride, the '
                'caller\'s cells linked (`CoreMode.cmK`)'),
    'glCallers': ('Data', 'List (String × List String)', None,
                  'the callees whose facts are carried, and their callers (`Res.glCallers`, `Res.callersM`)'),
    'fams': ('Fam', 'List (String × (Core.Fn → CRes → Bool))', 'EndExec.OwnOk',
             'the functions\' own residual families, ghost-free (`CoreMode.resFamG`)'),
    'gwFams': ('Fam', 'List (String × (Core.Fn → List (CCell × ℕ) → CRes → Bool))', 'EndExec.GwFamOk',
               'the functions\' own residual families over their own parameter words as ghosts (`CoreMode.resFamG`)'),
}


def own_files():
    """Each rule file's `OWN` (`fn/<f>.py`, read as a literal, the file not run): its function's own hand files, as globs
    under `lean_vm/`, its `CoreMode/Fn/<f>/` modules implied. Every rule file has one, every entry matches a file, no
    file is on two lists, and every `CoreMode/Fn/<f>/` has its rule file. The file of each, by function."""
    errs, owner = [], {}
    rules = sorted(os.path.basename(p)[:-3] for p in glob.glob(os.path.join(RULES, '*.py')))
    for d in sorted(glob.glob(os.path.join(FN, '*'))):
        if os.path.basename(d) not in rules:
            errs.append('CoreMode/Fn/%s has no rule file fn/%s.py' % ((os.path.basename(d),) * 2))
    for f in rules:
        own = None
        for n in ast.parse(open(os.path.join(RULES, f + '.py'), encoding='utf-8').read()).body:
            if isinstance(n, ast.Assign) and any(isinstance(x, ast.Name) and x.id == 'OWN' for x in n.targets):
                own = ast.literal_eval(n.value)
        if own is None:
            errs.append('fn/%s.py has no OWN' % f)
            continue
        implied = 'LeanVM/Guest/CoreMode/Fn/%s/*.lean' % f
        if implied in own:
            errs.append('fn/%s.py: OWN lists %s, which is implied' % (f, implied))
        for e in [x for x in own if x != implied] + ([implied] if os.path.isdir(os.path.join(FN, f)) else []):
            hits = sorted(x for x in glob.glob(os.path.join(LV, e), recursive=True) if os.path.isfile(x))
            if not hits:
                errs.append('fn/%s.py: OWN entry %s matches no file' % (f, e))
            for x in hits:
                x = os.path.relpath(x, LV)
                if owner.setdefault(x, f) != f:
                    errs.append('%s is on the OWN lists of %s and %s' % (x, owner[x], f))
    if errs:
        raise SystemExit('fnreg: OWN:\n  ' + '\n  '.join(errs))
    return owner


header = genfiles.header('core-mode/fnreg.py')


def scan():
    """Each function's modules and the kinds they define."""
    fns = {}
    for d in sorted(glob.glob(os.path.join(FN, '*'))):
        f = os.path.basename(d)
        got = {}
        for part in ('Data', 'Fam', 'Sound'):
            p = os.path.join(d, part + '.lean')
            if os.path.exists(p):
                t = open(p, encoding='utf-8').read()
                got[part] = {k for k in KINDS if re.search(r'^(?:noncomputable )?(?:def|abbrev) %s\b' % k, t, re.M)} | \
                    {k[:-3] for k in re.findall(r'^theorem (\w+_ok)\b', t, re.M)}
        fns[f] = got
    return fns


def render():
    fns = scan()
    files, errs = {}, []
    for f, got in fns.items():
        for k, (part, _, pred, _) in KINDS.items():
            if k in got.get(part, ()) and pred and k not in got.get('Sound', ()):
                errs.append('CoreMode/Fn/%s: %s without its Sound.lean `%s_ok`' % (f, k, k))
    if errs:
        raise SystemExit('fnreg:\n  ' + '\n  '.join(errs))

    def mod(f, part):
        return 'LeanVM.Guest.CoreMode.Fn.%s.%s' % (f, part)

    def reg(part):
        t = []
        for k, (p, ty, _, what) in KINDS.items():
            if p != part:
                continue
            terms = ['Own.%s.%s' % (f, k) for f, got in fns.items() if k in got.get(part, ())]
            title, ref = what.split(' (`')
            t.append('/-- **%s**, each function\'s own (`%s). -/\n%sdef %s : %s :=\n  %s\n\n' % (
                title[0].upper() + title[1:], ref, 'noncomputable ' if part == 'Fam' else '', k, ty,
                ' ++\n  '.join(terms + ['[]'])))
            for f, got in fns.items():
                if k in got.get(part, ()):
                    t.append('theorem %s_of_%s : ∀ x ∈ Own.%s.%s, x ∈ %s := by\n  intro x hx\n  simp [%s, hx]\n\n' % (
                        k, f, f, k, k, k))
        return t
    # the data
    m = 'LeanVM.Guest.CoreMode.Gen.FnData'
    t = [header(m, 'Each function\'s own routing data, by kind.')]
    t += ['public import %s\n' % mod(f, 'Data') for f, got in fns.items() if 'Data' in got]
    t.append('public import LeanVM.Guest.CoreMode.FnReg\n\nnamespace LeanVM.Guest.CoreMode.FnReg\n\n'
             'open LeanVM.Guest LeanVM.Guest.Core\n\n@[expose] public section\n\n')
    t += reg('Data')
    t.append('end\n\nend LeanVM.Guest.CoreMode.FnReg\n')
    files[os.path.join(OUT, 'FnData.lean')] = ''.join(t)
    # the families
    m = 'LeanVM.Guest.CoreMode.Gen.FnFams'
    t = [header(m, 'Each function\'s own residual families.')]
    t += ['public import %s\n' % mod(f, 'Fam') for f, got in fns.items() if 'Fam' in got]
    t.append('public import LeanVM.Guest.CoreMode.CoreRes\n\nnamespace LeanVM.Guest.CoreMode.FnReg\n\n'
             'open LeanVM.Guest LeanVM.Guest.Core\n\n@[expose] public section\n\n')
    t += reg('Fam')
    t.append('end\n\nend LeanVM.Guest.CoreMode.FnReg\n')
    files[os.path.join(OUT, 'FnFams.lean')] = ''.join(t)
    # their soundness
    m = 'LeanVM.Guest.CoreMode.Gen.FnSound'
    t = [header(m, 'Each function\'s own routing facts and families, sound.')]
    t += ['public import %s\n' % mod(f, 'Sound') for f, got in fns.items() if 'Sound' in got]
    t.append('public import LeanVM.Guest.CoreMode.Gen.FnData\npublic import LeanVM.Guest.CoreMode.Gen.FnFams\n'
             'public import LeanVM.Guest.EndExecCoreFn\n\nnamespace LeanVM.Guest.CoreMode.FnReg\n\n'
             'open LeanVM.Guest LeanVM.Guest.Core\n\npublic section\n\n')
    for k, (part, _, pred, what) in KINDS.items():
        if pred is None:
            continue
        terms = ['Own.%s.%s_ok' % (f, k) for f, got in fns.items() if k in got.get(part, ())]
        # the registry `a ++ b ++ … ++ []`, left-nested
        proof = 'all_nil'
        if terms:
            proof = terms[0]
            for x in terms[1:]:
                proof = '(all_append %s\n    %s)' % (proof, x)
            proof = 'all_append %s all_nil' % proof
        t.append('/-- **%s**: each holds (`%s`). -/\ntheorem %s_ok : ∀ c ∈ %s, %s c :=\n  %s\n\n' % (
            what[0].upper() + what[1:].split(' (`')[0], pred, k, k, pred, proof))
    t.append('end\n\nend LeanVM.Guest.CoreMode.FnReg\n')
    files[os.path.join(OUT, 'FnSound.lean')] = ''.join(t)
    return files


def main(argv):
    own_files()
    files = render()
    check = '--check' in argv
    bad = genfiles.sync(files, [p for p in files if os.path.exists(p)], check)
    genfiles.fail_if_stale(bad, check)
    print('fnreg: %d functions\' modules, %s' % (len(scan()), 'unchanged' if not bad else ('stale' if check else
                                                                                           'written')))


if __name__ == '__main__':
    main(sys.argv[1:])
