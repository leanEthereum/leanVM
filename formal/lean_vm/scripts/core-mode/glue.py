"""The core route's ties to the global function index `j`, by pack: everything else of the core route
names a function by its stable key (`Fn.«k»`).

* `CoreMode/GlueA/<pack>.lean`: for each function whose core the pack holds, `Fn.«k».advice`, its entry, length and
  hints by pc (`Data.adviceFn{j}`, the statement's advice), `idx`, its index `j`, and with table jumps `jt0`, its first
  jump-table slot (the pairing's states name their tables from it).
* `CoreMode/GlueC/<pack>.lean`: for each function of the pack with a link (`Checked.code{j}`),
  `Fn.«k».code_mem`, that its code is the program's, and with its alignment tables' entries too
  (`Bridge.ProgAl.tab{j}`) `Fn.«k».tie`, the tables at its index its data (`CoreMode.cfOk_of_tie`, `Gen/*/Route`).

An added or removed function renumbers `j` and moves the jump table's slots here only.

usage (from formal/lean_vm): python3 -I scripts/core-mode/glue.py [--check]
"""
import sys, os, re, glob
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
import coredata  # noqa: E402
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import compiled as C  # noqa: E402

LV = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
GUEST = os.path.join(LV, 'LeanVM', 'Guest')
STMT = os.path.join(LV, '..', 'Statement', 'Data')


header = genfiles.header('core-mode/glue.py')


def main(check=False):
    name = dict(coredata.name_strings(os.path.join(GUEST, 'Data'))[0])
    t = ''.join(open(f, encoding='utf-8').read() for f in sorted(glob.glob(os.path.join(STMT, 'AdviceHints*.lean'))))
    adv = {m.group(1): int(m.group(2)) for m in
           re.finditer(r'/-- `([^`]*)`: its entry, length and hints by pc\. -/\ndef adviceFn(\d+)', t)}
    # each function's plumbing equation: `Checked`'s, or for a long one `Bridge.ProgAl`'s; its namespace and module
    link, plumb = {}, {}
    for f in glob.glob(os.path.join(GUEST, 'Checked', 'Link*.lean')):
        mod = 'LeanVM.Guest.Checked.' + os.path.basename(f)[:-5]
        t = open(f, encoding='utf-8').read()
        for j in re.findall(r'^kernel_rfl code(\d+) :', t, re.M):
            link[int(j)] = mod
        plumb.update((int(j), ('Checked', mod)) for j in re.findall(r'^kernel_rfl plumbEq(\d+) :', t, re.M))
    # each function's alignment tables' entries (`Bridge.ProgAl.tab{j}`): their module, the entries
    tab = {}
    for f in glob.glob(os.path.join(GUEST, 'Bridge', 'ProgAl', 'Tab*.lean')):
        mod = 'LeanVM.Guest.Bridge.ProgAl.' + os.path.basename(f)[:-5]
        for j, ex, en in re.findall(r'^theorem tab(\d+) : \(Bridge\.extraOf \1, Bridge\.entsOf \1, Bridge\.adviceOf \1\) = '
                                    r'\((\[[^\]]*\]), (\[.*\]), Data\.adviceFn\1\) :=$', open(f, encoding='utf-8').read(), re.M):
            tab[int(j)] = (mod, ex, en)
        for j in re.findall(r'^kernel_rfl plumbEq(\d+) :', open(f, encoding='utf-8').read(), re.M):
            plumb.setdefault(int(j), ('Bridge.ProgAl', mod))
    tied = lambda j: j in link and j in plumb and j in tab
    # each function in the pack holding its core (as `heap.pack_of`), its code in its bundle's pack
    home, bpack = {}, {}
    home = {k: bs[0][0] for k, bs in C.BD.core_blocks().items()}
    # each function's first jump-table slot: its plumbing's table jumps' least (`armsOf`'s)
    jt0 = {}
    for k, (pack, blk) in C.BD.bundle_blocks().items():
        bpack[k] = pack
        bs = [int(m.group(1)) for m in re.finditer(r'\(\d+, \d+, (\d+)\)', (re.findall(r'^  arms := (.*)$', blk, re.M) or [''])[0])]
        bs += [int(m.group(1)) for m in re.finditer(r'\(\d+, \d+, \[[^\]]*\], \d+, (\d+)\)',
                                                    (re.findall(r'^  chains := (.*)$', blk, re.M) or [''])[0])]
        if bs:
            jt0[k] = min(bs)
    packs = {}
    for k, pack in home.items():
        if name.get(k) in adv and k in bpack:
            packs.setdefault(pack, []).append(k)
    want = {}
    for pack, ks in sorted(packs.items()):
        ks = sorted(ks)
        a = [header(f'LeanVM.Guest.CoreMode.GlueA.«{pack}»', 'The advice of the pack\'s functions, by stable key.'),
             'public import Statement.Data.AdviceHints\n\nset_option linter.all false\nset_option linter.style.nameCheck false\n']
        c = [header(f'LeanVM.Guest.CoreMode.GlueC.«{pack}»', 'The code of the pack\'s functions, the program\'s.'),
             f'public import LeanVM.Guest.SoundFacts\npublic import LeanVM.Guest.CoreMode.GlueA.«{pack}»\n',
             ''.join(f'public import {m}\n' for m in sorted({link[adv[name[k]]] for k in ks if adv[name[k]] in link} |
                                                             {m for k in ks if tied(adv[name[k]])
                                                              for m in (tab[adv[name[k]]][0], plumb[adv[name[k]]][1])})),
             ''.join(f'public import LeanVM.Guest.Pack.«{q}».Bundle\n' for q in sorted({bpack[k] for k in ks})),
             '\nset_option linter.all false\nset_option linter.style.nameCheck false\n']
        a.append('\n/-! Each function\'s entry, length and hints by pc (`advice`) and its index in the program (`idx`). -/\n\n'
                 'namespace LeanVM.Guest\n\n@[expose] public section\n\n')
        c.append('\n/-! Each function\'s code is the program\'s (`code_mem`); the program\'s tables at its index are its data '
                 '(`tie`). -/\n\nnamespace LeanVM.Guest\n\npublic section\n\n')
        for k in ks:
            j = adv[name[k]]
            a.append(f'abbrev Fn.«{k}».advice := Data.adviceFn{j}\nabbrev Fn.«{k}».idx : ℕ := {j}\n')
            if k in jt0:
                a.append(f'abbrev Fn.«{k}».jt0 : ℕ := {jt0[k]}\n')
            if j in link:
                c.append(f'theorem Fn.«{k}».code_mem : code ∈ Data.functions := Checked.code{j} ▸ End.fnOf_mem (by decide)\n')
            if tied(j):
                c.append(f'theorem Fn.«{k}».tie : fnOf idx = code ∧ coreOf idx = core ∧ certOf idx = cert.withPows Data.powTree ∧ '
                         f'B2C.plumbOf idx = plumb ∧ (Bridge.extraOf idx, Bridge.entsOf idx, Bridge.adviceOf idx) = '
                         f'({tab[j][1]}, {tab[j][2]}, advice) :=\n  ⟨Checked.code{j}, Checked.core{j}, Checked.cert{j}, '
                         f'{plumb[j][0]}.plumbEq{j}, Bridge.ProgAl.tab{j}⟩\n')
        a.append('\nend\n\nend LeanVM.Guest\n')
        c.append('\nend\n\nend LeanVM.Guest\n')
        want[os.path.join(GUEST, 'CoreMode', 'GlueA', pack + '.lean')] = ''.join(a)
        want[os.path.join(GUEST, 'CoreMode', 'GlueC', pack + '.lean')] = ''.join(c)
    have = glob.glob(os.path.join(GUEST, 'CoreMode', 'GlueA', '*.lean')) + \
        glob.glob(os.path.join(GUEST, 'CoreMode', 'GlueC', '*.lean'))
    stale = genfiles.sync(want, have, check)
    genfiles.fail_if_stale(stale, check)
    print('glue: %d packs' % (len(want) // 2))


if __name__ == '__main__':
    main('--check' in sys.argv)
