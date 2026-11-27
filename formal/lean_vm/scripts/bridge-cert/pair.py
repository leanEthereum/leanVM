"""The computed hints' data check of every compiled function (`LeanVM/Guest/Bridge/PairChk/*.lean`).

Per module of alignment checks `align.py` writes (`Bridge/Align/*.lean`, `Bridge/AlignCtx/*/Ctx.lean`), each
function's `Bridge.pairChk` over its pack data and its hint-only cells, by `decide +kernel` (of its trie form
`Bridge.pairChkF` when the function looks up many cells, `by_trie`);
per link module of `Guest/Checked`, each function's check over `Bridge.ctxOf` with its advice's entry
(`Bridge.pairJ_of`, reusing the `Checked` and `ProgAl` link equations); and the assembly over every function
(`PairChk/All.lean`). `checks.py` writes them, a hash pack's and a link module's checks in one module with the other
checks' (`Bridge/Chk/`).
"""
import os, re, sys, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
import data
import progal

BR = os.path.join(data.ROOT, 'Bridge')
OUT = os.path.join(BR, 'PairChk')
HEAD = genfiles.header('bridge-cert/pair.py')


def check_module(ctx_mod):
    """The module of checks for the functions whose context `ctx_mod` holds."""
    if '.Align.«' in ctx_mod:
        return 'LeanVM.Guest.Bridge.PairChk.«' + ctx_mod.split('.Align.«')[1]
    k = ctx_mod.split('.AlignCtx.«')[1].split('»')[0]
    return f'LeanVM.Guest.Bridge.PairChk.«W_{k}»'


def pack_imports(ctx_mod):
    """The pack modules (bundles, core) the context module `ctx_mod` imports."""
    m = ctx_mod[:-len('.Ok')] + '.Ctx' if ctx_mod.endswith('».Ok') else ctx_mod
    path = os.path.join(data.LEAN_VM, *[x.strip('«»') for x in m.split('.')]) + '.lean'
    return sorted(re.findall(r'^public import (LeanVM\.Guest\.Pack\.\S+)$', open(path, encoding='utf-8').read(), re.M))


def hint_frame(h):
    """`Bridge.hintFrame`: the frame values a computed hint names."""
    st = lambda d: list(d[1]) if d[0] == 'stack' else []
    k = h[0]
    if k == 'bits':
        return [h[1]] + st(h[4])
    if k == 'bitsExp':
        return [h[1]] + st(h[3])
    if k == 'digitsExp':
        return [h[1]] + ([h[6]] if h[6] is not None else []) + st(h[7])
    if k == 'windowsExp':
        return [h[1]] + st(h[5])
    if k == 'limbs':
        return [h[1]] + list(h[2])
    if k == 'log2Ceil':
        return [h[4]] + st(h[1])
    if k == 'inverse':
        return [h[1], h[2]]
    return []


def hint_buf(h):
    """`Bridge.hintBuf`'s pointer: the buffer a computed hint writes, or a `log2Ceil` reads (`[]` if none)."""
    d = {'bits': 4, 'bitsExp': 3, 'digitsExp': 7, 'windowsExp': 5, 'log2Ceil': 1}.get(h[0])
    return [h[d][1]] if d is not None and h[d][0] == 'heap' else []


def hint_atoms(ss):
    """The hint atoms of a body, at any depth."""
    for s in ss:
        if s[0] == 'atom' and s[1] == 'hint':
            yield s[2]
        elif s[0] == 'ite':
            yield from hint_atoms(s[1])
            yield from hint_atoms(s[2])
        elif s[0] == 'match':
            for a in s[1]:
                yield from hint_atoms(a)


# below this many steps of walks the trie gains nothing measurable (`PairChk.P24`), so the check keeps the plain form
TRIE_MIN_WALK = 10 ** 4


def by_trie(k, cores, bund):
    """Whether `k`'s check reads its cells from a trie (`Bridge.pairChkF`): when its lookups' walks of the cell list
    (each to its value's index: the frame values and the buffer pointer, `cellOk`) outweigh packing the list, four
    times its length, and `TRIE_MIN_WALK`."""
    walk = sum(v for h in hint_atoms(data.body_of(cores[k])) if h[0] not in ('witness', 'alloc', 'allocDyn')
               for v in hint_frame(h) + hint_buf(h))
    return walk > max(4 * len(bund[k]['locs']), TRIE_MIN_WALK)


def gen():
    """The files, and the paths this check owns on disk."""
    ctxs, lk = progal.contexts(), progal.links()
    n = max(lk) + 1
    cores, bund = data.core_texts(), data.bundles()
    files = {}
    # the checks over the pack data
    by_mod = {}
    for j, (k, _, _) in sorted(lk.items()):
        by_mod.setdefault(ctxs[k][2], []).append(k)
    for cm, ks in sorted(by_mod.items()):
        mod = check_module(cm)
        # a function of many cell lookups runs the check over its cells packed in a trie (`Bridge.pairChk_of_fast`)
        body = data.fn_thms((k, 'pairOk', f'Bridge.pairChk {ctxs[k][0]} cert.locs fs core.body = true',
                             ':= Bridge.pairChk_of_fast (by decide +kernel)' if by_trie(k, cores, bund) else
                             'decide +kernel') for k in ks)
        files[os.path.join(OUT, mod.split('PairChk.')[1].strip('«»') + '.lean')] = (
            HEAD(mod=mod, what="The kernel's checks that compiled functions' computed hints pass the data check.")
            + 'public import LeanVM.Guest.Bridge.PairFast\n' + ''.join(f'public import {m}\n' for m in pack_imports(cm))
            + '\n' + body.rstrip('\n') + '\n')
    # the checks by index
    groups = {}
    for j in sorted(lk):
        groups.setdefault(lk[j][1], []).append(j)
    fss = set()
    for p in glob.glob(os.path.join(data.ROOT, 'Checked', 'Link*.lean')):
        fss |= set(int(x) for x in re.findall(r'^kernel_rfl fsEq(\d+) ', open(p, encoding='utf-8').read(), re.M))
    for lmod, js in sorted(groups.items()):
        imps = {'LeanVM.Guest.Bridge.PairLink', f'LeanVM.Guest.Checked.{lmod}', f'LeanVM.Guest.Bridge.ProgAl.Tab{lmod[len("Link"):]}'}  # the tables' entries, not the alignment checks
        imps |= {check_module(ctxs[lk[j][0]][2]) for j in js}
        body = []
        for j in js:
            k, _, _ = lk[j]
            fe = f'Checked.fsEq{j}'
            if j not in fss:
                body.append(f'kernel_rfl fsEq{j} : B2C.fsN {j} = Fn.«{k}».fs\n')
                fe = f'fsEq{j}'
            body.append(f'''kernel_rfl adv{j} : Data.adviceFns[{j}]? = some Data.adviceFn{j}
kernel_rfl len{j} : Data.adviceFn{j}.2.1 = Fn.«{k}».code.instructionCount
theorem pok{j} : Bridge.PairJ {j} := Bridge.pairJ_of Checked.code{j} Checked.core{j} Checked.cert{j} Bridge.ProgAl.tab{j} {fe} Fn.«{k}».pairOk adv{j} len{j}
''')
        files[os.path.join(OUT, f'{lmod}.lean')] = (
            HEAD(mod=f'LeanVM.Guest.Bridge.PairChk.{lmod}',
                        what=f"The functions of `Checked.{lmod}` pass the computed hints' data check over `Bridge.ctxOf`.")
            + ''.join(f'public import {m}\n' for m in sorted(imps)) + '''meta import LeanVM.Guest.KernelLit
import all LeanVM.Guest.Data.Functions
import all Statement.Data.AdviceHints

namespace LeanVM.Guest.Bridge.PairChk

open LeanVM.Guest

public section

''' + ''.join(body) + '''
end

end LeanVM.Guest.Bridge.PairChk
''')
    step = 256
    parts = [(lo, min(lo + step, n)) for lo in range(1, n, step)]
    thms = ''.join(f'''theorem pairJ_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.PairJ j := fun j h1 h2 ↦
  {progal.bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := fun j ↦ Bridge.PairJ j) {la} {lb} pok{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    top = progal.bisect([lo for lo, _ in parts] + [n], lambda a, la, lb: f'(pairJ_{a} j {la} {lb})')
    files[os.path.join(OUT, 'All.lean')] = (
        HEAD(mod='LeanVM.Guest.Bridge.PairChk.All',
                    what="Every compiled function's computed hints pass the data check.")
        + ''.join(f'public import LeanVM.Guest.Bridge.PairChk.{m}\n' for m in sorted(groups)) + f'''
namespace LeanVM.Guest.Bridge.PairChk

open LeanVM.Guest

public section

{thms}/-- **Every compiled function's computed hints pass the data check.** -/
theorem pairJ_all : ∀ j, 1 ≤ j → j < {n} → Bridge.PairJ j := fun j h1 h2 ↦
  {top}

end

end LeanVM.Guest.Bridge.PairChk
''')
    print(f'bridge-cert: the computed hints of {len(lk)} functions over {len(groups)} link modules')
    return data.quiet(files), set(glob.glob(os.path.join(OUT, '*.lean')))
