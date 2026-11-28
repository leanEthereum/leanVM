"""The allocation track's check of every compiled function (`LeanVM/Guest/Bridge/AllocChk/*.lean`).

Per module of alignment checks `align.py` writes, each function's `Bridge.allocFnChk` over its alignment context
(the context `align.py` names, written out), core function, code and advice, by `decide +kernel`
(`Fn.«k».allocFnOk`); per link module of `Guest/Checked`, each function's `Bridge.AllocFnJ` (`Bridge.allocFnJ_of`,
reusing the `Checked` and `ProgAl` link equations); and the assembly over every function (`AllocChk/All.lean`:
`allocFnJ_all`, and `allocFnChk_guest`, the check by name at `Bridge.alignA`); the same for the address hints' check
(`Bridge.addrFnChk`, `Fn.«k».addrFnOk`, `addrFnChk_guest`), the buffer hints' check (`Bridge.bufFnChk`,
`Fn.«k».bufFnOk`, `bufFnChk_guest`) and the frame hints' sizes check (`Bridge.frChk` at the callees `frchk.py`
lists, `Fn.«k».frFnOk`, `frFnChk_guest`). The checks are mirrored here (`chk`, `addr_chk`, `buf_chk`, its cells
left to the kernel, `frchk.fr_data`),
so that a function failing it fails here, naming why. Run after `progal.py`; `--check` writes nothing and fails
when a file is stale.

    python3 -I scripts/bridge-cert/alloc.py [--check]
"""
import os, re, sys, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import genfiles  # noqa: E402
import data
import progal
import align
import frchk

BR = os.path.join(data.ROOT, 'Bridge')
OUT = os.path.join(BR, 'AllocChk')
HEAD = genfiles.header('bridge-cert/alloc.py')
ALLOC = ('alloc', 'allocDyn', 'allocArm', 'allocFrames')


def cnt_alloc(ss):
    """`Bridge.cntL`: the allocation atoms of a block (`data.core_body`), nested ones included."""
    n = 0
    for s in ss:
        if s[0] == 'a' and s[1][0] == 'hint' and s[1][1][0] in ('alloc', 'allocDyn'):
            n += 1
        elif s[0] == 'ite':
            n += cnt_alloc(s[2]) + cnt_alloc(s[3])
        elif s[0] == 'match':
            n += sum(cnt_alloc(a) for a in s[2])
    return n


def matches(ss):
    """Every `match` of a block, nested ones included, as (selector, arm count)."""
    out = []
    for s in ss:
        if s[0] == 'ite':
            out += matches(s[2]) + matches(s[3])
        elif s[0] == 'match':
            out.append((s[1], len(s[2])))
            for a in s[2]:
                out += matches(a)
    return out


def no_ret(ss):
    """`Bridge.noRetB`."""
    for s in ss:
        if s[0] == 'ret':
            return False
        if s[0] == 'ite' and not (no_ret(s[2]) and no_ret(s[3])):
            return False
        if s[0] == 'match' and not all(no_ret(a) for a in s[2]):
            return False
    return True


def chk(F, body, name, A, pows, jt):
    """`Bridge.allocFnChk`, mirrored: the reason it fails, or `None`."""
    entry, code, stat = F['entry'], F['code'], F['stat']
    sites, arms = F['sites'], F['arms']

    def zero_at(o):
        return stat.get(o) == ('k', 0, 0)

    def self_at(o):
        s = stat.get(o)
        return s is not None and ((s[0] == 'fpg' and s[1] == 0) or (s[0] == 'k' and s[1] == 1 and s[2] == 0 and F['main']))

    def next_at(o):
        s = stat.get(o)
        return (s[0] == 'fpg' and s[1] != 0) if s is not None else o in F['nxt']

    def pc_at(o):
        s = stat.get(o)
        return pows.get(s[1]) if s is not None and s[0] == 'k' and s[2] == 0 else None

    def is_jump(c):
        return c[0] == '.jump'

    def next_jump(a):
        return a + next((i for i, c in enumerate(code[a:]) if is_jump(c)), len(code[a:]))
    ptr = lambda h: h[1] if h[0] in ALLOC else None
    is_frame = lambda h: ptr(h) is not None and ptr(h) in sites
    is_buf = lambda h: ptr(h) is not None and not is_frame(h)
    hs = [(max(pc - A['entry'], 0), h) for pc, l in A['hints'] for h in l if ptr(h) is not None]
    fr = [(a, h) for a, h in hs if is_frame(h)]
    bs = [(a, h) for a, h in hs if is_buf(h)]
    pend = lambda off: any(a < off <= next_jump(a) for a, _ in fr)
    for pc, l in A['hints']:
        p = pend(max(pc - entry, 0))
        for h in l:
            if p and (is_buf(h) or is_frame(h)):
                return f'hints out of order at pc {pc}'
            p = p or is_frame(h)
    for i, c in enumerate(code):
        if not is_jump(c) or not any(i < a for a, _ in bs):
            continue
        oc, od, of = c[1]
        if zero_at(oc) and of not in sites and not next_at(of):
            continue
        t = pc_at(od)
        if not (self_at(of) and of not in sites and not (od == 0 and of == 1) and od not in arms and t is not None
                and not any(i < a and entry + a < t for a, _ in bs)):
            return f'jump at offset {i} before a buffer'
    for a, h in fr:
        nj = next_jump(a)
        if h[0] not in ('alloc', 'allocArm', 'allocFrames') or nj >= len(code) or not is_jump(code[nj]):
            return f'frame hint at offset {a}'
        oc, od, q = code[nj][1]
        if q != ptr(h) or zero_at(oc) or self_at(q) or next_at(q) or (od == 0 and q == 1):
            return f'frame hint at offset {a}: its jump'
    for i, c in enumerate(code):
        if not is_jump(c):
            continue
        q = c[1][2]
        at = [r for r in fr if next_jump(r[0]) == i]
        if q in sites and not any(ptr(h) == q for _, h in at):
            return f'call site jump at offset {i} without its frame hint'
        if len(at) > 1:
            return f'two frame hints for the jump at offset {i}'
    if cnt_alloc(body) > len(bs):
        return 'fewer buffer hints than allocation atoms'
    if fr:
        for i, c in enumerate(code):
            if is_jump(c):
                t = pc_at(c[1][1])
                if t is not None and pend(max(t - entry, 0)):
                    return f'jump target of offset {i} pending'
        for x, n in matches(body):
            for od, (sel, base) in arms.items():
                if sel != x:
                    continue
                for k in range(n):
                    t = jt.get(base + k)
                    if t is not None and pend(max(t - entry, 0)):
                        return f'arm target {t} pending'
        if any(pend(max(s[3] - entry, 0)) for s in sites.values()):
            return 'a return pc pending'
    loop = len(body) >= 2 and body[-1] == ('ret', []) and body[-2][0] == 'callIf' and body[-2][2] == name
    if not loop and any(is_jump(c) and next_at(c[1][2]) for c in code):
        return 'a jump through a next frame outside a loop helper'
    if loop:
        args = body[-2][3]
        if not no_ret(body[:-2]) or any(list(s[0]) == list(args) and not s[1] for s in sites.values()):
            return "the loop helper's last call"
    return None


def addr_chk(F, name, body, A, fs):
    """`Bridge.addrFnChk`, mirrored: the reason it fails, or `None`."""
    loop = len(body) >= 2 and body[-1] == ('ret', []) and body[-2][0] == 'callIf' and body[-2][2] == name
    for pc, l in A['hints']:
        for h in l:
            if h[0] == 'frameAddress' and not (h[1] == fs and loop):
                return f'frame address at pc {pc}'
            if h[0] == 'cellAddress' and not (F['stat'].get(h[1]) == ('fpg', h[2], 0) and h[2] < fs and h[1] < fs):
                return f'cell address at pc {pc}'
    return None


def is_alloc_atom(s):
    return s[0] == 'a' and s[1][0] == 'hint' and s[1][1][0] in ('alloc', 'allocDyn')


def no_alloc(s):
    """`Bridge.Stmt.noAlloc`."""
    if s[0] == 'a':
        return not is_alloc_atom(s)
    if s[0] == 'ite':
        return all(no_alloc(t) for t in s[2] + s[3])
    if s[0] == 'match':
        return all(no_alloc(t) for a in s[2] for t in a)
    return True


def ret_free(s):
    """`Bridge.Stmt.retFree`."""
    if s[0] == 'ret':
        return False
    if s[0] == 'ite':
        return all(ret_free(t) for t in s[2] + s[3])
    if s[0] == 'match':
        return all(ret_free(t) for a in s[2] for t in a)
    return True


def buf_chk(F, body, A):
    """`Bridge.bufFnChk`, mirrored but for its cells: the reason it fails, or `None`."""
    top = [s[1][1] for s in body if is_alloc_atom(s)]
    for i, s in enumerate(body):
        if s[0] != 'a' and not (no_alloc(s) and (not any(is_alloc_atom(t) for t in body[i + 1:]) or ret_free(s))):
            return f'allocation shape at statement {i}'
    ptr = lambda h: h[1] if h[0] in ALLOC else None
    bs = [h for _, l in A['hints'] for h in l if ptr(h) is not None and ptr(h) not in F['sites']]
    if len(bs) != len(top):
        return f'{len(bs)} buffer hints for {len(top)} allocation atoms'
    for k, (a, h) in enumerate(zip(top, bs)):
        unal = h[0] == 'alloc' and h[3] == ('id', 'false')
        if not ((a[0] == 'alloc' and unal and h[2] == a[2]) or (a[0] == 'allocDyn' and h[0] == 'allocDyn')
                or (a[0] == 'allocDyn' and unal and h[2] < 2 ** 28)):
            return f'buffer hint {k}'
    return None


def check_module(ctx_mod):
    """The module of checks for the functions whose context `ctx_mod` holds."""
    if '.AlignCtx.«' in ctx_mod:
        k = ctx_mod.split('.AlignCtx.«')[1].split('»')[0]
        return f'LeanVM.Guest.Bridge.AllocChk.«W_{k}»'
    return ctx_mod.replace('.Align.', '.AllocChk.')


def imports_of(path):
    return re.findall(r'^public import (\S+)$', open(path, encoding='utf-8').read(), re.M)


def run(check):
    ctxs, lk = progal.contexts(), progal.links()
    n = max(lk) + 1
    fns, adv, cores = align.functions(), data.advice(), data.core_texts()
    pows = align.pow_table()
    jt = align.jump_table(pows)
    fss = {key: int(re.search(r'^def fs : ℕ := (\d+)$', blk, re.M).group(1)) for key, (_, blk) in data.bundle_blocks().items()}
    fails = []
    bund = data.bundles()
    cal = frchk.callee_table(lk, cores, fss, bund)
    frcs = {}
    for j, (k, _, _) in sorted(lk.items()):
        F = dict(fns[k], main=(j == 1))
        params, body, name = data.core_fn(cores[k])
        why = (chk(F, body, name, adv[F['entry']], pows, jt) or addr_chk(F, name, body, adv[F['entry']], fss[k])
               or buf_chk(F, body, adv[F['entry']]))
        frcs[j], bad = frchk.fr_data(F, adv[F['entry']], params, body, bund[k]['locs'], frchk.extra_of(ctxs[k][0]),
                                     fss[k], cal.get)
        if bad:
            why = why or f'frame hint sizes at {bad}'
        if why:
            fails.append(f'{k} ({why})')
    if fails:
        sys.exit('bridge-cert: failing the allocation track check: ' + ', '.join(fails))
    files = {}
    by_mod = {}
    for j, (k, _, _) in sorted(lk.items()):
        by_mod.setdefault(ctxs[k][2], []).append((j, k))
    for cm, jks in sorted(by_mod.items()):
        mod = check_module(cm)
        win = '.AlignCtx.«' in cm
        if win:
            # a long function: its context module (`Ctx`), without the alignment's checks
            cm = cm[:-len('.Ok')] + '.Ctx'
            imps = [cm]
        else:
            path = os.path.join(BR, 'Align', cm.split('.Align.')[1].strip('«»') + '.lean')
            imps = [m for m in imports_of(path) if m not in ('LeanVM.Guest.Bridge.AlignDefs', 'LeanVM.Guest.Bridge.ChkLit')]
        thms = []
        for j, k in jks:
            cells, ents, _ = ctxs[k]
            ctx = 'alignCtx' if win else (
                f'(Bridge.AlignCtx.ofData cert.locs {cells} code.entryPc {"true" if j == 1 else "false"} plumb '
                f'Data.powTree Data.jtTrie {ents} CoreMode.haltPc code.instructionCount)')
            thms.append((k, 'allocFnOk', f'Bridge.allocFnChk {ctx} core code.code Fn.«{k}».advice = true',
                         'decide +kernel'))
            thms.append((k, 'addrFnOk', f'Bridge.addrFnChk {ctx} fs core Fn.«{k}».advice = true', 'decide +kernel'))
            thms.append((k, 'bufFnOk', f'Bridge.bufFnChk {ctx} fs core Fn.«{k}».advice = true', 'decide +kernel'))
            thms.append((k, 'frFnOk', f'Bridge.frChk {ctx} fs {frcs[j]} core.params core.body Fn.«{k}».advice = true',
                         'decide +kernel'))
        files[os.path.join(OUT, mod.split('AllocChk.')[1].strip('«»') + '.lean')] = (
            HEAD(mod=mod, what="The kernel's checks that compiled functions pass the allocation track's check.")
            + 'public import LeanVM.Guest.Bridge.AddrChk\npublic import LeanVM.Guest.Bridge.FrChk\n'
            + ''.join(f'public import {m}\n' for m in sorted(set(imps)))
            + 'import all Statement.Data.AdviceHints\n\n' + data.fn_thms(thms))
    groups = {}
    for j in sorted(lk):
        groups.setdefault(lk[j][1], []).append(j)
    for lmod, js in sorted(groups.items()):
        imps = {'LeanVM.Guest.Bridge.AddrChk', 'LeanVM.Guest.Bridge.FrChk', f'LeanVM.Guest.Checked.{lmod}',
                f'LeanVM.Guest.Bridge.ProgAl.Tab{lmod[len("Link"):]}'}
        imps |= {check_module(ctxs[lk[j][0]][2]) for j in js}
        body = []
        for j in js:
            k, _, hp = lk[j]
            pe = f'Checked.plumbEq{j}' if hp else f'Bridge.ProgAl.plumbEq{j}'
            body.append(f'theorem aok{j} : Bridge.AllocFnJ {j} := Bridge.allocFnJ_of Checked.code{j} Checked.core{j} '
                        f'Checked.cert{j} {pe} Bridge.ProgAl.tab{j} rfl Fn.«{k}».allocFnOk\n')
            body.append(f'kernel_rfl fsEq{j} : B2C.fsN {j} = Fn.«{k}».fs\n')
            body.append(f'theorem dok{j} : Bridge.AddrFnJ {j} := Bridge.addrFnJ_of Checked.code{j} Checked.core{j} '
                        f'Checked.cert{j} {pe} Bridge.ProgAl.tab{j} rfl fsEq{j} Fn.«{k}».addrFnOk\n')
            body.append(f'theorem bok{j} : Bridge.BufFnJ {j} := Bridge.bufFnJ_of Checked.code{j} Checked.core{j} '
                        f'Checked.cert{j} {pe} Bridge.ProgAl.tab{j} rfl fsEq{j} Fn.«{k}».bufFnOk\n')
            body.append(f'theorem rok{j} : Bridge.FrFnJ {j} := Bridge.frFnJ_of Checked.code{j} Checked.core{j} '
                        f'Checked.cert{j} {pe} Bridge.ProgAl.tab{j} rfl fsEq{j} Fn.«{k}».frFnOk\n')
        files[os.path.join(OUT, f'{lmod}.lean')] = (
            HEAD(mod=f'LeanVM.Guest.Bridge.AllocChk.{lmod}',
                 what=f"The functions of `Checked.{lmod}` pass the allocation track's check over `Bridge.ctxOf`.")
            + ''.join(f'public import {m}\n' for m in sorted(imps)) + '''meta import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.Bridge.AllocChk

open LeanVM.Guest

public section

''' + ''.join(body) + '''
end

end LeanVM.Guest.Bridge.AllocChk
''')
    pred = 'fun j ↦ Bridge.AllocFnJ j'
    step = 256
    parts = [(lo, min(lo + step, n)) for lo in range(1, n, step)]
    thms = ''.join(f'''theorem allocFnJ_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.AllocFnJ j := fun j h1 h2 ↦
  {progal.bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := {pred}) {la} {lb} aok{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    top = progal.bisect([lo for lo, _ in parts] + [n], lambda a, la, lb: f'(allocFnJ_{a} j {la} {lb})')
    dpred = 'fun j ↦ Bridge.AddrFnJ j'
    dthms = ''.join(f'''theorem addrFnJ_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.AddrFnJ j := fun j h1 h2 ↦
  {progal.bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := {dpred}) {la} {lb} dok{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    dtop = progal.bisect([lo for lo, _ in parts] + [n], lambda a, la, lb: f'(addrFnJ_{a} j {la} {lb})')
    bpred = 'fun j ↦ Bridge.BufFnJ j'
    bthms = ''.join(f'''theorem bufFnJ_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.BufFnJ j := fun j h1 h2 ↦
  {progal.bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := {bpred}) {la} {lb} bok{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    btop = progal.bisect([lo for lo, _ in parts] + [n], lambda a, la, lb: f'(bufFnJ_{a} j {la} {lb})')
    rpred = 'fun j ↦ Bridge.FrFnJ j'
    rthms = ''.join(f'''theorem frFnJ_{m} : ∀ j, {lo} ≤ j → j < {hi} → Bridge.FrFnJ j := fun j h1 h2 ↦
  {progal.bisect(list(range(lo, hi + 1)), lambda a, la, lb: f"(at_of_bounds (P := {rpred}) {la} {lb} rok{lo + a})")}

''' for m, (lo, hi) in enumerate(parts))
    rtop = progal.bisect([lo for lo, _ in parts] + [n], lambda a, la, lb: f'(frFnJ_{a} j {la} {lb})')
    files[os.path.join(OUT, 'All.lean')] = (
        HEAD(mod='LeanVM.Guest.Bridge.AllocChk.All', what="Every compiled function passes the allocation track's check.")
        + ''.join(f'public import LeanVM.Guest.Bridge.AllocChk.{m}\n' for m in sorted(groups)) + f'''
namespace LeanVM.Guest.Bridge.AllocChk

open LeanVM.Guest

public section

{thms}/-- **Every compiled function passes the allocation track's check.** -/
theorem allocFnJ_all : ∀ j, 1 ≤ j → j < nFns → Bridge.AllocFnJ j := fun j h1 (h2 : j < {n}) ↦
  {top}

/-- **Every core function passes the allocation track's check at the deployed alignment.** -/
theorem allocFnChk_guest : ∀ f fn, Guest.coreProgram.find? f = some fn →
    Bridge.allocFnChk (Bridge.alignA f).X fn (Bridge.alignA f).code (Bridge.alignA f).d = true :=
  Bridge.allocFnChk_alignA allocFnJ_all

{dthms}/-- **Every compiled function passes the address hints' check.** -/
theorem addrFnJ_all : ∀ j, 1 ≤ j → j < nFns → Bridge.AddrFnJ j := fun j h1 (h2 : j < {n}) ↦
  {dtop}

/-- **Every core function passes the address hints' check at the deployed alignment.** -/
theorem addrFnChk_guest : ∀ f fn, Guest.coreProgram.find? f = some fn →
    Bridge.addrFnChk (Bridge.alignA f).X (B2C.fs f) fn (Bridge.alignA f).d = true :=
  Bridge.addrFnChk_alignA addrFnJ_all

{bthms}/-- **Every compiled function passes the buffer hints' check.** -/
theorem bufFnJ_all : ∀ j, 1 ≤ j → j < nFns → Bridge.BufFnJ j := fun j h1 (h2 : j < {n}) ↦
  {btop}

/-- **Every core function passes the buffer hints' check at the deployed alignment.** -/
theorem bufFnChk_guest : ∀ f fn, Guest.coreProgram.find? f = some fn →
    Bridge.bufFnChk (Bridge.alignA f).X (B2C.fs f) fn (Bridge.alignA f).d = true :=
  Bridge.bufFnChk_alignA bufFnJ_all

{rthms}/-- **Every compiled function passes the frame hints' sizes check.** -/
theorem frFnJ_all : ∀ j, 1 ≤ j → j < nFns → Bridge.FrFnJ j := fun j h1 (h2 : j < {n}) ↦
  {rtop}

/-- **Every core function passes the frame hints' sizes check at the deployed alignment.** -/
theorem frFnChk_guest : ∀ f fn, Guest.coreProgram.find? f = some fn →
    ∃ cs, Bridge.frChk (Bridge.alignA f).X (B2C.fs f) cs fn.params fn.body (Bridge.alignA f).d = true :=
  Bridge.frFnChk_alignA frFnJ_all

end

end LeanVM.Guest.Bridge.AllocChk
''')
    existing = set(glob.glob(os.path.join(OUT, '*.lean')))
    stale = genfiles.sync(files, existing, check)
    print(f'bridge-cert: the allocation track and address hints of {len(lk)} functions over {len(groups)} link modules')
    genfiles.fail_if_stale(stale, check, data.LEAN_VM)


if __name__ == '__main__':
    run('--check' in sys.argv[1:])
