"""The core route's checks of each function on it (`route.py`): `Gen/<pack>/Core.lean`, its core data
(`CoreMode.CFun`: its frame walk, alignment context, heap certificate, core function, advice entry, powers and
promised cells) and the kernel's checks tying them to its mode certificate (`CoreMode.CoreOk`), hence its frame
interface (`Mode.FnSpecC`); `Gen/<pack>/Route.lean`, its core data the deployed guest's (`CoreMode.CfOk`). A heap
check `callc.py` windowed (`GenW/<fn>/`) is taken from its windows; a body longer than `SPLIT` statements has its
longest passes checked as declarations of their own (the kernel's memory goes by declaration). A pack with many checks
of long functions (`SPLIT_N`) has its core data in `Gen/<pack>/Defs.lean` and its independent checks in windows
(`CoreW<i>`, `RouteW<i>`), which build side by side; its `Core` and `Route` assemble them.
Usage: python3 -I scripts/core-mode/core.py [--check]  (with `CORE_MODE_CACHE` as for `heap.py`)"""
import os, re, sys, glob, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.append(os.path.join(HERE, '..'))
import genfiles  # noqa: E402
import route, heap  # noqa: E402
import callc  # noqa: E402

GUEST = route.GUEST
GEN = os.path.join(GUEST, 'CoreMode', 'Gen')
HEADER = genfiles.header('core-mode/core.py')


def index(pattern, files):
    """Each match's first group to the module (path under `LeanVM/`) whose text has it."""
    out = {}
    for f in files:
        mod = 'LeanVM.' + os.path.relpath(f, os.path.dirname(GUEST))[:-5].replace(os.sep, '.')
        for m in re.finditer(pattern, open(f, encoding='utf-8').read(), re.M):
            out[m.group(1)] = mod
    return out


def quote(mod):
    """A module name with `«»` around a pack or function component that needs it."""
    return '.'.join(('«%s»' % p) if (p[0].isdigit() or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', p) or
                                     re.fullmatch(r'P\d+', p)) else p for p in mod.split('.'))


def frame_term(mod):
    """The frame walk's acceptance from its module: one check, or a long function's windows chained."""
    if '.FrameL' in mod:
        return '⟨by decide +kernel, by decide +kernel, frameAcc⟩'
    return 'CoreMode.frameAcc_of (by decide +kernel) frameOk'


def pair_mod(g, n):
    """The module of function `n`'s pairing in pack `g`: the pack's, or a long function's own (windows)."""
    if os.path.exists(os.path.join(GEN, g, n, 'Ok.lean')):
        return 'LeanVM.Guest.CoreMode.Gen.%s.%s.Ok' % (g, n)
    return 'LeanVM.Guest.CoreMode.Gen.%s.Pair' % g


# a body of more statements (nested ones included) than `SPLIT` has its longest passes over the body checked apart
# (`verify_tables`' and `verify_sig_lean_sphincs`': a module's memory is its heaviest declaration's)
# (`shapeOk_of`, `honB_of`): the kernel's memory goes by declaration, not by module
SPLIT = 5000
# a heap certificate of more residual lists than `RES_SPLIT` has each list's families checked apart
RES_SPLIT = 8
# a heap certificate with one list of more residuals than `RES_B` has its families checked in slices (`CoreMode.sliceAll`)
# of weight at most `RES_B`: the kernel's memory grows over one evaluation, with the residuals' weight; a residual a range check or a top-level selector bounds (`cheap_res`) is two lookups in tries the slice builds once
# (`CoreMode.resFamT`), of weight `1 / RES_CHEAP`
RES_B, RES_CHEAP = 2, 32
# a body of more statements than `HON_SPLIT` has its honest valuation's parts checked apart (`honB_of`): in one
# evaluation its route check is the heaviest declaration of its module
HON_SPLIT = 2000
# a body with a frame run of more values than `FA_RUN` has its frame run cells at returns checked `FA_B` values at a
# time (`CoreMode.faRetOk_of_kchunks`): one evaluation over a long run is the heaviest declaration of its module
FA_RUN = 64
FA_B = 32


def nstmts(body):
    """The statements of a core body, nested ones included."""
    t = 0
    for s in body:
        t += 1
        if s[0] == 'ite':
            t += nstmts(s[2]) + nstmts(s[3])
        elif s[0] == 'match':
            t += sum(nstmts(a) for a in s[2])
    return t


def long_body(k):
    return nstmts(heap.CORE[k][1]) > SPLIT


def max_run(ss):
    """The longest frame run of a body's statements, nested ones included."""
    m = 0
    for s in ss:
        if s[0] == 'a' and s[1][0] == 'frameAddr' and len(s[1]) > 2:
            m = max(m, len(s[1][2]))
        elif s[0] == 'ite':
            m = max(m, max_run(s[2]), max_run(s[3]))
        elif s[0] == 'match':
            m = max([m] + [max_run(a) for a in s[2]])
    return m


def fa_chunks(k):
    """The number of `FA_B`-value chunks `k`'s frame run cells at returns are checked in, or None (one evaluation)."""
    n = max_run(heap.CORE[k][1])
    return -(-n // FA_B) if n > FA_RUN else None


def faret(k):
    """`CoreOk.faret`'s parts (`fa_chunks`), if any, and its proof: one kernel evaluation of `faRetOkF`, the check in one
    pass, else the chunks'."""
    m = fa_chunks(k)
    if m is None:
        return '', f'CoreMode.faRetOk_of_F {DK}'
    code = 'code.chunks.flatten'
    out = ''.join(thm(k, f'faret{c}', f'CoreMode.faRetC cfun {code} {FA_B} {c} = true') for c in range(m))
    out += thm(k, 'faret_runs', f'CoreMode.runsLe ({FA_B} * {m}) (Bridge.stmtsOf cfun.fn.body) = true')
    tail = 'fun c hc ↦ by\n    interval_cases c\n    exacts [%s]' % ', '.join(f'faret{c}' for c in range(m))
    out += thm(k, 'faret', f'CoreMode.faRetOk cfun {code} = true',
               f'\n  CoreMode.faRetOk_of_kchunks {FA_B} {m} (by decide) faret_runs {tail}')
    return out, 'faret'


# each pack's `DataC` text, read once
_DATAC = {}


def datac_of(k, po):
    """The text of `k`'s namespace in its pack's `DataC`, or ''."""
    f = os.path.join(GEN, po[k][0], 'DataC.lean')
    if f not in _DATAC:
        # the lists `callc.py` writes `data% [...]` (`Guest/DataLit.lean`) read as the literals
        _DATAC[f] = open(f, encoding='utf-8').read().replace('data% ', '') if os.path.exists(f) else ''
    s = _DATAC[f]
    i = s.find('namespace LeanVM.Guest.Fn.«%s»\n' % k)
    if i < 0:
        return ''
    j = s.find('\nend LeanVM.Guest.Fn.«%s»' % k, i)
    return s[i:j if j > 0 else len(s)]


def res_chunks(k, po):
    """The residual lists of `k`'s heap certificate (`hcert.res`'s `res0 ++ res1 ++ ...` in its pack's `DataC`), or
    none."""
    m = re.search(r'\n  res := \(([^)]*)\)\n', datac_of(k, po))
    if not m:
        return []
    return [x.strip() for x in m.group(1).split('++')]


def res_items(k, po, name=None):
    """The residuals of `k`'s heap certificate when they are one list literal (`hcert.res := [...]`), or of its residual
    list `name` (`def name`, a chunk of `res`), as texts, else none."""
    s = datac_of(k, po)
    head = f'\ndef {name} : List CoreMode.CRes :=\n  ' if name else '\n  res := '
    i = s.find(head + '[')
    if i < 0:
        return []
    out, depth, cur = [], 0, ''
    for ch in s[i + len(head):]:
        if ch in ')]⟩':
            depth -= 1
            if depth == 0:
                break
        if depth == 1 and ch == ',':
            out.append(' '.join(cur.split()))
            cur = ''
            continue
        if depth >= 1:
            cur += ch
        if ch in '([⟨':
            depth += 1
    if cur.strip():
        out.append(' '.join(cur.split()))
    return out


def cheap_res(k, r):
    """A residual `e(x) < n` that `CoreMode.resFamT` decides by lookups: `x` range checked below `N ≤ n` (`Res.rcBound`)
    or a top-level selector of at most `n` arms (`Res.topSels`)."""
    m = re.fullmatch(r'\.lt \(\.val (\d+)\) \(\.num (\d+)\)', r)
    if not m:
        return False
    import callcres
    x, n = int(m.group(1)), int(m.group(2))
    body = heap.CORE[k][1]
    if not (n < 2 ** 62 and x + 1 < 2 ** 20):
        return False
    N = callcres.rc_bound(callcres.top_atoms(body), x)
    return (N is not None and N <= n) or any(y == x and a <= n for y, a in callc.top_sels(body))


def parse_res(t):
    """A residual's Lean text (`emitc.lres`) as the mirrors' tuple."""
    toks = re.findall(r'\.\w+|\d+|[()\[\]⟨⟩,]', t)
    pos = [0]

    def peek():
        return toks[pos[0]]

    def take(x=None):
        tok = toks[pos[0]]
        assert x is None or tok == x, (t, tok, x)
        pos[0] += 1
        return tok

    def seq(item, close):
        out = []
        while peek() != close:
            out.append(item())
            if peek() == ',':
                take(',')
        take(close)
        return out

    def num():
        return int(take())

    def cell():
        take('⟨'); take('[')
        bs = seq(lambda: (take('('), num(), take(','), num(), take(')'))[1::2], ']')
        take(',')
        off = num()
        take('⟩')
        return tuple(tuple(b) for b in bs), off

    def idx():
        take('(')
        kind = take()[1:]
        v = cell() if kind == 'mono' else num()
        take(')')
        return kind, v

    def run():
        take('⟨')
        c = cell(); take(',')
        s = num(); take(',')
        lo = idx(); take(',')
        hi = idx()
        take('⟩')
        return c, s, lo, hi

    def cond():
        kind = take()[1:]
        args = []
        while peek().isdigit():
            args.append(num())
        return (kind, *args)

    def res():
        kind = take()[1:]
        if kind == 'under':
            take('[')
            cs = seq(cond, ']')
            take('(')
            r = res()
            take(')')
            return 'under', cs, r
        if kind == 'lt':
            return 'lt', idx(), idx()
        if kind == 'sub':
            return 'sub', cell(), run()
        if kind == 'subP':
            c = cell()
            take('[')
            return 'subP', c, seq(cell, ']')
        return 'subR', run(), run()
    r = res()
    assert pos[0] == len(toks), t
    return r


def res_hint(k, t):
    """The disjunct of `resFamG` the mirrors find to hold of the residual text `t` (`CoreMode.resFamHint`): `1` `resFam`
    over the indexed atoms (`CoreMode.resFamX`), `2` `resQ`, `3` `rcPts`, `4` `rcTab`, `5` the function's own family,
    `6` a ghost family; `0`, `resFamG`'s order, for one `cheapT` takes or none the mirrors see."""
    import callcres
    import fnrules
    if cheap_res(k, t):
        return 0
    r = parse_res(t)
    if all(v < callcres.I.GB for v in callcres.vals(r)):
        if res_q(k, r):
            return 2
        fam = callcres.res_fam(k, r, {'preR': [], 'preP': []})
        # the mirror's `resFam` takes a function's own exponent bounds (`exp_bound`), which are its own family's
        if fam and not any(fnrules.first('exp_bound', k, v) is not None for v in callcres.vals(r)):
            return 1
        if callcres.rc_pts(k, r):
            return 3
        if callcres.rc_tab(k, r):
            return 4
        if fnrules.some('fam', k, r):
            return 5
        if fam:
            return 1
    return 6 if (r[0] == 'sub' and callcres.st_sub(k, r[1]) == r) or fnrules.some('ghost', k, r) else 0


def expq_b(k, x):
    """`CoreMode.expQB`: the mirror's `expq_bound` without a function's own bounds (`exp_bound`, its own family's), None
    where one answers first."""
    import callcres
    import fnrules
    b = callcres.expq0(k, x)
    if b is None and fnrules.first('exp_bound', k, x) is not None:
        return None
    return b if b is not None else callcres.expq_bound(k, x)


def res_q(k, r):
    """`CoreMode.resQ`: an exponent fact's bound (`expQB`) or a dimension fact (`dimLt`), under branch conditions."""
    import callcres
    if r[0] == 'under':
        return res_q(k, r[2])
    if r[0] != 'lt':
        return False
    a, b = r[1], r[2]
    one = lambda i: i[0] == 'mono' and len(i[1][0]) == 1 and i[1][0][0][1] == 1
    if a[0] == 'val' and b[0] == 'num':
        B = expq_b(k, a[1])
        return b[1] < callcres.CAPE and B is not None and B <= b[1]
    if one(a) and b[0] == 'num':
        B = expq_b(k, a[1][0][0][0])
        return b[1] < callcres.CAPE and B is not None and B + a[1][1] <= b[1]
    if a[0] == 'num' and one(b):
        B = expq_b(k, b[1][0][0][0])
        return a[1] < b[1][1] and B is not None and B + b[1][1] < callcres.CAPE
    if a[0] == 'val' and one(b):
        return callcres.dim_ok(k, a[1], 0, b[1][0][0][0], b[1][1])
    if one(a) and one(b):
        return callcres.dim_ok(k, a[1][0][0][0], a[1][1], b[1][0][0][0], b[1][1])
    return False


def hints_text(hs):
    """A list of hints (`0` past its last nonzero one) as a Lean list, or as its runs (`CoreMode.hintRuns`) when that is
    shorter."""
    hs = list(hs)
    while hs and not hs[-1]:
        hs.pop()
    runs = []
    for h in hs:
        if runs and runs[-1][0] == h:
            runs[-1][1] += 1
        else:
            runs.append([h, 1])
    flat = f'[{", ".join(map(str, hs))}]'
    rl = f'(CoreMode.hintRuns [{", ".join(f"({h}, {n})" for h, n in runs)}])'
    return rl if len(rl) < len(flat) else flat


def res_cuts(k, items):
    """The slices' ends: each of weight at most `RES_B`, a cheap residual `1 / RES_CHEAP` (`cheap_res`), any other `1`."""
    cuts, acc = [], 0
    for j, r in enumerate(items):
        w = 1 if cheap_res(k, r) else RES_CHEAP
        if acc and acc + w > RES_B * RES_CHEAP:
            cuts.append(j)
            acc = 0
        acc += w
    return cuts + [len(items)]


def res_count(k, po):
    """The number of residuals of `k`'s heap certificate when they are one list literal (`hcert.res := [...]`), else
    0."""
    s = datac_of(k, po)
    i = s.find('\n  res := [')
    if i < 0:
        return 0
    depth, commas, empty = 0, 0, True
    for ch in s[i + len('\n  res := '):]:
        if depth == 1 and ch == ',':
            commas += 1
        if ch in ')]⟩':
            depth -= 1
            if depth == 0:
                break
        elif depth >= 1 and not ch.isspace():
            empty = False
        if ch in '([⟨':
            depth += 1
    return 0 if empty else commas + 1


DK = '(by decide +kernel)'
LEN = '(by rw [List.length_flatten]; decide +kernel)'
K = '⟨envC, funC, code.chunks.flatten⟩'


def thm(k, name, stmt, prf=DK):
    """A theorem of function `k`'s, `Fn.«k».name`: its statement and proof see `k`'s namespace."""
    return f'theorem Fn.«{k}».{name} : {stmt} := {prf}\n'


def shape(k):
    """`CoreOk.shape`: one kernel evaluation, or a long body's passes apart (`shapeOk_of`)."""
    if not long_body(k):
        return thm(k, 'core_shape', 'CoreMode.shapeOk cfun code.chunks.flatten = true')
    return (thm(k, 'core_body', 'CoreMode.bodyCore cfun.fn.body = true') +
            thm(k, 'core_tgt', 'CoreMode.tgtOk cfun code.chunks.flatten = true') +
            thm(k, 'core_rest', 'CoreMode.shapeRest cfun = true') +
            thm(k, 'core_shape', 'CoreMode.shapeOk cfun code.chunks.flatten = true',
                'CoreMode.shapeOk_of core_body core_tgt core_rest'))


def common(k):
    """The fields every route's check shares: the advice's hints, the code fetched, its operands, the powers (by key: its
    index in the program only in the glue, `GlueA`, `GlueC`)."""
    return (f'hints := Mode.hintsEq_of_fn (j := Fn.«{k}».idx) {DK} {DK} {DK} rfl, '
            f'fetch := Exec.guest_fetches Fn.«{k}».code_mem, '
            f'small := Mode.smallOps_of (CoreMode.offSmall_of_mem (f := code) Fn.«{k}».code_mem), '
            f'pows := Exec.PowTree.ok_of_okW Fn.«{k}».pows_ok, fpows := Exec.PowTree.ok_of_okW Fn.«{k}».fpows_ok')


_SIGS = {}


def sig_split(k):
    """A long body with calls, no heap contract: its signature check in parts (`CoreMode.ownOk_of`), its promised
    runs one by one; the number of runs, else None."""
    if not long_body(k):
        return None
    if 'S' not in _SIGS:
        _SIGS['S'] = route.sigs()
    G = _SIGS['S'].get(k)
    return None if G is None else len(G['postR'])


def sig_check(k, split):
    """`core_sig`: one kernel evaluation, or a long body's parts (`sig_split`, a body with calls)."""
    a = 'funC.sig cfun cfun.fn.params.length (CoreMode.retN cfun.fn.body)'
    n = sig_split(k) if split else None
    if n is None:
        return thm(k, 'core_sig', f'CoreMode.ownOk {a} (Mode.jtRng envC) = true')
    out = (thm(k, 'core_hc', 'cfun.hc = false') +
           thm(k, 'core_sigP', f'CoreMode.sigOkPre {a} (Mode.jtRng envC) = true') +
           thm(k, 'core_sigC', f'CoreMode.sigOkPost {a} = true') +
           thm(k, 'core_sigG', 'CoreMode.sigOkGh cfun cfun.fn.params.length = true'))
    for i in range(n):
        out += thm(k, f'core_sigR{i}', f'CoreMode.chunkAll (CoreMode.postRP {a}) funC.sig.postR {i} = true')
    tail = ('fun i hi ↦ absurd hi (Nat.not_lt_zero _)' if n == 0 else
            'fun i hi ↦ by\n    interval_cases i\n    exacts [%s]' % ', '.join(f'core_sigR{i}' for i in range(n)))
    out += (thm(k, 'core_sigR', f'CoreMode.sigOkPostR {a} = true', f'\n  CoreMode.all_of_chunks {n} {DK} {tail}') +
            thm(k, 'core_sig', f'CoreMode.ownOk {a} (Mode.jtRng envC) = true',
                'CoreMode.ownOk_of core_hc core_sigP core_sigC core_sigR core_sigG'))
    return out


def checks(k, j, frame, heap, split=False):
    """The kernel's checks of function `k` on the core route (`CoreMode.CoreOk`), each heavy one its own declaration
    (its own heartbeats), hence its frame interface."""
    fa, fap = faret(k)
    return (sig_check(k, split) + fa +
            thm(k, 'core_retv', '(cfun.hc || CoreMode.retVOk cfun funC.sig) = true') + shape(k) +
            thm(k, 'core_calls', 'code.chunks.flatten.all (CoreMode.jumpCallOk cfun) = true') +
            thm(k, 'core_jtd', 'CoreMode.jtdOk cfun envC code.chunks.flatten = true') +
            thm(k, 'core_nzrc', 'CoreMode.nzrOk cfun funC.res code.chunks.flatten = true') +
            thm(k, 'fnSpecC', f'Mode.FnSpecC {K} cfun',
                f'Mode.fnSpecC_of\n  {{ heap := {heap}, pair := pair_ok, frame := {frame}, sig := core_sig, retv := core_retv, '
                f'shape := core_shape, calls := core_calls, jtd := core_jtd, fsig := rfl, fsigs := rfl, fmain := {DK}, '
                f'fhalt := {DK}, xhalt := {DK}, fentry := rfl, flen := {DK}, xentry := {DK}, dhints := rfl, {common(k)}, '
                f'faret := {fap}, nzrc := core_nzrc }}'))


def dsp_arg(k):
    """`CFun.dsp`: callc's `dsp` for a body with a dispatch, else none."""
    return 'dsp' if any(s[0] == 'dispatch' for s in heap.CORE[k][1]) else '[]'


def cfun_def(k, j, rest):
    return f'noncomputable def Fn.«{k}».cfun : CoreMode.CFun := ⟨frameFun, alignCtx, hcert, core, Fn.«{k}».advice, Fn.«{k}».pows, {rest}⟩\n'


def cfun_c(k, j, frame):
    """A body with calls: its core data, its heap check (`heapOkC` at its callees' heap signatures `csigs`, in windows
    past `heapwin.BUDGET`, `heap_proof`), the kernel's checks."""
    return (cfun_def(k, j, f'[], csigs, {dsp_arg(k)}, hcFlag, hcCallees, {callc.gl_lean(k)}'),
            thm(k, 'heap_okC', 'CoreMode.heapOkC cfun.pows cfun.sigOf core hcert = true', heap_proof(k)) +
            thm(k, 'core_callsB', 'CoreMode.callsB cfun = true') +
            checks(k, j, frame, '.c heap_okC rfl core_callsB rfl rfl', True))


def _win_mod(sub, k, *arm):
    """The module `CoreMode/<sub>/<k>[/<arm>]/Ok.lean` of a heap check in windows, if there is one."""
    if os.path.exists(os.path.join(GUEST, 'CoreMode', sub, k, *arm, 'Ok.lean')):
        return '.'.join(['LeanVM.Guest.CoreMode', sub, quote(k), *arm, 'Ok'])
    return None


def heap_win(k):
    """The module of `k`'s heap check in windows (`callc.windows`), if it has one."""
    return _win_mod('GenW', k)


def heap_winL(k):
    """The module of loop helper `k`'s heap check in windows (`loopcc.windows`), if it has one."""
    return _win_mod('GenWL', k)


def heap_proof(k):
    """`heapOkC`'s proof: one kernel evaluation, or its windows' (`GenW/<fn>/Ok.lean`); a split at a selector
    (`callc.split_of`), its shared checks and each arm's, one kernel evaluation each (`heapOkC_split`)."""
    if heap_win(k):
        return 'heap_okW'
    sp = callc.split_of(k)
    if sp:
        arms = 'CoreMode.selArmsOk_nil'
        for r in reversed(range(sp[1])):
            prf = f'Fn.«{k}».Arm{r}.heap_okW' if heap_win_arm(k, r) else DK
            arms = f'(CoreMode.selArmsOk_cons {prf}\n    {arms})'
        return f'CoreMode.heapOkC_split {DK}\n    {arms}'
    return DK


def heap_win_arm(k, r):
    """The module of arm `r`'s heap check in windows, of a split certificate (`callc.windows`), if it has one."""
    return _win_mod('GenW', k, 'A%d' % r)


def heap_win_arms(k):
    """The modules of a split certificate's arms in windows."""
    sp = callc.split_of(k)
    return [m for m in (heap_win_arm(k, r) for r in range(sp[1] if sp else 0)) if m]


def loop_tail(k, frame):
    return (f'pair := pair_ok, frame := {frame}, sig := loop_sig, shape := loop_shape, sigE := rfl, fsig := rfl, fentry := rfl, '
            f'flen := {DK}, xentry := {DK}, xlen := {DK}, dhints := rfl, {common(k)}, hc := rfl, hcs := rfl')


def cfun_lc(k, j, frame):
    """A loop helper with calls: its core data, the kernel's checks (`CoreMode.LoopOkC`: `heapOkC`'s loop rules at its
    callees' heap signatures `csigs`, its signature, code and shape)."""
    if k in LONG:
        # its core data apart (`Gen/<pack>/Cfun.lean`), its passes in windows
        return ('', thm(k, 'heap_okC', 'CoreMode.heapOkC cfun.pows cfun.sigOf core hcert = true',
                        'heap_okW' if heap_winL(k) else DK) +
                thm(k, 'loop_sig', 'CoreMode.sigOkLP funC.sig hcert.sig core.params.length (CoreMode.tailPass core.body) '
                    'cfun.gl = true') +
                thm(k, 'loop_code', 'CoreMode.loopCodeC cfun code.chunks.flatten = true') + LONG[k][3] + loop_long(k, j, frame))
    return (cfun_def(k, j, f'[], csigs, [], false, [], {callc.gl_lean(k)}'),
            thm(k, 'heap_okC', 'CoreMode.heapOkC cfun.pows cfun.sigOf core hcert = true',
                'heap_okW' if heap_winL(k) else DK) +
            thm(k, 'loop_sig', 'CoreMode.sigOkLP funC.sig hcert.sig core.params.length (CoreMode.tailPass core.body) '
                'cfun.gl = true') +
            thm(k, 'loop_code', 'CoreMode.loopCodeC cfun code.chunks.flatten = true') +
            thm(k, 'loop_shape', 'CoreMode.loopShapeOkC cfun = true') +
            (thm(k, 'fnSpecC', f'Mode.FnSpecC {K} cfun',
                 f'CoreMode.fnSpecC_of_loopC\n  {{ heap := heap_okC, body := {DK}, tgt := {DK}, jtd := {DK}, calls := {DK}, top := {DK}, '
                 f'rdFree := {DK}, cptr := {DK}, ders := rfl, gw := rfl, nofa := {DK}, code := loop_code, fsigs := rfl, '
                 f'gtail := {DK}, nzrc := {DK}, '
                 f'{loop_tail(k, frame)} }}')))


# a long loop helper's passes over its body and code in windows (`CoreMode/LoopWin.lean`, `RouteWin.lean`): nested
# statements per body window, instructions per code window
import windows  # noqa: E402
WIN_STMTS, WIN_CODE = windows.CORE_STMTS, windows.CORE_CODE
# a function's own code window size (`windows.py`)
WIN_CODES = windows.own('CORE_WIN')
# set by `main`: the long loop helpers' modules, each function's mode pack, the module of function `j`'s code
LONG, PACK_OF = {}, {}
codes_mod = None


def pre_stmts(ss):
    """`Bridge.stmtsOf`'s order: each statement, then those nested in it."""
    for s in ss:
        yield s
        if s[0] == 'ite':
            yield from pre_stmts(s[2]); yield from pre_stmts(s[3])
        elif s[0] == 'match':
            for a in s[2]:
                yield from pre_stmts(a)


def mlens(ss):
    """`CoreMode.matchLens`."""
    return [(s[1], len(s[2])) for s in pre_stmts(ss) if s[0] == 'match']


def body_cuts(body, end):
    """Cuts at top-level statements before `end`, each window at most `WIN_STMTS` nested statements."""
    cuts, acc = [], 0
    for i in range(end):
        n = nstmts([body[i]])
        if acc and acc + n > WIN_STMTS:
            cuts.append(i)
            acc = 0
        acc += n
    return cuts


def code_cuts(code, win=WIN_CODE):
    """Cuts of the code every `win` instructions, none right after a `DEREF` (a table read's jump is next)."""
    cuts, b = [], win
    while b < len(code):
        while b < len(code) and code[b - 1][0] == '.deref':
            b += 1
        if b < len(code):
            cuts.append(b)
        b += win
    return cuts


def lst(xs):
    return '[' + ', '.join(xs) + ']'


# a chain's last cut, the end it names: an equation of numbers, the kernel's
FIN = '(by show _ = _; decide +kernel)'


def chain(items, final):
    """`⟨a ≤ b, w, ⟨…⟩⟩` over windows `[(b, proof)]`, ending in `final`."""
    out = final
    for prf in reversed(items):
        out = f'⟨by decide, {prf}, {out}⟩'
    return out


def align_ctx(k):
    """`k`'s alignment context as the `bridge` step wrote it: `(module, name)`, the one with its cells packed ahead
    (`alignCtxP`) for a function aligned over code slices, else `alignCtx`, in its own windows' module or its pack's."""
    own = os.path.join(GUEST, 'Bridge', 'AlignCtx', k, 'Ctx.lean')
    if os.path.exists(own):
        packed = 'alignCtxP' in open(own, encoding='utf-8').read()
        return f'LeanVM.Guest.Bridge.AlignCtx.«{k}».Ctx', 'alignCtxP' if packed else 'alignCtx'
    pack = heap.pack_of()[k][0]
    if not os.path.exists(os.path.join(GUEST, 'Bridge', 'Align', f'{pack}.lean')):
        raise SystemExit(f'core: no alignment context for {k}')
    return f'LeanVM.Guest.Bridge.Align.«{pack}»', 'alignCtx'


def long_loop(k, j, hp, frame_mod, gl):
    """A long loop helper's own modules (`Gen/<hp>/`): its core data (`Cfun`), its body's windows (`LW<i>`), its code's
    (`CW<i>`), its core data checks' (`RW<i>`, `SW<i>`): `({path: text}, Core imports, Route imports)`."""
    import align as AL
    params, body = heap.CORE[k]
    code = AL.functions()[k]['code']
    n = len(body)
    cs = body_cuts(body, n - 2)
    lb = [0] + cs + [n - 2]
    ml_w = [mlens(body[lb[i]:lb[i + 1]]) for i in range(len(lb) - 1)]
    ml = [m for w in ml_w for m in w]
    ccs = code_cuts(code, WIN_CODES.get(k, WIN_CODE)) + [len(code)]
    cb = [0] + ccs
    base = f'LeanVM.Guest.CoreMode.Gen.«{hp}»'
    files = {}
    hdr = lambda m, w: HEADER(mod=f'{base}.{m}', what=w)
    ns = lambda body_: (f'\nset_option Elab.async false\nset_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\n'
                        f'@[expose] public section\n\n{body_}\nend\n\nend LeanVM.Guest\n')
    mlt = lst(f'({x}, {y})' for x, y in ml)
    ctx_mod, ctx = align_ctx(k)
    files['Cfun'] = (hdr('Cfun', f'The core data of `{k}`, apart (its passes are checked in windows).') +
                     ''.join(f'public import {m}\n' for m in sorted({
                         'LeanVM.Guest.CoreMode.RouteWin', quote(frame_mod), ctx_mod,
                         f'{base}.DataLC', 'LeanVM.Guest.Pack.«%s».%s' % heap.pack_of()[k], f'LeanVM.Guest.CoreMode.GlueC.«{hp}»',
                         f'LeanVM.Guest.CoreMode.Pows.«{hp}»',
                         'Statement.Data.AdviceHints'})) +
                     ns(f'noncomputable def Fn.«{k}».cfun : CoreMode.CFun := ⟨frameFun, {ctx}, hcert, core, '
                        f'Fn.«{k}».advice, Fn.«{k}».pows, [], csigs, [], false, [], {gl}⟩\n\n'
                        f'/-- Its `match`es\' selectors and lengths. -/\ndef Fn.«{k}».mlL : List (ℕ × ℕ) :=\n  {mlt}\n'))
    imp = f'public import {base}.Cfun\n'
    cimps, rimps = [f'{base}.Cfun'], [f'{base}.Cfun']
    lws, rws, sws = [], [], []
    for i in range(len(lb) - 1):
        a, b = lb[i], lb[i + 1]
        files[f'LW{i}'] = (hdr(f'LW{i}', f'Window {i} of `{k}`\'s body: statements {a} to {b - 1}.') + imp +
                           ns(f'theorem Fn.«{k}».lw{i} : CoreMode.winL cfun (CoreMode.slice cfun.fn.body {a} {b}) '
                              f'{lst(f"({x}, {y})" for x, y in ml_w[i])} = true := by\n  decide +kernel\n'))
        cimps.append(f'{base}.LW{i}')
        lws.append(f'Fn.«{k}».lw{i}')
    rb = lb[:-1] + [n]
    sb = lb[:-1] + [n - 1]
    for i in range(len(rb) - 1):
        a, b = rb[i], rb[i + 1]
        files[f'RW{i}'] = (hdr(f'RW{i}', f'Window {i} of `{k}`\'s cells: statements {a} to {b - 1}.') + imp +
                           ns(f'theorem Fn.«{k}».rw{i} : CoreMode.cellsB Fn.«{k}».idx (CoreMode.slice cfun.fn.body {a} {b}) = true := by\n'
                              f'  decide +kernel\n'))
        rimps.append(f'{base}.RW{i}')
        rws.append(f'Fn.«{k}».rw{i}')
        a, b = sb[i], sb[i + 1]
        files[f'SW{i}'] = (hdr(f'SW{i}', f'Window {i} of `{k}`\'s selectors: statements {a} to {b - 1}.') + imp +
                           ns(f'theorem Fn.«{k}».selw{i} : (CoreMode.noRetTop (CoreMode.slice cfun.fn.body {a} {b}) && '
                              f'CoreMode.selGo Fn.«{k}».idx cfun.fn.params cfun.fn.body (CoreMode.seenF [] (cfun.fn.body.take {a})) '
                              f'(CoreMode.slice cfun.fn.body {a} {b})) = true := by\n  decide +kernel\n'))
        rimps.append(f'{base}.SW{i}')
        sws.append(f'Fn.«{k}».selw{i}')
    cws = []
    # several code windows: each over the slice of the chunks it covers, with the alignment context's tries stated
    # (`CLit`: `pair.py`'s `ALit`, the chunks' lengths), by `CoreMode.cw_of_slice` (`CoreMode/LoopWinS.lean`)
    from pair import alit_mod, cut_of
    amod = alit_mod(k) if len(cb) > 2 and ctx == 'alignCtxP' else None
    if amod:
        clens = AL.functions()[k]['clens']
        files['CLit'] = (hdr('CLit', f'`{k}`\'s code windows\' data: its chunks\' lengths and its core data with the '
                             'alignment context\'s tries stated once.') +
                         ''.join(f'public import {m}\n' for m in sorted({
                             amod, f'{base}.Cfun', 'LeanVM.Guest.CoreMode.LoopWinS', 'LeanVM.Guest.KernelLit'})) +
                         ns(f'kernel_lit Fn.«{k}».clens : List ℕ := Fn.«{k}».code.chunks.map List.length\n\n'
                            f'/-- `cfun`, its alignment context\'s tries stated (`alignL`). -/\n'
                            f'noncomputable def Fn.«{k}».cfunL : CoreMode.CFun := {{ Fn.«{k}».cfun with X := Fn.«{k}».alignL }}\n\n'
                            f'theorem Fn.«{k}».cfun_lit : Fn.«{k}».cfun = Fn.«{k}».cfunL := by\n'
                            f'  rw [Fn.«{k}».cfunL, ← Fn.«{k}».alignL_eq]; rfl\n'))
    for i in range(len(cb) - 1):
        a, b = cb[i], cb[i + 1]
        stmt = (f'theorem Fn.«{k}».cw{i} : (CoreMode.tgtGo cfun mlL {a} (CoreMode.slice code.chunks.flatten {a} {b}) && '
                f'CoreMode.jtdGo cfun envC mlL [] (CoreMode.slice code.chunks.flatten {a} {b})) = true :=')
        if amod:
            prf = (f'\n  CoreMode.cw_of_slice (ca := {cut_of(clens, a)}) (cb := {cut_of(clens, b)})\n'
                   f'    (by rw [Fn.«{k}».clens_eq]; decide +kernel) (by rw [Fn.«{k}».cfun_lit]; decide +kernel)\n')
        else:
            prf = ' by\n  decide +kernel\n'
        files[f'CW{i}'] = (hdr(f'CW{i}', f'Window {i} of `{k}`\'s code: offsets {a} to {b - 1}.') +
                           (f'public import {base}.CLit\n' if amod else imp) + ns(stmt + prf))
        cimps.append(f'{base}.CW{i}')
        cws.append(f'Fn.«{k}».cw{i}')
    pairs = lambda m: lst(f'({x}, {y})' for x, y in m)
    lcs = lst(f'({lb[i + 1]}, {pairs(ml_w[i])})' for i in range(len(lb) - 1))
    wins = f'CoreMode.LoopWins {K} cfun mlL {lcs} {lst(str(c) for c in ccs)}'
    thms = (thm(k, 'loop_rest', 'CoreMode.loopShapeRest cfun = true') +
            thm(k, 'loop_tailL', 'CoreMode.tailL cfun = true') +
            thm(k, 'loop_wins', wins,
                f'⟨{DK}, {chain(lws, FIN)}, loop_tailL, {chain(cws, FIN)}, loop_rest, {DK}⟩'))
    fn = f'Fn.«{k}».cfun.fn'
    hons = (f'theorem hon{j}_long : (CoreMode.bodyCore {fn}.body || CoreMode.loopBC {fn}) = true ∧ '
            f'(Bridge.stmtsOf {fn}.body).all (CoreMode.ptrCellB {j}) = true ∧ '
            f'(Bridge.stmtsOf {fn}.body).all (CoreMode.retCellB {j}) = true ∧ '
            f'(CoreMode.selGo {j} {fn}.params {fn}.body [] {fn}.body || CoreMode.loopBC {fn}) = true :=\n'
            f'  CoreMode.honB_long (j := {j}) (fn := {fn}) (cs := {lst(str(b) for b in rb[1:])}) '
            f'(ss := {lst(str(b) for b in sb[1:])})\n  {chain(rws, FIN)}\n  {chain(sws, FIN)} {DK}\n'
            f'theorem hon{j}_rest : CoreMode.honRest {j} {fn} = true := by decide +kernel\n')
    return files, cimps, rimps, thms, hons


def loop_long(k, j, frame):
    """A long loop helper's checks (`CoreMode.LoopOkC`), its passes by its windows (`loop_wins`), each other heavy one
    its own declaration (its own heartbeats); its frame walk's acceptance `frame` unless the walk is in windows, its
    pairing's by its context (`align_ctx`)."""
    code = 'code.chunks.flatten'
    parts = [('gtail', 'CoreMode.tailG cfun = true'),
             ('env', 'CoreMode.envOk cfun.frame = true'), ('arms', 'CoreMode.armsOk cfun.frame = true'),
             ('flen', f'cfun.frame.len = {code}.length'), ('xlen', f'cfun.X.len = {code}.length'),
             ('xentry', 'cfun.X.entry = funC.entry')]
    # a length of the code: of its chunks, summed, not of their concatenation
    out = ''.join(thm(k, 'loop_' + n, st, LEN if n.endswith('len') else DK) for n, st in parts)
    out += thm(k, 'loop_hints', f'∀ i < {code}.length, Mode.hintsAt Data.adviceHints (funC.entry + i) = '
               f'Mode.hintsAt cfun.frame.hints (funC.entry + i)',
               f'Mode.hintsEq_of_fn (K := {K}) (j := Fn.«{k}».idx) (d := Fn.«{k}».advice) {DK} {DK} {DK} rfl')
    out += thm(k, 'loop_fetch', f'Exec.Fetches guestProgram funC.entry {code}',
               f'Exec.guest_fetches Fn.«{k}».code_mem')
    out += thm(k, 'loop_small', f'∀ i (hi : i < {code}.length), CoreMode.SmallOps {code}[i]',
               f'Mode.smallOps_of (CoreMode.offSmall_of_mem (f := code) Fn.«{k}».code_mem)')
    f = '(CoreMode.loopFields_of_wins loop_wins)'
    return out + thm(k, 'fnSpecC', f'Mode.FnSpecC {K} cfun',
                     'CoreMode.fnSpecC_of_loopC\n  { heap := heap_okC, '
                     f'body := {f}.1, calls := {f}.2.1, top := {f}.2.2.1, rdFree := {f}.2.2.2.1, cptr := {f}.2.2.2.2.1, '
                     f'nofa := {f}.2.2.2.2.2.1, tgt := {f}.2.2.2.2.2.2.1, jtd := {f}.2.2.2.2.2.2.2.1, shape := {f}.2.2.2.2.2.2.2.2, '
                     'ders := rfl, gw := rfl, code := loop_code, fsigs := rfl, gtail := loop_gtail, nzrc := CoreMode.nzr_of_wins loop_wins, '
                     f'pair := {"pair_okP" if align_ctx(k)[1] == "alignCtxP" else "pair_ok"}, '
                     f'frame := {"⟨loop_env, loop_arms, frameAcc⟩" if frame.startswith("⟨") else frame}, sig := loop_sig, sigE := rfl, fsig := rfl, '
                     'fentry := rfl, flen := loop_flen, xentry := loop_xentry, xlen := loop_xlen, dhints := rfl, '
                     'hints := loop_hints, fetch := loop_fetch, small := loop_small, '
                     f'pows := Exec.PowTree.ok_of_okW Fn.«{k}».pows_ok, fpows := Exec.PowTree.ok_of_okW Fn.«{k}».fpows_ok, '
                     'hc := rfl, hcs := rfl }')


def cfun_m(k, j, frame):
    """A body without calls: its core data and promised cells, the kernel's checks."""
    return (cfun_def(k, j, 'hpost, [], [], false, [], []'),
            thm(k, 'core_post', 'CoreMode.postOk cfun.pows cfun.H cfun.post cfun.fn.body = true') +
            checks(k, j, frame, f'.m1 heap_ok core_post {DK} rfl rfl rfl'))


def core_file(ks, parts):
    """A pack's `Core.lean` body: the functions' core data, then their checks."""
    defs = ''.join(d for d, _ in parts)
    irr = ' '.join(f'Fn.«{k}».pairO Fn.«{k}».pairS' for k in ks)
    thms = ''.join(t for _, t in parts)
    defs = f'@[expose] public section\n\n{defs}\nend\n\n' if defs else ''
    return ('set_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\n' + defs + 'public section\n\n'
            f'attribute [local irreducible] {irr}\n\n' + thms + '\nend\n\nend LeanVM.Guest\n')


# a pack with at least `SPLIT_N` independent checks (`core_leaf`, `route_leaf`) of `big` functions has its independent
# checks in windows of at most about `WIN_W` (`weight`) each (`Gen/<pack>/CoreW<i>`, `RouteW<i>`), built side by side
# from its core data alone (`Gen/<pack>/Defs`), and only what assembles them in its `Core` and `Route`: one module's
# checks run one after another
SPLIT_N, WIN_W = 12, 160
# set by `main`: the functions whose checks this generator cuts into parts (`big`)
BIG = set()


def big(k, po):
    """A function some of whose checks this generator cuts into parts (a long body, a long frame run, many residual
    lists), each part about a pass over a long body; a long loop helper's passes are in its windows."""
    return k not in LONG and (nstmts(heap.CORE[k][1]) > HON_SPLIT or fa_chunks(k) is not None or
                              len(res_chunks(k, po)) > RES_SPLIT)


def weight(d):
    """A check's estimated cost: `20` for one of a `big` function's (`RES_B` for a slice of its residuals), else `1`."""
    if re.search(r'Fn\.«([^»]+)»', d).group(1) not in BIG:
        return 1
    return RES_B if d.startswith('theorem res') and 'CoreMode.sliceAll' in d else 20


def decls_of(text):
    """A text's declarations, each from its line starting `theorem ` to the next."""
    out = []
    for line in text.splitlines(keepends=True):
        if line.startswith('theorem ') or not out:
            out.append(line)
        else:
            out[-1] += line
    return out


def core_leaf(d):
    """A check of `Core` that cites no other: one kernel evaluation."""
    return d.count('\n') == 1 and d.endswith(f':= {DK}\n')


def route_leaf(d):
    """A check of `Route` that cites none of the pack's others (`res<i>_…`, `hon<i>_…`)."""
    return d.count('\n') == 1 and not re.search(r'\b(?:res|hon)\d+_\w', d.split(' : ', 1)[1])


def slices(name, part, stmt, p, l, n, b, unfold=None, cuts=None, wrap=None, hints=None):
    """Theorem `name : stmt`, `stmt` being `l.all p = true` (after unfolding `unfold`; `wrap` of it if given, `p` then
    the predicate `wrap` reads) for a list `l` of `n` entries, from its slices of `b` entries, or ending at `cuts`
    (`part<c>`, `CoreMode.sliceAll`), each its own kernel evaluation. With `hints = (q, sound, hs)`, a slice with a
    nonzero hint in `hs` (one an entry) is checked by `q` at its hints (`CoreMode.sliceAll_of_H`)."""
    cuts = [0] + (cuts or (list(range(b, n, b)) + [n]))

    def proof(c):
        hs = hints and hints[2][cuts[c]:cuts[c + 1]]
        if not hs or not any(hs):
            return 'by decide +kernel'
        return f'CoreMode.sliceAll_of_H {hints[1]} (q := {hints[0]}) (hs := {hints_text(hs)}) (by decide +kernel)'
    out = ''.join(f'theorem {part}{c} : CoreMode.sliceAll {p} {l} {cuts[c]} {cuts[c + 1]} = true := {proof(c)}\n'
                  for c in range(len(cuts) - 1))
    prf = 'CoreMode.all_drop_of_le (by decide +kernel)'
    for c in reversed(range(len(cuts) - 1)):
        prf = f'CoreMode.all_drop_of_slice (by decide) {part}{c}\n    ({prf})'
    pre = f'\n  rw [{unfold}]' if unfold else ''
    prf = f'CoreMode.all_of_drop_zero\n    ({prf})'
    if wrap:
        prf = f'{wrap} ({prf})'
    return out + f'theorem {name} : {stmt} = true := by{pre}\n  exact {prf}\n'


def windows_of(ds):
    """The leaves `ds` (texts) in windows: heaviest first, each to the lightest window, each window in their order."""
    w = [weight(d) for d in ds]
    n = -(-sum(w) // WIN_W)
    load, out = [0] * n, [[] for _ in range(n)]
    for i in sorted(range(len(ds)), key=lambda i: (-w[i], i)):
        b = min(range(n), key=lambda b: (load[b], b))
        load[b] += w[i]
        out[b].append(i)
    return [[ds[i] for i in sorted(b)] for b in out if b]


def split_pack(ds, leaf):
    """`ds` as `(windows, the rest)` when at least `SPLIT_N` of its leaves are a `big` function's, else None."""
    ls = [d for d in ds if leaf(d)]
    if sum(weight(d) > 1 for d in ls) < SPLIT_N:
        return None
    return windows_of(ls), [d for d in ds if not leaf(d)]


def hctab_file(packs):
    """`Gen/HcTab.lean`: the table of heap contracts (`CoreMode.hcTab`), each function's by its core data."""
    hc = sorted(heap.hc_fns())
    pk = {k: p for p, ks in packs.items() for k in ks}
    imps = ['LeanVM.Guest.CoreMode.Contracts'] + sorted({'LeanVM.Guest.CoreMode.Gen.«%s».Core' % pk[k] for k in hc})
    items = ',\n    '.join('CoreMode.hcEnt LeanVM.Guest.Fn.«%s».cfun' % k for k in hc)
    return (HEADER(mod='LeanVM.Guest.CoreMode.Gen.HcTab',
                          what='The functions whose contract is their own heap signature (`CFun.hc`), by their core data.') +
            ''.join('public import %s\n' % m for m in imps) +
            '\nnamespace LeanVM.Guest.CoreMode\n\n@[expose] public section\n\n'
            '/-- **The heap contracts\' table**: each function on a heap contract, its entry, signature, frame cells and '
            'counts. -/\nnoncomputable def hcTab : List HcEnt :=\n  [%s]\n\nend\n\nend LeanVM.Guest.CoreMode\n' % items)


def main(check=False):
    R = route.route_sub()
    po = heap.pack_of()
    # by the pack of its code, by key (the pack's `coreFns`);
    # a function's heap data and pairing are in its heap pack's `Gen/<pack>/` (`heap.pack_of`)
    packs = {}
    for k in sorted(R):
        packs.setdefault(R[k]['bpack'], []).append(k)
    frames = index(r'^(?:namespace LeanVM\.Guest\.Fn\.|noncomputable def Fn\.|frame_fn% )«([^»]+)»(?:$|\.frameFun\b| )', glob.glob(os.path.join(GUEST, 'CoreMode', 'Pack', '*', 'Frame*.lean')))
    # a long function's frame walk: its windows chained (`FrameL<k>`), not one of its windows (`FrameD<k>W<m>`)
    frames.update(index(r'^namespace LeanVM\.Guest\.Fn\.«([^»]+)»$', glob.glob(os.path.join(GUEST, 'CoreMode', 'Pack', '*', 'FrameL*.lean'))))
    codes = index(r'^kernel_rfl code(\d+) :', glob.glob(os.path.join(GUEST, 'Checked', 'Link*.lean')))
    tabs = index(r'^theorem tab(\d+) :', glob.glob(os.path.join(GUEST, 'Bridge', 'ProgAl', 'Tab*.lean')))
    files = {}
    S = route.sigs()
    # the long loop helpers: their core data apart, their passes in windows (`long_loop`)
    global LONG, PACK_OF, codes_mod
    codes_mod = lambda j: codes[str(j)]
    PACK_OF = {k: p for p, ks in packs.items() for k in ks}
    LONG = {}
    for k in sorted(R):
        if R[k].get('kind') == 'lc' and long_body(k):
            fr = frames[k].replace('.FrameL', '.FrameD')
            fl, cimps, rimps_, thms, hons_ = long_loop(k, R[k]['j'], po[k][0], fr, callc.gl_lean(k))
            for nm, text in fl.items():
                files[os.path.join(GEN, po[k][0], nm + '.lean')] = text
            LONG[k] = (cimps, rimps_, hons_, thms)
    BIG.update(k for k in R if big(k, po))
    for p, ks in sorted(packs.items()):
        imps = {'LeanVM.Guest.Mode.InvCert', 'LeanVM.Guest.CoreMode.Small',
                'LeanVM.Guest.SoundFacts', 'LeanVM.Guest.Exec'}
        # what only the assemblies read: the heap checks' and a long loop helper's windows
        pimps = set()
        body = []
        for k in ks:
            j = R[k]['j']
            imps.add(quote(frames[k])); imps.add('LeanVM.Guest.CoreMode.GlueC.«%s»' % po[k][0])
            imps.add(quote(pair_mod(po[k][0], k)))
            imps.add('LeanVM.Guest.CoreMode.Pows.«%s»' % po[k][0])
            if R[k].get('kind') != 'lc':
                imps.add('LeanVM.Guest.CoreMode.FaRetSplit')
            if os.path.exists(os.path.join(GEN, po[k][0], 'Ok.lean')):
                imps.add('LeanVM.Guest.CoreMode.Gen.«%s».Ok' % po[k][0])
            if R[k].get('kind') == 'lc':
                imps.add('LeanVM.Guest.CoreMode.Gen.«%s».DataLC' % po[k][0])
                imps.add('LeanVM.Guest.CoreMode.CoreLoopC')
                imps.add('LeanVM.Guest.Pack.«%s».%s' % po[k])
                if heap_winL(k):
                    pimps.add(heap_winL(k))
                if k in LONG:
                    imps.add(LONG[k][0][0])
                    pimps |= set(LONG[k][0][1:])
                body.append(cfun_lc(k, j, frame_term(frames[k])))
                continue
            if R[k].get('kind') == 'c':
                imps.add('LeanVM.Guest.CoreMode.Gen.«%s».DataC' % po[k][0])
                if sig_split(k) is not None:
                    imps.add('LeanVM.Guest.CoreMode.SigSplit')
                if heap_win(k):
                    pimps.add(heap_win(k))
                pimps |= set(heap_win_arms(k))
                imps.add('LeanVM.Guest.Pack.«%s».%s' % po[k])
                body.append(cfun_c(k, j, frame_term(frames[k])))
                continue
            imps.add('LeanVM.Guest.CoreMode.Gen.«%s».Ok' % p)
            body.append(cfun_m(k, j, frame_term(frames[k])))
        base = 'LeanVM.Guest.CoreMode.Gen.«%s»' % p
        mod = f'{base}.Core'
        data = 'import all LeanVM.Guest.Data.Functions\nimport all Statement.Data.AdviceHints\n\nset_option Elab.async false\n'
        pub = lambda ms: ''.join('public import %s\n' % m for m in sorted(ms))
        # past `SPLIT_W`, the core data apart (`Defs`) and the independent checks in windows beside each other
        cut = split_pack(decls_of(''.join(t for _, t in body)), core_leaf)
        if cut:
            cwins, rest = cut
            files[os.path.join(GEN, p, 'Defs.lean')] = (
                HEADER(mod=f'{base}.Defs', what='The core data of `%s` and %d more.' % (ks[0], len(ks) - 1)) + pub(imps) +
                data + '\nset_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\n@[expose] public section\n\n' +
                ''.join(d for d, _ in body) + '\nend\n\nend LeanVM.Guest\n')
            for w, ds in enumerate(cwins):
                ws = sorted({re.search(r'Fn\.«([^»]+)»', d).group(1) for d in ds})
                files[os.path.join(GEN, p, f'CoreW{w}.lean')] = (
                    HEADER(mod=f'{base}.CoreW{w}', what='Window %d of the core route\'s checks of `%s`\'s pack.' % (w, ks[0])) +
                    pub({f'{base}.Defs'}) + data + core_file(ws, [('', ''.join(ds))]))
            imps = {f'{base}.Defs'} | {f'{base}.CoreW{w}' for w in range(len(cwins))} | imps | pimps
            text = core_file(ks, [('', ''.join(rest))])
        else:
            imps |= pimps
            text = core_file(ks, body)
        files[os.path.join(GEN, p, 'Core.lean')] = (
            HEADER(mod=mod, what='The core route\'s checks of `%s` and %d more.' % (ks[0], len(ks) - 1)) +
            pub(imps) + data + text +
            f'\nnamespace LeanVM.Guest.ModePack.«{p}»\n\n@[expose] public section\n\n'
            f'/-- The core data of the pack\'s functions on the core route. -/\n'
            f'noncomputable def coreFns : List CoreMode.CFun :=\n  [%s]\n\nend\n\nend LeanVM.Guest.ModePack.«{p}»\n'
            % ', '.join('LeanVM.Guest.Fn.«%s».cfun' % k for k in ks))
        rimps = {'LeanVM.Guest.CoreMode.Route', mod}
        glues, rsplit = set(), set()
        oks, hons, decls = [], [], []
        for i, k in enumerate(ks):
            j = R[k]['j']
            # the tables at `j` through the glue's `tie` (`GlueC`): the route names `k` by its key, `j` only as `Fn.«k».idx`
            assert str(j) in codes and str(j) in tabs, k
            glues.add('LeanVM.Guest.CoreMode.GlueC.«%s»' % po[k][0])
            x = f'Fn.«{k}».idx'
            hb = '(by decide +kernel)'
            rch = res_chunks(k, po)
            rw = []
            if len(rch) > RES_SPLIT:
                fk = f'Fn.«{k}»'
                fam = f'(CoreMode.resFamG {fk}.cfun.fn {fk}.cfun.xc {fk}.cfun.H.sig.gw)'
                for c in rch:
                    hs = [res_hint(k, t) for t in res_items(k, po, c)]
                    prf = f'CoreMode.all_of_TH (hs := {hints_text(hs)})' if any(hs) else 'CoreMode.all_of_T'
                    hons.append(f'theorem res{i}_{c} : {fk}.{c}.all {fam} = true := {prf} (by decide +kernel)\n')
                rsplit.add('LeanVM.Guest.CoreMode.ResTab')
                hons.append(f'theorem res{i}_ok : CoreMode.resOk {fk}.cfun = true := by\n'
                            f'  rw [CoreMode.resOk, show {fk}.cfun.H.res = ({" ++ ".join(fk + "." + c for c in rch)}) from rfl]\n'
                            f'  simp only [List.all_append, {", ".join(f"res{i}_{c}" for c in rch)}, Bool.and_self]\n')
                rw.append(f'res{i}_ok')
                hb = f'(by rw [{", ".join(rw)}]; decide +kernel)'
            elif res_count(k, po) > RES_B:
                fk = f'Fn.«{k}»'
                items = res_items(k, po)
                assert len(items) == res_count(k, po), k
                tries = f'(CoreMode.rcT {fk}.cfun.fn.body) (CoreMode.constT {fk}.cfun.fn.body)'
                args = f'{fk}.cfun.fn {fk}.cfun.xc {fk}.cfun.H.sig.gw'
                fam = f'(CoreMode.resFamT {tries} {args})'
                hints = (f'(CoreMode.resFamTH {tries} {args})', 'CoreMode.resFamTH_sound', [res_hint(k, t) for t in items])
                hons.append(slices(f'res{i}_ok', f'res{i}_s', f'CoreMode.resOk {fk}.cfun', fam, f'{fk}.cfun.H.res',
                                   len(items), RES_B, 'CoreMode.resOk', res_cuts(k, items), 'CoreMode.all_of_T', hints))
                rsplit |= {'LeanVM.Guest.CoreMode.ResSplit', 'LeanVM.Guest.CoreMode.ResTab'}
                rw.append(f'res{i}_ok')
                hb = f'(by rw [{", ".join(rw)}]; decide +kernel)'
            if k in LONG:
                rimps |= set(LONG[k][1])
                hons.append(LONG[k][2])
                hb = (f'(by rw [CoreMode.honB_of hon{j}_long.1 hon{j}_long.2.1 hon{j}_long.2.2.1 hon{j}_long.2.2.2 '
                      f'hon{j}_rest, CoreMode.faOkB_of_noFA (CoreMode.loopFields_of_wins Fn.«{k}».loop_wins).2.2.2.2.2.1'
                      f'{"".join(", " + x for x in rw)}]; decide +kernel)')
            elif nstmts(heap.CORE[k][1]) > HON_SPLIT:
                fn = f'Fn.«{k}».cfun.fn'
                parts = [('body', f'(CoreMode.bodyCore {fn}.body || CoreMode.loopBC {fn})', 'its body\'s statements'),
                         ('ptr', f'(Bridge.stmtsOf {fn}.body).all (CoreMode.ptrCellB {x})', 'its pointers\' cells'),
                         ('ret', f'(Bridge.stmtsOf {fn}.body).all (CoreMode.retCellB {x})', 'its returned values\' cells'),
                         ('sel', f'(CoreMode.selGo {x} {fn}.params {fn}.body [] {fn}.body || CoreMode.loopBC {fn})', 'its `match`es\' selectors'),
                         ('rest', f'CoreMode.honRest {x} {fn}', 'the rest of its frame')]
                # a pass over the body's statements by the recursor (`StmtWalk.lean`), not over their list; its
                # pointers' cells looked up in a trie of its values' cells (`CoreMode.locT`)
                walk = 'rw [← CoreMode.stmtsAll_eq]; decide +kernel'
                prf = {'ptr': f'CoreMode.all_ptrCellB_of_T (by {walk})', 'ret': f'by {walk}'}
                for nm, st, doc in parts:
                    hons.append(f'theorem hon{i}_{nm} : {st} = true := {prf.get(nm, "by decide +kernel")}\n')
                rsplit.add('LeanVM.Guest.CoreMode.ResTab')
                hb = (f'(by rw [CoreMode.honB_of hon{i}_body hon{i}_ptr hon{i}_ret hon{i}_sel hon{i}_rest{"".join(", " + x for x in rw)}]; '
                      f'decide +kernel)')
            # each its own declaration, its own heartbeats
            hx = f'Fn.«{k}».alignCtxEq' if k in LONG and align_ctx(k)[1] == 'alignCtxP' else 'rfl'
            decls.append(f'theorem cfOk{i} : CoreMode.CfOk Fn.«{k}».cfun := CoreMode.cfOk_of_tie (by decide) Fn.«{k}».tie '
                         f'rfl rfl {hx} {hb}\n')
            oks.append(f'cfOk{i}')
        chain = 'List.forall_mem_nil _'
        for q in reversed(oks):
            chain = 'List.forall_mem_cons.2 ⟨%s, %s⟩' % (q, chain)
        ns = f'namespace LeanVM.Guest.ModePack.«{p}»\n\nopen LeanVM.Guest\n\npublic section\n\n'
        checks_ = ''.join(hons) + ''.join(decls)
        # a pack with its core data apart: its independent checks in windows past `SPLIT_W`, beside its `Core`'s
        cut = split_pack(decls_of(checks_), route_leaf) if os.path.join(GEN, p, 'Defs.lean') in files else None
        if cut:
            rwins, rest = cut
            for w, ds in enumerate(rwins):
                files[os.path.join(GEN, p, f'RouteW{w}.lean')] = (
                    HEADER(mod=f'{base}.RouteW{w}', what='Window %d of the core route\'s data of `%s`\'s pack.' % (w, ks[0])) +
                    pub({f'{base}.Defs', 'LeanVM.Guest.CoreMode.Route'} | glues | rsplit) + data + '\n' + ns + ''.join(ds) +
                    f'\nend\n\nend LeanVM.Guest.ModePack.«{p}»\n')
            rimps |= {f'{base}.RouteW{w}' for w in range(len(rwins))}
            checks_ = ''.join(rest)
        files[os.path.join(GEN, p, 'Route.lean')] = (
            HEADER(mod=f'{base}.Route', what='The core route\'s data of `%s` and %d more, the deployed guest\'s.' % (ks[0], len(ks) - 1)) +
            pub(rimps | glues | rsplit) + data + '\n' + ns + checks_ +
            f'\n/-- The pack\'s core data, each the deployed guest\'s. -/\n'
            f'theorem coreFns_ok : ∀ Cf ∈ coreFns, CoreMode.CfOk Cf :=\n  {chain}\n\nend\n\nend LeanVM.Guest.ModePack.«{p}»\n')
    files[os.path.join(GEN, 'HcTab.lean')] = hctab_file(packs)
    have = (glob.glob(os.path.join(GEN, '*', 'Core.lean')) + glob.glob(os.path.join(GEN, '*', 'Route.lean')) +
            [f for pat in ('Cfun', 'CLit', 'LW*', 'CW*', 'RW*', 'SW*', 'Defs', 'CoreW*', 'RouteW*') for f in glob.glob(os.path.join(GEN, '*', pat + '.lean'))])
    stale = genfiles.sync(files, have, check)
    lines = sum(text.count('\n') for text in files.values())
    print('core route: %d functions, %d packs, %d files, %d lines' % (len(R), len(packs), len(files), lines) +
          ((', stale: %d %s' % (len(stale), stale[:3])) if check else ''))
    genfiles.fail_if_stale(stale, check)


if __name__ == '__main__':
    main('--check' in sys.argv)
