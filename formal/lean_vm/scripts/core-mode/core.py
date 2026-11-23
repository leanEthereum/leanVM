"""The core route's checks of each function on it (`route.py`): `Gen/<pack>/Core.lean`, its core data
(`CoreMode.CFun`: its frame walk, alignment context, heap certificate, core function, advice entry, powers and
promised cells) and the kernel's checks tying them to its mode certificate (`CoreMode.CoreOk`), hence its frame
interface (`Mode.FnSpecC`); `Gen/<pack>/Route.lean`, its core data the deployed guest's (`CoreMode.CfOk`). A heap
check `callc.py` windowed (`GenW/<fn>/`) is taken from its windows; a body longer than `SPLIT` statements has its
longest passes checked as declarations of their own (the kernel's memory goes by declaration).
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
    """`CoreOk.faret`'s parts (`fa_chunks`), if any, and its proof."""
    m = fa_chunks(k)
    if m is None:
        return '', DK
    code = 'code.chunks.flatten'
    out = ''.join(thm(k, f'faret{c}', f'CoreMode.faRetC cfun {code} {FA_B} {c} = true') for c in range(m))
    out += thm(k, 'faret_runs', f'CoreMode.runsLe ({FA_B} * {m}) (Bridge.stmtsOf cfun.fn.body) = true')
    tail = 'fun c hc ↦ by\n    interval_cases c\n    exacts [%s]' % ', '.join(f'faret{c}' for c in range(m))
    out += thm(k, 'faret', f'CoreMode.faRetOk cfun {code} = true',
               f'\n  CoreMode.faRetOk_of_kchunks {FA_B} {m} (by decide) faret_runs {tail}')
    return out, 'faret'


def res_chunks(k, po):
    """The residual lists of `k`'s heap certificate (`hcert.res`'s `res0 ++ res1 ++ ...` in its pack's `DataC`), or
    none."""
    f = os.path.join(GEN, po[k][0], 'DataC.lean')
    if not os.path.exists(f):
        return []
    s = open(f, encoding='utf-8').read()
    i = s.find('namespace LeanVM.Guest.Fn.«%s»\n' % k)
    if i < 0:
        return []
    j = s.find('\nend LeanVM.Guest.Fn.«%s»' % k, i)
    m = re.search(r'\n  res := \(([^)]*)\)\n', s[i:j if j > 0 else len(s)])
    if not m:
        return []
    return [x.strip() for x in m.group(1).split('++')]


DK = '(by decide +kernel)'
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
            checks(k, j, frame, f'.c heap_okC rfl {DK} rfl rfl', True))


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
    for i in range(len(cb) - 1):
        a, b = cb[i], cb[i + 1]
        files[f'CW{i}'] = (hdr(f'CW{i}', f'Window {i} of `{k}`\'s code: offsets {a} to {b - 1}.') + imp +
                           ns(f'theorem Fn.«{k}».cw{i} : (CoreMode.tgtGo cfun mlL {a} (CoreMode.slice code.chunks.flatten {a} {b}) && '
                              f'CoreMode.jtdGo cfun envC mlL [] (CoreMode.slice code.chunks.flatten {a} {b})) = true := by\n'
                              f'  decide +kernel\n'))
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
    out = ''.join(thm(k, 'loop_' + n, st) for n, st in parts)
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
    return ('set_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\n@[expose] public section\n\n' + defs + '\nend\n\npublic section\n\n'
            f'attribute [local irreducible] {irr}\n\n' + thms + '\nend\n\nend LeanVM.Guest\n')

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
    tabs = index(r'^kernel_rfl tab(\d+) :', glob.glob(os.path.join(GUEST, 'Bridge', 'ProgAl', 'Tab*.lean')))
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
    for p, ks in sorted(packs.items()):
        imps = {'LeanVM.Guest.Mode.InvCert', 'LeanVM.Guest.CoreMode.Small',
                'LeanVM.Guest.SoundFacts', 'LeanVM.Guest.Exec'}
        body = []
        for k in ks:
            j = R[k]['j']
            imps.add(quote(frames[k])); imps.add('LeanVM.Guest.CoreMode.GlueC.«%s»' % po[k][0])
            imps.add(quote(pair_mod(po[k][0], k)))
            imps.add('LeanVM.Guest.CoreMode.Pows.«%s»' % po[k][0])
            if R[k].get('kind') != 'lc' and fa_chunks(k) is not None:
                imps.add('LeanVM.Guest.CoreMode.FaRetSplit')
            if os.path.exists(os.path.join(GEN, po[k][0], 'Ok.lean')):
                imps.add('LeanVM.Guest.CoreMode.Gen.«%s».Ok' % po[k][0])
            if R[k].get('kind') == 'lc':
                imps.add('LeanVM.Guest.CoreMode.Gen.«%s».DataLC' % po[k][0])
                imps.add('LeanVM.Guest.CoreMode.CoreLoopC')
                imps.add('LeanVM.Guest.Pack.«%s».%s' % po[k])
                if heap_winL(k):
                    imps.add(heap_winL(k))
                if k in LONG:
                    imps |= set(LONG[k][0])
                body.append(cfun_lc(k, j, frame_term(frames[k])))
                continue
            if R[k].get('kind') == 'c':
                imps.add('LeanVM.Guest.CoreMode.Gen.«%s».DataC' % po[k][0])
                if sig_split(k) is not None:
                    imps.add('LeanVM.Guest.CoreMode.SigSplit')
                if heap_win(k):
                    imps.add(heap_win(k))
                imps |= set(heap_win_arms(k))
                imps.add('LeanVM.Guest.Pack.«%s».%s' % po[k])
                body.append(cfun_c(k, j, frame_term(frames[k])))
                continue
            imps.add('LeanVM.Guest.CoreMode.Gen.«%s».Ok' % p)
            body.append(cfun_m(k, j, frame_term(frames[k])))
        mod = 'LeanVM.Guest.CoreMode.Gen.«%s».Core' % p
        files[os.path.join(GEN, p, 'Core.lean')] = (
            HEADER(mod=mod, what='The core route\'s checks of `%s` and %d more.' % (ks[0], len(ks) - 1)) +
            ''.join('public import %s\n' % m for m in sorted(imps)) + 'import all Statement.Data.Bytecode\nimport all Statement.Data.AdviceHints\n\nset_option Elab.async false\n' + core_file(ks, body) +
            f'\nnamespace LeanVM.Guest.ModePack.«{p}»\n\n@[expose] public section\n\n'
            f'/-- The core data of the pack\'s functions on the core route. -/\n'
            f'noncomputable def coreFns : List CoreMode.CFun :=\n  [%s]\n\nend\n\nend LeanVM.Guest.ModePack.«{p}»\n'
            % ', '.join('LeanVM.Guest.Fn.«%s».cfun' % k for k in ks))
        rimps = {'LeanVM.Guest.CoreMode.Route', mod}
        oks, hons, decls = [], [], []
        for i, k in enumerate(ks):
            j = R[k]['j']
            # the tables at `j` through the glue's `tie` (`GlueC`): the route names `k` by its key, `j` only as `Fn.«k».idx`
            assert str(j) in codes and str(j) in tabs, k
            rimps.add('LeanVM.Guest.CoreMode.GlueC.«%s»' % po[k][0])
            x = f'Fn.«{k}».idx'
            hb = '(by decide +kernel)'
            rch = res_chunks(k, po)
            rw = []
            if len(rch) > RES_SPLIT:
                fk = f'Fn.«{k}»'
                fam = f'(CoreMode.resFamG {fk}.cfun.fn {fk}.cfun.xc {fk}.cfun.H.sig.gw)'
                for c in rch:
                    hons.append(f'theorem res{i}_{c} : {fk}.{c}.all {fam} = true := by decide +kernel\n')
                hons.append(f'theorem res{i}_ok : CoreMode.resOk {fk}.cfun = true := by\n'
                            f'  rw [CoreMode.resOk, show {fk}.cfun.H.res = ({" ++ ".join(fk + "." + c for c in rch)}) from rfl]\n'
                            f'  simp only [List.all_append, {", ".join(f"res{i}_{c}" for c in rch)}, Bool.and_self]\n')
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
                for nm, st, doc in parts:
                    hons.append(f'theorem hon{i}_{nm} : {st} = true := by decide +kernel\n')
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
        rmod = 'LeanVM.Guest.CoreMode.Gen.«%s».Route' % p
        files[os.path.join(GEN, p, 'Route.lean')] = (
            HEADER(mod=rmod, what='The core route\'s data of `%s` and %d more, the deployed guest\'s.' % (ks[0], len(ks) - 1)) +
            ''.join('public import %s\n' % m for m in sorted(rimps)) + 'import all Statement.Data.Bytecode\nimport all Statement.Data.AdviceHints\n\nset_option Elab.async false\n\n'
            f'namespace LeanVM.Guest.ModePack.«{p}»\n\nopen LeanVM.Guest\n\npublic section\n\n' + ''.join(hons) + ''.join(decls) +
            f'\n/-- The pack\'s core data, each the deployed guest\'s. -/\n'
            f'theorem coreFns_ok : ∀ Cf ∈ coreFns, CoreMode.CfOk Cf :=\n  {chain}\n\nend\n\nend LeanVM.Guest.ModePack.«{p}»\n')
    files[os.path.join(GEN, 'HcTab.lean')] = hctab_file(packs)
    have = (glob.glob(os.path.join(GEN, '*', 'Core.lean')) + glob.glob(os.path.join(GEN, '*', 'Route.lean')) +
            [f for pat in ('Cfun', 'LW*', 'CW*', 'RW*', 'SW*') for f in glob.glob(os.path.join(GEN, '*', pat + '.lean'))])
    stale = genfiles.sync(files, have, check)
    lines = sum(text.count('\n') for text in files.values())
    print('core route: %d functions, %d packs, %d files, %d lines' % (len(R), len(packs), len(files), lines) +
          ((', stale: %d %s' % (len(stale), stale[:3])) if check else ''))
    genfiles.fail_if_stale(stale, check)


if __name__ == '__main__':
    main('--check' in sys.argv)
