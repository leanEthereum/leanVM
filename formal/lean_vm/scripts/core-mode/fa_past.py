"""The frame walk's cells past a frame run, written at every return (`CoreMode.faRetAt`'s past-the-run cells): for
`callc.py`, which runs without the walk's inputs loaded. Reads `{name: [[kp, base, length], ...]}` (each top-level
`frameAddr kp run`, its first value's frame cell and its length) on stdin, writes `{name: [[kp, i], ...]}`, the cells
`i` past each run (below `length + PAST`) written at every return. The walk is the core route's: its oracle and stores
the pairing's (`pair.pair`) at the def-use designation of the reads (`heap.reads_of`, the certificate's not being
known yet), its residual divisors its own (`frame_run.own_nz`), as `frame_gen.py` walks a routed function; no mode
walk."""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import frame as FR  # noqa: E402
import frame_run as FRR  # noqa: E402
import frame_data as FD  # noqa: E402

PAST = 160


def main():
    import memo
    memo.follow()
    req = json.load(sys.stdin)
    D = FD.load()
    import pair as PR
    import heap
    texts, bundles, advice = PR.data.core_texts(), PR.data.bundles(), PR.data.advice()
    fns = PR.AL.functions()
    pows = PR.AL.pow_table()
    jt = PR.AL.jump_table(pows)
    entry_by_name = {F['name']: F['entry'] for F in fns.values()}

    def walk(k):
        """`k`'s frame walk at its pairing's oracle and stores (`pair.collect`'s, at the def-use reads)."""
        F, B = fns[k], bundles[k]
        A = advice[F['entry']]
        body = PR.body_of(texts[k])
        callees = sorted({s[1] if s[0] == 'call' else s[2] for s in PR.AL.walk_stmts(body) if s[0] in ('call', 'callIf')})
        ents = {n: entry_by_name[n] for n in callees if n in entry_by_name}
        extra, _ = PR.AL.align(F, PR.AL.body_of(texts[k]), A, B['locs'], B['plumb'], pows, jt, ents)
        O, S, _ = PR.pair(F, body, A, B['locs'], extra, pows, jt, ents, heap.reads_of(*heap.CORE[k]), [])
        f = D['fns'][k]
        Fx, entry, ln, sig, tgt, nzr = FRR.inputs(D, k, FRR.own_nz(D, k, O, S))
        FR.Walk(Fx, entry, ln, sig, D['fsig'], f['hints'], nzr, tgt, set(O), D['halt'], S=set(S)).run(f['ops'])
    rets = []
    exit0 = FR.Walk.exit

    def exit(self, i, A, kind, succ, od, of):
        if kind[0] == 'ret':
            rets.append(set(A.w))
        return exit0(self, i, A, kind, succ, od, of)
    FR.Walk.exit = exit
    out = {}
    for k, fas in req.items():
        rets.clear()
        try:
            walk(k)
        except (FR.Fail, PR.Fail, PR.AL.Fail):
            out[k] = []
            continue
        W = set.intersection(*rets) if rets else set()
        out[k] = [[kp, i] for kp, base, ln in fas if ln for i in range(ln, ln + PAST) if base + i in W]
    json.dump(out, sys.stdout)


if __name__ == '__main__':
    main()
