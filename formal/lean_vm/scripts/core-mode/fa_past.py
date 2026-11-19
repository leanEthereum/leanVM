"""The frame walk's cells past a frame run, written at every return (`CoreMode.faRetAt`'s past-the-run cells): for
`callc.py`, which runs without the walk's inputs loaded. Reads `{name: [[kp, base, length], ...]}` (each top-level
`frameAddr kp run`, its first value's frame cell and its length) on stdin, writes `{name: [[kp, i], ...]}`, the cells
`i` past each run (below `length + PAST`) written at every return. `MODE_CERT_CACHE` (and `FRAME_CACHE`) as
`frame_run.py`'s."""
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
    D = FD.load(os.environ['MODE_CERT_CACHE'], os.environ.get('FRAME_CACHE'))
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
            FRR.run(D, k)
        except (FR.Fail, KeyError):
            out[k] = []
            continue
        W = set.intersection(*rets) if rets else set()
        out[k] = [[kp, i] for kp, base, ln in fas if ln for i in range(ln, ln + PAST) if base + i in W]
    json.dump(out, sys.stdout)


if __name__ == '__main__':
    main()
