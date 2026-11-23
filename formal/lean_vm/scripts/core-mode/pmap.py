"""`pmap(f, xs)`: `[f(x) for x in xs]` in forked worker processes, in order.

Each worker is a fork of the caller, so `f` may be any function (a closure over the caller's state) and reads the
caller's state as it was at the call; what `f` changes in a worker's state is lost, only its result comes back.
So `f` must be a function of its argument and of state the loop does not change: the per-function loops of the core
route's generators, whose iterations are independent. An exception in `f` is raised again in the caller.
`CORE_MODE_JOBS` caps the workers (default: half the CPUs); `CORE_MODE_JOBS=1` runs in this process.
"""
import os
import sys

_F = None


def jobs():
    n = os.environ.get('CORE_MODE_JOBS')
    return max(1, int(n)) if n else max(1, (os.cpu_count() or 2) // 2)


def _call(x):
    try:
        return True, _F(x)
    except BaseException as e:  # carried back to the caller
        return False, e


def pmap(f, xs):
    global _F
    xs = list(xs)
    n = min(jobs(), len(xs))
    if n <= 1 or sys.platform == 'win32':
        return [f(x) for x in xs]
    import multiprocessing as mp
    _F = f
    try:
        with mp.get_context('fork').Pool(n) as pool:
            out = pool.map(_call, xs, chunksize=1)
    finally:
        _F = None
    res = []
    for ok, v in out:
        if not ok:
            raise v
        res.append(v)
    return res
