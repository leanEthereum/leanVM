"""`open_stacked`'s rules: its arms, by stack log (`scripts/count`)."""
import re


def count_arms(g):
    """The opening arms `open_stacked__L{m}`, `m` from `0` (`gen.G.os_names`)."""
    ns = [n for n in g.by if re.fullmatch(r'open_stacked__L\d+', n)]
    out = ['open_stacked__L%d' % m for m in range(len(ns))]
    assert sorted(out) == sorted(ns), ns
    return out

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
