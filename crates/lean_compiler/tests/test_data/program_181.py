# Regression: a ragged const-array access that picks a valid deeper branch
# used to panic on a `depth()` assertion computed from element 0
MIXED = [1, [2]]


def main():
    assert MIXED[1][0] == 2
    return
