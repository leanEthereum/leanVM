# Regression: match_range inside an `if` inside a `range` loop, writing a result
# declared in the (outer) loop scope and read after the branch. The `match_range`
# expansion must reuse the outer cell, not shadow it — otherwise the read after the
# branch sees uninitialized memory. `i` is a runtime loop variable, so neither the
# `if` nor the `match_range` folds at compile time. The accumulator is threaded
# through an explicit buffer (loop-carried mutables are unsupported).
def sq(n: Const):
    return n * n

def main():
    acc_buf = Array(4)
    acc_buf[0] = 0
    for i in range(1, 4):
        idx = i - 1
        contrib: Imm
        if i != 0:
            contrib = match_range(i, range(1, 4), lambda k: sq(k))
        else:
            contrib = 0
        acc_buf[idx + 1] = acc_buf[idx] + contrib
    acc = acc_buf[3]
    assert acc == 14  # sq(1) + sq(2) + sq(3) = 1 + 4 + 9
    return
