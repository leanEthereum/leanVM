@inline
def chk(a):
    assert a != GEN ** 3
    return a

@inline
def add(acc, k: Const):
    return acc * GEN ** (k + 1)

def main():
    q = 1
    xs = StackBuf(3)
    xs[0] = GEN ** 0
    xs[1] = GEN ** 1
    xs[2] = q[GEN]
    acc = GEN
    for p in unroll(0, 3):
        acc = match(log(chk(xs[p])), range(0, 4), lambda k: add(acc, k))
    q[1] = acc
    return
