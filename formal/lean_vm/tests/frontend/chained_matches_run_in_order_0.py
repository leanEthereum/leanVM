@inline
def add(acc, k: Const):
    return acc * GEN ** (k + 1)

def main():
    xs = StackBuf(3)
    xs[0] = GEN ** 1
    xs[1] = GEN ** 3
    xs[2] = GEN ** 0
    acc = GEN
    for p in unroll(0, 3):
        acc = match(log(xs[p]), range(0, 4), lambda k: add(acc * GEN ** p, k))
    p = 1
    p[1] = acc
    p[GEN] = 0
    return
