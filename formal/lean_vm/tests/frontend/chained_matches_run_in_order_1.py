@inline
def add(acc, k: Const):
    return acc * GEN ** (k + 1)

def main():
    xs = StackBuf(3)
    xs[0] = GEN ** 1
    xs[1] = GEN ** 3
    xs[2] = GEN ** 0
    acc = GEN
    acc = match(log(xs[0]), range(0, 4), lambda k: add(acc * GEN ** 0, k))
    acc = match(log(xs[1]), range(0, 4), lambda k: add(acc * GEN ** 1, k))
    acc = match(log(xs[2]), range(0, 4), lambda k: add(acc * GEN ** 2, k))
    p = 1
    p[1] = acc
    p[GEN] = 0
    return
