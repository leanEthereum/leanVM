@inline
def id(k: Const):
    return GEN ** k

@inline
def sel(a):
    r = match(log(a), range(0, 4), lambda k: id(k))
    return r

@inline
def add(acc, k: Const):
    return acc * GEN ** (k + 1)

def main():
    q = 1
    xs = [GEN ** 0, GEN ** 1]
    ys = [GEN ** 2, GEN ** 0]
    acc = GEN
    for p in unroll(0, 2):
        acc = match(log(sel(xs[p])), range(0, 4), lambda k: add(acc, k))
        acc = match(log(ys[p]), range(0, 4), lambda k: add(acc, k))
    q[1] = acc
    q[GEN] = 0
    return
