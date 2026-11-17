def two(i: Const):
    return GEN ** i, GEN ** i

def pick(x, k: Const):
    k, e = match(log(x), range(0, 2), lambda i: two(i))
    return k + e

def main():
    r = pick(GEN ** 1, 7)
    p = GEN ** 0
    p[1] = r
    p[GEN] = GEN ** 0
    return
