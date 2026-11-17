def two(i: Const):
    return GEN ** i, GEN ** i

def pick(x, k: Const):
    sb = StackBuf(2)
    sb[0] = 0
    sb[k], e = match(log(x), range(0, 2), lambda i: two(i))
    return sb[1] + e

def main():
    r = pick(GEN ** 1, 1)
    p = GEN ** 0
    p[1] = r
    p[GEN] = GEN ** 0
    return
