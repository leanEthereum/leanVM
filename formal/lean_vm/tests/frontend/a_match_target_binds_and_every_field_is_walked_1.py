def two(i: Const):
    return GEN ** i, GEN ** i

def pick(k: Const):
    a, b = match(log(GEN ** k), range(0, 2), lambda i: two(i + k))
    return a + b

def main():
    r = pick(1)
    p = GEN ** 0
    p[1] = r
    p[GEN] = GEN ** 0
    return
