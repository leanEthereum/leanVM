def two(i: Const):
    return GEN ** i, GEN ** i

def main():
    for j in unroll(0, 2):
        j, e = match(log(GEN ** 1), range(0, 2), lambda i: two(i))
    r = j + e
    p = GEN ** 0
    p[1] = r
    p[GEN] = GEN ** 0
    return
