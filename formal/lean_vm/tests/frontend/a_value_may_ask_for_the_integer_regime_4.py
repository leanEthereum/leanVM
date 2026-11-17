def main():
    for i in unroll(3, 4):
        v = const(i - 1)
        p = GEN ** 0
        p[1] = v
    return
