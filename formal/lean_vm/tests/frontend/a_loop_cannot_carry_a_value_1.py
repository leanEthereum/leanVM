def main():
    p = GEN ** 0
    t = 7
    for i in mul_range(1, 8):
        p[i] = t
        for k in unroll(0, 1):
            if k == 0:
                t = 9
    return
