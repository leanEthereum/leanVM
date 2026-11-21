def main():
    p = GEN ** 0
    t = [1, 2]
    for i in mul_range(1, 8):
        p[i] = t[0]
        t = [3, 4]
    return
