def main():
    h = StackBuf(2)
    h[0] = 5
    h[1] = 7
    for i in mul_range(1, GEN ** 4):
        p = 1
        p[1] = h[0]
        p[GEN] = h[1]
    return
