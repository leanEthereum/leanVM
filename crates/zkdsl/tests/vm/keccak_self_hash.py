def main():
    a = StackBuf(2)
    a[0] = 5
    a[1] = 7
    c = StackBuf(2)
    keccak(a, a, c)
    p = 1
    p[1] = c[0]
    p[GEN] = c[1]
    return
