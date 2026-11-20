def f(s: StackBuf(2)):
    return s[0]

def main():
    b = StackBuf(3)
    b[0] = GEN ** 1
    r = f(b)
    p = GEN ** 0
    p[1] = r
    p[GEN] = GEN ** 0
    return
