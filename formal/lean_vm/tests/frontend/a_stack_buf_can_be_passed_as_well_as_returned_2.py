def f(s: StackBuf(2)):
    return s[0]

def main():
    r = f(GEN ** 1)
    p = GEN ** 0
    p[1] = r
    p[GEN] = GEN ** 0
    return
