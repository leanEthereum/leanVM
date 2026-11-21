def swap(s: StackBuf(2)):
    t = StackBuf(2)
    t[0] = s[1]
    t[1] = s[0]
    return t

def main():
    b = StackBuf(2)
    b[0] = GEN ** 1
    b[1] = GEN ** 2
    r = swap(b)
    p = GEN ** 0
    p[1] = r[0]
    p[GEN] = r[1]
    return
