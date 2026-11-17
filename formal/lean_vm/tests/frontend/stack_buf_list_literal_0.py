def main():
    s = [5, 7]
    s = [s[1], s[0]]
    t = [s[0] + s[1], 3]
    out = StackBuf(2)
    keccak(s, t, out)
    p = 1
    p[1] = out[0]
    p[GEN] = out[1]
    return
