def main():
    s = StackBuf(2)
    s[0] = s[1]
    s[1] = s[0]
    p = 1
    p[1] = s[0]
    p[GEN] = s[0]
    return
