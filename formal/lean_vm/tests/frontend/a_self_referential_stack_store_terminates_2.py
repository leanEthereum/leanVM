def main():
    s = StackBuf(2)
    s[0] = 5
    s[1] = 7
    s = [s[1], s[0]]
    p = 1
    p[1] = s[0]
    p[GEN] = s[1]
    return
