def pick():
    s = StackBuf(2)
    s[0] = GEN ** 1
    s[1] = GEN ** 2
    s = hint_witness("m")
    return s

def main():
    r = pick()
    p = GEN ** 0
    p[1] = r
    p[GEN] = GEN ** 0
    return
