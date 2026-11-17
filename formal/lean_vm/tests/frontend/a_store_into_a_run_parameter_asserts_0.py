def pin(s: StackBuf(2)):
    s[0] = GEN ** 5
    s[1] = GEN ** 6
    return GEN ** 0

def main():
    b = StackBuf(2)
    hint_witness(b, "adv")
    z = pin(b)
    p = GEN ** 0
    p[1] = b[0]
    p[GEN] = b[1]
    return
