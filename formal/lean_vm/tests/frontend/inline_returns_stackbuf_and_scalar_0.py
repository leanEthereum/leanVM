def main():
    s = StackBuf(2)
    s[0] = 5
    s[1] = 7
    s, x = step(s, 9)
    s, y = step(s, x)
    p = 1
    p[1] = s[0]
    p[GEN] = s[1]
    return

@inline
def step(state, v):
    tg = StackBuf(2)
    tg[0] = v
    tg[1] = 3
    nb = StackBuf(2)
    keccak(state, tg, nb)
    return nb, v
