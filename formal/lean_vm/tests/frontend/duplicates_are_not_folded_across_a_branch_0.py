def main():
    x = GEN ** 3
    r = HeapBuf(2)
    # The same constant in both arms, and the else arm is the one that runs.
    if x == GEN ** 5:
        r[1] = GEN ** 4
    else:
        r[1] = GEN ** 4
    p = 1
    p[1] = r[1]
    p[GEN] = x
    return
