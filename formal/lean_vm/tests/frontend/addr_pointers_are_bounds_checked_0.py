def main():
    b = StackBuf(2)
    p = addr(b)
    p[GEN ** 40] = GEN ** 3
    return
