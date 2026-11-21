def main():
    o = StackBuf(2)
    t = [1, 2]
    for i in mul_range(1, 8):
        keccak(t, t, o)
        t = [3, 4]
    return
