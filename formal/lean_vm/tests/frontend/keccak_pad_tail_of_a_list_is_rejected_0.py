def main():
    out = StackBuf(2)
    keccak([1, 2], [3, 4], out, tail=[5, 0, 0, 0], len=80, pad_tail=1)
    return
