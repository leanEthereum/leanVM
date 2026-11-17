def main():
    out = StackBuf(2)
    keccak([1, 2], [3, 4], out, tail=[5, 6, 7, 8], len=129)
    return
