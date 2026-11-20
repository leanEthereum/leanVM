def main():
    out = StackBuf(2)
    keccak([1, 2], [3, 4], out, len=40)
    return
