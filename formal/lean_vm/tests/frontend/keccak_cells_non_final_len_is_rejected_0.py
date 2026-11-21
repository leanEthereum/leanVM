def main():
    out = StackBuf(13)
    keccak_cells([1, 2], out, final=0, len=16)
    return
