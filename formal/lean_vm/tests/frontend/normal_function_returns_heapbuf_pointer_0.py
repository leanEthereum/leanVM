def main():
    out = make()
    p = 1
    p[1] = out[1]
    p[GEN] = out[GEN]
    return

def make():
    out = HeapBuf(2)
    out[1] = 17
    out[GEN] = 23
    return out
