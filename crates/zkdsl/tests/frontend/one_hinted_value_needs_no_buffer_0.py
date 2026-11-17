def main():
    mb = StackBuf(1)
    hint_witness(mb[0:1], "m")
    m = mb[0]
    assert log m < 8
    p = GEN ** 0
    p[1] = m
    p[GEN] = GEN ** 0
    return
