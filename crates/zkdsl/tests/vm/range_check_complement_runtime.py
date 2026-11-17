def main():
    nb = StackBuf(1)
    hint_witness(nb[0:1], "n")
    n = nb[0]
    x = GEN ** 0
    assert log x < log n
    p = 1
    p[1] = x
    p[GEN] = x
    return
