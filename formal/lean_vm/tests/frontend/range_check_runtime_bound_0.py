def main():
    nb = StackBuf(1)
    hint_witness(nb[0:1], "n")
    n = nb[0]
    assert log n < 64
    x = GEN ** 5
    assert log x < log n
    assert log 1 < log n
    p = 1
    p[1] = x
    p[GEN] = n
    return
