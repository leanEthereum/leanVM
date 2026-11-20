def main():
    nb = StackBuf(1)
    hint_witness(nb[0:1], "n")
    n = nb[0]
    assert_gpow(n)
    x = GEN ** 3
    assert log x < log n
    p = 1
    p[1] = x
    p[GEN] = x
    return
