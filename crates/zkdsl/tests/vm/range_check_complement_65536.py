def main():
    x = GEN ** 0
    assert log x < 65536
    p = 1
    p[1] = x
    p[GEN] = x
    return
