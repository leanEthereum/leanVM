def main():
    x = GEN ** 5
    assert log x < log GEN ** 8
    y = GEN ** 7
    assert log y < 8
    assert log 1 < log GEN ** 8
    z = x * y
    assert log z < 13
    p = 1
    p[1] = z
    p[GEN] = x
    return
