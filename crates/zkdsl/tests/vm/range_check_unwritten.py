def main():
    x = GEN ** 300
    assert log x < 400
    p = 1
    p[1] = x
    p[GEN] = x
    return
