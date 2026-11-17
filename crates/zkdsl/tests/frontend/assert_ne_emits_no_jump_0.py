def main():
    x = GEN ** 5
    y = GEN ** 7
    assert x != y
    p = 1
    p[1] = x
    p[GEN] = y
    return
