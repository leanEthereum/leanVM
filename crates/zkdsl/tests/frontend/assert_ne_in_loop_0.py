def main():
    c = GEN ** 9
    for i in mul_range(1, GEN ** 6):
        assert i != c
    p = 1
    p[1] = 5
    p[GEN] = 7
    return
