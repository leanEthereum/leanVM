def main():
    x = GEN ** 6
    q = x / (GEN ** 2)
    z = GEN ** (6 // 2)
    p = 1
    p[1] = q
    p[GEN] = z
    return
