def main():
    a = GEN ** 20
    b = GEN ** 7
    q = a / b
    r = 1 / b
    p = 1
    p[1] = q * b
    p[GEN] = r * b
    return
