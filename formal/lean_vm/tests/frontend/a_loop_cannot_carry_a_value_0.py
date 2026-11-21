def main():
    s = GEN ** 0
    for i in mul_range(1, 8):
        s = s * GEN
    p = GEN ** 0
    p[1] = s
    p[GEN] = GEN ** 0
    return
