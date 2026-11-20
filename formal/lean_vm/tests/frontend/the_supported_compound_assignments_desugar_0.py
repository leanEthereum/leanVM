def main():
    x = 4
    x += 1
    x *= 2
    x //= 2
    x %= 3
    x -= 1
    p = GEN ** 0
    p[1] = x
    p[GEN] = x
    return
