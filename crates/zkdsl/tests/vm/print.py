def main():
    x = 5
    y = x * GEN
    print(y)
    print("the product", y * y)
    b = HeapBuf(2)
    b[1] = 3
    print(b[1])
    p = 1
    p[1] = y
    p[GEN] = b[1]
    return
