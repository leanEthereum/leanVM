def main():
    for i in mul_range(1, GEN ** 6):
        assert log i < log GEN ** 6
    p = 1
    p[1] = 5
    p[GEN] = 7
    return
