Y_TOWER = 18446744073709551616

def main():
    yt = Y_TOWER
    a = yt * GEN
    b = Y_TOWER * GEN
    assert a == b
    p = GEN ** 0
    p[1] = a
    p[GEN] = b
    return
