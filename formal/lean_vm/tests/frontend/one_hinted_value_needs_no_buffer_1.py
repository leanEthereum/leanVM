def main():
    m = hint_witness("m")
    assert log m < 8
    p = GEN ** 0
    p[1] = m
    p[GEN] = GEN ** 0
    return
