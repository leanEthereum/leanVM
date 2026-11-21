def main():
    a = StackBuf(328)
    x = GEN ** 5792
    assert log x < 65536
    for i in unroll(0, 164):
        assert a[0] == 8
    return
