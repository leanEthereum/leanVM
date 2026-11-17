def main():
    a = StackBuf(5)
    a[0] = 5
    a[1] = 5 + 2
    assert a[0] == 5
    return
