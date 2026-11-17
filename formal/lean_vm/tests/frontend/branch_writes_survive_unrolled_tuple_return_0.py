def main():
    public = GEN ** 0
    flag = public[1]
    a = [5, 7]
    b = [13, 17]
    for i in unroll(0, 1):
        a, b = select_pair(flag, a, b)
    assert a[0] == 13
    assert a[1] == 17
    assert b[0] == 5
    assert b[1] == 7
    return

@inline
def select_pair(flag, a, b):
    first = StackBuf(2)
    second = StackBuf(2)
    if flag == 0:
        first[0] = a[0]
        first[1] = a[1]
        second[0] = b[0]
        second[1] = b[1]
    else:
        first[0] = b[0]
        first[1] = b[1]
        second[0] = a[0]
        second[1] = a[1]
    return first, second
