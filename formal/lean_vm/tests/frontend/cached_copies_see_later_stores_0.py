
def square(h):
    return h[GEN] * h[GEN]

def main():
    h = HeapBuf(2)
    early = StackBuf(1)
    other = StackBuf(1)
    early[0] = h[GEN]
    value = hint_witness("value")
    early[0] = value
    early[0] = h[GEN]
    result = square(h)
    public = 1
    assert public[1] == result
    return
