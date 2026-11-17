
def fill(h):
    value = hint_witness("value")
    h[1] = value
    return

def main():
    h = HeapBuf(1)
    early = StackBuf(1)
    early[0] = h[1]
    fill(h)
    out = StackBuf(2)
    out[0] = h[1] * h[1]
    out[1] = h[1]
    public = 1
    assert public[1] == out[0]
    assert public[GEN] == out[1]
    return
