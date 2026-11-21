
def fill(h):
    value = hint_witness("value")
    h[1] = value
    return

def main():
    h = HeapBuf(1)
    assert log(h) < 1024
    hint_witness(h[0:1], "value")
    out = StackBuf(2)
    out[0] = h[1] * h[1]
    out[1] = h[1]
    public = 1
    assert public[1] == out[0]
    assert public[GEN] == out[1]
    return
