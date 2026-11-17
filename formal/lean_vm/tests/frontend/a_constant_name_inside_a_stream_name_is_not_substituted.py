SEED = 8

def main():
    s = StackBuf(1)
    hint_witness(s, "SEED")
    assert s[0] == 8
    return
