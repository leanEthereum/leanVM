def stop():
    s = hint_witness("stop")
    assert log(s) < 8
    return s

def main():
    for i in mul_range(1, stop()):
        x = i
    return
