# Error: const-array index out of bounds must surface as a structured
# `CompileError`
ARR = [10, 20]


def main():
    assert ARR[2] == 0
    return
