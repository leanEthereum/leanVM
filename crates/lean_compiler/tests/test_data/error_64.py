# Error: function parameter shadows a top-level scalar constant.
# Without rejection, `C` inside `pick` resolves to the constant value
# rather than the parameter.
C = 111


def main():
    out = pick(222)
    assert out == 222
    return


def pick(C):
    return C
