# Error: function parameter shadows a top-level const array.
# Without rejection, `ARR[0]` inside `pick` silently resolved to the
# const array instead of the caller-provided runtime array.
ARR = [111]


def main():
    local = Array(1)
    local[0] = 222
    out = pick(local)
    assert out == 222
    return


def pick(ARR):
    return ARR[0]
