from snark_lib import *


def main():
    p = 0
    seed = p[0]
    n = p[1]
    last_write = p[2]
    match_tally = p[3]
    pipeline_squared = p[4]
    paired = p[5]
    flag = p[6]
    alt = p[7]

    assert n == 4

    counter_buf = Array(5)
    counter_buf[0] = 0
    for i in range(0, 4):
        counter_buf[i + 1] = 2 * i + 1
    assert counter_buf[4] == last_write

    acc_buf = Array(5)
    acc_buf[0] = seed
    for i in range(0, 4):
        a: Mut = acc_buf[i]
        match i:
            case 0:
                a = a + 1
            case 1:
                a = a + 3
            case 2:
                a = a + 5
            case 3:
                a = a + 7
        acc_buf[i + 1] = a
    assert acc_buf[4] == match_tally

    assert sqr_via_pipeline(seed + n) == pipeline_squared

    assert paired_sum(seed, n) == paired

    chosen: Imm
    if flag == 1:
        chosen = seed
    else:
        chosen = seed * 2
    assert chosen == alt

    assert flag * (1 - flag) == 0
    return


@inline
def sqr_via_pipeline(x):
    return mul_boxed(x, x)


def mul_boxed(a, b):
    return a * b


def paired_sum(a, b):
    total_buf = Array(5)
    total_buf[0] = 0
    for i in range(0, 4):
        total_buf[i + 1] = total_buf[i] + a + b
    return total_buf[4]
