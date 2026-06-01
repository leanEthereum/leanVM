from snark_lib import *

ARR = [1, 2, 3, 4, 5]


def main():
    x = (len(ARR) + ARR[2]) / ARR[3]
    sum_buf = Array(x + 1)
    sum_buf[0] = 0
    for i in range(0, x):
        sum_buf[i + 1] = sum_buf[i] + 1
    sum = sum_buf[x]
    assert sum == 2
    return
