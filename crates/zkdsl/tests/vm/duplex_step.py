
from snark_lib import *

Y = 18446744073709551616

@inline
def challenge_from_state(state):
    return state[0]

@inline
def fs_pack(rate, k: Const, x, tag):
    rate[2 * k] = x
    rate[2 * k + 1] = Y * tag
    return

def main():
    seed = [17195033418914725426, 428513430413020027537992053012892565, 257116918944239717510212610026684884823, 22419017885407545356794260588114009968, 296961243940228212369120540763663007988]
    rate = StackBuf(2)
    fs_pack(rate, 0, 110680464442257309701, 1)
    sp = StackBuf(13)
    keccak(rate[0:2], [0, 0], sp, cap=seed)
    first = challenge_from_state(sp)
    nxt = StackBuf(13)
    keccak([0, 0], [0, 0], nxt, cap=sp)
    second = challenge_from_state(nxt)
    p = GEN ** 0
    p[1] = first
    p[GEN] = second
    return
