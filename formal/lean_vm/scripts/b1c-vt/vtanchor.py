# Library: the positions and values in verify_tables' body (vt_ir.txt from dump.py, or $VT_IR) that the generators past
# its table sumcheck read, found from the body rather than fixed: the `eq_prefix_chain` call filling `zc_peq` (`EQP`,
# its first argument `PEQ`, its last `GZN`), the last table sumcheck record's loads before it (its cursor `CUR`, offset 5, and claim
# `CLAIM`, offset 6), the forms' window from the call to the final claim's check (`WLO`, `WHI`).
import os, re
HERE = os.path.dirname(os.path.abspath(__file__))
IRF = os.environ.get('VT_IR', os.path.join(HERE, 'vt_ir.txt'))


def _ir():
    ir = {}
    for line in open(IRF).read().splitlines():
        k, _, s = line.partition(': ')
        if k == 'params':
            continue
        ir[int(k)] = s.strip().removesuffix(' ::')
    return ir


def anchors():
    ir = _ir()
    eqp = [p for p, s in ir.items() if re.match(r'\.call "eq_prefix_chain(_rev)?" \[\.n (\d+),', s)]
    assert len(eqp) == 1, eqp
    eqp = eqp[0]
    peq = int(re.match(r'\.call "eq_prefix_chain(_rev)?" \[\.n (\d+),', ir[eqp]).group(2))
    gzn = int(re.findall(r'\.n (\d+)', ir[eqp])[-1])
    # the record's loads at offsets 0 .. 6, the last ones before the call
    rec = {}
    for p in range(eqp - 1, eqp - 40, -1):
        m = re.match(r'\.atom \(\.load \(\.n (\d+)\) \(\.n (\d+)\) ([0-6])\)$', ir[p])
        if m and int(m.group(3)) not in rec:
            rec[int(m.group(3))] = (int(m.group(1)), int(m.group(2)))
        if len(rec) == 7:
            break
    assert len(rec) == 7 and len({r[1] for r in rec.values()}) == 1, rec
    cur, claim = rec[5][0], rec[6][0]
    whi = [p for p, s in ir.items() if p > eqp and re.match(r'\.atom \(\.assertEq \(\.n \d+\) \(\.n %d\)\)$' % claim, s)]
    assert len(whi) == 1, whi
    return dict(EQP=eqp, PEQ=peq, GZN=gzn, CUR=cur, CLAIM=claim, WLO=eqp + 1, WHI=whi[0])


A = anchors()
EQP, PEQ, GZN, CUR, CLAIM, WLO, WHI = A['EQP'], A['PEQ'], A['GZN'], A['CUR'], A['CLAIM'], A['WLO'], A['WHI']
