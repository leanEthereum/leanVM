"""Lean literals of the static certificates of `Memory/Static.lean` (`Cert`), for the generated
families (`family.py`) and the tables read off them."""


def lean_pairs(l): return '[' + ', '.join('(%d, %d)' % q for q in l) + ']'
def lean_ks(l): return '[' + ', '.join('(.n %d, %d)' % q for q in l) + ']'
def lean_aff(b): return '⟨%d, %s⟩' % (b[0], lean_pairs(b[1]))
def lean_vec(l): return '[' + ', '.join(map(str, l)) + ']'
def lean_affv(b): return '⟨%s, [%s]⟩' % (lean_vec(b[0]), ', '.join('(%d, %s)' % (k, lean_vec(v)) for k, v in b[1]))


def lean_acc(r):
    """A bound and its preconditions (`Acc`)."""
    return '(%s, %s)' % (lean_aff((r[0], r[1])), lean_pairs(r[2]))


def lean_accv(r):
    """A bound by coordinate and its preconditions (`AccV`)."""
    return '(%s, %s)' % (lean_affv((r[0], r[1])), lean_pairs(r[2]))


def lean_cert(c):
    if c[0] == 'stat':
        return '.stat %s %s %s' % (lean_pairs(c[1]), lean_aff(c[2]), lean_ks(c[3]))
    endc = 'none' if c[1] is None else '(some %d)' % c[1]
    return '.loop %s %s %s %s' % (endc, lean_pairs(c[2]), lean_aff(c[3]), lean_ks(c[4]))
