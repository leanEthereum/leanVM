"""Does the compiled code perform a function's heap events in the core's statement order? (core-mode census)

Each core `load` atom (a read, or a store when its word is already defined: the core does not say which)
is matched with a `DEREF` of mode `cell` of the compiled code at the certificate's cells (`Cert.locs`):
pointer cell, offset, word cell. Within each block between control statements (an `ite`, a `match` or
an arm starts a new block; calls do not), the matched offsets should increase. Reported: atoms matched, atoms with no `DEREF` of
their own (a cell the compiler shares with an earlier load: its `DEREF` is the earlier one's, so it
is earlier still, which a check that covers the earlier load already covers), and the functions whose matched offsets go
back, with the count of such inversions. A measurement, not a proof."""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import coreir

D = coreir.load()


def loads(body, out):
    for s in body:
        if s[0] == 'a' and s[1][0] == 'load':
            out.append(('load',) + s[1][1:])
        elif s[0] == 'a' and s[1][0] == 'hint' and s[1][1][0] == 'witness':
            out.append(('wit',))
        elif s[0] == 'ite':
            out.append(('cut',)); loads(s[2], out); out.append(('cut',)); loads(s[3], out); out.append(('cut',))
        elif s[0] == 'match':
            for a in s[2]:
                out.append(('cut',)); loads(a, out)
            out.append(('cut',))
        elif s[0] in ('call', 'callIf', 'dispatch'):
            out.append((s[0],))
    return out


def main():
    stats = collections.Counter()
    bad = []
    for k, (params, body) in D['core'].items():
        c = D['comp'][k]
        code, locs = c['code'], c['locs']
        if code is None:
            continue
        at = collections.defaultdict(list)
        for i, (op, a) in enumerate(code):
            if op == 'deref' and len(a) == 4 and a[3] == '.cell':
                at[(a[0], a[1], a[2])].append(i)
        seq, seen = [], set()
        for e in loads(body, []):
            if e[0] == 'cut':
                seq.append(None)
                continue
            if e[0] != 'load':
                continue
            d, p, off = e[1:]
            if d >= len(locs) or p >= len(locs):
                stats['no-cell'] += 1
                continue
            key = (locs[p], off, locs[d])
            hits = at.get(key, [])
            if not hits:
                stats['no-deref'] += 1
                continue
            if key in seen:
                stats['shared-with-earlier'] += 1
                continue
            seen.add(key)
            stats['matched'] += 1
            seq.append(hits)
        inv, last = 0, -1
        for hits in seq:
            if hits is None:
                last = -1
                continue
            nxt = [h for h in hits if h >= last]
            if nxt:
                last = min(nxt)
            else:
                inv += 1
        if inv:
            bad.append((inv, k))
    print(dict(stats))
    print(f'functions with a load or store out of statement order: {len(bad)} of {len(D["core"])}')
    for inv, k in sorted(bad, reverse=True)[:25]:
        print(f'  {k:45s} {inv}')


if __name__ == '__main__':
    main()
