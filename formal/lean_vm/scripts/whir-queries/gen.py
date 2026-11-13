"""Generate S1b's per-specialization Lean lists from the regenerated guest data.

  python3 -I gen.py LEAN_VM shapes   the `openingQueriesShapes` list (Interface.lean)
  python3 -I gen.py LEAN_VM specs    the specializations, one per line
  python3 -I gen.py LEAN_VM walk     the walk_path (index, pd, cd) list
"""
import os, re, sys, glob
D = os.path.join(sys.argv[1], 'LeanVM') + '/' + 'Guest/Data/'
fns = {}   # name -> (idx, file)
bodies = {}  # coreN -> namespace text
order = []
for f in sorted(glob.glob(D + 'Core*.lean')):
    t = open(f).read()
    for m in re.finditer(r'noncomputable def core(\d+) : Core\.Fn where\n  name := "([^"]*)"', t):
        fns[m.group(2)] = int(m.group(1))
    for m in re.finditer(r'^namespace (core\d+)\n(.*?)^end \1$', t, re.M | re.S):
        bodies[m.group(1)] = m.group(2)
# Each compiled name's stable name (`Data/NameStrings.lean`, `guest-core`): a loop's is its caller's and its rank.
stable = {c: s for s, c in re.findall(r'^abbrev «([^»]+)» : String := "([^"]+)"$',
                                     open(D + 'NameStrings.lean').read(), re.M)}

def oq_specs():
    out = []
    for name, i in fns.items():
        if not name.startswith('opening_queries__L'):
            continue
        ps = [int(x) for x in name[len('opening_queries__L'):].split('_L')]
        odd, base, folds, leaf, depth, cd, mu, vanish, nhs, hsb, final = ps
        b = bodies['core%d' % i]
        loop = re.search(r'callIf \(\.n \d+\) "(__loop\d+)"', b).group(1)
        vs = []
        if final:
            lb = bodies['core%d' % fns[loop]]
            m = re.search(r'\.copy \(\.n (\d+)\) \(\.n \d+\)\) ::\n((?:  \.atom \(\.(?:const|add|mul) [^\n]*\n)+)', lb)
            consts = re.findall(r'\.const \(\.n \d+\) \(word (\d+) 0\)', m.group(2))
            vs = [int(c) for c in consts[:mu]]
            assert len(vs) == mu, (name, consts)
        out.append(dict(name=name, idx=i, loop=loop, loopidx=fns[loop], odd=odd, base=base, folds=folds,
                        leaf=leaf, depth=depth, cd=cd, mu=mu, vanish=vanish, nhs=nhs, hsb=hsb, final=final, vs=vs))
    out.sort(key=lambda d: d['idx'])
    return out

if __name__ == '__main__':
    mode = sys.argv[2]
    if mode == 'shapes':
        for d in oq_specs():
            print('    ("%s", ⟨%d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, [%s]⟩),' % (
                d['name'], d['odd'], d['base'], d['folds'], d['leaf'], d['depth'], d['cd'], d['mu'],
                d['vanish'], d['nhs'], d['hsb'], d['final'], ', '.join(map(str, d['vs']))))
    elif mode == 'walk':
        for name, i in sorted(fns.items(), key=lambda p: p[1]):
            if name.startswith('walk_path__L'):
                pd, cd = map(int, name[len('walk_path__L'):].split('_L'))
                print(i, pd, cd, name)
    elif mode == 'specs':
        for d in oq_specs():
            print(d)
