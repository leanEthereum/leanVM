import json,sys
import os
cg=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'cg.json')))
bymod={f['mod']:f for f in cg}
status=sys.argv[1]
total=set()
for line in open(status):
    c=line.split('|')
    if len(c)>8 and c[2].strip().isdigit() and 'yes' in c[6]:
        total.add(int(c[2]))
# also stated (225) counts as available
part={}
for line in open(status):
    c=line.split('|')
    if len(c)>8 and c[2].strip().isdigit(): part[int(c[2])]=c[5].strip()
rem=[f for f in cg if f['idx'] not in total]
def ready(f,extra=set()):
    return all(bymod[c]['idx'] in total|extra or bymod[c]['idx']==225 for c in f['callees'])
fr=[f for f in rem if ready(f)]
fr.sort(key=lambda f:(f['h'],f['idx']))
print('frontier now:',len(fr),sum(f['n'] for f in fr))
for f in fr: print(f"{f['idx']:5} h{f['h']} {part.get(f['idx'],'?')} n={f['n']:4} loops={f['loops']} {f['key'][:80]}")
