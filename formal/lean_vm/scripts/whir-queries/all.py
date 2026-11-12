"""Regenerate the WHIR queries' per-specialization Lean files from the guest's data.

    python3 -I scripts/whir-queries/all.py LEAN_VM

`gen.py` reads the core IR (`LeanVM/Guest/Data/Core*.lean`); the others write
`B1/Bits/QueryWindowsData.lean` (`genqwdata`), `B1/Opening/WalkBody0-2.lean` and `WalkFns.lean`
(`genwalk`), `B1/Opening/QueriesBody0-3.lean`, `QueriesW0-3.lean`, `QueriesAllW.lean` (`genoq`),
`B1/Opening/QueriesPlacedS0-3.lean` (`genplaced`),
`Guest/WalkWp.lean`, `WalkWpOk.lean` (`genwp`) and `Guest/WalkOq0-3.lean`, `WalkOqOk0-3.lean`
(`genwalkoq`). The shapes' lists in `Interface.lean`, `QueriesT.lean`, `QueryWindowsT.lean` and
`Witness.lean` come from `gen.py shapes` and `gen.py walk`.
"""
import os, subprocess, sys
here = os.path.dirname(os.path.abspath(__file__))
for g in ['genqwdata', 'genwalk', 'genoq', 'genplaced', 'genwp', 'genwalkoq']:
    subprocess.run([sys.executable, '-I', os.path.join(here, g + '.py'), sys.argv[1]], check=True,
                   stdout=subprocess.DEVNULL)
