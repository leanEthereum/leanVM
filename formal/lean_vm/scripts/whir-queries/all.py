"""Regenerate the WHIR queries' per-specialization Lean files from the guest's data.

    python3 -I scripts/whir-queries/all.py LEAN_VM

`gen.py` reads the core IR (`LeanVM/Guest/Data/Core*.lean`); the others write
`B1/Bits/QueryWindowsData.lean` (`genqwdata`), `B1/Opening/WalkBody0-2.lean` and `WalkFns.lean`
(`genwalk`), `B1/Opening/QueriesBody0-3.lean` and `QueriesFns.lean`'s cases (`genoq`),
`Guest/WalkWp.lean`, `WalkWpOk.lean` (`genwp`), `Guest/WalkOq0-3.lean`, `WalkOqOk0-3.lean`
(`genwalkoq`), `Guest/WalkLq0-3.lean`, `WalkLqOk0-3.lean`, `WalkOs0-3.lean`, `WalkOsOk0-3.lean` (`genwalklqos`), and the specializations' lists in `Interface.lean`, `QueriesT.lean`,
`QueryWindowsT.lean` and `Witness.lean` (`lists`). Functions are named by their stable names
(`Guest/CoreRef.lean`), read from `Data/NameStrings.lean`.
"""
import os, subprocess, sys
here = os.path.dirname(os.path.abspath(__file__))
for g in ['lists', 'genqwdata', 'genwalk', 'genoq', 'genwp', 'genwalkoq', 'genwalklqos']:
    subprocess.run([sys.executable, '-I', os.path.join(here, g + '.py'), sys.argv[1]], check=True,
                   stdout=subprocess.DEVNULL)
