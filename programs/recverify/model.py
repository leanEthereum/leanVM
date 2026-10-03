"""Model the guest's cycles and committed words per inner proof under field-multiply options (README.md).

`python3 programs/recverify/model.py programs/recverify/measured.json`, from the workspace root, after building the host and the guest.

    cycles_X = plumbing (+ soft float, unless counted as removed) + sum_op n_op * c_X(op)
    rows_X   = the same per table, the new class CLMUL aside
    words_X  = stack_sizes(rows_X of the eleven tables, log_ram 21, log_advice 16) + CLMUL rows * words per row

`measured.json` holds, per run, the measured cycles and rows (`recverify-host`), the operation counts (`profile.py ops` on the counting build) and the plumbing and soft float split (`profile.py classes`). `shared` (core runs) is what k proofs of one program would share: everything outside `replay` (the program's setup, reading the advice, committing) and the one-time initializations (`initialize`) under it, `replay` building no circuit. `sw` is the guest's software kernels, `ext` the machine's extension-field instructions it uses now (the EXT table), and CLMUL a hypothetical class whose words per row are an estimate.
"""

import json
import math
import subprocess
import sys
from pathlib import Path

ELF = "programs/recverify/guest/target/riscv64im-leanvm-zkvm/release/recverify"
TABLES = ["ALU", "LOAD", "STORE", "LD", "SD", "SHIFT", "MUL", "MULH", "DIV", "HASH", "EXT"]
NEW_WORDS = {"CLMUL": 34}
OPS = ["Emul", "ExK", "Esq", "Kmul", "Ksq"]
OPTIONS = ("sw", "clmul", "ext")
# Cycles, rows per table (net of the loop) per operation. `sw` and `ext` are `prim` runs of this guest, `sw` on its software
# kernels. `clmul` was priced with a stand-in not carried here (a carry-less multiply pair), so it is an estimate.
COST = {
    "sw": {
        "Emul": (1244, {"ALU": 675, "LD": 117, "SD": 101, "SHIFT": 63, "MUL": 288}),
        "ExK": (635, {"ALU": 345, "LD": 57, "SD": 50, "SHIFT": 39, "MUL": 144}),
        "Esq": (147, {"ALU": 87, "LD": 10, "SD": 2, "SHIFT": 48}),
        "Kmul": (209, {"ALU": 113, "LD": 19, "SD": 16, "SHIFT": 13, "MUL": 48}),
        "Ksq": (53, {"ALU": 30, "LD": 7, "SHIFT": 16}),
    },
    "clmul": {
        "Emul": (76, {"ALU": 39, "LD": 5, "SD": 2, "SHIFT": 18, "CLMUL": 12}),
        "ExK": (51, {"ALU": 23, "LD": 2, "SD": 2, "SHIFT": 18, "CLMUL": 6}),
        "Esq": (52, {"ALU": 24, "LD": 2, "SD": 2, "SHIFT": 18, "CLMUL": 6}),
        "Kmul": (15, {"ALU": 7, "SHIFT": 6, "CLMUL": 2}),
        "Ksq": (15, {"ALU": 7, "SHIFT": 6, "CLMUL": 2}),
    },
    "ext": {
        "Emul": (15, {"LD": 6, "SD": 8, "EXT": 1}),
        "ExK": (14, {"ALU": 1, "LD": 6, "SD": 6, "EXT": 1}),
        "Esq": (12, {"LD": 6, "SD": 5, "EXT": 1}),
        "Kmul": (9, {"ALU": 2, "LD": 2, "SD": 4, "EXT": 1}),
        "Ksq": (7, {"LD": 2, "SD": 4, "EXT": 1}),
    },
}
LIMIT = 1 << 28


def words(rows):
    heights = [str(max(0, round(rows.get(t, 0)))) for t in TABLES]
    out = subprocess.run(["target/release/recverify-host", ELF, "words", "21", "16", *heights], capture_output=True, text=True, check=True).stdout
    base = int(out.split()[1])
    return base + sum(rows.get(c, 0) * w for c, w in NEW_WORDS.items())


def model(run, option, no_float):
    # Measured plumbing (and soft float), plus every field operation at the option's cost.
    cycles = run["plumbing"]["T"]
    rows = dict(run["plumbing"]["rows"])
    if not no_float:
        cycles += run["float"]["T"]
        for t, r in run["float"]["rows"].items():
            rows[t] = rows.get(t, 0) + r
    for op in OPS:
        n = run["ops"][op]
        c_x, r_x = COST[option][op]
        cycles += n * c_x
        for t, r in r_x.items():
            rows[t] = rows.get(t, 0) + n * r
    w = words(rows)
    per_row = (w - words({})) / cycles
    return cycles, rows, w, per_row


runs = json.loads(Path(sys.argv[1]).read_text())
for name, run in runs.items():
    for no_float in (False, True):
        for option in OPTIONS:
            cycles, rows, w, per_row = model(run, option, no_float)
            fit = (LIMIT - words({})) / per_row
            new = {c: round(rows.get(c, 0)) for c in [*NEW_WORDS, "EXT"] if rows.get(c, 0)}
            print(
                f"{name:24} {option:6} {'no float' if no_float else 'float   '} cycles {cycles / 1e6:9.2f}M (2^{math.log2(cycles):.2f}) "
                f"words {w / 1e6:10.1f}M (2^{math.log2(w):.2f}) {per_row:5.1f} w/cycle, one proof holds {fit / 1e6:5.2f}M cycles, "
                f"x{cycles / fit:6.2f} {new}"
            )

# k inner proofs of one program in one guest run: the program's setup and the one-time initializations once, the rest per proof.
for name, run in runs.items():
    if "shared" not in run:
        continue
    for option in OPTIONS:
        cycles, _, w, per_row = model(run, option, True)
        per_proof = cycles - run["shared"]
        fit = (LIMIT - words({})) / per_row
        for k in (1, 2):
            total = run["shared"] + k * per_proof
            print(
                f"{name:24} {option:6} no float k={k} cycles {total / 1e6:8.2f}M words {(total * per_row + words({})) / 1e6:9.1f}M "
                f"x{total / fit:5.2f} of one proof"
            )
