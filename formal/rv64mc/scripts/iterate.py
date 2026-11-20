#!/usr/bin/env python3
"""Helpers of `iterate.sh`: a `lean` that records each module's cost, and the run's report.

  iterate.py sysroot DIR          a sysroot like the toolchain's whose `lean` and `leanir` are `iterate.py wrap`
  iterate.py wrap TOOL ARGS...    (from Lake) run the real tool in one of $ITER_JOBS slots, append a row to $ITER_LOG
  iterate.py report META LABEL    the run's TSV row and markdown section, from the files in META
  iterate.py sweep PROJECT META   `rv_sweep` (Tactic/Sym.lean) on each template META/templates.txt lists as changed

A row of $ITER_LOG: module, tool, exit code, wall s, CPU s (user + system of the process and its children), peak RSS MB.
A module that fails keeps its output in $ITER_LOG's directory, `fail/<module>.txt`. Standard library only.
"""

import fcntl
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
import time
from collections import defaultdict
from pathlib import Path

CLASSES = ("Gen.Tmpl", "Gen.Link", "Gen other", "Statement", "Model", "Spec", "Proof", "Table", "Final", "other")


def module_class(m: str) -> str:
    if not m.startswith("Rv64mc."):
        return "Statement"
    rest = m[len("Rv64mc."):]
    for prefix, cls in (("Gen.Tmpl.", "Gen.Tmpl"), ("Gen.Link.", "Gen.Link"), ("Gen.", "Gen other"),
                        ("Model.", "Model"), ("Spec.", "Spec"), ("Proof.", "Proof"), ("Table.", "Table"),
                        ("Final.", "Final")):
        if rest.startswith(prefix):
            return cls
    return "Gen other" if rest == "Gen" else "other"


def sysroot(into: Path) -> None:
    real = Path(subprocess.run(["lean", "--print-prefix"], capture_output=True, text=True, check=True).stdout.strip())
    (into / "bin").mkdir(parents=True)
    for entry in real.iterdir():
        if entry.name != "bin":
            (into / entry.name).symlink_to(entry)
    for entry in (real / "bin").iterdir():
        target = into / "bin" / entry.name
        if entry.name in ("lean", "leanir"):
            script = shlex.join([sys.executable, "-I", os.path.abspath(__file__), "wrap", entry.name])
            target.write_text(f'#!/bin/sh\nexec {script} "$@"\n', encoding="utf-8")
            target.chmod(0o755)
        else:
            target.symlink_to(entry)
    print(real / "bin")


def wrap(tool: str, args: list[str]) -> None:
    real = os.path.join(os.environ["ITER_BIN"], tool)
    env = {k: v for k, v in os.environ.items() if not k.startswith("ITER_")}
    env.pop("LAKE_OVERRIDE_LEAN", None)
    if "ITER_SYSROOT" in os.environ:
        env["LEAN_SYSROOT"] = os.environ["ITER_SYSROOT"]
    else:
        env.pop("LEAN_SYSROOT", None)
    if tool == "lean":
        setup = args[args.index("--setup") + 1] if "--setup" in args else None
    else:
        setup = args[0] if tool == "leanir" and args else None
    if setup is None:
        os.execve(real, [real, *args], env)
    name = json.load(open(setup, encoding="utf-8"))["name"] + ("" if tool == "lean" else f":{tool}")
    log = Path(os.environ["ITER_LOG"])
    slots = int(os.environ.get("ITER_JOBS", "8"))
    lock = None
    while lock is None:
        for i in range(slots):
            f = open(log.parent / f"slot{i}", "w")
            try:
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
                lock = f
                break
            except OSError:
                f.close()
        else:
            time.sleep(0.2)
    start = time.monotonic()
    with tempfile.TemporaryFile() as fo, tempfile.TemporaryFile() as fe:
        child = subprocess.Popen([real, *args], env=env, stdout=fo, stderr=fe)
        _, status, usage = os.wait4(child.pid, 0)
        fo.seek(0)
        fe.seek(0)
        out, err = fo.read(), fe.read()
    code = os.waitstatus_to_exitcode(status)
    wall = time.monotonic() - start
    lock.close()
    with open(log, "a", encoding="utf-8") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        cpu = usage.ru_utime + usage.ru_stime
        f.write(f"{name}\t{tool}\t{code}\t{wall:.1f}\t{cpu:.1f}\t{usage.ru_maxrss / 1024:.0f}\n")
    if code != 0:
        (log.parent / "fail").mkdir(exist_ok=True)
        (log.parent / "fail" / f"{name}.txt").write_bytes(out + err)
    sys.stdout.buffer.write(out)
    sys.stdout.flush()
    sys.stderr.buffer.write(err)
    sys.stderr.flush()
    sys.exit(code if code >= 0 else 128 - code)


def first_error(text: str) -> str:
    for line in text.splitlines():
        try:
            msg = json.loads(line)
        except ValueError:
            msg = None
        if isinstance(msg, dict) and msg.get("severity") == "error":
            pos = msg.get("pos") or {}
            data = str(msg.get("data", "")).strip().splitlines()
            return f"{Path(msg.get('fileName', '')).name}:{pos.get('line', '?')}: {data[0][:180] if data else ''}"
    for line in text.splitlines():
        if re.search(r"\berror\b", line):
            line = re.sub(r"^.*?/(Rv64mc/[^ ]*\.lean)", r"\1", line.strip())
            return line[:200]
    return text.strip().splitlines()[-1][:200] if text.strip() else "(no output)"


def read(path: Path, default: str = "") -> str:
    return path.read_text(encoding="utf-8").strip() if path.exists() else default


def read_time(path: Path) -> dict:
    """`/usr/bin/time -f '%e %U %S %M %x'`: wall, CPU (user + system), peak RSS MB, exit code."""
    lines = read(path).splitlines()
    parts = lines[-1].split() if lines else []
    if len(parts) < 3:
        return {}
    out = {"wall": float(parts[0]), "cpu": float(parts[1]) + float(parts[2])}
    if len(parts) >= 5:
        out["rss"], out["code"] = int(parts[3]) / 1024, parts[4]
    return out


def report(meta: Path, label: str) -> None:
    rows = [l.split("\t") for l in read(meta / "lean.tsv").splitlines() if l]
    per = defaultdict(lambda: [0, 0.0, []])
    failed = []
    total_cpu = 0.0
    for name, tool, code, wall, cpu, rss in rows:
        cpu = float(cpu)
        total_cpu += cpu
        mod = name.split(":")[0]
        cls = module_class(mod)
        if tool == "lean":
            per[cls][0] += 1
            per[cls][2].append(mod)
        per[cls][1] += cpu
        if code != "0":
            failed.append((mod, first_error(read(meta / "fail" / f"{name}.txt"))))
    # Failures Lake reports without running `lean` (a bad import): its `✖ … Running M` line and the error after it.
    seen = {m for m, _ in failed}
    log_lines = read(meta / "build.txt").splitlines()
    for i, line in enumerate(log_lines):
        hit = re.match(r"^✖ \[\d+/\d+\] Running (\S+)$", line)
        if hit and hit.group(1).startswith("Rv64mc") and hit.group(1) not in seen:
            seen.add(hit.group(1))
            err = next((l for l in log_lines[i + 1:i + 4] if l.startswith("error")), "(no message)")
            if "no such file" in err:
                err = "its source does not exist (a removed template)"
            failed.append((hit.group(1), err.removeprefix("error: ")[:200]))
    times = {k: read_time(meta / f"{k}.time") for k in ("regen", "layouts", "build")}
    elf = read(meta / "elf-diff.txt")
    tmpl = read(meta / "templates.txt")
    tsummary = next((l for l in tmpl.splitlines() if l.startswith("templates:")), "templates: ?")
    changed = [l.split("\t")[1] for l in tmpl.splitlines() if l.startswith(("changed\t", "added\t", "removed\t"))]
    ch = re.search(r"templates: (\d+) changed", tsummary)
    raw = re.search(r"^\s*raw: (.*)$", elf, re.M)
    mod_addr = re.search(r"^\s*modulo addresses: (.*)$", elf, re.M)
    sweep = [l.split("\t") for l in read(meta / "sweep.tsv").splitlines() if l]
    sweep_cpu = sum(float(r[2]) for r in sweep)
    build = times.get("build", {})
    regen = times.get("regen", {})
    layouts = times.get("layouts", {})
    link_cpu = per["Gen.Link"][1] + per["Gen other"][1]
    proof_mods = per["Proof"][0] + per["Spec"][0] + per["Table"][0] + per["Final"][0] + per["Model"][0]
    pre = regen.get("cpu", 0) + layouts.get("cpu", 0)
    row = [label, read(meta / "sha"), ch.group(1) if ch else "?", f"{per['Gen.Tmpl'][1]:.0f}", f"{link_cpu:.0f}",
           str(per["Proof"][0]), str(proof_mods), str(len(failed)), f"{pre:.0f}", f"{build.get('cpu', 0):.0f}",
           f"{total_cpu:.0f}", f"{pre + build.get('cpu', 0):.0f}",
           f"{regen.get('wall', 0) + layouts.get('wall', 0) + build.get('wall', 0):.0f}",
           f"{sweep_cpu:.0f}"]
    tsv = meta / "row.tsv"
    tsv.write_text("\t".join(row) + "\n", encoding="utf-8")
    md = [f"## {label}: {read(meta / 'title', label)}", "",
          f"Copy of `{read(meta / 'sha')}`; patch `{read(meta / 'patch')}` ({read(meta / 'patch-files')}).", "",
          f"**Binary.** {raw.group(0).strip() if raw else 'raw: ?'}; {mod_addr.group(0).strip() if mod_addr else ''}. "
          f"{tsummary}" + (f": {', '.join(changed[:12])}{', ...' if len(changed) > 12 else ''}" if changed else "")
          + ".", "",
          f"**Generation.** `regen.sh` {regen.get('cpu', 0):.0f} CPU-s / {regen.get('wall', 0):.0f} s, "
          f"`type-layouts.sh` {layouts.get('cpu', 0):.0f} CPU-s / {layouts.get('wall', 0):.0f} s"
          + (f" (Layouts.lean {read(meta / 'layouts-changed')})" if (meta / "layouts-changed").exists() else "")
          + ".", "",
          f"**Build** (`lake build Rv64mc`, {read(meta / 'jobs')} modules at once): {build.get('cpu', 0):.0f} CPU-s "
          f"(the `lean` processes {total_cpu:.0f}), {build.get('wall', 0):.0f} s wall, "
          f"exit {build.get('code', '?')}.", "",
          "| class | modules rebuilt | CPU-s |", "| --- | --- | --- |"]
    for cls in CLASSES:
        if per[cls][0] or per[cls][1]:
            md.append(f"| {cls} | {per[cls][0]} | {per[cls][1]:.0f} |")
    md.append("")
    rebuilt = sorted(m for cls in ("Model", "Spec", "Proof", "Table", "Final") for m in per[cls][2])
    if rebuilt:
        md += [f"Rebuilt proofs and specs: {', '.join(m.removeprefix('Rv64mc.') for m in rebuilt)}.", ""]
    if failed:
        md += ["**Failed:**", ""] + [f"- `{m}`: `{e}`" for m, e in failed] + [""]
    else:
        md += ["**Failed:** none.", ""]
    if sweep:
        md += [f"**Sweep** (`rv_sweep` on the changed templates): " + "; ".join(
            f"`{r[0]}` {float(r[2]):.1f} CPU-s ({r[1]})" for r in sweep) + ".", ""]
    (meta / "section.md").write_text("\n".join(md) + "\n", encoding="utf-8")
    print("\n".join(md))
    print("\t".join(row))


# Callees that do not return get a contract whose postcondition is False, every other one a contract promising nothing.
NORET = re.compile(r"^(handleError|panic.*|.*Fail.*|.*failed.*|assertFailed.*|sliceIndexFail|.*Overflow"
                   r"|capacityOverflow|halt|abort.*|unwrapFailed|expectFailed|oom.*|handleAllocError)$")


def sweep_probe(project: Path, mod: str) -> str:
    ns = "Rv64mc.Gen." + mod
    text = (project / "Rv64mc/Gen/Tmpl" / (mod.replace(".", "/") + ".lean")).read_text(encoding="utf-8")
    noret = [f for f in re.findall(r"^  ([A-Za-z0-9_]+) : Callee$", text, re.M) if NORET.match(f)]
    hyps = "".join(f"\n    (h_{f} : rvIsa.Contract p c L.{f}.idx (fun _ _ _ _ => True) (fun _ _ _ _ _ _ => False))"
                   for f in noret)
    using = ", ".join([f"h_{f}" for f in noret] + ["hspec"])
    return f"""import Rv64mc.Gen.Tmpl.{mod}
import Rv64mc.Tactic.Sym

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

set_option maxHeartbeats 4000000 in
theorem probe {{E : Type}} (c : Context rvIsa E) (p : Lprog (Op Reg) Reg) (L : {ns}.Link) (i : Nat)
    (hp : p[i]? = some ({ns}.tmpl L)) (hL : {ns}.Link.WF p L){hyps}
    (hspec : ∀ f, rvIsa.Contract p c f (fun _ _ _ _ => True) (fun _ _ _ _ _ _ => True)) :
    rvIsa.Contract p c i
      (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧ 0x10000#64 ≤ top ∧ top ≤ 0x7fffffffffffffff#64)
      (fun _ _ _ _ _ _ => True) := by
  rv_sweep hp with [hL] using [{using}]
  all_goals sorry
"""


def sweep(project: Path, meta: Path) -> None:
    mods = [l.split("\t")[1] for l in read(meta / "templates.txt").splitlines()
            if l.startswith(("changed\t", "added\t"))]
    out = meta / "sweep"
    out.mkdir(exist_ok=True)
    rows = []
    for mod in mods:
        src = out / (mod.replace(".", "_") + ".lean")
        src.write_text(sweep_probe(project, mod), encoding="utf-8")
        start = time.monotonic()
        with open(out / (src.stem + ".txt"), "wb") as log:
            child = subprocess.Popen(["timeout", "3600", "lake", "env", "lean", str(src)], cwd=project, stdout=log,
                                     stderr=subprocess.STDOUT)
            _, status, usage = os.wait4(child.pid, 0)
        code = os.waitstatus_to_exitcode(status)
        text = (out / (src.stem + ".txt")).read_text(encoding="utf-8", errors="replace")
        state = "ok" if code == 0 else "timeout" if code == 124 else f"failed: {first_error(text)}"
        rows.append(f"{mod}\t{state}\t{usage.ru_utime + usage.ru_stime:.1f}\t{time.monotonic() - start:.1f}\n")
    (meta / "sweep.tsv").write_text("".join(rows), encoding="utf-8")
    print("".join(rows), end="")


HEADER = ("label\tsha\ttemplates_changed\ttmpl_cpu_s\tlink_cpu_s\tproof_modules\tproof_spec_table_final_model_modules"
          "\tfailed_modules\tregen_layouts_cpu_s\tbuild_cpu_s\tlean_cpu_s\ttotal_cpu_s\ttotal_wall_s\tsweep_cpu_s\n")

if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "sysroot":
        sysroot(Path(sys.argv[2]))
    elif cmd == "wrap":
        wrap(sys.argv[2], sys.argv[3:])
    elif cmd == "report":
        report(Path(sys.argv[2]), sys.argv[3])
    elif cmd == "sweep":
        sweep(Path(sys.argv[2]), Path(sys.argv[3]))
    elif cmd == "header":
        sys.stdout.write(HEADER)
    else:
        sys.exit(__doc__)
