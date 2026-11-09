#!/usr/bin/env python3
"""Where a Lean file's build time goes: its declarations, and in each the steps that cost.

  python3 -I tools/profile.py FILE [N]    the N costliest declarations of FILE (default 8)

FILE is checked with `lake env lean` in its project, from the built dependencies (build them
first), one declaration after another (`Elab.async=false`: with it on, the profiler's times
overlap) under Lean's profiler. For each costly declaration, the steps whose own time (not their
sub-steps') is largest: the tactic, unification (`Meta.isDefEq`, `whnf`), instance search or kernel
check where a fix applies. What usually helps, by what the step is:

* `decide`, `decide +kernel` on lists: a quadratic or structural check (`Nodup`, `∉` through a
  derived `DecidableEq`): decide it by numbers, a linear pass (`List.IsChain (· < ·)`, a `Bool`
  comparing fields, a faster `Decidable` instance).
* `show`, `rfl`, `exact` with `isDefEq`/`whnf` under it: unification unfolding a definition to
  match two heads; rewrite the goal to the same head first (`List.getD_cons_zero`, a lemma).
* `simp`, `split_ifs`, `omega`, `tauto` in a long proof: they read the whole context; prove the
  fact as a lemma outside (in an empty context), or `clear * - h` first.
* the kernel check of a declaration (`typechecking declarations`): a large term; split it.
"""
import os
import re
import resource
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LINE = re.compile(r"^( *)\[([\w.]+)\] \[([\d.]+)\] \S+ ?(.*)$")
NOISE = re.compile(r"^(focus|with_annotate_state.*|case body.*|refine_lift|\(|·|)$")


def project_of(path):
    d = os.path.dirname(os.path.abspath(path))
    while d.startswith(ROOT) and d != ROOT:
        if any(os.path.exists(os.path.join(d, f)) for f in ("lakefile.toml", "lakefile.lean")):
            return d
        d = os.path.dirname(d)
    sys.exit(f"{path}: not in a Lake project of {ROOT}")


class Node:
    def __init__(self, cls, secs, text, depth):
        self.cls, self.secs, self.text, self.depth, self.kids = cls, secs, text, depth, []

    def own(self):
        return self.secs - sum(k.secs for k in self.kids)

    def walk(self):
        yield self
        for k in self.kids:
            yield from k.walk()


def parse(out):
    """The profiler's tree: one line a node, two spaces a level, a node's first text line."""
    roots, stack = [], []
    for line in out.splitlines():
        m = LINE.match(line)
        if not m:
            continue
        n = Node(m.group(2), float(m.group(3)), m.group(4).strip(), len(m.group(1)) // 2)
        while stack and stack[-1].depth >= n.depth:
            stack.pop()
        (stack[-1].kids if stack else roots).append(n)
        stack.append(n)
    return roots


def proof_steps(node):
    """A proof's steps at its outermost level: the tactic block's own steps, looking through the
    wrappers the profiler adds (`focus`, a sequence's unnamed node)."""
    for k in node.kids:
        if k.cls == "Elab.step" and NOISE.match(k.text):
            yield from proof_steps(k)
        elif k.cls == "Elab.step":
            yield k


def name_of(cmd):
    """A command's declaration: its `Elab.definition.value` node, else its first words."""
    for n in cmd.walk():
        if n.cls == "Elab.definition.value":
            return n.text
    for n in cmd.walk():
        m = re.search(r"declarations \[([^\]]+)\]", n.text)
        if m:
            return m.group(1)
    return cmd.text[:80] or "(command)"


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    path, top = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 8
    proj = project_of(path)
    cap = int(os.environ.get("LEAN_VMEM_KB", "40000000")) * 1024
    cmd = ["lake", "env", "lean", "-DElab.async=false", "-Dtrace.profiler=true",
           "-Dtrace.profiler.threshold=50", os.path.relpath(os.path.abspath(path), proj)]
    r = subprocess.run(cmd, cwd=proj, capture_output=True, text=True,
                       preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_AS, (cap, cap)))
    use = resource.getrusage(resource.RUSAGE_CHILDREN)
    errors = [l for l in (r.stdout + r.stderr).splitlines() if ": error" in l]
    # a `set_option … in` or `variable … in` wrapper is reported beside what it wraps: skip it
    cmds = [n for n in parse(r.stdout) if n.cls == "Elab.command" and
            (n.kids or not n.text.startswith(("set_option", "variable")))]
    print(f"{path}: {use.ru_utime + use.ru_stime:.1f} CPU-s, peak {use.ru_maxrss // 1024} MB, "
          f"{len(cmds)} commands over 50 ms")
    for e in errors[:5]:
        print("  " + e)
    # a `set_option … in` wraps its declaration: count each declaration once, by its name
    best = {}
    for c in cmds:
        k = name_of(c)
        if k not in best or c.secs > best[k].secs:
            best[k] = c
    for c in sorted(best.values(), key=lambda c: -c.secs)[:top]:
        print(f"\n{c.secs:7.1f} s  {name_of(c)}")
        steps = [n for n in c.walk() if n is not c and not NOISE.match(n.text)]
        for n in sorted(steps, key=lambda n: -n.own())[:4]:
            if n.own() < max(0.2, 0.05 * c.secs):
                break
            print(f"  {n.own():6.1f} s  {n.cls}: {n.text[:100]}")
        # a proof whose time is spread: its own steps, by their whole time
        body = [n for n in c.walk() if n.cls == "Elab.definition.value"]
        if body:
            parts = sorted(proof_steps(body[0]), key=lambda n: -n.secs)
            if parts and parts[0].secs >= max(0.5, 0.1 * c.secs):
                print("  the proof's steps, by their whole time:")
                for n in parts[:5]:
                    print(f"  {n.secs:6.1f} s  {n.text[:100]}")


if __name__ == "__main__":
    main()
