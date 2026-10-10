#!/usr/bin/env python3
"""Make Aeneas's translation of the guest's three closures type-check: five rewrites, nothing else.

Aeneas's model of the `FnOnce` and `FnMut` traits has no room for what a closure gives back besides its output: the
final value of a mutable borrow it takes as an argument or captures (Aeneas issues #1046 and #961). It translates
each closure body correctly, with those final values as extra results, but then declares its trait instance with the
trait's types, which do not match. Each rewrite below routes the extra results, and fails if its target is not found
exactly once:

1. `tweak_hash`'s closure writes the `&mut Stream` it is given: its instance's output becomes the final stream, which
   the model of `hash_with` hashes (see `FunsExternal.lean`).
2. `wots_leaf`'s closure does the same, and also gives back its own state, which holds the `&mut` capture of `end`:
   its instance's output becomes both, as the translated `wots_leaf` already destructures them.
3. `verify`'s closure as `FnOnce`: `call_once` consumes the closure, so the state it gives back is dropped.
4. `verify`'s closure as `FnMut`: `call_mut` gives back the closure's next state, and a function that ends the nested
   borrow of its capture `chains` on it; the instance returns that function applied to that state, which is what the
   caller's borrow ends with.
5. `verify` calls `wots_leaf` with that closure, whose type holds a mutable borrow, and so destructures the result as
   if `wots_leaf` gave the closure's final state back too, which `wots_leaf`'s translation does not (Aeneas issue
   #961): `verify` takes the result whole, the closure's final state being unused (`chains` is dropped after).
"""

import re
import sys

REWRITES = [
    (
        r"core\.ops\.function\.FnOnce\s+\(tweak_hash\.closure N\)\s+leanvm_guest\.Stream\s+Unit\s+:= \{",
        "core.ops.function.FnOnce (tweak_hash.closure N)\n  leanvm_guest.Stream leanvm_guest.Stream := {",
    ),
    (
        r"core\.ops\.function\.FnOnce\s+\(wots_leaf\.closure T0\)\s+leanvm_guest\.Stream\s+Unit\s+:= \{",
        "core.ops.function.FnOnce (wots_leaf.closure T0)\n"
        "  leanvm_guest.Stream ((wots_leaf.closure T0) × leanvm_guest.Stream) := {",
    ),
    (
        r"call_once :=\s+verify\.closure\.Insts\.CoreOpsFunctionFnOnceTupleUsizeArrayU642\.call_once\s*\}",
        "call_once := fun c i => do\n"
        "    let (a, _) ← verify.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU642.call_once c i\n"
        "    ok a\n"
        "}",
    ),
    (
        r"call_mut :=\s+verify\.closure\.Insts\.CoreOpsFunctionFnMutTupleUsizeArrayU642\.call_mut\s*\}",
        "call_mut := fun c i => do\n"
        "    let (a, c1, back) ← verify.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU642.call_mut c i\n"
        "    ok (a, back c1)\n"
        "}",
    ),
    (
        r"let \(leaf, _\) ←\s+wots_leaf verify\.closure",
        "let leaf ←\n      wots_leaf verify.closure",
    ),
]


def main() -> None:
    path = sys.argv[1]
    with open(path, encoding="utf-8") as f:
        text = f.read()
    for pattern, replacement in REWRITES:
        text, n = re.subn(pattern, replacement, text)
        if n != 1:
            sys.exit(f"patch_closures: {pattern!r} matched {n} times, not once: the translation changed")
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


if __name__ == "__main__":
    main()
