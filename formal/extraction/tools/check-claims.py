#!/usr/bin/env python3
"""Check the axioms of every claim against claims.toml.

Ported from Plonky3-lean's tools/check-claims.py.

Lists every theorem in `Refinement.Claims` with the axioms it depends on (what
`#print axioms` reports) and requires the result to equal claims.toml exactly:
every claim has an entry, every entry names a claim, and each claim's axioms are
the ones its entry allows. A claim that starts to depend on `sorryAx`, or on the
`Lean.ofReduceBool` axiom that `native_decide` adds, therefore fails.

Run after `lake build`.

  tools/check-claims.py           check
  tools/check-claims.py --print   print the claims and their axioms as
                                  claims.toml entries, and check nothing
"""
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

LIST_CLAIMS = """\
import Refinement
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let theorems := env.constants.toList.filter fun (_, ci) => ci matches .thmInfo _
  let inClaims := theorems.filter fun (n, _) => (`Refinement.Claims).isPrefixOf n
  let names : NameSet := inClaims.foldl (fun s (n, _) => s.insert n) {}
  -- Fail closed: a theorem is skipped as auxiliary only when its name has an
  -- internal component (`_proof_1`, a number, ...) and a proper prefix of it is
  -- itself a claim, as for `X.holds._proof_1`. Every other theorem in
  -- `Refinement.Claims` is a claim, including one about an item aeneas names
  -- `_` or `__1`.
  let internal (n : Name) : Bool := n.components.any fun
    | .str _ s => s.startsWith "_" && s != "_"
    | _ => true
  let rec underClaim : Name → Bool
    | .anonymous => false
    | p@(.str q _) | p@(.num q _) => names.contains p || underClaim q
  let aux (n : Name) : Bool := internal n && underClaim n.getPrefix
  -- A `private` theorem is named `_private.<module>.0.<name>`. One in
  -- `Refinement.Claims` reads as a claim, so it is reported, and rejected,
  -- unless it is auxiliary to a claim by the rule above: in a module, Lean makes
  -- a claim's `_proof_1` private.
  for (n, _) in theorems do
    if let some u := privateToUserName? n then
      if (`Refinement.Claims).isPrefixOf u && !aux u then
        IO.println s!"PRIVATE\\t{u}"
  let claims := inClaims.filter fun (n, _) => !aux n
  for (n, _) in claims.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let axs ← liftCoreM (Lean.collectAxioms n)
    let axs := axs.qsort (fun a b => a.toString < b.toString)
    IO.println s!"{n}\\t{String.intercalate "," (axs.toList.map toString)}"
"""


def actual():
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(LIST_CLAIMS)
    try:
        r = subprocess.run(["lake", "env", "lean", f.name], cwd=ROOT, text=True,
                           capture_output=True)
    finally:
        Path(f.name).unlink()
    if r.returncode != 0:
        sys.exit(f"error: listing the claims failed (run `lake build` first?):\n{r.stdout}{r.stderr}")
    out, private = {}, []
    for line in r.stdout.splitlines():
        name, _, axs = line.partition("\t")
        if name == "PRIVATE":
            private.append(axs)
            continue
        out[name] = sorted(a for a in axs.split(",") if a)
    return out, private


def main(argv):
    claims, private = actual()
    if argv == ["--print"]:
        for name, axs in claims.items():
            print("[[claim]]")
            print(f'name   = "{name}"')
            print("axioms = [" + ", ".join(f'"{a}"' for a in axs) + "]")
            print()
        return
    if argv:
        sys.exit(__doc__)
    allowed = {c["name"]: sorted(c["axioms"])
               for c in tomllib.loads((ROOT / "claims.toml").read_text()).get("claim", [])}
    fail = False
    for name in private:
        print(f"FAIL: {name} is a private theorem in Refinement.Claims; a claim must be public")
        fail = True
    for name, axs in claims.items():
        if name not in allowed:
            print(f"FAIL: {name} is a claim with no claims.toml entry (axioms: {axs})")
            fail = True
        elif axs != allowed[name]:
            print(f"FAIL: {name} depends on {axs}; claims.toml allows {allowed[name]}")
            fail = True
    for name in allowed:
        if name not in claims:
            print(f"FAIL: claims.toml names {name}, which is not a theorem in Refinement.Claims")
            fail = True
    if fail:
        sys.exit(1)
    print(f"check-claims: {len(claims)} claim(s), each with exactly the axioms claims.toml allows")


if __name__ == "__main__":
    main(sys.argv[1:])
