import Lake
open Lake DSL

/-!
The root is no Lean project: `Statement`, `common`, `lean_vm`, `lean_xmss`, `lean_sphincs`,
`lean_da` and `extraction` are seven, each built in its own directory. `lake build` here runs `check-all.sh`, which builds and checks them
one after another as `.github/workflows/lean.yml` does.
-/

package leanerVM

/-- Every build and check of the seven projects; runs again on each `lake build`. -/
@[default_target]
target checkAll : Unit := Job.async do
  let child ← IO.Process.spawn {
    cmd := "bash", args := #[(__dir__ / "check-all.sh").toString], cwd := __dir__ }
  let code ← child.wait
  if code != 0 then
    error s!"check-all.sh failed with exit code {code}"
