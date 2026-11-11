/-
  The list decoder's parameters at every shape `(μ, R)`, `15 ≤ μ ≤ 28`, `1 ≤ R ≤ 4`, as the
  extractor computes them (`LeanVM/Protocol/Extraction/Extractor.lean`): the input of `cost.py`.
  `cd lean_vm && lake env lean scripts/extractor-cost/params.lean > params.csv`
-/
import LeanVM.Protocol.Extraction.Extractor
open LeanVM.Extraction LeanVM.Parameters.Whir
def row (μ R : ℕ) : String :=
  let κ := μ - initialFold
  let k := 2 ^ κ + initialFold
  let n := 2 ^ (κ + R)
  let A := johnsonThreshold μ R
  let m := gsMultiplicityAt k n A
  let W := m * A - 1
  let ℓ := W / (k - 1)
  s!"{μ},{R},{κ},{n},{A},{m},{ℓ},{gsNumConstraints n m},{gsNumVars k W}"
#eval IO.println "mu,R,kappa,n,A,m,ell,conditions,vars"
#eval do for μ in List.range' 15 14 do for R in List.range' 1 4 do IO.println (row μ R)
