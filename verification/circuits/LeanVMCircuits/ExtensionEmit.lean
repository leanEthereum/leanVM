module

public import LeanVMCircuits.ExtensionProduct

@[expose] public section

/-! Emit only the proved EXT identity shape, with explicit errors for unsupported columns or coefficients. -/

namespace LeanVMCircuits.ExtensionProduct.Emit

/-- Bind a logical source column to its production table column. -/
def column (c : ℕ) : Except String String :=
  if c = 0 then .ok "accumulate"
  else if c < 10 then .ok (if c = 1 then "limbs" else s!"limbs + {c - 1}")
  else if c < 13 then .ok (if c = 10 then "new" else s!"new + {c - 10}")
  else .error s!"unsupported EXT identity column {c}"

def identity (id : Rec.Identity) (i : ℕ) : Except String String := do
  let [(output, coefficient)] := id.linear | throw "EXT identity must have exactly one linear output"
  unless output = 10 + i ∧ coefficient = 1 do throw "unsupported EXT identity linear term"
  let output ← column output
  let products ← id.prods.mapM fun (a, b, w) => do
    unless w = 1 do throw "unsupported EXT identity product coefficient"
    return s!"({← column a}, {← column b}, F192::ONE)"
  return s!"    let mut f{i} = BusForm::new(n_columns, F192::ZERO);\n" ++
    s!"    f{i}.coeffs[{output}] = F192::ONE;\n" ++
    s!"    f{i}.prods = vec![" ++ String.intercalate ", " products ++ "];\n"

/-- Emit the EXT function from the same `rows` used by the Clean source and its soundness theorem. -/
def emit : Except String String := do
  unless rows.length = 3 do throw "EXT must have exactly three limb identities"
  let forms ← rows.zipIdx.mapM fun (id, i) => identity id i
  return "/// EXT's three committed field identities, bound to the table's local columns.\n" ++
    "pub(crate) fn extension_identities(n_columns: usize, accumulate: usize, limbs: usize, new: usize) -> Vec<BusForm> {\n" ++
    String.join forms ++ "    vec![f0, f1, f2]\n}\n"

end LeanVMCircuits.ExtensionProduct.Emit
