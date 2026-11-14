module

public import LeanVM.Guest.Fast.FunctionNames
public import LeanVM.Guest.B1.Da.Verify

/-!
# `da_verify`'s witness reader, its frames numbered

`dvWit σ Vm` (`B1/Da/Verify.lean`) reads the DA matrix off `da_verify`'s callees' frames, which it
names by string literals (`"da_verify_column"`, `"__loop25"`, `"da_verify_cell"`). `dvWitN σ Vn`
reads the same frames by the functions' indices (`fn_idx%`, `Guest/CoreRef.lean`);
`dvWitN_eq`: at `Vn k = Vm (decoderFunctionName k)` they are equal.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Da LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main

@[expose] public section

/-- Column `h`'s valuation (`da_verify_column`). -/
def dvColVN (σ : Val) (Vn : NFrames) (h : ℕ) : Val := Vn (fn_idx% da_verify_column) (dvColArgs σ h) []

/-- Blob `i`'s iteration of column `h`'s blob loop (`da_verify_column_loop0`), its valuation
(`colRowV`). -/
def dvRowVN (σ : Val) (Vn : NFrames) (i h : ℕ) : Val :=
  Vn (fn_idx% da_verify_column_loop0) [gen ^ i, σ (.n 1), dvColVN σ Vn h (.n 14), σ (.n 22), gen ^ h, dvColVN σ Vn h (.n 15)] []

/-- The symbols, padded outside the matrix (`dvSymsP`), the cell check function's. -/
noncomputable def dvSymsPN (σ : Val) (Vn : NFrames) (i h : ℕ) : List E :=
  if i < dvRows σ ∧ h < 128 then
    cellSymsOf (Vn (fn_idx% da_verify_cell) [dvColVN σ Vn h (.n 14)]
      [dvRowVN σ Vn i h (.n 6), dvRowVN σ Vn i h (.n 7), dvRowVN σ Vn i h (.n 8)])
  else List.replicate 128 0

/-- **`da_verify`'s witness** (`dvWit`), its frames numbered. -/
noncomputable def dvWitN (σ : Val) (Vn : NFrames) : LeanVM.Da.MatrixWitness :=
  ⟨daRows (dvRows σ) (dvSymsPN σ Vn)⟩

/-- **The readers are equal.** -/
theorem dvWitN_eq (σ : Val) (Vm : FrameMap) :
    dvWitN σ (fun k ↦ Vm (decoderFunctionName k)) = dvWit σ Vm := by
  unfold dvWitN dvWit dvSymsPN dvSymsP dvSyms colSyms colRowV dvRowVN dvColVN
  simp only [name_da_verify_column, name_da_blob_loop, name_da_verify_cell, dvColArgs, List.getD_cons_succ,
    List.getD_cons_zero]

end
end LeanVM.Guest.Fast
