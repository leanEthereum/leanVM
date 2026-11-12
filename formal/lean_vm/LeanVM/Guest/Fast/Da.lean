module

public import LeanVM.Guest.Fast.FunctionIdx
public import LeanVM.Guest.B1.Da.Verify

/-!
# `da_verify`'s witness reader, its frames numbered

`dvWit σ Vm` (`B1/Da/Verify.lean`) reads the DA matrix off `da_verify`'s callees' frames, which it
names by string literals (`"da_verify_column"`, `"__loop25"`, `"da_verify_cell"`). `dvWitN σ Vn`
reads the same frames by the functions' indices (`Fast/FunctionIdx.lean`: `30`, `420`, `31`);
`dvWitN_eq`: at `Vn k = Vm (decoderFunctionName k)` they are equal.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Da LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main

@[expose] public section

/-- Column `h`'s valuation (`da_verify_column`, function `30`). -/
def dvColVN (σ : Val) (Vn : NFrames) (h : ℕ) : Val := Vn 30 (dvColArgs σ h) []

/-- Blob `i`'s iteration of column `h`'s blob loop (`__loop25`, function `420`), its valuation
(`colRowV`). -/
def dvRowVN (σ : Val) (Vn : NFrames) (i h : ℕ) : Val :=
  Vn 420 [gen ^ i, σ (.n 1), dvColVN σ Vn h (.n 13), σ (.n 22), gen ^ h, dvColVN σ Vn h (.n 14)] []

/-- The symbols, padded outside the matrix (`dvSymsP`), the cell check function `31`'s. -/
noncomputable def dvSymsPN (σ : Val) (Vn : NFrames) (i h : ℕ) : List K :=
  if i < dvRows σ ∧ h < 128 then
    cellSymsOf (Vn 31 [dvColVN σ Vn h (.n 13)]
      [dvRowVN σ Vn i h (.n 6), dvRowVN σ Vn i h (.n 7), dvRowVN σ Vn i h (.n 8)])
  else List.replicate 256 0

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
