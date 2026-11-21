module

public import LeanVM.Guest.Fast.FunctionNames
public import LeanVM.Guest.B1.Da.Verify
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify»

/-!
# `da_verify`'s witness reader, its frames numbered

`dvWit σ Vm` (`B1/Da/Verify.lean`) reads the DA matrix off `da_verify`'s callees' frames, which it
names by string literals (the blob loop, `"da_verify_blob"`, its cell loop, `"da_verify_cell"`). `dvWitN σ Vn`
reads the same frames by the functions' indices (`fn_idx%`, `Guest/CoreRef.lean`);
`dvWitN_eq`: at `Vn k = Vm (decoderFunctionName k)` they are equal.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Da LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main

@[expose] public section

/-- Blob `i`'s iteration of the blob loop (`da_verify_loop0`), its valuation (`dvBlobV`). -/
def dvBlobLVN (σ : Val) (Vn : NFrames) (i : ℕ) : Val :=
  Vn (fn_idx% da_verify_loop0) [gen ^ i, σ (.n (val% «da_verify» "n_blob_g")), σ (.n (val% «da_verify» "weights")), σ (.n (val% «da_verify» "roots"))] []

/-- Blob `i`'s valuation (`da_verify_blob`, `blobV`). -/
def dvBlobVN (σ : Val) (Vn : NFrames) (i : ℕ) : Val :=
  Vn (fn_idx% da_verify_blob) [σ (.n 8)] [dvBlobLVN σ Vn i (.n 4), dvBlobLVN σ Vn i (.n 5)]

/-- Cell `h`'s iteration of blob `i`'s cell loop (`da_verify_blob_loop0`, `blobCellV`). -/
def dvCellVN (σ : Val) (Vn : NFrames) (i h : ℕ) : Val :=
  Vn (fn_idx% da_verify_blob_loop0) [gen ^ h, σ (.n 8), dvBlobVN σ Vn i (.n 1)] []

/-- The symbols, padded outside the matrix (`dvSymsP`), the cell check function's. -/
noncomputable def dvSymsPN (σ : Val) (Vn : NFrames) (i h : ℕ) : List E :=
  if i < dvRows σ ∧ h < 128 then
    cellSymsOf (Vn (fn_idx% da_verify_cell) [dvCellVN σ Vn i h (.n 4)]
      [dvCellVN σ Vn i h (.n 5), dvCellVN σ Vn i h (.n 6), dvCellVN σ Vn i h (.n 7)])
  else List.replicate 128 0

/-- **`da_verify`'s witness** (`dvWit`), its frames numbered. -/
noncomputable def dvWitN (σ : Val) (Vn : NFrames) : LeanVM.Da.MatrixWitness :=
  ⟨daRows (dvRows σ) (dvSymsPN σ Vn)⟩

/-- **The readers are equal.** -/
theorem dvWitN_eq (σ : Val) (Vm : FrameMap) :
    dvWitN σ (fun k ↦ Vm (decoderFunctionName k)) = dvWit σ Vm := by
  unfold dvWitN dvWit dvSymsPN dvSymsP dvSyms blobSyms blobCellV blobV dvBlobV dvCellVN dvBlobVN dvBlobLVN
  simp only [name_da_verify_loop0, name_da_verify_blob, name_da_blob_loop, name_da_verify_cell]

end
end LeanVM.Guest.Fast
