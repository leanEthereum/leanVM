/-
  LeanVM.Guest.B1.Da.BlobChk

  `da_verify_blob`'s body and `da_verify_blob_loop0`'s, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.BlobDefs
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem blob_ok : blobOk fn% «da_verify_blob» = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c_ok : cOk (coreProgram.getD idx% «da_verify_blob_loop0» default) = true := by decide +kernel

theorem find_da_verify_blob :
    coreProgram.find? name% «da_verify_blob» = some fn% «da_verify_blob» :=
  coreProgram_find?_at (j := idx% «da_verify_blob») rfl

set_option maxRecDepth 100000 in
theorem c_idx : coreProgram.indexOf? name% «da_verify_blob_loop0» = some idx% «da_verify_blob_loop0» :=
  coreProgram_indexOf?_at (j := idx% «da_verify_blob_loop0») rfl

theorem find_c : coreProgram.find? name% «da_verify_blob_loop0» =
    some (coreProgram.getD idx% «da_verify_blob_loop0» default) :=
  find_of_idx c_idx

end
end LeanVM.Guest.B1.Da
