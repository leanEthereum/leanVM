/-
  LeanVM.Guest.B1.Digest.ClaimListCBig

  `claim_list_digest`'s big frame loop `__loop15` (136 claims, 64 blocks), evaluated (by kernel
  evaluation), for its completeness: `grpcOk`'s parts, each a kernel check of its own.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCBig1
public import LeanVM.Guest.B1.Digest.ClaimListCBig2
public import LeanVM.Guest.B1.Digest.ClaimListCBig4
public import LeanVM.Guest.B1.Digest.ClaimListCBig5

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

@[expose] public section

theorem grpc_big : grpcOk (coreProgram.getD 359 default) "__loop15" 136 21 565 20 = true := by
  have h1 := big_c1
  have h2 := big_c2
  have h4 := big_c4
  have h5 := big_c5
  simp only [bigF, bigS, bigCSpec, bigFn, Bool.and_eq_true] at h1 h2 h4 h5
  simp only [grpcOk, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h1.1.1.1, h1.1.1.2⟩, h1.1.2⟩, h1.2⟩, h2⟩, h4⟩, h5.1.1⟩, h5.1.2⟩, h5.2⟩

end
end LeanVM.Guest.B1.Digest
