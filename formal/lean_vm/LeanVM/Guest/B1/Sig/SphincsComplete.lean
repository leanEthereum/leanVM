/-
  LeanVM.Guest.B1.Sig.SphincsComplete

  `verify_sig_lean_sphincs` (`lean_ethereum.py:4143-4244`) is complete, loading
  only the claim and the byte table (`verify_sig_lean_sphincs_complete_loads_of`), given its
  blocks' completeness (`SphincsBlocksComplete`).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsTopComplete
public import LeanVM.Guest.B1.Sig.SphincsData
public import LeanVM.Guest.B1.Sig.SphincsLoads

/-!
# `verify_sig_lean_sphincs`, complete

`G` is `lean_ethereum.py`. The body (`sBody_splitC`) is the statements before the root's check
(`sPre`): the digest and FORS (`sBottom_complete`), the bottom layer, the middle layer's address
(`sMidAddrs_vals`), the middle layer, the top layer's address (`sTopAddrs_vals`) and the top layer
(`layer_stage`); then `root[0] == pk_root` (`G:4243`) and the return. The statement's verification
by stages (`verifyWithKeccak_iff_stages`) gives each layer's root from the one below, the FORS key
at the bottom (`sForsKeyOf_eq`), the key's root at the top. The loads are the claim's and the byte
table's (`listLoadsB` of `loadPtrs sPre`, `sBody_loads`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)
open LeanVM.Protocol.KeccakHash

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The body's stages -/

/-- The statements before the root's check. -/
def sPre : List Stmt :=
  (sDigestBlock ++ (sForsAddrs ++ sForsB.1)) ++
    (sLayerB.1 ++ (sMidAddrs ++ (sLayerM.1 ++ (sTopAddrs ++ sLayerT.1))))

theorem sBody_splitC : sBody = sPre ++ [.atom (.assertEq sLayerT.2.2 sRoot), .ret []] := by
  simp only [sBody, sAfterDigest, sPre, List.append_assoc]

theorem sMidAddrs_seq : SeqOK 5398 sMidAddrs 5407 := seqB_ok (by decide +kernel)
theorem sTopAddrs_seq : SeqOK 5556 sTopAddrs 5562 := seqB_ok (by decide +kernel)
theorem sBottom_nb : NumBelow 5249 (Stmt.valsList (sDigestBlock ++ (sForsAddrs ++ sForsB.1))) :=
  numBelow_of_all (by decide +kernel)
theorem sLayerB_nb : NumBelow 5398 (Stmt.valsList sLayerB.1) := numBelow_of_all (by decide +kernel)
theorem sLayerM_nb : NumBelow 5556 (Stmt.valsList sLayerM.1) := numBelow_of_all (by decide +kernel)
theorem sLayerT_le : 5562 ≤ sLayerT.2.1 := by decide +kernel
theorem sLayerB_rootC : ∃ k < 5398, sLayerB.2.2 = .n k := ⟨(sLayerB.2.2).idx, by decide +kernel, by decide +kernel⟩
theorem sLayerM_rootC : ∃ k < 5556, sLayerM.2.2 = .n k := ⟨(sLayerM.2.2).idx, by decide +kernel, by decide +kernel⟩
theorem sAfterDigest_ptrs : loadPtrs (sForsAddrs ++ sForsB.1) = [] ∧ loadPtrs sMidAddrs = [] ∧
    loadPtrs sTopAddrs = [] := by decide +kernel
theorem sLayerB_ptrs : ∀ q ∈ loadPtrs sLayerB.1, q < 5398 := by decide +kernel
theorem sLayerM_ptrs : ∀ q ∈ loadPtrs sLayerM.1, q < 5556 := by decide +kernel

/-- **The body's loads**: through the claim's `n0` at an offset below `4`, or through a pointer of
`sPre`'s byte reads. -/
theorem sBody_loads : listLoadsB (loadPtrs sPre) (Fn.«verify_sig_lean_sphincs».core).body = true := by
  rw [sBody_eq]; decide +kernel

/-! ## The stages, complete -/

/-- **The statements before the root's check complete**, for a claim of `pk` and `m` at `n0`
signed by `sig`, the byte table at `n1`: the top layer reaches the key's root, and the byte reads
are the table's. -/
theorem sPre_complete (hB : SphincsBlocksComplete) (hC : SpWotsCalls C) (hm : MemOK rd 256)
    {bb : E} (hbb : ByteBits rd bb) (pk : Sphincs.PublicKey) (m : HashSig.Message)
    (sig : Sphincs.Signature) (hv : Sphincs.verifyWithKeccak pk m sig = true) (σ : Val)
    (h1 : σ (.n 1) = bb)
    (hat : ClaimAt rd (σ (.n 0)) (cellOf128 pk.publicSeed) (cellOf128 pk.root) (msgLo m) (msgHi m)) :
    Completes C rd 2 sLayerT.2.1 sPre σ (fun σ' => σ' sLayerT.2.2 = cellOf128 pk.root ∧
      σ' sRoot = cellOf128 pk.root ∧ TablePtrs bb σ' sPre) := by
  obtain ⟨r0, r1, h0, h1', h2⟩ := (verifyWithKeccak_iff_stages pk m sig).mp hv
  rw [sForsKeyOf_eq] at h0
  have hT8 := sLayerT_le
  unfold sPre
  refine Completes.append (m := 5249) (by norm_num) (by omega) sBottom_nb
    (sBottom_complete hB hm hbb pk m sig σ h1 hat) (fun σA heA hA => ?_)
  have hA1 : σA (.n 1) = bb := by rw [heA.apply (Or.inl (by norm_num))]; exact h1
  -- the bottom layer
  obtain ⟨hr0, hL0⟩ := layer_stage hB hC hm hbb (l := 0) (by norm_num) h0
    σA hA1 hA hA.2.2.2.2.2.1 hA.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2
  set R0 := layerRootCell pk (digestIdx pk m sig) sig ⟨0, by decide⟩ (forsKeyCell pk m sig)
    with hR0d
  refine Completes.append (m := 5398) (by norm_num) (by omega) sLayerB_nb hL0
    (fun σB heB ⟨hB0, hBp⟩ => ?_)
  have tB : ∀ k < 5249, σB (.n k) = σA (.n k) := fun k hk => heB.apply (Or.inl hk)
  -- the middle layer's address
  refine Completes.seq sMidAddrs_seq (by omega) (fun σC heC hAtC => ?_)
  have tC : ∀ k < 5398, σC (.n k) = σB (.n k) := fun k hk => heC.apply (Or.inl hk)
  have tCA : ∀ k < 5249, σC (.n k) = σA (.n k) := fun k hk => by rw [tC k (by omega), tB k hk]
  have hAC := hA.congr tCA
  obtain ⟨ha0C, ha1C⟩ := sMidAddrs_vals hAC.2.2.2.1.2.2.2.1 hAC.2.2.2.1.2.2.2.2 hAtC
  have hsC : σC (sSignedOf 1) = R0 := by
    obtain ⟨k, hk, ek⟩ := sLayerB_rootC
    show σC sLayerB.2.2 = R0
    rw [ek, tC k hk, ← ek]; exact hB0
  -- the middle layer
  rw [hr0] at h1'
  obtain ⟨hr1, hL1⟩ := layer_stage hB hC hm hbb (l := 1) (by norm_num) h1'
    σC (by rw [tCA 1 (by norm_num)]; exact hA1) hAC ha0C ha1C hsC
  set R1 := layerRootCell pk (digestIdx pk m sig) sig ⟨1, by decide⟩ R0 with hR1d
  refine Completes.append (m := 5556) (by norm_num) (by omega) sLayerM_nb hL1
    (fun σD heD ⟨hD1, hDp⟩ => ?_)
  have tD : ∀ k < 5407, σD (.n k) = σC (.n k) := fun k hk => heD.apply (Or.inl hk)
  -- the top layer's address
  refine Completes.seq sTopAddrs_seq (by omega) (fun σE heE hAtE => ?_)
  have tE : ∀ k < 5556, σE (.n k) = σD (.n k) := fun k hk => heE.apply (Or.inl hk)
  have tEC : ∀ k < 5407, σE (.n k) = σC (.n k) := fun k hk => by rw [tE k (by omega), tD k hk]
  have tEA : ∀ k < 5249, σE (.n k) = σA (.n k) := fun k hk => by rw [tEC k (by omega), tCA k hk]
  have hAE := hA.congr tEA
  obtain ⟨ha0E, ha1E⟩ := sTopAddrs_vals hAE.2.2.2.1.2.2.2.1 hAE.2.2.2.1.2.2.2.2 hAtE
  have hsE : σE (sSignedOf 2) = R1 := by
    obtain ⟨k, hk, ek⟩ := sLayerM_rootC
    show σE sLayerM.2.2 = R1
    rw [ek, tE k hk, ← ek]; exact hD1
  -- the top layer
  rw [hr1] at h2
  obtain ⟨hr2, hL2⟩ := layer_stage hB hC hm hbb (l := 2) (by norm_num) h2
    σE (by rw [tEA 1 (by norm_num)]; exact hA1) hAE ha0E ha1E hsE
  have hR2 : layerRootCell pk (digestIdx pk m sig) sig ⟨2, by decide⟩ R1 = cellOf128 pk.root := by
    rw [hr2, cellOf128_cellVal]
  obtain ⟨σF, heF, ⟨hF2, hFp⟩, hhF⟩ := hL2
  have tF : ∀ k < 5562, σF (.n k) = σE (.n k) := fun k hk => heF.apply (Or.inl hk)
  have tFA : ∀ k < 5249, σF (.n k) = σA (.n k) := fun k hk => by rw [tF k (by omega), tEA k hk]
  have tFB : ∀ k < 5398, σF (.n k) = σB (.n k) := fun k hk => by
    rw [tF k (by omega), tE k (by omega), tD k (by omega), tC k hk]
  have tFD : ∀ k < 5556, σF (.n k) = σD (.n k) := fun k hk => by rw [tF k (by omega), tE k hk]
  obtain ⟨-, -, hrA, -, hqA, -⟩ := hA
  refine ⟨σF, heF, ⟨hF2.trans hR2, by rw [show sRoot = .n 3 from rfl, tFA 3 (by norm_num)]; exact hrA,
    ?_⟩, hhF⟩
  refine TablePtrs.append (TablePtrs.append (hqA.congr sDigestBlock_ptrs fun k hk => tFA k (by omega))
    (TablePtrs.nil_of sAfterDigest_ptrs.1)) ?_
  refine TablePtrs.append (hBp.congr sLayerB_ptrs tFB) (TablePtrs.append
    (TablePtrs.nil_of sAfterDigest_ptrs.2.1) (TablePtrs.append (hDp.congr sLayerM_ptrs tFD)
      (TablePtrs.append (TablePtrs.nil_of sAfterDigest_ptrs.2.2) hFp)))

/-- **`verify_sig_lean_sphincs` is complete, loading the claim and the byte table**, given its
blocks' completeness. -/
theorem verify_sig_lean_sphincs_complete_loads_of (hB : SphincsBlocksComplete) :
    verify_sig_lean_sphincs_complete_loads_Spec := by
  intro C rd p bb pk m sig hC hm hbb hat hv
  let σ0 : Val := Function.update (Function.update (fun _ => (0 : E)) (.n 0) p) (.n 1) bb
  have e0 : σ0 (.n 0) = p := by
    simp only [σ0]
    rw [Function.update_of_ne (by simp), Function.update_self]
  have e1 : σ0 (.n 1) = bb := Function.update_self ..
  obtain ⟨σf, hef, ⟨hroot, hrt, hptrs⟩, hhf⟩ :=
    sPre_complete hB hC hm hbb pk m sig hv σ0 e1 (by rw [e0]; exact hat)
  have f0 : σf (.n 0) = p := by rw [hef.apply (Or.inl (by norm_num))]; exact e0
  have f1 : σf (.n 1) = bb := by rw [hef.apply (Or.inl (by norm_num))]; exact e1
  refine ⟨σf, f0, f1, ?_, ?_⟩
  · rw [sBody_eq, sBody_splitC, holdsList_append]
    refine hhf _ _ ⟨?_, rfl⟩
    show σf sLayerT.2.2 + σf sRoot = 0
    rw [hroot, hrt]; exact e_add_self _
  · intro es vs hw A hA
    have hok := loads_of_walk sBody_loads hw
    rcases loadAddrs_of_loadOk hok A hA with ⟨k, hk, e⟩ | ⟨q, hq, e⟩
    · exact Or.inl ⟨k, hk, by rw [e, f0]⟩
    · obtain ⟨v, hv256, ev⟩ := hptrs q hq
      exact Or.inr ⟨v, hv256, by rw [e, ev, limb_mul_ofK (hbb 0 (by norm_num)).1]⟩

end
end LeanVM.Guest.B1.Sig
