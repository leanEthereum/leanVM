/-
  LeanVM.Guest.B1.Sig.SphincsBottomComplete

  The first stages of `verify_sig_lean_sphincs` (`lean_ethereum.py:3926-4011` at leanVM main 40f877dc)
  are complete for an honest signature: the message digest, the bottom key's address, FORS.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsStagesComplete

/-!
# The digest and FORS, complete

`G` is `lean_ethereum.py`. From the arguments (`n0` the claim, `n1` the byte table) to `n5249`,
the body is `sDigestBlock` (`G:3926-3999`), `sForsAddrs` (`G:4003-4004`) and `sForsB`
(`G:4006-4011`). `sBottom_complete`: for a claim of `pk` and `m` and a signature `sig`, under the
blocks' completeness, they complete with the padding run, `PK.seed`, `PK.root`, the digest's number
`digestT pk m sig` (`DigestAt`), the byte table's pointers, the bottom key's `A0` and `A1`, and the
FORS key cell (`forsKeyCell`, whose value is the statement's FORS key, `sForsKeyOf_eq`). The
signature's FORS openings are hinted (`forsSecretCell`, `forsSibCell`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## What the digest block leaves -/

theorem sFVal_below {c z : Nat} (hc : c < 24) (hz : z < 10) : ∃ k < 1372, sFVal c z = .n k :=
  ⟨300 + 29 * c + 3 * (9 - z), by omega, rfl⟩

/-- `DigestAt` reads values below `n1372` only. -/
theorem DigestAt.congr {σ σ' : Val} {T : Nat} (h : DigestAt σ T)
    (ha : ∀ k < 1372, σ' (.n k) = σ (.n k)) : DigestAt σ' T := by
  obtain ⟨hT, hb, hv, hl, hm⟩ := h
  refine ⟨hT, fun k hk => by rw [ha _ (by omega)]; exact hb k hk, fun c hc z hz => ?_,
    fun l hl3 z hz => ?_, by rw [show sTreeMid = .n 1279 from rfl, ha _ (by norm_num)]; exact hm⟩
  · obtain ⟨k, hk, ek⟩ := sFVal_below hc hz
    rw [ek, ha k hk, ← ek]; exact hv c hc z hz
  · obtain ⟨k, hk, ek⟩ := sLVal_below (sLeafOff l + z)
    rw [ek, ha k hk, ← ek]; exact hl l hl3 z hz

/-- The pointers of the digest block's byte reads: the unused bytes'. -/
def sDigestPtrList : List Nat := (List.range 6).map (fbPtr 1312)

theorem sDigestBlock_ptrList : ∀ q ∈ loadPtrs sDigestBlock, q ∈ sDigestPtrList := by decide +kernel

theorem tablePtrs_of_digestPtrs {σ : Val} {bb : E} (h : DigestPtrs σ bb) :
    TablePtrs bb σ sDigestBlock := by
  intro q hq
  have hm := sDigestBlock_ptrList q hq
  simp only [sDigestPtrList, List.mem_map, List.mem_range] at hm
  obtain ⟨k, hk, rfl⟩ := hm
  exact h k (by omega)

/-- What the stages up to FORS leave, for the claim of `pk` and `m` signed by `sig`. -/
def BottomPost (bb : E) (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature)
    (σ : Val) : Prop :=
  PadOK σ sPad ∧ σ sPP = cellOf128 pk.publicSeed ∧ σ sRoot = cellOf128 pk.root ∧
    DigestAt σ (digestT pk m sig) ∧ TablePtrs bb σ sDigestBlock ∧
    σ sA0B = adrsCell0 0 (layerTreeN (digestT pk m sig) 0) ∧
    σ sKeyB = adrsCell1 0 (layerLeafN (digestT pk m sig) 0) 0 0 ∧ σ sForsPk = forsKeyCell pk m sig

theorem sDigestBlock_nb : NumBelow 1372 (Stmt.valsList sDigestBlock) := numBelow_of_all (by decide +kernel)

theorem sDigestBlock_ptrs : ∀ q ∈ loadPtrs sDigestBlock, q < 1372 := by decide +kernel

theorem sForsAddrs_seq : SeqOK 1372 sForsAddrs 1382 := seqB_ok (by decide +kernel)

theorem sForsB_nb : NumBelow 5249 (Stmt.valsList sForsB.1) := numBelow_of_all (by decide +kernel)

/-- `BottomPost` reads values below `n5249` only. -/
theorem BottomPost.congr {bb : E} {pk : Sphincs.PublicKey} {m : HashSig.Message}
    {sig : Sphincs.Signature} {σ σ' : Val} (h : BottomPost bb pk m sig σ)
    (ha : ∀ k < 5249, σ' (.n k) = σ (.n k)) : BottomPost bb pk m sig σ' := by
  obtain ⟨hp, hpp, hr, hd, hq, ha0, hk, hf⟩ := h
  refine ⟨hp.congr (b := 5249) (by unfold sPad; omega) fun j hj => (ha j hj).symm,
    by rw [show sPP = .n 2 from rfl, ha _ (by norm_num)]; exact hpp,
    by rw [show sRoot = .n 3 from rfl, ha _ (by norm_num)]; exact hr,
    hd.congr fun k hk => ha k (by omega),
    hq.congr (b := 5249) (fun q hq' => by have := sDigestBlock_ptrs q hq'; omega) ha,
    by rw [show sA0B = .n 1379 from rfl, ha _ (by norm_num)]; exact ha0,
    by rw [show sKeyB = .n 1381 from rfl, ha _ (by norm_num)]; exact hk,
    by rw [show sForsPk = .n 5248 from rfl, ha _ (by norm_num)]; exact hf⟩

/-- **The digest, the bottom key's address and FORS complete** for the claim of `pk` and `m` at
`n0`, the byte table at `n1`, a signature `sig`. -/
theorem sBottom_complete (hB : SphincsBlocksComplete) (hm : MemOK rd 256) {bb : E}
    (hbb : ByteBits rd bb) (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature)
    (σ : Val) (h1 : σ (.n 1) = bb)
    (hat : ClaimAt rd (σ (.n 0)) (cellOf128 pk.publicSeed) (cellOf128 pk.root) (msgLo m) (msgHi m)) :
    Completes C rd 2 5249 (sDigestBlock ++ (sForsAddrs ++ sForsB.1)) σ (BottomPost bb pk m sig) := by
  set T := digestT pk m sig with hTd
  refine Completes.append (m := 1372) (by norm_num) (by norm_num) sDigestBlock_nb
    (sDigestBlock_complete hm hbb pk m sig.randomizer hat σ rfl h1)
    (fun σA heA hA => ?_)
  obtain ⟨hppA, hrA, -, hpA, hdA, hqA⟩ := hA
  replace hdA : DigestAt σA T := by
    have e : (Id.run (Sphincs.Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk
      sig.randomizer m)).toNat = T := rfl
    rw [e] at hdA; exact hdA
  replace hqA := tablePtrs_of_digestPtrs hqA
  refine Completes.seq sForsAddrs_seq (by norm_num) (fun σB heB hAt => ?_)
  have tB : ∀ k < 1372, σB (.n k) = σA (.n k) := fun k hk => heB.apply (Or.inl hk)
  have hdB := hdA.congr tB
  obtain ⟨ha0B, hkB⟩ := sForsAddrs_vals hdB.2.2.2.1 hdB.2.2.2.2 hAt
  have hpB : PadOK σB sPad := hpA.congr (b := 1372) (by unfold sPad; omega) fun j hj => (tB j hj).symm
  have hppB : σB sPP = cellOf128 pk.publicSeed := by
    rw [show sPP = .n 2 from rfl, tB 2 (by norm_num)]; exact hppA
  have hF := hB.fors C rd σB (layerTreeN T 0) (layerLeafN T 0) (forsLeafN T) (forsSecretCell sig)
    (forsSibCell sig) hpB ha0B hkB
    (fun c _ => forsLeafN_lt T c)
    (fun c hc z hz => by
      have e : sForsBit (10 * c + z) = sMdBit (10 * c + 9 - z) := by
        simp only [sForsBit]
        rw [show (10 * c + z) / 10 = c by omega, show (10 * c + z) % 10 = z by omega]
      rw [e, hdB.mdBit (by omega), testBit_forsLeafN]
      simp [hz, bitE])
    (fun c hc z hz => by
      have e : sVals (10 * c + z) = sFVal c z := by
        simp only [sVals]
        rw [show (10 * c + z) / 10 = c by omega, show (10 * c + z) % 10 = z by omega]
      rw [e]; exact hdB.2.2.1 c hc z hz)
  obtain ⟨σC, heC, hfC, hhC⟩ := hF
  have tC : ∀ k < 1382, σC (.n k) = σB (.n k) := fun k hk => heC.apply (Or.inl hk)
  have tCA : ∀ k < 1372, σC (.n k) = σA (.n k) := fun k hk => by rw [tC k (by omega), tB k hk]
  refine ⟨σC, heC, ⟨hpA.congr (b := 1372) (by unfold sPad; omega) fun j hj => (tCA j hj).symm,
    by rw [show sPP = .n 2 from rfl, tCA 2 (by norm_num)]; exact hppA,
    by rw [show sRoot = .n 3 from rfl, tCA 3 (by norm_num)]; exact hrA,
    hdA.congr tCA, hqA.congr sDigestBlock_ptrs tCA,
    by rw [show sA0B = .n 1379 from rfl, tC _ (by norm_num)]; exact ha0B,
    by rw [show sKeyB = .n 1381 from rfl, tC _ (by norm_num)]; exact hkB,
    by rw [hfC, hppB]; rfl⟩, hhC⟩

end
end LeanVM.Guest.B1.Sig
