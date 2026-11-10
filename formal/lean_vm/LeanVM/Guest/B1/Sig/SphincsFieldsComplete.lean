/-
  LeanVM.Guest.B1.Sig.SphincsFieldsComplete

  The digest's fields and check in `verify_sig_lean_sphincs` (`lean_ethereum.py:3973-4024` at
  leanVM main 40f877dc) are complete: the bits hinted from `H_msg`'s cells, every field and byte rebuilt,
  the cells checked, the second call's unused bytes read and its high lane checked; and the whole
  message digest block completes on a claim.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsDigestComplete

/-!
# The digest's fields and check, complete

* `sFieldsCheck_complete`: from `H_msg`'s canonical cells, the block after the calls completes
  with `DigestAt σ' T`, `T` the digest's number;
* `sDigestBlock_complete`: the whole block on a claim, `T` the statement's `H_msg` of the claim and
  the randomizer.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## Transport -/

theorem BitsAt.congr {σ σ' : Val} {T : Nat} (h : BitsAt σ T) (hσ : ∀ k < 300, σ' (.n k) = σ (.n k)) :
    BitsAt σ' T := fun k hk => by rw [hσ _ (by omega)]; exact h k hk

theorem sFVal_lt {c z : Nat} (hc : c < 24) (hz : z < 10) : ∃ k < 995, sFVal c z = .n k :=
  ⟨300 + 29 * c + 3 * (9 - z), by omega, rfl⟩

theorem FValsAt.congr {σ σ' : Val} {T : Nat} (h : FValsAt σ T) (hσ : ∀ k < 995, σ' (.n k) = σ (.n k)) :
    FValsAt σ' T := fun c hc z hz => by
  obtain ⟨k, hk, e⟩ := sFVal_lt hc hz
  rw [e, hσ k hk, ← e]; exact h c hc z hz

theorem sLVal_lt {i : Nat} (hi : i < 26) : ∃ k < 1067, sLVal i = .n k := by
  unfold sLVal; split_ifs <;> exact ⟨_, by omega, rfl⟩

theorem LValsAt.congr {σ σ' : Val} {T : Nat} (h : LValsAt σ T) (hσ : ∀ k < 1067, σ' (.n k) = σ (.n k)) :
    LValsAt σ' T := fun l hl z hz => by
  have : sLeafOff l + z < 26 := by
    simp only [sLeafOff, sLeafLen] at hz ⊢; split_ifs at hz <;> omega
  obtain ⟨k, hk, e⟩ := sLVal_lt this
  rw [e, hσ k hk, ← e]; exact h l hl z hz

/-! ## The block after the calls -/

/-- The digest's number from `H_msg`'s cells. -/
def digestNatOf (x0 x1 y : E) : Nat := cellNat x0 + 2 ^ 128 * cellNat x1 + 2 ^ 256 * (cellNat y % 2 ^ 16)

theorem digestNatOf_lt (x0 x1 y : E) : digestNatOf x0 x1 y < 2 ^ 272 := by
  have := cellNat_lt x0; have := cellNat_lt x1
  unfold digestNatOf; omega

/-- The second call's unused bytes: its low limb's bits from 16. -/
def unusedOf (y : E) : Nat := kToNat (y.limb 0) / 2 ^ 16

theorem unusedOf_lt (y : E) : unusedOf y < 2 ^ 48 := by
  have := kToNat_lt (y.limb 0); unfold unusedOf; omega

theorem canon_eq192 {x : E} (h : IsCanonical128 x) : x = eOfNat128 (cellNat x) := by
  have h0 := kToNat_lt (x.limb 0)
  have h1 := kToNat_lt (x.limb 1)
  rw [eq_ofLimbs_of_canonical h, eOfNat128, cellNat]
  simp only [ofLimbs_limb0, ofLimbs_limb1]
  rw [show (kToNat (x.limb 0) + 2 ^ 64 * kToNat (x.limb 1)) / 2 ^ 64 = kToNat (x.limb 1) by omega,
    show (kToNat (x.limb 0) + 2 ^ 64 * kToNat (x.limb 1)) / 2 ^ 128 = 0 by omega,
    ← ofBits_mod, show (kToNat (x.limb 0) + 2 ^ 64 * kToNat (x.limb 1)) % 2 ^ 64 = kToNat (x.limb 0) by omega,
    ofBits_kToNat, ofBits_kToNat, Value.ofBits_zero]

theorem sFieldsSplit : sBitsHint ++ sBooleans ++ sForsFields ++ sLeafShifts ++ sMdBytes ++ sCheck =
    (sBitsHint ++ sBooleans) ++ ((sForsFields ++ sLeafShifts ++ sMdBytes ++ sCheckA ++
      [cst 1295 corr0W]) ++ ([addS sHm0 sMd0.2.2 (.n 1295)] ++
      (([cst 1296 corr1W, addS (.n 1297) sMd1.2.2 (.n 1296)] ++ sCheckB) ++
        ([addS sHm0b (.n 1303) (.n 1305)] ++
        ([hintW "sp_unused" (runV 1306 6)] ++ (sUnused.1 ++ (sCheckC ++
          [.atom (.assertInK (.n 1371) sUnused.2.2)]))))))) := by
  rw [sCheck_split]; simp only [sCheckCorr, List.append_assoc]; rfl

theorem sFields_seq_ok :
    SeqOK 300 (sForsFields ++ sLeafShifts ++ sMdBytes ++ sCheckA ++ [cst 1295 corr0W]) 1296 :=
  seqB_ok (by decide +kernel)

theorem sCheckB_ok :
    SeqOK 1296 ([cst 1296 corr1W, addS (.n 1297) sMd1.2.2 (.n 1296)] ++ sCheckB) 1306 :=
  seqB_ok (by decide +kernel)
theorem sCheckC_ok : SeqOK 1363 sCheckC 1372 := seqB_ok (by decide +kernel)

theorem sBits_atoms : atomsOnly (sBitsHint ++ sBooleans) = true := by decide +kernel
theorem sBits_nb : NumBelow 300 (Stmt.valsList (sBitsHint ++ sBooleans)) := numBelow_of_all (by decide +kernel)

theorem mem_sBooleans' {a : Atom} (h : Stmt.atom a ∈ sBooleans) :
    ∃ k < 272, a = .mul (.n (28 + k)) (.n (28 + k)) (.n (28 + k)) := by
  simp only [sBooleans, booleans, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map] at h
  rcases h with ⟨b, hb, hm⟩ | ⟨j, hj, e⟩
  · simp only [mulS, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hm
    rcases hm with rfl | rfl
    · exact ⟨b, by omega, rfl⟩
    · exact ⟨128 + b, by omega, by rw [show 28 + (128 + b) = 156 + b by omega]⟩
  · simp only [mulS, Stmt.atom.injEq] at e
    exact ⟨256 + j, by omega, by rw [← e, show 28 + (256 + j) = 284 + j by omega]⟩

/-- **The block after `H_msg`'s calls completes**: the bits hinted from the calls' canonical cells,
the fields, the bytes, the cells checked, the unused bytes read and the high lane checked; it gives
the digest's fields of `T`, the cells' number, and the unused bytes' pointers. -/
theorem sFieldsCheck_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) (σ : Val)
    (h1 : σ (.n 1) = bb) (hc0 : IsCanonical128 (σ sHm0)) (hc0b : IsCanonical128 (σ sHm0b))
    (hc1 : IsCanonical128 (σ sHm1)) :
    Completes C rd 28 1372 (sBitsHint ++ sBooleans ++ sForsFields ++ sLeafShifts ++ sMdBytes ++ sCheck) σ
      (fun σ' => DigestAt σ' (digestNatOf (σ sHm0) (σ sHm0b) (σ sHm1)) ∧
        ∀ k ≤ 5, BytePtr bb (σ' (.n (fbPtr 1312 k)))) := by
  set T := digestNatOf (σ sHm0) (σ sHm0b) (σ sHm1) with hT
  have hTlt : T < 2 ^ 272 := digestNatOf_lt _ _ _
  have n0 := cellNat_lt (σ sHm0)
  have n0b := cellNat_lt (σ sHm0b)
  set f : Nat → E := fun k => bitE (T.testBit k) with hf
  rw [sFieldsSplit]
  refine Completes.reload ((updRun_ext σ 28 272 f).mono le_rfl (by norm_num)) ?_
  set σb := updRun σ 28 272 f with hσb
  have hbits : BitsAt σb T := fun k hk => updRun_at σ 28 272 f hk
  have blow : ∀ k < 28, σb (.n k) = σ (.n k) := fun k hk => by
    rw [hσb]; exact updRun_below σ 28 272 f ⟨k, hk, rfl⟩
  -- the bits' hints and checks
  have hchk : AtomsHold rd σb (sBitsHint ++ sBooleans) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · simp only [sBitsHint, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl | rfl <;> trivial
    · obtain ⟨k, hk, rfl⟩ := mem_sBooleans' ha
      show σb _ = σb _ * σb _
      rw [hbits k hk]
      exact (bitE_mul_self _).symm
  refine Completes.append (m := 300) (by norm_num) (by norm_num) sBits_nb
    (completes_atoms (Post := fun σ' => σ' = σb) sBits_atoms (Ext.refl _ _ _) rfl hchk)
    (fun σ' _ e => ?_)
  subst e
  -- the fields, the leaves, the bytes, the tree's middle byte and the unused bits
  refine Completes.seq (m := 1296) sFields_seq_ok (by norm_num) (fun σ1 he1 hh1' => ?_)
  have t1 : ∀ k < 300, σ1 (.n k) = σb (.n k) := fun k hk => he1.apply (Or.inl hk)
  have hb1 : BitsAt σ1 T := hbits.congr t1
  have hh1 : AtomsHold rd σ1 (sForsFields ++ sLeafShifts ++ sMdBytes ++ sCheckA) :=
    AtomsHold.left (ys := [cst 1295 corr0W]) hh1'
  have k18 : σ1 (.n 1295) = corr0W :=
    (AtomsHold.right (xs := sForsFields ++ sLeafShifts ++ sMdBytes ++ sCheckA) hh1').atom
      (a := .const _ _) (by simp [cst])
  have hA3 : AtomsHold rd σ1 (sForsFields ++ sLeafShifts ++ sMdBytes) := AtomsHold.left (ys := sCheckA) hh1
  have hA2 : AtomsHold rd σ1 (sForsFields ++ sLeafShifts) := AtomsHold.left (ys := sMdBytes) hA3
  have hv1 : FValsAt σ1 T := sForsFields_sound hb1 (AtomsHold.left (ys := sLeafShifts) hA2)
  have hl1 : LValsAt σ1 T := sLeafShifts_sound hb1 (AtomsHold.right (xs := sForsFields) hA2)
  have hmd : AtomsHold rd σ1 sMdBytes := AtomsHold.right (xs := sForsFields ++ sLeafShifts) hA3
  have hmd2 : AtomsHold rd σ1 ((sMdByte 0 1067).1 ++ sMd0.1) := AtomsHold.left (ys := sMd1.1) hmd
  have m0 : σ1 sMd0.2.2 + corr0W = eOfNat128 (T % 2 ^ 128) :=
    sMd0_sound hv1 (AtomsHold.left (ys := sMd0.1) hmd2) (AtomsHold.right (xs := (sMdByte 0 1067).1) hmd2)
  have m1 : σ1 sMd1.2.2 + corr1W = eOfNat128 (T / 2 ^ 128 % 2 ^ 112) :=
    sMd1_sound hv1 (AtomsHold.right (xs := (sMdByte 0 1067).1 ++ sMd0.1) hmd)
  obtain ⟨tm1, pad1⟩ := sCheckA_sound hb1 hl1 (AtomsHold.right (xs := sForsFields ++ sLeafShifts ++ sMdBytes) hh1)
  have v0 : σ1 sHm0 = eOfNat128 (T % 2 ^ 128) := by
    rw [show sHm0 = .n 17 from rfl, t1 _ (by norm_num), blow _ (by norm_num), ← show sHm0 = .n 17 from rfl,
      canon_eq192 hc0]
    congr 1; simp only [hT, digestNatOf]; omega
  refine Completes.checks (xs := [addS sHm0 sMd0.2.2 (.n 1295)]) rfl (fun a ha => by
      simp only [addS, List.mem_singleton, Stmt.atom.injEq] at ha
      subst ha
      show σ1 sHm0 = σ1 sMd0.2.2 + σ1 (.n 1295)
      rw [v0, k18, m0])
    (numBelow_of_all (by decide +kernel)) (by norm_num) ?_
  -- `md1 + corr1`, the tree index's high bytes placed
  refine Completes.seq (m := 1306) sCheckB_ok (by norm_num) (fun σ2 he2 hh2' => ?_)
  have t2 : ∀ k < 1296, σ2 (.n k) = σ1 (.n k) := fun k hk => he2.apply (Or.inl hk)
  have hh2 : AtomsHold rd σ2 sCheckB :=
    AtomsHold.right (xs := [cst 1296 corr1W, addS (.n 1297) sMd1.2.2 (.n 1296)]) hh2'
  have hc0 := AtomsHold.left (ys := sCheckB) hh2'
  have k19 : σ2 (.n 1296) = corr1W := hc0.atom (a := .const _ _) (by simp [cst])
  have a20 : σ2 (.n 1297) = σ2 sMd1.2.2 + σ2 (.n 1296) := hc0.atom (a := .add _ _ _) (by simp [addS])
  have hB := sCheckB_sound (hl1.congr fun k hk => t2 k (by omega))
    (by rw [show sTreeMid = .n 1279 from rfl, t2 _ (by norm_num)]; exact tm1)
    (by rw [t2 _ (by norm_num)]; exact pad1)
    (by rw [a20, k19, show sMd1.2.2 = .n 1276 by decide +kernel, t2 _ (by norm_num), ← show sMd1.2.2 = .n 1276 by
      decide +kernel]; exact m1) hh2
  have v0b : σ2 sHm0b = eOfNat128 (T / 2 ^ 128 % 2 ^ 128) := by
    rw [show sHm0b = .n 18 from rfl, t2 _ (by norm_num), t1 _ (by norm_num), blow _ (by norm_num),
      ← show sHm0b = .n 18 from rfl, canon_eq192 hc0b]
    congr 1; simp only [hT, digestNatOf]; omega
  refine Completes.checks (xs := [addS sHm0b (.n 1303) (.n 1305)]) rfl (fun a ha => by
      simp only [addS, List.mem_singleton, Stmt.atom.injEq] at ha
      subst ha
      show σ2 sHm0b = σ2 (.n 1303) + σ2 (.n 1305)
      rw [v0b, hB])
    (numBelow_of_all (by decide +kernel)) (by norm_num) ?_
  -- the unused bytes
  set U := unusedOf (σ sHm1) with hU
  set g : Nat → E := fun k => ofK (addressOfIndex (U / 256 ^ k % 256)) with hg
  refine Completes.reload ((updRun_ext σ2 1306 6 g).mono le_rfl (by norm_num)) ?_
  set σu := updRun σ2 1306 6 g with hσu
  have ulow : ∀ k < 1306, σu (.n k) = σ2 (.n k) := fun k hk => by
    rw [hσu]; exact updRun_below σ2 1306 6 g ⟨k, hk, rfl⟩
  refine Completes.append (xs := [hintW "sp_unused" (runV 1306 6)]) (m := 1312) (by norm_num) (by norm_num)
    (by rw [valsList_hint]; exact numBelow_of_all (by decide)) (hintKeep_complete _ _ _ _ _)
    (fun σ3 _ e3 => ?_)
  subst e3
  refine Completes.append (m := 1363) (by norm_num) (by norm_num)
    (sFromBytes_shape (sMarks 1306 6).1 (sMarks 1306 6).2 1312 ⟨1311, by norm_num, by simp [sMarks]⟩
      (fun m hm => by simp [sMarks] at hm; obtain ⟨k, hk, rfl⟩ := hm; exact ⟨1306 + k, by omega, rfl⟩)).2.2
    (sFromMarks_complete (b := 1306) (n := 6) (x := 1312) (X := U) hm hbb (by norm_num) (by norm_num) σu
      (by norm_num) (by norm_num) (fun t ht => by rw [hσu]; exact updRun_at σ2 1306 6 g ht)
      (by rw [ulow _ (by norm_num), t2 _ (by norm_num), t1 _ (by norm_num), blow _ (by norm_num)]; exact h1))
    (fun σ4 he4 ⟨hu4, hp4⟩ => ?_)
  -- the high lane
  refine Completes.seq (m := 1372) sCheckC_ok (by norm_num) (fun σ5 he5 hh5 => ?_)
  have t5 : ∀ k < 1296, σ5 (.n k) = σ1 (.n k) := fun k hk => by
    rw [he5.apply (Or.inl (by omega)), he4.apply (Or.inl (by omega)), ulow k (by omega), t2 k hk]
  have hl5 : LValsAt σ5 T := hl1.congr fun k hk => t5 k (by omega)
  have hu5 : σ5 sUnused.2.2 = eOfNat U := by
    rw [show sUnused.2.2 = .n 1362 by decide +kernel, he5.apply (Or.inl (by norm_num)),
      ← show sUnused.2.2 = .n 1362 by decide +kernel, show sUnused = sFromMarks 1306 6 1312 from rfl, hu4,
      Nat.mod_eq_of_lt (by have := unusedOf_lt (σ sHm1); norm_num; omega)]
  have hC := sCheckC_sound hl5 hu5 (unusedOf_lt _) hh5
  have y5 : σ5 sHm1 = σ sHm1 := by
    rw [show sHm1 = .n 27 from rfl, t5 _ (by norm_num), t1 _ (by norm_num), blow _ (by norm_num)]
  refine Completes.checks (xs := [.atom (.assertInK (.n 1371) sUnused.2.2)]) rfl (fun a ha => by
      simp only [List.mem_singleton, Stmt.atom.injEq] at ha
      subst ha
      refine ⟨?_, by rw [hu5]; exact eOfNat_isInK _⟩
      have hl : T / 2 ^ 256 % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by norm_num)
      have e1 : cellNat (σ sHm1) % 2 ^ 16 = kToNat ((σ sHm1).limb 0) % 2 ^ 16 := by unfold cellNat; omega
      have e2 : T / 2 ^ 256 % 2 ^ 16 = cellNat (σ sHm1) % 2 ^ 16 := by
        simp only [hT, digestNatOf]; omega
      have hk : 2 ^ 16 * U + T / 2 ^ 256 % 2 ^ 16 = kToNat ((σ sHm1).limb 0) := by
        rw [e2, e1]; simp only [hU, unusedOf]; omega
      rw [hC, y5, word_y_inv', add_assoc, add_comm (eOfNat (T / 2 ^ 256 % 2 ^ 16)),
        Value.eOfNat_add_of_lt hl, hk, show eOfNat (kToNat ((σ sHm1).limb 0)) = ofK ((σ sHm1).limb 0) by
          rw [LeanVM.Protocol.Verifier.eOfNat, ofBits_kToNat], split_hi hc1]
      exact ofK_isInK _)
    (numBelow_of_all (by decide +kernel)) le_rfl ?_
  refine Completes.nil' ⟨⟨hTlt, hb1.congr fun k hk => t5 k (by omega), (hv1.congr fun k hk => t5 k (by omega)),
    hl5, by rw [show sTreeMid = .n 1279 from rfl, t5 _ (by norm_num)]; exact tm1⟩, fun k hk => ?_⟩
  rw [he5.apply (Or.inl (by simp only [fbPtr]; split <;> omega))]
  exact hp4 k hk

/-! ## The whole block -/

theorem canon_dh1 (d) : IsCanonical128 (digestHalves d).1 := by simp [IsCanonical128, digestHalves]
theorem canon_dh2 (d) : IsCanonical128 (digestHalves d).2 := by simp [IsCanonical128, digestHalves]

theorem hmsgNat_lt (d0 d1 : E × E) : hmsgNat d0 d1 < 2 ^ 272 := digestNatOf_lt d0.1 d0.2 d1.1

theorem cellOf128_eq192 (v : BitVec 128) : cellOf128 v = eOfNat128 v.toNat := by
  rw [canon_eq192 (isCanonical128_cellOf128 v), cellNat_cellOf128]

theorem sDigestBlock_split : sDigestBlock = sMsg ++ (sDigests ++
    (sBitsHint ++ sBooleans ++ sForsFields ++ sLeafShifts ++ sMdBytes ++ sCheck)) := by
  simp only [sDigestBlock, List.append_assoc]

theorem sMsg_nb : NumBelow 6 (Stmt.valsList sMsg) := numBelow_of_all (by decide +kernel)
theorem sDigests_nb : NumBelow 28 (Stmt.valsList sDigests) := numBelow_of_all (by decide +kernel)

/-- The byte pointers of the message block: the second call's six unused bytes. -/
def DigestPtrs (σ : Val) (bb : E) : Prop := ∀ k ≤ 5, BytePtr bb (σ (.n (fbPtr 1312 k)))

/-- **The message digest's block completes** on a claim: the keys and message loaded, the
randomizer `R` hinted, and the block's fields those of the statement's `H_msg` of the claim and
`R`. -/
theorem sDigestBlock_complete (hm : MemOK rd 256) {bb p : E} (hbb : ByteBits rd bb) (pk : Sphincs.PublicKey)
    (msg : HashSig.Message) (R : HashSig.Randomizer)
    (hcl : ClaimAt rd p (cellOf128 pk.publicSeed) (cellOf128 pk.root) (cellOf128 (msg.extractLsb' 0 128))
      (cellOf128 (msg.extractLsb' 128 128)))
    (σ : Val) (h0 : σ (.n 0) = p) (h1 : σ (.n 1) = bb) :
    Completes C rd 2 1372 sDigestBlock σ (fun σ' => σ' sPP = cellOf128 pk.publicSeed ∧
      σ' sRoot = cellOf128 pk.root ∧ σ' sRand = cellOf128 R ∧ PadOK σ' sPad ∧
      DigestAt σ' (Id.run (Sphincs.Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk R
        msg)).toNat ∧ DigestPtrs σ' bb) := by
  set M := msg.toNat with hMdef
  have hM : M < 2 ^ 256 := msg.isLt
  have e0 : cellOf128 (msg.extractLsb' 0 128) = eOfNat128 (M % 2 ^ 128) := by
    rw [cellOf128_eq192, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have e1 : cellOf128 (msg.extractLsb' 128 128) = eOfNat128 (M / 2 ^ 128) := by
    rw [cellOf128_eq192, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
  rw [e0, e1] at hcl
  rw [sDigestBlock_split]
  refine Completes.append (m := 6) (by norm_num) (by norm_num) sMsg_nb
    (sMsg_complete hcl σ h0) (fun σ1 he1 ⟨pP, pR, m0, m1⟩ => ?_)
  have hm0 : IsCanonical128 (σ1 sM0) := by rw [m0]; exact canon_eOfNat128 (Nat.mod_lt _ (by norm_num))
  have hm1 : IsCanonical128 (σ1 sM1) := by rw [m1]; exact canon_eOfNat128 (by omega)
  refine Completes.append (m := 28) (by norm_num) (by norm_num) sDigests_nb
    (sDigests_complete (C := C) (rd := rd) (Rho := cellOf128 R) (isCanonical128_cellOf128 R) σ1
      (by rw [pP]; exact isCanonical128_cellOf128 _) (by rw [pR]; exact isCanonical128_cellOf128 _) hm0 hm1)
    (fun σ2 he2 ⟨rR, hpad, d0, d1⟩ => ?_)
  have t21 : ∀ k < 6, σ2 (.n k) = σ1 (.n k) := fun k hk => he2.apply (Or.inl hk)
  have hcells : ∀ i, hmsgCells σ2 i = [cellOf128 R, cellOf128 pk.publicSeed, cellOf128 pk.root,
      eOfNat128 (M % 2 ^ 128), eOfNat128 (M / 2 ^ 128), word (i * 2 ^ 24) 0] := by
    intro i
    simp only [hmsgCells]
    rw [rR, show sPP = .n 2 from rfl, t21 2 (by norm_num), show sRoot = .n 3 from rfl, t21 3 (by norm_num),
      show sM0 = .n 4 from rfl, t21 4 (by norm_num), show sM1 = .n 5 from rfl, t21 5 (by norm_num)]
    rw [← show sPP = .n 2 from rfl, pP, ← show sRoot = .n 3 from rfl, pR, ← show sM0 = .n 4 from rfl, m0,
      ← show sM1 = .n 5 from rfl, m1]
  have hmn : msgNat (eOfNat128 (M % 2 ^ 128)) (eOfNat128 (M / 2 ^ 128)) = M := by
    simp only [msgNat]
    rw [cellNat_eOfNat128 (Nat.mod_lt _ (by norm_num)), cellNat_eOfNat128 (by omega)]
    omega
  rw [hcells, hcellLen, hmsg_take (by norm_num), hmn] at d0
  rw [hcells, hcellLen, hmsg_take (by norm_num), hmn] at d1
  have hT : digestNatOf (σ2 sHm0) (σ2 sHm0b) (σ2 sHm1) =
      (Id.run (Sphincs.Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk R msg)).toNat := by
    have hpk : (⟨cellVal (cellOf128 pk.publicSeed), cellVal (cellOf128 pk.root)⟩ : Sphincs.PublicKey) = pk := by
      have e1 : cellVal (cellOf128 pk.publicSeed) = pk.publicSeed := cellVal_cellOf128 _
      have e2 : cellVal (cellOf128 pk.root) = pk.root := cellVal_cellOf128 _
      rw [e1, e2]
    have hR : R = cellVal (cellOf128 R) := (cellVal_cellOf128 R).symm
    rw [← hpk, hR, hmsgDigest_cells, ← hMdef, ← d0, d1, digestOf_toNat (hmsgNat_lt _ _)]
    rfl
  have h12 : σ2 (.n 1) = bb := by
    rw [he2.apply (Or.inl (by norm_num)), he1.apply (Or.inl (by norm_num))]; exact h1
  refine ((sFieldsCheck_complete hm hbb σ2 h12
      (by have e := congrArg Prod.fst d0; dsimp only at e; rw [e]; exact canon_dh1 _)
      (by have e := congrArg Prod.snd d0; dsimp only at e; rw [e]; exact canon_dh2 _)
      (by rw [d1]; exact canon_dh1 _)).keep
    (Q := fun σ' => σ' sPP = cellOf128 pk.publicSeed ∧ σ' sRoot = cellOf128 pk.root ∧
      σ' sRand = cellOf128 R ∧ PadOK σ' sPad)
    (Q' := fun σ' => σ' sPP = cellOf128 pk.publicSeed ∧ σ' sRoot = cellOf128 pk.root ∧
      σ' sRand = cellOf128 R ∧ PadOK σ' sPad)
    ⟨by rw [show sPP = .n 2 from rfl, t21 2 (by norm_num)]; exact pP,
      by rw [show sRoot = .n 3 from rfl, t21 3 (by norm_num)]; exact pR, rR, hpad⟩
    (fun σ' he ⟨q1, q2, q3, q4⟩ => ⟨by rw [show sPP = .n 2 from rfl, he.apply (Or.inl (by norm_num))]; exact q1,
      by rw [show sRoot = .n 3 from rfl, he.apply (Or.inl (by norm_num))]; exact q2,
      by rw [show sRand = .n 6 from rfl, he.apply (Or.inl (by norm_num))]; exact q3,
      q4.congr (b := 28) (by simp [sPad]) (fun k hk => (he.apply (Or.inl hk)).symm)⟩)).mono
    le_rfl le_rfl ?_
  rintro σ' ⟨⟨hD, hu⟩, q1, q2, q3, q4⟩
  exact ⟨q1, q2, q3, q4, by rw [← hT]; exact hD, hu⟩

end
end LeanVM.Guest.B1.Sig
