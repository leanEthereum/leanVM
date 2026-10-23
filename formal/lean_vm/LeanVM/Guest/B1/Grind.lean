/-
  LeanVM.Guest.B1.Grind

  B1 for `grind_check` and its loop `__loop6`: the proof-of-work check of the specification's
  `.grind`.
-/

module

public import LeanVM.Guest.B1.OpeningOod

/-!
# `grind_check` (TRIAGE #18)

`grind_check(st0, st1, nonce, g^bits)` (G:701-737) squeezes the base at `DS_POW_BASE`, absorbs
the nonce at `DS_POW_NONCE`, splits the digest's low lane off, decomposes it into 64 Boolean
frame cells (`gcBit`, reconstructed over `COORD_BASIS`), names the run by `addr`, and the loop
`__loop6` reads the run's first `bits` cells as zero. At `bits = 0` the nonce is zero. That is
`powOk bits nonce D` (V:482) for the digest `.grind` checks (V:566-572); the run read past its
64 cells is memory the meaning names.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `__loop6` -/

theorem find_loop6 : coreProgram.find? "__loop6" = some Data.core36 :=
  Program.find?_of_indexOf? (j := 36) (by decide +kernel) rfl

theorem loop6_step (rd : Reader) (N p : E) (d : ℕ) (x : E) :
    coreProgram.relN rd (d + 1) "__loop6" (x :: [N, p]) [] ↔
      LoadHolds rd (p * x) 0 0 ∧ IsInK (x * gen + N) ∧
        (x * gen + N ≠ 0 → coreProgram.relN rd d "__loop6" (x * gen :: [N, p]) []) := by
  rw [relN_succ_iff find_loop6, show Fn.params Data.core36 = [.n 0, .n 1, .n 2] from rfl,
    show Fn.body Data.core36 = Data.core36.body from rfl, Data.core36.body]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true,
    word_gen, word_zero]
  constructor
  · rintro ⟨σ, hp, h3, l4, h5, a4, h6, h7, h8, h9, h10, hK, hcall⟩
    simp only [List.cons.injEq] at hp
    obtain ⟨rfl, rfl, rfl, -⟩ := hp
    rw [h5, add_zero] at a4
    rw [a4, h3] at l4
    refine ⟨l4, by rwa [h8, h7, h6] at hK, fun hne => ?_⟩
    have := hcall (by rwa [h8, h7, h6])
    rwa [h10, h9] at this
  · rintro ⟨l4, hK, hcall⟩
    refine ⟨setl (Val.ofArgs [x, N, p]) 3 [p * x, 0, 0, gen, x * gen, x * gen + N, gen, x * gen],
      ?_, ?_⟩
    · b1_look
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try b1_look)
      · exact l4
      · exact add_zero 0
      · exact hK
      · exact hcall

/-! ## The lane's bits -/

/-- The accumulator after bit `i`. -/
def gcAcc : ℕ → ℕ
  | 0 => 34
  | i + 1 => 100 + 3 * i

/-- Bit `i` of the lane: booleanity, then (past the first, folded) its term added. -/
def gcBit : ℕ → List Stmt
  | 0 => [.atom (.mul (.n 34) (.n 34) (.n 34))]
  | i + 1 => [.atom (.mul (.n (35 + i)) (.n (35 + i)) (.n (35 + i))),
      .atom (.const (.n (98 + 3 * i)) (word (2 ^ (i + 1)) 0 0)),
      .atom (.mul (.n (99 + 3 * i)) (.n (35 + i)) (.n (98 + 3 * i))),
      .atom (.add (.n (100 + 3 * i)) (.n (gcAcc i)) (.n (99 + 3 * i)))]

/-- What bit `i` asks of a valuation. -/
def GcBitOk (σ : Val) : ℕ → Prop
  | 0 => σ (.n 34) = σ (.n 34) * σ (.n 34)
  | i + 1 => σ (.n (35 + i)) = σ (.n (35 + i)) * σ (.n (35 + i)) ∧
      σ (.n (98 + 3 * i)) = word (2 ^ (i + 1)) 0 0 ∧
      σ (.n (99 + 3 * i)) = σ (.n (35 + i)) * σ (.n (98 + 3 * i)) ∧
      σ (.n (100 + 3 * i)) = σ (.n (gcAcc i)) + σ (.n (99 + 3 * i))

theorem holds_gcBit {C : CallRel} {rd : Reader} {σ : Val} (i : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gcBit i) True kret ↔ GcBitOk σ i := by
  cases i <;> simp only [gcBit, GcBitOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

theorem word_coordBasis {i : ℕ} (h : i < 64) : word (2 ^ i) 0 0 = coordBasis i := by
  rw [word_eOfNat, coordBasis_of_lt h]

theorem gc_acc {σ : Val} : ∀ n, n < 64 → (∀ i < n + 1, GcBitOk σ i) →
    σ (.n (gcAcc n)) = ∑ i ∈ Finset.range (n + 1), σ (.n (34 + i)) * coordBasis i
  | 0, _, _ => by
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, Nat.add_zero, coordBasis, pow_zero,
      eOfNat192_of_lt (show (1 : ℕ) < 2 ^ 64 by decide), eOfNat_one, mul_one]
    rfl
  | n + 1, hn, h => by
    obtain ⟨-, e98, e99, e100⟩ := h (n + 1) (by omega)
    rw [gcAcc, e100, gc_acc n (by omega) (fun i hi => h i (by omega)), e99, e98,
      word_coordBasis hn, Finset.sum_range_succ (n := n + 1), show 34 + (n + 1) = 35 + n by omega]

/-! ## The body -/

/-- The 64 frame cells of the lane's bits. -/
def gcRun : List V := (List.range 64).map fun i => .n (34 + i)

/-- The expansion of `grind_check`. -/
def gcBody : List Stmt :=
  [.atom (.const (.n 4) (word 1 0 0)), .atom (.add (.n 5) (.n 3) (.n 4)),
    .ite (.n 5) [.atom (.const (.n 6) (word 0 0 0)), .atom (.assertEq (.n 2) (.n 6))] [],
    .atom (.copy (.n 7) (.n 0)), .atom (.copy (.n 8) (.n 1))] ++
  squeezeStateT (.n 7) (.n 8) 9 3 ++ fsCompressT (.n 14) (.n 15) (.n 2) 16 4 ++
  canonicalLimbsT (.n 28) 30 ++ [.atom (.hint (.bits (.n 30) 0 64 (.stack gcRun)))] ++
  ((List.range 64).map gcBit).flatten ++
  [.atom (.assertEq (.n 286) (.n 30)), .atom (.frameAddr (.n 287) gcRun),
    .atom (.const (.n 288) (word 1 0 0)), .atom (.add (.n 289) (.n 288) (.n 3)),
    .atom (.const (.n 290) (word 1 0 0)), .callIf (.n 289) "__loop6" [.n 290, .n 3, .n 287],
    .ret []]

theorem core3_body : Fn.body Data.core3 = gcBody := stmtsEqb_sound (by decide +kernel)

/-! ## The meaning -/

/-- The digest `.grind` checks (V:566-572): the base squeezed at tag 3, then the nonce absorbed
at tag 4. -/
def gcDigest (cv : Digest) (nonce : E) : Digest :=
  blake2sBytes (digestBytes (blake2sBytes (digestBytes cv ++ blockOf 0 3)) ++ blockOf nonce 4)

/-- `p` names a frame run holding the 64 bits of `L`: every readable word at `p·g^k`, `k < 64`,
is bit `k`. -/
def FrameBits (rd : Reader) (p : E) (L : ℕ) : Prop :=
  IsInK p ∧ ∀ k < 64, ∀ w, rd (p.limb 0 * Parameters.gpow k) = some w → w = bitE (L.testBit k)

/-- **`grind_check(st0, st1, nonce, g^bits)`** (G:701-737; TRIAGE #18): `bits` below the order of
`g`, the state the cells of `cv`, `powOk bits nonce` (V:482) of the digest `.grind` checks, and the
frame run `p` of the digest's low lane's bits reading zero at its first `bits` words. -/
def MeaningGrindCheck (rd : Reader) : List E → List E → Prop
  | [s0, s1, nonce, ng], rets =>
      rets = [] ∧ ∃ m < ordG, ng = gen ^ m ∧ ∃ cv, (s0, s1) = digestScalars cv ∧
        powOk m nonce (gcDigest cv nonce) = true ∧
        ∃ p, FrameBits rd p (kToNat ((digestScalars (gcDigest cv nonce)).1.limb 0)) ∧
          ∀ j < m, LoadHolds rd p j 0
  | _, _ => False

/-! ## The theorem -/

theorem find_grind_check : coreProgram.find? "grind_check" = some Data.core3 :=
  Program.find?_of_indexOf? (j := 3) (by decide +kernel) rfl

theorem gcRun_getElem (k : ℕ) (hk : k < gcRun.length) : gcRun[k] = .n (34 + k) := by
  simp [gcRun]

theorem length_gcRun : gcRun.length = 64 := by simp [gcRun]

theorem bitE_eq_zero_iff (b : Bool) : bitE b = 0 ↔ b = false := by
  cases b <;> simp [bitE]

/-- The low lane's bits make `powOk`: zero below `m` (those past 64 are zero anyway). -/
theorem powOk_of_bits {m : ℕ} {nonce : E} {D : Digest} (hm : 0 < m)
    (h : ∀ i < m, i < 64 → (kToNat ((digestScalars D).1.limb 0)).testBit i = false) :
    powOk m nonce D = true := by
  unfold powOk
  rw [ite_neg' (by omega), decide_eq_true_eq, ← kToNat_digestScalars_limb0]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < m
  · by_cases h64 : i < 64
    · simp [hi, h i hi h64]
    · have hlt := ((digestScalars D).1.limb 0).toBitVec.isLt
      simp only [hi, decide_true, Bool.true_and]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide)
        (by omega)))
  · simp [hi]

theorem grind_check_sound_aux (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "grind_check" args rets) : MeaningGrindCheck rd args rets := by
  rw [rel_iff_sem find_grind_check, core3_body,
    show Fn.params Data.core3 = [.n 0, .n 1, .n 2, .n 3] from rfl, gcBody] at h
  simp only [holdsList_append, Stmt.HoldsList] at h
  simp only [holds_ite_noRet (.n 5) [.atom (.const (.n 6) (word 0 0 0)),
    .atom (.assertEq (.n 2) (.n 6))] [] rfl rfl] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, holds_squeezeStateT _ _ _ (show 3 < 256 by decide),
    holds_fsCompressT _ _ _ _ (show 4 < 256 by decide), holds_canonicalLimbsT,
    holdsList_range_flatten 64 gcBit (fun i => by cases i <;> rfl), holds_gcBit, List.map_cons,
    List.map_nil, word_one, word_zero, true_and] at h
  obtain ⟨σ, hp, h4, h5, ⟨-, hz, -⟩, h7, h8, ⟨cv, hcv, eS⟩, ⟨cvb, hcvb, eF⟩,
    ⟨hcan, h30, -, -, -⟩, hbits, a286, ⟨hK0, hframe⟩, h288, h289, h290, hK, hcall, hret⟩ := h
  subst hp
  rw [h289, h288] at hK hcall
  rw [h290] at hcall
  obtain ⟨m, hm, hN, hB⟩ := (guarded_loop_iff (loop6_step rd (σ (.n 3)) (σ (.n 287)))).mp
    ⟨hK, hcall⟩
  rw [h7, h8] at hcv
  have f14 : σ (.n 14) = (digestScalars (absorbCv cv 0 3)).1 := eS 5 (by omega)
  have f15 : σ (.n 15) = (digestScalars (absorbCv cv 0 3)).2 := eS 6 (by omega)
  have gb : cvb = absorbCv cv 0 3 := digestScalars_injective (by rw [← hcvb, f14, f15])
  subst gb
  have f28 : σ (.n 28) = (digestScalars (gcDigest cv (σ (.n 2)))).1 := eF 12 (by omega) (by omega)
  set L := kToNat ((digestScalars (gcDigest cv (σ (.n 2)))).1.limb 0)
  have hsum := gc_acc 63 (by omega) hbits
  rw [show gcAcc 63 = 286 from rfl, e_add_eq_zero_iff.mp a286] at hsum
  obtain ⟨-, hb⟩ := bits_of_reconstruct_zero (n := 64) (by omega)
    (b := fun i => σ (.n (34 + i))) (fun i hi => by
      cases i with
      | zero => exact (hbits 0 (by omega)).symm
      | succ i => exact (show σ (.n (34 + (i + 1))) = σ (.n (35 + i)) by rw [show 34 + (i + 1) = 35 + i by omega]) ▸
          (hbits (i + 1) hi).1.symm) hsum.symm
  rw [h30, eToNat_ofK, f28] at hb
  have hloads : ∀ j < m, LoadHolds rd (σ (.n 287)) j 0 := fun j hj => by
    have := hB j hj
    rwa [loadHolds_mul_gen_pow, Nat.add_zero] at this
  have hfr : ∀ k < 64, ∀ w, rd ((σ (.n 287)).limb 0 * Parameters.gpow k) = some w →
      w = bitE (L.testBit k) := fun k hk w hw => by
    rw [hframe k (by rw [length_gcRun]; exact hk) w hw, gcRun_getElem]
    exact hb k hk
  refine ⟨hret.symm, m, hm, hN, cv, hcv, ?_, σ (.n 287), ⟨hK0, hfr⟩, hloads⟩
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have h5z : σ (.n 5) = 0 := by rw [h5, h4, hN, pow_zero]; exact e_add_self 1
      obtain ⟨h6, a2, -⟩ := hz h5z
      rw [h6, add_zero] at a2
      unfold powOk
      simp [a2, limb_zero]
    · refine powOk_of_bits h0 fun i hi h64 => ?_
      have := hfr i h64 0 (hloads i hi).2
      rw [eq_comm, bitE_eq_zero_iff] at this
      exact this

/-! ## Completeness -/

/-- The honest accumulator after bit `i` of `L`. -/
def gcAccV (L : ℕ) : ℕ → E
  | 0 => bitE (L.testBit 0)
  | i + 1 => gcAccV L i + bitE (L.testBit (i + 1)) * word (2 ^ (i + 1)) 0 0

theorem gcAccV_eq (L : ℕ) : ∀ n < 64,
    gcAccV L n = ∑ i ∈ Finset.range (n + 1), bitE (L.testBit i) * coordBasis i
  | 0, _ => by
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, coordBasis, pow_zero,
      eOfNat192_of_lt (show (1 : ℕ) < 2 ^ 64 by decide), eOfNat_one, mul_one]
    rfl
  | n + 1, hn => by
    rw [gcAccV, gcAccV_eq L n (by omega), Finset.sum_range_succ (n := n + 1), word_coordBasis hn]

/-- The honest values of the reconstruction, from `.n 98`. -/
def gcVals (L t : ℕ) : E :=
  if t % 3 = 0 then word (2 ^ (t / 3 + 1)) 0 0
  else if t % 3 = 1 then bitE (L.testBit (t / 3 + 1)) * word (2 ^ (t / 3 + 1)) 0 0
  else gcAccV L (t / 3 + 1)

theorem gcVals_0 (L i : ℕ) : gcVals L (3 * i) = word (2 ^ (i + 1)) 0 0 := by
  simp only [gcVals]; rw [ite_pos' (by omega), show 3 * i / 3 = i by omega]

theorem gcVals_1 (L i : ℕ) :
    gcVals L (3 * i + 1) = bitE (L.testBit (i + 1)) * word (2 ^ (i + 1)) 0 0 := by
  simp only [gcVals]; rw [ite_neg' (by omega), ite_pos' (by omega), show (3 * i + 1) / 3 = i by omega]

theorem gcVals_2 (L i : ℕ) : gcVals L (3 * i + 2) = gcAccV L (i + 1) := by
  simp only [gcVals]; rw [ite_neg' (by omega), ite_neg' (by omega), show (3 * i + 2) / 3 = i by omega]

theorem grind_check_complete_aux (rd : Reader) (args rets : List E)
    (h : MeaningGrindCheck rd args rets) : coreProgram.Rel rd "grind_check" args rets := by
  obtain ⟨s0, s1, nonce, N, rfl⟩ : ∃ s0 s1 nonce N, args = [s0, s1, nonce, N] := by
    match args, h with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨rfl, m, hm, hN, cv, hcv, hpow, p, ⟨hpK, hfr⟩, hloads⟩ := h
  rw [rel_iff_sem find_grind_check, core3_body,
    show Fn.params Data.core3 = [.n 0, .n 1, .n 2, .n 3] from rfl, gcBody]
  simp only [holdsList_append, Stmt.HoldsList]
  simp only [holds_ite_noRet (.n 5) [.atom (.const (.n 6) (word 0 0 0)),
    .atom (.assertEq (.n 2) (.n 6))] [] rfl rfl]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, holds_squeezeStateT _ _ _ (show 3 < 256 by decide),
    holds_fsCompressT _ _ _ _ (show 4 < 256 by decide), holds_canonicalLimbsT,
    holdsList_range_flatten 64 gcBit (fun i => by cases i <;> rfl), holds_gcBit, List.map_cons,
    List.map_nil, word_one, word_zero, true_and]
  set B := absorbCv cv 0 3
  set o0 := (digestScalars (absorbCv B nonce 4)).1
  set L := kToNat (o0.limb 0)
  have hL : L < 2 ^ 64 := (o0.limb 0).toBitVec.isLt
  set τ := setl (setv (setv (setl (setv (setv (setl (Val.ofArgs [s0, s1, nonce, N]) 4
    [1, N + 1, 0, s0, s1]) 9 7 (sqStateVals cv 3)) 16 14 (fsVals nonce B 4)) 30
    [ofK (o0.limb 0), o0 + ofK (o0.limb 0), word 1 0 1, ofK (o0.limb 1)]) 34 64
    (fun i => bitE (L.testBit i))) 98 189 (gcVals L)) 287 [p, 1, 1 + N, 1]
  have tb : ∀ i < 64, τ (.n (34 + i)) = bitE (L.testBit i) := fun i hi => by
    simp only [τ, setl, List.length_cons, List.length_nil]
    rw [set_n_lt (by omega), set_n_lt (by omega), set_n_in (by omega) (by omega),
      Nat.add_sub_cancel_left]
  have tg : ∀ t < 189, τ (.n (98 + t)) = gcVals L t := fun t ht => by
    simp only [τ, setl, List.length_cons, List.length_nil]
    rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have t28 : τ (.n 28) = o0 := by simp only [τ]; b1_look; rfl
  have t30 : τ (.n 30) = ofK (o0.limb 0) := by simp only [τ]; b1_look
  have t2 : τ (.n 2) = nonce := by simp only [τ]; b1_look
  have t5 : τ (.n 5) = N + 1 := by simp only [τ]; b1_look
  have t6 : τ (.n 6) = 0 := by simp only [τ]; b1_look
  have t287 : τ (.n 287) = p := by simp only [τ]; b1_look
  have hcall := (guarded_loop_iff (loop6_step rd N p)).mpr ⟨m, hm, hN, fun j hj => by
    rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hloads j hj⟩
  refine ⟨τ, ?_, ?_, ?_, ⟨?_, fun h5 => ?_, fun _ => trivial⟩, ?_, ?_, ⟨cv, ?_, fun k hk => ?_⟩,
    ⟨B, ?_, fun k hk1 hk2 => ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, fun i hi => ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, trivial⟩
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · rw [t5, hN]; exact isInK_add (gen_pow_isInK m) (by rw [← pow_zero gen]; exact gen_pow_isInK 0)
  · rw [t5, hN, e_add_eq_zero_iff, ← pow_zero gen] at h5
    have hm0 : m = 0 := gen_pow_inj (by omega) (by decide) h5
    subst hm0
    unfold powOk at hpow
    simp only [↓reduceIte, decide_eq_true_eq] at hpow
    have hn : nonce = 0 := by rw [eq_ofLimbs nonce, hpow.1, hpow.2.1, hpow.2.2, ← zero_eq_ofLimbs]
    rw [t6, t2, hn]
    exact ⟨rfl, add_zero 0, trivial⟩
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look; exact hcv
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
    show ((digestScalars (absorbCv cv 0 3)).1, (digestScalars (absorbCv cv 0 3)).2) = _
    rw [Prod.mk.eta]
  · rw [t2]
    simp only [τ]; b1_look
  · rw [t28]; exact (isCanonical128_digestScalars _).1
  · rw [t30, t28]
  · simp only [τ]; b1_look; rfl
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look; rfl
  · cases i with
    | zero =>
      show τ (.n (34 + 0)) = τ (.n (34 + 0)) * τ (.n (34 + 0))
      rw [tb 0 hi, bitE_mul_self]
    | succ i =>
      have e1 := tb (i + 1) hi
      have e2 := tg (3 * i) (by omega)
      have e3 := tg (3 * i + 1) (by omega)
      have e4 := tg (3 * i + 2) (by omega)
      rw [gcVals_0] at e2
      rw [gcVals_1] at e3
      rw [gcVals_2] at e4
      rw [show 34 + (i + 1) = 35 + i by omega] at e1
      rw [show 98 + 3 * i = 98 + 3 * i by rfl] at e2
      rw [show 98 + (3 * i + 1) = 99 + 3 * i by omega] at e3
      rw [show 98 + (3 * i + 2) = 100 + 3 * i by omega] at e4
      have ea : τ (.n (gcAcc i)) = gcAccV L i := by
        cases i with
        | zero => exact tb 0 (by omega)
        | succ i =>
          have := tg (3 * i + 2) (by omega)
          rw [gcVals_2, show 98 + (3 * i + 2) = 100 + 3 * i by omega] at this
          exact this
      refine ⟨by rw [e1, bitE_mul_self], e2, by rw [e3, e1, e2], by rw [e4, ea, e3, gcAccV]⟩
  · have e := tg 188 (by omega)
    rw [show (188 : ℕ) = 3 * 62 + 2 by rfl, gcVals_2, gcAccV_eq L 63 (by omega)] at e
    rw [show 98 + (3 * 62 + 2) = 286 by rfl] at e
    have hr := reconstruct_bits 0 hL
    simp only [Nat.zero_add, pow_zero, one_mul] at hr
    rw [e, t30, show (63 : ℕ) + 1 = 64 from rfl, hr, eOfNat192_of_lt hL]
    have : eOfNat L = ofK (o0.limb 0) := by rw [eOfNat, ofBits_kToNat]
    rw [this]
    exact e_add_self _
  · rw [t287]; exact hpK
  · intro k hk w hw
    rw [t287] at hw
    rw [gcRun_getElem, tb k (by rw [length_gcRun] at hk; exact hk)]
    exact hfr k (by rw [length_gcRun] at hk; exact hk) w hw
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look; exact hcall.1
  · simp only [τ]; b1_look; exact hcall.2

theorem grind_check_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "grind_check" args rets ↔ MeaningGrindCheck rd args rets :=
  ⟨grind_check_sound_aux rd args rets, grind_check_complete_aux rd args rets⟩

end
end LeanVM.Guest.B1
