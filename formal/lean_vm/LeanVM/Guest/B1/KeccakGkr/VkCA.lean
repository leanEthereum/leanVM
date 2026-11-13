/-
  LeanVM.Guest.B1.KeccakGkr.VkCA

  `verify_keccak`'s head, completely: `y` in the exponent, the copies, the point, the squeezes, the
  committed word.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkHead
public import LeanVM.Guest.B1.KeccakGkr.VkCSpec

/-!
# The head, completely

`vkBits_complete`: on a valuation satisfying the equations of `vkBitsT` but its pins, the bits of
`y = τ - 3` hinted, `y` in the exponent (`y_g`, `step_g = g^(y/8)`, `rem_g = g^(y%8)`) is computed and the
section holds (its pins and its check).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

theorem bitE_mul_self (b : Bool) : bitE b * bitE b = bitE b := by cases b <;> simp [bitE]

theorem word3 : word 3 0 = gen ^ 2 ^ 0 + 1 := by
  rw [word_eOfNat, show (3 : ℕ) = 2 ^ 1 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one,
    ← word_eOfNat, word_two_pow (by decide)]; simp

theorem word5 : word 5 0 = gen ^ 2 ^ 1 + 1 := by
  rw [word_eOfNat, show (5 : ℕ) = 2 ^ 2 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one,
    ← word_eOfNat, word_two_pow (by decide)]; norm_num

theorem word17 : word 17 0 = gen ^ 2 ^ 2 + 1 := by
  rw [word_eOfNat, show (17 : ℕ) = 2 ^ 4 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one,
    ← word_eOfNat, word_two_pow (by decide)]; norm_num

theorem mulG {d x y : ℕ} (hx : x < d) (hy : y < d)
    (h : Good rd S w σ (.mul (.n d) (.n x) (.n y))) : σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [Good] at h
  rwa [ite_pos' ⟨hx, hy⟩] at h

theorem div8_bits {y : ℕ} (hy : y < 32) :
    bitsVal (fun j ↦ y.testBit (j + 3)) 2 = y / 8 := by
  interval_cases y <;> rfl

theorem mod8_bits {y : ℕ} (hy : y < 32) :
    bitsVal (fun j ↦ y.testBit j) 3 = y % 8 := by
  interval_cases y <;> rfl

set_option maxRecDepth 20000 in
/-- **`y` in the exponent, completely**: `step_g = g^(y/8)` (value 34), `rem_g = g^(y%8)` (48). -/
theorem vkBits_complete {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28)
    (hg : ∀ s ∈ vkBitsT, pinB s = false → GoodS rd S w σ s) (h6 : σ (.n 6) = gen ^ τ)
    (hbits : ∀ j < 5, σ (.n (21 + j)) = bitE ((τ - 3).testBit j)) :
    σ (.n 18) = gen ^ (τ - 4) ∧ σ (.n 20) = gen ^ (τ - 3) ∧
      σ (.n 34) = gen ^ ((τ - 3) / krStep) ∧ σ (.n 48) = gen ^ ((τ - 3) % krStep) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ vkBitsT next kret := by
  have gd : ∀ a, Stmt.atom a ∈ vkBitsT → pinB (.atom a) = false → Good rd S w σ a :=
    fun a h hp ↦ hg _ h hp
  have c16 := gd (.const (.n 17) (word 8070450532247928836 0)) (by simp [vkBitsT]) rfl
  have m17 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 18) (.n 6) (.n 17)) (by simp [vkBitsT]) rfl)
  have c18 := gd (.const (.n 19) (word 2 0)) (by simp [vkBitsT]) rfl
  have m19 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 20) (.n 18) (.n 19)) (by simp [vkBitsT]) rfl)
  have c25 := gd (.const (.n 26) (word 1 0)) (by simp [vkBitsT]) rfl
  have c26 := gd (.const (.n 27) (word 3 0)) (by simp [vkBitsT]) rfl
  have m27 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 28) (.n 24) (.n 27)) (by simp [vkBitsT]) rfl)
  have a28 := gd (.add (.n 29) (.n 26) (.n 28)) (by simp [vkBitsT]) rfl
  have c29 := gd (.const (.n 30) (word 1 0)) (by simp [vkBitsT]) rfl
  have c30 := gd (.const (.n 31) (word 5 0)) (by simp [vkBitsT]) rfl
  have m31 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 32) (.n 25) (.n 31)) (by simp [vkBitsT]) rfl)
  have a32 := gd (.add (.n 33) (.n 30) (.n 32)) (by simp [vkBitsT]) rfl
  have m33 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 34) (.n 29) (.n 33)) (by simp [vkBitsT]) rfl)
  have c34 := gd (.const (.n 35) (word 1 0)) (by simp [vkBitsT]) rfl
  have c35 := gd (.const (.n 36) (word 3 0)) (by simp [vkBitsT]) rfl
  have m36 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 37) (.n 21) (.n 36)) (by simp [vkBitsT]) rfl)
  have a37 := gd (.add (.n 38) (.n 35) (.n 37)) (by simp [vkBitsT]) rfl
  have c38 := gd (.const (.n 39) (word 1 0)) (by simp [vkBitsT]) rfl
  have c39 := gd (.const (.n 40) (word 5 0)) (by simp [vkBitsT]) rfl
  have m40 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 41) (.n 22) (.n 40)) (by simp [vkBitsT]) rfl)
  have a41 := gd (.add (.n 42) (.n 39) (.n 41)) (by simp [vkBitsT]) rfl
  have m42 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 43) (.n 38) (.n 42)) (by simp [vkBitsT]) rfl)
  have c43 := gd (.const (.n 44) (word 1 0)) (by simp [vkBitsT]) rfl
  have c44 := gd (.const (.n 45) (word 17 0)) (by simp [vkBitsT]) rfl
  have m45 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 46) (.n 23) (.n 45)) (by simp [vkBitsT]) rfl)
  have a46 := gd (.add (.n 47) (.n 44) (.n 46)) (by simp [vkBitsT]) rfl
  have m47 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 48) (.n 43) (.n 47)) (by simp [vkBitsT]) rfl)
  have m48 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 49) (.n 34) (.n 34)) (by simp [vkBitsT]) rfl)
  have m49 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 50) (.n 49) (.n 49)) (by simp [vkBitsT]) rfl)
  have m50 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 51) (.n 50) (.n 50)) (by simp [vkBitsT]) rfl)
  have m51 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 52) (.n 51) (.n 48)) (by simp [vkBitsT]) rfl)
  have c52 := gd (.const (.n 53) (word 2 0)) (by simp [vkBitsT]) rfl
  have m53 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 54) (.n 18) (.n 53)) (by simp [vkBitsT]) rfl)
  simp only [Good] at c16 c18 c25 c26 a28 c29 c30 a32 c34 c35 a37 c38 c39 a41 c43 c44 a46 c52
  set y := τ - 3 with hy
  have hy32 : y < 32 := by omega
  have b0 := hbits 0 (by norm_num)
  have b1 := hbits 1 (by norm_num)
  have b2 := hbits 2 (by norm_num)
  have b3 := hbits 3 (by norm_num)
  have b4 := hbits 4 (by norm_num)
  simp only [Nat.add_zero, Nat.reduceAdd] at b0 b1 b2 b3 b4
  have h17 : σ (.n 18) = gen ^ (τ - 4) := by
    rw [m17, h6, c16, show τ = τ - 4 + 4 by omega, pow_add, mul_assoc, mul_comm (gen ^ 4),
      word_ginv4_mul, mul_one]
    congr 1
  have h19 : σ (.n 20) = gen ^ (τ - 3) := by
    rw [m19, h17, c18, word_gen, ← pow_succ]; congr 1; omega
  have h33 : σ (.n 34) = gen ^ (y / 8) := by
    rw [m33, a32, m31, c30, c29, a28, m27, c26, c25, b3, b4, word_one, word3, word5,
      ← div8_bits hy32, ← prod_bitE_gen_pow]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have h47 : σ (.n 48) = gen ^ (y % 8) := by
    rw [m47, a46, m45, c44, c43, m42, a41, m40, c39, c38, a37, m36, c35, c34, b0, b1, b2, word_one,
      word3, word5, word17, ← mod8_bits hy32, ← prod_bitE_gen_pow]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have h51 : σ (.n 52) = gen ^ y := by
    rw [m51, m50, m49, m48, h33, h47]
    simp only [← pow_add]
    congr 1; omega
  refine ⟨h17, h19, by simpa only [krStep] using h33, by simpa only [krStep] using h47,
    fun {next kret} hn ↦ ?_⟩
  simp only [vkBitsT, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨c16, m17, c18, m19, trivial, ?_, ?_, ?_, ?_, ?_, c25, c26, m27, a28, c29, c30, m31, a32,
    m33, c34, c35, m36, a37, c38, c39, m40, a41, m42, c43, c44, m45, a46, m47, m48, m49, m50, m51,
    c52, m53, ?_, hn⟩
  · rw [b0, bitE_mul_self]
  · rw [b1, bitE_mul_self]
  · rw [b2, bitE_mul_self]
  · rw [b3, bitE_mul_self]
  · rw [b4, bitE_mul_self]
  · rw [h51, m53, c52, h17, word_gen, ← pow_succ, show τ - 4 + 1 = y by omega]
    exact e_add_self _

/-- **A squeeze with nothing waiting, completely.** -/
theorem sqZero_complete {capb o : ℕ} (hσ : ∀ v, σ v = σ (.n v.idx))
    (hr : resid (atomsL (sqZeroT capb o)) = [])
    (hg : ∀ s ∈ sqZeroT capb o, GoodS rd S w σ s) (hz : ∀ k < 4, σ (.n (69 + k)) = 0) :
    σ (.n (o + 13)) = (⟨(cap5 capb).map σ, []⟩ : Fs).squeeze.1 ∧
      (cap5 (o + 8)).map σ = (⟨(cap5 capb).map σ, []⟩ : Fs).squeeze.2.cap ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (sqZeroT capb o) next kret := by
  have hall : (sqZeroT capb o).all isAtom = true := by simp [sqZeroT, challengeT, keccakA, isAtom]
  have H : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (sqZeroT capb o) next kret :=
    fun hn ↦ block_holds hall hσ hg (by rw [hr]; simp) hn
  obtain ⟨q1, q2, -⟩ := sqZeroT_holds rfl hz (H (next := True) (kret := fun _ ↦ True) trivial)
  exact ⟨q1, q2, H⟩

theorem sq_kernel0 : resid (atomsL (sqZeroT 12 73)) = [] := by
  decide +kernel

theorem sq_kernelL : ∀ i < 5,
    resid (atomsL (sqZeroT (if i = 0 then 81 else 82 + 14 * i) (88 + 14 * i))) = [] := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- **`verify_keccak`'s head, completely.** -/
theorem vkHead_complete (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ s ∈ vkHeadT, pinB s = false → GoodS rd S w σ s)
    (hS7 : ∀ d off, Atom.load d (.n 7) off ∉ S) (hS5 : ∀ d off, Atom.load d (.n 5) off ∉ S)
    {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (h6 : σ (.n 6) = gen ^ τ)
    (hbits : ∀ j < 5, σ (.n (21 + j)) = bitE ((τ - 3).testBit j)) {chis : List E}
    (hchi : ReadsAt rd (σ (.n 7)) chis) (h4 : 4 ≤ chis.length) {committed : E}
    (hcur : LoadHolds rd (σ (.n 5)) 0 committed) :
    σ (.n 18) = gen ^ (τ - 4) ∧ σ (.n 20) = gen ^ (τ - 3) ∧
    σ (.n 34) = gen ^ ((τ - 3) / krStep) ∧ σ (.n 48) = gen ^ ((τ - 3) % krStep) ∧
    (∀ i < 4, σ (.n (55 + i)) = chis.getD i 0) ∧
    σ (.n 63) = 1 + σ (.n 18) ∧ σ (.n 64) = 1 ∧ σ (.n 66) = σ (.n 7) * gen ^ 4 ∧
    σ (.n 67) = σ (.n 61) * σ (.n 18) ∧
    (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).squeezeN 1 =
      ([σ (.n 86)], ⟨(cap5 81).map σ, []⟩) ∧
    (⟨(cap5 81).map σ, []⟩ : Fs).squeezeN 5 =
      ((List.range 5).map (fun i ↦ σ (.n (101 + 14 * i))), ⟨(cap5 152).map σ, []⟩) ∧
    σ (.n 158) = committed ∧ FsPackOk σ (.n 158) (158 + 1) dsObserve ∧
    (σ (.n 159), σ (.n 160)) = Keccak.scalarCells committed dsObserve ∧
    ∀ {next : Prop} {kret : List E → Prop},
      (∀ i < 4, LoadHolds rd (σ (.n 9)) i (σ (.n (55 + i)))) →
      LoadHolds rd (σ (.n 67)) 0 (σ (.n 86)) →
      (∀ i < 5, LoadHolds rd (σ (.n 87)) i (σ (.n (101 + 14 * i)))) → next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkHeadT next kret := by
  have hnp2 : (copyWordsT (.n 7) (.n 9) 0 0 55 4 ++ vkPointT ++ vkSqueezesT ++
      fsNextT (.n 5) 0 158).all (fun s ↦ !pinB s) = true := by decide +kernel
  have gx : ∀ s, s ∈ copyWordsT (.n 7) (.n 9) 0 0 55 4 ++ vkPointT ++ vkSqueezesT ++
      fsNextT (.n 5) 0 158 → GoodS rd S w σ s := fun s hs ↦
    hg s (by simp only [vkHeadT, List.mem_append] at hs ⊢; tauto)
      (by have := List.all_eq_true.mp hnp2 s hs; simpa using this)
  -- the copies
  have gcp : ∀ i < 5, σ (.n (12 + i)) = σ (.n i) := fun i hi ↦
    hg (.atom (.copy (.n (12 + i)) (.n i))) (by
      simp only [vkHeadT, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩))))) rfl
  -- the bits
  obtain ⟨h18, h20, h34, h48, HB⟩ := vkBits_complete (C := fun _ _ _ ↦ True) hτ1 hτ2
    (fun s hs hp ↦ hg s (by simp only [vkHeadT, List.mem_append]; tauto) hp) h6 hbits
  -- the copied words
  have gcw : ∀ s ∈ copyWordsT (.n 7) (.n 9) 0 0 55 4, GoodS rd S w σ s := fun s hs ↦
    gx s (by simp only [List.mem_append]; tauto)
  have e55 : ∀ i < 4, σ (.n (55 + i)) = chis.getD i 0 := by
    intro i hi
    have g := gcw (.atom (.load (.n (55 + i)) (.n 7) (0 + i))) (by
      simp only [copyWordsT, List.mem_flatten, List.mem_map, List.mem_range]
      exact ⟨_, ⟨i, hi, rfl⟩, by simp⟩)
    exact load_val (w := w) g (hS7 _ _)
      (by rw [zero_add, List.getD_eq_getElem _ _ (by omega)]; exact hchi i (by omega))
  -- the point
  have gp : ∀ s ∈ vkPointT, GoodS rd S w σ s := fun s hs ↦
    gx s (by simp only [List.mem_append]; tauto)
  have gp' := gp
  simp only [vkPointT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true, GoodS] at gp'
  obtain ⟨c59, m60, -, c62, a63, c64, c65, m66, -, m67, c68, z69, z70, z71, z72⟩ := gp'
  have m60' := mulG (by norm_num) (by norm_num) m60
  have m66' := mulG (by norm_num) (by norm_num) m66
  have m67' := mulG (by norm_num) (by norm_num) m67
  simp only [Good] at c59 c62 a63 c64 c65 c68 z69 z70 z71 z72
  have hz : ∀ k < 4, σ (.n (69 + k)) = 0 := by
    intro k hk
    interval_cases k
    · rw [z69, word_zero]
    · rw [z70, word_zero]
    · rw [z71, word_zero]
    · rw [z72, word_zero]
  have e63 : σ (.n 63) = 1 + σ (.n 18) := by rw [a63, c62, word_one]
  have e66 : σ (.n 66) = σ (.n 7) * gen ^ 4 := by rw [m66', c65, word_16]
  -- the squeezes
  have gsq : ∀ s ∈ vkSqueezesT, GoodS rd S w σ s := fun s hs ↦
    gx s (by simp only [List.mem_append]; tauto)
  -- the segment's squeeze
  have hcap12 : (cap5 12).map σ = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] := by
    simp only [cap5, List.map_cons, List.map_nil]
    rw [gcp 0 (by omega), gcp 1 (by omega), gcp 2 (by omega), gcp 3 (by omega), gcp 4 (by omega)]
  have gs0 : ∀ s ∈ sqZeroT 12 73, GoodS rd S w σ s := fun s hs ↦
    gsq s (List.mem_append_left _ (List.mem_append_left _ hs))
  obtain ⟨q0c, q0p, H0⟩ := sqZero_complete (C := fun _ _ _ ↦ True) hσ sq_kernel0 gs0 hz
  rw [hcap12] at q0c q0p
  -- the lanes' squeezes
  have step : ∀ i < 5,
      σ (.n (88 + 14 * i + 13)) =
          (⟨(cap5 (if i = 0 then 81 else 82 + 14 * i)).map σ, []⟩ : Fs).squeeze.1 ∧
        (cap5 (88 + 14 * i + 8)).map σ =
          (⟨(cap5 (if i = 0 then 81 else 82 + 14 * i)).map σ, []⟩ : Fs).squeeze.2.cap ∧
        ∀ {next : Prop} {kret : List E → Prop}, next →
          Stmt.HoldsList (fun _ _ _ ↦ True) rd σ
            (sqZeroT (if i = 0 then 81 else 82 + 14 * i) (88 + 14 * i)) next kret := by
    intro i hi
    exact sqZero_complete hσ (sq_kernelL i hi)
      (fun s hs ↦ gsq s (List.mem_append_right _ (List.mem_flatten.mpr
        ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, List.mem_append_left _ hs⟩))) hz
  have q1 : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).squeezeN 1 =
      ([σ (.n 86)], ⟨(cap5 81).map σ, []⟩) := by
    simp only [Fs.squeezeN]
    rw [← q0c]
    have : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).squeeze.2 =
        ⟨(cap5 81).map σ, []⟩ := by
      rw [show ((⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).squeeze.2) =
        ⟨(⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).squeeze.2.cap, []⟩ from rfl,
        ← q0p]
    rw [this]
  have q5 : (⟨(cap5 81).map σ, []⟩ : Fs).squeezeN 5 =
      ((List.range 5).map (fun i ↦ σ (.n (101 + 14 * i))), ⟨(cap5 152).map σ, []⟩) := by
    have st : ∀ i < 5, σ (.n (101 + 14 * i)) =
          (⟨(cap5 (if i = 0 then 81 else 82 + 14 * i)).map σ, []⟩ : Fs).squeeze.1 ∧
        (cap5 (96 + 14 * i)).map σ =
          (⟨(cap5 (if i = 0 then 81 else 82 + 14 * i)).map σ, []⟩ : Fs).squeeze.2.cap := by
      intro i hi
      obtain ⟨a, b, -⟩ := step i hi
      exact ⟨by rw [show 101 + 14 * i = 88 + 14 * i + 13 by omega]; exact a,
        by rw [← b]; congr 2; omega⟩
    have hs : ∀ i < 5, (⟨(cap5 (if i = 0 then 81 else 82 + 14 * i)).map σ, []⟩ : Fs).squeeze.2 =
        ⟨(cap5 (96 + 14 * i)).map σ, []⟩ := by
      intro i hi
      rw [show (⟨(cap5 (if i = 0 then 81 else 82 + 14 * i)).map σ, []⟩ : Fs).squeeze.2 =
        ⟨(⟨(cap5 (if i = 0 then 81 else 82 + 14 * i)).map σ, []⟩ : Fs).squeeze.2.cap, []⟩ from rfl,
        ← (st i hi).2]
    have s0 := st 0 (by omega); have s1 := st 1 (by omega); have s2 := st 2 (by omega)
    have s3 := st 3 (by omega); have s4 := st 4 (by omega)
    have h0 := hs 0 (by omega); have h1 := hs 1 (by omega); have h2 := hs 2 (by omega)
    have h3 := hs 3 (by omega); have h4 := hs 4 (by omega)
    simp only [↓reduceIte, Nat.reduceMul, Nat.reduceAdd, Nat.one_ne_zero,
      OfNat.ofNat_ne_zero] at s0 s1 s2 s3 s4 h0 h1 h2 h3 h4
    simp only [Fs.squeezeN, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, Nat.reduceMul, Nat.reduceAdd]
    rw [h0, h1, h2, h3, h4, ← s0.1, ← s1.1, ← s2.1, ← s3.1, ← s4.1]
  -- the committed word
  have gfs : ∀ s ∈ fsNextT (.n 5) 0 158, GoodS rd S w σ s := fun s hs ↦
    gx s (List.mem_append_right _ hs)
  obtain ⟨fv, fcells, FN⟩ := fsNext_complete (C := fun _ _ _ ↦ True) gfs (hS5 _ _) hcur
  have fpk : FsPackOk σ (.n 158) (158 + 1) dsObserve :=
    ((holds_fsNextT _ _ _ _ _).1 (FN (next := True) (kret := fun _ ↦ True) trivial)).1.2
  refine ⟨h18, h20, h34, h48, e55, e63, by rw [c64, word_one], e66, m67', q1, q5, fv, fpk,
    fcells, fun {next kret} lw l86 lr hn ↦ ?_⟩
  rw [vkHeadT, holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_append, holdsList_map_atoms]
  refine ⟨fun i hi ↦ by simp only [Atom.Holds]; exact gcp i hi, HB ?_⟩
  -- the copied words
  rw [copyWordsT, holdsList_range_flatten _ _ (fun _ ↦ rfl)]
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨?_, by rw [zero_add]; exact lw i hi⟩
    rw [zero_add, e55 i hi, List.getD_eq_getElem _ _ (by omega)]
    exact hchi i (by omega)
  -- the point
  simp only [vkPointT, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨c59, m60', trivial, c62, a63, c64, c65, m66', ?_, fun _ ↦ trivial, m67', c68, z69, z70,
    z71, z72, ?_⟩
  · rw [e63, h18]
    exact isInK_add ((isInK_iff _).mpr ⟨1, ofK_one.symm⟩) ((isInK_iff _).mpr ⟨_, gen_pow_eq_ofK _⟩)
  -- the squeezes
  rw [vkSqueezesT, holdsList_append, holdsList_append, holdsList_range_flatten _ _ (fun _ ↦ rfl)]
  refine H0 ?_
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨l86, trivial, fun i hi ↦ ?_, ?_⟩
  · rw [holdsList_append]
    refine (step i hi).2.2 ?_
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact lr i hi
  -- the committed word
  exact FN hn

end
end LeanVM.Guest.B1.VerifySub
