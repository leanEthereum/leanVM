/-
  LeanVM.Protocol.Whir.Sound.Candidates

  The level-0 Johnson list of a committed word and the candidates the commitment binds: every
  list member is the lane-wise encoding of a candidate stack, and every candidate's encoding is a
  list member.
-/

module

public import LeanVM.Protocol.EndToEnd.Candidates
public import LeanVM.Protocol.ToArkLib.Whir.Interleaved

/-!
# The level-0 list and the candidates

The level-0 oracle of the deployed WHIR opening (`verify_whir` level `0`,
`python-verifier/verifier.py:1008-1065` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`)
is the committed word read lane by lane: lane `u` of column `v` is `laneOf W u v`, word `63 − u`
of leaf `v` (the program's `row.reverse.map ofK`). Its code is the novel-basis Reed-Solomon code
`C₀ = RS[E, D_{μ−6,R}, 2^(μ−6)]` (`range_enc`), and its list at agreement threshold `A` is
`iList C₀ A (laneWord μ R W)`.

* `isInK_of_agree`: a codeword of the `E`-code whose entries lie in `K` on at least `2^κ`
  coordinates has a `K`-valued message. The message's limbs `1` and `2` encode `K`-codewords
  vanishing on those coordinates (Annex B's remark: "limbs 1, 2 are codewords agreeing with `0` on
  more than `2^κ − 1` points"), hence vanish.
* `exists_candidate_of_mem_iList`: **every list member is the encoding of a candidate**, for a
  threshold `A ≥ 2^(μ−6)` (every Johnson threshold is: `LevelCode.two_pow_le_thr`).
* `mem_iList_of_candidate`: conversely, the encoding of a candidate is a list member.
* `encStack_injective`: the encoding determines the stack, so list members and candidates are in
  bijection.

The candidates are `LeanVM.Protocol.EndToEnd.Candidates`: the stack's block `u` (cells
`x + 2^(μ−6)·u`) is the message of lane `u`, `f(u, x) = q(x, u)` of Annex B "Optimizations".
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir
  LeanVM.Protocol.EndToEnd

@[expose] public section

/-! ## The level-0 word and code -/

/-- The level-0 interleaved word of a committed word: lane `u` of column `v`. -/
def laneWord (μ R : ℕ) (W : Word) : Fin (2 ^ laneBits) → Fin (2 ^ (μ - laneBits + R)) → E :=
  fun u v ↦ laneOf W u v

/-- The lane-wise encoding of a stack: lane `u` encodes block `u`. -/
def encStack (μ R : ℕ) (q : Column μ) : Fin (2 ^ laneBits) → Fin (2 ^ (μ - laneBits + R)) → E :=
  fun u ↦ enc (μ - laneBits) R (blockOf q u)

/-- `Agrees` is agreement of the lane word with the stack's encoding. -/
theorem agrees_iff_agreeOn (μ R : ℕ) (W : Word) (q : Column μ)
    (S : Finset (Fin (2 ^ (μ - laneBits + R)))) :
    Agrees μ R W q S ↔ AgreeOn (laneWord μ R W) (encStack μ R q) S :=
  ⟨fun h u v hv ↦ h v hv u, fun h v hv u ↦ h u v hv⟩

/-! ## `K`-valuedness -/

section Limbs

variable {κ R : ℕ}

/-- The limb `i` of a message, as a `K`-valued message. -/
def msgLimb (g : (Fin κ → Bool) → E) (i : Fin 3) : (Fin κ → Bool) → K := fun u ↦ (g u).limb i

/-- A message is the sum of its limbs in the basis `1, y, y²`. -/
theorem msg_eq_limbs (g : (Fin κ → Bool) → E) :
    g = (fun u ↦ ofK (msgLimb g 0 u)) + y • (fun u ↦ ofK (msgLimb g 1 u)) +
      (y ^ 2) • (fun u ↦ ofK (msgLimb g 2 u)) := by
  funext u
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, msgLimb]
  conv_lhs => rw [E.eq_sum_limbs (g u)]
  ring

/-- The encoding of a message, limb by limb: limb `i` of a codeword entry is the `K`-encoding of
limb `i` of the message. -/
theorem enc_eq_ofLimbs (g : (Fin κ → Bool) → E) (v : Fin (2 ^ (κ + R))) :
    enc κ R g v = E.ofLimbs (encK κ R (msgLimb g 0) v) (encK κ R (msgLimb g 1) v)
      (encK κ R (msgLimb g 2) v) := by
  conv_lhs => rw [msg_eq_limbs g]
  rw [map_add, map_add, map_smul, map_smul, enc_ofK, enc_ofK, enc_ofK, ofLimbs_eq]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Limb `i` of a codeword entry is the `K`-encoding of limb `i` of the message. -/
theorem limb_enc (g : (Fin κ → Bool) → E) (v : Fin (2 ^ (κ + R))) (i : Fin 3) :
    (enc κ R g v).limb i = encK κ R (msgLimb g i) v := by
  rw [enc_eq_ofLimbs, limb_ofLimbs]
  fin_cases i <;> rfl

/-- A `K`-message whose encoding vanishes on `2^κ` coordinates is zero. -/
theorem eq_zero_of_encK_vanish (h : κ + R ≤ 64) (a : (Fin κ → Bool) → K)
    (S : Finset (Fin (2 ^ (κ + R)))) (hS : 2 ^ κ ≤ S.card) (hv : ∀ v ∈ S, encK κ R a v = 0) :
    a = 0 := by
  have hmem : enc κ R (fun u ↦ ofK (a u)) ∈ ReedSolomon.code (domain κ R h) (2 ^ κ) := by
    rw [← range_enc h]; exact LinearMap.mem_range_self _ _
  have h0 : enc κ R (fun u ↦ ofK (a u)) = 0 :=
    eq_of_mem_code_of_agreeOn (domain κ R h) hmem (Submodule.zero_mem _) S hS fun v hvS ↦ by
      rw [enc_ofK]; simp [hv v hvS]
  have h1 : (fun u ↦ ofK (a u)) = 0 := enc_injective h (h0.trans (map_zero _).symm)
  funext u
  exact ofK_injective ((congrFun h1 u).trans (by simp))

/-- **`K`-valuedness.** If the encoding of a message lies in `K` on at least `2^κ` coordinates,
every entry of the message lies in `K`. -/
theorem isInK_of_agree (h : κ + R ≤ 64) (g : (Fin κ → Bool) → E)
    (S : Finset (Fin (2 ^ (κ + R)))) (hS : 2 ^ κ ≤ S.card) (hK : ∀ v ∈ S, IsInK (enc κ R g v)) :
    ∀ u, IsInK (g u) := by
  have h1 := eq_zero_of_encK_vanish h (msgLimb g 1) S hS fun v hv ↦ by
    rw [← limb_enc]; exact (hK v hv).1
  have h2 := eq_zero_of_encK_vanish h (msgLimb g 2) S hS fun v hv ↦ by
    rw [← limb_enc]; exact (hK v hv).2
  exact fun u ↦ ⟨congrFun h1 u, congrFun h2 u⟩

end Limbs

/-! ## Stacks from lane messages -/

section Stack

variable {μ : ℕ}

/-- The stack whose block `u` is the `K`-message `a u`: cell `i` is `a (i / 2^κ) (i % 2^κ)`. -/
def stackOf (hμ : laneBits ≤ μ) (a : Fin (2 ^ laneBits) → (Fin (μ - laneBits) → Bool) → K) :
    Column μ :=
  ⟨Vector.ofFn fun i : Fin (2 ^ μ) ↦
    a ⟨i / 2 ^ (μ - laneBits), by
      have hi := i.isLt
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      rwa [Nat.add_sub_cancel' hμ]⟩
      ((bitsEquiv (μ - laneBits)).symm ⟨i % 2 ^ (μ - laneBits), Nat.mod_lt _ (Nat.two_pow_pos _)⟩)⟩

/-- Block `u` of `stackOf a` is `a u`. -/
theorem blockOf_stackOf (hμ : laneBits ≤ μ)
    (a : Fin (2 ^ laneBits) → (Fin (μ - laneBits) → Bool) → K) (u : Fin (2 ^ laneBits)) :
    blockOf (stackOf hμ a) u = fun x ↦ ofK (a u x) := by
  funext x
  have hx := bitsToNat_lt x
  have hlt : bitsToNat x + 2 ^ (μ - laneBits) * u < 2 ^ μ := by
    have hu := u.isLt
    calc bitsToNat x + 2 ^ (μ - laneBits) * u < 2 ^ (μ - laneBits) * (u + 1) := by nlinarith
      _ ≤ 2 ^ (μ - laneBits) * 2 ^ laneBits := Nat.mul_le_mul_left _ hu
      _ = 2 ^ μ := by rw [← pow_add, Nat.sub_add_cancel hμ]
  simp only [EndToEnd.blockOf, stackOf, Vector.getD, Vector.toArray_ofFn, Array.getD_eq_getD_getElem?,
    Array.getElem?_ofFn, hlt, dite_true, Option.getD_some]
  congr 2
  · apply Fin.ext
    simp only
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hx, zero_add]
  · apply (bitsEquiv (μ - laneBits)).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    simp only [bitsEquiv_val]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

/-- The blocks determine the stack. -/
theorem eq_of_blockOf_eq (hμ : laneBits ≤ μ) {q q' : Column μ}
    (h : ∀ u, blockOf q u = blockOf q' u) : q = q' := by
  obtain ⟨v⟩ := q
  obtain ⟨v'⟩ := q'
  congr 1
  apply Vector.ext
  intro i hi
  -- Cell `i` is cell `x + 2^κ u` of block `u = i / 2^κ`, `x = i % 2^κ`.
  have hu : i / 2 ^ (μ - laneBits) < 2 ^ laneBits := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_sub_cancel' hμ]
    exact hi
  have hx : bitsToNat ((bitsEquiv (μ - laneBits)).symm
      ⟨i % 2 ^ (μ - laneBits), Nat.mod_lt _ (Nat.two_pow_pos _)⟩) = i % 2 ^ (μ - laneBits) := by
    rw [← bitsEquiv_val, Equiv.apply_symm_apply]
  have := congrFun (h ⟨i / 2 ^ (μ - laneBits), hu⟩) ((bitsEquiv (μ - laneBits)).symm
      ⟨i % 2 ^ (μ - laneBits), Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
  simp only [EndToEnd.blockOf, hx, Nat.mod_add_div] at this
  have := ofK_injective this
  simpa [Vector.getD, hi] using this

end Stack

/-! ## The bridge -/

variable {μ R A : ℕ}

/-- The encoding of a stack determines the stack. -/
theorem encStack_injective (hμ : laneBits ≤ μ) (h : μ - laneBits + R ≤ 64) :
    Function.Injective (encStack μ R) := fun _ _ hqq ↦
  eq_of_blockOf_eq hμ fun u ↦ enc_injective h (congrFun hqq u)

/-- The encoding of a stack is an interleaved codeword of the level-0 code. -/
theorem isInterleavedCodeword_encStack (h : μ - laneBits + R ≤ 64) (q : Column μ) :
    IsInterleavedCodeword (ReedSolomon.code (domain (μ - laneBits) R h) (2 ^ (μ - laneBits)))
      (encStack μ R q) := fun u ↦ by
  rw [← range_enc h]; exact LinearMap.mem_range_self _ _

/-- **Every level-0 list member is the encoding of a candidate.** An interleaved codeword of the
level-0 code agreeing with the lane word of `W` on at least `A ≥ 2^(μ−6)` columns is
`encStack q` for a candidate `q` of `W`. -/
theorem exists_candidate_of_mem_iList (hμ : laneBits ≤ μ) (h : μ - laneBits + R ≤ 64)
    (hA : 2 ^ (μ - laneBits) ≤ A) {W : Word}
    {U : Fin (2 ^ laneBits) → Fin (2 ^ (μ - laneBits + R)) → E}
    (hU : U ∈ iList (ReedSolomon.code (domain (μ - laneBits) R h) (2 ^ (μ - laneBits))) A
      (laneWord μ R W)) :
    ∃ q ∈ Candidates μ R A W, U = encStack μ R q := by
  rw [mem_iList] at hU
  obtain ⟨hcw, S, hS, hagree⟩ := hU
  -- Every row is the encoding of a message.
  have hmsg : ∀ u, ∃ g, enc (μ - laneBits) R g = U u := fun u ↦ by
    have := hcw u
    rw [← range_enc h] at this
    exact this
  choose g hg using hmsg
  -- The messages are `K`-valued.
  have hK : ∀ u x, IsInK (g u x) := fun u ↦
    isInK_of_agree h (g u) S (hA.trans hS) fun v hv ↦ by
      rw [hg u, ← hagree u v hv, isInK_iff]
      exact ⟨_, rfl⟩
  let a : Fin (2 ^ laneBits) → (Fin (μ - laneBits) → Bool) → K := fun u x ↦ (g u x).limb 0
  have hga : ∀ u, g u = fun x ↦ ofK (a u x) := fun u ↦ funext fun x ↦ by
    obtain ⟨c, hc⟩ := (isInK_iff _).mp (hK u x)
    simp [a, hc]
  refine ⟨stackOf hμ a, ⟨S, hS, (agrees_iff_agreeOn _ _ _ _ _).mpr ?_⟩, ?_⟩
  · intro u v hv
    rw [hagree u v hv, encStack, blockOf_stackOf, ← hga, hg]
  · funext u
    rw [encStack, blockOf_stackOf, ← hga, hg]

/-- **The encoding of a candidate is a level-0 list member.** -/
theorem mem_iList_of_candidate (h : μ - laneBits + R ≤ 64) {W : Word} {q : Column μ}
    (hq : q ∈ Candidates μ R A W) :
    encStack μ R q ∈ iList (ReedSolomon.code (domain (μ - laneBits) R h) (2 ^ (μ - laneBits))) A
      (laneWord μ R W) := by
  obtain ⟨S, hS, hagree⟩ := hq
  rw [mem_iList]
  exact ⟨isInterleavedCodeword_encStack h q, S, hS, (agrees_iff_agreeOn _ _ _ _ _).mp hagree⟩

end
end LeanVM.Protocol.Whir.Sound
