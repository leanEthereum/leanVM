/-
  LeanVM.Guest.B1.VerifySub.PhLinkCycles

  `verify_sub`'s cycle bits: the `24` hinted bits at `cbits` are the bits of the cycle count.
-/

module

public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Guest.B1.Link.RoundsLoop
public import LeanVM.Guest.B1.Link.Arith.Side
public import LeanVM.Protocol.Keccak.Multilinear
import LeanVM.Guest.CoreLemmas
import Mathlib.Tactic.IntervalCases

/-!
# The cycle bits

`vsCbT` (statements `182 .. 374`, checked by the kernel): the hint of `24` bits at `cbits`, each
read and pinned to `b = b²`, the product of their factors `1 + b·(g^(2^k) + 1)` asserted equal to
`g_cycles`. `cbFacts`: when `g_cycles = g^N` with `N < 2^34`, then `N < 2^24` and the words at
`cbits` are `bitsE N 24`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The factors' constants, `g^(2^k) + 1` as words. -/
def cbC : List ℕ := [3, 5, 17, 257, 65537, 4294967297, 26, 324, 69648, 4311744768,
  281474976776219, 111669150021, 69053, 4300293457, 18696262193434, 72058698282434911,
  98799108396552526, 7508852687479268, 313291816297575, 6076785667380547346,
  13470757684146121987, 12749500389507444803, 16291502563427555124, 5203926764172326182]

set_option maxRecDepth 100000 in
theorem cbC_eq : ∀ k < 24, word (cbC.getD k 0) 0 = gen ^ 2 ^ k + 1 := by
  intro k hk
  have hb : 2 ^ k < u128Bound := by
    unfold u128Bound
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hk) (by norm_num)
  rw [← gpow, ← Link.Arith.gpowE_eq_gpow hb]
  interval_cases k <;> decide +kernel

/-- The bit block `k`'s bit, `cbits[k]` as read. -/
def cbV (k : ℕ) : ℕ := if k = 0 then 241 else 240 + 7 * k

/-- The running product after block `k`. -/
def cbA (k : ℕ) : ℕ := 246 + 7 * k

/-- Block `0`. -/
def cbBlk0 : List Stmt :=
  [.atom (.load (.n 241) (.n 8) 0), .atom (.mul (.n 242) (.n 241) (.n 241)),
    .atom (.load (.n 242) (.n 8) 0), .atom (.const (.n 243) (word 1 0)),
    .atom (.const (.n 244) (word 3 0)), .atom (.mul (.n 245) (.n 241) (.n 244)),
    .atom (.add (.n 246) (.n 243) (.n 245))]

/-- Block `k ≥ 1`, its values from `v = 240 + 7k`. -/
def cbBlk (k : ℕ) : List Stmt :=
  [.atom (.load (.n (240 + 7 * k)) (.n 8) k),
    .atom (.mul (.n (241 + 7 * k)) (.n (240 + 7 * k)) (.n (240 + 7 * k))),
    .atom (.load (.n (241 + 7 * k)) (.n 8) k), .atom (.const (.n (242 + 7 * k)) (word 1 0)),
    .atom (.const (.n (243 + 7 * k)) (word (cbC.getD k 0) 0)),
    .atom (.mul (.n (244 + 7 * k)) (.n (240 + 7 * k)) (.n (243 + 7 * k))),
    .atom (.add (.n (245 + 7 * k)) (.n (242 + 7 * k)) (.n (244 + 7 * k))),
    .atom (.mul (.n (246 + 7 * k)) (.n (cbA (k - 1))) (.n (245 + 7 * k)))]

/-- `verify_sub`'s statements 182 to 374. -/
def vsCbT : List Stmt :=
  [.atom (.hint (.bitsExp (.n 240) 24 (.heap (.n 8) 0 24)))] ++ cbBlk0 ++
    ((List.range 23).map fun i ↦ cbBlk (i + 1)).flatten ++ [.atom (.assertEq (.n 407) (.n 240))]

theorem vsCbT_eq : (vsPre.drop 182).take 193 = vsCbT := stmtsEqb_sound (by decide +kernel)

/-- What block `k` holds. -/
def CbOk (rd : Reader) (σ : Val) (k : ℕ) : Prop :=
  LoadHolds rd (σ (.n 8)) k (σ (.n (cbV k))) ∧ σ (.n (cbV k)) * σ (.n (cbV k)) = σ (.n (cbV k)) ∧
    σ (.n (cbA k)) = (if k = 0 then 1 else σ (.n (cbA (k - 1)))) *
      (1 + σ (.n (cbV k)) * (gen ^ 2 ^ k + 1))

theorem cbBlk0_ok {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ cbBlk0 True kret) : CbOk rd σ 0 := by
  simp only [cbBlk0, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l1, m2, l3, c4, c5, m6, a7, -⟩ := h
  have hb : σ (.n 242) = σ (.n 241) := loadHolds_unique l3 l1
  simp only [CbOk, cbA, cbV, ↓reduceIte, one_mul, Nat.mul_zero, Nat.add_zero, pow_zero]
  refine ⟨l1, by rw [← m2, hb], ?_⟩
  have e5 := cbC_eq 0 (by norm_num)
  simp only [cbC, List.getD_cons_zero] at e5
  rw [a7, m6, c4, c5, e5, word_one, pow_zero, pow_one]

theorem cbBlk_ok {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k < 24) (h : Stmt.HoldsList C rd σ (cbBlk k) True kret) : CbOk rd σ k := by
  simp only [cbBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l1, m2, l3, c4, c5, m6, a7, m8, -⟩ := h
  have hb : σ (.n (241 + 7 * k)) = σ (.n (240 + 7 * k)) := loadHolds_unique l3 l1
  have hv : cbV k = 240 + 7 * k := by simp [cbV]; omega
  rw [CbOk, hv]
  refine ⟨l1, by rw [← m2, hb], ?_⟩
  have hk0 : k ≠ 0 := by omega
  simp only [hk0, ↓reduceIte]
  rw [show cbA k = 246 + 7 * k from rfl, m8, a7, m6, c4, c5, cbC_eq k hk, word_one]

theorem cbBlk_noRet (k : ℕ) : Stmt.noRetList (cbBlk k) = true := by
  simp [cbBlk, Stmt.noRetList, Stmt.noRet]

/-- The block facts from the template. -/
theorem cb_ok {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ vsCbT True kret) :
    (∀ k < 24, CbOk rd σ k) ∧ σ (.n 407) = σ (.n 240) := by
  rw [vsCbT, holdsList_append, holdsList_append, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds] at h
  obtain ⟨-, h⟩ := h
  rw [holdsList_noRet cbBlk0 (by decide)] at h
  obtain ⟨h0, h⟩ := h
  rw [holdsList_range_flatten _ _ (fun i ↦ cbBlk_noRet (i + 1))] at h
  obtain ⟨hb, h⟩ := h
  simp only [Atom.Holds] at h
  refine ⟨fun k hk ↦ ?_, eq_of_add_zero h.1⟩
  rcases k with _ | i
  · exact cbBlk0_ok h0
  · exact cbBlk_ok (by omega) hk (hb i (by omega))

/-- The number the bits `d 0 .. d (k - 1)` spell, the lowest first. -/
def bsum (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => bsum d k + 2 ^ k * d k

theorem bsum_lt (d : ℕ → ℕ) (hd : ∀ k, d k ≤ 1) : ∀ k, bsum d k < 2 ^ k
  | 0 => by simp [bsum]
  | k + 1 => by
    have := bsum_lt d hd k
    have := hd k
    simp only [bsum, pow_succ]
    nlinarith

theorem bsum_succ' (d : ℕ → ℕ) : ∀ m, bsum d (m + 1) = d 0 + 2 * bsum (fun k ↦ d (k + 1)) m
  | 0 => by simp [bsum]
  | m + 1 => by
    rw [bsum, bsum_succ' d m, bsum, pow_succ]
    ring

/-- **`bitsE` of the number bits spell** is the bits. -/
theorem bitsE_bsum : ∀ (m : ℕ) (d : ℕ → ℕ), (∀ k, d k ≤ 1) →
    KeccakGkr.bitsE (bsum d m) m = (List.range m).map fun k ↦ if d k = 1 then (1 : E) else 0
  | 0, _, _ => rfl
  | m + 1, d, hd => by
    rw [bsum_succ', List.range_succ_eq_map, List.map_cons, List.map_map, KeccakGkr.bitsE]
    have h0 := hd 0
    have e1 : (d 0 + 2 * bsum (fun k ↦ d (k + 1)) m) % 2 = d 0 := by omega
    have e2 : (d 0 + 2 * bsum (fun k ↦ d (k + 1)) m) / 2 = bsum (fun k ↦ d (k + 1)) m := by omega
    rw [e1, e2, bitsE_bsum m _ (fun k ↦ hd (k + 1))]
    rfl

/-- The bits' number. -/
def cbN (σ : Val) : ℕ := bsum (fun k ↦ Link.bv (σ (.n (cbV k)))) 24

theorem cb_acc {rd : Reader} {σ : Val} (H : ∀ k < 24, CbOk rd σ k) :
    ∀ k < 24, σ (.n (cbA k)) = gen ^ bsum (fun k ↦ Link.bv (σ (.n (cbV k)))) (k + 1) := by
  intro k hk
  induction k with
  | zero =>
    obtain ⟨-, hb, he⟩ := H 0 (by norm_num)
    simp only [↓reduceIte, one_mul] at he
    rw [he, Link.bit_factor hb.symm]
    simp [bsum, Link.bv]
  | succ k ih =>
    obtain ⟨-, hb, he⟩ := H (k + 1) hk
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at he
    rw [he, ih (by omega), Link.bit_factor hb.symm, ← pow_add]
    congr 1

/-- **The cycle bits**: on `g_cycles = g^N`, `N < 2^34`, the words at `cbits` are `N`'s `24`
bits, and `N < 2^24`. -/
theorem cbFacts {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ vsCbT True kret) {N : ℕ} (hN : N < 2 ^ 34)
    (hg : σ (.n 240) = gen ^ N) : N < 2 ^ 24 ∧ ReadsAt rd (σ (.n 8)) (KeccakGkr.bitsE N 24) := by
  obtain ⟨H, he⟩ := cb_ok h
  have hacc := cb_acc H 23 (by norm_num)
  have hlt := bsum_lt (fun k ↦ Link.bv (σ (.n (cbV k)))) (fun k ↦ Link.bv_le _) 24
  have hNe : N = cbN σ := by
    refine Digest.gen_pow_inj' hN (by unfold cbN; omega) ?_
    rw [← hg, ← he]
    exact hacc
  refine ⟨by rw [hNe]; exact hlt, ?_⟩
  rw [hNe, cbN, bitsE_bsum 24 _ (fun k ↦ Link.bv_le _)]
  intro k hk
  simp only [List.length_map, List.length_range] at hk
  simp only [List.getElem_map, List.getElem_range]
  obtain ⟨hl, hb, -⟩ := H k hk
  convert hl using 1
  have := bitE_of_mul_self hb
  by_cases h1 : σ (.n (cbV k)) = 1
  · simp [Link.bv, h1]
  · rw [this]; simp [Link.bv, h1, Value.bitE]

end
end LeanVM.Guest.B1.VerifySub
