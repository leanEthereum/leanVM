/-
  LeanVM.Guest.B1.KeccakGkr.VkFirst

  `verify_keccak`'s first claim record (G:2955-2973) and the dot products it uses.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkHead
public import LeanVM.Guest.B1.KeccakGkr.VkSpec

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Dot products of loaded words -/

/-- **A dot product of loaded pairs**: the words at `p`, `q` the offsets give are `P k`, `Q k`. -/
theorem pairsDotT_holds {p q : V} {offs : List (ℕ × ℕ)} {b : ℕ} {P Q : ℕ → E}
    (hP : ∀ k < offs.length, ∀ v, LoadHolds rd (σ p) (offs.getD k (0, 0)).1 v → v = P k)
    (hQ : ∀ k < offs.length, ∀ v, LoadHolds rd (σ q) (offs.getD k (0, 0)).2 v → v = Q k)
    (h2 : 2 ≤ offs.length) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (pairsDotT p q offs b) next kret) :
    σ (.n (pairsDotV b offs.length)) = ∑ k ∈ range offs.length, P k * Q k ∧ next := by
  rw [pairsDotT, holdsList_range_flatten _ _ (fun k ↦ by split <;> rfl)] at h
  obtain ⟨hall, hn⟩ := h
  have acc : ∀ k, 1 ≤ k → k < offs.length →
      σ (.n (b + 4 * k + 2)) = ∑ j ∈ range (k + 1), P j * Q j := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro _ hk
      have hb := hall (k + 1) hk
      simp only [show k + 1 ≠ 0 by omega, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
        and_true] at hb
      obtain ⟨l1, l2, m, a⟩ := hb
      rw [show b + 4 * (k + 1) + 2 = b + 4 * (k + 1) + 2 from rfl, a, m,
        hP (k + 1) hk _ l1, hQ (k + 1) hk _ l2, Finset.sum_range_succ _ (k + 1)]
      congr 1
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have h0 := hall 0 (by omega)
        simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0
        obtain ⟨l1', l2', m'⟩ := h0
        simp only [↓reduceIte, zero_add, Finset.sum_range_one]
        rw [m', hP 0 (by omega) _ l1', hQ 0 (by omega) _ l2']
      · simp only [show ¬ (k + 1 = 1) by omega, ↓reduceIte]
        rw [show b + 4 * (k + 1) - 2 = b + 4 * k + 2 by omega]
        exact ih (by omega) (by omega)
  refine ⟨?_, hn⟩
  rw [pairsDotV, acc (offs.length - 1) (by omega) (by omega), show offs.length - 1 + 1 =
    offs.length by omega]

theorem list_sum_eq_range : ∀ (l : List E), l.sum = ∑ i ∈ range l.length, l.getD i 0
  | [] => by simp
  | a :: l => by
    rw [List.sum_cons, list_sum_eq_range l, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

theorem sumE_eqKernel (pt : List E) : sumE (eqKernel pt) = 1 := by
  rw [sumE_eq_sum, list_sum_eq_range, eqKernel_length, ← sum_eqAt pt]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  rw [eqKernel_getD]
  simp only [Finset.mem_range.1 hw, ↓reduceIte]

/-! ## Equality trees on the heap -/

/-- An `eqtree`'s last level: from the point's words `rs` at `p` (from `po`), the weights
`eqKernel rs` at `o` from `2^n - 2`. -/
theorem eqtreeT_last {p o : V} {po b n : ℕ} (hn : 1 ≤ n) {rs : List E} (hrs : rs.length = n)
    (hpt : ∀ t < n, LoadHolds rd (σ p) (po + t) (rs.getD t 0)) {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (eqtreeT p o po b n) next kret) :
    (∀ i < 2 ^ n, LoadHolds rd (σ o) (2 ^ n - 2 + i) ((eqKernel rs).getD i 0)) ∧ next := by
  obtain ⟨hA, hnx⟩ := (holdsList_atoms (eqtreeT_atoms p o po b n) next kret).1 h
  refine ⟨fun i hi ↦ ?_, hnx⟩
  have := eqtree_sound hn hA hrs hpt n hn le_rfl i hi
  rwa [show rs.take n = rs by rw [← hrs]; exact List.take_length] at this

theorem word_2p30 : word 1073741824 0 = gen ^ 30 := by
  rw [show (1073741824 : ℕ) = 2 ^ 30 from rfl]; exact word_two_pow (by decide)

/-- **The first claim's record** (G:2955-2973). -/
theorem vkFirstT_holds {τ : ℕ} (hτ1 : 9 ≤ τ) {chis outs rl : List E} {r0 : E}
    (hchi : τ ≤ chis.length) (hzv : ∀ i < 4, LoadHolds rd (σ (.n 9)) i (chis.getD i 0))
    (hrl : rl.length = 5) (hrlL : ∀ i < 5, LoadHolds rd (σ (.n 87)) i (rl.getD i 0))
    (hseg : LoadHolds rd (σ (.n 67)) 0 r0)
    (hpt : ReadsAt rd (σ (.n 61)) ((chis.take τ).drop 4 ++ [r0]))
    (houts : outs.length = 25) (hol : ReadsAt rd (σ (.n 8)) outs)
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ vkFirstT next kret) :
    ClaimRec rd ((1 : ℕ) = 1) (σ (.n 161)) (vkFirst (chis.take τ) outs (σ (.n 158)) [r0] rl)
        (τ - 3) ∧
      (∀ lane < 32, LoadHolds rd (σ (.n 234)) (30 + lane) ((eqKernel rl).getD lane 0)) ∧ next := by
  rw [vkFirstT] at h
  simp only [holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨-, e202, l202, l58, -, h⟩ := h
  -- the instance weights
  have hmu4 : ((chis.take τ).take 4).length = 4 := by simp; omega
  obtain ⟨hmu, h⟩ := eqtreeT_last (rs := (chis.take τ).take 4) (by omega) hmu4 (fun t ht ↦ by
    have : ((chis.take τ).take 4).getD t 0 = chis.getD t 0 := by
      simp [List.getD_eq_getElem?_getD, show t < 4 from ht, show t < τ by omega]
    rw [this]; simpa using hzv t ht) h
  obtain ⟨hcw, h⟩ := copyWordsT_holds h
  obtain ⟨-, h⟩ := h
  -- the lanes
  obtain ⟨hlane, h⟩ := eqtreeT_last (rs := rl) (by omega) hrl (fun t ht ↦ by
    simpa using hrlL t (by omega)) h
  obtain ⟨e380, e381, l381, -, h⟩ := h
  -- the segment
  obtain ⟨hsw, h⟩ := eqtreeT_last (rs := [r0]) (n := 1) le_rfl rfl (fun t ht ↦ by
    obtain rfl : t = 0 := by omega
    simpa using hseg) h
  -- the output lanes' dot
  obtain ⟨hdot, h⟩ := pairsDotT_holds (P := fun k ↦ (eqKernel rl).getD k 0)
    (Q := fun k ↦ outs.getD k 0) (fun k hk v hv ↦ by
      simp only [consecOffs, List.length_map, List.length_range] at hk
      have := hlane k (by omega)
      simp only [consecOffs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some] at hv
      simp only [show 2 ^ 5 - 2 = 30 from rfl] at this
      exact loadHolds_unique hv this)
    (fun k hk v hv ↦ by
      simp only [consecOffs, List.length_map, List.length_range] at hk
      simp only [consecOffs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some, zero_add] at hv
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact loadHolds_unique hv (hol k (by omega)))
    (by simp [consecOffs]) h
  obtain ⟨l485, e486, e487, l487, hn⟩ := h
  simp only [consecOffs, List.length_map, List.length_range, pairsDotV] at hdot
  have hl30 : ∀ lane < 32, LoadHolds rd (σ (.n 234)) (30 + lane) ((eqKernel rl).getD lane 0) :=
    fun lane hl ↦ by simpa using hlane lane (by simpa using hl)
  refine ⟨?_, hl30, hn⟩
  have h1600 : ∀ j ∈ List.range keccakBits, j / 64 < 25 := fun j hj ↦ by
    have := List.mem_range.1 hj; simp only [keccakBits] at this; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨σ (.n 61), l58, ?_⟩, σ (.n 341), (eqKernel rl).take 25, l381,
    by simp [eqKernel_length, hrl], ?_, ?_⟩
  · simp [vkFirst, eqKernel_length, hmu4, pack]
  · simp [vkFirst]; omega
  · suffices hv : (vkFirst (chis.take τ) outs (σ (.n 158)) [r0] rl).value = σ (.n 447) by
      rw [hv]; exact l487
    rw [e487, e486, hdot]
    have := hsw 1 (by norm_num)
    simp only [show 2 ^ 1 - 2 + 1 = 1 from rfl] at this
    rw [loadHolds_unique l485 this]
    simp only [vkFirst, keccakSegments_eq, show 2 - 1 = 1 from rfl]
    symm
    rw [dot_eq _ _ (by simp [eqKernel_length, hrl, houts])]
    simp only [List.length_take, eqKernel_length, hrl, show min 25 (2 ^ 5) = 25 from rfl]
    refine congrArg (σ (.n 158) + (eqKernel [r0]).getD 1 0 * ·)
      (Finset.sum_congr rfl fun k hk ↦ ?_)
    simp [List.getD_eq_getElem?_getD, Finset.mem_range.1 hk]
  · rw [e202, word_one] at l202
    simp only [vkFirst, sumE_eqKernel]; exact l202
  · intro i hi
    have h1 := (hcw i hi).1
    have h2 := (hcw i hi).2
    have h3 := hmu i (by simp [pack] at hi; omega)
    simp only [show 2 ^ 4 - 2 = 14 from rfl] at h3
    rw [loadHolds_unique h1 h3] at h2
    exact h2
  · simpa [vkFirst] using hpt
  · rw [e381, e380, word_2p30]
    intro k hk
    simp only [List.length_take, eqKernel_length, hrl] at hk
    rw [loadHolds_mul_gen_pow, List.getElem_take]
    have := hl30 k (by omega)
    rwa [List.getElem_eq_getD 0]
  · simp only [decide_true, ↓reduceIte, vkFirst, firstWeights]
    refine List.map_congr_left fun j hj ↦ ?_
    simp [List.getD_eq_getElem?_getD, h1600 j hj]

end
end LeanVM.Guest.B1.VerifySub
