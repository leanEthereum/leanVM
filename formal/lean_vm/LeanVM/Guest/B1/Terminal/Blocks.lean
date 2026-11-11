/-
  LeanVM.Guest.B1.Terminal.Blocks

  The claims' blocks of `check_opening_terminal` (G:3482-3519): each adds its claim's term to the
  running sum and multiplies the running power of `λ` by `lam_cl`.
-/

module

public import LeanVM.Guest.B1.Terminal.Template

/-!
# The claims' blocks

The words the blocks read are named by `valOf` (the word read at a place, by choice; a read
word is it, `valOf_eq`). Over the exponents `e` of `kappa_base` (`σ (35 + i) = g^(e i)`), claim
`j`'s low length is `cLow e j`. `claimsT_sound` gives the sum's value: the start plus each claim's
`claimTerm` at its power `λ^(1 + rk j)`, `rk` counting the claims kept before it, and the final
power.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The word at `p·g^k`, if one is read there (`0` otherwise). -/
noncomputable def valOf (rd : Reader) (p : E) (k : ℕ) : E :=
  open Classical in if h : ∃ v, LoadHolds rd p k v then h.choose else 0

theorem valOf_eq {p : E} {k : ℕ} {w : E} (h : LoadHolds rd p k w) : valOf rd p k = w := by
  have hex : ∃ v, LoadHolds rd p k v := ⟨w, h⟩
  simp only [valOf, hex, ↓reduceDIte]
  exact loadHolds_unique hex.choose_spec h

theorem eq_valOf {p : E} {k : ℕ} {w : E} (h : LoadHolds rd p k w) : w = valOf rd p k :=
  (valOf_eq h).symm

/-- Slot `s`'s eq factor over the six slot coordinates, top bit first. -/
def slotProd (s1 s0 : ℕ → E) (s : ℕ) : E :=
  let f := fun k ↦ if s.testBit k then s1 k else s0 k
  f 5 * f 4 * f 3 * f 2 * f 1 * f 0

/-- Claim `j`'s low length over the exponents `e` of `kappa_base`. -/
def cLow (e : ℕ → ℕ) (j : ℕ) : ℕ := e (claimKappaSrc j) + claimKappaAdj j

/-- Claim `j`'s term of the sum at the power `L`: the chain's value at `20` or `22` at its low
length, the public input's chain value (`34`), or the slot factor over the slot points (`24`, `25`)
and the table chain's value, and the column's selector. -/
noncomputable def claimTerm (rd : Reader) (σ : Val) (e : ℕ → ℕ) (L : E) (j : ℕ) : E :=
  match termKind j with
  | 0 => L * valOf rd (σ (.n 20)) (cLow e j) * σ (.n (selV (termCol j)))
  | 1 => L * valOf rd (σ (.n 22)) (cLow e j) * σ (.n (selV (termCol j)))
  | 2 => L * σ (.n 34) * σ (.n (selV (termCol j)))
  | 3 => L * (slotProd (valOf rd (σ (.n 24))) (valOf rd (σ (.n 25))) (termSlot j) *
      valOf rd (σ (.n 22)) (cLow e j)) * σ (.n (selV 4))
  | _ => 0

/-- **A low length**: `kb[src]·g^adj`. -/
theorem kapT_sound {src adj r : ℕ} (hadj : adj < 64) {rest : List Stmt} {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ ((kapT src adj r).1 ++ rest) next kret) :
    σ (.n (kapT src adj r).2.1) = σ (.n (kbV src)) * gen ^ adj ∧
      Stmt.HoldsList C rd σ rest next kret := by
  unfold kapT at h ⊢
  by_cases h0 : adj = 0
  · subst h0
    simp only [↓reduceIte, List.nil_append, pow_zero, mul_one] at h ⊢
    exact ⟨by simp, h⟩
  · simp only [h0, ↓reduceIte, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds,
      Atom.Holds] at h ⊢
    obtain ⟨c0, m1, h⟩ := h
    exact ⟨by rw [m1, c0, word_two_pow hadj], h⟩

theorem zrT_sound {ch kr sel lr r acc n : ℕ} {L : E} (hkr : σ (.n kr) = gen ^ n)
    (hl : σ (.n lr) = L) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (zrT ch kr sel lr r acc) next kret) :
    σ (.n (r + 4)) = σ (.n acc) + L * valOf rd (σ (.n ch)) n * σ (.n sel) ∧
      σ (.n (r + 5)) = L * σ (.n 9) ∧ next := by
  simp only [zrT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨e0, l1, e2, e3, e4, e5, hn⟩ := h
  rw [e0, hkr, loadHolds_mul_gen_pow, Nat.add_zero] at l1
  exact ⟨by rw [e4, e3, e2, hl, valOf_eq l1], by rw [e5, hl], hn⟩

theorem slotPt_load {s k : ℕ} {v : E} (h : LoadHolds rd (σ (.n (slotPt s k))) k v) :
    v = if s.testBit k then valOf rd (σ (.n 24)) k else valOf rd (σ (.n 25)) k := by
  unfold slotPt at h
  by_cases hb : s.testBit k
  · simp only [hb, ↓reduceIte] at h ⊢; exact eq_valOf h
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact eq_valOf h

theorem qT_sound {s kr lr r acc n : ℕ} {L : E} (hkr : σ (.n kr) = gen ^ n)
    (hl : σ (.n lr) = L) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (qT s kr lr r acc) next kret) :
    σ (.n (r + 16)) = σ (.n acc) + L * (slotProd (valOf rd (σ (.n 24))) (valOf rd (σ (.n 25))) s *
      valOf rd (σ (.n 22)) n) * σ (.n (selV 4)) ∧ σ (.n (r + 17)) = L * σ (.n 9) ∧ next := by
  simp only [qT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l0, l1, e2, l3, e4, l5, e6, l7, e8, l9, e10, e11, l12, e13, e14, e15, e16, e17, hn⟩ := h
  rw [e11, hkr, loadHolds_mul_gen_pow, Nat.add_zero] at l12
  refine ⟨?_, by rw [e17, hl], hn⟩
  rw [e16, e15, e14, e13, e10, e8, e6, e4, e2, hl, valOf_eq l12, slotPt_load l0, slotPt_load l1,
    slotPt_load l3, slotPt_load l5, slotPt_load l7, slotPt_load l9]
  rfl

theorem pT_sound {sel lr r acc : ℕ} {L : E} (hl : σ (.n lr) = L) {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (pT sel lr r acc) next kret) :
    σ (.n (r + 2)) = σ (.n acc) + L * σ (.n 34) * σ (.n sel) ∧
      σ (.n (r + 3)) = L * σ (.n 9) ∧ next := by
  simp only [pT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨e0, e1, e2, e3, hn⟩ := h
  exact ⟨by rw [e2, e1, e0, hl], by rw [e3, hl], hn⟩

/-- An array's entry below a bound every entry is below. -/
theorem getD_fst_lt {l : List (ℕ × ℕ)} {n : ℕ} (hn : 0 < n) (h : (l.all fun p ↦ decide (p.1 < n)) = true)
    (j : ℕ) : (l.getD j (0, 0)).1 < n := by
  rw [List.getD_eq_getElem?_getD]
  cases hj : l[j]? with
  | none => exact hn
  | some p =>
    have := List.all_eq_true.mp h p (List.mem_of_getElem? hj)
    simpa using this

theorem claimKappaSrc_lt (j : ℕ) : claimKappaSrc j < 8 :=
  getD_fst_lt (l := Data.arr_CLAIM_KAPPA_SRC) (by decide) (by decide +kernel) j

theorem claimKappaAdj_lt (j : ℕ) : claimKappaAdj j < 64 :=
  getD_fst_lt (l := Data.arr_CLAIM_KAPPA_ADJ) (by decide) (by decide +kernel) j

/-- A claim's low length's `g`-power. -/
theorem claimKap_sound {e : ℕ → ℕ} (he : ∀ i < 8, σ (.n (kbV i)) = gen ^ e i) {j r : ℕ}
    {rest : List Stmt} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ ((claimKap j r).1 ++ rest) next kret) :
    σ (.n (claimKap j r).2.1) = gen ^ cLow e j ∧ Stmt.HoldsList C rd σ rest next kret := by
  obtain ⟨e1, h⟩ := kapT_sound (claimKappaAdj_lt j) h
  exact ⟨by rw [claimKap, e1, he _ (claimKappaSrc_lt j), ← pow_add]; rfl, h⟩

/-- **One claim's block**: the sum gains the claim's term, and the power is multiplied by
`lam_cl` unless the claim is an output lane's. -/
theorem claimT_sound {e : ℕ → ℕ} (he : ∀ i < 8, σ (.n (kbV i)) = gen ^ e i) {j r acc lr : ℕ}
    {L : E} (hl : σ (.n lr) = L) {rest : List Stmt} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ ((claimT j r acc lr).1 ++ rest) next kret) :
    σ (.n (claimT j r acc lr).2.2.1) = σ (.n acc) + claimTerm rd σ e L j ∧
      σ (.n (claimT j r acc lr).2.2.2) = (if termKind j < 4 then L * σ (.n 9) else L) ∧
      Stmt.HoldsList C rd σ rest next kret := by
  rcases hk : termKind j with _ | _ | _ | _ | k
  · simp only [claimT, claimTerm, hk, List.append_assoc] at h ⊢
    obtain ⟨hkr, h⟩ := claimKap_sound he h
    rw [holdsList_append] at h
    obtain ⟨e1, e2, h⟩ := zrT_sound hkr hl h
    exact ⟨e1, by simpa using e2, h⟩
  · simp only [claimT, claimTerm, hk, List.append_assoc] at h ⊢
    obtain ⟨hkr, h⟩ := claimKap_sound he h
    rw [holdsList_append] at h
    obtain ⟨e1, e2, h⟩ := zrT_sound hkr hl h
    exact ⟨e1, by simpa using e2, h⟩
  · simp only [claimT, claimTerm, hk] at h ⊢
    rw [holdsList_append] at h
    obtain ⟨e1, e2, h⟩ := pT_sound hl h
    exact ⟨e1, by simpa using e2, h⟩
  · simp only [claimT, claimTerm, hk, List.append_assoc] at h ⊢
    obtain ⟨hkr, h⟩ := claimKap_sound he h
    rw [holdsList_append] at h
    obtain ⟨e1, e2, h⟩ := qT_sound hkr hl h
    exact ⟨e1, by simpa using e2, h⟩
  · simp only [claimT, claimTerm, hk, List.nil_append] at h ⊢
    exact ⟨by simp, by simpa [show ¬ (k + 1 + 1 + 1 + 1 < 4) by omega] using hl, h⟩

/-- **The claims' blocks**: over the claims `s, …, s + n - 1`, the power `λ^(1 + rk s)` at `lr`
and `rk` counting the kept claims, the sum's value is the start plus every claim's term at its
power, and the final power is `λ^(1 + rk (s + n))`. -/
theorem claimsT_sound {e : ℕ → ℕ} (he : ∀ i < 8, σ (.n (kbV i)) = gen ^ e i) {rk : ℕ → ℕ}
    {lam : E} (h9 : σ (.n 9) = lam) :
    ∀ (n s r acc lr : ℕ) {next : Prop} {kret : List E → Prop},
      (∀ j < s + n, rk (j + 1) = rk j + if termKind j < 4 then 1 else 0) →
      σ (.n lr) = lam ^ (1 + rk s) →
      Stmt.HoldsList C rd σ (claimsT (List.range' s n) r acc lr).1 next kret →
      σ (.n (claimsT (List.range' s n) r acc lr).2.2.1) =
          σ (.n acc) + ∑ i ∈ range n, claimTerm rd σ e (lam ^ (1 + rk (s + i))) (s + i) ∧
        σ (.n (claimsT (List.range' s n) r acc lr).2.2.2) = lam ^ (1 + rk (s + n)) ∧ next
  | 0, s, r, acc, lr, next, kret, _, hl, h => by
    simp only [List.range'_zero, claimsT, Stmt.HoldsList] at h ⊢
    exact ⟨by simp, by simpa using hl, h⟩
  | n + 1, s, r, acc, lr, next, kret, hrk, hl, h => by
    simp only [List.range'_succ, claimsT] at h ⊢
    obtain ⟨e1, e2, h⟩ := claimT_sound he hl h
    have hl' : σ (.n (claimT s r acc lr).2.2.2) = lam ^ (1 + rk (s + 1)) := by
      rw [e2, hrk s (by omega), h9]
      split <;> ring
    obtain ⟨f1, f2, hn⟩ := claimsT_sound he h9 n (s + 1) _ _ _
      (fun j hj ↦ hrk j (by omega)) hl' h
    refine ⟨?_, by rw [f2, show s + 1 + n = s + (n + 1) by omega], hn⟩
    rw [f1, e1, sum_range_succ', add_zero, add_assoc, add_comm (claimTerm _ _ _ _ s)]
    simp only [show ∀ i, s + 1 + i = s + (i + 1) from fun i ↦ by omega]

end
end LeanVM.Guest.B1.VerifySub
