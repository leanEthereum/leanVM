/-
  LeanVM.Guest.B1.Sig.SpWotsComplete

  `sp_wots`'s template is complete (`sp_wots_completeT`): for digits of sum `128` and any chain
  values, its body holds of a valuation whose arguments are `pp`, the address `(a0, a1)` and the
  digits' encoding, returning the one-time leaf of the values over cells (`spLeafCell`).
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsGroupComplete
public import LeanVM.Guest.B1.Sig.SpWotsSound
public import LeanVM.Guest.B1.Sig.CompleteKit

/-!
# `sp_wots`'s template, complete

The valuation: the arguments; the copies and the powers; each digit group with the digits' word
(`spKd`) and the chain values loaded at its arm's starts (`spGroupsC`), the first setting the
padding run; the checks, which hold since the digits are the encoding's (`spCheck_complete`); the
leaf's message over that run (`spLeaf_complete`); the copy. The returned leaf is then read off by
soundness (`sp_wots_soundT`): its digits and chain values are the loaded ones.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The digits -/

/-- The digits' base-4 number, digit `0` lowest. -/
def spDn (d : Nat → Nat) : Nat := ∑ i ∈ Finset.range 64, d i * 4 ^ i

/-- Group `p`'s digit word: its `spN p` base-4 digits from digit `3p`. -/
def spK (d : Nat → Nat) (p : Nat) : Nat := spDn d / 4 ^ (3 * p) % 4 ^ spN p

theorem spK_lt (d : Nat → Nat) (p : Nat) : spK d p < 4 ^ spN p := Nat.mod_lt _ (by positivity)

theorem spK_digit (d : Nat → Nat) {p t : Nat} (ht : t < spN p) :
    spK d p / 4 ^ t % 4 = spDn d / 4 ^ (3 * p + t) % 4 := by
  unfold spK
  obtain ⟨m, hm⟩ : ∃ m, spN p = t + (m + 1) := ⟨spN p - t - 1, by omega⟩
  rw [hm, pow_add, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← pow_add, pow_succ,
    Nat.mod_mul_left_mod]

theorem spDn_digit {d : Nat → Nat} (hd : ∀ i, d i < 4) {i : Nat} (hi : i < 64) :
    spDn d / 4 ^ i % 4 = d i :=
  base4_digit hd 64 i hi

theorem spLeafCell_congr {pp a0 a1 : E} {d d' : Nat → Nat} {s s' : Nat → E}
    (hd : ∀ i < 64, d i = d' i) (hs : ∀ i < 64, s i = s' i) :
    spLeafCell pp a0 a1 d s = spLeafCell pp a0 a1 d' s' := by
  have e : (List.range 64).map (fun i => chainT (spStepCell pp a0 a1) i (3 - d i) (d i) (s i)) =
      (List.range 64).map (fun i => chainT (spStepCell pp a0 a1) i (3 - d' i) (d' i) (s' i)) :=
    List.map_congr_left fun i hi => by
      simp only [hd i (List.mem_range.mp hi), hs i (List.mem_range.mp hi)]
  unfold spLeafCell
  rw [e]

theorem spX_congr {d d' : Nat → Nat} (hd : ∀ i < 64, d i = d' i) : spX d 64 = spX d' 64 := by
  have e : (List.range 64).map (spField d) = (List.range 64).map (spField d') :=
    List.map_congr_left fun i hi => by unfold spField; rw [hd i (List.mem_range.mp hi)]
  unfold spX
  rw [e]

/-! ## A group's post, kept -/

/-- The end of group `p`. -/
def spEnd (p : Nat) : Nat :=
  (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).2

theorem spEnd_eq (p : Nat) :
    spEnd p = spArmB (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 (4 ^ spN p) :=
  spGroupT_end ..

theorem spState_succ_end {p : Nat} (hp : p < 21) : (spState (p + 1)).2.2 = spEnd p := by
  rw [spState_succ, spEnd, spN_of_lt hp]

theorem spState_le_end (p : Nat) : (spState p).2.2 + 6 ≤ spEnd p := by
  rw [spEnd_eq]
  have := spArmB_ge (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 (4 ^ spN p)
  have := spL_ge (p == 0) (spState p).2.2
  omega

theorem spState_mono : ∀ {p q : Nat}, p ≤ q → q ≤ 21 → (spState p).2.2 ≤ (spState q).2.2
  | p, q, h, hq => by
      induction q with
      | zero => have : p = 0 := by omega
                subst this; exact le_rfl
      | succ q ih =>
          rcases Nat.lt_or_ge p (q + 1) with h' | h'
          · have := ih (by omega) (by omega)
            rw [spState_succ_end (by omega)]
            have := spState_le_end q
            omega
          · have : p = q + 1 := by omega
            subst this; exact le_rfl

/-- Every group's arms lie above the padding run. -/
theorem spL_state : ∀ q, q ≤ 21 → 21 ≤ spL (q == 0) (spState q).2.2
  | 0, _ => by rw [spState_zero]; decide
  | q + 1, hq => by
      have ih := spL_state q (by omega)
      have h1 : spL (q + 1 == 0) (spState (q + 1)).2.2 = (spState (q + 1)).2.2 := by simp [spL]
      rw [h1, spState_succ_end (by omega), spEnd_eq]
      have := spArmB_ge (3 * q) (spN q) (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1 (4 ^ spN q)
      omega

/-- A later group's running product and encoding lie below its base, and its base above `26`. -/
theorem spState_in {p : Nat} (hp0 : 0 < p) (hp : p ≤ 21) :
    NBv (spState p).2.2 (spState p).1 ∧ NBv (spState p).2.2 (spState p).2.1 ∧ 27 ≤ (spState p).2.2 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hl := spL_state q (by omega)
  have he := spEnc_lt_end (3 * q) 3 (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1
  have hg := spArmB_ge (3 * q) 3 (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1 (4 ^ 3)
  have hend : (spState (q + 1)).2.2 = spArmB (3 * q) 3 (q == 0) (spState q).2.2 (spState q).1
      (spState q).2.1 (4 ^ 3) := by
    rw [spState_succ_end (by omega), spEnd_eq, spN_of_lt (by omega)]
  rw [hend]
  rw [spState_succ]
  unfold spEnc at he
  exact ⟨⟨_, by omega, rfl⟩, ⟨_, by unfold spEnc; omega, rfl⟩, by omega⟩

/-- What group `q` establishes: its digit word, its arm's tips canonical and starts loaded. -/
def SpGP (d : Nat → Nat) (vals : Nat → E) (q : Nat) (σ : Val) : Prop :=
  σ (.n (spState q).2.2) = ofK (addressOfIndex (spK d q)) ∧
    SpArmPost (3 * q) (spN q) (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1 (spK d q)
      (fun t => vals (3 * q + t)) σ

theorem spPost_q {q t : Nat} (k : Nat) (hk : k < 4 ^ spN q) (ht : t < spN q) :
    ((spState q).2.2 ≤ spSlot (q == 0) (spState q).2.2 t 2 ∧ spSlot (q == 0) (spState q).2.2 t 2 < spEnd q) ∧
      ∃ j, spStartOf (3 * q) (spN q) (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1 k
        (spArmB (3 * q) (spN q) (q == 0) (spState q).2.2 (spState q).1 (spState q).2.1 k) t = .n j ∧
        (spState q).2.2 ≤ j ∧ j < spEnd q := by
  obtain ⟨⟨h1, h2⟩, j, ej, h3, h4⟩ := spPost_bounds (3 * q) (spN q) (q == 0) (spState q).2.2
    (spState q).1 (spState q).2.1 hk ht
  have := spL_ge (q == 0) (spState q).2.2
  rw [← spEnd_eq] at h2 h4
  exact ⟨⟨by omega, h2⟩, j, ej, by omega, h4⟩

theorem SpGP.keep {d : Nat → Nat} {vals : Nat → E} {q : Nat}
    {σ σ' : Val} (h : SpGP d vals q σ) {lo hi : Nat} (he : Ext lo hi σ σ') (hlo : spEnd q ≤ lo) :
    SpGP d vals q σ' := by
  have hB := spState_le_end q
  refine ⟨by rw [he.apply (Or.inl (by omega))]; exact h.1, fun t ht => ?_, fun t ht => ?_⟩
  · rw [he.apply (Or.inl (by have := (spPost_q (spK d q) (spK_lt d q) ht).1.2; omega))]
    exact h.2.1 t ht
  · obtain ⟨j, e, -, hj⟩ := (spPost_q (spK d q) (spK_lt d q) ht).2
    rw [e, he.apply (Or.inl (by omega)), ← e]
    exact h.2.2 t ht

/-! ## The groups -/

/-- Groups `p ..< p + m`. -/
def spGL : Nat → Nat → List Stmt
  | _, 0 => []
  | p, m + 1 => (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).1 ++
      spGL (p + 1) m

theorem spGL_eq : ∀ m p, p + m ≤ 21 →
    (spGroupsT m p (spState p).1 (spState p).2.1 (spState p).2.2).1 = spGL p m
  | 0, _, _ => by simp [spGroupsT, spGL]
  | m + 1, p, h => by
      rw [spGroupsT_fst, spGL, spN_of_lt (by omega), spGL_eq m (p + 1) (by omega)]

theorem spGL_snoc : ∀ m p, spGL p (m + 1) = spGL p m ++
    (spGroupT (3 * (p + m)) (spN (p + m)) (p + m == 0) (spState (p + m)).1 (spState (p + m)).2.1
      (spState (p + m)).2.2).1
  | 0, p => by simp [spGL]
  | m + 1, p => by
      rw [spGL, spGL_snoc m (p + 1), spGL, List.append_assoc, show p + 1 + m = p + (m + 1) by omega]

/-- The end of groups `p ..< p + m`. -/
def spGLEnd (p m : Nat) : Nat := if m = 0 then (spState p).2.2 else spEnd (p + m - 1)

/-- What a valuation needs before group `p`: before the first, `pp` and `at` canonical; before a
later one, those and the padding run (`SpGood`). -/
def SpBefore (p : Nat) (σ : Val) : Prop :=
  if p = 0 then IsCanonical128 (σ (.n 0)) ∧ IsCanonical128 (σ (.n 4)) ∧ IsCanonical128 (σ (.n 5))
  else SpGood spPad σ

/-- **Group `p` of the body completes**, its digit word `g^k` loaded. -/
theorem spGroupP_complete {p k : Nat} (hp : p < 22) (hk : k < 4 ^ spN p) (hm : MemOK rd 64)
    (σ : Val) (hσ : SpBefore p σ) (vals : Nat → E) (hv : ∀ t < spN p, IsCanonical128 (vals t)) :
    Completes C rd (spState p).2.2
      (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).2
      (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).1 σ
      (fun σ' => σ' (.n (spState p).2.2) = ofK (addressOfIndex k) ∧
        SpArmPost (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 k vals σ' ∧
        SpGood spPad σ') := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp only [SpBefore, ↓reduceIte] at hσ
    rw [spState_zero]
    exact spGroupT_complete (Bs := 26) (spN_le 0) hk hm le_rfl (by decide) ⟨0, by norm_num, rfl⟩
      ⟨0, by norm_num, rfl⟩ vals hv σ (fun σ' hag hpre =>
        ⟨by rw [← hag 0 (by norm_num)]; exact hσ.1, by rw [← hag 4 (by norm_num)]; exact hσ.2.1,
          by rw [← hag 5 (by norm_num)]; exact hσ.2.2, padRun_ok (P := 16 + 5) hpre⟩)
  · have hσ' : SpGood spPad σ := by simpa [SpBefore, show p ≠ 0 by omega] using hσ
    obtain ⟨hpi, hei, h24⟩ := spState_in hp0 (by omega)
    have hl : spL (p == 0) (spState p).2.2 = (spState p).2.2 := by
      simp [spL, show p ≠ 0 by omega]
    exact spGroupT_complete (Bs := (spState p).2.2) (spN_le p) hk hm (by omega) (by rw [hl]; omega)
      hpi hei vals hv σ (fun σ' hag _ =>
        spGood_congr (B := (spState p).2.2) (by simp [spPad]; omega) (by omega) hag hσ')

/-- **Group `p`'s values are numbered below its end.** -/
theorem spGroupP_nb {p : Nat} (hp : p < 22) :
    NumBelow (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).2
      (Stmt.valsList (spGroupT (3 * p) (spN p) (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).1) := by
  have hl := spL_state p (by omega)
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [spState_zero] at hl ⊢
    exact spGroupT_nb (spN_le 0) (by omega) ⟨0, by norm_num, rfl⟩ ⟨0, by norm_num, rfl⟩
  · obtain ⟨hpi, hei, -⟩ := spState_in hp0 (by omega)
    have hl' : spL (p == 0) (spState p).2.2 = (spState p).2.2 := by
      simp [spL, show p ≠ 0 by omega]
    exact spGroupT_nb (spN_le p) (by omega) (by rw [hl']; exact NBv.mono' hpi (by omega))
      (by rw [hl']; exact NBv.mono' hei (by omega))

/-- **Groups `p ..< p + m`' values are numbered below their end.** -/
theorem spGL_nb : ∀ m p, p + m ≤ 22 → NumBelow (spGLEnd p m) (Stmt.valsList (spGL p m))
  | 0, _, _ => NumBelow.nil _
  | m + 1, p, hpm => by
      have hnb := spGroupP_nb (show p < 22 by omega)
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp only [spGL, List.append_nil]
        have e : spGLEnd p 1 = spEnd p := by simp [spGLEnd]
        rw [e]; exact hnb
      · have e : spGLEnd (p + 1) m = spGLEnd p (m + 1) := by
          unfold spGLEnd; simp only [show m ≠ 0 by omega, ↓reduceIte, Nat.add_eq_zero_iff]
          congr 1; omega
        have hle : spEnd p ≤ spGLEnd (p + 1) m := by
          unfold spGLEnd; simp only [show m ≠ 0 by omega, ↓reduceIte]
          have := spState_le_end (p + 1 + m - 1)
          have := spState_mono (p := p + 1) (q := p + 1 + m - 1) (by omega) (by omega)
          rw [← spState_succ_end (show p < 21 by omega)] at *
          omega
        simp only [spGL, valsList_append]
        rw [← e]
        exact (hnb.mono hle).append (spGL_nb m (p + 1) (by omega))

/-- **Groups `p ..< p + m` complete**, each with the digest's digits and the values loaded. -/
theorem spGroupsC (d : Nat → Nat) (vals : Nat → E) (hv : ∀ i, IsCanonical128 (vals i))
    (hm : MemOK rd 64) :
    ∀ m p, p + m ≤ 22 → ∀ σ, SpBefore p σ →
      Completes C rd (spState p).2.2 (spGLEnd p m) (spGL p m) σ
        (fun σ' => (∀ q, p ≤ q → q < p + m → SpGP d vals q σ') ∧ SpBefore (p + m) σ')
  | 0, p, _, σ, hσ => ⟨σ, Ext.refl _ _ _, ⟨fun q h1 h2 => by omega, by simpa using hσ⟩, fun _ _ hn => hn⟩
  | m + 1, p, hpm, σ, hσ => by
      have hp : p < 22 := by omega
      have hg := spGroupP_complete (C := C) hp (spK_lt d p) hm σ hσ
        (fun t => vals (3 * p + t)) (fun t _ => hv _)
      have hnb := spGroupP_nb hp
      have hbefore : ∀ σ', SpGood spPad σ' → SpBefore (p + 1) σ' := fun σ' h => by
        simpa [SpBefore] using h
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp only [spGL, List.append_nil]
        have e : spGLEnd p 1 = spEnd p := by simp [spGLEnd]
        rw [e]
        exact hg.mono le_rfl le_rfl (fun σ' hσ' => ⟨fun q h1 h2 => by
          have : q = p := by omega
          subst this; exact ⟨hσ'.1, hσ'.2.1⟩, hbefore σ' hσ'.2.2⟩)
      · have hp21 : p < 21 := by omega
        have hst := spState_succ_end hp21
        have e : spGLEnd (p + 1) m = spGLEnd p (m + 1) := by
          unfold spGLEnd; simp only [show m ≠ 0 by omega, ↓reduceIte, Nat.add_eq_zero_iff]
          congr 1; omega
        have hle : spEnd p ≤ spGLEnd (p + 1) m := by
          unfold spGLEnd; simp only [show m ≠ 0 by omega, ↓reduceIte]
          have := spState_le_end (p + 1 + m - 1)
          have := spState_mono (p := p + 1) (q := p + 1 + m - 1) (by omega) (by omega)
          omega
        simp only [spGL]
        refine Completes.append (m := spEnd p) (by have := spState_le_end p; omega)
          (by rw [← e]; exact hle) hnb hg (fun σ1 _ hp1 => ?_)
        have ih := spGroupsC d vals hv hm m (p + 1) (by omega) σ1 (hbefore σ1 hp1.2.2)
        rw [hst, e] at ih
        refine (ih.keep (Q := SpGP d vals p) (Q' := SpGP d vals p) ⟨hp1.1, hp1.2.1⟩
          (fun σ' he' hq => hq.keep he' le_rfl)).mono le_rfl le_rfl
          (fun σ' ⟨⟨hr, hb⟩, hq⟩ => ⟨fun q h1 h2 => ?_, by rwa [show p + 1 + m = p + (m + 1) by omega] at hb⟩)
        rcases Nat.lt_or_ge q (p + 1) with h | h
        · have : q = p := by omega
          subst this; exact hq
        · exact hr q h (by omega)

theorem spGL_full : spGL 0 22 = spGs.1 ++ spLast.1 := by
  rw [spGL_snoc 21 0, ← spGL_eq 21 0 (by norm_num), ← spGs_fst, spLast_eq]
  rfl

theorem spGLEnd_full : spGLEnd 0 22 = spC := by
  unfold spGLEnd
  simp only [show (22 : Nat) ≠ 0 by norm_num, ↓reduceIte]
  rw [spC, spLast_eq]
  rfl

theorem spC_ge : 27 ≤ spC := by
  rw [← spGLEnd_full]
  unfold spGLEnd
  simp only [show (22 : Nat) ≠ 0 by norm_num, ↓reduceIte, show 0 + 22 - 1 = 21 by norm_num]
  have := spState_le_end 21
  have := (spState_in (p := 21) (by norm_num) le_rfl).2.2
  omega

/-- The body before its checks: the copies, the powers and the groups. -/
def spHead : List Stmt := (spCopies ++ spPowers) ++ (spGs.1 ++ spLast.1)

/-- **The copies, the powers and the groups complete**, the digits `d`'s and the values loaded. -/
theorem spCode_complete {d : Nat → Nat} (hd : ∀ i, d i < 4) (vals : Nat → E)
    (hv : ∀ i, IsCanonical128 (vals i)) (hm : MemOK rd 64)
    (σ : Val) (h0 : IsCanonical128 (σ (.n 0))) (h1 : IsCanonical128 (σ (.n 1)))
    (h2 : IsCanonical128 (σ (.n 2))) :
    Completes C rd 4 spC spHead σ
      (fun σ' => (∀ s < 10, σ' (.n (6 + s)) = gen ^ s) ∧ (∀ q < 22, SpGP d vals q σ') ∧
        SpGood spPad σ') ∧
    NumBelow spC (Stmt.valsList spHead) := by
  have _ := hd
  have hseq : SeqOK 4 (spCopies ++ spPowers) 16 := seqB_ok (by decide +kernel)
  rw [spHead, ← spGL_full, ← spGLEnd_full]
  have hst0 : (spState 0).2.2 = 16 := by rw [spState_zero]
  have hC := spC_ge
  rw [← spGLEnd_full] at hC
  refine ⟨Completes.append (m := 16) (by norm_num) (by omega) hseq.numBelow (seq_completes hseq σ)
    (fun σ1 he1 hp1 => ?_), ?_⟩
  · have hpow : ∀ s < 10, σ1 (.n (6 + s)) = gen ^ s := by
      intro s hs
      have e : σ1 (.n (6 + s)) = word (2 ^ s) 0 0 := hp1.atom (a := .const (.n (6 + s)) _) (by
        simp only [spCopies, spPowers, cst, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨s, hs, rfl⟩)
      rw [e, word_eq_eOfNat, Value.gen_pow_eq_eOfNat (by omega)]
    have hag : AgreeBelow 4 σ σ1 := he1.agree
    have e4 : σ1 (.n 4) = σ1 (.n 1) := hp1.atom (a := .copy (.n 4) (.n 1)) (by simp [spCopies, copyS])
    have e5 : σ1 (.n 5) = σ1 (.n 2) := hp1.atom (a := .copy (.n 5) (.n 2)) (by simp [spCopies, copyS])
    have hg := spGroupsC (C := C) d vals hv hm 22 0 (by norm_num) σ1
      (by simp only [SpBefore, ↓reduceIte]
          exact ⟨by rw [← hag 0 (by norm_num)]; exact h0,
            by rw [e4, ← hag 1 (by norm_num)]; exact h1, by rw [e5, ← hag 2 (by norm_num)]; exact h2⟩)
    rw [hst0] at hg
    refine (hg.keep (Q := fun σ => ∀ s < 10, σ (.n (6 + s)) = gen ^ s)
      (Q' := fun σ => ∀ s < 10, σ (.n (6 + s)) = gen ^ s) hpow
      (fun σ' he' hq s hs => by rw [he'.apply (Or.inl (by omega))]; exact hq s hs)).mono le_rfl le_rfl
      (fun σ' ⟨⟨hr, hb⟩, hq⟩ => ⟨hq, fun q hq' => hr q (Nat.zero_le _) (by omega),
        by simpa [SpBefore] using hb⟩)
  · rw [valsList_append]
    have hnb := spGL_nb 22 0 (by norm_num)
    exact (hseq.numBelow.mono (by omega)).append hnb

theorem spN_mod (i : Nat) (hi : i < 64) : i % 3 < spN (i / 3) := by
  unfold spN; split <;> omega

/-- **The codeword's product and encoding**, the groups' digits `d`'s. -/
theorem spVals {d : Nat → Nat} (hd : ∀ i, d i < 4) (hsum : ∑ i ∈ Finset.range 64, d i = 128)
    {vals : Nat → E} {σ : Val} {rest : List Stmt} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (spGs.1 ++ (spLast.1 ++ rest)) next kret)
    (hpow : ∀ s < 10, σ (.n (6 + s)) = gen ^ s) (hgp : ∀ q < 22, SpGP d vals q σ) :
    σ (.n (spEnc false 1 (spState 21).2.2)) = eOfNat192 (spX d 64) ∧
      σ (.n (spProd false 1 (spState 21).2.2)) = spTarget := by
  rw [spGs_fst] at h
  obtain ⟨s2, hpad, hg⟩ := spGroupsT_sound (C := C) (rd := rd) (σ := σ) 21 0 (by norm_num) h
  have hpad := hpad rfl (by norm_num)
  rw [spLast_eq] at s2
  obtain ⟨-, -, kL, hkL, hxL, haL⟩ := spGroupT_sound s2
  have hgrp : ∀ p < 22, SpGroupOK rd σ p := by
    intro p hp
    by_cases hp21 : p < 21
    · simpa using hg p hp21
    · have : p = 21 := by omega
      subst this
      exact ⟨kL, by simpa [spN] using hkL, hxL, by simpa [spN] using haL⟩
  obtain ⟨-, hprod, henc⟩ := spCodeword_sound hpow hpad hgrp
  have hdig : ∀ i < 64, spDigit σ i = d i := fun i hi => by
    unfold spDigit
    rw [spDigitWord_eq (spK_lt d (i / 3)) (hgp (i / 3) (by omega)).1, spK_digit d (spN_mod i hi),
      show 3 * (i / 3) + i % 3 = i by omega, spDn_digit hd hi]
  refine ⟨by rw [henc, spX_congr hdig], ?_⟩
  rw [hprod, Finset.sum_congr rfl fun i hi => hdig i (Finset.mem_range.mp hi), hsum, spTarget_eq]

/-! ## The checks and the leaf -/

theorem upds3 (σ : Val) (e0 e1 e2 : E) (k : Nat) :
    upds σ [(k, e0), (k + 1, e1), (k + 2, e2)] (.n k) = e0 ∧
      upds σ [(k, e0), (k + 1, e1), (k + 2, e2)] (.n (k + 1)) = e1 ∧
      upds σ [(k, e0), (k + 1, e1), (k + 2, e2)] (.n (k + 2)) = e2 := by
  refine ⟨upds_cons_self _ _ _ _, ?_, ?_⟩
  · rw [upds_cons_ne _ _ _ (by omega), upds_cons_self]
  · rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]

/-- The codeword's product and encoding lie below the checks. -/
theorem spEP_lt : spEnc false 1 (spState 21).2.2 < spC ∧ spProd false 1 (spState 21).2.2 < spC := by
  have h := spEnc_lt_end 63 1 false (spState 21).2.2 (spState 21).1 (spState 21).2.1
  have e : spC = spArmB 63 1 false (spState 21).2.2 (spState 21).1 (spState 21).2.1 (4 ^ 1) := by
    rw [spC, spLast_eq, spGroupT_end]
  rw [← e] at h
  unfold spEnc at h
  exact ⟨by unfold spEnc; omega, by omega⟩

/-- **The checks complete**, the encoding the argument's and the product the target. -/
theorem spChecks_eq : spChecks =
    [.atom (.assertEq (.n (spEnc false 1 (spState 21).2.2)) (.n 3)), cst spC spTarget,
      .atom (.assertEq (.n (spProd false 1 (spState 21).2.2)) (.n spC)), cst (spC + 1) spPkC,
      addS (.n (spC + 2)) (.n 2) (.n (spC + 1))] := by
  rw [spChecks, spGs_eq]

theorem spCheck_complete (σ : Val)
    (henc : σ (.n (spEnc false 1 (spState 21).2.2)) = σ (.n 3))
    (hprod : σ (.n (spProd false 1 (spState 21).2.2)) = spTarget) :
    Completes C rd spC (spC + 3) spChecks σ
      (fun σ' => σ' (.n (spC + 2)) = σ (.n 2) + spPkC) := by
  obtain ⟨hE, hP⟩ := spEP_lt
  have hC := spC_ge
  obtain ⟨e0, e1, e2⟩ := upds3 σ spTarget spPkC (σ (.n 2) + spPkC) spC
  have hext : Ext spC (spC + 3) σ
      (upds σ [(spC, spTarget), (spC + 1, spPkC), (spC + 2, σ (.n 2) + spPkC)]) :=
    upds_ext σ _ (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp)
  set σ3 := upds σ [(spC, spTarget), (spC + 1, spPkC), (spC + 2, σ (.n 2) + spPkC)]
    with hσ3
  have below : ∀ j < spC, σ3 (.n j) = σ (.n j) := fun j hj => hext.apply (Or.inl hj)
  rw [spChecks_eq]
  refine completes_atoms rfl hext (by rw [e2]) (fun a ha => ?_)
  simp only [cst, addS, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · show σ3 _ + σ3 _ = 0
    rw [below _ hE, below 3 (by omega), henc, e_add_self]
  · exact e0
  · show σ3 _ + σ3 _ = 0
    rw [below _ hP, e0, hprod, e_add_self]
  · exact e1
  · show σ3 _ = σ3 _ + σ3 _
    rw [e2, below 2 (by omega), e1]

theorem spChecks_nb : NumBelow (spC + 3) (Stmt.valsList spChecks) := by
  obtain ⟨hE, hP⟩ := spEP_lt
  have hC := spC_ge
  intro v hv
  rw [spChecks_eq] at hv
  simp only [cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with (rfl | rfl) | rfl | (rfl | rfl) | rfl | (rfl | rfl | rfl)
  all_goals exact ⟨_, by omega, rfl⟩

theorem spEnd_le_C {q : Nat} (hq : q < 22) : spEnd q ≤ spC := by
  rw [← spGLEnd_full]
  unfold spGLEnd
  simp only [show (22 : Nat) ≠ 0 by norm_num, ↓reduceIte, show 0 + 22 - 1 = 21 by norm_num]
  rcases Nat.lt_or_ge q 21 with h | h
  · rw [← spState_succ_end h]
    have := spState_mono (p := q + 1) (q := 21) (by omega) le_rfl
    have := spState_le_end 21
    omega
  · have : q = 21 := by omega
    subst this; exact le_rfl

theorem spLeafCells_lt : ∀ v ∈ spLeafCells, ∃ j, v = .n j ∧ j < spC + 3 := by
  intro v hv
  rw [spLeafCells_eq] at hv
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hv
  rcases hv with rfl | rfl | rfl | ⟨i, hi, rfl⟩
  · exact ⟨0, rfl, by omega⟩
  · exact ⟨1, rfl, by omega⟩
  · exact ⟨_, rfl, by omega⟩
  · have hp : i / 3 < 22 := by omega
    have h := (spPost_q (q := i / 3) 0 (by positivity) (spN_mod i hi)).1.2
    have := spEnd_le_C hp
    exact ⟨_, rfl, by omega⟩

/-- **The leaf's message completes** on canonical cells, over the padding run. -/
theorem spLeaf_complete (σ : Val) (hp : PadOK σ spPad) (hc : ∀ v ∈ spLeafCells, IsCanonical128 (σ v)) :
    Completes C rd (spC + 3) spLeafK.2.1 spLeafK.1 σ (fun _ => True) ∧
      NumBelow spLeafK.2.1 (Stmt.valsList spLeafK.1) := by
  have hC := spC_ge
  obtain ⟨h1, h2, -⟩ := kMsg_complete (C := C) (rd := rd) (pad := spPad)
    (cells := spLeafCells.map KC.cell) (len := 1072) (tailRun := false) (b := spC + 3) σ hp
    (by simp [spPad]; omega) (fun c hcm => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hcm
      obtain ⟨j, ej, hj⟩ := spLeafCells_lt v hv
      exact ⟨⟨j, hj, ej⟩, hc v hv⟩) (fun h => by simp at h)
  exact ⟨h1, h2⟩

theorem spLeafCells_KCb : ∀ c ∈ spLeafCells.map KC.cell, KCb (spC + 3) c := by
  intro c hcm
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hcm
  obtain ⟨j, ej, hj⟩ := spLeafCells_lt v hv
  exact ⟨j, hj, ej⟩

theorem spLeafK_le : spC + 3 ≤ spLeafK.2.1 :=
  kMsg_le (by simp [spPad]; have := spC_ge; omega) spLeafCells_KCb

theorem spLeafK_out : spLeafK.2.2 < spLeafK.2.1 := by
  have := kMsg_out spPad (spLeafCells.map KC.cell) 1072 false (spC + 3)
  show (kMsg spPad (spLeafCells.map KC.cell) 1072 false none (spC + 3)).2.2 <
    (kMsg spPad (spLeafCells.map KC.cell) 1072 false none (spC + 3)).2.1
  omega

theorem spLeaf_nb : NumBelow spLeafK.2.1 (Stmt.valsList spLeafK.1) :=
  kMsg_numBelow (by simp [spPad]; have := spC_ge; omega) spLeafCells_KCb

/-! ## `sp_wots`'s template, complete -/

/-- **The chain starts read off the frame are the loaded ones.** -/
theorem spStart_eq {d : Nat → Nat} {vals : Nat → E} {σ : Val} (hgp : ∀ q < 22, SpGP d vals q σ)
    {i : Nat} (hi : i < 64) : σ (spStart σ i) = vals i := by
  have hp : i / 3 < 22 := by omega
  have hs : spStart σ i = spStartAt (spK d) i := by
    unfold spStart spStartAt
    dsimp only
    rw [spDigitWord_eq (spK_lt d (i / 3)) (hgp (i / 3) hp).1]
  have h := (hgp (i / 3) hp).2.2 (i % 3) (spN_mod i hi)
  rw [hs]
  change σ (spStartAt (spK d) i) = vals (3 * (i / 3) + i % 3) at h
  rw [h, show 3 * (i / 3) + i % 3 = i by omega]

/-- **The digits the frame's dispatches take are the loaded ones.** -/
theorem spDigit_eq {d : Nat → Nat} (hd : ∀ i, d i < 4) {vals : Nat → E} {σ : Val}
    (hgp : ∀ q < 22, SpGP d vals q σ) {i : Nat} (hi : i < 64) : spDigit σ i = d i := by
  unfold spDigit
  rw [spDigitWord_eq (spK_lt d (i / 3)) (hgp (i / 3) (by omega)).1, spK_digit d (spN_mod i hi),
    show 3 * (i / 3) + i % 3 = i by omega, spDn_digit hd hi]

/-- **`sp_wots`'s template is complete**: for canonical `pp`, `a0`, `a1`, digits below `4` of sum
`128` and canonical chain values, on a memory of at least `64` words, its body holds of some
valuation whose arguments are `pp`, `a0`, `a1` and the digits' encoding (`spX`), returning the
one-time leaf of the values (`spLeafCell`). -/
theorem sp_wots_completeT {pp a0 a1 : E} (hpp : IsCanonical128 pp) (ha0 : IsCanonical128 a0)
    (ha1 : IsCanonical128 a1) {d : Nat → Nat} (hd : ∀ i, d i < 4)
    (hsum : ∑ i ∈ Finset.range 64, d i = 128) {vals : Nat → E} (hv : ∀ i, IsCanonical128 (vals i))
    (hm : MemOK rd 64) :
    ∃ σ : Val, σ (.n 0) = pp ∧ σ (.n 1) = a0 ∧ σ (.n 2) = a1 ∧ σ (.n 3) = eOfNat192 (spX d 64) ∧
      Stmt.HoldsList C rd σ spBodyT False (fun rs => rs = [spLeafCell pp a0 a1 d vals]) := by
  set σI : Val := Function.update (Function.update (Function.update (Function.update (fun _ => 0)
    (.n 0) pp) (.n 1) a0) (.n 2) a1) (.n 3) (eOfNat192 (spX d 64)) with hσI
  have i0 : σI (.n 0) = pp := by simp [hσI]
  have i1 : σI (.n 1) = a0 := by simp [hσI]
  have i2 : σI (.n 2) = a1 := by simp [hσI]
  have i3 : σI (.n 3) = eOfNat192 (spX d 64) := by simp [hσI]
  have hC := spC_ge
  have c0 : IsCanonical128 (σI (.n 0)) := by rw [i0]; exact hpp
  have c1 : IsCanonical128 (σI (.n 1)) := by rw [i1]; exact ha0
  have c2 : IsCanonical128 (σI (.n 2)) := by rw [i2]; exact ha1
  obtain ⟨hA, hnbA⟩ := spCode_complete (C := C) (rd := rd) hd vals hv hm σI c0 c1 c2
  -- the checks
  have hB : Completes C rd 4 (spC + 3) (spHead ++ spChecks) σI
      (fun σ' => ((∀ q < 22, SpGP d vals q σ') ∧ SpGood spPad σ') ∧
        σ' (.n (spC + 2)) = σI (.n 2) + spPkC) := by
    refine Completes.append (m := spC) (by omega) (by omega) hnbA hA.withHolds
      (fun σ2 he2 ⟨⟨hpow, hgp, hgd⟩, hh2⟩ => ?_)
    have hag2 : AgreeBelow 4 σI σ2 := he2.agree
    have h23 : σ2 (.n 3) = eOfNat192 (spX d 64) := by rw [← hag2 3 (by norm_num)]; exact i3
    have h22 : σ2 (.n 2) = σI (.n 2) := (hag2 2 (by norm_num)).symm
    have hs := (holdsList_split_atoms (xs := spCopies ++ spPowers) rfl hh2).2
    rw [show spGs.1 ++ spLast.1 = spGs.1 ++ (spLast.1 ++ []) by simp] at hs
    obtain ⟨henc, hprod⟩ := spVals hd hsum hs hpow hgp
    refine ((spCheck_complete (C := C) (rd := rd) σ2 (by rw [henc, h23]) hprod).keep
      (Q := fun σ => (∀ q < 22, SpGP d vals q σ) ∧ SpGood spPad σ)
      (Q' := fun σ => (∀ q < 22, SpGP d vals q σ) ∧ SpGood spPad σ) ⟨hgp, hgd⟩
      (fun σ' he' hq => ⟨fun q hq' => (hq.1 q hq').keep he' (spEnd_le_C hq'),
        spGood_congr (B := spC) (by simp [spPad]; omega) (by omega) he'.agree hq.2⟩)).mono le_rfl le_rfl
      (fun σ' ⟨h1, h2⟩ => ⟨h2, by rw [h1, h22]⟩)
  -- the leaf
  have hLe : spC + 3 ≤ spLeafK.2.1 := spLeafK_le
  have hnbB : NumBelow (spC + 3) (Stmt.valsList (spHead ++ spChecks)) := by
    rw [valsList_append]; exact (hnbA.mono (by omega)).append spChecks_nb
  have hL : Completes C rd 4 spLeafK.2.1 ((spHead ++ spChecks) ++ spLeafK.1) σI
      (fun σ' => ∀ q < 22, SpGP d vals q σ') := by
    refine Completes.append (m := spC + 3) (by omega) hLe hnbB hB (fun σ3 he3 ⟨⟨hgp3, hgd3⟩, h32⟩ => ?_)
    have hag3 : AgreeBelow 4 σI σ3 := he3.agree
    have hcells : ∀ v ∈ spLeafCells, IsCanonical128 (σ3 v) := by
      intro v hv'
      rw [spLeafCells_eq] at hv'
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hv'
      rcases hv' with rfl | rfl | rfl | ⟨i, hi, rfl⟩
      · rw [← hag3 0 (by norm_num)]; exact c0
      · rw [← hag3 1 (by norm_num)]; exact c1
      · rw [h32]; exact canon_add c2 (canon_word _ _)
      · have hp : i / 3 < 22 := by omega
        exact (hgp3 (i / 3) hp).2.1 (i % 3) (spN_mod i hi)
    refine ((spLeaf_complete (C := C) (rd := rd) σ3 hgd3.2.2.2 hcells).1.keep
      (Q := fun σ => ∀ q < 22, SpGP d vals q σ) (Q' := fun σ => ∀ q < 22, SpGP d vals q σ) hgp3
      (fun σ' he' hq q hq' => (hq q hq').keep he' (by have := spEnd_le_C hq'; omega))).mono le_rfl le_rfl
      (fun σ' h => h.2)
  -- the copy
  have hlt : spLeafK.2.2 < spLeafK.2.1 := spLeafK_out
  have hnbL : NumBelow spLeafK.2.1 (Stmt.valsList ((spHead ++ spChecks) ++ spLeafK.1)) := by
    rw [valsList_append]; exact (hnbB.mono hLe).append spLeaf_nb
  have hD : Completes C rd 4 (spLeafK.2.1 + 1)
      (((spHead ++ spChecks) ++ spLeafK.1) ++ [copyS (.n spLeafK.2.1) (.n spLeafK.2.2)])
      σI (fun σ' => ∀ q < 22, SpGP d vals q σ') := by
    refine Completes.append (m := spLeafK.2.1) (by omega) (by omega) hnbL hL (fun σ4 he4 hgp4 => ?_)
    have hext : Ext spLeafK.2.1 (spLeafK.2.1 + 1) σ4 (upds σ4 [(spLeafK.2.1, σ4 (.n spLeafK.2.2))]) :=
      upds_ext σ4 _ (by simp)
    refine completes_atoms rfl hext (fun q hq => (hgp4 q hq).keep hext
      (by have := spEnd_le_C hq; omega)) (fun a ha => ?_)
    simp only [copyS, List.mem_singleton, Stmt.atom.injEq] at ha
    subst ha
    show upds σ4 _ _ = upds σ4 _ _
    rw [upds_cons_self, hext.apply (Or.inl hlt)]
  obtain ⟨σf, hef, hgpf, hhf⟩ := hD
  have f0 : σf (.n 0) = pp := by rw [hef.apply (Or.inl (by norm_num))]; exact i0
  have f1 : σf (.n 1) = a0 := by rw [hef.apply (Or.inl (by norm_num))]; exact i1
  have f2 : σf (.n 2) = a1 := by rw [hef.apply (Or.inl (by norm_num))]; exact i2
  have f3 : σf (.n 3) = eOfNat192 (spX d 64) := by rw [hef.apply (Or.inl (by norm_num))]; exact i3
  have hbody : spBodyT = (((spHead ++ spChecks) ++ spLeafK.1) ++
      [copyS (.n spLeafK.2.1) (.n spLeafK.2.2)]) ++ [.ret [.n spLeafK.2.1]] := by
    rw [spBodyT_parts, spHead]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hH : Stmt.HoldsList C rd σf spBodyT False (fun rs => rs = [σf (.n spLeafK.2.1)]) := by
    rw [hbody, holdsList_append]
    exact hhf _ _ rfl
  obtain ⟨lf, hrets, -, -, -, -, hval⟩ := sp_wots_soundT hH
  have e : σf (.n spLeafK.2.1) = spLeafCell pp a0 a1 d vals := by
    rw [List.singleton_inj.mp hrets, hval, f0, f1, f2]
    exact spLeafCell_congr (fun i hi => spDigit_eq hd hgpf hi) (fun i hi => spStart_eq hgpf hi)
  refine ⟨σf, f0, f1, f2, f3, ?_⟩
  rw [← e]
  exact hH

end
end LeanVM.Guest.B1.Sig
