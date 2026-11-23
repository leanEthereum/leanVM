/-
  LeanVM.Guest.B1.Bits.GrindFwd

  `grind_check` inlined, on a caller's evaluated valuation: its own values are the honest ones.
-/

module

public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.B1.Fwd.Eval

/-!
# `grind_check` inlined, evaluated

A caller's completeness evaluates its body (`Fwd.ev`) from an oracle `wo` for the hints. On the
statements of `gcInlineT b o w tabs`, the caller's word `w` and tables `tabs` older than the
expansion (`w.idx < o`, `tabs.idx < o`), no store into its values (`loadInto`), the oracle at the
windows the honest ones (`gcWin`), a memory where the windows' range checks pass (`hrc`) and the
tables at `tabs` (`WinTabs`): every own value is `gcVals`' (`gcInline_vals_of_good`), the range
checks' complements and touched words being the only ones their relations allow. So
`gcInline_complete_of` applies (`gcInline_holds_of_good`).

The proof is for `gcInlineOT b o off w tabs`, the expansion with its table reads at `off`, where
the tables are a constant `tabs·g^off` folded into the reads (`gcInlineO_vals_of_good`, its blocks
in `VerifySub/GrindOff`); `gcInlineT` is it at `off = 0`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- A load into one of the values `lo ..< hi`. -/
def loadInto (lo hi : ℕ) : Atom → Bool
  | .load d _ _ => decide (lo ≤ d.idx ∧ d.idx < hi)
  | _ => false

theorem rdAt_of_loadHolds {rd : Reader} {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) :
    rdAt rd p k = v := by
  unfold rdAt; rw [h.2]; rfl

/-- The honest window `j ≤ gcW b` of the word `w` (`gcVals`' value `2 + j`, which reads neither the
memory nor the tables). -/
noncomputable def gcWin (b : ℕ) (w : E) (j : ℕ) : E := gcVals (fun _ => none) b w 0 (2 + j)

theorem gcVals_win {rd : Reader} {b : ℕ} {w tabs : E} {j : ℕ} (hj : j ≤ gcW b) :
    gcVals rd b w tabs (2 + j) = gcWin b w j := by
  unfold gcWin gcVals
  simp only [show ¬ (2 + j = 0) by omega, show ¬ (2 + j = 1) by omega, ↓reduceIte]
  by_cases h : 2 + j < gcW b + 2
  · simp only [h, ↓reduceIte]
  · simp only [show 2 + j = gcW b + 2 by omega, ↓reduceIte]

/-! ## `grind_check` inlined on constant tables -/

/-- `gcHead b`, its table read at `off`. -/
def gcHeadO (b off : ℕ) : List Stmt :=
  [.atom (.hint (.windowsExp (.n 0) b 11 (gcW b)
      (.stack ((List.range (gcW b)).map fun j => .n (2 + j))))),
    .atom (.hint (.windowsExp (.n 0) (b + 11 * gcW b) (gcTop b) 1 (.stack [.n (gcW b + 2)]))),
    .atom (.const (.n (gcW b + 3)) (wBound (gcTop b))),
    .atom (.rangeCheck (.n (gcW b + 2)) (.n (gcW b + 4)) (.n (gcW b + 5)) (.n (gcW b + 6))
      (.n (gcW b + 3))),
    .atom (.mul (.n (gcW b + 7)) (.n 1) (.n (gcW b + 2))),
    .atom (.load (.n (gcW b + 8)) (.n (gcW b + 7)) off)]

/-- `gcIterAt W i`, its table read at `off`. -/
def gcIterAtO (W i off : ℕ) : List Stmt :=
  [.atom (.const (.n (W + 9 * i)) (wBound 11)),
    .atom (.rangeCheck (.n (W + 2 - i)) (.n (W + 9 * i + 1)) (.n (W + 9 * i + 2))
      (.n (W + 9 * i + 3)) (.n (W + 9 * i))),
    .atom (.const (.n (W + 9 * i + 4)) (word 2048 0)),
    .atom (.mul (.n (W + 9 * i + 5)) (.n (W + 9 * i - 1)) (.n (W + 9 * i + 4))),
    .atom (.mul (.n (W + 9 * i + 6)) (.n 1) (.n (W + 2 - i))),
    .atom (.load (.n (W + 9 * i + 7)) (.n (W + 9 * i + 6)) off),
    .atom (.add (.n (W + 9 * i + 8)) (.n (W + 9 * i + 5)) (.n (W + 9 * i + 7)))]

/-- `gcPre b`, its table reads at `off`. -/
def gcPreO (b off : ℕ) : List Stmt :=
  gcHeadO b off ++ ((List.range (gcW b)).map fun i => gcIterAtO (gcW b) (i + 1) off).flatten ++
    gcTailPre b

/-- **`grind_check(w, t·g^off, b)` inlined**, its own values from `.n o`, its table reads at `off`. -/
def gcInlineOT (b o off : ℕ) (w tabs : V) : List Stmt := Stmt.renameList (gcRen o w tabs) (gcPreO b off)

theorem winTab_loadO {rd : Reader} {t : E} {off : ℕ} (ht : WinTabs rd (t * gen ^ off)) {e : ℕ}
    (he : e < 2 ^ 11) : LoadHolds rd (t * gen ^ e) off (eOfNat e) := by
  have h := winTab_load ht he
  rw [mul_right_comm, loadHolds_mul_gen_pow, Nat.add_zero] at h
  exact h

variable {rd : Reader} {S : List Atom} {wo : ℕ → E} {σ : Val}

/-- **`grind_check` inlined, its table reads at `off`, evaluated, is honest** on its own values:
`gcVals` at the tables `tabs`, the windows at `tabs·g^off`. -/
theorem gcInlineO_vals_of_good {b o off : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V}
    (hwo : w.idx < o) (hto : tabs.idx < o)
    (hg : ∀ s ∈ gcInlineOT b o off w tabs, GoodS rd S wo σ s)
    (hS : ∀ a ∈ S, loadInto o (o + (gcLen b - 2)) a = false)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ tabs * gen ^ off))
    (hwin : ∀ j ≤ gcW b, wo (o + j) = gcWin b (σ w) j) :
    ∀ k, 2 ≤ k → k < gcLen b → σ (.n (o + k - 2)) = gcVals rd b (σ w) (σ tabs) k := by
  obtain ⟨hT1, hT, hsum⟩ := gc_shape b hb
  have hW1 := gcW_pos b hb
  generalize hWd : gcW b = W at hT1 hT hsum hW1 hwin
  generalize hRd : gcRen o w tabs = R at hg
  have Rk : ∀ k, 2 ≤ k → R (.n k) = .n (o + k - 2) := fun k hk ↦ by
    rw [← hRd]; exact gcRen_own o w tabs hk
  have R0 : R (.n 0) = w := by rw [← hRd]; rfl
  have R1 : R (.n 1) = tabs := by rw [← hRd]; rfl
  -- the valuation through the renaming
  let τ : ℕ → E := fun k ↦ σ (R (.n k))
  have τk : ∀ k, 2 ≤ k → τ k = σ (.n (o + k - 2)) := fun k hk ↦ by simp only [τ, Rk k hk]
  have τ0 : τ 0 = σ w := by simp only [τ, R0]
  have τ1 : τ 1 = σ tabs := by simp only [τ, R1]
  have rlt : ∀ x d, x < d → 2 ≤ d → (R (.n x)).idx < (R (.n d)).idx := by
    intro x d hx hd
    rw [Rk d hd]
    rcases Nat.lt_or_ge x 2 with h2 | h2
    · rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
      · rw [R0]; show w.idx < o + d - 2; omega
      · rw [R1]; show tabs.idx < o + d - 2; omega
    · rw [Rk x h2]; show o + x - 2 < o + d - 2; omega
  generalize hG : gcVals rd b (σ w) (σ tabs) = G
  -- the atoms' equations
  have hgA : ∀ a, Stmt.atom a ∈ gcPreO b off → Good rd S wo σ (a.rename R) := fun a ha ↦ by
    have := hg _ (by rw [gcInlineOT, hRd]; exact renameList_mem ha)
    exact this
  have gconst : ∀ d c, Stmt.atom (.const (.n d) c) ∈ gcPreO b off → τ d = c := fun d c h ↦ hgA _ h
  have gadd : ∀ d x y, Stmt.atom (.add (.n d) (.n x) (.n y)) ∈ gcPreO b off → τ d = τ x + τ y :=
    fun d x y h ↦ hgA _ h
  have gmul : ∀ d x y, x < d → y < d → 2 ≤ d → Stmt.atom (.mul (.n d) (.n x) (.n y)) ∈ gcPreO b off →
      τ d = τ x * τ y := by
    intro d x y hx hy hd h
    have := hgA _ h
    simp only [Atom.rename, Good] at this
    rwa [ite_eq_left ⟨rlt x d hx hd, rlt y d hy hd⟩] at this
  have gload : ∀ d p k, 2 ≤ d → d < gcLen b → Stmt.atom (.load (.n d) (.n p) k) ∈ gcPreO b off →
      τ d = rdAt rd (τ p) k := by
    intro d p k hd hdl h
    have := hgA _ h
    simp only [Atom.rename, Good] at this
    rcases this with h' | h'
    · have := hS _ h'
      simp only [loadInto, Rk d hd, decide_eq_false_iff_not] at this
      exact absurd ⟨by show o ≤ o + d - 2; omega, by show o + d - 2 < o + (gcLen b - 2); omega⟩ this
    · exact h'
  have grc : ∀ x y t1 t2 k, k < y → 2 ≤ y →
      Stmt.atom (.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n k)) ∈ gcPreO b off →
      τ t1 = rdAt rd (τ x) 0 ∧ τ t2 = rdAt rd (τ y) 0 ∧ τ y = τ k * (τ x)⁻¹ := by
    intro x y t1 t2 k hk hy h
    have := hgA _ h
    simp only [Atom.rename, Good] at this
    rwa [ite_eq_left (rlt k y hk hy)] at this
  -- membership in the expansion
  have mH : ∀ s ∈ gcHeadO b off, s ∈ gcPreO b off := fun s h ↦
    List.mem_append_left _ (List.mem_append_left _ h)
  have mI : ∀ i, 1 ≤ i → i ≤ W → ∀ s ∈ gcIterAtO W i off, s ∈ gcPreO b off := fun i h1 h2 s h ↦
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr ⟨gcIterAtO W i off,
      List.mem_map.mpr ⟨i - 1, List.mem_range.mpr (by omega), by rw [hWd, Nat.sub_add_cancel h1]⟩,
      h⟩))
  have mT : ∀ s ∈ gcTailPre b, s ∈ gcPreO b off := fun s h ↦ List.mem_append_right _ h
  -- the windows
  have hwins : ∀ j ≤ W, τ (2 + j) = G (2 + j) := by
    intro j hj
    rw [← hG, gcVals_win (by rw [hWd]; exact hj), ← hwin j hj]
    rcases Nat.lt_or_ge j W with hjW | hjW
    · have := hgA (.hint (.windowsExp (.n 0) b 11 (gcW b)
        (.stack ((List.range (gcW b)).map fun j => .n (2 + j))))) (mH _ (by simp [gcHeadO]))
      simp only [Atom.rename, Hint.rename, Dest.rename, Good, hWd] at this
      have hv := this (R (.n (2 + j)))
        (List.mem_map.mpr ⟨.n (2 + j), List.mem_map.mpr ⟨j, List.mem_range.mpr hjW, rfl⟩, rfl⟩)
      rw [Rk _ (by omega)] at hv
      show σ (R (.n (2 + j))) = _
      rw [Rk _ (by omega), hv]
      show wo (o + (2 + j) - 2) = _
      congr 1; omega
    · obtain rfl : j = W := by omega
      have := hgA (.hint (.windowsExp (.n 0) (b + 11 * gcW b) (gcTop b) 1 (.stack [.n (gcW b + 2)])))
        (mH _ (by simp [gcHeadO]))
      simp only [Atom.rename, Hint.rename, Dest.rename, Good, hWd] at this
      have hv := this (R (.n (j + 2))) (by simp)
      rw [Rk _ (by omega)] at hv
      show σ (R (.n (2 + j))) = _
      rw [Nat.add_comm 2 j, Rk _ (by omega), hv]
      show wo (o + (j + 2) - 2) = _
      congr 1
  -- the honest values
  have hV0 := gcV_zero_lt (hWd ▸ hsum) (σ w)
  have hV0' : gcV b (σ w) 0 < 2 ^ 11 := lt_of_lt_of_le hV0 (Nat.pow_le_pow_right (by decide) hT)
  have Gw2 : G (W + 2) = gen ^ gcV b (σ w) 0 := by rw [← hG, ← hWd]; exact gv_top
  have gne : ∀ e : ℕ, (gen ^ e : E) ≠ 0 := fun e ↦ pow_ne_zero _ gen_ne_zero
  -- the head
  have hhead : ∀ r < 7, τ (W + 2 + r) = G (W + 2 + r) := by
    have e2 : τ (W + 2) = gen ^ gcV b (σ w) 0 := by
      rw [← Gw2, show W + 2 = 2 + W by ring]; exact hwins W le_rfl
    obtain ⟨y, t1, t2, r1, r2, r3⟩ := hrc _ hT _ hV0
    obtain ⟨c1, c2, c3⟩ := rcWit_spec (rd := rd) ⟨y, t1, t2, r1, r2, r3⟩
    have e3 : τ (W + 3) = wBound (gcTop b) := gconst _ _ (mH _ (by simp [gcHeadO, hWd]))
    obtain ⟨e5, e6, e4⟩ := grc (W + 2) (W + 4) (W + 5) (W + 6) (W + 3) (by omega) (by omega)
      (mH _ (by simp [gcHeadO, hWd]))
    have e7 : τ (W + 7) = τ 1 * τ (W + 2) :=
      gmul _ _ _ (by omega) (by omega) (by omega) (mH _ (by simp [gcHeadO, hWd]))
    have e8 : τ (W + 8) = rdAt rd (τ (W + 7)) off :=
      gload _ _ _ (by omega) (by rw [gcLen, hWd]; omega) (mH _ (by simp [gcHeadO, hWd]))
    rw [e2, e3] at e4
    rw [e2] at e5
    rw [τ1, e2] at e7
    rw [e7, rdAt_of_loadHolds (winTab_loadO ht hV0')] at e8
    have h4 : τ (W + 4) = (rcWit rd (gen ^ gcV b (σ w) 0) (wBound (gcTop b))).1 := by
      rw [e4]
      exact ((eq_mul_inv_iff_mul_eq₀ (gne _)).2 (by rw [mul_comm]; exact c2.symm)).symm
    rw [h4, rdAt_of_loadHolds c3] at e6
    rw [rdAt_of_loadHolds c1] at e5
    intro r hr
    rw [← hG]
    unfold gcVals
    rw [hWd]
    interval_cases r
    · rw [Nat.add_zero, e2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left rfl]
    · rw [e3, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_left rfl]
    · rw [h4, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    · rw [e5, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    · rw [e6, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_left rfl]
    · rw [e7, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    · rw [e8, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  -- one Horner step
  have step : ∀ i, 1 ≤ i → i ≤ W → τ (W + 9 * i - 1) = G (W + 9 * i - 1) →
      ∀ r < 9, τ (W + 9 * i + r) = G (W + 9 * i + r) := by
    intro i h1 h2 hprev
    have h2' : i ≤ gcW b := by rw [hWd]; exact h2
    have gi : ∀ r < 9, G (W + 9 * i + r) = gcIterVal rd b (σ w) (σ tabs) i r := fun r hr ↦ by
      rw [← hG, ← hWd]; exact gv_iter h1 h2' hr
    have hwin' : gcV b (σ w) i % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by positivity)
    have ew : τ (W + 2 - i) = gen ^ (gcV b (σ w) i % 2 ^ 11) := by
      rw [show W + 2 - i = 2 + (W - i) by omega, hwins _ (by omega), ← hG,
        show 2 + (W - i) = gcW b + 2 - i by omega]
      exact gv_win h1 h2'
    have ep : τ (W + 9 * i - 1) = eOfNat (gcV b (σ w) (i - 1)) := by
      rw [hprev, ← hG, show W + 9 * i - 1 = gcW b + 9 * (i - 1) + 8 by omega]
      exact gv_acc (by omega)
    have mI' := mI i h1 h2
    obtain ⟨y, t1, t2, r1, r2, r3⟩ := hrc 11 le_rfl _ hwin'
    obtain ⟨c1, c2, c3⟩ := rcWit_spec (rd := rd) ⟨y, t1, t2, r1, r2, r3⟩
    have e0 : τ (W + 9 * i) = wBound 11 := gconst _ _ (mI' _ (by simp [gcIterAtO]))
    obtain ⟨e2, e3, e1⟩ := grc (W + 2 - i) (W + 9 * i + 1) (W + 9 * i + 2) (W + 9 * i + 3)
      (W + 9 * i) (by omega) (by omega) (mI' _ (by simp [gcIterAtO]))
    have e4 : τ (W + 9 * i + 4) = word 2048 0 := gconst _ _ (mI' _ (by simp [gcIterAtO]))
    have e5 : τ (W + 9 * i + 5) = τ (W + 9 * i - 1) * τ (W + 9 * i + 4) :=
      gmul _ _ _ (by omega) (by omega) (by omega) (mI' _ (by simp [gcIterAtO]))
    have e6 : τ (W + 9 * i + 6) = τ 1 * τ (W + 2 - i) :=
      gmul _ _ _ (by omega) (by omega) (by omega) (mI' _ (by simp [gcIterAtO]))
    have e7 : τ (W + 9 * i + 7) = rdAt rd (τ (W + 9 * i + 6)) off :=
      gload _ _ _ (by omega) (by rw [gcLen, hWd]; omega) (mI' _ (by simp [gcIterAtO]))
    have e8 : τ (W + 9 * i + 8) = τ (W + 9 * i + 5) + τ (W + 9 * i + 7) :=
      gadd _ _ _ (mI' _ (by simp [gcIterAtO]))
    rw [ew, e0] at e1
    rw [ew] at e2
    rw [τ1, ew] at e6
    rw [e6, rdAt_of_loadHolds (winTab_loadO ht hwin')] at e7
    rw [ep, e4] at e5
    rw [e5, e7] at e8
    have h1' : τ (W + 9 * i + 1) = (rcWit rd (gen ^ (gcV b (σ w) i % 2 ^ 11)) (wBound 11)).1 := by
      rw [e1]
      exact ((eq_mul_inv_iff_mul_eq₀ (gne _)).2 (by rw [mul_comm]; exact c2.symm)).symm
    rw [h1', rdAt_of_loadHolds c3] at e3
    rw [rdAt_of_loadHolds c1] at e2
    intro r hr
    rw [gi r hr]
    interval_cases r
    · rw [Nat.add_zero, e0]; rfl
    · rw [h1']; rfl
    · rw [e2]; rfl
    · rw [e3]; rfl
    · rw [e4]; rfl
    · rw [e5]; rfl
    · rw [e6]; rfl
    · rw [e7]; rfl
    · rw [e8]
      show _ = eOfNat (gcV b (σ w) i)
      have hp := gcV_pred (b := b) (σ w) h1 h2'
      have h64 : 2 ^ 11 * gcV b (σ w) (i - 1) < 2 ^ 64 := by
        rw [hp]
        exact lt_of_le_of_lt (Nat.mul_div_le _ _) (gcV_lt (σ w) _)
      rw [horner_step h64 hwin', hp, Nat.div_add_mod]
  have hiter : ∀ i, 1 ≤ i → i ≤ W → ∀ r < 9, τ (W + 9 * i + r) = G (W + 9 * i + r) := by
    intro i h1
    induction i, h1 using Nat.le_induction with
    | base =>
      intro h2
      refine step 1 le_rfl h2 ?_
      rw [show W + 9 * 1 - 1 = W + 2 + 6 by omega]
      exact hhead 6 (by omega)
    | succ i hi ih =>
      intro h2
      refine step (i + 1) (by omega) h2 ?_
      rw [show W + 9 * (i + 1) - 1 = W + 9 * i + 8 by omega]
      exact ih (by omega) 8 (by omega)
  -- the tail
  have htail : ∀ r < 7, τ (10 * W + 9 + r) = G (10 * W + 9 + r) := by
    have gt : ∀ r, G (10 * W + 9 + r) = gcTailVal b (σ w) r := fun r ↦ by
      rw [← hG, ← hWd]; exact gv_tail
    have ea : τ (10 * W + 8) = eOfNat (gcV b (σ w) W) := by
      rw [show 10 * W + 8 = W + 9 * W + 8 by ring, hiter W hW1 le_rfl 8 (by omega), ← hG, ← hWd]
      exact gv_acc le_rfl
    have e0 : τ (10 * W + 9) = word (2 ^ b) 0 := gconst _ _ (mT _ (by simp [gcTailPre, hWd]))
    have e1 : τ (10 * W + 10) = τ (10 * W + 8) * τ (10 * W + 9) :=
      gmul _ _ _ (by omega) (by omega) (by omega) (mT _ (by simp [gcTailPre, hWd]))
    have e2 : τ (10 * W + 11) = τ 0 + τ (10 * W + 10) := gadd _ _ _ (mT _ (by simp [gcTailPre, hWd]))
    have e3 : τ (10 * W + 12) = word 2 1 := gconst _ _ (mT _ (by simp [gcTailPre, hWd]))
    have e4 : τ (10 * W + 13) = τ (10 * W + 11) * τ (10 * W + 12) :=
      gmul _ _ _ (by omega) (by omega) (by omega) (mT _ (by simp [gcTailPre, hWd]))
    have e5 : τ (10 * W + 14) = word (2 ^ b) 0 := gconst _ _ (mT _ (by simp [gcTailPre, hWd]))
    have e6 : τ (10 * W + 15) = τ (10 * W + 8) * τ (10 * W + 14) :=
      gmul _ _ _ (by omega) (by omega) (by omega) (mT _ (by simp [gcTailPre, hWd]))
    rw [ea, e0] at e1
    rw [τ0, e1] at e2
    rw [e2, e3] at e4
    rw [ea, e5] at e6
    intro r hr
    rw [gt r]
    interval_cases r
    · rw [Nat.add_zero, e0]; rfl
    · rw [e1]; simp only [gcTailVal, hWd]
    · rw [e2]; simp only [gcTailVal, hWd]
    · rw [e3]; rfl
    · rw [e4]; simp only [gcTailVal, hWd]
    · rw [e5]; rfl
    · rw [e6]; simp only [gcTailVal, hWd]
  -- every own value
  intro k hk2 hkL
  rw [gcLen, hWd] at hkL
  rw [← τk k hk2]
  rcases Nat.lt_or_ge k (W + 2) with h | h
  · have := hwins (k - 2) (by omega)
    rwa [show 2 + (k - 2) = k by omega] at this
  rcases Nat.lt_or_ge k (W + 9) with h' | h'
  · have := hhead (k - (W + 2)) (by omega)
    rwa [show W + 2 + (k - (W + 2)) = k by omega] at this
  rcases Nat.lt_or_ge k (10 * W + 9) with h'' | h''
  · have := hiter ((k - W) / 9) (by omega) (by omega) ((k - W) % 9) (Nat.mod_lt _ (by omega))
    rwa [show W + 9 * ((k - W) / 9) + (k - W) % 9 = k by omega] at this
  · have := htail (k - (10 * W + 9)) (by omega)
    rwa [show 10 * W + 9 + (k - (10 * W + 9)) = k by omega] at this

/-- **`grind_check` inlined, its table reads at `off`, evaluated: its table reads' pointers** are the
tables' words `tabs·g^e`, `e < 2^11`: the head's, at `o + gcW b + 5`, and step `i + 1`'s, at
`o + gcW b + 9 (i + 1) + 4`. -/
theorem gcInlineO_ptrs_of_good {b o off : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V}
    (hwo : w.idx < o) (hto : tabs.idx < o)
    (hg : ∀ s ∈ gcInlineOT b o off w tabs, GoodS rd S wo σ s)
    (hS : ∀ a ∈ S, loadInto o (o + (gcLen b - 2)) a = false)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ tabs * gen ^ off))
    (hwin : ∀ j ≤ gcW b, wo (o + j) = gcWin b (σ w) j) :
    (∃ e < 2 ^ 11, σ (.n (o + gcW b + 5)) = σ tabs * gen ^ e) ∧
      ∀ i < gcW b, ∃ e < 2 ^ 11, σ (.n (o + gcW b + 9 * (i + 1) + 4)) = σ tabs * gen ^ e := by
  have hv := gcInlineO_vals_of_good hb hwo hto hg hS hrc ht hwin
  obtain ⟨hT1, hT, hsum⟩ := gc_shape b hb
  refine ⟨⟨gcV b (σ w) 0, ?_, ?_⟩, fun i hi ↦ ⟨gcV b (σ w) (i + 1) % 2 ^ 11, Nat.mod_lt _ (by positivity), ?_⟩⟩
  · exact lt_of_lt_of_le (gcV_zero_lt hsum (σ w)) (Nat.pow_le_pow_right (by decide) hT)
  · have := hv (gcW b + 7) (by omega) (by unfold gcLen; omega)
    rw [show o + (gcW b + 7) - 2 = o + gcW b + 5 by omega] at this
    rw [this, gv_top_ptr]
  · have := hv (gcW b + 9 * (i + 1) + 6) (by omega) (by unfold gcLen; omega)
    rw [show o + (gcW b + 9 * (i + 1) + 6) - 2 = o + gcW b + 9 * (i + 1) + 4 by omega,
      gv_iter (by omega) (by omega) (by omega)] at this
    rw [this]
    rfl

/-- **`grind_check` inlined, evaluated, is honest** on its own values. -/
theorem gcInline_vals_of_good {b o : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V}
    (hwo : w.idx < o) (hto : tabs.idx < o)
    (hg : ∀ s ∈ gcInlineT b o w tabs, GoodS rd S wo σ s)
    (hS : ∀ a ∈ S, loadInto o (o + (gcLen b - 2)) a = false)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ tabs))
    (hwin : ∀ j ≤ gcW b, wo (o + j) = gcWin b (σ w) j) :
    ∀ k, 2 ≤ k → k < gcLen b → σ (.n (o + k - 2)) = gcVals rd b (σ w) (σ tabs) k :=
  gcInlineO_vals_of_good (off := 0) hb hwo hto hg hS hrc (by rwa [pow_zero, mul_one]) hwin

/-- **`grind_check` inlined, evaluated: its table reads' pointers** are the tables' words `tabs·g^e`,
`e < 2^11`: the head's, at `o + gcW b + 5`, and step `i + 1`'s, at `o + gcW b + 9 (i + 1) + 4`. -/
theorem gcInline_ptrs_of_good {b o : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V}
    (hwo : w.idx < o) (hto : tabs.idx < o)
    (hg : ∀ s ∈ gcInlineT b o w tabs, GoodS rd S wo σ s)
    (hS : ∀ a ∈ S, loadInto o (o + (gcLen b - 2)) a = false)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ tabs))
    (hwin : ∀ j ≤ gcW b, wo (o + j) = gcWin b (σ w) j) :
    (∃ e < 2 ^ 11, σ (.n (o + gcW b + 5)) = σ tabs * gen ^ e) ∧
      ∀ i < gcW b, ∃ e < 2 ^ 11, σ (.n (o + gcW b + 9 * (i + 1) + 4)) = σ tabs * gen ^ e :=
  gcInlineO_ptrs_of_good (off := 0) hb hwo hto hg hS hrc (by rwa [pow_zero, mul_one]) hwin

/-- The inlined `grind_check`'s table reads' pointers: the head's, then each step's. -/
def gcPtrs (b o : ℕ) : List V :=
  .n (o + gcW b + 5) :: (List.range (gcW b)).map fun i => .n (o + gcW b + 9 * (i + 1) + 4)

/-- **`grind_check` inlined, evaluated: each of `gcPtrs` is a table word** `tabs·g^e`, `e < 2^11`. -/
theorem gcPtrs_of_good {b o : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V}
    (hwo : w.idx < o) (hto : tabs.idx < o)
    (hg : ∀ s ∈ gcInlineT b o w tabs, GoodS rd S wo σ s)
    (hS : ∀ a ∈ S, loadInto o (o + (gcLen b - 2)) a = false)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ tabs))
    (hwin : ∀ j ≤ gcW b, wo (o + j) = gcWin b (σ w) j) :
    ∀ p ∈ gcPtrs b o, ∃ e < 2 ^ 11, σ p = σ tabs * gen ^ e := by
  obtain ⟨g0, gI⟩ := gcInline_ptrs_of_good hb hwo hto hg hS hrc ht hwin
  intro p hp
  simp only [gcPtrs, List.mem_cons, List.mem_map, List.mem_range] at hp
  rcases hp with rfl | ⟨i, hi, rfl⟩
  · exact g0
  · exact gI i hi

/-- **`grind_check` inlined, evaluated, holds**: on the caller's evaluated valuation, the word
passing the proof of work. -/
theorem gcInline_holds_of_good {C : CallRel} {b o : ℕ} (hb : b ∈ grindBitsDeployed) {w tabs : V}
    (hwo : w.idx < o) (hto : tabs.idx < o)
    (hg : ∀ s ∈ gcInlineT b o w tabs, GoodS rd S wo σ s)
    (hS : ∀ a ∈ S, loadInto o (o + (gcLen b - 2)) a = false)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ tabs))
    (hwin : ∀ j ≤ gcW b, wo (o + j) = gcWin b (σ w) j)
    (hlow : ((σ w).limb 0).lane.toNat % 2 ^ b = 0) {next : Prop} (hn : next)
    {kret : List E → Prop} : Stmt.HoldsList C rd σ (gcInlineT b o w tabs) next kret :=
  gcInline_complete_of hrc hb ht hlow
    (gcInline_vals_of_good hb hwo hto hg hS hrc ht hwin) hn

end
end LeanVM.Guest.B1
