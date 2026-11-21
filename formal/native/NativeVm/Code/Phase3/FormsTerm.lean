module

public import NativeVm.Code.Phase3.FormsRep

/-!
# The bus forms of a side: `FormW.addTerm` in words

`atCode_spec`: the form at word `po` (at most `cap` terms, `FZ`), the key of `m` at word `qo` apart
from it, the coefficient `c` in `(r9, r10)`: the form becomes `f.addTerm m c`, only its words
written. The search keeps the scanned terms' indices (`AtScan`); a match adds the coefficient in
place (`AtFound`); none appends the term (there is room: the monomial is new only if `f` has fewer
than `cap` terms).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

/-- The registers `atCode` writes. -/
abbrev atRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .rsi, .r8]

/-- A term's coefficient plus `c`. -/
abbrev addC (c : EW) (t : TermW) : TermW := { t with coeff := t.coeff + c }

variable {w : UInt64} {po qo cap : Nat} {f : FormW} {m : Array Nat} {c : EW} {s : QState}
  {E : QState → Prop}

/-- The search after `j` terms, none matching. -/
def AtScan (w : UInt64) (po : Nat) (f : FormW) (m : Array Nat) (s t : QState) (j : Nat) : Prop :=
  j ≤ f.size ∧ t.reg .rcx = 0 ∧ t.reg .rsi = (f.size - j).toUInt64 ∧
    t.reg .rdx = wd w (po + 1 + 5 * j) ∧ t.mem = s.mem ∧
    ∀ i (h : i < j) (h' : i < f.size), f[i].cols ≠ m

/-- The search found term `i`, its coefficient added. -/
def AtFound (w : UInt64) (po cap : Nat) (f : FormW) (m : Array Nat) (c : EW) (s t : QState) : Prop :=
  t.reg .rcx = 1 ∧ t.reg .rsi = 0 ∧ ∃ i, f.findIdx? (·.cols == m) = some i ∧
    FZ t.mem w po cap (f.modify i (addC c)) ∧
    KeepS w (fun k ↦ po ≤ k ∧ k < po + 1 + 5 * cap) s.mem t.mem

theorem fs_toUInt64_ne_zero {n : Nat} (h : n < 2 ^ 64) :
    (n.toUInt64 != (0 : Int64).toUInt64) = decide (n ≠ 0) := by
  rw [show (0 : Int64).toUInt64 = (0 : Nat).toUInt64 from rfl]
  by_cases hn : n = 0
  · subst hn; rfl
  · have : n.toUInt64 ≠ (0 : Nat).toUInt64 := fun e ↦ hn ((toUInt64_inj h (by omega)).mp e)
    rw [bne_iff_ne.mpr this]
    simp [hn]

/-- The comparison's result: zero exactly when the term's monomial is `m`. -/
theorem key_cmp {t : TermW} (ht : t.cols.size ≤ 2) (hm : m.size ≤ 2)
    (ht' : ∀ i (h : i < t.cols.size), t.cols[i] < 2 ^ 64) (hm' : ∀ i (h : i < m.size), m[i] < 2 ^ 64) :
    ((t.cols.size.toUInt64 ^^^ m.size.toUInt64 |||
      ((t.cols.getD 0 0).toUInt64 ^^^ (m.getD 0 0).toUInt64) |||
      ((t.cols.getD 1 0).toUInt64 ^^^ (m.getD 1 0).toUInt64)) == (0 : Int64).toUInt64) =
      decide (t.cols = m) := by
  rw [show (0 : Int64).toUInt64 = 0 from rfl, Bool.eq_iff_iff, beq_iff_eq, key_test,
    decide_eq_true_iff, eq_iff_key ht hm ht' hm']

/-- A word of the working area after a store to one. -/
theorem upd_wd (mem : UInt64 → Option UInt64) {a k : Nat} (v : Option UInt64) (ha : a < 2 ^ 61)
    (hk : k < 2 ^ 61) :
    Function.update mem (wd w a) v (wd w k) = if k = a then v else mem (wd w k) := by
  rw [Function.update_apply]
  simp only [wd_inj hk ha]

theorem sub_one_toUInt64 {a : Nat} (h : 0 < a) : a.toUInt64 - 1 = (a - 1).toUInt64 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [← toUInt64_succ, Nat.add_sub_cancel]
  simp

theorem upd_wd_ne (mem : UInt64 → Option UInt64) {a k : Nat} (v : Option UInt64) (h : k ≠ a)
    (ha : a < 2 ^ 61) (hk : k < 2 ^ 61) :
    Function.update mem (wd w a) v (wd w k) = mem (wd w k) := by
  rw [upd_wd mem v ha hk, iteF h]

theorem upd_wd_eq (mem : UInt64 → Option UInt64) {a k : Nat} (v : Option UInt64) (h : k = a) :
    Function.update mem (wd w a) v (wd w k) = v := by
  rw [h, Function.update_self]

/-- The form with a term appended. -/
theorem FZ.push {mem : UInt64 → Option UInt64} (hf : FZ mem w po cap f) (hn : f.size < cap)
    (hk : KeyAt mem w qo m) (hb : po + 1 + 5 * cap < 2 ^ 61) :
    FZ (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update mem (wd w (po + 1 + 5 * f.size)) (some m.size.toUInt64))
        (wd w (po + 1 + 5 * f.size + 1)) (some (m.getD 0 0).toUInt64))
        (wd w (po + 1 + 5 * f.size + 2)) (some (m.getD 1 0).toUInt64))
        (wd w (po + 1 + 5 * f.size + 3)) (some c.c0))
        (wd w (po + 1 + 5 * f.size + 4)) (some c.c1))
        (wd w po) (some (f.size + 1).toUInt64))
      w po cap (f.push ⟨m, 0 + c⟩) := by
  obtain ⟨hcap, hn0, ht⟩ := hf
  refine ⟨by rw [Array.size_push]; omega, by rw [Array.size_push, Function.update_self], fun i hi ↦ ?_⟩
  rw [Array.size_push] at hi
  rw [Array.getElem_push]
  split
  · rename_i hi'
    refine (ht i hi').congr fun k hk ↦ ?_
    simp (disch := omega) only [upd_wd_ne]
  · have hi' : i = f.size := by omega
    subst hi'
    obtain ⟨h1, h2, -⟩ := hk
    refine ⟨⟨h1, h2, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp (disch := omega) only [upd_wd_ne, upd_wd_eq] <;>
      rw [zero_add_ew]

/-- The form with term `j`'s coefficient words updated. -/
theorem FZ.addC {mem : UInt64 → Option UInt64} {j : Nat} (hf : FZ mem w po cap f) (hj : j < f.size)
    (hb : po + 1 + 5 * cap < 2 ^ 61) :
    FZ (Function.update (Function.update mem (wd w (po + 1 + 5 * j + 3))
        (some (f[j].coeff + c).c0)) (wd w (po + 1 + 5 * j + 4)) (some (f[j].coeff + c).c1))
      w po cap (f.modify j (addC c)) := by
  obtain ⟨hcap, hn, ht⟩ := hf
  refine ⟨by rw [Array.size_modify]; exact hcap, ?_, fun i hi ↦ ?_⟩
  · rw [Array.size_modify]
    simp (disch := omega) only [upd_wd]
    rw [iteF (by omega), iteF (by omega)]
    exact hn
  · rw [Array.size_modify] at hi
    rw [Array.getElem_modify]
    split
    · subst i
      obtain ⟨hk, -⟩ := ht j hi
      refine ⟨hk.congr fun k hk ↦ ?_, ?_, ?_⟩
      · simp (disch := omega) only [upd_wd]
        rw [iteF (by omega), iteF (by omega)]
      · simp (disch := omega) only [upd_wd]
        rw [iteF (by omega)]
        simp
      · simp (disch := omega) only [upd_wd]
        simp
    · refine (ht i hi).congr fun k hk ↦ ?_
      simp (disch := omega) only [upd_wd]
      rw [iteF (by omega), iteF (by omega)]

/-- **`FormW.addTerm` in words.** -/
theorem atCode_spec (h13 : s.reg .r13 = wd w po) (h12 : s.reg .r12 = wd w qo)
    (h9 : s.reg .r9 = c.c0) (h10 : s.reg .r10 = c.c1)
    (hf : FZ s.mem w po cap f) (hk : KeyAt s.mem w qo m)
    (hroom : (∃ t ∈ f, t.cols = m) ∨ f.size < cap)
    (hdom : ∀ k < 1 + 5 * cap, (s.mem (wd w (po + k))).isSome)
    (hsep : qo + 3 ≤ po ∨ po + 1 + 5 * cap ≤ qo) (hb : po + 1 + 5 * cap < 2 ^ 61)
    (hq : qo + 3 < 2 ^ 61) :
    WP atCode s (fun s' ↦ FZ s'.mem w po cap (f.addTerm m c) ∧
      KeepS w (fun k ↦ po ≤ k ∧ k < po + 1 + 5 * cap) s.mem s'.mem ∧ RegsFrame atRegs s s') E := by
  have hf' := hf
  obtain ⟨hcap, hn, ht⟩ := hf
  obtain ⟨hms, hmb, hk0, hk1, hk2⟩ := hk
  have hnb : f.size < 2 ^ 61 := by omega
  have hdom' : ∀ k, po ≤ k → k < po + 1 + 5 * cap → (s.mem (wd w k)).isSome := fun k h1 h2 ↦ by
    have := hdom (k - po) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  unfold atCode
  refine ldw (k := 0) h13 (by rw [Nat.add_zero]; exact hn) ?_
  refine lea_wd (k := 1) (by rsimp; exact h13) ?_
  refine wp_reg rfl ?_
  refine WP.blk_cons (WP.loop
    (fun t ↦ RegsFrame atRegs s t ∧ ((∃ j, AtScan w po f m s t j) ∨ AtFound w po cap f m c s t))
    (fun t ↦ (t.reg .rsi).toNat) ⟨by rf_tac, .inl ⟨0, by omega, by rsimp, by rsimp; simp,
      by rsimp, rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩⟩ ?_ ?_)
  · -- one pass
    rintro t ⟨hR, ⟨j, hj, hcx, hsi, hdx, hmem, hne⟩ | ⟨-, hsi, -⟩⟩ hc
    · have hjn : j < f.size := by
        rw [cond_ne, hsi, rhs_imm, fs_toUInt64_ne_zero (by omega)] at hc
        simp only [decide_eq_true_eq] at hc
        omega
      have h12' : t.reg .r12 = wd w qo := (hR .r12 (by decide)).trans h12
      have h9' : t.reg .r9 = c.c0 := (hR .r9 (by decide)).trans h9
      have h10' : t.reg .r10 = c.c1 := (hR .r10 (by decide)).trans h10
      obtain ⟨⟨hts, htb, ht0, ht1, ht2⟩, hc0, hc1⟩ := ht j hjn
      rw [← hmem] at ht0 ht1 ht2 hc0 hc1 hk0 hk1 hk2
      refine ldw (k := 0) hdx (by rw [Nat.add_zero]; exact ht0) ?_
      refine ldw (k := 0) (by rsimp; exact h12') (by rw [Nat.add_zero]; exact hk0) ?_
      refine wp_reg rfl ?_
      refine ldw (k := 1) (by rsimp; exact hdx) ht1 ?_
      refine ldw (k := 1) (by rsimp; exact h12') hk1 ?_
      refine wp_reg rfl ?_
      refine wp_reg rfl ?_
      refine ldw (k := 2) (by rsimp; exact hdx) ht2 ?_
      refine ldw (k := 2) (by rsimp; exact h12') hk2 ?_
      refine wp_reg rfl ?_
      refine wp_reg rfl ?_
      have hcmp := key_cmp hts hms htb hmb
      by_cases heq : f[j].cols = m
      · refine wp_ite_true (by rw [cond_eq, rhs_imm]; rsimp; exact hcmp.trans (decide_eq_true heq)) ?_
        have hd3 : (t.mem (wd w (po + 1 + 5 * j + 3))).isSome := by
          rw [hmem]; exact hdom' _ (by omega) (by omega)
        have hd4 : (t.mem (wd w (po + 1 + 5 * j + 4))).isSome := by
          rw [hmem]; exact hdom' _ (by omega) (by omega)
        refine ldw (k := 3) (by rsimp; exact hdx) hc0 ?_
        refine wp_reg rfl ?_
        refine stw (k := 3) (by rsimp; exact hdx) hd3 ?_
        refine ldw (k := 4) (by rsimp; exact hdx) (by mem_simp; exact hc1) ?_
        refine wp_reg rfl ?_
        refine stw (k := 4) (by rsimp; exact hdx) (by mem_simp; exact hd4) ?_
        refine wp_reg rfl ?_
        refine wp_reg rfl ?_
        refine wp_done ⟨⟨by rfx; exact hR, .inr ⟨by rsimp, by rsimp, j, ?_, ?_, ?_⟩⟩, ?_⟩
        · rw [Array.findIdx?_eq_some_iff_getElem]
          exact ⟨hjn, by simpa using heq, fun i hi ↦ by simpa using hne i hi (by omega)⟩
        · have := FZ.addC (c := c) hf' hjn hb
          rw [← hmem] at this
          rsimp
          rw [h9', h10']
          exact this
        · rw [← hmem]
          exact KeepS.setMem (KeepS.setMem (KeepS.refl _ _) (k := po + 1 + 5 * j + 3)
            ⟨by omega, by omega⟩ _) (k := po + 1 + 5 * j + 4) ⟨by omega, by omega⟩ _
        · rsimp
          rw [hsi, toNat_toUInt64 (by omega)]
          change 0 < _
          omega
      · refine wp_ite_false (by rw [cond_eq, rhs_imm]; rsimp; exact hcmp.trans (decide_eq_false heq)) ?_
        refine wp_reg rfl ?_
        refine wp_reg rfl ?_
        refine wp_done ⟨⟨by rfx; exact hR, .inl ⟨j + 1, by omega, by rsimp; exact hcx, ?_, ?_,
          hmem, fun i hi hi' ↦ ?_⟩⟩, ?_⟩
        · rsimp; rw [hsi, sub_one_toUInt64 (by omega)]; rfl
        · rsimp; rw [hdx, wd_add40]; rfl
        · rcases (show i < j ∨ i = j by omega) with h | rfl
          · exact hne i h hi'
          · exact heq
        · rsimp
          rw [hsi, sub_one_toUInt64 (by omega), toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
          omega
    · rw [cond_ne, hsi, rhs_imm] at hc
      exact absurd hc (by decide)
  · -- the loop's exit
    rintro t ⟨hR, ⟨j, hj, hcx, hsi, hdx, hmem, hne⟩ | ⟨hcx, -, i, hi, hfz, hkp⟩⟩ hc
    · have hjn : j = f.size := by
        rw [cond_ne, hsi, rhs_imm, fs_toUInt64_ne_zero (by omega)] at hc
        simp only [decide_eq_false_iff_not, not_not] at hc
        omega
      subst hjn
      have hnone : f.findIdx? (·.cols == m) = none := by
        rw [Array.findIdx?_eq_none_iff]
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
        simpa using hne i hi hi
      have hroom' : f.size < cap := by
        rcases hroom with ⟨x, hx, e⟩ | h
        · obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
          exact absurd e (hne i hi hi)
        · exact h
      have h12' : t.reg .r12 = wd w qo := (hR .r12 (by decide)).trans h12
      have h13' : t.reg .r13 = wd w po := (hR .r13 (by decide)).trans h13
      have h9' : t.reg .r9 = c.c0 := (hR .r9 (by decide)).trans h9
      have h10' : t.reg .r10 = c.c1 := (hR .r10 (by decide)).trans h10
      have hd : ∀ k < 5, (t.mem (wd w (po + 1 + 5 * f.size + k))).isSome := fun k hk ↦ by
        rw [hmem]; exact hdom' _ (by omega) (by omega)
      have hd0 : (t.mem (wd w (po + 0))).isSome := by rw [hmem, Nat.add_zero]; exact hdom' _ le_rfl (by omega)
      rw [← hmem] at hk0 hk1 hk2 hn
      refine wp_ite_true (by rw [cond_eq, hcx]; rfl) ?_
      refine ldw (k := 0) h12' (by rw [Nat.add_zero]; exact hk0) ?_
      refine stw (k := 0) (by rsimp; exact hdx) (hd 0 (by omega)) ?_
      refine ldw (k := 1) (by rsimp; exact h12') (by mem_simp; exact hk1) ?_
      refine stw (k := 1) (by rsimp; exact hdx) (by mem_simp; exact hd 1 (by omega)) ?_
      refine ldw (k := 2) (by rsimp; exact h12') (by mem_simp; exact hk2) ?_
      refine stw (k := 2) (by rsimp; exact hdx) (by mem_simp; exact hd 2 (by omega)) ?_
      refine stw (k := 3) (by rsimp; exact hdx) (by mem_simp; exact hd 3 (by omega)) ?_
      refine stw (k := 4) (by rsimp; exact hdx) (by mem_simp; exact hd 4 (by omega)) ?_
      refine ldw (k := 0) (by rsimp; exact h13') (by mem_simp; rw [Nat.add_zero]; exact hn) ?_
      refine wp_reg rfl ?_
      refine stw (k := 0) (by rsimp; exact h13') (by mem_simp; exact hd0) ?_
      refine wp_done ⟨?_, ?_, by rfx; exact hR⟩
      · unfold FormW.addTerm
        rw [hnone]
        have := FZ.push (c := c) hf' hroom' ⟨hms, hmb, hmem ▸ hk0, hmem ▸ hk1, hmem ▸ hk2⟩ hb
        rw [← hmem] at this
        rsimp
        rw [h9', h10', toUInt64_succ]
        exact this
      · rw [← hmem]
        exact KeepS.setMem (KeepS.setMem (KeepS.setMem (KeepS.setMem (KeepS.setMem (KeepS.setMem
          (KeepS.refl _ _) (k := po + 1 + 5 * f.size + 0) ⟨by omega, by omega⟩ _)
          (k := po + 1 + 5 * f.size + 1) ⟨by omega, by omega⟩ _)
          (k := po + 1 + 5 * f.size + 2) ⟨by omega, by omega⟩ _)
          (k := po + 1 + 5 * f.size + 3) ⟨by omega, by omega⟩ _)
          (k := po + 1 + 5 * f.size + 4) ⟨by omega, by omega⟩ _) (k := po + 0) ⟨by omega, by omega⟩ _
    · refine wp_ite_false (by rw [cond_eq, hcx]; rfl) (WP.skip ⟨?_, hkp, hR⟩)
      unfold FormW.addTerm
      rw [hi]
      exact hfz

end NativeVm.Code.P3
