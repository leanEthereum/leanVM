module

public import NativeVm.Code.Phase3.FormsBuild

/-!
# The bus forms of a side: the padding rows' term

`evLoop_spec`: the block form's value on the padding row (`FormW.evaluate`), each term's coefficient
times its columns' padding lanes (`tvCode`, `scaleCol`), summed in `(r14, r15)`.
`evalCode_spec`: `sumR side += sel · pw · (F.evaluate row + 1)`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

variable {w ctx : UInt64} {s : QState} {E : QState → Prop}

/-- A term's value on a row. -/
def tvOf (row : Array EW) (t : TermW) : EW := t.cols.foldl (fun acc i ↦ acc * row.getD i 0) t.coeff

theorem evaluate_eq (F : FormW) (row : Array EW) :
    F.evaluate row = (F.toList.map (tvOf row)).foldl (· + ·) 0 := by
  unfold FormW.evaluate sumE
  rw [← Array.foldl_toList, Array.toList_map]
  rfl

/-- A monomial's fold, by its degree (at most two). -/
theorem foldl_small {β : Type} (c : Array Nat) (f : β → Nat → β) (init : β) (h : c.size ≤ 2) :
    c.foldl f init = if c.size = 0 then init else if c.size = 1 then f init (c.getD 0 0)
      else f (f init (c.getD 0 0)) (c.getD 1 0) := by
  rcases c with ⟨l⟩
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · simp at h

/-- The padding row's lanes from word `padOff`. -/
def PadAt (mem : UInt64 → Option UInt64) (w : UInt64) : Prop := ∀ a < 92, mem (wd w (padOff + a)) = some (Pv a)

/-- `A := A · P[column]`. -/
theorem scaleCol_spec {q k a : Nat} {v : EW} (hsi : s.reg .rsi = wd w q)
    (hbp : s.reg .rbp = wd w padOff) (ha : s.mem (wd w (q + k)) = some a.toUInt64)
    (hP : s.mem (wd w (padOff + a)) = some (Pv a)) (h9 : s.reg .r9 = v.c0)
    (h10 : s.reg .r10 = v.c1) :
    WP (scaleCol k) s (fun s' ↦ s'.reg .r9 = (v * kE (Pv a)).c0 ∧ s'.reg .r10 = (v * kE (Pv a)).c1 ∧
      s'.mem = s.mem ∧ RegsFrame [.rax, .rbx, .rcx, .r8, .r9, .r10, .r11] s s') E := by
  unfold scaleCol
  refine ldw (w := w) (j := q) (k := k) hsi ha ?_
  refine ldx (w := w) (j := padOff) (i := a) (k := 0) (by rsimp; exact hbp) (by rsimp)
    (by rw [Nat.add_zero]; exact hP) ?_
  refine WP.mono (escale_spec _) (fun s2 ⟨he, hm, hf⟩ ↦ ?_) (fun _ h ↦ h)
  rsimp at he
  rw [h9, h10] at he
  have : s2.reg .r9 = (v * kE (Pv a)).c0 ∧ s2.reg .r10 = (v * kE (Pv a)).c1 := by
    rw [← eOf_eq_toE, he, NativeVm.Equiv.EW.toE_mul, show kE (Pv a) = EW.ofK (Pv a) from rfl,
      NativeVm.Equiv.EW.toE_ofK]
    rfl
  refine ⟨this.1, this.2, hm, ?_⟩
  refine rf_trans (l' := sqRegs) (hl := List.Subset.refl _) ?_ hf
  rfx
  exact rf_refl _ _

/-- **A term's value** on the padding row, its coefficient in `A` and its degree in `rax`. -/
theorem tvCode_spec {q : Nat} {t : TermW} {row : Array EW} (hsi : s.reg .rsi = wd w q)
    (hbp : s.reg .rbp = wd w padOff) (hk : KeyAt s.mem w q t.cols) (hpad : PadAt s.mem w)
    (hrow : ∀ a ∈ t.cols, a < 92 ∧ row.getD a 0 = kE (Pv a))
    (hax : s.reg .rax = t.cols.size.toUInt64) (h9 : s.reg .r9 = t.coeff.c0)
    (h10 : s.reg .r10 = t.coeff.c1) :
    WP tvCode s (fun s' ↦ s'.reg .r9 = (tvOf row t).c0 ∧ s'.reg .r10 = (tvOf row t).c1 ∧
      s'.mem = s.mem ∧ RegsFrame [.rax, .rbx, .rcx, .r8, .r9, .r10, .r11] s s') E := by
  obtain ⟨hs, hb, h0, h1, h2⟩ := hk
  have hv : tvOf row t = if t.cols.size = 0 then t.coeff else if t.cols.size = 1 then
      t.coeff * kE (Pv (t.cols.getD 0 0)) else
      t.coeff * kE (Pv (t.cols.getD 0 0)) * kE (Pv (t.cols.getD 1 0)) := by
    unfold tvOf
    rw [foldl_small _ _ _ hs]
    have g : ∀ i (h : i < t.cols.size), row.getD (t.cols.getD i 0) 0 = kE (Pv (t.cols.getD i 0)) :=
      fun i h ↦ by
        rw [show t.cols.getD i 0 = t.cols[i] by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]; rfl]
        exact (hrow _ (Array.getElem_mem h)).2
    split
    · rfl
    · split
      · rw [g 0 (by omega)]
      · rw [g 0 (by omega), g 1 (by omega)]
  have gb : ∀ i (h : i < t.cols.size), t.cols.getD i 0 < 92 := fun i h ↦ by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
    exact (hrow _ (Array.getElem_mem h)).1
  unfold tvCode
  by_cases hz : t.cols.size = 0
  · refine wp_ite_true (by rw [cond_eq, hax, hz]; rfl) (WP.skip ⟨?_, ?_, rfl, rf_refl _ _⟩)
    · rw [hv, iteT hz]; exact h9
    · rw [hv, iteT hz]; exact h10
  · have hne : (Cond.cmp .eq .rax (.imm 0)).eval s = false := by
      rw [cond_eq, hax, rhs_imm, show (0 : Int64).toUInt64 = (0 : Nat).toUInt64 from rfl]
      simp only [beq_eq_false_iff_ne, ne_eq]
      rw [NativeVm.Transcript.toUInt64_inj (by omega) (by omega)]
      exact hz
    refine wp_ite_false hne ?_
    refine wp_then' (scaleCol_spec (E := E) (w := w) (q := q) (k := 1) (a := t.cols.getD 0 0) hsi hbp h1
      (hpad _ (gb 0 (by omega))) h9 h10) fun s1 ⟨a9, a10, am, af⟩ _ ↦ ?_
    have s1si : s1.reg .rsi = wd w q := (af .rsi (by decide)).trans hsi
    refine ldw (w := w) (j := q) (k := 0) s1si (by rw [am, Nat.add_zero]; exact h0) ?_
    by_cases h1' : t.cols.size = 1
    · refine wp_ite_true (by rw [cond_eq]; rsimp; rw [h1']; rfl)
        (WP.skip ⟨?_, ?_, by rsimp; exact am, ?_⟩)
      · rsimp; rw [a9, hv, iteF hz, iteT h1']
      · rsimp; rw [a10, hv, iteF hz, iteT h1']
      · exact rf_trans (l' := [.rax, .rbx, .rcx, .r8, .r9, .r10, .r11]) (hl := List.Subset.refl _)
          af (by rfx; exact rf_refl _ _)
    · have hne1 : (Cond.cmp .eq .rax (.imm 1)).eval (s1.setReg .rax t.cols.size.toUInt64) = false := by
        rw [cond_eq, rhs_imm]; rsimp
        rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl]
        simp only [beq_eq_false_iff_ne, ne_eq]
        rw [NativeVm.Transcript.toUInt64_inj (by omega) (by omega)]
        exact h1'
      refine wp_ite_false hne1 ?_
      refine WP.mono (scaleCol_spec (E := E) (w := w) (q := q) (k := 2) (a := t.cols.getD 1 0)
        (v := t.coeff * kE (Pv (t.cols.getD 0 0)))
        (by rsimp; exact s1si) (by rsimp; rw [af .rbp (by decide)]; exact hbp)
        (by rsimp; rw [am]; exact h2) (by rsimp; rw [am]; exact hpad _ (gb 1 (by omega)))
        (by rsimp; exact a9) (by rsimp; exact a10)) (fun s2 ⟨b9, b10, bm, bf'⟩ ↦ ?_) (fun _ h ↦ h)
      refine ⟨?_, ?_, by rw [bm]; rsimp; exact am, ?_⟩
      · rw [b9, hv, iteF hz, iteF h1']
      · rw [b10, hv, iteF hz, iteF h1']
      · exact rf_trans (l' := [.rax, .rbx, .rcx, .r8, .r9, .r10, .r11]) (hl := List.Subset.refl _)
          (rf_trans (l' := [.rax, .rbx, .rcx, .r8, .r9, .r10, .r11]) (hl := List.Subset.refl _) af
            (by rfx; exact rf_refl _ _)) bf'

/-- The registers the terms' loop writes. -/
abbrev evRegs : List Reg64 := [.rax, .rbx, .rcx, .r8, .r9, .r10, .r11, .r14, .r15, .rsi]

/-- The sum of the first `j` terms' values. -/
def evJ (F : FormW) (row : Array EW) (j : Nat) : EW := ((F.toList.take j).map (tvOf row)).foldl (· + ·) 0

theorem evJ_succ {F : FormW} {row : Array EW} {j : Nat} (hj : j < F.size) :
    evJ F row (j + 1) = evJ F row j + tvOf row F[j] := by
  have : j < F.toList.length := by simpa using hj
  rw [evJ, evJ, List.take_add_one, List.getElem?_eq_getElem this, Option.toList_some, List.map_append,
    List.foldl_append]
  simp

/-- **The block form on the padding row**, summed in `(r14, r15)`. -/
theorem evLoop_spec {F : FormW} {row : Array EW} (hsi : s.reg .rsi = wd w (fOff + 1))
    (hdx : s.reg .rdx = wd w (fOff + 1 + 5 * F.size)) (hbp : s.reg .rbp = wd w padOff)
    (h14 : s.reg .r14 = 0) (h15 : s.reg .r15 = 0) (hF : FZ s.mem w fOff fCap F)
    (hpad : PadAt s.mem w) (hrow : ∀ t ∈ F, ∀ a ∈ t.cols, a < 92 ∧ row.getD a 0 = kE (Pv a)) :
    WP evLoop s (fun s' ↦ s'.reg .r14 = (F.evaluate row).c0 ∧ s'.reg .r15 = (F.evaluate row).c1 ∧
      s'.mem = s.mem ∧ RegsFrame evRegs s s') E := by
  have v1 := fOff_val
  have v5 := fCap_val
  obtain ⟨hcap, -, ht⟩ := hF
  unfold evLoop
  refine WP.loop (fun t ↦ ∃ j ≤ F.size, t.reg .rsi = wd w (fOff + 1 + 5 * j) ∧
      t.reg .rdx = wd w (fOff + 1 + 5 * F.size) ∧ t.reg .rbp = wd w padOff ∧
      t.reg .r14 = (evJ F row j).c0 ∧ t.reg .r15 = (evJ F row j).c1 ∧ t.mem = s.mem ∧
      RegsFrame evRegs s t)
    (fun t ↦ (t.reg .rdx - t.reg .rsi).toNat)
    ⟨0, by omega, hsi, hdx, hbp, h14, h15, rfl, fun _ _ ↦ rfl⟩ ?_ ?_
  · rintro t ⟨j, hj, a1, a2, a3, a4, a5, am, aR⟩ hc
    have hjn : j < F.size := by
      rw [cond_ne, a1, rhs_reg, a2] at hc
      by_contra hn'
      have : j = F.size := by omega
      subst this
      simp at hc
    obtain ⟨hk, c0, c1⟩ := ht j hjn
    rw [← am] at hk c0 c1 hpad
    have hk' := hk
    obtain ⟨-, -, k0, -, -⟩ := hk'
    refine ldw (w := w) (j := fOff + 1 + 5 * j) (k := 3) a1 c0 ?_
    refine ldw (w := w) (j := fOff + 1 + 5 * j) (k := 4) (by rsimp; exact a1) c1 ?_
    refine ldw (w := w) (j := fOff + 1 + 5 * j) (k := 0) (by rsimp; exact a1)
      (by rw [Nat.add_zero]; exact k0) ?_
    refine wp_then' (tvCode_spec (E := E) (w := w) (q := fOff + 1 + 5 * j) (t := F[j]) (row := row)
      (by rsimp; exact a1) (by rsimp; exact a3) hk hpad
      (hrow _ (Array.getElem_mem hjn)) (by rsimp) (by rsimp) (by rsimp)) fun t1 ⟨b9, b10, bm, bR⟩ _ ↦ ?_
    have g : ∀ r ∉ [Reg64.rax, .rbx, .rcx, .r8, .r9, .r10, .r11], t1.reg r = t.reg r := fun r hr ↦ by
      rw [bR r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rsimp
      simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1]
    refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_done ⟨⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ?_⟩)))
    · rsimp; rw [g .rsi (by decide), a1, wd_add40, show fOff + 1 + 5 * j + 5 = fOff + 1 + 5 * (j + 1) by
        omega]
    · rsimp; rw [g .rdx (by decide), a2]
    · rsimp; rw [g .rbp (by decide), a3]
    · rsimp; rw [g .r14 (by decide), a4, b9, evJ_succ hjn]; rfl
    · rsimp; rw [g .r15 (by decide), a5, b10, evJ_succ hjn]; rfl
    · rsimp; rw [bm]; exact am
    · rfx
      refine rf_trans (l' := [.rax, .rbx, .rcx, .r8, .r9, .r10, .r11]) (hl := List.Subset.refl _) ?_ bR
      rfx
      exact aR
    · rsimp
      rw [g .rdx (by decide), g .rsi (by decide), a1, a2, wd_add40,
        wd_sub_toNat (by omega) (by oo), wd_sub_toNat (by omega) (by oo)]
      omega
  · rintro t ⟨j, hj, a1, a2, a3, a4, a5, am, aR⟩ hc
    have hjn : j = F.size := by
      rw [cond_ne, a1, rhs_reg, a2] at hc
      simp only [bne_eq_false_iff_eq] at hc
      exact (by have := (wd_inj (b := w) (by oo) (by oo)).mp hc; omega)
    subst hjn
    have e : evJ F row F.size = F.evaluate row := by
      rw [evJ, evaluate_eq, List.take_of_length_le (by simp)]
    rw [e] at a4 a5
    exact ⟨a4, a5, am, aR⟩

/-- The loop's start. -/
theorem evPre_spec {F : FormW} (hrdi : s.reg .rdi = ctx) (hwp : s.mem (wd ctx ctxWork) = some w)
    (hF : FZ s.mem w fOff fCap F) :
    WP evPre s (fun s' ↦ s'.reg .rsi = wd w (fOff + 1) ∧ s'.reg .rdx = wd w (fOff + 1 + 5 * F.size) ∧
      s'.reg .rbp = wd w padOff ∧ s'.reg .r14 = 0 ∧ s'.reg .r15 = 0 ∧ s'.mem = s.mem ∧
      s'.reg .rdi = ctx) E := by
  have v5 := fCap_val
  have hs := hF.1
  unfold evPre
  refine wk_wp hrdi hwp ?_
  refine lea0 (w := w) (k := fOff + 1) (by rsimp) ?_
  refine ldw0 (w := w) (k := fOff) (by rsimp) hF.2.1 ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl ?_))))))
  refine lea0 (w := w) (k := padOff) (by rsimp) ?_
  refine wp_done ⟨by rsimp, ?_, by rsimp, by rsimp, by rsimp, rfl, by rsimp; exact hrdi⟩
  rsimp
  rw [times40, add_comm, wd_eq_add]

theorem add_one_ew (x : EW) : x + 1 = ⟨x.c0 ^^^ 1, x.c1⟩ := by
  show EW.mk _ (x.c1 ^^^ 0) = _
  rw [UInt64.xor_zero]
  rfl

theorem sumR_off (side : Nat) : (sumR side).off = 54462 + 8 * side := by
  show scratchR.off + (1792 + 8 * side) = _
  rw [scratchR_off]; omega

/-- **The padding rows' term added**: `S + sel · pw · (ev + 1)`. -/
theorem evPost_spec {side sp : Nat} {ev sel pw S : EW} (h14 : s.reg .r14 = ev.c0)
    (h15 : s.reg .r15 = ev.c1) (hrdi : s.reg .rdi = ctx) (hwp : s.mem (wd ctx ctxWork) = some w)
    (hsel : s.mem (wd w vSel) = some (wd w sp)) (hs : EAtI s.mem w sp sel)
    (hp : EAtI s.mem w (sp + 102) pw) (hS : EAtI s.mem w (sumR side).off S) (hside : side < 3) :
    WP (evPost side) s (fun s' ↦ s'.reg .rdi = ctx ∧
      EAtI s'.mem w (sumR side).off (S + sel * pw * (ev + 1)) ∧
      KeepS w (fun k ↦ k = (sumR side).off ∨ k = (sumR side).off + 1) s.mem s'.mem) E := by
  have so := sumR_off side
  unfold evPost
  refine wp_reg rfl ?_
  refine wk_wp (by rsimp; exact hrdi) hwp ?_
  refine ldw0 (w := w) (k := vSel) (by rsimp) hsel ?_
  refine ldw (w := w) (j := sp) (k := 0) (by rsimp) (by rw [Nat.add_zero]; exact hs.1) ?_
  refine ldw (w := w) (j := sp) (k := 1) (by rsimp) hs.2 ?_
  refine ldw (w := w) (j := sp) (k := 102) (by rsimp) hp.1 ?_
  refine ldw (w := w) (j := sp) (k := 103) (by rsimp) hp.2 ?_
  refine WP.then (emul_spec _) fun t1 ⟨e1, m1, f1⟩ ↦ ?_
  rsimp at e1
  have p1 : t1.reg .r9 = (sel * pw).c0 ∧ t1.reg .r10 = (sel * pw).c1 := by
    rw [← eOf_eq_toE, e1, NativeVm.Equiv.EW.toE_mul]; rfl
  have g14 : t1.reg .r14 = ev.c0 ^^^ 1 := by rw [f1 .r14 (by decide)]; rsimp; rw [h14]
  have g15 : t1.reg .r15 = ev.c1 := by rw [f1 .r15 (by decide)]; rsimp; exact h15
  have gdi : t1.reg .rdi = ctx := by rw [f1 .rdi (by decide)]; rsimp; exact hrdi
  refine wp_reg rfl (wp_reg rfl ?_)
  refine WP.then (emul_spec _) fun t2 ⟨e2, m2, f2⟩ ↦ ?_
  rsimp at e2
  rw [p1.1, p1.2, g14, g15] at e2
  have p2 : t2.reg .r9 = (sel * pw * (ev + 1)).c0 ∧ t2.reg .r10 = (sel * pw * (ev + 1)).c1 := by
    rw [add_one_ew, ← eOf_eq_toE, e2, NativeVm.Equiv.EW.toE_mul]
    rfl
  have gdi2 : t2.reg .rdi = ctx := by rw [f2 .rdi (by decide)]; rsimp; exact gdi
  have mm : t2.mem = s.mem := by rw [m2]; show t1.mem = s.mem; rw [m1]; rfl
  refine wk_wp gdi2 (by rw [mm]; exact hwp) ?_
  refine ldw0 (w := w) (k := (sumR side).off) (by rsimp) (by rsimp; rw [mm]; exact hS.1) ?_
  refine wp_reg rfl ?_
  refine stw0 (w := w) (k := (sumR side).off) (by rsimp) (by rsimp; rw [mm, hS.1]; rfl) ?_
  refine ldw0 (w := w) (k := (sumR side).off + 1) (by rsimp)
    (by mem_simp; rw [mm]; exact hS.2) ?_
  refine wp_reg rfl ?_
  refine stw0 (w := w) (k := (sumR side).off + 1) (by rsimp)
    (by mem_simp; rw [mm, hS.2]; rfl) ?_
  refine wp_done ⟨by rsimp; exact gdi2, ⟨?_, ?_⟩, ?_⟩
  · mem_simp; rw [p2.1]; rfl
  · mem_simp; rw [p2.2]; rfl
  · rw [← mm]
    keep_tac



/-- **The padding rows' term**: `sumR side += sel · pw · (F.evaluate row + 1)`, the selector at the
word `vSel` holds, its padding weight `102` words on. -/
theorem evalCode_spec {side sp : Nat} {F : FormW} {row : Array EW} {sel pw S : EW}
    (hrdi : s.reg .rdi = ctx) (hwp : s.mem (wd ctx ctxWork) = some w)
    (hF : FZ s.mem w fOff fCap F) (hpad : PadAt s.mem w)
    (hrow : ∀ t ∈ F, ∀ a ∈ t.cols, a < 92 ∧ row.getD a 0 = kE (Pv a))
    (hsel : s.mem (wd w vSel) = some (wd w sp)) (hs : EAtI s.mem w sp sel)
    (hp : EAtI s.mem w (sp + 102) pw) (hS : EAtI s.mem w (sumR side).off S) (hside : side < 3) :
    WP (evalCode side) s (fun s' ↦ s'.reg .rdi = ctx ∧
      EAtI s'.mem w (sumR side).off (S + sel * pw * (F.evaluate row + 1)) ∧
      KeepS w (fun k ↦ k = (sumR side).off ∨ k = (sumR side).off + 1) s.mem s'.mem) E := by
  unfold evalCode
  refine wp_then' (evPre_spec (E := E) hrdi hwp hF) fun s1 ⟨a1, a2, a3, a4, a5, am, ar⟩ _ ↦ ?_
  refine wp_then' (evLoop_spec (E := E) (row := row) a1 a2 a3 a4 a5 (by rw [am]; exact hF)
    (by rw [am]; exact hpad) hrow) fun s2 ⟨b14, b15, bm, bR⟩ _ ↦ ?_
  have mm : s2.mem = s.mem := bm.trans am
  refine WP.mono (evPost_spec (E := E) (side := side) (sp := sp) b14 b15
    ((bR .rdi (by decide)).trans ar) (by rw [mm]; exact hwp) (by rw [mm]; exact hsel)
    (by rw [mm]; exact hs) (by rw [mm]; exact hp) (by rw [mm]; exact hS) hside)
    (fun s3 ⟨c1, c2, c3⟩ ↦ ⟨c1, c2, by rw [← mm]; exact c3⟩) (fun _ h ↦ h)

end NativeVm.Code.P3
