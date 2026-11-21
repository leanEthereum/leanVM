module

public import NativeVm.Code.Phase3.FormsBuild

/-!
# The bus forms of a side: the owner's form

`acLoop_spec`: for each term of the block form, `G.addTerm m (sel · c)` (`emul`, then `atCode`), so
`G` becomes `G.addScaled F sel`; there is room for every new monomial when the result's monomials
fit `formCap` (`room_gJ`, from the shapes). `accCode_spec`: the loop, the next selector and one
block fewer.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

variable {w ctx : UInt64} {s : QState} {E : QState → Prop}

/-- `G` after the first `j` terms of `F`. -/
def gJ (g F : FormW) (sel : EW) (j : Nat) : FormW :=
  (F.toList.take j).foldl (fun acc t ↦ acc.addTerm t.cols (sel * t.coeff)) g

theorem gJ_succ {g F : FormW} {sel : EW} {j : Nat} (hj : j < F.size) :
    gJ g F sel (j + 1) = (gJ g F sel j).addTerm F[j].cols (sel * F[j].coeff) := by
  have : j < F.toList.length := by simpa using hj
  rw [gJ, gJ, List.take_add_one, List.getElem?_eq_getElem this, Option.toList_some, List.foldl_append]
  simp

theorem gJ_all (g F : FormW) (sel : EW) : gJ g F sel F.size = g.addScaled F sel := by
  rw [gJ, List.take_of_length_le (by simp), FormW.addScaled, ← Array.foldl_toList]

theorem shape_gJ (g F : FormW) (sel : EW) (j : Nat) :
    shape (gJ g F sel j) = ((shape F).take j).foldl addMono (shape g) := by
  rw [gJ, shape_foldl_addTerm]
  simp [shape, List.map_take]

theorem size_eq_shape (f : FormW) : f.size = (shape f).length := by simp [shape]

/-- **Room for term `j`**: its monomial is in `G` already, or `G` has fewer than `formCap` terms. -/
theorem room_gJ {g F : FormW} {sel : EW} {j : Nat} (hj : j < F.size)
    (hroom : ((shape F).foldl addMono (shape g)).length ≤ formCap) :
    (∃ t ∈ gJ g F sel j, t.cols = F[j].cols) ∨ (gJ g F sel j).size < formCap := by
  by_cases hm : F[j].cols.toList ∈ shape (gJ g F sel j)
  · left
    simp only [shape, List.mem_map, Array.mem_toList_iff] at hm
    obtain ⟨t, ht, e⟩ := hm
    exact ⟨t, ht, Array.toList_inj.mp e⟩
  · right
    have h1 := shape_addTerm (gJ g F sel j) F[j].cols (sel * F[j].coeff)
    rw [← gJ_succ hj, addMono, iteF hm] at h1
    have h2 : shape (gJ g F sel (j + 1)) <+: (shape F).foldl addMono (shape g) := by
      rw [shape_gJ]
      conv_rhs => rw [← List.take_append_drop (j + 1) (shape F)]
      exact foldl_addMono_append _ _ _
    have := h2.length_le
    rw [h1, List.length_append, List.length_singleton] at this
    rw [size_eq_shape]
    omega

/-- The registers the terms' loop writes. -/
abbrev acRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r12, .r14]

/-- **`G := G.addScaled F sel`**, `G` at word `go`, `F` the block form, the selector at word `sp`. -/
theorem acLoop_spec {go sp : Nat} {g F : FormW} {sel : EW}
    (h13 : s.reg .r13 = wd w go) (h14 : s.reg .r14 = wd w (fOff + 1))
    (h15 : s.reg .r15 = wd w (fOff + 1 + 5 * F.size)) (hbp : s.reg .rbp = wd w sp)
    (hG : FZ s.mem w go formCap g) (hF : FZ s.mem w fOff fCap F) (hs : EAtI s.mem w sp sel)
    (hroom : ((shape F).foldl addMono (shape g)).length ≤ formCap)
    (hdom : ∀ k < 1 + 5 * formCap, (s.mem (wd w (go + k))).isSome)
    (hgo : go + 1 + 5 * formCap ≤ fOff) (hsp : sp + 2 ≤ go ∨ go + 1 + 5 * formCap ≤ sp)
    (hsp' : sp + 2 < 2 ^ 61) :
    WP acLoop s (fun s' ↦ FZ s'.mem w go formCap (g.addScaled F sel) ∧
      KeepS w (fun k ↦ go ≤ k ∧ k < go + 1 + 5 * formCap) s.mem s'.mem ∧
      RegsFrame acRegs s s') E := by
  have v1 := fOff_val
  have v5 := fCap_val
  have vc : formCap = 148 := rfl
  have hFs := hF.1
  unfold acLoop
  refine WP.loop (fun t ↦ ∃ j ≤ F.size, t.reg .r14 = wd w (fOff + 1 + 5 * j) ∧
      FZ t.mem w go formCap (gJ g F sel j) ∧
      KeepS w (fun k ↦ go ≤ k ∧ k < go + 1 + 5 * formCap) s.mem t.mem ∧ RegsFrame acRegs s t ∧
      ∀ k < 1 + 5 * formCap, (t.mem (wd w (go + k))).isSome)
    (fun t ↦ (t.reg .r15 - t.reg .r14).toNat)
    ⟨0, by omega, h14, hG, KeepS.refl _ _, fun _ _ ↦ rfl, hdom⟩ ?_ ?_
  · rintro t ⟨j, hj, a14, aG, aK, aR, aD⟩ hc
    have a15 : t.reg .r15 = wd w (fOff + 1 + 5 * F.size) := (aR .r15 (by decide)).trans h15
    have hjn : j < F.size := by
      rw [cond_ne, a14, rhs_reg, a15] at hc
      by_contra hn'
      have : j = F.size := by omega
      subst this
      simp at hc
    have kw : ∀ k, k < 2 ^ 61 → (k < go ∨ go + 1 + 5 * formCap ≤ k) → t.mem (wd w k) = s.mem (wd w k) :=
      fun k hk hk' ↦ aK.word (by omega) fun i hi ↦ ⟨by omega, by omega⟩
    obtain ⟨hk, c0, c1⟩ := hF.2.2 j hjn
    have abp : t.reg .rbp = wd w sp := (aR .rbp (by decide)).trans hbp
    have a13 : t.reg .r13 = wd w go := (aR .r13 (by decide)).trans h13
    refine ldw (w := w) (j := sp) (k := 0) abp
      (by rw [Nat.add_zero, kw sp (by omega) (by omega)]; exact hs.1) ?_
    refine ldw (w := w) (j := sp) (k := 1) (by rsimp; exact abp)
      (by rsimp; rw [kw (sp + 1) (by omega) (by omega)]; exact hs.2) ?_
    refine ldw (w := w) (j := fOff + 1 + 5 * j) (k := 3) (by rsimp; exact a14)
      (by rsimp; rw [kw _ (by omega) (by omega)]; exact c0) ?_
    refine ldw (w := w) (j := fOff + 1 + 5 * j) (k := 4) (by rsimp; exact a14)
      (by rsimp; rw [kw _ (by omega) (by omega)]; exact c1) ?_
    refine WP.then (emul_spec _) fun t1 ⟨e1, m1, f1⟩ ↦ ?_
    rsimp at e1
    have p1 : t1.reg .r9 = (sel * F[j].coeff).c0 ∧ t1.reg .r10 = (sel * F[j].coeff).c1 := by
      rw [← eOf_eq_toE, e1, NativeVm.Equiv.EW.toE_mul]; rfl
    have g1 : ∀ r ∉ eRegs, r ≠ .r11 → r ≠ .r12 → t1.reg r = t.reg r := fun r hr h11 h12 ↦ by
      rw [f1 r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rsimp
      simp [hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, h11, h12]
    have mt : t1.mem = t.mem := m1
    refine wp_reg rfl ?_
    refine wp_then' (atCode_spec (E := E) (w := w) (po := go) (qo := fOff + 1 + 5 * j) (cap := formCap)
      (f := gJ g F sel j) (m := F[j].cols) (c := sel * F[j].coeff)
      (by rsimp; rw [g1 .r13 (by decide) (by decide) (by decide)]; exact a13)
      (by rsimp; rw [g1 .r14 (by decide) (by decide) (by decide)]; exact a14)
      (by rsimp; exact p1.1) (by rsimp; exact p1.2)
      (by rsimp; rw [mt]; exact aG)
      (by rsimp; rw [mt]; exact hk.congr fun k hk' ↦ kw _ (by omega) (by omega))
      (room_gJ hjn hroom) (fun k hk' ↦ by rsimp; rw [mt]; exact aD k hk')
      (.inr (by omega)) (by omega) (by omega)) fun t2 ⟨b1, b2, b3⟩ bd ↦ ?_
    have a14' : t2.reg .r14 = wd w (fOff + 1 + 5 * j) := by
      rw [b3 .r14 (by decide)]; rsimp; rw [g1 .r14 (by decide) (by decide) (by decide)]; exact a14
    refine wp_reg rfl (wp_done ⟨⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    · rsimp; rw [a14', wd_add40, show fOff + 1 + 5 * j + 5 = fOff + 1 + 5 * (j + 1) by omega]
    · rsimp; rw [gJ_succ hjn]; exact b1
    · rsimp
      have b2' : KeepS w (fun k ↦ go ≤ k ∧ k < go + 1 + 5 * formCap) t.mem t2.mem := by
        rw [← mt]; exact b2
      exact aK.trans b2' (fun k h ↦ h) (fun k h ↦ h)
    · rfx
      refine rf_trans (l' := atRegs) (hl := List.Subset.refl _) ?_ b3
      rfx
      refine rf_trans (l' := eRegs) (hl := List.Subset.refl _) ?_ f1
      rfx
      exact aR
    · intro k hk
      rsimp
      rw [bd]
      rsimp
      rw [mt]
      exact aD k hk
    · have a15' : t2.reg .r15 = wd w (fOff + 1 + 5 * F.size) := by
        rw [b3 .r15 (by decide)]; rsimp; rw [g1 .r15 (by decide) (by decide) (by decide)]; exact a15
      rsimp
      rw [a15', a14', a14, a15, wd_add40, wd_sub_toNat (by omega) (by omega),
        wd_sub_toNat (by omega) (by omega)]
      omega
  · rintro t ⟨j, hj, a14, aG, aK, aR, -⟩ hc
    have a15 : t.reg .r15 = wd w (fOff + 1 + 5 * F.size) := (aR .r15 (by decide)).trans h15
    have hjn : j = F.size := by
      rw [cond_ne, a14, rhs_reg, a15] at hc
      simp only [bne_eq_false_iff_eq] at hc
      exact (by have := (wd_inj (b := w) (by omega) (by omega)).mp hc; omega)
    subst hjn
    exact ⟨by rw [← gJ_all]; exact aG, aK, aR⟩


/-- The loop's start. -/
theorem accPre_spec {go sp : Nat} {F : FormW} (hrdi : s.reg .rdi = ctx)
    (hwp : s.mem (wd ctx ctxWork) = some w) (hvg : s.mem (wd w vG) = some (wd w go))
    (hvs : s.mem (wd w vSel) = some (wd w sp)) (hF : FZ s.mem w fOff fCap F) :
    WP accPre s (fun s' ↦ s'.reg .r13 = wd w go ∧ s'.reg .rbp = wd w sp ∧
      s'.reg .r14 = wd w (fOff + 1) ∧ s'.reg .r15 = wd w (fOff + 1 + 5 * F.size) ∧
      s'.mem = s.mem ∧ s'.reg .rdi = ctx) E := by
  unfold accPre
  refine wk_wp hrdi hwp ?_
  refine ldw0 (w := w) (k := vG) (by rsimp) hvg ?_
  refine ldw0 (w := w) (k := vSel) (by rsimp) hvs ?_
  refine lea0 (w := w) (k := fOff + 1) (by rsimp) ?_
  refine ldw0 (w := w) (k := fOff) (by rsimp) hF.2.1 ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_done ⟨by rsimp, by rsimp,
    by rsimp, ?_, rfl, by rsimp; exact hrdi⟩)))))
  rsimp
  rw [times40, add_comm, wd_eq_add]

/-- The next selector, one block fewer. -/
theorem accPost_spec {sp rem : Nat} (hrdi : s.reg .rdi = ctx) (hwp : s.mem (wd ctx ctxWork) = some w)
    (hvs : s.mem (wd w vSel) = some (wd w sp)) (hvr : s.mem (wd w vRem) = some rem.toUInt64)
    (hrem : 0 < rem) :
    WP accPost s (fun s' ↦ s'.mem (wd w vSel) = some (wd w (sp + 2)) ∧
      s'.mem (wd w vRem) = some (rem - 1).toUInt64 ∧ s'.reg .rax = (rem - 1).toUInt64 ∧
      KeepS w (fun k ↦ k = vSel ∨ k = vRem) s.mem s'.mem ∧ s'.reg .rdi = ctx) E := by
  have v1 := vSel_val
  have v2 := vRem_val
  unfold accPost
  refine wk_wp hrdi hwp ?_
  refine ldw0 (w := w) (k := vSel) (by rsimp) hvs ?_
  refine wp_reg rfl ?_
  refine stw0 (w := w) (k := vSel) (by rsimp) (by rsimp; rw [hvs]; rfl) ?_
  refine ldw0 (w := w) (k := vRem) (by rsimp) (by mem_simp; exact hvr) ?_
  refine wp_reg rfl ?_
  refine stw0 (w := w) (k := vRem) (by rsimp) (by mem_simp; rw [hvr]; rfl) ?_
  refine wp_done ⟨?_, ?_, ?_, by keep_tac, by rsimp; exact hrdi⟩
  · mem_simp; rw [wd_add16]
  · mem_simp; rw [sub_one_toUInt64 hrem]
  · rsimp; rw [sub_one_toUInt64 hrem]

/-- **The owner's form**: `G := G.addScaled F sel`, `G` at the word `vG` holds, the selector at
the word `vSel` holds; the next selector, one block fewer (left in `rax`). -/
theorem accCode_spec {go sp rem : Nat} {g F : FormW} {sel : EW}
    (hrdi : s.reg .rdi = ctx) (hwp : s.mem (wd ctx ctxWork) = some w)
    (hcw : ∀ k < dataEnd, wd ctx ctxWork ≠ wd w k)
    (hvg : s.mem (wd w vG) = some (wd w go)) (hvs : s.mem (wd w vSel) = some (wd w sp))
    (hvr : s.mem (wd w vRem) = some rem.toUInt64) (hrem : 0 < rem)
    (hG : FZ s.mem w go formCap g) (hF : FZ s.mem w fOff fCap F) (hs : EAtI s.mem w sp sel)
    (hroom : ((shape F).foldl addMono (shape g)).length ≤ formCap)
    (hdom : ∀ k < 1 + 5 * formCap, (s.mem (wd w (go + k))).isSome)
    (hgo : go + 1 + 5 * formCap ≤ fOff) (hsp : sp + 2 ≤ go ∨ go + 1 + 5 * formCap ≤ sp)
    (hsp' : sp + 2 ≤ fOff) :
    WP accCode s (fun s' ↦ s'.reg .rdi = ctx ∧ FZ s'.mem w go formCap (g.addScaled F sel) ∧
      s'.mem (wd w vSel) = some (wd w (sp + 2)) ∧ s'.mem (wd w vRem) = some (rem - 1).toUInt64 ∧
      s'.reg .rax = (rem - 1).toUInt64 ∧
      KeepS w (fun k ↦ (go ≤ k ∧ k < go + 1 + 5 * formCap) ∨ k = vSel ∨ k = vRem) s.mem s'.mem) E := by
  have v1 := fOff_val
  have v2 := vSel_val
  have v3 := vRem_val
  have v4 := dataEnd_eq
  unfold accCode
  refine wp_then' (accPre_spec (E := E) hrdi hwp hvg hvs hF) fun s1 ⟨a13, abp, a14, a15, am, ar⟩ _ ↦ ?_
  refine wp_then' (acLoop_spec (E := E) (w := w) (go := go) (sp := sp) (sel := sel) a13 a14 a15 abp (by rw [am]; exact hG)
    (by rw [am]; exact hF) (by rw [am]; exact hs) hroom (fun k hk ↦ by rw [am]; exact hdom k hk)
    hgo hsp (by omega)) fun s2 ⟨bG, bK, bR⟩ _ ↦ ?_
  have kw : ∀ k, k < 2 ^ 61 → (k < go ∨ go + 1 + 5 * formCap ≤ k) → s2.mem (wd w k) = s.mem (wd w k) :=
    fun k hk hk' ↦ by rw [← am]; exact bK.word (by omega) fun i hi ↦ ⟨by omega, by omega⟩
  have r2 : s2.reg .rdi = ctx := (bR .rdi (by decide)).trans ar
  have c2 : s2.mem (wd ctx ctxWork) = some w := by
    rw [bK _ fun k hk ↦ hcw k (by unfold formCap at hk; omega), am]; exact hwp
  refine WP.mono (accPost_spec (E := E) (sp := sp) (rem := rem) r2 c2
    (by rw [kw _ (by omega) (by unfold formCap at *; omega)]; exact hvs)
    (by rw [kw _ (by omega) (by unfold formCap at *; omega)]; exact hvr) hrem)
    (fun s3 ⟨c1, c2', c3, cK, cr⟩ ↦ ⟨cr, ?_, c1, c2', c3, ?_⟩) (fun _ h ↦ h)
  · refine bG.congr fun k hk ↦ cK.word (by unfold formCap at *; omega) fun i hi ↦
      ⟨by unfold formCap at *; omega, by unfold formCap at *; omega⟩
  · rw [am] at bK
    exact bK.trans cK (fun k h ↦ .inl h) (fun k h ↦ .inr h)

end NativeVm.Code.P3
