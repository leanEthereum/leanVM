module

public import NativeVm.Code.Phase3.LayoutBase

/-!
# Phase 3's placements: the sizes and the rows

`fillT_spec`: table `t`'s `c` blocks, from block `k0`: its height at words `po + fo + 2 (k0 + j)`,
its rows at `po + 128 + k0 + j`. `fillC_spec`: every table's blocks in turn. `frameC_spec`: the
framework sizes. Each changes only the words it names (`Only`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

/-- `m'` is `m` but at the words `w` of the area at `p` with `A w`. -/
def Only (A : Nat → Prop) (p : UInt64) (m m' : UInt64 → Option UInt64) : Prop :=
  ∀ a, (∀ w, A w → a ≠ wd p w) → m' a = m a

theorem Only.refl (A : Nat → Prop) (p : UInt64) (m : UInt64 → Option UInt64) : Only A p m m :=
  fun _ _ ↦ rfl

theorem Only.trans {A B C : Nat → Prop} {p : UInt64} {m₁ m₂ m₃ : UInt64 → Option UInt64}
    (h₁ : Only A p m₁ m₂) (h₂ : Only B p m₂ m₃) (hA : ∀ w, A w → C w) (hB : ∀ w, B w → C w) :
    Only C p m₁ m₃ :=
  fun a ha ↦ (h₂ a fun w hw ↦ ha w (hB w hw)).trans (h₁ a fun w hw ↦ ha w (hA w hw))

theorem Only.mono {A C : Nat → Prop} {p : UInt64} {m m' : UInt64 → Option UInt64}
    (h : Only A p m m') (hA : ∀ w, A w → C w) : Only C p m m' :=
  fun a ha ↦ h a fun w hw ↦ ha w (hA w hw)

theorem Only.setMem {A : Nat → Prop} {p : UInt64} {m : UInt64 → Option UInt64} {s : QState}
    (h : Only A p m s.mem) {w : Nat} (hw : A w) (v : UInt64) : Only A p m (s.setMem (wd p w) v).mem :=
  fun a ha ↦ by
    rw [QState.setMem_mem, ite_eq_right_of_eq_false _ _ (eq_false (ha w hw))]
    exact h a ha

/-- The word `b` outside `A` is kept. -/
theorem Only.setReg {A : Nat → Prop} {p : UInt64} {m : UInt64 → Option UInt64} {s : QState}
    (h : Only A p m s.mem) (r : Reg64) (v : UInt64) : Only A p m (s.setReg r v).mem := h

theorem Only.word {A : Nat → Prop} {p : UInt64} {m m' : UInt64 → Option UInt64} (h : Only A p m m')
    {b : Nat} (hb : b < 2 ^ 61) (hA : ∀ w, A w → w < 2 ^ 61 ∧ w ≠ b) : m' (wd p b) = m (wd p b) :=
  h _ fun w hw e ↦ (hA w hw).2 ((wd_inj hb (hA w hw).1).mp e).symm

variable {s : QState} {E : QState → Prop}

/-! ## A table's blocks -/

/-- The words `fillT` writes, block `j` of `c`. -/
def fillW (po fo k0 c w : Nat) : Prop := ∃ j < c, w = po + fo + 2 * (k0 + j) ∨ w = po + 128 + (k0 + j)

theorem fillT_spec {p : UInt64} {po fo t c k0 hv rv : Nat} (hpo : po + 256 < 2 ^ 61)
    (hfo : fo + 2 * (k0 + c) ≤ 128) (h15 : s.reg .r15 = p) (h14 : s.reg .r14 = (2 * k0).toUInt64)
    (hh : s.mem (wd p (layoutR.off + 4 + t)) = some hv.toUInt64)
    (hr : s.mem (wd p (layoutR.off + 10 + t)) = some rv.toUInt64)
    (hdom : ∀ w < 256, (s.mem (wd p (po + w))).isSome) :
    WP (fillT po fo t c) s (fun s' ↦ s'.reg .r15 = p ∧ s'.reg .r14 = (2 * (k0 + c)).toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .r14] s s' ∧
      (∀ j < c, s'.mem (wd p (po + fo + 2 * (k0 + j))) = some hv.toUInt64 ∧
        s'.mem (wd p (po + 128 + (k0 + j))) = some rv.toUInt64) ∧
      Only (fillW po fo k0 c) p s.mem s'.mem ∧ ∀ a, (s'.mem a).isSome = (s.mem a).isSome) E := by
  unfold fillT
  refine wp_load (eval_aW h15 _) hh ?_
  refine wp_load (eval_aW (by rsimp; exact h15) _) hr ?_
  fstep [ofNat_toUInt64]
  apply WP.blk_cons
  apply WP.loop (fun u ↦ ∃ j ≤ c, u.reg .rcx = (c - j).toUInt64 ∧
      u.reg .r14 = (2 * (k0 + j)).toUInt64 ∧ u.reg .r15 = p ∧ u.reg .rax = hv.toUInt64 ∧
      u.reg .rbx = rv.toUInt64 ∧ RegsFrame [.rax, .rbx, .rcx, .r14] s u ∧
      (∀ j' < j, u.mem (wd p (po + fo + 2 * (k0 + j'))) = some hv.toUInt64 ∧
        u.mem (wd p (po + 128 + (k0 + j'))) = some rv.toUInt64) ∧
      Only (fillW po fo k0 j) p s.mem u.mem ∧ ∀ a, (u.mem a).isSome = (s.mem a).isSome)
    (fun u ↦ (u.reg .rcx).toNat)
  · refine ⟨0, by omega, by rsimp; rw [Nat.sub_zero], by rsimp; rw [h14, Nat.add_zero], by rsimp; exact h15, by rsimp, by rsimp,
      by rf_tac, fun j hj ↦ absurd hj (by omega), fun _ _ ↦ rfl, fun _ ↦ rfl⟩
  · rintro u ⟨j, hj, hcx, h14', h15', hax, hbx, hf, hw, ho, hd⟩ hc
    rw [cmp_ne_zero (a := c - j) (by omega) hcx] at hc
    have hjc : j < c := by simp at hc; omega
    have e1 : po + fo + 2 * (k0 + j) < po + 256 := by omega
    have e2 : po + 128 + (k0 + j) < po + 256 := by omega
    have hA : (u.mem (wd p (po + fo + 2 * (k0 + j)))).isSome := by
      rw [hd]; have := hdom (fo + 2 * (k0 + j)) (by omega); rwa [← Nat.add_assoc] at this
    have hB : (u.mem (wd p (po + 128 + (k0 + j)))).isSome := by
      rw [hd]; have := hdom (128 + (k0 + j)) (by omega); rwa [← Nat.add_assoc] at this
    have a1 := eval_aI (s := u) (k := po + fo) h15' h14'
    rw [show 2 * (k0 + j) + (po + fo) = po + fo + 2 * (k0 + j) by omega] at a1
    refine wp_store a1 hA ?_
    have a2 := eval_aH (s := u.setMem (wd p (po + fo + 2 * (k0 + j))) (u.reg .rax)) (k := po + 128)
      (by rsimp; exact h15') (by rsimp; exact h14')
    rw [show k0 + j + (po + 128) = po + 128 + (k0 + j) by omega] at a2
    refine wp_store a2 (by rw [dom_setMem hA]; exact hB) ?_
    fstep; fstep; fdone
    refine ⟨⟨j + 1, by omega, ?_, ?_, h15', hax, hbx, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hcx, toUInt64_sub_one (by omega) (by omega), Nat.sub_sub]
    · rw [h14', toUInt64_add_two]; congr 1
    · rf_tac; exact hf
    · intro j' hj'
      by_cases e : j' = j
      · subst e
        simp (disch := omega) only [setMem_wd_ne, setMem_wd_eq]
        rw [hax, hbx]
        exact ⟨rfl, rfl⟩
      · have hlt : j' < j := by omega
        simp (disch := omega) only [setMem_wd_ne]
        exact hw j' hlt
    · exact ((ho.mono fun w ⟨j', hj', h'⟩ ↦ ⟨j', by omega, h'⟩).setMem ⟨j, by omega, .inl rfl⟩
        _).setMem ⟨j, by omega, .inr rfl⟩ _
    · intro a
      rw [dom_setMem (by rw [dom_setMem hA]; exact hB), dom_setMem hA, hd]
    · rw [hcx, toUInt64_sub_one (show 1 ≤ c - j by omega) (by omega),
        toNat_toUInt64 (show c - j < 2 ^ 64 by omega), toNat_toUInt64 (show c - j - 1 < 2 ^ 64 by omega)]
      omega
  · rintro u ⟨j, hj, hcx, h14', h15', -, -, hf, hw, ho, hd⟩ hc
    rw [cmp_ne_zero (a := c - j) (by omega) hcx] at hc
    have hjc : j = c := by simp at hc; omega
    subst hjc
    exact WP.blk_nil ⟨h15', h14', hf, hw, ho, hd⟩

/-! ## Every table's blocks -/

/-- The owners of the blocks of a shape. -/
def ownersOf (L : List (Nat × Nat)) : List Nat := L.flatMap fun x ↦ List.replicate x.2 x.1

theorem ownersOf_cons (x : Nat × Nat) (L : List (Nat × Nat)) :
    ownersOf (x :: L) = List.replicate x.2 x.1 ++ ownersOf L := by
  simp [ownersOf]

theorem ownersOf_getD_cons {x : Nat × Nat} {L : List (Nat × Nat)} {j : Nat} :
    (ownersOf (x :: L)).getD j 0 = if j < x.2 then x.1 else (ownersOf L).getD (j - x.2) 0 := by
  rw [ownersOf_cons]
  split
  · rw [List.getD_append _ _ _ _ (by simpa using ‹j < x.2›)]
    simp [List.getD_eq_getElem?_getD, ‹j < x.2›]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_replicate]

theorem fillL_spec {p : UInt64} {po fo : Nat} {H R : Nat → Nat} (L : List (Nat × Nat))
    {k0 : Nat} (hpo : po + 256 < 2 ^ 61) (hpl : layoutR.off + 16 ≤ po)
    (hfo : fo + 2 * (k0 + (ownersOf L).length) ≤ 128) (hL : ∀ x ∈ L, x.1 < 6)
    (h15 : s.reg .r15 = p) (h14 : s.reg .r14 = (2 * k0).toUInt64)
    (hh : ∀ t < 6, s.mem (wd p (layoutR.off + 4 + t)) = some (H t).toUInt64)
    (hr : ∀ t < 6, s.mem (wd p (layoutR.off + 10 + t)) = some (R t).toUInt64)
    (hdom : ∀ w < 256, (s.mem (wd p (po + w))).isSome) :
    WP (blk (L.map fun x ↦ fillT po fo x.1 x.2)) s (fun s' ↦ s'.reg .r15 = p ∧
      RegsFrame [.rax, .rbx, .rcx, .r14] s s' ∧
      (∀ j < (ownersOf L).length,
        s'.mem (wd p (po + fo + 2 * (k0 + j))) = some (H ((ownersOf L).getD j 0)).toUInt64 ∧
        s'.mem (wd p (po + 128 + (k0 + j))) = some (R ((ownersOf L).getD j 0)).toUInt64) ∧
      Only (fillW po fo k0 (ownersOf L).length) p s.mem s'.mem ∧
      ∀ a, (s'.mem a).isSome = (s.mem a).isSome) E := by
  induction L generalizing s k0 with
  | nil =>
    exact WP.blk_nil ⟨h15, rf_refl _ _, fun j hj ↦ absurd hj (by simp [ownersOf]),
      fun _ _ ↦ rfl, fun _ ↦ rfl⟩
  | cons x L ih =>
    have hlen : (ownersOf (x :: L)).length = x.2 + (ownersOf L).length := by
      rw [ownersOf_cons, List.length_append, List.length_replicate]
    have hx := hL x (by simp)
    refine WP.blk_cons (WP.mono (WP.frame (fillT_spec (po := po) (fo := fo) (c := x.2) (k0 := k0) (t := x.1)
      (hv := H x.1) (rv := R x.1) hpo (by omega) h15 h14 (hh _ hx) (hr _ hx) hdom))
      (fun s₁ ⟨⟨a15, a14, af, aw, ao, ad⟩, _, _⟩ ↦ ?_) fun _ h ↦ h.1)
    have keepL : ∀ k < 16, s₁.mem (wd p (layoutR.off + k)) = s.mem (wd p (layoutR.off + k)) :=
      fun k hk ↦ ao.word (by unfold layoutR at *; simp only [Transcript.workWords_val] at *; omega)
        fun w ⟨j, hj, hw⟩ ↦ by unfold layoutR at *; omega
    have hh' : ∀ t < 6, s₁.mem (wd p (layoutR.off + 4 + t)) = some (H t).toUInt64 := fun t ht ↦ by
      have := keepL (4 + t) (by omega)
      rw [← Nat.add_assoc] at this
      rw [this]; exact hh t ht
    have hr' : ∀ t < 6, s₁.mem (wd p (layoutR.off + 10 + t)) = some (R t).toUInt64 := fun t ht ↦ by
      have := keepL (10 + t) (by omega)
      rw [← Nat.add_assoc] at this
      rw [this]; exact hr t ht
    refine WP.mono (ih (k0 := k0 + x.2) (by omega) (fun y hy ↦ hL y (by simp [hy])) a15 a14 hh' hr'
      (fun w hw ↦ by rw [ad]; exact hdom w hw)) (fun s₂ ⟨b15, bf, bw, bo, bd⟩ ↦ ?_) fun _ h ↦ h
    refine ⟨b15, ?_, fun j hj ↦ ?_, ?_, fun a ↦ (bd a).trans (ad a)⟩
    · intro r hr'; rw [bf r hr', af r hr']
    · rw [ownersOf_getD_cons]
      split
      · rw [bo.word (by omega) fun w ⟨j', hj', hw⟩ ↦ ⟨by omega, by omega⟩,
          bo.word (by omega) fun w ⟨j', hj', hw⟩ ↦ ⟨by omega, by omega⟩]
        exact aw j ‹_›
      · have := bw (j - x.2) (by omega)
        rwa [show k0 + x.2 + (j - x.2) = k0 + j by omega] at this
    · exact ao.trans bo (fun w ⟨j, hj, hw⟩ ↦ ⟨j, by omega, hw⟩)
        fun w ⟨j, hj, hw⟩ ↦ ⟨x.2 + j, by omega, by omega⟩

theorem fillC_spec {p : UInt64} {po fo : Nat} {H R : Nat → Nat} (L : List (Nat × Nat))
    (hpo : po + 256 < 2 ^ 61) (hpl : layoutR.off + 16 ≤ po)
    (hfo : fo + 2 * (ownersOf L).length ≤ 128) (hL : ∀ x ∈ L, x.1 < 6) (h15 : s.reg .r15 = p)
    (hh : ∀ t < 6, s.mem (wd p (layoutR.off + 4 + t)) = some (H t).toUInt64)
    (hr : ∀ t < 6, s.mem (wd p (layoutR.off + 10 + t)) = some (R t).toUInt64)
    (hdom : ∀ w < 256, (s.mem (wd p (po + w))).isSome) :
    WP (fillC po fo L) s (fun s' ↦ s'.reg .r15 = p ∧
      RegsFrame [.rax, .rbx, .rcx, .r14] s s' ∧
      (∀ j < (ownersOf L).length,
        s'.mem (wd p (po + fo + 2 * j)) = some (H ((ownersOf L).getD j 0)).toUInt64 ∧
        s'.mem (wd p (po + 128 + j)) = some (R ((ownersOf L).getD j 0)).toUInt64) ∧
      Only (fillW po fo 0 (ownersOf L).length) p s.mem s'.mem ∧
      ∀ a, (s'.mem a).isSome = (s.mem a).isSome) E := by
  unfold fillC
  fstep
  refine WP.mono (fillL_spec (k0 := 0) L hpo hpl (by omega) hL (by rsimp; exact h15) (by rsimp; rfl)
    hh hr hdom) (fun s' ⟨a, b, c, d, e⟩ ↦ ⟨a, fun r hr ↦ ?_, fun j hj ↦ ?_, d, e⟩) fun _ h ↦ h
  · rw [b r hr]; rsimp; simp only [List.mem_cons, not_or] at hr; simp [hr.2.2.2.1]
  · have := c j hj; rwa [Nat.zero_add] at this

/-! ## The framework sizes -/

theorem frameC_spec {p : UInt64} {po lm lb : Nat} (hpo : po + 256 < 2 ^ 61)
    (hpl : layoutR.off + 16 ≤ po) (h15 : s.reg .r15 = p)
    (hm : s.mem (wd p layoutR.off) = some lm.toUInt64)
    (hb : s.mem (wd p (layoutR.off + 1)) = some lb.toUInt64)
    (hdom : ∀ w < 256, (s.mem (wd p (po + w))).isSome) :
    WP (frameC po) s (fun s' ↦ s'.reg .r15 = p ∧ RegsFrame [.rax] s s' ∧
      s'.mem (wd p po) = some (0 : Nat).toUInt64 ∧ s'.mem (wd p (po + 2)) = some lm.toUInt64 ∧
      s'.mem (wd p (po + 4)) = some lb.toUInt64 ∧
      Only (fun w ↦ w = po ∨ w = po + 2 ∨ w = po + 4) p s.mem s'.mem ∧
      ∀ a, (s'.mem a).isSome = (s.mem a).isSome) E := by
  have hl : layoutR.off < 2 ^ 61 := by unfold layoutR at *; omega
  have d0 : (s.mem (wd p po)).isSome := by have := hdom 0 (by omega); rwa [Nat.add_zero] at this
  have d2 := hdom 2 (by omega)
  have d4 := hdom 4 (by omega)
  unfold frameC
  refine wp_storei (eval_aW h15 _) d0 ?_
  refine wp_load (eval_aW (by rsimp; exact h15) _)
    (by rw [QState.setMem_mem, ite_eq_right_of_eq_false _ _ (eq_false fun e ↦ by
      rw [wd_inj (by omega) (by omega)] at e; omega)]; exact hm) ?_
  have d2' : ∀ v w : UInt64, (((s.setMem (wd p po) v).setReg .rax w).mem (wd p (po + 2))).isSome := by
    intro v w; rw [QState.setReg_mem, dom_setMem d0]; exact d2
  refine wp_store (eval_aW (by rsimp; exact h15) _) (d2' _ _) ?_
  refine wp_load (eval_aW (by rsimp; exact h15) _) (by p3wsimp; exact hb) ?_
  refine wp_store (eval_aW (by rsimp; exact h15) _)
    (by rw [QState.setReg_mem, dom_setMem (d2' _ _), QState.setReg_mem, dom_setMem d0]; exact d4) ?_
  refine WP.blk_nil ⟨by rsimp; exact h15, rf_of fun r hr ↦ ?_, by p3wsimp; rfl, by p3wsimp, by p3wsimp,
    ?_, fun a ↦ ?_⟩
  · have : r ≠ .rax := by simpa using hr
    p3wsimp
    simp [this]
  · intro a ha
    simp only [QState.setReg_mem, QState.setMem_mem, ha po (.inl rfl), ha (po + 2) (.inr (.inl rfl)),
      ha (po + 4) (.inr (.inr rfl)), ↓reduceIte]
  · simp only [QState.setReg_mem, QState.setMem_mem]
    split_ifs with e1 e2 e3 <;> first | rfl | (subst a; rw [Option.isSome_some]; first | exact d0.symm | exact d2.symm | exact d4.symm)

end NativeVm.Code.P3
