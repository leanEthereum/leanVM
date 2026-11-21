module

public import NativeVm.Code.Phase3.FormsTerm
public import NativeVm.Code.Phase3.FormsCheck

/-!
# The bus forms of a side: a block's form

`entLoop_spec`: the entries' loop adds entry `j`'s term (the slot weight times the coefficient,
`escale`, then `atCode`) to the block form, so after the loop it is `buildF`. `buildCode_spec`: the
owner's form's address to `vG`, `F := const β`, the loop, the next block's data to `vCur`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

variable {w ctx : UInt64} {s : QState} {E : QState → Prop}

/-- The registers the entries' loop writes. -/
abbrev entRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r12]

/-- The block form after `j` entries. -/
def bf (es : List DEnt) (ws : Array EW) (β : EW) (j : Nat) : FormW :=
  (es.take j).foldl (entStep ws) (FormW.const β)

theorem bf_size_le (es : List DEnt) (ws : Array EW) (β : EW) (j : Nat) :
    (bf es ws β j).size ≤ 1 + j := by
  have h := congrArg List.length (shape_foldl_entStep (es.take j) ws (FormW.const β))
  simp only [shape, List.length_map, Array.length_toList] at h
  rw [bf, h]
  refine (length_foldl_addMono _ _).trans ?_
  simp [FormW.const]

theorem bf_succ {es : List DEnt} {j : Nat} (hj : j < es.length) (ws : Array EW) (β : EW) :
    bf es ws β (j + 1) = entStep ws (bf es ws β j) es[j] := by
  rw [bf, bf, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
  rfl

theorem bf_all (es : List DEnt) (ws : Array EW) (β : EW) : bf es ws β es.length = buildF es ws β := by
  rw [bf, List.take_length]; rfl

theorem blkOk_spec {side : Nat} {b : DBlk} (h : blkOk side b = true) :
    b.1 < 6 ∧ b.2.length ≤ 31 ∧ ∀ e ∈ b.2, e.1 < slotN side ∧ e.2.1.length ≤ 2 ∧
      (∀ a ∈ e.2.1, a < 92 ∧ (b.1 ≠ 5 → a < 40)) ∧ e.2.2 < 2 ^ 31 := by
  simp only [blkOk, entOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun e he ↦ ?_⟩
  obtain ⟨⟨⟨a, b'⟩, c⟩, d⟩ := h3 e he
  refine ⟨a, b', fun x hx ↦ ⟨(c x hx).1, fun ho ↦ ?_⟩, d⟩
  rcases (c x hx).2 with h | h
  · exact absurd h ho
  · exact h

theorem slotN_le (side : Nat) : slotN side ≤ 16 := by unfold slotN; split <;> omega

/-- **The entries' loop**: from `const β`, entry `j` at word `q + 5 j` and the slot weights from
`wOff`, the block form becomes `buildF es ws β`. -/
theorem entLoop_spec {q wOff : Nat} {es : List DEnt} {ws : Array EW} {β : EW}
    (h12 : s.reg .r12 = wd w q) (h14 : s.reg .r14 = wd w (q + 5 * es.length))
    (h13 : s.reg .r13 = wd w fOff) (h15 : s.reg .r15 = wd w wOff)
    (hf : FZ s.mem w fOff fCap (FormW.const β))
    (hent : ∀ j (h : j < es.length), EntAt s.mem w (q + 5 * j) es[j])
    (hws : ∀ e ∈ es, EAtI s.mem w (wOff + 2 * e.1) (ws.getD e.1 0))
    (hb : ∀ e ∈ es, e.1 < 16 ∧ e.2.1.length ≤ 2 ∧ ∀ a ∈ e.2.1, a < 2 ^ 64)
    (hn : es.length ≤ 31) (hdom : ∀ k, SF k → (s.mem (wd w k)).isSome)
    (hq : vG < q) (hq' : q + 5 * es.length ≤ dataEnd)
    (hwo : wOff + 32 ≤ fOff ∨ fOff + 1 + 5 * fCap ≤ wOff) (hwo' : wOff + 32 ≤ dataEnd) :
    WP entLoop s (fun s' ↦ FZ s'.mem w fOff fCap (buildF es ws β) ∧
      s'.reg .r12 = wd w (q + 5 * es.length) ∧ KeepS w SF s.mem s'.mem ∧
      RegsFrame entRegs s s') E := by
  unfold entLoop
  refine WP.loop (fun t ↦ ∃ j ≤ es.length, t.reg .r12 = wd w (q + 5 * j) ∧
      t.reg .r14 = wd w (q + 5 * es.length) ∧ RegsFrame entRegs s t ∧
      FZ t.mem w fOff fCap (bf es ws β j) ∧ KeepS w SF s.mem t.mem ∧
      ∀ k, SF k → (t.mem (wd w k)).isSome)
    (fun t ↦ (t.reg .r14 - t.reg .r12).toNat)
    ⟨0, by omega, by rw [h12]; rfl, h14, fun _ _ ↦ rfl, hf, KeepS.refl _ _, hdom⟩ ?_ ?_
  · rintro t ⟨j, hj, h12', h14', hR, hfz, hkp, hdt⟩ hc
    have hjn : j < es.length := by
      rw [cond_ne, h12', rhs_reg, h14'] at hc
      by_contra hn'
      have : j = es.length := by omega
      subst this
      simp at hc
    have hkw : ∀ k, k < dataEnd → ¬ SF k → t.mem (wd w k) = s.mem (wd w k) := fun k hk' hk ↦
      hkp.word (k := k) (by oo) fun i hi ↦ ⟨by oo, fun e ↦ hk (e ▸ hi)⟩
    have he := hb _ (List.getElem_mem hjn)
    obtain ⟨e0, e1, e2, e3, e4⟩ := hent j hjn
    obtain ⟨hw0, hw1⟩ := hws _ (List.getElem_mem hjn)
    rw [← hkw (q + 5 * j) (by oo) (by oo)] at e0
    rw [← hkw (q + 5 * j + 1) (by oo) (by oo)] at e1
    rw [← hkw (q + 5 * j + 2) (by oo) (by oo)] at e2
    rw [← hkw (q + 5 * j + 3) (by oo) (by oo)] at e3
    rw [← hkw (q + 5 * j + 4) (by oo) (by oo)] at e4
    rw [← hkw (wOff + 2 * es[j].1) (by oo) (by oo)] at hw0
    rw [← hkw (wOff + 2 * es[j].1 + 1) (by oo) (by oo)] at hw1
    have h13' : t.reg .r13 = wd w fOff := (hR .r13 (by decide)).trans h13
    have h15' : t.reg .r15 = wd w wOff := (hR .r15 (by decide)).trans h15
    refine ldw (k := 3) h12' e3 ?_
    refine wp_reg rfl ?_
    have hrax : ((t.setReg .rax es[j].1.toUInt64).setReg .rax
        ((t.setReg .rax es[j].1.toUInt64).reg .rax <<< (1 : Nat).toUInt64)).reg .rax =
        (2 * es[j].1).toUInt64 := by
      rsimp; rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, toUInt64_shl _ 1 (by omega),
        Nat.pow_one]
    refine ldx (i := 2 * es[j].1) (k := 0) (by rsimp; exact h15') hrax
      (by rw [Nat.add_zero]; exact hw0) ?_
    refine ldx (i := 2 * es[j].1) (k := 1) (by rsimp; exact h15') (by rsimp; exact hrax)
      (by exact hw1) ?_
    refine ldw (k := 4) (by rsimp; exact h12') e4 ?_
    refine WP.then (escale_spec _) fun t1 ⟨he1, hm1, hf1⟩ ↦ ?_
    rsimp at he1
    have hscale : t1.reg .r9 = (ws.getD es[j].1 0 * kE es[j].2.2.toUInt64).c0 ∧
        t1.reg .r10 = (ws.getD es[j].1 0 * kE es[j].2.2.toUInt64).c1 := by
      rw [← eOf_eq_toE, he1, NativeVm.Equiv.EW.toE_mul, show kE es[j].2.2.toUInt64 =
        EW.ofK es[j].2.2.toUInt64 from rfl, NativeVm.Equiv.EW.toE_ofK]
      rfl
    have g : ∀ r ∉ sqRegs, r ≠ .r11 → t1.reg r = t.reg r := fun r hr h11 ↦ by
      rw [hf1 r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2, h11]
    refine wp_then' (atCode_spec (E := E) (w := w) (po := fOff) (qo := q + 5 * j) (cap := fCap)
      (f := bf es ws β j) (m := es[j].2.1.toArray) (c := ws.getD es[j].1 0 * kE es[j].2.2.toUInt64)
      (by rw [g .r13 (by decide) (by decide)]; exact h13')
      (by rw [g .r12 (by decide) (by decide)]; exact h12') hscale.1 hscale.2
      (by rw [hm1]; exact hfz)
      (by rw [hm1]; exact (EntAt.key ⟨e0, e1, e2, e3, e4⟩ he.2.1 he.2.2))
      (.inr (by have := bf_size_le es ws β j; unfold fCap; omega))
      (fun k hk ↦ by rw [hm1]; exact hdt _ (by oo))
      (.inr (by oo)) (by oo) (by oo)) fun t2 ⟨hf2, hk2, hr2⟩ hd2 ↦ ?_
    have h12t : t2.reg .r12 = wd w (q + 5 * j) := by
      rw [hr2 .r12 (by decide), g .r12 (by decide) (by decide)]; exact h12'
    refine wp_reg rfl (wp_done ⟨⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    · rsimp; rw [h12t, wd_add40, show q + 5 * j + 5 = q + 5 * (j + 1) by omega]
    · rsimp
      rw [hr2 .r14 (by decide), g .r14 (by decide) (by decide)]; exact h14'
    · refine rf_setReg ?_ (by simp) _
      refine rf_trans (l' := atRegs) (hl := List.Subset.refl _) ?_ hr2
      refine rf_trans (l' := sqRegs) (hl := List.Subset.refl _) ?_ hf1
      rfx
      exact hR
    · rsimp
      rw [bf_succ hjn]
      exact hf2
    · refine (hkp.trans (show KeepS w SF t.mem t1.mem by rw [hm1]; exact KeepS.refl _ _)
        (fun k h ↦ h) (fun k h ↦ h)).trans hk2 (fun k h ↦ h) (fun k h ↦ h)
    · intro k hk
      rsimp
      rw [hd2, hm1]
      exact hdt k hk
    · rsimp
      rw [hr2 .r14 (by decide), g .r14 (by decide) (by decide), h14', h12t, wd_add40, h12',
        wd_sub_toNat (by omega) (by oo), wd_sub_toNat (by omega) (by oo)]
      omega
  · rintro t ⟨j, hj, h12', h14', hR, hfz, hkp, -⟩ hc
    have hjn : j = es.length := by
      rw [cond_ne, h12', rhs_reg, h14'] at hc
      simp only [bne_eq_false_iff_eq] at hc
      exact (by have := (wd_inj (b := w) (by oo) (by oo)).mp hc; omega)
    subst hjn
    exact ⟨by rw [← bf_all]; exact hfz, h12', hkp, hR⟩

theorem EntAt.congr {mem mem' : UInt64 → Option UInt64} {q : Nat} {e : DEnt}
    (h : ∀ k < 5, mem' (wd w (q + k)) = mem (wd w (q + k))) (he : EntAt mem w q e) :
    EntAt mem' w q e :=
  ⟨by rw [← Nat.add_zero q, h 0 (by omega)]; exact he.1, by rw [h 1 (by omega)]; exact he.2.1,
    by rw [h 2 (by omega)]; exact he.2.2.1, by rw [h 3 (by omega)]; exact he.2.2.2.1,
    by rw [h 4 (by omega)]; exact he.2.2.2.2⟩

/-- **The block form's start.** -/
theorem buildPre_spec {side wOff bOff q : Nat} {b : DBlk} {β : EW}
    (hrdi : s.reg .rdi = ctx) (hwp : s.mem (wd ctx ctxWork) = some w)
    (hcur : s.mem (wd w vCur) = some (wd w q)) (hblk : BlkAt s.mem w q side b)
    (hβ : EAtI s.mem w bOff β) (hdom : ∀ k, fOff ≤ k → k ≤ vG → (s.mem (wd w k)).isSome)
    (hq : vG < q) (hq' : q + 2 + 5 * b.2.length ≤ dataEnd)
    (hbo : bOff + 2 ≤ fOff ∨ vG < bOff) (hbo' : bOff + 2 ≤ dataEnd) :
    WP (buildPre wOff bOff) s (fun s' ↦ s'.reg .rdi = ctx ∧ s'.reg .r12 = wd w (q + 2) ∧
      s'.reg .r14 = wd w (q + 2 + 5 * b.2.length) ∧ s'.reg .r13 = wd w fOff ∧
      s'.reg .r15 = wd w wOff ∧ FZ s'.mem w fOff fCap (FormW.const β) ∧
      s'.mem (wd w vG) = some (wd w (busR.off + formOff b.1 side)) ∧
      KeepS w (fun k ↦ (fOff ≤ k ∧ k < fOff + 6) ∨ k = vG) s.mem s'.mem) E := by
  have v1 := fOff_val
  have v2 := vG_val
  have v3 := vCur_val
  have v4 := dataEnd_eq
  obtain ⟨hg, hn, -⟩ := hblk
  have hnb : b.2.length < 2 ^ 50 := by omega
  unfold buildPre
  refine wk_wp hrdi hwp ?_
  refine ldw0 (w := w) (k := vCur) (by rsimp) hcur ?_
  refine ldw (w := w) (j := q) (k := 0) (by rsimp) (by rw [Nat.add_zero]; exact hg) ?_
  refine wp_reg rfl ?_
  refine wp_reg rfl ?_
  refine stw0 (w := w) (k := vG) (by rsimp) (hdom _ (by omega) le_rfl) ?_
  refine stiw0 (w := w) (k := fOff) (by rsimp) (by mem_simp; exact hdom _ le_rfl (by omega)) ?_
  refine stiw0 (w := w) (k := fOff + 1) (by rsimp) (by mem_simp; exact hdom _ (by omega) (by omega)) ?_
  refine stiw0 (w := w) (k := fOff + 2) (by rsimp) (by mem_simp; exact hdom _ (by omega) (by omega)) ?_
  refine stiw0 (w := w) (k := fOff + 3) (by rsimp) (by mem_simp; exact hdom _ (by omega) (by omega)) ?_
  refine ldw0 (w := w) (k := bOff) (by rsimp) (by mem_simp; exact hβ.1) ?_
  refine stw0 (w := w) (k := fOff + 4) (by rsimp) (by mem_simp; exact hdom _ (by omega) (by omega)) ?_
  refine ldw0 (w := w) (k := bOff + 1) (by rsimp) (by mem_simp; exact hβ.2) ?_
  refine stw0 (w := w) (k := fOff + 5) (by rsimp) (by mem_simp; exact hdom _ (by omega) (by omega)) ?_
  refine ldw (w := w) (j := q) (k := 1) (by rsimp) (by mem_simp; exact hn) ?_
  refine wp_reg rfl ?_
  refine wp_reg rfl ?_
  refine wp_reg rfl ?_
  refine wp_reg rfl ?_
  refine wp_reg rfl ?_
  refine wp_reg rfl ?_
  refine lea0 (w := w) (k := fOff) (by rsimp) ?_
  refine lea0 (w := w) (k := wOff) (by rsimp) ?_
  refine wp_done ⟨by rsimp; exact hrdi, by rsimp; rw [wd_add16], ?_, by rsimp, by rsimp, ?_, ?_, ?_⟩
  · rsimp
    rw [wd_add16, times40 _, add_comm, wd_eq_add]
  · refine ⟨by simp [FormW.const, fCap], by mem_simp; rfl, fun i hi ↦ ?_⟩
    have : i = 0 := by simpa [FormW.const] using hi
    subst this
    refine ⟨⟨by simp [FormW.const], by simp [FormW.const], ?_, ?_, ?_⟩, ?_, ?_⟩ <;> mem_simp <;> rfl
  · mem_simp
    rw [show Nat.toUInt64 3 = 3 from rfl, times8, add_comm]
    rfl
  · keep_tac

/-- **A block's form**: `F = buildF`, the owner's form's address in `vG`, the next block's data in
`vCur`. -/
theorem buildCode_spec {side wOff bOff q : Nat} {b : DBlk} {ws : Array EW} {β : EW}
    (hrdi : s.reg .rdi = ctx) (hwp : s.mem (wd ctx ctxWork) = some w)
    (hcw : ∀ k < dataEnd, wd ctx ctxWork ≠ wd w k)
    (hcur : s.mem (wd w vCur) = some (wd w q)) (hblk : BlkAt s.mem w q side b)
    (hok : blkOk side b = true)
    (hws : ∀ e ∈ b.2, EAtI s.mem w (wOff + 2 * e.1) (ws.getD e.1 0))
    (hβ : EAtI s.mem w bOff β) (hdom : ∀ k, fOff ≤ k → k ≤ vG → (s.mem (wd w k)).isSome)
    (hq : vG < q) (hq' : q + 2 + 5 * b.2.length ≤ dataEnd)
    (hwo : wOff + 32 ≤ fOff ∨ vG < wOff) (hwo' : wOff + 32 ≤ dataEnd)
    (hbo : bOff + 2 ≤ fOff ∨ vG < bOff) (hbo' : bOff + 2 ≤ dataEnd) :
    WP (buildCode wOff bOff) s (fun s' ↦ s'.reg .rdi = ctx ∧
      FZ s'.mem w fOff fCap (buildF b.2 ws β) ∧
      s'.mem (wd w vCur) = some (wd w (q + (encBlk side b).length)) ∧
      s'.mem (wd w vG) = some (wd w (busR.off + formOff b.1 side)) ∧
      KeepS w (fun k ↦ SF k ∨ k = vCur ∨ k = vG) s.mem s'.mem) E := by
  have v1 := fOff_val
  have v2 := vG_val
  have v3 := vCur_val
  have v4 := dataEnd_eq
  have v5 := fCap_val
  obtain ⟨-, hn31, hent⟩ := blkOk_spec hok
  have hblk' := hblk
  obtain ⟨-, -, hE⟩ := hblk'
  unfold buildCode
  refine wp_then' (buildPre_spec (E := E) (w := w) (wOff := wOff) hrdi hwp hcur hblk hβ hdom hq hq'
    hbo hbo') fun s1 ⟨r1, r12, r14, r13, r15, hF, hG, hK1⟩ hd1 ↦ ?_
  have k1 : ∀ k, k < dataEnd → ¬ ((fOff ≤ k ∧ k < fOff + 6) ∨ k = vG) →
      s1.mem (wd w k) = s.mem (wd w k) := fun k hk hn ↦
    hK1.word (by oo) fun j hj ↦ ⟨by oo, fun e ↦ hn (e ▸ hj)⟩
  refine wp_then' (entLoop_spec (E := E) (w := w) (q := q + 2) (wOff := wOff) (es := b.2) (ws := ws)
    (β := β) r12 (by rw [r14]) r13 r15 hF
    (fun j hj ↦ (hE j hj).congr fun k hk ↦ k1 _ (by oo) (by oo))
    (fun e he ↦ by
      have := (hent e he).1
      have := slotN_le side
      exact (hws e he).congr fun k hk ↦ k1 _ (by oo) (by oo))
    (fun e he ↦ ⟨by have := (hent e he).1; have := slotN_le side; omega, (hent e he).2.1,
      fun a ha ↦ by have := ((hent e he).2.2.1 a ha).1; omega⟩)
    hn31 (fun k hk ↦ by rw [hd1]; exact hdom k (by oo) (by oo)) (by oo) (by oo) (by oo) hwo')
    fun s2 ⟨hF2, h12, hK2, hR2⟩ hd2 ↦ ?_
  have k2 : ∀ k, k < dataEnd → ¬ SF k → s2.mem (wd w k) = s1.mem (wd w k) := fun k hk hn ↦
    hK2.word (by oo) fun j hj ↦ ⟨by oo, fun e ↦ hn (e ▸ hj)⟩
  have hr2 : s2.reg .rdi = ctx := (hR2 .rdi (by decide)).trans r1
  have hc2 : s2.mem (wd ctx ctxWork) = some w := by
    rw [hK2 _ fun k hk ↦ hcw k (by oo), hK1 _ fun k hk ↦ hcw k (by oo)]
    exact hwp
  refine wk_wp hr2 hc2 ?_
  refine stw0 (w := w) (k := vCur) (by rsimp) (by rsimp; rw [hd2, hd1]; exact hdom _ (by oo) (by oo)) ?_
  refine wp_done ⟨by rsimp; exact hr2, ?_, ?_, ?_, ?_⟩
  · refine hF2.congr fun k hk ↦ ?_
    mem_simp
  · mem_simp
    rw [h12, encBlk_length]
    congr 2
    omega
  · mem_simp
    rw [k2 _ (by oo) (by oo)]
    exact hG
  · refine KeepS.setMem ((hK1.trans hK2 (fun k h ↦ ?_) (fun k h ↦ .inl h)).setReg') (.inr (.inl rfl)) _
    rcases h with h | h
    · exact .inl ⟨by oo, by oo⟩
    · exact .inr (.inr h)

end NativeVm.Code.P3
