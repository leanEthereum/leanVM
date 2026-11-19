module

public import NativeVm.Code.Phase3.SelPad

/-!
# Phase 3's selectors: the loops

`selFw_spec`: the `fw` framework placements' `eqAbove` at words `fo + 2 j`; `selTb_spec`: the `nb`
table placements' `eqAbove` at `to + 2 k` and their blocks' `paddingWeight` at `wo + 2 k`. Each
reads words outside what it writes (`Keeps`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

/-- `m'` is `m` at every word `w` of the area at `p` outside `[lo, hi)`. -/
def KeepsOut (p : UInt64) (lo hi : Nat) (m m' : UInt64 → Option UInt64) : Prop :=
  ∀ w < 2 ^ 61, (w < lo ∨ hi ≤ w) → m' (wd p w) = m (wd p w)

theorem PointAt.keeps {m m' : UInt64 → Option UInt64} {p : UInt64} {lo hi : Nat}
    {point : Array EW} (h : PointAt m p point) (hk : KeepsOut p lo hi m m')
    (hlo : hi ≤ pointR.off ∨ pointR.off + 128 ≤ lo) (hps : point.size ≤ 64)
    (hb : pointR.off + 128 < 2 ^ 61) : PointAt m' p point := fun t ht ↦ by
  rw [hk _ (by omega) (by omega), hk _ (by omega) (by omega)]
  exact h t ht

variable {s : QState} {F : QState → Prop}

/-- A store of `r9` or `r10` to word `w` through `aI r14 k`. -/
theorem store_step {p : UInt64} {ix : Reg64} {i k : Nat} {src : Reg64} {xs : List Stmt}
    {P : QState → Prop} (h15 : s.reg .r15 = p) (h14 : s.reg ix = i.toUInt64)
    (hd : (s.mem (wd p (k + i))).isSome)
    (h : WP (blk xs) (s.setMem (wd p (k + i)) (s.reg src)) P F) :
    WP (blk (I (.store (aI ix k) src) :: xs)) s P F := by
  refine wp_store ((eval_aI h15 h14 k).trans (by rw [Nat.add_comm])) hd h

theorem selFw_spec {p : UInt64} {po fo fw : Nat} {pl : Array LeanVM.Protocol.Verifier.Placement} {point : Array EW}
    (hfw : pl.size = fw) (hfwb : fw ≤ 64) (hfo : fo + 2 * fw < 2 ^ 61)
    (h15 : s.reg .r15 = p)
    (hpl : ∀ j (h : j < pl.size), s.mem (wd p (po + 2 * j)) = some pl[j].variableCount.toUInt64 ∧
      s.mem (wd p (po + 2 * j + 1)) = some pl[j].index.toUInt64 ∧
      pl[j].variableCount < 2 ^ 64 ∧ pl[j].index < 2 ^ 64)
    (hn : s.mem (wd p depthR.off) = some point.size.toUInt64) (hps : point.size < 64)
    (hp : PointAt s.mem p point)
    (hsep : (fo + 2 * fw ≤ po ∨ po + 2 * fw ≤ fo) ∧ (fo + 2 * fw ≤ depthR.off ∨ depthR.off < fo) ∧
      (fo + 2 * fw ≤ pointR.off ∨ pointR.off + 128 ≤ fo) ∧ po + 2 * fw < 2 ^ 61 ∧
      depthR.off < 2 ^ 61 ∧ pointR.off + 128 < 2 ^ 61)
    (hdom : ∀ w < 2 * fw, (s.mem (wd p (fo + w))).isSome) :
    WP (selFw po fo fw) s (fun s' ↦
      (∀ j (h : j < pl.size), s'.mem (wd p (fo + 2 * j)) = some (eqAbove pl[j] point).c0 ∧
        s'.mem (wd p (fo + 2 * j + 1)) = some (eqAbove pl[j] point).c1) ∧
      KeepsOut p fo (fo + 2 * fw) s.mem s'.mem ∧ (∀ a, (s'.mem a).isSome = (s.mem a).isSome) ∧
      (∀ a, (∀ w, fo ≤ w → w < fo + 2 * fw → a ≠ wd p w) → s'.mem a = s.mem a) ∧
      RegsFrame (.r14 :: selRegs) s s') F := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hsep
  unfold selFw
  fstep
  apply WP.blk_cons
  apply WP.loop (fun u ↦ ∃ i ≤ fw, u.reg .r14 = (2 * i).toUInt64 ∧
      (∀ j (h : j < pl.size), j < i → u.mem (wd p (fo + 2 * j)) = some (eqAbove pl[j] point).c0 ∧
        u.mem (wd p (fo + 2 * j + 1)) = some (eqAbove pl[j] point).c1) ∧
      KeepsOut p fo (fo + 2 * fw) s.mem u.mem ∧ (∀ a, (u.mem a).isSome = (s.mem a).isSome) ∧
      (∀ a, (∀ w, fo ≤ w → w < fo + 2 * fw → a ≠ wd p w) → u.mem a = s.mem a) ∧
      RegsFrame (.r14 :: selRegs) s u)
    (fun u ↦ fw - (u.reg .r14).toNat / 2)
  · exact ⟨0, by omega, by rsimp; rfl, fun j _ hj ↦ absurd hj (by omega), fun _ _ _ ↦ rfl,
      fun _ ↦ rfl, fun _ _ ↦ rfl, by rf_tac⟩
  · rintro u ⟨i, hi, h14, hw, hk, hd, ho, hf⟩ hc
    rw [cmp_ne_lit (a := 2 * i) (by omega) (by omega) h14] at hc
    have hif : i < fw := by simp at hc; omega
    have hi' : i < pl.size := by omega
    have h15' : u.reg .r15 = p := by rw [hf .r15 (by decide)]; exact h15
    obtain ⟨v1, v2, v3, v4⟩ := hpl i hi'
    refine wp_then (eqAb_spec (src := po) (point := point) h15' h14
      (by rw [hk _ (by omega) (by omega)]; exact v1) (by rw [hk _ (by omega) (by omega)]; exact v2)
      (by rw [hk _ (by omega) (by omega)]; exact hn) v3 v4 hps
      (hp.keeps hk (by omega) (by omega) s6)) fun u₁ ⟨e9, e10, em, ef⟩ ↦ ?_
    have r14 : u₁.reg .r14 = (2 * i).toUInt64 := by rw [ef .r14 (by decide)]; exact h14
    have r15 : u₁.reg .r15 = p := by rw [ef .r15 (by decide)]; exact h15'
    have d0 : (u₁.mem (wd p (fo + 2 * i))).isSome := by rw [em, hd]; exact hdom _ (by omega)
    have d1 : (u₁.mem (wd p (fo + 1 + 2 * i))).isSome := by
      rw [em, hd, show fo + 1 + 2 * i = fo + (2 * i + 1) by omega]; exact hdom _ (by omega)
    refine store_step r15 r14 d0 ?_
    refine store_step (by rsimp; exact r15) (by rsimp; exact r14) (by rw [dom_setMem d0]; exact d1) ?_
    fstep; fdone
    refine ⟨⟨i + 1, by omega, by rw [r14, toUInt64_add_two]; congr 1, fun j hj hji ↦ ?_, ?_, ?_, ?_,
      ?_⟩, ?_⟩
    · by_cases e : j = i
      · subst e
        refine ⟨?_, ?_⟩
        · rw [setMem_other (by omega) (by omega) (by omega), setMem_same, e9]
        · rw [show fo + 2 * j + 1 = fo + 1 + 2 * j by omega, setMem_same, e10]
      · rw [setMem_other (by omega) (by omega) (by omega), setMem_other (by omega) (by omega) (by omega),
          setMem_other (by omega) (by omega) (by omega), setMem_other (by omega) (by omega) (by omega),
          em]
        exact hw j hj (by omega)
    · intro w hw' hout
      rw [setMem_other (by omega) hw' (by omega), setMem_other (by omega) hw' (by omega), em]
      exact hk w hw' hout
    · intro a
      rw [dom_setMem (by rw [dom_setMem d0]; exact d1), dom_setMem d0, em, hd]
    · intro a ha
      rw [QState.setMem_mem, QState.setMem_mem,
        ite_eq_right_of_eq_false _ _ (eq_false (ha _ (by omega) (by omega))),
        ite_eq_right_of_eq_false _ _ (eq_false (ha _ (by omega) (by omega))), em]
      exact ho a ha
    · intro r hr
      have hr' := hr
      simp only [selRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      rw [QState.setReg_reg, ite_eq_right_of_eq_false _ _ (eq_false hr'.1), QState.setMem_reg,
        QState.setMem_reg, ef r (fun h ↦ hr (List.mem_cons_of_mem _ h))]
      exact hf r hr
    · rw [r14, toUInt64_add_two, Transcript.toNat_toUInt64 (by omega), h14,
        Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro u ⟨i, hi, h14, hw, hk, hd, ho, hf⟩ hc
    rw [cmp_ne_lit (a := 2 * i) (by omega) (by omega) h14] at hc
    have hif : i = fw := by simp at hc; omega
    exact WP.blk_nil ⟨fun j hj ↦ hw j hj (by omega), hk, hd, ho, hf⟩

theorem selTb_spec {p : UInt64} {po ro tso wo nb : Nat} {pl : Array LeanVM.Protocol.Verifier.Placement}
    {B : Array BusBlockW} {point : Array EW}
    (hsz : pl.size = nb) (hB : B.size = nb) (hnb : nb ≤ 64) (htw : tso + 2 * nb ≤ wo)
    (hwo : wo + 2 * nb < 2 ^ 61) (h15 : s.reg .r15 = p)
    (hpl : ∀ k (h : k < pl.size), s.mem (wd p (po + 2 * k)) = some pl[k].variableCount.toUInt64 ∧
      s.mem (wd p (po + 2 * k + 1)) = some pl[k].index.toUInt64 ∧
      pl[k].variableCount < 2 ^ 64 ∧ pl[k].index < 2 ^ 64)
    (hrows : ∀ k (h : k < B.size), s.mem (wd p (ro + k)) = some B[k].rows.toUInt64 ∧
      B[k].rows < 2 ^ 64)
    (hlr : ∀ k (h : k < pl.size) (h' : k < B.size), pl[k].variableCount = B[k].logRows)
    (hn : s.mem (wd p depthR.off) = some point.size.toUInt64) (hps : point.size < 64)
    (hp : PointAt s.mem p point)
    (hsep : (wo + 2 * nb ≤ po ∨ po + 2 * nb ≤ tso) ∧ (wo + 2 * nb ≤ ro ∨ ro + nb ≤ tso) ∧
      (wo + 2 * nb ≤ depthR.off ∨ depthR.off < tso) ∧
      (wo + 2 * nb ≤ pointR.off ∨ pointR.off + 128 ≤ tso) ∧ po + 2 * nb < 2 ^ 61 ∧
      ro + nb < 2 ^ 61 ∧ depthR.off < 2 ^ 61 ∧ pointR.off + 128 < 2 ^ 61)
    (hdomT : ∀ w < 2 * nb, (s.mem (wd p (tso + w))).isSome)
    (hdomW : ∀ w < 2 * nb, (s.mem (wd p (wo + w))).isSome) :
    WP (selTb po ro tso wo nb) s (fun s' ↦
      (∀ k (h : k < pl.size), s'.mem (wd p (tso + 2 * k)) = some (eqAbove pl[k] point).c0 ∧
        s'.mem (wd p (tso + 2 * k + 1)) = some (eqAbove pl[k] point).c1) ∧
      (∀ k (h : k < B.size),
        s'.mem (wd p (wo + 2 * k)) = some (paddingWeight (point.extract 0 B[k].logRows) B[k].rows).c0 ∧
        s'.mem (wd p (wo + 2 * k + 1)) =
          some (paddingWeight (point.extract 0 B[k].logRows) B[k].rows).c1) ∧
      (∀ a, (s'.mem a).isSome = (s.mem a).isSome) ∧
      (∀ a, (∀ w, tso ≤ w → w < wo + 2 * nb → a ≠ wd p w) → s'.mem a = s.mem a) ∧
      RegsFrame (.r14 :: selRegs) s s') F := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hsep
  unfold selTb
  fstep
  apply WP.blk_cons
  apply WP.loop (fun u ↦ ∃ i ≤ nb, u.reg .r14 = (2 * i).toUInt64 ∧
      (∀ k (h : k < pl.size), k < i → u.mem (wd p (tso + 2 * k)) = some (eqAbove pl[k] point).c0 ∧
        u.mem (wd p (tso + 2 * k + 1)) = some (eqAbove pl[k] point).c1) ∧
      (∀ k (h : k < B.size), k < i →
        u.mem (wd p (wo + 2 * k)) = some (paddingWeight (point.extract 0 B[k].logRows) B[k].rows).c0 ∧
        u.mem (wd p (wo + 2 * k + 1)) =
          some (paddingWeight (point.extract 0 B[k].logRows) B[k].rows).c1) ∧
      KeepsOut p tso (wo + 2 * nb) s.mem u.mem ∧ (∀ a, (u.mem a).isSome = (s.mem a).isSome) ∧
      (∀ a, (∀ w, tso ≤ w → w < wo + 2 * nb → a ≠ wd p w) → u.mem a = s.mem a) ∧
      RegsFrame (.r14 :: selRegs) s u)
    (fun u ↦ nb - (u.reg .r14).toNat / 2)
  · exact ⟨0, by omega, by rsimp; rfl, fun k _ hk ↦ absurd hk (by omega),
      fun k _ hk ↦ absurd hk (by omega), fun _ _ _ ↦ rfl, fun _ ↦ rfl, fun _ _ ↦ rfl, by rf_tac⟩
  · rintro u ⟨i, hi, h14, hw, hw', hk, hd, ho, hf⟩ hc
    rw [cmp_ne_lit (a := 2 * i) (by omega) (by omega) h14] at hc
    have hif : i < nb := by simp at hc; omega
    have hi' : i < pl.size := by omega
    have hiB : i < B.size := by omega
    have h15' : u.reg .r15 = p := by rw [hf .r15 (by decide)]; exact h15
    obtain ⟨v1, v2, v3, v4⟩ := hpl i hi'
    obtain ⟨w1, w2⟩ := hrows i hiB
    have hpu := hp.keeps hk (by omega) (by omega) s8
    have hnu : u.mem (wd p depthR.off) = some point.size.toUInt64 := by
      rw [hk _ (by omega) (by omega)]; exact hn
    refine wp_then (eqAb_spec (src := po) (point := point) h15' h14
      (by rw [hk _ (by omega) (by omega)]; exact v1) (by rw [hk _ (by omega) (by omega)]; exact v2)
      hnu v3 v4 hps hpu) fun u₁ ⟨e9, e10, em, ef⟩ ↦ ?_
    have r14 : u₁.reg .r14 = (2 * i).toUInt64 := by rw [ef .r14 (by decide)]; exact h14
    have r15 : u₁.reg .r15 = p := by rw [ef .r15 (by decide)]; exact h15'
    have d0 : (u₁.mem (wd p (tso + 2 * i))).isSome := by rw [em, hd]; exact hdomT _ (by omega)
    have d1 : (u₁.mem (wd p (tso + 1 + 2 * i))).isSome := by
      rw [em, hd, show tso + 1 + 2 * i = tso + (2 * i + 1) by omega]; exact hdomT _ (by omega)
    refine store_step r15 r14 d0 ?_
    refine store_step (by rsimp; exact r15) (by rsimp; exact r14) (by rw [dom_setMem d0]; exact d1) ?_
    -- the padding weight
    set u₂ := (u₁.setMem (wd p (tso + 2 * i)) (u₁.reg .r9)).setMem (wd p (tso + 1 + 2 * i))
      ((u₁.setMem (wd p (tso + 2 * i)) (u₁.reg .r9)).reg .r10) with hu₂
    have m2 : ∀ w < 2 ^ 61, w ≠ tso + 2 * i → w ≠ tso + 1 + 2 * i →
        u₂.mem (wd p w) = u.mem (wd p w) := fun w hw hw1 hw2 ↦ by
      rw [hu₂, setMem_other (by omega) hw (by omega), setMem_other (by omega) hw (by omega), em]
    refine wp_then (padAb_spec (p := p) (src := po) (rows := ro) (i := i) (point := point) (lr := pl[i].variableCount)
      (R := B[i].rows) (by rw [hu₂]; rsimp; exact r15) (by rw [hu₂]; rsimp; exact r14)
      (by rw [m2 _ (by omega) (by omega) (by omega)]; exact (hk _ (by omega) (by omega)).trans v1)
      (by rw [m2 _ (by omega) (by omega) (by omega)]; exact (hk _ (by omega) (by omega)).trans w1)
      (by rw [m2 _ (by omega) (by omega) (by omega)]; exact hnu) v3 w2 hps
      (fun t ht ↦ by
        rw [m2 _ (by omega) (by omega) (by omega), m2 _ (by omega) (by omega) (by omega)]
        exact hpu t ht)) fun u₃ ⟨g9, g10, gm, gf⟩ ↦ ?_
    have r14' : u₃.reg .r14 = (2 * i).toUInt64 := by rw [gf .r14 (by decide), hu₂]; rsimp; exact r14
    have r15' : u₃.reg .r15 = p := by rw [gf .r15 (by decide), hu₂]; rsimp; exact r15
    have hu₂d : ∀ a, (u₂.mem a).isSome = (s.mem a).isSome := fun a ↦ by
      rw [hu₂, dom_setMem (by rw [dom_setMem d0]; exact d1), dom_setMem d0, em, hd]
    have d2 : (u₃.mem (wd p (wo + 2 * i))).isSome := by rw [gm, hu₂d]; exact hdomW _ (by omega)
    have d3 : (u₃.mem (wd p (wo + 1 + 2 * i))).isSome := by
      rw [gm, hu₂d, show wo + 1 + 2 * i = wo + (2 * i + 1) by omega]; exact hdomW _ (by omega)
    rw [hlr i hi' hiB] at g9 g10
    refine store_step r15' r14' d2 ?_
    refine store_step (by rsimp; exact r15') (by rsimp; exact r14') (by rw [dom_setMem d2]; exact d3) ?_
    fstep; fdone
    refine ⟨⟨i + 1, by omega, by rw [r14', toUInt64_add_two]; congr 1, fun k hk' hki ↦ ?_,
      fun k hk' hki ↦ ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [setMem_other (by omega) (by omega) (by omega), setMem_other (by omega) (by omega) (by omega),
        setMem_other (by omega) (by omega) (by omega), setMem_other (by omega) (by omega) (by omega), gm]
      by_cases e : k = i
      · subst e
        rw [hu₂, setMem_other (by omega) (by omega) (by omega), setMem_same, e9,
          show tso + 2 * k + 1 = tso + 1 + 2 * k by omega, setMem_same, QState.setMem_reg, e10]
        exact ⟨rfl, rfl⟩
      · rw [m2 _ (by omega) (by omega) (by omega), m2 _ (by omega) (by omega) (by omega)]
        exact hw k hk' (by omega)
    · by_cases e : k = i
      · subst e
        refine ⟨?_, ?_⟩
        · rw [setMem_other (by omega) (by omega) (by omega), setMem_same, g9]
        · rw [show wo + 2 * k + 1 = wo + 1 + 2 * k by omega, setMem_same, g10]
      · rw [setMem_other (by omega) (by omega) (by omega), setMem_other (by omega) (by omega) (by omega),
          setMem_other (by omega) (by omega) (by omega), setMem_other (by omega) (by omega) (by omega),
          gm, m2 _ (by omega) (by omega) (by omega), m2 _ (by omega) (by omega) (by omega)]
        exact hw' k hk' (by omega)
    · intro w hw' hout
      rw [setMem_other (by omega) hw' (by omega), setMem_other (by omega) hw' (by omega), gm,
        m2 _ hw' (by omega) (by omega)]
      exact hk w hw' hout
    · intro a
      rw [dom_setMem (by rw [dom_setMem d2]; exact d3), dom_setMem d2, gm, hu₂d]
    · intro a ha
      rw [QState.setMem_mem, QState.setMem_mem,
        ite_eq_right_of_eq_false _ _ (eq_false (ha _ (by omega) (by omega))),
        ite_eq_right_of_eq_false _ _ (eq_false (ha _ (by omega) (by omega))), gm, hu₂,
        QState.setMem_mem, QState.setMem_mem,
        ite_eq_right_of_eq_false _ _ (eq_false (ha _ (by omega) (by omega))),
        ite_eq_right_of_eq_false _ _ (eq_false (ha _ (by omega) (by omega))), em]
      exact ho a ha
    · intro r hr
      have hr' := hr
      simp only [selRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      have hr2 : r ∉ selRegs := fun h ↦ hr (List.mem_cons_of_mem _ h)
      rw [QState.setReg_reg, ite_eq_right_of_eq_false _ _ (eq_false hr'.1), QState.setMem_reg,
        QState.setMem_reg, gf r hr2, hu₂, QState.setMem_reg, QState.setMem_reg, ef r hr2]
      exact hf r hr
    · rw [r14', toUInt64_add_two, Transcript.toNat_toUInt64 (by omega), h14,
        Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro u ⟨i, hi, h14, hw, hw', hk, hd, ho, hf⟩ hc
    rw [cmp_ne_lit (a := 2 * i) (by omega) (by omega) h14] at hc
    have hif : i = nb := by simp at hc; omega
    exact WP.blk_nil ⟨fun k hk' ↦ hw k hk' (by omega), fun k hk' ↦ hw' k hk' (by omega), hd, ho, hf⟩

end NativeVm.Code.P3
