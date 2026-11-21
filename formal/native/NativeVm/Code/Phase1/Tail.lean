module

public import NativeVm.Code.Phase1.Place

/-!
# Phase 1 after reading

`tail_spec`: from the eight scalars' low limbs at layout words `9 ..` and their high limbs' `or` in
`r13`, `tail` ends normally exactly when phase 1's checks hold (`TailOk`), the layout then written
(`LayoutAt`), and fails otherwise; it writes only the layout's words (`LFr`).
-/

@[expose] public section

namespace NativeVm.Code.Phase1

open Native NativeVm.Model LeanVM.Protocol.Verifier
open NativeVm.Transcript (wd wp_then toNat_toUInt64 ctxBytecodeLen)

variable {s : QState}

/-- The high limbs' `or`. -/
def orC (a : Array EW) : UInt64 := a.foldl (fun x e ↦ x ||| e.c1) 0

theorem orC_push (a : Array EW) (x : EW) : orC (a.push x) = orC a ||| x.c1 := by
  simp [orC]

theorem foldl_or_eq_zero (l : List EW) (x : UInt64) :
    l.foldl (fun x e ↦ x ||| e.c1) x = 0 ↔ x = 0 ∧ ∀ e ∈ l, e.c1 = 0 := by
  induction l generalizing x with
  | nil => simp
  | cons e l ih =>
    rw [List.foldl_cons, ih, UInt64.or_eq_zero_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem orC_eq_zero (a : Array EW) : orC a = 0 ↔ (a.all (·.c1 == 0)) = true := by
  rw [orC, ← Array.foldl_toList, foldl_or_eq_zero, Array.all_eq_true_iff_forall_mem]
  simp

theorem getD_word {a : Array EW} {i : Nat} : (a.getD i 0).c0 = (a.getD i 0).c0.toNat.toUInt64 :=
  (toUInt64_toNat _).symm

theorem plF_vars {κ : Nat → Nat} {c : Nat} {pl : Placement} (h : plF κ c = some pl) :
    pl.variableCount = κ c := by
  unfold plF at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · cases h; rfl

theorem layoutA_stackLog (bc : Array UInt64) (a : Array EW) :
    (layoutA bc a).stackLog = stackLogF (kapF (lmA a) (bitLength bc.size - 5) (heightsF (rowsA a))) := by
  unfold layoutA
  rw [(layoutF_facts bc (lmA a) (bitLength bc.size - 5) (rowsA a)).2.2.2.2.2.2.2]
  rfl

theorem tail_spec {p ctx : UInt64} {bc : Array UInt64} {a : Array EW} (hr14 : s.reg .r14 = p)
    (hrdi : s.reg .rdi = ctx) (hn : s.mem (wd ctx ctxBytecodeLen) = some bc.size.toUInt64)
    (hn64 : bc.size < 2 ^ 64) (hd : LDom p s.mem) (ha : a.size = 8)
    (hw : ∀ i < 8, s.mem (wd p (9 + i)) = some (a.getD i 0).c0) (h13 : s.reg .r13 = orC a) :
    WP tail s (fun s' ↦ TailOk bc a ∧ LayoutAt s'.mem p bc (layoutA bc a) (rateA a) ∧ LFr p s s')
      (fun s' ↦ ¬ TailOk bc a ∧ LFr p s s') := by
  unfold tail checks
  apply WP.blk_cons
  have hlm : (a.getD 0 0).c0.toNat = lmA a := rfl
  have hra : (a.getD 7 0).c0.toNat = rateA a := (rateA_eq ha).symm
  refine wp_then (WP.mono (checkBc_spec hr14 hrdi hn hn64 hd) (fun _ h ↦ h)
    (fun _ ⟨h1, h2⟩ ↦ ⟨fun h ↦ h1 ⟨h.2.2.1, h.2.2.2.1⟩, h2⟩)) fun s₁ ⟨b1, b2, b3, F1, b13⟩ ↦ ?_
  refine WP.mono (checkScalars_spec (v0 := (a.getD 0 0).c0) (v7 := (a.getD 7 0).c0)
    (by rw [F1.r14, hr14]) (LDom.of_fr hd F1)
    (by rw [b3 9 (by omega) (by omega)]; exact hw 0 (by omega))
    (by rw [b3 16 (by omega) (by omega)]; exact hw 7 (by omega)))
    (fun s₂ ⟨c1, c2, c3, c4, F2⟩ ↦ ?_)
    (fun _ ⟨h1, h2⟩ ↦ ⟨fun h ↦ h1 ⟨by rw [b13, h13]; exact (orC_eq_zero a).mpr h.1,
      by rw [hra]; exact h.2.1, by rw [hlm]; exact h.2.2.2.2.1⟩, F1.trans h2⟩)
  rw [b13, h13] at c1
  obtain ⟨o1, o2, o3⟩ := c1
  rw [hra] at o2
  rw [hlm] at o3
  have hs2 : ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 3 → k < 2 ^ 61 → s₂.mem (wd p k) = s.mem (wd p k) :=
    fun k h0 h1 h3 hk ↦ (c4 k h0 h3 hk).trans (b3 k h1 hk)
  have hrs := rowsA_size ha
  refine wp_then (WP.mono (heights_spec (rw := fun i ↦ (a.getD (1 + i) 0).c0)
    (by rw [F2.r14, F1.r14, hr14]) (LDom.of_fr (LDom.of_fr hd F1) F2) fun i hi ↦ by
      rw [hs2 _ (by omega) (by omega) (by omega) (by omega)]
      have := hw (1 + i) (by omega)
      rwa [show 9 + (1 + i) = 10 + i by omega] at this) (fun _ h ↦ h)
    (fun _ ⟨h1, h2⟩ ↦ ⟨fun h ↦ h1 fun i hi ↦ by
      have := h.2.2.2.2.2.1 i hi; rwa [rowsA_getD ha hi] at this, (F1.trans F2).trans h2⟩))
    fun s₃ ⟨d1, d2, d3, F3⟩ ↦ ?_
  have hrows : ∀ i < 6, (rowsA a).getD i 0 ≤ 2 ^ 30 := fun i hi ↦ by
    rw [rowsA_getD ha hi]; exact d1 i hi
  have hhs : ∀ i < 6, (heightsF (rowsA a)).getD i 0 ≤ 30 := fun i hi ↦ by
    rw [heightsF_getD hrs hi]
    have := log2Ceil_le (hrows i hi)
    unfold floorF; split <;> omega
  have hm3 : KapMem s₃.mem p (lmA a) (bitLength bc.size - 5) (heightsF (rowsA a)) := by
    refine ⟨?_, ?_, fun i hi ↦ ?_, o3.2, by have := b1.2.2; omega, hhs⟩
    · rw [d3 0 (by omega) (by omega), c2, getD_word]; rfl
    · rw [d3 1 (by omega) (by omega), c4 1 (by omega) (by omega) (by omega), b2]
    · rw [d2 i hi, heightsF_getD hrs hi, rowsA_getD ha hi]
  refine wp_then (WP.mono (stackC_spec (by rw [F3.r14, F2.r14, F1.r14, hr14])
    (LDom.of_fr (LDom.of_fr (LDom.of_fr hd F1) F2) F3) hm3) (fun _ h ↦ h)
    (fun _ ⟨h1, h2⟩ ↦ ⟨fun h ↦ h1 ?_, ((F1.trans F2).trans F3).trans h2⟩))
    fun s₄ ⟨e1, e2, e3, e4, F4⟩ ↦ ?_
  · rw [← layoutA_stackLog]; exact h.2.2.2.2.2.2
  have hm4 : KapMem s₄.mem p (lmA a) (bitLength bc.size - 5) (heightsF (rowsA a)) := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hm3
    exact ⟨by rw [e3 0 (by omega) (by omega)]; exact a1, by rw [e3 1 (by omega) (by omega)]; exact a2,
      fun i hi ↦ by rw [e3 _ (by omega) (by omega)]; exact a3 i hi, a4, a5, a6⟩
  refine WP.mono (placeLoop_spec (by rw [F4.r14, F3.r14, F2.r14, F1.r14, hr14])
    (LDom.of_fr (LDom.of_fr (LDom.of_fr (LDom.of_fr hd F1) F2) F3) F4) hm4 e4)
    (fun s₅ ⟨g1, g2, F5⟩ ↦ ?_) (fun _ h ↦ h)
  have hrows' : ∀ i < 6, (rowsA a).getD i 0 ≤ 2 ^ 30 := hrows
  have FF := layoutF_facts bc (lmA a) (bitLength bc.size - 5) (rowsA a)
  have hA : layoutF bc (lmA a) (bitLength bc.size - 5) (rowsA a) = layoutA bc a := rfl
  rw [hA] at FF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, -⟩ := FF
  have hlb : bitLength bc.size - 5 ≤ 30 := by have := b1.2.2; omega
  have w0 : s₅.mem p = some (lmA a).toUInt64 := by
    rw [← NativeVm.Transcript.wd_zero p, g2 0 (by omega), e3 0 (by omega) (by omega),
      d3 0 (by omega) (by omega), c2, getD_word]; rfl
  have w1 : s₅.mem (wd p 1) = some (bitLength bc.size - 5).toUInt64 := by
    rw [g2 1 (by omega), e3 1 (by omega) (by omega), d3 1 (by omega) (by omega),
      c4 1 (by omega) (by omega) (by omega), b2]
  have w2 : s₅.mem (wd p 2) = some (layoutA bc a).stackLog.toUInt64 := by
    rw [g2 2 (by omega), e2, layoutA_stackLog]
  have w3 : s₅.mem (wd p 3) = some (rateA a).toUInt64 := by
    rw [g2 3 (by omega), e3 3 (by omega) (by omega), d3 3 (by omega) (by omega), c3, ← hra,
      ← getD_word]
  have hsl := layoutA_stackLog bc a
  refine ⟨⟨(orC_eq_zero a).mp o1, o2, b1.1, b1.2, o3, hrows', by rw [hsl]; exact e1⟩, ?_,
    (((F1.trans F2).trans F3).trans F4).trans F5⟩
  exact {
    bytecode := f3
    logMemory := ⟨by rw [f1]; omega, by rw [f1]; exact w0⟩
    logBytecode := ⟨by rw [f2]; omega, by rw [f2]; exact w1⟩
    stackLog := ⟨by rw [hsl]; omega, w2⟩
    rateWord := ⟨by omega, w3⟩
    heightsSize := by rw [f4]; exact heightsF_size hrs
    heights := fun i (hi : i < 6) ↦ ⟨by rw [f4]; have := hhs i hi; omega, by
      rw [f4, g2 _ (by omega), e3 _ (by omega) (by omega), d2 i hi,
        heightsF_getD hrs hi, rowsA_getD ha hi]⟩
    rows := ⟨rowsA a, hrs, fun i (hi : i < 6) ↦ ⟨⟨by have := hrows' i hi; omega, by
      rw [g2 _ (by omega), e3 _ (by omega) (by omega),
        d3 _ (by omega) (by omega), hs2 _ (by omega) (by omega) (by omega) (by omega),
        rowsA_getD ha hi, ← getD_word]
      have := hw (1 + i) (by omega)
      rwa [show 9 + (1 + i) = 10 + i by omega] at this⟩, hrows' i hi⟩, by rw [f4]; exact f5⟩
    placementsSize := by rw [f6, columnCount_val]
    placements := fun c hc ↦ by
      rw [columnCount_val] at hc
      rw [f7 c hc]; exact g1 c hc
    logMemoryBound := by rw [f1]; exact o3
    logBytecodeBound := by rw [f2]; exact hlb
    stackLogBound := ⟨by rw [hsl]; exact Nat.le_max_left _ _, by rw [hsl]; exact e1⟩
    rateBound := o2
    heightsBound := fun i hi ↦ by rw [f4]; exact hhs i hi
    placementsBound := fun c hc pl hpl ↦ by
      rw [columnCount_val] at hc
      rw [f7 c hc] at hpl
      rw [plF_vars hpl, pointCap_val]
      exact hm3.kap_le c }

end NativeVm.Code.Phase1
