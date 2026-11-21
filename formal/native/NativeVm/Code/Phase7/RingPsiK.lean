module

public import NativeVm.Code.Phase7.RingCoeffK
public import NativeVm.Code.Phase7.RingWE

/-!
# Ring switching's inner map on the slices

`psiK sO gO iO`: `images = s.map (ringPsi · g)` from the slices `s` at work words `sO` (`64`
elements) and `g` at `gO` (eight) to `iO`, `rbp` the working area. Element by element
(`psiElem`): the sum `Σ_b g_b · s_i^(2^b)` accumulated in place, one `psiStep b` per `g_b`, each
`s_i^(2^b)` by `esqn`.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wdisp wdisp_toUInt64 wp_load wp_store wp_storei)

variable {s : QState} {F : QState → Prop}

/-! ## `ringPsi` term by term -/

/-- `ringPsi`'s step. -/
def psiF (acc : E × E) (gB : E) : E × E := (acc.1 + gB * acc.2, acc.2 * acc.2)

theorem psiF_foldl_snd : ∀ (L : List E) (acc : E × E),
    (L.foldl psiF acc).2 = acc.2 ^ 2 ^ L.length
  | [], acc => by simp
  | gB :: L, acc => by
    rw [List.foldl_cons, psiF_foldl_snd L, List.length_cons]
    show (acc.2 * acc.2) ^ 2 ^ L.length = _
    rw [← sq, ← pow_mul, pow_succ, mul_comm]

theorem ringPsi_eq (v : E) (g : List E) : ringPsi v g = (g.foldl psiF (0, v)).1 := rfl

theorem psi_take_succ (v : E) (g : List E) {b : Nat} (hb : b < g.length) :
    ((g.take (b + 1)).foldl psiF (0, v)).1 =
      ((g.take b).foldl psiF (0, v)).1 + g.getD b 0 * v ^ 2 ^ b := by
  rw [take_succ_getD g hb, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [psiF]
  rw [psiF_foldl_snd, List.length_take, Nat.min_eq_left (by omega)]

/-! ## One term -/

/-- `[rsi] += g_b · [r13]^(2^b)`. -/
def psiStep (gO b : Nat) : Stmt := blk [
  I (.load .r9 (at_ .r13 0)), I (.load .r10 (at_ .r13 8)), I (.movi .rdx (Int64.ofNat b)), esqn,
  I (.load .r11 (at_ .rbp (wdisp (gO + 2 * b)))), I (.load .r12 (at_ .rbp (wdisp (gO + 2 * b + 1)))),
  emul,
  I (.load .rdx (at_ .rsi 0)), I (.xor .r9 .rdx), I (.store (at_ .rsi 0) .r9),
  I (.load .rdx (at_ .rsi 8)), I (.xor .r10 .rdx), I (.store (at_ .rsi 8) .r10)]

theorem toNat_ofNat_small {b : Nat} (hb : b < 2 ^ 62) : (Int64.ofNat b).toUInt64.toNat = b := by
  rw [show (Int64.ofNat b).toUInt64 = b.toUInt64 by rfl, toNat_toUInt64 (by omega)]

/-- The element's state through its terms. -/
structure PsiInv (s0 t : QState) (W p d : UInt64) (v : E) (gO : Nat) (Gl : List E) (b : Nat) :
    Prop where
  rbp : t.reg .rbp = W
  r13 : t.reg .r13 = p
  rsi : t.reg .rsi = d
  r15 : t.reg .r15 = s0.reg .r15
  out : EW t.mem d 0 ((Gl.take b).foldl psiF (0, v)).1
  frame : ∀ a, a ≠ ew d 0 → a ≠ ew d 1 → t.mem a = s0.mem a

/-- **One term.** -/
theorem psiStep_spec {s0 t : QState} {W p d : UInt64} {v : E} {gO b : Nat} {Gl : List E}
    (hI : PsiInv s0 t W p d v gO Gl b) (hb : b < Gl.length) (hb8 : b < 64)
    (hv : EW s0.mem p 0 v) (hG : EArr s0.mem (ew W gO) Gl)
    (hdp : ∀ i < 2, ∀ j < 2, ew d i ≠ ew p j)
    (hdg : ∀ j < 2 * Gl.length, ew d 0 ≠ ew W (gO + j) ∧ ew d 1 ≠ ew W (gO + j)) :
    WP (psiStep gO b) t (fun t' ↦ PsiInv s0 t' W p d v gO Gl (b + 1)) F := by
  obtain ⟨v0, v1⟩ := hv
  obtain ⟨g0, g1⟩ := EArr_word hG hb
  obtain ⟨o0, o1⟩ := hI.out
  have mp : ∀ j < 2, t.mem (ew p j) = s0.mem (ew p j) := fun j hj ↦
    hI.frame _ (Ne.symm (hdp 0 (by omega) j hj)) (Ne.symm (hdp 1 (by omega) j hj))
  have mg : ∀ j < 2 * Gl.length, t.mem (ew W (gO + j)) = s0.mem (ew W (gO + j)) := fun j hj ↦
    hI.frame _ (Ne.symm (hdg j hj).1) (Ne.symm (hdg j hj).2)
  unfold psiStep
  refine WP.load_at (by
    rw [hI.r13, int64Zero_toUInt64, UInt64.add_zero, ← ew_zero p, mp 0 (by omega)]; exact v0) ?_
  refine WP.load_at (by
    rsimp; rw [hI.r13]; show t.mem (ew p 1) = _; rw [mp 1 (by omega)]; exact v1) ?_
  fstep
  refine WP.then (esqn_spec _) fun t1 ⟨e1, _, m1, f1⟩ ↦ ?_
  rsimp at e1 m1
  have r1 : ∀ r ∉ eRegs, t1.reg r = t.reg r := fun r hr ↦ by
    rw [f1 r hr]
    simp only [eRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rsimp
    simp [hr.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]
  have gA : ∀ j, j < 2 * Gl.length → ew W (gO + j) = ew (ew W gO) j := fun j _ ↦ (ew_ew W gO j).symm
  refine wp_load (eval_w (by rw [r1 .rbp (by decide), hI.rbp]) _) (by
    rw [m1, mg _ (by omega), gA _ (by omega)]; exact g0) ?_
  refine wp_load (eval_w (by rsimp; rw [r1 .rbp (by decide), hI.rbp]) _) (by
    rsimp; rw [m1, show gO + 2 * b + 1 = gO + (2 * b + 1) by omega, mg _ (by omega),
      gA _ (by omega)]; exact g1) ?_
  refine WP.then (emul_spec _) fun t2 ⟨e2, m2, f2⟩ ↦ ?_
  rsimp at e2 m2
  have r2 : ∀ r ∉ eRegs, r ≠ .r11 → r ≠ .r12 → t2.reg r = t.reg r := fun r hr h11 h12 ↦ by
    rw [f2 r hr]; rsimp; simp only [h11, h12, ↓reduceIte]; exact r1 r hr
  have d0 : t2.reg .rsi + 0 = ew d 0 := by
    rw [r2 .rsi (by decide) (by decide) (by decide), hI.rsi, UInt64.add_zero, ew_zero]
  have d1 : t2.reg .rsi + 8 = ew d 1 := by
    rw [r2 .rsi (by decide) (by decide) (by decide), hI.rsi]; rfl
  refine WP.load_at (by rw [int64Zero_toUInt64, d0, m2, m1]; exact o0) ?_
  fstep
  refine WP.store_at (by rsimp; rw [d0, m2, m1, o0]; rfl) ?_
  refine WP.load_at (by
    rsimp; rw [d1, QState.setMem_mem, d0, ite_eq_right_iff.mpr (fun h ↦ absurd h
      (ew_ne d (by omega) (by omega) (by omega)))]
    rsimp; rw [m2, m1]
    exact o1) ?_
  fstep
  refine WP.store_at (by
    rsimp; rw [d1]; exact isSome_setMem (by rsimp; rw [m2, m1, o1]; rfl) _ _) ?_
  fdone
  rw [int64Lit_toUInt64, d1, d0]
  have hv : eOf (t2.reg .r9 ^^^ ((((Gl.take b).foldl psiF (0, v)).1).limb 0).lane)
      (t2.reg .r10 ^^^ ((((Gl.take b).foldl psiF (0, v)).1).limb 1).lane) =
      ((Gl.take (b + 1)).foldl psiF (0, v)).1 := by
    rw [eOf_add, e2, e1, eOf_lanes, eOf_lanes, eOf_lanes, toNat_ofNat_small (by omega),
      psi_take_succ v Gl hb]
    ring
  obtain ⟨w0, w1⟩ := eOf_eq_iff.mp hv
  have n01 : ew d 0 ≠ ew d 1 := ew_ne d (by omega) (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, fun a h0 h1 ↦ ?_⟩
  · rsimp; rw [r2 .rbp (by decide) (by decide) (by decide), hI.rbp]
  · rsimp; rw [r2 .r13 (by decide) (by decide) (by decide), hI.r13]
  · rsimp; rw [r2 .rsi (by decide) (by decide) (by decide), hI.rsi]
  · rsimp; rw [r2 .r15 (by decide) (by decide) (by decide), hI.r15]
  · show _ = some _
    simp only [QState.setMem_mem, QState.setReg_mem, Nat.mul_zero, n01, ↓reduceIte]
    rw [w0]
  · show _ = some _
    simp only [QState.setMem_mem, Nat.mul_zero, Nat.zero_add, ↓reduceIte]
    rw [w1]
  · simp only [QState.setMem_mem, QState.setReg_mem, h0, h1, ↓reduceIte, m2, m1]
    exact hI.frame a h0 h1

/-! ## One element -/

/-- `[rsi] := ringPsi [r13] g`. -/
def psiElem (gO : Nat) : Stmt := blk [
  I (.storei (at_ .rsi 0) 0), I (.storei (at_ .rsi 8) 0), blk ((List.range 8).map (psiStep gO))]

/-- **One image.** -/
theorem psiElem_spec {W p d : UInt64} {v : E} {gO : Nat} {Gl : List E}
    (hbp : s.reg .rbp = W) (h13 : s.reg .r13 = p) (hsi : s.reg .rsi = d) (hv : EW s.mem p 0 v)
    (hG : EArr s.mem (ew W gO) Gl) (hGl : Gl.length = 8)
    (hd0 : (s.mem (ew d 0)).isSome) (hd1 : (s.mem (ew d 1)).isSome)
    (hdp : ∀ i < 2, ∀ j < 2, ew d i ≠ ew p j)
    (hdg : ∀ j < 2 * Gl.length, ew d 0 ≠ ew W (gO + j) ∧ ew d 1 ≠ ew W (gO + j)) :
    WP (psiElem gO) s (fun t ↦ PsiInv s t W p d v gO Gl 8) F := by
  have a0 : s.reg .rsi + (0 : Int64).toUInt64 = ew d 0 := by
    rw [hsi, int64Zero_toUInt64, UInt64.add_zero, ew_zero]
  have a1 : s.reg .rsi + 8 = ew d 1 := by rw [hsi]; rfl
  unfold psiElem
  refine wp_storei (by rw [eval_at, a0]) hd0 ?_
  refine wp_storei (by rw [eval_at]; rsimp; rw [a1]) (isSome_setMem hd1 _ _) ?_
  have n01 : ew d 0 ≠ ew d 1 := ew_ne d (by omega) (by omega) (by omega)
  refine WP.then (WP.blk_range (psiStep gO) (fun b t ↦ PsiInv s t W p d v gO Gl b) 8
    (fun b hb t ht ↦ psiStep_spec ht (by omega) (by omega) hv hG hdp hdg) ?_) fun t ht ↦ WP.blk_nil ht
  refine ⟨by rsimp; exact hbp, by rsimp; exact h13, by rsimp; exact hsi, by rsimp, ⟨?_, ?_⟩,
    fun a h0 h1 ↦ ?_⟩
  · simp only [QState.setMem_mem, Nat.mul_zero, n01, ↓reduceIte, List.take_zero, List.foldl_nil,
      lane_zero0, int64Zero_toUInt64]
  · simp only [QState.setMem_mem, Nat.mul_zero, Nat.zero_add, ↓reduceIte, List.take_zero,
      List.foldl_nil, lane_zero1, int64Zero_toUInt64]
  · simp only [QState.setMem_mem, h0, h1, ↓reduceIte]

/-! ## Every image -/

/-- `images := s.map (ringPsi · g)` at work words `iO`. -/
def psiK (sO gO iO : Nat) : Stmt := blk [
  I (.lea .r13 (at_ .rbp (wdisp sO))), I (.lea .rsi (at_ .rbp (wdisp iO))), I (.movi .r15 64),
  .loop (.test false .r15 (.reg .r15)) (blk [psiElem gO,
    I (.addi .r13 16), I (.addi .rsi 16), I (.subi .r15 1)])]

theorem EW_shift {mem : UInt64 → Option UInt64} {W : UInt64} {o k : Nat} {x : E} :
    EW mem (ew W o) k x ↔ EW mem (ew W (o + 2 * k)) 0 x := by
  simp only [EW, ew_ew, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.add_assoc]

theorem ringPsi_take (v : E) {Gl : List E} (h : Gl.length = 8) :
    ((Gl.take 8).foldl psiF (0, v)).1 = ringPsi v Gl := by
  rw [List.take_of_length_le (by omega), ringPsi_eq]

/-- **`psiK` writes the images.** -/
theorem psiK_spec {W : UInt64} {sO gO iO : Nat} {Sl Gl : List E} (hbp : s.reg .rbp = W)
    (hS : EArr s.mem (ew W sO) Sl) (hSl : Sl.length = 64) (hG : EArr s.mem (ew W gO) Gl)
    (hGl : Gl.length = 8) (hdom : ∀ k < 128, (s.mem (ew W (iO + k))).isSome)
    (his : iO + 128 ≤ sO ∨ sO + 128 ≤ iO) (hig : iO + 128 ≤ gO ∨ gO + 16 ≤ iO)
    (hb : sO + 128 < 2 ^ 59 ∧ gO + 16 < 2 ^ 59 ∧ iO + 128 < 2 ^ 59) :
    WP (psiK sO gO iO) s (fun s' ↦ s'.reg .rbp = W ∧
      EArr s'.mem (ew W iO) (Sl.map (ringPsi · Gl)) ∧
      ∀ a, (∀ k < 128, a ≠ ew W (iO + k)) → s'.mem a = s.mem a) F := by
  have outI : ∀ (t : QState), (∀ a, (∀ k < 128, a ≠ ew W (iO + k)) → t.mem a = s.mem a) →
      ∀ j, (j < iO ∨ iO + 128 ≤ j) → j < 2 ^ 60 → t.mem (ew W j) = s.mem (ew W j) :=
    fun t tF j hj hj' ↦ tF _ fun i hi e ↦ by
      have := (ew_inj (b := W) (by omega) (by omega)).mp e; omega
  unfold psiK
  fstep; fstep; fstep
  rw [at_wdisp, at_wdisp]
  rsimp
  rw [hbp]
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ i ≤ 64, t.reg .r13 = ew W (sO + 2 * i) ∧ t.reg .rsi = ew W (iO + 2 * i) ∧
      t.reg .r15 = (64 - i).toUInt64 ∧ t.reg .rbp = W ∧
      (∀ k < i, EW t.mem (ew W iO) k (ringPsi (Sl.getD k 0) Gl)) ∧
      (∀ k < 128, (t.mem (ew W (iO + k))).isSome) ∧
      ∀ a, (∀ k < 128, a ≠ ew W (iO + k)) → t.mem a = s.mem a)
    (fun t ↦ (t.reg .r15).toNat)
  · refine ⟨0, by omega, by rsimp; rw [Nat.mul_zero, Nat.add_zero],
      by rsimp; rw [Nat.mul_zero, Nat.add_zero], by rsimp; rfl, by rsimp; exact hbp,
      fun k hk ↦ absurd hk (Nat.not_lt_zero _), fun k hk ↦ by rsimp; exact hdom k hk,
      fun a _ ↦ by rsimp⟩
  · intro t ⟨i, hi, t13, tsi, t15, tbp, tD, tW, tF⟩ hc
    have hin : i < 64 := cnt_lt (t15 ▸ cond_test_true hc)
    have hv : EW t.mem (ew W (sO + 2 * i)) 0 (Sl.getD i 0) := by
      rw [← EW_shift]
      obtain ⟨v0, v1⟩ := EArr_word hS (k := i) (by omega)
      refine ⟨?_, ?_⟩
      · rw [ew_ew, outI t tF _ (by omega) (by omega), ← ew_ew]; exact v0
      · rw [ew_ew, outI t tF _ (by omega) (by omega), ← ew_ew]; exact v1
    have hGt : EArr t.mem (ew W gO) Gl := EArr_congr (fun j hj ↦ by
      rw [ew_ew, outI t tF _ (by omega) (by omega), ← ew_ew]) hG
    have hd0 : (t.mem (ew (ew W (iO + 2 * i)) 0)).isSome := by
      rw [ew_ew, Nat.add_assoc]; exact tW (2 * i + 0) (by omega)
    have hd1 : (t.mem (ew (ew W (iO + 2 * i)) 1)).isSome := by
      rw [ew_ew, Nat.add_assoc]; exact tW (2 * i + 1) (by omega)
    have hdp : ∀ a < 2, ∀ b < 2, ew (ew W (iO + 2 * i)) a ≠ ew (ew W (sO + 2 * i)) b :=
      fun a ha b hb e ↦ by
        rw [ew_ew, ew_ew] at e
        have := (ew_inj (b := W) (i := iO + 2 * i + a) (j := sO + 2 * i + b) (by omega)
          (by omega)).mp e
        omega
    have hdg : ∀ j < 2 * Gl.length, ew (ew W (iO + 2 * i)) 0 ≠ ew W (gO + j) ∧
        ew (ew W (iO + 2 * i)) 1 ≠ ew W (gO + j) := fun j hj ↦ by
      rw [hGl] at hj
      refine ⟨fun e ↦ ?_, fun e ↦ ?_⟩ <;> rw [ew_ew] at e
      · have := (ew_inj (b := W) (i := iO + 2 * i + 0) (j := gO + j) (by omega) (by omega)).mp e
        omega
      · have := (ew_inj (b := W) (i := iO + 2 * i + 1) (j := gO + j) (by omega) (by omega)).mp e
        omega
    refine WP.then (WP.withDom (psiElem_spec (F := F) (p := ew W (sO + 2 * i))
      (d := ew W (iO + 2 * i)) tbp t13 tsi hv hGt hGl hd0 hd1 hdp hdg))
      fun t1 ⟨h1, d1⟩ ↦ ?_
    fstep; fstep; fstep; fdone
    have keep : ∀ j, j ≠ iO + 2 * i → j ≠ iO + 2 * i + 1 → j < 2 ^ 60 →
        t1.mem (ew W j) = t.mem (ew W j) := fun j h0 h1' hj ↦
      h1.frame _ (fun e ↦ by
          rw [ew_ew] at e; have := (ew_inj (b := W) (by omega) (by omega)).mp e; omega)
        (fun e ↦ by
          rw [ew_ew] at e; have := (ew_inj (b := W) (by omega) (by omega)).mp e; omega)
    refine ⟨⟨i + 1, hin, ?_, ?_, ?_, ?_, fun k hk ↦ ?_, fun k hk ↦ ?_, fun a ha ↦ ?_⟩, ?_⟩
    · rw [h1.r13]; uring
    · rw [h1.rsi]; uring
    · rw [h1.r15, t15, cnt_succ hin]
    · exact h1.rbp
    · rcases Nat.lt_or_ge k i with hki | hki
      · have := tD k hki
        rw [EW_shift] at this ⊢
        obtain ⟨x0, x1⟩ := this
        refine ⟨?_, ?_⟩
        · rw [ew_ew, keep _ (by omega) (by omega) (by omega), ← ew_ew]; exact x0
        · rw [ew_ew, keep _ (by omega) (by omega) (by omega), ← ew_ew]; exact x1
      · obtain rfl : k = i := by omega
        rw [EW_shift, ← ringPsi_take _ hGl]
        exact h1.out
    · rw [d1]; exact tW k hk
    · rw [h1.frame a (fun e ↦ ha (2 * i) (by omega) (by rw [e, ew_ew, Nat.add_zero]))
        (fun e ↦ ha (2 * i + 1) (by omega) (by rw [e, ew_ew, Nat.add_assoc]))]
      exact tF a ha
    · rw [h1.r15, t15, cnt_succ hin]
      exact cnt_dec (by omega) hin
  · intro t ⟨i, hi, _, _, t15, tbp, tD, _, tF⟩ hc
    obtain rfl : i = 64 := cnt_eq (by omega) hi (t15 ▸ cond_test_false hc)
    refine WP.blk_nil ⟨tbp, ?_, tF⟩
    rw [EArr_iff_EW, List.length_map, hSl]
    intro k hk
    have e : (Sl.map (ringPsi · Gl)).getD k 0 = ringPsi (Sl.getD k 0) Gl := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < Sl.length by omega)]
    rw [e]
    exact tD k hk

end NativeVm.Code.Ring
