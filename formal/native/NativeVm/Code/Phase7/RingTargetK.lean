module

public import NativeVm.Code.Phase7.RingPsiK

/-!
# Ring switching's target

`targetK fO iO zO tO`: `ringTarget`'s fold, `Σ_p f_p · frobenius8 (polyEval images z_p) p` for `p`
from `7` down, `z` squared eight times a step from `gen`: `f` at work words `fO`, the images at `iO`
(`64` elements), `z` kept at `zO`, the sum at `tO`; `rbp` the working area. One `tStep p` per
`p`.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wdisp wdisp_toUInt64 wp_load wp_store wp_storei)

variable {s : QState} {F : QState → Prop}

/-! ## The fold -/

/-- `ringTarget`'s step. -/
def tF (images f : List E) (acc : E × E) (p : Nat) : E × E :=
  (acc.1 + f.getD p 0 * frobenius8 (polyEval images (frobenius8 acc.2 1)) p, frobenius8 acc.2 1)

/-- The fold after `j` steps, `p = 7, 6, …`. -/
def tAt (images f : List E) (j : Nat) : E × E :=
  ((List.range j).map (7 - ·)).foldl (tF images f) (0, gen)

theorem tAt_succ (images f : List E) (j : Nat) :
    tAt images f (j + 1) = tF images f (tAt images f j) (7 - j) := by
  rw [tAt, tAt, List.range_succ, List.map_append, List.foldl_append]
  rfl

theorem range_reverse_eq : (List.range ringMapWidth).reverse = (List.range 8).map (7 - ·) := by
  decide

theorem ringTarget_eq (sl f g : List E) :
    ringTarget sl f g = (tAt (sl.map (ringPsi · g)) f 8).1 := by
  rw [ringTarget, range_reverse_eq]
  rfl

/-! ## One step -/

/-- `z := z^(2^8)`; the sum `+= f_p · (polyEval images z)^(2^(8p))`. -/
def tStep (fO iO zO tO p : Nat) : Stmt := blk [
  I (.load .r9 (at_ .rbp (wdisp zO))), I (.load .r10 (at_ .rbp (wdisp (zO + 1)))),
  I (.movi .rdx 8), esqn,
  I (.store (at_ .rbp (wdisp zO)) .r9), I (.store (at_ .rbp (wdisp (zO + 1))) .r10),
  I (.mov .r11 .r9), I (.mov .r12 .r10), I (.lea .r13 (at_ .rbp (wdisp iO))), I (.movi .r15 64),
  epolyEval,
  I (.movi .rdx (Int64.ofNat (8 * p))), esqn,
  I (.load .r11 (at_ .rbp (wdisp (fO + 2 * p)))), I (.load .r12 (at_ .rbp (wdisp (fO + 2 * p + 1)))),
  emul,
  I (.load .rdx (at_ .rbp (wdisp tO))), I (.xor .r9 .rdx), I (.store (at_ .rbp (wdisp tO)) .r9),
  I (.load .rdx (at_ .rbp (wdisp (tO + 1)))), I (.xor .r10 .rdx),
  I (.store (at_ .rbp (wdisp (tO + 1))) .r10)]

/-- The step's state: `z` and the sum, everything else as at the start. -/
structure TInv (s0 t : QState) (W : UInt64) (zO tO : Nat) (acc : E × E) : Prop where
  rbp : t.reg .rbp = W
  z : EW t.mem (ew W zO) 0 acc.2
  sum : EW t.mem (ew W tO) 0 acc.1
  frame : ∀ a, a ≠ ew W zO → a ≠ ew W (zO + 1) → a ≠ ew W tO → a ≠ ew W (tO + 1) →
    t.mem a = s0.mem a

theorem ew_EW0 {mem : UInt64 → Option UInt64} {W : UInt64} {o : Nat} {x : E} :
    EW mem (ew W o) 0 x ↔ mem (ew W o) = some (x.limb 0).lane ∧
      mem (ew W (o + 1)) = some (x.limb 1).lane := by
  simp only [EW, ew_ew, Nat.mul_zero, Nat.add_zero, Nat.zero_add]

theorem frob1 (x : E) : x ^ 2 ^ (8 : UInt64).toNat = frobenius8 x 1 := by
  rw [frobenius8, ringMapWidth]
  rfl

/-- **One step.** -/
theorem tStep_spec {s0 t : QState} {W : UInt64} {fO iO zO tO p : Nat} {Fl Il : List E}
    {acc : E × E} (hI : TInv s0 t W zO tO acc) (hp : p < 8)
    (hF : EArr s0.mem (ew W fO) Fl) (hFl : Fl.length = 8) (hIm : EArr s0.mem (ew W iO) Il)
    (hIl : Il.length = 64)
    (hzt : zO + 2 ≤ tO ∨ tO + 2 ≤ zO) (hzf : zO + 2 ≤ fO ∨ fO + 16 ≤ zO)
    (hzi : zO + 2 ≤ iO ∨ iO + 128 ≤ zO) (htf : tO + 2 ≤ fO ∨ fO + 16 ≤ tO)
    (hti : tO + 2 ≤ iO ∨ iO + 128 ≤ tO)
    (hb : fO + 16 < 2 ^ 59 ∧ iO + 128 < 2 ^ 59 ∧ zO + 2 < 2 ^ 59 ∧ tO + 2 < 2 ^ 59) :
    WP (tStep fO iO zO tO p) t (fun t' ↦ TInv s0 t' W zO tO (tF Il Fl acc p)) F := by
  have out : ∀ j, (j < zO ∨ zO + 2 ≤ j) → (j < tO ∨ tO + 2 ≤ j) → j < 2 ^ 60 →
      t.mem (ew W j) = s0.mem (ew W j) := fun j h1 h2 h3 ↦
    hI.frame _ (fun e ↦ by have := (ew_inj (b := W) (by omega) (by omega)).mp e; omega)
      (fun e ↦ by have := (ew_inj (b := W) (by omega) (by omega)).mp e; omega)
      (fun e ↦ by have := (ew_inj (b := W) (by omega) (by omega)).mp e; omega)
      (fun e ↦ by have := (ew_inj (b := W) (by omega) (by omega)).mp e; omega)
  obtain ⟨z0, z1⟩ := ew_EW0.mp hI.z
  obtain ⟨u0, u1⟩ := ew_EW0.mp hI.sum
  have hIt : EArr t.mem (ew W iO) Il := EArr_congr (fun j hj ↦ by
    rw [ew_ew, out _ (by omega) (by omega) (by omega), ← ew_ew]) hIm
  obtain ⟨f0, f1⟩ := EArr_word hF (k := p) (by omega)
  unfold tStep
  refine wp_load (eval_w hI.rbp _) z0 ?_
  refine wp_load (eval_w (by rsimp; exact hI.rbp) _) (by rsimp; exact z1) ?_
  fstep
  refine WP.then (esqn_spec _) fun t1 ⟨e1, _, m1, f1'⟩ ↦ ?_
  rsimp at e1 m1
  have r1 : ∀ r ∉ eRegs, t1.reg r = t.reg r := fun r hr ↦ by
    rw [f1' r hr]
    simp only [eRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rsimp
    simp [hr.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]
  have bp1 : t1.reg .rbp = W := by rw [r1 .rbp (by decide), hI.rbp]
  have hz : eOf (t1.reg .r9) (t1.reg .r10) = frobenius8 acc.2 1 := by
    rw [e1, eOf_lanes, frob1]
  obtain ⟨y0, y1⟩ := eOf_eq_iff.mp hz
  have nz : zO ≠ zO + 1 := by omega
  have nzt0 : tO ≠ zO := by omega
  have nzt1 : tO ≠ zO + 1 := by omega
  have nzt2 : tO + 1 ≠ zO := by omega
  have nzt3 : tO + 1 ≠ zO + 1 := by omega
  have nt : tO + 1 ≠ tO := by omega
  refine wp_store (eval_w bp1 _) (by rw [m1, z0]; rfl) ?_
  refine wp_store (eval_w (by rsimp; exact bp1) _)
    (isSome_setMem (by rw [m1, z1]; rfl) _ _) ?_
  fstep; fstep; fstep; fstep
  rw [at_wdisp]
  rsimp
  rw [bp1]
  -- the memory after the two stores of `z`
  have hIt1 : EArr ((t1.setMem (ew W zO) (t1.reg .r9)).setMem (ew W (zO + 1)) (t1.reg .r10)).mem
      (ew W iO) Il := EArr_congr (fun j hj ↦ by
        rw [hIl] at hj
        rw [ew_ew, setMem_ew _ _ _ _ _ (by omega) (by omega),
          setMem_ew _ _ _ _ _ (by omega) (by omega), m1]
        simp only [show iO + j ≠ zO + 1 by omega, show iO + j ≠ zO by omega, ↓reduceIte]) hIt
  refine WP.then (epolyEval_spec (F := F) (cs := Il) (by rsimp; exact hIt1)
    (by rsimp; rw [hIl]; rfl) (by omega)) fun t2 ⟨e2, m2, f2⟩ ↦ ?_
  rsimp at e2 m2
  rw [y0, y1, eOf_lanes] at e2
  have bp2 : t2.reg .rbp = W := by rw [f2 .rbp (by decide)]; rsimp; exact bp1
  fstep
  refine WP.then (esqn_spec _) fun t3 ⟨e3, _, m3, f3⟩ ↦ ?_
  rsimp at e3 m3
  rw [e2, toNat_ofNat8 (by omega), esqn_frob] at e3
  have bp3 : t3.reg .rbp = W := by rw [f3 .rbp (by decide)]; rsimp; exact bp2
  have memF : ∀ j, (j < zO ∨ zO + 2 ≤ j) → (j < tO ∨ tO + 2 ≤ j) → j < 2 ^ 60 →
      t3.mem (ew W j) = s0.mem (ew W j) := fun j h1 h2 h3 ↦ by
    rw [m3, m2, setMem_ew _ _ _ _ _ (by omega) (by omega),
      setMem_ew _ _ _ _ _ (by omega) (by omega), m1]
    simp only [show j ≠ zO + 1 by omega, show j ≠ zO by omega, ↓reduceIte]
    exact out j h1 h2 h3
  refine wp_load (eval_w bp3 _) (by
    rw [memF _ (by omega) (by omega) (by omega), ← ew_ew]; exact f0) ?_
  refine wp_load (eval_w (by rsimp; exact bp3) _) (by
    rsimp; rw [memF _ (by omega) (by omega) (by omega),
      show fO + 2 * p + 1 = fO + (2 * p + 1) by omega, ← ew_ew]; exact f1) ?_
  refine WP.then (emul_spec _) fun t4 ⟨e4, m4, f4⟩ ↦ ?_
  rsimp at e4 m4
  rw [e3, eOf_lanes] at e4
  have bp4 : t4.reg .rbp = W := by rw [f4 .rbp (by decide)]; rsimp; exact bp3
  have memT : ∀ j, (j = tO ∨ j = tO + 1) → t4.mem (ew W j) = t.mem (ew W j) := fun j hj ↦ by
    rw [m4, m3, m2, setMem_ew _ _ _ _ _ (by omega) (by omega),
      setMem_ew _ _ _ _ _ (by omega) (by omega), m1]
    simp only [show j ≠ zO + 1 by omega, show j ≠ zO by omega, ↓reduceIte]
  refine wp_load (eval_w bp4 _) (by rw [memT _ (.inl rfl)]; exact u0) ?_
  fstep
  refine wp_store (eval_w (by rsimp; exact bp4) _) (by rsimp; rw [memT _ (.inl rfl), u0]; rfl) ?_
  refine wp_load (eval_w (by rsimp; exact bp4) _) (by
    rsimp; rw [setMem_ew _ _ _ _ _ (by omega) (by omega)]
    simp only [nt, ↓reduceIte]
    rsimp; rw [memT _ (.inr rfl)]; exact u1) ?_
  fstep
  refine wp_store (eval_w (by rsimp; exact bp4) _) (by
    rsimp; exact isSome_setMem (by rsimp; rw [memT _ (.inr rfl), u1]; rfl) _ _) ?_
  fdone
  have hs : eOf (t4.reg .r9 ^^^ (acc.1.limb 0).lane) (t4.reg .r10 ^^^ (acc.1.limb 1).lane) =
      (tF Il Fl acc p).1 := by
    rw [eOf_add, e4, eOf_lanes, tF]
    simp only [List.getD_eq_getElem?_getD]
    ring
  obtain ⟨w0, w1⟩ := eOf_eq_iff.mp hs
  refine ⟨by rsimp; exact bp4, ew_EW0.mpr ⟨?_, ?_⟩, ew_EW0.mpr ⟨?_, ?_⟩, fun a ha hb' hc hd ↦ ?_⟩
  · simp (disch := omega) only [setMem_ew, QState.setReg_mem, m4, m3, m2, Ne.symm nzt0,
      Ne.symm nzt2, nz, ↓reduceIte, tF, y0]
  · simp (disch := omega) only [setMem_ew, QState.setReg_mem, m4, m3, m2, Ne.symm nzt1,
      Ne.symm nzt3, ↓reduceIte, tF, y1]
  · simp (disch := omega) only [setMem_ew, QState.setReg_mem, Ne.symm nt, ↓reduceIte, w0]
  · simp (disch := omega) only [setMem_ew, ↓reduceIte, w1]
  · simp only [QState.setMem_mem, QState.setReg_mem, hd, hc, ↓reduceIte, m4, m3, m2, m1, ha, hb']
    exact hI.frame a ha hb' hc hd

/-! ## The target -/

/-- `ringTarget`'s fold, the sum at work words `tO`. -/
def targetK (fO iO zO tO : Nat) : Stmt := blk [
  I (.storei (at_ .rbp (wdisp zO)) 2), I (.storei (at_ .rbp (wdisp (zO + 1))) 0),
  I (.storei (at_ .rbp (wdisp tO)) 0), I (.storei (at_ .rbp (wdisp (tO + 1))) 0),
  blk ((List.range 8).map fun j ↦ tStep fO iO zO tO (7 - j))]

theorem gen_lanes : (gen.limb 0).lane = 2 ∧ (gen.limb 1).lane = 0 := by
  rw [← NativeVm.Equiv.toE_gen, show NativeVm.Model.gen.toE = eOf 2 0 from rfl, limb0_eOf,
    limb1_eOf]
  exact ⟨rfl, rfl⟩

/-- **`targetK` computes `ringTarget`'s fold.** -/
theorem targetK_spec {W : UInt64} {fO iO zO tO : Nat} {Fl Il : List E} (hbp : s.reg .rbp = W)
    (hF : EArr s.mem (ew W fO) Fl) (hFl : Fl.length = 8) (hIm : EArr s.mem (ew W iO) Il)
    (hIl : Il.length = 64)
    (hz0 : (s.mem (ew W zO)).isSome) (hz1 : (s.mem (ew W (zO + 1))).isSome)
    (ht0 : (s.mem (ew W tO)).isSome) (ht1 : (s.mem (ew W (tO + 1))).isSome)
    (hzt : zO + 2 ≤ tO ∨ tO + 2 ≤ zO) (hzf : zO + 2 ≤ fO ∨ fO + 16 ≤ zO)
    (hzi : zO + 2 ≤ iO ∨ iO + 128 ≤ zO) (htf : tO + 2 ≤ fO ∨ fO + 16 ≤ tO)
    (hti : tO + 2 ≤ iO ∨ iO + 128 ≤ tO)
    (hb : fO + 16 < 2 ^ 59 ∧ iO + 128 < 2 ^ 59 ∧ zO + 2 < 2 ^ 59 ∧ tO + 2 < 2 ^ 59) :
    WP (targetK fO iO zO tO) s (fun s' ↦ TInv s s' W zO tO (tAt Il Fl 8)) F := by
  unfold targetK
  refine wp_storei (eval_w hbp _) hz0 ?_
  refine wp_storei (eval_w (by rsimp; exact hbp) _) (isSome_setMem hz1 _ _) ?_
  refine wp_storei (eval_w (by rsimp; exact hbp) _) (isSome_setMem (isSome_setMem ht0 _ _) _ _) ?_
  refine wp_storei (eval_w (by rsimp; exact hbp) _)
    (isSome_setMem (isSome_setMem (isSome_setMem ht1 _ _) _ _) _ _) ?_
  have hstep : ∀ j < 8, ∀ t, TInv s t W zO tO (tAt Il Fl j) →
      WP (tStep fO iO zO tO (7 - j)) t (fun t' ↦ TInv s t' W zO tO (tAt Il Fl (j + 1))) F := by
    intro j hj t ht
    rw [tAt_succ]
    exact tStep_spec ht (by omega) hF hFl hIm hIl hzt hzf hzi htf hti hb
  refine WP.then (WP.blk_range _ (fun j t ↦ TInv s t W zO tO (tAt Il Fl j)) 8 hstep ?_)
    fun t ht ↦ WP.blk_nil ht
  obtain ⟨g0, g1⟩ := gen_lanes
  refine ⟨by rsimp; exact hbp, ew_EW0.mpr ⟨?_, ?_⟩, ew_EW0.mpr ⟨?_, ?_⟩, fun a ha hb' hc hd ↦ ?_⟩
  · simp (disch := omega) only [setMem_ew, tAt, List.range_zero, List.map_nil, List.foldl_nil,
      show zO ≠ tO + 1 by omega, show zO ≠ tO by omega, show zO ≠ zO + 1 by omega, ↓reduceIte, g0]
    rfl
  · simp (disch := omega) only [setMem_ew, tAt, List.range_zero, List.map_nil, List.foldl_nil,
      show zO + 1 ≠ tO + 1 by omega, show zO + 1 ≠ tO by omega, ↓reduceIte, g1]
    rfl
  · simp (disch := omega) only [setMem_ew, tAt, List.range_zero, List.map_nil, List.foldl_nil,
      show tO ≠ tO + 1 by omega, ↓reduceIte, lane_zero0]
    rfl
  · simp (disch := omega) only [setMem_ew, tAt, List.range_zero, List.map_nil, List.foldl_nil,
      ↓reduceIte, lane_zero1]
    rfl
  · simp only [QState.setMem_mem, ha, hb', hc, hd, ↓reduceIte]

end NativeVm.Code.Ring
