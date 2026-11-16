module

public import Quantum.Sphincs.Hybrid.RStage
public import Quantum.Sphincs.Assembly.Template

@[expose] public section

/-!
# The high-bits fix-up stage

The staged exchanges move whole `1088`-bit `h`-values into slots, while the template's `H_msg`
correction `cor256` only fixes the bits below `256`. A fix-up stage exchanges back the bits from
`256` on.

* `hiMix w s`: the bits of `w` below `256`, those of `s` from `256` on (`out256_hiMix`,
  `hiEq_hiMix`). `HiEq x y`: equal bits from `256` on (`HiEq.refl`, `HiEq.symm`, `HiEq.trans`,
  `hiEq_add`, `hiEq_cor128`); `cor256_eq_of_hiEq`: `cor256` restores the bits below `256`.
* `hiStageOn F pos sh hpos`: an involutive fiberwise stage over abstract `W`, `J`; for the labels
  `a` with `F w lo a` (distinct positions), the high bits of the slot `u a` and of the cell
  `h (pos w lo a)` are exchanged, shifted by `sh w lo a`. The predicate, positions and shifts may
  read the low parts `lo` of the slots, which the stage keeps (`hiStageOn_spec`).
* `setHC y h hc`: path-stage coordinates with `h` and the `h`-slots replaced; `pStageK` and
  `pStageK'` commute with it (`pStageK_setHC`, `pStageK'_setHC`) and `pStageHOn` is one
  (`pStageHOn_exists_setHC`).
-/

open Quantum Quantum.Sponge
open HashSig (Digest HashOutput)
open Quantum.Xmss (X Z out256 bitOf bitOf_xor bitOf_decide_eq_one getLsbD_out256)
open Quantum.Xmss.Assembly (embed128)
open Quantum.Sphincs.Hybrid (PSt pStageK pStageK' pStageHOn pStageHOn_spec pStages pCellH pCellK)
open Quantum.Xmss.Hybrid (IsFirst isFirst_inj)

namespace Quantum.Sphincs.Assembly

/-! ## Low and high bits -/

/-- The bits of `w` below `256` and those of `s` from `256` on. -/
def hiMix (w s : X) : X := fun j ↦ if j.val < 256 then w j else s j

/-- Equal bits from `256` on. -/
def HiEq (x y : X) : Prop := ∀ j : Fin 1088, 256 ≤ j.val → x j = y j

theorem out256_hiMix (w s : X) : out256 (hiMix w s) = out256 w := by
  unfold out256
  exact congrArg _ (funext fun j ↦ ite_eq_left j.isLt)

theorem hiEq_hiMix (w s : X) : HiEq (hiMix w s) s :=
  fun _ hj ↦ ite_eq_right (Nat.not_lt.2 hj)

theorem HiEq.refl (x : X) : HiEq x x :=
  fun _ _ ↦ rfl

theorem HiEq.symm {x y : X} (h : HiEq x y) : HiEq y x :=
  fun j hj ↦ (h j hj).symm

theorem HiEq.trans {x y z : X} (h₁ : HiEq x y) (h₂ : HiEq y z) : HiEq x z :=
  fun j hj ↦ (h₁ j hj).trans (h₂ j hj)

theorem hiEq_add {a b c d : X} (h₁ : HiEq a b) (h₂ : HiEq c d) : HiEq (a + c) (b + d) :=
  fun j hj ↦ by rw [Pi.add_apply, Pi.add_apply, h₁ j hj, h₂ j hj]

theorem hiEq_cor128 (d : Digest) (r w : X) : HiEq (cor128 d r w) w := fun j hj ↦ by
  simp only [cor128, Pi.add_apply, embed128, ite_eq_right (show ¬j.val < 128 by omega), add_zero]

/-- `cor256` restores the bits below `256` of a value with the same bits from `256` on. -/
theorem cor256_eq_of_hiEq {y : HashOutput} {r w w₀ : X} (hw : HiEq w w₀)
    (hy : y = out256 (r + w₀)) : cor256 y r w = w₀ := by
  subst hy
  funext j
  by_cases hj : j.val < 256
  · have h3 : ∀ a b c : ZMod 2, a + (b + c + (b + a)) = c := by decide
    simp only [cor256, Pi.add_apply, embed256, ite_eq_left hj, BitVec.getLsbD_xor, bitOf_xor,
      getLsbD_out256 _ _ hj, Fin.eta, bitOf_decide_eq_one]
    exact h3 _ _ _
  · simp only [cor256, Pi.add_apply, embed256, ite_eq_right hj, add_zero]
    exact hw j (by omega)

/-- Exchanging the high bits twice, with the same shift, gives back the value. -/
theorem hiMix_hiMix_add (x y s : X) : hiMix (hiMix x (y + s)) (hiMix y (x + s) + s) = x := by
  have h2 : ∀ a b : ZMod 2, a + b + b = a := by decide
  funext j
  by_cases hj : j.val < 256
  · simp only [hiMix, ite_eq_left hj]
  · simp only [hiMix, ite_eq_right hj, Pi.add_apply, h2]

/-! ## The fix-up stage, over abstract types -/

section hiStage

variable {W J : Type*} (F : W → (J → HashOutput) → J → Prop)
  (pos : W → (J → HashOutput) → J → Z) (sh : W → (J → HashOutput) → J → X)

open scoped Classical in
/-- The fix-up stage's cells: a cell of a label in `F` exchanges its high bits with the label's
slot. -/
noncomputable def hiStageH (h : Z → X) (u : J → X) (lo : J → HashOutput) (w : W) (z : Z) : X :=
  if hz : ∃ a, F w lo a ∧ pos w lo a = z then
    hiMix (h z) (u hz.choose + sh w lo hz.choose)
  else h z

open scoped Classical in
/-- The fix-up stage's slots: the slot of a label in `F` exchanges its high bits with its cell. -/
noncomputable def hiStageU (h : Z → X) (u : J → X) (lo : J → HashOutput) (w : W) (a : J) : X :=
  if F w lo a then hiMix (u a) (h (pos w lo a) + sh w lo a) else u a

theorem out256_hiStageU (h : Z → X) (u : J → X) (lo : J → HashOutput) (w : W) (a : J) :
    out256 (hiStageU F pos sh h u lo w a) = out256 (u a) := by
  by_cases ha : F w lo a
  · rw [hiStageU, ite_eq_left ha, out256_hiMix]
  · rw [hiStageU, ite_eq_right ha]

variable {F pos} in
theorem hiStageH_pos (hpos : ∀ w lo a b, F w lo a → F w lo b → pos w lo a = pos w lo b → a = b)
    (h : Z → X) (u : J → X) (lo : J → HashOutput) (w : W) {a : J} (ha : F w lo a) :
    hiStageH F pos sh h u lo w (pos w lo a) = hiMix (h (pos w lo a)) (u a + sh w lo a) := by
  have hz : ∃ b, F w lo b ∧ pos w lo b = pos w lo a := ⟨a, ha, rfl⟩
  have hc : hz.choose = a := hpos _ _ _ _ hz.choose_spec.1 ha hz.choose_spec.2
  rw [hiStageH, dite_eq_left hz, hc]

theorem hiStageH_of_forall (h : Z → X) (u : J → X) (lo : J → HashOutput) (w : W) {z : Z}
    (hz : ∀ a, F w lo a → pos w lo a ≠ z) : hiStageH F pos sh h u lo w z = h z := by
  rw [hiStageH, dite_eq_right]
  rintro ⟨a, ha, rfl⟩
  exact hz a ha rfl

/-- The fix-up stage as a map. -/
noncomputable def hiStageFun (t : ((Z → X) × (J → X)) × W) : ((Z → X) × (J → X)) × W :=
  ((hiStageH F pos sh t.1.1 t.1.2 (fun b ↦ out256 (t.1.2 b)) t.2,
    hiStageU F pos sh t.1.1 t.1.2 (fun b ↦ out256 (t.1.2 b)) t.2), t.2)

variable {F pos} in
theorem hiStageFun_involutive
    (hpos : ∀ w lo a b, F w lo a → F w lo b → pos w lo a = pos w lo b → a = b) :
    Function.Involutive (hiStageFun F pos sh) := by
  rintro ⟨⟨h, u⟩, w⟩
  have hlo : (fun b ↦ out256 (hiStageU F pos sh h u (fun b ↦ out256 (u b)) w b)) =
      fun b ↦ out256 (u b) :=
    funext fun b ↦ out256_hiStageU F pos sh h u _ w b
  simp only [hiStageFun]
  rw [hlo]
  refine Prod.ext (Prod.ext (funext fun z ↦ ?_) (funext fun a ↦ ?_)) rfl
  · by_cases hz : ∃ a, F w (fun b ↦ out256 (u b)) a ∧ pos w (fun b ↦ out256 (u b)) a = z
    · obtain ⟨a, ha, rfl⟩ := hz
      dsimp only
      rw [hiStageH_pos sh hpos _ _ _ w ha, hiStageH_pos sh hpos _ _ _ w ha, hiStageU,
        ite_eq_left ha, hiMix_hiMix_add]
    · have hz' : ∀ a, F w (fun b ↦ out256 (u b)) a → pos w (fun b ↦ out256 (u b)) a ≠ z :=
        fun a ha he ↦ hz ⟨a, ha, he⟩
      dsimp only
      rw [hiStageH_of_forall F pos sh _ _ _ w hz', hiStageH_of_forall F pos sh _ _ _ w hz']
  · by_cases ha : F w (fun b ↦ out256 (u b)) a
    · dsimp only
      rw [hiStageU, ite_eq_left ha, hiStageH_pos sh hpos _ _ _ w ha, hiStageU, ite_eq_left ha,
        hiMix_hiMix_add]
    · dsimp only
      rw [hiStageU, ite_eq_right ha, hiStageU, ite_eq_right ha]

/-- **The fix-up stage**: for the data `w` and the low parts `lo` of the slots, which it keeps, the
slot of each label `a` with `F w lo a` (distinct positions) and the cell `pos w lo a` exchange
their bits from `256` on, shifted by `sh w lo a`. It is its own inverse. -/
noncomputable def hiStageOn
    (hpos : ∀ w lo a b, F w lo a → F w lo b → pos w lo a = pos w lo b → a = b) :
    ((Z → X) × (J → X)) × W ≃ ((Z → X) × (J → X)) × W :=
  Function.Involutive.toPerm _ (hiStageFun_involutive sh hpos)

/-- **The fix-up stage**: it keeps the data and the low parts of the slots; a slot of a label in
`F` and its cell exchange their high bits (shifted); the other slots, and the cells of no label in
`F`, keep their values. -/
theorem hiStageOn_spec
    (hpos : ∀ w lo a b, F w lo a → F w lo b → pos w lo a = pos w lo b → a = b)
    (h : Z → X) (u : J → X) (w : W) :
    ∃ (h' : Z → X) (u' : J → X), hiStageOn F pos sh hpos ((h, u), w) = ((h', u'), w) ∧
      (∀ a, out256 (u' a) = out256 (u a)) ∧
      (∀ a, F w (fun b ↦ out256 (u b)) a →
        u' a = hiMix (u a) (h (pos w (fun b ↦ out256 (u b)) a) + sh w (fun b ↦ out256 (u b)) a) ∧
        h' (pos w (fun b ↦ out256 (u b)) a) =
          hiMix (h (pos w (fun b ↦ out256 (u b)) a)) (u a + sh w (fun b ↦ out256 (u b)) a)) ∧
      (∀ a, ¬F w (fun b ↦ out256 (u b)) a → u' a = u a) ∧
      ∀ z, (∀ a, F w (fun b ↦ out256 (u b)) a → pos w (fun b ↦ out256 (u b)) a ≠ z) →
        h' z = h z :=
  ⟨hiStageH F pos sh h u (fun b ↦ out256 (u b)) w, hiStageU F pos sh h u (fun b ↦ out256 (u b)) w,
    rfl, fun a ↦ out256_hiStageU F pos sh h u _ w a,
    fun a ha ↦ ⟨by rw [hiStageU, ite_eq_left ha], hiStageH_pos sh hpos h u _ w ha⟩,
    fun a ha ↦ by rw [hiStageU, ite_eq_right ha],
    fun _ hz ↦ hiStageH_of_forall F pos sh h u _ w hz⟩

end hiStage

/-! ## Replacing `h` and the `h`-slots of path-stage coordinates -/

section setHC

variable {E F J : Type}

/-- Path-stage coordinates with `h` and the `h`-slots replaced. -/
def setHC (y : PSt E F J) (h : Z → X) (hc : J → X) : PSt E F J :=
  (((((h, y.1.1.1.1.2), y.1.1.1.2), y.1.1.2), (y.1.2.1, y.1.2.2.1, hc)), y.2)

@[simp] theorem setHC_h (y : PSt E F J) (h : Z → X) (hc : J → X) :
    (setHC y h hc).1.1.1.1.1 = h :=
  rfl

@[simp] theorem setHC_kk' (y : PSt E F J) (h : Z → X) (hc : J → X) :
    (setHC y h hc).1.1.1.1.2 = y.1.1.1.1.2 :=
  rfl

@[simp] theorem setHC_perm (y : PSt E F J) (h : Z → X) (hc : J → X) :
    (setHC y h hc).1.1.1.2 = y.1.1.1.2 :=
  rfl

@[simp] theorem setHC_e (y : PSt E F J) (h : Z → X) (hc : J → X) :
    (setHC y h hc).1.1.2 = y.1.1.2 :=
  rfl

@[simp] theorem setHC_kc (y : PSt E F J) (h : Z → X) (hc : J → X) :
    (setHC y h hc).1.2.1 = y.1.2.1 :=
  rfl

@[simp] theorem setHC_k'c (y : PSt E F J) (h : Z → X) (hc : J → X) :
    (setHC y h hc).1.2.2.1 = y.1.2.2.1 :=
  rfl

@[simp] theorem setHC_hc (y : PSt E F J) (h : Z → X) (hc : J → X) :
    (setHC y h hc).1.2.2.2 = hc :=
  rfl

@[simp] theorem setHC_f (y : PSt E F J) (h : Z → X) (hc : J → X) : (setHC y h hc).2 = y.2 :=
  rfl

@[simp] theorem setHC_setHC (y : PSt E F J) (h h' : Z → X) (hc hc' : J → X) :
    setHC (setHC y h hc) h' hc' = setHC y h' hc' :=
  rfl

@[simp] theorem setHC_self (y : PSt E F J) : setHC y y.1.1.1.1.1 y.1.2.2.2 = y :=
  rfl

variable (c : E → F → J → X)

/-- The `k`-stage keeps `h` and the `h`-slots, and does not read them. -/
theorem pStageK_setHC (y : PSt E F J) (h : Z → X) (hc : J → X) :
    pStageK c (setHC y h hc) = setHC (pStageK c y) h hc :=
  rfl

/-- The `k'`-stage keeps `h` and the `h`-slots, and does not read them. -/
theorem pStageK'_setHC (y : PSt E F J) (h : Z → X) (hc : J → X) :
    pStageK' c (setHC y h hc) = setHC (pStageK' c y) h hc :=
  rfl

/-- The partial `h`-stage only changes `h` and the `h`-slots. -/
theorem pStageHOn_exists_setHC (ord : J ↪ ℕ) (y : PSt E F J) :
    ∃ (h : Z → X) (hc : J → X), pStageHOn c ord y = setHC y h hc := by
  obtain ⟨⟨⟨⟨⟨h, k, k'⟩, π⟩, e⟩, kc, k'c, hc⟩, f⟩ := y
  obtain ⟨h₂, hc₂, eH, -⟩ := pStageHOn_spec c ord h k k' π e kc k'c hc f
  exact ⟨h₂, hc₂, eH⟩

end setHC

/-! ## The path stages with the fix-up and the undoing of the `k`- and `k'`-stages -/

section pFull

variable {E F J : Type} (c : E → F → J → X) (ord : J ↪ ℕ)

/-- The data the fix-up keeps: `k`, `k'`, `π`, `E`, the `k`- and `k'`-coins, and `F`. -/
abbrev PW (E F J : Type) : Type :=
  (X → Z) × (X → Z) × Equiv.Perm (X × Z) × E × (J → Z) × (J → Z) × F

/-- The fix-up's view: `h` with the `h`-slots, and the rest. -/
def pView : PSt E F J ≃ ((Z → X) × (J → X)) × PW E F J where
  toFun y := ((y.1.1.1.1.1, y.1.2.2.2),
    (y.1.1.1.1.2.1, y.1.1.1.1.2.2, y.1.1.1.2, y.1.1.2, y.1.2.1, y.1.2.2.1, y.2))
  invFun p := (((((p.1.1, p.2.1, p.2.2.1), p.2.2.2.1), p.2.2.2.2.1),
    (p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.1.2)), p.2.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The labels' capacities from the kept data (`pCellH`). -/
def pPosW (w : PW E F J) (_ : J → HashOutput) (a : J) : Z :=
  (w.2.2.1 (c w.2.2.2.1 w.2.2.2.2.2.2 a, w.2.2.2.2.1 a)).2 + w.2.2.2.2.2.1 a

/-- The labels' rates from the kept data. -/
def pShW (w : PW E F J) (_ : J → HashOutput) (a : J) : X :=
  (w.2.2.1 (c w.2.2.2.1 w.2.2.2.2.2.2 a, w.2.2.2.2.1 a)).1

/-- The first labels. -/
def pFW (w : PW E F J) (lo : J → HashOutput) (a : J) : Prop :=
  IsFirst ord (pPosW c w lo) a

theorem pFW_inj (w : PW E F J) (lo : J → HashOutput) (a b : J) (ha : pFW c ord w lo a)
    (hb : pFW c ord w lo b) (h : pPosW c w lo a = pPosW c w lo b) : a = b :=
  isFirst_inj ord (pPosW c w lo) a b ha hb h

/-- **The fix-up**: at the first labels, the bits of `h` from `256` on are given back. -/
noncomputable def pHiE : PSt E F J ≃ PSt E F J :=
  pView.trans ((hiStageOn (pFW c ord) (pPosW c) (pShW c) (pFW_inj c ord)).trans pView.symm)

/-- **The undoing of the `k`- and `k'`-stages.** -/
noncomputable def pUndo : PSt E F J ≃ PSt E F J :=
  ((pStageK c).trans (pStageK' c)).symm

/-- **The full stage**: the path stages, the fix-up, the undoing of the `k`- and `k'`-stages. Only
`h` and the `h`-slots change. -/
noncomputable def pFull : PSt E F J ≃ PSt E F J :=
  (pStages c ord).trans ((pHiE c ord).trans (pUndo c))

/-- The labels' rates read off the coordinates. -/
def pShY (y : PSt E F J) (a : J) : X :=
  (y.1.1.1.2 (pCellK c y a, y.1.2.1 a)).1

/-- **The fix-up**: `h` and the slots replaced; the slots keep their first `256` bits; at the
first labels' capacities `h` takes the bits from `256` on of the slot plus the rate. -/
theorem pHiE_spec (y : PSt E F J) :
    ∃ (h' : Z → X) (hc' : J → X), pHiE c ord y = setHC y h' hc' ∧
      (∀ a, out256 (hc' a) = out256 (y.1.2.2.2 a)) ∧
      (∀ a, IsFirst ord (pCellH c y) a →
        h' (pCellH c y a) = hiMix (y.1.1.1.1.1 (pCellH c y a)) (y.1.2.2.2 a + pShY c y a)) ∧
      ∀ z, (∀ a, IsFirst ord (pCellH c y) a → pCellH c y a ≠ z) → h' z = y.1.1.1.1.1 z := by
  obtain ⟨h', u', he, h1, h2, -, h4⟩ := hiStageOn_spec (pFW c ord) (pPosW c) (pShW c)
    (pFW_inj c ord) y.1.1.1.1.1 y.1.2.2.2 (pView y).2
  refine ⟨h', u', ?_, h1, fun a ha ↦ (h2 a ha).2, h4⟩
  show pView.symm (hiStageOn (pFW c ord) (pPosW c) (pShW c) (pFW_inj c ord)
    ((y.1.1.1.1.1, y.1.2.2.2), (pView y).2)) = _
  rw [he]
  rfl

/-- **Undoing the `k`- and `k'`-stages** after the `h`-stage. -/
theorem pUndo_setHC (y : PSt E F J) (h : Z → X) (hc : J → X) :
    pUndo c (setHC (pStageK' c (pStageK c y)) h hc) = setHC y h hc := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  rw [Equiv.trans_apply, pStageK_setHC, pStageK'_setHC]

/-- The path stages are their `k`- and `k'`-stages with new `h` and slots. -/
theorem pStages_eq_setHC (x : PSt E F J) :
    pStages c ord x = setHC (pStageK' c (pStageK c x)) (pStages c ord x).1.1.1.1.1
      (pStages c ord x).1.2.2.2 := by
  obtain ⟨h, hc, he⟩ := pStageHOn_exists_setHC c ord (pStageK' c (pStageK c x))
  have e : pStages c ord x = pStageHOn c ord (pStageK' c (pStageK c x)) := rfl
  rw [e, he]
  rfl

/-- **The full stage** is the coordinates with new `h` and slots: the slots keep the first `256`
bits of the path stages' slots; at the first labels' capacities `h` is the fix-up's value, and
elsewhere the path stages' `h`. -/
theorem pFull_eq (x : PSt E F J) :
    ∃ (h₃ : Z → X) (hc₃ : J → X), pFull c ord x = setHC x h₃ hc₃ ∧
      (∀ a, out256 (hc₃ a) = out256 ((pStages c ord x).1.2.2.2 a)) ∧
      (∀ a, IsFirst ord (pCellH c (pStages c ord x)) a →
        h₃ (pCellH c (pStages c ord x) a) =
          hiMix ((pStages c ord x).1.1.1.1.1 (pCellH c (pStages c ord x) a))
            ((pStages c ord x).1.2.2.2 a + pShY c (pStages c ord x) a)) ∧
      ∀ z, (∀ a, IsFirst ord (pCellH c (pStages c ord x)) a → pCellH c (pStages c ord x) a ≠ z) →
        h₃ z = (pStages c ord x).1.1.1.1.1 z := by
  obtain ⟨h₃, hc₃, e3, f1, f2, f3⟩ := pHiE_spec c ord (pStages c ord x)
  refine ⟨h₃, hc₃, ?_, f1, f2, f3⟩
  show pUndo c (pHiE c ord (pStages c ord x)) = _
  rw [e3, pStages_eq_setHC c ord x, setHC_setHC, pUndo_setHC]

end pFull

end Quantum.Sphincs.Assembly

end
