/-
  LeanVM.Guest.B1.Tables.Kids.Direct

  Leaves loading through their parameters at bounded offsets: their relation loads from any
  region holding those runs (`Program.RelIn`).
-/

module

public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Selectors.Interface
public import LeanVM.Guest.B1.Selectors.LayoutBasic

/-!
# Leaves with direct loads

`dloadB bs`: an atom that is not a load, or a load through parameter `p` at an offset below
`bs[p]` (`0` past the table: no load). `dloadCheck g bs`: `g`'s parameters are `.n 0 ..`, one per
entry of `bs`, and its body is a leaf (`Lift.Stmt.leafOkList`) of such atoms; the kernel checks it.

`PtrIn R p B`: the `B` words from `p` lie in `R`. `relIn_of_dload`: a function passing
`dloadCheck g bs` whose parameter runs `(args[p], bs[p])` lie in `R` has its relation by a tree
loading from `R` only. `ptrIn_ofK`: a run from `g^b` lies in `R` when `b ..< b + B` does.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Lift
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- A load through a parameter at an offset below its bound, or no load. -/
def dloadB (bs : List ℕ) : Atom → Bool
  | .load _ p off => decide (p = .n p.idx) && decide (off < bs.getD p.idx 0)
  | _ => true

/-- `g`'s parameters are `.n 0 ..< .n bs.length` and its body a leaf of `dloadB bs` atoms. -/
noncomputable def dloadCheck (g : String) (bs : List ℕ) : Bool :=
  match coreProgram.find? g with
  | some fn => decide (fn.params = (List.range bs.length).map V.n) &&
      Lift.Stmt.leafOkList (dloadB bs) fn.body
  | none => false

/-- `p` is in `K` and the `B` words from `p` lie in `R`. -/
def PtrIn (R : ℕ → Prop) (p : E) (B : ℕ) : Prop :=
  IsInK p ∧ ∀ off < B, ∃ i, p.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i

theorem ptrIn_ofK {R : ℕ → Prop} {b B : ℕ} (h : ∀ i < B, R (b + i)) :
    PtrIn R (ofK (addressOfIndex b)) B :=
  ⟨tb_isInK_ofK _, fun off hoff ↦ ⟨b + off, Main.addr_ofK b off, h off hoff⟩⟩

theorem ptrIn_mono {R : ℕ → Prop} {p : E} {B B' : ℕ} (h : PtrIn R p B) (hle : B' ≤ B) :
    PtrIn R p B' := ⟨h.1, fun off hoff ↦ h.2 off (by omega)⟩

/-- A run from `p·g^j` lies inside the run from `p`. -/
theorem ptrIn_mul {R : ℕ → Prop} {p : E} {j B : ℕ} (h : PtrIn R p (j + B)) :
    PtrIn R (p * gen ^ j) B := by
  have hg : Parameters.addressOfIndex j ≠ 0 := pow_ne_zero _ g_ne_zero
  refine ⟨by rw [gen_pow_eq_ofK]; exact (tb_isInK_mul_ofK hg).mpr h.1, fun off hoff ↦ ?_⟩
  obtain ⟨i, hi, hr⟩ := h.2 (j + off) (by omega)
  refine ⟨i, ?_, hr⟩
  rw [gen_pow_eq_ofK, tb_limb0_mul_ofK h.1, mul_assoc, Parameters.addressOfIndex,
      Parameters.addressOfIndex,
    ← pow_add]
  exact hi

/-- **A leaf loading through its parameters loads from `R`** when their runs lie in `R`. -/
theorem relIn_of_dload {g : String} {bs : List ℕ} (hck : dloadCheck g bs = true) {rd : Reader}
    {R : ℕ → Prop} {args rets : List E}
    (hreg : ∀ p < bs.length, 0 < bs.getD p 0 → PtrIn R (args.getD p 0) (bs.getD p 0))
    (h : coreProgram.Rel rd g args rets) : coreProgram.RelIn rd R g args rets := by
  unfold dloadCheck at hck
  split at hck
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
    obtain ⟨hp, hleaf⟩ := hck
    refine relIn_of_leaf hf hleaf (fun σ es vs hpa hw A hA ↦ ?_) h
    have hall := walk_leafOk (σ := σ) _ hleaf
    rw [hw] at hall
    obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
    have hok := hall e he
    cases e with
    | atom a =>
      cases a with
      | load d p off =>
        simp only [EvLeafOk, dloadB, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨hpn, hoff⟩ := hok
        have hplt : p.idx < bs.length := by
          by_contra hc
          rw [List.getD_eq_default _ _ (by omega)] at hoff
          omega
        simp only [Ev.loadAddr?, Option.some.injEq] at hea
        subst hea
        have hσp : σ p = args.getD p.idx 0 := by
          rw [← hpa, hp, List.getD_eq_getElem _ _ (by simp; omega)]
          simp only [List.getElem_map, List.getElem_range]
          rw [← hpn]
        rw [hσp]
        exact (hreg _ hplt (by omega)).2 off hoff
      | _ => simp [Ev.loadAddr?] at hea
    | _ => simp [Ev.loadAddr?] at hea
  · exact absurd hck (by simp)

end
end LeanVM.Guest.B1.Tables
