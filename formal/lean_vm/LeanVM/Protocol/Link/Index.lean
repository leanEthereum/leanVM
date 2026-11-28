/-
  LeanVM.Protocol.Link.Index

  The index side's claim is the state link's right side at the drawn challenges.
-/

module

public import LeanVM.Protocol.Link.Skeleton
public import LeanVM.Protocol.Hotwire.StateLink
import LeanVM.Facts.Hotwire
import LeanVM.Parameters.Field

/-!
# The index side's claim

`verifyLink`'s index side starts from `eq(ζ, 0)·ŝ_init + eq(ζ, T)·ŝ_fin` (`indexClaim`), with
`ŝ_γ = 1 + γ_pc·pc + γ_fp·fp` (`state_gamma`), `ŝ_init` at `pc = fp = 1` and `ŝ_fin` at the last
instruction's address and `fp = 1`. `indexClaim_eq_scalarRhs`: it is `StateLink.lean`'s right side
`scalarRhs T s_init s_fin ζ γ` at `ζ` and `γ` the challenges `verify_link` reads them from
(`linkZeta`, `linkGammaState`), in characteristic two, where its difference is a sum. This is the
claim side of the arithmetization `verifyLink_sound` takes (`hidx`).
-/

namespace LeanVM.Protocol.Link

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Hotwire

@[expose] public section

/-- `ζ`, the state link's point, as `verify_link` slices it from the drawn challenges. -/
def linkZeta (layout : Layout) (chunks : Chunks) (drawn : List E) : List E :=
  let tables := layout.tables
  let heights := layout.tableLogHeights
  let width := chunks.width
  let pointers := tables.map (·.links.pointers)
  let nPointers := (pointers.map List.length).sum
  let nRows := heights.foldl max 0
  let drawn := drawn.drop (nTables - 1)
  let drawn := drawn.drop 2
  let drawn := drawn.drop 3
  let (_, drawn) := tables.foldl (fun (acc : List (List E) × List E) t ↦
    (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length)) ([], drawn)
  let drawn := drawn.drop bytecodeSlotBits
  let drawn := drawn.drop 2
  let drawn := drawn.drop nPointers
  let drawn := drawn.drop nRows
  let zeta := drawn.take width
  zeta

/-- `(γ_pc, γ_fp)`, the state's coefficients, as `verify_link` slices them. -/
def linkGammaState (drawn : List E) : List E := (drawn.drop (nTables - 1)).take 2

/-- **The index side's claim is the state link's right side**: `eq(ζ, 0)·⟨(1, γ), (1, s_init)⟩ −
eq(ζ, T)·⟨(1, γ), (1, s_fin)⟩` at `s_init = (1, 1)`, `s_fin = (g^(2^log_bytecode − 1), 1)` and the
drawn `ζ`, `γ`, `T` the cycle count. -/
theorem indexClaim_eq_scalarRhs (layout : Layout) (chunks : Chunks) (drawn : List E) :
    indexClaim layout chunks drawn =
      scalarRhs (linkCycles layout) ![1, 1] ![gpow (2 ^ layout.logBytecode - 1), 1]
        (fun i : Fin (linkZeta layout chunks drawn).length ↦ (linkZeta layout chunks drawn)[i])
        ![(linkGammaState drawn).getD 0 0, (linkGammaState drawn).getD 1 0] := by
  have hz : (List.ofFn fun i : Fin (linkZeta layout chunks drawn).length ↦
      (linkZeta layout chunks drawn)[i]) = linkZeta layout chunks drawn :=
    List.ext_getElem (by simp) (by simp)
  rw [scalarRhs, hz, dotAug_eq, dotAug_eq, CharTwo.sub_eq_add]
  simp only [Fin.sum_univ_two, aug_zero, aug_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  show linkEqAt _ 0 * _ + linkEqAt _ _ * _ = _
  rw [linkEqAt, linkEqAt, linkEqAt_eq, linkEqAt_eq]
  simp only [linkGammaState, linkZeta, linkCycles]
  ring

end

end LeanVM.Protocol.Link
