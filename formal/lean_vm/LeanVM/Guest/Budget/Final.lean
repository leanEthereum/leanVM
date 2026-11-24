/-
  LeanVM.Guest.Budget.Final

  The budget `mainBudget` and the bounds on `main`'s callees' instructions it rests on.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.EndComplete
public import LeanVM.Guest.B1.Main.KidsT
public import LeanVM.Guest.Budget.Static
public import LeanVM.Guest.Budget.MainCount
public import LeanVM.Guest.B1.Main.MainHonestBudgetB
public import LeanVM.Guest.Budget.Instrs
public import LeanVM.Guest.AcceptableChild

/-!
# `main`'s budget

`mainBudget`: `main`'s words (`mainWords`) at the static bounds and `verify_sub`'s words at each child's announced
stack log and rate, and its instructions (`mainInstrs`) at the callees' weights, the children's loop's `l5Lin` and the
jump table's. `claims_lt`, `clHonest_weight`, `dvNH_weight`: the claim lists' and `da_verify`'s instructions on their
honest trees within `MainCounts`' affine bounds.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol
open LeanVM.Guest.End (Budget work bytecode)
open LeanVM.Guest.B1.Main (hm hDvNH)

@[expose] public section

/-- **The budget**: `main`'s words (B1-f's `mainWords`) at the static bounds `SB`, `SK` and
`verify_sub`'s words `Bvf μ r` at a child's announced stack log `μ` and rate `r`, and its
instructions (`mainInstrs`) at the callees' weights `H`, the children's loop's instructions
`l5Lin (c5 op) (s5 op) (v5 op)` and the jump table's `jt`. -/
def mainBudget (fs : String → ℕ) (SB SK : String → ℕ) (Bvf : ℕ → ℕ → ℕ) (ω : Opcode → String → ℕ)
    (H : ∀ op, MainCounts (ω op) fs) (c5 s5 : Opcode → ℕ) (v5 : Opcode → ℕ → ℕ → ℕ)
    (jt : Opcode → ℕ) : Budget :=
  ⟨B1.Main.mainWords fs SB SK Bvf, fun op => mainInstrs (H op) (c5 op) (s5 op) (v5 op) (jt op)⟩

/-- The declared claims of each scheme are held by the raw signatures and the children's claims
(`GuestLimits`), so are fewer than the coverage slots, below `2^23`. -/
theorem claims_lt {s : NodeStatement} {w : NodeWitness} (hl : GuestLimits s w) :
    s.claims.xmss.length < 2 ^ 23 ∧ s.claims.sphincs.length < 2 ^ 23 := by
  have hx := hl.claimsHeldWithMultiplicity.1.length_le
  have hs := hl.claimsHeldWithMultiplicity.2.length_le
  have hc := hl.coverageSlotsBelow2Pow23
  have hx' := List.sum_le_sum (l := w.children)
    (f := fun ch ↦ ch.statement.claims.xmss.length)
    (g := fun ch ↦ ch.statement.claims.xmss.length + ch.statement.claims.sphincs.length)
    fun _ _ ↦ Nat.le_add_right _ _
  have hs' := List.sum_le_sum (l := w.children)
    (f := fun ch ↦ ch.statement.claims.sphincs.length)
    (g := fun ch ↦ ch.statement.claims.xmss.length + ch.statement.claims.sphincs.length)
    fun _ _ ↦ Nat.le_add_left _ _
  simp only [List.length_append, List.length_map, List.length_flatten, List.map_map,
    Function.comp_def] at hx hs
  unfold coverageSlots at hc
  omega

/-- **`main`'s claim lists' instructions** on their honest trees: `clA + clS · n` on `n` claims. -/
theorem clHonest_weight {ω fs : String → ℕ} (H : MainCounts ω fs) {n : ℕ} (hn : n < 2 ^ 23) (rd : Reader) (t : Tree)
    (args rets : List E) (hnm : t.name = "claim_list_digest") (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (hT : B1.Main.clHonest n t) : t.weight ω ≤ H.clA + H.clS * n :=
  H.cl rd t args rets n hnm hv hb hT (by omega)

/-- **`main`'s `da_verify`'s instructions** on its honest tree at the checked blob matrix: `dvA`,
`dvR` per row and `dvP` per padded row. -/
theorem dvNH_weight {ω fs : String → ℕ} (H : MainCounts ω fs) {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hr : NodeRelation bytecode seed s w) (hnd : (hm fs 0 seed s w).nd = 1) (rd : Reader) (t : Tree)
    (args rets : List E) (hnm : t.name = "da_verify") (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (hT : hDvNH w t) :
    t.weight ω ≤ H.dvA + H.dvR * (work s w).rawDaRows + H.dvP * (work s w).rawDaPad := by
  obtain ⟨p, hp, -, hw⟩ := B1.Main.checked_da fs 0 hr hnd
  have er : (work s w).rawDaRows = p.2.rows.length := by
    simp [work, hp]
  have ep : (work s w).rawDaPad = 2 ^ B1.Da.wLog p.2 := by
    simp [work, hp, LeanDa.maxRows, B1.Da.wLog]
  unfold hDvNH at hT
  rw [hp] at hT
  simp only [Option.map_some, Option.getD_some] at hT
  rw [er, ep]
  exact H.dv rd t args rets _ _ hnm hv hb hT hw.1 hw.2.1 rfl

end
end LeanVM.Guest.Budget
