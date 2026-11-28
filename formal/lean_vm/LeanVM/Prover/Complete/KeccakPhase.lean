/-
  LeanVM.Prover.Complete.KeccakPhase

  The Keccak phase in the assembly's terms: from the link's claims (`LinkOut`) and the link's
  sending every `KECCAK` output lane (`LinkLanes`), `KeccakWins`.
-/

module

public import LeanVM.Prover.Complete.Assemble
public import LeanVM.Prover.Complete.Keccak
import LeanVM.Protocol.Relation.Placement

/-!
# The Keccak phase, assembled

`keccakValidity` reads the `KECCAK` table's output lanes' values from the link's columns and
rejects a link missing one (`liftOption`); `LinkLanes link` says the link sent each.
`wins_keccak_of_linkOut`: from `LinkOut` (its column claims hold of the witness's columns, the
table's row point of its log-height) and `LinkLanes`, the Keccak phase wins with the
postcondition `KeccakWins` asks. `keccakWins_of_linkLanes`: `KeccakWins` where every link the
link phase leaves sends the lanes.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.Keccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover

/-- The link sent the value of every `KECCAK` output lane. -/
def LinkLanes (link : LinkEnd) : Prop :=
  ∀ lane < keccakStateLanes, ∃ v, (keccakOut + lane, v) ∈ (link.columns.getD opKeccak ([], [])).2

/-- The link's `KECCAK` values hold of the witness's columns, from its column claims. -/
theorem keccak_values_hold {W : Witness} {link : LinkEnd}
    (h : ∀ c ∈ linkColumnClaims link, c.HoldsIn W.cols) :
    ∀ cv ∈ (link.columns.getD opKeccak ([], [])).2,
      cv.2 = mleK (W.cols.getD (globalColumnBases.getD opKeccak 0 + cv.1) #[])
        (link.columns.getD opKeccak ([], [])).1 := by
  intro cv hcv
  by_cases hl : opKeccak < link.columns.length
  · have hget : link.columns.getD opKeccak ([], []) = link.columns[opKeccak] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    rw [hget] at hcv ⊢
    have hb : opKeccak < globalColumnBases.length := by
      rw [globalColumnBases_eq]; decide
    have hmem : (globalColumnBases.getD opKeccak 0, link.columns[opKeccak]) ∈
        globalColumnBases.zip link.columns := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
      exact List.mem_iff_getElem.2 ⟨opKeccak, by simp [hb, hl], by simp⟩
    exact h ⟨_, link.columns[opKeccak].1, cv.2⟩
      (List.mem_flatMap.2 ⟨_, hmem, List.mem_map.2 ⟨cv, hcv, rfl⟩⟩)
  · have hget : link.columns.getD opKeccak ([], []) = ([], []) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : link.columns.length ≤ opKeccak)]
    rw [hget] at hcv
    simp at hcv

/-- **The Keccak phase wins** with `KeccakWins`'s postcondition, from the link's claims. -/
theorem wins_keccak_of_linkOut {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {ρ : ℕ} {W : Witness} (hA : Admitted prog input t ρ W) {link : LinkEnd} (hout : LinkOut W link)
    (cs : List Committed) :
    Wins 17 (fun a b g cs' ↦ a = b ∧ g = false ∧ cs' = cs ∧ (∀ c ∈ a.1, c.HoldsIn W.cols) ∧
        SlicesHoldIn (W.cols.getD qkeccak #[]) a.2.1 a.2.2 ∧
        (∀ c ∈ a.1, ∀ p, W.layout.placements.getD c.column none = some p →
          c.point.length = p.variableCount) ∧
        a.2.1.length = W.layout.tableLogHeights.getD opKeccak 0 + qkeccakSlotBits ∧
        a.1.length = 1)
      (keccakValidity W.layout link)
      (Script.alongside (keccakValidity W.layout link)
        (KeccakGkr.keccakPhaseProve (W.layout.tableLogHeights.getD opKeccak 0) W.cols link))
      false cs := by
  obtain ⟨-, steps, -, -, hl, -⟩ := witness?_spec hA.witness
  have hlm := (buildLayout_spec hl).1
  refine LeanVM.Prover.Wins.mono (fun _ _ _ _ h ↦ ⟨h.1, h.2.1, h.2.2.1,
      fun c hc ↦ (h.2.2.2.1 c hc).1, h.2.2.2.2.1, fun c hc p hp ↦ ?_, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2⟩) _ _ _ _
    (wins_keccak hA.witness link (hout.2.2.2.1 opKeccak (by decide)) hout.2.2.2.2.2.2.2.1
      (keccak_values_hold hout.1) cs)
  obtain ⟨-, hcol, hlen⟩ := h.2.2.2.1 c hc
  rw [hcol] at hp
  rw [hlen, placement_variableCount hl hp, (columnKappas_memory _ _).2.2]

/-- **The Keccak phase wins** (`KeccakWins`). -/
theorem keccakWins : KeccakWins := fun _ _ _ _ _ hA _ hout cs ↦ wins_keccak_of_linkOut hA hout cs

end LeanVM.Prover.Complete.Keccak

end
