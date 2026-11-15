/-
  LeanVM.Guest.B1.Main.MainGoalsDvTB

  `main`'s `da_verify` on an honest run, by a tree of its honest shape, within its words bound
  (`hDvB`) at the direct DA witness, for the budget.

  The witness and `Da.MatrixWitness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsDvT
public import LeanVM.Guest.B1.Da.WitnessAtTB
public import LeanVM.Guest.AcceptableChild

/-!
# `da_verify` on an honest run, within its bound

`hDvB fs SB SK w`: `Da.dvB` at the directly held DA claim's witness (`0` without one).
`MainGoalDvTB`: `MainGoalDvT` within `hDvB`; `mainGoalDvTB`: as `mainGoalDvT`, from the static
bounds `Da.DvStaticB`. `completeAtDTB_lin_mono`: `completeAtDT_lin_mono` within a bound.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Coverage (coveragePlan)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB Returns)
open LeanVM.Guest.B1.Da (reads_of_memL exists_of_length_succ wLog)

@[expose] public section

/-- A callee's bounded completeness reading fewer words holds reading more. -/
theorem completeAtDTB_lin_mono {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Lin Lin' : Layout} {args : List E} {Out : List E → Layout → Prop} {T : Tree → Prop} {B : ℕ}
    (hm : ∀ rd, MemL rd Lin' → MemL rd Lin) (hr : ∀ i, RegionL Lin i → RegionL Lin' i)
    (h : CompleteAtDTB fs cert κ f Lin args Out T B) : CompleteAtDTB fs cert κ f Lin' args Out T B := by
  intro fp
  obtain ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hR⟩ := h fp
  refine ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hM => ?_⟩
  obtain ⟨t, ⟨hn', hv, hb, hp, ht, hlo, hdd⟩, hT⟩ := hR rd hl (by
    rw [memL_append] at hM ⊢; exact ⟨hM.1, hm rd hM.2⟩)
  exact ⟨t, ⟨hn', hv, hb, hp, ht, loadsIn_mono t fp hr hlo, hdd⟩, hT⟩

/-- **`da_verify`'s words bound on the checked DA claim's witness.** -/
def hDvB (fs : String → ℕ) (SB SK : String → ℕ) (w : NodeWitness) : ℕ :=
  (w.daMatrix.map fun p => Da.dvB fs SB SK p.2.rows.length (wLog p.2)).getD 0

/-- `da_verify` complete by a tree of its honest shape, within `hDvB`. -/
def MainGoalDvTB (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) (SB SK : String → ℕ) : Prop :=
  (hm fs fp seed s w).nd = 1 →
    CompleteAtDTB fs cert 20 "da_verify" (hLmain fs fp seed s w) []
      (Returns (hm fs fp seed s w).daR) (hDvNH w) (hDvB fs SB SK w)

theorem MainGoalDvTB.goal {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest}
    {s : NodeStatement} {w : NodeWitness} {SB SK : String → ℕ}
    (h : MainGoalDvTB fs cert fp seed s w SB SK) : MainGoalDvT fs cert fp seed s w :=
  fun hn => (h hn).toDT

variable {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ)

/-- **`da_verify` on an honest run, by a tree of its honest shape, within `hDvB`.** -/
theorem mainGoalDvTB (hn : NodeRelation bytecode seed s w) (hrf : Lift.RunsFit fs cert)
    {SB SK : String → ℕ} (hS : Da.DvStaticB fs SB SK) :
    MainGoalDvTB fs cert fp seed s w SB SK := by
  intro h1
  obtain ⟨p, hp, hR, hw⟩ := checked_da fs fp hn h1
  rw [hR, hDvNH, hDvB, hp]
  simp only [Option.map_some, Option.getD_some]
  have h := Da.da_verify_completeAtTB fs cert hrf hw hS
  refine completeAtDTB_lin_mono (fun _ _ q hq => by simp at hq) (fun i hi => ?_)
    (h.lowMono (by norm_num))
  obtain ⟨q, hq, -⟩ := hi
  simp at hq

end
end LeanVM.Guest.B1.Main
