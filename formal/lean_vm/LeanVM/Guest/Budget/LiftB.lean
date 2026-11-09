/-
  LeanVM.Guest.Budget.LiftB

  G7's lifts of pure callees (the signature verifiers, `open_stacked`'s leaf callees) within the
  static words bound of their valid trees (`CompleteAtDTB`).
-/

module

public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.Lift.Sig
public import LeanVM.Guest.Lift.OsCallees
public import LeanVM.Guest.Memory.Size

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- The words bound of every valid tree of `f` at `args`, as `completeAtDTB_of_relIn` takes it
(`TotalLe` at `args`). -/
def TotalAt (fs : String → ℕ) (f : String) (args : List E) (B : ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (rets : List E), t.name = f → t.Valid coreProgram rd args rets →
    t.BufsOk coreProgram → t.total fs ≤ B

theorem TotalLe.at {f : String} {B : List E → ℕ} (h : TotalLe coreProgram fs f B) (args : List E) :
    TotalAt fs f args (B args) := fun rd t rets hn hv hb => h rd t args rets hn hv hb

/-- `CompleteRelRegD` within the words bound `B args`. -/
def CompleteRelRegDB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) (Reg : List E → (ℕ → Prop) → Prop) (B : List E → ℕ) :
    Prop :=
  ∀ args rets Lin, Reg args (RegionL Lin) → (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) →
    CompleteAtDTB fs cert k f Lin args (Returns rets) (fun _ => True) (B args)

/-- **A leaf callee whose relation is its meaning, placed on its regions within its words
bound.** -/
theorem completeRelRegDB_of_iff {f : String} {spec : List (ℕ × ℕ)}
    {Pre : Reader → List E → List E → Prop} (hok : LeafSpecOk f spec)
    (hiff : ∀ rd args rets, coreProgram.Rel rd f args rets ↔ Pre rd args rets) (k : ℕ)
    {B : List E → ℕ} (hB : TotalLe coreProgram fs f B) :
    CompleteRelRegDB fs cert k f Pre (RegPtrs spec) B := by
  obtain ⟨fn, hf, hpar, hleaf⟩ := hok
  intro args rets Lin hreg hpre
  refine completeAtDTB_of_relIn (Lift.pureIn_of_leafOk hf hleaf) (List.mem_singleton_self _)
    (TotalLe.at hB args) fun rd hl hL => Lift.relIn_of_leaf hf hleaf (fun σ es vs hp hw A hA => ?_)
      ((hiff rd args rets).mpr (hpre rd hl hL))
  have hall := Lift.walk_leafOk (σ := σ) fn.body hleaf
  rw [hw] at hall
  obtain ⟨q, hq, off, hoff, rfl⟩ := loads_spec hall A hA
  have hσ : σ (.n q.1) = args.getD q.1 0 := by
    have h1 := hpar q hq
    have h2 : (fn.params.map σ)[q.1]? = args[q.1]? := by rw [hp]
    rw [List.getElem?_map, h1] at h2
    simp only [Option.map_some] at h2
    rw [List.getD_eq_getElem?_getD, ← h2]
    rfl
  rw [hσ]
  exact hreg q hq off hoff

end
end LeanVM.Guest.B1
