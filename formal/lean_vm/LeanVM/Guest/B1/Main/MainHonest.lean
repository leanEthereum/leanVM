/-
  LeanVM.Guest.B1.Main.MainHonest

  `main`'s honest run from a witness of `NodeRel` within the deployed limits: the coverage plan of
  each region, its counts and their bounds.
-/

module

public import LeanVM.Guest.B1.Main.MainC
public import LeanVM.Guest.B1.Main.Plan
public import LeanVM.Guest.End

/-!
# `main`'s honest run

Each region's writers are its raw claims, then every child's claims (`writersX` and siblings),
given slots by `assign` over the declared claims (`planX`). The counts of `main`'s run are the
declared claims, the duplicates `assign` adds, the raw claims, the children and the raw DA claims
(`honestCounts`); the deployed limits bound them (`honest_total`, `honest_ud`, …), the coverage
table being exactly the writers (`writers_length`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Hints
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.End

@[expose] public section

/-- DA claims are compared by `Hints`' instance, which is equality. -/
instance : LawfulBEq DaClaim where
  rfl {a} := by
    show (a.1.toList == a.1.toList && a.2.toList == a.2.toList) = true
    simp
  eq_of_beq {a b} h := by
    change (a.1.toList == b.1.toList && a.2.toList == b.2.toList) = true at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact Prod.ext (Vector.toList_inj.mp h.1) (Vector.toList_inj.mp h.2)

section Writers

variable (s : NodeStatement) (w : NodeWitness)

/-- The leanXMSS region's writers: the raw claims, then every child's. -/
def writersX : List XmssClaim :=
  (direct s.claims.xmss w.xmss).map (·.1) ++ (w.children.map (·.statement.claims.xmss)).flatten

/-- The leanSPHINCS region's writers. -/
def writersS : List SphincsClaim :=
  (direct s.claims.sphincs w.sphincs).map (·.1) ++
    (w.children.map (·.statement.claims.sphincs)).flatten

/-- The DA region's writers. -/
def writersD : List DaClaim :=
  (direct s.claims.da w.da).map (·.1) ++ (w.children.map (·.statement.claims.da)).flatten

/-- The leanXMSS region's slots and duplicates. -/
def planX : List ℕ × List XmssClaim := assign s.claims.xmss [] [] (writersX s w)

/-- The leanSPHINCS region's slots and duplicates. -/
def planS : List ℕ × List SphincsClaim := assign s.claims.sphincs [] [] (writersS s w)

/-- The DA region's slots and duplicates. -/
def planD : List ℕ × List DaClaim := assign s.claims.da [] [] (writersD s w)

end Writers

/-! ## The counts -/

section Counts

variable {s : NodeStatement} {w : NodeWitness}

theorem count_writersX (hlim : Limits s w) (x : XmssClaim) :
    @List.count _ instBEqOfDecidableEq x s.claims.xmss ≤
      @List.count _ instBEqOfDecidableEq x (writersX s w) := by
  rw [lawful_beq_subsingleton instBEqOfDecidableEq inferInstance, writersX, List.count_append,
    List.count_flatten, List.map_map]
  exact hlim.xmssHeld x

theorem count_writersS (hlim : Limits s w) (x : SphincsClaim) :
    @List.count _ instBEqOfDecidableEq x s.claims.sphincs ≤
      @List.count _ instBEqOfDecidableEq x (writersS s w) := by
  rw [lawful_beq_subsingleton instBEqOfDecidableEq inferInstance, writersS, List.count_append,
    List.count_flatten, List.map_map]
  exact hlim.sphincsHeld x

theorem count_writersD (hlim : Limits s w) (x : DaClaim) :
    @List.count _ instBEqOfDecidableEq x s.claims.da ≤
      @List.count _ instBEqOfDecidableEq x (writersD s w) := by
  rw [lawful_beq_subsingleton instBEqOfDecidableEq inferInstance, writersD, List.count_append,
    List.count_flatten, List.map_map]
  exact hlim.daHeld x

theorem writersX_length (hlim : Limits s w) :
    (writersX s w).length = s.claims.xmss.length + (planX s w).2.length :=
  assign_length_total (count_writersX hlim)

theorem writersS_length (hlim : Limits s w) :
    (writersS s w).length = s.claims.sphincs.length + (planS s w).2.length :=
  assign_length_total (count_writersS hlim)

theorem writersD_length (hlim : Limits s w) :
    (writersD s w).length = s.claims.da.length + (planD s w).2.length :=
  assign_length_total (count_writersD hlim)

/-- **The coverage table is the regions' declared claims and duplicates.** -/
theorem coverage_eq : coverage s w = s.claims.xmss.length + (planX s w).2.length +
    (s.claims.sphincs.length + (planS s w).2.length) + (s.claims.da.length + (planD s w).2.length) := by
  simp only [coverage, plan_dups, planX, planS, planD, writersX, writersS, writersD]
  omega

theorem length_flatten_le {β : Type} (l : List (List β)) (n b : ℕ) (hl : l.length ≤ n)
    (hb : ∀ x ∈ l, x.length ≤ b) : l.flatten.length ≤ n * b := by
  rw [List.length_flatten]
  calc (l.map List.length).sum ≤ l.length * b := by
        have := List.sum_le_length_nsmul (l.map List.length) b (by simpa using hb)
        simpa using this
    _ ≤ n * b := Nat.mul_le_mul_right _ hl

/-- At most `1 + 16·16` DA claims are written. -/
theorem writersD_le (hlim : Limits s w) : (writersD s w).length ≤ 257 := by
  rw [writersD, List.length_append, List.length_map]
  have h1 := hlim.directDa
  have h2 := length_flatten_le (w.children.map (·.statement.claims.da)) 16 16 (by simpa using hlim.children)
    (by simpa using fun c hc => hlim.daRoots.2 c hc)
  omega

end Counts

end
end LeanVM.Guest.B1.Main
