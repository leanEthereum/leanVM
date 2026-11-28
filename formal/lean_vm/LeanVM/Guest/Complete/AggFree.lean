module

public import LeanVM.Guest.Complete.Free
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.CoreRef

/-!
# `aggregate_claims`' callees, free

Its four loops and the batching sumcheck have no witness hint in their subtrees and every computed
hint pinned locally (kernel evaluation), so each completes where its relation holds
(`callCompletes_free`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- Function `j`, named `g`, is free: no witness hint, every computed hint pinned. -/
noncomputable def freeAt (g : String) (j : ℕ) : Bool := noWitness g j && exactFree g j

theorem free_of {g : String} {j : ℕ} (h : freeAt g j = true) : NoWitG g ∧ ExactFreeG g := by
  simp only [freeAt, Bool.and_eq_true] at h
  exact ⟨noWitG_of h.1, exactFreeG_of h.2⟩

set_option maxRecDepth 100000 in
theorem agg_loop0_free : NoWitG name% «aggregate_claims_loop0» ∧ ExactFreeG name% «aggregate_claims_loop0» :=
  free_of (by decide +kernel : freeAt name% «aggregate_claims_loop0» idx% «aggregate_claims_loop0» = true)

set_option maxRecDepth 100000 in
theorem agg_loop1_free : NoWitG name% «aggregate_claims_loop1» ∧ ExactFreeG name% «aggregate_claims_loop1» :=
  free_of (by decide +kernel : freeAt name% «aggregate_claims_loop1» idx% «aggregate_claims_loop1» = true)

set_option maxRecDepth 100000 in
theorem agg_loop2_free : NoWitG name% «aggregate_claims_loop2» ∧ ExactFreeG name% «aggregate_claims_loop2» :=
  free_of (by decide +kernel : freeAt name% «aggregate_claims_loop2» idx% «aggregate_claims_loop2» = true)

set_option maxRecDepth 100000 in
theorem agg_loop3_free : NoWitG name% «aggregate_claims_loop3» ∧ ExactFreeG name% «aggregate_claims_loop3» :=
  free_of (by decide +kernel : freeAt name% «aggregate_claims_loop3» idx% «aggregate_claims_loop3» = true)

set_option maxRecDepth 100000 in
theorem agg_bs_free : NoWitG "batch_sumcheck__L25" ∧ ExactFreeG "batch_sumcheck__L25" :=
  free_of (by decide +kernel : freeAt "batch_sumcheck__L25" idx% «batch_sumcheck__L25» = true)

end
end LeanVM.Guest.Complete
