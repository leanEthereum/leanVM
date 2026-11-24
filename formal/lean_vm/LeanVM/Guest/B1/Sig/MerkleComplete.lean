/-
  LeanVM.Guest.B1.Sig.MerkleComplete

  A 64-byte `keccak` of four cells completes, its output their hash.
-/

module

public import LeanVM.Guest.B1.Sig.CodewordComplete
public import LeanVM.Guest.B1.Sig.KMsgComplete

/-!
# A path level's hash, complete

* `check_complete`: an atom holding already completes on an empty range;
* `mPair`: a level's children in the order of its bit;
* `k64_complete`: a 64-byte `keccak` completes, its output the inputs' `hcell`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- **A holding atom completes**, changing nothing. -/
theorem check_complete {a : Atom} {σ : Val} (h : a.Holds rd σ) (lo : Nat) :
    Completes C rd lo lo [.atom a] σ (fun σ' => σ' = σ) :=
  completes_atoms rfl (Ext.refl _ _ _) rfl (fun x hx => by
    simp only [List.mem_singleton, Stmt.atom.injEq] at hx
    subst hx; exact h)

/-- A level's children in the order of its bit, from the node and the sibling. -/
def mPair (bit : Bool) (node sib : E) : E × E := if bit then (sib, node) else (node, sib)

theorem k64_vals_eq (pad : Nat) (m0 m1 m2 m3 : V) (c o : Nat) :
    k64 pad m0 m1 m2 m3 c o = [cst c (word (2 ^ 63) 0)] ++ [kecS [m0, m1, m2, m3, .n pad, .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)]
      (runV o 1) false false] := rfl

/-- **A 64-byte `keccak` completes**, its output the inputs' `hcell`. -/
theorem k64_complete {pad : Nat} {m0 m1 m2 m3 : V} {c : Nat} (σ : Val) (hp : PadOK σ pad)
    (hpc : pad + 5 ≤ c) (hm : ∀ v ∈ [m0, m1, m2, m3], NBv c v) :
    Completes C rd c (c + 2) (k64 pad m0 m1 m2 m3 c (c + 1)) σ
      (fun σ' => σ' (.n (c + 1)) = (hcell [σ m0, σ m1, σ m2, σ m3]).1) := by
  rw [k64_vals_eq]
  refine Completes.append (m := c + 1) (by omega) (by omega)
    (by simp [cst, Stmt.vals, Atom.vals]; exact .cons ⟨c, by omega, rfl⟩ (.nil _))
    (cst_complete σ c _) (fun σ1 he1 hp1 => ?_)
  have hag : AgreeBelow c σ σ1 := he1.agree
  have hin : ∀ v ∈ [m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n (pad + 4)], NBv (c + 1) v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact (hm _ (by simp)).mono' (by omega)
    · exact (hm _ (by simp)).mono' (by omega)
    · exact (hm _ (by simp)).mono' (by omega)
    · exact (hm _ (by simp)).mono' (by omega)
    all_goals exact ⟨_, by omega, rfl⟩
  obtain ⟨σ2, he2, hp2, hh2⟩ := kecS_complete (C := C) (rd := rd) σ1 (c + 1) (.inl rfl) rfl hin false false
  refine ⟨σ2, he2.mono (by omega) (by omega), ?_, hh2⟩
  · show σ2 (.n (c + 1)) = _
    have hk : AtomsHold rd σ2 [kecS [m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c,
        .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)] (runV (c + 1) 1) false false] :=
      atomsHold_of_holdsList rfl (hh2 True (fun _ => True) trivial)
    have hag2 : AgreeBelow (c + 1) σ1 σ2 := he2.agree
    have hp2' : PadOK σ2 pad := hp.congr hpc (fun j hj => (hag j hj).trans (hag2 j (by omega)))
    have := k64_sound (rd := rd) (m0 := m0) (m1 := m1) (m2 := m2) (m3 := m3) (c := c) (o := c + 1) hp2' (h := ?_)
    · rw [this]
      congr 2
      simp only [List.cons.injEq]
      refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;>
        exact ((hag2.apply ((hm _ (by simp)).mono' (by omega))).trans (hag.apply (hm _ (by simp))))
    · rw [k64_vals_eq]
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · simp only [cst, List.mem_singleton, Stmt.atom.injEq] at ha
        subst ha
        show σ2 (.n c) = _
        rw [hag2.apply ⟨c, by omega, rfl⟩]
        exact hp1
      · exact hk a ha

end
end LeanVM.Guest.B1.Sig
