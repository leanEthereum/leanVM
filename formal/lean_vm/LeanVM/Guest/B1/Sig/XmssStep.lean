/-
  LeanVM.Guest.B1.Sig.XmssStep

  A 64-byte `keccak`, the chain step's hash, in single-assignment form.
-/

module

public import LeanVM.Guest.B1.Sig.WotsCongr
public import LeanVM.Guest.B1.Sig.MerkleComplete
public import LeanVM.Guest.B1.Sig.XmssLayer

/-!
# A 64-byte `keccak`, in single-assignment form

* `runV_nodup`, `mem_runV`: a run's values are distinct, the values in its range;
* `k64_ins`, `k64_outs`, `k64_vals`: a 64-byte `keccak`'s inputs, outputs and values;
* `k64_ssa`: it is in single-assignment form.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {rd : Reader}

theorem runV_nodup (o n : Nat) : (runV o n).Nodup := by
  unfold runV
  refine List.Nodup.map (fun a b e => ?_) List.nodup_range
  simp only [V.mk.injEq, true_and] at e
  omega

theorem mem_runV {o n : Nat} {x : V} : x ∈ runV o n ↔ InR o n x := by
  unfold runV InR
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

theorem k64_ins (pad : Nat) (m0 m1 m2 m3 : V) (c : Nat) (x : V) :
    x ∈ [m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n (pad + 4)] ↔ x ∈ [m0, m1, m2, m3] ∨ x = .n c ∨ InR pad 5 x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, InR]
  constructor
  · rintro (h | h | h | h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | exact Or.inl (by simp [h]) | exact Or.inr (Or.inl rfl) |
      exact Or.inr (Or.inr ⟨0, by omega, rfl⟩) | exact Or.inr (Or.inr ⟨1, by omega, rfl⟩) |
      exact Or.inr (Or.inr ⟨2, by omega, rfl⟩) | exact Or.inr (Or.inr ⟨3, by omega, rfl⟩) |
      exact Or.inr (Or.inr ⟨4, by omega, rfl⟩)
  · rintro ((h | h | h | h) | rfl | ⟨j, hj, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · simp
    · interval_cases j <;> simp

/-- **A 64-byte `keccak` is in single-assignment form**, its inputs off its outputs. -/
theorem k64_ssa {pad : Nat} {m0 m1 m2 m3 : V} {c o : Nat} (hco : c + 1 ≤ o ∨ o + 1 ≤ c)
    (hm : ∀ v ∈ [m0, m1, m2, m3], ¬ InR o 1 v) (hpo : pad + 5 ≤ o ∨ o + 1 ≤ pad) :
    SSA (k64 pad m0 m1 m2 m3 c o) := by
  refine ⟨trivial, fun v hv h => by simp [aReads] at h, fun v hv h => ?_, ⟨rfl, by simp [runV],
    runV_nodup o 1⟩, fun v hv h => ?_, fun v hv => by simp [outsList] at hv, trivial⟩
  · simp only [outsList, aOuts, List.append_nil, kecS] at hv
    rw [mem_runV] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    simp only [Atom.vals, List.mem_singleton, V.mk.injEq, true_and] at h
    omega
  · simp only [aOuts] at hv
    rw [mem_runV] at hv
    simp only [aReads] at h
    rcases (k64_ins pad m0 m1 m2 m3 c v).mp h with h | rfl | ⟨k, hk, rfl⟩
    · exact hm v h hv
    · obtain ⟨j, hj, e⟩ := hv
      simp only [V.mk.injEq, true_and] at e
      omega
    · obtain ⟨j, hj, e⟩ := hv
      simp only [V.mk.injEq, true_and] at e
      omega

theorem k64_outs (pad : Nat) (m0 m1 m2 m3 : V) (c o : Nat) :
    outsList (k64 pad m0 m1 m2 m3 c o) = .n c :: runV o 1 := by
  simp [k64, cst, kecS, outsList, aOuts]

theorem k64_vals (pad : Nat) (m0 m1 m2 m3 : V) (c o : Nat) {x : V}
    (hx : x ∈ Stmt.valsList (k64 pad m0 m1 m2 m3 c o)) :
    x ∈ [m0, m1, m2, m3] ∨ x = .n c ∨ InR pad 5 x ∨ InR o 1 x := by
  simp only [k64, cst, kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
    List.mem_append, List.mem_singleton] at hx
  rcases hx with rfl | hx | hx
  · exact Or.inr (Or.inl rfl)
  · rcases (k64_ins pad m0 m1 m2 m3 c x).mp hx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (mem_runV.mp hx)))

end
end LeanVM.Guest.B1.Sig
