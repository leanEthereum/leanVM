/-
  LeanVM.Guest.B1.Sig.XmssStep

  leanXMSS's chain step, for completeness: a step equal to `xW` on the chains, steps and powers the
  codeword uses, its constants below the codeword's base.
-/

module

public import LeanVM.Guest.B1.Sig.WotsCongr
public import LeanVM.Guest.B1.Sig.MerkleComplete
public import LeanVM.Guest.B1.Sig.XmssLayer

/-!
# leanXMSS's chain step, complete

* `k64_ssa`: a 64-byte `keccak` is in single-assignment form;
* `xWc`: `xW` with its step's address, chain index and power clamped to the ones the codeword
  uses (`xW_weq`), so that its constants lie below the codeword;
* `XGood`: the values the step reads that its proofs need: the padding run and the powers;
  `xWc_shape`, `xGood_stable`, `xWc_sound`.
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

/-! ## The step -/

/-- **`xW` clamped**: the step's address, chain index and power clamped to the ones the codeword
uses, so that all its constants lie below the codeword. -/
def xWc (layer b : Nat) : WotsT where
  step i s v c o := k64 xPad (.n 1) (.n (xA layer b + 2 * min s 2 + 1)) v (.n (138 + min i 57)) c o
  size := 1
  power j := .n (128 + min j 9)

theorem xW_weq (layer b : Nat) : WEq (xW layer b) (xWc layer b) 58 := by
  refine ⟨rfl, fun i hi s hs => ?_, fun j hj => ?_⟩
  · funext v c o
    simp only [xW, xWots, xWc, xTag, Nat.min_eq_left (show s ≤ 2 by omega),
      Nat.min_eq_left (show i ≤ 57 by omega)]
  · simp only [xW, xWots, xWc, xPower, Nat.min_eq_left (show j ≤ 9 by omega)]

/-- The values leanXMSS's chain step reads that its proofs need: the padding run and the powers. -/
def XGood (_layer _b : Nat) (σ : Val) : Prop :=
  PadOK σ xPad ∧ ∀ s < 10, σ (.n (128 + s)) = gen ^ s

theorem xWc_atoms (layer b : Nat) : StepAtoms (xWc layer b) := fun _ _ _ _ _ => rfl

theorem xWc_shape {layer b : Nat} (hB : 211 ≤ xA layer b) : StepShape (xWc layer b) (xA layer b + 6) := by
  intro i s v c o hc ho hco h1 h2
  have hs2 : min s 2 ≤ 2 := Nat.min_le_right _ _
  have hi57 : min i 57 ≤ 57 := Nat.min_le_right _ _
  refine ⟨k64_ssa hco (fun x hx => ?_) (Or.inl (by simp [xPad]; omega)), fun x hx => ?_, fun x hx => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals first | exact h2 | (rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega)
  · change x ∈ outsList (k64 xPad (.n 1) (.n (xA layer b + 2 * min s 2 + 1)) v (.n (138 + min i 57)) c o) at hx
    rw [k64_outs] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl ⟨0, by simp [xWc], by simp⟩
    · exact Or.inr (mem_runV.mp hx)
  · rcases k64_vals _ _ _ _ _ c o hx with hx | rfl | ⟨k, hk, rfl⟩ | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl ⟨1, by omega, rfl⟩)
      · exact Or.inr (Or.inl ⟨_, by omega, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨_, by omega, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨0, by simp [xWc], by simp⟩))
    · exact Or.inr (Or.inl ⟨_, by simp [xPad]; omega, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr hx))

theorem xGood_congr {layer b : Nat} (hB : 211 ≤ xA layer b) {σ σ' : Val}
    (hσ : AgreeBelow (xA layer b + 6) σ σ') (h : XGood layer b σ) : XGood layer b σ' := by
  obtain ⟨g4, g5⟩ := h
  refine ⟨g4.congr (b := xA layer b + 6) (by simp [xPad]; omega) hσ, fun s hs => ?_⟩
  rw [hσ.apply ⟨_, by omega, rfl⟩]; exact g5 s hs

theorem xGood_stable {layer b : Nat} (hB : 211 ≤ xA layer b) :
    GoodStable (xA layer b + 6) (XGood layer b) :=
  fun _ _ hσ h => xGood_congr hB hσ h

theorem xWc_sound {layer b : Nat} {σ : Val} (hg : XGood layer b σ) :
    StepSound rd σ (xWc layer b)
      (fun i s y => (hcell [σ (.n 1), σ (.n (xA layer b + 2 * min s 2 + 1)), y, σ (.n (138 + min i 57))]).1) := by
  intro i s v c o h
  exact k64_sound hg.1 h

theorem xWc_pow {layer b : Nat} {σ : Val} (hg : XGood layer b σ) :
    ∀ s < 10, σ ((xWc layer b).power s) = gen ^ s := by
  intro s hs
  simp only [xWc, Nat.min_eq_left (show s ≤ 9 by omega)]
  exact hg.2 s hs

theorem xWc_pw (layer b : Nat) (hB : 211 ≤ xA layer b) : ∀ j, NBv (xA layer b + 6) ((xWc layer b).power j) :=
  fun j => ⟨128 + min j 9, by have := Nat.min_le_right j 9; omega, rfl⟩

end
end LeanVM.Guest.B1.Sig
