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

* `k64_ssa`, `k64_fwd_canon`: a 64-byte `keccak` is in single-assignment form and reads and writes
  canonical cells;
* `xWc`: `xW` with its step's address, chain index and power clamped to the ones the codeword
  uses (`xW_weq`), so that its constants lie below the codeword;
* `XGood`: the values the step reads: `P`, the step addresses, the chain indices, the padding run
  and the powers; `xWc_shape`, `xWc_canon`, `xWc_sound`.
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

/-- **A 64-byte `keccak` reads and writes canonical cells**, its inputs canonical and the padding
run set. -/
theorem k64_fwd_canon {pad : Nat} {m0 m1 m2 m3 : V} {c o : Nat} (σ : Val) (hco : c + 1 ≤ o ∨ o + 1 ≤ c)
    (hm : ∀ v ∈ [m0, m1, m2, m3], ¬ InR o 1 v ∧ v ≠ .n c ∧ IsCanonical128 (σ v))
    (hpc : pad + 5 ≤ c) (hpo : pad + 5 ≤ o) (hp : PadOK σ pad) :
    KCanon (fwd (k64 pad m0 m1 m2 m3 c o) σ) (k64 pad m0 m1 m2 m3 c o) ∧
      ∀ j < 1, IsCanonical128 (fwd (k64 pad m0 m1 m2 m3 c o) σ (.n (o + j))) := by
  set σ1 := Function.update σ (.n c) (word (2 ^ 63) 0 0) with hσ1
  have hf : fwd (k64 pad m0 m1 m2 m3 c o) σ = updL σ1 (runV o 1)
      (kOut ([m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1),
        .n (pad + 2), .n (pad + 3), .n (pad + 4)].map σ1) false false) := rfl
  refine ⟨fun ins outs i o' hmem cc => ?_, fun j hj => ?_⟩
  · simp only [k64, cst, kecS, List.mem_cons, Stmt.atom.injEq, reduceCtorEq, false_or,
      List.not_mem_nil, or_false, Atom.keccak.injEq] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    rw [hf]
    have hmap : ∀ v ∈ [m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1),
        .n (pad + 2), .n (pad + 3), .n (pad + 4)], updL σ1 (runV o 1) (kOut ([m0, m1, m2, m3, .n pad,
          .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1), .n (pad + 2), .n (pad + 3),
          .n (pad + 4)].map σ1) false false) v = σ1 v := by
      intro v hv
      refine updL_of_not_mem σ1 _ _ fun h => ?_
      rw [mem_runV] at h
      rcases (k64_ins pad m0 m1 m2 m3 c v).mp hv with h' | rfl | ⟨k, hk, rfl⟩
      · exact (hm v h').1 h
      · obtain ⟨j, hj, e⟩ := h
        simp only [V.mk.injEq, true_and] at e
        omega
      · obtain ⟨j, hj, e⟩ := h
        simp only [V.mk.injEq, true_and] at e
        omega
    rw [List.map_congr_left hmap]
    have h4 : ∀ v ∈ [m0, m1, m2, m3], IsCanonical128 (σ1 v) := fun v hv => by
      rw [hσ1, Function.update_of_ne (hm v hv).2.1]
      exact (hm v hv).2.2
    have hpk : ∀ k < 5, σ1 (.n (pad + k)) = σ (.n (pad + k)) := fun k hk => by
      rw [hσ1, Function.update_of_ne (by simp; omega)]
    have hc1 : σ1 (.n c) = word (2 ^ 63) 0 0 := by rw [hσ1, Function.update_self]
    obtain ⟨q0, q1, q2, q3, q4⟩ := hp
    have p0 := hpk 0 (by norm_num)
    have p1 := hpk 1 (by norm_num)
    have p2 := hpk 2 (by norm_num)
    have p3 := hpk 3 (by norm_num)
    have p4 := hpk 4 (by norm_num)
    simp only [Nat.add_zero] at p0
    fin_cases cc <;> simp [cells13, q0, q1, q2, q3, q4, p0, p1, p2, p3, p4, hc1] <;>
      first | exact h4 _ (by simp) | exact canon_word _ _
  · rw [hf]
    have := updL_at σ1 (runV o 1) (kOut ([m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2),
      .n (pad + 3), .n c, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)].map σ1) false false)
      (runV_nodup o 1) j (by simp [runV]; omega)
    have hj' : (runV o 1)[j]'(by simp [runV]; omega) = .n (o + j) := by simp [runV]; omega
    rw [hj'] at this
    rw [this]
    exact canon_kOut _ _ _ _

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

/-- The values leanXMSS's chain step reads. -/
def XGood (layer b : Nat) (σ : Val) : Prop :=
  IsCanonical128 (σ (.n 1)) ∧ (∀ s < 3, IsCanonical128 (σ (.n (xA layer b + 2 * s + 1)))) ∧
    (∀ i < 58, IsCanonical128 (σ (.n (138 + i)))) ∧ PadOK σ xPad ∧ ∀ s < 10, σ (.n (128 + s)) = gen ^ s

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
  obtain ⟨g1, g2, g3, g4, g5⟩ := h
  refine ⟨by rw [hσ.apply ⟨1, by omega, rfl⟩]; exact g1, fun s hs => ?_, fun i hi => ?_,
    g4.congr (b := xA layer b + 6) (by simp [xPad]; omega) hσ, fun s hs => ?_⟩
  · rw [hσ.apply ⟨_, by omega, rfl⟩]; exact g2 s hs
  · rw [hσ.apply ⟨_, by omega, rfl⟩]; exact g3 i hi
  · rw [hσ.apply ⟨_, by omega, rfl⟩]; exact g5 s hs

theorem xWc_canon {layer b : Nat} (hB : 211 ≤ xA layer b) :
    StepCanon (xWc layer b) (xA layer b + 6) (XGood layer b) := by
  refine ⟨fun σ σ' hσ h => xGood_congr hB hσ h, fun i s v c o σ hc ho hco h1 h2 hg hv => ?_⟩
  obtain ⟨g1, g2, g3, g4, -⟩ := hg
  have hs2 : min s 2 < 3 := by have := Nat.min_le_right s 2; omega
  have hi57 : min i 57 < 58 := by have := Nat.min_le_right i 57; omega
  refine k64_fwd_canon σ hco (fun x hx => ?_) (by simp [xPad]; omega) (by simp [xPad]; omega) g4
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  have hv1 : v ≠ .n c := fun e => h1 ⟨0, by simp [xWc], by rw [e]; simp⟩
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨by rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega,
      by simp only [ne_eq, V.mk.injEq, true_and]; omega, g1⟩
  · exact ⟨by rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega,
      by simp only [ne_eq, V.mk.injEq, true_and]; omega, g2 _ hs2⟩
  · exact ⟨h2, hv1, hv⟩
  · exact ⟨by rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega,
      by simp only [ne_eq, V.mk.injEq, true_and]; omega, g3 _ hi57⟩

theorem xWc_sound {layer b : Nat} {σ : Val} (hg : XGood layer b σ) :
    StepSound rd σ (xWc layer b)
      (fun i s y => (hcell [σ (.n 1), σ (.n (xA layer b + 2 * min s 2 + 1)), y, σ (.n (138 + min i 57))]).1) := by
  intro i s v c o h
  exact k64_sound hg.2.2.2.1 h

theorem xWc_pow {layer b : Nat} {σ : Val} (hg : XGood layer b σ) :
    ∀ s < 10, σ ((xWc layer b).power s) = gen ^ s := by
  intro s hs
  simp only [xWc, Nat.min_eq_left (show s ≤ 9 by omega)]
  exact hg.2.2.2.2 s hs

theorem xWc_pw (layer b : Nat) (hB : 211 ≤ xA layer b) : ∀ j, NBv (xA layer b + 6) ((xWc layer b).power j) :=
  fun j => ⟨128 + min j 9, by have := Nat.min_le_right j 9; omega, rfl⟩

end
end LeanVM.Guest.B1.Sig
