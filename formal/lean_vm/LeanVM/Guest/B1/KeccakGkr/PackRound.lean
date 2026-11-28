/-
  LeanVM.Guest.B1.KeccakGkr.PackRound

  An equality-mode round of a layer's pack and segment, as the guest's statements compute it, and
  rounds chained into `packRunF`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Plain
public import LeanVM.Guest.B1.KeccakGkr.LayerSpec

/-!
# An equality-mode round

`packRoundT`: round `q` reads its coordinate `prev_point[q]` and the two coefficients `g₁`, `g₂`
(`fs_next`), squeezes the challenge from the capacity with four zero rate cells (`sq2_atoms`),
stores it at `point[q]` and computes the next normalized claim `claim + (r + c)·g₁ + (r + c²)·g₂`
(`packRound_facts`: `eqRound`). `EqChain`: rounds chained by `eqRound`, which `packRunF` runs
(`packRunF_of_chain`). From the archive's `PackLoop` (tag `formal-bus-archive`), whose loops
`layer_rounds` replaced.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Two words absorbed and a squeeze -/

/-- **A squeeze of two read words**: `c₁`'s and `c₂`'s `fs_next` cells (`a + 1`, `a + 2`,
`a + 4`, `a + 5`), four zeros and the capacity in one `KECCAK` atom: the challenge its output
`o` (`challenge_from_state`) and the outputs `o + 8 .. o + 12` are
`(⟨cap, []⟩.absorbAll [c₁, c₂]).squeeze`'s. -/
theorem sq2_atoms {a o : ℕ} {zs capV : List V} {cap : List E}
    (p1 : FsPackOk σ (.n a) (a + 1) dsObserve) (p2 : FsPackOk σ (.n (a + 3)) (a + 3 + 1) dsObserve)
    (hk : (Atom.keccak ([V.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV)
      ((List.range 13).map fun k ↦ .n (o + k)) false false).Holds rd σ)
    (hz : zs.map σ = [0, 0, 0, 0])
    (hc : capV.map σ = cap) :
    σ (.n o) = ((⟨cap, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 3))] dsObserve).squeeze.1 ∧
      [σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)), σ (.n (o + 12))] =
        ((⟨cap, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 3))] dsObserve).squeeze.2.cap := by
  have s0 := fsNext_scalar p1
  have s2 := fsNext_scalar p2
  have habs : (⟨cap, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 3))] dsObserve =
      ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)]⟩ := rfl
  have hin : ([V.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV).map σ =
      rateOf [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)] ++ cap := by
    rw [rateOf_two, ← s0, ← s2, List.map_append, List.map_append, hz, hc]
    rfl
  have := squeeze_atom (s := ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)]⟩) hk hin
    (b := o) rfl
  simp only [range13_map, List.drop, List.map_cons, List.map_nil] at this
  rw [habs]
  exact ⟨this.1, this.2⟩

/-! ## Rounds chained -/

/-- The capacity cells from `b`. -/
def cap5 (b : ℕ) : List V := [.n b, .n (b + 1), .n (b + 2), .n (b + 3), .n (b + 4)]

/-- Rounds chained by `eqRound`: from the normalized claim `cl` and capacity `cap`, the coordinates `rs` and messages `ms` give the challenges `chs`, final claim `cl'` and capacity `cap'`. -/
def EqChain : List E → List (E × E) → E → List E → List E → E → List E → Prop
  | [], [], cl, cap, chs, cl', cap' => chs = [] ∧ cl' = cl ∧ cap' = cap
  | r :: rs, (g1, g2) :: ms, cl, cap, chs, cl', cap' =>
      ∃ (ch cl1 : E) (cap1 chs' : List E),
        eqRound ⟨cap, []⟩ g1 g2 r cl = (ch, cl1, ⟨cap1, []⟩) ∧ chs = ch :: chs' ∧
          EqChain rs ms cl1 cap1 chs' cl' cap'
  | _, _, _, _, _, _, _ => False

/-- A round of `packRunF` is `eqRound`. -/
theorem packRunF_cons (r g1 g2 v : E) (rs : List E) (ms : List (E × E)) (s : Fs) :
    packRunF (r :: rs) ((g1, g2) :: ms) v s =
      (((packRunF rs ms (eqRound s g1 g2 r v).2.1 (eqRound s g1 g2 r v).2.2).1.1,
        (eqRound s g1 g2 r v).1 ::
          (packRunF rs ms (eqRound s g1 g2 r v).2.1 (eqRound s g1 g2 r v).2.2).1.2),
        (packRunF rs ms (eqRound s g1 g2 r v).2.1 (eqRound s g1 g2 r v).2.2).2) := by
  have e : polyEval [v + r * sumE [g1, g2], g1, g2]
      (s.absorbAll [g1, g2] dsObserve).squeeze.1 = (eqRound s g1 g2 r v).2.1 := by
    simp only [eqRound, polyEval, sumE, List.foldl, List.foldr]
    ring
  simp only [packRunF]
  rw [e]
  rfl

/-- `packRunF` runs a chain. -/
theorem packRunF_of_chain : ∀ (rs : List E) (ms : List (E × E)) (cl : E) (cap chs : List E)
    (cl' : E) (cap' : List E), EqChain rs ms cl cap chs cl' cap' →
    packRunF rs ms cl ⟨cap, []⟩ = ((cl', chs), ⟨cap', []⟩)
  | [], [], _, _, _, _, _, h => by
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | r :: rs, (g1, g2) :: ms, cl, cap, chs, cl', cap', h => by
    obtain ⟨ch, cl1, cap1, chs', he, rfl, hc⟩ := h
    rw [packRunF_cons, he]
    simp only
    rw [packRunF_of_chain rs ms cl1 cap1 chs' cl' cap' hc]
  | [], _ :: _, _, _, _, _, _, h => h.elim
  | _ :: _, [], _, _, _, _, _, h => h.elim

theorem packEqChain_length : ∀ {rs : List E} {ms : List (E × E)} {cl : E} {cap chs : List E}
    {cl' : E} {cap' : List E}, EqChain rs ms cl cap chs cl' cap' →
    ms.length = rs.length ∧ chs.length = rs.length
  | [], [], _, _, _, _, _, h => by obtain ⟨rfl, -⟩ := h; simp
  | _ :: _, (_, _) :: _, _, _, _, _, _, h => by
    obtain ⟨_, _, _, _, -, rfl, hc⟩ := h
    have := packEqChain_length hc
    simp [this.1, this.2]
  | [], _ :: _, _, _, _, _, _, h => h.elim
  | _ :: _, [], _, _, _, _, _, h => h.elim

/-! ## A round of the eight-round loop -/

/-- Round `q` reads its coordinate and two coefficients, squeezes the challenge and stores the next normalized claim. -/
def packRoundT (pp cu pt : V) (q b c : ℕ) (pre : List Stmt) (zs cap : List V) (cl : V) :
    List Stmt :=
  [.atom (.load (.n b) pp q)] ++ fsNextT cu (2 * q) (b + 1) ++ fsNextT cu (2 * q + 1) (b + 4) ++
    pre ++
  [keccakA ([.n (b + 2), .n (b + 3), .n (b + 5), .n (b + 6)] ++ zs ++ cap)
    ((List.range 13).map fun k ↦ .n (c + k))] ++
  [.atom (.load (.n c) pt q), .atom (.add (.n (c + 13)) (.n b) (.n c)),
    .atom (.mul (.n (c + 14)) (.n (c + 13)) (.n (b + 1))),
    .atom (.add (.n (c + 15)) cl (.n (c + 14))),
    .atom (.mul (.n (c + 16)) (.n c) (.n c)),
    .atom (.add (.n (c + 17)) (.n b) (.n (c + 16))),
    .atom (.mul (.n (c + 18)) (.n (c + 17)) (.n (b + 4))),
    .atom (.add (.n (c + 19)) (.n (c + 15)) (.n (c + 18)))]

theorem fsNextT_atoms (cu : V) (off b : ℕ) : AllAtoms (fsNextT cu off b) := by
  intro s hs
  simp only [fsNextT, fsPackT, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem challengeT_atoms (s0 : V) (b : ℕ) : AllAtoms (challengeT s0 b) := by
  intro s hs
  simp only [challengeT, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  exact ⟨_, rfl⟩

theorem fsNextT_facts {cu : V} {off b : ℕ} (H : ∀ a, Stmt.atom a ∈ fsNextT cu off b → a.Holds rd σ) :
    LoadHolds rd (σ cu) off (σ (.n b)) ∧ FsPackOk σ (.n b) (b + 1) dsObserve :=
  ((holds_fsNextT (C := fun _ _ _ ↦ True) cu off b True (fun _ ↦ False)).1
    ((holdsList_atoms (fsNextT_atoms cu off b) True _).2 ⟨H, trivial⟩)).1

theorem challengeT_facts {s0 : V} {b : ℕ}
    (H : ∀ a, Stmt.atom a ∈ challengeT s0 b → a.Holds rd σ) : ChallengeOk σ s0 b :=
  ((holds_challengeT (C := fun _ _ _ ↦ True) s0 b True (fun _ ↦ False)).1
    ((holdsList_atoms (challengeT_atoms s0 b) True _).2 ⟨H, trivial⟩)).1

/-- **A round's facts**: the coordinate and the two words read, and `eqRound` of them on the
capacity: the challenge (stored at `pt[q]`), the normalized claim and the capacity after. -/
theorem packRound_facts {pp cu pt : V} {q b c : ℕ} {pre : List Stmt} {zs cap : List V} {cl : V}
    (H : ∀ a, Stmt.atom a ∈ packRoundT pp cu pt q b c pre zs cap cl → a.Holds rd σ)
    (hz : zs.map σ = [0, 0, 0, 0]) :
    LoadHolds rd (σ pp) q (σ (.n b)) ∧ LoadHolds rd (σ cu) (2 * q) (σ (.n (b + 1))) ∧
      LoadHolds rd (σ cu) (2 * q + 1) (σ (.n (b + 4))) ∧ LoadHolds rd (σ pt) q (σ (.n c)) ∧
      eqRound ⟨cap.map σ, []⟩ (σ (.n (b + 1))) (σ (.n (b + 4))) (σ (.n b)) (σ cl) =
        (σ (.n c), σ (.n (c + 19)), ⟨(cap5 (c + 8)).map σ, []⟩) := by
  have m1 : ∀ a, Stmt.atom a ∈ fsNextT cu (2 * q) (b + 1) → a.Holds rd σ := fun a ha ↦
    H a (by simp only [packRoundT, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr ha)))))
  have m2 : ∀ a, Stmt.atom a ∈ fsNextT cu (2 * q + 1) (b + 4) → a.Holds rd σ := fun a ha ↦
    H a (by simp only [packRoundT, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr ha))))
  have hk : (Atom.keccak ([V.n (b + 2), .n (b + 3), .n (b + 5), .n (b + 6)] ++ zs ++ cap)
      ((List.range 13).map fun k ↦ .n (c + k)) false false).Holds rd σ :=
    H _ (by simp [packRoundT, keccakA])
  have l0 : LoadHolds rd (σ pp) q (σ (.n b)) := H (.load (.n b) pp q) (by simp [packRoundT])
  obtain ⟨l1, p1⟩ := fsNextT_facts m1
  obtain ⟨l2, p2⟩ := fsNextT_facts m2
  have q0 := sq2_atoms (a := b + 1) (o := c) (zs := zs) (capV := cap) (cap := cap.map σ) p1 p2
    (by simpa [Nat.add_assoc] using hk) hz rfl
  have l3 : LoadHolds rd (σ pt) q (σ (.n c)) := H (.load (.n c) pt q) (by simp [packRoundT])
  have e14 : σ (.n (c + 13)) = σ (.n b) + σ (.n c) := H (.add (.n (c + 13)) (.n b) (.n c)) (by simp [packRoundT])
  have e17 : σ (.n (c + 14)) = σ (.n (c + 13)) * σ (.n (b + 1)) := H (.mul (.n (c + 14)) (.n (c + 13)) (.n (b + 1))) (by simp [packRoundT])
  have e18 : σ (.n (c + 15)) = σ cl + σ (.n (c + 14)) := H (.add (.n (c + 15)) cl (.n (c + 14))) (by simp [packRoundT])
  have e19 : σ (.n (c + 16)) = σ (.n c) * σ (.n c) := H (.mul (.n (c + 16)) (.n c) (.n c)) (by simp [packRoundT])
  have e20 : σ (.n (c + 17)) = σ (.n b) + σ (.n (c + 16)) := H (.add (.n (c + 17)) (.n b) (.n (c + 16))) (by simp [packRoundT])
  have e21 : σ (.n (c + 18)) = σ (.n (c + 17)) * σ (.n (b + 4)) := H (.mul (.n (c + 18)) (.n (c + 17)) (.n (b + 4))) (by simp [packRoundT])
  have e22 : σ (.n (c + 19)) = σ (.n (c + 15)) + σ (.n (c + 18)) := H (.add (.n (c + 19)) (.n (c + 15)) (.n (c + 18))) (by simp [packRoundT])
  have hsq : ((⟨cap.map σ, []⟩ : Fs).absorbAll [σ (.n (b + 1)), σ (.n (b + 4))] dsObserve).squeeze =
      (σ (.n c), ⟨(cap5 (c + 8)).map σ, []⟩) := by
    refine Prod.ext q0.1.symm ?_
    have h2 := q0.2
    simp only [cap5, List.map_cons, List.map_nil, Nat.add_assoc, Nat.reduceAdd] at h2 ⊢
    rw [h2]
    rfl
  refine ⟨l0, l1, l2, l3, ?_⟩
  simp only [eqRound]
  rw [hsq]
  simp only [Prod.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  rw [e22, e21, e20, e19, e18, e17, e14]

end
end LeanVM.Guest.B1.VerifySub
