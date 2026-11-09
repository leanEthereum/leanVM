/-
  LeanVM.Guest.B1.Gkr.Round

  One equality-mode sumcheck round of the bus GKR as the guest expands it: four stream words
  absorbed, a permutation, the challenge, the derived constant coefficient and the round
  polynomial at the challenge.
-/

module

public import LeanVM.Guest.B1.Gkr.Spec

/-!
# One GKR round (G:1879-1889, `gkr_rounds`, G:1130-1139)

A round `q` of `verify_bus_gkr`'s inner loop (and of `gkr_rounds`) from value `B`: four
`fs_next` of the words at `cursor·g^(4q + i)` (`c1 .. c4`), one `KECCAK` taking their cells over
the carried capacity, `challenge_from_state` of its output, the eq factor `e = pt[q]`,
`c0 = claim + e·Σ c`, the challenge stored at `pt[42 + q]`, and the next claim
`c0 + r·(c1 + r·(c2 + r·(c3 + r·c4)))`. `holds_gkRound`: it is one round of `gkrRun`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Round `q` from value `B`, on the cursor, the point row, the claim and the carried capacity. -/
def gkRoundT (B q : ℕ) (cur pt claimV : V) (cap : List V) : List Stmt :=
  fsNextT cur (4 * q) B ++ fsNextT cur (4 * q + 1) (B + 10) ++
    fsNextT cur (4 * q + 2) (B + 20) ++ fsNextT cur (4 * q + 3) (B + 30) ++
    [keccakA ([.n (B + 7), .n (B + 9), .n (B + 17), .n (B + 19), .n (B + 27), .n (B + 29),
        .n (B + 37), .n (B + 39)] ++ cap) ((List.range 13).map fun k ↦ .n (B + 40 + k))] ++
    challengeT (.n (B + 40)) (.n (B + 41)) (B + 53) ++
    [.atom (.load (.n (B + 60)) pt q), .atom (.add (.n (B + 61)) (.n B) (.n (B + 10))),
      .atom (.add (.n (B + 62)) (.n (B + 61)) (.n (B + 20))),
      .atom (.add (.n (B + 63)) (.n (B + 62)) (.n (B + 30))),
      .atom (.mul (.n (B + 64)) (.n (B + 60)) (.n (B + 63))),
      .atom (.add (.n (B + 65)) claimV (.n (B + 64))),
      .atom (.load (.n (B + 59)) pt (42 + q)),
      .atom (.mul (.n (B + 66)) (.n (B + 59)) (.n (B + 30))),
      .atom (.add (.n (B + 67)) (.n (B + 20)) (.n (B + 66))),
      .atom (.mul (.n (B + 68)) (.n (B + 59)) (.n (B + 67))),
      .atom (.add (.n (B + 69)) (.n (B + 10)) (.n (B + 68))),
      .atom (.mul (.n (B + 70)) (.n (B + 59)) (.n (B + 69))),
      .atom (.add (.n (B + 71)) (.n B) (.n (B + 70))),
      .atom (.mul (.n (B + 72)) (.n (B + 59)) (.n (B + 71))),
      .atom (.add (.n (B + 73)) (.n (B + 65)) (.n (B + 72)))]

theorem gkRoundT_noRet (B q : ℕ) (cur pt claimV : V) (cap : List V) :
    Stmt.noRetList (gkRoundT B q cur pt claimV cap) = true := by
  simp only [gkRoundT, tb_noRetList_append]; rfl

/-- The scalars of four words read, each with the tag `dsObserve`. -/
theorem absorbAll_four (cap : List E) (xs : List E) (hx : xs.length = 4) :
    ((⟨cap, []⟩ : Fs).absorbAll xs dsObserve) = ⟨cap, xs.map (·, dsObserve)⟩ := by
  rw [absorbAll_short _ _ _ (by simp [hx])]
  simp

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **One round**: it reads four words at the cursor, and its challenge, its next capacity and its
claim are one round of `gkrRun` from the carried capacity; the challenge is stored at
`pt[42 + q]` and the eq factor read at `pt[q]`. -/
theorem holds_gkRound {B q : ℕ} {cur pt claimV : V} {cap : List V}
    (h : Stmt.HoldsList C rd σ (gkRoundT B q cur pt claimV cap) True kret) :
    AllCanonical (cap.map σ) ∧
    ∃ xs : List E, xs.length = 4 ∧ (∀ i < 4, LoadHolds rd (σ cur) (4 * q + i) (xs.getD i 0)) ∧
      σ (.n (B + 59)) = ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).squeeze.1 ∧
      ((List.range 5).map fun k ↦ σ (.n (B + 48 + k))) =
        ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).squeeze.2.cap ∧
      LoadHolds rd (σ pt) (42 + q) (σ (.n (B + 59))) ∧
      ∃ e, LoadHolds rd (σ pt) q e ∧
        σ (.n (B + 73)) = polyEval ((σ claimV + e * sumE xs) :: xs) (σ (.n (B + 59))) := by
  unfold gkRoundT at h
  rw [tb_holdsList_append_noRet (by rfl), tb_holdsList_append_noRet (by rfl),
    tb_holdsList_append_noRet (by rfl), tb_holdsList_append_noRet (by rfl),
    tb_holdsList_append_noRet (by rfl), tb_holdsList_append_noRet (by rfl)] at h
  obtain ⟨⟨⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, hk⟩, hch⟩, ht⟩ := h
  rw [holds_fsNextT] at f0 f1 f2 f3
  rw [holds_challengeT] at hch
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, keccakA] at hk ht
  obtain ⟨hl0, pk0⟩ := f0.1
  obtain ⟨hl1, pk1⟩ := f1.1
  obtain ⟨hl2, pk2⟩ := f2.1
  obtain ⟨hl3, pk3⟩ := f3.1
  -- the permutation
  obtain ⟨-, -, hcan, hout⟩ := keccakA_perm (rd := rd) (σ := σ) hk
  have can : ∀ j, j = B + 7 ∨ j = B + 17 ∨ j = B + 27 ∨ j = B + 37 → IsCanonical128 (σ (.n j)) := by
    intro j hj
    apply hcan
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons]
    rcases hj with rfl | rfl | rfl | rfl <;> simp
  have cell : ∀ b, (FsPackOk σ (.n b) (b + 1) dsObserve) → IsCanonical128 (σ (.n (b + 7))) →
      σ (.n (b + 7)) = (Keccak.scalarCells (σ (.n b)) dsObserve).1 ∧
      σ (.n (b + 9)) = (Keccak.scalarCells (σ (.n b)) dsObserve).2 := fun b hpk hc => by
    have := fsPackT_cells hpk (by rw [show b + 1 + 6 = b + 7 by omega]; exact hc)
    rw [show b + 1 + 6 = b + 7 by omega, show b + 1 + 8 = b + 9 by omega] at this
    exact Prod.ext_iff.mp this
  obtain ⟨e07, e09⟩ := cell B pk0 (can _ (Or.inl rfl))
  obtain ⟨e17, e19⟩ := cell (B + 10) pk1 (by rw [show B + 10 + 7 = B + 17 by omega]; exact can _ (by simp))
  obtain ⟨e27, e29⟩ := cell (B + 20) pk2 (by rw [show B + 20 + 7 = B + 27 by omega]; exact can _ (by simp))
  obtain ⟨e37, e39⟩ := cell (B + 30) pk3 (by rw [show B + 30 + 7 = B + 37 by omega]; exact can _ (by simp))
  simp only [show B + 10 + 7 = B + 17 by omega, show B + 10 + 9 = B + 19 by omega,
    show B + 20 + 7 = B + 27 by omega, show B + 20 + 9 = B + 29 by omega,
    show B + 30 + 7 = B + 37 by omega, show B + 30 + 9 = B + 39 by omega] at e17 e19 e27 e29 e37 e39
  let xs := [σ (.n B), σ (.n (B + 10)), σ (.n (B + 20)), σ (.n (B + 30))]
  have hs := absorbAll_four (cap.map σ) xs rfl
  have hperm : ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).perm =
      permOf (([V.n (B + 7), V.n (B + 9), V.n (B + 17), V.n (B + 19), V.n (B + 27),
        V.n (B + 29), V.n (B + 37), V.n (B + 39)] ++ cap).map σ) := by
    rw [hs, perm_eq_cells _ (by simp [xs])]
    simp [xs, pendCells, e07, e09, e17, e19, e27, e29, e37, e39]
  set P := ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).perm with hP
  have hout' : ∀ k (hk : k < 13), σ (.n (B + 40 + k)) = cellsOfState P false ⟨k, hk⟩ := by
    intro k hk
    have := outs_eq hout ⟨k, hk⟩ (by simpa using hk)
    simpa [hperm] using this
  have hch' := challengeT_value hch.1 (hout' 0 (by omega)) (hout' 1 (by omega))
  rw [show B + 53 + 6 = B + 59 by omega] at hch'
  refine ⟨fun c hc => hcan c (by simp only [List.map_append, List.mem_append]; exact Or.inr hc),
    xs, rfl, fun i hi => ?_, ?_, ?_, ht.2.2.2.2.2.2.1, σ (.n (B + 60)), ht.1, ?_⟩
  · interval_cases i
    · exact hl0
    · exact hl1
    · exact hl2
    · exact hl3
  · rw [hch']; rfl
  · show _ = capOf P
    simp only [capOf, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append]
    rw [show B + 48 + 0 = B + 40 + 8 by omega, show B + 48 + 1 = B + 40 + 9 by omega,
      show B + 48 + 2 = B + 40 + 10 by omega, show B + 48 + 3 = B + 40 + 11 by omega,
      show B + 48 + 4 = B + 40 + 12 by omega, hout' 8 (by omega), hout' 9 (by omega),
      hout' 10 (by omega), hout' 11 (by omega), hout' 12 (by omega)]
    rfl
  · obtain ⟨-, e61, e62, e63, e64, e65, -, e66, e67, e68, e69, e70, e71, e72, e73⟩ := ht
    rw [e73, e72, e71, e70, e69, e68, e67, e66, e65, e64, e63, e62, e61]
    simp only [polyEval, List.foldr, sumE, List.foldl, xs]
    ring

end Sem

end
end LeanVM.Guest.B1.Tables
