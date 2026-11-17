/-
  LeanVM.Guest.B1.Gkr.Round

  One equality-mode sumcheck round of the bus GKR as the guest expands it: four stream words
  absorbed, a permutation, the challenge, the derived constant coefficient and the round
  polynomial at the challenge.
-/

module

public import LeanVM.Guest.B1.Gkr.Spec

/-!
# One GKR round (`gkr_rounds`)

A round `q` of `verify_bus_gkr`'s inner loop (and of `gkr_rounds`) from value `B`: four
`fs_next` of the words at `cursor·g^(4q + i)` (`c1 .. c4`, three values each), one `KECCAK`
taking their cells over the carried capacity (the round's grind, of `0` bits, is this
permutation), `challenge_from_state` of its output, the eq factor `e = pt[q]`,
`c0 = claim + e·Σ c`, the challenge stored at `pt[42 + q]`, and the next claim
`c0 + r·(c1 + r·(c2 + r·(c3 + r·c4)))`. `holds_gkRound`: it is one round of `gkrRun`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Round `q` from value `B`, on the cursor, the point row, the claim and the carried capacity. -/
def gkRoundT (B q : ℕ) (cur pt claimV : V) (cap : List V) : List Stmt :=
  fsNextT cur (4 * q) B ++ fsNextT cur (4 * q + 1) (B + 3) ++
    fsNextT cur (4 * q + 2) (B + 6) ++ fsNextT cur (4 * q + 3) (B + 9) ++
    [keccakA ([.n (B + 1), .n (B + 2), .n (B + 4), .n (B + 5), .n (B + 7), .n (B + 8),
        .n (B + 10), .n (B + 11)] ++ cap) ((List.range 13).map fun k ↦ .n (B + 12 + k))] ++
    challengeT (.n (B + 12)) (B + 25) ++
    [.atom (.load (.n (B + 26)) pt q), .atom (.add (.n (B + 27)) (.n B) (.n (B + 3))),
      .atom (.add (.n (B + 28)) (.n (B + 27)) (.n (B + 6))),
      .atom (.add (.n (B + 29)) (.n (B + 28)) (.n (B + 9))),
      .atom (.mul (.n (B + 30)) (.n (B + 26)) (.n (B + 29))),
      .atom (.add (.n (B + 31)) claimV (.n (B + 30))),
      .atom (.load (.n (B + 25)) pt (42 + q)),
      .atom (.mul (.n (B + 32)) (.n (B + 25)) (.n (B + 9))),
      .atom (.add (.n (B + 33)) (.n (B + 6)) (.n (B + 32))),
      .atom (.mul (.n (B + 34)) (.n (B + 25)) (.n (B + 33))),
      .atom (.add (.n (B + 35)) (.n (B + 3)) (.n (B + 34))),
      .atom (.mul (.n (B + 36)) (.n (B + 25)) (.n (B + 35))),
      .atom (.add (.n (B + 37)) (.n B) (.n (B + 36))),
      .atom (.mul (.n (B + 38)) (.n (B + 25)) (.n (B + 37))),
      .atom (.add (.n (B + 39)) (.n (B + 31)) (.n (B + 38)))]

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
    ∃ xs : List E, xs.length = 4 ∧ (∀ i < 4, LoadHolds rd (σ cur) (4 * q + i) (xs.getD i 0)) ∧
      σ (.n (B + 25)) = ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).squeeze.1 ∧
      ((List.range 5).map fun k ↦ σ (.n (B + 20 + k))) =
        ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).squeeze.2.cap ∧
      LoadHolds rd (σ pt) (42 + q) (σ (.n (B + 25))) ∧
      ∃ e, LoadHolds rd (σ pt) q e ∧
        σ (.n (B + 39)) = polyEval ((σ claimV + e * sumE xs) :: xs) (σ (.n (B + 25))) := by
  unfold gkRoundT at h
  rw [tb_holdsList_append_noRet (by rfl), tb_holdsList_append_noRet (by rfl),
    tb_holdsList_append_noRet (by rfl), tb_holdsList_append_noRet (by rfl),
    tb_holdsList_append_noRet (by rfl), tb_holdsList_append_noRet (by rfl)] at h
  obtain ⟨⟨⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, hk⟩, hch⟩, ht⟩ := h
  rw [holds_fsNextT] at f0 f1 f2 f3
  simp only [challengeT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, keccakA] at hk hch ht
  obtain ⟨hl0, pk0⟩ := f0.1
  obtain ⟨hl1, pk1⟩ := f1.1
  obtain ⟨hl2, pk2⟩ := f2.1
  obtain ⟨hl3, pk3⟩ := f3.1
  -- the permutation
  obtain ⟨-, -, hout⟩ := keccakA_perm (rd := rd) (σ := σ) hk
  have cell : ∀ b, (FsPackOk σ (.n b) (b + 1) dsObserve) →
      σ (.n (b + 1)) = (Keccak.scalarCells (σ (.n b)) dsObserve).1 ∧
      σ (.n (b + 2)) = (Keccak.scalarCells (σ (.n b)) dsObserve).2 := fun b hpk =>
    Prod.ext_iff.mp (fsPackT_cells hpk)
  obtain ⟨e01, e02⟩ := cell B pk0
  obtain ⟨e04, e05⟩ := cell (B + 3) pk1
  obtain ⟨e07, e08⟩ := cell (B + 6) pk2
  obtain ⟨e10, e11⟩ := cell (B + 9) pk3
  simp only [show B + 3 + 1 = B + 4 by omega, show B + 3 + 2 = B + 5 by omega,
    show B + 6 + 1 = B + 7 by omega, show B + 6 + 2 = B + 8 by omega,
    show B + 9 + 1 = B + 10 by omega, show B + 9 + 2 = B + 11 by omega] at e04 e05 e07 e08 e10 e11
  let xs := [σ (.n B), σ (.n (B + 3)), σ (.n (B + 6)), σ (.n (B + 9))]
  have hs := absorbAll_four (cap.map σ) xs rfl
  have hperm : ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).perm =
      permOf (([V.n (B + 1), V.n (B + 2), V.n (B + 4), V.n (B + 5), V.n (B + 7),
        V.n (B + 8), V.n (B + 10), V.n (B + 11)] ++ cap).map σ) := by
    rw [hs, perm_eq_cells _ (by simp [xs])]
    simp [xs, pendCells, e01, e02, e04, e05, e07, e08, e10, e11]
  set P := ((⟨cap.map σ, []⟩ : Fs).absorbAll xs dsObserve).perm with hP
  have hout' : ∀ k (hk : k < 13), σ (.n (B + 12 + k)) = cellsOfState P false ⟨k, hk⟩ := by
    intro k hk
    have := outs_eq hout ⟨k, hk⟩ (by simpa using hk)
    simpa [hperm] using this
  have hch' : σ (.n (B + 25)) = challengeOf P := by
    rw [hch, show B + 12 = B + 12 + 0 by rfl, hout' 0 (by omega), Keccak.challengeOf_cells]
    rfl
  refine ⟨xs, rfl, fun i hi => ?_, ?_, ?_, ht.2.2.2.2.2.2.1, σ (.n (B + 26)), ht.1, ?_⟩
  · interval_cases i
    · exact hl0
    · exact hl1
    · exact hl2
    · exact hl3
  · rw [hch']; rfl
  · show _ = capOf P
    simp only [capOf, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append]
    rw [show B + 20 + 0 = B + 12 + 8 by omega, show B + 20 + 1 = B + 12 + 9 by omega,
      show B + 20 + 2 = B + 12 + 10 by omega, show B + 20 + 3 = B + 12 + 11 by omega,
      show B + 20 + 4 = B + 12 + 12 by omega, hout' 8 (by omega), hout' 9 (by omega),
      hout' 10 (by omega), hout' 11 (by omega), hout' 12 (by omega)]
    rfl
  · obtain ⟨-, e27, e28, e29, e30, e31, -, e32, e33, e34, e35, e36, e37, e38, e39⟩ := ht
    rw [e39, e38, e37, e36, e35, e34, e33, e32, e31, e30, e29, e28, e27]
    simp only [polyEval, List.foldr, sumE, List.foldl, xs]
    ring

end Sem

end
end LeanVM.Guest.B1.Tables
