module

public import FORS.SmallBudget.Contact.Signing

@[expose] public section

/-! **The end of the game for the contact potential, and the bound.** At the end, a recorded contact
at a revealed secret, or a near cover with a recorded contact, against a
completed table, has probability at most the weighted recorded contacts with their coefficients: a
contact has the chance of its weight, settled contacts pay one, and a near cover makes the capped
near potential one. Through the whole game the event is paid by the start potential and
`2^-128 (N rate) + payB` per FORS leaf query. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenBridge
open HiddenReveal PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

/-! ### The event -/

/-- **The event of A4** against a completed table: a recorded contact at a revealed secret, or a
near cover with a recorded contact. -/
def A4ev (K : Ctx) (root : Digest) (T : Coordinate → Digest) (s : State) (outcome : Outcome)
    (R : List Coordinate) : Prop :=
  (∃ index κ leaf, Coordinate.fors index κ leaf 0 ∈ R ∧ RecordedContactAt s T K index κ leaf) ∨
  ForsNearRecorded s T K root outcome R

/-- The final value of A4: the chance of a valid transcript and the event over the completion. -/
noncomputable def finalA4 (K : Ctx) (root : Digest) : FinalF := fun o R s =>
  o.elim 0 fun outcome =>
    Pr{let T ← completion s.known}[SigningTranscript.Valid outcome.2.1 ∧ A4ev K root T s outcome R]

/-- The final value of A4 is at most one. -/
theorem finalA4_le_one (K : Ctx) (root : Digest) (o : Option HiddenBridge.Outcome) (R : List Coordinate)
    (s : State) : finalA4 K root o R s ≤ 1 := by
  unfold finalA4
  cases o with
  | none => exact zero_le_one
  | some outcome =>
      rw [Option.elim_some]
      exact prEvent_le_one _

/-! ### The event is monotone in the cache -/

/-- A cached digest stays cached when the run caches more. -/
theorem cachedDigest_mono {s s' : State} (hext : Extends s s') {parameter : PublicParameter}
    {root : Digest} {message : Message} {randomness : Randomness} {digest : MessageDigest}
    (h : cachedDigest s.cache parameter root message randomness = some digest) :
    cachedDigest s'.cache parameter root message randomness = some digest := by
  unfold cachedDigest at h ⊢
  obtain ⟨w, h0, -⟩ := Option.map_eq_some_iff.mp h
  rwa [allSome_of_eq _ w fun call => hext.1 _ _ (allSome_some h0 call), ← h0]

/-- **A fresh cache entry keeps the event of A4**: every part of it is monotone in the cache and in
the guesses. -/
theorem a4ev_store (K : Ctx) (root : Digest) (T : Coordinate → Digest) (s : State) (outcome : Outcome)
    (R : List Coordinate) (x : HashInput) (u : HashOutput) (hx : s.cache x = none)
    (h : A4ev K root T s outcome R) : A4ev K root T (s.store x u) outcome R := by
  have hext := extends_store s x u hx
  have hrec : ∀ index κ leaf, RecordedContactAt s T K index κ leaf →
      RecordedContactAt (s.store x u) T K index κ leaf := by
    rintro index κ leaf ⟨v, ⟨w, ⟨hc, hi⟩, ht⟩, hr⟩
    exact ⟨v, ⟨w, ⟨hext.1 _ _ hc, hi⟩, ht⟩, hext.2.2 _ hr⟩
  rcases h with ⟨index, κ, leaf, hmem, hc⟩ | ⟨hvalid, digest, hdig, hland, hunsigned, κ, hc, hcov⟩
  · exact Or.inl ⟨index, κ, leaf, hmem, hrec _ _ _ hc⟩
  · exact Or.inr ⟨hvalid, digest, cachedDigest_mono hext hdig, hland, hunsigned, κ, hrec _ _ _ hc, hcov⟩

/-- The final value of A4 grows with a fresh cache entry. -/
theorem finalA4_store (K : Ctx) (root : Digest) (o : Option HiddenBridge.Outcome) (R : List Coordinate)
    (s : State) (x : HashInput) (u : HashOutput) (hx : s.cache x = none) :
    finalA4 K root o R s ≤ finalA4 K root o R (s.store x u) := by
  unfold finalA4
  cases o with
  | none => exact le_rfl
  | some outcome =>
      simp only [Option.elim]
      exact prEvent_mono_of_support _ _ _ fun T _ h => ⟨h.1, a4ev_store K root T s outcome R x u hx h.2⟩

/-! ### The end of the game -/

/-! ### The bound -/

end FORS.Security.ForsPotential
