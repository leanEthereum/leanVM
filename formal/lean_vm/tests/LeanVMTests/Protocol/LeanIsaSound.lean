import LeanVM.Protocol.LeanIsa.Sound

/-!
# Tests: the adaptor, soundness

* **The statement, by type**, at the BLAKE2s inhabitant of `FlockSpec`: admissible sizes and
  `M3Holds` of the leanISA instance give `SatisfiedBy` of the witness read off the stack, with no
  other hypothesis. Its BLAKE2s conjunct alone needs only the Flock clause.
* **The bus as one bus.** On any witness of the ensemble, the two sides' tuples are one multiset
  exactly when the three channel pairs balance, and the instance's balance is that of a witness
  agreeing with the stack.
* **The relation's clauses are equivalences**, the direction this module does not use included:
  the counts, on a stack and a witness that agree.
* **The limbs are read at the deployed slots.** At a size vector of the instance tests, the
  pinned Rust places `QFLOCK` at offset `4980736`, and limb `k` of row `x` is read at the stack's
  cell `4980736 + slot k + 256 x`, with the slots of `hash_flock.rs:86-108`; a transposed strided
  read would fail this.
-/

namespace LeanVMTests.Protocol.LeanIsaSound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa
open Air.Flat (EnsembleWitness)

/-- The adaptor's soundness at the BLAKE2s inhabitant. -/
example (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (input : PublicInput)
    (hs : s.Admissible prog)
    (h : M3Holds (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog s) input q) :
    SatisfiedBy prog input (witnessOf Blake2sFlock.blake2sFlockSpec prog s q) :=
  satisfiedBy_witnessOf _ prog s q hs h

/-- The BLAKE2s validity needs the Flock clause alone. -/
example (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))
    (h : (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog s).aux q) :
    Blake2sRowsValid (witnessOf Blake2sFlock.blake2sFlockSpec prog s q) :=
  blake2sRowsValid_witnessOf _ prog s q h

/-- The bus as one bus, on any witness. -/
example (prog : Program) (w : EnsembleWitness (leanIsaEnsemble prog)) :
    (sideTuples w .push).Perm (sideTuples w .pull) ↔
      BalancedPair w StatePull.toRaw StatePush.toRaw ∧ BalancedPair w MemPull.toRaw MemPush.toRaw ∧
        BalancedPair w BytecodePull.toRaw BytecodePush.toRaw := by
  rw [balanced_iff]
  exact ⟨fun h ↦ ⟨h 0, h 1, h 2⟩, fun h k ↦ by fin_cases k; exacts [h.1, h.2.1, h.2.2]⟩

/-- The counts, both ways, on a stack and a witness that agree. -/
example (F : FlockSpec) (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))
    (w : EnsembleWitness (leanIsaEnsemble prog)) (h : Agrees F s q w) :
    CountsNonzero w ↔ (leanIsaInstance F prog s).CountsNonzero q :=
  countsNonzero_iff h

/-! ## The limbs' cells -/

/-- Four `XOR` instructions. -/
def prog4 : Program := ⟨2, by decide, fun _ ↦ .xor 0 0 0⟩

/-- The second size vector of the instance tests, the `BLAKE2S` table of eight rows. -/
def s₂ : Sizes := ⟨18, by decide, ![2 ^ 2, 2 ^ 18, 2 ^ 5, 2 ^ 0, 2 ^ 7, 2 ^ 3]⟩

#guard (List.finRange 18).all fun k ↦ (List.finRange (2 ^ s₂.τ 5)).all fun x ↦
  (boolIndex ((layout prog4 s₂ Blake2sFlock.blake2sFlockSpec.slot).extend (limbCol k)
      (boolVec x))).val ==
    4980736 + [10, 11, 12, 13, 14, 15, 16, 17, 4, 5, 6, 7, 0, 1, 2, 3, 18, 19][k]! + 256 * x

end LeanVMTests.Protocol.LeanIsaSound
