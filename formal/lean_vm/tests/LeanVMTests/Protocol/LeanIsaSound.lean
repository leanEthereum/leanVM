import LeanVM.Protocol.LeanIsa.Sound

/-!
# Tests: the adaptor, soundness

* **The statement, by type**: admissible sizes and `M3Holds` of the leanISA instance give
  `SatisfiedBy` of the witness read off the stack, with no other hypothesis. Its `KECCAK` conjunct
  alone needs only the Keccak clause (the output lanes, derived as the second twelve rounds of the
  committed middle state, are Keccak-f[1600] of the input lanes when the middle state is the first
  twelve rounds of them).
* **The bus as one bus.** On any witness of the ensemble, the two sides' tuples are one multiset
  exactly when the three channel pairs balance, and the instance's balance is that of a witness
  agreeing with the stack.
* **The relation's clauses are equivalences**, the direction this module does not use included:
  the counts, on a stack and a witness that agree.
* **The input lanes are read at the deployed cells.** At a size vector of the instance tests, the
  pinned verifier's `build_layout` places `QKECCAK` at offset `4194304` with a `KECCAK` table of
  `2^9` rows, and input lane `l` of row `x` is read at the stack's cell
  `4194304 + 512 l + x` (the lane is `QKECCAK`'s column at slot `l`, `slot << kappa`,
  `crates/verifier/src/layout.rs:531-553`);
  a read with the slot in the low coordinates would fail this.
-/

namespace LeanVMTests.Protocol.LeanIsaSound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa
open Air.Flat (EnsembleWitness)

/-- The adaptor's soundness. -/
example (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s)) (input : PublicInput)
    (hs : s.Admissible prog) (h : M3Holds (leanIsaInstance prog s) input q) :
    SatisfiedBy prog input (witnessOf prog s q) :=
  satisfiedBy_witnessOf prog s q hs h

/-- The `KECCAK` validity needs the Keccak clause alone. -/
example (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s))
    (h : (leanIsaInstance prog s).aux q) : KeccakRowsValid (witnessOf prog s q) :=
  keccakRowsValid_witnessOf prog s q h

/-- The bus as one bus, on any witness. -/
example (prog : LeanIsaProgram) (κ : ℕ) (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (sideTuples w .push).Perm (sideTuples w .pull) ↔
      BalancedPair w StatePull.toRaw StatePush.toRaw ∧ BalancedPair w MemPull.toRaw MemPush.toRaw ∧
        BalancedPair w BytecodePull.toRaw BytecodePush.toRaw := by
  rw [balanced_iff]
  exact ⟨fun h ↦ ⟨h 0, h 1, h 2⟩, fun h k ↦ by fin_cases k; exacts [h.1, h.2.1, h.2.2]⟩

/-- The counts, both ways, on a stack and a witness that agree. -/
example (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s)) (κ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog κ)) (h : Agrees s q w) :
    CountsNonzero w ↔ (leanIsaInstance prog s).CountsNonzero q :=
  countsNonzero_iff h

/-! ## The input lanes' cells -/

/-- Four `XOR` instructions. -/
def prog4 : LeanIsaProgram := ⟨2, by decide, fun _ ↦ .xor 0 0 0⟩

/-- The second size vector of the instance tests, the `KECCAK` table at its floor `2^9`. -/
def s₂ : Sizes := ⟨18, by decide, ![2 ^ 2, 2 ^ 18, 2 ^ 5, 2 ^ 0, 2 ^ 7, 2 ^ 3]⟩

#guard s₂.τ 5 = 9
#guard (List.finRange 25).all fun l ↦ (List.finRange (2 ^ s₂.τ 5)).all fun x ↦
  (boolIndex ((layout prog4 s₂).extend (inCol l) (boolVec x))).val ==
    4194304 + 512 * l.val + x.val

end LeanVMTests.Protocol.LeanIsaSound
