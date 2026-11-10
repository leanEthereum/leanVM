/-
  LeanVM.Guest.Batch.Prog

  The batching as a program of the verifier language: the count, the children's claims and the
  sumcheck's messages are prover scalars, the lambdas and the sumcheck's challenges are samples.
-/

module

public import LeanVM.Guest.Batch.Sound
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# The batching as a verifier program

`Node.batch` runs on the duplex sponge of the verifier language: `observe` is a read's
absorption (tag `1`) and `sample` a sample's squeeze. So the batching is a program
`boundedBatchingProgram M bytecode` (`LeanVM.Protocol.Compile.VerifierProgram`; defined in `Statement/LeanVmGuestCompleteness.lean`,
with the batching's end statement `BatchingSound`) whose prover sends the count `g^n` and
three zeros, each child's words and the zeros to a whole rate (`childCells`), the sumcheck's
messages and the final value, and whose challenges are the lambdas and the sumcheck's challenges.
It reads the count as the `n < M` with `g^n` the first scalar (`countOf`), checks the padding,
the final claim, and that the deferred claim holds of `bytecode`, then accepts.

`runProof_batchAny`: run with Keccak-256 and Keccak-f[1600] from the batching's seed
(`batchSeed`), on the stream of the count, children of the bytecode's shapes, the rounds of its
size and the final value (`batchingStream`), it accepts exactly where `batch` defers a claim that
holds. So the random-oracle theorem of this program (`LeanVM.Guest.Batch.Rom`) is the batching's,
Keccak-256 and Keccak-f[1600] modelled as random oracles. The final value is read (absorbed)
after the last challenge, where `batch` takes it from the hints: the absorption changes no
challenge.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The cells -/

theorem padRate_eq (ws : List E) : padToRate ws = ws ++ List.replicate (zerosToWholeRate ws.length) 0 := rfl

theorem length_words {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c) :
    c.words.length = childWordCount (Nat.log2 bytecode.length) := by
  obtain ⟨h1, h2⟩ := hc
  simp only [DeferredClaim.HasBytecodeShape] at h2
  simp [ChildClaims.words, DeferredClaim.cells, childWordCount, h1, h2]
  omega

/-- A child of the bytecode's shapes has `childWordCount` words, then the padding. -/
theorem childCells_eq {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c) :
    childCells c = c.words ++
      List.replicate (zerosToWholeRate (childWordCount (Nat.log2 bytecode.length))) 0 := by
  rw [childCells, padRate_eq, length_words hc]

theorem length_childCells {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c) :
    (childCells c).length =
      childWordCount (Nat.log2 bytecode.length) + zerosToWholeRate (childWordCount (Nat.log2 bytecode.length)) := by
  rw [childCells_eq hc, List.length_append, length_words hc, List.length_replicate]

/-- A child of the bytecode's shapes is read back off its words. -/
theorem parseChild_words {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c) :
    parseChild (Nat.log2 bytecode.length) c.words = some c := by
  obtain ⟨pi, ⟨bp, bv⟩, ⟨bp', bv'⟩⟩ := c
  obtain ⟨h1, h2⟩ := hc
  simp only [DeferredClaim.HasBytecodeShape] at h1 h2
  generalize Nat.log2 bytecode.length = nB at *
  subst h1
  simp [parseChild, ChildClaims.words, DeferredClaim.cells,
    digestOfScalars_digestScalars, List.getD_eq_getElem?_getD, List.drop_append, h2, List.drop_eq_nil_of_le]

/-- The padded words are read back off. -/
theorem parseChild_childCells {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c) :
    parseChild (Nat.log2 bytecode.length) (childCells c) = some c := by
  rw [← parseChild_words hc, childCells_eq hc]
  obtain ⟨pi, ⟨bp, bv⟩, ⟨bp', bv'⟩⟩ := c
  obtain ⟨h1, h2⟩ := hc
  simp only [DeferredClaim.HasBytecodeShape] at h1 h2
  generalize Nat.log2 bytecode.length = nB at *
  subst h1
  simp [parseChild, ChildClaims.words, DeferredClaim.cells,
    List.getD_eq_getElem?_getD, List.drop_append, h2,
    List.drop_eq_nil_of_le]

theorem drop_childCells {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c) :
    (childCells c).drop (childWordCount (Nat.log2 bytecode.length)) =
      List.replicate (zerosToWholeRate (childWordCount (Nat.log2 bytecode.length))) 0 := by
  rw [childCells_eq hc, List.drop_left' (length_words hc)]

/-- The count's power is read back below `M ≤ 2^64 - 1`. -/
theorem countOf_gpow {M n : ℕ} (hM : M ≤ 2 ^ 64 - 1) (hn : n < M) :
    childCountOfGeneratorPower M (Verifier.gpow n) = some n := by
  have hex : ∃ m, m < M ∧ Verifier.gpow m = Verifier.gpow n := ⟨n, hn, rfl⟩
  rw [childCountOfGeneratorPower, dite_eq_left hex, Option.some.injEq]
  generalize hk : Nat.find hex = k at *
  obtain ⟨hlt, hs⟩ : k < M ∧ Verifier.gpow k = Verifier.gpow n := hk ▸ Nat.find_spec hex
  have hK : ∀ m, Verifier.gpow m = ofK (Parameters.addressOfIndex m) := fun m ↦ by
    show gen ^ m = algebraMap K E (g ^ m)
    rw [map_pow]
    rfl
  rw [hK k, hK n] at hs
  exact gpow_injOn (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) (ofK_injective hs)

theorem headCells_eq (n : ℕ) : childCountCells n = [Verifier.gpow n, 0, 0, 0] := rfl

/-! ## The compiled run, piece by piece -/

/-- The deployed compiled run: Keccak-256 and Keccak-f[1600]. -/
abbrev runD {α : Type} (p : VerifierProgram α) (s : VerifierProgramState) : Option (α ×
    VerifierProgramState) :=
  Id.run (runWithHash keccak256 keccakF1600 p s)

/-- The compiled run of a sequence: the first program's, then the continuation's. -/
theorem runD_bind {α β : Type} (f : α → VerifierProgram β) :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState), runD (p.bind f) s =
      match runD p s with
      | some (a, s') => runD (f a) s'
      | none => none
  | .ret a, s => rfl
  | .fail, s => rfl
  | .read k, ⟨sp, [], os, roots⟩ => rfl
  | .read k, ⟨sp, x :: xs, os, roots⟩ => runD_bind f (k x) _
  | .sample k, s => runD_bind f (k _) _
  | .grind b k, ⟨sp, [], os, roots⟩ => rfl
  | .grind b k, ⟨sp, n :: xs, os, roots⟩ => by
    show (if _ then _ else _) = match (if _ then _ else _) with
      | some (a, s') => runD (f a) s'
      | none => none
    split
    · exact runD_bind f k _
    · rfl
  | .commit ht w k, ⟨sp, [], os, roots⟩ => rfl
  | .commit ht w k, ⟨sp, [x0], os, roots⟩ => rfl
  | .commit ht w k, ⟨sp, x0 :: x1 :: xs, os, roots⟩ => by
    show (match digestFromHalves (x0, x1) with | some root => _ | none => _) =
      match (match digestFromHalves (x0, x1) with | some root => _ | none => _) with
      | some (a, s') => runD (f a) s'
      | none => none
    split
    · exact runD_bind f k _
    · rfl
  | .query i ps k, s => by
    rcases h : s.roots[i]? with _ | ⟨root, height, width⟩ <;>
      rcases hs : s.openings with _ | ⟨phase, rest⟩
    · simp only [runD, VerifierProgram.bind, Compile.runWithHash, h, hs]
      rfl
    · simp only [runD, VerifierProgram.bind, Compile.runWithHash, h, hs]
      rfl
    · simp only [runD, VerifierProgram.bind, Compile.runWithHash, h, hs]
      rfl
    · simp only [runD, VerifierProgram.bind, Compile.runWithHash, h, hs]
      rcases ho : Id.run (openPhaseWithHash keccak256 root height width ps phase) with _ | rows
      · simp only [Id.run] at ho
        simp only [id_bind, ho]
        rfl
      · simp only [Id.run] at ho
        simp only [id_bind, ho]
        exact runD_bind f (k rows) _

/-- **`p` runs from the sponge `sp` on the scalars `xs`, returning `a` at the sponge `sp'`**,
whatever follows in the proof. -/
def RunsTo {α : Type} (p : VerifierProgram α) (sp : Sponge) (xs : List E) (a : α) (sp' : Sponge) :
    Prop :=
  ∀ (rest : List E) (os : List (List Opening)) (roots : List (Digest × ℕ × ℕ)),
    runD p ⟨sp, xs ++ rest, os, roots⟩ = some (a, ⟨sp', rest, os, roots⟩)

theorem runsTo_ret {α : Type} (a : α) (sp : Sponge) : RunsTo (VerifierProgram.ret a) sp [] a sp :=
  fun _ _ _ ↦ rfl

theorem RunsTo.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {sp sp1 sp2 :
    Sponge}
    {xs ys : List E} {a : α} {b : β} (hp : RunsTo p sp xs a sp1)
    (hf : RunsTo (f a) sp1 ys b sp2) : RunsTo (p >>= f) sp (xs ++ ys) b sp2 := by
  intro rest os roots
  show runD (p.bind f) _ = _
  rw [runD_bind, List.append_assoc, hp]
  exact hf rest os roots

theorem RunsTo.of_eq {α : Type} {p : VerifierProgram α} {sp sp' : Sponge} {xs ys : List E} {a : α}
    (h : RunsTo p sp xs a sp') (hxy : xs = ys) : RunsTo p sp ys a sp' := hxy ▸ h

theorem runsTo_readE (sp : Sponge) (x : E) : RunsTo VerifierProgram.readScalar sp [x] x (obs
    sp x) :=
  fun _ _ _ ↦ rfl

theorem runsTo_sampleE (sp : Sponge) : RunsTo VerifierProgram.sampleChallenge sp [] (sq sp).1 (sq
    sp).2 :=
  fun _ _ _ ↦ rfl

theorem runsTo_require {c : Prop} [Decidable c] (hc : c) (sp : Sponge) :
    RunsTo (VerifierProgram.require c) sp [] () sp := by
  intro rest os roots
  simp [VerifierProgram.require, hc]
  rfl

theorem runsTo_liftOption {α : Type} (a : α) (sp : Sponge) :
    RunsTo (liftOption (some a)) sp [] a sp := runsTo_ret a sp

theorem runsTo_readN (sp : Sponge) :
    ∀ xs : List E, RunsTo (VerifierProgram.readScalars xs.length) sp xs xs (obsAll sp xs)
  | [] => runsTo_ret _ _
  | x :: xs => by
    have h := (runsTo_readE sp x).bind (f := fun x ↦ do
        let xs ← VerifierProgram.readScalars xs.length
        return x :: xs)
      ((runsTo_readN (obs sp x) xs).bind (f := fun xs' ↦ (pure (x :: xs') : VerifierProgram
          (List E)))
        (runsTo_ret _ _))
    exact h.of_eq (by simp)

theorem runsTo_readN' (sp : Sponge) {n : ℕ} (xs : List E) (hn : xs.length = n) :
    RunsTo (VerifierProgram.readScalars n) sp xs xs (obsAll sp xs) := hn ▸ runsTo_readN sp xs

/-- A shaped child is read off its cells. -/
theorem runsTo_readChild {bytecode : List K} {c : ChildClaims} (hc : ChildHasBytecodeShape bytecode c)
    (sp : Sponge) :
    RunsTo (readChild (Nat.log2 bytecode.length)) sp (childCells c) c
      (obsAll sp (childCells c)) := by
  have h := (runsTo_readN' sp (childCells c) (length_childCells hc)).bind
    (f := fun xs ↦ do
      VerifierProgram.require (xs.drop (childWordCount (Nat.log2 bytecode.length)) =
        List.replicate (zerosToWholeRate (childWordCount (Nat.log2 bytecode.length))) 0)
      liftOption (parseChild (Nat.log2 bytecode.length) xs))
    ((runsTo_require (drop_childCells hc) _).bind
      (f := fun _ ↦ liftOption (parseChild (Nat.log2 bytecode.length) (childCells c)))
      (by rw [parseChild_childCells hc]; exact runsTo_liftOption c _))
  exact h.of_eq (by simp)

/-- Shaped children are read off their cells. -/
theorem runsTo_readChildren {bytecode : List K} :
    ∀ {cs : List ChildClaims}, (∀ c ∈ cs, ChildHasBytecodeShape bytecode c) → ∀ sp : Sponge,
      RunsTo (readChildren (Nat.log2 bytecode.length) cs.length) sp (cs.flatMap childCells) cs
        (obsAll sp (cs.flatMap childCells))
  | [], _, sp => runsTo_ret _ sp
  | c :: cs, hs, sp => by
    have h := (runsTo_readChild (hs c List.mem_cons_self) sp).bind
      (f := fun c ↦ do
        let cs ← readChildren (Nat.log2 bytecode.length) cs.length
        return c :: cs)
      ((runsTo_readChildren (fun c' h' ↦ hs c' (List.mem_cons_of_mem c h')) _).bind
        (f := fun cs' ↦ (pure (c :: cs') : VerifierProgram (List ChildClaims))) (runsTo_ret _ _))
    rw [List.append_nil, ← obsAll_append, ← List.flatMap_cons] at h
    exact h

/-- The count is read off its cells. -/
theorem runsTo_readCount {M n : ℕ} (hM : M ≤ 2 ^ 64 - 1) (hn : n < M) (sp : Sponge) :
    RunsTo (readChildCount M) sp (childCountCells n) n (obsAll sp (childCountCells n)) := by
  have h := (runsTo_readN' sp (childCountCells n) rfl).bind
    (f := fun xs ↦ do
      VerifierProgram.require (xs.drop 1 = List.replicate (rateScalars - 1) 0)
      liftOption (childCountOfGeneratorPower M (xs.getD 0 0)))
    ((runsTo_require (show (childCountCells n).drop 1 = List.replicate (rateScalars - 1) 0 from rfl)
      _).bind (f := fun _ ↦ liftOption (childCountOfGeneratorPower M ((childCountCells n).getD 0 0)))
      (by rw [show (childCountCells n).getD 0 0 = Verifier.gpow n from rfl, countOf_gpow hM hn]
          exact runsTo_liftOption n _))
  exact h.of_eq (by simp)

/-- The rounds of the sumcheck are `rsRun`'s. -/
theorem runsTo_roundsProg : ∀ (rounds : List (E × E)) (claim : E) (sp : Sponge) {k : ℕ},
    rounds.length = k →
      RunsTo (sumcheckRoundsProgram claim k) sp (rounds.flatMap fun g ↦ [g.1, g.2])
        (rsRun rounds claim sp).1 (rsRun rounds claim sp).2
  | [], claim, sp, _, hk => by subst hk; exact runsTo_ret _ sp
  | (g1, gInf) :: rounds, claim, sp, _, hk => by
    subst hk
    have h := (runsTo_readE sp g1).bind
      (f := fun g1 ↦ do
        let gInf ← VerifierProgram.readScalar
        let r ← VerifierProgram.sampleChallenge
        let rest ← sumcheckRoundsProgram (sumcheckRoundPolynomial claim (g1, gInf) r) rounds.length
        return (r :: rest.1, rest.2))
      ((runsTo_readE (obs sp g1) gInf).bind
        (f := fun gInf ↦ do
          let r ← VerifierProgram.sampleChallenge
          let rest ← sumcheckRoundsProgram (sumcheckRoundPolynomial claim (g1, gInf) r) rounds.length
          return (r :: rest.1, rest.2))
        ((runsTo_sampleE (obs (obs sp g1) gInf)).bind
          (f := fun r ↦ do
            let rest ← sumcheckRoundsProgram (sumcheckRoundPolynomial claim (g1, gInf) r) rounds.length
            return (r :: rest.1, rest.2))
          ((runsTo_roundsProg rounds _ _ rfl).bind
            (f := fun rest ↦ (pure (_ :: rest.1, rest.2) : VerifierProgram (List E × E)))
            (runsTo_ret _ _))))
    exact h.of_eq (by simp)

/-- A check followed by acceptance. -/
theorem runD_require_true (c : Prop) [Decidable c] (s : VerifierProgramState) :
    runD (VerifierProgram.require c >>= fun _ ↦ (pure true : VerifierProgram Bool)) s =
      if c then some (true, s) else none := by
  unfold VerifierProgram.require
  split_ifs <;> rfl

/-- A run continues where its first program's run ends. -/
theorem runD_bind_of_runsTo {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {sp sp'
    : Sponge}
    {xs : List E} {a : α} (hp : RunsTo p sp xs a sp') (rest : List E) (os : List (List Opening))
    (roots : List (Digest × ℕ × ℕ)) :
    runD (p >>= f) ⟨sp, xs ++ rest, os, roots⟩ = runD (f a) ⟨sp', rest, os, roots⟩ := by
  show runD (p.bind f) _ = _
  rw [runD_bind, hp]

/-- **The program is the batching**: with Keccak-256 and Keccak-f[1600], from the batching's
seed, on the stream of fewer than `M` children of the bytecode's shapes and rounds of its size,
the program accepts exactly where `batch` defers a claim that holds of `bytecode`. -/
theorem runProof_batchAny {M : ℕ} (hM : M ≤ 2 ^ 64 - 1) {bytecode : List K}
    {cs : List ChildClaims} {h : BatchingHints} (hn : cs.length < M)
    (hs : ∀ c ∈ cs, ChildHasBytecodeShape bytecode c)
    (hr : h.sumcheckMessages.length = Nat.log2 bytecode.length) :
    Id.run (runProofWithHash keccak256 keccakF1600 (boundedBatchingProgram M bytecode) batchSeed
        ⟨batchingStream cs h, []⟩) = true ↔
      ∃ d, batch cs h = some d ∧ d.HoldsWithShape bytecode := by
  have hstream : batchingStream cs h = childCountCells cs.length ++ (cs.flatMap childCells ++
      (h.sumcheckMessages.flatMap (fun g ↦ [g.1, g.2]) ++ [h.finalBytecodeValue])) := by
    simp only [batchingStream, cellsBeforeChallenge, List.append_assoc]
  show (match runD (boundedBatchingProgram M bytecode) ⟨⟨batchSeed, [], none⟩, batchingStream cs h, [], []⟩ with
      | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
      | _ => false) = true ↔ _
  have hsp : batchSponge cs = obsAll (obsAll ⟨batchSeed, [], none⟩ (childCountCells cs.length))
      (cs.flatMap childCells) := obsAll_append _ _ _
  rw [hstream, boundedBatchingProgram, runD_bind_of_runsTo (runsTo_readCount hM hn _), batchingProgram,
    runD_bind_of_runsTo (runsTo_readChildren hs _), ← hsp, batchingAfterChildren,
    ← List.nil_append (List.flatMap _ _ ++ _),
    runD_bind_of_runsTo (runsTo_sampleE _),
    runD_bind_of_runsTo (runsTo_roundsProg h.sumcheckMessages _ _ hr),
    ← List.append_nil [h.finalBytecodeValue],
    runD_bind_of_runsTo (runsTo_readE _ _), runD_require_true, batch_eq']
  simp only [lambdasB, claimB, spB, sqL]
  split_ifs <;> simp_all

end
end LeanVM.Guest.Batch
