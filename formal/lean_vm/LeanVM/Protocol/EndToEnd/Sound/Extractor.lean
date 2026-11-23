/-
  LeanVM.Protocol.EndToEnd.Sound.Extractor

  The extracted runs and logs the agreement-set extractor is proved against: extracted runs of
  sequences, their roots, the halting run of a witness's memory image, and the committed word of a
  prefix of the log.
-/

module

import LeanVM.Protocol.EndToEnd.Sound.Theorem
import LeanVM.Protocol.EndToEnd.Front.LayoutBridgeB
import LeanVM.Protocol.LeanIsa.Read
import LeanVM.Protocol.Rom.Statement
public import LeanVM.Protocol.Extraction.Defs
public import LeanVM.Protocol.WithHash
import LeanVM.Protocol.WithHashBridge
public import LeanVM.Protocol.EndToEnd.Front.LayoutInstance
public import LeanVM.Protocol.Compile.Rom.History
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.FiniteBounds
public import ArkLib.Data.CodingTheory.ReedSolomon
public import CompPoly.Univariate.Lagrange
public import Mathlib.Tactic

/-!
# Extracted runs, the witness's memory image and the committed word

* `xrun_bind`, `xrun_rootsInv`: the extracted run of a sequence is the runs of its parts, and the
  roots of a run are its history's commitments.
* `haltingRun_imageOf`: the specification's memory image is the witness's (`imageOf`).
* `committedWord_eq`: the word read from the Keccak-256 answers of a prefix of the log is the
  word extracted from the whole log, provided no entry past the prefix answers the root.
* `logged2`: the experiment in two stages, the adversary's log then the verifier's.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete (publicInputDigest)
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## Extracted runs -/

section XRun

variable (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)

/-- **The extracted run of a sequence** is the extracted run of its first part, then of the
second from where the first stopped. -/
theorem xrun_bind {α β : Type} (f : α → VerifierProgram β) :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) (h : List Ev),
      xrun H F (p.bind f) s h = (xrun H F p s h).bind fun r ↦ xrun H F (f r.1) r.2.1 r.2.2
  | .ret a, s, h => rfl
  | .fail, s, h => rfl
  | .read k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · rcases Compile.absorb (m := Option) F s.sponge _ _ with _ | sp
      · rfl
      · exact xrun_bind f _ _ _
    · rfl
  | .sample k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    rcases squeeze (m := Option) F s.sponge with _ | r
    · rfl
    · exact xrun_bind f _ _ _
  | .grind bits k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · rcases absorbNonce (m := Option) F s.sponge _ with _ | r
      · rfl
      · simp only [Option.bind_some]
        split
        · exact xrun_bind f _ _ _
        · rfl
    · rfl
  | .commit height width k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · rcases Compile.absorb (m := Option) F s.sponge _ _ with _ | sp0
      · rfl
      · simp only [Option.bind_some]
        rcases Compile.absorb (m := Option) F sp0 _ _ with _ | sp1
        · rfl
        · exact xrun_bind f _ _ _
    · rfl
  | .query i ps k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · split
      · exact xrun_bind f _ _ _
      · rfl
    · rfl

/-- **The roots of an extracted run are its history's commitments**, the words extracted under
the roots. -/
theorem xrun_rootsInv {α : Type} :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) (h : List Ev) {a : α} {s' :
        VerifierProgramState} {h' : List Ev},
      RootsInv H s h → xrun H F p s h = some (a, s', h') → RootsInv H s' h'
  | .ret a, s, h, _, _, _, hR, hr => by
    simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact hR
  | .fail, s, h, _, _, _, _, hr => by simp [xrun] at hr
  | .read k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · rename_i x xs hs _
      simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨sp, -, hr⟩ := hr
      exact xrun_rootsInv _ _ _ (rootsInv_append_read hR x sp xs) hr
    · simp at hr
  | .sample k, s, h, _, _, _, hR, hr => by
    simp only [xrun, Option.bind_eq_some_iff] at hr
    obtain ⟨r, -, hr⟩ := hr
    exact xrun_rootsInv _ _ _ (rootsInv_append_sample hR _ r.2) hr
  | .grind bits k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · rename_i n xs hs _
      simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨r, -, hr⟩ := hr
      split at hr
      · exact xrun_rootsInv _ _ _ (rootsInv_append_grind hR bits r.2 xs) hr
      · simp at hr
    · simp at hr
  | .commit height width k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · rename_i x0 x1 xs hs _
      simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨sp0, -, sp1, -, hr⟩ := hr
      exact xrun_rootsInv _ _ _
        (rootsInv_append_commit hR (digestFromHalves (x0, x1)) height width sp1 xs) hr
    · simp at hr
  | .query i ps k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · next root ht w phase rest hroot hphase =>
      split at hr
      · next rows ho =>
        exact xrun_rootsInv _ _ _ (rootsInv_append_query hR rows rest) hr
      · simp at hr
    · simp at hr

end XRun

/-! ## The commitment -/

variable {prog : LeanIsaProgram} {input : PublicInput}

/-! ## The candidates -/

/-! ## The memory image -/

/-- Halting runs of equal images are equal. -/
theorem haltingRun_congr {κ κ' : ℕ} (L : MemoryImage κ) (L' : MemoryImage κ') (e : κ = κ')
    (hL : ∀ i : Fin (2 ^ κ), L i = L' (Fin.cast (congrArg (2 ^ ·) e) i)) :
    Extraction.haltingRun prog L = Extraction.haltingRun prog L' := by
  subst e
  have : L = L' := funext hL
  rw [this]

/-- An entry read with a default inside the vector. -/
theorem getD_eq {n : ℕ} (v : Vector K n) {i j : ℕ} (hij : i = j) (h : i < n) :
    v[i] = v.getD j 0 := by
  subst hij
  simp [Vector.getD, h]

/-- A cell of a memory column is the stack's cell at the column's placement. -/
theorem cell_memCol (s : Sizes) (q : Column (leanIsaμ prog s)) (j : Fin 3)
    (x : Fin (2 ^ s.logMem)) :
    cell prog s q (memCol j) x =
      q.values.getD (((verifierLayout prog s).placement j).index + x) 0 := by
  have hp := placement_committed prog s (memCol j) (not_isVirtual_memCol j)
  rw [refCol_memCol] at hp
  rw [hp]
  have h := column_committed prog s q (memCol j) (not_isVirtual_memCol j) x
  exact h.trans (getD_eq _ (Nat.add_comm _ _) _)

/-- **The specification's memory image is the witness's**: their halting runs agree. -/
theorem haltingRun_imageOf (s : Sizes) (hs : s.logMem ≤ maxLogMem)
    (q : Column (leanIsaμ prog s)) :
    Extraction.haltingRun prog (imageOf (witnessOf prog s q).data).2 =
      Extraction.haltingRun prog
        (Extraction.memoryImage (verifierLayout prog s) (q.values : Vector K (2 ^ _))) := by
  have hrows : memRows (witnessOf prog s q).data = LeanIsa.imageRows prog s q :=
    memRows_witnessOf prog s q (lt_of_le_of_lt hs (by decide))
  have hκ : (imageOf (witnessOf prog s q).data).1 = s.logMem := by
    simp only [imageOf, hrows, LeanIsa.imageRows, Array.size_ofFn,
      Nat.log_pow (by norm_num : 1 < 2)]
    exact min_eq_left hs
  refine haltingRun_congr _ _ hκ fun i ↦ ?_
  simp only [imageOf, hrows]
  have hi : (i : ℕ) < (LeanIsa.imageRows prog s q).size := by
    rw [LeanIsa.imageRows, Array.size_ofFn]; exact lt_of_lt_of_eq i.isLt (by rw [hκ])
  rw [Array.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
  simp only [LeanIsa.imageRows, Array.getElem_ofFn, Extraction.memoryImage]
  exact congrArg₂ E.ofLimbs (cell_memCol s q 0 _) (cell_memCol s q 1 _)

/-- A witness representing a valid execution has its image's halting run, valid. -/
theorem haltingRun_valid {κw : ℕ} {w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog κw)}
    {t : Execution prog}
    (hrep : AssignmentRepresents w t) (hv : ValidExecution prog input t) :
    ∃ t', Extraction.haltingRun prog (imageOf w.data).2 = some t' ∧
      ValidExecution prog input t' := by
  obtain ⟨κ, image, steps⟩ := t
  obtain ⟨hκ, himage, -⟩ := hrep
  generalize imageOf w.data = p at hκ himage ⊢
  obtain ⟨κ', image'⟩ := p
  dsimp only at hκ himage ⊢
  subst hκ
  obtain rfl : image' = image := funext fun i ↦ himage i i.isLt
  have h : ∃ n, Semantics.run prog image' n Registers.initial = some (Registers.final prog) :=
    ⟨steps, hv.2⟩
  rcases hh : Extraction.haltingRun prog image' with _ | t'
  · simp [Extraction.haltingRun, h] at hh
  · simp only [Extraction.haltingRun, h, ↓reduceDIte, Option.some.injEq] at hh
    subst hh
    exact ⟨_, rfl, hv.1, by dsimp only; convert Nat.find_spec h using 3⟩

/-! ## The extractor -/

/-- **The word the specification reads from a prefix of the log is the word extracted from the
whole log**, without failure and when no hash entry past the prefix answers the root. -/
theorem committedWord_eq {X : Type} {σ : Seeds X} {ℓ : Log} {k : ℕ} {r : Digest}
    (hf : ¬ Fail σ ℓ) (hr : ∀ x, .inl (x, r) ∉ ℓ.drop k) (ht w : ℕ) :
    Extraction.committedWord (lookH (ℓ.take k)) r ht w = extract (lookH ℓ) r ht w := by
  have hbefore : HEntriesBefore ℓ r k := by
    intro i hi x hei
    by_contra hik
    refine hr x ?_
    rw [List.mem_iff_getElem]
    exact ⟨i - k, by simp; omega, by
      simp only [List.getElem_drop, Nat.add_sub_cancel' (by omega : k ≤ i)]; exact hei⟩
  rw [← extract_take_eq hf hbefore ht w]
  rfl

/-! ## The experiment in two stages -/

/-- The logged experiment in two stages: the adversary's run from the empty log, with the log it
leaves, then the verifier's run from that log. -/
noncomputable def logged2 {α : Type} (A : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) : ProbComp ((α × Log) × (Bool × Log)) :=
  (simulateQ loggedRO A).run [] >>= fun p ↦
    (fun r ↦ (p, r)) <$> (simulateQ loggedRO (V p.1)).run p.2

/-- The logged experiment forgets the adversary's log. -/
theorem logExperiment_eq_logged2 {α : Type} (A : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) :
    logExperiment A V = (fun w ↦ ((w.1.1, w.2.1), w.2.2)) <$> logged2 A V := by
  rw [logExperiment, Rom.run_simulateQ_bind, logged2, map_bind]
  refine bind_congr fun p ↦ ?_
  rw [simulateQ_map, StateT.run_map, Functor.map_map]

end
end LeanVM.Protocol.EndToEnd.Sound
