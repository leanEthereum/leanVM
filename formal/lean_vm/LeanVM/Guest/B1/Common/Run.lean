/-
  LeanVM.Guest.B1.Common.Run

  The carried sponge's operations are the Spec's, and the Spec's programs run on it: `RunsTo`
  composes, and reads, samples and proofs of work are its steps.
-/

module

public import LeanVM.Guest.B1.Common.Sponge
public import LeanVM.Guest.B1.Common.Phase
public import LeanVM.Protocol.WithHash

/-!
# Runs on the carried sponge

* `perm_eq`: the Spec's permutation input of a sponge the guest carries as `s` permutes to
  `s.perm`; `carries_absorb`, `carries_squeeze`: `Fs.absorb` and `Fs.squeeze` are `absorb` and
  `squeeze` (`Statement/LeanVmVerifier.lean`, at `Id` and `keccakF`) on the carried cells.
* `RunsTo.bind`, `runsTo_ret`: runs compose (`RunsTo.bindG`, `RunsToG.bindFrom`,
  `RunsFromG.bind` through a ground challenge); `runsTo_readE`, `runsTo_readN`, `runsTo_sampleE`,
  `runsTo_sampleN`: the Spec's reads and samples as runs on the carried sponge
  (`Fs.absorb … dsObserve`, `Fs.squeeze`).
* `runsToG_grind`: a proof of work, the nonce absorbed with `dsPowNonce` and permuted, `powOk`
  of the permutation's lane `2`, its challenge left ground; `runsFromG_sample` returns it.
* `grindSample bits`, `grindWords bits n`, `runsTo_grindSample`: a grind of `bits` then a
  challenge (`fs_grind_squeeze`) is `Fs.grindSqueeze`, reading the nonce unless `bits = 0`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The operations -/

/-- The cells of the permutation input: the rate cells of the waiting scalars, then the
capacity's. -/
theorem stateOfCells_carried (S : KeccakState) (pend : List (E × ℕ)) :
    stateOfCells (cells13 (rateOf pend ++ capOf S)) false = duplexInput ⟨S, pend, none⟩ := by
  apply Keccak.stateOfCells_duplex
  · intro c hc
    simp only [cells13, rateOf]
    rw [List.getD_append _ _ _ _ (by simpa using hc), List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range hc]
    rfl
  · intro c hc
    fin_cases c <;> simp_all [cells13, rateOf, capOf]

/-- **The carried sponge permutes as the Spec's.** -/
theorem perm_eq {s : Fs} {sp : Sponge} (h : s.Carries sp) : keccakF1600 (duplexInput sp) = s.perm := by
  obtain ⟨st, p, g⟩ := sp
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3
  subst h3
  rw [Fs.perm, permOf, ← h1, stateOfCells_carried, ← h2]

/-- **`Fs.absorb` is `absorb`.** -/
theorem carries_absorb {s : Fs} {sp : Sponge} (h : s.Carries sp) (x : E) (t : ℕ) :
    (s.absorb x t).Carries (Id.run (Compile.absorb (m := Id) keccakF1600 sp x t)) := by
  have hp := perm_eq h
  obtain ⟨h1, h2, h3⟩ := h
  unfold Fs.absorb
  split_ifs with hl
  · rw [Keccak.absorb_id_full sp x t (by rw [h2]; exact hl), hp]
    generalize s.perm = S
    exact ⟨rfl, rfl, h3⟩
  · obtain ⟨st, p, g⟩ := sp
    simp only at h1 h2 h3
    subst h2 h3
    have : Compile.absorb (m := Id) keccakF1600 ⟨st, s.pend, none⟩ x t =
        ⟨st, s.pend ++ [(x, t)], none⟩ := by
      unfold Compile.absorb
      rw [ite_eq_right (show ¬ s.pend.length = rateScalars from hl)]
      rfl
    rw [this]
    exact ⟨h1, rfl, rfl⟩

/-- **`Fs.squeeze` is `squeeze`.** -/
theorem carries_squeeze {s : Fs} {sp : Sponge} (h : s.Carries sp) :
    (Id.run (Compile.squeeze (m := Id) keccakF1600 sp)).1 = s.squeeze.1 ∧
      s.squeeze.2.Carries (Id.run (Compile.squeeze (m := Id) keccakF1600 sp)).2 := by
  have hp := perm_eq h
  rw [Keccak.squeeze_id sp h.2.2, hp]
  simp only [Fs.squeeze]
  generalize s.perm = S
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Composing runs -/

theorem prog_bind_eq {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β) : p >>= f =
    p.bind f := rfl

theorem run_bind {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β) (st :
    VerifierProgramState) :
    runId (p.bind f) st = (runId p st).bind (fun r => runId (f r.1) r.2) := by
  induction p generalizing st with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    simp only [runId, VerifierProgram.bind, Compile.runWithHash]
    split
    · exact ih _ _
    · rfl
  | sample k ih => exact ih _ _
  | grind b k ih =>
    simp only [runId, VerifierProgram.bind, Compile.runWithHash]
    split
    · simp only [bind, pure]
      split
      · exact ih _
      · rfl
    · rfl
  | commit h w k ih =>
    simp only [runId, VerifierProgram.bind, Compile.runWithHash]
    split
    · exact ih _
    · rfl
  | query i ps k ih =>
    simp only [runId, VerifierProgram.bind, Compile.runWithHash]
    split
    · simp only [bind]
      split
      · exact ih _ _
      · rfl
    · rfl

theorem runsTo_ret {α : Type} (a : α) (s : Fs) : RunsTo (pure a : VerifierProgram α) s [] a s :=
  fun sp h _ _ _ => ⟨sp, h, rfl⟩

theorem RunsTo.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {s s1 s2 : Fs}
    {xs ys : List E}
    {a : α} {b : β} (h1 : RunsTo p s xs a s1) (h2 : RunsTo (f a) s1 ys b s2) :
    RunsTo (p >>= f) s (xs ++ ys) b s2 := by
  intro sp hs rest os roots
  obtain ⟨sp1, hs1, e1⟩ := h1 sp hs (ys ++ rest) os roots
  obtain ⟨sp2, hs2, e2⟩ := h2 sp1 hs1 rest os roots
  refine ⟨sp2, hs2, ?_⟩
  rw [prog_bind_eq, run_bind, List.append_assoc, e1]
  exact e2

theorem RunsTo.of_eq {α : Type} {p : VerifierProgram α} {s s' t t' : Fs} {xs xs' : List E} {a
    a' : α}
    (h : RunsTo p s xs a t) (hs : s = s') (hx : xs = xs') (ha : a = a') (ht : t = t') :
    RunsTo p s' xs' a' t' := by
  subst hs hx ha ht; exact h

/-! ## The steps -/

/-- **A read** absorbs the stream word with `dsObserve`. -/
theorem runsTo_readE (s : Fs) (x : E) : RunsTo VerifierProgram.readScalar s [x] x (s.absorb x
    dsObserve) := by
  intro sp hs rest os roots
  obtain ⟨st, p, g⟩ := sp
  have h3 : g = none := hs.2.2
  subst h3
  exact ⟨_, carries_absorb hs x dsObserve, rfl⟩

/-- **A sample** squeezes. -/
theorem runsTo_sampleE (s : Fs) : RunsTo VerifierProgram.sampleChallenge s [] s.squeeze.1
    s.squeeze.2 := by
  intro sp hs rest os roots
  obtain ⟨e1, e2⟩ := carries_squeeze hs
  refine ⟨_, e2, ?_⟩
  simp only [runId, VerifierProgram.sampleChallenge, Compile.runWithHash, List.nil_append]
  rw [← e1]
  rfl

theorem runsTo_readN (s : Fs) (xs : List E) :
    RunsTo (VerifierProgram.readScalars xs.length) s xs xs (s.absorbAll xs dsObserve) := by
  induction xs generalizing s with
  | nil => exact runsTo_ret _ _
  | cons x xs ih =>
    have h := (runsTo_readE s x).bind (f := fun x => do let xs ← VerifierProgram.readScalars xs.length; return x :: xs)
      ((ih (s.absorb x dsObserve)).bind (f := fun xs => (pure (x :: xs) : VerifierProgram (List E)))
        (runsTo_ret (x :: xs) _))
    simpa [VerifierProgram.readScalars, Fs.absorbAll, List.foldl] using h

theorem runsTo_sampleN (n : ℕ) (s : Fs) :
    RunsTo (VerifierProgram.sampleChallenges n) s [] (s.squeezeN n).1 (s.squeezeN n).2 := by
  induction n generalizing s with
  | zero => exact runsTo_ret _ _
  | succ n ih =>
    have h := (runsTo_sampleE s).bind (f := fun x => do let xs ← VerifierProgram.sampleChallenges n; return x :: xs)
      ((ih s.squeeze.2).bind (f := fun xs => (pure (s.squeeze.1 :: xs) : VerifierProgram (List E)))
        (runsTo_ret _ _))
    simpa [VerifierProgram.sampleChallenges, Fs.squeezeN] using h

/-! ## Through a ground challenge -/

theorem RunsTo.bindG {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {s s1 : Fs}
    {xs ys : List E} {a : α} {b : β} {cap : List E} {c : E} (h1 : RunsTo p s xs a s1)
    (h2 : RunsToG (f a) s1 ys b cap c) : RunsToG (p >>= f) s (xs ++ ys) b cap c := by
  intro sp hs rest os roots
  obtain ⟨sp1, hs1, e1⟩ := h1 sp hs (ys ++ rest) os roots
  obtain ⟨sp2, hs2, e2⟩ := h2 sp1 hs1 rest os roots
  refine ⟨sp2, hs2, ?_⟩
  rw [prog_bind_eq, run_bind, List.append_assoc, e1]
  exact e2

theorem RunsToG.bindFrom {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {s s2 : Fs} {xs ys : List E} {a : α} {b : β} {cap : List E} {c : E}
    (h1 : RunsToG p s xs a cap c) (h2 : RunsFromG (f a) cap c ys b s2) :
    RunsTo (p >>= f) s (xs ++ ys) b s2 := by
  intro sp hs rest os roots
  obtain ⟨sp1, hs1, e1⟩ := h1 sp hs (ys ++ rest) os roots
  obtain ⟨sp2, hs2, e2⟩ := h2 sp1 hs1 rest os roots
  refine ⟨sp2, hs2, ?_⟩
  rw [prog_bind_eq, run_bind, List.append_assoc, e1]
  exact e2

theorem RunsFromG.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {s1 s2 : Fs} {xs ys : List E} {a : α} {b : β} {cap : List E} {c : E}
    (h1 : RunsFromG p cap c xs a s1) (h2 : RunsTo (f a) s1 ys b s2) :
    RunsFromG (p >>= f) cap c (xs ++ ys) b s2 := by
  intro sp hs rest os roots
  obtain ⟨sp1, hs1, e1⟩ := h1 sp hs (ys ++ rest) os roots
  obtain ⟨sp2, hs2, e2⟩ := h2 sp1 hs1 rest os roots
  refine ⟨sp2, hs2, ?_⟩
  rw [prog_bind_eq, run_bind, List.append_assoc, e1]
  exact e2

/-- The Spec's grind, at any hash and permutation: the nonce absorbed, the permutation, its lane
`2` checked and its challenge ground (stated over a variable `F`, so that `rfl` cannot unfold
Keccak-f). -/
theorem runWithHash_grind (H : List UInt8 → Digest) (F : KeccakState → KeccakState) (bits : ℕ)
    {α : Type} (k : VerifierProgram α) (st : KeccakState) (p : List (E × ℕ)) (n : E)
    (rest : List E) (os : List (List Opening)) (roots : List (Digest × ℕ × ℕ)) :
    Compile.runWithHash (m := Id) H F (.grind bits k) ⟨⟨st, p, none⟩, n :: rest, os, roots⟩ =
      if powOk bits (Keccak.lane (F (duplexInput
          (Id.run (Compile.absorb (m := Id) F ⟨st, p, none⟩ n dsPowNonce)))) 2) = true then
        Compile.runWithHash (m := Id) H F k ⟨⟨F (duplexInput
          (Id.run (Compile.absorb (m := Id) F ⟨st, p, none⟩ n dsPowNonce))), [],
          some (challengeOf (F (duplexInput
            (Id.run (Compile.absorb (m := Id) F ⟨st, p, none⟩ n dsPowNonce)))))⟩, rest, os, roots⟩
      else none := rfl

/-- The Spec's grind from a carried sponge (`absorbNonce`): the nonce absorbed, the permutation,
its lane `2` checked and its challenge ground. -/
theorem run_grind_carried (bits : ℕ) {α : Type} (k : VerifierProgram α) {s : Fs} {sp : Sponge}
    (hs : s.Carries sp) (n : E) (rest : List E) (os : List (List Opening))
    (roots : List (Digest × ℕ × ℕ)) :
    runId (.grind bits k) ⟨sp, n :: rest, os, roots⟩ =
      if powOk bits (Keccak.lane (s.nonceState n) 2) = true then
        runId k ⟨⟨s.nonceState n, [], some (challengeOf (s.nonceState n))⟩, rest, os, roots⟩
      else none := by
  have ha := carries_absorb hs n dsPowNonce
  have hp := perm_eq ha
  obtain ⟨st, p, g⟩ := sp
  have h3 : g = none := hs.2.2
  subst h3
  rw [Fs.nonceState, runId, runWithHash_grind, hp]

/-- **A proof of work** of `bits ≠ 0`: the nonce read, absorbed with `dsPowNonce` and permuted,
`powOk` of the permutation's lane `2`; the permutation's challenge is ground. -/
theorem runsToG_grind {bits : ℕ} (hb : bits ≠ 0) (s : Fs) (n : E)
    (hok : powOk bits (Keccak.lane (s.nonceState n) 2) = true) :
    RunsToG (VerifierProgram.grindProofOfWork bits) s [n] () (capOf (s.nonceState n))
      (challengeOf (s.nonceState n)) := by
  intro sp hs rest os roots
  refine ⟨⟨s.nonceState n, [], some (challengeOf (s.nonceState n))⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
  rw [VerifierProgram.grindProofOfWork, ite_eq_right hb, List.cons_append, List.nil_append,
    run_grind_carried bits _ hs n rest os roots, ite_eq_left hok]
  rfl

/-- **A sample returns the ground challenge.** -/
theorem runsFromG_sample (cap : List E) (c : E) :
    RunsFromG VerifierProgram.sampleChallenge cap c [] c ⟨cap, []⟩ := by
  intro sp hs rest os roots
  obtain ⟨st, p, g⟩ := sp
  obtain ⟨h1, h2, h3⟩ := hs
  simp only at h1 h2 h3
  subst h2 h3
  exact ⟨_, ⟨h1, rfl, rfl⟩, rfl⟩

/-- A grind of `bits` then a challenge (`fs_grind_squeeze`). -/
def grindSample (bits : ℕ) : VerifierProgram E := do
  VerifierProgram.grindProofOfWork bits
  VerifierProgram.sampleChallenge

/-- The stream words `grindSample bits` reads: the nonce, unless `bits = 0`. -/
def grindWords (bits : ℕ) (n : E) : List E := if bits = 0 then [] else [n]

/-- **A grind then a challenge is `Fs.grindSqueeze`**: at zero bits a plain squeeze, otherwise the
nonce's permutation, its challenge and capacity, when its proof of work passes. -/
theorem runsTo_grindSample (bits : ℕ) (s : Fs) (n : E) (hok : s.GrindOk bits n) :
    RunsTo (grindSample bits) s (grindWords bits n) (s.grindSqueeze bits n).1
      (s.grindSqueeze bits n).2 := by
  by_cases hb : bits = 0
  · subst hb
    exact runsTo_sampleE s
  · have hok' : powOk bits (Keccak.lane (s.nonceState n) 2) = true := hok.resolve_left hb
    have h := (runsToG_grind hb s n hok').bindFrom
      (f := fun _ => VerifierProgram.sampleChallenge) (runsFromG_sample _ _)
    rw [Fs.grindSqueeze_pos s hb n]
    simpa [grindWords, grindSample, hb] using h

/-! ## Cells of waiting scalars and permutations -/

/-- The rate cells of the waiting scalars, scalar by scalar (`Keccak.scalarCells`). -/
def pendCells (pend : List (E × ℕ)) : List E :=
  pend.flatMap fun p => [(Keccak.scalarCells p.1 p.2).1, (Keccak.scalarCells p.1 p.2).2]

/-- The rate cells of up to four waiting scalars: their cells, then zeros. -/
theorem rateOf_eq_cells (pend : List (E × ℕ)) (h : pend.length ≤ 4) :
    rateOf pend = pendCells pend ++ List.replicate (8 - 2 * pend.length) 0 := by
  match pend, h with
  | [], _ => simp [rateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes, pendCells,
      zero_eq_ofLimbs]
  | [a], _ => simp [rateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes, pendCells,
      Keccak.scalarCells, zero_eq_ofLimbs, ofLimbs_limb]
  | [a, b], _ => simp [rateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes, pendCells,
      Keccak.scalarCells, zero_eq_ofLimbs, ofLimbs_limb]
  | [a, b, c], _ => simp [rateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes,
      pendCells, Keccak.scalarCells, zero_eq_ofLimbs, ofLimbs_limb]
  | [a, b, c, d], _ => simp [rateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes,
      pendCells, Keccak.scalarCells, ofLimbs_limb]

/-- A sponge's next permutation, its cells written out. -/
theorem perm_eq_cells (s : Fs) (h : s.pend.length ≤ 4) :
    s.perm = permOf (pendCells s.pend ++ List.replicate (8 - 2 * s.pend.length) 0 ++ s.cap) := by
  rw [Fs.perm, rateOf_eq_cells _ h]

/-- Absorbing below a full queue appends. -/
theorem absorbAll_short (s : Fs) (xs : List E) (t : ℕ) (h : s.pend.length + xs.length ≤ 4) :
    s.absorbAll xs t = ⟨s.cap, s.pend ++ xs.map (·, t)⟩ := by
  induction xs generalizing s with
  | nil => simp [Fs.absorbAll]
  | cons x xs ih =>
    simp only [List.length_cons] at h
    have hl : s.pend.length ≠ rateScalars := by unfold rateScalars; omega
    simp only [Fs.absorbAll, List.foldl_cons] at ih ⊢
    rw [show s.absorb x t = ⟨s.cap, s.pend ++ [(x, t)]⟩ by simp [Fs.absorb, hl],
      ih _ (by simp; omega)]
    simp

/-- The cells of a `KECCAK` atom's outputs, one by one. -/
theorem outs_eq {σ : Val} {outs : List V} {f : Fin 13 → E}
    (h : cells13 (outs.map σ) = f) (k : Fin 13) (hk : k.val < outs.length) :
    σ outs[k.val] = f k := by
  rw [← h]
  simp [cells13, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]

end
end LeanVM.Guest.B1
