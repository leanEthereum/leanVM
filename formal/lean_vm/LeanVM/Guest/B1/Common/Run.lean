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
* `RunsTo.bind`, `runsTo_ret`: runs compose; `runsTo_readE`, `runsTo_readN`, `runsTo_sampleE`,
  `runsTo_sampleN`, `runsTo_grindP`: the Spec's reads, samples and proofs of work as runs on the
  carried sponge (`Fs.absorb … dsObserve`, `Fs.squeeze`, the nonce absorbed with `dsPowNonce`
  and `powOk` of the challenge after it).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The operations -/

/-- The cells of the permutation input: the rate cells of the waiting scalars, then the
capacity's. -/
theorem stateOfCells_carried (S : KeccakState) (pend : List (E × ℕ)) :
    stateOfCells (cells13 (rateOf pend ++ capOf S)) false = duplexInput ⟨S, pend⟩ := by
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
  obtain ⟨h1, h2⟩ := h
  rw [Fs.perm, permOf, ← h1, stateOfCells_carried, ← h2]

/-- **`Fs.absorb` is `absorb`.** -/
theorem carries_absorb {s : Fs} {sp : Sponge} (h : s.Carries sp) (x : E) (t : ℕ) :
    (s.absorb x t).Carries (Id.run (Compile.absorb (m := Id) keccakF1600 sp x t)) := by
  have hp := perm_eq h
  obtain ⟨h1, h2⟩ := h
  unfold Fs.absorb
  split_ifs with hl
  · rw [Keccak.absorb_id_full sp x t (by rw [h2]; exact hl), hp]
    exact ⟨rfl, rfl⟩
  · have : Compile.absorb (m := Id) keccakF1600 sp x t =
        { sp with pending := sp.pending ++ [(x, t)] } := by
      simp [Compile.absorb, h2, hl]
      rfl
    rw [this]
    exact ⟨h1, by rw [← h2]; rfl⟩

/-- **`Fs.squeeze` is `squeeze`.** -/
theorem carries_squeeze {s : Fs} {sp : Sponge} (h : s.Carries sp) :
    (Id.run (Compile.squeeze (m := Id) keccakF1600 sp)).1 = s.squeeze.1 ∧
      s.squeeze.2.Carries (Id.run (Compile.squeeze (m := Id) keccakF1600 sp)).2 := by
  have hp := perm_eq h
  rw [Keccak.squeeze_id, hp]
  exact ⟨rfl, rfl, rfl⟩

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
    · rfl
    · exact ih _ _
  | sample k ih => exact ih _ _
  | grind b k ih =>
    simp only [runId, VerifierProgram.bind, Compile.runWithHash]
    split
    · rfl
    · simp only [bind, pure]
      split
      · exact ih _
      · rfl
  | commit h w k ih =>
    simp only [runId, VerifierProgram.bind, Compile.runWithHash]
    split
    · simp only [bind]
      split
      · exact ih _
      · rfl
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

/-- **A proof of work**: the nonce absorbed with `dsPowNonce`, a squeeze, and `powOk` of its
challenge. -/
theorem runsTo_grindP (bits : ℕ) (hb : bits ≠ 0) (s : Fs) (n : E)
    (hok : powOk bits (s.absorb n dsPowNonce).squeeze.1 = true) :
    RunsTo (VerifierProgram.grindProofOfWork bits) s [n] () (s.absorb n dsPowNonce).squeeze.2 := by
  intro sp hs rest os roots
  have ha := carries_absorb hs n dsPowNonce
  obtain ⟨e1, e2⟩ := carries_squeeze ha
  refine ⟨_, e2, ?_⟩
  simp only [VerifierProgram.grindProofOfWork, hb, ↓reduceIte]
  have key : runId (VerifierProgram.grind bits (.ret ())) ⟨sp, [n] ++ rest, os, roots⟩ =
      (if powOk bits (Id.run (Compile.squeeze (m := Id) keccakF1600
          (Id.run (Compile.absorb (m := Id) keccakF1600 sp n dsPowNonce)))).1 = true then
        some ((), ⟨(Id.run (Compile.squeeze (m := Id) keccakF1600
          (Id.run (Compile.absorb (m := Id) keccakF1600 sp n dsPowNonce)))).2, rest, os, roots⟩)
      else none) := rfl
  rw [key, e1]
  simp only [hok, ↓reduceIte]

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
      Keccak.scalarCells, zero_eq_ofLimbs]
  | [a, b], _ => simp [rateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes, pendCells,
      Keccak.scalarCells, zero_eq_ofLimbs]
  | [a, b, c], _ => simp [rateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes,
      pendCells, Keccak.scalarCells, zero_eq_ofLimbs]
  | [a, b, c, d], _ => simp [rateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes,
      pendCells, Keccak.scalarCells]

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
