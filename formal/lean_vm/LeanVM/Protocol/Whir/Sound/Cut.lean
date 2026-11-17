/-
  LeanVM.Protocol.Whir.Sound.Cut

  The ghost opening cut right after the final polynomial is read: it returns the same trace, on a
  prefix of every history the full one returns on.
-/

module

public import LeanVM.Protocol.Whir.Sound.Spec
public import LeanVM.Protocol.EndToEnd.Sound.Frame

/-!
# The opening, cut at the final polynomial

The agreement-set extractor needs the trace of an accepting run (`WhirTrace`: the rounds, the high
parts, the final polynomial), and reads its challenges off the adversary's permutation queries. An
honest prover need not query the permutations after the final polynomial (the final positions'
are its own business, the last tail challenge it never uses), so the extractor runs the opening
only up to the final polynomial.

* `whirLevelsGF logN fin`: the ghost levels with the final level's step after its rounds a
  parameter; `whirLevelsG` is it at `finFull` (`whirLevelsG_eq`), the cut at `finCut`, which reads
  the final polynomial and returns.
* `after_whirLevelsGF_cut`: wherever `whirLevelsG` returns a trace after a history, the cut
  returns the same trace after a prefix of it.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
  LeanVM.Protocol.EndToEnd.Sound VerifierProgram

@[expose] public section

/-- **The ghost levels with the final step a parameter**: `fin index level s rounds` runs after the
final level's rounds. -/
def whirLevelsGF (logN : ℕ)
    (fin : ℕ → Whir.Level → WhirState → List FoldRound → VerifierProgram WhirTrace) :
    ℕ → List Whir.Level → WhirState → VerifierProgram WhirTrace
  | _, [], _ => VerifierProgram.fail
  | index, [level], s => foldRounds level.fold s >>= fun r ↦ fin index level r.1 r.2
  | index, level :: next :: rest, s => foldRounds level.fold s >>= fun r ↦
      midTailC logN index level next (fun high s' ↦
        whirLevelsGF logN fin (index + 1) (next :: rest) s' >>= fun tr ↦
          VerifierProgram.ret (.mid r.2 high tr)) r.1 r.2

/-- The full final step: `finalTailG`, then the trace's leaf. -/
def finFull (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) : VerifierProgram WhirTrace :=
  finalTailG logN laneFolds eb index level s rounds >>= fun folded ↦
    VerifierProgram.ret (.final rounds folded)

/-- **The cut final step**: read the final polynomial and return the trace's leaf. -/
def finCut (logN : ℕ) (_ : ℕ) (level : Whir.Level) (s : WhirState) (rounds : List FoldRound) :
    VerifierProgram WhirTrace :=
  readScalars (2 ^ (logN - s.alphas.length) + level.fold) >>= fun folded ↦
    VerifierProgram.ret (.final rounds folded)

theorem whirLevelsG_eq (logN laneFolds : ℕ) (eb : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
      whirLevelsG logN laneFolds eb index levels s =
        whirLevelsGF logN (finFull logN laneFolds eb) index levels s
  | _, [], _ => rfl
  | _, [_], _ => rfl
  | index, level :: next :: rest, s => by
    rw [whirLevelsG, whirLevelsGF]
    refine congrArg (Bind.bind (foldRounds level.fold s)) (funext fun r ↦ ?_)
    refine congrArg (fun k ↦ midTailC logN index level next k r.1 r.2) (funext fun high ↦
      funext fun s' ↦ ?_)
    rw [whirLevelsG_eq logN laneFolds eb (index + 1) (next :: rest) s']

/-- `midTailC` is its part before the continuation, then the continuation. -/
def midTailPre (logN index : ℕ) (level next : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) : VerifierProgram (List E × WhirState) :=
  midTailC logN index level next (fun high s' ↦ VerifierProgram.ret (high, s')) s rounds

theorem midTailC_eq_pre {α : Type} (logN index : ℕ) (level next : Whir.Level)
    (k : List E → WhirState → VerifierProgram α) (s : WhirState) (rounds : List FoldRound) :
    midTailC logN index level next k s rounds =
      (midTailPre logN index level next s rounds).bind fun p ↦ k p.1 p.2 := by
  simp only [midTailPre, midTailC, VerifierProgram.bind_eq, VerifierProgram.bind_assoc,
    VerifierProgram.ret_bind]

/-- The final level after its final polynomial: the query group and the tail, as in
`finalTailG`. -/
def finalTailRest (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) (folded : List E) : VerifierProgram Unit :=
  grindProofOfWork Whir.queryGrindingBits >>= fun _ ↦
  (sampleQueries (logN - s.alphas.length + level.logInvRate) level.queries >>= fun qs ↦
    queryOpenings index qs >>= fun words ↦
    VerifierProgram.require ((List.zip qs words).all fun (qq, row) ↦
      foldRow (lanesOf index row) (K.ofBits qq) rounds =
        novelEval folded (subspaceAt (logN - s.alphas.length) (K.ofBits qq)))) >>= fun _ ↦
  sumcheck s.claim 3 (List.replicate (logN - s.alphas.length) none) >>= fun r ↦
  VerifierProgram.require (s.glued.foldl
      (fun weight glued ↦ weight + glued.scalar * glued.weightAt ((s.alphas ++ r.1).drop glued.foldStart))
      (eb ((s.alphas ++ r.1).drop laneFolds ++ (s.alphas ++ r.1).take laneFolds)) *
    multilinearEval (folded.take (2 ^ (logN - s.alphas.length))) r.1 = r.2)

/-- The rest of the final level, given the trace's leaf. -/
def finRest (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) : WhirTrace → VerifierProgram Unit
  | .final _ folded => finalTailRest logN laneFolds eb index level s rounds folded
  | .mid _ _ _ => VerifierProgram.fail

/-- **The full final step is the cut one, then the rest returning the same trace.** -/
theorem finFull_eq (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) :
    finFull logN laneFolds eb index level s rounds =
      (finCut logN index level s rounds).bind fun tr ↦
        (finRest logN laneFolds eb index level s rounds tr).bind fun _ ↦ VerifierProgram.ret tr := by
  simp only [finFull, finCut, finalTailG, finRest, finalTailRest, VerifierProgram.bind_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

/-- `ret` reaches only itself. -/
theorem after_ret_eq' {α : Type} {a b : α} {l : List Ev}
    (h : (VerifierProgram.ret a).after l = some (.ret b)) : l = [] ∧ a = b := by
  rcases l with _ | ⟨e, l⟩
  · simp only [VerifierProgram.after, Option.some.injEq, VerifierProgram.ret.injEq] at h
    exact ⟨rfl, h⟩
  · simp [VerifierProgram.after] at h

/-- **The cut returns the full one's trace**, after a prefix of the history. -/
theorem after_whirLevelsGF_cut (logN laneFolds : ℕ) (eb : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState) (h : List Ev) (v : WhirTrace),
      (whirLevelsGF logN (finFull logN laneFolds eb) index levels s).after h = some (.ret v) →
      ∃ h₁ h₂, h = h₁ ++ h₂ ∧
        (whirLevelsGF logN (finCut logN) index levels s).after h₁ = some (.ret v)
  | index, [], s, h, v, hv => by
    rcases h with _ | ⟨e, h⟩ <;> simp [whirLevelsGF, VerifierProgram.after] at hv
  | index, [level], s, h, v, hv => by
    rw [whirLevelsGF, VerifierProgram.bind_eq] at hv
    obtain ⟨r, hA, hB, rfl, hr, hfin⟩ := after_bind_ret hv
    rw [finFull_eq] at hfin
    obtain ⟨tr, hB₁, hB₂, rfl, hcut, hrest⟩ := after_bind_ret hfin
    obtain ⟨tr', hC₁, hC₂, -, -, hret⟩ := after_bind_ret hrest
    obtain ⟨-, rfl⟩ := after_ret_eq' hret
    refine ⟨hA ++ hB₁, hB₂, by rw [List.append_assoc], ?_⟩
    rw [whirLevelsGF, VerifierProgram.bind_eq, VerifierProgram.after_bind_append _ hr]
    exact hcut
  | index, level :: next :: rest, s, h, v, hv => by
    rw [whirLevelsGF, VerifierProgram.bind_eq] at hv
    obtain ⟨r, hA, hB, rfl, hr, hmid⟩ := after_bind_ret hv
    rw [midTailC_eq_pre] at hmid
    obtain ⟨p, hP, hK, rfl, hp, hk⟩ := after_bind_ret hmid
    rw [VerifierProgram.bind_eq] at hk
    obtain ⟨tr, hI, hJ, rfl, hin, hret⟩ := after_bind_ret hk
    obtain ⟨rfl, rfl⟩ := after_ret_eq' hret
    obtain ⟨hI₁, hI₂, rfl, hcut⟩ :=
      after_whirLevelsGF_cut logN laneFolds eb (index + 1) (next :: rest) p.2 hI tr hin
    refine ⟨hA ++ hP ++ hI₁, hI₂, by simp only [List.append_assoc, List.append_nil], ?_⟩
    rw [whirLevelsGF, VerifierProgram.bind_eq, List.append_assoc,
      VerifierProgram.after_bind_append _ hr, midTailC_eq_pre,
      VerifierProgram.after_bind_append _ hp, VerifierProgram.bind_eq,
      ← List.append_nil hI₁, VerifierProgram.after_bind_append _ hcut]
    rfl

end
end LeanVM.Protocol.Whir.Sound
