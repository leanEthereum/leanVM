/-
  LeanVM.Guest.B1.VsC.VsNatRun

  Deployed runs read backwards step by step on the carried sponge, packed steps included.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatChain
public import LeanVM.Guest.B1.VsC.VsNatFront
public import LeanVM.Guest.B1.Link.Packed
public import LeanVM.Guest.B1.Link.PackedMessage
public import LeanVM.Guest.B1.VerifySub.PhLinkRun

/-!
# Deployed runs, step by step

A deployed run (`runId`) of `p.bind f` from a sponge carried as `F`:
* `natBind_fwd`: where a forward run of `p` is known (`RunsTo`), the run goes on with `f` at its value, from
  a sponge carried as its end (packed draws and reads, whose forward runs read no choice of the prover);
* `natBind_np`: where `p` has no packed step, `p`'s part is a carried run (`runTc`), read backwards by
  the `runTc_*` lemmas;
* the steps: `natLiftOption`, `natGrindSample` (a grind then a challenge), `natRead`, `natSamplePacked`
  (`pkSqueeze`), `natSample5` (the fresh coefficients' draw), `natReadPacked` (`pkAbsorb`),
  `natRequire`, `natRet`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none NoPacked
  noPacked_grindProofOfWork noPacked_sampleChallenge)
open LeanVM.Guest.B1.VerifySub (runId_bind_some)

@[expose] public section

variable {α β : Type}

/-- **A forward run fixes the deployed run's first part.** -/
theorem natBind_fwd {p : VerifierProgram α} {f : α → VerifierProgram β} {s s' : Fs} {ys : List E} {a : α}
    (hp : RunsTo p s ys a s') {sp : Sponge} (hs : s.Carries sp) {rest : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {r : β × VerifierProgramState}
    (h : runId (p.bind f) ⟨sp, ys ++ rest, os, R⟩ = some r) :
    ∃ sp', s'.Carries sp' ∧ runId (f a) ⟨sp', rest, os, R⟩ = some r := by
  obtain ⟨sp', hc', e⟩ := hp sp hs rest os R
  rw [run_bind, e] at h
  exact ⟨sp', hc', h⟩

/-- **A first part with no packed step is a carried run.** -/
theorem natBind_np {p : VerifierProgram α} (hnp : NoPacked p) {f : α → VerifierProgram β} {F : Fs}
    {g : Option E} {sp : Sponge} (hs : TCar F g sp) {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {r : β × VerifierProgramState}
    (h : runId (p.bind f) ⟨sp, xs, os, R⟩ = some r) :
    ∃ a st1, runTc p ⟨F, g, xs, os, R⟩ =
        some (a, ⟨fsOfT st1.sponge, st1.sponge.ground, st1.stream, st1.openings, st1.roots⟩) ∧
      runId (f a) st1 = some r := by
  obtain ⟨a, st1, h1, h2⟩ := runId_bind_some h
  exact ⟨a, st1, runTc_of_runId hnp hs h1, h2⟩

/-- A carried run's end, as the deployed run's state. -/
theorem natEnd {F : Fs} {xs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)}
    {st1 : VerifierProgramState}
    (h : (⟨fsOfT st1.sponge, st1.sponge.ground, st1.stream, st1.openings, st1.roots⟩ : TSt) =
      ⟨F, none, xs, os, R⟩) :
    TCar F none st1.sponge ∧ st1 = ⟨st1.sponge, xs, os, R⟩ := by
  simp only [TSt.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨tcar_of_eq h1 h2, ?_⟩
  obtain ⟨sp, s, o, r⟩ := st1
  simp only at h3 h4 h5
  subst h3 h4 h5
  rfl

theorem natLiftOption {o : Option α} {f : α → VerifierProgram β} {st : VerifierProgramState}
    {r : β × VerifierProgramState} (h : runId ((liftOption o).bind f) st = some r) :
    ∃ a, o = some a ∧ runId (f a) st = some r := by
  cases o with
  | none =>
    change runId VerifierProgram.fail st = some r at h
    simp [Compile.runWithHash] at h
  | some a => exact ⟨a, rfl, h⟩

/-- A grind then a challenge leaves nothing waiting. -/
theorem grindSqueeze_pend (s : Fs) (bits : ℕ) (n : E) :
    s.grindSqueeze bits n = ((s.grindSqueeze bits n).1, ⟨(s.grindSqueeze bits n).2.cap, []⟩) := by
  by_cases hz : bits = 0
  · subst hz; rw [grindSqueeze_zero]; rfl
  · rw [Fs.grindSqueeze_pos _ hz]

/-- **A grind then a challenge, backwards.** -/
theorem natGrindSample {b : ℕ} {K : E → VerifierProgram β} {F : Fs} {sp : Sponge} (hs : TCar F none sp)
    {xs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {r : β × VerifierProgramState}
    (h : runId ((VerifierProgram.grindProofOfWork b).bind fun _ => VerifierProgram.sampleChallenge.bind K)
      ⟨sp, xs, os, R⟩ = some r) :
    ∃ n xs1, xs = grindWords b n ++ xs1 ∧ F.GrindOk b n ∧ ∃ sp1,
      (⟨(F.grindSqueeze b n).2.cap, []⟩ : Fs).Carries sp1 ∧
      runId (K (F.grindSqueeze b n).1) ⟨sp1, xs1, os, R⟩ = some r := by
  have e : (VerifierProgram.grindProofOfWork b).bind (fun _ => VerifierProgram.sampleChallenge.bind K) =
      (grindSample b).bind K := by
    simp only [grindSample, VerifierProgram.bind_eq', VerifierProgram.bind_assoc']
  rw [e] at h
  have hnp : NoPacked (grindSample b) :=
    Tables.NoPacked.bind (noPacked_grindProofOfWork b) fun _ => noPacked_sampleChallenge
  obtain ⟨y, st1, t, h2⟩ := natBind_np hnp hs h
  have t' : runTc ((VerifierProgram.grindProofOfWork b).bind fun _ =>
      VerifierProgram.sampleChallenge.bind VerifierProgram.ret) ⟨F, none, xs, os, R⟩ = _ := t
  obtain ⟨n, xs3, hx, hok, t2⟩ := natGrind_inv t'
  have e2 := runTc_ret_inv t2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨rfl, e3⟩ := e2
  have hp : (F.grindSqueeze b n).2 = ⟨(F.grindSqueeze b n).2.cap, []⟩ := congrArg Prod.snd (grindSqueeze_pend F b n)
  rw [hp] at e3
  obtain ⟨hc, hst⟩ := natEnd (st1 := st1) (F := ⟨(F.grindSqueeze b n).2.cap, []⟩) (xs := xs3) (os := os) (R := R)
    e3
  rw [hst] at h2
  exact ⟨n, xs3, hx, hok, _, hc, h2⟩

/-- **A read, backwards.** -/
theorem natRead {f : E → VerifierProgram β} {F : Fs} {sp : Sponge} (hs : F.Carries sp) {xs : List E}
    {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {r : β × VerifierProgramState}
    (h : runId (VerifierProgram.readScalar.bind f) ⟨sp, xs, os, R⟩ = some r) :
    ∃ x xs', xs = x :: xs' ∧ ∃ sp', (F.absorb x dsObserve).Carries sp' ∧ runId (f x) ⟨sp', xs', os, R⟩ = some r := by
  cases xs with
  | nil => exact absurd h (by simp [VerifierProgram.readScalar, VerifierProgram.bind, runId, Compile.runWithHash])
  | cons x xs' =>
    obtain ⟨sp', hc, h'⟩ := natBind_fwd (runsTo_readE F x) hs (rest := xs') h
    exact ⟨x, xs', rfl, sp', hc, h'⟩

/-- The permutations a packed draw of `n` challenges takes. -/
def pkCount (n : ℕ) : ℕ := (n + 7) / 8

/-- **A packed draw, backwards**: from the carried capacity, `pkSqueeze`'s cells. -/
theorem natSamplePacked {n : ℕ} (hn : 1 ≤ n) {f : List E → VerifierProgram β} {cap : List E} {sp : Sponge}
    (hs : (⟨cap, []⟩ : Fs).Carries sp) {xs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)}
    {r : β × VerifierProgramState}
    (h : runId ((VerifierProgram.sampleChallengesPacked n).bind f) ⟨sp, xs, os, R⟩ = some r) :
    ∃ sp', (⟨(Link.pkSqueeze (pkCount n) cap).2, []⟩ : Fs).Carries sp' ∧
      runId (f ((Link.pkSqueeze (pkCount n) cap).1.take n)) ⟨sp', xs, os, R⟩ = some r :=
  natBind_fwd (Link.runsTo_samplePacked cap (p := pkCount n) (by unfold pkCount; omega) (by unfold pkCount; omega))
    hs (rest := xs) h

/-- **The fresh coefficients' draw, backwards**: cells `0 .. 4` of the next permutation. -/
theorem natSample5 {f : List E → VerifierProgram β} {F : Fs} {sp : Sponge} (hs : F.Carries sp) {xs : List E}
    {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {r : β × VerifierProgramState}
    (h : runId ((VerifierProgram.sampleChallengesPacked 5).bind f) ⟨sp, xs, os, R⟩ = some r) :
    ∃ sp', (⟨capOf F.perm, []⟩ : Fs).Carries sp' ∧
      runId (f ((List.range 5).map (Link.cellAt F.perm))) ⟨sp', xs, os, R⟩ = some r :=
  natBind_fwd (VerifySub.runsTo_samplePacked5 F) hs (rest := xs) h

/-- A packed read's run reads its words. -/
theorem readPacked_len {n : ℕ} {f : List E → VerifierProgram β} {st : VerifierProgramState}
    {r : β × VerifierProgramState} (h : runId ((VerifierProgram.readScalarsPacked n).bind f) st = some r) :
    n ≤ st.stream.length := by
  by_contra hn
  obtain ⟨sp, xs, os, R⟩ := st
  simp only at hn
  simp [VerifierProgram.readScalarsPacked, VerifierProgram.bind, runId, Compile.runWithHash, hn] at h

/-- **A packed read of `8 b` words, backwards**: from the carried capacity, `pkAbsorb`. -/
theorem natReadPacked {b : ℕ} {f : List E → VerifierProgram β} {cap : List E} {sp : Sponge}
    (hs : (⟨cap, []⟩ : Fs).Carries sp) {xs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)}
    {r : β × VerifierProgramState}
    (h : runId ((VerifierProgram.readScalarsPacked (8 * b)).bind f) ⟨sp, xs, os, R⟩ = some r) :
    ∃ msg rest, msg.length = 8 * b ∧ xs = msg ++ rest ∧ ∃ sp', (⟨Link.pkAbsorb b msg cap, []⟩ : Fs).Carries sp' ∧
      runId (f msg) ⟨sp', rest, os, R⟩ = some r := by
  have hl := readPacked_len h
  simp only at hl
  have hm : (xs.take (8 * b)).length = 8 * b := by simp; omega
  have hx : xs = xs.take (8 * b) ++ xs.drop (8 * b) := (List.take_append_drop _ _).symm
  rw [hx] at h
  obtain ⟨sp', hc, h'⟩ := natBind_fwd (Link.runsTo_readPacked cap (xs.take (8 * b)) hm) hs h
  exact ⟨_, _, hm, hx, sp', hc, h'⟩

/-- **A requirement, backwards.** -/
theorem natRequire {c : Prop} [Decidable c] {f : Unit → VerifierProgram β} {st : VerifierProgramState}
    {r : β × VerifierProgramState} (h : runId ((VerifierProgram.require c).bind f) st = some r) :
    c ∧ runId (f ()) st = some r := by
  unfold VerifierProgram.require at h
  split_ifs at h with hc
  · exact ⟨hc, h⟩
  · exact absurd h (by simp [VerifierProgram.bind, runId, Compile.runWithHash])

/-- **A return, backwards.** -/
theorem natRet {a : α} {st : VerifierProgramState} {r : α × VerifierProgramState}
    (h : runId (VerifierProgram.ret a) st = some r) : r = (a, st) := (Option.some.inj h).symm

end
end LeanVM.Guest.B1.VsC
