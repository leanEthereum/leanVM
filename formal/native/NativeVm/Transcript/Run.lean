module

public import NativeVm.Input

/-!
# `run`, one constructor at a time

The deployed reading `run (m := Id) keccakF1600` of each constructor of the verifier language as a
step on the state (`readStep`, `sampleStep`, `grindStep`, `commitStep`, `queryStep`) followed by
the program's continuation (`run_read`, …), and `run` of a `bind` (`run_bind`). The gadgets'
specifications (`NativeVm.Transcript`) are stated with these steps.
-/

@[expose] public section

namespace NativeVm.Transcript

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

/-- `run` over Keccak-f[1600], in `Id`. -/
abbrev runK {α : Type} (p : VerifierProgram α) (st : VerifierProgramState) :
    Option (α × VerifierProgramState) :=
  Id.run (run (m := Id) keccakF1600 p st)

/-- `read`: the next scalar, absorbed; `none` at the stream's end or while a challenge waits. -/
def readStep (st : VerifierProgramState) : Option (E × VerifierProgramState) :=
  match st.stream, st.sponge.ground with
  | x :: xs, none =>
    some (x, ⟨Id.run (absorb (m := Id) keccakF1600 st.sponge x dsObserve), xs, st.openings,
      st.roots⟩)
  | _, _ => none

/-- `sample`: the challenge squeezed. -/
def sampleStep (st : VerifierProgramState) : E × VerifierProgramState :=
  let r := Id.run (squeeze (m := Id) keccakF1600 st.sponge)
  (r.1, { st with sponge := r.2 })

/-- `grind bits`: the nonce read, absorbed and permuted, its proof of work checked. -/
def grindStep (bits : Nat) (st : VerifierProgramState) : Option VerifierProgramState :=
  match st.stream, st.sponge.ground with
  | n :: xs, none =>
    let r := Id.run (absorbNonce (m := Id) keccakF1600 st.sponge n)
    if powOk bits r.1 then some { st with sponge := r.2, stream := xs } else none
  | _, _ => none

/-- `commit height width`: two scalars absorbed, their digest appended to the roots. -/
def commitStep (height width : Nat) (st : VerifierProgramState) : Option VerifierProgramState :=
  match st.stream, st.sponge.ground with
  | x0 :: x1 :: xs, none =>
    let sp := Id.run (absorb (m := Id) keccakF1600 st.sponge x0 dsObserve)
    let sp := Id.run (absorb (m := Id) keccakF1600 sp x1 dsObserve)
    some ⟨sp, xs, st.openings, st.roots ++ [(digestFromHalves (x0, x1), height, width)]⟩
  | _, _ => none

/-- `query i positions`: the next phase opened against root `i`. -/
def queryStep (i : Nat) (ps : List Nat) (st : VerifierProgramState) :
    Option (List (List K) × VerifierProgramState) :=
  match st.roots[i]?, st.openings with
  | some (root, height, width), phase :: rest =>
    match Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) with
    | some rows => some (rows, { st with openings := rest })
    | none => none
  | _, _ => none

variable {α β : Type}

theorem run_ret (a : α) (st : VerifierProgramState) : runK (.ret a) st = some (a, st) := (rfl)

theorem run_fail (st : VerifierProgramState) : runK (α := α) .fail st = none := (rfl)

theorem run_read (k : E → VerifierProgram α) (st : VerifierProgramState) :
    runK (.read k) st = match readStep st with
      | some (x, st') => runK (k x) st'
      | none => none := by
  unfold runK readStep
  rw [Compile.run.eq_def]
  rcases st with ⟨⟨_, _, g⟩, xs, _, _⟩
  cases xs <;> cases g <;> rfl

theorem run_sample (k : E → VerifierProgram α) (st : VerifierProgramState) :
    runK (.sample k) st = runK (k (sampleStep st).1) (sampleStep st).2 := by
  unfold runK sampleStep
  rw [Compile.run.eq_def]
  rfl

theorem run_grind (bits : Nat) (k : VerifierProgram α) (st : VerifierProgramState) :
    runK (.grind bits k) st = match grindStep bits st with
      | some st' => runK k st'
      | none => none := by
  unfold runK grindStep
  rw [Compile.run.eq_def]
  rcases st with ⟨⟨_, _, g⟩, xs, _, _⟩
  cases xs with
  | nil => cases g <;> rfl
  | cons n xs =>
    cases g with
    | some _ => rfl
    | none =>
      simp only
      generalize absorbNonce (m := Id) keccakF1600 _ n = r
      rcases r with ⟨pow, sp'⟩
      by_cases hb : powOk bits pow = true
      · simp only [Id.run, bind, hb, ite_true]
      · simp only [Id.run, bind, hb, Bool.false_eq_true, ite_false]; rfl

theorem run_commit (h w : Nat) (k : VerifierProgram α) (st : VerifierProgramState) :
    runK (.commit h w k) st = match commitStep h w st with
      | some st' => runK k st'
      | none => none := by
  unfold runK commitStep
  rw [Compile.run.eq_def]
  rcases st with ⟨⟨_, _, g⟩, xs, _, _⟩
  rcases xs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> cases g <;> rfl

theorem run_query (i : Nat) (ps : List Nat) (k : List (List K) → VerifierProgram α)
    (st : VerifierProgramState) :
    runK (.query i ps k) st = match queryStep i ps st with
      | some (rows, st') => runK (k rows) st'
      | none => none := by
  unfold runK queryStep
  rw [Compile.run.eq_def]
  rcases st with ⟨sp, xs, os, rs⟩
  simp only
  cases rs[i]? with
  | none => rfl
  | some r =>
    rcases r with ⟨root, height, width⟩
    cases os with
    | nil => rfl
    | cons phase rest =>
      simp only
      generalize openPhase (m := Id) keccakF1600 root height width ps phase = o
      rcases o with _ | rows <;> rfl

/-- `run` of a sequence: the first program, then the second on its result. -/
theorem run_bind (p : VerifierProgram α) (f : α → VerifierProgram β)
    (st : VerifierProgramState) :
    runK (p.bind f) st = match runK p st with
      | some (a, st') => runK (f a) st'
      | none => none := by
  induction p generalizing st with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    rw [VerifierProgram.bind, run_read, run_read]
    cases readStep st with
    | none => rfl
    | some r => exact ih r.1 r.2
  | sample k ih =>
    rw [VerifierProgram.bind, run_sample, run_sample]
    exact ih _ _
  | grind b k ih =>
    rw [VerifierProgram.bind, run_grind, run_grind]
    cases grindStep b st with
    | none => rfl
    | some st' => exact ih st'
  | commit h w k ih =>
    rw [VerifierProgram.bind, run_commit, run_commit]
    cases commitStep h w st with
    | none => rfl
    | some st' => exact ih st'
  | query i ps k ih =>
    rw [VerifierProgram.bind, run_query, run_query]
    cases queryStep i ps st with
    | none => rfl
    | some r => exact ih r.1 r.2

/-- `runProof` over Keccak-f[1600]: the run from the seed, then the proof consumed. -/
theorem runProof_eq (program : VerifierProgram Bool) (seed : KeccakState) (proof : Proof) :
    Id.run (runProof (m := Id) keccakF1600 program seed proof) =
      match runK program ⟨⟨seed, [], none⟩, proof.stream, proof.openings, []⟩ with
      | some (true, st) => st.stream.isEmpty && st.openings.isEmpty
      | _ => false := by
  unfold runProof runK
  show (match Id.run (Compile.run (m := Id) keccakF1600 program _) with
    | some (true, s) => _ | _ => _) = _
  generalize Id.run (Compile.run (m := Id) keccakF1600 program _) = r
  rcases r with _ | ⟨_ | _, _⟩ <;> rfl

end NativeVm.Transcript
