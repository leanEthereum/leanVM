import Statement.LeanVmVerifier

/-!
# The Rust transcript, and how it runs the statement's programs

`crates/verifier/src/transcript.rs`'s `Transcript` holds the proof, the sponge and how many
scalars and phases of openings it has read. `TState` is that, plus the roots the statement's
`VerifierProgramState` keeps (a ghost: the Rust passes each root to `merkle` itself). A Rust
function that takes `&mut Transcript` and returns `Result` is mirrored in `TM`, the state monad
over `TState` that fails on any `Err`.

`Sim m P` says the mirror `m` runs the statement's program fragment `P`: whenever `m` returns
`a`, the statement's `run` of `P` (over Keccak-f[1600]) from the state `TState.toSpec` stands for
returns `a` in the state the final transcript stands for. It is the soundness direction (an `Err`
rejects anyway), and it composes through `bind` (`Sim.bind`).
-/

namespace Rv64Verifier.Model
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.KeccakHash

/-- The Rust `Transcript`, with the roots read so far as a ghost. -/
structure TState where
  proof : Proof
  sponge : Sponge
  streamOffset : ℕ
  openingOffset : ℕ
  roots : List (Digest × ℕ × ℕ)

/-- The statement's state a transcript stands for. -/
def TState.toSpec (t : TState) : VerifierProgramState :=
  ⟨t.sponge, t.proof.stream.drop t.streamOffset, t.proof.openings.drop t.openingOffset, t.roots⟩

/-- The Rust transcript's methods: `none` is any `Err`. -/
abbrev TM := StateT TState Option

/-- The statement's run over Keccak-f[1600]. -/
def runK {α : Type} (P : VerifierProgram α) (σ : VerifierProgramState) :
    Option (α × VerifierProgramState) :=
  Id.run (run (m := Id) keccakF1600 P σ)

/-- `m` runs `P`. -/
def Sim {α : Type} (m : TM α) (P : VerifierProgram α) : Prop :=
  ∀ t a t', m.run t = some (a, t') → runK P t.toSpec = some (a, t'.toSpec)

/-! ## The statement's run, sequenced -/

theorem runK_bind {α β : Type} (P : VerifierProgram α) (Q : α → VerifierProgram β)
    (σ : VerifierProgramState) :
    runK (P >>= Q) σ = match runK P σ with
      | some (a, σ') => runK (Q a) σ'
      | none => none := by
  show runK (P.bind Q) σ = _
  induction P generalizing σ with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    simp only [VerifierProgram.bind, runK]
    rw [Compile.run, Compile.run]
    rcases σ.stream with _ | ⟨x, xs⟩
    · rfl
    · exact ih x _
  | sample k ih =>
    simp only [VerifierProgram.bind, runK]
    rw [Compile.run, Compile.run]
    exact ih _ _
  | grind bits k ih =>
    simp only [VerifierProgram.bind, runK]
    rw [Compile.run, Compile.run]
    rcases σ.stream with _ | ⟨x, xs⟩
    · rfl
    · simp only [Id.run, bind, pure]
      rcases squeeze (m := Id) keccakF1600 (absorb (m := Id) keccakF1600 σ.sponge x dsPowNonce)
        with ⟨c, sp⟩
      dsimp only
      split_ifs
      · exact ih _
      · rfl
  | commit h w k ih =>
    simp only [VerifierProgram.bind, runK]
    rw [Compile.run, Compile.run]
    rcases σ.stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
    · rfl
    · rfl
    · simp only [Id.run, bind, pure]
      split
      · exact ih _
      · rfl
  | query i ps k ih =>
    simp only [VerifierProgram.bind, runK]
    rw [Compile.run, Compile.run]
    split
    · simp only [Id.run, bind, pure]
      split
      · exact ih _ _
      · rfl
    · rfl

/-! ## Composing simulations -/

theorem Sim.pure {α : Type} (a : α) : Sim (Pure.pure a : TM α) (VerifierProgram.ret a) := by
  intro t b t' h
  simp only [StateT.run_pure] at h
  cases h
  rfl

theorem Sim.bind {α β : Type} {m : TM α} {P : VerifierProgram α} {k : α → TM β}
    {Q : α → VerifierProgram β} (hm : Sim m P) (hk : ∀ a, Sim (k a) (Q a)) :
    Sim (m >>= k) (P >>= Q) := by
  intro t b t' h
  rw [StateT.run_bind] at h
  cases hmt : m.run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨a, t₁⟩ := p
    rw [hmt] at h
    rw [runK_bind, hm t a t₁ hmt]
    exact hk a t₁ b t' h

/-! ## The transcript's methods -/

namespace TM

/-- `Transcript::next`: the next scalar of the stream, not absorbed. -/
def next : TM E := fun t ↦
  match t.proof.stream[t.streamOffset]? with
  | some x => some (x, { t with streamOffset := t.streamOffset + 1 })
  | none => none

/-- `Sponge::absorb` of the transcript's sponge. -/
def absorbTag (x : E) (tag : ℕ) : TM Unit := fun t ↦
  some ((), { t with sponge := Id.run (absorb (m := Id) keccakF1600 t.sponge x tag) })

/-- `Transcript::next_scalar`: read, then observe. -/
def nextScalar : TM E := fun t ↦
  match t.proof.stream[t.streamOffset]? with
  | some x =>
    some (x, { t with
      streamOffset := t.streamOffset + 1
      sponge := Id.run (absorb (m := Id) keccakF1600 t.sponge x dsObserve) })
  | none => none

/-- `Transcript::sample`. -/
def sample : TM E := fun t ↦
  let r := Id.run (squeeze (m := Id) keccakF1600 t.sponge)
  some (r.1, { t with sponge := r.2 })

/-- `Transcript::next_scalars`. -/
def nextScalars : ℕ → TM (List E)
  | 0 => pure []
  | n + 1 => do
    let x ← nextScalar
    let xs ← nextScalars n
    pure (x :: xs)

/-- `Transcript::samples`. -/
def samples : ℕ → TM (List E)
  | 0 => pure []
  | n + 1 => do
    let x ← sample
    let xs ← samples n
    pure (x :: xs)

/-- `Transcript::grind_check(bits)` in checked mode: the nonce read and absorbed with its own
tag, a challenge drawn, the proof of work checked (`powOk`: the low `bits` bits of the challenge's
first limb are zero, or the nonce is zero when `bits = 0`). -/
def grind (bits : ℕ) : TM Unit := fun t ↦
  match t.proof.stream[t.streamOffset]? with
  | some n =>
    let r := Id.run (squeeze (m := Id) keccakF1600
      (Id.run (absorb (m := Id) keccakF1600 t.sponge n dsPowNonce)))
    if powOk bits n r.1 then some ((), { t with streamOffset := t.streamOffset + 1, sponge := r.2 })
    else none
  | none => none

/-- A commitment's root: `next_scalars(2)`, both observed, then `Digest::from_halves`; the root is
kept as a ghost with the shape of its tree. -/
def commit (height width : ℕ) : TM Digest := fun t ↦
  match t.proof.stream[t.streamOffset]?, t.proof.stream[t.streamOffset + 1]? with
  | some x0, some x1 =>
    let sponge := Id.run (absorb (m := Id) keccakF1600
      (Id.run (absorb (m := Id) keccakF1600 t.sponge x0 dsObserve)) x1 dsObserve)
    match digestFromHalves (x0, x1) with
    | some root => some (root, { t with
        streamOffset := t.streamOffset + 2
        sponge := sponge
        roots := t.roots ++ [(root, height, width)] })
    | none => none
  | _, _ => none

/-- `Transcript::merkle` on the `i`-th root read: the next phase of openings, checked against the
root at `positions`; the leaves. -/
def merkle (i : ℕ) (positions : List ℕ) : TM (List (List K)) := fun t ↦
  match t.roots[i]?, t.proof.openings[t.openingOffset]? with
  | some (root, height, width), some phase =>
    match Id.run (openPhase (m := Id) keccakF1600 root height width positions phase) with
    | some rows => some (rows, { t with openingOffset := t.openingOffset + 1 })
    | none => none
  | _, _ => none

/-- `require(c, _)?`. -/
def require (c : Prop) [Decidable c] : TM Unit := fun t ↦ if c then some ((), t) else none

end TM

theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

theorem drop_cons_of_getElem? {α : Type} {l : List α} {i : ℕ} {x : α} (h : l[i]? = some x) :
    l.drop i = x :: l.drop (i + 1) := by
  have hlt : i < l.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  rw [List.getElem?_eq_getElem hlt] at h
  rw [List.drop_eq_getElem_cons hlt, Option.some.inj h]

theorem Sim.nextScalar : Sim TM.nextScalar VerifierProgram.readScalar := by
  intro t a t' h
  simp only [TM.nextScalar, StateT.run] at h
  split at h
  · rename_i x hx
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hlt : t.streamOffset < t.proof.stream.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hx; cases hx
    have hx' : t.proof.stream[t.streamOffset] = x := by
      rw [List.getElem?_eq_getElem hlt] at hx; exact Option.some.inj hx
    simp only [VerifierProgram.readScalar, runK, TState.toSpec, Compile.run,
      List.drop_eq_getElem_cons hlt, hx']
    rfl
  · simp at h

theorem Sim.sample : Sim TM.sample VerifierProgram.sampleChallenge := by
  intro t a t' h
  simp only [TM.sample, StateT.run, Option.some.injEq] at h
  cases h
  rfl

theorem Sim.nextScalars : ∀ n, Sim (TM.nextScalars n) (VerifierProgram.readScalars n)
  | 0 => Sim.pure []
  | n + 1 => Sim.bind Sim.nextScalar fun x ↦
      Sim.bind (Sim.nextScalars n) fun xs ↦ Sim.pure (x :: xs)

theorem Sim.samples : ∀ n, Sim (TM.samples n) (VerifierProgram.sampleChallenges n)
  | 0 => Sim.pure []
  | n + 1 => Sim.bind Sim.sample fun x ↦ Sim.bind (Sim.samples n) fun xs ↦ Sim.pure (x :: xs)

theorem Sim.grind (bits : ℕ) : Sim (TM.grind bits) (VerifierProgram.grindProofOfWork bits) := by
  intro t a t' h
  simp only [TM.grind, StateT.run] at h
  split at h
  · rename_i n hn
    split_ifs at h with hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [VerifierProgram.grindProofOfWork, runK, TState.toSpec, Compile.run,
      drop_cons_of_getElem? hn]
    simp only [Id.run] at hp
    simp only [id_bind, hp, ↓reduceIte]
    rfl
  · cases h

/-- `m` runs `P`, whose value the Rust does not use (a commitment: the Rust keeps the root it
read, the statement its index in the roots). -/
def SimUnit {α : Type} (m : TM α) (P : VerifierProgram Unit) : Prop :=
  ∀ t a t', m.run t = some (a, t') → runK P t.toSpec = some ((), t'.toSpec)

theorem Sim.bindUnit {α β : Type} {m : TM α} {P : VerifierProgram Unit} {k : α → TM β}
    {Q : VerifierProgram β} (hm : SimUnit m P) (hk : ∀ a, Sim (k a) Q) :
    Sim (m >>= k) (P >>= fun _ ↦ Q) := by
  intro t b t' h
  rw [StateT.run_bind] at h
  cases hmt : m.run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨a, t₁⟩ := p
    rw [hmt] at h
    rw [runK_bind, hm t a t₁ hmt]
    exact hk a t₁ b t' h

theorem SimUnit.commit (height width : ℕ) :
    SimUnit (TM.commit height width) (VerifierProgram.readCommitment height width) := by
  intro t a t' h
  simp only [TM.commit, StateT.run] at h
  split at h
  · rename_i x0 x1 h0 h1
    split at h
    · rename_i root hroot
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have hd : t.proof.stream.drop t.streamOffset =
          x0 :: x1 :: t.proof.stream.drop (t.streamOffset + 2) := by
        rw [drop_cons_of_getElem? h0, drop_cons_of_getElem? h1]
      simp only [VerifierProgram.readCommitment, runK, TState.toSpec, Compile.run, hd]
      simp only [Id.run, bind, pure, hroot]
    · cases h
  · cases h

theorem Sim.merkle (i : ℕ) (positions : List ℕ) :
    Sim (TM.merkle i positions) (VerifierProgram.queryOpenings i positions) := by
  intro t a t' h
  simp only [TM.merkle, StateT.run] at h
  split at h
  · rename_i root height width phase hr hp
    split at h
    · rename_i rows hrows
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [VerifierProgram.queryOpenings, runK, TState.toSpec, Compile.run, hr,
        drop_cons_of_getElem? hp]
      simp only [Id.run] at hrows ⊢
      rw [hrows]
      rfl
    · cases h
  · cases h

theorem Sim.require (c : Prop) [Decidable c] : Sim (TM.require c) (VerifierProgram.require c) := by
  intro t a t' h
  simp only [TM.require, StateT.run] at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp only [VerifierProgram.require, hc, ↓reduceIte]
  rfl

end Rv64Verifier.Model
