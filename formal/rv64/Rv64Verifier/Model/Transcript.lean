import Statement.LeanVmVerifier
import Rv64Verifier.Model.Multilinear

/-!
# The Rust transcript, and how it runs the statement's programs

`crates/verifier/src/transcript.rs`'s `Transcript` holds the proof, the sponge and how many
scalars and phases of openings it has read. `TState` is that, plus the roots the statement's
`VerifierProgramState` keeps (a ghost: the Rust passes each root to `merkle` itself). A Rust
function that takes `&mut Transcript` and returns `Result` is mirrored in `TM`, the state monad
over `TState` that fails on any `Err` or panic.

`SimR m P r` says the mirror `m` runs the statement's program fragment `P` up to `r`: whenever `m`
returns `a`, the statement's `run` of `P` (over Keccak-f[1600]) from the state `TState.toSpec`
stands for returns some `b` with `r a b`, in the state the final transcript stands for. `Sim` is
`SimR` with equality. It is the soundness direction (an `Err` rejects anyway), and it composes
through `bind` (`SimR.bind`). `Returns m R` says what `m` returns satisfies `R`.

The mirrors of the transcript's methods, `sumcheck_round_poly` and `sumcheck` are here, each
with its simulation; the other files compose them.
-/

namespace Rv64Verifier.Model
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

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

/-- The Rust transcript's methods: `none` is any `Err` or panic. -/
abbrev TM := StateT TState Option

/-- The statement's run over Keccak-f[1600]. -/
def runK {α : Type} (P : VerifierProgram α) (σ : VerifierProgramState) :
    Option (α × VerifierProgramState) :=
  Id.run (run (m := Id) keccakF1600 P σ)

/-- `m` runs `P`, its value related to `P`'s by `r`. -/
def SimR {α β : Type} (m : TM α) (P : VerifierProgram β) (r : α → β → Prop) : Prop :=
  ∀ t a t', m.run t = some (a, t') → ∃ b, runK P t.toSpec = some (b, t'.toSpec) ∧ r a b

/-- `m` runs `P`, returning the same value. -/
def Sim {α : Type} (m : TM α) (P : VerifierProgram α) : Prop := SimR m P (· = ·)

theorem Sim.intro {α : Type} {m : TM α} {P : VerifierProgram α}
    (h : ∀ t a t', m.run t = some (a, t') → runK P t.toSpec = some (a, t'.toSpec)) : Sim m P :=
  fun t a t' hm ↦ ⟨a, h t a t' hm, rfl⟩

theorem Sim.run_eq {α : Type} {m : TM α} {P : VerifierProgram α} (h : Sim m P) {t : TState}
    {a : α} {t' : TState} (hm : m.run t = some (a, t')) :
    runK P t.toSpec = some (a, t'.toSpec) := by
  obtain ⟨b, hb, rfl⟩ := h t a t' hm
  exact hb

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

theorem VerifierProgram.bind_assoc {α β γ : Type} (P : VerifierProgram α)
    (f : α → VerifierProgram β) (g : β → VerifierProgram γ) :
    (P >>= f) >>= g = P >>= fun x ↦ f x >>= g := by
  show (P.bind f).bind g = P.bind fun x ↦ (f x).bind g
  induction P with
  | ret a => rfl
  | fail => rfl
  | read k ih => simp only [VerifierProgram.bind, ih]
  | sample k ih => simp only [VerifierProgram.bind, ih]
  | grind b k ih => simp only [VerifierProgram.bind, ih]
  | commit h w k ih => simp only [VerifierProgram.bind, ih]
  | query i ps k ih => simp only [VerifierProgram.bind, ih]

theorem VerifierProgram.bind_ret {α : Type} (P : VerifierProgram α) :
    (P >>= fun x ↦ VerifierProgram.ret x) = P := by
  show P.bind VerifierProgram.ret = P
  induction P with
  | ret a => rfl
  | fail => rfl
  | read k ih => simp only [VerifierProgram.bind, ih]
  | sample k ih => simp only [VerifierProgram.bind, ih]
  | grind b k ih => simp only [VerifierProgram.bind, ih]
  | commit h w k ih => simp only [VerifierProgram.bind, ih]
  | query i ps k ih => simp only [VerifierProgram.bind, ih]

theorem VerifierProgram.ret_bind {α β : Type} (a : α) (f : α → VerifierProgram β) :
    (VerifierProgram.ret a >>= f) = f a := rfl

/-! ## Composing simulations -/

theorem SimR.mono {α β : Type} {m : TM α} {P : VerifierProgram β} {r r' : α → β → Prop}
    (h : SimR m P r) (hr : ∀ a b, r a b → r' a b) : SimR m P r' := by
  intro t a t' hm
  obtain ⟨b, hb, hab⟩ := h t a t' hm
  exact ⟨b, hb, hr a b hab⟩

theorem SimR.congr {α β : Type} {m : TM α} {P P' : VerifierProgram β} {r : α → β → Prop}
    (h : P = P') (hm : SimR m P' r) : SimR m P r := h ▸ hm

theorem SimR.pure {α β : Type} {r : α → β → Prop} {a : α} {b : β} (h : r a b) :
    SimR (Pure.pure a : TM α) (VerifierProgram.ret b) r := by
  intro t a' t' hm
  simp only [StateT.run_pure] at hm
  cases hm
  exact ⟨b, rfl, h⟩

theorem SimR.bind {α β γ δ : Type} {m : TM α} {P : VerifierProgram β} {r : α → β → Prop}
    {k : α → TM γ} {Q : β → VerifierProgram δ} {r' : γ → δ → Prop} (hm : SimR m P r)
    (hk : ∀ a b, r a b → SimR (k a) (Q b) r') : SimR (m >>= k) (P >>= Q) r' := by
  intro t c t' h
  rw [StateT.run_bind] at h
  cases hmt : m.run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨a, t₁⟩ := p
    rw [hmt] at h
    obtain ⟨b, hb, hab⟩ := hm t a t₁ hmt
    rw [runK_bind, hb]
    exact hk a b hab t₁ c t' h

theorem SimR.of_sim {α : Type} {m : TM α} {P : VerifierProgram α} (h : Sim m P) :
    SimR m P (· = ·) := h

theorem Sim.of_simR {α : Type} {m : TM α} {P : VerifierProgram α} (h : SimR m P (· = ·)) :
    Sim m P := h

theorem Sim.congr {α : Type} {m : TM α} {P P' : VerifierProgram α} (h : P = P') (hm : Sim m P') :
    Sim m P := h ▸ hm

theorem Sim.pure {α : Type} (a : α) : Sim (Pure.pure a : TM α) (VerifierProgram.ret a) :=
  SimR.pure rfl

/-- A step whose value both sides share. -/
theorem SimR.bindEq {α γ δ : Type} {m : TM α} {P : VerifierProgram α} {k : α → TM γ}
    {Q : α → VerifierProgram δ} {r : γ → δ → Prop} (hm : Sim m P) (hk : ∀ a, SimR (k a) (Q a) r) :
    SimR (m >>= k) (P >>= Q) r :=
  SimR.bind hm fun a _ h ↦ by subst h; exact hk a

theorem Sim.bind {α β : Type} {m : TM α} {P : VerifierProgram α} {k : α → TM β}
    {Q : α → VerifierProgram β} (hm : Sim m P) (hk : ∀ a, Sim (k a) (Q a)) :
    Sim (m >>= k) (P >>= Q) :=
  SimR.bindEq hm hk

/-- A mirror whose value the statement reads through `f`. -/
theorem SimR.map_sim {α β : Type} {m : TM α} {P : VerifierProgram β} {f : α → β}
    (h : SimR m P fun a b ↦ f a = b) : Sim (f <$> m) P := by
  intro t b t' hr
  rw [StateT.run_map] at hr
  cases hmt : m.run t with
  | none => simp [hmt] at hr
  | some p =>
    obtain ⟨a, t₁⟩ := p
    simp only [hmt, Option.map_eq_map, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact h t a t₁ hmt

theorem SimR.of_map {α β : Type} {m : TM α} {P : VerifierProgram β} {f : α → β}
    (h : Sim (f <$> m) P) : SimR m P fun a b ↦ f a = b := by
  intro t a t' hm
  have hr : (f <$> m).run t = some (f a, t') := by
    rw [StateT.run_map, hm]
    rfl
  exact ⟨f a, h.run_eq hr, rfl⟩

/-- `m` runs `P`, whose value the Rust does not use (a commitment: the Rust keeps the root it
read, the statement its index in the roots). -/
def SimUnit {α : Type} (m : TM α) (P : VerifierProgram Unit) : Prop := SimR m P fun _ _ ↦ True

theorem SimR.bindUnit {α γ δ : Type} {m : TM α} {P : VerifierProgram Unit} {k : α → TM γ}
    {Q : VerifierProgram δ} {r' : γ → δ → Prop} (hm : SimUnit m P) (hk : ∀ a, SimR (k a) Q r') :
    SimR (m >>= k) (P >>= fun _ ↦ Q) r' :=
  SimR.bind hm fun a _ _ ↦ hk a

theorem Sim.bindUnit {α β : Type} {m : TM α} {P : VerifierProgram Unit} {k : α → TM β}
    {Q : VerifierProgram β} (hm : SimUnit m P) (hk : ∀ a, Sim (k a) Q) :
    Sim (m >>= k) (P >>= fun _ ↦ Q) :=
  SimR.bindUnit hm hk

/-! ## What a mirror returns -/

/-- What a mirror returns satisfies `R`. -/
def Returns {α : Type} (m : TM α) (R : α → Prop) : Prop :=
  ∀ t a t', m.run t = some (a, t') → R a

theorem Returns.pure {α : Type} {R : α → Prop} {a : α} (h : R a) :
    Returns (Pure.pure a : TM α) R := by
  intro t b t' hr
  cases (Option.some.inj hr : ((a, t) : α × TState) = (b, t'))
  exact h

theorem Returns.bind {α β : Type} {m : TM α} {k : α → TM β} {R : α → Prop} {S : β → Prop}
    (hm : Returns m R) (hk : ∀ a, R a → Returns (k a) S) : Returns (m >>= k) S := by
  intro t b t' h
  rw [StateT.run_bind] at h
  cases hmt : m.run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨a, t₁⟩ := p
    rw [hmt] at h
    exact hk a (hm t a t₁ hmt) t₁ b t' h

theorem Returns.true {α : Type} (m : TM α) : Returns m fun _ ↦ True := fun _ _ _ _ ↦ trivial

theorem Returns.bindAll {α β : Type} {m : TM α} {k : α → TM β} {S : β → Prop}
    (hk : ∀ a, Returns (k a) S) : Returns (m >>= k) S :=
  Returns.bind (Returns.true m) fun a _ ↦ hk a

theorem SimR.and_returns {α β : Type} {m : TM α} {P : VerifierProgram β} {r : α → β → Prop}
    {R : α → Prop} (h : SimR m P r) (hR : Returns m R) : SimR m P fun a b ↦ r a b ∧ R a := by
  intro t a t' hm
  obtain ⟨b, hb, hab⟩ := h t a t' hm
  exact ⟨b, hb, hab, hR t a t' hm⟩

theorem SimR.bindPost {α γ δ : Type} {m : TM α} {P : VerifierProgram α} {k : α → TM γ}
    {Q : α → VerifierProgram δ} {r : γ → δ → Prop} {R : α → Prop} (hm : Sim m P)
    (hR : Returns m R) (hk : ∀ a, R a → SimR (k a) (Q a) r) : SimR (m >>= k) (P >>= Q) r :=
  SimR.bind (SimR.and_returns hm hR) fun a _ h ↦ by obtain ⟨rfl, hRa⟩ := h; exact hk a hRa

theorem Sim.bindPost {α β : Type} {m : TM α} {P : VerifierProgram α} {k : α → TM β}
    {Q : α → VerifierProgram β} {R : α → Prop} (hm : Sim m P) (hR : Returns m R)
    (hk : ∀ a, R a → Sim (k a) (Q a)) : Sim (m >>= k) (P >>= Q) :=
  SimR.bindPost hm hR hk

/-! ## Failures, checks, and reads of the transcript's position -/

namespace TM

/-- A Rust failure (`Err` or panic). -/
def fail {α : Type} : TM α := fun _ ↦ none

/-- `?` on a pure `Option`: an `Err` or a panic of a pure step. -/
def ofOption {α : Type} : Option α → TM α
  | some a => Pure.pure a
  | none => TM.fail

/-- `TM.ofOption`, as `Model.Bus` names it. -/
abbrev lift {α : Type} (o : Option α) : TM α := TM.ofOption o

/-- `require(c, _)?`. -/
def require (c : Prop) [Decidable c] : TM Unit := fun t ↦ if c then some ((), t) else none

/-- `Transcript::stream_offset`. -/
def streamPosition : TM ℕ := fun t ↦ some (t.streamOffset, t)

/-- `Transcript::finish`: nothing of the proof is left unread. -/
def finish : TM Unit := fun t ↦
  if t.streamOffset = t.proof.stream.length ∧ t.openingOffset = t.proof.openings.length then
    some ((), t)
  else none

end TM

theorem SimR.fail_left {α β : Type} {P : VerifierProgram β} {r : α → β → Prop} :
    SimR (TM.fail : TM α) P r := by
  intro t a t' h
  cases h

theorem SimR.ofOption_bind {α γ δ : Type} {o : Option α} {k : α → TM γ} {Q : VerifierProgram δ}
    {r : γ → δ → Prop} (hk : ∀ a, o = some a → SimR (k a) Q r) :
    SimR (TM.ofOption o >>= k) Q r := by
  cases o with
  | none => intro t a t' h; cases h
  | some a =>
    intro t c t' h
    simp only [TM.ofOption, StateT.run_bind, StateT.run_pure] at h
    exact hk a rfl t c t' h

/-- A pure step of the Rust's against one of the statement's that reads nothing. -/
theorem SimR.ofOption {α β : Type} {o : Option α} {P : VerifierProgram β} {r : α → β → Prop}
    (h : ∀ a, o = some a → ∃ b, (∀ σ, runK P σ = some (b, σ)) ∧ r a b) :
    SimR (TM.ofOption o) P r := by
  cases o with
  | none => intro t a t' h; cases h
  | some a =>
    intro t c t' hm
    simp only [TM.ofOption, StateT.run_pure] at hm
    cases (Option.some.inj hm : ((a, t) : α × TState) = (c, t'))
    obtain ⟨b, hb, hab⟩ := h a rfl
    exact ⟨b, hb _, hab⟩

theorem Sim.liftBind {α β : Type} {o : Option α} {k : α → TM β} {Q : VerifierProgram β}
    (h : ∀ a, o = some a → Sim (k a) Q) : Sim (TM.lift o >>= k) Q :=
  SimR.ofOption_bind h

theorem Sim.lift {α : Type} {o : Option α} {P : VerifierProgram α}
    (h : ∀ a, o = some a → ∀ σ, runK P σ = some (a, σ)) : Sim (TM.lift o) P :=
  SimR.ofOption fun a ha ↦ ⟨a, h a ha, rfl⟩

theorem Sim.require (c : Prop) [Decidable c] : Sim (TM.require c) (VerifierProgram.require c) := by
  refine Sim.intro fun t a t' h ↦ ?_
  simp only [TM.require, StateT.run] at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp only [VerifierProgram.require, hc, ↓reduceIte]
  rfl

theorem Sim.requireIff {c c' : Prop} [Decidable c] [Decidable c'] (h : c ↔ c') :
    Sim (TM.require c) (VerifierProgram.require c') := by
  refine Sim.intro fun t a t' hr ↦ ?_
  simp only [TM.require, StateT.run] at hr
  split_ifs at hr with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨-, rfl⟩ := hr
  simp only [VerifierProgram.require, h.mp hc, ↓reduceIte]
  rfl

theorem SimR.require_iff {c c' : Prop} [Decidable c] [Decidable c'] (h : c ↔ c') :
    SimR (TM.require c) (VerifierProgram.require c') (fun _ _ ↦ True) :=
  SimR.mono (Sim.requireIff h) fun _ _ _ ↦ trivial

/-- A check both make; what follows may use it. -/
theorem SimR.require_post {c c' : Prop} [Decidable c] [Decidable c'] (h : c ↔ c') :
    SimR (TM.require c) (VerifierProgram.require c') (fun _ _ ↦ c) := by
  intro t a t' hm
  simp only [TM.require, StateT.run] at hm
  by_cases hc : c
  · rw [ite_eq_left hc] at hm
    cases hm
    refine ⟨(), ?_, hc⟩
    simp only [VerifierProgram.require, h.mp hc, ↓reduceIte]
    rfl
  · rw [ite_eq_right hc] at hm
    cases hm

/-- A check of the Rust's that the statement leaves out: the rest runs `Q` when it holds. -/
theorem SimR.require_left {γ δ : Type} {c : Prop} [Decidable c] {k : Unit → TM γ}
    {Q : VerifierProgram δ} {r : γ → δ → Prop} (hk : c → SimR (k ()) Q r) :
    SimR (TM.require c >>= k) Q r := by
  intro t a t' h
  rw [StateT.run_bind] at h
  simp only [TM.require, StateT.run] at h
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    exact hk hc t a t' h
  · rw [ite_eq_right hc] at h
    cases h

/-- A read of the stream's position, which the statement does not make. -/
theorem SimR.streamPosition_left {γ δ : Type} {k : ℕ → TM γ} {Q : VerifierProgram δ}
    {r : γ → δ → Prop} (hk : ∀ n, SimR (k n) Q r) : SimR (TM.streamPosition >>= k) Q r := by
  intro t a t' h
  rw [StateT.run_bind] at h
  exact hk t.streamOffset t a t' h

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

end TM

theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

theorem drop_cons_of_getElem? {α : Type} {l : List α} {i : ℕ} {x : α} (h : l[i]? = some x) :
    l.drop i = x :: l.drop (i + 1) := by
  have hlt : i < l.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  rw [List.getElem?_eq_getElem hlt] at h
  rw [List.drop_eq_getElem_cons hlt, Option.some.inj h]

theorem Sim.nextScalar : Sim TM.nextScalar VerifierProgram.readScalar := by
  refine Sim.intro fun t a t' h ↦ ?_
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
  refine Sim.intro fun t a t' h ↦ ?_
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

theorem Returns.nextScalars : ∀ n, Returns (TM.nextScalars n) fun xs ↦ xs.length = n
  | 0 => Returns.pure rfl
  | n + 1 => Returns.bind (Returns.true _) fun x _ ↦ Returns.bind (Returns.nextScalars n)
      fun xs hxs ↦ Returns.pure (by simp [hxs])

theorem Returns.samples : ∀ n, Returns (TM.samples n) fun xs ↦ xs.length = n
  | 0 => Returns.pure rfl
  | n + 1 => Returns.bind (Returns.true _) fun x _ ↦ Returns.bind (Returns.samples n)
      fun xs hxs ↦ Returns.pure (by simp [hxs])

theorem Sim.grind (bits : ℕ) : Sim (TM.grind bits) (VerifierProgram.grindProofOfWork bits) := by
  refine Sim.intro fun t a t' h ↦ ?_
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

theorem SimUnit.commit (height width : ℕ) :
    SimUnit (TM.commit height width) (VerifierProgram.readCommitment height width) := by
  refine fun t a t' h ↦ ⟨(), ?_, trivial⟩
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
  refine Sim.intro fun t a t' h ↦ ?_
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

/-! ## `sumcheck_round_poly` and `sumcheck` (`transcript.rs:188-233`) -/

/-- `Transcript::sumcheck_round_poly(count, claim, eq_factor)`. Every caller passes `count ≥ 3`, so
`count - 2` does not wrap. -/
def TM.sumcheckRoundPoly (count : ℕ) (claim : E) : Option E → TM (List E)
  | none => do
    let constant ← TM.nextScalar
    let tail ← TM.nextScalars (count - 2)
    pure ([constant, claim + sumE tail] ++ tail)
  | some eqFactor => do
    let tail ← TM.nextScalars (count - 1)
    pure ([claim + eqFactor * sumE tail] ++ tail)

theorem Sim.sumcheckRoundPoly (count : ℕ) (claim : E) (e : Option E) :
    Sim (TM.sumcheckRoundPoly count claim e) (sumcheckRoundPoly count claim e) := by
  cases e with
  | none => exact Sim.bind Sim.nextScalar fun x ↦ Sim.bind (Sim.nextScalars _) fun xs ↦
      Sim.pure _
  | some f => exact Sim.bind (Sim.nextScalars _) fun xs ↦ Sim.pure _

/-- One iteration of `sumcheck`'s loop: the round polynomial, the challenge, `point.push`, the
claim at the challenge. -/
def TM.sumcheckRound (count : ℕ) (acc : List E × E) (equality : Option E) : TM (List E × E) := do
  let message ← TM.sumcheckRoundPoly count acc.2 equality
  let challenge ← TM.sample
  pure (acc.1 ++ [challenge], polyEvalRust message challenge)

/-- `sumcheck(transcript, claim, count, equalities)`. -/
def TM.sumcheck (claim : E) (count : ℕ) (equalities : List (Option E)) : TM (List E × E) :=
  equalities.foldlM (TM.sumcheckRound count) ([], claim)

/-- The loop after the point pushed so far, followed by `k`. -/
theorem SimR.sumcheckLoop_bind {β γ : Type} (count : ℕ) {r : β → γ → Prop} :
    ∀ (eqs : List (Option E)) (pre : List E) (claim : E) (k : List E × E → TM β)
    (K : List E × E → VerifierProgram γ),
    (∀ p v, p.length = eqs.length → SimR (k (pre ++ p, v)) (K (p, v)) r) →
    SimR (eqs.foldlM (TM.sumcheckRound count) (pre, claim) >>= k) (sumcheck claim count eqs >>= K) r
  | [], pre, claim, k, K, h => by
    have h0 := h [] claim rfl
    rw [List.append_nil] at h0
    simp only [List.foldlM_nil, pure_bind]
    exact h0
  | e :: es, pre, claim, k, K, h => by
    simp only [List.foldlM_cons, TM.sumcheckRound, bind_assoc, pure_bind]
    rw [sumcheck]
    simp only [VerifierProgram.bind_assoc]
    refine SimR.bindEq (Sim.sumcheckRoundPoly count claim e) fun message ↦
      SimR.bindEq Sim.sample fun c ↦ ?_
    rw [polyEvalRust_eq]
    refine SimR.sumcheckLoop_bind count es (pre ++ [c]) _ k _ fun p v hp ↦ ?_
    have h1 := h (c :: p) v (by simp [hp])
    rw [List.append_assoc, List.singleton_append]
    exact h1

/-- **`sumcheck` runs `sumcheck`**, followed by `k`, whose point has a coordinate per round. -/
theorem SimR.sumcheck_bind {β γ : Type} (claim : E) (count : ℕ) (eqs : List (Option E))
    {k : List E × E → TM β} {K : List E × E → VerifierProgram γ} {r : β → γ → Prop}
    (h : ∀ p v, p.length = eqs.length → SimR (k (p, v)) (K (p, v)) r) :
    SimR (TM.sumcheck claim count eqs >>= k) (sumcheck claim count eqs >>= K) r :=
  SimR.sumcheckLoop_bind count eqs [] claim k K h

theorem Sim.sumcheck (claim : E) (count : ℕ) (equalities : List (Option E)) :
    Sim (TM.sumcheck claim count equalities) (sumcheck claim count equalities) := by
  have := SimR.sumcheck_bind claim count equalities (k := fun x ↦ Pure.pure x)
    (K := VerifierProgram.ret) (r := (· = ·)) fun p v _ ↦ Sim.pure (p, v)
  rw [bind_pure, VerifierProgram.bind_ret] at this
  exact this

theorem Returns.sumcheckLoop (count : ℕ) : ∀ (equalities : List (Option E)) (point : List E)
    (claim : E), Returns (equalities.foldlM (TM.sumcheckRound count) (point, claim))
      fun r ↦ r.1.length = point.length + equalities.length
  | [], point, claim => Returns.pure rfl
  | _ :: equalities, point, _ => by
    simp only [List.foldlM_cons, TM.sumcheckRound, bind_assoc, pure_bind]
    refine Returns.bindAll fun _ ↦ Returns.bindAll fun _ ↦ ?_
    refine fun t a t' h ↦ (Returns.sumcheckLoop count equalities _ _ t a t' h).trans ?_
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem Returns.sumcheck (claim : E) (count : ℕ) (equalities : List (Option E)) :
    Returns (TM.sumcheck claim count equalities) fun r ↦ r.1.length = equalities.length := by
  intro t a t' h
  have := Returns.sumcheckLoop count equalities [] claim t a t' h
  simpa using this

end Rv64Verifier.Model
