module

public import NativeVm.Model.Transcript

/-!
# The model against the statement: the correspondence and the simulation judgement

The model (`NativeVm.Model`) threads a `TState` through `VM = StateT TState Option`; the statement
runs a `VerifierProgram` on a `VerifierProgramState` (`LeanVM.Protocol.Compile.run`, over
Keccak-f[1600] in `Id`). `TState.Rel t s` says the two states agree:

* the sponges' states are equal, their waiting scalars equal under `EW.toE` (tags as numbers), their
  ground challenges equal under `EW.toE` (`SpongeW.Rel`);
* the stream from the cursor is the statement's stream under `EW.toE`, the cursor within the stream;
* the openings from the phase cursor are the statement's under `OpeningW.toOpening`, the phase
  cursor within them;
* the roots read are equal (`RootW.toRoot`).

`Sim m p R` (`m` simulates `p`, the results related by `R`): from related states, both reject, or
both return, with related results and related states. A phase is proved by composing the
simulations of its steps: `Sim.bind`, `Sim.pure`, `Sim.reject`, `Sim.liftOpt`, `Sim.require`,
`Sim.mono`, and the loop `Sim.foldlM` (a list fold on both sides). The verifier language is given a
`LawfulMonad` instance here, so the monad laws normalize programs on both sides.
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

/-! ## The correspondence of states -/

/-- The opening a decoded one denotes: its position as a number, its leaf's words as `K`. -/
def _root_.NativeVm.Model.OpeningW.toOpening (o : OpeningW) : Opening :=
  ⟨o.leafIndex.toNat, o.leaf.toList.map K.ofLane, o.path.toList⟩

/-- A phase of openings as the statement holds it. -/
def phaseOpenings (phase : Array OpeningW) : List Opening := phase.toList.map OpeningW.toOpening

/-- A root as the statement holds it: digest, height, width. -/
def _root_.NativeVm.Model.RootW.toRoot (r : RootW) : Digest × ℕ × ℕ := (r.digest, r.height, r.width)

/-- The waiting scalars as the statement holds them. -/
def pendingE (pending : Array (EW × UInt64)) : List (E × ℕ) :=
  pending.toList.map fun p ↦ (p.1.toE, p.2.toNat)

/-- The model's sponge is the statement's. -/
structure _root_.NativeVm.Model.SpongeW.Rel (w : SpongeW) (s : Sponge) : Prop where
  state : w.state = s.state
  pending : pendingE w.pending = s.pending
  ground : w.ground.map EW.toE = s.ground

/-- **The correspondence of states**: the sponges agree, the stream from the cursor and the
openings from the phase cursor are the statement's, the cursors within bounds, the roots equal. -/
structure _root_.NativeVm.Model.TState.Rel (t : TState) (s : VerifierProgramState) : Prop where
  sponge : t.sponge.Rel s.sponge
  cursor_le : t.cursor ≤ t.stream.size
  stream : (t.stream.toList.drop t.cursor).map EW.toE = s.stream
  phase_le : t.phase ≤ t.openings.size
  openings : (t.openings.toList.drop t.phase).map phaseOpenings = s.openings
  roots : t.roots.toList.map RootW.toRoot = s.roots

/-! ## The simulation judgement -/

/-- The statement's run over Keccak-f[1600]. -/
def runSpec {β : Type} (p : VerifierProgram β) (s : VerifierProgramState) :
    Option (β × VerifierProgramState) :=
  Id.run (run (m := Id) keccakF1600 p s)

/-- **`m` simulates `p`**: from related states both reject, or both return related results in
related states. -/
def Sim {α β : Type} (m : VM α) (p : VerifierProgram β) (R : α → β → Prop) : Prop :=
  ∀ t s, TState.Rel t s →
    Option.Rel (fun (x : α × TState) (y : β × VerifierProgramState) ↦ R x.1 y.1 ∧ TState.Rel x.2 y.2)
      (m.run t) (runSpec p s)

/-! ## The statement's run -/

namespace VerifierProgram

variable {α β γ : Type}

theorem bind_eq (p : VerifierProgram α) (f : α → VerifierProgram β) : p >>= f = p.bind f := rfl

theorem pure_eq (a : α) : (pure a : VerifierProgram α) = .ret a := rfl

theorem bind_assoc' (p : VerifierProgram α) (f : α → VerifierProgram β)
    (g : β → VerifierProgram γ) : (p.bind f).bind g = p.bind fun x ↦ (f x).bind g := by
  induction p with
  | ret a => rfl
  | fail => rfl
  | read k ih => exact congrArg VerifierProgram.read (funext ih)
  | sample k ih => exact congrArg VerifierProgram.sample (funext ih)
  | grind b k ih => exact congrArg (VerifierProgram.grind b) ih
  | commit h w k ih => exact congrArg (VerifierProgram.commit h w) ih
  | query i ps k ih => exact congrArg (VerifierProgram.query i ps) (funext ih)

theorem bind_ret (p : VerifierProgram α) : p.bind .ret = p := by
  induction p with
  | ret a => rfl
  | fail => rfl
  | read k ih => exact congrArg VerifierProgram.read (funext ih)
  | sample k ih => exact congrArg VerifierProgram.sample (funext ih)
  | grind b k ih => exact congrArg (VerifierProgram.grind b) ih
  | commit h w k ih => exact congrArg (VerifierProgram.commit h w) ih
  | query i ps k ih => exact congrArg (VerifierProgram.query i ps) (funext ih)

/-- The verifier language is a lawful monad, so the monad laws normalize its programs. -/
instance : LawfulMonad VerifierProgram := LawfulMonad.mk'
  (id_map := bind_ret) (pure_bind := fun _ _ ↦ rfl) (bind_assoc := bind_assoc')

end VerifierProgram

@[simp] theorem runSpec_ret {β : Type} (b : β) (s : VerifierProgramState) :
    runSpec (.ret b) s = some (b, s) := rfl

@[simp] theorem runSpec_pure {β : Type} (b : β) (s : VerifierProgramState) :
    runSpec (pure b) s = some (b, s) := rfl

@[simp] theorem runSpec_fail {β : Type} (s : VerifierProgramState) :
    runSpec (.fail : VerifierProgram β) s = none := rfl

/-- The run of a sequence is the runs in turn. -/
theorem runSpec_bind {α β : Type} (p : VerifierProgram α) (f : α → VerifierProgram β)
    (s : VerifierProgramState) :
    runSpec (p >>= f) s = (runSpec p s).bind fun y ↦ runSpec (f y.1) y.2 := by
  rw [VerifierProgram.bind_eq]
  induction p generalizing s with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    rcases s with ⟨⟨st, pend, _ | c⟩, _ | ⟨x, xs⟩, os, rs⟩
    · rfl
    · exact ih x _
    · rfl
    · rfl
  | sample k ih => exact ih _ _
  | grind b k ih =>
    rcases s with ⟨⟨st, pend, _ | c⟩, _ | ⟨x, xs⟩, os, rs⟩
    · rfl
    · simp only [VerifierProgram.bind, runSpec, Compile.run, Id.run_bind]
      split
      · exact ih _
      · rfl
    · rfl
    · rfl
  | commit h w k ih =>
    rcases s with ⟨⟨st, pend, _ | c⟩, _ | ⟨x0, _ | ⟨x1, xs⟩⟩, os, rs⟩ <;> first | rfl | exact ih _
  | query i ps k ih =>
    rcases s with ⟨sp, st, _ | ⟨ph, rest⟩, rs⟩ <;> rcases hr : rs[i]? with _ | ⟨root, height, width⟩
    all_goals simp only [VerifierProgram.bind, runSpec, Compile.run, hr]
    all_goals try rfl
    generalize openPhase (m := Id) keccakF1600 root height width ps ph = o
    rcases o with _ | rows
    · rfl
    · exact ih rows _

/-! ## Composition -/

namespace Sim

variable {α β γ δ : Type}

theorem mono {m : VM α} {p : VerifierProgram β} {R R' : α → β → Prop} (h : Sim m p R)
    (hR : ∀ a b, R a b → R' a b) : Sim m p R' := by
  intro t s hts
  have := h t s hts
  revert this
  generalize m.run t = x
  generalize runSpec p s = y
  rintro (⟨⟨h1, h2⟩⟩ | _)
  · exact .some ⟨hR _ _ h1, h2⟩
  · exact .none

theorem pure {a : α} {b : β} {R : α → β → Prop} (h : R a b) :
    Sim (Pure.pure a : VM α) (Pure.pure b : VerifierProgram β) R :=
  fun _ _ hts ↦ .some ⟨h, hts⟩

theorem ret {a : α} {b : β} {R : α → β → Prop} (h : R a b) :
    Sim (Pure.pure a : VM α) (.ret b : VerifierProgram β) R :=
  pure h

theorem reject {R : α → β → Prop} : Sim (Model.reject : VM α) (.fail : VerifierProgram β) R :=
  fun _ _ _ ↦ .none

theorem bind {m : VM α} {p : VerifierProgram β} {f : α → VM γ} {g : β → VerifierProgram δ}
    {R : α → β → Prop} {S : γ → δ → Prop} (hm : Sim m p R)
    (hf : ∀ a b, R a b → Sim (f a) (g b) S) : Sim (m >>= f) (p >>= g) S := by
  intro t s hts
  rw [runSpec_bind, StateT.run_bind]
  have := hm t s hts
  revert this
  generalize m.run t = x
  generalize runSpec p s = y
  rintro (⟨⟨h1, h2⟩⟩ | _)
  · exact hf _ _ h1 _ _ h2
  · exact .none

theorem liftOpt {o : Option α} {o' : Option β} {R : α → β → Prop} (h : Option.Rel R o o') :
    Sim (Model.liftOpt o) (Verifier.liftOption o') R := by
  rcases h with h | _
  · exact fun _ _ hts ↦ .some ⟨h, hts⟩
  · exact reject

theorem require {c : Bool} {c' : Prop} [Decidable c'] (h : c = true ↔ c') :
    Sim (Model.require c) (VerifierProgram.require c') fun _ _ ↦ True := by
  unfold Model.require VerifierProgram.require
  split <;> split
  · exact ret trivial
  · rename_i h1 h2; exact absurd (h.1 h1) h2
  · rename_i h1 h2; exact absurd (h.2 h2) h1
  · exact reject

/-- A fold on both sides over related lists, the accumulators related. -/
theorem foldlM {Q : γ → δ → Prop} {R : α → β → Prop} {f : α → γ → VM α}
    {g : β → δ → VerifierProgram β} (hstep : ∀ a b x y, R a b → Q x y → Sim (f a x) (g b y) R) :
    ∀ {l : List γ} {l' : List δ}, List.Forall₂ Q l l' → ∀ {a b}, R a b →
      Sim (l.foldlM f a) (l'.foldlM g b) R
  | [], [], .nil, _, _, h => pure h
  | _ :: _, _ :: _, .cons hxy hl, _, _, h => by
    simp only [List.foldlM_cons]
    exact bind (hstep _ _ _ _ h hxy) fun _ _ h' ↦ foldlM hstep hl h'

end Sim

end NativeVm.Equiv
