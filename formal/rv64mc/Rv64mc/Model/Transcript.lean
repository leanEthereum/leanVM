module

public import Rv64mc.Model.Sponge
public import Rv64mc.Model.Multilinear

/-!
# `transcript.rs`'s `Transcript`, and how it runs the statement's programs

`crates/verifier/src/transcript.rs`'s `Transcript` holds the proof, the sponge (`SpongeRust`,
`Model.Sponge`), how many scalars and phases of openings it has read, and whether it checks.
`TState` is that, plus the roots the statement's `VerifierProgramState` keeps (a ghost: the Rust
passes each root to `merkle` itself). The proof is the statement's `Proof`: the Rust's stream is
its scalars' limbs, and a Rust `MerklePath` is `MerklePathRust.ofOpening` of an opening. A Rust
function that takes `&mut Transcript` and returns a `Result` is mirrored in `TM`, the state monad
over `TState`. Where the Rust panics a mirror may return anything; it fails (`none`) only where the
Rust fails, an `Err` or a panic the verifier relies on (`Sponge::absorb`'s assert).

`SimR m P r` says the mirror `m` runs the statement's program fragment `P` up to `r`: from a state
keeping `TState.Inv` (the sponge's shape, the offsets within the proof, checked mode, every leaf
index a `u64`), whenever `m` returns `a`, the statement's `run` of `P` over Keccak-f[1600] from the
state `TState.toSpec` stands for returns some `b` with `r a b`, in the state the final transcript
stands for, which keeps the invariant. It is the soundness direction (an `Err` rejects anyway),
and it composes through `bind` (`SimR.bind`). `Sim` is `SimR` with equality; `Returns m R` says
what `m` returns satisfies `R`.

The methods: `next_scalar`, `sample`, `next_scalars`, `samples`, `grind_check` (with
`grinding_bits`), `merkle`, `sumcheck_round_poly`, `sumcheck` and `finish`, each with its
simulation (`merkle` from a root the statement read, `merkle_run`), and a root's read as the
verifier makes it (`next_scalars(2)` and `Digest::from_halves`, `TM.commit`). Since a
simulation holds of a mirror that always fails, each method also has a success lemma (the mirror
succeeds when the Rust's checks pass, `nextScalar_succeeds` and the others, at the end).

The monad `TM`, `SimR`, `Sim`, `SimUnit`, `Returns` and their combinators are the API the other
modules' mirrors (the Keccak GKR, WHIR, the layout, the bus, the walk) are written on, whether or
not this module uses them.
-/

namespace Rv64mc.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

attribute [local irreducible] keccakF1600 keccakFRust

/-! ## The transcript and the statement's state -/

/-- The Rust `Transcript`, with the roots read so far as a ghost. -/
structure TState where
  /-- `proof`. -/
  proof : Proof
  /-- `sponge`. -/
  sponge : SpongeRust
  /-- `stream_offset`. -/
  streamOffset : ℕ
  /-- `opening_offset`. -/
  openingOffset : ℕ
  /-- `checked`. -/
  checked : Bool
  /-- The roots read so far, each with its tree's height and width (ghost). -/
  roots : List (Digest × ℕ × ℕ)

/-- What every transcript of the verifier keeps: the sponge's shape, the offsets within the
proof, checked mode, and leaf indices that are `u64`s. -/
def TState.Inv (t : TState) : Prop :=
  t.sponge.Inv ∧ t.streamOffset ≤ t.proof.stream.length ∧
    t.openingOffset ≤ t.proof.openings.length ∧ t.checked = true ∧
    ∀ phase ∈ t.proof.openings, ∀ o ∈ phase, o.leafIndex < 2 ^ 64

/-- The statement's state a transcript stands for. -/
def TState.toSpec (t : TState) : VerifierProgramState :=
  ⟨t.sponge.toSpec, t.proof.stream.drop t.streamOffset, t.proof.openings.drop t.openingOffset,
    t.roots⟩

/-- The Rust transcript's methods: `none` is any `Err` or panic. -/
abbrev TM := StateT TState Option

/-- The statement's run over Keccak-f[1600]. -/
def runK {α : Type} (P : VerifierProgram α) (σ : VerifierProgramState) :
    Option (α × VerifierProgramState) :=
  Id.run (run (m := Id) keccakF1600 P σ)

/-- The roots a transcript has read (its ghost). -/
abbrev Roots : Type := List (Digest × ℕ × ℕ)

/-- `m` runs `P`, its value related to `P`'s by `r`, from the transcripts whose ghost roots
satisfy `pre` (a fragment that opens a root it holds: `verify_whir`). -/
def SimRoots {α β : Type} (pre : Roots → Prop) (m : TM α) (P : VerifierProgram β)
    (r : α → β → Prop) : Prop :=
  ∀ t a t', t.Inv → pre t.roots → m.run t = some (a, t') →
    t'.Inv ∧ ∃ b, runK P t.toSpec = some (b, t'.toSpec) ∧ r a b

/-- `m` runs `P`, its value related to `P`'s by `r`: `SimRoots` from every transcript
(`SimR.iff_roots`), its combinators derived from `SimRoots`'. -/
def SimR {α β : Type} (m : TM α) (P : VerifierProgram β) (r : α → β → Prop) : Prop :=
  ∀ t a t', t.Inv → m.run t = some (a, t') →
    t'.Inv ∧ ∃ b, runK P t.toSpec = some (b, t'.toSpec) ∧ r a b

theorem SimR.iff_roots {α β : Type} {m : TM α} {P : VerifierProgram β} {r : α → β → Prop} :
    SimR m P r ↔ SimRoots (fun _ ↦ True) m P r :=
  ⟨fun h t a t' hi _ hm ↦ h t a t' hi hm, fun h t a t' hi hm ↦ h t a t' hi trivial hm⟩

/-- `m` runs `P`, returning the same value. -/
def Sim {α : Type} (m : TM α) (P : VerifierProgram α) : Prop := SimR m P (· = ·)

theorem Sim.intro {α : Type} {m : TM α} {P : VerifierProgram α}
    (h : ∀ t a t', t.Inv → m.run t = some (a, t') →
      t'.Inv ∧ runK P t.toSpec = some (a, t'.toSpec)) : Sim m P :=
  fun t a t' hi hm ↦ ⟨(h t a t' hi hm).1, a, (h t a t' hi hm).2, rfl⟩

/-! ## The statement's run, sequenced -/

theorem runK_bind {α β : Type} (P : VerifierProgram α) (Q : α → VerifierProgram β)
    (σ : VerifierProgramState) :
    runK (P >>= Q) σ = match runK P σ with
      | some (a, σ') => runK (Q a) σ'
      | none => none := by
  show runK (P.bind Q) σ = _
  induction P generalizing σ <;>
    simp only [VerifierProgram.bind, runK, Compile.run, Id.run, bind, pure] at * <;>
    split <;> split <;> (try split_ifs) <;> simp_all

theorem VerifierProgram.bind_assoc' {α β γ : Type} (P : VerifierProgram α)
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

theorem VerifierProgram.bind_ret' {α : Type} (P : VerifierProgram α) :
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

/-! ## Composing simulations -/

theorem SimRoots.mono {α β : Type} {pre : Roots → Prop} {m : TM α} {P : VerifierProgram β}
    {r r' : α → β → Prop} (h : SimRoots pre m P r) (hr : ∀ a b, r a b → r' a b) :
    SimRoots pre m P r' := by
  intro t a t' hi hp hm
  obtain ⟨hi', b, hb, hab⟩ := h t a t' hi hp hm
  exact ⟨hi', b, hb, hr a b hab⟩

theorem SimR.mono {α β : Type} {m : TM α} {P : VerifierProgram β} {r r' : α → β → Prop}
    (h : SimR m P r) (hr : ∀ a b, r a b → r' a b) : SimR m P r' :=
  SimR.iff_roots.2 (SimRoots.mono (SimR.iff_roots.1 h) hr)

theorem SimRoots.weaken {α β : Type} {pre pre' : Roots → Prop} {m : TM α} {P : VerifierProgram β}
    {r : α → β → Prop} (hp : ∀ roots, pre roots → pre' roots) (h : SimRoots pre' m P r) :
    SimRoots pre m P r :=
  fun t a t' hi hpr hm ↦ h t a t' hi (hp _ hpr) hm

/-- A simulation from every transcript holds from any. -/
theorem SimRoots.of {α β : Type} {pre : Roots → Prop} {m : TM α} {P : VerifierProgram β}
    {r : α → β → Prop} (h : SimR m P r) : SimRoots pre m P r :=
  SimRoots.weaken (fun _ _ ↦ trivial) (SimR.iff_roots.1 h)

theorem SimRoots.pure {α β : Type} {pre : Roots → Prop} {r : α → β → Prop} {a : α} {b : β}
    (h : r a b) : SimRoots pre (Pure.pure a : TM α) (VerifierProgram.ret b) r := by
  intro t a' t' hi _ hm
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  exact ⟨hi, b, rfl, h⟩

theorem SimR.pure {α β : Type} {r : α → β → Prop} {a : α} {b : β} (h : r a b) :
    SimR (Pure.pure a : TM α) (VerifierProgram.ret b) r :=
  SimR.iff_roots.2 (SimRoots.pure h)

/-- Sequencing, the continuation run from the roots `mid` the first step leaves. -/
theorem SimRoots.bind {α β γ δ : Type} {pre mid : Roots → Prop} {m : TM α}
    {P : VerifierProgram β} {r : α → β → Prop} {k : α → TM γ} {Q : β → VerifierProgram δ}
    {r' : γ → δ → Prop} (hm : SimRoots pre m P r)
    (hmid : ∀ t a t', t.Inv → pre t.roots → m.run t = some (a, t') → mid t'.roots)
    (hk : ∀ a b, r a b → SimRoots mid (k a) (Q b) r') : SimRoots pre (m >>= k) (P >>= Q) r' := by
  intro t c t' hi hp h
  rw [StateT.run_bind] at h
  cases hmt : m.run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨a, t₁⟩ := p
    rw [hmt] at h
    obtain ⟨hi₁, b, hb, hab⟩ := hm t a t₁ hi hp hmt
    rw [runK_bind, hb]
    exact hk a b hab t₁ c t' hi₁ (hmid t a t₁ hi hp hmt) h

theorem SimR.bind {α β γ δ : Type} {m : TM α} {P : VerifierProgram β} {r : α → β → Prop}
    {k : α → TM γ} {Q : β → VerifierProgram δ} {r' : γ → δ → Prop} (hm : SimR m P r)
    (hk : ∀ a b, r a b → SimR (k a) (Q b) r') : SimR (m >>= k) (P >>= Q) r' :=
  SimR.iff_roots.2 (SimRoots.bind (SimR.iff_roots.1 hm) (fun _ _ _ _ _ _ ↦ trivial)
    fun a b h ↦ SimR.iff_roots.1 (hk a b h))

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

/-- `m` runs `P`, whose value the Rust does not use (a commitment: the Rust keeps the root it
read, the statement its index in the roots). -/
def SimUnit {α : Type} (m : TM α) (P : VerifierProgram Unit) : Prop := SimR m P fun _ _ ↦ True

theorem SimR.bindUnit {α γ δ : Type} {m : TM α} {P : VerifierProgram Unit} {k : α → TM γ}
    {Q : VerifierProgram δ} {r' : γ → δ → Prop} (hm : SimUnit m P) (hk : ∀ a, SimR (k a) Q r') :
    SimR (m >>= k) (P >>= fun _ ↦ Q) r' :=
  SimR.bind hm fun a _ _ ↦ hk a

/-! ## What a mirror returns -/

/-- What a mirror returns satisfies `R`. -/
def Returns {α : Type} (m : TM α) (R : α → Prop) : Prop :=
  ∀ t a t', m.run t = some (a, t') → R a

theorem Returns.pure {α : Type} {R : α → Prop} {a : α} (h : R a) :
    Returns (Pure.pure a : TM α) R := by
  intro t b t' hr
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, -⟩ := hr
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
  intro t a t' hi hm
  obtain ⟨hi', b, hb, hab⟩ := h t a t' hi hm
  exact ⟨hi', b, hb, hab, hR t a t' hm⟩

theorem SimR.bindPost {α γ δ : Type} {m : TM α} {P : VerifierProgram α} {k : α → TM γ}
    {Q : α → VerifierProgram δ} {r : γ → δ → Prop} {R : α → Prop} (hm : Sim m P)
    (hR : Returns m R) (hk : ∀ a, R a → SimR (k a) (Q a) r) : SimR (m >>= k) (P >>= Q) r :=
  SimR.bind (SimR.and_returns hm hR) fun a _ h ↦ by obtain ⟨rfl, hRa⟩ := h; exact hk a hRa

/-! ## Failures and checks -/

namespace TM

/-- A Rust failure (`Err` or panic). -/
def fail {α : Type} : TM α := fun _ ↦ none

/-- `?` on a pure `Option`: an `Err` or a panic of a pure step. -/
def ofOption {α : Type} : Option α → TM α
  | some a => Pure.pure a
  | none => TM.fail

/-- `require(c, _)?`. -/
def require (c : Prop) [Decidable c] : TM Unit := fun t ↦ if c then some ((), t) else none

/-- `Transcript::checked`. -/
def checked : TM Bool := fun t ↦ some (t.checked, t)

/-- `Transcript::stream_offset`. -/
def streamPosition : TM ℕ := fun t ↦ some (t.streamOffset, t)

end TM

theorem Sim.require (c : Prop) [Decidable c] :
    Sim (TM.require c) (VerifierProgram.require c) := by
  refine Sim.intro fun t a t' hi h ↦ ?_
  simp only [TM.require, StateT.run] at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  refine ⟨hi, ?_⟩
  simp only [VerifierProgram.require, hc, ↓reduceIte]
  rfl

/-- A check of the Rust's that the statement leaves out: the rest runs `Q` when it holds. -/
theorem SimR.require_left {γ δ : Type} {c : Prop} [Decidable c] {k : Unit → TM γ}
    {Q : VerifierProgram δ} {r : γ → δ → Prop} (hk : c → SimR (k ()) Q r) :
    SimR (TM.require c >>= k) Q r := by
  intro t a t' hi h
  rw [StateT.run_bind] at h
  simp only [TM.require, StateT.run] at h
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    exact hk hc t a t' hi h
  · rw [ite_eq_right hc] at h
    cases h

/-- A read of the stream's position, which the statement does not make. -/
theorem SimR.streamPosition_left {γ δ : Type} {k : ℕ → TM γ} {Q : VerifierProgram δ}
    {r : γ → δ → Prop} (hk : ∀ n, SimR (k n) Q r) : SimR (TM.streamPosition >>= k) Q r := by
  intro t a t' hi h
  rw [StateT.run_bind] at h
  exact hk t.streamOffset t a t' hi h

/-! ## Checks, `Option` steps and roots, for the mirrors' simulations -/

/-- `E * K` (`impl Mul<K> for E`): both limbs by `base_mul`. -/
def mulKE (x : E) (k : K) : E := ofLimbsW (eMulK (limbs x) k.toBitVec)

theorem mulKE_eq (x : E) (k : K) : mulKE x k = x * ofK k := by
  rw [mulKE, eMulK_eq, ofLimbsW_limbs]

/-- `if transcript.checked() { body }`. -/
def TM.whenChecked (body : TM Unit) : TM Unit := do
  if ← TM.checked then body else Pure.pure ()

/-- A `checked()` test the Rust makes and the statement does not: the checked branch, the mode
of every simulated transcript. -/
theorem SimRoots.checked_bind {γ δ : Type} {pre : Roots → Prop} {k : Bool → TM γ}
    {Q : VerifierProgram δ} {r : γ → δ → Prop} (h : SimRoots pre (k true) Q r) :
    SimRoots pre (TM.checked >>= k) Q r := by
  intro t a t' hi hp hm
  have e : (TM.checked >>= k).run t = (k t.checked).run t := rfl
  rw [e, hi.2.2.2.1] at hm
  exact h t a t' hi hp hm

theorem SimR.checked_bind {γ δ : Type} {k : Bool → TM γ} {Q : VerifierProgram δ}
    {r : γ → δ → Prop} (h : SimR (k true) Q r) : SimR (TM.checked >>= k) Q r :=
  SimR.iff_roots.2 (SimRoots.checked_bind (SimR.iff_roots.1 h))

/-- **A `checked()` branch runs its body.** -/
theorem SimRoots.whenChecked_bind {γ δ : Type} {pre : Roots → Prop} {body : TM Unit}
    {k : Unit → TM γ} {Q : VerifierProgram δ} {r : γ → δ → Prop}
    (h : SimRoots pre (body >>= k) Q r) : SimRoots pre (TM.whenChecked body >>= k) Q r := by
  have e : TM.whenChecked body >>= k =
      TM.checked >>= fun c ↦ (if c then body else Pure.pure ()) >>= k := by
    simp only [TM.whenChecked, bind_assoc]
  rw [e]
  exact SimRoots.checked_bind h

theorem SimR.whenChecked_bind {γ δ : Type} {body : TM Unit} {k : Unit → TM γ}
    {Q : VerifierProgram δ} {r : γ → δ → Prop} (h : SimR (body >>= k) Q r) :
    SimR (TM.whenChecked body >>= k) Q r :=
  SimR.iff_roots.2 (SimRoots.whenChecked_bind (SimR.iff_roots.1 h))

/-- A pure `Option` step of the Rust (`?` or a panic) that the statement does not make. -/
theorem SimRoots.ofOption_bind {α γ δ : Type} {pre : Roots → Prop} {o : Option α}
    {k : α → TM γ} {Q : VerifierProgram δ} {r : γ → δ → Prop}
    (h : ∀ a, o = some a → SimRoots pre (k a) Q r) : SimRoots pre (TM.ofOption o >>= k) Q r := by
  cases o with
  | none =>
    intro t a t' _ _ hm
    have e : (TM.ofOption (none : Option α) >>= k).run t = none := rfl
    rw [e] at hm
    cases hm
  | some a =>
    have := h a rfl
    simpa only [TM.ofOption, pure_bind] using this

theorem SimR.ofOption_bind {α γ δ : Type} {o : Option α} {k : α → TM γ} {Q : VerifierProgram δ}
    {r : γ → δ → Prop} (h : ∀ a, o = some a → SimR (k a) Q r) : SimR (TM.ofOption o >>= k) Q r :=
  SimR.iff_roots.2 (SimRoots.ofOption_bind fun a ha ↦ SimR.iff_roots.1 (h a ha))

/-- `require` of a condition equivalent to the statement's. -/
theorem Sim.require_iff {c c' : Prop} [Decidable c] [Decidable c'] (h : c ↔ c') :
    Sim (TM.require c) (VerifierProgram.require c') := by
  have : TM.require c = TM.require c' := by
    funext t
    by_cases hc : c
    · simp [TM.require, hc, h.mp hc]
    · simp [TM.require, hc, mt h.mpr hc]
  rw [this]
  exact Sim.require c'

/-- A check the statement makes, which holds. -/
theorem SimRoots.require_right {γ δ : Type} {pre : Roots → Prop} {c : Prop} [Decidable c]
    (hc : c) {m : TM γ} {K : Unit → VerifierProgram δ} {r : γ → δ → Prop}
    (h : SimRoots pre m (K ()) r) : SimRoots pre m (VerifierProgram.require c >>= K) r := by
  have e : (VerifierProgram.require c >>= K) = K () := by
    simp only [VerifierProgram.require, ite_eq_left hc]; rfl
  rw [e]
  exact h

theorem SimRoots.fail {α β : Type} {pre : Roots → Prop} {P : VerifierProgram β}
    {r : α → β → Prop} : SimRoots pre (TM.fail : TM α) P r := by
  intro t a t' _ _ h
  cases h

/-- `mapM` of a function that returns `g` on every element. -/
theorem mapM_eq_some_map {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (l : List α), (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x (by simp), mapM_eq_some_map f g l fun y hy ↦ h y (by simp [hy])]
    rfl

/-- `P` reads no commitment. -/
def NoCommit {α : Type} : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoCommit (k x)
  | .sample k => ∀ x, NoCommit (k x)
  | .grind _ k => NoCommit k
  | .commit _ _ _ => False
  | .query _ _ k => ∀ rows, NoCommit (k rows)

theorem NoCommit.bind {α β : Type} {P : VerifierProgram α} {Q : α → VerifierProgram β}
    (hP : NoCommit P) (hQ : ∀ a, NoCommit (Q a)) : NoCommit (P >>= Q) := by
  show NoCommit (P.bind Q)
  induction P with
  | ret a => exact hQ a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hP x)
  | sample k ih => exact fun x ↦ ih x (hP x)
  | grind b k ih => exact ih hP
  | commit h w k ih => exact hP.elim
  | query i ps k ih => exact fun rows ↦ ih rows (hP rows)

theorem NoCommit.ret {α : Type} (a : α) : NoCommit (VerifierProgram.ret a) := trivial

theorem NoCommit.readScalar : NoCommit VerifierProgram.readScalar := fun _ ↦ trivial

theorem NoCommit.sampleChallenge : NoCommit VerifierProgram.sampleChallenge := fun _ ↦ trivial

theorem NoCommit.grindProofOfWork (bits : ℕ) :
    NoCommit (VerifierProgram.grindProofOfWork bits) := by
  unfold VerifierProgram.grindProofOfWork
  split <;> trivial

theorem NoCommit.require (c : Prop) [Decidable c] : NoCommit (VerifierProgram.require c) := by
  unfold VerifierProgram.require
  split <;> trivial

/-- A run of a program that reads no commitment keeps the roots. -/
theorem NoCommit.runK_roots {α : Type} {P : VerifierProgram α} (hP : NoCommit P) :
    ∀ {σ : VerifierProgramState} {b : α} {σ' : VerifierProgramState},
      runK P σ = some (b, σ') → σ'.roots = σ.roots := by
  induction P with
  | ret a =>
    intro σ b σ' h
    simp only [runK, Compile.run, Id.run, pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  | fail => intro σ b σ' h; cases h
  | read k ih =>
    intro σ b σ' h
    simp only [runK, Compile.run, Id.run] at h
    split at h
    · rename_i x xs _ _
      exact ih x (hP x)
        (σ := ⟨absorb (m := Id) keccakF1600 σ.sponge x dsObserve, xs, σ.openings, σ.roots⟩) h
    · cases h
  | sample k ih =>
    intro σ b σ' h
    simp only [runK, Compile.run, Id.run] at h
    exact ih _ (hP _)
      (σ := ⟨(squeeze (m := Id) keccakF1600 σ.sponge).2, σ.stream, σ.openings, σ.roots⟩) h
  | grind bits k ih =>
    intro σ b σ' h
    simp only [runK, Compile.run, Id.run] at h
    split at h
    · rename_i n xs _ _
      change (if powOk bits (absorbNonce (m := Id) keccakF1600 σ.sponge n).1 then
        Compile.run (m := Id) keccakF1600 k
          ⟨(absorbNonce (m := Id) keccakF1600 σ.sponge n).2, xs, σ.openings, σ.roots⟩
        else pure none : Id _) = _ at h
      split_ifs at h
      exact ih hP
        (σ := ⟨(absorbNonce (m := Id) keccakF1600 σ.sponge n).2, xs, σ.openings, σ.roots⟩) h
    · cases h
  | commit h w k ih => exact hP.elim
  | query i ps k ih =>
    intro σ b σ' h
    simp only [runK, Compile.run, Id.run] at h
    split at h
    · rename_i root height width phase rest _ _
      change (match (openPhase (m := Id) keccakF1600 root height width ps phase :
          Option (List (List K))) with
        | some rows => Compile.run (m := Id) keccakF1600 (k rows)
            ⟨σ.sponge, σ.stream, rest, σ.roots⟩
        | none => pure none : Id _) = _ at h
      split at h
      · exact ih _ (hP _) (σ := ⟨σ.sponge, σ.stream, rest, σ.roots⟩) h
      · cases h
    · cases h

theorem NoCommit.readScalars : ∀ n, NoCommit (VerifierProgram.readScalars n)
  | 0 => NoCommit.ret _
  | n + 1 => NoCommit.bind NoCommit.readScalar fun _ ↦
      NoCommit.bind (NoCommit.readScalars n) fun _ ↦ NoCommit.ret _

theorem NoCommit.sampleChallenges : ∀ n, NoCommit (VerifierProgram.sampleChallenges n)
  | 0 => NoCommit.ret _
  | n + 1 => NoCommit.bind NoCommit.sampleChallenge fun _ ↦
      NoCommit.bind (NoCommit.sampleChallenges n) fun _ ↦ NoCommit.ret _

/-- Close `NoCommit P` for a program built by `bind` from reads, samples, grinds, checks,
openings and sumchecks; `match`es on pairs are split. -/
macro "no_commit" : tactic => `(tactic| repeat' (first
  | exact NoCommit.ret _
  | exact NoCommit.readScalar
  | exact NoCommit.sampleChallenge
  | apply NoCommit.bind
  | exact NoCommit.readScalars _
  | exact NoCommit.sampleChallenges _
  | exact NoCommit.grindProofOfWork _
  | exact NoCommit.require _
  | intro _
  | split
  | trivial))

/-- `m` keeps the roots, from every transcript keeping `TState.Inv`. -/
def RootsKept {α : Type} (m : TM α) : Prop :=
  ∀ t a t', t.Inv → m.run t = some (a, t') → t'.roots = t.roots

/-- **A mirror of a program that reads no commitment keeps the roots.** -/
theorem RootsKept.ofSimR {α β : Type} {m : TM α} {P : VerifierProgram β} {r : α → β → Prop}
    (h : SimR m P r) (hP : NoCommit P) : RootsKept m := by
  intro t a t' hi hm
  obtain ⟨-, b, hb, -⟩ := h t a t' hi hm
  exact hP.runK_roots hb

theorem RootsKept.pure {α : Type} (a : α) : RootsKept (Pure.pure a : TM α) := by
  intro t b t' _ h
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]

/-- A simulated step that reads no commitment, then steps that keep the roots. -/
theorem RootsKept.bindSim {α β γ : Type} {m : TM α} {P : VerifierProgram β} {r : α → β → Prop}
    {k : α → TM γ} (hm : SimR m P r) (hP : NoCommit P) (hk : ∀ a, RootsKept (k a)) :
    RootsKept (m >>= k) := by
  intro t c t' hi h
  rw [StateT.run_bind] at h
  cases hmt : m.run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨a, t₁⟩ := p
    rw [hmt] at h
    exact (hk a t₁ c t' (hm t a t₁ hi hmt).1 h).trans (RootsKept.ofSimR hm hP t a t₁ hi hmt)

/-- A simulated step that reads no commitment, then the rest from the same roots. -/
theorem SimRoots.bindR {α β γ δ : Type} {pre : Roots → Prop} {m : TM α} {P : VerifierProgram β}
    {r : α → β → Prop} {k : α → TM γ} {Q : β → VerifierProgram δ} {r' : γ → δ → Prop}
    (hm : SimR m P r) (hP : NoCommit P) (hk : ∀ a b, r a b → SimRoots pre (k a) (Q b) r') :
    SimRoots pre (m >>= k) (P >>= Q) r' :=
  SimRoots.bind (SimRoots.of hm)
    (fun t a t' hi hp hmt ↦ by rw [RootsKept.ofSimR hm hP t a t' hi hmt]; exact hp) hk

theorem SimRoots.bindE {α γ δ : Type} {pre : Roots → Prop} {m : TM α} {P : VerifierProgram α}
    {k : α → TM γ} {Q : α → VerifierProgram δ} {r' : γ → δ → Prop} (hm : Sim m P)
    (hP : NoCommit P) (hk : ∀ a, SimRoots pre (k a) (Q a) r') :
    SimRoots pre (m >>= k) (P >>= Q) r' :=
  SimRoots.bindR hm hP fun a _ h ↦ by subst h; exact hk a

/-! ## Reading and sampling -/

private theorem drop_cons_of_getElem? {α : Type} {l : List α} {i : ℕ} {x : α} (h : l[i]? = some x) :
    l.drop i = x :: l.drop (i + 1) := by
  have hlt : i < l.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  rw [List.getElem?_eq_getElem hlt] at h
  rw [List.drop_eq_getElem_cons hlt, Option.some.inj h]

private theorem lt_of_getElem? {α : Type} {l : List α} {i : ℕ} {x : α} (h : l[i]? = some x) :
    i < l.length := by
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h

theorem absorb_some_ground {r r' : SpongeRust} {v : E} {t : BitVec 64}
    (h : r.absorb v t = some r') : r.ground = none := by
  cases hg : r.ground with
  | none => rfl
  | some c => rw [absorb_ground r (by simp [hg])] at h; cases h

/-- The sponge `absorb` returns is the statement's. -/
theorem absorb_some {r r' : SpongeRust} (hi : r.Inv) {v : E} {t : BitVec 64}
    (h : r.absorb v t = some r') :
    r'.Inv ∧ r'.toSpec = (absorb (m := Id) keccakF1600 r.toSpec v t.toNat : Sponge) := by
  obtain ⟨r'', h', hi', hs⟩ := absorb_toSpec r hi (absorb_some_ground h) v t
  rw [h] at h'
  cases h'
  exact ⟨hi', hs⟩

theorem toSpec_ground (r : SpongeRust) : r.toSpec.ground = r.ground := rfl

namespace TM

/-- `Transcript::next`: the next scalar of the stream, not absorbed. -/
def next : TM E := fun t ↦
  match t.proof.stream[t.streamOffset]? with
  | some x => some (x, { t with streamOffset := t.streamOffset + 1 })
  | none => none

/-- `Transcript::next_scalar`: `next`, then `Sponge::observe`. -/
def nextScalar : TM E := fun t ↦
  match t.proof.stream[t.streamOffset]? with
  | some x => (t.sponge.observe x).map fun s ↦
      (x, { t with streamOffset := t.streamOffset + 1, sponge := s })
  | none => none

/-- `Transcript::sample`. -/
def sample : TM E := fun t ↦ some (t.sponge.sample.1, { t with sponge := t.sponge.sample.2 })

/-- `Transcript::next_scalars(count)`: `(0..count).map(|_| self.next_scalar()).collect()`. -/
def nextScalars : ℕ → TM (List E)
  | 0 => Pure.pure []
  | n + 1 => do
    let x ← nextScalar
    let xs ← nextScalars n
    Pure.pure (x :: xs)

/-- `Transcript::samples(count)`. -/
def samples : ℕ → TM (List E)
  | 0 => Pure.pure []
  | n + 1 => do
    let x ← sample
    let xs ← samples n
    Pure.pure (x :: xs)

end TM

theorem Sim.nextScalar : Sim TM.nextScalar VerifierProgram.readScalar := by
  refine Sim.intro fun t a t' hi h ↦ ?_
  simp only [TM.nextScalar, StateT.run] at h
  split at h
  · rename_i x hx
    cases hs : t.sponge.observe x with
    | none => rw [hs] at h; cases h
    | some s =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hg := absorb_some_ground hs
      obtain ⟨hsi, hss⟩ := absorb_some hi.1 hs
      refine ⟨⟨hsi, by dsimp only; have := lt_of_getElem? hx; omega, hi.2.2⟩, ?_⟩
      simp only [VerifierProgram.readScalar, runK, TState.toSpec, Compile.run,
        drop_cons_of_getElem? hx, toSpec_ground, hg]
      rw [show dsObserve = dsObserveR.toNat from rfl, ← hss]
      rfl
  · cases h

theorem Sim.sample : Sim TM.sample VerifierProgram.sampleChallenge := by
  refine Sim.intro fun t a t' hi h ↦ ?_
  simp only [TM.sample, StateT.run, Option.some.injEq] at h
  obtain ⟨hs, hsi⟩ := sample_toSpec t.sponge hi.1
  cases h
  refine ⟨⟨hsi, hi.2⟩, ?_⟩
  simp only [VerifierProgram.sampleChallenge, runK, TState.toSpec, Compile.run, Id.run]
  rw [← hs]
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

/-! ## `grinding_bits` and `grind_check` -/

/-- `grinding_bits(numerator)`: `u128::BITS - (numerator - 1).leading_zeros()` (`0` for
`numerator <= 1`), less `128 - SECURITY_BITS`, saturating. -/
def grindingBitsRust (numerator : BitVec 128) : ℕ :=
  let log := if numerator ≤ 1#128 then 0 else 128 - (numerator - 1#128).clz.toNat
  log - (128 - 125)

/-- **`grinding_bits` is `grindingBits`.** -/
theorem grindingBitsRust_eq (numerator : BitVec 128) :
    grindingBitsRust numerator = grindingBits numerator.toNat := by
  rw [grindingBitsRust, grindingBits, securityBits]
  by_cases h : numerator ≤ 1#128
  · have h' : numerator.toNat ≤ 1 := by simpa [BitVec.le_def] using h
    rw [ite_eq_left h, ite_eq_left h']
  · have h' : ¬ numerator.toNat ≤ 1 := by simpa [BitVec.le_def] using h
    rw [ite_eq_right h, ite_eq_right h', sub_clz_eq_bitLength, bitLength]
    have hne : (numerator - 1#128).toNat ≠ 0 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
      simp
      omega
    rw [ite_eq_right hne, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
    simp

/-- The proof-of-work mask: `1u64.checked_shl(bits).map_or(u64::MAX, |bit| bit - 1)`. -/
def powMask (bits : ℕ) : BitVec 64 :=
  if bits < 64 then (1#64 <<< bits) - 1#64 else BitVec.allOnes 64

theorem powMask_iff (bits : ℕ) (pow : BitVec 64) :
    pow &&& powMask bits = 0#64 ↔ powOk bits (UInt64.ofBitVec pow) = true := by
  rw [powOk, decide_eq_true_iff, powMask]
  show _ ↔ pow.toNat % 2 ^ bits = 0
  split
  · rename_i hb
    have hlt : 2 ^ bits < 2 ^ 64 := Nat.pow_lt_pow_right (a := 2) (by norm_num) hb
    have h2 : (1#64 <<< bits).toNat = 2 ^ bits := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.one_mod_two_pow (by norm_num),
        Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt hlt]
    have hm : ((1#64 <<< bits) - 1#64).toNat = 2 ^ bits - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h2]; exact Nat.one_le_two_pow), h2]
      rfl
    rw [← BitVec.toNat_inj, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]
    exact Iff.rfl
  · rename_i hb
    rw [BitVec.and_allOnes]
    have hp : pow.toNat < 2 ^ bits :=
      lt_of_lt_of_le pow.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.mod_eq_of_lt hp]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq (by simpa using h)

namespace TM

/-- `Transcript::grind_check(bits)`: nothing for `0` bits; otherwise `next`, `absorb_nonce`, and
in checked mode `require(pow & mask == 0)`. -/
def grindCheck (bits : ℕ) : TM Unit := fun t ↦
  if bits = 0 then some ((), t)
  else
    match t.proof.stream[t.streamOffset]? with
    | some n =>
      match t.sponge.absorbNonce n with
      | some (pow, s) =>
        if !t.checked || pow &&& powMask bits = 0#64 then
          some ((), { t with streamOffset := t.streamOffset + 1, sponge := s })
        else none
      | none => none
    | none => none

end TM

theorem absorbNonce_some {r r' : SpongeRust} (hi : r.Inv) {n : E} {pow : BitVec 64}
    (h : r.absorbNonce n = some (pow, r')) :
    r.ground = none ∧ r'.Inv ∧
      (UInt64.ofBitVec pow, r'.toSpec) =
        (absorbNonce (m := Id) keccakF1600 r.toSpec n : UInt64 × Sponge) := by
  have hg : r.ground = none := by
    cases hg : r.ground with
    | none => rfl
    | some c =>
      simp [SpongeRust.absorbNonce, absorb_ground r (by simp [hg])] at h
  obtain ⟨pow', r'', h', hi', hs⟩ := absorbNonce_toSpec r hi hg n
  rw [h] at h'
  cases h'
  exact ⟨hg, hi', hs⟩

theorem Sim.grindCheck (bits : ℕ) :
    Sim (TM.grindCheck bits) (VerifierProgram.grindProofOfWork bits) := by
  refine Sim.intro fun t a t' hi h ↦ ?_
  simp only [TM.grindCheck, StateT.run] at h
  by_cases hb : bits = 0
  · rw [ite_eq_left hb] at h
    cases h
    refine ⟨hi, ?_⟩
    simp only [VerifierProgram.grindProofOfWork, hb, ↓reduceIte]
    rfl
  · rw [ite_eq_right hb] at h
    split at h
    · rename_i n hn
      split at h
      · rename_i pow s hs
        obtain ⟨hg, hsi, hss⟩ := absorbNonce_some hi.1 hs
        split_ifs at h with hm
        cases h
        have hm' : pow &&& powMask bits = 0#64 := by
          simpa [hi.2.2.2.1] using hm
        refine ⟨⟨hsi, by dsimp only; have := lt_of_getElem? hn; omega, hi.2.2⟩, ?_⟩
        simp only [VerifierProgram.grindProofOfWork, hb, ↓reduceIte, runK, TState.toSpec,
          Compile.run, drop_cons_of_getElem? hn, toSpec_ground, hg]
        rw [← hss]
        have hp : powOk bits (UInt64.ofBitVec pow) = true := (powMask_iff bits pow).mp hm'
        show (if powOk bits (UInt64.ofBitVec pow) = true then _ else _) = _
        rw [ite_eq_left hp]
        rfl
      · cases h
    · cases h

/-! ## A root's read -/

theorem Sim.run_eq' {α : Type} {m : TM α} {P : VerifierProgram α} (h : Sim m P) (t : TState)
    (a : α) (t' : TState) (hi : t.Inv) (hm : m.run t = some (a, t')) :
    t'.Inv ∧ runK P t.toSpec = some (a, t'.toSpec) := by
  obtain ⟨hi', b, hb, rfl⟩ := h t a t' hi hm
  exact ⟨hi', hb⟩

theorem nextScalar_some {t t' : TState} {x : E} (h : TM.nextScalar.run t = some (x, t')) :
    ∃ s, t.proof.stream[t.streamOffset]? = some x ∧ t.sponge.observe x = some s ∧
      t' = { t with streamOffset := t.streamOffset + 1, sponge := s } := by
  simp only [TM.nextScalar, StateT.run] at h
  split at h
  · rename_i y hy
    cases hs : t.sponge.observe y with
    | none => rw [hs] at h; cases h
    | some s =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨s, hy, hs, rfl⟩
  · cases h

private theorem runK_readCommitment_of (height width : ℕ) (σ : VerifierProgramState) {x0 x1 : E}
    {xs : List E} (hs : σ.stream = x0 :: x1 :: xs) (hg : σ.sponge.ground = none) :
    runK (VerifierProgram.readCommitment height width) σ = some ((), { σ with
      sponge := (absorb (m := Id) keccakF1600
        (absorb (m := Id) keccakF1600 σ.sponge x0 dsObserve) x1 dsObserve : Sponge),
      stream := xs, roots := σ.roots ++ [(digestFromHalves (x0, x1), height, width)] }) := by
  unfold runK VerifierProgram.readCommitment
  rw [Compile.run]
  simp only [hs, hg]
  rfl

namespace TM

/-- Keep a root the statement reads (ghost: the Rust keeps it in a local). -/
def ghostRoot (root : Digest) (height width : ℕ) : TM Unit := fun t ↦
  some ((), { t with roots := t.roots ++ [(root, height, width)] })

/-- A root's read, as `lib.rs` and `whir.rs` make it: `next_scalars(2)`, then
`Digest::from_halves(halves[0], halves[1])`; the root is kept as a ghost with its tree's shape. -/
def commit (height width : ℕ) : TM (List (BitVec 8)) := do
  let halves ← nextScalars 2
  ghostRoot (digestFromHalves (halves.getD 0 0, halves.getD 1 0)) height width
  Pure.pure (digestFromHalvesRust (limbs (halves.getD 0 0)) (limbs (halves.getD 1 0)))

end TM

/-- **A root's read runs `readCommitment`**, the root the bytes of the one the statement keeps. -/
theorem SimR.commit (height width : ℕ) :
    SimR (TM.commit height width) (VerifierProgram.readCommitment height width) fun root _ ↦
      ∃ x0 x1, root = digestBits (digestFromHalves (x0, x1)) := by
  intro t a t' hi h
  simp only [TM.commit, TM.nextScalars, StateT.run_bind, bind_assoc, pure_bind] at h
  cases h0 : TM.nextScalar.run t with
  | none => simp [h0] at h
  | some p0 =>
    obtain ⟨x0, t1⟩ := p0
    rw [h0] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    cases h1 : TM.nextScalar.run t1 with
    | none => simp [h1] at h
    | some p1 =>
      obtain ⟨x1, t2⟩ := p1
      rw [h1] at h
      obtain ⟨s1, hx0, ho1, rfl⟩ := nextScalar_some h0
      obtain ⟨s2, hx1, ho2, rfl⟩ := nextScalar_some h1
      simp only [Option.bind_some, TM.ghostRoot, StateT.run, List.getD_cons_zero,
        List.getD_cons_succ] at h
      cases h
      simp only at hx1
      have hg := absorb_some_ground ho1
      obtain ⟨hi1, hs1⟩ := absorb_some hi.1 ho1
      obtain ⟨hi2, hs2⟩ := absorb_some hi1 ho2
      have hd : t.proof.stream.drop t.streamOffset =
          x0 :: x1 :: t.proof.stream.drop (t.streamOffset + 1 + 1) := by
        rw [drop_cons_of_getElem? hx0, drop_cons_of_getElem? hx1]
      have hlt := lt_of_getElem? hx1
      refine ⟨⟨hi2, by dsimp only; omega, hi.2.2⟩, (), ?_, x0, x1,
        (digestFromHalvesRust_eq x0 x1).trans rfl⟩
      rw [TState.toSpec, runK_readCommitment_of _ _ _ hd (by rw [toSpec_ground]; exact hg)]
      simp only [TState.toSpec, hs2, hs1]
      rfl

/-! ## `merkle` -/

namespace TM

/-- `Transcript::merkle(root, block_length, queries, leaf_words)`: `log2_strict(block_length)?`,
the next phase of openings (`opening_offset += 1`), then its shape, its positions and, in checked
mode, its roots; the leaves. The compiled code tests only `x & (x - 1) == 0` in `log2_strict`:
LTO knows `block_length ≠ 0` at every call. -/
def merkle (root : List (BitVec 8)) (blockLength : BitVec 64) (queries : List (BitVec 64))
    (leafWords : ℕ) : TM (List (List (BitVec 64))) := fun t ↦
  match log2StrictRust blockLength with
  | none => none
  | some height =>
    match t.proof.openings[t.openingOffset]? with
    | none => none
    | some phase =>
      let paths := phase.map MerklePathRust.ofOpening
      let t := { t with openingOffset := t.openingOffset + 1 }
      if paths.all (fun p ↦ p.leaf.length == leafWords && p.siblings.length == height) then
        if paths.map (·.leafIndex) = queries then
          if !t.checked || paths.all (fun p ↦ p.root == root) then some (paths.map (·.leaf), t)
          else none
        else none
      else none

end TM

theorem log2StrictRust_two_pow {height : ℕ} (hh : height < 64) :
    log2StrictRust (BitVec.ofNat 64 (2 ^ height)) = some height := by
  rw [log2StrictRust_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (a := 2) (by norm_num) hh), log2Strict]
  have hand : 2 ^ height &&& (2 ^ height - 1) = 0 := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
  rw [ite_eq_left ⟨Nat.two_pow_pos height, hand⟩, bitLength,
    ite_eq_right (Nat.two_pow_pos height).ne', Nat.log2_two_pow, Nat.add_sub_cancel]

/-- The statement's `openAll` when every opening climbs to the root at its own position. -/
private theorem openAll_of_all (root : Digest) (height width : ℕ) :
    ∀ (phase : List Opening),
      (∀ o ∈ phase, openOne (m := Id) keccakF1600 root height width o.leafIndex o = true) →
      (openAll (m := Id) keccakF1600 root height width (phase.map Opening.leafIndex) phase :
        Option (List (List K) × List Opening)) = some (phase.map Opening.leaf, [])
  | [], _ => rfl
  | o :: os, h => by
    have ho := h o (by simp)
    have hos := openAll_of_all root height width os fun o' ho' ↦ h o' (by simp [ho'])
    simp only [List.map_cons, openAll]
    have hob : openOne (m := Id) keccakF1600 root height width o.leafIndex o = (true : Id Bool) :=
      ho
    rw [hob]
    show Option.map (fun r ↦ (o.leaf :: r.1, r.2)) (openAll (m := Id) keccakF1600 root height width
      (os.map Opening.leafIndex) os : Option (List (List K) × List Opening)) = _
    rw [hos]
    rfl

private theorem openOne_of_root (root : Digest) (height width : ℕ) (o : Opening)
    (hi : o.leafIndex < 2 ^ 64) (hw : o.leaf.length = width) (hh : o.path.length = height)
    (hh64 : height < 64) (hr : (MerklePathRust.ofOpening o).root = digestBits root) :
    openOne (m := Id) keccakF1600 root height width o.leafIndex o = true := by
  rw [rootRust_eq o hi (by omega)] at hr
  have hr' := digestBits_injective hr
  unfold openOne
  rw [ite_eq_left ⟨hw, hh⟩]
  show decide ((climb (m := Id) keccakF1600 (keccak256With (m := Id) keccakF1600
    (o.leaf.flatMap K.toBytes)) o.leafIndex o.path : Digest).toList = root.toList) = true
  rw [hr']
  simp

/-- **`merkle` opens the phase the statement opens**, from a root the statement read (the
`i`-th, of `2^height` rows of `width` words), at the positions the statement samples. -/
theorem merkle_run {t t' : TState} {rows : List (List (BitVec 64))} (hi : t.Inv) {i : ℕ}
    {root : Digest} {height width : ℕ} (hroot : t.roots[i]? = some (root, height, width))
    (hh : height < 64) {queries : List (BitVec 64)} {positions : List ℕ}
    (hq : queries.map BitVec.toNat = positions)
    (hm : (TM.merkle (digestBits root) (BitVec.ofNat 64 (2 ^ height)) queries width).run t =
      some (rows, t')) :
    t'.Inv ∧ ∃ rows', runK (VerifierProgram.queryOpenings i positions) t.toSpec =
      some (rows', t'.toSpec) ∧ rows = rows'.map (·.map BF64.toBitVec) := by
  simp only [TM.merkle, StateT.run, log2StrictRust_two_pow hh] at hm
  split at hm
  · cases hm
  · rename_i phase hp
    have hlt := lt_of_getElem? hp
    have hidx : ∀ o ∈ phase, o.leafIndex < 2 ^ 64 :=
      hi.2.2.2.2 phase (List.mem_of_getElem? hp)
    split_ifs at hm with h1 h2 h3
    cases hm
    have h3' : ((phase.map MerklePathRust.ofOpening).all fun p ↦ p.root == digestBits root) =
        true := by simpa [hi.2.2.2.1] using h3
    have hshape : ∀ o ∈ phase, o.leaf.length = width ∧ o.path.length = height := by
      intro o ho
      have := List.all_eq_true.mp h1 (MerklePathRust.ofOpening o) (List.mem_map_of_mem ho)
      simpa [MerklePathRust.ofOpening] using this
    have hpos : phase.map Opening.leafIndex = positions := by
      rw [← hq, ← h2, List.map_map, List.map_map]
      apply List.map_congr_left
      intro o ho
      simp [MerklePathRust.ofOpening]
      exact (Nat.mod_eq_of_lt (hidx o ho)).symm
    have hroots : ∀ o ∈ phase,
        openOne (m := Id) keccakF1600 root height width o.leafIndex o = true := by
      intro o ho
      have := List.all_eq_true.mp h3' (MerklePathRust.ofOpening o) (List.mem_map_of_mem ho)
      exact openOne_of_root root height width o (hidx o ho) (hshape o ho).1 (hshape o ho).2 hh
        (by simpa using this)
    refine ⟨⟨hi.1, hi.2.1, by dsimp only; omega, hi.2.2.2⟩, phase.map Opening.leaf, ?_, ?_⟩
    · simp only [VerifierProgram.queryOpenings, runK, TState.toSpec, Compile.run, hroot,
        drop_cons_of_getElem? hp]
      simp only [Id.run, bind, pure]
      have hop : (openPhase (m := Id) keccakF1600 root height width positions phase :
          Option (List (List K))) = some (phase.map Opening.leaf) := by
        unfold openPhase
        rw [ite_eq_left ⟨hshape, hpos⟩, ← hpos]
        show (match (openAll (m := Id) keccakF1600 root height width
          (phase.map Opening.leafIndex) phase : Option (List (List K) × List Opening)) with
          | some (rows, _) => some rows | none => none) = _
        rw [openAll_of_all root height width phase hroots]
      rw [hop]
    · simp [MerklePathRust.ofOpening, List.map_map]

/-! ## `sumcheck_round_poly` and `sumcheck` -/

/-- `usize` subtraction, wrapping (no overflow checks). -/
def usizeSub (a b : ℕ) : ℕ := (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat

/-- `usize` addition, wrapping. -/
def usizeAdd (a b : ℕ) : ℕ := (BitVec.ofNat 64 a + BitVec.ofNat 64 b).toNat

theorem usizeAdd_eq {a b : ℕ} (h : a + b < 2 ^ 64) : usizeAdd a b = a + b := by
  rw [usizeAdd, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
    Nat.mod_eq_of_lt h]

theorem usizeSub_eq {a b : ℕ} (h : b ≤ a) (ha : a < 2 ^ 64) : usizeSub a b = a - b := by
  rw [usizeSub, BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (by omega)]; exact h),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)]

/-- `E::sum` of a list of words. -/
def sumRust (values : List E) : E := ofLimbsW (eSum (values.map limbs))

theorem sumRust_eq (values : List E) : sumRust values = sumE values := by
  rw [sumRust, eSum_eq, ofLimbsW_limbs]

namespace TM

/-- `Transcript::sumcheck_round_poly(count, claim, eq_factor)`: the coefficients the stream holds,
the one the claim fixes, then `grind_check(grinding_bits(count - 1 + [eq]))`. -/
def sumcheckRoundPoly (count : ℕ) (claim : E) : Option E → TM (List E)
  | none => do
    let constant ← nextScalar
    let tail ← nextScalars (usizeSub count 2)
    let poly := [constant, claim + sumRust tail] ++ tail
    grindCheck (grindingBitsRust (BitVec.ofNat 128 (usizeAdd (usizeSub count 1) 0)))
    Pure.pure poly
  | some eqFactor => do
    let tail ← nextScalars (usizeSub count 1)
    let poly := [claim + eqFactor * sumRust tail] ++ tail
    grindCheck (grindingBitsRust (BitVec.ofNat 128 (usizeAdd (usizeSub count 1) 1)))
    Pure.pure poly

/-- One iteration of `sumcheck`'s loop: the round polynomial, the challenge, `point.push`, the
claim at the challenge. -/
def sumcheckRound (count : ℕ) (acc : List E × E) (equality : Option E) : TM (List E × E) := do
  let message ← sumcheckRoundPoly count acc.2 equality
  let challenge ← sample
  Pure.pure (acc.1 ++ [challenge], polyEvalRust message challenge)

/-- `sumcheck(transcript, claim, count, equalities)`. -/
def sumcheck (claim : E) (count : ℕ) (equalities : List (Option E)) : TM (List E × E) :=
  equalities.foldlM (sumcheckRound count) ([], claim)

end TM

theorem grindingBitsRust_ofNat {n : ℕ} (h : n < 2 ^ 64) :
    grindingBitsRust (BitVec.ofNat 128 n) = grindingBits n := by
  rw [grindingBitsRust_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- **`sumcheck_round_poly` runs `sumcheckRoundPoly`**, for the counts of the verifier's rounds
(`2 ≤ count`: no subtraction wraps; the verifier's counts are at most `5`). -/
theorem Sim.sumcheckRoundPoly {count : ℕ} (hc : 2 ≤ count) (hc' : count < 2 ^ 64) (claim : E)
    (e : Option E) :
    Sim (TM.sumcheckRoundPoly count claim e) (sumcheckRoundPoly count claim e) := by
  cases e with
  | none =>
    simp only [TM.sumcheckRoundPoly, usizeSub_eq (by omega : 2 ≤ count) hc',
      usizeSub_eq (by omega : 1 ≤ count) hc', usizeAdd_eq (by omega : count - 1 + 0 < 2 ^ 64),
      Nat.add_zero,
      grindingBitsRust_ofNat (by omega : count - 1 < 2 ^ 64), sumRust_eq]
    exact Sim.bind Sim.nextScalar fun x ↦ Sim.bind (Sim.nextScalars _) fun xs ↦
      Sim.bind (Sim.grindCheck _) fun _ ↦ Sim.pure _
  | some f =>
    simp only [TM.sumcheckRoundPoly, usizeSub_eq (by omega : 1 ≤ count) hc',
      usizeAdd_eq (by omega : count - 1 + 1 < 2 ^ 64),
      grindingBitsRust_ofNat (by omega : count - 1 + 1 < 2 ^ 64), sumRust_eq]
    exact Sim.bind (Sim.nextScalars _) fun xs ↦ Sim.bind (Sim.grindCheck _) fun _ ↦ Sim.pure _

/-- The loop after the point pushed so far, followed by `k`. -/
theorem SimR.sumcheckLoop_bind {β γ : Type} {count : ℕ} (hc : 2 ≤ count) (hc' : count < 2 ^ 64)
    {r : β → γ → Prop} :
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
    simp only [VerifierProgram.bind_assoc']
    refine SimR.bindEq (Sim.sumcheckRoundPoly hc hc' claim e) fun message ↦
      SimR.bindEq Sim.sample fun c ↦ ?_
    rw [polyEvalRust_eq]
    refine SimR.sumcheckLoop_bind hc hc' es (pre ++ [c]) _ k _ fun p v hp ↦ ?_
    have h1 := h (c :: p) v (by simp [hp])
    rw [List.append_assoc, List.singleton_append]
    exact h1

/-- **`sumcheck` runs `sumcheck`**, followed by `k`, whose point has a coordinate per round. -/
theorem SimR.sumcheck_bind {β γ : Type} (claim : E) {count : ℕ} (hc : 2 ≤ count)
    (hc' : count < 2 ^ 64) (eqs : List (Option E)) {k : List E × E → TM β}
    {K : List E × E → VerifierProgram γ} {r : β → γ → Prop}
    (h : ∀ p v, p.length = eqs.length → SimR (k (p, v)) (K (p, v)) r) :
    SimR (TM.sumcheck claim count eqs >>= k) (sumcheck claim count eqs >>= K) r :=
  SimR.sumcheckLoop_bind hc hc' eqs [] claim k K h

theorem Sim.sumcheck (claim : E) {count : ℕ} (hc : 2 ≤ count) (hc' : count < 2 ^ 64)
    (equalities : List (Option E)) :
    Sim (TM.sumcheck claim count equalities) (sumcheck claim count equalities) := by
  have := SimR.sumcheck_bind claim hc hc' equalities (k := fun x ↦ Pure.pure x)
    (K := VerifierProgram.ret) (r := (· = ·)) fun p v _ ↦ Sim.pure (p, v)
  rw [bind_pure, VerifierProgram.bind_ret'] at this
  exact this

theorem NoCommit.sumcheck (claim : E) (count : ℕ) (equalities : List (Option E)) :
    NoCommit (sumcheck claim count equalities) := by
  induction equalities generalizing claim with
  | nil => exact NoCommit.ret _
  | cons e es ih =>
    rw [LeanVM.Protocol.Verifier.sumcheck]
    refine NoCommit.bind ?_ fun _ ↦ NoCommit.bind NoCommit.sampleChallenge fun _ ↦
      NoCommit.bind (ih _) fun _ ↦ NoCommit.ret _
    cases e
    · exact NoCommit.bind NoCommit.readScalar fun _ ↦ NoCommit.bind (NoCommit.readScalars _)
        fun _ ↦ NoCommit.bind (NoCommit.grindProofOfWork _) fun _ ↦ NoCommit.ret _
    · exact NoCommit.bind (NoCommit.readScalars _) fun _ ↦
        NoCommit.bind (NoCommit.grindProofOfWork _) fun _ ↦ NoCommit.ret _

/-! ## `Transcript::new` and `finish` -/

/-- `Transcript::new(proof, fiat_shamir_iv, public_input, checked)`. -/
def TState.new (proof : Proof) (iv publicInput : Digest) (checked : Bool) : TState :=
  ⟨proof, SpongeRust.new (digestBits iv) (digestBits publicInput), 0, 0, checked, []⟩

/-- **`Transcript::new` is the statement's start**: the sponge at the permutation of `seedInput`,
the whole proof unread. -/
theorem TState.toSpec_new (proof : Proof) (iv publicInput : Digest) (checked : Bool) :
    (TState.new proof iv publicInput checked).toSpec =
      ⟨⟨keccakF1600 (seedInput iv publicInput), [], none⟩, proof.stream, proof.openings, []⟩ := by
  simp only [TState.new, TState.toSpec, (Rv64mc.Model.new_toSpec iv publicInput).1, List.drop_zero]

theorem TState.inv_new (proof : Proof) (iv publicInput : Digest)
    (h : ∀ phase ∈ proof.openings, ∀ o ∈ phase, o.leafIndex < 2 ^ 64) :
    (TState.new proof iv publicInput true).Inv :=
  ⟨(Rv64mc.Model.new_toSpec iv publicInput).2, Nat.zero_le _, Nat.zero_le _, rfl, h⟩

/-- `Transcript::finish`: nothing of the proof is left unread. -/
def TM.finish : TM Unit := fun t ↦
  if t.streamOffset = t.proof.stream.length then
    if t.openingOffset = t.proof.openings.length then some ((), t) else none
  else none

theorem finish_some {t t' : TState} (h : TM.finish.run t = some ((), t')) :
    (t.toSpec.stream.isEmpty && t.toSpec.openings.isEmpty) = true := by
  simp only [TM.finish, StateT.run] at h
  split_ifs at h with h1 h2
  simp [TState.toSpec, h1, h2]

/-- **A mirror that simulates a program accepts what `runProof` accepts**: a transcript started by
`Transcript::new` that returns `true` and then finishes. -/
theorem runProof_of_sim {m : TM Bool} {P : VerifierProgram Bool} (hs : Sim m P) (proof : Proof)
    (iv publicInput : Digest) (hl : ∀ phase ∈ proof.openings, ∀ o ∈ phase, o.leafIndex < 2 ^ 64)
    {t' : TState}
    (h : (do let b ← m; TM.finish; Pure.pure b : TM Bool).run
      (TState.new proof iv publicInput true) = some (true, t')) :
    (runProof (m := Id) keccakF1600 P (keccakF1600 (seedInput iv publicInput)) proof : Bool) =
      true := by
  rw [StateT.run_bind] at h
  cases hm : m.run (TState.new proof iv publicInput true) with
  | none => rw [hm] at h; cases h
  | some p =>
    obtain ⟨b, t₁⟩ := p
    rw [hm] at h
    simp only [Option.bind_eq_bind, Option.bind_some, StateT.run_bind] at h
    cases hf : TM.finish.run t₁ with
    | none => rw [hf] at h; cases h
    | some q =>
      obtain ⟨u, t₂⟩ := q
      rw [hf] at h
      simp only [Option.bind_some, StateT.run_pure, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨hi₁, hr⟩ := Sim.run_eq' hs _ _ _ (TState.inv_new proof iv publicInput hl) hm
      rw [TState.toSpec_new] at hr
      have hfin := finish_some hf
      unfold runProof
      simp only [runK, Id.run] at hr
      rw [show (run (m := Id) keccakF1600 P ⟨⟨keccakF1600 (seedInput iv publicInput), [], none⟩,
        proof.stream, proof.openings, []⟩ : Option (Bool × VerifierProgramState)) =
        some (true, t₁.toSpec) from hr]
      exact hfin

/-! ## The methods succeed when the Rust's checks pass

Each simulation above holds of a mirror that fails; these say the mirrors do not fail where the
Rust does not. -/

private theorem absorb_ground_eq (s : Sponge) (x : E) (tag : ℕ) :
    (absorb (m := Id) keccakF1600 s x tag : Sponge).ground = s.ground := by
  unfold absorb
  split <;> rfl

theorem absorb_some_ground_none {r r' : SpongeRust} (hi : r.Inv) {v : E} {t : BitVec 64}
    (h : r.absorb v t = some r') : r'.ground = none := by
  have hg := absorb_some_ground h
  rw [← toSpec_ground, (absorb_some hi h).2, absorb_ground_eq, toSpec_ground, hg]

/-- `next_scalar` succeeds on a scalar left in the stream when no ground challenge waits. -/
theorem nextScalar_succeeds {t : TState} (hi : t.Inv)
    (hl : t.streamOffset < t.proof.stream.length) (hg : t.sponge.ground = none) :
    ∃ t', TM.nextScalar.run t = some (t.proof.stream[t.streamOffset], t') ∧ t'.Inv ∧
      t'.sponge.ground = none ∧ t'.streamOffset = t.streamOffset + 1 ∧ t'.proof = t.proof := by
  obtain ⟨r', h', hi', -⟩ := absorb_toSpec t.sponge hi.1 hg t.proof.stream[t.streamOffset]
    dsObserveR
  refine ⟨{ t with streamOffset := t.streamOffset + 1, sponge := r' }, ?_,
    ⟨hi', by dsimp only; omega, hi.2.2⟩, absorb_some_ground_none hi.1 h', rfl, rfl⟩
  simp only [TM.nextScalar, StateT.run, List.getElem?_eq_getElem hl, SpongeRust.observe, h',
    Option.map_some]

/-- `next_scalars(n)` succeeds on `n` scalars left in the stream when no ground challenge
waits. -/
theorem nextScalars_succeeds : ∀ (n : ℕ) {t : TState}, t.Inv →
    t.streamOffset + n ≤ t.proof.stream.length → t.sponge.ground = none →
    ∃ xs t', (TM.nextScalars n).run t = some (xs, t') ∧ t'.Inv ∧ t'.sponge.ground = none ∧
      t'.streamOffset = t.streamOffset + n ∧ t'.proof = t.proof
  | 0, t, hi, _, hg => ⟨[], t, rfl, hi, hg, rfl, rfl⟩
  | n + 1, t, hi, hl, hg => by
    obtain ⟨t1, h1, hi1, hg1, ho1, hp1⟩ := nextScalar_succeeds hi (by omega) hg
    obtain ⟨xs, t2, h2, hi2, hg2, ho2, hp2⟩ :=
      nextScalars_succeeds n hi1 (by rw [ho1, hp1]; omega) hg1
    refine ⟨t.proof.stream[t.streamOffset] :: xs, t2, ?_, hi2, hg2, by omega, hp2.trans hp1⟩
    simp only [TM.nextScalars, StateT.run_bind, h1, Option.bind_eq_bind, Option.bind_some, h2]
    rfl

/-- `samples` never fails. -/
theorem sample_succeeds (t : TState) : (TM.sample.run t).isSome := rfl

/-- `grind_check(0)` does nothing. -/
theorem grindCheck_zero (t : TState) : (TM.grindCheck 0).run t = some ((), t) := rfl

/-- `grind_check(bits)` succeeds on a nonce left in the stream, no ground challenge waiting,
when the permutation's proof of work has its `bits` low bits zero. -/
theorem grindCheck_succeeds {t : TState} (hi : t.Inv) {bits : ℕ} (hb : bits ≠ 0)
    (hl : t.streamOffset < t.proof.stream.length) (hg : t.sponge.ground = none) :
    ∃ pow s, t.sponge.absorbNonce t.proof.stream[t.streamOffset] = some (pow, s) ∧
      (powOk bits (UInt64.ofBitVec pow) = true →
        ∃ t', (TM.grindCheck bits).run t = some ((), t')) := by
  obtain ⟨pow, s, h, -, -⟩ := absorbNonce_toSpec t.sponge hi.1 hg t.proof.stream[t.streamOffset]
  refine ⟨pow, s, h, fun hp ↦ ⟨{ t with streamOffset := t.streamOffset + 1, sponge := s }, ?_⟩⟩
  simp only [TM.grindCheck, StateT.run, hb, ↓reduceIte, List.getElem?_eq_getElem hl, h,
    (powMask_iff bits pow).mpr hp, hi.2.2.2.1, Bool.not_true, decide_true, Bool.or_true]

/-- A root's read succeeds on two scalars left in the stream when no ground challenge waits. -/
theorem commit_succeeds {t : TState} (hi : t.Inv) (height width : ℕ)
    (hl : t.streamOffset + 2 ≤ t.proof.stream.length) (hg : t.sponge.ground = none) :
    ∃ root t', (TM.commit height width).run t = some (root, t') := by
  obtain ⟨xs, t', h, -⟩ := nextScalars_succeeds 2 hi hl hg
  refine ⟨digestFromHalvesRust (limbs (xs.getD 0 0)) (limbs (xs.getD 1 0)),
    { t' with roots := t'.roots ++ [(digestFromHalves (xs.getD 0 0, xs.getD 1 0), height, width)] },
    ?_⟩
  simp only [TM.commit, StateT.run_bind, h, Option.bind_eq_bind, Option.bind_some]
  rfl

/-- `merkle` succeeds on the next phase when its shape, positions and roots check. -/
theorem merkle_succeeds {t : TState} {height width : ℕ} (hh : height < 64)
    {root : List (BitVec 8)} {queries : List (BitVec 64)} {phase : List Opening}
    (hp : t.proof.openings[t.openingOffset]? = some phase)
    (hshape : ∀ o ∈ phase, o.leaf.length = width ∧ o.path.length = height)
    (hpos : phase.map (fun o ↦ BitVec.ofNat 64 o.leafIndex) = queries)
    (hroot : ∀ o ∈ phase, (MerklePathRust.ofOpening o).root = root) :
    ∃ t', (TM.merkle root (BitVec.ofNat 64 (2 ^ height)) queries width).run t =
      some ((phase.map MerklePathRust.ofOpening).map (·.leaf), t') := by
  refine ⟨{ t with openingOffset := t.openingOffset + 1 }, ?_⟩
  have h1 : ((phase.map MerklePathRust.ofOpening).all fun p ↦
      p.leaf.length == width && p.siblings.length == height) = true := by
    simp only [List.all_map, List.all_eq_true]
    intro o ho
    simp [MerklePathRust.ofOpening, hshape o ho]
  have h2 : (phase.map MerklePathRust.ofOpening).map (·.leafIndex) = queries := by
    rw [← hpos, List.map_map]
    rfl
  have h3 : ((phase.map MerklePathRust.ofOpening).all fun p ↦ p.root == root) = true := by
    simp only [List.all_map, List.all_eq_true]
    intro o ho
    simp [hroot o ho]
  simp only [TM.merkle, StateT.run, log2StrictRust_two_pow hh, hp, h1, h2, h3, ↓reduceIte,
    Bool.or_true]

/-- `finish` succeeds once the whole proof is read. -/
theorem finish_succeeds {t : TState} (hs : t.streamOffset = t.proof.stream.length)
    (ho : t.openingOffset = t.proof.openings.length) : TM.finish.run t = some ((), t) := by
  simp [TM.finish, StateT.run, hs, ho]

/-! ## Completeness: where the statement runs, the mirror returns

`Comp m P`: from a state keeping `TState.Inv`, whenever the statement's `run` of `P` from the state
it stands for returns, `m` returns. It composes through `bind` with the step's simulation, which
lines up the two intermediate states (`Comp.bind`). -/

/-- `m` returns wherever `P` runs. -/
def Comp {α β : Type} (m : TM α) (P : VerifierProgram β) : Prop :=
  ∀ t b σ', t.Inv → runK P t.toSpec = some (b, σ') → ∃ a t', m.run t = some (a, t')

theorem Comp.pure {α β : Type} (a : α) (b : β) :
    Comp (Pure.pure a : TM α) (VerifierProgram.ret b) :=
  fun _ _ _ _ _ ↦ ⟨a, _, rfl⟩

theorem Comp.bind {α β γ δ : Type} {m : TM α} {P : VerifierProgram β} {r : α → β → Prop}
    {k : α → TM γ} {Q : β → VerifierProgram δ} (hm : Comp m P) (hs : SimR m P r)
    (hk : ∀ a b, r a b → Comp (k a) (Q b)) : Comp (m >>= k) (P >>= Q) := by
  intro t c σ' hi h
  rw [runK_bind] at h
  cases hP : runK P t.toSpec with
  | none => rw [hP] at h; cases h
  | some p =>
    obtain ⟨b₁, σ₁⟩ := p
    rw [hP] at h
    obtain ⟨a, t₁, hm₁⟩ := hm t b₁ σ₁ hi hP
    obtain ⟨hi₁, b, hb, hab⟩ := hs t a t₁ hi hm₁
    rw [hb] at hP
    simp only [Option.some.injEq, Prod.mk.injEq] at hP
    obtain ⟨rfl, rfl⟩ := hP
    obtain ⟨c', t₂, h₂⟩ := hk a b hab t₁ c _ hi₁ h
    exact ⟨c', t₂, by rw [StateT.run_bind, hm₁]; exact h₂⟩

theorem Comp.bindEq {α γ δ : Type} {m : TM α} {P : VerifierProgram α} {k : α → TM γ}
    {Q : α → VerifierProgram δ} (hm : Comp m P) (hs : Sim m P) (hk : ∀ a, Comp (k a) (Q a)) :
    Comp (m >>= k) (P >>= Q) :=
  Comp.bind hm hs fun a _ h ↦ by subst h; exact hk a

private theorem drop_eq_cons {α : Type} {l : List α} {i : ℕ} {x : α} {xs : List α}
    (h : l.drop i = x :: xs) : ∃ hi : i < l.length, l[i] = x := by
  have hlt : i < l.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    cases h
  refine ⟨hlt, ?_⟩
  rw [List.drop_eq_getElem_cons hlt] at h
  exact (List.cons.inj h).1

theorem Comp.nextScalar : Comp TM.nextScalar VerifierProgram.readScalar := by
  intro t b σ' hi h
  simp only [VerifierProgram.readScalar, runK, Compile.run, Id.run, TState.toSpec] at h
  split at h
  · rename_i x xs hs hg
    obtain ⟨hl, -⟩ := drop_eq_cons hs
    obtain ⟨t', h', -⟩ := nextScalar_succeeds hi hl (by rw [← toSpec_ground]; exact hg)
    exact ⟨_, t', h'⟩
  · cases h

theorem Comp.sample : Comp TM.sample VerifierProgram.sampleChallenge :=
  fun _ _ _ _ _ ↦ ⟨_, _, rfl⟩

theorem Comp.nextScalars : ∀ n, Comp (TM.nextScalars n) (VerifierProgram.readScalars n)
  | 0 => Comp.pure _ _
  | n + 1 => Comp.bindEq Comp.nextScalar Sim.nextScalar fun _ ↦
      Comp.bindEq (Comp.nextScalars n) (Sim.nextScalars n) fun _ ↦ Comp.pure _ _

theorem Comp.samples : ∀ n, Comp (TM.samples n) (VerifierProgram.sampleChallenges n)
  | 0 => Comp.pure _ _
  | n + 1 => Comp.bindEq Comp.sample Sim.sample fun _ ↦
      Comp.bindEq (Comp.samples n) (Sim.samples n) fun _ ↦ Comp.pure _ _

theorem Comp.grindCheck (bits : ℕ) :
    Comp (TM.grindCheck bits) (VerifierProgram.grindProofOfWork bits) := by
  intro t b σ' hi h
  by_cases hb : bits = 0
  · subst hb
    exact ⟨(), t, rfl⟩
  · simp only [VerifierProgram.grindProofOfWork, hb, ↓reduceIte, runK, Compile.run, Id.run,
      TState.toSpec] at h
    split at h
    · rename_i n xs hs hg
      obtain ⟨hl, rfl⟩ := drop_eq_cons hs
      obtain ⟨pow, s, habs, hk⟩ :=
        grindCheck_succeeds hi hb hl (by rw [← toSpec_ground]; exact hg)
      obtain ⟨-, -, hspec⟩ := absorbNonce_some hi.1 habs
      rw [← hspec] at h
      by_cases hp : powOk bits (UInt64.ofBitVec pow) = true
      · obtain ⟨t', h'⟩ := hk hp
        exact ⟨(), t', h'⟩
      · change (if powOk bits (UInt64.ofBitVec pow) = true then _ else _ : Id _) = _ at h
        rw [ite_eq_right hp] at h
        cases h
    · cases h

theorem Comp.require_iff {c c' : Prop} [Decidable c] [Decidable c'] (h : c ↔ c') :
    Comp (TM.require c) (VerifierProgram.require c') := by
  intro t b σ' _ hr
  by_cases hc : c'
  · exact ⟨(), t, by simp [TM.require, StateT.run, h.mpr hc]⟩
  · simp only [VerifierProgram.require, hc, ↓reduceIte, runK, Compile.run, Id.run] at hr
    cases hr

/-- A `checked()` branch: the body's completeness. -/
theorem Comp.whenChecked_bind {γ δ : Type} {body : TM Unit} {k : Unit → TM γ}
    {Q : VerifierProgram δ} (h : Comp (body >>= k) Q) : Comp (TM.whenChecked body >>= k) Q := by
  intro t b σ' hi hr
  have e : (TM.whenChecked body >>= k).run t = (body >>= k).run t := by
    have e1 : TM.whenChecked body >>= k =
        TM.checked >>= fun c ↦ (if c then body else Pure.pure ()) >>= k := by
      simp only [TM.whenChecked, bind_assoc]
    rw [e1]
    show ((if t.checked then body else Pure.pure ()) >>= k).run t = _
    rw [hi.2.2.2.1]
    rfl
  rw [e]
  exact h t b σ' hi hr

/-- A pure step of the Rust that returns. -/
theorem Comp.ofOption_bind {α γ δ : Type} {o : Option α} {a : α} {k : α → TM γ}
    {Q : VerifierProgram δ} (ho : o = some a) (h : Comp (k a) Q) :
    Comp (TM.ofOption o >>= k) Q := by
  subst ho
  simpa only [TM.ofOption, pure_bind] using h

theorem Comp.sumcheckRoundPoly {count : ℕ} (hc : 2 ≤ count) (hc' : count < 2 ^ 64) (claim : E)
    (e : Option E) :
    Comp (TM.sumcheckRoundPoly count claim e) (sumcheckRoundPoly count claim e) := by
  cases e with
  | none =>
    simp only [TM.sumcheckRoundPoly, usizeSub_eq (by omega : 2 ≤ count) hc',
      usizeSub_eq (by omega : 1 ≤ count) hc', usizeAdd_eq (by omega : count - 1 + 0 < 2 ^ 64),
      Nat.add_zero, grindingBitsRust_ofNat (by omega : count - 1 < 2 ^ 64), sumRust_eq]
    exact Comp.bindEq Comp.nextScalar Sim.nextScalar fun x ↦
      Comp.bindEq (Comp.nextScalars _) (Sim.nextScalars _) fun xs ↦
        Comp.bindEq (Comp.grindCheck _) (Sim.grindCheck _) fun _ ↦ Comp.pure _ _
  | some f =>
    simp only [TM.sumcheckRoundPoly, usizeSub_eq (by omega : 1 ≤ count) hc',
      usizeAdd_eq (by omega : count - 1 + 1 < 2 ^ 64),
      grindingBitsRust_ofNat (by omega : count - 1 + 1 < 2 ^ 64), sumRust_eq]
    exact Comp.bindEq (Comp.nextScalars _) (Sim.nextScalars _) fun xs ↦
      Comp.bindEq (Comp.grindCheck _) (Sim.grindCheck _) fun _ ↦ Comp.pure _ _

/-- The sumcheck loop after the point pushed so far, followed by `k`. -/
theorem Comp.sumcheckLoop_bind {β γ : Type} {count : ℕ} (hc : 2 ≤ count)
    (hc' : count < 2 ^ 64) :
    ∀ (eqs : List (Option E)) (pre : List E) (claim : E) (k : List E × E → TM β)
    (K : List E × E → VerifierProgram γ),
    (∀ p v, p.length = eqs.length → Comp (k (pre ++ p, v)) (K (p, v))) →
    Comp (eqs.foldlM (TM.sumcheckRound count) (pre, claim) >>= k) (sumcheck claim count eqs >>= K)
  | [], pre, claim, k, K, h => by
    have h0 := h [] claim rfl
    rw [List.append_nil] at h0
    simp only [List.foldlM_nil, pure_bind]
    exact h0
  | e :: es, pre, claim, k, K, h => by
    simp only [List.foldlM_cons, TM.sumcheckRound, bind_assoc, pure_bind]
    rw [sumcheck]
    simp only [VerifierProgram.bind_assoc']
    refine Comp.bindEq (Comp.sumcheckRoundPoly hc hc' claim e)
      (Sim.sumcheckRoundPoly hc hc' claim e) fun message ↦
      Comp.bindEq Comp.sample Sim.sample fun c ↦ ?_
    rw [polyEvalRust_eq]
    refine Comp.sumcheckLoop_bind hc hc' es (pre ++ [c]) _ k _ fun p v hp ↦ ?_
    have h1 := h (c :: p) v (by simp [hp])
    rw [List.append_assoc, List.singleton_append]
    exact h1

theorem Comp.sumcheck_bind {β γ : Type} (claim : E) {count : ℕ} (hc : 2 ≤ count)
    (hc' : count < 2 ^ 64) (eqs : List (Option E)) {k : List E × E → TM β}
    {K : List E × E → VerifierProgram γ}
    (h : ∀ p v, p.length = eqs.length → Comp (k (p, v)) (K (p, v))) :
    Comp (TM.sumcheck claim count eqs >>= k) (sumcheck claim count eqs >>= K) :=
  Comp.sumcheckLoop_bind hc hc' eqs [] claim k K h

/-- `sumcheck`, its point of a coordinate per round. -/
theorem SimR.sumcheck_len (claim : E) {count : ℕ} (hc : 2 ≤ count) (hc' : count < 2 ^ 64)
    (eqs : List (Option E)) :
    SimR (TM.sumcheck claim count eqs) (sumcheck claim count eqs)
      fun a b ↦ a = b ∧ a.1.length = eqs.length := by
  have h := SimR.sumcheck_bind claim hc hc' eqs (k := fun x ↦ Pure.pure x)
    (K := VerifierProgram.ret) (r := fun a b ↦ a = b ∧ a.1.length = eqs.length)
    fun p v hp ↦ SimR.pure ⟨rfl, hp⟩
  rwa [bind_pure, VerifierProgram.bind_ret'] at h

end

end Rv64mc.Model
