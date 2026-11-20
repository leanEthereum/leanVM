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
over `TState` that fails on any `Err` or panic.

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
verifier makes it (`next_scalars(2)` and `Digest::from_halves`, `TM.commit`).
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

/-- `m` runs `P`, its value related to `P`'s by `r`. -/
def SimR {α β : Type} (m : TM α) (P : VerifierProgram β) (r : α → β → Prop) : Prop :=
  ∀ t a t', t.Inv → m.run t = some (a, t') →
    t'.Inv ∧ ∃ b, runK P t.toSpec = some (b, t'.toSpec) ∧ r a b

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
  induction P generalizing σ with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    simp only [VerifierProgram.bind, runK]
    rw [Compile.run, Compile.run]
    split
    · exact ih _ _
    · rfl
  | sample k ih =>
    simp only [VerifierProgram.bind, runK]
    rw [Compile.run, Compile.run]
    exact ih _ _
  | grind bits k ih =>
    simp only [VerifierProgram.bind, runK]
    rw [Compile.run, Compile.run]
    split
    · simp only [Id.run, bind, pure]
      rename_i _ _ n _ _ _
      obtain ⟨pow, sp⟩ := absorbNonce (m := Id) keccakF1600 σ.sponge n
      dsimp only
      split_ifs
      · exact ih _
      · rfl
    · rfl
  | commit h w k ih =>
    simp only [VerifierProgram.bind, runK]
    rw [Compile.run, Compile.run]
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

theorem SimR.mono {α β : Type} {m : TM α} {P : VerifierProgram β} {r r' : α → β → Prop}
    (h : SimR m P r) (hr : ∀ a b, r a b → r' a b) : SimR m P r' := by
  intro t a t' hi hm
  obtain ⟨hi', b, hb, hab⟩ := h t a t' hi hm
  exact ⟨hi', b, hb, hr a b hab⟩

theorem SimR.pure {α β : Type} {r : α → β → Prop} {a : α} {b : β} (h : r a b) :
    SimR (Pure.pure a : TM α) (VerifierProgram.ret b) r := by
  intro t a' t' hi hm
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  exact ⟨hi, b, rfl, h⟩

theorem SimR.bind {α β γ δ : Type} {m : TM α} {P : VerifierProgram β} {r : α → β → Prop}
    {k : α → TM γ} {Q : β → VerifierProgram δ} {r' : γ → δ → Prop} (hm : SimR m P r)
    (hk : ∀ a b, r a b → SimR (k a) (Q b) r') : SimR (m >>= k) (P >>= Q) r' := by
  intro t c t' hi h
  rw [StateT.run_bind] at h
  cases hmt : m.run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨a, t₁⟩ := p
    rw [hmt] at h
    obtain ⟨hi₁, b, hb, hab⟩ := hm t a t₁ hi hmt
    rw [runK_bind, hb]
    exact hk a b hab t₁ c t' hi₁ h

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

/-! ## Reading and sampling -/

theorem drop_cons_of_getElem? {α : Type} {l : List α} {i : ℕ} {x : α} (h : l[i]? = some x) :
    l.drop i = x :: l.drop (i + 1) := by
  have hlt : i < l.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  rw [List.getElem?_eq_getElem hlt] at h
  rw [List.drop_eq_getElem_cons hlt, Option.some.inj h]

theorem lt_of_getElem? {α : Type} {l : List α} {i : ℕ} {x : α} (h : l[i]? = some x) :
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

theorem sub_clz_eq_bitLength128 (x : BitVec 128) : 128 - x.clz.toNat = bitLength x.toNat := by
  by_cases hx : x = 0#128
  · subst hx
    have : (0#128).clz = 128#128 := BitVec.clz_eq_iff_eq_zero.mpr rfl
    simp [this, bitLength]
  · have hlt : x.clz < 128#128 := BitVec.clz_lt_iff_ne_zero.mpr hx
    have hlt' : x.clz.toNat < 128 := by
      have := BitVec.lt_def.mp hlt
      simpa using this
    have hlo := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by norm_num) hx
    have hhi := BitVec.toNat_lt_two_pow_sub_clz (x := x)
    have hne : x.toNat ≠ 0 := by
      intro h
      exact hx (BitVec.eq_of_toNat_eq (by simpa using h))
    have hlog : Nat.log2 x.toNat = 128 - 1 - x.clz.toNat := by
      rw [Nat.log2_eq_iff hne]
      refine ⟨hlo, ?_⟩
      have : 128 - 1 - x.clz.toNat + 1 = 128 - x.clz.toNat := by omega
      rw [this]
      exact hhi
    simp only [bitLength, hne, ite_false, hlog]
    omega

/-- **`grinding_bits` is `grindingBits`.** -/
theorem grindingBitsRust_eq (numerator : BitVec 128) :
    grindingBitsRust numerator = grindingBits numerator.toNat := by
  rw [grindingBitsRust, grindingBits, securityBits]
  by_cases h : numerator ≤ 1#128
  · have h' : numerator.toNat ≤ 1 := by simpa [BitVec.le_def] using h
    rw [ite_eq_left h, ite_eq_left h']
  · have h' : ¬ numerator.toNat ≤ 1 := by simpa [BitVec.le_def] using h
    rw [ite_eq_right h, ite_eq_right h', sub_clz_eq_bitLength128, bitLength]
    have hne : (numerator - 1#128).toNat ≠ 0 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
      simp
      omega
    rw [ite_eq_right hne, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
    simp

/-- The proof-of-work mask: `1u64.checked_shl(bits).map_or(u64::MAX, |bit| bit - 1)`. -/
def powMask (bits : ℕ) : BitVec 64 := if bits < 64 then (1#64 <<< bits) - 1#64 else BitVec.allOnes 64

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

theorem runK_readCommitment_of (height width : ℕ) (σ : VerifierProgramState) {x0 x1 : E}
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
mode, its roots; the leaves. -/
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

theorem digestBits_injective : Function.Injective digestBits := by
  intro a b h
  have h' := congrArg digestWordsRust h
  rw [digestBits, digestBits, digestWordsRust_digestBytes, digestWordsRust_digestBytes] at h'
  have hl : a.toList = b.toList :=
    List.map_injective_iff.mpr (fun x y hxy ↦ UInt64.toBitVec_inj.mp hxy) h'
  exact Vector.toList_inj.mp hl

theorem log2StrictRust_two_pow {height : ℕ} (hh : height < 64) :
    log2StrictRust (BitVec.ofNat 64 (2 ^ height)) = some height := by
  rw [log2StrictRust_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (a := 2) (by norm_num) hh), log2Strict]
  have hand : 2 ^ height &&& (2 ^ height - 1) = 0 := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
  rw [ite_eq_left ⟨Nat.two_pow_pos height, hand⟩, bitLength,
    ite_eq_right (Nat.two_pow_pos height).ne', Nat.log2_two_pow, Nat.add_sub_cancel]

/-- The statement's `openAll` when every opening climbs to the root at its own position. -/
theorem openAll_of_all (root : Digest) (height width : ℕ) :
    ∀ (phase : List Opening),
      (∀ o ∈ phase, openOne (m := Id) keccakF1600 root height width o.leafIndex o = true) →
      (openAll (m := Id) keccakF1600 root height width (phase.map Opening.leafIndex) phase :
        Option (List (List K) × List Opening)) = some (phase.map Opening.leaf, [])
  | [], _ => rfl
  | o :: os, h => by
    have ho := h o (by simp)
    have hos := openAll_of_all root height width os fun o' ho' ↦ h o' (by simp [ho'])
    simp only [List.map_cons, openAll]
    have hob : openOne (m := Id) keccakF1600 root height width o.leafIndex o = (true : Id Bool) := ho
    rw [hob]
    show Option.map (fun r ↦ (o.leaf :: r.1, r.2)) (openAll (m := Id) keccakF1600 root height width
      (os.map Opening.leafIndex) os : Option (List (List K) × List Opening)) = _
    rw [hos]
    rfl

theorem openOne_of_root (root : Digest) (height width : ℕ) (o : Opening)
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
    grindCheck (grindingBitsRust (BitVec.ofNat 128 (usizeSub count 1 + 0)))
    Pure.pure poly
  | some eqFactor => do
    let tail ← nextScalars (usizeSub count 1)
    let poly := [claim + eqFactor * sumRust tail] ++ tail
    grindCheck (grindingBitsRust (BitVec.ofNat 128 (usizeSub count 1 + 1)))
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
(`2 ≤ count`: neither subtraction wraps). -/
theorem Sim.sumcheckRoundPoly {count : ℕ} (hc : 2 ≤ count) (hc' : count < 2 ^ 64) (claim : E)
    (e : Option E) :
    Sim (TM.sumcheckRoundPoly count claim e) (sumcheckRoundPoly count claim e) := by
  cases e with
  | none =>
    simp only [TM.sumcheckRoundPoly, usizeSub_eq (by omega : 2 ≤ count) hc',
      usizeSub_eq (by omega : 1 ≤ count) hc', Nat.add_zero,
      grindingBitsRust_ofNat (by omega : count - 1 < 2 ^ 64), sumRust_eq]
    exact Sim.bind Sim.nextScalar fun x ↦ Sim.bind (Sim.nextScalars _) fun xs ↦
      Sim.bind (Sim.grindCheck _) fun _ ↦ Sim.pure _
  | some f =>
    simp only [TM.sumcheckRoundPoly, usizeSub_eq (by omega : 1 ≤ count) hc',
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

end

end Rv64mc.Model
