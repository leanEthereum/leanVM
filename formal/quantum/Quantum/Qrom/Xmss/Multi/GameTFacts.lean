module

public import Quantum.Qrom.Xmss.GameTFacts
public import Quantum.Qrom.Xmss.Multi.GameT
public import Quantum.Qrom.Xmss.Multi.Classify
public import Quantum.Xmss.Assembly.PrefixRun

@[expose] public section

/-!
# The call invariants of leanXMSS's multi-user runtime-2 game, in the decompressed basis

The `n`-user analog of `Quantum.Qrom.Xmss.GameTFacts`: the facts `win_imp_badQN` needs about the
register at the end of the challenge prefix (`prefixTN (SelMemN n) cwUpdN A` realized at
`thetaOfN S0 w`, run against `runtimeR`), per user `i`: user `i`'s transcript's signatures are the
table's (`(w.user i).signature H`), user `i`'s memory records their selections (`Records`) and
every hardwired chain cell of user `i` has a known input (`HwKnown`, on `projU i`). The function
`H` is the register's view `hvwN s`; the template programs no message-digest cell of any user
(`cellOf_ne_msg`), so the view at those cells never changes along the run (`MsgAgree`).

* Support semantics (`HTQN`, `HTQ₂N`) at the register `RRegN n M`, the ports in the decompressed
  basis, reveals, program ports of user `i` (`htQ₂N_progThen`), sponge-only steps, read programs
  as functions of the register (`DetQN`).
* `det_grindTN`: user `i`'s randomizer search answers the view's selection and records it in
  user `i`'s memory (`grindMem`), the other users' memories kept.
* `htQ₂_selectTN`, `htQ₂_publishTN`, `htQ₂_topTN_none`, `htQ₂_topTN_some` (a memo hit makes no
  call), `invQN_step`, `htQ₂_signTN`: a signature keeps the invariant `InvQN log T` (per-user
  transcripts, records, hardwired cells from published signatures, selected keys requested, the
  memo agreeing with the view and only holding requested top keys).
* `htQ_logSignsN`, `htQ₂_prefixTN`: the adversary's memo transform with all users' transcript.
* `prefixFactsQN`: on every branch of the prefix, in the decompressed basis, the register is
  supported where `PreFactsQN` holds, for a good table.
-/

open Matrix IPFunctor
open scoped Kronecker

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss (Known layerDisclosed)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT revealThen progThen readLift
  readLiftQ RevealVals recStep_branch liftRead decR decR_branch_apply decR_step_noBot NoBot
  querySupportedOn_run querySupportedOn_queryStep_imp clsKraus_dec_ne_zero dbs_dec_ne_zero
  cellRead_dec_ne_zero one_dec_ne_zero compressAll_mul_cellDiscard_mul_compressAll_ne_zero
  snd_eq_of_hwPort dbs_one_dec_eq liftAns lowerRes lowerRes_liftAns realizeT_readLift_readCall
  realizeT_bind realizeT_bind₂ readLift_bind₂ realizeT_substitute querySupportedOn_inter initU
  noBot_init querySupportedOn_conj_compressReg or_isSome)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec muLogSigns muLogAfter withMuSignLog MuSignLog)

attribute [local irreducible] xmssRom

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

-- The adversary's commands, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "MuP" n => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (muAdvSpec n SigningRequest (Option Signature))

/-- The register of runtime 2 with record ports at the memory `Finset (HPosN n) × M`. -/
abbrev RRegN (n : ℕ) (M : Type) : Type :=
  HwReg HashOutput HashDomain (Finset (HPosN n) × M)

/-- The signature of runtime 2 with record ports at the memory `Finset (HPosN n) × M`. -/
abbrev RSpecN (n : ℕ) (M : Type) : QuantumOracleSpec.{0, 0} :=
  recHwSpec HashOutput HashDomain (HPosN n) M

/-! ## The canonical game -/

/-- **The canonical multi-user runtime-2 game** at the hidden values `θ`: the trials' reads record
codeword selections in user `i`'s memory (`cwUpdN i`). -/
noncomputable def muGameQN (valid : SignLog → Bool) (A : MuAdversary n) (θ : HPosN n → Digest) :
    QComp (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)) (QReg.of Unit) (QReg.of Unit)
      Bool :=
  realizeT θ (muGameT (SelMemN n) cwUpdN valid A)

/-- The canonical challenge prefix at `θ`. -/
noncomputable def prefixQN (A : MuAdversary n) (θ : HPosN n → Digest) :
    QComp (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)) (QReg.of Unit) (QReg.of Unit)
      ((Fin n → PublicKey) × MuRun n) :=
  realizeT θ (prefixTN (SelMemN n) cwUpdN A)

/-- The initial memory: no coordinate recorded, no selection. -/
def m0N : Finset (HPosN n) × SelMemN n :=
  (∅, fun _ _ _ ↦ none)

/-! ## Support semantics -/

section hoare

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset (HPosN n) × M)

/-- **Support semantics of a program in the decompressed basis**: from an operator supported on
registers in `P`, the branch at every leaf `p` is supported on `Q p`. -/
def HTQN {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments.{0} (RSpecN n M) Ω A)
    (P : Set (RRegN n M)) (Q : (Σ u, Ω u) → Set (RRegN n M)) : Prop :=
  ∀ ρ : Matrix (A × RRegN n M) (A × RRegN n M) ℂ,
    QuerySupportedOn (fun m : A × RRegN n M ↦ m.2) P ρ →
    ∀ p, QuerySupportedOn (fun m : p.1 × RRegN n M ↦ m.2) (Q p)
      (((decR (X := HashOutput) (Z := HashDomain) m₀).run .instruments y).branch p ρ)

/-- `HTQN` for programs on a fixed final register. -/
def HTQ₂N {A B : QReg} {α : Type} (y : QComp (RSpecN n M) A B α) (P : Set (RRegN n M))
    (Q : α → Set (RRegN n M)) : Prop :=
  ∀ ρ : Matrix (A × RRegN n M) (A × RRegN n M) ℂ,
    QuerySupportedOn (fun m : A × RRegN n M ↦ m.2) P ρ →
    ∀ a, QuerySupportedOn (fun m : B × RRegN n M ↦ m.2) (Q a)
      (((decR (X := HashOutput) (Z := HashDomain) m₀).run₂ .instruments y).branch a ρ)

variable {m₀}

theorem HTQN.mono {Ω : QReg → Type} {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (RSpecN n M) Ω A}
    {P P' : Set (RRegN n M)} {Q Q' : (Σ u, Ω u) → Set (RRegN n M)} (h : HTQN m₀ y P Q)
    (hP : P' ⊆ P) (hQ : ∀ p, Q p ⊆ Q' p) : HTQN m₀ y P' Q' :=
  fun ρ hρ p ↦ (h ρ (hρ.mono hP) p).mono (hQ p)

theorem HTQ₂N.mono {A B : QReg} {α : Type} {y : QComp (RSpecN n M) A B α}
    {P P' : Set (RRegN n M)} {Q Q' : α → Set (RRegN n M)} (h : HTQ₂N m₀ y P Q) (hP : P' ⊆ P)
    (hQ : ∀ a, Q a ⊆ Q' a) : HTQ₂N m₀ y P' Q' :=
  fun ρ hρ a ↦ (h ρ (hρ.mono hP) a).mono (hQ a)

theorem htQ₂N_iff {A B : QReg} {α : Type} (y : QComp (RSpecN n M) A B α) (P : Set (RRegN n M))
    (Q : α → Set (RRegN n M)) : HTQ₂N m₀ y P Q ↔ HTQN m₀ y P fun p ↦ Q p.2.2 := by
  constructor
  · intro h ρ hρ p
    obtain ⟨u, hu, a⟩ := p
    subst hu
    exact h ρ hρ a
  · intro h ρ hρ a
    exact h ρ hρ ⟨B, rfl, a⟩

theorem htQN_of_htQ₂N {A B : QReg} {α : Type} {y : QComp (RSpecN n M) A B α}
    {P : Set (RRegN n M)} {Q : α → Set (RRegN n M)} (h : HTQ₂N m₀ y P Q) :
    HTQN m₀ y P fun p ↦ Q p.2.2 :=
  (htQ₂N_iff y P Q).mp h

theorem htQ₂N_of_htQN {A B : QReg} {α : Type} {y : QComp (RSpecN n M) A B α}
    {P : Set (RRegN n M)} {Q : α → Set (RRegN n M)} (h : HTQN m₀ y P fun p ↦ Q p.2.2) :
    HTQ₂N m₀ y P Q :=
  (htQ₂N_iff y P Q).mpr h

theorem htQN_pure {Ω : QReg → Type} {A : QReg} (y : Ω A) {P : Set (RRegN n M)}
    {Q : (Σ u, Ω u) → Set (RRegN n M)} (h : P ⊆ Q ⟨A, y⟩) :
    HTQN m₀ (QuantumComp.pure (L := LocalSig.instruments.{0}) (spec := RSpecN n M) y) P Q := by
  classical
  intro ρ hρ p
  rw [QuantumRuntime.run_pure]
  by_cases hp : p = ⟨A, y⟩
  · subst hp
    rw [DSubInstrument.branch_ret_self]
    exact hρ.mono h
  · rw [DSubInstrument.branch_ret_of_ne _ hp]
    exact querySupportedOn_zero _ _

theorem htQ₂N_pure {A : QReg} {α : Type} (a : α) {P : Set (RRegN n M)} {Q : α → Set (RRegN n M)}
    (h : P ⊆ Q a) : HTQ₂N m₀ (QuantumComp₂.pure a : QComp (RSpecN n M) A A α) P Q := by
  intro ρ hρ a'
  rw [QuantumRuntime.run₂_pure]
  by_cases ha : a' = a
  · subst ha
    rw [SubInstrument.branch_pure_self]
    exact hρ.mono h
  · rw [SubInstrument.branch_pure_of_ne ha]
    exact querySupportedOn_zero _ _

theorem HTQN.bind {Ω Ω' : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (RSpecN n M) Ω A}
    {P : Set (RRegN n M)} {Q : (Σ u, Ω u) → Set (RRegN n M)} (hx : HTQN m₀ x P Q)
    {k : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (RSpecN n M) Ω' u}
    {R : (Σ u, Ω' u) → Set (RRegN n M)} (hk : ∀ u a, HTQN m₀ (k u a) (Q ⟨u, a⟩) R) :
    HTQN m₀ (x.bind k) P R := by
  intro ρ hρ p
  rw [QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun q ↦ hk q.1 q.2 _ (hx ρ hρ q) p

theorem HTQ₂N.bind {A B C : QReg} {α β : Type} {x : QComp (RSpecN n M) A B α}
    {P : Set (RRegN n M)} {Q : α → Set (RRegN n M)} (hx : HTQ₂N m₀ x P Q)
    {k : α → QComp (RSpecN n M) B C β} {R : β → Set (RRegN n M)}
    (hk : ∀ a, HTQ₂N m₀ (k a) (Q a) R) : HTQ₂N m₀ (x.bind k) P R := by
  intro ρ hρ b
  erw [QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun a ↦ hk a _ (hx ρ hρ a) b

theorem htQN_primBind {Ω : QReg → Type} {A : QReg} (o : LocalSig.instruments.{0}.Op A)
    {k : (b : LocalSig.instruments.{0}.Outcome o) →
      QuantumComp LocalSig.instruments.{0} (RSpecN n M) Ω (LocalSig.instruments.{0}.next o b)}
    {P : Set (RRegN n M)} {Q : (Σ u, Ω u) → Set (RRegN n M)} (hk : ∀ b, HTQN m₀ (k b) P Q) :
    HTQN m₀ (QuantumComp.primBind o k) P Q := by
  intro ρ hρ p
  rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun b ↦ hk b _ (QuerySupportedOn.amplify_snd (q := id) hρ _) p

/-- **A local operation keeps the register.** -/
theorem htQ₂N_act_bind {A B C : QReg} {α β : Type} (p : SubInstrument A B β)
    {k : β → QComp (RSpecN n M) B C α} {P : Set (RRegN n M)} {Q : α → Set (RRegN n M)}
    (hk : ∀ b, HTQ₂N m₀ (k b) P Q) : HTQ₂N m₀ ((QComp.act p).bind k) P Q := by
  intro ρ hρ a
  rw [QuantumRuntime.run₂_act_bind]
  erw [DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun b ↦ hk b _ (QuerySupportedOn.amplify_snd (q := id) hρ _) a

theorem htQ₂N_act {A B : QReg} {β : Type} (p : SubInstrument A B β) (P : Set (RRegN n M)) :
    HTQ₂N m₀ (QComp.act (spec := RSpecN n M) p) P fun _ ↦ P := by
  rw [← QuantumComp₂.bind_pure (QComp.act (spec := RSpecN n M) p)]
  exact htQ₂N_act_bind p fun b ↦ htQ₂N_pure b subset_rfl

/-- A call whose step moves the support from `P` to `P' r` at the result `r`. -/
theorem htQN_queryBind {Ω : QReg → Type} {A : QReg} (i : (RSpecN n M).Port)
    (E : QReg) (ℓ : A ≃ (RSpecN n M).In i × E)
    {k : (RSpecN n M).Result i →
      QuantumComp LocalSig.instruments.{0} (RSpecN n M) Ω (QReg.of ((RSpecN n M).Out i × E))}
    {P : Set (RRegN n M)} (P' : (RSpecN n M).Result i → Set (RRegN n M))
    {Q : (Σ u, Ω u) → Set (RRegN n M)}
    (hstep : ∀ r (σ : Matrix ((RSpecN n M).In i × RRegN n M) ((RSpecN n M).In i × RRegN n M) ℂ),
      QuerySupportedOn (fun m : (RSpecN n M).In i × RRegN n M ↦ m.2) P σ →
        QuerySupportedOn (fun m : (RSpecN n M).Out i × RRegN n M ↦ m.2) (P' r)
          (((decR (X := HashOutput) (Z := HashDomain) m₀).step i).branch r σ))
    (hk : ∀ r, HTQN m₀ (k r) (P' r) Q) : HTQN m₀ (QuantumComp.queryBind i E ℓ k) P Q := by
  intro ρ hρ p
  rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun r ↦ hk r _
    (querySupportedOn_queryStep_imp (decR (X := HashOutput) (Z := HashDomain) m₀) i E ℓ r P
      (P' r) (hstep r) hρ) p

theorem htQ₂N_queryBind {A B : QReg} {α : Type} (i : (RSpecN n M).Port)
    (E : QReg) (ℓ : A ≃ (RSpecN n M).In i × E)
    {k : (RSpecN n M).Result i → QComp (RSpecN n M) (QReg.of ((RSpecN n M).Out i × E)) B α}
    {P : Set (RRegN n M)} (P' : (RSpecN n M).Result i → Set (RRegN n M))
    {Q : α → Set (RRegN n M)}
    (hstep : ∀ r (σ : Matrix ((RSpecN n M).In i × RRegN n M) ((RSpecN n M).In i × RRegN n M) ℂ),
      QuerySupportedOn (fun m : (RSpecN n M).In i × RRegN n M ↦ m.2) P σ →
        QuerySupportedOn (fun m : (RSpecN n M).Out i × RRegN n M ↦ m.2) (P' r)
          (((decR (X := HashOutput) (Z := HashDomain) m₀).step i).branch r σ))
    (hk : ∀ r, HTQ₂N m₀ (k r) (P' r) Q) :
    HTQ₂N m₀ (QuantumComp₂.queryBind (L := LocalSig.instruments) i E ℓ k) P Q := by
  intro ρ hρ a
  erw [QuantumRuntime.run₂_queryBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun r ↦ hk r _
    (querySupportedOn_queryStep_imp (decR (X := HashOutput) (Z := HashDomain) m₀) i E ℓ r P
      (P' r) (hstep r) hρ) a

variable (m₀) in
/-- **Every run keeps `NoBot`.** -/
theorem htQN_noBot {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (RSpecN n M) Ω A) :
    HTQN m₀ y {s | NoBot s} fun _ ↦ {s | NoBot s} :=
  fun _ hρ p ↦ querySupportedOn_run (decR (X := HashOutput) (Z := HashDomain) m₀) {s | NoBot s}
    (decR_step_noBot m₀) .instruments y hρ p

theorem HTQ₂N.and_noBot {A B : QReg} {α : Type} {y : QComp (RSpecN n M) A B α}
    {P : Set (RRegN n M)} {Q : α → Set (RRegN n M)} (h : HTQ₂N m₀ y P Q)
    (hP : ∀ s ∈ P, NoBot s) : HTQ₂N m₀ y P fun a ↦ Q a ∩ {s | NoBot s} :=
  fun ρ hρ a ↦ querySupportedOn_inter (h ρ hρ a)
    (htQ₂N_of_htQN (Q := fun _ ↦ {s | NoBot s}) (htQN_noBot m₀ y) ρ (hρ.mono hP) a)

end hoare

/-! ## The ports in the decompressed basis -/

section ports

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset (HPosN n) × M)

/-- **A sponge port keeps the decompressed register.** -/
theorem decR_sponge_suppN (i : SpongePort) (r : (RSpecN n M).Result (.inl (.inl (.inl i))))
    (P : Set (RRegN n M))
    (σ : Matrix ((RSpecN n M).In (.inl (.inl (.inl i))) × RRegN n M)
      ((RSpecN n M).In (.inl (.inl (.inl i))) × RRegN n M) ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpecN n M).In (.inl (.inl (.inl i))) × RRegN n M ↦ m.2)
      P σ) :
    QuerySupportedOn (fun m : (RSpecN n M).Out (.inl (.inl (.inl i))) × RRegN n M ↦ m.2) P
      (((decR (X := HashOutput) (Z := HashDomain) m₀).step (.inl (.inl (.inl i)))).branch r
        σ) := by
  rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inl (.inl i)) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
  cases i <;> (rw [snd_eq_of_hwPort _ m' m hK]; exact hm)

omit [Fintype M] [DecidableEq M] in
/-- The registers after recording `T` from `P` with memory `mem` before. -/
def RecSetQN (P : Set (RRegN n M)) (T : Finset (HPosN n)) (mem : Finset (HPosN n) × M) :
    Set (RRegN n M) :=
  {s | ∃ s₀ ∈ P, s₀.2.2 = mem ∧ s = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ T, s₀.2.2.2))}

/-- **A record of `T` adds `T` to the label** and keeps everything else. -/
theorem decR_rec_suppN (T : Finset (HPosN n)) (mem : (RSpecN n M).Result (.inr T))
    (P : Set (RRegN n M))
    (σ : Matrix ((RSpecN n M).In (.inr T) × RRegN n M) ((RSpecN n M).In (.inr T) × RRegN n M) ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpecN n M).In (.inr T) × RRegN n M ↦ m.2) P σ) :
    QuerySupportedOn (fun m : (RSpecN n M).Out (.inr T) × RRegN n M ↦ m.2) (RecSetQN P T mem)
      (((decR (X := HashOutput) (Z := HashDomain) m₀).step (.inr T)).branch mem σ) := by
  obtain ⟨lab, mm⟩ := mem
  rw [decR_branch_apply m₀ (.inr T) (lab, mm) _ (recStep_branch T (lab, mm))]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
  obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
  exact ⟨m.2, hm, hp, Prod.ext (dbs_one_dec_eq hR) hφ⟩

omit [Fintype M] [DecidableEq M] in
/-- **The effect of hardwiring the `h`-cell `z` to `a`** on the decompressed register: the
hardwired cells updated, no empty cell kept, every other `h` database cell kept. -/
def ProgRelHN (z : HashDomain) (a : HashOutput) (s s' : RRegN n M) : Prop :=
  s'.2 = (progUpdate (.programH z a) s.2.1, s.2.2) ∧ (NoBot s → NoBot s') ∧
    ∀ z', z' ≠ z → s'.1.1 z' = s.1.1 z'

/-- **A program call of an `h`-cell in the decompressed basis** (`ProgRelHN`). -/
theorem decR_progH_suppN (z : HashDomain) (a : HashOutput)
    (r : (RSpecN n M).Result (.inl (.inr (.programH z a)))) (P : Set (RRegN n M))
    (σ : Matrix ((RSpecN n M).In (.inl (.inr (.programH z a))) × RRegN n M)
      ((RSpecN n M).In (.inl (.inr (.programH z a))) × RRegN n M) ℂ)
    (hσ : QuerySupportedOn
      (fun m : (RSpecN n M).In (.inl (.inr (.programH z a))) × RRegN n M ↦ m.2) P σ) :
    QuerySupportedOn (fun m : (RSpecN n M).Out (.inl (.inr (.programH z a))) × RRegN n M ↦ m.2)
      {s' | ∃ s ∈ P, ProgRelHN z a s s'}
      (((decR (X := HashOutput) (Z := HashDomain) m₀).step (.inl (.inr (.programH z a)))).branch
        r σ) := by
  rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inr (.programH z a)) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ⟨m.2, hm, ?_⟩
  obtain ⟨-, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
  rw [show (cellDiscard z r.1 ⊗ₖ (1 : Matrix (Database HashOutput HashDomain ×
    Database HashOutput HashDomain) (Database HashOutput HashDomain ×
      Database HashOutput HashDomain) ℂ)) = cellDiscard z r.1 ⊗ₖ
      ((1 : Matrix (Database HashOutput HashDomain) (Database HashOutput HashDomain) ℂ) ⊗ₖ 1) by
    rw [one_kronecker_one]] at hR
  obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
  obtain ⟨hc, hs⟩ := compressAll_mul_cellDiscard_mul_compressAll_ne_zero h₁
  have e₂ := one_dec_ne_zero h₂
  have e₃ := one_dec_ne_zero h₃
  refine ⟨hφ, fun hnb ↦ ⟨fun z' ↦ ?_, by rw [e₂]; exact hnb.2.1, by rw [e₃]; exact hnb.2.2⟩,
    fun z' hz' ↦ hc z' hz'⟩
  by_cases hz : z' = z
  · subst hz
    exact hs
  · rw [hc z' hz]
    exact hnb.1 z'

omit [Fintype M] [DecidableEq M] in
/-- The register after a read of the `h`-cell `z` updating the inner memory with `upd`: the
databases and hardwired cells kept, the memory updated with the view's cell. -/
def readFinHN (s : RRegN n M) (z : HashDomain) (upd : M → Option HashOutput → M) : RRegN n M :=
  (s.1, s.2.1, (s.2.2.1, upd s.2.2.2 ((hwView s.2.1 s.1).1 z)))

/-- **A read of an `h`-cell in the decompressed basis**: it returns the view's cell with the
memory before, keeps the databases and hardwired cells, and updates the memory. -/
theorem decR_readH_suppN (z : HashDomain) (upd : M → Option HashOutput → M)
    (r : (RSpecN n M).Result (.inl (.inl (.inr (liftRead (.readH z upd))))))
    (U : Set (RRegN n M))
    (σ : Matrix ((RSpecN n M).In (.inl (.inl (.inr (liftRead (.readH z upd))))) × RRegN n M)
      ((RSpecN n M).In (.inl (.inl (.inr (liftRead (.readH z upd))))) × RRegN n M) ℂ)
    (hσ : QuerySupportedOn
      (fun p : (RSpecN n M).In (.inl (.inl (.inr (liftRead (.readH z upd))))) × RRegN n M ↦ p.2)
        U σ) :
    QuerySupportedOn
      (fun p : (RSpecN n M).Out (.inl (.inl (.inr (liftRead (.readH z upd))))) × RRegN n M ↦ p.2)
      {s' | ∃ s ∈ U, r = liftAns s (.readH z upd) ∧ s' = readFinHN s z upd}
      (((decR (X := HashOutput) (Z := HashDomain) m₀).step
        (.inl (.inl (.inr (liftRead (.readH z upd)))))).branch r σ) := by
  rw [decR_branch_apply m₀ (.inl (.inl (.inr (liftRead (.readH z upd))))) r _
    (runtime2_branch m₀ (.inl (.inr (liftRead (.readH z upd)))) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ⟨m.2, hm, ?_⟩
  obtain ⟨o, mm⟩ := r
  obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
  rw [show (cellRead m.2.2.1.1 z o ⊗ₖ (1 : Matrix (Database HashOutput HashDomain ×
    Database HashOutput HashDomain) (Database HashOutput HashDomain ×
      Database HashOutput HashDomain) ℂ)) = cellRead m.2.2.1.1 z o ⊗ₖ
      ((1 : Matrix (Database HashOutput HashDomain) (Database HashOutput HashDomain) ℂ) ⊗ₖ 1) by
    rw [one_kronecker_one]] at hR
  obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
  obtain ⟨e₁, hr⟩ := cellRead_dec_ne_zero h₁
  have hD : m'.2.1 = m.2.1 := Prod.ext e₁ (Prod.ext (one_dec_ne_zero h₂) (one_dec_ne_zero h₃))
  subst hp hr
  exact ⟨rfl, Prod.ext hD hφ⟩

end ports

/-! ## Reveals, program ports, sponge-only steps -/

section template

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset (HPosN n) × M)
  (θ : HPosN n → Digest)

theorem htQN_realizeT_bind {Ω Ω' : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (XSpecN M n) Ω A}
    {g : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (XSpecN M n) Ω' u}
    {P : Set (RRegN n M)} {Q : (Σ u, Ω u) → Set (RRegN n M)} {R : (Σ u, Ω' u) → Set (RRegN n M)}
    (hx : HTQN m₀ (realizeT θ x) P Q) (hg : ∀ u a, HTQN m₀ (realizeT θ (g u a)) (Q ⟨u, a⟩) R) :
    HTQN m₀ (realizeT θ (x.bind g)) P R := by
  rw [realizeT_bind]
  exact HTQN.bind hx hg

theorem htQ₂N_realizeT_bind {A B C : QReg} {α β : Type} {x : QComp (XSpecN M n) A B α}
    {k : α → QComp (XSpecN M n) B C β} {P : Set (RRegN n M)} {Q : α → Set (RRegN n M)}
    {R : β → Set (RRegN n M)} (hx : HTQ₂N m₀ (realizeT θ x) P Q)
    (hk : ∀ a, HTQ₂N m₀ (realizeT θ (k a)) (Q a) R) : HTQ₂N m₀ (realizeT θ (x.bind k)) P R := by
  rw [realizeT_bind₂]
  exact HTQ₂N.bind hx hk

/-- **A realized reveal is the record port**: the values of `θ` on `T`, the label grown by `T`. -/
theorem htQ₂N_revealThen {B C : QReg} {α : Type} (T : Finset (HPosN n))
    (k : RevealVals (HDN n) T × (Finset (HPosN n) × M) → QComp (XSpecN M n) B C α)
    (P : Set (RRegN n M)) (Q : α → Set (RRegN n M))
    (hk : ∀ mem, HTQ₂N m₀ (realizeT θ (k (restrictTo T θ, mem)))
      {s | ∃ s₀ ∈ P, s₀.2.2 = mem ∧ s = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ T, s₀.2.2.2))} Q) :
    HTQ₂N m₀ (realizeT θ (revealThen goodQN T k)) P Q := by
  have e : realizeT θ (revealThen goodQN T k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpecN n M) (.inr T) B
        (Equiv.uniqueProd B Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((RSpecN n M).Out (.inr T) × B)) (B := B)
            (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ (k (restrictTo T θ, mem)) :=
    rfl
  rw [e]
  exact htQ₂N_queryBind (.inr T) B _ (RecSetQN P T)
    (fun mem σ hσ ↦ decR_rec_suppN m₀ T mem P σ hσ) fun mem ↦ htQ₂N_act_bind _ fun _ ↦ hk mem

/-- **A realized program port of user `i`'s structural position** moves the register by
`ProgRelHN`. -/
theorem htQ₂N_progThen {B C : QReg} {α : Type} (i : Fin n) (p : Pos) (hp : p.IsStruct)
    (S0 : MasterSeed) (k : QComp (XSpecN M n) B C α) (P : Set (RRegN n M))
    (Q : α → Set (RRegN n M))
    (hk : HTQ₂N m₀ (realizeT θ k)
      {s' | ∃ s ∈ P, ProgRelHN (cellOf S0 p (tabOf (userOf θ i))) (tabOf (userOf θ i) p) s s'}
      Q) :
    HTQ₂N m₀ (realizeT θ (progThen (progTN i p) trivial k)) P Q := by
  have e : realizeT θ (progThen (progTN i p) trivial k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpecN n M)
        (.inl (.inr ((progTN i p).realize θ))) B (Equiv.uniqueProd B Unit).symm fun _ ↦
          (QComp.act (A := QReg.of ((RSpecN n M).Out (.inl (.inr ((progTN i p).realize θ))) × B))
            (B := B) (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ k :=
    rfl
  rw [e]
  have hr := realize_progTN hp i S0 θ
  revert hk
  generalize (progTN i p).realize θ = c at hr ⊢
  subst hr
  intro hk
  exact htQ₂N_queryBind _ B _ (fun _ ↦ {s' | ∃ s ∈ P, ProgRelHN _ _ s s'})
    (fun r σ hσ ↦ decR_progH_suppN m₀ _ _ r P σ hσ) fun _ ↦ htQ₂N_act_bind _ fun _ ↦ hk

/-- **Sponge-only steps keep every register set**. -/
theorem htQN_sponge {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (spongeSpec HashOutput HashDomain) Ω A)
    (P : Set (RRegN n M)) :
    HTQN m₀ (realizeT θ (readLift goodQN (y.liftOrdinary
      (t := hwReadCmdSpec HashOutput HashDomain M)))) P fun _ ↦ P := by
  induction y using QuantumComp.inductionOn with
  | pure A y => exact htQN_pure y subset_rfl
  | primBind A o k ih =>
    have e : realizeT θ (readLift goodQN ((QuantumComp.primBind o k).liftOrdinary
        (t := hwReadCmdSpec HashOutput HashDomain M))) =
        QuantumComp.primBind o fun b ↦
          realizeT θ (readLift goodQN ((k b).liftOrdinary
            (t := hwReadCmdSpec HashOutput HashDomain M))) :=
      rfl
    rw [e]
    exact htQN_primBind o fun b ↦ ih b
  | queryBind A i E ℓ k ih =>
    have e : realizeT θ (readLift goodQN ((QuantumComp.queryBind i E ℓ k).liftOrdinary
        (t := hwReadCmdSpec HashOutput HashDomain M))) =
        QuantumComp.queryBind (spec := RSpecN n M) (.inl (.inl (.inl i))) E ℓ
          fun r ↦ realizeT θ (readLift goodQN ((k r).liftOrdinary
            (t := hwReadCmdSpec HashOutput HashDomain M))) :=
      rfl
    rw [e]
    exact htQN_queryBind _ E ℓ (fun _ ↦ P) (fun r σ hσ ↦ decR_sponge_suppN m₀ i r P σ hσ)
      fun r ↦ ih r

end template

/-! ## Read programs as functions of the register -/

section det

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset (HPosN n) × M)
  (θ : HPosN n → Digest)

/-- **A read program answers as a function of the register**: from registers without empty cell,
run lifted, realized and in the decompressed basis, it returns `out s` and leaves `fin s`. -/
def DetQN {B : QReg} {α : Type} (y : QComp (hwReadSpec HashOutput HashDomain M) B B α)
    (out : RRegN n M → α) (fin : RRegN n M → RRegN n M) : Prop :=
  ∀ P : Set (RRegN n M), (∀ s ∈ P, NoBot s) →
    HTQ₂N m₀ (realizeT θ (readLiftQ goodQN y)) P fun a ↦ {s' | ∃ s ∈ P, a = out s ∧ s' = fin s}

variable {m₀ θ}

theorem DetQN.congr {B : QReg} {α : Type} {y : QComp (hwReadSpec HashOutput HashDomain M) B B α}
    {out out' : RRegN n M → α} {fin fin' : RRegN n M → RRegN n M} (h : DetQN m₀ θ y out fin)
    (e : ∀ s, NoBot s → out s = out' s ∧ fin s = fin' s) : DetQN m₀ θ y out' fin' := by
  intro P hP
  refine (h P hP).mono subset_rfl fun a ↦ ?_
  rintro s' ⟨s, hs, ha, rfl⟩
  obtain ⟨e₁, e₂⟩ := e s (hP s hs)
  exact ⟨s, hs, ha.trans e₁, e₂⟩

theorem detQN_pure {B : QReg} {α : Type} (a : α) :
    DetQN m₀ θ (QuantumComp₂.pure a : QComp (hwReadSpec HashOutput HashDomain M) B B α)
      (fun _ ↦ a) fun s ↦ s :=
  fun _ _ ↦ htQ₂N_pure a fun s hs ↦ ⟨s, hs, rfl, rfl⟩

theorem DetQN.bind {B : QReg} {α β : Type}
    {x : QComp (hwReadSpec HashOutput HashDomain M) B B α}
    {out : RRegN n M → α} {fin : RRegN n M → RRegN n M} (hx : DetQN m₀ θ x out fin)
    {k : α → QComp (hwReadSpec HashOutput HashDomain M) B B β} {out' : α → RRegN n M → β}
    {fin' : α → RRegN n M → RRegN n M} (hk : ∀ a, DetQN m₀ θ (k a) (out' a) (fin' a)) :
    DetQN m₀ θ (x.bind k) (fun s ↦ out' (out s) (fin s)) fun s ↦ fin' (out s) (fin s) := by
  intro P hP
  rw [readLift_bind₂, realizeT_bind₂]
  refine HTQ₂N.bind ((hx P hP).and_noBot hP) fun a ↦
    ((hk a) _ fun s hs ↦ hs.2).mono subset_rfl fun b ↦ ?_
  rintro s'' ⟨s', ⟨⟨s, hs, rfl, rfl⟩, -⟩, rfl, rfl⟩
  exact ⟨s, hs, rfl, rfl⟩

/-- **A read of an `h`-cell answers the view's cell with the memory and updates the memory.** -/
theorem detQN_readH (z : HashDomain) (upd : M → Option HashOutput → M) (B : QReg) :
    DetQN m₀ θ (readCall (.readH z upd) B) (fun s ↦ ((hwView s.2.1 s.1).1 z, s.2.2.2))
      fun s ↦ readFinHN s z upd := by
  intro P _ ρ hρ a
  rw [realizeT_readLift_readCall]
  erw [QuantumRuntime.run₂_queryBind, DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun r ↦ ?_
  have hq := querySupportedOn_queryStep_imp (decR (X := HashOutput) (Z := HashDomain) m₀)
    (.inl (.inl (.inr (liftRead (.readH z upd))))) B
    (Equiv.uniqueProd B Unit).symm r P
    {s' | ∃ s ∈ P, r = liftAns s (.readH z upd) ∧ s' = readFinHN s z upd}
    (fun τ hτ ↦ decR_readH_suppN m₀ z upd r P τ hτ) hρ
  rw [QuantumRuntime.run₂_act_bind]
  erw [DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun u ↦ ?_
  rw [QuantumRuntime.run₂_pure]
  by_cases ha : a = lowerRes (.readH z upd) r
  · subst ha
    rw [SubInstrument.branch_pure_self, LinearMap.id_apply, DSubInstrument.branch_frame_apply]
    refine (QuerySupportedOn.amplify_snd (q := fun s : RRegN n M ↦ s) hq _).mono ?_
    rintro s' ⟨s, hs, hr, rfl⟩
    exact ⟨s, hs, by rw [hr, lowerRes_liftAns]; rfl, rfl⟩
  · rw [SubInstrument.branch_pure_of_ne ha]
    exact querySupportedOn_zero _ _

end det

/-! ## The randomizer search as a function of the view -/

section grind

/-- **The hash of the register's view**: the hardwired value of a cell, else its database
value (`0` on an empty cell, which the decompressed registers do not have). -/
def hvwN {M : Type} (s : RRegN n M) (z : HashDomain) : HashOutput :=
  ((hwView s.2.1 s.1).1 z).getD 0

theorem hwView_eq_some_hvwN {M : Type} {s : RRegN n M} (hs : NoBot s) (z : HashDomain) :
    (hwView s.2.1 s.1).1 z = some (hvwN s z) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (or_isSome (s.2.1.1 z) (hs.1 z))
  show (s.2.1.1 z).or (s.1.1 z) = some (((s.2.1.1 z).or (s.1.1 z)).getD 0)
  rw [ha]
  rfl

/-- The view of the projected register is the register's view. -/
theorem viewH_unionH_eqN (s : RRegN n (SelMemN n)) :
    viewH (unionH (s.1, s.2.1, s.2.2.2)) = hvwN s :=
  rfl

variable {m₀ : Finset (HPosN n) × SelMemN n} {θ : HPosN n → Digest}

/-- **User `i`'s randomizer search answers the view's selection** and updates user `i`'s memory by
`grindMem`, the other users' memories kept. -/
theorem det_grindTN (i : Fin n) (v : QTable) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (base : Randomizer) (k trial : ℕ) :
    DetQN m₀ θ (grindT (SelMemN n) (cwUpdN i) v.param B l e message base k trial)
      (fun s ↦ v.selectFrom (hvwN s) l e message base k trial)
      (fun s ↦ (s.1, s.2.1, (s.2.2.1, Function.update s.2.2.2 i
        (grindMem (hvwN s) v.param l e message base k trial (s.2.2.2 i))))) := by
  induction k generalizing trial with
  | zero =>
    exact (detQN_pure none).congr fun s _ ↦ ⟨rfl,
      (congrArg (fun m ↦ (s.1, s.2.1, (s.2.2.1, m))) (Function.update_eq_self i s.2.2.2)).symm⟩
  | succ k ih =>
    rw [grindT]
    have aux : ∀ r : Option HashOutput × SelMemN n, DetQN m₀ θ
        (match Codeword.decode (truncateHash (r.1.getD 0)) with
          | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
          | none => grindT (SelMemN n) (cwUpdN i) v.param B l e message base k (trial + 1))
        (fun s ↦ match Codeword.decode (truncateHash (r.1.getD 0)) with
          | some x => some (base + BitVec.ofNat digestBits trial, x)
          | none => v.selectFrom (hvwN s) l e message base k (trial + 1))
        (fun s ↦ match Codeword.decode (truncateHash (r.1.getD 0)) with
          | some _ => s
          | none => (s.1, s.2.1, (s.2.2.1, Function.update s.2.2.2 i
              (grindMem (hvwN s) v.param l e message base k (trial + 1) (s.2.2.2 i))))) := by
      intro r
      rcases Codeword.decode (truncateHash (r.1.getD 0)) with _ | x
      · exact ih (trial + 1)
      · exact detQN_pure _
    refine ((detQN_readH _ _ B).bind aux).congr fun s hs ↦ ⟨?_, ?_⟩
    · simp only [readFinHN, hwView_eq_some_hvwN hs, Option.getD_some, QTable.selectFrom]
      rfl
    · simp only [readFinHN, hwView_eq_some_hvwN hs, Option.getD_some, grindMem]
      rcases Codeword.decode (truncateHash (hvwN s (trialCell v.param l e message base trial)))
        with _ | x
      · simp only [cwUpdN, Function.update_self, Function.update_idem]
        rfl
      · rfl

end grind

/-! ## Programs, searches and publications in the decompressed basis -/

section steps

theorem hvwN_eq {M : Type} {s s' : RRegN n M} (h₁ : s'.1 = s.1) (h₂ : s'.2.1 = s.2.1) :
    hvwN s' = hvwN s := by
  unfold hvwN
  rw [h₁, h₂]

theorem noBot_of_eqN {M : Type} {s s' : RRegN n M} (h₁ : s'.1 = s.1) (hs : NoBot s) :
    NoBot s' := by
  show Quantum.Xmss.Assembly.NoBotDb s'.1
  rw [h₁]
  exact hs

/-- **The summary of program calls of the positions `ps`** of a user with master seed `S0` and
table `v`: no empty cell kept, the inner memory kept, and the hardwired and database `h`-cells
kept off the positions' cells. -/
def ProgsSumN {M : Type} (S0 : MasterSeed) (v : QTable) (ps : List Pos) (s s' : RRegN n M) :
    Prop :=
  (NoBot s → NoBot s') ∧ s'.2.2.2 = s.2.2.2 ∧
    ∀ z, (∀ p ∈ ps, z ≠ cellOf S0 p v) → s'.2.1.1 z = s.2.1.1 z ∧ s'.1.1 z = s.1.1 z

theorem hvwN_of_progsSum {M : Type} {S0 : MasterSeed} {v : QTable} {ps : List Pos}
    {s s' : RRegN n M} (h : ProgsSumN S0 v ps s s') {z : HashDomain}
    (hz : ∀ p ∈ ps, z ≠ cellOf S0 p v) : hvwN s' z = hvwN s z := by
  obtain ⟨h₁, h₂⟩ := h.2.2 z hz
  show ((s'.2.1.1 z).or (s'.1.1 z)).getD 0 = ((s.2.1.1 z).or (s.1.1 z)).getD 0
  rw [h₁, h₂]

/-- Program calls of a user's structural positions keep the view at every user's message-digest
cells. -/
theorem msgAgree_of_progsSumN {M : Type} {S0 : MasterSeed} {v : QTable} {ps : List Pos}
    (hps : ∀ p ∈ ps, p.IsStruct) {s s' : RRegN n M} (h : ProgsSumN S0 v ps s s') (u : QTable) :
    MsgAgree u (hvwN s) (hvwN s') :=
  fun l e d ↦ (hvwN_of_progsSum h fun p hp ↦ cellOf_ne_msg S0 (hps p hp) _ l e d |>.symm).symm

variable (S0 : Fin n → MasterSeed) (w : QTableN n)
variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset (HPosN n) × M)

/-- **Program calls of user `i`'s structural positions** move the register by `ProgsSumN`. -/
theorem htQ₂N_progPos (i : Fin n) (B : QReg) :
    ∀ (ps : List Pos), (∀ p ∈ ps, p.IsStruct) → ∀ P : Set (RRegN n M),
      HTQ₂N m₀ (realizeT (thetaOfN S0 w) (progPosN M i B ps)) P
        fun _ ↦ {s' | ∃ s ∈ P, ProgsSumN (S0 i) (w.user i) ps s s'}
  | [], _, P => htQ₂N_pure () fun s hs ↦ ⟨s, hs, id, rfl, fun _ _ ↦ ⟨rfl, rfl⟩⟩
  | p :: ps, hps, P => by
    refine htQ₂N_progThen m₀ (thetaOfN S0 w) i p (hps p List.mem_cons_self) (S0 i) _ P _
      ((htQ₂N_progPos i B ps (fun q hq ↦ hps q (List.mem_cons_of_mem _ hq)) _).mono subset_rfl
        fun _ ↦ ?_)
    rintro s₂ ⟨s₁, ⟨s, hs, hR⟩, hS⟩
    rw [userOf_thetaOfN, tabOf_thetaOf] at hR
    obtain ⟨hR₁, hR₂, hR₃⟩ := hR
    refine ⟨s, hs, fun hnb ↦ hS.1 (hR₂ hnb), hS.2.1.trans (congrArg (·.2.2) hR₁),
      fun z hz ↦ ?_⟩
    have hz₀ : z ≠ cellOf (S0 i) p (w.user i) := hz p List.mem_cons_self
    obtain ⟨e₁, e₂⟩ := hS.2.2 z fun q hq ↦ hz q (List.mem_cons_of_mem _ hq)
    refine ⟨e₁.trans ?_, e₂.trans (hR₃ z hz₀)⟩
    rw [show s₁.2.1 = progUpdate (.programH (cellOf (S0 i) p (w.user i)) (w.user i p)) s.2.1 from
      congrArg Prod.fst hR₁]
    exact Function.update_of_ne hz₀ _ _

variable {m₀ : Finset (HPosN n) × SelMemN n}

/-- **User `i`'s search in the decompressed basis**: the view's selection, user `i`'s memory
updated by `grindMem`, databases and hardwired cells kept. -/
theorem htQ₂_selectTN (i : Fin n) {P : PublicParameter} (hP : P = (w.user i).param) (B : QReg)
    (l : Layer) (e : KeyIndex) (msg : MsgBytes) (rnd : Pos) (U : Set (RRegN n (SelMemN n)))
    (hU : ∀ s ∈ U, NoBot s) :
    HTQ₂N m₀ (realizeT (thetaOfN S0 w) (selectTN (SelMemN n) cwUpdN i P B l e msg rnd)) U
      fun g ↦ {s' | ∃ s ∈ U, g = (w.user i).select (hvwN s) l e msg (truncateHash (w.user i rnd)) ∧
        s'.1 = s.1 ∧ s'.2.1 = s.2.1 ∧
        s'.2.2.2 = Function.update s.2.2.2 i (grindMem (hvwN s) (w.user i).param l e msg
          (truncateHash (w.user i rnd)) randomizerAttemptLimit 0 (s.2.2.2 i))} := by
  subst hP
  rw [selectTN]
  refine htQ₂N_revealThen m₀ (thetaOfN S0 w) _ _ U _ fun mem ↦ ?_
  have hb : truncateHash (tabRN (restrictTo (atU i {loC rnd}) (thetaOfN S0 w)) i rnd) =
      truncateHash (w.user i rnd) :=
    (baseOfN_eq (thetaOfN S0 w) i rnd).trans (by rw [userOf_thetaOfN, tabOf_thetaOf])
  dsimp only
  rw [hb]
  refine ((det_grindTN (m₀ := m₀) (θ := thetaOfN S0 w) i (w.user i) B l e msg
    (truncateHash (w.user i rnd)) randomizerAttemptLimit 0) _ ?_).mono subset_rfl fun g ↦ ?_
  · rintro s ⟨s₀, hs₀, -, rfl⟩
    exact hU s₀ hs₀
  · rintro s' ⟨s, ⟨s₀, hs₀, -, rfl⟩, rfl, rfl⟩
    exact ⟨s₀, hs₀, rfl, rfl, rfl, rfl⟩

/-- **Publishing user `i`'s layer signature in the decompressed basis**: the table's layer
signature, the register moved by the program calls of its positions. -/
theorem htQ₂_publishTN (i : Fin n) (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) (U : Set (RRegN n (SelMemN n))) :
    HTQ₂N m₀ (realizeT (thetaOfN S0 w) (publishTN (SelMemN n) i B l e ρ x)) U
      fun sig ↦ {s' | ∃ s ∈ U, sig = layerSigOf (w.user i) l e ρ x ∧
        ProgsSumN (S0 i) (w.user i) (layerPos l e x) s s'} := by
  rw [publishTN]
  refine htQ₂N_revealThen m₀ (thetaOfN S0 w) _ _ U _ fun mem ↦ ?_
  refine htQ₂N_realizeT_bind m₀ (thetaOfN S0 w)
    (htQ₂N_progPos S0 w m₀ i B _ (fun p hp ↦ isStruct_of_mem_layerPos hp) _) fun _ ↦
      htQ₂N_pure _ ?_
  rintro s₂ ⟨s₁, ⟨s, hs, -, rfl⟩, hS⟩
  refine ⟨s, hs, ?_, hS.1, hS.2.1, hS.2.2⟩
  have h := layerOutN_eq (thetaOfN S0 w) i l e ρ x
  rw [userOf_thetaOfN, tabOf_thetaOf] at h
  exact h

/-- A request's top selection is its top key's. -/
theorem topSelOf_eq_layerSel (v : QTable) (H : HashDomain → HashOutput) (r : SigningRequest) :
    topSelOf v H (topKeyOf r) = layerSel v H r topLayer := by
  rw [topSelOf_eq, layerSel, layerMsg_top, layerBase_top]
  rfl

theorem topSelOf_congr {v : QTable} {H H' : HashDomain → HashOutput} (h : MsgAgree v H H')
    (t : KeyIndex) : topSelOf v H t = topSelOf v H' t :=
  select_congr h _ _ _ _

/-- **User `j`'s top layer's search without a memoized selection**: the bottom root revealed,
then the view's top selection, user `j`'s memory updated by `grindMem`. -/
theorem htQ₂_topTN_none (j : Fin n) {P : PublicParameter} (hP : P = (w.user j).param)
    (B : QReg) (r : SigningRequest) (U : Set (RRegN n (SelMemN n))) (hU : ∀ s ∈ U, NoBot s) :
    HTQ₂N m₀ (realizeT (thetaOfN S0 w) (topTN (SelMemN n) cwUpdN j P B r none)) U
      fun gt ↦ {s' | ∃ s ∈ U, s'.1 = s.1 ∧ s'.2.1 = s.2.1 ∧
        gt = layerSel (w.user j) (hvwN s) r topLayer ∧
        s'.2.2.2 = Function.update s.2.2.2 j (grindMem (hvwN s) (w.user j).param topLayer
          (keyIndexOnLayer r.leafIndex topLayer) (layerMsg (w.user j) r topLayer)
          (layerBase (w.user j) r topLayer) randomizerAttemptLimit 0 (s.2.2.2 j))} := by
  rw [topTN]
  refine htQ₂N_revealThen m₀ _ _ _ _ _ fun mem ↦ ?_
  dsimp only
  rw [show (tabRN (restrictTo (atU j (rootReveal r)) (thetaOfN S0 w)) j).bottomRoot r.leafIndex =
    (w.user j).bottomRoot r.leafIndex from
      (rootOfN_eq _ j r).trans (by rw [userOf_thetaOfN, tabOf_thetaOf])]
  refine (htQ₂_selectTN S0 w j hP B _ _ _ _ _ ?_).mono subset_rfl fun gt ↦ ?_
  · rintro s₁ ⟨s, hs, -, rfl⟩
    exact hU s hs
  · rintro s₂ ⟨s₁, ⟨s, hs, -, rfl⟩, hgt, h21, h22, hm2⟩
    refine ⟨s, hs, h21, h22, ?_, ?_⟩
    · rw [hgt, layerSel, layerMsg_top, layerBase_top]
      rfl
    · rw [hm2, layerMsg_top, layerBase_top]
      rfl

/-- **A memo hit makes no call**: the memoized selection, the register unchanged. -/
theorem htQ₂_topTN_some (j : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (o : TopSel) (U : Set (RRegN n (SelMemN n))) :
    HTQ₂N m₀ (realizeT (thetaOfN S0 w) (topTN (SelMemN n) cwUpdN j P B r (some o))) U
      fun gt ↦ {s' | gt = o ∧ s' ∈ U} :=
  htQ₂N_pure o fun _ hs ↦ ⟨rfl, hs⟩

end steps

/-! ## The invariant of the challenge prefix -/

section inv

/-- User `i`'s transcript after a request of user `j`. -/
theorem userN_append (log : MuSignLog n SigningRequest (Option Signature)) (j : Fin n)
    (r : SigningRequest) (b : Option Signature) (i : Fin n) :
    SufCma.Multi.MuSignLog.user (log ++ [⟨(j, r), b⟩]) i =
      SufCma.Multi.MuSignLog.user log i ++ if j = i then [⟨r, b⟩] else [] :=
  SufCma.Multi.MuSignLog.user_append_singleton log j r b i

theorem userN_append_self (log : MuSignLog n SigningRequest (Option Signature)) (j : Fin n)
    (r : SigningRequest) (b : Option Signature) :
    SufCma.Multi.MuSignLog.user (log ++ [⟨(j, r), b⟩]) j =
      SufCma.Multi.MuSignLog.user log j ++ [⟨r, b⟩] := by
  rw [userN_append, ite_eq_left rfl]

theorem userN_append_of_ne (log : MuSignLog n SigningRequest (Option Signature)) {j i : Fin n}
    (r : SigningRequest) (b : Option Signature) (h : j ≠ i) :
    SufCma.Multi.MuSignLog.user (log ++ [⟨(j, r), b⟩]) i = SufCma.Multi.MuSignLog.user log i := by
  rw [userN_append, ite_eq_right h, List.append_nil]

theorem mem_userN_append_left {log : MuSignLog n SigningRequest (Option Signature)} {j i : Fin n}
    {r : SigningRequest} {b : Option Signature} {q : (_ : SigningRequest) × Option Signature}
    (hq : q ∈ SufCma.Multi.MuSignLog.user log i) :
    q ∈ SufCma.Multi.MuSignLog.user (log ++ [⟨(j, r), b⟩]) i := by
  rw [userN_append]
  exact List.mem_append_left _ hq

theorem mem_userN_append_self (log : MuSignLog n SigningRequest (Option Signature)) (j : Fin n)
    (r : SigningRequest) (b : Option Signature) :
    (⟨r, b⟩ : (_ : SigningRequest) × Option Signature) ∈
      SufCma.Multi.MuSignLog.user (log ++ [⟨(j, r), b⟩]) j := by
  rw [userN_append_self]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem mem_userN_append {log : MuSignLog n SigningRequest (Option Signature)} {j i : Fin n}
    {r : SigningRequest} {b : Option Signature} {q : (_ : SigningRequest) × Option Signature}
    (hq : q ∈ SufCma.Multi.MuSignLog.user (log ++ [⟨(j, r), b⟩]) i) :
    q ∈ SufCma.Multi.MuSignLog.user log i ∨ (j = i ∧ q = ⟨r, b⟩) := by
  rw [userN_append] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact .inl hq
  · split_ifs at hq with hji
    · exact .inr ⟨hji, List.mem_singleton.mp hq⟩
    · exact absurd hq List.not_mem_nil

/-- User `j`'s memory after the bottom layer's search of a request against `H`. -/
def botMemN (v : QTable) (H : HashDomain → HashOutput) (r : SigningRequest) (m : SelMem) :
    SelMem :=
  grindMem H v.param bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)
    (layerMsg v r bottomLayer)
    (layerBase v r bottomLayer) randomizerAttemptLimit 0 m

/-- **User `j`'s memory after a signature** against `H` with the memoized top selection `h`: the
bottom layer's search, then the top layer's search unless the memo hits. -/
def sigMemN (v : QTable) (H : HashDomain → HashOutput) (r : SigningRequest) :
    Option TopSel → SelMem → SelMem
  | none, m => grindMem H v.param topLayer (keyIndexOnLayer r.leafIndex topLayer)
      (layerMsg v r topLayer) (layerBase v r topLayer) randomizerAttemptLimit 0 (botMemN v H r m)
  | some _, m => botMemN v H r m

section sigMem

variable (v : QTable) (H : HashDomain → HashOutput) (r : SigningRequest)

theorem botMemN_top (m : SelMem) :
    botMemN v H r m topLayer (keyIndexOnLayer r.leafIndex topLayer) =
      m topLayer (keyIndexOnLayer r.leafIndex topLayer) :=
  grindMem_of_ne _ _ _ _ _ _ (fun h ↦ absurd h.1 (by decide)) _ _ _

theorem sigMemN_bottom (h : Option TopSel) (m : SelMem) :
    sigMemN v H r h m bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) =
      botMemN v H r m bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) := by
  cases h with
  | none => exact grindMem_of_ne _ _ _ _ _ _ (fun h ↦ absurd h.1 (by decide)) _ _ _
  | some _ => rfl

theorem sigMemN_of_ne {l : Layer} {e : KeyIndex}
    (hk : ¬((l = bottomLayer ∧ e = keyIndexOnLayer r.leafIndex bottomLayer) ∨
      (l = topLayer ∧ e = keyIndexOnLayer r.leafIndex topLayer))) (h : Option TopSel)
    (m : SelMem) : sigMemN v H r h m l e = m l e := by
  have hb : botMemN v H r m l e = m l e :=
    grindMem_of_ne _ _ _ _ _ _ (fun h ↦ hk (.inl h)) _ _ _
  cases h with
  | none => exact (grindMem_of_ne _ _ _ _ _ _ (fun h ↦ hk (.inr h)) _ _ _).trans hb
  | some _ => exact hb

theorem sigMemN_of_ne_none {l : Layer} {e : KeyIndex} (h : Option TopSel) (m : SelMem)
    (hne : m l e ≠ none) : sigMemN v H r h m l e = m l e := by
  have hb : botMemN v H r m l e = m l e := grindMem_of_ne_none _ _ _ _ _ _ _ _ _ hne
  cases h with
  | none => exact (grindMem_of_ne_none _ _ _ _ _ _ _ _ _ (by rwa [hb])).trans hb
  | some _ => exact hb

end sigMem

variable (S0 : Fin n → MasterSeed) (w : QTableN n)

/-- **Hardwired cells come from published signatures**: every hardwired `h`-cell is the cell of a
position of a user `i` that a request of `i`'s transcript with both selections publishes. -/
def HwFromN (log : MuSignLog n SigningRequest (Option Signature)) (s : RRegN n (SelMemN n)) :
    Prop :=
  ∀ z, (s.2.1.1 z).isSome → ∃ i, ∃ q ∈ log.user i, ∃ selB selT,
    layerSel (w.user i) (hvwN s) q.1 bottomLayer = some selB ∧
    layerSel (w.user i) (hvwN s) q.1 topLayer = some selT ∧
    ∃ l, ∃ p ∈ layerPos l (keyIndexOnLayer q.1.leafIndex l)
      (if l = bottomLayer then selB.2 else selT.2), z = cellOf (S0 i) p (w.user i)

/-- **Selected keys were requested**, per user. -/
def MemFromN (log : MuSignLog n SigningRequest (Option Signature)) (s : RRegN n (SelMemN n)) :
    Prop :=
  ∀ i l e, s.2.2.2 i l e ≠ none → ∃ q ∈ log.user i, keyIndexOnLayer q.1.leafIndex l = e

/-- **The memo agrees with the view and holds only requested top keys.** -/
def MemoOKN (log : MuSignLog n SigningRequest (Option Signature)) (T : SelMemo n)
    (s : RRegN n (SelMemN n)) : Prop :=
  ∀ i t o, T i t = some o → o = topSelOf (w.user i) (hvwN s) t ∧ ∃ q ∈ log.user i, topKeyOf q.1 = t

/-- **The invariant along the challenge prefix** with all users' transcript `log` and the memo
`T`, in the decompressed basis: no empty cell, each user's transcript's signatures are the user's
table's against the view, hardwired cells from published signatures, selected keys requested,
without leaf reuse in a user's transcript that user's memory records its selections, and the memo
agrees with the view. -/
def InvQN (log : MuSignLog n SigningRequest (Option Signature)) (T : SelMemo n) :
    Set (RRegN n (SelMemN n)) :=
  {s | NoBot s ∧ (∀ i, ∀ q ∈ log.user i, q.2 = (w.user i).signature (hvwN s) q.1) ∧
    HwFromN S0 w log s ∧ MemFromN log s ∧
    (∀ i, SigningTranscript.NoLeafIndexReused (log.user i) →
      ∀ q ∈ log.user i, Records (w.user i) (hvwN s) (s.2.2.2 i) q.1) ∧
    MemoOKN w log T s}

/-- **One signature of user `j` keeps the invariant**, from the classical effect of `signTN` with
the memoized selection `h` of the request's top key on the decompressed register. -/
theorem invQN_step {log : MuSignLog n SigningRequest (Option Signature)} {T : SelMemo n}
    {j : Fin n} {r : SigningRequest} {h : Option TopSel} (hh : T j (topKeyOf r) = h)
    {s s' : RRegN n (SelMemN n)} {sig : Option Signature} {gt : TopSel}
    (hs : s ∈ InvQN S0 w log T) (hnb : NoBot s')
    (hH : ∀ i, MsgAgree (w.user i) (hvwN s) (hvwN s'))
    (hsig : sig = (w.user j).signature (hvwN s) r)
    (hgt : gt = layerSel (w.user j) (hvwN s) r topLayer)
    (hmem : s'.2.2.2 = Function.update s.2.2.2 j (sigMemN (w.user j) (hvwN s) r h (s.2.2.2 j)))
    (hW : ∀ z, (s'.2.1.1 z).isSome → (s.2.1.1 z).isSome ∨ ∃ selB selT,
      layerSel (w.user j) (hvwN s) r bottomLayer = some selB ∧
      layerSel (w.user j) (hvwN s) r topLayer = some selT ∧
      ∃ l, ∃ p ∈ layerPos l (keyIndexOnLayer r.leafIndex l)
        (if l = bottomLayer then selB.2 else selT.2), z = cellOf (S0 j) p (w.user j)) :
    s' ∈ InvQN S0 w (log ++ [⟨(j, r), sig⟩]) (T.put j (topKeyOf r) gt) := by
  obtain ⟨-, hsigs, hhw, hmf, hrec, hmemo⟩ := hs
  have hsel : ∀ i q l, layerSel (w.user i) (hvwN s) q l = layerSel (w.user i) (hvwN s') q l :=
    fun i _ _ ↦ select_congr (hH i) _ _ _ _
  have hmj : s'.2.2.2 j = sigMemN (w.user j) (hvwN s) r h (s.2.2.2 j) := by
    rw [hmem, Function.update_self]
  have hmi : ∀ i, i ≠ j → s'.2.2.2 i = s.2.2.2 i := fun i hi ↦ by
    rw [hmem, Function.update_of_ne hi]
  refine ⟨hnb, ?_, ?_, ?_, ?_, ?_⟩
  · intro i q hq
    rcases mem_userN_append hq with hq | ⟨rfl, rfl⟩
    · rw [hsigs i q hq, signature_congr (hH i)]
    · exact hsig.trans (signature_congr (hH _) r)
  · intro z hz
    rcases hW z hz with hz₀ | ⟨selB, selT, hB, hT, hp⟩
    · obtain ⟨i, q, hq, selB, selT, hB, hT, hp⟩ := hhw z hz₀
      exact ⟨i, q, mem_userN_append_left hq, selB, selT, (hsel _ _ _).symm.trans hB,
        (hsel _ _ _).symm.trans hT, hp⟩
    · exact ⟨j, ⟨r, sig⟩, mem_userN_append_self log j r sig, selB, selT,
        (hsel _ _ _).symm.trans hB, (hsel _ _ _).symm.trans hT, hp⟩
  · intro i l e hle
    by_cases hij : i = j
    · subst hij
      by_cases hk : (l = bottomLayer ∧ e = keyIndexOnLayer r.leafIndex bottomLayer) ∨
          (l = topLayer ∧ e = keyIndexOnLayer r.leafIndex topLayer)
      · refine ⟨⟨r, sig⟩, mem_userN_append_self _ _ _ _, ?_⟩
        rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
      · rw [hmj, sigMemN_of_ne _ _ _ hk] at hle
        obtain ⟨q, hq, hqk⟩ := hmf i l e hle
        exact ⟨q, mem_userN_append_left hq, hqk⟩
    · rw [hmi i hij] at hle
      obtain ⟨q, hq, hqk⟩ := hmf i l e hle
      exact ⟨q, mem_userN_append_left hq, hqk⟩
  · intro i hnr q hq
    rw [← records_congr (hH i)]
    by_cases hij : i = j
    · subst hij
      rw [userN_append_self] at hnr hq
      have hnr₀ : SigningTranscript.NoLeafIndexReused (log.user i) := by
        unfold SigningTranscript.NoLeafIndexReused at hnr ⊢
        rw [List.map_append] at hnr
        exact (List.nodup_append.mp hnr).1
      rw [hmj]
      rcases List.mem_append.mp hq with hq | hq
      · intro l sel hls
        have h0 := hrec i hnr₀ q hq l sel hls
        have hne : s.2.2.2 i l (keyIndexOnLayer q.1.leafIndex l) ≠ none := by
          rw [h0]
          exact Option.some_ne_none _
        rw [sigMemN_of_ne_none _ _ _ _ _ hne, h0]
      · obtain rfl := List.mem_singleton.mp hq
        intro l sel hls
        rcases layer_cases l with rfl | rfl
        · have hnone : s.2.2.2 i bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) = none := by
            by_contra hne
            obtain ⟨q', hq', hqk⟩ := hmf _ _ _ hne
            exact Quantum.Xmss.not_noLeafIndexReused_append
              (by rw [← leafIndex_eq_of_bottom hqk]; exact List.mem_map_of_mem hq') sig hnr
          rw [sigMemN_bottom]
          exact grindMem_of_select _ _ _ _ _ (w.user i) _ _ _ hnone hls
        · have hold : ∀ q' ∈ log.user i,
              keyIndexOnLayer q'.1.leafIndex topLayer = keyIndexOnLayer r.leafIndex topLayer →
              s.2.2.2 i topLayer (keyIndexOnLayer r.leafIndex topLayer) =
                some (cell (w.user i).param (.msg topLayer (keyIndexOnLayer r.leafIndex topLayer))
                  (layerMsg (w.user i) r topLayer, sel.1),
                  (w.user i).messageDigest (hvwN s) topLayer
                    (keyIndexOnLayer r.leafIndex topLayer) (layerMsg (w.user i) r topLayer)
                    sel.1) := by
            intro q' hq' hqk
            have hls' : layerSel (w.user i) (hvwN s) q'.1 topLayer = some sel :=
              (layerSel_top_eq hqk).trans hls
            have h0 := hrec i hnr₀ q' hq' topLayer sel hls'
            rw [hqk, layerMsg_top_eq hqk] at h0
            exact h0
          have hb := botMemN_top (w.user i) (hvwN s) r (s.2.2.2 i)
          cases h with
          | none =>
            show grindMem (hvwN s) (w.user i).param topLayer (keyIndexOnLayer r.leafIndex topLayer)
              (layerMsg (w.user i) r topLayer) (layerBase (w.user i) r topLayer)
              randomizerAttemptLimit 0 (botMemN (w.user i) (hvwN s) r (s.2.2.2 i)) topLayer
              (keyIndexOnLayer r.leafIndex topLayer) = _
            rcases hm : s.2.2.2 i topLayer (keyIndexOnLayer r.leafIndex topLayer) with _ | c
            · rw [hm] at hb
              exact grindMem_of_select _ _ _ _ _ (w.user i) _ _ _ hb hls
            · obtain ⟨q', hq', hqk⟩ := hmf _ _ _ (by rw [hm]; exact Option.some_ne_none c)
              have h0 := hold q' hq' hqk
              rw [hm] at hb
              rw [grindMem_of_some _ _ _ _ _ _ _ _ _ hb, ← hm, h0]
          | some o =>
            obtain ⟨-, q', hq', hqk⟩ := hmemo i _ o hh
            show botMemN (w.user i) (hvwN s) r (s.2.2.2 i) topLayer
              (keyIndexOnLayer r.leafIndex topLayer) = _
            rw [hb]
            exact hold q' hq' hqk
    · rw [userN_append_of_ne _ _ _ (Ne.symm hij)] at hnr hq
      rw [hmi i hij]
      exact hrec i hnr q hq
  · intro i t o ho
    by_cases hit : i = j ∧ t = topKeyOf r
    · obtain ⟨rfl, rfl⟩ := hit
      rw [SelMemo.put_self] at ho
      obtain rfl := Option.some.inj ho
      refine ⟨?_, ⟨r, sig⟩, mem_userN_append_self _ _ _ _, rfl⟩
      rw [hgt, ← topSelOf_eq_layerSel]
      exact topSelOf_congr (hH _) _
    · rw [SelMemo.put_of_ne _ _ hit] at ho
      obtain ⟨ho, q, hq, hqt⟩ := hmemo i t o ho
      exact ⟨ho.trans (topSelOf_congr (hH i) t), q, mem_userN_append_left hq, hqt⟩

/-- **Hardwired chain cells of user `i` have known inputs**, from `HwFromN` on a good table: a
hardwired cell of user `i`'s chain was programmed by user `i`. -/
theorem hwKnown_of_hwFromN (hw : (tableN S0).good w)
    {log : MuSignLog n SigningRequest (Option Signature)} {s : RRegN n (SelMemN n)}
    (h : HwFromN S0 w log s) (i : Fin n) :
    HwKnown (S0 i) (w.user i) (hvwN s) (projU i (s.1, s.2.1, s.2.2.2))
      ((log.user i).map Sigma.fst) := by
  intro l e c step hz
  obtain ⟨j, q, hq, selB, selT, hB, hT, l', p, hp, hzp⟩ := h _ hz
  have hij : ((i, .chain l e c step) : PosN n) = (j, p) := hw.1 hzp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
  obtain ⟨rfl, rfl, hle⟩ := chain_mem_layerPos hp
  have hB' : (w.user i).select (hvwN s) bottomLayer (keyIndexOnLayer q.1.leafIndex bottomLayer)
      (messageBytes q.1.message) ((w.user i).bottomBase q.1) = some selB := by
    rw [← layerMsg_bottom, ← layerBase_bottom]
    exact hB
  have hT' : (w.user i).select (hvwN s) topLayer (keyIndexOnLayer q.1.leafIndex topLayer)
      (rootBytes ((w.user i).bottomRoot q.1.leafIndex)) ((w.user i).topBase q.1) = some selT := by
    rw [← layerMsg_top, ← layerBase_top]
    exact hT
  set x := if l = bottomLayer then selB.2 else selT.2 with hx
  have hd : Quantum.Xmss.Pos.chain l (keyIndexOnLayer q.1.leafIndex l) c (x c).val ∈
      (w.user i).disclosures (hvwN s) ((log.user i).map Sigma.fst) := by
    refine Or.inr (Set.mem_biUnion (List.mem_map_of_mem hq) ?_)
    simp only [QTable.disclosedBy, hB', hT']
    rcases layer_cases l with rfl | rfl
    · exact Or.inl (Or.inl ⟨c, by rw [hx, ite_eq_left rfl]⟩)
    · exact Or.inr (Or.inl ⟨c, by rw [hx, ite_eq_right (by decide)]⟩)
  have hk := known_chain_le (Known.disclosed _ hd) (step.val - (x c).val) (by
    have := step.isLt
    omega)
  rwa [Nat.add_sub_cancel' hle] at hk

end inv

/-! ## The signer keeps the invariant -/

section sign

variable (S0 : Fin n → MasterSeed) (w : QTableN n) {m₀ : Finset (HPosN n) × SelMemN n}

/-- The registers after user `j`'s two searches (or the bottom search and the memo hit `h`) of
a request `r`, from the invariant, with selections `gb`, `gt`. -/
def MidN (log : MuSignLog n SigningRequest (Option Signature)) (T : SelMemo n) (j : Fin n)
    (r : SigningRequest) (h : Option TopSel) (gb gt : TopSel) : Set (RRegN n (SelMemN n)) :=
  {s₃ | ∃ s ∈ InvQN S0 w log T, s₃.1 = s.1 ∧ s₃.2.1 = s.2.1 ∧
    gb = layerSel (w.user j) (hvwN s) r bottomLayer ∧
    gt = layerSel (w.user j) (hvwN s) r topLayer ∧
    s₃.2.2.2 = Function.update s.2.2.2 j (sigMemN (w.user j) (hvwN s) r h (s.2.2.2 j))}

/-- **The publications of a signature keep the invariant** from `MidN`. -/
theorem htQ₂_pubN (j : Fin n) (B : QReg) (r : SigningRequest)
    (log : MuSignLog n SigningRequest (Option Signature)) (T : SelMemo n) {h : Option TopSel}
    (hh : T j (topKeyOf r) = h) (gb gt : TopSel) :
    HTQ₂N m₀ (realizeT (thetaOfN S0 w) (pubBothN (publishTN (SelMemN n) j B) r gb gt))
      (MidN S0 w log T j r h gb gt)
      fun sig ↦ InvQN S0 w (log ++ [⟨(j, r), sig⟩]) (T.put j (topKeyOf r) gt) := by
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  rotate_left 3
  · rw [pubBothN]
    refine htQ₂N_realizeT_bind m₀ _ (htQ₂_publishTN S0 w j B _ _ _ _ _) fun sb ↦ ?_
    refine htQ₂N_realizeT_bind m₀ _ (htQ₂_publishTN S0 w j B _ _ _ _ _) fun st ↦ ?_
    refine htQ₂N_pure _ ?_
    rintro s₅ ⟨s₄, ⟨s₃, hs₃, rfl, hS4⟩, rfl, hS5⟩
    obtain ⟨s, hs, h31, h32, hgb, hgt, hm3⟩ := hs₃
    have e3 : hvwN s₃ = hvwN s := hvwN_eq h31 h32
    have hps : ∀ l e x, ∀ p ∈ layerPos l e x, p.IsStruct := fun _ _ _ _ hp ↦
      isStruct_of_mem_layerPos hp
    refine invQN_step S0 w hh hs (hS5.1 (hS4.1 (noBot_of_eqN h31 hs.1))) ?_ ?_ hgt ?_ ?_
    · intro i
      rw [← e3]
      exact (msgAgree_of_progsSumN (hps _ _ _) hS4 _).trans
        (msgAgree_of_progsSumN (hps _ _ _) hS5 _)
    · simp only [QTable.signature, QTable.bottomSignature, QTable.topSignature,
        QTable.layerSignature]
      rw [show (w.user j).select (hvwN s) bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)
          (messageBytes r.message) ((w.user j).bottomBase r) = some (ρb, xb) from by
        rw [hgb, layerSel, layerMsg_bottom, layerBase_bottom],
        show (w.user j).select (hvwN s) topLayer (keyIndexOnLayer r.leafIndex topLayer)
          (rootBytes ((w.user j).bottomRoot r.leafIndex)) ((w.user j).topBase r) = some (ρt, xt)
          from by rw [hgt, layerSel, layerMsg_top, layerBase_top]]
      rfl
    · rw [hS5.2.1, hS4.2.1, hm3]
    · intro z hz
      by_cases hzT : ∃ p ∈ layerPos topLayer (keyIndexOnLayer r.leafIndex topLayer) xt,
          z = cellOf (S0 j) p (w.user j)
      · exact .inr ⟨(ρb, xb), (ρt, xt), hgb.symm, hgt.symm, topLayer, by
          rw [ite_eq_right (by decide)]
          exact hzT⟩
      · by_cases hzB : ∃ p ∈ layerPos bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) xb,
            z = cellOf (S0 j) p (w.user j)
        · exact .inr ⟨(ρb, xb), (ρt, xt), hgb.symm, hgt.symm, bottomLayer, by
            rw [ite_eq_left rfl]
            exact hzB⟩
        · refine .inl ?_
          rw [← h32, ← (hS4.2.2 z fun p hp hzp ↦ hzB ⟨p, hp, hzp⟩).1,
            ← (hS5.2.2 z fun p hp hzp ↦ hzT ⟨p, hp, hzp⟩).1]
          exact hz
  all_goals
    refine htQ₂N_pure _ ?_
    intro s₃ hs₃
    obtain ⟨s, hs, h31, h32, hgb, hgt, hm3⟩ := hs₃
    refine invQN_step S0 w hh hs (noBot_of_eqN h31 hs.1) ?_ ?_ hgt hm3
      fun z hz ↦ .inl (by rwa [h32] at hz)
    · intro i
      rw [hvwN_eq h31 h32]
      exact fun _ _ _ ↦ rfl
    · simp only [QTable.signature, QTable.bottomSignature, QTable.topSignature,
        QTable.layerSignature]
      rw [show (w.user j).select (hvwN s) bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)
          (messageBytes r.message) ((w.user j).bottomBase r) =
            layerSel (w.user j) (hvwN s) r bottomLayer from by
          rw [layerSel, layerMsg_bottom, layerBase_bottom],
        show (w.user j).select (hvwN s) topLayer (keyIndexOnLayer r.leafIndex topLayer)
          (rootBytes ((w.user j).bottomRoot r.leafIndex)) ((w.user j).topBase r) =
            layerSel (w.user j) (hvwN s) r topLayer
          from by rw [layerSel, layerMsg_top, layerBase_top], ← hgb, ← hgt]
      rfl

/-- **A signature of user `j` keeps the invariant `InvQN`** in the decompressed basis: the request
and its answer appended to the transcript, the answer's top selection memoized. -/
theorem htQ₂_signTN (j : Fin n) {P : PublicParameter} (hP : P = (w.user j).param) (B : QReg)
    (r : SigningRequest) (log : MuSignLog n SigningRequest (Option Signature)) (T : SelMemo n) :
    HTQ₂N m₀ (realizeT (thetaOfN S0 w)
      (signTN (SelMemN n) cwUpdN j P B r (T j (topKeyOf r)))) (InvQN S0 w log T)
      fun a ↦ InvQN S0 w (log ++ [⟨(j, r), a.1⟩]) (T.put j (topKeyOf r) a.2) := by
  generalize hh : T j (topKeyOf r) = h
  rw [signTN, signWithN]
  refine htQ₂N_realizeT_bind m₀ _ (htQ₂_selectTN S0 w j hP B _ _ _ _ _ fun s hs ↦ hs.1)
    fun gb ↦ ?_
  refine htQ₂N_realizeT_bind m₀ _ (Q := MidN S0 w log T j r h gb) ?_ fun gt ↦ ?_
  · cases h with
    | none =>
      refine (htQ₂_topTN_none S0 w j hP B r _ ?_).mono subset_rfl fun gt ↦ ?_
      · rintro s₁ ⟨s, hs, -, h11, -, -⟩
        exact noBot_of_eqN h11 hs.1
      · rintro s₂ ⟨s₁, ⟨s, hs, hgb, h11, h12, hm1⟩, h21, h22, hgt, hm2⟩
        rw [hvwN_eq h11 h12] at hgt hm2
        refine ⟨s, hs, h21.trans h11, h22.trans h12, ?_, hgt, ?_⟩
        · rw [hgb, layerSel, layerMsg_bottom, layerBase_bottom]
          rfl
        · rw [hm2, hm1, Function.update_self, Function.update_idem, sigMemN, botMemN,
            layerMsg_bottom, layerBase_bottom]
          rfl
    | some o =>
      refine (htQ₂_topTN_some S0 w j P B r o _).mono subset_rfl fun gt ↦ ?_
      rintro s₁ ⟨rfl, s, hs, hgb, h11, h12, hm1⟩
      refine ⟨s, hs, h11, h12, ?_, ?_, ?_⟩
      · rw [hgb, layerSel, layerMsg_bottom, layerBase_bottom]
        rfl
      · rw [(hs.2.2.2.2.2 j _ _ hh).1, topSelOf_eq_layerSel]
      · rw [hm1, sigMemN, botMemN, layerMsg_bottom, layerBase_bottom]
        rfl
  · rw [QuantumComp₂.map_eq_bind_pure]
    exact htQ₂N_realizeT_bind m₀ _ (htQ₂_pubN S0 w j B r log T hh gb gt) fun sig ↦
      htQ₂N_pure _ subset_rfl

end sign

/-! ## The challenge prefix -/

section prefixRun

variable {m₀ : Finset (HPosN n) × SelMemN n}

/-- **The adversary's memo transform with all users' transcript**: sponge-only steps keep
`Inv log T`, a signing request of user `j` moves it to the extended transcript and memo. -/
theorem htQ_logSignsN (θ : HPosN n → Digest) (P : Fin n → PublicParameter)
    (Inv : MuSignLog n SigningRequest (Option Signature) → SelMemo n →
      Set (RRegN n (SelMemN n)))
    (hsign : ∀ (B : QReg) (j : Fin n) (r : SigningRequest)
      (log : MuSignLog n SigningRequest (Option Signature)) (T : SelMemo n),
      HTQ₂N m₀ (realizeT θ (signTN (SelMemN n) cwUpdN j (P j) B r (T j (topKeyOf r))))
        (Inv log T) fun a ↦ Inv (log ++ [⟨(j, r), a.1⟩]) (T.put j (topKeyOf r) a.2))
    {Ω Y : QReg → Type} (leaf : ∀ u, Ω u → MuSignLog n SigningRequest (Option Signature) → Y u)
    (Q : (Σ u, Y u) → Set (RRegN n (SelMemN n)))
    (hleaf : ∀ u y log T, Inv log T ⊆ Q ⟨u, leaf u y log⟩) {A : QReg}
    (x : IFreeM (MuP n) Ω A) (log : MuSignLog n SigningRequest (Option Signature))
    (T : SelMemo n) :
    HTQN m₀ ((memoFrom T (muLogSigns leaf x log)).substitute fun A c ↦
      realizeT θ (challengeTN (SelMemN n) cwUpdN P A c)) (Inv log T) Q := by
  induction x using IFreeM.inductionOn generalizing log T with
  | pure u y => exact htQN_pure (leaf u y log) (hleaf u y log T)
  | liftBind s c next ih =>
    rcases c with o | ⟨_ | ⟨j, r⟩, E, ℓ⟩
    · refine HTQN.bind
        (x := realizeT θ (challengeTN (SelMemN n) cwUpdN P s (QuantumComp.Cmd.prim o)))
        (Q := fun _ ↦ Inv log T) (htQN_sponge m₀ θ _ (Inv log T)) fun u ans ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b log T
    · refine HTQN.bind (x := realizeT θ (challengeTN (SelMemN n) cwUpdN P s
        (QuantumComp.Cmd.query MuPort.hash E ℓ)))
        (Q := fun _ ↦ Inv log T) (htQN_sponge m₀ θ _ (Inv log T)) fun u ans ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b log T
    · refine HTQN.bind (x := realizeT θ (challengeTN (SelMemN n) cwUpdN P s
        (QuantumComp.Cmd.query (MuPort.sign j (r, T j (topKeyOf r))) E ℓ)))
        (Q := fun p ↦ Inv (log ++ [⟨(j, r), p.2.1.down.1⟩]) (T.put j (topKeyOf r) p.2.1.down.2))
        ?_ fun u ans ↦ ?_
      · have hs : HTQ₂N m₀ (realizeT θ (signAtN j (r, T j (topKeyOf r)) E ℓ fun B ↦
            signTN (SelMemN n) cwUpdN j (P j) B r (T j (topKeyOf r))))
            (Inv log T) fun a ↦ Inv (log ++ [⟨(j, r), a.1⟩]) (T.put j (topKeyOf r) a.2) :=
          htQ₂N_realizeT_bind m₀ θ (htQ₂N_act _ _) fun _ ↦ hsign _ j r log T
        exact htQN_realizeT_bind m₀ θ (htQN_of_htQ₂N hs) fun _ l ↦ htQN_pure _ subset_rfl
      · obtain ⟨b, hb⟩ := ans
        subst hb
        exact ih (ULift.up b.down.1) _ _

/-- **The challenge prefix**: all users' public keys revealed, then the adversary's memo transform
against the challenger with all users' transcript, moving `Inv log T` along the transcript and
the memo; it returns the revealed public keys. -/
theorem htQ₂_prefixTN (θ : HPosN n → Digest) (A : MuAdversary n)
    (Inv : MuSignLog n SigningRequest (Option Signature) → SelMemo n →
      Set (RRegN n (SelMemN n)))
    (hsign : ∀ (B : QReg) (j : Fin n) (r : SigningRequest)
      (log : MuSignLog n SigningRequest (Option Signature)) (T : SelMemo n),
      HTQ₂N m₀ (realizeT θ (signTN (SelMemN n) cwUpdN j (pkDN θ j).parameter B r
        (T j (topKeyOf r)))) (Inv log T)
        fun a ↦ Inv (log ++ [⟨(j, r), a.1⟩]) (T.put j (topKeyOf r) a.2))
    (P₀ : Set (RRegN n (SelMemN n)))
    (hroot : ∀ s ∈ P₀, (s.1, s.2.1, (s.2.2.1 ∪ pkRevealN, s.2.2.2)) ∈ Inv [] fun _ _ ↦ none) :
    HTQ₂N m₀ (realizeT θ (prefixTN (SelMemN n) cwUpdN A)) P₀
      (fun pre ↦ {s | (∃ T, s ∈ Inv pre.2.2 T) ∧ pre.1 = pkDN θ}) := by
  unfold prefixTN
  refine htQ₂N_revealThen m₀ θ _ _ P₀ _ fun mem ↦ ?_
  refine htQ₂N_realizeT_bind m₀ θ (Q := fun run : MuRun n ↦ {s | ∃ T, s ∈ Inv run.2 T}) ?_
    fun run ↦ htQ₂N_pure _ fun s hs ↦ ⟨hs, rfl⟩
  refine htQ₂N_of_htQN (HTQN.mono (P := Inv [] fun _ _ ↦ none) ?_ ?_ fun _ ↦ subset_rfl)
  · have e := realizeT_substitute (good := goodQN) (M := SelMemN n) θ
      (challengeTN (SelMemN n) cwUpdN fun i ↦ (pkDN θ i).parameter)
      (memoFrom (fun _ _ ↦ none) (withMuSignLog (A (pkDN θ))))
    refine (congrArg (fun y ↦ HTQN m₀ y (Inv [] fun _ _ ↦ none)
      fun p ↦ {s | ∃ T, s ∈ Inv p.2.2.2 T}) e).mpr ?_
    exact htQ_logSignsN θ _ Inv hsign _
      (fun q : (Σ u, QuantumComp₂.Leaf (QReg.of Unit)
        ((Fin n × Forgery) × MuSignLog n SigningRequest (Option Signature)) u) ↦
          {s | ∃ T, s ∈ Inv q.2.2.2 T})
      (fun _ _ _ T _ hs ↦ ⟨T, hs⟩) _ [] _
  · rintro s ⟨s₀, hs₀, -, rfl⟩
    exact hroot s₀ hs₀

/-- **The initial operator in the decompressed basis**: no empty cell, no hardwired cell, memory
`m₀`. -/
theorem init_decQN (m₀ : Finset (HPosN n) × SelMemN n) :
    QuerySupportedOn (fun p : Unit × RRegN n (SelMemN n) ↦ p.2)
      {s | NoBot s ∧ s.2 = (hwEmpty HashOutput HashDomain, m₀)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset (HPosN n) × SelMemN n)) (initU m₀)) := by
  have h0 : QuerySupportedOn (fun p : Unit × RRegN n (SelMemN n) ↦ p.2)
      {s | s.2 = (hwEmpty HashOutput HashDomain, m₀)} (initU m₀) := by
    intro m m' hm
    change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
      Database.empty), hwEmpty HashOutput HashDomain, m₀) : RRegN n (SelMemN n))).matrix) m m' ≠ 0
      at hm
    simp only [SubState.matrix_basis] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · exact ⟨congrArg Prod.snd he.1.symm, congrArg Prod.snd he.2.symm⟩
    · exact absurd rfl h
  exact querySupportedOn_inter (noBot_init m₀ (A := Unit) (SubState.basis ()).matrix)
    (querySupportedOn_conj_compressReg (P := fun b ↦ b = (hwEmpty HashOutput HashDomain, m₀)) h0)

variable (S0 : Fin n → MasterSeed) (w : QTableN n)

/-- **The facts of a prefix outcome `pre`** on a register `s` (`win_imp_badQN`'s hypotheses per
user `i` on the projected register `(s.1, s.2.1, s.2.2.2)`, with `H` its view): the public keys
are the table's, no empty cell, and per user `i`: `i`'s transcript's signatures are the table's,
without leaf reuse in `i`'s transcript `i`'s memory records its selections, and every hardwired
chain cell of `i` has a known input. -/
def PreFactsQN (pre : (Fin n → PublicKey) × MuRun n) (s : RRegN n (SelMemN n)) : Prop :=
  (∀ i, pre.1 i = (w.user i).publicKey) ∧ NoBot s ∧
    ∀ i, (∀ q ∈ pre.2.2.user i,
        q.2 = (w.user i).signature (viewH (unionH (s.1, s.2.1, s.2.2.2))) q.1) ∧
      (SigningTranscript.NoLeafIndexReused (pre.2.2.user i) → ∀ q ∈ pre.2.2.user i,
        Records (w.user i) (viewH (unionH (s.1, s.2.1, s.2.2.2))) (s.2.2.2 i) q.1) ∧
      HwKnown (S0 i) (w.user i) (viewH (unionH (s.1, s.2.1, s.2.2.2)))
        (projU i (s.1, s.2.1, s.2.2.2)) ((pre.2.2.user i).map Sigma.fst)

/-- **The call invariants of the canonical prefix**: for a good table `w`, on every branch of the
challenge prefix `prefixQN A (thetaOfN S0 w)` run against `runtimeR m₀` from a memory with no
selection, in the decompressed basis, the register is supported where `PreFactsQN` holds. -/
theorem prefixFactsQN (hw : (tableN S0).good w) (A : MuAdversary n)
    (m₀ : Finset (HPosN n) × SelMemN n) (hm₀ : m₀.2 = fun _ _ _ ↦ none)
    (pre : (Fin n → PublicKey) × MuRun n) :
    QuerySupportedOn (fun p : Unit × RRegN n (SelMemN n) ↦ p.2) {s | PreFactsQN S0 w pre s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset (HPosN n) × SelMemN n))
        (((runtimeR m₀).run₂ .instruments (prefixQN A (thetaOfN S0 w))).branch pre
          (initU m₀))) := by
  rw [Quantum.Xmss.Assembly.conj_branch₂ m₀ (prefixQN A (thetaOfN S0 w)) pre (initU m₀)]
  have hpk : ∀ i, pkDN (thetaOfN S0 w) i = (w.user i).publicKey := fun i ↦ by
    rw [pkDN_eq, userOf_thetaOfN, tabOf_thetaOf]
  have H := htQ₂_prefixTN (m₀ := m₀) (thetaOfN S0 w) A (InvQN S0 w)
    (fun B j r log T ↦ htQ₂_signTN S0 w j (by rw [hpk]; rfl) B r log T)
    {s | NoBot s ∧ s.2 = (hwEmpty HashOutput HashDomain, m₀)} fun s hs ↦ by
      obtain ⟨hnb, hs2⟩ := hs
      refine ⟨hnb, fun i q hq ↦ absurd hq (by simp), fun z hz ↦ ?_, fun i l e hle ↦ ?_,
        fun i _ q hq ↦ absurd hq (by simp), fun i t o ho ↦ absurd ho (by simp)⟩
      · rw [show s.2.1 = hwEmpty HashOutput HashDomain from congrArg Prod.fst hs2] at hz
        exact absurd hz (by simp [hwEmpty, Database.empty])
      · rw [show s.2.2.2 = m₀.2 from congrArg (·.2.2) hs2, hm₀] at hle
        exact absurd rfl hle
  refine (H _ (init_decQN m₀) pre).mono ?_
  rintro s ⟨⟨T, hinv⟩, hpre⟩
  exact ⟨fun i ↦ by rw [hpre, hpk], hinv.1, fun i ↦ ⟨hinv.2.1 i, hinv.2.2.2.2.1 i,
    hwKnown_of_hwFromN S0 w hw hinv.2.2.1 i⟩⟩

end prefixRun

end Quantum.Qrom.Xmss.Multi

end
