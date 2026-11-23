module

public import Quantum.Qrom.Sphincs.GameTFactsPre
public import Quantum.Qrom.Sphincs.Multi.Template
public import Quantum.Qrom.Sphincs.Multi.Classify

@[expose] public section

/-!
# The canonical multi-user runtime-2 game of leanSPHINCS, in the decompressed basis

The `n`-user analog of the support semantics, the counter search and the signer of
`Quantum.Qrom.Sphincs.GameTFacts`, at the register `RRegSN n M`.

* `muGameQSN`, `prefixQSN`, `m0SN`: the canonical game (trial reads record codeword selections in
  user `i`'s memory, `cwUpdN i`), its challenge prefix and the initial memory.
* Support semantics (`HTQSN`, `HTQ₂SN`), the ports in the decompressed basis, reveals, program
  ports, sponge-only steps, read programs as functions of the register (`DetQSN`).
* `det_grindSN`: user `i`'s counter search answers the view's selection and records it in user
  `i`'s memory (`grindMemS`), the other users' memories kept.
* User `j`'s steps (`StepRelSN`, `htQ₂SN_selOrMemoS`: a memo hit makes no call) and signature
  (`SignEffN`, `htQ₂SN_signS`); no table cell is an encoding cell of any user
  (`cellOf_ne_encCellSN`).
-/

open Matrix IPFunctor
open scoped Kronecker
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Hybrid (LazyProg restrictTo progUpdate runtime2_branch)
open Quantum.Xmss.Assembly (recHwSpec realizeT revealThen progThen readLift readLiftQ RevealVals
  runtimeR NoBot initU noBot_init querySupportedOn_conj_compressReg querySupportedOn_inter decR
  decR_branch_apply decR_step_noBot recStep_branch querySupportedOn_run
  querySupportedOn_queryStep_imp clsKraus_dec_ne_zero dbs_dec_ne_zero cellRead_dec_ne_zero
  one_dec_ne_zero compressAll_mul_cellDiscard_mul_compressAll_ne_zero snd_eq_of_hwPort
  dbs_one_dec_eq liftAns lowerRes lowerRes_liftAns realizeT_readLift_readCall realizeT_bind
  realizeT_bind₂ readLift_bind₂ realizeT_substitute or_isSome liftRead)

attribute [local irreducible] sphincsRom

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

/-- The register of runtime 2 with record ports at the memory `Finset (TPosN n) × M`. -/
abbrev RRegSN (n : ℕ) (M : Type) : Type :=
  HwReg PairOut HashDomain (Finset (TPosN n) × M)

/-- The signature of runtime 2 with record ports at the memory `Finset (TPosN n) × M`. -/
abbrev RSpecSN (n : ℕ) (M : Type) : QuantumOracleSpec.{0, 0} :=
  recHwSpec PairOut HashDomain (TPosN n) M

/-! ## The canonical game -/

/-- **The canonical multi-user runtime-2 game** at the users' policies `pols` and the hidden
values `θ`: the trials' reads record codeword selections in user `i`'s memory (`cwUpdN i`). -/
noncomputable def muGameQSN (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (θ : TValsN n) :
    QComp (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)) (QReg.of Unit) (QReg.of Unit)
      Bool :=
  realizeT θ (muGameT (SelMemN n) cwUpdN pols valid A)

/-- The canonical challenge prefix at `θ`. -/
noncomputable def prefixQSN (pols : Fin n → DigestPolicy) (A : MuAdversaryS n) (θ : TValsN n) :
    QComp (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)) (QReg.of Unit) (QReg.of Unit)
      ((Fin n → PublicKey) × MuRunS n) :=
  realizeT θ (prefixTN (SelMemN n) cwUpdN pols A)

/-- The initial memory: no coordinate recorded, no selection. -/
def m0SN : Finset (TPosN n) × SelMemN n :=
  (∅, fun _ _ ↦ none)

/-! ## Support semantics in the decompressed basis -/

section hoare

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset (TPosN n) × M)

/-- **Support semantics of a program in the decompressed basis**: from an operator supported on
registers in `P`, the branch at every leaf `p` is supported on `Q p`. -/
def HTQSN {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (RSpecSN n M) Ω A)
    (P : Set (RRegSN n M)) (Q : (Σ u, Ω u) → Set (RRegSN n M)) : Prop :=
  ∀ ρ : Matrix (A × RRegSN n M) (A × RRegSN n M) ℂ,
    QuerySupportedOn (fun m : A × RRegSN n M ↦ m.2) P ρ →
    ∀ p, QuerySupportedOn (fun m : p.1 × RRegSN n M ↦ m.2) (Q p)
      (((decR (X := PairOut) (Z := HashDomain) m₀).run .instruments y).branch p ρ)

/-- `HTQSN` for programs on a fixed final register. -/
def HTQ₂SN {A B : QReg} {α : Type} (y : QComp (RSpecSN n M) A B α) (P : Set (RRegSN n M))
    (Q : α → Set (RRegSN n M)) : Prop :=
  ∀ ρ : Matrix (A × RRegSN n M) (A × RRegSN n M) ℂ,
    QuerySupportedOn (fun m : A × RRegSN n M ↦ m.2) P ρ →
    ∀ a, QuerySupportedOn (fun m : B × RRegSN n M ↦ m.2) (Q a)
      (((decR (X := PairOut) (Z := HashDomain) m₀).run₂ .instruments y).branch a ρ)

variable {m₀}

theorem HTQSN.mono {Ω : QReg → Type} {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (RSpecSN n M) Ω A}
    {P P' : Set (RRegSN n M)} {Q Q' : (Σ u, Ω u) → Set (RRegSN n M)} (h : HTQSN m₀ y P Q)
    (hP : P' ⊆ P) (hQ : ∀ p, Q p ⊆ Q' p) : HTQSN m₀ y P' Q' :=
  fun ρ hρ p ↦ (h ρ (hρ.mono hP) p).mono (hQ p)

theorem HTQ₂SN.mono {A B : QReg} {α : Type} {y : QComp (RSpecSN n M) A B α}
    {P P' : Set (RRegSN n M)} {Q Q' : α → Set (RRegSN n M)} (h : HTQ₂SN m₀ y P Q)
    (hP : P' ⊆ P) (hQ : ∀ a, Q a ⊆ Q' a) : HTQ₂SN m₀ y P' Q' :=
  fun ρ hρ a ↦ (h ρ (hρ.mono hP) a).mono (hQ a)

theorem htQ₂SN_iff {A B : QReg} {α : Type} (y : QComp (RSpecSN n M) A B α)
    (P : Set (RRegSN n M)) (Q : α → Set (RRegSN n M)) :
    HTQ₂SN m₀ y P Q ↔ HTQSN m₀ y P fun p ↦ Q p.2.2 := by
  constructor
  · intro h ρ hρ p
    obtain ⟨u, hu, a⟩ := p
    subst hu
    exact h ρ hρ a
  · intro h ρ hρ a
    exact h ρ hρ ⟨B, rfl, a⟩

theorem htQSN_of_htQ₂SN {A B : QReg} {α : Type} {y : QComp (RSpecSN n M) A B α}
    {P : Set (RRegSN n M)} {Q : α → Set (RRegSN n M)} (h : HTQ₂SN m₀ y P Q) :
    HTQSN m₀ y P fun p ↦ Q p.2.2 :=
  (htQ₂SN_iff y P Q).mp h

theorem htQ₂SN_of_htQSN {A B : QReg} {α : Type} {y : QComp (RSpecSN n M) A B α}
    {P : Set (RRegSN n M)} {Q : α → Set (RRegSN n M)} (h : HTQSN m₀ y P fun p ↦ Q p.2.2) :
    HTQ₂SN m₀ y P Q :=
  (htQ₂SN_iff y P Q).mpr h

theorem htQSN_pure {Ω : QReg → Type} {A : QReg} (y : Ω A) {P : Set (RRegSN n M)}
    {Q : (Σ u, Ω u) → Set (RRegSN n M)} (h : P ⊆ Q ⟨A, y⟩) :
    HTQSN m₀ (QuantumComp.pure (L := LocalSig.instruments.{0}) (spec := RSpecSN n M) y) P Q := by
  classical
  intro ρ hρ p
  rw [QuantumRuntime.run_pure]
  by_cases hp : p = ⟨A, y⟩
  · subst hp
    rw [DSubInstrument.branch_ret_self]
    exact hρ.mono h
  · rw [DSubInstrument.branch_ret_of_ne _ hp]
    exact querySupportedOn_zero _ _

theorem htQ₂SN_pure {A : QReg} {α : Type} (a : α) {P : Set (RRegSN n M)}
    {Q : α → Set (RRegSN n M)} (h : P ⊆ Q a) :
    HTQ₂SN m₀ (QuantumComp₂.pure a : QComp (RSpecSN n M) A A α) P Q := by
  intro ρ hρ a'
  rw [QuantumRuntime.run₂_pure]
  by_cases ha : a' = a
  · subst ha
    rw [SubInstrument.branch_pure_self]
    exact hρ.mono h
  · rw [SubInstrument.branch_pure_of_ne ha]
    exact querySupportedOn_zero _ _

theorem HTQSN.bind {Ω Ω' : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (RSpecSN n M) Ω A}
    {P : Set (RRegSN n M)} {Q : (Σ u, Ω u) → Set (RRegSN n M)} (hx : HTQSN m₀ x P Q)
    {k : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (RSpecSN n M) Ω' u}
    {R : (Σ u, Ω' u) → Set (RRegSN n M)} (hk : ∀ u a, HTQSN m₀ (k u a) (Q ⟨u, a⟩) R) :
    HTQSN m₀ (x.bind k) P R := by
  intro ρ hρ p
  rw [QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun q ↦ hk q.1 q.2 _ (hx ρ hρ q) p

theorem HTQ₂SN.bind {A B C : QReg} {α β : Type} {x : QComp (RSpecSN n M) A B α}
    {P : Set (RRegSN n M)} {Q : α → Set (RRegSN n M)} (hx : HTQ₂SN m₀ x P Q)
    {k : α → QComp (RSpecSN n M) B C β} {R : β → Set (RRegSN n M)}
    (hk : ∀ a, HTQ₂SN m₀ (k a) (Q a) R) : HTQ₂SN m₀ (x.bind k) P R := by
  intro ρ hρ b
  erw [QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun a ↦ hk a _ (hx ρ hρ a) b

theorem htQSN_primBind {Ω : QReg → Type} {A : QReg} (o : LocalSig.instruments.{0}.Op A)
    {k : (b : LocalSig.instruments.{0}.Outcome o) →
      QuantumComp LocalSig.instruments.{0} (RSpecSN n M) Ω (LocalSig.instruments.{0}.next o b)}
    {P : Set (RRegSN n M)} {Q : (Σ u, Ω u) → Set (RRegSN n M)} (hk : ∀ b, HTQSN m₀ (k b) P Q) :
    HTQSN m₀ (QuantumComp.primBind o k) P Q := by
  intro ρ hρ p
  rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun b ↦ hk b _ (QuerySupportedOn.amplify_snd (q := id) hρ _) p

/-- **A local operation keeps the register.** -/
theorem htQ₂SN_act_bind {A B C : QReg} {α β : Type} (p : SubInstrument A B β)
    {k : β → QComp (RSpecSN n M) B C α} {P : Set (RRegSN n M)} {Q : α → Set (RRegSN n M)}
    (hk : ∀ b, HTQ₂SN m₀ (k b) P Q) : HTQ₂SN m₀ ((QComp.act p).bind k) P Q := by
  intro ρ hρ a
  rw [QuantumRuntime.run₂_act_bind]
  erw [DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun b ↦ hk b _ (QuerySupportedOn.amplify_snd (q := id) hρ _) a

theorem htQ₂SN_act {A B : QReg} {β : Type} (p : SubInstrument A B β) (P : Set (RRegSN n M)) :
    HTQ₂SN m₀ (QComp.act (spec := RSpecSN n M) p) P fun _ ↦ P := by
  rw [← QuantumComp₂.bind_pure (QComp.act (spec := RSpecSN n M) p)]
  exact htQ₂SN_act_bind p fun b ↦ htQ₂SN_pure b subset_rfl

/-- A call whose step moves the support from `P` to `P' r` at the result `r`. -/
theorem htQSN_queryBind {Ω : QReg → Type} {A : QReg} (i : (RSpecSN n M).Port)
    (E : QReg) (ℓ : A ≃ (RSpecSN n M).In i × E)
    {k : (RSpecSN n M).Result i →
      QuantumComp LocalSig.instruments.{0} (RSpecSN n M) Ω (QReg.of ((RSpecSN n M).Out i × E))}
    {P : Set (RRegSN n M)} (P' : (RSpecSN n M).Result i → Set (RRegSN n M))
    {Q : (Σ u, Ω u) → Set (RRegSN n M)}
    (hstep : ∀ r (σ : Matrix ((RSpecSN n M).In i × RRegSN n M)
        ((RSpecSN n M).In i × RRegSN n M) ℂ),
      QuerySupportedOn (fun m : (RSpecSN n M).In i × RRegSN n M ↦ m.2) P σ →
        QuerySupportedOn (fun m : (RSpecSN n M).Out i × RRegSN n M ↦ m.2) (P' r)
          (((decR (X := PairOut) (Z := HashDomain) m₀).step i).branch r σ))
    (hk : ∀ r, HTQSN m₀ (k r) (P' r) Q) : HTQSN m₀ (QuantumComp.queryBind i E ℓ k) P Q := by
  intro ρ hρ p
  rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun r ↦ hk r _
    (querySupportedOn_queryStep_imp (decR (X := PairOut) (Z := HashDomain) m₀) i E ℓ r P
      (P' r) (hstep r) hρ) p

theorem htQ₂SN_queryBind {A B : QReg} {α : Type} (i : (RSpecSN n M).Port)
    (E : QReg) (ℓ : A ≃ (RSpecSN n M).In i × E)
    {k : (RSpecSN n M).Result i → QComp (RSpecSN n M) (QReg.of ((RSpecSN n M).Out i × E)) B α}
    {P : Set (RRegSN n M)} (P' : (RSpecSN n M).Result i → Set (RRegSN n M))
    {Q : α → Set (RRegSN n M)}
    (hstep : ∀ r (σ : Matrix ((RSpecSN n M).In i × RRegSN n M)
        ((RSpecSN n M).In i × RRegSN n M) ℂ),
      QuerySupportedOn (fun m : (RSpecSN n M).In i × RRegSN n M ↦ m.2) P σ →
        QuerySupportedOn (fun m : (RSpecSN n M).Out i × RRegSN n M ↦ m.2) (P' r)
          (((decR (X := PairOut) (Z := HashDomain) m₀).step i).branch r σ))
    (hk : ∀ r, HTQ₂SN m₀ (k r) (P' r) Q) :
    HTQ₂SN m₀ (QuantumComp₂.queryBind (L := LocalSig.instruments) i E ℓ k) P Q := by
  intro ρ hρ a
  erw [QuantumRuntime.run₂_queryBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun r ↦ hk r _
    (querySupportedOn_queryStep_imp (decR (X := PairOut) (Z := HashDomain) m₀) i E ℓ r P
      (P' r) (hstep r) hρ) a

variable (m₀) in
/-- **Every run keeps `NoBot`.** -/
theorem htQSN_noBot {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (RSpecSN n M) Ω A) :
    HTQSN m₀ y {s | NoBot s} fun _ ↦ {s | NoBot s} :=
  fun _ hρ p ↦ querySupportedOn_run (decR (X := PairOut) (Z := HashDomain) m₀)
    {s | NoBot s} (decR_step_noBot m₀) .instruments y hρ p

theorem HTQ₂SN.and_noBot {A B : QReg} {α : Type} {y : QComp (RSpecSN n M) A B α}
    {P : Set (RRegSN n M)} {Q : α → Set (RRegSN n M)} (h : HTQ₂SN m₀ y P Q)
    (hP : ∀ s ∈ P, NoBot s) : HTQ₂SN m₀ y P fun a ↦ Q a ∩ {s | NoBot s} :=
  fun ρ hρ a ↦ querySupportedOn_inter (h ρ hρ a)
    (htQ₂SN_of_htQSN (Q := fun _ ↦ {s | NoBot s}) (htQSN_noBot m₀ y) ρ (hρ.mono hP) a)

end hoare

/-! ## The ports in the decompressed basis -/

section ports

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset (TPosN n) × M)

/-- **A sponge port keeps the decompressed register.** -/
theorem decR_sponge_suppSN (i : SpongePort) (r : (RSpecSN n M).Result (.inl (.inl (.inl i))))
    (P : Set (RRegSN n M))
    (σ : Matrix ((RSpecSN n M).In (.inl (.inl (.inl i))) × RRegSN n M)
      ((RSpecSN n M).In (.inl (.inl (.inl i))) × RRegSN n M) ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpecSN n M).In (.inl (.inl (.inl i))) × RRegSN n M ↦ m.2)
      P σ) :
    QuerySupportedOn (fun m : (RSpecSN n M).Out (.inl (.inl (.inl i))) × RRegSN n M ↦ m.2) P
      (((decR (X := PairOut) (Z := HashDomain) m₀).step (.inl (.inl (.inl i)))).branch r
        σ) := by
  rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inl (.inl i)) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
  cases i <;> (rw [snd_eq_of_hwPort _ m' m hK]; exact hm)

omit [Fintype M] [DecidableEq M] in
/-- The registers after recording `T` from `P` with memory `mem` before. -/
def RecSetQSN (P : Set (RRegSN n M)) (T : Finset (TPosN n)) (mem : Finset (TPosN n) × M) :
    Set (RRegSN n M) :=
  {s | ∃ s₀ ∈ P, s₀.2.2 = mem ∧ s = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ T, s₀.2.2.2))}

/-- **A record of `T` adds `T` to the label** and keeps everything else. -/
theorem decR_rec_suppSN (T : Finset (TPosN n)) (mem : (RSpecSN n M).Result (.inr T))
    (P : Set (RRegSN n M))
    (σ : Matrix ((RSpecSN n M).In (.inr T) × RRegSN n M) ((RSpecSN n M).In (.inr T) × RRegSN n M)
      ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpecSN n M).In (.inr T) × RRegSN n M ↦ m.2) P σ) :
    QuerySupportedOn (fun m : (RSpecSN n M).Out (.inr T) × RRegSN n M ↦ m.2) (RecSetQSN P T mem)
      (((decR (X := PairOut) (Z := HashDomain) m₀).step (.inr T)).branch mem σ) := by
  obtain ⟨lab, mm⟩ := mem
  rw [decR_branch_apply m₀ (.inr T) (lab, mm) _ (recStep_branch T (lab, mm))]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
  obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
  exact ⟨m.2, hm, hp, Prod.ext (dbs_one_dec_eq hR) hφ⟩

omit [Fintype M] [DecidableEq M] in
/-- **The effect of hardwiring the `h`-cell `z` to `a`** on the decompressed register: the
hardwired cells updated, no empty cell kept, every other `h` database cell kept. -/
def ProgRelHSN (z : HashDomain) (a : PairOut) (s s' : RRegSN n M) : Prop :=
  s'.2 = (progUpdate (.programH z a) s.2.1, s.2.2) ∧ (NoBot s → NoBot s') ∧
    ∀ z', z' ≠ z → s'.1.1 z' = s.1.1 z'

/-- **A program call of an `h`-cell in the decompressed basis** (`ProgRelHSN`). -/
theorem decR_progH_suppSN (z : HashDomain) (a : PairOut)
    (r : (RSpecSN n M).Result (.inl (.inr (.programH z a)))) (P : Set (RRegSN n M))
    (σ : Matrix ((RSpecSN n M).In (.inl (.inr (.programH z a))) × RRegSN n M)
      ((RSpecSN n M).In (.inl (.inr (.programH z a))) × RRegSN n M) ℂ)
    (hσ : QuerySupportedOn
      (fun m : (RSpecSN n M).In (.inl (.inr (.programH z a))) × RRegSN n M ↦ m.2) P σ) :
    QuerySupportedOn (fun m : (RSpecSN n M).Out (.inl (.inr (.programH z a))) × RRegSN n M ↦ m.2)
      {s' | ∃ s ∈ P, ProgRelHSN z a s s'}
      (((decR (X := PairOut) (Z := HashDomain) m₀).step
        (.inl (.inr (.programH z a)))).branch r σ) := by
  rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inr (.programH z a)) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ⟨m.2, hm, ?_⟩
  obtain ⟨-, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
  rw [show (cellDiscard z r.1 ⊗ₖ (1 : Matrix (Database PairOut HashDomain ×
    Database PairOut HashDomain) (Database PairOut HashDomain ×
      Database PairOut HashDomain) ℂ)) = cellDiscard z r.1 ⊗ₖ
      ((1 : Matrix (Database PairOut HashDomain) (Database PairOut HashDomain) ℂ) ⊗ₖ
        1) by rw [one_kronecker_one]] at hR
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
/-- The register after a read of the `h`-cell `z` updating the inner memory with `upd`. -/
def readFinHSN (s : RRegSN n M) (z : HashDomain) (upd : M → Option PairOut → M) : RRegSN n M :=
  (s.1, s.2.1, (s.2.2.1, upd s.2.2.2 ((hwView s.2.1 s.1).1 z)))

/-- **A read of an `h`-cell in the decompressed basis**: it returns the view's cell with the
memory before, keeps the databases and hardwired cells, and updates the memory. -/
theorem decR_readH_suppSN (z : HashDomain) (upd : M → Option PairOut → M)
    (r : (RSpecSN n M).Result (.inl (.inl (.inr (liftRead (.readH z upd))))))
    (U : Set (RRegSN n M))
    (σ : Matrix ((RSpecSN n M).In (.inl (.inl (.inr (liftRead (.readH z upd))))) × RRegSN n M)
      ((RSpecSN n M).In (.inl (.inl (.inr (liftRead (.readH z upd))))) × RRegSN n M) ℂ)
    (hσ : QuerySupportedOn
      (fun p : (RSpecSN n M).In (.inl (.inl (.inr (liftRead (.readH z upd))))) × RRegSN n M ↦
        p.2) U σ) :
    QuerySupportedOn
      (fun p : (RSpecSN n M).Out (.inl (.inl (.inr (liftRead (.readH z upd))))) × RRegSN n M ↦
        p.2)
      {s' | ∃ s ∈ U, r = liftAns s (.readH z upd) ∧ s' = readFinHSN s z upd}
      (((decR (X := PairOut) (Z := HashDomain) m₀).step
        (.inl (.inl (.inr (liftRead (.readH z upd)))))).branch r σ) := by
  rw [decR_branch_apply m₀ (.inl (.inl (.inr (liftRead (.readH z upd))))) r _
    (runtime2_branch m₀ (.inl (.inr (liftRead (.readH z upd)))) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ⟨m.2, hm, ?_⟩
  obtain ⟨o, mm⟩ := r
  obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
  rw [show (cellRead m.2.2.1.1 z o ⊗ₖ (1 : Matrix (Database PairOut HashDomain ×
    Database PairOut HashDomain) (Database PairOut HashDomain ×
      Database PairOut HashDomain) ℂ)) = cellRead m.2.2.1.1 z o ⊗ₖ
      ((1 : Matrix (Database PairOut HashDomain) (Database PairOut HashDomain) ℂ) ⊗ₖ
        1) by rw [one_kronecker_one]] at hR
  obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
  obtain ⟨e₁, hr⟩ := cellRead_dec_ne_zero h₁
  have hD : m'.2.1 = m.2.1 := Prod.ext e₁ (Prod.ext (one_dec_ne_zero h₂) (one_dec_ne_zero h₃))
  subst hp hr
  exact ⟨rfl, Prod.ext hD hφ⟩

end ports

/-! ## Reveals, program ports, sponge-only steps -/

section template

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset (TPosN n) × M) (θ : TValsN n)

theorem htQSN_realizeT_bind {Ω Ω' : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (XSpecSN M n) Ω A}
    {g : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (XSpecSN M n) Ω' u}
    {P : Set (RRegSN n M)} {Q : (Σ u, Ω u) → Set (RRegSN n M)}
    {R : (Σ u, Ω' u) → Set (RRegSN n M)}
    (hx : HTQSN m₀ (realizeT θ x) P Q) (hg : ∀ u a, HTQSN m₀ (realizeT θ (g u a)) (Q ⟨u, a⟩) R) :
    HTQSN m₀ (realizeT θ (x.bind g)) P R := by
  rw [realizeT_bind]
  exact HTQSN.bind hx hg

theorem htQ₂SN_realizeT_bind {A B C : QReg} {α β : Type} {x : QComp (XSpecSN M n) A B α}
    {k : α → QComp (XSpecSN M n) B C β} {P : Set (RRegSN n M)} {Q : α → Set (RRegSN n M)}
    {R : β → Set (RRegSN n M)} (hx : HTQ₂SN m₀ (realizeT θ x) P Q)
    (hk : ∀ a, HTQ₂SN m₀ (realizeT θ (k a)) (Q a) R) :
    HTQ₂SN m₀ (realizeT θ (x.bind k)) P R := by
  rw [realizeT_bind₂]
  exact HTQ₂SN.bind hx hk

/-- **A realized reveal is the record port**: the values of `θ` on `T`, the label grown by `T`. -/
theorem htQ₂SN_revealThen {B C : QReg} {α : Type} (T : Finset (TPosN n))
    (k : RevealVals (TValN n) T × (Finset (TPosN n) × M) → QComp (XSpecSN M n) B C α)
    (P : Set (RRegSN n M)) (Q : α → Set (RRegSN n M))
    (hk : ∀ mem, HTQ₂SN m₀ (realizeT θ (k (restrictTo T θ, mem)))
      {s | ∃ s₀ ∈ P, s₀.2.2 = mem ∧ s = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ T, s₀.2.2.2))} Q) :
    HTQ₂SN m₀ (realizeT θ (revealThen goodQN T k)) P Q := by
  have e : realizeT θ (revealThen goodQN T k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpecSN n M) (.inr T) B
        (Equiv.uniqueProd B Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((RSpecSN n M).Out (.inr T) × B)) (B := B)
            (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ (k (restrictTo T θ, mem)) :=
    rfl
  rw [e]
  exact htQ₂SN_queryBind (.inr T) B _ (RecSetQSN P T)
    (fun mem σ hσ ↦ decR_rec_suppSN m₀ T mem P σ hσ) fun mem ↦ htQ₂SN_act_bind _ fun _ ↦ hk mem

/-- **A realized program port hardwiring `z` with `a`** moves the register by `ProgRelHSN`. -/
theorem htQ₂SN_progThen {B C : QReg} {α : Type}
    (p : LazyProg PairOut HashDomain (TPosN n) (TValN n)) {z : HashDomain} {a : PairOut}
    (hr : p.realize θ = .programH z a) (k : QComp (XSpecSN M n) B C α) (P : Set (RRegSN n M))
    (Q : α → Set (RRegSN n M))
    (hk : HTQ₂SN m₀ (realizeT θ k) {s' | ∃ s ∈ P, ProgRelHSN z a s s'} Q) :
    HTQ₂SN m₀ (realizeT θ (progThen p trivial k)) P Q := by
  have e : realizeT θ (progThen p trivial k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpecSN n M)
        (.inl (.inr (p.realize θ))) B (Equiv.uniqueProd B Unit).symm fun _ ↦
          (QComp.act (A := QReg.of ((RSpecSN n M).Out (.inl (.inr (p.realize θ))) × B))
            (B := B) (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ k :=
    rfl
  rw [e]
  revert hk
  generalize p.realize θ = c at hr ⊢
  subst hr
  intro hk
  exact htQ₂SN_queryBind _ B _ (fun _ ↦ {s' | ∃ s ∈ P, ProgRelHSN _ _ s s'})
    (fun r σ hσ ↦ decR_progH_suppSN m₀ _ _ r P σ hσ) fun _ ↦ htQ₂SN_act_bind _ fun _ ↦ hk

/-- **Sponge-only steps keep every register set**. -/
theorem htQSN_sponge {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (spongeSpec PairOut HashDomain) Ω A)
    (P : Set (RRegSN n M)) :
    HTQSN m₀ (realizeT θ (readLift goodQN (y.liftOrdinary
      (t := hwReadCmdSpec PairOut HashDomain M)))) P fun _ ↦ P := by
  induction y using QuantumComp.inductionOn with
  | pure A y => exact htQSN_pure y subset_rfl
  | primBind A o k ih =>
    have e : realizeT θ (readLift goodQN ((QuantumComp.primBind o k).liftOrdinary
        (t := hwReadCmdSpec PairOut HashDomain M))) =
        QuantumComp.primBind o fun b ↦
          realizeT θ (readLift goodQN ((k b).liftOrdinary
            (t := hwReadCmdSpec PairOut HashDomain M))) :=
      rfl
    rw [e]
    exact htQSN_primBind o fun b ↦ ih b
  | queryBind A i E ℓ k ih =>
    have e : realizeT θ (readLift goodQN ((QuantumComp.queryBind i E ℓ k).liftOrdinary
        (t := hwReadCmdSpec PairOut HashDomain M))) =
        QuantumComp.queryBind (spec := RSpecSN n M) (.inl (.inl (.inl i))) E ℓ
          fun r ↦ realizeT θ (readLift goodQN ((k r).liftOrdinary
            (t := hwReadCmdSpec PairOut HashDomain M))) :=
      rfl
    rw [e]
    exact htQSN_queryBind _ E ℓ (fun _ ↦ P) (fun r σ hσ ↦ decR_sponge_suppSN m₀ i r P σ hσ)
      fun r ↦ ih r

end template

/-! ## Read programs as functions of the register -/

section det

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset (TPosN n) × M) (θ : TValsN n)

/-- **A read program answers as a function of the register**: from registers without empty cell,
run lifted, realized and in the decompressed basis, it returns `out s` and leaves `fin s`. -/
def DetQSN {B : QReg} {α : Type} (y : QComp (hwReadSpec PairOut HashDomain M) B B α)
    (out : RRegSN n M → α) (fin : RRegSN n M → RRegSN n M) : Prop :=
  ∀ P : Set (RRegSN n M), (∀ s ∈ P, NoBot s) →
    HTQ₂SN m₀ (realizeT θ (readLiftQ goodQN y)) P
      fun a ↦ {s' | ∃ s ∈ P, a = out s ∧ s' = fin s}

variable {m₀ θ}

theorem DetQSN.congr {B : QReg} {α : Type}
    {y : QComp (hwReadSpec PairOut HashDomain M) B B α}
    {out out' : RRegSN n M → α} {fin fin' : RRegSN n M → RRegSN n M} (h : DetQSN m₀ θ y out fin)
    (e : ∀ s, NoBot s → out s = out' s ∧ fin s = fin' s) : DetQSN m₀ θ y out' fin' := by
  intro P hP
  refine (h P hP).mono subset_rfl fun a ↦ ?_
  rintro s' ⟨s, hs, ha, rfl⟩
  obtain ⟨e₁, e₂⟩ := e s (hP s hs)
  exact ⟨s, hs, ha.trans e₁, e₂⟩

theorem detQSN_pure {B : QReg} {α : Type} (a : α) :
    DetQSN m₀ θ (QuantumComp₂.pure a : QComp (hwReadSpec PairOut HashDomain M) B B α)
      (fun _ ↦ a) fun s ↦ s :=
  fun _ _ ↦ htQ₂SN_pure a fun s hs ↦ ⟨s, hs, rfl, rfl⟩

theorem DetQSN.bind {B : QReg} {α β : Type}
    {x : QComp (hwReadSpec PairOut HashDomain M) B B α}
    {out : RRegSN n M → α} {fin : RRegSN n M → RRegSN n M} (hx : DetQSN m₀ θ x out fin)
    {k : α → QComp (hwReadSpec PairOut HashDomain M) B B β} {out' : α → RRegSN n M → β}
    {fin' : α → RRegSN n M → RRegSN n M} (hk : ∀ a, DetQSN m₀ θ (k a) (out' a) (fin' a)) :
    DetQSN m₀ θ (x.bind k) (fun s ↦ out' (out s) (fin s)) fun s ↦ fin' (out s) (fin s) := by
  intro P hP
  rw [readLift_bind₂, realizeT_bind₂]
  refine HTQ₂SN.bind ((hx P hP).and_noBot hP) fun a ↦
    ((hk a) _ fun s hs ↦ hs.2).mono subset_rfl fun b ↦ ?_
  rintro s'' ⟨s', ⟨⟨s, hs, rfl, rfl⟩, -⟩, rfl, rfl⟩
  exact ⟨s, hs, rfl, rfl⟩

/-- **A read of an `h`-cell answers the view's cell with the memory and updates the memory.** -/
theorem detQSN_readH (z : HashDomain) (upd : M → Option PairOut → M) (B : QReg) :
    DetQSN m₀ θ (readCall (.readH z upd) B) (fun s ↦ ((hwView s.2.1 s.1).1 z, s.2.2.2))
      fun s ↦ readFinHSN s z upd := by
  intro P _ ρ hρ a
  rw [realizeT_readLift_readCall]
  erw [QuantumRuntime.run₂_queryBind, DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun r ↦ ?_
  have hq := querySupportedOn_queryStep_imp (decR (X := PairOut) (Z := HashDomain) m₀)
    (.inl (.inl (.inr (liftRead (.readH z upd))))) B
    (Equiv.uniqueProd B Unit).symm r P
    {s' | ∃ s ∈ P, r = liftAns s (.readH z upd) ∧ s' = readFinHSN s z upd}
    (fun τ hτ ↦ decR_readH_suppSN m₀ z upd r P τ hτ) hρ
  rw [QuantumRuntime.run₂_act_bind]
  erw [DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun u ↦ ?_
  rw [QuantumRuntime.run₂_pure]
  by_cases ha : a = lowerRes (.readH z upd) r
  · subst ha
    rw [SubInstrument.branch_pure_self, LinearMap.id_apply, DSubInstrument.branch_frame_apply]
    refine (QuerySupportedOn.amplify_snd (q := fun s : RRegSN n M ↦ s) hq _).mono ?_
    rintro s' ⟨s, hs, hr, rfl⟩
    exact ⟨s, hs, by rw [hr, lowerRes_liftAns]; rfl, rfl⟩
  · rw [SubInstrument.branch_pure_of_ne ha]
    exact querySupportedOn_zero _ _

end det

/-! ## The counter search as a function of the view -/

section grind

/-- **The pair of the register's view**: the hardwired pair of a cell, else its database pair
(`0` on an empty cell, which the decompressed registers do not have). -/
def hvwSN {M : Type} (s : RRegSN n M) (z : HashDomain) : PairOut :=
  ((hwView s.2.1 s.1).1 z).getD 0

/-- The hash of the register's view: the first component of the pair. -/
def hHSN {M : Type} (s : RRegSN n M) (z : HashDomain) : HashOutput :=
  (hvwSN s z).1

theorem hwView_eq_some_hvwSN {M : Type} {s : RRegSN n M} (hs : NoBot s) (z : HashDomain) :
    (hwView s.2.1 s.1).1 z = some (hvwSN s z) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (or_isSome (s.2.1.1 z) (hs.1 z))
  show (s.2.1.1 z).or (s.1.1 z) = some (((s.2.1.1 z).or (s.1.1 z)).getD 0)
  rw [ha]
  rfl

variable {m₀ : Finset (TPosN n) × SelMemN n} {θ : TValsN n}

/-- **User `i`'s counter search answers the view's selection** and updates user `i`'s memory by
`grindMemS`, the other users' memories kept. -/
theorem det_grindSN (i : Fin n) (v : QTable) (B : QReg) (K : Key) (m : Digest) (k c : ℕ) :
    DetQSN m₀ θ (grindT (SelMemN n) (cwUpdN i) v.publicSeed B K m k c)
      (fun s ↦ v.selectFrom (hHSN s) K.1 K.2.1 K.2.2 m k c)
      (fun s ↦ (s.1, s.2.1, (s.2.2.1, Function.update s.2.2.2 i
        (grindMemS (hvwSN s) v.publicSeed K m k c (s.2.2.2 i))))) := by
  induction k generalizing c with
  | zero =>
    exact (detQSN_pure none).congr fun s _ ↦ ⟨rfl,
      (congrArg (fun m ↦ (s.1, s.2.1, (s.2.2.1, m))) (Function.update_eq_self i s.2.2.2)).symm⟩
  | succ k ih =>
    rw [grindT]
    refine DetQSN.congr (DetQSN.bind (detQSN_readH _ _ B)
      (out' := fun r s ↦ (TargetSum.decodeDigest (truncateHash (r.1.getD 0).1)).elim
        (v.selectFrom (hHSN s) K.1 K.2.1 K.2.2 m k (c + 1))
        fun x ↦ some (BitVec.ofNat counterBits c, x))
      (fin' := fun r s ↦ (TargetSum.decodeDigest (truncateHash (r.1.getD 0).1)).elim
        (s.1, s.2.1, (s.2.2.1, Function.update s.2.2.2 i
          (grindMemS (hvwSN s) v.publicSeed K m k (c + 1) (s.2.2.2 i))))
        fun _ ↦ s) fun r ↦ ?_) fun s hs ↦ ⟨?_, ?_⟩
    · rcases TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) with _ | x
      · exact ih (c + 1)
      · exact detQSN_pure _
    · have e : v.encDigest (hHSN s) K.1 K.2.1 K.2.2 m (BitVec.ofNat counterBits c) =
          truncateHash (hvwSN s (trialCell v.publicSeed K m c)).1 :=
        rfl
      simp only [readFinHSN, hwView_eq_some_hvwSN hs, Option.getD_some]
      rw [QTable.selectFrom, e]
      rcases TargetSum.decodeDigest (truncateHash (hvwSN s (trialCell v.publicSeed K m c)).1)
        with _ | x <;> rfl
    · simp only [readFinHSN, hwView_eq_some_hvwSN hs, Option.getD_some]
      rw [grindMemS]
      rcases TargetSum.decodeDigest (truncateHash (hvwSN s (trialCell v.publicSeed K m c)).1)
        with _ | x
      · simp only [Option.elim, cwUpdN, Function.update_self, Function.update_idem]
        rfl
      · simp only [Option.elim, cwUpdN]

end grind

/-! ## The view, the cells and the encoding cells -/

section cells

theorem hvwSN_congr {M : Type} {s s' : RRegSN n M} {z : HashDomain}
    (h1 : s'.2.1.1 z = s.2.1.1 z) (h2 : s'.1.1 z = s.1.1 z) : hvwSN s' z = hvwSN s z := by
  show ((s'.2.1.1 z).or (s'.1.1 z)).getD 0 = ((s.2.1.1 z).or (s.1.1 z)).getD 0
  rw [h1, h2]

theorem hvwSN_tuple {M : Type} (s : RRegSN n M) (L : Finset (TPosN n)) (m : M) :
    hvwSN (s.1, s.2.1, (L, m)) = hvwSN s :=
  rfl

theorem noBot_of_fst_eqSN {M : Type} {s s' : RRegSN n M} (h : s'.1 = s.1) (hs : NoBot s) :
    NoBot s' := by
  show Quantum.Xmss.Assembly.NoBotDb s'.1
  rw [h]
  exact hs

/-- An encoding cell names its slot, whatever `PK.seed`. -/
theorem slotF_encCell (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (m : Digest) (c : EncodingCounter) : slotF (encCell seed l τ e m c) = some (.enc l τ e) :=
  slotOfInput_pkOfInput (slotOf_cell (s := .enc l τ e) ⟨0, 0, seed⟩ 0 trivial (m, c))

/-- **No cell of a table is an encoding cell**, of any user. -/
theorem cellOf_ne_encCellSN (S0 : MasterSeed) (v : QTable) (p : Pos) (seed : PublicParameter)
    (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (m : Digest) (c : EncodingCounter) :
    cellOf S0 p v ≠ encCell seed l τ e m c := fun h ↦
  posSlot_ne_enc v p.1 l τ e
    (Option.some.inj ((slotF_cellOf S0 v p).symm.trans (h ▸ slotF_encCell seed l τ e m c)))

end cells

/-! ## Programs, searches and publications of user `j` in the decompressed basis -/

section steps

variable (θ : TValsN n)

/-- **A step of user `j`'s signer changing only the cells of `j`'s positions `C`**: no empty cell
kept, the inner memory kept, the label grown by `j`'s value coordinates, and the hardwired and
database `h`-cells kept off the positions' cells. -/
def StepRelSN (j : Fin n) (C : Set Pos) (s s' : RRegSN n (SelMemN n)) : Prop :=
  (NoBot s → NoBot s') ∧ s'.2.2.2 = s.2.2.2 ∧ s.2.2.1 ⊆ s'.2.2.1 ∧
    (∀ t ∈ s'.2.2.1, t ∈ s.2.2.1 ∨ (t.1 = j ∧ t.2.IsVal)) ∧
    ∀ z, (∀ p ∈ C, z ≠ cellQ (userOf θ j) p) → s'.2.1.1 z = s.2.1.1 z ∧ s'.1.1 z = s.1.1 z

variable {θ}

theorem StepRelSN.refl (j : Fin n) (C : Set Pos) (s : RRegSN n (SelMemN n)) :
    StepRelSN θ j C s s :=
  ⟨id, rfl, subset_rfl, fun _ ht ↦ .inl ht, fun _ _ ↦ ⟨rfl, rfl⟩⟩

theorem StepRelSN.trans {j : Fin n} {C C' : Set Pos} {s s₁ s₂ : RRegSN n (SelMemN n)}
    (h₁ : StepRelSN θ j C s s₁) (h₂ : StepRelSN θ j C' s₁ s₂) : StepRelSN θ j (C ∪ C') s s₂ :=
  ⟨fun h ↦ h₂.1 (h₁.1 h), h₂.2.1.trans h₁.2.1, h₁.2.2.1.trans h₂.2.2.1,
    fun t ht ↦ (h₂.2.2.2.1 t ht).elim (fun ht ↦ h₁.2.2.2.1 t ht) .inr, fun z hz ↦ by
      obtain ⟨a₁, b₁⟩ := h₁.2.2.2.2 z fun p hp ↦ hz p (.inl hp)
      obtain ⟨a₂, b₂⟩ := h₂.2.2.2.2 z fun p hp ↦ hz p (.inr hp)
      exact ⟨a₂.trans a₁, b₂.trans b₁⟩⟩

theorem StepRelSN.mono {j : Fin n} {C C' : Set Pos} {s s' : RRegSN n (SelMemN n)}
    (h : StepRelSN θ j C s s') (hC : C ⊆ C') : StepRelSN θ j C' s s' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun z hz ↦ h.2.2.2.2 z fun p hp ↦ hz p (hC hp)⟩

theorem stepRelSN_reveal (j : Fin n) {T : Finset TPos} (hT : ValOnly T)
    (s : RRegSN n (SelMemN n)) :
    StepRelSN θ j ∅ s (s.1, s.2.1, (s.2.2.1 ∪ atU j T, s.2.2.2)) :=
  ⟨id, rfl, Finset.subset_union_left, fun _ ht ↦ (Finset.mem_union.1 ht).imp_right fun ht ↦
    ⟨(mem_atU_iff.1 ht).1, hT _ (mem_atU_iff.1 ht).2⟩, fun _ _ ↦ ⟨rfl, rfl⟩⟩

theorem stepRelSN_prog {j : Fin n} {p : Pos} {s s' : RRegSN n (SelMemN n)}
    (h : ProgRelHSN (cellQ (userOf θ j) p) (tabOf (userOf θ j) p) s s') :
    StepRelSN θ j {p} s s' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h2, congrArg (·.2.2) h1, ?_, fun t ht ↦ .inl ?_, fun z hz ↦ ⟨?_, h3 z (hz p rfl)⟩⟩
  · rw [show s'.2.2.1 = s.2.2.1 from congrArg (·.2.1) h1]
  · rwa [show s'.2.2.1 = s.2.2.1 from congrArg (·.2.1) h1] at ht
  · rw [show s'.2.1 = progUpdate (.programH (cellQ (userOf θ j) p) (tabOf (userOf θ j) p)) s.2.1
      from congrArg Prod.fst h1]
    exact Function.update_of_ne (hz p rfl) _ _

variable {m₀ : Finset (TPosN n) × SelMemN n}

variable (θ) in
/-- **Program calls of user `j`'s structural positions** move the register by `StepRelSN`. -/
theorem htQ₂SN_progPos (j : Fin n) (B : QReg) : ∀ (ps : List Pos), (∀ p ∈ ps, p.1.IsStruct) →
    ∀ P : Set (RRegSN n (SelMemN n)), HTQ₂SN m₀ (realizeT θ (progPosN (SelMemN n) j B ps)) P
      fun _ ↦ {s' | ∃ s ∈ P, StepRelSN θ j {p | p ∈ ps} s s'}
  | [], _, P => htQ₂SN_pure () fun s hs ↦ ⟨s, hs, StepRelSN.refl _ _ s⟩
  | p :: ps, hps, P => by
    refine htQ₂SN_progThen m₀ θ (progTN j p) (realize_progTN (hps p List.mem_cons_self) j θ)
      _ P _ ((htQ₂SN_progPos j B ps (fun q hq ↦ hps q (List.mem_cons_of_mem _ hq)) _).mono
        subset_rfl fun _ ↦ ?_)
    rintro s₂ ⟨s₁, ⟨s, hs, hR⟩, hS⟩
    refine ⟨s, hs, ((stepRelSN_prog hR).trans hS).mono ?_⟩
    rintro q (hq | hq)
    · exact List.mem_cons.2 (.inl hq)
    · exact List.mem_cons_of_mem _ hq

variable (θ) in
/-- **User `j`'s counter search in the decompressed basis**: the view's selection, user `j`'s
memory updated by `grindMemS`, the label grown by `j`'s value the key signs. -/
theorem htQ₂SN_selectS (j : Fin n) (B : QReg) (K : Key) (P : Set (RRegSN n (SelMemN n)))
    (hP : ∀ s ∈ P, NoBot s) :
    HTQ₂SN m₀ (realizeT θ (selectTN (SelMemN n) cwUpdN j (tabOf (userOf θ j)).publicSeed B K)) P
      fun g ↦ {s' | ∃ s ∈ P, g = (tabOf (userOf θ j)).selectFrom (hHSN s) K.1 K.2.1 K.2.2
          ((tabOf (userOf θ j)).valuePos (msgPos K)) encodingAttemptLimit 0 ∧
        s'.1 = s.1 ∧ s'.2.1 = s.2.1 ∧ s'.2.2.1 = s.2.2.1 ∪ atU j {vcoord (msgPos K)} ∧
        s'.2.2.2 = Function.update s.2.2.2 j (grindMemS (hvwSN s) (tabOf (userOf θ j)).publicSeed
          K ((tabOf (userOf θ j)).valuePos (msgPos K)) encodingAttemptLimit 0 (s.2.2.2 j))} := by
  rw [selectTN]
  refine htQ₂SN_revealThen m₀ θ _ _ P _ fun mem ↦ ?_
  have hb : (tabRN (restrictTo (atU j {vcoord (msgPos K)}) θ) j).valuePos (msgPos K) =
      (tabOf (userOf θ j)).valuePos (msgPos K) :=
    valuePos_tabOf_congr _ (tabRN_restrictTo_congr (atU_restrict _) θ _
      (Finset.mem_singleton_self _))
  dsimp only
  rw [hb]
  refine ((det_grindSN (m₀ := m₀) (θ := θ) j (tabOf (userOf θ j)) B K _ encodingAttemptLimit
    0) _ ?_).mono subset_rfl fun g ↦ ?_
  · rintro s ⟨s₀, hs₀, -, rfl⟩
    exact hP s₀ hs₀
  · rintro s' ⟨s, ⟨s₀, hs₀, -, rfl⟩, hg, hs'⟩
    refine ⟨s₀, hs₀, hg, by rw [hs'], by rw [hs'], by rw [hs'], ?_⟩
    simp only [hs', hvwSN_tuple]

/-- The memory after a memoized selection (kept) or a counter search (`grindMemS`). -/
def grindO (P : HashDomain → PairOut) (seed : PublicParameter) (K : Key) (m : Digest) :
    Option SelS → SelMem → SelMem
  | some _, mem => mem
  | none, mem => grindMemS P seed K m encodingAttemptLimit 0 mem

theorem grindO_some (P : HashDomain → PairOut) (seed : PublicParameter) (K : Key) (m : Digest)
    (x : SelS) (mem : SelMem) : grindO P seed K m (some x) mem = mem :=
  rfl

theorem grindO_none (P : HashDomain → PairOut) (seed : PublicParameter) (K : Key) (m : Digest)
    (mem : SelMem) : grindO P seed K m none mem = grindMemS P seed K m encodingAttemptLimit 0 mem :=
  rfl

variable (θ) in
/-- **User `j`'s selection of `K` or its memo** in the decompressed basis: the memo, or the view's
selection with user `j`'s memory updated by the search. -/
theorem htQ₂SN_selOrMemoS (j : Fin n) (B : QReg) (K : Key) (o : Option SelS)
    (P : Set (RRegSN n (SelMemN n))) (hP : ∀ s ∈ P, NoBot s) :
    HTQ₂SN m₀ (realizeT θ (selOrMemoTN (SelMemN n) cwUpdN j (tabOf (userOf θ j)).publicSeed B K
      o)) P
      fun g ↦ {s' | ∃ s ∈ P, g = o.getD ((tabOf (userOf θ j)).selectFrom (hHSN s) K.1 K.2.1
          K.2.2 ((tabOf (userOf θ j)).valuePos (msgPos K)) encodingAttemptLimit 0) ∧
        s'.1 = s.1 ∧ s'.2.1 = s.2.1 ∧ s.2.2.1 ⊆ s'.2.2.1 ∧
        s'.2.2.1 ⊆ s.2.2.1 ∪ atU j {vcoord (msgPos K)} ∧
        s'.2.2.2 = Function.update s.2.2.2 j (grindO (hvwSN s) (tabOf (userOf θ j)).publicSeed
          K ((tabOf (userOf θ j)).valuePos (msgPos K)) o (s.2.2.2 j))} := by
  cases o with
  | some x =>
    exact htQ₂SN_pure x fun s hs ↦ ⟨s, hs, Option.getD_some.symm, rfl, rfl, subset_rfl,
      Finset.subset_union_left, by rw [grindO_some, Function.update_eq_self]⟩
  | none =>
    refine (htQ₂SN_selectS θ j B K P hP).mono subset_rfl fun g ↦ ?_
    rintro s' ⟨s, hs, hg, h1, h2, h3, h4⟩
    refine ⟨s, hs, by rw [Option.getD_none]; exact hg, h1, h2,
      by rw [h3]; exact Finset.subset_union_left, by rw [h3], ?_⟩
    rw [grindO_none]
    exact h4

variable (θ) in
/-- **Publishing user `j`'s layer signature in the decompressed basis.** -/
theorem htQ₂SN_publishS (j : Fin n) (B : QReg) (K : Key) (c : EncodingCounter) (x : Encoding)
    (P : Set (RRegSN n (SelMemN n))) :
    HTQ₂SN m₀ (realizeT θ (publishTN (SelMemN n) j B K c x)) P
      fun sig ↦ {s' | ∃ s ∈ P, sig = layerSigD (userOf θ j) K c x ∧
        StepRelSN θ j {p | p ∈ layerPos K x} s s'} := by
  rw [publishTN]
  refine htQ₂SN_revealThen m₀ θ _ _ P _ fun mem ↦ ?_
  refine htQ₂SN_realizeT_bind m₀ θ
    (htQ₂SN_progPos θ j B _ (fun p hp ↦ isStruct_of_mem_layerPos hp) _) fun _ ↦ htQ₂SN_pure _ ?_
  rintro s₂ ⟨s₁, ⟨s, hs, -, rfl⟩, hS⟩
  refine ⟨s, hs, ?_, ((stepRelSN_reveal j (valOnly_layerReveal K x) s).trans hS).mono
    fun p hp ↦ hp.resolve_left id⟩
  have hm := tabRN_restrictTo_congr (atU_restrict (i := j) (layerReveal K x)) θ
  have hc : ∀ i, (tabRN (restrictTo (atU j (layerReveal K x)) θ) j).chainValue K.1 K.2.1 K.2.2 i
      (x i).val = (tabOf (userOf θ j)).chainValue K.1 K.2.1 K.2.2 i (x i).val := fun i ↦
    chainValue_tabOf_congr (hm _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))))
  have hp : (tabRN (restrictTo (atU j (layerReveal K x)) θ) j).authPath K.1 K.2.1 K.2.2 =
      (tabOf (userOf θ j)).authPath K.1 K.2.1 K.2.2 := funext fun z ↦
    treeValue_tabOf_congr (hm _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun z : Fin (layerHeight K.1) ↦
        treeC K.1 K.2.1 z.val ((K.2.2.val >>> z.val) ^^^ 1)) (Finset.mem_univ z))))
  rw [layerSigD_eq]
  simp only [hc, hp]

variable (θ) in
/-- **User `j`'s FORS opening in the decompressed basis.** -/
theorem htQ₂SN_forsOpenS (j : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (P : Set (RRegSN n (SelMemN n))) :
    HTQ₂SN m₀ (realizeT θ (forsOpenTN (SelMemN n) j B idx lv)) P
      fun fo ↦ {s' | ∃ s ∈ P, fo = forsD (userOf θ j) idx lv ∧
        StepRelSN θ j {p | p ∈ forsPos idx lv} s s'} := by
  rw [forsOpenTN]
  refine htQ₂SN_revealThen m₀ θ _ _ P _ fun mem ↦ ?_
  refine htQ₂SN_realizeT_bind m₀ θ
    (htQ₂SN_progPos θ j B _ (fun p hp ↦ isStruct_of_mem_forsPos hp) _) fun _ ↦ htQ₂SN_pure _ ?_
  rintro s₂ ⟨s₁, ⟨s, hs, -, rfl⟩, hS⟩
  refine ⟨s, hs, ?_, ((stepRelSN_reveal j (valOnly_forsReveal idx lv) s).trans hS).mono
    fun p hp ↦ hp.resolve_left id⟩
  have hm := tabRN_restrictTo_congr (atU_restrict (i := j) (forsReveal idx lv)) θ
  rw [forsD_eq]
  funext κ
  have h1 : (tabRN (restrictTo (atU j (forsReveal idx lv)) θ) j).forsSecret idx κ (lv κ) =
      (tabOf (userOf θ j)).forsSecret idx κ (lv κ) :=
    dig_tabOf_congr (hm _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ κ)))))
  have h2 : ∀ z : Fin forsTreeHeight,
      (tabRN (restrictTo (atU j (forsReveal idx lv)) θ) j).forsValue idx κ z.val
        (((lv κ).val >>> z.val) ^^^ 1) =
      (tabOf (userOf θ j)).forsValue idx κ z.val (((lv κ).val >>> z.val) ^^^ 1) := fun z ↦
    forsValue_tabOf_congr (hm _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun q : ForsTreeIndex × Fin forsTreeHeight ↦
        forsC idx q.1 q.2.val (((lv q.1).val >>> q.2.val) ^^^ 1)) (Finset.mem_univ (κ, z)))))
  exact congrArg₂ ForsTreeOpening.mk h1 (funext h2)

variable (θ) in
/-- **The publication of user `j`'s signature in the decompressed basis**: when all three
searches succeed, the signature from the revealed values and the program calls of its positions;
nothing otherwise. -/
theorem htQ₂SN_publishAllS (j : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) (g₀ g₁ g₂ : SelS)
    (P : Set (RRegSN n (SelMemN n))) :
    HTQ₂SN m₀ (realizeT θ (publishAllTN (SelMemN n) j B idx lv R g₀ g₁ g₂)) P
      fun sig ↦ {s' | ∃ s ∈ P, sig = sigOf3 R (forsD (userOf θ j) idx lv)
          (g₀.map fun g ↦ layerSigD (userOf θ j) (keyOf 0 idx) g.1 g.2)
          (g₁.map fun g ↦ layerSigD (userOf θ j) (keyOf 1 idx) g.1 g.2)
          (g₂.map fun g ↦ layerSigD (userOf θ j) (keyOf 2 idx) g.1 g.2) ∧
        StepRelSN θ j (pubSet idx lv g₀ g₁ g₂) s s'} := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;>
    try exact htQ₂SN_pure _ fun s hs ↦ ⟨s, hs, rfl, StepRelSN.refl _ _ s⟩
  simp only [publishAllTN]
  refine htQ₂SN_realizeT_bind m₀ θ (htQ₂SN_forsOpenS θ j B idx lv P) fun fo ↦ ?_
  refine htQ₂SN_realizeT_bind m₀ θ (htQ₂SN_publishS θ j B _ _ _ _) fun b ↦ ?_
  refine htQ₂SN_realizeT_bind m₀ θ (htQ₂SN_publishS θ j B _ _ _ _) fun mi ↦ ?_
  refine htQ₂SN_realizeT_bind m₀ θ (htQ₂SN_publishS θ j B _ _ _ _) fun t ↦ htQ₂SN_pure _ ?_
  rintro s₄ ⟨s₃, ⟨s₂, ⟨s₁, ⟨s, hs, rfl, h1⟩, rfl, h2⟩, rfl, h3⟩, rfl, h4⟩
  refine ⟨s, hs, rfl, (((h1.trans h2).trans h3).trans h4).mono ?_⟩
  rintro p (((hp | hp) | hp) | hp)
  · exact Or.inl hp
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl hp))
  · exact Or.inr (Or.inr (Or.inr hp))

end steps

/-! ## A signature of user `j` in the decompressed basis -/

section signer

/-- The opening of a layer signature of `K_l(idx)` with the selection `sel`. -/
def layerOpenS (v : QTable) (idx : Index) (l : Layer) (sel : EncodingCounter × Encoding) :
    LayerSignature l :=
  ⟨sel.1, fun i ↦ v.chainValue l (treeOfIndex l idx) (leafOfIndex l idx) i (sel.2 i).val,
    v.authPath l (treeOfIndex l idx) (leafOfIndex l idx)⟩

theorem layerSig_eq_mapOpen (v : QTable) (H : HashDomain → HashOutput) (idx : Index)
    (l : Layer) : v.layerSig H idx l = (v.layerSelect H idx l).map (layerOpenS v idx l) :=
  rfl

/-- **The memory after the three selections** of a signature of index `idx` with the memo `h`:
a memoized key kept, the others searched. -/
def grind3N (θ : TVals) (P : HashDomain → PairOut) (idx : Index) (h : KeyMemo) (mem : SelMem) :
    SelMem :=
  grindO P (tabOf θ).publicSeed (keyOf 2 idx) ((tabOf θ).layerMessage idx 2) (h (keyOf 2 idx))
    (grindO P (tabOf θ).publicSeed (keyOf 1 idx) ((tabOf θ).layerMessage idx 1) (h (keyOf 1 idx))
      (grindO P (tabOf θ).publicSeed (keyOf 0 idx) ((tabOf θ).layerMessage idx 0)
        (h (keyOf 0 idx)) mem))

/-- **The effect of user `j`'s signature of `msg` with the memo `h`** on the decompressed
register, at the event side's digest policy: no empty cell, the view kept at every encoding cell,
the label grown by `j`'s value coordinates and digest reveal, user `j`'s memory moved by the
searches of the keys missing from the memo (`grind3N`), the selections (memoized, else the view's),
the answer from them, and the hardwired cells: the earlier ones, `j`'s digest cell with its stream
pair, and, when all three selections succeed, the published positions' cells. -/
def SignEffN (θ : TValsN n) (j : Fin n) (msg : Message) (h : KeyMemo)
    (s : RRegSN n (SelMemN n)) (a : Option Signature × MemoAns) (s' : RRegSN n (SelMemN n)) :
    Prop :=
  NoBot s' ∧
  (∀ seed l τ e m c, hvwSN s' (encCell seed l τ e m c) = hvwSN s (encCell seed l τ e m c)) ∧
  s.2.2.1 ⊆ s'.2.2.1 ∧
  (∀ t ∈ s'.2.2.1, t ∈ s.2.2.1 ∨ (t.1 = j ∧ (t.2.IsVal ∨ t.2 ∈ strNeed (labU s.2.2.1 j) msg))) ∧
  atU j (strNeed (labU s.2.2.1 j) msg) ⊆ s'.2.2.1 ∧
  s'.2.2.2 = Function.update s.2.2.2 j (grind3N (userOf θ j) (hvwSN s)
    (idxS (userOf θ j) (labU s.2.2.1 j) msg) h (s.2.2.2 j)) ∧
  ∃ g₀ g₁ g₂ : SelS,
    g₀ = (h (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j) msg))).getD
      ((tabOf (userOf θ j)).layerSelect (hHSN s) (idxS (userOf θ j) (labU s.2.2.1 j) msg) 0) ∧
    g₁ = (h (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j) msg))).getD
      ((tabOf (userOf θ j)).layerSelect (hHSN s) (idxS (userOf θ j) (labU s.2.2.1 j) msg) 1) ∧
    g₂ = (h (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j) msg))).getD
      ((tabOf (userOf θ j)).layerSelect (hHSN s) (idxS (userOf θ j) (labU s.2.2.1 j) msg) 2) ∧
    a = (sigOf3 ((tabOf (userOf θ j)).randomizer msg)
      ((tabOf (userOf θ j)).forsOpening (idxS (userOf θ j) (labU s.2.2.1 j) msg)
        (lvS (userOf θ j) (labU s.2.2.1 j) msg))
      (g₀.map (layerOpenS (tabOf (userOf θ j)) (idxS (userOf θ j) (labU s.2.2.1 j) msg) 0))
      (g₁.map (layerOpenS (tabOf (userOf θ j)) (idxS (userOf θ j) (labU s.2.2.1 j) msg) 1))
      (g₂.map (layerOpenS (tabOf (userOf θ j)) (idxS (userOf θ j) (labU s.2.2.1 j) msg) 2)),
      (idxS (userOf θ j) (labU s.2.2.1 j) msg, layerSels g₀ g₁ g₂)) ∧
    ∀ z ω, s'.2.1.1 z = some ω → s.2.1.1 z = some ω ∨
      (z = cellQ (userOf θ j) (digPos msg) ∧ ω = dgS (userOf θ j) (labU s.2.2.1 j) msg) ∨
      ∃ sel₀ sel₁ sel₂ : EncodingCounter × Encoding,
        g₀ = some sel₀ ∧ g₁ = some sel₁ ∧ g₂ = some sel₂ ∧
        ∃ p, (p ∈ forsPos (idxS (userOf θ j) (labU s.2.2.1 j) msg)
            (lvS (userOf θ j) (labU s.2.2.1 j) msg) ∨
          p ∈ layerPos (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j) msg)) sel₀.2 ∨
          p ∈ layerPos (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j) msg)) sel₁.2 ∨
          p ∈ layerPos (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j) msg)) sel₂.2) ∧
          z = cellQ (userOf θ j) p

theorem grindO_congr {P P' : HashDomain → PairOut} {seed : PublicParameter} {K : Key}
    {m : Digest} (h : ∀ c, P (trialCell seed K m c) = P' (trialCell seed K m c))
    (o : Option SelS) (mem : SelMem) : grindO P seed K m o mem = grindO P' seed K m o mem := by
  cases o with
  | some _ => rfl
  | none => exact grindMemS_congr h _ _ _

theorem isVal_of_mem_atU_vcoord {j : Fin n} {q : Quantum.Sphincs.ValPos} {t : TPosN n}
    (ht : t ∈ atU j {vcoord q}) : t.1 = j ∧ t.2.IsVal := by
  obtain ⟨hj, ht⟩ := mem_atU_iff.1 ht
  rw [Finset.mem_singleton.1 ht]
  exact ⟨hj, isVal_vcoord q⟩

variable {θ : TValsN n}

/-- **The assembly of a signature's effect** from its steps: the reveals and the digest program
(`s₃`), the three selections (`s₄`, `s₅`, `s₆`) and the publication (`s₇`). -/
theorem signEffN_of {j : Fin n} {msg : Message} {h : KeyMemo}
    {s s₃ s₄ s₅ s₆ s₇ : RRegSN n (SelMemN n)} {sig : Option Signature} {g₀ g₁ g₂ : SelS}
    (hp1 : s₃.2 = (progUpdate (.programH (cellQ (userOf θ j) (digPos msg))
      (dgS (userOf θ j) (labU s.2.2.1 j) msg)) s.2.1,
      ((s.2.2.1 ∪ atU j {seedC, rootC, rndC msg}) ∪ atU j (strNeed (labU s.2.2.1 j) msg),
        s.2.2.2)))
    (hp2 : NoBot s → NoBot s₃)
    (hp3 : ∀ z', z' ≠ cellQ (userOf θ j) (digPos msg) → s₃.1.1 z' = s.1.1 z')
    (hg₀ : g₀ = (h (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j) msg))).getD
      ((tabOf (userOf θ j)).selectFrom (hHSN s₃)
        (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j) msg)).1
        (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j) msg)).2.1
        (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j) msg)).2.2
        ((tabOf (userOf θ j)).valuePos (msgPos (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j)
          msg)))) encodingAttemptLimit 0))
    (e41 : s₄.1 = s₃.1) (e42 : s₄.2.1 = s₃.2.1) (e43 : s₃.2.2.1 ⊆ s₄.2.2.1)
    (e43' : s₄.2.2.1 ⊆
      s₃.2.2.1 ∪ atU j {vcoord (msgPos (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j) msg)))})
    (e44 : s₄.2.2.2 = Function.update s₃.2.2.2 j (grindO (hvwSN s₃)
      (tabOf (userOf θ j)).publicSeed (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j) msg))
      ((tabOf (userOf θ j)).valuePos (msgPos (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j) msg))))
      (h (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j) msg))) (s₃.2.2.2 j)))
    (hg₁ : g₁ = (h (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j) msg))).getD
      ((tabOf (userOf θ j)).selectFrom (hHSN s₄)
        (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j) msg)).1
        (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j) msg)).2.1
        (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j) msg)).2.2
        ((tabOf (userOf θ j)).valuePos (msgPos (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j)
          msg)))) encodingAttemptLimit 0))
    (e51 : s₅.1 = s₄.1) (e52 : s₅.2.1 = s₄.2.1) (e53 : s₄.2.2.1 ⊆ s₅.2.2.1)
    (e53' : s₅.2.2.1 ⊆
      s₄.2.2.1 ∪ atU j {vcoord (msgPos (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j) msg)))})
    (e54 : s₅.2.2.2 = Function.update s₄.2.2.2 j (grindO (hvwSN s₄)
      (tabOf (userOf θ j)).publicSeed (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j) msg))
      ((tabOf (userOf θ j)).valuePos (msgPos (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j) msg))))
      (h (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j) msg))) (s₄.2.2.2 j)))
    (hg₂ : g₂ = (h (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j) msg))).getD
      ((tabOf (userOf θ j)).selectFrom (hHSN s₅)
        (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j) msg)).1
        (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j) msg)).2.1
        (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j) msg)).2.2
        ((tabOf (userOf θ j)).valuePos (msgPos (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j)
          msg)))) encodingAttemptLimit 0))
    (e61 : s₆.1 = s₅.1) (e62 : s₆.2.1 = s₅.2.1) (e63 : s₅.2.2.1 ⊆ s₆.2.2.1)
    (e63' : s₆.2.2.1 ⊆
      s₅.2.2.1 ∪ atU j {vcoord (msgPos (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j) msg)))})
    (e64 : s₆.2.2.2 = Function.update s₅.2.2.2 j (grindO (hvwSN s₅)
      (tabOf (userOf θ j)).publicSeed (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j) msg))
      ((tabOf (userOf θ j)).valuePos (msgPos (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j) msg))))
      (h (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j) msg))) (s₅.2.2.2 j)))
    (hsig : sig = sigOf3 ((tabOf (userOf θ j)).randomizer msg)
      (forsD (userOf θ j) (idxS (userOf θ j) (labU s.2.2.1 j) msg)
        (lvS (userOf θ j) (labU s.2.2.1 j) msg))
      (g₀.map fun g ↦ layerSigD (userOf θ j) (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j) msg))
        g.1 g.2)
      (g₁.map fun g ↦ layerSigD (userOf θ j) (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j) msg))
        g.1 g.2)
      (g₂.map fun g ↦ layerSigD (userOf θ j) (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j) msg))
        g.1 g.2))
    (h7 : StepRelSN θ j (pubSet (idxS (userOf θ j) (labU s.2.2.1 j) msg)
      (lvS (userOf θ j) (labU s.2.2.1 j) msg) g₀ g₁ g₂) s₆ s₇)
    (hs : NoBot s) :
    SignEffN θ j msg h s (sig, (idxS (userOf θ j) (labU s.2.2.1 j) msg, layerSels g₀ g₁ g₂))
      s₇ := by
  have hz3 : s₃.2.1 = progUpdate (.programH (cellQ (userOf θ j) (digPos msg))
      (dgS (userOf θ j) (labU s.2.2.1 j) msg)) s.2.1 := congrArg Prod.fst hp1
  have hv3 : ∀ seed l τ e m c, hvwSN s₃ (encCell seed l τ e m c) =
      hvwSN s (encCell seed l τ e m c) := fun seed l τ e m c ↦ by
    have hz : encCell seed l τ e m c ≠ cellQ (userOf θ j) (digPos msg) :=
      fun h ↦ cellOf_ne_encCellSN _ _ _ seed l τ e m c h.symm
    refine hvwSN_congr ?_ (hp3 _ hz)
    rw [hz3, progUpdate_programH_fst, Function.update_of_ne hz]
  have hv4 : ∀ seed l τ e m c, hvwSN s₄ (encCell seed l τ e m c) =
      hvwSN s (encCell seed l τ e m c) := fun seed l τ e m c ↦
    (hvwSN_congr (by rw [e42]) (by rw [e41])).trans (hv3 seed l τ e m c)
  have hv5 : ∀ seed l τ e m c, hvwSN s₅ (encCell seed l τ e m c) =
      hvwSN s (encCell seed l τ e m c) := fun seed l τ e m c ↦
    (hvwSN_congr (by rw [e52]) (by rw [e51])).trans (hv4 seed l τ e m c)
  have hv6 : ∀ seed l τ e m c, hvwSN s₆ (encCell seed l τ e m c) =
      hvwSN s (encCell seed l τ e m c) := fun seed l τ e m c ↦
    (hvwSN_congr (by rw [e62]) (by rw [e61])).trans (hv5 seed l τ e m c)
  have hv7 : ∀ seed l τ e m c, hvwSN s₇ (encCell seed l τ e m c) =
      hvwSN s (encCell seed l τ e m c) := fun seed l τ e m c ↦ by
    obtain ⟨a, b⟩ := h7.2.2.2.2 _ fun p _ h ↦ cellOf_ne_encCellSN _ _ p seed l τ e m c h.symm
    exact (hvwSN_congr a b).trans (hv6 seed l τ e m c)
  have hsel : ∀ s' : RRegSN n (SelMemN n), (∀ seed l τ e m c, hvwSN s' (encCell seed l τ e m c)
      = hvwSN s (encCell seed l τ e m c)) → ∀ l,
      (tabOf (userOf θ j)).selectFrom (hHSN s')
        (keyOf l (idxS (userOf θ j) (labU s.2.2.1 j) msg)).1
        (keyOf l (idxS (userOf θ j) (labU s.2.2.1 j) msg)).2.1
        (keyOf l (idxS (userOf θ j) (labU s.2.2.1 j) msg)).2.2
        ((tabOf (userOf θ j)).valuePos (msgPos (keyOf l (idxS (userOf θ j) (labU s.2.2.1 j)
          msg)))) encodingAttemptLimit 0 =
      (tabOf (userOf θ j)).layerSelect (hHSN s) (idxS (userOf θ j) (labU s.2.2.1 j) msg) l :=
    fun s' hs' l ↦ by
      have hea : EncAgree (tabOf (userOf θ j)).publicSeed (hHSN s') (hHSN s) :=
        fun l τ e m c ↦ congrArg Prod.fst (hs' _ l τ e m c)
      rw [QTable.layerSelect_eq]
      unfold QTable.select
      rw [EncAgree.selectFrom hea]
      rfl
  have h0 : g₀ = (h (keyOf 0 (idxS (userOf θ j) (labU s.2.2.1 j) msg))).getD
      ((tabOf (userOf θ j)).layerSelect (hHSN s) (idxS (userOf θ j) (labU s.2.2.1 j) msg) 0) := by
    rw [hg₀, hsel s₃ hv3 0]
  have h1 : g₁ = (h (keyOf 1 (idxS (userOf θ j) (labU s.2.2.1 j) msg))).getD
      ((tabOf (userOf θ j)).layerSelect (hHSN s) (idxS (userOf θ j) (labU s.2.2.1 j) msg) 1) := by
    rw [hg₁, hsel s₄ hv4 1]
  have h2 : g₂ = (h (keyOf 2 (idxS (userOf θ j) (labU s.2.2.1 j) msg))).getD
      ((tabOf (userOf θ j)).layerSelect (hHSN s) (idxS (userOf θ j) (labU s.2.2.1 j) msg) 2) := by
    rw [hg₂, hsel s₅ hv5 2]
  have hgr : ∀ s' : RRegSN n (SelMemN n), (∀ seed l τ e m c, hvwSN s' (encCell seed l τ e m c)
      = hvwSN s (encCell seed l τ e m c)) → ∀ l o mem,
      grindO (hvwSN s') (tabOf (userOf θ j)).publicSeed
        (keyOf l (idxS (userOf θ j) (labU s.2.2.1 j) msg))
        ((tabOf (userOf θ j)).valuePos (msgPos (keyOf l (idxS (userOf θ j) (labU s.2.2.1 j)
          msg)))) o mem =
      grindO (hvwSN s) (tabOf (userOf θ j)).publicSeed
        (keyOf l (idxS (userOf θ j) (labU s.2.2.1 j) msg))
        ((tabOf (userOf θ j)).layerMessage (idxS (userOf θ j) (labU s.2.2.1 j) msg) l) o mem :=
    fun s' hs' l o mem ↦ by
      rw [QTable.msgPos_eq]
      exact grindO_congr (fun c ↦ hs' _ _ _ _ _ _) o mem
  have hmem3 : s₃.2.2.2 = s.2.2.2 := congrArg (·.2.2) hp1
  have hlab3 : s₃.2.2.1 = s.2.2.1 ∪ atU j {seedC, rootC, rndC msg} ∪
      atU j (strNeed (labU s.2.2.1 j) msg) := congrArg (·.2.1) hp1
  have hsub : s.2.2.1 ∪ atU j (strNeed (labU s.2.2.1 j) msg) ⊆ s₇.2.2.1 := by
    refine subset_trans ?_ (subset_trans e43 (subset_trans e53 (subset_trans e63 h7.2.2.1)))
    rw [hlab3]
    intro t ht
    simp only [Finset.mem_union] at ht ⊢
    tauto
  have hsigN : sig = sigOf3 ((tabOf (userOf θ j)).randomizer msg)
      ((tabOf (userOf θ j)).forsOpening (idxS (userOf θ j) (labU s.2.2.1 j) msg)
        (lvS (userOf θ j) (labU s.2.2.1 j) msg))
      (g₀.map (layerOpenS (tabOf (userOf θ j)) (idxS (userOf θ j) (labU s.2.2.1 j) msg) 0))
      (g₁.map (layerOpenS (tabOf (userOf θ j)) (idxS (userOf θ j) (labU s.2.2.1 j) msg) 1))
      (g₂.map (layerOpenS (tabOf (userOf θ j)) (idxS (userOf θ j) (labU s.2.2.1 j) msg) 2)) := by
    rw [hsig, forsD_eq]
    simp only [layerSigD_eq]
    rfl
  refine ⟨h7.1 (noBot_of_fst_eqSN (by rw [e61, e51, e41]) (hp2 hs)), hv7,
    subset_trans Finset.subset_union_left hsub, ?_, subset_trans Finset.subset_union_right hsub,
    ?_, g₀, g₁, g₂, h0, h1, h2, by rw [hsigN], ?_⟩
  · intro t ht
    rcases h7.2.2.2.1 t ht with ht | ht
    · have ht3 : t ∈ s₃.2.2.1 ∨ (t.1 = j ∧ t.2.IsVal) := by
        rcases Finset.mem_union.1 (e63' ht) with ht | ht
        · rcases Finset.mem_union.1 (e53' ht) with ht | ht
          · rcases Finset.mem_union.1 (e43' ht) with ht | ht
            · exact .inl ht
            · exact .inr (isVal_of_mem_atU_vcoord ht)
          · exact .inr (isVal_of_mem_atU_vcoord ht)
        · exact .inr (isVal_of_mem_atU_vcoord ht)
      rcases ht3 with ht | ht
      · rw [hlab3] at ht
        simp only [Finset.mem_union] at ht
        rcases ht with (ht | ht) | ht
        · exact .inl ht
        · exact .inr ⟨(mem_atU_iff.1 ht).1, .inl (valOnly_sigReveal msg _ (mem_atU_iff.1 ht).2)⟩
        · exact .inr ⟨(mem_atU_iff.1 ht).1, .inr (mem_atU_iff.1 ht).2⟩
      · exact .inr ⟨ht.1, .inl ht.2⟩
    · exact .inr ⟨ht.1, .inl ht.2⟩
  · rw [h7.2.1, e64, e54, e44, hmem3]
    simp only [Function.update_self, Function.update_idem]
    rw [hgr s₅ hv5, hgr s₄ hv4, hgr s₃ hv3]
    rfl
  · intro z ω hz
    by_cases hp : ∃ p ∈ pubSet (idxS (userOf θ j) (labU s.2.2.1 j) msg)
        (lvS (userOf θ j) (labU s.2.2.1 j) msg) g₀ g₁ g₂, z = cellQ (userOf θ j) p
    · obtain ⟨p, hpm, rfl⟩ := hp
      obtain ⟨sel₀, sel₁, sel₂, e0, e1, e2, hcase⟩ := pubSet_cases hpm
      exact .inr (.inr ⟨sel₀, sel₁, sel₂, e0, e1, e2, p, hcase, rfl⟩)
    · simp only [not_exists, not_and] at hp
      have hz6 : s₇.2.1.1 z = s₆.2.1.1 z := (h7.2.2.2.2 z fun p hp' h ↦ hp p hp' h).1
      rw [hz6, e62, e52, e42, hz3, progUpdate_programH_fst] at hz
      by_cases hzd : z = cellQ (userOf θ j) (digPos msg)
      · rw [hzd, Function.update_self] at hz
        exact .inr (.inl ⟨hzd, (Option.some.inj hz).symm⟩)
      · rw [Function.update_of_ne hzd] at hz
        exact .inl hz

variable {m₀ : Finset (TPosN n) × SelMemN n}

variable (θ) in
/-- **User `j`'s signature at the event side's digest policy with the memo `h`, in the
decompressed basis** (`SignEffN`). -/
theorem htQ₂SN_signS (j : Fin n) (B : QReg) (msg : Message) (h : KeyMemo)
    (P : Set (RRegSN n (SelMemN n))) (hP : ∀ s ∈ P, NoBot s) :
    HTQ₂SN m₀ (realizeT θ (signTN (SelMemN n) cwUpdN (strPolN n) j B msg h)) P
      fun a ↦ {s' | ∃ s ∈ P, SignEffN θ j msg h s a s'} := by
  rw [signTN]
  refine htQ₂SN_revealThen m₀ θ _ _ P _ fun mem₁ ↦ ?_
  refine htQ₂SN_revealThen m₀ θ _ _ _ _ fun mem₂ ↦ ?_
  have hd : digestTN (strPolN n j) j mem₁.1 msg
      (restrictTo (atU j ((strPolN n j).need (labU mem₁.1 j) msg)) θ) =
      digestOfPair (dgS (userOf θ j) (labU mem₁.1 j) msg) :=
    congrArg digestOfPair
      (pairRN_restrictTo (mk_mem_atU j (strPol.out_mem (labU mem₁.1 j) msg)) θ)
  have hr : (digPortN (strPolN n j) j mem₁.1 msg).realize θ =
      .programH (cellQ (userOf θ j) (digPos msg)) (dgS (userOf θ j) (labU mem₁.1 j) msg) := by
    rw [realize_digPortN, ← cellOf_digPos (seedsOf θ j)]
    rfl
  have hm := tabRN_restrictTo_congr (atU_restrict (i := j) {seedC, rootC, rndC msg}) θ
  have hs₀ : (tabRN (restrictTo (atU j {seedC, rootC, rndC msg}) θ) j).publicSeed =
      (tabOf (userOf θ j)).publicSeed :=
    publicSeed_tabOf_congr (hm _ (by simp))
  have hR₀ : (tabRN (restrictTo (atU j {seedC, rootC, rndC msg}) θ) j).randomizer msg =
      (tabOf (userOf θ j)).randomizer msg :=
    randomizer_tabOf_congr (hm _ (by simp))
  dsimp only
  rw [hs₀, hR₀, hd]
  refine htQ₂SN_progThen m₀ θ _ hr _ _ _ ?_
  refine htQ₂SN_realizeT_bind m₀ θ (htQ₂SN_selOrMemoS θ j B _ _ _ ?_) fun g₀ ↦ ?_
  · rintro s₃ ⟨s₂, ⟨s₁, ⟨s, hs, -, rfl⟩, -, rfl⟩, hpr⟩
    exact hpr.2.1 (hP s hs)
  refine htQ₂SN_realizeT_bind m₀ θ (htQ₂SN_selOrMemoS θ j B _ _ _ ?_) fun g₁ ↦ ?_
  · rintro s₄ ⟨s₃, ⟨s₂, ⟨s₁, ⟨s, hs, -, rfl⟩, -, rfl⟩, hpr⟩, -, h41, -⟩
    exact noBot_of_fst_eqSN h41 (hpr.2.1 (hP s hs))
  refine htQ₂SN_realizeT_bind m₀ θ (htQ₂SN_selOrMemoS θ j B _ _ _ ?_) fun g₂ ↦ ?_
  · rintro s₅ ⟨s₄, ⟨s₃, ⟨s₂, ⟨s₁, ⟨s, hs, -, rfl⟩, -, rfl⟩, hpr⟩, -, h41, -⟩, -, h51, -⟩
    exact noBot_of_fst_eqSN (h51.trans h41) (hpr.2.1 (hP s hs))
  rw [QuantumComp₂.map_eq_bind_pure]
  refine htQ₂SN_realizeT_bind m₀ θ (htQ₂SN_publishAllS θ j B _ _ _ g₀ g₁ g₂ _) fun sig ↦
    htQ₂SN_pure _ ?_
  rintro s₇ ⟨s₆, ⟨s₅, ⟨s₄, ⟨s₃, ⟨s₂, ⟨s₁, ⟨s, hs, rfl, rfl⟩, rfl, rfl⟩, hpr⟩, hg₀, e41, e42,
    e43, e43', e44⟩, hg₁, e51, e52, e53, e53', e54⟩, hg₂, e61, e62, e63, e63', e64⟩, hsig, h7⟩
  exact ⟨s, hs, signEffN_of hpr.1 hpr.2.1 hpr.2.2 hg₀ e41 e42 e43 e43' e44 hg₁ e51 e52 e53 e53'
    e54 hg₂ e61 e62 e63 e63' e64 hsig h7 (hP s hs)⟩

end signer

end Quantum.Qrom.Sphincs.Multi

end
