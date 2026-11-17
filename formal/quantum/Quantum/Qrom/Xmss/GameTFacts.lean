module

public import Quantum.Qrom.Xmss.GameT
public import Quantum.Xmss.Assembly.PrefixRun

@[expose] public section

/-!
# The call invariants of leanXMSS's runtime-2 game, in the decompressed basis

The facts `win_imp_badQ` needs about the register at the end of the challenge prefix
(`prefixT SelMem cwUpd A` realized at `thetaOf S0 v`, run against `runtimeR`): the transcript's
signatures are the table's (`v.signature H`), the memory records their selections (`Records`) and
every hardwired chain cell has a known input (`HwKnown`). They hold in the decompressed basis
(`decR`, EndReads), where the databases have no empty cell (`NoBot`), the adversary's hash calls
and the reads keep the register, and a program call changes only its own cell. The function `H`
is the register's view `hvw s` (hardwired cell, else database): the template never programs a
message-digest cell (`cellOf_ne_msg`), so the view at those cells, which is all the
signatures and selections read (`MsgAgree`), never changes along the run.

* Support semantics (`HTQ`, `HTQ₂`), the QRPM's `PrefixRun` at `X := HashOutput`,
  `Z := HashDomain`: ports in the decompressed basis (`decR_sponge_supp`, `decR_rec_supp`,
  `decR_progH_supp`, `decR_readH_supp`), reveals, program ports, sponge-only steps, read programs
  as functions of the register (`DetQ`).
* `det_grindT`: the randomizer search answers the view's selection and records it in the memory
  (`grindMem`).
* `htQ₂_selectT`, `htQ₂_publishT`: a layer's search answers the view's selection and updates the
  memory by `grindMem`; a publication programs its positions (`ProgsSum`). `invQ_step`,
  `htQ₂_signT`: a signature keeps the invariant `InvQ log` (transcript, records, hardwired cells
  from published signatures, selected keys requested).
* `prefixFactsQ`: on every branch of the prefix, in the decompressed basis, the register is
  supported where `PreFactsQ` holds.
-/

open Matrix IPFunctor
open scoped Kronecker

namespace Quantum.Qrom.Xmss

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

attribute [local irreducible] xmssRom

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-- The register of runtime 2 with record ports at the memory `Finset HPos × M`. -/
abbrev RReg (M : Type) : Type :=
  HwReg HashOutput HashDomain (Finset HPos × M)

/-- The signature of runtime 2 with record ports at the memory `Finset HPos × M`. -/
abbrev RSpec (M : Type) : QuantumOracleSpec.{0, 0} :=
  recHwSpec HashOutput HashDomain HPos M

/-! ## Support semantics -/

section hoare

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset HPos × M)

/-- **Support semantics of a program in the decompressed basis**: from an operator supported on
registers in `P`, the branch at every leaf `p` is supported on `Q p`. -/
def HTQ {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments.{0} (RSpec M) Ω A)
    (P : Set (RReg M)) (Q : (Σ u, Ω u) → Set (RReg M)) : Prop :=
  ∀ ρ : Matrix (A × RReg M) (A × RReg M) ℂ,
    QuerySupportedOn (fun m : A × RReg M ↦ m.2) P ρ →
    ∀ p, QuerySupportedOn (fun m : p.1 × RReg M ↦ m.2) (Q p)
      (((decR (X := HashOutput) (Z := HashDomain) m₀).run .instruments y).branch p ρ)

/-- `HTQ` for programs on a fixed final register. -/
def HTQ₂ {A B : QReg} {α : Type} (y : QComp (RSpec M) A B α) (P : Set (RReg M))
    (Q : α → Set (RReg M)) : Prop :=
  ∀ ρ : Matrix (A × RReg M) (A × RReg M) ℂ,
    QuerySupportedOn (fun m : A × RReg M ↦ m.2) P ρ →
    ∀ a, QuerySupportedOn (fun m : B × RReg M ↦ m.2) (Q a)
      (((decR (X := HashOutput) (Z := HashDomain) m₀).run₂ .instruments y).branch a ρ)

variable {m₀}

theorem HTQ.mono {Ω : QReg → Type} {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (RSpec M) Ω A}
    {P P' : Set (RReg M)} {Q Q' : (Σ u, Ω u) → Set (RReg M)} (h : HTQ m₀ y P Q)
    (hP : P' ⊆ P) (hQ : ∀ p, Q p ⊆ Q' p) : HTQ m₀ y P' Q' :=
  fun ρ hρ p ↦ (h ρ (hρ.mono hP) p).mono (hQ p)

theorem HTQ₂.mono {A B : QReg} {α : Type} {y : QComp (RSpec M) A B α}
    {P P' : Set (RReg M)} {Q Q' : α → Set (RReg M)} (h : HTQ₂ m₀ y P Q) (hP : P' ⊆ P)
    (hQ : ∀ a, Q a ⊆ Q' a) : HTQ₂ m₀ y P' Q' :=
  fun ρ hρ a ↦ (h ρ (hρ.mono hP) a).mono (hQ a)

theorem htQ₂_iff {A B : QReg} {α : Type} (y : QComp (RSpec M) A B α) (P : Set (RReg M))
    (Q : α → Set (RReg M)) : HTQ₂ m₀ y P Q ↔ HTQ m₀ y P fun p ↦ Q p.2.2 := by
  constructor
  · intro h ρ hρ p
    obtain ⟨u, hu, a⟩ := p
    subst hu
    exact h ρ hρ a
  · intro h ρ hρ a
    exact h ρ hρ ⟨B, rfl, a⟩

theorem htQ_of_htQ₂ {A B : QReg} {α : Type} {y : QComp (RSpec M) A B α}
    {P : Set (RReg M)} {Q : α → Set (RReg M)} (h : HTQ₂ m₀ y P Q) :
    HTQ m₀ y P fun p ↦ Q p.2.2 :=
  (htQ₂_iff y P Q).mp h

theorem htQ₂_of_htQ {A B : QReg} {α : Type} {y : QComp (RSpec M) A B α}
    {P : Set (RReg M)} {Q : α → Set (RReg M)} (h : HTQ m₀ y P fun p ↦ Q p.2.2) :
    HTQ₂ m₀ y P Q :=
  (htQ₂_iff y P Q).mpr h

theorem htQ_pure {Ω : QReg → Type} {A : QReg} (y : Ω A) {P : Set (RReg M)}
    {Q : (Σ u, Ω u) → Set (RReg M)} (h : P ⊆ Q ⟨A, y⟩) :
    HTQ m₀ (QuantumComp.pure (L := LocalSig.instruments.{0}) (spec := RSpec M) y) P Q := by
  classical
  intro ρ hρ p
  rw [QuantumRuntime.run_pure]
  by_cases hp : p = ⟨A, y⟩
  · subst hp
    rw [DSubInstrument.branch_ret_self]
    exact hρ.mono h
  · rw [DSubInstrument.branch_ret_of_ne _ hp]
    exact querySupportedOn_zero _ _

theorem htQ₂_pure {A : QReg} {α : Type} (a : α) {P : Set (RReg M)} {Q : α → Set (RReg M)}
    (h : P ⊆ Q a) : HTQ₂ m₀ (QuantumComp₂.pure a : QComp (RSpec M) A A α) P Q := by
  intro ρ hρ a'
  rw [QuantumRuntime.run₂_pure]
  by_cases ha : a' = a
  · subst ha
    rw [SubInstrument.branch_pure_self]
    exact hρ.mono h
  · rw [SubInstrument.branch_pure_of_ne ha]
    exact querySupportedOn_zero _ _

theorem HTQ.bind {Ω Ω' : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (RSpec M) Ω A}
    {P : Set (RReg M)} {Q : (Σ u, Ω u) → Set (RReg M)} (hx : HTQ m₀ x P Q)
    {k : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (RSpec M) Ω' u}
    {R : (Σ u, Ω' u) → Set (RReg M)} (hk : ∀ u a, HTQ m₀ (k u a) (Q ⟨u, a⟩) R) :
    HTQ m₀ (x.bind k) P R := by
  intro ρ hρ p
  rw [QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun q ↦ hk q.1 q.2 _ (hx ρ hρ q) p

theorem HTQ₂.bind {A B C : QReg} {α β : Type} {x : QComp (RSpec M) A B α}
    {P : Set (RReg M)} {Q : α → Set (RReg M)} (hx : HTQ₂ m₀ x P Q)
    {k : α → QComp (RSpec M) B C β} {R : β → Set (RReg M)}
    (hk : ∀ a, HTQ₂ m₀ (k a) (Q a) R) : HTQ₂ m₀ (x.bind k) P R := by
  intro ρ hρ b
  erw [QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun a ↦ hk a _ (hx ρ hρ a) b

theorem htQ_primBind {Ω : QReg → Type} {A : QReg} (o : LocalSig.instruments.{0}.Op A)
    {k : (b : LocalSig.instruments.{0}.Outcome o) →
      QuantumComp LocalSig.instruments.{0} (RSpec M) Ω (LocalSig.instruments.{0}.next o b)}
    {P : Set (RReg M)} {Q : (Σ u, Ω u) → Set (RReg M)} (hk : ∀ b, HTQ m₀ (k b) P Q) :
    HTQ m₀ (QuantumComp.primBind o k) P Q := by
  intro ρ hρ p
  rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun b ↦ hk b _ (QuerySupportedOn.amplify_snd (q := id) hρ _) p

/-- **A local operation keeps the register.** -/
theorem htQ₂_act_bind {A B C : QReg} {α β : Type} (p : SubInstrument A B β)
    {k : β → QComp (RSpec M) B C α} {P : Set (RReg M)} {Q : α → Set (RReg M)}
    (hk : ∀ b, HTQ₂ m₀ (k b) P Q) : HTQ₂ m₀ ((QComp.act p).bind k) P Q := by
  intro ρ hρ a
  rw [QuantumRuntime.run₂_act_bind]
  erw [DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun b ↦ hk b _ (QuerySupportedOn.amplify_snd (q := id) hρ _) a

theorem htQ₂_act {A B : QReg} {β : Type} (p : SubInstrument A B β) (P : Set (RReg M)) :
    HTQ₂ m₀ (QComp.act (spec := RSpec M) p) P fun _ ↦ P := by
  rw [← QuantumComp₂.bind_pure (QComp.act (spec := RSpec M) p)]
  exact htQ₂_act_bind p fun b ↦ htQ₂_pure b subset_rfl

/-- A call whose step moves the support from `P` to `P' r` at the result `r`. -/
theorem htQ_queryBind {Ω : QReg → Type} {A : QReg} (i : (RSpec M).Port)
    (E : QReg) (ℓ : A ≃ (RSpec M).In i × E)
    {k : (RSpec M).Result i →
      QuantumComp LocalSig.instruments.{0} (RSpec M) Ω (QReg.of ((RSpec M).Out i × E))}
    {P : Set (RReg M)} (P' : (RSpec M).Result i → Set (RReg M))
    {Q : (Σ u, Ω u) → Set (RReg M)}
    (hstep : ∀ r (σ : Matrix ((RSpec M).In i × RReg M) ((RSpec M).In i × RReg M) ℂ),
      QuerySupportedOn (fun m : (RSpec M).In i × RReg M ↦ m.2) P σ →
        QuerySupportedOn (fun m : (RSpec M).Out i × RReg M ↦ m.2) (P' r)
          (((decR (X := HashOutput) (Z := HashDomain) m₀).step i).branch r σ))
    (hk : ∀ r, HTQ m₀ (k r) (P' r) Q) : HTQ m₀ (QuantumComp.queryBind i E ℓ k) P Q := by
  intro ρ hρ p
  rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun r ↦ hk r _
    (querySupportedOn_queryStep_imp (decR (X := HashOutput) (Z := HashDomain) m₀) i E ℓ r P
      (P' r) (hstep r) hρ) p

theorem htQ₂_queryBind {A B : QReg} {α : Type} (i : (RSpec M).Port)
    (E : QReg) (ℓ : A ≃ (RSpec M).In i × E)
    {k : (RSpec M).Result i → QComp (RSpec M) (QReg.of ((RSpec M).Out i × E)) B α}
    {P : Set (RReg M)} (P' : (RSpec M).Result i → Set (RReg M)) {Q : α → Set (RReg M)}
    (hstep : ∀ r (σ : Matrix ((RSpec M).In i × RReg M) ((RSpec M).In i × RReg M) ℂ),
      QuerySupportedOn (fun m : (RSpec M).In i × RReg M ↦ m.2) P σ →
        QuerySupportedOn (fun m : (RSpec M).Out i × RReg M ↦ m.2) (P' r)
          (((decR (X := HashOutput) (Z := HashDomain) m₀).step i).branch r σ))
    (hk : ∀ r, HTQ₂ m₀ (k r) (P' r) Q) :
    HTQ₂ m₀ (QuantumComp₂.queryBind (L := LocalSig.instruments) i E ℓ k) P Q := by
  intro ρ hρ a
  erw [QuantumRuntime.run₂_queryBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun r ↦ hk r _
    (querySupportedOn_queryStep_imp (decR (X := HashOutput) (Z := HashDomain) m₀) i E ℓ r P
      (P' r) (hstep r) hρ) a

variable (m₀) in
/-- **Every run keeps `NoBot`.** -/
theorem htQ_noBot {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (RSpec M) Ω A) :
    HTQ m₀ y {s | NoBot s} fun _ ↦ {s | NoBot s} :=
  fun _ hρ p ↦ querySupportedOn_run (decR (X := HashOutput) (Z := HashDomain) m₀) {s | NoBot s}
    (decR_step_noBot m₀) .instruments y hρ p

theorem HTQ₂.and_noBot {A B : QReg} {α : Type} {y : QComp (RSpec M) A B α}
    {P : Set (RReg M)} {Q : α → Set (RReg M)} (h : HTQ₂ m₀ y P Q)
    (hP : ∀ s ∈ P, NoBot s) : HTQ₂ m₀ y P fun a ↦ Q a ∩ {s | NoBot s} :=
  fun ρ hρ a ↦ querySupportedOn_inter (h ρ hρ a)
    (htQ₂_of_htQ (Q := fun _ ↦ {s | NoBot s}) (htQ_noBot m₀ y) ρ (hρ.mono hP) a)

end hoare

/-! ## The ports in the decompressed basis -/

section ports

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset HPos × M)

/-- **A sponge port keeps the decompressed register.** -/
theorem decR_sponge_supp (i : SpongePort) (r : (RSpec M).Result (.inl (.inl (.inl i))))
    (P : Set (RReg M))
    (σ : Matrix ((RSpec M).In (.inl (.inl (.inl i))) × RReg M)
      ((RSpec M).In (.inl (.inl (.inl i))) × RReg M) ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpec M).In (.inl (.inl (.inl i))) × RReg M ↦ m.2) P σ) :
    QuerySupportedOn (fun m : (RSpec M).Out (.inl (.inl (.inl i))) × RReg M ↦ m.2) P
      (((decR (X := HashOutput) (Z := HashDomain) m₀).step (.inl (.inl (.inl i)))).branch r σ) := by
  rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inl (.inl i)) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
  cases i <;> (rw [snd_eq_of_hwPort _ m' m hK]; exact hm)

omit [Fintype M] [DecidableEq M] in
/-- The registers after recording `T` from `P` with memory `mem` before. -/
def RecSetQ (P : Set (RReg M)) (T : Finset HPos) (mem : Finset HPos × M) : Set (RReg M) :=
  {s | ∃ s₀ ∈ P, s₀.2.2 = mem ∧ s = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ T, s₀.2.2.2))}

/-- **A record of `T` adds `T` to the label** and keeps everything else. -/
theorem decR_rec_supp (T : Finset HPos) (mem : (RSpec M).Result (.inr T)) (P : Set (RReg M))
    (σ : Matrix ((RSpec M).In (.inr T) × RReg M) ((RSpec M).In (.inr T) × RReg M) ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpec M).In (.inr T) × RReg M ↦ m.2) P σ) :
    QuerySupportedOn (fun m : (RSpec M).Out (.inr T) × RReg M ↦ m.2) (RecSetQ P T mem)
      (((decR (X := HashOutput) (Z := HashDomain) m₀).step (.inr T)).branch mem σ) := by
  obtain ⟨lab, mm⟩ := mem
  rw [decR_branch_apply m₀ (.inr T) (lab, mm) _ (recStep_branch T (lab, mm))]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
  obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
  exact ⟨m.2, hm, hp, Prod.ext (dbs_one_dec_eq hR) hφ⟩

omit [Fintype M] [DecidableEq M] in
/-- **The effect of hardwiring the `h`-cell `z` to `a`** on the decompressed register: the
hardwired cells updated, no empty cell kept, every other `h` database cell kept. -/
def ProgRelH (z : HashDomain) (a : HashOutput) (s s' : RReg M) : Prop :=
  s'.2 = (progUpdate (.programH z a) s.2.1, s.2.2) ∧ (NoBot s → NoBot s') ∧
    ∀ z', z' ≠ z → s'.1.1 z' = s.1.1 z'

/-- **A program call of an `h`-cell in the decompressed basis** (`ProgRelH`). -/
theorem decR_progH_supp (z : HashDomain) (a : HashOutput)
    (r : (RSpec M).Result (.inl (.inr (.programH z a)))) (P : Set (RReg M))
    (σ : Matrix ((RSpec M).In (.inl (.inr (.programH z a))) × RReg M)
      ((RSpec M).In (.inl (.inr (.programH z a))) × RReg M) ℂ)
    (hσ : QuerySupportedOn
      (fun m : (RSpec M).In (.inl (.inr (.programH z a))) × RReg M ↦ m.2) P σ) :
    QuerySupportedOn (fun m : (RSpec M).Out (.inl (.inr (.programH z a))) × RReg M ↦ m.2)
      {s' | ∃ s ∈ P, ProgRelH z a s s'}
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
def readFinH (s : RReg M) (z : HashDomain) (upd : M → Option HashOutput → M) : RReg M :=
  (s.1, s.2.1, (s.2.2.1, upd s.2.2.2 ((hwView s.2.1 s.1).1 z)))

/-- **A read of an `h`-cell in the decompressed basis**: it returns the view's cell with the
memory before, keeps the databases and hardwired cells, and updates the memory. -/
theorem decR_readH_supp (z : HashDomain) (upd : M → Option HashOutput → M)
    (r : (RSpec M).Result (.inl (.inl (.inr (liftRead (.readH z upd)))))) (U : Set (RReg M))
    (σ : Matrix ((RSpec M).In (.inl (.inl (.inr (liftRead (.readH z upd))))) × RReg M)
      ((RSpec M).In (.inl (.inl (.inr (liftRead (.readH z upd))))) × RReg M) ℂ)
    (hσ : QuerySupportedOn
      (fun p : (RSpec M).In (.inl (.inl (.inr (liftRead (.readH z upd))))) × RReg M ↦ p.2) U σ) :
    QuerySupportedOn
      (fun p : (RSpec M).Out (.inl (.inl (.inr (liftRead (.readH z upd))))) × RReg M ↦ p.2)
      {s' | ∃ s ∈ U, r = liftAns s (.readH z upd) ∧ s' = readFinH s z upd}
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

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset HPos × M) (θ : HPos → Digest)

theorem htQ_realizeT_bind {Ω Ω' : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (XSpec M) Ω A}
    {g : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (XSpec M) Ω' u}
    {P : Set (RReg M)} {Q : (Σ u, Ω u) → Set (RReg M)} {R : (Σ u, Ω' u) → Set (RReg M)}
    (hx : HTQ m₀ (realizeT θ x) P Q) (hg : ∀ u a, HTQ m₀ (realizeT θ (g u a)) (Q ⟨u, a⟩) R) :
    HTQ m₀ (realizeT θ (x.bind g)) P R := by
  rw [realizeT_bind]
  exact HTQ.bind hx hg

theorem htQ₂_realizeT_bind {A B C : QReg} {α β : Type} {x : QComp (XSpec M) A B α}
    {k : α → QComp (XSpec M) B C β} {P : Set (RReg M)} {Q : α → Set (RReg M)}
    {R : β → Set (RReg M)} (hx : HTQ₂ m₀ (realizeT θ x) P Q)
    (hk : ∀ a, HTQ₂ m₀ (realizeT θ (k a)) (Q a) R) : HTQ₂ m₀ (realizeT θ (x.bind k)) P R := by
  rw [realizeT_bind₂]
  exact HTQ₂.bind hx hk

/-- **A realized reveal is the record port**: the values of `θ` on `T`, the label grown by `T`. -/
theorem htQ₂_revealThen {B C : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals HD T × (Finset HPos × M) → QComp (XSpec M) B C α)
    (P : Set (RReg M)) (Q : α → Set (RReg M))
    (hk : ∀ mem, HTQ₂ m₀ (realizeT θ (k (restrictTo T θ, mem)))
      {s | ∃ s₀ ∈ P, s₀.2.2 = mem ∧ s = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ T, s₀.2.2.2))} Q) :
    HTQ₂ m₀ (realizeT θ (revealThen goodQ T k)) P Q := by
  have e : realizeT θ (revealThen goodQ T k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpec M) (.inr T) B
        (Equiv.uniqueProd B Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((RSpec M).Out (.inr T) × B)) (B := B)
            (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ (k (restrictTo T θ, mem)) :=
    rfl
  rw [e]
  exact htQ₂_queryBind (.inr T) B _ (RecSetQ P T) (fun mem σ hσ ↦ decR_rec_supp m₀ T mem P σ hσ)
    fun mem ↦ htQ₂_act_bind _ fun _ ↦ hk mem

/-- **A realized program port of a structural position** moves the register by `ProgRelH`. -/
theorem htQ₂_progThen {B C : QReg} {α : Type} (p : Pos) (hp : p.IsStruct) (S0 : MasterSeed)
    (k : QComp (XSpec M) B C α) (P : Set (RReg M)) (Q : α → Set (RReg M))
    (hk : HTQ₂ m₀ (realizeT θ k)
      {s' | ∃ s ∈ P, ProgRelH (cellOf S0 p (tabOf θ)) (tabOf θ p) s s'} Q) :
    HTQ₂ m₀ (realizeT θ (progThen (progT p) trivial k)) P Q := by
  have e : realizeT θ (progThen (progT p) trivial k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpec M)
        (.inl (.inr ((progT p).realize θ))) B (Equiv.uniqueProd B Unit).symm fun _ ↦
          (QComp.act (A := QReg.of ((RSpec M).Out (.inl (.inr ((progT p).realize θ))) × B))
            (B := B) (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ k :=
    rfl
  rw [e]
  have hr := realize_progT hp S0 θ
  revert hk
  generalize (progT p).realize θ = c at hr ⊢
  subst hr
  intro hk
  exact htQ₂_queryBind _ B _ (fun _ ↦ {s' | ∃ s ∈ P, ProgRelH _ _ s s'})
    (fun r σ hσ ↦ decR_progH_supp m₀ _ _ r P σ hσ) fun _ ↦ htQ₂_act_bind _ fun _ ↦ hk

/-- **Sponge-only steps keep every register set**. -/
theorem htQ_sponge {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (spongeSpec HashOutput HashDomain) Ω A)
    (P : Set (RReg M)) :
    HTQ m₀ (realizeT θ (readLift goodQ (y.liftOrdinary
      (t := hwReadCmdSpec HashOutput HashDomain M)))) P fun _ ↦ P := by
  induction y using QuantumComp.inductionOn with
  | pure A y => exact htQ_pure y subset_rfl
  | primBind A o k ih =>
    have e : realizeT θ (readLift goodQ ((QuantumComp.primBind o k).liftOrdinary
        (t := hwReadCmdSpec HashOutput HashDomain M))) =
        QuantumComp.primBind o fun b ↦
          realizeT θ (readLift goodQ ((k b).liftOrdinary
            (t := hwReadCmdSpec HashOutput HashDomain M))) :=
      rfl
    rw [e]
    exact htQ_primBind o fun b ↦ ih b
  | queryBind A i E ℓ k ih =>
    have e : realizeT θ (readLift goodQ ((QuantumComp.queryBind i E ℓ k).liftOrdinary
        (t := hwReadCmdSpec HashOutput HashDomain M))) =
        QuantumComp.queryBind (spec := RSpec M) (.inl (.inl (.inl i))) E ℓ
          fun r ↦ realizeT θ (readLift goodQ ((k r).liftOrdinary
            (t := hwReadCmdSpec HashOutput HashDomain M))) :=
      rfl
    rw [e]
    exact htQ_queryBind _ E ℓ (fun _ ↦ P) (fun r σ hσ ↦ decR_sponge_supp m₀ i r P σ hσ)
      fun r ↦ ih r

end template

/-! ## Read programs as functions of the register -/

section det

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset HPos × M) (θ : HPos → Digest)

/-- **A read program answers as a function of the register**: from registers without empty cell,
run lifted, realized and in the decompressed basis, it returns `out s` and leaves `fin s`. -/
def DetQ {B : QReg} {α : Type} (y : QComp (hwReadSpec HashOutput HashDomain M) B B α)
    (out : RReg M → α) (fin : RReg M → RReg M) : Prop :=
  ∀ P : Set (RReg M), (∀ s ∈ P, NoBot s) →
    HTQ₂ m₀ (realizeT θ (readLiftQ goodQ y)) P fun a ↦ {s' | ∃ s ∈ P, a = out s ∧ s' = fin s}

variable {m₀ θ}

theorem DetQ.congr {B : QReg} {α : Type} {y : QComp (hwReadSpec HashOutput HashDomain M) B B α}
    {out out' : RReg M → α} {fin fin' : RReg M → RReg M} (h : DetQ m₀ θ y out fin)
    (e : ∀ s, NoBot s → out s = out' s ∧ fin s = fin' s) : DetQ m₀ θ y out' fin' := by
  intro P hP
  refine (h P hP).mono subset_rfl fun a ↦ ?_
  rintro s' ⟨s, hs, ha, rfl⟩
  obtain ⟨e₁, e₂⟩ := e s (hP s hs)
  exact ⟨s, hs, ha.trans e₁, e₂⟩

theorem detQ_pure {B : QReg} {α : Type} (a : α) :
    DetQ m₀ θ (QuantumComp₂.pure a : QComp (hwReadSpec HashOutput HashDomain M) B B α)
      (fun _ ↦ a) fun s ↦ s :=
  fun _ _ ↦ htQ₂_pure a fun s hs ↦ ⟨s, hs, rfl, rfl⟩

theorem DetQ.bind {B : QReg} {α β : Type} {x : QComp (hwReadSpec HashOutput HashDomain M) B B α}
    {out : RReg M → α} {fin : RReg M → RReg M} (hx : DetQ m₀ θ x out fin)
    {k : α → QComp (hwReadSpec HashOutput HashDomain M) B B β} {out' : α → RReg M → β}
    {fin' : α → RReg M → RReg M} (hk : ∀ a, DetQ m₀ θ (k a) (out' a) (fin' a)) :
    DetQ m₀ θ (x.bind k) (fun s ↦ out' (out s) (fin s)) fun s ↦ fin' (out s) (fin s) := by
  intro P hP
  rw [readLift_bind₂, realizeT_bind₂]
  refine HTQ₂.bind ((hx P hP).and_noBot hP) fun a ↦
    ((hk a) _ fun s hs ↦ hs.2).mono subset_rfl fun b ↦ ?_
  rintro s'' ⟨s', ⟨⟨s, hs, rfl, rfl⟩, -⟩, rfl, rfl⟩
  exact ⟨s, hs, rfl, rfl⟩

/-- **A read of an `h`-cell answers the view's cell with the memory and updates the memory.** -/
theorem detQ_readH (z : HashDomain) (upd : M → Option HashOutput → M) (B : QReg) :
    DetQ m₀ θ (readCall (.readH z upd) B) (fun s ↦ ((hwView s.2.1 s.1).1 z, s.2.2.2))
      fun s ↦ readFinH s z upd := by
  intro P _ ρ hρ a
  rw [realizeT_readLift_readCall]
  erw [QuantumRuntime.run₂_queryBind, DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun r ↦ ?_
  have hq := querySupportedOn_queryStep_imp (decR (X := HashOutput) (Z := HashDomain) m₀)
    (.inl (.inl (.inr (liftRead (.readH z upd))))) B
    (Equiv.uniqueProd B Unit).symm r P
    {s' | ∃ s ∈ P, r = liftAns s (.readH z upd) ∧ s' = readFinH s z upd}
    (fun τ hτ ↦ decR_readH_supp m₀ z upd r P τ hτ) hρ
  rw [QuantumRuntime.run₂_act_bind]
  erw [DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun u ↦ ?_
  rw [QuantumRuntime.run₂_pure]
  by_cases ha : a = lowerRes (.readH z upd) r
  · subst ha
    rw [SubInstrument.branch_pure_self, LinearMap.id_apply, DSubInstrument.branch_frame_apply]
    refine (QuerySupportedOn.amplify_snd (q := fun s : RReg M ↦ s) hq _).mono ?_
    rintro s' ⟨s, hs, hr, rfl⟩
    exact ⟨s, hs, by rw [hr, lowerRes_liftAns]; rfl, rfl⟩
  · rw [SubInstrument.branch_pure_of_ne ha]
    exact querySupportedOn_zero _ _

end det

/-! ## The randomizer search as a function of the view -/

section grind

/-- **The hash of the register's view**: the hardwired value of a cell, else its database
value (`0` on an empty cell, which the decompressed registers do not have). -/
def hvw {M : Type} (s : RReg M) (z : HashDomain) : HashOutput :=
  ((hwView s.2.1 s.1).1 z).getD 0

theorem hwView_eq_some_hvw {M : Type} {s : RReg M} (hs : NoBot s) (z : HashDomain) :
    (hwView s.2.1 s.1).1 z = some (hvw s z) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (or_isSome (s.2.1.1 z) (hs.1 z))
  show (s.2.1.1 z).or (s.1.1 z) = some (((s.2.1.1 z).or (s.1.1 z)).getD 0)
  rw [ha]
  rfl

/-- **The memory after the randomizer search** against `H` from `m`: each trial's read updates the
memory with `cwUpd`, until a codeword. -/
def grindMem (H : HashDomain → HashOutput) (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (base : Randomizer) : ℕ → ℕ → SelMem → SelMem
  | 0, _, m => m
  | n + 1, trial, m =>
    match Codeword.decode (truncateHash (H (trialCell P l e message base trial))) with
    | some _ => cwUpd l e (trialCell P l e message base trial) m
        (some (H (trialCell P l e message base trial)))
    | none => grindMem H P l e message base n (trial + 1) (cwUpd l e
        (trialCell P l e message base trial) m (some (H (trialCell P l e message base trial))))

variable {m₀ : Finset HPos × SelMem} {θ : HPos → Digest}

/-- **The randomizer search answers the view's selection** and updates the memory by `grindMem`.
-/
theorem det_grindT (v : QTable) (B : QReg) (l : Layer) (e : KeyIndex) (message : MsgBytes)
    (base : Randomizer) (n trial : ℕ) :
    DetQ m₀ θ (grindT SelMem cwUpd v.param B l e message base n trial)
      (fun s ↦ v.selectFrom (hvw s) l e message base n trial)
      (fun s ↦ (s.1, s.2.1, (s.2.2.1, grindMem (hvw s) v.param l e message base n trial
        s.2.2.2))) := by
  induction n generalizing trial with
  | zero => exact (detQ_pure none).congr fun s _ ↦ ⟨rfl, rfl⟩
  | succ n ih =>
    rw [grindT]
    have aux : ∀ r : Option HashOutput × SelMem, DetQ m₀ θ
        (match Codeword.decode (truncateHash (r.1.getD 0)) with
          | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
          | none => grindT SelMem cwUpd v.param B l e message base n (trial + 1))
        (fun s ↦ match Codeword.decode (truncateHash (r.1.getD 0)) with
          | some x => some (base + BitVec.ofNat digestBits trial, x)
          | none => v.selectFrom (hvw s) l e message base n (trial + 1))
        (fun s ↦ match Codeword.decode (truncateHash (r.1.getD 0)) with
          | some _ => s
          | none => (s.1, s.2.1, (s.2.2.1, grindMem (hvw s) v.param l e message base n
              (trial + 1) s.2.2.2))) := by
      intro r
      rcases Codeword.decode (truncateHash (r.1.getD 0)) with _ | x
      · exact ih (trial + 1)
      · exact detQ_pure _
    refine ((detQ_readH _ _ B).bind aux).congr fun s hs ↦ ⟨?_, ?_⟩
    · simp only [readFinH, hwView_eq_some_hvw hs, Option.getD_some, QTable.selectFrom]
      rfl
    · simp only [readFinH, hwView_eq_some_hvw hs, Option.getD_some, grindMem]
      rcases Codeword.decode (truncateHash (hvw s (trialCell v.param l e message base trial)))
        with _ | x <;> rfl

end grind

/-! ## The selections against views that agree on the message-digest cells -/

section msg

variable (v : QTable)

/-- Two hash functions agree on the message-digest cells under `v`'s parameter. -/
def MsgAgree (H H' : HashDomain → HashOutput) : Prop :=
  ∀ l e d, H (cell v.param (.msg l e) d) = H' (cell v.param (.msg l e) d)

variable {v} {H H' : HashDomain → HashOutput}

theorem MsgAgree.trans {H'' : HashDomain → HashOutput} (h : MsgAgree v H H')
    (h' : MsgAgree v H' H'') : MsgAgree v H H'' :=
  fun l e d ↦ (h l e d).trans (h' l e d)

theorem selectFrom_congr (h : MsgAgree v H H') (l : Layer) (e : KeyIndex) (msg : MsgBytes)
    (base : Randomizer) : ∀ n trial,
    v.selectFrom H l e msg base n trial = v.selectFrom H' l e msg base n trial
  | 0, _ => rfl
  | n + 1, trial => by
    simp only [QTable.selectFrom, QTable.messageDigest,
      selectFrom_congr h l e msg base n (trial + 1)]
    rw [h l e (msg, base + BitVec.ofNat digestBits trial)]

theorem select_congr (h : MsgAgree v H H') (l : Layer) (e : KeyIndex) (msg : MsgBytes)
    (base : Randomizer) : v.select H l e msg base = v.select H' l e msg base :=
  selectFrom_congr h l e msg base _ _

theorem signature_congr (h : MsgAgree v H H') (r : SigningRequest) :
    v.signature H r = v.signature H' r := by
  simp only [QTable.signature, QTable.bottomSignature, QTable.topSignature,
    QTable.layerSignature, select_congr h]

theorem disclosures_congr (h : MsgAgree v H H') (reqs : List SigningRequest) :
    v.disclosures H reqs = v.disclosures H' reqs := by
  simp only [QTable.disclosures, QTable.disclosedBy, select_congr h]

theorem records_congr (h : MsgAgree v H H') (m : SelMem) (req : SigningRequest) :
    Records v H m req ↔ Records v H' m req := by
  simp only [Records, select_congr h, QTable.messageDigest]
  refine forall₂_congr fun l sel ↦ imp_congr_right fun _ ↦ ?_
  rw [h l (keyIndexOnLayer req.leafIndex l) (layerMsg v req l, sel.1)]

theorem cellOf_ne_msg (S0 : MasterSeed) {p : Pos} (hp : p.IsStruct) (P : PublicParameter)
    (l : Layer) (e : KeyIndex) (d : Payload (.msg l e)) : cellOf S0 p v ≠ cell P (.msg l e) d := by
  intro hc
  have h1 := slotOf_cellOf S0 v p
  rw [hc, slotOf_cell P (s := .msg l e) trivial d] at h1
  have h2 := Option.some.inj h1
  cases p with
  | chain => cases h2
  | leaf => cases h2
  | node => cases h2
  | seed | param | prf | rndBottom | rndTop => exact absurd hp id

end msg

/-! ## The memory after the randomizer search -/

section grindMem

theorem valid_of_decode {d : Digest} {x : Encoding} (h : Codeword.decode d = some x) :
    Codeword.Valid d := by
  unfold Codeword.decode at h
  split_ifs at h with hv
  exact hv

theorem not_valid_of_decode {d : Digest} (h : Codeword.decode d = none) : ¬Codeword.Valid d := by
  unfold Codeword.decode at h
  split_ifs at h with hv
  exact hv

variable (H : HashDomain → HashOutput) (P : PublicParameter) (l : Layer) (e : KeyIndex)
  (msg : MsgBytes) (base : Randomizer)

/-- The search changes only its key's memory. -/
theorem grindMem_of_ne {l' : Layer} {e' : KeyIndex} (h : ¬(l' = l ∧ e' = e)) :
    ∀ n trial m, grindMem H P l e msg base n trial m l' e' = m l' e'
  | 0, _, _ => rfl
  | n + 1, trial, m => by
    have hc : ∀ m' : SelMem, cwUpd l e (trialCell P l e msg base trial) m'
        (some (H (trialCell P l e msg base trial))) l' e' = m' l' e' := fun m' ↦ by
      show (if m' l e = none then cwSel m' l e _ _ else m') l' e' = m' l' e'
      split_ifs
      · unfold cwSel
        split_ifs
        · exact SelMem.select_of_ne _ _ _ h
        · rfl
      · rfl
    simp only [grindMem]
    rcases Codeword.decode (truncateHash (H (trialCell P l e msg base trial))) with _ | x
    · exact (grindMem_of_ne h n (trial + 1) _).trans (hc m)
    · exact hc m

/-- The search keeps a selected key's memory. -/
theorem grindMem_of_some {c : HashDomain × Digest} :
    ∀ n trial m, m l e = some c → grindMem H P l e msg base n trial m l e = some c
  | 0, _, _, hm => hm
  | n + 1, trial, m, hm => by
    have hc : cwUpd l e (trialCell P l e msg base trial) m
        (some (H (trialCell P l e msg base trial))) = m := by
      show (if m l e = none then cwSel m l e _ _ else m) = m
      rw [ite_eq_right (by rw [hm]; exact Option.some_ne_none c)]
    simp only [grindMem, hc]
    rcases Codeword.decode (truncateHash (H (trialCell P l e msg base trial))) with _ | x
    · exact grindMem_of_some n (trial + 1) m hm
    · exact hm

theorem grindMem_of_ne_none {l' : Layer} {e' : KeyIndex} (n trial : ℕ) (m : SelMem)
    (hm : m l' e' ≠ none) : grindMem H P l e msg base n trial m l' e' = m l' e' := by
  by_cases h : l' = l ∧ e' = e
  · obtain ⟨rfl, rfl⟩ := h
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hm
    rw [hc]
    exact grindMem_of_some H P l' e' msg base n trial m hc
  · exact grindMem_of_ne H P l e msg base h n trial m

/-- **The search records its selection** in an unselected key's memory. -/
theorem grindMem_of_select (v : QTable) : ∀ n trial (m : SelMem) {ρ : Randomizer}
    {x : Encoding}, m l e = none → v.selectFrom H l e msg base n trial = some (ρ, x) →
    grindMem H v.param l e msg base n trial m l e =
      some (cell v.param (.msg l e) (msg, ρ), truncateHash (H (cell v.param (.msg l e) (msg, ρ))))
  | 0, _, _, _, _, _, h => by simp [QTable.selectFrom] at h
  | n + 1, trial, m, ρ, x, hm, h => by
    rw [QTable.selectFrom] at h
    simp only [grindMem]
    change (match Codeword.decode (truncateHash (H (trialCell v.param l e msg base trial))) with
      | some x => some (base + BitVec.ofNat digestBits trial, x)
      | none => v.selectFrom H l e msg base n (trial + 1)) = _ at h
    rcases hd : Codeword.decode (truncateHash (H (trialCell v.param l e msg base trial)))
      with _ | x₀
    · rw [hd] at h
      have hc : cwUpd l e (trialCell v.param l e msg base trial) m
          (some (H (trialCell v.param l e msg base trial))) = m := by
        rw [cwUpd_some_of_none l e _ hm, cwSel, ite_eq_right (not_valid_of_decode hd)]
      dsimp only
      rw [hc]
      exact grindMem_of_select v n (trial + 1) m hm h
    · rw [hd] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      dsimp only
      rw [cwUpd_some_of_none l e _ hm, cwSel, ite_eq_left (valid_of_decode hd), SelMem.select_self]
      rfl

end grindMem

/-! ## Programs, searches and publications in the decompressed basis -/

section steps

variable (S0 : MasterSeed) (v : QTable)

theorem hvw_eq {M : Type} {s s' : RReg M} (h₁ : s'.1 = s.1) (h₂ : s'.2.1 = s.2.1) :
    hvw s' = hvw s := by
  unfold hvw
  rw [h₁, h₂]

theorem noBot_of_eq {M : Type} {s s' : RReg M} (h₁ : s'.1 = s.1) (hs : NoBot s) : NoBot s' := by
  show Quantum.Xmss.Assembly.NoBotDb s'.1
  rw [h₁]
  exact hs

/-- **The summary of program calls of the positions `ps`**: no empty cell kept, the inner memory
kept, and the hardwired and database `h`-cells kept off the positions' cells. -/
def ProgsSum {M : Type} (ps : List Pos) (s s' : RReg M) : Prop :=
  (NoBot s → NoBot s') ∧ s'.2.2.2 = s.2.2.2 ∧
    ∀ z, (∀ p ∈ ps, z ≠ cellOf S0 p v) → s'.2.1.1 z = s.2.1.1 z ∧ s'.1.1 z = s.1.1 z

theorem hvw_of_progsSum {M : Type} {ps : List Pos} {s s' : RReg M} (h : ProgsSum S0 v ps s s')
    {z : HashDomain} (hz : ∀ p ∈ ps, z ≠ cellOf S0 p v) : hvw s' z = hvw s z := by
  obtain ⟨h₁, h₂⟩ := h.2.2 z hz
  show ((s'.2.1.1 z).or (s'.1.1 z)).getD 0 = ((s.2.1.1 z).or (s.1.1 z)).getD 0
  rw [h₁, h₂]

theorem msgAgree_of_progsSum {M : Type} {ps : List Pos} (hps : ∀ p ∈ ps, p.IsStruct)
    {s s' : RReg M} (h : ProgsSum S0 v ps s s') : MsgAgree v (hvw s) (hvw s') :=
  fun l e d ↦ (hvw_of_progsSum S0 v h fun p hp ↦ cellOf_ne_msg S0 (hps p hp) _ l e d |>.symm).symm

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset HPos × M)

/-- **Program calls of structural positions** move the register by `ProgsSum`. -/
theorem htQ₂_progPos (B : QReg) : ∀ (ps : List Pos), (∀ p ∈ ps, p.IsStruct) → ∀ P : Set (RReg M),
    HTQ₂ m₀ (realizeT (thetaOf S0 v) (progPos M B ps)) P
      fun _ ↦ {s' | ∃ s ∈ P, ProgsSum S0 v ps s s'}
  | [], _, P => htQ₂_pure () fun s hs ↦ ⟨s, hs, id, rfl, fun _ _ ↦ ⟨rfl, rfl⟩⟩
  | p :: ps, hps, P => by
    refine htQ₂_progThen m₀ (thetaOf S0 v) p (hps p List.mem_cons_self) S0 _ P _
      ((htQ₂_progPos B ps (fun q hq ↦ hps q (List.mem_cons_of_mem _ hq)) _).mono subset_rfl
        fun _ ↦ ?_)
    rintro s₂ ⟨s₁, ⟨s, hs, hR⟩, hS⟩
    rw [tabOf_thetaOf] at hR
    obtain ⟨hR₁, hR₂, hR₃⟩ := hR
    refine ⟨s, hs, fun hnb ↦ hS.1 (hR₂ hnb), hS.2.1.trans (congrArg (·.2.2) hR₁),
      fun z hz ↦ ?_⟩
    have hz₀ : z ≠ cellOf S0 p v := hz p List.mem_cons_self
    obtain ⟨e₁, e₂⟩ := hS.2.2 z fun q hq ↦ hz q (List.mem_cons_of_mem _ hq)
    refine ⟨e₁.trans ?_, e₂.trans (hR₃ z hz₀)⟩
    rw [show s₁.2.1 = progUpdate (.programH (cellOf S0 p v) (v p)) s.2.1 from
      congrArg Prod.fst hR₁]
    exact Function.update_of_ne hz₀ _ _

variable {m₀ : Finset HPos × SelMem}

/-- **A layer's search in the decompressed basis**: the view's selection, the memory updated by
`grindMem`, databases and hardwired cells kept. -/
theorem htQ₂_selectT (B : QReg) (l : Layer) (e : KeyIndex) (msg : MsgBytes) (rnd : Pos)
    (P : Set (RReg SelMem)) (hP : ∀ s ∈ P, NoBot s) :
    HTQ₂ m₀ (realizeT (thetaOf S0 v) (selectT SelMem cwUpd v.param B l e msg rnd)) P
      fun g ↦ {s' | ∃ s ∈ P, g = v.select (hvw s) l e msg (truncateHash (v rnd)) ∧
        s'.1 = s.1 ∧ s'.2.1 = s.2.1 ∧
        s'.2.2.2 = grindMem (hvw s) v.param l e msg (truncateHash (v rnd)) randomizerAttemptLimit 0
          s.2.2.2} := by
  rw [selectT]
  refine htQ₂_revealThen m₀ (thetaOf S0 v) _ _ P _ fun mem ↦ ?_
  have hb : truncateHash (tabR (restrictTo {loC rnd} (thetaOf S0 v)) rnd) = truncateHash (v rnd) :=
    (baseOf_eq (thetaOf S0 v) rnd).trans (by rw [tabOf_thetaOf])
  dsimp only
  rw [hb]
  refine ((det_grindT (m₀ := m₀) (θ := thetaOf S0 v) v B l e msg (truncateHash (v rnd))
    randomizerAttemptLimit 0) _ ?_).mono subset_rfl fun g ↦ ?_
  · rintro s ⟨s₀, hs₀, -, rfl⟩
    exact hP s₀ hs₀
  · rintro s' ⟨s, ⟨s₀, hs₀, -, rfl⟩, rfl, rfl⟩
    exact ⟨s₀, hs₀, rfl, rfl, rfl, rfl⟩

/-- **Publishing a layer signature in the decompressed basis**: the table's layer signature, the
register moved by the program calls of its positions. -/
theorem htQ₂_publishT (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer) (x : Encoding)
    (P : Set (RReg SelMem)) :
    HTQ₂ m₀ (realizeT (thetaOf S0 v) (publishT SelMem B l e ρ x)) P
      fun sig ↦ {s' | ∃ s ∈ P, sig = layerSigOf v l e ρ x ∧
        ProgsSum S0 v (layerPos l e x) s s'} := by
  rw [publishT]
  refine htQ₂_revealThen m₀ (thetaOf S0 v) _ _ P _ fun mem ↦ ?_
  refine htQ₂_realizeT_bind m₀ (thetaOf S0 v)
    (htQ₂_progPos S0 v m₀ B _ (fun p hp ↦ isStruct_of_mem_layerPos hp) _) fun _ ↦
      htQ₂_pure _ ?_
  rintro s₂ ⟨s₁, ⟨s, hs, -, rfl⟩, hS⟩
  refine ⟨s, hs, ?_, hS.1, hS.2.1, hS.2.2⟩
  rw [layerSigOf_congr (thetaOf S0 v) subset_rfl, tabOf_thetaOf]

end steps

/-! ## The invariant of the challenge prefix -/

section inv

variable (S0 : MasterSeed) (v : QTable)

/-- A request's selection on layer `l` against `H`. -/
def layerSel (H : HashDomain → HashOutput) (r : SigningRequest) (l : Layer) :
    Option (Randomizer × Encoding) :=
  v.select H l (keyIndexOnLayer r.leafIndex l) (layerMsg v r l) (layerBase v r l)

/-- **Hardwired cells come from published signatures**: every hardwired `h`-cell is the cell of a
position that a logged request with both selections publishes. -/
def HwFrom (log : SignLog) (s : RReg SelMem) : Prop :=
  ∀ z, (s.2.1.1 z).isSome → ∃ q ∈ log, ∃ selB selT,
    layerSel v (hvw s) q.1 bottomLayer = some selB ∧ layerSel v (hvw s) q.1 topLayer = some selT ∧
    ∃ l, ∃ p ∈ layerPos l (keyIndexOnLayer q.1.leafIndex l)
      (if l = bottomLayer then selB.2 else selT.2), z = cellOf S0 p v

/-- **Selected keys were requested.** -/
def MemFrom (log : SignLog) (s : RReg SelMem) : Prop :=
  ∀ l e, s.2.2.2 l e ≠ none → ∃ q ∈ log, keyIndexOnLayer q.1.leafIndex l = e

/-- **The invariant along the challenge prefix** with the signing transcript `log`, in the
decompressed basis: no empty cell, the transcript's signatures are the table's against the view,
hardwired cells from published signatures, selected keys requested, and, without leaf reuse, the
memory records every request's selections. -/
def InvQ (log : SignLog) : Set (RReg SelMem) :=
  {s | NoBot s ∧ (∀ q ∈ log, q.2 = v.signature (hvw s) q.1) ∧ HwFrom S0 v log s ∧
    MemFrom log s ∧
    (SigningTranscript.NoLeafIndexReused log → ∀ q ∈ log, Records v (hvw s) s.2.2.2 q.1)}

theorem layer_cases (l : Layer) : l = bottomLayer ∨ l = topLayer := by
  rcases l with ⟨_ | _ | n, h⟩
  · exact .inl rfl
  · exact .inr rfl
  · exact absurd h (by simp [layerCount])

theorem leafIndex_eq_of_bottom {i i' : LeafIndex}
    (h : keyIndexOnLayer i bottomLayer = keyIndexOnLayer i' bottomLayer) : i = i' := by
  have h' := congrArg Fin.val h
  simp only [keyIndexOnLayer, bottomLayer, Nat.mul_zero, pow_zero, Nat.div_one] at h'
  exact Fin.ext h'

variable {v} in
theorem layerMsg_top_eq {r r' : SigningRequest}
    (h : keyIndexOnLayer r.leafIndex topLayer = keyIndexOnLayer r'.leafIndex topLayer) :
    layerMsg v r topLayer = layerMsg v r' topLayer := by
  rw [layerMsg_top, layerMsg_top]
  unfold QTable.bottomRoot
  rw [h]

variable {v} in
theorem layerSel_top_eq {H : HashDomain → HashOutput} {r r' : SigningRequest}
    (h : keyIndexOnLayer r.leafIndex topLayer = keyIndexOnLayer r'.leafIndex topLayer) :
    layerSel v H r topLayer = layerSel v H r' topLayer := by
  unfold layerSel
  rw [layerMsg_top_eq h, layerBase_top, layerBase_top]
  unfold QTable.topBase QTable.bottomRoot
  rw [h]

/-- **One signature keeps the invariant**, from the classical effect of `signT` on the
decompressed register. -/
theorem invQ_step {log : SignLog} {r : SigningRequest} {s s' : RReg SelMem}
    {sig : Option Signature} (hs : s ∈ InvQ S0 v log) (hnb : NoBot s')
    (hH : MsgAgree v (hvw s) (hvw s')) (hsig : sig = v.signature (hvw s) r)
    (hmem : s'.2.2.2 = grindMem (hvw s) v.param topLayer (keyIndexOnLayer r.leafIndex topLayer)
      (layerMsg v r topLayer) (layerBase v r topLayer) randomizerAttemptLimit 0
      (grindMem (hvw s) v.param bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)
        (layerMsg v r bottomLayer) (layerBase v r bottomLayer) randomizerAttemptLimit 0 s.2.2.2))
    (hW : ∀ z, (s'.2.1.1 z).isSome → (s.2.1.1 z).isSome ∨ ∃ selB selT,
      layerSel v (hvw s) r bottomLayer = some selB ∧ layerSel v (hvw s) r topLayer = some selT ∧
      ∃ l, ∃ p ∈ layerPos l (keyIndexOnLayer r.leafIndex l)
        (if l = bottomLayer then selB.2 else selT.2), z = cellOf S0 p v) :
    s' ∈ InvQ S0 v (log ++ [⟨r, sig⟩]) := by
  obtain ⟨-, hsigs, hhw, hmf, hrec⟩ := hs
  have hsel : ∀ q l, layerSel v (hvw s) q l = layerSel v (hvw s') q l :=
    fun _ _ ↦ select_congr hH _ _ _ _
  have hbt : bottomLayer ≠ topLayer := by decide
  refine ⟨hnb, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · rw [hsigs q hq, signature_congr hH]
    · rw [List.mem_singleton.mp hq]
      exact hsig.trans (signature_congr hH r)
  · intro z hz
    rcases hW z hz with hz₀ | ⟨selB, selT, hB, hT, hp⟩
    · obtain ⟨q, hq, selB, selT, hB, hT, hp⟩ := hhw z hz₀
      exact ⟨q, List.mem_append_left _ hq, selB, selT, (hsel _ _).symm.trans hB,
        (hsel _ _).symm.trans hT, hp⟩
    · exact ⟨⟨r, sig⟩, List.mem_append_right _ (List.mem_singleton_self _), selB, selT,
        (hsel _ _).symm.trans hB, (hsel _ _).symm.trans hT, hp⟩
  · intro l e hle
    by_cases hk : (l = bottomLayer ∧ e = keyIndexOnLayer r.leafIndex bottomLayer) ∨
        (l = topLayer ∧ e = keyIndexOnLayer r.leafIndex topLayer)
    · refine ⟨⟨r, sig⟩, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    · rw [hmem, grindMem_of_ne _ _ _ _ _ _ (fun h ↦ hk (.inr h)),
        grindMem_of_ne _ _ _ _ _ _ (fun h ↦ hk (.inl h))] at hle
      obtain ⟨q, hq, hqk⟩ := hmf l e hle
      exact ⟨q, List.mem_append_left _ hq, hqk⟩
  · intro hnr q hq
    have hnr₀ : SigningTranscript.NoLeafIndexReused log := by
      unfold SigningTranscript.NoLeafIndexReused at hnr ⊢
      rw [List.map_append] at hnr
      exact (List.nodup_append.mp hnr).1
    rw [← records_congr hH]
    rcases List.mem_append.mp hq with hq | hq
    · intro l sel hls
      have h0 := hrec hnr₀ q hq l sel hls
      have hne : s.2.2.2 l (keyIndexOnLayer q.1.leafIndex l) ≠ none := by
        rw [h0]
        exact Option.some_ne_none _
      rw [hmem, grindMem_of_ne_none _ _ _ _ _ _ _ _ _ (by
        rwa [grindMem_of_ne_none _ _ _ _ _ _ _ _ _ hne]),
        grindMem_of_ne_none _ _ _ _ _ _ _ _ _ hne, h0]
    · obtain rfl := List.mem_singleton.mp hq
      intro l sel hls
      rcases layer_cases l with rfl | rfl
      · have hnone : s.2.2.2 bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) = none := by
          by_contra hne
          obtain ⟨q', hq', hqk⟩ := hmf _ _ hne
          exact Quantum.Xmss.not_noLeafIndexReused_append
            (by rw [← leafIndex_eq_of_bottom hqk]; exact List.mem_map_of_mem hq') sig hnr
        rw [hmem, grindMem_of_ne _ _ _ _ _ _ (fun h ↦ hbt h.1)]
        exact grindMem_of_select _ _ _ _ _ v _ _ _ hnone hls
      · have hb : grindMem (hvw s) v.param bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)
            (layerMsg v r bottomLayer) (layerBase v r bottomLayer) randomizerAttemptLimit 0 s.2.2.2
            topLayer (keyIndexOnLayer r.leafIndex topLayer) =
            s.2.2.2 topLayer (keyIndexOnLayer r.leafIndex topLayer) :=
          grindMem_of_ne _ _ _ _ _ _ (fun h ↦ hbt h.1.symm) _ _ _
        rcases hm : s.2.2.2 topLayer (keyIndexOnLayer r.leafIndex topLayer) with _ | c
        · rw [hm] at hb
          rw [hmem]
          exact grindMem_of_select _ _ _ _ _ v _ _ _ hb hls
        · obtain ⟨q', hq', hqk⟩ := hmf _ _ (by rw [hm]; exact Option.some_ne_none c)
          have hls' : layerSel v (hvw s) q'.1 topLayer = some sel :=
            (layerSel_top_eq hqk).trans hls
          have h0 := hrec hnr₀ q' hq' topLayer sel hls'
          rw [hqk, layerMsg_top_eq hqk] at h0
          rw [hm] at hb
          rw [hmem, grindMem_of_some _ _ _ _ _ _ _ _ _ hb, ← hm, h0]

/-- The view of the projected register is the register's view. -/
theorem viewH_unionH_eq (s : RReg SelMem) : viewH (unionH (s.1, s.2.1, s.2.2.2)) = hvw s :=
  rfl

theorem known_chain_le {D : Set Quantum.Xmss.Pos} {l : Layer} {e : KeyIndex} {i : ChainIndex}
    {j : ℕ} (h : Known D (.chain l e i j)) :
    ∀ k, j + k < chainLength → Known D (.chain l e i (j + k))
  | 0, _ => h
  | k + 1, hk => Known.chain l e i ⟨j + k, by omega⟩ (known_chain_le h k (by omega))

theorem chain_mem_layerPos {l l' : Layer} {e e' : KeyIndex} {i : ChainIndex} {step : ChainStep}
    {x : Encoding} (hp : Pos.chain l e i step ∈ layerPos l' e' x) :
    l = l' ∧ e = e' ∧ (x i).val ≤ step.val := by
  simp only [layerPos, pathNode, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_cons, List.mem_finRange, true_and, decide_eq_true_eq] at hp
  rcases hp with ⟨i', step', hs', he⟩ | he | ⟨lev, he⟩
  · cases he
    exact ⟨rfl, rfl, hs'⟩
  · cases he
  · cases he

/-- **Hardwired chain cells have known inputs**, from `HwFrom`. -/
theorem hwKnown_of_hwFrom {log : SignLog} {s : RReg SelMem} (h : HwFrom S0 v log s) :
    HwKnown S0 v (hvw s) (s.1, s.2.1, s.2.2.2) (log.map Sigma.fst) := by
  intro l e i step hz
  obtain ⟨q, hq, selB, selT, hB, hT, l', p, hp, hzp⟩ := h _ hz
  obtain rfl : Pos.chain l e i step = p := (table S0).inj v hzp
  obtain ⟨rfl, rfl, hle⟩ := chain_mem_layerPos hp
  have hB' : v.select (hvw s) bottomLayer (keyIndexOnLayer q.1.leafIndex bottomLayer)
      (messageBytes q.1.message) (v.bottomBase q.1) = some selB := by
    rw [← layerMsg_bottom, ← layerBase_bottom]
    exact hB
  have hT' : v.select (hvw s) topLayer (keyIndexOnLayer q.1.leafIndex topLayer)
      (rootBytes (v.bottomRoot q.1.leafIndex)) (v.topBase q.1) = some selT := by
    rw [← layerMsg_top, ← layerBase_top]
    exact hT
  set x := if l = bottomLayer then selB.2 else selT.2 with hx
  have hd : Quantum.Xmss.Pos.chain l (keyIndexOnLayer q.1.leafIndex l) i (x i).val ∈
      v.disclosures (hvw s) (log.map Sigma.fst) := by
    refine Or.inr (Set.mem_biUnion (List.mem_map_of_mem hq) ?_)
    simp only [QTable.disclosedBy, hB', hT']
    rcases layer_cases l with rfl | rfl
    · exact Or.inl (Or.inl ⟨i, by rw [hx, ite_eq_left rfl]⟩)
    · exact Or.inr (Or.inl ⟨i, by rw [hx, ite_eq_right (by decide)]⟩)
  have hk := known_chain_le (Known.disclosed _ hd) (step.val - (x i).val) (by
    have := step.isLt
    omega)
  rwa [Nat.add_sub_cancel' hle] at hk

end inv

/-! ## The signer keeps the invariant -/

section sign

variable (S0 : MasterSeed) (v : QTable) {m₀ : Finset HPos × SelMem}

/-- **A signature keeps the invariant `InvQ`** in the decompressed basis. -/
theorem htQ₂_signT (B : QReg) (r : SigningRequest) (log : SignLog) :
    HTQ₂ m₀ (realizeT (thetaOf S0 v) (signT SelMem cwUpd v.param B r)) (InvQ S0 v log)
      fun sig ↦ InvQ S0 v (log ++ [⟨r, sig⟩]) := by
  rw [signT]
  refine htQ₂_realizeT_bind m₀ _ (htQ₂_selectT S0 v B _ _ _ _ _ fun s hs ↦ hs.1) fun gb ↦ ?_
  refine htQ₂_revealThen m₀ _ _ _ _ _ fun mem ↦ ?_
  dsimp only
  rw [show (tabR (restrictTo (rootReveal r) (thetaOf S0 v))).bottomRoot r.leafIndex =
    v.bottomRoot r.leafIndex from (rootOf_eq _ r).trans (by rw [tabOf_thetaOf])]
  refine htQ₂_realizeT_bind m₀ _ (htQ₂_selectT S0 v B _ _ _ _ _ ?_) fun gt ↦ ?_
  · rintro s₂ ⟨s₁, ⟨s, hs, -, h1, -, -⟩, -, rfl⟩
    exact noBot_of_eq h1 hs.1
  have key : ∀ s₃ ∈ {s₃ : RReg SelMem | ∃ s₂ ∈ {s₂ : RReg SelMem | ∃ s₁ ∈ {s₁ : RReg SelMem |
      ∃ s ∈ InvQ S0 v log, gb = v.select (hvw s) bottomLayer
        (keyIndexOnLayer r.leafIndex bottomLayer) (messageBytes r.message)
          (truncateHash (v (.rndBottom (keyIndexOnLayer r.leafIndex bottomLayer) r.message))) ∧
        s₁.1 = s.1 ∧ s₁.2.1 = s.2.1 ∧ s₁.2.2.2 = grindMem (hvw s) v.param bottomLayer
          (keyIndexOnLayer r.leafIndex bottomLayer) (messageBytes r.message)
          (truncateHash (v (.rndBottom (keyIndexOnLayer r.leafIndex bottomLayer) r.message)))
          randomizerAttemptLimit 0 s.2.2.2}, s₁.2.2 = mem ∧
        s₂ = (s₁.1, s₁.2.1, (s₁.2.2.1 ∪ rootReveal r, s₁.2.2.2))},
      gt = v.select (hvw s₂) topLayer (keyIndexOnLayer r.leafIndex topLayer)
        (rootBytes (v.bottomRoot r.leafIndex))
        (truncateHash (v (.rndTop (keyIndexOnLayer r.leafIndex topLayer)
          (v.bottomRoot r.leafIndex)))) ∧
      s₃.1 = s₂.1 ∧ s₃.2.1 = s₂.2.1 ∧ s₃.2.2.2 = grindMem (hvw s₂) v.param topLayer
        (keyIndexOnLayer r.leafIndex topLayer) (rootBytes (v.bottomRoot r.leafIndex))
        (truncateHash (v (.rndTop (keyIndexOnLayer r.leafIndex topLayer)
          (v.bottomRoot r.leafIndex)))) randomizerAttemptLimit 0 s₂.2.2.2},
      ∃ s ∈ InvQ S0 v log, s₃.1 = s.1 ∧ s₃.2.1 = s.2.1 ∧
        gb = layerSel v (hvw s) r bottomLayer ∧ gt = layerSel v (hvw s) r topLayer ∧
        s₃.2.2.2 = grindMem (hvw s) v.param topLayer (keyIndexOnLayer r.leafIndex topLayer)
          (layerMsg v r topLayer) (layerBase v r topLayer) randomizerAttemptLimit 0
          (grindMem (hvw s) v.param bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)
            (layerMsg v r bottomLayer) (layerBase v r bottomLayer) randomizerAttemptLimit 0
            s.2.2.2) := by
    rintro s₃ ⟨s₂, ⟨s₁, ⟨s, hs, hgb, h11, h12, hm1⟩, -, rfl⟩, hgt, h31, h32, hm3⟩
    have e2 : hvw (s₁.1, s₁.2.1, (s₁.2.2.1 ∪ rootReveal r, s₁.2.2.2)) = hvw s := hvw_eq h11 h12
    rw [e2] at hgt hm3
    refine ⟨s, hs, h31.trans h11, h32.trans h12, ?_, ?_, ?_⟩
    · rw [hgb, layerSel, layerMsg_bottom, layerBase_bottom]
      rfl
    · rw [hgt, layerSel, layerMsg_top, layerBase_top]
      rfl
    · rw [hm3, layerMsg_bottom, layerBase_bottom, layerMsg_top, layerBase_top]
      exact congrArg _ hm1
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  rotate_left 3
  · refine htQ₂_realizeT_bind m₀ _ (htQ₂_publishT S0 v B _ _ _ _ _) fun sb ↦ ?_
    refine htQ₂_realizeT_bind m₀ _ (htQ₂_publishT S0 v B _ _ _ _ _) fun st ↦ ?_
    refine htQ₂_pure _ ?_
    rintro s₅ ⟨s₄, ⟨s₃, hs₃, rfl, hS4⟩, rfl, hS5⟩
    obtain ⟨s, hs, h31, h32, hgb, hgt, hm3⟩ := key s₃ hs₃
    have e3 : hvw s₃ = hvw s := hvw_eq h31 h32
    have hps : ∀ l e x, ∀ p ∈ layerPos l e x, p.IsStruct := fun _ _ _ _ hp ↦
      isStruct_of_mem_layerPos hp
    refine invQ_step S0 v hs (hS5.1 (hS4.1 (noBot_of_eq h31 hs.1))) ?_ ?_ ?_ ?_
    · rw [← e3]
      exact (msgAgree_of_progsSum S0 v (hps _ _ _) hS4).trans
        (msgAgree_of_progsSum S0 v (hps _ _ _) hS5)
    · simp only [QTable.signature, QTable.bottomSignature, QTable.topSignature,
        QTable.layerSignature]
      rw [show v.select (hvw s) bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)
          (messageBytes r.message) (v.bottomBase r) = some (ρb, xb) from by
        rw [hgb, layerSel, layerMsg_bottom, layerBase_bottom],
        show v.select (hvw s) topLayer (keyIndexOnLayer r.leafIndex topLayer)
          (rootBytes (v.bottomRoot r.leafIndex)) (v.topBase r) = some (ρt, xt) from by
        rw [hgt, layerSel, layerMsg_top, layerBase_top]]
      rfl
    · rw [hS5.2.1, hS4.2.1, hm3]
    · intro z hz
      by_cases hzT : ∃ p ∈ layerPos topLayer (keyIndexOnLayer r.leafIndex topLayer) xt,
          z = cellOf S0 p v
      · exact .inr ⟨(ρb, xb), (ρt, xt), hgb.symm, hgt.symm, topLayer, by
          rw [ite_eq_right (by decide)]
          exact hzT⟩
      · by_cases hzB : ∃ p ∈ layerPos bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) xb,
            z = cellOf S0 p v
        · exact .inr ⟨(ρb, xb), (ρt, xt), hgb.symm, hgt.symm, bottomLayer, by
            rw [ite_eq_left rfl]
            exact hzB⟩
        · refine .inl ?_
          rw [← h32, ← (hS4.2.2 z fun p hp hzp ↦ hzB ⟨p, hp, hzp⟩).1,
            ← (hS5.2.2 z fun p hp hzp ↦ hzT ⟨p, hp, hzp⟩).1]
          exact hz
  all_goals
    refine htQ₂_pure _ ?_
    intro s₃ hs₃
    obtain ⟨s, hs, h31, h32, hgb, hgt, hm3⟩ := key s₃ hs₃
    refine invQ_step S0 v hs (noBot_of_eq h31 hs.1) ?_ ?_ hm3 fun z hz ↦ .inl (by rwa [h32] at hz)
    · rw [hvw_eq h31 h32]
      exact fun _ _ _ ↦ rfl
    · simp only [QTable.signature, QTable.bottomSignature, QTable.topSignature,
        QTable.layerSignature]
      rw [show v.select (hvw s) bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)
          (messageBytes r.message) (v.bottomBase r) = layerSel v (hvw s) r bottomLayer from by
        rw [layerSel, layerMsg_bottom, layerBase_bottom],
        show v.select (hvw s) topLayer (keyIndexOnLayer r.leafIndex topLayer)
          (rootBytes (v.bottomRoot r.leafIndex)) (v.topBase r) = layerSel v (hvw s) r topLayer
          from by rw [layerSel, layerMsg_top, layerBase_top], ← hgb, ← hgt]
      rfl

end sign

/-! ## The challenge prefix -/

section prefixRun

variable (S0 : MasterSeed) (v : QTable) {m₀ : Finset HPos × SelMem}

-- The adversary's commands, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "AdvP" => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (SufCma.advSpec SigningRequest (Option Signature))

/-- **The substituted adversary with its signing log**: sponge-only steps keep `Inv log`, a
signing request moves it to the extended log. -/
theorem htQ_logSigns (Inv : SignLog → Set (RReg SelMem))
    (hsign : ∀ (B : QReg) (r : SigningRequest) (log : SignLog),
      HTQ₂ m₀ (realizeT (thetaOf S0 v) (signT SelMem cwUpd v.param B r)) (Inv log)
        (fun sig ↦ Inv (log ++ [⟨r, sig⟩])))
    {Ω Y : QReg → Type} (leaf : ∀ u, Ω u → SignLog → Y u) (Q : (Σ u, Y u) → Set (RReg SelMem))
    (hleaf : ∀ u y log, Inv log ⊆ Q ⟨u, leaf u y log⟩) {A : QReg}
    (x : IPFunctor.IFreeM AdvP Ω A) (log : SignLog) :
    HTQ m₀ ((SufCma.logSigns leaf x log).substitute fun A c ↦
      realizeT (thetaOf S0 v) (challengeT SelMem cwUpd v.param A c)) (Inv log) Q := by
  induction x using IPFunctor.IFreeM.inductionOn generalizing log with
  | pure u y => exact htQ_pure (leaf u y log) (hleaf u y log)
  | liftBind s c next ih =>
    refine HTQ.bind (x := realizeT (thetaOf S0 v) (challengeT SelMem cwUpd v.param s c))
      (Q := fun p ↦ Inv (SufCma.logAfter c p.2.1 log)) ?_ fun u ans ↦ ?_
    · rcases c with o | ⟨_ | r, E, ℓ⟩
      · exact htQ_sponge m₀ (thetaOf S0 v) _ (Inv log)
      · exact htQ_sponge m₀ (thetaOf S0 v) _ (Inv log)
      · have hs : HTQ₂ m₀ (realizeT (thetaOf S0 v) (signAt SelMem cwUpd v.param r E ℓ))
            (Inv log) fun sig ↦ Inv (log ++ [⟨r, sig⟩]) :=
          htQ₂_realizeT_bind m₀ (thetaOf S0 v) (htQ₂_act _ _) fun _ ↦ hsign _ r log
        exact htQ_realizeT_bind m₀ (thetaOf S0 v) (htQ_of_htQ₂ hs) fun _ l ↦
          htQ_pure _ subset_rfl
    · obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b (SufCma.logAfter c b log)

/-- **The challenge prefix**: the public key revealed, then the adversary against the challenger
with its signing log, moving `Inv log` along the log; it returns the revealed public key. -/
theorem htQ₂_prefixT (A : Adversary) (Inv : SignLog → Set (RReg SelMem))
    (hsign : ∀ (B : QReg) (r : SigningRequest) (log : SignLog),
      HTQ₂ m₀ (realizeT (thetaOf S0 v) (signT SelMem cwUpd v.param B r)) (Inv log)
        (fun sig ↦ Inv (log ++ [⟨r, sig⟩])))
    (P₀ : Set (RReg SelMem))
    (hroot : ∀ s ∈ P₀, (s.1, s.2.1, (s.2.2.1 ∪ pkReveal, s.2.2.2)) ∈ Inv []) :
    HTQ₂ m₀ (realizeT (thetaOf S0 v) (prefixT SelMem cwUpd A)) P₀
      (fun pre ↦ {s | s ∈ Inv pre.2.2 ∧ pre.1 = pkD (thetaOf S0 v)}) := by
  unfold prefixT
  refine htQ₂_revealThen m₀ (thetaOf S0 v) _ _ P₀ _ fun mem ↦ ?_
  have hP : (pkT (restrictTo pkReveal (thetaOf S0 v))).parameter = v.param := by
    rw [show pkT (restrictTo pkReveal (thetaOf S0 v)) = pkD (thetaOf S0 v) from rfl, pkD_eq,
      tabOf_thetaOf]
    rfl
  dsimp only
  rw [hP]
  refine htQ₂_realizeT_bind m₀ (thetaOf S0 v) (Q := fun run ↦ Inv run.2) ?_ fun run ↦
    htQ₂_pure _ fun s hs ↦ ⟨hs, rfl⟩
  refine htQ₂_of_htQ (HTQ.mono (P := Inv []) ?_ ?_ fun _ ↦ subset_rfl)
  · have e := realizeT_substitute (good := goodQ) (M := SelMem) (thetaOf S0 v)
      (challengeT SelMem cwUpd v.param)
      (SufCma.withSignLog (A (pkT (restrictTo pkReveal (thetaOf S0 v)))))
    refine (congrArg (fun y ↦ HTQ m₀ y (Inv []) fun p ↦ Inv p.2.2.2) e).mpr ?_
    exact htQ_logSigns S0 v Inv hsign _
      (fun q : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) (Forgery × SignLog) u) ↦ Inv q.2.2.2)
      (fun _ _ _ ↦ subset_rfl) _ []
  · rintro s ⟨s₀, hs₀, -, rfl⟩
    exact hroot s₀ hs₀

/-- **The initial operator in the decompressed basis**: no empty cell, no hardwired cell, memory
`m₀`. -/
theorem init_decQ (m₀ : Finset HPos × SelMem) :
    QuerySupportedOn (fun p : Unit × RReg SelMem ↦ p.2)
      {s | NoBot s ∧ s.2 = (hwEmpty HashOutput HashDomain, m₀)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset HPos × SelMem)) (initU m₀)) := by
  have h0 : QuerySupportedOn (fun p : Unit × RReg SelMem ↦ p.2)
      {s | s.2 = (hwEmpty HashOutput HashDomain, m₀)} (initU m₀) := by
    intro m m' hm
    change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
      Database.empty), hwEmpty HashOutput HashDomain, m₀) : RReg SelMem)).matrix) m m' ≠ 0 at hm
    simp only [SubState.matrix_basis] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · exact ⟨congrArg Prod.snd he.1.symm, congrArg Prod.snd he.2.symm⟩
    · exact absurd rfl h
  exact querySupportedOn_inter (noBot_init m₀ (A := Unit) (SubState.basis ()).matrix)
    (querySupportedOn_conj_compressReg (P := fun b ↦ b = (hwEmpty HashOutput HashDomain, m₀)) h0)

/-- **The facts of a prefix outcome `pre`** on a register `s` (`win_imp_badQ`'s hypotheses on the
projected register `(s.1, s.2.1, s.2.2.2)`, with `H` its view): the public key is the table's, no
empty cell, the transcript's signatures are the table's, without leaf reuse the memory records
every request's selections, and every hardwired chain cell has a known input. -/
def PreFactsQ (pre : PublicKey × (Forgery × SignLog)) (s : RReg SelMem) : Prop :=
  pre.1 = v.publicKey ∧ NoBot s ∧
    (∀ q ∈ pre.2.2, q.2 = v.signature (viewH (unionH (s.1, s.2.1, s.2.2.2))) q.1) ∧
    (SigningTranscript.NoLeafIndexReused pre.2.2 →
      ∀ q ∈ pre.2.2, Records v (viewH (unionH (s.1, s.2.1, s.2.2.2))) s.2.2.2 q.1) ∧
    HwKnown S0 v (viewH (unionH (s.1, s.2.1, s.2.2.2))) (s.1, s.2.1, s.2.2.2)
      (pre.2.2.map Sigma.fst)

/-- **The call invariants of the canonical prefix**: on every branch of the challenge prefix
`prefixQ A (thetaOf S0 v)` run against `runtimeR m₀` from a memory with no selection, in the
decompressed basis, the register is supported where `PreFactsQ` holds. -/
theorem prefixFactsQ (A : Adversary) (m₀ : Finset HPos × SelMem) (hm₀ : m₀.2 = fun _ _ ↦ none)
    (pre : PublicKey × (Forgery × SignLog)) :
    QuerySupportedOn (fun p : Unit × RReg SelMem ↦ p.2) {s | PreFactsQ S0 v pre s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset HPos × SelMem))
        (((runtimeR m₀).run₂ .instruments (prefixQ A (thetaOf S0 v))).branch pre (initU m₀))) := by
  rw [Quantum.Xmss.Assembly.conj_branch₂ m₀ (prefixQ A (thetaOf S0 v)) pre (initU m₀)]
  have H := htQ₂_prefixT S0 v (m₀ := m₀) A (InvQ S0 v) (fun B r log ↦ htQ₂_signT S0 v B r log)
    {s | NoBot s ∧ s.2 = (hwEmpty HashOutput HashDomain, m₀)} fun s hs ↦ by
      obtain ⟨hnb, hs2⟩ := hs
      refine ⟨hnb, fun q hq ↦ absurd hq List.not_mem_nil, fun z hz ↦ ?_, fun l e hle ↦ ?_,
        fun _ q hq ↦ absurd hq List.not_mem_nil⟩
      · rw [show s.2.1 = hwEmpty HashOutput HashDomain from congrArg Prod.fst hs2] at hz
        exact absurd hz (by simp [hwEmpty, Database.empty])
      · rw [show s.2.2.2 = m₀.2 from congrArg (·.2.2) hs2, hm₀] at hle
        exact absurd rfl hle
  refine (H _ (init_decQ m₀) pre).mono ?_
  rintro s ⟨hinv, hpk⟩
  refine ⟨by rw [hpk, pkD_eq, tabOf_thetaOf], hinv.1, hinv.2.1, hinv.2.2.2.2,
    hwKnown_of_hwFrom S0 v hinv.2.2.1⟩

end prefixRun

end Quantum.Qrom.Xmss

end
