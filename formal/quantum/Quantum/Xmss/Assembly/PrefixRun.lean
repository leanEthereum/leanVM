module

public import Quantum.Xmss.Assembly.WinDecomp

@[expose] public section

/-!
# Support semantics of the realized template programs in the decompressed basis

Hoare-style statements on the runs of realized template programs in runtime 2 with record ports,
in the decompressed basis `decR m₀` (EndReads): from an operator supported on registers in `P`,
every branch is supported on the registers of the postcondition.

The Hoare predicates, the ports, reveals, program ports, sponge-only steps and read programs are
generic in the hidden coordinates `S`, their values `D`, the allowed programs `good` and the inner
memory `M` (leanSPHINCS instantiates them); the randomizer search and the challenge prefix are
leanXMSS's.

* `HT`, `HT₂`: the Hoare predicates for general and fixed-register programs, with `mono`, `bind`,
  `pure`, local operations (`ht₂_act_bind`) and calls (`ht_queryBind`, `ht₂_queryBind`); every
  run keeps `NoBot` (`ht_noBot`).
* Ports in the decompressed basis: sponge ports keep the register (`decR_sponge_supp`), a record
  of `T` adds `T` to the label (`decR_rec_supp`), a program call moves only its cell and sets the
  hardwired cell (`ProgRel`, `decR_prog_supp`), a read keeps the databases and updates the memory
  (`decR_readU_supp`).
* `ht₂_revealThen`, `ht₂_progThen`, `ht_sponge`: reveals, program ports, sponge-only steps;
  `ht₂_progSlots`: leanXMSS's slots.
* `Det`: read programs answer as functions of the register; `det_hashTrial`: a one-block trial
  answers the view's hash; `det_grindR`: the randomizer search answers `grindV` of the view and
  updates the memory by `grindMemV`.
* `ht₂_prefixT`: the challenge prefix with the signing log; `init_dec`: the initial operator.
-/

open Matrix
open scoped Kronecker

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma LeanXmss.RandomPermutationModel

/- Instance search for the run families over the register `PReg` exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## Generic facts on the hardwired register -/

section generic

theorem snd_eq_of_hwPort {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    [AddCommGroup X] [AddCommGroup Z] {M' : Type} [Fintype M'] [DecidableEq M']
    {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
    (read : HwReg X Z M' → A → Y) (m' m : (A × Y) × HwReg X Z M')
    (h : (((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M') * hwPort read *
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M')) m' m ≠ 0) :
    m'.2 = m.2 := by
  rw [one_kron_mul_hwPort_mul_one_kron, tableOracle_apply] at h
  split_ifs at h with he
  · rw [he]
    rfl
  · exact absurd rfl h

theorem dbs_one_dec_eq {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    [AddCommGroup X] [AddCommGroup Z] {D' D : DbReg X Z}
    (h : (compressDbs X Z * (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ) * compressDbs X Z) D' D ≠ 0) :
    D' = D := by
  rw [Matrix.mul_one, compressDbs_mul_self] at h
  by_contra hD
  exact h (Matrix.one_apply_ne hD)

end generic

/-! ## The Hoare predicates -/

/-- The register of runtime 2 with record ports at the memory `Finset S × M`. -/
abbrev PRegOf (S M : Type) : Type := HwReg X Z (Finset S × M)

/-- The register of runtime 2 with record ports at leanXMSS's memory. -/
abbrev PReg : Type := PRegOf HPos Selections

section hoare

variable {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]
  (m₀ : Finset S × M)

/-- **Support semantics of a program in the decompressed basis**: from an operator supported on
registers in `P`, the branch at every leaf `p` is supported on `Q p`. -/
def HT {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A) (P : Set (PRegOf S M))
    (Q : (Σ u, Ω u) → Set (PRegOf S M)) : Prop :=
  ∀ ρ : Matrix (A × PRegOf S M) (A × PRegOf S M) ℂ,
    QuerySupportedOn (fun m : A × PRegOf S M ↦ m.2) P ρ →
    ∀ p, QuerySupportedOn (fun m : p.1 × PRegOf S M ↦ m.2) (Q p)
      (((decR (X := X) (Z := Z) m₀).run .instruments y).branch p ρ)

/-- `HT` for programs on a fixed final register: the branch at every return value `a` is supported
on `Q a`. -/
def HT₂ {A B : QReg} {α : Type} (y : QComp (recHwSpec X Z S M) A B α) (P : Set (PRegOf S M))
    (Q : α → Set (PRegOf S M)) : Prop :=
  ∀ ρ : Matrix (A × PRegOf S M) (A × PRegOf S M) ℂ,
    QuerySupportedOn (fun m : A × PRegOf S M ↦ m.2) P ρ →
    ∀ a, QuerySupportedOn (fun m : B × PRegOf S M ↦ m.2) (Q a)
      (((decR (X := X) (Z := Z) m₀).run₂ .instruments y).branch a ρ)

variable {m₀}

theorem HT.mono {Ω : QReg → Type} {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A}
    {P P' : Set (PRegOf S M)} {Q Q' : (Σ u, Ω u) → Set (PRegOf S M)} (h : HT m₀ y P Q)
    (hP : P' ⊆ P) (hQ : ∀ p, Q p ⊆ Q' p) : HT m₀ y P' Q' :=
  fun ρ hρ p ↦ (h ρ (hρ.mono hP) p).mono (hQ p)

theorem HT₂.mono {A B : QReg} {α : Type} {y : QComp (recHwSpec X Z S M) A B α}
    {P P' : Set (PRegOf S M)} {Q Q' : α → Set (PRegOf S M)} (h : HT₂ m₀ y P Q) (hP : P' ⊆ P)
    (hQ : ∀ a, Q a ⊆ Q' a) : HT₂ m₀ y P' Q' :=
  fun ρ hρ a ↦ (h ρ (hρ.mono hP) a).mono (hQ a)

/-- `HT₂` is `HT` at the leaves `⟨B, rfl, a⟩`. -/
theorem ht₂_iff {A B : QReg} {α : Type} (y : QComp (recHwSpec X Z S M) A B α)
    (P : Set (PRegOf S M)) (Q : α → Set (PRegOf S M)) :
    HT₂ m₀ y P Q ↔ HT m₀ y P fun p ↦ Q p.2.2 := by
  constructor
  · intro h ρ hρ p
    obtain ⟨u, hu, a⟩ := p
    subst hu
    exact h ρ hρ a
  · intro h ρ hρ a
    exact h ρ hρ ⟨B, rfl, a⟩

theorem ht_of_ht₂ {A B : QReg} {α : Type} {y : QComp (recHwSpec X Z S M) A B α}
    {P : Set (PRegOf S M)} {Q : α → Set (PRegOf S M)} (h : HT₂ m₀ y P Q) :
    HT m₀ y P fun p ↦ Q p.2.2 :=
  (ht₂_iff y P Q).mp h

theorem ht₂_of_ht {A B : QReg} {α : Type} {y : QComp (recHwSpec X Z S M) A B α}
    {P : Set (PRegOf S M)} {Q : α → Set (PRegOf S M)} (h : HT m₀ y P fun p ↦ Q p.2.2) :
    HT₂ m₀ y P Q :=
  (ht₂_iff y P Q).mpr h

theorem ht_pure {Ω : QReg → Type} {A : QReg} (y : Ω A) {P : Set (PRegOf S M)}
    {Q : (Σ u, Ω u) → Set (PRegOf S M)} (h : P ⊆ Q ⟨A, y⟩) :
    HT m₀ (QuantumComp.pure (L := LocalSig.instruments.{0})
      (spec := recHwSpec X Z S M) y) P Q := by
  classical
  intro ρ hρ p
  rw [QuantumRuntime.run_pure]
  by_cases hp : p = ⟨A, y⟩
  · subst hp
    rw [DSubInstrument.branch_ret_self]
    exact hρ.mono h
  · rw [DSubInstrument.branch_ret_of_ne _ hp]
    exact querySupportedOn_zero _ _

theorem ht₂_pure {A : QReg} {α : Type} (a : α) {P : Set (PRegOf S M)}
    {Q : α → Set (PRegOf S M)} (h : P ⊆ Q a) :
    HT₂ m₀ (QuantumComp₂.pure a : QComp (recHwSpec X Z S M) A A α) P Q := by
  intro ρ hρ a'
  rw [QuantumRuntime.run₂_pure]
  by_cases ha : a' = a
  · subst ha
    rw [SubInstrument.branch_pure_self]
    exact hρ.mono h
  · rw [SubInstrument.branch_pure_of_ne ha]
    exact querySupportedOn_zero _ _

theorem HT.bind {Ω Ω' : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A}
    {P : Set (PRegOf S M)} {Q : (Σ u, Ω u) → Set (PRegOf S M)} (hx : HT m₀ x P Q)
    {k : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω' u}
    {R : (Σ u, Ω' u) → Set (PRegOf S M)} (hk : ∀ u a, HT m₀ (k u a) (Q ⟨u, a⟩) R) :
    HT m₀ (x.bind k) P R := by
  intro ρ hρ p
  rw [QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun q ↦ hk q.1 q.2 _ (hx ρ hρ q) p

theorem HT₂.bind {A B C : QReg} {α β : Type} {x : QComp (recHwSpec X Z S M) A B α}
    {P : Set (PRegOf S M)} {Q : α → Set (PRegOf S M)} (hx : HT₂ m₀ x P Q)
    {k : α → QComp (recHwSpec X Z S M) B C β} {R : β → Set (PRegOf S M)}
    (hk : ∀ a, HT₂ m₀ (k a) (Q a) R) : HT₂ m₀ (x.bind k) P R := by
  intro ρ hρ b
  erw [QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun a ↦ hk a _ (hx ρ hρ a) b

theorem ht_primBind {Ω : QReg → Type} {A : QReg} (o : LocalSig.instruments.{0}.Op A)
    {k : (b : LocalSig.instruments.{0}.Outcome o) →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
        (LocalSig.instruments.{0}.next o b)}
    {P : Set (PRegOf S M)} {Q : (Σ u, Ω u) → Set (PRegOf S M)} (hk : ∀ b, HT m₀ (k b) P Q) :
    HT m₀ (QuantumComp.primBind o k) P Q := by
  intro ρ hρ p
  rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun b ↦ hk b _ (QuerySupportedOn.amplify_snd (q := id) hρ _) p

/-- **A local operation keeps the register.** -/
theorem ht₂_act_bind {A B C : QReg} {α β : Type} (p : SubInstrument A B β)
    {k : β → QComp (recHwSpec X Z S M) B C α} {P : Set (PRegOf S M)} {Q : α → Set (PRegOf S M)}
    (hk : ∀ b, HT₂ m₀ (k b) P Q) : HT₂ m₀ ((QComp.act p).bind k) P Q := by
  intro ρ hρ a
  rw [QuantumRuntime.run₂_act_bind]
  erw [DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun b ↦ hk b _ (QuerySupportedOn.amplify_snd (q := id) hρ _) a

theorem ht₂_act {A B : QReg} {β : Type} (p : SubInstrument A B β) (P : Set (PRegOf S M)) :
    HT₂ m₀ (QComp.act (spec := recHwSpec X Z S M) p) P fun _ ↦ P := by
  rw [← QuantumComp₂.bind_pure (QComp.act (spec := recHwSpec X Z S M) p)]
  exact ht₂_act_bind p fun b ↦ ht₂_pure b subset_rfl

/-- A call whose step moves the support from `P` to `P' r` at the result `r`. -/
theorem ht_queryBind {Ω : QReg → Type} {A : QReg} (i : (recHwSpec X Z S M).Port)
    (E : QReg) (ℓ : A ≃ (recHwSpec X Z S M).In i × E)
    {k : (recHwSpec X Z S M).Result i →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
        (QReg.of ((recHwSpec X Z S M).Out i × E))}
    {P : Set (PRegOf S M)} (P' : (recHwSpec X Z S M).Result i → Set (PRegOf S M))
    {Q : (Σ u, Ω u) → Set (PRegOf S M)}
    (hstep : ∀ r (σ : Matrix ((recHwSpec X Z S M).In i × PRegOf S M)
      ((recHwSpec X Z S M).In i × PRegOf S M) ℂ),
      QuerySupportedOn (fun m : (recHwSpec X Z S M).In i × PRegOf S M ↦ m.2) P σ →
        QuerySupportedOn (fun m : (recHwSpec X Z S M).Out i × PRegOf S M ↦ m.2) (P' r)
          (((decR (X := X) (Z := Z) m₀).step i).branch r σ))
    (hk : ∀ r, HT m₀ (k r) (P' r) Q) : HT m₀ (QuantumComp.queryBind i E ℓ k) P Q := by
  intro ρ hρ p
  rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun r ↦ hk r _
    (querySupportedOn_queryStep_imp (decR (X := X) (Z := Z) m₀) i E ℓ r P (P' r) (hstep r) hρ) p

theorem ht₂_queryBind {A B : QReg} {α : Type} (i : (recHwSpec X Z S M).Port)
    (E : QReg) (ℓ : A ≃ (recHwSpec X Z S M).In i × E)
    {k : (recHwSpec X Z S M).Result i →
      QComp (recHwSpec X Z S M) (QReg.of ((recHwSpec X Z S M).Out i × E)) B α}
    {P : Set (PRegOf S M)} (P' : (recHwSpec X Z S M).Result i → Set (PRegOf S M))
    {Q : α → Set (PRegOf S M)}
    (hstep : ∀ r (σ : Matrix ((recHwSpec X Z S M).In i × PRegOf S M)
      ((recHwSpec X Z S M).In i × PRegOf S M) ℂ),
      QuerySupportedOn (fun m : (recHwSpec X Z S M).In i × PRegOf S M ↦ m.2) P σ →
        QuerySupportedOn (fun m : (recHwSpec X Z S M).Out i × PRegOf S M ↦ m.2) (P' r)
          (((decR (X := X) (Z := Z) m₀).step i).branch r σ))
    (hk : ∀ r, HT₂ m₀ (k r) (P' r) Q) :
    HT₂ m₀ (QuantumComp₂.queryBind (L := LocalSig.instruments) i E ℓ k) P Q := by
  intro ρ hρ a
  erw [QuantumRuntime.run₂_queryBind, DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum fun r ↦ hk r _
    (querySupportedOn_queryStep_imp (decR (X := X) (Z := Z) m₀) i E ℓ r P (P' r) (hstep r) hρ) a

variable (m₀) in
/-- **Every run keeps `NoBot`** (`decR_step_noBot`). -/
theorem ht_noBot {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A) :
    HT m₀ y {s | NoBot s} fun _ ↦ {s | NoBot s} :=
  fun _ hρ p ↦ querySupportedOn_run (decR (X := X) (Z := Z) m₀) {s | NoBot s}
    (decR_step_noBot m₀) .instruments y hρ p

theorem HT₂.and_noBot {A B : QReg} {α : Type} {y : QComp (recHwSpec X Z S M) A B α}
    {P : Set (PRegOf S M)} {Q : α → Set (PRegOf S M)} (h : HT₂ m₀ y P Q)
    (hP : ∀ s ∈ P, NoBot s) : HT₂ m₀ y P fun a ↦ Q a ∩ {s | NoBot s} :=
  fun ρ hρ a ↦ querySupportedOn_inter (h ρ hρ a)
    (ht₂_of_ht (Q := fun _ ↦ {s | NoBot s}) (ht_noBot m₀ y) ρ (hρ.mono hP) a)

end hoare

/-! ## The ports in the decompressed basis -/

section ports

variable {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]
  (m₀ : Finset S × M)

/-- **A sponge port keeps the decompressed register.** -/
theorem decR_sponge_supp (i : SpongePort)
    (r : (recHwSpec X Z S M).Result (.inl (.inl (.inl i)))) (P : Set (PRegOf S M))
    (σ : Matrix ((recHwSpec X Z S M).In (.inl (.inl (.inl i))) × PRegOf S M)
      ((recHwSpec X Z S M).In (.inl (.inl (.inl i))) × PRegOf S M) ℂ)
    (hσ : QuerySupportedOn
      (fun m : (recHwSpec X Z S M).In (.inl (.inl (.inl i))) × PRegOf S M ↦ m.2) P σ) :
    QuerySupportedOn
      (fun m : (recHwSpec X Z S M).Out (.inl (.inl (.inl i))) × PRegOf S M ↦ m.2) P
      (((decR (X := X) (Z := Z) m₀).step (.inl (.inl (.inl i)))).branch r σ) := by
  rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inl (.inl i)) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
  cases i <;> (rw [snd_eq_of_hwPort _ m' m hK]; exact hm)

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
/-- The registers after recording `T` from `P` with memory `mem` before. -/
def RecSet (P : Set (PRegOf S M)) (T : Finset S) (mem : Finset S × M) : Set (PRegOf S M) :=
  {s | ∃ s₀ ∈ P, s₀.2.2 = mem ∧ s = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ T, s₀.2.2.2))}

/-- **A record of `T` adds `T` to the label** and keeps everything else. -/
theorem decR_rec_supp (T : Finset S) (mem : (recHwSpec X Z S M).Result (.inr T))
    (P : Set (PRegOf S M))
    (σ : Matrix ((recHwSpec X Z S M).In (.inr T) × PRegOf S M)
      ((recHwSpec X Z S M).In (.inr T) × PRegOf S M) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z S M).In (.inr T) × PRegOf S M ↦ m.2) P σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z S M).Out (.inr T) × PRegOf S M ↦ m.2)
      (RecSet P T mem) (((decR (X := X) (Z := Z) m₀).step (.inr T)).branch mem σ) := by
  obtain ⟨lab, mm⟩ := mem
  rw [decR_branch_apply m₀ (.inr T) (lab, mm) _ (recStep_branch T (lab, mm))]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
  obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
  exact ⟨m.2, hm, hp, Prod.ext (dbs_one_dec_eq hR) hφ⟩

omit [Fintype S] [DecidableEq S] in
/-- **The effect of a program call `c`** on the decompressed register: the hardwired cells as
`progUpdate c`, no empty cell kept, and every database cell other than `c`'s kept. -/
def ProgRel (c : HwProg X Z) (s s' : PRegOf S M) : Prop :=
  s'.2 = (progUpdate c s.2.1, s.2.2) ∧ (NoBot s → NoBot s') ∧
    (∀ z, (∀ a, c ≠ .programH z a) → s'.1.1 z = s.1.1 z) ∧
    (∀ x, (∀ a, c ≠ .programK x a) → s'.1.2.1 x = s.1.2.1 x) ∧
    (∀ x, (∀ a, c ≠ .programK' x a) → s'.1.2.2 x = s.1.2.2 x)

omit [Fintype S] [DecidableEq S] in
/-- The effect of a sequence of program calls. -/
def ProgsRel : List (HwProg X Z) → PRegOf S M → PRegOf S M → Prop
  | [], s, s' => s = s'
  | c :: cs, s, s' => ∃ mid, ProgRel c s mid ∧ ProgsRel cs mid s'

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
theorem progsRel_append {l₁ l₂ : List (HwProg X Z)} {s mid s' : PRegOf S M}
    (h₁ : ProgsRel l₁ s mid) (h₂ : ProgsRel l₂ mid s') : ProgsRel (l₁ ++ l₂) s s' := by
  induction l₁ generalizing s with
  | nil =>
    subst h₁
    exact h₂
  | cons c cs ih =>
    obtain ⟨m, hm, hr⟩ := h₁
    exact ⟨m, hm, ih hr⟩

/-- **A program call in the decompressed basis** (`ProgRel`). -/
theorem decR_prog_supp (c : HwProg X Z) (r : (recHwSpec X Z S M).Result (.inl (.inr c)))
    (P : Set (PRegOf S M))
    (σ : Matrix ((recHwSpec X Z S M).In (.inl (.inr c)) × PRegOf S M)
      ((recHwSpec X Z S M).In (.inl (.inr c)) × PRegOf S M) ℂ)
    (hσ : QuerySupportedOn
      (fun m : (recHwSpec X Z S M).In (.inl (.inr c)) × PRegOf S M ↦ m.2) P σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z S M).Out (.inl (.inr c)) × PRegOf S M ↦ m.2)
      {s' | ∃ s ∈ P, ProgRel c s s'}
      (((decR (X := X) (Z := Z) m₀).step (.inl (.inr c))).branch r σ) := by
  rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inr c) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ⟨m.2, hm, ?_⟩
  cases c with
  | programH z a =>
    obtain ⟨-, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
    rw [show (cellDiscard z r.1 ⊗ₖ (1 : Matrix (Database X Z × Database X Z)
      (Database X Z × Database X Z) ℂ)) = cellDiscard z r.1 ⊗ₖ
        ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ 1) by rw [one_kronecker_one]] at hR
    obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
    obtain ⟨hc, hs⟩ := compressAll_mul_cellDiscard_mul_compressAll_ne_zero h₁
    have e₂ := one_dec_ne_zero h₂
    have e₃ := one_dec_ne_zero h₃
    refine ⟨hφ, fun hnb ↦ ⟨fun z' ↦ ?_, by rw [e₂]; exact hnb.2.1, by rw [e₃]; exact hnb.2.2⟩,
      fun z' hz' ↦ hc z' fun h ↦ hz' a (by rw [h]), fun x _ ↦ congrFun e₂ x,
      fun x _ ↦ congrFun e₃ x⟩
    by_cases hz : z' = z
    · subst hz
      exact hs
    · rw [hc z' hz]
      exact hnb.1 z'
  | programK x a =>
    obtain ⟨-, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
    obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
    obtain ⟨hc, hs⟩ := compressAll_mul_cellDiscard_mul_compressAll_ne_zero h₂
    have e₁ := one_dec_ne_zero h₁
    have e₃ := one_dec_ne_zero h₃
    refine ⟨hφ, fun hnb ↦ ⟨by rw [e₁]; exact hnb.1, fun x' ↦ ?_, by rw [e₃]; exact hnb.2.2⟩,
      fun z _ ↦ congrFun e₁ z, fun x' hx' ↦ hc x' fun h ↦ hx' a (by rw [h]),
      fun x' _ ↦ congrFun e₃ x'⟩
    by_cases hx : x' = x
    · subst hx
      exact hs
    · rw [hc x' hx]
      exact hnb.2.1 x'
  | programK' x a =>
    obtain ⟨-, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
    obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
    obtain ⟨hc, hs⟩ := compressAll_mul_cellDiscard_mul_compressAll_ne_zero h₃
    have e₁ := one_dec_ne_zero h₁
    have e₂ := one_dec_ne_zero h₂
    refine ⟨hφ, fun hnb ↦ ⟨by rw [e₁]; exact hnb.1, by rw [e₂]; exact hnb.2.1, fun x' ↦ ?_⟩,
      fun z _ ↦ congrFun e₁ z, fun x' _ ↦ congrFun e₂ x',
      fun x' hx' ↦ hc x' fun h ↦ hx' a (by rw [h])⟩
    by_cases hx : x' = x
    · subst hx
      exact hs
    · rw [hc x' hx]
      exact hnb.2.2 x'

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
/-- The register after a read of `c`: the databases and hardwired cells kept, the inner memory
updated by the read's update with the view's cell. -/
def readFin (s : PRegOf S M) : HwRead X Z M → PRegOf S M
  | .readH z upd => (s.1, s.2.1, (s.2.2.1, upd s.2.2.2 ((hwView s.2.1 s.1).1 z)))
  | .readK x upd => (s.1, s.2.1, (s.2.2.1, upd s.2.2.2 ((hwView s.2.1 s.1).2.1 x)))
  | .readK' x upd => (s.1, s.2.1, (s.2.2.1, upd s.2.2.2 ((hwView s.2.1 s.1).2.2 x)))

/-- **A read in the decompressed basis**: it returns the view's cell with the memory before,
keeps the databases and hardwired cells, and updates the memory. -/
theorem decR_readU_supp (c : HwRead X Z M)
    (r : (recHwSpec X Z S M).Result (.inl (.inl (.inr (liftRead c)))))
    (U : Set (PRegOf S M))
    (σ : Matrix ((recHwSpec X Z S M).In (.inl (.inl (.inr (liftRead c)))) × PRegOf S M)
      ((recHwSpec X Z S M).In (.inl (.inl (.inr (liftRead c)))) × PRegOf S M) ℂ)
    (hσ : QuerySupportedOn
      (fun p : (recHwSpec X Z S M).In (.inl (.inl (.inr (liftRead c)))) × PRegOf S M ↦ p.2)
        U σ) :
    QuerySupportedOn
      (fun p : (recHwSpec X Z S M).Out (.inl (.inl (.inr (liftRead c)))) × PRegOf S M ↦ p.2)
      {s' | ∃ s ∈ U, r = liftAns s c ∧ s' = readFin s c}
      (((decR (X := X) (Z := Z) m₀).step (.inl (.inl (.inr (liftRead c))))).branch r σ) := by
  rw [decR_branch_apply m₀ (.inl (.inl (.inr (liftRead c)))) r _
    (runtime2_branch m₀ (.inl (.inr (liftRead c))) r)]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ⟨m.2, hm, ?_⟩
  cases c with
  | readH z upd =>
    obtain ⟨o, mm⟩ := r
    obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
    rw [show (cellRead m.2.2.1.1 z o ⊗ₖ (1 : Matrix (Database X Z × Database X Z)
      (Database X Z × Database X Z) ℂ)) = cellRead m.2.2.1.1 z o ⊗ₖ
        ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ 1) by rw [one_kronecker_one]] at hR
    obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
    obtain ⟨e₁, hr⟩ := cellRead_dec_ne_zero h₁
    have hD : m'.2.1 = m.2.1 := Prod.ext e₁ (Prod.ext (one_dec_ne_zero h₂) (one_dec_ne_zero h₃))
    subst hp hr
    exact ⟨rfl, Prod.ext hD hφ⟩
  | readK x upd =>
    obtain ⟨o, mm⟩ := r
    obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
    obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
    obtain ⟨e₂, hr⟩ := cellRead_dec_ne_zero h₂
    have hD : m'.2.1 = m.2.1 := Prod.ext (one_dec_ne_zero h₁) (Prod.ext e₂ (one_dec_ne_zero h₃))
    subst hp hr
    exact ⟨rfl, Prod.ext hD hφ⟩
  | readK' x upd =>
    obtain ⟨o, mm⟩ := r
    obtain ⟨hp, hφ, hR⟩ := clsKraus_dec_ne_zero _ _ _ hK
    obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero hR
    obtain ⟨e₃, hr⟩ := cellRead_dec_ne_zero h₃
    have hD : m'.2.1 = m.2.1 := Prod.ext (one_dec_ne_zero h₁) (Prod.ext (one_dec_ne_zero h₂) e₃)
    subst hp hr
    exact ⟨rfl, Prod.ext hD hφ⟩

end ports

/-! ## Reveals, program ports and sponge-only steps -/

section template

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} {M : Type} [Fintype M]
  [DecidableEq M] {good : LazyProg X Z S D → Prop} (m₀ : Finset S × M) (v : (s : S) → D s)

theorem ht_realizeT_bind {Ω Ω' : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (tmplSpec X Z S D M good) Ω A}
    {g : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (tmplSpec X Z S D M good) Ω' u}
    {P : Set (PRegOf S M)} {Q : (Σ u, Ω u) → Set (PRegOf S M)} {R : (Σ u, Ω' u) → Set (PRegOf S M)}
    (hx : HT m₀ (realizeT v x) P Q) (hg : ∀ u a, HT m₀ (realizeT v (g u a)) (Q ⟨u, a⟩) R) :
    HT m₀ (realizeT v (x.bind g)) P R := by
  rw [realizeT_bind]
  exact HT.bind hx hg

theorem ht₂_realizeT_bind {A B C : QReg} {α β : Type} {x : QComp (tmplSpec X Z S D M good) A B α}
    {k : α → QComp (tmplSpec X Z S D M good) B C β} {P : Set (PRegOf S M)}
    {Q : α → Set (PRegOf S M)} {R : β → Set (PRegOf S M)} (hx : HT₂ m₀ (realizeT v x) P Q)
    (hk : ∀ a, HT₂ m₀ (realizeT v (k a)) (Q a) R) : HT₂ m₀ (realizeT v (x.bind k)) P R := by
  rw [realizeT_bind₂]
  exact HT₂.bind hx hk

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
theorem realizeT_revealThen {B C : QReg} {α : Type} (T : Finset S)
    (k : RevealVals D T × (Finset S × M) → QComp (tmplSpec X Z S D M good) B C α) :
    realizeT v (revealThen good T k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments)
        (spec := recHwSpec X Z S M) (.inr T) B (Equiv.uniqueProd B Unit).symm
        fun mem ↦ (QComp.act (A := QReg.of ((recHwSpec X Z S M).Out (.inr T) × B))
          (B := B) (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
            realizeT v (k (restrictTo T v, mem)) :=
  rfl

/-- **A realized reveal is the record port**: the values of `v` on `T`, the label grown by `T`. -/
theorem ht₂_revealThen {B C : QReg} {α : Type} (T : Finset S)
    (k : RevealVals D T × (Finset S × M) → QComp (tmplSpec X Z S D M good) B C α)
    (P : Set (PRegOf S M)) (Q : α → Set (PRegOf S M))
    (hk : ∀ mem, HT₂ m₀ (realizeT v (k (restrictTo T v, mem)))
      {s | ∃ s₀ ∈ P, s₀.2.2 = mem ∧ s = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ T, s₀.2.2.2))} Q) :
    HT₂ m₀ (realizeT v (revealThen good T k)) P Q := by
  rw [realizeT_revealThen]
  exact ht₂_queryBind (.inr T) B _ (RecSet P T) (fun mem σ hσ ↦ decR_rec_supp m₀ T mem P σ hσ)
    fun mem ↦ ht₂_act_bind _ fun _ ↦ hk mem

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
theorem realizeT_progThen {B C : QReg} {α : Type} (p : LazyProg X Z S D) (hp : good p)
    (k : QComp (tmplSpec X Z S D M good) B C α) :
    realizeT v (progThen p hp k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments)
        (spec := recHwSpec X Z S M) (.inl (.inr (p.realize v))) B
        (Equiv.uniqueProd B Unit).symm fun _ ↦
          (QComp.act (A := QReg.of ((recHwSpec X Z S M).Out
            (.inl (.inr (p.realize v))) × B)) (B := B)
            (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦ realizeT v k := by
  cases p <;> rfl

/-- **A realized program port** moves the register by `ProgRel` of its realized call. -/
theorem ht₂_progThen {B C : QReg} {α : Type} (p : LazyProg X Z S D) (hp : good p)
    (k : QComp (tmplSpec X Z S D M good) B C α) (P : Set (PRegOf S M)) (Q : α → Set (PRegOf S M))
    (hk : HT₂ m₀ (realizeT v k) {s' | ∃ s ∈ P, ProgRel (p.realize v) s s'} Q) :
    HT₂ m₀ (realizeT v (progThen p hp k)) P Q := by
  rw [realizeT_progThen]
  exact ht₂_queryBind _ B _ (fun _ ↦ {s' | ∃ s ∈ P, ProgRel (p.realize v) s s'})
    (fun r σ hσ ↦ decR_prog_supp m₀ (p.realize v) r P σ hσ) fun _ ↦ ht₂_act_bind _ fun _ ↦ hk

/-- **Sponge-only steps keep every register set**: in the decompressed basis the sponge ports read
the register without changing it, and local operations do not touch it. -/
theorem ht_sponge {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (spongeSpec X Z) Ω A) (P : Set (PRegOf S M)) :
    HT m₀ (realizeT v (readLift good (y.liftOrdinary (t := hwReadCmdSpec X Z M)))) P
      fun _ ↦ P := by
  induction y using QuantumComp.inductionOn with
  | pure A y => exact ht_pure y subset_rfl
  | primBind A o k ih =>
    have e : realizeT v (readLift good ((QuantumComp.primBind o k).liftOrdinary
        (t := hwReadCmdSpec X Z M))) =
        QuantumComp.primBind o fun b ↦
          realizeT v (readLift good ((k b).liftOrdinary (t := hwReadCmdSpec X Z M))) :=
      rfl
    rw [e]
    exact ht_primBind o fun b ↦ ih b
  | queryBind A i E ℓ k ih =>
    have e : realizeT v (readLift good ((QuantumComp.queryBind i E ℓ k).liftOrdinary
        (t := hwReadCmdSpec X Z M))) =
        QuantumComp.queryBind (spec := recHwSpec X Z S M) (.inl (.inl (.inl i))) E ℓ
          fun r ↦ realizeT v (readLift good ((k r).liftOrdinary
            (t := hwReadCmdSpec X Z M))) :=
      rfl
    rw [e]
    exact ht_queryBind _ E ℓ (fun _ ↦ P) (fun r σ hσ ↦ decR_sponge_supp m₀ i r P σ hσ)
      fun r ↦ ih r

end template

section templateX

variable (m₀ : Finset HPos × Selections) (v : HPos → Digest)

theorem ht₂_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) (P : Set PReg) :
    HT₂ m₀ (realizeT v (progPorts Selections B ps)) P
      fun _ ↦ {s' | ∃ s ∈ P, ProgsRel (ps.map (·.realize v)) s s'} := by
  induction ps generalizing P with
  | nil => exact ht₂_pure () fun s hs ↦ ⟨s, hs, rfl⟩
  | cons p ps ih =>
    refine ht₂_progThen m₀ v p trivial _ P _ ((ih _).mono subset_rfl fun _ ↦ ?_)
    rintro s'' ⟨s', ⟨s, hs, h₁⟩, h₂⟩
    exact ⟨s, hs, s', h₁, h₂⟩

/-- **Programming the honest paths of slots**: the register moves along their program calls. -/
theorem ht₂_progSlots (pub : Pub) (B : QReg) (ss : List Slot) (P : Set PReg) :
    HT₂ m₀ (realizeT v (progSlots Selections pub B ss)) P
      (fun _ ↦ {s' | ∃ s ∈ P, ProgsRel ((ss.flatMap (slotPorts pub)).map (·.realize v)) s s'}) := by
  induction ss generalizing P with
  | nil => exact ht₂_pure () fun s hs ↦ ⟨s, hs, rfl⟩
  | cons s ss ih =>
    rw [progSlots, realizeT_bind₂]
    refine HT₂.bind (ht₂_progPorts m₀ v B (slotPorts pub s) P) fun _ ↦
      (ih _).mono subset_rfl fun _ ↦ ?_
    rintro s'' ⟨s', ⟨s₀, hs₀, h₁⟩, h₂⟩
    refine ⟨s₀, hs₀, ?_⟩
    rw [List.flatMap_cons, List.map_append]
    exact progsRel_append h₁ h₂

/-- **The challenger's local operations and permutation calls keep every register set.** -/
theorem ht_challengeT_perm (pub : Pub) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A)
    (hc : (∃ o, c = .prim o) ∨ ∃ p E ℓ, c = .query (.perm p) E ℓ) (P : Set PReg) :
    HT m₀ (realizeT v (challengeT Selections cwUpd pub A c)) P fun _ ↦ P := by
  rcases hc with ⟨o, rfl⟩ | ⟨p, E, ℓ, rfl⟩
  · exact ht_sponge m₀ v _ P
  · exact ht_sponge m₀ v _ P

end templateX

/-! ## Read programs as functions of the register -/

section det

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} {M : Type} [Fintype M]
  [DecidableEq M] (m₀ : Finset S × M) (v : (s : S) → D s) (good : LazyProg X Z S D → Prop)

/-- **A read program answers as a function of the register**: from registers without empty cell,
run lifted, realized and in the decompressed basis, it returns `out s` and leaves `fin s`. -/
def Det {B : QReg} {α : Type} (y : QComp (hwReadSpec X Z M) B B α) (out : PRegOf S M → α)
    (fin : PRegOf S M → PRegOf S M) : Prop :=
  ∀ P : Set (PRegOf S M), (∀ s ∈ P, NoBot s) →
    HT₂ m₀ (realizeT v (readLiftQ good y)) P fun a ↦ {s' | ∃ s ∈ P, a = out s ∧ s' = fin s}

/-- `Det` for a logging read program, at every starting log. -/
def DetS {B : QReg} {α : Type}
    (x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α)
    (out : PRegOf S M → List (SpongeRead X Z) → α × List (SpongeRead X Z))
    (fin : PRegOf S M → List (SpongeRead X Z) → PRegOf S M) : Prop :=
  ∀ l, Det m₀ v good (x.run l) (fun s ↦ out s l) fun s ↦ fin s l

variable {m₀ v good}

theorem Det.congr {B : QReg} {α : Type} {y : QComp (hwReadSpec X Z M) B B α}
    {out out' : PRegOf S M → α} {fin fin' : PRegOf S M → PRegOf S M} (h : Det m₀ v good y out fin)
    (e : ∀ s, NoBot s → out s = out' s ∧ fin s = fin' s) : Det m₀ v good y out' fin' := by
  intro P hP
  refine (h P hP).mono subset_rfl fun a ↦ ?_
  rintro s' ⟨s, hs, ha, rfl⟩
  obtain ⟨e₁, e₂⟩ := e s (hP s hs)
  exact ⟨s, hs, ha.trans e₁, e₂⟩

theorem det_pure {B : QReg} {α : Type} (a : α) :
    Det m₀ v good (QuantumComp₂.pure a : QComp (hwReadSpec X Z M) B B α) (fun _ ↦ a)
      fun s ↦ s :=
  fun _ _ ↦ ht₂_pure a fun s hs ↦ ⟨s, hs, rfl, rfl⟩

theorem Det.bind {B : QReg} {α β : Type} {x : QComp (hwReadSpec X Z M) B B α}
    {out : PRegOf S M → α} {fin : PRegOf S M → PRegOf S M} (hx : Det m₀ v good x out fin)
    {k : α → QComp (hwReadSpec X Z M) B B β} {out' : α → PRegOf S M → β}
    {fin' : α → PRegOf S M → PRegOf S M} (hk : ∀ a, Det m₀ v good (k a) (out' a) (fin' a)) :
    Det m₀ v good (x.bind k) (fun s ↦ out' (out s) (fin s)) fun s ↦ fin' (out s) (fin s) := by
  intro P hP
  rw [readLift_bind₂, realizeT_bind₂]
  refine HT₂.bind ((hx P hP).and_noBot hP) fun a ↦
    ((hk a) _ fun s hs ↦ hs.2).mono subset_rfl fun b ↦ ?_
  rintro s'' ⟨s', ⟨⟨s, hs, rfl, rfl⟩, -⟩, rfl, rfl⟩
  exact ⟨s, hs, rfl, rfl⟩

theorem Det.map {B : QReg} {α β : Type} {x : QComp (hwReadSpec X Z M) B B α}
    {out : PRegOf S M → α} {fin : PRegOf S M → PRegOf S M} (hx : Det m₀ v good x out fin)
    (f : α → β) : Det m₀ v good (x.map f) (fun s ↦ f (out s)) fin := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact hx.bind fun a ↦ det_pure (f a)

/-- **A read answers the view's cell with the memory and updates the memory.** -/
theorem det_readCall (c : HwRead X Z M) (B : QReg) :
    Det m₀ v good (readCall c B) (fun s ↦ viewAns s c) fun s ↦ readFin s c := by
  intro P _ ρ hρ a
  rw [realizeT_readLift_readCall]
  erw [QuantumRuntime.run₂_queryBind, DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun r ↦ ?_
  have hq := querySupportedOn_queryStep_imp (decR (X := X) (Z := Z) m₀)
    (.inl (.inl (.inr (liftRead c)))) B
    (Equiv.uniqueProd B Unit).symm r P {s' | ∃ s ∈ P, r = liftAns s c ∧ s' = readFin s c}
    (fun τ hτ ↦ decR_readU_supp m₀ c r P τ hτ) hρ
  rw [QuantumRuntime.run₂_act_bind]
  erw [DSubInstrument.branch_bind_apply]
  refine QuerySupportedOn.tsum fun u ↦ ?_
  rw [QuantumRuntime.run₂_pure]
  by_cases ha : a = lowerRes c r
  · subst ha
    rw [SubInstrument.branch_pure_self, LinearMap.id_apply, DSubInstrument.branch_frame_apply]
    refine (QuerySupportedOn.amplify_snd (q := fun s : PRegOf S M ↦ s) hq _).mono ?_
    rintro s' ⟨s, hs, hr, rfl⟩
    exact ⟨s, hs, by rw [hr, lowerRes_liftAns], rfl⟩
  · rw [SubInstrument.branch_pure_of_ne ha]
    exact querySupportedOn_zero _ _

/-! ### Stateful read programs -/

theorem detS_pure {B : QReg} {α : Type} (a : α) :
    DetS m₀ v good
      (pure a : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α)
      (fun _ l ↦ (a, l)) fun s _ ↦ s :=
  fun l ↦ det_pure (a, l)

theorem DetS.bind {B : QReg} {α β : Type}
    {x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α}
    {out : PRegOf S M → List (SpongeRead X Z) → α × List (SpongeRead X Z)}
    {fin : PRegOf S M → List (SpongeRead X Z) → PRegOf S M} (hx : DetS m₀ v good x out fin)
    {f : α → StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) β}
    {g : α → PRegOf S M → List (SpongeRead X Z) → β × List (SpongeRead X Z)}
    {h : α → PRegOf S M → List (SpongeRead X Z) → PRegOf S M}
    (hf : ∀ a, DetS m₀ v good (f a) (g a) (h a)) :
    DetS m₀ v good (x >>= f) (fun s l ↦ g (out s l).1 (fin s l) (out s l).2)
      fun s l ↦ h (out s l).1 (fin s l) (out s l).2 := by
  intro l
  rw [StateT.run_bind]
  exact (hx l).bind fun p ↦ hf p.1 p.2

theorem DetS.map {B : QReg} {α β : Type}
    {x : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) α}
    {out : PRegOf S M → List (SpongeRead X Z) → α × List (SpongeRead X Z)}
    {fin : PRegOf S M → List (SpongeRead X Z) → PRegOf S M} (hx : DetS m₀ v good x out fin)
    (f : α → β) :
    DetS m₀ v good (f <$> x) (fun s l ↦ (f (out s l).1, (out s l).2)) fin := by
  rw [map_eq_bind_pure_comp]
  exact hx.bind fun a ↦ detS_pure (f a)

/-- A read followed by a function of its result. -/
theorem det_readCall_pure {α : Type} (c : HwRead X Z M) (B : QReg) (f : c.Result → α) :
    Det m₀ v good ((readCall c B).bind fun r ↦ QuantumComp₂.pure (f r))
      (fun s ↦ f (viewAns s c)) fun s ↦ readFin s c :=
  (det_readCall c B).bind fun r ↦ det_pure (f r)

theorem detS_rdK (B : QReg) (x : X) :
    DetS m₀ v good (rdK (M := M) B x)
      (fun s l ↦ ((viewAns s (.readK x (keepMem (M := M)))).1.getD 0,
        l ++ [.k x ((viewAns s (.readK x (keepMem (M := M)))).1.getD 0)]))
      fun s _ ↦ readFin s (.readK x keepMem) := by
  intro l
  have h := det_readCall_pure (m₀ := m₀) (v := v) (good := good) (.readK x (keepMem (M := M))) B
    fun r ↦ (r.1.getD 0, l ++ [.k x (r.1.getD 0)])
  exact h

theorem detS_rdK' (B : QReg) (x : X) :
    DetS m₀ v good (rdK' (M := M) B x)
      (fun s l ↦ ((viewAns s (.readK' x (keepMem (M := M)))).1.getD 0,
        l ++ [.k' x ((viewAns s (.readK' x (keepMem (M := M)))).1.getD 0)]))
      fun s _ ↦ readFin s (.readK' x keepMem) := by
  intro l
  have h := det_readCall_pure (m₀ := m₀) (v := v) (good := good) (.readK' x (keepMem (M := M))) B
    fun r ↦ (r.1.getD 0, l ++ [.k' x (r.1.getD 0)])
  exact h

theorem detS_rdHU (B : QReg) (z : Z) (u : M → Option X → M) :
    DetS m₀ v good (rdHU M B z u)
      (fun s l ↦ ((viewAns s (.readH z u)).1.getD 0,
        l ++ [.h z ((viewAns s (.readH z u)).1.getD 0)]))
      fun s _ ↦ readFin s (.readH z u) := by
  intro l
  have h := det_readCall_pure (m₀ := m₀) (v := v) (good := good) (.readH z u) B
    fun r ↦ (r.1.getD 0, l ++ [.h z (r.1.getD 0)])
  exact h

end det

/-! ## One-block trials as functions of the view -/

section trial

/-- The state after `π` in a one-block trial on the block `b`. -/
def trialMid (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (b : X) : X × Z :=
  π ((0 : X) + b, (0 : Z) + t.2.1 ((0 : X) + b))

/-- The rate after a one-block trial on the block `b`. -/
def trialRate (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (b : X) : X :=
  (trialMid t π b).1 + t.1 ((trialMid t π b).2 + t.2.2 (trialMid t π b).1)

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} {M : Type} [Fintype M]
  [DecidableEq M] {m₀ : Finset S × M} {v : (s : S) → D s} {good : LazyProg X Z S D → Prop}

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
/-- The memory after a one-block trial read with the update `u`. -/
def trialMem (u : X → X → M → Option X → M) (π : Equiv.Perm (X × Z)) (b : X)
    (s : PRegOf S M) : M :=
  u b (trialMid (regFns s) π b).1 s.2.2.2 ((hwView s.2.1 s.1).1
    ((trialMid (regFns s) π b).2 + (regFns s).2.2 (trialMid (regFns s) π b).1))

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] in
/-- On a register without empty cell, the view's `h`-cell is the register's function. -/
theorem hwView_h_of_noBot {s : PRegOf S M} (hs : NoBot s) (z : Z) :
    (hwView s.2.1 s.1).1 z = some ((regFns s).1 z) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (or_isSome (s.2.1.1 z) (hs.1 z))
  show (s.2.1.1 z).or (s.1.1 z) = some (((s.2.1.1 z).or (s.1.1 z)).getD 0)
  rw [ha]
  rfl

/-- **A one-block trial answers the view's hash** and updates the memory by its `h`-read. -/
theorem det_hashTrial (u : X → X → M → Option X → M) (π : Equiv.Perm (X × Z))
    (B : QReg) {input : HashInput} {b : X} (hb : blocks input = [b]) :
    Det m₀ v good (hashTrial M u π B input) (fun s ↦ out256 (trialRate (regFns s) π b))
      fun s ↦ (s.1, s.2.1, (s.2.2.1, trialMem u π b s)) := by
  unfold hashTrial
  rw [hb, List.foldlM_cons]
  have hr := (detS_rdK (m₀ := m₀) (v := v) (good := good) B (((0, 0) : X × Z).1 + b)).bind
    fun a ↦ (detS_rdK' (m₀ := m₀) (v := v) (good := good) B
      (π (((0, 0) : X × Z).1 + b, ((0, 0) : X × Z).2 + a)).1).bind fun c ↦
    (detS_rdHU (m₀ := m₀) (v := v) (good := good) B
      ((π (((0, 0) : X × Z).1 + b, ((0, 0) : X × Z).2 + a)).2 + c)
      (u b (π (((0, 0) : X × Z).1 + b, ((0, 0) : X × Z).2 + a)).1)).bind fun w ↦
    detS_pure (m₀ := m₀) (v := v) (good := good) (B := B)
      ((π (((0, 0) : X × Z).1 + b, ((0, 0) : X × Z).2 + a)).1 + w,
        (π (((0, 0) : X × Z).1 + b, ((0, 0) : X × Z).2 + a)).2 + c)
  have hr' : DetS m₀ v good (rdRoundU M u π B (0, 0) b) _ _ := hr
  have h2 := hr'.bind fun s' ↦ detS_pure (m₀ := m₀) (v := v) (good := good) (B := B) s'
  have h3 := ((h2.map fun s ↦ s.1).map out256) []
  have h4 := h3.map Prod.fst
  apply Det.congr
  · exact h4
  · exact fun _ _ ↦ ⟨rfl, rfl⟩

end trial

/-! ## The randomizer search -/

section grind

/-- The view's message digest of key `e` of layer `l` on `msg` with randomizer `ρ`. -/
def trialDigest (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter) (l : Layer)
    (e : KeyIndex) (msg : HashInput) (ρ : Randomizer) : Digest :=
  trunc128 ((blocks (msgInput P l e msg ρ)).foldl (absorbStep (spongePerm t π)) (0, 0)).1

/-- The randomizer search against the functions `t`: trials `base + trial`, ..., until a
codeword. -/
def grindV (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter) (l : Layer)
    (e : KeyIndex) (msg : HashInput) (base : Randomizer) :
    ℕ → ℕ → Option (Randomizer × Encoding)
  | 0, _ => none
  | n + 1, trial =>
    match Codeword.decode (trialDigest t π P l e msg (base + BitVec.ofNat digestBits trial)) with
    | some x => some (base + BitVec.ofNat digestBits trial, x)
    | none => grindV t π P l e msg base n (trial + 1)

/-- The memory after the randomizer search: the found selection, if the key was unselected. -/
noncomputable def grindMemV (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
    (l : Layer) (e : KeyIndex) (msg : HashInput) (base : Randomizer) (n trial : ℕ)
    (m : Selections) : Selections :=
  match m l e, grindV t π P l e msg base n trial with
  | none, some (ρ, _) =>
    m.select l e ((blocks (msgInput P l e msg ρ)).headD 0) (trialDigest t π P l e msg ρ)
  | _, _ => m

theorem trialDigest_eq {t : SpongeKeys X Z} {π : Equiv.Perm (X × Z)} {P : PublicParameter}
    {l : Layer} {e : KeyIndex} {msg : HashInput} {ρ : Randomizer} {b : X}
    (hb : blocks (msgInput P l e msg ρ) = [b]) :
    trialDigest t π P l e msg ρ = trunc128 (trialRate t π b) := by
  unfold trialDigest
  rw [hb]
  rfl

theorem length_blocks_msgInput (P : PublicParameter) (l : Layer) (e : KeyIndex) {msg : HashInput}
    (hm : msg.length ≤ 32) (ρ : Randomizer) : (blocks (msgInput P l e msg ρ)).length = 1 := by
  rw [msgInput, length_blocks, XmssCost.thInput_length, List.length_append]
  simp only [littleEndianBytes, List.length_ofFn]
  omega

theorem blocks_msgInput (P : PublicParameter) (l : Layer) (e : KeyIndex) {msg : HashInput}
    (hm : msg.length ≤ 32) (ρ : Randomizer) :
    blocks (msgInput P l e msg ρ) = [(blocks (msgInput P l e msg ρ)).headD 0] := by
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (length_blocks_msgInput P l e hm ρ)
  rw [hb]
  rfl

theorem grindMemV_zero (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
    (l : Layer) (e : KeyIndex) (msg : HashInput) (base : Randomizer) (trial : ℕ)
    (m : Selections) : grindMemV t π P l e msg base 0 trial m = m := by
  unfold grindMemV
  rcases m l e with _ | _ <;> rfl

theorem grindMemV_succ (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
    (l : Layer) (e : KeyIndex) (msg : HashInput) (base : Randomizer) (n trial : ℕ)
    (m : Selections) {b : X}
    (hb : blocks (msgInput P l e msg (base + BitVec.ofNat digestBits trial)) = [b]) :
    grindMemV t π P l e msg base (n + 1) trial m =
      match Codeword.decode (trialDigest t π P l e msg (base + BitVec.ofNat digestBits trial)) with
      | some _ => cwUpd l e b (trialMid t π b).1 m
          (some (t.1 ((trialMid t π b).2 + t.2.2 (trialMid t π b).1)))
      | none => grindMemV t π P l e msg base n (trial + 1) (cwUpd l e b (trialMid t π b).1 m
          (some (t.1 ((trialMid t π b).2 + t.2.2 (trialMid t π b).1)))) := by
  have hD := trialDigest_eq (t := t) (π := π) hb
  rcases hd : Codeword.decode (trialDigest t π P l e msg (base + BitVec.ofNat digestBits trial))
    with _ | x
  · have hv : ¬ Codeword.Valid (trunc128 (trialRate t π b)) := fun h ↦ by
      rw [hD, Codeword.decode, ite_eq_left h] at hd
      exact Option.some_ne_none _ hd
    have hcw : cwUpd l e b (trialMid t π b).1 m
        (some (t.1 ((trialMid t π b).2 + t.2.2 (trialMid t π b).1))) = m := by
      show (if m l e = none then cwSel m l e b (trialMid t π b).1
        (t.1 ((trialMid t π b).2 + t.2.2 (trialMid t π b).1)) else m) = m
      split_ifs
      · exact ite_eq_right hv
      · rfl
    rw [hcw]
    simp only [grindMemV, grindV, hd]
  · have hv : Codeword.Valid (trunc128 (trialRate t π b)) := by
      by_contra h
      rw [hD, Codeword.decode, ite_eq_right h] at hd
      exact Option.some_ne_none _ hd.symm
    simp only [grindMemV, grindV, hd]
    rcases hm : m l e with _ | y
    · show m.select l e
        ((blocks (msgInput P l e msg (base + BitVec.ofNat digestBits trial))).headD 0)
        (trialDigest t π P l e msg (base + BitVec.ofNat digestBits trial)) = _
      rw [hb, cwUpd_some_of_none l e b _ hm, cwSel, ite_eq_left (show Codeword.Valid
        (trunc128 ((trialMid t π b).1 + t.1 ((trialMid t π b).2 + t.2.2 (trialMid t π b).1)))
          from hv), hD]
      rfl
    · show m = if m l e = none then _ else m
      rw [hm, ite_eq_right (Option.some_ne_none y)]

variable {m₀ : Finset HPos × Selections} {v : HPos → Digest}

/-- **The randomizer search answers as a function of the view**: its result is `grindV` of the
register's functions, and it updates the memory by `grindMemV`. -/
theorem det_grindR (pub : Pub) (B : QReg) (l : Layer) (e : KeyIndex) {msg : HashInput}
    (hm : msg.length ≤ 32) (base : Randomizer) (n trial : ℕ) :
    Det m₀ v goodAll (grindR Selections cwUpd pub B l e msg base n trial)
      (fun s ↦ grindV (regFns s) pub.perm pub.param l e msg base n trial)
      (fun s ↦ (s.1, s.2.1,
        (s.2.2.1, grindMemV (regFns s) pub.perm pub.param l e msg base n trial s.2.2.2))) := by
  induction n generalizing trial with
  | zero =>
    refine (det_pure none).congr fun s _ ↦ ⟨rfl, ?_⟩
    rw [grindMemV_zero]
  | succ n ih =>
    obtain ⟨b, hb⟩ : ∃ b, blocks (msgInput pub.param l e msg
        (base + BitVec.ofNat digestBits trial)) = [b] :=
      ⟨_, blocks_msgInput pub.param l e hm (base + BitVec.ofNat digestBits trial)⟩
    have aux : ∀ out : HashOutput, Det m₀ v goodAll
        (match Codeword.decode (truncateHash out) with
          | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
          | none => grindR Selections cwUpd pub B l e msg base n (trial + 1))
        (fun s ↦ match Codeword.decode (truncateHash out) with
          | some x => some (base + BitVec.ofNat digestBits trial, x)
          | none => grindV (regFns s) pub.perm pub.param l e msg base n (trial + 1))
        (fun s ↦ match Codeword.decode (truncateHash out) with
          | some _ => s
          | none => (s.1, s.2.1, (s.2.2.1,
              grindMemV (regFns s) pub.perm pub.param l e msg base n (trial + 1) s.2.2.2))) := by
      intro out
      cases Codeword.decode (truncateHash out) with
      | none => exact ih (trial + 1)
      | some x => exact det_pure _
    rw [grindR]
    refine ((det_hashTrial (cwUpd l e) pub.perm B hb).bind aux).congr fun s hs ↦ ⟨?_, ?_⟩
    · show (match Codeword.decode (trunc128 (trialRate (regFns s) pub.perm b)) with
          | some x => some (base + BitVec.ofNat digestBits trial, x)
          | none => grindV (regFns s) pub.perm pub.param l e msg base n (trial + 1)) = _
      rw [grindV, trialDigest_eq hb]
    · show (match Codeword.decode (trunc128 (trialRate (regFns s) pub.perm b)) with
          | some _ => (s.1, s.2.1, (s.2.2.1, trialMem (cwUpd l e) pub.perm b s))
          | none => (s.1, s.2.1, (s.2.2.1, grindMemV (regFns s) pub.perm pub.param l e msg base n
              (trial + 1) (trialMem (cwUpd l e) pub.perm b s)))) = _
      rw [grindMemV_succ _ _ _ _ _ _ _ _ _ _ hb, ← trialDigest_eq hb]
      have hw : trialMem (cwUpd l e) pub.perm b s =
          cwUpd l e b (trialMid (regFns s) pub.perm b).1 s.2.2.2 (some ((regFns s).1
            ((trialMid (regFns s) pub.perm b).2 +
              (regFns s).2.2 (trialMid (regFns s) pub.perm b).1))) := by
        rw [trialMem, hwView_h_of_noBot hs]
      rw [hw]
      cases Codeword.decode (trialDigest (regFns s) pub.perm pub.param l e msg
        (base + BitVec.ofNat digestBits trial)) <;> rfl

end grind

/-! ## The challenge prefix -/

section prefixRun

variable (m₀ : Finset HPos × Selections) (v : HPos → Digest)

/-- **The substituted adversary with its signing log**: along the adversary's program, sponge-only
steps keep the invariant `Inv log`, and a signing request moves it to the extended log. -/
theorem ht_logSigns (pub : Pub) (Inv : SignLog → Set PReg)
    (hsign : ∀ (B : QReg) (r : SigningRequest) (log : SignLog),
      HT₂ m₀ (realizeT v (signT Selections cwUpd pub B r)) (Inv log)
        (fun sig ↦ Inv (log ++ [⟨r, sig⟩])))
    {Ω Y : QReg → Type} (leaf : ∀ u, Ω u → SignLog → Y u) (Q : (Σ u, Y u) → Set PReg)
    (hleaf : ∀ u y log, Inv log ⊆ Q ⟨u, leaf u y log⟩) {A : QReg}
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z))) Ω A)
    (log : SignLog) :
    HT m₀ ((logSigns (S := X × Z) leaf x log).substitute fun A c ↦
      realizeT v (challengeT Selections cwUpd pub A c)) (Inv log) Q := by
  induction x using IPFunctor.IFreeM.inductionOn generalizing log with
  | pure u y => exact ht_pure (leaf u y log) (hleaf u y log)
  | liftBind s c next ih =>
    refine HT.bind (x := realizeT v (challengeT Selections cwUpd pub s c))
      (Q := fun p ↦ Inv (logAfter c p.2.1 log)) ?_ fun u ans ↦ ?_
    · rcases c with o | ⟨p | r, E, ℓ⟩
      · exact ht_challengeT_perm m₀ v pub s _ (.inl ⟨o, rfl⟩) (Inv log)
      · exact ht_challengeT_perm m₀ v pub s _ (.inr ⟨p, E, ℓ, rfl⟩) (Inv log)
      · have hs : HT₂ m₀ (realizeT v (signAt Selections cwUpd pub r E ℓ)) (Inv log)
            fun sig ↦ Inv (log ++ [⟨r, sig⟩]) :=
          ht₂_realizeT_bind m₀ v (ht₂_act _ _) fun _ ↦ hsign _ r log
        exact ht_realizeT_bind m₀ v (ht_of_ht₂ hs) fun _ l ↦ ht_pure _ subset_rfl
    · obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b (logAfter c b log)

/-- **The challenge prefix**: the root revealed (label grown by the root's position), then the
adversary against the challenger with its signing log, moving the invariant `Inv log` along the
log; it returns the public key of the revealed root. -/
theorem ht₂_prefixT (pub : Pub) (A : Adversary (X × Z)) (Inv : SignLog → Set PReg)
    (hsign : ∀ (B : QReg) (r : SigningRequest) (log : SignLog),
      HT₂ m₀ (realizeT v (signT Selections cwUpd pub B r)) (Inv log)
        (fun sig ↦ Inv (log ++ [⟨r, sig⟩])))
    (P₀ : Set PReg) (hroot : ∀ s ∈ P₀, (s.1, s.2.1, (s.2.2.1 ∪ {.inl rootPos}, s.2.2.2)) ∈ Inv []) :
    HT₂ m₀ (realizeT v (prefixT Selections cwUpd pub A)) P₀
      (fun pre ↦ {s | s ∈ Inv pre.2.2 ∧
        pre.1 = ⟨extendVals (restrictTo {.inl rootPos} v) rootPos, pub.param⟩}) := by
  unfold prefixT
  refine ht₂_revealThen m₀ v _ _ P₀ _ fun mem ↦ ?_
  refine ht₂_realizeT_bind m₀ v (Q := fun run ↦ Inv run.2) ?_ fun run ↦
    ht₂_pure _ fun s hs ↦ ⟨hs, rfl⟩
  refine ht₂_of_ht (HT.mono (P := Inv []) ?_ ?_ fun _ ↦ subset_rfl)
  · have e := realizeT_substitute (good := goodAll) (M := Selections) v
      (challengeT Selections cwUpd pub)
      (withSignLog (A ⟨extendVals (restrictTo {.inl rootPos} v, mem).1 rootPos, pub.param⟩))
    refine (congrArg (fun y ↦ HT m₀ y (Inv []) fun p ↦ Inv p.2.2.2) e).mpr ?_
    exact ht_logSigns m₀ v pub Inv hsign _
      (fun q : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) (Forgery × SignLog) u) ↦ Inv q.2.2.2)
      (fun _ _ _ ↦ subset_rfl) _ []
  · rintro s ⟨s₀, hs₀, -, rfl⟩
    exact hroot s₀ hs₀

end prefixRun

/-! ## The initial operator -/

/-- **The initial operator in the decompressed basis**: no empty cell, no hardwired cell, memory
`m₀`. -/
theorem init_dec {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]
    (m₀ : Finset S × M) :
    QuerySupportedOn (fun p : Unit × PRegOf S M ↦ p.2) {s | NoBot s ∧ s.2 = (hwEmpty X Z, m₀)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset S × M))
        (initU m₀)) := by
  have h0 : QuerySupportedOn (fun p : Unit × PRegOf S M ↦ p.2) {s | s.2 = (hwEmpty X Z, m₀)}
      (initU m₀) := by
    intro m m' hm
    change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
      Database.empty), hwEmpty X Z, m₀) : PRegOf S M)).matrix) m m' ≠ 0 at hm
    simp only [SubState.matrix_basis] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · exact ⟨congrArg Prod.snd he.1.symm, congrArg Prod.snd he.2.symm⟩
    · exact absurd rfl h
  exact querySupportedOn_inter (noBot_init m₀ (A := Unit) (SubState.basis ()).matrix)
    (querySupportedOn_conj_compressReg (P := fun b ↦ b = (hwEmpty X Z, m₀)) h0)

end Quantum.Xmss.Assembly

end
