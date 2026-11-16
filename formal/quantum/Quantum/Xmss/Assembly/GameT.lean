module

public import Quantum.Xmss.Assembly.Template
public import Quantum.Xmss.Assembly.Runtime1
public import Quantum.Xmss.Assembly.RecordPorts

@[expose] public section

/-!
# The template game against runtime 1

**The canonical runtime-2 game** (`runtime2Law`). For an honest table `L : HonestTable`, an inner
memory `M` with a trial update `upd : TrialUpd M` (Security: `M = Selections`, `upd = cwUpd`),
the initial memory `m₀ = (T₀, m)` (label `T₀`, canonically `∅`) and an adversary `A`, the runtime-2
game of `L` is
`(runtimeR m₀).evalDistMap .instruments (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ f`:
runtime 2 (no hardwired cell at the start) extended by the record ports, running the template
game with `L`'s public data `pubOf L` (parameter, `π`, keys), realized at `L`'s hidden values
`valueAt L` (honest values and randomizer bases). Its winning probability observes `{true}` with
`ρ = SubState.basis ()` and `f = fun p ↦ p.2.2`.

**From the realized template to the read program.**
* `DropRec S x y`: `x` over `recHwSpec X Z S M` is `y` over `hwSpec X Z Unit` with record calls
  inserted, its reads updating the memory (any update) where `y`'s keep it. The tools here
  (`ReadsRel` and its `bind`/`map`/`act` lemmas, `realizeT_bind₂`, `readLift_bind₂`,
  `dropRec_realizeT_substitute`, `dropRec_readLift_liftOrdinary`, `dropRec_revealThen`,
  `dropRec_progSlots`) give, in RecordDrop, the structural fact
  `dropRec_gameT : DropRec HPos (realizeT v (gameT M upd pub A)) (gameD Unit pub v A)` and the
  simulation `evalDistMap_runtime1R_eq` (forgetting the memory register, which is classical).
* `dropsTo_gameD`: if every program call hardwires a cell of `W` with its `W` value
  (`ProgsOf W pub v`), `gameD` is `gameReadsT` with program calls inserted (Runtime1's `DropsTo`).
  `progsOf_tableHw`: at `pubOf L`, `valueAt L` this holds for `tableHw L`, the cells of the honest
  paths of every slot a layer signature makes public with their `L.keys` values (`roundH`'s
  last-round correction vanishes: `roundH_snd`); `ProgsOf.mono` extends it to every `W` with
  `HwLe (tableHw L) W`.

**`gameReadsT` against `gameReads`: they differ in the signer.** With
`b = honestEval L.keys L.perm (schemeWithHashFromSeed.keygen L.masterSeed)` (TableComp's `b` at
`t = L.keys`, `π = L.perm`, `S0 = L.masterSeed`; `b.1 = (L.publicKey, L.secretKey)`), both are
`gameReadsWith M L.perm L.secretKey _ L.publicKey A` (`gameReads_honest`, `gameReadsT_pubOf`): the
same simulated adversary calls, verification reads and winning condition. The signer of
`gameReads` is `signReads`, the read program of the whole signer (scheme seed rederivation, the
randomizer base, the trials, the chain starts and openings, the bottom tree's path and root); the
signer of `gameReadsT` is `signAtR`, which reads only the trials (`grindR`, the base
`valueAt L (.inr lab)`) and takes the opened chain values, the paths and the bottom root from
`valueAt L`.
* Against the honest functions (`spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m`) every read is
  deterministic and both signers return `L.signature r` (`readsTo_signWithR`), so the laws agree
  (`evalDistMap_gameReads_eq_gameReadsT`) and the QRPM game at `L` has the law of `gameReadsT`
  (`evalDistMap_game_eq_gameReadsT`, G1 → G2 for `gameReadsT`).
* **Missing: lazy sampling of the signer's data.** TableComp's runtime 1 hardwires only key
  generation's reads (`readsHw b.2`, the top tree): `signReads`' reads of the randomizer base and
  of the bottom layer's cells hit the database there, while `gameReadsT` takes those values from
  `pubOf L`, `valueAt L`, so per table the two runtime-1 laws differ, and agree only on average.
  With the step above, the missing theorem is TableLaw's `spongeEvalDistMap_eq_tableLaw` applied to
  `gameReadsT` and an honest computation `full` (in place of key generation) such that, for every
  `t` and `L t = ⟨t, π, S0⟩`: (a) `gameReadsT M (pubOf (L t)) (valueAt (L t)) A = y (honestEval t π
  full)` for some `y` (the result of `full` determines the parameter and `valueAt (L t)`, the
  randomizer bases included; `gameReadsT` does not read `pub.keys`), and (b)
  `HwLe (tableHw (L t)) (readsHw (honestEval t π full).2)`. Not constructed here: `full` (both
  layers' trees, the scheme seed and parameter, the randomizer bases of all labels) and (a), (b).
-/

open Matrix
open scoped Kronecker

universe w

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma LeanXmss.RandomPermutationModel

/-! ## Sequencing, substitution and transport -/

section shape

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

omit [Fintype M] [DecidableEq M] in
/-- `DropsTo` for substitutions whose commands drop. -/
theorem dropsTo_substitute (L : Hw X Z) {spec₀ : QuantumOracleSpec.{0, 0}}
    {σ₁ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec X Z M))}
    {σ₂ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwReadSpec X Z M))}
    (h : ∀ A c, DropsTo L (σ₁ A c) (σ₂ A c)) {Ω : QReg → Type} {A : QReg}
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀) Ω A) :
    DropsTo L (x.substitute σ₁) (x.substitute σ₂) := by
  induction x using IPFunctor.IFreeM.inductionOn with
  | pure _ y => exact DropsTo.pure y
  | liftBind A c next ih =>
    rw [IPFunctor.IFreeM.substitute_liftBind, IPFunctor.IFreeM.substitute_liftBind]
    refine DropsTo.bind (h A c) fun u ans ↦ ?_
    obtain ⟨b, hb⟩ := ans
    subst hb
    exact ih b

end shape

/-! ## Programs with record calls -/

section drop

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} {M : Type}

variable (S) in
/-- **`DropRec S x y`**: the program `x` over `recHwSpec` (memory `Finset S × M`) is `y` over
`hwSpec` with memory `Unit`, with record calls inserted (each followed by the relabelling `e`
back to the register before the call), its reads updating the memory arbitrarily where `y`'s keep
it, and its continuations after a read depending on the read value only. -/
inductive DropRec {Ω : QReg → Type w} : {A : QReg} →
    QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A →
      QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω A → Prop
  | pure {A : QReg} (y : Ω A) : DropRec (QuantumComp.pure y) (QuantumComp.pure y)
  | prim {A : QReg} (o : LocalSig.instruments.{0}.Op A)
      {k : (b : LocalSig.instruments.{0}.Outcome o) →
        QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
          (LocalSig.instruments.next o b)}
      {k' : (b : LocalSig.instruments.{0}.Outcome o) →
        QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω (LocalSig.instruments.next o b)}
      (h : ∀ b, DropRec (k b) (k' b)) :
      DropRec (QuantumComp.primBind o k) (QuantumComp.primBind o k')
  | sponge {A : QReg} (i : SpongePort) (E : QReg)
      (ℓ : A ≃ (hwSpec X Z Unit).In (.inl (.inl i)) × E)
      {k : (recHwSpec X Z S M).Result (.inl (.inl (.inl i))) →
        QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
          (QReg.of ((recHwSpec X Z S M).Out (.inl (.inl (.inl i))) × E))}
      {k' : (hwSpec X Z Unit).Result (.inl (.inl i)) →
        QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω
          (QReg.of ((hwSpec X Z Unit).Out (.inl (.inl i)) × E))}
      (h : ∀ r, DropRec (k r) (k' r)) :
      DropRec (QuantumComp.queryBind (spec := recHwSpec X Z S M) (.inl (.inl (.inl i))) E ℓ k)
        (QuantumComp.queryBind (spec := hwSpec X Z Unit) (.inl (.inl i)) E ℓ k')
  | readH {A : QReg} (z : Z) (upd : Finset S × M → Option X → Finset S × M) (E : QReg)
      (ℓ : A ≃ (hwSpec X Z Unit).In (.inl (.inr (.readH z keepMem))) × E)
      {k : (recHwSpec X Z S M).Result (.inl (.inl (.inr (.readH z upd)))) →
        QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
          (QReg.of ((recHwSpec X Z S M).Out (.inl (.inl (.inr (.readH z upd)))) × E))}
      {k' : (hwSpec X Z Unit).Result (.inl (.inr (.readH z keepMem))) →
        QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω
          (QReg.of ((hwSpec X Z Unit).Out (.inl (.inr (.readH z keepMem))) × E))}
      (h : ∀ (o : Option X) (p : Finset S × M), DropRec (k (o, p)) (k' (o, ()))) :
      DropRec (QuantumComp.queryBind (spec := recHwSpec X Z S M)
          (.inl (.inl (.inr (.readH z upd)))) E ℓ k)
        (QuantumComp.queryBind (spec := hwSpec X Z Unit) (.inl (.inr (.readH z keepMem))) E ℓ k')
  | readK {A : QReg} (x : X) (upd : Finset S × M → Option Z → Finset S × M) (E : QReg)
      (ℓ : A ≃ (hwSpec X Z Unit).In (.inl (.inr (.readK x keepMem))) × E)
      {k : (recHwSpec X Z S M).Result (.inl (.inl (.inr (.readK x upd)))) →
        QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
          (QReg.of ((recHwSpec X Z S M).Out (.inl (.inl (.inr (.readK x upd)))) × E))}
      {k' : (hwSpec X Z Unit).Result (.inl (.inr (.readK x keepMem))) →
        QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω
          (QReg.of ((hwSpec X Z Unit).Out (.inl (.inr (.readK x keepMem))) × E))}
      (h : ∀ (o : Option Z) (p : Finset S × M), DropRec (k (o, p)) (k' (o, ()))) :
      DropRec (QuantumComp.queryBind (spec := recHwSpec X Z S M)
          (.inl (.inl (.inr (.readK x upd)))) E ℓ k)
        (QuantumComp.queryBind (spec := hwSpec X Z Unit) (.inl (.inr (.readK x keepMem))) E ℓ k')
  | readK' {A : QReg} (x : X) (upd : Finset S × M → Option Z → Finset S × M) (E : QReg)
      (ℓ : A ≃ (hwSpec X Z Unit).In (.inl (.inr (.readK' x keepMem))) × E)
      {k : (recHwSpec X Z S M).Result (.inl (.inl (.inr (.readK' x upd)))) →
        QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
          (QReg.of ((recHwSpec X Z S M).Out (.inl (.inl (.inr (.readK' x upd)))) × E))}
      {k' : (hwSpec X Z Unit).Result (.inl (.inr (.readK' x keepMem))) →
        QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω
          (QReg.of ((hwSpec X Z Unit).Out (.inl (.inr (.readK' x keepMem))) × E))}
      (h : ∀ (o : Option Z) (p : Finset S × M), DropRec (k (o, p)) (k' (o, ()))) :
      DropRec (QuantumComp.queryBind (spec := recHwSpec X Z S M)
          (.inl (.inl (.inr (.readK' x upd)))) E ℓ k)
        (QuantumComp.queryBind (spec := hwSpec X Z Unit) (.inl (.inr (.readK' x keepMem))) E ℓ k')
  | prog {A : QReg} (c : HwProg X Z) (E : QReg) (ℓ : A ≃ (hwSpec X Z Unit).In (.inr c) × E)
      {k : (recHwSpec X Z S M).Result (.inl (.inr c)) →
        QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
          (QReg.of ((recHwSpec X Z S M).Out (.inl (.inr c)) × E))}
      {k' : (hwSpec X Z Unit).Result (.inr c) →
        QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω
          (QReg.of ((hwSpec X Z Unit).Out (.inr c) × E))}
      (h : ∀ r, DropRec (k r) (k' r)) :
      DropRec (QuantumComp.queryBind (spec := recHwSpec X Z S M) (.inl (.inr c)) E ℓ k)
        (QuantumComp.queryBind (spec := hwSpec X Z Unit) (.inr c) E ℓ k')
  | record {A : QReg} (T : Finset S) (E : QReg)
      (ℓ : A ≃ (recHwSpec X Z S M).In (.inr T) × E)
      (e : (recHwSpec X Z S M).Out (.inr T) × E ≃ A) (he : ∀ a, e (ℓ a) = a)
      {k : (recHwSpec X Z S M).Result (.inr T) →
        QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A}
      {y : QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω A}
      (h : ∀ r, DropRec (k r) y) :
      DropRec (QuantumComp.queryBind (spec := recHwSpec X Z S M) (.inr T) E ℓ fun r ↦
        QuantumComp.primBind (L := LocalSig.instruments.{0})
          ⟨Unit, fun _ ↦ A, SubInstrument.relabel e⟩ fun _ ↦ k r) y

/-- `DropRec` is compatible with sequencing. -/
theorem DropRec.bind {Ω Ω' : QReg → Type w} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A}
    {y : QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω A} (h : DropRec S x y)
    {k : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω' u}
    {k' : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω' u}
    (hk : ∀ u l, DropRec S (k u l) (k' u l)) : DropRec S (x.bind k) (y.bind k') := by
  induction h with
  | pure y => exact hk _ y
  | prim o _ ih => exact DropRec.prim o ih
  | sponge i E ℓ _ ih => exact DropRec.sponge i E ℓ ih
  | @readH _ z upd E ℓ k₀ k₀' _ ih =>
    exact DropRec.readH (S := S) z upd E ℓ (k := fun r ↦ (k₀ r).bind k)
      (k' := fun r ↦ (k₀' r).bind k') ih
  | @readK _ x upd E ℓ k₀ k₀' _ ih =>
    exact DropRec.readK (S := S) x upd E ℓ (k := fun r ↦ (k₀ r).bind k)
      (k' := fun r ↦ (k₀' r).bind k') ih
  | @readK' _ x upd E ℓ k₀ k₀' _ ih =>
    exact DropRec.readK' (S := S) x upd E ℓ (k := fun r ↦ (k₀ r).bind k)
      (k' := fun r ↦ (k₀' r).bind k') ih
  | prog c E ℓ _ ih => exact DropRec.prog c E ℓ ih
  | record T E ℓ e he _ ih => exact DropRec.record T E ℓ e he ih

/-- `DropRec` is compatible with sequencing of programs on a fixed final register. -/
theorem DropRec.bind₂ {A B C : QReg} {α β : Type}
    {x : QComp (recHwSpec X Z S M) A B α} {y : QComp (hwSpec X Z Unit) A B α}
    (h : DropRec S x y) {k : α → QComp (recHwSpec X Z S M) B C β}
    {k' : α → QComp (hwSpec X Z Unit) B C β} (hk : ∀ a, DropRec S (k a) (k' a)) :
    DropRec S (x.bind k) (y.bind k') :=
  DropRec.bind h (by rintro u ⟨rfl, a⟩; exact hk a)

end drop

section shape2

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] {S : Type}
  {M : Type}

/-- `DropRec` for substitutions whose commands drop. -/
theorem dropRec_substitute {spec₀ : QuantumOracleSpec.{0, 0}}
    {σ₁ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z S M))}
    {σ₂ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec X Z Unit))}
    (h : ∀ A c, DropRec S (σ₁ A c) (σ₂ A c)) {Ω : QReg → Type} {A : QReg}
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀) Ω A) :
    DropRec S (x.substitute σ₁) (x.substitute σ₂) := by
  induction x using IPFunctor.IFreeM.inductionOn with
  | pure _ y => exact DropRec.pure y
  | liftBind A c next ih =>
    rw [IPFunctor.IFreeM.substitute_liftBind, IPFunctor.IFreeM.substitute_liftBind]
    refine DropRec.bind (h A c) fun u ans ↦ ?_
    obtain ⟨b, hb⟩ := ans
    subst hb
    exact ih b

/-- Substituting twice is substituting the substituted commands. -/
theorem substitute_substitute {I : Type*} {P Q R : IPFunctor.Endo I}
    (σ : IPFunctor.CommandSubstitution P Q) (τ : IPFunctor.CommandSubstitution Q R)
    {Ω : I → Type*} {s : I} (x : IPFunctor.IFreeM P Ω s) :
    (x.substitute σ).substitute τ = x.substitute fun s a ↦ (σ s a).substitute τ := by
  induction x using IPFunctor.IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind s a next ih =>
    rw [IPFunctor.IFreeM.substitute_liftBind, IPFunctor.IFreeM.substitute_liftBind,
      IPFunctor.IFreeM.substitute_bind]
    congr 1
    funext t ans
    obtain ⟨b, hb⟩ := ans
    subst hb
    exact ih b

universe u v

variable {D : S → Type} {good : LazyProg X Z S D → Prop}

theorem realizeT_bind {Λ : LocalSig.{u, v}} {Ω Ω' : QReg → Type} {A : QReg}
    (val : (s : S) → D s) (x : QuantumComp Λ (tmplSpec X Z S D M good) Ω A)
    (g : ∀ u, Ω u → QuantumComp Λ (tmplSpec X Z S D M good) Ω' u) :
    realizeT val (x.bind g) = (realizeT val x).bind fun u a ↦ realizeT val (g u a) := by
  have h := IPFunctor.IFreeM.substitute_bind (tmplLens (good := good) (M := M) val).toSubstitution
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor Λ (tmplSpec X Z S D M good)) Ω A) g
  simp only [IPFunctor.IFreeM.substitute_toSubstitution] at h
  exact h

theorem realizeT_bind₂ {A B C : QReg} {α β : Type} (val : (s : S) → D s)
    (x : QComp (tmplSpec X Z S D M good) A B α) (k : α → QComp (tmplSpec X Z S D M good) B C β) :
    realizeT val (x.bind k) = QuantumComp₂.bind (realizeT val x) fun a ↦ realizeT val (k a) := by
  refine (realizeT_bind (Λ := LocalSig.instruments) val x _).trans ?_
  congr 1
  funext u p
  rcases p with ⟨rfl, a⟩
  rfl

theorem realizeT_substitute {spec₀ : QuantumOracleSpec.{0, 0}} (v : (s : S) → D s)
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (tmplSpec X Z S D M good)))
    {Ω : QReg → Type} {A : QReg}
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀) Ω A) :
    realizeT v (x.substitute σ) = x.substitute fun A c ↦ realizeT v (σ A c) := by
  simp only [realizeT, ← IPFunctor.IFreeM.substitute_toSubstitution]
  exact substitute_substitute _ _ x

theorem dropRec_realizeT_bind {Ω Ω' : QReg → Type} {A : QReg} (v : (s : S) → D s)
    {x : QuantumComp LocalSig.instruments.{0} (tmplSpec X Z S D M good) Ω A}
    {y : QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω A}
    (h : DropRec S (realizeT v x) y)
    {g : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (tmplSpec X Z S D M good) Ω' u}
    {k : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (hwSpec X Z Unit) Ω' u}
    (hk : ∀ u a, DropRec S (realizeT v (g u a)) (k u a)) :
    DropRec S (realizeT v (x.bind g)) (y.bind k) := by
  rw [realizeT_bind]
  exact DropRec.bind h hk

theorem dropRec_realizeT_substitute {spec₀ : QuantumOracleSpec.{0, 0}} (v : (s : S) → D s)
    {σ₁ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (tmplSpec X Z S D M good))}
    {σ₂ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec X Z Unit))}
    (h : ∀ A c, DropRec S (realizeT v (σ₁ A c)) (σ₂ A c)) {Ω : QReg → Type} {A : QReg}
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀) Ω A) :
    DropRec S (realizeT v (x.substitute σ₁)) (x.substitute σ₂) := by
  rw [realizeT_substitute]
  exact dropRec_substitute h x

theorem dropRec_realizeT_act_bind {A B C : QReg} {α β : Type} (v : (s : S) → D s)
    (p : SubInstrument A B α) {k : α → QComp (tmplSpec X Z S D M good) B C β}
    {k' : α → QComp (hwSpec X Z Unit) B C β} (h : ∀ a, DropRec S (realizeT v (k a)) (k' a)) :
    DropRec S (realizeT v ((QComp.act p).bind k)) ((QComp.act p).bind k') :=
  DropRec.prim (o := (⟨α, fun _ ↦ B, p⟩ : LocalSig.instruments.{0}.Op A)) h

theorem readLift_bind₂ {A B C : QReg} {α β : Type} (x : QComp (hwReadSpec X Z M) A B α)
    (k : α → QComp (hwReadSpec X Z M) B C β) :
    readLiftQ good (x.bind k) =
      QuantumComp₂.bind (readLiftQ good x) fun a ↦ readLiftQ good (k a) := by
  have h := IPFunctor.IFreeM.substitute_bind (readLens (S := S) (D := D) good).toSubstitution
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwReadSpec X Z M))
      (QuantumComp₂.Leaf B α) A) (fun _ p ↦ p.casesOn fun h a ↦ h ▸ k a)
  simp only [IPFunctor.IFreeM.substitute_toSubstitution] at h
  refine h.trans ?_
  congr 1
  funext u p
  rcases p with ⟨rfl, a⟩
  rfl

/-- A program over `hwReadSpec` with memory `Unit` as one over `hwSpec`, fixed final register. -/
def liftReadC {A B : QReg} {α : Type} (y : QComp (hwReadSpec X Z Unit) A B α) :
    QComp (hwSpec X Z Unit) A B α :=
  liftReadProg y

theorem liftReadProg_bind₂ {A B C : QReg} {α β : Type} (x : QComp (hwReadSpec X Z Unit) A B α)
    (k : α → QComp (hwReadSpec X Z Unit) B C β) :
    liftReadC (x.bind k) = QuantumComp₂.bind (liftReadC x) fun a ↦ liftReadC (k a) := by
  have h := IPFunctor.IFreeM.substitute_bind (liftReadLens (X := X) (Z := Z) (M := Unit)).toSubstitution
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwReadSpec X Z Unit))
      (QuantumComp₂.Leaf B α) A) (fun _ p ↦ p.casesOn fun h a ↦ h ▸ k a)
  simp only [IPFunctor.IFreeM.substitute_toSubstitution] at h
  refine h.trans ?_
  congr 1
  funext u p
  rcases p with ⟨rfl, a⟩
  rfl

variable (good) in
/-- **A read program with memory `M` and one with memory `Unit` that read alike**: the template
lift of the first, realized at `v`, drops to the second. -/
abbrev ReadsRel (v : (s : S) → D s) {B C : QReg} {α : Type} (x : QComp (hwReadSpec X Z M) B C α)
    (y : QComp (hwReadSpec X Z Unit) B C α) : Prop :=
  DropRec S (realizeT v (readLiftQ good x)) (liftReadC y)

theorem readsRel_pure (v : (s : S) → D s) {B : QReg} {α : Type} (a : α) :
    ReadsRel good v (QuantumComp₂.pure a : QComp (hwReadSpec X Z M) B B α) (QuantumComp₂.pure a) :=
  DropRec.pure _

theorem ReadsRel.bind {v : (s : S) → D s} {A B C : QReg} {α β : Type}
    {x : QComp (hwReadSpec X Z M) A B α} {y : QComp (hwReadSpec X Z Unit) A B α}
    (h : ReadsRel good v x y) {k : α → QComp (hwReadSpec X Z M) B C β}
    {k' : α → QComp (hwReadSpec X Z Unit) B C β} (hk : ∀ a, ReadsRel good v (k a) (k' a)) :
    ReadsRel good v (x.bind k) (y.bind k') := by
  unfold ReadsRel
  rw [readLift_bind₂, realizeT_bind₂, liftReadProg_bind₂]
  exact DropRec.bind₂ h hk

theorem ReadsRel.map {v : (s : S) → D s} {A B : QReg} {α β : Type}
    {x : QComp (hwReadSpec X Z M) A B α} {y : QComp (hwReadSpec X Z Unit) A B α}
    (h : ReadsRel good v x y) (f : α → β) : ReadsRel good v (x.map f) (y.map f) := by
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure]
  exact h.bind fun a ↦ readsRel_pure v (f a)

theorem readsRel_act_bind (v : (s : S) → D s) {A B C : QReg} {α β : Type}
    (p : SubInstrument A B α) {k : α → QComp (hwReadSpec X Z M) B C β}
    {k' : α → QComp (hwReadSpec X Z Unit) B C β} (h : ∀ a, ReadsRel good v (k a) (k' a)) :
    ReadsRel good v ((QComp.act p).bind k) ((QComp.act p).bind k') :=
  DropRec.prim (o := (⟨α, fun _ ↦ B, p⟩ : LocalSig.instruments.{0}.Op A)) h

/-- A program over the sponge ports, lifted to the read ports at memories `M` and `Unit`. -/
theorem dropRec_readLift_liftOrdinary (v : (s : S) → D s) {Ω : QReg → Type} {A : QReg}
    (z : QuantumComp LocalSig.instruments.{0} (spongeSpec X Z) Ω A) :
    DropRec S (realizeT v (readLift good (z.liftOrdinary (t := hwReadCmdSpec X Z M))))
      (liftReadProg (z.liftOrdinary (t := hwReadCmdSpec X Z Unit))) := by
  induction z using QuantumComp.inductionOn with
  | pure _ y => exact DropRec.pure y
  | primBind _ o k ih => exact DropRec.prim o ih
  | queryBind _ i E ℓ k ih => exact DropRec.sponge i E ℓ ih

end shape2

/-! ## The game programs cells of the table with their table values -/

section absorb

variable {α β : Type} [AddCommGroup α] [AddCommGroup β]

/-- The rate after absorbing `msg` of length `j + 1` under `spongePerm t π`, from the state before
its last block. -/
theorem fst_foldl_spongePerm (t : SpongeKeys α β) (π : Equiv.Perm (α × β)) (msg : List α) {j : ℕ}
    (hj : msg.length = j + 1) :
    (msg.foldl (absorbStep (spongePerm t π)) (0, 0)).1 =
      (π (((msg.take j).foldl (absorbStep (spongePerm t π)) (0, 0)).1 + msg.getD j 0,
        ((msg.take j).foldl (absorbStep (spongePerm t π)) (0, 0)).2 +
          t.2.1 (((msg.take j).foldl (absorbStep (spongePerm t π)) (0, 0)).1 + msg.getD j 0))).1 +
      t.1 ((π (((msg.take j).foldl (absorbStep (spongePerm t π)) (0, 0)).1 + msg.getD j 0,
        ((msg.take j).foldl (absorbStep (spongePerm t π)) (0, 0)).2 +
          t.2.1 (((msg.take j).foldl (absorbStep (spongePerm t π)) (0, 0)).1 +
            msg.getD j 0))).2 +
        t.2.2 (π (((msg.take j).foldl (absorbStep (spongePerm t π)) (0, 0)).1 + msg.getD j 0,
          ((msg.take j).foldl (absorbStep (spongePerm t π)) (0, 0)).2 +
            t.2.1 (((msg.take j).foldl (absorbStep (spongePerm t π)) (0, 0)).1 +
              msg.getD j 0))).1) := by
  obtain ⟨l, b, rfl⟩ : ∃ l b, msg = l ++ [b] :=
    ⟨msg.dropLast, msg.getLast (by rintro rfl; simp at hj), (List.dropLast_append_getLast _).symm⟩
  have hl : l.length = j := by simpa using hj
  subst hl
  have hb : (l ++ [b]).getD l.length 0 = b := by simp
  rw [List.take_left' rfl, hb, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

end absorb

section table

/-- The rate after the last round of the absorption of `msg`, in the template's terms. -/
theorem spongeHash_lastRound (pub : Pub) (msg : List X) {j : ℕ} (hj : msg.length = j + 1) :
    spongeHash (spongePerm pub.keys pub.perm) msg =
      (midAt pub (stateAt pub msg j) (msg.getD j 0)).1 +
        pub.keys.1 ((midAt pub (stateAt pub msg j) (msg.getD j 0)).2 +
          pub.keys.2.2 (midAt pub (stateAt pub msg j) (msg.getD j 0)).1) :=
  fst_foldl_spongePerm pub.keys pub.perm msg hj

theorem embed128_xor_self (d : Digest) : embed128 (d ^^^ d) = 0 := by
  funext j
  simp [embed128]

theorem length_flatMap_of_length {γ δ : Type} {g : γ → List δ} {n : ℕ}
    (hg : ∀ a, (g a).length = n) (l : List γ) : (l.flatMap g).length = n * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, hg, List.length_cons]
    ring

/-- Payload lengths do not depend on the values. -/
theorem slotPayload_length_congr (f g : ValPos → Digest) (s : Slot) :
    (slotPayload f s).length = (slotPayload g s).length := by
  cases s
  case leaf =>
    refine (length_flatMap_of_length (n := 16) (fun _ ↦ List.length_ofFn) _).trans ?_
    refine Eq.trans ?_ (length_flatMap_of_length (n := 16) (fun _ ↦ List.length_ofFn) _).symm
    exact congrArg (16 * ·) (List.length_ofFn.trans List.length_ofFn.symm)
  all_goals simp only [slotPayload, Verification.chainPayload, nodePayload, littleEndianBytes,
    List.length_append, List.length_ofFn]

/-- A slot's input has `nBlocks` blocks at any values. -/
theorem blocks_slotInput_length (pub : Pub) (s : Slot) (f : ValPos → Digest) :
    (blocks (slotInput pub s f)).length = nBlocks pub s := by
  simp only [nBlocks, length_blocks, slotInput, thInput, hasherInput, List.length_append,
    slotPayload_length_congr f (fun _ ↦ 0) s]

theorem valuePos_cpos (L : HonestTable) (l : Layer) (e : KeyIndex) (i : ChainIndex) (j : ℕ) :
    valuePos L (cpos l e i j) = L.chainValue l e i (j % chainLength) :=
  rfl

theorem valuePos_tpos (L : HonestTable) (l : Layer) (level index : ℕ) :
    valuePos L (tpos l level index) = L.treeValue l (level % (layerHeight + 1)) (index % 2 ^ 32) :=
  rfl

/-- The slots of a layer signature: chain steps, the leaf, the nodes on the path. -/
theorem mem_layerSlots {l : Layer} {e : KeyIndex} {w : Encoding} {s : Slot}
    (hs : s ∈ layerSlots l e w) :
    (∃ step i, s = .chain l e step i) ∨ s = .leaf l e ∨
      ∃ lev < layerHeight, s = .node l (lev + 1) (e.val / 2 ^ (lev + 1)) := by
  simp only [layerSlots, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons,
    List.mem_range] at hs
  rcases hs with ⟨i, -, step, -, rfl⟩ | rfl | ⟨lev, hlev, rfl⟩
  · exact Or.inl ⟨step, i, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨lev, hlev, rfl⟩)

theorem keyIndex_lt (e : KeyIndex) : e.val < 4294967296 :=
  e.isLt

/-- The children of a node on a key's path have indices below `2 ^ 32`. -/
theorem two_mul_div_add_one_lt (e : KeyIndex) (lev : ℕ) :
    2 * (e.val / 2 ^ (lev + 1)) + 1 < 4294967296 := by
  have h2 : 2 ≤ 2 ^ (lev + 1) :=
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (lev + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : e.val / 2 ^ (lev + 1) ≤ e.val / 2 := Nat.div_le_div_left h2 (by norm_num)
  have := keyIndex_lt e
  omega

theorem step_add_one_lt (step : ChainStep) : step.val + 1 < chainLength := by
  have := step.isLt
  have := chainLength_pred_lt
  omega

theorem slotOutPos_mem {l : Layer} {e : KeyIndex} {w : Encoding} {s : Slot}
    (hs : s ∈ layerSlots l e w) : slotOutPos s ∈ slotNeed s := by
  rcases mem_layerSlots hs with ⟨step, i, rfl⟩ | rfl | ⟨lev, -, rfl⟩
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- Values agreeing with the table on `slotNeed s` give the honest payload. -/
theorem slotPayload_eq (L : HonestTable) {l : Layer} {e : KeyIndex} {w : Encoding} {s : Slot}
    (hs : s ∈ layerSlots l e w) {f : ValPos → Digest} (hf : ∀ q ∈ slotNeed s, f q = valuePos L q) :
    slotPayload f s = L.payload s := by
  rcases mem_layerSlots hs with ⟨step, i, rfl⟩ | rfl | ⟨lev, hlev, rfl⟩
  · rw [slotPayload, hf _ (Finset.mem_insert_self _ _), valuePos_cpos,
      Nat.mod_eq_of_lt (Nat.lt_of_succ_lt (step_add_one_lt step))]
    rfl
  · show digestsPayload _ = digestsPayload _
    congr 1
    funext i
    rw [hf _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))),
      valuePos_cpos, Nat.mod_eq_of_lt chainLength_pred_lt]
    rfl
  · have h0 := hf _ (Finset.mem_insert_self _ _)
    have h1 := hf _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hi := two_mul_div_add_one_lt e lev
    rw [slotPayload, h0, h1, valuePos_tpos, valuePos_tpos, Nat.add_sub_cancel,
      Nat.mod_eq_of_lt (show lev < layerHeight + 1 by omega),
      Nat.mod_eq_of_lt (show 2 * (e.val / 2 ^ (lev + 1)) < 2 ^ 32 by norm_num; omega),
      Nat.mod_eq_of_lt (show 2 * (e.val / 2 ^ (lev + 1)) + 1 < 2 ^ 32 by norm_num; omega)]
    simp only [HonestTable.payload, Nat.add_sub_cancel]

/-- The value at a slot's output position is the digest of its honest input. -/
theorem valuePos_slotOutPos (L : HonestTable) {l : Layer} {e : KeyIndex} {w : Encoding} {s : Slot}
    (hs : s ∈ layerSlots l e w) :
    valuePos L (slotOutPos s) = L.digest (thInput L.param (slotFields s) (L.payload s)) := by
  rcases mem_layerSlots hs with ⟨step, i, rfl⟩ | rfl | ⟨lev, hlev, rfl⟩
  · rw [slotOutPos, valuePos_cpos, Nat.mod_eq_of_lt (step_add_one_lt step),
      HonestTable.chainValue_succ]
    rfl
  · rw [slotOutPos, valuePos_tpos, Nat.zero_mod,
      Nat.mod_eq_of_lt (show e.val < 2 ^ 32 from keyIndex_lt e), HonestTable.treeValue,
      leafKey_val]
    rfl
  · have he := keyIndex_lt e
    rw [slotOutPos, valuePos_tpos, Nat.mod_eq_of_lt (show lev + 1 < layerHeight + 1 by omega),
      Nat.mod_eq_of_lt (show e.val / 2 ^ (lev + 1) < 2 ^ 32 by
        norm_num; exact (Nat.div_le_self _ _).trans_lt he),
      HonestTable.treeValue_succ]
    simp only [HonestTable.payload, slotFields, Nat.add_sub_cancel]

/-- **The last-round correction vanishes at the table**: at `pubOf L` and the values of `L`, the
`h`-cell of every round of a layer signature's slot holds its `L.keys` value. -/
theorem roundH_snd (L : HonestTable) {l : Layer} {e : KeyIndex} {w : Encoding} {s : Slot}
    (hs : s ∈ layerSlots l e w) (j : ℕ) :
    (roundH (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j).2 =
      L.keys.1 (roundH (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j).1 := by
  set f := extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L)) with hf_def
  have hf : ∀ q ∈ slotNeed s, f q = valuePos L q := fun q hq ↦ by
    rw [hf_def, extendVals_restrictTo (inl_mem_inlSet.mpr hq)]
    rfl
  have hout : f (slotOutPos s) = trunc128 (spongeHash (spongePerm (pubOf L).keys (pubOf L).perm)
      (blocks (slotInput (pubOf L) s f))) := by
    rw [hf _ (slotOutPos_mem hs), valuePos_slotOutPos L hs, slotInput, slotPayload_eq L hs hf]
    exact (L.trunc128_spongeHash _).symm
  have hlen := blocks_slotInput_length (pubOf L) s f
  dsimp only [roundH]
  split_ifs with hj
  · rw [hout, spongeHash_lastRound _ _ (hlen.trans hj.symm), embed128_xor_self, add_zero]
    rfl
  · rfl

/-- The program ports the template game calls at the table `L` (in-table keys, as `signT` signs),
realized. -/
def progSet (L : HonestTable) : Set (HwProg X Z) :=
  {c | ∃ (l : Layer) (e : KeyIndex) (w : Encoding) (s : Slot), e.val < keyCount l ∧
    s ∈ layerSlots l e w ∧ ∃ p ∈ slotPorts (pubOf L) s, p.realize (valueAt L) = c}

open Classical in
/-- **The table's cells the game programs**: the cells of the honest paths of every slot a layer
signature makes public, with their values in `L.keys`. -/
noncomputable def tableHw (L : HonestTable) : Hw X Z :=
  (fun z ↦ if ∃ a, HwProg.programH z a ∈ progSet L then some (L.keys.1 z) else none,
   fun x ↦ if ∃ a, HwProg.programK x a ∈ progSet L then some (L.keys.2.1 x) else none,
   fun x ↦ if ∃ a, HwProg.programK' x a ∈ progSet L then some (L.keys.2.2 x) else none)

theorem tableHw_fst {L : HonestTable} {z : Z} {a : X} (h : HwProg.programH z a ∈ progSet L) :
    (tableHw L).1 z = some (L.keys.1 z) := by
  have h' : ∃ a, HwProg.programH z a ∈ progSet L := ⟨a, h⟩
  simp only [tableHw, h', ↓reduceIte]

theorem tableHw_snd_fst {L : HonestTable} {x : X} {a : Z} (h : HwProg.programK x a ∈ progSet L) :
    (tableHw L).2.1 x = some (L.keys.2.1 x) := by
  have h' : ∃ a, HwProg.programK x a ∈ progSet L := ⟨a, h⟩
  simp only [tableHw, h', ↓reduceIte]

theorem tableHw_snd_snd {L : HonestTable} {x : X} {a : Z} (h : HwProg.programK' x a ∈ progSet L) :
    (tableHw L).2.2 x = some (L.keys.2.2 x) := by
  have h' : ∃ a, HwProg.programK' x a ∈ progSet L := ⟨a, h⟩
  simp only [tableHw, h', ↓reduceIte]

/-- **The template game programs cells of the table with their table values.** -/
theorem progOf_tableHw (L : HonestTable) {c : HwProg X Z} (hc : c ∈ progSet L) :
    ProgOf (tableHw L) c := by
  have hc' := hc
  obtain ⟨l, e, w, s, -, hs, p, hp, hpc⟩ := hc
  simp only [slotPorts, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  obtain ⟨j, -, rfl | rfl | rfl⟩ := hp <;> subst hpc
  · exact tableHw_snd_fst hc'
  · exact tableHw_snd_snd hc'
  · exact (tableHw_fst hc').trans (congrArg some (roundH_snd L hs j).symm)

end table

/-! ## The realized game without reveals, and its read program -/

section programs

variable (M : Type) [Fintype M] [DecidableEq M]

/-- A program over `hwReadSpec` with fixed final register as one over `hwSpec`. -/
def liftReadQ {A B : QReg} {α : Type} (y : QComp (hwReadSpec X Z M) A B α) :
    QComp (hwSpec X Z M) A B α :=
  liftReadProg y

/-- The program calls of the template ports `ps` realized at `v`. -/
noncomputable def progPortsD (v : HPos → Digest) (B : QReg) :
    List (LazyProg X Z HPos XD) → QComp (hwSpec X Z M) B B Unit
  | [] => QuantumComp₂.pure ()
  | p :: ps => (progCall (p.realize v) B).bind fun _ ↦ progPortsD v B ps

/-- The program calls of the honest paths of the slots `ss`, realized at `v`. -/
noncomputable def progSlotsD (pub : Pub) (v : HPos → Digest) (B : QReg) :
    List Slot → QComp (hwSpec X Z M) B B Unit
  | [] => QuantumComp₂.pure ()
  | s :: ss => (progPortsD M v B (slotPorts pub s)).bind fun _ ↦ progSlotsD pub v B ss

/-- A layer signature with randomizer `ρ` and codeword `x` read from the values `v` revealed on
`layerNeed l e x`, with those values. -/
def layerSig (v : HPos → Digest) (l : Layer) (e : KeyIndex) (ρ : Randomizer) (x : Encoding) :
    Option (LayerSignature × (ValPos → Digest)) :=
  some (⟨ρ, fun i ↦ extendVals (restrictTo (inlSet (layerNeed l e x)) v) (cpos l e i (x i).val),
    fun level ↦ extendVals (restrictTo (inlSet (layerNeed l e x)) v) (siblingPos l e level)⟩,
    extendVals (restrictTo (inlSet (layerNeed l e x)) v))

/-- **A layer signature, realized with its reveals dropped**: the randomizer search through read
ports (keeping the memory) from the base `v (.inr lab)`, then the program calls of the slots the
signature makes public. -/
noncomputable def signLayerD (pub : Pub) (v : HPos → Digest) (B : QReg) (lab : RLabel) :
    QComp (hwSpec X Z M) B B (Option (LayerSignature × (ValPos → Digest))) :=
  (liftReadQ M (grindR M (keepUpd M) pub B lab.layer lab.key lab.msg (v (.inr lab))
    randomizerAttemptLimit 0)).bind fun g ↦
    match g with
    | none => QuantumComp₂.pure none
    | some (ρ, x) => (progSlotsD M pub v B (layerSlots lab.layer lab.key x)).bind fun _ ↦
        QuantumComp₂.pure (layerSig v lab.layer lab.key ρ x)

/-- **A layer signature as reads**: the randomizer search through read ports from the base
`v (.inr lab)`; the opened chain values and the path are the values `v`. -/
noncomputable def signLayerR (pub : Pub) (v : HPos → Digest) (B : QReg) (lab : RLabel) :
    QComp (hwReadSpec X Z M) B B (Option (LayerSignature × (ValPos → Digest))) :=
  (grindR M (keepUpd M) pub B lab.layer lab.key lab.msg (v (.inr lab)) randomizerAttemptLimit
    0).bind fun g ↦
    match g with
    | none => QuantumComp₂.pure none
    | some (ρ, x) => QuantumComp₂.pure (layerSig v lab.layer lab.key ρ x)

/-- Two layer signatures as `signT` combines them. -/
noncomputable def signWith {spec : QuantumOracleSpec.{0, 0}} (B : QReg)
    (layer : RLabel → QComp spec B B (Option (LayerSignature × (ValPos → Digest))))
    (r : SigningRequest) : QComp spec B B (Option Signature) :=
  (layer (botLabel r)).bind fun b ↦
    match b with
    | none => QuantumComp₂.pure none
    | some (bottom, f) =>
      (layer (topLabel r (f (botRootPos r)))).bind fun t ↦
        match t with
        | none => QuantumComp₂.pure none
        | some (top, _) => QuantumComp₂.pure
            (some ⟨r.leafIndex, fun l ↦ if l = bottomLayer then bottom else top⟩)

/-- The answer to a signing request with the adversary's register held, from a signer. -/
noncomputable def signAtWith {spec : QuantumOracleSpec.{0, 0}}
    (sgn : ∀ B : QReg, SigningRequest → QComp spec B B (Option Signature)) (r : SigningRequest)
    (E : QReg) {A : QReg} (ℓ : A ≃ (advSpec (X × Z)).In (.sign r) × E) :
    QComp spec A (QReg.of ((advSpec (X × Z)).Out (.sign r) × E)) (Option Signature) :=
  (QComp.act (spec := spec) (B := QReg.of ((advSpec (X × Z)).Out (.sign r) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ sgn _ r

/-- The signing answer of the realized game with its reveals dropped. -/
noncomputable def signAtD (pub : Pub) (v : HPos → Digest) (r : SigningRequest) (E : QReg)
    {A : QReg} (ℓ : A ≃ (advSpec (X × Z)).In (.sign r) × E) :
    QComp (hwSpec X Z M) A (QReg.of ((advSpec (X × Z)).Out (.sign r) × E)) (Option Signature) :=
  signAtWith (fun B ↦ signWith B (signLayerD M pub v B)) r E ℓ

/-- The signing answer as reads, the values from `v`. -/
noncomputable def signAtR (pub : Pub) (v : HPos → Digest) (r : SigningRequest) (E : QReg)
    {A : QReg} (ℓ : A ≃ (advSpec (X × Z)).In (.sign r) × E) :
    QComp (hwReadSpec X Z M) A (QReg.of ((advSpec (X × Z)).Out (.sign r) × E))
      (Option Signature) :=
  signAtWith (fun B ↦ signWith B (signLayerR M pub v B)) r E ℓ

/-- **The challenger of the realized game with its reveals dropped**: as `challengeT`, with the
reads lifted to `hwSpec` and a signing request answered by `signAtD`. -/
noncomputable def challengeD (pub : Pub) (v : HPos → Digest) :
    IPFunctor.CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z)))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec X Z M))
  | A, .prim o => liftReadProg ((simulate LocalSig.Interp.instruments pub.perm
      (challenge keccakStateEquiv (noKey pub) A (.prim o))).liftOrdinary
        (t := hwReadCmdSpec X Z M))
  | A, .query (.perm p) E ℓ => liftReadProg ((simulate LocalSig.Interp.instruments pub.perm
      (challenge keccakStateEquiv (noKey pub) A (.query (.perm p) E ℓ))).liftOrdinary
        (t := hwReadCmdSpec X Z M))
  | _, .query (.sign r) E ℓ =>
      QuantumComp.bind (signAtD M pub v r E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- **The challenger with honest reads, from a signer**: as `challengeReads`, a signing request
answered by `sgn`. -/
noncomputable def challengeWith (π : Equiv.Perm (X × Z)) (sk : SecretKey)
    (sgn : ∀ (r : SigningRequest) (E : QReg) {A : QReg},
      (A ≃ (advSpec (X × Z)).In (.sign r) × E) →
        QComp (hwReadSpec X Z M) A (QReg.of ((advSpec (X × Z)).Out (.sign r) × E))
          (Option Signature)) :
    IPFunctor.CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z)))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwReadSpec X Z M))
  | A, .prim o => (simulate LocalSig.Interp.instruments π
      (challenge keccakStateEquiv sk A (.prim o))).liftOrdinary
  | A, .query (.perm p) E ℓ => (simulate LocalSig.Interp.instruments π
      (challenge keccakStateEquiv sk A (.query (.perm p) E ℓ))).liftOrdinary
  | _, .query (.sign r) E ℓ =>
      QuantumComp.bind (sgn r E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The public key the template game reveals: the root value of `v` and the parameter. -/
def pkOf (pub : Pub) (v : HPos → Digest) : PublicKey :=
  ⟨extendVals (restrictTo {.inl rootPos} v) rootPos, pub.param⟩

/-- **The realized template game with its reveals dropped** (over `hwSpec`): the adversary on
`pkOf pub v` against `challengeD`, verification through read ports, the winning condition. -/
noncomputable def gameD (pub : Pub) (v : HPos → Digest) (A : Adversary (X × Z)) :
    QComp (hwSpec X Z M) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind
    (IPFunctor.IFreeM.substitute (challengeD M pub v) (withSignLog (A (pkOf pub v))))
    fun run ↦ (liftReadQ M ((readsProgram M pub.perm _ (schemeWithHashFromSeed.verify
      (pkOf pub v) run.1)).map Prod.fst)).bind fun verified ↦
        QuantumComp₂.pure (sufCmaScheme.winningCondition run.2 run.1 && verified)

/-- **The game's reads from a signer** (`gameReads` has the signer `signReads`). -/
noncomputable def gameReadsWith (π : Equiv.Perm (X × Z)) (sk : SecretKey)
    (sgn : ∀ (r : SigningRequest) (E : QReg) {A : QReg},
      (A ≃ (advSpec (X × Z)).In (.sign r) × E) →
        QComp (hwReadSpec X Z M) A (QReg.of ((advSpec (X × Z)).Out (.sign r) × E))
          (Option Signature))
    (pk : PublicKey) (A : Adversary (X × Z)) :
    QComp (hwReadSpec X Z M) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (IPFunctor.IFreeM.substitute (challengeWith M π sk sgn) (withSignLog (A pk)))
    fun run ↦
    ((readsProgram M π _ (schemeWithHashFromSeed.verify pk run.1)).map Prod.fst).bind
      fun verified ↦ QuantumComp₂.pure (sufCmaScheme.winningCondition run.2 run.1 && verified)

/-- **The game's reads with the grind-only signer** (`gameReadsT`): `gameReadsWith` with the
signer `signAtR`, which reads only the randomizer trials and takes chain values and paths from
`v`. -/
noncomputable def gameReadsT (pub : Pub) (v : HPos → Digest) (A : Adversary (X × Z)) :
    QComp (hwReadSpec X Z M) (QReg.of Unit) (QReg.of Unit) Bool :=
  gameReadsWith M pub.perm (noKey pub) (signAtR M pub v) (pkOf pub v) A

end programs

/-! ## Dropping the program calls -/

section drops

variable {M : Type} (W : Hw X Z)

theorem dropsTo_progPortsD (v : HPos → Digest) (B : QReg) {C : QReg} {α : Type}
    {x : QComp (hwSpec X Z M) B C α} {y : QComp (hwReadSpec X Z M) B C α} (hx : DropsTo W x y) :
    ∀ ps : List (LazyProg X Z HPos XD), (∀ p ∈ ps, ProgOf W (p.realize v)) →
      DropsTo W ((progPortsD M v B ps).bind fun _ ↦ x) y
  | [], _ => hx
  | p :: ps, h => by
    rw [progPortsD, QuantumComp₂.bind_assoc]
    exact DropsTo.progCall_bind _ (h p List.mem_cons_self)
      (dropsTo_progPortsD v B hx ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

theorem dropsTo_progSlotsD (pub : Pub) (v : HPos → Digest) (B : QReg) {C : QReg} {α : Type}
    {x : QComp (hwSpec X Z M) B C α} {y : QComp (hwReadSpec X Z M) B C α} (hx : DropsTo W x y) :
    ∀ ss : List Slot, (∀ s ∈ ss, ∀ p ∈ slotPorts pub s, ProgOf W (p.realize v)) →
      DropsTo W ((progSlotsD M pub v B ss).bind fun _ ↦ x) y
  | [], _ => hx
  | s :: ss, h => by
    rw [progSlotsD, QuantumComp₂.bind_assoc]
    exact dropsTo_progPortsD W v B
      (dropsTo_progSlotsD pub v B hx ss fun t ht ↦ h t (List.mem_cons_of_mem _ ht)) _
      (h s List.mem_cons_self)

/-- Every program port the game calls at `pub`, `v` (in-table keys) programs a cell of `W` with
its `W` value. -/
def ProgsOf (pub : Pub) (v : HPos → Digest) : Prop :=
  ∀ (l : Layer) (e : KeyIndex) (x : Encoding), e.val < keyCount l → ∀ s ∈ layerSlots l e x,
    ∀ p ∈ slotPorts pub s, ProgOf W (p.realize v)

variable {W}

theorem dropsTo_signLayerD {pub : Pub} {v : HPos → Digest} (h : ProgsOf W pub v) (B : QReg)
    (lab : RLabel) (he : lab.key.val < keyCount lab.layer) :
    DropsTo W (signLayerD M pub v B lab) (signLayerR M pub v B lab) := by
  refine DropsTo.bind₂ (dropsTo_liftReadProg W _) fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · exact DropsTo.pure _
  · exact dropsTo_progSlotsD W pub v B (DropsTo.pure _) _ (h lab.layer lab.key x he)

theorem dropsTo_signWith (B : QReg)
    {layerD : RLabel → QComp (hwSpec X Z M) B B (Option (LayerSignature × (ValPos → Digest)))}
    {layerR : RLabel → QComp (hwReadSpec X Z M) B B (Option (LayerSignature × (ValPos → Digest)))}
    (h : ∀ lab, lab.key.val < keyCount lab.layer → DropsTo W (layerD lab) (layerR lab))
    (r : SigningRequest) : DropsTo W (signWith B layerD r) (signWith B layerR r) := by
  refine DropsTo.bind₂ (h (botLabel r) (keyIndexOnLayer_lt r.leafIndex bottomLayer)) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · exact DropsTo.pure _
  · refine DropsTo.bind₂ (h (topLabel r _) (keyIndexOnLayer_lt r.leafIndex topLayer)) fun t ↦ ?_
    rcases t with _ | ⟨top, _⟩
    · exact DropsTo.pure _
    · exact DropsTo.pure _

theorem dropsTo_signAtD {pub : Pub} {v : HPos → Digest} (h : ProgsOf W pub v)
    (r : SigningRequest) (E : QReg) {A : QReg} (ℓ : A ≃ (advSpec (X × Z)).In (.sign r) × E) :
    DropsTo W (signAtD M pub v r E ℓ) (signAtR M pub v r E ℓ) := by
  rw [signAtD, signAtR, signAtWith, signAtWith, QComp.act_bind, QComp.act_bind]
  exact DropsTo.prim _ fun _ ↦ dropsTo_signWith _ (dropsTo_signLayerD h _) r

theorem dropsTo_challengeD {pub : Pub} {v : HPos → Digest} (h : ProgsOf W pub v) (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z))).A A) :
    DropsTo W (challengeD M pub v A c)
      (challengeWith M pub.perm (noKey pub) (signAtR M pub v) A c) := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact dropsTo_liftReadProg W _
  · exact dropsTo_liftReadProg W _
  · exact DropsTo.bind (dropsTo_signAtD h r E ℓ) fun _ _ ↦ DropsTo.pure _

/-- **The realized game with its reveals dropped is its read program with program calls
inserted**, when every program call hardwires a cell of `W` with its `W` value. -/
theorem dropsTo_gameD {pub : Pub} {v : HPos → Digest} (h : ProgsOf W pub v)
    (A : Adversary (X × Z)) : DropsTo W (gameD M pub v A) (gameReadsT M pub v A) :=
  DropsTo.bind₂ (dropsTo_substitute W (dropsTo_challengeD h) _) fun _ ↦
    DropsTo.bind₂ (dropsTo_liftReadProg W _) fun _ ↦ DropsTo.pure _

/-- A cell programmed with its value in `W` keeps it in any `W'` extending `W`. -/
theorem progOf_mono {W' : Hw X Z} (hW : HwLe W W') {c : HwProg X Z} (hc : ProgOf W c) :
    ProgOf W' c := by
  cases c with
  | programH z a =>
    have hc' : W.1 z = some a := hc
    show W'.1 z = some a
    rcases hW.1 z with h0 | h0
    · rw [hc'] at h0
      exact absurd h0 (Option.some_ne_none a)
    · rw [← h0, hc']
  | programK x a =>
    have hc' : W.2.1 x = some a := hc
    show W'.2.1 x = some a
    rcases hW.2.1 x with h0 | h0
    · rw [hc'] at h0
      exact absurd h0 (Option.some_ne_none a)
    · rw [← h0, hc']
  | programK' x a =>
    have hc' : W.2.2 x = some a := hc
    show W'.2.2 x = some a
    rcases hW.2.2 x with h0 | h0
    · rw [hc'] at h0
      exact absurd h0 (Option.some_ne_none a)
    · rw [← h0, hc']

theorem ProgsOf.mono {W' : Hw X Z} (hW : HwLe W W') {pub : Pub} {v : HPos → Digest}
    (h : ProgsOf W pub v) : ProgsOf W' pub v :=
  fun l e x he s hs p hp ↦ progOf_mono hW (h l e x he s hs p hp)

/-- **At the table, the game programs cells of `tableHw L` with their values.** -/
theorem progsOf_tableHw (L : HonestTable) : ProgsOf (tableHw L) (pubOf L) (valueAt L) :=
  fun l e x he s hs p hp ↦ progOf_tableHw L ⟨l, e, x, s, he, hs, p, hp, rfl⟩

end drops

/-! ## The two read programs differ only in the signer -/

section signer

variable (M : Type)

/-- `challengeReads` is `challengeWith` with the signer `signReads`. -/
theorem challengeReads_eq (π : Equiv.Perm (X × Z)) (sk : SecretKey) :
    challengeReads M π sk = challengeWith M π sk (fun r E _ ℓ ↦ signReads M π sk r E ℓ) := by
  funext A c
  rcases c with o | ⟨p | r, E, ℓ⟩ <;> rfl

/-- The challenger's local operations and permutation calls do not read the secret key. -/
theorem challengeWith_sk (π : Equiv.Perm (X × Z)) (sk sk' : SecretKey)
    (sgn : ∀ (r : SigningRequest) (E : QReg) {A : QReg},
      (A ≃ (advSpec (X × Z)).In (.sign r) × E) →
        QComp (hwReadSpec X Z M) A (QReg.of ((advSpec (X × Z)).Out (.sign r) × E))
          (Option Signature)) :
    challengeWith M π sk sgn = challengeWith M π sk' sgn := by
  funext A c
  rcases c with o | ⟨p | r, E, ℓ⟩ <;> rfl

/-- **`gameReads` from the honest key generation of `L`** is `gameReadsWith` at `L`'s keys with
the signer `signReads` (the read program of `schemeWithHashFromSeed.sign L.secretKey`). -/
theorem gameReads_honest (L : HonestTable) (A : Adversary (X × Z)) :
    gameReads M L.perm A (honestEval L.keys L.perm (schemeWithHashFromSeed.keygen L.masterSeed)) =
      gameReadsWith M L.perm L.secretKey (fun r E _ ℓ ↦ signReads M L.perm L.secretKey r E ℓ)
        L.publicKey A := by
  rw [gameReads, challengedReads, L.fst_honestEval_keygen, challengeReads_eq]
  rfl

/-- The public key the template game reveals at `L` is `L`'s. -/
theorem pkOf_pubOf (L : HonestTable) : pkOf (pubOf L) (valueAt L) = L.publicKey := by
  rw [pkOf, extendVals_restrictTo (Finset.mem_singleton_self _)]
  simp only [valueAt_inl, HonestTable.publicKey, pubOf, rootPos, tpos, valuePos]
  rfl

/-- **`gameReadsT` at `L`** is `gameReadsWith` at `L`'s keys with the grind-only signer
`signAtR`: the two read programs differ only in the answer to a signing request. -/
theorem gameReadsT_pubOf (L : HonestTable) (A : Adversary (X × Z)) :
    gameReadsT M (pubOf L) (valueAt L) A =
      gameReadsWith M L.perm L.secretKey (signAtR M (pubOf L) (valueAt L)) L.publicKey A := by
  rw [gameReadsT, pkOf_pubOf, gameReadsWith, gameReadsWith,
    challengeWith_sk M _ (noKey (pubOf L)) L.secretKey]
  rfl

end signer

/-! ## Dropping the record ports of the realized game -/

section records

variable {M : Type} (v : HPos → Digest)

theorem dropRec_revealThen {B C : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B C α)
    {y : QComp (hwSpec X Z Unit) B C α}
    (h : ∀ r, DropRec HPos (realizeT v (k (restrictTo T v, r))) y) :
    DropRec HPos (realizeT v (revealThen goodAll T k)) y :=
  DropRec.record T B _ _ (fun a ↦ Equiv.apply_symm_apply _ a) h

theorem dropRec_progThen {B C : QReg} {α : Type} (p : LazyProg X Z HPos XD)
    {k : QComp (XSpec M) B C α} {y : QComp (hwSpec X Z Unit) B C α}
    (h : DropRec HPos (realizeT v k) y) :
    DropRec HPos (realizeT v (progThen p trivial k))
      ((progCall (p.realize v) B).bind fun _ ↦ y) :=
  DropRec.prog (p.realize v) B (Equiv.uniqueProd B Unit).symm
    (k := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ realizeT v k)
    (k' := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ y)
    fun _ ↦ DropRec.prim _ fun _ ↦ h

theorem dropRec_progPorts (B : QReg) :
    ∀ ps : List (LazyProg X Z HPos XD),
      DropRec HPos (realizeT v (progPorts M B ps)) (progPortsD Unit v B ps)
  | [] => DropRec.pure _
  | p :: ps => dropRec_progThen v p (dropRec_progPorts B ps)

theorem dropRec_progSlots (pub : Pub) (B : QReg) :
    ∀ ss : List Slot,
      DropRec HPos (realizeT v (progSlots M pub B ss)) (progSlotsD Unit pub v B ss)
  | [] => DropRec.pure _
  | s :: ss => by
    rw [progSlots, progSlotsD, realizeT_bind₂]
    exact DropRec.bind₂ (dropRec_progPorts v B _) fun _ ↦ dropRec_progSlots pub B ss

end records

/-! ## The grind-only signer against the honest functions -/

section honest

variable {M : Type} [Fintype M] [DecidableEq M] (L : HonestTable) {m : M} {B : QReg}

theorem readsTo_hashTrial (input : HashInput) :
    ReadsTo L.keys (hwEmpty X Z) m (hashTrial M (fun _ _ ↦ keepMem) L.perm B input)
      (L.hash input) := by
  have h := ((readsToS_readsImpl (t := L.keys) (W := hwEmpty X Z) (m := m) (B := B) (M := M)
    L.perm input) []).map Prod.fst
  rw [overwrite_hwEmpty, readHash_eq_traceImpl] at h
  exact h

/-- **The randomizer search through read ports returns the table's selection.** -/
theorem readsTo_grindR (l : Layer) (e : KeyIndex) (message : HashInput) (base : Randomizer) :
    ∀ n trial, ReadsTo L.keys (hwEmpty X Z) m
      (grindR M (keepUpd M) (pubOf L) B l e message base n trial)
      (L.selectFrom l e message base n trial)
  | 0, _ => readsTo_pure _
  | n + 1, trial => by
    rw [grindR]
    refine (readsTo_hashTrial L _).bind ?_
    show ReadsTo _ _ _ (match Codeword.decode (truncateHash (L.hash (thInput L.param
        (hashDomainFields (.message l e)) (message ++ littleEndianBytes 16
          (base + BitVec.ofNat digestBits trial))))) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindR M (keepUpd M) (pubOf L) B l e message base n (trial + 1))
      (match Codeword.decode (truncateHash (L.hash (thInput L.param
        (hashDomainFields (.message l e)) (message ++ littleEndianBytes 16
          (base + BitVec.ofNat digestBits trial))))) with
      | some x => some (base + BitVec.ofNat digestBits trial, x)
      | none => L.selectFrom l e message base n (trial + 1))
    cases Codeword.decode _ with
    | none => exact readsTo_grindR l e message base n (trial + 1)
    | some x => exact readsTo_pure _

theorem cpos_mem_layerNeed (l : Layer) (e : KeyIndex) (x : Encoding) (i : ChainIndex) :
    cpos l e i (x i).val ∈ layerNeed l e x :=
  Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image_of_mem (fun i ↦ cpos l e i (x i).val) (Finset.mem_univ i)))

theorem siblingPos_mem_layerNeed (l : Layer) (e : KeyIndex) (x : Encoding)
    (level : Fin layerHeight) : siblingPos l e level ∈ layerNeed l e x :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem (siblingPos l e) (Finset.mem_univ level))

/-- **A layer signature from the revealed values is the table's.** -/
theorem layerSig_valueAt (l : Layer) (e : KeyIndex) (ρ : Randomizer) (x : Encoding) :
    layerSig (valueAt L) l e ρ x =
      some (⟨ρ, fun i ↦ L.chainValue l e i (x i).val, L.authPath l e⟩,
        extendVals (restrictTo (inlSet (layerNeed l e x)) (valueAt L))) := by
  have hc : ∀ i, extendVals (restrictTo (inlSet (layerNeed l e x)) (valueAt L))
      (cpos l e i (x i).val) = L.chainValue l e i (x i).val := fun i ↦ by
    rw [extendVals_restrictTo (inl_mem_inlSet.mpr (cpos_mem_layerNeed l e x i)), valueAt_inl,
      valuePos_cpos, Nat.mod_eq_of_lt (x i).isLt]
  have hs : ∀ level, extendVals (restrictTo (inlSet (layerNeed l e x)) (valueAt L))
      (siblingPos l e level) = L.authPath l e level := fun level ↦ by
    have hlt : Nat.xor (e.val / 2 ^ level.val) 1 < 2 ^ 32 :=
      Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt (keyIndex_lt e)) (by norm_num)
    rw [extendVals_restrictTo (inl_mem_inlSet.mpr (siblingPos_mem_layerNeed l e x level)),
      valueAt_inl, siblingPos, valuePos_tpos,
      Nat.mod_eq_of_lt (show level.val < layerHeight + 1 by have := level.isLt; omega),
      Nat.mod_eq_of_lt hlt]
    rfl
  simp only [layerSig, hc, hs]

/-- The value a layer signature of the grind-only signer returns at `L`. -/
def layerValue (lab : RLabel) : Option (LayerSignature × (ValPos → Digest)) :=
  match L.select lab.layer lab.key lab.msg with
  | none => none
  | some (ρ, x) => layerSig (valueAt L) lab.layer lab.key ρ x

theorem readsTo_signLayerR (lab : RLabel) :
    ReadsTo L.keys (hwEmpty X Z) m (signLayerR M (pubOf L) (valueAt L) B lab)
      (layerValue L lab) := by
  rw [signLayerR]
  refine (readsTo_grindR L lab.layer lab.key lab.msg _ _ _).bind ?_
  show ReadsTo _ _ _ (match L.select lab.layer lab.key lab.msg with
    | none => QuantumComp₂.pure none
    | some (ρ, x) => QuantumComp₂.pure (layerSig (valueAt L) lab.layer lab.key ρ x))
      (layerValue L lab)
  rw [layerValue]
  rcases L.select lab.layer lab.key lab.msg with _ | ⟨ρ, x⟩
  · exact readsTo_pure _
  · exact readsTo_pure _

/-- The root of the bottom tree of a leaf index is revealed by its bottom layer signature. -/
theorem bottomRoot_mem_layerNeed (idx : LeafIndex) (x : Encoding) :
    tpos bottomLayer layerHeight (keyIndexOnLayer idx topLayer).val ∈
      layerNeed bottomLayer (keyIndexOnLayer idx bottomLayer) x := by
  have hs : Slot.node bottomLayer (15 + 1)
      ((keyIndexOnLayer idx bottomLayer).val / 2 ^ (15 + 1)) ∈
        layerSlots bottomLayer (keyIndexOnLayer idx bottomLayer) x := by
    simp only [layerSlots, List.mem_append, List.mem_cons, List.mem_map, List.mem_range]
    exact Or.inr (Or.inr ⟨15, by decide, rfl⟩)
  have hp : tpos bottomLayer layerHeight (keyIndexOnLayer idx topLayer).val =
      tpos bottomLayer (15 + 1) ((keyIndexOnLayer idx bottomLayer).val / 2 ^ (15 + 1)) := by
    simp [keyIndexOnLayer, bottomLayer, topLayer, layerHeight]
  rw [hp]
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (slotNeed_subset_needUnion hs ?_))
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem valuePos_bottomRoot (idx : LeafIndex) :
    valuePos L (tpos bottomLayer layerHeight (keyIndexOnLayer idx topLayer).val) =
      L.bottomRoot idx := by
  rw [valuePos_tpos, Nat.mod_eq_of_lt (Nat.lt_succ_self _), Nat.mod_eq_of_lt
    (show (keyIndexOnLayer idx topLayer).val < 2 ^ 32 from keyIndex_lt _)]
  rfl

/-- **The grind-only signer returns the table's signature** against the honest functions. -/
theorem readsTo_signWithR (r : SigningRequest) :
    ReadsTo L.keys (hwEmpty X Z) m (signWith B (signLayerR M (pubOf L) (valueAt L) B) r)
      (L.signature r) := by
  rw [signWith]
  refine (readsTo_signLayerR L _).bind ?_
  rw [layerValue]
  dsimp only [botLabel, RLabel.layer, RLabel.key, RLabel.msg]
  rcases hb : L.select bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)
    (littleEndianBytes 32 r.message) with _ | ⟨ρ, x⟩
  · have h : L.signature r = none := by
      simp only [HonestTable.signature, HonestTable.layerSignature, hb, Option.map_none,
        Option.bind_none]
    rw [h]
    exact readsTo_pure _
  · dsimp only
    rw [layerSig_valueAt]
    dsimp only [botRootPos]
    rw [extendVals_restrictTo (inl_mem_inlSet.mpr (bottomRoot_mem_layerNeed r.leafIndex x)),
      valueAt_inl, valuePos_bottomRoot]
    refine (readsTo_signLayerR L _).bind ?_
    rw [layerValue]
    dsimp only [topLabel, RLabel.layer, RLabel.key, RLabel.msg]
    rcases ht : L.select topLayer (keyIndexOnLayer r.leafIndex topLayer)
      (littleEndianBytes 16 (L.bottomRoot r.leafIndex)) with _ | ⟨ρ', x'⟩
    · have h : L.signature r = none := by
        simp only [HonestTable.signature, HonestTable.layerSignature, hb, ht, Option.map_none,
          Option.map_some, Option.bind_some]
      rw [h]
      exact readsTo_pure _
    · dsimp only
      rw [layerSig_valueAt]
      have h : L.signature r = some ⟨r.leafIndex, fun l ↦ if l = bottomLayer then
          ⟨ρ, fun i ↦
            L.chainValue bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) i (x i).val,
            L.authPath bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)⟩ else
          ⟨ρ', fun i ↦ L.chainValue topLayer (keyIndexOnLayer r.leafIndex topLayer) i (x' i).val,
            L.authPath topLayer (keyIndexOnLayer r.leafIndex topLayer)⟩⟩ := by
        simp only [HonestTable.signature, HonestTable.layerSignature, hb, ht, Option.map_some,
          Option.bind_some]
      rw [h]
      exact readsTo_pure _

variable (m)

theorem intertwines_classicalOn_readsTo_empty {B : QReg} {α : Type}
    {x₁ : QComp (qrpmSpec (X × Z)) B B α} {x₂ : QComp (hwReadSpec X Z M) B B α} {v : α}
    (h₁ : ClassicalOn (permutationRuntime (spongePerm L.keys L.perm)) x₁ (pure v) LinearMap.id)
    (h₂ : ReadsTo L.keys (hwEmpty X Z) m x₂ v) :
    DSubInstrument.Intertwines ((hwAt (hwEmpty X Z) m).amplifyLeft B)
      (fun _ ↦ (hwAt (hwEmpty X Z) m).amplifyLeft B)
      ((permutationRuntime (spongePerm L.keys L.perm)).run₂ .instruments x₁)
      ((spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m).run₂ .instruments x₂) := by
  have h := intertwines_of_classicalOn_readsTo L.keys (hwEmpty X Z) m L.perm
    (by rw [overwrite_hwEmpty]; exact h₁) h₂
  rw [overwrite_hwEmpty] at h
  exact h

/-- **The challenger with the grind-only signer intertwines with the challenger** against the
honest functions of `L`. -/
theorem intertwines_challengeR (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z))).A A) :
    DSubInstrument.Intertwines ((hwAt (hwEmpty X Z) m).amplifyLeft A)
      (fun p : Σ u, {b : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z))).B
        A c // (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z))).src A c b =
          u} ↦ (hwAt (hwEmpty X Z) m).amplifyLeft p.1)
      ((permutationRuntime (spongePerm L.keys L.perm)).run .instruments
        (challenge keccakStateEquiv L.secretKey A c))
      ((spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m).run .instruments
        (challengeWith M L.perm L.secretKey (signAtR M (pubOf L) (valueAt L)) A c)) := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · have h := intertwines_simulate L.perm L.keys (hwEmpty X Z) m
      (challenge keccakStateEquiv L.secretKey A (.prim o))
    rw [overwrite_hwEmpty] at h
    exact h
  · have h := intertwines_simulate L.perm L.keys (hwEmpty X Z) m
      (challenge keccakStateEquiv L.secretKey A (.query (.perm p) E ℓ))
    rw [overwrite_hwEmpty] at h
    exact h
  · change DSubInstrument.Intertwines _ _
      ((permutationRuntime (spongePerm L.keys L.perm)).run .instruments
        (QuantumComp.bind (signTree keccakStateEquiv L.secretKey r E ℓ) _))
      ((spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m).run .instruments
        (QuantumComp.bind (signAtR M (pubOf L) (valueAt L) r E ℓ) _))
    refine intertwines_run_bind (R₁ := permutationRuntime (spongePerm L.keys L.perm))
      (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m) (V := hwAt (hwEmpty X Z) m)
      (intertwines_run_of_run₂ (R₁ := permutationRuntime (spongePerm L.keys L.perm))
        (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m) (V := hwAt (hwEmpty X Z) m) ?_)
      fun p ↦ ?_
    · rw [signTree, signAtR, signAtWith]
      refine intertwines_run₂_act_bind (R₁ := permutationRuntime (spongePerm L.keys L.perm))
        (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m) (V := hwAt (hwEmpty X Z) m)
        (A := A) (B := QReg.of ((advSpec (X × Z)).Out (.sign r) × E)) _ fun _ ↦ ?_
      exact intertwines_classicalOn_readsTo_empty L m
        ((classicalOn_toQuantumAt_permImpl L.keys L.perm _ _).congr
          (L.simulateQ_sign_eq _ (fun _ ↦ rfl) r) rfl) (readsTo_signWithR L r)
    · exact intertwines_run_pure (R₁ := permutationRuntime (spongePerm L.keys L.perm))
        (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m) (V := hwAt (hwEmpty X Z) m) _

/-- **The game and its grind-only reads intertwine** against the honest functions of `L`. -/
theorem intertwines_game_gameReadsT (A : Adversary (X × Z)) :
    DSubInstrument.Intertwines ((hwAt (hwEmpty X Z) m).amplifyLeft (QReg.of Unit))
      (fun _ ↦ (hwAt (hwEmpty X Z) m).amplifyLeft (QReg.of Unit))
      ((permutationRuntime (spongePerm L.keys L.perm)).run₂ .instruments
        (game keccakStateEquiv L.masterSeed A))
      ((spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m).run₂ .instruments
        (gameReadsT M (pubOf L) (valueAt L) A)) := by
  rw [gameReadsT_pubOf, game, run₂_bind_of_classicalOn_pure
    ((classicalOn_toQuantumAt_permImpl L.keys L.perm _ _).congr
      (simulateQ_generateKeys L.keys L.perm _ (fun _ ↦ rfl) L.masterSeed) rfl),
    L.fst_honestEval_keygen]
  dsimp only
  refine intertwines_run₂_bind (R₁ := permutationRuntime (spongePerm L.keys L.perm))
    (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m) (V := hwAt (hwEmpty X Z) m)
    (intertwines_run₂_of_run (intertwines_substitute (spec₀ := advSpec (X × Z))
      (R₁ := permutationRuntime (spongePerm L.keys L.perm))
      (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m) (V := hwAt (hwEmpty X Z) m)
      (fun A c ↦ intertwines_challengeR L m A c) _))
    fun run ↦ ?_
  refine intertwines_run₂_bind (R₁ := permutationRuntime (spongePerm L.keys L.perm))
    (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m) (V := hwAt (hwEmpty X Z) m)
    (intertwines_classicalOn_readsTo_empty L m ?_
      ((readsTo_readsProgram_hwEmpty L.perm (schemeWithHashFromSeed.verify _ run.1)).map
        Prod.fst))
    fun _ ↦ intertwines_run₂_pure _
  exact (classicalOn_toQuantumAt_permImpl L.keys L.perm _ _).congr
    (simulateQ_verify L.keys L.perm _ (fun _ ↦ rfl) _ run.1) rfl

/-- **G1 → G2 with the grind-only signer**: against `φ = spongePerm L.keys L.perm`, the game at
`L`'s master seed has the law of `gameReadsT` at `pubOf L`, `valueAt L` against the honest
functions `L.keys` read through read ports. -/
theorem evalDistMap_game_eq_gameReadsT (A : Adversary (X × Z)) (ρ : SubState (QReg.of Unit))
    {γ : Type*} [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (permutationRuntime (spongePerm L.keys L.perm)).evalDistMap .instruments
        (game keccakStateEquiv L.masterSeed A) ρ f =
      (spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m).evalDistMap .instruments
        (gameReadsT M (pubOf L) (valueAt L) A) ρ f :=
  evalDistMap_eq_of_intertwines (R₁ := permutationRuntime (spongePerm L.keys L.perm))
    (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m) (K := hwCol (hwEmpty X Z) m)
    (conjTranspose_hwCol_mul_self _ m) (hwAt_basis _ m)
    (intertwines_run_of_run₂ (intertwines_game_gameReadsT L m A)) ρ f

/-- **The two read programs have the same law against the honest functions**: `gameReads` after
the honest key generation of `L` and `gameReadsT` at `L` (G2 for both signers). -/
theorem evalDistMap_gameReads_eq_gameReadsT (A : Adversary (X × Z)) (ρ : SubState (QReg.of Unit))
    {γ : Type*} [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m).evalDistMap .instruments
        (gameReads M L.perm A
          (honestEval L.keys L.perm (schemeWithHashFromSeed.keygen L.masterSeed))) ρ f =
      (spongeFnReadRuntime X Z L.keys (hwEmpty X Z) m).evalDistMap .instruments
        (gameReadsT M (pubOf L) (valueAt L) A) ρ f := by
  have h := evalDistMap_game_eq_reads L.keys (hwEmpty X Z) m L.perm L.masterSeed A ρ f
  rw [overwrite_hwEmpty] at h
  exact h.symm.trans (evalDistMap_game_eq_gameReadsT L m A ρ f)

end honest

/-! ## The canonical runtime-2 game and runtime 1 -/

section canonical

open MeasureTheory

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **The canonical runtime-2 game of the table `L`**: runtime 2 with record ports, from the
memory `m₀`, running the template game with `L`'s public data, realized at `L`'s hidden values, its
trials' `h`-reads updating the memory with `upd`. -/
noncomputable def runtime2Law (upd : TrialUpd M) (m₀ : Finset HPos × M) (L : HonestTable)
    (A : Adversary (X × Z)) (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) : Measure γ :=
  (runtimeR m₀).evalDistMap .instruments (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ f

omit [Fintype M] [DecidableEq M] in
theorem hwLe_refl (W : Hw X Z) : HwLe W W :=
  ⟨fun _ ↦ Or.inr rfl, fun _ ↦ Or.inr rfl, fun _ ↦ Or.inr rfl⟩

end canonical

end Quantum.Xmss.Assembly

end
