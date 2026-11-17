module

public import Quantum.StdModel.Props.Basic
public import Quantum.StdModel.StraightLine
public import Quantum.Classical

@[expose] public section

/-!
# Classical challengers at a fixed table

At a fixed table, an adversary whose classical calls are answered by classical code runs as the
adversary whose calls are answered by the samplers of that code. `kRun W K leaf x s` is the
canonical form: `x` over `advSpec W.spec R`, each hash call kept, each classical call `q` answered
by the stateful sampler `K s q` run with uniform coins (`kTree`). `tRun W T leaf x s` is the same
recursion with any call trees `T`; two families of call trees with equal runs give equal runs
(`run_tRun_congr`).

* `run_challenged_withCallLog`: the SUF-CMA challenger with its signing transcript runs at the
  table `tab` as the canonical run against `signKernel`.
* `hcallImpl`, `runH`: a reduction's classical algorithms may also call the world's primitive
  (its honest hash work, by the classical calls of the hash ports) beside its own classical ports;
  `runH σ leaf x s` is `runCalls` with such handlers.
* `run_answered_logCalls_runH`: a reduction `runH σ` against a property challenger `ans`, with its
  transcript, runs at the table `tab` as the canonical run against `hKernel`, whose state is the
  handler state and the reduction's transcript.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

namespace Quantum.StdModel

open Common Props

/-! ## Generic facts on runs -/

section Generic

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) {A B : QReg}

/-- The framed relabelling map of `ℓ`, the map of a relabelling against `R`. -/
noncomputable def relabelMap {B' : QReg} (ℓ : A ≃ B') : MatrixMap (A × R.D) (B' × R.D) :=
  ((SubInstrument.relabel ℓ).frame R.D).branch ()

/-- A classical sampler run with uniform coins runs as itself. -/
theorem classicalOn_coinImpl_toQuantumAt {α : Type} (pa : ProbComp α) :
    ClassicalOn R (pa.toQuantumAt (QComp.coinImpl spec B)) pa LinearMap.id :=
  fun a ↦ branch_run₂_toQuantumAt_coinImpl R pa a

variable {R}

/-- Two programs that run as the same classical sampler through the same map have equal
runs. -/
theorem run₂_eq_of_classicalOn {α : Type} {x y : QComp spec A B α} {pa : ProbComp α}
    {Φ : MatrixMap (A × R.D) (B × R.D)} (hx : ClassicalOn R x pa Φ) (hy : ClassicalOn R y pa Φ) :
    R.run₂ .instruments x = R.run₂ .instruments y :=
  DSubInstrument.ext (funext fun a ↦ (hx a).trans (hy a).symm)

/-- Fixed-register programs with equal fixed-register runs have equal runs. -/
theorem run_eq_of_run₂_eq {α : Type} {x y : QComp spec A B α}
    (h : R.run₂ .instruments x = R.run₂ .instruments y) :
    R.run .instruments x = R.run .instruments y := by
  refine DSubInstrument.ext (funext fun p ↦ ?_)
  obtain ⟨u, hu, a⟩ := p
  subst hu
  exact congrArg (fun z : SubInstrument _ _ α ↦ z.branch a) h

/-- Sequencing fixed-register programs with equal runs and continuations with equal runs. -/
theorem run_bind_congr {α : Type} {Y : QReg → Type} {x y : QComp spec A B α}
    {k₁ k₂ : ∀ u, QuantumComp₂.Leaf B α u →
      QuantumComp LocalSig.instruments.{0} spec Y u}
    (h : R.run₂ .instruments x = R.run₂ .instruments y)
    (hk : ∀ a, R.run .instruments (k₁ B ⟨rfl, a⟩) = R.run .instruments (k₂ B ⟨rfl, a⟩)) :
    R.run .instruments (QuantumComp.bind x k₁) = R.run .instruments (QuantumComp.bind y k₂) := by
  have e₁ := QuantumRuntime.run_bind R LocalSig.Interp.instruments x k₁
  have e₂ := QuantumRuntime.run_bind R LocalSig.Interp.instruments y k₂
  rw [run_eq_of_run₂_eq h] at e₁
  refine e₁.trans ((congrArg (DSubInstrument.bind _) (funext fun p ↦ ?_)).trans e₂.symm)
  obtain ⟨u, hu, a⟩ := p
  subst hu
  exact hk a

/-- Sequencing a program and a relabelled program with equal runs, with continuations agreeing
through the relabelling. -/
theorem run_bind_map_congr {α β : Type} {Y : QReg → Type} (x : QComp spec A B α)
    (y : QComp spec A B β) (f : α → β)
    (hxy : R.run₂ .instruments (x.map f) = R.run₂ .instruments y)
    (k₁ : ∀ u, QuantumComp₂.Leaf B α u → QuantumComp LocalSig.instruments.{0} spec Y u)
    (k₂ : ∀ u, QuantumComp₂.Leaf B β u → QuantumComp LocalSig.instruments.{0} spec Y u)
    (hk : ∀ a, R.run .instruments (k₁ B ⟨rfl, a⟩) = R.run .instruments (k₂ B ⟨rfl, f a⟩)) :
    R.run .instruments (QuantumComp.bind x k₁) = R.run .instruments (QuantumComp.bind y k₂) := by
  have h₁ := run_bind_congr (R := R) (x := x) (y := x) (k₁ := k₁)
    (k₂ := fun u l ↦ k₂ u ⟨l.1, f l.2⟩) rfl hk
  have h₂ := run_bind_congr (R := R) (x := x.map f) (y := y) (k₁ := k₂) (k₂ := k₂) hxy
    fun _ ↦ rfl
  refine h₁.trans (Eq.trans ?_ h₂)
  rw [QuantumComp₂.map_eq_bind_pure]
  refine congrArg (R.run .instruments) ((congrArg (IFreeM.bind _) ?_).trans
    (IFreeM.bind_assoc _ _ _).symm)
  funext u l
  obtain ⟨rfl, r⟩ := l
  rfl

/-- A command followed by continuations with equal runs. -/
theorem run_liftBind_congr {X : QReg → Type}
    (c : QuantumComp.Cmd LocalSig.instruments.{0} spec A)
    {f g : (b : c.Resp) → IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec) X
      (c.next b)}
    (h : ∀ b, R.run .instruments (f b) = R.run .instruments (g b)) :
    R.run .instruments (IFreeM.liftBind (P := QuantumComp.toIPFunctor _ spec) c f) =
      R.run .instruments (IFreeM.liftBind (P := QuantumComp.toIPFunctor _ spec) c g) := by
  rcases c with o | ⟨i, E, ℓ⟩
  · exact (QuantumRuntime.run_primBind R _ o fun b ↦ f (ULift.up b)).trans
      ((congrArg (DSubInstrument.bind _) (funext fun b ↦ h (ULift.up b))).trans
        (QuantumRuntime.run_primBind R _ o fun b ↦ g (ULift.up b)).symm)
  · exact (QuantumRuntime.run_queryBind R _ i E ℓ fun b ↦ f (ULift.up b)).trans
      ((congrArg (DSubInstrument.bind _) (funext fun b ↦ h (ULift.up b))).trans
        (QuantumRuntime.run_queryBind R _ i E ℓ fun b ↦ g (ULift.up b)).symm)

end Generic

variable (W : OracleWorld) {Q : Type} {R : OracleSpec.{0, 0} Q} {St : Type}

/-! ## Runs with call trees -/

variable (R St) in
/-- A family of call trees: the answer to the classical call `q` from the state `s` with the
adversary's register `A ≃ Unit × E` held, returning the answer and the next state. -/
abbrev CallTrees :=
  (s : St) → (q : Q) → (E : QReg) → {A : QReg} → (ℓ : A ≃ (advSpec W.spec R).In (.call q) × E) →
    QComp W.spec A (QReg.of ((advSpec W.spec R).Out (.call q) × E)) (R.Range q × St)

/-- **The run with call trees `T`** of `x` from the state `s`: local operations and hash calls
kept, each classical call answered by `T`, the final state handed to `leaf`. -/
noncomputable def tRun {X Y : QReg → Type} (T : CallTrees W R St) (leaf : ∀ u, X u → St → Y u) :
    {A : QReg} →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A →
      St → IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} W.spec) Y A
  | _, .pure x, s => .pure (leaf _ x s)
  | _, .liftBind (.prim o) next, s => .liftBind (.prim o) fun b ↦ tRun T leaf (next b) s
  | _, .liftBind (.query (.hash p) E ℓ) next, s =>
      .liftBind (.query p E ℓ) fun b ↦ tRun T leaf (next b) s
  | _, .liftBind (.query (.call q) E ℓ) next, s =>
      QuantumComp.bind (T s q E ℓ) fun _ l ↦ l.1 ▸ tRun T leaf (next ⟨l.2.1⟩) l.2.2

variable {W} in
/-- **Call trees with equal runs give equal runs.** -/
theorem run_tRun_congr (tab : W.Tab) {X Y : QReg → Type} {T₁ T₂ : CallTrees W R St}
    (hT : ∀ (s : St) (q : Q) (E A : QReg) (ℓ : A ≃ (advSpec W.spec R).In (.call q) × E),
      (W.runtime tab).run₂ .instruments (T₁ s q E ℓ) =
        (W.runtime tab).run₂ .instruments (T₂ s q E ℓ))
    (leaf : ∀ u, X u → St → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A)
    (s : St) :
    (W.runtime tab).run .instruments (tRun W T₁ leaf x s) =
      (W.runtime tab).run .instruments (tRun W T₂ leaf x s) := by
  induction x using IFreeM.inductionOn generalizing s with
  | pure _ _ => rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨p | q, E, ℓ⟩
    · exact run_liftBind_congr (.prim o) fun b ↦ ih b s
    · exact run_liftBind_congr (.query p E ℓ) fun b ↦ ih b s
    · exact run_bind_congr (hT s q E A ℓ) fun a ↦ ih ⟨a.1⟩ a.2

/-! ## The canonical run -/

variable (R) in
/-- **A stateful classical challenger at a fixed table**: from the state and a classical query,
a sampler of the answer and the next state. -/
abbrev Kernel (St : Type) := St → (q : Q) → ProbComp (R.Range q × St)

/-- The canonical answer to the classical call `q` with the adversary's register
`A ≃ Unit × E` held: relabel, then sample `K s q` with uniform coins. -/
noncomputable def kTree (K : Kernel R St) : CallTrees W R St := fun s q E _ ℓ ↦
  (QComp.act (B := QReg.of ((advSpec W.spec R).Out (.call q) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ (K s q).toQuantumAt (QComp.coinImpl W.spec _)

/-- **The canonical run** of `x` against the kernel `K` from the state `s`: local operations and
hash calls kept, each classical call answered by `kTree`, the final state handed to `leaf`. -/
noncomputable def kRun {X Y : QReg → Type} (K : Kernel R St) (leaf : ∀ u, X u → St → Y u)
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R))
      X A) (s : St) : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} W.spec) Y A :=
  tRun W (kTree W K) leaf x s

/-- The canonical run of a fixed-register program, returning its value and the final state. -/
noncomputable def kRunQ (K : Kernel R St) {A B : QReg} {α : Type}
    (x : QComp (advSpec W.spec R) A B α) (s : St) : QComp W.spec A B (α × St) :=
  kRun W K (fun _ l s ↦ ⟨l.1, (l.2, s)⟩) x s

/-- The call case of the canonical run. -/
theorem kRun_call {X Y : QReg → Type} (K : Kernel R St) (leaf : ∀ u, X u → St → Y u) (q : Q)
    (E : QReg) {A : QReg} (ℓ : A ≃ (advSpec W.spec R).In (.call q) × E)
    (next : (b : ULift (R.Range q)) →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X
        (QReg.of ((advSpec W.spec R).Out (.call q) × E))) (s : St) :
    kRun W K leaf (IFreeM.liftBind (P := QuantumComp.toIPFunctor _ (advSpec W.spec R))
      (.query (.call q) E ℓ) next) s =
      QuantumComp.bind (kTree W K s q E ℓ) fun _ l ↦ l.1 ▸ kRun W K leaf (next ⟨l.2.1⟩) l.2.2 :=
  rfl

/-- **The canonical call tree runs as its sampler**, through the framed relabelling. -/
theorem classicalOn_kTree (Rt : QuantumRuntime W.spec) (K : Kernel R St) (s : St) (q : Q)
    (E : QReg) {A : QReg} (ℓ : A ≃ (advSpec W.spec R).In (.call q) × E) :
    ClassicalOn Rt (kTree W K s q E ℓ) (K s q)
      (relabelMap Rt (B' := QReg.of ((advSpec W.spec R).Out (.call q) × E)) ℓ) :=
  ((classicalOn_act (R := Rt) (B := QReg.of ((advSpec W.spec R).Out (.call q) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ classicalOn_coinImpl_toQuantumAt Rt (K s q)).congr
      (pure_bind _ _) (LinearMap.id_comp _)

/-! ## The SUF-CMA challenger -/

section Suf

variable {PK Req Resp F Seed SK : Type} (sch : Qrom.SchemeOver W.Oracles Seed PK SK Req Resp F)
  (sk : SK)

/-- The signer's call trees: the signer's answer, logged after the transcript. -/
noncomputable def signTrees : CallTrees W (Req →ₒ Resp) (QueryLog (Req →ₒ Resp)) :=
  fun log r E _ ℓ ↦ (signTree W sch sk r E ℓ).bind fun a ↦ QuantumComp₂.pure (a, log ++ [⟨r, a⟩])

/-- The signer at the table `tab` as a kernel: its answer, logged. -/
noncomputable def signKernel (tab : W.Tab) : Kernel (Req →ₒ Resp) (QueryLog (Req →ₒ Resp)) :=
  fun log r ↦ (fun a ↦ (a, log ++ [⟨r, a⟩])) <$> simulateQ (W.eager tab) (sch.sign sk r)

/-- The challenger on a program with its transcript is the run with the signer's call trees. -/
theorem substitute_logCalls_eq {X Y : QReg → Type}
    (leaf : ∀ u, X u → QueryLog (Req →ₒ Resp) → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (advSpec W.spec (Req →ₒ Resp))) X A) (log : QueryLog (Req →ₒ Resp)) :
    IFreeM.substitute (challenge W sch sk) (logCalls leaf x log) =
      tRun W (signTrees W sch sk) leaf x log := by
  induction x using IFreeM.inductionOn generalizing log with
  | pure _ _ => rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨p | r, E, ℓ⟩
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b log)
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b log)
    · refine (IFreeM.bind_assoc _ _ _).trans ((congrArg (IFreeM.bind _) ?_).trans
        (IFreeM.bind_assoc _ _ _).symm)
      funext u l
      obtain ⟨rfl, a⟩ := l
      exact ih ⟨a⟩ _

variable {W} in
/-- The signer's call tree runs as the signer at the table, logged, through the framed
relabelling. -/
theorem classicalOn_signTrees (tab : W.Tab) (log : QueryLog (Req →ₒ Resp)) (r : Req) (E : QReg)
    {A : QReg} (ℓ : A ≃ (advSpec W.spec (Req →ₒ Resp)).In (.call r) × E) :
    ClassicalOn (W.runtime tab) (signTrees W sch sk log r E ℓ) (signKernel W sch sk tab log r)
      (relabelMap (W.runtime tab)
        (B' := QReg.of ((advSpec W.spec (Req →ₒ Resp)).Out (.call r) × E)) ℓ) := by
  have h := ((classicalOn_act (R := W.runtime tab)
    (B := QReg.of ((advSpec W.spec (Req →ₒ Resp)).Out (.call r) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦
      W.classicalOn_toQuantumAt tab _ (sch.sign sk r)).bind fun a ↦
        classicalOn_pure (R := W.runtime tab) (spec := W.spec) (a, log ++ [⟨r, a⟩])
  refine h.congr ?_ ?_
  · simp only [pure_bind, signKernel, map_eq_bind_pure_comp, Function.comp_def]
  · rw [LinearMap.id_comp, LinearMap.id_comp]
    rfl

variable {W} in
/-- **The SUF-CMA challenger at a fixed table** with the signing transcript runs as the canonical
run against the signer's kernel. -/
theorem run_challenged_withCallLog (tab : W.Tab) {A B : QReg} {α : Type}
    (x : QComp (advSpec W.spec (Req →ₒ Resp)) A B α) :
    (W.runtime tab).run .instruments (challenged W sch sk (withCallLog x)) =
      (W.runtime tab).run .instruments (kRunQ W (signKernel W sch sk tab) x []) := by
  have h := substitute_logCalls_eq W sch sk (X := QuantumComp₂.Leaf B α)
    (fun (u : QReg) (l : QuantumComp₂.Leaf B α u) (log : QueryLog (Req →ₒ Resp)) ↦
      (⟨l.1, (l.2, log)⟩ : QuantumComp₂.Leaf B (α × QueryLog (Req →ₒ Resp)) u)) x []
  exact (congrArg ((W.runtime tab).run .instruments) h).trans (run_tRun_congr tab
    (fun s q E A ℓ ↦ run₂_eq_of_classicalOn (classicalOn_signTrees sch sk tab s q E ℓ)
      (classicalOn_kTree W _ _ s q E ℓ)) _ x [])

variable {W} in
/-- The SUF-CMA challenger at a fixed table, fixed-register form. -/
theorem run₂_challenged_withCallLog (tab : W.Tab) {A B : QReg} {α : Type}
    (x : QComp (advSpec W.spec (Req →ₒ Resp)) A B α) :
    (W.runtime tab).run₂ .instruments (challenged W sch sk (withCallLog x)) =
      (W.runtime tab).run₂ .instruments (kRunQ W (signKernel W sch sk tab) x []) := by
  rw [QuantumRuntime.run₂_eq_comap, QuantumRuntime.run₂_eq_comap,
    run_challenged_withCallLog]

end Suf

/-! ## Reductions with honest work -/

section Reduction

variable {Q' : Type} {R' : OracleSpec.{0, 0} Q'}

variable (R') in
/-- A program over the world's ports as a program over a reduction's hash ports. -/
def liftHash {X : QReg → Type} :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} W.spec) X A →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R')) X A
  | _, .pure x => .pure x
  | _, .liftBind (.prim o) next => .liftBind (.prim o) fun b ↦ liftHash (next b)
  | _, .liftBind (.query p E ℓ) next =>
      .liftBind (.query (.hash p) E ℓ) fun b ↦ liftHash (next b)

variable (R') in
/-- The held register `B` beside a classical port's trivial register. -/
def callSplit (q' : Q') (B : QReg) : B ≃ (advSpec W.spec R').In (.call q') × B :=
  (Equiv.uniqueProd B Unit).symm

variable (R') in
/-- **A classical call of the reduction's port `q'`** beside the held register `B`. -/
noncomputable def callQ (q' : Q') (B : QReg) : QComp (advSpec W.spec R') B B (R'.Range q') :=
  (QuantumComp₂.query (L := LocalSig.instruments.{0}) (spec := advSpec W.spec R') (.call q') B
    (callSplit W R' q' B)).bind fun r ↦
      (QComp.act (A := QReg.of ((advSpec W.spec R').Out (.call q') × B)) (B := B)
        (SubInstrument.relabel (callSplit W R' q' B).symm)).bind fun _ ↦ QuantumComp₂.pure r

variable (R') in
/-- **A reduction's classical algorithms** beside a held register: the world's coins and
primitive by its classical calls on the hash ports, the reduction's own ports by `callQ`. -/
noncomputable def hcallImpl (B : QReg) :
    QueryImpl (W.Oracles + R') (QComp (advSpec W.spec R') B B)
  | .inl t => liftHash W R' (W.impl B t)
  | .inr q' => callQ W R' q' B

variable (R R') in
/-- A reduction's handler with honest work: from its state and the adversary's classical query,
an algorithm over the world's oracles and the reduction's ports. -/
abbrev HHandler (St : Type) :=
  St → (q : Q) → OracleComp (W.Oracles + R') (R.Range q × St)

/-- The reduction's answer to the adversary's classical call `q`: relabel, then run the
handler. -/
noncomputable def answerTreeH (σ : HHandler W R R' St) (s : St) (q : Q) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec W.spec R).In (.call q) × E) :
    QComp (advSpec W.spec R') A (QReg.of ((advSpec W.spec R).Out (.call q) × E))
      (R.Range q × St) :=
  (QComp.act (B := QReg.of ((advSpec W.spec R).Out (.call q) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ (σ s q).toQuantumAt (hcallImpl W R' _)

/-- **The straight-line reduction with honest work**: `A`'s program `x`, every local operation and
hash call kept, every classical call answered by the handler `σ` (`answerTreeH`). -/
noncomputable def runH {X Y : QReg → Type} (σ : HHandler W R R' St)
    (leaf : ∀ u, X u → St → Y u) :
    {A : QReg} →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A →
      St → IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R')) Y A
  | _, .pure x, s => .pure (leaf _ x s)
  | _, .liftBind (.prim o) next, s => .liftBind (.prim o) fun b ↦ runH σ leaf (next b) s
  | _, .liftBind (.query (.hash p) E ℓ) next, s =>
      .liftBind (.query (.hash p) E ℓ) fun b ↦ runH σ leaf (next b) s
  | _, .liftBind (.query (.call q) E ℓ) next, s =>
      QuantumComp.bind (answerTreeH W σ s q E ℓ) fun _ l ↦
        l.1 ▸ runH σ leaf (next ⟨l.2.1⟩) l.2.2

/-- A fixed-register program with its transcript from `log`. -/
def withCallLogFrom {S : QuantumOracleSpec.{0, 0}} {QS : Type} {RS : OracleSpec.{0, 0} QS}
    {A B : QReg} {α : Type} (log : QueryLog RS) (x : QComp (advSpec S RS) A B α) :
    QComp (advSpec S RS) A B (α × QueryLog RS) :=
  logCalls (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x log

/-- Keeping the transcript of a sequence: the transcript of the first program, then of the
continuation from it. -/
theorem logCalls_bind {S : QuantumOracleSpec.{0, 0}} {QS : Type} {RS : OracleSpec.{0, 0} QS}
    {Y Z : QReg → Type} (leaf : ∀ u, Y u → QueryLog RS → Z u) {A B : QReg} {α : Type}
    (x : QComp (advSpec S RS) A B α)
    (k : ∀ u, QuantumComp₂.Leaf B α u →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec S RS)) Y u)
    (log : QueryLog RS) :
    logCalls leaf (QuantumComp.bind x k) log =
      QuantumComp.bind (withCallLogFrom log x) fun u l ↦
        logCalls leaf (k u ⟨l.1, l.2.1⟩) l.2.2 := by
  induction x using IFreeM.inductionOn generalizing log with
  | pure u l =>
    obtain ⟨rfl, a⟩ := l
    rfl
  | liftBind A c next ih => exact congrArg (IFreeM.liftBind c) (funext fun b ↦ ih b _)

/-- A relabelling followed by its inverse is the identity map. -/
theorem relabel_symm_comp {A B : QReg} (e : A ≃ B) (D : QReg) :
    ((SubInstrument.relabel e.symm).frame D).branch () ∘ₗ
        ((SubInstrument.relabel e).frame D).branch () = LinearMap.id := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [LinearMap.comp_apply, SubInstrument.frame_relabel, SubInstrument.frame_relabel,
    SubInstrument.relabel_branch_apply, SubInstrument.relabel_branch_apply,
    Matrix.submatrix_submatrix]
  ext ⟨a, d⟩ ⟨b, d'⟩
  simp

variable {W} in
/-- **The reduction's oracles at the table `tab`** against the challenger `ans`: the world's
oracles answered by the table, the reduction's ports by the challenger, each appended to the
reduction's transcript. -/
noncomputable def logImpl (tab : W.Tab) (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q')) :
    QueryImpl (W.Oracles + R') (StateT (QueryLog R') ProbComp)
  | .inl t => StateT.lift (W.eager tab t)
  | .inr q' => fun log ↦ (fun a ↦ (a, log ++ [⟨q', a⟩])) <$> simulateQ (W.eager tab) (ans q')

variable {W} in
/-- **The kernel of a reduction against a challenger** at the table `tab`: the handler run by
`logImpl`, with the handler state and the reduction's transcript as the state. -/
noncomputable def hKernel (tab : W.Tab) (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q'))
    (σ : HHandler W R R' St) : Kernel R (St × QueryLog R') :=
  fun p q ↦ (fun r ↦ (r.1.1, (r.1.2, r.2))) <$> (simulateQ (logImpl tab ans) (σ p.1 q)).run p.2

/-- The challenger on lifted world calls passes them through. -/
theorem answered_logCalls_liftHash_bind (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q'))
    (log : QueryLog R') {A B C : QReg} {α β : Type} (y : QComp W.spec A B α)
    (k : α → QComp (advSpec W.spec R') B C β) :
    answered W ans (withCallLogFrom log (QuantumComp₂.bind (liftHash W R' y) k)) =
      y.bind fun a ↦ answered W ans (withCallLogFrom log (k a)) := by
  induction y using IFreeM.inductionOn with
  | pure u l =>
    obtain ⟨rfl, a⟩ := l
    rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨p, E, ℓ⟩
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b)
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b)

/-- The challenger on a classical call of the reduction's port: its answer, between the
relabellings, logged. -/
theorem answered_logCalls_callQ_bind (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q'))
    (log : QueryLog R') (q' : Q') {B C : QReg} {β : Type}
    (k : R'.Range q' → QComp (advSpec W.spec R') B C β) :
    answered W ans (withCallLogFrom log (QuantumComp₂.bind (callQ W R' q' B) k)) =
      (callTree W ans q' B (callSplit W R' q' B)).bind fun a ↦
        (QComp.act (A := QReg.of ((advSpec W.spec R').Out (.call q') × B)) (B := B)
          (SubInstrument.relabel (callSplit W R' q' B).symm)).bind fun _ ↦
            answered W ans (withCallLogFrom (log ++ [⟨q', a⟩]) (k a)) := by
  refine (IFreeM.bind_assoc _ _ _).trans (congrArg (IFreeM.bind _) ?_)
  funext u l
  obtain ⟨rfl, a⟩ := l
  rfl

variable {W} in
/-- **A reduction's classical algorithm against a challenger at a fixed table** runs as the
algorithm answered by `logImpl`, with its transcript. -/
theorem classicalOn_answered_hcall (tab : W.Tab)
    (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q')) {B : QReg} {α : Type}
    (oa : OracleComp (W.Oracles + R') α) (log : QueryLog R') :
    ClassicalOn (W.runtime tab)
      (answered W ans (withCallLogFrom log (oa.toQuantumAt (hcallImpl W R' B))))
      ((simulateQ (logImpl tab ans) oa).run log) LinearMap.id := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a =>
    refine (classicalOn_pure (R := W.runtime tab) (spec := W.spec) (B := B) (a, log)).congr ?_ rfl
    simp
  | query_bind t k ih =>
    rw [toQuantumAt_query_bind]
    rcases t with t | q'
    · rw [show hcallImpl W R' B (.inl t) = liftHash W R' (W.impl B t) from rfl,
        answered_logCalls_liftHash_bind]
      refine ((W.classicalOn_impl tab B t).bind_id fun a ↦ ih a log).congr ?_ rfl
      simp [logImpl, StateT.run_bind, StateT.run_lift]
    · rw [show hcallImpl W R' B (.inr q') = callQ W R' q' B from rfl,
        answered_logCalls_callQ_bind]
      have h := ((classicalOn_act (R := W.runtime tab) (spec := W.spec)
        (B := QReg.of ((advSpec W.spec R').Out (.call q') × B))
        (SubInstrument.relabel (callSplit W R' q' B))).bind fun _ ↦
          W.classicalOn_toQuantumAt tab _ (ans q')).bind fun a ↦
            (classicalOn_act (R := W.runtime tab) (spec := W.spec)
              (A := QReg.of ((advSpec W.spec R').Out (.call q') × B)) (B := B)
              (SubInstrument.relabel (callSplit W R' q' B).symm)).bind fun _ ↦
                ih a (log ++ [⟨q', a⟩])
      refine h.congr ?_ ?_
      · simp only [pure_bind, logImpl, simulateQ_bind, simulateQ_spec_query, StateT.run]
        change _ = (((fun a ↦ (a, log ++ [⟨q', a⟩])) <$> simulateQ (W.eager tab) (ans q')) >>=
          fun p ↦ simulateQ (logImpl tab ans) (k p.1) p.2)
        rw [bind_map_left]
      · rw [LinearMap.id_comp, LinearMap.id_comp]
        refine LinearMap.ext fun ρ ↦ ?_
        rw [LinearMap.comp_apply, SubInstrument.frame_relabel, SubInstrument.frame_relabel,
          SubInstrument.relabel_branch_apply, SubInstrument.relabel_branch_apply,
          Matrix.submatrix_submatrix]
        ext ⟨a, d⟩ ⟨b, d'⟩
        rfl

/-- The reduction's call trees against the challenger, with the transcript in the state. -/
noncomputable def hTrees (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q'))
    (σ : HHandler W R R' St) : CallTrees W R (St × QueryLog R') := fun p q E _ ℓ ↦
  (answered W ans (withCallLogFrom p.2 (answerTreeH W σ p.1 q E ℓ))).bind fun r ↦
    QuantumComp₂.pure (r.1.1, (r.1.2, r.2))

/-- The challenger on a reduction with its transcript is the run with the reduction's call
trees. -/
theorem answered_logCalls_runH_eq (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q'))
    (σ : HHandler W R R' St) {X Y Z : QReg → Type} (leaf : ∀ u, X u → St → Y u)
    (leafL : ∀ u, Y u → QueryLog R' → Z u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A)
    (s : St) (log : QueryLog R') :
    IFreeM.substitute (answerSub W ans) (logCalls leafL (runH W σ leaf x s) log) =
      tRun W (hTrees W ans σ) (fun u y p ↦ leafL u (leaf u y p.1) p.2) x (s, log) := by
  induction x using IFreeM.inductionOn generalizing s log with
  | pure _ _ => rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨p | q, E, ℓ⟩
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b s log)
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b s log)
    · refine (congrArg (IFreeM.substitute _) (logCalls_bind leafL (answerTreeH W σ s q E ℓ) _
        log)).trans ((IFreeM.substitute_bind _ _ _).trans ((congrArg (IFreeM.bind _) ?_).trans
          (IFreeM.bind_assoc _ _ _).symm))
      funext u l
      obtain ⟨rfl, ⟨⟨a, s'⟩, log'⟩⟩ := l
      exact ih ⟨a⟩ s' log'

variable {W} in
/-- The reduction's call tree runs as its kernel, through the framed relabelling. -/
theorem classicalOn_hTrees (tab : W.Tab) (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q'))
    (σ : HHandler W R R' St) (p : St × QueryLog R') (q : Q) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec W.spec R).In (.call q) × E) :
    ClassicalOn (W.runtime tab) (hTrees W ans σ p q E ℓ) (hKernel tab ans σ p q)
      (relabelMap (W.runtime tab) (B' := QReg.of ((advSpec W.spec R).Out (.call q) × E)) ℓ) := by
  have h := ((classicalOn_act (R := W.runtime tab) (spec := W.spec)
    (B := QReg.of ((advSpec W.spec R).Out (.call q) × E)) (SubInstrument.relabel ℓ)).bind
      fun _ ↦ classicalOn_answered_hcall tab ans (σ p.1 q) p.2).bind fun r ↦
        classicalOn_pure (R := W.runtime tab) (spec := W.spec) (r.1.1, (r.1.2, r.2))
  refine h.congr ?_ ?_
  · simp only [pure_bind, hKernel, map_eq_bind_pure_comp, Function.comp_def]
  · rw [LinearMap.id_comp, LinearMap.id_comp]
    rfl

variable {W} in
/-- **A reduction against a property challenger at a fixed table**, with the reduction's
transcript, runs as the canonical run against `hKernel`. -/
theorem run_answered_logCalls_runH (tab : W.Tab)
    (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q')) (σ : HHandler W R R' St)
    {X Y Z : QReg → Type} (leaf : ∀ u, X u → St → Y u) (leafL : ∀ u, Y u → QueryLog R' → Z u)
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A)
    (s : St) (log : QueryLog R') :
    (W.runtime tab).run .instruments
        (IFreeM.substitute (answerSub W ans) (logCalls leafL (runH W σ leaf x s) log)) =
      (W.runtime tab).run .instruments
        (kRun W (hKernel tab ans σ) (fun u y p ↦ leafL u (leaf u y p.1) p.2) x (s, log)) := by
  rw [answered_logCalls_runH_eq]
  exact run_tRun_congr tab (fun p q E A ℓ ↦ run₂_eq_of_classicalOn
    (classicalOn_hTrees tab ans σ p q E ℓ) (classicalOn_kTree W _ _ p q E ℓ)) _ x (s, log)

variable {W} in
/-- The world's oracles and the challenger at the table `tab`, without the transcript. -/
noncomputable def plainImpl (tab : W.Tab)
    (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q')) :
    QueryImpl (W.Oracles + R') ProbComp
  | .inl t => W.eager tab t
  | .inr q' => simulateQ (W.eager tab) (ans q')

variable {W} in
/-- Keeping the transcript does not change the result. -/
theorem fst_run_logImpl (tab : W.Tab) (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q'))
    {α : Type} (oa : OracleComp (W.Oracles + R') α) (log : QueryLog R') :
    Prod.fst <$> (simulateQ (logImpl tab ans) oa).run log = simulateQ (plainImpl tab ans) oa := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with t | q'
    · simp [logImpl, plainImpl, StateT.run_bind, StateT.run_lift, ih]
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      change ((fun a ↦ (a, log ++ [⟨q', a⟩])) <$> simulateQ (W.eager tab) (ans q')) >>= _ = _
      simp [plainImpl, map_eq_bind_pure_comp]

/-- The cost in world calls of a reduction's classical query. -/
def hcallCost : (W.Oracles + R').Domain → ℕ
  | .inl t => W.cost t
  | .inr _ => 0

/-- A lifted world program's hash charge is its call count. -/
theorem isChargeBound_liftHash {X : QReg → Type} {A : QReg}
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} W.spec) X A) {n : ℕ}
    (h : IFreeM.IsChargeBound y (fun _ c ↦ c.queryCharge) n) :
    IFreeM.IsChargeBound (liftHash W R' y) (cmdCharge hashCharge) n := by
  induction y using IFreeM.inductionOn generalizing n with
  | pure _ _ => trivial
  | liftBind A c next ih =>
    rw [IFreeM.isChargeBound_liftBind_iff] at h
    rcases c with o | ⟨p, E, ℓ⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨h.1, fun b ↦ ih b (h.2 b)⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨h.1, fun b ↦ ih b (h.2 b)⟩

/-- Each classical query of a reduction costs its world calls in hash calls. -/
theorem isChargeBound_hcallImpl (B : QReg) (t : (W.Oracles + R').Domain) :
    IFreeM.IsChargeBound (hcallImpl W R' B t) (cmdCharge hashCharge) (hcallCost W t) := by
  rcases t with t | q'
  · exact isChargeBound_liftHash W (W.impl B t) (W.isTotalQueryBound_impl B t)
  · change IFreeM.IsChargeBound (callQ W R' q' B) _ 0
    unfold callQ
    refine IFreeM.IsChargeBound.mono (n₁ := 0 + 0) (FreeM₂.isChargeBound_bind (n₁ := 0)
      (n₂ := 0) (isChargeBound_query₂ (S := W.spec) (RS := R') hashCharge (.call q') B
        (callSplit W R' q' B)) fun _ ↦ ?_) le_rfl
    exact (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (isChargeBound_act _ _ 0) fun _ ↦
      IFreeM.isChargeBound_pure _ 0).mono le_rfl

/-- A reduction's classical algorithm costing at most `n` world calls makes at most `n` hash
calls. -/
theorem isChargeBound_toQuantumAt_hcallImpl (B : QReg) {α : Type}
    {oa : OracleComp (W.Oracles + R') α} {n : ℕ}
    (h : QueryCostAtMost oa (hcallCost W (R' := R')) n) :
    IFreeM.IsChargeBound (oa.toQuantumAt (hcallImpl W R' B)) (cmdCharge hashCharge) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h
    rw [toQuantumAt_query_bind]
    have hb := FreeM₂.isChargeBound_bind (isChargeBound_hcallImpl W B t) fun y ↦ ih y (h.2 y)
    rwa [Nat.add_sub_cancel' h.1] at hb

/-- **A reduction's hash calls**: at most `n` when `A` is within `n` counting a hash call one and a
classical call `k`, and every handler costs at most `k` world calls (its honest work). -/
theorem isChargeBound_runH_hash {X Y : QReg → Type} (σ : HHandler W R R' St)
    (leaf : ∀ u, X u → St → Y u) {k : ℕ}
    (hσ : ∀ s q, QueryCostAtMost (σ s q) (hcallCost W (R' := R')) k)
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A)
    (s : St) {n : ℕ}
    (hx : IFreeM.IsChargeBound x (cmdCharge (srcCharge (hashCharge (Q := Q')) k)) n) :
    IFreeM.IsChargeBound (runH W σ leaf x s) (cmdCharge hashCharge) n := by
  induction x using IFreeM.inductionOn generalizing s n with
  | pure _ _ => trivial
  | liftBind A cmd next ih =>
    replace hx := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hx
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨hx.1, fun b ↦ ih b s (hx.2 b)⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨hx.1, fun b ↦ ih b s (hx.2 b)⟩
    · have ht : IFreeM.IsChargeBound (answerTreeH W σ s q E ℓ) (cmdCharge hashCharge) (0 + k) :=
        FreeM₂.isChargeBound_bind (isChargeBound_act hashCharge _ 0) fun _ ↦
          isChargeBound_toQuantumAt_hcallImpl W _ (hσ s q)
      have hk : k ≤ n := hx.1
      refine (IFreeM.isChargeBound_bind (n₂ := n - k) ht fun u l ↦ ?_).mono (by omega)
      obtain ⟨rfl, v⟩ := l
      exact ih ⟨v.1⟩ v.2 (hx.2 ⟨v.1⟩)

/-- An adversary within `n` hash calls and `m` classical calls is within `n + k * m` when a
classical call counts `k`. -/
theorem isChargeBound_srcCharge {X : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A)
    {n m : ℕ} (k : ℕ) (hn : IFreeM.IsChargeBound x (cmdCharge hashCharge) n)
    (hm : IFreeM.IsChargeBound x (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound x (cmdCharge (srcCharge (hashCharge (Q := Q')) k)) (n + k * m) := by
  induction x using IFreeM.inductionOn generalizing n m with
  | pure _ _ => trivial
  | liftBind A cmd next ih =>
    replace hn := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hn
    replace hm := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hm
    refine (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ?_
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact ⟨Nat.zero_le _, fun b ↦ ih b (hn.2 b) (hm.2 b)⟩
    · have h1 : 1 ≤ n := hn.1
      refine ⟨by change 1 ≤ n + k * m; omega, fun b ↦ (ih b (hn.2 b) (hm.2 b)).mono ?_⟩
      change n - 1 + k * (m - 0) ≤ n + k * m - 1
      rw [Nat.sub_zero]
      omega
    · have h1 : 1 ≤ m := hm.1
      refine ⟨by change k ≤ n + k * m; nlinarith, fun b ↦ (ih b (hn.2 b) (hm.2 b)).mono ?_⟩
      change n - 0 + k * (m - 1) ≤ n + k * m - k
      rw [Nat.mul_sub_one]
      have : k ≤ k * m := Nat.le_mul_of_pos_right k h1
      omega

end Reduction

/-! ## State projections and probabilities -/

variable {W} in
/-- **Projecting the kernel's state**: if the kernel `K₂` answers as `K₁` on the projected state,
the canonical runs agree when the leaf reads only the projection. -/
theorem run_kRun_map (Rt : QuantumRuntime W.spec) {St₂ : Type} (K₁ : Kernel R St)
    (K₂ : Kernel R St₂) (π : St₂ → St) (hK : ∀ s q, Prod.map id π <$> K₂ s q = K₁ (π s) q)
    {X Y : QReg → Type} (leaf : ∀ u, X u → St → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A)
    (s : St₂) :
    Rt.run .instruments (kRun W K₂ (fun u y s ↦ leaf u y (π s)) x s) =
      Rt.run .instruments (kRun W K₁ leaf x (π s)) := by
  induction x using IFreeM.inductionOn generalizing s with
  | pure _ _ => rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨p | q, E, ℓ⟩
    · exact run_liftBind_congr (.prim o) fun b ↦ ih b s
    · exact run_liftBind_congr (.query p E ℓ) fun b ↦ ih b s
    · have hmap : ClassicalOn Rt ((kTree W K₂ s q E ℓ).map (Prod.map id π)) (K₁ (π s) q)
          (relabelMap Rt (B' := QReg.of ((advSpec W.spec R).Out (.call q) × E)) ℓ) := by
        rw [QuantumComp₂.map_eq_bind_pure]
        refine ((classicalOn_kTree W Rt K₂ s q E ℓ).bind fun r ↦
          classicalOn_pure (R := Rt) (spec := W.spec) (Prod.map id π r)).congr ?_ ?_
        · rw [← hK, map_eq_bind_pure_comp]
          rfl
        · exact LinearMap.id_comp _
      exact run_bind_map_congr _ _ (Prod.map id π)
        (run₂_eq_of_classicalOn hmap (classicalOn_kTree W Rt K₁ (π s) q E ℓ)) _ _
        fun a ↦ ih ⟨a.1⟩ a.2

/-- Sequencing a program that runs as a classical sampler with continuations whose runs agree on
the sampler's support. -/
theorem run_bind_congr_support {spec : QuantumOracleSpec.{0, 0}} {Rt : QuantumRuntime spec}
    {A B : QReg} {α : Type} {Y : QReg → Type} {x : QComp spec A B α} {pa : ProbComp α}
    {Φ : MatrixMap (A × Rt.D) (B × Rt.D)} (hx : ClassicalOn Rt x pa Φ)
    {k₁ k₂ : ∀ u, QuantumComp₂.Leaf B α u → QuantumComp LocalSig.instruments.{0} spec Y u}
    (hk : ∀ a ∈ support pa,
      Rt.run .instruments (k₁ B ⟨rfl, a⟩) = Rt.run .instruments (k₂ B ⟨rfl, a⟩)) :
    Rt.run .instruments (QuantumComp.bind x k₁) =
      Rt.run .instruments (QuantumComp.bind x k₂) := by
  have e₁ := QuantumRuntime.run_bind Rt LocalSig.Interp.instruments x k₁
  have e₂ := QuantumRuntime.run_bind Rt LocalSig.Interp.instruments x k₂
  rw [e₁, e₂]
  refine DSubInstrument.ext (funext fun c ↦ LinearMap.ext fun ρ ↦ ?_)
  rw [DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply]
  refine tsum_congr fun p ↦ ?_
  obtain ⟨u, hu, a⟩ := p
  subst hu
  by_cases ha : a ∈ support pa
  · rw [hk a ha]
  · have h0 : (Rt.run .instruments x).branch ⟨_, rfl, a⟩ = 0 := by
      have h := hx a
      rw [prEvent_eq_zero_of_not_mem_support pa ha] at h
      simp only [ENNReal.toReal_zero, Complex.ofReal_zero, zero_smul] at h
      exact h
    rw [h0]
    simp

variable {W} in
/-- **Simulation of kernels**: if on the states satisfying `Inv` the kernel `K₂` answers as `K₁`
on the projected state and keeps `Inv`, the canonical runs agree when the leaves agree through
the projection on such states. -/
theorem run_kRun_sim (Rt : QuantumRuntime W.spec) {St₂ : Type} (K₁ : Kernel R St)
    (K₂ : Kernel R St₂) (Inv : St₂ → Prop) (π : St₂ → St)
    (hK : ∀ s, Inv s → ∀ q, Prod.map id π <$> K₂ s q = K₁ (π s) q)
    (hInv : ∀ s, Inv s → ∀ q, ∀ p ∈ support (K₂ s q), Inv p.2)
    {X Y : QReg → Type} (leaf₁ : ∀ u, X u → St → Y u) (leaf₂ : ∀ u, X u → St₂ → Y u)
    (hleaf : ∀ s, Inv s → ∀ u y, leaf₂ u y s = leaf₁ u y (π s)) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A)
    (s : St₂) (hs : Inv s) :
    Rt.run .instruments (kRun W K₂ leaf₂ x s) =
      Rt.run .instruments (kRun W K₁ leaf₁ x (π s)) := by
  induction x using IFreeM.inductionOn generalizing s with
  | pure u y => exact congrArg (fun z ↦ Rt.run .instruments (IFreeM.pure
      (P := QuantumComp.toIPFunctor LocalSig.instruments.{0} W.spec) z)) (hleaf s hs u y)
  | liftBind A c next ih =>
    rcases c with o | ⟨p | q, E, ℓ⟩
    · exact run_liftBind_congr (.prim o) fun b ↦ ih b s hs
    · exact run_liftBind_congr (.query p E ℓ) fun b ↦ ih b s hs
    · have hmap : ClassicalOn Rt ((kTree W K₂ s q E ℓ).map (Prod.map id π)) (K₁ (π s) q)
          (relabelMap Rt (B' := QReg.of ((advSpec W.spec R).Out (.call q) × E)) ℓ) := by
        rw [QuantumComp₂.map_eq_bind_pure]
        refine ((classicalOn_kTree W Rt K₂ s q E ℓ).bind fun r ↦
          classicalOn_pure (R := Rt) (spec := W.spec) (Prod.map id π r)).congr ?_ ?_
        · rw [← hK s hs, map_eq_bind_pure_comp]
          rfl
        · exact LinearMap.id_comp _
      refine (run_bind_congr_support (classicalOn_kTree W Rt K₂ s q E ℓ)
        (k₂ := fun u l ↦ (fun _ l ↦ l.1 ▸ kRun W K₁ leaf₁ (next ⟨l.2.1⟩) l.2.2 :
          ∀ u, QuantumComp₂.Leaf (QReg.of ((advSpec W.spec R).Out (.call q) × E))
            (R.Range q × St) u → _) u ⟨l.1, Prod.map id π l.2⟩)
        fun a ha ↦ ih ⟨a.1⟩ a.2 (hInv s hs q a ha)).trans ?_
      exact run_bind_map_congr _ _ (Prod.map id π)
        (run₂_eq_of_classicalOn hmap (classicalOn_kTree W Rt K₁ (π s) q E ℓ)) _ _ fun _ ↦ rfl

/-- Relabelling the value of a canonical run relabels its leaves. -/
theorem imap_kRun {X : QReg → Type} {B : QReg} {β γ : Type} (K : Kernel R St)
    (leaf : ∀ u, X u → St → QuantumComp₂.Leaf B β u) (g : β → γ) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A)
    (s : St) :
    QuantumComp₂.map g (kRun W K leaf x s : QComp W.spec A B β) =
      kRun W K (fun u y s ↦ ⟨(leaf u y s).1, g (leaf u y s).2⟩) x s := by
  induction x using IFreeM.inductionOn generalizing s with
  | pure _ _ => rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨p | q, E, ℓ⟩
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b s)
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b s)
    · refine (IFreeM.imap_bind _ _ _).trans (congrArg (IFreeM.bind _) ?_)
      funext u l
      obtain ⟨rfl, a, s'⟩ := l
      exact ih ⟨a⟩ s'

variable {W} in
/-- Programs with equal runs at the table `tab` win with equal probabilities. -/
theorem probAt_congr {tab : W.Tab} {x y : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool}
    (h : (W.runtime tab).run .instruments x = (W.runtime tab).run .instruments y) :
    W.probAt tab x = W.probAt tab y := by
  simp only [OracleWorld.probAt, QuantumRuntime.evalDistMap, QuantumRuntime.jointPost, h]

/-! ## Games in normal form -/

section Normal

variable {Q' : Type} {R' : OracleSpec.{0, 0} Q'}

/-- Sequencing fixed-register programs with equal runs. -/
theorem run₂_bind_congr {spec : QuantumOracleSpec.{0, 0}} {Rt : QuantumRuntime spec}
    {A B C : QReg} {α β : Type} {x y : QComp spec A B α} {k₁ k₂ : α → QComp spec B C β}
    (h : Rt.run₂ .instruments x = Rt.run₂ .instruments y)
    (hk : ∀ a, Rt.run₂ .instruments (k₁ a) = Rt.run₂ .instruments (k₂ a)) :
    Rt.run₂ .instruments (x.bind k₁) = Rt.run₂ .instruments (y.bind k₂) := by
  rw [QuantumRuntime.run₂_bind, QuantumRuntime.run₂_bind, h]
  exact congrArg _ (funext hk)

/-- The transcript of a sequence of fixed-register programs. -/
theorem withCallLogFrom_bind {S : QuantumOracleSpec.{0, 0}} {QS : Type}
    {RS : OracleSpec.{0, 0} QS} {A B C : QReg} {α β : Type} (log : QueryLog RS)
    (x : QComp (advSpec S RS) A B α) (k : α → QComp (advSpec S RS) B C β) :
    withCallLogFrom log (x.bind k) =
      (withCallLogFrom log x).bind fun p ↦ withCallLogFrom p.2 (k p.1) := by
  refine (logCalls_bind _ x (fun _ p ↦ p.casesOn fun h a ↦ h ▸ k a) log).trans
    (congrArg (IFreeM.bind _) ?_)
  funext u l
  obtain ⟨rfl, a, log'⟩ := l
  rfl

/-- The challenger on a sequence of fixed-register programs. -/
theorem answered_bind (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q')) {A B C : QReg}
    {α β : Type} (x : QComp (advSpec W.spec R') A B α) (k : α → QComp (advSpec W.spec R') B C β) :
    answered W ans (x.bind k) = (answered W ans x).bind fun a ↦ answered W ans (k a) := by
  refine (IFreeM.substitute_bind _ x _).trans (congrArg (IFreeM.bind _) ?_)
  funext u l
  obtain ⟨rfl, a⟩ := l
  rfl

/-- A reduction run on a fixed-register adversary, returning the value and the final state. -/
noncomputable def runHQ (σ : HHandler W R R' St) {A B : QReg} {α : Type}
    (x : QComp (advSpec W.spec R) A B α) (s : St) : QComp (advSpec W.spec R') A B (α × St) :=
  runH W σ (X := QuantumComp₂.Leaf B α) (Y := QuantumComp₂.Leaf B (α × St))
    (fun _ l s ↦ ⟨l.1, (l.2, s)⟩) x s

/-- The canonical run against a reduction's kernel, returning the value, the handler state and
the reduction's transcript. -/
noncomputable def kRunL (K : Kernel R (St × QueryLog R')) {A B : QReg} {α : Type}
    (x : QComp (advSpec W.spec R) A B α) (s : St) (log : QueryLog R') :
    QComp W.spec A B ((α × St) × QueryLog R') :=
  kRun W K (Y := QuantumComp₂.Leaf B ((α × St) × QueryLog R'))
    (fun _ l q ↦ ⟨l.1, ((l.2, q.1), q.2)⟩) x (s, log)

/-- The canonical run against a reduction's kernel is the canonical run with the transcript in
the state, reassociated. -/
theorem kRunL_eq_map (K : Kernel R (St × QueryLog R')) {A B : QReg} {α : Type}
    (x : QComp (advSpec W.spec R) A B α) (s : St) (log : QueryLog R') :
    kRunL W K x s log = (kRunQ W K x (s, log)).map fun r ↦ ((r.1, r.2.1), r.2.2) :=
  (imap_kRun W K (X := QuantumComp₂.Leaf B α) (fun _ l s ↦ ⟨l.1, (l.2, s)⟩)
    (fun r ↦ ((r.1, r.2.1), r.2.2)) x (s, log)).symm

variable {W} in
/-- **Collapsing a canonical run**: when `K₂` simulates `K₁` through `π` on the states satisfying
`Inv`, the values of the two runs read through decisions that agree through `π` have equal
runs. -/
theorem run₂_map_kRunQ_sim (Rt : QuantumRuntime W.spec) {St₂ : Type} (K₁ : Kernel R St)
    (K₂ : Kernel R St₂) (Inv : St₂ → Prop) (π : St₂ → St)
    (hK : ∀ s, Inv s → ∀ q, Prod.map id π <$> K₂ s q = K₁ (π s) q)
    (hInv : ∀ s, Inv s → ∀ q, ∀ p ∈ support (K₂ s q), Inv p.2) {A B : QReg} {α γ : Type}
    (x : QComp (advSpec W.spec R) A B α) (s : St₂) (hs : Inv s) (d₁ : α × St → γ)
    (d₂ : α × St₂ → γ) (hd : ∀ a s, Inv s → d₂ (a, s) = d₁ (a, π s)) :
    Rt.run₂ .instruments ((kRunQ W K₂ x s).map d₂) =
      Rt.run₂ .instruments ((kRunQ W K₁ x (π s)).map d₁) := by
  have e₁ := imap_kRun W K₁ (X := QuantumComp₂.Leaf B α) (fun _ l s ↦ ⟨l.1, (l.2, s)⟩) d₁ x
    (π s)
  have e₂ := imap_kRun W K₂ (X := QuantumComp₂.Leaf B α) (fun _ l s ↦ ⟨l.1, (l.2, s)⟩) d₂ x s
  refine (congrArg (Rt.run₂ .instruments) e₂).trans (Eq.trans ?_
    (congrArg (Rt.run₂ .instruments) e₁).symm)
  refine congrArg (fun d ↦ d.comap (QuantumComp₂.leafEquiv B γ)
    (QuantumComp₂.leafEquiv B γ).injective) (?_ : Rt.run .instruments _ = Rt.run .instruments _)
  exact run_kRun_sim Rt K₁ K₂ Inv π hK hInv _ _
    (fun s hs u l ↦ by simp only [hd l.2 s hs]) x s hs

variable {W} in
/-- The run of a reduction against a challenger, fixed-register form. -/
theorem run₂_answered_withCallLogFrom_runHQ (tab : W.Tab)
    (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q')) (σ : HHandler W R R' St)
    {A B : QReg} {α : Type} (x : QComp (advSpec W.spec R) A B α) (s : St)
    (log : QueryLog R') :
    (W.runtime tab).run₂ .instruments (answered W ans (withCallLogFrom log (runHQ W σ x s))) =
      (W.runtime tab).run₂ .instruments (kRunL W (hKernel tab ans σ) x s log) :=
  congrArg (fun d ↦ d.comap (QuantumComp₂.leafEquiv B ((α × St) × QueryLog R'))
    (QuantumComp₂.leafEquiv B _).injective) (run_answered_logCalls_runH tab ans σ _ _ x s log)

/-- **A straight-line reduction**: a classical setup `pre`, the adversary `adv` run once with
its classical calls answered by the handler `σ` from the state `st0`, then a classical output
`post` from the forgery and the final state. Every classical algorithm may do honest work
through the world's oracles. -/
noncomputable def slRed {S0 F Out : Type} (pre : OracleComp (W.Oracles + R') S0)
    (adv : S0 → QComp (advSpec W.spec R) (QReg.of Unit) (QReg.of Unit) F) (st0 : S0 → St)
    (σ : HHandler W R R' St) (post : S0 → F → St → OracleComp (W.Oracles + R') Out) :
    QComp (advSpec W.spec R') (QReg.of Unit) (QReg.of Unit) Out :=
  QuantumComp₂.bind (pre.toQuantumAt (hcallImpl W R' _)) fun a ↦
    QuantumComp₂.bind (runHQ W σ (adv a) (st0 a)) fun r ↦
      (post a r.1 r.2).toQuantumAt (hcallImpl W R' _)

variable {W} in
/-- The normal form of a straight-line reduction against a challenger at a fixed table: the
setup's sampler, the canonical run, the output's sampler. -/
noncomputable def slNormal (tab : W.Tab) (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q'))
    {S0 F Out : Type} (pre : OracleComp (W.Oracles + R') S0)
    (adv : S0 → QComp (advSpec W.spec R) (QReg.of Unit) (QReg.of Unit) F) (st0 : S0 → St)
    (σ : HHandler W R R' St) (post : S0 → F → St → OracleComp (W.Oracles + R') Out) :
    QComp W.spec (QReg.of Unit) (QReg.of Unit) (Out × QueryLog R') :=
  QuantumComp₂.bind (((simulateQ (logImpl tab ans) pre).run []).toQuantumAt
    (QComp.coinImpl W.spec _)) fun p ↦
    QuantumComp₂.bind (kRunL W (hKernel tab ans σ) (adv p.1) (st0 p.1) p.2) fun r ↦
      ((simulateQ (logImpl tab ans) (post p.1 r.1.1 r.1.2)).run r.2).toQuantumAt
        (QComp.coinImpl W.spec _)

variable {W} in
/-- **A straight-line reduction against a challenger at a fixed table**, with its transcript,
runs as its normal form. -/
theorem run₂_answered_withCallLog_slRed (tab : W.Tab)
    (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q')) {S0 F Out : Type}
    (pre : OracleComp (W.Oracles + R') S0)
    (adv : S0 → QComp (advSpec W.spec R) (QReg.of Unit) (QReg.of Unit) F) (st0 : S0 → St)
    (σ : HHandler W R R' St) (post : S0 → F → St → OracleComp (W.Oracles + R') Out) :
    (W.runtime tab).run₂ .instruments (answered W ans (withCallLog (slRed W pre adv st0 σ post))) =
      (W.runtime tab).run₂ .instruments (slNormal tab ans pre adv st0 σ post) := by
  rw [show withCallLog (slRed W pre adv st0 σ post) =
    withCallLogFrom [] (slRed W pre adv st0 σ post) from rfl, slRed, withCallLogFrom_bind,
    answered_bind]
  refine run₂_bind_congr (run₂_eq_of_classicalOn (classicalOn_answered_hcall tab ans pre [])
    (classicalOn_coinImpl_toQuantumAt _ _)) fun p ↦ ?_
  rw [withCallLogFrom_bind, answered_bind]
  exact run₂_bind_congr (run₂_answered_withCallLogFrom_runHQ tab ans σ (adv p.1) (st0 p.1) p.2)
    fun r ↦ run₂_eq_of_classicalOn (classicalOn_answered_hcall tab ans _ _)
      (classicalOn_coinImpl_toQuantumAt _ _)

variable {W} in
/-- **A property game of a straight-line reduction at a fixed table**: the challenger's setup,
the reduction in normal form, the challenger's decision, all classical but the canonical run. -/
theorem run₂_game_slRed (tab : W.Tab) {Pub Out : Type} (E : Experiment W R' Pub Out)
    {S0 F : Type} (pre : Pub → OracleComp (W.Oracles + R') S0)
    (adv : Pub → S0 → QComp (advSpec W.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Pub → S0 → St) (σ : Pub → HHandler W R R' St)
    (post : Pub → S0 → F → St → OracleComp (W.Oracles + R') Out) :
    (W.runtime tab).run₂ .instruments
        (E.game fun p ↦ slRed W (pre p) (adv p) (st0 p) (σ p) (post p)) =
      (W.runtime tab).run₂ .instruments
        (QuantumComp₂.bind ((simulateQ (W.eager tab) E.setup).toQuantumAt
          (QComp.coinImpl W.spec _)) fun s ↦
          QuantumComp₂.bind (slNormal tab (E.answer s) (pre (E.pub s)) (adv (E.pub s))
            (st0 (E.pub s)) (σ (E.pub s)) (post (E.pub s))) fun r ↦
            (simulateQ (W.eager tab) (E.judge s r.2 r.1)).toQuantumAt
              (QComp.coinImpl W.spec _)) := by
  refine run₂_bind_congr (run₂_eq_of_classicalOn (W.classicalOn_toQuantumAt tab _ E.setup)
    (classicalOn_coinImpl_toQuantumAt _ _)) fun s ↦ ?_
  refine run₂_bind_congr (run₂_answered_withCallLog_slRed tab (E.answer s) _ _ _ _ _) fun r ↦ ?_
  exact run₂_eq_of_classicalOn (W.classicalOn_toQuantumAt tab _ _)
    (classicalOn_coinImpl_toQuantumAt _ _)

variable {W} in
/-- **The SUF-CMA game at a fixed table** in normal form: key generation, the canonical run
against the signer's kernel, verification. -/
theorem run₂_sufGame {PK Req Resp F Seed SK : Type}
    (sch : Qrom.SchemeOver W.Oracles Seed PK SK Req Resp F) (tab : W.Tab) (S0 : Seed)
    (A : SufAdversary W PK Req Resp F) :
    (W.runtime tab).run₂ .instruments (game W sch S0 A) =
      (W.runtime tab).run₂ .instruments
        (((simulateQ (W.eager tab) (sch.generateKeys S0)).toQuantumAt
          (QComp.coinImpl W.spec _)).bind fun keys ↦
          (kRunQ W (signKernel W sch keys.2 tab) (A keys.1) []).bind fun run ↦
            ((simulateQ (W.eager tab) (sch.verify keys.1 run.1)).toQuantumAt
              (QComp.coinImpl W.spec _)).bind fun verified ↦
              QuantumComp₂.pure (sch.winningCondition run.2 run.1 && verified)) := by
  refine run₂_bind_congr (run₂_eq_of_classicalOn (W.classicalOn_toQuantumAt tab _ _)
    (classicalOn_coinImpl_toQuantumAt _ _)) fun keys ↦ ?_
  refine run₂_bind_congr (run₂_challenged_withCallLog sch keys.2 tab (A keys.1)) fun run ↦ ?_
  exact run₂_bind_congr (run₂_eq_of_classicalOn (W.classicalOn_toQuantumAt tab _ _)
    (classicalOn_coinImpl_toQuantumAt _ _)) fun _ ↦ rfl

/-- **A straight-line reduction's hash calls**: `A`'s hash calls, plus the honest work of its
setup (`c₀`), of each handler (`k` per classical call of `A`) and of its output (`c₁`). -/
theorem isChargeBound_slRed_hash {S0 F Out : Type} (pre : OracleComp (W.Oracles + R') S0)
    (adv : S0 → QComp (advSpec W.spec R) (QReg.of Unit) (QReg.of Unit) F) (st0 : S0 → St)
    (σ : HHandler W R R' St) (post : S0 → F → St → OracleComp (W.Oracles + R') Out)
    {c₀ c₁ k n m : ℕ} (hpre : QueryCostAtMost pre (hcallCost W (R' := R')) c₀)
    (hσ : ∀ s q, QueryCostAtMost (σ s q) (hcallCost W (R' := R')) k)
    (hpost : ∀ a f s, QueryCostAtMost (post a f s) (hcallCost W (R' := R')) c₁)
    (hn : ∀ a, IFreeM.IsChargeBound (adv a) (cmdCharge hashCharge) n)
    (hm : ∀ a, IFreeM.IsChargeBound (adv a) (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (slRed W pre adv st0 σ post) (cmdCharge hashCharge)
      (c₀ + ((n + k * m) + c₁)) :=
  FreeM₂.isChargeBound_bind (isChargeBound_toQuantumAt_hcallImpl W _ hpre) fun a ↦
    FreeM₂.isChargeBound_bind (x := runHQ W σ (adv a) (st0 a))
      (isChargeBound_runH_hash W σ _ hσ (adv a) (st0 a)
        (isChargeBound_srcCharge W (adv a) k (hn a) (hm a))) fun (r : F × St) ↦
      isChargeBound_toQuantumAt_hcallImpl W _ (hpost a r.1 r.2)

end Normal

end Quantum.StdModel

end
