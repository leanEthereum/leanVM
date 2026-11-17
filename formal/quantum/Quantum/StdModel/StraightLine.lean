module

public import Quantum.StdModel.World

@[expose] public section

/-!
# Straight-line reductions: classical answers to an adversary's classical ports

A reduction `B` runs the adversary `A` once, forwarding every hash call unchanged and answering
every classical call `q` of `A` by classical code: a handler `σ s q`, from the handler's state
`s`, an algorithm over coins and `B`'s own classical ports `R'` returning the answer and the next
state (`Handler`). `runCalls σ leaf x s` is the program `B`: one structural pass over `A`'s
program `x`, each command of `x` kept in order, a classical call replaced by the handler run by
classical calls of `B`'s ports (`answerTree`), the final state handed to `leaf`. Nothing is
copied, rewound or measured beyond `A`'s own classical results. A stateless handler is a
`CommandSubstitution` (`callSubst`).

## Main statements

* `isChargeBound_runCalls`: `B` makes, under any charge `c` of its ports, at most `n` when `A`
  makes at most `n` under the charge `c` on hash ports and `k` per classical call, every handler
  costing at most `k`.
* `isChargeBound_runCalls_hash`: **`B` keeps `A`'s hash-call charge**: the hash ports of `B` are
  called exactly where `A` calls them.
* `isChargeBound_runCalls_call`: `B`'s classical calls: at most `k * n` when `A` makes at most
  `n` classical calls and each handler makes at most `k`.
* `lossless_runCalls`: `B` of a lossless `A` is lossless.
* `isChargeBound_substitute_callSubst_hash`, `isChargeBound_substitute_callSubst_call`: the same
  for stateless handlers.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

namespace Quantum.StdModel

open Common

variable {spec : QuantumOracleSpec.{0, 0}} {Q Q' : Type} {R : OracleSpec.{0, 0} Q}
  {R' : OracleSpec.{0, 0} Q'}

/-! ## Classical calls of `B`'s ports -/

variable (spec R') in
/-- `B`'s coins and classical queries beside a held register `B`: coins by uniform coins, a query
`q'` by the call of the classical port `q'`. -/
noncomputable def callImpl (B : QReg) : QueryImpl (unifSpec + R') (QComp (advSpec spec R') B B)
  | .inl n => QComp.coinImpl (advSpec spec R') B n
  | .inr q' => QComp.callBasis (spec := advSpec spec R') (.call q') B () fun _ r ↦ r

/-- The charge of `B`'s classical queries under a charge `c` of its ports: coins free, `q'` at
`c (.call q')`. -/
def callCost {P : Type} (c : Port P Q' → ℕ) : ℕ ⊕ Q' → ℕ
  | .inl _ => 0
  | .inr q' => c (.call q')

/-- Every algorithm costs nothing under the zero cost. -/
theorem queryCostAtMost_zero {ι : Type} {O : OracleSpec.{0, 0} ι} {α : Type}
    (oa : OracleComp O α) : QueryCostAtMost oa (fun _ ↦ 0) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff]
    exact ⟨le_rfl, fun u ↦ ih u⟩

theorem lossless_callImpl (B : QReg) (t : (unifSpec + R').Domain) :
    (callImpl spec R' B t).Lossless .instruments := by
  rcases t with n | q'
  exacts [QComp.lossless_coinImpl n, QComp.lossless_callBasis _ _ _ _]

section Charge

variable {S : QuantumOracleSpec.{0, 0}} {QS : Type} {RS : OracleSpec.{0, 0} QS}

/-- A local subinstrument is free. -/
theorem isChargeBound_act {A B : QReg} {α : Type} (c : Port S.Port QS → ℕ)
    (p : SubInstrument A B α) (n : ℕ) :
    IFreeM.IsChargeBound (QComp.act (spec := advSpec S RS) p) (cmdCharge c) n :=
  (IFreeM.isChargeBound_liftBind_iff _ _ n).mpr ⟨Nat.zero_le n, fun _ ↦ trivial⟩

/-- A call of port `i` costs `c i`. -/
theorem isChargeBound_query₂ {A : QReg} (c : Port S.Port QS → ℕ) (i : Port S.Port QS)
    (E : QReg) (ℓ : A ≃ (advSpec S RS).In i × E) :
    IFreeM.IsChargeBound (QuantumComp₂.query (L := LocalSig.instruments.{0}) i E ℓ)
      (cmdCharge c) (c i) :=
  (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_refl _, fun _ ↦ trivial⟩

/-- A basis call of port `i` costs `c i`. -/
theorem isChargeBound_callBasis {β : Type} (c : Port S.Port QS → ℕ) (i : Port S.Port QS)
    (B : QReg) (a : (advSpec S RS).In i)
    (read : (advSpec S RS).Out i → (advSpec S RS).Result i → β) :
    IFreeM.IsChargeBound (QComp.callBasis i B a read) (cmdCharge c) (c i) := by
  unfold QComp.callBasis
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := c i + 0)
    (isChargeBound_act c _ 0) fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := c i) (n₂ := 0)
      (isChargeBound_query₂ c _ _ _) fun _ ↦ isChargeBound_act c _ 0) (by omega)

end Charge

/-- Each classical query of `B` costs its `callCost`. -/
theorem isChargeBound_callImpl (c : Port spec.Port Q' → ℕ) (B : QReg)
    (t : (unifSpec + R').Domain) :
    IFreeM.IsChargeBound (callImpl spec R' B t) (cmdCharge c) (callCost c t) := by
  rcases t with n | q'
  · exact isChargeBound_act c _ _
  · exact isChargeBound_callBasis c _ _ _ _

/-- **A classical algorithm of `B` costing at most `n`** runs to a program of charge at most
`n`. -/
theorem isChargeBound_toQuantumAt_callImpl (c : Port spec.Port Q' → ℕ) (B : QReg) {α : Type}
    {oa : OracleComp (unifSpec + R') α} {n : ℕ} (h : QueryCostAtMost oa (callCost c) n) :
    IFreeM.IsChargeBound (oa.toQuantumAt (callImpl spec R' B)) (cmdCharge c) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h
    rw [toQuantumAt_query_bind]
    have hb := FreeM₂.isChargeBound_bind (isChargeBound_callImpl c B t) fun y ↦ ih y (h.2 y)
    rwa [Nat.add_sub_cancel' h.1] at hb

/-! ## Stateful handlers -/

variable (R R') in
/-- **A classical handler** with state `St`: from the state `s` and `A`'s classical query `q`, an
algorithm over coins and `B`'s classical ports returning the answer and the next state. -/
abbrev Handler (St : Type) := St → (q : Q) → OracleComp (unifSpec + R') (R.Range q × St)

variable {St : Type}

/-- The answer to `A`'s classical call `q` with `A`'s register `A ≃ Unit × E` held: relabel the
register, then run the handler by classical calls. -/
noncomputable def answerTree (σ : Handler R R' St) (s : St) (q : Q) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec spec R).In (.call q) × E) :
    QComp (advSpec spec R') A (QReg.of ((advSpec spec R).Out (.call q) × E)) (R.Range q × St) :=
  (QComp.act (B := QReg.of ((advSpec spec R).Out (.call q) × E)) (SubInstrument.relabel ℓ)).bind
    fun _ ↦ (σ s q).toQuantumAt (callImpl spec R' _)

/-- **The straight-line reduction**: `A`'s program `x` from the handler state `s`, every local
operation and hash call kept, every classical call answered by the handler (`answerTree`), the
leaf and the final state handed to `leaf`. -/
noncomputable def runCalls {X Y : QReg → Type} (σ : Handler R R' St)
    (leaf : ∀ u, X u → St → Y u) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec spec R)) X A →
      St → IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec spec R')) Y A
  | _, .pure x, s => .pure (leaf _ x s)
  | _, .liftBind (.prim o) next, s => .liftBind (.prim o) fun b ↦ runCalls σ leaf (next b) s
  | _, .liftBind (.query (.hash p) E ℓ) next, s =>
      .liftBind (.query (.hash p) E ℓ) fun b ↦ runCalls σ leaf (next b) s
  | _, .liftBind (.query (.call q) E ℓ) next, s =>
      QuantumComp.bind (answerTree σ s q E ℓ) fun _ l ↦
        l.1 ▸ runCalls σ leaf (next ⟨l.2.1⟩) l.2.2

variable {X Y : QReg → Type} (σ : Handler R R' St) (leaf : ∀ u, X u → St → Y u)

/-- The charge of `A`'s ports matching the charge `c` of `B`'s: `c` on hash ports, `k` per
classical call. -/
def srcCharge (c : Port spec.Port Q' → ℕ) (k : ℕ) : Port spec.Port Q → ℕ
  | .hash p => c (.hash p)
  | .call _ => k

/-- **`B`'s charge.** If every handler costs at most `k` under the charge `c` of `B`'s ports and
`A` is within `n` under `c` on hash ports and `k` per classical call, then `B` is within `n`. -/
theorem isChargeBound_runCalls (c : Port spec.Port Q' → ℕ) {k : ℕ}
    (hσ : ∀ s q, QueryCostAtMost (σ s q) (callCost c) k) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec spec R)) X A)
    (s : St) {n : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge (srcCharge c k)) n) :
    IFreeM.IsChargeBound (runCalls σ leaf x s) (cmdCharge c) n := by
  induction x using IFreeM.inductionOn generalizing s n with
  | pure _ _ => trivial
  | liftBind A cmd next ih =>
    replace hx := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hx
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨hx.1, fun b ↦ ih b s (hx.2 b)⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨hx.1, fun b ↦ ih b s (hx.2 b)⟩
    · have ht : IFreeM.IsChargeBound (answerTree σ s q E ℓ) (cmdCharge c) (0 + k) :=
        FreeM₂.isChargeBound_bind (isChargeBound_act c _ 0) fun _ ↦
          isChargeBound_toQuantumAt_callImpl c _ (hσ s q)
      have hk : k ≤ n := hx.1
      rw [runCalls]
      refine (IFreeM.isChargeBound_bind (n₂ := n - k) ht fun u l ↦ ?_).mono (by omega)
      obtain ⟨rfl, v⟩ := l
      exact ih ⟨v.1⟩ v.2 (hx.2 ⟨v.1⟩)

/-- **`B` keeps `A`'s hash charge**: the handlers call no hash port, and `B` calls the hash ports
where `A` does. -/
theorem isChargeBound_runCalls_hash {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec spec R)) X A)
    (s : St) {n : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge hashCharge) n) :
    IFreeM.IsChargeBound (runCalls σ leaf x s) (cmdCharge hashCharge) n := by
  have hc : callCost (hashCharge (P := spec.Port) (Q := Q')) = fun _ ↦ 0 := by
    funext t
    rcases t with _ | _ <;> rfl
  have hs : srcCharge (Q := Q) (hashCharge (P := spec.Port) (Q := Q')) 0 = hashCharge := by
    funext i
    rcases i with _ | _ <;> rfl
  refine isChargeBound_runCalls σ leaf hashCharge (k := 0) (fun s q ↦ ?_) x s ?_
  · rw [hc]
    exact queryCostAtMost_zero _
  · rwa [hs]

/-- **`B`'s classical calls**: at most `k * n` when `A` makes at most `n` classical calls and
every handler at most `k`. -/
theorem isChargeBound_runCalls_call {k : ℕ}
    (hσ : ∀ s q, QueryCostAtMost (σ s q) (callCost (callCharge (P := spec.Port))) k)
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec spec R)) X A)
    (s : St) {n : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge callCharge) n) :
    IFreeM.IsChargeBound (runCalls σ leaf x s) (cmdCharge callCharge) (k * n) := by
  have hs : (fun A a ↦ k * cmdCharge (L := LocalSig.instruments.{0}) (R := R)
      (callCharge (P := spec.Port)) A a) =
      cmdCharge (srcCharge (callCharge (P := spec.Port) (Q := Q')) k) := by
    funext A a
    rcases a with o | ⟨_ | _, E, ℓ⟩
    · exact Nat.mul_zero k
    · exact Nat.mul_zero k
    · exact Nat.mul_one k
  refine isChargeBound_runCalls σ leaf callCharge hσ x s ?_
  rw [← hs]
  exact hx.mul k

/-- **`B` of a lossless `A` is lossless.** -/
theorem lossless_runCalls {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (advSpec spec R) X A) (s : St)
    (hx : x.Lossless .instruments) :
    QuantumComp.Lossless (spec := advSpec spec R') LocalSig.Interp.instruments
      (runCalls σ leaf x s) := by
  induction x using IFreeM.inductionOn generalizing s with
  | pure _ _ => trivial
  | liftBind A cmd next ih =>
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact ⟨hx.1, fun b ↦ ih b s (hx.2 b)⟩
    · exact ⟨hx.1, fun b ↦ ih b s (hx.2 b)⟩
    · refine QuantumComp.Lossless.bind ?_ fun u l ↦ ?_
      · exact QuantumComp₂.lossless_bind (QComp.lossless_act (SubInstrument.lossless_relabel _))
          fun _ ↦ lossless_toQuantumAt (lossless_callImpl _) _
      · obtain ⟨rfl, v⟩ := l
        exact ih ⟨v.1⟩ v.2 (hx.2 ⟨v.1⟩)

/-! ## Stateless handlers -/

/-- **A stateless handler as a command substitution**: local operations and hash calls kept,
the classical call `q` answered by `τ q` run by classical calls of `B`'s ports. -/
noncomputable def callSubst (τ : (q : Q) → OracleComp (unifSpec + R') (R.Range q)) :
    CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec spec R))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec spec R'))
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query (.hash p) E ℓ =>
      QuantumComp.queryBind (spec := advSpec spec R') (.hash p) E ℓ fun r ↦
        QuantumComp.pure ⟨ULift.up r, rfl⟩
  | _, .query (.call q) E ℓ =>
      QuantumComp.bind
        ((QComp.act (B := QReg.of ((advSpec spec R).Out (.call q) × E))
          (SubInstrument.relabel ℓ)).bind fun _ ↦ (τ q).toQuantumAt (callImpl spec R' _))
        fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- Each command of `A` is replaced within its charge, when every handler costs at most `k`. -/
theorem isChargeBound_callSubst (τ : (q : Q) → OracleComp (unifSpec + R') (R.Range q))
    (c : Port spec.Port Q' → ℕ) {k : ℕ} (hτ : ∀ q, QueryCostAtMost (τ q) (callCost c) k)
    (A : QReg) (cmd : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec spec R) A) :
    IFreeM.IsChargeBound (callSubst τ A cmd) (cmdCharge c) (cmdCharge (srcCharge c k) A cmd) := by
  rcases cmd with o | ⟨p | q, E, ℓ⟩
  · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨Nat.zero_le _, fun _ ↦ trivial⟩
  · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_refl _, fun _ ↦ trivial⟩
  · have ht := FreeM₂.isChargeBound_bind (isChargeBound_act c
      (SubInstrument.relabel (B := QReg.of ((advSpec spec R).Out (.call q) × E)) ℓ) 0)
      fun _ ↦ isChargeBound_toQuantumAt_callImpl c _ (hτ q)
    refine (IFreeM.isChargeBound_bind ht fun _ _ ↦ IFreeM.isChargeBound_pure _ 0).mono ?_
    change 0 + k + 0 ≤ k
    omega

/-- **A stateless reduction keeps `A`'s hash charge.** -/
theorem isChargeBound_substitute_callSubst_hash
    (τ : (q : Q) → OracleComp (unifSpec + R') (R.Range q)) {A : QReg}
    {x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec spec R)) X A}
    {n : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge hashCharge) n) :
    IFreeM.IsChargeBound (IFreeM.substitute (callSubst τ) x) (cmdCharge hashCharge) n := by
  have hc : callCost (hashCharge (P := spec.Port) (Q := Q')) = fun _ ↦ 0 := by
    funext t
    rcases t with _ | _ <;> rfl
  have hs : srcCharge (Q := Q) (hashCharge (P := spec.Port) (Q := Q')) 0 = hashCharge := by
    funext i
    rcases i with _ | _ <;> rfl
  refine IFreeM.IsChargeBound.substitute (callSubst τ) (fun A cmd ↦ ?_) hx
  have h := isChargeBound_callSubst τ hashCharge (k := 0)
    (fun q ↦ by rw [hc]; exact queryCostAtMost_zero _) A cmd
  rwa [hs] at h

/-- **A stateless reduction's classical calls**: at most `k * n`. -/
theorem isChargeBound_substitute_callSubst_call
    (τ : (q : Q) → OracleComp (unifSpec + R') (R.Range q)) {k : ℕ}
    (hτ : ∀ q, QueryCostAtMost (τ q) (callCost (callCharge (P := spec.Port))) k)
    {A : QReg}
    {x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec spec R)) X A}
    {n : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge callCharge) n) :
    IFreeM.IsChargeBound (IFreeM.substitute (callSubst τ) x) (cmdCharge callCharge) (k * n) := by
  refine IFreeM.IsChargeBound.substitute_mul (callSubst τ) k (fun A cmd ↦ ?_) hx
  refine (isChargeBound_callSubst τ callCharge hτ A cmd).mono ?_
  rcases cmd with o | ⟨_ | _, E, ℓ⟩
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact (Nat.mul_one k).ge

end Quantum.StdModel

end
