import Rv64Verifier.Model.Transcript
import Rv64Verifier.Model.Multilinear
import Rv64Verifier.Model.FieldAlg

/-!
# The sumcheck and the bus, as the Rust runs them

Mirrors of `crates/verifier/src/transcript.rs`'s `sumcheck_round_poly` and `sumcheck`, and of
`crates/verifier/src/bus.rs`, in `TM`, each with a `Sim` against the statement's program.
-/

namespace Rv64Verifier.Model
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier

/-! ## Generic lemmas -/

theorem VerifierProgram.bind_assoc {α β γ : Type} (P : VerifierProgram α)
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

theorem VerifierProgram.bind_ret {α : Type} (P : VerifierProgram α) :
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

theorem VerifierProgram.ret_bind {α β : Type} (a : α) (f : α → VerifierProgram β) :
    (VerifierProgram.ret a >>= f) = f a := rfl

theorem Sim.requireIff {c c' : Prop} [Decidable c] [Decidable c'] (h : c ↔ c') :
    Sim (TM.require c) (VerifierProgram.require c') := by
  intro t a t' hr
  simp only [TM.require, StateT.run] at hr
  split_ifs at hr with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨-, rfl⟩ := hr
  simp only [VerifierProgram.require, h.mp hc, ↓reduceIte]
  rfl

/-- What a mirror returns satisfies `R`. -/
def Returns {α : Type} (m : TM α) (R : α → Prop) : Prop :=
  ∀ t a t', m.run t = some (a, t') → R a

theorem Sim.bindPost {α β : Type} {m : TM α} {P : VerifierProgram α} {k : α → TM β}
    {Q : α → VerifierProgram β} {R : α → Prop} (hm : Sim m P) (hR : Returns m R)
    (hk : ∀ a, R a → Sim (k a) (Q a)) : Sim (m >>= k) (P >>= Q) := by
  intro t b t' h
  rw [StateT.run_bind] at h
  cases hmt : m.run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨a, t₁⟩ := p
    rw [hmt] at h
    rw [runK_bind, hm t a t₁ hmt]
    exact hk a (hR t a t₁ hmt) t₁ b t' h

theorem Sim.congr {α : Type} {m : TM α} {P P' : VerifierProgram α} (h : P = P') (hm : Sim m P') :
    Sim m P := h ▸ hm

theorem Returns.pure {α : Type} {R : α → Prop} {a : α} (h : R a) :
    Returns (Pure.pure a : TM α) R := by
  intro t b t' hr
  cases (Option.some.inj hr : ((a, t) : α × TState) = (b, t'))
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

namespace TM

/-- A pure `Result` step, `?`: fail on `none`. -/
def lift {α : Type} (o : Option α) : TM α := fun t ↦ o.map (·, t)

end TM

theorem Sim.liftBind {α β : Type} {o : Option α} {k : α → TM β} {Q : VerifierProgram β}
    (h : ∀ a, o = some a → Sim (k a) Q) : Sim (TM.lift o >>= k) Q := by
  intro t b t' hr
  rw [StateT.run_bind] at hr
  cases ho : o with
  | none => simp [ho, TM.lift, StateT.run] at hr
  | some a =>
    simp only [ho, TM.lift, StateT.run, Option.map_some] at hr
    exact h a ho t b t' hr

theorem Sim.lift {α : Type} {o : Option α} {P : VerifierProgram α}
    (h : ∀ a, o = some a → ∀ σ, runK P σ = some (a, σ)) : Sim (TM.lift o) P := by
  intro t a t' hr
  cases ho : o with
  | none => simp [ho, TM.lift, StateT.run] at hr
  | some b =>
    simp only [ho, TM.lift, StateT.run, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact h b ho _

/-- `m` runs `P`, its value standing for `P`'s through `f`. -/
def SimR {α β : Type} (m : TM α) (P : VerifierProgram β) (f : α → β) : Prop :=
  ∀ t a t', m.run t = some (a, t') → runK P t.toSpec = some (f a, t'.toSpec)

theorem SimR.sim {α β : Type} {m : TM α} {P : VerifierProgram β} {f : α → β} (h : SimR m P f) :
    Sim (f <$> m) P := by
  intro t b t' hr
  rw [StateT.run_map] at hr
  cases hmt : m.run t with
  | none => simp [hmt] at hr
  | some p =>
    obtain ⟨a, t₁⟩ := p
    simp only [hmt, Option.map_eq_map, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact h t a t₁ hmt

theorem SimR.pure {α β : Type} {f : α → β} {a : α} {b : β} (h : f a = b) :
    SimR (Pure.pure a : TM α) (VerifierProgram.ret b) f := by
  intro t c t' hr
  cases (Option.some.inj hr : ((a, t) : α × TState) = (c, t'))
  rw [h]
  rfl

theorem SimR.bindPost {α β γ : Type} {m : TM α} {P : VerifierProgram α} {k : α → TM β}
    {Q : α → VerifierProgram γ} {f : β → γ} {R : α → Prop} (hm : Sim m P) (hR : Returns m R)
    (hk : ∀ a, R a → SimR (k a) (Q a) f) : SimR (m >>= k) (P >>= Q) f := by
  intro t b t' h
  rw [StateT.run_bind] at h
  cases hmt : m.run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨a, t₁⟩ := p
    rw [hmt] at h
    rw [runK_bind, hm t a t₁ hmt]
    exact hk a (hR t a t₁ hmt) t₁ b t' h

theorem SimR.bind {α β γ : Type} {m : TM α} {P : VerifierProgram α} {k : α → TM β}
    {Q : α → VerifierProgram γ} {f : β → γ} (hm : Sim m P) (hk : ∀ a, SimR (k a) (Q a) f) :
    SimR (m >>= k) (P >>= Q) f :=
  SimR.bindPost hm (Returns.true m) fun a _ ↦ hk a

theorem Returns.nextScalars : ∀ n, Returns (TM.nextScalars n) fun xs ↦ xs.length = n
  | 0 => Returns.pure rfl
  | n + 1 => Returns.bind (Returns.true _) fun x _ ↦ Returns.bind (Returns.nextScalars n)
      fun xs hxs ↦ Returns.pure (by simp [hxs])

theorem Returns.samples : ∀ n, Returns (TM.samples n) fun xs ↦ xs.length = n
  | 0 => Returns.pure rfl
  | n + 1 => Returns.bind (Returns.true _) fun x _ ↦ Returns.bind (Returns.samples n)
      fun xs hxs ↦ Returns.pure (by simp [hxs])

/-! ## `sumcheck_round_poly`, `sumcheck` (`transcript.rs`) -/

/-- `Transcript::sumcheck_round_poly(count, claim, eq_factor)`. Every caller passes `count ≥ 3`, so
`count - 2` does not wrap. -/
def sumcheckRoundPolyM (count : ℕ) (claim : E) : Option E → TM (List E)
  | none => do
    let constant ← TM.nextScalar
    let tail ← TM.nextScalars (count - 2)
    pure ([constant, claim + sumE tail] ++ tail)
  | some eqFactor => do
    let tail ← TM.nextScalars (count - 1)
    pure ([claim + eqFactor * sumE tail] ++ tail)

/-- `sumcheck`'s loop over `equalities`, from the point pushed so far and the running claim. -/
def sumcheckLoop (count : ℕ) : List (Option E) → List E → E → TM (List E × E)
  | [], point, claim => pure (point, claim)
  | equality :: equalities, point, claim => do
    let message ← sumcheckRoundPolyM count claim equality
    let challenge ← TM.sample
    sumcheckLoop count equalities (point ++ [challenge]) (polyEvalRust message challenge)

/-- `sumcheck(transcript, claim, count, equalities)`. -/
def sumcheckM (claim : E) (count : ℕ) (equalities : List (Option E)) : TM (List E × E) :=
  sumcheckLoop count equalities [] claim

theorem Sim.sumcheckRoundPoly (count : ℕ) (claim : E) (equality : Option E) :
    Sim (sumcheckRoundPolyM count claim equality) (sumcheckRoundPoly count claim equality) := by
  cases equality with
  | none =>
    exact Sim.bind Sim.nextScalar fun _ ↦ Sim.bind (Sim.nextScalars _) fun _ ↦ Sim.pure _
  | some r => exact Sim.bind (Sim.nextScalars _) fun _ ↦ Sim.pure _

theorem Sim.sumcheckLoop (count : ℕ) :
    ∀ (equalities : List (Option E)) (point : List E) (claim : E),
    Sim (sumcheckLoop count equalities point claim)
      (sumcheck claim count equalities >>= fun r ↦ VerifierProgram.ret (point ++ r.1, r.2))
  | [], point, claim => by
    show Sim (Pure.pure (point, claim)) (VerifierProgram.ret (point ++ [], claim))
    rw [List.append_nil]
    exact Sim.pure _
  | equality :: equalities, point, claim => by
    simp only [Model.sumcheckLoop, sumcheck, VerifierProgram.bind_assoc]
    refine Sim.bind (Sim.sumcheckRoundPoly _ _ _) fun message ↦ Sim.bind Sim.sample fun c ↦ ?_
    have := Sim.sumcheckLoop count equalities (point ++ [c]) (polyEvalRust message c)
    rw [polyEvalRust_eq] at this ⊢
    refine Sim.congr ?_ this
    congr 1
    funext r
    simp only [List.append_assoc, List.singleton_append]
    rfl

theorem Sim.sumcheck (claim : E) (count : ℕ) (equalities : List (Option E)) :
    Sim (sumcheckM claim count equalities) (sumcheck claim count equalities) := by
  have := Sim.sumcheckLoop count equalities [] claim
  simp only [List.nil_append] at this
  exact Sim.congr (VerifierProgram.bind_ret _).symm this

theorem Returns.sumcheckLoop (count : ℕ) : ∀ (equalities : List (Option E)) (point : List E)
    (claim : E), Returns (sumcheckLoop count equalities point claim)
      fun r ↦ r.1.length = point.length + equalities.length
  | [], point, claim => Returns.pure rfl
  | _ :: equalities, point, _ => Returns.bind (Returns.true _) fun _ _ ↦
      Returns.bind (Returns.true _) fun _ _ ↦ by
        refine fun t a t' h ↦ (Returns.sumcheckLoop count equalities _ _ t a t' h).trans ?_
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega

theorem Returns.sumcheck (claim : E) (count : ℕ) (equalities : List (Option E)) :
    Returns (sumcheckM claim count equalities) fun r ↦ r.1.length = equalities.length := by
  intro t a t' h
  have := Returns.sumcheckLoop count equalities [] claim t a t' h
  simpa using this

/-! ## `verify_gkr_grand_products` (`bus.rs`) -/

/-- One iteration of `verify_gkr_grand_products`' loop, over `step` levels. -/
def gkrStepM (step : ℕ) (state : GkrState) : TM GkrState := do
  let combiner ← TM.sample
  let claim := polyEvalRust state.values combiner
  let equalities := state.point.map some
  let (x, claim) ← sumcheckM claim ((1 <<< step) + 1) equalities
  let child0 ← TM.nextScalars (1 <<< step)
  let child1 ← TM.nextScalars (1 <<< step)
  let child2 ← TM.nextScalars (1 <<< step)
  let children := [child0, child1, child2]
  let products := children.map fun child ↦ child.foldl (fun acc value ↦ acc * value) 1
  TM.require (claim = polyEvalRust products combiner)
  let y ← TM.samples step
  let values ← TM.lift (children.mapM fun child ↦ multilinearEvalRust child y)
  pure ⟨values, y ++ x⟩

/-- The `while layer > 0` loop: one level when `layer` is odd, two otherwise. -/
def gkrLoopM (layer : ℕ) (state : GkrState) : TM GkrState :=
  if _h : layer > 0 then do
    let step := if layer % 2 = 1 then 1 else 2
    let state ← gkrStepM step state
    gkrLoopM (layer - step) state
  else pure state
termination_by layer
decreasing_by split <;> omega

/-- `verify_gkr_grand_products(depth, transcript)`. -/
def verifyGkrM (depth : ℕ) : TM (E × List E × List E) := do
  let shared ← TM.nextScalar
  let count ← TM.nextScalar
  let state ← gkrLoopM depth ⟨[shared, shared, count], []⟩
  pure (count, state.point, state.values)

theorem multilinearEvalRust_some {mle point : List E} {v : E}
    (h : multilinearEvalRust mle point = some v) : v = multilinearEval mle point := by
  by_cases hc : point.length < 64 ∧ mle.length = 2 ^ point.length
  · rw [multilinearEvalRust_eq _ _ hc] at h
    exact (Option.some.inj h).symm
  · simp [multilinearEvalRust, hc] at h

theorem mapM_some {α β : Type} {f : α → Option β} {g : α → β}
    (hf : ∀ a b, f a = some b → b = g a) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → r = l.map g
  | [], r, h => by
    simp only [List.mapM_nil] at h
    cases h
    rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some r' =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some] at h
        cases (Option.some.inj h : b :: r' = r)
        rw [hf a b ha, mapM_some hf l r' hl]
        rfl

theorem Sim.gkrStep (step : ℕ) (state : GkrState) :
    Sim (gkrStepM step state) (gkrStep step state) := by
  unfold gkrStepM Verifier.gkrStep
  simp only [Nat.one_shiftLeft, polyEvalRust_eq]
  refine Sim.bind Sim.sample fun combiner ↦ ?_
  refine Sim.bind (Sim.sumcheck _ _ _) fun ⟨x, claim⟩ ↦ ?_
  refine Sim.bind (Sim.nextScalars _) fun c0 ↦ Sim.bind (Sim.nextScalars _) fun c1 ↦
    Sim.bind (Sim.nextScalars _) fun c2 ↦ Sim.bind (Sim.require _) fun _ ↦
    Sim.bind (Sim.samples _) fun y ↦ Sim.liftBind fun values hv ↦ ?_
  rw [mapM_some (fun _ _ h ↦ multilinearEvalRust_some h) _ _ hv]
  exact Sim.pure _

theorem Returns.gkrStep (step : ℕ) (state : GkrState) :
    Returns (gkrStepM step state) fun s ↦ s.point.length = step + state.point.length := by
  unfold gkrStepM
  refine Returns.bind (Returns.true _) fun _ _ ↦
    Returns.bind (Returns.sumcheck _ _ _) fun ⟨x, c⟩ hx ↦ ?_
  refine Returns.bind (Returns.true _) fun _ _ ↦ Returns.bind (Returns.true _) fun _ _ ↦
    Returns.bind (Returns.true _) fun _ _ ↦ Returns.bind (Returns.true _) fun _ _ ↦
    Returns.bind (Returns.samples _) fun y hy ↦ Returns.bind (Returns.true _) fun _ _ ↦
    Returns.pure ?_
  simp only [List.length_append, List.length_map] at hx ⊢
  omega

theorem Sim.gkrLoop (layer : ℕ) : ∀ state, Sim (gkrLoopM layer state) (gkrLayers layer state) := by
  induction layer using Nat.strong_induction_on with
  | _ layer ih =>
    intro state
    rw [gkrLoopM]
    match layer with
    | 0 => exact Sim.pure _
    | 1 =>
      simp only [gkrLayers]
      exact Sim.bind (Sim.gkrStep 1 state) fun s ↦ ih 0 (by omega) s
    | n + 2 =>
      simp only [gkrLayers]
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · have h1 : ¬ (n + 2) % 2 = 1 := by omega
        have h2 : ¬ n % 2 = 1 := by omega
        simp only [h1, h2, ↓reduceIte, gt_iff_lt, Nat.zero_lt_succ, ↓reduceDIte]
        exact Sim.bind (Sim.gkrStep 2 state) fun s ↦ ih n (by omega) s
      · have h1 : (n + 2) % 2 = 1 := by omega
        simp only [h1, hn, ↓reduceIte, gt_iff_lt, Nat.zero_lt_succ, ↓reduceDIte]
        exact Sim.bind (Sim.gkrStep 1 state) fun s ↦ ih (n + 1) (by omega) s

theorem Returns.gkrLoop (layer : ℕ) : ∀ state,
    Returns (gkrLoopM layer state) fun s ↦ s.point.length = layer + state.point.length := by
  induction layer using Nat.strong_induction_on with
  | _ layer ih =>
    intro state
    rw [gkrLoopM]
    by_cases h : layer > 0
    · simp only [h, ↓reduceDIte]
      refine Returns.bind (Returns.gkrStep _ state) fun s hs ↦ ?_
      have hlt : layer - (if layer % 2 = 1 then 1 else 2) < layer := by split <;> omega
      refine fun t a t' hr ↦ (ih _ hlt s t a t' hr).trans ?_
      rw [hs]
      split <;> omega
    · simp only [h, ↓reduceDIte]
      exact Returns.pure (by omega)

theorem Sim.verifyGkr (depth : ℕ) : Sim (verifyGkrM depth) (verifyGkrGrandProducts depth) :=
  Sim.bind Sim.nextScalar fun _ ↦ Sim.bind Sim.nextScalar fun _ ↦
    Sim.bind (Sim.gkrLoop depth _) fun _ ↦ Sim.pure _

theorem Returns.verifyGkr (depth : ℕ) :
    Returns (verifyGkrM depth) fun r ↦ r.2.1.length = depth :=
  Returns.bind (Returns.true _) fun _ _ ↦ Returns.bind (Returns.true _) fun _ _ ↦
    Returns.bind (Returns.gkrLoop depth _) fun _ h ↦ Returns.pure (by simpa using h)

/-! ## Forms (`layout.rs`)

A monomial is the statement's sorted list of column indices: `Monomial::One` is `[]`, `X(i)` is
`[i]`, `Xy(i, j)` is `[i, j]`. Indexing a slice out of bounds panics, a dead end, so a mirror reads
`getD`.
-/

/-- One term of `Form::add_scaled`: added into the first equal monomial, or pushed. -/
def addTermRust (terms : List (List ℕ × E)) (monomial : List ℕ) (c : E) : List (List ℕ × E) :=
  match terms.findIdx? (fun t ↦ t.1 = monomial) with
  | some i => terms.modify i fun t ↦ (t.1, t.2 + c)
  | none => terms ++ [(monomial, c)]

/-- `Form::add_scaled(other, weight)`. -/
def addScaledRust (f other : Form) (weight : E) : Form :=
  ⟨other.terms.foldl (fun terms t ↦ addTermRust terms t.1 (weight * t.2)) f.terms⟩

/-- One term of `Form::evaluate`. -/
def termValueRust (column : List E) : List ℕ × E → E
  | ([], c) => c
  | ([i], c) => c * column.getD i 0
  | ([i, j], c) => c * column.getD i 0 * column.getD j 0
  | (m, c) => m.foldl (fun acc i ↦ acc * column.getD i 0) c

/-- `Form::evaluate(column)`. -/
def evaluateRust (f : Form) (column : List E) : E := sumE (f.terms.map (termValueRust column))

theorem addTermRust_eq : ∀ (terms : List (List ℕ × E)) (m : List ℕ) (c : E),
    addTermRust terms m c = addTerm terms m c
  | [], m, c => by simp [addTermRust, addTerm]
  | (m', c') :: rest, m, c => by
    have ih := addTermRust_eq rest m c
    unfold addTermRust at ih ⊢
    rw [List.findIdx?_cons]
    by_cases h : m' = m
    · subst h
      simp [addTerm]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, addTerm]
      cases hf : rest.findIdx? (fun t ↦ decide (t.1 = m)) with
      | none => simp only [hf] at ih; simp [ih]
      | some i => simp only [hf] at ih; simp [ih]

theorem addScaledRust_eq (f other : Form) (weight : E) :
    addScaledRust f other weight = f.addScaled other weight := by
  simp only [addScaledRust, Form.addScaled, addTermRust_eq]

theorem evaluateRust_eq (f : Form) (column : List E) :
    evaluateRust f column = f.evaluate (column.getD · 0) := by
  unfold evaluateRust Form.evaluate
  congr 1
  apply List.map_congr_left
  rintro ⟨_ | ⟨i, _ | ⟨j, _ | ⟨k, m⟩⟩⟩, c⟩ _ <;> rfl

/-! ## The bus layout (`bus.rs`) -/

/-- `BusLayout`. -/
structure BusLayoutRust where
  depth : ℕ
  framework : List PlacementRust
  tables : List PlacementRust

/-- `bus_layout(framework_log_rows, blocks)`. -/
def busLayoutRust (frameworkLogRows : List ℕ) (blocks : List BusBlock) : BusLayoutRust :=
  let sizes := frameworkLogRows ++ blocks.map (·.logRows)
  let stacked := stackOffsetsRust sizes
  let framework : List PlacementRust := (sizes.zip stacked.1).map fun p ↦ ⟨p.1, p.2⟩
  ⟨stacked.2, framework.take frameworkLogRows.length, framework.drop frameworkLogRows.length⟩

theorem zip_map_toSpec : ∀ (sizes : List ℕ) (offsets : List (BitVec 64)),
    ((sizes.zip offsets).map fun p ↦ (⟨p.1, p.2⟩ : PlacementRust)).map PlacementRust.toSpec =
      List.zipWith (fun size offset ↦ ({ variableCount := size, index := offset } : Placement))
        sizes (offsets.map BitVec.toNat)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | s :: ss, o :: os => by
    simp only [List.zip_cons_cons, List.map_cons, List.zipWith_cons_cons, zip_map_toSpec ss os]
    rfl

theorem busLayoutRust_spec (frameworkLogRows : List ℕ) (blocks : List BusBlock)
    (h : ((frameworkLogRows ++ blocks.map (·.logRows)).map (2 ^ ·)).sum < 2 ^ 64) :
    (busLayoutRust frameworkLogRows blocks).depth = (busLayout frameworkLogRows blocks).depth ∧
    (busLayoutRust frameworkLogRows blocks).framework.map PlacementRust.toSpec =
      (busLayout frameworkLogRows blocks).framework ∧
    (busLayoutRust frameworkLogRows blocks).tables.map PlacementRust.toSpec =
      (busLayout frameworkLogRows blocks).tables := by
  obtain ⟨h1, h2⟩ := stackOffsetsRust_eq _ h
  have hS : stackOffsets (frameworkLogRows ++ blocks.map (·.logRows)) =
      ((stackOffsetsRust (frameworkLogRows ++ blocks.map (·.logRows))).1.map BitVec.toNat,
        (stackOffsetsRust (frameworkLogRows ++ blocks.map (·.logRows))).2) :=
    Prod.ext h1.symm h2.symm
  simp only [busLayoutRust, busLayout, hS, List.map_take, List.map_drop, zip_map_toSpec]
  exact ⟨trivial, trivial, trivial⟩

theorem busLayoutRust_depth_le (frameworkLogRows : List ℕ) (blocks : List BusBlock) :
    (busLayoutRust frameworkLogRows blocks).depth ≤ 64 := by
  simp only [busLayoutRust, stackOffsetsRust, log2CeilRust]
  omega

/-! ## `verify_bus_balance` (`bus.rs`) -/

/-- `GEN`, `E::new(2, 0, 0)`. -/
def genRust : E := eNew 2#64

/-- `gpow(index) = GEN.pow(index)` (`layout.rs`). -/
def gpowRust (index : BitVec 64) : E := genRust ^ index.toNat

/-- `SEP_STATE = ONE`. -/
def sepStateRust : E := 1

/-- `SEP_MEM = GEN`. -/
def sepMemRust : E := genRust

/-- `SEP_BYTECODE = E::new(4, 0, 0)`. -/
def sepBytecodeRust : E := eNew 4#64

theorem genRust_eq : genRust = gen := rfl

theorem gpowRust_eq (index : BitVec 64) : gpowRust index = gpow index.toNat := rfl

theorem sepStateRust_eq : sepStateRust = sepState := rfl

theorem sepMemRust_eq : sepMemRust = sepMem := rfl

theorem sepBytecodeRust_eq : sepBytecodeRust = sepBytecode := by
  apply limbs_inj
  have h : (sepBytecode : E) = gen * ex := by
    rw [sepBytecode, pow_two]
    rfl
  rw [h, ← ltimesX_eq, show gen = ofK (BF64.ofBitVec 2#64) from rfl, limbs_ofK, sepBytecodeRust,
    eNew, limbs_ofK]
  simp only [BF64.toBitVec_ofBitVec]
  decide

/-- The block form of `verify_bus_balance`'s inner loop: `constant(side_beta)` plus each
coordinate times its slot's weight. -/
def blockFormRust (block : BusBlock) (sideWeights : List E) (sideBeta : E) : Form :=
  block.coordinates.zipIdx.foldl
    (fun form (coordinate, slot) ↦ addScaledRust form coordinate (sideWeights.getD slot 0))
    (Form.const sideBeta)

theorem blockFormRust_eq (block : BusBlock) (sideWeights : List E) (sideBeta : E) :
    blockFormRust block sideWeights sideBeta = blockForm block sideWeights sideBeta := by
  simp only [blockFormRust, blockForm, addScaledRust_eq]

/-- One iteration of the loop over a side's table blocks: the owner's form for the side gains the
block's, and the padding rows their difference. -/
def blockStepRust (point : List E) (side : ℕ) (sideWeights : List E) (sideBeta : E)
    (acc : List (List Form) × E) (sb : E × BusBlock) : List (List Form) × E :=
  let selector := sb.1
  let block := sb.2
  let blockForm := blockFormRust block sideWeights sideBeta
  let forms := acc.1.modify block.owner fun row ↦
    row.modify side fun form ↦ addScaledRust form blockForm selector
  let padding := (tables.getD block.owner default).padding
  let weight := paddingWeightRust (point.take block.logRows) (BitVec.ofNat 64 block.rows)
  (forms, acc.2 + selector * weight * (evaluateRust blockForm padding + 1))

/-- One iteration of `verify_bus_balance`'s loop over the sides: the forms with the side's table
blocks added, and the side's total. -/
def sideStepRust (point treeValues : List E) (forms : List (List Form)) (side : ℕ)
    (blocks : List BusBlock) (sideLayout : BusLayoutRust)
    (frameworkFingerprints sideWeights : List E) (sideBeta : E) : List (List Form) × E :=
  let frameworkSelectors := sideLayout.framework.map (·.eqAbove point)
  let tableSelectors := sideLayout.tables.map (·.eqAbove point)
  let shifted := frameworkFingerprints.map (sideBeta + ·)
  let known := dotRust frameworkSelectors shifted
  let r :=
    (tableSelectors.zip blocks).foldl (blockStepRust point side sideWeights sideBeta) (forms, 0)
  let onesPadding := sumE (frameworkSelectors ++ tableSelectors) + 1
  (r.1, treeValues.getD side 0 + known + onesPadding + r.2)

theorem sideStepRust_eq (point treeValues : List E) (forms : List (List Form)) (side : ℕ)
    (blocks : List BusBlock) (sideLayout : BusLayoutRust) (spec : BusLayout)
    (frameworkFingerprints sideWeights : List E) (sideBeta : E)
    (hfw : sideLayout.framework.map PlacementRust.toSpec = spec.framework)
    (htb : sideLayout.tables.map PlacementRust.toSpec = spec.tables)
    (hpoint : point.length ≤ 64) (hblocks : ∀ b ∈ blocks, b.logRows < 64 ∧ b.rows < 2 ^ 64) :
    sideStepRust point treeValues forms side blocks sideLayout frameworkFingerprints sideWeights
        sideBeta =
      accumulateSide forms side blocks spec frameworkFingerprints sideWeights sideBeta point
        (treeValues.getD side 0) := by
  have hsel : ∀ ps : List PlacementRust,
      ps.map (·.eqAbove point) = (ps.map PlacementRust.toSpec).map (·.eqAbove point) := by
    intro ps
    simp only [List.map_map]
    apply List.map_congr_left
    intro p _
    exact PlacementRust.eqAbove_eq p point hpoint
  have hfold : ∀ (l : List (E × BusBlock)) (init : List (List Form) × E),
      (∀ x ∈ l, x.2 ∈ blocks) →
      l.foldl (blockStepRust point side sideWeights sideBeta) init =
        l.foldl (fun (acc : List (List Form) × E) (sb : E × BusBlock) ↦
          let form := blockForm sb.2 sideWeights sideBeta
          let padding := (tables.getD sb.2.owner default).padding
          (acc.1.modify sb.2.owner fun row ↦ row.modify side fun f ↦ f.addScaled form sb.1,
            acc.2 + sb.1 * paddingWeight (point.take sb.2.logRows) sb.2.rows *
              (form.evaluate (padding.getD · 0) + 1))) init := by
    intro l init hl
    apply foldl_congr_mem
    intro acc sb hsb
    obtain ⟨hlog, hrows⟩ := hblocks sb.2 (hl sb hsb)
    have hlen : (point.take sb.2.logRows).length < 64 := by
      rw [List.length_take]; omega
    simp only [blockStepRust, blockFormRust_eq, addScaledRust_eq, evaluateRust_eq,
      paddingWeightRust_eq _ _ hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrows]
  have hmem : ∀ x ∈ (spec.tables.map (·.eqAbove point)).zip blocks, x.2 ∈ blocks :=
    fun x hx ↦ List.of_mem_zip hx |>.2
  simp only [sideStepRust, accumulateSide, hsel sideLayout.framework, hsel sideLayout.tables, hfw,
    htb, dotRust_eq, hfold _ _ hmem]

/-- `BusResult`, with `bytecode_point`, which the statement leaves out. -/
structure BusResultRust where
  claims : List ColumnClaim
  bytecodePoint : List E
  point : List E
  forms : List (List Form)
  totals : List E

/-- The statement's `BusResult`. -/
def BusResultRust.toSpec (r : BusResultRust) : BusResult := ⟨r.claims, r.point, r.forms, r.totals⟩

/-- `verify_bus_balance(layout, transcript)`, in checked mode. `bytecodeEvaluate` is
`layout.bytecode.evaluate`. -/
def verifyBusBalanceM (bytecodeEvaluate : List E → Option E) (layout : Layout) :
    TM BusResultRust := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayoutRust frameworkLogRows layout.push
  let pullLayout := busLayoutRust frameworkLogRows layout.pull
  let countLayout := busLayoutRust [] layout.count
  let alphas ← TM.samples busBits
  let weights := eqKernelRust alphas
  let beta ← TM.sample
  let (countRoot, point, treeValues) ← verifyGkrM pushLayout.depth
  TM.require (countRoot ≠ 0)
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory ← TM.nextScalars 3
  let memoryFinal ← TM.nextScalar
  let bytecodeFinal ← TM.nextScalar
  let claims : List ColumnClaim :=
    [memory0, memory1, memory2].map (fun column ↦ ⟨column, memoryLow, memory.getD column 0⟩) ++
      [⟨memoryFinalCounters, memoryLow, memoryFinal⟩,
        ⟨bytecodeFinalCounters, bytecodeLow, bytecodeFinal⟩]
  let memoryIndex := indexMleRust memoryLow
  let bytecodeIndex := indexMleRust bytecodeLow
  let bytecodePoint := bytecodeLow ++ alphas
  let bytecodeValue ← TM.lift (bytecodeEvaluate bytecodePoint)
  let fingerprints := fun (pc memoryCount bytecodeCount : E) ↦
    [dotRust (weights.take 3) [sepStateRust, pc, gpowRust 0#64],
      dotRust (weights.take 6) [sepMemRust, memoryIndex, memoryCount, memory.getD 0 0,
        memory.getD 1 0, memory.getD 2 0],
      dotRust (weights.take 3) [sepBytecodeRust, bytecodeIndex, bytecodeCount] + bytecodeValue]
  let finalPc := gpowRust ((1#64 <<< (layout.logBytecode % 64)) - 1#64)
  let sides : List (List BusBlock × BusLayoutRust × List E × List E × E) :=
    [(layout.push, pushLayout, fingerprints (gpowRust 0#64) 1 1, weights, beta),
      (layout.pull, pullLayout, fingerprints finalPc memoryFinal bytecodeFinal, weights, beta),
      (layout.count, countLayout, [], [1], 0)]
  let r := sides.zipIdx.foldl (fun (acc : List (List Form) × List E) sd ↦
      let side := sideStepRust point treeValues acc.1 sd.2 sd.1.1 sd.1.2.1 sd.1.2.2.1 sd.1.2.2.2.1
        sd.1.2.2.2.2
      (side.1, acc.2 ++ [side.2]))
    (List.replicate tables.length (List.replicate 3 {}), [])
  pure ⟨claims, bytecodePoint, point, r.1, r.2⟩

/-- What the Rust's machine integers need of a layout: each side's blocks, stacked, fit in a
`u64`, and every block's row count is a `u64`. -/
structure BusBounds (layout : Layout) : Prop where
  push : (([0, layout.logMemory, layout.logBytecode] ++ layout.push.map (·.logRows)).map
    (2 ^ ·)).sum < 2 ^ 64
  pull : (([0, layout.logMemory, layout.logBytecode] ++ layout.pull.map (·.logRows)).map
    (2 ^ ·)).sum < 2 ^ 64
  count : (((([] : List ℕ)) ++ layout.count.map (·.logRows)).map (2 ^ ·)).sum < 2 ^ 64
  rows : ∀ b ∈ layout.push ++ layout.pull ++ layout.count, b.rows < 2 ^ 64

theorem lt_64_of_mem {l : List ℕ} {x : ℕ} (hx : x ∈ l) (h : (l.map (2 ^ ·)).sum < 2 ^ 64) :
    x < 64 := by
  have : 2 ^ x ≤ (l.map (2 ^ ·)).sum := List.le_sum_of_mem (List.mem_map_of_mem hx)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt this h)

theorem blocks_bounded {f : List ℕ} {blocks : List BusBlock}
    (h : ((f ++ blocks.map (·.logRows)).map (2 ^ ·)).sum < 2 ^ 64)
    (hrows : ∀ b ∈ blocks, b.rows < 2 ^ 64) : ∀ b ∈ blocks, b.logRows < 64 ∧ b.rows < 2 ^ 64 :=
  fun b hb ↦ ⟨lt_64_of_mem (List.mem_append_right _ (List.mem_map_of_mem hb)) h, hrows b hb⟩

theorem finalPc_eq (logBytecode : ℕ) (h : logBytecode < 64) :
    gpowRust ((1#64 <<< (logBytecode % 64)) - 1#64) = gpow (2 ^ logBytecode - 1) := by
  rw [gpowRust_eq]
  congr 1
  have hp : 1 ≤ 2 ^ logBytecode := Nat.one_le_two_pow
  have hlt : 2 ^ logBytecode < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) h
  rw [Nat.mod_eq_of_lt h, BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp only [BitVec.toNat_ofNat, Nat.one_mod_two_pow (by norm_num : 0 < 64), one_mul,
      Nat.mod_eq_of_lt hlt]
  · rw [BitVec.le_def, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp only [BitVec.toNat_ofNat, Nat.one_mod_two_pow (by norm_num : 0 < 64), one_mul,
      Nat.mod_eq_of_lt hlt]
    exact hp

/-- **`verify_bus_balance` runs `verifyBusBalance`**, its value the statement's but for
`bytecode_point`, given the bounds and the statement's fixed-polynomial value wherever the Rust's
`Bytecode::evaluate` returns. -/
theorem SimR.verifyBusBalance (bytecodeEvaluate : List E → Option E)
    (bytecodeValue : List K → List E → VerifierProgram E) (layout : Layout) (hb : BusBounds layout)
    (hv : ∀ pt v, bytecodeEvaluate pt = some v →
      ∀ σ, runK (bytecodeValue layout.bytecode pt) σ = some (v, σ)) :
    SimR (verifyBusBalanceM bytecodeEvaluate layout)
      (Verifier.verifyBusBalance bytecodeValue layout) BusResultRust.toSpec := by
  obtain ⟨hpush, hpull, hcount, hrows⟩ := hb
  obtain ⟨hd, hfw0, htb0⟩ := busLayoutRust_spec _ _ hpush
  obtain ⟨-, hfw1, htb1⟩ := busLayoutRust_spec _ _ hpull
  obtain ⟨-, hfw2, htb2⟩ := busLayoutRust_spec _ _ hcount
  have hdle := busLayoutRust_depth_le [0, layout.logMemory, layout.logBytecode] layout.push
  rw [hd] at hdle
  have hlb : layout.logBytecode < 64 := lt_64_of_mem (by simp) hpush
  have hb0 := blocks_bounded hpush fun b hb ↦ hrows b (by simp [hb])
  have hb1 := blocks_bounded hpull fun b hb ↦ hrows b (by simp [hb])
  have hb2 := blocks_bounded hcount fun b hb ↦ hrows b (by simp [hb])
  unfold verifyBusBalanceM Verifier.verifyBusBalance
  simp only [hd, eqKernelRust_eq]
  refine SimR.bind (Sim.samples _) fun alphas ↦ SimR.bind Sim.sample fun beta ↦ ?_
  refine SimR.bindPost (Sim.verifyGkr _) (Returns.verifyGkr _) fun ⟨countRoot, point, treeValues⟩
    hlen ↦ ?_
  refine SimR.bind (Sim.require _) fun _ ↦ ?_
  refine SimR.bindPost (Sim.nextScalars 3) (Returns.nextScalars 3) fun memory hmem ↦ ?_
  refine SimR.bind Sim.nextScalar fun memoryFinal ↦ SimR.bind Sim.nextScalar fun bytecodeFinal ↦ ?_
  refine SimR.bind (Sim.lift (hv _)) fun bytecodeValue ↦ ?_
  match memory, hmem with
  | [m0, m1, m2], _ =>
  apply SimR.pure
  have hpt : point.length ≤ 64 := by simp only at hlen; omega
  simp only [finalPc_eq _ hlb]
  simp only [dotRust_eq, indexMleRust_eq, gpowRust_eq, sepStateRust_eq, sepMemRust_eq,
    sepBytecodeRust_eq, List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons,
    List.foldl_nil, sideStepRust_eq _ _ _ _ _ _ _ _ _ _ hfw0 htb0 hpt hb0,
    sideStepRust_eq _ _ _ _ _ _ _ _ _ _ hfw1 htb1 hpt hb1,
    sideStepRust_eq _ _ _ _ _ _ _ _ _ _ hfw2 htb2 hpt hb2]
  have hinit : List.replicate tables.length (List.replicate 3 ({} : Form)) =
      tables.map fun _ ↦ [{}, {}, {}] := rfl
  simp only [hinit, fingerprints, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add, Nat.reduceAdd,
    List.nil_append, List.cons_append, memory0, memory1, memory2, List.map_cons, List.map_nil,
    List.zipWith_cons_cons, List.zipWith_nil_left, List.getD_cons_zero, List.getD_cons_succ,
    BusResultRust.toSpec]

theorem Sim.verifyBusBalance (bytecodeEvaluate : List E → Option E)
    (bytecodeValue : List K → List E → VerifierProgram E) (layout : Layout) (hb : BusBounds layout)
    (hv : ∀ pt v, bytecodeEvaluate pt = some v →
      ∀ σ, runK (bytecodeValue layout.bytecode pt) σ = some (v, σ)) :
    Sim (BusResultRust.toSpec <$> verifyBusBalanceM bytecodeEvaluate layout)
      (Verifier.verifyBusBalance bytecodeValue layout) :=
  (SimR.verifyBusBalance bytecodeEvaluate bytecodeValue layout hb hv).sim

theorem blockStepRust_length (point : List E) (side : ℕ) (sideWeights : List E) (sideBeta : E) :
    ∀ (l : List (E × BusBlock)) (acc : List (List Form) × E),
      (l.foldl (blockStepRust point side sideWeights sideBeta) acc).1.length = acc.1.length
  | [], _ => rfl
  | sb :: l, acc => by
    rw [List.foldl_cons, blockStepRust_length point side sideWeights sideBeta l]
    simp [blockStepRust]

theorem sideStepRust_length (point treeValues : List E) (forms : List (List Form)) (side : ℕ)
    (blocks : List BusBlock) (sideLayout : BusLayoutRust)
    (frameworkFingerprints sideWeights : List E) (sideBeta : E) :
    (sideStepRust point treeValues forms side blocks sideLayout frameworkFingerprints sideWeights
      sideBeta).1.length = forms.length := by
  simp only [sideStepRust, blockStepRust_length]

theorem Returns.bindAll {α β : Type} {m : TM α} {k : α → TM β} {S : β → Prop}
    (hk : ∀ a, Returns (k a) S) : Returns (m >>= k) S :=
  Returns.bind (Returns.true m) fun a _ ↦ hk a

/-- `verify_bus_balance` returns a row of forms per table, as `table_sumcheck` takes them. -/
theorem Returns.verifyBusBalance (bytecodeEvaluate : List E → Option E) (layout : Layout) :
    Returns (verifyBusBalanceM bytecodeEvaluate layout) fun r ↦ r.forms.length = tables.length := by
  unfold verifyBusBalanceM
  refine Returns.bindAll fun _ ↦ Returns.bindAll fun _ ↦ Returns.bindAll fun _ ↦
    Returns.bindAll fun _ ↦ Returns.bindAll fun _ ↦ Returns.bindAll fun _ ↦
    Returns.bindAll fun _ ↦ Returns.bindAll fun _ ↦ Returns.pure ?_
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil,
    sideStepRust_length, List.length_replicate]

/-- The deployed verifier's fixed polynomial: `Bytecode::evaluate` returns the multilinear
extension of the words. -/
theorem Sim.verifyBusBalance_computed (bytecodeEvaluate : List E → Option E) (layout : Layout)
    (hb : BusBounds layout)
    (hv : ∀ pt v, bytecodeEvaluate pt = some v → v = multilinearEval (layout.bytecode.map ofK) pt) :
    Sim (BusResultRust.toSpec <$> verifyBusBalanceM bytecodeEvaluate layout)
      (Verifier.verifyBusBalance computedBytecodeValue layout) :=
  Sim.verifyBusBalance _ _ layout hb fun pt v h σ ↦ by
    rw [hv pt v h]
    rfl

/-! ## `table_sumcheck` (`bus.rs`) -/

/-- The weights loops of `table_sumcheck`: for each coordinate `v` of the point, for each table,
`weights[index] *= …`. -/
def tableWeightsRust (tableCount : ℕ) (heights : List ℕ) (equalityPoint point : List E) : List E :=
  point.zipIdx.foldl (fun weights cv ↦
      let equality := 1 + equalityPoint.getD cv.2 0 + cv.1
      heights.zipIdx.foldl (fun weights hi ↦
        weights.modify hi.2 (· * if hi.1 > cv.2 then equality else cv.1)) weights)
    (List.replicate tableCount 1)

/-- The loop reading each table's evaluations, after the rows pushed so far. -/
def readRowsM (point : List E) :
    List (Table × ℕ) → List (List E × List E) → TM (List (List E × List E))
  | [], rows => pure rows
  | (table, height) :: rest, rows => do
    let evaluations ← TM.nextScalars table.width
    readRowsM point rest (rows ++ [(point.take height, evaluations)])

/-- One iteration of the checked terminal's loop: `(terminal, cursor)` past a table. -/
def terminalStep (constraintPowers formPowers : List E) (acc : E × ℕ)
    (item : ((Table × (List E × List E)) × List Form) × E) : E × ℕ :=
  let table := item.1.1.1
  let evaluations := item.1.1.2.2
  let forms := item.1.2
  let weight := item.2
  let n := table.nConstraints
  let summand := dotRust ((constraintPowers.drop acc.2).take n) (table.constraints evaluations)
  let formValues := forms.map (evaluateRust · evaluations)
  (acc.1 + weight * (summand + dotRust formPowers formValues), acc.2 + n)

/-- The checked terminal, `Σ weight · (constraints + forms)`. -/
def terminalRust (constraintPowers formPowers : List E)
    (items : List (((Table × (List E × List E)) × List Form) × E)) : E :=
  (items.foldl (terminalStep constraintPowers formPowers) (0, 0)).1

/-- `table_sumcheck(tables, table_log_heights, bus_forms, constraint_powers, form_powers,
equality_point, target, transcript)`, in checked mode. -/
def tableSumcheckM (tablesL : List Table) (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    TM (List (List E × List E)) := do
  let nRounds := heights.max?.getD 0
  let (challenges, claim) ← sumcheckM target 4 (List.replicate nRounds none)
  let point := challenges.reverse
  let weights := tableWeightsRust tablesL.length heights equalityPoint point
  let rows ← readRowsM point (tablesL.zip heights) []
  TM.require
    (terminalRust constraintPowers formPowers (((tablesL.zip rows).zip busForms).zip weights) =
      claim)
  pure rows

theorem max?_getD (l : List ℕ) : l.max?.getD 0 = l.foldl max 0 := by
  cases l with
  | nil => rfl
  | cons a l =>
    simp only [List.foldl_cons, Nat.zero_max]
    rfl

theorem modify_append_length {α : Type} (f : α → α) (r : α) (rest : List α) :
    ∀ pre : List α, (pre ++ r :: rest).modify pre.length f = pre ++ f r :: rest
  | [] => rfl
  | a :: pre => by
    simp only [List.cons_append, List.length_cons, List.modify_succ_cons,
      modify_append_length f r rest pre]

theorem modifyLoop_eq (g : ℕ → E → E) : ∀ (hs : List ℕ) (pre rest : List E),
    hs.length ≤ rest.length →
    (hs.zipIdx pre.length).foldl (fun ws (hi : ℕ × ℕ) ↦ ws.modify hi.2 (g hi.1)) (pre ++ rest) =
      pre ++ (List.zipWith (fun w h ↦ g h w) rest hs ++ rest.drop hs.length)
  | [], pre, rest, _ => by simp
  | h :: hs, pre, [], hl => by simp at hl
  | h :: hs, pre, r :: rest, hl => by
    simp only [List.zipIdx_cons, List.foldl_cons, modify_append_length]
    have := modifyLoop_eq g hs (pre ++ [g h r]) rest (by simp at hl; omega)
    simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
      List.singleton_append] at this
    rw [this]
    simp

theorem foldl_congr_inv {α β : Type} {f g : β → α → β} (P : β → Prop)
    (hP : ∀ b a, P b → P (g b a)) (h : ∀ b a, P b → f b a = g b a) :
    ∀ (l : List α) (init : β), P init → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | a :: l, init, hi => by
    simp only [List.foldl_cons, h init a hi]
    exact foldl_congr_inv P hP h l _ (hP init a hi)

theorem tableWeightsRust_eq (heights : List ℕ) (equalityPoint point : List E) :
    tableWeightsRust heights.length heights equalityPoint point =
      tableWeights heights equalityPoint point := by
  unfold tableWeightsRust tableWeights
  rw [← List.map_const']
  refine foldl_congr_inv (fun ws ↦ ws.length = heights.length) ?_ ?_ _ _ (by simp)
  · intro ws x hws
    simp [hws]
  · intro ws x hws
    have := modifyLoop_eq
      (fun h w ↦ w * if h > x.2 then 1 + equalityPoint.getD x.2 0 + x.1 else x.1) heights [] ws
      (by omega)
    simp only [List.length_nil, List.nil_append] at this
    simp only [this, List.drop_eq_nil_of_le (show ws.length ≤ heights.length by omega),
      List.append_nil]

theorem tableWeights_length (heights : List ℕ) (equalityPoint point : List E) :
    (tableWeights heights equalityPoint point).length = heights.length := by
  unfold tableWeights
  suffices ∀ (l : List (E × ℕ)) (init : List E), init.length = heights.length →
      (l.foldl (fun weights (x : E × ℕ) ↦ List.zipWith (fun weight height ↦ weight *
        if x.2 < height then 1 + equalityPoint.getD x.2 0 + x.1 else x.1) weights heights)
        init).length = heights.length from this _ _ (by simp)
  intro l
  induction l with
  | nil => intro init h; exact h
  | cons x l ih => intro init h; exact ih _ (by simp [h])

/-- The statement's step of `tableTerms`' sum, over a table's quadruple and its row. -/
def specStep (constraintPowers formPowers : List E) (acc : E × ℕ)
    (qr : (Table × ℕ × List Form × E) × (List E × List E)) : E × ℕ :=
  let table := qr.1.1
  let forms := qr.1.2.2.1
  let weight := qr.1.2.2.2
  let evaluations := qr.2.2
  let summand := dot ((constraintPowers.drop acc.2).take table.nConstraints)
    (table.constraints evaluations)
  (acc.1 + weight * (summand + dot formPowers (forms.map (·.evaluate (evaluations.getD · 0)))),
    acc.2 + table.nConstraints)

theorem readRows_sim (point constraintPowers formPowers : List E) {β : Type} :
    ∀ (Q : List (Table × ℕ × List Form × E)) (acc : List (List E × List E)) (cursor : ℕ) (final : E)
      (k : List (List E × List E) → TM β) (K : E × List (List E × List E) → VerifierProgram β),
      (∀ rs : List (List E × List E), rs.length = Q.length →
        Sim (k (acc ++ rs))
          (K (((Q.zip rs).foldl (specStep constraintPowers formPowers) (final, cursor)).1, rs))) →
      Sim (readRowsM point (Q.map fun q ↦ (q.1, q.2.1)) acc >>= k)
        (tableTerms constraintPowers formPowers point Q cursor final >>= K)
  | [], acc, cursor, final, k, K, h => by
    have h0 := h [] rfl
    rw [List.append_nil] at h0
    simp only [List.map_nil, readRowsM, pure_bind]
    exact h0
  | (table, height, forms, weight) :: Q, acc, cursor, final, k, K, h => by
    simp only [List.map_cons, readRowsM, tableTerms, bind_assoc, VerifierProgram.bind_assoc]
    refine Sim.bind (Sim.nextScalars _) fun evaluations ↦ ?_
    refine readRows_sim point constraintPowers formPowers Q
      (acc ++ [(point.take height, evaluations)]) _ _ k
      (fun x ↦ K (x.1, (point.take height, evaluations) :: x.2)) fun rs hrs ↦ ?_
    have := h ((point.take height, evaluations) :: rs) (by simp [hrs])
    simp only [List.append_assoc, List.singleton_append]
    exact this

theorem zip_heights_eq : ∀ (T : List Table) (H : List ℕ) (F : List (List Form)) (W : List E),
    H.length = T.length → F.length = T.length → W.length = T.length →
    T.zip H = (T.zip (H.zip (F.zip W))).map fun q ↦ (q.1, q.2.1)
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, hH, _, _ => by simp at hH
  | _ :: _, _ :: _, [], _, _, hF, _ => by simp at hF
  | _ :: _, _ :: _, _ :: _, [], _, _, hW => by simp at hW
  | t :: T, h :: H, f :: F, w :: W, hH, hF, hW => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hH hF hW
    simp only [List.zip_cons_cons, List.map_cons, zip_heights_eq T H F W hH hF hW]

theorem terminal_eq (constraintPowers formPowers : List E) :
    ∀ (T : List Table) (H : List ℕ) (F : List (List Form)) (W : List E)
      (R : List (List E × List E)) (acc : E × ℕ),
    H.length = T.length → F.length = T.length → W.length = T.length → R.length = T.length →
    (((T.zip R).zip F).zip W).foldl (terminalStep constraintPowers formPowers) acc =
      ((T.zip (H.zip (F.zip W))).zip R).foldl (specStep constraintPowers formPowers) acc
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _, hH, _, _, _ => by simp at hH
  | _ :: _, _ :: _, [], _, _, _, _, hF, _, _ => by simp at hF
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, hW, _ => by simp at hW
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, hR => by simp at hR
  | t :: T, h :: H, f :: F, w :: W, r :: R, acc, hH, hF, hW, hR => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hH hF hW hR
    have hs : terminalStep constraintPowers formPowers acc (((t, r), f), w) =
        specStep constraintPowers formPowers acc ((t, h, f, w), r) := by
      simp only [terminalStep, specStep, dotRust_eq, evaluateRust_eq]
    simp only [List.zip_cons_cons, List.foldl_cons, hs]
    exact terminal_eq constraintPowers formPowers T H F W R _ hH hF hW hR

/-- **`table_sumcheck` runs `tableSumcheck`**, on the statement's tables, given a height and a
form row per table (as `build_layout` and `verify_bus_balance` give them). -/
theorem Sim.tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E)
    (hh : heights.length = tables.length) (hf : busForms.length = tables.length) :
    Sim (tableSumcheckM tables heights busForms constraintPowers formPowers equalityPoint target)
      (Verifier.tableSumcheck heights busForms constraintPowers formPowers equalityPoint
        target) := by
  unfold tableSumcheckM Verifier.tableSumcheck
  simp only [max?_getD]
  refine Sim.bind (Sim.sumcheck _ _ _) fun ⟨challenges, claim⟩ ↦ ?_
  dsimp only
  rw [show tables.length = heights.length from hh.symm, tableWeightsRust_eq]
  have hw := tableWeights_length heights equalityPoint challenges.reverse
  rw [zip_heights_eq tables heights busForms _ hh hf (hw.trans hh)]
  refine readRows_sim _ _ _ _ [] 0 0 _ _ fun rs hrs ↦ ?_
  simp only [List.length_zip, hh, hf, hw, min_self] at hrs
  simp only [List.nil_append]
  have ht : terminalRust constraintPowers formPowers
      (((tables.zip rs).zip busForms).zip (tableWeights heights equalityPoint challenges.reverse)) =
      (((tables.zip (heights.zip (busForms.zip (tableWeights heights equalityPoint
        challenges.reverse)))).zip rs).foldl (specStep constraintPowers formPowers) (0, 0)).1 := by
    rw [terminalRust, terminal_eq _ _ tables heights busForms _ rs (0, 0) hh hf (hw.trans hh) hrs]
  exact Sim.bind (Sim.requireIff (by simp only [ht])) fun _ ↦ Sim.pure _

end Rv64Verifier.Model
