module

public import VCVio.CryptoFoundations.ReplayFork
public import VCVio.CryptoFoundations.ReplayForkCost

@[expose] public section

/-!
# The replay fork commutes with answering an extra oracle by a fixed function

The replay fork (`OracleComp.contextFork`, VCVio) runs a program, selects an occurrence of a
target query from its output, and completes that occurrence a second time with fresh answers for
every later query. When the program's queries of an extra oracle `X` are answered by a fixed
function `c` (`collapse c`: the other queries forwarded), forking the collapsed program is
collapsing the fork of the program with `X` as an oracle (`contextFork_collapse`): both completions
see the same `c`. So the fork's queries of `X` are counted by VCVio's bound on the fork
(`isQueryBoundP_contextFork`), and a fork of a program whose hash is a fixed table `h` is a
program querying `h` at most twice as often.

The proof reads the fork through a semantic form (`sem`): the first run, and for each `s` the
program completing occurrence `s` a second time (`lhs_eq_rhs`); `sem` commutes with `collapse`
(`map_collapse_sem`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA: it bounds the
collision term of his forking reduction.
-/

set_option linter.unusedSectionVars false

open PFunctor PFunctor.FreeM PFunctor.FreeM.Cursor OracleSpec OracleComp

namespace LeanDa.Fork

section Free

variable {P : PFunctor.{0, 0}} [DecidableEq P.A] {α β : Type}

/-- **The fork's semantic form**: the first run, with, for each `s`, the program completing the
`s`-th occurrence of the target `t` a second time, which returns the second output and the two
answers at the occurrence (`none` when there is no such occurrence). -/
def sem (t : P.A) : FreeM P α → FreeM P (α × (ℕ → FreeM P (Option (α × P.B t × P.B t))))
  | .pure x => FreeM.pure (x, fun _ ↦ FreeM.pure none)
  | .liftBind a next =>
    if h : a = t then
      FreeM.liftBind a fun u ↦ FreeM.bind (sem t (next u)) fun p ↦
        FreeM.pure (p.1, fun s ↦ match s with
          | 0 => FreeM.liftBind a fun u₂ ↦
              FreeM.map (fun x₂ ↦ some (x₂, h ▸ u, h ▸ u₂)) (next u₂)
          | s + 1 => p.2 s)
    else FreeM.liftBind a fun u ↦ sem t (next u)

/-- The fork read from a first path: the selected occurrence completed once more. -/
def lhs (t : P.A) (prog : FreeM P α) (sel : α → Option ℕ) (D : α → FreeM P β)
    (F : α → ℕ → α → P.B t → P.B t → β) (dflt : β) : FreeM P β :=
  FreeM.bind (withPath prog) fun path ↦
    match sel (output prog path) with
    | none => D (output prog path)
    | some s =>
      match locateAt? t prog path s with
      | none => FreeM.pure dflt
      | some loc => FreeM.map (fun c ↦ F (output prog path) s (output prog c.path)
          loc.completion.answer c.answer) loc.occurrence.complete

/-- The fork read from the semantic form. -/
def rhs (t : P.A) (prog : FreeM P α) (sel : α → Option ℕ) (D : α → FreeM P β)
    (F : α → ℕ → α → P.B t → P.B t → β) (dflt : β) : FreeM P β :=
  FreeM.bind (sem t prog) fun p ↦
    match sel p.1 with
    | none => D p.1
    | some s => FreeM.bind (p.2 s) fun o ↦
      match o with
      | none => FreeM.pure dflt
      | some q => FreeM.pure (F p.1 s q.1 q.2.1 q.2.2)

/-- Observing a completion through its output and answer reads only the occurrence's
continuation. -/
theorem map_complete {t : P.A} {prog : FreeM P α} {n : ℕ} (occ : Occurrence t prog n)
    (G : α → P.B t → β) :
    FreeM.map (fun c : occ.Completion ↦ G (output prog c.path) c.answer) occ.complete =
      FreeM.liftBind t fun a ↦ FreeM.map (fun x ↦ G x a) (occ.resume a) := by
  unfold Occurrence.complete
  simp only [FreeM.map]
  congr 1
  funext a
  rw [← FreeM.comp_map]
  conv_rhs => rw [← map_output_withPath (occ.resume a), ← FreeM.comp_map]
  congr 1
  funext s
  exact congrArg (G · a) (Occurrence.output_plug occ a s)

theorem lhs_pure (t : P.A) (x : α) (sel : α → Option ℕ) (D : α → FreeM P β)
    (F : α → ℕ → α → P.B t → P.B t → β) (dflt : β) :
    lhs t (FreeM.pure x) sel D F dflt = rhs t (FreeM.pure x) sel D F dflt := by
  unfold lhs rhs
  simp only [sem]
  change (match sel x with
    | none => D x
    | some s => match locateAt? t (FreeM.pure x) (⟨⟩ : Path (FreeM.pure x : FreeM P α)) s with
      | none => FreeM.pure dflt
      | some loc => FreeM.map (fun (c : loc.occurrence.Completion) ↦
          F x s (output (FreeM.pure x) c.path) loc.completion.answer c.answer)
            loc.occurrence.complete) = (match sel x with
    | none => D x
    | some s => FreeM.bind (FreeM.pure none) fun o ↦ match o with
      | none => FreeM.pure dflt
      | some (q : α × P.B t × P.B t) => FreeM.pure (F x s q.1 q.2.1 q.2.2))
  rcases sel x with _ | s
  · rfl
  · rfl

theorem output_liftBind (a : P.A) (next : P.B a → FreeM P α) (u : P.B a) (p : Path (next u)) :
    output (FreeM.liftBind a next) (⟨u, p⟩ : Path (FreeM.liftBind a next)) = output (next u) p :=
  rfl

/-- **The fork's two readings agree.** -/
theorem lhs_eq_rhs (t : P.A) : (prog : FreeM P α) →
    ∀ (sel : α → Option ℕ) (D : α → FreeM P β) (F : α → ℕ → α → P.B t → P.B t → β) (dflt : β),
      lhs t prog sel D F dflt = rhs t prog sel D F dflt
  | .pure x => lhs_pure t x
  | .liftBind a next => by
    intro sel D F dflt
    by_cases h : a = t
    · subst h
      have hl : lhs a (FreeM.liftBind a next) sel D F dflt = FreeM.liftBind a fun u ↦
          lhs a (next u) (fun x ↦ match sel x with | some (s + 1) => some s | _ => none)
            (fun x ↦ match sel x with
              | some 0 => FreeM.liftBind a fun u₂ ↦ FreeM.map (fun x₂ ↦ F x 0 x₂ u u₂) (next u₂)
              | _ => D x)
            (fun x s ↦ F x (s + 1)) dflt := by
        unfold lhs
        rw [withPath_liftBind_bind]
        congr 1
        funext u
        congr 1
        funext p
        simp only [output_liftBind]
        rcases hs : sel (output (next u) p) with _ | _ | s
        · simp only
        · simp only
          rw [locateAt?_liftBind_same_zero]
          simp only [Located.here]
          rw [map_complete (Occurrence.here next) (fun x₂ u₂ ↦ F (output (next u) p) 0 x₂ u u₂)]
          rfl
        · simp only
          rw [locateAt?_liftBind_same_succ]
          rcases hloc : locateAt? a (next u) p s with _ | loc
          · rfl
          · simp only [Option.map_some]
            rw [map_complete (Located.prependSame u loc).occurrence (fun x₂ a₂ ↦
                F (output (next u) p) (s + 1) x₂ (Located.prependSame u loc).completion.answer a₂),
              map_complete loc.occurrence (fun x₂ a₂ ↦
                F (output (next u) p) (s + 1) x₂ loc.completion.answer a₂)]
            rfl
      have hr : rhs a (FreeM.liftBind a next) sel D F dflt = FreeM.liftBind a fun u ↦
          rhs a (next u) (fun x ↦ match sel x with | some (s + 1) => some s | _ => none)
            (fun x ↦ match sel x with
              | some 0 => FreeM.liftBind a fun u₂ ↦ FreeM.map (fun x₂ ↦ F x 0 x₂ u u₂) (next u₂)
              | _ => D x)
            (fun x s ↦ F x (s + 1)) dflt := by
        unfold rhs
        simp only [sem, dite_true]
        change FreeM.liftBind a _ = _
        congr 1
        funext u
        rw [FreeM.bind_assoc]
        congr 1
        funext p
        rcases hs : sel p.1 with _ | _ | s
        · simp only [FreeM.bind, hs]
        · simp only [FreeM.bind, hs]
          congr 1
          funext u₂
          rw [← FreeM.bind_pure_comp, FreeM.bind_assoc, ← FreeM.bind_pure_comp]
          rfl
        · simp only [FreeM.bind, hs]
      rw [hl, hr]
      congr 1
      funext u
      exact lhs_eq_rhs a (next u) _ _ _ _
    · have hl : lhs t (FreeM.liftBind a next) sel D F dflt =
          FreeM.liftBind a fun u ↦ lhs t (next u) sel D F dflt := by
        unfold lhs
        rw [withPath_liftBind_bind]
        congr 1
        funext u
        congr 1
        funext p
        simp only [output_liftBind]
        rcases hs : sel (output (next u) p) with _ | s
        · rfl
        · simp only
          rw [locateAt?_liftBind_other h]
          rcases hloc : locateAt? t (next u) p s with _ | loc
          · rfl
          · simp only [Option.map_some]
            rw [map_complete (Located.prependOther h u loc).occurrence (fun x₂ a₂ ↦
                F (output (next u) p) s x₂ (Located.prependOther h u loc).completion.answer a₂),
              map_complete loc.occurrence (fun x₂ a₂ ↦
                F (output (next u) p) s x₂ loc.completion.answer a₂)]
            rfl
      have hr : rhs t (FreeM.liftBind a next) sel D F dflt =
          FreeM.liftBind a fun u ↦ rhs t (next u) sel D F dflt := by
        unfold rhs
        simp only [sem, h, dite_false]
        rfl
      rw [hl, hr]
      congr 1
      funext u
      exact lhs_eq_rhs t (next u) _ _ _ _

end Free


section Spec

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ] {Ψ : OracleSpec ι} {X : OracleSpec κ}
  {α : Type}

/-- **An extra oracle answered by a fixed function**: the queries of `Ψ` forwarded, those of `X`
answered by `c`. -/
def col (c : (x : κ) → X.Range x) : QueryImpl (Ψ + X) (OracleComp Ψ)
  | .inl i => FreeM.lift (P := Ψ.toPFunctor) i
  | .inr x => pure (c x)

/-- The fork's semantic form of an oracle computation. -/
abbrev semO {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} (t : ι) (prog : OracleComp spec α) :
    OracleComp spec (α × (ℕ → OracleComp spec (Option (α × spec.Range t × spec.Range t)))) :=
  sem (P := spec.toPFunctor) t prog

theorem col_inl_bind (c : (x : κ) → X.Range x) {β : Type} (i : ι)
    (k : Ψ.Range i → OracleComp Ψ β) :
    (col (Ψ := Ψ) c (.inl i) >>= k) = FreeM.liftBind i k := rfl

theorem simulateQ_col_liftBind_inl (c : (x : κ) → X.Range x) {β : Type} (i : ι)
    (next : Ψ.Range i → OracleComp (Ψ + X) β) :
    simulateQ (col c) (FreeM.liftBind (P := (Ψ + X).toPFunctor) (.inl i) next) =
      FreeM.liftBind (P := Ψ.toPFunctor) i fun u ↦ simulateQ (col c) (next u) := rfl

theorem simulateQ_col_liftBind_inr (c : (x : κ) → X.Range x) {β : Type} (x : κ)
    (next : X.Range x → OracleComp (Ψ + X) β) :
    simulateQ (col c) (FreeM.liftBind (P := (Ψ + X).toPFunctor) (.inr x) next) =
      simulateQ (col c) (next (c x)) := rfl

/-- **The semantic form commutes with answering `X` by `c`.** -/
theorem map_collapse_sem (c : (x : κ) → X.Range x) (t : ι) :
    (prog : OracleComp (Ψ + X) α) →
      FreeM.map (fun p ↦ (p.1, fun s ↦ simulateQ (col c) (p.2 s)))
          (simulateQ (col c) (semO (spec := Ψ + X) (.inl t) prog)) =
        semO (spec := Ψ) t (simulateQ (col c) prog)
  | .pure x => rfl
  | .liftBind (.inr x) next => by
    have h : (Sum.inr x : ι ⊕ κ) ≠ .inl t := by simp
    simp only [semO, sem, h, dite_false]
    rw [simulateQ_col_liftBind_inr, simulateQ_col_liftBind_inr]
    exact map_collapse_sem c t (next (c x))
  | .liftBind (.inl a) next => by
    by_cases h : a = t
    · subst h
      simp only [semO, sem, dite_true]
      rw [simulateQ_col_liftBind_inl, simulateQ_col_liftBind_inl]
      simp only [FreeM.map, sem, dite_true]
      congr 1
      funext u
      have ih := map_collapse_sem c a (next u)
      simp only [semO] at ih
      rw [← ih]
      rw [show ∀ {γ δ : Type} (x : OracleComp (Ψ + X) γ) (g : γ → OracleComp (Ψ + X) δ),
          simulateQ (col c) (FreeM.bind x g) =
            FreeM.bind (simulateQ (col c) x) fun a ↦ simulateQ (col c) (g a) from
        fun x g ↦ simulateQ_bind _ x g]
      rw [← FreeM.bind_pure_comp, FreeM.bind_assoc, ← FreeM.bind_pure_comp, FreeM.bind_assoc]
      congr 1
      funext p
      change FreeM.pure _ = FreeM.pure _
      congr 1
      refine Prod.ext rfl (funext fun s ↦ ?_)
      rcases s with _ | s
      · change simulateQ (col c) (FreeM.liftBind (P := (Ψ + X).toPFunctor) (.inl a) _) = _
        rw [simulateQ_col_liftBind_inl]
        congr 1
        funext u₂
        exact simulateQ_map (col c) (next u₂) (fun x₂ ↦ some (x₂, u, u₂))
      · rfl
    · have h' : (Sum.inl a : ι ⊕ κ) ≠ .inl t := by simpa using h
      simp only [semO, sem, h', dite_false]
      rw [simulateQ_col_liftBind_inl, simulateQ_col_liftBind_inl]
      simp only [FreeM.map, sem, h, dite_false]
      congr 1
      funext u
      exact map_collapse_sem c t (next u)

end Spec

section ContextFork

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [∀ t, DecidableEq (spec.Range t)]
  {α : Type}

/-- The fork's accepted pairs: different answers at the occurrence, and both outputs select it. -/
def forkObs {qb : ι → ℕ} {i : ι} (cf : α → Option (Fin (qb i + 1))) (x₁ : α) (s : ℕ) (x₂ : α)
    (a₁ a₂ : spec.Range i) : Option (α × α) :=
  if a₁ = a₂ then none
  else if (cf x₁).map Fin.val = some s ∧ (cf x₂).map Fin.val = some s then some (x₁, x₂) else none

theorem map_val_eq_some_iff {n : ℕ} (o : Option (Fin n)) (k : Fin n) :
    o.map Fin.val = some k.val ↔ o = some k := by
  constructor
  · intro h
    rcases o with _ | o
    · cases h
    · simp only [Option.map_some, Option.some.injEq] at h
      rw [Fin.ext h]
  · rintro rfl; rfl

/-- **The replay fork read from a first path** (VCVio's `contextFork`, unfolded). -/
theorem contextFork_eq_lhs (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    contextFork main qb i cf = lhs (P := spec.toPFunctor) i main (fun x ↦ (cf x).map Fin.val)
      (fun _ ↦ FreeM.pure none) (forkObs (spec := spec) cf) none := by
  have e1 : contextFork main qb i cf = contextForkByClassify main qb i cf := by
    unfold contextFork contextForkWitness contextForkByClassify
    rw [PFunctor.FreeM.Cursor.filterMapLocateAndForkSelected_eq_filterMapLocateAndForkBy]
    unfold PFunctor.FreeM.Cursor.filterMapLocateAndForkBy
    rw [← PFunctor.FreeM.comp_map,
      PFunctor.FreeM.Cursor.map_locateAndForkBy,
      PFunctor.FreeM.Cursor.map_locateAndForkBy]
    apply congrArg (PFunctor.FreeM.bind (PFunctor.FreeM.withPath main))
    funext path
    rcases hcf : cf (PFunctor.FreeM.output main path) with _ | s
    · rfl
    · rcases hlocate : PFunctor.FreeM.Cursor.locateAt?
          (P := spec.toPFunctor) i main path s with _ | located
      · simp [hlocate]
      · simp only [hlocate]
        apply congrArg (fun f => PFunctor.FreeM.map f located.fork)
        funext view
        simp only [Function.comp_apply, Option.join, Option.map]
        unfold acceptContextForkWitness classifyForkView
        split <;> split <;> simp_all
        grind
  rw [e1]
  unfold contextForkByClassify lhs
  rw [PFunctor.FreeM.Cursor.filterMapLocateAndForkBy_eq_bind_complete]
  congr 1
  funext path
  rcases hcf : cf (output main path) with _ | k
  · simp only [hcf, Option.map_none]; rfl
  · simp only [hcf, Option.map_some]
    rcases hl : locateAt? i main path k.val with _ | loc
    · rw [hl]; rfl
    · rw [hl]
      change FreeM.map _ loc.occurrence.complete = FreeM.map _ loc.occurrence.complete
      congr 1
      funext second
      have hp := loc.path_eq
      unfold classifyForkView forkObs
      simp only [ForkView.firstPath_mk, ForkView.secondPath_mk, ForkView.firstAnswer_mk,
        ForkView.secondAnswer_mk, hp, map_val_eq_some_iff]

end ContextFork

section Collapse

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ] {Ψ : OracleSpec ι} {X : OracleSpec κ}
  [∀ t, DecidableEq (Ψ.Range t)] [∀ x, DecidableEq (X.Range x)] {α : Type}

/-- **Forking a program whose extra oracle is answered by a fixed function `c` is answering it by
`c` in the fork of the program**, whose two completions query the extra oracle. -/
theorem contextFork_collapse (c : (x : κ) → X.Range x) (main : OracleComp (Ψ + X) α)
    (qb : ι ⊕ κ → ℕ) (t : ι) (cf : α → Option (Fin (qb (.inl t) + 1))) :
    contextFork (simulateQ (col c) main) (fun i ↦ qb (.inl i)) t cf =
      simulateQ (col c) (contextFork main qb (.inl t) cf) := by
  rw [contextFork_eq_lhs, contextFork_eq_lhs, lhs_eq_rhs, lhs_eq_rhs]
  unfold rhs
  have hs := map_collapse_sem c t main
  simp only [semO] at hs
  rw [← hs]
  rw [show ∀ {γ δ : Type} (x : OracleComp (Ψ + X) γ) (g : γ → OracleComp (Ψ + X) δ),
      simulateQ (col c) (FreeM.bind x g) =
        FreeM.bind (simulateQ (col c) x) fun a ↦ simulateQ (col c) (g a) from
    fun x g ↦ simulateQ_bind _ x g]
  rw [← FreeM.bind_pure_comp, FreeM.bind_assoc]
  congr 1
  funext p
  change (match (cf p.1).map Fin.val with
    | none => FreeM.pure none
    | some s => _) = simulateQ (col c) (match (cf p.1).map Fin.val with
    | none => FreeM.pure none
    | some s => _)
  rcases (cf p.1).map Fin.val with _ | s
  · rfl
  · change FreeM.bind (simulateQ (col c) (p.2 s)) _ = simulateQ (col c) (FreeM.bind (p.2 s) _)
    rw [show ∀ {γ δ : Type} (x : OracleComp (Ψ + X) γ) (g : γ → OracleComp (Ψ + X) δ),
        simulateQ (col c) (FreeM.bind x g) =
          FreeM.bind (simulateQ (col c) x) fun a ↦ simulateQ (col c) (g a) from
      fun x g ↦ simulateQ_bind _ x g]
    congr 1
    funext o
    rcases o with _ | q
    · rfl
    · rfl

end Collapse

end LeanDa.Fork
