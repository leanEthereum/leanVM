module

public import Quantum.StdModel.Qrom.CpreLaw

@[expose] public section

/-!
# Runtime 1 runs the CPRE template realized at the table

At the hidden values `θ = thetaOf s v`, runtime 1 with record ports, the honest cells of
`(P, s, v)` hardwired, runs the realized template `realizeT θ (cpreT C P …)` with the law of the
read program of `gameθ` (`runtime1R_cpreT_eq`). With `probAvg_cpre_slRed_eq_reads` the QROM CPRE
game of a straight-line reduction is the average of runtime 1 on the realized template
(`probAvg_cpre_slRed_eq_runtime1R`), the left side of the hidden-value hybrid.

* **Records** (`dropRec_cpreT`): the realized template drops to `gameD θ` over `hwSpec` with
  memory `Unit`: reveals become their values, the reads keep the memory
  (`dropRec_readSub_cmd`, the read substitution with `updC` against `keepAll`).
* **Programs** (`dropsTo_gameD`): every program of `gameD θ` hardwires an honest cell with its
  value, so `gameD θ` is the read program of `gameθ` with program calls inserted.
-/

open IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Quantum.StdModel.Qrom.CpreQ

open Quantum Quantum.Qrom Props HashSig
open Quantum.Sponge (spongeHardwiredReadRuntime keepMem hwSpec HwProg)
open Quantum.Xmss.Hybrid (uavg LazyProg restrictTo)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtime1R realizeT readLift readLiftQ revealThen
  progThen RevealVals DropRec realizeT_bind realizeT_bind₂ dropRec_realizeT_act_bind liftReadC
  liftReadProg liftReadLens DropsTo dropsTo_liftReadProg progCall ProgOf
  evalDistMap_runtime1R_eq evalDistMap_runtime1_eq_spongeHardwiredReadRuntime tmplLens readLens
  substitute_substitute dropRec_substitute)

variable {Par Tw J Val Fn Out : Type} {Msg : Fn → Type} {ch : Chains Par Tw J Val}

/-! ## Dropping the reads' memory updates -/

section reads

/-- `DropRec` steps on two programs: normalize both heads, then match the command. -/
local macro "drop_prim" : tactic => `(tactic| (
  (conv => arg 2; whnf); (conv => arg 3; whnf);
  refine dropRec_liftBind_prim _ fun _ ↦ ?_))
local macro "drop_sponge" : tactic => `(tactic| (
  (conv => arg 2; whnf); (conv => arg 3; whnf);
  refine dropRec_liftBind_sponge _ _ _ fun _ ↦ ?_))
local macro "drop_readH" : tactic => `(tactic| (
  (conv => arg 2; whnf); (conv => arg 3; whnf);
  refine dropRec_liftBind_readH _ _ _ _ fun _ _ ↦ ?_))
local macro "drop_pure" : tactic => `(tactic| (
  (conv => arg 2; whnf); (conv => arg 3; whnf);
  exact DropRec.pure _))

/-- **One command of the read substitution**: realized from the template with the policy
`updC`, it drops to the read substitution keeping the memory `Unit`. -/
theorem dropRec_readSub_cmd (θ : (s : CSrc ch) → CD ch s) (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)).A A) :
    DropRec (CSrc ch) (realizeT θ (readLift goodC (readSub updC A c)))
      (liftReadProg (readSub (keepAll Caller Unit) A c)) := by
  rcases c with o | ⟨p | ⟨tag, n | z⟩, E, ℓ⟩
  · drop_prim
    drop_pure
  · drop_sponge
    drop_pure
  · drop_prim
    drop_prim
    drop_pure
  · drop_prim
    drop_readH
    drop_prim
    drop_pure

/-- **A read program of tagged calls**, realized from the template with the policy `updC`,
drops to the read program keeping the memory `Unit`. -/
theorem dropRec_readLift_substitute (θ : (s : CSrc ch) → CD ch s) {Ω : QReg → Type}
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A) :
    DropRec (CSrc ch) (realizeT θ (readLift goodC (IFreeM.substitute (readSub updC) x)))
      (liftReadProg (IFreeM.substitute (readSub (keepAll Caller Unit)) x)) := by
  simp only [realizeT, readLift, liftReadProg]
  rw [← IFreeM.substitute_toSubstitution, ← IFreeM.substitute_toSubstitution,
    ← IFreeM.substitute_toSubstitution, substitute_substitute, substitute_substitute,
    substitute_substitute]
  refine dropRec_substitute (fun A c ↦ ?_) x
  have h := dropRec_readSub_cmd θ A c
  simp only [realizeT, readLift, liftReadProg, ← IFreeM.substitute_toSubstitution,
    substitute_substitute] at h
  exact h

/-- `dropRec_readLift_substitute` for fixed final registers. -/
theorem dropRec_readLift_toReads (θ : (s : CSrc ch) → CD ch s) {A B : QReg} {α : Type}
    (x : QComp (MixSpec Caller) A B α) :
    DropRec (CSrc ch) (realizeT θ (readLiftQ goodC (toReads updC x)))
      (liftReadC (toReads (keepAll Caller Unit) x)) :=
  dropRec_readLift_substitute θ x

end reads

/-! ## The realized template without reveals -/

section drop

variable [Fintype J] [DecidableEq J] [Inhabited Val] (θ : (s : CSrc ch) → CD ch s)

omit [Fintype J] [DecidableEq J] [Inhabited Val] in
/-- A reveal is dropped, its continuation at the values of `θ`. -/
theorem dropRec_revealThen' {B C : QReg} {α : Type} (T : Finset (CSrc ch))
    (k : RevealVals (CD ch) T × (Finset (CSrc ch) × JMem) → QComp (TSpec ch) B C α)
    {y : QComp (hwSpec HashOutput HashDomain Unit) B C α}
    (h : ∀ r, DropRec (CSrc ch) (realizeT θ (k (restrictTo T θ, r))) y) :
    DropRec (CSrc ch) (realizeT θ (revealThen goodC T k)) y :=
  DropRec.record T B _ _ (fun a ↦ Equiv.apply_symm_apply _ a) h

omit [Fintype J] [DecidableEq J] [Inhabited Val] in
/-- A template program port becomes the program call it realizes. -/
theorem dropRec_progThen' {B C : QReg} {α : Type}
    (p : LazyProg HashOutput HashDomain (CSrc ch) (CD ch)) {k : QComp (TSpec ch) B C α}
    {y : QComp (hwSpec HashOutput HashDomain Unit) B C α} (h : DropRec (CSrc ch) (realizeT θ k) y) :
    DropRec (CSrc ch) (realizeT θ (progThen p trivial k))
      ((progCall (p.realize θ) B).bind fun _ ↦ y) :=
  DropRec.prog (p.realize θ) B (Equiv.uniqueProd B Unit).symm
    (k := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ realizeT θ k)
    (k' := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ y)
    fun _ ↦ DropRec.prim _ fun _ ↦ h

omit [Fintype J] [DecidableEq J] [Inhabited Val] in
theorem dropRec_map {B C : QReg} {α β : Type} {x : QComp (TSpec ch) B C α}
    {y : QComp (hwSpec HashOutput HashDomain Unit) B C α} (h : DropRec (CSrc ch) (realizeT θ x) y)
    (f : α → β) : DropRec (CSrc ch) (realizeT θ (x.map f)) (y.map f) := by
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure, realizeT_bind₂]
  exact DropRec.bind₂ h fun _ ↦ DropRec.pure _

/-- **The honest cells of chain `j` from `ν`, hardwired** (realized). -/
noncomputable def progFromD (P : Par) (B : QReg) (j : J) (ν : ℕ) :
    QComp (hwSpec HashOutput HashDomain Unit) B B Unit :=
  if h : ν < ch.len j then
    (progCall ((progP P ⟨j, ⟨ν, h⟩⟩).realize θ) B).bind fun _ ↦ progFromD P B j (ν + 1)
  else QuantumComp₂.pure ()
termination_by ch.len j - ν

omit [Fintype J] [DecidableEq J] [Inhabited Val] in
theorem dropRec_pure_eq {B : QReg} {α : Type} {a b : α} (h : a = b) :
    DropRec (CSrc ch) (realizeT θ (QuantumComp₂.pure (L := LocalSig.instruments.{0})
      (spec := TSpec ch) (A := B) a)) (QuantumComp₂.pure b) := by
  subst h
  exact DropRec.pure _

omit [Fintype J] in
theorem dropRec_progFrom (P : Par) (B : QReg) (j : J) :
    ∀ ν, DropRec (CSrc ch) (realizeT θ (progFrom (ch := ch) P B j ν)) (progFromD θ P B j ν) := by
  intro ν
  induction h : ch.len j - ν generalizing ν with
  | zero =>
    rw [progFrom, dite_eq_right (by omega), progFromD, dite_eq_right (by omega)]
    exact DropRec.pure _
  | succ n ih =>
    have hν : ν < ch.len j := by omega
    rw [progFrom, dite_eq_left hν, progFromD, dite_eq_left hν]
    exact dropRec_progThen' θ _ (ih (ν + 1) (by omega))

omit [Fintype J] in
theorem cval_extendR {T : Finset (CSrc ch)} {j : J} {ν : ℕ} (h : ν ≤ ch.len j)
    (hT : srcOf j ν h ∈ T) : cval (extendR (restrictTo T θ)) j ν = cval θ j ν :=
  cval_congr h (extendR_restrictTo θ hT)

omit [Inhabited Val] in
theorem srcOf_mem_openSet {j : J} {μ : ℕ} (h : μ ≤ ch.len j) : srcOf j μ h ∈ openSet ch j μ := by
  simp [openSet, h]

omit [Fintype J] [DecidableEq J] [Inhabited Val] in
theorem srcOf_mem_endSet {j : J} : srcOf j (ch.len j) le_rfl ∈ endSet ch j :=
  Finset.mem_singleton_self _

/-- **The value of chain `j` at `μ`, realized**: the programs of an opening, then the value. -/
noncomputable def valueD (P : Par) (B : QReg) (j : J) (μ : ℕ) :
    QComp (hwSpec HashOutput HashDomain Unit) B B Val :=
  if μ < ch.len j then (progFromD θ P B j μ).bind fun _ ↦ QuantumComp₂.pure (cval θ j μ)
  else QuantumComp₂.pure (cval θ j (ch.len j))

theorem dropRec_valueT (P : Par) (B : QReg) (j : J) (μ : ℕ) :
    DropRec (CSrc ch) (realizeT θ (valueT (ch := ch) P B j μ)) (valueD θ P B j μ) := by
  unfold valueT valueD
  split_ifs with hμ
  · refine dropRec_revealThen' θ _ _ fun r ↦ ?_
    rw [realizeT_bind₂]
    refine DropRec.bind₂ (dropRec_progFrom θ P B j μ) fun _ ↦ ?_
    exact dropRec_pure_eq θ (cval_extendR θ hμ.le (srcOf_mem_openSet hμ.le))
  · refine dropRec_revealThen' θ _ _ fun r ↦ ?_
    exact dropRec_pure_eq θ (cval_extendR θ le_rfl srcOf_mem_endSet)

/-- The challenger's reads keeping the memory `Unit`. -/
noncomputable def keepD {α : Type} (B : QReg) (oa : OracleComp romWorld.Oracles α) :
    QComp (hwSpec HashOutput HashDomain Unit) B B α :=
  liftReadC (toReads (keepAll Caller Unit) (oa.toQuantumAt (mixImpl .answer B)))

/-- **An evaluation, realized**: at a step tweak the programs of the chain, then the reads. -/
noncomputable def evalD (C : TwColl Par Tw Fn Msg Out) (P : Par) (B : QReg) (l : Fn) (t : Tw)
    (m : Msg l) : QComp (hwSpec HashOutput HashDomain Unit) B B Out :=
  @dite _ (ch.IsStepTweak t) (Classical.propDecidable _)
    (fun h ↦ (progFromD θ P B h.choose 0).bind fun _ ↦ keepD B (C.eval romWorld l P t m))
    (fun _ ↦ keepD B (C.eval romWorld l P t m))

theorem dropRec_evalT (C : TwColl Par Tw Fn Msg Out) (P : Par) (B : QReg) (l : Fn) (t : Tw)
    (m : Msg l) :
    DropRec (CSrc ch) (realizeT θ (evalT (ch := ch) C P B l t m)) (evalD θ C P B l t m) := by
  unfold evalT evalD
  by_cases h : ch.IsStepTweak t
  · rw [dite_eq_left h, dite_eq_left h]
    refine dropRec_revealThen' θ _ _ fun r ↦ ?_
    rw [realizeT_bind₂]
    exact DropRec.bind₂ (dropRec_progFrom θ P B _ 0) fun _ ↦ dropRec_readLift_toReads θ _
  · rw [dite_eq_right h, dite_eq_right h]
    exact dropRec_readLift_toReads θ _

/-- **The challenger's answers, realized.** -/
noncomputable def ansD (C : TwColl Par Tw Fn Msg Out) (P : Par) (B : QReg) :
    (q : CpreQuery J Tw Fn Msg) →
      QComp (hwSpec HashOutput HashDomain Unit) B B (CpreQuery.Resp Par Val Out q)
  | .value j μ => valueD θ P B j μ
  | .eval l t m => evalD θ C P B l t m
  | .reveal => QuantumComp₂.pure P

theorem dropRec_ansT (C : TwColl Par Tw Fn Msg Out) (P : Par) (B : QReg)
    (q : CpreQuery J Tw Fn Msg) :
    DropRec (CSrc ch) (realizeT θ (ansT (ch := ch) C P B q)) (ansD θ C P B q) := by
  cases q with
  | value j μ => exact dropRec_valueT θ P B j μ
  | eval l t m => exact dropRec_evalT θ C P B l t m
  | reveal => exact DropRec.pure _

/-- **The reduction's oracles, realized.** -/
noncomputable def dImpl (C : TwColl Par Tw Fn Msg Out) (P : Par) (B : QReg) :
    QueryImpl (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (StateT (QueryLog (CQ Par Tw J Val Fn Msg Out))
        (QComp (hwSpec HashOutput HashDomain Unit) B B))
  | .inl i => fun log ↦ (liftReadC (toReads (keepAll Caller Unit) (mixImpl .red B i))).map
      fun a ↦ (a, log)
  | .inr q' => fun log ↦ (ansD θ C P B q').map fun a ↦ (a, log ++ [⟨q', a⟩])

theorem dropRec_tImplRun {α : Type} (C : TwColl Par Tw Fn Msg Out) (P : Par) (B : QReg)
    (x : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) α)
    (log : QueryLog (CQ Par Tw J Val Fn Msg Out)) :
    DropRec (CSrc ch) (realizeT θ ((simulateQ (tImpl (ch := ch) C P B) x).run log))
      ((simulateQ (dImpl θ C P B) x).run log) := by
  induction x using OracleComp.inductionOn generalizing log with
  | pure a => exact DropRec.pure _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with i | q'
    · change DropRec (CSrc ch) (realizeT θ (QuantumComp₂.bind ((readLiftQ goodC
          (toReads updC (mixImpl .red B i))).map fun a ↦ (a, log)) fun p ↦
            (simulateQ (tImpl (ch := ch) C P B) (k p.1)).run p.2))
        (QuantumComp₂.bind ((liftReadC (toReads (keepAll Caller Unit) (mixImpl .red B i))).map
          fun a ↦ (a, log)) fun p ↦ (simulateQ (dImpl θ C P B) (k p.1)).run p.2)
      rw [realizeT_bind₂]
      exact DropRec.bind₂ (dropRec_map θ (dropRec_readLift_toReads θ _) _) fun _ ↦ ih _ _
    · change DropRec (CSrc ch) (realizeT θ (QuantumComp₂.bind ((ansT C P B q').map
          fun a ↦ (a, log ++ [⟨q', a⟩])) fun p ↦
            (simulateQ (tImpl (ch := ch) C P B) (k p.1)).run p.2))
        (QuantumComp₂.bind ((ansD θ C P B q').map fun a ↦ (a, log ++ [⟨q', a⟩])) fun p ↦
          (simulateQ (dImpl θ C P B) (k p.1)).run p.2)
      rw [realizeT_bind₂]
      exact DropRec.bind₂ (dropRec_map θ (dropRec_ansT θ C P B q') _) fun _ ↦ ih _ _

variable {Q St : Type} {R : OracleSpec.{0, 0} Q}

/-- The reduction's answer to the adversary's classical call, realized. -/
noncomputable def dTree (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (s : St × QueryLog (CQ Par Tw J Val Fn Msg Out)) (q : Q) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E) :
    QComp (hwSpec HashOutput HashDomain Unit) A
      (QReg.of ((advSpec romWorld.spec R).Out (.call q) × E))
      (R.Range q × (St × QueryLog (CQ Par Tw J Val Fn Msg Out))) :=
  (QComp.act (spec := hwSpec HashOutput HashDomain Unit)
    (B := QReg.of ((advSpec romWorld.spec R).Out (.call q) × E)) (SubInstrument.relabel ℓ)).bind
      fun _ ↦ ((simulateQ (dImpl θ C P _) (σ s.1 q)).run s.2).map fun r ↦ (r.1.1, (r.1.2, r.2))

/-- **The adversary run by the reduction, realized.** -/
noncomputable def dRun {X Y : QReg → Type} (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (leaf : ∀ u, X u → St × QueryLog (CQ Par Tw J Val Fn Msg Out) → Y u) :
    {A : QReg} →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A →
      St × QueryLog (CQ Par Tw J Val Fn Msg Out) →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Unit))
        Y A
  | _, .pure x, s => .pure (leaf _ x s)
  | A, .liftBind (.prim o) next, s =>
      QuantumComp.bind (liftReadProg (readSub (keepAll Caller Unit) A (.prim o))) fun _ b ↦
        b.2 ▸ dRun C P σ leaf (next b.1) s
  | A, .liftBind (.query (.hash p) E ℓ) next, s =>
      QuantumComp.bind (liftReadProg (readSub (keepAll Caller Unit) A (.query (.hash p) E ℓ)))
        fun _ b ↦ b.2 ▸ dRun C P σ leaf (next b.1) s
  | _, .liftBind (.query (.call q) E ℓ) next, s =>
      QuantumComp.bind (dTree θ C P σ s q E ℓ) fun _ l ↦
        l.1 ▸ dRun C P σ leaf (next ⟨l.2.1⟩) l.2.2

omit [Fintype J] [DecidableEq J] [Inhabited Val] in
/-- Sequencing a fixed-register program in a general continuation. -/
theorem dropRec_bind_leaf {A B : QReg} {α : Type} {Ω : QReg → Type}
    {x : QComp (TSpec ch) A B α} {y : QComp (hwSpec HashOutput HashDomain Unit) A B α}
    (h : DropRec (CSrc ch) (realizeT θ x) y)
    {k : ∀ u, QuantumComp₂.Leaf B α u →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (TSpec ch)) Ω u}
    {k' : ∀ u, QuantumComp₂.Leaf B α u →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Unit))
        Ω u}
    (hk : ∀ u l, DropRec (CSrc ch) (realizeT θ (k u l)) (k' u l)) :
    DropRec (CSrc ch) (realizeT θ (QuantumComp.bind x k)) (QuantumComp.bind y k') := by
  have e := realizeT_bind (Λ := LocalSig.instruments.{0}) θ
    (x : QuantumComp LocalSig.instruments.{0} (TSpec ch) (QuantumComp₂.Leaf B α) A) k
  exact e ▸ DropRec.bind h hk

theorem dropRec_tRun {X Y : QReg → Type} (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (leaf : ∀ u, X u → St × QueryLog (CQ Par Tw J Val Fn Msg Out) → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A)
    (s : St × QueryLog (CQ Par Tw J Val Fn Msg Out)) :
    DropRec (CSrc ch) (realizeT θ (tRun (ch := ch) C P σ leaf x s)) (dRun θ C P σ leaf x s) := by
  induction x using IFreeM.inductionOn generalizing s with
  | pure _ _ =>
    rw [tRun, dRun]
    exact DropRec.pure _
  | liftBind A c next ih =>
    rcases c with o | ⟨p | q, E, ℓ⟩
    · rw [tRun, dRun, realizeT_bind]
      refine DropRec.bind (dropRec_readSub_cmd θ A (.prim o)) fun u b ↦ ?_
      obtain ⟨b, e⟩ := b
      subst e
      exact ih b s
    · rw [tRun, dRun, hashT, realizeT_bind]
      refine DropRec.bind (dropRec_readSub_cmd θ A (.query (.hash p) E ℓ)) fun u b ↦ ?_
      obtain ⟨b, e⟩ := b
      subst e
      exact ih b s
    · rw [tRun, dRun]
      refine dropRec_bind_leaf θ (dropRec_realizeT_act_bind θ _ fun _ ↦
        dropRec_map θ (dropRec_tImplRun θ C P _ _ _) _) fun u l ↦ ?_
      obtain ⟨e, l⟩ := l
      subst e
      exact ih _ _

/-- The adversary run, realized, returning the value, the handler state and the transcript. -/
noncomputable def dRunL (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St) {A B : QReg} {α : Type}
    (x : QComp (advSpec romWorld.spec R) A B α) (s : St)
    (log : QueryLog (CQ Par Tw J Val Fn Msg Out)) :
    QComp (hwSpec HashOutput HashDomain Unit) A B
      ((α × St) × QueryLog (CQ Par Tw J Val Fn Msg Out)) :=
  dRun θ C P σ (Y := QuantumComp₂.Leaf B ((α × St) × QueryLog (CQ Par Tw J Val Fn Msg Out)))
    (fun _ l q ↦ ⟨l.1, ((l.2, q.1), q.2)⟩) x (s, log)

/-- **The decision, realized**: the forgery's walk by reads keeping the memory, then the
decision with the honest values of `θ`. -/
noncomputable def judgeD (P : Par) (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out))
    (out : J × ℕ × Val) :
    QComp (hwSpec HashOutput HashDomain Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  (liftReadC (toReads (keepAll Caller Unit) ((ch.walk romWorld P out.1 out.2.1
    (ch.len out.1 - out.2.1) out.2.2).toQuantumAt (mixImpl .judge _)))).bind fun e' ↦
    QuantumComp₂.pure (holds (CpreValid ch log ∧ out.2.1 < ch.len out.1 ∧
      e' = cval θ out.1 (ch.len out.1) ∧
      (OpenedAtOrBelow log out.1 out.2.1 → out.2.2 ≠ cval θ out.1 out.2.1)))

omit [Fintype J] in
theorem dropRec_judgeT (P : Par) (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out))
    (out : J × ℕ × Val) :
    DropRec (CSrc ch) (realizeT θ (judgeT (ch := ch) P log out)) (judgeD θ P log out) := by
  obtain ⟨j, μ, z⟩ := out
  rw [judgeT, judgeD, realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_readLift_toReads θ _) fun e' ↦ ?_
  refine dropRec_revealThen' θ _ _ fun r ↦ dropRec_pure_eq θ ?_
  have he : cval (extendR (restrictTo (judgeSet ch log j μ) θ)) j (ch.len j) =
      cval θ j (ch.len j) :=
    cval_extendR θ le_rfl (Finset.mem_union_left _ srcOf_mem_endSet)
  refine congrArg holds (propext (and_congr_right fun _ ↦ and_congr_right fun hμ ↦ ?_))
  rw [he]
  refine and_congr_right fun _ ↦ imp_congr_right fun hO ↦ ?_
  dsimp only at hμ hO ⊢
  have hmem : srcOf j μ hμ.le ∈ judgeSet ch log j μ := by
    simp only [judgeSet]
    rw [dite_eq_left ⟨hμ.le, hO⟩]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  rw [cval_extendR θ hμ.le hmem]

/-- **The realized template game without reveals.** -/
noncomputable def gameD {S0 F : Type} (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    QComp (hwSpec HashOutput HashDomain Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind ((simulateQ (dImpl θ C P _) pre).run []) fun p ↦
    QuantumComp₂.bind (dRunL θ C P σ (adv p.1) (st0 p.1) p.2) fun r ↦
      QuantumComp₂.bind ((simulateQ (dImpl θ C P _) (post p.1 r.1.1 r.1.2)).run r.2) fun o ↦
        judgeD θ P o.2 o.1

/-- **The realized template drops to `gameD`.** -/
theorem dropRec_cpreT {S0 F : Type} (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    DropRec (CSrc ch) (realizeT θ (cpreT (ch := ch) C P pre adv st0 σ post))
      (gameD θ C P pre adv st0 σ post) := by
  rw [cpreT, gameD, realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_tImplRun θ C P _ pre []) fun p ↦ ?_
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_tRun θ C P σ _ _ _) fun r ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_tImplRun θ C P _ _ _) fun o ↦ dropRec_judgeT θ P _ _

end drop

/-! ## The read program of `gameθ` with program calls inserted -/

section progs

variable {T M : Type}

theorem toReads_bind₂ (upd : T → HashDomain → M → Option HashOutput → M) {A B C : QReg}
    {α β : Type} (x : QComp (MixSpec T) A B α) (k : α → QComp (MixSpec T) B C β) :
    toReads upd (x.bind k) = QuantumComp₂.bind (toReads upd x) fun a ↦ toReads upd (k a) := by
  have h := IFreeM.substitute_bind (readSub upd)
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec T))
      (QuantumComp₂.Leaf B α) A) (fun _ p ↦ p.casesOn fun h a ↦ h ▸ k a)
  refine h.trans ?_
  congr 1
  funext u p
  rcases p with ⟨rfl, a⟩
  rfl

theorem toReads_map (upd : T → HashDomain → M → Option HashOutput → M) {A B : QReg}
    {α β : Type} (x : QComp (MixSpec T) A B α) (f : α → β) :
    toReads upd (x.map f) = (toReads upd x).map f := by
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure, toReads_bind₂]
  rfl

end progs

section progs2

variable [DecidableEq J] [Inhabited Val] {L : Quantum.Sponge.Hw HashOutput HashDomain}

theorem dropsTo_map {B C : QReg} {α β : Type}
    {x : QComp (hwSpec HashOutput HashDomain Unit) B C α}
    {y : QComp (Quantum.Sponge.hwReadSpec HashOutput HashDomain Unit) B C α}
    (h : DropsTo L x y) (f : α → β) : DropsTo L (x.map f) (y.map f) := by
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure]
  exact DropsTo.bind₂ h fun _ ↦ DropsTo.pure _

variable (θ : (s : CSrc ch) → CD ch s) {P : Par}
  (hL : ∀ p : CPos ch, ProgOf L ((progP P p).realize θ))
include hL

theorem dropsTo_progFromD (B : QReg) (j : J) {α : Type}
    {x : QComp (hwSpec HashOutput HashDomain Unit) B B α}
    {y : QComp (Quantum.Sponge.hwReadSpec HashOutput HashDomain Unit) B B α}
    (h : DropsTo L x y) :
    ∀ ν, DropsTo L ((progFromD θ P B j ν).bind fun _ ↦ x) y := by
  intro ν
  induction hn : ch.len j - ν generalizing ν with
  | zero =>
    rw [progFromD, dite_eq_right (by omega), QuantumComp₂.pure_bind]
    exact h
  | succ n ih =>
    have hν : ν < ch.len j := by omega
    rw [progFromD, dite_eq_left hν, QuantumComp₂.bind_assoc]
    exact DropsTo.progCall_bind _ (hL _) (ih (ν + 1) (by omega))

theorem dropsTo_ansD (C : TwColl Par Tw Fn Msg Out) (B : QReg) (q : CpreQuery J Tw Fn Msg) :
    DropsTo L (ansD θ C P B q)
      (toReads (keepAll Caller Unit) ((ansθ C P θ q).toQuantumAt (mixImpl .answer B))) := by
  cases q with
  | value j μ =>
    change DropsTo L (valueD θ P B j μ) (QuantumComp₂.pure (cval θ j (min μ (ch.len j))))
    unfold valueD
    split_ifs with hμ
    · rw [min_eq_left hμ.le]
      exact dropsTo_progFromD θ hL B j (DropsTo.pure _) μ
    · rw [min_eq_right (by omega)]
      exact DropsTo.pure _
  | eval l t m =>
    change DropsTo L (evalD θ C P B l t m) _
    unfold evalD
    by_cases h : ch.IsStepTweak t
    · rw [dite_eq_left h]
      exact dropsTo_progFromD θ hL B _ (dropsTo_liftReadProg L _) 0
    · rw [dite_eq_right h]
      exact dropsTo_liftReadProg L _
  | reveal => exact DropsTo.pure _

theorem dropsTo_dImplRun (C : TwColl Par Tw Fn Msg Out) (B : QReg) {α : Type}
    (x : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) α)
    (log : QueryLog (CQ Par Tw J Val Fn Msg Out)) :
    DropsTo L ((simulateQ (dImpl θ C P B) x).run log)
      (toReads (keepAll Caller Unit) ((simulateQ (redImpl (ansθ C P θ) B) x).run log)) := by
  induction x using OracleComp.inductionOn generalizing log with
  | pure a => exact DropsTo.pure _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with i | q'
    · change DropsTo L (QuantumComp₂.bind ((liftReadC (toReads (keepAll Caller Unit)
          (mixImpl .red B i))).map fun a ↦ (a, log)) fun p ↦
            (simulateQ (dImpl θ C P B) (k p.1)).run p.2)
        (toReads (keepAll Caller Unit) (QuantumComp₂.bind ((mixImpl .red B i).map
          fun a ↦ (a, log)) fun p ↦ (simulateQ (redImpl (ansθ C P θ) B) (k p.1)).run p.2))
      rw [toReads_bind₂, toReads_map]
      exact DropsTo.bind₂ (dropsTo_map (dropsTo_liftReadProg L _) _) fun _ ↦ ih _ _
    · change DropsTo L (QuantumComp₂.bind ((ansD θ C P B q').map
          fun a ↦ (a, log ++ [⟨q', a⟩])) fun p ↦ (simulateQ (dImpl θ C P B) (k p.1)).run p.2)
        (toReads (keepAll Caller Unit) (QuantumComp₂.bind
          (((ansθ C P θ q').toQuantumAt (mixImpl .answer B)).map
            fun a ↦ (a, log ++ [⟨q', a⟩])) fun p ↦
              (simulateQ (redImpl (ansθ C P θ) B) (k p.1)).run p.2))
      rw [toReads_bind₂, toReads_map]
      exact DropsTo.bind₂ (dropsTo_map (dropsTo_ansD θ hL C B q') _) fun _ ↦ ih _ _

variable {Q St : Type} {R : OracleSpec.{0, 0} Q}

omit [DecidableEq J] [Inhabited Val] hL in
theorem toReads_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    toReads (keepAll Caller Unit) (QComp.act (spec := MixSpec Caller) p) = QComp.act p :=
  rfl

omit hL in
/-- Sequencing a fixed-register program in a general continuation, against the read program. -/
theorem dropsTo_bind_leaf {A B : QReg} {α : Type} {Ω : QReg → Type}
    {x : QComp (hwSpec HashOutput HashDomain Unit) A B α} {y : QComp (MixSpec Caller) A B α}
    (h : DropsTo L x (toReads (keepAll Caller Unit) y))
    {k : ∀ u, QuantumComp₂.Leaf B α u →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Unit))
        Ω u}
    {k' : ∀ u, QuantumComp₂.Leaf B α u →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω u}
    (hk : ∀ u l, DropsTo L (k u l) (IFreeM.substitute (readSub (keepAll Caller Unit)) (k' u l))) :
    DropsTo L (QuantumComp.bind x k)
      (IFreeM.substitute (readSub (keepAll Caller Unit)) (QuantumComp.bind y k')) := by
  have e := IFreeM.substitute_bind (readSub (keepAll Caller Unit))
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller))
      (QuantumComp₂.Leaf B α) A) k'
  exact e ▸ DropsTo.bind h hk

theorem dropsTo_dRun {X Y : QReg → Type} (C : TwColl Par Tw Fn Msg Out)
    (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (leaf : ∀ u, X u → St × QueryLog (CQ Par Tw J Val Fn Msg Out) → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A)
    (s : St × QueryLog (CQ Par Tw J Val Fn Msg Out)) :
    DropsTo L (dRun θ C P σ leaf x s)
      (IFreeM.substitute (readSub (keepAll Caller Unit))
        (mixRun (mixTrees (ansθ C P θ) σ) leaf x s)) := by
  induction x using IFreeM.inductionOn generalizing s with
  | pure _ _ =>
    rw [dRun, mixRun]
    exact DropsTo.pure _
  | liftBind A c next ih =>
    rcases c with o | ⟨p | q, E, ℓ⟩
    · rw [dRun, mixRun]
      refine DropsTo.bind (dropsTo_liftReadProg L _) fun u b ↦ ?_
      obtain ⟨b, e⟩ := b
      subst e
      exact ih b s
    · rw [dRun, mixRun]
      refine DropsTo.bind (dropsTo_liftReadProg L _) fun u b ↦ ?_
      obtain ⟨b, e⟩ := b
      subst e
      exact ih b s
    · rw [dRun, mixRun]
      have ht : DropsTo L (dTree θ C P σ s q E ℓ)
          (toReads (keepAll Caller Unit) (mixTrees (ansθ C P θ) σ s q E ℓ)) := by
        rw [dTree, mixTrees, toReads_bind₂, toReads_act, QComp.act_bind, QComp.act_bind]
        refine DropsTo.prim _ fun _ ↦ ?_
        rw [toReads_map]
        exact dropsTo_map (dropsTo_dImplRun θ hL C _ _ _) _
      refine dropsTo_bind_leaf ht fun u l ↦ ?_
      obtain ⟨e, l⟩ := l
      subst e
      exact ih _ _

omit [DecidableEq J] [Inhabited Val] hL in
theorem dropsTo_judgeD (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)) (out : J × ℕ × Val) :
    DropsTo L (judgeD θ P log out)
      (toReads (keepAll Caller Unit) ((judgeθ P θ log out).toQuantumAt (mixImpl .judge _))) := by
  rw [judgeθ, OracleComp.toQuantumAt, simulateQ_map, QuantumComp₂.map_eq, toReads_map, judgeD,
    ← QuantumComp₂.map_eq_bind_pure]
  exact dropsTo_map (dropsTo_liftReadProg L _) _

/-- **`gameD` is the read program of `gameθ` with program calls inserted.** -/
theorem dropsTo_gameD {S0 F : Type} (C : TwColl Par Tw Fn Msg Out)
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    DropsTo L (gameD θ C P pre adv st0 σ post)
      (toReads (keepAll Caller Unit) (gameθ C P θ pre adv st0 σ post)) := by
  rw [gameθ, mixNormal, toReads_bind₂, toReads_bind₂, QuantumComp₂.bind_assoc, gameD]
  refine DropsTo.bind₂ (dropsTo_dImplRun θ hL C _ pre []) fun p ↦ ?_
  rw [toReads_bind₂, QuantumComp₂.bind_assoc]
  refine DropsTo.bind₂ (dropsTo_dRun θ hL C σ _ _ _) fun r ↦ ?_
  exact DropsTo.bind₂ (dropsTo_dImplRun θ hL C _ _ _) fun o ↦ dropsTo_judgeD θ _ _

end progs2

/-! ## Runtime 1 on the realized template -/

section main

variable [Fintype J] [DecidableEq J] [Inhabited Val] {Q St S0 F : Type} {R : OracleSpec.{0, 0} Q}

omit [Fintype J] in
/-- Every honest cell is a hardwired cell of the lazy table, with its value. -/
theorem progOf_lazyT (P : Par) (s : J → Val)
    (hinj : ∀ θ, Function.Injective (cellOf (ch := ch) P θ)) (v : CPos ch → HashOutput)
    (p : CPos ch) : ProgOf ((lazyT P s hinj).hwOf v) ((progP P p).realize (thetaOf s v)) := by
  rw [realize_progP]
  exact (lazyT P s hinj).tableDb_cell v v p

/-- **Runtime 1 runs the realized template as the read program of `gameθ`**: with the honest
cells of `(P, s, v)` hardwired, from any memory. -/
theorem runtime1R_cpreT_eq (C : TwColl Par Tw Fn Msg Out) (P : Par) (s : J → Val)
    (hinj : ∀ θ, Function.Injective (cellOf (ch := ch) P θ)) (v : CPos ch → HashOutput)
    (m₀ : Finset (CSrc ch) × JMem)
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    (runtime1R HashOutput HashDomain ((lazyT P s hinj).hwOf v) m₀).evalDistMap .instruments
        (realizeT (thetaOf s v) (cpreT (ch := ch) C P pre adv st0 σ post)) (SubState.basis ())
        (fun p ↦ p.2.2) =
      (spongeHardwiredReadRuntime HashOutput HashDomain ((lazyT P s hinj).hwOf v) ()).evalDistMap
        .instruments (toReads (keepAll Caller Unit) (gameθ C P (thetaOf s v) pre adv st0 σ post))
        (SubState.basis ()) (fun p ↦ p.2.2) :=
  (evalDistMap_runtime1R_eq _ m₀ (dropRec_cpreT (thetaOf s v) C P pre adv st0 σ post) _ _).trans
    (evalDistMap_runtime1_eq_spongeHardwiredReadRuntime _ ()
      (dropsTo_gameD (thetaOf s v) (progOf_lazyT P s hinj v) C pre adv st0 σ post) _ _)

/-- **The QROM CPRE game of a straight-line reduction is runtime 1 on the realized template**,
averaged over the parameter, the starts and the honest outputs. -/
theorem probAvg_cpre_slRed_eq_runtime1R [Fintype Par] [SampleableType Par] [Fintype Val]
    [SampleableType Val] (C : TwColl Par Tw Fn Msg Out) (hlen : StepLen ch)
    (hinj : ∀ P θ, Function.Injective (cellOf (ch := ch) P θ)) (m₀ : Finset (CSrc ch) × JMem)
    (pre : Unit → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Unit → S0 → St) (σ : Unit → HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : Unit → S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    romWorld.probAvg ((cpre romWorld ch C).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) =
      uavg fun P : Par ↦ uavg fun s : J → Val ↦ uavg fun v : CPos ch → HashOutput ↦
        (runtime1R HashOutput HashDomain ((lazyT P s (hinj P)).hwOf v) m₀).evalDistMap
          .instruments (realizeT (thetaOf s v) (cpreT (ch := ch) C P (pre ()) (adv ()) (st0 ())
            (σ ()) (post ()))) (SubState.basis ()) (fun p ↦ p.2.2) {true} := by
  rw [probAvg_cpre_slRed_eq_reads C hlen hinj pre adv st0 σ post]
  refine congrArg uavg (funext fun P ↦ congrArg uavg (funext fun s ↦
    congrArg uavg (funext fun v ↦ ?_)))
  rw [runtime1R_cpreT_eq]

end main

end Quantum.StdModel.Qrom.CpreQ

end
