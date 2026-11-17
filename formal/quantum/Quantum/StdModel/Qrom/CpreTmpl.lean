module

public import Quantum.StdModel.Props.Cpre
public import Quantum.StdModel.Qrom.OffTweak
public import Quantum.Xmss.Assembly.Template

@[expose] public section

/-!
# The CPRE game in the QROM as a runtime-2 template

At a fixed public parameter `P`, the CPRE game against a QROM adversary is written as a template
program of the hidden-cell hybrid (`Quantum.Xmss.Assembly.Template`, at `X := HashOutput`,
`Z := HashDomain`), so that the hybrid's runtime 2 hardwires an honest chain cell only once the
chain is opened there.

* **Hidden coordinates** (`CSrc ch = J ⊕ CPos ch`, values `CD ch`): the chain starts (`Val`) and
  the full hash outputs of the honest cells `(j, ν)`, `ν < len j` (`CPos ch`). `cval θ j ν` is the
  chain value at `ν`, a function of the coordinate `srcOf j ν` only; `cellOf P θ p` the honest cell
  of position `p`.
* **Ports.** `progP P p` hardwires the honest cell of `p` with its output (`realize_progP`).
  `valueT`: an opening at `μ < len j` reveals `openSet j μ` (the value's source and the outputs of
  the cells from `μ`), hardwires the cells from `μ` and answers from the revealed values; a value
  at or above the end reveals the end's source only. `evalT`: an evaluation at a chain step tweak
  first opens that chain at `0` (such a transcript loses), then reads its cell like the challenger.
  `judgeT`: the forgery's walk by read ports recording each read cell and value in the memory
  (`recU`), then the revealed honest values decide.
* `cpreT P B`: the adversary against `challengeT P` (local operations and hash calls on port `h`),
  its classical transcript, then `judgeT`. `disc_cpreT`: it reveals before it programs.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

namespace Quantum.StdModel.Qrom.CpreQ

open Quantum Quantum.Qrom Props HashSig
open Quantum.Sponge (Hw HwRead HwProg hwReadSpec hwReadCmdSpec keepMem SpongePort)
open Quantum.Xmss.Hybrid (LazyProg restrictTo Agree)
open Quantum.Xmss.Assembly (tmplSpec revealThen progThen readLift readLiftQ RevealVals Disc
  disc_revealThen disc_progThen disc_readLift disc_act disc_bind disc₂_bind disc_substitute
  disc_queryBind disc_primBind disc_cast disc_mono)

variable {Par Tw J Val Fn Out : Type} {Msg : Fn → Type}

/-! ## Positions and hidden coordinates -/

section coords

variable (ch : Chains Par Tw J Val)

/-- **The chain positions** `(j, ν)`, `ν < len j`: the honest cells. -/
abbrev CPos : Type := Σ j : J, Fin (ch.len j)

/-- **The hidden coordinates**: the chain starts and the honest cells' outputs. -/
abbrev CSrc : Type := J ⊕ CPos ch

/-- A start is a chain value, an honest cell's output a hash output. -/
def CD : CSrc ch → Type :=
  Sum.elim (fun _ ↦ Val) (fun _ ↦ HashOutput)

variable [Fintype Val] [DecidableEq Val] [Inhabited Val]

instance instFintypeCD : (s : CSrc ch) → Fintype (CD ch s)
  | .inl _ => inferInstanceAs (Fintype Val)
  | .inr _ => inferInstanceAs (Fintype HashOutput)

instance instDecidableEqCD : (s : CSrc ch) → DecidableEq (CD ch s)
  | .inl _ => inferInstanceAs (DecidableEq Val)
  | .inr _ => inferInstanceAs (DecidableEq HashOutput)

instance instInhabitedCD : (s : CSrc ch) → Inhabited (CD ch s)
  | .inl _ => inferInstanceAs (Inhabited Val)
  | .inr _ => ⟨(0 : HashOutput)⟩

instance instNonemptyCD (s : CSrc ch) : Nonempty (CD ch s) :=
  ⟨default⟩

end coords

variable {ch : Chains Par Tw J Val}

/-- **The value of chain `j` at position `ν`** from the hidden values: the start at `0`, the
truncated output of the cell `(j, ν - 1)` above (the start beyond the chain). -/
def cval (θ : (s : CSrc ch) → CD ch s) (j : J) : ℕ → Val
  | 0 => θ (.inl j)
  | ν + 1 => if h : ν < ch.len j then ch.step.trunc (θ (.inr ⟨j, ⟨ν, h⟩⟩)) else θ (.inl j)

/-- **The source coordinate of the chain value at `ν ≤ len j`**: the start at `0`, the output of
the cell below otherwise. -/
def srcOf (j : J) : (ν : ℕ) → ν ≤ ch.len j → CSrc ch
  | 0, _ => .inl j
  | ν + 1, h => .inr ⟨j, ⟨ν, h⟩⟩

/-- The chain value at `ν ≤ len j` reads only its source coordinate. -/
theorem cval_congr {θ θ' : (s : CSrc ch) → CD ch s} {j : J} {ν : ℕ} (h : ν ≤ ch.len j)
    (hθ : θ (srcOf j ν h) = θ' (srcOf j ν h)) : cval θ j ν = cval θ' j ν := by
  cases ν with
  | zero => exact hθ
  | succ ν =>
    have h' : ν < ch.len j := h
    simp only [cval, h', ↓reduceDIte]
    exact congrArg ch.step.trunc hθ

/-- **The honest cell of position `p`** at the parameter `P`: the code of the step input. -/
def cellOf (P : Par) (θ : (s : CSrc ch) → CD ch s) (p : CPos ch) : HashDomain :=
  (encodeInput (ch.step.layout () P (ch.tweak p.1 p.2) (cval θ p.1 p.2))).getD 0

theorem cellOf_congr (P : Par) {θ θ' : (s : CSrc ch) → CD ch s} (p : CPos ch)
    (hθ : θ (srcOf p.1 p.2 p.2.isLt.le) = θ' (srcOf p.1 p.2 p.2.isLt.le)) :
    cellOf P θ p = cellOf P θ' p := by
  unfold cellOf
  rw [cval_congr p.2.isLt.le hθ]

variable [Fintype J] [DecidableEq J] [Inhabited Val]

/-- Revealed values extended to all coordinates by defaults. -/
noncomputable def extendR {T : Finset (CSrc ch)} (w : RevealVals (CD ch) T) :
    (s : CSrc ch) → CD ch s :=
  fun s ↦ if h : s ∈ T then w ⟨s, h⟩ else default

omit [Fintype J] in
theorem extendR_restrictTo {T : Finset (CSrc ch)} (θ : (s : CSrc ch) → CD ch s) {s : CSrc ch}
    (hs : s ∈ T) : extendR (restrictTo T θ) s = θ s := by
  simp only [extendR, hs, ↓reduceDIte, restrictTo]

/-! ## Program ports -/

/-- The coordinates of the program port of `p`: its input's source and its output. -/
def progNeed (p : CPos ch) : Finset (CSrc ch) :=
  {srcOf p.1 p.2 p.2.isLt.le, .inr p}

/-- **The template program port of position `p`**: hardwire its honest cell with its output. -/
noncomputable def progP (P : Par) (p : CPos ch) :
    LazyProg HashOutput HashDomain (CSrc ch) (CD ch) :=
  .programH (progNeed p) fun w ↦ (cellOf P (extendR w) p, extendR w (.inr p))

omit [Fintype J] in
theorem realize_progP (P : Par) (θ : (s : CSrc ch) → CD ch s) (p : CPos ch) :
    (progP P p).realize θ = .programH (cellOf P θ p) (θ (.inr p)) := by
  have h1 : cellOf P (extendR (restrictTo (progNeed p) θ)) p = cellOf P θ p :=
    cellOf_congr P p (extendR_restrictTo θ (by simp [progNeed]))
  have h2 : extendR (restrictTo (progNeed p) θ) (.inr p) = θ (.inr p) :=
    extendR_restrictTo θ (by simp [progNeed])
  simp only [progP, LazyProg.realize, h1]
  rw [h2]

/-! ## The template -/

/-- Every template program port is admitted. -/
def goodC : LazyProg HashOutput HashDomain (CSrc ch) (CD ch) → Prop :=
  fun _ ↦ True

/-- The inner memory: the cells and values the forgery's walk read. -/
abbrev JMem : Type := Finset (HashDomain × HashOutput)

variable (ch) in
/-- The template signature of the CPRE game. -/
abbrev TSpec : QuantumOracleSpec.{0, 0} :=
  tmplSpec HashOutput HashDomain (CSrc ch) (CD ch) JMem goodC

/-- The memory update of the forgery's walk: record the read cell with its value. -/
def recU (z : HashDomain) (m : JMem) : Option HashOutput → JMem
  | some y => insert (z, y) m
  | none => m

/-- **The read policies of runtime 2**: the decision's walk records, every other read keeps the
memory. -/
def updC : Caller → HashDomain → JMem → Option HashOutput → JMem
  | .judge, z => recU z
  | _, _ => keepMem

variable (ch) in
/-- **The coordinates an opening at `μ` reveals**: the source of the value at `μ` and the outputs
of the cells from `μ`. -/
noncomputable def openSet (j : J) (μ : ℕ) : Finset (CSrc ch) :=
  (if h : μ ≤ ch.len j then {srcOf j μ h} else ∅) ∪
    (Finset.univ.filter fun p : CPos ch ↦ p.1 = j ∧ μ ≤ p.2.val).image Sum.inr

variable (ch) in
/-- The coordinate of the end of chain `j`. -/
def endSet (j : J) : Finset (CSrc ch) :=
  {srcOf j (ch.len j) le_rfl}

/-- **Hardwire the honest cells of chain `j` from position `ν` upward.** -/
noncomputable def progFrom (P : Par) (B : QReg) (j : J) (ν : ℕ) : QComp (TSpec ch) B B Unit :=
  if h : ν < ch.len j then progThen (progP P ⟨j, ⟨ν, h⟩⟩) trivial (progFrom P B j (ν + 1))
  else QuantumComp₂.pure ()
termination_by ch.len j - ν

/-- **Open chain `j` at `μ`**: reveal `openSet j μ`, hardwire the cells from `μ`, continue with
the revealed values. -/
noncomputable def openT {α : Type} (P : Par) (B : QReg) (j : J) (μ : ℕ)
    (k : RevealVals (CD ch) (openSet ch j μ) → QComp (TSpec ch) B B α) :
    QComp (TSpec ch) B B α :=
  revealThen goodC (openSet ch j μ) fun r ↦ (progFrom P B j μ).bind fun _ ↦ k r.1

/-- **The value of chain `j` at `μ` in runtime 2**: an opening below the end, else the end's
source revealed. -/
noncomputable def valueT (P : Par) (B : QReg) (j : J) (μ : ℕ) : QComp (TSpec ch) B B Val :=
  if μ < ch.len j then openT P B j μ fun w ↦ QuantumComp₂.pure (cval (extendR w) j μ)
  else revealThen goodC (endSet ch j) fun r ↦
    QuantumComp₂.pure (cval (extendR r.1) j (ch.len j))

/-- The challenger's computation over the model's oracles by read ports keeping the memory. -/
noncomputable def keepReads {α : Type} (B : QReg) (oa : OracleComp romWorld.Oracles α) :
    QComp (TSpec ch) B B α :=
  readLiftQ goodC (toReads updC (oa.toQuantumAt (mixImpl .answer B)))

/-- **An evaluation in runtime 2**: at a chain step tweak, open that chain at `0` first; then the
challenger's evaluation by reads. -/
noncomputable def evalT (C : TwColl Par Tw Fn Msg Out) (P : Par) (B : QReg) (l : Fn) (t : Tw)
    (m : Msg l) : QComp (TSpec ch) B B Out :=
  @dite _ (ch.IsStepTweak t) (Classical.propDecidable _)
    (fun h ↦ openT P B h.choose 0 fun _ ↦ keepReads B (C.eval romWorld l P t m))
    (fun _ ↦ keepReads B (C.eval romWorld l P t m))

/-- **The answer of runtime 2's challenger** to a classical query. -/
noncomputable def ansT (C : TwColl Par Tw Fn Msg Out) (P : Par) (B : QReg) :
    (q : CpreQuery J Tw Fn Msg) → QComp (TSpec ch) B B (CpreQuery.Resp Par Val Out q)
  | .value j μ => valueT P B j μ
  | .eval l t m => evalT C P B l t m
  | .reveal => QuantumComp₂.pure P

/-! ## A straight-line reduction against the template challenger -/

section red

variable {Q St : Type} {R : OracleSpec.{0, 0} Q}

/-- The CPRE ports. -/
abbrev CQ (Par Tw J Val Fn : Type) (Msg : Fn → Type) (Out : Type) :=
  CpreSpec Par Tw J Val Fn Msg Out

/-- **The reduction's oracles in runtime 2**: a coin is a coin, a hash a read port keeping the
memory, a CPRE query the template answer `ansT`, logged. -/
noncomputable def tImpl (C : TwColl Par Tw Fn Msg Out) (P : Par) (B : QReg) :
    QueryImpl (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (StateT (QueryLog (CQ Par Tw J Val Fn Msg Out)) (QComp (TSpec ch) B B))
  | .inl i => fun log ↦ (readLiftQ goodC (toReads updC (mixImpl .red B i))).map
      fun a ↦ (a, log)
  | .inr q' => fun log ↦ (ansT C P B q').map fun a ↦ (a, log ++ [⟨q', a⟩])

/-- The reduction's answer to the adversary's classical call `q` in runtime 2: relabel, then the
handler against `tImpl`. -/
noncomputable def tTree (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (s : St × QueryLog (CQ Par Tw J Val Fn Msg Out)) (q : Q) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E) :
    QComp (TSpec ch) A (QReg.of ((advSpec romWorld.spec R).Out (.call q) × E))
      (R.Range q × (St × QueryLog (CQ Par Tw J Val Fn Msg Out))) :=
  (QComp.act (spec := TSpec ch) (B := QReg.of ((advSpec romWorld.spec R).Out (.call q) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦
      ((simulateQ (tImpl C P _) (σ s.1 q)).run s.2).map fun r ↦ (r.1.1, (r.1.2, r.2))

/-- An adversary's hash call as a template program: the read substitution's call of port `h`. -/
noncomputable def hashT {A : QReg} (p : romWorld.spec.Port) (E : QReg)
    (ℓ : A ≃ (advSpec romWorld.spec R).In (.hash p) × E) :
    IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (TSpec ch))
      (fun t ↦ {b : (QuantumComp.toIPFunctor LocalSig.instruments.{0}
          (advSpec romWorld.spec R)).B A (.query (.hash p) E ℓ) //
        (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)).src A
          (.query (.hash p) E ℓ) b = t}) A :=
  readLift goodC (readSub updC A (.query (.hash p) E ℓ))

/-- **The adversary run by the reduction in runtime 2**: local operations kept, hash calls on
port `h`, each classical call answered by the handler (`tTree`), as `mixRun`. -/
noncomputable def tRun {X Y : QReg → Type} (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (leaf : ∀ u, X u → St × QueryLog (CQ Par Tw J Val Fn Msg Out) → Y u) :
    {A : QReg} →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A →
      St × QueryLog (CQ Par Tw J Val Fn Msg Out) →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (TSpec ch)) Y A
  | _, .pure x, s => .pure (leaf _ x s)
  | A, .liftBind (.prim o) next, s =>
      QuantumComp.bind (readLift goodC (readSub updC A (.prim o))) fun _ b ↦
        b.2 ▸ tRun C P σ leaf (next b.1) s
  | _, .liftBind (.query (.hash p) E ℓ) next, s =>
      QuantumComp.bind (hashT p E ℓ) fun _ b ↦ b.2 ▸ tRun C P σ leaf (next b.1) s
  | _, .liftBind (.query (.call q) E ℓ) next, s =>
      QuantumComp.bind (tTree C P σ s q E ℓ) fun _ l ↦
        l.1 ▸ tRun C P σ leaf (next ⟨l.2.1⟩) l.2.2

/-- The adversary run by the reduction in runtime 2, returning the value, the handler state and
the transcript. -/
noncomputable def tRunL (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St) {A B : QReg} {α : Type}
    (x : QComp (advSpec romWorld.spec R) A B α) (s : St)
    (log : QueryLog (CQ Par Tw J Val Fn Msg Out)) :
    QComp (TSpec ch) A B ((α × St) × QueryLog (CQ Par Tw J Val Fn Msg Out)) :=
  tRun C P σ (Y := QuantumComp₂.Leaf B ((α × St) × QueryLog (CQ Par Tw J Val Fn Msg Out)))
    (fun _ l q ↦ ⟨l.1, ((l.2, q.1), q.2)⟩) x (s, log)

end red

open scoped Classical in
variable (ch) in
/-- The coordinates the decision reveals: the end, and the value at the forgery's position when
the chain is opened at or below it. -/
noncomputable def judgeSet (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)) (j : J) (μ : ℕ) :
    Finset (CSrc ch) :=
  endSet ch j ∪ (if h : μ ≤ ch.len j ∧ OpenedAtOrBelow log j μ then {srcOf j μ h.1} else ∅)

/-- **The decision in runtime 2**: walk the forgery `(j, μ, z)` by read ports recording the read
cells and values, then decide with the revealed end (and the revealed value at `μ` when the chain
is opened at or below `μ`). -/
noncomputable def judgeT (P : Par) (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out))
    (out : J × ℕ × Val) : QComp (TSpec ch) (QReg.of Unit) (QReg.of Unit) Bool :=
  (readLiftQ goodC (toReads updC ((ch.walk romWorld P out.1 out.2.1 (ch.len out.1 - out.2.1)
    out.2.2).toQuantumAt (mixImpl .judge _)))).bind fun e' ↦
    revealThen goodC (judgeSet ch log out.1 out.2.1) fun r ↦
      QuantumComp₂.pure (holds (CpreValid ch log ∧ out.2.1 < ch.len out.1 ∧
        e' = cval (extendR r.1) out.1 (ch.len out.1) ∧
        (OpenedAtOrBelow log out.1 out.2.1 → out.2.2 ≠ cval (extendR r.1) out.1 out.2.1)))

/-- **The CPRE game of a straight-line reduction in runtime 2, as a template**, at the parameter
`P`: the reduction's setup, the adversary run by its handler, its output (classical hash calls by
read ports keeping the memory, CPRE queries by the template challenger), then the decision. -/
noncomputable def cpreT {Q St S0 F : Type} {R : OracleSpec.{0, 0} Q}
    (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    QComp (TSpec ch) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind ((simulateQ (tImpl C P _) pre).run []) fun p ↦
    QuantumComp₂.bind (tRunL C P σ (adv p.1) (st0 p.1) p.2) fun r ↦
      QuantumComp₂.bind ((simulateQ (tImpl C P _) (post p.1 r.1.1 r.1.2)).run r.2) fun o ↦
        judgeT P o.2 o.1

/-! ## The template reveals before it programs -/

omit [Inhabited Val] in
theorem progNeed_subset_openSet {j : J} {μ ν : ℕ} (hμ : μ ≤ ν) (hν : ν < ch.len j) :
    progNeed (⟨j, ⟨ν, hν⟩⟩ : CPos ch) ⊆ openSet ch j μ := by
  intro s hs
  simp only [progNeed, Finset.mem_insert, Finset.mem_singleton] at hs
  simp only [openSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rcases hs with rfl | rfl
  · rcases Nat.eq_or_lt_of_le hμ with rfl | hlt
    · left
      simp [show μ ≤ ch.len j from hν.le]
    · cases ν with
      | zero => omega
      | succ ν => exact Or.inr ⟨⟨j, ⟨ν, hν.le⟩⟩, ⟨rfl, by simp; omega⟩, rfl⟩
  · exact Or.inr ⟨⟨j, ⟨ν, hν⟩⟩, ⟨rfl, hμ⟩, rfl⟩

theorem disc_progFrom (P : Par) (B : QReg) (j : J) (μ : ℕ) :
    ∀ ν, μ ≤ ν → ∀ T, openSet ch j μ ⊆ T → Disc (progFrom (ch := ch) P B j ν) T := by
  intro ν
  induction h : ch.len j - ν generalizing ν with
  | zero =>
    intro _ _ _
    rw [progFrom, dite_eq_right (by omega)]
    trivial
  | succ n ih =>
    intro hμ T hT
    have hν : ν < ch.len j := by omega
    rw [progFrom, dite_eq_left hν]
    exact disc_progThen _ trivial _ T ((progNeed_subset_openSet hμ hν).trans hT)
      (ih (ν + 1) (by omega) (by omega) T hT)

theorem disc_openT {α : Type} (P : Par) (B : QReg) (j : J) (μ : ℕ)
    (k : RevealVals (CD ch) (openSet ch j μ) → QComp (TSpec ch) B B α)
    (hk : ∀ r T, Disc (k r) T) (T : Finset (CSrc ch)) : Disc (openT P B j μ k) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _
    (disc_progFrom P B j μ μ le_rfl _ Finset.subset_union_right) fun _ _ _ ↦ hk _ _

omit [Fintype J] [Inhabited Val] in
theorem disc_keepReads {α : Type} (B : QReg) (oa : OracleComp romWorld.Oracles α)
    (T : Finset (CSrc ch)) : Disc (keepReads (ch := ch) B oa) T :=
  disc_readLift _ T

theorem disc_ansT (C : TwColl Par Tw Fn Msg Out) (P : Par) (B : QReg)
    (q : CpreQuery J Tw Fn Msg) (T : Finset (CSrc ch)) : Disc (ansT C P B q) T := by
  cases q with
  | value j μ =>
    show Disc (valueT P B j μ) T
    unfold valueT
    split_ifs
    · exact disc_openT P B j μ (fun w ↦ QuantumComp₂.pure (cval (extendR w) j μ))
        (fun _ _ ↦ by trivial) T
    · exact disc_revealThen _ _ T fun _ ↦ trivial
  | eval l t m =>
    show Disc (evalT C P B l t m) T
    unfold evalT
    by_cases h : ch.IsStepTweak t
    · rw [dite_eq_left h]
      exact disc_openT P B _ 0 _ (fun _ _ ↦ disc_keepReads _ _ _) T
    · rw [dite_eq_right h]
      exact disc_keepReads _ _ _
  | reveal => trivial

omit [Fintype J] [Inhabited Val] in
theorem disc_map {B C : QReg} {α β : Type} (x : QComp (TSpec ch) B C α) (f : α → β)
    {T : Finset (CSrc ch)} (hx : Disc x T) : Disc (x.map f) T := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact disc₂_bind _ _ hx fun _ _ _ ↦ trivial

theorem disc_tImplRun {α : Type} (C : TwColl Par Tw Fn Msg Out) (P : Par) (B : QReg)
    (x : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) α)
    (log : QueryLog (CQ Par Tw J Val Fn Msg Out)) (T : Finset (CSrc ch)) :
    Disc ((simulateQ (tImpl (ch := ch) C P B) x).run log) T := by
  induction x using OracleComp.inductionOn generalizing log T with
  | pure a => trivial
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with i | q'
    · change Disc (QuantumComp₂.bind ((readLiftQ goodC (toReads updC (mixImpl .red B i))).map
          fun a ↦ (a, log)) fun p ↦ (simulateQ (tImpl (ch := ch) C P B) (k p.1)).run p.2) T
      exact disc₂_bind _ _ (disc_map _ _ (disc_readLift _ T)) fun _ _ _ ↦ ih _ _ _
    · change Disc (QuantumComp₂.bind ((ansT C P B q').map fun a ↦ (a, log ++ [⟨q', a⟩]))
          fun p ↦ (simulateQ (tImpl (ch := ch) C P B) (k p.1)).run p.2) T
      exact disc₂_bind _ _ (disc_map _ _ (disc_ansT C P B q' T)) fun _ _ _ ↦ ih _ _ _

theorem disc_tRun {Q St : Type} {R : OracleSpec.{0, 0} Q} {X Y : QReg → Type}
    (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (leaf : ∀ u, X u → St × QueryLog (CQ Par Tw J Val Fn Msg Out) → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A)
    (s : St × QueryLog (CQ Par Tw J Val Fn Msg Out)) (T : Finset (CSrc ch)) :
    Disc (tRun (ch := ch) C P σ leaf x s) T := by
  induction x using IFreeM.inductionOn generalizing s T with
  | pure _ _ => rw [tRun]; exact trivial
  | liftBind _ c next ih =>
    rcases c with o | ⟨p | q, E, ℓ⟩
    · rw [tRun]
      refine disc_bind _ _ (disc_readLift _ T) fun _ b _ _ ↦ ?_
      obtain ⟨b, e⟩ := b
      subst e
      exact ih b s _
    · rw [tRun]
      refine disc_bind _ _ (disc_readLift _ T) fun _ b _ _ ↦ ?_
      obtain ⟨b, e⟩ := b
      subst e
      exact ih b s _
    · rw [tRun]
      refine disc_bind _ _ (disc₂_bind _ _ (disc_act _ T) fun _ _ _ ↦
        disc_map _ _ (disc_tImplRun C P _ _ _ _)) fun _ l _ _ ↦ ?_
      obtain ⟨e, l⟩ := l
      subst e
      exact ih _ _ _

omit [Fintype J] in
theorem disc_judgeT (P : Par) (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out))
    (out : J × ℕ × Val) (T : Finset (CSrc ch)) : Disc (judgeT (ch := ch) P log out) T :=
  disc₂_bind _ _ (disc_readLift _ T) fun _ _ _ ↦ disc_revealThen _ _ _ fun _ ↦ trivial

/-- **The template game reveals before it programs.** -/
theorem disc_cpreT {Q St S0 F : Type} {R : OracleSpec.{0, 0} Q} (C : TwColl Par Tw Fn Msg Out)
    (P : Par) (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) (T : Finset (CSrc ch)) :
    Disc (cpreT (ch := ch) C P pre adv st0 σ post) T :=
  disc₂_bind _ _ (disc_tImplRun C P _ pre [] T) fun _ _ _ ↦
    disc₂_bind _ _ (disc_tRun C P σ _ _ _ _) fun _ _ _ ↦
      disc₂_bind _ _ (disc_tImplRun C P _ _ _ _) fun _ _ _ ↦ disc_judgeT P _ _ _

end Quantum.StdModel.Qrom.CpreQ

end
