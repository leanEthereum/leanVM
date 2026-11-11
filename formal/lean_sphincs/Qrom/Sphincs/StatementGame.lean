module

public import Statement.LeanSphincsQrom
public import Qrom.Sphincs.Game
public import Sphincs.Bridge
public import Qrom.Sphincs.StatementAlgs

@[expose] public section

/-!
# The statement's game in the quantum random-oracle model is the proof's

The trusted game of `Statement/LeanSphincsQrom.lean` (`Sphincs.QuantumRandomOracleModel.winProb`)
and the proof's (`Qrom.Sphincs.winProb`) are one game in two sets of types: the same quantum random
oracle on the inputs of at most `2048` bytes, and classical ports for the public key and the signer
that differ only in the types of keys, signatures and logs (`Sphincs.Model.publicKeyEquiv`,
`Sphincs.Model.signatureEquiv`). A statement adversary becomes a proof adversary
(`Qrom.Sphincs.toQromAdversary`) by the command substitution `Qrom.Sphincs.portCalls`, which keeps
its local operations and hash calls and forwards each port call to the proof's port, reading the
answer back (`Qrom.Sphincs.resEquiv`); it keeps the call budget
(`Qrom.Sphincs.isTotalQueryBound_toQromAdversary`).

The two runtimes correspond through the relabelling of the signing log (`Qrom.Sphincs.regMap`),
since key generation and the signer agree through the maps (`Qrom.SphincsStatement.keysOn_fst`,
`Qrom.SphincsStatement.signOn_eq`): every run of a translated program is the run of the program,
relabelled (`Qrom.Sphincs.intertwines_run_portCalls`). The verifiers agree too
(`Qrom.SphincsStatement.verifyOn_eq`), and so do the logs' records of the forgery, so both games
give the same winning probability (`Qrom.Sphincs.winProb_eq_qrom`).
-/

open Matrix OracleSpec OracleComp FORS Quantum
open scoped Kronecker ENNReal

universe v w

namespace Qrom.Sphincs

attribute [local instance] _root_.Sphincs.Model.params

open _root_.Sphincs.Model (ofModelPublicKey toModelPublicKey ofModelSignature toModelSignature
  publicKeyEquiv signatureEquiv toModelForgery)

/-- The signing log's instances, found once: on the product registers they are large. -/
instance : DecidableEq Log := inferInstance
instance : Fintype Log := inferInstance

/-- A hash function on the proof's inputs as one on the statement's: the same function, the two
types of inputs and outputs being the same, and their groups both XOR. -/
abbrev asStmt (H : Input → HashOutput) :
    _root_.Sphincs.QuantumRandomOracleModel.Input →
      _root_.Sphincs.QuantumRandomOracleModel.Output :=
  H

/-- A message of the statement as the proof's: the same bit vector. -/
abbrev asMsg (m : HashSig.Message) : Message :=
  m

/-- The messages, the proof's as the statement's. -/
def msgEquiv : Message ≃ HashSig.Message :=
  Equiv.refl _

/-- **Key generation**, as `Qrom.SphincsStatement.keysOn_fst` with the statement's types. -/
theorem keysOn_fst (seed : MasterSeed) (H : Input → HashOutput) :
    (_root_.Sphincs.QuantumRandomOracleModel.keysOn seed (asStmt H)).1 =
      ofModelPublicKey (keysOf seed H).1 :=
  SphincsStatement.keysOn_fst seed H

/-- **The signer**, as `Qrom.SphincsStatement.signOn_eq` with the statement's types. -/
theorem signOn_eq (seed : MasterSeed) (H : Input → HashOutput) (m : HashSig.Message) :
    _root_.Sphincs.QuantumRandomOracleModel.signOn seed (asStmt H) m =
      Option.map ofModelSignature (signOf seed H (asMsg m)) :=
  SphincsStatement.signOn_eq seed H m

/-- **The verifier**, as `Qrom.SphincsStatement.verifyOn_eq` with the statement's types. -/
theorem verifyOn_eq (H : Input → HashOutput) (pk : _root_.Sphincs.PublicKey)
    (F : _root_.Sphincs.Forgery) :
    _root_.Sphincs.QuantumRandomOracleModel.verifyOn (asStmt H) pk F =
      evalWithAnswerFn (QueryImpl.ofFn (extend H))
        (FORS.Concrete.verify (toModelPublicKey pk) (asMsg F.message)
          (toModelSignature F.signature)) :=
  SphincsStatement.verifyOn_eq H pk F

/-! ## The ports and their answers -/

/-- A port of the statement's game as the proof's. -/
def portOf : _root_.Sphincs.QuantumRandomOracleModel.Port → Port
  | .publicKey => .pk
  | .sign m => .sign (asMsg m)

/-- The answers of a port, the proof's as the statement's. -/
def ansEquiv : (j : _root_.Sphincs.QuantumRandomOracleModel.Port) →
    Res (portOf j) ≃ _root_.Sphincs.QuantumRandomOracleModel.Answer j
  | .publicKey => publicKeyEquiv
  | .sign _ => Equiv.optionCongr signatureEquiv

/-- A log entry, the proof's as the statement's. -/
def entryEquiv :
    Message × Option FORS.Signature ≃ HashSig.Message × Option _root_.Sphincs.Signature :=
  msgEquiv.prodCongr (Equiv.optionCongr signatureEquiv)

/-- The signing logs, the proof's as the statement's, entry by entry. -/
def logEquiv : Log ≃ _root_.Sphincs.QuantumRandomOracleModel.Log :=
  (Equiv.listEquivOfEquiv entryEquiv).subtypeEquiv fun l ↦ by
    simp [Equiv.listEquivOfEquiv]
    rfl

/-- The result of a port, the proof's as the statement's. -/
def resEquiv (j : _root_.Sphincs.QuantumRandomOracleModel.Port) :
    Res (portOf j) × Log ≃ _root_.Sphincs.QuantumRandomOracleModel.Answer j ×
      _root_.Sphincs.QuantumRandomOracleModel.Log :=
  (ansEquiv j).prodCongr logEquiv

/-! ## The translation of programs -/

/-- Each command of a statement program as a proof program: local operations and hash calls are
kept, a port call goes to the corresponding port, its result read back by `resEquiv`. -/
noncomputable def portSubst :
    IPFunctor.CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{v}
        _root_.Sphincs.QuantumRandomOracleModel.spec)
      (QuantumComp.toIPFunctor LocalSig.instruments.{v} Spec)
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query (.inl u) F ℓ =>
      QuantumComp.queryBind (spec := Spec) (.inl u) F ℓ fun r ↦ QuantumComp.pure ⟨ULift.up r, rfl⟩
  | _, .query (.inr j) F ℓ =>
      QuantumComp.queryBind (spec := Spec) (.inr (portOf j)) F ℓ fun r ↦
        QuantumComp.pure ⟨ULift.up (resEquiv j r), rfl⟩

/-- **The translation of a statement program.** -/
noncomputable def portCalls {W : QReg → Type w} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} _root_.Sphincs.QuantumRandomOracleModel.spec W A) :
    QuantumComp LocalSig.instruments.{v} Spec W A :=
  IPFunctor.IFreeM.substitute portSubst x


/-- The translation of a fixed-register statement program. -/
noncomputable def portCalls₂ {A B : QReg} {α : Type w}
    (x : QuantumComp₂ LocalSig.instruments.{v} _root_.Sphincs.QuantumRandomOracleModel.spec A B α) :
    QuantumComp₂ LocalSig.instruments.{v} Spec A B α :=
  portCalls x

section calls

variable {W : QReg → Type w}

theorem portCalls_primBind {A : QReg} (o : LocalSig.instruments.{v}.Op A)
    (k : (b : LocalSig.instruments.{v}.Outcome o) →
      QuantumComp LocalSig.instruments.{v} _root_.Sphincs.QuantumRandomOracleModel.spec W
        (LocalSig.instruments.{v}.next o b)) :
    portCalls (QuantumComp.primBind o k) = QuantumComp.primBind o fun b ↦ portCalls (k b) :=
  rfl

theorem portCalls_queryBind_inl {A : QReg} (F : QReg)
    (ℓ : A ≃ _root_.Sphincs.QuantumRandomOracleModel.spec.In (.inl ()) × F)
    (k : _root_.Sphincs.QuantumRandomOracleModel.spec.Result (.inl ()) →
      QuantumComp LocalSig.instruments.{v} _root_.Sphincs.QuantumRandomOracleModel.spec W
        (QReg.of (_root_.Sphincs.QuantumRandomOracleModel.spec.Out (.inl ()) × F))) :
    portCalls (QuantumComp.queryBind (.inl ()) F ℓ k) =
      QuantumComp.queryBind (spec := Spec) (.inl ()) F ℓ fun r ↦ portCalls (k r) :=
  rfl

theorem portCalls_queryBind_inr {A : QReg} (j : _root_.Sphincs.QuantumRandomOracleModel.Port)
    (F : QReg) (ℓ : A ≃ _root_.Sphincs.QuantumRandomOracleModel.spec.In (.inr j) × F)
    (k : _root_.Sphincs.QuantumRandomOracleModel.spec.Result (.inr j) →
      QuantumComp LocalSig.instruments.{v} _root_.Sphincs.QuantumRandomOracleModel.spec W
        (QReg.of (_root_.Sphincs.QuantumRandomOracleModel.spec.Out (.inr j) × F))) :
    portCalls (QuantumComp.queryBind (.inr j) F ℓ k) =
      QuantumComp.queryBind (spec := Spec) (.inr (portOf j)) F ℓ fun r ↦
        portCalls (k (resEquiv j r)) :=
  rfl

/-- **The translation keeps the call budget.** -/
theorem isTotalQueryBound_portCalls {A : QReg}
    {x : QuantumComp LocalSig.instruments.{v} _root_.Sphincs.QuantumRandomOracleModel.spec W A}
    {n : ℕ} (hx : x.IsTotalQueryBound n) : (portCalls x).IsTotalQueryBound n := by
  refine IPFunctor.IFreeM.IsChargeBound.substitute portSubst (fun A c ↦ ?_) hx
  change QuantumComp.IsTotalQueryBound (portSubst A c) (QuantumComp.Cmd.queryCharge c)
  cases c with
  | prim o => simp [portSubst, QuantumComp.Cmd.queryCharge]
  | query i F ℓ =>
    rcases i with ⟨⟩ | j
    · exact (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
        ⟨Nat.one_pos, fun _ ↦ QuantumComp.isTotalQueryBound_pure _ _⟩
    · exact (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
        ⟨Nat.one_pos, fun _ ↦ QuantumComp.isTotalQueryBound_pure _ _⟩

end calls

/-! ## The translated adversary -/

/-- **The statement's adversary as the proof's.** On the FORS public key, the adversary runs on
the statement's key, its hash calls unchanged and its port calls forwarded to the proof's ports,
the answers read back through the maps of keys, signatures and logs; its forgery is read as the
model's. -/
noncomputable def toQromAdversary {A : QReg}
    (adv : _root_.Sphincs.QuantumRandomOracleModel.Adversary A) : Adversary A :=
  fun pk ↦ QuantumComp₂.map toModelForgery (portCalls₂ (adv (ofModelPublicKey pk)))

/-- **The translated adversary keeps the call budget.** -/
theorem isTotalQueryBound_toQromAdversary {A : QReg}
    {adv : _root_.Sphincs.QuantumRandomOracleModel.Adversary A} {n : ℕ}
    (h : ∀ pk, (adv pk).IsTotalQueryBound n) :
    ∀ pk, (toQromAdversary adv pk).IsTotalQueryBound n := fun pk ↦ by
  have h' := OvGame.isTotalQueryBound_bind₂ (m := 0) (portCalls₂ (adv (ofModelPublicKey pk)))
    (isTotalQueryBound_portCalls (h (ofModelPublicKey pk)))
    (k := fun F ↦ QuantumComp₂.pure (toModelForgery F))
    fun _ ↦ QuantumComp.isTotalQueryBound_pure _ _
  rw [Nat.add_zero, ← QuantumComp₂.map_eq_bind_pure] at h'
  exact h'

/-! ## The runtimes correspond -/

/-- The runtime registers, the statement's as the proof's. -/
def regEquiv : _root_.Sphincs.QuantumRandomOracleModel.Log × Unit ≃ Log × Unit :=
  logEquiv.symm.prodCongr (Equiv.refl Unit)

/-- The relabelling of the runtime register, from the statement's to the proof's. -/
noncomputable def regMap :
    MatrixMap (_root_.Sphincs.QuantumRandomOracleModel.Log × Unit) (Log × Unit) :=
  MatrixMap.conj (basisMatrix regEquiv)

theorem amplifyLeft_regMap (B : Type) [Fintype B] [DecidableEq B] :
    regMap.amplifyLeft B = MatrixMap.conj (basisMatrix ((Equiv.refl B).prodCongr regEquiv)) := by
  rw [regMap, MatrixMap.amplifyLeft_conj, one_kronecker_basisMatrix]
  rfl

theorem basisMatrix_equiv_mul_apply' {l m n : Type*} [Fintype m] [DecidableEq n] (e : m ≃ n)
    (M : Matrix m l ℂ) (i : n) (j : l) : (basisMatrix e * M) i j = M (e.symm i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm i)]
  · simp
  · intro b _ hb
    rw [basisMatrix_apply, ite_eq_right fun h ↦ hb (by rw [h, Equiv.symm_apply_apply]), zero_mul]
  · simp

theorem signatureLimit_eq : FORS.signatureLimit = _root_.Sphincs.signatureLimit := rfl

/-- **The ports correspond**: on the statement's log of a proof log, a port of the statement's game
answers what the proof's answers, read back. -/
theorem portTrans_logEquiv (seed : MasterSeed) (H : Input → HashOutput)
    (j : _root_.Sphincs.QuantumRandomOracleModel.Port) (l : Log) :
    _root_.Sphincs.QuantumRandomOracleModel.portTrans seed (asStmt H) j (logEquiv l) =
      resEquiv j ((realGame seed H).trans (portOf j) l) := by
  rw [show (realGame seed H).trans = portTrans (keysOf seed H).1 (signOf seed H) from rfl]
  cases j with
  | publicKey =>
    rw [_root_.Sphincs.QuantumRandomOracleModel.portTrans.eq_def, keysOn_fst]
    rfl
  | sign m =>
    have hlen : (logEquiv l).1.length = l.1.length := List.length_map _
    dsimp only [_root_.Sphincs.QuantumRandomOracleModel.portTrans, portOf, portTrans]
    by_cases h : l.1.length < FORS.signatureLimit
    · have h' : (logEquiv l).1.length < _root_.Sphincs.signatureLimit := by
        rw [hlen, ← signatureLimit_eq]
        exact h
      rw [dite_eq_left h', dite_eq_left h]
      refine Prod.ext (signOn_eq seed H m) (Subtype.ext ?_)
      change (logEquiv l).1 ++
          [(m, _root_.Sphincs.QuantumRandomOracleModel.signOn seed (asStmt H) m)] =
        List.map entryEquiv (l.1 ++ [(asMsg m, signOf seed H (asMsg m))])
      rw [List.map_append, signOn_eq seed H m]
      rfl
    · have h' : ¬ (logEquiv l).1.length < _root_.Sphincs.signatureLimit := by
        rw [hlen, ← signatureLimit_eq]
        exact h
      rw [dite_eq_right h', dite_eq_right h]
      rfl

/-- **A hash call**: the table oracles of the two runtimes commute with the relabelling. -/
theorem hashStep_regMap (seed : MasterSeed) (H : Input → HashOutput) :
    MatrixMap.conj (tableOracle fun t : Log × Unit ↦ (realGame seed H).answer t.1 H) ∘ₗ
        regMap.amplifyLeft (Input × HashOutput) =
      regMap.amplifyLeft (Input × HashOutput) ∘ₗ
        MatrixMap.conj (tableOracle (X := Input) (Y := HashOutput)
          fun _ : _root_.Sphincs.QuantumRandomOracleModel.Log × Unit ↦ H) := by
  rw [amplifyLeft_regMap, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul, tableOracle, tableOracle,
    ← basisMatrix_comp, ← basisMatrix_comp]
  rfl

theorem hashStep_branch_regMap (seed : MasterSeed) (H : Input → HashOutput)
    (u : Spec.Result (.inl ())) :
    (((realGame seed H).sampled H).step (.inl ())).branch u ∘ₗ
        regMap.amplifyLeft (Input × HashOutput) =
      regMap.amplifyLeft (Input × HashOutput) ∘ₗ
        ((_root_.Sphincs.QuantumRandomOracleModel.runtime seed (asStmt H)).step (.inl ())).branch
          u :=
  hashStep_regMap seed H

theorem sideKraus_realGame_apply (seed : MasterSeed) (H : Input → HashOutput) (j : Port)
    (r : Res j × Log) (s s' : Log) :
    (realGame seed H).sideKraus Unit j r ((), (s, ())) ((), (s', ())) =
      if ((realGame seed H).trans j r.2).1 = r.1 ∧ ((realGame seed H).trans j r.2).2 = s ∧
        r.2 = s' then 1 else 0 := by
  simp only [OvGame.sideKraus, Matrix.smul_apply, kroneckerMap_apply, Matrix.one_apply_eq,
    Matrix.single_apply, smul_eq_mul, one_mul, mul_one]
  by_cases h : ((realGame seed H).trans j r.2).1 = r.1 <;> simp [h]

theorem portKraus_apply (seed : MasterSeed) (H : Input → HashOutput)
    (j : _root_.Sphincs.QuantumRandomOracleModel.Port)
    (r : _root_.Sphincs.QuantumRandomOracleModel.Answer j ×
      _root_.Sphincs.QuantumRandomOracleModel.Log)
    (s s' : _root_.Sphincs.QuantumRandomOracleModel.Log) :
    _root_.Sphincs.QuantumRandomOracleModel.portKraus seed (asStmt H) j r ((), (s, ()))
        ((), (s', ())) =
      if (_root_.Sphincs.QuantumRandomOracleModel.portTrans seed (asStmt H) j r.2).1 = r.1 ∧
        (_root_.Sphincs.QuantumRandomOracleModel.portTrans seed (asStmt H) j r.2).2 = s ∧
        r.2 = s' then 1 else 0 := by
  simp only [_root_.Sphincs.QuantumRandomOracleModel.portKraus, Matrix.smul_apply,
    kroneckerMap_apply, Matrix.one_apply_eq, Matrix.single_apply, smul_eq_mul, one_mul, mul_one]
  by_cases h : (_root_.Sphincs.QuantumRandomOracleModel.portTrans seed (asStmt H) j r.2).1 = r.1 <;>
    simp [h]

/-- **A port call**: the Kraus operators of the two runtimes commute with the relabelling, the
proof's result read back by `resEquiv`. -/
theorem portKraus_regMap₀ (seed : MasterSeed) (H : Input → HashOutput)
    (j : _root_.Sphincs.QuantumRandomOracleModel.Port) (r : Res (portOf j) × Log) :
    MatrixMap.conj ((realGame seed H).sideKraus Unit (portOf j) r) ∘ₗ regMap.amplifyLeft Unit =
      regMap.amplifyLeft Unit ∘ₗ
        MatrixMap.conj
          (_root_.Sphincs.QuantumRandomOracleModel.portKraus seed (asStmt H) j (resEquiv j r)) := by
  rw [amplifyLeft_regMap, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
  refine congrArg MatrixMap.conj ?_
  ext ⟨⟨⟩, s₁, ⟨⟩⟩ ⟨⟨⟩, s₂, ⟨⟩⟩
  rw [mul_basisMatrix_apply, basisMatrix_equiv_mul_apply']
  change (realGame seed H).sideKraus Unit (portOf j) r ((), (s₁, ())) ((), (logEquiv.symm s₂, ())) =
    _root_.Sphincs.QuantumRandomOracleModel.portKraus seed (asStmt H) j (resEquiv j r)
      ((), (logEquiv s₁, ())) ((), (s₂, ()))
  rw [sideKraus_realGame_apply, portKraus_apply]
  obtain ⟨a, l⟩ := r
  have ht := portTrans_logEquiv seed H j l
  have hc : (((realGame seed H).trans (portOf j) l).1 = a ∧
      ((realGame seed H).trans (portOf j) l).2 = s₁ ∧ l = logEquiv.symm s₂) ↔
      ((_root_.Sphincs.QuantumRandomOracleModel.portTrans seed (asStmt H) j (logEquiv l)).1 =
          ansEquiv j a ∧
        (_root_.Sphincs.QuantumRandomOracleModel.portTrans seed (asStmt H) j (logEquiv l)).2 =
          logEquiv s₁ ∧ logEquiv l = s₂) := by
    rw [ht]
    simp only [resEquiv, Equiv.prodCongr_apply, Prod.map, EmbeddingLike.apply_eq_iff_eq,
      Equiv.eq_symm_apply]
  by_cases h : ((realGame seed H).trans (portOf j) l).1 = a ∧
      ((realGame seed H).trans (portOf j) l).2 = s₁ ∧ l = logEquiv.symm s₂
  · rw [ite_eq_left h]
    exact (ite_eq_left (hc.mp h)).symm
  · rw [ite_eq_right h]
    exact (ite_eq_right fun h' ↦ h (hc.mpr h')).symm

theorem portStep_branch_regMap (seed : MasterSeed) (H : Input → HashOutput)
    (j : _root_.Sphincs.QuantumRandomOracleModel.Port) (r : Spec.Result (.inr (portOf j))) :
    (((realGame seed H).sampled H).step (.inr (portOf j))).branch r ∘ₗ regMap.amplifyLeft Unit =
      regMap.amplifyLeft Unit ∘ₗ
        ((_root_.Sphincs.QuantumRandomOracleModel.runtime seed (asStmt H)).step (.inr j)).branch
          (resEquiv j r) :=
  portKraus_regMap₀ seed H j r

/-! ## The runs correspond -/

section run

open QuantumRuntime SubInstrument DSubInstrument

/-- A call, relabelled in and out, intertwines through `id ⊗ V` when the port's steps do. -/
theorem call_intertwines {A I O E D₁ D₂ ι₁ ι₂ : Type} [Fintype A] [DecidableEq A] [Fintype I]
    [DecidableEq I] [Fintype O] [DecidableEq O] [Fintype E] [DecidableEq E] [Fintype D₁]
    [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂] (ℓ : A ≃ I × E) (V : MatrixMap D₁ D₂)
    (s₁ : SubInstrument (I × D₁) (O × D₁) ι₁) (s₂ : SubInstrument (I × D₂) (O × D₂) ι₂) (r₁ : ι₁)
    (r₂ : ι₂) (h : s₂.branch r₂ ∘ₗ V.amplifyLeft I = V.amplifyLeft O ∘ₗ s₁.branch r₁)
    (ρ : Matrix (A × D₁) (A × D₁) ℂ) :
    (relabel (queryEquivOut O D₂ E)).branch ()
        ((s₂.frame E).branch r₂ ((relabel (queryEquivIn ℓ D₂)).branch () (V.amplifyLeft A ρ))) =
      V.amplifyLeft (O × E) ((relabel (queryEquivOut O D₁ E)).branch ()
        ((s₁.frame E).branch r₁ ((relabel (queryEquivIn ℓ D₁)).branch () ρ))) := by
  have h₁ := LinearMap.congr_fun (intertwines_relabel_queryEquivIn V ℓ ()) ρ
  have h₂ := LinearMap.congr_fun (congrArg (fun Φ ↦ MatrixMap.amplify Φ E) h)
    ((relabel (queryEquivIn ℓ D₁)).branch () ρ)
  have h₃ := LinearMap.congr_fun (intertwines_relabel_queryEquivOut V O E ())
    ((s₁.frame E).branch r₁ ((relabel (queryEquivIn ℓ D₁)).branch () ρ))
  simp only [LinearMap.comp_apply, MatrixMap.amplify_comp] at h₁ h₂ h₃
  rw [h₁, branch_frame_apply, h₂]
  exact h₃

/-- Sequencing intertwines when the first steps do through a bijection of their outcomes and the
continuations at corresponding outcomes do. -/
theorem intertwines_bind_equiv {X X' Y Y' ι ι' κ : Type*} [Fintype X] [Fintype X'] [Fintype Y]
    [Fintype Y'] {C C' : κ → Type*} [∀ c, Fintype (C c)] [∀ c, Fintype (C' c)]
    {L₁ : MatrixMap X X'} {L₂ : MatrixMap Y Y'} {L₃ : ∀ c, MatrixMap (C c) (C' c)}
    {p : SubInstrument X Y ι} {p' : SubInstrument X' Y' ι'} (e : ι' ≃ ι)
    {k : ι → DSubInstrument Y κ C} {k' : ι' → DSubInstrument Y' κ C'}
    (hp : ∀ i', p'.branch i' ∘ₗ L₁ = L₂ ∘ₗ p.branch (e i'))
    (hk : ∀ i', Intertwines L₂ L₃ (k (e i')) (k' i')) :
    Intertwines L₁ L₃ (DSubInstrument.bind p k) (DSubInstrument.bind p' k') :=
  fun c ↦ LinearMap.ext fun ρ ↦ by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, branch_bind_apply, branch_bind_apply,
    MatrixMap.map_tsum (L₃ c) (f := fun i ↦ (k i).branch c (p.branch i ρ))
      ((p.isCPTNIFamily.comp_eval (fun i ↦ (k i).isCPTNIFamily) c).summable_apply ρ),
    ← e.tsum_eq]
  refine tsum_congr fun i' ↦ ?_
  have h₁ := LinearMap.congr_fun (hp i') ρ
  have h₂ := LinearMap.congr_fun (hk i' c) (p.branch (e i') ρ)
  simp only [LinearMap.comp_apply] at h₁ h₂
  rw [h₁, h₂]

variable (seed : MasterSeed) (H : Input → HashOutput)

/-- **The runs correspond**: the translated program run against the proof's game after relabelling
the register is the program run against the statement's game, relabelled. -/
theorem intertwines_run_portCalls {W : QReg → Type w} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} _root_.Sphincs.QuantumRandomOracleModel.spec W A) :
    Intertwines (regMap.amplifyLeft A) (fun p : Σ u, W u ↦ regMap.amplifyLeft p.1)
      ((_root_.Sphincs.QuantumRandomOracleModel.runtime seed (asStmt H)).run .instruments x)
      (((realGame seed H).sampled H).run .instruments (portCalls x)) := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    exact Intertwines.ret
      (B := fun p : Σ u, W u ↦ p.1 × (_root_.Sphincs.QuantumRandomOracleModel.runtime seed
        (asStmt H)).D)
      (B' := fun p : Σ u, W u ↦ p.1 × ((realGame seed H).sampled H).D)
      (fun p ↦ regMap.amplifyLeft p.1) ⟨_, y⟩
  | primBind _ o k ih =>
    rw [portCalls_primBind, run_primBind, run_primBind]
    exact (Intertwines.frame_amplifyLeft _ regMap).bind ih
  | queryBind _ i F ℓ k ih =>
    rcases i with u | j
    · cases u
      rw [run_queryBind]
      refine Intertwines.bind (p' := ((realGame seed H).sampled H).queryStep (.inl ()) F ℓ)
        (k' := fun r ↦ ((realGame seed H).sampled H).run .instruments (portCalls (k r)))
        (fun u ↦ LinearMap.ext fun ρ ↦ ?_) ih
      exact (queryStep_branch_apply (R := (realGame seed H).sampled H) (.inl ()) F ℓ u _).trans
        ((call_intertwines ℓ regMap _ _ u u (hashStep_branch_regMap seed H u) ρ).trans (congrArg _
          (queryStep_branch_apply
            (R := _root_.Sphincs.QuantumRandomOracleModel.runtime seed (asStmt H)) (.inl ()) F ℓ
            u ρ).symm))
    · rw [run_queryBind]
      refine intertwines_bind_equiv (resEquiv j)
        (p' := ((realGame seed H).sampled H).queryStep (.inr (portOf j)) F ℓ)
        (k' := fun r ↦ ((realGame seed H).sampled H).run .instruments
          (portCalls (k (resEquiv j r))))
        (fun r ↦ LinearMap.ext fun ρ ↦ ?_) fun r ↦ ih (resEquiv j r)
      exact (queryStep_branch_apply (R := (realGame seed H).sampled H) (.inr (portOf j)) F ℓ r
        _).trans ((call_intertwines ℓ regMap _ _ _ r (portStep_branch_regMap seed H j r) ρ).trans
          (congrArg _ (queryStep_branch_apply
            (R := _root_.Sphincs.QuantumRandomOracleModel.runtime seed (asStmt H)) (.inr j) F ℓ
            (resEquiv j r) ρ).symm))

/-- The initial registers correspond. -/
theorem regMap_init :
    regMap (_root_.Sphincs.QuantumRandomOracleModel.runtime seed (asStmt H)).init.matrix =
      ((realGame seed H).sampled H).init.matrix := by
  change regMap (Matrix.single _root_.Sphincs.QuantumRandomOracleModel.Log.empty
      _root_.Sphincs.QuantumRandomOracleModel.Log.empty (1 : ℂ) ⊗ₖ Matrix.single () () 1) =
    Matrix.single Log.empty Log.empty (1 : ℂ) ⊗ₖ Matrix.single () () 1
  rw [Matrix.single_kronecker_single, Matrix.single_kronecker_single, one_mul, regMap,
    OvGame.conj_basisMatrix_single]
  rfl

/-- **The joint post-states correspond**: that of the translated program in the proof's game is
that of the program in the statement's game, its runtime register relabelled. -/
theorem matrix_jointPost_portCalls {W : QReg → Type w} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} _root_.Sphincs.QuantumRandomOracleModel.spec W A)
    (ρ : SubState A) (p : Σ u, W u) :
    (((realGame seed H).sampled H).jointPost .instruments (portCalls x) ρ p).matrix =
      regMap.amplifyLeft p.1
        ((_root_.Sphincs.QuantumRandomOracleModel.runtime seed (asStmt H)).jointPost .instruments x
          ρ p).matrix :=
  (congrArg ((((realGame seed H).sampled H).run .instruments (portCalls x)).branch p)
    ((MatrixMap.amplifyLeft_kronecker _ _ _).trans
      (congrArg (ρ.matrix ⊗ₖ ·) (regMap_init seed H))).symm).trans
    (LinearMap.congr_fun (intertwines_run_portCalls seed H x p)
      (ρ.matrix ⊗ₖ (_root_.Sphincs.QuantumRandomOracleModel.runtime seed (asStmt H)).init.matrix))

end run

/-! ## The adversary with its key -/

section withKey

open QuantumRuntime

theorem portCalls₂_bind {A B C : QReg} {α β : Type w}
    (x : QuantumComp₂ LocalSig.instruments.{v} _root_.Sphincs.QuantumRandomOracleModel.spec A B α)
    (k : α →
      QuantumComp₂ LocalSig.instruments.{v} _root_.Sphincs.QuantumRandomOracleModel.spec B C β) :
    portCalls₂ (x.bind k) = (portCalls₂ x).bind fun a ↦ portCalls₂ (k a) := by
  unfold portCalls₂ portCalls QuantumComp₂.bind IPFunctor.FreeM₂.bind
  refine (IPFunctor.IFreeM.substitute_bind portSubst
    (X := fun u ↦ PSigma fun _ : u = B ↦ α) x _).trans ?_
  congr 1
  funext t y
  obtain ⟨h, a⟩ := y
  cases h
  rfl

theorem portCalls₂_map {A B : QReg} {α β : Type w}
    (x : QuantumComp₂ LocalSig.instruments.{v} _root_.Sphincs.QuantumRandomOracleModel.spec A B α)
    (f : α → β) : portCalls₂ (x.map f) = (portCalls₂ x).map f := by
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure, portCalls₂_bind]
  rfl

/-- Reading the key through the translation reads the proof's key, mapped. -/
theorem portCalls₂_readKey (A : QReg) :
    portCalls₂ (_root_.Sphincs.QuantumRandomOracleModel.readKey A) =
      QComp.callBasis (spec := Spec) (Sum.inr Port.pk) A () fun _ r ↦ ofModelPublicKey r.1 :=
  rfl

/-- A basis call whose read-out is mapped by `f` is the call with its outcome mapped. -/
theorem callBasisMeasure_comp {spec : QuantumOracleSpec.{0, 0}} (p : spec.Port) (B : QReg)
    {β γ : Type} (read : spec.Out p → spec.Result p → β) (f : β → γ) (r : spec.Result p) :
    QComp.callBasisMeasure p B (fun o r ↦ f (read o r)) r =
      (QComp.callBasisMeasure p B read r).map f := by
  have hc : DSubInstrument.classical (B := fun _ ↦ Unit) (fun o : spec.Out p ↦ f (read o r))
      (fun _ ↦ ()) = (DSubInstrument.classical (B := fun _ ↦ Unit) (fun o ↦ read o r)
        (fun _ ↦ ())).map (C := fun _ ↦ Unit) f := by
    rw [DSubInstrument.classical, DSubInstrument.classical, DSubInstrument.map_map]
    rfl
  rw [QComp.callBasisMeasure, QComp.callBasisMeasure, hc, DSubInstrument.frame_map,
    DSubInstrument.map_eq_bind_ret, DSubInstrument.bind_assoc, SubInstrument.map_eq_bind_pure,
    SubInstrument.bind, DSubInstrument.bind_assoc]
  refine congrArg _ (funext fun c ↦ ?_)
  rw [DSubInstrument.ret_bind, DSubInstrument.bind_assoc]
  simp only [DSubInstrument.ret_bind]

theorem run₂_callBasis_comp {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)
    (p : spec.Port) (B : QReg) (a : spec.In p) {β γ : Type} (read : spec.Out p → spec.Result p → β)
    (f : β → γ) :
    R.run₂ .instruments (QComp.callBasis p B a fun o r ↦ f (read o r)) =
      (R.run₂ .instruments (QComp.callBasis p B a read)).map f := by
  rw [QComp.run₂_callBasis, QComp.run₂_callBasis, SubInstrument.map_eq_bind_pure,
    SubInstrument.bind_assoc]
  refine congrArg _ (funext fun _ ↦ ?_)
  rw [SubInstrument.bind_assoc]
  refine congrArg _ (funext fun r ↦ ?_)
  rw [SubInstrument.bind_assoc, callBasisMeasure_comp, SubInstrument.frame_map,
    SubInstrument.map_eq_bind_pure, SubInstrument.bind_assoc]
  simp only [SubInstrument.pure_bind, SubInstrument.bind_pure]

/-- The forgeries and keys of the leaves, the statement's as the proof's. -/
def leafOf (v : _root_.Sphincs.PublicKey × _root_.Sphincs.Forgery) : PublicKey × FORS.Forgery :=
  (toModelPublicKey v.1, toModelForgery v.2)

/-- **The translated adversary with its key** runs as the translation of the statement's
adversary with its key, the leaves read as the proof's. -/
theorem run₂_withKey (R : QuantumRuntime Spec) {A : QReg}
    (adv : _root_.Sphincs.QuantumRandomOracleModel.Adversary A) :
    R.run₂ .instruments (withKey (toQromAdversary adv)) =
      (R.run₂ .instruments
        (portCalls₂ (_root_.Sphincs.QuantumRandomOracleModel.withKey adv))).map leafOf := by
  rw [_root_.Sphincs.QuantumRandomOracleModel.withKey, portCalls₂_bind, portCalls₂_readKey,
    run₂_bind, run₂_callBasis_comp R (Sum.inr Port.pk) A ()
      (fun _ (r : Spec.Result (Sum.inr Port.pk)) ↦ r.1) ofModelPublicKey, withKey, readKey,
    run₂_bind, SubInstrument.map_eq_bind_pure leafOf, SubInstrument.bind_assoc,
    SubInstrument.map_eq_bind_pure ofModelPublicKey, SubInstrument.bind_assoc]
  simp only [SubInstrument.pure_bind]
  refine congrArg _ (funext fun pk ↦ ?_)
  rw [toQromAdversary, portCalls₂_map, run₂_map, run₂_map, run₂_map,
    SubInstrument.map_eq_bind_pure, SubInstrument.map_eq_bind_pure,
    SubInstrument.map_eq_bind_pure, SubInstrument.bind_assoc, SubInstrument.bind_assoc]
  simp only [SubInstrument.pure_bind]
  rfl

end withKey

/-! ## The winning weights correspond -/

section weights

open QuantumRuntime

/-- The forgeries, the statement's as the proof's. -/
def forgeryEquiv : _root_.Sphincs.Forgery ≃ FORS.Forgery where
  toFun := toModelForgery
  invFun F := ⟨F.message, ofModelSignature F.signature⟩
  left_inv F := by
    change (⟨F.message, ofModelSignature (toModelSignature F.signature)⟩ :
      _root_.Sphincs.Forgery) = F
    rw [show ofModelSignature (toModelSignature F.signature) = F.signature from
      signatureEquiv.right_inv F.signature]
  right_inv F := by
    change (⟨F.message, toModelSignature (ofModelSignature F.signature)⟩ : FORS.Forgery) = F
    rw [show toModelSignature (ofModelSignature F.signature) = F.signature from
      signatureEquiv.left_inv F.signature]

/-- The leaves, the statement's as the proof's. -/
def valueEquiv : _root_.Sphincs.PublicKey × _root_.Sphincs.Forgery ≃ PublicKey × FORS.Forgery :=
  publicKeyEquiv.symm.prodCongr forgeryEquiv

theorem valueEquiv_apply (v : _root_.Sphincs.PublicKey × _root_.Sphincs.Forgery) :
    valueEquiv v = leafOf v :=
  rfl

/-- The statement's log of a proof log holds a forgery when the proof log holds it, read as the
model's. -/
theorem contains_logEquiv (l : Log) (F : _root_.Sphincs.Forgery) :
    (logEquiv l).Contains F ↔ l.Contains (toModelForgery F) := by
  change (∃ e ∈ l.1.map entryEquiv, e.1 = F.message ∧ e.2 = some F.signature) ↔
    ∃ e ∈ l.1, e.1 = asMsg F.message ∧ e.2 = some (toModelSignature F.signature)
  simp only [List.mem_map]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, h1, h2⟩
    exact ⟨e, he, h1, (_root_.Sphincs.Model.map_eq_some_iff _ _).mp h2⟩
  · rintro ⟨e, he, h1, h2⟩
    exact ⟨_, ⟨e, he, rfl⟩, h1, (_root_.Sphincs.Model.map_eq_some_iff _ _).mpr h2⟩

/-- The verifier's answer on `H`. -/
theorem eval_verifier_fst (H : Input → HashOutput) (v : PublicKey × FORS.Forgery) :
    (evalWithAnswerFn (QueryImpl.ofFn H) (verifier v)).1 =
      evalWithAnswerFn (QueryImpl.ofFn (extend H))
        (Concrete.verify v.1 v.2.message v.2.signature : OracleComp HashSpec Bool) := by
  rw [verifier, eval_liftH, eval_traced]

/-- **The winning conditions correspond.** -/
theorem win_leafOf (seed : MasterSeed) (H : Input → HashOutput)
    (w : _root_.Sphincs.PublicKey × _root_.Sphincs.Forgery) (l : Log) :
    win (leafOf w, evalWithAnswerFn (QueryImpl.ofFn ((realGame seed H).answer l H))
        (verifier (leafOf w))) l =
      _root_.Sphincs.QuantumRandomOracleModel.win (asStmt H) w (logEquiv l) := by
  have ha : (realGame seed H).answer l H = H := rfl
  have hv := eval_verifier_fst H (leafOf w)
  have hs := verifyOn_eq H w.1 w.2
  have hc : (logEquiv l).Contains w.2 ↔ l.Contains (leafOf w).2 := contains_logEquiv l w.2
  rw [ha]
  simp only [win, _root_.Sphincs.QuantumRandomOracleModel.win]
  rw [hv, hs, decide_eq_decide.mpr hc.symm]
  rfl

/-- The weight of a log after relabelling the runtime register is the weight of the statement's
log. -/
theorem blockW_regMap {B : Type} [Fintype B] [DecidableEq B] (l : Log)
    (J : Matrix (B × (_root_.Sphincs.QuantumRandomOracleModel.Log × Unit))
      (B × (_root_.Sphincs.QuantumRandomOracleModel.Log × Unit)) ℂ) :
    OvGame.blockW l (regMap.amplifyLeft B J) = OvGame.blockW (logEquiv l) J := by
  rw [amplifyLeft_regMap, conj_basisMatrix_equiv]
  rfl

/-- The joint post-state of the translated adversary with its key at a leaf is that of the
statement's adversary at the corresponding leaf, its runtime register relabelled. -/
theorem matrix_jointPost₂_withKey (seed : MasterSeed) (H : Input → HashOutput) {A : QReg}
    (adv : _root_.Sphincs.QuantumRandomOracleModel.Adversary A) (ρ : SubState A)
    (w : _root_.Sphincs.PublicKey × _root_.Sphincs.Forgery) :
    (((realGame seed H).sampled H).jointPost₂ .instruments (withKey (toQromAdversary adv)) ρ
        (leafOf w)).matrix =
      regMap.amplifyLeft (QReg.of Unit)
        ((_root_.Sphincs.QuantumRandomOracleModel.runtime seed (asStmt H)).jointPost₂ .instruments
          (_root_.Sphincs.QuantumRandomOracleModel.withKey adv) ρ w).matrix := by
  rw [matrix_jointPost₂, run₂_withKey, SubInstrument.branch_map_apply,
    tsum_eq_single (⟨w, rfl⟩ : leafOf ⁻¹' {leafOf w}) ?_]
  · exact matrix_jointPost_portCalls seed H (_root_.Sphincs.QuantumRandomOracleModel.withKey adv)
      ρ ⟨_, rfl, w⟩
  · rintro ⟨w', hw'⟩ hne
    exact absurd (Subtype.ext (valueEquiv.injective (show valueEquiv w' = valueEquiv w from hw')))
      hne

/-- **The winning weights correspond** on `SK.seed` and `H`. -/
theorem winWeight_eq (seed : MasterSeed) (H : Input → HashOutput) {A : QReg}
    (adv : _root_.Sphincs.QuantumRandomOracleModel.Adversary A) (ρ : SubState A) :
    (∑' p, ∑ log : _root_.Sphincs.QuantumRandomOracleModel.Log,
      if _root_.Sphincs.QuantumRandomOracleModel.win (asStmt H) p.2.2 log then
        ENNReal.ofReal (∑ b, (((_root_.Sphincs.QuantumRandomOracleModel.runtime seed
          (asStmt H)).jointPost .instruments (_root_.Sphincs.QuantumRandomOracleModel.withKey adv)
            ρ p).matrix (b, (log, ())) (b, (log, ()))).re) else 0) =
      OvGame.sideW (realGame seed H) H .instruments (gameProg (toQromAdversary adv)) ρ
        fun p s ↦ win p.2.2 s := by
  have hP : OvGame.sideW (realGame seed H) H .instruments (gameProg (toQromAdversary adv)) ρ
      (fun p s ↦ win p.2.2 s) =
      ∑' w : _root_.Sphincs.PublicKey × _root_.Sphincs.Forgery,
        ∑ log : _root_.Sphincs.QuantumRandomOracleModel.Log,
          if _root_.Sphincs.QuantumRandomOracleModel.win (asStmt H) w log then
            OvGame.blockW log ((_root_.Sphincs.QuantumRandomOracleModel.runtime seed
              (asStmt H)).jointPost₂ .instruments
                (_root_.Sphincs.QuantumRandomOracleModel.withKey adv) ρ w).matrix else 0 := by
    rw [gameProg, OvGame.sideW_withVerifier,
      OvGame.sideW_eq_sum (realGame seed H) H _ (withKey (toQromAdversary adv)),
      ← (QuantumComp₂.leafEquiv _ _).tsum_eq, ← valueEquiv.tsum_eq]
    refine tsum_congr fun w ↦ Fintype.sum_equiv logEquiv _ _ fun l ↦ ?_
    simp only [QuantumComp₂.leafEquiv_apply, valueEquiv_apply]
    have hJ := (congrArg (OvGame.blockW l) (matrix_jointPost₂_withKey seed H adv ρ w)).trans
      (blockW_regMap (B := (QReg.of Unit).carrier) l _)
    have hw := win_leafOf seed H w l
    by_cases hc : _root_.Sphincs.QuantumRandomOracleModel.win (asStmt H) w (logEquiv l) = true
    · exact (ite_eq_left (hw.trans hc)).trans (hJ.trans (ite_eq_left hc).symm)
    · exact (ite_eq_right fun h ↦ hc (hw.symm.trans h)).trans (ite_eq_right hc).symm
  refine Eq.trans ?_ hP.symm
  refine (Equiv.tsum_eq (QuantumComp₂.leafEquiv (QReg.of Unit)
    (_root_.Sphincs.PublicKey × _root_.Sphincs.Forgery)) (fun p ↦
      ∑ log : _root_.Sphincs.QuantumRandomOracleModel.Log,
        if _root_.Sphincs.QuantumRandomOracleModel.win (asStmt H) p.2.2 log then
          ENNReal.ofReal (∑ b, (((_root_.Sphincs.QuantumRandomOracleModel.runtime seed
            (asStmt H)).jointPost .instruments (_root_.Sphincs.QuantumRandomOracleModel.withKey adv)
              ρ p).matrix (b, (log, ())) (b, (log, ()))).re) else 0)).symm.trans
    (tsum_congr fun w ↦ Finset.sum_congr rfl fun log _ ↦ ?_)
  rfl

end weights

/-! ## The games -/

/-- **The statement's game is the proof's**: the statement's adversary wins the statement's game
as often as its translation wins the proof's. -/
theorem winProb_eq_qrom {A : QReg} (adv : _root_.Sphincs.QuantumRandomOracleModel.Adversary A)
    (ρ : SubState A) :
    _root_.Sphincs.QuantumRandomOracleModel.winProb adv ρ = winProb (toQromAdversary adv) ρ := by
  unfold _root_.Sphincs.QuantumRandomOracleModel.winProb winProb
  refine Finset.sum_congr rfl fun seed _ ↦ ?_
  have hcard : Fintype.card (_root_.Sphincs.QuantumRandomOracleModel.Input →
      _root_.Sphincs.QuantumRandomOracleModel.Output) = Fintype.card (Input → HashOutput) :=
    Fintype.card_congr (Equiv.refl _)
  refine Fintype.sum_equiv (Equiv.refl _) _ _ fun H ↦ ?_
  exact congrArg₂ (· * ·)
    (congrArg (fun n : ℕ ↦ ((Fintype.card MasterSeed : ℝ≥0∞) * n)⁻¹) hcard)
    (winWeight_eq seed H adv ρ)

/-- **The statement's game is bounded by the proof's.** -/
theorem winProb_le_qrom {A : QReg} (adv : _root_.Sphincs.QuantumRandomOracleModel.Adversary A)
    (ρ : SubState A) :
    _root_.Sphincs.QuantumRandomOracleModel.winProb adv ρ ≤ winProb (toQromAdversary adv) ρ :=
  (winProb_eq_qrom adv ρ).le

end Qrom.Sphincs
