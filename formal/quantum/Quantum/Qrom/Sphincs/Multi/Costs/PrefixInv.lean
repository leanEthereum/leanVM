module

public import Quantum.Qrom.Sphincs.Multi.Costs.Defs

@[expose] public section

/-!
# The classical costs of the `n`-user runtime 2: the invariant at the prefix's calls

The `n`-user analog of `Quantum.Qrom.Sphincs.Costs.PrefixInv`. With distinct `PK.seed`s, the
challenge prefix `prefixQSN (strPolN n) A θ` satisfies `PrefixInvQSN (pkQN θ) (honQN θ) A θ`
(`prefixInvQSN`): every call is a sponge or record port, a trial read of an encoding slot at its
owner, or a program of an exempt cell off the encoding slots; the input has no hardwired encoding
cell (`EncFreeSN`), no selection of a trial read's key (`selOkS`) and no decompressed `⊥`.

* **The port charge** (`bQSN`, `portOkQSN_of_bQSN`): `0` on the allowed ports, `1` otherwise.
  `chgO_prefixQSN`: the realized prefix is within budget `0`. User `i`'s programs realize cells of
  user `i`'s table (`progExQSN_cellOf`: exempt for their owner `i`, or without owner at the key
  expansion; at no encoding slot of any user), the digest port included. User `i`'s searches read
  trial cells under the seed its signature revealed, which is user `i`'s `PK.seed` at the realized
  values (`chgR_signTN`); their owner is `i` (`ownerS_of_slotOf`). A memo hit calls nothing.
* **No hardwired encoding cell** (`stepEncSN`, `encGSN`): CostRun's
  `forallQueries_of_charge_step`.
* **No selection of the read key**: GameTSel's `forallQueries_noSelReadS`.
* **No decompressed `⊥`**: EventSqrt's `forallQueries_noBot`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT revealThen progThen readLift
  readLiftQ RevealVals liftRead tmplLens readLens NoBot forallQueries_noBot noBot_init
  forallQueries_and forallQueries_of_charge_step querySupportedOn_traceRight chg_act chg_map
  isChargeBound_zero isChargeBound_mono_charge recKraus_ne_zero realizeT_bind realizeT_bind₂
  realizeT_substitute)
open Quantum.Qrom.MultiUser (ownerOf)

attribute [local irreducible] sphincsRom

/- Instance search for the registers over `Finset (TPosN n)` exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ} {pk : Fin n → PublicKey} {hon : Fin n → HonestCells}

/-! ## The port charge -/

/-- A trial read of an encoding slot at its owner. -/
def ReadOkQSN (pk : Fin n → PublicKey) (c : HwRead PairOut HashDomain (QMemSN n)) : Prop :=
  ∃ z i K, slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2) ∧ ownerS pk z = some i ∧
    c = trialReadSN z (i, K)

/-- A program of an exempt cell off every user's encoding slots. -/
def ProgExQSN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells)
    (c : HwProg PairOut HashDomain) : Prop :=
  ∃ z a, c = .programH z a ∧ ExemptCellN pk hon z ∧
    ∀ i (K : Key), slotOf (pk i) z ≠ some (.enc K.1 K.2.1 K.2.2)

/-- **The port charge of the prefix**: `0` on sponge and record ports, trial reads of encoding
slots at their owner and programs of exempt cells off the encoding slots; `1` otherwise. -/
noncomputable def bQSN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells) :
    (RSpecSN n (SelMemN n)).Port → ℕ
  | .inl (.inl (.inl _)) => 0
  | .inl (.inl (.inr c)) => @ite ℕ (ReadOkQSN pk c) (Classical.propDecidable _) 0 1
  | .inl (.inr c) => @ite ℕ (ProgExQSN pk hon c) (Classical.propDecidable _) 0 1
  | .inr _ => 0

theorem readOkQSN_of_bQSN {c : HwRead PairOut HashDomain (QMemSN n)}
    (h : bQSN pk hon (.inl (.inl (.inr c))) = 0) : ReadOkQSN pk c := by
  by_contra hc
  exact one_ne_zero ((ite_eq_right hc).symm.trans h)

theorem progExQSN_of_bQSN {c : HwProg PairOut HashDomain} (h : bQSN pk hon (.inl (.inr c)) = 0) :
    ProgExQSN pk hon c := by
  by_contra hc
  exact one_ne_zero ((ite_eq_right hc).symm.trans h)

/-- A port of charge `0` is a port of the prefix. -/
theorem portOkQSN_of_bQSN {i : (RSpecSN n (SelMemN n)).Port} (h : bQSN pk hon i = 0) :
    PortOkQSN pk hon i := by
  rcases i with ((p | c) | c) | T
  · trivial
  · exact readOkQSN_of_bQSN h
  · obtain ⟨z, a, hc, hz, -⟩ := progExQSN_of_bQSN h
    exact ⟨z, a, hc, hz⟩
  · trivial

/-- The charge on runtime 1's ports, through `liftRead`. -/
noncomputable def dQSN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells) :
    (hwReadSpec PairOut HashDomain (SelMemN n)).Port → ℕ
  | .inl i => bQSN pk hon (.inl (.inl (.inl i)))
  | .inr c => bQSN pk hon (.inl (.inl (.inr (liftRead (S := TPosN n) c))))

/-- The charge on the template ports at `θ`, through the realization. -/
noncomputable def tQSN (θ : TValsN n) : (XSpecSN (SelMemN n) n).Port → ℕ
  | .inl (.inl (.inl i)) => bQSN (pkQN θ) (honQN θ) (.inl (.inl (.inl i)))
  | .inl (.inl (.inr c)) => bQSN (pkQN θ) (honQN θ) (.inl (.inl (.inr c.1)))
  | .inl (.inr p) => bQSN (pkQN θ) (honQN θ) (.inl (.inr (p.1.realize θ)))
  | .inr T => bQSN (pkQN θ) (honQN θ) (.inr T)

/-! ## The realized prefix is within budget `0` -/

section charge

variable {Ω : QReg → Type}

/-- Distinct `PK.seed`s of the tables are distinct `PK.seed`s of the public keys. -/
theorem injective_pkQN_publicSeed {θ : TValsN n} (hP : PDistinct (tabOfN θ)) :
    Function.Injective fun i ↦ (pkQN θ i).publicSeed :=
  hP

/-- **A cell of user `i`'s table is exempt**: for its owner `i`, or without owner at the key
expansion. -/
theorem exemptCellN_cellOf (θ : TValsN n) (hP : PDistinct (tabOfN θ)) (i : Fin n) (p : Pos) :
    ExemptCellN (pkQN θ) (honQN θ) (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) := by
  by_cases hp : IsExpandPos p
  · refine exemptCellN_of_owner_none ?_
    show ownerOf _ prefixS _ = none
    unfold ownerOf
    rw [prefixS_cellOf_expand _ _ hp]
    rfl
  · have ho : ownerS (pkQN θ) (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) = some i :=
      ownerOf_cellOfN hP (seedsOf θ) i hp
    exact exemptCellN_of_owner ho (exemptCell_cellOf (seedsOf θ i) (tabOf (userOf θ i)) p)

/-- **A cell of user `i`'s table is at no encoding slot** of any user. -/
theorem slotOf_cellOf_ne_encSN (θ : TValsN n) (hP : PDistinct (tabOfN θ)) (i : Fin n) (p : Pos)
    (j : Fin n) (K : Key) :
    slotOf (pkQN θ j) (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) ≠
      some (.enc K.1 K.2.1 K.2.2) := by
  intro h
  have hj := prefixS_of_slotOf h (prefixedSlot_enc _ _ _)
  by_cases hp : IsExpandPos p
  · rw [prefixS_cellOf_expand _ _ hp] at hj
    cases hj
  · rw [prefixS_cellOf _ _ hp] at hj
    obtain rfl : j = i := injective_pkQN_publicSeed hP (Option.some.inj hj).symm
    have hsl : slotOf (tabOf (userOf θ j)).publicKey
        (cellOf (seedsOf θ j) p (tabOf (userOf θ j))) =
          some (posSlot (tabOf (userOf θ j)) p.1) :=
      slotOf_cell ((tabOf (userOf θ j)).expandedKey (seedsOf θ j)) (tabOf (userOf θ j)).root
        (slotInRange_posSlot (tabOf (userOf θ j)) p) _
    exact posSlot_ne_enc (tabOf (userOf θ j)) p.1 K.1 K.2.1 K.2.2
      (Option.some.inj (hsl.symm.trans h))

/-- **A cell of user `i`'s table is programmed at no cost.** -/
theorem progExQSN_cellOf (θ : TValsN n) (hP : PDistinct (tabOfN θ)) (i : Fin n) (p : Pos)
    (a : PairOut) :
    ProgExQSN (pkQN θ) (honQN θ) (.programH (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) a) :=
  ⟨_, _, rfl, exemptCellN_cellOf θ hP i p, slotOf_cellOf_ne_encSN θ hP i p⟩

/-- A realized program port of user `i`'s structural position has charge `0`. -/
theorem tQSN_progTN (θ : TValsN n) (hP : PDistinct (tabOfN θ)) (i : Fin n) {p : Pos}
    (hp : p.1.IsStruct) : tQSN θ (.inl (.inr ⟨progTN i p, trivial⟩)) = 0 := by
  show bQSN (pkQN θ) (honQN θ) (.inl (.inr ((progTN i p).realize θ))) = 0
  rw [realize_progTN hp i θ]
  exact ite_eq_left (progExQSN_cellOf θ hP i p _)

/-- User `i`'s realized digest port has charge `0`. -/
theorem tQSN_digPortN (θ : TValsN n) (hP : PDistinct (tabOfN θ)) (pol : DigestPolicy)
    (i : Fin n) (L : Finset (TPosN n)) (msg : Message) :
    tQSN θ (.inl (.inr ⟨digPortN pol i L msg, trivial⟩)) = 0 := by
  show bQSN (pkQN θ) (honQN θ) (.inl (.inr ((digPortN pol i L msg).realize θ))) = 0
  rw [realize_digPortN, ← cellOf_digPos (seedsOf θ i)]
  exact ite_eq_left (progExQSN_cellOf θ hP i (digPos msg) _)

/-- Realizing keeps the charge. -/
theorem chgO_realizeTN (θ : TValsN n) {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (XSpecSN (SelMemN n) n) Ω A} {k : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (tQSN θ)) k) :
    IFreeM.IsChargeBound (realizeT θ y) (portCharge (bQSN (pkQN θ) (honQN θ))) k := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens (good := goodQN) (M := SelMemN n) θ) ?_
  have he : (fun s cmd ↦ portCharge (L := LocalSig.instruments.{0}) (bQSN (pkQN θ) (honQN θ)) s
      ((tmplLens (good := goodQN) (M := SelMemN n) θ).toFunA s cmd)) = portCharge (tQSN θ) := by
    funext s cmd
    rcases cmd with o | ⟨((i | c) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

/-- Lifting runtime 1's programs keeps the charge. -/
theorem chgO_readLiftSN (θ : TValsN n) {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (hwReadSpec PairOut HashDomain (SelMemN n)) Ω A}
    {k : ℕ} (h : IFreeM.IsChargeBound y (portCharge (dQSN (pkQN θ) (honQN θ))) k) :
    IFreeM.IsChargeBound (readLift (goodQN (n := n)) y) (portCharge (tQSN θ)) k := by
  refine IFreeM.IsChargeBound.mapLens (readLens (goodQN (n := n))) ?_
  have he : (fun s cmd ↦ portCharge (L := LocalSig.instruments.{0}) (tQSN θ) s
      ((readLens (goodQN (n := n))).toFunA s cmd)) = portCharge (dQSN (pkQN θ) (honQN θ)) := by
    funext s cmd
    rcases cmd with o | ⟨i | c, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

/-- A read call of a trial read. -/
theorem chgO_readCallSN (c : HwRead PairOut HashDomain (SelMemN n))
    (hc : ReadOkQSN pk (liftRead (S := TPosN n) c)) (B : QReg) :
    IFreeM.IsChargeBound (readCall c B) (portCharge (dQSN pk hon)) 0 := by
  unfold readCall
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
      ⟨Nat.le_of_eq (ite_eq_left hc), fun _ ↦ trivial⟩)
    fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ trivial

/-- **User `i`'s counter search under its `PK.seed`** calls only trial reads of encoding slots
owned by `i`. -/
theorem chgO_grindTN (hPk : Function.Injective fun i ↦ (pk i).publicSeed) (i : Fin n) (B : QReg)
    (K : Key) (m : Digest) :
    ∀ k cnt, IFreeM.IsChargeBound
      (grindT (SelMemN n) (cwUpdN i) (pk i).publicSeed B K m k cnt) (portCharge (dQSN pk hon)) 0
  | 0, _ => trivial
  | k + 1, cnt => by
    have hc : ReadOkQSN pk (liftRead (S := TPosN n) (.readH (trialCell (pk i).publicSeed K m cnt)
        (cwUpdN i K (trialCell (pk i).publicSeed K m cnt)))) :=
      ⟨_, i, K, slotOf_trialCell (pk i) K m cnt,
        ownerS_of_slotOf hPk (slotOf_trialCell (pk i) K m cnt) (prefixedSlot_enc _ _ _), rfl⟩
    rw [grindT]
    refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_readCallSN _ hc B) fun r ↦ ?_
    generalize TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) = dd
    cases dd with
    | none => exact chgO_grindTN hPk i B K m k (cnt + 1)
    | some x => trivial

theorem chgO_revealThenSN (θ : TValsN n) {B B' : QReg} {α : Type} (T : Finset (TPosN n))
    (k : RevealVals (TValN n) T × (Finset (TPosN n) × SelMemN n) →
      QComp (XSpecSN (SelMemN n) n) B B' α)
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (tQSN θ)) 0) :
    IFreeM.IsChargeBound (revealThen goodQN T k) (portCharge (tQSN θ)) 0 :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨le_rfl, fun r ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ hk r⟩

theorem chgO_progThenSN (θ : TValsN n) {B B' : QReg} {α : Type}
    {p : LazyProg PairOut HashDomain (TPosN n) (TValN n)}
    (hp : tQSN θ (.inl (.inr ⟨p, trivial⟩)) = 0) (k : QComp (XSpecSN (SelMemN n) n) B B' α)
    (hk : IFreeM.IsChargeBound k (portCharge (tQSN θ)) 0) :
    IFreeM.IsChargeBound (progThen p trivial k) (portCharge (tQSN θ)) 0 :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨hp.le, fun _ ↦
    IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0)
      fun _ ↦ hk) (Nat.zero_le _)⟩

theorem chgO_progPosSN (θ : TValsN n) (hP : PDistinct (tabOfN θ)) (i : Fin n) (B : QReg) :
    ∀ ps : List Pos, (∀ p ∈ ps, p.1.IsStruct) →
      IFreeM.IsChargeBound (progPosN (SelMemN n) i B ps) (portCharge (tQSN θ)) 0
  | [], _ => trivial
  | p :: ps, h => chgO_progThenSN θ (tQSN_progTN θ hP i (h p List.mem_cons_self)) _
      (chgO_progPosSN θ hP i B ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

/-- **User `i`'s search under its canonical `PK.seed`** calls only ports of charge `0`. -/
theorem chgO_selectTN (θ : TValsN n) (hP : PDistinct (tabOfN θ)) (i : Fin n) (B : QReg)
    (K : Key) :
    IFreeM.IsChargeBound (selectTN (SelMemN n) cwUpdN i (tabOf (userOf θ i)).publicSeed B K)
      (portCharge (tQSN θ)) 0 :=
  chgO_revealThenSN θ _ _ fun _ ↦ chgO_readLiftSN θ
    (chgO_grindTN (pk := pkQN θ) (injective_pkQN_publicSeed hP) i B K _ _ 0)

/-- User `i`'s selection or memo: a memo hit calls nothing. -/
theorem chgO_selOrMemoTN (θ : TValsN n) (hP : PDistinct (tabOfN θ)) (i : Fin n) (B : QReg)
    (K : Key) (o : Option SelS) :
    IFreeM.IsChargeBound
      (selOrMemoTN (SelMemN n) cwUpdN i (tabOf (userOf θ i)).publicSeed B K o)
      (portCharge (tQSN θ)) 0 := by
  cases o with
  | none => exact chgO_selectTN θ hP i B K
  | some o => trivial

theorem chgO_publishTN (θ : TValsN n) (hP : PDistinct (tabOfN θ)) (i : Fin n) (B : QReg)
    (K : Key) (cnt : EncodingCounter) (x : Encoding) :
    IFreeM.IsChargeBound (publishTN (SelMemN n) i B K cnt x) (portCharge (tQSN θ)) 0 :=
  chgO_revealThenSN θ _ _ fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (chgO_progPosSN θ hP i B _ fun _ hp ↦ isStruct_of_mem_layerPos hp) fun _ ↦ trivial

theorem chgO_forsOpenTN (θ : TValsN n) (hP : PDistinct (tabOfN θ)) (i : Fin n) (B : QReg)
    (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    IFreeM.IsChargeBound (forsOpenTN (SelMemN n) i B idx lv) (portCharge (tQSN θ)) 0 :=
  chgO_revealThenSN θ _ _ fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (chgO_progPosSN θ hP i B _ fun _ hp ↦ isStruct_of_mem_forsPos hp) fun _ ↦ trivial

theorem chgO_publishAllTN (θ : TValsN n) (hP : PDistinct (tabOfN θ)) (i : Fin n) (B : QReg)
    (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) (g₀ g₁ g₂ : SelS) :
    IFreeM.IsChargeBound (publishAllTN (SelMemN n) i B idx lv R g₀ g₁ g₂)
      (portCharge (tQSN θ)) 0 := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try trivial
  simp only [publishAllTN]
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_forsOpenTN θ hP i B _ _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_publishTN θ hP i B _ _ _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_publishTN θ hP i B _ _ _) fun _ ↦ ?_
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_publishTN θ hP i B _ _ _) fun _ ↦
    trivial

/-- **A realized reveal**: the record port, then the continuation at the values of `θ`. -/
theorem chgR_revealThenSN (θ : TValsN n) {B C : QReg} {α : Type} (T : Finset (TPosN n))
    (k : RevealVals (TValN n) T × (Finset (TPosN n) × SelMemN n) →
      QComp (XSpecSN (SelMemN n) n) B C α)
    (hk : ∀ mem, IFreeM.IsChargeBound (realizeT θ (k (restrictTo T θ, mem)))
      (portCharge (bQSN pk hon)) 0) :
    IFreeM.IsChargeBound (realizeT θ (revealThen goodQN T k)) (portCharge (bQSN pk hon)) 0 := by
  have e : realizeT θ (revealThen goodQN T k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpecSN n (SelMemN n)) (.inr T)
        B (Equiv.uniqueProd B Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((RSpecSN n (SelMemN n)).Out (.inr T) × B)) (B := B)
            (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ (k (restrictTo T θ, mem)) :=
    rfl
  refine (congrArg (fun y ↦ IFreeM.IsChargeBound y (portCharge (bQSN pk hon)) 0) e).mpr ?_
  exact (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨le_rfl, fun r ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ hk r⟩

/-- **User `i`'s realized signature** calls only ports of charge `0`: the first reveal fixes the
seed of the searches to user `i`'s `PK.seed`. -/
theorem chgR_signTN (θ : TValsN n) (hP : PDistinct (tabOfN θ)) (pols : Fin n → DigestPolicy)
    (i : Fin n) (B : QReg) (msg : Message) (h : KeyMemo) :
    IFreeM.IsChargeBound (realizeT θ (signTN (SelMemN n) cwUpdN pols i B msg h))
      (portCharge (bQSN (pkQN θ) (honQN θ))) 0 := by
  rw [signTN]
  refine chgR_revealThenSN θ _ _ fun mem₁ ↦ ?_
  have hs₀ : (tabRN (restrictTo (atU i {seedC, rootC, rndC msg}) θ) i).publicSeed =
      (tabOf (userOf θ i)).publicSeed :=
    publicSeed_tabOf_congr (tabRN_restrictTo_congr (atU_restrict _) θ _ (by simp))
  dsimp only
  rw [hs₀]
  refine chgO_realizeTN θ (chgO_revealThenSN θ _ _ fun r₂ ↦
    chgO_progThenSN θ (tQSN_digPortN θ hP (pols i) i _ msg) _ ?_)
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_selOrMemoTN θ hP i B _ _) fun _ ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_selOrMemoTN θ hP i B _ _) fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_selOrMemoTN θ hP i B _ _) fun _ ↦
        chg_map _ _ (chgO_publishAllTN θ hP i B _ _ _ _ _ _)

/-- **The realized challenger** calls only ports of charge `0`. -/
theorem chgR_challengeTN (θ : TValsN n) (hP : PDistinct (tabOfN θ))
    (pols : Fin n → DigestPolicy) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} (memoSpecS n) A) :
    IFreeM.IsChargeBound (realizeT θ (challengeTN (SelMemN n) cwUpdN pols A cmd))
      (portCharge (bQSN (pkQN θ) (honQN θ))) 0 := by
  rcases cmd with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact chgO_realizeTN θ (chgO_readLiftSN θ (isChargeBound_liftOrdinary _
      ((isChargeBound_liftH_iff _ _ _).mpr (isChargeBound_mono_charge
        (fun _ a ↦ by cases a <;> exact le_rfl) (isChargeBound_zero _)))))
  · exact chgO_realizeTN θ (chgO_readLiftSN θ (isChargeBound_liftOrdinary _
      ((isChargeBound_liftH_iff _ _ _).mpr (isChargeBound_mono_charge
        (fun _ a ↦ by cases a <;> exact le_rfl) (isChargeBound_zero _)))))
  · refine (congrArg (fun y ↦ IFreeM.IsChargeBound y (portCharge (bQSN (pkQN θ) (honQN θ))) 0)
      (realizeT_bind θ (signAtSN i q E ℓ fun B ↦ signTN (SelMemN n) cwUpdN pols i B q.1 q.2)
        _)).mpr ?_
    refine IFreeM.isChargeBound_bind (n₁ := 0) (n₂ := 0) ?_ fun _ _ ↦
      chgO_realizeTN θ (IFreeM.isChargeBound_pure _ 0)
    rw [signAtSN, realizeT_bind₂]
    exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_realizeTN θ (chg_act _ _ 0))
      fun _ ↦ chgR_signTN θ hP pols i _ q.1 q.2

/-- **The realized challenge prefix** calls only ports of charge `0`, with distinct `PK.seed`s. -/
theorem chgO_prefixQSN (pols : Fin n → DigestPolicy) (A : MuAdversaryS n) (θ : TValsN n)
    (hP : PDistinct (tabOfN θ)) :
    IFreeM.IsChargeBound (prefixQSN pols A θ) (portCharge (bQSN (pkQN θ) (honQN θ))) 0 := by
  unfold prefixQSN prefixTN
  refine chgR_revealThenSN θ _ _ fun mem ↦ ?_
  dsimp only
  rw [realizeT_bind₂]
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) ?_ fun _ ↦
    chgO_realizeTN θ (IFreeM.isChargeBound_pure _ 0)
  unfold challengedTN
  refine (congrArg (fun y ↦ IFreeM.IsChargeBound y (portCharge (bQSN (pkQN θ) (honQN θ))) 0)
    (realizeT_substitute θ (challengeTN (SelMemN n) cwUpdN pols) _)).mpr ?_
  exact IFreeM.IsChargeBound.substitute _ (c := fun _ _ ↦ 0)
    (fun s cmd ↦ chgR_challengeTN θ hP pols s cmd) (isChargeBound_zero _)

end charge

/-! ## No hardwired encoding cell -/

section enc

theorem encFreeSN_of_hw {s s' : RRegSN n (SelMemN n)} (h : s'.2.1 = s.2.1)
    (hs : EncFreeSN pk s) : EncFreeSN pk s' := by
  intro x hx
  rw [h] at hx
  exact hs x hx

theorem encFreeSN_progUpdate {s s' : RRegSN n (SelMemN n)} {c : HwProg PairOut HashDomain}
    {z : HashDomain} {a : PairOut} (h : s'.2.1 = progUpdate c s.2.1)
    (hc : c = .programH z a) (hz : ∀ i (K : Key), slotOf (pk i) z ≠ some (.enc K.1 K.2.1 K.2.2))
    (hs : EncFreeSN pk s) : EncFreeSN pk s' := by
  subst hc
  intro x hx i K
  rw [h] at hx
  have hx' : (Function.update s.2.1.1 z (some a) x).isSome := hx
  by_cases hxz : x = z
  · subst hxz
    exact hz i K
  · rw [Function.update_of_ne hxz] at hx'
    exact hs x hx' i K

/-- A read port keeps the hardwired cells. -/
theorem hwReadKraus_ne_zero_hwQSN (c : HwRead PairOut HashDomain (QMemSN n)) (r : c.Result)
    {u u' : Unit} {s s' : RRegSN n (SelMemN n)} (h : hwReadKraus c r (u', s') (u, s) ≠ 0) :
    s'.2.1 = s.2.1 := by
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at h
    obtain ⟨-, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at h
    obtain ⟨-, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at h
    obtain ⟨-, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]

/-- **A port of charge `0` keeps the support on `EncFreeSN` registers.** -/
theorem stepEncSN (i : (RSpecSN n (SelMemN n)).Port) (hi : bQSN pk hon i = 0)
    (r : (RSpecSN n (SelMemN n)).Result i)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In i ×
        (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D)
      ((RSpecSN n (SelMemN n)).In i ×
        (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D) ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).In i ×
      (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D ↦ m.2)
        {s : RRegSN n (SelMemN n) | EncFreeSN pk s} σ) :
    QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).Out i ×
      (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D ↦ m.2)
        {s : RRegSN n (SelMemN n) | EncFreeSN pk s}
        (((runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · have hb : ((runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).step
        (.inl (.inl (.inl i)))).branch r σ = MatrixMap.conj ((spongeHardwired PairOut
          HashDomain (hwEmpty PairOut HashDomain) (m0SN (n := n))).U i) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty PairOut HashDomain)
        (m0SN (n := n)) i r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      encFreeSN_of_hw (congrArg Prod.fst (snd_eq_of_spongeHardwired_U_ne_zero
        (hwEmpty PairOut HashDomain) (m0SN (n := n)) i q.1 q'.1 q.2 q'.2 hK)) hq
  · have hb : ((runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).step
        (.inl (.inl (.inr c)))).branch r σ = MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty PairOut HashDomain)
        (m0SN (n := n)) c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      encFreeSN_of_hw (hwReadKraus_ne_zero_hwQSN c r (u := q.1) (s := q.2) (u' := q'.1)
        (s' := q'.2) hK) hq
  · have hb : ((runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).step
        (.inl (.inr c))).branch r σ = MatrixMap.conj (hwProgKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty PairOut HashDomain)
        (m0SN (n := n)) c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    obtain ⟨z, a, hc, -, hz⟩ := progExQSN_of_bQSN hi
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      encFreeSN_progUpdate (congrArg Prod.fst (hwProgKraus_ne_zero_snd c r (u := q.1)
        (s := q.2) (u' := q'.1) (s' := q'.2) hK)) hc hz hq
  · exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
      have he := recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK
      exact encFreeSN_of_hw (congrArg Prod.fst he :) hq

open scoped Classical in
/-- The encoding grade: `0` on `EncFreeSN` registers, `1` otherwise. -/
noncomputable def encGSN (pk : Fin n → PublicKey) (s : RRegSN n (SelMemN n)) : ℕ :=
  if EncFreeSN pk s then 0 else 1

theorem encGSN_le_one (s : RRegSN n (SelMemN n)) : encGSN pk s ≤ 1 := by
  unfold encGSN
  split <;> omega

theorem encFreeSN_of_encGSN {s : RRegSN n (SelMemN n)} (h : encGSN pk s ≤ 0) :
    EncFreeSN pk s := by
  by_contra hc
  unfold encGSN at h
  rw [ite_eq_right hc] at h
  omega

theorem encGSN_of_encFreeSN {s : RRegSN n (SelMemN n)} (h : EncFreeSN pk s) : encGSN pk s ≤ 0 := by
  unfold encGSN
  rw [ite_eq_left h]

/-- The ports raise the encoding grade by at most their charge. -/
theorem encGSN_step (i : (RSpecSN n (SelMemN n)).Port) (r : (RSpecSN n (SelMemN n)).Result i)
    (t : ℕ)
    (σ : Matrix ((RSpecSN n (SelMemN n)).In i ×
        (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D)
      ((RSpecSN n (SelMemN n)).In i ×
        (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D) ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).In i ×
      (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D ↦ encGSN pk m.2)
        (Set.Iic t) σ) :
    QuerySupportedOn (fun m : (RSpecSN n (SelMemN n)).Out i ×
      (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).D ↦ encGSN pk m.2)
        (Set.Iic (t + bQSN pk hon i))
        (((runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).step i).branch r σ) := by
  by_cases h1 : 1 ≤ t + bQSN pk hon i
  · exact fun m m' _ ↦ ⟨Set.mem_Iic.2 ((encGSN_le_one _).trans h1),
      Set.mem_Iic.2 ((encGSN_le_one _).trans h1)⟩
  · have ht : t = 0 := by omega
    have hi : bQSN pk hon i = 0 := by omega
    subst ht
    rw [hi]
    exact (stepEncSN i hi r σ (hσ.imp fun m hm ↦ encFreeSN_of_encGSN (Set.mem_Iic.1 hm))).imp
      fun m hm ↦ Set.mem_Iic.2 (encGSN_of_encFreeSN hm)

/-- The initial operator has no hardwired cell. -/
theorem querySupportedOn_initQSN_encGSN :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := PairOut) (Z := HashDomain)
      (m0SN (n := n))).D ↦ encGSN pk m.2) (Set.Iic 0) (initQSN (n := n)) := by
  have h0 : EncFreeSN pk (((Database.empty, Database.empty, Database.empty),
      hwEmpty PairOut HashDomain, m0SN) : RRegSN n (SelMemN n)) := fun x hx ↦ by
    rw [show (hwEmpty PairOut HashDomain).1 x = none from rfl] at hx
    cases hx
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty PairOut HashDomain, m0SN) : RRegSN n (SelMemN n))).matrix) m m'
      ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · exact ⟨Set.mem_Iic.2 ((congrArg (encGSN pk) he.1).symm.trans_le (encGSN_of_encFreeSN h0)),
      Set.mem_Iic.2 ((congrArg (encGSN pk) he.2).symm.trans_le (encGSN_of_encFreeSN h0))⟩
  · exact absurd rfl h

end enc

/-! ## The invariant -/

/-- **The challenge prefix satisfies `PrefixInvQSN`** for distinct `PK.seed`s: its calls are
sponge and record ports, trial reads of encoding slots at their owner and programs of exempt
cells, on registers without hardwired encoding cell, without a selection of the read key and
without decompressed `⊥`. -/
theorem prefixInvQSN (A : MuAdversaryS n) (θ : TValsN n) (hP : PDistinct (tabOfN θ)) :
    PrefixInvQSN (pkQN θ) (honQN θ) A θ := by
  have hb := chgO_prefixQSN (strPolN n) A θ hP
  have h1 := forallQueries_of_charge_step (runtimeR (m0SN (n := n))) (fun s ↦ encGSN (pkQN θ) s)
    (bQSN (pkQN θ) (honQN θ)) (bQSN (pkQN θ) (honQN θ))
    (fun i r t σ hσ ↦ encGSN_step i r t σ hσ) .instruments (prefixQSN (strPolN n) A θ) hb hb
    querySupportedOn_initQSN_encGSN
  have h3 := forallQueries_noBot (m0SN (n := n)) .instruments (prefixQSN (strPolN n) A θ)
    (noBot_init (m0SN (n := n)) (SubState.basis ()).matrix)
  have h4 := forallQueries_noSelReadS (strPolN n) A θ (m0SN (n := n)) rfl
    (SubState.basis ()).matrix
  refine ⟨_, fun i E σ hQ ↦ ?_, forallQueries_and h1 (forallQueries_and h3 h4)⟩
  obtain ⟨⟨hb0, hg⟩, hnb, hsel⟩ := hQ
  refine ⟨portOkQSN_of_bQSN hb0, ?_, querySupportedOn_traceRight
    (q := fun a : (RSpecSN n (SelMemN n)).In i × RRegSN n (SelMemN n) ↦ a.2) hsel, hnb⟩
  exact (querySupportedOn_traceRight (q := fun a : (RSpecSN n (SelMemN n)).In i ×
    RRegSN n (SelMemN n) ↦ encGSN (pkQN θ) a.2) hg).imp
      fun a ha ↦ encFreeSN_of_encGSN (Set.mem_Iic.1 ha)

end Quantum.Qrom.Sphincs.Multi

end
