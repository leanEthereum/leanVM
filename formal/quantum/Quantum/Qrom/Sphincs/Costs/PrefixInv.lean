module

public import Quantum.Qrom.Sphincs.Costs.Ports

@[expose] public section

/-!
# The classical costs of leanSPHINCS's runtime 2: the invariant at the prefix's calls

The challenge prefix `prefixQ pol A θ` satisfies `PrefixInvQ (pkQ θ) (honQ θ) pol A θ`
(`prefixInvQ`), the hypothesis of `twPQ_le`: every call of the prefix is a sponge or record port,
a trial read of an encoding slot under `pkQ θ`, or a program of an exempt cell; the input has no
hardwired encoding cell (`EncFree`) and no decompressed `⊥`.

* **The port charge** (`bQ`, `portOkQ_of_bQ`): `0` on the allowed ports (programs of exempt cells
  off the encoding slots), `1` otherwise. `chgO_prefixQ`: the realized prefix is within budget
  `0`. The program ports realize table cells (`progExQ_cellOf`: exempt, `exemptCell_cellOf`, at no
  encoding slot, `posSlot_ne_enc`), the digest port included. A search reads trial cells under
  the seed the signature revealed, which is `PK.seed` only at the realized values: the signature
  is bounded on the realized program (`chgR_revealThen`, `chgR_signT`), the rest on the template
  (`tQ`, `chgO_realizeT`).
* **No hardwired encoding cell** (`stepEnc`, `encG`): every port of charge `0` keeps the support
  on `EncFree` registers, CostRun's `forallQueries_of_charge_step`.
* **No decompressed `⊥`**: EventSqrt's `forallQueries_noBot`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT revealThen progThen readLift
  readLiftQ RevealVals liftRead tmplLens readLens NoBot forallQueries_noBot noBot_init
  forallQueries_and forallQueries_of_charge_step querySupportedOn_traceRight chg_act
  isChargeBound_zero isChargeBound_mono_charge recKraus_ne_zero realizeT_bind realizeT_bind₂
  realizeT_substitute)

attribute [local irreducible] sphincsRom

/- Instance search for the registers over `Finset TPos` exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {pk : PublicKey} {hon : HonestCells}

/-! ## The port charge -/

/-- A trial read of an encoding slot under `pk`. -/
def ReadOkQ (pk : PublicKey) (c : HwRead PairOut Qrom.HashDomain QMem) : Prop :=
  ∃ z K, slotOf pk z = some (.enc K.1 K.2.1 K.2.2) ∧ c = trialRead z K

/-- A program of an exempt cell off the encoding slots. -/
def ProgExQ (pk : PublicKey) (hon : HonestCells) (c : HwProg PairOut Qrom.HashDomain) : Prop :=
  ∃ z a, c = .programH z a ∧ ExemptCell pk hon z ∧
    ∀ K : Key, slotOf pk z ≠ some (.enc K.1 K.2.1 K.2.2)

/-- **The port charge of the prefix**: `0` on sponge and record ports, trial reads of encoding
slots and programs of exempt cells off the encoding slots; `1` otherwise. -/
noncomputable def bQ (pk : PublicKey) (hon : HonestCells) :
    (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port → ℕ
  | .inl (.inl (.inl _)) => 0
  | .inl (.inl (.inr c)) => @ite ℕ (ReadOkQ pk c) (Classical.propDecidable _) 0 1
  | .inl (.inr c) => @ite ℕ (ProgExQ pk hon c) (Classical.propDecidable _) 0 1
  | .inr _ => 0

theorem readOkQ_of_bQ {c : HwRead PairOut Qrom.HashDomain QMem}
    (h : bQ pk hon (.inl (.inl (.inr c))) = 0) : ReadOkQ pk c := by
  by_contra hc
  exact one_ne_zero ((ite_eq_right hc).symm.trans h)

theorem progExQ_of_bQ {c : HwProg PairOut Qrom.HashDomain}
    (h : bQ pk hon (.inl (.inr c)) = 0) : ProgExQ pk hon c := by
  by_contra hc
  exact one_ne_zero ((ite_eq_right hc).symm.trans h)

/-- A port of charge `0` is a port of the prefix. -/
theorem portOkQ_of_bQ {i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port}
    (h : bQ pk hon i = 0) : PortOkQ pk hon i := by
  rcases i with ((p | c) | c) | T
  · trivial
  · exact readOkQ_of_bQ h
  · obtain ⟨z, a, hc, hz, -⟩ := progExQ_of_bQ h
    exact ⟨z, a, hc, hz⟩
  · trivial

/-- The charge on runtime 1's ports, through `liftRead`. -/
noncomputable def dQ (pk : PublicKey) (hon : HonestCells) :
    (hwReadSpec PairOut Qrom.HashDomain SelMem).Port → ℕ
  | .inl i => bQ pk hon (.inl (.inl (.inl i)))
  | .inr c => bQ pk hon (.inl (.inl (.inr (liftRead (S := TPos) c))))

/-- The charge on the template ports at `θ`, through the realization. -/
noncomputable def tQ (θ : TVals) : (SSpecQ SelMem).Port → ℕ
  | .inl (.inl (.inl i)) => bQ (pkQ θ) (honQ θ) (.inl (.inl (.inl i)))
  | .inl (.inl (.inr c)) => bQ (pkQ θ) (honQ θ) (.inl (.inl (.inr c.1)))
  | .inl (.inr p) => bQ (pkQ θ) (honQ θ) (.inl (.inr (p.1.realize θ)))
  | .inr T => bQ (pkQ θ) (honQ θ) (.inr T)

/-! ## The realized prefix is within budget `0` -/

section charge

variable {Ω : QReg → Type}

/-- **A table cell is programmed at no cost**: exempt, at no encoding slot. -/
theorem progExQ_cellOf (θ : TVals) (p : Pos) (a : PairOut) :
    ProgExQ (pkQ θ) (honQ θ) (.programH (cellOf (seedOf θ) p (tabOf θ)) a) := by
  have hsl : slotOf (pkQ θ) (cellOf (seedOf θ) p (tabOf θ)) = some (posSlot (tabOf θ) p.1) :=
    slotOf_cell ((tabOf θ).expandedKey (seedOf θ)) (tabOf θ).root
      (slotInRange_posSlot (tabOf θ) p) _
  refine ⟨_, _, rfl, exemptCell_cellOf (seedOf θ) (tabOf θ) p, fun K h ↦ ?_⟩
  rw [hsl] at h
  exact posSlot_ne_enc (tabOf θ) p.1 K.1 K.2.1 K.2.2 (Option.some.inj h)

/-- A realized program port of a structural position has charge `0`. -/
theorem tQ_progT (θ : TVals) {p : Pos} (hp : p.1.IsStruct) :
    tQ θ (.inl (.inr ⟨progT p, trivial⟩)) = 0 := by
  show bQ (pkQ θ) (honQ θ) (.inl (.inr ((progT p).realize θ))) = 0
  rw [realize_progT hp (seedOf θ) θ]
  exact ite_eq_left (progExQ_cellOf θ p _)

/-- The realized digest port has charge `0`. -/
theorem tQ_digPort (θ : TVals) (pol : DigestPolicy) (L : Finset TPos) (msg : Message) :
    tQ θ (.inl (.inr ⟨digPort pol L msg, trivial⟩)) = 0 := by
  show bQ (pkQ θ) (honQ θ) (.inl (.inr ((digPort pol L msg).realize θ))) = 0
  rw [realize_digPort, ← cellOf_digPos (seedOf θ)]
  exact ite_eq_left (progExQ_cellOf θ (digPos msg) _)

/-- Realizing keeps the charge. -/
theorem chgO_realizeT (θ : TVals) {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (SSpecQ SelMem) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (tQ θ)) n) :
    IFreeM.IsChargeBound (realizeT θ y) (portCharge (bQ (pkQ θ) (honQ θ))) n := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens θ) ?_
  have he : (fun s cmd ↦ portCharge (L := LocalSig.instruments.{0}) (bQ (pkQ θ) (honQ θ)) s
      ((tmplLens θ).toFunA s cmd)) = portCharge (tQ θ) := by
    funext s cmd
    rcases cmd with o | ⟨((i | c) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

/-- Lifting runtime 1's programs keeps the charge. -/
theorem chgO_readLift (θ : TVals) {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (hwReadSpec PairOut Qrom.HashDomain SelMem) Ω A}
    {n : ℕ} (h : IFreeM.IsChargeBound y (portCharge (dQ (pkQ θ) (honQ θ))) n) :
    IFreeM.IsChargeBound (readLift goodQ y) (portCharge (tQ θ)) n := by
  refine IFreeM.IsChargeBound.mapLens (readLens goodQ) ?_
  have he : (fun s cmd ↦ portCharge (L := LocalSig.instruments.{0}) (tQ θ) s
      ((readLens goodQ).toFunA s cmd)) = portCharge (dQ (pkQ θ) (honQ θ)) := by
    funext s cmd
    rcases cmd with o | ⟨i | c, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

/-- A read call of a trial read. -/
theorem chgO_readCall (pk : PublicKey) (hon : HonestCells)
    (c : HwRead PairOut Qrom.HashDomain SelMem) (hc : ReadOkQ pk (liftRead (S := TPos) c))
    (B : QReg) : IFreeM.IsChargeBound (readCall c B) (portCharge (dQ pk hon)) 0 := by
  unfold readCall
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
      ⟨Nat.le_of_eq (ite_eq_left hc), fun _ ↦ trivial⟩)
    fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ trivial

/-- **The counter search under `PK.seed`** calls only trial reads of encoding slots. -/
theorem chgO_grindT (pk : PublicKey) (hon : HonestCells) (B : QReg) (K : Key) (m : Digest) :
    ∀ n cnt, IFreeM.IsChargeBound (grindT SelMem cwUpd pk.publicSeed B K m n cnt)
      (portCharge (dQ pk hon)) 0
  | 0, _ => trivial
  | n + 1, cnt => by
    have hc : ReadOkQ pk (liftRead (S := TPos) (.readH (trialCell pk.publicSeed K m cnt)
        (cwUpd K (trialCell pk.publicSeed K m cnt)))) :=
      ⟨_, K, slotOf_trialCell pk K m cnt, rfl⟩
    rw [grindT]
    refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_readCall pk hon _ hc B)
      fun r ↦ ?_
    generalize TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) = dd
    cases dd with
    | none => exact chgO_grindT pk hon B K m n (cnt + 1)
    | some x => trivial

theorem chgO_revealThen (θ : TVals) {B B' : QReg} {α : Type} (T : Finset TPos)
    (k : RevealVals TVal T × (Finset TPos × SelMem) → QComp (SSpecQ SelMem) B B' α)
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (tQ θ)) 0) :
    IFreeM.IsChargeBound (revealThen goodQ T k) (portCharge (tQ θ)) 0 :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨le_rfl, fun r ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ hk r⟩

theorem chgO_progThen (θ : TVals) {B B' : QReg} {α : Type}
    {p : LazyProg PairOut Qrom.HashDomain TPos TVal}
    (hp : tQ θ (.inl (.inr ⟨p, trivial⟩)) = 0) (k : QComp (SSpecQ SelMem) B B' α)
    (hk : IFreeM.IsChargeBound k (portCharge (tQ θ)) 0) :
    IFreeM.IsChargeBound (progThen p trivial k) (portCharge (tQ θ)) 0 :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨hp.le, fun _ ↦
    IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0)
      fun _ ↦ hk) (Nat.zero_le _)⟩

theorem chgO_progPos (θ : TVals) (B : QReg) :
    ∀ ps : List Pos, (∀ p ∈ ps, p.1.IsStruct) →
      IFreeM.IsChargeBound (progPos SelMem B ps) (portCharge (tQ θ)) 0
  | [], _ => trivial
  | p :: ps, h => chgO_progThen θ (tQ_progT θ (h p List.mem_cons_self)) _
      (chgO_progPos θ B ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

/-- **A search under the canonical `PK.seed`** calls only ports of charge `0`. -/
theorem chgO_selectT (θ : TVals) (B : QReg) (K : Key) :
    IFreeM.IsChargeBound (selectT SelMem cwUpd (tabOf θ).publicSeed B K)
      (portCharge (tQ θ)) 0 :=
  chgO_revealThen θ _ _ fun _ ↦ chgO_readLift θ
    (chgO_grindT (pkQ θ) (honQ θ) B K _ _ 0)

theorem chgO_publishT (θ : TVals) (B : QReg) (K : Key) (cnt : EncodingCounter) (x : Encoding) :
    IFreeM.IsChargeBound (publishT SelMem B K cnt x) (portCharge (tQ θ)) 0 :=
  chgO_revealThen θ _ _ fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (chgO_progPos θ B _ fun _ hp ↦ isStruct_of_mem_layerPos hp) fun _ ↦ trivial

theorem chgO_forsOpenT (θ : TVals) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    IFreeM.IsChargeBound (forsOpenT SelMem B idx lv) (portCharge (tQ θ)) 0 :=
  chgO_revealThen θ _ _ fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (chgO_progPos θ B _ fun _ hp ↦ isStruct_of_mem_forsPos hp) fun _ ↦ trivial

theorem chgO_publishAllT (θ : TVals) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer)
    (g₀ g₁ g₂ : Option (EncodingCounter × Encoding)) :
    IFreeM.IsChargeBound (publishAllT SelMem B idx lv R g₀ g₁ g₂) (portCharge (tQ θ)) 0 := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try trivial
  simp only [publishAllT]
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_forsOpenT θ B _ _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_publishT θ B _ _ _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_publishT θ B _ _ _) fun _ ↦ ?_
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_publishT θ B _ _ _) fun _ ↦ trivial

/-- **A realized reveal**: the record port, then the continuation at the values of `θ`. -/
theorem chgR_revealThen (θ : TVals) {B B' : QReg} {α : Type} (T : Finset TPos)
    (k : RevealVals TVal T × (Finset TPos × SelMem) → QComp (SSpecQ SelMem) B B' α)
    (hk : ∀ mem, IFreeM.IsChargeBound (realizeT θ (k (restrictTo T θ, mem)))
      (portCharge (bQ (pkQ θ) (honQ θ))) 0) :
    IFreeM.IsChargeBound (realizeT θ (revealThen goodQ T k))
      (portCharge (bQ (pkQ θ) (honQ θ))) 0 := by
  have e : realizeT θ (revealThen goodQ T k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments)
        (spec := recHwSpec PairOut Qrom.HashDomain TPos SelMem) (.inr T) B
        (Equiv.uniqueProd B Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).Out (.inr T) ×
            B)) (B := B) (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ (k (restrictTo T θ, mem)) :=
    rfl
  rw [e]
  exact (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨le_rfl, fun r ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ hk r⟩

/-- **A realized signature** calls only ports of charge `0`: the first reveal fixes the seed of
the searches to `PK.seed`. -/
theorem chgR_signT (θ : TVals) (pol : DigestPolicy) (B : QReg) (msg : Message) :
    IFreeM.IsChargeBound (realizeT θ (signT SelMem cwUpd pol B msg))
      (portCharge (bQ (pkQ θ) (honQ θ))) 0 := by
  rw [signT]
  refine chgR_revealThen θ _ _ fun mem₁ ↦ ?_
  have hs₀ : (tabR (restrictTo {seedC, rootC, rndC msg} θ)).publicSeed = (tabOf θ).publicSeed :=
    sigTabD_publicSeed msg
  dsimp only
  rw [hs₀]
  refine chgO_realizeT θ (chgO_revealThen θ _ _ fun r₂ ↦
    chgO_progThen θ (tQ_digPort θ pol _ msg) _ ?_)
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_selectT θ B _) fun _ ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_selectT θ B _) fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_selectT θ B _) fun _ ↦
        chgO_publishAllT θ B _ _ _ _ _ _

/-- **The realized challenger** calls only ports of charge `0`. -/
theorem chgR_challengeT (θ : TVals) (pol : DigestPolicy) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    IFreeM.IsChargeBound (realizeT θ (challengeT SelMem cwUpd pol A cmd))
      (portCharge (bQ (pkQ θ) (honQ θ))) 0 := by
  rcases cmd with o | ⟨_ | msg, E, ℓ⟩
  · exact chgO_realizeT θ (chgO_readLift θ (isChargeBound_liftOrdinary _
      ((isChargeBound_liftH_iff _ _ _).mpr (isChargeBound_mono_charge
        (fun _ a ↦ by cases a <;> exact le_rfl) (isChargeBound_zero _)))))
  · exact chgO_realizeT θ (chgO_readLift θ (isChargeBound_liftOrdinary _
      ((isChargeBound_liftH_iff _ _ _).mpr (isChargeBound_mono_charge
        (fun _ a ↦ by cases a <;> exact le_rfl) (isChargeBound_zero _)))))
  · refine (congrArg (fun y ↦ IFreeM.IsChargeBound y (portCharge (bQ (pkQ θ) (honQ θ))) 0)
      (realizeT_bind θ (signAt SelMem cwUpd pol msg E ℓ) _)).mpr ?_
    refine IFreeM.isChargeBound_bind (n₁ := 0) (n₂ := 0) ?_ fun _ _ ↦
      chgO_realizeT θ (IFreeM.isChargeBound_pure _ 0)
    rw [signAt, realizeT_bind₂]
    exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_realizeT θ (chg_act _ _ 0))
      fun _ ↦ chgR_signT θ pol _ msg

/-- **The realized challenge prefix** calls only ports of charge `0`. -/
theorem chgO_prefixQ (pol : DigestPolicy) (A : SAdversary) (θ : TVals) :
    IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge (bQ (pkQ θ) (honQ θ))) 0 := by
  unfold prefixQ prefixT
  refine chgR_revealThen θ _ _ fun mem ↦ ?_
  dsimp only
  rw [realizeT_bind₂]
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) ?_ fun _ ↦
    chgO_realizeT θ (IFreeM.isChargeBound_pure _ 0)
  unfold challengedT
  refine (congrArg (fun y ↦ IFreeM.IsChargeBound y (portCharge (bQ (pkQ θ) (honQ θ))) 0)
    (realizeT_substitute θ (challengeT SelMem cwUpd pol) _)).mpr ?_
  exact IFreeM.IsChargeBound.substitute _ (c := fun _ _ ↦ 0)
    (fun s cmd ↦ chgR_challengeT θ pol s cmd) (isChargeBound_zero _)

end charge

/-! ## No hardwired encoding cell -/

section enc

theorem encFree_of_hw {s s' : RegQ} (h : s'.2.1 = s.2.1) (hs : EncFree pk s) : EncFree pk s' := by
  intro x hx
  rw [h] at hx
  exact hs x hx

theorem encFree_progUpdate {s s' : RegQ} {c : HwProg PairOut Qrom.HashDomain}
    {z : Qrom.HashDomain} {a : PairOut} (h : s'.2.1 = progUpdate c s.2.1)
    (hc : c = .programH z a) (hz : ∀ K : Key, slotOf pk z ≠ some (.enc K.1 K.2.1 K.2.2))
    (hs : EncFree pk s) : EncFree pk s' := by
  subst hc
  intro x hx K
  rw [h] at hx
  have hx' : (Function.update s.2.1.1 z (some a) x).isSome := hx
  by_cases hxz : x = z
  · subst hxz
    exact hz K
  · rw [Function.update_of_ne hxz] at hx'
    exact hs x hx' K

/-- A read port keeps the hardwired cells. -/
theorem hwReadKraus_ne_zero_hwQ (c : HwRead PairOut Qrom.HashDomain QMem) (r : c.Result)
    {u u' : Unit} {s s' : RegQ} (h : hwReadKraus c r (u', s') (u, s) ≠ 0) :
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

/-- **A port of charge `0` keeps the support on `EncFree` registers.** -/
theorem stepEnc (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port) (hi : bQ pk hon i = 0)
    (r : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Result i)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
        (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
        (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
      (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D ↦ m.2) {s : RegQ | EncFree pk s}
        σ) :
    QuerySupportedOn (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Out i ×
      (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D ↦ m.2) {s : RegQ | EncFree pk s}
        (((runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · have hb : ((runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step
        (.inl (.inl (.inl i)))).branch r σ = MatrixMap.conj ((spongeHardwired PairOut
          Qrom.HashDomain (hwEmpty PairOut Qrom.HashDomain) m0Q).U i) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty PairOut Qrom.HashDomain)
        m0Q i r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      encFree_of_hw (congrArg Prod.fst (snd_eq_of_spongeHardwired_U_ne_zero
        (hwEmpty PairOut Qrom.HashDomain) m0Q i q.1 q'.1 q.2 q'.2 hK)) hq
  · have hb : ((runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step
        (.inl (.inl (.inr c)))).branch r σ = MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty PairOut Qrom.HashDomain)
        m0Q c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      encFree_of_hw (hwReadKraus_ne_zero_hwQ c r (u := q.1) (s := q.2) (u' := q'.1)
        (s' := q'.2) hK) hq
  · have hb : ((runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step
        (.inl (.inr c))).branch r σ = MatrixMap.conj (hwProgKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty PairOut Qrom.HashDomain)
        m0Q c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    obtain ⟨z, a, hc, -, hz⟩ := progExQ_of_bQ hi
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      encFree_progUpdate (congrArg Prod.fst (hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2)
        (u' := q'.1) (s' := q'.2) hK)) hc hz hq
  · exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
      have he := recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK
      exact encFree_of_hw (congrArg Prod.fst he :) hq

open scoped Classical in
/-- The encoding grade: `0` on `EncFree` registers, `1` otherwise. -/
noncomputable def encG (pk : PublicKey) (s : RegQ) : ℕ :=
  if EncFree pk s then 0 else 1

theorem encG_le_one (s : RegQ) : encG pk s ≤ 1 := by
  unfold encG
  split <;> omega

theorem encFree_of_encG {s : RegQ} (h : encG pk s ≤ 0) : EncFree pk s := by
  by_contra hc
  unfold encG at h
  rw [ite_eq_right hc] at h
  omega

theorem encG_of_encFree {s : RegQ} (h : EncFree pk s) : encG pk s ≤ 0 := by
  unfold encG
  rw [ite_eq_left h]

/-- The ports raise the encoding grade by at most their charge. -/
theorem encG_step (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (r : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Result i) (t : ℕ)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
        (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D)
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
        (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
      (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D ↦ encG pk m.2) (Set.Iic t) σ) :
    QuerySupportedOn (fun m : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Out i ×
      (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).D ↦ encG pk m.2)
        (Set.Iic (t + bQ pk hon i))
        (((runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q).step i).branch r σ) := by
  by_cases h1 : 1 ≤ t + bQ pk hon i
  · exact fun m m' _ ↦ ⟨Set.mem_Iic.2 ((encG_le_one _).trans h1),
      Set.mem_Iic.2 ((encG_le_one _).trans h1)⟩
  · have ht : t = 0 := by omega
    have hi : bQ pk hon i = 0 := by omega
    subst ht
    rw [hi]
    exact (stepEnc i hi r σ (hσ.imp fun m hm ↦ encFree_of_encG (Set.mem_Iic.1 hm))).imp
      fun m hm ↦ Set.mem_Iic.2 (encG_of_encFree hm)

/-- The initial operator has no hardwired cell. -/
theorem querySupportedOn_initQ_encG :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := PairOut) (Z := Qrom.HashDomain)
      m0Q).D ↦ encG pk m.2) (Set.Iic 0) initQ := by
  have h0 : EncFree pk (((Database.empty, Database.empty, Database.empty),
      hwEmpty PairOut Qrom.HashDomain, m0Q) : RegQ) := fun x hx ↦ by
    rw [show (hwEmpty PairOut Qrom.HashDomain).1 x = none from rfl] at hx
    cases hx
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty PairOut Qrom.HashDomain, m0Q) : RegQ)).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · exact ⟨Set.mem_Iic.2 ((congrArg (encG pk) he.1).symm.trans_le (encG_of_encFree h0)),
      Set.mem_Iic.2 ((congrArg (encG pk) he.2).symm.trans_le (encG_of_encFree h0))⟩
  · exact absurd rfl h

end enc

/-! ## The invariant -/

/-- **The challenge prefix satisfies `PrefixInvQ`**: its calls are sponge and record ports, trial
reads of encoding slots and programs of exempt cells, on registers without hardwired encoding
cell and without decompressed `⊥`. -/
theorem prefixInvQ (pol : DigestPolicy) (A : SAdversary) (θ : TVals) :
    PrefixInvQ (pkQ θ) (honQ θ) pol A θ := by
  have hb := chgO_prefixQ pol A θ
  have h1 := forallQueries_of_charge_step (runtimeR m0Q) (fun s ↦ encG (pkQ θ) s)
    (bQ (pkQ θ) (honQ θ)) (bQ (pkQ θ) (honQ θ)) (fun i r t σ hσ ↦ encG_step i r t σ hσ)
    .instruments (prefixQ pol A θ) hb hb querySupportedOn_initQ_encG
  have h3 := forallQueries_noBot m0Q .instruments (prefixQ pol A θ)
    (noBot_init m0Q (SubState.basis ()).matrix)
  refine ⟨_, fun i E σ hP ↦ ?_, forallQueries_and h1 h3⟩
  obtain ⟨⟨hb0, hg⟩, hnb⟩ := hP
  refine ⟨portOkQ_of_bQ hb0, ?_, hnb⟩
  exact (querySupportedOn_traceRight (q := fun a : (recHwSpec PairOut Qrom.HashDomain TPos
    SelMem).In i × RegQ ↦ encG (pkQ θ) a.2) hg).imp fun a ha ↦ encFree_of_encG (Set.mem_Iic.1 ha)

end Quantum.Qrom.Sphincs

end
