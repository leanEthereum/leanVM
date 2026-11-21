module

public import Quantum.Qrom.Xmss.Multi.Costs.Defs

@[expose] public section

/-!
# The classical costs of the `n`-user runtime 2: the invariant at the prefix's calls

The `n`-user analog of `Quantum.Qrom.Xmss.Costs.PrefixInv`. With distinct public parameters and
no leaf requested twice, the challenge prefix `prefixQN A θ` satisfies
`PrefixInvQN (honQN θ) (parQN θ) A θ` (`prefixInvQN`): every call is a sponge or record port, a
trial read of a message slot at its owner, or a program of an exempt cell; the input has no
hardwired message cell (`MsgFreeN`), no selection of a trial read's key (`selOk`) and no
decompressed `⊥`.

* **The port charge** (`bQN`, `portOkQN_of_bQN`): `0` on the allowed ports, `1` otherwise.
  `chgO_prefixQN`: the prefix is within budget `0`. The trial reads of user `i`'s searches are
  hashed under the challenger's parameter of `i`, the revealed parameter `parQN θ i`
  (`pkDN_eq`), so their owner is `i` (`ownerOf_cell`); the program ports realize honest cells of
  structural positions (`exemptCellN_of_owner`, `ownerOf_cellOfN`).
* **No hardwired message cell** (`stepMsgN`, `msgGN`): CostRun's `forallQueries_of_charge_step`.
* **No selection of the read key**: GameTSel's `forallQueries_noSelRead`.
* **No decompressed `⊥`**: EventSqrt's `forallQueries_noBot`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid HashSig LeanXmss
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT revealThen progThen readLift
  readLiftQ RevealVals liftRead tmplLens readLens NoBot forallQueries_noBot noBot_init
  forallQueries_and forallQueries_of_charge_step querySupportedOn_traceRight chg_act chg_map
  isChargeBound_zero isChargeBound_mono_charge recKraus_ne_zero realizeT_bind₂
  realizeT_substitute)
open Quantum.Qrom.MultiUser (ownerOf)

attribute [local irreducible] xmssRom

/- Instance search for the register's memory exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ} {hon : Fin n → HonestCells} {P : Fin n → PublicParameter}

/-! ## The port charge -/

/-- A trial read of a message slot at its owner. -/
def ReadOkQN (P : Fin n → PublicParameter) (c : HwRead HashOutput HashDomain (QMemN n)) :
    Prop :=
  ∃ z i l e, slotOf z = some (.msg l e) ∧ ownerOf P prefixOf z = some i ∧
    c = trialReadN z (i, l, e)

/-- A program of an exempt cell off the message slots. -/
def ProgExQN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter)
    (c : HwProg HashOutput HashDomain) : Prop :=
  ∃ z a, c = .programH z a ∧ ExemptCellN hon P z ∧ ∀ l e, slotOf z ≠ some (.msg l e)

/-- **The port charge of the prefix**: `0` on sponge and record ports, trial reads of message
slots at their owner and programs of exempt cells off the message slots; `1` otherwise. -/
noncomputable def bQN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter) :
    (RSpecN n (SelMemN n)).Port → ℕ
  | .inl (.inl (.inl _)) => 0
  | .inl (.inl (.inr c)) => @ite ℕ (ReadOkQN P c) (Classical.propDecidable _) 0 1
  | .inl (.inr c) => @ite ℕ (ProgExQN hon P c) (Classical.propDecidable _) 0 1
  | .inr _ => 0

theorem readOkQN_of_bQN {c : HwRead HashOutput HashDomain (QMemN n)}
    (h : bQN hon P (.inl (.inl (.inr c))) = 0) : ReadOkQN P c := by
  by_contra hc
  exact one_ne_zero ((ite_eq_right hc).symm.trans h)

theorem progExQN_of_bQN {c : HwProg HashOutput HashDomain} (h : bQN hon P (.inl (.inr c)) = 0) :
    ProgExQN hon P c := by
  by_contra hc
  exact one_ne_zero ((ite_eq_right hc).symm.trans h)

/-- A port of charge `0` is a port of the prefix. -/
theorem portOkQN_of_bQN {i : (RSpecN n (SelMemN n)).Port} (h : bQN hon P i = 0) :
    PortOkQN hon P i := by
  rcases i with ((p | c) | c) | T
  · trivial
  · exact readOkQN_of_bQN h
  · exact progExQN_of_bQN h
  · trivial

/-- The charge on runtime 1's ports, through `liftRead`. -/
noncomputable def dQN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter) :
    (hwReadSpec HashOutput HashDomain (SelMemN n)).Port → ℕ
  | .inl i => bQN hon P (.inl (.inl (.inl i)))
  | .inr c => bQN hon P (.inl (.inl (.inr (liftRead (S := HPosN n) c))))

/-- The charge on the template ports at `θ`, through the realization. -/
noncomputable def tQN (θ : HPosN n → Digest) : (XSpecN (SelMemN n) n).Port → ℕ
  | .inl (.inl (.inl i)) => bQN (honQN θ) (parQN θ) (.inl (.inl (.inl i)))
  | .inl (.inl (.inr c)) => bQN (honQN θ) (parQN θ) (.inl (.inl (.inr c.1)))
  | .inl (.inr p) => bQN (honQN θ) (parQN θ) (.inl (.inr (p.1.realize θ)))
  | .inr T => bQN (honQN θ) (parQN θ) (.inr T)

/-! ## The prefix is within budget `0` -/

section charge

variable {Ω : QReg → Type}

theorem slotOf_cellOf_ne_msgN (S0 : MasterSeed) (v : QTable) {p : Pos} (hp : p.IsStruct)
    (l : Layer) (e : KeyIndex) : slotOf (cellOf S0 p v) ≠ some (.msg l e) := by
  rw [slotOf_cellOf S0 v p]
  intro h
  have h2 := Option.some.inj h
  cases p with
  | chain => cases h2
  | leaf => cases h2
  | node => cases h2
  | seed | param | prf | rndBottom | rndTop => exact absurd hp id

/-- A realized program port of user `i`'s structural position has charge `0`. -/
theorem tQN_progTN (θ : HPosN n → Digest) (hP : PDistinct (tabOfN θ)) (i : Fin n) {p : Pos}
    (hp : p.IsStruct) : tQN θ (.inl (.inr ⟨progTN i p, trivial⟩)) = 0 := by
  show bQN (honQN θ) (parQN θ) (.inl (.inr ((progTN i p).realize θ))) = 0
  rw [realize_progTN hp i (seedsOf θ i) θ]
  have h1 : p ≠ .seed := by
    rintro rfl
    exact hp
  have h2 : p ≠ .param := by
    rintro rfl
    exact hp
  have ho : ownerOf (parQN θ) prefixOf (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) = some i :=
    ownerOf_cellOfN hP (seedsOf θ) i h1 h2
  have h : ProgExQN (honQN θ) (parQN θ)
      (.programH (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) (tabOf (userOf θ i) p)) :=
    ⟨_, _, rfl, exemptCellN_of_owner ho (exemptCell_cellOf (seedsOf θ i) (tabOf (userOf θ i)) hp),
      slotOf_cellOf_ne_msgN (seedsOf θ i) (tabOf (userOf θ i)) hp⟩
  exact ite_eq_left h

/-- Realizing keeps the charge. -/
theorem chgO_realizeTN (θ : HPosN n → Digest) {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (XSpecN (SelMemN n) n) Ω A} {k : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (tQN θ)) k) :
    IFreeM.IsChargeBound (realizeT θ y) (portCharge (bQN (honQN θ) (parQN θ))) k := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens (good := goodQN) (M := SelMemN n) θ) ?_
  have he : (fun s cmd ↦ portCharge (L := LocalSig.instruments.{0}) (bQN (honQN θ) (parQN θ)) s
      ((tmplLens (good := goodQN) (M := SelMemN n) θ).toFunA s cmd)) = portCharge (tQN θ) := by
    funext s cmd
    rcases cmd with o | ⟨((i | c) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

/-- Lifting runtime 1's programs keeps the charge. -/
theorem chgO_readLiftN (θ : HPosN n → Digest) {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (hwReadSpec HashOutput HashDomain (SelMemN n)) Ω A}
    {k : ℕ} (h : IFreeM.IsChargeBound y (portCharge (dQN (honQN θ) (parQN θ))) k) :
    IFreeM.IsChargeBound (readLift (goodQN (n := n)) y) (portCharge (tQN θ)) k := by
  refine IFreeM.IsChargeBound.mapLens (readLens (goodQN (n := n))) ?_
  have he : (fun s cmd ↦ portCharge (L := LocalSig.instruments.{0}) (tQN θ) s
      ((readLens (goodQN (n := n))).toFunA s cmd)) = portCharge (dQN (honQN θ) (parQN θ)) := by
    funext s cmd
    rcases cmd with o | ⟨i | c, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

/-- A read call of a trial read. -/
theorem chgO_readCallN (c : HwRead HashOutput HashDomain (SelMemN n))
    (hc : ReadOkQN P (liftRead (S := HPosN n) c)) (B : QReg) :
    IFreeM.IsChargeBound (readCall c B) (portCharge (dQN hon P)) 0 := by
  unfold readCall
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
      ⟨Nat.le_of_eq (ite_eq_left hc), fun _ ↦ trivial⟩)
    fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ trivial

/-- **User `i`'s randomizer search** under its parameter calls only trial reads of message slots
owned by `i`. -/
theorem chgO_grindTN (hP : Function.Injective P) (i : Fin n) (B : QReg) (l : Layer)
    (e : KeyIndex) (message : MsgBytes) (base : Randomizer) :
    ∀ k trial, IFreeM.IsChargeBound
      (grindT (SelMemN n) (cwUpdN i) (P i) B l e message base k trial) (portCharge (dQN hon P)) 0
  | 0, _ => trivial
  | k + 1, trial => by
    have hc : ReadOkQN P (liftRead (S := HPosN n) (.readH (trialCell (P i) l e message base trial)
        (cwUpdN i l e (trialCell (P i) l e message base trial)))) :=
      ⟨_, i, l, e, slotOf_cell (P i) (show Addressable (.msg l e) from trivial) _,
        ownerOf_cell hP i (show Addressable (.msg l e) from trivial) rfl _, rfl⟩
    rw [grindT]
    refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_readCallN _ hc B) fun r ↦ ?_
    split
    · trivial
    · exact chgO_grindTN hP i B l e message base k (trial + 1)

theorem chgO_revealThenN (θ : HPosN n → Digest) {B B' : QReg} {α : Type} (T : Finset (HPosN n))
    (k : RevealVals (HDN n) T × (Finset (HPosN n) × SelMemN n) →
      QComp (XSpecN (SelMemN n) n) B B' α)
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (tQN θ)) 0) :
    IFreeM.IsChargeBound (revealThen goodQN T k) (portCharge (tQN θ)) 0 :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨le_rfl, fun r ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ hk r⟩

theorem chgO_progThenN (θ : HPosN n → Digest) (hP : PDistinct (tabOfN θ)) (i : Fin n)
    {B B' : QReg} {α : Type} {p : Pos} (hp : p.IsStruct) (k : QComp (XSpecN (SelMemN n) n) B B' α)
    (hk : IFreeM.IsChargeBound k (portCharge (tQN θ)) 0) :
    IFreeM.IsChargeBound (progThen (progTN i p) trivial k) (portCharge (tQN θ)) 0 :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨(tQN_progTN θ hP i hp).le, fun _ ↦
    IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0)
      fun _ ↦ hk) (Nat.zero_le _)⟩

theorem chgO_progPosN (θ : HPosN n → Digest) (hP : PDistinct (tabOfN θ)) (i : Fin n)
    (B : QReg) : ∀ ps : List Pos, (∀ p ∈ ps, p.IsStruct) →
      IFreeM.IsChargeBound (progPosN (SelMemN n) i B ps) (portCharge (tQN θ)) 0
  | [], _ => trivial
  | p :: ps, h => chgO_progThenN θ hP i (h p List.mem_cons_self) _
      (chgO_progPosN θ hP i B ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

theorem chgO_selectTN (θ : HPosN n → Digest) (hP : PDistinct (tabOfN θ)) (i : Fin n)
    (B : QReg) (l : Layer) (e : KeyIndex) (message : MsgBytes) (rnd : Pos) :
    IFreeM.IsChargeBound (selectTN (SelMemN n) cwUpdN i (parQN θ i) B l e message rnd)
      (portCharge (tQN θ)) 0 :=
  chgO_revealThenN θ _ _ fun _ ↦ chgO_readLiftN θ (chgO_grindTN hP i B l e message _ _ 0)

theorem chgO_publishTN (θ : HPosN n → Digest) (hP : PDistinct (tabOfN θ)) (i : Fin n)
    (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer) (x : Encoding) :
    IFreeM.IsChargeBound (publishTN (SelMemN n) i B l e ρ x) (portCharge (tQN θ)) 0 :=
  chgO_revealThenN θ _ _ fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (chgO_progPosN θ hP i B _ fun _ hp ↦ isStruct_of_mem_layerPos hp) fun _ ↦ trivial

/-- The top layer's search or memo: no call on a memo hit. -/
theorem chgO_topTN (θ : HPosN n → Digest) (hP : PDistinct (tabOfN θ)) (i : Fin n) (B : QReg)
    (r : SigningRequest) (h : Option TopSel) :
    IFreeM.IsChargeBound (topTN (SelMemN n) cwUpdN i (parQN θ i) B r h) (portCharge (tQN θ)) 0 :=
  by
  rcases h with _ | o
  · exact chgO_revealThenN θ _ _ fun _ ↦ chgO_selectTN θ hP i B _ _ _ _
  · trivial

theorem chgO_pubBothN (θ : HPosN n → Digest) (hP : PDistinct (tabOfN θ)) (i : Fin n) (B : QReg)
    (r : SigningRequest) (gb gt : TopSel) :
    IFreeM.IsChargeBound (pubBothN (publishTN (SelMemN n) i B) r gb gt) (portCharge (tQN θ)) 0
    := by
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · trivial
  · trivial
  · trivial
  · simp only [pubBothN]
    exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_publishTN θ hP i B _ _ _ _)
      fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_publishTN θ hP i B _ _ _ _)
        fun _ ↦ trivial

/-- **A signature of user `i`** calls only ports of charge `0`. -/
theorem chgO_signTN (θ : HPosN n → Digest) (hP : PDistinct (tabOfN θ)) (i : Fin n) (B : QReg)
    (r : SigningRequest) (h : Option TopSel) :
    IFreeM.IsChargeBound (signTN (SelMemN n) cwUpdN i (parQN θ i) B r h) (portCharge (tQN θ)) 0
    := by
  unfold signTN signWithN
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_selectTN θ hP i B _ _ _ _) fun gb ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_topTN θ hP i B r h) fun gt ↦
      chg_map _ _ (chgO_pubBothN θ hP i B r gb gt)

/-- **The challenger** with the users' parameters calls only ports of charge `0`. -/
theorem chgO_challengeTN (θ : HPosN n → Digest) (hP : PDistinct (tabOfN θ)) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} (memoSpec n) A) :
    IFreeM.IsChargeBound (challengeTN (SelMemN n) cwUpdN (parQN θ) A cmd) (portCharge (tQN θ))
      0 := by
  rcases cmd with o | ⟨_ | ⟨i, r, h⟩, E, ℓ⟩
  · exact chgO_readLiftN θ (isChargeBound_liftOrdinary _ ((isChargeBound_liftH_iff _ _ _).mpr
      (isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (isChargeBound_zero _))))
  · exact chgO_readLiftN θ (isChargeBound_liftOrdinary _ ((isChargeBound_liftH_iff _ _ _).mpr
      (isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (isChargeBound_zero _))))
  · exact IFreeM.isChargeBound_bind (n₁ := 0) (n₂ := 0) (FreeM₂.isChargeBound_bind
      (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ chgO_signTN θ hP i _ r h) fun _ _ ↦
        IFreeM.isChargeBound_pure _ 0

/-- **The realized memo transform against the challenger** with the users' parameters calls only
ports of charge `0`. -/
theorem chgO_challengedTN (θ : HPosN n → Digest) (hP : PDistinct (tabOfN θ))
    {P' : Fin n → PublicParameter} (hP' : ∀ i, P' i = parQN θ i) {A B : QReg} {α : Type}
    (x : QComp (memoSpec n) A B α) :
    IFreeM.IsChargeBound (realizeT θ (challengedTN (SelMemN n) cwUpdN P' x))
      (portCharge (bQN (honQN θ) (parQN θ))) 0 := by
  obtain rfl : P' = parQN θ := funext hP'
  unfold challengedTN
  refine (congrArg (fun y ↦ IFreeM.IsChargeBound y (portCharge (bQN (honQN θ) (parQN θ))) 0)
    (realizeT_substitute θ (challengeTN (SelMemN n) cwUpdN (parQN θ)) x)).mpr ?_
  exact IFreeM.IsChargeBound.substitute _ (c := fun _ _ ↦ 0)
    (fun s cmd ↦ chgO_realizeTN θ (chgO_challengeTN θ hP s cmd)) (isChargeBound_zero _)

/-- A realized reveal, then a continuation of charge `0` at the revealed values. -/
theorem chgO_realizeT_revealThenN (θ : HPosN n → Digest) {B C : QReg} {α : Type}
    (T : Finset (HPosN n))
    (k : RevealVals (HDN n) T × (Finset (HPosN n) × SelMemN n) →
      QComp (XSpecN (SelMemN n) n) B C α)
    (hk : ∀ mem, IFreeM.IsChargeBound (realizeT θ (k (restrictTo T θ, mem)))
      (portCharge (bQN hon P)) 0) :
    IFreeM.IsChargeBound (realizeT θ (revealThen goodQN T k)) (portCharge (bQN hon P)) 0 := by
  have e : realizeT θ (revealThen goodQN T k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpecN n (SelMemN n)) (.inr T)
        B (Equiv.uniqueProd B Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((RSpecN n (SelMemN n)).Out (.inr T) × B)) (B := B)
            (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ (k (restrictTo T θ, mem)) :=
    rfl
  refine (congrArg (fun y ↦ IFreeM.IsChargeBound y (portCharge (bQN hon P)) 0) e).mpr ?_
  exact (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨le_rfl, fun r ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ hk r⟩

/-- **The realized challenge prefix** calls only ports of charge `0`, with distinct public
parameters. -/
theorem chgO_prefixQN (A : MuAdversary n) (θ : HPosN n → Digest) (hP : PDistinct (tabOfN θ)) :
    IFreeM.IsChargeBound (prefixQN A θ) (portCharge (bQN (honQN θ) (parQN θ))) 0 := by
  unfold prefixQN prefixTN
  refine chgO_realizeT_revealThenN θ _ _ fun mem ↦ ?_
  rw [realizeT_bind₂]
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (chgO_challengedTN θ hP (fun i ↦ (congrArg PublicKey.parameter (pkDN_eq θ i)).trans rfl) _)
    fun _ ↦ trivial

end charge

/-! ## No hardwired message cell -/

section msg

theorem msgFreeN_of_hw {s s' : RRegN n (SelMemN n)} (h : s'.2.1 = s.2.1) (hs : MsgFreeN s) :
    MsgFreeN s' := by
  intro x hx
  rw [h] at hx
  exact hs x hx

theorem msgFreeN_progUpdate {s s' : RRegN n (SelMemN n)} {c : HwProg HashOutput HashDomain}
    {z : HashDomain} {a : HashOutput} (h : s'.2.1 = progUpdate c s.2.1)
    (hc : c = .programH z a) (hz : ∀ l e, slotOf z ≠ some (.msg l e)) (hs : MsgFreeN s) :
    MsgFreeN s' := by
  subst hc
  intro x hx l e
  rw [h] at hx
  have hx' : (Function.update s.2.1.1 z (some a) x).isSome := hx
  by_cases hxz : x = z
  · subst hxz
    exact hz l e
  · rw [Function.update_of_ne hxz] at hx'
    exact hs x hx' l e

/-- A read port keeps the hardwired cells. -/
theorem hwReadKraus_ne_zero_hwQN (c : HwRead HashOutput HashDomain (QMemN n)) (r : c.Result)
    {u u' : Unit} {s s' : RRegN n (SelMemN n)} (h : hwReadKraus c r (u', s') (u, s) ≠ 0) :
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

/-- **A port of charge `0` keeps the support on `MsgFreeN` registers.** -/
theorem stepMsgN (i : (RSpecN n (SelMemN n)).Port) (hi : bQN hon P i = 0)
    (r : (RSpecN n (SelMemN n)).Result i)
    (σ : Matrix ((RSpecN n (SelMemN n)).In i ×
        (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D)
      ((RSpecN n (SelMemN n)).In i ×
        (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D) ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).In i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D ↦ m.2)
        {s : RRegN n (SelMemN n) | MsgFreeN s} σ) :
    QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).Out i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D ↦ m.2)
        {s : RRegN n (SelMemN n) | MsgFreeN s}
        (((runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · have hb : ((runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step
        (.inl (.inl (.inl i)))).branch r σ = MatrixMap.conj ((spongeHardwired HashOutput
          HashDomain (hwEmpty HashOutput HashDomain) (m0N (n := n))).U i) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty HashOutput HashDomain)
        (m0N (n := n)) i r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      msgFreeN_of_hw (congrArg Prod.fst (snd_eq_of_spongeHardwired_U_ne_zero
        (hwEmpty HashOutput HashDomain) (m0N (n := n)) i q.1 q'.1 q.2 q'.2 hK)) hq
  · have hb : ((runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step
        (.inl (.inl (.inr c)))).branch r σ = MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain)
        (m0N (n := n)) c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      msgFreeN_of_hw (hwReadKraus_ne_zero_hwQN c r (u := q.1) (s := q.2) (u' := q'.1)
        (s' := q'.2) hK) hq
  · have hb : ((runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step
        (.inl (.inr c))).branch r σ = MatrixMap.conj (hwProgKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty HashOutput HashDomain)
        (m0N (n := n)) c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    obtain ⟨z, a, hc, -, hz⟩ := progExQN_of_bQN hi
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      msgFreeN_progUpdate (congrArg Prod.fst (hwProgKraus_ne_zero_snd c r (u := q.1)
        (s := q.2) (u' := q'.1) (s' := q'.2) hK)) hc hz hq
  · exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
      have he := recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK
      exact msgFreeN_of_hw (congrArg Prod.fst he :) hq

open scoped Classical in
/-- The message grade: `0` on `MsgFreeN` registers, `1` otherwise. -/
noncomputable def msgGN (s : RRegN n (SelMemN n)) : ℕ :=
  if MsgFreeN s then 0 else 1

theorem msgGN_le_one (s : RRegN n (SelMemN n)) : msgGN s ≤ 1 := by
  unfold msgGN
  split <;> omega

theorem msgFreeN_of_msgGN {s : RRegN n (SelMemN n)} (h : msgGN s ≤ 0) : MsgFreeN s := by
  by_contra hc
  unfold msgGN at h
  rw [ite_eq_right hc] at h
  omega

theorem msgGN_of_msgFreeN {s : RRegN n (SelMemN n)} (h : MsgFreeN s) : msgGN s ≤ 0 := by
  unfold msgGN
  rw [ite_eq_left h]

/-- The ports raise the message grade by at most their charge. -/
theorem msgGN_step (i : (RSpecN n (SelMemN n)).Port) (r : (RSpecN n (SelMemN n)).Result i)
    (t : ℕ)
    (σ : Matrix ((RSpecN n (SelMemN n)).In i ×
        (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D)
      ((RSpecN n (SelMemN n)).In i ×
        (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D) ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).In i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D ↦ msgGN m.2)
        (Set.Iic t) σ) :
    QuerySupportedOn (fun m : (RSpecN n (SelMemN n)).Out i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).D ↦ msgGN m.2)
        (Set.Iic (t + bQN hon P i))
        (((runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).step i).branch r σ) := by
  by_cases h1 : 1 ≤ t + bQN hon P i
  · exact fun m m' _ ↦ ⟨Set.mem_Iic.2 ((msgGN_le_one _).trans h1),
      Set.mem_Iic.2 ((msgGN_le_one _).trans h1)⟩
  · have ht : t = 0 := by omega
    have hi : bQN hon P i = 0 := by omega
    subst ht
    rw [hi]
    exact (stepMsgN i hi r σ (hσ.imp fun m hm ↦ msgFreeN_of_msgGN (Set.mem_Iic.1 hm))).imp
      fun m hm ↦ Set.mem_Iic.2 (msgGN_of_msgFreeN hm)

/-- The initial operator has no hardwired cell. -/
theorem querySupportedOn_initQN_msgGN :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := HashOutput) (Z := HashDomain)
      (m0N (n := n))).D ↦ msgGN m.2) (Set.Iic 0) (initQN (n := n)) := by
  have h0 : MsgFreeN (((Database.empty, Database.empty, Database.empty),
      hwEmpty HashOutput HashDomain, m0N) : RRegN n (SelMemN n)) := fun x hx ↦ by
    rw [show (hwEmpty HashOutput HashDomain).1 x = none from rfl] at hx
    cases hx
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty HashOutput HashDomain, m0N) : RRegN n (SelMemN n))).matrix) m m'
      ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · exact ⟨Set.mem_Iic.2 ((congrArg msgGN he.1).symm.trans_le (msgGN_of_msgFreeN h0)),
      Set.mem_Iic.2 ((congrArg msgGN he.2).symm.trans_le (msgGN_of_msgFreeN h0))⟩
  · exact absurd rfl h

end msg

/-! ## The invariant -/

/-- **The challenge prefix satisfies `PrefixInvQN`** for distinct public parameters and an
adversary that never reuses a leaf of a user: its calls are sponge and record ports, trial reads
of message slots at their owner and programs of exempt cells, on registers without hardwired
message cell, without a selection of the read key and without decompressed `⊥`. -/
theorem prefixInvQN (A : MuAdversary n) (hleaf : NoLeafReuseMu A) (θ : HPosN n → Digest)
    (hP : PDistinct (tabOfN θ)) : PrefixInvQN (honQN θ) (parQN θ) A θ := by
  have hb := chgO_prefixQN A θ hP
  have h1 := forallQueries_of_charge_step (runtimeR (m0N (n := n))) (fun s ↦ msgGN s)
    (bQN (honQN θ) (parQN θ)) (bQN (honQN θ) (parQN θ)) (fun i r t σ hσ ↦ msgGN_step i r t σ hσ)
    .instruments (prefixQN A θ) hb hb querySupportedOn_initQN_msgGN
  have h3 := forallQueries_noBot (m0N (n := n)) .instruments (prefixQN A θ)
    (noBot_init (m0N (n := n)) (SubState.basis ()).matrix)
  have h4 := forallQueries_noSelRead A hleaf θ (m0N (n := n)) rfl (SubState.basis ()).matrix
  refine ⟨_, fun i E σ hQ ↦ ?_, forallQueries_and h1 (forallQueries_and h3 h4)⟩
  obtain ⟨⟨hb0, hg⟩, hnb, hsel⟩ := hQ
  refine ⟨portOkQN_of_bQN hb0, ?_, querySupportedOn_traceRight
    (q := fun a : (RSpecN n (SelMemN n)).In i × RRegN n (SelMemN n) ↦ a.2) hsel, hnb⟩
  exact (querySupportedOn_traceRight (q := fun a : (RSpecN n (SelMemN n)).In i ×
    RRegN n (SelMemN n) ↦ msgGN a.2) hg).imp fun a ha ↦ msgFreeN_of_msgGN (Set.mem_Iic.1 ha)

end Quantum.Qrom.Xmss.Multi

end
