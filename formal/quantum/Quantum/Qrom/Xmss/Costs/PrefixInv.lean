module

public import Quantum.Qrom.Xmss.Costs.Ports

@[expose] public section

/-!
# The classical costs of runtime 2: the invariant at the prefix's calls

The challenge prefix `prefixQ A θ` satisfies `PrefixInvQ (honQ θ) A θ` (`prefixInvQ`), the
hypothesis of `twPQ_le`: every call of the prefix is a sponge or record port, a trial read of a
message slot, or a program of an exempt cell; the input has no hardwired message cell
(`MsgFree`) and no decompressed `⊥`.

* **The port charge** (`bQ`, `portOkQ_of_bQ`): `0` on the allowed ports (programs of exempt
  cells off the message slots), `1` otherwise. `chgO_prefixQ`: the prefix is within budget `0`
  (`chgO_grindT`, `chgO_selectT`, `chgO_publishT`, `chgO_signT`, `chgO_challengeT`,
  `chgO_prefixT`; the program ports realize honest cells of structural positions,
  `exemptCell_cellOf`, `slotOf_cellOf_ne_msg`).
* **No hardwired message cell** (`stepMsg`, `forallQueries_msgG`): every port of charge `0`
  keeps the support on `MsgFree` registers (sponge, read and record ports keep the hardwired
  cells; a program hardwires one cell off the message slots), CostRun's
  `forallQueries_of_charge_step` with the grade `msgG`.
* **No decompressed `⊥`**: EventSqrt's `forallQueries_noBot`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid HashSig LeanXmss
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT revealThen progThen readLift
  readLiftQ RevealVals liftRead tmplLens readLens NoBot forallQueries_noBot noBot_init
  forallQueries_and forallQueries_of_charge_step querySupportedOn_traceRight chg_act
  isChargeBound_zero isChargeBound_mono_charge recKraus_ne_zero)

attribute [local irreducible] xmssRom

variable {hon : HonestCells}

/-! ## The port charge -/

/-- A trial read of a message slot. -/
def ReadOkQ (c : HwRead HashOutput HashDomain QMem) : Prop :=
  ∃ z l e, slotOf z = some (.msg l e) ∧ c = trialRead z l e

/-- A program of an exempt cell off the message slots. -/
def ProgExQ (hon : HonestCells) (c : HwProg HashOutput HashDomain) : Prop :=
  ∃ z a, c = .programH z a ∧ ExemptCell hon z ∧ ∀ l e, slotOf z ≠ some (.msg l e)

/-- **The port charge of the prefix**: `0` on sponge and record ports, trial reads of message
slots and programs of exempt cells off the message slots; `1` otherwise. -/
noncomputable def bQ (hon : HonestCells) :
    (recHwSpec HashOutput HashDomain HPos SelMem).Port → ℕ
  | .inl (.inl (.inl _)) => 0
  | .inl (.inl (.inr c)) => @ite ℕ (ReadOkQ c) (Classical.propDecidable _) 0 1
  | .inl (.inr c) => @ite ℕ (ProgExQ hon c) (Classical.propDecidable _) 0 1
  | .inr _ => 0

theorem readOkQ_of_bQ {c : HwRead HashOutput HashDomain QMem}
    (h : bQ hon (.inl (.inl (.inr c))) = 0) : ReadOkQ c := by
  by_contra hc
  exact one_ne_zero ((ite_eq_right hc).symm.trans h)

theorem progExQ_of_bQ {c : HwProg HashOutput HashDomain} (h : bQ hon (.inl (.inr c)) = 0) :
    ProgExQ hon c := by
  by_contra hc
  exact one_ne_zero ((ite_eq_right hc).symm.trans h)

/-- A port of charge `0` is a port of the prefix. -/
theorem portOkQ_of_bQ {i : (recHwSpec HashOutput HashDomain HPos SelMem).Port}
    (h : bQ hon i = 0) : PortOkQ hon i := by
  rcases i with ((p | c) | c) | T
  · trivial
  · exact readOkQ_of_bQ h
  · obtain ⟨z, a, hc, hz, -⟩ := progExQ_of_bQ h
    exact ⟨z, a, hc, hz⟩
  · trivial

/-- The charge on runtime 1's ports, through `liftRead`. -/
noncomputable def dQ (hon : HonestCells) :
    (hwReadSpec HashOutput HashDomain SelMem).Port → ℕ
  | .inl i => bQ hon (.inl (.inl (.inl i)))
  | .inr c => bQ hon (.inl (.inl (.inr (liftRead (S := HPos) c))))

/-- The charge on the template ports at `θ`, through the realization. -/
noncomputable def tQ (θ : HPos → Digest) : (XSpec SelMem).Port → ℕ
  | .inl (.inl (.inl i)) => bQ (honQ θ) (.inl (.inl (.inl i)))
  | .inl (.inl (.inr c)) => bQ (honQ θ) (.inl (.inl (.inr c.1)))
  | .inl (.inr p) => bQ (honQ θ) (.inl (.inr (p.1.realize θ)))
  | .inr T => bQ (honQ θ) (.inr T)

/-! ## The prefix is within budget `0` -/

section charge

variable {Ω : QReg → Type}

theorem slotOf_cellOf_ne_msg (S0 : MasterSeed) (v : QTable) {p : Pos} (hp : p.IsStruct)
    (l : Layer) (e : KeyIndex) : slotOf (cellOf S0 p v) ≠ some (.msg l e) := by
  rw [slotOf_cellOf S0 v p]
  intro h
  have h2 := Option.some.inj h
  cases p with
  | chain => cases h2
  | leaf => cases h2
  | node => cases h2
  | seed | param | prf | rndBottom | rndTop => exact absurd hp id

/-- A realized program port of a structural position has charge `0`. -/
theorem tQ_progT (θ : HPos → Digest) {p : Pos} (hp : p.IsStruct) :
    tQ θ (.inl (.inr ⟨progT p, trivial⟩)) = 0 := by
  show bQ (honQ θ) (.inl (.inr ((progT p).realize θ))) = 0
  rw [realize_progT hp (seedOf θ) θ]
  have h : ProgExQ (honQ θ) (.programH (cellOf (seedOf θ) p (tabOf θ)) (tabOf θ p)) :=
    ⟨_, _, rfl, exemptCell_cellOf (seedOf θ) (tabOf θ) hp,
      slotOf_cellOf_ne_msg (seedOf θ) (tabOf θ) hp⟩
  exact ite_eq_left h

/-- Realizing keeps the charge. -/
theorem chgO_realizeT (θ : HPos → Digest) {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (XSpec SelMem) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (tQ θ)) n) :
    IFreeM.IsChargeBound (realizeT θ y) (portCharge (bQ (honQ θ))) n := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens θ) ?_
  have he : (fun s cmd ↦ portCharge (L := LocalSig.instruments.{0}) (bQ (honQ θ)) s
      ((tmplLens θ).toFunA s cmd)) = portCharge (tQ θ) := by
    funext s cmd
    rcases cmd with o | ⟨((i | c) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

/-- Lifting runtime 1's programs keeps the charge. -/
theorem chgO_readLift (θ : HPos → Digest) {A : QReg}
    {y : QuantumComp LocalSig.instruments.{0} (hwReadSpec HashOutput HashDomain SelMem) Ω A}
    {n : ℕ} (h : IFreeM.IsChargeBound y (portCharge (dQ (honQ θ))) n) :
    IFreeM.IsChargeBound (readLift goodQ y) (portCharge (tQ θ)) n := by
  refine IFreeM.IsChargeBound.mapLens (readLens goodQ) ?_
  have he : (fun s cmd ↦ portCharge (L := LocalSig.instruments.{0}) (tQ θ) s
      ((readLens goodQ).toFunA s cmd)) = portCharge (dQ (honQ θ)) := by
    funext s cmd
    rcases cmd with o | ⟨i | c, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

/-- A read call of a trial read. -/
theorem chgO_readCall (hon : HonestCells) (c : HwRead HashOutput HashDomain SelMem)
    (hc : ReadOkQ (liftRead (S := HPos) c)) (B : QReg) :
    IFreeM.IsChargeBound (readCall c B) (portCharge (dQ hon)) 0 := by
  unfold readCall
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
      ⟨Nat.le_of_eq (ite_eq_left hc), fun _ ↦ trivial⟩)
    fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ trivial

/-- **The randomizer search** calls only trial reads of message slots. -/
theorem chgO_grindT (hon : HonestCells) (P : PublicParameter) (B : QReg) (l : Layer)
    (e : KeyIndex) (message : MsgBytes) (base : Randomizer) :
    ∀ n trial, IFreeM.IsChargeBound (grindT SelMem cwUpd P B l e message base n trial)
      (portCharge (dQ hon)) 0
  | 0, _ => trivial
  | n + 1, trial => by
    have hc : ReadOkQ (liftRead (S := HPos) (.readH (trialCell P l e message base trial)
        (cwUpd l e (trialCell P l e message base trial)))) :=
      ⟨_, l, e, slotOf_cell P (show Addressable (.msg l e) from trivial) _, rfl⟩
    rw [grindT]
    refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_readCall hon _ hc B) fun r ↦ ?_
    split
    · trivial
    · exact chgO_grindT hon P B l e message base n (trial + 1)

theorem chgO_revealThen (θ : HPos → Digest) {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals HD T × (Finset HPos × SelMem) → QComp (XSpec SelMem) B B' α)
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (tQ θ)) 0) :
    IFreeM.IsChargeBound (revealThen goodQ T k) (portCharge (tQ θ)) 0 :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨le_rfl, fun r ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ hk r⟩

theorem chgO_progThen (θ : HPos → Digest) {B B' : QReg} {α : Type} {p : Pos}
    (hp : p.IsStruct) (k : QComp (XSpec SelMem) B B' α)
    (hk : IFreeM.IsChargeBound k (portCharge (tQ θ)) 0) :
    IFreeM.IsChargeBound (progThen (progT p) trivial k) (portCharge (tQ θ)) 0 :=
  (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨(tQ_progT θ hp).le, fun _ ↦
    IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0)
      fun _ ↦ hk) (Nat.zero_le _)⟩

theorem chgO_progPos (θ : HPos → Digest) (B : QReg) :
    ∀ ps : List Pos, (∀ p ∈ ps, p.IsStruct) →
      IFreeM.IsChargeBound (progPos SelMem B ps) (portCharge (tQ θ)) 0
  | [], _ => trivial
  | p :: ps, h => chgO_progThen θ (h p List.mem_cons_self) _
      (chgO_progPos θ B ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

theorem chgO_selectT (θ : HPos → Digest) (P : PublicParameter) (B : QReg) (l : Layer)
    (e : KeyIndex) (message : MsgBytes) (rnd : Pos) :
    IFreeM.IsChargeBound (selectT SelMem cwUpd P B l e message rnd) (portCharge (tQ θ)) 0 :=
  chgO_revealThen θ _ _ fun _ ↦ chgO_readLift θ (chgO_grindT (honQ θ) P B l e message _ _ 0)

theorem chgO_publishT (θ : HPos → Digest) (B : QReg) (l : Layer) (e : KeyIndex)
    (ρ : Randomizer) (x : Encoding) :
    IFreeM.IsChargeBound (publishT SelMem B l e ρ x) (portCharge (tQ θ)) 0 :=
  chgO_revealThen θ _ _ fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (chgO_progPos θ B _ fun _ hp ↦ isStruct_of_mem_layerPos hp) fun _ ↦ trivial

/-- **A signature** calls only ports of charge `0`. -/
theorem chgO_signT (θ : HPos → Digest) (P : PublicParameter) (B : QReg) (r : SigningRequest) :
    IFreeM.IsChargeBound (signT SelMem cwUpd P B r) (portCharge (tQ θ)) 0 := by
  unfold signT
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_selectT θ P B _ _ _ _) fun gb ↦
    chgO_revealThen θ _ _ fun rr ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
      (chgO_selectT θ P B _ _ _ _) fun gt ↦ ?_
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · trivial
  · trivial
  · trivial
  · exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_publishT θ B _ _ _ _) fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgO_publishT θ B _ _ _ _) fun _ ↦ trivial

/-- **The challenger** calls only ports of charge `0`. -/
theorem chgO_challengeT (θ : HPos → Digest) (P : PublicParameter) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0}
      (SufCma.advSpec SigningRequest (Option Signature)) A) :
    IFreeM.IsChargeBound (challengeT SelMem cwUpd P A cmd) (portCharge (tQ θ)) 0 := by
  rcases cmd with o | ⟨_ | r, E, ℓ⟩
  · exact chgO_readLift θ (isChargeBound_liftOrdinary _ ((isChargeBound_liftH_iff _ _ _).mpr
      (isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (isChargeBound_zero _))))
  · exact chgO_readLift θ (isChargeBound_liftOrdinary _ ((isChargeBound_liftH_iff _ _ _).mpr
      (isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (isChargeBound_zero _))))
  · exact IFreeM.isChargeBound_bind (n₁ := 0) (n₂ := 0) (FreeM₂.isChargeBound_bind
      (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ chgO_signT θ P _ r) fun _ _ ↦
        IFreeM.isChargeBound_pure _ 0

/-- **The challenge prefix** calls only ports of charge `0`. -/
theorem chgO_prefixT (θ : HPos → Digest) (A : Adversary) :
    IFreeM.IsChargeBound (prefixT SelMem cwUpd A) (portCharge (tQ θ)) 0 :=
  chgO_revealThen θ _ _ fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    (IFreeM.IsChargeBound.substitute (challengeT SelMem cwUpd _) (c := fun _ _ ↦ 0)
      (fun s cmd ↦ chgO_challengeT θ _ s cmd) (isChargeBound_zero _)) fun _ ↦ trivial

/-- **The realized challenge prefix** calls only ports of charge `0`. -/
theorem chgO_prefixQ (A : Adversary) (θ : HPos → Digest) :
    IFreeM.IsChargeBound (prefixQ A θ) (portCharge (bQ (honQ θ))) 0 :=
  chgO_realizeT θ (chgO_prefixT θ A)

end charge

/-! ## No hardwired message cell -/

section msg

theorem msgFree_of_hw {s s' : RReg SelMem} (h : s'.2.1 = s.2.1) (hs : MsgFree s) :
    MsgFree s' := by
  intro x hx
  rw [h] at hx
  exact hs x hx

theorem msgFree_progUpdate {s s' : RReg SelMem} {c : HwProg HashOutput HashDomain}
    {z : HashDomain} {a : HashOutput} (h : s'.2.1 = progUpdate c s.2.1)
    (hc : c = .programH z a) (hz : ∀ l e, slotOf z ≠ some (.msg l e)) (hs : MsgFree s) :
    MsgFree s' := by
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
theorem hwReadKraus_ne_zero_hwQ (c : HwRead HashOutput HashDomain QMem) (r : c.Result)
    {u u' : Unit} {s s' : RReg SelMem} (h : hwReadKraus c r (u', s') (u, s) ≠ 0) :
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

/-- **A port of charge `0` keeps the support on `MsgFree` registers.** -/
theorem stepMsg (i : (recHwSpec HashOutput HashDomain HPos SelMem).Port) (hi : bQ hon i = 0)
    (r : (recHwSpec HashOutput HashDomain HPos SelMem).Result i)
    (σ : Matrix ((recHwSpec HashOutput HashDomain HPos SelMem).In i ×
        (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D)
      ((recHwSpec HashOutput HashDomain HPos SelMem).In i ×
        (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain HPos SelMem).In i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D ↦ m.2) {s : RReg SelMem | MsgFree s}
        σ) :
    QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain HPos SelMem).Out i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D ↦ m.2) {s : RReg SelMem | MsgFree s}
        (((runtimeR (X := HashOutput) (Z := HashDomain) m0Q).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · have hb : ((runtimeR (X := HashOutput) (Z := HashDomain) m0Q).step
        (.inl (.inl (.inl i)))).branch r σ = MatrixMap.conj ((spongeHardwired HashOutput
          HashDomain (hwEmpty HashOutput HashDomain) m0Q).U i) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty HashOutput HashDomain)
        m0Q i r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      msgFree_of_hw (congrArg Prod.fst (snd_eq_of_spongeHardwired_U_ne_zero
        (hwEmpty HashOutput HashDomain) m0Q i q.1 q'.1 q.2 q'.2 hK)) hq
  · have hb : ((runtimeR (X := HashOutput) (Z := HashDomain) m0Q).step
        (.inl (.inl (.inr c)))).branch r σ = MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain)
        m0Q c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      msgFree_of_hw (hwReadKraus_ne_zero_hwQ c r (u := q.1) (s := q.2) (u' := q'.1)
        (s' := q'.2) hK) hq
  · have hb : ((runtimeR (X := HashOutput) (Z := HashDomain) m0Q).step
        (.inl (.inr c))).branch r σ = MatrixMap.conj (hwProgKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty HashOutput HashDomain)
        m0Q c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    obtain ⟨z, a, hc, -, hz⟩ := progExQ_of_bQ hi
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      msgFree_progUpdate (congrArg Prod.fst (hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2)
        (u' := q'.1) (s' := q'.2) hK)) hc hz hq
  · exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
      have he := recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK
      exact msgFree_of_hw (congrArg Prod.fst he :) hq

open scoped Classical in
/-- The message grade: `0` on `MsgFree` registers, `1` otherwise. -/
noncomputable def msgG (s : RReg SelMem) : ℕ :=
  if MsgFree s then 0 else 1

theorem msgG_le_one (s : RReg SelMem) : msgG s ≤ 1 := by
  unfold msgG
  split <;> omega

theorem msgFree_of_msgG {s : RReg SelMem} (h : msgG s ≤ 0) : MsgFree s := by
  by_contra hc
  unfold msgG at h
  rw [ite_eq_right hc] at h
  omega

theorem msgG_of_msgFree {s : RReg SelMem} (h : MsgFree s) : msgG s ≤ 0 := by
  unfold msgG
  rw [ite_eq_left h]

/-- The ports raise the message grade by at most their charge. -/
theorem msgG_step (i : (recHwSpec HashOutput HashDomain HPos SelMem).Port)
    (r : (recHwSpec HashOutput HashDomain HPos SelMem).Result i) (t : ℕ)
    (σ : Matrix ((recHwSpec HashOutput HashDomain HPos SelMem).In i ×
        (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D)
      ((recHwSpec HashOutput HashDomain HPos SelMem).In i ×
        (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain HPos SelMem).In i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D ↦ msgG m.2) (Set.Iic t) σ) :
    QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain HPos SelMem).Out i ×
      (runtimeR (X := HashOutput) (Z := HashDomain) m0Q).D ↦ msgG m.2) (Set.Iic (t + bQ hon i))
        (((runtimeR (X := HashOutput) (Z := HashDomain) m0Q).step i).branch r σ) := by
  by_cases h1 : 1 ≤ t + bQ hon i
  · exact fun m m' _ ↦ ⟨Set.mem_Iic.2 ((msgG_le_one _).trans h1),
      Set.mem_Iic.2 ((msgG_le_one _).trans h1)⟩
  · have ht : t = 0 := by omega
    have hi : bQ hon i = 0 := by omega
    subst ht
    rw [hi]
    exact (stepMsg i hi r σ (hσ.imp fun m hm ↦ msgFree_of_msgG (Set.mem_Iic.1 hm))).imp
      fun m hm ↦ Set.mem_Iic.2 (msgG_of_msgFree hm)

/-- The initial operator has no hardwired cell. -/
theorem querySupportedOn_initQ_msgG :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := HashOutput) (Z := HashDomain)
      m0Q).D ↦ msgG m.2) (Set.Iic 0) initQ := by
  have h0 : MsgFree (((Database.empty, Database.empty, Database.empty),
      hwEmpty HashOutput HashDomain, m0Q) : RReg SelMem) := fun x hx ↦ by
    rw [show (hwEmpty HashOutput HashDomain).1 x = none from rfl] at hx
    cases hx
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty HashOutput HashDomain, m0Q) : RReg SelMem)).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · exact ⟨Set.mem_Iic.2 ((congrArg msgG he.1).symm.trans_le (msgG_of_msgFree h0)),
      Set.mem_Iic.2 ((congrArg msgG he.2).symm.trans_le (msgG_of_msgFree h0))⟩
  · exact absurd rfl h

end msg

/-! ## The invariant -/

/-- **The challenge prefix satisfies `PrefixInvQ`**: its calls are sponge and record ports, trial
reads of message slots and programs of exempt cells, on registers without hardwired message cell
and without decompressed `⊥`. -/
theorem prefixInvQ (A : Adversary) (θ : HPos → Digest) : PrefixInvQ (honQ θ) A θ := by
  have hb := chgO_prefixQ A θ
  have h1 := forallQueries_of_charge_step (runtimeR m0Q) (fun s ↦ msgG s) (bQ (honQ θ))
    (bQ (honQ θ)) (fun i r t σ hσ ↦ msgG_step i r t σ hσ) .instruments (prefixQ A θ) hb hb
    querySupportedOn_initQ_msgG
  have h3 := forallQueries_noBot m0Q .instruments (prefixQ A θ)
    (noBot_init m0Q (SubState.basis ()).matrix)
  refine ⟨_, fun i E σ hP ↦ ?_, forallQueries_and h1 h3⟩
  obtain ⟨⟨hb0, hg⟩, hnb⟩ := hP
  refine ⟨portOkQ_of_bQ hb0, ?_, hnb⟩
  exact (querySupportedOn_traceRight (q := fun a : (recHwSpec HashOutput HashDomain HPos
    SelMem).In i × RReg SelMem ↦ msgG a.2) hg).imp fun a ha ↦ msgFree_of_msgG (Set.mem_Iic.1 ha)

end Quantum.Qrom.Xmss

end
