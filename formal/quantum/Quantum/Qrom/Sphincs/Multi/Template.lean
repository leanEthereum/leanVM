module

public import Quantum.Qrom.Sphincs.Multi.Table
public import Quantum.Qrom.Sphincs.Multi.Memo
public import Quantum.Qrom.Sphincs.Multi.StreamN
public import Quantum.Qrom.Sphincs.GameT
public import Quantum.Qrom.Sphincs.StreamGame

@[expose] public section

/-!
# leanSPHINCS's multi-user runtime-2 game in the QROM, as a template program

The `n`-user analog of `Quantum.Qrom.Sphincs.Template`. Runtime 2 hardwires a cell of a user's
honest table only once its input and value are public; the users' hidden values enter the game
only through reveal ports.

**Hidden coordinates** (`TPosN n := Fin n × TPos`): user `i`'s single-user coordinates `(i, s)`
(its master seed, positions, digest cells, digest stream, marks). `userOf θ i` is user `i`'s
single-user hidden values; `tabOfN θ`, `seedsOf θ` the table of `n` users and the master seeds,
`thetaOfN S0 w` their inverse (pads `0`); `tvalsEquivN` adds the users' pads. `atU i T` is user
`i`'s copy of the single-user coordinates `T`, `labU L i` user `i`'s part of a label.

**Ports.** `progTN i p` hardwires the cell of user `i`'s structural position `p` with its value
(`realize_progTN`); `digPortN pol i L M` user `i`'s digest cell of `M` with the pair at the
policy's coordinate on user `i`'s label (`realize_digPortN_msgPol`). A trial read of user `i`'s
key `K` updates the memory with `upd i K z`.

* `selectTN`, `forsOpenTN`, `publishTN`, `publishAllTN`: as `selectT`, ... on user `i`'s
  coordinates; `selOrMemoTN`: a memoized selection without any call, or the search.
* `signTN pols i B M h`: `signT` at user `i`'s policy with user `i`'s memo `h`; the answer is the
  signature and the request's `MemoAns`.
* `muGameT M upd pols valid A`: reveal all users' public keys, the adversary's memo transform
  (`memoFromS`) against `challengeTN` (hash calls regrouped on port `h`, signing requests by
  `signTN`), the verification through read ports under the forged user's key, the winning
  condition with distinct `PK.seed`s (`pdOK`) and every user's transcript valid. `prefixTN`,
  `verifyTN`, `muGameT_eq_prefixTN_bind`.
* `disc_muGameT`, `keepsLab_muGameT`, `viewBy_muGameT`, `viewByOn_muGameT`: the game reveals
  before it programs and its reads keep the label.
-/

open Matrix
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime
open Quantum.Sponge (HwReg hwReadSpec hwReadCmdSpec readCall)
open Quantum.Sphincs (Key keyOf msgPos uavg_comp_equiv)
open Quantum.Xmss.Hybrid (LazyProg restrictTo uavg ViewBy ViewByOn lazy_const suppAt_empty
  KeepsLab keepsLab_bind keepsLab₂_bind keepsLab_substitute keepsLab_act keepsLab_revealThen
  keepsLab_progThen keepsLab_readLift)
open Quantum.Xmss.Assembly (tmplSpec runtimeR realizeT revealThen progThen readLift readLiftQ
  RevealVals Disc disc_revealThen disc_progThen disc_readLift disc_act disc_bind disc₂_bind
  disc_substitute viewBy_runtimeR_of_disc revealThen_bind)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec muChallenge withMuSignLog MuSignLog)

attribute [local irreducible] sphincsRom

variable {n : ℕ}

-- The adversary's commands with the memo, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "MemoPS" n => QuantumComp.toIPFunctor LocalSig.instruments.{0} (memoSpecS n)

/-! ## Hidden coordinates of `n` users -/

/-- **The hidden coordinates of `n` users**: user `i`'s single-user coordinates. -/
abbrev TPosN (n : ℕ) : Type :=
  Fin n × TPos

/-- A coordinate's value: its single-user value. -/
abbrev TValN (n : ℕ) : TPosN n → Type :=
  fun a ↦ TVal a.2

/-- **The hidden values of `n` users.** -/
abbrev TValsN (n : ℕ) : Type :=
  (a : TPosN n) → TValN n a

/-- User `i`'s hidden values. -/
def userOf (θ : TValsN n) (i : Fin n) : TVals :=
  fun s ↦ θ (i, s)

/-- **The table of `n` users of the hidden values.** -/
def tabOfN (θ : TValsN n) : QTableN n :=
  fun a ↦ tabOf (userOf θ a.1) a.2

/-- **The users' master seeds of the hidden values.** -/
def seedsOf (θ : TValsN n) : Fin n → MasterSeed :=
  fun i ↦ seedOf (userOf θ i)

/-- The hidden values of the users' master seeds and a table of `n` users: the pads are `0`. -/
def thetaOfN (S0 : Fin n → MasterSeed) (w : QTableN n) : TValsN n :=
  fun a ↦ thetaOf (S0 a.1) (w.user a.1) a.2

theorem userOf_thetaOfN (S0 : Fin n → MasterSeed) (w : QTableN n) (i : Fin n) :
    userOf (thetaOfN S0 w) i = thetaOf (S0 i) (w.user i) :=
  rfl

theorem user_tabOfN (θ : TValsN n) (i : Fin n) : (tabOfN θ).user i = tabOf (userOf θ i) :=
  rfl

@[simp]
theorem tabOfN_thetaOfN (S0 : Fin n → MasterSeed) (w : QTableN n) :
    tabOfN (thetaOfN S0 w) = w :=
  funext fun a ↦ congrFun (tabOf_thetaOf (S0 a.1) (w.user a.1)) a.2

@[simp]
theorem seedsOf_thetaOfN (S0 : Fin n → MasterSeed) (w : QTableN n) :
    seedsOf (thetaOfN S0 w) = S0 :=
  rfl

/-- User `i`'s values after an update at one of its coordinates. -/
theorem userOf_update_self (θ : TValsN n) (i : Fin n) (s : TPos) (d : TVal s) :
    userOf (Function.update θ (i, s) d) i = Function.update (userOf θ i) s d := by
  funext t
  by_cases h : t = s
  · subst h
    exact (Function.update_self (i, t) d θ).trans (Function.update_self t d (userOf θ i)).symm
  · exact (Function.update_of_ne (a := ((i, t) : TPosN n)) (a' := ((i, s) : TPosN n))
      (fun e ↦ h (congrArg Prod.snd e)) d θ).trans (Function.update_of_ne h d (userOf θ i)).symm

/-- Another user's values after an update at user `i`'s coordinate. -/
theorem userOf_update_of_ne (θ : TValsN n) {i j : Fin n} (h : j ≠ i) (s : TPos) (d : TVal s) :
    userOf (Function.update θ (i, s) d) j = userOf θ j :=
  funext fun t ↦ by
    change Function.update θ (i, s) d (j, t) = θ (j, t)
    exact Function.update_of_ne (fun e ↦ h (congrArg Prod.fst e)) _ θ

/-- The hidden values of the users' master seeds, a table of `n` users and the users' pads. -/
def thetaOfPadsN (S0 : Fin n → MasterSeed) (w : QTableN n) (r : Fin n → TPads) : TValsN n :=
  fun a ↦ tvalsEquiv.symm ((S0 a.1, w.user a.1), r a.1) a.2

theorem userOf_thetaOfPadsN (S0 : Fin n → MasterSeed) (w : QTableN n) (r : Fin n → TPads)
    (i : Fin n) : userOf (thetaOfPadsN S0 w r) i = tvalsEquiv.symm ((S0 i, w.user i), r i) :=
  rfl

/-- **The hidden values are the users' master seeds, the table of `n` users and the pads.** -/
def tvalsEquivN : TValsN n ≃ ((Fin n → MasterSeed) × QTableN n) × (Fin n → TPads) where
  toFun θ := ((seedsOf θ, tabOfN θ), fun i ↦ (tvalsEquiv (userOf θ i)).2)
  invFun x := thetaOfPadsN x.1.1 x.1.2 x.2
  left_inv θ := funext fun a ↦ congrFun (tvalsEquiv.symm_apply_apply (userOf θ a.1)) a.2
  right_inv x := by
    have h : ∀ i, tvalsEquiv (userOf (thetaOfPadsN x.1.1 x.1.2 x.2) i) =
        ((x.1.1 i, x.1.2.user i), x.2 i) := fun i ↦ tvalsEquiv.apply_symm_apply _
    refine Prod.ext (Prod.ext (funext fun i ↦ congrArg (fun y ↦ y.1.1) (h i))
      (funext fun a ↦ congrFun (congrArg (fun y ↦ y.1.2) (h a.1)) a.2))
      (funext fun i ↦ congrArg Prod.snd (h i))

/-- **Averaging over the hidden values a function of the seeds and the table** averages over the
seeds and the table. -/
theorem uavg_seedsOf_tabOfN (F : (Fin n → MasterSeed) → QTableN n → ℝ≥0∞) :
    uavg (fun θ : TValsN n ↦ F (seedsOf θ) (tabOfN θ)) =
      uavg (fun x : (Fin n → MasterSeed) × QTableN n ↦ F x.1 x.2) :=
  (uavg_comp_equiv tvalsEquivN
    fun y : ((Fin n → MasterSeed) × QTableN n) × (Fin n → TPads) ↦ F y.1.1 y.1.2).trans
    (uavg_comp_fst fun x : (Fin n → MasterSeed) × QTableN n ↦ F x.1 x.2)

/- Instance search for the registers over `Finset (TPosN n)` exceeds the default size: named
instances. -/
set_option synthInstance.maxSize 2000 in
/-- Runtime 2's register with the memory of `n` users has decidable equality. -/
instance instDecidableEqHwRegTPosN (n : ℕ) (M : Type) [DecidableEq M] :
    DecidableEq (HwReg PairOut HashDomain (Finset (TPosN n) × M)) :=
  Quantum.Sponge.HwReg.instDecidableEq

set_option synthInstance.maxSize 2000 in
/-- Runtime 2's register with the memory of `n` users is finite. -/
instance instFintypeHwRegTPosN (n : ℕ) (M : Type) [Fintype M] [DecidableEq M] :
    Fintype (HwReg PairOut HashDomain (Finset (TPosN n) × M)) :=
  Quantum.Sponge.HwReg.instFintype

/-! ## Revealed values -/

/-- User `i`'s table of the values revealed on `T` (a default value off `T`). -/
noncomputable def tabRN {T : Finset (TPosN n)} (w : RevealVals (TValN n) T) (i : Fin n) :
    QTable :=
  tabOf (SValsN.user (extWN w) i)

/-- User `i`'s pair revealed at a coordinate (a default value off `T`). -/
noncomputable def pairRN {T : Finset (TPosN n)} (w : RevealVals (TValN n) T) (i : Fin n)
    (s : TPos) : PairOut :=
  pairAt (SValsN.user (extWN w) i) s

theorem pairRN_restrictTo {T : Finset (TPosN n)} {i : Fin n} {s : TPos} (h : (i, s) ∈ T)
    (θ : TValsN n) : pairRN (restrictTo T θ) i s = pairAt (userOf θ i) s := by
  cases s with
  | val p => exact extWN_of_mem _ h
  | dig m => exact extWN_of_mem _ h
  | str j => exact extWN_of_mem _ h
  | asg m j => rfl

/-- **User `i`'s revealed values agree with `θ`** on the single-user coordinates revealed. -/
theorem tabRN_restrictTo_congr {T : Finset (TPosN n)} {i : Fin n} {U : Finset TPos}
    (hU : ∀ s ∈ U, (i, s) ∈ T) (θ : TValsN n) :
    ∀ s ∈ U, pairAt (SValsN.user (extWN (restrictTo T θ)) i) s = pairAt (userOf θ i) s :=
  fun _ hs ↦ pairRN_restrictTo (hU _ hs) θ

theorem atU_restrict {i : Fin n} (U : Finset TPos) : ∀ s ∈ U, (i, s) ∈ atU i U :=
  fun _ hs ↦ mk_mem_atU i hs

/-! ## Template program ports -/

/-- Every template program port is allowed. -/
def goodQN : LazyProg PairOut HashDomain (TPosN n) (TValN n) → Prop :=
  fun _ ↦ True

/-- **The program port of user `i`'s structural position `p`**: hardwire its cell to its value,
both read from user `i`'s coordinates `progNeed p` (the master seed is not read). -/
noncomputable def progTN (i : Fin n) (p : Pos) : LazyProg PairOut HashDomain (TPosN n) (TValN n) :=
  .programH (atU i (progNeed p)) fun w ↦ (cellOf 0 p (tabRN w i), tabRN w i p)

theorem need_progTN (i : Fin n) (p : Pos) : (progTN i p).need = atU i (progNeed p) :=
  rfl

/-- **The program port of user `i`'s structural position, realized**: its cell at user `i`'s
master seed, with its value. -/
theorem realize_progTN {p : Pos} (hp : p.1.IsStruct) (i : Fin n) (θ : TValsN n) :
    (progTN i p).realize θ =
      .programH (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) (tabOf (userOf θ i) p) := by
  have hm := tabRN_restrictTo_congr (atU_restrict (i := i) (progNeed p)) θ
  have hc : cellOf 0 p (tabRN (restrictTo (atU i (progNeed p)) θ) i) =
      cellOf (seedsOf θ i) p (tabOf (userOf θ i)) :=
    cellOf_tabOf_congr hp 0 _ fun s hs ↦ hm s (cellNeed_subset_progNeed p hs)
  have hv : tabRN (restrictTo (atU i (progNeed p)) θ) i p = tabOf (userOf θ i) p :=
    hm _ (coordOf_mem_progNeed p)
  simp only [progTN, LazyProg.realize, hc, hv]

/-- **User `i`'s digest port of `M`**: hardwire user `i`'s digest cell of `M` (call 0 of `H_msg`)
to the pair at the policy's coordinate on user `i`'s label. -/
noncomputable def digPortN (pol : DigestPolicy) (i : Fin n) (L : Finset (TPosN n))
    (msg : Message) : LazyProg PairOut HashDomain (TPosN n) (TValN n) :=
  .programH (atU i (digNeed pol (labU L i) msg)) fun w ↦
    (digestCell (tabRN w i).publicSeed (tabRN w i).root ((tabRN w i).randomizer msg) msg 0,
      pairRN w i (pol.out (labU L i) msg))

theorem need_digPortN (pol : DigestPolicy) (i : Fin n) (L : Finset (TPosN n)) (msg : Message) :
    (digPortN pol i L msg).need = atU i (digNeed pol (labU L i) msg) :=
  rfl

/-- **User `i`'s digest port, realized**: the digest cell at user `i`'s hidden values with the
policy's pair. -/
theorem realize_digPortN (pol : DigestPolicy) (i : Fin n) (L : Finset (TPosN n))
    (msg : Message) (θ : TValsN n) :
    (digPortN pol i L msg).realize θ =
      .programH (digestCell (tabOf (userOf θ i)).publicSeed (tabOf (userOf θ i)).root
        ((tabOf (userOf θ i)).randomizer msg) msg 0)
        (pairAt (userOf θ i) (pol.out (labU L i) msg)) := by
  have hm := tabRN_restrictTo_congr (atU_restrict (i := i) (digNeed pol (labU L i) msg)) θ
  have hs : (tabRN (restrictTo (atU i (digNeed pol (labU L i) msg)) θ) i).publicSeed =
      (tabOf (userOf θ i)).publicSeed :=
    publicSeed_tabOf_congr (hm _ (by simp [digNeed]))
  have hr : (tabRN (restrictTo (atU i (digNeed pol (labU L i) msg)) θ) i).root =
      (tabOf (userOf θ i)).root :=
    root_tabOf_congr (hm _ (by simp [digNeed]))
  have hR : (tabRN (restrictTo (atU i (digNeed pol (labU L i) msg)) θ) i).randomizer msg =
      (tabOf (userOf θ i)).randomizer msg :=
    randomizer_tabOf_congr (hm _ (by simp [digNeed]))
  have ho : pairRN (restrictTo (atU i (digNeed pol (labU L i) msg)) θ) i (pol.out (labU L i) msg) =
      pairAt (userOf θ i) (pol.out (labU L i) msg) :=
    hm _ (by simp [digNeed])
  simp only [digPortN, LazyProg.realize, hs, hr, hR, ho]

/-- **At `msgPol` user `i`'s digest port is the digest cell's program port.** -/
theorem realize_digPortN_msgPol (i : Fin n) (L : Finset (TPosN n)) (msg : Message)
    (θ : TValsN n) :
    (digPortN msgPol i L msg).realize θ =
      .programH (cellOf (seedsOf θ i) (digPos msg) (tabOf (userOf θ i)))
        (tabOf (userOf θ i) (digPos msg)) := by
  rw [realize_digPortN, cellOf_digPos]
  rfl

/-- User `i`'s digest of `M` from the revealed values `w` on the policy's coordinates at the
label `L`. -/
noncomputable def digestTN (pol : DigestPolicy) (i : Fin n) (L : Finset (TPosN n))
    (msg : Message) {T : Finset (TPosN n)} (w : RevealVals (TValN n) T) : MessageDigest :=
  digestOfPair (pairRN w i (pol.out (labU L i) msg))

/-! ## Multi-user ports of the game -/

/-- The secret keys carrying nothing. -/
def noKeysS : Fin n → SecretKey :=
  fun _ ↦ 0

/-- **Distinct `PK.seed`s** of the public keys (classically decided). -/
noncomputable def pdOK (pks : Fin n → PublicKey) : Bool :=
  @decide (Function.Injective fun i ↦ (pks i).publicSeed) (Classical.propDecidable _)

theorem pdOK_eq_true {pks : Fin n → PublicKey}
    (h : Function.Injective fun i ↦ (pks i).publicSeed) : pdOK pks = true :=
  @decide_eq_true _ (Classical.propDecidable _) h

/-- The answer to user `i`'s signing request `q` with the adversary's register held, from a
program `sgn` beside the held register. -/
noncomputable def signAtSN {spec : QuantumOracleSpec.{0, 0}} (i : Fin n) (q : Message × KeyMemo)
    (E : QReg) {A : QReg} (ℓ : A ≃ (memoSpecS n).In (.sign i q) × E)
    (sgn : (B : QReg) → QComp spec B B (Option Signature × MemoAns)) :
    QComp spec A (QReg.of ((memoSpecS n).Out (.sign i q) × E)) (Option Signature × MemoAns) :=
  (QComp.act (spec := spec)
    (B := QReg.of ((SufCma.advSpec Message (Option Signature)).Out (.sign q.1) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ sgn _

/-- **The users' digest policy on the hybrid side**: `msgPol` for every user. -/
def msgPolN (n : ℕ) : Fin n → DigestPolicy :=
  fun _ ↦ msgPol

/-- **The users' digest policy on the event side**: `strPol` for every user. -/
noncomputable def strPolN (n : ℕ) : Fin n → DigestPolicy :=
  fun _ ↦ strPol

/-! ## The template game -/

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **leanSPHINCS's multi-user template signature in the QROM**, with inner memory `M`. -/
abbrev XSpecSN (n : ℕ) : QuantumOracleSpec.{0, 0} :=
  tmplSpec PairOut HashDomain (TPosN n) (TValN n) M goodQN

variable (upd : Fin n → TrialUpd M)

/-- Call user `i`'s program ports of the positions `ps` in order. -/
noncomputable def progPosN (i : Fin n) (B : QReg) : List Pos → QComp (XSpecSN M n) B B Unit
  | [] => QuantumComp₂.pure ()
  | p :: ps => progThen (progTN i p) trivial (progPosN i B ps)

/-- **User `i`'s FORS opening of instance `idx` at the leaves `lv`**: reveal its coordinates,
hardwire the positions it makes public, and read the opening from the revealed values. -/
noncomputable def forsOpenTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    QComp (XSpecSN M n) B B (ForsTreeIndex → ForsTreeOpening) :=
  revealThen goodQN (atU i (forsReveal idx lv)) fun r ↦
    (progPosN M i B (forsPos idx lv)).bind fun _ ↦
      QuantumComp₂.pure ((tabRN r.1 i).forsOpening idx lv)

/-- **The counter search of user `i`'s key `K`** under `PK.seed = seed`: reveal the value `K`
signs, then the trials on it through reads updating the memory with `upd i`. -/
noncomputable def selectTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) :
    QComp (XSpecSN M n) B B SelS :=
  revealThen goodQN (atU i {vcoord (msgPos K)}) fun r₀ ↦
    readLiftQ goodQN (grindT M (upd i) seed B K ((tabRN r₀.1 i).valuePos (msgPos K))
      encodingAttemptLimit 0)

/-- **User `i`'s selection of key `K` or its memo**: a memoized selection without any call, or
the counter search. -/
noncomputable def selOrMemoTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) :
    Option SelS → QComp (XSpecSN M n) B B SelS
  | some o => QuantumComp₂.pure o
  | none => selectTN M upd i seed B K

/-- **The publication of user `i`'s layer signature by `K`** with counter `c` and codeword `x`:
reveal the layer's coordinates, hardwire the positions it makes public, and read the signature
from the revealed values. -/
noncomputable def publishTN (i : Fin n) (B : QReg) (K : Key) (c : EncodingCounter)
    (x : Encoding) : QComp (XSpecSN M n) B B (LayerSignature K.1) :=
  revealThen goodQN (atU i (layerReveal K x)) fun r ↦
    (progPosN M i B (layerPos K x)).bind fun _ ↦
      QuantumComp₂.pure ⟨c, fun j ↦ (tabRN r.1 i).chainValue K.1 K.2.1 K.2.2 j (x j).val,
        (tabRN r.1 i).authPath K.1 K.2.1 K.2.2⟩

/-- **The publication of user `i`'s signature** from the three selections: when all three
succeed, the FORS opening and the three layer signatures; `none` otherwise, with nothing revealed
or hardwired. -/
noncomputable def publishAllTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) :
    SelS → SelS → SelS → QComp (XSpecSN M n) B B (Option Signature)
  | some (c₀, x₀), some (c₁, x₁), some (c₂, x₂) =>
    (forsOpenTN M i B idx lv).bind fun fo ↦
    (publishTN M i B (keyOf 0 idx) c₀ x₀).bind fun bottom ↦
    (publishTN M i B (keyOf 1 idx) c₁ x₁).bind fun middle ↦
    (publishTN M i B (keyOf 2 idx) c₂ x₂).bind fun top ↦
      QuantumComp₂.pure (some ⟨R, fo, KeyGenerationAndSigning.layerSignatures bottom middle top⟩)
  | _, _, _ => QuantumComp₂.pure none

/-- **User `i`'s signature in runtime 2** with user `i`'s memo `h`: reveal `PK.seed`, `PK.root`
and `R(M)` of user `i` (the result carries the label `L` before), the digest's coordinates under
user `i`'s policy on user `i`'s part of `L`, hardwire the digest cell; the three layers' selections
(memoized or searched); the publication; the answer and the request's `MemoAns`. -/
noncomputable def signTN (pols : Fin n → DigestPolicy) (i : Fin n) (B : QReg) (msg : Message)
    (h : KeyMemo) : QComp (XSpecSN M n) B B (Option Signature × MemoAns) :=
  revealThen goodQN (atU i {seedC, rootC, rndC msg}) fun r₁ ↦
  revealThen goodQN (atU i ((pols i).need (labU r₁.2.1 i) msg)) fun r₂ ↦
  progThen (digPortN (pols i) i r₁.2.1 msg) trivial <|
  (selOrMemoTN M upd i (tabRN r₁.1 i).publicSeed B
      (keyOf 0 (digestIndex (digestTN (pols i) i r₁.2.1 msg r₂.1)))
      (h (keyOf 0 (digestIndex (digestTN (pols i) i r₁.2.1 msg r₂.1))))).bind fun g₀ ↦
  (selOrMemoTN M upd i (tabRN r₁.1 i).publicSeed B
      (keyOf 1 (digestIndex (digestTN (pols i) i r₁.2.1 msg r₂.1)))
      (h (keyOf 1 (digestIndex (digestTN (pols i) i r₁.2.1 msg r₂.1))))).bind fun g₁ ↦
  (selOrMemoTN M upd i (tabRN r₁.1 i).publicSeed B
      (keyOf 2 (digestIndex (digestTN (pols i) i r₁.2.1 msg r₂.1)))
      (h (keyOf 2 (digestIndex (digestTN (pols i) i r₁.2.1 msg r₂.1))))).bind fun g₂ ↦
  (publishAllTN M i B (digestIndex (digestTN (pols i) i r₁.2.1 msg r₂.1))
      (digestForsLeaves (digestTN (pols i) i r₁.2.1 msg r₂.1)) ((tabRN r₁.1 i).randomizer msg)
      g₀ g₁ g₂).map fun s ↦
    (s, (digestIndex (digestTN (pols i) i r₁.2.1 msg r₂.1), layerSels g₀ g₁ g₂))

/-- **The multi-user challenger of runtime 2** at the users' policies `pols`: local operations
and hash calls as `muChallenge` (regrouped, lifted to port `h`), a signing request of user `i`
answered by `signTN`. -/
noncomputable def challengeTN (pols : Fin n → DigestPolicy) :
    IPFunctor.CommandSubstitution (MemoPS n)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (XSpecSN M n))
  | A, .prim o => readLift goodQN ((liftH (regroupCalls hmsgRoute
      (muChallenge sphincsRom (noKeysS (n := n)) A (.prim o)))).liftOrdinary
        (t := hwReadCmdSpec PairOut HashDomain M))
  | A, .query .hash E ℓ => readLift goodQN ((liftH (regroupCalls hmsgRoute
      (muChallenge sphincsRom (noKeysS (n := n)) A (.query .hash E ℓ)))).liftOrdinary
        (t := hwReadCmdSpec PairOut HashDomain M))
  | _, .query (.sign i q) E ℓ =>
      QuantumComp.bind (signAtSN i q E ℓ fun B ↦ signTN M upd pols i B q.1 q.2) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's memo transform against the challenger of runtime 2. -/
noncomputable def challengedTN (pols : Fin n → DigestPolicy) {A B : QReg} {α : Type}
    (x : QComp (memoSpecS n) A B α) : QComp (XSpecSN M n) A B α :=
  IPFunctor.IFreeM.substitute (challengeTN M upd pols) x

/-- The coordinates of all users' public keys: their `PK.seed` and `PK.root`. -/
def pkRevealN : Finset (TPosN n) :=
  Finset.univ ×ˢ pkReveal

/-- The users' public keys read from revealed values. -/
noncomputable def pksT {T : Finset (TPosN n)} (w : RevealVals (TValN n) T) :
    Fin n → PublicKey :=
  fun i ↦ (tabRN w i).publicKey

/-- The leaf of a multi-user run: the forged user and forgery, and all users' transcript. -/
abbrev MuRunS (n : ℕ) : Type :=
  (Fin n × Forgery) × MuSignLog n Message (Option Signature)

/-- **A computation's read program, then a pure step**. Irreducible: unfolding a concrete `oa`
evaluates the hashed inputs' encodings, so proofs unfold it explicitly (`readsThenTN_eq`). -/
@[irreducible]
noncomputable def readsThenTN {α β : Type} (oa : OracleComp RomOracles α) (f : α → β) :
    QComp (XSpecSN M n) (QReg.of Unit) (QReg.of Unit) β :=
  (readLiftQ goodQN ((readsProgram M _ oa).map Prod.fst)).bind fun a ↦ QuantumComp₂.pure (f a)

omit [Fintype M] [DecidableEq M] in
theorem readsThenTN_eq {α β : Type} (oa : OracleComp RomOracles α) (f : α → β) :
    readsThenTN (n := n) M oa f =
      (readLiftQ goodQN ((readsProgram M _ oa).map Prod.fst)).bind fun a ↦
        QuantumComp₂.pure (f a) := by
  unfold readsThenTN
  rfl

/-- **The verification of the game** through read ports under the forged user's key, and the
winning condition with distinct `PK.seed`s and every user's transcript valid. -/
noncomputable def verifyTN (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (x : (Fin n → PublicKey) × MuRunS n) : QComp (XSpecSN M n) (QReg.of Unit) (QReg.of Unit) Bool :=
  readsThenTN M (sphincsRom.verify (x.1 x.2.1.1) x.2.1.2) fun b ↦
    pdOK x.1 && sphincsRom.winningCondition (x.2.2.user x.2.1.1) x.2.1.2 &&
      x.2.2.allValid valid && b

/-- **The multi-user SUF-CMA game as runtime 2 runs it, as a template**: reveal all users'
public keys, run the adversary's memo transform from the empty memo against the challenger of
runtime 2 with all users' transcript, and verify. -/
noncomputable def muGameT (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n) :
    QComp (XSpecSN M n) (QReg.of Unit) (QReg.of Unit) Bool :=
  revealThen goodQN pkRevealN fun r₀ ↦
    (challengedTN M upd pols (memoFromS (fun _ _ ↦ none) (withMuSignLog (A (pksT r₀.1))))).bind
      fun run ↦ verifyTN M valid (pksT r₀.1, run)

/-- **The challenge prefix of the game**: reveal the public keys and run the adversary's memo
transform against the challenger of runtime 2; return the public keys and the run. -/
noncomputable def prefixTN (pols : Fin n → DigestPolicy) (A : MuAdversaryS n) :
    QComp (XSpecSN M n) (QReg.of Unit) (QReg.of Unit) ((Fin n → PublicKey) × MuRunS n) :=
  revealThen goodQN pkRevealN fun r₀ ↦
    (challengedTN M upd pols (memoFromS (fun _ _ ↦ none) (withMuSignLog (A (pksT r₀.1))))).bind
      fun run ↦ QuantumComp₂.pure (pksT r₀.1, run)

omit [Fintype M] [DecidableEq M] in
/-- **The game is its challenge prefix, then the verification.** -/
theorem muGameT_eq_prefixTN_bind (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n) :
    muGameT M upd pols valid A = (prefixTN M upd pols A).bind (verifyTN M valid) := by
  simp only [muGameT, prefixTN, revealThen_bind, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]

/-! ## The game reveals before it programs -/

omit [Fintype M] [DecidableEq M] in
theorem disc_mapTN {B C : QReg} {α β : Type} (x : QComp (XSpecSN M n) B C α) (f : α → β)
    (T : Finset (TPosN n)) (hx : Disc x T) : Disc (x.map f) T := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact disc₂_bind _ _ hx fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_progPosN (i : Fin n) (B : QReg) (ps : List Pos) (T : Finset (TPosN n))
    (h : ∀ p ∈ ps, atU i (progNeed p) ⊆ T) : Disc (progPosN M i B ps) T := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact disc_progThen _ trivial _ T (h p List.mem_cons_self)
      (ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

omit [Fintype M] [DecidableEq M] in
theorem disc_forsOpenTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (T : Finset (TPosN n)) :
    Disc (forsOpenTN M i B idx lv) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _ (disc_progPosN M i B _ _ fun _ hp ↦
    (atU_mono i ((progNeed_subset_needUnion hp).trans (Finset.subset_union_left.trans
      Finset.subset_union_left))).trans Finset.subset_union_right) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_selectTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key)
    (T : Finset (TPosN n)) : Disc (selectTN M upd i seed B K) T :=
  disc_revealThen _ _ T fun _ ↦ disc_readLift _ _

omit [Fintype M] [DecidableEq M] in
theorem disc_selOrMemoTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key)
    (o : Option SelS) (T : Finset (TPosN n)) : Disc (selOrMemoTN M upd i seed B K o) T := by
  rcases o with _ | o
  · exact disc_selectTN M upd i seed B K T
  · trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_publishTN (i : Fin n) (B : QReg) (K : Key) (c : EncodingCounter) (x : Encoding)
    (T : Finset (TPosN n)) : Disc (publishTN M i B K c x) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _ (disc_progPosN M i B _ _ fun _ hp ↦
    (atU_mono i ((progNeed_subset_needUnion hp).trans (Finset.subset_union_left.trans
      Finset.subset_union_left))).trans Finset.subset_union_right) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_publishAllTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) (g₀ g₁ g₂ : SelS)
    (T : Finset (TPosN n)) : Disc (publishAllTN M i B idx lv R g₀ g₁ g₂) T := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try trivial
  exact disc₂_bind _ _ (disc_forsOpenTN M i B _ _ T) fun _ T₁ _ ↦
    disc₂_bind _ _ (disc_publishTN M i B _ _ _ T₁) fun _ T₂ _ ↦
      disc₂_bind _ _ (disc_publishTN M i B _ _ _ T₂) fun _ T₃ _ ↦
        disc₂_bind _ _ (disc_publishTN M i B _ _ _ T₃) fun _ _ _ ↦ trivial

theorem atU_digNeed_subset (pol : DigestPolicy) (i : Fin n) (T L : Finset (TPosN n))
    (msg : Message) :
    atU i (digNeed pol (labU L i) msg) ⊆
      T ∪ atU i {seedC, rootC, rndC msg} ∪ atU i (pol.need (labU L i) msg) := by
  intro a ha
  obtain ⟨rfl, hs⟩ := mem_atU_iff.1 ha
  have h := digNeed_subset pol ∅ (labU L a.1) msg hs
  rw [Finset.empty_union, Finset.mem_union] at h
  rcases h with h | h
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (mem_atU_iff.2 ⟨rfl, h⟩))
  · exact Finset.mem_union_right _ (mem_atU_iff.2 ⟨rfl, h⟩)

omit [Fintype M] [DecidableEq M] in
theorem disc_signTN (pols : Fin n → DigestPolicy) (i : Fin n) (B : QReg) (msg : Message)
    (h : KeyMemo) (T : Finset (TPosN n)) : Disc (signTN M upd pols i B msg h) T :=
  disc_revealThen _ _ T fun r₁ ↦ disc_revealThen _ _ _ fun _ ↦
    disc_progThen _ trivial _ _ (atU_digNeed_subset (pols i) i T r₁.2.1 msg)
      (disc₂_bind _ _ (disc_selOrMemoTN M upd i _ B _ _ _) fun _ T₁ _ ↦
        disc₂_bind _ _ (disc_selOrMemoTN M upd i _ B _ _ T₁) fun _ T₂ _ ↦
          disc₂_bind _ _ (disc_selOrMemoTN M upd i _ B _ _ T₂) fun _ T₃ _ ↦
            disc_mapTN M _ _ T₃ (disc_publishAllTN M i B _ _ _ _ _ _ T₃))

omit [Fintype M] [DecidableEq M] in
theorem disc_challengeTN (pols : Fin n → DigestPolicy) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (memoSpecS n) A) (T : Finset (TPosN n)) :
    Disc (challengeTN M upd pols A c) T := by
  rcases c with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact disc_readLift _ _
  · exact disc_readLift _ _
  · exact disc_bind _ _ (disc₂_bind _ _ (disc_act _ _) fun _ T' _ ↦
      disc_signTN M upd pols i _ q.1 q.2 T') fun _ _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix reveals before it programs. -/
theorem disc_prefixTN (pols : Fin n → DigestPolicy) (A : MuAdversaryS n)
    (T : Finset (TPosN n)) : Disc (prefixTN M upd pols A) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _
    (disc_substitute _ (disc_challengeTN M upd pols) _ _) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- A read program followed by a pure step never programs. -/
theorem disc_readsThenTN {α β : Type} (oa : OracleComp RomOracles α) (f : α → β)
    (T : Finset (TPosN n)) : Disc (readsThenTN M oa f) T := by
  rw [readsThenTN_eq]
  exact disc₂_bind _ _ (disc_readLift _ _) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The verification never programs. -/
theorem disc_verifyTN (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (x : (Fin n → PublicKey) × MuRunS n) (T : Finset (TPosN n)) : Disc (verifyTN M valid x) T :=
  disc_readsThenTN M _ _ T

omit [Fintype M] [DecidableEq M] in
/-- **The game reveals before it programs.** -/
theorem disc_muGameT (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (T : Finset (TPosN n)) : Disc (muGameT M upd pols valid A) T := by
  rw [muGameT_eq_prefixTN_bind]
  exact disc₂_bind (prefixTN M upd pols A) (verifyTN M valid) (disc_prefixTN M upd pols A T)
    fun x T' _ ↦ disc_verifyTN M valid x T'

/-! ## The game's reads keep the label -/

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_mapTN {B C : QReg} {α β : Type} (x : QComp (XSpecSN M n) B C α) (f : α → β)
    (hx : KeepsLab x) : KeepsLab (x.map f) := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact keepsLab₂_bind _ _ hx fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_progPosN (i : Fin n) (B : QReg) (ps : List Pos) :
    KeepsLab (progPosN M i B ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact keepsLab_progThen _ trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_forsOpenTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) : KeepsLab (forsOpenTN M i B idx lv) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _ (keepsLab_progPosN M i B _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_selectTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) :
    KeepsLab (selectTN M upd i seed B K) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab_readLift _

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_selOrMemoTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key)
    (o : Option SelS) : KeepsLab (selOrMemoTN M upd i seed B K o) := by
  rcases o with _ | o
  · exact keepsLab_selectTN M upd i seed B K
  · trivial

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_publishTN (i : Fin n) (B : QReg) (K : Key) (c : EncodingCounter)
    (x : Encoding) : KeepsLab (publishTN M i B K c x) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _ (keepsLab_progPosN M i B _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_publishAllTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) (g₀ g₁ g₂ : SelS) :
    KeepsLab (publishAllTN M i B idx lv R g₀ g₁ g₂) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try trivial
  exact keepsLab₂_bind _ _ (keepsLab_forsOpenTN M i B _ _) fun _ ↦
    keepsLab₂_bind _ _ (keepsLab_publishTN M i B _ _ _) fun _ ↦
      keepsLab₂_bind _ _ (keepsLab_publishTN M i B _ _ _) fun _ ↦
        keepsLab₂_bind _ _ (keepsLab_publishTN M i B _ _ _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_signTN (pols : Fin n → DigestPolicy) (i : Fin n) (B : QReg) (msg : Message)
    (h : KeyMemo) : KeepsLab (signTN M upd pols i B msg h) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab_revealThen _ _ fun _ ↦
    keepsLab_progThen _ trivial _ (keepsLab₂_bind _ _ (keepsLab_selOrMemoTN M upd i _ B _ _)
      fun _ ↦ keepsLab₂_bind _ _ (keepsLab_selOrMemoTN M upd i _ B _ _) fun _ ↦
        keepsLab₂_bind _ _ (keepsLab_selOrMemoTN M upd i _ B _ _) fun _ ↦
          keepsLab_mapTN M _ _ (keepsLab_publishAllTN M i B _ _ _ _ _ _))

omit [Fintype M] [DecidableEq M] in
theorem keepsLab_challengeTN (pols : Fin n → DigestPolicy) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (memoSpecS n) A) :
    KeepsLab (challengeTN M upd pols A c) := by
  rcases c with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact keepsLab_readLift _
  · exact keepsLab_readLift _
  · exact keepsLab_bind _ _ (keepsLab₂_bind _ _ (keepsLab_act _) fun _ ↦
      keepsLab_signTN M upd pols i _ q.1 q.2) fun _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix's reads keep the label. -/
theorem keepsLab_prefixTN (pols : Fin n → DigestPolicy) (A : MuAdversaryS n) :
    KeepsLab (prefixTN M upd pols A) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _
    (keepsLab_substitute _ (keepsLab_challengeTN M upd pols) _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- A read program followed by a pure step keeps the label. -/
theorem keepsLab_readsThenTN {α β : Type} (oa : OracleComp RomOracles α) (f : α → β) :
    KeepsLab (readsThenTN (n := n) M oa f) := by
  rw [readsThenTN_eq]
  exact keepsLab₂_bind _ _ (keepsLab_readLift _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The verification's reads keep the label. -/
theorem keepsLab_verifyTN (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (x : (Fin n → PublicKey) × MuRunS n) : KeepsLab (verifyTN M valid x) :=
  keepsLab_readsThenTN M _ _

omit [Fintype M] [DecidableEq M] in
/-- **The game's reads keep the label.** -/
theorem keepsLab_muGameT (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n) :
    KeepsLab (muGameT M upd pols valid A) := by
  rw [muGameT_eq_prefixTN_bind]
  exact keepsLab₂_bind (prefixTN M upd pols A) (verifyTN M valid) (keepsLab_prefixTN M upd pols A)
    fun x ↦ keepsLab_verifyTN M valid x

/-! ## Lazy sampling -/

/-- **The lazy-sampling property of the runtime-2 game.** For every initial state that does not
depend on the hidden values, the realized games satisfy `ViewBy` for runtime 2 with record ports
and the memory label, at every call. -/
theorem viewBy_muGameT (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (m₀ : Finset (TPosN n) × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg PairOut HashDomain (Finset (TPosN n) × M)))
      (QReg.of Unit × QReg.of (HwReg PairOut HashDomain (Finset (TPosN n) × M))) ℂ) (j : ℕ) :
    ViewBy (runtimeR m₀) LocalSig.Interp.instruments (fun r ↦ r.2.2.1)
      (fun θ ↦ realizeT θ (muGameT M upd pols valid A)) (fun _ ↦ ρ) j :=
  viewBy_runtimeR_of_disc _ m₀ (muGameT M upd pols valid A) ∅ (disc_muGameT M upd pols valid A ∅)
    (fun _ ↦ ρ) (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ) j

/-- **`ViewByOn` for the runtime-2 game**: the `hview` hypothesis of the hidden-mass bounds, for
weights vanishing on the program ports. -/
theorem viewByOn_muGameT (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (m₀ : Finset (TPosN n) × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg PairOut HashDomain (Finset (TPosN n) × M)))
      (QReg.of Unit × QReg.of (HwReg PairOut HashDomain (Finset (TPosN n) × M))) ℂ) (j : ℕ) :
    ViewByOn (runtimeR m₀) LocalSig.Interp.instruments (fun i ↦ i.isLeft = true)
      (fun r ↦ r.2.2.1) (fun θ ↦ realizeT θ (muGameT M upd pols valid A)) (fun _ ↦ ρ) j :=
  (viewBy_muGameT M upd pols valid A m₀ ρ j).viewByOn _

end Quantum.Qrom.Sphincs.Multi

end
