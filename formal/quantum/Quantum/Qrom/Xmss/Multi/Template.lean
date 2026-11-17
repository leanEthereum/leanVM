module

public import Quantum.Qrom.Xmss.Multi.Runtime1

@[expose] public section

/-!
# leanXMSS's multi-user runtime-2 game in the QROM, as a template program

The `n`-user analog of `Quantum.Qrom.Xmss.Template`. Runtime 2 hardwires a cell of a user's
honest table only once its input and value are public; the users' hidden values enter the game
only through reveal ports.

**Hidden coordinates** (`HPosN n := Fin n × HPos`, a `Digest` each): user `i`'s single-user
coordinates `(i, s)`, the halves of its master seed and of each position's value. `userOf θ i` is
user `i`'s single-user hidden values; `tabOfN θ`, `seedsOf θ` the table of `n` users and the master
seeds, `thetaOfN S0 w` their inverse (`thetaEquivN`). `atU i T` is user `i`'s copy of the
single-user coordinates `T`.

**Ports.** `progTN i p` hardwires the cell of user `i`'s structural position `p` with its value
(`realize_progTN`). A trial read of user `i`'s key `(l, e)` updates the memory with `upd i l e z`.

* `selectTN`, `publishTN`: as `selectT`, `publishT` on user `i`'s coordinates.
* `topTN i P B r h`: the top layer's search of a request (the bottom root revealed first), or the
  memoized selection `h` without any call.
* `signTN`: `signWithN` with these: the bottom layer's search, the top layer's search or memo, both
  layers published when both succeed; the answer and the top selection.
* `muGameT M upd valid A`: reveal all users' public keys, the adversary's memo transform
  (`memoFrom`) against `challengeTN` (hash calls on port `h`, signing requests by `signTN`), the
  verification through read ports under the forged user's key, the winning condition with every
  user's transcript valid. `prefixTN`, `verifyTN`, `muGameT_eq_prefixTN_bind`.
* `disc_muGameT`, `viewBy_muGameT`, `viewByOn_muGameT`: the game reveals before it programs.

Each top key of each user is searched at most once along a run: `memoFrom` memoizes the answer's
top selection at the first request below a top key (`memoFrom`), whether or not that request's
bottom layer succeeded.
-/

open Matrix
open scoped ENNReal

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec runtimeR realizeT revealThen progThen
  readLift readLiftQ RevealVals Disc disc_revealThen disc_progThen disc_readLift disc_act
  disc_bind disc₂_bind disc_substitute viewBy_runtimeR_of_disc revealThen_bind)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec muChallenge withMuSignLog MuSignLog)

variable {n : ℕ}

-- The adversary's commands with the memo, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "MemoP" n => QuantumComp.toIPFunctor LocalSig.instruments.{0} (memoSpec n)

/-! ## Hidden coordinates of `n` users -/

/-- **The hidden coordinates of `n` users**: user `i`'s single-user coordinates. -/
abbrev HPosN (n : ℕ) : Type :=
  Fin n × HPos

/-- A digest per hidden coordinate. -/
abbrev HDN (n : ℕ) : HPosN n → Type :=
  fun _ ↦ Digest

/-- Runtime 2's register with the memory of `n` users has decidable equality (named: the
generic search exceeds the instance size limit). -/
instance instDecidableEqHwRegN (n : ℕ) (M : Type) [DecidableEq M] :
    DecidableEq (HwReg HashOutput HashDomain (Finset (HPosN n) × M)) :=
  HwReg.instDecidableEq

/-- Runtime 2's register with the memory of `n` users is finite. -/
instance instFintypeHwRegN (n : ℕ) (M : Type) [Fintype M] [DecidableEq M] :
    Fintype (HwReg HashOutput HashDomain (Finset (HPosN n) × M)) :=
  HwReg.instFintype

/-- User `i`'s hidden values. -/
def userOf (θ : HPosN n → Digest) (i : Fin n) : HPos → Digest :=
  fun s ↦ θ (i, s)

/-- The table of `n` users of the hidden values. -/
def tabOfN (θ : HPosN n → Digest) : QTableN n :=
  fun a ↦ tabOf (userOf θ a.1) a.2

/-- The users' master seeds of the hidden values. -/
def seedsOf (θ : HPosN n → Digest) : Fin n → MasterSeed :=
  fun i ↦ seedOf (userOf θ i)

/-- The hidden values of the users' master seeds and a table of `n` users. -/
def thetaOfN (S0 : Fin n → MasterSeed) (w : QTableN n) : HPosN n → Digest :=
  fun a ↦ thetaOf (S0 a.1) (w.user a.1) a.2

theorem userOf_thetaOfN (S0 : Fin n → MasterSeed) (w : QTableN n) (i : Fin n) :
    userOf (thetaOfN S0 w) i = thetaOf (S0 i) (w.user i) :=
  rfl

theorem user_tabOfN (θ : HPosN n → Digest) (i : Fin n) :
    (tabOfN θ).user i = tabOf (userOf θ i) :=
  rfl

@[simp]
theorem tabOfN_thetaOfN (S0 : Fin n → MasterSeed) (w : QTableN n) :
    tabOfN (thetaOfN S0 w) = w :=
  funext fun a ↦ congrFun (tabOf_thetaOf (S0 a.1) (w.user a.1)) a.2

@[simp]
theorem seedsOf_thetaOfN (S0 : Fin n → MasterSeed) (w : QTableN n) :
    seedsOf (thetaOfN S0 w) = S0 :=
  funext fun i ↦ seedOf_thetaOf (S0 i) (w.user i)

theorem thetaOfN_seedsOf_tabOfN (θ : HPosN n → Digest) :
    thetaOfN (seedsOf θ) (tabOfN θ) = θ :=
  funext fun a ↦ congrFun (thetaOf_seedOf_tabOf (userOf θ a.1)) a.2

/-- **The hidden values are the users' master seeds and the table of `n` users.** -/
def thetaEquivN : (HPosN n → Digest) ≃ (Fin n → MasterSeed) × QTableN n where
  toFun θ := (seedsOf θ, tabOfN θ)
  invFun p := thetaOfN p.1 p.2
  left_inv θ := thetaOfN_seedsOf_tabOfN θ
  right_inv p := Prod.ext (seedsOf_thetaOfN p.1 p.2) (tabOfN_thetaOfN p.1 p.2)

/-- User `i`'s copy of the single-user coordinates `T`. -/
def atU (i : Fin n) (T : Finset HPos) : Finset (HPosN n) :=
  {i} ×ˢ T

theorem mem_atU {i j : Fin n} {T : Finset HPos} {s : HPos} :
    (j, s) ∈ atU i T ↔ j = i ∧ s ∈ T := by
  simp only [atU, Finset.mem_product, Finset.mem_singleton]

theorem mk_mem_atU (i : Fin n) {T : Finset HPos} {s : HPos} (h : s ∈ T) : (i, s) ∈ atU i T :=
  mem_atU.2 ⟨rfl, h⟩

theorem atU_mono (i : Fin n) {T T' : Finset HPos} (h : T ⊆ T') : atU i T ⊆ atU i T' :=
  Finset.product_subset_product_right h

theorem atU_union (i : Fin n) (T T' : Finset HPos) : atU i (T ∪ T') = atU i T ∪ atU i T' :=
  Finset.product_union

/-! ## Revealed values -/

/-- The values revealed on `T`, extended by `0`. -/
def extendTN {T : Finset (HPosN n)} (w : RevealVals (HDN n) T) : HPosN n → Digest :=
  fun s ↦ if h : s ∈ T then w ⟨s, h⟩ else 0

theorem extendTN_restrictTo {T : Finset (HPosN n)} {s : HPosN n} (h : s ∈ T)
    (θ : HPosN n → Digest) : extendTN (restrictTo T θ) s = θ s := by
  rw [extendTN, dite_eq_left h]
  rfl

/-- User `i`'s table of the values revealed on `T`. -/
def tabRN {T : Finset (HPosN n)} (w : RevealVals (HDN n) T) (i : Fin n) : QTable :=
  tabOf (userOf (extendTN w) i)

/-- User `i`'s values revealed on `T` agree with `θ` on the single-user coordinates of `T`. -/
theorem userOf_extendTN_restrictTo {T : Finset (HPosN n)} {i : Fin n} {s : HPos}
    (h : (i, s) ∈ T) (θ : HPosN n → Digest) :
    userOf (extendTN (restrictTo T θ)) i s = userOf θ i s :=
  extendTN_restrictTo h θ

/-! ## Template program ports -/

/-- Every template program port is allowed. -/
def goodQN : LazyProg HashOutput HashDomain (HPosN n) (HDN n) → Prop :=
  fun _ ↦ True

/-- **The program port of user `i`'s structural position `p`**: hardwire its cell to its value,
both read from user `i`'s coordinates `progNeed p` (the master seed is not read). -/
def progTN (i : Fin n) (p : Pos) : LazyProg HashOutput HashDomain (HPosN n) (HDN n) :=
  .programH (atU i (progNeed p)) fun w ↦ (cellOf 0 p (tabRN w i), tabRN w i p)

theorem need_progTN (i : Fin n) (p : Pos) : (progTN i p).need = atU i (progNeed p) :=
  rfl

/-- **The program port of user `i`'s structural position, realized**: its cell at any master
seed, with its value. -/
theorem realize_progTN {p : Pos} (hp : p.IsStruct) (i : Fin n) (S0 : MasterSeed)
    (θ : HPosN n → Digest) :
    (progTN i p).realize θ =
      .programH (cellOf S0 p (tabOf (userOf θ i))) (tabOf (userOf θ i) p) := by
  have hc : cellOf 0 p (tabRN (restrictTo (atU i (progNeed p)) θ) i) =
      cellOf S0 p (tabOf (userOf θ i)) :=
    cellOf_tabOf_congr hp 0 S0 fun s hs ↦ userOf_extendTN_restrictTo
      (mk_mem_atU i (cellNeed_subset_progNeed p hs)) θ
  have hv : tabRN (restrictTo (atU i (progNeed p)) θ) i p = tabOf (userOf θ i) p :=
    congrArg₂ joinHalves
      (userOf_extendTN_restrictTo (mk_mem_atU i (loC_mem_progNeed p)) θ)
      (userOf_extendTN_restrictTo (mk_mem_atU i (hiC_mem_progNeed p)) θ)
  simp only [progTN, LazyProg.realize, hc, hv]

/-! ## The template game -/

variable (M : Type) [Fintype M] [DecidableEq M]

/-- leanXMSS's multi-user template signature in the QROM, with inner memory `M`. -/
abbrev XSpecN (n : ℕ) : QuantumOracleSpec.{0, 0} :=
  tmplSpec HashOutput HashDomain (HPosN n) (HDN n) M goodQN

variable (upd : Fin n → TrialUpd M)

/-- **User `i`'s randomizer search in runtime 2**: reveal the base's low half, then search
through read ports updating the memory with `upd i`. -/
noncomputable def selectTN (i : Fin n) (P : PublicParameter) (B : QReg) (l : Layer)
    (e : KeyIndex) (message : MsgBytes) (rnd : Pos) : QComp (XSpecN M n) B B TopSel :=
  revealThen goodQN (atU i {loC rnd}) fun r₀ ↦
    readLiftQ goodQN (grindT M (upd i) P B l e message (truncateHash (tabRN r₀.1 i rnd))
      randomizerAttemptLimit 0)

/-- Call user `i`'s program ports of the positions `ps` in order. -/
noncomputable def progPosN (i : Fin n) (B : QReg) : List Pos → QComp (XSpecN M n) B B Unit
  | [] => QuantumComp₂.pure ()
  | p :: ps => progThen (progTN i p) trivial (progPosN i B ps)

/-- **Publishing user `i`'s layer signature**: reveal the layer's coordinates, hardwire the
positions it makes public, and read the signature from the revealed values. -/
noncomputable def publishTN (i : Fin n) (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) : QComp (XSpecN M n) B B LayerSignature :=
  revealThen goodQN (atU i (layerReveal l e x)) fun r ↦
    (progPosN M i B (layerPos l e x)).bind fun _ ↦
      QuantumComp₂.pure (layerSigOf (tabRN r.1 i) l e ρ x)

/-- **User `i`'s top layer's search or its memo**: the memoized selection, or the bottom root
revealed and the search on it. -/
noncomputable def topTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest) :
    Option TopSel → QComp (XSpecN M n) B B TopSel
  | some o => QuantumComp₂.pure o
  | none => revealThen goodQN (atU i (rootReveal r)) fun rr ↦
      selectTN M upd i P B topLayer (keyIndexOnLayer r.leafIndex topLayer)
        (rootBytes ((tabRN rr.1 i).bottomRoot r.leafIndex))
        (.rndTop (keyIndexOnLayer r.leafIndex topLayer) ((tabRN rr.1 i).bottomRoot r.leafIndex))

/-- **User `i`'s signature in runtime 2**, with the memoized top selection `h`: the bottom
layer's search, the top layer's search or memo, the layers published when both succeed. -/
noncomputable def signTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) : QComp (XSpecN M n) B B (Option Signature × TopSel) :=
  signWithN B (selectTN M upd i P B) (publishTN M i B) (topTN M upd i P B r h) r

/-- **The multi-user challenger of runtime 2**, the users' parameters `P`: local operations and
hash calls as `muChallenge` on port `h`, a signing request of user `i` answered by `signTN`. -/
noncomputable def challengeTN (P : Fin n → PublicParameter) :
    IPFunctor.CommandSubstitution (MemoP n)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (XSpecN M n))
  | A, .prim o => readLift goodQN ((liftH (muChallenge xmssRom (noKeys (n := n)) A
      (.prim o))).liftOrdinary (t := hwReadCmdSpec HashOutput HashDomain M))
  | A, .query .hash E ℓ => readLift goodQN ((liftH (muChallenge xmssRom (noKeys (n := n)) A
      (.query .hash E ℓ))).liftOrdinary (t := hwReadCmdSpec HashOutput HashDomain M))
  | _, .query (.sign i q) E ℓ =>
      QuantumComp.bind (signAtN i q E ℓ fun B ↦ signTN M upd i (P i) B q.1 q.2) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's memo transform against the challenger of runtime 2. -/
noncomputable def challengedTN (P : Fin n → PublicParameter) {A B : QReg} {α : Type}
    (x : QComp (memoSpec n) A B α) : QComp (XSpecN M n) A B α :=
  IPFunctor.IFreeM.substitute (challengeTN M upd P) x

/-- The coordinates of all users' public keys: their parameters and roots. -/
def pkRevealN : Finset (HPosN n) :=
  Finset.univ ×ˢ pkReveal

/-- The users' public keys read from revealed values. -/
def pksT {T : Finset (HPosN n)} (w : RevealVals (HDN n) T) : Fin n → PublicKey :=
  fun i ↦ (tabRN w i).publicKey

/-- The leaf of a multi-user run: the forged user and forgery, and all users' transcript. -/
abbrev MuRun (n : ℕ) : Type :=
  (Fin n × Forgery) × MuSignLog n SigningRequest (Option Signature)

/-- **The multi-user SUF-CMA game as runtime 2 runs it, as a template**: reveal all users'
public keys, run the adversary's memo transform from the empty memo against the challenger of
runtime 2 with all users' transcript, verify the forgery through read ports under the forged
user's key, and return the winning condition with every user's transcript valid. -/
noncomputable def muGameT (valid : SignLog → Bool) (A : MuAdversary n) :
    QComp (XSpecN M n) (QReg.of Unit) (QReg.of Unit) Bool :=
  revealThen goodQN pkRevealN fun r₀ ↦
    (challengedTN M upd (fun i ↦ (pksT r₀.1 i).parameter)
      (memoFrom (fun _ _ ↦ none) (withMuSignLog (A (pksT r₀.1))))).bind fun run ↦
      (readLiftQ goodQN ((readsProgram M _ (xmssRom.verify (pksT r₀.1 run.1.1) run.1.2)).map
        Prod.fst)).bind fun verified ↦
        QuantumComp₂.pure (xmssRom.winningCondition (run.2.user run.1.1) run.1.2 &&
          run.2.allValid valid && verified)

/-- **The challenge prefix of the game**: reveal the public keys and run the adversary's memo
transform against the challenger of runtime 2 with all users' transcript; return the public
keys and the run. -/
noncomputable def prefixTN (A : MuAdversary n) :
    QComp (XSpecN M n) (QReg.of Unit) (QReg.of Unit) ((Fin n → PublicKey) × MuRun n) :=
  revealThen goodQN pkRevealN fun r₀ ↦
    (challengedTN M upd (fun i ↦ (pksT r₀.1 i).parameter)
      (memoFrom (fun _ _ ↦ none) (withMuSignLog (A (pksT r₀.1))))).bind fun run ↦
      QuantumComp₂.pure (pksT r₀.1, run)

/-- **The verification of the game** through read ports, and the winning condition. -/
noncomputable def verifyTN (valid : SignLog → Bool) (x : (Fin n → PublicKey) × MuRun n) :
    QComp (XSpecN M n) (QReg.of Unit) (QReg.of Unit) Bool :=
  (readLiftQ goodQN ((readsProgram M _ (xmssRom.verify (x.1 x.2.1.1) x.2.1.2)).map
    Prod.fst)).bind fun verified ↦
    QuantumComp₂.pure (xmssRom.winningCondition (x.2.2.user x.2.1.1) x.2.1.2 &&
      x.2.2.allValid valid && verified)

omit [Fintype M] [DecidableEq M] in
/-- **The game is its challenge prefix, then the verification.** -/
theorem muGameT_eq_prefixTN_bind (valid : SignLog → Bool) (A : MuAdversary n) :
    muGameT M upd valid A = (prefixTN M upd A).bind (verifyTN M valid) := by
  simp only [muGameT, prefixTN, revealThen_bind, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
  rfl

/-! ## The game reveals before it programs -/

attribute [local irreducible] xmssRom

omit [Fintype M] [DecidableEq M] in
theorem disc_progPosN (i : Fin n) (B : QReg) (ps : List Pos) (T : Finset (HPosN n))
    (h : ∀ p ∈ ps, atU i (progNeed p) ⊆ T) : Disc (progPosN M i B ps) T := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact disc_progThen _ trivial _ T (h p List.mem_cons_self)
      (ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

omit [Fintype M] [DecidableEq M] in
theorem disc_selectTN (i : Fin n) (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (rnd : Pos) (T : Finset (HPosN n)) :
    Disc (selectTN M upd i P B l e message rnd) T :=
  disc_revealThen _ _ T fun _ ↦ disc_readLift _ _

omit [Fintype M] [DecidableEq M] in
theorem disc_publishTN (i : Fin n) (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) (T : Finset (HPosN n)) : Disc (publishTN M i B l e ρ x) T := by
  refine disc_revealThen _ _ T fun r ↦
    disc₂_bind _ _ (disc_progPosN M i B _ _ fun p hp ↦ ?_) fun _ _ _ ↦ trivial
  exact (atU_mono i ((progNeed_subset_needUnion hp).trans (Finset.subset_union_left.trans
    Finset.subset_union_left))).trans Finset.subset_union_right

omit [Fintype M] [DecidableEq M] in
theorem disc_topTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) (T : Finset (HPosN n)) : Disc (topTN M upd i P B r h) T := by
  rcases h with _ | o
  · exact disc_revealThen _ _ T fun _ ↦ disc_selectTN M upd i P B _ _ _ _ _
  · trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_pubBothN (i : Fin n) (B : QReg) (r : SigningRequest) (gb gt : TopSel)
    (T : Finset (HPosN n)) : Disc (pubBothN (publishTN M i B) r gb gt) T := by
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · trivial
  · trivial
  · trivial
  · exact disc₂_bind _ _ (disc_publishTN M i B _ _ _ _ T) fun _ T₃ _ ↦
      disc₂_bind _ _ (disc_publishTN M i B _ _ _ _ T₃) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_signTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) (T : Finset (HPosN n)) : Disc (signTN M upd i P B r h) T := by
  unfold signTN signWithN
  refine disc₂_bind _ _ (disc_selectTN M upd i P B _ _ _ _ T) fun gb T' _ ↦ ?_
  refine disc₂_bind _ _ (disc_topTN M upd i P B r h T') fun gt T'' _ ↦ ?_
  rw [QuantumComp₂.map_eq_bind_pure]
  exact disc₂_bind _ _ (disc_pubBothN M i B r gb gt T'') fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_challengeTN (P : Fin n → PublicParameter) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (memoSpec n) A) (T : Finset (HPosN n)) :
    Disc (challengeTN M upd P A c) T := by
  rcases c with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact disc_readLift _ _
  · exact disc_readLift _ _
  · exact disc_bind _ _ (disc₂_bind _ _ (disc_act _ _) fun _ T' _ ↦
      disc_signTN M upd i (P i) _ q.1 q.2 T') fun _ _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix reveals before it programs. -/
theorem disc_prefixTN (A : MuAdversary n) (T : Finset (HPosN n)) : Disc (prefixTN M upd A) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _
    (disc_substitute _ (disc_challengeTN M upd _) _ _) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The verification never programs. -/
theorem disc_verifyTN (valid : SignLog → Bool) (x : (Fin n → PublicKey) × MuRun n)
    (T : Finset (HPosN n)) : Disc (verifyTN M valid x) T := by
  unfold verifyTN
  generalize (readsProgram M _ (xmssRom.verify (x.1 x.2.1.1) x.2.1.2)).map Prod.fst = y
  exact disc₂_bind _ _ (disc_readLift _ T) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The game reveals before it programs.** -/
theorem disc_muGameT (valid : SignLog → Bool) (A : MuAdversary n) (T : Finset (HPosN n)) :
    Disc (muGameT M upd valid A) T := by
  rw [muGameT_eq_prefixTN_bind]
  exact disc₂_bind (prefixTN M upd A) (verifyTN M valid) (disc_prefixTN M upd A T)
    fun x T' _ ↦ disc_verifyTN M valid x T'

/-- **The lazy-sampling property of the runtime-2 game.** For every initial state that does not
depend on the hidden values, the realized games satisfy `ViewBy` for runtime 2 with record ports
and the memory label, at every call. -/
theorem viewBy_muGameT (valid : SignLog → Bool) (A : MuAdversary n)
    (m₀ : Finset (HPosN n) × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (HPosN n) × M)))
      (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (HPosN n) × M))) ℂ) (j : ℕ) :
    ViewBy (runtimeR m₀) LocalSig.Interp.instruments (fun r ↦ r.2.2.1)
      (fun θ ↦ realizeT θ (muGameT M upd valid A)) (fun _ ↦ ρ) j :=
  viewBy_runtimeR_of_disc _ m₀ (muGameT M upd valid A) ∅ (disc_muGameT M upd valid A ∅)
    (fun _ ↦ ρ) (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ) j

/-- **`ViewByOn` for the runtime-2 game**: the `hview` hypothesis of the hidden-mass bounds, for
weights vanishing on the program ports. -/
theorem viewByOn_muGameT (valid : SignLog → Bool) (A : MuAdversary n)
    (m₀ : Finset (HPosN n) × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (HPosN n) × M)))
      (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (HPosN n) × M))) ℂ) (j : ℕ) :
    ViewByOn (runtimeR m₀) LocalSig.Interp.instruments (fun i ↦ i.isLeft = true)
      (fun r ↦ r.2.2.1) (fun θ ↦ realizeT θ (muGameT M upd valid A)) (fun _ ↦ ρ) j :=
  (viewBy_muGameT M upd valid A m₀ ρ j).viewByOn _

end Quantum.Qrom.Xmss.Multi

end
