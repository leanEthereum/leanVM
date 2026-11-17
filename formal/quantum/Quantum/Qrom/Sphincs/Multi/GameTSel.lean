module

public import Quantum.Qrom.Sphincs.Multi.Events
public import Quantum.Qrom.Sphincs.Multi.Template
public import Quantum.Xmss.Assembly.WinDecomp
public import Quantum.Xmss.Assembly.Costs

@[expose] public section

/-!
# No counter search of the multi-user leanSPHINCS template reads a selected key

With the memo (`memoFromS`), every key `(i, K)` of every user is searched at most once along a run
of the canonical template (memory `SelMemN n`, trial updates `cwUpdN`): a request of user `i`
searches the three keys `keyOf l idx` its memo `T i` does not hold (three layers, so three distinct
keys), and the memo afterwards holds all three. A search stops at its first codeword, the only
trial read that selects. Hence at every trial read of runtime 2 the memory holds no selection for
the read's key (`forallQueries_noSelReadS`), with no hypothesis on the adversary.

* `trialUpdSN z κ`, `trialReadSN z κ`: the trial read of key `κ` at the cell `z` in runtime 2
  (`liftRead (.readH z (cwUpdN i K z))`); `trialUpdSN_inj`: the read names its key.
* `UnselOffS K s`: the keys outside `K` hold no selection in `s`.
* `SelPS y K Q`: a syntactic invariant of template programs: every read is a trial read of a key
  outside the current set `K`; a trial read whose digest is a codeword adds its key.
* `forallQueries_of_selPS`: the realized program of a template satisfying `SelPS` presents, at
  every trial read, only registers without a selection of the read's key.
* `selP_signTN`, `selP_memoFromS`, `selP_prefixTN`: the searched keys are within the memoized ones
  (`KofT`); `forallQueries_noSelReadS`, `noSelQS_trialRead`.
-/

open Matrix IPFunctor
open scoped Kronecker
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open Quantum.Sphincs (Key keyOf)
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec runtimeR realizeT revealThen progThen
  readLift readLiftQ RevealVals liftRead lowerRes readMono_liftRead readLift_bind₂ readLens
  querySupportedOn_queryStep_imp)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec)

attribute [local irreducible] sphincsRom

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/- Instance search for the register's memory exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

-- The adversary's commands, as indexed polynomial functors.
set_option quotPrecheck false in
local notation "MuPS" n => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (muAdvSpec n Message (Option Signature))

set_option quotPrecheck false in
local notation "MemoPS" n => QuantumComp.toIPFunctor LocalSig.instruments.{0} (memoSpecS n)

/-! ## Keys, trial reads, selections -/

/-- A key of a user: the user and the WOTS+C key. -/
abbrev UKeyS (n : ℕ) : Type :=
  Fin n × Key

/-- Runtime 2's register with the canonical memory of `n` users. -/
abbrev SRegSN (n : ℕ) : Type :=
  HwReg PairOut HashDomain (Finset (TPosN n) × SelMemN n)

/-- The selection a register's memory holds for a key. -/
def memAtS (s : SRegSN n) (κ : UKeyS n) : Option (HashDomain × Digest) :=
  s.2.2.2 κ.1 κ.2

/-- The memory update of a trial read of key `κ` at the cell `z`, beside the label. -/
def trialUpdSN (z : HashDomain) (κ : UKeyS n) :
    Finset (TPosN n) × SelMemN n → Option PairOut → Finset (TPosN n) × SelMemN n :=
  fun m o ↦ (m.1, cwUpdN κ.1 κ.2 z m.2 o)

/-- **The trial read of key `κ` at the cell `z`** in runtime 2. -/
def trialReadSN (z : HashDomain) (κ : UKeyS n) :
    HwRead PairOut HashDomain (Finset (TPosN n) × SelMemN n) :=
  .readH z (trialUpdSN z κ)

theorem liftRead_cwUpdN (z : HashDomain) (i : Fin n) (K : Key) :
    liftRead (S := TPosN n) (.readH z (cwUpdN i K z)) = trialReadSN z (i, K) :=
  rfl

theorem trialUpdSN_snd (z : HashDomain) (κ : UKeyS n) (m : Finset (TPosN n) × SelMemN n)
    (o : Option PairOut) : (trialUpdSN z κ m o).2 = cwUpdN κ.1 κ.2 z m.2 o :=
  rfl

/-- A trial whose digest is no codeword keeps the memory. -/
theorem cwUpdN_of_decode_none (i : Fin n) (K : Key) (z : HashDomain) (m : SelMemN n)
    {o : Option PairOut} (h : TargetSum.decodeDigest (truncateHash (o.getD 0).1) = none) :
    cwUpdN i K z m o = m := by
  cases o with
  | none => exact cwUpdN_none i K z m
  | some ω =>
    rw [Option.getD_some] at h
    have hv : ¬Quantum.Sphincs.Codeword.Valid (pairDigest ω) :=
      Quantum.Sphincs.Codeword.decode_eq_none_iff.1 h
    have hm : cwUpd K z (m i) (some ω) = m i := by
      show (if m i K = none then cwSel (m i) K z ω else m i) = m i
      split_ifs
      · rw [cwSel, ite_eq_right hv]
      · rfl
    rw [cwUpdN, hm, Function.update_eq_self]

/-- A trial read changes the memory at its own key only. -/
theorem cwUpdN_key_of_ne (i : Fin n) (K : Key) (z : HashDomain) (m : SelMemN n)
    (o : Option PairOut) {j : Fin n} {K' : Key} (h : ¬(j = i ∧ K' = K)) :
    cwUpdN i K z m o j K' = m j K' := by
  by_cases hj : j = i
  · subst hj
    have h' : K' ≠ K := fun e ↦ h ⟨rfl, e⟩
    rw [cwUpdN, Function.update_self]
    cases o with
    | none => rfl
    | some ω =>
      show (if m j K = none then cwSel (m j) K z ω else m j) K' = m j K'
      split_ifs
      · unfold cwSel
        split_ifs
        · exact SelMem.select_of_ne _ _ _ h'
        · rfl
      · rfl
  · rw [cwUpdN, Function.update_of_ne hj]

/-- Some pair's digest is a codeword. -/
theorem exists_valid_pairOut : ∃ ω : PairOut, Quantum.Sphincs.Codeword.Valid (pairDigest ω) := by
  have hc : 0 < Quantum.Sphincs.cwCount := by
    rw [Quantum.Sphincs.cwCount_eq]
    norm_num
  obtain ⟨d, hd⟩ := Finset.card_pos.1 hc
  have hd' : Quantum.Sphincs.Codeword.Valid d := (Finset.mem_filter.1 hd).2
  have hf : 0 < (Finset.univ.filter fun ω : HashOutput × HashOutput ↦ pairDigest ω = d).card := by
    rw [card_fiber_pairDigest]
    positivity
  obtain ⟨ω, hω⟩ := Finset.card_pos.1 hf
  have e : pairDigest ω = d := (Finset.mem_filter.1 hω).2
  subst e
  exact ⟨ω, hd'⟩

/-- **A trial read names its key.** -/
theorem trialUpdSN_inj {z : HashDomain} {κ κ' : UKeyS n} (h : trialUpdSN z κ = trialUpdSN z κ') :
    κ = κ' := by
  obtain ⟨ω, hω⟩ := exists_valid_pairOut
  by_contra hne
  have hne' : ¬(κ.1 = κ'.1 ∧ κ.2 = κ'.2) := fun ⟨h1, h2⟩ ↦ hne (Prod.ext h1 h2)
  have e : (trialUpdSN z κ ((∅ : Finset (TPosN n)), fun _ _ ↦ none) (some ω)).2 κ.1 κ.2 =
      (trialUpdSN z κ' ((∅ : Finset (TPosN n)), fun _ _ ↦ none) (some ω)).2 κ.1 κ.2 := by
    rw [h]
  rw [trialUpdSN_snd, trialUpdSN_snd, cwUpdN_key_of_ne _ _ _ _ _ hne',
    cwUpdN_some_of_none _ _ _ (m := fun _ _ ↦ none) rfl] at e
  exact (cwSelN_eq_none_iff (m := fun _ _ ↦ none) rfl z ω).1 e hω

/-- **The keys outside `K` hold no selection.** -/
def UnselOffS (K : Set (UKeyS n)) (s : SRegSN n) : Prop :=
  ∀ κ ∉ K, memAtS s κ = none

theorem UnselOffS.mono {K K' : Set (UKeyS n)} {s : SRegSN n} (h : UnselOffS K s)
    (hK : K ⊆ K') : UnselOffS K' s :=
  fun κ hκ ↦ h κ fun h' ↦ hκ (hK h')

theorem unselOffS_of_mem {K : Set (UKeyS n)} {s s' : SRegSN n} (h : s'.2.2.2 = s.2.2.2)
    (hs : UnselOffS K s) : UnselOffS K s' := by
  intro κ hκ
  rw [memAtS, h]
  exact hs κ hκ

/-! ## Selection conditions at the ports -/

/-- The condition at a port of runtime 2: a trial read sees no selection of its key. -/
def selOkS : (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).Port → SRegSN n → Prop
  | .inl (.inl (.inr (.readH z u))), s => ∀ κ, u = trialUpdSN z κ → memAtS s κ = none
  | _, _ => True

/-- **No selected read**: the input of a trial read holds no selection of its key. -/
def NoSelQS : ∀ (i : (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).Port) (E : QReg),
    Matrix (((recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).In i ×
      QReg.of (SRegSN n)) × E) (((recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).In i ×
      QReg.of (SRegSN n)) × E) ℂ → Prop :=
  fun i E σ ↦ QuerySupportedOn (fun m : ((recHwSpec PairOut HashDomain (TPosN n)
    (SelMemN n)).In i × QReg.of (SRegSN n)) × E ↦ m.1.2) {s | selOkS i s} σ

/-- The reads `SelPS` allows: trial reads of keys outside `K`. -/
def ReadOkSN (K : Set (UKeyS n)) :
    HwRead PairOut HashDomain (Finset (TPosN n) × SelMemN n) → Prop
  | .readH z u => ∃ κ, u = trialUpdSN z κ ∧ κ ∉ K
  | .readK .. => False
  | .readK' .. => False

/-- The key set after a read: a trial read whose digest is a codeword adds its key. -/
def readPostSN (K : Set (UKeyS n)) :
    (c : HwRead PairOut HashDomain (Finset (TPosN n) × SelMemN n)) → c.Result → Set (UKeyS n)
  | .readH z u, r =>
      if TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) = none then K
      else K ∪ {κ | u = trialUpdSN z κ}
  | .readK .., _ => K
  | .readK' .., _ => K

theorem readPostSN_mono {K K' : Set (UKeyS n)} (hK : K ⊆ K')
    (c : HwRead PairOut HashDomain (Finset (TPosN n) × SelMemN n)) (r : c.Result) :
    readPostSN K c r ⊆ readPostSN K' c r := by
  cases c with
  | readH z u =>
    simp only [readPostSN]
    split_ifs
    · exact hK
    · exact Set.union_subset_union_left _ hK
  | readK => exact hK
  | readK' => exact hK

theorem selOkS_of_readOkSN {K : Set (UKeyS n)}
    {c : HwRead PairOut HashDomain (Finset (TPosN n) × SelMemN n)} (hc : ReadOkSN K c)
    {s : SRegSN n} (hs : UnselOffS K s) : selOkS (.inl (.inl (.inr c))) s := by
  cases c with
  | readH z u =>
    obtain ⟨κ₀, rfl, hκ₀⟩ := hc
    intro κ hκ
    rw [← trialUpdSN_inj hκ]
    exact hs κ₀ hκ₀
  | readK => exact hc.elim
  | readK' => exact hc.elim

/-! ## The steps of runtime 2 on the invariant -/

section steps

variable (m₀ : Finset (TPosN n) × SelMemN n)

/-- A step of runtime 2 at port `i` carries support on `UnselOffS K` to support on
`UnselOffS (K' r)` at the result `r`. -/
def StepSelS (i : (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).Port)
    (K : Set (UKeyS n))
    (K' : (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).Result i → Set (UKeyS n)) :
    Prop :=
  ∀ r σ, QuerySupportedOn (fun m : (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).In i ×
      (runtimeR m₀).D ↦ m.2) {s | UnselOffS K s} σ →
    QuerySupportedOn (fun m : (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).Out i ×
      (runtimeR m₀).D ↦ m.2) {s | UnselOffS (K' r) s} (((runtimeR m₀).step i).branch r σ)

theorem stepSelS_sponge (i : SpongePort) (K : Set (UKeyS n)) :
    StepSelS m₀ (.inl (.inl (.inl i))) K fun _ ↦ K := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired PairOut HashDomain
        (hwEmpty PairOut HashDomain) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty PairOut HashDomain) m₀ i
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    have he := snd_eq_of_spongeHardwired_U_ne_zero
      (hwEmpty PairOut HashDomain) m₀ i q.1 q'.1 q.2 q'.2 hK
    exact unselOffS_of_mem (congrArg (fun t ↦ t.2.2) he) hq

/-- A read's register before and after: the memory is the result's, then its update. -/
theorem readKrausH_memS (z : HashDomain)
    (u : Finset (TPosN n) × SelMemN n → Option PairOut → Finset (TPosN n) × SelMemN n)
    (r : Option PairOut × (Finset (TPosN n) × SelMemN n)) {a a' : Unit} {s s' : SRegSN n}
    (h : hwReadKraus (.readH z u) r (a', s') (a, s) ≠ 0) : s.2.2 = r.2 ∧ s'.2.2 = u r.2 r.1 := by
  simp only [hwReadKraus, readKrausH] at h
  obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
  exact ⟨hp, congrArg Prod.snd hφ⟩

theorem stepSelS_read
    (c : {c : HwRead PairOut HashDomain (Finset (TPosN n) × SelMemN n) //
      ReadMono (Quantum.Xmss.Assembly.memLab PairOut HashDomain (TPosN n) (SelMemN n)) c})
    {K : Set (UKeyS n)} (hc : ReadOkSN K c.1) :
    StepSelS m₀ (.inl (.inl (.inr c.1))) K fun r ↦ readPostSN K c.1 r := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty PairOut HashDomain) m₀ c.1
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  obtain ⟨c, hcm⟩ := c
  cases c with
  | readK => exact hc.elim
  | readK' => exact hc.elim
  | readH z u =>
    obtain ⟨κ₀, rfl, hκ₀⟩ := hc
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
      obtain ⟨h1, h2⟩ := readKrausH_memS z _ r hK
      have hq' : UnselOffS K q.2 := hq
      have h1' : q.2.2.2.2 = r.2.2 := congrArg Prod.snd h1
      show UnselOffS (readPostSN K (.readH z (trialUpdSN z κ₀)) r) q'.2
      intro κ hκ
      have hm : memAtS q'.2 κ = cwUpdN κ₀.1 κ₀.2 z r.2.2 r.1 κ.1 κ.2 := by
        show (q'.2.2.2).2 κ.1 κ.2 = _
        rw [h2, trialUpdSN_snd]
      rw [hm]
      by_cases hd : TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) = none
      · have hκ' : κ ∉ K := by
          simp only [readPostSN] at hκ
          rwa [ite_eq_left hd] at hκ
        rw [cwUpdN_of_decode_none _ _ _ _ hd, ← h1']
        exact hq' κ hκ'
      · have hκ' : κ ∉ K ∪ {κ | trialUpdSN z κ₀ = trialUpdSN z κ} := by
          simp only [readPostSN] at hκ
          rwa [ite_eq_right hd] at hκ
        have hκ1 : κ ∉ K := fun h ↦ hκ' (Or.inl h)
        have hne : ¬(κ.1 = κ₀.1 ∧ κ.2 = κ₀.2) := fun ⟨e1, e2⟩ ↦
          hκ' (Or.inr (by rw [show κ = κ₀ from Prod.ext e1 e2]; exact rfl))
        rw [cwUpdN_key_of_ne _ _ _ _ _ hne, ← h1']
        exact hq' κ hκ1

theorem stepSelS_prog (c : HwProg PairOut HashDomain) (K : Set (UKeyS n)) :
    StepSelS m₀ (.inl (.inr c)) K fun _ ↦ K := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty PairOut HashDomain) m₀ c
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    unselOffS_of_mem (congrArg (fun t ↦ t.2.2) (hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2)
      (u' := q'.1) (s' := q'.2) hK)) hq

theorem stepSelS_rec (T : Finset (TPosN n)) (K : Set (UKeyS n)) :
    StepSelS m₀ (Sum.inr T) K fun _ ↦ K := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    unselOffS_of_mem (congrArg (fun t ↦ t.2.2) (Quantum.Xmss.Assembly.recKraus_ne_zero
      (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK)) hq

end steps

/-! ## The syntactic invariant of template programs -/

section selP

/-- The condition before a template port. -/
def portPreSN (K : Set (UKeyS n)) : (XSpecSN (SelMemN n) n).Port → Prop
  | .inl (.inl (.inr c)) => ReadOkSN K c.1
  | _ => True

/-- The condition before a command. -/
def cmdPreSN (K : Set (UKeyS n)) {A : QReg} :
    QuantumComp.Cmd LocalSig.instruments.{0} (XSpecSN (SelMemN n) n) A → Prop
  | .prim _ => True
  | .query i _ _ => portPreSN K i

/-- The key set after a command and its response. -/
def cmdPostSN (K : Set (UKeyS n)) {A : QReg} :
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (XSpecSN (SelMemN n) n) A) → c.Resp →
      Set (UKeyS n)
  | .prim _, _ => K
  | .query (.inl (.inl (.inl _))) _ _, _ => K
  | .query (.inl (.inl (.inr c))) _ _, b => readPostSN K c.1 b.down
  | .query (.inl (.inr _)) _ _, _ => K
  | .query (.inr _) _ _, _ => K

theorem cmdPreSN_anti {K K' : Set (UKeyS n)} (hK : K ⊆ K') {A : QReg}
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (XSpecSN (SelMemN n) n) A)
    (h : cmdPreSN K' c) : cmdPreSN K c := by
  rcases c with o | ⟨((i | ⟨c, hcm⟩) | p) | T, E, ℓ⟩
  · trivial
  · trivial
  · cases c with
    | readH z u =>
      obtain ⟨κ, hu, hκ⟩ := h
      exact ⟨κ, hu, fun h' ↦ hκ (hK h')⟩
    | readK => exact h.elim
    | readK' => exact h.elim
  · trivial
  · trivial

theorem cmdPostSN_mono {K K' : Set (UKeyS n)} (hK : K ⊆ K') {A : QReg}
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (XSpecSN (SelMemN n) n) A) (b : c.Resp) :
    cmdPostSN K c b ⊆ cmdPostSN K' c b := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · exact hK
  · exact hK
  · exact readPostSN_mono hK c.1 _
  · exact hK
  · exact hK

/-- **The selection invariant of a template program**: every read is a trial read of a key
outside the current set, which grows by the key of a trial whose digest is a codeword; at every
leaf the set is within `Q` of the leaf. -/
def SelPS {Ω : QReg → Type} :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (XSpecSN (SelMemN n) n)) Ω A → Set (UKeyS n) → ((Σ u, Ω u) → Set (UKeyS n)) → Prop
  | A, .pure y, K, Q => K ⊆ Q ⟨A, y⟩
  | _, .liftBind c next, K, Q => cmdPreSN K c ∧ ∀ b, SelPS (next b) (cmdPostSN K c b) Q

variable {Ω : QReg → Type}

theorem SelPS.anti {A : QReg}
    {y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (XSpecSN (SelMemN n) n)) Ω A}
    {K K' : Set (UKeyS n)} {Q Q' : (Σ u, Ω u) → Set (UKeyS n)} (h : SelPS y K' Q)
    (hK : K ⊆ K') (hQ : ∀ p, Q p ⊆ Q' p) : SelPS y K Q' := by
  induction y using IFreeM.inductionOn generalizing K K' with
  | pure _ a => exact hK.trans (h.trans (hQ _))
  | liftBind _ c next ih =>
    exact ⟨cmdPreSN_anti hK c h.1, fun b ↦ ih b (h.2 b) (cmdPostSN_mono hK c b)⟩

theorem selPS_bind {Ω' : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (XSpecSN (SelMemN n) n)) Ω A)
    (g : ∀ u, Ω u →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (XSpecSN (SelMemN n) n)) Ω' u)
    {K : Set (UKeyS n)} {Q : (Σ u, Ω u) → Set (UKeyS n)} {R : (Σ u, Ω' u) → Set (UKeyS n)}
    (hx : SelPS x K Q) (hg : ∀ u a, SelPS (g u a) (Q ⟨u, a⟩) R) : SelPS (x.bind g) K R := by
  induction x using IFreeM.inductionOn generalizing K with
  | pure _ a => exact (hg _ a).anti hx fun _ ↦ subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

/-- `SelPS` for programs on a fixed final register. -/
abbrev SelP₂S {A B : QReg} {α : Type} (y : QComp (XSpecSN (SelMemN n) n) A B α)
    (K : Set (UKeyS n)) (Q : α → Set (UKeyS n)) : Prop :=
  SelPS y K fun p ↦ Q p.2.2

theorem SelP₂S.anti {A B : QReg} {α : Type} {y : QComp (XSpecSN (SelMemN n) n) A B α}
    {K K' : Set (UKeyS n)} {Q Q' : α → Set (UKeyS n)} (h : SelP₂S y K' Q) (hK : K ⊆ K')
    (hQ : ∀ a, Q a ⊆ Q' a) : SelP₂S y K Q' :=
  SelPS.anti h hK fun p ↦ hQ p.2.2

theorem selP₂S_bind {A B C : QReg} {α β : Type} {x : QComp (XSpecSN (SelMemN n) n) A B α}
    {k : α → QComp (XSpecSN (SelMemN n) n) B C β} {K : Set (UKeyS n)} {Q : α → Set (UKeyS n)}
    {R : β → Set (UKeyS n)} (hx : SelP₂S x K Q) (hk : ∀ a, SelP₂S (k a) (Q a) R) :
    SelP₂S (x.bind k) K R := by
  refine selPS_bind x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hk a

theorem selP₂S_pure {A : QReg} {α : Type} (a : α) {K : Set (UKeyS n)} {Q : α → Set (UKeyS n)}
    (h : K ⊆ Q a) : SelP₂S (QuantumComp₂.pure a : QComp (XSpecSN (SelMemN n) n) A A α) K Q :=
  h

theorem selP₂S_act_bind {A B C : QReg} {α β : Type} (p : SubInstrument A B β)
    {k : β → QComp (XSpecSN (SelMemN n) n) B C α} {K : Set (UKeyS n)} {Q : α → Set (UKeyS n)}
    (hk : ∀ b, SelP₂S (k b) K Q) : SelP₂S ((QComp.act p).bind k) K Q :=
  ⟨trivial, fun b ↦ hk b.down⟩

theorem selP₂S_map {A B : QReg} {α β : Type} {x : QComp (XSpecSN (SelMemN n) n) A B α}
    (f : α → β) {K : Set (UKeyS n)} {Q : α → Set (UKeyS n)} {R : β → Set (UKeyS n)}
    (hx : SelP₂S x K Q) (hQ : ∀ a, Q a ⊆ R (f a)) : SelP₂S (x.map f) K R := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact selP₂S_bind hx fun a ↦ selP₂S_pure (f a) (hQ a)

theorem selP₂S_revealThen {B C : QReg} {α : Type} (T : Finset (TPosN n))
    (k : RevealVals (TValN n) T × (Finset (TPosN n) × SelMemN n) →
      QComp (XSpecSN (SelMemN n) n) B C α) {K : Set (UKeyS n)} {Q : α → Set (UKeyS n)}
    (hk : ∀ r, SelP₂S (k r) K Q) : SelP₂S (revealThen goodQN T k) K Q :=
  ⟨trivial, fun r ↦ selP₂S_act_bind _ fun _ ↦ hk r.down⟩

theorem selP₂S_progThen {B C : QReg} {α : Type}
    (p : LazyProg PairOut HashDomain (TPosN n) (TValN n)) (hp : goodQN p)
    {k : QComp (XSpecSN (SelMemN n) n) B C α} {K : Set (UKeyS n)} {Q : α → Set (UKeyS n)}
    (hk : SelP₂S k K Q) : SelP₂S (progThen p hp k) K Q :=
  ⟨trivial, fun _ ↦ selP₂S_act_bind _ fun _ ↦ hk⟩

end selP

/-! ## The invariant at the calls -/

section forallQ

variable (m₀ : Finset (TPosN n) × SelMemN n) {Ω : QReg → Type}

/-- One call of a realized program on the invariant. -/
theorem forallQueries_queryBind_of_stepSelS {A : QReg}
    (i : (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).In i × E)
    (k' : (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).Result i →
      QuantumComp LocalSig.instruments.{0} (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n))
        Ω (QReg.of ((recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).Out i × E)))
    {K : Set (UKeyS n)}
    {K' : (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).Result i → Set (UKeyS n)}
    (hpre : ∀ s, UnselOffS K s → selOkS i s) (hstep : StepSelS m₀ i K K')
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of ((recHwSpec PairOut HashDomain (TPosN n)
        (SelMemN n)).Out i × E) × (runtimeR m₀).D ↦ m.2) {s | UnselOffS (K' r) s} ρ' →
      (runtimeR m₀).ForallQueries .instruments NoSelQS (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | UnselOffS K s} ρ) :
    (runtimeR m₀).ForallQueries .instruments NoSelQS (QuantumComp.queryBind i E ℓ k') ρ := by
  refine ⟨?_, fun r ↦ hk r _ (querySupportedOn_queryStep_imp (runtimeR m₀) i E ℓ r _ _
    (hstep r) hρ)⟩
  have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).imp
    (q' := fun m : ((recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).In i ×
      (runtimeR m₀).D) × E ↦ m.1.2) (S' := {s | UnselOffS K s}) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  show QuerySupportedOn _ {s | selOkS i s} _
  exact h₁.mono fun s hs ↦ hpre s hs

/-- **The realized program of a template satisfying `SelPS`, from registers without selections
outside `K`, sees no selection of the key at any trial read.** -/
theorem forallQueries_of_selPS (θ : TValsN n) {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (XSpecSN (SelMemN n) n) Ω A) :
    ∀ K Q, SelPS y K Q → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | UnselOffS K s} ρ →
      (runtimeR m₀).ForallQueries .instruments NoSelQS (realizeT θ y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro K Q hy ρ hρ b
    exact ih b K Q (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro K Q hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepSelS m₀ (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT θ (k r)) (fun _ _ ↦ trivial) (stepSelS_sponge m₀ i K)
        (fun r ↦ ih r K Q (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepSelS m₀ (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT θ (k r)) (fun s hs ↦ selOkS_of_readOkSN hy.1 hs)
        (stepSelS_read m₀ c hy.1) (fun r ↦ ih r _ Q (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepSelS m₀
          (.inl (.inr ((LazyProg.programH T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun _ _ ↦ trivial) (stepSelS_prog m₀ _ K) (fun r ↦ ih r K Q (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepSelS m₀
          (.inl (.inr ((LazyProg.programK T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun _ _ ↦ trivial) (stepSelS_prog m₀ _ K) (fun r ↦ ih r K Q (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepSelS m₀
          (.inl (.inr ((LazyProg.programK' T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun _ _ ↦ trivial) (stepSelS_prog m₀ _ K) (fun r ↦ ih r K Q (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepSelS m₀ (.inr T) E ℓ
        (fun m ↦ realizeT θ (k (restrictTo T θ, m))) (fun _ _ ↦ trivial) (stepSelS_rec m₀ T K)
        (fun m ↦ ih (restrictTo T θ, m) K Q (hy.2 (ULift.up (restrictTo T θ, m)))) ρ hρ

end forallQ

/-! ## The template's pieces -/

section pieces

theorem selP₂S_queryBind {B C : QReg} {α : Type} (i : (XSpecSN (SelMemN n) n).Port)
    (ℓ : B ≃ (XSpecSN (SelMemN n) n).In i × B)
    {k : (XSpecSN (SelMemN n) n).Result i →
      QComp (XSpecSN (SelMemN n) n) (QReg.of ((XSpecSN (SelMemN n) n).Out i × B)) C α}
    {K : Set (UKeyS n)} {Q : α → Set (UKeyS n)} (hpre : portPreSN K i)
    (hk : ∀ r, SelP₂S (k r) (cmdPostSN K (.query i B ℓ) (ULift.up r)) Q) :
    SelP₂S (QuantumComp₂.queryBind (L := LocalSig.instruments) i B ℓ k) K Q :=
  ⟨hpre, fun b ↦ hk b.down⟩

/-- A read program's read, lifted to the template. -/
theorem readLiftQ_readCallS (c : HwRead PairOut HashDomain (SelMemN n)) (B : QReg) :
    readLiftQ (goodQN (n := n)) (readCall c B) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := XSpecSN (SelMemN n) n)
        (.inl (.inl (.inr ⟨liftRead c, readMono_liftRead c⟩))) B (Equiv.uniqueProd B Unit).symm
        fun r ↦ (QComp.act (A := QReg.of ((XSpecSN (SelMemN n) n).Out
          (.inl (.inl (.inr ⟨liftRead c, readMono_liftRead c⟩))) × B)) (B := B)
          (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
            QuantumComp₂.pure (lowerRes c r) := by
  cases c <;> rfl

/-- **A trial read of an unsearched key**: its key joins the set when its digest is a
codeword. -/
theorem selP_trialReadS (i : Fin n) (K : Key) (z : HashDomain) (B : QReg)
    {Ks : Set (UKeyS n)} (hκ : (i, K) ∉ Ks) :
    SelP₂S (readLiftQ (goodQN (n := n)) (readCall (.readH z (cwUpdN i K z)) B)) Ks fun r ↦
      if TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) = none then Ks
      else insert (i, K) Ks := by
  rw [readLiftQ_readCallS]
  refine selP₂S_queryBind _ _ ⟨(i, K), rfl, hκ⟩ fun b ↦ selP₂S_act_bind _ fun _ ↦
    selP₂S_pure _ ?_
  show (if TargetSum.decodeDigest (truncateHash (b.1.getD 0).1) = none then Ks
      else Ks ∪ {κ | trialUpdSN z (i, K) = trialUpdSN z κ}) ⊆
    (if TargetSum.decodeDigest (truncateHash (b.1.getD 0).1) = none then Ks
      else insert (i, K) Ks)
  by_cases hd : TargetSum.decodeDigest (truncateHash (b.1.getD 0).1) = none
  · rw [ite_eq_left hd, ite_eq_left hd]
  · rw [ite_eq_right hd, ite_eq_right hd]
    rintro κ (hκ' | hκ')
    · exact Set.mem_insert_of_mem _ hκ'
    · rw [← trialUpdSN_inj hκ']
      exact Set.mem_insert _ _

/-- **A counter search of an unsearched key** adds at most its key. -/
theorem selP_grindTS (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) (m : Digest)
    {Ks : Set (UKeyS n)} (hκ : (i, K) ∉ Ks) :
    ∀ k c, SelP₂S (readLiftQ (goodQN (n := n))
      (grindT (SelMemN n) (cwUpdN i) seed B K m k c)) Ks fun _ ↦ insert (i, K) Ks
  | 0, _ => selP₂S_pure (A := B) _ (Set.subset_insert _ _)
  | k + 1, c => by
    rw [grindT, readLift_bind₂]
    refine selP₂S_bind (selP_trialReadS i K _ B hκ) fun r ↦ ?_
    generalize TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) = d
    cases d with
    | none =>
      rw [ite_eq_left rfl]
      exact selP_grindTS i seed B K m hκ k (c + 1)
    | some x =>
      rw [ite_eq_right (Option.some_ne_none x)]
      exact selP₂S_pure _ subset_rfl

theorem selP_selectTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key)
    {Ks : Set (UKeyS n)} (hκ : (i, K) ∉ Ks) :
    SelP₂S (selectTN (SelMemN n) cwUpdN i seed B K) Ks fun _ ↦ insert (i, K) Ks :=
  selP₂S_revealThen _ _ fun _ ↦ selP_grindTS i seed B K _ hκ _ 0

theorem selP_selOrMemoTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key)
    (o : Option SelS) {Ks : Set (UKeyS n)} (hκ : o = none → (i, K) ∉ Ks) :
    SelP₂S (selOrMemoTN (SelMemN n) cwUpdN i seed B K o) Ks fun _ ↦ insert (i, K) Ks := by
  rcases o with _ | o
  · exact selP_selectTN i seed B K (hκ rfl)
  · exact selP₂S_pure _ (Set.subset_insert _ _)

theorem selP_progPosN (i : Fin n) (B : QReg) (K : Set (UKeyS n)) :
    ∀ ps : List Pos, SelP₂S (progPosN (SelMemN n) i B ps) K fun _ ↦ K
  | [] => selP₂S_pure (A := B) _ subset_rfl
  | _ :: ps => selP₂S_progThen _ trivial (selP_progPosN i B K ps)

theorem selP_forsOpenTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (K : Set (UKeyS n)) :
    SelP₂S (forsOpenTN (SelMemN n) i B idx lv) K fun _ ↦ K :=
  selP₂S_revealThen _ _ fun _ ↦ selP₂S_bind (selP_progPosN i B K _) fun _ ↦
    selP₂S_pure _ subset_rfl

theorem selP_publishTN (i : Fin n) (B : QReg) (K : Key) (c : EncodingCounter) (x : Encoding)
    (Ks : Set (UKeyS n)) :
    SelP₂S (publishTN (SelMemN n) i B K c x) Ks fun _ ↦ Ks :=
  selP₂S_revealThen _ _ fun _ ↦ selP₂S_bind (selP_progPosN i B Ks _) fun _ ↦
    selP₂S_pure _ subset_rfl

theorem selP_publishAllTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) (g₀ g₁ g₂ : SelS)
    (K : Set (UKeyS n)) :
    SelP₂S (publishAllTN (SelMemN n) i B idx lv R g₀ g₁ g₂) K fun _ ↦ K := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact selP₂S_pure _ subset_rfl
  exact selP₂S_bind (selP_forsOpenTN i B _ _ K) fun _ ↦
    selP₂S_bind (selP_publishTN i B _ _ _ K) fun _ ↦
      selP₂S_bind (selP_publishTN i B _ _ _ K) fun _ ↦
        selP₂S_bind (selP_publishTN i B _ _ _ K) fun _ ↦ selP₂S_pure _ subset_rfl

/-- The keys of two layers differ. -/
theorem keyOf_ne_of_layer_ne {l l' : Layer} (h : l ≠ l') (idx idx' : Index) :
    keyOf l idx ≠ keyOf l' idx' :=
  fun e ↦ h (congrArg Prod.fst e)

/-- **A signing request of user `i` with memo `h`** searches the three keys of its index that
`h` does not hold, and adds at most these. -/
theorem selP_signTN (pols : Fin n → DigestPolicy) (i : Fin n) (B : QReg) (msg : Message)
    (h : KeyMemo) (K : Set (UKeyS n)) (hK : ∀ K', h K' = none → (i, K') ∉ K) :
    SelP₂S (signTN (SelMemN n) cwUpdN pols i B msg h) K
      fun a ↦ K ∪ {κ | ∃ l : Layer, (i, keyOf l a.2.1) = κ} := by
  unfold signTN
  refine selP₂S_revealThen _ _ fun r₁ ↦ selP₂S_revealThen _ _ fun r₂ ↦
    selP₂S_progThen _ trivial ?_
  generalize digestIndex (digestTN (pols i) i r₁.2.1 msg r₂.1) = idx
  refine selP₂S_bind (selP_selOrMemoTN i _ B _ _ (hK _)) fun g₀ ↦ ?_
  refine selP₂S_bind (selP_selOrMemoTN i _ B _ _ fun h1 ↦ ?_) fun g₁ ↦ ?_
  · rintro (he | hm)
    · exact keyOf_ne_of_layer_ne (by decide) idx idx (congrArg Prod.snd he)
    · exact hK _ h1 hm
  refine selP₂S_bind (selP_selOrMemoTN i _ B _ _ fun h2 ↦ ?_) fun g₂ ↦ ?_
  · rintro (he | he | hm)
    · exact keyOf_ne_of_layer_ne (by decide) idx idx (congrArg Prod.snd he)
    · exact keyOf_ne_of_layer_ne (by decide) idx idx (congrArg Prod.snd he)
    · exact hK _ h2 hm
  refine selP₂S_map _ (selP_publishAllTN i B _ _ _ _ _ _ _) fun _ ↦ ?_
  rintro κ (rfl | rfl | rfl | hκ)
  · exact .inr ⟨2, rfl⟩
  · exact .inr ⟨1, rfl⟩
  · exact .inr ⟨0, rfl⟩
  · exact .inl hκ

/-- **Runtime 1's programs lifted from the QROM read nothing.** -/
theorem selP_readLift_liftHS {Y : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (qromSpec HashDomain PairOut) Y A)
    (K : Set (UKeyS n)) :
    SelPS (readLift (goodQN (n := n))
      ((liftH x).liftOrdinary (t := hwReadCmdSpec PairOut HashDomain (SelMemN n)))) K
      fun _ ↦ K := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind _ c next ih =>
    show SelPS (IFreeM.mapLens _ (IFreeM.mapLens _ (IFreeM.mapLens _
      (IFreeM.liftBind c next)))) K _
    rw [IFreeM.mapLens_liftBind, IFreeM.mapLens_liftBind, IFreeM.mapLens_liftBind]
    rcases c with o | ⟨_, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _⟩
    · exact ⟨trivial, fun b ↦ ih _⟩

end pieces

/-! ## The memo transform: each key searched at most once -/

section memo

/-- **The searched keys**: the keys the memo holds. -/
def KofT (T : SelMemoS n) : Set (UKeyS n) :=
  {κ | T κ.1 κ.2 ≠ none}

/-- After a request of user `i` with memo answer `a`, the memo holds the request's three keys
and every key it held. -/
theorem union_subset_kofT_put (T : SelMemoS n) (i : Fin n) (a : MemoAns) :
    KofT T ∪ {κ | ∃ l : Layer, (i, keyOf l a.1) = κ} ⊆ KofT (T.put i a) := by
  rintro κ (hκ | ⟨l, rfl⟩)
  · show T.put i a κ.1 κ.2 ≠ none
    by_cases hj : κ.1 = i ∧ κ.2 = keyOf κ.2.1 a.1
    · obtain ⟨h1, h2⟩ := hj
      rw [h1, h2, SelMemoS.put_self]
      exact Option.some_ne_none _
    · rw [SelMemoS.put_of_ne T hj]
      exact hκ
  · show T.put i a i (keyOf l a.1) ≠ none
    rw [SelMemoS.put_self]
    exact Option.some_ne_none _

variable (pols : Fin n → DigestPolicy)

/-- The challenger at a signing request of user `i` with memo `q.2`. -/
theorem selP_challengeTN_sign {A : QReg} (i : Fin n) (q : Message × KeyMemo) (E : QReg)
    (ℓ : A ≃ (memoSpecS n).In (.sign i q) × E) {K : Set (UKeyS n)}
    (hK : ∀ K', q.2 K' = none → (i, K') ∉ K) :
    SelPS (challengeTN (SelMemN n) cwUpdN pols A (.query (.sign i q) E ℓ)) K
      fun p ↦ K ∪ {κ | ∃ l : Layer,
        (i, keyOf l (ULift.down p.2.1 : Option Signature × MemoAns).2.1) = κ} := by
  refine selPS_bind _ _ (Q := fun p ↦ K ∪ {κ | ∃ l : Layer, (i, keyOf l p.2.2.2.1) = κ}) ?_
    fun _ _ ↦ subset_rfl
  unfold signAtSN
  exact selP₂S_act_bind _ fun _ ↦ selP_signTN pols i _ q.1 q.2 K hK

/-- **The memo transform against the challenger keeps the selection invariant** from the keys
the memo holds. -/
theorem selP_memoFromS {Y : QReg → Type} {A : QReg} (y : IFreeM (MuPS n) Y A) :
    ∀ T : SelMemoS n,
      SelPS ((memoFromS T y).substitute (challengeTN (SelMemN n) cwUpdN pols)) (KofT T)
        fun _ ↦ Set.univ := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => intro _; exact Set.subset_univ _
  | liftBind A c next ih =>
    intro T
    rcases c with o | ⟨_ | ⟨i, msg⟩, E, ℓ⟩
    · refine selPS_bind _ _ (selP_readLift_liftHS _ _) fun u ans ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b T
    · refine selPS_bind _ _ (selP_readLift_liftHS _ _) fun u ans ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b T
    · refine selPS_bind _ _ (selP_challengeTN_sign pols i (msg, T i) E ℓ
        fun K' hK' hm ↦ hm hK') fun u ans ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      exact SelPS.anti (ih _ _)
        (union_subset_kofT_put T i (ULift.down b : Option Signature × MemoAns).2)
        fun _ ↦ subset_rfl

end memo

/-! ## The challenge prefix -/

section prefixSel

/-- **The canonical challenge prefix keeps the selection invariant** from no searched key. -/
theorem selP_prefixTN (pols : Fin n → DigestPolicy) (A : MuAdversaryS n) :
    SelP₂S (prefixTN (SelMemN n) cwUpdN pols A) ∅ fun _ ↦ Set.univ := by
  refine selP₂S_revealThen _ _ fun r₀ ↦ selP₂S_bind (Q := fun _ ↦ Set.univ) ?_ fun _ ↦
    selP₂S_pure _ subset_rfl
  exact SelPS.anti (selP_memoFromS pols _ fun _ _ ↦ none) (Set.empty_subset _)
    fun _ ↦ subset_rfl

/-- The initial register holds no selection when the initial memory holds none. -/
theorem querySupportedOn_init_unselS (m₀ : Finset (TPosN n) × SelMemN n)
    (hm₀ : m₀.2 = fun _ _ ↦ none) (K : Set (UKeyS n)) {A : QReg} (σ : Matrix A A ℂ) :
    QuerySupportedOn (fun a : A × QReg.of (SRegSN n) ↦ a.2) {s | UnselOffS K s}
      (σ ⊗ₖ (runtimeR (X := PairOut) (Z := HashDomain) m₀).init.matrix) := by
  intro a b h
  change (σ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
    hwEmpty PairOut HashDomain, m₀) : SRegSN n)).matrix) a b ≠ 0 at h
  rw [SubState.matrix_basis, kroneckerMap_apply] at h
  have h' := right_ne_zero_of_mul h
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · refine ⟨fun κ _ ↦ ?_, fun κ _ ↦ ?_⟩
    · show a.2.2.2.2 κ.1 κ.2 = none
      rw [← he.1, hm₀]
    · show b.2.2.2.2 κ.1 κ.2 = none
      rw [← he.2, hm₀]
  · exact absurd rfl h'

/-- **No counter search re-reads a selected key**: at every hidden value `θ` and from an initial
memory without selections, every trial read of the canonical challenge prefix sees no selection
of its key. -/
theorem forallQueries_noSelReadS (pols : Fin n → DigestPolicy) (A : MuAdversaryS n)
    (θ : TValsN n) (m₀ : Finset (TPosN n) × SelMemN n)
    (hm₀ : m₀.2 = fun _ _ ↦ none) (σ : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) :
    (runtimeR m₀).ForallQueries .instruments NoSelQS
      (realizeT θ (prefixTN (SelMemN n) cwUpdN pols A))
      (σ ⊗ₖ (runtimeR (X := PairOut) (Z := HashDomain) m₀).init.matrix) :=
  forallQueries_of_selPS m₀ θ _ ∅ _ (selP_prefixTN pols A) _
    (querySupportedOn_init_unselS m₀ hm₀ ∅ σ)

/-- At a trial read of key `κ`, `NoSelQS` is the absence of a selection of `κ`. -/
theorem noSelQS_trialRead {z : HashDomain} {κ : UKeyS n} {E : QReg}
    {σ : Matrix (((recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).In
      (.inl (.inl (.inr (trialReadSN z κ)))) × QReg.of (SRegSN n)) × E)
      (((recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).In
      (.inl (.inl (.inr (trialReadSN z κ)))) × QReg.of (SRegSN n)) × E) ℂ}
    (h : NoSelQS (.inl (.inl (.inr (trialReadSN z κ)))) E σ) :
    QuerySupportedOn (fun m : ((recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).In
      (.inl (.inl (.inr (trialReadSN z κ)))) × QReg.of (SRegSN n)) × E ↦ memAtS m.1.2 κ)
      {none} σ :=
  h.imp fun _ hs ↦ hs κ rfl

end prefixSel

end Quantum.Qrom.Sphincs.Multi

end
