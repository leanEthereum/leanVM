module

public import Quantum.Qrom.Xmss.Multi.GameT
public import Quantum.Qrom.Xmss.Multi.Events
public import Quantum.Xmss.Assembly.WinDecomp
public import Quantum.Xmss.Assembly.Costs

@[expose] public section

/-!
# No randomizer search of the multi-user template reads a selected key

With the top-layer memo (`memoFrom`), every key `(i, l, e)` of every user is searched at most once
along a run of the canonical template (memory `SelMemN n`, trial updates `cwUpdN`): a bottom key
once per requested leaf (`NoLeafReuseMu`), a top key only when its selection is not memoized, and
the memo holds the selection of every searched top key. A search stops at its first codeword, the
only trial read that selects. Hence at every trial read of runtime 2 the memory holds no selection
for the read's key (`forallQueries_noSelRead`): the design's `noSelectedRead`, which makes the
re-grind charges of the classical costs vanish.

* `trialUpdN z κ`, `trialReadN z κ`: the trial read of key `κ` at the cell `z` in runtime 2
  (`liftRead (.readH z (cwUpdN i l e z))`); `trialUpdN_inj`: the read names its key.
* `UnselOff K s`: the keys outside `K` hold no selection in `s`.
* `SelP y K Q`: a syntactic invariant of template programs: every read is a trial read of a key
  outside the current set `K`; a trial read whose digest is a codeword adds its key.
* `forallQueries_of_selP`: the realized program of a template satisfying `SelP` presents, at every
  trial read, only registers without a selection of the read's key.
* `selP_prefixTN`, `forallQueries_noSelRead`: the canonical challenge prefix satisfies `SelP`.
-/

open Matrix IPFunctor
open scoped Kronecker

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec runtimeR realizeT revealThen progThen
  readLift readLiftQ RevealVals liftRead lowerRes readMono_liftRead readLift_bind₂ readLens
  querySupportedOn_queryStep_imp)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec cmdCharge withMuSignLog
  isChargeBound_withMuSignLog)

attribute [local irreducible] xmssRom

/- Instance search for the register's memory exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

-- The adversary's commands, as indexed polynomial functors.
set_option quotPrecheck false in
local notation "MuP" n => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (muAdvSpec n SigningRequest (Option Signature))

set_option quotPrecheck false in
local notation "MemoP" n => QuantumComp.toIPFunctor LocalSig.instruments.{0} (memoSpec n)

/-! ## Keys, trial reads, selections -/

/-- A key of a user: the user, the layer and the key index. -/
abbrev UKey (n : ℕ) : Type :=
  Fin n × Layer × KeyIndex

/-- Runtime 2's register with the canonical memory of `n` users. -/
abbrev SRegN (n : ℕ) : Type :=
  HwReg HashOutput HashDomain (Finset (HPosN n) × SelMemN n)

/-- The selection a register's memory holds for a key. -/
def memAt (s : SRegN n) (κ : UKey n) : Option (HashDomain × Digest) :=
  s.2.2.2 κ.1 κ.2.1 κ.2.2

/-- The memory update of a trial read of key `κ` at the cell `z`, beside the label. -/
def trialUpdN (z : HashDomain) (κ : UKey n) :
    Finset (HPosN n) × SelMemN n → Option HashOutput → Finset (HPosN n) × SelMemN n :=
  fun m o ↦ (m.1, cwUpdN κ.1 κ.2.1 κ.2.2 z m.2 o)

/-- **The trial read of key `κ` at the cell `z`** in runtime 2. -/
def trialReadN (z : HashDomain) (κ : UKey n) :
    HwRead HashOutput HashDomain (Finset (HPosN n) × SelMemN n) :=
  .readH z (trialUpdN z κ)

theorem liftRead_cwUpdN (z : HashDomain) (i : Fin n) (l : Layer) (e : KeyIndex) :
    liftRead (S := HPosN n) (.readH z (cwUpdN i l e z)) = trialReadN z (i, l, e) :=
  rfl

/-- A trial whose digest is no codeword keeps the memory. -/
theorem cwUpdN_of_decode_none (i : Fin n) (l : Layer) (e : KeyIndex) (z : HashDomain)
    (m : SelMemN n) {o : Option HashOutput}
    (h : Codeword.decode (truncateHash (o.getD 0)) = none) : cwUpdN i l e z m o = m := by
  cases o with
  | none => exact cwUpdN_none i l e z m
  | some v =>
    have hv : ¬Codeword.Valid (truncateHash v) := by
      unfold Codeword.decode at h
      split_ifs at h with hv'
      exact hv'
    have hm : cwUpd l e z (m i) (some v) = m i := by
      show (if m i l e = none then cwSel (m i) l e z v else m i) = m i
      split_ifs
      · rw [cwSel, ite_eq_right hv]
      · rfl
    rw [cwUpdN, hm, Function.update_eq_self]

/-- A trial read changes the memory at its own key only. -/
theorem cwUpdN_apply_of_ne (i : Fin n) (l : Layer) (e : KeyIndex) (z : HashDomain)
    (m : SelMemN n) (o : Option HashOutput) {j : Fin n} {l' : Layer} {e' : KeyIndex}
    (h : ¬(j = i ∧ l' = l ∧ e' = e)) : cwUpdN i l e z m o j l' e' = m j l' e' := by
  by_cases hj : j = i
  · subst hj
    have h' : ¬(l' = l ∧ e' = e) := fun h'' ↦ h ⟨rfl, h''⟩
    rw [cwUpdN, Function.update_self]
    cases o with
    | none => rfl
    | some v =>
      show (if m j l e = none then cwSel (m j) l e z v else m j) l' e' = m j l' e'
      split_ifs
      · unfold cwSel
        split_ifs
        · exact SelMem.select_of_ne _ _ _ h'
        · rfl
      · rfl
  · rw [cwUpdN, Function.update_of_ne hj]

theorem cwCount_pos : 0 < Quantum.Xmss.cwCount := by
  rw [Quantum.Xmss.cwCount_eq]
  norm_num

/-- Some hash output truncates to a codeword. -/
theorem exists_valid_hashOutput : ∃ v : HashOutput, Codeword.Valid (truncateHash v) := by
  have hpos :
      0 < (Finset.univ.filter fun v : HashOutput ↦ Codeword.Valid (truncateHash v)).card := by
    rw [card_codeword_truncateHash]
    exact Nat.mul_pos cwCount_pos (by positivity)
  obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
  exact ⟨v, (Finset.mem_filter.1 hv).2⟩

/-- **A trial read names its key.** -/
theorem trialUpdN_inj {z : HashDomain} {κ κ' : UKey n} (h : trialUpdN z κ = trialUpdN z κ') :
    κ = κ' := by
  obtain ⟨v, hv⟩ := exists_valid_hashOutput
  by_contra hne
  have hne' : ¬(κ.1 = κ'.1 ∧ κ.2.1 = κ'.2.1 ∧ κ.2.2 = κ'.2.2) := fun ⟨h1, h2, h3⟩ ↦
    hne (Prod.ext h1 (Prod.ext h2 h3))
  have e := congrArg (fun f ↦ (f ((∅ : Finset (HPosN n)), fun _ _ _ ↦ none) (some v)).2 κ.1
    κ.2.1 κ.2.2) h
  simp only [trialUpdN] at e
  rw [cwUpdN_apply_of_ne _ _ _ _ _ _ hne',
    cwUpdN_some_of_none _ _ _ _ (m := fun _ _ _ ↦ none) rfl] at e
  exact (cwSelN_eq_none_iff (m := fun _ _ _ ↦ none) rfl z v).1 e hv

/-- **The keys outside `K` hold no selection.** -/
def UnselOff (K : Set (UKey n)) (s : SRegN n) : Prop :=
  ∀ κ ∉ K, memAt s κ = none

theorem UnselOff.mono {K K' : Set (UKey n)} {s : SRegN n} (h : UnselOff K s) (hK : K ⊆ K') :
    UnselOff K' s :=
  fun κ hκ ↦ h κ fun h' ↦ hκ (hK h')

theorem unselOff_of_mem {K : Set (UKey n)} {s s' : SRegN n} (h : s'.2.2.2 = s.2.2.2)
    (hs : UnselOff K s) : UnselOff K s' := by
  intro κ hκ
  rw [memAt, h]
  exact hs κ hκ

/-! ## Selection conditions at the ports -/

/-- The condition at a port of runtime 2: a trial read sees no selection of its key. -/
def selOk : (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).Port → SRegN n → Prop
  | .inl (.inl (.inr (.readH z u))), s => ∀ κ, u = trialUpdN z κ → memAt s κ = none
  | _, _ => True

/-- **No selected read**: the input of a trial read holds no selection of its key. -/
def NoSelQ : ∀ (i : (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).Port) (E : QReg),
    Matrix (((recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).In i ×
      QReg.of (SRegN n)) × E) (((recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).In i ×
      QReg.of (SRegN n)) × E) ℂ → Prop :=
  fun i E σ ↦ QuerySupportedOn (fun m : ((recHwSpec HashOutput HashDomain (HPosN n)
    (SelMemN n)).In i × QReg.of (SRegN n)) × E ↦ m.1.2) {s | selOk i s} σ

/-- The reads `SelP` allows: trial reads of keys outside `K`. -/
def ReadOkS (K : Set (UKey n)) :
    HwRead HashOutput HashDomain (Finset (HPosN n) × SelMemN n) → Prop
  | .readH z u => ∃ κ, u = trialUpdN z κ ∧ κ ∉ K
  | .readK .. => False
  | .readK' .. => False

/-- The key set after a read: a trial read whose digest is a codeword adds its key. -/
def readPostS (K : Set (UKey n)) :
    (c : HwRead HashOutput HashDomain (Finset (HPosN n) × SelMemN n)) → c.Result → Set (UKey n)
  | .readH z u, r =>
      if Codeword.decode (truncateHash (r.1.getD 0)) = none then K else K ∪ {κ | u = trialUpdN z κ}
  | .readK .., _ => K
  | .readK' .., _ => K

theorem readPostS_mono {K K' : Set (UKey n)} (hK : K ⊆ K')
    (c : HwRead HashOutput HashDomain (Finset (HPosN n) × SelMemN n)) (r : c.Result) :
    readPostS K c r ⊆ readPostS K' c r := by
  cases c with
  | readH z u =>
    simp only [readPostS]
    split_ifs
    · exact hK
    · exact Set.union_subset_union_left _ hK
  | readK => exact hK
  | readK' => exact hK

theorem selOk_of_readOkS {K : Set (UKey n)}
    {c : HwRead HashOutput HashDomain (Finset (HPosN n) × SelMemN n)} (hc : ReadOkS K c)
    {s : SRegN n} (hs : UnselOff K s) : selOk (.inl (.inl (.inr c))) s := by
  cases c with
  | readH z u =>
    obtain ⟨κ₀, rfl, hκ₀⟩ := hc
    intro κ hκ
    rw [← trialUpdN_inj hκ]
    exact hs κ₀ hκ₀
  | readK => exact hc.elim
  | readK' => exact hc.elim

/-! ## The steps of runtime 2 on the invariant -/

section steps

variable (m₀ : Finset (HPosN n) × SelMemN n)

/-- A step of runtime 2 at port `i` carries support on `UnselOff K` to support on
`UnselOff (K' r)` at the result `r`. -/
def StepSel (i : (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).Port)
    (K : Set (UKey n))
    (K' : (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).Result i → Set (UKey n)) :
    Prop :=
  ∀ r σ, QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).In i ×
      (runtimeR m₀).D ↦ m.2) {s | UnselOff K s} σ →
    QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).Out i ×
      (runtimeR m₀).D ↦ m.2) {s | UnselOff (K' r) s} (((runtimeR m₀).step i).branch r σ)

theorem stepSel_sponge (i : SpongePort) (K : Set (UKey n)) :
    StepSel m₀ (.inl (.inl (.inl i))) K fun _ ↦ K := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired HashOutput HashDomain
        (hwEmpty HashOutput HashDomain) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty HashOutput HashDomain) m₀ i
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    have he := snd_eq_of_spongeHardwired_U_ne_zero
      (hwEmpty HashOutput HashDomain) m₀ i q.1 q'.1 q.2 q'.2 hK
    exact unselOff_of_mem (congrArg (fun t ↦ t.2.2) he) hq

/-- A read's register before and after: the memory is the result's, then its update. -/
theorem readKrausH_mem (z : HashDomain)
    (u : Finset (HPosN n) × SelMemN n → Option HashOutput → Finset (HPosN n) × SelMemN n)
    (r : Option HashOutput × (Finset (HPosN n) × SelMemN n)) {a a' : Unit} {s s' : SRegN n}
    (h : hwReadKraus (.readH z u) r (a', s') (a, s) ≠ 0) : s.2.2 = r.2 ∧ s'.2.2 = u r.2 r.1 := by
  simp only [hwReadKraus, readKrausH] at h
  obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
  exact ⟨hp, congrArg Prod.snd hφ⟩

theorem stepSel_read
    (c : {c : HwRead HashOutput HashDomain (Finset (HPosN n) × SelMemN n) //
      ReadMono (Quantum.Xmss.Assembly.memLab HashOutput HashDomain (HPosN n) (SelMemN n)) c})
    {K : Set (UKey n)} (hc : ReadOkS K c.1) :
    StepSel m₀ (.inl (.inl (.inr c.1))) K fun r ↦ readPostS K c.1 r := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain) m₀ c.1
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  obtain ⟨c, hcm⟩ := c
  cases c with
  | readK => exact hc.elim
  | readK' => exact hc.elim
  | readH z u =>
    obtain ⟨κ₀, rfl, hκ₀⟩ := hc
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
      obtain ⟨h1, h2⟩ := readKrausH_mem z _ r hK
      have hq' : UnselOff K q.2 := hq
      have h1' : q.2.2.2.2 = r.2.2 := congrArg Prod.snd h1
      show UnselOff (readPostS K (.readH z (trialUpdN z κ₀)) r) q'.2
      intro κ hκ
      have hm : memAt q'.2 κ = cwUpdN κ₀.1 κ₀.2.1 κ₀.2.2 z r.2.2 r.1 κ.1 κ.2.1 κ.2.2 := by
        show (q'.2.2.2).2 κ.1 κ.2.1 κ.2.2 = _
        rw [h2]
        rfl
      rw [hm]
      by_cases hd : Codeword.decode (truncateHash (r.1.getD 0)) = none
      · have hκ' : κ ∉ K := by
          simp only [readPostS] at hκ
          rwa [ite_eq_left hd] at hκ
        rw [cwUpdN_of_decode_none _ _ _ _ _ hd, ← h1']
        exact hq' κ hκ'
      · have hκ' : κ ∉ K ∪ {κ | trialUpdN z κ₀ = trialUpdN z κ} := by
          simp only [readPostS] at hκ
          rwa [ite_eq_right hd] at hκ
        have hκ1 : κ ∉ K := fun h ↦ hκ' (Or.inl h)
        have hne : ¬(κ.1 = κ₀.1 ∧ κ.2.1 = κ₀.2.1 ∧ κ.2.2 = κ₀.2.2) := fun ⟨e1, e2, e3⟩ ↦
          hκ' (Or.inr (by rw [show κ = κ₀ from Prod.ext e1 (Prod.ext e2 e3)]; exact rfl))
        rw [cwUpdN_apply_of_ne _ _ _ _ _ _ hne, ← h1']
        exact hq' κ hκ1

theorem stepSel_prog (c : HwProg HashOutput HashDomain) (K : Set (UKey n)) :
    StepSel m₀ (.inl (.inr c)) K fun _ ↦ K := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty HashOutput HashDomain) m₀ c
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    unselOff_of_mem (congrArg (fun t ↦ t.2.2) (hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2)
      (u' := q'.1) (s' := q'.2) hK)) hq

theorem stepSel_rec (T : Finset (HPosN n)) (K : Set (UKey n)) :
    StepSel m₀ (Sum.inr T) K fun _ ↦ K := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    unselOff_of_mem (congrArg (fun t ↦ t.2.2) (Quantum.Xmss.Assembly.recKraus_ne_zero
      (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK)) hq

end steps

/-! ## The syntactic invariant of template programs -/

section selP

/-- The condition before a template port. -/
def portPreS (K : Set (UKey n)) : (XSpecN (SelMemN n) n).Port → Prop
  | .inl (.inl (.inr c)) => ReadOkS K c.1
  | _ => True

/-- The condition before a command. -/
def cmdPreS (K : Set (UKey n)) {A : QReg} :
    QuantumComp.Cmd LocalSig.instruments.{0} (XSpecN (SelMemN n) n) A → Prop
  | .prim _ => True
  | .query i _ _ => portPreS K i

/-- The key set after a command and its response. -/
def cmdPostS (K : Set (UKey n)) {A : QReg} :
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (XSpecN (SelMemN n) n) A) → c.Resp →
      Set (UKey n)
  | .prim _, _ => K
  | .query (.inl (.inl (.inl _))) _ _, _ => K
  | .query (.inl (.inl (.inr c))) _ _, b => readPostS K c.1 b.down
  | .query (.inl (.inr _)) _ _, _ => K
  | .query (.inr _) _ _, _ => K

theorem cmdPreS_anti {K K' : Set (UKey n)} (hK : K ⊆ K') {A : QReg}
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (XSpecN (SelMemN n) n) A)
    (h : cmdPreS K' c) : cmdPreS K c := by
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

theorem cmdPostS_mono {K K' : Set (UKey n)} (hK : K ⊆ K') {A : QReg}
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (XSpecN (SelMemN n) n) A) (b : c.Resp) :
    cmdPostS K c b ⊆ cmdPostS K' c b := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · exact hK
  · exact hK
  · exact readPostS_mono hK c.1 _
  · exact hK
  · exact hK

/-- **The selection invariant of a template program**: every read is a trial read of a key
outside the current set, which grows by the key of a trial whose digest is a codeword; at every
leaf the set is within `Q` of the leaf. -/
def SelP {Ω : QReg → Type} :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (XSpecN (SelMemN n) n)) Ω A → Set (UKey n) → ((Σ u, Ω u) → Set (UKey n)) → Prop
  | A, .pure y, K, Q => K ⊆ Q ⟨A, y⟩
  | _, .liftBind c next, K, Q => cmdPreS K c ∧ ∀ b, SelP (next b) (cmdPostS K c b) Q

variable {Ω : QReg → Type}

theorem SelP.anti {A : QReg}
    {y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (XSpecN (SelMemN n) n)) Ω A}
    {K K' : Set (UKey n)} {Q Q' : (Σ u, Ω u) → Set (UKey n)} (h : SelP y K' Q) (hK : K ⊆ K')
    (hQ : ∀ p, Q p ⊆ Q' p) : SelP y K Q' := by
  induction y using IFreeM.inductionOn generalizing K K' with
  | pure _ a => exact hK.trans (h.trans (hQ _))
  | liftBind _ c next ih =>
    exact ⟨cmdPreS_anti hK c h.1, fun b ↦ ih b (h.2 b) (cmdPostS_mono hK c b)⟩

theorem selP_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (XSpecN (SelMemN n) n)) Ω A)
    (K : Set (UKey n)) (Q : (Σ u, Ω u) → Set (UKey n)) : SelP (e ▸ y) K Q ↔ SelP y K Q := by
  subst e
  rfl

theorem selP_bind {Ω' : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (XSpecN (SelMemN n) n)) Ω A)
    (g : ∀ u, Ω u →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (XSpecN (SelMemN n) n)) Ω' u)
    {K : Set (UKey n)} {Q : (Σ u, Ω u) → Set (UKey n)} {R : (Σ u, Ω' u) → Set (UKey n)}
    (hx : SelP x K Q) (hg : ∀ u a, SelP (g u a) (Q ⟨u, a⟩) R) : SelP (x.bind g) K R := by
  induction x using IFreeM.inductionOn generalizing K with
  | pure _ a => exact (hg _ a).anti hx fun _ ↦ subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

/-- `SelP` for programs on a fixed final register. -/
abbrev SelP₂ {A B : QReg} {α : Type} (y : QComp (XSpecN (SelMemN n) n) A B α) (K : Set (UKey n))
    (Q : α → Set (UKey n)) : Prop :=
  SelP y K fun p ↦ Q p.2.2

theorem SelP₂.anti {A B : QReg} {α : Type} {y : QComp (XSpecN (SelMemN n) n) A B α}
    {K K' : Set (UKey n)} {Q Q' : α → Set (UKey n)} (h : SelP₂ y K' Q) (hK : K ⊆ K')
    (hQ : ∀ a, Q a ⊆ Q' a) : SelP₂ y K Q' :=
  SelP.anti h hK fun p ↦ hQ p.2.2

theorem selP₂_bind {A B C : QReg} {α β : Type} {x : QComp (XSpecN (SelMemN n) n) A B α}
    {k : α → QComp (XSpecN (SelMemN n) n) B C β} {K : Set (UKey n)} {Q : α → Set (UKey n)}
    {R : β → Set (UKey n)} (hx : SelP₂ x K Q) (hk : ∀ a, SelP₂ (k a) (Q a) R) :
    SelP₂ (x.bind k) K R := by
  refine selP_bind x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hk a

theorem selP₂_pure {A : QReg} {α : Type} (a : α) {K : Set (UKey n)} {Q : α → Set (UKey n)}
    (h : K ⊆ Q a) : SelP₂ (QuantumComp₂.pure a : QComp (XSpecN (SelMemN n) n) A A α) K Q :=
  h

theorem selP₂_act_bind {A B C : QReg} {α β : Type} (p : SubInstrument A B β)
    {k : β → QComp (XSpecN (SelMemN n) n) B C α} {K : Set (UKey n)} {Q : α → Set (UKey n)}
    (hk : ∀ b, SelP₂ (k b) K Q) : SelP₂ ((QComp.act p).bind k) K Q :=
  ⟨trivial, fun b ↦ hk b.down⟩

theorem selP₂_map {A B : QReg} {α β : Type} {x : QComp (XSpecN (SelMemN n) n) A B α}
    (f : α → β) {K : Set (UKey n)} {Q : α → Set (UKey n)} {R : β → Set (UKey n)}
    (hx : SelP₂ x K Q) (hQ : ∀ a, Q a ⊆ R (f a)) : SelP₂ (x.map f) K R := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact selP₂_bind hx fun a ↦ selP₂_pure (f a) (hQ a)

theorem selP₂_revealThen {B C : QReg} {α : Type} (T : Finset (HPosN n))
    (k : RevealVals (HDN n) T × (Finset (HPosN n) × SelMemN n) →
      QComp (XSpecN (SelMemN n) n) B C α) {K : Set (UKey n)} {Q : α → Set (UKey n)}
    (hk : ∀ r, SelP₂ (k r) K Q) : SelP₂ (revealThen goodQN T k) K Q :=
  ⟨trivial, fun r ↦ selP₂_act_bind _ fun _ ↦ hk r.down⟩

theorem selP₂_progThen {B C : QReg} {α : Type}
    (p : LazyProg HashOutput HashDomain (HPosN n) (HDN n)) (hp : goodQN p)
    {k : QComp (XSpecN (SelMemN n) n) B C α} {K : Set (UKey n)} {Q : α → Set (UKey n)}
    (hk : SelP₂ k K Q) : SelP₂ (progThen p hp k) K Q :=
  ⟨trivial, fun _ ↦ selP₂_act_bind _ fun _ ↦ hk⟩

end selP

/-! ## The invariant at the calls -/

section forallQ

variable (m₀ : Finset (HPosN n) × SelMemN n) {Ω : QReg → Type}

/-- One call of a realized program on the invariant. -/
theorem forallQueries_queryBind_of_stepSel {A : QReg}
    (i : (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).In i × E)
    (k' : (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).Result i →
      QuantumComp LocalSig.instruments.{0} (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n))
        Ω (QReg.of ((recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).Out i × E)))
    {K : Set (UKey n)}
    {K' : (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).Result i → Set (UKey n)}
    (hpre : ∀ s, UnselOff K s → selOk i s) (hstep : StepSel m₀ i K K')
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of ((recHwSpec HashOutput HashDomain (HPosN n)
        (SelMemN n)).Out i × E) × (runtimeR m₀).D ↦ m.2) {s | UnselOff (K' r) s} ρ' →
      (runtimeR m₀).ForallQueries .instruments NoSelQ (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | UnselOff K s} ρ) :
    (runtimeR m₀).ForallQueries .instruments NoSelQ (QuantumComp.queryBind i E ℓ k') ρ := by
  refine ⟨?_, fun r ↦ hk r _ (querySupportedOn_queryStep_imp (runtimeR m₀) i E ℓ r _ _
    (hstep r) hρ)⟩
  have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).imp
    (q' := fun m : ((recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).In i ×
      (runtimeR m₀).D) × E ↦ m.1.2) (S' := {s | UnselOff K s}) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  show QuerySupportedOn _ {s | selOk i s} _
  exact h₁.mono fun s hs ↦ hpre s hs

/-- **The realized program of a template satisfying `SelP`, from registers without selections
outside `K`, sees no selection of the key at any trial read.** -/
theorem forallQueries_of_selP (θ : HPosN n → Digest) {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (XSpecN (SelMemN n) n) Ω A) :
    ∀ K Q, SelP y K Q → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | UnselOff K s} ρ →
      (runtimeR m₀).ForallQueries .instruments NoSelQ (realizeT θ y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro K Q hy ρ hρ b
    exact ih b K Q (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro K Q hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepSel m₀ (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT θ (k r)) (fun _ _ ↦ trivial) (stepSel_sponge m₀ i K)
        (fun r ↦ ih r K Q (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepSel m₀ (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT θ (k r)) (fun s hs ↦ selOk_of_readOkS hy.1 hs)
        (stepSel_read m₀ c hy.1) (fun r ↦ ih r _ Q (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepSel m₀
          (.inl (.inr ((LazyProg.programH T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun _ _ ↦ trivial) (stepSel_prog m₀ _ K) (fun r ↦ ih r K Q (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepSel m₀
          (.inl (.inr ((LazyProg.programK T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun _ _ ↦ trivial) (stepSel_prog m₀ _ K) (fun r ↦ ih r K Q (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepSel m₀
          (.inl (.inr ((LazyProg.programK' T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun _ _ ↦ trivial) (stepSel_prog m₀ _ K) (fun r ↦ ih r K Q (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepSel m₀ (.inr T) E ℓ
        (fun m ↦ realizeT θ (k (restrictTo T θ, m))) (fun _ _ ↦ trivial) (stepSel_rec m₀ T K)
        (fun m ↦ ih (restrictTo T θ, m) K Q (hy.2 (ULift.up (restrictTo T θ, m)))) ρ hρ

end forallQ

/-! ## The template's pieces -/

section pieces

theorem selP₂_queryBind {B C : QReg} {α : Type} (i : (XSpecN (SelMemN n) n).Port)
    (ℓ : B ≃ (XSpecN (SelMemN n) n).In i × B)
    {k : (XSpecN (SelMemN n) n).Result i →
      QComp (XSpecN (SelMemN n) n) (QReg.of ((XSpecN (SelMemN n) n).Out i × B)) C α}
    {K : Set (UKey n)} {Q : α → Set (UKey n)} (hpre : portPreS K i)
    (hk : ∀ r, SelP₂ (k r) (cmdPostS K (.query i B ℓ) (ULift.up r)) Q) :
    SelP₂ (QuantumComp₂.queryBind (L := LocalSig.instruments) i B ℓ k) K Q :=
  ⟨hpre, fun b ↦ hk b.down⟩

/-- A read program's read, lifted to the template. -/
theorem readLiftQ_readCall (c : HwRead HashOutput HashDomain (SelMemN n)) (B : QReg) :
    readLiftQ (goodQN (n := n)) (readCall c B) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := XSpecN (SelMemN n) n)
        (.inl (.inl (.inr ⟨liftRead c, readMono_liftRead c⟩))) B (Equiv.uniqueProd B Unit).symm
        fun r ↦ (QComp.act (A := QReg.of ((XSpecN (SelMemN n) n).Out
          (.inl (.inl (.inr ⟨liftRead c, readMono_liftRead c⟩))) × B)) (B := B)
          (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
            QuantumComp₂.pure (lowerRes c r) := by
  cases c <;> rfl

/-- **A trial read of an unsearched key**: its key joins the set when its digest is a
codeword. -/
theorem selP_trialRead (i : Fin n) (l : Layer) (e : KeyIndex) (z : HashDomain) (B : QReg)
    {K : Set (UKey n)} (hκ : (i, l, e) ∉ K) :
    SelP₂ (readLiftQ (goodQN (n := n)) (readCall (.readH z (cwUpdN i l e z)) B)) K fun r ↦
      if Codeword.decode (truncateHash (r.1.getD 0)) = none then K else insert (i, l, e) K := by
  rw [readLiftQ_readCall]
  refine selP₂_queryBind _ _ ⟨(i, l, e), rfl, hκ⟩ fun b ↦ selP₂_act_bind _ fun _ ↦
    selP₂_pure _ ?_
  show (if Codeword.decode (truncateHash (b.1.getD 0)) = none then K
      else K ∪ {κ | trialUpdN z (i, l, e) = trialUpdN z κ}) ⊆
    (if Codeword.decode (truncateHash (b.1.getD 0)) = none then K else insert (i, l, e) K)
  by_cases hd : Codeword.decode (truncateHash (b.1.getD 0)) = none
  · rw [ite_eq_left hd, ite_eq_left hd]
  · rw [ite_eq_right hd, ite_eq_right hd]
    rintro κ (hκ' | hκ')
    · exact Set.mem_insert_of_mem _ hκ'
    · rw [← trialUpdN_inj hκ']
      exact Set.mem_insert _ _

/-- **A randomizer search of an unsearched key** adds at most its key. -/
theorem selP_grindT (i : Fin n) (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (base : Randomizer) {K : Set (UKey n)} (hκ : (i, l, e) ∉ K) :
    ∀ k trial, SelP₂ (readLiftQ (goodQN (n := n))
      (grindT (SelMemN n) (cwUpdN i) P B l e message base k trial)) K
      fun _ ↦ insert (i, l, e) K
  | 0, _ => selP₂_pure (A := B) _ (Set.subset_insert _ _)
  | k + 1, trial => by
    rw [grindT, readLift_bind₂]
    refine selP₂_bind (selP_trialRead i l e _ B hκ) fun r ↦ ?_
    generalize Codeword.decode (truncateHash (r.1.getD 0)) = d
    cases d with
    | none =>
      rw [ite_eq_left rfl]
      exact selP_grindT i P B l e message base hκ k (trial + 1)
    | some x =>
      rw [ite_eq_right (Option.some_ne_none x)]
      exact selP₂_pure _ subset_rfl

theorem selP_selectTN (i : Fin n) (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (rnd : Pos) {K : Set (UKey n)} (hκ : (i, l, e) ∉ K) :
    SelP₂ (selectTN (SelMemN n) cwUpdN i P B l e message rnd) K fun _ ↦ insert (i, l, e) K :=
  selP₂_revealThen _ _ fun _ ↦ selP_grindT i P B l e message _ hκ _ 0

theorem selP_progPosN (i : Fin n) (B : QReg) (K : Set (UKey n)) :
    ∀ ps : List Pos, SelP₂ (progPosN (SelMemN n) i B ps) K fun _ ↦ K
  | [] => selP₂_pure (A := B) _ subset_rfl
  | _ :: ps => selP₂_progThen _ trivial (selP_progPosN i B K ps)

theorem selP_publishTN (i : Fin n) (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) (K : Set (UKey n)) :
    SelP₂ (publishTN (SelMemN n) i B l e ρ x) K fun _ ↦ K :=
  selP₂_revealThen _ _ fun _ ↦ selP₂_bind (selP_progPosN i B K _) fun _ ↦
    selP₂_pure _ subset_rfl

theorem selP_pubBothN (i : Fin n) (B : QReg) (r : SigningRequest) (gb gt : TopSel)
    (K : Set (UKey n)) :
    SelP₂ (pubBothN (publishTN (SelMemN n) i B) r gb gt) K fun _ ↦ K := by
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · exact selP₂_pure _ subset_rfl
  · exact selP₂_pure _ subset_rfl
  · exact selP₂_pure _ subset_rfl
  · exact selP₂_bind (selP_publishTN i B _ _ _ _ K) fun _ ↦
      selP₂_bind (selP_publishTN i B _ _ _ _ K) fun _ ↦ selP₂_pure _ subset_rfl

/-- The key set after a request's top layer: its top key added unless memoized. -/
def topKeys (K : Set (UKey n)) (κ : UKey n) : Option TopSel → Set (UKey n)
  | some _ => K
  | none => insert κ K

/-- User `i`'s bottom key of a request. -/
def botKey (i : Fin n) (r : SigningRequest) : UKey n :=
  (i, bottomLayer, keyIndexOnLayer r.leafIndex bottomLayer)

/-- User `i`'s top key of a request. -/
def topKeyN (i : Fin n) (r : SigningRequest) : UKey n :=
  (i, topLayer, topKeyOf r)

theorem selP_topTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) {K : Set (UKey n)} (hκ : h = none → topKeyN i r ∉ K) :
    SelP₂ (topTN (SelMemN n) cwUpdN i P B r h) K fun _ ↦ topKeys K (topKeyN i r) h := by
  rcases h with _ | o
  · exact selP₂_revealThen _ _ fun _ ↦ selP_selectTN i P B _ _ _ _ (hκ rfl)
  · exact selP₂_pure _ subset_rfl

/-- **A signing request** adds its bottom key, and its top key unless memoized. -/
theorem selP_signTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) {K : Set (UKey n)} (hb : botKey i r ∉ K)
    (ht : h = none → topKeyN i r ∉ insert (botKey i r) K) :
    SelP₂ (signTN (SelMemN n) cwUpdN i P B r h) K
      fun _ ↦ topKeys (insert (botKey i r) K) (topKeyN i r) h := by
  unfold signTN signWithN
  refine selP₂_bind (selP_selectTN i P B _ _ _ _ hb) fun gb ↦ ?_
  refine selP₂_bind (selP_topTN i P B r h ht) fun gt ↦ ?_
  exact selP₂_map _ (selP_pubBothN i B r gb gt _) fun _ ↦ subset_rfl

/-- **Runtime 1's programs lifted from the QROM read nothing.** -/
theorem selP_readLift_liftH {Y : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} romSpec Y A) (K : Set (UKey n)) :
    SelP (readLift (goodQN (n := n))
      ((liftH x).liftOrdinary (t := hwReadCmdSpec HashOutput HashDomain (SelMemN n)))) K
      fun _ ↦ K := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind _ c next ih =>
    show SelP (IFreeM.mapLens _ (IFreeM.mapLens _ (IFreeM.mapLens _
      (IFreeM.liftBind c next)))) K _
    rw [IFreeM.mapLens_liftBind, IFreeM.mapLens_liftBind, IFreeM.mapLens_liftBind]
    rcases c with o | ⟨_, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _⟩
    · exact ⟨trivial, fun b ↦ ih _⟩

end pieces

/-! ## The memo transform: each key searched at most once -/

section memo

/-- **The searched keys**: the bottom keys of the requested leaves `U`, the memoized top keys. -/
def KofN (U : Finset (Fin n × LeafIndex)) (T : SelMemo n) : Set (UKey n) :=
  {κ | (κ.2.1 = bottomLayer ∧ ∃ ℓ, (κ.1, ℓ) ∈ U ∧ keyIndexOnLayer ℓ bottomLayer = κ.2.2) ∨
    (κ.2.1 = topLayer ∧ T κ.1 κ.2.2 ≠ none)}

theorem bottomLayer_ne_topLayer : bottomLayer ≠ topLayer := by
  decide

theorem keyIndexOnLayer_bottom_inj {ℓ ℓ' : LeafIndex}
    (h : keyIndexOnLayer ℓ bottomLayer = keyIndexOnLayer ℓ' bottomLayer) : ℓ = ℓ' := by
  have h' := congrArg Fin.val h
  simp only [keyIndexOnLayer, bottomLayer, Nat.mul_zero, pow_zero, Nat.div_one] at h'
  exact Fin.ext h'

theorem botKey_not_mem_KofN {U : Finset (Fin n × LeafIndex)} {T : SelMemo n} {i : Fin n}
    {r : SigningRequest} (hU : (i, r.leafIndex) ∉ U) : botKey i r ∉ KofN U T := by
  rintro (⟨-, ℓ, hℓ, he⟩ | ⟨ht, -⟩)
  · exact hU (keyIndexOnLayer_bottom_inj he ▸ hℓ)
  · exact bottomLayer_ne_topLayer ht

theorem topKeyN_not_mem {U : Finset (Fin n × LeafIndex)} {T : SelMemo n} {i : Fin n}
    {r : SigningRequest} (hT : T i (topKeyOf r) = none) :
    topKeyN i r ∉ insert (botKey i r) (KofN U T) := by
  rintro (h | ⟨hb, -⟩ | ⟨-, ht⟩)
  · exact bottomLayer_ne_topLayer (congrArg (fun κ : UKey n ↦ κ.2.1) h).symm
  · exact bottomLayer_ne_topLayer hb.symm
  · exact ht hT

theorem topKeys_subset_KofN (U : Finset (Fin n × LeafIndex)) (T : SelMemo n) (i : Fin n)
    (r : SigningRequest) (s : TopSel) :
    topKeys (insert (botKey i r) (KofN U T)) (topKeyN i r) (T i (topKeyOf r)) ⊆
      KofN (insert (i, r.leafIndex) U) (T.put i (topKeyOf r) s) := by
  have hK : insert (botKey i r) (KofN U T) ⊆
      KofN (insert (i, r.leafIndex) U) (T.put i (topKeyOf r) s) := by
    rintro κ (rfl | (⟨hb, ℓ, hℓ, he⟩ | ⟨ht, hT⟩))
    · exact .inl ⟨rfl, r.leafIndex, Finset.mem_insert_self _ _, rfl⟩
    · exact .inl ⟨hb, ℓ, Finset.mem_insert_of_mem hℓ, he⟩
    · refine .inr ⟨ht, ?_⟩
      by_cases hκ : κ.1 = i ∧ κ.2.2 = topKeyOf r
      · obtain ⟨h1, h2⟩ := hκ
        rw [h1, h2, SelMemo.put_self]
        exact Option.some_ne_none _
      · rw [SelMemo.put_of_ne _ _ hκ]
        exact hT
  cases hT : T i (topKeyOf r) with
  | some o => exact hK
  | none =>
    rintro κ (rfl | hκ)
    · refine .inr ⟨rfl, ?_⟩
      show T.put i (topKeyOf r) s i (topKeyOf r) ≠ none
      rw [SelMemo.put_self]
      exact Option.some_ne_none _
    · exact hK hκ

variable (P : Fin n → PublicParameter)

/-- The challenger at a signing request with the memoized selection `T i (topKeyOf r)`. -/
theorem selP_challengeTN_sign {A : QReg} (i : Fin n) (r : SigningRequest) (h : Option TopSel)
    (E : QReg) (ℓ : A ≃ (memoSpec n).In (.sign i (r, h)) × E) {K : Set (UKey n)}
    (hb : botKey i r ∉ K) (ht : h = none → topKeyN i r ∉ insert (botKey i r) K) :
    SelP (challengeTN (SelMemN n) cwUpdN P A (.query (.sign i (r, h)) E ℓ)) K
      fun _ ↦ topKeys (insert (botKey i r) K) (topKeyN i r) h :=
  selP_bind _ _ (Q := fun _ ↦ topKeys (insert (botKey i r) K) (topKeyN i r) h)
    (selP₂_act_bind _ fun _ ↦ selP_signTN i (P i) _ r h hb ht) fun _ _ ↦ subset_rfl

/-- **The memo transform against the challenger keeps the selection invariant**, from the keys
searched so far (`KofN U T`), when the adversary requests no leaf of `U` again and each other
leaf at most once. -/
theorem selP_memoFrom {C : QReg} {α : Type} {A : QReg}
    (y : IFreeM (MuP n) (QuantumComp₂.Leaf C α) A) :
    ∀ (T : SelMemo n) (U : Finset (Fin n × LeafIndex)),
      (∀ i ℓ, IFreeM.IsChargeBound y (cmdCharge (leafChargeAt i ℓ))
        (if (i, ℓ) ∈ U then 0 else 1)) →
      SelP ((memoFrom T y).substitute (challengeTN (SelMemN n) cwUpdN P)) (KofN U T)
        fun _ ↦ Set.univ := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => intro _ _ _; exact Set.subset_univ _
  | liftBind A c next ih =>
    intro T U hU
    rcases c with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
    · refine selP_bind _ _ (selP_readLift_liftH _ _) fun u ans ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b T U fun j ℓ' ↦ by
        have hc : IFreeM.IsChargeBound (next b) (cmdCharge (leafChargeAt j ℓ'))
            ((if (j, ℓ') ∈ U then 0 else 1) - cmdCharge (leafChargeAt j ℓ') A (.prim o)) :=
          (hU j ℓ').2 b
        exact hc.mono (Nat.sub_le _ _)
    · refine selP_bind _ _ (selP_readLift_liftH _ _) fun u ans ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b T U fun j ℓ' ↦ by
        have hc : IFreeM.IsChargeBound (next b) (cmdCharge (leafChargeAt j ℓ'))
            ((if (j, ℓ') ∈ U then 0 else 1) -
              cmdCharge (leafChargeAt j ℓ') A (.query .hash E ℓ)) := (hU j ℓ').2 b
        exact hc.mono (Nat.sub_le _ _)
    · have hle := (hU i r.leafIndex).1
      have hU' : (i, r.leafIndex) ∉ U := fun h ↦ by
        simp [cmdCharge, leafChargeAt, h] at hle
      refine selP_bind _ _ (selP_challengeTN_sign P i r (T i (topKeyOf r)) E ℓ
        (botKey_not_mem_KofN hU') fun hT ↦ topKeyN_not_mem hT) fun u ans ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      refine SelP.anti (ih _ _ (insert (i, r.leafIndex) U) fun j ℓ' ↦ ?_)
        (topKeys_subset_KofN U T i r (ULift.down b : Option Signature × TopSel).2)
        fun _ ↦ subset_rfl
      have hc : IFreeM.IsChargeBound (next (ULift.up (ULift.down b : Option Signature × TopSel).1))
          (cmdCharge (leafChargeAt j ℓ')) ((if (j, ℓ') ∈ U then 0 else 1) -
            cmdCharge (leafChargeAt j ℓ') A (.query (.sign i r) E ℓ)) :=
        (hU j ℓ').2 (ULift.up (ULift.down b : Option Signature × TopSel).1)
      refine hc.mono ?_
      show (if (j, ℓ') ∈ U then 0 else 1) - (if i = j ∧ r.leafIndex = ℓ' then 1 else 0) ≤
        if (j, ℓ') ∈ insert (i, r.leafIndex) U then 0 else 1
      by_cases hj : i = j ∧ r.leafIndex = ℓ'
      · obtain ⟨rfl, rfl⟩ := hj
        simp [hU']
      · have hne : (j, ℓ') ≠ (i, r.leafIndex) := fun h ↦
          hj ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩
        simp [hj, Finset.mem_insert, hne]

end memo

/-! ## The challenge prefix -/

section prefixSel

/-- **The canonical challenge prefix keeps the selection invariant** from no searched key, for
an adversary that never reuses a leaf of a user. -/
theorem selP_prefixTN (A : MuAdversary n) (hleaf : NoLeafReuseMu A) :
    SelP₂ (prefixTN (SelMemN n) cwUpdN A) ∅ fun _ ↦ Set.univ := by
  refine selP₂_revealThen _ _ fun r₀ ↦ selP₂_bind (Q := fun _ ↦ Set.univ) ?_ fun _ ↦
    selP₂_pure _ subset_rfl
  refine SelP.anti (selP_memoFrom _ _ (fun _ _ ↦ none) ∅ fun i ℓ ↦ ?_) ?_ fun _ ↦ subset_rfl
  · exact (isChargeBound_withMuSignLog (hleaf (pksT r₀.1) i ℓ)).mono (by simp)
  · exact Set.empty_subset _

/-- The initial register holds no selection when the initial memory holds none. -/
theorem querySupportedOn_init_unsel (m₀ : Finset (HPosN n) × SelMemN n)
    (hm₀ : m₀.2 = fun _ _ _ ↦ none) (K : Set (UKey n)) {A : QReg} (σ : Matrix A A ℂ) :
    QuerySupportedOn (fun a : A × QReg.of (SRegN n) ↦ a.2) {s | UnselOff K s}
      (σ ⊗ₖ (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix) := by
  intro a b h
  change (σ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
    hwEmpty HashOutput HashDomain, m₀) : SRegN n)).matrix) a b ≠ 0 at h
  rw [SubState.matrix_basis, kroneckerMap_apply] at h
  have h' := right_ne_zero_of_mul h
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · refine ⟨fun κ _ ↦ ?_, fun κ _ ↦ ?_⟩
    · show a.2.2.2.2 κ.1 κ.2.1 κ.2.2 = none
      rw [← he.1, hm₀]
    · show b.2.2.2.2 κ.1 κ.2.1 κ.2.2 = none
      rw [← he.2, hm₀]
  · exact absurd rfl h'

/-- **No randomizer search re-reads a selected key** (the design's `noSelectedRead`): for an
adversary that never reuses a leaf of a user, at every hidden value `θ` and from an initial
memory without selections, every trial read of the canonical challenge prefix sees no selection
of its key. -/
theorem forallQueries_noSelRead (A : MuAdversary n) (hleaf : NoLeafReuseMu A)
    (θ : HPosN n → Digest) (m₀ : Finset (HPosN n) × SelMemN n)
    (hm₀ : m₀.2 = fun _ _ _ ↦ none) (σ : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) :
    (runtimeR m₀).ForallQueries .instruments NoSelQ
      (realizeT θ (prefixTN (SelMemN n) cwUpdN A))
      (σ ⊗ₖ (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix) :=
  forallQueries_of_selP m₀ θ _ ∅ _ (selP_prefixTN A hleaf) _
    (querySupportedOn_init_unsel m₀ hm₀ ∅ σ)

/-- At a trial read of key `κ`, `NoSelQ` is the absence of a selection of `κ`. -/
theorem noSelQ_trialRead {z : HashDomain} {κ : UKey n} {E : QReg}
    {σ : Matrix (((recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).In
      (.inl (.inl (.inr (trialReadN z κ)))) × QReg.of (SRegN n)) × E)
      (((recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).In
      (.inl (.inl (.inr (trialReadN z κ)))) × QReg.of (SRegN n)) × E) ℂ}
    (h : NoSelQ (.inl (.inl (.inr (trialReadN z κ)))) E σ) :
    QuerySupportedOn (fun m : ((recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)).In
      (.inl (.inl (.inr (trialReadN z κ)))) × QReg.of (SRegN n)) × E ↦ memAt m.1.2 κ) {none} σ :=
  h.imp fun _ hs ↦ hs κ rfl

end prefixSel

end Quantum.Qrom.Xmss.Multi

end
