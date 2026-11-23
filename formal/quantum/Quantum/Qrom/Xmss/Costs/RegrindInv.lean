module

public import Quantum.Qrom.Xmss.Costs.RegrindModes

@[expose] public section

/-!
# Re-grinds: the invariant of the challenge prefix in the decompressed basis

In the decompressed basis the databases have no empty cell, the adversary's hash calls and the
reads keep them, and a program changes only its own cell, never a message-digest cell. So the
view's values at the message-digest cells are fixed along the prefix, and the trial reads return
them.

* **The invariant** (`RgGlob`, `rgInv`): no decompressed `⊥`, no hardwired message-digest cell,
  the recorded trial outcomes are the view's (`RgRd`), and every selection of a key is trial `j`
  of a search of the key's only label (`RgLab`: a revealed bottom base, or the canonical top
  label), read, a codeword in the view, the earlier trials of that search read and no codewords
  (`RgSelW`, `RgNoPre`). Within a search, the key's selection (if any) is by the search's label,
  and the earlier trials of the search were read and are no codewords.
* **The guard** (`rgBotCnt`, `rgGuard`, `forallQueries_rgGuard`): no bottom base of a key is
  revealed before a reveal of one; CostRun's budget with `chgBot_prefixQ` (no leaf reuse).
* **The steps** (`rgInv_read`, `rgInv_prog`, `rgInv_rec`, `rgInv_step`): every allowed call keeps
  the invariant of its mode within the guard. A reveal of a bottom base starts the search of an
  unselected key (the guard); a top key's label is canonical.
* **At the calls of the prefix** (`forallQueries_rgInv`): every call of `prefixQ A θ` is presented
  an operator whose decompressed form is supported on the invariant of a mode allowing it.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid HashSig LeanXmss
open Quantum.Xmss.Assembly (recHwSpec runtimeR runtimeRH decR liftRead liftAns NoBot
  forallQueries_of_charge_budget forallQueries_forall forallQueries_of_modedP_sguard
  conjReg_branch conj_one_kronecker_comp_self querySupportedOn_traceRight)

attribute [local irreducible] xmssRom

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

theorem slotOf_trialCell (P : PublicParameter) (l : Layer) (e : KeyIndex) (msg : MsgBytes)
    (base : Randomizer) (i : ℕ) : slotOf (trialCell P l e msg base i) = some (.msg l e) :=
  slotOf_cell P (show Addressable (.msg l e) from trivial) _

/-! ## The invariant -/

section inv

variable (θ : HPos → Digest)

/-- **The trials before `j`** of a search: read, and no codewords in the view. -/
def RgNoPre (rd : HashDomain → Option HashOutput) (s : RReg SelMem) (l : Layer) (e : KeyIndex)
    (msg : MsgBytes) (base : Randomizer) (j : ℕ) : Prop :=
  ∀ i < j, rd (trialCell (tabOf θ).param l e msg base i) ≠ none ∧
    ¬Codeword.Valid (truncateHash (hvw s (trialCell (tabOf θ).param l e msg base i)))

/-- **A selection by a search**: trial `j` of the search, read, a codeword in the view, the
earlier trials read and no codewords. -/
def RgSelW (rd : HashDomain → Option HashOutput) (s : RReg SelMem) (l : Layer) (e : KeyIndex)
    (msg : MsgBytes) (base : Randomizer) (sel : HashDomain × Digest) : Prop :=
  ∃ j, sel.1 = trialCell (tabOf θ).param l e msg base j ∧ rd sel.1 ≠ none ∧
    sel.2 = truncateHash (hvw s sel.1) ∧ Codeword.Valid sel.2 ∧ RgNoPre θ rd s l e msg base j

/-- **The label of a search**: of a bottom key, with a revealed base; of a top key, canonical. -/
def RgLab (T : Finset HPos) (l : Layer) (e : KeyIndex) (msg : MsgBytes) (base : Randomizer) :
    Prop :=
  (l = bottomLayer → BotRev e T) ∧ (l = topLayer → msg = rootBytes (rgRoot θ e) ∧
    base = truncateHash (tabOf θ (.rndTop e (rgRoot θ e))))

/-- The recorded trial outcomes are the view's values at message-digest cells. -/
def RgRd (rd : HashDomain → Option HashOutput) (s : RReg SelMem) : Prop :=
  ∀ z y, rd z = some y → (∃ l e, slotOf z = some (.msg l e)) ∧ hvw s z = y

/-- No message-digest cell is hardwired. -/
def RgMsgHw (s : RReg SelMem) : Prop :=
  ∀ x l e, slotOf x = some (.msg l e) → s.2.1.1 x = none

/-- **The invariant between searches.** -/
def RgGlob (rd : HashDomain → Option HashOutput) (s : RReg SelMem) : Prop :=
  NoBot s ∧ RgMsgHw s ∧ RgRd rd s ∧ ∀ l e sel, s.2.2.2 l e = some sel →
    ∃ msg base, RgLab θ s.2.2.1 l e msg base ∧ RgSelW θ rd s l e msg base sel

/-- **The invariant of a mode.** -/
def rgInv : RgMode → Set (RReg SelMem)
  | ⟨.free, rd⟩ => {s | RgGlob θ rd s}
  | ⟨.srch l e msg base j, rd⟩ => {s | RgGlob θ rd s ∧ RgLab θ s.2.2.1 l e msg base ∧
      (∀ sel, s.2.2.2 l e = some sel → RgSelW θ rd s l e msg base sel) ∧
      RgNoPre θ rd s l e msg base j}

variable {θ}

theorem rgGlob_of_inv {μ : RgMode} {s : RReg SelMem} (h : s ∈ rgInv θ μ) : RgGlob θ μ.2 s := by
  obtain ⟨σ, rd⟩ := μ
  cases σ with
  | free => exact h
  | srch => exact h.1

/-- More recorded trial reads. -/
def RdLe (rd rd' : HashDomain → Option HashOutput) : Prop :=
  ∀ z, rd z ≠ none → rd' z ≠ none

theorem rgNoPre_congr {rd rd' : HashDomain → Option HashOutput} {s s' : RReg SelMem}
    {l : Layer} {e : KeyIndex} {msg : MsgBytes} {base : Randomizer} {j : ℕ} (hrd : RdLe rd rd')
    (hH : ∀ i, hvw s' (trialCell (tabOf θ).param l e msg base i) =
      hvw s (trialCell (tabOf θ).param l e msg base i))
    (h : RgNoPre θ rd s l e msg base j) : RgNoPre θ rd' s' l e msg base j := fun i hi ↦ by
  obtain ⟨h1, h2⟩ := h i hi
  exact ⟨hrd _ h1, by rw [hH]; exact h2⟩

theorem rgSelW_congr {rd rd' : HashDomain → Option HashOutput} {s s' : RReg SelMem}
    {l : Layer} {e : KeyIndex} {msg : MsgBytes} {base : Randomizer} {sel : HashDomain × Digest}
    (hrd : RdLe rd rd')
    (hH : ∀ i, hvw s' (trialCell (tabOf θ).param l e msg base i) =
      hvw s (trialCell (tabOf θ).param l e msg base i))
    (h : RgSelW θ rd s l e msg base sel) : RgSelW θ rd' s' l e msg base sel := by
  obtain ⟨j, h1, h2, h3, h4, h5⟩ := h
  refine ⟨j, h1, hrd _ h2, ?_, h4, rgNoPre_congr hrd hH h5⟩
  rw [h1] at h3 ⊢
  rw [hH]
  exact h3

theorem rgLab_mono {T T' : Finset HPos} (hT : T ⊆ T') {l : Layer} {e : KeyIndex}
    {msg : MsgBytes} {base : Randomizer} (h : RgLab θ T l e msg base) :
    RgLab θ T' l e msg base :=
  ⟨fun hl ↦ let ⟨m, hm⟩ := h.1 hl; ⟨m, hT hm⟩, h.2⟩

theorem rgGlob_congr {rd rd' : HashDomain → Option HashOutput} {s s' : RReg SelMem}
    (hrd : RdLe rd rd') (hnb : NoBot s') (hmsg : RgMsgHw s') (hRd : RgRd rd' s')
    (hH : ∀ x l e, slotOf x = some (.msg l e) → hvw s' x = hvw s x)
    (hm : s'.2.2.2 = s.2.2.2) (hT : s.2.2.1 ⊆ s'.2.2.1) (h : RgGlob θ rd s) :
    RgGlob θ rd' s' := by
  refine ⟨hnb, hmsg, hRd, fun l e sel hsel ↦ ?_⟩
  rw [hm] at hsel
  obtain ⟨msg, base, hl, hw⟩ := h.2.2.2 l e sel hsel
  exact ⟨msg, base, rgLab_mono hT hl,
    rgSelW_congr hrd (fun i ↦ hH _ _ _ (slotOf_trialCell _ l e msg base i)) hw⟩

/-- **A trial read keeps the invariant**: the view's value at the trial cell is recorded and the
selection updated; the search stops at a codeword. -/
theorem rgInv_read {l : Layer} {e : KeyIndex} {msg : MsgBytes} {base : Randomizer} {j : ℕ}
    {rd : HashDomain → Option HashOutput} {z : HashDomain}
    (hz : z = trialCell (tabOf θ).param l e msg base j) {s s' : RReg SelMem}
    (hs : s ∈ rgInv θ (.srch l e msg base j, rd)) (h1 : s'.1 = s.1) (h2 : s'.2.1 = s.2.1)
    (h3 : s'.2.2.1 = s.2.2.1) (h4 : s'.2.2.2 = cwUpd l e z s.2.2.2 (some (hvw s z))) :
    s' ∈ rgInv θ ((if Codeword.Valid (truncateHash (hvw s z)) then .free
      else .srch l e msg base (j + 1)), Function.update rd z (some (hvw s z))) := by
  obtain ⟨⟨hnb, hmsg, hrd, hsel⟩, hlab, hcur, hpre⟩ := hs
  have hH : hvw s' = hvw s := hvw_eq h1 h2
  have hle : RdLe rd (Function.update rd z (some (hvw s z))) := fun w hw ↦ by
    by_cases hwz : w = z
    · rw [hwz, Function.update_self]
      exact Option.some_ne_none _
    · rwa [Function.update_of_ne hwz]
  have hHi : ∀ i, hvw s' (trialCell (tabOf θ).param l e msg base i) =
      hvw s (trialCell (tabOf θ).param l e msg base i) := fun i ↦ by rw [hH]
  have hRd : RgRd (Function.update rd z (some (hvw s z))) s' := by
    intro w y' hw
    by_cases hwz : w = z
    · rw [hwz, Function.update_self] at hw
      cases hw
      rw [hwz, hz]
      exact ⟨⟨l, e, slotOf_trialCell _ l e msg base j⟩, by rw [hH]⟩
    · rw [Function.update_of_ne hwz] at hw
      obtain ⟨hw1, hw2⟩ := hrd w y' hw
      exact ⟨hw1, by rw [hH]; exact hw2⟩
  have hnb' : NoBot s' := noBot_of_eq h1 hnb
  have hmsg' : RgMsgHw s' := fun x l' e' hx ↦ by rw [h2]; exact hmsg x l' e' hx
  have hT : s.2.2.1 ⊆ s'.2.2.1 := by rw [h3]
  have hglob : s'.2.2.2 = s.2.2.2 → RgGlob θ (Function.update rd z (some (hvw s z))) s' :=
    fun hm ↦ rgGlob_congr hle hnb' hmsg' hRd (fun x _ _ _ ↦ by rw [hH]) hm hT
      ⟨hnb, hmsg, hrd, hsel⟩
  by_cases hv : Codeword.Valid (truncateHash (hvw s z))
  · rw [ite_eq_left hv]
    by_cases hm : s.2.2.2 l e = none
    · have hm' : s'.2.2.2 = s.2.2.2.select l e z (truncateHash (hvw s z)) := by
        rw [h4, cwUpd_some_of_none l e z hm, cwSel, ite_eq_left hv]
      refine ⟨hnb', hmsg', hRd, fun l' e' sel hs' ↦ ?_⟩
      rw [hm'] at hs'
      by_cases hk : l' = l ∧ e' = e
      · obtain ⟨rfl, rfl⟩ := hk
        rw [SelMem.select_self] at hs'
        cases hs'
        refine ⟨msg, base, rgLab_mono hT hlab, j, hz, ?_, by rw [hH], hv,
          rgNoPre_congr hle hHi hpre⟩
        show Function.update rd z (some (hvw s z)) z ≠ none
        rw [Function.update_self]
        exact Option.some_ne_none _
      · rw [SelMem.select_of_ne _ _ _ hk] at hs'
        obtain ⟨msg', base', hl', hw'⟩ := hsel l' e' sel hs'
        exact ⟨msg', base', rgLab_mono hT hl', rgSelW_congr hle (fun i ↦ by rw [hH]) hw'⟩
    · exact hglob (by rw [h4]; exact ite_eq_right hm)
  · rw [ite_eq_right hv]
    have hm' : s'.2.2.2 = s.2.2.2 := by
      rw [h4]
      show (if s.2.2.2 l e = none then cwSel s.2.2.2 l e z (hvw s z) else s.2.2.2) = s.2.2.2
      split_ifs
      · exact ite_eq_right hv
      · rfl
    refine ⟨hglob hm', rgLab_mono hT hlab, fun sel hs' ↦ ?_, fun i hi ↦ ?_⟩
    · rw [hm'] at hs'
      exact rgSelW_congr hle hHi (hcur sel hs')
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact rgNoPre_congr hle hHi hpre i hi
      · rw [hi, ← hz, hH]
        refine ⟨?_, hv⟩
        rw [Function.update_self]
        exact Option.some_ne_none _

/-- **A program off the message slots keeps the invariant between searches.** -/
theorem rgInv_prog {μ : RgMode} {z : HashDomain} {a : HashOutput}
    (hz : ∀ l e, slotOf z ≠ some (.msg l e)) {s s' : RReg SelMem} (hs : s ∈ rgInv θ μ)
    (hR : ProgRelH z a s s') : s' ∈ rgInv θ (.free, μ.2) := by
  obtain ⟨hR1, hR2, hR3⟩ := hR
  have hg := rgGlob_of_inv hs
  have hW : ∀ x, x ≠ z → s'.2.1.1 x = s.2.1.1 x := fun x hx ↦ by
    rw [show s'.2.1 = progUpdate (.programH z a) s.2.1 from congrArg Prod.fst hR1]
    exact Function.update_of_ne hx _ _
  have hne : ∀ x l e, slotOf x = some (.msg l e) → x ≠ z := fun x l e hx hxz ↦
    hz l e (hxz ▸ hx)
  have hH : ∀ x l e, slotOf x = some (.msg l e) → hvw s' x = hvw s x := fun x l e hx ↦ by
    show ((s'.2.1.1 x).or (s'.1.1 x)).getD 0 = ((s.2.1.1 x).or (s.1.1 x)).getD 0
    rw [hW x (hne x l e hx), hR3 x (hne x l e hx)]
  have hm : s'.2.2 = s.2.2 := by rw [hR1]
  refine rgGlob_congr (fun _ h ↦ h) (hR2 hg.1)
    (fun x l e hx ↦ by rw [hW x (hne x l e hx)]; exact hg.2.1 x l e hx) (fun w y hw ↦ ?_) hH
    (by rw [hm]) (by rw [hm]) hg
  obtain ⟨⟨l, e, hw1⟩, hw2⟩ := hg.2.2.1 w y hw
  exact ⟨⟨l, e, hw1⟩, by rw [hH w l e hw1]; exact hw2⟩

end inv

/-! ## The guard -/

section guard

/-- The counter: a bottom base of key `e` is revealed. -/
noncomputable def rgBotCnt (e : KeyIndex) (s : RReg SelMem) : ℕ :=
  @ite _ (BotRev e s.2.2.1) (Classical.propDecidable _) 1 0

/-- **The guard**: no bottom base of a key is revealed before a reveal of one. -/
def rgGuard (i : (RSpec SelMem).Port) : Set (RReg SelMem) :=
  {s | ∀ e, rgBotCnt e s ≤ 0 + 1 - botRevCharge e i}

theorem rgBotCnt_le_one (e : KeyIndex) (s : RReg SelMem) : rgBotCnt e s ≤ 1 := by
  unfold rgBotCnt
  split_ifs <;> omega

theorem rgBotCnt_congr {e : KeyIndex} {s s' : RReg SelMem} (h : s'.2.2.1 = s.2.2.1) :
    rgBotCnt e s' = rgBotCnt e s := by
  unfold rgBotCnt
  rw [h]

/-- **Every port of the decompressed runtime raises the counter by at most its charge.** -/
theorem rgBotCnt_step (e : KeyIndex) (i : (RSpec SelMem).Port) (r : (RSpec SelMem).Result i)
    (t : ℕ)
    (σ : Matrix ((RSpec SelMem).In i × (decR (X := HashOutput) (Z := HashDomain) m0Q).D)
      ((RSpec SelMem).In i × (decR (X := HashOutput) (Z := HashDomain) m0Q).D) ℂ)
    (hσ : QuerySupportedOn (fun m : (RSpec SelMem).In i ×
      (decR (X := HashOutput) (Z := HashDomain) m0Q).D ↦ rgBotCnt e m.2) (Set.Iic t) σ) :
    QuerySupportedOn (fun m : (RSpec SelMem).Out i ×
      (decR (X := HashOutput) (Z := HashDomain) m0Q).D ↦ rgBotCnt e m.2)
      (Set.Iic (t + botRevCharge e i))
      (((decR (X := HashOutput) (Z := HashDomain) m0Q).step i).branch r σ) := by
  have hσ' : QuerySupportedOn (fun m : (RSpec SelMem).In i × RReg SelMem ↦ m.2)
      {s | rgBotCnt e s ≤ t} σ := hσ.imp fun _ h ↦ h
  refine (?_ : QuerySupportedOn (fun m : (RSpec SelMem).Out i × RReg SelMem ↦ m.2)
    {s | rgBotCnt e s ≤ t + botRevCharge e i} _).imp fun _ h ↦ h
  have hall : botRevCharge e i = 1 → ∀ τ : Matrix ((RSpec SelMem).Out i × RReg SelMem)
      ((RSpec SelMem).Out i × RReg SelMem) ℂ,
      QuerySupportedOn (fun m : (RSpec SelMem).Out i × RReg SelMem ↦ m.2)
        {s | rgBotCnt e s ≤ t + botRevCharge e i} τ := fun h1 τ _ _ _ ↦ by
    rw [h1]
    exact ⟨(rgBotCnt_le_one e _).trans (Nat.le_add_left 1 t),
      (rgBotCnt_le_one e _).trans (Nat.le_add_left 1 t)⟩
  rcases i with ((p | c) | c) | T
  · exact (decR_sponge_supp m0Q p r _ σ hσ').mono fun _ hs ↦ hs.trans (Nat.le_add_right _ _)
  · by_cases hc : RdPort c
    · obtain ⟨z, u, rfl⟩ := hc
      refine (decR_readH_supp m0Q z u r _ σ hσ').mono ?_
      rintro _ ⟨s, hs, -, rfl⟩
      exact hs.trans (Nat.le_add_right _ _)
    · exact hall (ite_eq_right hc) _
  · by_cases hc : PgPort c
    · obtain ⟨z, a, rfl⟩ := hc
      refine (decR_progH_supp m0Q z a r _ σ hσ').mono ?_
      rintro s' ⟨s, hs, hR⟩
      exact ((rgBotCnt_congr (congrArg (fun p ↦ p.2.1) hR.1)).trans_le hs).trans
        (Nat.le_add_right _ _)
    · exact hall (ite_eq_right hc) _
  · by_cases hT : BotRev e T
    · exact hall (ite_eq_left hT) _
    · refine (decR_rec_supp m0Q T r _ σ hσ').mono ?_
      rintro s' ⟨s, hs, -, rfl⟩
      show rgBotCnt e (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) ≤ t + botRevCharge e (.inr T)
      rw [botRevCharge_rec_of_not hT, Nat.add_zero]
      refine le_trans ?_ (show rgBotCnt e s ≤ t from hs)
      by_cases hb : BotRev e s.2.2.1
      · rw [show rgBotCnt e s = 1 from ite_eq_left hb]
        exact rgBotCnt_le_one e _
      · have hb' : ¬BotRev e (s.2.2.1 ∪ T) := fun ⟨m, hm⟩ ↦
          (Finset.mem_union.mp hm).elim (fun h ↦ hb ⟨m, h⟩) fun h ↦ hT ⟨m, h⟩
        show @ite _ (BotRev e (s.2.2.1 ∪ T)) (Classical.propDecidable _) 1 0 ≤ _
        rw [ite_eq_right hb']
        exact Nat.zero_le _

theorem rgBotCnt_init (e : KeyIndex) :
    QuerySupportedOn (fun m : QReg.of Unit × (decR (X := HashOutput) (Z := HashDomain) m0Q).D ↦
      rgBotCnt e m.2) (Set.Iic 0)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg HashOutput HashDomain QMem) initQ) := by
  refine (init_decQ m0Q).imp fun m hm ↦ ?_
  have h : m.2.2.2.1 = ∅ := congrArg (fun p ↦ p.2.1) hm.2
  show rgBotCnt e m.2 ≤ 0
  unfold rgBotCnt
  rw [ite_eq_right fun ⟨_, hb⟩ ↦ by rw [h] at hb; exact Finset.notMem_empty _ hb]

/-- **The guard at the calls of the prefix**, in the decompressed basis, against an adversary that
reuses no leaf. -/
theorem forallQueries_rgGuard {A : Adversary} (hleaf : NoLeafReuse A) (θ : HPos → Digest) :
    (decR (X := HashOutput) (Z := HashDomain) m0Q).ForallQueries .instruments (fun i E σ ↦
      QuerySupportedOn (fun m : ((RSpec SelMem).In i × RReg SelMem) × E ↦ m.1.2) (rgGuard i) σ)
      (prefixQ A θ)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg HashOutput HashDomain QMem) initQ) :=
  (forallQueries_forall (decR (X := HashOutput) (Z := HashDomain) m0Q) fun e ↦
    forallQueries_of_charge_budget (decR (X := HashOutput) (Z := HashDomain) m0Q) (rgBotCnt e)
      (botRevCharge e) (rgBotCnt_step e) .instruments _ (chgBot_prefixQ θ e hleaf)
      (rgBotCnt_init e)).mono .instruments fun _ _ _ h m m' hm ↦
    ⟨fun e ↦ (h e m m' hm).1, fun e ↦ (h e m m' hm).2⟩

end guard

/-! ## The steps -/

section steps

variable {θ : HPos → Digest}

/-- **A reveal keeps the invariant within the guard**: a reveal of a bottom base starts the
search of an unselected key, a reveal of a top base the search of its canonical label. -/
theorem rgInv_rec {μ : RgMode} {T : Finset HPos} (hT : RgRevOk θ T) {s s' : RReg SelMem}
    (hs : s ∈ rgInv θ μ) (hg : s ∈ rgGuard (.inr T))
    (hs' : s' = (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2))) : s' ∈ rgInv θ (rgRev θ T, μ.2) := by
  subst hs'
  have hG := rgGlob_of_inv hs
  have hGlob : RgGlob θ μ.2 (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) :=
    rgGlob_congr (s := s) (s' := (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2))) (fun _ h ↦ h) hG.1 hG.2.1
      hG.2.2.1 (fun _ _ _ _ ↦ rfl) rfl Finset.subset_union_left hG
  have hbt : bottomLayer ≠ topLayer := by decide
  rcases rgRev_cases θ T with h | ⟨p, rfl, h⟩
  · rw [h]
    exact hGlob
  · rw [h]
    cases p with
    | rndBottom e m =>
      refine ⟨hGlob, ⟨fun _ ↦ ⟨m, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩,
        fun h' ↦ absurd h' hbt⟩, fun sel hsel ↦ ?_, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
      exfalso
      obtain ⟨msg', base', hl, -⟩ := hG.2.2.2 _ _ sel hsel
      have hc := hg e
      rw [show botRevCharge e (.inr {loC (.rndBottom e m)}) = 1 from
        ite_eq_left ⟨m, Finset.mem_singleton_self _⟩] at hc
      unfold rgBotCnt at hc
      rw [ite_eq_left (hl.1 rfl)] at hc
      omega
    | rndTop b d =>
      have hd : d = rgRoot θ b := hT b d rfl
      subst hd
      refine ⟨hGlob, ⟨fun h' ↦ absurd h'.symm hbt, fun _ ↦ ⟨rfl, rfl⟩⟩, fun sel hsel ↦ ?_,
        fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
      obtain ⟨msg', base', hl, hw⟩ := hG.2.2.2 _ _ sel hsel
      obtain ⟨h1, h2⟩ := hl.2 rfl
      subst h1 h2
      exact rgSelW_congr (fun _ h ↦ h) (fun _ ↦ rfl) hw
    | seed => exact hGlob
    | param => exact hGlob
    | prf => exact hGlob
    | chain => exact hGlob
    | leaf => exact hGlob
    | node => exact hGlob

/-- **Every allowed call keeps the invariant of its mode**, within the guard. -/
theorem rgInv_step (μ : RgMode) (i : (RSpec SelMem).Port) (r : (RSpec SelMem).Result i)
    (σ : Matrix ((RSpec SelMem).In i × (decR (X := HashOutput) (Z := HashDomain) m0Q).D)
      ((RSpec SelMem).In i × (decR (X := HashOutput) (Z := HashDomain) m0Q).D) ℂ)
    (hok : rgOkZ θ μ i)
    (hσ : QuerySupportedOn (fun m : (RSpec SelMem).In i ×
      (decR (X := HashOutput) (Z := HashDomain) m0Q).D ↦ m.2) (rgInv θ μ ∩ rgGuard i) σ) :
    QuerySupportedOn (fun m : (RSpec SelMem).Out i ×
      (decR (X := HashOutput) (Z := HashDomain) m0Q).D ↦ m.2) (rgInv θ (rgNxZ θ μ i r))
      (((decR (X := HashOutput) (Z := HashDomain) m0Q).step i).branch r σ) := by
  rcases i with ((p | c) | c) | T
  · exact (decR_sponge_supp m0Q p r _ σ hσ).mono fun _ hs ↦ rgGlob_of_inv hs.1
  · obtain ⟨σ₀, rd⟩ := μ
    cases σ₀ with
    | free => exact hok.elim
    | srch l e msg base j =>
      obtain ⟨z, hz⟩ : ∃ z, z = trialCell (tabOf θ).param l e msg base j := ⟨_, rfl⟩
      have hc : c = trialRead z l e := by rw [hz]; exact hok
      subst hc
      refine (decR_readH_supp m0Q z (cwUpd l e z) r _ σ hσ).mono ?_
      rintro _ ⟨s, ⟨hs, -⟩, rfl, rfl⟩
      have hv : (hwView s.2.1 s.1).1 z = some (hvw s z) := hwView_eq_some_hvw hs.1.1 z
      have hmode : rgNxZ θ (.srch l e msg base j, rd) (.inl (.inl (.inr (trialRead z l e))))
          (liftAns s (.readH z (cwUpd l e z))) =
          ((if Codeword.Valid (truncateHash (hvw s z)) then .free
            else .srch l e msg base (j + 1)), Function.update rd z (some (hvw s z))) := by
        show ((if Codeword.Valid (truncateHash (((hwView s.2.1 s.1).1 z).getD 0)) then SMode.free
          else SMode.srch l e msg base (j + 1)), Function.update rd z ((hwView s.2.1 s.1).1 z)) = _
        rw [hv]
        rfl
      rw [hmode]
      exact rgInv_read hz hs rfl rfl rfl
        (by show cwUpd l e z s.2.2.2 ((hwView s.2.1 s.1).1 z) = _; rw [hv])
  · obtain ⟨z, a, rfl, hz⟩ := hok
    refine (decR_progH_supp m0Q z a r _ σ hσ).mono ?_
    rintro _ ⟨_, hs, hR⟩
    exact rgInv_prog hz hs.1 hR
  · refine (decR_rec_supp m0Q T r _ σ hσ).mono ?_
    rintro _ ⟨_, hs, -, hs'⟩
    exact rgInv_rec hok hs.1 hs.2 hs'

variable (θ)

theorem rgInv_init :
    QuerySupportedOn (fun m : QReg.of Unit × RReg SelMem ↦ m.2) (rgInv θ (.free, fun _ ↦ none))
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg HashOutput HashDomain QMem) initQ) := by
  refine (init_decQ m0Q).mono ?_
  rintro s ⟨hn, hs⟩
  have hW : s.2.1 = hwEmpty HashOutput HashDomain := congrArg Prod.fst hs
  have hm : s.2.2 = m0Q := congrArg Prod.snd hs
  refine ⟨hn, fun x _ _ _ ↦ by simp [hW, hwEmpty, Database.empty], fun _ _ h ↦ by simp at h,
    fun l e sel h ↦ ?_⟩
  rw [hm] at h
  simp [m0Q] at h

/-! ## The invariant at the calls of the prefix -/

/-- **The invariant at the calls of the prefix, in the decompressed basis.** -/
theorem forallQueries_rgInv_dec {A : Adversary} (hleaf : NoLeafReuse A) :
    (decR (X := HashOutput) (Z := HashDomain) m0Q).ForallQueries .instruments (fun i E σ ↦ ∃ μ,
      rgOkZ θ μ i ∧ QuerySupportedOn (fun m : ((RSpec SelMem).In i × RReg SelMem) × E ↦ m.1.2)
        (rgInv θ μ) σ) (prefixQ A θ)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg HashOutput HashDomain QMem) initQ) :=
  forallQueries_of_modedP_sguard (decR (X := HashOutput) (Z := HashDomain) m0Q) .instruments
    (rgInv θ) rgGuard (fun μ i r σ hok hσ ↦ rgInv_step μ i r σ hok hσ) (prefixQ A θ)
    (.free, fun _ ↦ none) (rgModed_prefixQ θ A _) (forallQueries_rgGuard hleaf θ) (rgInv_init θ)

/-- **The invariant at the calls of the prefix**: against an adversary that reuses no leaf,
every call of `prefixQ A θ` is presented an operator whose decompressed form is supported on the
invariant of a mode allowing it. -/
theorem forallQueries_rgInv {A : Adversary} (hleaf : NoLeafReuse A) :
    (runtimeR m0Q).ForallQueries .instruments (fun i E τ ↦ ∃ μ, rgOkZ θ μ i ∧
      QuerySupportedOn (fun m : (RSpec SelMem).In i × RReg SelMem ↦ m.2) (rgInv θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpec SelMem).In i) ((RSpec SelMem).In i) ℂ) ⊗ₖ
          compressReg HashOutput HashDomain QMem) (MatrixMap.traceRight _ E τ))) (prefixQ A θ)
      initQ := by
  have hC : compressReg HashOutput HashDomain QMem * compressReg HashOutput HashDomain QMem = 1 :=
    compressReg_mul_self
  have hstep : ∀ i r, ((runtimeRH (X := HashOutput) (Z := HashDomain) m0Q).step i).branch r ∘ₗ
      (MatrixMap.conj (compressReg HashOutput HashDomain QMem)).amplifyLeft
        ((RSpec SelMem).In i) =
      (MatrixMap.conj (compressReg HashOutput HashDomain QMem)).amplifyLeft
        ((RSpec SelMem).Out i) ∘ₗ
        ((decR (X := HashOutput) (Z := HashDomain) m0Q).step i).branch r := fun i r ↦ by
    rw [conjReg_branch (runtimeRH m0Q) (compressReg HashOutput HashDomain QMem)
      compressReg_mul_self conjTranspose_compressReg i r]
    simp only [MatrixMap.amplifyLeft_conj]
    rw [← LinearMap.comp_assoc, conj_one_kronecker_comp_self (runtimeRH m0Q) _ hC,
      LinearMap.id_comp]
  have h2 := ForallQueries.of_simulation .instruments
    (R₁ := decR (X := HashOutput) (Z := HashDomain) m0Q)
    (R₂ := runtimeRH (X := HashOutput) (Z := HashDomain) m0Q)
    (V := MatrixMap.conj (compressReg HashOutput HashDomain QMem)) hstep
    (P₂ := fun i E τ ↦ ∃ μ, rgOkZ θ μ i ∧
      QuerySupportedOn (fun m : (RSpec SelMem).In i × RReg SelMem ↦ m.2) (rgInv θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpec SelMem).In i) ((RSpec SelMem).In i) ℂ) ⊗ₖ
          compressReg HashOutput HashDomain QMem) (MatrixMap.traceRight _ E τ)))
    (fun i E τ ⟨μ, hok, hτ⟩ ↦ ⟨μ, hok, by
      rw [MatrixMap.amplifyLeft_conj,
        ← LinearMap.comp_apply (MatrixMap.conj _) (MatrixMap.traceRight _ E),
        ← MatrixMap.traceRight_comp_amplify, LinearMap.comp_apply,
        ← LinearMap.comp_apply (MatrixMap.amplify _ E) (MatrixMap.amplify _ E),
        ← MatrixMap.amplify_comp, conj_one_kronecker_comp_self (runtimeRH m0Q) _ hC,
        MatrixMap.amplify_id, LinearMap.id_apply]
      exact querySupportedOn_traceRight
        (q := fun m : (RSpec SelMem).In i × RReg SelMem ↦ m.2) hτ⟩)
    (forallQueries_rgInv_dec θ hleaf)
  have hρ' : (MatrixMap.conj (compressReg HashOutput HashDomain QMem)).amplifyLeft (QReg.of Unit)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg HashOutput HashDomain QMem) initQ) = initQ := by
    rw [MatrixMap.amplifyLeft_conj,
      ← LinearMap.comp_apply (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg HashOutput HashDomain QMem)), conj_one_kronecker_comp_self (runtimeRH m0Q) _ hC,
      LinearMap.id_apply]
  rw [hρ'] at h2
  exact h2

end steps

end Quantum.Qrom.Xmss

end
