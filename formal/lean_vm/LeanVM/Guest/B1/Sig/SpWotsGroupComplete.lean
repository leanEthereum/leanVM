/-
  LeanVM.Guest.B1.Sig.SpWotsGroupComplete

  The digit dispatches of `sp_wots` complete in sequence: each digit word `g^k` loaded, each
  dispatch taking arm `k`, whose chains' starts are loaded, over the padding run.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsStepComplete
public import LeanVM.Guest.B1.Sig.SpWotsArms
public import LeanVM.Guest.B1.Sig.SpWotsCheck
public import LeanVM.Guest.B1.Sig.WotsChainComplete

/-!
# The dispatches, complete

A dispatch of `sp_wots` is over `armsM spW`, whose arm `k` below `4^n` is the shared arm `armT spW`
(`armM_eq`): so a dispatch completes by the shared `matchArm_complete`, its chain step in
single-assignment form above the padding run and reading it (`SpGood spPad`, `spWp_shape`,
`spWp_stable`), as leanXMSS's in `main_loop2` (`XmssSegCodeC`).

* `SpArmPost`: arm `k`'s starts holding `vals`;
* `spArmB_eq`, `spGroupArms_getElem`, `spGroupArms_end_ge`, `spGroupMatch_numBelow`: arm `k` below
  `4^n` is `armT`'s from `armB`'s base; a dispatch ends past its `4^n` arms; its values are numbered
  below its end;
* `spState_step`, `spState_mono`, `spState_in`: the groups' bases grow, the running product and
  encoding below each;
* `spPos`, `SpMPost`, `spMatches_complete`, `spMatches_numBelow`: the dispatches complete in
  sequence, each by the arm of its honest digits, its chains' starts loaded.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- What arm `k` of the group from `B` leaves: its starts holding `vals`. -/
def SpArmPost (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat) (vals : Nat → E)
    (σ : Val) : Prop :=
  ∀ t < n, σ (spStartOf first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k) t) = vals t

theorem padRun_seq (P : Nat) : SeqOK P (padRun P) (P + 5) := by
  simp [padRun, List.range_succ, SeqOK, ASeq, cst]

theorem spW_shape {Bs : Nat} (h : spPad + 5 ≤ Bs) : StepShape spW Bs :=
  StepShape.mono (spWp_shape (b := spPad) (B := spPad + 5) le_rfl (by simp [spPad])) h

theorem spW_stable {Bs : Nat} (h : spPad + 5 ≤ Bs) : GoodStable Bs (SpGood spPad) :=
  (spWp_stable (b := spPad) (B := spPad + 5) le_rfl).mono h

theorem spW_power_nb' {Bs k n : Nat} (h : 16 ≤ Bs) (hn : n ≤ 3) : NBv Bs (spW.power (digitSum k n)) :=
  ⟨6 + digitSum k n, by have := digitSum_le_nine k n hn; omega, rfl⟩

/-! ## A group's arms -/

theorem spN_le' (p : Nat) : spN p ≤ 3 := by unfold spN; split <;> omega

theorem four_pow_spN_le (p : Nat) : 4 ^ spN p ≤ 64 := by unfold spN; split <;> norm_num

theorem spN_pos (p : Nat) : 1 ≤ spN p := by unfold spN; split <;> omega

/-- Arm `k ≤ 4^n`'s base is the shared `armB`'s. -/
theorem spArmB_eq (first n : Nat) (fold : Bool) (vb : Nat) (prodIn encIn : V) {k : Nat} (hk : k ≤ 4 ^ n) :
    spArmB first n fold vb prodIn encIn k = armB spW first n fold prodIn encIn vb k :=
  armBaseM_eq _ _ _ _ _ _ _ _ _ 0 k _ (by omega)

/-- **Arm `k` below `4^n` of group `p`'s dispatch** is `armT`'s from `armB`'s base. -/
theorem spGroupArms_getElem {p k : Nat} (hk : k < 4 ^ spN p) (prodIn encIn : V) (vb : Nat) :
    ∃ h : k < (spGroupArms p prodIn encIn vb).1.length, (spGroupArms p prodIn encIn vb).1[k] =
      (armT spW (slotsT spW (p == 0) vb) (3 * p) (spN p) (p == 0) prodIn encIn
        (prodT spW (p == 0) (spN p) vb) (encT spW (p == 0) (spN p) vb) k
        (armB spW (3 * p) (spN p) (p == 0) prodIn encIn vb k)).1 := by
  have h64 := four_pow_spN_le p
  have hl : k < (spGroupArms p prodIn encIn vb).1.length := by
    rw [spGroupArms_eq, spArmsT, armsM_length]; omega
  refine ⟨hl, ?_⟩
  simp only [spGroupArms_eq, spArmsT]
  rw [armsM_getElem]
  simp only [Nat.zero_add]
  rw [armM_eq _ _ _ _ _ _ _ _ _ _ hk, armBaseM_eq _ _ _ _ _ _ _ _ _ 0 k _ (by omega)]
  rfl

/-- **Group `p`'s dispatch ends past its `4^n` arms.** -/
theorem spGroupArms_split (p : Nat) (prodIn encIn : V) (vb : Nat) :
    spGroupArms p prodIn encIn vb =
      ((armsT spW (slotsT spW (p == 0) vb) (3 * p) (spN p) (p == 0) prodIn encIn
          (prodT spW (p == 0) (spN p) vb) (encT spW (p == 0) (spN p) vb) (4 ^ spN p) 0 (vb + 6)).1 ++
        (armsM spW (slotsT spW (p == 0) vb) (3 * p) (spN p) (p == 0) prodIn encIn
          (prodT spW (p == 0) (spN p) vb) (encT spW (p == 0) (spN p) vb) (64 - 4 ^ spN p) (4 ^ spN p)
          (armB spW (3 * p) (spN p) (p == 0) prodIn encIn vb (4 ^ spN p))).1,
        (armsM spW (slotsT spW (p == 0) vb) (3 * p) (spN p) (p == 0) prodIn encIn
          (prodT spW (p == 0) (spN p) vb) (encT spW (p == 0) (spN p) vb) (64 - 4 ^ spN p) (4 ^ spN p)
          (armB spW (3 * p) (spN p) (p == 0) prodIn encIn vb (4 ^ spN p))).2) := by
  have h64 := four_pow_spN_le p
  simp only [spGroupArms_eq, spArmsT]
  rw [show (64 : Nat) = 4 ^ spN p + (64 - 4 ^ spN p) by omega, armsM_append,
    armsM_eq _ _ _ _ _ _ _ _ _ (4 ^ spN p) 0 _ (by omega), armsT_snd, Nat.zero_add, Nat.add_sub_cancel_left]
  rfl

theorem spGroupArms_end_ge (p : Nat) (prodIn encIn : V) (vb : Nat) :
    armB spW (3 * p) (spN p) (p == 0) prodIn encIn vb (4 ^ spN p) ≤ (spGroupArms p prodIn encIn vb).2 := by
  rw [spGroupArms_split]
  exact armsM_snd_ge _ _ _ _ _ _ _ _ _ _ _ _

theorem spGroupArms_end_one (p : Nat) (prodIn encIn : V) (vb : Nat) :
    groupStart (p == 0) vb + chainStride spW * spN p + 2 ≤ (spGroupArms p prodIn encIn vb).2 := by
  rw [← armB_one spW (3 * p) (spN p) (p == 0) prodIn encIn vb]
  exact le_trans (armB_mono spW _ _ _ _ _ _ (Nat.one_le_two_pow.trans (Nat.pow_le_pow_left (by norm_num) _)))
    (spGroupArms_end_ge p prodIn encIn vb)

/-- **A group's dispatch is numbered below its end.** -/
theorem spGroupMatch_numBelow {B : Nat} (hW : StepShape spW B) {p vb d : Nat} {prodIn encIn : V}
    (hB : B ≤ vb + 6) (hd : d < vb + 6) (hpi : NBv (vb + 6) prodIn) (hei : NBv (vb + 6) encIn)
    (hpw : ∀ k, NBv (vb + 6) (spW.power (digitSum k (spN p)))) :
    NumBelow (spGroupArms p prodIn encIn vb).2
      (Stmt.valsList [.match_ (.n d) (spGroupArms p prodIn encIn vb).1]) := by
  have hge := spGroupArms_end_one p prodIn encIn vb
  have hgs : vb + 6 ≤ groupStart (p == 0) vb := by rw [groupStart_eq]
  simp only [valsList_cons, valsList_nil, List.append_nil, Stmt.vals]
  refine NumBelow.cons ⟨d, by omega, rfl⟩ ?_
  have h1 := groupArmsT_numBelow (first := 3 * p) (n := spN p) (fold := p == 0) hW hB hpi hei hpw
  have h1' : NumBelow (armB spW (3 * p) (spN p) (p == 0) prodIn encIn vb (4 ^ spN p))
      (Stmt.valsArms (armsT spW (slotsT spW (p == 0) vb) (3 * p) (spN p) (p == 0) prodIn encIn
        (prodT spW (p == 0) (spN p) vb) (encT spW (p == 0) (spN p) vb) (4 ^ spN p) 0 (vb + 6)).1) := by
    simpa only [groupArmsT] using h1
  rw [spGroupArms_split]
  dsimp only
  rw [valsArms_append]
  rcases Nat.lt_or_ge p 21 with hp | hp
  · have hn : spN p = 3 := by simp [spN, hp]
    have e : (64 : Nat) - 4 ^ spN p = 0 := by rw [hn]; norm_num
    rw [e]
    simp only [armsM, Stmt.valsArms, List.append_nil]
    exact h1'
  · have hn : spN p = 1 := by simp [spN, show ¬ p < 21 by omega]
    have hp0 : (p == 0) = false := by simp; omega
    rw [hp0] at h1' ⊢
    rw [hn] at h1' hpw ⊢
    have hle := armsM_snd_ge spW (slotsT spW false vb) (3 * p) 1 false prodIn encIn (prodT spW false 1 vb)
      (encT spW false 1 vb) 60 4 (armB spW (3 * p) 1 false prodIn encIn vb 4)
    have h2 := armsM_numBelow (first := 3 * p) (n := 1) hW (by norm_num) hB hpi hei hpw 60 4
      (armB spW (3 * p) 1 false prodIn encIn vb 4) (by norm_num) (by norm_num)
      (armB_pos spW (3 * p) 1 false prodIn encIn vb (by norm_num))
    exact (h1'.mono hle).append h2

/-! ## The groups' state -/

theorem spState_succ_end (p : Nat) :
    (spState (p + 1)).2.2 + 6 = (spGroupArms p (spState p).1 (spState p).2.1 (spState p).2.2).2 := by
  have := armsM_snd_ge spW (slotsT spW (p == 0) (spState p).2.2) (3 * p) (spN p) (p == 0)
    (spState p).1 (spState p).2.1 (prodT spW (p == 0) (spN p) (spState p).2.2)
    (encT spW (p == 0) (spN p) (spState p).2.2) 64 0 ((spState p).2.2 + 6)
  rw [spState_succ]
  simp only [spGroupArms_eq, spArmsT] at this ⊢
  exact Nat.sub_add_cancel (by exact le_trans (by omega) this)

theorem spState_step (p : Nat) :
    (spState p).2.2 + 6 + chainStride spW * spN p + 2 ≤ (spState (p + 1)).2.2 + 6 := by
  rw [spState_succ_end]
  have := spGroupArms_end_one p (spState p).1 (spState p).2.1 (spState p).2.2
  rw [groupStart_eq] at this
  omega

theorem spState_mono (p : Nat) : ∀ m, (spState p).2.2 ≤ (spState (p + m)).2.2
  | 0 => le_rfl
  | m + 1 => by
      have := spState_mono p m
      have := spState_step (p + m)
      rw [show p + (m + 1) = p + m + 1 by omega]
      omega

theorem spState_ge (p : Nat) : spPad ≤ (spState p).2.2 := by
  have := spState_mono 0 p
  rw [Nat.zero_add, spState_zero] at this
  exact this

theorem spState_ge_add : ∀ p, spPad + p ≤ (spState p).2.2
  | 0 => by simp [spState_zero]
  | p + 1 => by
      have := spState_ge_add p
      have := spState_step p
      omega

theorem spState_in : ∀ p, NBv ((spState p).2.2 + 6) (spState p).1 ∧ NBv ((spState p).2.2 + 6) (spState p).2.1
  | 0 => ⟨⟨0, by simp [spState_zero], rfl⟩, ⟨0, by simp [spState_zero], rfl⟩⟩
  | p + 1 => by
      have h := spState_step p
      rw [spState_succ_end] at h
      rw [spState_succ_end, spState_succ]
      simp only [spEnc, spProd, groupStart_eq] at h ⊢
      exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩

/-! ## The dispatches, in sequence -/

/-- Chain `3q + t`'s start, in the arm of group `q`'s digits. -/
def spPos (K : Nat → Nat) (q t : Nat) : V :=
  grpPos spW (3 * q) (spN q) (q == 0) (spState q).1 (spState q).2.1 (spState q).2.2 (K q) t

theorem spPos_lt {K : Nat → Nat} {q t : Nat} (hk : K q < 4 ^ spN q) (ht : t < spN q) :
    ∃ j, spPos K q t = .n j ∧ (spState q).2.2 + 6 ≤ j ∧ j < (spState (q + 1)).2.2 + 6 := by
  obtain ⟨j, e, h1, h2, -⟩ := grpPos_spec spW (3 * q) (spN q) (q == 0) (spState q).1 (spState q).2.1
    (spState q).2.2 (K q) t hk ht
  have := spGroupArms_end_ge q (spState q).1 (spState q).2.1 (spState q).2.2
  rw [← spState_succ_end] at this
  exact ⟨j, e, h1, by omega⟩

theorem spTip_lt {q t : Nat} (ht : t < spN q) :
    (spState q).2.2 + 6 ≤ spSlot (q == 0) (spState q).2.2 t 2 ∧
      spSlot (q == 0) (spState q).2.2 t 2 < (spState (q + 1)).2.2 + 6 := by
  have hs := slot_bounds spW (q == 0) (spState q).2.2 t 2 (by norm_num)
  have h3 : chainStride spW * (t + 1) ≤ chainStride spW * spN q := Nat.mul_le_mul_left _ (by omega)
  have := spState_step q
  rw [groupStart_eq] at hs
  unfold spSlot
  constructor <;> omega

/-- What the dispatches `p ..< p + m` establish: the padding run, and per group its chains' starts
loaded. -/
def SpMPost (K : Nat → Nat) (vals : Nat → E) (p m : Nat) (σ : Val) : Prop :=
  SpGood spPad σ ∧ ∀ q, p ≤ q → q < p + m → ∀ t < spN q, σ (spPos K q t) = vals (3 * q + t)

section groups

variable (K : Nat → Nat) (hK : ∀ p < 22, K p < 4 ^ spN p) (vals : Nat → E)
include hK

/-- **The dispatches `p ..< p + m` complete**, each by the arm of its digits `K q`, the digit words
loaded. -/
theorem spMatches_complete : ∀ m p, p + m ≤ 22 → ∀ σ, SpGood spPad σ →
    (∀ q < 22, σ (.n (spDg + q)) = ofK (addressOfIndex (K q))) →
    Completes C rd ((spState p).2.2 + 6) ((spState (p + m)).2.2 + 6)
      ((List.range m).map fun q => spMatch (p + q)) σ (SpMPost K vals p m)
  | 0, p, _, σ, hg, _ => ⟨σ, Ext.refl _ _ _, ⟨hg, fun q h1 h2 => by omega⟩, fun _ _ hn => hn⟩
  | m + 1, p, hpm, σ, hg, hx => by
      have hvp := spState_ge p
      have hBp : spPad + 5 ≤ (spState p).2.2 + 6 := by omega
      obtain ⟨hpi, hei⟩ := spState_in p
      have hkp := hK p (by omega)
      obtain ⟨hkl, harm⟩ := spGroupArms_getElem (p := p) hkp (spState p).1 (spState p).2.1 (spState p).2.2
      have hend := spState_succ_end p
      have hE := spGroupArms_end_ge p (spState p).1 (spState p).2.1 (spState p).2.2
      have hhead := matchArm_complete (C := C) (rd := rd) (spW_shape hBp) (spW_stable hBp) (spWp_atoms spPad)
        (first := 3 * p) (Ee := (spState (p + 1)).2.2 + 6) (d := spDg + p) hkp le_rfl
        (hpi.mono' le_rfl) (hei.mono' le_rfl) (spW_power_nb' (by simp [spPad] at hvp ⊢; omega) (spN_le' p))
        hkl harm (by rw [hend]; exact hE) (by simp only [spDg, spPad] at hvp ⊢; omega)
        (fun t => vals (3 * p + t)) σ hg (hx p (by omega))
      have hnb := spGroupMatch_numBelow (spW_shape hBp) (p := p) (d := spDg + p) le_rfl
        (by simp only [spDg, spPad] at hvp ⊢; omega) hpi hei
        (fun _ => spW_power_nb' (by simp only [spPad] at hvp; omega) (spN_le' p))
      rw [← hend] at hnb
      have hl : (List.range (m + 1)).map (fun q => spMatch (p + q)) =
          [spMatch p] ++ (List.range m).map (fun q => spMatch (p + 1 + q)) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero, List.singleton_append]
        congr 1
        exact List.map_congr_left fun q _ => by
          simp only [Function.comp_apply, show p + (q + 1) = p + 1 + q by omega]
      have hm1 := spState_mono (p + 1) m
      have hp1 := spState_step p
      rw [hl, show p + (m + 1) = p + 1 + m by omega]
      refine Completes.append (m := (spState (p + 1)).2.2 + 6) (by omega) (by omega) hnb hhead
        (fun σ1 he1 hq1 => ?_)
      have hx1 : ∀ q < 22, σ1 (.n (spDg + q)) = ofK (addressOfIndex (K q)) := fun q hq => by
        rw [he1.apply (Or.inl (by simp only [spDg, spPad] at hvp ⊢; omega))]; exact hx q hq
      have ih := spMatches_complete m (p + 1) (by omega) σ1 hq1.1 hx1
      refine (ih.keep (Q := fun σ => ∀ t < spN p, σ (spPos K p t) = vals (3 * p + t))
        (Q' := fun σ => ∀ t < spN p, σ (spPos K p t) = vals (3 * p + t))
        hq1.2.1 (fun σ' he' hq t ht => ?_)).mono le_rfl le_rfl
        (fun σ' ⟨⟨hg', hr⟩, hq'⟩ => ⟨hg', fun q h1 h2 => ?_⟩)
      · obtain ⟨j, ej, -, hj⟩ := spPos_lt (K := K) (q := p) hkp ht
        rw [ej, he'.apply (Or.inl hj), ← ej]
        exact hq t ht
      · rcases Nat.lt_or_ge q (p + 1) with hq | hq
        · obtain rfl : q = p := by omega
          exact hq'
        · exact hr q hq (by omega)

omit hK in
theorem spMatches_numBelow : ∀ m p, NumBelow ((spState (p + m)).2.2 + 6)
    (Stmt.valsList ((List.range m).map fun q => spMatch (p + q)))
  | 0, _ => NumBelow.nil _
  | m + 1, p => by
      have hvp := spState_ge p
      have hBp : spPad + 5 ≤ (spState p).2.2 + 6 := by omega
      obtain ⟨hpi, hei⟩ := spState_in p
      have hnb := spGroupMatch_numBelow (spW_shape hBp) (p := p) (d := spDg + p) le_rfl
        (by have := spState_ge_add p; simp only [spDg, spPad] at this ⊢; omega) hpi hei
        (fun _ => spW_power_nb' (by simp only [spPad] at hvp; omega) (spN_le' p))
      rw [← spState_succ_end] at hnb
      have hm1 := spState_mono (p + 1) m
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero, valsList_cons]
      have ih := spMatches_numBelow m (p + 1)
      rw [show p + 1 + m = p + (m + 1) by omega] at ih hm1
      have h' : NumBelow ((spState (p + (m + 1))).2.2 + 6) (spMatch p).vals := by
        have := hnb.mono (show (spState (p + 1)).2.2 + 6 ≤ (spState (p + (m + 1))).2.2 + 6 by omega)
        rwa [valsList_cons, valsList_nil, List.append_nil] at this
      refine h'.append ?_
      refine (List.map_congr_left fun q _ => ?_) ▸ ih
      simp only [Function.comp_apply, show p + 1 + q = p + (q + 1) by omega]

end groups

end
end LeanVM.Guest.B1.Sig
