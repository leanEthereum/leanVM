/-
  LeanVM.Guest.B1.Sig.XmssSegCwC

  The dispatches of leanXMSS's codeword inline in `__loop2` complete: an arm `k` below `4^n` is
  `armT`'s, and a group's dispatch completes by the arm of its honest digits.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegStepC
public import LeanVM.Guest.B1.Sig.WotsGroupComplete
public import LeanVM.Guest.B1.Sig.XmssSegArms

/-!
# The codeword's dispatches, complete

* `armM_eq`, `armsM_eq`: arm `k < 4^n` of a group is `armT`'s; the `4^4` arms of a group of four
  are `armsT`'s;
* `armsM_append`: the arms of a table split at an arm;
* `matchArm_complete`: a dispatch on `d` whose arm `k` is `armT`'s from `armB … k`, its chains'
  starts `vals` loaded: the arm's atoms and its starts kept, the step's reads
  (`good`) kept.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The arms -/

theorem armM_eq (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) {k : Nat} (b : Nat) (hk : k < 4 ^ n) :
    armM W slots first n fold prodIn encIn prodOut encOut k b =
      armT W slots first n fold prodIn encIn prodOut encOut k b := by
  simp only [armM, armT, Nat.mod_eq_of_lt hk]

theorem armsM_eq (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : ∀ (m k b : Nat), k + m ≤ 4 ^ n →
    armsM W slots first n fold prodIn encIn prodOut encOut m k b =
      armsT W slots first n fold prodIn encIn prodOut encOut m k b
  | 0, _, _, _ => rfl
  | m + 1, k, b, h => by
      simp only [armsM, armsT, armM_eq W slots first n fold prodIn encIn prodOut encOut b
        (show k < 4 ^ n by omega)]
      rw [armsM_eq W slots first n fold prodIn encIn prodOut encOut m (k + 1) _ (by omega)]

theorem armsM_append (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (m : Nat) : ∀ (j k b : Nat),
    armsM W slots first n fold prodIn encIn prodOut encOut (j + m) k b =
      ((armsM W slots first n fold prodIn encIn prodOut encOut j k b).1 ++
        (armsM W slots first n fold prodIn encIn prodOut encOut m (k + j)
          (armsM W slots first n fold prodIn encIn prodOut encOut j k b).2).1,
        (armsM W slots first n fold prodIn encIn prodOut encOut m (k + j)
          (armsM W slots first n fold prodIn encIn prodOut encOut j k b).2).2)
  | 0, k, b => by simp [armsM]
  | j + 1, k, b => by
      rw [show j + 1 + m = (j + m) + 1 by omega]
      simp only [armsM]
      rw [armsM_append W slots first n fold prodIn encIn prodOut encOut m j (k + 1),
        show k + 1 + j = k + (j + 1) by omega]
      rfl

/-! ## A group's dispatch -/

/-- **A group's dispatch completes** by arm `k`, `armT`'s from `armB … k`, its starts `vals`
loaded, the dispatch's end `Ee` past the arms. -/
theorem matchArm_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : GoodStable B good) (hWa : StepAtoms W) {first n : Nat} {fold : Bool} {prodIn encIn : V}
    {b k d Ee : Nat} {arms : List (List Stmt)} (hk : k < 4 ^ n) (hB : B ≤ b + 6) (hpi : NBv B prodIn)
    (hei : NBv B encIn) (hpw : NBv B (W.power (digitSum k n))) (hkl : k < arms.length)
    (harm : arms[k] = (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b)
      (encT W fold n b) k (armB W first n fold prodIn encIn b k)).1)
    (hE : armB W first n fold prodIn encIn b (4 ^ n) ≤ Ee) (hd : d < b + 6) (vals : Nat → E)
    (σ : Val) (hg : good σ)
    (hx : σ (.n d) = ofK (addressOfIndex k)) :
    Completes C rd (b + 6) Ee [.match_ (.n d) arms] σ
      (fun σ' => good σ' ∧ (∀ t < n, σ' (grpPos W first n fold prodIn encIn b k t) = vals t) ∧
        AtomsHold rd σ' (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b)
          (encT W fold n b) k (armB W first n fold prodIn encIn b k)).1) := by
  set σr := sLoad (grpPos W first n fold prodIn encIn b k) vals σ n with hσr
  have hpos : ∀ t < n, ∃ j, grpPos W first n fold prodIn encIn b k t = .n j ∧ b + 6 ≤ j ∧
      j < armB W first n fold prodIn encIn b (4 ^ n) := fun t ht => by
    obtain ⟨j, e, h1, h2, -⟩ := grpPos_spec W first n fold prodIn encIn b k t hk ht
    exact ⟨j, e, h1, h2⟩
  have hext : Ext (b + 6) (armB W first n fold prodIn encIn b (4 ^ n)) σ σr := fun v hv =>
    sLoad_other _ _ σ n fun t ht e => by
      obtain ⟨j, ej, h1, h2⟩ := hpos t ht
      rw [ej] at e
      exact hv j h1 h2 e
  have hat : ∀ t < n, σr (grpPos W first n fold prodIn encIn b k t) = vals t :=
    sLoad_at _ vals σ n (fun a c h1 h2 => grpPos_ne hk h1 h2)
  have hgr : good σr := hc _ _ (fun j hj => (hext.apply (Or.inl (by omega))).symm) hg
  have hxr : σr (.n d) = ofK (addressOfIndex k) := by rw [hext.apply (Or.inl hd)]; exact hx
  refine Completes.reload (hext.mono le_rfl hE) (match_complete hkl ⟨d, hd, rfl⟩ hxr ?_)
  rw [harm]
  obtain ⟨σ', he', hp', hh'⟩ := groupArm_complete (C := C) (rd := rd) (first := first) (n := n)
    (fold := fold) (prodIn := prodIn) (encIn := encIn) (b := b) (k := k) hW hk hB hpi hei hpw σr
  refine ⟨σ', he'.mono le_rfl hE, ⟨hc _ _ (fun j hj => (he'.apply (Or.inl (by omega))).symm) hgr,
    fun t ht => ?_, atomsHold_of_holdsList (armT_atoms hWa ..)
      (hh' True (fun _ => True) trivial)⟩, hh'⟩
  obtain ⟨j, ej, -⟩ := hpos t ht
  rw [hp'.1, ej, fwd_hint_keep _ σr hp'.2
    (armStart_mem W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) k
      (armB W first n fold prodIn encIn b k) ht) (.n j) (by rw [← ej]; exact List.mem_singleton_self _),
    ← ej, hat t ht]

/-! ## The groups' state -/

theorem armM_snd_ge (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k b : Nat) :
    b ≤ (armM W slots first n fold prodIn encIn prodOut encOut k b).2 := by
  have hw : ∀ st, (if fold then b + 1 else b) ≤
      (walksT W slots first k st n 0 (if fold then b + 1 else b)).2 := fun st => by
    rw [walksT_snd, walkBase_eq]; omega
  have hb : b ≤ (if fold then b + 1 else b) := by split <;> omega
  have h := hw (if k = 0 then W.size + 1 else W.size)
  unfold armM
  by_cases hk : k % 4 ^ n = 0 <;> simp only [hk, ↓reduceIte] <;> omega

theorem armsM_snd_ge (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) :
    ∀ m k b, b ≤ (armsM W slots first n fold prodIn encIn prodOut encOut m k b).2
  | 0, _, _ => le_rfl
  | m + 1, k, b => by
      simp only [armsM]
      refine le_trans ?_ (armsM_snd_ge W slots first n fold prodIn encIn prodOut encOut m (k + 1) _)
      have h1 := armM_snd_ge W slots first n fold prodIn encIn prodOut encOut k b
      split <;> omega

/-- Group `p`'s running product's and encoding's cells and its base (`sGroupsT`'s state), the
first group's base `v0`. -/
def sgState (W : WotsT) (v0 : Nat) : Nat → V × V × Nat
  | 0 => (.n 0, .n 0, v0)
  | p + 1 =>
      let st := sgState W v0 p
      (prodT W (p == 0) (lxN p) st.2.2, encT W (p == 0) (lxN p) st.2.2,
        (sGroupArms W p st.1 st.2.1 st.2.2).2 - 6)

/-- Group `p`'s dispatch. -/
def sgMatch (W : WotsT) (dg v0 p : Nat) : Stmt :=
  .match_ (.n (dg + p)) (sGroupArms W p (sgState W v0 p).1 (sgState W v0 p).2.1 (sgState W v0 p).2.2).1

theorem sGroupsT_fst (W : WotsT) (dg v0 : Nat) : ∀ m p,
    (sGroupsT W dg m p (sgState W v0 p).1 (sgState W v0 p).2.1 (sgState W v0 p).2.2).1 =
      (List.range m).map (fun q => sgMatch W dg v0 (p + q))
  | 0, _ => rfl
  | m + 1, p => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [sGroupsT]
      have := sGroupsT_fst W dg v0 m (p + 1)
      simp only [sgState] at this ⊢
      rw [this]
      congr 1
      refine List.map_congr_left fun q _ => ?_
      simp only [Function.comp_apply, show p + 1 + q = p + (q + 1) by omega]

theorem sgState_succ_end (W : WotsT) (v0 p : Nat) :
    (sgState W v0 (p + 1)).2.2 + 6 =
      (sGroupArms W p (sgState W v0 p).1 (sgState W v0 p).2.1 (sgState W v0 p).2.2).2 := by
  have := armsM_snd_ge W (slotsT W (p == 0) (sgState W v0 p).2.2) (4 * p) (lxN p) (p == 0)
    (sgState W v0 p).1 (sgState W v0 p).2.1 (prodT W (p == 0) (lxN p) (sgState W v0 p).2.2)
    (encT W (p == 0) (lxN p) (sgState W v0 p).2.2) 256 0 ((sgState W v0 p).2.2 + 6)
  simp only [sgState, sGroupArms] at this ⊢
  omega

theorem lxN_four {p : Nat} (hp : p < 14) : lxN p = 4 := by simp [lxN, hp]
theorem lxN_tail : lxN 14 = 2 := rfl

/-- A four-digit group's arms are `armsT`'s; their end is `armB … (4^4)`. -/
theorem sGroupArms_four (W : WotsT) {p : Nat} (hp : p < 14) (prodIn encIn : V) (vb : Nat) :
    sGroupArms W p prodIn encIn vb =
      armsT W (slotsT W (p == 0) vb) (4 * p) 4 (p == 0) prodIn encIn (prodT W (p == 0) 4 vb)
        (encT W (p == 0) 4 vb) 256 0 (vb + 6) := by
  simp only [sGroupArms, lxN_four hp]
  exact armsM_eq W _ _ _ _ _ _ _ _ 256 0 _ (by norm_num)

theorem sGroupArms_four_snd (W : WotsT) {p : Nat} (hp : p < 14) (prodIn encIn : V) (vb : Nat) :
    (sGroupArms W p prodIn encIn vb).2 = armB W (4 * p) 4 (p == 0) prodIn encIn vb (4 ^ 4) := by
  rw [sGroupArms_four W hp, armsT_snd, armB, show (4 : Nat) ^ 4 = 256 by norm_num]

/-- The tail's arms: the first `4^2` are `armsT`'s. -/
theorem sGroupArms_tail (W : WotsT) (prodIn encIn : V) (vb : Nat) :
    sGroupArms W 14 prodIn encIn vb =
      ((armsT W (slotsT W false vb) 56 2 false prodIn encIn (prodT W false 2 vb) (encT W false 2 vb) 16 0
          (vb + 6)).1 ++
        (armsM W (slotsT W false vb) 56 2 false prodIn encIn (prodT W false 2 vb) (encT W false 2 vb) 240 16
          (armB W 56 2 false prodIn encIn vb 16)).1,
        (armsM W (slotsT W false vb) 56 2 false prodIn encIn (prodT W false 2 vb) (encT W false 2 vb) 240 16
          (armB W 56 2 false prodIn encIn vb 16)).2) := by
  simp only [sGroupArms, lxN_tail, show (14 == 0) = false from rfl, show 4 * 14 = 56 from rfl]
  rw [show (256 : Nat) = 16 + 240 from rfl, armsM_append, armsM_eq _ _ _ _ _ _ _ _ _ 16 0 _ (by norm_num),
    armsT_snd]
  simp only [armB]

theorem sGroupArms_tail_ge (W : WotsT) (prodIn encIn : V) (vb : Nat) :
    armB W 56 2 false prodIn encIn vb (4 ^ 2) ≤ (sGroupArms W 14 prodIn encIn vb).2 := by
  rw [sGroupArms_tail, show (4 : Nat) ^ 2 = 16 by norm_num]
  dsimp only
  exact armsM_snd_ge W (slotsT W false vb) 56 2 false prodIn encIn (prodT W false 2 vb) (encT W false 2 vb)
    240 16 _

theorem sGroupArms_getElem (W : WotsT) {p k : Nat} (hp : p ≤ 14) (hk : k < 4 ^ lxN p) (prodIn encIn : V)
    (vb : Nat) :
    ∃ h : k < (sGroupArms W p prodIn encIn vb).1.length, (sGroupArms W p prodIn encIn vb).1[k] =
      (armT W (slotsT W (p == 0) vb) (4 * p) (lxN p) (p == 0) prodIn encIn (prodT W (p == 0) (lxN p) vb)
        (encT W (p == 0) (lxN p) vb) k (armB W (4 * p) (lxN p) (p == 0) prodIn encIn vb k)).1 := by
  rcases Nat.lt_or_ge p 14 with hp' | hp'
  · have hn := lxN_four hp'
    rw [hn] at hk ⊢
    have hl : k < (sGroupArms W p prodIn encIn vb).1.length := by
      rw [sGroupArms_four W hp', armsT_length]; norm_num at hk; omega
    refine ⟨hl, ?_⟩
    simp only [sGroupArms_four W hp']
    rw [armsT_getElem]
    simp only [Nat.zero_add]
    rfl
  · have hp14 : p = 14 := by omega
    subst hp14
    rw [lxN_tail] at hk ⊢
    have hl : k < (sGroupArms W 14 prodIn encIn vb).1.length := by
      simp only [sGroupArms, armsM_length]; norm_num at hk; omega
    refine ⟨hl, ?_⟩
    simp only [sGroupArms_tail]
    have hk16 : k < (armsT W (slotsT W false vb) 56 2 false prodIn encIn (prodT W false 2 vb)
        (encT W false 2 vb) 16 0 (vb + 6)).1.length := by rw [armsT_length]; norm_num at hk; omega
    rw [List.getElem_append_left hk16, armsT_getElem]
    simp only [Nat.zero_add]
    rfl

end
end LeanVM.Guest.B1.Sig
