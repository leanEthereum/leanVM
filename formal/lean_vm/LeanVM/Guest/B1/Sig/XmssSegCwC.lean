/-
  LeanVM.Guest.B1.Sig.XmssSegCwC

  The dispatches of leanXMSS's codeword inline in `main_loop2` complete: the groups' state and
  arms, an arm `k` below `4^n` being `armT`'s (`WotsChainComplete`).
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegStepC
public import LeanVM.Guest.B1.Sig.WotsChainComplete
public import LeanVM.Guest.B1.Sig.XmssSegArms

/-!
# The codeword's dispatches, complete

* `sgState`, `sgMatch`, `sGroupsT_fst`, `sgState_succ_end`: group `p`'s state and dispatch;
* `sGroupArms_four`, `sGroupArms_tail`, `sGroupArms_getElem`: a group of four's `4^4` arms are
  `armsT`'s, the tail's first `4^2`; arm `k` below `4^n` is `armT`'s from `armB … k`, as
  `matchArm_complete` (`WotsChainComplete`) takes it.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The groups' state -/

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
