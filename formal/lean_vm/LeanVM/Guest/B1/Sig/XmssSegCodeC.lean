/-
  LeanVM.Guest.B1.Sig.XmssSegCodeC

  The codeword of leanXMSS's check inline in `__loop2` completes: its `15` digit words hinted at
  the honest digits, their range checks, the `15` dispatches back to back, the digest's first cell
  their encoding and the target their sum.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegCwC
public import LeanVM.Guest.B1.Sig.XmssSegArms
public import LeanVM.Guest.B1.Sig.XmssBound

/-!
# The codeword in `__loop2`, complete

* `armM_c` … `sCodewordT_c`, `sSt_c`, `sStart_c`, `sTip_c`: the codeword with `sW` is the one with
  the clamped step `sWc` (the chains `< 58`, the steps `< 3`, the powers `≤ 12` it uses);
* `sgState_eq_sSt`: the groups' state, as the soundness proof names it;
* `armsM_numBelow`, `sGroupArms_numBelow`: a dispatch's values are numbered below its end (the
  tail's arms `≥ 16` are `armT`'s values or fewer);
* `sGroups_complete`: the dispatches complete in sequence, each by the arm of its honest digits;
* `sCodewordT_complete`: the codeword completes.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The clamped step -/

section clamp

variable (layer b : Nat)

theorem armM_c (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool) (prodIn encIn prodOut encOut : V)
    (k b' : Nat) (hn : first + n ≤ 58) (hd : n ≤ 4) :
    armM (sW layer b) slots first n fold prodIn encIn prodOut encOut k b' =
      armM (sWc layer b) slots first n fold prodIn encIn prodOut encOut k b' := by
  have h := sW_weq layer b
  have hp := sW_power layer b (j := digitSum k n) (by have := lx_digitSum_le k n; omega)
  have he : (sW layer b).enc = (sWc layer b).enc := rfl
  simp only [armM, h.size, hp, he]
  rw [walksT_weq h slots first k _ n 0 _ (by omega)]

theorem armsM_c (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool) (prodIn encIn prodOut encOut : V)
    (hn : first + n ≤ 58) (hd : n ≤ 4) : ∀ m k b',
    armsM (sW layer b) slots first n fold prodIn encIn prodOut encOut m k b' =
      armsM (sWc layer b) slots first n fold prodIn encIn prodOut encOut m k b'
  | 0, _, _ => rfl
  | m + 1, k, b' => by
      simp only [armsM]
      rw [armM_c layer b slots first n fold prodIn encIn prodOut encOut k b' hn hd,
        armsM_c slots first n fold prodIn encIn prodOut encOut hn hd m (k + 1)]

theorem armBaseM_c (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool) (prodIn encIn prodOut encOut : V)
    (hn : first + n ≤ 58) (hd : n ≤ 4) : ∀ k j b',
    armBaseM (sW layer b) slots first n fold prodIn encIn prodOut encOut k j b' =
      armBaseM (sWc layer b) slots first n fold prodIn encIn prodOut encOut k j b'
  | _, 0, _ => rfl
  | k, j + 1, b' => by
      simp only [armBaseM]
      rw [armM_c layer b slots first n fold prodIn encIn prodOut encOut k b' hn hd,
        armBaseM_c slots first n fold prodIn encIn prodOut encOut hn hd (k + 1) j]

theorem lxN_le (p : Nat) : lxN p ≤ 4 := by unfold lxN; split <;> omega

theorem lxN_fit {p : Nat} (hp : p ≤ 14) : 4 * p + lxN p ≤ 58 := by unfold lxN; split <;> omega

theorem sGroupArms_c {p : Nat} (hp : p ≤ 14) (prodIn encIn : V) (vb : Nat) :
    sGroupArms (sW layer b) p prodIn encIn vb = sGroupArms (sWc layer b) p prodIn encIn vb := by
  have h := sW_weq layer b
  unfold sGroupArms
  rw [slotsT_weq h, prodT_weq h, encT_weq h, armsM_c layer b _ _ _ _ _ _ _ _ (lxN_fit hp) (lxN_le p)]

theorem sGroupsT_c (dg : Nat) : ∀ m p prod enc vb, p + m ≤ 15 →
    sGroupsT (sW layer b) dg m p prod enc vb = sGroupsT (sWc layer b) dg m p prod enc vb
  | 0, _, _, _, _, _ => rfl
  | m + 1, p, prod, enc, vb, hm => by
      have h := sW_weq layer b
      simp only [sGroupsT]
      rw [sGroupArms_c layer b (by omega), prodT_weq h, encT_weq h, slotsT_weq h,
        sGroupsT_c dg m (p + 1) _ _ _ (by omega)]

theorem sCodewordT_c (target : E) (d0 : V) (dg : Nat) :
    sCodewordT (sW layer b) target d0 dg = sCodewordT (sWc layer b) target d0 dg := by
  unfold sCodewordT
  rw [sGroupsT_c layer b dg 15 0 _ _ _ (by omega)]

theorem sSt_c (vb0 : Nat) : ∀ p, p ≤ 15 → sSt (sW layer b) vb0 p = sSt (sWc layer b) vb0 p
  | 0, _ => rfl
  | p + 1, hp => by
      have h := sW_weq layer b
      simp only [sSt]
      rw [sSt_c vb0 p (by omega), prodT_weq h, encT_weq h, sGroupArms_c layer b (by omega)]

theorem sStart_c (σ : Val) (dg vb0 : Nat) {i : Nat} (hi : i < 58) :
    sStart (sW layer b) σ dg vb0 i = sStart (sWc layer b) σ dg vb0 i := by
  have h := sW_weq layer b
  have hp : i / 4 ≤ 14 := by omega
  unfold sStart
  rw [sSt_c layer b vb0 (i / 4) (by omega), armStart_weq h, slotsT_weq h, prodT_weq h, encT_weq h,
    armBaseM_c layer b _ _ _ _ _ _ _ _ (lxN_fit hp) (lxN_le _)]

theorem sTip_c (vb0 : Nat) {i : Nat} (hi : i < 58) : sTip (sW layer b) vb0 i = sTip (sWc layer b) vb0 i := by
  unfold sTip
  rw [sSt_c layer b vb0 (i / 4) (by omega), slotsT_weq (sW_weq layer b)]

end clamp

theorem sgState_eq_sSt (W : WotsT) (v0 : Nat) : ∀ p, sgState W v0 p = sSt W v0 p
  | 0 => rfl
  | p + 1 => by simp only [sgState, sSt, sgState_eq_sSt W v0 p]

/-! ## A dispatch's values, numbered below its end -/

/-- The arms of a group's dispatch are numbered below its end. -/
theorem groupArmsT_numBelow {W : WotsT} {B : Nat} (hW : StepShape W B) {first n : Nat} {fold : Bool}
    {prodIn encIn : V} {b : Nat} (hB : B ≤ b + 6) (hpi : NBv (b + 6) prodIn) (hei : NBv (b + 6) encIn)
    (hpw : ∀ j, NBv (b + 6) (W.power j)) :
    NumBelow (armB W first n fold prodIn encIn b (4 ^ n))
      (Stmt.valsArms (groupArmsT W first n fold prodIn encIn b).1) := by
  have h := groupD_numBelow (pre := []) (d := b) (first := first) (n := n) (fold := fold) hW hB le_rfl
    (.nil _) hpi hei (fun _ _ => hpw _)
  have hend : (groupD W first n fold prodIn encIn b [] b).2 = armB W first n fold prodIn encIn b (4 ^ n) := by
    simp only [groupD, groupArmsT]; rw [armsT_snd]; rfl
  rw [hend] at h
  intro v hv
  refine h v (mem_valsList_of_mem (s := .match_ (.n b) (groupArmsT W first n fold prodIn encIn b).1)
    (by simp [groupD]) (List.mem_cons_of_mem _ hv))

theorem armM_snd_pos (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat)
    (prodIn encIn prodOut encOut : V) {k : Nat} (hk : k ≠ 0) (a : Nat) :
    (armM W slots first n false prodIn encIn prodOut encOut k a).2 =
      if k % 4 ^ n = 0 then walkBase W.size k 0 n a else walkBase W.size k 0 n a + 1 := by
  unfold armM
  by_cases h : k % 4 ^ n = 0 <;> simp [h, hk, walksT_snd]

theorem armM_snd_gt (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat)
    (prodIn encIn prodOut encOut : V) {k : Nat} (hk : k ≠ 0) (hn : 1 ≤ n) (a : Nat) :
    a + 1 ≤ (armM W slots first n false prodIn encIn prodOut encOut k a).2 := by
  rw [armM_snd_pos W slots first n prodIn encIn prodOut encOut hk a, walkBase_eq]
  split
  · rename_i h0
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h4 : k % 4 = 0 := by
      have : k % 4 ^ (n' + 1) % 4 = k % 4 :=
        Nat.mod_mod_of_dvd k (Dvd.intro_left (4 ^ n') (by rw [pow_succ]))
      rw [← this, h0]
    have hw : walkSum W.size k 0 (n' + 1) = walkSize W.size (dig k 0) + walkSum W.size k 1 n' := rfl
    have hd : dig k 0 = 0 := by simp [dig, h4]
    rw [hw, hd, walkSize]
    simp only [show ¬ (0 = 3) from by omega, ↓reduceIte]
    omega
  · omega

theorem armM_vals_sub (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) {k : Nat} (hk : k ≠ 0) (a : Nat) {x : V}
    (hx : x ∈ Stmt.valsList (armM W slots first n fold prodIn encIn prodOut encOut k a).1) :
    x ∈ Stmt.valsList (armT W slots first n fold prodIn encIn prodOut encOut k a).1 := by
  unfold armM at hx
  unfold armT
  simp only [hk, ↓reduceIte] at hx ⊢
  split at hx <;>
    simp only [valsList_append, List.mem_append, valsList_cons, valsList_nil, List.append_nil, copyS, cst,
      addS, mulS, Stmt.vals, Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢ <;> tauto

/-- **A later arm's values**, `fold = false`, are numbered below any bound past its walks. -/
theorem armT_numBelow_pos {W : WotsT} {B : Nat} (hW : StepShape W B) {first n : Nat} {prodIn encIn : V}
    {vb k a E : Nat} (hB : B ≤ vb + 6) (hk : k ≠ 0)
    (ha : groupStart false vb + chainStride W * n + 2 ≤ a) (hE : walkBase W.size k 0 n a + 1 ≤ E)
    (hpi : NBv (vb + 6) prodIn) (hei : NBv (vb + 6) encIn) (hpw : NBv (vb + 6) (W.power (digitSum k n))) :
    NumBelow E (Stmt.valsList (armT W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb)
      (encT W false n vb) k a).1) := by
  have hW' := StepShape.mono hW hB
  have hgs : vb + 6 ≤ groupStart false vb := by simp [groupStart]
  have hwb := walkBase_le W.size k a (Nat.zero_le n)
  simp only [walkBase] at hwb
  obtain ⟨l1, l2, l3⟩ := armPos_lay W false (B := vb + 6) (n := n) (k := k) (a := a) le_rfl ha
  have hP1 : ∀ x, NBv (vb + 6) x → ∃ j < E, x = .n j := by
    rintro x ⟨j, hj, rfl⟩; exact ⟨j, by omega, rfl⟩
  refine armT_vals hW' (by simpa [hk] using l1) (by simpa [hk] using l2) hP1 (fun x hx => ?_)
    ⟨?_, ?_, ?_, hP1 _ hpi, hP1 _ hei, hP1 _ hpw, ?_⟩
  · obtain ⟨j, rfl, h⟩ := l3 x (by simpa [hk] using hx)
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rcases h with h | h
    · exact ⟨j, by omega, rfl⟩
    · exact ⟨j, by omega, rfl⟩
  · exact ⟨_, by omega, rfl⟩
  · exact ⟨_, by omega, rfl⟩
  · exact ⟨_, by omega, rfl⟩
  · rw [walksT_snd]
    exact ⟨_, by simpa using hE, rfl⟩

/-- **The arms `k ..< k + m` of a dispatch, `fold = false`, past arm `0`**, ending at a multiple of
`4^n`, are numbered below their end. -/
theorem armsM_numBelow {W : WotsT} {B : Nat} (hW : StepShape W B) {first n : Nat} {prodIn encIn : V}
    {vb : Nat} (hn : 1 ≤ n) (hB : B ≤ vb + 6) (hpi : NBv (vb + 6) prodIn) (hei : NBv (vb + 6) encIn)
    (hpw : ∀ j, NBv (vb + 6) (W.power j)) : ∀ m k a, k ≠ 0 → (k + m) % 4 ^ n = 0 →
    groupStart false vb + chainStride W * n + 2 ≤ a →
    NumBelow (armsM W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb) (encT W false n vb)
      m k a).2 (Stmt.valsArms (armsM W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb)
        (encT W false n vb) m k a).1)
  | 0, _, _, _, _, _ => NumBelow.nil _
  | m + 1, k, a, hk, hm, ha => by
      have hN : 2 ≤ 4 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
      simp only [armsM, hk, ↓reduceIte, Stmt.valsArms]
      set a' := (armM W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb) (encT W false n vb)
        k a).2 with ha'
      have hge := armM_snd_ge W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb)
        (encT W false n vb) k a
      have hrest := armsM_snd_ge W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb)
        (encT W false n vb) m (k + 1) a'
      have hsnd := armM_snd_pos W (slotsT W false vb) first n prodIn encIn (prodT W false n vb)
        (encT W false n vb) hk a
      -- arm `k`'s walks end below the rest's end
      have hE : walkBase W.size k 0 n a + 1 ≤ (armsM W (slotsT W false vb) first n false prodIn encIn
          (prodT W false n vb) (encT W false n vb) m (k + 1) a').2 := by
        by_cases h0 : k % 4 ^ n = 0
        · simp only [h0, ↓reduceIte] at hsnd
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
            refine ⟨m - 1, ?_⟩
            rcases Nat.eq_zero_or_pos m with h | h
            · subst h
              exfalso
              rw [Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)] at hm
              omega
            · omega
          simp only [armsM]
          have h1 := armM_snd_gt W (slotsT W false vb) first n prodIn encIn (prodT W false n vb)
            (encT W false n vb) (show k + 1 ≠ 0 by omega) hn a'
          have h2 := armsM_snd_ge W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb)
            (encT W false n vb) m' (k + 1 + 1)
            (if k + 1 = 0 then (armM W (slotsT W false vb) first n false prodIn encIn (prodT W false n vb)
              (encT W false n vb) (k + 1) a').2 + 2 else (armM W (slotsT W false vb) first n false prodIn encIn
                (prodT W false n vb) (encT W false n vb) (k + 1) a').2)
          simp only [show k + 1 ≠ 0 by omega, ↓reduceIte] at h2 ⊢
          omega
        · simp only [h0, ↓reduceIte] at hsnd
          omega
      refine NumBelow.append ?_ (armsM_numBelow hW hn hB hpi hei hpw m (k + 1) a' (by omega)
        (by rw [show k + 1 + m = k + (m + 1) by omega]; exact hm) (by omega))
      intro x hx
      exact armT_numBelow_pos hW hB hk ha hE hpi hei (hpw _) x
        (armM_vals_sub _ _ _ _ _ _ _ _ _ hk a hx)

theorem valsArms_append : ∀ (xs ys : List (List Stmt)),
    Stmt.valsArms (xs ++ ys) = Stmt.valsArms xs ++ Stmt.valsArms ys
  | [], _ => rfl
  | x :: xs, ys => by simp only [List.cons_append, Stmt.valsArms, valsArms_append xs ys, List.append_assoc]

/-- A group's arms end past `armB … (4^n)`. -/
theorem sGroupArms_end_ge (W : WotsT) {p : Nat} (hp : p ≤ 14) (prodIn encIn : V) (vb : Nat) :
    armB W (4 * p) (lxN p) (p == 0) prodIn encIn vb (4 ^ lxN p) ≤ (sGroupArms W p prodIn encIn vb).2 := by
  rcases Nat.lt_or_ge p 14 with hp' | hp'
  · rw [sGroupArms_four_snd W hp', lxN_four hp']
  · obtain rfl : p = 14 := by omega
    exact sGroupArms_tail_ge W prodIn encIn vb

theorem sGroupArms_end_one (W : WotsT) {p : Nat} (hp : p ≤ 14) (prodIn encIn : V) (vb : Nat) :
    groupStart (p == 0) vb + chainStride W * lxN p + 2 ≤ (sGroupArms W p prodIn encIn vb).2 := by
  rw [← armB_one W (4 * p) (lxN p) (p == 0) prodIn encIn vb]
  exact le_trans (armB_mono W _ _ _ _ _ _ (Nat.one_le_two_pow.trans (Nat.pow_le_pow_left (by norm_num) _)))
    (sGroupArms_end_ge W hp prodIn encIn vb)

/-- **A group's dispatch is numbered below its end.** -/
theorem sGroupMatch_numBelow {W : WotsT} {B : Nat} (hW : StepShape W B) {p vb d : Nat} {prodIn encIn : V}
    (hp : p ≤ 14) (hB : B ≤ vb + 6) (hd : d < vb + 6) (hpi : NBv (vb + 6) prodIn) (hei : NBv (vb + 6) encIn)
    (hpw : ∀ j, NBv (vb + 6) (W.power j)) :
    NumBelow (sGroupArms W p prodIn encIn vb).2
      (Stmt.valsList [.match_ (.n d) (sGroupArms W p prodIn encIn vb).1]) := by
  have hge := sGroupArms_end_one W hp prodIn encIn vb
  have hgs : vb + 6 ≤ groupStart (p == 0) vb := by rw [groupStart_eq]; split <;> omega
  simp only [valsList_cons, valsList_nil, List.append_nil, Stmt.vals]
  refine NumBelow.cons ⟨d, by omega, rfl⟩ ?_
  rcases Nat.lt_or_ge p 14 with hp' | hp'
  · have h := groupArmsT_numBelow (first := 4 * p) (n := 4) (fold := p == 0) hW hB hpi hei hpw
    rw [sGroupArms_four_snd W hp', sGroupArms_four W hp']
    simpa only [groupArmsT, show (4 : Nat) ^ 4 = 256 by norm_num] using h
  · obtain rfl : p = 14 := by omega
    have h1 := groupArmsT_numBelow (first := 56) (n := 2) (fold := false) hW hB hpi hei hpw
    have h2 := armsM_numBelow (first := 56) (n := 2) hW (by norm_num) hB hpi hei hpw 240 16
      (armB W 56 2 false prodIn encIn vb 16) (by norm_num) (by norm_num)
      (armB_pos W 56 2 false prodIn encIn vb (by norm_num))
    have h1' : NumBelow (armB W 56 2 false prodIn encIn vb 16) (Stmt.valsArms (armsT W (slotsT W false vb) 56 2
        false prodIn encIn (prodT W false 2 vb) (encT W false 2 vb) 16 0 (vb + 6)).1) := by
      simpa only [groupArmsT, show (4 : Nat) ^ 2 = 16 by norm_num] using h1
    have hle := armsM_snd_ge W (slotsT W false vb) 56 2 false prodIn encIn (prodT W false 2 vb)
      (encT W false 2 vb) 240 16 (armB W 56 2 false prodIn encIn vb 16)
    rw [sGroupArms_tail]
    dsimp only
    rw [valsArms_append]
    exact (h1'.mono hle).append h2

/-! ## The groups' state -/

theorem sgState_step (W : WotsT) (v0 : Nat) {p : Nat} (hp : p ≤ 14) :
    (sgState W v0 p).2.2 + 6 + (if p == 0 then 1 else 0) + chainStride W * lxN p + 2 ≤
      (sgState W v0 (p + 1)).2.2 + 6 := by
  rw [sgState_succ_end]
  have := sGroupArms_end_one W hp (sgState W v0 p).1 (sgState W v0 p).2.1 (sgState W v0 p).2.2
  rw [groupStart_eq] at this
  omega

theorem sgState_mono (W : WotsT) (v0 p : Nat) : ∀ m, p + m ≤ 15 → (sgState W v0 p).2.2 ≤ (sgState W v0 (p + m)).2.2
  | 0, _ => le_rfl
  | m + 1, h => by
      have := sgState_mono W v0 p m (by omega)
      have := sgState_step W v0 (p := p + m) (by omega)
      rw [show p + (m + 1) = p + m + 1 by omega]
      omega

theorem sgState_in (W : WotsT) (v0 : Nat) : ∀ p, p ≤ 15 →
    NBv ((sgState W v0 p).2.2 + 6) (sgState W v0 p).1 ∧ NBv ((sgState W v0 p).2.2 + 6) (sgState W v0 p).2.1
  | 0, _ => ⟨⟨0, by simp [sgState], rfl⟩, ⟨0, by simp [sgState], rfl⟩⟩
  | p + 1, hp => by
      have := sgState_step W v0 (p := p) (by omega)
      have hs : ∀ x, x + 6 + (if p == 0 then 1 else 0) + chainStride W * lxN p + 2 ≤
          (sgState W v0 (p + 1)).2.2 + 6 → x + 6 + (if p == 0 then 1 else 0) + chainStride W * lxN p + 1 <
          (sgState W v0 (p + 1)).2.2 + 6 := fun x h => by omega
      have h2 := hs _ this
      refine ⟨⟨_, ?_, rfl⟩, ⟨_, ?_, rfl⟩⟩ <;> simp only [groupStart_eq] <;> omega

/-! ## The dispatches, in sequence -/

section groups

variable {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B) (hc : GoodStable B good)
  (hWa : StepAtoms W) {dg v0 : Nat} (hB : B ≤ v0 + 6) (hdg : dg + 15 ≤ v0 + 6) (hpw : ∀ j, NBv B (W.power j))
  (K : Nat → Nat) (hK : ∀ p < 15, K p < 4 ^ lxN p) (vals : Nat → E)
include hW hc hWa hB hdg hpw hK

/-- Chain `4q + t`'s start, in the arm of group `q`'s digits. -/
def sgPos (W : WotsT) (v0 : Nat) (K : Nat → Nat) (q t : Nat) : V :=
  grpPos W (4 * q) (lxN q) (q == 0) (sgState W v0 q).1 (sgState W v0 q).2.1 (sgState W v0 q).2.2 (K q) t

omit hW hc hWa hB hdg hpw hK in
theorem sgPos_lt {W : WotsT} {v0 : Nat} {K : Nat → Nat} {q t : Nat} (hq : q ≤ 14) (hk : K q < 4 ^ lxN q)
    (ht : t < lxN q) : ∃ j, sgPos W v0 K q t = .n j ∧ (sgState W v0 q).2.2 + 6 ≤ j ∧
      j < (sgState W v0 (q + 1)).2.2 + 6 := by
  obtain ⟨j, e, h1, h2, -⟩ := grpPos_spec W (4 * q) (lxN q) (q == 0) (sgState W v0 q).1 (sgState W v0 q).2.1
    (sgState W v0 q).2.2 (K q) t hk ht
  have := sGroupArms_end_ge W hq (sgState W v0 q).1 (sgState W v0 q).2.1 (sgState W v0 q).2.2
  rw [← sgState_succ_end] at this
  exact ⟨j, e, h1, by omega⟩

omit hW hc hWa hB hdg hpw hK in
theorem sgTip_lt (W : WotsT) (v0 : Nat) {q t : Nat} (hq : q ≤ 14) (ht : t < lxN q) :
    (sgState W v0 q).2.2 + 6 ≤ slotsT W (q == 0) (sgState W v0 q).2.2 t 2 ∧
      slotsT W (q == 0) (sgState W v0 q).2.2 t 2 < (sgState W v0 (q + 1)).2.2 + 6 := by
  have hs := slot_bounds W (q == 0) (sgState W v0 q).2.2 t 2 (by norm_num)
  have h3 : chainStride W * (t + 1) ≤ chainStride W * lxN q := Nat.mul_le_mul_left _ (by omega)
  have := sgState_step W v0 hq
  rw [groupStart_eq] at hs
  constructor <;> split at hs <;> simp_all <;> omega

/-- What the dispatches `p ..< p + m` establish: the step's reads, and per group its chains' starts
loaded. -/
def SgPost (W : WotsT) (good : Val → Prop) (v0 : Nat) (K : Nat → Nat) (vals : Nat → E) (p m : Nat) (σ : Val) :
    Prop :=
  good σ ∧ ∀ q, p ≤ q → q < p + m → ∀ t < lxN q, σ (sgPos W v0 K q t) = vals (4 * q + t)

/-- **The dispatches `p ..< p + m` complete**, each by the arm of its digits `K q`, the digit words
loaded. -/
theorem sGroups_complete : ∀ m p, p + m ≤ 15 → ∀ σ, good σ →
    (∀ q < 15, σ (.n (dg + q)) = ofK (addressOfIndex (K q))) →
    Completes C rd ((sgState W v0 p).2.2 + 6) ((sgState W v0 (p + m)).2.2 + 6)
      ((List.range m).map fun q => sgMatch W dg v0 (p + q)) σ (SgPost W good v0 K vals p m)
  | 0, p, _, σ, hg, _ => ⟨σ, Ext.refl _ _ _, ⟨hg, fun q h1 h2 => by omega⟩, fun _ _ hn => hn⟩
  | m + 1, p, hpm, σ, hg, hx => by
      have hvp := sgState_mono W v0 0 p (by omega)
      simp only [Nat.zero_add, sgState] at hvp
      have hBp : B ≤ (sgState W v0 p).2.2 + 6 := by omega
      obtain ⟨hpi, hei⟩ := sgState_in W v0 p (by omega)
      have hpwp : ∀ j, NBv ((sgState W v0 p).2.2 + 6) (W.power j) := fun j => (hpw j).mono' hBp
      have hkp := hK p (by omega)
      obtain ⟨hkl, harm⟩ := sGroupArms_getElem W (p := p) (by omega) hkp (sgState W v0 p).1 (sgState W v0 p).2.1
        (sgState W v0 p).2.2
      have hend := sgState_succ_end W v0 p
      have hE := sGroupArms_end_ge W (p := p) (by omega) (sgState W v0 p).1 (sgState W v0 p).2.1
        (sgState W v0 p).2.2
      have hhead := matchArm_complete (C := C) (rd := rd) (hW.mono hBp) (hc.mono hBp) hWa
        (first := 4 * p) (Ee := (sgState W v0 (p + 1)).2.2 + 6) (d := dg + p) hkp le_rfl hpi hei (hpwp _) hkl harm
        (by rw [hend]; exact hE) (by omega) (fun t => vals (4 * p + t)) σ hg (hx p (by omega))
      have hnb := sGroupMatch_numBelow hW (p := p) (d := dg + p) (by omega) hBp (by omega) hpi hei hpwp
      rw [← hend] at hnb
      have hl : (List.range (m + 1)).map (fun q => sgMatch W dg v0 (p + q)) =
          [sgMatch W dg v0 p] ++ (List.range m).map (fun q => sgMatch W dg v0 (p + 1 + q)) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero, List.singleton_append]
        congr 1
        exact List.map_congr_left fun q _ => by
          simp only [Function.comp_apply, show p + (q + 1) = p + 1 + q by omega]
      have hm1 := sgState_mono W v0 (p + 1) m (by omega)
      have hp1 := sgState_mono W v0 p 1 (by omega)
      rw [hl, show p + (m + 1) = p + 1 + m by omega]
      refine Completes.append (m := (sgState W v0 (p + 1)).2.2 + 6) (by omega) (by omega) hnb hhead
        (fun σ1 he1 hq1 => ?_)
      have hx1 : ∀ q < 15, σ1 (.n (dg + q)) = ofK (addressOfIndex (K q)) := fun q hq => by
        rw [he1.apply (Or.inl (by omega))]; exact hx q hq
      have ih := sGroups_complete m (p + 1) (by omega) σ1 hq1.1 hx1
      refine (ih.keep (Q := fun σ => ∀ t < lxN p, σ (sgPos W v0 K p t) = vals (4 * p + t))
        (Q' := fun σ => ∀ t < lxN p, σ (sgPos W v0 K p t) = vals (4 * p + t))
        hq1.2.1 (fun σ' he' hq t ht => ?_)).mono le_rfl le_rfl
        (fun σ' ⟨⟨hg', hr⟩, hq'⟩ => ⟨hg', fun q h1 h2 => ?_⟩)
      · obtain ⟨j, ej, -, hj⟩ := sgPos_lt (W := W) (v0 := v0) (K := K) (q := p) (by omega) hkp ht
        rw [ej, he'.apply (Or.inl hj), ← ej]
        exact hq t ht
      · rcases Nat.lt_or_ge q (p + 1) with hq | hq
        · obtain rfl : q = p := by omega
          exact hq'
        · exact hr q hq (by omega)

omit hc hWa hK in
theorem sGroups_numBelow : ∀ m p, p + m ≤ 15 →
    NumBelow ((sgState W v0 (p + m)).2.2 + 6)
      (Stmt.valsList ((List.range m).map fun q => sgMatch W dg v0 (p + q)))
  | 0, _, _ => NumBelow.nil _
  | m + 1, p, hpm => by
      have hvp := sgState_mono W v0 0 p (by omega)
      simp only [Nat.zero_add, sgState] at hvp
      have hBp : B ≤ (sgState W v0 p).2.2 + 6 := by omega
      obtain ⟨hpi, hei⟩ := sgState_in W v0 p (by omega)
      have hnb := sGroupMatch_numBelow hW (p := p) (d := dg + p) (by omega) hBp (by omega) hpi hei
        (fun j => (hpw j).mono' hBp)
      rw [← sgState_succ_end] at hnb
      have hm1 := sgState_mono W v0 (p + 1) m (by omega)
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero, valsList_cons]
      have ih := sGroups_numBelow m (p + 1) (by omega)
      rw [show p + 1 + m = p + (m + 1) by omega] at ih hm1
      have h' : NumBelow ((sgState W v0 (p + (m + 1))).2.2 + 6) (sgMatch W dg v0 p).vals := by
        have := hnb.mono (show (sgState W v0 (p + 1)).2.2 + 6 ≤ (sgState W v0 (p + (m + 1))).2.2 + 6 by omega)
        rwa [valsList_cons, valsList_nil, List.append_nil] at this
      refine h'.append ?_
      refine (List.map_congr_left fun q _ => ?_) ▸ ih
      simp only [Function.comp_apply, show p + 1 + q = p + (q + 1) by omega]

end groups

/-! ## The digit words' range checks -/

theorem digitChecks_numBelow {dg : Nat} : ∀ m, NumBelow (dg + 15 + 4 * m)
    (Stmt.valsList ((List.range m).flatMap fun p =>
      rangeS (.n (dg + p)) (if p < 14 then bound255 else word (2 ^ 15) 0) (dg + 15 + 4 * p)))
  | 0 => NumBelow.nil _
  | m + 1 => by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, valsList_append]
      refine ((digitChecks_numBelow m).mono (by omega)).append ?_
      intro v hv
      revert hv
      simp only [rangeS, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, by omega, rfl⟩

theorem digitChecks_complete {dg : Nat} {K : Nat → Nat} (hm : MemOK rd 256) (hK : ∀ p < 15, K p < 4 ^ lxN p) :
    ∀ m, m ≤ 15 → ∀ σ : Val, (∀ q < 15, σ (.n (dg + q)) = ofK (addressOfIndex (K q))) →
    Completes C rd (dg + 15) (dg + 15 + 4 * m) ((List.range m).flatMap fun p =>
      rangeS (.n (dg + p)) (if p < 14 then bound255 else word (2 ^ 15) 0) (dg + 15 + 4 * p)) σ
      (fun _ => True)
  | 0, _, σ, _ => ⟨σ, Ext.refl _ _ _, trivial, fun _ _ hn => hn⟩
  | m + 1, hm15, σ, hx => by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      have hnb := digitChecks_numBelow (dg := dg) m
      refine Completes.append (m := dg + 15 + 4 * m) (by omega) (by omega) hnb
        (digitChecks_complete hm hK m (by omega) σ hx) (fun σ1 he1 _ => ?_)
      have hx1 : σ1 (.n (dg + m)) = ofK (addressOfIndex (K m)) := by
        rw [he1.apply (Or.inl (by omega))]; exact hx m (by omega)
      rw [show dg + 15 + 4 * (m + 1) = dg + 15 + 4 * m + 4 by omega]
      have hkm := hK m (by omega)
      by_cases h14 : m < 14
      · simp only [h14, ↓reduceIte]
        rw [bound255_eq]
        have hk : K m < 256 := by rw [lxN_four h14] at hkm; norm_num at hkm; exact hkm
        exact rangeS_complete (K := 256) hm le_rfl hk σ1 (.n (dg + m)) ⟨dg + m, by omega, rfl⟩ hx1
      · simp only [h14, ↓reduceIte]
        obtain rfl : m = 14 := by omega
        rw [lxN_tail] at hkm
        rw [word_two_pow_eq (by norm_num)]
        exact rangeS_complete (K := 16) hm (by norm_num) (by norm_num at hkm; exact hkm) σ1 (.n (dg + 14))
          ⟨dg + 14, by omega, rfl⟩ hx1

/-! ## The codeword's values -/

/-- **The product and the encoding the dispatches fold**, from the arms they take. -/
theorem sGroups_vals {σ : Val} {W : WotsT} {f : Nat → Nat → E → E} (hs : StepSound rd σ W f)
    (hpow : ∀ s < 13, σ (W.power s) = gen ^ s) {dg vb0 : Nat} (hg : ∀ p < 15, GroupOKM rd σ W dg vb0 p)
    (hE : ∀ first n k, W.enc first n k = k * 4 ^ first := by intros; rfl) :
    σ (sSt W vb0 15).1 = gen ^ (∑ i ∈ Finset.range 58, lxDigit (sK σ dg) i) ∧
      σ (sSt W vb0 15).2.1 = lit (∑ i ∈ Finset.range 58, lxDigit (sK σ dg) i * 4 ^ i) := by
  set K := sK σ dg with hKdef
  have hK : ∀ p < 15, K p < 256 ∧ AtomsHold rd σ (sArm W vb0 p (K p)).1 := by
    intro p hp
    obtain ⟨k, hk, hx, ha⟩ := hg p hp
    have e : K p = k := logG_eq hk (by norm_num) hx
    rw [e]
    exact ⟨hk, ha⟩
  have harm : ∀ p < 15, ArmOKM W f σ (slotsT W (p == 0) (sSt W vb0 p).2.2) (4 * p) (lxN p)
      (p == 0) (sSt W vb0 p).1 (sSt W vb0 p).2.1
      (prodT W (p == 0) (lxN p) (sSt W vb0 p).2.2)
      (encT W (p == 0) (lxN p) (sSt W vb0 p).2.2) (K p)
      (armStart W (slotsT W (p == 0) (sSt W vb0 p).2.2) (p == 0) (K p)
        (armBaseM W (slotsT W (p == 0) (sSt W vb0 p).2.2) (4 * p) (lxN p) (p == 0)
          (sSt W vb0 p).1 (sSt W vb0 p).2.1
          (prodT W (p == 0) (lxN p) (sSt W vb0 p).2.2)
          (encT W (p == 0) (lxN p) (sSt W vb0 p).2.2) 0 (K p) ((sSt W vb0 p).2.2 + 6))) :=
    fun p hp => armM_sound hs (hK p hp).2
  have hN : ∀ p, lxN p ≤ 4 := lxN_le
  refine ⟨?_, ?_⟩
  · have hpr : ∀ p < 15, σ (sSt W vb0 (p + 1)).1 =
        gen ^ (∑ q ∈ Finset.range (p + 1), digitSum (K q) (lxN q)) := by
      intro p hp
      have hle : ∀ q, digitSum (K q) (lxN q) < 13 := fun q => by
        have := lx_digitSum_le (K q) (lxN q); have := hN q; omega
      induction p with
      | zero =>
          have := (harm 0 (by omega)).prod
          simp only [sSt, beq_self_eq_true, ↓reduceIte, one_mul] at this ⊢
          rw [this, hpow _ (hle 0)]
          simp
      | succ p ih =>
          have := (harm (p + 1) (by omega)).prod
          simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte] at this
          show σ (prodT W (p + 1 == 0) (lxN (p + 1)) (sSt W vb0 (p + 1)).2.2) = _
          rw [this, hpow _ (hle _), Finset.sum_range_succ (n := p + 1), pow_add, ← ih (by omega)]
    rw [hpr 14 (by omega), lx_digitSum_total]
  · have hen : ∀ p < 15, σ (sSt W vb0 (p + 1)).2.1 =
        lit (∑ q ∈ Finset.range (p + 1), lxEncTerm K q) := by
      intro p hp
      induction p with
      | zero =>
          have := (harm 0 (by omega)).enc
          rw [hE] at this
          simp only [sSt, beq_self_eq_true, ↓reduceIte, zero_add] at this ⊢
          rw [this]
          simp [lxEncTerm]
      | succ p ih =>
          have := (harm (p + 1) (by omega)).enc
          rw [hE] at this
          simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte] at this
          show σ (encT W (p + 1 == 0) (lxN (p + 1)) (sSt W vb0 (p + 1)).2.2) = _
          rw [this, ih (by omega), ← lx_enc_step K hp]
          rfl
    rw [hen 14 (by omega), lx_enc_total]

theorem armBaseM_eq (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : ∀ k j b, k + j ≤ 4 ^ n →
    armBaseM W slots first n fold prodIn encIn prodOut encOut k j b =
      armBase W slots first n fold prodIn encIn prodOut encOut k j b
  | _, 0, _, _ => rfl
  | k, j + 1, b, h => by
      simp only [armBaseM, armBase]
      rw [armM_eq W slots first n fold prodIn encIn prodOut encOut b (show k < 4 ^ n by omega),
        armBaseM_eq W slots first n fold prodIn encIn prodOut encOut (k + 1) j _ (by omega)]

/-- Chain `i`'s start, read with the honest digits, is its start in the arm of those digits. -/
theorem sStart_eq_sgPos (W : WotsT) (σ : Val) {dg v0 : Nat} {K : Nat → Nat} (hK : ∀ p < 15, K p < 4 ^ lxN p)
    (hx : ∀ q < 15, σ (.n (dg + q)) = ofK (addressOfIndex (K q))) {i : Nat} (hi : i < 58) :
    sStart W σ dg v0 i = sgPos W v0 K (i / 4) (i % 4) := by
  have hq : i / 4 < 15 := by omega
  have h256 : 4 ^ lxN (i / 4) ≤ 256 := by unfold lxN; split <;> norm_num
  have hk : sK σ dg (i / 4) = K (i / 4) :=
    logG_eq (bound := 256) (lt_of_lt_of_le (hK _ hq) h256) (by norm_num) (hx _ hq)
  unfold sStart sgPos grpPos armB
  rw [hk, ← sgState_eq_sSt, armBaseM_eq _ _ _ _ _ _ _ _ _ 0 _ _ (by have := hK _ hq; omega)]

/-! ## The codeword -/

theorem sCodewordT_fst (W : WotsT) (target : E) (d0 : V) (dg : Nat) :
    (sCodewordT W target d0 dg).1 = [hintW "lx_digits" (runV dg 15)] ++ (sDigitChecks dg ++
      ([cst (dg + 75) closeLane] ++ ((List.range 15).map (fun q => sgMatch W dg (dg + 70) q) ++
        [copyS d0 (sSt W (dg + 70) 15).2.1, cst ((sSt W (dg + 70) 15).2.2 + 6) target,
          .atom (.assertEq (sSt W (dg + 70) 15).1 (.n ((sSt W (dg + 70) 15).2.2 + 6)))]))) := by
  have hgs := sGroupsT_eq W dg (dg + 70) 15 0
  simp only [Nat.zero_add] at hgs
  have hgs' : (sGroupsT W dg 15 0 (.n 0) (.n 0) (dg + 70)).2 = _ := hgs
  have hf := sGroupsT_fst W dg (dg + 70) 15 0
  simp only [Nat.zero_add] at hf
  have hf' : (sGroupsT W dg 15 0 (.n 0) (.n 0) (dg + 70)).1 = _ := hf
  unfold sCodewordT
  simp only [List.append_assoc]
  rw [hgs', hf']

theorem sCodewordT_snd (W : WotsT) (target : E) (d0 : V) (dg : Nat) :
    (sCodewordT W target d0 dg).2.1 = (sSt W (dg + 70) 15).2.2 + 6 + 1 := by
  have hgs := sGroupsT_eq W dg (dg + 70) 15 0
  simp only [Nat.zero_add] at hgs
  have hgs' : (sGroupsT W dg 15 0 (.n 0) (.n 0) (dg + 70)).2 = _ := hgs
  unfold sCodewordT
  simp only
  rw [hgs']

/-- **The codeword of `__loop2` completes**: its digit words hinted at the honest digits `K`, its
dispatches taking their arms, the chains' starts `vals` loaded, the digest's first cell `d0` the
digits' base-4 number and the target `g` to their sum. -/
theorem sCodewordT_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : GoodStable B good) (hWa : StepAtoms W) {F : Val → Nat → Nat → E → E}
    (hss : ∀ σ, good σ → StepSound rd σ W (F σ)) (hpow : ∀ σ, good σ → ∀ s < 13, σ (W.power s) = gen ^ s)
    {target : E} {d0 : V} {dg : Nat} (hB : B ≤ dg) (hpw : ∀ j, NBv B (W.power j)) (hm : MemOK rd 256)
    (K : Nat → Nat) (hK : ∀ p < 15, K p < 4 ^ lxN p) (vals : Nat → E) (hd0 : NBv dg d0) (σ : Val) (hg : good σ)
    (hsum : gen ^ (∑ i ∈ Finset.range 58, lxDigit K i) = target)
    (hd0v : σ d0 = lit (∑ i ∈ Finset.range 58, lxDigit K i * 4 ^ i))
    (hE : ∀ first n k, W.enc first n k = k * 4 ^ first := by intros; rfl) :
    Completes C rd dg (sCodewordT W target d0 dg).2.1 (sCodewordT W target d0 dg).1 σ
      (fun σ' => good σ' ∧ (∀ q < 15, σ' (.n (dg + q)) = ofK (addressOfIndex (K q))) ∧
        ∀ i < 58, σ' (sStart W σ' dg (dg + 70) i) = vals i) := by
  rw [sCodewordT_fst, sCodewordT_snd]
  have h15 : dg + 70 ≤ (sgState W (dg + 70) 15).2.2 := sgState_mono W (dg + 70) 0 15 (by omega)
  rw [← sgState_eq_sSt]
  set c := (sgState W (dg + 70) 15).2.2 + 6 with hcdef
  set σr := updRun σ dg 15 (fun p => ofK (addressOfIndex (K p))) with hσr
  have her : Ext dg (dg + 15) σ σr := updRun_ext σ dg 15 _
  have hxr : ∀ q < 15, σr (.n (dg + q)) = ofK (addressOfIndex (K q)) := fun q hq => updRun_at σ dg 15 _ hq
  have hgr : good σr := hc σ σr (fun j hj => (her.agree j (by omega))) hg
  have hd0r : σr d0 = σ d0 := by obtain ⟨j, hj, rfl⟩ := hd0; exact her.apply (Or.inl hj)
  refine Completes.reload (her.mono le_rfl (by omega)) ?_
  -- the hint
  refine Completes.append (m := dg + 15) (by omega) (by omega)
    (by
      rw [valsList_hint]
      intro v hv
      obtain ⟨j, hj, rfl⟩ := mem_runV.mp hv
      exact ⟨_, by omega, rfl⟩)
    (hintKeep_complete σr "lx_digits" (runV dg 15) dg (dg + 15)) (fun σ1 _ e1 => ?_)
  subst e1
  -- the range checks
  refine Completes.append (m := dg + 75) (by omega) (by omega) (digitChecks_numBelow (dg := dg) 15)
    (digitChecks_complete (C := C) hm hK 15 le_rfl σr hxr) (fun σ2 he2 _ => ?_)
  have hx2 : ∀ q < 15, σ2 (.n (dg + q)) = ofK (addressOfIndex (K q)) := fun q hq => by
    rw [he2.apply (Or.inl (by omega))]; exact hxr q hq
  have hg2 : good σ2 := hc σr σ2 (fun j hj => he2.agree j (by omega)) hgr
  have hd02 : σ2 d0 = σ d0 := by
    obtain ⟨j, hj, rfl⟩ := hd0; rw [he2.apply (Or.inl (by omega))]; exact hd0r
  -- the hoisted constant
  refine Completes.append (m := dg + 76) (by omega) (by omega)
    (by intro v hv; simp only [cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
      List.mem_singleton] at hv; exact ⟨_, by omega, hv⟩)
    (cst_complete σ2 (dg + 75) closeLane) (fun σ3 he3 _ => ?_)
  have hx3 : ∀ q < 15, σ3 (.n (dg + q)) = ofK (addressOfIndex (K q)) := fun q hq => by
    rw [he3.apply (Or.inl (by omega))]; exact hx2 q hq
  have hg3 : good σ3 := hc σ2 σ3 (fun j hj => he3.agree j (by omega)) hg2
  have hd03 : σ3 d0 = σ d0 := by
    obtain ⟨j, hj, rfl⟩ := hd0; rw [he3.apply (Or.inl (by omega))]; exact hd02
  -- the dispatches
  have hgc : Completes C rd (dg + 76) c ((List.range 15).map fun q => sgMatch W dg (dg + 70) q) σ3 _ :=
    (sGroups_complete (C := C) (rd := rd) hW hc hWa (dg := dg) (v0 := dg + 70) (by omega) (by omega)
      hpw K hK vals 15 0 (by omega) σ3 hg3 hx3).withHolds
  have hnbg : NumBelow c (Stmt.valsList ((List.range 15).map fun q => sgMatch W dg (dg + 70) q)) :=
    sGroups_numBelow hW (dg := dg) (v0 := dg + 70) (by omega) (by omega) hpw 15 0 (by omega)
  refine Completes.append (m := c) (by omega) (by omega) hnbg hgc (fun σ4 he4 hp4 => ?_)
  obtain ⟨⟨hg4, hpost⟩, hh4⟩ := hp4
  have hx4 : ∀ q < 15, σ4 (.n (dg + q)) = ofK (addressOfIndex (K q)) := fun q hq => by
    rw [he4.apply (Or.inl (by omega))]; exact hx3 q hq
  have hd04 : σ4 d0 = σ d0 := by
    obtain ⟨j, hj, rfl⟩ := hd0; rw [he4.apply (Or.inl (by omega))]; exact hd03
  -- the values the dispatches fold
  have hgs := sGroupsT_fst W dg (dg + 70) 15 0
  simp only [Nat.zero_add] at hgs
  have hgok := (sGroupsT_sound (rd := rd) (σ := σ4) (C := C) (kret := fun _ => True) (rest := []) hWa dg
    (dg + 70) 15 0 (by rw [List.append_nil, ← sgState_eq_sSt, hgs]; exact hh4)).2
  obtain ⟨hprod, henc⟩ := sGroups_vals (hss σ4 hg4) (hpow σ4 hg4) (fun p hp => by simpa using hgok p hp) hE
  have hk4 : ∀ i < 58, lxDigit (sK σ4 dg) i = lxDigit K i := fun i hi => by
    have h256 : 4 ^ lxN (i / 4) ≤ 256 := by unfold lxN; split <;> norm_num
    unfold lxDigit sK
    rw [logG_eq (bound := 256) (lt_of_lt_of_le (hK _ (by omega)) h256) (by norm_num) (hx4 _ (by omega))]
  rw [Finset.sum_congr rfl fun i hi => hk4 i (Finset.mem_range.mp hi), hsum, ← sgState_eq_sSt] at hprod
  rw [Finset.sum_congr rfl fun i hi => by rw [hk4 i (Finset.mem_range.mp hi)], ← hd0v, ← hd04,
    ← sgState_eq_sSt] at henc
  -- the checks
  obtain ⟨hpi15, hei15⟩ := sgState_in W (dg + 70) 15 le_rfl
  have hext : Ext c (c + 1) σ4 (upds σ4 [(c, target)]) := upds_ext σ4 _ (by simp)
  have hpv : upds σ4 [(c, target)] (sgState W (dg + 70) 15).1 = target := by
    obtain ⟨j, hj, e⟩ := hpi15; rw [e, hext.apply (Or.inl hj), ← e, hprod]
  have hev : upds σ4 [(c, target)] (sgState W (dg + 70) 15).2.1 = σ4 d0 := by
    obtain ⟨j, hj, e⟩ := hei15; rw [e, hext.apply (Or.inl hj), ← e, henc]
  have hdv : upds σ4 [(c, target)] d0 = σ4 d0 := by
    obtain ⟨j, hj, rfl⟩ := hd0; exact hext.apply (Or.inl (by omega))
  have hx5 : ∀ q < 15, upds σ4 [(c, target)] (.n (dg + q)) = ofK (addressOfIndex (K q)) := fun q hq => by
    rw [hext.apply (Or.inl (by omega))]; exact hx4 q hq
  refine completes_atoms rfl hext ⟨hc _ _ (fun j hj => hext.agree j (by omega)) hg4,
    hx5, fun i hi => ?_⟩ (fun a ha => ?_)
  · have hq : i / 4 ≤ 14 := by omega
    have ht : i % 4 < lxN (i / 4) := by unfold lxN; split <;> omega
    have hle := sgState_mono W (dg + 70) (i / 4 + 1) (15 - (i / 4 + 1)) (by omega)
    rw [show i / 4 + 1 + (15 - (i / 4 + 1)) = 15 by omega] at hle
    have hst := hpost (i / 4) (by omega) (by omega)
    rw [sStart_eq_sgPos W _ hK hx5 hi]
    obtain ⟨j, ej, -, hj⟩ := sgPos_lt (W := W) (v0 := dg + 70) (K := K) hq (hK _ (by omega)) ht
    rw [ej, hext.apply (Or.inl (by omega)), ← ej, hst _ ht, show 4 * (i / 4) + i % 4 = i by omega]
  · simp only [copyS, cst, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · show upds σ4 [(c, target)] d0 = upds σ4 [(c, target)] (sgState W (dg + 70) 15).2.1
      rw [hdv, hev]
    · exact upds_cons_self σ4 c target []
    · show upds σ4 [(c, target)] _ + upds σ4 [(c, target)] (.n c) = 0
      rw [hpv, upds_cons_self]
      exact e_add_self _

end
end LeanVM.Guest.B1.Sig
