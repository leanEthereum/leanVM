module

public import NativeRustcVmArm.KeccakGkr.FirstClaim.Defs
public import NativeRustcVm.Layout.RepLemmas

/-!
# `first_claim`: bytes kept

The frame's bytes a block's writes or a callee's changes miss (`written_same`, `local_same`,
`local_same_out`), the result's (`out_same`), the bit weights (`w_keep_out`); the result's bytes
and an argument's apart from the frame's locals (`out_local_apart`, `arg_local_apart'`).
-/

namespace NativeRustcVmArm.KeccakGkr.FirstClaim

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.Layout (Same)
open NativeRustcVm.KeccakGkr (claimBytes weightsBytes)

public section

/-- **Bytes a block did not write**: every write of region `r` misses the `n` bytes from `o`. -/
theorem written_same [Labels] {env : Env} {S : SState} {m m' : MachineData}
    (hm : Match env S m') (hwf : env.WF) (hd : m.dmem = env.mem0) {r : Nat} {b : BitVec 64}
    {sz o n : Nat} (hb : env.regions[r]? = some (b, sz)) (hnw : b.toNat + sz ≤ 2 ^ 64)
    (hon : o + n ≤ sz) (hS : ∀ w ∈ S.mem, w.r = r ∧ (w.off + w.n ≤ o ∨ o + n ≤ w.off)) :
    Same m.dmem m'.dmem (b + BitVec.ofNat 64 o) n := fun j hj ↦ by
  rw [hd]
  refine hm.get?_mem0 hwf fun ⟨w, hw, b', sz', hb', h1, h2⟩ ↦ ?_
  obtain ⟨hr, hdis⟩ := hS w hw
  rw [hr, hb] at hb'
  cases hb'
  have e : (b + BitVec.ofNat 64 o + BitVec.ofNat 64 j).toNat = b.toNat + (o + j) := by
    rw [NativeRustcVm.addr_add_add]; exact toNat_add_ofNat' (by omega)
  rw [e] at h1 h2
  omega

variable {inst segment lanePoint output : Array EW} {m0 st : MachineData}

/-- **Frame bytes kept** by a change in a callee's stack below the body's SP, in the written
regions and in the frame's bytes `o'` to `o' + n'` apart from them. -/
theorem local_same (hpre : FirstClaimPre inst segment lanePoint output m0) (hb : Body m0 st)
    {st' : MachineData} {o n o' n' s : Nat} (hon : o + n ≤ 1408) (hs : s < 2 ^ 63)
    (ho' : o' + n' ≤ 1408) (hdis : o + n ≤ o' ∨ o' + n' ≤ o) {R : BitVec 64 → Prop}
    (hso : SameOutside st.dmem st'.dmem R)
    (hR : ∀ p, R p → InRange (stackBelow st s) s p ∨ NativeRustcVm.InAny (wsOf m0) p ∨
      InRange (fbA m0 + BitVec.ofNat 64 o') n' p) :
    Same st.dmem st'.dmem (fbA m0 + BitVec.ofNat 64 o) n :=
  NativeRustcVm.Layout.Same.of_sameOutside hso fun i hi hRp ↦ by
    rw [NativeRustcVm.addr_add_add] at hRp
    rcases hR _ hRp with h' | h' | h'
    · unfold stackBelow at h'
      rw [hb.sp] at h'
      exact not_inRange_below (by omega) h'
    · exact slot_not hpre.1 (by decide) (wsOff hpre) (show o + i < 1408 by omega) h'
    · unfold InRange at h'
      rw [show fbA m0 + BitVec.ofNat 64 (o + i) - (fbA m0 + BitVec.ofNat 64 o') =
        BitVec.ofNat 64 (o + i) - BitVec.ofNat 64 o' by bv_omega, BitVec.toNat_sub,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h'
      omega

/-- **Part of an argument's region** is apart from the frame's bytes `o'` to `o' + n'`. -/
theorem arg_local_apart' (hpre : FirstClaimPre inst segment lanePoint output m0) {r : Region}
    (hr : r ∈ rsOf m0 inst.size) {o l : Nat} (hol : o + l ≤ r.size) {o' n' : Nat}
    (hon : o' + n' ≤ 1408) :
    Apart (r.addr + BitVec.ofNat 64 o) l (fbA m0 + BitVec.ofNat 64 o') n' := by
  have h := arg_local_apart hpre hr hon
  have hnw := (Areas.ok (pre_areas hpre) (Or.inr hr)).2
  unfold Apart at h ⊢
  unfold NativeRustcVm.NoWrap at hnw
  rcases Nat.lt_or_ge (r.addr.toNat + o) (2 ^ 64) with hlt | hge
  · rw [toNat_add_ofNat' hlt]; omega
  · have e : (r.addr + BitVec.ofNat 64 o).toNat = 0 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod,
        show r.addr.toNat + o = 2 ^ 64 by omega, Nat.mod_self]
    rw [e]; omega

/-- **The result's bytes** `o` to `o + n` are apart from the frame's `o'` to `o' + n'`. -/
theorem out_local_apart (hpre : FirstClaimPre inst segment lanePoint output m0) {o n o' n' : Nat}
    (hon : o + n ≤ 776) (hon' : o' + n' ≤ 1408) (hn : 0 < n) (hn' : 0 < n') :
    Apart (outA m0 + BitVec.ofNat 64 o) n (fbA m0 + BitVec.ofNat 64 o') n' := by
  have hS := hpre.1
  have hA := pre_areas hpre
  have hw : (⟨outA m0, 8 + claimBytes⟩ : Region) ∈ wsOf m0 := by simp
  have h := Areas.apart_stack hA hw
  have hook := Areas.ok hA (Or.inl hw)
  have e : fbA m0 + BitVec.ofNat 64 o' =
      stackBelow m0 firstClaimStack + BitVec.ofNat 64 (firstClaimStack - 1408 + o') := by
    rw [stack_eq]; unfold stackBelow fbA; bv_omega
  rw [e]
  exact Apart.sub (o := o) (n := n) (o' := firstClaimStack - 1408 + o') (n' := n') h hook.2
    (noWrap_stackBelow hS) (by show o + n ≤ 8 + 768; omega) (by rw [stack_eq]; omega) hn hn'

/-- **Frame bytes kept** by a change in the result's bytes `o'` to `o' + n'`. -/
theorem local_same_out (hpre : FirstClaimPre inst segment lanePoint output m0) {d d' : DataMem}
    {o n o' n' : Nat} (hon : o + n ≤ 1408) (hon' : o' + n' ≤ 776) (hn' : 0 < n')
    (hs : SameOutside d d' (InRange (outA m0 + BitVec.ofNat 64 o') n')) :
    Same d d' (fbA m0 + BitVec.ofNat 64 o) n :=
  NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj ↦ by
    have hfw : (fbA m0).toNat + 1416 ≤ 2 ^ 64 := (frame_word_ok hpre).2
    have hw : (⟨outA m0, 8 + claimBytes⟩ : Region) ∈ wsOf m0 := by simp
    have hook : (outA m0).toNat + 776 ≤ 2 ^ 64 := (Areas.ok (pre_areas hpre) (Or.inl hw)).2
    exact NativeRustcVm.Apart.not_inRange_add
      (out_local_apart hpre (o := o') (n := n') (o' := o) (n' := n) hon' hon hn' (by omega)).symm
      (by unfold NativeRustcVm.NoWrap; rw [toNat_add_ofNat' (by omega)]; omega)
      (by
        unfold NativeRustcVm.NoWrap
        rw [toNat_add_ofNat' (by omega)]
        omega) hj

/-- **The result's bytes kept** by a change in its bytes `o'` to `o' + n'` apart from them. -/
theorem out_same {d d' : DataMem} {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    {o n o' n' : Nat} (hon : o + n ≤ 776) (hon' : o' + n' ≤ 776) (hdis : o + n ≤ o' ∨ o' + n' ≤ o)
    (hR : ∀ p, R p → InRange (outA m0 + BitVec.ofNat 64 o') n' p) :
    Same d d' (outA m0 + BitVec.ofNat 64 o) n :=
  NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hRp ↦ by
    have := hR _ hRp
    rw [NativeRustcVm.addr_add_add] at this
    exact not_inRange_off (by omega) (by omega) (by omega) this

/-- **The bit weights kept** by a change in the result. -/
theorem w_keep_out (hpre : FirstClaimPre inst segment lanePoint output m0) {d d' : DataMem}
    {f : Nat → EW} (h : ElemsAt d (wtsA m0) f 1600) {R : BitVec 64 → Prop}
    (hs : SameOutside d d' R) (hR : ∀ p, R p → InRange (outA m0) (8 + claimBytes) p) :
    ElemsAt d' (wtsA m0) f 1600 := by
  have hA := pre_areas hpre
  have hap := Areas.apart_ws hA (i := 1) (j := 0) (by simp) (by simp) (by decide)
  simp only [wsOf, List.getElem_cons_succ, List.getElem_cons_zero] at hap
  have hwok : (wtsA m0).toNat + 25600 ≤ 2 ^ 64 :=
    (Areas.ok hA (Or.inl (show (⟨wtsA m0, weightsBytes⟩ : Region) ∈ wsOf m0 by simp))).2
  have hook : (outA m0).toNat + (8 + claimBytes) ≤ 2 ^ 64 :=
    (Areas.ok hA (Or.inl (show (⟨outA m0, 8 + claimBytes⟩ : Region) ∈ wsOf m0 by simp))).2
  exact h.keep hs (fun p hp hRp ↦ NativeRustcVm.Apart.not_inRange hap hwok hook hp (hR p hRp))
    (by unfold NoWrap; omega)

end

end NativeRustcVmArm.KeccakGkr.FirstClaim
