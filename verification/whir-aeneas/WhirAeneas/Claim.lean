import WhirAeneas.Generated.Statement.Funs
import WhirAeneas.ClaimShape

namespace WhirAeneas.Claim
open Aeneas Aeneas.Std

/-- The extracted release shift computes the mathematical block length under
its source guard. This lemma covers the x86-64 extraction ABI. -/
theorem shift_one_value (vars : Usize)
    (hword : UScalarTy.Usize.numBits = 64) (hvars : vars.val < 64) :
    (Usize.wrapping_shl 1#usize vars).val = 2 ^ vars.val := by
  have hp : 2 ^ vars.val < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hvars
  change ((1#usize).bv.shiftLeft
    (vars.val % UScalarTy.Usize.numBits)).toNat = 2 ^ vars.val
  have h1 : (1#usize).bv = BitVec.ofNat UScalarTy.Usize.numBits 1 :=
    UScalar.ofNatCore_bv 1 _
  rw [h1, hword, Nat.mod_eq_of_lt hvars]
  simp only [BitVec.shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  norm_num
  simpa using hp

theorem bits_cast_value (hword : UScalarTy.Usize.numBits = 64) :
    (UScalar.cast .Usize core.num.Usize.BITS).val = 64 := by
  simp only [UScalar.cast_val_eq, core.num.Usize.BITS, UScalar.ofNat,
    UScalar.ofNatCore_val_eq, hword]
  norm_num

/-- Exact Boolean and failure-free behavior of the actual translated helper.
Checked addition rejects overflow before comparing the enclosing block end. -/
theorem aligned_slice_eq (offset vars committed : Usize)
    (hword : UScalarTy.Usize.numBits = 64) :
    StatementSource.stack.is_aligned_slice offset vars committed =
      .ok (decide (vars.val < 64 ∧ offset.val % 2 ^ vars.val = 0 ∧
        offset.val + 2 ^ vars.val ≤ committed.val)) := by
  have hbits := bits_cast_value hword
  have hplatform : System.Platform.numBits = 64 := hword
  unfold StatementSource.stack.is_aligned_slice
  simp only [lift]
  by_cases hv : vars.val < 64
  · have hlen := shift_one_value vars hword hv
    simp only [UScalar.lt_equiv, hv]
    simp only [core.num.Usize.is_multiple_of, UScalar.is_multiple_of]
    by_cases hm : offset.val % 2 ^ vars.val = 0
    · simp only [hm]
      have hsum := Usize.checked_add_bv_spec offset (Usize.wrapping_shl 1#usize vars)
      cases hc : Usize.checked_add offset (Usize.wrapping_shl 1#usize vars) with
      | none =>
        simp only [hc] at hsum
        have hcomm : committed.val ≤ Usize.max := by scalar_tac
        have hnot : ¬ offset.val + 2 ^ vars.val ≤ committed.val := by
          rw [hlen] at hsum
          omega
        simp [hc, core.option.Option.is_some_and, hlen, hm, hnot]
      | some finish =>
        simp only [hc] at hsum
        have hend : finish.val = offset.val + 2 ^ vars.val := by simpa [hlen] using hsum.2.1
        simp [hc, core.option.Option.is_some_and,
          StatementSource.stack.is_aligned_slice.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeBool.call_once,
          UScalar.le_equiv, hend, hplatform, hlen, hv, hm]
    · simp [hlen, hm]
  · simp [UScalar.lt_equiv, hbits, hv]

/-- Exact content-level behavior of the actual generated point-claim guard. -/
theorem point_guard_eq {E : Type} (copy : core.marker.Copy E)
    (offset : Usize) (point : alloc.vec.Vec E) (value : E) (committed : Usize)
    (hword : UScalarTy.Usize.numBits = 64) :
    StatementSource.stack.StackClaim.is_well_formed copy
      (.Point offset point value) committed =
      .ok (decide (point.val.length < 64 ∧
        offset.val % 2 ^ point.val.length = 0 ∧
        offset.val + 2 ^ point.val.length ≤ committed.val)) := by
  simp [StatementSource.stack.StackClaim.is_well_formed, StatementSource.stack.StackClaim.support,
    aligned_slice_eq _ _ _ hword, alloc.vec.Vec.len]

/-- Exact generated strided-claim behavior, including support-width overflow.
The guard uses the enclosing block, not only the selected strided positions. -/
theorem strided_guard_eq {E : Type} (copy : core.marker.Copy E)
    (offset slot stride : Usize) (point : alloc.vec.Vec E) (value : E) (committed : Usize)
    (hword : UScalarTy.Usize.numBits = 64) :
    StatementSource.stack.StackClaim.is_well_formed copy
      (.Strided offset slot stride point value) committed =
      .ok (decide (stride.val + point.val.length < 64 ∧ slot.val < 2 ^ stride.val ∧
        offset.val % 2 ^ (stride.val + point.val.length) = 0 ∧
        offset.val + 2 ^ (stride.val + point.val.length) ≤ committed.val)) := by
  have hplatform : System.Platform.numBits = 64 := hword
  have hsum := Usize.checked_add_bv_spec stride (alloc.vec.Vec.len point)
  cases hc : Usize.checked_add stride (alloc.vec.Vec.len point) with
  | none =>
    simp only [hc, alloc.vec.Vec.len_val] at hsum
    change Usize.max < stride.val + point.val.length at hsum
    have hmax : 64 ≤ Usize.max := by simp [Usize.max, Usize.numBits, hplatform]
    have hd : ¬ stride.val + point.val.length < 64 := by omega
    simp [StatementSource.stack.StackClaim.is_well_formed, StatementSource.stack.StackClaim.support,
      lift, hc, core.option.Option.map, hd]
  | some vars =>
    simp only [hc, alloc.vec.Vec.len_val] at hsum
    have hv : vars.val = stride.val + point.val.length := hsum.2.1
    by_cases hs : stride.val < 64
    · have hlen := shift_one_value stride hword hs
      by_cases hslot : slot.val < 2 ^ stride.val
      · simp [StatementSource.stack.StackClaim.is_well_formed, StatementSource.stack.StackClaim.support,
          lift, hc, core.option.Option.map,
          StatementSource.stack.StackClaim.support.closure.Insts.CoreOpsFunctionFnOnceTupleUsizePairUsizeUsize.call_once,
          aligned_slice_eq _ _ _ hword, UScalar.lt_equiv, hplatform, hlen, hs, hslot, hv]
      · simp [StatementSource.stack.StackClaim.is_well_formed, StatementSource.stack.StackClaim.support,
          lift, hc, core.option.Option.map,
          StatementSource.stack.StackClaim.support.closure.Insts.CoreOpsFunctionFnOnceTupleUsizePairUsizeUsize.call_once,
          UScalar.lt_equiv, hlen, hslot]
    · have hd : ¬ stride.val + point.val.length < 64 := by omega
      simp [StatementSource.stack.StackClaim.is_well_formed, StatementSource.stack.StackClaim.support,
        lift, hc, core.option.Option.map,
        StatementSource.stack.StackClaim.support.closure.Insts.CoreOpsFunctionFnOnceTupleUsizePairUsizeUsize.call_once,
        UScalar.lt_equiv, hplatform, hs, hd]

/-- Metadata interpretation into the actual handwritten model. The coordinate
map is arbitrary because this guard inspects only lengths and selectors; this
is not a field-arithmetic refinement relation. -/
def toModel {E : Type} (encode : E → Whir.Concrete.E) :
    StatementSource.stack.StackClaim E → Whir.RingPCSGame.PointClaim
  | .Point offset point value =>
      .point offset.val (point.val.map encode).toArray (encode value)
  | .Strided offset slot stride point value =>
      .strided offset.val slot.val stride.val (point.val.map encode).toArray (encode value)

/-- Exact successful Boolean result, including rejection, for arbitrary claim
metadata. There is no Shape premise. The ABI and occupied-prefix layout are
explicit, and Vec represents valid logical content rather than allocator state. -/
theorem guard_eq_occupied {E : Type} (copy : core.marker.Copy E)
    (encode : E → Whir.Concrete.E) (claim : StatementSource.stack.StackClaim E)
    (n : Nat) (committed : Usize) (hword : UScalarTy.Usize.numBits = 64)
    (hn : n < 64) (hcomm : committed.val ≤ 2 ^ n) :
    StatementSource.stack.StackClaim.is_well_formed copy claim committed =
      .ok (ClaimShape.checkOccupied n committed.val (toModel encode claim)) := by
  cases claim with
  | Point offset point value =>
    rw [point_guard_eq copy offset point value committed hword]
    simp only [toModel, ClaimShape.checkOccupied, List.size_toArray, List.length_map]
    by_cases hd : point.val.length ≤ n
    · have hw : point.val.length < 64 := hd.trans_lt hn
      simp [hd, hw]
    · have hend : ¬ offset.val + 2 ^ point.val.length ≤ committed.val := by
        intro h
        exact hd (Whir.SuccinctPointWeight.dimension_le_of_block_bound
          offset.val point.val.length n (h.trans hcomm))
      simp [hd, hend]
  | Strided offset slot stride point value =>
    rw [strided_guard_eq copy offset slot stride point value committed hword]
    simp only [toModel, ClaimShape.checkOccupied, List.size_toArray, List.length_map]
    by_cases hd : stride.val + point.val.length ≤ n
    · have hw : stride.val + point.val.length < 64 := hd.trans_lt hn
      simp [hd, hw, and_comm, and_left_comm]
    · have hend : ¬ offset.val + 2 ^ (stride.val + point.val.length) ≤ committed.val := by
        intro h
        exact hd (Whir.SuccinctPointWeight.dimension_le_of_block_bound
          offset.val (stride.val + point.val.length) n (h.trans hcomm))
      simp [hd, hend]

theorem guard_eq_model {E : Type} (copy : core.marker.Copy E)
    (encode : E → Whir.Concrete.E) (claim : StatementSource.stack.StackClaim E)
    (n : Nat) (committed : Usize) (hword : UScalarTy.Usize.numBits = 64)
    (hn : n < 64) (hcomm : committed.val ≤ 2 ^ n) :
    StatementSource.stack.StackClaim.is_well_formed copy claim committed =
      .ok (Whir.SuccinctPointWeight.check n (toModel encode claim) &&
        decide (ClaimShape.blockFits committed.val (toModel encode claim))) := by
  rw [guard_eq_occupied copy encode claim n committed hword hn hcomm,
    ClaimShape.checkOccupied_eq n committed.val (toModel encode claim) hcomm]

theorem guard_accept_iff {E : Type} (copy : core.marker.Copy E)
    (encode : E → Whir.Concrete.E) (claim : StatementSource.stack.StackClaim E)
    (n : Nat) (committed : Usize) (hword : UScalarTy.Usize.numBits = 64)
    (hn : n < 64) (hcomm : committed.val ≤ 2 ^ n) :
    (StatementSource.stack.StackClaim.is_well_formed copy claim committed).match = .ok true ↔
      Whir.SuccinctPointWeight.Shape n (toModel encode claim) ∧
        ClaimShape.blockFits committed.val (toModel encode claim) := by
  rw [guard_eq_occupied copy encode claim n committed hword hn hcomm, Result.match.ok]
  simp only [MatchResult.ok.injEq]
  exact ClaimShape.checkOccupied_true_iff n committed.val (toModel encode claim) hcomm

theorem guard_reject_iff {E : Type} (copy : core.marker.Copy E)
    (encode : E → Whir.Concrete.E) (claim : StatementSource.stack.StackClaim E)
    (n : Nat) (committed : Usize) (hword : UScalarTy.Usize.numBits = 64)
    (hn : n < 64) (hcomm : committed.val ≤ 2 ^ n) :
    (StatementSource.stack.StackClaim.is_well_formed copy claim committed).match = .ok false ↔
      ¬ (Whir.SuccinctPointWeight.Shape n (toModel encode claim) ∧
        ClaimShape.blockFits committed.val (toModel encode claim)) := by
  rw [guard_eq_occupied copy encode claim n committed hword hn hcomm, Result.match.ok]
  simp only [MatchResult.ok.injEq]
  have htrue := ClaimShape.checkOccupied_true_iff n committed.val (toModel encode claim) hcomm
  constructor
  · intro hf hprop
    have ht := htrue.mpr hprop
    simp [ht] at hf
  · intro hneg
    cases hb : ClaimShape.checkOccupied n committed.val (toModel encode claim) with
    | false => rfl
    | true => exact False.elim (hneg (htrue.mp hb))

/-- Soundness-relevant direction: the source cannot accept metadata outside the
actual model's Shape under the runtime/layout premises. Shape is not assumed. -/
theorem guard_accept_implies_model_accept {E : Type} (copy : core.marker.Copy E)
    (encode : E → Whir.Concrete.E) (claim : StatementSource.stack.StackClaim E)
    (n : Nat) (committed : Usize) (hword : UScalarTy.Usize.numBits = 64)
    (hn : n < 64) (hcomm : committed.val ≤ 2 ^ n)
    (haccept : (StatementSource.stack.StackClaim.is_well_formed copy claim committed).match = .ok true) :
    Whir.SuccinctPointWeight.check n (toModel encode claim) = true := by
  exact (Whir.SuccinctPointWeight.check_iff n (toModel encode claim)).mpr
    ((guard_accept_iff copy encode claim n committed hword hn hcomm).mp haccept).1

/-- Equality with the actual model when every cube position is occupied. -/
theorem guard_full_cube_eq {E : Type} (copy : core.marker.Copy E)
    (encode : E → Whir.Concrete.E) (claim : StatementSource.stack.StackClaim E)
    (n : Nat) (committed : Usize) (hword : UScalarTy.Usize.numBits = 64)
    (hn : n < 64) (hcomm : committed.val = 2 ^ n) :
    StatementSource.stack.StackClaim.is_well_formed copy claim committed =
      .ok (Whir.SuccinctPointWeight.check n (toModel encode claim)) := by
  rw [guard_eq_occupied copy encode claim n committed hword hn hcomm.le, hcomm,
    ClaimShape.checkOccupied_full_cube]

end WhirAeneas.Claim
