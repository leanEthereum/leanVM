import WhirAeneas.Claim
import WhirAeneas.StatementShape

/-! The actual generated `pcs::stack::Statement::check` computes the
metadata-level `StatementShape.check`, including its error and error order.
Premises: the x86-64 word width, `log_n < 64`, and the occupied prefix
`committed ≤ 2 ^ log_n`, which the verifier's preceding shape guard establishes. -/
namespace WhirAeneas.Statement
open Aeneas Aeneas.Std StatementSource

variable {E : Type}

/-- Metadata interpretation of a source region. -/
def region (encode : E → Whir.Concrete.E) (r : ring_switch.RingSwitch E) : StatementShape.Region :=
  ⟨r.offset.val, r.qflock_vars.val,
    r.claims.val.map fun c => ((c.suffix_point.val.map encode).toArray, c.s_hat_v.val.map encode)⟩

/-- Interpretation of the source result. Errors this check never produces have
no interpretation. -/
def toShape : core.result.Result Unit whir.verify.WhirError → Option (Except StatementShape.Error Unit)
  | .Ok () => some (.ok ())
  | .Err .NoRingClaim => some (.error .noRingClaim)
  | .Err (.Region index) => some (.error (.region index.val))
  | .Err (.PointClaim index) => some (.error (.pointClaim index.val))
  | .Err _ => none

theorem toShape_ok {r : core.result.Result Unit whir.verify.WhirError}
    (h : toShape r = some (.ok ())) : r = .Ok () := by
  rcases r with ⟨⟩ | e
  · rfl
  · cases e <;> simp [toShape] at h

private theorem loop_cont {α β : Type} {body : α → Result (ControlFlow α β)} {x x' : α}
    (h : body x = .ok (.cont x')) : loop body x = loop body x' := by
  rw [loop]; simp [h]

private theorem loop_done {α β : Type} {body : α → Result (ControlFlow α β)} {x : α} {y : β}
    (h : body x = .ok (.done y)) : loop body x = .ok y := by
  rw [loop]; simp [h]

private theorem succ_val (i : Usize) (n : Nat) (hi : i.val < n) (hn : n ≤ Usize.max) :
    (Std.Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have : i.val + 1 < UScalar.size .Usize := by
    have := Usize.max_def; simp only [UScalar.size] at *; scalar_tac
  have h1 : (1#usize).val = 1 := by simp
  rw [h1]
  exact Nat.mod_eq_of_lt this

private theorem zero_val : (0#usize).val = 0 := by simp

private theorem slice_index (s : Slice α) (i : Usize) (hi : i.val < s.val.length) :
    Slice.index_usize s i = .ok s.val[i.val] := by
  simp [Slice.index_usize, Slice.getElem?_Usize_eq, hi]

private theorem vec_index (v : alloc.vec.Vec α) (i : Usize) (hi : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = .ok v.val[i.val] := by
  rw [alloc.vec.Vec.index_slice_index]
  simp [alloc.vec.Vec.index_usize, hi]

/-! ## No ring claim -/

theorem loop0_false (s : Slice (ring_switch.RingSwitch E)) (i : Usize) :
    stack.Statement.check_loop0 s i false = .ok false := by
  unfold stack.Statement.check_loop0
  apply loop_done
  simp only [stack.Statement.check_loop0.body]
  split <;> simp

theorem loop0_true (s : Slice (ring_switch.RingSwitch E)) :
    ∀ i : Usize, i.val ≤ s.val.length →
      stack.Statement.check_loop0 s i true =
        .ok ((s.val.drop i.val).all fun r => r.claims.val.isEmpty) := by
  intro i hi
  induction h : s.val.length - i.val generalizing i with
  | zero =>
    have hge : s.val.length ≤ i.val := by omega
    unfold stack.Statement.check_loop0
    apply loop_done
    simp [stack.Statement.check_loop0.body, UScalar.lt_equiv, Slice.len_val,
      Nat.not_lt.mpr hge, List.drop_eq_nil_of_le hge]
  | succ k ih =>
    have hlt : i.val < s.val.length := by omega
    have hsucc := succ_val i s.val.length hlt (Slice.length_ineq s)
    have hdrop := List.drop_eq_getElem_cons hlt
    have hbody : stack.Statement.check_loop0.body s i true =
        .ok (.cont (Std.Usize.wrapping_add i 1#usize, s.val[i.val].claims.val.isEmpty)) := by
      simp only [stack.Statement.check_loop0.body, UScalar.lt_equiv, Slice.len_val, Slice.length,
        hlt, ↓reduceIte, slice_index s i hlt, Std.bind_ok, bind_tc_ok,
        StdGuards.vec_is_empty, lift]
    unfold stack.Statement.check_loop0
    rw [loop_cont hbody]
    rw [hdrop, List.all_cons]
    cases hempty : s.val[i.val].claims.val.isEmpty with
    | false =>
      have := loop0_false s (Std.Usize.wrapping_add i 1#usize)
      unfold stack.Statement.check_loop0 at this
      simpa using this
    | true =>
      have := ih (Std.Usize.wrapping_add i 1#usize) (by omega) (by omega)
      unfold stack.Statement.check_loop0 at this
      simpa [hsucc] using this

/-! ## Regions -/

theorem spans_region_eq (c : ring_switch.SliceClaim E) (vars : Usize) :
    stack.spans_region c vars =
      .ok (decide (c.suffix_point.val.length = vars.val ∧ c.s_hat_v.val.length = 64)) := by
  unfold stack.spans_region
  have h64 : (64#usize).val = 64 := by simp
  simp only [UScalar.eq_equiv, alloc.vec.Vec.len_val, alloc.vec.Vec.length,
    primitives.field.gf2_64.F64.DEGREE, h64]
  by_cases h1 : c.suffix_point.val.length = vars.val <;> simp [h1]

/-- Boolean source region guard. -/
def regionOk (encode : E → Whir.Concrete.E) (logN committed : Nat)
    (r : ring_switch.RingSwitch E) : Bool :=
  decide ((region encode r).Valid logN committed)

theorem inner_false (ring : ring_switch.RingSwitch E) (i : Usize) :
    stack.Statement.check_loop1_loop0 ring i false = .ok (ring.offset, ring.qflock_vars, false) := by
  unfold stack.Statement.check_loop1_loop0
  apply loop_done
  simp only [stack.Statement.check_loop1_loop0.body]
  split <;> simp

theorem inner_true (ring : ring_switch.RingSwitch E) :
    ∀ i : Usize, i.val ≤ ring.claims.val.length →
      stack.Statement.check_loop1_loop0 ring i true =
        .ok (ring.offset, ring.qflock_vars, (ring.claims.val.drop i.val).all fun c =>
          decide (c.suffix_point.val.length = ring.qflock_vars.val ∧ c.s_hat_v.val.length = 64)) := by
  intro i hi
  induction h : ring.claims.val.length - i.val generalizing i with
  | zero =>
    have hge : ring.claims.val.length ≤ i.val := by omega
    unfold stack.Statement.check_loop1_loop0
    apply loop_done
    simp [stack.Statement.check_loop1_loop0.body, UScalar.lt_equiv, alloc.vec.Vec.len_val,
      Nat.not_lt.mpr hge, List.drop_eq_nil_of_le hge]
  | succ k ih =>
    have hlt : i.val < ring.claims.val.length := by omega
    have hsucc := succ_val i ring.claims.val.length hlt ring.claims.property
    have hdrop := List.drop_eq_getElem_cons hlt
    have hbody : stack.Statement.check_loop1_loop0.body ring i true =
        .ok (.cont (Std.Usize.wrapping_add i 1#usize,
          decide (ring.claims.val[i.val].suffix_point.val.length = ring.qflock_vars.val ∧
            ring.claims.val[i.val].s_hat_v.val.length = 64))) := by
      simp only [stack.Statement.check_loop1_loop0.body, UScalar.lt_equiv, alloc.vec.Vec.len_val,
        alloc.vec.Vec.length, hlt, ↓reduceIte, vec_index ring.claims i hlt, Std.bind_ok,
        bind_tc_ok, spans_region_eq, lift]
    unfold stack.Statement.check_loop1_loop0
    rw [loop_cont hbody, hdrop, List.all_cons]
    cases hspan : decide (ring.claims.val[i.val].suffix_point.val.length = ring.qflock_vars.val ∧
        ring.claims.val[i.val].s_hat_v.val.length = 64) with
    | false =>
      have := inner_false ring (Std.Usize.wrapping_add i 1#usize)
      unfold stack.Statement.check_loop1_loop0 at this
      simpa using this
    | true =>
      have := ih (Std.Usize.wrapping_add i 1#usize) (by omega) (by omega)
      unfold stack.Statement.check_loop1_loop0 at this
      simpa [hsucc] using this

theorem spans_all (encode : E → Whir.Concrete.E) (ring : ring_switch.RingSwitch E) :
    (ring.claims.val.all fun c =>
      decide (c.suffix_point.val.length = ring.qflock_vars.val ∧ c.s_hat_v.val.length = 64)) =
      decide (region encode ring).Spans := by
  apply Bool.eq_iff_iff.mpr
  simp [StatementShape.Region.Spans, region, List.all_eq_true]

def regionsFrom (logN committed : Nat) (rings : List StatementShape.Region) (start : Nat) :
    Except StatementShape.Error Unit :=
  match (rings.drop start).findIdx? (fun r => !decide (r.Valid logN committed)) with
  | some j => .error (.region (start + j))
  | none => .ok ()

theorem loop1_err (s : Slice (ring_switch.RingSwitch E)) (log_n committed i : Usize)
    (e : whir.verify.WhirError) :
    stack.Statement.check_loop1 s log_n committed i (.Err e) = .ok (.Err e) := by
  unfold stack.Statement.check_loop1
  apply loop_done
  simp only [stack.Statement.check_loop1.body, core.result.Result.is_ok]
  split <;> simp

/-- The source region verdict in the order the generated body decides it. -/
theorem regionOk_eq (encode : E → Whir.Concrete.E) (logN committed : Nat)
    (r : ring_switch.RingSwitch E) :
    regionOk encode logN committed r =
      (decide (¬ logN < r.qflock_vars.val) && decide (region encode r).Spans &&
        decide (r.qflock_vars.val < 64 ∧ r.offset.val % 2 ^ r.qflock_vars.val = 0 ∧
          r.offset.val + 2 ^ r.qflock_vars.val ≤ committed)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [regionOk, Bool.and_eq_true, decide_eq_true_eq]
  unfold StatementShape.Region.Valid
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨by simp only [region] at h1; omega, h2⟩, h3, h4, h5⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    exact ⟨by simp only [region]; omega, h2, h3, h4, h5⟩

/-- One region iteration: the generated body continues with the region's verdict. -/
theorem loop1_body (encode : E → Whir.Concrete.E) (s : Slice (ring_switch.RingSwitch E))
    (log_n committed i : Usize) (hword : UScalarTy.Usize.numBits = 64) (hlt : i.val < s.val.length) :
    stack.Statement.check_loop1.body s log_n committed i (.Ok ()) =
      .ok (.cont (Std.Usize.wrapping_add i 1#usize,
        if regionOk encode log_n.val committed.val s.val[i.val] then .Ok ()
        else .Err (whir.verify.WhirError.Region i))) := by
  simp only [stack.Statement.check_loop1.body, UScalar.lt_equiv, Slice.len_val, Slice.length,
    hlt, ↓reduceIte, core.result.Result.is_ok, Std.bind_ok, slice_index s i hlt,
    inner_true s.val[i.val] 0#usize (by simp), zero_val, List.drop_zero, spans_all encode,
    Claim.aligned_slice_eq _ _ _ hword, gt_iff_lt, lift]
  rw [regionOk_eq]
  by_cases hv : log_n.val < s.val[i.val].qflock_vars.val
  · simp [hv]
  · by_cases hs : (region encode s.val[i.val]).Spans
    · by_cases ha : s.val[i.val].qflock_vars.val < 64 ∧
          s.val[i.val].offset.val % 2 ^ s.val[i.val].qflock_vars.val = 0 ∧
          s.val[i.val].offset.val + 2 ^ s.val[i.val].qflock_vars.val ≤ committed.val
      · simp [hv, ha, hs]
      · simp only [decide_eq_false ha, decide_eq_true hs, decide_eq_true hv]
        first | simp [hv, ha] | (rw [if_neg ha]; simp)
    · simp only [decide_eq_false hs]
      simp [hv]

theorem loop1_ok (encode : E → Whir.Concrete.E) (s : Slice (ring_switch.RingSwitch E))
    (log_n committed : Usize) (hword : UScalarTy.Usize.numBits = 64) :
    ∀ i : Usize, i.val ≤ s.val.length →
      ∃ r, stack.Statement.check_loop1 s log_n committed i (.Ok ()) = .ok r ∧
        toShape r = some (regionsFrom log_n.val committed.val (s.val.map (region encode)) i.val) := by
  intro i hi
  induction h : s.val.length - i.val generalizing i with
  | zero =>
    have hge : s.val.length ≤ i.val := by omega
    have hnil : (s.val.map (region encode)).drop i.val = [] :=
      List.drop_eq_nil_of_le (by simpa using hge)
    refine ⟨.Ok (), ?_, ?_⟩
    · unfold stack.Statement.check_loop1
      apply loop_done
      simp [stack.Statement.check_loop1.body, UScalar.lt_equiv, Slice.len_val, Nat.not_lt.mpr hge]
    · simp [toShape, regionsFrom, hnil]
  | succ k ih =>
    have hlt : i.val < s.val.length := by omega
    have hsucc := succ_val i s.val.length hlt (Slice.length_ineq s)
    have hdrop : (s.val.map (region encode)).drop i.val =
        region encode s.val[i.val] :: (s.val.map (region encode)).drop (i.val + 1) := by
      rw [← List.map_drop, List.drop_eq_getElem_cons hlt, List.map_cons, List.map_drop]
    unfold stack.Statement.check_loop1
    rw [loop_cont (loop1_body encode s log_n committed i hword hlt)]
    cases hok : regionOk encode log_n.val committed.val s.val[i.val] with
    | false =>
      refine ⟨.Err (whir.verify.WhirError.Region i), ?_, ?_⟩
      · have := loop1_err s log_n committed (Std.Usize.wrapping_add i 1#usize)
          (whir.verify.WhirError.Region i)
        unfold stack.Statement.check_loop1 at this
        simpa using this
      · have hbad : (!decide ((region encode s.val[i.val]).Valid log_n.val committed.val)) = true := by
          simpa [regionOk] using hok
        simp [toShape, regionsFrom, hdrop, List.findIdx?_cons, hbad]
    | true =>
      obtain ⟨r, hr, hshape⟩ := ih (Std.Usize.wrapping_add i 1#usize) (by omega) (by omega)
      refine ⟨r, ?_, ?_⟩
      · unfold stack.Statement.check_loop1 at hr
        simpa using hr
      · have hgood : (!decide ((region encode s.val[i.val]).Valid log_n.val committed.val)) = false := by
          simpa [regionOk] using hok
        rw [hshape, hsucc]
        simp only [regionsFrom, hdrop, List.findIdx?_cons, hgood]
        cases (List.drop (i.val + 1) (s.val.map (region encode))).findIdx?
            (fun r => !decide (r.Valid log_n.val committed.val)) with
        | none => simp
        | some j => simp; omega

/-! ## Point claims -/

def pointsFrom (logN committed : Nat) (points : List Whir.RingPCSGame.PointClaim) (start : Nat) :
    Except StatementShape.Error Unit :=
  match (points.drop start).findIdx? (fun p => !ClaimShape.checkOccupied logN committed p) with
  | some j => .error (.pointClaim (start + j))
  | none => .ok ()

theorem loop2_err (copy : core.marker.Copy E) (s : Slice (stack.StackClaim E))
    (committed i : Usize) (e : whir.verify.WhirError) :
    stack.Statement.check_loop2 copy s committed i (.Err e) = .ok (.Err e) := by
  unfold stack.Statement.check_loop2
  apply loop_done
  simp only [stack.Statement.check_loop2.body, core.result.Result.is_ok]
  split <;> simp

theorem loop2_ok (copy : core.marker.Copy E) (encode : E → Whir.Concrete.E)
    (s : Slice (stack.StackClaim E)) (log_n committed : Usize)
    (hword : UScalarTy.Usize.numBits = 64) (hn : log_n.val < 64)
    (hcomm : committed.val ≤ 2 ^ log_n.val) :
    ∀ i : Usize, i.val ≤ s.val.length →
      ∃ r, stack.Statement.check_loop2 copy s committed i (.Ok ()) = .ok r ∧
        toShape r = some (pointsFrom log_n.val committed.val (s.val.map (Claim.toModel encode)) i.val) := by
  intro i hi
  induction h : s.val.length - i.val generalizing i with
  | zero =>
    have hge : s.val.length ≤ i.val := by omega
    have hnil : (s.val.map (Claim.toModel encode)).drop i.val = [] :=
      List.drop_eq_nil_of_le (by simpa using hge)
    refine ⟨.Ok (), ?_, ?_⟩
    · unfold stack.Statement.check_loop2
      apply loop_done
      simp [stack.Statement.check_loop2.body, UScalar.lt_equiv, Slice.len_val, Nat.not_lt.mpr hge]
    · simp [toShape, pointsFrom, hnil]
  | succ k ih =>
    have hlt : i.val < s.val.length := by omega
    have hsucc := succ_val i s.val.length hlt (Slice.length_ineq s)
    have hguard := Claim.guard_eq_occupied copy encode s.val[i.val] log_n.val committed hword hn hcomm
    have hbody : stack.Statement.check_loop2.body copy s committed i (.Ok ()) =
        .ok (.cont (Std.Usize.wrapping_add i 1#usize,
          if ClaimShape.checkOccupied log_n.val committed.val (Claim.toModel encode s.val[i.val])
          then .Ok () else .Err (whir.verify.WhirError.PointClaim i))) := by
      simp only [stack.Statement.check_loop2.body, UScalar.lt_equiv, Slice.len_val, Slice.length,
        hlt, ↓reduceIte, core.result.Result.is_ok, Std.bind_ok, bind_tc_ok,
        slice_index s i hlt, hguard, lift]
      split_ifs <;> simp_all
    have hdrop : (s.val.map (Claim.toModel encode)).drop i.val =
        Claim.toModel encode s.val[i.val] :: (s.val.map (Claim.toModel encode)).drop (i.val + 1) := by
      rw [← List.map_drop, List.drop_eq_getElem_cons hlt, List.map_cons, List.map_drop]
    unfold stack.Statement.check_loop2
    rw [loop_cont hbody]
    cases hok : ClaimShape.checkOccupied log_n.val committed.val (Claim.toModel encode s.val[i.val]) with
    | false =>
      refine ⟨.Err (whir.verify.WhirError.PointClaim i), ?_, ?_⟩
      · have := loop2_err copy s committed (Std.Usize.wrapping_add i 1#usize)
          (whir.verify.WhirError.PointClaim i)
        unfold stack.Statement.check_loop2 at this
        simpa using this
      · simp [toShape, pointsFrom, hdrop, List.findIdx?_cons, hok]
    | true =>
      obtain ⟨r, hr, hshape⟩ := ih (Std.Usize.wrapping_add i 1#usize) (by omega) (by omega)
      refine ⟨r, ?_, ?_⟩
      · unfold stack.Statement.check_loop2 at hr
        simpa using hr
      · rw [hshape, hsucc]
        simp only [pointsFrom, hdrop, List.findIdx?_cons, hok, Bool.not_true]
        cases (List.drop (i.val + 1) (s.val.map (Claim.toModel encode))).findIdx?
            (fun p => !ClaimShape.checkOccupied log_n.val committed.val p) with
        | none => simp
        | some j => simp; omega

/-! ## The whole check -/

/-- Exact result of the actual generated check, including which error it
returns, for arbitrary statements. -/
theorem check_eq (copy : core.marker.Copy E) (encode : E → Whir.Concrete.E)
    (st : stack.Statement E) (log_n committed : Usize)
    (hword : UScalarTy.Usize.numBits = 64) (hn : log_n.val < 64)
    (hcomm : committed.val ≤ 2 ^ log_n.val) :
    ∃ r, stack.Statement.check copy st log_n committed = .ok r ∧
      toShape r = some (StatementShape.check log_n.val committed.val
        (st.rings.val.map (region encode)) (st.points.val.map (Claim.toModel encode))) := by
  have hall : (st.rings.val.map (region encode)).all (fun r => r.claims.isEmpty) =
      st.rings.val.all (fun r => r.claims.val.isEmpty) := by
    simp [List.all_map, Function.comp_def, region]
  unfold stack.Statement.check
  rw [loop0_true st.rings 0#usize (by simp)]
  simp only [Std.bind_ok, bind_tc_ok, zero_val, List.drop_zero]
  unfold StatementShape.check
  rw [hall]
  cases hempty : st.rings.val.all (fun r => r.claims.val.isEmpty) with
  | true =>
    refine ⟨_, rfl, ?_⟩
    simp [toShape]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨r1, hr1, hshape1⟩ := loop1_ok encode st.rings log_n committed hword 0#usize (by simp)
    rw [hr1]
    simp only [Std.bind_ok, bind_tc_ok]
    simp only [zero_val, regionsFrom, List.drop_zero, Nat.zero_add] at hshape1
    cases hreg : (st.rings.val.map (region encode)).findIdx?
        (fun r => !decide (r.Valid log_n.val committed.val)) with
    | some j =>
      rw [hreg] at hshape1
      rcases r1 with ⟨⟩ | e
      · simp [toShape] at hshape1
      · exact ⟨_, loop2_err copy st.points committed 0#usize e, hshape1⟩
    | none =>
      rw [hreg] at hshape1
      have hr1ok := toShape_ok hshape1
      subst hr1ok
      obtain ⟨r2, hr2, hshape2⟩ :=
        loop2_ok copy encode st.points log_n committed hword hn hcomm 0#usize (by simp)
      refine ⟨r2, hr2, ?_⟩
      simp only [zero_val, pointsFrom, List.drop_zero, Nat.zero_add] at hshape2
      cases hpt : (st.points.val.map (Claim.toModel encode)).findIdx?
          (fun p => !ClaimShape.checkOccupied log_n.val committed.val p) with
      | none => rw [hpt] at hshape2; exact hshape2
      | some j => rw [hpt] at hshape2; exact hshape2

/-- Source acceptance, exactly. -/
theorem check_accept_iff (copy : core.marker.Copy E) (encode : E → Whir.Concrete.E)
    (st : stack.Statement E) (log_n committed : Usize)
    (hword : UScalarTy.Usize.numBits = 64) (hn : log_n.val < 64)
    (hcomm : committed.val ≤ 2 ^ log_n.val) :
    stack.Statement.check copy st log_n committed = .ok (.Ok ()) ↔
      StatementShape.check log_n.val committed.val
        (st.rings.val.map (region encode)) (st.points.val.map (Claim.toModel encode)) = .ok () := by
  obtain ⟨r, hr, hshape⟩ := check_eq copy encode st log_n committed hword hn hcomm
  rw [hr]
  constructor
  · intro h
    have hr' : r = .Ok () := Result.ok_injective h
    subst hr'
    simpa [toShape] using hshape.symm
  · intro h
    rw [h] at hshape
    rw [toShape_ok hshape]

/-- Soundness-relevant direction: source acceptance gives the model's native
shape premises for the flattened family and every point claim. -/
theorem check_accept_model (copy : core.marker.Copy E) (encode : E → Whir.Concrete.E)
    (st : stack.Statement E) (log_n committed : Usize)
    (hword : UScalarTy.Usize.numBits = 64) (hn : log_n.val < 64)
    (hcomm : committed.val ≤ 2 ^ log_n.val)
    (haccept : stack.Statement.check copy st log_n committed = .ok (.Ok ())) :
    StatementShape.family (st.rings.val.map (region encode)) ≠ [] ∧
      Whir.SuccinctRingWeight.FamilyShape log_n.val
        (StatementShape.familyFn (st.rings.val.map (region encode))) ∧
      ∀ p ∈ st.points.val.map (Claim.toModel encode), Whir.SuccinctPointWeight.Shape log_n.val p :=
  StatementShape.check_ok_model log_n.val committed.val _ _ hcomm
    ((check_accept_iff copy encode st log_n committed hword hn hcomm).mp haccept)

/-- Full-cube converse: a model-shaped statement is accepted when each region
carries a claim and every claim spans its region with 64 slices. -/
theorem check_accept_of_model (copy : core.marker.Copy E) (encode : E → Whir.Concrete.E)
    (st : stack.Statement E) (log_n committed : Usize)
    (hword : UScalarTy.Usize.numBits = 64) (hn : log_n.val < 64)
    (hfull : committed.val = 2 ^ log_n.val)
    (hclaims : ∀ r ∈ st.rings.val.map (region encode), r.claims ≠ [])
    (hspans : ∀ r ∈ st.rings.val.map (region encode), r.Spans)
    (hnonempty : st.rings.val ≠ [])
    (hfamily : Whir.SuccinctRingWeight.FamilyShape log_n.val
      (StatementShape.familyFn (st.rings.val.map (region encode))))
    (hpoints : ∀ p ∈ st.points.val.map (Claim.toModel encode),
      Whir.SuccinctPointWeight.Shape log_n.val p) :
    stack.Statement.check copy st log_n committed = .ok (.Ok ()) := by
  rw [check_accept_iff copy encode st log_n committed hword hn hfull.le, hfull]
  exact StatementShape.check_ok_of_model log_n.val _ _ hn hclaims hspans
    (by simpa using hnonempty) hfamily hpoints

end WhirAeneas.Statement
