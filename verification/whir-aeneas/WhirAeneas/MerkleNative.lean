import WhirAeneas.Merkle

/-! The generated native `open_rows` (`pcs::verifier::open_rows_native`, the body of
`OpeningVerifier::open_rows` for `VerifierState`): read the next length-prefixed hint, decode it
with `PrunedMerklePaths::from_hint` for the distinct queries, authenticate it with
`PrunedMerklePaths::open`, and return each opening's row. A hint that does not decode or
authenticate is `InvalidHint`, one that is absent or cut short is `MissingHint`, and a poisoned
transcript returns its error; both failures poison it. -/
namespace WhirAeneas.MerkleNative
open Aeneas Aeneas.Std ReplaySource WhirAeneas.Merkle

/-- The verifier state, as the native `open_rows` takes it. -/
abbrev VS := fiat_shamir.verifier.VerifierState

/-- The transcript error. -/
abbrev TE := fiat_shamir.verifier.TranscriptError

private theorem loop_cont {α β : Type} {body : α → Result (ControlFlow α β)} {x x' : α}
    (h : body x = .ok (.cont x')) : loop body x = loop body x' := by
  rw [loop]; simp [h]

private theorem loop_done {α β : Type} {body : α → Result (ControlFlow α β)} {x : α} {y : β}
    (h : body x = .ok (.done y)) : loop body x = .ok y := by
  rw [loop]; simp [h]

/-! ## Reading the hint -/

/-- `u32::from_le_bytes` inverts `u32::to_le_bytes`. -/
theorem from_le_to_le (L : U32) : core.num.U32.from_le_bytes (core.num.U32.to_le_bytes L) = L := by
  have key : (core.num.U32.from_le_bytes (core.num.U32.to_le_bytes L)).bv = L.bv := by
    unfold core.num.U32.from_le_bytes
    have hv : List.map U8.bv (core.num.U32.to_le_bytes L).val = L.bv.toLEBytes := by
      simp [core.num.U32.to_le_bytes, List.map_map, Function.comp_def]
    apply BitVec.eq_of_toNat_eq
    simp
    rw [hv, BitVec.fromLEBytes_toLEBytes (by decide)]
    simp
  rcases hx : core.num.U32.from_le_bytes (core.num.U32.to_le_bytes L) with ⟨x⟩
  rw [hx] at key
  cases L
  exact congrArg UScalar.mk key

/-- The four bytes of a `u32`'s little-endian encoding. -/
theorem to_le_four (L : U32) : ∃ a b c d : U8, (core.num.U32.to_le_bytes L).val = [a, b, c, d] := by
  have h : (core.num.U32.to_le_bytes L).val.length = 4 := by simp [core.num.U32.to_le_bytes]
  match hl : (core.num.U32.to_le_bytes L).val, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

/-- The length a hint's prefix encodes, when the prefix is the four bytes `a b c d`. -/
theorem decode_prefix (L : U32) (a b c d : U8) (h : (core.num.U32.to_le_bytes L).val = [a, b, c, d]) :
    core.num.U32.from_le_bytes (Array.make 4#usize [a, b, c, d]) = L := by
  have : (Array.make 4#usize [a, b, c, d]) = core.num.U32.to_le_bytes L := by
    rw [Array.eq_iff]; simp only [Array.make_val, h]
  rw [this, from_le_to_le]

/-- The next hint: the four-byte little-endian length `L`, then those bytes. -/
theorem next_ok (hs : fiat_shamir.proof.Hints)
    (L : U32) (hint more : Slice U8) (hL : L.val = hint.val.length)
    (hb : hs.rest.val = (core.num.U32.to_le_bytes L).val ++ hint.val ++ more.val) :
    fiat_shamir.proof.Hints.Insts.CoreIterTraitsIteratorIteratorSharedASliceU8.next hs =
      .ok (some hint, { rest := more }) := by
  obtain ⟨a, b, c, d, habcd⟩ := to_le_four L
  rw [habcd] at hb
  have hl := hs.rest.property
  have hl' : hs.rest.length = hs.rest.val.length := rfl
  have hlen : hs.rest.val.length = 4 + hint.val.length + more.val.length := by
    rw [hb]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hcast : (UScalar.cast .Usize L).val = hint.val.length := by
    rw [U32.cast_Usize_val_eq]; exact hL
  have hsub : (Std.Usize.wrapping_sub (Slice.len hs.rest) 4#usize).val = hint.val.length + more.val.length := by
    rw [sub_val _ _ (by simp only [Slice.len_val, UScalar.ofNatCore_val_eq]; omega)]
    simp only [Slice.len_val, UScalar.ofNatCore_val_eq]; omega
  have hadd : (Std.Usize.wrapping_add 4#usize (UScalar.cast .Usize L)).val = 4 + hint.val.length := by
    rw [add_val _ _ (by rw [hcast]; simp only [UScalar.ofNatCore_val_eq]; omega)]
    simp only [UScalar.ofNatCore_val_eq, hcast]
  have hrest : hs.rest.val.drop 4 = hint.val ++ more.val := by
    rw [hb, List.append_assoc, List.drop_left' (by rfl)]
  obtain ⟨t, ht, et⟩ := slice_range hs.rest 4#usize (Std.Usize.wrapping_add 4#usize (UScalar.cast .Usize L))
    (by rw [hadd]; simp only [UScalar.ofNatCore_val_eq]; omega) (by rw [hadd]; omega)
  have et' : t = hint := by
    apply Slice.ext
    rw [et, hadd]
    simp only [UScalar.ofNatCore_val_eq, Nat.add_sub_cancel_left, hrest]
    exact List.take_left' rfl
  have hfrom : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) hs.rest
      { start := Std.Usize.wrapping_add 4#usize (UScalar.cast .Usize L) } = .ok more := by
    have hle : (Std.Usize.wrapping_add 4#usize (UScalar.cast .Usize L)).val ≤ hs.rest.length := by
      rw [hadd, hl']; omega
    simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice.index, hle,
      ↓reduceIte]
    congr 1
    apply Slice.ext
    simp only [Slice.drop, Slice.from_val, hadd]
    rw [show 4 + hint.val.length = 4 + hint.val.length from rfl, ← List.drop_drop, hrest]
    exact List.drop_left' rfl
  have hnot : ¬ (Slice.len hs.rest < 4#usize) := by
    intro h
    have : (Slice.len hs.rest).val < (4#usize).val := h
    simp only [Slice.len_val, UScalar.ofNatCore_val_eq] at this
    omega
  have hnot2 : ¬ (Std.Usize.wrapping_sub (Slice.len hs.rest) 4#usize < UScalar.cast .Usize L) := by
    intro h
    have : (Std.Usize.wrapping_sub (Slice.len hs.rest) 4#usize).val < (UScalar.cast .Usize L).val := h
    omega
  have hi0 := slice_index hs.rest 0#usize (by simp only [UScalar.ofNatCore_val_eq]; omega)
  have hi1 := slice_index hs.rest 1#usize (by simp only [UScalar.ofNatCore_val_eq]; omega)
  have hi2 := slice_index hs.rest 2#usize (by simp only [UScalar.ofNatCore_val_eq]; omega)
  have hi3 := slice_index hs.rest 3#usize (by simp only [UScalar.ofNatCore_val_eq]; omega)
  simp only [hb, UScalar.ofNatCore_val_eq] at hi0 hi1 hi2 hi3
  unfold fiat_shamir.proof.Hints.Insts.CoreIterTraitsIteratorIteratorSharedASliceU8.next
  simp only [hnot, ↓reduceIte, lift, bind_ok, hi0, hi1, hi2, hi3]
  simp only [List.cons_append, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [decode_prefix L a b c d habcd, hnot2, ↓reduceIte, bind_ok, hfrom]
  simp only [ht, bind_ok, et']

/-- No next hint: fewer than four bytes remain, or the length they encode runs past the bytes
after them. Nothing is consumed. -/
theorem next_none (hs : fiat_shamir.proof.Hints)
    (h : hs.rest.val.length < 4 ∨ ∃ (L : U32) (rest : List U8),
      hs.rest.val = (core.num.U32.to_le_bytes L).val ++ rest ∧ rest.length < L.val) :
    fiat_shamir.proof.Hints.Insts.CoreIterTraitsIteratorIteratorSharedASliceU8.next hs = .ok (none, hs) := by
  have hl' : hs.rest.length = hs.rest.val.length := rfl
  rcases h with h4 | ⟨L, rest, hb, hr⟩
  · have hlt : Slice.len hs.rest < 4#usize := by
      show (Slice.len hs.rest).val < (4#usize).val
      simp only [Slice.len_val, UScalar.ofNatCore_val_eq]; omega
    unfold fiat_shamir.proof.Hints.Insts.CoreIterTraitsIteratorIteratorSharedASliceU8.next
    simp only [hlt, ↓reduceIte]
  · obtain ⟨a, b, c, d, habcd⟩ := to_le_four L
    rw [habcd] at hb
    have hlen : hs.rest.val.length = 4 + rest.length := by
      rw [hb]; simp only [List.length_append, List.length_cons, List.length_nil]
    have hnot : ¬ (Slice.len hs.rest < 4#usize) := by
      intro h
      have : (Slice.len hs.rest).val < (4#usize).val := h
      simp only [Slice.len_val, UScalar.ofNatCore_val_eq] at this
      omega
    have hsub : (Std.Usize.wrapping_sub (Slice.len hs.rest) 4#usize).val = rest.length := by
      rw [sub_val _ _ (by simp only [Slice.len_val, UScalar.ofNatCore_val_eq]; omega)]
      simp only [Slice.len_val, UScalar.ofNatCore_val_eq]; omega
    have hlt2 : Std.Usize.wrapping_sub (Slice.len hs.rest) 4#usize < UScalar.cast .Usize L := by
      show (Std.Usize.wrapping_sub (Slice.len hs.rest) 4#usize).val < (UScalar.cast .Usize L).val
      rw [hsub, U32.cast_Usize_val_eq]; exact hr
    have hi0 := slice_index hs.rest 0#usize (by simp only [UScalar.ofNatCore_val_eq]; omega)
    have hi1 := slice_index hs.rest 1#usize (by simp only [UScalar.ofNatCore_val_eq]; omega)
    have hi2 := slice_index hs.rest 2#usize (by simp only [UScalar.ofNatCore_val_eq]; omega)
    have hi3 := slice_index hs.rest 3#usize (by simp only [UScalar.ofNatCore_val_eq]; omega)
    simp only [hb, UScalar.ofNatCore_val_eq] at hi0 hi1 hi2 hi3
    unfold fiat_shamir.proof.Hints.Insts.CoreIterTraitsIteratorIteratorSharedASliceU8.next
    simp only [hnot, ↓reduceIte, lift, bind_ok, hi0, hi1, hi2, hi3]
    simp only [List.cons_append, List.getElem_cons_zero, List.getElem_cons_succ]
    simp only [decode_prefix L a b c d habcd, hlt2, ↓reduceIte]

/-- Reading a hint: the four-byte little-endian length `L`, then those bytes. -/
theorem prover_hint_ok (vs : VS) (hp : vs.poison = none)
    (L : U32) (hint more : Slice U8) (hL : L.val = hint.val.length)
    (hb : vs.hints.rest.val = (core.num.U32.to_le_bytes L).val ++ hint.val ++ more.val) :
    fiat_shamir.verifier.VerifierState.prover_hint vs =
      .ok (.Ok hint, { vs with hints := ⟨more⟩, hints_read := Std.Usize.wrapping_add vs.hints_read 1#usize }) := by
  unfold fiat_shamir.verifier.VerifierState.prover_hint
  simp [hp, next_ok vs.hints L hint more hL hb, core.option.Option.ok_or, lift,
    fiat_shamir.verifier.VerifierState.guard, core.result.Result.Insts.CoreOpsTry.branch]

/-- A hint that is absent or cut short: fewer than four bytes remain, or the length they encode
runs past the bytes after them. -/
theorem prover_hint_missing (vs : VS) (hp : vs.poison = none)
    (h : vs.hints.rest.val.length < 4 ∨ ∃ (L : U32) (rest : List U8),
      vs.hints.rest.val = (core.num.U32.to_le_bytes L).val ++ rest ∧ rest.length < L.val) :
    fiat_shamir.verifier.VerifierState.prover_hint vs =
      .ok (.Err (.MissingHint vs.hints_read), { vs with poison := some (.MissingHint vs.hints_read) }) := by
  unfold fiat_shamir.verifier.VerifierState.prover_hint
  simp [hp, next_none vs.hints h, core.option.Option.ok_or,
    fiat_shamir.verifier.VerifierState.guard, core.option.Option.get_or_insert,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

/-- A poisoned transcript reads no hint and returns its error. -/
theorem prover_hint_poisoned (vs : VS) (e : TE) (hp : vs.poison = some e) :
    fiat_shamir.verifier.VerifierState.prover_hint vs = .ok (.Err e, vs) := by
  unfold fiat_shamir.verifier.VerifierState.prover_hint
  simp [hp]

/-! ## Decoding the hint -/

/-- Reading and decoding a hint: the decoder's value, or `InvalidHint` (indexed by the hints read
before it) poisoning the transcript. -/
theorem prover_hint_with_ok {T F : Type}
    (fn : core.ops.function.FnOnce F (Slice U8) (Option T))
    (vs vs1 : VS) (decode : F) (hint : Slice U8) (r : Option T)
    (hph : fiat_shamir.verifier.VerifierState.prover_hint vs = .ok (.Ok hint, vs1))
    (hp1 : vs1.poison = none) (hdec : fn.call_once decode hint = .ok r) :
    fiat_shamir.verifier.VerifierState.prover_hint_with fn vs decode = .ok (match r with
      | some x => (.Ok x, vs1)
      | none => (.Err (.InvalidHint vs.hints_read), { vs1 with poison := some (.InvalidHint vs.hints_read) })) := by
  unfold fiat_shamir.verifier.VerifierState.prover_hint_with
  cases r <;>
  simp [hph, hdec, core.result.Result.Insts.CoreOpsTry.branch, core.option.Option.ok_or,
    fiat_shamir.verifier.VerifierState.guard, core.option.Option.get_or_insert, hp1]

/-- A hint that cannot be read is not decoded; its error is returned. -/
theorem prover_hint_with_err {T F : Type}
    (fn : core.ops.function.FnOnce F (Slice U8) (Option T))
    (vs vs1 : VS) (decode : F) (e : TE)
    (hph : fiat_shamir.verifier.VerifierState.prover_hint vs = .ok (.Err e, vs1)) :
    fiat_shamir.verifier.VerifierState.prover_hint_with fn vs decode = .ok (.Err e, vs1) := by
  unfold fiat_shamir.verifier.VerifierState.prover_hint_with
  simp [hph, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

/-- The native decoder of a hint: the openings `open` authenticates from the paths `from_hint`
decodes for `n` distinct queries, or nothing. -/
def decodeOpen (hint : Slice U8) (n : Usize) (root : Digest) (depth : Usize) (queries : Slice Usize)
    (row_words leaf_words : Usize) : Result (Option merkle.Openings) := do
  let fo ← merkle.PrunedMerklePaths.from_hint hint n row_words
  match fo with
  | none => .ok none
  | some p => p.open root (Std.Usize.wrapping_shl 1#usize depth) queries row_words leaf_words

/-- The closure `authenticate` passes to `prover_hint_with` is `decodeOpen`. -/
theorem closure_eq (n : Usize) (root : Digest) (depth : Usize) (queries : Slice Usize)
    (row_words leaf_words : Usize) (hint : Slice U8) :
    verifier.authenticate.closure.Insts.CoreOpsFunctionFnOnceTupleShared6SliceU8OptionOpenings.call_once
      (n, row_words, root, depth, queries, leaf_words) hint =
      decodeOpen hint n root depth queries row_words leaf_words := by
  unfold verifier.authenticate.closure.Insts.CoreOpsFunctionFnOnceTupleShared6SliceU8OptionOpenings.call_once
    decodeOpen
  show Bind.bind (merkle.PrunedMerklePaths.from_hint hint n row_words) _ =
    Bind.bind (merkle.PrunedMerklePaths.from_hint hint n row_words) _
  congr 1
  funext fo
  cases fo <;> simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok, lift,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]

/-! ## Each opening's row -/

/-- Query `i`'s row: its leaf image `images[i*leaf_words, (i+1)*leaf_words)` with the first
`leaf_words - row_words` words (the zero prefix) dropped, for each query the openings hold. -/
def rowsOf (o : merkle.Openings) (row_words : Nat) : List (List U64) :=
  (List.range (o.images.val.length / o.leaf_words.val)).map fun i =>
    ((o.images.val.drop (i * o.leaf_words.val)).take o.leaf_words.val).drop (o.leaf_words.val - row_words)

private theorem list_clone_id {α : Type} (c : α → Result α) (hc : ∀ x, c x = .ok x) (l : List α) :
    List.clone c l = .ok ⟨l, rfl⟩ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.clone, List.mapM_with_length] at ih ⊢
    simp only [ih, hc, bind_tc_ok]
    rfl

private theorem to_vec_ok {α : Type} (c : core.clone.Clone α) (hc : ∀ x, c.clone x = .ok x) (s : Slice α) :
    ∃ w, alloc.slice.Slice.to_vec c s = .ok w ∧ w.val = s.val := by
  simp only [alloc.slice.Slice.to_vec, Slice.clone, list_clone_id c.clone hc, bind_tc_ok]
  exact ⟨_, rfl, by simp [alloc.vec.Vec.val]⟩

/-- Query `i`'s full leaf image. -/
theorem image_eq (o : merkle.Openings) (i : Usize)
    (hi : (i.val + 1) * o.leaf_words.val ≤ o.images.val.length) :
    ∃ s, merkle.Openings.image o i = .ok s ∧
      s.val = (o.images.val.drop (i.val * o.leaf_words.val)).take o.leaf_words.val := by
  have hl := o.images.slice.property
  have hm : (Std.Usize.wrapping_mul i o.leaf_words).val = i.val * o.leaf_words.val :=
    mul_val _ _ (by simp only [alloc.vec.Vec.val] at hi; rw [Nat.succ_mul] at hi; omega)
  have h1 : (Std.Usize.wrapping_mul i o.leaf_words).val ≤ o.images.slice.length := by
    rw [hm]; simp only [alloc.vec.Vec.val] at hi; show _ ≤ o.images.slice.val.length
    rw [Nat.succ_mul] at hi; omega
  have h2 : o.leaf_words.val ≤ (o.images.slice.drop (Std.Usize.wrapping_mul i o.leaf_words)).length := by
    show _ ≤ (o.images.slice.drop _).val.length
    simp only [Slice.drop, Slice.from_val, List.length_drop, hm]
    simp only [alloc.vec.Vec.val] at hi; rw [Nat.succ_mul] at hi; omega
  unfold merkle.Openings.image
  simp only [lift, bind_ok, alloc.vec.Vec.index, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index, h1, ↓reduceIte]
  simp only [core.slice.index.SliceIndexRangeToUsizeSlice.index, h2, ↓reduceIte]
  refine ⟨_, rfl, ?_⟩
  simp [Slice.drop, List.slice, hm, alloc.vec.Vec.val]

theorem rowsOf_length (o : merkle.Openings) (rw : Nat) :
    (rowsOf o rw).length = o.images.val.length / o.leaf_words.val := by
  simp [rowsOf]

theorem rows_loop_eq (o : merkle.Openings) (rw n : Usize) (hrw : rw.val ≤ o.leaf_words.val)
    (hn : n.val = o.images.val.length / o.leaf_words.val) :
    ∀ (k : Nat) (i : Usize) (rows : alloc.vec.Vec (alloc.vec.Vec U64)), n.val - i.val = k → i.val ≤ n.val →
      rows.val.map (·.val) = (rowsOf o rw.val).take i.val →
      ∃ rows', merkle.Openings.rows_loop o rw n rows i = .ok rows' ∧ rows'.val.map (·.val) = rowsOf o rw.val := by
  have hmax : o.images.val.length ≤ Usize.max := o.images.slice.property
  intro k
  induction k with
  | zero =>
    intro i rows hk hi hrows
    have hin : i.val = n.val := by omega
    refine ⟨rows, ?_, ?_⟩
    · unfold merkle.Openings.rows_loop
      apply loop_done
      have : ¬ (i < n) := by intro h; have : i.val < n.val := h; omega
      simp [merkle.Openings.rows_loop.body, this]
    · rw [hrows, hin, hn, ← rowsOf_length o rw.val, List.take_length]
  | succ k ih =>
    intro i rows hk hi hrows
    have hin : i.val < n.val := by omega
    have hlt : i < n := hin
    have hnl : n.val ≤ o.images.val.length := by rw [hn]; exact Nat.div_le_self _ _
    have hil : (i.val + 1) * o.leaf_words.val ≤ o.images.val.length := by
      have h1 : i.val + 1 ≤ o.images.val.length / o.leaf_words.val := by omega
      exact (Nat.mul_le_mul_right _ h1).trans (Nat.div_mul_le_self _ _)
    obtain ⟨s, hs, es⟩ := image_eq o i hil
    have hil' : i.val * o.leaf_words.val + o.leaf_words.val ≤ o.images.val.length := by
      rw [Nat.add_mul, Nat.one_mul] at hil; exact hil
    have hsl : s.val.length = o.leaf_words.val := by
      rw [es, List.length_take, List.length_drop]
      omega
    have hsl2 : s.length = o.leaf_words.val := hsl
    have hsub : (Std.Usize.wrapping_sub o.leaf_words rw).val = o.leaf_words.val - rw.val :=
      sub_val _ _ hrw
    have hfrom : core.slice.index.SliceIndexRangeFromUsizeSlice.index
        { start := Std.Usize.wrapping_sub o.leaf_words rw } s = .ok (s.drop (Std.Usize.wrapping_sub o.leaf_words rw)) := by
      have hle : (Std.Usize.wrapping_sub o.leaf_words rw).val ≤ s.length := by
        rw [hsub]; show _ ≤ s.val.length; omega
      simp only [core.slice.index.SliceIndexRangeFromUsizeSlice.index, hle, ↓reduceIte]
    obtain ⟨v, hv, ev⟩ := to_vec_ok primitives.field.gf2_64.F64.Insts.CoreCloneClone (fun _ => rfl)
      (s.drop (Std.Usize.wrapping_sub o.leaf_words rw))
    have hrl : rows.val.length = i.val := by
      have := congrArg List.length hrows
      rw [List.length_map, List.length_take, rowsOf_length] at this
      rw [this]; omega
    obtain ⟨rows1, hpush, epush⟩ := push_ok rows v (by rw [hrl]; omega)
    have hadd : (Std.Usize.wrapping_add i 1#usize).val = i.val + 1 :=
      add_val _ _ (by simp only [UScalar.ofNatCore_val_eq]; omega)
    have hbody : merkle.Openings.rows_loop.body o rw n rows i =
        .ok (.cont (rows1, Std.Usize.wrapping_add i 1#usize)) := by
      unfold merkle.Openings.rows_loop.body
      simp only [hlt, ↓reduceIte, hs, bind_ok, lift]
      simp only [core.slice.index.Slice.index, hfrom, bind_ok, hv, hpush]
    obtain ⟨rows', h', e'⟩ := ih (Std.Usize.wrapping_add i 1#usize) rows1 (by rw [hadd]; omega)
      (by rw [hadd]; omega) (by
        rw [epush, hadd, List.map_append, hrows, List.map_singleton, ev]
        rw [List.take_succ_eq_append_getElem (by rw [rowsOf_length]; omega)]
        congr 1
        simp only [Slice.drop, Slice.from_val, hsub, es, rowsOf, List.getElem_map, List.getElem_range])
    exact ⟨rows', by unfold merkle.Openings.rows_loop; rw [loop_cont hbody]; exact h', e'⟩

/-- `Openings::rows`: each opening's row, its leaf image with the zero prefix dropped. -/
theorem rows_eq (o : merkle.Openings) (rw : Usize) (h0 : 0 < o.leaf_words.val)
    (hrw : rw.val ≤ o.leaf_words.val) :
    ∃ rows, merkle.Openings.rows o rw = .ok rows ∧ rows.val.map (·.val) = rowsOf o rw.val := by
  obtain ⟨n, hn, en⟩ : ∃ n : Usize, alloc.vec.Vec.len o.images / o.leaf_words = Result.ok n ∧
      n.val = o.images.val.length / o.leaf_words.val := by
    obtain ⟨z, hz, hp⟩ := UScalar.div_bv_spec (alloc.vec.Vec.len o.images) (y := o.leaf_words)
      (by intro h; rw [h] at h0; simp at h0)
    exact ⟨z, hz, by rw [hp.1]; simp [alloc.vec.Vec.val]⟩
  obtain ⟨rows', h', e'⟩ := rows_loop_eq o rw n hrw en _ 0#usize
    (alloc.vec.Vec.with_capacity _ n) rfl (by simp) (by simp [alloc.vec.Vec.with_capacity])
  refine ⟨rows', ?_, e'⟩
  unfold merkle.Openings.rows merkle.Openings.len
  simp only [hn, bind_ok]
  exact h'

/-! ## The native `open_rows` -/

/-- The leaf count `open` is given: `1 << depth` is `2^depth` for a depth below the word size. -/
theorem shl_one_val (hword : UScalarTy.Usize.numBits = 64) (depth : Usize) (h : depth.val < 64) :
    (Std.Usize.wrapping_shl 1#usize depth).val = 2 ^ depth.val := by
  have e : (Std.Usize.wrapping_shl 1#usize depth).val =
      ((1#usize : Usize).bv <<< (depth.val % UScalarTy.Usize.numBits)).toNat := rfl
  have h1 : (1#usize : Usize).bv.toNat = 1 := by
    have : (1#usize : Usize).val = 1 := by simp
    exact this
  rw [e, BitVec.toNat_shiftLeft, h1, hword, Nat.mod_eq_of_lt h, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h)

/-- `open` over `2^depth` leaves applied to the decoded paths returns `oo`; no paths open nothing. -/
def OpensTo (fo : Option merkle.PrunedMerklePaths) (root : Digest) (depth : Usize) (queries : Slice Usize)
    (rw lw : Usize) (oo : Option merkle.Openings) : Prop :=
  match fo with
  | none => oo = none
  | some p => p.open root (Std.Usize.wrapping_shl 1#usize depth) queries rw lw = .ok oo

theorem decodeOpen_eq (hint : Slice U8) (n : Usize) (root : Digest) (depth : Usize) (queries : Slice Usize)
    (rw lw : Usize) (fo : Option merkle.PrunedMerklePaths)
    (hf : merkle.PrunedMerklePaths.from_hint hint n rw = .ok fo) (oo : Option merkle.Openings)
    (ho : OpensTo fo root depth queries rw lw oo) :
    decodeOpen hint n root depth queries rw lw = .ok oo := by
  unfold decodeOpen
  rw [hf, bind_ok]
  cases fo with
  | none => simp only [OpensTo] at ho; rw [ho]
  | some p => exact ho

theorem authenticate_eq (vs : VS) (hp : vs.poison = none) (root : Digest) (depth : Usize)
    (queries : Slice Usize) (rw lw : Usize) (L : U32) (hint more : Slice U8) (hL : L.val = hint.val.length)
    (hb : vs.hints.rest.val = (core.num.U32.to_le_bytes L).val ++ hint.val ++ more.val)
    (distinct : alloc.vec.Vec Usize) (hd : merkle.sorted_unique queries = .ok distinct)
    (oo : Option merkle.Openings)
    (hdec : decodeOpen hint (alloc.vec.Vec.len distinct) root depth queries rw lw = .ok oo) :
    verifier.authenticate vs root depth queries rw lw = .ok (match oo with
      | some o => (.Ok o, { vs with hints := ⟨more⟩, hints_read := Std.Usize.wrapping_add vs.hints_read 1#usize })
      | none => (.Err (.InvalidHint vs.hints_read),
          { vs with hints := ⟨more⟩, hints_read := Std.Usize.wrapping_add vs.hints_read 1#usize,
                    poison := some (.InvalidHint vs.hints_read) })) := by
  unfold verifier.authenticate
  rw [hd, bind_ok]
  refine (prover_hint_with_ok (F := verifier.authenticate.closure)
    verifier.authenticate.closure.Insts.CoreOpsFunctionFnOnceTupleShared6SliceU8OptionOpenings vs _
    (alloc.vec.Vec.len distinct, rw, root, depth, queries, lw) hint oo (prover_hint_ok vs hp L hint more hL hb)
    (by simp [hp])
    (by rw [← hdec]; exact closure_eq _ root depth queries rw lw hint)).trans ?_
  cases oo <;> rfl

/-- A hint that cannot be read is not decoded; `authenticate` returns its error. -/
theorem authenticate_err (vs vs1 : VS) (e : TE) (root : Digest) (depth : Usize)
    (queries : Slice Usize) (rw lw : Usize)
    (hph : fiat_shamir.verifier.VerifierState.prover_hint vs = .ok (.Err e, vs1)) :
    verifier.authenticate vs root depth queries rw lw = .ok (.Err e, vs1) := by
  obtain ⟨distinct, hd⟩ : ∃ d, merkle.sorted_unique queries = .ok d := ⟨_, rfl⟩
  unfold verifier.authenticate
  rw [hd, bind_ok]
  exact prover_hint_with_err (F := verifier.authenticate.closure) _ vs vs1 _ e hph

/-- The native `open_rows` on a transcript whose next hint is `hint` (its four-byte little-endian
length `L`, then its bytes) followed by `more`: it reads the hint, decodes it with `from_hint`
for the `n` distinct queries and authenticates it with `open` over `2^depth` leaves. When both
succeed it returns each opening's row, otherwise `InvalidHint` indexed by the hints read before
it, poisoning the transcript. -/
theorem open_rows_eq (vs : VS) (hp : vs.poison = none) (root : Digest) (depth : Usize)
    (queries : Slice Usize) (rw lw : Usize) (L : U32) (hint more : Slice U8) (hL : L.val = hint.val.length)
    (hb : vs.hints.rest.val = (core.num.U32.to_le_bytes L).val ++ hint.val ++ more.val)
    (distinct : alloc.vec.Vec Usize) (hd : merkle.sorted_unique queries = .ok distinct)
    (fo : Option merkle.PrunedMerklePaths)
    (hf : merkle.PrunedMerklePaths.from_hint hint (alloc.vec.Vec.len distinct) rw = .ok fo)
    (oo : Option merkle.Openings)
    (ho : OpensTo fo root depth queries rw lw oo)
    (hw : ∀ o, oo = some o → 0 < o.leaf_words.val ∧ rw.val ≤ o.leaf_words.val) :
    match oo with
    | some o => ∃ rows : alloc.vec.Vec (alloc.vec.Vec U64), verifier.open_rows_native vs root depth queries rw lw =
        Result.ok (core.result.Result.Ok rows,
          ({ vs with hints := ⟨more⟩, hints_read := Std.Usize.wrapping_add vs.hints_read 1#usize } : VS)) ∧
        rows.val.map (fun r : alloc.vec.Vec U64 => r.val) = rowsOf o rw.val
    | none => verifier.open_rows_native vs root depth queries rw lw =
        Result.ok (core.result.Result.Err (fiat_shamir.verifier.TranscriptError.InvalidHint vs.hints_read),
          ({ vs with hints := ⟨more⟩, hints_read := Std.Usize.wrapping_add vs.hints_read 1#usize,
                     poison := some (fiat_shamir.verifier.TranscriptError.InvalidHint vs.hints_read) } : VS)) := by
  have ha := authenticate_eq vs hp root depth queries rw lw L hint more hL hb distinct hd oo
    (decodeOpen_eq hint _ root depth queries rw lw fo hf oo ho)
  cases oo with
  | none =>
    unfold verifier.open_rows_native
    rw [ha]
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  | some o =>
    obtain ⟨h0, hrw⟩ := hw o rfl
    obtain ⟨rows, hr, er⟩ := rows_eq o rw h0 hrw
    refine ⟨rows, ?_, er⟩
    unfold verifier.open_rows_native
    rw [ha]
    simp [core.result.Result.Insts.CoreOpsTry.branch, hr]

/-- A hint that is absent or cut short is `MissingHint`, indexed by the hints read before it,
and poisons the transcript. -/
theorem open_rows_missing (vs : VS) (hp : vs.poison = none) (root : Digest) (depth : Usize)
    (queries : Slice Usize) (rw lw : Usize)
    (h : vs.hints.rest.val.length < 4 ∨ ∃ (L : U32) (rest : List U8),
      vs.hints.rest.val = (core.num.U32.to_le_bytes L).val ++ rest ∧ rest.length < L.val) :
    verifier.open_rows_native vs root depth queries rw lw =
      .ok (.Err (.MissingHint vs.hints_read), { vs with poison := some (.MissingHint vs.hints_read) }) := by
  unfold verifier.open_rows_native
  rw [authenticate_err vs _ _ root depth queries rw lw (prover_hint_missing vs hp h)]
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

/-- A poisoned transcript returns its error and is unchanged. -/
theorem open_rows_poisoned (vs : VS) (e : TE) (hp : vs.poison = some e) (root : Digest) (depth : Usize)
    (queries : Slice Usize) (rw lw : Usize) :
    verifier.open_rows_native vs root depth queries rw lw = .ok (.Err e, vs) := by
  unfold verifier.open_rows_native
  rw [authenticate_err vs _ _ root depth queries rw lw (prover_hint_poisoned vs e hp)]
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

end WhirAeneas.MerkleNative
