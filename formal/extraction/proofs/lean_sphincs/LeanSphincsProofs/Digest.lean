import LeanSphincsProofs.Common

/-!
# The message digest

`message_digest` (`h_msg`, then `digest_fields`) computes the statement's index and FORS leaves
(`Verification.messageDigest`, `digestIndex`, `digestForsLeaves`).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation Sphincs
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)
open lean_sphincs

namespace LeanSphincsProofs

namespace Digest

/-! ## Running a computation -/

/-- A loop whose body returns, keeps `inv` and decreases `μ` returns, with `Q`. -/
theorem loop_induct {α β : Type} (body : α → RustM (ControlFlow α β)) (inv : α → Prop)
    (Q : β → Prop) (μ : α → Nat)
    (hstep : ∀ x, inv x → ∃ r, body x = ok r ∧
      (match r with
        | .cont x' => inv x' ∧ μ x' < μ x
        | .done y => Q y)) :
    ∀ x, inv x → ∃ y, loop body x = ok y ∧ Q y := by
  intro x
  induction h : μ x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro hx
    obtain ⟨r, hr, hpost⟩ := hstep x hx
    rw [loop.eq_def, hr, Aeneas.Std.bind_ok]
    cases r with
    | cont x' =>
      obtain ⟨hi, hlt⟩ := hpost
      exact ih _ (h ▸ hlt) x' rfl hi
    | done y => exact ⟨y, rfl, hpost⟩

/-- `usize` has at least 32 bits. -/
theorem pow32_le : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
  cases System.Platform.numBits_eq with
  | inl h => simp [h]
  | inr h => simp [h]

/-! ## The library models and the bytes (as in `Hash.lean`) -/

/-! ## Machine words -/

theorem usize_size_ge : 2 ^ 32 ≤ Usize.size := by
  rw [Usize.size_def]
  exact Nat.pow_le_pow_right (by omega)
    (by cases System.Platform.numBits_eq <;> simp [Usize.numBits, *])

/-! ## The constants -/

theorem MD_BYTES_eq : ∃ v, internals.MD_BYTES = ok v ∧ v.val = 30 := by
  apply ok_of_triple
  hax_mvcgen [internals.MD_BYTES, core.num.Usize.div_ceil]
  all_goals simp [internals.FORS_TREES, internals.FORS_HEIGHT] at *
  all_goals scalar_tac

theorem H_eq : ∃ v, internals.H = ok v ∧ v.val = 26 := by
  apply ok_of_triple
  hax_mvcgen [internals.H]
  all_goals simp [internals.LAYER_HEIGHTS] at *
  all_goals scalar_tac

/-- The bit `digest_fields` reads at position `p`: each byte's most significant bit first. -/
def bitAt (d : List Std.U8) (p : Nat) : Nat := (d[p / 8]!).val / 2 ^ (7 - p % 8) % 2

theorem bit_call (d : Array Std.U8 64#usize) (p : Std.Usize) (hp : p.val < 512) :
    ∃ r, scheme.digest_fields.closure.Insts.CoreOpsFunctionFnTupleUsizeUsize.call d p = ok r ∧
      r.val = bitAt d.val p.val := by
  apply ok_of_triple
  hax_mvcgen [scheme.digest_fields.closure.Insts.CoreOpsFunctionFnTupleUsizeUsize.call,
    core.Usize.Insts.CoreConvertFromU8.from]
  case vc1.hQ =>
    rename_i r4 h4 r3 h3 r2 h2 r1 h1 _ r h _ _
    obtain ⟨hlt, rfl⟩ := h3
    have e4 : r4.val = p.val / 8 := by simpa using h4
    have e1 : r1.val = 7 - p.val % 8 := by scalar_tac
    simp only [bitAt]
    rw [getElem!_pos d.val _ (by simpa [e4] using hlt)]
    simp [UScalar.cast_val_eq, UScalar.val_and, h, e1, e4, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
    apply Nat.mod_eq_of_lt
    have := pow32_le
    omega
  all_goals (simp at *; scalar_tac)

theorem bit_triple (d : Array Std.U8 64#usize) (p : Std.Usize) (hp : p.val < 512) :
    ⦃ ⌜ True ⌝ ⦄
    scheme.digest_fields.closure.Insts.CoreOpsFunctionFnTupleUsizeUsize.call d p
    ⦃ ⇓ r => ⌜ r.val = bitAt d.val p.val ⌝ ⦄ := by
  obtain ⟨r, hr, h⟩ := bit_call d p hp
  exact Hax.triple_of_ok hr h

theorem bitAt_lt (d : List Std.U8) (p : Nat) : bitAt d p < 2 := Nat.mod_lt _ (by decide)

/-- The leaf of FORS tree `c` after `n` of its bits, most significant first. -/
def leafFold (d : List Std.U8) (c n : Nat) : Nat :=
  (List.range n).foldl (fun v j ↦ 2 * v + bitAt d (10 * c + j)) 0

theorem inner_call (d : Array Std.U8 64#usize) (c v j : Std.Usize) (hc : c.val < 24)
    (hj : j.val < 10) (hv : v.val < 2 ^ 10) :
    ∃ r, scheme.digest_fields.closure_1.closure.Insts.CoreOpsFunctionFnMutPairUsizeUsizeUsize.call_mut
        ((d, c) : scheme.digest_fields.closure_1.closure) (v, j) =
          ok (r, ((d, c) : scheme.digest_fields.closure_1.closure)) ∧
      r.val = 2 * v.val + bitAt d.val (10 * c.val + j.val) := by
  have := ok_of_triple (x := scheme.digest_fields.closure_1.closure.Insts.CoreOpsFunctionFnMutPairUsizeUsizeUsize.call_mut
        ((d, c) : scheme.digest_fields.closure_1.closure) (v, j))
      (P := fun r => r.2 = ((d, c) : scheme.digest_fields.closure_1.closure) ∧
        r.1.val = 2 * v.val + bitAt d.val (10 * c.val + j.val)) (by
    hax_mvcgen [scheme.digest_fields.closure_1.closure.Insts.CoreOpsFunctionFnMutPairUsizeUsizeUsize.call_mut,
      bit_triple]
    case vc2.hQ =>
      rename_i r3 h3 _ _ r2 h2 r1 h1 rb hb
      refine ⟨rfl, ?_⟩
      have e1 : r1.val = 10 * c.val + j.val := by simp [internals.FORS_HEIGHT] at h2; omega
      have e3 : r3.val = v.val <<< 1 := by
        have : (1#i32).toNat = 1 := by decide
        rw [h3, this, Nat.shiftLeft_eq]
        apply Nat.mod_eq_of_lt
        have := usize_size_ge
        omega
      rw [UScalar.val_or, hb, e1, e3, ← Nat.shiftLeft_add_eq_or_of_lt (bitAt_lt _ _), Nat.shiftLeft_eq]
      omega
    all_goals (simp [internals.FORS_HEIGHT] at *; first | scalar_tac | (have := numBits_ge; omega)))
  obtain ⟨⟨r, s⟩, hr, hs, hval⟩ := this
  subst hs
  exact ⟨r, hr, hval⟩

/-- A fold over a range, by an invariant `g` of the position and the accumulator. -/
theorem range_fold {B F : Type} (inst : core.ops.function.FnMut F (B × Std.Usize) B) (f : F)
    (s e : Std.Usize) (init : B) (g : Nat → B → Prop) (hse : s.val ≤ e.val) (h0 : g s.val init)
    (hstep : ∀ (i : Std.Usize) (acc : B), s.val ≤ i.val → i.val < e.val → g i.val acc →
      ∃ r, inst.call_mut f (acc, i) = ok (r, f) ∧ g (i.val + 1) r) :
    ∃ r, core.iter.traits.iterator.Iterator.fold.default
        (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator core.Usize.Insts.CoreIterRangeStep)
        inst { start := s, «end» := e } init f = ok r ∧ g e.val r := by
  unfold core.iter.traits.iterator.Iterator.fold.default core.iter.traits.iterator.iter_fold
    core.iter.traits.iterator.iter_fold_loop
  refine loop_induct _
    (fun x : core.ops.range.Range Std.Usize × F × B =>
      x.2.1 = f ∧ x.1.«end» = e ∧ s.val ≤ x.1.start.val ∧ x.1.start.val ≤ e.val ∧
        g x.1.start.val x.2.2)
    (fun r => g e.val r) (fun x => e.val - x.1.start.val) ?_ _ ⟨rfl, rfl, Nat.le_refl _, hse, h0⟩
  rintro ⟨⟨i, e'⟩, f', acc⟩ ⟨hf, he, hsi, hie, hg⟩
  simp only at hf he hsi hie hg
  subst hf he
  by_cases hlt : i.val < e'.val
  · obtain ⟨s', hs', hnext⟩ := range_next_lt i e' hlt
    obtain ⟨r, hr, hg'⟩ := hstep i acc hsi hlt hg
    refine ⟨.cont ({ start := s', «end» := e' }, f', r), ?_, ?_⟩
    · simp [core.iter.traits.iterator.iter_fold_loop.body,
        core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator, hnext, hr]
    · refine ⟨⟨rfl, rfl, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [hs'] <;> omega
  · have hnext := range_next_ge i e' (by omega)
    refine ⟨.done acc, ?_, ?_⟩
    · simp [core.iter.traits.iterator.iter_fold_loop.body,
        core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator, hnext]
    · have : i.val = e'.val := by omega
      simpa [this] using hg

theorem leafFold_succ (d : List Std.U8) (c n : Nat) :
    leafFold d c (n + 1) = 2 * leafFold d c n + bitAt d (10 * c + n) := by
  simp [leafFold, List.range_succ]

theorem leafFold_lt (d : List Std.U8) (c n : Nat) : leafFold d c n < 2 ^ n := by
  induction n with
  | zero => simp [leafFold]
  | succ n ih =>
    have := bitAt_lt d (10 * c + n)
    rw [leafFold_succ, Nat.pow_succ]
    omega

/-- The `from_fn` closure of `digest_fields`: the leaf of FORS tree `c`. -/
theorem leaf_call (d : Array Std.U8 64#usize) (c : Std.Usize) (hc : c.val < 24) :
    ∃ r, scheme.digest_fields.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut d c =
        ok (r, d) ∧ r.val = leafFold d.val c.val 10 := by
  obtain ⟨r, hr, hg⟩ := range_fold
    scheme.digest_fields.closure_1.closure.Insts.CoreOpsFunctionFnMutPairUsizeUsizeUsize
    ((d, c) : scheme.digest_fields.closure_1.closure) 0#usize internals.FORS_HEIGHT 0#usize
    (fun n acc => acc.val = leafFold d.val c.val n) (by simp) (by simp [leafFold])
    (fun i acc _ hi hacc => by
      have hi' : i.val < 10 := by simpa [internals.FORS_HEIGHT] using hi
      have hlt := leafFold_lt d.val c.val i.val
      have hp : 2 ^ i.val ≤ 2 ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
      obtain ⟨r, hr, hv⟩ := inner_call d c acc i hc hi' (by omega)
      exact ⟨r, hr, by rw [hv, hacc, leafFold_succ]⟩)
  refine ⟨r, ?_, by simpa [internals.FORS_HEIGHT] using hg⟩
  simp only [scheme.digest_fields.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut, hr,
    Aeneas.Std.bind_ok]

/-- The leaves `digest_fields` reads. -/
theorem leaves_from_fn (d : Array Std.U8 64#usize) :
    ∃ a : Array Std.Usize 24#usize, core.array.from_fn 24#usize
        scheme.digest_fields.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeUsize d = ok a ∧
      ∀ c : Nat, c < 24 → (a.val[c]!).val = leafFold d.val c 10 := by
  have hidx : ∀ k : Nat, k < 24 →
      ((BitVec.ofNat UScalarTy.Usize.numBits k)#uscalar : Std.Usize).val = k := by
    intro k hk
    show (BitVec.ofNat UScalarTy.Usize.numBits k).toNat = k
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := pow32_le
    omega
  have hspec := rust_primitives.slice.array_from_fn_spec 24#usize
    scheme.digest_fields.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeUsize d (fun k hk => by
      obtain ⟨r, hr, _⟩ := leaf_call d _ (by rw [hidx k (by simpa using hk)]; simpa using hk)
      exact Hax.triple_of_ok hr rfl)
  obtain ⟨a, ha, hpost⟩ := ok_of_triple hspec
  refine ⟨a, ha, fun c hc => ?_⟩
  obtain ⟨r, hr, hv⟩ := leaf_call d _ (by rw [hidx c hc]; exact hc)
  have hrc : r = a.val[c]'(by simpa using hc) := by
    simpa using Hax.triple_noThrow_elim (hpost c (by simpa using hc)) hr
  rw [getElem!_pos a.val c (by simpa using hc), ← hrc, hv, hidx c hc]

/-- A fold over a slice's iterator, by an invariant `g` of what was read and the accumulator. -/
theorem seq_fold {T B F : Type} (inst : core.ops.function.FnMut F (B × T) B) (f : F)
    (all : List T) (g : List T → B → Prop)
    (hstep : ∀ (pre : List T) (x : T) (suf : List T) (acc : B), pre ++ x :: suf = all → g pre acc →
      ∃ r, inst.call_mut f (acc, x) = ok (r, f) ∧ g (pre ++ [x]) r)
    (it : core.slice.iter.Iter T) (init : B) (hit : it.val = all) (h0 : g [] init) :
    ∃ r, core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold inst it init f =
      ok r ∧ g all r := by
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
    core.iter.traits.iterator.Iterator.fold.default core.iter.traits.iterator.iter_fold
    core.iter.traits.iterator.iter_fold_loop
  refine loop_induct _
    (fun x : core.slice.iter.Iter T × F × B =>
      x.2.1 = f ∧ ∃ pre, pre ++ x.1.val = all ∧ g pre x.2.2)
    (fun r => g all r) (fun x => x.1.val.length) ?_ _ ⟨rfl, [], by simpa using hit, h0⟩
  rintro ⟨it', f', acc⟩ ⟨hf, pre, hpre, hg⟩
  simp only at hf hpre hg
  subst hf
  cases hval : it'.val with
  | nil =>
    refine ⟨.done acc, ?_, ?_⟩
    · have hlen : Slice.len it' = 0#usize := by
        have : it'.length = 0 := by simp [Slice.length, hval]
        scalar_tac
      simp [core.iter.traits.iterator.iter_fold_loop.body,
        core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
        rust_primitives.sequence.seq_len, hlen]
    · rw [hval] at hpre
      simpa [← hpre] using hg
  | cons x xs =>
    obtain ⟨r, hr, hg'⟩ := hstep pre x xs acc (by rw [← hval]; exact hpre) hg
    have hlen : ¬ Slice.len it' = 0#usize := by
      intro h
      have : it'.length = 0 := by scalar_tac
      simp [Slice.length, hval] at this
    have hrem : ∃ s : core.slice.iter.Iter T, s.val = xs ∧
        rust_primitives.sequence.seq_remove it' 0#usize = ok (x, s) := by
      simp [rust_primitives.sequence.seq_remove, hval]
      exact ⟨_, by simp, rfl⟩
    obtain ⟨s, hs, hrem⟩ := hrem
    refine ⟨.cont (s, f', r), ?_, ?_⟩
    · simp only [core.iter.traits.iterator.iter_fold_loop.body,
        core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
        rust_primitives.sequence.seq_len, Aeneas.Std.bind_ok, hlen, ite_false, hrem]
      simp [hr]
    · refine ⟨⟨rfl, pre ++ [x], ?_, hg'⟩, ?_⟩
      · simp only [hs, List.append_assoc, List.singleton_append, ← hpre, hval]
      · simp [hs]

/-- A slice's iterator is the slice. -/
theorem iter_eq {T : Type} (s : Slice T) :
    core.slice.Slice.iter s = ok (s : core.slice.iter.Iter T) := by
  unfold core.slice.Slice.iter
  exact Aeneas.Std.bind_ok _ _

/-- A byte string as a big-endian number (`int` of `digest_fields`). -/
def beInt (l : List Std.U8) : Nat := l.foldl (fun v b ↦ 256 * v + b.val) 0

theorem beInt_append_singleton (l : List Std.U8) (b : Std.U8) :
    beInt (l ++ [b]) = 256 * beInt l + b.val := by
  simp [beInt]

theorem beInt_lt (l : List Std.U8) : beInt l < 256 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [beInt]
  | append_singleton l b ih =>
    have hb : b.val < 256 := by scalar_tac
    rw [beInt_append_singleton, List.length_append, List.length_singleton, Nat.pow_succ]
    omega

theorem int_step (c : scheme.digest_fields.closure_2.closure) (v : Std.U64) (b : Std.U8)
    (hv : v.val < 2 ^ 24) :
    ∃ r, scheme.digest_fields.closure_2.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U8U64.call_mut
        c (v, b) = ok (r, c) ∧ r.val = 256 * v.val + b.val := by
  have := ok_of_triple (x := scheme.digest_fields.closure_2.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U8U64.call_mut
        c (v, b)) (P := fun r => r.2 = c ∧ r.1.val = 256 * v.val + b.val) (by
    hax_mvcgen [scheme.digest_fields.closure_2.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U8U64.call_mut,
      core.U64.Insts.CoreConvertFromU8.from]
    case vc1.hQ =>
      rename_i r h _ _
      refine ⟨trivial, ?_⟩
      have hb : b.val < 2 ^ 8 := by scalar_tac
      have e8 : (8#i32).toNat = 8 := by decide
      have hs : U64.size = 2 ^ 64 := by scalar_tac
      have e : r.val = v.val <<< 8 := by
        rw [h, e8, Nat.shiftLeft_eq, hs]
        apply Nat.mod_eq_of_lt
        omega
      have hm : b.val % 2 ^ UScalarTy.U64.numBits = b.val :=
        Nat.mod_eq_of_lt (by show b.val < 2 ^ 64; omega)
      rw [UScalar.val_or, e, UScalar.cast_val_eq, hm, ← Nat.shiftLeft_add_eq_or_of_lt hb,
        Nat.shiftLeft_eq]
      omega)
  obtain ⟨⟨r, s⟩, hr, hs, hval⟩ := this
  subst hs
  exact ⟨r, hr, hval⟩

theorem array_index_range {N : Std.Usize} (a : Array Std.U8 N) (s e : Std.Usize)
    (hse : s.val ≤ e.val) (he : e.val ≤ N.val) :
    ∃ sl : Slice Std.U8, core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)) a
        { start := s, «end» := e } = ok sl ∧ sl.val = (a.val.drop s.val).take (e.val - s.val) := by
  simp [core.Array.Insts.CoreOpsIndexIndex.index, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, hse, he,
    Slice.subslice]
  simp [List.slice]

theorem one_shl_u64 (bits : Std.Usize) (hb : bits.val ≤ 18) :
    (1#u64).val <<< bits.val % U64.size = 2 ^ bits.val := by
  have hs : U64.size = 2 ^ 64 := by scalar_tac
  have hp : 2 ^ bits.val ≤ 2 ^ 18 := Nat.pow_le_pow_right (by omega) hb
  have h1 : (1#u64).val = 1 := by decide
  rw [hs, h1, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (by omega)

/-- The mask of `int`: the low `bits` bits. -/
theorem mask_eq (x : Std.U64) (bits : Std.Usize) (hb : bits.val ≤ 18) :
    ∃ r, (do
        let i2 ← 1#u64 <<< bits
        let i3 ← i2 - 1#u64
        ok (x &&& i3) : RustM Std.U64) = ok r ∧ r.val = x.val % 2 ^ bits.val := by
  apply ok_of_triple
  hax_mvcgen
  case vc1.hQ =>
    rename_i r1 h1 _ _ r h _
    have e1 : r1.val = 2 ^ bits.val := by rw [h1, one_shl_u64 bits hb]
    have e : r.val = 2 ^ bits.val - 1 := by rw [h, e1]; simp
    rw [UScalar.val_and, e, Nat.and_two_pow_sub_one_eq_mod]
  case vc2.h_fail =>
    rename_i r h _ _ hlt
    rw [one_shl_u64 bits hb] at h
    have := Nat.two_pow_pos bits.val
    simp at hlt
    omega
  simp at *; scalar_tac

theorem int_call (s : Slice Std.U8) (bits : Std.Usize) (hlen : s.val.length ≤ 3)
    (hb : bits.val ≤ 18) :
    ∃ r, scheme.digest_fields.closure_2.Insts.CoreOpsFunctionFnPairShared0SliceU8UsizeU64.call ()
        (s, bits) = ok r ∧ r.val = beInt s.val % 2 ^ bits.val := by
  obtain ⟨v, hv, hg⟩ := seq_fold
    scheme.digest_fields.closure_2.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U8U64 ()
    s.val (fun pre acc => acc.val = beInt pre)
    (fun pre x suf acc hall hacc => by
      have hl : pre.length ≤ 2 := by
        have := congrArg List.length hall
        simp at this
        omega
      have hlt := beInt_lt pre
      have hp : 256 ^ pre.length ≤ 256 ^ 2 := Nat.pow_le_pow_right (by omega) hl
      obtain ⟨r, hr, hval⟩ := int_step () acc x (by omega)
      exact ⟨r, hr, by rw [hval, hacc, beInt_append_singleton]⟩)
    s 0#u64 rfl (by simp [beInt])
  obtain ⟨r, hr, hval⟩ := mask_eq v bits hb
  refine ⟨r, ?_, by rw [hval, hg]⟩
  simp only [scheme.digest_fields.closure_2.Insts.CoreOpsFunctionFnPairShared0SliceU8UsizeU64.call,
    iter_eq]
  show (do
    let i ← (ok s : RustM (core.slice.iter.Iter Std.U8))
    let i1 ← core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
      scheme.digest_fields.closure_2.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U8U64 i 0#u64 ()
    let i2 ← 1#u64 <<< bits
    let i3 ← i2 - 1#u64
    ok (i1 &&& i3)) = ok r
  erw [Aeneas.Std.bind_ok, hv, Aeneas.Std.bind_ok]
  exact hr

/-- A computation known to return, as a triple. -/
theorem triple_of_ex {α : Type} {x : RustM α} {P : α → Prop} (h : ∃ v, x = ok v ∧ P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  obtain ⟨v, hv, hP⟩ := h
  exact Hax.triple_of_ok hv hP

theorem MD_BYTES_triple : ⦃ ⌜ True ⌝ ⦄ internals.MD_BYTES ⦃ ⇓ r => ⌜ r.val = 30 ⌝ ⦄ :=
  triple_of_ex MD_BYTES_eq

theorem H_triple : ⦃ ⌜ True ⌝ ⦄ internals.H ⦃ ⇓ r => ⌜ r.val = 26 ⌝ ⦄ := triple_of_ex H_eq

theorem TREE_INDEX_BYTES_triple :
    ⦃ ⌜ True ⌝ ⦄ internals.TREE_INDEX_BYTES ⦃ ⇓ r => ⌜ r.val = 3 ⌝ ⦄ := by
  hax_mvcgen [internals.TREE_INDEX_BYTES, core.num.Usize.div_ceil, H_triple]
  all_goals simp [internals.LAYER_HEIGHTS] at *
  all_goals scalar_tac

theorem LEAF_INDEX_BYTES_triple :
    ⦃ ⌜ True ⌝ ⦄ internals.LEAF_INDEX_BYTES ⦃ ⇓ r => ⌜ r.val = 1 ⌝ ⦄ := by
  hax_mvcgen [internals.LEAF_INDEX_BYTES, core.num.Usize.div_ceil]
  all_goals simp [internals.LAYER_HEIGHTS] at *
  all_goals scalar_tac

theorem DIGEST_BYTES_triple :
    ⦃ ⌜ True ⌝ ⦄ internals.DIGEST_BYTES ⦃ ⇓ r => ⌜ r.val = 34 ⌝ ⦄ := by
  hax_mvcgen [internals.DIGEST_BYTES, MD_BYTES_triple, TREE_INDEX_BYTES_triple,
    LEAF_INDEX_BYTES_triple]
  all_goals scalar_tac

theorem DIGEST_CALLS_triple :
    ⦃ ⌜ True ⌝ ⦄ internals.DIGEST_CALLS ⦃ ⇓ r => ⌜ r.val = 2 ⌝ ⦄ := by
  hax_mvcgen [internals.DIGEST_CALLS, core.num.Usize.div_ceil, DIGEST_BYTES_triple]
  all_goals simp at *
  all_goals scalar_tac

theorem leaves_triple (d : Array Std.U8 64#usize) :
    ⦃ ⌜ True ⌝ ⦄
    core.array.from_fn 24#usize
      scheme.digest_fields.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeUsize d
    ⦃ ⇓ a => ⌜ ∀ c : Nat, c < 24 → (a.val[c]!).val = leafFold d.val c 10 ⌝ ⦄ :=
  triple_of_ex (leaves_from_fn d)

theorem index_range_triple {N : Std.Usize} (a : Array Std.U8 N) (s e : Std.Usize)
    (hse : s.val ≤ e.val) (he : e.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreOpsIndexIndex.index
      (core.Slice.Insts.CoreOpsIndexIndex
        (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)) a
      { start := s, «end» := e }
    ⦃ ⇓ sl => ⌜ sl.val = (a.val.drop s.val).take (e.val - s.val) ⌝ ⦄ :=
  triple_of_ex (array_index_range a s e hse he)

theorem int_triple (s : Slice Std.U8) (bits : Std.Usize) (hlen : s.val.length ≤ 3)
    (hb : bits.val ≤ 18) :
    ⦃ ⌜ True ⌝ ⦄
    scheme.digest_fields.closure_2.Insts.CoreOpsFunctionFnPairShared0SliceU8UsizeU64.call ()
      (s, bits)
    ⦃ ⇓ r => ⌜ r.val = beInt s.val % 2 ^ bits.val ⌝ ⦄ :=
  triple_of_ex (int_call s bits hlen hb)

/-- `digest_fields`: the index and the leaves, as numbers read from the digest's bytes. -/
theorem digest_fields_eq (d : Array Std.U8 64#usize) :
    ∃ idx leaves, scheme.digest_fields d = ok (idx, leaves) ∧
      idx.val = beInt ((d.val.drop 30).take 3) % 2 ^ 18 * 2 ^ 8 +
        beInt ((d.val.drop 33).take 1) % 2 ^ 8 ∧
      ∀ c : Nat, c < 24 → (leaves.val[c]!).val = leafFold d.val c 10 := by
  have := ok_of_triple (x := scheme.digest_fields d) (P := fun r =>
      r.1.val = beInt ((d.val.drop 30).take 3) % 2 ^ 18 * 2 ^ 8 +
        beInt ((d.val.drop 33).take 1) % 2 ^ 8 ∧
      ∀ c : Nat, c < 24 → (r.2.val[c]!).val = leafFold d.val c 10) (by
    hax_mvcgen [scheme.digest_fields, leaves_triple, MD_BYTES_triple, TREE_INDEX_BYTES_triple,
      DIGEST_BYTES_triple, H_triple, index_range_triple, int_triple]
    case vc9.hQ =>
      simp [internals.LAYER_HEIGHTS] at *
      rename_i lv i hi i1 hi1 i2 hi2 s hs h8v i4 hi4 i5 hi5 _ tree htree i6 hi6 i7 hi7 s1 hs1
        leaf hleaf r hr _ hl h8 _
      subst h8
      refine ⟨?_, hl⟩
      have e8 : (8#usize).val = 8 := by decide
      have ei5 : i5.val = 18 := by rw [hi5, hi4, e8]
      have es : s.val = List.take 3 (List.drop 30 d.val) := by rw [hs, hi2, hi, hi1]
      have es1 : s1.val = List.take 1 (List.drop 33 d.val) := by rw [hs1, hi7, hi6, hi, hi1]
      rw [hr, htree, hleaf, es, es1, ei5, e8]
      generalize beInt (List.take 3 (List.drop 30 d.val)) = X
      generalize beInt (List.take 1 (List.drop 33 d.val)) = Y
      have hA : X % 2 ^ 18 < 2 ^ 18 := Nat.mod_lt _ (by decide)
      have hB : Y % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
      have hs64 : U64.size = 2 ^ 64 := by scalar_tac
      have hm : (X % 2 ^ 18) <<< 8 % U64.size = (X % 2 ^ 18) <<< 8 := by
        rw [Nat.shiftLeft_eq, hs64]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hm, ← Nat.shiftLeft_add_eq_or_of_lt hB, Nat.shiftLeft_eq]
      norm_num
    all_goals simp [internals.LAYER_HEIGHTS] at *
    all_goals scalar_tac)
  obtain ⟨⟨idx, leaves⟩, h, h1, h2⟩ := this
  exact ⟨idx, leaves, h, h1, h2⟩

/-! ## `h_msg` -/

theorem mul32 (i : Std.Usize) (hi : i.val ≤ 2) : ∃ r, 32#usize * i = ok r ∧ r.val = 32 * i.val := by
  apply ok_of_triple
  hax_mvcgen
  scalar_tac

theorem add1 (i : Std.Usize) (hi : i.val ≤ 2) : ∃ r, i + 1#usize = ok r ∧ r.val = i.val + 1 := by
  apply ok_of_triple
  hax_mvcgen
  scalar_tac

/-- Digest call `i`'s bytes: the hash of what the hasher holds and the call's counter. -/
def callBytes (π : KeccakState → KeccakState) (Z : List UInt8) (i : Nat) : List UInt8 :=
  hashBytes π (Z ++ bigEndianBytes 4 (BitVec.ofNat 32 i))

theorem h_msg_body {π : KeccakState → KeccakState} (H : HasherSpec π)
    (hclone : ∀ h, keccak256.Hasher.Insts.CoreCloneClone.clone h = ok h)
    (z : keccak256.Hasher) (Z : List UInt8) (hz : H.Absorbed z Z) (i e : Std.Usize)
    (hi : i.val < e.val) (he : e.val = 2) (out : Array Std.U8 64#usize) :
    ∃ (s' : Std.Usize) (out' : Array Std.U8 64#usize),
      hash.h_msg_loop.body z { start := i, «end» := e } out =
        ok (.cont ({ start := s', «end» := e }, out')) ∧ s'.val = i.val + 1 ∧
      (callBytes π Z i.val).length = 32 ∧
      bytes out'.val = (bytes out.val).take (32 * i.val) ++ callBytes π Z i.val ++
        (bytes out.val).drop (32 * (i.val + 1)) := by
  obtain ⟨s', hs', hnext⟩ := range_next_lt i e hi
  obtain ⟨h1, back, hup, hA1, -⟩ := H.update z Z
    (Aeneas.Std.core.num.U32.to_be_bytes (UScalar.cast .U32 i)).to_slice hz
  obtain ⟨call, hfin, hcall⟩ := H.finalize h1 _ hA1
  obtain ⟨i2, hi2, hi2v⟩ := mul32 i (by omega)
  obtain ⟨i3, hi3, hi3v⟩ := add1 i (by omega)
  obtain ⟨i4, hi4, hi4v⟩ := mul32 i3 (by omega)
  obtain ⟨s1, wb, hidx, hs1, hwb⟩ := array_index_mut_range out i2 i4 (by omega)
    (by have : (64#usize).val = 64 := by decide
        omega)
  have hcopy := copy_from_slice_u8 s1 call.to_slice (by
    simp [Slice.length, hs1, List.slice]
    omega)
  have hcall' : bytes call.val = callBytes π Z i.val := by
    rw [callBytes, ← cast_u32_bv, ← bytes_u32_to_be_bytes]
    simpa using hcall
  refine ⟨s', wb call.to_slice, ?_, hs', ?_, ?_⟩
  · simp [hash.h_msg_loop.body, hnext, hclone, u32_to_be_bytes, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice, hup, hfin, hi2, hi3, hi4, hidx, hcopy, lift]
  · rw [← hcall']
    simp [bytes]
  · rw [hwb, ← hcall']
    simp [bytes, List.setSlice!, hi2v]
    have hm : min 32 (64 - 32 * i.val) = 32 := by omega
    rw [hm, List.take_of_length_le (by simp), show 32 * i.val + 32 = 32 * (i.val + 1) by omega]

theorem h_msg_loop_eq {π : KeccakState → KeccakState} (H : HasherSpec π)
    (hclone : ∀ h, keccak256.Hasher.Insts.CoreCloneClone.clone h = ok h)
    (z : keccak256.Hasher) (Z : List UInt8) (hz : H.Absorbed z Z) (e : Std.Usize)
    (he : e.val = 2) (out0 : Array Std.U8 64#usize) :
    ∃ out, hash.h_msg_loop { start := 0#usize, «end» := e } z out0 = ok out ∧
      (∀ j < 2, (callBytes π Z j).length = 32) ∧
      bytes out.val = callBytes π Z 0 ++ callBytes π Z 1 := by
  unfold hash.h_msg_loop
  obtain ⟨out, hout, hlen, hb⟩ := loop_induct
    (fun x : core.ops.range.Range Std.Usize × Array Std.U8 64#usize =>
      hash.h_msg_loop.body z x.1 x.2)
    (fun x => x.1.«end» = e ∧ x.1.start.val ≤ 2 ∧
      (∀ j < x.1.start.val, (callBytes π Z j).length = 32) ∧
      (bytes x.2.val).take (32 * x.1.start.val) =
        (List.range x.1.start.val).flatMap (callBytes π Z))
    (fun out => (∀ j < 2, (callBytes π Z j).length = 32) ∧
      bytes out.val = (List.range 2).flatMap (callBytes π Z))
    (fun x => 2 - x.1.start.val)
    (by
      rintro ⟨⟨i, e'⟩, out⟩ ⟨hee, hi2, hl, hb⟩
      simp only at hee hi2 hl hb
      subst hee
      by_cases hlt : i.val < 2
      · obtain ⟨s', out', hbody, hs', hcl, hb'⟩ :=
          h_msg_body H hclone z Z hz i e' (by omega) he out
        refine ⟨_, hbody, ⟨rfl, by simp only [hs']; omega, ?_, ?_⟩, by simp only [hs']; omega⟩
        · intro j hj
          simp only [hs'] at hj
          by_cases hji : j < i.val
          · exact hl j hji
          · have : j = i.val := by omega
            exact this ▸ hcl
        · simp only [hs', hb', List.range_succ, List.flatMap_append, List.flatMap_singleton,
            ← hb]
          apply List.take_left'
          have : (bytes out.val).length = 64 := by simp [bytes]
          simp [hcl]
          omega
      · have hi : i.val = 2 := by omega
        refine ⟨.done out, ?_, ?_⟩
        · simp [hash.h_msg_loop.body, range_next_ge i e' (by omega)]
        · refine ⟨fun j hj => hl j (by omega), ?_⟩
          rw [← hi, ← hb, List.take_of_length_le (by simp [bytes, hi])])
    ({ start := 0#usize, «end» := e }, out0) ⟨rfl, by simp, by simp, by simp⟩
  exact ⟨out, hout, hlen, by simpa [List.range_succ] using hb⟩

/-- `h_msg`: the two digest calls of `R ‖ PK.seed ‖ PK.root ‖ M`, one after the other. -/
theorem h_msg_eq {π : KeccakState → KeccakState} (H : HasherSpec π)
    (hclone : ∀ h, keccak256.Hasher.Insts.CoreCloneClone.clone h = ok h)
    (r seed root : Array Std.U8 16#usize) (m : Array Std.U8 32#usize) :
    ∃ out, hash.h_msg r seed root m = ok out ∧
      (∀ j < 2, (callBytes π
        (bytes r.val ++ bytes seed.val ++ bytes root.val ++ bytes m.val) j).length = 32) ∧
      bytes out.val =
        callBytes π (bytes r.val ++ bytes seed.val ++ bytes root.val ++ bytes m.val) 0 ++
        callBytes π (bytes r.val ++ bytes seed.val ++ bytes root.val ++ bytes m.val) 1 := by
  obtain ⟨z, hnew, h0⟩ := H.new
  obtain ⟨h1, b1, hu1, ha1, hb1⟩ := H.update z [] r.to_slice h0
  obtain ⟨h2, b2, hu2, ha2, hb2⟩ := H.update h1 _ seed.to_slice ha1
  obtain ⟨h3, b3, hu3, ha3, hb3⟩ := H.update h2 _ root.to_slice ha2
  obtain ⟨h4, b4, hu4, ha4, hb4⟩ := H.update h3 _ m.to_slice ha3
  obtain ⟨out0, hrep, -⟩ := array_repeat 64#usize core.U8.Insts.CoreCloneClone (fun _ => rfl) 0#u8
  obtain ⟨e, he, hev⟩ := ok_of_triple DIGEST_CALLS_triple
  obtain ⟨out, hout, hlen, hb⟩ := h_msg_loop_eq H hclone h4
    (bytes r.val ++ bytes seed.val ++ bytes root.val ++ bytes m.val)
    (by simpa [Array.to_slice] using ha4) e hev out0
  refine ⟨out, ?_, hlen, hb⟩
  simp [hash.h_msg, hnew, core.array.Array.as_slice, rust_primitives.slice.array_as_slice, hu1,
    hu2, hu3, hu4, hrep, he, hb1, hb2, hb3, hb4, hout]

/-! ## The statement's digest -/

/-- **The statement's message digest**: the low 34 bytes of the number the two calls' bytes
spell, least significant byte first. -/
theorem messageDigest_eq (π : KeccakState → KeccakState) (pk : scheme.LeanSphincsPublicKey)
    (r : Array Std.U8 16#usize) (m : Array Std.U8 32#usize)
    (hlen : ∀ j < 2, (callBytes π
      (bytes r.val ++ bytes pk.pk_seed.val ++ bytes pk.root.val ++ bytes m.val) j).length = 32) :
    Id.run (Verification.messageDigest (inId π) (toPublicKey pk) (toDigest r) (toMessage m)) =
      BitVec.ofNat (8 * digestByteCount) (leNat (
        callBytes π (bytes r.val ++ bytes pk.pk_seed.val ++ bytes pk.root.val ++ bytes m.val) 0 ++
        callBytes π (bytes r.val ++ bytes pk.pk_seed.val ++ bytes pk.root.val ++ bytes m.val) 1)) := by
  have hcall : ∀ call : DigestCall,
      Id.run (Verification.messageDigestCall (inId π) (toDigest r) (toPublicKey pk).publicSeed
        (toPublicKey pk).root (toMessage m) call) =
      BitVec.ofNat 256 (leNat (callBytes π
        (bytes r.val ++ bytes pk.pk_seed.val ++ bytes pk.root.val ++ bytes m.val) call.val)) := by
    intro call
    simp only [Verification.messageDigestCall, toPublicKey, littleEndianBytes_toDigest,
      littleEndianBytes_toMessage, keccakHash_inId, callBytes]
  have hsum : ∀ f : DigestCall → Nat, ∑ c, f c = f 0 + f 1 := fun f => Fin.sum_univ_two f
  have hmod : ∀ l : List UInt8, l.length = 32 →
      (BitVec.ofNat 256 (leNat l)).toNat = leNat l := by
    intro l hl
    have := leNat_lt l
    rw [hl, show (256 : ℕ) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt this
  simp only [Verification.messageDigest, Id.run_bind, Id.run_pure, sequenceFin_id,
    truncateMessageDigest, digestValue, hsum, hcall]
  rw [show ((0 : DigestCall) : ℕ) = 0 from rfl, show ((1 : DigestCall) : ℕ) = 1 from rfl,
    hmod _ (hlen 0 (by omega)), hmod _ (hlen 1 (by omega)), leNat_append, hlen 0 (by omega)]
  rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mul_one, Nat.mul_comm (256 ^ 32)]
  rfl

/-- A byte of the low `N` bytes of a number is that byte of the number. -/
theorem byte_of_mod (X N p : Nat) (hp : p < N) :
    X % 2 ^ (8 * N) / 2 ^ (8 * p) % 2 ^ 8 = X / 256 ^ p % 256 := by
  have e : 2 ^ (8 * N) = 2 ^ (8 * p) * 2 ^ (8 * (N - p)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hd : 2 ^ 8 ∣ 2 ^ (8 * (N - p)) := Nat.pow_dvd_pow 2 (by omega)
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hd, Nat.pow_mul]
  rfl

/-- A byte of the digest the first 34 of the bytes `B` spell: that byte of `B`. -/
theorem digest_byte (B : List UInt8) (p : Nat) (hp : p < 34) (hB : p < B.length) :
    messageDigestByte (BitVec.ofNat (8 * digestByteCount) (leNat B)) p = B[p].toNat := by
  have hp' : p < digestByteCount := hp
  simp only [messageDigestByte, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  rw [byte_of_mod _ _ _ hp', leNat_byte B p hB]

theorem bytes_getElem_toNat (d : List Std.U8) (i : Nat) (h : i < (bytes d).length) :
    ((bytes d)[i]).toNat = (d[i]!).val := by
  have h' : i < d.length := by simpa [bytes] using h
  simp only [bytes, List.getElem_map, getElem!_pos d i h', b8, UInt8.toNat_ofBitVec]
  rfl

section
variable (d : List Std.U8) (hd : d.length = 64)
include hd

/-- A byte of the statement's digest is the Rust digest's. -/
theorem digest_byte_bytes (p : Nat) (hp : p < 34) :
    messageDigestByte (BitVec.ofNat (8 * digestByteCount) (leNat (bytes d))) p = (d[p]!).val := by
  have hl : p < (bytes d).length := by simp [bytes, hd]; omega
  rw [digest_byte _ p hp hl, bytes_getElem_toNat]

/-- A bit of the statement's digest is the one `digest_fields` reads. -/
theorem digest_bit (p : Nat) (hp : p < 272) :
    messageDigestBit (BitVec.ofNat (8 * digestByteCount) (leNat (bytes d))) p = bitAt d p := by
  simp only [messageDigestBit, bitAt, digest_byte_bytes d hd (p / 8) (by omega)]

/-- The statement's big-endian integer of some of the digest's bytes is `int`'s. -/
theorem digest_bigEndian (start count : Nat) (h : start + count ≤ 34) :
    messageDigestBigEndian (BitVec.ofNat (8 * digestByteCount) (leNat (bytes d))) start count =
      beInt ((d.drop start).take count) := by
  induction count with
  | zero => simp [messageDigestBigEndian, beInt]
  | succ n ih =>
    have ih := ih (by omega)
    have hlt : n < (d.drop start).length := by simp [hd]; omega
    simp only [messageDigestBigEndian] at ih
    simp only [messageDigestBigEndian, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ih, digest_byte_bytes d hd (start + n) (by omega)]
    rw [List.take_succ_eq_append_getElem hlt, beInt_append_singleton, List.getElem_drop,
      getElem!_pos d (start + n) (by omega)]

/-- The statement's leaf of FORS tree `c`, before its reduction, is `digest_fields`'s. -/
theorem digest_leafFold (c n : Nat) (hc : c < 24) (hn : n ≤ 10) :
    (List.range n).foldl (fun value j ↦ 2 * value +
      messageDigestBit (BitVec.ofNat (8 * digestByteCount) (leNat (bytes d)))
        (forsTreeHeight * c + j)) 0 = leafFold d c n := by
  induction n with
  | zero => simp [leafFold]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), leafFold_succ]
    simp only [List.foldl_cons, List.foldl_nil, forsTreeHeight]
    rw [digest_bit d hd _ (by omega)]

end

end Digest

open Digest in
/-- **`message_digest`** returns the index and the FORS leaves of the statement's message
digest. -/
theorem messageDigest_spec {π : KeccakState → KeccakState} (H : HasherSpec π)
    (hclone : ∀ h, keccak256.Hasher.Insts.CoreCloneClone.clone h = ok h) : MessageDigestSpec π := by
  intro pk r m
  obtain ⟨out, hout, hlen, hb⟩ := h_msg_eq H hclone r pk.pk_seed pk.root m
  obtain ⟨idx, leaves, hdf, hidx, hleaves⟩ := digest_fields_eq out
  have hd : out.val.length = 64 := by simp
  refine ⟨idx, leaves, by simp only [scheme.message_digest, hout, Aeneas.Std.bind_ok, hdf], ?_, ?_⟩
  · rw [messageDigest_eq π pk r m hlen, ← hb, hidx]
    simp only [digestIndex, forsMessageByteCount, treeIndexByteCount, leafIndexByteCount,
      digest_bigEndian out.val hd 30 3 (by omega), digest_bigEndian out.val hd (30 + 3) 1 (by omega)]
  · intro κ
    rw [messageDigest_eq π pk r m hlen, ← hb, hleaves κ.val κ.isLt]
    have hf := digest_leafFold out.val hd κ.val forsTreeHeight κ.isLt (Nat.le_refl 10)
    simp only [digestForsLeaves, forsLeafOfNat]
    rw [hf]
    exact (Nat.mod_eq_of_lt (leafFold_lt _ _ _)).symm

end LeanSphincsProofs
