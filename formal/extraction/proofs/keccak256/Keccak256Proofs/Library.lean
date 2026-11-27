import Keccak256Proofs.Common

/-!
# The library models, as equations

What the Rust library models the extractions step through compute: slices of arrays and writing
them back, `fill`, `clone`, loops over a range, folds, `from_fn`, an array's element.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)

namespace Keccak256Proofs

/-! ## Slices of arrays -/

theorem setSlice!_length {α : Type} (l : List α) (i : ℕ) (s : List α) :
    (l.setSlice! i s).length = l.length := by
  simp only [List.setSlice!, List.length_append, List.length_take, List.length_drop]
  omega

/-- `&mut a[..e]`. -/
theorem array_index_mut_range_to {α : Type} {N : Std.Usize} (a : Array α N) (e : Std.Usize)
    (he : e.val ≤ N.val) :
    ∃ s back, core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { «end» := e } = ok (s, back) ∧
      s.val = a.val.take e.val ∧ ∀ t : Slice α, (back t).val = a.val.setSlice! 0 t.val := by
  simp [core.Array.Insts.CoreOpsIndexIndexMut.index_mut, core.array.Array.as_mut_slice,
    rust_primitives.slice.array_as_mut_slice, core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_slice_mut, Slice.subslice, Array.to_slice_mut]
  refine ⟨_, _, by simp only [he, ↓reduceIte]; exact Aeneas.Std.bind_ok _ _, by simp, fun t => ?_⟩
  rw [Array.from_slice_val _ _ (by simp)]
  simp

/-- `&mut a[b..]`. -/
theorem array_index_mut_range_from {α : Type} {N : Std.Usize} (a : Array α N) (b : Std.Usize)
    (hb : b.val ≤ N.val) :
    ∃ s back, core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { start := b } = ok (s, back) ∧
      s.val = a.val.drop b.val ∧ ∀ t : Slice α, (back t).val = a.val.setSlice! b.val t.val := by
  simp [core.Array.Insts.CoreOpsIndexIndexMut.index_mut, core.array.Array.as_mut_slice,
    rust_primitives.slice.array_as_mut_slice, core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_slice_mut, rust_primitives.slice.slice_length, Slice.subslice,
    Array.to_slice_mut]
  refine ⟨_, _, by simp only [hb, ↓reduceIte]; exact Aeneas.Std.bind_ok _ _, by simp [List.slice], fun t => ?_⟩
  rw [Array.from_slice_val _ _ (by simp)]
  simp

/-- `x.to_be_bytes()` for a `u64`. -/
theorem u64_to_be_bytes (x : Std.U64) :
    core.num.U64.to_be_bytes x = ok (Aeneas.Std.core.num.U64.to_be_bytes x) := rfl

theorem fill_step {α : Type} (l s : List α) (v : α) (i : ℕ)
    (h : l = List.replicate i v ++ s.drop i) (hi : i < s.length) :
    l.set i v = List.replicate (i + 1) v ++ s.drop (i + 1) := by
  subst h
  rw [List.set_append_right _ _ (by simp), List.length_replicate, Nat.sub_self,
    List.drop_eq_getElem_cons hi, List.set_cons_zero, List.replicate_succ', List.append_assoc]
  rfl

/-- `fill`'s loop invariant after `i` bytes. -/
def fillInv (s : Slice Std.U8) (v : Std.U8) (i : Std.Usize) (acc : Slice Std.U8) : RustM Prop :=
  ok (acc.val = List.replicate i.val v ++ s.val.drop i.val)

@[spec]
theorem fill_loop_spec (s : Slice Std.U8) (v : Std.U8) (n : Std.Usize) (hn : n.val ≤ s.length) :
    ⦃ ⌜ True ⌝ ⦄
    core.slice.Slice.fill_loop core.U8.Insts.CoreCloneClone { start := 0#usize, «end» := n } s v
    ⦃ ⇓ r => ⌜ (fillInv s v n r).holds ⌝ ⦄ := by
  unfold core.slice.Slice.fill_loop
  apply Hax.loop_range_spec_unsigned (inv := fillInv s v)
  · simp
  · simp [fillInv]
  · intro acc i _ hi hinv
    simp only [fillInv, holds_ok] at hinv
    have hlen : acc.length = s.length := by
      have hn' : n.val ≤ s.val.length := hn
      show acc.val.length = s.val.length
      rw [hinv]; simp; omega
    hax_mvcgen [core.slice.Slice.fill_loop.body, fillInv, core.U8.Insts.CoreCloneClone.clone]
    case vc1.hQ =>
      rename_i hlt nx hnx r1 r2 hr s1 r hs1 hr'
      obtain ⟨hx, rfl, rfl⟩ := hr
      refine ⟨hlt, trivial, hnx, ?_⟩
      have hs : s.val.length = s.length := rfl
      simp only [fillInv, holds_ok, hr', hnx]
      simp [s1]
      exact fill_step _ _ _ _ hinv (by have : n.val ≤ s.val.length := hn; omega)
    case vc2.h_fail =>
      rename_i hlt nx hnx r1 r2 hr s1 hs1
      obtain ⟨hx, rfl, rfl⟩ := hr
      have : s1.length = acc.length := by simp [s1]
      omega
    case vc1.hQ =>
      have : i.val = n.val := by scalar_tac
      rw [hinv, this]
    scalar_tac

/-- `s.fill(v)` on bytes: every byte `v`. -/
theorem slice_fill_u8 (s : Slice Std.U8) (v : Std.U8) :
    ∃ r, core.slice.Slice.fill core.U8.Insts.CoreCloneClone s v = ok r ∧
      r.val = List.replicate s.length v := by
  have key : ⦃ ⌜ True ⌝ ⦄ core.slice.Slice.fill core.U8.Insts.CoreCloneClone s v
      ⦃ ⇓ r => ⌜ r.val = List.replicate s.length v ⌝ ⦄ := by
    hax_mvcgen [core.slice.Slice.fill, fillInv, core.slice.Slice.len,
      rust_primitives.slice.slice_length]
    case vc1.hn => scalar_tac
    case vc2.h_ok =>
      rename_i hpos k hk h1 r1 x back hx s2 r hs2 hr hinv
      obtain ⟨hlt, rfl, rfl⟩ := hx
      have hsl : s.len.val = s.val.length := by simp
      have hk1 : k.val + 1 = s.val.length := by scalar_tac
      have hstep := fill_step r1.val s.val v k.val hinv (by omega)
      rw [hr]
      simp only [s2, Slice.set_val_eq, List.set_set]
      rw [hstep, hk1, List.drop_length, List.append_nil]
    case vc3.h_fail =>
      rename_i hpos k hk h1 r1 x back hx s2 hs2 hinv
      obtain ⟨hlt, rfl, rfl⟩ := hx
      have : s2.length = r1.length := by simp [s2]
      omega
    case vc4.h_fail =>
      rename_i hpos k hk h1 r1 hlen hinv
      have hsl : s.len.val = s.val.length := by simp
      have : r1.val.length = s.val.length := by rw [hinv]; simp; scalar_tac
      have : r1.length = r1.val.length := rfl
      scalar_tac
    case vc5.h_fail => scalar_tac
    case vc6.hQ =>
      rename_i hpos
      have hsl : s.len.val = s.val.length := by simp
      have h0 : s.val.length = 0 := by scalar_tac
      have : s.length = 0 := h0
      rw [this, List.replicate_zero]
      exact List.eq_nil_of_length_eq_zero h0
  obtain ⟨r, hr⟩ := Hax.triple_noThrow_exists_ok key
  exact ⟨r, hr, Hax.triple_noThrow_elim key hr⟩

@[simp] theorem bytes_append (l₁ l₂ : List Std.U8) : bytes (l₁ ++ l₂) = bytes l₁ ++ bytes l₂ := by
  simp [bytes]

/-! ## The library models, as triples for `hax_mvcgen` -/

theorem triple_of_exists {α : Type} {x : RustM α} {P : α → Prop} (h : ∃ r, x = ok r ∧ P r) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  obtain ⟨r, hr, hp⟩ := h
  exact Hax.triple_of_ok hr hp

theorem exists_of_triple {α : Type} {x : RustM α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) : ∃ r, x = ok r ∧ P r := by
  obtain ⟨r, hr⟩ := Hax.triple_noThrow_exists_ok h
  exact ⟨r, hr, Hax.triple_noThrow_elim h hr⟩

@[spec]
theorem array_index_mut_range_triple {α : Type} {N : Std.Usize} (a : Array α N) (b e : Std.Usize)
    (h : b.val ≤ e.val) (he : e.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { start := b, «end» := e }
    ⦃ ⇓ r => ⌜ r.1.val = List.slice b.val e.val a.val ∧
      ∀ t : Slice α, (r.2 t).val = a.val.setSlice! b.val t.val ⌝ ⦄ := by
  obtain ⟨s, back, h1, h2, h3⟩ := array_index_mut_range a b e h he
  exact Hax.triple_of_ok h1 ⟨h2, h3⟩

@[spec]
theorem array_index_mut_range_to_triple {α : Type} {N : Std.Usize} (a : Array α N) (e : Std.Usize)
    (he : e.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { «end» := e }
    ⦃ ⇓ r => ⌜ r.1.val = a.val.take e.val ∧
      ∀ t : Slice α, (r.2 t).val = a.val.setSlice! 0 t.val ⌝ ⦄ := by
  obtain ⟨s, back, h1, h2, h3⟩ := array_index_mut_range_to a e he
  exact Hax.triple_of_ok h1 ⟨h2, h3⟩

@[spec]
theorem array_index_mut_range_from_triple {α : Type} {N : Std.Usize} (a : Array α N)
    (b : Std.Usize) (hb : b.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { start := b }
    ⦃ ⇓ r => ⌜ r.1.val = a.val.drop b.val ∧
      ∀ t : Slice α, (r.2 t).val = a.val.setSlice! b.val t.val ⌝ ⦄ := by
  obtain ⟨s, back, h1, h2, h3⟩ := array_index_mut_range_from a b hb
  exact Hax.triple_of_ok h1 ⟨h2, h3⟩

@[spec]
theorem copy_from_slice_u8_triple (d s : Slice Std.U8) (h : d.length = s.length) :
    ⦃ ⌜ True ⌝ ⦄ core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy d s
    ⦃ ⇓ r => ⌜ r = s ⌝ ⦄ :=
  Hax.triple_of_ok (copy_from_slice_u8 d s h) rfl

@[spec]
theorem slice_fill_u8_triple (s : Slice Std.U8) (v : Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ core.slice.Slice.fill core.U8.Insts.CoreCloneClone s v
    ⦃ ⇓ r => ⌜ r.val = List.replicate s.length v ⌝ ⦄ :=
  triple_of_exists (slice_fill_u8 s v)

@[spec]
theorem array_repeat_u8_triple (N : Std.Usize) (x : Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ core.array.repeat N core.U8.Insts.CoreCloneClone x
    ⦃ ⇓ a => ⌜ a.val = List.replicate N.val x ⌝ ⦄ :=
  triple_of_exists (array_repeat N _ (fun _ => rfl) x)

theorem bytes_setSlice! (l : List Std.U8) (i : ℕ) (s : List Std.U8) :
    bytes (l.setSlice! i s) = (bytes l).setSlice! i (bytes s) := by
  simp [List.setSlice!, bytes, List.map_take, List.map_drop]

/-- Writing over the middle of three pieces replaces it. -/
theorem setSlice!_mid {α : Type} (p w q w' : List α) (hw : w'.length = w.length) :
    (p ++ w ++ q).setSlice! p.length w' = p ++ w' ++ q := by
  simp [List.setSlice!, hw]

/-- `setSlice!_mid` at a stated index. -/
theorem setSlice!_mid' {α : Type} (p w q w' : List α) (i : ℕ) (hi : p.length = i)
    (hw : w'.length = w.length) : (p ++ w ++ q).setSlice! i w' = p ++ w' ++ q := by
  subst hi; exact setSlice!_mid p w q w' hw

theorem bytes_replicate_zero (n : ℕ) : bytes (List.replicate n 0#u8) = List.replicate n 0 := by
  simp only [bytes, List.map_replicate]; rfl

theorem u64_bv_eq_ofNat (x : Std.U64) : x.bv = BitVec.ofNat 64 x.val := by
  apply BitVec.eq_of_toNat_eq
  simp

/-! ## `clone` -/

theorem array_map_clone_fold {α : Type} (N : Std.Usize) (inst : core.clone.Clone α)
    (hclone : ∀ y, inst.clone y = ok y) (c : core.array.CloneArray.clone.closure α N) :
    ∀ (l acc : List α),
      List.foldlM (fun (s : List α × core.array.CloneArray.clone.closure α N) x => do
          let __x ← (core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT N
            inst).call_mut s.2 x
          match __x with
          | (v, f') => ok (s.1 ++ [v], f')) (acc, c) l = ok (acc ++ l, c) := by
  intro l
  induction l with
  | nil => intro acc; simp [List.foldlM]; rfl
  | cons x xs ih =>
    intro acc
    simp [List.foldlM,
      core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut, hclone]
    have ih' := ih (acc ++ [x])
    simp [core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut,
      hclone] at ih'
    exact ih'

/-- `clone` of an array whose elements' `clone` returns its argument. -/
theorem array_clone {α : Type} {N : Std.Usize} (inst : core.clone.Clone α)
    (hclone : ∀ y, inst.clone y = ok y) (a : Array α N) :
    core.Array.Insts.CoreCloneClone.clone inst a = ok a := by
  have hf := array_map_clone_fold N inst hclone () a.val []
  simp only [core.Array.Insts.CoreCloneClone.clone, core.array.Array.map,
    rust_primitives.slice.array_map]
  split
  · rename_i heq; erw [hf, RustM.match.ok] at heq; cases heq
  · rename_i heq; erw [hf, RustM.match.ok] at heq; cases heq
  · rename_i result heq
    erw [hf, RustM.match.ok] at heq
    cases heq
    exact congrArg ok (Aeneas.Std.Array.ext _ _ (by simp))

/-- **`Hasher::clone`** returns the hasher. -/
theorem hasher_clone (h : keccak256.Hasher) :
    keccak256.Hasher.Insts.CoreCloneClone.clone h = ok h := by
  simp only [keccak256.Hasher.Insts.CoreCloneClone.clone,
    array_clone core.U64.Insts.CoreCloneClone (fun _ => rfl),
    array_clone core.U8.Insts.CoreCloneClone (fun _ => rfl),
    core.Usize.Insts.CoreCloneClone.clone]
  simp

/-! ## Loops over a range, folds and `from_fn`, as equations -/

/-- A loop over `s..e` whose body, below the end, steps to the next index keeping `inv`, and at
the end returns its state: it returns a state satisfying `inv e`. -/
theorem range_loop {β : Type}
    (body : core.ops.range.Range Std.Usize × β →
      RustM (ControlFlow (core.ops.range.Range Std.Usize × β) β))
    (e : Std.Usize) (inv : Nat → β → Prop)
    (hdone : ∀ (i : Std.Usize) acc, e.val ≤ i.val →
      body ({ start := i, «end» := e }, acc) = ok (.done acc))
    (hstep : ∀ (i : Std.Usize) acc, i.val < e.val → inv i.val acc →
      ∃ (i' : Std.Usize) (acc' : β), i'.val = i.val + 1 ∧
        body ({ start := i, «end» := e }, acc) = ok (.cont ({ start := i', «end» := e }, acc')) ∧
        inv i'.val acc')
    (s : Std.Usize) (init : β) (hs : s.val ≤ e.val) (hinit : inv s.val init) :
    ∃ r, loop body ({ start := s, «end» := e }, init) = ok r ∧ inv e.val r := by
  suffices gen : ∀ (n : Nat) (i : Std.Usize) acc, e.val - i.val = n → i.val ≤ e.val →
      inv i.val acc → ∃ r, loop body ({ start := i, «end» := e }, acc) = ok r ∧ inv e.val r from
    gen _ s init rfl hs hinit
  intro n
  induction n with
  | zero =>
    intro i acc hn hle hinv
    have hie : i.val = e.val := by omega
    refine ⟨acc, ?_, hie ▸ hinv⟩
    rw [loop.eq_def, hdone i acc (by omega), Aeneas.Std.bind_ok]
  | succ n ih =>
    intro i acc hn hle hinv
    obtain ⟨i', acc', hi', hbody, hinv'⟩ := hstep i acc (by omega) hinv
    rw [loop.eq_def, hbody, Aeneas.Std.bind_ok]
    exact ih i' acc' (by omega) (by omega) hinv'

/-- A fold over `s..e` whose closure keeps `inv` and itself: it returns a value satisfying
`inv e`. -/
theorem range_fold {B F : Type} (inst : core.ops.function.FnMut F (B × Std.Usize) B) (f : F)
    (e : Std.Usize) (inv : Nat → B → Prop)
    (hstep : ∀ (i : Std.Usize) acc, i.val < e.val → inv i.val acc →
      ∃ acc', inst.call_mut f (acc, i) = ok (acc', f) ∧ inv (i.val + 1) acc')
    (s : Std.Usize) (init : B) (hs : s.val ≤ e.val) (hinit : inv s.val init) :
    ∃ r, core.iter.traits.iterator.Iterator.fold.default
        (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator core.Usize.Insts.CoreIterRangeStep)
        inst { start := s, «end» := e } init f = ok r ∧ inv e.val r := by
  unfold core.iter.traits.iterator.Iterator.fold.default core.iter.traits.iterator.iter_fold
    core.iter.traits.iterator.iter_fold_loop
  generalize hbody : (fun x : core.ops.range.Range Std.Usize × F × B => match x with
    | (iter2, f1, accum1) => core.iter.traits.iterator.iter_fold_loop.body
        (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator
          core.Usize.Insts.CoreIterRangeStep) inst iter2 f1 accum1) = body
  have hdone : ∀ (i : Std.Usize) acc, e.val ≤ i.val →
      body ({ start := i, «end» := e }, f, acc) = ok (.done acc) := by
    intro i acc hi
    subst hbody
    simp only [core.iter.traits.iterator.iter_fold_loop.body,
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator, range_next_ge i e hi,
      Aeneas.Std.bind_ok]
    rfl
  have hcont : ∀ (i : Std.Usize) acc, i.val < e.val → inv i.val acc →
      ∃ (i' : Std.Usize) (acc' : B), i'.val = i.val + 1 ∧
        body ({ start := i, «end» := e }, f, acc) =
          ok (.cont ({ start := i', «end» := e }, f, acc')) ∧ inv i'.val acc' := by
    intro i acc hi hinv
    obtain ⟨i', hi', hnext⟩ := range_next_lt i e hi
    obtain ⟨acc', hcall, hinv'⟩ := hstep i acc hi hinv
    refine ⟨i', acc', hi', ?_, hi' ▸ hinv'⟩
    subst hbody
    simp only [core.iter.traits.iterator.iter_fold_loop.body,
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator, hnext, Aeneas.Std.bind_ok]
    show (do let (accum1, f1) ← inst.call_mut f (acc, i); ok (ControlFlow.cont (_, f1, accum1))) = _
    rw [hcall]
    simp
  suffices gen : ∀ (n : Nat) (i : Std.Usize) acc, e.val - i.val = n → i.val ≤ e.val →
      inv i.val acc → ∃ r, loop body ({ start := i, «end» := e }, f, acc) = ok r ∧ inv e.val r from
    gen _ s init rfl hs hinit
  intro n
  induction n with
  | zero =>
    intro i acc hn hle hinv
    have hie : i.val = e.val := by omega
    refine ⟨acc, ?_, hie ▸ hinv⟩
    rw [loop.eq_def, hdone i acc (by omega), Aeneas.Std.bind_ok]
  | succ n ih =>
    intro i acc hn hle hinv
    obtain ⟨i', acc', hi', hb, hinv'⟩ := hcont i acc (by omega) hinv
    rw [loop.eq_def, hb, Aeneas.Std.bind_ok]
    exact ih i' acc' (by omega) (by omega) hinv'

/-- The primitive under `from_fn`, for a closure that returns `g i` at `i` and keeps itself. -/
theorem array_from_fn_eq {T F : Type} (N : Std.Usize) (inst : core.ops.function.FnMut F Std.Usize T)
    (c : F) (g : Nat → T)
    (h : ∀ i : Std.Usize, i.val < N.val → inst.call_mut c i = ok (g i.val, c)) :
    ∃ a, rust_primitives.slice.array_from_fn N inst c = ok a ∧
      a.val = (List.range N.val).map g := by
  have go : ∀ n, n ≤ N.val →
      rust_primitives.slice.array_from_fn_go inst c n = ok ((List.range n).map g, c) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hv : (⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩ : Std.Usize).val = n := by
        have := N.hBounds
        simp only [UScalar.val, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      rw [rust_primitives.slice.array_from_fn_go, ih (by omega)]
      simp only [Aeneas.Std.bind_ok]
      rw [h _ (by rw [hv]; omega), hv]
      simp [List.range_succ]
  unfold rust_primitives.slice.array_from_fn
  rw [go N.val (Nat.le_refl _)]
  simp

/-- `from_fn` of a closure that returns `g i` at `i` and keeps itself: the array of the `g i`. -/
theorem from_fn_eq {T F : Type} (N : Std.Usize) (inst : core.ops.function.FnMut F Std.Usize T)
    (c : F) (g : Nat → T)
    (h : ∀ i : Std.Usize, i.val < N.val → inst.call_mut c i = ok (g i.val, c)) :
    ∃ a, core.array.from_fn N inst c = ok a ∧ a.val = (List.range N.val).map g :=
  array_from_fn_eq N inst c g h

/-- `from_fn` of a closure that keeps itself and returns, at `i`, something satisfying `P i`. -/
theorem from_fn_pred {T F : Type} [Inhabited T] (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (P : Nat → T → Prop)
    (h : ∀ i : Std.Usize, i.val < N.val → ∃ r, inst.call_mut c i = ok (r, c) ∧ P i.val r) :
    ∃ a, core.array.from_fn N inst c = ok a ∧ ∀ n < N.val, P n a.val[n]! := by
  have hex : ∀ n : Nat, ∃ r : T, n < N.val →
      (∀ i : Std.Usize, i.val = n → inst.call_mut c i = ok (r, c)) ∧ P n r := by
    intro n
    by_cases hn : n < N.val
    · have hv : (⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩ : Std.Usize).val = n := by
        have := N.hBounds
        simp only [UScalar.val, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by scalar_tac)
      obtain ⟨r, hr, hp⟩ := h _ (by rw [hv]; exact hn)
      rw [hv] at hp
      refine ⟨r, fun _ => ⟨fun i hi => ?_, hp⟩⟩
      have : i = ⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩ :=
        (UScalar.eq_equiv _ _).2 (by rw [hi, hv])
      rw [this]
      exact hr
    · exact ⟨default, fun h => absurd h hn⟩
  choose g hg using hex
  obtain ⟨a, ha, hav⟩ := from_fn_eq N inst c g (fun i hi => (hg i.val hi).1 i rfl)
  refine ⟨a, ha, fun n hn => ?_⟩
  rw [hav]
  simpa [hn] using (hg n hn).2

/-- An element of an array, by an index within it. -/
theorem array_index_eq {α : Type} [Inhabited α] {N : Std.Usize} (a : Array α N) (i : Std.Usize)
    (h : i.val < N.val) : Array.index_usize a i = ok (a.val[i.val]!) := by
  have hs : Array.index_usize a i ⦃ x => x = a.val[i.val]! ⦄ := by
    step*
    rw [x_post1, getElem!_pos a.val i.val x_post]
  obtain ⟨x, hx, rfl⟩ := WP.spec_imp_exists hs
  exact hx

end Keccak256Proofs
