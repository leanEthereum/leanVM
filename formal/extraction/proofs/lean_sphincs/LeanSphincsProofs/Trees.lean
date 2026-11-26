import LeanSphincsProofs.Common

/-!
# The Merkle folds: `tree_root` and `fors_root`

`keccak256::path_root` folds a leaf and its path into a root with any node function
(`path_root_fold`); `scheme::tree_root` is it with the hypertree's node, `fors::fors_root` it with
a FORS tree's node, once per tree, then `T_k` of the roots.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation Sphincs
open LeanVM.Semantics (KeccakState)

namespace LeanSphincsProofs

/-! ## Bytes -/

/-! ## The tweakable hash at an address -/

section
variable {π : KeccakState → KeccakState}

end

theorem ite_ok {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then ok a else ok b : RustM α) = ok (if c then a else b) := by
  split <;> rfl

theorem range_next_spec (i e : Std.Usize) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start := i, «end» := e } ⦃ r =>
      (i.val < e.val ∧ ∃ s : Std.Usize, s.val = i.val + 1 ∧ r = (some i, { start := s, «end» := e })) ∨
      (e.val ≤ i.val ∧ r = (none, { start := i, «end» := e })) ⦄ := by
  have t := Hax.IteratorRange_next_spec_usize i e
    (Q := PostCond.noThrow fun r => ⌜(i.val < e.val ∧ ∃ s : Std.Usize, s.val = i.val + 1 ∧
      r = (some i, { start := s, «end» := e })) ∨ (e.val ≤ i.val ∧ r = (none, { start := i, «end» := e }))⌝)
    (fun h s hs => Or.inl ⟨h, s, hs, rfl⟩) (fun h => Or.inr ⟨h, rfl⟩)
  obtain ⟨v, hv⟩ := Hax.triple_noThrow_exists_ok t
  have hp := Hax.triple_noThrow_elim t hv
  exact spec_of_exists ⟨v, hv, hp⟩

/-- The statement's `foldPath` with a pure node function. -/
def foldId (nodeS : ℕ → ℕ → HashInput → Digest) (e : ℕ) (sib : ℕ → Digest) (n : ℕ) (v : Digest) :
    Digest :=
  Id.run (foldPath (m := Id) (fun l j p => pure (nodeS l j p)) e sib n v)

theorem foldId_zero (nodeS : ℕ → ℕ → HashInput → Digest) (e : ℕ) (sib : ℕ → Digest) (v : Digest) :
    foldId nodeS e sib 0 v = v := rfl

theorem foldId_succ (nodeS : ℕ → ℕ → HashInput → Digest) (e : ℕ) (sib : ℕ → Digest) (l : ℕ)
    (v : Digest) :
    foldId nodeS e sib (l + 1) v =
      nodeS l (e / 2 ^ (l + 1))
        (if e.testBit l then nodePayload (sib l) (foldId nodeS e sib l v)
        else nodePayload (foldId nodeS e sib l v) (sib l)) :=
  rfl

/-- `keccak256::path_root` with any node function: the statement's `foldPath`. -/
theorem path_root_fold {T1 : Type}
    (inst : core.ops.function.Fn T1 (Std.Usize × Std.Usize × Array (Array Std.U8 16#usize) 2#usize)
      (Array Std.U8 16#usize)) (nd : T1) (nodeS : ℕ → ℕ → HashInput → Digest)
    (leaf : Array Std.U8 16#usize) (e : Std.Usize) (path : Slice (Array Std.U8 16#usize))
    (hcall : ∀ (z j : Std.Usize) (ch : Array (Array Std.U8 16#usize) 2#usize), 1 ≤ z.val →
      z.val ≤ path.length → j.val ≤ e.val → ∃ r, inst.call nd (z, j, ch) = ok r ∧
        toDigest r = nodeS (z.val - 1) j.val (bytes ((ch.val.map Array.val).flatten)))
    (hlen : path.length ≤ 16) :
    ∃ r, keccak256.path_root inst leaf e path nd = ok r ∧
      toDigest r = foldId nodeS e.val (fun z => toDigest path.val[z]!) path.length (toDigest leaf) := by
  apply WP.spec_imp_exists
  unfold keccak256.path_root
  have hl : core.slice.Slice.len path = ok path.len := by
    simp [core.slice.Slice.len, rust_primitives.slice.slice_length]
  rw [hl]
  simp only [Aeneas.Std.bind_ok]
  unfold keccak256.path_root_loop
  apply loop.spec_decr_nat (fun x => x.1.«end».val - x.1.start.val)
    (fun x => x.1.«end» = path.len ∧ x.1.start.val ≤ path.length ∧
      toDigest x.2 = foldId nodeS e.val (fun z => toDigest path.val[z]!) x.1.start.val (toDigest leaf))
  · rintro ⟨⟨i, en⟩, cur⟩ ⟨hen, hi, hcur⟩
    simp only at hen hi hcur
    subst hen
    unfold keccak256.path_root_loop.body
    have hplen : path.len.val = path.length := Slice.len_val path
    step with range_next_spec as ⟨r, it, hnext⟩
    rcases hnext with ⟨hlt, s, hs, rfl, rfl⟩ | ⟨hge, rfl, rfl⟩
    · simp only
      have hil : i.val < path.length := by omega
      step as ⟨sib, hsib⟩
      step as ⟨i0, hi0⟩
      · have := numBits_ge; omega
      simp only [lift, ite_ok, Aeneas.Std.bind_ok]
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      · have := numBits_ge; omega
      obtain ⟨r, hr, hv⟩ := hcall i2 i3
        (if i0 &&& 1#usize = 0#usize then Array.make 2#usize [cur, sib] (by rfl)
          else Array.make 2#usize [sib, cur] (by rfl)) (by omega) (by omega)
        (by rw [hi3]; exact Nat.shiftRight_le _ _)
      rw [hr]
      simp only [Aeneas.Std.bind_ok, WP.spec_ok]
      refine ⟨trivial, by omega, ?_, by omega⟩
      rw [hv, hs, foldId_succ, ← hcur]
      have h1 : i2.val - 1 = i.val := by omega
      have h3 : i3.val = e.val / 2 ^ (i.val + 1) := by rw [hi3, hi2, Nat.shiftRight_eq_div_pow]
      have hsibv : toDigest (path.val[i.val]!) = toDigest sib := by
        rw [getElem!_pos path.val i.val hil]; subst sib; rfl
      rw [h1, h3, hsibv]
      congr 1
      have hbit : (i0 &&& 1#usize = 0#usize) ↔ e.val.testBit i.val = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, ← hi0]
        constructor
        · intro h
          have := congrArg UScalar.val h
          simp only [UScalar.val_and] at this
          simp at this
          simp [this]
        · intro h
          apply UScalar.eq_of_val_eq
          simp only [UScalar.val_and]
          simp at h ⊢
          omega
      by_cases hb : i0 &&& 1#usize = 0#usize
      · simp [hb, hbit.mp hb, nodePayload, littleEndianBytes_toDigest, bytes]
      · have : e.val.testBit i.val = true := by
          cases h : e.val.testBit i.val
          · exact absurd (hbit.mpr h) hb
          · rfl
        simp [hb, this, nodePayload, littleEndianBytes_toDigest, bytes]
    · simp only [WP.spec_ok]
      have : i.val = path.length := by omega
      rw [hcur, this]
  · exact ⟨rfl, by simp, by simp [foldId_zero]⟩

section
variable {π : KeccakState → KeccakState}

/-- `scheme::node`: node `j` at height `z` of a key's tree, the statement's `H` at that node. -/
theorem node_spec (hth : ThSpec π) (htree : TreeAdrsSpec) (hw : AdrsWordSpec)
    (seed : Array Std.U8 16#usize) (k : lean_sphincs.wots.OtsKey) (z j : Std.Usize)
    (ch : Array (Array Std.U8 16#usize) 2#usize) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (hk : KeyIs k layer tree leaf) :
    ∃ r, lean_sphincs.scheme.node seed k z j ch = ok r ∧
      toDigest r = Id.run (Verification.tweakableHash (inId π) (toDigest seed)
        (.node layer tree z.val j.val) (bytes ((ch.val.map Array.val).flatten))) := by
  obtain ⟨hkl, hkt, -⟩ := hk
  have hl32 : k.layer.val < 2 ^ 32 := by have := layer.isLt; simp [layerCount] at this; omega
  obtain ⟨a, a1, ha, ha1, hA1⟩ := htree k lean_sphincs.hash.TREE .tree
    (by simp [lean_sphincs.hash.TREE, AddressType.word]) hl32
  obtain ⟨-, ⟨a2, ha2, hA2⟩, -, -⟩ := hw a1 _ (UScalar.cast .U32 z) hA1
  obtain ⟨-, -, -, ⟨a3, ha3, hA3⟩⟩ := hw a2 _ (UScalar.cast .U32 j) hA2
  have hslice : 16 * ch.to_slice.length ≤ Usize.max := by
    have : ch.to_slice.length = 2 := by simp
    rw [this]; scalar_tac
  obtain ⟨d, hd, hval⟩ := th_digests_adrs hth seed a3 _ ch.to_slice hA3 hslice
  refine ⟨d, ?_, ?_⟩
  · simp only [lean_sphincs.scheme.node, ha, ha1, lift, ha2, ha3, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice, Aeneas.Std.bind_ok]
    exact hd
  · rw [hval]
    simp only [Verification.tweakableHash, hashDomainFields, makeAddress, cast_u32_bv, hkl, hkt]
    simp

/-- **`tree_root`** is the statement's `treeFold`. -/
theorem treeRoot_spec (hth : ThSpec π) (htree : TreeAdrsSpec) (hw : AdrsWordSpec) :
    TreeRootSpec π := by
  intro seed k leafValue path layer tree leaf hk hlen
  have hcast : (UScalar.cast .Usize k.leaf).val = leaf.val := by
    rw [← hk.2.2]
    exact UScalar.cast_val_mod_pow_greater_numBits_eq .Usize k.leaf
      (by simp only [UScalarTy.numBits]; exact numBits_ge)
  obtain ⟨r, hr, hv⟩ := path_root_fold
    lean_sphincs.scheme.tree_root.closure.Insts.CoreOpsFunctionFnTupleUsizeUsizeShared2ArrayArrayU8162ArrayU816
    (seed, k)
    (fun l j p => Id.run (Verification.tweakableHash (inId π) (toDigest seed) (.node layer tree (l + 1) j) p))
    leafValue (UScalar.cast .Usize k.leaf) path
    (by
      intro z j ch hz _ _
      obtain ⟨r, hr, hv⟩ := node_spec hth htree hw seed k z j ch layer tree leaf hk
      refine ⟨r, hr, ?_⟩
      have : z.val - 1 + 1 = z.val := by omega
      rw [hv, this])
    hlen
  refine ⟨r, ?_, ?_⟩
  · simp only [lean_sphincs.scheme.tree_root, lift, Aeneas.Std.bind_ok]
    exact hr
  · rw [hv, hcast]
    rfl

/-! ## FORS -/

/-- `fors_adrs`: the address of an instance, the bottom key of its index. -/
theorem fors_adrs_spec (hk : KeyAdrsSpec) (hof : OfIndexSpec) (idx : Std.U64) (index : Index)
    (hidx : idx.val = index.val) (t : Std.U32) (T : AddressType) (ht : t.val = T.word) :
    ∃ a, lean_sphincs.fors.fors_adrs idx t = ok a ∧
      AdrsIs a (makeAddress 0 (treeOfIndex 0 index).val T (leafOfIndex 0 index).val 0 0) := by
  obtain ⟨k, hk0, hkl, hkt, hkf⟩ := hof 0#usize idx 0 index (by simp) hidx
  have hl0 : k.layer.val = 0 := by simpa using hkl
  obtain ⟨a, ha, hA⟩ := hk k t T ht (by omega)
  refine ⟨a, ?_, ?_⟩
  · simp only [lean_sphincs.fors.fors_adrs, hk0, Aeneas.Std.bind_ok]
    exact ha
  · rw [hl0, hkt, hkf] at hA
    exact hA

/-- `fors_node_adrs`: node `j` at height `z` of tree `c`, its tree index counted across the
trees. -/
theorem fors_node_adrs_spec (hk : KeyAdrsSpec) (hw : AdrsWordSpec) (hof : OfIndexSpec)
    (idx : Std.U64) (index : Index) (hidx : idx.val = index.val) (c z j : Std.Usize)
    (κ : ForsTreeIndex) (hc : c.val = κ.val) (hz : z.val ≤ 10) (hj : j.val < 2 ^ 16) :
    ∃ a, lean_sphincs.fors.fors_node_adrs idx c z j = ok a ∧
      AdrsIs a (makeAddress 0 (treeOfIndex 0 index).val .forsTree (leafOfIndex 0 index).val z.val
        (forsTreeIndex κ z.val j.val)) := by
  obtain ⟨a, ha, hA⟩ := fors_adrs_spec hk hof idx index hidx lean_sphincs.hash.FORS_TREE .forsTree
    (by simp [lean_sphincs.hash.FORS_TREE, AddressType.word])
  obtain ⟨-, ⟨a1, ha1, hA1⟩, -, -⟩ := hw a _ (UScalar.cast .U32 z) hA
  have hFH : lean_sphincs.internals.FORS_HEIGHT.val = 10 := by
    simp [lean_sphincs.internals.FORS_HEIGHT]
  have hκ := κ.isLt
  simp only [forsTreeCount] at hκ
  have hnb := numBits_ge
  have hsz : 2 ^ 32 ≤ Usize.size := by
    have h32 : (32 : ℕ) ≤ Usize.numBits := by
      cases System.Platform.numBits_eq <;> simp [Usize.numBits, *]
    rw [Usize.size_def]; exact Nat.pow_le_pow_right (by omega) h32
  have hmax : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  have hpow : 2 ^ (10 - z.val) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
  apply WP.spec_imp_exists
  unfold lean_sphincs.fors.fors_node_adrs
  simp only [ha, lift, ha1, Aeneas.Std.bind_ok]
  have hzle : z.val ≤ lean_sphincs.internals.FORS_HEIGHT.val := by rw [hFH]; exact hz
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  · rw [hi1, hFH]; omega
  have hi2v : i2.val = c.val * 2 ^ (10 - z.val) := by
    rw [hi2, hi1, hFH, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    nlinarith
  have hprod : c.val * 2 ^ (10 - z.val) ≤ 23 * 2 ^ 10 := Nat.mul_le_mul (by omega) hpow
  have hsum : i2.val + j.val ≤ Usize.max := by
    have : i2.val + j.val ≤ 23 * 2 ^ 10 + 2 ^ 16 := Nat.add_le_add (hi2v ▸ hprod) hj.le
    omega
  step as ⟨i3, hi3⟩
  obtain ⟨-, -, -, ⟨a2, ha2, hA2⟩⟩ := hw a1 _ (UScalar.cast .U32 i3) hA1
  rw [ha2, WP.spec_ok]
  simp only [makeAddress, cast_u32_bv, forsTreeIndex, forsTreeHeight] at hA2 ⊢
  rw [hi3, hi2v, hc] at hA2
  exact hA2

/-- `fors_node`: the statement's `H` at a FORS node. -/
theorem fors_node_spec (hth : ThSpec π) (hk : KeyAdrsSpec) (hw : AdrsWordSpec) (hof : OfIndexSpec)
    (seed : Array Std.U8 16#usize) (idx : Std.U64) (index : Index) (hidx : idx.val = index.val)
    (c z j : Std.Usize) (ch : Array (Array Std.U8 16#usize) 2#usize) (κ : ForsTreeIndex)
    (hc : c.val = κ.val) (hz : z.val ≤ 10) (hj : j.val < 2 ^ 16) :
    ∃ r, lean_sphincs.fors.fors_node seed idx c z j ch = ok r ∧
      toDigest r = Id.run (Verification.tweakableHash (inId π) (toDigest seed)
        (.forsNode index κ z.val j.val) (bytes ((ch.val.map Array.val).flatten))) := by
  obtain ⟨a, ha, hA⟩ := fors_node_adrs_spec hk hw hof idx index hidx c z j κ hc hz hj
  have hslice : 16 * ch.to_slice.length ≤ Usize.max := by
    have : ch.to_slice.length = 2 := by simp
    rw [this]; scalar_tac
  obtain ⟨d, hd, hval⟩ := th_digests_adrs hth seed a _ ch.to_slice hA hslice
  refine ⟨d, ?_, ?_⟩
  · simp only [lean_sphincs.fors.fors_node, ha, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice, Aeneas.Std.bind_ok]
    exact hd
  · rw [hval]
    simp only [Verification.tweakableHash, hashDomainFields]
    simp

/-- `fors_leaf`: the statement's `F` of a FORS leaf's secret. -/
theorem fors_leaf_spec (hth : ThSpec π) (hk : KeyAdrsSpec) (hw : AdrsWordSpec) (hof : OfIndexSpec)
    (seed : Array Std.U8 16#usize) (idx : Std.U64) (index : Index) (hidx : idx.val = index.val)
    (c s : Std.Usize) (secret : Array Std.U8 16#usize) (κ : ForsTreeIndex) (leaf : ForsLeafIndex)
    (hc : c.val = κ.val) (hs : s.val = leaf.val) :
    ∃ r, lean_sphincs.fors.fors_leaf seed idx c s secret = ok r ∧
      toDigest r = Id.run (Verification.forsLeafHash (inId π) (toDigest seed) index κ leaf
        (toDigest secret)) := by
  have hl := leaf.isLt
  simp only [forsTreeHeight] at hl
  obtain ⟨a, ha, hA⟩ := fors_node_adrs_spec hk hw hof idx index hidx c 0#usize s κ hc (by simp)
    (by omega)
  obtain ⟨d, hd, hval⟩ := th_adrs hth seed a _ secret.to_slice hA
  refine ⟨d, ?_, ?_⟩
  · simp only [lean_sphincs.fors.fors_leaf, ha, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice, Aeneas.Std.bind_ok]
    exact hd
  · rw [hval]
    simp only [Verification.forsLeafHash, Verification.tweakableHash, hashDomainFields,
      littleEndianBytes_toDigest, hs]
    simp
end

theorem bind_exists {α β : Type} (x : α) (f : α → RustM β) (h : ∃ a, f x = ok a) :
    ∃ a, (ok x >>= f) = ok a := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, by rw [Aeneas.Std.bind_tc_ok, ha]⟩

theorem foldlM_ok_exists {σ α : Type} (step : σ → α → RustM σ) (h : ∀ s x, ∃ s', step s x = ok s')
    (l : List α) (acc : σ) : ∃ r, List.foldlM step acc l = ok r := by
  induction l generalizing acc with
  | nil => exact ⟨acc, rfl⟩
  | cons x xs ih =>
    obtain ⟨s', hs'⟩ := h acc x
    obtain ⟨r, hr⟩ := ih s'
    exact ⟨r, by rw [List.foldlM_cons, hs', Aeneas.Std.bind_tc_ok, hr]⟩

theorem match_ok_of_exists {α : Type} {x : RustM α} (hx : ∃ r, x = ok r) :
    (∀ e a, x.match ≠ .vis (.fail e) a) ∧ x.match ≠ .div := by
  obtain ⟨r, rfl⟩ := hx
  rw [RustM.match.ok]
  refine ⟨?_, ?_⟩
  · intro e a h; cases h
  · intro h; cases h

theorem mapM_clone_ok {T : Type} (inst : core.clone.Clone T) (hclone : ∀ y, ∃ y', inst.clone y = ok y')
    (l : List T) : ∃ l', List.mapM inst.clone l = ok l' ∧ l'.length = l.length := by
  induction l with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := hclone x
    obtain ⟨ys, hys, hlen⟩ := ih
    refine ⟨y :: ys, ?_, by simp [hlen]⟩
    rw [List.mapM_cons, hy, hys]
    simp only [Aeneas.Std.bind_tc_ok]
    rfl

theorem from_fn_go_remove {T : Type} (N : Std.Usize) (inst : core.clone.Clone T)
    (s : core.array.repeat.closure T N) (k : ℕ) (hk : k ≤ s.val.length) :
    ∃ s' : core.array.repeat.closure T N, rust_primitives.slice.array_from_fn_go
      (core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT N inst) s k = ok (s.val.take k, s') ∧
      s'.val = s.val.drop k := by
  induction k with
  | zero => exact ⟨s, rust_primitives.slice.array_from_fn_go.eq_1 _ _, by simp⟩
  | succ k ih =>
    obtain ⟨s', hs', hval⟩ := ih (by omega)
    have hpos : (0#usize : Std.Usize).val < s'.val.length := by
      rw [hval, List.length_drop]; simp; omega
    have e2 := rust_primitives.slice.array_from_fn_go.eq_2
      (core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT N inst) s k
    rw [e2, hs']
    simp only [Aeneas.Std.bind_ok,
      core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut,
      rust_primitives.sequence.seq_remove, hpos, ↓reduceDIte]
    erw [Aeneas.Std.bind_ok]
    have hk' : k < s.val.length := by omega
    refine ⟨_, congrArg ok (Prod.ext ?_ rfl), ?_⟩
    · simp only [List.take_add_one, List.getElem?_eq_getElem hk']
      simp [hval]
    · rw [slice_from_val]
      simp [hval]

theorem from_fn_remove_ok {T : Type} (N : Std.Usize) (inst : core.clone.Clone T)
    (s : core.array.repeat.closure T N) (h : N.val ≤ s.val.length) :
    ∃ a, rust_primitives.slice.array_from_fn N
      (core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT N inst) s = ok a := by
  obtain ⟨s', hs', -⟩ := from_fn_go_remove N inst s N.val h
  unfold rust_primitives.slice.array_from_fn
  rw [hs']
  simp only [Aeneas.Std.bind_ok]
  have hl : (List.take N.val s.val).length = N.val := by rw [List.length_take]; omega
  simp only [hl, ↓reduceDIte]
  exact ⟨_, rfl⟩

theorem repeat_ok {T : Type} (N : Std.Usize) (inst : core.clone.Clone T)
    (hclone : ∀ y, ∃ y', inst.clone y = ok y') (x : T) :
    ∃ a, core.array.repeat N inst x = ok a := by
  unfold core.array.repeat rust_primitives.sequence.seq_create
  by_cases h0 : N.val = 0
  · simp only [h0, ↓reduceIte]
    exact bind_exists _ _ (from_fn_remove_ok N inst _ (by rw [h0]; exact Nat.zero_le _))
  · obtain ⟨l', hl', hlen⟩ := mapM_clone_ok inst hclone (List.replicate (N.val - 1) x)
    have hN : (l' ++ [x]).length = N.val := by simp [hlen]; omega
    have hb : (l' ++ [x]).length ≤ Usize.max := by rw [hN]; scalar_tac
    simp only [h0, ↓reduceIte, hl', RustM.match.ok, hb, ↓reduceDIte]
    exact bind_exists _ _ (from_fn_remove_ok N inst _ (by rw [slice_from_val, hN]))

theorem array_u8_clone (a : Array Std.U8 16#usize) :
    ∃ a', (core.Array.Insts.CoreCloneClone 16#usize core.U8.Insts.CoreCloneClone).clone a = ok a' := by
  simp only [core.Array.Insts.CoreCloneClone.clone, core.array.Array.map, rust_primitives.slice.array_map]
  split
  · rename_i h
    exact absurd h ((match_ok_of_exists (foldlM_ok_exists _ (by
      intro s x
      exact ⟨(s.1 ++ [x], s.2), by
        simp [core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut,
          core.U8.Insts.CoreCloneClone.clone]⟩) _ _)).1 _ _)
  · rename_i h
    exact absurd h ((match_ok_of_exists (foldlM_ok_exists _ (by
      intro s x
      exact ⟨(s.1 ++ [x], s.2), by
        simp [core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut,
          core.U8.Insts.CoreCloneClone.clone]⟩) _ _)).2)
  · exact ⟨_, rfl⟩

/-! ## The FORS trees and their key -/

theorem foldId_congr (nodeS : ℕ → ℕ → HashInput → Digest) (e : ℕ) (sib sib' : ℕ → Digest) (n : ℕ)
    (v : Digest) (h : ∀ z, z < n → sib z = sib' z) : foldId nodeS e sib n v = foldId nodeS e sib' n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [foldId_succ, foldId_succ, ih (fun z hz => h z (by omega)), h n (by omega)]

theorem foldId_eq_foldPath (node : ℕ → ℕ → HashInput → Id Digest) (e : ℕ) (sib : ℕ → Digest) (n : ℕ)
    (v : Digest) :
    foldId (fun l j p => Id.run (node l j p)) e sib n v = Id.run (foldPath node e sib n v) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [foldId_succ, ih]; rfl

theorem getElem!_set' {α : Type} [Inhabited α] (l : List α) (a j : ℕ) (x : α) :
    (l.set a x)[j]! = if a = j ∧ j < l.length then x else l[j]! := by
  by_cases h : a = j
  · subst h
    by_cases hj : a < l.length <;> simp [hj]
  · simp [h]

section
variable {π : KeccakState → KeccakState}

/-- One FORS tree: the leaf of its secret, folded up its path, is the statement's
`forsTreeRecover`. -/
theorem fors_tree_spec (hth : ThSpec π) (hk : KeyAdrsSpec) (hw : AdrsWordSpec) (hof : OfIndexSpec)
    (seed : Array Std.U8 16#usize) (idx : Std.U64) (index : Index) (hidx : idx.val = index.val)
    (c s : Std.Usize) (o : lean_sphincs.fors.ForsTreeOpening) (κ : ForsTreeIndex) (hc : c.val = κ.val)
    (hs : s.val < 2 ^ forsTreeHeight) :
    ∃ leaf r, lean_sphincs.fors.fors_leaf seed idx c s o.secret = ok leaf ∧
      keccak256.path_root
        lean_sphincs.fors.fors_root.closure.Insts.CoreOpsFunctionFnTupleUsizeUsizeShared3ArrayArrayU8162ArrayU816
        leaf s o.path.to_slice (seed, idx, c) = ok r ∧
      toDigest r = Id.run (Verification.forsTreeRecover (inId π) (toDigest seed) index κ
        (forsLeafOfNat s.val) (toForsOpening o)) := by
  have hs' : s.val < 2 ^ 10 := hs
  have hleafv : (forsLeafOfNat s.val).val = s.val := Nat.mod_eq_of_lt hs
  have hplen : o.path.to_slice.length = 10 := by simp
  obtain ⟨leaf, hleaf, hleafD⟩ := fors_leaf_spec hth hk hw hof seed idx index hidx c s o.secret κ
    (forsLeafOfNat s.val) hc hleafv.symm
  obtain ⟨r, hr, hv⟩ := path_root_fold
    lean_sphincs.fors.fors_root.closure.Insts.CoreOpsFunctionFnTupleUsizeUsizeShared3ArrayArrayU8162ArrayU816
    (seed, idx, c)
    (fun l j p => Id.run (Verification.tweakableHash (inId π) (toDigest seed) (.forsNode index κ (l + 1) j) p))
    leaf s o.path.to_slice
    (by
      intro z j ch hz hz' hj
      obtain ⟨r, hr, hv⟩ := fors_node_spec hth hk hw hof seed idx index hidx c z j ch κ hc
        (by omega) (by omega)
      refine ⟨r, hr, ?_⟩
      have : z.val - 1 + 1 = z.val := by omega
      rw [hv, this])
    (by omega)
  refine ⟨leaf, r, hleaf, hr, ?_⟩
  rw [hv, hplen, hleafD]
  rw [foldId_congr _ _ _ (fun level => if h : level < forsTreeHeight then (toForsOpening o).path ⟨level, h⟩ else 0)]
  · rw [foldId_eq_foldPath
      (fun l j => Verification.tweakableHash (inId π) (toDigest seed) (.forsNode index κ (l + 1) j))]
    simp only [Verification.forsTreeRecover, Id.run_bind, hleafv]
    rfl
  · intro z hz
    have hz' : z < forsTreeHeight := hz
    simp [hz', toForsOpening]

/-- **`fors_root`** is the statement's `forsRecover`. -/
theorem forsRoot_spec (hth : ThSpec π) (hk : KeyAdrsSpec) (hw : AdrsWordSpec) (hof : OfIndexSpec) :
    ForsRootSpec π := by
  intro seed idx leaves opening index hidx hleaves
  let R : ForsTreeIndex → Digest := fun κ => Id.run (Verification.forsTreeRecover (inId π)
    (toDigest seed) index κ (forsLeafOfNat leaves.val[κ.val]!.val) (toForsOpening opening.val[κ.val]!))
  obtain ⟨a0, ha0⟩ := repeat_ok 16#usize core.U8.Insts.CoreCloneClone (fun y => ⟨y, rfl⟩) 0#u8
  obtain ⟨roots0, hroots0⟩ := repeat_ok 24#usize
    (core.Array.Insts.CoreCloneClone 16#usize core.U8.Insts.CoreCloneClone) array_u8_clone a0
  have hFT : lean_sphincs.internals.FORS_TREES.val = 24 := by simp [lean_sphincs.internals.FORS_TREES]
  have hloop : lean_sphincs.fors.fors_root_loop { start := 0#usize, «end» := lean_sphincs.internals.FORS_TREES }
      seed idx leaves opening roots0 ⦃ roots => ∀ κ : ForsTreeIndex, toDigest roots.val[κ.val]! = R κ ⦄ := by
    unfold lean_sphincs.fors.fors_root_loop
    apply loop.spec_decr_nat (fun x => x.1.«end».val - x.1.start.val)
      (fun x => x.1.«end» = lean_sphincs.internals.FORS_TREES ∧ x.1.start.val ≤ 24 ∧
        ∀ κ : ForsTreeIndex, κ.val < x.1.start.val → toDigest x.2.val[κ.val]! = R κ)
    · rintro ⟨⟨i, en⟩, roots⟩ ⟨hen, hi, hinv⟩
      simp only at hen hi hinv
      subst hen
      unfold lean_sphincs.fors.fors_root_loop.body
      step with range_next_spec as ⟨r, it, hnext⟩
      rcases hnext with ⟨hlt, s', hs', rfl, rfl⟩ | ⟨hge, rfl, rfl⟩
      · simp only
        have hi24 : i.val < 24 := by omega
        step as ⟨s, hs1, hs2⟩
        step as ⟨tree, ht1, ht2⟩
        have hl : i.val < leaves.val.length := hs1
        have ho : i.val < opening.val.length := ht1
        have hsv : s.val < 2 ^ forsTreeHeight := by
          have := hleaves ⟨i.val, hi24⟩
          rw [getElem!_pos leaves.val i.val hl] at this
          rw [hs2]; exact this
        obtain ⟨leaf, r, hleaf, hr, hv⟩ := fors_tree_spec hth hk hw hof seed idx index hidx i s tree
          ⟨i.val, hi24⟩ rfl hsv
        simp only [hleaf, core.array.Array.as_slice, rust_primitives.slice.array_as_slice, hr,
          Aeneas.Std.bind_ok]
        step as ⟨a1, ha1⟩
        have hrl : roots.val.length = 24 := roots.property
        refine ⟨by omega, ?_, by omega⟩
        intro κ hκ
        rw [ha1, Array.set_val_eq, getElem!_set']
        by_cases hik : i.val = κ.val
        · have hκe : κ = ⟨i.val, hi24⟩ := Fin.ext hik.symm
          have hcond : i.val = κ.val ∧ κ.val < roots.val.length := ⟨hik, by rw [hrl]; exact κ.isLt⟩
          rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), hv]
          subst hκe
          simp only [R]
          rw [getElem!_pos leaves.val i.val hl, getElem!_pos opening.val i.val ho, ← hs2, ← ht2]
        · have hcond : ¬(i.val = κ.val ∧ κ.val < roots.val.length) := fun h => hik h.1
          rw [ite_eq_right_of_eq_false _ _ (eq_false hcond)]
          exact hinv κ (by omega)
      · simp only [WP.spec_ok]
        intro κ
        exact hinv κ (by have := κ.isLt; simp only [forsTreeCount] at this; omega)
    · exact ⟨rfl, by simp, fun κ h => absurd h (by simp)⟩
  obtain ⟨roots1, hroots1, hR⟩ := WP.spec_imp_exists hloop
  obtain ⟨a, ha, hA⟩ := fors_adrs_spec hk hof idx index hidx lean_sphincs.hash.FORS_ROOTS .forsRoots
    (by simp [lean_sphincs.hash.FORS_ROOTS, AddressType.word])
  have hslice : 16 * roots1.to_slice.length ≤ Usize.max := by
    have : roots1.to_slice.length = 24 := by simp
    rw [this]; scalar_tac
  obtain ⟨d, hd, hval⟩ := th_digests_adrs hth seed a _ roots1.to_slice hA hslice
  have hlen1 : roots1.val.length = 24 := roots1.property
  have hpay : digestsPayload R = bytes ((roots1.val.map Array.val).flatten) := by
    have hof' : List.ofFn R = roots1.val.map toDigest := by
      apply List.ext_getElem
      · rw [List.length_ofFn, List.length_map, hlen1]
        rfl
      · intro n h1 h2
        have hn : n < 24 := by rw [List.length_ofFn] at h1; exact h1
        rw [List.getElem_ofFn, List.getElem_map, ← hR ⟨n, hn⟩, getElem!_pos roots1.val n (by omega)]
    rw [bytes_flatten, digestsPayload, hof']
    exact flatMap_map' _ _ _
  refine ⟨d, ?_, ?_⟩
  · simp only [lean_sphincs.fors.fors_root, ha0, hroots0, hroots1, lean_sphincs.fors.fors_key, ha,
      core.array.Array.as_slice, rust_primitives.slice.array_as_slice, Aeneas.Std.bind_ok]
    exact hd
  · rw [hval]
    simp only [Verification.forsRecover, Id.run_bind, sequenceFin_id, Verification.forsPublicKey,
      Verification.tweakableHash, hashDomainFields]
    have hts : roots1.to_slice.val = roots1.val := by simp
    rw [hts, ← hpay]

end
