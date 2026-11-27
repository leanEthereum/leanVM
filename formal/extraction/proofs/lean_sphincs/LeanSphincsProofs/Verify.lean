import LeanSphincsProofs.Common

/-!
# `verify`

The loop of `verify` over the three layers, and with it the theorem this package is for: given each
function's theorem (`Defs.lean`), the extracted `verify` returns the statement's `Verification.verify`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation Sphincs
open LeanVM.Semantics (KeccakState)
open lean_sphincs
open Keccak256Proofs

namespace LeanSphincsProofs

/-! ## Where a layer's path sits -/

/-- `path_range`'s loop invariant: below layer `i ≤ 2` are `8 i` path nodes. -/
def pathRangeInv (i : Std.Usize) (start : Std.Usize) : RustM Prop := ok (start.val = 8 * i.val)

theorem layerHeights_val : internals.LAYER_HEIGHTS.val = [8#usize, 8#usize, 10#usize] := by
  simp [internals.LAYER_HEIGHTS]

theorem layerHeights_getElem (i : ℕ) (h : i < internals.LAYER_HEIGHTS.val.length) :
    (internals.LAYER_HEIGHTS.val[i]).val = if i = 2 then 10 else 8 := by
  have hv := layerHeights_val
  have h3 : i < 3 := by simpa [hv] using h
  simp only [hv]
  interval_cases i <;> simp

@[spec]
theorem path_range_loop_spec (layer : Std.Usize) (hl : layer.val ≤ 2) :
    ⦃ ⌜ True ⌝ ⦄
    scheme.path_range_loop { start := 0#usize, «end» := layer } 0#usize
    ⦃ ⇓ r => ⌜ (pathRangeInv layer r).holds ⌝ ⦄ := by
  unfold scheme.path_range_loop
  apply Hax.loop_range_spec_unsigned (inv := pathRangeInv)
  · simp
  · simp [pathRangeInv]
  · intro acc i _ hi hinv
    hax_mvcgen [scheme.path_range_loop.body, pathRangeInv]
    case vc1.hQ =>
      rename_i hacc hlt s hs r hr r' hr'
      obtain ⟨hlen, rfl⟩ := hr
      have := layerHeights_getElem i.val hlen
      refine ⟨hlt, trivial, hs, ?_⟩
      simp only [pathRangeInv, holds_ok]
      split_ifs at this <;> omega
    case vc2.h_fail =>
      rename_i hacc hlt s hs r hr hov
      obtain ⟨hlen, rfl⟩ := hr
      have := layerHeights_getElem i.val hlen
      exfalso
      split_ifs at this <;> scalar_tac
    case vc3.h_fail =>
      rename_i hlen
      have : internals.LAYER_HEIGHTS.length = 3 := by simp [Array.length, layerHeights_val]
      omega
    case vc1.hQ =>
      rename_i hacc hge
      have : i.val = layer.val := by omega
      rw [hacc, this]

/-- `path_range`: layer `l`'s path is the `h_l` nodes after the `8 l` of the layers below. -/
theorem path_range_spec (layer : Std.Usize) (hl : layer.val ≤ 2) :
    ⦃ ⌜ True ⌝ ⦄
    scheme.path_range layer
    ⦃ ⇓ r => ⌜ r.start.val = 8 * layer.val ∧
      r.«end».val = 8 * layer.val + (if layer.val = 2 then 10 else 8) ⌝ ⦄ := by
  have hlen3 : internals.LAYER_HEIGHTS.length = 3 := by simp [Array.length, layerHeights_val]
  hax_mvcgen [scheme.path_range, pathRangeInv]
  case vc2.hQ =>
    rename_i r0 r1 h1 r2 h2 h0
    obtain ⟨hlen, rfl⟩ := h1
    have := layerHeights_getElem layer.val hlen
    refine ⟨h0, ?_⟩
    rw [h2, h0, this]
  case vc3.h_fail =>
    rename_i r0 r1 h1 hov h0
    obtain ⟨hlen, rfl⟩ := h1
    have := layerHeights_getElem layer.val hlen
    exfalso
    split_ifs at this <;> scalar_tac
  case vc4.h_fail => rename_i hge _; omega

/-- A slice of a slice, by a range within it. -/
theorem slice_index_range {T : Type} (s : Slice T) (r : core.ops.range.Range Std.Usize)
    (h1 : r.start.val ≤ r.«end».val) (h2 : r.«end».val ≤ s.length) :
    ∃ s', core.Slice.Insts.CoreOpsIndexIndex.index
        (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s r = ok s' ∧
      s'.val = List.slice r.start.val r.«end».val s.val := by
  have h1' : r.start ≤ r.«end» := by scalar_tac
  have h2' : r.«end».val ≤ s.val.length := h2
  simp [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice, h1', h1, h2']

/-- `LeanSphincsSignature::path`: layer `l`'s path, a slice of `paths`. -/
theorem path_eq (sig : scheme.LeanSphincsSignature) (layer : Std.Usize) (hl : layer.val ≤ 2) :
    ∃ s, scheme.LeanSphincsSignature.path sig layer = ok s ∧
      s.val = List.slice (8 * layer.val)
        (8 * layer.val + (if layer.val = 2 then 10 else 8)) sig.paths.val := by
  obtain ⟨r, hr⟩ := Hax.triple_noThrow_exists_ok (path_range_spec layer hl)
  obtain ⟨hs, he⟩ := Hax.triple_noThrow_elim (path_range_spec layer hl) hr
  have hlen : sig.paths.val.length = 26 := by simp
  obtain ⟨s, hs1, hs2⟩ := slice_index_range sig.paths.to_slice r (by omega)
    (by show r.«end».val ≤ sig.paths.to_slice.val.length; simp; split_ifs at he <;> omega)
  refine ⟨s, ?_, ?_⟩
  · simp only [scheme.LeanSphincsSignature.path, hr, Aeneas.Std.bind_ok,
      core.Array.Insts.CoreOpsIndexIndex.index, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice]
    exact hs1
  · rw [hs2, hs, he]; simp

/-! ## The loop's iterator -/

/-- One step of `layers.iter().enumerate()`: the next layer and its number. -/
theorem enumerate_next {T : Type} (s : Slice T) (x : T) (xs : List T) (c : Std.Usize)
    (hs : s.val = x :: xs) (hc : c.val + 1 ≤ Usize.max) :
    ∃ it, core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
        { iter := s, count := c } = ok (core.option.Option.Some (c, x), it) ∧
      it.iter.val = xs ∧ it.count.val = c.val + 1 := by
  have hlen : s.val.length = xs.length + 1 := by simp [hs]
  have hne : ¬ (Slice.len s = 0#usize) := by
    intro h
    have : (Slice.len s).val = 0 := by rw [h]; rfl
    scalar_tac
  have t : ⦃ ⌜ True ⌝ ⦄
      core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
        { iter := s, count := c }
      ⦃ ⇓ r => ⌜ r.1 = core.option.Option.Some (c, x) ∧ r.2.iter.val = xs ∧
        r.2.count.val = c.val + 1 ⌝ ⦄ := by
    hax_mvcgen [core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      rust_primitives.sequence.seq_len, rust_primitives.sequence.seq_remove]
    case vc2.hQ =>
      rename_i r hr
      refine ⟨?_, ?_, ?_⟩
      · simp [hs]
      · simp [hs]
      · scalar_tac
    case vc3.h_fail => scalar_tac
    case vc4.hQ => rename_i h; exact absurd (by simp [hlen] : (0#usize).val < s.val.length) h
  obtain ⟨⟨o, it⟩, hr, h0, h1, h2⟩ := ok_of_triple t
  exact ⟨it, by rw [hr]; simp only at h0; rw [h0], h1, h2⟩

/-- The iterator, once every layer is taken, gives none. -/
theorem enumerate_next_nil {T : Type} (s : Slice T) (c : Std.Usize) (hs : s.val = []) :
    core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
        { iter := s, count := c } =
      ok (core.option.Option.None, { iter := s, count := c }) := by
  have h0 : Slice.len s = 0#usize := by
    rw [UScalar.eq_equiv]
    simp [hs]
  simp [core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    rust_primitives.sequence.seq_len, h0]
  rfl

theorem foldPath_congr {m : Type → Type} [Monad m] (node : ℕ → ℕ → HashInput → m Digest)
    (leaf : ℕ) (p q : ℕ → Digest) :
    ∀ (n : ℕ) (v : Digest), (∀ z < n, p z = q z) →
      foldPath node leaf p n v = foldPath node leaf q n v
  | 0, _, _ => rfl
  | n + 1, v, h => by
    simp only [foldPath]
    rw [foldPath_congr node leaf p q n v (fun z hz ↦ h z (by omega)), h n (by omega)]

/-! ## One layer -/

/-- A turn of `verify`'s loop, given what its first three calls return. -/
theorem verify_body_eq (root rand : Array Std.U8 16#usize)
    (fors : Array fors.ForsTreeOpening 24#usize) (layers : Array scheme.LayerSignature 3#usize)
    (paths : Array (Array Std.U8 16#usize) 26#usize) (seed : Array Std.U8 16#usize) (idx : Std.U64)
    (s : core.slice.iter.Iter scheme.LayerSignature) (c : Std.Usize) (x : scheme.LayerSignature)
    (it' : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter scheme.LayerSignature))
    (key : wots.OtsKey) (o : core.option.Option (Array Std.U8 64#usize × Array Std.U8 16#usize))
    (signed : Array Std.U8 16#usize)
    (hnext : core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT scheme.LayerSignature)
        { iter := s, count := c } = ok (core.option.Option.Some (c, x), it'))
    (hk : wots.OtsKey.of_index c idx = ok key)
    (ho : wots.wots_leaf seed key signed x.counter x.wots = ok o) :
    scheme.verify_loop.body root rand fors layers paths seed idx { iter := s, count := c } signed =
      (match o with
        | .None => ok (.done false)
        | .Some p1 => do
          let s ← scheme.LeanSphincsSignature.path ⟨rand, fors, layers, paths⟩ c
          let signed1 ← scheme.tree_root seed key p1.2 s
          ok (.cont (it', signed1))) := by
  unfold scheme.verify_loop.body
  rw [hnext, Aeneas.Std.bind_ok]
  refine Eq.trans (b := (do
    let key ← wots.OtsKey.of_index c idx
    let o1 ← wots.wots_leaf seed key signed x.counter x.wots
    match o1 with
      | .None => ok (.done false)
      | .Some p1 => do
        let s ← scheme.LeanSphincsSignature.path ⟨rand, fors, layers, paths⟩ c
        let signed1 ← scheme.tree_root seed key p1.2 s
        ok (.cont (it', signed1)))) rfl ?_
  rw [hk, Aeneas.Std.bind_ok, ho, Aeneas.Std.bind_ok]
  cases o <;> rfl

section
variable {π : KeccakState → KeccakState}

/-- One turn of `verify`'s loop at layer `l`: `false` if the layer's counter does not encode
what it signs, else on to the next layer with the root of this one's tree. -/
theorem verify_body_step (hof : OfIndexSpec) (hwots : WotsLeafSpec π) (htree : TreeRootSpec π)
    (pk : scheme.LeanSphincsPublicKey) (sig : scheme.LeanSphincsSignature) (idx : Std.U64)
    (index : Index) (hidx : idx.val = index.val) (l : Layer)
    (it : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter scheme.LayerSignature))
    (hit : it.iter.val = sig.layers.val.drop l.val) (hc : it.count.val = l.val)
    (signed : Array Std.U8 16#usize) :
    ∃ r, scheme.verify_loop.body pk.root sig.randomizer sig.fors sig.layers sig.paths pk.pk_seed
        idx it signed = ok r ∧
      ∀ o, Id.run (Verification.otsLeaf (inId π) (toDigest pk.pk_seed) l (treeOfIndex l index)
          (leafOfIndex l index) (toDigest signed) ((toSignature sig).layers l).counter
          ((toSignature sig).layers l).chainValues) = o →
      (o = none → r = .done false) ∧
      ∀ value, o = some value → ∃ it' signed', r = .cont (it', signed') ∧
          it'.iter.val = sig.layers.val.drop (l.val + 1) ∧ it'.count.val = l.val + 1 ∧
          toDigest signed' = Id.run (Verification.treeFold (inId π) (toDigest pk.pk_seed) l
            (treeOfIndex l index) (leafOfIndex l index) (Verification.layerPath (toSignature sig) l)
            (layerHeight l) value) := by
  have hl3 : l.val < 3 := l.isLt
  have hlen : sig.layers.val.length = 3 := by simp
  have hdrop : sig.layers.val.drop l.val = sig.layers.val[l.val]! :: sig.layers.val.drop (l.val + 1) := by
    rw [List.drop_eq_getElem_cons (by omega), getElem!_pos sig.layers.val l.val (by omega)]
  obtain ⟨s, c⟩ := it
  simp only at hit hc
  obtain ⟨it', hnext, hi1, hi2⟩ := enumerate_next s _ _ c (hit.trans hdrop) (by scalar_tac)
  obtain ⟨key, hk1, hk2⟩ := hof c idx l index hc hidx
  obtain ⟨o, ho1, ho2⟩ := hwots pk.pk_seed key signed (sig.layers.val[l.val]!).counter
    (sig.layers.val[l.val]!).wots l _ _ hk2
  rw [verify_body_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnext hk1 ho1]
  have hcl : c.val ≤ 2 := by omega
  simp only [toSignature, toLayerSignature]
  rw [← ho2]
  match o, ho1 with
  | .None, _ =>
    refine ⟨_, rfl, ?_⟩
    rintro _ rfl
    exact ⟨fun _ ↦ rfl, fun v hv ↦ by cases hv⟩
  | .Some (cw, leaf), _ =>
    obtain ⟨p, hp1, hp2⟩ := path_eq ⟨sig.randomizer, sig.fors, sig.layers, sig.paths⟩ c hcl
    have hplen : p.length = layerHeight l := by
      show p.val.length = _
      rw [hp2]
      have : sig.paths.val.length = 26 := by simp
      simp only [List.slice, layerHeight, hc, List.length_take, List.length_drop, this]
      split_ifs <;> omega
    obtain ⟨r, hr1, hr2⟩ := htree pk.pk_seed key leaf p l _ _ hk2
      (by rw [hplen]; simp only [layerHeight]; split_ifs <;> omega)
    refine ⟨.cont (it', r), by simp only [hp1, hr1, Aeneas.Std.bind_ok], ?_⟩
    rintro _ rfl
    refine ⟨fun h ↦ (by cases h), ?_⟩
    intro value hv
    obtain rfl : toDigest leaf = value := Option.some.inj hv
    refine ⟨it', r, rfl, hi1, by omega, ?_⟩
    rw [hr2, hplen]
    simp only [Verification.treeFold]
    congr 1
    apply foldPath_congr
    intro z hz
    have hz26 : 8 * l.val + z < 26 := by
      simp only [layerHeight] at hz
      split_ifs at hz <;> omega
    have hpz : z < p.val.length := by rw [← hplen] at hz; exact hz
    simp only [Verification.layerPath, hz, ↓reduceDIte, toLayerSignature, bitsBelowLayer]
    congr 1
    rw [getElem!_pos p.val z hpz, getElem!_pos sig.paths.val _ (by simpa using hz26)]
    simp only [hp2, List.slice, hc, List.getElem_take, List.getElem_drop]

/-! ## The loop -/

/-- The loop past the top layer: nothing is left, and the verdict is whether what the layers
reached is `PK.root`. -/
theorem verify_loop_done (pk : scheme.LeanSphincsPublicKey) (sig : scheme.LeanSphincsSignature)
    (idx : Std.U64)
    (it : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter scheme.LayerSignature))
    (hit : it.iter.val = []) (signed : Array Std.U8 16#usize) :
    scheme.verify_loop it pk.root sig.randomizer sig.fors sig.layers sig.paths pk.pk_seed idx signed =
      ok (decide (signed = pk.root)) := by
  obtain ⟨s, c⟩ := it
  have hb : scheme.verify_loop.body pk.root sig.randomizer sig.fors sig.layers sig.paths pk.pk_seed
      idx { iter := s, count := c } signed = ok (.done (decide (signed = pk.root))) := by
    unfold scheme.verify_loop.body
    rw [enumerate_next_nil s c hit, Aeneas.Std.bind_ok]
    simp only [array_eq, Aeneas.Std.bind_ok]
    rfl
  unfold scheme.verify_loop
  rw [loop.eq_def]
  simp only [hb, Aeneas.Std.bind_ok]

/-- The layer the loop is on with `k + 1` layers left. -/
def layerAt (k : ℕ) : Layer := ⟨2 - k, by unfold layerCount; omega⟩

/-- The statement's walk, one layer unfolded. -/
theorem verifyLayers_succ (seed : PublicParameter) (index : Index) (S : Sphincs.Signature) (k : ℕ)
    (hk : k < 3) (msg : Digest) :
    Id.run (Verification.verifyLayers (inId π) seed index S (k + 1) msg) =
      match Id.run (Verification.otsLeaf (inId π) seed (layerAt k)
          (treeOfIndex (layerAt k) index) (leafOfIndex (layerAt k) index) msg
          (S.layers (layerAt k)).counter (S.layers (layerAt k)).chainValues) with
      | none => none
      | some value =>
        if k = 0 then
          some (Id.run (Verification.treeFold (inId π) seed (layerAt k)
            (treeOfIndex (layerAt k) index) (leafOfIndex (layerAt k) index)
            (Verification.layerPath S (layerAt k)) (layerHeight (layerAt k)) value))
        else
          Id.run (Verification.verifyLayers (inId π) seed index S k
            (Id.run (Verification.treeFold (inId π) seed (layerAt k)
              (treeOfIndex (layerAt k) index) (leafOfIndex (layerAt k) index)
              (Verification.layerPath S (layerAt k)) (layerHeight (layerAt k)) value))) := by
  have hk' : k < layerCount := hk
  generalize ho : Id.run (Verification.otsLeaf (inId π) seed (layerAt k)
    (treeOfIndex (layerAt k) index) (leafOfIndex (layerAt k) index) msg
    (S.layers (layerAt k)).counter (S.layers (layerAt k)).chainValues) = o
  conv_lhs => unfold Verification.verifyLayers
  simp only [hk', ↓reduceDIte, Id.run_bind]
  split
  · rename_i value heq
    obtain rfl : o = some value := ho.symm.trans heq
    simp only
    split_ifs <;> rfl
  · rename_i hnone
    cases o with
    | none => rfl
    | some value => exact (hnone value ho).elim

/-- **The loop**, with `k + 1` layers left: the statement's walk up the hypertree, compared with
`PK.root`. -/
theorem verify_loop_eq (hof : OfIndexSpec) (hwots : WotsLeafSpec π) (htree : TreeRootSpec π)
    (pk : scheme.LeanSphincsPublicKey) (sig : scheme.LeanSphincsSignature) (idx : Std.U64)
    (index : Index) (hidx : idx.val = index.val) :
    ∀ (k : ℕ) (_ : k < 3)
      (it : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter scheme.LayerSignature))
      (signed : Array Std.U8 16#usize),
      it.iter.val = sig.layers.val.drop (2 - k) → it.count.val = 2 - k →
      scheme.verify_loop it pk.root sig.randomizer sig.fors sig.layers sig.paths pk.pk_seed idx
          signed =
        ok (match Id.run (Verification.verifyLayers (inId π) (toDigest pk.pk_seed) index
            (toSignature sig) (k + 1) (toDigest signed)) with
          | none => false
          | some root => decide (root = toDigest pk.root)) := by
  intro k
  induction k with
  | zero =>
    intro hk it signed hit hc
    obtain ⟨r, hr, hm⟩ := verify_body_step hof hwots htree pk sig idx index hidx (layerAt 0) it
      hit hc signed
    refine Eq.trans ?_ (congrArg (fun o ↦ ok (match o with
      | none => false
      | some root => decide (root = toDigest pk.root)))
      (verifyLayers_succ (π := π) (toDigest pk.pk_seed) index (toSignature sig) 0 hk
        (toDigest signed)).symm)
    unfold scheme.verify_loop
    rw [loop.eq_def]
    simp only [hr, Aeneas.Std.bind_ok]
    generalize ho : Id.run (Verification.otsLeaf (inId π) (toDigest pk.pk_seed) (layerAt 0)
        (treeOfIndex (layerAt 0) index) (leafOfIndex (layerAt 0) index) (toDigest signed)
        ((toSignature sig).layers (layerAt 0)).counter
        ((toSignature sig).layers (layerAt 0)).chainValues) = o
    have hm' := hm o ho
    clear hm ho
    rcases o with _ | value
    · obtain rfl := hm'.1 rfl
      rfl
    · obtain ⟨it', signed', rfl, hi1, -, hd⟩ := hm'.2 value rfl
      have hnil : it'.iter.val = [] := by rw [hi1]; simp [layerAt]
      have := verify_loop_done pk sig idx it' hnil signed'
      unfold scheme.verify_loop at this
      simp only [this, ↓reduceIte, ← hd]
      exact congrArg ok (decide_eq_decide.mpr ⟨fun h ↦ congrArg toDigest h, toDigest_inj⟩)
  | succ k ih =>
    intro hk it signed hit hc
    obtain ⟨r, hr, hm⟩ := verify_body_step hof hwots htree pk sig idx index hidx (layerAt (k + 1))
      it hit hc signed
    refine Eq.trans ?_ (congrArg (fun o ↦ ok (match o with
      | none => false
      | some root => decide (root = toDigest pk.root)))
      (verifyLayers_succ (π := π) (toDigest pk.pk_seed) index (toSignature sig) (k + 1) hk
        (toDigest signed)).symm)
    unfold scheme.verify_loop
    rw [loop.eq_def]
    simp only [hr, Aeneas.Std.bind_ok]
    generalize ho : Id.run (Verification.otsLeaf (inId π) (toDigest pk.pk_seed) (layerAt (k + 1))
        (treeOfIndex (layerAt (k + 1)) index) (leafOfIndex (layerAt (k + 1)) index) (toDigest signed)
        ((toSignature sig).layers (layerAt (k + 1))).counter
        ((toSignature sig).layers (layerAt (k + 1))).chainValues) = o
    have hm' := hm o ho
    clear hm ho
    rcases o with _ | value
    · obtain rfl := hm'.1 rfl
      rfl
    · obtain ⟨it', signed', rfl, hi1, hi2, hd⟩ := hm'.2 value rfl
      have := ih (by omega) it' signed' (by rw [hi1]; congr 1; simp only [layerAt]; omega)
        (by rw [hi2]; simp only [layerAt]; omega)
      unfold scheme.verify_loop at this
      simp only [this, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, ← hd]

/-! ## `verify` -/

/-- **`verify`**, given each function's theorem: the extracted Rust verifier returns, and returns
the statement's verdict. -/
theorem verify_of_specs (hmd : MessageDigestSpec π) (hfors : ForsRootSpec π) (hof : OfIndexSpec)
    (hwots : WotsLeafSpec π) (htree : TreeRootSpec π) : VerifySpec π := by
  intro pk m sig
  obtain ⟨idx, leaves, hmd1, hidx, hleaves⟩ := hmd pk sig.randomizer m
  generalize hD : Id.run (Verification.messageDigest (inId π) (toPublicKey pk)
    (toDigest sig.randomizer) (toMessage m)) = D at hidx hleaves
  obtain ⟨fk, hf1, hf2⟩ := hfors pk.pk_seed idx leaves sig.fors (digestIndex D) hidx
    (fun κ ↦ by rw [hleaves κ]; exact (digestForsLeaves D κ).isLt)
  have hloop := verify_loop_eq hof hwots htree pk sig idx (digestIndex D) hidx 2 (by decide)
    { iter := sig.layers.to_slice, count := 0#usize } fk (by simp) rfl
  unfold scheme.verify
  simp only [hmd1, Aeneas.Std.bind_ok]
  have hl : (fun κ : ForsTreeIndex ↦ forsLeafOfNat (leaves.val[κ.val]!).val) = digestForsLeaves D := by
    funext κ
    apply Fin.ext
    rw [← hleaves κ]
    exact Nat.mod_eq_of_lt (by rw [hleaves κ]; exact (digestForsLeaves D κ).isLt)
  rw [hl] at hf2
  simp [hf1, core.array.Array.as_slice, core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.default, rust_primitives.slice.array_as_slice,
    rust_primitives.sequence.seq_from_slice, core.iter.adapters.enumerate.Enumerate.new]
  erw [Aeneas.Std.bind_ok]
  refine Eq.trans hloop (congrArg ok ?_)
  clear hloop
  unfold Verification.verify
  simp only [Id.run_bind]
  have hD' : Id.run (Verification.messageDigest (inId π) (toPublicKey pk) (toSignature sig).randomizer
      (toMessage m)) = D := hD
  rw [hD']
  have hf2' : Id.run (Verification.forsRecover (inId π) (toPublicKey pk).publicSeed (digestIndex D)
      (digestForsLeaves D) (toSignature sig).forsOpening) = toDigest fk := hf2.symm
  rw [hf2']
  have hv : Id.run (Verification.verifyLayers (inId π) (toPublicKey pk).publicSeed (digestIndex D)
      (toSignature sig) layerCount (toDigest fk)) =
    Id.run (Verification.verifyLayers (inId π) (toDigest pk.pk_seed) (digestIndex D)
      (toSignature sig) (2 + 1) (toDigest fk)) := rfl
  rw [hv]
  generalize Id.run (Verification.verifyLayers (inId π) (toDigest pk.pk_seed) (digestIndex D)
      (toSignature sig) (2 + 1) (toDigest fk)) = v
  rcases v with _ | root <;> rfl

end

end LeanSphincsProofs
