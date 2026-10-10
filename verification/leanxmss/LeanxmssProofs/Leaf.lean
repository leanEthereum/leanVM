import LeanxmssProofs.Hash

/-!
# Chains and the one-time public key's leaf

The guest walks each chain from its digit to its end with `Chains::walk`, inside `wots_leaf`'s hash of the ends: the
leaf is the specification's `otsLeaf` of `otsRecover`.
-/

open Aeneas Aeneas.Std Result WP
open EthCryptographySpecs.Xmss EthCryptographySpecs.Xmss.Constants

namespace leanxmss.Proofs.Leaf

open Bytes

/-- The chain template's bytes: the chain tweak at position `p` for leaf `e`, the public parameter, the value `v`. -/
def tmpl (pp : Std.Array U64 2#usize) (e : Std.U32) (p : Nat) (v : List UInt8) : List UInt8 :=
  [0, 1, 0, 0] ++ le 4 p ++ ([0, 0, 0, 0] ++ le 4 e.val ++ ofWords pp.val) ++ v

/-- The first two words of BLAKE2s are the first 16 bytes of the hash. -/
theorem digest2 (bs : List UInt8) :
    ofWords [(blake2s bs).val[0]!, (blake2s bs).val[1]!] = (Blake2s.hash (toBA bs)).toList.take 16 := by
  simp only [blake2s, digestWords, Std.Array.make_val]
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ, ofWords_cons, ofWords_nil, List.append_nil]
  rw [le_word _ (by simp), le_word _ (by simp)]
  simp only [List.drop_zero]
  rw [show (16 : Nat) = 8 + 8 from rfl, List.take_add]

/-- The chain tweak's bytes, at a position below `2^32`. -/
theorem chainTweak (p : Nat) (hp : p < 2 ^ 32) (e : Std.U32) :
    (makeTweak .chain (UInt32.ofNat p) (u32 e)).toList = [0, 1, 0, 0] ++ le 4 p ++ [0, 0, 0, 0] ++ le 4 e.val := by
  have h : (UInt32.ofNat p).toNat = p := by simp; omega
  rw [makeTweak_toList, wordBytes_toList, wordBytes_toList, u32_toNat, h]
  rfl

/-- One step of `Template::chain` on a chain template writes the position and the value, keeps the template's
shape, and computes the specification's `chainStep`. -/
theorem chainStep_tmpl (pp : Std.Array U64 2#usize) (e : Std.U32) (i : Fin Constants.V) (s : Fin Constants.CHAIN_LENGTH)
    (p : Nat) (v : List UInt8) (hv : v.length = 16) (value : Std.Array U64 2#usize) :
    (leanvm_guest.Template.chainStep 4 32 (tmpl pp e p v) value (8 * i.val + s.val)).1 =
        tmpl pp e (8 * i.val + s.val) (ofWords value.val) ∧
      Statement.digest (leanvm_guest.Template.chainStep 4 32 (tmpl pp e p v) value (8 * i.val + s.val)).2 =
        chainStep (Statement.digest pp) (u32 e) i s (Statement.digest value) := by
  have h1 : splice (splice (tmpl pp e p v) 4 (le 4 (8 * i.val + s.val))) 32 (ofWords value.val) =
      tmpl pp e (8 * i.val + s.val) (ofWords value.val) := by
    unfold tmpl
    rw [show [(0 : UInt8), 1, 0, 0] ++ le 4 p ++ ([0, 0, 0, 0] ++ le 4 e.val ++ ofWords pp.val) ++ v =
      [(0 : UInt8), 1, 0, 0] ++ le 4 p ++ (([0, 0, 0, 0] ++ le 4 e.val ++ ofWords pp.val) ++ v) by simp]
    have h := splice_exact [(0 : UInt8), 1, 0, 0] (le 4 p) (([0, 0, 0, 0] ++ le 4 e.val ++ ofWords pp.val) ++ v)
      (le 4 (8 * i.val + s.val)) (by simp)
    rw [show ([(0 : UInt8), 1, 0, 0]).length = 4 from rfl] at h
    rw [h]
    rw [show [(0 : UInt8), 1, 0, 0] ++ le 4 (8 * i.val + s.val) ++
        (([0, 0, 0, 0] ++ le 4 e.val ++ ofWords pp.val) ++ v) =
      ([(0 : UInt8), 1, 0, 0] ++ le 4 (8 * i.val + s.val) ++ ([0, 0, 0, 0] ++ le 4 e.val ++ ofWords pp.val)) ++ v
      by simp]
    rw [splice_append_right _ _ _ _ (by simp)]
    simp [splice, hv]
  have hp : 8 * i.val + s.val < 2 ^ 32 := by
    have := i.isLt; have := s.isLt; simp [Constants.V, Constants.CHAIN_LENGTH, Constants.W] at *; omega
  have hin : toBA (tmpl pp e (8 * i.val + s.val) (ofWords value.val)) =
      tweakInput (Statement.digest pp) .chain (chainPosition i s) (u32 e) (packBytes (Statement.digest value)) := by
    have hc : chainPosition i s = UInt32.ofNat (8 * i.val + s.val) := rfl
    rw [tweakInput, hc, packBytes_eq, chainTweak _ hp, packBytes_publicParam, packBytes_digest, ← toBA_append,
      ← toBA_append]
    unfold tmpl
    simp
  simp only [leanvm_guest.Template.chainStep, h1, true_and]
  apply vector_eq_of_toList
  rw [digest_toList, Std.Array.make_val, digest2, chainStep, tweakHash_toList, hin]

/-- `k` steps of `Template::chain` from position `8 i + s` walk the specification's chain `i` from `s`. -/
theorem fold_tmpl (pp : Std.Array U64 2#usize) (e : Std.U32) (i : Fin Constants.V)
    (f : List UInt8 × Std.Array U64 2#usize → Nat → List UInt8 × Std.Array U64 2#usize)
    (hf : ∀ t v c, f (t, v) c = leanvm_guest.Template.chainStep 4 32 t v c)
    (s k : Nat) (h : s + k < Constants.CHAIN_LENGTH) (p : Nat) (v : List UInt8) (hv : v.length = 16)
    (value : Std.Array U64 2#usize) :
    ∃ p' v', ((List.range' (8 * i.val + s) k).foldl f (tmpl pp e p v, value)).1 = tmpl pp e p' v' ∧ v'.length = 16 ∧
      Statement.digest ((List.range' (8 * i.val + s) k).foldl f (tmpl pp e p v, value)).2 =
        chain (Statement.digest pp) (u32 e) i s k h (Statement.digest value) := by
  induction k with
  | zero => exact ⟨p, v, rfl, hv, rfl⟩
  | succ k ih =>
    obtain ⟨p', v', h1, hv', h2⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range' (8 * i.val + s) k).foldl f (tmpl pp e p v, value) = r at h1 h2
    obtain ⟨t, w⟩ := r
    simp only at h1 h2
    subst h1
    have hc := chainStep_tmpl pp e i ⟨s + k, by omega⟩ p' v' hv' w
    simp only at hc
    rw [hf, show 8 * i.val + s + 1 * k = 8 * i.val + (s + k) by omega, hc.1, hc.2, h2]
    exact ⟨_, _, rfl, by simp, rfl⟩

/-- `CHAIN_LENGTH` is 8. -/
theorem chainLength_ok : leanxmss.CHAIN_LENGTH = ok 8#usize := by
  simp only [leanxmss.CHAIN_LENGTH, leanxmss.W]
  apply eq_ok_of_spec
  step*
  · have : (3#usize : Usize).val = 3 := rfl
    rw [this]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
  · apply UScalar.eq_of_val_eq
    rw [x_post]
    have : (8#usize : Usize).val = 8 := rfl
    rw [this]
    rcases System.Platform.numBits_eq with h | h <;> simp [Usize.size, Usize.numBits, h]

/-- The guest's chain tweak type is the specification's. -/
theorem tweakChain_eq : leanxmss.TWEAK_CHAIN = tyByte .chain := by
  simp only [leanxmss.TWEAK_CHAIN]; rfl

/-- The guest's leaf tweak type is the specification's. -/
theorem tweakWotsPk_eq : leanxmss.TWEAK_WOTS_PK = tyByte .leaf := by
  simp only [leanxmss.TWEAK_WOTS_PK]; rfl

/-- `Chains::new` writes the chain tweak for position 0 and the public parameter, the value zero. -/
theorem new_ok (pp : Std.Array U64 2#usize) (leaf : Std.U32) :
    leanxmss.Chains.new pp leaf = ok ⟨tmpl pp leaf 0 (ofWords [0#u64, 0#u64])⟩ := by
  simp only [leanxmss.Chains.new, tweak_ok, leanvm_guest.Template.new, Std.Array.index_usize]
  simp
  obtain ⟨l, hl⟩ : ∃ l, pp.val = l := ⟨_, rfl⟩
  have hla : l.length = 2 := by rw [← hl]; simp
  have e : [tweakWord0 leanxmss.TWEAK_CHAIN 0#u32, tweakWord1 leaf, pp.val[0]'(by simp), pp.val[1]'(by simp),
      0#u64, 0#u64] = [tweakWord0 (tyByte .chain) 0#u32, tweakWord1 leaf] ++ pp.val ++ [0#u64, 0#u64] := by
    match l, hla with
    | [a0, a1], _ => simp [hl, tweakChain_eq]
  rw [e, ofWords_append, ofWords_append, tweak_bytes, show u32 0#u32 = UInt32.ofNat 0 from rfl,
    chainTweak 0 (by norm_num)]
  simp [tmpl]

/-- `Template::chain` from position `8 i + s` to `8 i + 7` walks chain `i` from `s` to its end. -/
theorem chain_ok (pp : Std.Array U64 2#usize) (e : Std.U32) (i : Fin Constants.V) (s : Nat)
    (hs : s < Constants.CHAIN_LENGTH) (p : Nat) (v : List UInt8) (hv : v.length = 16) (a b : Std.U32)
    (ha : a.val = 8 * i.val + s) (hb : b.val = 8 * i.val + 7) (value : Std.Array U64 2#usize) :
    ∃ value' p' v', leanvm_guest.Template.chain (W1 := 6#usize) 4#usize 32#usize (tmpl pp e p v) ⟨a, b⟩ value =
        ok (value', tmpl pp e p' v') ∧ v'.length = 16 ∧
      Statement.digest value' = chain (Statement.digest pp) (u32 e) i s (Constants.CHAIN_LENGTH - 1 - s)
        (by omega) (Statement.digest value) := by
  have hs' : s ≤ 7 := by simp [Constants.CHAIN_LENGTH, Constants.W] at hs; omega
  obtain ⟨p', v', h1, hv', h2⟩ := fold_tmpl pp e i (fun x c => leanvm_guest.Template.chainStep 4 32 x.1 x.2 c)
    (fun _ _ _ => rfl) s (Constants.CHAIN_LENGTH - 1 - s) (by omega) p v hv value
  have hk : 8 * i.val + 7 - (8 * i.val + s) = Constants.CHAIN_LENGTH - 1 - s := by
    simp [Constants.CHAIN_LENGTH, Constants.W]; omega
  simp only [leanvm_guest.Template.chain]
  simp only [ha, hb, hk]
  simp [hs']
  have key : ∀ r : List UInt8 × Std.Array U64 2#usize, r.1 = tmpl pp e p' v' →
      (let (t, value) := r; (ok (value, t) : Result (Std.Array U64 2#usize × leanvm_guest.Template 6#usize))) =
        ok (r.2, tmpl pp e p' v') := by
    rintro ⟨t, w⟩ h; simp only at h; subst h; rfl
  exact ⟨_, p', v', key _ h1, hv', h2⟩

/-- `Chains::walk` from value `dg` to value 7 of chain `k` walks the specification's chain `k` to its end. -/
theorem walk_ok (pp : Std.Array U64 2#usize) (e : Std.U32) (p : Nat) (v : List UInt8) (hv : v.length = 16)
    (k : Std.Usize) (hk : k.val < Constants.V) (dg en : Std.Usize) (hdg : dg.val < Constants.CHAIN_LENGTH)
    (hen : en.val = 7) (tip : Std.Array U64 2#usize) :
    ∃ value' p' v', leanxmss.Chains.walk ⟨tmpl pp e p v⟩ k ⟨dg, en⟩ tip = ok (value', ⟨tmpl pp e p' v'⟩) ∧
      v'.length = 16 ∧
      Statement.digest value' = chain (Statement.digest pp) (u32 e) ⟨k.val, hk⟩ dg.val
        (Constants.CHAIN_LENGTH - 1 - dg.val) (by omega) (Statement.digest tip) := by
  have hk' : k.val < 42 := hk
  have hdg' : dg.val < 8 := hdg
  suffices h : spec (leanxmss.Chains.walk ⟨tmpl pp e p v⟩ k ⟨dg, en⟩ tip) (fun r => ∃ p' v',
      r.2 = ⟨tmpl pp e p' v'⟩ ∧ v'.length = 16 ∧ Statement.digest r.1 = chain (Statement.digest pp) (u32 e)
        ⟨k.val, hk⟩ dg.val (Constants.CHAIN_LENGTH - 1 - dg.val) (by omega) (Statement.digest tip)) by
    obtain ⟨⟨r1, r2⟩, hr, p', v', h1, h2, h3⟩ := exists_ok_of_spec h
    exact ⟨r1, p', v', by rw [hr, ← h1], h2, h3⟩
  unfold leanxmss.Chains.walk
  simp only [lift, chainLength_ok]
  step*
  have c1 : (UScalar.cast .U32 i2).val = 8 * k.val :=
    by rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by simp [UScalarTy.numBits]; omega)]; omega
  have c2 : (UScalar.cast .U32 dg).val = dg.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by simp [UScalarTy.numBits]; omega)
  have c3 : (UScalar.cast .U32 en).val = en.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by simp [UScalarTy.numBits]; omega)
  obtain ⟨w, p', v', hc, hv', hd⟩ := chain_ok pp e ⟨k.val, hk⟩ dg.val hdg p v hv i4 i6 (by simp; omega)
    (by simp; omega) tip
  rw [hc]
  simp
  exact ⟨p', v', rfl, hv', hd⟩

/-- `CHAIN_LENGTH - 1` is 7. -/
theorem seven_ok : (8#usize - 1#usize : Result Std.Usize) = ok 7#usize := by
  apply eq_ok_of_spec
  step*

/-- `verify`'s closure for chain `k` returns the `k`-th public value `otsRecover` computes, and keeps the template's
shape. -/
theorem callMut_ok (pp : Std.Array U64 2#usize) (leaf : Std.U32) (sig : leanxmss.Signature) (d : leanxmss.Digits)
    (x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V)
    (hd : ∀ i : Std.Usize, (hi : i.val < Constants.V) → ∃ v, leanxmss.Digits.get d i = ok v ∧ v.val = (x[i.val]'hi).val)
    (k : Std.Usize) (hk : k.val < Constants.V) (p : Nat) (v : List UInt8) (hv : v.length = 16) :
    ∃ a p' v' back, leanxmss.verify.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU642.call_mut
        ((⟨tmpl pp leaf p v⟩ : leanxmss.Chains), d, sig) k = ok (a, (⟨tmpl pp leaf p' v'⟩, d, sig), back) ∧
      back (⟨tmpl pp leaf p' v'⟩, d, sig) = (⟨tmpl pp leaf p' v'⟩, d, sig) ∧
      v'.length = 16 ∧
      Statement.digest a =
        (otsRecover (Statement.digest pp) (u32 leaf) (Statement.signature sig).chainElements x)[k.val] := by
  obtain ⟨dg, hget, hdgv⟩ := hd k hk
  have hk' : k.val < sig.chain_tips.val.length := by simp; exact hk
  obtain ⟨w, p', v', hw, hv', hdw⟩ := walk_ok pp leaf p v hv k hk dg 7#usize (by rw [hdgv]; exact (x[k.val]).isLt) rfl
    (sig.chain_tips.val[k.val]'hk')
  refine ⟨w, p', v', fun c3 => (c3.1, d, sig), ?_, rfl, hv', ?_⟩
  · simp [leanxmss.verify.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU642.call_mut, hget, chainLength_ok,
      seven_ok,
      Std.Array.index_usize, List.getElem?_eq_getElem hk', hw]
    rfl
  · rw [hdw]
    simp [otsRecover, Statement.signature, List.getElem?_eq_getElem hk', hdgv]

/-- The ends the guest's leaf hashes, as the specification's. -/
abbrev ends (pp : Std.Array U64 2#usize) (leaf : Std.U32) (sig : leanxmss.Signature)
    (x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V) : Vector Digest Constants.V :=
  otsRecover (Statement.digest pp) (u32 leaf) (Statement.signature sig).chainElements x

/-- The stream's first bytes: the leaf tweak and the public parameter. -/
abbrev head (pp : Std.Array U64 2#usize) (leaf : Std.U32) : List UInt8 :=
  ofWords [tweakWord0 (tyByte .leaf) 0#u32, tweakWord1 leaf] ++ ofWords pp.val

/-- After `k` ends, the closure's state holds a chain template and the stream the first `k` ends. -/
def Good (pp : Std.Array U64 2#usize) (leaf : Std.U32) (sig : leanxmss.Signature) (d : leanxmss.Digits)
    (x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V) (k : Nat) (c : leanxmss.verify.closure)
    (s : List UInt8) : Prop :=
  ∃ p v, c = ((⟨tmpl pp leaf p v⟩ : leanxmss.Chains), d, sig) ∧ v.length = 16 ∧
    s = head pp leaf ++ ((ends pp leaf sig x).toList.take k).flatMap Vector.toList

/-- The closure's call for the next chain keeps the invariant, the stream getting that chain's end. -/
theorem good_step (pp : Std.Array U64 2#usize) (leaf : Std.U32) (sig : leanxmss.Signature) (d : leanxmss.Digits)
    (x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V)
    (hd : ∀ i : Std.Usize, (hi : i.val < Constants.V) → ∃ v, leanxmss.Digits.get d i = ok v ∧ v.val = (x[i.val]'hi).val)
    (k : Nat) (c : leanxmss.verify.closure) (s : List UInt8) (hg : Good pp leaf sig d x k c s) (hk : k < 42) :
    ∃ a c' back, (∀ k' : Std.Usize, k'.val = k →
        leanxmss.verify.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU642.call_mut c k' = ok (a, c', back)) ∧
      Good pp leaf sig d x (k + 1) (back c') (s ++ ofWords a.val) := by
  obtain ⟨p, v, rfl, hv, rfl⟩ := hg
  obtain ⟨k', rfl⟩ : ∃ k' : Std.Usize, k'.val = k := ⟨⟨BitVec.ofNat _ k⟩, by
    show (BitVec.ofNat _ k).toNat = k
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h] <;> omega⟩
  obtain ⟨a, p', v', back, hc, hb, hv', ha⟩ := callMut_ok pp leaf sig d x hd k' hk p v hv
  refine ⟨a, _, back, fun k'' hk'' => ?_, p', v', hb, hv', ?_⟩
  · rw [show k'' = k' from UScalar.eq_of_val_eq hk'', hc]; rfl
  · rw [← digest_toList, ha, List.take_add_one, List.getElem?_eq_getElem (by simp; exact hk)]
    simp; rfl

/-- `wots_leaf`'s closure writes the leaf tweak, the public parameter and the 42 ends, in order. -/
theorem closure_ok (pp : Std.Array U64 2#usize) (leaf : Std.U32) (sig : leanxmss.Signature) (d : leanxmss.Digits)
    (x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V)
    (hd : ∀ i : Std.Usize, (hi : i.val < Constants.V) → ∃ v, leanxmss.Digits.get d i = ok v ∧ v.val = (x[i.val]'hi).val)
    (c : leanxmss.verify.closure) (hg : Good pp leaf sig d x 0 c (head pp leaf)) :
    ∃ c' s, leanxmss.wots_leaf.closure.Insts.CoreOpsFunctionFnOnceTupleMut3StreamTuple.call_once
        leanxmss.verify.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU642 (leaf, pp, c) [] =
          ok ((leaf, pp, c'), s) ∧
      Good pp leaf sig d x 42 c' s := by
  suffices h : spec (leanxmss.wots_leaf.closure.Insts.CoreOpsFunctionFnOnceTupleMut3StreamTuple.call_once
      leanxmss.verify.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU642 (leaf, pp, c) [])
      (fun r => ∃ c', r.1 = (leaf, pp, c') ∧ Good pp leaf sig d x 42 c' r.2) by
    obtain ⟨⟨r1, r2⟩, hr, c', h1, h2⟩ := exists_ok_of_spec h
    simp only at h1 h2
    exact ⟨c', r2, by rw [hr, h1]; rfl, h2⟩
  obtain ⟨p, v, rfl, hv, hs⟩ := hg
  set_option maxRecDepth 100000 in
  simp (maxSteps := 10000000) only [tweakWotsPk_eq, tweak_ok,
    leanxmss.wots_leaf.closure.Insts.CoreOpsFunctionFnOnceTupleMut3StreamTuple.call_once, leanvm_guest.Stream.write,
    bind_ok, uncurry_apply_pair, List.nil_append]
  have hg : Good pp leaf sig d x 0 ((⟨tmpl pp leaf p v⟩ : leanxmss.Chains), d, sig) (head pp leaf) :=
    ⟨p, v, rfl, hv, hs⟩
  clear hs hv
  iterate 42
    obtain ⟨a, c1, back, hcall, hg⟩ := good_step pp leaf sig d x hd _ _ _ hg (by omega)
    rw [hcall]
    on_goal 2 => simp
    set_option maxRecDepth 100000 in
    simp (maxSteps := 10000000) only [bind_ok, uncurry_apply_pair]
    simp only [Nat.reduceAdd] at hg
    clear hcall
  rw [spec_ok]
  refine ⟨_, rfl, ?_⟩
  convert hg using 1
  simp [head]

/-- The specification's concatenation of digests is the concatenation of their bytes. -/
theorem foldl_packBytes (L : List Digest) (acc : ByteArray) :
    L.foldl (fun acc d => acc ++ packBytes d) acc = acc ++ toBA (L.flatMap Vector.toList) := by
  induction L generalizing acc with
  | nil => apply ByteArray.ext; simp
  | cons d L ih => rw [List.foldl_cons, ih, List.flatMap_cons, toBA_append, packBytes_eq, ByteArray.append_assoc]

end leanxmss.Proofs.Leaf

namespace leanxmss.Proofs

open Bytes Leaf

/-- `verify`'s leaf, from the chains `Chains::new` makes and digits that are the specification's `x`, is the
specification's leaf of the public values `otsRecover` walks to from the signature's chain tips. -/
theorem wots_leaf_spec (pp : Std.Array U64 2#usize) (leaf : Std.U32) (sig : leanxmss.Signature)
    (d : leanxmss.Digits) (x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V)
    (hd : ∀ i : Std.Usize, (hi : i.val < Constants.V) → ∃ v, leanxmss.Digits.get d i = ok v ∧ v.val = (x[i.val]'hi).val) :
    ∃ chains, leanxmss.Chains.new pp leaf = ok chains ∧
      ∃ l, leanxmss.wots_leaf leanxmss.verify.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU642 pp leaf
          (chains, d, sig) = ok l ∧
        Statement.digest l = otsLeaf (Statement.digest pp) (u32 leaf)
          (otsRecover (Statement.digest pp) (u32 leaf) (Statement.signature sig).chainElements x) := by
  refine ⟨_, new_ok pp leaf, ?_⟩
  obtain ⟨c', s, hc, p, v, -, -, hs⟩ := closure_ok pp leaf sig d x hd _
    ⟨0, ofWords [0#u64, 0#u64], rfl, by simp, by simp⟩
  obtain ⟨l, hl, hlb⟩ := digest_blake2s s
  refine ⟨l, ?_, ?_⟩
  · simp only [leanxmss.wots_leaf, leanxmss.V, leanvm_guest.hash_with]
    simp [hc]
    exact (bind_ok _ _).trans hl
  · apply vector_eq_of_toList
    have hin : toBA s = tweakInput (Statement.digest pp) .leaf 0 (u32 leaf)
        ((ends pp leaf sig x).toList.foldl (fun acc d => acc ++ packBytes d) ByteArray.empty) := by
      rw [hs, foldl_packBytes, tweakInput, packBytes_eq, show (0 : UInt32) = u32 0#u32 from rfl, ← tweak_bytes,
        packBytes_publicParam, List.take_of_length_le (by simp [Constants.V])]
      apply ByteArray.ext
      simp [head]
    rw [digest_toList, hlb, otsLeaf, tweakHash_toList, hin]

end leanxmss.Proofs
