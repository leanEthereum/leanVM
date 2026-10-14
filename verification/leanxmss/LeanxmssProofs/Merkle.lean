import LeanxmssProofs.Hash

/-!
# The Merkle path

The guest's `merkle_root`, 32 unrolled `merkle_node`s on one template, is the specification's `computeRoot`.

Between nodes the template is the Merkle tweak's fixed bytes, the public parameter, and fields each node overwrites
(`Shape`). Each `merkle_node` writes its tweak's position and index and the two children, in the order bit `LEVEL` of
the leaf index picks, so the template becomes the specification's `tweakInput` (`nodeBytes`) and its digest the
specification's `climbStep` (`level_bind`). The 32 levels are then one repeated step.
-/

open Aeneas Aeneas.Std Result WP
open EthCryptographySpecs.Xmss EthCryptographySpecs.Xmss.Constants

namespace leanxmss.Proofs.Merkle

open Bytes

/-! ## The SDK models on this template -/

/-- A small `usize`'s value, whatever the platform's width. -/
theorem usize_val_small (i : Nat) (h : i < 2 ^ 32) : (⟨BitVec.ofNat _ i⟩ : Usize).val = i := by
  show (BitVec.ofNat _ i).toNat = i
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with h' | h' <;> simp [h'] <;> omega

/-- The same, with the width as `simp` leaves it. -/
theorem usize_val_small' (i : Nat) (h : i < 2 ^ 32) :
    (UScalar.mk (ty := .Usize) (BitVec.ofNat System.Platform.numBits i)).val = i :=
  usize_val_small i h

/-- A `usize` literal's value. -/
theorem usize_lit {n : Nat} {h} : (UScalar.ofNat (ty := .Usize) n h).val = n := by simp

/-- Mapping over a success. -/
@[local simp] theorem map_ok {α β : Type} (f : α → β) (x : α) : (f <$> (ok x : Result α)) = ok (f x) := by
  rw [← pure_tc_eq, map_pure, pure_tc_eq]

/-- A `mapM` whose every call succeeds. -/
theorem mapM_ok {α β : Type} (l : List α) (f : α → Result β) (g : α → β) (h : ∀ a ∈ l, f a = ok (g a)) :
    l.mapM f = ok (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.mapM_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]
    simp

theorem u8_ofNat_val (n : Nat) : UInt8.ofNat (UScalar.mk (ty := .U8) (BitVec.ofNat 8 n)).val = UInt8.ofNat n := by
  apply UInt8.toNat_inj.mp
  show (UInt8.ofNat (BitVec.ofNat 8 n).toNat).toNat = _
  simp [UInt8.toNat_ofNat']

theorem u8_setWidth (w : U64) :
    UInt8.ofNat (UScalar.mk (ty := .U8) (BitVec.setWidth 8 w.bv)).val = UInt8.ofNat w.val := by
  apply UInt8.toNat_inj.mp
  show (UInt8.ofNat (BitVec.setWidth 8 w.bv).toNat).toNat = _
  simp [UInt8.toNat_ofNat', UScalar.bv_toNat]

/-- A digest's two words. -/
theorem pair_val (a : Std.Array U64 2#usize) : ∃ w0 w1, a.val = [w0, w1] := by
  have h := a.property
  rcases hv : a.val with _ | ⟨w0, _ | ⟨w1, _ | _⟩⟩ <;> rw [hv] at h <;> simp at h
  exact ⟨w0, w1, rfl⟩

/-- `Template::write` of a `u32` at an aligned offset inside the block: its four little-endian bytes there. -/
theorem write_u32 (t : List UInt8) (pos : Usize) (v : Std.U32) (h1 : pos.val % 4 = 0) (h2 : pos.val ≤ 60) :
    leanvm_guest.Template.write (W1 := 8#usize) U32.Insts.Leanvm_guestPlainPlain t pos v =
      ok (splice t pos.val (le 4 v.val)) := by
  simp only [leanvm_guest.Template.write, U32.Insts.Leanvm_guestPlainPlain.SIZE,
    U32.Insts.Leanvm_guestPlainPlain.ALIGN, U32.Insts.Leanvm_guestPlainPlain.byte]
  simp [h1, h2, massert, List.range_succ]
  rw [usize_val_small' 0 (by omega), usize_val_small' 1 (by omega), usize_val_small' 2 (by omega),
    usize_val_small' 3 (by omega)]
  simp only [le, u8_ofNat_val]
  simp [Nat.div_div_eq_div_mul]

/-- The size of a digest, `[u64; 2]`. -/
theorem pair_size :
    Array.Insts.Leanvm_guestPlainPlain.SIZE 2#usize U64.Insts.Leanvm_guestPlainPlain = ok 16#usize := by
  simp only [Array.Insts.Leanvm_guestPlainPlain.SIZE, U64.Insts.Leanvm_guestPlainPlain.SIZE, bind_ok]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [usize_val_small _ (by simp)]
  rfl

/-- `Template::write` of a digest at an aligned offset inside the block: its words' bytes there. -/
theorem write_pair (t : List UInt8) (pos : Usize) (a : Std.Array U64 2#usize) (h1 : pos.val % 8 = 0)
    (h2 : pos.val ≤ 48) :
    leanvm_guest.Template.write (W1 := 8#usize)
      (Array.Insts.Leanvm_guestPlainPlain 2#usize U64.Insts.Leanvm_guestPlainPlain) t pos a =
      ok (splice t pos.val (ofWords a.val)) := by
  have e8 : (8#usize : Usize).val = 8 := by simp
  have e16 : (16#usize : Usize).val = 16 := by simp
  have hl : a.val.length = 2 := by simp
  have hg : ∀ i ∈ List.range 16, Array.Insts.Leanvm_guestPlainPlain.byte U64.Insts.Leanvm_guestPlainPlain a
      ⟨BitVec.ofNat _ i⟩ = ok (⟨BitVec.ofNat 8 (a.val[i / 8]!.val / 2 ^ (8 * (i % 8)))⟩ : Std.U8) := by
    intro i hi
    simp only [List.mem_range] at hi
    simp only [Array.Insts.Leanvm_guestPlainPlain.byte, U64.Insts.Leanvm_guestPlainPlain.SIZE, bind_ok,
      U64.Insts.Leanvm_guestPlainPlain.byte]
    rw [usize_val_small i (by omega), e8, List.getElem?_eq_getElem (by omega)]
    simp only
    rw [usize_val_small _ (by omega), getElem!_pos a.val (i / 8) (by omega)]
  simp only [leanvm_guest.Template.write]
  simp only [pair_size, Array.Insts.Leanvm_guestPlainPlain.ALIGN, U64.Insts.Leanvm_guestPlainPlain.ALIGN, bind_ok,
    e8, e16]
  rw [mapM_ok _ _ _ hg]
  obtain ⟨w0, w1, hw⟩ := pair_val a
  rw [hw]
  simp [massert, h1, h2, List.range_succ, ofWords, le, Nat.div_div_eq_div_mul, u8_ofNat_val, u8_setWidth]

/-- `Template::new` of eight words: their bytes. -/
theorem template_new (ws : Std.Array U64 8#usize) : leanvm_guest.Template.new ws = ok (ofWords ws.val) := by
  simp [leanvm_guest.Template.new, massert]

@[local step] theorem write_u32_spec (t : List UInt8) (pos : Usize) (v : Std.U32) (h1 : pos.val % 4 = 0)
    (h2 : pos.val ≤ 60) :
    leanvm_guest.Template.write (W1 := 8#usize) U32.Insts.Leanvm_guestPlainPlain t pos v
      ⦃ r => r = splice t pos.val (le 4 v.val) ⦄ := by
  rw [write_u32 t pos v h1 h2]; simp

@[local step] theorem write_pair_spec (t : List UInt8) (pos : Usize) (a : Std.Array U64 2#usize)
    (h1 : pos.val % 8 = 0) (h2 : pos.val ≤ 48) :
    leanvm_guest.Template.write (W1 := 8#usize)
      (Array.Insts.Leanvm_guestPlainPlain 2#usize U64.Insts.Leanvm_guestPlainPlain) t pos a
      ⦃ r => r = splice t pos.val (ofWords a.val) ⦄ := by
  rw [write_pair t pos a h1 h2]; simp

@[local step] theorem template_digest_spec (t : List UInt8) :
    leanvm_guest.Template.digest (W1 := 8#usize) t ⦃ p => p = (blake2s t, t) ⦄ := by
  simp [leanvm_guest.Template.digest]

/-! ## One node -/

/-- Bit 4 of `(b << 4) >> L` is bit `L` of `b`, and the only bit `& 16` keeps. -/
theorem side_nat (b L : Nat) : ((b <<< 4) >>> L) &&& 16 = 16 * ((b >>> L) % 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show 16 * ((b >>> L) % 2) = ((b >>> L) % 2 ^ 1) <<< 4 by rw [Nat.shiftLeft_eq]; omega,
    show (16 : Nat) = 2 ^ 4 from rfl]
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow]
  by_cases h : i = 4
  · subst h; simp
  · have : ¬ (i ≥ 4 ∧ i - 4 < 1) := by omega
    simp only [Bool.and_assoc]
    cases hi : decide (i ≥ 4) <;> cases hj : decide (i - 4 < 1) <;> simp_all

/-- `merkle_node`'s `side`: 16 bytes when bit `LEVEL` of the leaf index is set, else 0. -/
theorem side_val (bits : U64) (hb : bits.val < 2 ^ 32) (L : Usize) (i i1 : U64)
    (hi : i.val = bits.val <<< 4 % U64.size) (hi1 : i1.val = i.val >>> L.val) :
    (UScalar.cast .Usize (i1 &&& 16#u64)).val = 16 * ((bits.val >>> L.val) % 2) := by
  have hm := Nat.mod_two_eq_zero_or_one (bits.val >>> L.val)
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
  · rw [UScalar.val_and, hi1, hi, Nat.mod_eq_of_lt]
    · exact side_nat _ _
    · simp [U64.size, U64.numBits, Nat.shiftLeft_eq]; omega
  · rw [UScalar.val_and]
    have := Nat.and_le_right (n := i1.val) (m := (16#u64 : U64).val)
    have h16 : (16#u64 : U64).val = 16 := by simp
    rw [h16] at this ⊢
    have h32 : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
      rcases System.Platform.numBits_eq with h' | h' <;> simp [h']
    omega

/-- The first four bytes of every Merkle tweak. -/
def head : List UInt8 := [EthCryptographySpecs.Xmss.PROTOCOL_DOMAIN_SEP, TweakType.merkle.toByte, 0, 0]

/-- The template's bytes once `merkle_node` at level `L` has written its fields: the specification's input to the
parent's hash. -/
def nodeBytes (pp : Std.Array U64 2#usize) (L bits : Nat) (child sib : Std.Array U64 2#usize) : List UInt8 :=
  (makeTweak .merkle (UInt32.ofNat (L + 1)) (UInt32.ofNat (bits >>> (L + 1)))).toList ++ ofWords pp.val ++
    (if (bits >>> L) % 2 = 0 then ofWords child.val ++ ofWords sib.val else ofWords sib.val ++ ofWords child.val)

/-- `merkle_node` on a template of the right shape writes `nodeBytes` and returns the first half of its digest. -/
theorem node_spec (L : Usize) (hL : L.val < 32) (pp : Std.Array U64 2#usize) (x y z : List UInt8)
    (hx : x.length = 4) (hy : y.length = 4) (hz : z.length = 32) (bits : U64) (hb : bits.val < 2 ^ 32)
    (child sib : Std.Array U64 2#usize) :
    leanxmss.merkle_node L (head ++ x ++ [0, 0, 0, 0] ++ y ++ ofWords pp.val ++ z) bits child sib ⦃ p =>
      p.2 = nodeBytes pp L.val bits.val child sib ∧
        ofWords p.1.val = (Blake2s.hash (toBA (nodeBytes pp L.val bits.val child sib))).toList.take 16 ⦄ := by
  unfold leanxmss.merkle_node
  simp only [lift, leanxmss.TWEAK_POSITION, leanxmss.TWEAK_INDEX, leanxmss.PAYLOAD]
  step*
  all_goals rw [side_val bits hb L i i1 i_post i1_post] at *
  all_goals have hm := Nat.mod_two_eq_zero_or_one (bits.val >>> L.val)
  all_goals try omega
  · scalar_tac
  have hsh : bits.val >>> (L.val + 1) ≤ bits.val := Nat.shiftRight_le _ _
  have e1 : (UScalar.cast .U32 i3).val = L.val + 1 := by
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
    · exact i3_post
    · simp; omega
  have e2 : (UScalar.cast .U32 i5).val = bits.val >>> (L.val + 1) := by
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
    · rw [i5_post, i3_post]
    · rw [i5_post, i3_post]; show _ < 2 ^ 32; omega
  have m1 : (L.val + 1) % 4294967296 = L.val + 1 := Nat.mod_eq_of_lt (by omega)
  have m2 : (bits.val >>> (L.val + 1)) % 4294967296 = bits.val >>> (L.val + 1) := Nat.mod_eq_of_lt (by omega)
  obtain ⟨d, hd, hdb⟩ := digest_blake2s node4
  rw [a_post, hd]
  simp only [bind_ok, spec_ok, node5_post]
  suffices hn : node4 = nodeBytes pp L.val bits.val child sib by rw [← hn]; exact ⟨rfl, hdb⟩
  rw [node4_post, node3_post, node2_post, node1_post, e1, e2]
  rcases hm with h | h
  · rw [show i8.val = 32 by omega, show i10.val = 48 by omega]
    simp [nodeBytes, h, makeTweak_toList, wordBytes_toList, splice, head, hx, hy, hz, m1, m2, List.take_append,
      List.drop_append, List.take_of_length_le, List.drop_of_length_le]
  · rw [show i8.val = 48 by omega, show i10.val = 32 by omega]
    simp [nodeBytes, h, makeTweak_toList, wordBytes_toList, splice, head, hx, hy, hz, m1, m2, List.take_append,
      List.drop_append, List.take_of_length_le, List.drop_of_length_le]

/-- The template's shape between nodes: the Merkle tweak's fixed bytes, the public parameter, and the fields each
node overwrites. -/
def Shape (pp : Std.Array U64 2#usize) (t : List UInt8) : Prop :=
  ∃ x y z, x.length = 4 ∧ y.length = 4 ∧ z.length = 32 ∧ t = head ++ x ++ [0, 0, 0, 0] ++ y ++ ofWords pp.val ++ z

/-- A node leaves the template in shape for the next. -/
theorem nodeBytes_shape (pp : Std.Array U64 2#usize) (L bits : Nat) (child sib : Std.Array U64 2#usize) :
    Shape pp (nodeBytes pp L bits child sib) := by
  refine ⟨(Blake2s.Internal.wordBytes (UInt32.ofNat (L + 1))).toList,
    (Blake2s.Internal.wordBytes (UInt32.ofNat (bits >>> (L + 1)))).toList,
    if (bits >>> L) % 2 = 0 then ofWords child.val ++ ofWords sib.val else ofWords sib.val ++ ofWords child.val,
    Vector.length_toList, Vector.length_toList, by split <;> simp, ?_⟩
  rw [nodeBytes, makeTweak_toList]
  rfl

/-- The first half of the digest of `nodeBytes` is the specification's `climbStep`. -/
theorem node_digest (pp child sib r : Std.Array U64 2#usize) (L bits : Nat)
    (hr : ofWords r.val = (Blake2s.hash (toBA (nodeBytes pp L bits child sib))).toList.take 16) :
    Statement.digest r = Internal.climbStep (Statement.digest pp) bits L (Statement.digest child)
      (Statement.digest sib) := by
  apply vector_eq_of_toList
  rw [digest_toList, hr]
  unfold Internal.climbStep merkleNode
  by_cases h : (bits >>> L) % 2 = 0
  · have hin : toBA (nodeBytes pp L bits child sib) = tweakInput (Statement.digest pp) .merkle
        (UInt32.ofNat (L + 1)) (UInt32.ofNat (bits >>> (L + 1)))
        (packBytes (Statement.digest child) ++ packBytes (Statement.digest sib)) := by
      rw [tweakInput, packBytes_publicParam, packBytes_eq (makeTweak _ _ _), packBytes_digest, packBytes_digest,
        nodeBytes, if_pos h, toBA_append, toBA_append, toBA_append]
    rw [if_pos (by simpa using h), tweakHash_toList, hin]
  · have hin : toBA (nodeBytes pp L bits child sib) = tweakInput (Statement.digest pp) .merkle
        (UInt32.ofNat (L + 1)) (UInt32.ofNat (bits >>> (L + 1)))
        (packBytes (Statement.digest sib) ++ packBytes (Statement.digest child)) := by
      rw [tweakInput, packBytes_publicParam, packBytes_eq (makeTweak _ _ _), packBytes_digest, packBytes_digest,
        nodeBytes, if_neg h, toBA_append, toBA_append, toBA_append]
    rw [if_neg (by simpa using h), tweakHash_toList, hin]

/-! ## The path -/

/-- The specification's authentication path of the guest's. -/
abbrev specPath (path : Std.Array (Std.Array U64 2#usize) 32#usize) : Vector Digest LOG_LIFETIME :=
  Vector.ofFn fun i => Statement.digest (path.val.getD i.val default)

/-- Indexing the path in bounds. -/
theorem index_path (path : Std.Array (Std.Array U64 2#usize) 32#usize) (L : Usize) (hL : L.val < 32) :
    Std.Array.index_usize path L = ok (path.val.getD L.val default) := by
  obtain ⟨a, ha, rfl⟩ := exists_ok_of_spec (Std.Array.index_usize_spec path L (by simpa using hL))
  rw [ha, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
  rfl

/-- One level of `merkle_root`: from a template in shape and the node the specification reaches after `k` levels,
indexing the path and `merkle_node` at level `k` give a template in shape and the node it reaches after `k + 1`;
the rest of the computation `f` then continues from those. -/
theorem level_bind {β : Type} (pp : Std.Array U64 2#usize) (bits : U64) (hb : bits.val < 2 ^ 32)
    (path : Std.Array (Std.Array U64 2#usize) 32#usize) (k : Nat) (L : Usize) (hL' : L.val = k) (hk : k < 32)
    (t : List UInt8) (ht : Shape pp t) (c : Std.Array U64 2#usize) (lf : Digest)
    (hc : Statement.digest c =
      Internal.climbUpto (Statement.digest pp) bits.val (specPath path) k (Nat.le_of_lt hk) lf)
    (f : Std.Array U64 2#usize × leanvm_guest.Template 8#usize → Result β) (Q : β → Prop)
    (hf : ∀ c' t', Shape pp t' → Statement.digest c' =
      Internal.climbUpto (Statement.digest pp) bits.val (specPath path) (k + 1) hk lf →
      ∃ r, f (c', t') = ok r ∧ Q r) :
    ∃ r, (Std.Array.index_usize path L >>= fun a => leanxmss.merkle_node L t bits c a >>= f) = ok r ∧ Q r := by
  subst hL'
  have hL := hk
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := ht
  obtain ⟨⟨c', t'⟩, hp, h1, h2⟩ := exists_ok_of_spec (node_spec L hL pp x y z hx hy hz bits hb c
    (path.val.getD L.val default))
  rw [index_path path L hL, bind_tc_ok, hp, bind_tc_ok]
  simp only at h1 h2
  apply hf
  · rw [h1]; exact nodeBytes_shape _ _ _ _ _
  · rw [node_digest pp c _ c' L.val bits.val h2, Internal.climbUpto, ← hc]
    simp

end leanxmss.Proofs.Merkle

namespace leanxmss.Proofs

open Bytes Merkle

/-- `merkle_root` folds a leaf up its path as the specification's `computeRoot` does, the leaf index's bits choosing
each node's side. -/
theorem merkle_root_spec (pp : Std.Array U64 2#usize) (leaf : Std.U32) (l : Std.Array U64 2#usize)
    (path : Std.Array (Std.Array U64 2#usize) 32#usize) :
    ∃ r, leanxmss.merkle_root pp leaf l path = ok r ∧
      Statement.digest r = computeRoot (Statement.digest pp) (u32 leaf)
        (Vector.ofFn fun i => Statement.digest (path.val.getD i.val default)) (Statement.digest l) := by
  obtain ⟨p0, p1, hpp⟩ := pair_val pp
  have hty : leanxmss.TWEAK_MERKLE = tyByte .merkle := by
    apply UScalar.eq_of_val_eq; simp [leanxmss.TWEAK_MERKLE]; rfl
  have hp0 : Std.Array.index_usize pp 0#usize = ok p0 := by simp [Std.Array.index_usize, hpp]
  have hp1 : Std.Array.index_usize pp 1#usize = ok p1 := by simp [Std.Array.index_usize, hpp]
  have ht0 : Std.Array.index_usize (Std.Array.make 2#usize [tweakWord0 (tyByte .merkle) 0#u32, tweakWord1 0#u32])
      0#usize = ok (tweakWord0 (tyByte .merkle) 0#u32) := by simp [Std.Array.index_usize]
  have ht1 : Std.Array.index_usize (Std.Array.make 2#usize [tweakWord0 (tyByte .merkle) 0#u32, tweakWord1 0#u32])
      1#usize = ok (tweakWord1 0#u32) := by simp [Std.Array.index_usize]
  have hbits : (core.convert.num.FromU64U32.from leaf).val = leaf.val :=
    core.convert.num.FromU64U32.from_val_eq leaf
  have hb : (core.convert.num.FromU64U32.from leaf).val < 2 ^ 32 := by
    rw [hbits]; have := leaf.hBounds; simpa using this
  unfold leanxmss.merkle_root
  rw [hty, tweak_ok]
  simp only [bind_ok, lift, ht0, ht1, hp0, hp1, template_new]
  -- The fresh template: the tweak at position and index 0, the public parameter, zeros.
  have hs : Shape pp (ofWords (Std.Array.make 8#usize
      [tweakWord0 (tyByte .merkle) 0#u32, tweakWord1 0#u32, p0, p1, 0#u64, 0#u64, 0#u64, 0#u64]).val) := by
    refine ⟨(Blake2s.Internal.wordBytes (u32 0#u32)).toList, (Blake2s.Internal.wordBytes (u32 0#u32)).toList,
      ofWords [0#u64, 0#u64, 0#u64, 0#u64], Vector.length_toList, Vector.length_toList, by simp, ?_⟩
    have e := tweak_bytes .merkle 0#u32 0#u32
    rw [makeTweak_toList] at e
    rw [Std.Array.make_val, hpp, show [tweakWord0 (tyByte .merkle) 0#u32, tweakWord1 0#u32, p0, p1, 0#u64, 0#u64,
      0#u64, 0#u64] = [tweakWord0 (tyByte .merkle) 0#u32, tweakWord1 0#u32] ++ [p0, p1] ++ [0#u64, 0#u64, 0#u64, 0#u64]
      from rfl, ofWords_append, ofWords_append, e]
    rfl
  have hroot : computeRoot (Statement.digest pp) (u32 leaf)
      (Vector.ofFn fun i => Statement.digest (path.val.getD i.val default)) (Statement.digest l) =
      Internal.climbUpto (Statement.digest pp) (core.convert.num.FromU64U32.from leaf).val
        (specPath path) 32 (Nat.le_refl _) (Statement.digest l) := by
    rw [computeRoot, u32_toNat, hbits]
    rfl
  have hl : Statement.digest l = Internal.climbUpto (Statement.digest pp) (core.convert.num.FromU64U32.from leaf).val
      (specPath path) 0 (Nat.zero_le _) (Statement.digest l) := rfl
  rw [hroot]
  generalize core.convert.num.FromU64U32.from leaf = bits at hb hl ⊢
  -- The 32 levels, each from the template and node the previous one left.
  iterate 32
    refine level_bind _ _ hb _ _ _ usize_lit (by decide) _ ‹_› _ _ ‹_› _ _ ?_
    intro c t hs hc
  exact ⟨c, rfl, hc⟩

end leanxmss.Proofs
