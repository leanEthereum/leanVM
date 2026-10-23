/-
  LeanVM.Guest.B1.Sig.SphincsScheme

  leanSPHINCS verification with BLAKE2s (`Node.sphincsVerify`) as pure functions of the guest's
  cells.
-/

module

public import LeanVM.Guest.B1.Sig.XmssScheme

/-!
# leanSPHINCS over cells

As for leanXMSS (`XmssScheme`): the lemmas hold for any oracle instance on `Id` with `SQ`, that it
is BLAKE2s, so that the kernel never unfolds the hash, and each routine is a pure function of
cells. `sVerify_iff` splits verification into the message digest, the forest key it selects, the
one-time leaf and the tree; the forest's pieces (`forestWalk`, `childRecover`, `subFold`,
`topFold`, `superHash`, `forestRecover`) follow, each over the cells the guest hashes.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value Sphincs Sphincs.Concrete

@[expose] public section

/-- The oracle is BLAKE2s. -/
def SQ (inst : HasQuery Sphincs.HashSpec Id) : Prop :=
  ∀ x, (inst.query (spec := Sphincs.HashSpec) x : Id HashOutput) = Node.blake2sBits x

theorem sq_blake2s : SQ ⟨Node.blake2sBits⟩ := fun _ => rfl

variable {inst : HasQuery Sphincs.HashSpec Id}

/-- A cell as a leanSPHINCS digest. -/
def sv (x : E) : Sphincs.Digest := cellVal x

/-- A cell as a leanSPHINCS public parameter. -/
def spp (x : E) : Sphincs.PublicParameter := cellVal x

theorem bytesLE_sv (x : E) : Sphincs.bytesLE 16 (sv x) = cellBytes x := sphincs_bytesLE_cellVal x

theorem bytesLE_spp (x : E) : Sphincs.bytesLE 16 (spp x) = cellBytes x := sphincs_bytesLE_cellVal x

theorem sflatMap_bytesLE_sv : ∀ (l : List E), List.flatMap (Sphincs.bytesLE 16) (l.map sv) = l.flatMap cellBytes
  | [] => rfl
  | x :: l => by
      show Sphincs.bytesLE 16 (sv x) ++ List.flatMap (Sphincs.bytesLE 16) (l.map sv) = cellBytes x ++ l.flatMap cellBytes
      rw [bytesLE_sv, sflatMap_bytesLE_sv l]

/-- **A hash of cells**: a tweakable hash whose input is the bytes of cells is the value of the
first cell of their `hcell`. -/
theorem sHash_cells (hq : SQ inst) {P : PublicParameter} {dom : HashDomain}
    {payload : HashInput} {cs : List E} (h : tweakableHashInput P dom payload = cs.flatMap cellBytes) :
    @tweakableHash Id _ inst P dom payload = sv (hcell cs).1 := by
  rw [tweakableHash.eq_def]
  simp only [bind, pure, oracleHash]
  rw [hq, h, sphincs_truncateHash_blake2sBits]
  rfl

/-- A hash of bytes `r`, as a digest. -/
theorem sHash_bytes (hq : SQ inst) {P : PublicParameter} {dom : HashDomain}
    {payload : HashInput} {r : List UInt8} (h : tweakableHashInput P dom payload = r) :
    @tweakableHash Id _ inst P dom payload = sv (hb r).1 := by
  rw [tweakableHash.eq_def]
  simp only [bind, pure, oracleHash]
  rw [hq, h, sphincs_truncateHash_blake2sBits]
  rfl

theorem sSequenceFin_id {α : Type} : ∀ {n : Nat} (f : Fin n → Id α), Sphincs.Concrete.sequenceFin f = f
  | 0, f => funext fun i => i.elim0
  | n + 1, f => by
      simp only [Sphincs.Concrete.sequenceFin]
      have := sSequenceFin_id (fun i : Fin n => f i.succ)
      rw [this]
      funext i
      refine Fin.cases rfl (fun j => rfl) i

/-! ## Addresses -/

theorem sTweak (tag step hi lo : Nat) :
    Sphincs.fieldBytes (Sphincs.tweakFields tag step hi lo) = cellBytes (eOfNat (addrNat tag step hi lo)) :=
  sphincs_fieldBytes_tweakFields tag step hi lo

/-! ## Verification -/

theorem verifyLayers_one (P : PublicParameter) (index : Index) (σ : Signature) (msg : Sphincs.Digest) :
    @verifyLayers Id _ inst P index σ 1 msg =
      (@otsLeaf Id _ inst P topLayer 0 (leafIndexAt index topLayer) msg (σ.layers topLayer).counter
        (σ.layers topLayer).chainValues).map fun v =>
          @treeFold Id _ inst P topLayer 0 (leafIndexAt index topLayer) (signaturePath σ topLayer)
            (layerHeight topLayer) v := by
  rw [verifyLayers.eq_2]
  simp only [bind, pure, show (0 : Nat) < numLayers from Nat.one_pos, ↓reduceDIte]
  have e : (⟨0, Nat.one_pos⟩ : Layer) = topLayer := rfl
  simp only [e, treeIndexAt]
  split
  next v h =>
    have h' : @otsLeaf Id _ inst P topLayer 0 (leafIndexAt index topLayer) msg (σ.layers topLayer).counter
        (σ.layers topLayer).chainValues = some v := h
    rw [h', verifyLayers.eq_1]
    rfl
  next h =>
    cases h' : @otsLeaf Id _ inst P topLayer 0 (leafIndexAt index topLayer) msg (σ.layers topLayer).counter
        (σ.layers topLayer).chainValues with
    | none => rfl
    | some v => exact absurd h' (h v)

/-- **Verification**: the digest selects the forest key, which the one-time signature signs
under a leaf whose path reaches the key's root. -/
theorem sVerify_iff (pk : PublicKey) (msg : Message) (σ : Signature) :
    @Sphincs.Concrete.verify Id _ inst pk msg σ = true ↔
      ∃ leaf, @otsLeaf Id _ inst pk.parameter topLayer 0
          (leafIndexAt (digestIndex (@messageDigest Id _ inst pk.parameter pk.root msg σ.randomness)) topLayer)
          (@forestRecover Id _ inst pk.parameter
            (digestIndex (@messageDigest Id _ inst pk.parameter pk.root msg σ.randomness))
            (digestMarks (@messageDigest Id _ inst pk.parameter pk.root msg σ.randomness)) σ.forest)
          (σ.layers topLayer).counter (σ.layers topLayer).chainValues = some leaf ∧
        @treeFold Id _ inst pk.parameter topLayer 0
          (leafIndexAt (digestIndex (@messageDigest Id _ inst pk.parameter pk.root msg σ.randomness)) topLayer)
          (signaturePath σ topLayer) (layerHeight topLayer) leaf = pk.root := by
  rw [Sphincs.Concrete.verify.eq_def]
  simp only [bind, pure, show numLayers = 1 from rfl, verifyLayers_one]
  split
  next r h =>
    rw [decide_eq_true_iff]
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    constructor
    · intro hr; exact ⟨v, hv, hr⟩
    · rintro ⟨v', hv', hr⟩
      rw [hv] at hv'
      cases hv'
      exact hr
  next h =>
    refine ⟨fun h => absurd h Bool.false_ne_true, ?_⟩
    rintro ⟨v, hv, -⟩
    rw [hv] at h
    exact absurd h (by simp)

theorem sphincsVerify_iff (pk : PublicKey) (msg : Message) (σ : Signature) :
    Node.sphincsVerify pk msg σ = true ↔
      ∃ leaf, @otsLeaf Id _ ⟨Node.blake2sBits⟩ pk.parameter topLayer 0
          (leafIndexAt (digestIndex (@messageDigest Id _ ⟨Node.blake2sBits⟩ pk.parameter pk.root msg
            σ.randomness)) topLayer)
          (@forestRecover Id _ ⟨Node.blake2sBits⟩ pk.parameter
            (digestIndex (@messageDigest Id _ ⟨Node.blake2sBits⟩ pk.parameter pk.root msg σ.randomness))
            (digestMarks (@messageDigest Id _ ⟨Node.blake2sBits⟩ pk.parameter pk.root msg σ.randomness))
            σ.forest)
          (σ.layers topLayer).counter (σ.layers topLayer).chainValues = some leaf ∧
        @treeFold Id _ ⟨Node.blake2sBits⟩ pk.parameter topLayer 0
          (leafIndexAt (digestIndex (@messageDigest Id _ ⟨Node.blake2sBits⟩ pk.parameter pk.root msg
            σ.randomness)) topLayer)
          (signaturePath σ topLayer) (layerHeight topLayer) leaf = pk.root := by
  rw [Node.sphincsVerify.eq_def, idRun]
  exact sVerify_iff pk msg σ

theorem leafIndexAt_top (index : Index) : (leafIndexAt index topLayer).val = index.val := by
  have h : index.val < 67108864 := index.isLt
  simp [leafIndexAt, heightBelow, heightAbove, layerHeight, maxLayerHeight, totalHeight, h]

/-! ## The one-time signature -/

theorem sOtsLeaf_id (P : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (msg : Sphincs.Digest) (ctr : Counter) (vals : ChainIndex → Sphincs.Digest) :
    @otsLeaf Id _ inst P lay tree leaf msg ctr vals =
      (TargetSum.decodeDigest (@tweakableHash Id _ inst P (.encoding lay tree leaf)
        (Sphincs.bytesLE 16 msg ++ Sphincs.bytesLE 4 ctr))).map fun enc =>
        @leafHash Id _ inst P lay tree leaf fun i =>
          @recoverChain Id _ inst P lay tree leaf i (enc i) (vals i) := by
  rw [otsLeaf.eq_def]
  simp only [bind, pure, encode]
  split
  next enc h => rw [h, sSequenceFin_id]; rfl
  next h =>
    cases h' : TargetSum.decodeDigest (@tweakableHash Id _ inst P (.encoding lay tree leaf)
        (Sphincs.bytesLE 16 msg ++ Sphincs.bytesLE 4 ctr)) with
    | none => rfl
    | some enc => exact absurd h' (h enc)

theorem sChainWalk_succ (P : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (i : ChainIndex) (start n : Nat) (v : Sphincs.Digest) :
    @chainWalk Id _ inst P lay tree leaf i start (n + 1) v =
      if hstep : start + n < chainLength - 1 then
        @tweakableHash Id _ inst P (.chain lay tree leaf i ⟨start + n, hstep⟩)
          (Sphincs.bytesLE 16 (@chainWalk Id _ inst P lay tree leaf i start n v))
      else 0 := by
  rw [chainWalk.eq_2]
  simp only [bind]
  split <;> rfl

theorem sChainWalk_shift (P : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (i : ChainIndex) :
    ∀ (n start : Nat) (v : Sphincs.Digest) (hs : start < chainLength - 1), start + n + 1 ≤ chainLength - 1 →
      @chainWalk Id _ inst P lay tree leaf i start (n + 1) v =
        @chainWalk Id _ inst P lay tree leaf i (start + 1) n
          (@tweakableHash Id _ inst P (.chain lay tree leaf i ⟨start, hs⟩) (Sphincs.bytesLE 16 v))
  | 0, start, v, hs, _ => by
      rw [sChainWalk_succ, dite_of (by omega), chainWalk.eq_1, chainWalk.eq_1]
      rfl
  | n + 1, start, v, hs, h => by
      have h1 : start + (n + 1) < chainLength - 1 := by omega
      have h2 : start + 1 + n < chainLength - 1 := by omega
      rw [sChainWalk_succ, dite_of h1, sChainWalk_shift P lay tree leaf i n start v hs (by omega), sChainWalk_succ,
        dite_of h2]
      have : (⟨start + (n + 1), h1⟩ : ChainStep) = ⟨start + 1 + n, h2⟩ := Fin.ext (by simp only; omega)
      rw [this]

/-- **A one-time chain step over cells.** -/
theorem sChainStep_cells (hq : SQ inst) {pp a x : E} {lay : Layer} {tree : TreeIndex} {leaf : LeafIndex}
    {i : ChainIndex} {s : ChainStep} (ha : cellBytes a = tweakBytes (.chain lay tree leaf i s)) :
    @tweakableHash Id _ inst (spp pp) (.chain lay tree leaf i s) (Sphincs.bytesLE 16 (sv x)) =
      sv (hcell [pp, a, x]).1 := by
  apply sHash_cells hq
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ Sphincs.bytesLE 16 (sv x) = _
  rw [bytesLE_spp, bytesLE_sv, ← ha]
  simp

/-- **A one-time chain walked from digit `d` over cells**, its step addresses `idx + A(i, s)`. -/
theorem sRecoverChain_cells (hq : SQ inst) {pp idx : E} {lay : Layer} {tree : TreeIndex} {leaf : LeafIndex}
    {i : ChainIndex}
    (hadr : ∀ (s : ChainStep), cellBytes (idx + eOfNat (tw 1 + i.val * hiMul + s.val * stepMul)) =
      tweakBytes (.chain lay tree leaf i s)) :
    ∀ (d : Digit) (x : E), @recoverChain Id _ inst (spp pp) lay tree leaf i d (sv x) =
      sv (tipPair false pp (fun _ => 0) idx i.val d.val x).1 := by
  have hwalk : ∀ (n start : Nat) (x : E), start + n + 1 ≤ chainLength - 1 →
      @chainWalk Id _ inst (spp pp) lay tree leaf i start (n + 1) (sv x) =
        sv (chainFrom false pp (fun _ => 0) idx i.val n start x).1 := by
    intro n
    induction n with
    | zero =>
        intro start x h
        rw [sChainWalk_succ, dite_of (by omega), chainWalk.eq_1]
        exact sChainStep_cells hq (hadr ⟨start + 0, by omega⟩)
    | succ n ih =>
        intro start x h
        rw [sChainWalk_shift _ _ _ _ _ _ _ _ (by omega) h, sChainStep_cells hq (hadr ⟨start, by omega⟩),
          ih (start + 1) _ (by omega)]
        rfl
  intro d x
  have hd := d.isLt
  simp only [chainLength, winternitzBits] at hd
  by_cases h3 : d.val = 3
  · simp only [recoverChain, tipPair, h3, ↓reduceIte, chainLength, winternitzBits]
    rw [show 2 ^ 2 - 1 - 3 = 0 from rfl, chainWalk.eq_1]
    rfl
  · simp only [recoverChain, tipPair, h3, ↓reduceIte]
    rw [show chainLength - 1 - d.val = (2 - d.val) + 1 by simp [chainLength, winternitzBits]; omega]
    exact hwalk _ _ _ (by simp [chainLength, winternitzBits]; omega)

/-- **The one-time leaf over cells.** -/
theorem sLeafHash_cells (hq : SQ inst) {pp a : E} {lay : Layer} {tree : TreeIndex} {leaf : LeafIndex}
    (tips : Nat → E) (ha : cellBytes a = tweakBytes (.leaf lay tree leaf)) :
    @leafHash Id _ inst (spp pp) lay tree leaf (fun i => sv (tips i.val)) =
      sv (hcell (pp :: a :: (List.range numChains).map tips)).1 := by
  apply sHash_cells hq
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++
    (List.ofFn fun i : ChainIndex => sv (tips i.val)).flatMap (Sphincs.bytesLE 16) = _
  rw [bytesLE_spp, ← ha, show (List.ofFn fun i : ChainIndex => sv (tips i.val)) =
      ((List.range numChains).map tips).map sv
    from (ofFn_val_eq numChains (fun i => sv (tips i))).trans (List.map_map.symm)]
  exact (congrArg (fun t => cellBytes pp ++ cellBytes a ++ t) (sflatMap_bytesLE_sv _)).trans (by simp)

/-- **The tree over cells**: the fold of a path whose addresses' bytes are the nodes' tweaks, its
bits the leaf's. -/
theorem sTreeFold_cells (hq : SQ inst) {pp : E} {A : Nat → E} {lay : Layer} {tree : TreeIndex}
    {leaf : LeafIndex}
    (hA : ∀ l < maxLayerHeight, cellBytes (A l) = tweakBytes (.node lay tree (l + 1) (leaf.val / 2 ^ (l + 1))))
    (sibs : Nat → E) :
    ∀ m ≤ maxLayerHeight, ∀ x : E,
      @treeFold Id _ inst (spp pp) lay tree leaf (fun l => sv (sibs l)) m (sv x) =
        sv (mFold pp A (fun l => leaf.val.testBit l) sibs m 0 x)
  | 0, _, x => by rw [treeFold.eq_1]; rfl
  | m + 1, hm, x => by
      rw [treeFold.eq_2, mFold_succ]
      simp only [bind, Nat.zero_add]
      rw [sTreeFold_cells hq hA sibs m (by omega) x]
      split
      · next hb =>
        apply sHash_cells hq
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv (sibs m)) ++
          Sphincs.bytesLE 16 (sv _)) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA m (by omega)]
        simp
      · next hb =>
        apply sHash_cells hq
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv _) ++
          Sphincs.bytesLE 16 (sv (sibs m))) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA m (by omega)]
        simp

/-! ## The target-sum code -/

theorem sDigit_ofNat (N : Nat) (i : ChainIndex) :
    (TargetSum.digestEncoding (BitVec.ofNat 128 N) i).val = N % 2 ^ 128 / 4 ^ i.val % 4 := by
  show (BitVec.extractLsb' (2 * i.val) 2 (BitVec.ofNat 128 N)).toNat = _
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

/-- **A codeword's digits**: the digest holding the literal of `64` digits below 4 summing to
120 decodes to them. -/
theorem sDecode_lit {dig : Nat → Nat} (hd : ∀ j, dig j < 4)
    (hs : ∑ i ∈ Finset.range numChains, dig i = targetSum) :
    TargetSum.decodeDigest (sv (lit (∑ j ∈ Finset.range numChains, dig j * 4 ^ j))) =
      some fun i => ⟨dig i.val, hd _⟩ := by
  have hlt := base4_lt hd numChains
  have hlt' : ∑ j ∈ Finset.range numChains, dig j * 4 ^ j < 2 ^ 128 := by
    have : (4 : Nat) ^ numChains = 2 ^ 128 := by norm_num [numChains]
    omega
  have hsv : sv (lit (∑ j ∈ Finset.range numChains, dig j * 4 ^ j)) =
      BitVec.ofNat 128 (∑ j ∈ Finset.range numChains, dig j * 4 ^ j) := by
    show cellVal _ = _
    rw [cellVal, cellNat_lit, Nat.mod_eq_of_lt hlt']
  rw [hsv]
  have henc : TargetSum.digestEncoding (BitVec.ofNat 128 (∑ j ∈ Finset.range numChains, dig j * 4 ^ j)) =
      fun i => ⟨dig i.val, hd _⟩ := by
    funext i
    apply Fin.ext
    show (TargetSum.digestEncoding _ i).val = _
    rw [sDigit_ofNat, Nat.mod_eq_of_lt (a := ∑ j ∈ Finset.range numChains, dig j * 4 ^ j) hlt']
    exact base4_digit hd _ _ i.isLt
  have hv : TargetSum.Valid (fun i : ChainIndex => (⟨dig i.val, hd _⟩ : Digit)) := by
    rw [TargetSum.Valid, TargetSum.sum, ← hs, ← Fin.sum_univ_eq_sum_range]
  simp only [TargetSum.decodeDigest, henc, hv, ↓reduceIte]

/-! ## The message digest -/

theorem truncateMessageDigest_blake2sBits (I : List UInt8) :
    truncateMessageDigest (Node.blake2sBits I) =
      BitVec.ofNat messageDigestBits (cellNat (hb I).1 + 2 ^ 128 * cellNat (hb I).2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  show ((Node.blake2sBits I).toNat >>> 0) % 2 ^ messageDigestBits = _
  rw [Nat.shiftRight_zero, blake2sBits_toNat]
  rfl

/-- **The message digest over cells**: the two cells of the hash of `P | A | m | ρ`. -/
theorem sMessageDigest_cells (hq : SQ inst) {pp a m0 m1 rho : E} {root : Sphincs.Digest} {m : Message}
    (ha : cellBytes a = tweakBytes .message) (hm : Sphincs.bytesLE 32 m = cellBytes m0 ++ cellBytes m1) :
    @messageDigest Id _ inst (spp pp) root m (sv rho) =
      BitVec.ofNat messageDigestBits (cellNat (hcell [pp, a, m0, m1, rho]).1 +
        2 ^ 128 * cellNat (hcell [pp, a, m0, m1, rho]).2) := by
  have hI : tweakableHashInput (spp pp) .message (messageDigestPayload root m (sv rho)) =
      [pp, a, m0, m1, rho].flatMap cellBytes := by
    show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 32 m ++ Sphincs.bytesLE 16 (sv rho)) = _
    rw [bytesLE_spp, bytesLE_sv, ← ha, hm]
    simp
  rw [messageDigest.eq_def]
  simp only [bind, pure, messageDigestCall, oracleHash]
  rw [hq, truncateMessageDigest_blake2sBits, hI]
  rfl

theorem mod_div_mod {x n k w : Nat} (h : k + w ≤ n) : x % 2 ^ n / 2 ^ k % 2 ^ w = x / 2 ^ k % 2 ^ w := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self x, ← pow_add,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 h)]

theorem digest_div {c0 c1 k : Nat} (h0 : c0 < 2 ^ 128) :
    (c0 + 2 ^ 128 * c1) % 2 ^ messageDigestBits / 2 ^ (128 + k) = c1 % 2 ^ (234 - 128) / 2 ^ k := by
  have e1 : (c0 + 2 ^ 128 * c1) % 2 ^ 128 = c0 := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  have e2 : (c0 + 2 ^ 128 * c1) / 2 ^ 128 = c1 := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h0, Nat.zero_add]
  rw [show messageDigestBits = 128 + (234 - 128) from rfl, pow_add 2 128 (234 - 128), Nat.mod_mul, e1, e2,
    pow_add 2 128 k, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h0,
    Nat.zero_add]

/-- The index a digest of two cells selects: the low 26 bits of the second. -/
theorem digestIndex_ofNat {c0 c1 : Nat} (h0 : c0 < 2 ^ 128) :
    (digestIndex (BitVec.ofNat messageDigestBits (c0 + 2 ^ 128 * c1))).val = c1 % 2 ^ 26 := by
  show ((BitVec.ofNat messageDigestBits (c0 + 2 ^ 128 * c1)).extractLsb' 128 26).toNat = _
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show (128 : Nat) = 128 + 0 from rfl, digest_div h0, pow_zero, Nat.div_one,
    Nat.mod_mod_of_dvd _ (by norm_num)]

/-- A field of the second cell. -/
theorem digestField_ofNat {c0 c1 : Nat} (h0 : c0 < 2 ^ 128) {k w : Nat} (hk : k + w ≤ 106) :
    ((BitVec.ofNat messageDigestBits (c0 + 2 ^ 128 * c1)).extractLsb' (128 + k) w).toNat = c1 / 2 ^ k % 2 ^ w := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, digest_div h0,
    mod_div_mod (by omega)]

/-- A byte of the first cell. -/
theorem digestByte_ofNat {c0 c1 : Nat} {k : Nat} (hk : k + 8 ≤ 128) :
    ((BitVec.ofNat messageDigestBits (c0 + 2 ^ 128 * c1)).extractLsb' k 8).toNat = c0 / 2 ^ k % 2 ^ 8 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have e : c0 + 2 ^ 128 * c1 = c0 + 2 ^ k * (2 ^ 8 * (2 ^ (120 - k) * c1)) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← pow_add, ← pow_add, show k + 8 + (120 - k) = 128 by omega]
  have hm : (c0 + 2 ^ 128 * c1) % 2 ^ messageDigestBits / 2 ^ k % 2 ^ 8 = (c0 + 2 ^ 128 * c1) / 2 ^ k % 2 ^ 8 :=
    mod_div_mod (show k + 8 ≤ messageDigestBits by simp only [messageDigestBits, totalHeight, forestCoords, coordBits]; omega)
  rw [hm, e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

/-! ## The forest -/

/-- `n` steps of forest chain `i` from position `s` over cells, under the key's address `ka`
(`sp_forest_key`). -/
def fChain (pp ka : E) (i s : Nat) (v : E) : Nat → E
  | 0 => v
  | n + 1 => (hcell [pp, ka + eOfNat (tw 15 + i * 2 ^ 43 + (s + n) * stepMul), fChain pp ka i s v n]).1

/-- **A forest chain over cells.** -/
theorem sForestWalk_cells (hq : SQ inst) {pp ka : E} {index : Index} {c : Coord} {s : SuperIdx} {j : SubIdx}
    {a : ChildIdx} {i : FChain}
    (hadr : ∀ t : FStep, cellBytes (ka + eOfNat (tw 15 + i.val * 2 ^ 43 + t.val * stepMul)) =
      tweakBytes (.fchain index c s j a i t)) (start : Nat) (x : E) :
    ∀ n, start + n ≤ chainTop →
      @forestWalk Id _ inst (spp pp) index c s j a i start n (sv x) = sv (fChain pp ka i.val start x n)
  | 0, _ => by rw [forestWalk.eq_1]; rfl
  | n + 1, h => by
      rw [forestWalk.eq_2]
      simp only [bind]
      rw [sForestWalk_cells hq hadr start x n (by omega), dite_of (by omega)]
      apply sHash_cells hq
      show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ Sphincs.bytesLE 16 (sv _) = _
      rw [bytesLE_spp, bytesLE_sv, ← hadr ⟨start + n, by omega⟩]
      simp

/-- **A forest chain from its deficit.** -/
theorem sForestRecoverChain_cells (hq : SQ inst) {pp ka : E} {index : Index} {c : Coord} {s : SuperIdx}
    {j : SubIdx} {a : ChildIdx} {i : FChain}
    (hadr : ∀ t : FStep, cellBytes (ka + eOfNat (tw 15 + i.val * 2 ^ 43 + t.val * stepMul)) =
      tweakBytes (.fchain index c s j a i t)) (d : FPos) (x : E) :
    @forestRecoverChain Id _ inst (spp pp) index c s j a i d (sv x) =
      sv (fChain pp ka i.val (4 - d.val) x d.val) :=
  sForestWalk_cells hq hadr _ x _ (by have := d.isLt; simp only [chainTop] at this ⊢; omega)

/-- The end of chain `k` of a child opened at `word` from the value `vals k`. -/
def fEnds (pp ka : E) (word : Codeword) (vals : Nat → E) (k : Nat) : E :=
  fChain pp ka k (4 - (word ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩).val) (vals k) (word ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩).val

/-- **A child leaf over cells**: the hash of the six chain ends. -/
theorem sChildRecover_cells (hq : SQ inst) {pp ka aL : E} {index : Index} {c : Coord} {s : SuperIdx}
    {j : SubIdx} {a : ChildIdx} (word : Codeword) (vals : Nat → E)
    (hadr : ∀ (i : FChain) (t : FStep), cellBytes (ka + eOfNat (tw 15 + i.val * 2 ^ 43 + t.val * stepMul)) =
      tweakBytes (.fchain index c s j a i t))
    (hL : cellBytes aL = tweakBytes (.childLeaf index c s j a)) :
    @childRecover Id _ inst (spp pp) index c s j a word (fun i => sv (vals i.val)) =
      sv (hcell (pp :: aL :: (List.range 6).map (fEnds pp ka word vals))).1 := by
  rw [childRecover.eq_def]
  simp only [bind, sSequenceFin_id]
  apply sHash_cells hq
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (List.ofFn _).flatMap (Sphincs.bytesLE 16) = _
  rw [bytesLE_spp, ← hL]
  simp only [sForestRecoverChain_cells hq (hadr _)]
  have e : (fun i : FChain => sv (fChain pp ka i.val (4 - (word i).val) (vals i.val) (word i).val)) =
      fun i : FChain => sv (fEnds pp ka word vals i.val) := funext fun i => by
    rw [fEnds, show (⟨i.val % 6, Nat.mod_lt _ (by norm_num)⟩ : FChain) = i from Fin.ext (Nat.mod_eq_of_lt i.isLt)]
  rw [e]
  show cellBytes pp ++ cellBytes aL ++
    (List.ofFn fun i : FChain => sv (fEnds pp ka word vals i.val)).flatMap (Sphincs.bytesLE 16) = _
  rw [show (List.ofFn fun i : FChain => sv (fEnds pp ka word vals i.val)) =
      ((List.range 6).map (fEnds pp ka word vals)).map sv from
    (ofFn_val_eq childChains (fun k => sv (fEnds pp ka word vals k))).trans List.map_map.symm]
  exact (congrArg (fun t => cellBytes pp ++ cellBytes aL ++ t) (sflatMap_bytesLE_sv _)).trans (by simp)

/-- A tree of the forest folded over cells: its addresses' bytes are the nodes' tweaks, its bits
the leaf's. -/
theorem sSubFold_cells (hq : SQ inst) {pp : E} {A : Nat → E} {index : Index} {c : Coord} {s : SuperIdx}
    {j : SubIdx} {a : ChildIdx}
    (hA : ∀ (l : Fin subHeight) (node : ChildIdx), node.val = a.val / 2 ^ (l.val + 1) →
      cellBytes (A l.val) = tweakBytes (.subNode index c s j l node))
    (sibs : Nat → E) :
    ∀ m ≤ subHeight, ∀ x : E,
      @subFold Id _ inst (spp pp) index c s j a (fun l => sv (sibs l.val)) m (sv x) =
        sv (mFold pp A (fun l => a.val.testBit l) sibs m 0 x)
  | 0, _, x => by rw [subFold.eq_1]; rfl
  | m + 1, hm, x => by
      rw [subFold.eq_2, mFold_succ]
      simp only [bind, Nat.zero_add]
      rw [sSubFold_cells hq hA sibs m (by omega) x, dite_of (by omega)]
      split
      · next hb =>
        apply sHash_cells hq
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv (sibs m)) ++
          Sphincs.bytesLE 16 (sv _)) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
        simp
      · next hb =>
        apply sHash_cells hq
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv _) ++
          Sphincs.bytesLE 16 (sv (sibs m))) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
        simp

theorem sTopFold_cells (hq : SQ inst) {pp : E} {A : Nat → E} {index : Index} {c : Coord} {s : SuperIdx}
    (hA : ∀ (l : Fin topHeight) (node : SuperIdx), node.val = s.val / 2 ^ (l.val + 1) →
      cellBytes (A l.val) = tweakBytes (.topNode index c l node))
    (sibs : Nat → E) :
    ∀ m ≤ topHeight, ∀ x : E,
      @topFold Id _ inst (spp pp) index c s (fun l => sv (sibs l.val)) m (sv x) =
        sv (mFold pp A (fun l => s.val.testBit l) sibs m 0 x)
  | 0, _, x => by rw [topFold.eq_1]; rfl
  | m + 1, hm, x => by
      rw [topFold.eq_2, mFold_succ]
      simp only [bind, Nat.zero_add]
      rw [sTopFold_cells hq hA sibs m (by omega) x, dite_of (by omega)]
      split
      · next hb =>
        apply sHash_cells hq
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv (sibs m)) ++
          Sphincs.bytesLE 16 (sv _)) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
        simp
      · next hb =>
        apply sHash_cells hq
        show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ (Sphincs.bytesLE 16 (sv _) ++
          Sphincs.bytesLE 16 (sv (sibs m))) = _
        rw [bytesLE_spp, bytesLE_sv, bytesLE_sv, ← hA ⟨m, by omega⟩ _ rfl]
        simp

/-- **A super-child over cells.** -/
theorem sSuperHash_cells (hq : SQ inst) {pp aS t00 t01 t10 t11 : E} {index : Index} {c : Coord}
    {s : SuperIdx} (hS : cellBytes aS = tweakBytes (.superChild index c s)) :
    @superHash Id _ inst (spp pp) index c s (fun j => if j = 0 then (sv t00, sv t01) else (sv t10, sv t11)) =
      sv (hcell [pp, aS, t00, t01, t10, t11]).1 := by
  apply sHash_cells hq
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ superPayload _ = _
  rw [bytesLE_spp, ← hS]
  simp [superPayload, nodePayload, bytesLE_sv]

/-- **The forest key over cells**: the hash of the sixteen top nodes. -/
theorem sForestRecover_cells (hq : SQ inst) {pp aR : E} {index : Index} {marks : Coord → CoordMark}
    {opening : Coord → CoordOpening} (T : Nat → E)
    (hc : ∀ c : Coord, @coordRecover Id _ inst (spp pp) index c (marks c) (opening c) =
      (sv (T (2 * c.val)), sv (T (2 * c.val + 1))))
    (hR : cellBytes aR = tweakBytes (.roots index)) :
    @forestRecover Id _ inst (spp pp) index marks opening = sv (hcell (pp :: aR :: (List.range 16).map T)).1 := by
  rw [forestRecover.eq_def]
  simp only [bind, sSequenceFin_id]
  apply sHash_cells hq
  show Sphincs.bytesLE 16 (spp pp) ++ tweakBytes _ ++ rootsPayload _ = _
  rw [bytesLE_spp, ← hR]
  simp only [rootsPayload, nodePayload, hc]
  show cellBytes pp ++ cellBytes aR ++ (List.ofFn fun c : Coord => (sv (T (2 * c.val)), sv (T (2 * c.val + 1)))).flatMap
    (fun p => Sphincs.bytesLE 16 p.1 ++ Sphincs.bytesLE 16 p.2) = _
  rw [show (List.ofFn fun c : Coord => (sv (T (2 * c.val)), sv (T (2 * c.val + 1)))) =
      (List.range 8).map (fun k => (sv (T (2 * k)), sv (T (2 * k + 1)))) from
    ofFn_val_eq forestCoords (fun k => (sv (T (2 * k)), sv (T (2 * k + 1))))]
  simp [List.range_succ, bytesLE_sv]

end
end LeanVM.Guest.B1.Sig
