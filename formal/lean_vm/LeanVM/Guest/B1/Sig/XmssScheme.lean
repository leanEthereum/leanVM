/-
  LeanVM.Guest.B1.Sig.XmssScheme

  leanXMSS verification with Keccak-256 (`Node.xmssVerify`) as pure functions of the guest's cells.
-/

module

public import LeanVM.Guest.B1.Sig.Bytes
public import LeanVM.Guest.B1.Sig.Shapes
public import Common.WithHash
public import LeanVM.Guest.WithHashBridge
public import LeanVM.Guest.WithHash

/-!
# leanXMSS over cells

`Node.xmssVerify` runs `LeanXmss.Verification.verify` in `Id` with Keccak-256 as the oracle. The
lemmas
here are stated for any oracle instance on `Id` with the hypothesis `XQ` that it is Keccak-256: the
kernel then never compares the instance with another term, which would unfold the hash. Each
routine is a pure function in `Id` (`*_id`, `*_succ`), and a hash of cells' bytes is the first cell
of their `hcell`, the digest's two cells (`tweakableHash_cells`).

* `verify_iff`, `xmssVerify_iff`: the bottom layer's root, then the top layer's from it, is the
  key's;
* `layerRoot_id`, `otsLeaf_id`, `chainWalk_succ`, `chainWalk_shift`: the routines in `Id`;
* `chainStep_cells`, `recoverChain_cells` (over `xChain`), `leafHash_cells`, `messageDigest_cells`,
  `treeFold_cells` (over `xFold`): the routines on cells whose addresses' bytes are the tweaks';
* `decode_lit`, `decode_some`: a codeword is the literal of its base-4 digits, summing to `106`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanXmss HashSig LeanXmss.Verification HashSig.OverPermutation

@[expose] public section

/-- The digest cells of the Keccak-256 hash of cells. -/
def hcell (cs : List E) : E × E := digestHalves (keccak256 (cs.flatMap cellBytes))

theorem cellsBytes_eq_flatMap (cs : List E) : cellsBytes cs = cs.flatMap cellBytes := rfl

/-- The oracle is Keccak-256. -/
def XQ (inst : HasQuery LeanXmss.HashSpec Id) : Prop :=
  ∀ x, (inst.query (spec := LeanXmss.HashSpec) x : Id HashOutput) = Node.keccakBits x

theorem xq_keccak : XQ ⟨Node.keccakBits⟩ := fun _ => rfl

variable {inst : HasQuery LeanXmss.HashSpec Id}

/-- **A hash of cells**: a tweakable hash whose input is the bytes of cells is the value of the
first cell of their `hcell`. -/
theorem tweakableHash_cells (hq : XQ inst) {P : PublicParameter} {dom : HashDomain}
    {payload : HashInput} {cs : List E} (h : tweakableHashInput P dom payload = cs.flatMap cellBytes) :
    @tweakableHashWithHash Id _ inst P dom payload = cellVal (hcell cs).1 := by
  unfold tweakableHashWithHash thWithHash
  simp only [bind, pure, oracleHashWithHash]
  rw [hq, show thInput P (hashDomainFields dom) payload = cs.flatMap cellBytes from h,
    truncateHash_keccakBits]
  rfl

theorem sequenceFin_id {α : Type} : ∀ {n : Nat} (f : Fin n → Id α), sequenceFin f = f
  | 0, f => funext fun i => i.elim0
  | n + 1, f => by
      simp only [sequenceFin]
      have := sequenceFin_id (fun i : Fin n => f i.succ)
      rw [this]
      funext i
      refine Fin.cases rfl (fun j => rfl) i

/-- **Verification**: the bottom layer's root, then the top layer's from it, is the key's. -/
theorem verify_iff (pk : PublicKey) (msg : Message) (σ : Signature) :
    @LeanXmss.Verification.verifyWithHash Id _ inst pk msg σ = true ↔
      ∃ r0, @layerRootWithHash Id _ inst pk.parameter bottomLayer (keyIndexOnLayer σ.leafIndex
          bottomLayer)
          (littleEndianBytes 32 msg) (σ.layers bottomLayer) = some r0 ∧
        @layerRootWithHash Id _ inst pk.parameter topLayer (keyIndexOnLayer σ.leafIndex topLayer) (littleEndianBytes 16 r0)
          (σ.layers topLayer) = some pk.root := by
  rw [LeanXmss.Verification.verifyWithHash.eq_def]
  simp only [bind, pure]
  split
  next r0 h1 =>
    split
    next r h2 =>
      rw [decide_eq_true_iff]
      constructor
      · rintro rfl; exact ⟨r0, h1, h2⟩
      · rintro ⟨r0', h1', h2'⟩
        have e := Option.some.inj (h1.symm.trans h1')
        subst e
        exact Option.some.inj (h2.symm.trans h2')
    next h2 =>
      refine ⟨fun h => absurd h Bool.false_ne_true, ?_⟩
      rintro ⟨r0', h1', h2'⟩
      have e := Option.some.inj (h1.symm.trans h1')
      subst e
      exact absurd h2' (h2 _)
  next h1 =>
    refine ⟨fun h => absurd h Bool.false_ne_true, ?_⟩
    rintro ⟨r0', h1', -⟩
    exact absurd h1' (h1 _)

theorem idRun {α : Type} (x : Id α) : Id.run x = x := rfl

theorem xmssVerify_iff (pk : PublicKey) (msg : Message) (σ : Signature) :
    LeanXmss.verifyWithKeccak pk msg σ = true ↔
      ∃ r0, @layerRootWithHash Id _ ⟨Node.keccakBits⟩ pk.parameter bottomLayer
          (keyIndexOnLayer σ.leafIndex bottomLayer) (littleEndianBytes 32 msg) (σ.layers
              bottomLayer) = some r0 ∧
        @layerRootWithHash Id _ ⟨Node.keccakBits⟩ pk.parameter topLayer (keyIndexOnLayer σ.leafIndex
            topLayer)
          (littleEndianBytes 16 r0) (σ.layers topLayer) = some pk.root := by
  rw [Node.xmssVerify_eq_withHash, idRun]
  exact verify_iff pk msg σ

/-! ## The routines in `Id` -/

theorem layerRoot_id (P : PublicParameter) (lay : Layer) (key : KeyIndex) (msg : HashInput)
    (part : LayerSignature) :
    @layerRootWithHash Id _ inst P lay key msg part =
      (@otsLeafWithHash Id _ inst P lay key msg part.randomizer part.chainValues).map
        (fun leaf => @treeFoldWithHash Id _ inst P lay key part.authenticationPath layerHeight leaf) := by
  rw [layerRootWithHash.eq_def]
  simp only [bind, pure]
  split
  next leaf h => rw [h]; rfl
  next h =>
    cases h' : @otsLeafWithHash Id _ inst P lay key msg part.randomizer part.chainValues with
    | none => rfl
    | some leaf => exact absurd h' (h leaf)

theorem otsLeaf_id (P : PublicParameter) (lay : Layer) (key : KeyIndex) (msg : HashInput)
    (R : Randomizer) (vals : ChainIndex → HashSig.Digest) :
    @otsLeafWithHash Id _ inst P lay key msg R vals =
      (Codeword.decode (@messageDigestWithHash Id _ inst P lay key msg R)).map fun enc =>
        @leafHashWithHash Id _ inst P lay key fun i => @recoverChainWithHash Id _ inst P lay key i (enc i) (vals i) := by
  rw [otsLeafWithHash.eq_def]
  simp only [bind, pure]
  split
  next enc h => rw [h, sequenceFin_id]; rfl
  next h =>
    cases h' : Codeword.decode (@messageDigestWithHash Id _ inst P lay key msg R) with
    | none => rfl
    | some enc => exact absurd h' (h enc)

theorem dite_of {c : Prop} [Decidable c] (h : c) {α : Sort*} (t : c → α) (e : ¬c → α) :
    dite c t e = t h := by simp [h]

theorem chainWalk_succ (P : PublicParameter) (lay : Layer) (key : KeyIndex) (i : ChainIndex)
    (start n : Nat) (v : HashSig.Digest) :
    @chainWalkWithHash Id _ inst P lay key i start (n + 1) v =
      if hstep : start + n < chainLength - 1 then
        @tweakableHashWithHash Id _ inst P (.chain lay key ⟨start + n, hstep⟩)
          (chainPayload i (@chainWalkWithHash Id _ inst P lay key i start n v))
      else 0 := by
  rw [chainWalk_eq_succ]
  simp only [bind]
  split <;> rfl

/-- The first step of a walk taken first. -/
theorem chainWalk_shift (P : PublicParameter) (lay : Layer) (key : KeyIndex) (i : ChainIndex) :
    ∀ (n start : Nat) (v : HashSig.Digest) (hs : start < chainLength - 1),
      start + n + 1 ≤ chainLength - 1 →
      @chainWalkWithHash Id _ inst P lay key i start (n + 1) v =
        @chainWalkWithHash Id _ inst P lay key i (start + 1) n
          (@tweakableHashWithHash Id _ inst P (.chain lay key ⟨start, hs⟩) (chainPayload i v))
  | 0, start, v, hs, _ => by
      rw [chainWalk_succ, dite_of (by omega), chainWalk_eq_zero, chainWalk_eq_zero]
      rfl
  | n + 1, start, v, hs, h => by
      have h1 : start + (n + 1) < chainLength - 1 := by omega
      have h2 : start + 1 + n < chainLength - 1 := by omega
      rw [chainWalk_succ, dite_of h1, chainWalk_shift P lay key i n start v hs (by omega),
        chainWalk_succ, dite_of h2]
      have : (⟨start + (n + 1), h1⟩ : ChainStep) = ⟨start + 1 + n, h2⟩ := Fin.ext (by simp only; omega)
      rw [this]

theorem treeFold_succ (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → HashSig.Digest) (m : Nat) (v : HashSig.Digest) :
    @treeFoldWithHash Id _ inst P lay key path (m + 1) v =
      let current := @treeFoldWithHash Id _ inst P lay key path m v
      let sibling := if hlevel : m < layerHeight then path ⟨m, hlevel⟩ else 0
      if key.val.testBit m then
        @tweakableHashWithHash Id _ inst P (.node lay (m + 1) (key.val / 2 ^ (m + 1))) (nodePayload sibling current)
      else
        @tweakableHashWithHash Id _ inst P (.node lay (m + 1) (key.val / 2 ^ (m + 1))) (nodePayload current sibling) := by
  rw [treeFold_eq_succ]
  simp only [bind]

/-! ## Hashes of cells -/

/-- A cell as a leanXMSS digest. -/
def xv (x : E) : HashSig.Digest := cellVal x

/-- A cell as a leanXMSS public parameter. -/
def xpp (x : E) : PublicParameter := cellVal x

theorem bytesLE_xv (x : E) : littleEndianBytes 16 (xv x) = cellBytes x := bytesLE_cellVal x

theorem bytesLE_xpp (x : E) : littleEndianBytes 16 (xpp x) = cellBytes x := bytesLE_cellVal x

theorem bytesLE_ofNat_cell {i : Nat} (hi : i < 2 ^ 64) :
    littleEndianBytes 16 (BitVec.ofNat 128 i) = cellBytes (eOfNat i) := by
  rw [bytesLE_eq, cellBytes_eOfNat hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- A hash of cells, as a digest. -/
theorem tweakableHash_xv (hq : XQ inst) {P : PublicParameter} {dom : HashDomain}
    {payload : HashInput} {cs : List E} (h : tweakableHashInput P dom payload = cs.flatMap cellBytes) :
    @tweakableHashWithHash Id _ inst P dom payload = xv (hcell cs).1 := tweakableHash_cells hq h

/-- **A chain step over cells**, its address's bytes those of the step's tweak. -/
theorem chainStep_cells (hq : XQ inst) {pp a x : E} {lay : Layer} {key : KeyIndex} {i : ChainIndex}
    {s : ChainStep} (ha : cellBytes a = tweakBytes (.chain lay key s)) :
    @tweakableHashWithHash Id _ inst (xpp pp) (.chain lay key s) (chainPayload i (xv x)) =
      xv (hcell [pp, a, x, eOfNat i.val]).1 := by
  apply tweakableHash_xv hq
  show littleEndianBytes 16 (xpp pp) ++ tweakBytes _ ++ (littleEndianBytes 16 (xv x) ++ littleEndianBytes 16 (BitVec.ofNat 128 i.val)) = _
  rw [bytesLE_xpp, bytesLE_xv, ← ha,
    bytesLE_ofNat_cell (by have := i.isLt; simp [chainCount] at this; omega)]
  simp

/-- `n` chain steps from position `s` on cells: the step leaving position `s` hashes `P`, its
address `adr s`, the value and the chain index. -/
def xChain (pp : E) (adr : Nat → E) (i : Nat) : Nat → Nat → E → E
  | 0, _, x => x
  | n + 1, s, x => xChain pp adr i n (s + 1) (hcell [pp, adr s, x, eOfNat i]).1

/-- **A chain walked from digit `d` over cells.** -/
theorem recoverChain_cells (hq : XQ inst) {pp : E} {adr : Nat → E} {lay : Layer} {key : KeyIndex}
    {i : ChainIndex} (hadr : ∀ (s : ChainStep), cellBytes (adr s) = tweakBytes (.chain lay key s)) :
    ∀ (d : WinternitzDigit) (x : E), @recoverChainWithHash Id _ inst (xpp pp) lay key i d (xv x) =
      xv (xChain pp adr i.val (3 - d.val) d.val x) := by
  have hwalk : ∀ (n start : Nat) (x : E), start + n ≤ chainLength - 1 →
      @chainWalkWithHash Id _ inst (xpp pp) lay key i start n (xv x) = xv (xChain pp adr i.val n start x) := by
    intro n
    induction n with
    | zero => intro start x _; rw [chainWalk_eq_zero]; rfl
    | succ n ih =>
        intro start x h
        rw [chainWalk_shift _ _ _ _ _ _ _ (by omega) h, chainStep_cells hq (hadr ⟨start, by omega⟩),
          ih (start + 1) _ (by omega)]
        rfl
  intro d x
  have hd := d.isLt
  simp only [chainLength, winternitzBits] at hd
  rw [recoverChainWithHash, show chainLength - 1 - d.val = 3 - d.val by simp [chainLength, winternitzBits]]
  exact hwalk _ _ _ (by simp [chainLength, winternitzBits]; omega)

theorem ofFn_val_eq {α : Type} (n : Nat) (g : Nat → α) :
    (List.ofFn fun i : Fin n => g i.val) = (List.range n).map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem flatMap_bytesLE_xv : ∀ (l : List E), List.flatMap (littleEndianBytes 16) (l.map xv) = l.flatMap cellBytes
  | [] => rfl
  | x :: l => by
      show littleEndianBytes 16 (xv x) ++ List.flatMap (littleEndianBytes 16) (l.map xv) = cellBytes x ++ l.flatMap cellBytes
      rw [bytesLE_xv, flatMap_bytesLE_xv l]

/-- **The one-time leaf over cells.** -/
theorem leafHash_cells (hq : XQ inst) {pp a : E} {lay : Layer} {key : KeyIndex} (tips : Nat → E)
    (ha : cellBytes a = tweakBytes (.leaf lay key)) :
    @leafHashWithHash Id _ inst (xpp pp) lay key (fun i => xv (tips i.val)) =
      xv (hcell (pp :: a :: (List.range chainCount).map tips)).1 := by
  apply tweakableHash_xv hq
  show littleEndianBytes 16 (xpp pp) ++ tweakBytes _ ++
    (List.ofFn fun i : ChainIndex => xv (tips i.val)).flatMap (littleEndianBytes 16) = _
  rw [bytesLE_xpp, ← ha, show (List.ofFn fun i : ChainIndex => xv (tips i.val)) =
      ((List.range chainCount).map tips).map xv
    from (ofFn_val_eq chainCount (fun i => xv (tips i))).trans (List.map_map.symm)]
  exact (congrArg (fun t => cellBytes pp ++ cellBytes a ++ t) (flatMap_bytesLE_xv _)).trans (by simp)

/-- **The message digest over cells.** -/
theorem messageDigest_cells (hq : XQ inst) {pp a rho : E} {lay : Layer} {key : KeyIndex}
    {M : HashInput} {cs : List E} (ha : cellBytes a = tweakBytes (.message lay key))
    (hM : M = cs.flatMap cellBytes) :
    @messageDigestWithHash Id _ inst (xpp pp) lay key M (xv rho) = xv (hcell (pp :: a :: cs ++ [rho])).1 := by
  apply tweakableHash_xv hq
  show littleEndianBytes 16 (xpp pp) ++ tweakBytes _ ++ (M ++ littleEndianBytes 16 (xv rho)) = _
  rw [bytesLE_xpp, bytesLE_xv, ← ha, hM]
  simp

/-- `m` levels of a Merkle path on cells, the last level taken last: level `l` hashes `P`, its
address `A l` and the pair in the order of bit `l`. -/
def xFold (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) : Nat → E → E
  | 0, x => x
  | m + 1, x =>
      let y := xFold pp A bits sibs m x
      (hcell [pp, A m, if bits m then sibs m else y, if bits m then y else sibs m]).1

/-- **A layer's tree over cells**: the fold of a path whose addresses' bytes are the nodes'
tweaks, its bits the key's. -/
theorem treeFold_cells (hq : XQ inst) {pp : E} {A : Nat → E} {lay : Layer} {key : KeyIndex}
    (hA : ∀ l < layerHeight, cellBytes (A l) = tweakBytes (.node lay (l + 1) (key.val / 2 ^ (l + 1))))
    (sibs : Nat → E) :
    ∀ m ≤ layerHeight, ∀ x : E,
      @treeFoldWithHash Id _ inst (xpp pp) lay key (fun l => xv (sibs l.val)) m (xv x) =
        xv (xFold pp A (fun l => key.val.testBit l) sibs m x)
  | 0, _, x => by rw [treeFold_eq_zero]; rfl
  | m + 1, hm, x => by
      rw [treeFold_succ]
      simp only [xFold]
      rw [treeFold_cells hq hA sibs m (by omega) x, dite_of (by omega)]
      split
      · apply tweakableHash_xv hq
        show littleEndianBytes 16 (xpp pp) ++ tweakBytes _ ++ (littleEndianBytes 16 (xv (sibs m)) ++ littleEndianBytes 16 (xv _)) = _
        rw [bytesLE_xpp, bytesLE_xv, bytesLE_xv, ← hA m (by omega)]
        simp_all
      · apply tweakableHash_xv hq
        show littleEndianBytes 16 (xpp pp) ++ tweakBytes _ ++ (littleEndianBytes 16 (xv _) ++ littleEndianBytes 16 (xv (sibs m))) = _
        rw [bytesLE_xpp, bytesLE_xv, bytesLE_xv, ← hA m (by omega)]
        simp_all

/-! ## The codeword -/

theorem base4_lt {dig : Nat → Nat} (hd : ∀ j, dig j < 4) :
    ∀ n, ∑ j ∈ Finset.range n, dig j * 4 ^ j < 4 ^ n
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ, pow_succ]
      have := base4_lt hd n
      have h3 : dig n * 4 ^ n ≤ 3 * 4 ^ n := Nat.mul_le_mul_right _ (by have := hd n; omega)
      omega

theorem base4_digit {dig : Nat → Nat} (hd : ∀ j, dig j < 4) :
    ∀ n i, i < n → (∑ j ∈ Finset.range n, dig j * 4 ^ j) / 4 ^ i % 4 = dig i
  | 0, _, h => absurd h (by omega)
  | n + 1, i, h => by
      rw [Finset.sum_range_succ]
      by_cases hi : i = n
      · subst hi
        rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (base4_lt hd i), Nat.zero_add,
          Nat.mod_eq_of_lt (hd i)]
      · have hlt : i < n := by omega
        rw [show dig n * 4 ^ n = 4 ^ i * (4 * (dig n * 4 ^ (n - i - 1))) by
          rw [show 4 ^ n = 4 ^ i * 4 * 4 ^ (n - i - 1) by
            rw [mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega]; ring,
          Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left, base4_digit hd n i hlt]

theorem cellNat_lit (N : Nat) : cellNat (lit N) = N % 2 ^ 128 := by
  simp only [cellNat, lit, word, ofLimbs_limb0, ofLimbs_limb1, kToNat_ofBits, Nat.mod_mod]
  have h1 := Nat.mod_mul_right_div_self N (2 ^ 64) (2 ^ 64)
  have h2 : N % 2 ^ 128 % 2 ^ 64 = N % 2 ^ 64 := Nat.mod_mod_of_dvd _ (by norm_num)
  have h3 := Nat.mod_add_div (N % 2 ^ 128) (2 ^ 64)
  rw [show (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 by norm_num] at h1
  omega

theorem cellVal_lit (N : Nat) : cellVal (lit N) = BitVec.ofNat 128 N := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_cellVal, cellNat_lit, BitVec.toNat_ofNat]

theorem xv_lit (N : Nat) : xv (lit N) = BitVec.ofNat 128 N := cellVal_lit N

theorem digit_ofNat {n : Nat} (N : Nat) (i : Fin n) :
    (digestDigits (BitVec.ofNat 128 N) i).val = N % 2 ^ 128 / 4 ^ i.val % 4 := by
  show (BitVec.extractLsb' (2 * i.val) 2 (BitVec.ofNat 128 N)).toNat = _
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem digit_val {n : Nat} (d : HashSig.Digest) (i : Fin n) :
    (digestDigits d i).val = d.toNat / 4 ^ i.val % 4 := by
  show (BitVec.extractLsb' (2 * i.val) 2 d).toNat = _
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

/-- **A codeword's digits**: the digest holding the literal of `58` digits below 4 summing to
106 decodes to them. -/
theorem decode_lit {dig : Nat → Nat} (hd : ∀ j, dig j < 4)
    (hs : ∑ i ∈ Finset.range chainCount, dig i = targetSum) :
    Codeword.decode (xv (lit (∑ j ∈ Finset.range chainCount, dig j * 4 ^ j))) =
      some fun i => ⟨dig i.val, hd _⟩ := by
  have hlt := base4_lt hd chainCount
  have hlt' : ∑ j ∈ Finset.range chainCount, dig j * 4 ^ j < 2 ^ 116 := by
    have : (4 : Nat) ^ chainCount = 2 ^ 116 := by norm_num [chainCount]
    omega
  rw [xv_lit]
  have henc : (digestDigits (BitVec.ofNat 128 (∑ j ∈ Finset.range chainCount, dig j * 4 ^ j)) :
      Encoding) = fun i => ⟨dig i.val, hd _⟩ := by
    funext i
    apply Fin.ext
    rw [digit_ofNat, Nat.mod_eq_of_lt (a := ∑ j ∈ Finset.range chainCount, dig j * 4 ^ j)
        (by omega)]
    exact base4_digit hd _ _ i.isLt
  have hv : Codeword.Valid (BitVec.ofNat 128 (∑ j ∈ Finset.range chainCount, dig j * 4 ^ j)) := by
    refine ⟨?_, ?_⟩
    · have ht : (BitVec.ofNat 128 (∑ j ∈ Finset.range chainCount, dig j * 4 ^ j)).toNat =
          ∑ j ∈ Finset.range chainCount, dig j * 4 ^ j := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      show (BitVec.ofNat 128 (∑ j ∈ Finset.range chainCount, dig j * 4 ^ j)).toNat / 2 ^ (2 *
          58) = 0
      rw [ht]
      exact Nat.div_eq_of_lt (by norm_num at hlt' ⊢; omega)
    · rw [henc, Codeword.sum, ← hs, ← Fin.sum_univ_eq_sum_range]
  simp only [Codeword.decode]
  split_ifs
  rw [henc]

theorem base4_expand : ∀ n N, N < 4 ^ n → ∑ j ∈ Finset.range n, N / 4 ^ j % 4 * 4 ^ j = N
  | 0, N, h => by simp only [pow_zero, Nat.lt_one_iff] at h; simp [h]
  | n + 1, N, h => by
      rw [Finset.sum_range_succ']
      have ih := base4_expand n (N / 4) (by rw [pow_succ] at h; omega)
      have hs : ∑ j ∈ Finset.range n, N / 4 ^ (j + 1) % 4 * 4 ^ (j + 1) =
          4 * ∑ j ∈ Finset.range n, N / 4 / 4 ^ j % 4 * 4 ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ', Nat.div_div_eq_div_mul]
        ring
      rw [hs, ih]
      simp only [pow_zero, Nat.div_one, Nat.mul_one]
      omega

/-- **A codeword's digits, read back**: a digest that decodes holds the literal of its base-4
digits, which sum to 106. -/
theorem decode_some {d : HashSig.Digest} {enc : Encoding} (h : Codeword.decode d = some enc) :
    (∀ i : ChainIndex, (enc i).val = d.toNat / 4 ^ i.val % 4) ∧
      ∑ i ∈ Finset.range chainCount, d.toNat / 4 ^ i % 4 = targetSum ∧
      d.toNat = ∑ j ∈ Finset.range chainCount, d.toNat / 4 ^ j % 4 * 4 ^ j := by
  simp only [Codeword.decode] at h
  split at h
  next hv =>
    cases h
    refine ⟨fun i => digit_val d i, ?_, ?_⟩
    · rw [← hv.2, Codeword.sum, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun i _ => (digit_val d i).symm
    · have h1 := hv.1
      have hlt : d.toNat < 4 ^ chainCount := by
        simp only [winternitzBits, chainCount] at h1
        rw [Nat.div_eq_zero_iff] at h1
        norm_num [chainCount] at h1 ⊢
        omega
      exact (base4_expand _ _ hlt).symm
  next => cases h

end
end LeanVM.Guest.B1.Sig
