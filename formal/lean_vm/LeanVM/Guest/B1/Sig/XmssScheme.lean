/-
  LeanVM.Guest.B1.Sig.XmssScheme

  leanXMSS verification with BLAKE2s (`Node.xmssVerify`) as pure functions of the guest's cells.
-/

module

public import LeanVM.Guest.B1.Sig.Bytes
public import LeanVM.Guest.B1.Sig.Hashing
public import LeanVM.Guest.B1.Sig.Merkle

/-!
# leanXMSS over cells

`Node.xmssVerify` runs `LeanXmss.Concrete.verify` in `Id` with BLAKE2s as the oracle. The lemmas
here are stated for any oracle instance on `Id` with the hypothesis `XQ` that it is BLAKE2s: the
kernel then never compares the instance with another term, which would unfold the hash. Each
routine is a pure function in `Id` (`*_id`), and a hash of cells' bytes is the first cell of
their `hcell` (`tweakableHash_cells`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value LeanXmss LeanXmss.Concrete

@[expose] public section

/-- The oracle is BLAKE2s. -/
def XQ (inst : HasQuery LeanXmss.HashSpec Id) : Prop :=
  ∀ x, (inst.query (spec := LeanXmss.HashSpec) x : Id HashOutput) = Node.blake2sBits x

theorem xq_blake2s : XQ ⟨Node.blake2sBits⟩ := fun _ => rfl

variable {inst : HasQuery LeanXmss.HashSpec Id}

/-- **A hash of cells**: a tweakable hash whose input is the bytes of cells is the value of the
first cell of their `hcell`. -/
theorem tweakableHash_cells (hq : XQ inst) {P : PublicParameter} {dom : HashDomain}
    {payload : HashInput} {cs : List E} (h : tweakableHashInput P dom payload = cs.flatMap cellBytes) :
    @tweakableHash Id _ inst P dom payload = cellVal (hcell cs).1 := by
  rw [tweakableHash.eq_def]
  simp only [bind, pure, oracleHash]
  rw [hq, h, truncateHash_blake2sBits]
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
    @LeanXmss.Concrete.verify Id _ inst pk msg σ = true ↔
      ∃ r0, @layerRoot Id _ inst pk.parameter bottomLayer (keyAt σ.leafIndex bottomLayer) (bytesLE 32 msg)
          (σ.layers bottomLayer) = some r0 ∧
        @layerRoot Id _ inst pk.parameter topLayer (keyAt σ.leafIndex topLayer) (bytesLE 16 r0)
          (σ.layers topLayer) = some pk.root := by
  rw [LeanXmss.Concrete.verify.eq_def]
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
    Node.xmssVerify pk msg σ = true ↔
      ∃ r0, @layerRoot Id _ ⟨Node.blake2sBits⟩ pk.parameter bottomLayer (keyAt σ.leafIndex bottomLayer)
          (bytesLE 32 msg) (σ.layers bottomLayer) = some r0 ∧
        @layerRoot Id _ ⟨Node.blake2sBits⟩ pk.parameter topLayer (keyAt σ.leafIndex topLayer) (bytesLE 16 r0)
          (σ.layers topLayer) = some pk.root := by
  rw [Node.xmssVerify.eq_def, idRun]
  exact verify_iff pk msg σ

/-! ## The routines in `Id` -/

theorem layerRoot_id (P : PublicParameter) (lay : Layer) (key : KeyIndex) (msg : HashInput)
    (part : LayerSignature) :
    @layerRoot Id _ inst P lay key msg part =
      (@otsLeaf Id _ inst P lay key msg part.randomness part.chainValues).map
        (fun leaf => @treeFold Id _ inst P lay key part.path layerHeight leaf) := by
  rw [layerRoot.eq_def]
  simp only [bind, pure]
  split
  next leaf h => rw [h]; rfl
  next h =>
    cases h' : @otsLeaf Id _ inst P lay key msg part.randomness part.chainValues with
    | none => rfl
    | some leaf => exact absurd h' (h leaf)

theorem otsLeaf_id (P : PublicParameter) (lay : Layer) (key : KeyIndex) (msg : HashInput) (R : Randomness)
    (vals : ChainIndex → LeanXmss.Digest) :
    @otsLeaf Id _ inst P lay key msg R vals =
      (Codeword.decode (@messageDigest Id _ inst P lay key msg R)).map fun enc =>
        @leafHash Id _ inst P lay key fun i => @recoverChain Id _ inst P lay key i (enc i) (vals i) := by
  rw [otsLeaf.eq_def]
  simp only [bind, pure]
  split
  next enc h => rw [h, sequenceFin_id]; rfl
  next h =>
    cases h' : Codeword.decode (@messageDigest Id _ inst P lay key msg R) with
    | none => rfl
    | some enc => exact absurd h' (h enc)

theorem dite_of {c : Prop} [Decidable c] (h : c) {α : Sort*} (t : c → α) (e : ¬c → α) :
    dite c t e = t h := by simp [h]

theorem chainWalk_succ (P : PublicParameter) (lay : Layer) (key : KeyIndex) (i : ChainIndex) (start n : Nat)
    (v : LeanXmss.Digest) :
    @chainWalk Id _ inst P lay key i start (n + 1) v =
      if hstep : start + n < chainLength - 1 then
        @tweakableHash Id _ inst P (.chain lay key ⟨start + n, hstep⟩)
          (chainPayload i (@chainWalk Id _ inst P lay key i start n v))
      else 0 := by
  rw [chainWalk.eq_2]
  simp only [bind]
  split <;> rfl

/-- The first step of a walk taken first. -/
theorem chainWalk_shift (P : PublicParameter) (lay : Layer) (key : KeyIndex) (i : ChainIndex) :
    ∀ (n start : Nat) (v : LeanXmss.Digest) (hs : start < chainLength - 1), start + n + 1 ≤ chainLength - 1 →
      @chainWalk Id _ inst P lay key i start (n + 1) v =
        @chainWalk Id _ inst P lay key i (start + 1) n
          (@tweakableHash Id _ inst P (.chain lay key ⟨start, hs⟩) (chainPayload i v))
  | 0, start, v, hs, _ => by
      rw [chainWalk_succ, dite_of (by omega), chainWalk.eq_1, chainWalk.eq_1]
      rfl
  | n + 1, start, v, hs, h => by
      have h1 : start + (n + 1) < chainLength - 1 := by omega
      have h2 : start + 1 + n < chainLength - 1 := by omega
      rw [chainWalk_succ, dite_of h1, chainWalk_shift P lay key i n start v hs (by omega), chainWalk_succ,
        dite_of h2]
      have : (⟨start + (n + 1), h1⟩ : ChainStep) = ⟨start + 1 + n, h2⟩ := Fin.ext (by simp only; omega)
      rw [this]

/-! ## Hashes of cells -/

/-- A cell as a leanXMSS digest. -/
def xv (x : E) : LeanXmss.Digest := cellVal x

/-- A cell as a leanXMSS public parameter. -/
def xpp (x : E) : PublicParameter := cellVal x

theorem bytesLE_xv (x : E) : bytesLE 16 (xv x) = cellBytes x := bytesLE_cellVal x

theorem bytesLE_xpp (x : E) : bytesLE 16 (xpp x) = cellBytes x := bytesLE_cellVal x

theorem bytesLE_ofNat_cell {i : Nat} (hi : i < 2 ^ 64) :
    bytesLE 16 (BitVec.ofNat 128 i) = cellBytes (eOfNat i) := by
  rw [bytesLE_eq, cellBytes_eOfNat hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- A hash of cells, as a digest. -/
theorem tweakableHash_xv (hq : XQ inst) {P : PublicParameter} {dom : HashDomain}
    {payload : HashInput} {cs : List E} (h : tweakableHashInput P dom payload = cs.flatMap cellBytes) :
    @tweakableHash Id _ inst P dom payload = xv (hcell cs).1 := tweakableHash_cells hq h

/-- **A chain step over cells**, its address's bytes those of the step's tweak. -/
theorem chainStep_cells (hq : XQ inst) {pp a x : E} {lay : Layer} {key : KeyIndex} {i : ChainIndex}
    {s : ChainStep} (ha : cellBytes a = tweakBytes (.chain lay key s)) :
    @tweakableHash Id _ inst (xpp pp) (.chain lay key s) (chainPayload i (xv x)) =
      xv (hcell [pp, a, x, eOfNat i.val]).1 := by
  apply tweakableHash_xv hq
  show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (bytesLE 16 (xv x) ++ bytesLE 16 (BitVec.ofNat 128 i.val)) = _
  rw [bytesLE_xpp, bytesLE_xv, ← ha, bytesLE_ofNat_cell (by have := i.isLt; simp [numChains] at this; omega)]
  simp

/-- **A chain walked from digit `d` over cells.** -/
theorem recoverChain_cells (hq : XQ inst) {pp : E} {adr : Nat → E} {lay : Layer} {key : KeyIndex}
    {i : ChainIndex} (hadr : ∀ (s : ChainStep), cellBytes (adr s) = tweakBytes (.chain lay key s)) :
    ∀ (d : Digit) (x : E), @recoverChain Id _ inst (xpp pp) lay key i d (xv x) =
      xv (tipPair true pp adr 0 i.val d.val x).1 := by
  have hwalk : ∀ (n start : Nat) (x : E), start + n + 1 ≤ chainLength - 1 →
      @chainWalk Id _ inst (xpp pp) lay key i start (n + 1) (xv x) =
        xv (chainFrom true pp adr 0 i.val n start x).1 := by
    intro n
    induction n with
    | zero =>
        intro start x h
        rw [chainWalk_succ, dite_of (by omega), chainWalk.eq_1]
        exact chainStep_cells hq (hadr ⟨start + 0, by omega⟩)
    | succ n ih =>
        intro start x h
        rw [chainWalk_shift _ _ _ _ _ _ _ (by omega) h, chainStep_cells hq (hadr ⟨start, by omega⟩),
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

theorem ofFn_val_eq {α : Type} (n : Nat) (g : Nat → α) :
    (List.ofFn fun i : Fin n => g i.val) = (List.range n).map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem flatMap_bytesLE_xv : ∀ (l : List E), List.flatMap (bytesLE 16) (l.map xv) = l.flatMap cellBytes
  | [] => rfl
  | x :: l => by
      show bytesLE 16 (xv x) ++ List.flatMap (bytesLE 16) (l.map xv) = cellBytes x ++ l.flatMap cellBytes
      rw [bytesLE_xv, flatMap_bytesLE_xv l]

/-- **The one-time leaf over cells.** -/
theorem leafHash_cells (hq : XQ inst) {pp a : E} {lay : Layer} {key : KeyIndex} (tips : Nat → E)
    (ha : cellBytes a = tweakBytes (.leaf lay key)) :
    @leafHash Id _ inst (xpp pp) lay key (fun i => xv (tips i.val)) =
      xv (hcell (pp :: a :: (List.range numChains).map tips)).1 := by
  apply tweakableHash_xv hq
  show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (List.ofFn fun i : ChainIndex => xv (tips i.val)).flatMap (bytesLE 16) = _
  rw [bytesLE_xpp, ← ha, show (List.ofFn fun i : ChainIndex => xv (tips i.val)) = ((List.range numChains).map tips).map xv
    from (ofFn_val_eq numChains (fun i => xv (tips i))).trans (List.map_map.symm)]
  exact (congrArg (fun t => cellBytes pp ++ cellBytes a ++ t) (flatMap_bytesLE_xv _)).trans (by simp)

/-- **The message digest over cells.** -/
theorem messageDigest_cells (hq : XQ inst) {pp a rho : E} {lay : Layer} {key : KeyIndex} {M : HashInput}
    {cs : List E} (ha : cellBytes a = tweakBytes (.message lay key)) (hM : M = cs.flatMap cellBytes) :
    @messageDigest Id _ inst (xpp pp) lay key M (xv rho) = xv (hcell (pp :: a :: cs ++ [rho])).1 := by
  apply tweakableHash_xv hq
  show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (M ++ bytesLE 16 (xv rho)) = _
  rw [bytesLE_xpp, bytesLE_xv, ← ha, hM]
  simp

/-- A path's fold, its last level taken last. -/
theorem mFold_succ (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m l : Nat) (x : E), mFold pp A bits sibs (m + 1) l x =
      let y := mFold pp A bits sibs m l x
      (hcell [pp, A (l + m), if bits (l + m) then sibs (l + m) else y,
        if bits (l + m) then y else sibs (l + m)]).1
  | 0, l, x => rfl
  | m + 1, l, x => by
      rw [mFold, mFold_succ pp A bits sibs m (l + 1)]
      simp only [show l + 1 + m = l + (m + 1) by omega]
      rfl

/-- **A layer's tree over cells**: the fold of a path whose addresses' bytes are the nodes'
tweaks, its bits the key's. -/
theorem treeFold_cells (hq : XQ inst) {pp : E} {A : Nat → E} {lay : Layer} {key : KeyIndex}
    (hA : ∀ l < layerHeight, cellBytes (A l) = tweakBytes (.node lay (l + 1) (key.val / 2 ^ (l + 1))))
    (sibs : Nat → E) :
    ∀ m ≤ layerHeight, ∀ x : E, @treeFold Id _ inst (xpp pp) lay key (fun l => xv (sibs l.val)) m (xv x) =
      xv (mFold pp A (fun l => key.val.testBit l) sibs m 0 x)
  | 0, _, x => by rw [treeFold.eq_1]; rfl
  | m + 1, hm, x => by
      rw [treeFold.eq_2, mFold_succ]
      simp only [bind, Nat.zero_add]
      rw [treeFold_cells hq hA sibs m (by omega) x, dite_of (by omega)]
      split
      · next hb =>
        apply tweakableHash_xv hq
        show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (bytesLE 16 (xv (sibs m)) ++ bytesLE 16 (xv _)) = _
        rw [bytesLE_xpp, bytesLE_xv, bytesLE_xv, ← hA m (by omega)]
        simp
      · next hb =>
        apply tweakableHash_xv hq
        show bytesLE 16 (xpp pp) ++ tweakBytes _ ++ (bytesLE 16 (xv _) ++ bytesLE 16 (xv (sibs m))) = _
        rw [bytesLE_xpp, bytesLE_xv, bytesLE_xv, ← hA m (by omega)]
        simp

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

theorem xv_lit {N : Nat} (h : N < 2 ^ 128) : xv (lit N) = BitVec.ofNat 128 N := by
  show cellVal (lit N) = _
  rw [cellVal, cellNat_lit, Nat.mod_eq_of_lt h]

theorem lit_toNat (d : LeanXmss.Digest) : lit d.toNat = cellOf d := by
  simp only [lit, word, cellOf, ofBits_mod]
  rfl

theorem digit_ofNat (N i : Nat) : (Codeword.digit (BitVec.ofNat 128 N) i).val = N % 2 ^ 128 / 4 ^ i % 4 := by
  show (BitVec.extractLsb' (2 * i) 2 (BitVec.ofNat 128 N)).toNat = _
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

/-- **A codeword's digits**: the digest holding the literal of `58` digits below 4 summing to
106 decodes to them. -/
theorem decode_lit {dig : Nat → Nat} (hd : ∀ j, dig j < 4)
    (hs : ∑ i ∈ Finset.range numChains, dig i = targetSum) :
    Codeword.decode (xv (lit (∑ j ∈ Finset.range numChains, dig j * 4 ^ j))) = some fun i => ⟨dig i.val, hd _⟩ := by
  have hlt := base4_lt hd numChains
  have hlt' : ∑ j ∈ Finset.range numChains, dig j * 4 ^ j < 2 ^ 116 := by
    have : (4 : Nat) ^ numChains = 2 ^ 116 := by norm_num [numChains]
    omega
  rw [xv_lit (by omega)]
  have henc : Codeword.encoding (BitVec.ofNat 128 (∑ j ∈ Finset.range numChains, dig j * 4 ^ j)) =
      fun i => ⟨dig i.val, hd _⟩ := by
    funext i
    apply Fin.ext
    show (Codeword.digit _ i.val).val = dig i.val
    rw [digit_ofNat, Nat.mod_eq_of_lt (a := ∑ j ∈ Finset.range numChains, dig j * 4 ^ j) (by omega)]
    exact base4_digit hd _ _ i.isLt
  have hv : Codeword.Valid (BitVec.ofNat 128 (∑ j ∈ Finset.range numChains, dig j * 4 ^ j)) := by
    refine ⟨?_, ?_⟩
    · have ht : (BitVec.ofNat 128 (∑ j ∈ Finset.range numChains, dig j * 4 ^ j)).toNat =
          ∑ j ∈ Finset.range numChains, dig j * 4 ^ j := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      show (BitVec.ofNat 128 (∑ j ∈ Finset.range numChains, dig j * 4 ^ j)).toNat / 2 ^ (2 * 58) = 0
      rw [ht]
      exact Nat.div_eq_of_lt (by norm_num at hlt' ⊢; omega)
    · rw [henc, Codeword.sum, ← hs, ← Fin.sum_univ_eq_sum_range]
  simp only [Codeword.decode, hv, ↓reduceIte, henc]

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
theorem decode_some {d : LeanXmss.Digest} {enc : Encoding} (h : Codeword.decode d = some enc) :
    (∀ i : ChainIndex, (enc i).val = d.toNat / 4 ^ i.val % 4) ∧
      ∑ i ∈ Finset.range numChains, d.toNat / 4 ^ i % 4 = targetSum ∧
      d.toNat = ∑ j ∈ Finset.range numChains, d.toNat / 4 ^ j % 4 * 4 ^ j := by
  simp only [Codeword.decode] at h
  split at h
  next hv =>
    cases h
    have hdig : ∀ i : Nat, (Codeword.digit d i).val = d.toNat / 4 ^ i % 4 := fun i => by
      show (BitVec.extractLsb' (2 * i) 2 d).toNat = _
      rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_mul]
      norm_num
    refine ⟨fun i => hdig i.val, ?_, ?_⟩
    · rw [← hv.2, Codeword.sum, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun i _ => (hdig i.val).symm
    · have h1 := hv.1
      have hlt : d.toNat < 4 ^ numChains := by
        simp only [winternitzBits, numChains] at h1
        rw [Nat.div_eq_zero_iff] at h1
        norm_num [numChains] at h1 ⊢
        omega
      exact (base4_expand _ _ hlt).symm
  next => cases h

end
end LeanVM.Guest.B1.Sig
