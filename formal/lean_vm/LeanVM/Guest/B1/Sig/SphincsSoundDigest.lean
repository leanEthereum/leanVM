/-
  LeanVM.Guest.B1.Sig.SphincsSoundDigest

  The message digest of `verify_sig_lean_sphincs` (`lean_ethereum.py:4143-4216`)
  is sound: `H_msg`'s two calls hash `R | PK.seed | PK.root | M | BE_32(i)`, `M` the claim's two
  message cells, and whatever bits are hinted, they are the digest's, each field's values theirs.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsFields
public import LeanVM.Guest.B1.Sig.SphincsBytes
public import LeanVM.Guest.WithHashBridge

/-!
# The message digest, sound

* `kec84_sound`: a one-block `KECCAK` of five cells and a counter cell, 84 bytes, writes the digest's
  halves of their hash (`hcellLen`) into the cells it writes (two for `H_msg`'s first call, one for
  its second);
* `sMsg_sound`: the claim's keys and message cells loaded;
* `sDigests_sound`: the padding run, and `H_msg`'s two calls;
* `sCheck_sound`: the bits' number is the digest's: the first call's cells and the second call's low
  two bytes;
* `sDigestBlock_sound`: the whole block.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## An 84-byte `keccak` -/

/-- The digest cells of the Keccak-256 hash of the first `len` bytes of cells. -/
def hcellLen (cs : List E) (len : Nat) : E × E := digestHalves (keccak256 ((cellsBytes cs).take len))

theorem padCells_six (a b c d e f : E) :
    padCells [a, b, c, d, e, f] 84 = [a, b, c, d, e, f + word (2 ^ 32) 0, 0, 0, word (2 ^ 63) 0] := by
  simp [padCells, xorByte, padRead, rate, byteCell]

/-- A counter cell's bytes past its fourth: `i · 2^24` with `i < 256` spells `[0, 0, 0, i]` then
zeros. -/
theorem cellBytes_ctr_getD {i j : Nat} (hi : i < 256) (hj : 4 ≤ j) :
    (cellBytes (word (i * 2 ^ 24) 0)).getD j 0 = 0 := by
  rw [cellBytes_eq_leBytes, word_eq_eOfNat, cellNat_eOfNat (by omega)]
  by_cases hj16 : j < 16
  · rw [List.getD_eq_getElem _ _ (by simp [leBytes]; omega), getElem_leBytes]
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le (show i * 2 ^ 24 < 256 ^ 4 by omega) (Nat.pow_le_pow_right
      (by norm_num) hj))]
    rfl
  · rw [List.getD_eq_default _ _ (by simp [leBytes]; omega)]

/-- The counter cell with the `0x01` padding byte after it. -/
theorem word_ctr_pad {i : Nat} (hi : i < 256) :
    word (i * 2 ^ 24) 0 + word (2 ^ 32) 0 = word (i * 2 ^ 24 + 2 ^ 32) 0 := by
  rw [word_eq_eOfNat, word_eq_eOfNat, word_eq_eOfNat, ← Value.eOfNat_xor, Nat.xor_comm,
    show (2 : Nat) ^ 32 = 2 ^ 32 * 1 by norm_num, two_pow_mul_xor (by omega), add_comm]

/-- **An 84-byte `keccak`**: five cells and a counter cell `i · 2^24` (`BE_32(i)`, `i < 256`), one
block from the zero state. -/
theorem kec84_sound {ins : List V} {o n : Nat} {a b c d e : E} {i : Nat} (hi : i < 256)
    (hK : AtomsHold rd σ [kecS ins (runV o n) false false])
    (hrate : ∀ k < 9, σ (ins.getD k (.n 0)) =
      [a, b, c, d, e, word (i * 2 ^ 24 + 2 ^ 32) 0, 0, 0, word (2 ^ 63) 0].getD k 0)
    (hcap : ∀ k, 9 ≤ k → k < 13 → σ (ins.getD k (.n 0)) = 0) :
    (1 ≤ n → σ (.n o) = (hcellLen [a, b, c, d, e, word (i * 2 ^ 24) 0] 84).1) ∧
      (2 ≤ n → σ (.n (o + 1)) = (hcellLen [a, b, c, d, e, word (i * 2 ^ 24) 0] 84).2) := by
  have hk := hK.atom (List.mem_singleton_self _)
  obtain ⟨hl, -, O, hk, hw⟩ := keccak_holds_full hk
  have hget : ∀ k : Fin 13, cells13 (ins.map σ) k = σ (ins.getD k.val (.n 0)) := fun k => by
    simp only [cells13, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  have hpad : padCells [a, b, c, d, e, word (i * 2 ^ 24) 0] 84 =
      [a, b, c, d, e, word (i * 2 ^ 24 + 2 ^ 32) 0, 0, 0, word (2 ^ 63) 0] := by
    rw [padCells_six, word_ctr_pad hi]
  have := keccak_one (cells := [a, b, c, d, e, word (i * 2 ^ 24) 0]) (len := 84) (by simp)
    (by simp [rate])
    (fun j hj => by
      simp only [cellsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [show cellBytes a ++ (cellBytes b ++ (cellBytes c ++ (cellBytes d ++ (cellBytes e ++
          cellBytes (word (i * 2 ^ 24) 0))))) = (cellBytes a ++ cellBytes b ++ cellBytes c ++
          cellBytes d ++ cellBytes e) ++ cellBytes (word (i * 2 ^ 24) 0) by simp,
        getD_append_right' (by simp [cellBytes_eq_leBytes, leBytes]; omega)]
      exact cellBytes_ctr_getD hi (by simp [cellBytes_eq_leBytes, leBytes]; omega))
    (fun k hk => by rw [hget, hpad]; exact hrate k hk)
    (fun k hk => by rw [hget]; exact hcap k hk k.isLt) hk
  rw [hcellLen, ← this.2]
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · simpa [runV] using hw 0 (by simp [runV]; omega)
  · simpa [runV] using hw 1 (by simp [runV]; omega)

/-! ## `H_msg` -/

/-- The cells `H_msg`'s call `i` hashes, 84 bytes of them: `R`, `PK.seed`, `PK.root`, `M`'s two cells
and the counter's cell, `BE_32(i)` (`i · 2^24` for `i < 256`). -/
def hmsgCells (σ : Val) (i : Nat) : List E :=
  [σ sRand, σ sPP, σ sRoot, σ sM0, σ sM1, word (i * 2 ^ 24) 0]

/-- **`H_msg`'s two calls, sound**: the padding run, and each call's outputs the digest halves of
its 84 bytes. -/
theorem sDigests_sound (h : AtomsHold rd σ sDigests) :
    PadOK σ sPad ∧ (σ sHm0, σ sHm0b) = hcellLen (hmsgCells σ 0) 84 ∧
      σ sHm1 = (hcellLen (hmsgCells σ 1) 84).1 := by
  have c : ∀ (k : Nat) (w : E), Stmt.atom (.const (.n k) w) ∈ sDigests → σ (.n k) = w :=
    fun k w hm => h.atom hm
  have cp : ∀ (k : Nat) (v : V), Stmt.atom (.copy (.n k) v) ∈ sDigests → σ (.n k) = σ v :=
    fun k v hm => h.atom hm
  have p0 := c 12 (word 1 0) (by simp [sDigests, padRun, sPad, cst, List.range_succ])
  have p1 := c 13 (word 0 0) (by simp [sDigests, padRun, sPad, cst, List.range_succ])
  have p2 := c 14 (word 0 0) (by simp [sDigests, padRun, sPad, cst, List.range_succ])
  have p3 := c 15 (word 0 0) (by simp [sDigests, padRun, sPad, cst, List.range_succ])
  have p4 := c 16 (word 0 0) (by simp [sDigests, padRun, sPad, cst, List.range_succ])
  rw [word_zero] at p1 p2 p3 p4
  have hp : PadOK σ sPad := ⟨p0, p1, p2, p3, p4⟩
  have k0 := c 8 (word (2 ^ 32) 0) (by simp [sDigests, cst])
  have k1 := c 9 (word 0 0) (by simp [sDigests, cst])
  have k2 := c 10 (word 0 0) (by simp [sDigests, cst])
  have k3 := c 11 (word (2 ^ 63) 0) (by simp [sDigests, cst])
  have k4 := c 19 (word (2 ^ 24) 0) (by simp [sDigests, cst])
  have k5 := c 20 (word (2 ^ 32) 0) (by simp [sDigests, cst])
  have k6 := c 24 (word 0 0) (by simp [sDigests, cst])
  have k7 := c 25 (word 0 0) (by simp [sDigests, cst])
  have k8 := c 26 (word (2 ^ 63) 0) (by simp [sDigests, cst])
  have a32 : σ (.n 21) = σ (.n 19) + σ (.n 20) := h.atom (a := .add (.n 21) _ _) (by simp [sDigests, addS])
  have c7 := cp 7 sM1 (by simp [sDigests, copyS])
  have c33 := cp 22 sM1 (by simp [sDigests, copyS])
  have c34 := cp 23 (.n 21) (by simp [sDigests, copyS])
  have w1 : σ (.n 21) = word (1 * 2 ^ 24 + 2 ^ 32) 0 := by
    have e := word_ctr_pad (i := 1) (by norm_num)
    rw [one_mul] at e
    rw [a32, k4, k5, e, one_mul]
  rw [word_zero] at k1 k2 k6 k7
  refine ⟨hp, ?_, ?_⟩
  · obtain ⟨e1, e2⟩ := kec84_sound (ins := sHIns 7) (o := 17) (n := 2) (i := 0) (a := σ sRand)
      (b := σ sPP) (c := σ sRoot) (d := σ sM0) (e := σ sM1) (by norm_num)
      (h.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; simp [sDigests])
      (fun k hk => by interval_cases k <;> simp [sHIns, c7, k0, k1, k2, k3])
      (fun k h1 h2 => by interval_cases k <;> simp [sHIns, sPad, p1, p2, p3, p4])
    exact Prod.ext (e1 (by norm_num)) (e2 (by norm_num))
  · exact (kec84_sound (ins := sHIns 22) (o := 27) (n := 1) (i := 1) (a := σ sRand)
      (b := σ sPP) (c := σ sRoot) (d := σ sM0) (e := σ sM1) (by norm_num)
      (h.sub fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; simp [sDigests])
      (fun k hk => by interval_cases k <;> simp [sHIns, c33, c34, w1, k6, k7, k8])
      (fun k h1 h2 => by interval_cases k <;> simp [sHIns, sPad, p1, p2, p3, p4])).1 le_rfl

/-! ## The message -/

theorem word_eq128 {a b : Nat} (ha : a < 2 ^ 64) :
    word a b = eOfNat128 (a + 2 ^ 64 * b) := by
  unfold word eOfNat128
  rw [← ofBits_mod (a + 2 ^ 64 * b), show (a + 2 ^ 64 * b) % 2 ^ 64 = a by omega,
    show (a + 2 ^ 64 * b) / 2 ^ 64 = b by omega]

theorem pw_64 : word 0 1 = pw 64 := by simp [pw]

/-- **The message, sound**: the claim's keys and its message's two cells loaded. -/
theorem sMsg_sound (h : AtomsHold rd σ sMsg) :
    LoadHolds rd (σ (.n 0)) 0 (σ sPP) ∧ LoadHolds rd (σ (.n 0)) 1 (σ sRoot) ∧
      LoadHolds rd (σ (.n 0)) 2 (σ sM0) ∧ LoadHolds rd (σ (.n 0)) 3 (σ sM1) :=
  ⟨h.atom (a := .load _ _ _) (by simp [sMsg, loadS]), h.atom (a := .load _ _ _) (by simp [sMsg, loadS]),
    h.atom (a := .load _ _ _) (by simp [sMsg, loadS]), h.atom (a := .load _ _ _) (by simp [sMsg, loadS])⟩

/-! ## The check -/

theorem bitE_testBit (T k : Nat) : bitE (T.testBit k) = eOfNat (T / 2 ^ k % 2) := by
  rw [bitE_eq, Nat.toNat_testBit]

/-- The top leaf's low byte is the digest's byte 31. -/
theorem layerLeaf2_low (T : Nat) : layerLeafN T 2 % 2 ^ 8 = byteN T 31 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, testBit_layerLeafN, testBit_byteN]
  by_cases hj : j < 8
  · simp [hj, sLeafLen, sLeafOff, leafPos, show j < 10 by omega, show ¬ 16 + j < 8 by omega,
      show ¬ 16 + j < 16 by omega, show 16 + j < 24 by omega]
    congr 1; omega
  · simp [hj]

/-- The top leaf's two high bits are the digest's byte 30's low two. -/
theorem layerLeaf2_high (T : Nat) : layerLeafN T 2 >>> 8 = T / 2 ^ 240 % 2 ^ 2 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, testBit_layerLeafN, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 2
  · simp [hj, sLeafLen, sLeafOff, leafPos, show 8 + j < 10 by omega, show ¬ 16 + (8 + j) < 8 by omega,
      show ¬ 16 + (8 + j) < 16 by omega, show ¬ 16 + (8 + j) < 24 by omega]
    congr 1; omega
  · simp [hj, sLeafLen, show ¬ 8 + j < 10 by omega]

/-- The middle and bottom leaves are the second call's two low bytes. -/
theorem layerLeaf01 (T : Nat) : 2 ^ 8 * layerLeafN T 0 + layerLeafN T 1 = T / 2 ^ 256 % 2 ^ 16 := by
  have h1 : layerLeafN T 1 < 2 ^ 8 := by simpa [sLeafLen] using layerLeafN_lt T 1
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 8
  · simp only [hj, ↓reduceIte, testBit_layerLeafN]
    simp [sLeafLen, sLeafOff, leafPos, hj, show j < 16 by omega, show ¬ 8 + j < 8 by omega,
      show 8 + j < 16 by omega]
    congr 1; omega
  · simp only [hj, ↓reduceIte, testBit_layerLeafN]
    by_cases hj16 : j < 16
    · simp [sLeafLen, sLeafOff, leafPos, hj16, show j - 8 < 8 by omega]
      congr 1; omega
    · simp [sLeafLen, hj16, show ¬ j - 8 < 8 by omega]

theorem word_y_inv' : word 2 1 = y⁻¹ := by rw [y_inv]; rfl

/-- **The second call's low bytes**: its cell, the bytes `l` and the unused bytes `N` times `g^16`
checked into `K` after `y⁻¹`. -/
theorem high_low_bytes {x : E} {l N : Nat} (hl : l < 2 ^ 16)
    (hK : IsInK ((x + eOfNat l + eOfNat (2 ^ 16 * N)) * word 2 1)) : cellNat x % 2 ^ 16 = l := by
  rw [word_y_inv', eq_ofLimbs x, eOfNat_eq_ofLimbs, eOfNat_eq_ofLimbs, ofLimbs_add, ofLimbs_add,
    ofLimbs_mul_y_inv, isInK_ofLimbs_iff] at hK
  have h0 : x.limb 0 = K.ofBits l + K.ofBits (2 ^ 16 * N) := by
    rw [add_assoc] at hK
    exact (add_eq_zero_iff_eq_neg.mp hK).trans (CharTwo.neg_eq _)
  rw [cellNat, h0, ← ofBits_xor, Nat.xor_comm, two_pow_mul_xor hl, kToNat_ofBits]
  omega

/-- The tree index's high byte's six unused bits, folded most significant first. -/
def padV (b : Nat) : V := if b = 0 then .n 275 else .n (1280 + 3 * (b - 1) + 2)

theorem sPadBits_sound {T : Nat} (hb : BitsAt σ T) (h : AtomsHold rd σ sPadBits) :
    ∀ b ≤ 5, σ (padV b) = eOfNat (T / 2 ^ (247 - b) % 2 ^ (b + 1))
  | 0, _ => by
      rw [show padV 0 = .n (28 + 247) from rfl, hb 247 (by norm_num), bitE_testBit]
      norm_num
  | b + 1, hb5 => by
      have ih := sPadBits_sound hb h b (by omega)
      have mem : ∀ x ∈ [cst (1280 + 3 * b) (word 2 0),
          mulS (.n (1280 + 3 * b + 1)) (.n (if b = 0 then 275 else 1280 + 3 * b - 1)) (.n (1280 + 3 * b)),
          addS (.n (1280 + 3 * b + 2)) (.n (274 - b)) (.n (1280 + 3 * b + 1))], x ∈ sPadBits := fun x hx =>
        List.mem_flatMap.mpr ⟨b, List.mem_range.mpr (by omega), hx⟩
      have k : σ (.n (1280 + 3 * b)) = word 2 0 := h.atom (a := .const _ _) (mem _ (by simp [cst]))
      have m : σ (.n (1280 + 3 * b + 1)) = σ (padV b) * σ (.n (1280 + 3 * b)) := by
        have := h.atom (a := .mul _ _ _) (mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        rw [this]
        congr 2
        unfold padV
        split_ifs <;> first | rfl | (congr 1; omega)
      have a : σ (.n (1280 + 3 * b + 2)) = σ (.n (274 - b)) + σ (.n (1280 + 3 * b + 1)) :=
        h.atom (a := .add _ _ _) (mem _ (by simp [addS]))
      have hP : T / 2 ^ (247 - b) % 2 ^ (b + 1) < 2 ^ 6 :=
        lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [show padV (b + 1) = .n (1280 + 3 * b + 2) by simp [padV], a, m, k, ih, word_two, mul_comm,
        Value.gen_mul_eOfNat (by omega), show 274 - b = 28 + (246 - b) by omega, hb _ (by omega),
        bitE_testBit, add_comm, show 2 * (T / 2 ^ (247 - b) % 2 ^ (b + 1)) =
          2 ^ 1 * (T / 2 ^ (247 - b) % 2 ^ (b + 1)) by ring,
        Value.eOfNat_add_of_lt (s := 1) (r := T / 2 ^ (246 - b) % 2) (by omega)]
      congr 1
      rw [show 247 - (b + 1) = 246 - b by omega, show b + 1 + 1 = 1 + (b + 1) by ring,
        mod_split (T / 2 ^ (246 - b)) 1 (b + 1), Nat.div_div_eq_div_mul, ← pow_add,
        show 246 - b + 1 = 247 - b by omega, pow_one]

theorem lval_at {T : Nat} (hl : LValsAt σ T) {l z i : Nat} (hl3 : l < 3) (hz : z < sLeafLen l)
    (hi : i = 8 * l + z) : σ (sLVal i) = eOfNat (layerLeafN T l >>> z) := by
  subst hi; exact hl l hl3 z hz

/-- The check's statements before `d0[0] = md0`: the tree's middle byte, the unused bits. -/
def sCheckA : List Stmt :=
  [cst 1277 (word 256 0), mulS (.n 1278) (sLVal 24) (.n 1277), addS sTreeMid (sLVal 16) (.n 1278)] ++
    sPadBits

/-- `d0[0] = md0 + corr0` and `md1 + corr1` (`G:4210-4211`): the places `vals` carries taken out. -/
def sCheckCorr : List Stmt :=
  [cst 1295 corr0W, addS sHm0 sMd0.2.2 (.n 1295), cst 1296 corr1W, addS (.n 1297) sMd1.2.2 (.n 1296)]

/-- Between `d0[0] = md0 + corr0` and `d0[1] = …`: the tree index's two high bytes placed. -/
def sCheckB : List Stmt :=
  [cst 1298 (word 4 0), mulS (.n 1299) (.n 1294) (.n 1298), addS (.n 1300) (sLVal 24) (.n 1299),
    cst 1301 (pw 112), mulS (.n 1302) (.n 1300) (.n 1301), addS (.n 1303) (.n 1297) (.n 1302),
    cst 1304 (pw 120), mulS (.n 1305) sTreeMid (.n 1304)]

/-- After the unused bytes: the second call's high lane. -/
def sCheckC : List Stmt :=
  [addS (.n 1363) sHm1 (sLVal 8), cst 1364 (word 256 0), mulS (.n 1365) (sLVal 0) (.n 1364),
    addS (.n 1366) (.n 1363) (.n 1365), cst 1367 (word 65536 0),
    mulS (.n 1368) sUnused.2.2 (.n 1367), addS (.n 1369) (.n 1366) (.n 1368),
    cst 1370 (word 2 1), mulS (.n 1371) (.n 1369) (.n 1370)]

theorem sCheck_split : sCheck = sCheckA ++ sCheckCorr ++ sCheckB ++
    [addS sHm0b (.n 1303) (.n 1305), hintW "sp_unused" (runV 1306 6)] ++ sUnused.1 ++ sCheckC ++
    [.atom (.assertInK (.n 1371) sUnused.2.2)] := by
  simp [sCheck, sCheckA, sCheckCorr, sCheckB, sCheckC]

theorem lval_16 {T : Nat} (hl : LValsAt σ T) : σ (sLVal 16) = eOfNat (layerLeafN T 2) := by
  simpa using lval_at hl (l := 2) (z := 0) (by norm_num) (by simp [sLeafLen]) rfl

theorem lval_24 {T : Nat} (hl : LValsAt σ T) : σ (sLVal 24) = eOfNat (layerLeafN T 2 >>> 8) :=
  lval_at hl (l := 2) (z := 8) (by norm_num) (by simp [sLeafLen]) rfl

theorem lval_8 {T : Nat} (hl : LValsAt σ T) : σ (sLVal 8) = eOfNat (layerLeafN T 1) := by
  simpa using lval_at hl (l := 1) (z := 0) (by norm_num) (by simp [sLeafLen]) rfl

theorem lval_0 {T : Nat} (hl : LValsAt σ T) : σ (sLVal 0) = eOfNat (layerLeafN T 0) := by
  simpa using lval_at hl (l := 0) (z := 0) (by norm_num) (by simp [sLeafLen]) rfl

/-- **The tree's middle byte and the unused bits.** -/
theorem sCheckA_sound {T : Nat} (hb : BitsAt σ T) (hl : LValsAt σ T) (h : AtomsHold rd σ sCheckA) :
    σ sTreeMid = eOfNat (byteN T 31) ∧ σ (.n 1294) = eOfNat (T / 2 ^ 242 % 2 ^ 6) := by
  have hA := h.left
  have hL2 : layerLeafN T 2 < 2 ^ 10 := by simpa [sLeafLen] using layerLeafN_lt T 2
  refine ⟨?_, ?_⟩
  · have k : σ (.n 1277) = word 256 0 := hA.atom (a := .const _ _) (by simp [cst])
    have m : σ (.n 1278) = σ (sLVal 24) * σ (.n 1277) := hA.atom (a := .mul _ _ _) (by simp [mulS])
    have a : σ sTreeMid = σ (sLVal 16) + σ (.n 1278) := hA.atom (a := .add sTreeMid _ _) (by simp [addS])
    rw [a, m, k, lval_16 hl, lval_24 hl, word_eq_eOfNat, show (256 : Nat) = 2 ^ 8 by norm_num, mul_comm,
      Value.eOfNat_two_pow_mul (by rw [Nat.shiftRight_eq_div_pow]; omega), eOfNat_low, layerLeaf2_low]
  · have pad := sPadBits_sound hb h.right 5 le_rfl
    rw [show padV 5 = .n 1294 from rfl] at pad
    simpa using pad

/-- **The tree index's two high bytes placed**: with `md1`, the first call's second cell. -/
theorem sCheckB_sound {T : Nat} (hl : LValsAt σ T) (tm : σ sTreeMid = eOfNat (byteN T 31))
    (pad : σ (.n 1294) = eOfNat (T / 2 ^ 242 % 2 ^ 6))
    (h1 : σ (.n 1297) = eOfNat128 (T / 2 ^ 128 % 2 ^ 112)) (hB : AtomsHold rd σ sCheckB) :
    σ (.n 1303) + σ (.n 1305) = eOfNat128 (T / 2 ^ 128 % 2 ^ 128) := by
  have k6 : σ (.n 1298) = word 4 0 := hB.atom (a := .const _ _) (by simp [sCheckB, cst])
  have m7 : σ (.n 1299) = σ (.n 1294) * σ (.n 1298) := hB.atom (a := .mul _ _ _) (by simp [sCheckB, mulS])
  have a8 : σ (.n 1300) = σ (sLVal 24) + σ (.n 1299) := hB.atom (a := .add _ _ _) (by simp [sCheckB, addS])
  have k9 : σ (.n 1301) = pw 112 := hB.atom (a := .const _ _) (by simp [sCheckB, cst])
  have m0 : σ (.n 1302) = σ (.n 1300) * σ (.n 1301) := hB.atom (a := .mul _ _ _) (by simp [sCheckB, mulS])
  have a1 : σ (.n 1303) = σ (.n 1297) + σ (.n 1302) := hB.atom (a := .add _ _ _) (by simp [sCheckB, addS])
  have k2 : σ (.n 1304) = pw 120 := hB.atom (a := .const _ _) (by simp [sCheckB, cst])
  have m3 : σ (.n 1305) = σ sTreeMid * σ (.n 1304) := hB.atom (a := .mul _ _ _) (by simp [sCheckB, mulS])
  have b30 : σ (.n 1300) = eOfNat (byteN T 30) := by
    rw [a8, m7, k6, pad, lval_24 hl, layerLeaf2_high, word_eq_eOfNat, show (4 : Nat) = 2 ^ 2 by norm_num,
      mul_comm, Value.eOfNat_two_pow_mul (by omega), add_comm,
      Value.eOfNat_add_of_lt (Nat.mod_lt _ (by norm_num))]
    congr 1
    unfold byteN
    have e : T / 2 ^ 242 = T / 2 ^ 240 / 4 := by rw [Nat.div_div_eq_div_mul]; norm_num
    rw [e, show 8 * 30 = 240 by norm_num]
    generalize T / 2 ^ 240 = X
    omega
  have e41 : σ (.n 1303) = eOfNat128 (T / 2 ^ 128 % 2 ^ 120) := by
    rw [a1, m0, b30, k9, h1, pw_mul (by norm_num) (by have := byteN_lt T 30; norm_num; omega),
      eOfNat128_add_shift (Nat.mod_lt _ (by positivity)), show (120 : Nat) = 112 + 8 by norm_num,
      mod_split (T / 2 ^ 128) 112 8, Nat.div_div_eq_div_mul, ← pow_add, byteN, Nat.add_comm]
  rw [e41, m3, k2, tm, pw_mul (by norm_num) (by have := byteN_lt T 31; norm_num; omega),
    eOfNat128_add_shift (Nat.mod_lt _ (by positivity)), show (128 : Nat) = 120 + 8 by norm_num,
    mod_split (T / 2 ^ (120 + 8)) 120 8, Nat.div_div_eq_div_mul, ← pow_add, byteN, Nat.add_comm]

/-- **The second call's high lane**: its cell, the leaves' bytes and the unused bytes `N`, times
`y⁻¹`. -/
theorem sCheckC_sound {T N : Nat} (hl : LValsAt σ T) (hN : σ sUnused.2.2 = eOfNat N) (hN48 : N < 2 ^ 48)
    (hC : AtomsHold rd σ sCheckC) :
    σ (.n 1371) = (σ sHm1 + eOfNat (T / 2 ^ 256 % 2 ^ 16) + eOfNat (2 ^ 16 * N)) * word 2 1 := by
  have hL1 : layerLeafN T 1 < 2 ^ 8 := by simpa [sLeafLen] using layerLeafN_lt T 1
  have hL0 : layerLeafN T 0 < 2 ^ 8 := by simpa [sLeafLen] using layerLeafN_lt T 0
  have a01 : σ (.n 1363) = σ sHm1 + σ (sLVal 8) := hC.atom (a := .add _ _ _) (by simp [sCheckC, addS])
  have k02 : σ (.n 1364) = word 256 0 := hC.atom (a := .const _ _) (by simp [sCheckC, cst])
  have m03 : σ (.n 1365) = σ (sLVal 0) * σ (.n 1364) := hC.atom (a := .mul _ _ _) (by simp [sCheckC, mulS])
  have a04 : σ (.n 1366) = σ (.n 1363) + σ (.n 1365) := hC.atom (a := .add _ _ _) (by simp [sCheckC, addS])
  have k05 : σ (.n 1367) = word 65536 0 := hC.atom (a := .const _ _) (by simp [sCheckC, cst])
  have m06 : σ (.n 1368) = σ sUnused.2.2 * σ (.n 1367) := hC.atom (a := .mul _ _ _) (by simp [sCheckC, mulS])
  have a07 : σ (.n 1369) = σ (.n 1366) + σ (.n 1368) := hC.atom (a := .add _ _ _) (by simp [sCheckC, addS])
  have k08 : σ (.n 1370) = word 2 1 := hC.atom (a := .const _ _) (by simp [sCheckC, cst])
  have m09 : σ (.n 1371) = σ (.n 1369) * σ (.n 1370) := hC.atom (a := .mul _ _ _) (by simp [sCheckC, mulS])
  rw [m09, k08, a07, m06, k05, a04, m03, k02, a01, lval_8 hl, lval_0 hl, hN, word_eq_eOfNat, word_eq_eOfNat,
    show (256 : Nat) = 2 ^ 8 by norm_num, show (65536 : Nat) = 2 ^ 16 by norm_num,
    mul_comm (eOfNat (layerLeafN T 0)), Value.eOfNat_two_pow_mul (by omega), mul_comm (eOfNat N),
    Value.eOfNat_two_pow_mul (by omega), add_assoc (σ sHm1), add_comm (eOfNat (layerLeafN T 1)),
    Value.eOfNat_add_of_lt hL1, layerLeaf01]
  rfl

/-- **The check, sound**: the first call's cells are the digest's bytes `0 … 31` the bits spell,
the second call's low two bytes its bytes `32`, `33`. -/
theorem sCheck_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} (hbb : ByteBits L.read (σ (.n 1)))
    {T : Nat} (hb : BitsAt σ T) (hl : LValsAt σ T) (h0 : σ sMd0.2.2 + corr0W = eOfNat128 (T % 2 ^ 128))
    (h1 : σ sMd1.2.2 + corr1W = eOfNat128 (T / 2 ^ 128 % 2 ^ 112)) (h : AtomsHold L.read σ sCheck) :
    σ sTreeMid = eOfNat (byteN T 31) ∧ σ sHm0 = eOfNat128 (T % 2 ^ 128) ∧
      σ sHm0b = eOfNat128 (T / 2 ^ 128 % 2 ^ 128) ∧ cellNat (σ sHm1) % 2 ^ 16 = T / 2 ^ 256 % 2 ^ 16 := by
  rw [sCheck_split] at h
  have hK := h.right
  have hC := h.left.right
  have hU := h.left.left.right
  have hD := h.left.left.left.right
  have hB := h.left.left.left.left.right
  have hc := h.left.left.left.left.left.right
  have hA := h.left.left.left.left.left.left
  obtain ⟨tm, pad⟩ := sCheckA_sound hb hl hA
  refine ⟨tm, ?_, ?_, ?_⟩
  · have k : σ (.n 1295) = corr0W := hc.atom (a := .const _ _) (by simp [sCheckCorr, cst])
    have a : σ sHm0 = σ sMd0.2.2 + σ (.n 1295) := hc.atom (a := .add sHm0 _ _) (by simp [sCheckCorr, addS])
    rw [a, k, h0]
  · have k : σ (.n 1296) = corr1W := hc.atom (a := .const _ _) (by simp [sCheckCorr, cst])
    have a : σ (.n 1297) = σ sMd1.2.2 + σ (.n 1296) :=
      hc.atom (a := .add (.n 1297) _ _) (by simp [sCheckCorr, addS])
    have a4 : σ sHm0b = σ (.n 1303) + σ (.n 1305) := hD.atom (a := .add sHm0b _ _) (by simp [addS])
    rw [a4, sCheckB_sound hl tm pad (by rw [a, k, h1]) hB]
  · obtain ⟨N, hN, hNlt⟩ := sFromMarks_sound hκ hbb (b := 1306) (n := 6) (x := 1312) (by norm_num)
      (by norm_num) hU
    have hk : IsInK (σ (.n 1371)) := (hK.atom (a := .assertInK (.n 1371) sUnused.2.2) (by simp)).1
    rw [sCheckC_sound hl hN (by simpa using hNlt) hC] at hk
    exact high_low_bytes (Nat.mod_lt _ (by norm_num)) hk

/-! ## The block -/

/-- **What the digest block gives**: the digest's number `T` (`< 2^272`) whose bits the bit run
holds, every FORS leaf and layer leaf with their shifts, and the tree index's middle byte. -/
def DigestAt (σ : Val) (T : Nat) : Prop :=
  T < 2 ^ 272 ∧ BitsAt σ T ∧ FValsAt σ T ∧ LValsAt σ T ∧ σ sTreeMid = eOfNat (byteN T 31)

theorem DigestAt.mdBit {T : Nat} (h : DigestAt σ T) {p : Nat} (hp : p < 240) :
    σ (sMdBit p) = bitE (T.testBit (mdPos p)) := by
  rw [sMdBit_eq]; exact h.2.1 _ (by have := mdPos_lt hp; omega)

theorem DigestAt.leafBit {T : Nat} (h : DigestAt σ T) {b : Nat} (hb : b < 26) :
    σ (sLeafBit b) = bitE (T.testBit (leafPos b)) := by
  rw [sLeafBit_eq hb]; exact h.2.1 _ (leafPos_lt hb)

/-- The bytes `H_msg`'s call `i` hashes: `R | PK.seed | PK.root | M | BE_32(i)`, `M` the message
(its number), little endian, 84 bytes. -/
def hmsgBytes (R seed root : E) (M i : Nat) : List UInt8 :=
  cellBytes R ++ cellBytes seed ++ cellBytes root ++ leBytes M 32 ++ [0, 0, 0, UInt8.ofNat i]

/-- The digest's number from `H_msg`'s two calls: the first call's two cells and the second call's
low two bytes. -/
def hmsgNat (d0 d1 : E × E) : Nat := cellNat d0.1 + 2 ^ 128 * cellNat d0.2 + 2 ^ 256 * (cellNat d1.1 % 2 ^ 16)

/-- The message's number of its two cells. -/
def msgNat (c d : E) : Nat := cellNat c + 2 ^ 128 * cellNat d

theorem cells2_bytes (c d : E) : cellBytes c ++ cellBytes d = leBytes (msgNat c d) 32 := by
  rw [cellBytes_eq_leBytes, cellBytes_eq_leBytes, msgNat, show (32 : Nat) = 16 + 16 from rfl,
    show (2 : Nat) ^ 128 = 256 ^ 16 by norm_num,
    leBytes_add_mul _ _ _ _ (by have := cellNat_lt c; norm_num at this ⊢; omega)]

theorem ctr_bytes {i : Nat} (hi : i < 256) :
    (cellBytes (word (i * 2 ^ 24) 0)).take 4 = [0, 0, 0, UInt8.ofNat i] := by
  rw [cellBytes_eq_leBytes, word_eq_eOfNat, cellNat_eOfNat (by omega), ← leBytes_append _ 4 12,
    List.take_left' (by simp)]
  apply List.ext_getElem (by simp)
  intro n h1 h2
  rw [getElem_leBytes]
  have hn : n < 4 := by simpa using h1
  apply UInt8.toNat_inj.mp
  interval_cases n <;> simp <;> omega

theorem hmsg_take {R s r c d : E} {i : Nat} (hi : i < 256) :
    (cellsBytes [R, s, r, c, d, word (i * 2 ^ 24) 0]).take 84 = hmsgBytes R s r (msgNat c d) i := by
  have e : cellsBytes [R, s, r, c, d, word (i * 2 ^ 24) 0] =
      (cellBytes R ++ cellBytes s ++ cellBytes r ++ leBytes (msgNat c d) 32) ++
        cellBytes (word (i * 2 ^ 24) 0) := by
    rw [← cells2_bytes]; simp [cellsBytes]
  have hl : (cellBytes R ++ cellBytes s ++ cellBytes r ++ leBytes (msgNat c d) 32).length = 80 := by
    simp [cellBytes_eq_leBytes, leBytes]
  rw [e, show 84 = 80 + 4 from rfl, ← hl, List.take_length_add_append, hmsgBytes, ctr_bytes hi]

/-- **The message digest's block, sound**: the padding run; the claim's keys and message cells
loaded; and a number `T` whose bits and fields the block holds, `T` the digest `H_msg`'s two calls
give on `R | PK.seed | PK.root | M | BE_32(i)`. -/
theorem sDigestBlock_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ}
    (hbb : ByteBits L.read (σ (.n 1))) (h : AtomsHold L.read σ sDigestBlock) :
    PadOK σ sPad ∧ LoadHolds L.read (σ (.n 0)) 0 (σ sPP) ∧ LoadHolds L.read (σ (.n 0)) 1 (σ sRoot) ∧
      LoadHolds L.read (σ (.n 0)) 2 (σ sM0) ∧ LoadHolds L.read (σ (.n 0)) 3 (σ sM1) ∧
        ∃ T, DigestAt σ T ∧
          T = hmsgNat (digestHalves (keccak256 (hmsgBytes (σ sRand) (σ sPP) (σ sRoot)
              (msgNat (σ sM0) (σ sM1)) 0)))
            (digestHalves (keccak256 (hmsgBytes (σ sRand) (σ sPP) (σ sRoot)
              (msgNat (σ sM0) (σ sM1)) 1))) := by
  have hCk : AtomsHold L.read σ sCheck := h.right
  have hMd : AtomsHold L.read σ sMdBytes := h.left.right
  have hLs : AtomsHold L.read σ sLeafShifts := h.left.left.right
  have hFs : AtomsHold L.read σ sForsFields := h.left.left.left.right
  have hBo : AtomsHold L.read σ sBooleans := h.left.left.left.left.right
  have hDg : AtomsHold L.read σ sDigests := h.left.left.left.left.left.left.right
  have hMs : AtomsHold L.read σ sMsg := h.left.left.left.left.left.left.left
  obtain ⟨hp, d0, d1⟩ := sDigests_sound hDg
  obtain ⟨lP, lR, l2, l3⟩ := sMsg_sound hMs
  set T := bitsOf σ 28 272 with hTdef
  have hT : T < 2 ^ 272 := bitsOf_lt' σ
  have hb := sBooleans_bitsAt hBo
  have hv := sForsFields_sound hb hFs
  have hl := sLeafShifts_sound hb hLs
  have m0 := sMd0_sound hv (hMd.left.left) hMd.left.right
  have m1 := sMd1_sound hv hMd.right
  obtain ⟨tm, c0, c1, c2⟩ := sCheck_sound hκ hbb hb hl m0 m1 hCk
  refine ⟨hp, lP, lR, l2, l3, T, ⟨hT, hb, hv, hl, tm⟩, ?_⟩
  rw [hcellLen, hmsgCells, hmsg_take (by norm_num)] at d0
  rw [hcellLen, hmsgCells, hmsg_take (by norm_num)] at d1
  rw [← d0, hmsgNat]
  dsimp only
  rw [← d1]
  rw [c0, c1, cellNat_eOfNat128 (Nat.mod_lt _ (by norm_num)), cellNat_eOfNat128 (Nat.mod_lt _ (by norm_num)),
    c2]
  omega

/-! ## The statement's message digest -/

/-- **`H_msg`'s input is `hmsgBytes`**: `R | PK.seed | PK.root | M | BE_32(i)` of cells and a
message. -/
theorem hmsgBytes_eq (R seed root : E) (msg : HashSig.Message) (call : Sphincs.DigestCall) :
    HashSig.littleEndianBytes 16 (cellVal R) ++ HashSig.littleEndianBytes 16 (cellVal seed) ++
        HashSig.littleEndianBytes 16 (cellVal root) ++ HashSig.littleEndianBytes 32 msg ++
        Sphincs.bigEndianBytes 4 (BitVec.ofNat 32 call.val) =
      hmsgBytes R seed root msg.toNat call.val := by
  have hbe : Sphincs.bigEndianBytes 4 (BitVec.ofNat 32 call.val) = [0, 0, 0, UInt8.ofNat call.val] := by
    fin_cases call <;> decide
  rw [bytesLE_cellVal, bytesLE_cellVal, bytesLE_cellVal, hmsgBytes, hbe, bytesLE_eq]

/-- **The statement's message digest, from cells**: `H_msg` of the randomizer, the key and the
message is the number `hmsgNat` of `H_msg`'s two calls on `hmsgBytes`. -/
theorem hmsgDigest_cells (R seed root : E) (msg : HashSig.Message) :
    Id.run (Sphincs.Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600
        ⟨cellVal seed, cellVal root⟩ (cellVal R) msg) =
      BitVec.ofNat (8 * Sphincs.digestByteCount)
        (hmsgNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 0)))
          (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 1)))) := by
  simp only [Sphincs.Verification.messageDigest, Sphincs.Verification.messageDigestCall,
    keccakHash_keccakF1600, Id.run, bind, pure, sequenceFin_id]
  rw [Sphincs.truncateMessageDigest]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Sphincs.digestValue]
  have k : ∀ c : Sphincs.DigestCall, (Node.keccakBits
      (HashSig.littleEndianBytes 16 (cellVal R) ++ HashSig.littleEndianBytes 16 (cellVal seed) ++
        HashSig.littleEndianBytes 16 (cellVal root) ++ HashSig.littleEndianBytes 32 msg ++
        Sphincs.bigEndianBytes 4 (BitVec.ofNat 32 c.val))).toNat =
      cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat c.val))).1 +
        2 ^ 128 * cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat c.val))).2 :=
    fun c => by rw [hmsgBytes_eq, keccakBits_toNat]
  simp only [k]
  rw [Fin.sum_univ_eq_sum_range (fun c => (cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat c))).1 +
      2 ^ 128 * cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat c))).2) * 2 ^ (256 * c))
      Sphincs.digestCallCount, show Sphincs.digestCallCount = 2 from rfl, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, hmsgNat]
  generalize hN : 8 * Sphincs.digestByteCount = N
  have h2N : 2 ^ N = 2 ^ 256 * 2 ^ 16 := by
    rw [← hN, ← pow_add]
    exact congrArg (fun x => 2 ^ x) (show 8 * Sphincs.digestByteCount = 256 + 16 from rfl)
  rw [h2N]
  have a0 := cellNat_lt (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 0))).1
  have b0 := cellNat_lt (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 0))).2
  generalize cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 0))).1 = A0 at *
  generalize cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 0))).2 = B0 at *
  generalize cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 1))).1 = A1
  generalize cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 1))).2 = B1
  simp only [Nat.mul_zero, pow_zero, mul_one, zero_add]
  omega

/-! ## Algorithm 19: the digest's fields -/

/-- The statement's message digest of the number `T`. -/
abbrev digestOf (T : Nat) : Sphincs.MessageDigest := BitVec.ofNat (8 * Sphincs.digestByteCount) T

theorem two_pow_digestBits : 2 ^ (8 * Sphincs.digestByteCount) = 2 ^ 272 :=
  congrArg (fun x => 2 ^ x) (show 8 * Sphincs.digestByteCount = 272 from rfl)

theorem digestOf_toNat {T : Nat} (hT : T < 2 ^ 272) : (digestOf T).toNat = T := by
  rw [BitVec.toNat_ofNat, two_pow_digestBits, Nat.mod_eq_of_lt hT]

/-- **The statement's byte `p` is `T`'s.** -/
theorem messageDigestByte_eq {T p : Nat} (hT : T < 2 ^ 272) :
    Sphincs.messageDigestByte (digestOf T) p = byteN T p := by
  rw [Sphincs.messageDigestByte, BitVec.extractLsb'_toNat, digestOf_toNat hT, Nat.shiftRight_eq_div_pow,
    byteN]

/-- **The statement's bit `p`, most significant first, is `T`'s bit `mdPos p`.** -/
theorem messageDigestBit_eq {T p : Nat} (hT : T < 2 ^ 272) :
    Sphincs.messageDigestBit (digestOf T) p = (T.testBit (mdPos p)).toNat := by
  rw [Sphincs.messageDigestBit, messageDigestByte_eq hT, ← Nat.toNat_testBit, mdPos, testBit_byteN]
  simp [show 7 - p % 8 < 8 by omega]

/-- **The statement's FORS leaves are `forsLeafN`** (`base_2b`, Algorithm 19). -/
theorem digestForsLeaves_val {T : Nat} (hT : T < 2 ^ 272) (c : Sphincs.ForsTreeIndex) :
    (Sphincs.digestForsLeaves (digestOf T) c).val = forsLeafN T c.val := by
  have hc := c.isLt
  have hb : ∀ j < 10, Sphincs.messageDigestBit (digestOf T) (10 * c.val + j) =
      (T.testBit (mdPos (10 * c.val + j))).toNat := fun j _ => messageDigestBit_eq hT
  have hl := forsLeafN_lt T c.val
  simp only [Sphincs.digestForsLeaves, Sphincs.forsLeafOfNat, Sphincs.forsTreeHeight]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rw [hb 0 (by norm_num), hb 1 (by norm_num), hb 2 (by norm_num), hb 3 (by norm_num), hb 4 (by norm_num),
    hb 5 (by norm_num), hb 6 (by norm_num), hb 7 (by norm_num), hb 8 (by norm_num), hb 9 (by norm_num)]
  simp only [forsLeafN, bitsVal, Nat.add_zero] at hl ⊢
  simp (disch := omega) only [Nat.add_sub_assoc, Nat.reduceSub, Nat.add_zero] at hl ⊢
  norm_num at hl ⊢
  omega

/-- The index `idx` the digest picks: its layers' leaves, bottom first, eight bits each below the
top's ten. -/
def indexN (T : Nat) : Nat := layerLeafN T 0 + 2 ^ 8 * layerLeafN T 1 + 2 ^ 16 * layerLeafN T 2

theorem layerLeafN_bytes {T : Nat} :
    layerLeafN T 0 = byteN T 33 ∧ layerLeafN T 1 = byteN T 32 ∧
      layerLeafN T 2 = byteN T 31 + 2 ^ 8 * (byteN T 30 % 4) := by
  have h01 := layerLeaf01 T
  have hlo := layerLeaf2_low T
  have hhi := layerLeaf2_high T
  have l0 : layerLeafN T 0 < 2 ^ 8 := by simpa [sLeafLen] using layerLeafN_lt T 0
  have l1 : layerLeafN T 1 < 2 ^ 8 := by simpa [sLeafLen] using layerLeafN_lt T 1
  have l2 : layerLeafN T 2 < 2 ^ 10 := by simpa [sLeafLen] using layerLeafN_lt T 2
  have e33 : byteN T 33 = T / 2 ^ 256 / 2 ^ 8 % 2 ^ 8 := by
    rw [byteN, Nat.div_div_eq_div_mul, ← pow_add]
  have e31 : byteN T 30 % 4 = T / 2 ^ 240 % 2 ^ 2 := by
    rw [byteN, Nat.mod_mod_of_dvd _ (by norm_num)]; norm_num
  rw [Nat.shiftRight_eq_div_pow] at hhi
  refine ⟨?_, ?_, ?_⟩
  · rw [e33]; omega
  · rw [byteN, show 8 * 32 = 256 by norm_num]; omega
  · omega

/-- **The statement's index is `indexN`** (Algorithm 19: the tree index cut to 18 bits, then the
bottom leaf). -/
theorem digestIndex_val {T : Nat} (hT : T < 2 ^ 272) : (Sphincs.digestIndex (digestOf T)).val = indexN T := by
  obtain ⟨e0, e1, e2⟩ := layerLeafN_bytes (T := T)
  have b30 := byteN_lt T 30
  have b31 := byteN_lt T 31
  have b32 := byteN_lt T 32
  have b33 := byteN_lt T 33
  simp only [Sphincs.digestIndex, Sphincs.messageDigestBigEndian, Sphincs.forsMessageByteCount,
    Sphincs.treeIndexByteCount, Sphincs.leafIndexByteCount, List.range_succ, List.range_zero,
    List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, messageDigestByte_eq hT, indexN,
    e0, e1, e2]
  norm_num at b30 b31 b32 b33 ⊢
  omega

/-- Layer `l`'s tree of the index: the leaves of the layers above it. -/
def layerTreeN (T l : Nat) : Nat :=
  if l = 0 then layerLeafN T 1 + 2 ^ 8 * layerLeafN T 2 else if l = 1 then layerLeafN T 2 else 0

theorem layerLeafN_lt' (T : Nat) : layerLeafN T 0 < 2 ^ 8 ∧ layerLeafN T 1 < 2 ^ 8 ∧ layerLeafN T 2 < 2 ^ 10 :=
  ⟨by simpa [sLeafLen] using layerLeafN_lt T 0, by simpa [sLeafLen] using layerLeafN_lt T 1,
    by simpa [sLeafLen] using layerLeafN_lt T 2⟩

/-- **Each layer's leaf of the digest's index** is the layer's leaf the digest holds. -/
theorem leafOfIndex_digest {T : Nat} (hT : T < 2 ^ 272) (l : Sphincs.Layer) :
    (Sphincs.leafOfIndex l (Sphincs.digestIndex (digestOf T))).val = layerLeafN T l.val := by
  obtain ⟨h0, h1, h2⟩ := layerLeafN_lt' T
  rw [Sphincs.leafOfIndex]
  simp only [digestIndex_val hT, indexN, Sphincs.bitsBelowLayer, Sphincs.layerHeight]
  fin_cases l <;> simp <;> omega

/-- **Each layer's tree of the digest's index.** -/
theorem treeOfIndex_digest {T : Nat} (hT : T < 2 ^ 272) (l : Sphincs.Layer) :
    (Sphincs.treeOfIndex l (Sphincs.digestIndex (digestOf T))).val = layerTreeN T l.val := by
  obtain ⟨h0, h1, h2⟩ := layerLeafN_lt' T
  rw [Sphincs.treeOfIndex]
  simp only [digestIndex_val hT, indexN, Sphincs.bitsBelowLayer, Sphincs.layerHeight, layerTreeN]
  fin_cases l <;> simp <;> omega

/-! ## The block, against the statement -/

theorem cellPairVal_toNat (lo hi : E) : (cellPairVal lo hi).toNat = cellNat lo + 2 ^ 128 * cellNat hi := by
  rw [cellPairVal, BitVec.toNat_append, toNat_cellVal, toNat_cellVal, Nat.shiftLeft_eq, mul_comm,
    two_pow_mul_or (cellNat_lt lo), add_comm]

/-- **The message digest's block, sound, against the statement**: the padding run; the four words at
the claim pointer are the claim of `PK.seed`, `PK.root` and the message's two cells; and the
statement's `H_msg` of the claim and the randomizer is `digestOf T` for a `T` whose bits and fields
the block holds. -/
theorem sDigestBlock_sound_stmt {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ}
    (hbb : ByteBits L.read (σ (.n 1))) (h : AtomsHold L.read σ sDigestBlock) :
    PadOK σ sPad ∧ ∃ c d, ClaimAt L.read (σ (.n 0)) (σ sPP) (σ sRoot) c d ∧ ∃ T, DigestAt σ T ∧
        Id.run (Sphincs.Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600
          (sphincsClaimOf (σ sPP) (σ sRoot) c d).1 (cellVal (σ sRand))
          (sphincsClaimOf (σ sPP) (σ sRoot) c d).2) = digestOf T := by
  obtain ⟨hp, lP, lR, l2, l3, T, hD, hT⟩ := sDigestBlock_sound hκ hbb h
  refine ⟨hp, _, _, ⟨lP, lR, l2, l3⟩, T, hD, ?_⟩
  have hm : (cellPairVal (σ sM0) (σ sM1)).toNat = msgNat (σ sM0) (σ sM1) := cellPairVal_toNat _ _
  simp only [sphincsClaimOf]
  rw [hmsgDigest_cells, hm, ← hT]

/-! ## What the block holds, in the statement's terms -/

theorem DigestAt.forsBit {T : Nat} (h : DigestAt σ T) {c k : Nat} (hc : c < 24) (hk : k < 10) :
    σ (sMdBit (10 * c + 9 - k)) = bitE ((Sphincs.digestForsLeaves (digestOf T) ⟨c, hc⟩).val.testBit k) := by
  rw [h.mdBit (by omega), digestForsLeaves_val h.1, testBit_forsLeafN]
  simp [hk]

theorem DigestAt.forsVal {T : Nat} (h : DigestAt σ T) {c z : Nat} (hc : c < 24) (hz : z < 10) :
    σ (sFVal c z) =
      eOfNat (2 ^ (10 - z) * c + (Sphincs.digestForsLeaves (digestOf T) ⟨c, hc⟩).val >>> z) := by
  rw [h.2.2.1 c hc z hz, digestForsLeaves_val h.1]

theorem DigestAt.layerBit {T : Nat} (h : DigestAt σ T) {l k : Nat} (hl : l < 3) (hk : k < sLeafLen l) :
    σ (sLeafBit (8 * l + k)) =
      bitE ((Sphincs.leafOfIndex ⟨l, hl⟩ (Sphincs.digestIndex (digestOf T))).val.testBit k) := by
  have h26 : 8 * l + k < 26 := by simp only [sLeafLen] at hk; split_ifs at hk <;> omega
  rw [h.leafBit h26, leafOfIndex_digest h.1, testBit_layerLeafN]
  simp [hk, sLeafOff]

theorem DigestAt.layerVal {T : Nat} (h : DigestAt σ T) {l z : Nat} (hl : l < 3) (hz : z < sLeafLen l) :
    σ (sLVal (8 * l + z)) = eOfNat ((Sphincs.leafOfIndex ⟨l, hl⟩ (Sphincs.digestIndex (digestOf T))).val >>> z) := by
  rw [show 8 * l + z = sLeafOff l + z from rfl, h.2.2.2.1 l hl z hz, leafOfIndex_digest h.1]

theorem DigestAt.treeMid {T : Nat} (h : DigestAt σ T) :
    σ sTreeMid = eOfNat ((Sphincs.leafOfIndex ⟨2, by decide⟩ (Sphincs.digestIndex (digestOf T))).val % 2 ^ 8) := by
  rw [h.2.2.2.2, leafOfIndex_digest h.1, layerLeaf2_low]

end
end LeanVM.Guest.B1.Sig
