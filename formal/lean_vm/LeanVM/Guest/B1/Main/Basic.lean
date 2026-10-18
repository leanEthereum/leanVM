/-
  LeanVM.Guest.B1.Main.Basic

  The vocabulary of `main` and `aggregate_claims` (TRIAGE #76, #77): the memory, range checks
  against constant and runtime bounds, `mul_range` loops read forward, claims decoded from their
  cells, and the deferred claim of its 53 cells.
-/

module

public import LeanVM.Guest.B1.Sumcheck
public import LeanVM.Guest.B1.Tables
public import LeanVM.Spec.Node

/-!
# `main`: shared vocabulary

* `MemOk rd`: the reader is a memory of `2^κ` words, `16 ≤ κ ≤ 32`, as every valid execution's
  is. A range check is then sound: `rc_const` against a compile-time `g^c`, `rc_bound` against a
  runtime bound `L·g⁻¹` (`assert log x < log L`).
* `loop_sound`: a guarded `mul_range` loop read forward, through `Program.Rel` only: when the end
  is `g^m` below the order of `g`, the body holds at every `g^j`, `j < m`.
* Claims as cells: a signature claim is four cells, its key's root and parameter and the
  message's two halves (`claimBytes`); `xmssClaimOf`, `sphincsClaimOf` decode them from the
  cells' low limbs, and `xmssListDigest_claims` says the claims decoded from `4n` cells hash as
  the cells do.
* `deferOfCells`: the deferred claim of its 53 cells, `22` bytecode coordinates, the value, `28`
  matrix coordinates, the two values.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The memory and range checks -/

/-- The reader is a memory of `2^κ` words, `16 ≤ κ ≤ 32`, as every valid execution's is. -/
def MemOk (rd : Reader) : Prop := ∃ κ, 16 ≤ κ ∧ κ ≤ 32 ∧ ∃ L : MemImage κ, rd = L.read

/-- A word read at offset `0` through a pointer of the memory is a g-power below `2^32`. -/
theorem load_gpow {rd : Reader} (hm : MemOk rd) {x t : E} (h : LoadHolds rd x 0 t) :
    ∃ e < 2 ^ 32, x = gen ^ e := by
  obtain ⟨κ, -, hκ, L, rfl⟩ := hm
  obtain ⟨hx, hr⟩ := h
  rw [Parameters.gpow, pow_zero, mul_one] at hr
  obtain ⟨i, hi, -⟩ := (read_some_iff (by omega) L _ _).mp hr
  refine ⟨i, lt_of_lt_of_le i.2 (Nat.pow_le_pow_right (by decide) hκ), ?_⟩
  rw [eq_ofK_limb hx, hi, gen_pow_eq_ofK]

theorem gen_pow_inj' {a b : ℕ} (ha : a < 2 ^ 34) (hb : b < 2 ^ 34) (h : gen ^ a = gen ^ b) :
    a = b :=
  gen_pow_inj (by omega) (by omega) h

/-- A range check: its two reads make `x`, `y` g-powers below `2^32`, `k` their product. -/
theorem rc_sound {rd : Reader} (hm : MemOk rd) {x y t1 t2 k : E}
    (h : LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2) :
    ∃ e e', e < 2 ^ 32 ∧ e' < 2 ^ 32 ∧ x = gen ^ e ∧ k = gen ^ (e + e') := by
  obtain ⟨e, he, rfl⟩ := load_gpow hm h.1
  obtain ⟨e', he', rfl⟩ := load_gpow hm h.2.2
  exact ⟨e, e', he, he', rfl, by rw [h.2.1, pow_add]⟩

/-- **A range check against `g^c`**: `x = g^e` with `e ≤ c`. -/
theorem rc_const {rd : Reader} (hm : MemOk rd) {x y t1 t2 k : E} {c : ℕ} (hc : c < 2 ^ 33)
    (hk : k = gen ^ c) (h : LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2) :
    ∃ e ≤ c, x = gen ^ e := by
  obtain ⟨e, e', he, he', hx, hk'⟩ := rc_sound hm h
  have := gen_pow_inj' (by omega) (by omega) (hk.symm.trans hk')
  exact ⟨e, by omega, hx⟩

/-- `g⁻¹`, the word a runtime range bound is multiplied by. -/
abbrev ginvW : E := word 9223372036854775821 0 0

theorem ginvW_mul_gen : ginvW * gen = 1 := by
  unfold ginvW
  rw [word_eOfNat, gen, eOfNat, eOfNat, ← ofK_mul, ← ofK_one]
  congr 1

/-- **A range check against a runtime bound** `L = g^M` (`assert log x < log L`, its `k` the
product `L·g⁻¹`): `x = g^e` with `e < M`. -/
theorem rc_bound {rd : Reader} (hm : MemOk rd) {x y t1 t2 k L : E} {M : ℕ} (hM : M < 2 ^ 33)
    (hL : L = gen ^ M) (hk : k = L * ginvW)
    (h : LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2) : ∃ e < M, x = gen ^ e := by
  obtain ⟨e, e', he, he', hx, hk'⟩ := rc_sound hm h
  have : gen ^ M = gen ^ (e + e' + 1) := by
    rw [← hL, show L = L * (ginvW * gen) by rw [ginvW_mul_gen, mul_one], ← mul_assoc, ← hk, hk',
      pow_succ]
  have := gen_pow_inj' (by omega) (by omega) this
  exact ⟨e, by omega, hx⟩

/-! ## Compile-time g-powers -/

set_option maxRecDepth 100000 in
theorem word_gmax : word 9272771591053052074 0 0 = gen ^ 65535 := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

set_option maxRecDepth 100000 in
theorem word_g257 : word 139298 0 0 = gen ^ 257 := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

theorem word_g16 : word 65536 0 0 = gen ^ 16 := word_two_pow (a := 16) (by decide)

/-! ## `mul_range` loops, forward -/

theorem one_add_gen_pow_ne_zero {m : ℕ} (h0 : 0 < m) (hm : m < ordG) : 1 + gen ^ m ≠ 0 := by
  intro h
  have h1 : gen ^ m = gen ^ 0 := by rw [pow_zero]; exact (e_add_eq_zero_iff.mp h).symm
  have := gen_pow_inj hm (by norm_num) h1
  omega

/-- **A guarded loop, forward** (`for x in mul_range(1, N)`, `N = g^m`): if every run of the
helper at `x` gives the body `B x` and, while `x·g ≠ N`, a run at `x·g`, then the guard and its
call give `B` at every `g^j`, `j < m`. -/
theorem loop_sound {rd : Reader} {f : String} {ps : List E} {N : E} {m : ℕ} {B : E → Prop}
    (hm : m < ordG) (hN : N = gen ^ m)
    (hstep : ∀ x, coreProgram.Rel rd f (x :: ps) [] →
      B x ∧ (x * gen + N ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []))
    (h : 1 + N ≠ 0 → coreProgram.Rel rd f (1 :: ps) []) : ∀ j < m, B (gen ^ j) := by
  have key : ∀ t k, k + t = m → coreProgram.Rel rd f (gen ^ k :: ps) [] →
      ∀ j, k ≤ j → j < m → B (gen ^ j) := by
    intro t
    induction t with
    | zero => intro k hk _ j h1 h2; omega
    | succ t ih =>
      intro k hk hrun j h1 h2
      obtain ⟨hB, hnext⟩ := hstep _ hrun
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hB
      · have hne : gen ^ k * gen + N ≠ 0 := by
          intro he
          rw [gen_pow_add_eq_zero_iff, hN] at he
          have := gen_pow_inj hm (by unfold ordG at hm; omega) he
          omega
        have := hnext hne
        rw [gen_pow_mul_gen] at this
        exact ih (k + 1) (by omega) this j hlt h2
  intro j hj
  have h1 := h (by rw [hN]; exact one_add_gen_pow_ne_zero (by omega) hm)
  rw [← pow_zero gen] at h1
  exact key m 0 (by omega) h1 j (Nat.zero_le j) hj

/-! ## Bytes of numbers -/

/-- The `k` low little-endian bytes of `n`. -/
def leBytes (n k : ℕ) : List UInt8 := List.ofFn fun i : Fin k => UInt8.ofNat (n / 256 ^ i.val)

@[simp] theorem length_leBytes (n k : ℕ) : (leBytes n k).length = k := by simp [leBytes]

theorem getElem_leBytes (n k i : ℕ) (hi : i < (leBytes n k).length) :
    (leBytes n k)[i] = UInt8.ofNat (n / 256 ^ i) := by simp [leBytes]

theorem toNat_uint8_ofNat (n : ℕ) : (UInt8.ofNat n).toNat = n % 256 := by
  simp [UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat]

theorem uint8_ofNat_eq_iff {a b : ℕ} : UInt8.ofNat a = UInt8.ofNat b ↔ a % 256 = b % 256 := by
  constructor
  · intro h
    simpa [toNat_uint8_ofNat] using congrArg UInt8.toNat h
  · intro h
    apply UInt8.toNat_inj.mp
    simpa [toNat_uint8_ofNat] using h

theorem leBytes_mod (n k : ℕ) : leBytes (n % 256 ^ k) k = leBytes n k := by
  apply List.ext_getElem (by simp)
  intro i h1 _
  simp only [getElem_leBytes, uint8_ofNat_eq_iff]
  simp only [length_leBytes] at h1
  rw [show 256 ^ k = 256 ^ i * (256 * 256 ^ (k - i - 1)) by
      rw [← pow_succ', ← pow_add, show i + (k - i - 1 + 1) = k by omega],
    Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

theorem leBytes_append (n a b : ℕ) :
    leBytes n a ++ leBytes (n / 256 ^ a) b = leBytes n (a + b) := by
  apply List.ext_getElem (by simp)
  intro i _ h2
  simp only [length_leBytes] at h2
  by_cases hi : i < a
  · rw [List.getElem_append_left (by simpa using hi)]
    simp only [getElem_leBytes]
  · rw [List.getElem_append_right (by simpa using hi)]
    simp only [getElem_leBytes, length_leBytes, Nat.div_div_eq_div_mul, ← pow_add]
    congr 3
    omega

theorem leBytes_add_mul (lo hi a b : ℕ) (hlo : lo < 256 ^ a) :
    leBytes (lo + 256 ^ a * hi) (a + b) = leBytes lo a ++ leBytes hi b := by
  rw [← leBytes_append, ← leBytes_mod (lo + 256 ^ a * hi) a, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hlo, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlo, zero_add]

theorem bytesLE_eq (k : ℕ) (v : BitVec (8 * k)) : LeanXmss.bytesLE k v = leBytes v.toNat k := by
  apply List.ext_getElem (by simp [LeanXmss.bytesLE])
  intro i _ _
  simp only [LeanXmss.bytesLE, List.getElem_ofFn, getElem_leBytes]
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, toNat_uint8_ofNat,
    Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem wordBytes_eq (w : UInt32) : wordBytes w = leBytes w.toNat 4 := by
  apply List.ext_getElem (by simp [wordBytes])
  intro i _ h2
  simp only [length_leBytes] at h2
  simp only [getElem_leBytes]
  apply UInt8.toNat_inj.mp
  interval_cases i <;> simp [wordBytes, Nat.shiftRight_eq_div_pow]

theorem kBytes_eq (a : K) : kBytes a = leBytes (kToNat a) 8 := by
  have hlt : kToNat a < 2 ^ 64 := (a.toBitVec).isLt
  rw [kBytes, wordBytes_eq, wordBytes_eq]
  have hl : (lowWord a).toNat = kToNat a % 2 ^ 32 := by
    simp [lowWord, kToNat, UInt32.toNat, BitVec.extractLsb'_toNat]
  have hh : (highWord a).toNat = kToNat a / 2 ^ 32 := by
    simp only [highWord, kToNat, UInt32.toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hl, hh, show (2 : ℕ) ^ 32 = 256 ^ 4 by norm_num, leBytes_mod, leBytes_append]

/-! ## Claims as cells -/

/-- The number a cell's two low limbs hold. -/
def cellNat (x : E) : ℕ := kToNat (x.limb 0) + 2 ^ 64 * kToNat (x.limb 1)

theorem cellNat_lt (x : E) : cellNat x < 2 ^ 128 := by
  have h0 : kToNat (x.limb 0) < 2 ^ 64 := ((x.limb 0).toBitVec).isLt
  have h1 : kToNat (x.limb 1) < 2 ^ 64 := ((x.limb 1).toBitVec).isLt
  unfold cellNat; omega

theorem cellBytes_eq_leBytes (x : E) : cellBytes x = leBytes (cellNat x) 16 := by
  rw [cellBytes, kBytes_eq, kBytes_eq, cellNat, show (2 : ℕ) ^ 64 = 256 ^ 8 by norm_num,
    show 16 = 8 + 8 from rfl, leBytes_add_mul _ _ _ _ (by
      have := ((x.limb 0).toBitVec).isLt; simpa [kToNat] using this)]

/-- The 128-bit value of a cell's two low limbs. -/
def cellVal (x : E) : BitVec 128 := BitVec.ofNat 128 (cellNat x)

theorem toNat_cellVal (x : E) : (cellVal x).toNat = cellNat x := by
  rw [cellVal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (cellNat_lt x)]

/-- The 256-bit value of two cells, the first low. -/
def cellPairVal (lo hi : E) : BitVec 256 := BitVec.ofNat 256 (cellNat lo + 2 ^ 128 * cellNat hi)

theorem toNat_cellPairVal (lo hi : E) :
    (cellPairVal lo hi).toNat = cellNat lo + 2 ^ 128 * cellNat hi := by
  have h0 := cellNat_lt lo
  have h1 := cellNat_lt hi
  rw [cellPairVal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- **A claim's bytes are its cells'**: the root, the parameter and the message decoded from four
cells hash as the cells do. -/
theorem claimBytes_cells (a b c d : E) :
    claimBytes (cellVal a) (cellVal b) (cellPairVal c d) =
      cellBytes a ++ cellBytes b ++ (cellBytes c ++ cellBytes d) := by
  simp only [claimBytes, bytes16]
  rw [bytesLE_eq 16, bytesLE_eq 16, bytesLE_eq 32, toNat_cellVal, toNat_cellVal,
    toNat_cellPairVal, cellBytes_eq_leBytes, cellBytes_eq_leBytes, cellBytes_eq_leBytes,
    cellBytes_eq_leBytes, show (2 : ℕ) ^ 128 = 256 ^ 16 by norm_num, show 32 = 16 + 16 from rfl,
    leBytes_add_mul _ _ _ _ (by have := cellNat_lt c; norm_num at this ⊢; omega)]

/-- The leanXMSS claim of four cells: the key's root and parameter, the message's halves. -/
def xmssOf (a b c d : E) : XmssClaim := (⟨cellVal a, cellVal b⟩, cellPairVal c d)

/-- The leanSPHINCS claim of four cells. -/
def sphincsOf (a b c d : E) : SphincsClaim := (⟨cellVal a, cellVal b⟩, cellPairVal c d)

/-- The leanXMSS claims of a list of cells, four a claim. -/
def xmssClaims : List E → List XmssClaim
  | a :: b :: c :: d :: rest => xmssOf a b c d :: xmssClaims rest
  | _ => []

/-- The leanSPHINCS claims of a list of cells, four a claim. -/
def sphincsClaims : List E → List SphincsClaim
  | a :: b :: c :: d :: rest => sphincsOf a b c d :: sphincsClaims rest
  | _ => []

theorem xmssClaims_spec : ∀ (n : ℕ) (cs : List E), cs.length = 4 * n →
    (xmssClaims cs).length = n ∧
      (∀ j (h : j < (xmssClaims cs).length), (xmssClaims cs)[j] =
        xmssOf (cs.getD (4 * j) 0) (cs.getD (4 * j + 1) 0) (cs.getD (4 * j + 2) 0)
          (cs.getD (4 * j + 3) 0)) ∧
      (xmssClaims cs).flatMap (fun c => claimBytes c.1.root c.1.parameter c.2) =
        cs.flatMap cellBytes
  | 0, [], _ => ⟨rfl, fun j h => absurd h (by simp [xmssClaims]), rfl⟩
  | n + 1, a :: b :: c :: d :: rest, h => by
    have hr : rest.length = 4 * n := by simp at h; omega
    obtain ⟨h1, h2, h3⟩ := xmssClaims_spec n rest hr
    refine ⟨by simp [xmssClaims, h1], fun j hj => ?_, ?_⟩
    · cases j with
      | zero => rfl
      | succ j =>
        simp only [xmssClaims, List.getElem_cons_succ]
        rw [h2 j (by simpa [xmssClaims] using hj)]
        simp only [show 4 * (j + 1) = 4 * j + 3 + 1 by ring, show 4 * j + 3 + 1 + 1 = 4 * j + 1 + 3 + 1 by ring,
          show 4 * j + 3 + 1 + 2 = 4 * j + 2 + 3 + 1 by ring, show 4 * j + 3 + 1 + 3 = 4 * j + 3 + 3 + 1 by ring,
          List.getD_cons_succ]
    · simp only [xmssClaims, List.flatMap_cons, h3, xmssOf, claimBytes_cells, List.append_assoc]
  | 0, _ :: _, h => by simp at h
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega
  | n + 1, [_, _], h => by simp at h; omega
  | n + 1, [_, _, _], h => by simp at h; omega

theorem sphincsClaims_spec : ∀ (n : ℕ) (cs : List E), cs.length = 4 * n →
    (sphincsClaims cs).length = n ∧
      (∀ j (h : j < (sphincsClaims cs).length), (sphincsClaims cs)[j] =
        sphincsOf (cs.getD (4 * j) 0) (cs.getD (4 * j + 1) 0) (cs.getD (4 * j + 2) 0)
          (cs.getD (4 * j + 3) 0)) ∧
      (sphincsClaims cs).flatMap (fun c => claimBytes c.1.root c.1.parameter c.2) =
        cs.flatMap cellBytes
  | 0, [], _ => ⟨rfl, fun j h => absurd h (by simp [sphincsClaims]), rfl⟩
  | n + 1, a :: b :: c :: d :: rest, h => by
    have hr : rest.length = 4 * n := by simp at h; omega
    obtain ⟨h1, h2, h3⟩ := sphincsClaims_spec n rest hr
    refine ⟨by simp [sphincsClaims, h1], fun j hj => ?_, ?_⟩
    · cases j with
      | zero => rfl
      | succ j =>
        simp only [sphincsClaims, List.getElem_cons_succ]
        rw [h2 j (by simpa [sphincsClaims] using hj)]
        simp only [show 4 * (j + 1) = 4 * j + 3 + 1 by ring, show 4 * j + 3 + 1 + 1 = 4 * j + 1 + 3 + 1 by ring,
          show 4 * j + 3 + 1 + 2 = 4 * j + 2 + 3 + 1 by ring, show 4 * j + 3 + 1 + 3 = 4 * j + 3 + 3 + 1 by ring,
          List.getD_cons_succ]
    · simp only [sphincsClaims, List.flatMap_cons, h3, sphincsOf, claimBytes_cells, List.append_assoc]
  | 0, _ :: _, h => by simp at h
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega
  | n + 1, [_, _], h => by simp at h; omega
  | n + 1, [_, _, _], h => by simp at h; omega

/-- **The leanXMSS list digest of decoded claims** is the BLAKE2s of their cells. -/
theorem xmssListDigest_claims {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n) :
    xmssListDigest (xmssClaims cs) = blake2sBytes (cs.flatMap cellBytes) := by
  rw [xmssListDigest, (xmssClaims_spec n cs hlen).2.2]

/-- **The leanSPHINCS list digest of decoded claims** is the BLAKE2s of their cells. -/
theorem sphincsListDigest_claims {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n) :
    sphincsListDigest (sphincsClaims cs) = blake2sBytes (cs.flatMap cellBytes) := by
  rw [sphincsListDigest, (sphincsClaims_spec n cs hlen).2.2]

/-! ## The deferred claim of its cells -/

/-- The deferred claim of its 53 cells (`DEFER_STMT_*`): the bytecode point, its value, the matrix
point, the two values. -/
def deferOfCells (cs : List E) : DeferredClaim :=
  ⟨cs.take 22, cs.getD 22 0, (cs.drop 23).take 28, cs.getD 51 0, cs.getD 52 0⟩

theorem cells_deferOfCells {cs : List E} (h : cs.length = 53) : (deferOfCells cs).cells = cs := by
  have e1 : cs.drop 22 = cs.getD 22 0 :: cs.drop 23 := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.drop_eq_getElem_cons (by omega)
  have e2 : (cs.drop 23).drop 28 = [cs.getD 51 0, cs.getD 52 0] := by
    rw [List.drop_drop, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
      show 23 + 28 = 51 by rfl, List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega)]
  conv_rhs => rw [← List.take_append_drop 22 cs, e1, ← List.take_append_drop 28 (cs.drop 23), e2]
  simp [DeferredClaim.cells, deferOfCells]

theorem deferOfCells_cells {d : DeferredClaim} (h1 : d.bytecodePoint.length = 22)
    (h2 : d.matrixPoint.length = 28) : deferOfCells d.cells = d := by
  obtain ⟨bp, bv, mp, ma, mb⟩ := d
  simp only at h1 h2
  simp only [deferOfCells, DeferredClaim.cells, DeferredClaim.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [h1]
  · rw [List.getD_eq_getElem _ _ (by simp [h1, h2])]; simp [h1]
  · simp [h1, h2, List.drop_append, List.take_append]
  · rw [List.getD_eq_getElem _ _ (by simp [h1, h2])]; simp [h1, h2]
  · rw [List.getD_eq_getElem _ _ (by simp [h1, h2])]; simp [h1, h2]

theorem length_deferOfCells {cs : List E} (h : cs.length = 53) :
    (deferOfCells cs).bytecodePoint.length = 22 ∧ (deferOfCells cs).matrixPoint.length = 28 := by
  simp [deferOfCells, h]

end
end LeanVM.Guest.B1.Main
