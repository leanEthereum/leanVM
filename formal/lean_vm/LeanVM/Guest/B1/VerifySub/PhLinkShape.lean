/-
  LeanVM.Guest.B1.VerifySub.PhLinkShape

  `verify_sub`'s link shape: the tallest table's rows, the pointer width, its chunks, the cycle
  count and its bits, against the layout the announced sizes give.
-/

module

public import LeanVM.Guest.B1.VerifySub.PhLinkCycles
public import LeanVM.Guest.B1.Link.Arith.Calls
public import LeanVM.Guest.B1.Link.ChunkD
public import LeanVM.Guest.B1.Bits.SmallGPower
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»
import Mathlib.Tactic.IntervalCases

/-!
# The link's shape

`vsShapeAT`, `vsShapeIteT`, `vsShapeBT` (statements `375 .. 430`, checked by the kernel): the
hinted `g^n`, `g^w`, the flag and `g^p` (`link_shape`); `g^n` over every height, equal to one;
`g^w` in `g^19 .. g^24`, at least `g^log_mem`, the cycles below `2^w` (`assert_small_g_power`),
and either at least `2^(w - 1)` or `w` is `log_mem` or `19`; `chunk_d` at `w`. With the heights'
`table_size`s (`vsHeightsT`) and the cycle bits (`vsCbT`): `VsRun.shapeOk`, the link's shape is
the layout's (`linkRows`, `linkWidth`, `Chunks.new`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Link

@[expose] public section

/-- `verify_sub`'s statements 375 to 426. -/
def vsShapeAT : List Stmt := (
  .atom (.hint (.witness "link_shape" (.heap (.n 9) 0 4))) ::
  .atom (.load (.n 408) (.n 9) 0) ::
  .atom (.load (.n 409) (.n 9) 1) ::
  .atom (.load (.n 410) (.n 9) 2) ::
  .atom (.const (.n 411) (word 16777216 0)) ::
  .atom (.mul (.n 408) (.n 412) (.n 115)) ::
  .atom (.rangeCheck (.n 412) (.n 413) (.n 414) (.n 415) (.n 411)) ::
  .atom (.add (.n 416) (.n 408) (.n 115)) ::
  .atom (.const (.n 417) (word 16777216 0)) ::
  .atom (.mul (.n 408) (.n 418) (.n 116)) ::
  .atom (.rangeCheck (.n 418) (.n 419) (.n 420) (.n 421) (.n 417)) ::
  .atom (.add (.n 422) (.n 408) (.n 116)) ::
  .atom (.mul (.n 423) (.n 416) (.n 422)) ::
  .atom (.const (.n 424) (word 16777216 0)) ::
  .atom (.mul (.n 408) (.n 425) (.n 117)) ::
  .atom (.rangeCheck (.n 425) (.n 426) (.n 427) (.n 428) (.n 424)) ::
  .atom (.add (.n 429) (.n 408) (.n 117)) ::
  .atom (.mul (.n 430) (.n 423) (.n 429)) ::
  .atom (.const (.n 431) (word 16777216 0)) ::
  .atom (.mul (.n 408) (.n 432) (.n 118)) ::
  .atom (.rangeCheck (.n 432) (.n 433) (.n 434) (.n 435) (.n 431)) ::
  .atom (.add (.n 436) (.n 408) (.n 118)) ::
  .atom (.mul (.n 437) (.n 430) (.n 436)) ::
  .atom (.const (.n 438) (word 16777216 0)) ::
  .atom (.mul (.n 408) (.n 439) (.n 119)) ::
  .atom (.rangeCheck (.n 439) (.n 440) (.n 441) (.n 442) (.n 438)) ::
  .atom (.add (.n 443) (.n 408) (.n 119)) ::
  .atom (.mul (.n 444) (.n 437) (.n 443)) ::
  .atom (.const (.n 445) (word 16777216 0)) ::
  .atom (.mul (.n 408) (.n 446) (.n 120)) ::
  .atom (.rangeCheck (.n 446) (.n 447) (.n 448) (.n 449) (.n 445)) ::
  .atom (.add (.n 450) (.n 408) (.n 120)) ::
  .atom (.mul (.n 451) (.n 444) (.n 450)) ::
  .atom (.const (.n 452) (word 0 0)) ::
  .atom (.assertEq (.n 451) (.n 452)) ::
  .atom (.const (.n 453) (word 32 0)) ::
  .atom (.const (.n 454) (word 10248187242686185485 0)) ::
  .atom (.mul (.n 455) (.n 409) (.n 454)) ::
  .atom (.rangeCheck (.n 455) (.n 456) (.n 457) (.n 458) (.n 453)) ::
  .atom (.const (.n 459) (word 16777216 0)) ::
  .atom (.mul (.n 409) (.n 460) (.n 101)) ::
  .atom (.rangeCheck (.n 460) (.n 461) (.n 462) (.n 463) (.n 459)) ::
  .atom (.mul (.n 464) (.n 4) (.n 409)) ::
  .atom (.load (.n 465) (.n 464) 0) ::
  .atom (.const (.n 466) (word 9223372036854775821 0)) ::
  .atom (.mul (.n 467) (.n 465) (.n 466)) ::
  .atom (.mul (.n 467) (.n 468) (.n 240)) ::
  .call "assert_small_g_power" [.n 468, .n 4] [] ::
  .atom (.mul (.n 469) (.n 410) (.n 410)) ::
  .atom (.assertEq (.n 469) (.n 410)) ::
  .atom (.const (.n 470) (word 1 0)) ::
  .atom (.add (.n 471) (.n 410) (.n 470)) ::
  [])

theorem vsShapeAT_eq : (vsPre.drop 375).take 52 = vsShapeAT := stmtsEqb_sound (by decide +kernel)

/-- `verify_sub`'s statements 427 to 427. -/
def vsShapeIteT : List Stmt := (
  .ite (.n 471) [ .atom (.const (.n 472) (word 9223372036854775821 0)), .atom (.mul (.n 473) (.n 409) (.n 472)), .atom (.mul (.n 474) (.n 4) (.n 473)), .atom (.load (.n 475) (.n 474) 0), .atom (.mul (.n 240) (.n 476) (.n 475)), .call "assert_small_g_power" [.n 476, .n 4] []] [ .atom (.add (.n 477) (.n 409) (.n 101)), .atom (.const (.n 478) (word 524288 0)), .atom (.add (.n 479) (.n 409) (.n 478)), .atom (.mul (.n 480) (.n 477) (.n 479)), .atom (.const (.n 481) (word 0 0)), .atom (.assertEq (.n 480) (.n 481))] ::
  [])

theorem vsShapeIteT_eq : (vsPre.drop 427).take 1 = vsShapeIteT := stmtsEqb_sound (by decide +kernel)

/-- `verify_sub`'s statements 428 to 430. -/
def vsShapeBT : List Stmt := (
  .atom (.const (.n 482) (word 10248187242686185485 0)) ::
  .atom (.mul (.n 483) (.n 409) (.n 482)) ::
  .dispatch (.n 483) ["chunk_d__L19", "chunk_d__L20", "chunk_d__L21", "chunk_d__L22", "chunk_d__L23", "chunk_d__L24"] [] [.n 484] ::
  [])

theorem vsShapeBT_eq : (vsPre.drop 428).take 3 = vsShapeBT := stmtsEqb_sound (by decide +kernel)

/-- `verify_sub`'s statements 181 to 181. -/
def vsCycT : List Stmt := (
  .atom (.mul (.n 240) (.n 216) (.n 224)) ::
  [])

theorem vsCycT_eq : (vsPre.drop 181).take 1 = vsCycT := stmtsEqb_sound (by decide +kernel)


/-! ## Arithmetic -/

theorem winv19_mul : word 10248187242686185485 0 * gen ^ 19 = 1 := by
  rw [show gen ^ 19 = ofK (K.ofBits 524288) by
      rw [← word_two_pow (a := 19) (by decide)]; exact word_eOfNat _,
    show word 10248187242686185485 0 = ofK (K.ofBits 10248187242686185485) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 10248187242686185485 * K.ofBits 524288 = 1 by decide +kernel, ofK_one]

theorem pow_mul_winv19 {w : ℕ} (h : 19 ≤ w) : gen ^ w * word 10248187242686185485 0 = gen ^ (w - 19) := by
  conv_lhs => rw [show w = (w - 19) + 19 by omega, pow_add, mul_assoc, mul_comm (gen ^ 19), winv19_mul, mul_one]

theorem pow_mul_ginv {w : ℕ} (h : 1 ≤ w) : gen ^ w * Digest.ginvW = gen ^ (w - 1) := by
  conv_lhs => rw [show w = (w - 1) + 1 by omega, pow_succ, mul_assoc, mul_comm gen, Digest.ginvW_mul_gen, mul_one]

theorem eq_mul_winv19 {a b : E} (h : b = a * word 10248187242686185485 0) : a = b * gen ^ 19 := by
  rw [h, mul_assoc, winv19_mul, mul_one]

theorem bitLength_le {c w : ℕ} (h : c < 2 ^ w) : bitLength c ≤ w := by
  unfold bitLength
  split_ifs with h0
  · omega
  · have := (Nat.log2_lt h0).mpr h
    omega

theorem le_bitLength {c w : ℕ} (hw : 1 ≤ w) (h : 2 ^ (w - 1) ≤ c) : w ≤ bitLength c := by
  have h0 : c ≠ 0 := by have := Nat.one_le_two_pow (n := w - 1); omega
  unfold bitLength
  simp only [h0, ↓reduceIte]
  have := (Nat.le_log2 h0).mpr h
  omega

/-- The largest of a list of numbers, one of them, bounding every other. -/
theorem foldl_max_eq : ∀ (l : List ℕ) (a n : ℕ), a ≤ n → (∀ x ∈ l, x ≤ n) → (n = a ∨ n ∈ l) →
    l.foldl max a = n
  | [], a, n, _, _, h => by simp at h; simp [h]
  | x :: l, a, n, ha, hl, h => by
    simp only [List.foldl_cons]
    have hx := hl x (by simp)
    refine foldl_max_eq l (max a x) n (max_le ha hx) (fun y hy ↦ hl y (by simp [hy])) ?_
    rcases h with rfl | h
    · exact .inl (max_eq_left hx).symm
    · rcases List.mem_cons.mp h with rfl | h
      · exact .inl (max_eq_right ha).symm
      · exact .inr h

/-- `buildLayout` keeps the rows and the program's log. -/
theorem buildLayout_rows {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) :
    layout.tableRows = rows ∧
      layout.logBytecode = (log2Strict bytecode.length).getD 0 - bytecodeSlotBits := by
  unfold buildLayout at h
  split at h
  · cases h
  · rename_i ll hll
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp [hll]

theorem chunks_width {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) : c.width = w := by
  unfold Chunks.new at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  rw [← h]

/-- A `table_size` dispatch's facts. -/
theorem ts_facts {κ : ℕ} (L : MemoryImage κ) {C : CallRel}
    (hle : CallRel.Le C (coreProgram.Rel L.read)) {fs : List String} (hfs : fs = Link.tsNames)
    {kb rows bits gr lead rest : E}
    (hd : ∃ (j : ℕ) (_ : j < fs.length), kb = ofK (addressOfIndex j) ∧
      C fs[j] [rows, bits] [gr, lead, rest]) :
    ∃ j R, j ≤ 24 ∧ kb = gen ^ j ∧ R ≤ 2 ^ j ∧ rows = eOfNat R ∧ gr = gen ^ R ∧
      ReadsAt L.read bits (Link.cbitsE R j) ∧ LoadHolds L.read bits j (Link.bitE R j) := by
  obtain ⟨j, hj, hkb, R, hR, hrows, hb1, hb2, gr', lead', rest', hrets, hgr, -⟩ :=
    ts_of_dispatch L hle hfs hd
  simp only [List.cons.injEq, and_true] at hrets
  obtain ⟨rfl, rfl, rfl⟩ := hrets
  exact ⟨j, R, hj, hkb, hR, hrows, hgr, hb1, hb2⟩

/-! ## The shape -/

/-- **The link's shape**, against the layout. -/
structure ShapeOk (bytecode : List K) (rd : Reader) (σ : Val) : Prop where
  logBc : (vsLayout bytecode σ).logBytecode = guest_const% BYTECODE_LOG
  tablesEq : (vsLayout bytecode σ).tables = tables
  rowsLen : (vsLayout bytecode σ).tableRows.length = 6
  heightsLen : (vsLayout bytecode σ).tableLogHeights.length = 6
  tableRowsLe : ∀ t < 6,
    (vsLayout bytecode σ).tableRows.getD t 0 ≤ 2 ^ (vsLayout bytecode σ).tableLogHeights.getD t 0
  gH : ∀ t < 6, σ (.n (115 + t)) = gen ^ (vsLayout bytecode σ).tableLogHeights.getD t 0
  bitsPtr : ∀ t < 5, σ (.n (Link.Arith.bitsVn.getD (t + 1) 0)) =
    σ (.n (Link.Arith.bitsVn.getD t 0)) * word 67108864 0
  rowBits : ∀ t < 6, ReadsAt rd (σ (.n (Link.Arith.bitsVn.getD t 0)))
      (Link.cbitsE ((vsLayout bytecode σ).tableRows.getD t 0)
        ((vsLayout bytecode σ).tableLogHeights.getD t 0)) ∧
    LoadHolds rd (σ (.n (Link.Arith.bitsVn.getD t 0))) ((vsLayout bytecode σ).tableLogHeights.getD t 0)
      (Link.bitE ((vsLayout bytecode σ).tableRows.getD t 0)
        ((vsLayout bytecode σ).tableLogHeights.getD t 0))
  cycLt : linkCycles (vsLayout bytecode σ) < 2 ^ 24
  gCyc : σ (.n 240) = gen ^ linkCycles (vsLayout bytecode σ)
  cycleBits : ReadsAt rd (σ (.n 8)) (Link.bitsE (linkCycles (vsLayout bytecode σ)) 24)
  gN : σ (.n 408) = gen ^ linkRows (vsLayout bytecode σ)
  heightsLe : ∀ t < 6,
    (vsLayout bytecode σ).tableLogHeights.getD t 0 ≤ linkRows (vsLayout bytecode σ)
  rowsLe : linkRows (vsLayout bytecode σ) ≤ 24
  gW : σ (.n 409) = gen ^ linkWidth (vsLayout bytecode σ)
  widthGe : 19 ≤ linkWidth (vsLayout bytecode σ)
  widthLe : linkWidth (vsLayout bytecode σ) ≤ 24
  logMemoryLe : (vsLayout bytecode σ).logMemory ≤ linkWidth (vsLayout bytecode σ)
  chunks : ∃ c : Chunks, Chunks.new (linkWidth (vsLayout bytecode σ)) = some c ∧
    σ (.n 484) = gen ^ c.d

theorem link_bitsE_eq : ∀ (w n : ℕ), Link.bitsE n w = KeccakGkr.bitsE n w
  | 0, n => by simp [Link.bitsE, KeccakGkr.bitsE]
  | w + 1, n => by
    rw [Link.bitsE_succ, KeccakGkr.bitsE, link_bitsE_eq w]
    congr 1
    simp only [Link.bitE, Nat.shiftRight_zero]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, eOfNat_zero, eOfNat_one]

/-- A `chunk_d` dispatch at `g^j`: the chunks of `19 + j` bits. -/
theorem chunkD_of_dispatch {rd : Reader} {C : CallRel} (hle : CallRel.Le C (coreProgram.Rel rd))
    {j : ℕ} (hj : j < 6) {x : E}
    (h : C (["chunk_d__L19", "chunk_d__L20", "chunk_d__L21", "chunk_d__L22", "chunk_d__L23",
      "chunk_d__L24"][j]'(by simpa using hj)) [] [x]) :
    ∃ c : Chunks, Chunks.new (j + 19) = some c ∧ x = gen ^ c.d := by
  have hs := Link.chunk_d_sound rd [] [x]
  interval_cases j
  · obtain ⟨c, hc, he⟩ := hs.1 (hle _ _ _ h); exact ⟨c, hc, by simpa using he⟩
  · obtain ⟨c, hc, he⟩ := hs.2.1 (hle _ _ _ h); exact ⟨c, hc, by simpa using he⟩
  · obtain ⟨c, hc, he⟩ := hs.2.2.1 (hle _ _ _ h); exact ⟨c, hc, by simpa using he⟩
  · obtain ⟨c, hc, he⟩ := hs.2.2.2.1 (hle _ _ _ h); exact ⟨c, hc, by simpa using he⟩
  · obtain ⟨c, hc, he⟩ := hs.2.2.2.2.1 (hle _ _ _ h); exact ⟨c, hc, by simpa using he⟩
  · obtain ⟨c, hc, he⟩ := hs.2.2.2.2.2 (hle _ _ _ h); exact ⟨c, hc, by simpa using he⟩

theorem mul_zero_cases {a b : E} (h : a * b = 0) : a = 0 ∨ b = 0 := mul_eq_zero.mp h

set_option maxHeartbeats 1000000 in
/-- **The link's shape** of a run. -/
theorem VsRun.shapeOk {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {V : FrameMap}
    {σ : Val} {rets : List E} (R : VsRun bytecode L C V σ rets) : ShapeOk bytecode L.read σ := by
  have S := R.sizesOk
  have F := readsFacts (R.slice vsReadsT_eq)
  obtain ⟨hexp, -, h11⟩ := R.pre
  have hm := memOk_of (by omega) R.hκ L
  obtain ⟨hlmL, -, htabL, hthL, -, -, -⟩ := Stack.buildLayout_some S.build
  obtain ⟨hrowsL, hlbL⟩ := buildLayout_rows S.build
  have hlb : (vsLayout bytecode σ).logBytecode = 19 := by
    rw [hlbL, R.hbl]; decide
  -- the heights' `table_size`s
  have hh := R.slice vsHeightsT_eq
  simp only [vsHeightsT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hh
  obtain ⟨b106, b107, b108, b109, b110, b111, b112, b113, b114, b115, b116, b117, b118, b119, b120, b121, b122, b123, b124, b125, b126, b127, b128, b129, b130, b131, b132, b133, b134, b135, b136, b137, b138, b139, b140, b141, b142, b143, b144, b145, b146, b147, b148, b149, b150, b151, b152, b153, b154, b155, b156, b157, b158, b159, b160, b161, b162, b163, b164, b165, b166, b167, b168, b169, b170, b171, b172, b173, -⟩ := hh
  obtain ⟨j0, R0, hj0, hk0, hR0, hr0, hg0, hbs0, hb0⟩ := ts_facts L R.hle rfl b109
  obtain ⟨j1, R1, hj1, hk1, hR1, hr1, hg1, hbs1, hb1⟩ := ts_facts L R.hle rfl b121
  obtain ⟨j2, R2, hj2, hk2, hR2, hr2, hg2, hbs2, hb2⟩ := ts_facts L R.hle rfl b134
  obtain ⟨j3, R3, hj3, hk3, hR3, hr3, hg3, hbs3, hb3⟩ := ts_facts L R.hle rfl b147
  obtain ⟨j4, R4, hj4, hk4, hR4, hr4, hg4, hbs4, hb4⟩ := ts_facts L R.hle rfl b160
  obtain ⟨j5, R5, hj5, hk5, hR5, hr5, hg5, hbs5, hb5⟩ := ts_facts L R.hle rfl b173
  have p24 : ∀ {a : ℕ}, a ≤ 24 → 2 ^ a ≤ 2 ^ 24 := fun ha ↦ Nat.pow_le_pow_right (by norm_num) ha
  -- the rows
  have hrow : ∀ {t : ℕ} {x : E} {Rt : ℕ}, t < 6 → LoadHolds L.read (σ (.n 56)) t x → x = eOfNat Rt →
      Rt ≤ 2 ^ 24 → kToNat (((vsAnnounced σ).getD (t + 1) 0).limb 0) = Rt := by
    intro t x Rt ht hl hx hR
    rw [loadHolds_unique (F.rows t ht) hl, hx, kToNat_eOfNat (by omega)]
  have e0 := hrow (by norm_num) b108 hr0 (hR0.trans (p24 hj0))
  have e1 := hrow (by norm_num) b118 hr1 (hR1.trans (p24 hj1))
  have e2 := hrow (by norm_num) b131 hr2 (hR2.trans (p24 hj2))
  have e3 := hrow (by norm_num) b144 hr3 (hR3.trans (p24 hj3))
  have e4 := hrow (by norm_num) b157 hr4 (hR4.trans (p24 hj4))
  have e5 := hrow (by norm_num) b170 hr5 (hR5.trans (p24 hj5))
  have hTR : (vsLayout bytecode σ).tableRows = [R0, R1, R2, R3, R4, R5] := by
    rw [hrowsL, ← e0, ← e1, ← e2, ← e3, ← e4, ← e5]
    rfl
  -- the heights
  have hlen : (vsLayout bytecode σ).tableLogHeights.length = 6 := by
    rw [hthL, List.length_zipWith]; simp [vsRows, vsAnnounced, tableLogFloors, nTables]
  obtain ⟨a0, a1, a2, a3, a4, a5, hTH⟩ : ∃ a0 a1 a2 a3 a4 a5,
      (vsLayout bytecode σ).tableLogHeights = [a0, a1, a2, a3, a4, a5] := by
    match h : (vsLayout bytecode σ).tableLogHeights, hlen with
    | [a0, a1, a2, a3, a4, a5], _ => exact ⟨a0, a1, a2, a3, a4, a5, rfl⟩
  have hHe := S.heights
  rw [hTH] at hHe
  simp only [nTables, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.cons.injEq, and_true] at hHe
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hHe
  have h24 := S.heights24
  rw [hTH] at h24
  have i0 : j0 = a0 := Digest.gen_pow_inj' (by omega) (by have := h24 0 (by decide); simp at this; omega)
    (hk0.symm.trans q0)
  have i1 : j1 = a1 := Digest.gen_pow_inj' (by omega) (by have := h24 1 (by decide); simp at this; omega)
    (hk1.symm.trans q1)
  have i2 : j2 = a2 := Digest.gen_pow_inj' (by omega) (by have := h24 2 (by decide); simp at this; omega)
    (hk2.symm.trans q2)
  have i3 : j3 = a3 := Digest.gen_pow_inj' (by omega) (by have := h24 3 (by decide); simp at this; omega)
    (hk3.symm.trans q3)
  have i4 : j4 = a4 := Digest.gen_pow_inj' (by omega) (by have := h24 4 (by decide); simp at this; omega)
    (hk4.symm.trans q4)
  have i5 : j5 = a5 := Digest.gen_pow_inj' (by omega) (by have := h24 5 (by decide); simp at this; omega)
    (hk5.symm.trans q5)
  subst i0 i1 i2 i3 i4 i5
  -- the cycles
  have hc := R.slice vsCycT_eq
  simp only [vsCycT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hc
  have hcyc : linkCycles (vsLayout bytecode σ) = R0 + R1 + R2 + R3 + R4 + R5 := by
    rw [linkCycles, hTR]; simp
  have hgc : σ (.n 240) = gen ^ linkCycles (vsLayout bytecode σ) := by
    simp only [Atom.Holds] at b128 b141 b154 b167
    rw [hcyc, hc.1, b167, b154, b141, b128, hg0, hg1, hg2, hg3, hg4, hg5]
    simp only [← pow_add]
  have hcN : linkCycles (vsLayout bytecode σ) < 2 ^ 34 := by
    rw [hcyc]
    have := p24 hj0; have := p24 hj1; have := p24 hj2; have := p24 hj3; have := p24 hj4
    have := p24 hj5
    omega
  obtain ⟨hcyc24, hcb⟩ := cbFacts (R.slice vsCbT_eq) hcN hgc
  -- `g^n`
  have hA := R.slice vsShapeAT_eq
  simp only [vsShapeAT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hA
  obtain ⟨-, -, -, -, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20,
    s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39,
    s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50, s51, -⟩ := hA
  have w24 : word 16777216 0 = gen ^ 24 := word_two_pow (a := 24) (by norm_num)
  have rcN : ∀ {x b t1 t2 k : E}, k = word 16777216 0 →
      (LoadHolds L.read x 0 t1 ∧ k = x * b ∧ LoadHolds L.read b 0 t2) → ∃ e ≤ 24, x = gen ^ e :=
    fun hk h ↦ Digest.rc_const hm (c := 24) (by norm_num) (hk.trans w24) h
  obtain ⟨f0, hf0, x0⟩ := rcN s4 s6
  obtain ⟨f1, hf1, x1⟩ := rcN s8 s10
  obtain ⟨f2, hf2, x2⟩ := rcN s13 s15
  obtain ⟨f3, hf3, x3⟩ := rcN s18 s20
  obtain ⟨f4, hf4, x4⟩ := rcN s23 s25
  obtain ⟨f5, hf5, x5⟩ := rcN s28 s30
  set n0 := f0 + j0 with hn0
  have gn : σ (.n 408) = gen ^ n0 := by rw [s5, x0, q0, ← pow_add]
  have nt : ∀ {f a : ℕ} {x kb : E}, f ≤ 24 → a ≤ 24 → σ (.n 408) = x * kb → x = gen ^ f →
      kb = gen ^ a → n0 = f + a := by
    intro f a x kb hf ha h1 h2 h3
    refine Digest.gen_pow_inj' (by omega) (by omega) ?_
    rw [← gn, h1, h2, h3, pow_add]
  have h24' : ∀ t < 6, [j0, j1, j2, j3, j4, j5].getD t 0 ≤ 24 := fun t ht ↦ by
    have := h24 t ht; simpa using this
  have ha0 := h24' 0 (by decide); have ha1 := h24' 1 (by decide); have ha2 := h24' 2 (by decide)
  have ha3 := h24' 3 (by decide); have ha4 := h24' 4 (by decide); have ha5 := h24' 5 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at ha0 ha1 ha2 ha3 ha4 ha5
  have n1 := nt hf1 ha1 s9 x1 q1
  have n2 := nt hf2 ha2 s14 x2 q2
  have n3 := nt hf3 ha3 s19 x3 q3
  have n4 := nt hf4 ha4 s24 x4 q4
  have n5 := nt hf5 ha5 s29 x5 q5
  -- one height is `n`
  have hz : σ (.n 451) = 0 := by
    have := eq_of_add_zero s34; rw [this, s33, word_zero]
  have hone : n0 = j0 ∨ n0 = j1 ∨ n0 = j2 ∨ n0 = j3 ∨ n0 = j4 ∨ n0 = j5 := by
    have ef : ∀ {t : E} {a : ℕ}, σ (.n 408) + t = 0 → t = gen ^ a → a ≤ 24 → n0 = a := by
      intro t a h ht ha
      exact Digest.gen_pow_inj' (by omega) (by omega) (by rw [← gn, eq_of_add_zero h, ht])
    rw [s32, s27, s22, s17, s12] at hz
    rcases mul_zero_cases hz with hz | hz
    · rcases mul_zero_cases hz with hz | hz
      · rcases mul_zero_cases hz with hz | hz
        · rcases mul_zero_cases hz with hz | hz
          · rcases mul_zero_cases hz with hz | hz
            · exact .inl (ef (s7 ▸ hz) q0 ha0)
            · exact .inr (.inl (ef (s11 ▸ hz) q1 ha1))
          · exact .inr (.inr (.inl (ef (s16 ▸ hz) q2 ha2)))
        · exact .inr (.inr (.inr (.inl (ef (s21 ▸ hz) q3 ha3))))
      · exact .inr (.inr (.inr (.inr (.inl (ef (s26 ▸ hz) q4 ha4)))))
    · exact .inr (.inr (.inr (.inr (.inr (ef (s31 ▸ hz) q5 ha5)))))
  have hrows : linkRows (vsLayout bytecode σ) = n0 := by
    rw [linkRows, hTH]
    refine foldl_max_eq _ 0 n0 (Nat.zero_le _) (fun x hx ↦ ?_) (.inr ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
  -- `g^w`
  obtain ⟨ew, hew, x455⟩ := Digest.rc_const hm (c := 5) (by norm_num)
    (s35.trans (word_two_pow (a := 5) (by norm_num))) s38
  rw [s36] at s37
  have gw : σ (.n 409) = gen ^ (ew + 19) := by rw [eq_mul_winv19 s37, x455, pow_add]
  have glm : σ (.n 101) = gen ^ (vsLayout bytecode σ).logMemory := S.logMem
  have hlm30 : (vsLayout bytecode σ).logMemory ≤ 30 := by
    have := (Stack.buildLayout_some S.build).2.1; rw [hlmL]; exact this
  obtain ⟨em, hem, x460⟩ := rcN s39 s41
  have hwm : ew + 19 = em + (vsLayout bytecode σ).logMemory :=
    Digest.gen_pow_inj' (by omega) (by omega) (by rw [← gw, s40, x460, glm, pow_add])
  -- the cycles below `2^w`
  have hw4 : ew + 19 < sizeBits := lt_of_le_of_lt (by omega : ew + 19 ≤ 24) (by decide)
  have l465 : σ (.n 465) = gen ^ 2 ^ (ew + 19) := by
    have h43 : LoadHolds L.read (σ (.n 4) * gen ^ (ew + 19)) 0 (σ (.n 465)) := by
      rw [← gw, ← s42]; exact s43
    rw [loadHolds_mul_gen_pow, Nat.add_zero] at h43
    exact loadHolds_unique h43 (hexp.1 _ hw4)
  have asgp : ∀ {x : E}, C "assert_small_g_power" [x, σ (.n 4)] [] → ∃ e < 2 ^ 36, x = gen ^ e := by
    intro x hx
    exact ((assert_small_g_power_holds R.hκ (by omega) L x _ hexp []).mp (R.hle _ _ _ hx)).1
  obtain ⟨e2, he2, x468⟩ := asgp s47
  have hcycw : linkCycles (vsLayout bytecode σ) < 2 ^ (ew + 19) := by
    have hp : 1 ≤ 2 ^ (ew + 19) := Nat.one_le_two_pow
    have : gen ^ (2 ^ (ew + 19) - 1) = gen ^ (e2 + linkCycles (vsLayout bytecode σ)) := by
      rw [← pow_mul_ginv hp, ← l465, show Digest.ginvW = σ (.n 466) from s44.symm, ← s45, s46, x468,
        hgc, pow_add]
    have := gen_pow_inj (by have : 2 ^ (ew + 19) ≤ 2 ^ 24 := p24 (by omega); omega)
      (by omega) this
    omega
  -- the flag
  have hI := R.slice vsShapeIteT_eq
  simp only [vsShapeIteT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hI
  obtain ⟨-, hz1, hnz1⟩ := hI
  have hwide : ew + 19 ≤ bitLength (linkCycles (vsLayout bytecode σ)) ∨
      ew + 19 = (vsLayout bytecode σ).logMemory ∨ ew + 19 = 19 := by
    by_cases h471 : σ (.n 471) = 0
    · obtain ⟨t0, t1, t2, t3, t4, t5, -⟩ := hz1 h471
      left
      refine le_bitLength (by omega) ?_
      have g473 : σ (.n 473) = gen ^ (ew + 19 - 1) := by
        rw [t1, t0, gw]; exact pow_mul_ginv (by omega)
      have l475 : σ (.n 475) = gen ^ 2 ^ (ew + 19 - 1) := by
        have h3 : LoadHolds L.read (σ (.n 4) * gen ^ (ew + 19 - 1)) 0 (σ (.n 475)) := by
          rw [← g473, ← t2]; exact t3
        rw [loadHolds_mul_gen_pow, Nat.add_zero] at h3
        exact loadHolds_unique h3 (hexp.1 _ (by omega))
      obtain ⟨e3, he3, x476⟩ := asgp t5
      have : gen ^ linkCycles (vsLayout bytecode σ) = gen ^ (e3 + 2 ^ (ew + 19 - 1)) := by
        rw [← hgc, t4, x476, l475, pow_add]
      have := gen_pow_inj (by omega)
        (by have : 2 ^ (ew + 19 - 1) ≤ 2 ^ 24 := p24 (by omega); omega) this
      omega
    · obtain ⟨t0, t1, t2, t3, t4, t5, -⟩ := hnz1 h471
      right
      have h480 : σ (.n 480) = 0 := by rw [eq_of_add_zero t5, t4, word_zero]
      rw [t3, t0, t2, t1, show (524288 : ℕ) = 2 ^ 19 from rfl, word_two_pow (by norm_num)] at h480
      rcases mul_zero_cases h480 with h | h
      · left
        exact Digest.gen_pow_inj' (by omega) (by omega) (by rw [← gw, ← glm, eq_of_add_zero h])
      · right
        exact Digest.gen_pow_inj' (by omega) (by omega) (by rw [← gw, eq_of_add_zero h])
  have hpw : linkWidth (vsLayout bytecode σ) = ew + 19 := by
    have := bitLength_le hcycw
    simp only [linkWidth, pointerWidth, hlb, Nat.max_def]
    split_ifs <;> omega
  -- the chunks
  have hB := R.slice vsShapeBT_eq
  simp only [vsShapeBT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hB
  obtain ⟨u0, u1, ⟨j, hj, hsel, hcall⟩, -⟩ := hB
  have hj6 : j < 6 := by simpa using hj
  have hjw : j = ew := by
    refine Digest.gen_pow_inj' (by omega) (by omega) ?_
    rw [gen_pow_eq_ofK, ← hsel, u1, u0, gw, pow_mul_winv19 (by omega)]
    congr 1
  subst hjw
  obtain ⟨c, hc, hcd⟩ := chunkD_of_dispatch R.hle hj6 hcall
  have hn24 : n0 ≤ 24 := by omega
  simp only [Atom.Holds] at b119 b120 b132 b133 b145 b146 b158 b159 b171 b172
  refine ⟨hlb, htabL, by rw [hTR]; rfl, hlen, fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_,
    fun t ht ↦ ?_, hcyc24, hgc, by rw [link_bitsE_eq]; exact hcb, by rw [hrows]; exact gn,
    fun t ht ↦ ?_, by omega, by rw [hpw, gw], by omega, by omega, by omega,
    ⟨c, by rw [hpw]; exact hc, hcd⟩⟩
  · rw [hTR, hTH]
    interval_cases t <;> simpa
  · rw [hTH]
    interval_cases t <;> simpa
  · interval_cases t <;> simp only [Link.Arith.bitsVn, List.getD_cons_succ, List.getD_cons_zero]
    · rw [b120, b119]
    · rw [b133, b132]
    · rw [b146, b145]
    · rw [b159, b158]
    · rw [b172, b171]
  · rw [hTR, hTH]
    interval_cases t <;> simp only [Link.Arith.bitsVn, List.getD_cons_succ, List.getD_cons_zero] <;>
      exact ⟨by assumption, by assumption⟩
  · rw [hrows, hTH]
    interval_cases t <;> simp <;> omega

end
end LeanVM.Guest.B1.VerifySub
