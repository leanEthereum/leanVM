/-
  LeanVM.Guest.B1.VerifySub.Sizes

  `verify_sub`'s announced sizes: the tables' heights certified, the layout `buildLayout` gives,
  the stack's log, and `readAnnouncedSizes`' run.
-/

module

public import LeanVM.Guest.B1.VerifySub.Reads
public import LeanVM.Guest.B1.VerifySub.SizesRun
public import LeanVM.Guest.B1.Link.TableSize
public import LeanVM.Guest.B1.Stack.Certify
public import LeanVM.Guest.B1.Bits.GPower
public import LeanVM.Guest.Child.StackLog
public import LeanVM.Guest.B1.Common.MemSize
import LeanVM.Facts.Stack
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# The announced sizes

`vsHeightsT` (statements `106 .. 181`) certifies each table's log-height `h_t` against its row
count `R_t` (`table_size`): `h_t = max(log2_ceil(R_t), floor_t)`, `kb[2 + t] = g^(h_t)`
(`heightsFacts`). `vsStackT` (`431 .. 435`) places the stack (`certify_stack`) and range checks
`size_sel = g^(stackLog - 16)` below `g^15`. With the memory's log and the rate from
`g_power_of_word` (`ReadsFacts`), the announced sizes give a layout (`buildLayout`) whose stack has
`16 .. 30` variables: `phSizes`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_sub`'s statements 106 to 181. -/
def vsHeightsT : List Stmt := (
  .atom (.const (.n 140) (word 16777216 0)) ::
  .atom (.rangeCheck (.n 115) (.n 141) (.n 142) (.n 143) (.n 140)) ::
  .atom (.load (.n 144) (.n 56) 0) ::
  .dispatch (.n 115) ["table_size__L0", "table_size__L1", "table_size__L2", "table_size__L3", "table_size__L4", "table_size__L5", "table_size__L6", "table_size__L7", "table_size__L8", "table_size__L9", "table_size__L10", "table_size__L11", "table_size__L12", "table_size__L13", "table_size__L14", "table_size__L15", "table_size__L16", "table_size__L17", "table_size__L18", "table_size__L19", "table_size__L20", "table_size__L21", "table_size__L22", "table_size__L23", "table_size__L24"] [.n 144, .n 7] [.n 145, .n 146, .n 147] ::
  .atom (.const (.n 148) (word 1 0)) ::
  .atom (.assertEq (.n 146) (.n 148)) ::
  .atom (.const (.n 149) (word 0 0)) ::
  .atom (.add (.n 150) (.n 147) (.n 149)) ::
  .atom (.hint (.inverse (.n 150) (.n 151))) ::
  .atom (.assertNe (.n 150) (.n 151) (.n 152)) ::
  .atom (.const (.n 153) (word 16777216 0)) ::
  .atom (.rangeCheck (.n 116) (.n 154) (.n 155) (.n 156) (.n 153)) ::
  .atom (.load (.n 157) (.n 56) 1) ::
  .atom (.const (.n 158) (word 67108864 0)) ::
  .atom (.mul (.n 159) (.n 7) (.n 158)) ::
  .dispatch (.n 116) ["table_size__L0", "table_size__L1", "table_size__L2", "table_size__L3", "table_size__L4", "table_size__L5", "table_size__L6", "table_size__L7", "table_size__L8", "table_size__L9", "table_size__L10", "table_size__L11", "table_size__L12", "table_size__L13", "table_size__L14", "table_size__L15", "table_size__L16", "table_size__L17", "table_size__L18", "table_size__L19", "table_size__L20", "table_size__L21", "table_size__L22", "table_size__L23", "table_size__L24"] [.n 157, .n 159] [.n 160, .n 161, .n 162] ::
  .atom (.const (.n 163) (word 1 0)) ::
  .atom (.assertEq (.n 161) (.n 163)) ::
  .atom (.const (.n 164) (word 0 0)) ::
  .atom (.add (.n 165) (.n 162) (.n 164)) ::
  .atom (.hint (.inverse (.n 165) (.n 166))) ::
  .atom (.assertNe (.n 165) (.n 166) (.n 167)) ::
  .atom (.mul (.n 168) (.n 145) (.n 160)) ::
  .atom (.const (.n 169) (word 16777216 0)) ::
  .atom (.rangeCheck (.n 117) (.n 170) (.n 171) (.n 172) (.n 169)) ::
  .atom (.load (.n 173) (.n 56) 2) ::
  .atom (.const (.n 174) (word 67108864 0)) ::
  .atom (.mul (.n 175) (.n 159) (.n 174)) ::
  .dispatch (.n 117) ["table_size__L0", "table_size__L1", "table_size__L2", "table_size__L3", "table_size__L4", "table_size__L5", "table_size__L6", "table_size__L7", "table_size__L8", "table_size__L9", "table_size__L10", "table_size__L11", "table_size__L12", "table_size__L13", "table_size__L14", "table_size__L15", "table_size__L16", "table_size__L17", "table_size__L18", "table_size__L19", "table_size__L20", "table_size__L21", "table_size__L22", "table_size__L23", "table_size__L24"] [.n 173, .n 175] [.n 176, .n 177, .n 178] ::
  .atom (.const (.n 179) (word 1 0)) ::
  .atom (.assertEq (.n 177) (.n 179)) ::
  .atom (.const (.n 180) (word 0 0)) ::
  .atom (.add (.n 181) (.n 178) (.n 180)) ::
  .atom (.hint (.inverse (.n 181) (.n 182))) ::
  .atom (.assertNe (.n 181) (.n 182) (.n 183)) ::
  .atom (.mul (.n 184) (.n 168) (.n 176)) ::
  .atom (.const (.n 185) (word 16777216 0)) ::
  .atom (.rangeCheck (.n 118) (.n 186) (.n 187) (.n 188) (.n 185)) ::
  .atom (.load (.n 189) (.n 56) 3) ::
  .atom (.const (.n 190) (word 67108864 0)) ::
  .atom (.mul (.n 191) (.n 175) (.n 190)) ::
  .dispatch (.n 118) ["table_size__L0", "table_size__L1", "table_size__L2", "table_size__L3", "table_size__L4", "table_size__L5", "table_size__L6", "table_size__L7", "table_size__L8", "table_size__L9", "table_size__L10", "table_size__L11", "table_size__L12", "table_size__L13", "table_size__L14", "table_size__L15", "table_size__L16", "table_size__L17", "table_size__L18", "table_size__L19", "table_size__L20", "table_size__L21", "table_size__L22", "table_size__L23", "table_size__L24"] [.n 189, .n 191] [.n 192, .n 193, .n 194] ::
  .atom (.const (.n 195) (word 1 0)) ::
  .atom (.assertEq (.n 193) (.n 195)) ::
  .atom (.const (.n 196) (word 0 0)) ::
  .atom (.add (.n 197) (.n 194) (.n 196)) ::
  .atom (.hint (.inverse (.n 197) (.n 198))) ::
  .atom (.assertNe (.n 197) (.n 198) (.n 199)) ::
  .atom (.mul (.n 200) (.n 184) (.n 192)) ::
  .atom (.const (.n 201) (word 16777216 0)) ::
  .atom (.rangeCheck (.n 119) (.n 202) (.n 203) (.n 204) (.n 201)) ::
  .atom (.load (.n 205) (.n 56) 4) ::
  .atom (.const (.n 206) (word 67108864 0)) ::
  .atom (.mul (.n 207) (.n 191) (.n 206)) ::
  .dispatch (.n 119) ["table_size__L0", "table_size__L1", "table_size__L2", "table_size__L3", "table_size__L4", "table_size__L5", "table_size__L6", "table_size__L7", "table_size__L8", "table_size__L9", "table_size__L10", "table_size__L11", "table_size__L12", "table_size__L13", "table_size__L14", "table_size__L15", "table_size__L16", "table_size__L17", "table_size__L18", "table_size__L19", "table_size__L20", "table_size__L21", "table_size__L22", "table_size__L23", "table_size__L24"] [.n 205, .n 207] [.n 208, .n 209, .n 210] ::
  .atom (.const (.n 211) (word 1 0)) ::
  .atom (.assertEq (.n 209) (.n 211)) ::
  .atom (.const (.n 212) (word 0 0)) ::
  .atom (.add (.n 213) (.n 210) (.n 212)) ::
  .atom (.hint (.inverse (.n 213) (.n 214))) ::
  .atom (.assertNe (.n 213) (.n 214) (.n 215)) ::
  .atom (.mul (.n 216) (.n 200) (.n 208)) ::
  .atom (.const (.n 217) (word 16777216 0)) ::
  .atom (.rangeCheck (.n 120) (.n 218) (.n 219) (.n 220) (.n 217)) ::
  .atom (.load (.n 221) (.n 56) 5) ::
  .atom (.const (.n 222) (word 67108864 0)) ::
  .atom (.mul (.n 223) (.n 207) (.n 222)) ::
  .dispatch (.n 120) ["table_size__L0", "table_size__L1", "table_size__L2", "table_size__L3", "table_size__L4", "table_size__L5", "table_size__L6", "table_size__L7", "table_size__L8", "table_size__L9", "table_size__L10", "table_size__L11", "table_size__L12", "table_size__L13", "table_size__L14", "table_size__L15", "table_size__L16", "table_size__L17", "table_size__L18", "table_size__L19", "table_size__L20", "table_size__L21", "table_size__L22", "table_size__L23", "table_size__L24"] [.n 221, .n 223] [.n 224, .n 225, .n 226] ::
  .atom (.const (.n 227) (word 16777216 0)) ::
  .atom (.const (.n 228) (word 512 0)) ::
  .atom (.mul (.n 120) (.n 229) (.n 228)) ::
  .atom (.rangeCheck (.n 229) (.n 230) (.n 231) (.n 232) (.n 227)) ::
  .atom (.const (.n 233) (word 512 0)) ::
  .atom (.add (.n 234) (.n 120) (.n 233)) ::
  .ite (.n 234) [] [
    .atom (.const (.n 235) (word 1 0)),
    .atom (.assertEq (.n 225) (.n 235)),
    .atom (.const (.n 236) (word 0 0)),
    .atom (.add (.n 237) (.n 226) (.n 236)),
    .atom (.hint (.inverse (.n 237) (.n 238))),
    .atom (.assertNe (.n 237) (.n 238) (.n 239))] ::
  .atom (.mul (.n 240) (.n 216) (.n 224)) ::
  [])

theorem vsHeightsT_eq : (vsPre.drop 106).take 76 = vsHeightsT := stmtsEqb_sound (by decide +kernel)

/-- `verify_sub`'s statements 431 to 435. -/
def vsStackT : List Stmt := (
  .call "certify_stack" [.n 112, .n 4] [.n 485, .n 486, .n 487] ::
  .atom (.const (.n 488) (word 8198521646651277316 0)) ::
  .atom (.mul (.n 489) (.n 485) (.n 488)) ::
  .atom (.const (.n 490) (word 16384 0)) ::
  .atom (.rangeCheck (.n 489) (.n 491) (.n 492) (.n 493) (.n 490)) ::
  [])

theorem vsStackT_eq : (vsPre.drop 431).take 5 = vsStackT := stmtsEqb_sound (by decide +kernel)


/-! ## One table's height -/

theorem log2Ceil_of_cert {R j : ℕ} (h1 : R ≤ 2 ^ j) (h2 : j = 0 ∨ 2 ^ (j - 1) < R) :
    log2Ceil R = j := by
  have hle : log2Ceil R ≤ j := (log2Ceil_le_iff R j).2 h1
  rcases h2 with rfl | h2
  · omega
  · by_contra hne
    have : log2Ceil R ≤ j - 1 := by omega
    have := (log2Ceil_le_iff R (j - 1)).1 this
    omega

/-- **A `table_size` dispatch**: at the selector `g^j`, `j ≤ 24`, the specialization's meaning. -/
theorem ts_of_dispatch {κ : ℕ} (L : MemoryImage κ) {C : CallRel}
    (hle : CallRel.Le C (coreProgram.Rel L.read)) {fs : List String} (hfs : fs = Link.tsNames)
    {kb rows bits gr lead rest : E}
    (hd : ∃ (j : ℕ) (_ : j < fs.length), kb = ofK (addressOfIndex j) ∧
      C fs[j] [rows, bits] [gr, lead, rest]) :
    ∃ j ≤ 24, kb = gen ^ j ∧ Link.MeaningTS j L.read [rows, bits] [gr, lead, rest] := by
  subst hfs
  obtain ⟨j, hj, hx, hc⟩ := hd
  have hj' : j ≤ 24 := by simp [Link.tsNames] at hj; omega
  refine ⟨j, hj', by rw [hx, gen_pow_eq_ofK], Link.table_size_sound j hj' L.read _ _ ?_⟩
  rw [List.getD_eq_getElem _ _ hj]
  exact hle _ _ _ hc

/-- **A table's height, floor `0`**: `lead = 1` and `rest ≠ 0` asserted. -/
theorem height_floor0 {κ : ℕ} (L : MemoryImage κ) {C : CallRel}
    (hle : CallRel.Le C (coreProgram.Rel L.read)) {fs : List String} (hfs : fs = Link.tsNames)
    {kb rows bits gr lead rest : E}
    (hd : ∃ (j : ℕ) (_ : j < fs.length), kb = ofK (addressOfIndex j) ∧
      C fs[j] [rows, bits] [gr, lead, rest]) (hlead : lead = 1) (hrest : rest ≠ 0) :
    ∃ R h, h ≤ 24 ∧ kb = gen ^ h ∧ R ≤ 2 ^ h ∧ rows = eOfNat R ∧ gr = gen ^ R ∧
      h = max (log2Ceil R) 0 := by
  obtain ⟨j, hj, hkb, R, hR, hrows, -, -, gr', lead', rest', hrets, hgr, hcert⟩ :=
    ts_of_dispatch L hle hfs hd
  simp only [List.cons.injEq, and_true] at hrets
  obtain ⟨rfl, rfl, rfl⟩ := hrets
  refine ⟨R, j, hj, hkb, hR, hrows, hgr, ?_⟩
  rw [log2Ceil_of_cert hR (hcert.1 ⟨hlead, hrest⟩)]
  simp

theorem ne_of_assertNe {a inv p : E} (h : p = (a + 0) * inv ∧ p = 1) : a ≠ 0 := by
  rintro rfl
  rw [h.2, add_zero, zero_mul] at h
  exact one_ne_zero h.1

/-- `g^-16`, as the data writes it. -/
theorem word_ginv16_mul : word 8198521646651277316 0 * gen ^ 16 = 1 := by
  rw [show gen ^ 16 = ofK (K.ofBits 65536) by rw [← word_two_pow (a := 16) (by decide)]; exact word_eOfNat _,
    show word 8198521646651277316 0 = ofK (K.ofBits 8198521646651277316) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 8198521646651277316 * K.ofBits 65536 = 1 by decide +kernel, ofK_one]

theorem eq_of_add_zero {a b : E} (h : a + b = 0) : a = b := by
  have := congrArg (· + b) h
  simpa [add_assoc, e_add_self] using this

theorem lead_rest {lead c1 rest z s inv p : E} (h1 : c1 = word 1 0) (h2 : lead + c1 = 0)
    (h3 : z = word 0 0) (h4 : s = rest + z) (h5 : p = s * inv ∧ p = 1) : lead = 1 ∧ rest ≠ 0 := by
  refine ⟨by rw [eq_of_add_zero h2, h1, word_one], ?_⟩
  rintro rfl
  rw [h4, h3, word_zero, add_zero, zero_mul] at h5
  exact one_ne_zero (h5.1.symm.trans h5.2).symm

theorem memOk_of {κ : ℕ} (hκ1 : 1 ≤ κ) (hκ : κ ≤ 32) (L : MemoryImage κ) : Digest.MemOk L.read :=
  ⟨κ, hκ1, hκ, L, rfl⟩

/-- **The tables' heights**: each table's row count `R_t` and log-height
`h_t = max(log2_ceil(R_t), floor_t) ≤ 24`, `kb[2 + t] = g^(h_t)`, the count at `table_rows[t]`. -/
theorem heightsFacts {κ : ℕ} (hκ1 : 1 ≤ κ) (hκ : κ ≤ 32) (L : MemoryImage κ) {C : CallRel}
    (hle : CallRel.Le C (coreProgram.Rel L.read)) {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList C L.read σ vsHeightsT True kret) :
    ∃ R hs : List ℕ, R.length = nTables ∧
      hs = List.zipWith (fun r f ↦ max (log2Ceil r) f) R tableLogFloors ∧
      (∀ t < nTables, R.getD t 0 ≤ 2 ^ 24 ∧ hs.getD t 0 ≤ 24 ∧
        LoadHolds L.read (σ (.n (val% «verify_sub» "table_rows"))) t (eOfNat (R.getD t 0))) ∧
      (List.range nTables).map (fun t ↦ σ (.n (115 + t))) = hs.map (gen ^ ·) := by
  have hm := memOk_of hκ1 hκ L
  simp only [vsHeightsT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨b106, b107, b108, b109, b110, b111, b112, b113, b114, b115, b116, b117, b118, b119, b120, b121, b122, b123, b124, b125, b126, b127, b128, b129, b130, b131, b132, b133, b134, b135, b136, b137, b138, b139, b140, b141, b142, b143, b144, b145, b146, b147, b148, b149, b150, b151, b152, b153, b154, b155, b156, b157, b158, b159, b160, b161, b162, b163, b164, b165, b166, b167, b168, b169, b170, b171, b172, b173, b174, b175, b176, b177, b178, b179, -, -, b180n⟩ := h
  obtain ⟨R0, h0, hj0, hk0, hR0, hr0, -, he0⟩ := height_floor0 L hle rfl b109
    (lead_rest b110 b111 b112 b113 b115).1 (lead_rest b110 b111 b112 b113 b115).2
  obtain ⟨R1, h1, hj1, hk1, hR1, hr1, -, he1⟩ := height_floor0 L hle rfl b121
    (lead_rest b122 b123 b124 b125 b127).1 (lead_rest b122 b123 b124 b125 b127).2
  obtain ⟨R2, h2, hj2, hk2, hR2, hr2, -, he2⟩ := height_floor0 L hle rfl b134
    (lead_rest b135 b136 b137 b138 b140).1 (lead_rest b135 b136 b137 b138 b140).2
  obtain ⟨R3, h3, hj3, hk3, hR3, hr3, -, he3⟩ := height_floor0 L hle rfl b147
    (lead_rest b148 b149 b150 b151 b153).1 (lead_rest b148 b149 b150 b151 b153).2
  obtain ⟨R4, h4, hj4, hk4, hR4, hr4, -, he4⟩ := height_floor0 L hle rfl b160
    (lead_rest b161 b162 b163 b164 b166).1 (lead_rest b161 b162 b163 b164 b166).2
  -- the `KECCAK` table, floor `9`
  obtain ⟨j5, hj5, hk5, R5, hR5, hr5, -, -, gr5, lead5, rest5, hrets5, -, hcert5⟩ :=
    ts_of_dispatch L hle rfl b173
  simp only [List.cons.injEq, and_true] at hrets5
  obtain ⟨rfl, rfl, rfl⟩ := hrets5
  obtain ⟨e, he, h229⟩ := Digest.rc_const hm (c := 24) (by norm_num) (by rw [b174, show (16777216 : ℕ) = 2 ^ 24 from rfl, word_two_pow (by decide)]) b177
  have h228 : σ (.n 228) = gen ^ 9 := by rw [b175, show (512 : ℕ) = 2 ^ 9 from rfl, word_two_pow (by decide)]
  have hj9 : j5 = e + 9 := by
    have : gen ^ j5 = gen ^ (e + 9) := by rw [← hk5, b176, h229, h228, pow_add]
    exact Digest.gen_pow_inj' (by omega) (by omega) this
  have he5 : j5 = max (log2Ceil R5) 9 := by
    by_cases h0 : σ (.n 234) = 0
    · have h120 : σ (.n 120) = gen ^ 9 := by
        rw [b179, b178, show (512 : ℕ) = 2 ^ 9 from rfl, word_two_pow (by decide)] at h0
        exact eq_of_add_zero h0
      have : j5 = 9 := Digest.gen_pow_inj' (by omega) (by omega) (hk5.symm.trans h120)
      subst this
      have := (log2Ceil_le_iff R5 9).2 hR5
      omega
    · have hb := b180n h0
      obtain ⟨c1, c2, c3, c4, -, c6, -⟩ := hb
      obtain ⟨hl, hr⟩ := lead_rest c1 c2 c3 c4 c6
      rw [log2Ceil_of_cert hR5 (hcert5.1 ⟨hl, hr⟩)]
      omega
  refine ⟨[R0, R1, R2, R3, R4, R5], [h0, h1, h2, h3, h4, j5], rfl, ?_, fun t ht ↦ ?_, ?_⟩
  · simp only [List.zipWith, tableLogFloors, keccakMinStepsLog, he0, he1, he2, he3, he4, he5]
  · have p2 : ∀ {a : ℕ}, a ≤ 24 → 2 ^ a ≤ 2 ^ 24 := fun ha ↦ Nat.pow_le_pow_right (by norm_num) ha
    simp only [nTables] at ht
    interval_cases t
    · exact ⟨(hR0.trans (p2 hj0)), hj0, hr0 ▸ b108⟩
    · exact ⟨(hR1.trans (p2 hj1)), hj1, hr1 ▸ b118⟩
    · exact ⟨(hR2.trans (p2 hj2)), hj2, hr2 ▸ b131⟩
    · exact ⟨(hR3.trans (p2 hj3)), hj3, hr3 ▸ b144⟩
    · exact ⟨(hR4.trans (p2 hj4)), hj4, hr4 ▸ b157⟩
    · exact ⟨(hR5.trans (p2 hj5)), hj5, hr5 ▸ b170⟩
  · simp only [nTables, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append]
    rw [hk0, hk1, hk2, hk3, hk4, hk5]

/-! ## The layout -/

theorem kToNat_eOfNat {n : ℕ} (h : n < 2 ^ 64) : kToNat ((eOfNat n).limb 0) = n := by
  rw [eOfNat_eq_ofLimbs, ofLimbs_limb0, kToNat_ofBits, Nat.mod_eq_of_lt h]

theorem eOfNat_limb1 (n : ℕ) : (eOfNat n).limb 1 = 0 := by
  rw [eOfNat_eq_ofLimbs, ofLimbs_limb1]

/-- A word `g_power_of_word` reads: a small number's, its power returned. -/
theorem gpow_word {rd : Reader} {x r : E} (h : coreProgram.Rel rd "g_power_of_word" [x] [r]) :
    ∃ n < 2 ^ 6, x = eOfNat n ∧ r = gen ^ n := by
  obtain ⟨n, hn, hx, hr⟩ := (g_power_of_word_holds rd [x] [r]).mp h
  exact ⟨n, hn, hx, by simpa using hr⟩

/-- The stack's log is at most the largest layout's. -/
theorem stackLog_lt {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) : layout.stackLog < 2 ^ 34 := by
  obtain ⟨-, hlm, -, -, hh30, hsl, -⟩ := Stack.buildLayout_some h
  rw [hsl]
  have hle : (stack (columnKappas tables lm layout.tableLogHeights)).2 ≤
      (stack (columnKappas tables 30 (List.replicate nTables 30))).2 :=
    Child.stack_snd_mono fun b _ ↦ Child.forall₂_getD (Child.columnKappas_forall₂ tables hlm fun i ↦ by
      by_cases hi : i < nTables
      · have e : (List.replicate nTables 30).getD i 0 = 30 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left (by simpa using hi)]; rfl
        rw [e]; exact hh30 i hi
      · have hl : layout.tableLogHeights.length ≤ nTables := by
          obtain ⟨-, -, -, hth, -⟩ := Stack.buildLayout_some h
          rw [hth, List.length_zipWith]
          exact min_le_right _ _
        rw [List.getD_eq_default _ _ (by omega)]
        exact Nat.zero_le _) b.column
  have hS : ((stackBlocks.map fun b ↦ (columnKappas tables 30 (List.replicate nTables 30)).getD
      b.column 0).map fun k ↦ 2 ^ k).sum ≤ 2 ^ 42 := by decide +kernel
  have : (stack (columnKappas tables 30 (List.replicate nTables 30))).2 ≤ 42 := by
    rw [Stack.stack_eq, stackOffsets_snd]
    exact max_le (by decide) ((log2Ceil_le_iff _ _).2 hS)
  omega

/-- **What the announced sizes give**: the layout `buildLayout` builds from them, the rate in
`1 .. 4`, the stack placed by `certify_stack` with `16 .. 30` variables, the dispatches' selectors,
and the eight words' high limbs zero. -/
structure SizesOk (bytecode : List K) (rd : Reader) (σ : Val) : Prop where
  build : buildLayout bytecode (vsLogMem σ) (vsRows σ) = some (vsLayout bytecode σ)
  lir1 : 1 ≤ vsLir σ
  lir4 : vsLir σ ≤ 4
  st1 : Whir.minOpenLog ≤ (vsLayout bytecode σ).stackLog
  st2 : (vsLayout bytecode σ).stackLog ≤ 30
  sizeSel : σ (.n (val% «verify_sub» "size_sel")) =
    ofK (addressOfIndex ((vsLayout bytecode σ).stackLog - Whir.minOpenLog))
  rateSel : σ (.n (val% «verify_sub» "rate_sel")) = Whir.rateSel (vsLir σ)
  hi : ∀ x ∈ vsAnnounced σ, x.limb 1 = 0
  placed : Stack.StackPlaced rd (vsLayout bytecode σ) (σ (.n (val% «verify_sub» "gmv")))
    (σ (.n (val% «verify_sub» "offs"))) (σ (.n (val% «verify_sub» "kaps")))
  heights : (List.range nTables).map (fun t ↦ σ (.n (115 + t))) =
    (vsLayout bytecode σ).tableLogHeights.map (gen ^ ·)
  heights24 : ∀ t < nTables, (vsLayout bytecode σ).tableLogHeights.getD t 0 ≤ 24
  logMem : σ (.n (val% «verify_sub» "g_log_mem")) = gen ^ (vsLayout bytecode σ).logMemory

theorem sizesOk {κ : ℕ} (hκ11 : 11 ≤ κ) (hκ : κ ≤ 32) (L : MemoryImage κ) {C : CallRel}
    (hle : CallRel.Le C (coreProgram.Rel L.read)) {σ : Val} {kret : List E → Prop}
    {bytecode : List K} (hbl : bytecode.length = 2 ^ (Main.bytecodeLog + bytecodeSlotBits))
    (hexp : ExpTables L.read (σ (.n (val% «verify_sub» "g_squares"))))
    (hr : Stmt.HoldsList C L.read σ vsReadsT True kret)
    (hh : Stmt.HoldsList C L.read σ vsHeightsT True kret)
    (hs : Stmt.HoldsList C L.read σ vsStackT True kret) : SizesOk bytecode L.read σ := by
  have hm := memOk_of (by omega) hκ L
  have F := readsFacts hr
  obtain ⟨R, hgt, hRl, hhs, hR, hkb⟩ := heightsFacts (by omega) hκ L hle hh
  -- the memory's log
  obtain ⟨n, hn, hx1, hglm⟩ := gpow_word (hle _ _ _ F.memCall)
  obtain ⟨e1, he1, h1⟩ := Digest.rc_const hm (c := 30) (by norm_num) rfl F.memRc
  obtain ⟨e2, he2, h2⟩ := Digest.rc_const hm (c := 32) (by norm_num) rfl F.memRc2
  have hn30 : n = e1 := Digest.gen_pow_inj' (by omega) (by omega) (hglm.symm.trans h1)
  have hn1 : n = e2 + 1 := Digest.gen_pow_inj' (by omega) (by omega)
    (by rw [← hglm, F.memMul, h2, pow_succ])
  -- the rate
  obtain ⟨m, hm64, hx8, h94⟩ := gpow_word (hle _ _ _ F.rateCall)
  obtain ⟨e3, he3, h3⟩ := Digest.rc_const hm (c := 3) (by norm_num) rfl F.rateRc
  have hm1 : m = e3 + 1 := Digest.gen_pow_inj' (by omega) (by omega)
    (by rw [← h94, F.rateMul, h3, pow_succ])
  have hlm : vsLogMem σ = n := by
    rw [vsLogMem, show σ (.n (val% «verify_sub» "x@1")) = σ (.n 57) from rfl, hx1, kToNat_eOfNat (by omega)]
  have hlir : vsLir σ = m := by
    rw [vsLir, show σ (.n (val% «verify_sub» "x@8")) = σ (.n 91) from rfl, hx8, kToNat_eOfNat (by omega)]
  -- the rows
  have hxs : ∀ t < nTables, (vsAnnounced σ).getD (t + 1) 0 = eOfNat (R.getD t 0) :=
    fun t ht ↦ loadHolds_unique (F.rows t ht) (hR t ht).2.2
  have hrows : vsRows σ = R := by
    have e1 : vsRows σ = (List.range nTables).map fun t ↦
        kToNat (((vsAnnounced σ).getD (t + 1) 0).limb 0) := rfl
    have e2 : R = (List.range nTables).map fun t ↦ R.getD t 0 := by
      apply List.ext_getElem (by simp [hRl])
      intro t h1 h2
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    rw [e1, e2, List.map_inj_left]
    intro t ht
    rw [List.mem_range] at ht
    rw [hxs t ht, kToNat_eOfNat (by have := (hR t ht).1; omega)]
  -- the layout
  have hlog : log2Strict bytecode.length = some (Main.bytecodeLog + bytecodeSlotBits) := by
    rw [hbl]; decide
  obtain ⟨L0, hL0⟩ : ∃ L0, buildLayout bytecode n R = some L0 := by
    unfold buildLayout
    rw [hlog]
    simp only
    split_ifs with hc
    · exact ⟨_, rfl⟩
    refine absurd ⟨by simp [minLogMemory]; omega, by simp [maxLogMemory]; omega,
      List.all_eq_true.mpr fun r hr ↦ by
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hr
        have := (hR t (by omega)).1
        rw [List.getD_eq_getElem _ _ ht] at this
        exact decide_eq_true (this.trans (Nat.pow_le_pow_right (by norm_num) (by simp [maxTableLog]))),
      by decide, by decide, by rw [hRl]⟩ hc
  have hvl : vsLayout bytecode σ = L0 := by rw [vsLayout, hlm, hrows, hL0]; rfl
  obtain ⟨hlmL, -, -, hthL, -, -, -⟩ := Stack.buildLayout_some hL0
  have hheights : L0.tableLogHeights = hgt := by rw [hthL, hhs]
  -- the stack
  simp only [vsStackT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hs
  obtain ⟨c431, a432, a433, a434, a435, -⟩ := hs
  have hkbR : ReadsAt L.read (σ (.n 112)) (Stack.kappaSources L0.logMemory L0.tableLogHeights) := by
    have e : Stack.kappaSources L0.logMemory L0.tableLogHeights =
        (List.range 8).map fun i ↦ σ (.n (113 + i)) := by
      rw [hheights, hlmL, Stack.kappaSources]
      apply List.ext_getElem (by simp [nTables])
      intro i h1 h2
      simp only [List.length_cons, List.length_map, List.length_range, nTables] at h1
      have e6 : ∀ t < nTables, σ (.n (115 + t)) = gen ^ hgt.getD t 0 := by
        intro t ht
        have := congrArg (fun l ↦ l.getD t 0) hkb
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht,
          Option.map_some, Option.getD_some] at this
        rw [this]
        rcases h : hgt[t]? with _ | x
        · have : hgt.length = nTables := by rw [hhs, List.length_zipWith, hRl]; rfl
          rw [List.getElem?_eq_none_iff] at h; omega
        · simp [h]
      have k113 := F.kb.1
      have k114 := F.kb.2.1
      interval_cases i
      · exact k113.symm
      · exact (k114.trans hglm).symm
      · exact (e6 0 (by decide)).symm
      · exact (e6 1 (by decide)).symm
      · exact (e6 2 (by decide)).symm
      · exact (e6 3 (by decide)).symm
      · exact (e6 4 (by decide)).symm
      · exact (e6 5 (by decide)).symm
    rw [e]; exact F.kb.2.2
  obtain ⟨gmv, offs, kaps, hrets, hplaced⟩ := Stack.certify_stack_sound hκ11 hκ L _ _
    (hle _ _ _ c431) bytecode n R L0 hL0 hexp hkbR
  simp only [List.cons.injEq, and_true] at hrets
  obtain ⟨e485, e486, e487⟩ := hrets
  obtain ⟨e4, he4, h4⟩ := Digest.rc_const hm (c := 14) (by norm_num)
    (by rw [a434, show (16384 : ℕ) = 2 ^ 14 from rfl, word_two_pow (by decide)]) a435
  have hst := stackLog_lt hL0
  have hsl : L0.stackLog = e4 + 16 := by
    have : gen ^ L0.stackLog = gen ^ (e4 + 16) := by
      rw [pow_add, ← h4, a433, a432, e485, hplaced.1, mul_assoc, word_ginv16_mul, mul_one]
    exact Digest.gen_pow_inj' hst (by omega) this
  subst hvl
  refine ⟨by rw [hlm, hrows]; exact hL0, by omega, by omega, by simp [Whir.minOpenLog]; omega,
    by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4, gen_pow_eq_ofK]; congr 2; simp [Whir.minOpenLog]; omega
  · rw [h3, Whir.rateSel, gen_pow_eq_ofK, hlir]; congr 2; omega
  · intro x hx
    simp only [vsAnnounced, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show σ (.n (val% «verify_sub» "x@1")) = σ (.n 57) from rfl, hx1, eOfNat_limb1]
    · have e : σ (.n 60) = _ := hxs 0 (by decide)
      rw [e, eOfNat_limb1]
    · have e : σ (.n 63) = _ := hxs 1 (by decide)
      rw [e, eOfNat_limb1]
    · have e : σ (.n 66) = _ := hxs 2 (by decide)
      rw [e, eOfNat_limb1]
    · have e : σ (.n 82) = _ := hxs 3 (by decide)
      rw [e, eOfNat_limb1]
    · have e : σ (.n 85) = _ := hxs 4 (by decide)
      rw [e, eOfNat_limb1]
    · have e : σ (.n 88) = _ := hxs 5 (by decide)
      rw [e, eOfNat_limb1]
    · rw [show σ (.n (val% «verify_sub» "x@8")) = σ (.n 91) from rfl, hx8, eOfNat_limb1]
  · rw [← e485, ← e486, ← e487] at hplaced; exact hplaced
  · rw [hkb, hheights]
  · intro t ht; rw [hheights]; exact (hR t ht).2.1
  · rw [hglm, hlmL]

/-- The exponent tables at `g_squares`, and a memory of at least `2^11` words, from `VsRun`. -/
theorem VsRun.pre {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {V : FrameMap}
    {σ : Val} {rets : List E} (R : VsRun bytecode L C V σ rets) :
    ExpTables L.read (σ (.n (val% «verify_sub» "g_squares"))) ∧
      ExpWinTab L.read (σ (.n (val% «verify_sub» "g_squares"))) ∧ 11 ≤ κ := by
  have h := R.hpre
  rw [show (fn% «verify_sub»).params.map σ = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4),
    σ (.n 5)] from rfl] at h
  exact ⟨h.1, h.2, winTabBits_le_of_winTabs R.hκ L (winTabs_of_expWinTab h.2)⟩

theorem VsRun.sizesOk {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel}
    {V : FrameMap} {σ : Val} {rets : List E} (R : VsRun bytecode L C V σ rets) :
    SizesOk bytecode L.read σ :=
  VerifySub.sizesOk R.pre.2.2 R.hκ L R.hle R.hbl R.pre.1 (R.slice vsReadsT_eq) (R.slice vsHeightsT_eq)
    (R.slice vsStackT_eq)

/-- **The announced sizes**, sound. -/
theorem phSizes : PhSizes := by
  intro bytecode κ L C V σ rets R
  have S := R.sizesOk
  have F := readsFacts (R.slice vsReadsT_eq)
  refine ⟨F.words, ?_, S.build, S.lir1, S.lir4, S.st1, S.st2, S.sizeSel, S.rateSel⟩
  have h := runsTo_readAnnouncedSizes bytecode (vsF0 σ) (vsAnnounced σ) rfl S.hi S.build S.lir1 S.lir4
    S.st1 S.st2
  rw [F.absorb] at h
  exact h

end
end LeanVM.Guest.B1.VerifySub
