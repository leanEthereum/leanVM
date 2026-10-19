/-
  LeanVM.Guest.B1.Tables.VerifyTablesSel

  `verify_tables`' block selectors: the bits of a block's offset above its log-height, pinned by
  rebuilding the offset, and their equality weight against the bus point.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesZc

/-!
# The blocks' selectors (G:1572-1594)

For a push or count block of log-height `κ` at offset `off`, `verify_tables` decomposes `off`
into bits by hint, and over the `μ - κ` coordinates of the bus point above `κ` (`μ = |point|`)
multiplies `eq_chain` by `1 + bit + zeta[κ + k]` and `goff_chain` by `1 + bit·(g^(2^(κ+k)) + 1)`,
each bit pinned boolean (`__loop12`, … `__loop78`, one body, `selPre`). The rebuilt offset must be
`block_off_g[b]`: the bits are the offset's (`sel_rebuild`), so the chain's end is the block's
placement's `eqAbove` (`eqAbove_prod`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The selector loops -/

/-- The 65 selector loops, one per push and count block, in block order. -/
def selNames : List String :=
  ["__loop12", "__loop13", "__loop15", "__loop17", "__loop18", "__loop19",
    "__loop20", "__loop21", "__loop22", "__loop23", "__loop24", "__loop25",
    "__loop26", "__loop27", "__loop28", "__loop29", "__loop30", "__loop31",
    "__loop32", "__loop33", "__loop34", "__loop35", "__loop36", "__loop37",
    "__loop38", "__loop39", "__loop40", "__loop41", "__loop42", "__loop43",
    "__loop44", "__loop45", "__loop46", "__loop47", "__loop48", "__loop49",
    "__loop50", "__loop51", "__loop52", "__loop53", "__loop54", "__loop55",
    "__loop56", "__loop57", "__loop58", "__loop59", "__loop60", "__loop61",
    "__loop62", "__loop63", "__loop64", "__loop65", "__loop66", "__loop67",
    "__loop68", "__loop69", "__loop70", "__loop71", "__loop72", "__loop73",
    "__loop74", "__loop75", "__loop76", "__loop77", "__loop78"]

/-- A selector loop's statements before its `ret`, its own name `self`. -/
def selPre (self : String) : List Stmt :=
  [.atom (.mul (.n 8) (.n 2) (.n 0)), .atom (.load (.n 9) (.n 8) 0),
    .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 2) (.n 0)),
    .atom (.load (.n 10) (.n 11) 0), .atom (.mul (.n 12) (.n 3) (.n 0)),
    .atom (.load (.n 13) (.n 12) 0), .atom (.const (.n 14) (word 1 0 0)),
    .atom (.add (.n 15) (.n 14) (.n 9)), .atom (.mul (.n 16) (.n 4) (.n 0)),
    .atom (.load (.n 17) (.n 16) 0), .atom (.add (.n 18) (.n 15) (.n 17)),
    .atom (.mul (.n 19) (.n 13) (.n 18)), .atom (.mul (.n 20) (.n 3) (.n 0)),
    .atom (.load (.n 19) (.n 20) 1), .atom (.mul (.n 21) (.n 5) (.n 0)),
    .atom (.load (.n 22) (.n 21) 0), .atom (.const (.n 23) (word 1 0 0)),
    .atom (.mul (.n 24) (.n 7) (.n 0)), .atom (.mul (.n 25) (.n 6) (.n 24)),
    .atom (.load (.n 26) (.n 25) 0), .atom (.const (.n 27) (word 1 0 0)),
    .atom (.add (.n 28) (.n 26) (.n 27)), .atom (.mul (.n 29) (.n 9) (.n 28)),
    .atom (.add (.n 30) (.n 23) (.n 29)), .atom (.mul (.n 31) (.n 22) (.n 30)),
    .atom (.mul (.n 32) (.n 5) (.n 0)), .atom (.load (.n 31) (.n 32) 1),
    .atom (.const (.n 33) (word 2 0 0)), .atom (.mul (.n 34) (.n 0) (.n 33)),
    .atom (.add (.n 35) (.n 34) (.n 1)), .atom (.const (.n 36) (word 2 0 0)),
    .atom (.mul (.n 37) (.n 0) (.n 36)),
    .callIf (.n 35) self [.n 37, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]]

/-- A selector loop's shape: found, eight parameters, the body `selPre`. -/
noncomputable def selOk (self : String) : Bool :=
  match coreProgram.find? self with
  | some f => decide (f.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]) &&
      stmtsEqb f.body (selPre self ++ [.ret []])
  | none => false

theorem sel_ok : ∀ i < 65, selOk (selNames.getD i "") = true := by decide +kernel

/-- One iteration of a selector loop at `x`: the bit at `sel_bits[x]`, pinned boolean; the
equality chain and the rebuilt offset one step on. -/
def SelBody (rd : Reader) (sb ec zh go sq ka x : E) : Prop :=
  ∃ bit e z o s, LoadHolds rd (sb * x) 0 bit ∧ bit * bit = bit ∧ LoadHolds rd (ec * x) 0 e ∧
    LoadHolds rd (zh * x) 0 z ∧ LoadHolds rd (ec * x) 1 (e * (1 + bit + z)) ∧
    LoadHolds rd (go * x) 0 o ∧ LoadHolds rd (sq * (ka * x)) 0 s ∧
    LoadHolds rd (go * x) 1 (o * (1 + bit * (s + 1)))

theorem sel_step {rd : Reader} {self : String} (hok : selOk self = true) {x N sb ec zh go sq ka : E}
    (h : coreProgram.Rel rd self [x, N, sb, ec, zh, go, sq, ka] []) :
    SelBody rd sb ec zh go sq ka x ∧
      (x * gen + N ≠ 0 → coreProgram.Rel rd self [x * gen, N, sb, ec, zh, go, sq, ka] []) := by
  unfold selOk at hok
  split at hok
  · next f hf =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hpar, hbody⟩ := hok
    have hnr : Stmt.noRetList (selPre self) = true := by simp [selPre, Stmt.noRetList, Stmt.noRet]
    obtain ⟨σ, hp, hb, -⟩ := rel_pre hf (stmtsEqb_sound hbody) hnr h
    simp only [hpar, List.map_cons, List.map_nil, List.cons.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hp
    simp only [selPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one, word_gen,
      List.map_cons, List.map_nil] at hb
    obtain ⟨a8, l9, a10, a11, l10, a12, l13, c14, a15, a16, l17, a18, a19, a20, l19, a21, l22, c23,
      a24, a25, l26, c27, a28, a29, a30, a31, a32, l31, c33, a34, a35, c36, a37, hc⟩ := hb
    refine ⟨⟨σ (.n 9), σ (.n 13), σ (.n 17), σ (.n 22), σ (.n 26), by rw [← a8]; exact l9, ?_,
      by rw [← a12]; exact l13, by rw [← a16]; exact l17, ?_, by rw [← a21]; exact l22,
      by rw [← a24, ← a25]; exact l26, ?_⟩, fun hne => ?_⟩
    · rw [a11, ← a8] at l10
      rw [← a10]; exact loadHolds_unique l10 l9
    · rw [← a20]
      rw [a19, a18, a15, c14] at l19
      exact l19
    · rw [← a32]
      rw [a31, a30, a29, a28, c27, c23] at l31
      exact l31
    · have := hc.2 (by rw [a35, a34, c33]; exact hne)
      rw [a37, c36] at this
      exact this
  · exact absurd hok (by simp)

/-! ## Offsets and selectors -/

/-- **`eqAbove` as a product** over the coordinates from `κ`, for a point of `M`. -/
theorem eqAbove_prod {M κ off : ℕ} (zs : List E) (hzs : zs.length = M) :
    ({ vars := κ, index := off } : Placement).eqAbove zs =
      ∏ t ∈ Finset.range (M - κ), (1 + bitE (off.testBit (κ + t)) + zs.getD (κ + t) 0) := by
  simp only [Placement.eqAbove, Nat.zero_add, Nat.sub_zero, hzs]
  have hl : (selectorPoint (off >>> κ) (M - κ)).length = M - κ := by simp [selectorPoint]
  have hr : (zs.drop κ).length = M - κ := by simp [hzs]
  have h := eqEval_take (selectorPoint (off >>> κ) (M - κ)) (zs.drop κ) (M - κ) (by omega)
    (by omega)
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at h
  rw [h]
  refine Finset.prod_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  have h2 : (List.drop κ zs).getD t 0 = zs.getD (κ + t) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [h2]
  congr 2
  simp only [selectorPoint, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht',
    Option.map_some, Option.getD_some, eOfNat_shift_mod, Nat.testBit_shiftRight]

/-- The rebuilt offset of bits Boolean from `κ` up to `M`: a power of `g` below `2^M`, aligned to
`2^κ`, whose bits the bits are. -/
theorem sel_rebuild {M κ : ℕ} (hκ : κ ≤ M) {b : ℕ → E}
    (hb : ∀ t < M - κ, b (κ + t) * b (κ + t) = b (κ + t)) :
    ∃ off < 2 ^ M, 2 ^ κ ∣ off ∧
      ∏ t ∈ Finset.range (M - κ), (1 + b (κ + t) * (gen ^ 2 ^ (κ + t) + 1)) = gen ^ off ∧
      ∀ t < M - κ, b (κ + t) = bitE (off.testBit (κ + t)) := by
  set b' : ℕ → E := fun k => if k < κ then 0 else b k
  have hb' : ∀ j < M, b' j * b' j = b' j := fun j hj => by
    simp only [b']
    split
    · simp
    · have := hb (j - κ) (by omega); rwa [show κ + (j - κ) = j by omega] at this
  have hprod := prod_gen_pow_of_bool hb'
  have hsplit : ∏ j ∈ Finset.range M, (1 + b' j * (gen ^ 2 ^ j + 1)) =
      ∏ t ∈ Finset.range (M - κ), (1 + b' (κ + t) * (gen ^ 2 ^ (κ + t) + 1)) := by
    conv_lhs => rw [show M = κ + (M - κ) by omega]
    rw [Finset.prod_range_add, Finset.prod_eq_one (fun j hj => by
      simp [b', Finset.mem_range.mp hj]), one_mul]
  rw [hsplit] at hprod
  set off := bitsVal (fun j => decide (b' j = 1)) M
  have hoff : off < 2 ^ M := bitsVal_lt _ _
  have htb : ∀ k, off.testBit k = (decide (k < M) && decide (b' k = 1)) := fun k => by
    simp only [off, testBit_bitsVal]
  refine ⟨off, hoff, ?_, ?_, fun t ht => ?_⟩
  · refine Nat.dvd_of_mod_eq_zero (Nat.eq_of_testBit_eq fun i => ?_)
    rw [Nat.testBit_mod_two_pow, htb, Nat.zero_testBit]
    by_cases hi : i < κ <;> simp [hi, b']
  · rw [← hprod]
    exact Finset.prod_congr rfl fun t ht => by
      simp [b', show ¬ κ + t < κ by omega]
  · rw [htb]
    simp only [b', show ¬ κ + t < κ by omega, ↓reduceIte, show κ + t < M by omega, decide_true,
      Bool.true_and]
    exact bitE_of_mul_self (hb t ht)

/-! ## A block's selector in the body -/

/-- The selector loops' blocks, in order. -/
def selBlk : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84,
    85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
    101]

/-- Each selector's first statement. -/
def selStmt : List ℕ :=
  [1577, 1616, 1724, 1808, 1838, 1868, 1898, 1928, 1958, 1988, 2018, 2048,
    2078, 2108, 2138, 2168, 2198, 2228, 2258, 2288, 2318, 2348, 2378, 2408,
    2438, 2468, 2498, 2528, 2558, 2588, 2618, 2648, 2678, 2708, 2738, 2768,
    2798, 3397, 3426, 3456, 3486, 3516, 3546, 3576, 3606, 3636, 3666, 3696,
    3726, 3756, 3786, 3816, 3846, 3876, 3906, 3936, 3966, 3996, 4026, 4056,
    4086, 4116, 4146, 4176, 4206]

/-- Each selector's first value. -/
def selVal : List ℕ :=
  [1855, 1893, 1997, 2077, 2106, 2135, 2164, 2193, 2222, 2251, 2280, 2309,
    2338, 2367, 2396, 2425, 2454, 2483, 2512, 2541, 2570, 2599, 2628, 2657,
    2686, 2715, 2744, 2773, 2802, 2831, 2860, 2889, 2918, 2947, 2976, 3005,
    3034, 3706, 3734, 3763, 3792, 3821, 3850, 3879, 3908, 3937, 3966, 3995,
    4024, 4053, 4082, 4111, 4140, 4169, 4198, 4227, 4256, 4285, 4314, 4343,
    4372, 4401, 4430, 4459, 4488]

/-- A push or count block's selector, block `b`, from value `v`, its loop `self` (G:1572-1594). -/
def selT (b v : ℕ) (self : String) : List Stmt :=
  [.atom (.load (.n v) (.n 9) b), .atom (.const (.n (v + 1)) (word 8589934592 0 0)),
    .atom (.rangeCheck (.n v) (.n (v + 2)) (.n (v + 3)) (.n (v + 4)) (.n (v + 1))),
    .atom (.mul (.n 6) (.n (v + 5)) (.n v)), .atom (.const (.n (v + 6)) (word 8589934592 0 0)),
    .atom (.rangeCheck (.n (v + 5)) (.n (v + 7)) (.n (v + 8)) (.n (v + 9)) (.n (v + 6))),
    .atom (.mul (.n (v + 10)) (.n 5) (.n v)), .atom (.const (.n (v + 11)) (word 17179869184 0 0)),
    .atom (.hint (.allocDyn (.n (v + 12)) (.n (v + 11)))), .atom (.load (.n (v + 13)) (.n 128) b),
    .atom (.hint (.bitsExp (.n (v + 13)) 34 (.heap (.n (v + 12)) 0 34))),
    .atom (.mul (.n (v + 14)) (.n (v + 12)) (.n v)), .atom (.hint (.alloc (.n (v + 15)) 42)),
    .atom (.hint (.alloc (.n (v + 16)) 42)), .atom (.const (.n (v + 17)) (word 1 0 0)),
    .atom (.load (.n (v + 17)) (.n (v + 15)) 0), .atom (.const (.n (v + 18)) (word 1 0 0)),
    .atom (.load (.n (v + 18)) (.n (v + 16)) 0), .atom (.const (.n (v + 19)) (word 1 0 0)),
    .atom (.add (.n (v + 20)) (.n (v + 19)) (.n (v + 5))), .atom (.const (.n (v + 21)) (word 1 0 0)),
    .callIf (.n (v + 20)) self
      [.n (v + 21), .n (v + 5), .n (v + 14), .n (v + 15), .n (v + 10), .n (v + 16), .n 10, .n v],
    .atom (.mul (.n (v + 22)) (.n (v + 15)) (.n (v + 5))), .atom (.load (.n (v + 23)) (.n (v + 22)) 0),
    .atom (.mul (.n (v + 24)) (.n (v + 16)) (.n (v + 5))), .atom (.load (.n (v + 25)) (.n (v + 24)) 0),
    .atom (.load (.n (v + 26)) (.n 128) b), .atom (.assertEq (.n (v + 25)) (.n (v + 26)))]

theorem sel_blocks : ∀ i < 65, stmtsEqb (selT (selBlk.getD i 0) (selVal.getD i 0) (selNames.getD i ""))
    ((vtPre.drop (selStmt.getD i 0)).take 28) = true := by decide +kernel


theorem word_g34 : word 17179869184 0 0 = gen ^ 34 := word_two_pow (a := 34) (by decide)

/-- **A block's selector** (G:1572-1594): block `b = selBlk i` of log-height `k < 34`, at offset
`off`, with the bus point at `zeta` of length `μ = log g_bus_mu`: `k ≤ μ`, the offset is below
`2^μ` and aligned to `2^k`, and the selector at value `selVal i + 23` is the placement's
`eqAbove` at the point. -/
theorem vt_sel {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {σ : Val} (h : VtHolds Lm.read σ)
    {i : ℕ} (hi : i < 65) {k off : ℕ} (hk : k < 34)
    (hbk : LoadHolds Lm.read (σ (.n 9)) (selBlk.getD i 0) (gen ^ k))
    (hoff : LoadHolds Lm.read (σ (.n 128)) (selBlk.getD i 0) (gen ^ off)) (hoff62 : off < 2 ^ 62)
    {point : List E} (hz : ReadsAt Lm.read (σ (.n 5)) point) (hmu : σ (.n 6) = gen ^ point.length)
    (hml : point.length < 33) (hsq : ∀ j < 34, LoadHolds Lm.read (σ (.n 10)) j (gen ^ 2 ^ j)) :
    k ≤ point.length ∧ off < 2 ^ point.length ∧ 2 ^ k ∣ off ∧
      σ (.n (selVal.getD i 0 + 23)) = ({ vars := k, index := off } : Placement).eqAbove point := by
  set b := selBlk.getD i 0
  set v := selVal.getD i 0
  obtain ⟨kr, hb⟩ := h.slice _ _ (sel_blocks i hi)
  simp only [selT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and, word_one,
    List.map_cons, List.map_nil] at hb
  obtain ⟨l0, -, -, m6, c6, rc5, m10, -, l13, m14, c17, s17, c18, s18, c19, a20, c21, -, hloop,
    m22, l23, m24, l25, l26, ae⟩ := hb
  have ev : σ (.n v) = gen ^ k := loadHolds_unique l0 hbk
  obtain ⟨e, he, hee⟩ := rc_sound' hκ Lm (K := 34) (by omega) (by decide)
    (by rw [c6]; exact word_g33) rc5.1 rc5.2.1 rc5.2.2
  rw [hmu, hee, ev, ← pow_add] at m6
  have hmue : point.length = e + k := gen_pow_inj' (by omega) (by omega) m6
  -- the loop
  have hB := Main.loop_sound (B := SelBody Lm.read (σ (.n (v + 14))) (σ (.n (v + 15)))
      (σ (.n (v + 10))) (σ (.n (v + 16))) (σ (.n 10)) (σ (.n v)))
    (ps := [σ (.n (v + 5)), σ (.n (v + 14)), σ (.n (v + 15)), σ (.n (v + 10)), σ (.n (v + 16)),
      σ (.n 10), σ (.n v)]) (N := σ (.n (v + 5))) (m := e) (by unfold ordG; omega) hee
    (fun x hx => sel_step (sel_ok i hi) hx) (fun hne => by
      have := hloop (by rw [a20, c19]; exact hne)
      rw [c21] at this
      exact this)
  unfold SelBody at hB
  classical
  let bit : ℕ → E := fun t => if ht : t < e then Classical.choose (hB t ht) else 0
  have hbit : ∀ t (ht : t < e), ∃ e' z o s', LoadHolds Lm.read (σ (.n (v + 14)) * gen ^ t) 0 (bit t) ∧
      bit t * bit t = bit t ∧ LoadHolds Lm.read (σ (.n (v + 15)) * gen ^ t) 0 e' ∧
      LoadHolds Lm.read (σ (.n (v + 10)) * gen ^ t) 0 z ∧
      LoadHolds Lm.read (σ (.n (v + 15)) * gen ^ t) 1 (e' * (1 + bit t + z)) ∧
      LoadHolds Lm.read (σ (.n (v + 16)) * gen ^ t) 0 o ∧
      LoadHolds Lm.read (σ (.n 10) * (σ (.n v) * gen ^ t)) 0 s' ∧
      LoadHolds Lm.read (σ (.n (v + 16)) * gen ^ t) 1 (o * (1 + bit t * (s' + 1))) := fun t ht => by
    simp only [bit, ht, ↓reduceDIte]
    exact Classical.choose_spec (hB t ht)
  -- the chains
  have hzk : ∀ t < e, ∀ z, LoadHolds Lm.read (σ (.n (v + 10)) * gen ^ t) 0 z →
      z = point.getD (k + t) 0 := fun t ht z hl => by
    rw [m10, ev, mul_assoc, ← pow_add, loadHolds_gen_pow_mul, Nat.add_zero] at hl
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact loadHolds_unique hl (hz _ (by omega))
  have hchain : ∀ t ≤ e,
      LoadHolds Lm.read (σ (.n (v + 15))) t
        (∏ j ∈ Finset.range t, (1 + bit j + point.getD (k + j) 0)) ∧
      LoadHolds Lm.read (σ (.n (v + 16))) t
        (∏ j ∈ Finset.range t, (1 + bit j * (gen ^ 2 ^ (k + j) + 1))) := by
    intro t ht
    induction t with
    | zero =>
      simp only [Finset.range_zero, Finset.prod_empty]
      exact ⟨by rw [← c17]; exact s17, by rw [← c18]; exact s18⟩
    | succ t ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      obtain ⟨e', z, o, s', -, -, le, lz, le1, lo, ls, lo1⟩ := hbit t (by omega)
      rw [loadHolds_gen_pow_mul, Nat.add_zero] at le lo
      rw [loadHolds_gen_pow_mul] at le1 lo1
      rw [← mul_assoc, ev, mul_assoc, ← pow_add, loadHolds_gen_pow_mul, Nat.add_zero] at ls
      rw [loadHolds_unique le ih1, hzk t (by omega) z lz] at le1
      rw [loadHolds_unique lo ih2, loadHolds_unique ls (hsq _ (by omega))] at lo1
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      exact ⟨le1, lo1⟩
  obtain ⟨hc1, hc2⟩ := hchain e le_rfl
  rw [m22, hee, loadHolds_gen_pow_mul, Nat.add_zero] at l23
  rw [m24, hee, loadHolds_gen_pow_mul, Nat.add_zero] at l25
  have e23 := loadHolds_unique l23 hc1
  have e25 := loadHolds_unique l25 hc2
  have e26 := loadHolds_unique l26 hoff
  rw [e_add_eq_zero_iff, e25, e26] at ae
  -- the rebuilt offset is the block's
  obtain ⟨off', hoff', hdvd, hprod, hbits⟩ := sel_rebuild (M := point.length) (κ := k)
    (b := fun j => bit (j - k)) (by omega) (fun t ht => by
      simp only [Nat.add_sub_cancel_left]
      obtain ⟨-, -, -, -, -, hb2, -⟩ := hbit t (by omega)
      exact hb2)
  simp only [Nat.add_sub_cancel_left] at hprod hbits
  rw [show point.length - k = e by omega] at hprod hbits
  rw [hprod] at ae
  have h32 : 2 ^ point.length ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  have hoo : off' = off := gen_pow_inj' (by omega) (by omega) ae
  subst hoo
  refine ⟨by omega, hoff', hdvd, ?_⟩
  rw [e23, eqAbove_prod (M := point.length) point rfl, show point.length - k = e by omega]
  exact Finset.prod_congr rfl fun t ht => by rw [hbits t (Finset.mem_range.mp ht)]

end
end LeanVM.Guest.B1.VerifySub
