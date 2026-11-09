/-
  LeanVM.Guest.B1.VerifySub.Mid

  `verify_sub`'s sizes, `kappa_base` and the push side's total (G:3364-3390).
-/

module

public import LeanVM.Guest.B1.VerifySub.Template
public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Guest.B1.Bits.GPower
public import LeanVM.Guest.B1.Bits.Log2

/-!
# The sizes, `kappa_base`, the push total

* `vsSizesT_holds`: the rate exponent `lir ∈ [1, 4]` and the memory's log-size
  `logMem ∈ [16, 32]` as `g`-powers (`g_power_of_word`, range checks), `dims` stored after
  `g^logMem`, `kb = [1, g^logMem, dims…]` in the frame and `kappa_base` its copy.
* `vsPushT_holds`: the push blocks' product of `g_squares[kb[src]·g^adj]` is `g^Σ 2^κ_b`, and the
  bus depth is `g^(log2Ceil Σ)`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-! ## Range checks on `g`-powers -/

/-- A range check against `g^a` (`a ≤ 32`): the value is `g^e`, `e ≤ a`. -/
theorem rc_pow {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ) {x y t1 t2 k : V} {a : ℕ}
    (ha : a ≤ 32) (hk : σ k = gen ^ a) (h : (Atom.rangeCheck x y t1 t2 k).Holds L.read σ) :
    ∃ e ≤ a, σ x = gen ^ e := by
  obtain ⟨l1, m, l2⟩ := h
  have hK : a + 1 ≤ 2 ^ κ :=
    calc a + 1 ≤ 2 ^ 6 := by omega
      _ ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ6
  obtain ⟨e, he, hx⟩ := (rangeCheck_iff hκ L (σ x) (K := a + 1) (by omega) hK).1
    ⟨σ y, σ t1, σ t2, l1, by rw [show a + 1 - 1 = a by omega, ← gen_pow_eq_ofK, ← hk, m], l2⟩
  exact ⟨e, by omega, by rw [hx, gen_pow_eq_ofK]⟩

theorem gen_pow_eq_iff {a b : ℕ} (ha : a < 2 ^ 40) (hb : b < 2 ^ 40) (h : gen ^ a = gen ^ b) :
    a = b :=
  gen_pow_inj (by omega) (by omega) h

theorem word_pow2 {a : ℕ} (h : a < 64) : word (2 ^ a) 0 0 = gen ^ a := word_two_pow h

/-! ## The sizes -/

/-- **The sizes** (G:3364-3383): the rate exponent and the memory's log-size, `dims`, `kb` in the
frame (`140 .. 147`) and `kappa_base`. -/
theorem vsSizesT_holds {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ)
    (hC : CallRel.Le C (coreProgram.Rel L.read))
    (h : Stmt.HoldsList C L.read σ vsSizesT next kret) :
    ∃ lir logMem : ℕ, 1 ≤ lir ∧ lir ≤ 4 ∧ σ (.n 110) = eOfNat lir ∧ σ (.n 122) = gen ^ (lir - 1) ∧
      16 ≤ logMem ∧ logMem ≤ 32 ∧ σ (.n 27) = eOfNat logMem ∧ σ (.n 128) = gen ^ logMem ∧
      ∃ ds : List E, ds.length = 6 ∧ ReadsAt L.read (σ (.n 127)) (gen ^ logMem :: ds) ∧
        ReadsAt L.read (σ (.n 139)) (1 :: gen ^ logMem :: ds) ∧
        (∀ s < 8, σ (.n (140 + s)) = (1 :: gen ^ logMem :: ds).getD s 0) ∧ next := by
  rw [vsSizesT, show (List.range 6) = [0, 1, 2, 3, 4, 5] from rfl,
    show (List.range 8) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl] at h
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, vsCall, vsConst, vsMul, vsRange, vsAlloc, vsLd, Atom.Holds, true_and] at h
  obtain ⟨c112, e123, m122, e125, r124, c29, e131, r130, e135, e136, m130, r137, l130, e142,
    cp141, l0, l1, l2, l3, l4, l5, s0, s1, s2, s3, s4, s5, s6, s7, hn⟩ := h
  -- the rate
  obtain ⟨n, hn64, h112, hr122⟩ := (g_power_of_word_holds _ _ _).1 (hC _ _ _ c112)
  simp only [List.cons.injEq, and_true] at hr122
  obtain ⟨e, he, h124⟩ := rc_pow hκ hκ6 L (a := 3) (by norm_num)
    (by rw [e125, show (8 : ℕ) = 2 ^ 3 from rfl, word_pow2 (by norm_num)]) r124
  have hne : n = e + 1 := by
    rw [hr122, h124, e123, word_gen, ← pow_succ] at m122
    exact gen_pow_eq_iff (by omega) (by omega) m122
  -- the memory's log-size
  obtain ⟨m, hm64, h29, hr130⟩ := (g_power_of_word_holds _ _ _).1 (hC _ _ _ c29)
  simp only [List.cons.injEq, and_true] at hr130
  obtain ⟨e1, he1, h130⟩ := rc_pow hκ hκ6 L (a := 32) le_rfl
    (by rw [e131, word_pow2 (by norm_num)]) r130
  obtain ⟨e2, he2, h137⟩ := rc_pow hκ hκ6 L (a := 32) le_rfl
    (by rw [e135, word_pow2 (by norm_num)]) r137
  have hm1 : m = e1 := by rw [hr130] at h130; exact gen_pow_eq_iff (by omega) (by omega) h130
  have hm2 : m = e2 + 16 := by
    rw [hr130, h137, e136, show (65536 : ℕ) = 2 ^ 16 from rfl, word_pow2 (by norm_num),
      ← pow_add] at m130
    exact gen_pow_eq_iff (by omega) (by omega) m130
  have h140 : σ (.n 140) = 1 := by rw [e142, word_one]
  have h141 : σ (.n 141) = gen ^ m := by rw [cp141, hr130]
  refine ⟨n, m, by omega, by omega, h112, by rw [h124, hne]; rfl, by omega, by omega, h29, hr130,
    [σ (.n 142), σ (.n 143), σ (.n 144), σ (.n 145), σ (.n 146), σ (.n 147)], rfl, ?_, ?_,
    fun s hs ↦ ?_, hn⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · simp only [List.getElem_cons_zero]; rw [← hr130]; exact l130
    · exact l0
    · exact l1
    · exact l2
    · exact l3
    · exact l4
    · exact l5
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · simp only [List.getElem_cons_zero]; rw [← h140]; exact s0
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero]; rw [← h141]; exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
    · exact s7
  · interval_cases s
    · exact h140
    · exact h141
    all_goals rfl

/-! ## The push total -/

theorem blockKappaSrc_lt : ∀ b < Tables.nBlocks, Tables.blockKappaSrc.getD b 0 < 8 := by
  decide +kernel

theorem kbase_getD {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6) {i : ℕ} (hi : i < 8) :
    (1 :: gen ^ logMem :: hs.map (gen ^ ·)).getD i 0 = gen ^ (([0, logMem] ++ hs).getD i 0) := by
  match hs, hl with
  | [h0, h1, h2, h3, h4, h5], _ => interval_cases i <;> simp

theorem kbase_le {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32) (s : ℕ) :
    ([0, logMem] ++ hs).getD s 0 ≤ 32 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hx : ([0, logMem] ++ hs)[s]? with _ | x
  · simp
  · have hmem := List.mem_of_getElem? hx
    simp only [List.cons_append, List.mem_cons, List.nil_append] at hmem
    simp only [Option.getD_some]
    rcases hmem with rfl | rfl | hmem
    · omega
    · exact hm
    · have := hh x hmem; omega

theorem push_adj : ∀ b < 54, Tables.blockKappaAdj b ≠ 0 → Tables.blockKappaSrc.getD b 0 = 0 := by
  decide +kernel

theorem pushKappa_lt {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32)
    {b : ℕ} (hb : b < 54) : pushKappa logMem hs b < 34 := by
  unfold pushKappa
  by_cases h0 : Tables.blockKappaAdj b = 0
  · have := kbase_le hh hm (Tables.blockKappaSrc.getD b 0); omega
  · rw [push_adj b hb h0]
    have : Tables.blockKappaAdj b ≤ 19 := by unfold Tables.blockKappaAdj; split <;> omega
    simp only [List.cons_append, List.getD_cons_zero]
    omega

/-- One push block: `g_squares[kb[src]·g^adj] = g^(2^(κ + adj))` read at `g_squares·kb[src]`,
offset `adj`. -/
theorem push_read {κ : ℕ} {L : MemoryImage κ} (hexp : B1.ExpTables L.read (σ (.n 4)))
    {kb q a : V} {k adj : ℕ} (hk : k + adj < 34) (hkb : σ kb = gen ^ k)
    (ha : σ a = σ (.n 4) * σ kb) (hq : LoadHolds L.read (σ a) adj (σ q)) :
    σ q = gen ^ 2 ^ (k + adj) := by
  rw [ha, hkb, loadHolds_mul_gen_pow] at hq
  exact loadHolds_unique hq (hexp.1 _ hk)

theorem push_block {κ : ℕ} {L : MemoryImage κ} (hexp : B1.ExpTables L.read (σ (.n 4)))
    {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32)
    (hkbv : ∀ s < 8, σ (.n (140 + s)) = gen ^ (([0, logMem] ++ hs).getD s 0))
    {b : ℕ} (hb : b < 54) {q a : V}
    (ha : σ a = σ (.n 4) * σ (.n (140 + Tables.blockKappaSrc.getD b 0)))
    (hq : LoadHolds L.read (σ a) (Tables.blockKappaAdj b) (σ q)) :
    σ q = gen ^ 2 ^ pushKappa logMem hs b :=
  push_read hexp (pushKappa_lt hh hm hb) (hkbv _ (blockKappaSrc_lt b (by show b < 153; omega))) ha hq

theorem push_loop {κ : ℕ} {L : MemoryImage κ} (hexp : B1.ExpTables L.read (σ (.n 4)))
    {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32)
    (hkbv : ∀ s < 8, σ (.n (140 + s)) = gen ^ (([0, logMem] ++ hs).getD s 0)) :
    ∀ n < 54, ∀ {nx : Prop},
      Stmt.HoldsList C L.read σ ((List.range (n + 1)).flatMap vsPushStep) nx kret →
      σ (.n (vsPV n)) = gen ^ ((List.range (n + 1)).map fun b ↦ 2 ^ pushKappa logMem hs b).sum ∧ nx := by
  intro n
  induction n with
  | zero =>
    intro _ nx h
    rw [show List.range (0 + 1) = [0] from rfl] at h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, vsPushStep,
      ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd, vsMul] at h
    obtain ⟨m, l, hn⟩ := h
    refine ⟨?_, hn⟩
    rw [show vsPV 0 = 149 from rfl, push_block hexp hh hm hkbv (b := 0) (by norm_num) m l]
    simp
  | succ n ih =>
    intro hn nx h
    rw [List.range_succ, List.flatMap_append, holdsList_append] at h
    obtain ⟨hp, h⟩ := ih (by omega) h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, vsPushStep,
      Nat.add_one_ne_zero, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd, vsMul] at h
    obtain ⟨m, l, m2, hn'⟩ := h
    refine ⟨?_, hn'⟩
    rw [m2, Nat.add_sub_cancel, hp, push_block hexp hh hm hkbv hn m l, ← pow_add,
      List.range_succ (n := n + 1), List.map_append, List.sum_append]
    simp

theorem push_sum_lt {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32) :
    ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum < 2 ^ 40 := by
  have hle := List.sum_le_length_nsmul ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b)
    (2 ^ 33) (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      exact Nat.pow_le_pow_right (by norm_num)
        (by have := pushKappa_lt hh hm (List.mem_range.1 hb); omega))
  simp only [List.length_map, List.length_range, smul_eq_mul] at hle
  omega

/-- **The push total** (G:3386-3390): the bus depth `g^(log2Ceil Σ)` over the push blocks'
`Σ 2^κ_b`. -/
theorem vsPushT_holds {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ)
    (hC : CallRel.Le C (coreProgram.Rel L.read)) (hexp : B1.ExpTables L.read (σ (.n 4)))
    {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32)
    (hkbv : ∀ s < 8, σ (.n (140 + s)) = gen ^ (([0, logMem] ++ hs).getD s 0))
    (h : Stmt.HoldsList C L.read σ vsPushT next kret) :
    σ (.n 309) = gen ^ log2Ceil ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum ∧
      log2Ceil ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum < 34 ∧ next := by
  unfold vsPushT at h
  rw [holdsList_append] at h
  obtain ⟨hp, h⟩ := push_loop hexp hh hm hkbv 53 (by norm_num) h
  simp only [Stmt.HoldsList, Stmt.Holds, vsCall, List.map_cons, List.map_nil, Atom.Holds,
    true_and] at h
  obtain ⟨hc, hn⟩ := h
  rw [show vsPV 53 = 308 from rfl] at hp
  replace hp : σ (.n 308) = gen ^ ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum := hp
  have hr := (log2_holds.1 hκ hκ6 L _ _ hexp _).1 (hC _ _ _ hc)
  rw [hp, meaningLog2CeilExp_pow (by norm_num) (by have := push_sum_lt hh hm; omega)] at hr
  simp only [List.cons.injEq, and_true, Nat.zero_max] at hr
  exact ⟨hr.2, hr.1, hn⟩

end
end LeanVM.Guest.B1.VerifySub
