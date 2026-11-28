/-
  LeanVM.Guest.B1.VsC.VsPh1

  `verify_sub`'s windows `3 ..< 7` of `wA` (`WinsHyp`): the rate and the memory's log, their range
  checks, the tables' log heights and the sizes' second permutation.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh0
public import LeanVM.Guest.B1.VsC.VsW3

/-!
# Phase 1: the rate, the memory's log, the tables' heights

The windows `vsA_w3` (statement `69`, `g_power_of_word` of the stream's word `7`, the rate `r`),
`vsA_w4` (`70 ..< 74`: `g^(r - 1) ≤ g^3`), `vsA_w5` (statement `74`, `g_power_of_word` of the stream's
word `0`, the memory's log `m`) and `vsA_w6` (`75 ..< 109`: `m ≤ 30`, `m - 1 ≤ 32`, the heap witness
`table_logs` into window `0`'s first `HeapBuf`, an eight-word `HeapBuf` holding `1`, `g^m` and the six
log heights, a permutation, the stream's words `8`, `9`, the first height at most `24`, the sizes'
buffer's word `0`). `vsPh1_wins`: their hypotheses on `vsVal rd0 w args` from the rate `1 ≤ r ≤ 4`,
the memory's log `1 ≤ m ≤ 30`, the oracle's returns `g^r`, `g^m`, the heights `tl` (the first `g^h`,
`h ≤ 24`) that `rd0` and every memory holding `st.O` read at the first `HeapBuf` `b6`, the latter holding
`1 :: g^m :: tl` at the cursor.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

theorem headD_of_take_one {l : List Stmt} {x d : Stmt} (h : l.take 1 = [x]) : l.headD d = x := by
  cases l with
  | nil => simp at h
  | cons y ys => simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at h; simp [h]

/-- `g^a / g^b = g^(a - b)` for `b ≤ a`. -/
theorem gen_div {a b : ℕ} (h : b ≤ a) : gen ^ a * (gen ^ b)⁻¹ = gen ^ (a - b) :=
  (pow_sub₀ _ Value.gen_ne_zero h).symm

/-! ## The windows' statements -/

/-- Statement `74`. -/
def vsW5s : Stmt := .call "g_power_of_word" [.n 57] [.n 101]

/-- Statements `70 ..< 74`. -/
def vsW4 : List Atom := [
    .const (.n 95) (word 2 0),
    .mul (.n 94) (.n 96) (.n 95),
    .const (.n 97) (word 8 0),
    .rangeCheck (.n 96) (.n 98) (.n 99) (.n 100) (.n 97)]

/-- Statements `75 ..< 109`. -/
def vsW6 : List Atom := [
    .const (.n 102) (word 1073741824 0),
    .rangeCheck (.n 101) (.n 103) (.n 104) (.n 105) (.n 102),
    .const (.n 106) (word 4294967296 0),
    .const (.n 107) (word 2 0),
    .mul (.n 101) (.n 108) (.n 107),
    .rangeCheck (.n 108) (.n 109) (.n 110) (.n 111) (.n 106),
    .hint (.witness "table_logs" (.heap (.n 6) 0 6)),
    .hint (.alloc (.n 112) 8),
    .const (.n 113) (word 1 0),
    .copy (.n 114) (.n 101),
    .load (.n 115) (.n 6) 0, .load (.n 116) (.n 6) 1, .load (.n 117) (.n 6) 2,
    .load (.n 118) (.n 6) 3, .load (.n 119) (.n 6) 4, .load (.n 120) (.n 6) 5,
    .load (.n 113) (.n 112) 0, .load (.n 114) (.n 112) 1, .load (.n 115) (.n 112) 2,
    .load (.n 116) (.n 112) 3, .load (.n 117) (.n 112) 4, .load (.n 118) (.n 112) 5,
    .load (.n 119) (.n 112) 6, .load (.n 120) (.n 112) 7,
    .keccak [.n 83, .n 84, .n 86, .n 87, .n 89, .n 90, .n 92, .n 93, .n 77, .n 78, .n 79, .n 80, .n 81]
      [.n 121, .n 122, .n 123, .n 124, .n 125, .n 126, .n 127, .n 128, .n 129, .n 130, .n 131, .n 132, .n 133]
      false false,
    .load (.n 134) (.n 55) 8,
    .copy (.n 135) (.n 134),
    .const (.n 136) (word 0 1),
    .load (.n 137) (.n 55) 9,
    .copy (.n 138) (.n 137),
    .const (.n 139) (word 0 1),
    .const (.n 140) (word 16777216 0),
    .rangeCheck (.n 115) (.n 141) (.n 142) (.n 143) (.n 140),
    .load (.n 144) (.n 56) 0]

set_option maxRecDepth 100000 in
theorem vsW4_eq' : (vsA.drop 70).take 4 = vsW4.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vsW5_eq : (vsA.drop 74).take 1 = [vsW5s] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vsW6_eq : (vsA.drop 75).take 34 = vsW6.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

theorem vsA_w3_eq : vsA_w3 = .call vsW3s := by rw [vsA_w3, headD_of_take_one vsW3_eq]

theorem vsA_w4_eq : vsA_w4 = .run vsW4 := by rw [vsA_w4, vsW4_eq', atomsOf_map]

theorem vsA_w5_eq : vsA_w5 = .call vsW5s := by rw [vsA_w5, headD_of_take_one vsW5_eq]

theorem vsA_w6_eq : vsA_w6 = .run vsW6 := by rw [vsA_w6, vsW6_eq, atomsOf_map]

theorem vsW4_ne : vsW4.all neB = true := by decide +kernel

theorem vsW6_ne : vsW6.all neB = true := by decide +kernel

theorem vsW4_pure : vsW4.filter pureAsks =
    [.mul (.n 94) (.n 96) (.n 95), .rangeCheck (.n 96) (.n 98) (.n 99) (.n 100) (.n 97)] := by decide +kernel

theorem vsW4_mem : vsW4.filter memAsks = [] := by decide +kernel

theorem vsW4_alloc : allocDsts (vsW4.map Ev.atom) = [] ∧ (∀ σ, allocs σ (vsW4.map Ev.atom) = []) ∧
    (∀ σ, loadAddrs σ (vsW4.map Ev.atom) = []) ∧ (∀ σ, heapHintAddrs σ (vsW4.map Ev.atom) = []) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

set_option maxRecDepth 100000 in
theorem vsW6_pure : vsW6.filter pureAsks =
    [.rangeCheck (.n 101) (.n 103) (.n 104) (.n 105) (.n 102), .mul (.n 101) (.n 108) (.n 107),
      .rangeCheck (.n 108) (.n 109) (.n 110) (.n 111) (.n 106),
      .rangeCheck (.n 115) (.n 141) (.n 142) (.n 143) (.n 140)] := by decide +kernel

/-- The loads of window `6`: `(value, pointer, offset)`. -/
def vsW6ld : List (ℕ × ℕ × ℕ) := [(115, 6, 0), (116, 6, 1), (117, 6, 2), (118, 6, 3), (119, 6, 4), (120, 6, 5),
  (113, 112, 0), (114, 112, 1), (115, 112, 2), (116, 112, 3), (117, 112, 4), (118, 112, 5), (119, 112, 6),
  (120, 112, 7), (134, 55, 8), (137, 55, 9), (144, 56, 0)]

set_option maxRecDepth 100000 in
theorem vsW6_mem : vsW6.filter memAsks = vsW6ld.map fun q => .load (.n q.1) (.n q.2.1) q.2.2 := by
  decide +kernel

theorem vsW6_allocs (σ : Val) : allocs σ (vsW6.map Ev.atom) = [8] := rfl

theorem vsW6_allocDsts : allocDsts (vsW6.map Ev.atom) = [.n 112] := rfl

theorem vsW6_hintAddrs (σ : Val) : heapHintAddrs σ (vsW6.map Ev.atom) =
    (List.range 6).map fun j => (σ (.n 6)).limb 0 * addressOfIndex j := rfl

set_option maxRecDepth 100000 in
/-- The fresh loads of window `6` are no stores. -/
theorem vsW6_fresh : ((vsW6ld.filter fun q => q.2.1 ≠ 112).all fun q =>
    !(storesOf 6 vsAf).contains (.load (.n q.1) (.n q.2.1) q.2.2)) = true := by decide +kernel

/-! ## The values -/

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

theorem vsW4_good (ha : args.length = 6) : ∀ a ∈ vsW4, Good rd0 (storesOf 6 vsAf) w (vsVal rd0 w args) a :=
  vsA_run_good ha vsW4_eq' vsW4_ne

theorem vsW6_good (ha : args.length = 6) : ∀ a ∈ vsW6, Good rd0 (storesOf 6 vsAf) w (vsVal rd0 w args) a :=
  vsA_run_good ha vsW6_eq vsW6_ne

/-- The stream's words `0 ..< 8` as window `2` loads them. -/
theorem vsW2_val (ha : args.length = 6) {s : ℕ} (hw55 : w 55 = ptrAt s) {ws : List E}
    (h0 : ReadsAt rd0 (ptrAt s) ws) : ∀ q ∈ vsW2ld, ∀ h : q.2 < ws.length, vsVal rd0 w args (.n q.1) = ws[q.2] := by
  obtain ⟨-, -, -, fS⟩ := vsW2_facts
  have sl : ∀ q ∈ vsW2ld, Atom.load (.n q.1) (.n 55) q.2 ∉ storesOf 6 vsAf := fun q hq h => by
    have := List.all_eq_true.mp fS q hq
    rw [List.contains_iff_mem.mpr h] at this
    exact absurd this (by decide)
  have hg := vsA_run_good (rd0 := rd0) (w := w) ha vsW2_eq vsW2_ne
  have p55 : vsVal rd0 w args (.n 55) = ptrAt s := by rw [vsVal_55 ha, hw55]
  obtain ⟨-, -, om⟩ := vsW2_offs
  intro q hq h
  exact good_loadAt (sl q hq) (hg _ (List.contains_iff_mem.mp (List.all_eq_true.mp om q hq))) p55 h h0

end

/-! ## The windows' hypotheses -/

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

theorem lt_two_pow_k {k m : ℕ} (hk : 6 ≤ k) (hm : m ≤ 32) : m < 2 ^ k :=
  lt_of_le_of_lt hm (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk))

/-- **Window `4`'s hypotheses**: `g^(r - 1)` from `g^r`, at most `g^3`. -/
theorem vsW4_runHyp (hk : 6 ≤ k) (ha : args.length = 6) {r a : ℕ} (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (h94 : vsVal rd0 w args (.n 94) = gen ^ r) {D : ℕ → Prop} {O : Reader → Prop} :
    RunHyp k (vsVal rd0 w args) w a Own R D Pre O vsW4 := by
  have hg := vsW4_good (rd0 := rd0) (w := w) ha
  have h95 : vsVal rd0 w args (.n 95) = gen ^ 1 := by
    have := hg (.const (.n 95) (word 2 0)) (by simp [vsW4]); simp only [Good] at this
    rw [this]; exact wordG (j := 1) (by norm_num)
  have h97 : vsVal rd0 w args (.n 97) = gen ^ 3 := by
    have := hg (.const (.n 97) (word 8 0)) (by simp [vsW4]); simp only [Good] at this
    rw [this]; exact wordG (j := 3) (by norm_num)
  have h96 : vsVal rd0 w args (.n 96) = gen ^ (r - 1) := by
    have := hg (.mul (.n 94) (.n 96) (.n 95)) (by simp [vsW4])
    simp only [Good, show ¬ ((V.n 96).idx < (V.n 94).idx ∧ (V.n 95).idx < (V.n 94).idx) from by decide,
      ↓reduceIte] at this
    rw [this, h94, h95, gen_div hr1]
  have h98 : vsVal rd0 w args (.n 98) = gen ^ (3 - (r - 1)) := by
    have := (hg (.rangeCheck (.n 96) (.n 98) (.n 99) (.n 100) (.n 97)) (by simp [vsW4])).2.2
    simp only [show (V.n 97).idx < (V.n 98).idx from by decide, ↓reduceIte] at this
    rw [this, h97, h96, gen_div (by omega)]
  refine RunHyp.of_asks (by rw [vsW4_alloc.1, vsW4_alloc.2.1]; rfl)
    (by intro A hA; rw [vsW4_alloc.2.2.1] at hA; simp at hA)
    (by intro A hA; rw [vsW4_alloc.2.2.2] at hA; simp at hA) ?_ (by intro rd _ _ _ x hx; rw [vsW4_mem] at hx; simp at hx)
  intro x hx
  rw [vsW4_pure] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · show (if (V.n 96).idx < (V.n 94).idx ∧ (V.n 95).idx < (V.n 94).idx then True else vsVal rd0 w args (.n 95) ≠ 0)
    simp only [show ¬ ((V.n 96).idx < (V.n 94).idx ∧ (V.n 95).idx < (V.n 94).idx) from by decide, ↓reduceIte, h95]
    exact pow_ne_zero _ Value.gen_ne_zero
  · exact ⟨by rw [h96]; exact lowW_pow (lt_two_pow_k hk (by omega)),
      by rw [h98]; exact lowW_pow (lt_two_pow_k hk (by omega))⟩

/-- **Window `6`'s hypotheses.** -/
theorem vsW6_runHyp (hk : 6 ≤ k) (ha : args.length = 6) {m a b6 s b56 : ℕ} (hm1 : 1 ≤ m) (hm30 : m ≤ 30)
    (h101 : vsVal rd0 w args (.n 101) = gen ^ m) (hw6 : w 6 = ptrAt b6) (hw55 : w 55 = ptrAt s)
    (hw56 : w 56 = ptrAt b56) (hw112 : w 112 = ptrAt a)
    {h0 : ℕ} (hh0 : h0 ≤ 24) (t1 t2 t3 t4 t5 : E) (ws bs : List E)
    (hws : 10 ≤ ws.length) (hbs : 1 ≤ bs.length)
    (r6 : ReadsAt rd0 (ptrAt b6) [gen ^ h0, t1, t2, t3, t4, t5]) (r55 : ReadsAt rd0 (ptrAt s) ws)
    (r56 : ReadsAt rd0 (ptrAt b56) bs)
    {D : ℕ → Prop} {O : Reader → Prop}
    (hO6 : ∀ j < 6, Own (b6 + j)) (hOa : ∀ j < 8, Own (a + j)) (hOs : Own (s + 8) ∧ Own (s + 9)) (hOb : Own b56)
    (hrd : ∀ rd, O rd → ReadsAt rd (ptrAt b6) [gen ^ h0, t1, t2, t3, t4, t5] ∧
      ReadsAt rd (ptrAt a) [1, gen ^ m, gen ^ h0, t1, t2, t3, t4, t5] ∧
      ReadsAt rd (ptrAt s) ws ∧ ReadsAt rd (ptrAt b56) bs) :
    RunHyp k (vsVal rd0 w args) w a Own R D Pre O vsW6 := by
  have hg := vsW6_good (rd0 := rd0) (w := w) ha
  set σ0 := vsVal rd0 w args with hσ0
  have cst : ∀ (d : ℕ) (e : E), Atom.const (.n d) e ∈ vsW6 → σ0 (.n d) = e := fun d e h => hg _ h
  have h102 : σ0 (.n 102) = gen ^ 30 := (cst 102 _ (by simp [vsW6])).trans (wordG (j := 30) (by norm_num))
  have h106 : σ0 (.n 106) = gen ^ 32 := (cst 106 _ (by simp [vsW6])).trans (wordG (j := 32) (by norm_num))
  have h107 : σ0 (.n 107) = gen ^ 1 := (cst 107 _ (by simp [vsW6])).trans (wordG (j := 1) (by norm_num))
  have h140 : σ0 (.n 140) = gen ^ 24 := (cst 140 _ (by simp [vsW6])).trans (wordG (j := 24) (by norm_num))
  have h113 : σ0 (.n 113) = 1 :=
    (cst 113 _ (by simp [vsW6])).trans ((wordG (j := 0) (by norm_num) : word 1 0 = gen ^ 0).trans (pow_zero _))
  have h114 : σ0 (.n 114) = gen ^ m := (hg (.copy (.n 114) (.n 101)) (by simp [vsW6])).trans h101
  have h108 : σ0 (.n 108) = gen ^ (m - 1) := by
    have := hg (.mul (.n 101) (.n 108) (.n 107)) (by simp [vsW6])
    simp only [Good, show ¬ ((V.n 108).idx < (V.n 101).idx ∧ (V.n 107).idx < (V.n 101).idx) from by decide,
      ↓reduceIte] at this
    rw [this, h101, h107, gen_div hm1]
  have rc : ∀ x y t1 t2 kk : ℕ, Atom.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n kk) ∈ vsW6 → kk < y →
      σ0 (.n y) = σ0 (.n kk) * (σ0 (.n x))⁻¹ := fun x y t1 t2 kk h hl => by
    have := (hg _ h).2.2
    have hl' : (V.n kk).idx < (V.n y).idx := hl
    simpa only [hl', ↓reduceIte] using this
  have p6 : σ0 (.n 6) = ptrAt b6 := by
    rw [hσ0]; exact (vsW0_good ha (a := .hint (.alloc (.n 6) 6)) (by simp [vsW0, vsW0a])).trans hw6
  have p55 : σ0 (.n 55) = ptrAt s := by rw [hσ0, vsVal_55 ha, hw55]
  have p56 : σ0 (.n 56) = ptrAt b56 := by
    rw [hσ0]
    exact (vsA_run_good (rd0 := rd0) (w := w) ha vsW2_eq vsW2_ne (.hint (.alloc (.n 56) 6)) (by simp [vsW2])).trans
      hw56
  have p112 : σ0 (.n 112) = ptrAt a := (hg (.hint (.alloc (.n 112) 8)) (by simp [vsW6])).trans hw112
  -- the fresh loads
  have fr := vsW6_fresh
  have fresh : ∀ (b : ℕ) (xs : List E) (d pv off : ℕ), σ0 (.n pv) = ptrAt b → ReadsAt rd0 (ptrAt b) xs →
      (d, pv, off) ∈ vsW6ld → pv ≠ 112 → ∀ h : off < xs.length, σ0 (.n d) = xs[off] := by
    intro b xs d pv off hp hr hq hne h
    have hm' : Atom.load (.n d) (.n pv) off ∈ vsW6ld.map (fun q => Atom.load (.n q.1) (.n q.2.1) q.2.2) :=
      List.mem_map.mpr ⟨_, hq, rfl⟩
    rw [← vsW6_mem] at hm'
    have hm : Atom.load (.n d) (.n pv) off ∈ vsW6 := List.mem_of_mem_filter hm'
    have hs : Atom.load (.n d) (.n pv) off ∉ storesOf 6 vsAf := fun h' => by
      have := List.all_eq_true.mp fr (d, pv, off) (List.mem_filter.mpr ⟨hq, by simpa using hne⟩)
      rw [List.contains_iff_mem.mpr h'] at this
      exact absurd this (by decide)
    exact good_loadAt hs (hg _ hm) hp h hr
  have v115 : σ0 (.n 115) = gen ^ h0 := fresh b6 _ 115 6 0 p6 r6 (by simp [vsW6ld]) (by decide) (by simp)
  have v116 : σ0 (.n 116) = t1 := fresh b6 _ 116 6 1 p6 r6 (by simp [vsW6ld]) (by decide) (by simp)
  have v117 : σ0 (.n 117) = t2 := fresh b6 _ 117 6 2 p6 r6 (by simp [vsW6ld]) (by decide) (by simp)
  have v118 : σ0 (.n 118) = t3 := fresh b6 _ 118 6 3 p6 r6 (by simp [vsW6ld]) (by decide) (by simp)
  have v119 : σ0 (.n 119) = t4 := fresh b6 _ 119 6 4 p6 r6 (by simp [vsW6ld]) (by decide) (by simp)
  have v120 : σ0 (.n 120) = t5 := fresh b6 _ 120 6 5 p6 r6 (by simp [vsW6ld]) (by decide) (by simp)
  have v134 : σ0 (.n 134) = ws[8] := fresh s ws 134 55 8 p55 r55 (by simp [vsW6ld]) (by decide) (by omega)
  have v137 : σ0 (.n 137) = ws[9] := fresh s ws 137 55 9 p55 r55 (by simp [vsW6ld]) (by decide) (by omega)
  have v144 : σ0 (.n 144) = bs[0] := fresh b56 bs 144 56 0 p56 r56 (by simp [vsW6ld]) (by decide) (by omega)
  refine RunHyp.of_asks ?_ ?_ ?_ ?_ ?_
  · rw [vsW6_allocDsts, vsW6_allocs]; simp only [List.map_cons, List.map_nil, bases, hw112]
  · intro A hA
    obtain ⟨d, p, off, hm, rfl⟩ := mem_loadAddrs hA
    have hm' : Atom.load d p off ∈ vsW6.filter memAsks := List.mem_filter.mpr ⟨hm, rfl⟩
    rw [vsW6_mem, List.mem_map] at hm'
    obtain ⟨q, hq, he⟩ := hm'
    simp only [Atom.load.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp only [vsW6ld, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp only
    all_goals first
      | exact ⟨b6 + _, by rw [p6, ptrAt, B1.Main.addr_ofK], Or.inl (hO6 _ (by norm_num))⟩
      | exact ⟨a + _, by rw [p112, ptrAt, B1.Main.addr_ofK], Or.inl (hOa _ (by norm_num))⟩
      | exact ⟨s + _, by rw [p55, ptrAt, B1.Main.addr_ofK], Or.inl (by first | exact hOs.1 | exact hOs.2)⟩
      | exact ⟨b56 + 0, by rw [p56, ptrAt, B1.Main.addr_ofK], Or.inl (by simpa using hOb)⟩
  · intro A hA
    rw [vsW6_hintAddrs, List.mem_map] at hA
    obtain ⟨j, hj, rfl⟩ := hA
    rw [List.mem_range] at hj
    exact ⟨b6 + j, by rw [p6, ptrAt, B1.Main.addr_ofK], Or.inl (hO6 j hj)⟩
  · intro x hx
    rw [vsW6_pure] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h103 := rc 101 103 104 105 102 (by simp [vsW6]) (by decide)
      rw [h102, h101, gen_div hm30] at h103
      exact ⟨by rw [h101]; exact lowW_pow (lt_two_pow_k hk (by omega)),
        by rw [h103]; exact lowW_pow (lt_two_pow_k hk (by omega))⟩
    · show (if (V.n 108).idx < (V.n 101).idx ∧ (V.n 107).idx < (V.n 101).idx then True else σ0 (.n 107) ≠ 0)
      simp only [show ¬ ((V.n 108).idx < (V.n 101).idx ∧ (V.n 107).idx < (V.n 101).idx) from by decide, ↓reduceIte, h107]
      exact pow_ne_zero _ Value.gen_ne_zero
    · have h109 := rc 108 109 110 111 106 (by simp [vsW6]) (by decide)
      rw [h106, h108, gen_div (by omega)] at h109
      exact ⟨by rw [h108]; exact lowW_pow (lt_two_pow_k hk (by omega)),
        by rw [h109]; exact lowW_pow (lt_two_pow_k hk (by omega))⟩
    · have h141 := rc 115 141 142 143 140 (by simp [vsW6]) (by decide)
      rw [h140, v115, gen_div hh0] at h141
      exact ⟨by rw [v115]; exact lowW_pow (lt_two_pow_k hk (by omega)),
        by rw [h141]; exact lowW_pow (lt_two_pow_k hk (by omega))⟩
  · intro rd _ _ ho x hx
    obtain ⟨q6, qa, qs, q56⟩ := hrd rd ho
    rw [vsW6_mem, List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    simp only [vsW6ld, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals show LoadHolds rd _ _ _
    all_goals dsimp only
    · rw [p6, v115]; exact q6 0 (by simp)
    · rw [p6, v116]; exact q6 1 (by simp)
    · rw [p6, v117]; exact q6 2 (by simp)
    · rw [p6, v118]; exact q6 3 (by simp)
    · rw [p6, v119]; exact q6 4 (by simp)
    · rw [p6, v120]; exact q6 5 (by simp)
    · rw [p112, h113]; exact qa 0 (by simp)
    · rw [p112, h114]; exact qa 1 (by simp)
    · rw [p112, v115]; exact qa 2 (by simp)
    · rw [p112, v116]; exact qa 3 (by simp)
    · rw [p112, v117]; exact qa 4 (by simp)
    · rw [p112, v118]; exact qa 5 (by simp)
    · rw [p112, v119]; exact qa 6 (by simp)
    · rw [p112, v120]; exact qa 7 (by simp)
    · rw [p55, v134]; exact qs 8 (by omega)
    · rw [p55, v137]; exact qs 9 (by omega)
    · rw [p56, v144]; exact q56 0 (by omega)

/-- **Phase 1's windows' hypotheses** (`vsA_w3` … `vsA_w6`): the rate `1 ≤ r ≤ 4` (the stream's word `7`)
and the memory's log `1 ≤ m ≤ 30` (its word `0`), the oracle's `g^r`, `g^m`, the heights' `HeapBuf` `b6`
holding `g^(h_0)` (`h_0 ≤ 24`) and five more, the new `HeapBuf` at the cursor; `K` after them. -/
theorem vsPh1_wins (hk : 6 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop} {r m b6 s b56 : ℕ}
    (hr1 : 1 ≤ r) (hr4 : r ≤ 4) (hm1 : 1 ≤ m) (hm30 : m ≤ 30)
    (hw6 : w 6 = ptrAt b6) (hw55 : w 55 = ptrAt s) (hw56 : w 56 = ptrAt b56) (hw112 : w 112 = ptrAt st.a)
    (hw94 : w 94 = gen ^ r) (hw101 : w 101 = gen ^ m)
    {h0 : ℕ} (hh0 : h0 ≤ 24) (t1 t2 t3 t4 t5 : E) (ws : List E) (hws : 10 ≤ ws.length)
    (hw7 : ws.getD 7 0 = eOfNat r) (hw0 : ws.getD 0 0 = eOfNat m)
    (r6 : ReadsAt rd0 (ptrAt b6) [gen ^ h0, t1, t2, t3, t4, t5]) (r55 : ReadsAt rd0 (ptrAt s) ws)
    (r56 : ReadsAt rd0 (ptrAt b56) ((ws.drop 1).take 6))
    (hO6 : ∀ j < 6, Own (b6 + j)) (hOa : ∀ j < 8, Own (st.a + j)) (hOs : Own (s + 8) ∧ Own (s + 9))
    (hOb : Own b56)
    (hrd : ∀ rd, st.O rd → ReadsAt rd (ptrAt b6) [gen ^ h0, t1, t2, t3, t4, t5] ∧
      ReadsAt rd (ptrAt st.a) [1, gen ^ m, gen ^ h0, t1, t2, t3, t4, t5] ∧
      ReadsAt rd (ptrAt s) ws ∧ ReadsAt rd (ptrAt b56) ((ws.drop 1).take 6))
    (hK : K ⟨st.a + 8, leafEnd fs al "g_power_of_word" (leafEnd fs al "g_power_of_word" st.kc),
      fun rd => (st.O rd ∧ True) ∧ True, fun i => (st.D i ∨ False) ∨ False, st.Qs ++ [PostQuiet] ++ [PostQuiet]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsA_w3, vsA_w4, vsA_w5, vsA_w6] st K := by
  have val := vsW2_val (rd0 := rd0) (w := w) ha hw55 r55
  have h91 : vsVal rd0 w args (.n 91) = eOfNat r := by
    rw [val (91, 7) (by simp [vsW2ld]) (by omega), ← hw7, List.getD_eq_getElem]
  have h57 : vsVal rd0 w args (.n 57) = eOfNat m := by
    rw [val (57, 0) (by simp [vsW2ld]) (by omega), ← hw0, List.getD_eq_getElem]
  have h94 : vsVal rd0 w args (.n 94) = gen ^ r :=
    (vsVal_call_ret ha vsW3_eq (.n 94) (List.mem_singleton_self _)).trans hw94
  have h101 : vsVal rd0 w args (.n 101) = gen ^ m :=
    (vsVal_call_ret ha vsW5_eq (.n 101) (List.mem_singleton_self _)).trans hw101
  rw [vsA_w3_eq, vsA_w4_eq, vsA_w5_eq, vsA_w6_eq]
  have c3 := g_power_of_word_leafA fs al cert k (fun _ => False) (fun rd => Pre rd ∧ st.O rd)
    (n := r) (by omega)
  rw [← h91, ← h94] at c3
  refine winsHyp_call_leaf (g := "g_power_of_word") rfl c3 (fun _ h => h.elim) (fun _ h => h) ?_
  rw [WinsHyp]
  refine ⟨vsW4_runHyp hk ha hr1 hr4 h94, ?_⟩
  have c5 := g_power_of_word_leafA fs al cert k (fun _ => False)
    (fun rd => Pre rd ∧ (st.O rd ∧ True)) (n := m) (by omega)
  rw [← h57, ← h101] at c5
  refine winsHyp_call_leaf (g := "g_power_of_word") rfl c5 (fun _ h => h.elim) (fun _ h => h) ?_
  rw [WinsHyp]
  refine ⟨vsW6_runHyp hk ha hm1 hm30 h101 hw6 hw55 hw56 hw112 hh0 t1 t2 t3 t4 t5 ws ((ws.drop 1).take 6)
    hws (by simp; omega) r6 r55 r56 hO6 hOa hOs hOb (fun rd ho => hrd rd ho.1.1), ?_⟩
  rw [WinsHyp]
  exact hK

end

end
end LeanVM.Guest.B1.VsC
