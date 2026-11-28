/-
  LeanVM.Guest.B1.VsC.VsAvoid

  No fresh load of `verify_sub` reads the overlay's cells (`.n 19`'s twelve words): `VsCtx.VsAvoid`.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatFresh
public import LeanVM.Guest.B1.VsC.VsOrcMem
public import LeanVM.Guest.B1.VsC.VsOrcBuf
public import LeanVM.Guest.B1.VsC.VsW0
public import LeanVM.Guest.B1.VsC.VsPh3

/-!
# The fresh loads avoid the overlay

Every fresh load of `verify_sub` (each branch's arm when taken) reads through one of few pointers, and the
kernel checks that each part's loads read through a listed pointer at most its listed offset (`specOk`,
`spA_ok`, …, `spC_ok`). Each listed pointer is `ptrAt a` with its reads `a ..= a + m` below the overlay's
cells `x.base 13 + j` or past them (`PtrOff`): an own buffer at a fixed index (`ptrOff_buf`: the buffers
before `.n 19` end before it, the later start past it), a table read below the frame (`ptrOff_tab`: `.n 4`
times a grind window `g^k`, `k < 2^11`, or `g^width`), or a callee's return inside the stream's buffer
(`ptrOff_ret`). **`VsCtx.vsAvoid_of_hyp`**: `VsAvoid x` from `AvoidHyp x`, the placement's bounds and the
values the pointers are built from (`.n 409 = g^width`, `.n 101 = g^m`, the selectors `.n 115 …`, and the
returns `w 772`, `w 1076`, `w 2920` in the stream's buffer).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Pointers and the reads through them -/

/-- The value `.n i` is a pointer `ptrAt a` whose reads `a ..= a + m` lie off the twelve cells from `b`. -/
def PtrOff (σ : Val) (b i m : ℕ) : Prop :=
  ∃ a, σ (.n i) = ptrAt a ∧ a + m < 2 ^ 64 - 1 ∧ (a + m < b ∨ b + 12 ≤ a)

/-- A load reads through a listed pointer `(i, m)`, at offset at most `m`. -/
def specOk (sp : List (ℕ × ℕ)) : Atom → Bool
  | .load _ p off => decide (p = .n p.idx) && sp.any fun q => q.1 == p.idx && decide (off ≤ q.2)
  | _ => true

theorem ptrAt_limb_mul (a off : ℕ) : (ptrAt a).limb 0 * addressOfIndex off = addressOfIndex (a + off) := by
  simp [ptrAt, addressOfIndex, pow_add]

/-- **A block's fresh loads avoid the twelve cells from `b`** once each reads through a listed pointer whose
reads avoid them. -/
theorem avoidAt_of_spec {σ : Val} {b c : ℕ} {ss : List Stmt} {sp : List (ℕ × ℕ)}
    (hc : (freshLoads c ss).all (specOk sp) = true) (hb : b + 12 < 2 ^ 64 - 1)
    (hp : ∀ q ∈ sp, PtrOff σ b q.1 q.2) : AvoidAt σ b c ss := by
  intro a ha d p off e j hj he
  subst e
  have h1 := List.all_eq_true.mp hc _ ha
  simp only [specOk, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h1
  obtain ⟨hpn, q, hq, hq1, hoff⟩ := h1
  obtain ⟨a', hσ, hlt, hcase⟩ := hp q hq
  rw [hpn, ← hq1, hσ, ptrAt_limb_mul] at he
  have := addr_inj (by omega) (by omega) he
  omega

/-! ## The values the oracle gives -/

/-- The values a statement takes from the oracle: a call's returns, an allocation's pointer, a window hint's
words. -/
def orcVs : Stmt → List V
  | .call _ _ rets => rets
  | .dispatch _ _ _ rets => rets
  | .atom (.hint (.alloc d _)) => [d]
  | .atom (.hint (.allocDyn d _)) => [d]
  | .atom (.hint (.windowsExp _ _ _ _ (.stack ds))) => ds
  | _ => []

theorem goodS_orcVs {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {s : Stmt} (h : GoodS rd S w σ s) :
    ∀ v ∈ orcVs s, σ v = w v.idx := by
  intro v hv
  cases s with
  | call f a rets => exact h v hv
  | dispatch c fs a rets => exact h v hv
  | atom a =>
    cases a with
    | hint hh =>
      cases hh with
      | alloc d n =>
        simp only [orcVs, List.mem_singleton] at hv
        subst hv; exact h
      | allocDyn d n =>
        simp only [orcVs, List.mem_singleton] at hv
        subst hv; exact h
      | windowsExp v' st wd ct dd =>
        cases dd with
        | stack ds => exact h v hv
        | heap => simp [orcVs] at hv
      | _ => simp [orcVs] at hv
    | _ => simp [orcVs] at hv
  | _ => simp [orcVs] at hv

/-- An oracle value of a block whose statements hold. -/
def orcOk (ss : List Stmt) (i : ℕ) : Bool := (ss.flatMap orcVs).contains (.n i)

theorem good_orc {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {ss : List Stmt}
    (hg : ∀ s ∈ ss, GoodS rd S w σ s) {i : ℕ} (h : orcOk ss i = true) : σ (.n i) = w i := by
  simp only [orcOk, List.contains_iff_mem, List.mem_flatMap] at h
  obtain ⟨s, hs, hv⟩ := h
  exact goodS_orcVs (hg s hs) _ hv

/-- A product of older values in a block. -/
def mulOk (ss : List Stmt) (q : ℕ × ℕ × ℕ) : Bool :=
  decide (q.2.1 < q.1 ∧ q.2.2 < q.1) && (atomsOf ss).contains (.mul (.n q.1) (.n q.2.1) (.n q.2.2))

theorem good_mulA {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {ss : List Stmt}
    (hg : ∀ s ∈ ss, GoodS rd S w σ s) {d a b : ℕ} (h : mulOk ss (d, a, b) = true) :
    σ (.n d) = σ (.n a) * σ (.n b) := by
  simp only [mulOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  exact good_mulF (show Good rd S w σ _ from hg _ (mem_of_mem_atomsOf h.2)) h.1.1 h.1.2

/-! ## The grind windows -/

/-- An honest grind window is `g^k`, `k < 2^11`. -/
theorem gcWin_lt {b j : ℕ} (w : E) (hb : 64 ≤ b + 11 * gcW b + 11) (hj : j ≤ gcW b) :
    ∃ k < 2 ^ 11, gcWin b w j = gen ^ k := by
  unfold gcWin gcVals
  simp only [show (2 + j = 0) = False from eq_false (by omega), show (2 + j = 1) = False from eq_false (by omega),
    ↓reduceIte]
  by_cases h : 2 + j < gcW b + 2
  · simp only [h, ↓reduceIte]
    exact ⟨_, Nat.mod_lt _ (by positivity), rfl⟩
  · simp only [h, show (2 + j = gcW b + 2) = True from eq_true (by omega), ↓reduceIte]
    refine ⟨gcV b w 0, ?_, rfl⟩
    unfold gcV
    rw [Nat.sub_zero, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact lt_of_lt_of_le (kToNat_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem gcW_15 : gcW 15 = 4 := rfl
theorem gcW_2 : gcW 2 = 5 := rfl
theorem gcW_13 : gcW 13 = 4 := rfl

theorem expTabLen_win : 178 + 2 ^ 11 ≤ expTabLen := by decide

/-! ## The parts' pointers, checked by the kernel -/

/-- `vsA`'s: the heights `.n 6`, the stream `.n 55`, the sizes `.n 56`. -/
def spA : List (ℕ × ℕ) := [(6, 5), (55, 9), (56, 5)]

/-- `vsB`'s: `.n 8`, `.n 9`, and the width's table read `.n 464`. -/
def spB : List (ℕ × ℕ) := [(8, 23), (9, 2), (464, 0)]

/-- The flag's set arm: the table read `.n 474`. -/
def spI2z : List (ℕ × ℕ) := [(474, 0)]

/-- `vsC`'s: own buffers, the stream, the grinds' table reads, the selectors' reads of `.n 18`, `.n 13`'s, the
link's and the Keccak reduction's returned cursors. -/
def spC : List (ℕ × ℕ) :=
  [(9, 3), (10, 88), (11, 29), (12, 18), (13, 19), (14, 35), (16, 5), (17, 94), (21, 63), (23, 0), (55, 10),
    (521, 178), (529, 178), (538, 178), (547, 178), (556, 178), (591, 178), (599, 178), (608, 178), (617, 178),
    (626, 178), (635, 178), (772, 0), (801, 0), (1076, 143), (1299, 0), (1411, 0), (1532, 0), (1615, 0),
    (1742, 0), (1888, 0), (2920, 0), (2952, 178), (2960, 178), (2969, 178), (2978, 178), (2987, 178)]

set_option maxRecDepth 200000 in
theorem spA_ok : (freshLoads 6 vsAf).all (specOk spA) = true := by decide +kernel

theorem spI1_ok : (freshLoads 235 vsI1f).all (specOk []) = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem spB_ok : (freshLoads 240 vsB).all (specOk spB) = true := by decide +kernel

theorem spI2z_ok : (freshLoads 472 vsI2z).all (specOk spI2z) = true := by decide +kernel

theorem spI2n_ok : (freshLoads 477 vsI2n).all (specOk []) = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem spC_ok : (freshLoads 482 vsC).all (specOk spC) = true := by decide +kernel

/-- `vsC`'s products defining pointers: a table read's `.n 4 · g^k`, a buffer's `base · g^n`. -/
def mulsC : List (ℕ × ℕ × ℕ) :=
  [(521, 4, 516), (529, 4, 515), (538, 4, 514), (547, 4, 513), (556, 4, 512), (591, 4, 586), (599, 4, 585),
    (608, 4, 584), (617, 4, 583), (626, 4, 582), (635, 4, 581), (801, 13, 101), (1299, 18, 115), (1411, 18, 116),
    (1532, 18, 117), (1615, 18, 118), (1742, 18, 119), (1888, 18, 120), (2952, 4, 2947), (2960, 4, 2946),
    (2969, 4, 2945), (2978, 4, 2944), (2987, 4, 2943)]

/-- `vsC`'s oracle values the pointers use: the grind windows and the returned cursors. -/
def orcsC : List ℕ :=
  [512, 513, 514, 515, 516, 581, 582, 583, 584, 585, 586, 2943, 2944, 2945, 2946, 2947, 772, 1076, 2920]

set_option maxRecDepth 200000 in
theorem mulsC_ok : mulsC.all (mulOk vsC) = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem orcsC_ok : orcsC.all (orcOk vsC) = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem orcsA_ok : [55, 56].all (orcOk vsAf) = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem mulB_ok : mulOk vsB (464, 4, 409) = true := by decide +kernel

/-! ## On a context -/

namespace VsCtx

variable {x : VsCtx}

/-- **What `VsAvoid` reads off a context**: the placement's bounds, the chunk count, a causal return rule,
the values the table reads and the selectors' reads are built from, and the three returned cursors in the
stream's buffer. -/
structure AvoidHyp (x : VsCtx) : Prop where
  ht : x.qt + expTabLen ≤ x.fp
  hfc : x.fp + B2C.fs "verify_sub" ≤ x.cur
  hcur : x.cur < 2 ^ 60
  hp1 : 1 ≤ x.p
  hp : x.p ≤ 32
  hret : CausalRule x.ret
  n409 : ∃ n, 1 ≤ n ∧ n ≤ 24 ∧ x.σ0 (.n 409) = gen ^ n
  n101 : ∃ n ≤ 24, x.σ0 (.n 101) = gen ^ n
  sel : ∀ t ≤ 5, ∃ n ≤ 24, x.σ0 (.n (115 + t)) = gen ^ n
  rets : ∀ i ∈ [772, 1076, 2920], ∃ a, x.w i = ptrAt a ∧ x.base 18 ≤ a ∧ a ≤ x.base 18 + 256 * x.p

theorem base_eqA (j : ℕ) : x.base j = (bases x.cur (vsAllocSz x.p)).getD j 0 := rfl

theorem sz_len : (vsAllocSz x.p).length = 24 := rfl

/-- **An own buffer's pointer**, at `k` past its base, read up to `m` inside the buffer. -/
theorem ptrOff_buf (hx : x.AvoidHyp) {i j k m s : ℕ} (hj : j < 24) (h13 : j ≠ 13)
    (hv : x.σ0 (.n i) = ptrAt (x.base j + k)) (hs : (vsAllocSz x.p).getD j 0 = s) (hm : k + m < s) :
    PtrOff x.σ0 (x.base 13) i m := by
  have hin := bases_getD_in x.cur (vsAllocSz x.p) j (by rw [sz_len]; exact hj)
  have hsum : (vsAllocSz x.p).sum = 982 + 256 * x.p := vsAllocSz_sum x.p
  have hc := hx.hcur
  have hp := hx.hp
  refine ⟨x.base j + k, hv, ?_, ?_⟩
  · rw [base_eqA]; omega
  · rcases Nat.lt_or_gt_of_ne h13 with h | h
    · have := bases_getD_lt x.cur (vsAllocSz x.p) j 13 h (by rw [sz_len]; norm_num)
      left; rw [base_eqA, base_eqA]; omega
    · have := bases_getD_lt x.cur (vsAllocSz x.p) 13 j h (by rw [sz_len]; exact hj)
      have h12 : (vsAllocSz x.p).getD 13 0 = 12 := rfl
      right; rw [base_eqA, base_eqA]; omega

/-- **A table read** below the frame. -/
theorem ptrOff_tab (hx : x.AvoidHyp) {i k m : ℕ} (hv : x.σ0 (.n i) = ptrAt (x.qt + k)) (hm : k + m < 178 + 2 ^ 11) :
    PtrOff x.σ0 (x.base 13) i m := by
  have hE := expTabLen_win
  have hin := bases_getD_in x.cur (vsAllocSz x.p) 13 (by rw [sz_len]; norm_num)
  have ht := hx.ht
  have hf := hx.hfc
  have hc := hx.hcur
  refine ⟨x.qt + k, hv, ?_, Or.inl ?_⟩
  · omega
  · rw [base_eqA]; omega

/-- **A returned cursor** in the stream's buffer, read up to `143` past it. -/
theorem ptrOff_ret (hx : x.AvoidHyp) {i a m : ℕ} (hv : x.σ0 (.n i) = ptrAt a) (h1 : x.base 18 ≤ a)
    (h2 : a ≤ x.base 18 + 256 * x.p) (hm : m ≤ 143) : PtrOff x.σ0 (x.base 13) i m := by
  have hin := bases_getD_in x.cur (vsAllocSz x.p) 18 (by rw [sz_len]; norm_num)
  have hlt := bases_getD_lt x.cur (vsAllocSz x.p) 13 18 (by norm_num) (by rw [sz_len]; norm_num)
  have hsum : (vsAllocSz x.p).sum = 982 + 256 * x.p := vsAllocSz_sum x.p
  have h12 : (vsAllocSz x.p).getD 13 0 = 12 := rfl
  have h18 : (vsAllocSz x.p).getD 18 0 = 256 * x.p := rfl
  have hc := hx.hcur
  have hp := hx.hp
  rw [base_eqA] at h1 h2
  refine ⟨a, hv, ?_, Or.inr ?_⟩
  · omega
  · rw [base_eqA]; omega

/-- The buffers' pointers are the oracle's allocations. -/
theorem σ0_buf (hr : CausalRule x.ret) {i j : ℕ} (hj : j < 24) (hi : vsAllocIdx.getD j 0 = i)
    (hv : x.σ0 (.n i) = x.w i) : x.σ0 (.n i) = ptrAt (x.base j + 0) := by
  rw [hv, ← hi]
  exact vsW_alloc (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p) rfl hr hj

theorem σ0_fixed {i : ℕ} (hi : 6 ≤ i ∧ i < 24) : x.σ0 (.n i) = x.w i :=
  vsVal_fixed (rd0 := x.rd0) (w := x.w) (args := x.args) rfl hi

theorem σ0_4 : x.σ0 (.n 4) = ptrAt x.qt :=
  vsVal_param (rd := x.rd0) (w := x.w) (args := x.args) rfl (by norm_num : 4 < 6)

theorem σ0_orcC {i : ℕ} (h : i ∈ orcsC) : x.σ0 (.n i) = x.w i :=
  good_orc (vsVal_goodC (rd := x.rd0) (w := x.w) (args := x.args) rfl) (List.all_eq_true.mp orcsC_ok i h)

theorem σ0_mulC {d a b : ℕ} (h : (d, a, b) ∈ mulsC) : x.σ0 (.n d) = x.σ0 (.n a) * x.σ0 (.n b) :=
  good_mulA (vsVal_goodC (rd := x.rd0) (w := x.w) (args := x.args) rfl) (List.all_eq_true.mp mulsC_ok _ h)

/-- The honest grind windows are `g^k`, `k < 2^11`. -/
theorem w_win (hr : CausalRule x.ret) {i : ℕ}
    (h : (512 ≤ i ∧ i ≤ 516) ∨ (581 ≤ i ∧ i ≤ 586) ∨ (2943 ≤ i ∧ i ≤ 2947)) : ∃ k < 2 ^ 11, x.w i = gen ^ k := by
  have e := vsW_eq (rd1 := x.rd1) (cur := x.cur) (p := x.p) (args := x.args) (ret := x.ret) rfl hr i
  have h1 : i ∉ vsAllocIdx := by
    simp only [vsAllocIdx, List.mem_cons, List.not_mem_nil, or_false]; omega
  have h2 : i ≠ 42 := by omega
  rw [show x.w i = _ from e]
  unfold vsRule
  simp only [h1, h2, ↓reduceIte]
  rcases h with h | h | h
  · simp only [h, and_self, ↓reduceIte]; exact gcWin_lt _ (by decide) (by rw [gcW_15]; omega)
  · simp only [show (512 ≤ i ∧ i ≤ 516) = False from eq_false (by omega), h, and_self, ↓reduceIte]
    exact gcWin_lt _ (by decide) (by rw [gcW_2]; omega)
  · simp only [show (512 ≤ i ∧ i ≤ 516) = False from eq_false (by omega),
      show (581 ≤ i ∧ i ≤ 586) = False from eq_false (by omega), h, and_self, ↓reduceIte]
    exact gcWin_lt _ (by decide) (by rw [gcW_13]; omega)

/-- A grind's table read: `.n 4` times a window. -/
theorem ptrOff_win (hx : x.AvoidHyp) {d y : ℕ} (hq : (d, 4, y) ∈ mulsC) (hy : y ∈ orcsC)
    (hw : (512 ≤ y ∧ y ≤ 516) ∨ (581 ≤ y ∧ y ≤ 586) ∨ (2943 ≤ y ∧ y ≤ 2947)) : PtrOff x.σ0 (x.base 13) d 178 := by
  obtain ⟨k, hk, hwk⟩ := w_win hx.hret hw
  refine ptrOff_tab hx (k := k) ?_ (by omega)
  rw [σ0_mulC hq, σ0_4, σ0_orcC hy, hwk, ptrAt_mul_pow]

/-- A selector's read of `.n 18`: buffer `12` at `g^n`, `n ≤ 24`. -/
theorem ptrOff_sel (hx : x.AvoidHyp) {d t : ℕ} (ht : t ≤ 5) (hq : (d, 18, 115 + t) ∈ mulsC) :
    PtrOff x.σ0 (x.base 13) d 0 := by
  obtain ⟨n, hn, hv⟩ := hx.sel t ht
  refine ptrOff_buf hx (j := 12) (k := n) (s := 25) (by norm_num) (by norm_num) ?_ rfl (by omega)
  rw [σ0_mulC hq, σ0_buf hx.hret (i := 18) (j := 12) (by norm_num) rfl (σ0_fixed (by norm_num)), Nat.add_zero, hv,
    ptrAt_mul_pow]

/-- A returned cursor. -/
theorem ptrOff_retC (hx : x.AvoidHyp) {i m : ℕ} (hi : i ∈ [772, 1076, 2920]) (hm : m ≤ 143) :
    PtrOff x.σ0 (x.base 13) i m := by
  obtain ⟨a, hw, h1, h2⟩ := hx.rets i hi
  have hc : i ∈ orcsC := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> decide
  exact ptrOff_ret hx (by rw [σ0_orcC hc, hw]) h1 h2 hm

/-- A fixed buffer `.n (j + 6)`, read inside it. -/
theorem ptrOff_fixed (hx : x.AvoidHyp) {j m s : ℕ} (hj : j < 18) (h13 : j ≠ 13)
    (hs : (vsAllocSz x.p).getD j 0 = s) (hm : m < s) : PtrOff x.σ0 (x.base 13) (j + 6) m :=
  ptrOff_buf hx (by omega) h13
    (σ0_buf hx.hret (i := j + 6) (by omega) (by interval_cases j <;> rfl) (σ0_fixed (by omega))) hs (by omega)

theorem base13_lt (hx : x.AvoidHyp) : x.base 13 + 12 < 2 ^ 64 - 1 := by
  have hin := bases_getD_in x.cur (vsAllocSz x.p) 13 (by rw [sz_len]; norm_num)
  have hsum : (vsAllocSz x.p).sum = 982 + 256 * x.p := vsAllocSz_sum x.p
  have h12 : (vsAllocSz x.p).getD 13 0 = 12 := rfl
  have hc := hx.hcur
  have hp := hx.hp
  rw [base_eqA]; omega

/-- **No fresh load of `verify_sub` reads the overlay's cells**, from `AvoidHyp`. -/
theorem vsAvoid_of_hyp (hx : x.AvoidHyp) : x.VsAvoid := by
  have hb := base13_lt hx
  have hp1 := hx.hp1
  refine ⟨avoidAt_of_spec spA_ok hb ?_, fun _ => avoidAt_of_spec spI1_ok hb (by simp),
    avoidAt_of_spec spB_ok hb ?_, fun h => avoidAt_of_spec spI2z_ok hb ?_,
    fun _ => avoidAt_of_spec spI2n_ok hb (by simp), avoidAt_of_spec spC_ok hb ?_⟩
  · -- `vsA`
    have hA : ∀ i ∈ [55, 56], x.σ0 (.n i) = x.w i := fun i hi =>
      good_orc (vsVal_goodA (rd := x.rd0) (w := x.w) (args := x.args) rfl) (List.all_eq_true.mp orcsA_ok i hi)
    simp only [spA, List.forall_mem_cons]
    refine ⟨ptrOff_fixed hx (j := 0) (s := 6) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_buf hx (j := 18) (s := 256 * x.p) (by norm_num) (by norm_num)
        (σ0_buf hx.hret (i := 55) (by norm_num) rfl (hA 55 (by simp))) rfl (by omega),
      ptrOff_buf hx (j := 19) (s := 6) (by norm_num) (by norm_num)
        (σ0_buf hx.hret (i := 56) (by norm_num) rfl (hA 56 (by simp))) rfl (by norm_num), by simp⟩
  · -- `vsB`
    obtain ⟨n, hn1, hn2, h409⟩ := hx.n409
    have e1 : x.σ0 (.n 464) = x.σ0 (.n 4) * x.σ0 (.n 409) :=
      good_mulA (d := 464) (a := 4) (b := 409) (vsVal_goodB (rd := x.rd0) (w := x.w) (args := x.args) rfl) mulB_ok
    have e464 : x.σ0 (.n 464) = ptrAt (x.qt + n) := by rw [e1, σ0_4, h409, ptrAt_mul_pow]
    simp only [spB, List.forall_mem_cons]
    refine ⟨ptrOff_fixed hx (j := 2) (s := 24) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_fixed hx (j := 3) (s := 4) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_tab hx e464 (by omega), by simp⟩
  · -- the flag's set arm
    obtain ⟨n, hn1, hn2, h409⟩ := hx.n409
    have hg := vsVal_goodI2z (rd := x.rd0) (w := x.w) (args := x.args) rfl h
    have e472 : x.σ0 (.n 472) = word 9223372036854775821 0 := hg (.atom (.const (.n 472) _)) (by simp [vsI2z])
    have e473 : x.σ0 (.n 473) = x.σ0 (.n 409) * x.σ0 (.n 472) :=
      good_mulA (d := 473) (a := 409) (b := 472) hg (by decide +kernel)
    have e474 : x.σ0 (.n 474) = x.σ0 (.n 4) * x.σ0 (.n 473) := good_mulA (d := 474) (a := 4) (b := 473) hg (by decide +kernel)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have e : x.σ0 (.n 474) = ptrAt (x.qt + n') := by
      rw [e474, e473, e472, h409, σ0_4, pow_succ, mul_assoc, winv1_mul, mul_one, ptrAt_mul_pow]
    simp only [spI2z, List.forall_mem_cons]
    exact ⟨ptrOff_tab hx e (by omega), by simp⟩
  · -- `vsC`
    obtain ⟨n, hn, h101⟩ := hx.n101
    have e801 : x.σ0 (.n 801) = ptrAt (x.base 7 + n) := by
      rw [σ0_mulC (d := 801) (a := 13) (b := 101) (by decide), σ0_buf hx.hret (i := 13) (j := 7) (by norm_num) rfl
        (σ0_fixed (by norm_num)), Nat.add_zero, h101, ptrAt_mul_pow]
    simp only [spC, List.forall_mem_cons]
    refine ⟨ptrOff_fixed hx (j := 3) (s := 4) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_fixed hx (j := 4) (s := 153) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_fixed hx (j := 5) (s := 30) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_fixed hx (j := 6) (s := 24) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_fixed hx (j := 7) (s := 25) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_fixed hx (j := 8) (s := 36) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_fixed hx (j := 10) (s := 6) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_fixed hx (j := 11) (s := 126) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_fixed hx (j := 15) (s := 64) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_fixed hx (j := 17) (s := 1) (by norm_num) (by norm_num) rfl (by norm_num),
      ptrOff_buf hx (j := 18) (s := 256 * x.p) (by norm_num) (by norm_num) (σ0_buf hx.hret (i := 55) (by norm_num) rfl
        (good_orc (vsVal_goodA (rd := x.rd0) (w := x.w) (args := x.args) rfl)
          (List.all_eq_true.mp orcsA_ok 55 (by simp)))) rfl (by omega),
      ptrOff_win hx (y := 516) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 515) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 514) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 513) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 512) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 586) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 585) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 584) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 583) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 582) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 581) (by decide) (by decide) (by omega),
      ptrOff_retC hx (by simp) (by norm_num),
      ptrOff_buf hx (j := 7) (s := 25) (by norm_num) (by norm_num) e801 rfl (by omega),
      ptrOff_retC hx (by simp) (by norm_num),
      ptrOff_sel hx (t := 0) (by norm_num) (by decide),
      ptrOff_sel hx (t := 1) (by norm_num) (by decide),
      ptrOff_sel hx (t := 2) (by norm_num) (by decide),
      ptrOff_sel hx (t := 3) (by norm_num) (by decide),
      ptrOff_sel hx (t := 4) (by norm_num) (by decide),
      ptrOff_sel hx (t := 5) (by norm_num) (by decide),
      ptrOff_retC hx (by simp) (by norm_num),
      ptrOff_win hx (y := 2947) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 2946) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 2945) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 2944) (by decide) (by decide) (by omega),
      ptrOff_win hx (y := 2943) (by decide) (by decide) (by omega), by simp⟩

/-! ## At the honest context -/

/-- **`AvoidHyp` at an honest context**: from the placement, a causal return rule, the front's numbers `Num6`,
the link's data (`Lk2.Ok`: `link_rounds`' returned cursor `w 772`) and `Ph12`'s (`D3.Ok`: the packed message's
cursor `w 1076`, `verify_keccak`'s returned cursor `w 2920`). -/
theorem avoidHyp_of (hok : x.Ok) (hret : CausalRule x.ret) (h6 : x.Num6) {L : Lk2} (hL : L.Ok x) {D : D3}
    (hD : D.Ok x) : x.AvoidHyp := by
  obtain ⟨layout, r, hann, -, hN⟩ := frontNum_of_child hok.child
  have hl : x.lay = layout := by simp [VsCtx.lay, hann]
  have ha : x.args.length = 6 := rfl
  have wret : ∀ i, i ∉ vsAllocIdx → i ≠ 42 → ¬(512 ≤ i ∧ i ≤ 516) → ¬(581 ≤ i ∧ i ≤ 586) →
      ¬(2943 ≤ i ∧ i ≤ 2947) → x.w i = x.ret i fun j => vsVal x.rd1 x.w x.args (.n j) :=
    fun i h1 h2 h3 h4 h5 => vsW_ret (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p) ha hret h1 h2 h3 h4 h5
  refine ⟨hok.ht, hok.hfc, hok.hcur, hN.hp1, hN.hp, hret, ⟨x.wdS, ?_, ?_, h6.n409⟩, ⟨x.mS, ?_, h6.n101⟩,
    fun t ht => ?_, fun i hi => ?_⟩
  · have := hN.hw19; simp only [VsCtx.wdS, hl]; omega
  · exact (by simp only [VsCtx.wdS, hl]; exact hN.hw24)
  · have := hN.hmw; have := hN.hw24; simp only [VsCtx.mS, hl]; omega
  · rcases Nat.eq_zero_or_pos t with rfl | h0
    · refine ⟨x.h0S, ?_, h6.n115⟩
      simp only [VsCtx.h0S, hl]; exact hN.h24 0 (by norm_num)
    · refine ⟨x.hgS t, ?_, h6.sel t h0 ht⟩
      simp only [VsCtx.hgS, hl]; exact hN.h24 t (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · have hb := hL.hbIn
      refine ⟨L.b772, ?_, hb.1, by omega⟩
      rw [wret 772 (by decide) (by norm_num) (by omega) (by omega) (by omega),
        show x.ret 772 _ = _ from hL.r767 5 (by norm_num) _, hL.h772]
    · have hb := hD.hbmIn
      exact ⟨D.bm, hD.hbm, hb.1, by omega⟩
    · have hb := hD.hbmIn
      refine ⟨D.bm + 144 + D.nx, ?_, by omega, by omega⟩
      have hc5 : (capOf D.s'.perm).length = 5 := rfl
      rw [wret 2920 (by decide) (by norm_num) (by omega) (by omega) (by omega),
        show x.ret 2920 _ = _ from hD.rvk 5 (by norm_num) _, vkRets, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [hc5]), hc5]
      simp [ptrAt_mul_pow]

/-- **No fresh load of `verify_sub` reads the overlay's cells** at an honest context. -/
theorem vsAvoid_of (hok : x.Ok) (hret : CausalRule x.ret) (h6 : x.Num6) {L : Lk2} (hL : L.Ok x) {D : D3}
    (hD : D.Ok x) : x.VsAvoid :=
  vsAvoid_of_hyp (avoidHyp_of hok hret h6 hL hD)

/-- **`Hon.fresh` (`Bw3.fresh`) at an honest context.** -/
theorem fresh_of (hok : x.Ok) (hret : CausalRule x.ret) (h6 : x.Num6) {L : Lk2} (hL : L.Ok x) {D : D3}
    (hD : D.Ok x) : VsFresh x.rd1 x.rd0 x.w x.args :=
  fresh_of_avoid (vsAvoid_of hok hret h6 hL hD)

end VsCtx

end
end LeanVM.Guest.B1.VsC
