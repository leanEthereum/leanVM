/-
  LeanVM.Guest.B1.VsC.VsPh3

  `verify_sub`'s windows `wB` (statements `181 ..< 427`: the cycle count's bits, the link's shape,
  `cycles < 2^w`, the flag) and the pointer width's branch (`IteHyp` at `.n 471`).
-/

module

public import LeanVM.Guest.B1.VsC.VsPh2W
public import LeanVM.Guest.B1.VerifySub.PhLinkShape

/-!
# Phase 3: the cycle bits and the link's shape

`vsB0` (statements `181 ..< 422`, `vsB_w0`): `g_cycles = g^N` from the row counts' product, the heap
hint of `N`'s `24` bits at `cbits` (`.n 8`), each read and pinned `b = b²`, their factors' product asserted
equal to `g_cycles`; the heap witness `link_shape` (`g^n`, `g^w`, the flag, `g^p`) at `.n 9`; each height
`h_t ≤ n ≤ h_t + 24`, `n` one of them; `19 ≤ w ≤ 24`; `m ≤ w ≤ m + 24`; `g^(2^w - 1 - N)` from the exponent
table's `g^(2^w)`. `vsB_w1`: `assert_small_g_power` of it (`N < 2^w`). `vsB_w2`: the flag a bit, the
selector `.n 471 = flag + 1`. The flag set (`wI2z`): `assert_small_g_power` of `g^(N - 2^(w - 1))`; clear
(`wI2n`): `w = m` or `w = 19`.

* `cb_vals`: the bits' values and the product `g^(N mod 2^(k + 1))` after block `k`.
* **`vsPh3_wins`**: `WinsHyp … wB st (fun s => IteHyp … (.n 471) wI2z wI2n s K)` from the numeric facts.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The window's atoms -/

/-- Block `0` of the cycle bits. -/
def cbAt0 : List Atom :=
  [.load (.n 241) (.n 8) 0, .mul (.n 242) (.n 241) (.n 241), .load (.n 242) (.n 8) 0, .const (.n 243) (word 1 0),
    .const (.n 244) (word 3 0), .mul (.n 245) (.n 241) (.n 244), .add (.n 246) (.n 243) (.n 245)]

/-- Block `k ≥ 1` of the cycle bits. -/
def cbAtK (k : ℕ) : List Atom :=
  [.load (.n (240 + 7 * k)) (.n 8) k, .mul (.n (241 + 7 * k)) (.n (240 + 7 * k)) (.n (240 + 7 * k)),
    .load (.n (241 + 7 * k)) (.n 8) k, .const (.n (242 + 7 * k)) (word 1 0),
    .const (.n (243 + 7 * k)) (word (VerifySub.cbC.getD k 0) 0),
    .mul (.n (244 + 7 * k)) (.n (240 + 7 * k)) (.n (243 + 7 * k)),
    .add (.n (245 + 7 * k)) (.n (242 + 7 * k)) (.n (244 + 7 * k)),
    .mul (.n (246 + 7 * k)) (.n (239 + 7 * k)) (.n (245 + 7 * k))]

/-- The link's shape checks (statements `375 ..< 422`). -/
def vsSh : List Atom := [
    .hint (.witness "link_shape" (.heap (.n 9) 0 4)),
    .load (.n 408) (.n 9) 0, .load (.n 409) (.n 9) 1, .load (.n 410) (.n 9) 2,
    .const (.n 411) (word 16777216 0), .mul (.n 408) (.n 412) (.n 115),
    .rangeCheck (.n 412) (.n 413) (.n 414) (.n 415) (.n 411), .add (.n 416) (.n 408) (.n 115),
    .const (.n 417) (word 16777216 0), .mul (.n 408) (.n 418) (.n 116),
    .rangeCheck (.n 418) (.n 419) (.n 420) (.n 421) (.n 417), .add (.n 422) (.n 408) (.n 116),
    .mul (.n 423) (.n 416) (.n 422),
    .const (.n 424) (word 16777216 0), .mul (.n 408) (.n 425) (.n 117),
    .rangeCheck (.n 425) (.n 426) (.n 427) (.n 428) (.n 424), .add (.n 429) (.n 408) (.n 117),
    .mul (.n 430) (.n 423) (.n 429),
    .const (.n 431) (word 16777216 0), .mul (.n 408) (.n 432) (.n 118),
    .rangeCheck (.n 432) (.n 433) (.n 434) (.n 435) (.n 431), .add (.n 436) (.n 408) (.n 118),
    .mul (.n 437) (.n 430) (.n 436),
    .const (.n 438) (word 16777216 0), .mul (.n 408) (.n 439) (.n 119),
    .rangeCheck (.n 439) (.n 440) (.n 441) (.n 442) (.n 438), .add (.n 443) (.n 408) (.n 119),
    .mul (.n 444) (.n 437) (.n 443),
    .const (.n 445) (word 16777216 0), .mul (.n 408) (.n 446) (.n 120),
    .rangeCheck (.n 446) (.n 447) (.n 448) (.n 449) (.n 445), .add (.n 450) (.n 408) (.n 120),
    .mul (.n 451) (.n 444) (.n 450),
    .const (.n 452) (word 0 0), .assertEq (.n 451) (.n 452),
    .const (.n 453) (word 32 0), .const (.n 454) (word 10248187242686185485 0),
    .mul (.n 455) (.n 409) (.n 454), .rangeCheck (.n 455) (.n 456) (.n 457) (.n 458) (.n 453),
    .const (.n 459) (word 16777216 0), .mul (.n 409) (.n 460) (.n 101),
    .rangeCheck (.n 460) (.n 461) (.n 462) (.n 463) (.n 459),
    .mul (.n 464) (.n 4) (.n 409), .load (.n 465) (.n 464) 0,
    .const (.n 466) (word 9223372036854775821 0), .mul (.n 467) (.n 465) (.n 466),
    .mul (.n 467) (.n 468) (.n 240)]

/-- Statements `181 ..< 422`. -/
def vsB0 : List Atom :=
  [.mul (.n 240) (.n 216) (.n 224), .hint (.bitsExp (.n 240) 24 (.heap (.n 8) 0 24))] ++ cbAt0 ++
    ((List.range 23).map fun i => cbAtK (i + 1)).flatten ++ [.assertEq (.n 407) (.n 240)] ++ vsSh

/-- Statements `423 ..< 427`. -/
def vsB2 : List Atom :=
  [.mul (.n 469) (.n 410) (.n 410), .assertEq (.n 469) (.n 410), .const (.n 470) (word 1 0),
    .add (.n 471) (.n 410) (.n 470)]

/-- Statement `422`. -/
def vsB1s : Stmt := .call "assert_small_g_power" [.n 468, .n 4] []

/-- The flag set's atoms. -/
def vsZ : List Atom :=
  [.const (.n 472) (word 9223372036854775821 0), .mul (.n 473) (.n 409) (.n 472), .mul (.n 474) (.n 4) (.n 473),
    .load (.n 475) (.n 474) 0, .mul (.n 240) (.n 476) (.n 475)]

/-- The flag set's call. -/
def vsZs : Stmt := .call "assert_small_g_power" [.n 476, .n 4] []

/-- The flag clear's atoms. -/
def vsNa : List Atom :=
  [.add (.n 477) (.n 409) (.n 101), .const (.n 478) (word 524288 0), .add (.n 479) (.n 409) (.n 478),
    .mul (.n 480) (.n 477) (.n 479), .const (.n 481) (word 0 0), .assertEq (.n 480) (.n 481)]

set_option maxRecDepth 200000 in
theorem vsB0_eq : (vsB.drop 0).take 241 = vsB0.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsB1_eq : (vsB.drop 241).take 1 = [vsB1s] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsB2_eq : (vsB.drop 242).take 4 = vsB2.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

theorem wB_eq : wB = [.run vsB0, .call vsB1s, .run vsB2] := by
  rw [wB, vsB_w0, vsB_w1, vsB_w2, vsB0_eq, vsB2_eq, atomsOf_map, atomsOf_map, headD_of_take_one vsB1_eq]

theorem wI2z_eq : wI2z = [.run vsZ, .call vsZs] := rfl

theorem wI2n_eq : wI2n = [.run vsNa] := rfl

/-- The cycle bits' loads. -/
def cbLoads : List Atom :=
  (List.range 24).flatMap fun k => [.load (.n (VerifySub.cbV k)) (.n 8) k, .load (.n (VerifySub.cbV k + 1)) (.n 8) k]

set_option maxRecDepth 200000 in
theorem vsB0_mem : vsB0.filter memAsks =
    cbLoads ++ [.load (.n 408) (.n 9) 0, .load (.n 409) (.n 9) 1, .load (.n 410) (.n 9) 2,
      .load (.n 465) (.n 464) 0] := by decide +kernel

set_option maxRecDepth 200000 in
theorem vsB0_pure : vsB0.filter pureAsks = [.assertEq (.n 407) (.n 240)] ++ vsSh.filter pureAsks := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem vsSh_pure : vsSh.filter pureAsks = [
    .mul (.n 408) (.n 412) (.n 115), .rangeCheck (.n 412) (.n 413) (.n 414) (.n 415) (.n 411),
    .mul (.n 408) (.n 418) (.n 116), .rangeCheck (.n 418) (.n 419) (.n 420) (.n 421) (.n 417),
    .mul (.n 408) (.n 425) (.n 117), .rangeCheck (.n 425) (.n 426) (.n 427) (.n 428) (.n 424),
    .mul (.n 408) (.n 432) (.n 118), .rangeCheck (.n 432) (.n 433) (.n 434) (.n 435) (.n 431),
    .mul (.n 408) (.n 439) (.n 119), .rangeCheck (.n 439) (.n 440) (.n 441) (.n 442) (.n 438),
    .mul (.n 408) (.n 446) (.n 120), .rangeCheck (.n 446) (.n 447) (.n 448) (.n 449) (.n 445),
    .assertEq (.n 451) (.n 452), .rangeCheck (.n 455) (.n 456) (.n 457) (.n 458) (.n 453),
    .mul (.n 409) (.n 460) (.n 101), .rangeCheck (.n 460) (.n 461) (.n 462) (.n 463) (.n 459),
    .mul (.n 467) (.n 468) (.n 240)] := by decide +kernel

set_option maxRecDepth 200000 in
/-- The fresh loads of `vsB0`: the bits as first read, the shape, the table's word. -/
theorem vsB0_fresh : (((List.range 24).all fun k => !(storesOf 240 vsB).contains (.load (.n (VerifySub.cbV k)) (.n 8) k)) &&
    ([Atom.load (.n 408) (.n 9) 0, .load (.n 409) (.n 9) 1, .load (.n 410) (.n 9) 2, .load (.n 465) (.n 464) 0].all
      fun a => !(storesOf 240 vsB).contains a)) = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem vsZ_fresh : (storesOf 472 vsI2z).contains (.load (.n 475) (.n 474) 0) = false := by decide +kernel

set_option maxRecDepth 200000 in
theorem vsB0_hints (σ : Val) : heapHintAddrs σ (vsB0.map Ev.atom) =
    (List.range 24).map (fun j => (σ (.n 8)).limb 0 * addressOfIndex (0 + j)) ++
      (List.range 4).map (fun j => (σ (.n 9)).limb 0 * addressOfIndex (0 + j)) := rfl

set_option maxRecDepth 200000 in
theorem vsB0_allocs (σ : Val) : allocDsts (vsB0.map Ev.atom) = [] ∧ allocs σ (vsB0.map Ev.atom) = [] :=
  ⟨rfl, rfl⟩

/-! ## Arithmetic -/

theorem bv_bitE (N k : ℕ) : Link.bv (Link.bitE N k) = N / 2 ^ k % 2 := by
  rw [Link.bitE_eq, ← Nat.shiftRight_eq_div_pow]
  unfold Link.bv
  rcases Nat.mod_two_eq_zero_or_one (N >>> k) with h | h
  · simp [h]
  · simp [h]

/-- One more bit's factor. -/
theorem cb_factor (N k : ℕ) : gen ^ (N % 2 ^ k) * (1 + Link.bitE N k * (gen ^ 2 ^ k + 1)) = gen ^ (N % 2 ^ (k + 1)) := by
  have hb : Link.bitE N k = Link.bitE N k * Link.bitE N k := (bitE_mul_self N k).symm
  rw [Link.bit_factor hb, ← pow_add]
  congr 1
  rw [Nat.mod_pow_succ]
  change N % 2 ^ k + 2 ^ k * Link.bv (Link.bitE N k) = _
  rw [bv_bitE]

theorem pow_ne {m : ℕ} : gen ^ m ≠ 0 := pow_ne_zero _ Value.gen_ne_zero

theorem isInK_pow (m : ℕ) : IsInK (gen ^ m) := by rw [Value.gen_pow_eq_ofK]; exact Value.ofK_isInK _

theorem isInK_one' : IsInK (1 : E) := by simpa using isInK_pow 0

/-- `cbits`' words. -/
def cbL (N : ℕ) : List E := (List.range 24).map (Link.bitE N)

/-! ## The values -/

section
variable {rd0 : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

theorem good_mulF {d x y : ℕ} (h : Good rd0 S w σ (.mul (.n d) (.n x) (.n y))) (hx : x < d) (hy : y < d) :
    σ (.n d) = σ (.n x) * σ (.n y) := by
  have hc : (V.n x).idx < (V.n d).idx ∧ (V.n y).idx < (V.n d).idx := ⟨hx, hy⟩
  simpa only [Good, hc, and_self, ↓reduceIte] using h

theorem good_mulD {d x y : ℕ} (h : Good rd0 S w σ (.mul (.n d) (.n x) (.n y))) (hx : d < x) :
    σ (.n x) = σ (.n d) * (σ (.n y))⁻¹ := by
  have hc : ¬ ((V.n x).idx < (V.n d).idx ∧ (V.n y).idx < (V.n d).idx) := fun h => by
    have : x < d := h.1
    omega
  simpa only [Good, hc, ↓reduceIte] using h

theorem good_rcY {x y t1 t2 kk : ℕ} (h : Good rd0 S w σ (.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n kk)))
    (hk : kk < y) : σ (.n y) = σ (.n kk) * (σ (.n x))⁻¹ := by
  have hc : (V.n kk).idx < (V.n y).idx := hk
  simpa only [hc, ↓reduceIte] using h.2.2

/-- The range check's two words, low. -/
theorem rc_pureF {k : ℕ} {x y t1 t2 kk a b : ℕ} (hk : 6 ≤ k) (hb : b ≤ 32) (hab : a ≤ b)
    (hg : Good rd0 S w σ (.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n kk))) (hlt : kk < y)
    (hx : σ (.n x) = gen ^ a) (hkk : σ (.n kk) = gen ^ b) :
    PureF k σ (.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n kk)) := by
  have hy := good_rcY hg hlt
  rw [hkk, hx, gen_div hab] at hy
  exact ⟨by rw [hx]; exact lowW_pow (lt_two_pow_k hk (by omega)), by rw [hy]; exact lowW_pow (lt_two_pow_k hk (by omega))⟩

theorem pureF_div {k : ℕ} {d x y : ℕ} (hy : σ (.n y) ≠ 0) : PureF k σ (.mul (.n d) (.n x) (.n y)) := by
  show (if (V.n x).idx < (V.n d).idx ∧ (V.n y).idx < (V.n d).idx then True else σ (.n y) ≠ 0)
  split
  · trivial
  · exact hy

end

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

theorem vsB0_good (ha : args.length = 6) : ∀ a ∈ vsB0, Good rd0 (storesOf 240 vsB) w (vsVal rd0 w args) a := by
  intro a hm
  have h1 : Stmt.atom a ∈ (vsB.drop 0).take 241 := by rw [vsB0_eq]; exact List.mem_map_of_mem hm
  have hb : Stmt.atom a ∈ vsB := List.mem_of_mem_drop (List.mem_of_mem_take h1)
  exact vsVal_goodB ha (.atom a) hb

theorem cbAtK_mem {k : ℕ} (h1 : 1 ≤ k) (h2 : k < 24) {a : Atom} (ha : a ∈ cbAtK k) : a ∈ vsB0 :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr
    ⟨_, List.mem_map.mpr ⟨k - 1, List.mem_range.mpr (by omega), by rw [Nat.sub_add_cancel h1]⟩, ha⟩)))

theorem cbAt0_mem {a : Atom} (ha : a ∈ cbAt0) : a ∈ vsB0 :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))

theorem vsSh_mem {a : Atom} (ha : a ∈ vsSh) : a ∈ vsB0 := List.mem_append_right _ ha

/-- **The cycle bits' values**: each bit as read and pinned, the product after block `k`. -/
theorem cb_vals (ha : args.length = 6) {N b8 : ℕ} (p8 : vsVal rd0 w args (.n 8) = ptrAt b8)
    (r8 : ReadsAt rd0 (ptrAt b8) (cbL N)) :
    (∀ k < 24, vsVal rd0 w args (.n (VerifySub.cbV k)) = Link.bitE N k ∧
      vsVal rd0 w args (.n (VerifySub.cbV k + 1)) = Link.bitE N k) ∧
    ∀ k < 24, vsVal rd0 w args (.n (246 + 7 * k)) = gen ^ (N % 2 ^ (k + 1)) := by
  have hg := vsB0_good (rd0 := rd0) (w := w) ha
  set σ := vsVal rd0 w args
  have fr := vsB0_fresh
  rw [Bool.and_eq_true] at fr
  have fresh : ∀ k < 24, Atom.load (.n (VerifySub.cbV k)) (.n 8) k ∉ storesOf 240 vsB := fun k hk h => by
    have := List.all_eq_true.mp fr.1 k (List.mem_range.mpr hk)
    rw [List.contains_iff_mem.mpr h] at this
    exact absurd this (by decide)
  have mem0 : ∀ k < 24, Atom.load (.n (VerifySub.cbV k)) (.n 8) k ∈ vsB0 ∧
      Atom.mul (.n (VerifySub.cbV k + 1)) (.n (VerifySub.cbV k)) (.n (VerifySub.cbV k)) ∈ vsB0 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact ⟨cbAt0_mem (by simp [cbAt0, VerifySub.cbV]), cbAt0_mem (by simp [cbAt0, VerifySub.cbV])⟩
    · have hv : VerifySub.cbV k = 240 + 7 * k := by simp [VerifySub.cbV]; omega
      rw [hv, show 240 + 7 * k + 1 = 241 + 7 * k by omega]
      exact ⟨cbAtK_mem hk1 hk (by simp [cbAtK]), cbAtK_mem hk1 hk (by simp [cbAtK])⟩
  have bits : ∀ k < 24, σ (.n (VerifySub.cbV k)) = Link.bitE N k ∧ σ (.n (VerifySub.cbV k + 1)) = Link.bitE N k := by
    intro k hk
    have v : σ (.n (VerifySub.cbV k)) = Link.bitE N k := by
      have := good_loadAt (fresh k hk) (hg _ (mem0 k hk).1) p8 (by simpa [cbL] using hk) r8
      rw [this]; simp [cbL]
    refine ⟨v, ?_⟩
    have hlt : VerifySub.cbV k < VerifySub.cbV k + 1 := by omega
    rw [good_mulF (hg _ (mem0 k hk).2) hlt hlt, v, bitE_mul_self]
  refine ⟨bits, fun k hk => ?_⟩
  induction k with
  | zero =>
    have e245 := good_mulF (hg _ (cbAt0_mem (a := .mul (.n 245) (.n 241) (.n 244)) (by simp [cbAt0]))) (by omega) (by omega)
    have e246 : σ (.n 246) = σ (.n 243) + σ (.n 245) := hg (.add (.n 246) (.n 243) (.n 245)) (cbAt0_mem (by simp [cbAt0]))
    have e243 : σ (.n 243) = word 1 0 := hg (.const (.n 243) (word 1 0)) (cbAt0_mem (by simp [cbAt0]))
    have e244 : σ (.n 244) = word 3 0 := hg (.const (.n 244) (word 3 0)) (cbAt0_mem (by simp [cbAt0]))
    have c3 : word 3 0 = gen ^ 2 ^ 0 + 1 := by simpa [VerifySub.cbC] using VerifySub.cbC_eq 0 (by norm_num)
    have b0 : σ (.n 241) = Link.bitE N 0 := (bits 0 (by norm_num)).1
    rw [show 246 + 7 * 0 = 246 from rfl, e246, e245, e243, e244, b0, c3, one_eq_word, ← cb_factor N 0]
    simp [Nat.mod_one]
  | succ j ih =>
    have hk1 : 1 ≤ j + 1 := by omega
    set k := j + 1 with hkdef
    have mk := fun {a : Atom} (h : a ∈ cbAtK k) => hg a (cbAtK_mem hk1 hk h)
    have e246 := good_mulF (mk (a := .mul (.n (246 + 7 * k)) (.n (239 + 7 * k)) (.n (245 + 7 * k)))
      (by simp [cbAtK])) (by omega) (by omega)
    have e245 : σ (.n (245 + 7 * k)) = σ (.n (242 + 7 * k)) + σ (.n (244 + 7 * k)) :=
      mk (a := .add (.n (245 + 7 * k)) (.n (242 + 7 * k)) (.n (244 + 7 * k))) (by simp [cbAtK])
    have e244 := good_mulF (mk (a := .mul (.n (244 + 7 * k)) (.n (240 + 7 * k)) (.n (243 + 7 * k)))
      (by simp [cbAtK])) (by omega) (by omega)
    have e242 : σ (.n (242 + 7 * k)) = word 1 0 := mk (a := .const (.n (242 + 7 * k)) (word 1 0)) (by simp [cbAtK])
    have e243 : σ (.n (243 + 7 * k)) = word (VerifySub.cbC.getD k 0) 0 :=
      mk (a := .const (.n (243 + 7 * k)) (word (VerifySub.cbC.getD k 0) 0)) (by simp [cbAtK])
    have bk := (bits k hk).1
    have hv : VerifySub.cbV k = 240 + 7 * k := by simp [VerifySub.cbV, hkdef]
    rw [hv] at bk
    have hprev : 239 + 7 * k = 246 + 7 * j := by omega
    rw [e246, hprev, ih (by omega), e245, e244, e242, e243, bk, VerifySub.cbC_eq k hk, one_eq_word, cb_factor]

theorem vsB2_good (ha : args.length = 6) : ∀ a ∈ vsB2, Good rd0 (storesOf 240 vsB) w (vsVal rd0 w args) a := by
  intro a hm
  have h1 : Stmt.atom a ∈ (vsB.drop 242).take 4 := by rw [vsB2_eq]; exact List.mem_map_of_mem hm
  exact vsVal_goodB ha (.atom a) (List.mem_of_mem_drop (List.mem_of_mem_take h1))

end

/-! ## The window's hypotheses -/

theorem sizeBits_gt : 24 < sizeBits := by decide

theorem readsAt_one {rd : Reader} {a m : ℕ} {v : E} (h : LoadHolds rd (ptrAt a) m v) :
    ReadsAt rd (ptrAt (a + m)) [v] := fun j hj => by
  have : j = 0 := by simpa using hj
  subst this
  rw [← ptrAt_add, loadHolds_mul_gen_pow]
  simpa using h

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`vsB0`'s hypotheses**: the cycle count `N` (`g^N` the row counts' product), its bits at `b8`, the
shape `g^n`, `g^w`, the flag at `b9`, the heights at most `n`, one of them `n`, `19 ≤ w ≤ 24`, `m ≤ w`,
`N < 2^w`, the exponent table at `qt`. -/
theorem vsB0_runHyp (hk : 6 ≤ k) (ha : args.length = 6) {a : ℕ} {D : ℕ → Prop} {O : Reader → Prop}
    {b8 b9 qt N1 N2 n wd m : ℕ} {flag f4 : E} (h : ℕ → ℕ)
    (h216 : vsVal rd0 w args (.n 216) = gen ^ N1) (h224 : vsVal rd0 w args (.n 224) = gen ^ N2)
    (hv : ∀ t < 6, vsVal rd0 w args (.n (115 + t)) = gen ^ h t) (h101 : vsVal rd0 w args (.n 101) = gen ^ m)
    (h4 : vsVal rd0 w args (.n 4) = ptrAt qt) (hw8 : w 8 = ptrAt b8) (hw9 : w 9 = ptrAt b9)
    (hht : ∀ t < 6, h t ≤ n) (hn : ∃ t < 6, h t = n) (hn24 : n ≤ 24)
    (hw19 : 19 ≤ wd) (hw24 : wd ≤ 24) (hmw : m ≤ wd) (hN : N1 + N2 < 2 ^ wd)
    (r8 : ReadsAt rd0 (ptrAt b8) (cbL (N1 + N2))) (r9 : ReadsAt rd0 (ptrAt b9) [gen ^ n, gen ^ wd, flag, f4])
    (rq : ExpTables rd0 (ptrAt qt))
    (hO8 : ∀ j < 24, Own (b8 + j)) (hO9 : ∀ j < 4, Own (b9 + j)) (hRq : ∀ j < 178, R (qt + j))
    (hPre : ∀ rd, Pre rd → ExpTables rd (ptrAt qt))
    (hrd : ∀ rd, O rd → ReadsAt rd (ptrAt b8) (cbL (N1 + N2)) ∧ ReadsAt rd (ptrAt b9) [gen ^ n, gen ^ wd, flag, f4]) :
    RunHyp k (vsVal rd0 w args) w a Own R D Pre O vsB0 ∧ vsVal rd0 w args (.n 240) = gen ^ (N1 + N2) ∧
      vsVal rd0 w args (.n 409) = gen ^ wd ∧ vsVal rd0 w args (.n 410) = flag ∧
      vsVal rd0 w args (.n 468) = gen ^ (2 ^ wd - 1 - (N1 + N2)) := by
  have hg := vsB0_good (rd0 := rd0) (w := w) ha
  set σ := vsVal rd0 w args with hσ
  set N := N1 + N2 with hNdef
  have sh : ∀ x ∈ vsSh, Good rd0 (storesOf 240 vsB) w σ x := fun x hx => hg x (vsSh_mem hx)
  have p8 : σ (.n 8) = ptrAt b8 := (vsW0_good ha (a := .hint (.alloc (.n 8) 24)) (by simp [vsW0, vsW0a])).trans hw8
  have p9 : σ (.n 9) = ptrAt b9 := (vsW0_good ha (a := .hint (.alloc (.n 9) 4)) (by simp [vsW0, vsW0a])).trans hw9
  obtain ⟨bits, prod⟩ := cb_vals (rd0 := rd0) (w := w) ha p8 r8
  have hN24 : N < 2 ^ 24 := lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) hw24)
  have e240 : σ (.n 240) = gen ^ N := by
    rw [good_mulF (hg (.mul (.n 240) (.n 216) (.n 224)) (by simp [vsB0])) (by omega) (by omega), h216, h224,
      ← pow_add]
  have e407 : σ (.n 407) = gen ^ N := by
    have := prod 23 (by norm_num); rwa [Nat.mod_eq_of_lt hN24] at this
  have fr := vsB0_fresh
  rw [Bool.and_eq_true] at fr
  have fr2 : ∀ x ∈ [Atom.load (.n 408) (.n 9) 0, .load (.n 409) (.n 9) 1, .load (.n 410) (.n 9) 2,
      .load (.n 465) (.n 464) 0], x ∉ storesOf 240 vsB := fun x hx h' => by
    have := List.all_eq_true.mp fr.2 x hx
    rw [List.contains_iff_mem.mpr h'] at this
    exact absurd this (by decide)
  have ld : ∀ (d j : ℕ) (hj : j < 3), Atom.load (.n d) (.n 9) j ∈ vsSh → d = 408 + j →
      σ (.n d) = [gen ^ n, gen ^ wd, flag, f4][j]'(by simp; omega) := by
    intro d j hj hm hd
    subst hd
    exact good_loadAt (fr2 _ (by rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> simp))
      (sh _ hm) p9 (by simp; omega) r9
  have e408 : σ (.n 408) = gen ^ n := ld 408 0 (by norm_num) (by simp [vsSh]) rfl
  have e409 : σ (.n 409) = gen ^ wd := ld 409 1 (by norm_num) (by simp [vsSh]) rfl
  have e410 : σ (.n 410) = flag := ld 410 2 (by norm_num) (by simp [vsSh]) rfl
  have cs : ∀ (d : ℕ) (e : E), Atom.const (.n d) e ∈ vsSh → σ (.n d) = e := fun d e h => sh _ h
  have g24 : ∀ d, Atom.const (.n d) (word 16777216 0) ∈ vsSh → σ (.n d) = gen ^ 24 := fun d h =>
    (cs d _ h).trans (wordG (j := 24) (by norm_num))
  -- the heights' divisions and range checks
  have qv : ∀ t < 6, ∀ q, Atom.mul (.n 408) (.n q) (.n (115 + t)) ∈ vsSh → 408 < q →
      σ (.n q) = gen ^ (n - h t) := fun t ht q hm hq => by
    rw [good_mulD (sh _ hm) hq, e408, hv t ht, gen_div (hht t ht)]
  have hv' : ∀ t < 6, σ (.n (115 + t)) ≠ 0 := fun t ht => by rw [hv t ht]; exact pow_ne
  -- the product of `g^n + g^(h t)`
  have adv : ∀ t < 6, ∀ q, Atom.add (.n q) (.n 408) (.n (115 + t)) ∈ vsSh → σ (.n q) = gen ^ n + gen ^ h t :=
    fun t ht q hm => by rw [show σ (.n q) = σ (.n 408) + σ (.n (115 + t)) from sh _ hm, e408, hv t ht]
  have mf : ∀ d x y, Atom.mul (.n d) (.n x) (.n y) ∈ vsSh → x < d → y < d → σ (.n d) = σ (.n x) * σ (.n y) :=
    fun d x y hm hx hy => good_mulF (sh _ hm) hx hy
  have e451 : σ (.n 451) = 0 := by
    rw [mf 451 444 450 (by simp [vsSh]) (by omega) (by omega), mf 444 437 443 (by simp [vsSh]) (by omega) (by omega),
      mf 437 430 436 (by simp [vsSh]) (by omega) (by omega), mf 430 423 429 (by simp [vsSh]) (by omega) (by omega),
      mf 423 416 422 (by simp [vsSh]) (by omega) (by omega),
      adv 0 (by norm_num) 416 (by simp [vsSh]), adv 1 (by norm_num) 422 (by simp [vsSh]),
      adv 2 (by norm_num) 429 (by simp [vsSh]), adv 3 (by norm_num) 436 (by simp [vsSh]),
      adv 4 (by norm_num) 443 (by simp [vsSh]), adv 5 (by norm_num) 450 (by simp [vsSh])]
    obtain ⟨t, ht, htn⟩ := hn
    have z : ∀ s, s = t → gen ^ n + gen ^ h s = 0 := fun s hs => by rw [hs, htn]; exact Link.add_self_E _
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [z _ rfl]
  have e452 : σ (.n 452) = 0 := (cs 452 _ (by simp [vsSh])).trans zero_eq_word
  have e453 : σ (.n 453) = gen ^ 5 := (cs 453 _ (by simp [vsSh])).trans (wordG (j := 5) (by norm_num))
  have e455 : σ (.n 455) = gen ^ (wd - 19) := by
    rw [mf 455 409 454 (by simp [vsSh]) (by omega) (by omega), e409, cs 454 (word 10248187242686185485 0) (by simp [vsSh]),
      VerifySub.pow_mul_winv19 hw19]
  have e460 : σ (.n 460) = gen ^ (wd - m) := by
    rw [good_mulD (sh (.mul (.n 409) (.n 460) (.n 101)) (by simp [vsSh])) (by omega), e409, h101, gen_div hmw]
  have e464 : σ (.n 464) = ptrAt (qt + wd) := by
    rw [mf 464 4 409 (by simp [vsSh]) (by omega) (by omega), h4, e409, ptrAt_add]
  have rq1 : ReadsAt rd0 (ptrAt (qt + wd)) [gen ^ 2 ^ wd] := readsAt_one (rq.1 wd (by have := sizeBits_gt; omega))
  have e465 : σ (.n 465) = gen ^ 2 ^ wd :=
    good_loadAt (fr2 _ (by simp)) (sh (.load (.n 465) (.n 464) 0) (by simp [vsSh])) e464 (by simp) rq1
  have e467 : σ (.n 467) = gen ^ (2 ^ wd - 1) := by
    rw [mf 467 465 466 (by simp [vsSh]) (by omega) (by omega), e465, cs 466 (word 9223372036854775821 0) (by simp [vsSh])]
    exact VerifySub.pow_mul_ginv Nat.one_le_two_pow
  have e468 : σ (.n 468) = gen ^ (2 ^ wd - 1 - N) := by
    rw [good_mulD (sh (.mul (.n 467) (.n 468) (.n 240)) (by simp [vsSh])) (by omega), e467, e240,
      gen_div (by omega)]
  refine ⟨?_, e240, e409, e410, e468⟩
  have hi := vsB0_hints σ
  refine RunHyp.of_asks (by rw [(vsB0_allocs σ).1, (vsB0_allocs σ).2]; rfl) ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨d, p, off, hm, rfl⟩ := mem_loadAddrs hA
    have hm' : Atom.load d p off ∈ vsB0.filter memAsks := List.mem_filter.mpr ⟨hm, rfl⟩
    rw [vsB0_mem, List.mem_append] at hm'
    rcases hm' with hm' | hm'
    · simp only [cbLoads, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
        Atom.load.injEq] at hm'
      obtain ⟨j, hj, ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩ := hm'
      all_goals exact ⟨b8 + off, by rw [p8, ptrAt, B1.Main.addr_ofK], Or.inl (hO8 off hj)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Atom.load.injEq] at hm'
      rcases hm' with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
      · exact ⟨b9 + 0, by rw [p9, ptrAt, B1.Main.addr_ofK], Or.inl (hO9 0 (by norm_num))⟩
      · exact ⟨b9 + 1, by rw [p9, ptrAt, B1.Main.addr_ofK], Or.inl (hO9 1 (by norm_num))⟩
      · exact ⟨b9 + 2, by rw [p9, ptrAt, B1.Main.addr_ofK], Or.inl (hO9 2 (by norm_num))⟩
      · exact ⟨qt + wd + 0, by rw [e464, ptrAt, B1.Main.addr_ofK],
          Or.inr (Or.inl (by simpa using hRq wd (by omega)))⟩
  · intro A hA
    rw [hi, List.mem_append, List.mem_map, List.mem_map] at hA
    rcases hA with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [List.mem_range] at hj
      exact ⟨b8 + (0 + j), by rw [p8, ptrAt, B1.Main.addr_ofK], Or.inl (by simpa using hO8 j hj)⟩
    · rw [List.mem_range] at hj
      exact ⟨b9 + (0 + j), by rw [p9, ptrAt, B1.Main.addr_ofK], Or.inl (by simpa using hO9 j hj)⟩
  · intro x hx
    rw [vsB0_pure, List.mem_append, vsSh_pure] at hx
    have rcF := fun {x y t1 t2 kk aa bb : ℕ} (hm : Atom.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n kk) ∈ vsSh)
      (hb : bb ≤ 32) (hab : aa ≤ bb) (hlt : kk < y) (hx : σ (.n x) = gen ^ aa) (hkk : σ (.n kk) = gen ^ bb) =>
      rc_pureF (k := k) hk hb hab (sh _ hm) hlt hx hkk
    have hh : ∀ t < 6, n - h t ≤ 24 := fun t _ => by omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · show σ (.n 407) + σ (.n 240) = 0
      rw [e407, e240]; exact Link.add_self_E _
    · exact pureF_div (hv' 0 (by norm_num))
    · exact rcF (by simp [vsSh]) (by norm_num) (hh 0 (by norm_num)) (by omega)
        (qv 0 (by norm_num) 412 (by simp [vsSh]) (by omega)) (g24 411 (by simp [vsSh]))
    · exact pureF_div (hv' 1 (by norm_num))
    · exact rcF (by simp [vsSh]) (by norm_num) (hh 1 (by norm_num)) (by omega)
        (qv 1 (by norm_num) 418 (by simp [vsSh]) (by omega)) (g24 417 (by simp [vsSh]))
    · exact pureF_div (hv' 2 (by norm_num))
    · exact rcF (by simp [vsSh]) (by norm_num) (hh 2 (by norm_num)) (by omega)
        (qv 2 (by norm_num) 425 (by simp [vsSh]) (by omega)) (g24 424 (by simp [vsSh]))
    · exact pureF_div (hv' 3 (by norm_num))
    · exact rcF (by simp [vsSh]) (by norm_num) (hh 3 (by norm_num)) (by omega)
        (qv 3 (by norm_num) 432 (by simp [vsSh]) (by omega)) (g24 431 (by simp [vsSh]))
    · exact pureF_div (hv' 4 (by norm_num))
    · exact rcF (by simp [vsSh]) (by norm_num) (hh 4 (by norm_num)) (by omega)
        (qv 4 (by norm_num) 439 (by simp [vsSh]) (by omega)) (g24 438 (by simp [vsSh]))
    · exact pureF_div (hv' 5 (by norm_num))
    · exact rcF (by simp [vsSh]) (by norm_num) (hh 5 (by norm_num)) (by omega)
        (qv 5 (by norm_num) 446 (by simp [vsSh]) (by omega)) (g24 445 (by simp [vsSh]))
    · show σ (.n 451) + σ (.n 452) = 0
      rw [e451, e452, add_zero]
    · exact rcF (by simp [vsSh]) (by norm_num) (show wd - 19 ≤ 5 by omega) (by omega) e455 e453
    · exact pureF_div (by rw [h101]; exact pow_ne)
    · exact rcF (by simp [vsSh]) (by norm_num) (show wd - m ≤ 24 by omega) (by omega) e460
        (g24 459 (by simp [vsSh]))
    · exact pureF_div (by rw [e240]; exact pow_ne)
  · intro rd _ hp ho x hx
    obtain ⟨q8, q9⟩ := hrd rd ho
    rw [vsB0_mem, List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [cbLoads, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨j, hj, rfl | rfl⟩ := hx
      · show LoadHolds rd (σ (.n 8)) j (σ (.n (VerifySub.cbV j)))
        rw [p8, show σ (.n (VerifySub.cbV j)) = Link.bitE N j from (bits j hj).1]
        have := q8 j (by simpa [cbL] using hj)
        simpa [cbL] using this
      · show LoadHolds rd (σ (.n 8)) j (σ (.n (VerifySub.cbV j + 1)))
        rw [p8, show σ (.n (VerifySub.cbV j + 1)) = Link.bitE N j from (bits j hj).2]
        have := q8 j (by simpa [cbL] using hj)
        simpa [cbL] using this
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · show LoadHolds rd (σ (.n 9)) 0 (σ (.n 408)); rw [p9, e408]; exact q9 0 (by simp)
      · show LoadHolds rd (σ (.n 9)) 1 (σ (.n 409)); rw [p9, e409]; exact q9 1 (by simp)
      · show LoadHolds rd (σ (.n 9)) 2 (σ (.n 410)); rw [p9, e410]; exact q9 2 (by simp)
      · show LoadHolds rd (σ (.n 464)) 0 (σ (.n 465)); rw [e464, e465]
        exact readsAt_one ((hPre rd hp).1 wd (by have := sizeBits_gt; omega)) 0 (by simp)

/-- **`vsB2`'s hypotheses**: the flag a bit; the selector `flag + 1`. -/
theorem vsB2_runHyp (ha : args.length = 6) {a : ℕ} {D : ℕ → Prop} {O : Reader → Prop} {flag : E}
    (hf : flag = 0 ∨ flag = 1) (e410 : vsVal rd0 w args (.n 410) = flag) :
    RunHyp k (vsVal rd0 w args) w a Own R D Pre O vsB2 ∧ vsVal rd0 w args (.n 471) = flag + 1 := by
  have hg := vsB2_good (rd0 := rd0) (w := w) ha
  set σ := vsVal rd0 w args
  have e469 : σ (.n 469) = flag * flag := by
    rw [good_mulF (hg (.mul (.n 469) (.n 410) (.n 410)) (by simp [vsB2])) (by omega) (by omega), e410]
  have e470 : σ (.n 470) = 1 := (hg (.const (.n 470) (word 1 0)) (by simp [vsB2])).trans one_eq_word
  have e471 : σ (.n 471) = flag + 1 := by
    rw [show σ (.n 471) = σ (.n 410) + σ (.n 470) from hg (.add (.n 471) (.n 410) (.n 470)) (by simp [vsB2]), e410,
      e470]
  refine ⟨RunHyp.of_asks rfl (fun A hA => ?_) (fun A hA => ?_) (fun x hx => ?_) (fun rd _ _ _ x hx => ?_), e471⟩
  · rw [show loadAddrs σ (vsB2.map Ev.atom) = [] from rfl] at hA; simp at hA
  · rw [show heapHintAddrs σ (vsB2.map Ev.atom) = [] from rfl] at hA; simp at hA
  · rw [show vsB2.filter pureAsks = [.assertEq (.n 469) (.n 410)] by decide +kernel] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    show σ (.n 469) + σ (.n 410) = 0
    rw [e469, e410]
    rcases hf with rfl | rfl
    · simp
    · rw [mul_one]; exact Link.add_self_E _
  · rw [show vsB2.filter memAsks = [] by decide +kernel] at hx; simp at hx


/-- **The flag set's run**: `g^(N - 2^(w - 1))` from the exponent table's `g^(2^(w - 1))`. -/
theorem vsZ_runHyp (ha : args.length = 6) (h0 : vsVal rd0 w args (.n 471) = 0) {a : ℕ} {D : ℕ → Prop}
    {O : Reader → Prop} {qt N wd : ℕ} (hw1 : 1 ≤ wd) (hw24 : wd ≤ 24) (hNw : 2 ^ (wd - 1) ≤ N)
    (e240 : vsVal rd0 w args (.n 240) = gen ^ N) (e409 : vsVal rd0 w args (.n 409) = gen ^ wd)
    (h4 : vsVal rd0 w args (.n 4) = ptrAt qt) (rq : ExpTables rd0 (ptrAt qt)) (hRq : ∀ j < 178, R (qt + j))
    (hPre : ∀ rd, Pre rd → ExpTables rd (ptrAt qt)) :
    RunHyp k (vsVal rd0 w args) w a Own R D Pre O vsZ ∧
      vsVal rd0 w args (.n 476) = gen ^ (N - 2 ^ (wd - 1)) := by
  set σ := vsVal rd0 w args
  have hg : ∀ x ∈ vsZ, Good rd0 (storesOf 472 vsI2z) w σ x := fun x hx =>
    vsVal_goodI2z ha h0 (.atom x) (by simp only [vsZ, List.mem_cons, List.not_mem_nil, or_false] at hx
                                      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [vsI2z])
  have e472 : σ (.n 472) = Digest.ginvW := hg (.const (.n 472) (word 9223372036854775821 0)) (by simp [vsZ])
  have e473 : σ (.n 473) = gen ^ (wd - 1) := by
    rw [good_mulF (hg (.mul (.n 473) (.n 409) (.n 472)) (by simp [vsZ])) (by omega) (by omega), e409, e472,
      VerifySub.pow_mul_ginv hw1]
  have e474 : σ (.n 474) = ptrAt (qt + (wd - 1)) := by
    rw [good_mulF (hg (.mul (.n 474) (.n 4) (.n 473)) (by simp [vsZ])) (by omega) (by omega), h4, e473, ptrAt_add]
  have fr : Atom.load (.n 475) (.n 474) 0 ∉ storesOf 472 vsI2z := fun h => by
    have := vsZ_fresh
    rw [List.contains_iff_mem.mpr h] at this
    exact absurd this (by decide)
  have hlt : wd - 1 < sizeBits := by have := sizeBits_gt; omega
  have e475 : σ (.n 475) = gen ^ 2 ^ (wd - 1) :=
    good_loadAt fr (hg (.load (.n 475) (.n 474) 0) (by simp [vsZ])) e474 (by simp) (readsAt_one (rq.1 _ hlt))
  have e476 : σ (.n 476) = gen ^ (N - 2 ^ (wd - 1)) := by
    rw [good_mulD (hg (.mul (.n 240) (.n 476) (.n 475)) (by simp [vsZ])) (by omega), e240, e475, gen_div hNw]
  refine ⟨RunHyp.of_asks rfl (fun A hA => ?_) (fun A hA => ?_) (fun x hx => ?_) (fun rd _ hp _ x hx => ?_), e476⟩
  · obtain ⟨d, p, off, hm, rfl⟩ := mem_loadAddrs hA
    simp only [vsZ, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or, Atom.load.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact ⟨qt + (wd - 1) + 0, by rw [e474, ptrAt, B1.Main.addr_ofK], Or.inr (Or.inl (by simpa using hRq _ (by omega)))⟩
  · rw [show heapHintAddrs σ (vsZ.map Ev.atom) = [] from rfl] at hA; simp at hA
  · rw [show vsZ.filter pureAsks = [.mul (.n 240) (.n 476) (.n 475)] by decide +kernel] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact pureF_div (by rw [e475]; exact pow_ne)
  · rw [show vsZ.filter memAsks = [.load (.n 475) (.n 474) 0] by decide +kernel] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    show LoadHolds rd (σ (.n 474)) 0 (σ (.n 475))
    rw [e474, e475]
    exact readsAt_one ((hPre rd hp).1 _ hlt) 0 (by simp)

/-- **The flag clear's run**: `w = m` or `w = 19`. -/
theorem vsNa_runHyp (ha : args.length = 6) (h0 : vsVal rd0 w args (.n 471) ≠ 0) {a : ℕ} {D : ℕ → Prop}
    {O : Reader → Prop} {wd m : ℕ} (hwm : wd = m ∨ wd = 19)
    (e409 : vsVal rd0 w args (.n 409) = gen ^ wd) (h101 : vsVal rd0 w args (.n 101) = gen ^ m) :
    RunHyp k (vsVal rd0 w args) w a Own R D Pre O vsNa := by
  set σ := vsVal rd0 w args
  have hg : ∀ x ∈ vsNa, Good rd0 (storesOf 477 vsI2n) w σ x := fun x hx =>
    vsVal_goodI2n ha h0 (.atom x) (by simp only [vsNa, List.mem_cons, List.not_mem_nil, or_false] at hx
                                      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [vsI2n])
  have e477 : σ (.n 477) = gen ^ wd + gen ^ m := by
    rw [show σ (.n 477) = σ (.n 409) + σ (.n 101) from hg (.add (.n 477) (.n 409) (.n 101)) (by simp [vsNa]), e409,
      h101]
  have e478 : σ (.n 478) = gen ^ 19 :=
    (hg (.const (.n 478) (word 524288 0)) (by simp [vsNa])).trans (wordG (j := 19) (by norm_num))
  have e479 : σ (.n 479) = gen ^ wd + gen ^ 19 := by
    rw [show σ (.n 479) = σ (.n 409) + σ (.n 478) from hg (.add (.n 479) (.n 409) (.n 478)) (by simp [vsNa]), e409,
      e478]
  have e480 : σ (.n 480) = 0 := by
    rw [good_mulF (hg (.mul (.n 480) (.n 477) (.n 479)) (by simp [vsNa])) (by omega) (by omega), e477, e479]
    rcases hwm with rfl | rfl
    · rw [Link.add_self_E, zero_mul]
    · rw [Link.add_self_E, mul_zero]
  have e481 : σ (.n 481) = 0 := (hg (.const (.n 481) (word 0 0)) (by simp [vsNa])).trans zero_eq_word
  refine RunHyp.of_asks rfl (fun A hA => ?_) (fun A hA => ?_) (fun x hx => ?_) (fun rd _ _ _ x hx => ?_)
  · rw [show loadAddrs σ (vsNa.map Ev.atom) = [] from rfl] at hA; simp at hA
  · rw [show heapHintAddrs σ (vsNa.map Ev.atom) = [] from rfl] at hA; simp at hA
  · rw [show vsNa.filter pureAsks = [.assertEq (.n 480) (.n 481)] by decide +kernel] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    show σ (.n 480) + σ (.n 481) = 0
    rw [e480, e481, add_zero]
  · rw [show vsNa.filter memAsks = [] by decide +kernel] at hx; simp at hx

/-- **Phase 3's windows' hypotheses** (`wB`) and the pointer width's branch (`IteHyp` at `.n 471`): the
cycle count `N = N1 + N2` (the row counts' products `g^N1`, `g^N2`), its bits at `b8`; the link's shape
(`g^n`, `g^w`, the flag, a fourth word) at `b9`; `n` the largest height; `19 ≤ w ≤ 24`, `m ≤ w`,
`N < 2^w`; the flag set with `2^(w - 1) ≤ N` or clear with `w ∈ {m, 19}`; the exponent tables at `qt`;
`K` after either arm. -/
theorem vsPh3_wins (hk : 6 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    {b8 b9 qt N1 N2 n wd m : ℕ} {flag f4 : E} (h : ℕ → ℕ)
    (h216 : vsVal rd0 w args (.n 216) = gen ^ N1) (h224 : vsVal rd0 w args (.n 224) = gen ^ N2)
    (hv : ∀ t < 6, vsVal rd0 w args (.n (115 + t)) = gen ^ h t) (h101 : vsVal rd0 w args (.n 101) = gen ^ m)
    (h4 : vsVal rd0 w args (.n 4) = ptrAt qt) (hw8 : w 8 = ptrAt b8) (hw9 : w 9 = ptrAt b9)
    (hht : ∀ t < 6, h t ≤ n) (hn : ∃ t < 6, h t = n) (hn24 : n ≤ 24)
    (hw19 : 19 ≤ wd) (hw24 : wd ≤ 24) (hmw : m ≤ wd) (hN : N1 + N2 < 2 ^ wd)
    (hflag : (flag = 1 ∧ 2 ^ (wd - 1) ≤ N1 + N2) ∨ (flag = 0 ∧ (wd = m ∨ wd = 19)))
    (r8 : ReadsAt rd0 (ptrAt b8) (cbL (N1 + N2))) (r9 : ReadsAt rd0 (ptrAt b9) [gen ^ n, gen ^ wd, flag, f4])
    (rq : ExpTables rd0 (ptrAt qt))
    (hO8 : ∀ j < 24, Own (b8 + j)) (hO9 : ∀ j < 4, Own (b9 + j)) (hRq : ∀ j < 178, R (qt + j))
    (hPre : ∀ rd, Pre rd → ExpTables rd (ptrAt qt))
    (hrd : ∀ rd, st.O rd → ReadsAt rd (ptrAt b8) (cbL (N1 + N2)) ∧
      ReadsAt rd (ptrAt b9) [gen ^ n, gen ^ wd, flag, f4])
    (hKz : flag = 1 → K ⟨st.a, leafEnd fs al "assert_small_g_power" (leafEnd fs al "assert_small_g_power" st.kc),
      st.O, st.D, st.Qs ++ [PostQuiet, PostQuiet]⟩)
    (hKn : flag = 0 → K ⟨st.a, leafEnd fs al "assert_small_g_power" st.kc, st.O, st.D, st.Qs ++ [PostQuiet]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre wB st
      (fun s => IteHyp fs al cert k (vsVal rd0 w args) w Own R Pre (.n 471) wI2z wI2n s K) := by
  obtain ⟨rh0, e240, e409, e410, e468⟩ := vsB0_runHyp (a := st.a) (D := st.D) (O := st.O) (Own := Own) (R := R)
    (Pre := Pre) hk ha h h216 h224 hv h101 h4 hw8 hw9 hht hn hn24 hw19 hw24 hmw hN r8 r9 rq hO8 hO9 hRq hPre hrd
  have hf : flag = 0 ∨ flag = 1 := by
    rcases hflag with ⟨h1, -⟩ | ⟨h0, -⟩
    · exact .inr h1
    · exact .inl h0
  have h24 : 2 ^ wd ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) hw24
  have region : ∀ (D : ℕ → Prop), ∀ t < 144, ∃ i, (ptrAt qt).limb 0 * addressOfIndex (34 + t) = addressOfIndex i ∧
      ((R i ∨ Own i) ∨ D i) :=
    fun D t ht => ⟨qt + (34 + t), by rw [ptrAt, B1.Main.addr_ofK], Or.inl (Or.inl (hRq _ (by omega)))⟩
  rw [wB_eq, WinsHyp]
  refine ⟨rh0, ?_⟩
  have c1 := assert_small_g_power_leafA (fs := fs) (al := al) (cert := cert) (k := k) (by omega)
    (e := 2 ^ wd - 1 - (N1 + N2)) (by omega) (region fun _ => False)
  rw [← e468, ← h4] at c1
  refine winsHyp_call_leaf (g := "assert_small_g_power") rfl c1 (fun _ hi => Or.inl (hi.resolve_right id))
    (fun rd hp => by rw [h4]; exact hPre rd hp.1) ?_
  rw [WinsHyp]
  have e471 := (vsB2_runHyp (k := k) (a := 0) (D := fun _ => False) (O := fun _ => True) (Own := Own) (R := R)
    (Pre := Pre) ha hf e410).2
  refine ⟨(vsB2_runHyp ha hf e410).1, ?_⟩
  rw [WinsHyp]
  dsimp only
  rw [IteHyp]
  refine ⟨?_, fun h0 => ?_, fun h0 => ?_⟩
  · rw [e471]
    rcases hf with rfl | rfl
    · rw [zero_add]; exact isInK_one'
    · have := isInK_add isInK_one' isInK_one'
      rwa [Link.add_self_E] at this
  · have hf1 : flag = 1 := by
      rcases hf with rfl | rfl
      · rw [e471, zero_add] at h0; exact absurd h0 one_ne_zero
      · rfl
    have hNw : 2 ^ (wd - 1) ≤ N1 + N2 := by
      rcases hflag with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [h] at hf1; exact absurd hf1 zero_ne_one
    obtain ⟨rz, e476⟩ := vsZ_runHyp (a := st.a) (D := fun i => st.D i ∨ False) (O := fun rd => st.O rd ∧ True)
      (k := k) (Own := Own) (R := R) (Pre := Pre) ha h0 (by omega) hw24 hNw e240 e409 h4 rq hRq hPre
    rw [wI2z_eq, WinsHyp]
    refine ⟨rz, ?_⟩
    have cz := assert_small_g_power_leafA (fs := fs) (al := al) (cert := cert) (k := k) (by omega)
      (e := N1 + N2 - 2 ^ (wd - 1)) (lt_of_le_of_lt (Nat.sub_le _ _) (by omega)) (region fun _ => False)
    rw [← e476, ← h4] at cz
    refine winsHyp_call_leaf (g := "assert_small_g_power") rfl cz (fun _ hi => Or.inl (hi.resolve_right id))
      (fun rd hp => by rw [h4]; exact hPre rd hp.1) ?_
    rw [WinsHyp]
    exact st_congr (hKz hf1) rfl (fun rd => by simp) (fun i => by simp) (by simp)
  · have hwm : wd = m ∨ wd = 19 := by
      rcases hflag with ⟨h1, -⟩ | ⟨-, h⟩
      · rw [e471, h1, Link.add_self_E] at h0; exact absurd rfl h0
      · exact h
    have hf0 : flag = 0 := by
      rcases hf with h | h
      · exact h
      · rw [e471, h, Link.add_self_E] at h0; exact absurd rfl h0
    rw [wI2n_eq, WinsHyp]
    refine ⟨vsNa_runHyp ha h0 hwm e409 h101, ?_⟩
    rw [WinsHyp]
    exact st_congr (hKn hf0) rfl (fun rd => by simp) (fun i => by simp) (by simp)

end

/-- **A call window's hypotheses from its callee's `CallCompletesA`, the cursor advancing**: as
`winsHyp_call_of_completesA`, the rest asked only at ends past the callees' cursor. -/
theorem winsHyp_call_of_completesA_le {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
    {σ0 : Val} {w : ℕ → E} {Own R : ℕ → Prop} {Pre : Reader → Prop} {s : Stmt} {g : String} {ws : List W0}
    {st : St} {K : St → Prop} {Rg : ℕ → Prop} {Dg : ℕ → ℕ → ℕ → Prop} {Out Preg : Reader → Prop}
    {Post : Reader → Tree → Prop} (he : Enters σ0 g s)
    (h : CallCompletesA fs al cert k g ((argsOf s).map σ0) ((retsOf s).map σ0) Rg Dg Out Preg Post)
    (hR : ∀ i, Rg i → (R i ∨ Own i) ∨ st.D i) (hP : ∀ rd, Pre rd ∧ st.O rd → Preg rd)
    (hrest : ∀ Bc ec, st.kc ≤ ec → WinsHyp fs al cert k σ0 w Own R Pre ws
      ⟨st.a, ec, fun rd => st.O rd ∧ Out rd,
        fun i => st.D i ∨ Dg (allocBase (al g) st.kc) (allocBase (al g) st.kc + Bc) i, st.Qs ++ [Post]⟩ K) :
    WinsHyp fs al cert k σ0 w Own R Pre (.call s :: ws) st K := by
  obtain ⟨Bc, ec, hc⟩ := callAt_of_completesA h hP st.kc
  have hle : st.kc ≤ ec := by
    obtain ⟨-, -, hce, -⟩ := hc
    exact le_trans (le_allocBase _ _) (le_trans (Nat.le_add_right _ _) hce)
  rw [WinsHyp]
  exact ⟨g, Post, Bc, ec, Rg, _, Out, he, hR, hc, hrest Bc ec hle⟩


/-- **The row counts' products**: `g_cycles`' two factors, `g^(R 0 + … + R 4)` at `.n 216` and `g^(R 5)` at
`.n 224`, from `table_size`'s returns. -/
theorem vsVal_216 {rd0 : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6) (Rr : ℕ → ℕ)
    (hret : ∀ t < 6, w (tsRet t) = gen ^ Rr t) :
    vsVal rd0 w args (.n 216) = gen ^ (Rr 0 + Rr 1 + Rr 2 + Rr 3 + Rr 4) ∧
      vsVal rd0 w args (.n 224) = gen ^ Rr 5 := by
  obtain ⟨e7, -, e9, e10, e11, e12, e13, e14, e15, e16, e17⟩ := vsA_tables_eq
  have ret : ∀ {i x av pv : ℕ} (t : ℕ), t < 6 → (vsA.drop i).take 1 = [tsDisp x av pv (tsRet t)] →
      vsVal rd0 w args (.n (tsRet t)) = gen ^ Rr t := fun t ht e =>
    (vsVal_disp_ret (rd0 := rd0) (w := w) ha e _ (by simp)).trans (hret t ht)
  have mul : ∀ {i n x pp pv off : ℕ}, (vsA.drop i).take 12 = (tsRun n x pp pv off).map Stmt.atom → pp < n + 8 →
      vsVal rd0 w args (.n (n + 8)) = vsVal rd0 w args (.n pp) * vsVal rd0 w args (.n n) := fun e hp =>
    good_mulF (vsA_run_goodF (rd0 := rd0) (w := w) ha e (.mul (.n (_ + 8)) (.n _) (.n _))
      (List.mem_append_right _ (by simp))) hp (by omega)
  have r0 : vsVal rd0 w args (.n 145) = gen ^ Rr 0 := ret 0 (by norm_num) e7
  have r1 : vsVal rd0 w args (.n 160) = gen ^ Rr 1 := ret 1 (by norm_num) e9
  have r2 : vsVal rd0 w args (.n 176) = gen ^ Rr 2 := ret 2 (by norm_num) e11
  have r3 : vsVal rd0 w args (.n 192) = gen ^ Rr 3 := ret 3 (by norm_num) e13
  have r4 : vsVal rd0 w args (.n 208) = gen ^ Rr 4 := ret 4 (by norm_num) e15
  have r5 : vsVal rd0 w args (.n 224) = gen ^ Rr 5 := ret 5 (by norm_num) e17
  refine ⟨?_, r5⟩
  rw [show 216 = 208 + 8 from rfl, mul e16 (by norm_num), show 200 = 192 + 8 from rfl, mul e14 (by norm_num),
    show 184 = 176 + 8 from rfl, mul e12 (by norm_num), show 168 = 160 + 8 from rfl, mul e10 (by norm_num)]
  rw [r0, r1, r2, r3, r4, ← pow_add, ← pow_add, ← pow_add, ← pow_add]

end
end LeanVM.Guest.B1.VsC
