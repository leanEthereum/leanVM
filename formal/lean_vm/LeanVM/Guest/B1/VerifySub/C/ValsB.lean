/-
  LeanVM.Guest.B1.VerifySub.C.ValsB

  `verify_sub`'s honest valuation, its back: the ring map's challenges, `c_table`, `λ` and the
  target, the tail's candidate and arguments.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Vals
public import LeanVM.Guest.B1.VerifySub.Ctab
public import LeanVM.Guest.B1.VerifySub.Lam

/-!
# The back, honestly

* `vs_maps`: the ring map's nonce `n` read at `verify_keccak`'s cursor and absorbed into its
  capacity `cap` (`vsMapSt`), the grind's cell, and the sixteen challenges `vsRchs cap n` (the
  grind's challenge, fifteen squeezed), the capacity after them;
* `vs_ctabV`: `c_table`'s products `f_p · g_b^(2^(8p))` of the challenges;
* `vs_lam`: `λ` squeezed after the challenges, and the target over the pooled claims;
* `vs_tailV`: the stream's next pointer and `tabs`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The ring map grind's permutation: the nonce `n` absorbed into the capacity `cap`. -/
def vsMapSt (cap : List E) (n : E) : KeccakState := (⟨cap, []⟩ : Fs).nonceState n

/-- The ring map's sixteen challenges: the grind's challenge, then fifteen squeezed. -/
def vsRchs (cap : List E) (n : E) : List E :=
  challengeOf (vsMapSt cap n) :: ((⟨capOf (vsMapSt cap n), []⟩ : Fs).squeezeN 15).1

/-- `verify_keccak`'s returned capacity. -/
def vsKCap (w : ℕ → E) : List E := [w 590, w 591, w 592, w 593, w 594]

variable {rd : Reader} {w : ℕ → E} {args : List E}

local notation "ς" => vsσ rd w args

/-! ## The ring map's challenges -/

theorem vsMapSqz_noSide (i : ℕ) : (vsMapSqz i).all vsNoSideB = true := by
  simp [vsMapSqz, vsSqzT, keccakA, challengeT, vsCopy, vsNoSideB, needsSide]

theorem vs_flatMap_noSide {f : ℕ → List Stmt} (hf : ∀ i, (f i).all vsNoSideB = true) :
    ∀ l : List ℕ, (l.flatMap f).all vsNoSideB = true
  | [] => rfl
  | i :: l => by rw [List.flatMap_cons, List.all_append, hf i, vs_flatMap_noSide hf l]; rfl

theorem vsMapsT_split : vsMapsT =
    (List.range 5).map (fun i ↦ vsCopy (597 + i) (590 + i)) ++ fsNonceT (.n 595) 0 602 ++
    [keccakA [.n 603, .n 604, .n 8, .n 8, .n 8, .n 9, .n 10, .n 11, .n 597, .n 598, .n 599,
      .n 600, .n 601] (vsRun 605 13)] ++ vsTabsT 618 619 ++
    [grindCallT 13 (.n 606) (.n 619), vsCopy 620 605, vsCopy 621 620] ++
    (List.range' 0 15).flatMap vsMapSqz ++
    (vsAlloc 847 16 :: (List.range 16).map (fun i ↦ vsLd (vsCh i) 847 i)) := by
  rw [vsMapsT, ← List.range_eq_range']
  rfl

/-- **The ring map's challenges**: the nonce `n` at `verify_keccak`'s cursor,
the grind's permutation `vsMapSt`, its cell `1` for `grind_check`, `tabs`, the sixteen
challenges `vsRchs` at `vsCh i`, and the capacity after them at `840 .. 844`. -/
theorem vs_maps (hl : args.length = 6) {n : E} (hn : LoadHolds rd (w 595) 0 n) :
    ς (.n 602) = n ∧ ς (.n 606) = cellsOfState (vsMapSt (vsKCap w) n) false 1 ∧
      ς (.n 619) = ς (.n 4) * gen ^ winTabAt ∧
      (∀ i < 16, ς (.n (vsCh i)) = (vsRchs (vsKCap w) n).getD i 0) ∧
      ((⟨capOf (vsMapSt (vsKCap w) n), []⟩ : Fs).squeezeN 15).2 =
        ⟨[ς (.n 840), ς (.n 841), ς (.n 842), ς (.n 843), ς (.n 844)], []⟩ := by
  have hG := vsMapsT_good (rd := rd) (w := w) hl
  rw [vsMapsT_split] at hG
  have hz := vs_zero (rd := rd) (w := w) hl
  have mA : ∀ s ∈ (List.range 5).map (fun i ↦ vsCopy (597 + i) (590 + i)),
      GoodS rd vsSL w ς s := fun s hs ↦ hG s (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ hs))))))
  have mN : ∀ s ∈ fsNonceT (.n 595) 0 602, GoodS rd vsSL w ς s :=
    fun s hs ↦ hG s (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs))))))
  have mT : ∀ s ∈ vsTabsT 618 619, GoodS rd vsSL w ς s :=
    fun s hs ↦ hG s (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hs))))
  have mQ : ∀ s ∈ (List.range' 0 15).flatMap vsMapSqz, GoodS rd vsSL w ς s :=
    fun s hs ↦ hG s (List.mem_append_left _ (List.mem_append_right _ hs))
  have hk : (Atom.keccak [.n 603, .n 604, .n 8, .n 8, .n 8, .n 9, .n 10, .n 11, .n 597, .n 598,
      .n 599, .n 600, .n 601] (vsRun 605 13) false false).Holds rd ς :=
    vsg_atom (hG _ (by simp [keccakA])) rfl
  have c620 : ς (.n 620) = ς (.n 605) := vsg_copy (hG _ (by simp [vsCopy]))
  have c621 : ς (.n 621) = ς (.n 620) := vsg_copy (hG _ (by simp [vsCopy]))
  have cA : ∀ i < 5, ς (.n (597 + i)) = w (590 + i) := fun i hi ↦ by
    rw [vsg_copy (mA _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)),
      vs_w hl (by interval_cases i <;> decide)]
  have c0 := cA 0 (by omega)
  have c1 := cA 1 (by omega)
  have c2 := cA 2 (by omega)
  have c3 := cA 3 (by omega)
  have c4 := cA 4 (by omega)
  simp only [Nat.reduceAdd] at c0 c1 c2 c3 c4
  have e602 : ς (.n 602) = n :=
    vsg_read (mN _ List.mem_cons_self) (by decide +kernel) (by rw [vs_w hl (by decide)]; exact hn)
  have pk : FsPackOk ς (.n 602) 603 dsPowNonce := vsg_fsPack fun s hs ↦ mN s (List.mem_cons_of_mem _ hs)
  have h619 := vsg_tabs (c := 618) (by decide) mT
  have hsqH := vs_holdsList_good (C := fun _ _ _ ↦ True) (kret := fun _ ↦ True)
    (vs_flatMap_noSide vsMapSqz_noSide _) mQ (next := True) trivial
  obtain ⟨hsq, -⟩ := maps_chain hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 15 0 hsqH
  -- the nonce's permutation
  set S := vsMapSt (vsKCap w) n with hS
  have hcells : cells13 ((vsRun 605 13).map ς) = cellsOfState S false := by
    rw [hS, vsMapSt, Fs.nonceState,
      show (⟨vsKCap w, []⟩ : Fs).absorb n dsPowNonce = ⟨vsKCap w, [(n, dsPowNonce)]⟩ by
        simp [Fs.absorb, rateScalars]]
    refine keccakA_fs hk (by simp) ?_
    have hp := fsPackT_cells pk
    rw [e602] at hp
    simp only [List.map_cons, List.map_nil, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2, c0, c1, c2, c3, c4,
      vsKCap]
    simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.append_nil, ← hp,
      List.length_cons, List.length_nil]
    rfl
  have hc : ∀ c : Fin 13, ς (.n (605 + c.val)) = cellsOfState S false c := fun c ↦ by
    have := congrFun hcells c
    simpa [cells13, vsRun, c.isLt] using this
  have hcap0 : capOf S = (vsRun (vsChCap 0) 5).map ς := by
    simp only [capOf, vsChCap, ↓reduceIte, vsRun5_map]
    rw [← hc 8, ← hc 9, ← hc 10, ← hc 11, ← hc 12]
    rfl
  have hch0 : challengeOf S = ς (.n (vsCh 0)) := by
    rw [Keccak.challengeOf_cells, ← hc 0]
    simp only [vsCh]
    rw [c621, c620]
    rfl
  refine ⟨e602, hc 1, h619, fun i hi ↦ ?_, ?_⟩
  · rw [vsRchs, ← hS, hcap0, hsq, hch0]
    rcases i with _ | i
    · simp only [List.getD_cons_zero]
    · rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
        List.getElem_range']
      simp
  · rw [hcap0, hsq, show vsChCap (0 + 15) = 840 from rfl, vsRun5_map]

/-! ## `c_table` -/

theorem vsSqT_noSide : ∀ b < 8, ∀ q < 7, (vsSqT b (849 + 64 * b) q).all vsNoSideB = true := by
  decide +kernel

/-- Where `c_table[8 p + b]` is computed: block `b`'s first product, then term `p`'s. -/
def vsCtabD (b p : ℕ) : ℕ := if p = 0 then 849 + 64 * b else 849 + 64 * b + 1 + 9 * (p - 1) + 8

theorem vsCtabBlock_mem {b : ℕ} (hb : b < 8) {s : Stmt} (hs : s ∈ vsCtabBlock b) : s ∈ vsCtabT := by
  rw [vsCtabT]
  exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨b, List.mem_range.2 hb, hs⟩))

/-- **`c_table`'s products**: `c[8 p + b] = f_p · g_b^(2^(8 p))`, the challenges
`f = vsCh 0 .. 7`, `g = vsCh 8 .. 15`. -/
theorem vs_ctabV (hl : args.length = 6) {b : ℕ} (hb : b < 8) :
    ∀ p < 8, ς (.n (vsCtabD b p)) = ς (.n (vsCh p)) * ς (.n (vsCh (8 + b))) ^ 2 ^ (8 * p) := by
  have hG : ∀ s ∈ vsCtabBlock b, GoodS rd vsSL w ς s :=
    fun s hs ↦ vsCtabT_good hl s (vsCtabBlock_mem hb hs)
  set s0 := 849 + 64 * b with hs0
  -- the squarings of term `q + 1` from the previous power
  have hsq : ∀ q < 7, ς (.n (if q = 0 then vsCh (8 + b) else s0 + 1 + 9 * q - 2)) =
      ς (.n (vsCh (8 + b))) ^ 2 ^ (8 * q) := by
    intro q
    induction q with
    | zero => intro _; simp
    | succ q ih =>
      intro hq
      have hS := vs_holdsList_good (C := fun _ _ _ ↦ True) (kret := fun _ ↦ True)
        (vsSqT_noSide b hb q (by omega)) (fun s hs ↦ hG s (by
          rw [vsCtabBlock]
          exact List.mem_append_right _ (List.mem_flatMap.2 ⟨q, List.mem_range.2 (by omega),
            List.mem_append_left _ hs⟩))) (next := True) trivial
      obtain ⟨e7, -⟩ := vsSqT_holds (ih (by omega)) hS
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [show s0 + 1 + 9 * (q + 1) - 2 = s0 + 1 + 9 * q + 7 by omega, e7, ← pow_mul, ← pow_add,
        show 8 * q + 8 = 8 * (q + 1) by ring]
  intro p hp
  rcases p with _ | q
  · have m := vsg_mul (by simp [vsCh]; omega) (by simp [vsCh]; omega)
      (hG (.atom (.mul (.n s0) (.n (vsCh 0)) (.n (vsCh (8 + b))))) (by
        rw [vsCtabBlock]; exact List.mem_append_left _ List.mem_cons_self))
    simp only [vsCtabD, ↓reduceIte, Nat.mul_zero, pow_zero, pow_one]
    exact m
  · have hS := vs_holdsList_good (C := fun _ _ _ ↦ True) (kret := fun _ ↦ True)
      (vsSqT_noSide b hb q (by omega)) (fun s hs ↦ hG s (by
        rw [vsCtabBlock]
        exact List.mem_append_right _ (List.mem_flatMap.2 ⟨q, List.mem_range.2 (by omega),
          List.mem_append_left _ hs⟩))) (next := True) trivial
    obtain ⟨e7, -⟩ := vsSqT_holds (hsq q (by omega)) hS
    have m := vsg_mul (x := vsCh (q + 1)) (by simp [vsCh]; omega) (by omega)
      (hG (.atom (.mul (.n (s0 + 1 + 9 * q + 8)) (.n (vsCh (q + 1))) (.n (s0 + 1 + 9 * q + 7))))
        (by
          rw [vsCtabBlock]
          exact List.mem_append_right _ (List.mem_flatMap.2 ⟨q, List.mem_range.2 (by omega),
            List.mem_append_right _ List.mem_cons_self⟩)))
    simp only [vsCtabD, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [m, e7, ← pow_mul, ← pow_add, show 8 * q + 8 = 8 * (q + 1) by ring]

/-! ## The sizes, the placement, the push blocks -/

theorem vs_word_gen1 : word 2 0 = gen := by
  rw [show (2 : ℕ) = 2 ^ 1 from rfl, word_two_pow (by norm_num), pow_one]

/-- `rate_sel = g^(rate - 1)`. -/
theorem vs_rateSel (hl : args.length = 6) {rate : ℕ} (hr : 1 ≤ rate) (h64 : w 64 = gen ^ rate) :
    ς (.n 66) = gen ^ (rate - 1) := by
  have hG := vsSizesT_good (rd := rd) (w := w) hl
  have h65w : ς (.n 65) = word 2 0 := vsg_const (hG _ (by simp [vsSizesT, vsConst]))
  have h65 : ς (.n 65) = gen := by rw [h65w, vs_word_gen1]
  have h66 : ς (.n 66) = ς (.n 64) * (ς (.n 65))⁻¹ :=
    vsg_quot (by norm_num) (hG _ (by simp [vsSizesT, vsMul]))
  rw [h66, h65, vs_w hl (by decide), h64, show gen⁻¹ = (gen ^ 1)⁻¹ by rw [pow_one],
    ← pow_sub₀ _ gen_ne_zero hr]

/-- **The sizes**: `g^(rate - 1)` and its bound `g^3`, `g^logMem` and its bound `g^30`,
`g^(logMem - 1)` and its bound `g^32`, and `kb` in the frame: `1`, `g^logMem`, `dims_g[1 .. 6]`. -/
theorem vs_sizesV (hl : args.length = 6) {rate logMem : ℕ} (hr : 1 ≤ rate) (hm : 1 ≤ logMem)
    (h64 : w 64 = gen ^ rate) (h72 : w 72 = gen ^ logMem) :
    ς (.n 65) = gen ∧ ς (.n 66) = gen ^ (rate - 1) ∧ ς (.n 67) = gen ^ 3 ∧
      ς (.n 72) = gen ^ logMem ∧ ς (.n 73) = gen ^ 30 ∧ ς (.n 78) = gen ∧
      ς (.n 79) = gen ^ (logMem - 1) ∧ ς (.n 77) = gen ^ 32 ∧
      ς (.n 84) = 1 ∧ ς (.n 85) = gen ^ logMem ∧
      ∀ t < 6, ς (.n (86 + t)) = rdAt rd (w 71) (1 + t) := by
  have hG := vsSizesT_good (rd := rd) (w := w) hl
  have h65w : ς (.n 65) = word 2 0 := vsg_const (hG _ (by simp [vsSizesT, vsConst]))
  have h65 : ς (.n 65) = gen := by rw [h65w, vs_word_gen1]
  have h66 : ς (.n 66) = ς (.n 64) * (ς (.n 65))⁻¹ :=
    vsg_quot (by norm_num) (hG _ (by simp [vsSizesT, vsMul]))
  have h67 : ς (.n 67) = word 8 0 := vsg_const (hG _ (by simp [vsSizesT, vsConst]))
  have h73 : ς (.n 73) = word 1073741824 0 := vsg_const (hG _ (by simp [vsSizesT, vsConst]))
  have h77 : ς (.n 77) = word 4294967296 0 := vsg_const (hG _ (by simp [vsSizesT, vsConst]))
  have h78 : ς (.n 78) = word 2 0 := vsg_const (hG _ (by simp [vsSizesT, vsConst]))
  have h79 : ς (.n 79) = ς (.n 72) * (ς (.n 78))⁻¹ :=
    vsg_quot (by norm_num) (hG _ (by simp [vsSizesT, vsMul]))
  have h84 : ς (.n 84) = word 1 0 := vsg_const (hG _ (by simp [vsSizesT, vsConst]))
  have h85 : ς (.n 85) = ς (.n 72) := vsg_copy (hG _ (by simp [vsSizesT, vsCopy]))
  have e72 : ς (.n 72) = gen ^ logMem := by rw [vs_w hl (by decide), h72]
  have e78 : ς (.n 78) = gen := by rw [h78, vs_word_gen1]
  have e30 : word 1073741824 0 = gen ^ 30 := by
    rw [show (1073741824 : ℕ) = 2 ^ 30 from rfl, word_two_pow (by norm_num)]
  have e32 : word 4294967296 0 = gen ^ 32 := by
    rw [show (4294967296 : ℕ) = 2 ^ 32 from rfl, word_two_pow (by norm_num)]
  refine ⟨h65, ?_, ?_, e72, by rw [h73, e30], e78, ?_, by rw [h77, e32], by rw [h84, word_one],
    by rw [h85, e72], fun t ht ↦ ?_⟩
  · exact vs_rateSel hl hr h64
  · rw [h67, show (8 : ℕ) = 2 ^ 3 from rfl, word_two_pow (by norm_num)]
  · rw [h79, e72, e78]
    nth_rewrite 2 [← pow_one gen]
    rw [← pow_sub₀ _ gen_ne_zero hm]
  · rw [vsg_rdAt (hG _ (by
      rw [vsSizesT]
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩)))) (by interval_cases t <;> decide +kernel),
      vs_w hl (by decide)]

/-- **The stack's log's selector**: `g^(m - 20)` and its bound `g^10`. -/
theorem vs_placeV (hl : args.length = 6) {m : ℕ} (hm : 20 ≤ m) (h276 : w 276 = gen ^ m) :
    ς (.n 278) = gen ^ (m - 20) ∧ ς (.n 279) = gen ^ 10 := by
  have hG := vsPlaceT_good (rd := rd) (w := w) hl
  have h277 : ς (.n 277) = vsGinv20 := vsg_const (hG _ (by simp [vsPlaceT, vsConst]))
  have h278 : ς (.n 278) = ς (.n 276) * ς (.n 277) :=
    vsg_mul (by norm_num) (by norm_num) (hG _ (by simp [vsPlaceT, vsMul]))
  have h279 : ς (.n 279) = word 1024 0 := vsg_const (hG _ (by simp [vsPlaceT, vsConst]))
  refine ⟨?_, by rw [h279, show (1024 : ℕ) = 2 ^ 10 from rfl, word_two_pow (by norm_num)]⟩
  rw [h278, h277, vs_w hl (by decide), h276, show m = (m - 20) + 20 by omega, pow_add,
    Nat.add_sub_cancel, mul_assoc, mul_comm (gen ^ 20), vsGinv20_mul, mul_one]

/-- The pointer push block `b` reads through. -/
def vsPushP (b : ℕ) : ℕ := if b = 0 then 92 else 91 + 3 * b

/-- The value push block `b` reads. -/
def vsPushD (b : ℕ) : ℕ := if b = 0 then 93 else 92 + 3 * b

theorem vsPushStep_mul (b : ℕ) :
    vsMul (vsPushP b) 4 (84 + Tables.blockKappaSrc.getD b 0) ∈ vsPushStep b := by
  unfold vsPushStep vsPushP
  split <;> simp_all

theorem vsPushStep_ld (b : ℕ) :
    vsLd (vsPushD b) (vsPushP b) (Tables.blockKappaAdj b) ∈ vsPushStep b := by
  unfold vsPushStep vsPushP vsPushD
  split <;> simp_all

/-- **The push blocks' pointers**: `g_squares · kb[src]`. -/
theorem vs_pushP (hl : args.length = 6) {b : ℕ} (hb : b < 54) :
    ς (.n (vsPushP b)) = ς (.n 4) * ς (.n (84 + Tables.blockKappaSrc.getD b 0)) := by
  have hm : vsMul (vsPushP b) 4 (84 + Tables.blockKappaSrc.getD b 0) ∈ vsPushT := by
    rw [vsPushT]
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨b, List.mem_range.2 hb, vsPushStep_mul b⟩)
  have hsrc : Tables.blockKappaSrc.getD b 0 < 8 := blockKappaSrc_lt b (by show b < 153; omega)
  exact vsg_mul (by unfold vsPushP; split <;> omega) (by unfold vsPushP; split <;> omega)
    (vsPushT_good hl _ hm)

/-! ## The tail -/

/-- **The tail's values**: the stream's pointer past `verify_keccak`'s cursor,
`tabs`. -/
theorem vs_tailV (hl : args.length = 6) :
    ς (.n 1919) = w 595 * gen ∧ ς (.n 1921) = ς (.n 4) * gen ^ winTabAt := by
  have hG := vsTailP_good (rd := rd) (w := w) hl
  have hP : ∀ s ∈ [vsConst 1918 (word 2 0), vsMul 1919 595 1918], GoodS rd vsSL w ς s :=
    fun s hs ↦ hG s (by
      rw [vsTailP]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ hs)))))
  have c27 : ς (.n 1918) = word 2 0 := vsg_const (hP _ (by simp [vsMul, vsConst]))
  have m28 : ς (.n 1919) = ς (.n 595) * ς (.n 1918) :=
    vsg_mul (by norm_num) (by norm_num) (hP _ (by simp [vsMul, vsConst]))
  have h30 := vsg_tabs (c := 1920) (d := 1921) (by decide) fun s hs ↦ hG s (by
    rw [vsTailP]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ hs)))))
  exact ⟨by rw [m28, c27, vs_word_gen1, vs_w hl (by decide)], h30⟩

/-! ## `λ` and the target -/

/-- A read atom. -/
def vsIsLdB : Stmt → Bool
  | .atom (.load ..) => true
  | _ => false

/-- **A block of reads and atoms with automatic side conditions holds** from their equations and
the reads' words. -/
theorem vs_holdsList_goodLd {S : List Atom} {σ : Val} {C : CallRel} {blk : List Stmt}
    (hb : blk.all (fun s ↦ vsNoSideB s || vsIsLdB s) = true) (hg : ∀ s ∈ blk, GoodS rd S w σ s)
    (hld : ∀ d p off, Stmt.atom (.load d p off) ∈ blk →
      Atom.load d p off ∉ S ∧ ∃ v, LoadHolds rd (σ p) off v)
    {next : Prop} {kret : List E → Prop} (hn : next) : Stmt.HoldsList C rd σ blk next kret := by
  refine holdsList_straightN blk (List.all_eq_true.mpr fun s hs ↦ ?_) (fun s hs ↦ ?_) hn
  · have := List.all_eq_true.mp hb s hs
    cases s <;> simp_all [vsNoSideB, straightB, vsIsLdB]
  · have h1 := List.all_eq_true.mp hb s hs
    cases s with
    | atom a =>
      cases a with
      | load d p off =>
        obtain ⟨hS, v, hv⟩ := hld d p off hs
        show LoadHolds _ _ _ _
        rw [vsg_read (hg _ hs) hS hv]
        exact hv
      | _ => exact vsg_atom (hg _ hs) (by simpa [vsNoSideB, vsIsLdB] using h1)
    | _ => simp [vsNoSideB, vsIsLdB] at h1

theorem vsLamT_ok : vsLamT.all (fun s ↦ vsNoSideB s || vsIsLdB s) = true := by decide +kernel

theorem vsLamT_notS : ∀ i < 134,
    Atom.load (.n (1376 + 4 * i)) (.n (vsClaimAt (vsKept i)).1) (vsClaimAt (vsKept i)).2 ∉ vsSL := by
  decide +kernel

theorem vsLamT_loads {d p : V} {off : ℕ} (h : Stmt.atom (.load d p off) ∈ vsLamT) :
    (∃ i < 134, d = .n (1376 + 4 * i) ∧ p = .n (vsClaimAt (vsKept i)).1 ∧
      off = (vsClaimAt (vsKept i)).2) ∨ (d = .n 1915 ∧ p = .n 310 ∧ off = 0) := by
  simp only [vsLamT, vsSqzT, keccakA, challengeT, vsLamStep, vsLd, vsMul, vsAdd, List.mem_append,
    List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil, or_false,
    Stmt.atom.injEq, reduceCtorEq, false_or, Atom.load.injEq] at h
  rcases h with ⟨i, hi, h⟩ | h
  · exact Or.inl ⟨i, hi, h.1, h.2.1, h.2.2⟩
  · exact Or.inr h

/-- **`λ` and the target**: `λ` squeezed from the ring map's capacity, and the
target `dot (powers λ 137)` of `ring_switch_target`'s value, the claims kept (not an output
lane's), the Keccak reduction's word and the out-of-domain value. -/
theorem vs_lam (hl : args.length = 6) {claims : List ColumnClaim} (hcl : claims.length = 159)
    (hcol : claims.map (·.column) = Tables.claimColumns)
    (hpool : ReadsAt rd (w 6) ((claims.take 4).map (·.value)))
    (hcew : ReadsAt rd (w 582) (((claims.drop 4).take 153).map (·.value)))
    (hpi : ReadsAt rd (w 6 * gen ^ 157) ((claims.drop 157).map (·.value)))
    {v : E} (hv : ReadsAt rd (w 310) [v]) :
    (⟨[ς (.n 840), ς (.n 841), ς (.n 842), ς (.n 843), ς (.n 844)], []⟩ : Fs).squeeze =
        (ς (.n 1375), ⟨[ς (.n 1370), ς (.n 1371), ς (.n 1372), ς (.n 1373), ς (.n 1374)], []⟩) ∧
      ς (.n 1917) = dot (powers (ς (.n 1375)) 137)
        (w 1361 :: ((claims.filter (fun c ↦ c.column ∉ keccakOutputColumns)).map (·.value) ++
          [w 596, v])) := by
  have hz := vs_zero (rd := rd) (w := w) hl
  rw [← vs_w (rd := rd) (w := w) hl (a := 6) (by decide)] at hpool hpi
  rw [← vs_w (rd := rd) (w := w) hl (a := 582) (by decide)] at hcew
  rw [← vs_w (rd := rd) (w := w) hl (a := 310) (by decide)] at hv
  have hcl' := claim_load hcl hpool hcew hpi
  have hH : Stmt.HoldsList (fun _ _ _ ↦ True) rd ς vsLamT True (fun _ ↦ True) :=
    vs_holdsList_goodLd vsLamT_ok (vsLamT_good hl) (fun d p off hm ↦ by
      rcases vsLamT_loads hm with ⟨i, hi, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact ⟨vsLamT_notS i hi, _, hcl' (vsKept i) (by simp only [vsKept]; split <;> omega)⟩
      · exact ⟨by decide +kernel, _, hv 0 (by simp)⟩) trivial
  obtain ⟨hsq, ht, -⟩ := vsLamT_holds hz.1 hz.2.1 hz.2.2.1 hz.2.2.2 hcl hcol hpool hcew hpi hv hH
  refine ⟨hsq, ?_⟩
  rw [ht, vs_w (rd := rd) (w := w) hl (a := 1361) (by decide), vs_w (rd := rd) (w := w) hl (a := 596) (by decide)]

end
end LeanVM.Guest.B1.VerifySub
