/-
  LeanVM.Guest.B1.Gkr.VbgC

  `verify_bus_gkr`'s body, completely: on a memory holding the tables, the root-most step's and
  the layers' words, the last slot and the values' buffer, its honest valuation satisfies the
  body and returns the last slot's capacity, cursor and the values' buffer.
-/

module

public import LeanVM.Guest.B1.Gkr.VbgOdd
public import LeanVM.Guest.B1.Gkr.Loop8Complete
public import LeanVM.Guest.B1.Selectors.LayoutBasic
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr`'s body, completely (G:1867-2048)

`vbg_body_of`: the body evaluated forward (`vbgEvL`, the allocations answered by the buffers'
pointers, `vbgW`), its regions `vbR1 .. vbR9`: the range check of `g^depth` (the memory defined
at `g^depth` and `g^(32 - depth)`), the two roots read, the count asserted nonzero and the
combiner, the table `k_mod_next`, the tables `loop_bounds` and `depth_odd`, the depth's parity,
the root-most layer (`rtc_two` at an odd depth, `rtc_four` at an even one), the layer loop
(`ly_complete`), the last slot, the point's copy (`l8_complete`) and the values' buffer.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The regions of the body -/

/-- The depth's powers, the allocations, the range check, the capacity's copies. -/
def vbR1 : List Stmt :=
  [.atom (.const (.n 9) (word 4 0)), .atom (.mul (.n 10) (.n 6) (.n 9)),
    .atom (.mul (.n 11) (.n 10) (.n 10)), .atom (.mul (.n 12) (.n 11) (.n 10)),
    .atom (.mul (.n 13) (.n 12) (.n 12)), .atom (.mul (.n 14) (.n 13) (.n 13)),
    .atom (.mul (.n 15) (.n 14) (.n 10)), .atom (.hint (.allocDyn (.n 16) (.n 15))),
    .atom (.hint (.alloc (.n 17) 6034)), .atom (.hint (.alloc (.n 18) 1640)),
    .atom (.const (.n 19) (word 4294967296 0)),
    .atom (.rangeCheck (.n 6) (.n 20) (.n 21) (.n 22) (.n 19))] ++
  (List.range 5).map (fun k ↦ .atom (.copy (.n (23 + k)) (.n k)))

/-- The two roots. -/
def vbR2 : List Stmt :=
  fsNextT (.n 5) 0 28 ++ [.atom (.copy (.n 31) (.n 28)), .atom (.copy (.n 32) (.n 28))] ++
  fsNextT (.n 5) 1 33 ++ [.atom (.copy (.n 36) (.n 33))]

/-- The count asserted nonzero, the combiner, the claim, `k_mod_next`'s allocation. -/
def vbR3 : List Stmt :=
  [.atom (.const (.n 37) (word 0 0)), .atom (.add (.n 38) (.n 33) (.n 37)),
    .atom (.hint (.inverse (.n 38) (.n 39))), .atom (.assertNe (.n 38) (.n 39) (.n 40)),
    .atom (.const (.n 41) (word 1 0)), .atom (.const (.n 42) (word 0 0)),
    .atom (.const (.n 43) (word 0 0)), .atom (.const (.n 44) (word 0 0)),
    .atom (.const (.n 45) (word 0 0)),
    keccakA ([.n 29, .n 30, .n 34, .n 35, .n 42, .n 43, .n 44, .n 45] ++
      (List.range 5).map fun k ↦ .n (23 + k)) (lyOuts 46)] ++
  challengeT (.n 46) 59 ++
  [.atom (.mul (.n 60) (.n 59) (.n 36)), .atom (.add (.n 61) (.n 32) (.n 60)),
    .atom (.mul (.n 62) (.n 59) (.n 61)), .atom (.add (.n 63) (.n 31) (.n 62)),
    .atom (.hint (.alloc (.n 64) 8))]

/-- The table `k_mod_next` at `g^r` and `g^(4 + r)` (G:1912-1915). -/
def vbKmn (r : ℕ) : List Stmt :=
  [.atom (.const (.n (65 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0)),
    .atom (.load (.n (65 + 2 * r)) (.n 64) r),
    .atom (.const (.n (66 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0)),
    .atom (.load (.n (66 + 2 * r)) (.n 64) (4 + r))]

/-- The table `k_mod_next`, the tables' allocations. -/
def vbR4 : List Stmt :=
  ((List.range 4).map vbKmn).flatten ++
    [.atom (.hint (.alloc (.n 73) 33)), .atom (.hint (.alloc (.n 74) 33))]

/-- The tables `loop_bounds[d] = g^((d - 1)/2)`, `depth_odd[d] = g^(d % 2)`. -/
def vbTab (d : ℕ) : List Stmt :=
  [.atom (.const (.n (75 + 2 * d)) (word (2 ^ ((d - 1) / 2)) 0)),
    .atom (.load (.n (75 + 2 * d)) (.n 73) d),
    .atom (.const (.n (76 + 2 * d)) (word (2 ^ (d % 2)) 0)),
    .atom (.load (.n (76 + 2 * d)) (.n 74) d)]

/-- The tables. -/
def vbR5 : List Stmt := ((List.range 33).map vbTab).flatten

/-- The depth's parity. -/
def vbR6 : List Stmt :=
  [.atom (.mul (.n 141) (.n 74) (.n 6)), .atom (.load (.n 142) (.n 141) 0),
    .atom (.const (.n 143) (word 1 0)), .atom (.add (.n 144) (.n 142) (.n 143))]

/-- The root-most layer. -/
noncomputable def vbR7 : List Stmt := [.ite (.n 144) rtFour rtTwo]

/-- The layer loop. -/
def vbR8 : List Stmt :=
  [.atom (.const (.n 374) (word 4 0)), .atom (.mul (.n 374) (.n 375) (.n 142)),
    .atom (.const (.n 376) (word 1 0)), .atom (.mul (.n 377) (.n 73) (.n 6)),
    .atom (.load (.n 378) (.n 377) 0), .atom (.add (.n 379) (.n 376) (.n 378)),
    .atom (.const (.n 380) (word 1 0)), .atom (.mul (.n 381) (.n 73) (.n 6)),
    .atom (.load (.n 382) (.n 381) 0),
    .callIf (.n 379) name% «verify_bus_gkr_loop0» [.n 380, .n 382, .n 375, .n 16, .n 8, .n 17,
        .n 63, .n 142, .n 6,
      .n 64]]

/-- The last slot, the point's copy, the values' buffer, the returns. -/
def vbR9 : List Stmt :=
  [.atom (.mul (.n 383) (.n 6) (.n 6)), .atom (.mul (.n 384) (.n 383) (.n 6)),
    .atom (.mul (.n 385) (.n 384) (.n 384)), .atom (.mul (.n 386) (.n 385) (.n 385)),
    .atom (.mul (.n 387) (.n 386) (.n 6)), .atom (.mul (.n 388) (.n 16) (.n 387)),
    .atom (.load (.n 389) (.n 388) 5), .atom (.load (.n 390) (.n 388) 9),
    .atom (.const (.n 391) (word 1 0)), .atom (.add (.n 392) (.n 391) (.n 6)),
    .atom (.const (.n 393) (word 1 0)),
    .callIf (.n 392) name% «verify_bus_gkr_loop1» [.n 393, .n 6, .n 7, .n 390],
    .atom (.hint (.alloc (.n 394) 3)),
    .atom (.load (.n 395) (.n 388) 6), .atom (.load (.n 395) (.n 394) 0),
    .atom (.load (.n 396) (.n 388) 7), .atom (.load (.n 396) (.n 394) 1),
    .atom (.load (.n 397) (.n 388) 8), .atom (.load (.n 397) (.n 394) 2)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (398 + k)) (.n 388) k)) ++
  [.atom (.copy (.n 403) (.n 389)), .atom (.copy (.n 404) (.n 394))]

set_option maxRecDepth 10000 in
theorem vbgPre_eq' :
    vbgPre = vbR1 ++ vbR2 ++ vbR3 ++ vbR4 ++ vbR5 ++ vbR6 ++ vbR7 ++ vbR8 ++ vbR9 :=
  tbStmtsEqb_sound (by decide +kernel)

theorem tb_word_four : word 4 0 = gen ^ 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)]

theorem tb_list5_eq {l : List E} (h : l.length = 5) :
    ∃ a0 a1 a2 a3 a4, l = [a0, a1, a2, a3, a4] := by
  match l, h with
  | [a0, a1, a2, a3, a4], _ => exact ⟨a0, a1, a2, a3, a4, rfl⟩

theorem tb_list3_eq {l : List E} (h : l.length = 3) : ∃ a0 a1 a2, l = [a0, a1, a2] := by
  match l, h with
  | [a0, a1, a2], _ => exact ⟨a0, a1, a2, rfl⟩

/-- The allocations' pointers: the layers, the rounds' records, the rows, `k_mod_next`,
`loop_bounds`, `depth_odd`, the values' buffer. -/
def vbgW (layers rounds rows kmn bnd odd vals : E) : ℕ → E := fun i ↦
  if i = 16 then layers else if i = 17 then rounds else if i = 18 then rows else
    if i = 64 then kmn else if i = 73 then bnd else if i = 74 then odd else vals

/-- The root's sponge: the carried capacity, the two roots waiting. -/
def rootS (cap0 : List E) (x0 x1 : E) : Fs := ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩

/-- The root's state: the values `[root, root, count]`, no point. -/
def rootSt (x0 x1 : E) : GkrState := ⟨[x0, x0, x1], []⟩

section Body

variable {rd : Reader} {w : ℕ → E} {σ : Val}

/-- A block of the body without an `ite` or an `assertNe` satisfies its equations. -/
theorem vb_goodB (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((vbgPre.drop n).take blk.length) = true)
    (hne : blk.all noNeB = true) (hni : blk.all notIteB = true) :
    ∀ s ∈ blk, GoodS rd vbgS w σ s := by
  intro s hs
  have h := good_slice (G := fun s => GoodS rd vbgS w σ (fixNe s))
    (fun s hs => hG _ (List.mem_map_of_mem hs)) n blk heq hni s hs
  rwa [fixNe_of_noNe (List.all_eq_true.mp hne s hs)] at h

/-- A statement of the body satisfies the equations of its evaluation. -/
theorem vb_goodS (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS w σ s) (n : ℕ) (s : Stmt)
    (heq : tbStmtsEqb [s] ((vbgPre.drop n).take 1) = true) (hni : notIteB s = true) :
    GoodS rd vbgS w σ (fixNe s) :=
  good_slice (G := fun s => GoodS rd vbgS w σ (fixNe s))
    (fun s hs => hG _ (List.mem_map_of_mem hs)) n [s] heq (by simp [hni]) s List.mem_cons_self

/-- **`verify_bus_gkr`'s body, completely**, on its honest valuation, at `1 ≤ depth ≤ 32`: the
range check's words defined, the two roots at the cursor (the count nonzero), the tables, the
root-most step's words and the slot it leads to, every layer's words (`LyIter`), the last slot
with its point at `zeta` and its values in the values' buffer give the relation, returning the
last slot's capacity, cursor and the buffer. -/
theorem vbg_body_of {depth : ℕ} (hd1 : 1 ≤ depth) (hd : depth ≤ 32) {cap0 : List E}
    (hcl : cap0.length = 5) {cur zeta tabs layers rounds rows kmn bnd odd vals : E}
    (hrc : (rd (addressOfIndex depth)).isSome = true ∧ (rd (addressOfIndex (32 - depth))).isSome
        = true)
    {x0 x1 : E} (hx0 : LoadHolds rd cur 0 x0) (hx1 : LoadHolds rd cur 1 x1) (hcnt : x1 ≠ 0)
    (hkmn : KModNext rd kmn)
    (hbnd : TbReadsAt rd bnd ((List.range 33).map fun k ↦ gen ^ ((k - 1) / 2)))
    (hodt : TbReadsAt rd odd ((List.range 33).map fun k ↦ gen ^ (k % 2)))
    (hodd : depth % 2 = 1 → ∃ D : GkStepD, D.Ok (rootS cap0 x0 x1) (rootSt x0 x1) 1 ∧
      TbReadsAt rd (cur * gen ^ 2) D.xs ∧
      GkSlot rd layers 1 (D.s' (rootS cap0 x0 x1) (rootSt x0 x1) 1)
        (cur * gen ^ 2 * gen ^ D.xs.length) (D.st' (rootS cap0 x0 x1) (rootSt x0 x1) 1)
        (rows * gen ^ 40) gen 1 1)
    (heven : depth % 2 = 0 → ∃ D : GkStepD, D.Ok (rootS cap0 x0 x1) (rootSt x0 x1) 2 ∧
      TbReadsAt rd (cur * gen ^ 2) D.xs ∧
      GkSlot rd layers 2 (D.s' (rootS cap0 x0 x1) (rootSt x0 x1) 2)
        (cur * gen ^ 2 * gen ^ D.xs.length) (D.st' (rootS cap0 x0 x1) (rootSt x0 x1) 2)
        (rows * gen ^ 40) gen 1 gen)
    (hit : ∀ j < (depth - 1) / 2, LyIter rd layers rounds (depth % 2) j)
    {sF : Fs} {curF : E} {stF : GkrState} {rowF posF halfF parF : E}
    (hlast : GkSlot rd layers depth sF curF stF rowF posF halfF parF)
    (hz : TbReadsAt rd zeta stF.point) (hv : TbReadsAt rd vals stF.values) :
    Stmt.HoldsList (coreProgram.Rel rd) rd
        (B1.Val.ofArgs (ev rd (vbgW layers rounds rows kmn bnd odd vals)
          (cap0 ++ [cur, gen ^ depth, zeta, tabs]) vbgEvL)) vbgPre True
        (fun rs => rs = sF.cap ++ [curF, vals]) ∧
      vbgRets.map (B1.Val.ofArgs (ev rd (vbgW layers rounds rows kmn bnd odd vals)
        (cap0 ++ [cur, gen ^ depth, zeta, tabs]) vbgEvL)) = sF.cap ++ [curF, vals] := by
  obtain ⟨a0, a1, a2, a3, a4, rfl⟩ := tb_list5_eq hcl
  simp only [List.cons_append, List.nil_append]
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  set args : List E := [a0, a1, a2, a3, a4, cur, gen ^ depth, zeta, tabs] with hargs
  have hc9 : chk args.length vbgEvL = some c' := hc'
  set W : ℕ → E := vbgW layers rounds rows kmn bnd odd vals with hW
  set σ : Val := B1.Val.ofArgs (ev rd W args vbgEvL) with hσ
  have hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s := (ev_spec rd W vbgEvL args hc9).2.2
  have par : ∀ i < 9, σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd W hc9 (by simpa [hargs] using hi)
  have e0 : σ (.n 0) = a0 := par 0 (by omega)
  have e1 : σ (.n 1) = a1 := par 1 (by omega)
  have e2 : σ (.n 2) = a2 := par 2 (by omega)
  have e3 : σ (.n 3) = a3 := par 3 (by omega)
  have e4 : σ (.n 4) = a4 := par 4 (by omega)
  have e5 : σ (.n 5) = cur := par 5 (by omega)
  have e6 : σ (.n 6) = gen ^ depth := par 6 (by omega)
  have e7 : σ (.n 7) = zeta := par 7 (by omega)
  have e8 : σ (.n 8) = tabs := par 8 (by omega)
  have g : ∀ n (a : Atom), tbStmtsEqb [.atom a] ((vbgPre.drop n).take 1) = true →
      fixNe (.atom a) = .atom a → Good rd vbgS W σ a :=
    fun n a heq hf => vb_good (rd := rd) (w := W) (σ := σ) hG n a heq hf
  set sh := depth % 2 with hsh
  set m := (depth - 1) / 2 with hm
  -- the depth's powers, the allocations, the range check
  have c9 : σ (.n 9) = word 4 0 := g 0 (.const (.n 9) (word 4 0)) (by decide +kernel) rfl
  have m10 := good_mul (g 1 (.mul (.n 10) (.n 6) (.n 9)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m11 := good_mul (g 2 (.mul (.n 11) (.n 10) (.n 10)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m12 := good_mul (g 3 (.mul (.n 12) (.n 11) (.n 10)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m13 := good_mul (g 4 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m14 := good_mul (g 5 (.mul (.n 14) (.n 13) (.n 13)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m15 := good_mul (g 6 (.mul (.n 15) (.n 14) (.n 10)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have e16 : σ (.n 16) = layers := by
    have h : σ (.n 16) = W 16 := g 7 (.hint (.allocDyn (.n 16) (.n 15))) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e17 : σ (.n 17) = rounds := by
    have h : σ (.n 17) = W 17 := g 8 (.hint (.alloc (.n 17) 6034)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e18 : σ (.n 18) = rows := by
    have h : σ (.n 18) = W 18 := g 9 (.hint (.alloc (.n 18) 1640)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have c19 : σ (.n 19) = word 4294967296 0 :=
    g 10 (.const (.n 19) (word 4294967296 0)) (by decide +kernel) rfl
  have w32 : word 4294967296 0 = gen ^ 32 := by
    rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num)]
  have grc := g 11 (.rangeCheck (.n 6) (.n 20) (.n 21) (.n 22) (.n 19)) (by decide +kernel) rfl
  have h1920 : (V.n 19).idx < (V.n 20).idx := show 19 < 20 by norm_num
  have e20 : σ (.n 20) = gen ^ (32 - depth) := by
    have h3 : σ (.n 20) = σ (.n 19) * (σ (.n 6))⁻¹ := by
      have := grc.2.2
      simpa only [h1920, ↓reduceIte] using this
    have hp32 : gen ^ 32 = gen ^ (32 - depth) * gen ^ depth := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    rw [h3, c19, w32, e6, hp32, mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero _), mul_one]
  have hrcH : (Atom.rangeCheck (.n 6) (.n 20) (.n 21) (.n 22) (.n 19)).Holds rd σ := by
    refine holds_of_good grc ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e6]; exact tb_gen_pow_isInK _
    · rw [e6, gen_pow_eq_ofK, tb_addr_ofK, Nat.add_zero]
      exact hrc.1
    · rw [e20]; exact tb_gen_pow_isInK _
    · rw [e20, gen_pow_eq_ofK, tb_addr_ofK, Nat.add_zero]
      exact hrc.2
    · show (if (V.n 19).idx < (V.n 20).idx then σ (.n 6) ≠ 0 else True)
      simp only [h1920, ↓reduceIte]
      rw [e6]; exact gen_pow_ne_zero _
  have gq := vb_goodB hG 12 ((List.range 5).map fun k ↦ Stmt.atom (.copy (.n (23 + k)) (.n k)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have q23 : ∀ k < 5, σ (.n (23 + k)) = σ (.n k) := fun k hk =>
    gq _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  have q23a : σ (.n 23) = a0 :=
    (gq _ (List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩)).trans e0
  have q24a : σ (.n 24) = a1 :=
    (gq _ (List.mem_map.mpr ⟨1, List.mem_range.mpr (by omega), rfl⟩)).trans e1
  have q25a : σ (.n 25) = a2 :=
    (gq _ (List.mem_map.mpr ⟨2, List.mem_range.mpr (by omega), rfl⟩)).trans e2
  have q26a : σ (.n 26) = a3 :=
    (gq _ (List.mem_map.mpr ⟨3, List.mem_range.mpr (by omega), rfl⟩)).trans e3
  have q27a : σ (.n 27) = a4 :=
    (gq _ (List.mem_map.mpr ⟨4, List.mem_range.mpr (by omega), rfl⟩)).trans e4
  -- the two roots
  obtain ⟨e28, -, hfs28⟩ := fsNextT_good (C := coreProgram.Rel rd) (kret := fun _ => True)
    (vb_goodB hG 17 (fsNextT (.n 5) 0 28) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (by decide +kernel) (by rw [e5]; exact hx0)
  obtain ⟨e33, -, hfs33⟩ := fsNextT_good (C := coreProgram.Rel rd) (kret := fun _ => True)
    (vb_goodB hG 22 (fsNextT (.n 5) 1 33) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (by decide +kernel) (by rw [e5]; exact hx1)
  obtain ⟨⟨l28, p28⟩, -⟩ := (holds_fsNextT _ _ _ _ _).mp hfs28
  obtain ⟨⟨l33, p33⟩, -⟩ := (holds_fsNextT _ _ _ _ _).mp hfs33
  have q31 : σ (.n 31) = σ (.n 28) := g 20 (.copy (.n 31) (.n 28)) (by decide +kernel) rfl
  have q32 : σ (.n 32) = σ (.n 28) := g 21 (.copy (.n 32) (.n 28)) (by decide +kernel) rfl
  have q36 : σ (.n 36) = σ (.n 33) := g 25 (.copy (.n 36) (.n 33)) (by decide +kernel) rfl
  -- the count asserted nonzero
  have c37 : σ (.n 37) = word 0 0 := g 26 (.const (.n 37) (word 0 0)) (by decide +kernel) rfl
  have a38 : σ (.n 38) = σ (.n 33) + σ (.n 37) :=
    g 27 (.add (.n 38) (.n 33) (.n 37)) (by decide +kernel) rfl
  have i39 : σ (.n 39) = (σ (.n 38))⁻¹ :=
    g 28 (.hint (.inverse (.n 38) (.n 39))) (by decide +kernel) rfl
  have m40 : σ (.n 40) = σ (.n 38) * σ (.n 39) :=
    good_mulS (vb_goodS hG 29 (.atom (.assertNe (.n 38) (.n 39) (.n 40))) (by decide +kernel) rfl)
      (by omega) (by omega)
  have e38 : σ (.n 38) = x1 := by rw [a38, c37, tb_word_zero, add_zero, e33]
  -- the combiner and the claim
  have c41 : σ (.n 41) = word 1 0 := g 30 (.const (.n 41) (word 1 0)) (by decide +kernel) rfl
  have c42 : σ (.n 42) = word 0 0 := g 31 (.const (.n 42) (word 0 0)) (by decide +kernel) rfl
  have c43 : σ (.n 43) = word 0 0 := g 32 (.const (.n 43) (word 0 0)) (by decide +kernel) rfl
  have c44 : σ (.n 44) = word 0 0 := g 33 (.const (.n 44) (word 0 0)) (by decide +kernel) rfl
  have c45 : σ (.n 45) = word 0 0 := g 34 (.const (.n 45) (word 0 0)) (by decide +kernel) rfl
  have z42 : σ (.n 42) = 0 := by rw [c42, tb_word_zero]
  have z43 : σ (.n 43) = 0 := by rw [c43, tb_word_zero]
  have z44 : σ (.n 44) = 0 := by rw [c44, tb_word_zero]
  have z45 : σ (.n 45) = 0 := by rw [c45, tb_word_zero]
  have hins : (([.n 29, .n 30, .n 34, .n 35, .n 42, .n 43, .n 44, .n 45] ++
      (List.range 5).map fun k ↦ V.n (23 + k)) : List V).map σ =
      rateOf (rootS [a0, a1, a2, a3, a4] x0 x1).pend ++ (rootS [a0, a1, a2, a3, a4] x0 x1).cap := by
    have hcapE : ((List.range 5).map fun k ↦ V.n (23 + k)).map σ = [a0, a1, a2, a3, a4] := by
      show [σ (.n 23), σ (.n 24), σ (.n 25), σ (.n 26), σ (.n 27)] = [a0, a1, a2, a3, a4]
      rw [q23a, q24a, q25a, q26a, q27a]
    obtain ⟨e29, e30⟩ := Prod.ext_iff.mp (fsPackT_cells p28)
    obtain ⟨e34, e35⟩ := Prod.ext_iff.mp (fsPackT_cells p33)
    rw [List.map_append, hcapE, rateOf_eq_cells _ (by simp [rootS])]
    norm_num at e29 e30 e34 e35
    simp [rootS, pendCells, e29, e30, e34, e35, e28, e33, z42, z43, z44, z45]
  obtain ⟨k35, hP, hcap⟩ := lyc_keccak (rd := rd) (σ := σ) (S := vbgS) (w := W)
    (g 35 (.keccak ([.n 29, .n 30, .n 34, .n 35, .n 42, .n 43, .n 44, .n 45] ++
      (List.range 5).map fun k ↦ .n (23 + k)) (lyOuts 46) false false) (by decide +kernel) rfl)
  rw [hins] at hP hcap
  have hco := challengeT_good (vb_goodB hG 36 (challengeT (.n 46) 59) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  have e59 : σ (.n 59) = (rootS [a0, a1, a2, a3, a4] x0 x1).squeeze.1 :=
    challengeT_value hco (hP 0 (by omega))
  have m60 := good_mul (g 37 (.mul (.n 60) (.n 59) (.n 36)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have a61 : σ (.n 61) = σ (.n 32) + σ (.n 60) :=
    g 38 (.add (.n 61) (.n 32) (.n 60)) (by decide +kernel) rfl
  have m62 := good_mul (g 39 (.mul (.n 62) (.n 59) (.n 61)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have a63 : σ (.n 63) = σ (.n 31) + σ (.n 62) :=
    g 40 (.add (.n 63) (.n 31) (.n 62)) (by decide +kernel) rfl
  have e63 : σ (.n 63) = polyEval (rootSt x0 x1).values (rootS [a0, a1, a2, a3, a4] x0 x1).squeeze.1 := by
    rw [a63, m62, a61, m60, q31, q32, q36, e28, e33, ← e59]
    simp only [rootSt, polyEval, List.foldr]
    ring
  have hcapP : (lyCap 46).map σ = capOf (rootS [a0, a1, a2, a3, a4] x0 x1).perm := hcap
  have e64 : σ (.n 64) = kmn := by
    have h : σ (.n 64) = W 64 := g 41 (.hint (.alloc (.n 64) 8)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e73 : σ (.n 73) = bnd := by
    have h : σ (.n 73) = W 73 := g 58 (.hint (.alloc (.n 73) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e74 : σ (.n 74) = odd := by
    have h : σ (.n 74) = W 74 := g 59 (.hint (.alloc (.n 74) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  -- the tables
  have gK := vb_goodB hG 42 ((List.range 4).map vbKmn).flatten (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have KM : ∀ r < 4, ∀ s ∈ vbKmn r, SHolds (coreProgram.Rel rd) rd σ s := by
    intro r hr
    have mem : ∀ t ∈ vbKmn r, t ∈ ((List.range 4).map vbKmn).flatten := fun t ht =>
      List.mem_flatten.mpr ⟨vbKmn r, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩, ht⟩
    have c0 : σ (.n (65 + 2 * r)) = word (2 ^ ((r + 1) % 4)) 0 :=
      gK (.atom (.const (.n (65 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0))) (mem _ (by simp [vbKmn]))
    have c1 : σ (.n (66 + 2 * r)) = word (2 ^ ((r + 1) / 4)) 0 :=
      gK (.atom (.const (.n (66 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0))) (mem _ (by simp [vbKmn]))
    obtain ⟨k4, k0⟩ := hkmn r hr
    simp only [vbKmn, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    exact ⟨c0, show LoadHolds rd (σ (.n 64)) r (σ (.n (65 + 2 * r))) by
        rw [e64, c0, tb_word_two_pow (by omega)]; exact k0, c1,
      show LoadHolds rd (σ (.n 64)) (4 + r) (σ (.n (66 + 2 * r))) by
        rw [e64, c1, tb_word_two_pow (by omega)]; exact k4⟩
  have gT := vb_goodB hG 60 vbR5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hbk : ∀ k < 33, LoadHolds rd bnd k (gen ^ ((k - 1) / 2)) := fun k hk => by
    have := hbnd k (by simpa using hk)
    simpa using this
  have hok : ∀ k < 33, LoadHolds rd odd k (gen ^ (k % 2)) := fun k hk => by
    have := hodt k (by simpa using hk)
    simpa using this
  have TB : ∀ k < 33, ∀ s ∈ vbTab k, SHolds (coreProgram.Rel rd) rd σ s := by
    intro k hk
    have mem : ∀ t ∈ vbTab k, t ∈ vbR5 := fun t ht =>
      List.mem_flatten.mpr ⟨vbTab k, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ht⟩
    have c0 : σ (.n (75 + 2 * k)) = word (2 ^ ((k - 1) / 2)) 0 :=
      gT (.atom (.const (.n (75 + 2 * k)) (word (2 ^ ((k - 1) / 2)) 0))) (mem _ (by simp [vbTab]))
    have c1 : σ (.n (76 + 2 * k)) = word (2 ^ (k % 2)) 0 :=
      gT (.atom (.const (.n (76 + 2 * k)) (word (2 ^ (k % 2)) 0))) (mem _ (by simp [vbTab]))
    simp only [vbTab, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    exact ⟨c0, show LoadHolds rd (σ (.n 73)) k (σ (.n (75 + 2 * k))) by
        rw [e73, c0, tb_word_two_pow (by omega)]; exact hbk k hk, c1,
      show LoadHolds rd (σ (.n 74)) k (σ (.n (76 + 2 * k))) by
        rw [e74, c1, tb_word_two_pow (by omega)]; exact hok k hk⟩
  -- the depth's parity
  have m141 := good_mul (g 192 (.mul (.n 141) (.n 74) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  obtain ⟨e142, l142⟩ := good_read (g 193 (.load (.n 142) (.n 141) 0) (by decide +kernel) rfl)
    (by decide +kernel) (show LoadHolds rd (σ (.n 141)) 0 (gen ^ sh) by
      rw [m141, e74, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hok depth (by omega))
  have c143 : σ (.n 143) = word 1 0 := g 194 (.const (.n 143) (word 1 0)) (by decide +kernel) rfl
  have a144 : σ (.n 144) = σ (.n 142) + σ (.n 143) :=
    g 195 (.add (.n 144) (.n 142) (.n 143)) (by decide +kernel) rfl
  -- the root-most layer
  have R7 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR7 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    simp only [vbR7, Stmt.HoldsList]
    rw [tb_holds_ite_noRet _ _ _ rtFour_noRet rtTwo_noRet]
    refine ⟨⟨?_, fun h0 => ?_, fun hne => ?_⟩, trivial⟩
    · rw [a144, e142, c143, tb_word_one]
      exact tb_isInK_add (tb_gen_pow_isInK _) tb_isInK_one
    · have hsh0 : sh = 0 := by
        by_contra h
        rw [a144, e142, c143, tb_word_one, show sh = 1 by omega] at h0
        have := gen_pow_inj (a := 1) (b := 0) (by omega) (by omega)
          ((e_add_eq_zero_iff.mp h0).trans (pow_zero gen).symm)
        omega
      obtain ⟨D, hD, hxD, hS'⟩ := heven hsh0
      exact rtc_four hG rfl e59 e63 hcapP z42 z43 z44 z45 hD (by rw [e5]; exact hxD)
        (by rw [e16, e5, e18]; exact hS')
    · have hsh1 : sh = 1 := by
        by_contra h
        rw [a144, e142, c143, tb_word_one, show sh = 0 by omega, pow_zero, e_add_self] at hne
        exact hne rfl
      obtain ⟨D, hD, hxD, hS'⟩ := hodd hsh1
      exact rtc_two hG rfl e59 e63 hcapP z42 z43 z44 z45 hD (by rw [e5]; exact hxD)
        (by rw [e16, e5, e18]; exact hS')
  -- the layer loop
  have c374 : σ (.n 374) = word 4 0 := g 197 (.const (.n 374) (word 4 0)) (by decide +kernel) rfl
  have d375 : σ (.n 375) = σ (.n 374) * (σ (.n 142))⁻¹ := by
    have h := g 198 (.mul (.n 374) (.n 375) (.n 142)) (by decide +kernel) rfl
    have hn : ¬ ((V.n 375).idx < (V.n 374).idx ∧ (V.n 142).idx < (V.n 374).idx) := by
      show ¬ (375 < 374 ∧ 142 < 374); omega
    simpa only [Good, hn, ↓reduceIte] using h
  have e375 : σ (.n 375) = gen ^ (2 - sh) := by
    rw [d375, c374, tb_word_four, e142]
    have hs : sh ≤ 2 := by omega
    rw [show (gen : E) ^ 2 = gen ^ (2 - sh) * gen ^ sh by rw [← pow_add, Nat.sub_add_cancel hs],
      mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero _), mul_one]
  have c376 : σ (.n 376) = word 1 0 := g 199 (.const (.n 376) (word 1 0)) (by decide +kernel) rfl
  have m377 := good_mul (g 200 (.mul (.n 377) (.n 73) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have hbb : ∀ p, p = σ (.n 73) * σ (.n 6) → LoadHolds rd p 0 (gen ^ m) := fun p hp => by
    rw [hp, e73, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hbk depth (by omega)
  obtain ⟨e378, l378⟩ := good_read (g 201 (.load (.n 378) (.n 377) 0) (by decide +kernel) rfl)
    (by decide +kernel) (hbb _ m377)
  have a379 : σ (.n 379) = σ (.n 376) + σ (.n 378) :=
    g 202 (.add (.n 379) (.n 376) (.n 378)) (by decide +kernel) rfl
  have c380 : σ (.n 380) = word 1 0 := g 203 (.const (.n 380) (word 1 0)) (by decide +kernel) rfl
  have m381 := good_mul (g 204 (.mul (.n 381) (.n 73) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  obtain ⟨e382, l382⟩ := good_read (g 205 (.load (.n 382) (.n 381) 0) (by decide +kernel) rfl)
    (by decide +kernel) (hbb _ m381)
  -- the last slot, the point's copy, the values' buffer
  obtain ⟨hclF, hcapF, -, hcurF, hvlF, hvalF, hrowF, hplF, hptF, -, -, -⟩ := hlast
  have m383 := good_mul (g 207 (.mul (.n 383) (.n 6) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m384 := good_mul (g 208 (.mul (.n 384) (.n 383) (.n 6)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m385 := good_mul (g 209 (.mul (.n 385) (.n 384) (.n 384)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m386 := good_mul (g 210 (.mul (.n 386) (.n 385) (.n 385)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m387 := good_mul (g 211 (.mul (.n 387) (.n 386) (.n 6)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m388 := good_mul (g 212 (.mul (.n 388) (.n 16) (.n 387)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e388 : σ (.n 388) = layers * gen ^ (13 * depth) := by
    rw [m388, m387, m386, m385, m384, m383, e6, e16, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    ring_nf
  have ld : ∀ k v, LoadHolds rd layers (13 * depth + k) v → LoadHolds rd (σ (.n 388)) k v :=
    fun k v h => by rw [e388, tb_loadHolds_mul_gen_pow]; exact h
  obtain ⟨e389, l389⟩ := good_read (g 213 (.load (.n 389) (.n 388) 5) (by decide +kernel) rfl)
    (by decide +kernel) (ld 5 _ hcurF)
  obtain ⟨e390, l390⟩ := good_read (g 214 (.load (.n 390) (.n 388) 9) (by decide +kernel) rfl)
    (by decide +kernel) (ld 9 _ hrowF)
  have c391 : σ (.n 391) = word 1 0 := g 215 (.const (.n 391) (word 1 0)) (by decide +kernel) rfl
  have a392 : σ (.n 392) = σ (.n 391) + σ (.n 6) :=
    g 216 (.add (.n 392) (.n 391) (.n 6)) (by decide +kernel) rfl
  have c393 : σ (.n 393) = word 1 0 := g 217 (.const (.n 393) (word 1 0)) (by decide +kernel) rfl
  have e394 : σ (.n 394) = vals := by
    have h : σ (.n 394) = W 394 := g 219 (.hint (.alloc (.n 394) 3)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  obtain ⟨v0, v1, v2, hv3⟩ := tb_list3_eq hvlF
  have hvk : ∀ k < 3, LoadHolds rd vals k (stF.values.getD k 0) := fun k hk => by
    have := hv k (by rw [hvlF]; exact hk)
    rwa [← List.getD_eq_getElem _ 0] at this
  obtain ⟨e395, l395⟩ := good_read (g 220 (.load (.n 395) (.n 388) 6) (by decide +kernel) rfl)
    (by decide +kernel) (ld 6 _ (hvalF 0 (by omega)))
  obtain ⟨e396, l396⟩ := good_read (g 222 (.load (.n 396) (.n 388) 7) (by decide +kernel) rfl)
    (by decide +kernel) (ld 7 _ (hvalF 1 (by omega)))
  obtain ⟨e397, l397⟩ := good_read (g 224 (.load (.n 397) (.n 388) 8) (by decide +kernel) rfl)
    (by decide +kernel) (ld 8 _ (hvalF 2 (by omega)))
  have gC := vb_goodB hG 226 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (398 + k)) (.n 388) k)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have kC : ∀ k < 5, some (398 + k, 388, k) ∉ vbgS.map loadKey := by decide +kernel
  have rC : ∀ k < 5, σ (.n (398 + k)) = sF.cap.getD k 0 ∧
      LoadHolds rd (σ (.n 388)) k (σ (.n (398 + k))) := fun k hk =>
    good_readS (gC _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (kC k hk)
      (ld k _ (hcapF k hk))
  have q403 : σ (.n 403) = σ (.n 389) := g 231 (.copy (.n 403) (.n 389)) (by decide +kernel) rfl
  have q404 : σ (.n 404) = σ (.n 394) := g 232 (.copy (.n 404) (.n 394)) (by decide +kernel) rfl
  -- the regions
  have R1 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR1 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR1, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
      List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
    exact ⟨c9, m10, m11, m12, m13, m14, m15, trivial, trivial, trivial, c19, hrcH,
      fun k hk => q23 k hk⟩
  have R2 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR2 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR2, fsNextT, fsPackT, List.forall_mem_append, List.forall_mem_cons,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
    exact ⟨l28, p28.1, p28.2, q31, q32, l33, p33.1, p33.2, q36⟩
  have R3 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR3 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR3, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, and_assoc, keccakA, challengeT]
    exact ⟨c37, a38, trivial,
      show σ (.n 40) = σ (.n 38) * σ (.n 39) ∧ σ (.n 40) = 1 from
        ⟨m40, by rw [m40, i39, mul_inv_cancel₀ (by rw [e38]; exact hcnt)]⟩,
      c41, c42, c43, c44, c45, k35, hco, m60, a61, m62, a63, trivial⟩
  have R4 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR4 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR4, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨forall_flatten_range KM, trivial, trivial⟩
  have R5 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR5 True
      (fun rs => rs = sF.cap ++ [curF, vals]) :=
    holdsList_straightN _ (by decide +kernel) (forall_flatten_range TB) trivial
  have R6 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR6 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR6, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    exact ⟨m141, l142, c143, a144⟩
  have R8 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR8 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR8, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    refine ⟨c374, show σ (.n 374) = σ (.n 375) * σ (.n 142) by
        rw [d375, mul_assoc, inv_mul_cancel₀ (by rw [e142]; exact gen_pow_ne_zero _), mul_one],
      c376, m377, l378, a379, c380, m381, l382, ⟨?_, fun hne => ?_⟩⟩
    · rw [a379, c376, e378, tb_word_one]
      exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _)
    · have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [a379, c376, e378, tb_word_one, h0, pow_zero, e_add_self] at hne
          exact absurd rfl hne
        · exact h0
      show coreProgram.Rel rd name% «verify_bus_gkr_loop0» (List.map σ [.n 380, .n 382, .n 375,
          .n 16, .n 8, .n 17,
        .n 63, .n 142, .n 6, .n 64]) []
      simp only [List.map_cons, List.map_nil]
      rw [c380, tb_word_one, e382, e375, e16, e8, e17, e142, e6, e64]
      exact ly_complete hm0 (by omega) (by omega) hkmn hit
  have R9 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR9 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR9, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
      List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
    refine ⟨m383, m384, m385, m386, m387, m388, l389, l390, c391, a392, c393, ⟨?_, fun hne => ?_⟩,
      trivial, l395, ?_, l396, ?_, l397, ?_, fun k hk => (rC k hk).2, q403, q404⟩
    · rw [a392, c391, tb_word_one, e6]
      exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _)
    · show coreProgram.Rel rd name% «verify_bus_gkr_loop1» (List.map σ [.n 393, .n 6, .n 7,
        .n 390]) []
      simp only [List.map_cons, List.map_nil]
      rw [c393, tb_word_one, e6, e7, e390]
      exact l8_complete (by omega) (by omega) hplF hptF hz
    · show LoadHolds rd (σ (.n 394)) 0 (σ (.n 395))
      rw [e394, e395]; exact hvk 0 (by omega)
    · show LoadHolds rd (σ (.n 394)) 1 (σ (.n 396))
      rw [e394, e396]; exact hvk 1 (by omega)
    · show LoadHolds rd (σ (.n 394)) 2 (σ (.n 397))
      rw [e394, e397]; exact hvk 2 (by omega)
  obtain ⟨f0, f1, f2, f3, f4, hf5⟩ := tb_list5_eq hclF
  refine ⟨?_, ?_⟩
  · rw [vbgPre_eq']
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR4 ++ vbR5 ++ vbR6 ++ vbR7 ++
      vbR8) (by decide +kernel)).mpr ⟨?_, R9⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR4 ++ vbR5 ++ vbR6 ++ vbR7)
      (by decide +kernel)).mpr ⟨?_, R8⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR4 ++ vbR5 ++ vbR6)
      (by decide +kernel)).mpr ⟨?_, R7⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR4 ++ vbR5)
      (by decide +kernel)).mpr ⟨?_, R6⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR4)
      (by decide +kernel)).mpr ⟨?_, R5⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3) (by decide +kernel)).mpr
      ⟨?_, R4⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2) (by decide +kernel)).mpr ⟨?_, R3⟩
    exact (tb_holdsList_append_noRet (A := vbR1) (by decide +kernel)).mpr ⟨R1, R2⟩
  · have hc : ∀ k < 5, σ (.n (398 + k)) = sF.cap.getD k 0 := fun k hk => (rC k hk).1
    rw [hf5] at hc
    have h0 := hc 0 (by omega)
    have h1 := hc 1 (by omega)
    have h2 := hc 2 (by omega)
    have h3 := hc 3 (by omega)
    have h4 := hc 4 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3 h4
    show [σ (.n 398), σ (.n 399), σ (.n 400), σ (.n 401), σ (.n 402), σ (.n 403), σ (.n 404)] =
      sF.cap ++ [curF, vals]
    rw [hf5, h0, h1, h2, h3, h4, q403, q404, e389, e394]
    rfl

end Body

end
end LeanVM.Guest.B1.Tables
