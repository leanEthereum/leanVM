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
# `verify_bus_gkr`'s body, completely

`vbg_body_of`: the body evaluated forward (`vbgEvL`, the allocations answered by the buffers'
pointers, `vbgW`), its regions `vbR1 .. vbR9`: the range check of `g^depth` (the memory defined
at `g^depth` and `g^(32 - depth)`), the two roots read, the count asserted nonzero and the
combiner, the tables `loop_bounds` and `depth_odd`, the depth's parity, `start_g`, the
root-most layer (`rtc_two` at an odd depth, `rtc_four` at an even one), the layer loop
(`ly_complete`), the last slot and row, the point's copy (`l8_complete`) and the values' buffer.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The regions of the body -/

/-- The depth's powers, the allocations, the range check, the capacity's copies. -/
def vbR1 : List Stmt :=
  [.atom (.const (.n 10) (word 4 0)), .atom (.mul (.n 11) (.n 6) (.n 10)),
    .atom (.mul (.n 12) (.n 11) (.n 11)), .atom (.mul (.n 13) (.n 12) (.n 12)),
    .atom (.mul (.n 14) (.n 13) (.n 11)), .atom (.mul (.n 15) (.n 14) (.n 14)),
    .atom (.hint (.allocDyn (.n 16) (.n 15))),
    .atom (.hint (.alloc (.n 17) 6034)), .atom (.hint (.alloc (.n 18) 1640)),
    .atom (.const (.n 19) (word 4294967296 0)),
    .atom (.rangeCheck (.n 6) (.n 20) (.n 21) (.n 22) (.n 19))] ++
  (List.range 5).map (fun k ↦ .atom (.copy (.n (23 + k)) (.n k)))

/-- The two roots. -/
def vbR2 : List Stmt :=
  fsNextT (.n 5) 0 28 ++ [.atom (.copy (.n 31) (.n 28)), .atom (.copy (.n 32) (.n 28))] ++
  fsNextT (.n 5) 1 33 ++ [.atom (.copy (.n 36) (.n 33))]

/-- The count asserted nonzero, the combiner, the claim, the tables' allocations. -/
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
    .atom (.hint (.alloc (.n 64) 33)), .atom (.hint (.alloc (.n 65) 33))]

/-- The tables `loop_bounds[d] = g^((d - 1)/2)`, `depth_odd[d] = g^(d % 2)`. -/
def vbTab (d : ℕ) : List Stmt :=
  [.atom (.const (.n (66 + 2 * d)) (word (2 ^ ((d - 1) / 2)) 0)),
    .atom (.load (.n (66 + 2 * d)) (.n 64) d),
    .atom (.const (.n (67 + 2 * d)) (word (2 ^ (d % 2)) 0)),
    .atom (.load (.n (67 + 2 * d)) (.n 65) d)]

/-- The tables. -/
def vbR5 : List Stmt := ((List.range 33).map vbTab).flatten

/-- The depth's parity, `start_g` and the root-most slot. -/
def vbR6 : List Stmt :=
  [.atom (.mul (.n 132) (.n 65) (.n 6)), .atom (.load (.n 133) (.n 132) 0),
    .atom (.const (.n 134) (word 4 0)), .atom (.mul (.n 134) (.n 135) (.n 133)),
    .atom (.mul (.n 136) (.n 135) (.n 135)), .atom (.mul (.n 137) (.n 136) (.n 136)),
    .atom (.mul (.n 138) (.n 137) (.n 135)), .atom (.mul (.n 139) (.n 138) (.n 138)),
    .atom (.mul (.n 140) (.n 16) (.n 139)),
    .atom (.const (.n 141) (word 1 0)), .atom (.add (.n 142) (.n 133) (.n 141))]

/-- The root-most layer. -/
noncomputable def vbR7 : List Stmt := [.ite (.n 142) rtFour rtTwo]

/-- The layer loop. -/
def vbR8 : List Stmt :=
  [.atom (.mul (.n 365) (.n 64) (.n 6)), .atom (.load (.n 366) (.n 365) 0),
    .atom (.const (.n 367) (word 1 0)), .atom (.add (.n 368) (.n 367) (.n 366)),
    .atom (.const (.n 369) (word 1 0)),
    .callIf (.n 368) name% «verify_bus_gkr_loop0» [.n 369, .n 366, .n 135, .n 16, .n 8, .n 18,
        .n 17, .n 63, .n 133, .n 9, .n 6]]

/-- The last slot, the last row, the point's copy, the values' buffer, the returns. -/
def vbR9 : List Stmt :=
  [.atom (.mul (.n 370) (.n 366) (.n 366)), .atom (.mul (.n 371) (.n 370) (.n 135)),
    .atom (.mul (.n 372) (.n 371) (.n 371)), .atom (.mul (.n 373) (.n 372) (.n 372)),
    .atom (.mul (.n 374) (.n 373) (.n 371)), .atom (.mul (.n 375) (.n 374) (.n 374)),
    .atom (.mul (.n 376) (.n 16) (.n 375)), .atom (.load (.n 377) (.n 376) 5),
    .atom (.const (.n 378) (word 2 0)), .atom (.mul (.n 379) (.n 366) (.n 378)),
    .atom (.mul (.n 380) (.n 379) (.n 379)), .atom (.mul (.n 381) (.n 380) (.n 380)),
    .atom (.mul (.n 382) (.n 381) (.n 379)), .atom (.mul (.n 383) (.n 382) (.n 382)),
    .atom (.mul (.n 384) (.n 383) (.n 383)), .atom (.mul (.n 385) (.n 384) (.n 384)),
    .atom (.mul (.n 386) (.n 18) (.n 385)),
    .atom (.const (.n 387) (word 1 0)), .atom (.add (.n 388) (.n 387) (.n 6)),
    .atom (.const (.n 389) (word 1 0)),
    .callIf (.n 388) name% «verify_bus_gkr_loop1» [.n 389, .n 6, .n 7, .n 386],
    .atom (.hint (.alloc (.n 390) 3)),
    .atom (.load (.n 391) (.n 376) 6), .atom (.load (.n 391) (.n 390) 0),
    .atom (.load (.n 392) (.n 376) 7), .atom (.load (.n 392) (.n 390) 1),
    .atom (.load (.n 393) (.n 376) 8), .atom (.load (.n 393) (.n 390) 2)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (394 + k)) (.n 376) k)) ++
  [.atom (.copy (.n 399) (.n 377)), .atom (.copy (.n 400) (.n 390))]

set_option maxRecDepth 10000 in
theorem vbgPre_eq' :
    vbgPre = vbR1 ++ vbR2 ++ vbR3 ++ vbR5 ++ vbR6 ++ vbR7 ++ vbR8 ++ vbR9 :=
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

/-- The allocations' pointers: the layers, the rounds' records, the rows, `loop_bounds`,
`depth_odd`, the values' buffer. -/
def vbgW (layers rounds rows bnd odd vals : E) : ℕ → E := fun i ↦
  if i = 16 then layers else if i = 17 then rounds else if i = 18 then rows else
    if i = 64 then bnd else if i = 65 then odd else vals

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
    (hcl : cap0.length = 5) {cur zeta tabs stream layers rounds rows bnd odd vals : E}
    (hrc : (rd (addressOfIndex depth)).isSome = true ∧ (rd (addressOfIndex (32 - depth))).isSome
        = true)
    {x0 x1 : E} (hx0 : LoadHolds rd cur 0 x0) (hx1 : LoadHolds rd cur 1 x1) (hcnt : x1 ≠ 0)
    (hbnd : TbReadsAt rd bnd ((List.range 33).map fun k ↦ gen ^ ((k - 1) / 2)))
    (hodt : TbReadsAt rd odd ((List.range 33).map fun k ↦ gen ^ (k % 2)))
    (hodd : depth % 2 = 1 → ∃ D : GkStepD, D.Ok (rootS cap0 x0 x1) (rootSt x0 x1) 1 ∧
      TbReadsAt rd (cur * gen ^ 2) D.xs ∧
      GkSlot rd layers 1 (D.s' (rootS cap0 x0 x1) (rootSt x0 x1) 1)
        (cur * gen ^ 2 * gen ^ D.xs.length) (D.st' (rootS cap0 x0 x1) (rootSt x0 x1) 1)
        (rows * gen ^ 40) gen)
    (hrow1 : depth % 2 = 1 → LoadHolds rd rows 41 0)
    (heven : depth % 2 = 0 → ∃ D : GkStepD, D.Ok (rootS cap0 x0 x1) (rootSt x0 x1) 2 ∧
      TbReadsAt rd (cur * gen ^ 2) D.xs ∧
      GkSlot rd layers 2 (D.s' (rootS cap0 x0 x1) (rootSt x0 x1) 2)
        (cur * gen ^ 2 * gen ^ D.xs.length) (D.st' (rootS cap0 x0 x1) (rootSt x0 x1) 2)
        (rows * gen ^ 40) gen)
    (hit : ∀ j < (depth - 1) / 2, LyIter rd layers rows rounds (depth % 2) j)
    {sF : Fs} {curF : E} {stF : GkrState} {posF : E}
    (hlast : GkSlot rd layers depth sF curF stF (rows * gen ^ (40 * ((depth - 1) / 2 + 1))) posF)
    (hz : TbReadsAt rd zeta stF.point) (hv : TbReadsAt rd vals stF.values) :
    Stmt.HoldsList (coreProgram.Rel rd) rd
        (B1.Val.ofArgs (ev rd (vbgW layers rounds rows bnd odd vals)
          (cap0 ++ [cur, gen ^ depth, zeta, tabs, stream]) vbgEvL)) vbgPre True
        (fun rs => rs = sF.cap ++ [curF, vals]) ∧
      vbgRets.map (B1.Val.ofArgs (ev rd (vbgW layers rounds rows bnd odd vals)
        (cap0 ++ [cur, gen ^ depth, zeta, tabs, stream]) vbgEvL)) = sF.cap ++ [curF, vals] := by
  obtain ⟨a0, a1, a2, a3, a4, rfl⟩ := tb_list5_eq hcl
  simp only [List.cons_append, List.nil_append]
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  set args : List E := [a0, a1, a2, a3, a4, cur, gen ^ depth, zeta, tabs, stream] with hargs
  have hc9 : chk args.length vbgEvL = some c' := hc'
  set W : ℕ → E := vbgW layers rounds rows bnd odd vals with hW
  set σ : Val := B1.Val.ofArgs (ev rd W args vbgEvL) with hσ
  have hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s := (ev_spec rd W vbgEvL args hc9).2.2
  have par : ∀ i < 10, σ (.n i) = args.getD i 0 := fun i hi =>
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
  have e9 : σ (.n 9) = stream := par 9 (by omega)
  have g : ∀ n (a : Atom), tbStmtsEqb [.atom a] ((vbgPre.drop n).take 1) = true →
      fixNe (.atom a) = .atom a → Good rd vbgS W σ a :=
    fun n a heq hf => vb_good (rd := rd) (w := W) (σ := σ) hG n a heq hf
  set sh := depth % 2 with hsh
  set m := (depth - 1) / 2 with hm
  -- the depth's powers, the allocations, the range check
  have c10 : σ (.n 10) = word 4 0 := g 0 (.const (.n 10) (word 4 0)) (by decide +kernel) rfl
  have m11 := good_mul (g 1 (.mul (.n 11) (.n 6) (.n 10)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m12 := good_mul (g 2 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m13 := good_mul (g 3 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m14 := good_mul (g 4 (.mul (.n 14) (.n 13) (.n 11)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m15 := good_mul (g 5 (.mul (.n 15) (.n 14) (.n 14)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have e16 : σ (.n 16) = layers := by
    have h : σ (.n 16) = W 16 := g 6 (.hint (.allocDyn (.n 16) (.n 15))) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e17 : σ (.n 17) = rounds := by
    have h : σ (.n 17) = W 17 := g 7 (.hint (.alloc (.n 17) 6034)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e18 : σ (.n 18) = rows := by
    have h : σ (.n 18) = W 18 := g 8 (.hint (.alloc (.n 18) 1640)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have c19 : σ (.n 19) = word 4294967296 0 :=
    g 9 (.const (.n 19) (word 4294967296 0)) (by decide +kernel) rfl
  have w32 : word 4294967296 0 = gen ^ 32 := by
    rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num)]
  have grc := g 10 (.rangeCheck (.n 6) (.n 20) (.n 21) (.n 22) (.n 19)) (by decide +kernel) rfl
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
  have gq := vb_goodB hG 11 ((List.range 5).map fun k ↦ Stmt.atom (.copy (.n (23 + k)) (.n k)))
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
    (vb_goodB hG 16 (fsNextT (.n 5) 0 28) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (by decide +kernel) (by rw [e5]; exact hx0)
  obtain ⟨e33, -, hfs33⟩ := fsNextT_good (C := coreProgram.Rel rd) (kret := fun _ => True)
    (vb_goodB hG 21 (fsNextT (.n 5) 1 33) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (by decide +kernel) (by rw [e5]; exact hx1)
  obtain ⟨⟨l28, p28⟩, -⟩ := (holds_fsNextT _ _ _ _ _).mp hfs28
  obtain ⟨⟨l33, p33⟩, -⟩ := (holds_fsNextT _ _ _ _ _).mp hfs33
  have q31 : σ (.n 31) = σ (.n 28) := g 19 (.copy (.n 31) (.n 28)) (by decide +kernel) rfl
  have q32 : σ (.n 32) = σ (.n 28) := g 20 (.copy (.n 32) (.n 28)) (by decide +kernel) rfl
  have q36 : σ (.n 36) = σ (.n 33) := g 24 (.copy (.n 36) (.n 33)) (by decide +kernel) rfl
  -- the count asserted nonzero
  have c37 : σ (.n 37) = word 0 0 := g 25 (.const (.n 37) (word 0 0)) (by decide +kernel) rfl
  have a38 : σ (.n 38) = σ (.n 33) + σ (.n 37) :=
    g 26 (.add (.n 38) (.n 33) (.n 37)) (by decide +kernel) rfl
  have i39 : σ (.n 39) = (σ (.n 38))⁻¹ :=
    g 27 (.hint (.inverse (.n 38) (.n 39))) (by decide +kernel) rfl
  have m40 : σ (.n 40) = σ (.n 38) * σ (.n 39) :=
    good_mulS (vb_goodS hG 28 (.atom (.assertNe (.n 38) (.n 39) (.n 40))) (by decide +kernel) rfl)
      (by omega) (by omega)
  have e38 : σ (.n 38) = x1 := by rw [a38, c37, tb_word_zero, add_zero, e33]
  -- the combiner and the claim
  have c41 : σ (.n 41) = word 1 0 := g 29 (.const (.n 41) (word 1 0)) (by decide +kernel) rfl
  have c42 : σ (.n 42) = word 0 0 := g 30 (.const (.n 42) (word 0 0)) (by decide +kernel) rfl
  have c43 : σ (.n 43) = word 0 0 := g 31 (.const (.n 43) (word 0 0)) (by decide +kernel) rfl
  have c44 : σ (.n 44) = word 0 0 := g 32 (.const (.n 44) (word 0 0)) (by decide +kernel) rfl
  have c45 : σ (.n 45) = word 0 0 := g 33 (.const (.n 45) (word 0 0)) (by decide +kernel) rfl
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
    (g 34 (.keccak ([.n 29, .n 30, .n 34, .n 35, .n 42, .n 43, .n 44, .n 45] ++
      (List.range 5).map fun k ↦ .n (23 + k)) (lyOuts 46) false false) (by decide +kernel) rfl)
  rw [hins] at hP hcap
  have hco := challengeT_good (vb_goodB hG 35 (challengeT (.n 46) 59) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  have e59 : σ (.n 59) = (rootS [a0, a1, a2, a3, a4] x0 x1).squeeze.1 :=
    challengeT_value hco (hP 0 (by omega))
  have m60 := good_mul (g 36 (.mul (.n 60) (.n 59) (.n 36)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have a61 : σ (.n 61) = σ (.n 32) + σ (.n 60) :=
    g 37 (.add (.n 61) (.n 32) (.n 60)) (by decide +kernel) rfl
  have m62 := good_mul (g 38 (.mul (.n 62) (.n 59) (.n 61)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have a63 : σ (.n 63) = σ (.n 31) + σ (.n 62) :=
    g 39 (.add (.n 63) (.n 31) (.n 62)) (by decide +kernel) rfl
  have e63 : σ (.n 63) = polyEval (rootSt x0 x1).values (rootS [a0, a1, a2, a3, a4] x0 x1).squeeze.1 := by
    rw [a63, m62, a61, m60, q31, q32, q36, e28, e33, ← e59]
    simp only [rootSt, polyEval, List.foldr]
    ring
  have hcapP : (lyCap 46).map σ = capOf (rootS [a0, a1, a2, a3, a4] x0 x1).perm := hcap
  have e64 : σ (.n 64) = bnd := by
    have h : σ (.n 64) = W 64 := g 40 (.hint (.alloc (.n 64) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e65 : σ (.n 65) = odd := by
    have h : σ (.n 65) = W 65 := g 41 (.hint (.alloc (.n 65) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  -- the tables
  have gT := vb_goodB hG 42 vbR5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
    have c0 : σ (.n (66 + 2 * k)) = word (2 ^ ((k - 1) / 2)) 0 :=
      gT (.atom (.const (.n (66 + 2 * k)) (word (2 ^ ((k - 1) / 2)) 0))) (mem _ (by simp [vbTab]))
    have c1 : σ (.n (67 + 2 * k)) = word (2 ^ (k % 2)) 0 :=
      gT (.atom (.const (.n (67 + 2 * k)) (word (2 ^ (k % 2)) 0))) (mem _ (by simp [vbTab]))
    simp only [vbTab, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    exact ⟨c0, show LoadHolds rd (σ (.n 64)) k (σ (.n (66 + 2 * k))) by
        rw [e64, c0, tb_word_two_pow (by omega)]; exact hbk k hk, c1,
      show LoadHolds rd (σ (.n 65)) k (σ (.n (67 + 2 * k))) by
        rw [e65, c1, tb_word_two_pow (by omega)]; exact hok k hk⟩
  -- the depth's parity, `start_g` and the root-most slot
  have m132 := good_mul (g 174 (.mul (.n 132) (.n 65) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  obtain ⟨e133, l133⟩ := good_read (g 175 (.load (.n 133) (.n 132) 0) (by decide +kernel) rfl)
    (by decide +kernel) (show LoadHolds rd (σ (.n 132)) 0 (gen ^ sh) by
      rw [m132, e65, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hok depth (by omega))
  have c134 : σ (.n 134) = word 4 0 := g 176 (.const (.n 134) (word 4 0)) (by decide +kernel) rfl
  have d135 : σ (.n 135) = σ (.n 134) * (σ (.n 133))⁻¹ := by
    have h := g 177 (.mul (.n 134) (.n 135) (.n 133)) (by decide +kernel) rfl
    have hn : ¬ ((V.n 135).idx < (V.n 134).idx ∧ (V.n 133).idx < (V.n 134).idx) := by
      show ¬ (135 < 134 ∧ 133 < 134); omega
    simpa only [Good, hn, ↓reduceIte] using h
  have e135 : σ (.n 135) = gen ^ (2 - sh) := by
    rw [d135, c134, tb_word_four, e133]
    have hs : sh ≤ 2 := by omega
    rw [show (gen : E) ^ 2 = gen ^ (2 - sh) * gen ^ sh by rw [← pow_add, Nat.sub_add_cancel hs],
      mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero _), mul_one]
  have m136 := good_mul (g 178 (.mul (.n 136) (.n 135) (.n 135)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m137 := good_mul (g 179 (.mul (.n 137) (.n 136) (.n 136)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m138 := good_mul (g 180 (.mul (.n 138) (.n 137) (.n 135)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m139 := good_mul (g 181 (.mul (.n 139) (.n 138) (.n 138)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m140 := good_mul (g 182 (.mul (.n 140) (.n 16) (.n 139)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e140 : σ (.n 140) = σ (.n 16) * gen ^ (10 * (2 - sh)) := by
    rw [m140, m139, m138, m137, m136, e135, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have c141 : σ (.n 141) = word 1 0 := g 183 (.const (.n 141) (word 1 0)) (by decide +kernel) rfl
  have a142 : σ (.n 142) = σ (.n 133) + σ (.n 141) :=
    g 184 (.add (.n 142) (.n 133) (.n 141)) (by decide +kernel) rfl
  -- the root-most layer
  have R7 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR7 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    simp only [vbR7, Stmt.HoldsList]
    rw [tb_holds_ite_noRet _ _ _ rtFour_noRet rtTwo_noRet]
    refine ⟨⟨?_, fun h0 => ?_, fun hne => ?_⟩, trivial⟩
    · rw [a142, e133, c141, tb_word_one]
      exact tb_isInK_add (tb_gen_pow_isInK _) tb_isInK_one
    · have hsh0 : sh = 0 := by
        by_contra h
        rw [a142, e133, c141, tb_word_one, show sh = 1 by omega] at h0
        have := gen_pow_inj (a := 1) (b := 0) (by omega) (by omega)
          ((e_add_eq_zero_iff.mp h0).trans (pow_zero gen).symm)
        omega
      obtain ⟨D, hD, hxD, hS'⟩ := heven hsh0
      rw [hsh0] at e140
      exact rtc_four hG rfl e59 e63 hcapP z42 z43 z44 z45 hD (by rw [e5]; exact hxD) e140
        (by rw [e16, e5, e18]; exact hS')
    · have hsh1 : sh = 1 := by
        by_contra h
        rw [a142, e133, c141, tb_word_one, show sh = 0 by omega, pow_zero, e_add_self] at hne
        exact hne rfl
      obtain ⟨D, hD, hxD, hS'⟩ := hodd hsh1
      rw [hsh1] at e140
      exact rtc_two hG rfl e59 e63 hcapP z42 z43 z44 z45 hD (by rw [e5]; exact hxD) e140
        (by rw [e18]; exact hrow1 hsh1) (by rw [e16, e5, e18]; exact hS')
  -- the layer loop
  have m365 := good_mul (g 186 (.mul (.n 365) (.n 64) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  obtain ⟨e366, l366⟩ := good_read (g 187 (.load (.n 366) (.n 365) 0) (by decide +kernel) rfl)
    (by decide +kernel) (show LoadHolds rd (σ (.n 365)) 0 (gen ^ m) by
      rw [m365, e64, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hbk depth (by omega))
  have c367 : σ (.n 367) = word 1 0 := g 188 (.const (.n 367) (word 1 0)) (by decide +kernel) rfl
  have a368 : σ (.n 368) = σ (.n 367) + σ (.n 366) :=
    g 189 (.add (.n 368) (.n 367) (.n 366)) (by decide +kernel) rfl
  have c369 : σ (.n 369) = word 1 0 := g 190 (.const (.n 369) (word 1 0)) (by decide +kernel) rfl
  -- the last slot, the last row, the point's copy, the values' buffer
  obtain ⟨hclF, hcapF, -, hcurF, hvlF, hvalF, hplF, hptF, -⟩ := hlast
  have m370 := good_mul (g 192 (.mul (.n 370) (.n 366) (.n 366)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m371 := good_mul (g 193 (.mul (.n 371) (.n 370) (.n 135)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m372 := good_mul (g 194 (.mul (.n 372) (.n 371) (.n 371)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m373 := good_mul (g 195 (.mul (.n 373) (.n 372) (.n 372)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m374 := good_mul (g 196 (.mul (.n 374) (.n 373) (.n 371)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m375 := good_mul (g 197 (.mul (.n 375) (.n 374) (.n 374)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m376 := good_mul (g 198 (.mul (.n 376) (.n 16) (.n 375)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e371 : σ (.n 371) = gen ^ depth := by
    rw [m371, m370, e366, e135, ← pow_add, ← pow_add,
      show m + m + (2 - sh) = depth by omega]
  have e376 : σ (.n 376) = layers * gen ^ (10 * depth) := by
    rw [m376, m375, m374, m373, m372, e371, e16, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have ld : ∀ k v, LoadHolds rd layers (10 * depth + k) v → LoadHolds rd (σ (.n 376)) k v :=
    fun k v h => by rw [e376, tb_loadHolds_mul_gen_pow]; exact h
  obtain ⟨e377, l377⟩ := good_read (g 199 (.load (.n 377) (.n 376) 5) (by decide +kernel) rfl)
    (by decide +kernel) (ld 5 _ hcurF)
  have c378 : σ (.n 378) = word 2 0 := g 200 (.const (.n 378) (word 2 0)) (by decide +kernel) rfl
  have m379 := good_mul (g 201 (.mul (.n 379) (.n 366) (.n 378)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m380 := good_mul (g 202 (.mul (.n 380) (.n 379) (.n 379)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m381 := good_mul (g 203 (.mul (.n 381) (.n 380) (.n 380)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m382 := good_mul (g 204 (.mul (.n 382) (.n 381) (.n 379)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m383 := good_mul (g 205 (.mul (.n 383) (.n 382) (.n 382)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m384 := good_mul (g 206 (.mul (.n 384) (.n 383) (.n 383)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m385 := good_mul (g 207 (.mul (.n 385) (.n 384) (.n 384)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m386 := good_mul (g 208 (.mul (.n 386) (.n 18) (.n 385)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e386 : σ (.n 386) = rows * gen ^ (40 * (m + 1)) := by
    rw [m386, m385, m384, m383, m382, m381, m380, m379, c378, tb_word_gen, e366, e18, ← pow_succ]
    ring
  have c387 : σ (.n 387) = word 1 0 := g 209 (.const (.n 387) (word 1 0)) (by decide +kernel) rfl
  have a388 : σ (.n 388) = σ (.n 387) + σ (.n 6) :=
    g 210 (.add (.n 388) (.n 387) (.n 6)) (by decide +kernel) rfl
  have c389 : σ (.n 389) = word 1 0 := g 211 (.const (.n 389) (word 1 0)) (by decide +kernel) rfl
  have e390 : σ (.n 390) = vals := by
    have h : σ (.n 390) = W 390 := g 213 (.hint (.alloc (.n 390) 3)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  obtain ⟨v0, v1, v2, hv3⟩ := tb_list3_eq hvlF
  have hvk : ∀ k < 3, LoadHolds rd vals k (stF.values.getD k 0) := fun k hk => by
    have := hv k (by rw [hvlF]; exact hk)
    rwa [← List.getD_eq_getElem _ 0] at this
  obtain ⟨e391, l391⟩ := good_read (g 214 (.load (.n 391) (.n 376) 6) (by decide +kernel) rfl)
    (by decide +kernel) (ld 6 _ (hvalF 0 (by omega)))
  obtain ⟨e392, l392⟩ := good_read (g 216 (.load (.n 392) (.n 376) 7) (by decide +kernel) rfl)
    (by decide +kernel) (ld 7 _ (hvalF 1 (by omega)))
  obtain ⟨e393, l393⟩ := good_read (g 218 (.load (.n 393) (.n 376) 8) (by decide +kernel) rfl)
    (by decide +kernel) (ld 8 _ (hvalF 2 (by omega)))
  have gC := vb_goodB hG 220 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (394 + k)) (.n 376) k)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have kC : ∀ k < 5, some (394 + k, 376, k) ∉ vbgS.map loadKey := by decide +kernel
  have rC : ∀ k < 5, σ (.n (394 + k)) = sF.cap.getD k 0 ∧
      LoadHolds rd (σ (.n 376)) k (σ (.n (394 + k))) := fun k hk =>
    good_readS (gC _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (kC k hk)
      (ld k _ (hcapF k hk))
  have q399 : σ (.n 399) = σ (.n 377) := g 225 (.copy (.n 399) (.n 377)) (by decide +kernel) rfl
  have q400 : σ (.n 400) = σ (.n 390) := g 226 (.copy (.n 400) (.n 390)) (by decide +kernel) rfl
  -- the regions
  have R1 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR1 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR1, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
      List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
    exact ⟨c10, m11, m12, m13, m14, m15, trivial, trivial, trivial, c19, hrcH,
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
      c41, c42, c43, c44, c45, k35, hco, m60, a61, m62, a63, trivial, trivial⟩
  have R5 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR5 True
      (fun rs => rs = sF.cap ++ [curF, vals]) :=
    holdsList_straightN _ (by decide +kernel) (forall_flatten_range TB) trivial
  have R6 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR6 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR6, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    exact ⟨m132, l133, c134, show σ (.n 134) = σ (.n 135) * σ (.n 133) by
        rw [d135, mul_assoc, inv_mul_cancel₀ (by rw [e133]; exact gen_pow_ne_zero _), mul_one],
      m136, m137, m138, m139, m140, c141, a142⟩
  have R8 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR8 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR8, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    refine ⟨m365, l366, c367, a368, c369, ⟨?_, fun hne => ?_⟩⟩
    · rw [a368, c367, e366, tb_word_one]
      exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _)
    · have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [a368, c367, e366, tb_word_one, h0, pow_zero, e_add_self] at hne
          exact absurd rfl hne
        · exact h0
      show coreProgram.Rel rd name% «verify_bus_gkr_loop0» (List.map σ [.n 369, .n 366, .n 135,
          .n 16, .n 8, .n 18, .n 17, .n 63, .n 133, .n 9, .n 6]) []
      simp only [List.map_cons, List.map_nil]
      rw [c369, tb_word_one, e366, e135, e16, e8, e18, e17, e133, e9, e6]
      exact ly_complete hm0 (by omega) (by omega) hit
  have R9 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR9 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR9, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
      List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
    refine ⟨m370, m371, m372, m373, m374, m375, m376, l377, c378, m379, m380, m381, m382, m383,
      m384, m385, m386, c387, a388, c389, ⟨?_, fun hne => ?_⟩,
      trivial, l391, ?_, l392, ?_, l393, ?_, fun k hk => (rC k hk).2, q399, q400⟩
    · rw [a388, c387, tb_word_one, e6]
      exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _)
    · show coreProgram.Rel rd name% «verify_bus_gkr_loop1» (List.map σ [.n 389, .n 6, .n 7,
        .n 386]) []
      simp only [List.map_cons, List.map_nil]
      rw [c389, tb_word_one, e6, e7, e386]
      exact l8_complete (by omega) (by omega) hplF hptF hz
    · show LoadHolds rd (σ (.n 390)) 0 (σ (.n 391))
      rw [e390, e391]; exact hvk 0 (by omega)
    · show LoadHolds rd (σ (.n 390)) 1 (σ (.n 392))
      rw [e390, e392]; exact hvk 1 (by omega)
    · show LoadHolds rd (σ (.n 390)) 2 (σ (.n 393))
      rw [e390, e393]; exact hvk 2 (by omega)
  obtain ⟨f0, f1, f2, f3, f4, hf5⟩ := tb_list5_eq hclF
  refine ⟨?_, ?_⟩
  · rw [vbgPre_eq']
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR5 ++ vbR6 ++ vbR7 ++
      vbR8) (by decide +kernel)).mpr ⟨?_, R9⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR5 ++ vbR6 ++ vbR7)
      (by decide +kernel)).mpr ⟨?_, R8⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR5 ++ vbR6)
      (by decide +kernel)).mpr ⟨?_, R7⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR5)
      (by decide +kernel)).mpr ⟨?_, R6⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3) (by decide +kernel)).mpr
      ⟨?_, R5⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2) (by decide +kernel)).mpr ⟨?_, R3⟩
    exact (tb_holdsList_append_noRet (A := vbR1) (by decide +kernel)).mpr ⟨R1, R2⟩
  · have hc : ∀ k < 5, σ (.n (394 + k)) = sF.cap.getD k 0 := fun k hk => (rC k hk).1
    rw [hf5] at hc
    have h0 := hc 0 (by omega)
    have h1 := hc 1 (by omega)
    have h2 := hc 2 (by omega)
    have h3 := hc 3 (by omega)
    have h4 := hc 4 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3 h4
    show [σ (.n 394), σ (.n 395), σ (.n 396), σ (.n 397), σ (.n 398), σ (.n 399), σ (.n 400)] =
      sF.cap ++ [curF, vals]
    rw [hf5, h0, h1, h2, h3, h4, q399, q400, e377, e390]
    rfl

end Body

end
end LeanVM.Guest.B1.Tables
