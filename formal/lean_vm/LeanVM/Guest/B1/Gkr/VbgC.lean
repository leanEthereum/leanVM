/-
  LeanVM.Guest.B1.Gkr.VbgC

  `verify_bus_gkr`'s body, completely: on a memory holding the root slot, the tables, the odd
  step's and the layers' words and the last slot, its honest valuation satisfies the body and
  returns the last slot's capacity, cursor and values.
-/

module

public import LeanVM.Guest.B1.Gkr.VbgOdd
public import LeanVM.Guest.B1.Gkr.Loop8Complete
public import LeanVM.Guest.B1.Selectors.LayoutBasic

/-!
# `verify_bus_gkr`'s body, completely (G:1768-1940)

`vbg_holds_of`: the body evaluated forward (`vbgEvL`, the allocations answered by the buffers'
pointers), its regions `vbR1 .. vbR8`: the range check of `g^depth` (the memory defined at `g^depth`
and `g^(32 - depth)`), the two roots read and the count asserted nonzero, the root slot stored,
the tables, the binary layer at an odd depth (`odc_holds`), the layer loop (`ly_complete`), the
point's copy (`l8_complete`) and the last slot read.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The regions of the body -/

/-- The depth's powers, the allocations, the range check, the capacity's copies. -/
def vbR1 : List Stmt :=
  [.atom (.const (.n 8) (word 4 0 0)), .atom (.mul (.n 9) (.n 6) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.mul (.n 12) (.n 11) (.n 11)), .atom (.mul (.n 13) (.n 12) (.n 12)),
    .atom (.mul (.n 14) (.n 13) (.n 9)), .atom (.hint (.allocDyn (.n 15) (.n 14))),
    .atom (.hint (.alloc (.n 16) 6034)), .atom (.hint (.alloc (.n 17) 1640)),
    .atom (.const (.n 18) (word 4294967296 0 0)),
    .atom (.rangeCheck (.n 6) (.n 19) (.n 20) (.n 21) (.n 18)),
    .atom (.copy (.n 22) (.n 0)), .atom (.copy (.n 23) (.n 1)), .atom (.copy (.n 24) (.n 2)),
    .atom (.copy (.n 25) (.n 3)), .atom (.copy (.n 26) (.n 4))]

/-- The two roots. -/
def vbR2 : List Stmt := fsNextT (.n 5) 0 27 ++ fsNextT (.n 5) 1 37

/-- The count asserted nonzero, the root slot, the tables' allocations. -/
def vbR3 : List Stmt :=
  [.atom (.const (.n 47) (word 0 0 0)), .atom (.add (.n 48) (.n 37) (.n 47)),
    .atom (.hint (.inverse (.n 48) (.n 49))), .atom (.assertNe (.n 48) (.n 49) (.n 50)),
    .atom (.load (.n 22) (.n 15) 0), .atom (.load (.n 23) (.n 15) 1),
    .atom (.load (.n 24) (.n 15) 2), .atom (.load (.n 25) (.n 15) 3),
    .atom (.load (.n 26) (.n 15) 4), .atom (.load (.n 34) (.n 15) 13),
    .atom (.load (.n 36) (.n 15) 14), .atom (.load (.n 44) (.n 15) 15),
    .atom (.load (.n 46) (.n 15) 16), .atom (.const (.n 51) (word 4 0 0)),
    .atom (.mul (.n 52) (.n 5) (.n 51)), .atom (.load (.n 52) (.n 15) 5),
    .atom (.load (.n 27) (.n 15) 6), .atom (.load (.n 27) (.n 15) 7),
    .atom (.load (.n 37) (.n 15) 8), .atom (.load (.n 17) (.n 15) 9),
    .atom (.const (.n 53) (word 1 0 0)), .atom (.load (.n 53) (.n 15) 10),
    .atom (.const (.n 54) (word 1 0 0)), .atom (.load (.n 54) (.n 15) 11),
    .atom (.const (.n 55) (word 1 0 0)), .atom (.load (.n 55) (.n 15) 12),
    .atom (.hint (.alloc (.n 56) 8))]

/-- The table `k_mod_next` at `g^r` and `g^(4 + r)` (G:1802-1805). -/
def vbKmn (r : ℕ) : List Stmt :=
  [.atom (.const (.n (57 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0 0)),
    .atom (.load (.n (57 + 2 * r)) (.n 56) r),
    .atom (.const (.n (58 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0 0)),
    .atom (.load (.n (58 + 2 * r)) (.n 56) (4 + r))]

/-- The table `k_mod_next`, the tables' allocations. -/
def vbR3k : List Stmt :=
  ((List.range 4).map vbKmn).flatten ++
    [.atom (.hint (.alloc (.n 65) 33)), .atom (.hint (.alloc (.n 66) 33))]

/-- The tables `pairs[d] = g^(d/2)`, `depth_shift[d] = g^(d % 2)`. -/
def vbTab (k : ℕ) : List Stmt :=
  [.atom (.const (.n (67 + 2 * k)) (word (2 ^ (k / 2)) 0 0)),
    .atom (.load (.n (67 + 2 * k)) (.n 65) k),
    .atom (.const (.n (68 + 2 * k)) (word (2 ^ (k % 2)) 0 0)),
    .atom (.load (.n (68 + 2 * k)) (.n 66) k)]

/-- The tables. -/
def vbR4 : List Stmt := ((List.range 33).map vbTab).flatten

/-- The depth's parity. -/
def vbR5 : List Stmt :=
  [.atom (.mul (.n 133) (.n 66) (.n 6)), .atom (.load (.n 134) (.n 133) 0),
    .atom (.const (.n 135) (word 1 0 0)), .atom (.add (.n 136) (.n 134) (.n 135))]

/-- The binary layer at an odd depth. -/
def vbR6 : List Stmt := [.ite (.n 136) [] odBody]

/-- The layer loop. -/
def vbR7 : List Stmt :=
  [.atom (.const (.n 309) (word 1 0 0)), .atom (.mul (.n 310) (.n 65) (.n 6)),
    .atom (.load (.n 311) (.n 310) 0), .atom (.add (.n 312) (.n 309) (.n 311)),
    .atom (.const (.n 313) (word 1 0 0)), .atom (.mul (.n 314) (.n 65) (.n 6)),
    .atom (.load (.n 315) (.n 314) 0),
    .callIf (.n 312) "__loop6" [.n 313, .n 315, .n 66, .n 6, .n 15, .n 16, .n 56]]

/-- The last slot, the point's copy, the returns. -/
def vbR8 : List Stmt :=
  [.atom (.mul (.n 316) (.n 6) (.n 6)), .atom (.mul (.n 317) (.n 316) (.n 316)),
    .atom (.mul (.n 318) (.n 317) (.n 317)), .atom (.mul (.n 319) (.n 318) (.n 318)),
    .atom (.mul (.n 320) (.n 319) (.n 6)), .atom (.mul (.n 321) (.n 15) (.n 320)),
    .atom (.load (.n 322) (.n 321) 5), .atom (.load (.n 323) (.n 321) 9),
    .atom (.const (.n 324) (word 1 0 0)), .atom (.add (.n 325) (.n 324) (.n 6)),
    .atom (.const (.n 326) (word 1 0 0)),
    .callIf (.n 325) "__loop7" [.n 326, .n 6, .n 7, .n 323],
    .atom (.load (.n 327) (.n 321) 0), .atom (.load (.n 328) (.n 321) 1),
    .atom (.load (.n 329) (.n 321) 2), .atom (.load (.n 330) (.n 321) 3),
    .atom (.load (.n 331) (.n 321) 4), .atom (.copy (.n 332) (.n 322)),
    .atom (.load (.n 333) (.n 321) 6), .atom (.load (.n 334) (.n 321) 7),
    .atom (.load (.n 335) (.n 321) 8)]

theorem vbgPre_eq' :
    vbgPre = vbR1 ++ vbR2 ++ vbR3 ++ vbR3k ++ vbR4 ++ vbR5 ++ vbR6 ++ vbR7 ++ vbR8 :=
  tbStmtsEqb_sound (by decide +kernel)

theorem tb_word_four : word 4 0 0 = gen ^ 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)]

/-- The rate cells of the two roots waiting. -/
theorem rateOf_two_getD (x0 x1 : E) :
    (rateOf [(x0, dsObserve), (x1, dsObserve)]).getD 0 0 = (Keccak.scalarCells x0 dsObserve).1 ∧
      (rateOf [(x0, dsObserve), (x1, dsObserve)]).getD 1 0 =
        (Keccak.scalarCells x0 dsObserve).2 ∧
      (rateOf [(x0, dsObserve), (x1, dsObserve)]).getD 2 0 =
        (Keccak.scalarCells x1 dsObserve).1 ∧
      (rateOf [(x0, dsObserve), (x1, dsObserve)]).getD 3 0 =
        (Keccak.scalarCells x1 dsObserve).2 := by
  rw [rateOf_eq_cells _ (by simp)]
  simp [pendCells]

theorem tb_list5_eq {l : List E} (h : l.length = 5) : ∃ a0 a1 a2 a3 a4, l = [a0, a1, a2, a3, a4] := by
  match l, h with
  | [a0, a1, a2, a3, a4], _ => exact ⟨a0, a1, a2, a3, a4, rfl⟩

theorem tb_list3_eq {l : List E} (h : l.length = 3) : ∃ a0 a1 a2, l = [a0, a1, a2] := by
  match l, h with
  | [a0, a1, a2], _ => exact ⟨a0, a1, a2, rfl⟩

/-- The allocations' pointers: the layers, the rounds' records, the rows, `k_mod_next`, `pairs`,
`depth_shift`. -/
def vbgW (layers rounds rows kmn pairs dsh : E) : ℕ → E := fun i ↦
  if i = 15 then layers else if i = 16 then rounds else if i = 17 then rows else
    if i = 56 then kmn else if i = 65 then pairs else dsh

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

/-- **`verify_bus_gkr`'s body, completely**, on its honest valuation, at `1 ≤ depth ≤ 32`: the range check's words
defined, the two roots at the cursor (the count nonzero), the root slot, the tables, the binary
layer's words at an odd depth, every layer's words (`LyIter`), and the last slot with its point at
`zeta` give the relation, returning the last slot's capacity, cursor and values. -/
theorem vbg_body_of {depth : ℕ} (hd1 : 1 ≤ depth) (hd : depth ≤ 32) {cap0 : List E}
    (hcl : cap0.length = 5) {cur zeta layers rounds rows kmn pairs dsh : E}
    (hrc : (rd (addressOfIndex depth)).isSome = true ∧ (rd (addressOfIndex (32 - depth))).isSome
        = true)
    {x0 x1 : E} (hx0 : LoadHolds rd cur 0 x0) (hx1 : LoadHolds rd cur 1 x1) (hcnt : x1 ≠ 0)
    (hroot : GkSlotC rd layers 0 ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ (cur * gen ^ 2)
      ⟨[x0, x0, x1], []⟩ rows 1 1 1)
    (hkmn : KModNext rd kmn)
    (hpairs : TbReadsAt rd pairs ((List.range 33).map fun k ↦ gen ^ (k / 2)))
    (hdsh : TbReadsAt rd dsh ((List.range 33).map fun k ↦ gen ^ (k % 2)))
    (hodd : depth % 2 = 1 → ∃ D : GkStepD,
      D.Ok ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ ⟨[x0, x0, x1], []⟩ 1 ∧
      TbReadsAt rd (cur * gen ^ 2) D.xs ∧
      GkSlotC rd layers 1 (D.s' ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ ⟨[x0, x0, x1], []⟩ 1)
        (cur * gen ^ 2 * gen ^ 6)
        (D.st' ⟨cap0, [(x0, dsObserve), (x1, dsObserve)]⟩ ⟨[x0, x0, x1], []⟩ 1)
        (rows * gen ^ 40) gen 1 1)
    (hit : ∀ j < depth / 2, LyIter rd layers rounds (depth % 2) j)
    {sF : Fs} {curF : E} {stF : GkrState} {rowF posF halfF parF : E}
    (hlast : GkSlotC rd layers depth sF curF stF rowF posF halfF parF)
    (hz : TbReadsAt rd zeta stF.point) :
    Stmt.HoldsList (coreProgram.Rel rd) rd
        (B1.Val.ofArgs (ev rd (vbgW layers rounds rows kmn pairs dsh) (cap0 ++ [cur, gen ^ depth, zeta])
          vbgEvL)) vbgPre True (fun rs => rs = sF.cap ++ [curF] ++ stF.values) ∧
      vbgRets.map (B1.Val.ofArgs (ev rd (vbgW layers rounds rows kmn pairs dsh)
        (cap0 ++ [cur, gen ^ depth, zeta]) vbgEvL)) = sF.cap ++ [curF] ++ stF.values := by
  obtain ⟨a0, a1, a2, a3, a4, rfl⟩ := tb_list5_eq hcl
  simp only [List.cons_append, List.nil_append]
  obtain ⟨fn, hf, hp, hb⟩ := vbgFound
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  set args : List E := [a0, a1, a2, a3, a4, cur, gen ^ depth, zeta] with hargs
  have hc8 : chk args.length vbgEvL = some c' := hc'
  set W : ℕ → E := vbgW layers rounds rows kmn pairs dsh with hW
  set σ : Val := B1.Val.ofArgs (ev rd W args vbgEvL) with hσ
  have hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s := (ev_spec rd W vbgEvL args hc8).2.2
  have par : ∀ i < 8, σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd W hc8 (by simpa [hargs] using hi)
  have e0 : σ (.n 0) = a0 := par 0 (by omega)
  have e1 : σ (.n 1) = a1 := par 1 (by omega)
  have e2 : σ (.n 2) = a2 := par 2 (by omega)
  have e3 : σ (.n 3) = a3 := par 3 (by omega)
  have e4 : σ (.n 4) = a4 := par 4 (by omega)
  have e5 : σ (.n 5) = cur := par 5 (by omega)
  have e6 : σ (.n 6) = gen ^ depth := par 6 (by omega)
  have e7 : σ (.n 7) = zeta := par 7 (by omega)
  have g := fun n a heq hf => vb_good (rd := rd) (w := W) (σ := σ) hG n a heq hf
  set m := depth / 2 with hm
  set sh := depth % 2 with hsh
  have hd0 : depth = 2 * m + sh := by omega
  -- the depth's powers, the allocations, the range check
  have c8 : σ (.n 8) = word 4 0 0 := g 0 (.const (.n 8) (word 4 0 0)) (by decide +kernel) rfl
  have m9 := good_mul (g 1 (.mul (.n 9) (.n 6) (.n 8)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m10 := good_mul (g 2 (.mul (.n 10) (.n 9) (.n 9)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m11 := good_mul (g 3 (.mul (.n 11) (.n 10) (.n 10)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m12 := good_mul (g 4 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m13 := good_mul (g 5 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m14 := good_mul (g 6 (.mul (.n 14) (.n 13) (.n 9)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have e15 : σ (.n 15) = layers := by
    have h : σ (.n 15) = W 15 := g 7 (.hint (.allocDyn (.n 15) (.n 14))) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e16 : σ (.n 16) = rounds := by
    have h : σ (.n 16) = W 16 := g 8 (.hint (.alloc (.n 16) 6034)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e17 : σ (.n 17) = rows := by
    have h : σ (.n 17) = W 17 := g 9 (.hint (.alloc (.n 17) 1640)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have c18 : σ (.n 18) = word 4294967296 0 0 :=
    g 10 (.const (.n 18) (word 4294967296 0 0)) (by decide +kernel) rfl
  have w32 : word 4294967296 0 0 = gen ^ 32 := by
    rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num)]
  have grc := g 11 (.rangeCheck (.n 6) (.n 19) (.n 20) (.n 21) (.n 18)) (by decide +kernel) rfl
  have h1819 : (V.n 18).idx < (V.n 19).idx := show 18 < 19 by norm_num
  have e19 : σ (.n 19) = gen ^ (32 - depth) := by
    have h3 : σ (.n 19) = σ (.n 18) * (σ (.n 6))⁻¹ := by
      have := grc.2.2
      simpa only [h1819, ↓reduceIte] using this
    have hp32 : gen ^ 32 = gen ^ (32 - depth) * gen ^ depth := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    rw [h3, c18, w32, e6, hp32, mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero _), mul_one]
  have hrcH : (Atom.rangeCheck (.n 6) (.n 19) (.n 20) (.n 21) (.n 18)).Holds rd σ := by
    refine holds_of_good grc ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e6]; exact tb_gen_pow_isInK _
    · rw [e6, gen_pow_eq_ofK, tb_addr_ofK, Nat.add_zero]
      exact hrc.1
    · rw [e19]; exact tb_gen_pow_isInK _
    · rw [e19, gen_pow_eq_ofK, tb_addr_ofK, Nat.add_zero]
      exact hrc.2
    · show (if (V.n 18).idx < (V.n 19).idx then σ (.n 6) ≠ 0 else True)
      simp only [h1819, ↓reduceIte]
      rw [e6]; exact gen_pow_ne_zero _
  have q22 : σ (.n 22) = σ (.n 0) := g 12 (.copy (.n 22) (.n 0)) (by decide +kernel) rfl
  have q23 : σ (.n 23) = σ (.n 1) := g 13 (.copy (.n 23) (.n 1)) (by decide +kernel) rfl
  have q24 : σ (.n 24) = σ (.n 2) := g 14 (.copy (.n 24) (.n 2)) (by decide +kernel) rfl
  have q25 : σ (.n 25) = σ (.n 3) := g 15 (.copy (.n 25) (.n 3)) (by decide +kernel) rfl
  have q26 : σ (.n 26) = σ (.n 4) := g 16 (.copy (.n 26) (.n 4)) (by decide +kernel) rfl
  -- the two roots
  obtain ⟨e27, cl27, hfs27⟩ := fsNextT_good (C := coreProgram.Rel rd)
    (kret := fun rs => rs = sF.cap ++ [curF] ++ stF.values)
    (vb_goodB hG 17 (fsNextT (.n 5) 0 27) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (by decide +kernel) (by rw [e5]; exact hx0)
  obtain ⟨e37, cl37, hfs37⟩ := fsNextT_good (C := coreProgram.Rel rd)
    (kret := fun rs => rs = sF.cap ++ [curF] ++ stF.values)
    (vb_goodB hG 26 (fsNextT (.n 5) 1 37) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (by decide +kernel) (by rw [e5]; exact hx1)
  obtain ⟨e34, e36⟩ := Prod.ext_iff.mp cl27
  obtain ⟨e44, e46⟩ := Prod.ext_iff.mp cl37
  simp only [Nat.reduceAdd] at e34 e36 e44 e46
  -- the count asserted nonzero, the root slot
  have hroot' := hroot
  obtain ⟨-, -, -, hcap0, hrate0, hcur0, -, hval0, hrow0, -, -, hpos0, hhalf0, hpar0⟩ := hroot'
  simp only [Nat.mul_zero, Nat.zero_add] at hcap0 hrate0 hcur0 hval0 hrow0 hpos0 hhalf0 hpar0
  have c47 : σ (.n 47) = word 0 0 0 := g 35 (.const (.n 47) (word 0 0 0)) (by decide +kernel) rfl
  have a48 : σ (.n 48) = σ (.n 37) + σ (.n 47) :=
    g 36 (.add (.n 48) (.n 37) (.n 47)) (by decide +kernel) rfl
  have i49 : σ (.n 49) = (σ (.n 48))⁻¹ :=
    g 37 (.hint (.inverse (.n 48) (.n 49))) (by decide +kernel) rfl
  have m50 : σ (.n 50) = σ (.n 48) * σ (.n 49) :=
    good_mulS (vb_goodS hG 38 (.atom (.assertNe (.n 48) (.n 49) (.n 50))) (by decide +kernel) rfl)
      (by omega) (by omega)
  have e48 : σ (.n 48) = x1 := by rw [a48, c47, tb_word_zero, add_zero, e37]
  have c51 : σ (.n 51) = word 4 0 0 := g 48 (.const (.n 51) (word 4 0 0)) (by decide +kernel) rfl
  have m52 := good_mul (g 49 (.mul (.n 52) (.n 5) (.n 51)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have c53 : σ (.n 53) = word 1 0 0 := g 55 (.const (.n 53) (word 1 0 0)) (by decide +kernel) rfl
  have c54 : σ (.n 54) = word 1 0 0 := g 57 (.const (.n 54) (word 1 0 0)) (by decide +kernel) rfl
  have c55 : σ (.n 55) = word 1 0 0 := g 59 (.const (.n 55) (word 1 0 0)) (by decide +kernel) rfl
  have e56 : σ (.n 56) = kmn := by
    have h : σ (.n 56) = W 56 := g 61 (.hint (.alloc (.n 56) 8)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e65 : σ (.n 65) = pairs := by
    have h : σ (.n 65) = W 65 := g 78 (.hint (.alloc (.n 65) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e66 : σ (.n 66) = dsh := by
    have h : σ (.n 66) = W 66 := g 79 (.hint (.alloc (.n 66) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have hr2 := rateOf_two_getD x0 x1
  have R3 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR3 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    simp only [vbR3, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨c47, a48, trivial, ⟨m50, by rw [m50, i49, mul_inv_cancel₀ (by rw [e48]; exact hcnt)]⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, c51, m52, ?_, ?_, ?_, ?_, ?_, c53, ?_, c54, ?_, c55, ?_⟩
    · rw [e15, q22, e0]; exact hcap0 0 (by omega)
    · rw [e15, q23, e1]; exact hcap0 1 (by omega)
    · rw [e15, q24, e2]; exact hcap0 2 (by omega)
    · rw [e15, q25, e3]; exact hcap0 3 (by omega)
    · rw [e15, q26, e4]; exact hcap0 4 (by omega)
    · rw [e15, e34, ← hr2.1]; exact hrate0 0 (by omega)
    · rw [e15, e36, ← hr2.2.1]; exact hrate0 1 (by omega)
    · rw [e15, e44, ← hr2.2.2.1]; exact hrate0 2 (by omega)
    · rw [e15, e46, ← hr2.2.2.2]; exact hrate0 3 (by omega)
    · rw [e15, m52, e5, c51, tb_word_four]; exact hcur0
    · rw [e15, e27]; exact hval0 0 (by omega)
    · rw [e15, e27]; exact hval0 1 (by omega)
    · rw [e15, e37]; exact hval0 2 (by omega)
    · rw [e15, e17]; exact hrow0
    · rw [e15, c53, tb_word_one]; exact hpos0
    · rw [e15, c54, tb_word_one]; exact hhalf0
    · rw [e15, c55, tb_word_one]; exact hpar0
  -- the table `k_mod_next`
  have gK := vb_goodB hG 62 ((List.range 4).map vbKmn).flatten (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have R3k : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR3k True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    unfold vbR3k
    rw [tb_holdsList_append_noRet (by decide +kernel)]
    refine ⟨(tb_holdsList_flatten_range 4 vbKmn fun _ => rfl).mpr fun r hr => ?_, ?_⟩
    · have mem : ∀ t ∈ vbKmn r, t ∈ ((List.range 4).map vbKmn).flatten := fun t ht =>
        List.mem_flatten.mpr ⟨vbKmn r, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩, ht⟩
      have c0 : σ (.n (57 + 2 * r)) = word (2 ^ ((r + 1) % 4)) 0 0 :=
        gK (.atom (.const (.n (57 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0 0)))
          (mem _ (by simp [vbKmn]))
      have c1 : σ (.n (58 + 2 * r)) = word (2 ^ ((r + 1) / 4)) 0 0 :=
        gK (.atom (.const (.n (58 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0 0)))
          (mem _ (by simp [vbKmn]))
      rw [tb_word_two_pow (by omega)] at c0 c1
      obtain ⟨k4, k0⟩ := hkmn r hr
      simp only [vbKmn, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      refine ⟨by rw [c0, tb_word_two_pow (by omega)], by rw [e56, c0]; exact k0,
        by rw [c1, tb_word_two_pow (by omega)], by rw [e56, c1]; exact k4⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
  -- the tables
  have gT := vb_goodB hG 80 vbR4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hpk : ∀ k < 33, LoadHolds rd pairs k (gen ^ (k / 2)) := fun k hk => by
    have := hpairs k (by simpa using hk)
    simpa using this
  have hdk : ∀ k < 33, LoadHolds rd dsh k (gen ^ (k % 2)) := fun k hk => by
    have := hdsh k (by simpa using hk)
    simpa using this
  have R4 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR4 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    refine (tb_holdsList_flatten_range 33 vbTab fun _ => rfl).mpr fun k hk => ?_
    have mem : ∀ t ∈ vbTab k, t ∈ vbR4 := fun t ht =>
      List.mem_flatten.mpr ⟨vbTab k, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ht⟩
    have c0 : σ (.n (67 + 2 * k)) = word (2 ^ (k / 2)) 0 0 :=
      gT (.atom (.const (.n (67 + 2 * k)) (word (2 ^ (k / 2)) 0 0))) (mem _ (by simp [vbTab]))
    have c1 : σ (.n (68 + 2 * k)) = word (2 ^ (k % 2)) 0 0 :=
      gT (.atom (.const (.n (68 + 2 * k)) (word (2 ^ (k % 2)) 0 0))) (mem _ (by simp [vbTab]))
    rw [tb_word_two_pow (by omega)] at c0 c1
    simp only [vbTab, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨by rw [c0, tb_word_two_pow (by omega)], by rw [e65, c0]; exact hpk k hk,
      by rw [c1, tb_word_two_pow (by omega)], by rw [e66, c1]; exact hdk k hk⟩
  -- the depth's parity
  have m133 := good_mul (g 212 (.mul (.n 133) (.n 66) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have hdd : LoadHolds rd (σ (.n 133)) 0 (gen ^ sh) := by
    rw [m133, e66, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hdk depth (by omega)
  obtain ⟨e134, l134⟩ := good_read (g 213 (.load (.n 134) (.n 133) 0) (by decide +kernel) rfl)
    (by decide +kernel) hdd
  have c135 : σ (.n 135) = word 1 0 0 := g 214 (.const (.n 135) (word 1 0 0)) (by decide +kernel) rfl
  have a136 : σ (.n 136) = σ (.n 134) + σ (.n 135) :=
    g 215 (.add (.n 136) (.n 134) (.n 135)) (by decide +kernel) rfl
  have R5 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR5 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    simp only [vbR5, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨m133, l134, c135, a136⟩
  -- the binary layer at an odd depth
  have R6 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR6 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    simp only [vbR6, Stmt.HoldsList]
    rw [tb_holds_ite_noRet _ _ _ rfl odBody_noRet]
    refine ⟨⟨?_, fun _ => trivial, fun hne => ?_⟩, trivial⟩
    · rw [a136, e134, c135, tb_word_one]
      exact tb_isInK_add (tb_gen_pow_isInK _) tb_isInK_one
    · have hsh1 : sh = 1 := by
        by_contra h
        rw [a136, e134, c135, tb_word_one, show sh = 0 by omega, pow_zero, e_add_self] at hne
        exact hne rfl
      obtain ⟨D, hD, hxD, hS'⟩ := hodd hsh1
      exact odc_holds hG (by rw [e15]; exact hroot) hD rfl hxD
        (by rw [e15]; exact hS')
  -- the layer loop
  have c309 : σ (.n 309) = word 1 0 0 := g 217 (.const (.n 309) (word 1 0 0)) (by decide +kernel) rfl
  have m310 := good_mul (g 218 (.mul (.n 310) (.n 65) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have hpp : ∀ p, p = σ (.n 65) * σ (.n 6) → LoadHolds rd p 0 (gen ^ m) := fun p hp => by
    rw [hp, e65, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hpk depth (by omega)
  obtain ⟨e311, l311⟩ := good_read (g 219 (.load (.n 311) (.n 310) 0) (by decide +kernel) rfl)
    (by decide +kernel) (hpp _ m310)
  have a312 : σ (.n 312) = σ (.n 309) + σ (.n 311) :=
    g 220 (.add (.n 312) (.n 309) (.n 311)) (by decide +kernel) rfl
  have c313 : σ (.n 313) = word 1 0 0 := g 221 (.const (.n 313) (word 1 0 0)) (by decide +kernel) rfl
  have m314 := good_mul (g 222 (.mul (.n 314) (.n 65) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  obtain ⟨e315, l315⟩ := good_read (g 223 (.load (.n 315) (.n 314) 0) (by decide +kernel) rfl)
    (by decide +kernel) (hpp _ m314)
  have R7 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR7 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    simp only [vbR7, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil]
    refine ⟨c309, m310, l311, a312, c313, m314, l315, ?_, fun hne => ?_⟩
    · rw [a312, c309, e311, tb_word_one]
      exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _)
    · have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [a312, c309, e311, tb_word_one, h0, pow_zero, e_add_self] at hne
          exact absurd rfl hne
        · exact h0
      rw [c313, tb_word_one, e315, e66, e6, e15, e16, e56]
      exact ly_complete hm0 (by omega) (by omega)
        (by rw [m133, e66, e6] at hdd; exact hdd) hkmn hit
  -- the last slot, the point's copy
  obtain ⟨hclF, -, -, hcapF, -, hcurF, hvlF, hvalF, hrowF, hplF, hptF, -, -, -⟩ := hlast
  have m316 := good_mul (g 225 (.mul (.n 316) (.n 6) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m317 := good_mul (g 226 (.mul (.n 317) (.n 316) (.n 316)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m318 := good_mul (g 227 (.mul (.n 318) (.n 317) (.n 317)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m319 := good_mul (g 228 (.mul (.n 319) (.n 318) (.n 318)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m320 := good_mul (g 229 (.mul (.n 320) (.n 319) (.n 6)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m321 := good_mul (g 230 (.mul (.n 321) (.n 15) (.n 320)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e321 : σ (.n 321) = layers * gen ^ (17 * depth) := by
    rw [m321, m320, m319, m318, m317, m316, e6, e15, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    ring_nf
  have ld : ∀ k v, LoadHolds rd layers (17 * depth + k) v → LoadHolds rd (σ (.n 321)) k v :=
    fun k v h => by rw [e321, tb_loadHolds_mul_gen_pow]; exact h
  obtain ⟨e322, l322⟩ := good_read (g 231 (.load (.n 322) (.n 321) 5) (by decide +kernel) rfl)
    (by decide +kernel) (ld 5 _ hcurF)
  obtain ⟨e323, l323⟩ := good_read (g 232 (.load (.n 323) (.n 321) 9) (by decide +kernel) rfl)
    (by decide +kernel) (ld 9 _ hrowF)
  have c324 : σ (.n 324) = word 1 0 0 := g 233 (.const (.n 324) (word 1 0 0)) (by decide +kernel) rfl
  have a325 : σ (.n 325) = σ (.n 324) + σ (.n 6) :=
    g 234 (.add (.n 325) (.n 324) (.n 6)) (by decide +kernel) rfl
  have c326 : σ (.n 326) = word 1 0 0 := g 235 (.const (.n 326) (word 1 0 0)) (by decide +kernel) rfl
  obtain ⟨e327, l327⟩ := good_read (g 237 (.load (.n 327) (.n 321) 0) (by decide +kernel) rfl)
    (by decide +kernel) (ld 0 _ (hcapF 0 (by omega)))
  obtain ⟨e328, l328⟩ := good_read (g 238 (.load (.n 328) (.n 321) 1) (by decide +kernel) rfl)
    (by decide +kernel) (ld 1 _ (hcapF 1 (by omega)))
  obtain ⟨e329, l329⟩ := good_read (g 239 (.load (.n 329) (.n 321) 2) (by decide +kernel) rfl)
    (by decide +kernel) (ld 2 _ (hcapF 2 (by omega)))
  obtain ⟨e330, l330⟩ := good_read (g 240 (.load (.n 330) (.n 321) 3) (by decide +kernel) rfl)
    (by decide +kernel) (ld 3 _ (hcapF 3 (by omega)))
  obtain ⟨e331, l331⟩ := good_read (g 241 (.load (.n 331) (.n 321) 4) (by decide +kernel) rfl)
    (by decide +kernel) (ld 4 _ (hcapF 4 (by omega)))
  have q332 : σ (.n 332) = σ (.n 322) := g 242 (.copy (.n 332) (.n 322)) (by decide +kernel) rfl
  obtain ⟨e333, l333⟩ := good_read (g 243 (.load (.n 333) (.n 321) 6) (by decide +kernel) rfl)
    (by decide +kernel) (ld 6 _ (hvalF 0 (by omega)))
  obtain ⟨e334, l334⟩ := good_read (g 244 (.load (.n 334) (.n 321) 7) (by decide +kernel) rfl)
    (by decide +kernel) (ld 7 _ (hvalF 1 (by omega)))
  obtain ⟨e335, l335⟩ := good_read (g 245 (.load (.n 335) (.n 321) 8) (by decide +kernel) rfl)
    (by decide +kernel) (ld 8 _ (hvalF 2 (by omega)))
  have R8 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR8 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    simp only [vbR8, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil]
    refine ⟨m316, m317, m318, m319, m320, m321, l322, l323, c324, a325, c326, ?_, fun hne => ?_,
      l327, l328, l329, l330, l331, q332, l333, l334, l335⟩
    · rw [a325, c324, tb_word_one, e6]
      exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _)
    · rw [c326, tb_word_one, e6, e7, e323]
      exact l8_complete (by omega) (by omega) hplF hptF hz
  -- the relation
  have R1 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR1 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    simp only [vbR1, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨c8, m9, m10, m11, m12, m13, m14, trivial, trivial, trivial, c18, hrcH, q22, q23, q24,
      q25, q26⟩
  have R2 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR2 True
      (fun rs => rs = sF.cap ++ [curF] ++ stF.values) := by
    unfold vbR2
    rw [tb_holdsList_append_noRet (by decide +kernel)]
    exact ⟨hfs27, hfs37⟩
  obtain ⟨f0, f1, f2, f3, f4, hf5⟩ := tb_list5_eq hclF
  obtain ⟨v0, v1, v2, hv3⟩ := tb_list3_eq hvlF
  refine ⟨?_, ?_⟩
  · rw [vbgPre_eq']
    repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨R1, R2⟩, R3⟩, R3k⟩, R4⟩, R5⟩, R6⟩, R7⟩, R8⟩
  · simp only [vbgRets, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, hf5, hv3]
    rw [e327, e328, e329, e330, e331, q332, e322, e333, e334, e335, hf5, hv3]
    rfl


end Body

end
end LeanVM.Guest.B1.Tables
