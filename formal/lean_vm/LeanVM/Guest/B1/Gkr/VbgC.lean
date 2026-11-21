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
combiner, the table `k_mod_next`, the tables `loop_bounds` and `depth_odd`, the table
`rounds_len` (`vbR5b`, its words `g^(7 vbgRecs d)`, `vbgRlenC_word`), the buffers sized by the
depth and the depth's parity, the root-most layer (`rtc_two` at an odd depth, `rtc_four` at an
even one), the layer loop (`ly_complete`), the last layer record, the point's copy
(`l8_complete`) and the values' buffer.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The regions of the body -/

/-- The range check and the capacity's copies. -/
def vbR1 : List Stmt :=
  [.atom (.const (.n 9) (word 4294967296 0)),
    .atom (.rangeCheck (.n 6) (.n 10) (.n 11) (.n 12) (.n 9))] ++
  (List.range 5).map (fun k ↦ .atom (.copy (.n (13 + k)) (.n k)))

/-- The two roots. -/
def vbR2 : List Stmt :=
  fsNextT (.n 5) 0 18 ++ [.atom (.copy (.n 21) (.n 18)), .atom (.copy (.n 22) (.n 18))] ++
  fsNextT (.n 5) 1 23 ++ [.atom (.copy (.n 26) (.n 23))]

/-- The count asserted nonzero, the combiner, the claim, `k_mod_next`'s allocation. -/
def vbR3 : List Stmt :=
  [.atom (.const (.n 27) (word 0 0)), .atom (.add (.n 28) (.n 23) (.n 27)),
    .atom (.hint (.inverse (.n 28) (.n 29))), .atom (.assertNe (.n 28) (.n 29) (.n 30)),
    .atom (.const (.n 31) (word 1 0)), .atom (.const (.n 32) (word 0 0)),
    .atom (.const (.n 33) (word 0 0)), .atom (.const (.n 34) (word 0 0)),
    .atom (.const (.n 35) (word 0 0)),
    keccakA ([.n 19, .n 20, .n 24, .n 25, .n 32, .n 33, .n 34, .n 35] ++
      (List.range 5).map fun k ↦ .n (13 + k)) (lyOuts 36)] ++
  [.atom (.mul (.n 49) (.n 36) (.n 26)), .atom (.add (.n 50) (.n 22) (.n 49)),
    .atom (.mul (.n 51) (.n 36) (.n 50)), .atom (.add (.n 52) (.n 21) (.n 51)),
    .atom (.hint (.alloc (.n 53) 8))]

/-- The table `k_mod_next` at `g^r` and `g^(4 + r)`. -/
def vbKmn (r : ℕ) : List Stmt :=
  [.atom (.const (.n (54 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0)),
    .atom (.load (.n (54 + 2 * r)) (.n 53) r),
    .atom (.const (.n (55 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0)),
    .atom (.load (.n (55 + 2 * r)) (.n 53) (4 + r))]

/-- The table `k_mod_next`, the tables' allocations. -/
def vbR4 : List Stmt :=
  ((List.range 4).map vbKmn).flatten ++
    [.atom (.hint (.alloc (.n 62) 33)), .atom (.hint (.alloc (.n 63) 33))]

/-- The tables `loop_bounds[d] = g^((d - 1)/2)`, `depth_odd[d] = g^(d % 2)`. -/
def vbTab (d : ℕ) : List Stmt :=
  [.atom (.const (.n (64 + 2 * d)) (word (2 ^ ((d - 1) / 2)) 0)),
    .atom (.load (.n (64 + 2 * d)) (.n 62) d),
    .atom (.const (.n (65 + 2 * d)) (word (2 ^ (d % 2)) 0)),
    .atom (.load (.n (65 + 2 * d)) (.n 63) d)]

/-- The tables. -/
def vbR5 : List Stmt := ((List.range 33).map vbTab).flatten

/-- The words of `rounds_len[d] = g^(7 vbgRecs d)` as the guest writes them. -/
def vbgRlenC : List ℕ :=
  [128, 1, 1, 16384, 2097152, 4398046511104, 72057594037927936, 28311552, 59373627899904,
    1331200, 357341279027200, 1994129408, 13177532509686071341, 19144971340742656,
    114649923584, 5658449152, 3026418949596699502, 14339461213564502026, 72339069016414976,
    14321446816398262362, 9844868801359176632, 1200684955599940, 1921659016385833728,
    1464027225841409463, 13178530866277646351, 121597189967320544, 357465600145152,
    11259073835288242826, 240410548471636640, 17127689777364790713, 1952874600052300382,
    6480587450483717915, 7791253005434053457]

theorem vbgRlenC_gpow : ∀ d < 33, K.ofBits (vbgRlenC.getD d 0) = gpowK (7 * vbgRecs d) := by
  decide +kernel

theorem vbgRecs_lt : ∀ d < 33, 7 * vbgRecs d < u128Bound := by decide +kernel

/-- `rounds_len[d]`'s word is `g^(7 vbgRecs d)`. -/
theorem vbgRlenC_word {d : ℕ} (hd : d < 33) : word (vbgRlenC.getD d 0) 0 = gen ^ (7 * vbgRecs d) := by
  rw [tb_word_eOfNat]
  show ofK (K.ofBits (vbgRlenC.getD d 0)) = _
  rw [vbgRlenC_gpow d hd, gpowK_eq (vbgRecs_lt d hd),
    ← gen_pow_eq_ofK]

/-- The table `rounds_len` at `g^d`. -/
def vbRlen (d : ℕ) : List Stmt :=
  [.atom (.const (.n (131 + d)) (word (vbgRlenC.getD d 0) 0)),
    .atom (.load (.n (131 + d)) (.n 130) d)]

/-- The table `rounds_len`, its allocation first. -/
def vbR5b : List Stmt := .atom (.hint (.alloc (.n 130) 33)) :: ((List.range 33).map vbRlen).flatten

/-- The buffers sized by the depth (`n_quads`, `rounds_len[depth]`) and the depth's parity. -/
def vbR6 : List Stmt :=
  [.atom (.mul (.n 164) (.n 62) (.n 6)), .atom (.load (.n 165) (.n 164) 0),
    .atom (.const (.n 166) (word 2 0)), .atom (.mul (.n 167) (.n 165) (.n 166)),
    .atom (.mul (.n 168) (.n 167) (.n 167)), .atom (.mul (.n 169) (.n 168) (.n 167)),
    .atom (.mul (.n 170) (.n 169) (.n 169)), .atom (.mul (.n 171) (.n 170) (.n 170)),
    .atom (.mul (.n 172) (.n 171) (.n 167)), .atom (.hint (.allocDyn (.n 173) (.n 172))),
    .atom (.mul (.n 174) (.n 130) (.n 6)), .atom (.load (.n 175) (.n 174) 0),
    .atom (.hint (.allocDyn (.n 176) (.n 175))), .atom (.const (.n 177) (word 4 0)),
    .atom (.mul (.n 178) (.n 165) (.n 177)), .atom (.mul (.n 179) (.n 178) (.n 178)),
    .atom (.mul (.n 180) (.n 179) (.n 179)), .atom (.mul (.n 181) (.n 180) (.n 178)),
    .atom (.mul (.n 182) (.n 181) (.n 181)), .atom (.mul (.n 183) (.n 182) (.n 182)),
    .atom (.mul (.n 184) (.n 183) (.n 183)), .atom (.hint (.allocDyn (.n 185) (.n 184))),
    .atom (.mul (.n 186) (.n 63) (.n 6)), .atom (.load (.n 187) (.n 186) 0),
    .atom (.const (.n 188) (word 1 0)), .atom (.add (.n 189) (.n 187) (.n 188))]

/-- The root-most layer. -/
noncomputable def vbR7 : List Stmt := [.ite (.n 189) rtFour rtTwo]

/-- The layer loop. -/
def vbR8 : List Stmt :=
  [.atom (.const (.n 416) (word 4 0)), .atom (.mul (.n 416) (.n 417) (.n 187)),
    .atom (.const (.n 418) (word 1 0)), .atom (.add (.n 419) (.n 418) (.n 165)),
    .atom (.const (.n 420) (word 1 0)),
    .callIf (.n 419) name% «verify_bus_gkr_loop0» [.n 420, .n 165, .n 417, .n 173, .n 8, .n 176,
        .n 52, .n 187, .n 6, .n 53]]

/-- The last layer record, the point's copy, the values' buffer, the returns. -/
def vbR9 : List Stmt :=
  [.atom (.mul (.n 421) (.n 165) (.n 165)), .atom (.mul (.n 422) (.n 421) (.n 165)),
    .atom (.mul (.n 423) (.n 422) (.n 422)), .atom (.mul (.n 424) (.n 423) (.n 423)),
    .atom (.mul (.n 425) (.n 424) (.n 165)), .atom (.mul (.n 426) (.n 173) (.n 425)),
    .atom (.load (.n 427) (.n 426) 5), .atom (.load (.n 428) (.n 426) 9),
    .atom (.const (.n 429) (word 1 0)), .atom (.add (.n 430) (.n 429) (.n 6)),
    .atom (.const (.n 431) (word 1 0)),
    .callIf (.n 430) name% «verify_bus_gkr_loop1» [.n 431, .n 6, .n 7, .n 428],
    .atom (.hint (.alloc (.n 432) 3)),
    .atom (.load (.n 433) (.n 426) 6), .atom (.load (.n 433) (.n 432) 0),
    .atom (.load (.n 434) (.n 426) 7), .atom (.load (.n 434) (.n 432) 1),
    .atom (.load (.n 435) (.n 426) 8), .atom (.load (.n 435) (.n 432) 2)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (436 + k)) (.n 426) k)) ++
  [.atom (.copy (.n 441) (.n 427)), .atom (.copy (.n 442) (.n 432))]

set_option maxRecDepth 10000 in
theorem vbgPre_eq' :
    vbgPre = vbR1 ++ vbR2 ++ vbR3 ++ vbR4 ++ vbR5 ++ vbR5b ++ vbR6 ++ vbR7 ++ vbR8 ++ vbR9 :=
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

/-- The allocations' pointers: the layer records, the round records, the rows, `k_mod_next`,
`loop_bounds`, `depth_odd`, `rounds_len`, the values' buffer. -/
def vbgW (layers rounds rows kmn bnd odd rlen vals : E) : ℕ → E := fun i ↦
  if i = 173 then layers else if i = 176 then rounds else if i = 185 then rows else
    if i = 53 then kmn else if i = 62 then bnd else if i = 63 then odd else
      if i = 130 then rlen else vals

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
root-most step's words and the layer record it leads to, every layer's words (`LyIter`), the last
layer record with its point at `zeta` and its values in the values' buffer give the relation,
returning the last record's capacity, cursor and the buffer. -/
theorem vbg_body_of {depth : ℕ} (hd1 : 1 ≤ depth) (hd : depth ≤ 32) {cap0 : List E}
    (hcl : cap0.length = 5) {cur zeta tabs layers rounds rows kmn bnd odd rlen vals : E}
    (hrc : (rd (addressOfIndex depth)).isSome = true ∧ (rd (addressOfIndex (32 - depth))).isSome
        = true)
    {x0 x1 : E} (hx0 : LoadHolds rd cur 0 x0) (hx1 : LoadHolds rd cur 1 x1) (hcnt : x1 ≠ 0)
    (hkmn : KModNext rd kmn)
    (hbnd : TbReadsAt rd bnd ((List.range 33).map fun k ↦ gen ^ ((k - 1) / 2)))
    (hodt : TbReadsAt rd odd ((List.range 33).map fun k ↦ gen ^ (k % 2)))
    (hrl : TbReadsAt rd rlen ((List.range 33).map fun k ↦ gen ^ (7 * vbgRecs k)))
    (hodd : depth % 2 = 1 → ∃ D : GkStepD, D.Ok (rootS cap0 x0 x1) (rootSt x0 x1) 1 ∧
      TbReadsAt rd (cur * gen ^ 2) D.xs ∧
      GkSlot rd layers 1 (D.s' (rootS cap0 x0 x1) (rootSt x0 x1) 1)
        (cur * gen ^ 2 * gen ^ D.xs.length) (D.st' (rootS cap0 x0 x1) (rootSt x0 x1) 1)
        (rows * gen ^ 40) 1 1 1)
    (heven : depth % 2 = 0 → ∃ D : GkStepD, D.Ok (rootS cap0 x0 x1) (rootSt x0 x1) 2 ∧
      TbReadsAt rd (cur * gen ^ 2) D.xs ∧
      GkSlot rd layers 2 (D.s' (rootS cap0 x0 x1) (rootSt x0 x1) 2)
        (cur * gen ^ 2 * gen ^ D.xs.length) (D.st' (rootS cap0 x0 x1) (rootSt x0 x1) 2)
        (rows * gen ^ 40) 1 1 gen)
    (hit : ∀ j < (depth - 1) / 2, LyIter rd layers rounds (depth % 2) j)
    {sF : Fs} {curF : E} {stF : GkrState} {rowF posF halfF parF : E}
    (hlast : GkSlot rd layers depth sF curF stF rowF posF halfF parF)
    (hz : TbReadsAt rd zeta stF.point) (hv : TbReadsAt rd vals stF.values) :
    Stmt.HoldsList (coreProgram.Rel rd) rd
        (B1.Val.ofArgs (ev rd (vbgW layers rounds rows kmn bnd odd rlen vals)
          (cap0 ++ [cur, gen ^ depth, zeta, tabs]) vbgEvL)) vbgPre True
        (fun rs => rs = sF.cap ++ [curF, vals]) ∧
      vbgRets.map (B1.Val.ofArgs (ev rd (vbgW layers rounds rows kmn bnd odd rlen vals)
        (cap0 ++ [cur, gen ^ depth, zeta, tabs]) vbgEvL)) = sF.cap ++ [curF, vals] := by
  obtain ⟨a0, a1, a2, a3, a4, rfl⟩ := tb_list5_eq hcl
  simp only [List.cons_append, List.nil_append]
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  set args : List E := [a0, a1, a2, a3, a4, cur, gen ^ depth, zeta, tabs] with hargs
  have hc9 : chk args.length vbgEvL = some c' := hc'
  set W : ℕ → E := vbgW layers rounds rows kmn bnd odd rlen vals with hW
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
  -- the range check
  have c9 : σ (.n 9) = word 4294967296 0 :=
    g 0 (.const (.n 9) (word 4294967296 0)) (by decide +kernel) rfl
  have w32 : word 4294967296 0 = gen ^ 32 := by
    rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num)]
  have grc := g 1 (.rangeCheck (.n 6) (.n 10) (.n 11) (.n 12) (.n 9)) (by decide +kernel) rfl
  have h910 : (V.n 9).idx < (V.n 10).idx := show 9 < 10 by norm_num
  have e10 : σ (.n 10) = gen ^ (32 - depth) := by
    have h3 : σ (.n 10) = σ (.n 9) * (σ (.n 6))⁻¹ := by
      have := grc.2.2
      simpa only [h910, ↓reduceIte] using this
    have hp32 : gen ^ 32 = gen ^ (32 - depth) * gen ^ depth := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    rw [h3, c9, w32, e6, hp32, mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero _), mul_one]
  have hrcH : (Atom.rangeCheck (.n 6) (.n 10) (.n 11) (.n 12) (.n 9)).Holds rd σ := by
    refine holds_of_good grc ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e6]; exact tb_gen_pow_isInK _
    · rw [e6, gen_pow_eq_ofK, tb_addr_ofK, Nat.add_zero]
      exact hrc.1
    · rw [e10]; exact tb_gen_pow_isInK _
    · rw [e10, gen_pow_eq_ofK, tb_addr_ofK, Nat.add_zero]
      exact hrc.2
    · show (if (V.n 9).idx < (V.n 10).idx then σ (.n 6) ≠ 0 else True)
      simp only [h910, ↓reduceIte]
      rw [e6]; exact gen_pow_ne_zero _
  have gq := vb_goodB hG 2 ((List.range 5).map fun k ↦ Stmt.atom (.copy (.n (13 + k)) (.n k)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have q13 : ∀ k < 5, σ (.n (13 + k)) = σ (.n k) := fun k hk =>
    gq _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  have q13a : σ (.n 13) = a0 :=
    (gq _ (List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩)).trans e0
  have q14a : σ (.n 14) = a1 :=
    (gq _ (List.mem_map.mpr ⟨1, List.mem_range.mpr (by omega), rfl⟩)).trans e1
  have q15a : σ (.n 15) = a2 :=
    (gq _ (List.mem_map.mpr ⟨2, List.mem_range.mpr (by omega), rfl⟩)).trans e2
  have q16a : σ (.n 16) = a3 :=
    (gq _ (List.mem_map.mpr ⟨3, List.mem_range.mpr (by omega), rfl⟩)).trans e3
  have q17a : σ (.n 17) = a4 :=
    (gq _ (List.mem_map.mpr ⟨4, List.mem_range.mpr (by omega), rfl⟩)).trans e4
  -- the two roots
  obtain ⟨e18, -, hfs18⟩ := fsNextT_good (C := coreProgram.Rel rd) (kret := fun _ => True)
    (vb_goodB hG 7 (fsNextT (.n 5) 0 18) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (by decide +kernel) (by rw [e5]; exact hx0)
  obtain ⟨e23, -, hfs23⟩ := fsNextT_good (C := coreProgram.Rel rd) (kret := fun _ => True)
    (vb_goodB hG 12 (fsNextT (.n 5) 1 23) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (by decide +kernel) (by rw [e5]; exact hx1)
  obtain ⟨⟨l18, p18⟩, -⟩ := (holds_fsNextT _ _ _ _ _).mp hfs18
  obtain ⟨⟨l23, p23⟩, -⟩ := (holds_fsNextT _ _ _ _ _).mp hfs23
  have q21 : σ (.n 21) = σ (.n 18) := g 10 (.copy (.n 21) (.n 18)) (by decide +kernel) rfl
  have q22 : σ (.n 22) = σ (.n 18) := g 11 (.copy (.n 22) (.n 18)) (by decide +kernel) rfl
  have q26 : σ (.n 26) = σ (.n 23) := g 15 (.copy (.n 26) (.n 23)) (by decide +kernel) rfl
  -- the count asserted nonzero
  have c27 : σ (.n 27) = word 0 0 := g 16 (.const (.n 27) (word 0 0)) (by decide +kernel) rfl
  have a28 : σ (.n 28) = σ (.n 23) + σ (.n 27) :=
    g 17 (.add (.n 28) (.n 23) (.n 27)) (by decide +kernel) rfl
  have i29 : σ (.n 29) = (σ (.n 28))⁻¹ :=
    g 18 (.hint (.inverse (.n 28) (.n 29))) (by decide +kernel) rfl
  have m30 : σ (.n 30) = σ (.n 28) * σ (.n 29) :=
    good_mulS (vb_goodS hG 19 (.atom (.assertNe (.n 28) (.n 29) (.n 30))) (by decide +kernel) rfl)
      (by omega) (by omega)
  have e28 : σ (.n 28) = x1 := by rw [a28, c27, tb_word_zero, add_zero, e23]
  -- the combiner and the claim
  have c31 : σ (.n 31) = word 1 0 := g 20 (.const (.n 31) (word 1 0)) (by decide +kernel) rfl
  have c32 : σ (.n 32) = word 0 0 := g 21 (.const (.n 32) (word 0 0)) (by decide +kernel) rfl
  have c33 : σ (.n 33) = word 0 0 := g 22 (.const (.n 33) (word 0 0)) (by decide +kernel) rfl
  have c34 : σ (.n 34) = word 0 0 := g 23 (.const (.n 34) (word 0 0)) (by decide +kernel) rfl
  have c35 : σ (.n 35) = word 0 0 := g 24 (.const (.n 35) (word 0 0)) (by decide +kernel) rfl
  have z32 : σ (.n 32) = 0 := by rw [c32, tb_word_zero]
  have z33 : σ (.n 33) = 0 := by rw [c33, tb_word_zero]
  have z34 : σ (.n 34) = 0 := by rw [c34, tb_word_zero]
  have z35 : σ (.n 35) = 0 := by rw [c35, tb_word_zero]
  have hins : (([.n 19, .n 20, .n 24, .n 25, .n 32, .n 33, .n 34, .n 35] ++
      (List.range 5).map fun k ↦ V.n (13 + k)) : List V).map σ =
      rateOf (rootS [a0, a1, a2, a3, a4] x0 x1).pend ++ (rootS [a0, a1, a2, a3, a4] x0 x1).cap := by
    have hcapE : ((List.range 5).map fun k ↦ V.n (13 + k)).map σ = [a0, a1, a2, a3, a4] := by
      show [σ (.n 13), σ (.n 14), σ (.n 15), σ (.n 16), σ (.n 17)] = [a0, a1, a2, a3, a4]
      rw [q13a, q14a, q15a, q16a, q17a]
    obtain ⟨e19, e20⟩ := Prod.ext_iff.mp (fsPackT_cells p18)
    obtain ⟨e24, e25⟩ := Prod.ext_iff.mp (fsPackT_cells p23)
    rw [List.map_append, hcapE, rateOf_eq_cells _ (by simp [rootS])]
    norm_num at e19 e20 e24 e25
    simp [rootS, pendCells, e19, e20, e24, e25, e18, e23, z32, z33, z34, z35]
  obtain ⟨k25, hP, hcap⟩ := lyc_keccak (rd := rd) (σ := σ) (S := vbgS) (w := W)
    (g 25 (.keccak ([.n 19, .n 20, .n 24, .n 25, .n 32, .n 33, .n 34, .n 35] ++
      (List.range 5).map fun k ↦ .n (13 + k)) (lyOuts 36) false false) (by decide +kernel) rfl)
  rw [hins] at hP hcap
  have e36 : σ (.n 36) = (rootS [a0, a1, a2, a3, a4] x0 x1).squeeze.1 :=
    challengeT_value (s0 := .n 36) (b := 36) rfl (hP 0 (by omega))
  have m49 := good_mul (g 26 (.mul (.n 49) (.n 36) (.n 26)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have a50 : σ (.n 50) = σ (.n 22) + σ (.n 49) :=
    g 27 (.add (.n 50) (.n 22) (.n 49)) (by decide +kernel) rfl
  have m51 := good_mul (g 28 (.mul (.n 51) (.n 36) (.n 50)) (by decide +kernel) rfl) (by omega)
    (by omega)
  have a52 : σ (.n 52) = σ (.n 21) + σ (.n 51) :=
    g 29 (.add (.n 52) (.n 21) (.n 51)) (by decide +kernel) rfl
  have e52 : σ (.n 52) = polyEval (rootSt x0 x1).values (rootS [a0, a1, a2, a3, a4] x0 x1).squeeze.1 := by
    rw [a52, m51, a50, m49, q21, q22, q26, e18, e23, ← e36]
    simp only [rootSt, polyEval, List.foldr]
    ring
  have hcapP : (lyCap 36).map σ = capOf (rootS [a0, a1, a2, a3, a4] x0 x1).perm := hcap
  have e53 : σ (.n 53) = kmn := by
    have h : σ (.n 53) = W 53 := g 30 (.hint (.alloc (.n 53) 8)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e62 : σ (.n 62) = bnd := by
    have h : σ (.n 62) = W 62 := g 47 (.hint (.alloc (.n 62) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e63 : σ (.n 63) = odd := by
    have h : σ (.n 63) = W 63 := g 48 (.hint (.alloc (.n 63) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e130 : σ (.n 130) = rlen := by
    have h : σ (.n 130) = W 130 := g 181 (.hint (.alloc (.n 130) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  -- the tables
  have gK := vb_goodB hG 31 ((List.range 4).map vbKmn).flatten (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have KM : ∀ r < 4, ∀ s ∈ vbKmn r, SHolds (coreProgram.Rel rd) rd σ s := by
    intro r hr
    have mem : ∀ t ∈ vbKmn r, t ∈ ((List.range 4).map vbKmn).flatten := fun t ht =>
      List.mem_flatten.mpr ⟨vbKmn r, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩, ht⟩
    have c0 : σ (.n (54 + 2 * r)) = word (2 ^ ((r + 1) % 4)) 0 :=
      gK (.atom (.const (.n (54 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0))) (mem _ (by simp [vbKmn]))
    have c1 : σ (.n (55 + 2 * r)) = word (2 ^ ((r + 1) / 4)) 0 :=
      gK (.atom (.const (.n (55 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0))) (mem _ (by simp [vbKmn]))
    obtain ⟨k4, k0⟩ := hkmn r hr
    simp only [vbKmn, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    exact ⟨c0, show LoadHolds rd (σ (.n 53)) r (σ (.n (54 + 2 * r))) by
        rw [e53, c0, tb_word_two_pow (by omega)]; exact k0, c1,
      show LoadHolds rd (σ (.n 53)) (4 + r) (σ (.n (55 + 2 * r))) by
        rw [e53, c1, tb_word_two_pow (by omega)]; exact k4⟩
  have gT := vb_goodB hG 49 vbR5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hbk : ∀ k < 33, LoadHolds rd bnd k (gen ^ ((k - 1) / 2)) := fun k hk => by
    have := hbnd k (by simpa using hk)
    simpa using this
  have hok : ∀ k < 33, LoadHolds rd odd k (gen ^ (k % 2)) := fun k hk => by
    have := hodt k (by simpa using hk)
    simpa using this
  have hrk : ∀ k < 33, LoadHolds rd rlen k (gen ^ (7 * vbgRecs k)) := fun k hk => by
    have := hrl k (by simpa using hk)
    simpa using this
  have TB : ∀ k < 33, ∀ s ∈ vbTab k, SHolds (coreProgram.Rel rd) rd σ s := by
    intro k hk
    have mem : ∀ t ∈ vbTab k, t ∈ vbR5 := fun t ht =>
      List.mem_flatten.mpr ⟨vbTab k, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ht⟩
    have c0 : σ (.n (64 + 2 * k)) = word (2 ^ ((k - 1) / 2)) 0 :=
      gT (.atom (.const (.n (64 + 2 * k)) (word (2 ^ ((k - 1) / 2)) 0))) (mem _ (by simp [vbTab]))
    have c1 : σ (.n (65 + 2 * k)) = word (2 ^ (k % 2)) 0 :=
      gT (.atom (.const (.n (65 + 2 * k)) (word (2 ^ (k % 2)) 0))) (mem _ (by simp [vbTab]))
    simp only [vbTab, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    exact ⟨c0, show LoadHolds rd (σ (.n 62)) k (σ (.n (64 + 2 * k))) by
        rw [e62, c0, tb_word_two_pow (by omega)]; exact hbk k hk, c1,
      show LoadHolds rd (σ (.n 63)) k (σ (.n (65 + 2 * k))) by
        rw [e63, c1, tb_word_two_pow (by omega)]; exact hok k hk⟩
  have gR := vb_goodB hG 182 ((List.range 33).map vbRlen).flatten (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have RL : ∀ k < 33, ∀ s ∈ vbRlen k, SHolds (coreProgram.Rel rd) rd σ s := by
    intro k hk
    have mem : ∀ t ∈ vbRlen k, t ∈ ((List.range 33).map vbRlen).flatten := fun t ht =>
      List.mem_flatten.mpr ⟨vbRlen k, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ht⟩
    have c0 : σ (.n (131 + k)) = word (vbgRlenC.getD k 0) 0 :=
      gR (.atom (.const (.n (131 + k)) (word (vbgRlenC.getD k 0) 0))) (mem _ (by simp [vbRlen]))
    simp only [vbRlen, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    exact ⟨c0, show LoadHolds rd (σ (.n 130)) k (σ (.n (131 + k))) by
        rw [e130, c0, vbgRlenC_word hk]; exact hrk k hk⟩
  -- the buffers sized by the depth, the depth's parity
  have m164 := good_mul (g 248 (.mul (.n 164) (.n 62) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  obtain ⟨e165, l165⟩ := good_read (g 249 (.load (.n 165) (.n 164) 0) (by decide +kernel) rfl)
    (by decide +kernel) (show LoadHolds rd (σ (.n 164)) 0 (gen ^ m) by
      rw [m164, e62, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hbk depth (by omega))
  have c166 : σ (.n 166) = word 2 0 := g 250 (.const (.n 166) (word 2 0)) (by decide +kernel) rfl
  have m167 := good_mul (g 251 (.mul (.n 167) (.n 165) (.n 166)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m168 := good_mul (g 252 (.mul (.n 168) (.n 167) (.n 167)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m169 := good_mul (g 253 (.mul (.n 169) (.n 168) (.n 167)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m170 := good_mul (g 254 (.mul (.n 170) (.n 169) (.n 169)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m171 := good_mul (g 255 (.mul (.n 171) (.n 170) (.n 170)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m172 := good_mul (g 256 (.mul (.n 172) (.n 171) (.n 167)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e173 : σ (.n 173) = layers := by
    have h : σ (.n 173) = W 173 :=
      g 257 (.hint (.allocDyn (.n 173) (.n 172))) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have m174 := good_mul (g 258 (.mul (.n 174) (.n 130) (.n 6)) (by decide +kernel) rfl)
    (by omega) (by omega)
  obtain ⟨-, l175⟩ := good_read (g 259 (.load (.n 175) (.n 174) 0) (by decide +kernel) rfl)
    (by decide +kernel) (show LoadHolds rd (σ (.n 174)) 0 (gen ^ (7 * vbgRecs depth)) by
      rw [m174, e130, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hrk depth (by omega))
  have e176 : σ (.n 176) = rounds := by
    have h : σ (.n 176) = W 176 :=
      g 260 (.hint (.allocDyn (.n 176) (.n 175))) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have c177 : σ (.n 177) = word 4 0 := g 261 (.const (.n 177) (word 4 0)) (by decide +kernel) rfl
  have m178 := good_mul (g 262 (.mul (.n 178) (.n 165) (.n 177)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m179 := good_mul (g 263 (.mul (.n 179) (.n 178) (.n 178)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m180 := good_mul (g 264 (.mul (.n 180) (.n 179) (.n 179)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m181 := good_mul (g 265 (.mul (.n 181) (.n 180) (.n 178)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m182 := good_mul (g 266 (.mul (.n 182) (.n 181) (.n 181)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m183 := good_mul (g 267 (.mul (.n 183) (.n 182) (.n 182)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m184 := good_mul (g 268 (.mul (.n 184) (.n 183) (.n 183)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e185 : σ (.n 185) = rows := by
    have h : σ (.n 185) = W 185 :=
      g 269 (.hint (.allocDyn (.n 185) (.n 184))) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have m186 := good_mul (g 270 (.mul (.n 186) (.n 63) (.n 6)) (by decide +kernel) rfl) (by omega)
    (by omega)
  obtain ⟨e187, l187⟩ := good_read (g 271 (.load (.n 187) (.n 186) 0) (by decide +kernel) rfl)
    (by decide +kernel) (show LoadHolds rd (σ (.n 186)) 0 (gen ^ sh) by
      rw [m186, e63, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hok depth (by omega))
  have c188 : σ (.n 188) = word 1 0 := g 272 (.const (.n 188) (word 1 0)) (by decide +kernel) rfl
  have a189 : σ (.n 189) = σ (.n 187) + σ (.n 188) :=
    g 273 (.add (.n 189) (.n 187) (.n 188)) (by decide +kernel) rfl
  -- the root-most layer
  have R7 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR7 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    simp only [vbR7, Stmt.HoldsList]
    rw [tb_holds_ite_noRet _ _ _ rtFour_noRet rtTwo_noRet]
    refine ⟨⟨?_, fun h0 => ?_, fun hne => ?_⟩, trivial⟩
    · rw [a189, e187, c188, tb_word_one]
      exact tb_isInK_add (tb_gen_pow_isInK _) tb_isInK_one
    · have hsh0 : sh = 0 := by
        by_contra h
        rw [a189, e187, c188, tb_word_one, show sh = 1 by omega] at h0
        have := gen_pow_inj (a := 1) (b := 0) (by omega) (by omega)
          ((e_add_eq_zero_iff.mp h0).trans (pow_zero gen).symm)
        omega
      obtain ⟨D, hD, hxD, hS'⟩ := heven hsh0
      exact rtc_four hG rfl e36 e52 hcapP z32 z33 z34 z35 hD (by rw [e5]; exact hxD)
        (by rw [e173, e5, e185]; exact hS')
    · have hsh1 : sh = 1 := by
        by_contra h
        rw [a189, e187, c188, tb_word_one, show sh = 0 by omega, pow_zero, e_add_self] at hne
        exact hne rfl
      obtain ⟨D, hD, hxD, hS'⟩ := hodd hsh1
      exact rtc_two hG rfl e36 e52 hcapP z32 z33 z34 z35 hD (by rw [e5]; exact hxD)
        (by rw [e173, e5, e185]; exact hS')
  -- the layer loop
  have c416 : σ (.n 416) = word 4 0 := g 275 (.const (.n 416) (word 4 0)) (by decide +kernel) rfl
  have d417 : σ (.n 417) = σ (.n 416) * (σ (.n 187))⁻¹ := by
    have h := g 276 (.mul (.n 416) (.n 417) (.n 187)) (by decide +kernel) rfl
    have hn : ¬ ((V.n 417).idx < (V.n 416).idx ∧ (V.n 187).idx < (V.n 416).idx) := by
      show ¬ (417 < 416 ∧ 187 < 416); omega
    simpa only [Good, hn, ↓reduceIte] using h
  have e417 : σ (.n 417) = gen ^ (2 - sh) := by
    rw [d417, c416, tb_word_four, e187]
    have hs : sh ≤ 2 := by omega
    rw [show (gen : E) ^ 2 = gen ^ (2 - sh) * gen ^ sh by rw [← pow_add, Nat.sub_add_cancel hs],
      mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero _), mul_one]
  have c418 : σ (.n 418) = word 1 0 := g 277 (.const (.n 418) (word 1 0)) (by decide +kernel) rfl
  have a419 : σ (.n 419) = σ (.n 418) + σ (.n 165) :=
    g 278 (.add (.n 419) (.n 418) (.n 165)) (by decide +kernel) rfl
  have c420 : σ (.n 420) = word 1 0 := g 279 (.const (.n 420) (word 1 0)) (by decide +kernel) rfl
  -- the last layer record, the point's copy, the values' buffer
  obtain ⟨hclF, hcapF, -, hcurF, hvlF, hvalF, hrowF, hplF, hptF, -, -, -⟩ := hlast
  have m421 := good_mul (g 281 (.mul (.n 421) (.n 165) (.n 165)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m422 := good_mul (g 282 (.mul (.n 422) (.n 421) (.n 165)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m423 := good_mul (g 283 (.mul (.n 423) (.n 422) (.n 422)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m424 := good_mul (g 284 (.mul (.n 424) (.n 423) (.n 423)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m425 := good_mul (g 285 (.mul (.n 425) (.n 424) (.n 165)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m426 := good_mul (g 286 (.mul (.n 426) (.n 173) (.n 425)) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e426 : σ (.n 426) = layers * gen ^ (13 * m) := by
    rw [m426, m425, m424, m423, m422, m421, e165, e173]
    ring
  have ld : ∀ k v, LoadHolds rd layers (13 * ((depth - 1) / 2) + k) v →
      LoadHolds rd (σ (.n 426)) k v :=
    fun k v h => by rw [e426, tb_loadHolds_mul_gen_pow]; exact h
  obtain ⟨e427, l427⟩ := good_read (g 287 (.load (.n 427) (.n 426) 5) (by decide +kernel) rfl)
    (by decide +kernel) (ld 5 _ hcurF)
  obtain ⟨e428, l428⟩ := good_read (g 288 (.load (.n 428) (.n 426) 9) (by decide +kernel) rfl)
    (by decide +kernel) (ld 9 _ hrowF)
  have c429 : σ (.n 429) = word 1 0 := g 289 (.const (.n 429) (word 1 0)) (by decide +kernel) rfl
  have a430 : σ (.n 430) = σ (.n 429) + σ (.n 6) :=
    g 290 (.add (.n 430) (.n 429) (.n 6)) (by decide +kernel) rfl
  have c431 : σ (.n 431) = word 1 0 := g 291 (.const (.n 431) (word 1 0)) (by decide +kernel) rfl
  have e432 : σ (.n 432) = vals := by
    have h : σ (.n 432) = W 432 := g 293 (.hint (.alloc (.n 432) 3)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  obtain ⟨v0, v1, v2, hv3⟩ := tb_list3_eq hvlF
  have hvk : ∀ k < 3, LoadHolds rd vals k (stF.values.getD k 0) := fun k hk => by
    have := hv k (by rw [hvlF]; exact hk)
    rwa [← List.getD_eq_getElem _ 0] at this
  obtain ⟨e433, l433⟩ := good_read (g 294 (.load (.n 433) (.n 426) 6) (by decide +kernel) rfl)
    (by decide +kernel) (ld 6 _ (hvalF 0 (by omega)))
  obtain ⟨e434, l434⟩ := good_read (g 296 (.load (.n 434) (.n 426) 7) (by decide +kernel) rfl)
    (by decide +kernel) (ld 7 _ (hvalF 1 (by omega)))
  obtain ⟨e435, l435⟩ := good_read (g 298 (.load (.n 435) (.n 426) 8) (by decide +kernel) rfl)
    (by decide +kernel) (ld 8 _ (hvalF 2 (by omega)))
  have gC := vb_goodB hG 300 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (436 + k)) (.n 426) k)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have kC : ∀ k < 5, some (436 + k, 426, k) ∉ vbgS.map loadKey := by decide +kernel
  have rC : ∀ k < 5, σ (.n (436 + k)) = sF.cap.getD k 0 ∧
      LoadHolds rd (σ (.n 426)) k (σ (.n (436 + k))) := fun k hk =>
    good_readS (gC _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (kC k hk)
      (ld k _ (hcapF k hk))
  have q441 : σ (.n 441) = σ (.n 427) := g 305 (.copy (.n 441) (.n 427)) (by decide +kernel) rfl
  have q442 : σ (.n 442) = σ (.n 432) := g 306 (.copy (.n 442) (.n 432)) (by decide +kernel) rfl
  -- the regions
  have R1 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR1 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR1, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
      List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
    exact ⟨c9, hrcH, fun k hk => q13 k hk⟩
  have R2 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR2 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR2, fsNextT, fsPackT, List.forall_mem_append, List.forall_mem_cons,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
    exact ⟨l18, p18.1, p18.2, q21, q22, l23, p23.1, p23.2, q26⟩
  have R3 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR3 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR3, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, and_assoc, keccakA]
    exact ⟨c27, a28, trivial,
      show σ (.n 30) = σ (.n 28) * σ (.n 29) ∧ σ (.n 30) = 1 from
        ⟨m30, by rw [m30, i29, mul_inv_cancel₀ (by rw [e28]; exact hcnt)]⟩,
      c31, c32, c33, c34, c35, k25, m49, a50, m51, a52, trivial⟩
  have R4 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR4 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR4, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨forall_flatten_range KM, trivial, trivial⟩
  have R5 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR5 True
      (fun rs => rs = sF.cap ++ [curF, vals]) :=
    holdsList_straightN _ (by decide +kernel) (forall_flatten_range TB) trivial
  have R5b : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR5b True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR5b, List.forall_mem_cons]
    exact ⟨trivial, forall_flatten_range RL⟩
  have R6 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR6 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR6, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    exact ⟨m164, l165, c166, m167, m168, m169, m170, m171, m172, trivial, m174, l175, trivial, c177,
      m178, m179, m180, m181, m182, m183, m184, trivial, m186, l187, c188, a189⟩
  have R8 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR8 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR8, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    refine ⟨c416, show σ (.n 416) = σ (.n 417) * σ (.n 187) by
        rw [d417, mul_assoc, inv_mul_cancel₀ (by rw [e187]; exact gen_pow_ne_zero _), mul_one],
      c418, a419, c420, ⟨?_, fun hne => ?_⟩⟩
    · rw [a419, c418, e165, tb_word_one]
      exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _)
    · have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [a419, c418, e165, tb_word_one, h0, pow_zero, e_add_self] at hne
          exact absurd rfl hne
        · exact h0
      show coreProgram.Rel rd name% «verify_bus_gkr_loop0» (List.map σ [.n 420, .n 165, .n 417,
          .n 173, .n 8, .n 176, .n 52, .n 187, .n 6, .n 53]) []
      simp only [List.map_cons, List.map_nil]
      rw [c420, tb_word_one, e165, e417, e173, e8, e176, e187, e6, e53]
      exact ly_complete hm0 (by omega) (by omega) hkmn hit
  have R9 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR9 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR9, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
      List.mem_range, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, and_assoc]
    refine ⟨m421, m422, m423, m424, m425, m426, l427, l428, c429, a430, c431, ⟨?_, fun hne => ?_⟩,
      trivial, l433, ?_, l434, ?_, l435, ?_, fun k hk => (rC k hk).2, q441, q442⟩
    · rw [a430, c429, tb_word_one, e6]
      exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _)
    · show coreProgram.Rel rd name% «verify_bus_gkr_loop1» (List.map σ [.n 431, .n 6, .n 7,
        .n 428]) []
      simp only [List.map_cons, List.map_nil]
      rw [c431, tb_word_one, e6, e7, e428]
      exact l8_complete (by omega) (by omega) hplF hptF hz
    · show LoadHolds rd (σ (.n 432)) 0 (σ (.n 433))
      rw [e432, e433]; exact hvk 0 (by omega)
    · show LoadHolds rd (σ (.n 432)) 1 (σ (.n 434))
      rw [e432, e434]; exact hvk 1 (by omega)
    · show LoadHolds rd (σ (.n 432)) 2 (σ (.n 435))
      rw [e432, e435]; exact hvk 2 (by omega)
  obtain ⟨f0, f1, f2, f3, f4, hf5⟩ := tb_list5_eq hclF
  refine ⟨?_, ?_⟩
  · rw [vbgPre_eq']
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR4 ++ vbR5 ++ vbR5b ++ vbR6 ++
      vbR7 ++ vbR8) (by decide +kernel)).mpr ⟨?_, R9⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR4 ++ vbR5 ++ vbR5b ++ vbR6 ++
      vbR7) (by decide +kernel)).mpr ⟨?_, R8⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR4 ++ vbR5 ++ vbR5b ++ vbR6)
      (by decide +kernel)).mpr ⟨?_, R7⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR4 ++ vbR5 ++ vbR5b)
      (by decide +kernel)).mpr ⟨?_, R6⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR4 ++ vbR5)
      (by decide +kernel)).mpr ⟨?_, R5b⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3 ++ vbR4)
      (by decide +kernel)).mpr ⟨?_, R5⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2 ++ vbR3) (by decide +kernel)).mpr
      ⟨?_, R4⟩
    refine (tb_holdsList_append_noRet (A := vbR1 ++ vbR2) (by decide +kernel)).mpr ⟨?_, R3⟩
    exact (tb_holdsList_append_noRet (A := vbR1) (by decide +kernel)).mpr ⟨R1, R2⟩
  · have hc : ∀ k < 5, σ (.n (436 + k)) = sF.cap.getD k 0 := fun k hk => (rC k hk).1
    rw [hf5] at hc
    have h0 := hc 0 (by omega)
    have h1 := hc 1 (by omega)
    have h2 := hc 2 (by omega)
    have h3 := hc 3 (by omega)
    have h4 := hc 4 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3 h4
    show [σ (.n 436), σ (.n 437), σ (.n 438), σ (.n 439), σ (.n 440), σ (.n 441), σ (.n 442)] =
      sF.cap ++ [curF, vals]
    rw [hf5, h0, h1, h2, h3, h4, q441, q442, e427, e432]
    rfl

end Body

end
end LeanVM.Guest.B1.Tables
