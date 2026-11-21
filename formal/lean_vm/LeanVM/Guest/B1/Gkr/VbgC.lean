/-
  LeanVM.Guest.B1.Gkr.VbgC

  `verify_bus_gkr`'s body, completely: on a memory holding the tables, the root-most step's and
  the layers' words, the last slot and the values' buffer, its honest valuation satisfies the
  body and returns the last slot's capacity, cursor and the values' buffer.
-/

module

public import LeanVM.Guest.B1.Gkr.VbgOdd
public import LeanVM.Guest.B1.Gkr.Loop8Complete
public import LeanVM.Guest.B1.Gkr.GlCIter
public import LeanVM.Guest.B1.Selectors.LayoutBasic
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_bus_gkr»

/-!
# `verify_bus_gkr`'s body, completely

`vbg_body_of`: the body evaluated forward (`vbgEvL`, the allocations answered by the buffers'
pointers, `vbgW`), its regions `vbR1 .. vbR9`: the range check of `g^depth` (the memory defined
at `g^depth` and `g^(32 - depth)`), the two roots read, the count asserted nonzero and the
combiner, the tables `depth_odd`, `four_bounds` and `four_rem`, the depth's parity, `start_g`,
the root-most layer (`rtc_two` at an odd depth, `rtc_four` at an even one, on the arms renamed by
`rtSh`), the dispatch to `gkr_layers__L{o}` (`gls_complete`, each layer by `glc_lay`), the last
slot and row, the point's copy (`l8_complete`) and the values' buffer.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The regions of the body -/

/-- The depth's powers, the allocations, the range check, the capacity's copies. -/
def vbR1 : List Stmt :=
  [.atom (.const (.n (val% «verify_bus_gkr» "layers~0")) (word 4 0)), .atom (.mul (.n (val% «verify_bus_gkr» "layers~1")) (.n (val% «verify_bus_gkr» "g_bus_mu")) (.n (val% «verify_bus_gkr» "layers~0"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "layers~2")) (.n (val% «verify_bus_gkr» "layers~1")) (.n (val% «verify_bus_gkr» "layers~1"))), .atom (.mul (.n (val% «verify_bus_gkr» "layers~3")) (.n (val% «verify_bus_gkr» "layers~2")) (.n (val% «verify_bus_gkr» "layers~2"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "layers~4")) (.n (val% «verify_bus_gkr» "layers~3")) (.n (val% «verify_bus_gkr» "layers~1"))), .atom (.mul (.n (val% «verify_bus_gkr» "layers~5")) (.n (val% «verify_bus_gkr» "layers~4")) (.n (val% «verify_bus_gkr» "layers~4"))),
    .atom (.hint (.allocDyn (.n (val% «verify_bus_gkr» "layers")) (.n (val% «verify_bus_gkr» "layers~5")))),
    .atom (.hint (.alloc (.n (val% «verify_bus_gkr» "rounds")) 6034)), .atom (.hint (.alloc (.n (val% «verify_bus_gkr» "gkr_pts")) 1640)),
    .atom (.const (.n (val% «verify_bus_gkr» "s3#0")) (word 4294967296 0)),
    .atom (.rangeCheck (.n (val% «verify_bus_gkr» "g_bus_mu")) (.n (val% «verify_bus_gkr» "s3#1")) (.n (val% «verify_bus_gkr» "s3#2")) (.n (val% «verify_bus_gkr» "s3#3")) (.n (val% «verify_bus_gkr» "s3#0")))] ++
  (List.range 5).map (fun k ↦ .atom (.copy (.n ((val% «verify_bus_gkr» "sp[0]") + k)) (.n k)))

/-- The two roots. -/
def vbR2 : List Stmt :=
  fsNextT (.n (val% «verify_bus_gkr» "cursor@1")) 0 (val% «verify_bus_gkr» "x@1") ++ [.atom (.copy (.n (val% «verify_bus_gkr» "vals[0]")) (.n (val% «verify_bus_gkr» "x@1"))), .atom (.copy (.n (val% «verify_bus_gkr» "vals[1]")) (.n (val% «verify_bus_gkr» "x@1")))] ++
  fsNextT (.n (val% «verify_bus_gkr» "cursor@1")) 1 (val% «verify_bus_gkr» "x@2") ++ [.atom (.copy (.n (val% «verify_bus_gkr» "vals[2]")) (.n (val% «verify_bus_gkr» "x@2")))]

/-- The count asserted nonzero, the combiner, the claim, . -/
def vbR3 : List Stmt :=
  [.atom (.const (.n (val% «verify_bus_gkr» "s12#0")) (word 0 0)), .atom (.add (.n (val% «verify_bus_gkr» "s12#1")) (.n (val% «verify_bus_gkr» "x@2")) (.n (val% «verify_bus_gkr» "s12#0"))),
    .atom (.hint (.inverse (.n (val% «verify_bus_gkr» "s12#1")) (.n (val% «verify_bus_gkr» "s12#2")))), .atom (.assertNe (.n (val% «verify_bus_gkr» "s12#1")) (.n (val% «verify_bus_gkr» "s12#2")) (.n (val% «verify_bus_gkr» "s12#3"))),
    .atom (.const (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0")) (word 1 0)), .atom (.const (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]")) (word 0 0)),
    .atom (.const (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]")) (word 0 0)), .atom (.const (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]")) (word 0 0)),
    .atom (.const (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")) (word 0 0)),
    keccakA ([.n (val% «verify_bus_gkr» "rate[0]@1"), .n (val% «verify_bus_gkr» "rate[1]@1"), .n (val% «verify_bus_gkr» "rate[2]@1"), .n (val% «verify_bus_gkr» "rate[3]@1"), .n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] ++
      (List.range 5).map fun k ↦ .n ((val% «verify_bus_gkr» "sp[0]") + k)) (lyOuts (val% «verify_bus_gkr» "nxt[0]@1"))] ++
  [.atom (.mul (.n (val% «verify_bus_gkr» "claim@1~0")) (.n (val% «verify_bus_gkr» "nxt[0]@1")) (.n (val% «verify_bus_gkr» "vals[2]"))), .atom (.add (.n (val% «verify_bus_gkr» "claim@1")) (.n (val% «verify_bus_gkr» "vals[1]")) (.n (val% «verify_bus_gkr» "claim@1~0"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "claim@2~0")) (.n (val% «verify_bus_gkr» "nxt[0]@1")) (.n (val% «verify_bus_gkr» "claim@1"))), .atom (.add (.n (val% «verify_bus_gkr» "claim@2")) (.n (val% «verify_bus_gkr» "vals[0]")) (.n (val% «verify_bus_gkr» "claim@2~0")))]

/-- The tables' first entries. -/
def vbT0 : List Stmt :=
  [.atom (.hint (.alloc (.n (val% «verify_bus_gkr» "depth_odd")) 33)), .atom (.const (.n (val% «verify_bus_gkr» "s16#0")) (word 1 0)),
    .atom (.load (.n (val% «verify_bus_gkr» "s16#0")) (.n (val% «verify_bus_gkr» "depth_odd")) 0), .atom (.hint (.alloc (.n (val% «verify_bus_gkr» "four_bounds")) 33)),
    .atom (.hint (.alloc (.n (val% «verify_bus_gkr» "four_rem")) 33)), .atom (.const (.n (val% «verify_bus_gkr» "s19#0")) (word 1 0)),
    .atom (.load (.n (val% «verify_bus_gkr» "s19#0")) (.n (val% «verify_bus_gkr» "four_bounds")) 0), .atom (.const (.n (val% «verify_bus_gkr» "s20#0")) (word 1 0)),
    .atom (.load (.n (val% «verify_bus_gkr» "s20#0")) (.n (val% «verify_bus_gkr» "four_rem")) 0)]

/-- The tables at `depth = d + 1`: `depth_odd = g^(depth % 2)`, `four_bounds = g^((depth - 1)/8)`,
`four_rem = g^(((depth - 1)/2) % 4)`. -/
def vbTab (d : ℕ) : List Stmt :=
  [.atom (.const (.n (69 + 3 * d)) (word (2 ^ ((d + 1) % 2)) 0)),
    .atom (.load (.n (69 + 3 * d)) (.n (val% «verify_bus_gkr» "depth_odd")) (d + 1)),
    .atom (.const (.n (70 + 3 * d)) (word (2 ^ (d / 8)) 0)),
    .atom (.load (.n (70 + 3 * d)) (.n (val% «verify_bus_gkr» "four_bounds")) (d + 1)),
    .atom (.const (.n (71 + 3 * d)) (word (2 ^ ((d / 2) % 4)) 0)),
    .atom (.load (.n (71 + 3 * d)) (.n (val% «verify_bus_gkr» "four_rem")) (d + 1))]

/-- The tables. -/
def vbR5 : List Stmt := vbT0 ++ ((List.range 32).map vbTab).flatten

/-- The depth's parity, `start_g` and the root-most slot. -/
def vbR6 : List Stmt :=
  [.atom (.mul (.n (val% «verify_bus_gkr» "odd_g~0")) (.n (val% «verify_bus_gkr» "depth_odd")) (.n (val% «verify_bus_gkr» "g_bus_mu"))), .atom (.load (.n (val% «verify_bus_gkr» "odd_g")) (.n (val% «verify_bus_gkr» "odd_g~0")) 0),
    .atom (.const (.n (val% «verify_bus_gkr» "start_g~0")) (word 4 0)), .atom (.mul (.n (val% «verify_bus_gkr» "start_g~0")) (.n (val% «verify_bus_gkr» "start_g")) (.n (val% «verify_bus_gkr» "odd_g"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "nxt~0")) (.n (val% «verify_bus_gkr» "start_g")) (.n (val% «verify_bus_gkr» "start_g"))), .atom (.mul (.n (val% «verify_bus_gkr» "nxt~1")) (.n (val% «verify_bus_gkr» "nxt~0")) (.n (val% «verify_bus_gkr» "nxt~0"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "nxt~2")) (.n (val% «verify_bus_gkr» "nxt~1")) (.n (val% «verify_bus_gkr» "start_g"))), .atom (.mul (.n (val% «verify_bus_gkr» "nxt~3")) (.n (val% «verify_bus_gkr» "nxt~2")) (.n (val% «verify_bus_gkr» "nxt~2"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "nxt")) (.n (val% «verify_bus_gkr» "layers")) (.n (val% «verify_bus_gkr» "nxt~3"))),
    .atom (.const (.n (val% «verify_bus_gkr» "s26#0")) (word 1 0)), .atom (.add (.n (val% «verify_bus_gkr» "s26#1")) (.n (val% «verify_bus_gkr» "odd_g")) (.n (val% «verify_bus_gkr» "s26#0")))]

/-- The root-most layer. -/
noncomputable def vbR7 : List Stmt :=
  [.ite (.n (val% «verify_bus_gkr» "s26#1")) (Stmt.renameList rtSh rtFour) (Stmt.renameList rtSh rtTwo)]

/-- The radix-four layers: `n_four`, `rem_g`, `n_pairs`, the dispatch to `gkr_layers__L{o}`. -/
def vbR8 : List Stmt :=
  [.atom (.mul (.n (val% «verify_bus_gkr» "n_four~0")) (.n (val% «verify_bus_gkr» "four_bounds")) (.n (val% «verify_bus_gkr» "g_bus_mu"))), .atom (.load (.n (val% «verify_bus_gkr» "n_four")) (.n (val% «verify_bus_gkr» "n_four~0")) 0),
    .atom (.mul (.n (val% «verify_bus_gkr» "rem_g~0")) (.n (val% «verify_bus_gkr» "four_rem")) (.n (val% «verify_bus_gkr» "g_bus_mu"))), .atom (.load (.n (val% «verify_bus_gkr» "rem_g")) (.n (val% «verify_bus_gkr» "rem_g~0")) 0),
    .atom (.mul (.n (val% «verify_bus_gkr» "n_pairs~0")) (.n (val% «verify_bus_gkr» "n_four")) (.n (val% «verify_bus_gkr» "n_four"))), .atom (.mul (.n (val% «verify_bus_gkr» "n_pairs~1")) (.n (val% «verify_bus_gkr» "n_pairs~0")) (.n (val% «verify_bus_gkr» "n_pairs~0"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "n_pairs")) (.n (val% «verify_bus_gkr» "n_pairs~1")) (.n (val% «verify_bus_gkr» "rem_g"))),
    .dispatch (.n (val% «verify_bus_gkr» "odd_g")) [glcLsN 0, glcLsN 1] [.n (val% «verify_bus_gkr» "layers"), .n (val% «verify_bus_gkr» "rounds"), .n (val% «verify_bus_gkr» "gkr_pts"), .n (val% «verify_bus_gkr» "n_four"), .n (val% «verify_bus_gkr» "rem_g"), .n (val% «verify_bus_gkr» "start_g"), .n (val% «verify_bus_gkr» "g_bus_mu"),
      .n (val% «verify_bus_gkr» "tabs"), .n (val% «verify_bus_gkr» "stream")] [.n (val% «verify_bus_gkr» "done")]]

/-- The last slot, the last row, the point's copy, the values' buffer, the returns. -/
def vbR9 : List Stmt :=
  [.atom (.mul (.n (val% «verify_bus_gkr» "last~0")) (.n (val% «verify_bus_gkr» "n_pairs")) (.n (val% «verify_bus_gkr» "n_pairs"))), .atom (.mul (.n (val% «verify_bus_gkr» "last~1")) (.n (val% «verify_bus_gkr» "last~0")) (.n (val% «verify_bus_gkr» "start_g"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "last~2")) (.n (val% «verify_bus_gkr» "last~1")) (.n (val% «verify_bus_gkr» "last~1"))), .atom (.mul (.n (val% «verify_bus_gkr» "last~3")) (.n (val% «verify_bus_gkr» "last~2")) (.n (val% «verify_bus_gkr» "last~2"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "last~4")) (.n (val% «verify_bus_gkr» "last~3")) (.n (val% «verify_bus_gkr» "last~1"))), .atom (.mul (.n (val% «verify_bus_gkr» "last~5")) (.n (val% «verify_bus_gkr» "last~4")) (.n (val% «verify_bus_gkr» "last~4"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "last")) (.n (val% «verify_bus_gkr» "layers")) (.n (val% «verify_bus_gkr» "last~5"))), .atom (.load (.n (val% «verify_bus_gkr» "cursor@2")) (.n (val% «verify_bus_gkr» "last")) 5),
    .atom (.const (.n (val% «verify_bus_gkr» "final_point_row~0")) (word 2 0)), .atom (.mul (.n (val% «verify_bus_gkr» "final_point_row~1")) (.n (val% «verify_bus_gkr» "n_pairs")) (.n (val% «verify_bus_gkr» "final_point_row~0"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "final_point_row~2")) (.n (val% «verify_bus_gkr» "final_point_row~1")) (.n (val% «verify_bus_gkr» "final_point_row~1"))), .atom (.mul (.n (val% «verify_bus_gkr» "final_point_row~3")) (.n (val% «verify_bus_gkr» "final_point_row~2")) (.n (val% «verify_bus_gkr» "final_point_row~2"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "final_point_row~4")) (.n (val% «verify_bus_gkr» "final_point_row~3")) (.n (val% «verify_bus_gkr» "final_point_row~1"))), .atom (.mul (.n (val% «verify_bus_gkr» "final_point_row~5")) (.n (val% «verify_bus_gkr» "final_point_row~4")) (.n (val% «verify_bus_gkr» "final_point_row~4"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "final_point_row~6")) (.n (val% «verify_bus_gkr» "final_point_row~5")) (.n (val% «verify_bus_gkr» "final_point_row~5"))), .atom (.mul (.n (val% «verify_bus_gkr» "final_point_row~7")) (.n (val% «verify_bus_gkr» "final_point_row~6")) (.n (val% «verify_bus_gkr» "final_point_row~6"))),
    .atom (.mul (.n (val% «verify_bus_gkr» "final_point_row")) (.n (val% «verify_bus_gkr» "gkr_pts")) (.n (val% «verify_bus_gkr» "final_point_row~7"))),
    .atom (.const (.n (val% «verify_bus_gkr» "s34#0")) (word 1 0)), .atom (.add (.n (val% «verify_bus_gkr» "s34#1")) (.n (val% «verify_bus_gkr» "s34#0")) (.n (val% «verify_bus_gkr» "g_bus_mu"))),
    .atom (.const (.n (val% «verify_bus_gkr» "s34#2")) (word 1 0)),
    .callIf (.n (val% «verify_bus_gkr» "s34#1")) name% «verify_bus_gkr_loop0» [.n (val% «verify_bus_gkr» "s34#2"), .n (val% «verify_bus_gkr» "g_bus_mu"), .n (val% «verify_bus_gkr» "zeta"), .n (val% «verify_bus_gkr» "final_point_row")],
    .atom (.hint (.alloc (.n (val% «verify_bus_gkr» "leaves")) 3)),
    .atom (.load (.n (val% «verify_bus_gkr» "s36.u0.s0#0")) (.n (val% «verify_bus_gkr» "last")) 6), .atom (.load (.n (val% «verify_bus_gkr» "s36.u0.s0#0")) (.n (val% «verify_bus_gkr» "leaves")) 0),
    .atom (.load (.n (val% «verify_bus_gkr» "s36.u1.s0#0")) (.n (val% «verify_bus_gkr» "last")) 7), .atom (.load (.n (val% «verify_bus_gkr» "s36.u1.s0#0")) (.n (val% «verify_bus_gkr» "leaves")) 1),
    .atom (.load (.n (val% «verify_bus_gkr» "s36.u2.s0#0")) (.n (val% «verify_bus_gkr» "last")) 8), .atom (.load (.n (val% «verify_bus_gkr» "s36.u2.s0#0")) (.n (val% «verify_bus_gkr» "leaves")) 2)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n ((val% «verify_bus_gkr» "s37#0") + k)) (.n (val% «verify_bus_gkr» "last")) k)) ++
  [.atom (.copy (.n (val% «verify_bus_gkr» "s37#0[5]")) (.n (val% «verify_bus_gkr» "cursor@2"))), .atom (.copy (.n (val% «verify_bus_gkr» "s37#0[6]")) (.n (val% «verify_bus_gkr» "leaves")))]

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
def vbgW (layers rounds rows odd bnd rem vals : E) : ℕ → E := fun i ↦
  if i = 16 then layers else if i = 17 then rounds else if i = 18 then rows else
    if i = 63 then odd else if i = 65 then bnd else if i = 66 then rem else if i = 402 then 0
    else vals

/-! ## The root-most arms, renamed -/

theorem rtSh_idx (v : V) : (rtSh v).idx = if 66 ≤ v.idx then v.idx + 34 else v.idx := by
  unfold rtSh; split_ifs <;> rfl

theorem rtSh_lt {x y : V} : (rtSh x).idx < (rtSh y).idx ↔ x.idx < y.idx := by
  rw [rtSh_idx, rtSh_idx]; split_ifs <;> omega

theorem rtUn_rtSh {v : V} (h : v = .n v.idx) : rtUn (rtSh v) = v := by
  obtain ⟨k, rfl⟩ : ∃ k, v = .n k := ⟨v.idx, h⟩
  by_cases hk : k < 66
  · rw [rtSh_lo hk]; simp [rtUn]; omega
  · have h66 : 66 ≤ k := by omega
    rw [rtSh_hi h66]; simp [rtUn]; omega

/-- An atom of the arms: an equation over values `.n k`. -/
def armOkA (a : Atom) : Bool :=
  a.vals.all (fun v ↦ decide (v = .n v.idx)) &&
    match a with
    | .const .. | .add .. | .mul .. | .copy .. | .load .. | .keccak .. | .assertEq .. => true
    | _ => false

def armOkS : Stmt → Bool
  | .atom a => armOkA a
  | _ => false

theorem vbArms_ok : (rtFour ++ rtTwo).all armOkS = true := by decide +kernel

theorem vbArmsR_noNe :
    (Stmt.renameList rtSh rtFour ++ Stmt.renameList rtSh rtTwo).all noNeB = true := by
  decide +kernel

/-- **An arm's atom on its renamed equation** is on its own at `σ ∘ rtSh`. -/
theorem good_sh {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {a : Atom}
    (hok : armOkA a = true) (hg : Good rd S w σ (a.rename rtSh)) :
    Good rd (S.map (Atom.rename rtUn)) w (σ ∘ rtSh) a := by
  cases a with
  | const d e => exact hg
  | add d x y => exact hg
  | copy d s => exact hg
  | assertEq x y => trivial
  | keccak ins outs i o' =>
    obtain ⟨h1, h2, h3⟩ := hg
    refine ⟨by simpa using h1, by simpa using h2, fun c hc ↦ ?_⟩
    have := h3 c (by simpa using hc)
    simpa [List.map_map] using this
  | mul d x y =>
    simp only [Atom.rename, Good, rtSh_lt] at hg ⊢
    exact hg
  | load d p off =>
    obtain ⟨hd, hp⟩ : d = .n d.idx ∧ p = .n p.idx := by simpa [armOkA, Atom.vals] using hok
    rcases hg with h | h
    · left
      exact List.mem_map.mpr ⟨_, h, by simp [Atom.rename, rtUn_rtSh hd, rtUn_rtSh hp]⟩
    · exact .inr h
  | _ => simp [armOkA] at hok

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
root-most step's words and the slot it leads to, every layer's words (`GlIter`), the last slot
with its point at `zeta` and its values in the values' buffer give the relation, returning the
last slot's capacity, cursor and the buffer. -/
theorem vbg_body_of {depth : ℕ} (hd1 : 1 ≤ depth) (hd : depth ≤ 32) {cap0 : List E}
    (hcl : cap0.length = 5) {cur zeta tabs stream layers rounds rows odd bnd rem vals : E}
    (hrc : (rd (addressOfIndex depth)).isSome = true ∧ (rd (addressOfIndex (32 - depth))).isSome
        = true)
    {x0 x1 : E} (hx0 : LoadHolds rd cur 0 x0) (hx1 : LoadHolds rd cur 1 x1) (hcnt : x1 ≠ 0)
    (hodt : TbReadsAt rd odd ((List.range 33).map fun k ↦ gen ^ (k % 2)))
    (hfb : TbReadsAt rd bnd ((List.range 33).map fun k ↦ gen ^ ((k - 1) / 8)))
    (hfr : TbReadsAt rd rem ((List.range 33).map fun k ↦ gen ^ (((k - 1) / 2) % 4)))
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
    (hit : ∀ j < (depth - 1) / 2, GlIter rd layers rows rounds (depth % 2) j)
    {sF : Fs} {curF : E} {stF : GkrState} {posF : E}
    (hlast : GkSlot rd layers depth sF curF stF (rows * gen ^ (40 * ((depth - 1) / 2 + 1))) posF)
    (hz : TbReadsAt rd zeta stF.point) (hv : TbReadsAt rd vals stF.values) :
    Stmt.HoldsList (coreProgram.Rel rd) rd
        (B1.Val.ofArgs (ev rd (vbgW layers rounds rows odd bnd rem vals)
          (cap0 ++ [cur, gen ^ depth, zeta, tabs, stream]) vbgEvL)) vbgPre True
        (fun rs => rs = sF.cap ++ [curF, vals]) ∧
      vbgRets.map (B1.Val.ofArgs (ev rd (vbgW layers rounds rows odd bnd rem vals)
        (cap0 ++ [cur, gen ^ depth, zeta, tabs, stream]) vbgEvL)) = sF.cap ++ [curF, vals] := by
  obtain ⟨a0, a1, a2, a3, a4, rfl⟩ := tb_list5_eq hcl
  simp only [List.cons_append, List.nil_append]
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  set args : List E := [a0, a1, a2, a3, a4, cur, gen ^ depth, zeta, tabs, stream] with hargs
  have hc9 : chk args.length vbgEvL = some c' := hc'
  set W : ℕ → E := vbgW layers rounds rows odd bnd rem vals with hW
  set σ : Val := B1.Val.ofArgs (ev rd W args vbgEvL) with hσ
  have hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s := (ev_spec rd W vbgEvL args hc9).2.2
  have par : ∀ i < (val% «verify_bus_gkr» "layers~0"), σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd W hc9 (by simpa [hargs] using hi)
  have e0 : σ (.n (val% «verify_bus_gkr» "fs0")) = a0 := par 0 (by omega)
  have e1 : σ (.n (val% «verify_bus_gkr» "fs1")) = a1 := par 1 (by omega)
  have e2 : σ (.n (val% «verify_bus_gkr» "fs2")) = a2 := par 2 (by omega)
  have e3 : σ (.n (val% «verify_bus_gkr» "fs3")) = a3 := par 3 (by omega)
  have e4 : σ (.n (val% «verify_bus_gkr» "fs4")) = a4 := par 4 (by omega)
  have e5 : σ (.n (val% «verify_bus_gkr» "cursor@1")) = cur := par 5 (by omega)
  have e6 : σ (.n (val% «verify_bus_gkr» "g_bus_mu")) = gen ^ depth := par 6 (by omega)
  have e7 : σ (.n (val% «verify_bus_gkr» "zeta")) = zeta := par 7 (by omega)
  have e8 : σ (.n (val% «verify_bus_gkr» "tabs")) = tabs := par 8 (by omega)
  have e9 : σ (.n (val% «verify_bus_gkr» "stream")) = stream := par 9 (by omega)
  have g : ∀ n (a : Atom), tbStmtsEqb [.atom a] ((vbgPre.drop n).take 1) = true →
      fixNe (.atom a) = .atom a → Good rd vbgS W σ a :=
    fun n a heq hf => vb_good (rd := rd) (w := W) (σ := σ) hG n a heq hf
  set sh := depth % 2 with hsh
  set m := (depth - 1) / 2 with hm
  -- the depth's powers, the allocations, the range check
  have c10 : σ (.n (val% «verify_bus_gkr» "layers~0")) = word 4 0 := g 0 (.const (.n (val% «verify_bus_gkr» "layers~0")) (word 4 0)) (by decide +kernel) rfl
  have m11 := good_mul (g 1 (.mul (.n (val% «verify_bus_gkr» "layers~1")) (.n (val% «verify_bus_gkr» "g_bus_mu")) (.n (val% «verify_bus_gkr» "layers~0"))) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m12 := good_mul (g 2 (.mul (.n (val% «verify_bus_gkr» "layers~2")) (.n (val% «verify_bus_gkr» "layers~1")) (.n (val% «verify_bus_gkr» "layers~1"))) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m13 := good_mul (g 3 (.mul (.n (val% «verify_bus_gkr» "layers~3")) (.n (val% «verify_bus_gkr» "layers~2")) (.n (val% «verify_bus_gkr» "layers~2"))) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m14 := good_mul (g 4 (.mul (.n (val% «verify_bus_gkr» "layers~4")) (.n (val% «verify_bus_gkr» "layers~3")) (.n (val% «verify_bus_gkr» "layers~1"))) (by decide +kernel) rfl) (by omega)
    (by omega)
  have m15 := good_mul (g 5 (.mul (.n (val% «verify_bus_gkr» "layers~5")) (.n (val% «verify_bus_gkr» "layers~4")) (.n (val% «verify_bus_gkr» "layers~4"))) (by decide +kernel) rfl) (by omega)
    (by omega)
  have e16 : σ (.n (val% «verify_bus_gkr» "layers")) = layers := by
    have h : σ (.n (val% «verify_bus_gkr» "layers")) = W 16 := g 6 (.hint (.allocDyn (.n (val% «verify_bus_gkr» "layers")) (.n (val% «verify_bus_gkr» "layers~5")))) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e17 : σ (.n (val% «verify_bus_gkr» "rounds")) = rounds := by
    have h : σ (.n (val% «verify_bus_gkr» "rounds")) = W 17 := g 7 (.hint (.alloc (.n (val% «verify_bus_gkr» "rounds")) 6034)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e18 : σ (.n (val% «verify_bus_gkr» "gkr_pts")) = rows := by
    have h : σ (.n (val% «verify_bus_gkr» "gkr_pts")) = W 18 := g 8 (.hint (.alloc (.n (val% «verify_bus_gkr» "gkr_pts")) 1640)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have c19 : σ (.n (val% «verify_bus_gkr» "s3#0")) = word 4294967296 0 :=
    g 9 (.const (.n (val% «verify_bus_gkr» "s3#0")) (word 4294967296 0)) (by decide +kernel) rfl
  have w32 : word 4294967296 0 = gen ^ 32 := by
    rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num)]
  have grc := g 10 (.rangeCheck (.n (val% «verify_bus_gkr» "g_bus_mu")) (.n (val% «verify_bus_gkr» "s3#1")) (.n (val% «verify_bus_gkr» "s3#2")) (.n (val% «verify_bus_gkr» "s3#3")) (.n (val% «verify_bus_gkr» "s3#0"))) (by decide +kernel) rfl
  have h1920 : (V.n (val% «verify_bus_gkr» "s3#0")).idx < (V.n (val% «verify_bus_gkr» "s3#1")).idx := show 19 < 20 by norm_num
  have e20 : σ (.n (val% «verify_bus_gkr» "s3#1")) = gen ^ (32 - depth) := by
    have h3 : σ (.n (val% «verify_bus_gkr» "s3#1")) = σ (.n (val% «verify_bus_gkr» "s3#0")) * (σ (.n (val% «verify_bus_gkr» "g_bus_mu")))⁻¹ := by
      have := grc.2.2
      simpa only [h1920, ↓reduceIte] using this
    have hp32 : gen ^ 32 = gen ^ (32 - depth) * gen ^ depth := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    rw [h3, c19, w32, e6, hp32, mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero _), mul_one]
  have hrcH : (Atom.rangeCheck (.n (val% «verify_bus_gkr» "g_bus_mu")) (.n (val% «verify_bus_gkr» "s3#1")) (.n (val% «verify_bus_gkr» "s3#2")) (.n (val% «verify_bus_gkr» "s3#3")) (.n (val% «verify_bus_gkr» "s3#0"))).Holds rd σ := by
    refine holds_of_good grc ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e6]; exact tb_gen_pow_isInK _
    · rw [e6, gen_pow_eq_ofK, tb_addr_ofK, Nat.add_zero]
      exact hrc.1
    · rw [e20]; exact tb_gen_pow_isInK _
    · rw [e20, gen_pow_eq_ofK, tb_addr_ofK, Nat.add_zero]
      exact hrc.2
    · show (if (V.n (val% «verify_bus_gkr» "s3#0")).idx < (V.n (val% «verify_bus_gkr» "s3#1")).idx then σ (.n (val% «verify_bus_gkr» "g_bus_mu")) ≠ 0 else True)
      simp only [h1920, ↓reduceIte]
      rw [e6]; exact gen_pow_ne_zero _
  have gq := vb_goodB hG 11 ((List.range 5).map fun k ↦ Stmt.atom (.copy (.n ((val% «verify_bus_gkr» "sp[0]") + k)) (.n k)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have q23 : ∀ k < 5, σ (.n ((val% «verify_bus_gkr» "sp[0]") + k)) = σ (.n k) := fun k hk =>
    gq _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  have q23a : σ (.n (val% «verify_bus_gkr» "sp[0]")) = a0 :=
    (gq _ (List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩)).trans e0
  have q24a : σ (.n (val% «verify_bus_gkr» "sp[1]")) = a1 :=
    (gq _ (List.mem_map.mpr ⟨1, List.mem_range.mpr (by omega), rfl⟩)).trans e1
  have q25a : σ (.n (val% «verify_bus_gkr» "sp[2]")) = a2 :=
    (gq _ (List.mem_map.mpr ⟨2, List.mem_range.mpr (by omega), rfl⟩)).trans e2
  have q26a : σ (.n (val% «verify_bus_gkr» "sp[3]")) = a3 :=
    (gq _ (List.mem_map.mpr ⟨3, List.mem_range.mpr (by omega), rfl⟩)).trans e3
  have q27a : σ (.n (val% «verify_bus_gkr» "sp[4]")) = a4 :=
    (gq _ (List.mem_map.mpr ⟨4, List.mem_range.mpr (by omega), rfl⟩)).trans e4
  -- the two roots
  obtain ⟨e28, -, hfs28⟩ := fsNextT_good (C := coreProgram.Rel rd) (kret := fun _ => True)
    (vb_goodB hG 16 (fsNextT (.n (val% «verify_bus_gkr» "cursor@1")) 0 (val% «verify_bus_gkr» "x@1")) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (by decide +kernel) (by rw [e5]; exact hx0)
  obtain ⟨e33, -, hfs33⟩ := fsNextT_good (C := coreProgram.Rel rd) (kret := fun _ => True)
    (vb_goodB hG 21 (fsNextT (.n (val% «verify_bus_gkr» "cursor@1")) 1 (val% «verify_bus_gkr» "x@2")) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (by decide +kernel) (by rw [e5]; exact hx1)
  obtain ⟨⟨l28, p28⟩, -⟩ := (holds_fsNextT _ _ _ _ _).mp hfs28
  obtain ⟨⟨l33, p33⟩, -⟩ := (holds_fsNextT _ _ _ _ _).mp hfs33
  have q31 : σ (.n (val% «verify_bus_gkr» "vals[0]")) = σ (.n (val% «verify_bus_gkr» "x@1")) := g 19 (.copy (.n (val% «verify_bus_gkr» "vals[0]")) (.n (val% «verify_bus_gkr» "x@1"))) (by decide +kernel) rfl
  have q32 : σ (.n (val% «verify_bus_gkr» "vals[1]")) = σ (.n (val% «verify_bus_gkr» "x@1")) := g 20 (.copy (.n (val% «verify_bus_gkr» "vals[1]")) (.n (val% «verify_bus_gkr» "x@1"))) (by decide +kernel) rfl
  have q36 : σ (.n (val% «verify_bus_gkr» "vals[2]")) = σ (.n (val% «verify_bus_gkr» "x@2")) := g 24 (.copy (.n (val% «verify_bus_gkr» "vals[2]")) (.n (val% «verify_bus_gkr» "x@2"))) (by decide +kernel) rfl
  -- the count asserted nonzero
  have c37 : σ (.n (val% «verify_bus_gkr» "s12#0")) = word 0 0 := g 25 (.const (.n (val% «verify_bus_gkr» "s12#0")) (word 0 0)) (by decide +kernel) rfl
  have a38 : σ (.n (val% «verify_bus_gkr» "s12#1")) = σ (.n (val% «verify_bus_gkr» "x@2")) + σ (.n (val% «verify_bus_gkr» "s12#0")) :=
    g 26 (.add (.n (val% «verify_bus_gkr» "s12#1")) (.n (val% «verify_bus_gkr» "x@2")) (.n (val% «verify_bus_gkr» "s12#0"))) (by decide +kernel) rfl
  have i39 : σ (.n (val% «verify_bus_gkr» "s12#2")) = (σ (.n (val% «verify_bus_gkr» "s12#1")))⁻¹ :=
    g 27 (.hint (.inverse (.n (val% «verify_bus_gkr» "s12#1")) (.n (val% «verify_bus_gkr» "s12#2")))) (by decide +kernel) rfl
  have m40 : σ (.n (val% «verify_bus_gkr» "s12#3")) = σ (.n (val% «verify_bus_gkr» "s12#1")) * σ (.n (val% «verify_bus_gkr» "s12#2")) :=
    good_mulS (vb_goodS hG 28 (.atom (.assertNe (.n (val% «verify_bus_gkr» "s12#1")) (.n (val% «verify_bus_gkr» "s12#2")) (.n (val% «verify_bus_gkr» "s12#3")))) (by decide +kernel) rfl)
      (by omega) (by omega)
  have e38 : σ (.n (val% «verify_bus_gkr» "s12#1")) = x1 := by rw [a38, c37, tb_word_zero, add_zero, e33]
  -- the combiner and the claim
  have c41 : σ (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0")) = word 1 0 := g 29 (.const (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0")) (word 1 0)) (by decide +kernel) rfl
  have c42 : σ (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]")) = word 0 0 := g 30 (.const (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]")) (word 0 0)) (by decide +kernel) rfl
  have c43 : σ (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]")) = word 0 0 := g 31 (.const (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]")) (word 0 0)) (by decide +kernel) rfl
  have c44 : σ (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]")) = word 0 0 := g 32 (.const (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]")) (word 0 0)) (by decide +kernel) rfl
  have c45 : σ (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")) = word 0 0 := g 33 (.const (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")) (word 0 0)) (by decide +kernel) rfl
  have z42 : σ (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]")) = 0 := by rw [c42, tb_word_zero]
  have z43 : σ (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]")) = 0 := by rw [c43, tb_word_zero]
  have z44 : σ (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]")) = 0 := by rw [c44, tb_word_zero]
  have z45 : σ (.n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")) = 0 := by rw [c45, tb_word_zero]
  have hins : (([.n (val% «verify_bus_gkr» "rate[0]@1"), .n (val% «verify_bus_gkr» "rate[1]@1"), .n (val% «verify_bus_gkr» "rate[2]@1"), .n (val% «verify_bus_gkr» "rate[3]@1"), .n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] ++
      (List.range 5).map fun k ↦ V.n ((val% «verify_bus_gkr» "sp[0]") + k)) : List V).map σ =
      rateOf (rootS [a0, a1, a2, a3, a4] x0 x1).pend ++ (rootS [a0, a1, a2, a3, a4] x0 x1).cap := by
    have hcapE : ((List.range 5).map fun k ↦ V.n ((val% «verify_bus_gkr» "sp[0]") + k)).map σ = [a0, a1, a2, a3, a4] := by
      show [σ (.n (val% «verify_bus_gkr» "sp[0]")), σ (.n (val% «verify_bus_gkr» "sp[1]")), σ (.n (val% «verify_bus_gkr» "sp[2]")), σ (.n (val% «verify_bus_gkr» "sp[3]")), σ (.n (val% «verify_bus_gkr» "sp[4]"))] = [a0, a1, a2, a3, a4]
      rw [q23a, q24a, q25a, q26a, q27a]
    obtain ⟨e29, e30⟩ := Prod.ext_iff.mp (fsPackT_cells p28)
    obtain ⟨e34, e35⟩ := Prod.ext_iff.mp (fsPackT_cells p33)
    rw [List.map_append, hcapE, rateOf_eq_cells _ (by simp [rootS])]
    norm_num at e29 e30 e34 e35
    simp [rootS, pendCells, e29, e30, e34, e35, e28, e33, z42, z43, z44, z45]
  obtain ⟨k35, hP, hcap⟩ := lyc_keccak (rd := rd) (σ := σ) (S := vbgS) (w := W)
    (g 34 (.keccak ([.n (val% «verify_bus_gkr» "rate[0]@1"), .n (val% «verify_bus_gkr» "rate[1]@1"), .n (val% «verify_bus_gkr» "rate[2]@1"), .n (val% «verify_bus_gkr» "rate[3]@1"), .n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «verify_bus_gkr» "s13.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] ++
      (List.range 5).map fun k ↦ .n ((val% «verify_bus_gkr» "sp[0]") + k)) (lyOuts (val% «verify_bus_gkr» "nxt[0]@1")) false false) (by decide +kernel) rfl)
  rw [hins] at hP hcap
  have e59 : σ (.n (val% «verify_bus_gkr» "nxt[0]@1")) = (rootS [a0, a1, a2, a3, a4] x0 x1).squeeze.1 :=
    challengeT_value (s0 := .n (val% «verify_bus_gkr» "nxt[0]@1")) (b := 46) rfl (hP 0 (by omega))
  have m60 := good_mul (g 35 (.mul (.n (val% «verify_bus_gkr» "claim@1~0")) (.n (val% «verify_bus_gkr» "nxt[0]@1")) (.n (val% «verify_bus_gkr» "vals[2]"))) (by decide +kernel) rfl) (by omega)
    (by omega)
  have a61 : σ (.n (val% «verify_bus_gkr» "claim@1")) = σ (.n (val% «verify_bus_gkr» "vals[1]")) + σ (.n (val% «verify_bus_gkr» "claim@1~0")) :=
    g 36 (.add (.n (val% «verify_bus_gkr» "claim@1")) (.n (val% «verify_bus_gkr» "vals[1]")) (.n (val% «verify_bus_gkr» "claim@1~0"))) (by decide +kernel) rfl
  have m62 := good_mul (g 37 (.mul (.n (val% «verify_bus_gkr» "claim@2~0")) (.n (val% «verify_bus_gkr» "nxt[0]@1")) (.n (val% «verify_bus_gkr» "claim@1"))) (by decide +kernel) rfl) (by omega)
    (by omega)
  have a63 : σ (.n (val% «verify_bus_gkr» "claim@2")) = σ (.n (val% «verify_bus_gkr» "vals[0]")) + σ (.n (val% «verify_bus_gkr» "claim@2~0")) :=
    g 38 (.add (.n (val% «verify_bus_gkr» "claim@2")) (.n (val% «verify_bus_gkr» "vals[0]")) (.n (val% «verify_bus_gkr» "claim@2~0"))) (by decide +kernel) rfl
  have e63 : σ (.n (val% «verify_bus_gkr» "claim@2")) = polyEval (rootSt x0 x1).values (rootS [a0, a1, a2, a3, a4] x0 x1).squeeze.1 := by
    rw [a63, m62, a61, m60, q31, q32, q36, e28, e33, ← e59]
    simp only [rootSt, polyEval, List.foldr]
    ring
  have hcapP : (lyCap (val% «verify_bus_gkr» "nxt[0]@1")).map σ = capOf (rootS [a0, a1, a2, a3, a4] x0 x1).perm := hcap
  have e64 : σ (.n (val% «verify_bus_gkr» "depth_odd")) = odd := by
    have h : σ (.n (val% «verify_bus_gkr» "depth_odd")) = W 63 := g 39 (.hint (.alloc (.n (val% «verify_bus_gkr» "depth_odd")) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e66 : σ (.n (val% «verify_bus_gkr» "four_bounds")) = bnd := by
    have h : σ (.n (val% «verify_bus_gkr» "four_bounds")) = W 65 := g 42 (.hint (.alloc (.n (val% «verify_bus_gkr» "four_bounds")) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  have e67 : σ (.n (val% «verify_bus_gkr» "four_rem")) = rem := by
    have h : σ (.n (val% «verify_bus_gkr» "four_rem")) = W 66 := g 43 (.hint (.alloc (.n (val% «verify_bus_gkr» "four_rem")) 33)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  -- the tables
  have gT := vb_goodB hG 39 vbR5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hok : ∀ k < 33, LoadHolds rd odd k (gen ^ (k % 2)) := fun k hk => by
    have := hodt k (by simpa using hk)
    simpa using this
  have hbk : ∀ k < 33, LoadHolds rd bnd k (gen ^ ((k - 1) / 8)) := fun k hk => by
    have := hfb k (by simpa using hk)
    simpa using this
  have hrk : ∀ k < 33, LoadHolds rd rem k (gen ^ (((k - 1) / 2) % 4)) := fun k hk => by
    have := hfr k (by simpa using hk)
    simpa using this
  have T0 : ∀ s ∈ vbT0, SHolds (coreProgram.Rel rd) rd σ s := by
    have c65 : σ (.n (val% «verify_bus_gkr» "s16#0")) = word 1 0 :=
      gT (.atom (.const (.n (val% «verify_bus_gkr» "s16#0")) (word 1 0))) (by simp [vbR5, vbT0])
    have c68 : σ (.n (val% «verify_bus_gkr» "s19#0")) = word 1 0 :=
      gT (.atom (.const (.n (val% «verify_bus_gkr» "s19#0")) (word 1 0))) (by simp [vbR5, vbT0])
    have c69 : σ (.n (val% «verify_bus_gkr» "s20#0")) = word 1 0 :=
      gT (.atom (.const (.n (val% «verify_bus_gkr» "s20#0")) (word 1 0))) (by simp [vbR5, vbT0])
    simp only [vbT0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    refine ⟨trivial, c65, ?_, trivial, trivial, c68, ?_, c69, ?_⟩
    · show LoadHolds rd (σ (.n (val% «verify_bus_gkr» "depth_odd"))) 0 (σ (.n (val% «verify_bus_gkr» "s16#0")))
      rw [e64, c65, tb_word_one]; simpa using hok 0 (by omega)
    · show LoadHolds rd (σ (.n (val% «verify_bus_gkr» "four_bounds"))) 0 (σ (.n (val% «verify_bus_gkr» "s19#0")))
      rw [e66, c68, tb_word_one]; simpa using hbk 0 (by omega)
    · show LoadHolds rd (σ (.n (val% «verify_bus_gkr» "four_rem"))) 0 (σ (.n (val% «verify_bus_gkr» "s20#0")))
      rw [e67, c69, tb_word_one]; simpa using hrk 0 (by omega)
  have TB : ∀ d < 32, ∀ s ∈ vbTab d, SHolds (coreProgram.Rel rd) rd σ s := by
    intro d hd
    have mem : ∀ t ∈ vbTab d, t ∈ vbR5 := fun t ht => List.mem_append_right _
      (List.mem_flatten.mpr ⟨vbTab d, List.mem_map.mpr ⟨d, List.mem_range.mpr hd, rfl⟩, ht⟩)
    have c0 : σ (.n (69 + 3 * d)) = word (2 ^ ((d + 1) % 2)) 0 :=
      gT (.atom (.const (.n (69 + 3 * d)) (word (2 ^ ((d + 1) % 2)) 0))) (mem _ (by simp [vbTab]))
    have c1 : σ (.n (70 + 3 * d)) = word (2 ^ (d / 8)) 0 :=
      gT (.atom (.const (.n (70 + 3 * d)) (word (2 ^ (d / 8)) 0))) (mem _ (by simp [vbTab]))
    have c2 : σ (.n (71 + 3 * d)) = word (2 ^ ((d / 2) % 4)) 0 :=
      gT (.atom (.const (.n (71 + 3 * d)) (word (2 ^ ((d / 2) % 4)) 0))) (mem _ (by simp [vbTab]))
    simp only [vbTab, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    refine ⟨c0, ?_, c1, ?_, c2, ?_⟩
    · show LoadHolds rd (σ (.n (val% «verify_bus_gkr» "depth_odd"))) (d + 1) (σ (.n (69 + 3 * d)))
      rw [e64, c0, tb_word_two_pow (by omega)]; exact hok (d + 1) (by omega)
    · show LoadHolds rd (σ (.n (val% «verify_bus_gkr» "four_bounds"))) (d + 1) (σ (.n (70 + 3 * d)))
      rw [e66, c1, tb_word_two_pow (by omega)]
      have := hbk (d + 1) (by omega)
      rwa [show d + 1 - 1 = d by omega] at this
    · show LoadHolds rd (σ (.n (val% «verify_bus_gkr» "four_rem"))) (d + 1) (σ (.n (71 + 3 * d)))
      rw [e67, c2, tb_word_two_pow (by omega)]
      have := hrk (d + 1) (by omega)
      rwa [show d + 1 - 1 = d by omega] at this
  -- the depth's parity, `start_g` and the root-most slot
  have m132 := good_mul (g 240 (.mul (.n (val% «verify_bus_gkr» "odd_g~0")) (.n (val% «verify_bus_gkr» "depth_odd")) (.n (val% «verify_bus_gkr» "g_bus_mu"))) (by decide +kernel) rfl) (by omega)
    (by omega)
  obtain ⟨e133, l133⟩ := good_read (g 241 (.load (.n (val% «verify_bus_gkr» "odd_g")) (.n (val% «verify_bus_gkr» "odd_g~0")) 0) (by decide +kernel) rfl)
    (by decide +kernel) (show LoadHolds rd (σ (.n (val% «verify_bus_gkr» "odd_g~0"))) 0 (gen ^ sh) by
      rw [m132, e64, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hok depth (by omega))
  have c134 : σ (.n (val% «verify_bus_gkr» "start_g~0")) = word 4 0 := g 242 (.const (.n (val% «verify_bus_gkr» "start_g~0")) (word 4 0)) (by decide +kernel) rfl
  have d135 : σ (.n (val% «verify_bus_gkr» "start_g")) = σ (.n (val% «verify_bus_gkr» "start_g~0")) * (σ (.n (val% «verify_bus_gkr» "odd_g")))⁻¹ := by
    have h := g 243 (.mul (.n (val% «verify_bus_gkr» "start_g~0")) (.n (val% «verify_bus_gkr» "start_g")) (.n (val% «verify_bus_gkr» "odd_g"))) (by decide +kernel) rfl
    have hn : ¬ ((V.n (val% «verify_bus_gkr» "start_g")).idx < (V.n (val% «verify_bus_gkr» "start_g~0")).idx ∧ (V.n (val% «verify_bus_gkr» "odd_g")).idx < (V.n (val% «verify_bus_gkr» "start_g~0")).idx) := by
      show ¬ (168 < 167 ∧ 166 < 167); omega
    simpa only [Good, hn, ↓reduceIte] using h
  have e135 : σ (.n (val% «verify_bus_gkr» "start_g")) = gen ^ (2 - sh) := by
    rw [d135, c134, tb_word_four, e133]
    have hs : sh ≤ 2 := by omega
    rw [show (gen : E) ^ 2 = gen ^ (2 - sh) * gen ^ sh by rw [← pow_add, Nat.sub_add_cancel hs],
      mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero _), mul_one]
  have m136 := good_mul (g 244 (.mul (.n (val% «verify_bus_gkr» "nxt~0")) (.n (val% «verify_bus_gkr» "start_g")) (.n (val% «verify_bus_gkr» "start_g"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m137 := good_mul (g 245 (.mul (.n (val% «verify_bus_gkr» "nxt~1")) (.n (val% «verify_bus_gkr» "nxt~0")) (.n (val% «verify_bus_gkr» "nxt~0"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m138 := good_mul (g 246 (.mul (.n (val% «verify_bus_gkr» "nxt~2")) (.n (val% «verify_bus_gkr» "nxt~1")) (.n (val% «verify_bus_gkr» "start_g"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m139 := good_mul (g 247 (.mul (.n (val% «verify_bus_gkr» "nxt~3")) (.n (val% «verify_bus_gkr» "nxt~2")) (.n (val% «verify_bus_gkr» "nxt~2"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m140 := good_mul (g 248 (.mul (.n (val% «verify_bus_gkr» "nxt")) (.n (val% «verify_bus_gkr» "layers")) (.n (val% «verify_bus_gkr» "nxt~3"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e140 : σ (.n (val% «verify_bus_gkr» "nxt")) = σ (.n (val% «verify_bus_gkr» "layers")) * gen ^ (10 * (2 - sh)) := by
    rw [m140, m139, m138, m137, m136, e135, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have c141 : σ (.n (val% «verify_bus_gkr» "s26#0")) = word 1 0 := g 249 (.const (.n (val% «verify_bus_gkr» "s26#0")) (word 1 0)) (by decide +kernel) rfl
  have a142 : σ (.n (val% «verify_bus_gkr» "s26#1")) = σ (.n (val% «verify_bus_gkr» "odd_g")) + σ (.n (val% «verify_bus_gkr» "s26#0")) :=
    g 250 (.add (.n (val% «verify_bus_gkr» "s26#1")) (.n (val% «verify_bus_gkr» "odd_g")) (.n (val% «verify_bus_gkr» "s26#0"))) (by decide +kernel) rfl
  -- the root-most layer, on its arms renamed back (`rtSh`)
  have sh_lo : ∀ k, k < 66 → (σ ∘ rtSh) (.n k) = σ (.n k) := fun k hk ↦ by
    simp only [Function.comp_apply, rtSh_lo hk]
  have hcapSh : (lyCap (val% «verify_bus_gkr» "nxt[0]@1")).map (σ ∘ rtSh) = (lyCap (val% «verify_bus_gkr» "nxt[0]@1")).map σ := by
    simp only [lyCap, List.map_map]
    refine List.map_congr_left fun k hk ↦ ?_
    have := List.mem_range.mp hk
    simp only [Function.comp_apply, rtSh_lo (show 46 + 8 + k < 66 by omega)]
  have h140 : (σ ∘ rtSh) (.n (val% «verify_bus_gkr» "s21.u24.s1#0")) = σ (.n (val% «verify_bus_gkr» "nxt")) := by
    simp only [Function.comp_apply, rtSh_hi (show 66 ≤ 139 by omega)]
  have hArms : ∀ t ∈ rtFour ++ rtTwo, GoodS rd (vbgS.map (Atom.rename rtUn)) W (σ ∘ rtSh) t := by
    intro t ht
    have hite := good_ite (G := fun s => GoodS rd vbgS W σ (fixNe s))
      (fun s hs => hG _ (List.mem_map_of_mem hs)) 251 (.n (val% «verify_bus_gkr» "s26#1")) (Stmt.renameList rtSh rtFour)
      (Stmt.renameList rtSh rtTwo) (by decide +kernel)
    have hmem : t.rename rtSh ∈ Stmt.renameList rtSh rtFour ++ Stmt.renameList rtSh rtTwo := by
      rcases List.mem_append.mp ht with h | h
      · exact List.mem_append_left _ (mem_renameList_of h)
      · exact List.mem_append_right _ (mem_renameList_of h)
    have h1 := hite _ hmem
    rw [fixNe_of_noNe (List.all_eq_true.mp vbArmsR_noNe _ hmem)] at h1
    have hok' := List.all_eq_true.mp vbArms_ok t ht
    cases t with
    | atom a => exact good_sh hok' h1
    | _ => simp [armOkS] at hok'
  have hk2 : ∀ i < 6, some (chB (val% «verify_bus_gkr» "nxt[9]@5") i, 5, 2 + i) ∉
      ((vbgS.map (Atom.rename rtUn)).map loadKey) := by decide +kernel
  have hk4 : ∀ i < 12, some (chB (val% «verify_bus_gkr» "s21.u25.s1#0") i, 5, 2 + i) ∉
      ((vbgS.map (Atom.rename rtUn)).map loadKey) := by decide +kernel
  have R7 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR7 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    simp only [vbR7, Stmt.HoldsList]
    rw [tb_holds_ite_noRet _ _ _ (by decide +kernel) (by decide +kernel)]
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
      rw [Stmt.holdsList_rename]
      refine rtc_four hArms hk4 rfl (by rw [sh_lo 46 (by omega)]; exact e59)
        (by rw [sh_lo 62 (by omega)]; exact e63)
        (by rw [hcapSh]; exact hcapP)
        (by rw [sh_lo 42 (by omega)]; exact z42) (by rw [sh_lo 43 (by omega)]; exact z43)
        (by rw [sh_lo 44 (by omega)]; exact z44) (by rw [sh_lo 45 (by omega)]; exact z45) hD
        (by rw [sh_lo 5 (by omega), e5]; exact hxD)
        (by rw [h140, sh_lo 16 (by omega)]; exact e140)
        (by rw [sh_lo 16 (by omega), sh_lo 5 (by omega), sh_lo 18 (by omega), e16, e5, e18]
            exact hS')
    · have hsh1 : sh = 1 := by
        by_contra h
        rw [a142, e133, c141, tb_word_one, show sh = 0 by omega, pow_zero, e_add_self] at hne
        exact hne rfl
      obtain ⟨D, hD, hxD, hS'⟩ := hodd hsh1
      rw [hsh1] at e140
      rw [Stmt.holdsList_rename]
      refine rtc_two hArms hk2 rfl (by rw [sh_lo 46 (by omega)]; exact e59)
        (by rw [sh_lo 62 (by omega)]; exact e63)
        (by rw [hcapSh]; exact hcapP)
        (by rw [sh_lo 42 (by omega)]; exact z42) (by rw [sh_lo 43 (by omega)]; exact z43)
        (by rw [sh_lo 44 (by omega)]; exact z44) (by rw [sh_lo 45 (by omega)]; exact z45) hD
        (by rw [sh_lo 5 (by omega), e5]; exact hxD)
        (by rw [h140, sh_lo 16 (by omega)]; exact e140)
        (by rw [sh_lo 18 (by omega), e18]; exact hrow1 hsh1)
        (by rw [sh_lo 16 (by omega), sh_lo 5 (by omega), sh_lo 18 (by omega), e16, e5, e18]
            exact hS')
  -- the radix-four layers
  have m399 := good_mul (g 252 (.mul (.n (val% «verify_bus_gkr» "n_four~0")) (.n (val% «verify_bus_gkr» "four_bounds")) (.n (val% «verify_bus_gkr» "g_bus_mu"))) (by decide +kernel) rfl) (by omega)
    (by omega)
  obtain ⟨e400, l400⟩ := good_read (g 253 (.load (.n (val% «verify_bus_gkr» "n_four")) (.n (val% «verify_bus_gkr» "n_four~0")) 0) (by decide +kernel) rfl)
    (by decide +kernel) (show LoadHolds rd (σ (.n (val% «verify_bus_gkr» "n_four~0"))) 0 (gen ^ (m / 4)) by
      rw [m399, e66, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]
      have := hbk depth (by omega)
      rwa [show (depth - 1) / 8 = m / 4 by omega] at this)
  have m401 := good_mul (g 254 (.mul (.n (val% «verify_bus_gkr» "rem_g~0")) (.n (val% «verify_bus_gkr» "four_rem")) (.n (val% «verify_bus_gkr» "g_bus_mu"))) (by decide +kernel) rfl) (by omega)
    (by omega)
  obtain ⟨e402, l402⟩ := good_read (g 255 (.load (.n (val% «verify_bus_gkr» "rem_g")) (.n (val% «verify_bus_gkr» "rem_g~0")) 0) (by decide +kernel) rfl)
    (by decide +kernel) (show LoadHolds rd (σ (.n (val% «verify_bus_gkr» "rem_g~0"))) 0 (gen ^ (m % 4)) by
      rw [m401, e67, e6, tb_loadHolds_mul_gen_pow, Nat.add_zero]
      have := hrk depth (by omega)
      rwa [show ((depth - 1) / 2) % 4 = m % 4 by omega] at this)
  have m403 := good_mul (g 256 (.mul (.n (val% «verify_bus_gkr» "n_pairs~0")) (.n (val% «verify_bus_gkr» "n_four")) (.n (val% «verify_bus_gkr» "n_four"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m404 := good_mul (g 257 (.mul (.n (val% «verify_bus_gkr» "n_pairs~1")) (.n (val% «verify_bus_gkr» "n_pairs~0")) (.n (val% «verify_bus_gkr» "n_pairs~0"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m405 := good_mul (g 258 (.mul (.n (val% «verify_bus_gkr» "n_pairs")) (.n (val% «verify_bus_gkr» "n_pairs~1")) (.n (val% «verify_bus_gkr» "rem_g"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e366 : σ (.n (val% «verify_bus_gkr» "n_pairs")) = gen ^ m := by
    rw [m405, m404, m403, e400, e402]
    conv_rhs => rw [← Nat.div_add_mod m 4]
    ring
  have e406 : σ (.n (val% «verify_bus_gkr» "done")) = 0 := by
    have h := vb_goodS hG 259 (.dispatch (.n (val% «verify_bus_gkr» "odd_g")) [glcLsN 0, glcLsN 1] [.n (val% «verify_bus_gkr» "layers"), .n (val% «verify_bus_gkr» "rounds"), .n (val% «verify_bus_gkr» "gkr_pts"),
      .n (val% «verify_bus_gkr» "n_four"), .n (val% «verify_bus_gkr» "rem_g"), .n (val% «verify_bus_gkr» "start_g"), .n (val% «verify_bus_gkr» "g_bus_mu"), .n (val% «verify_bus_gkr» "tabs"), .n (val% «verify_bus_gkr» "stream")] [.n (val% «verify_bus_gkr» "done")]) (by decide +kernel) rfl
    have h' : σ (.n (val% «verify_bus_gkr» "done")) = W 402 := h (.n (val% «verify_bus_gkr» "done")) List.mem_cons_self
    rw [h']; simp [hW, vbgW]
  have R8 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR8 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR8, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    refine ⟨m399, l400, m401, l402, m403, m404, m405, ⟨sh, by simp; omega, by
      rw [e133]; exact gen_pow_eq_ofK sh, ?_⟩⟩
    have hL := gls_complete (rd := rd) (o := sh) (n := m / 4) (r := m % 4) (by omega) (by omega)
      (by omega) (layers := layers) (rounds := rounds) (pts := rows) (start := gen ^ (2 - sh))
      (gmu := gen ^ depth) (tabs := tabs) (stream := stream)
      (fun j hj ↦ glc_lay (by omega) (by omega) (hit j (by omega)))
    simp only [List.map_cons, List.map_nil]
    rw [e16, e17, e18, e400, e402, e135, e6, e8, e9, e406]
    rcases (by omega : sh = 0 ∨ sh = 1) with h | h <;> simp only [h] at hL ⊢ <;> exact hL
  -- the last slot, the last row, the point's copy, the values' buffer
  obtain ⟨hclF, hcapF, -, hcurF, hvlF, hvalF, hplF, hptF, -⟩ := hlast
  have m370 := good_mul (g 260 (.mul (.n (val% «verify_bus_gkr» "last~0")) (.n (val% «verify_bus_gkr» "n_pairs")) (.n (val% «verify_bus_gkr» "n_pairs"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m371 := good_mul (g 261 (.mul (.n (val% «verify_bus_gkr» "last~1")) (.n (val% «verify_bus_gkr» "last~0")) (.n (val% «verify_bus_gkr» "start_g"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m372 := good_mul (g 262 (.mul (.n (val% «verify_bus_gkr» "last~2")) (.n (val% «verify_bus_gkr» "last~1")) (.n (val% «verify_bus_gkr» "last~1"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m373 := good_mul (g 263 (.mul (.n (val% «verify_bus_gkr» "last~3")) (.n (val% «verify_bus_gkr» "last~2")) (.n (val% «verify_bus_gkr» "last~2"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m374 := good_mul (g 264 (.mul (.n (val% «verify_bus_gkr» "last~4")) (.n (val% «verify_bus_gkr» "last~3")) (.n (val% «verify_bus_gkr» "last~1"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m375 := good_mul (g 265 (.mul (.n (val% «verify_bus_gkr» "last~5")) (.n (val% «verify_bus_gkr» "last~4")) (.n (val% «verify_bus_gkr» "last~4"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m376 := good_mul (g 266 (.mul (.n (val% «verify_bus_gkr» "last")) (.n (val% «verify_bus_gkr» "layers")) (.n (val% «verify_bus_gkr» "last~5"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e371 : σ (.n (val% «verify_bus_gkr» "last~1")) = gen ^ depth := by
    rw [m371, m370, e366, e135, ← pow_add, ← pow_add,
      show m + m + (2 - sh) = depth by omega]
  have e376 : σ (.n (val% «verify_bus_gkr» "last")) = layers * gen ^ (10 * depth) := by
    rw [m376, m375, m374, m373, m372, e371, e16, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have ld : ∀ k v, LoadHolds rd layers (10 * depth + k) v → LoadHolds rd (σ (.n (val% «verify_bus_gkr» "last"))) k v :=
    fun k v h => by rw [e376, tb_loadHolds_mul_gen_pow]; exact h
  obtain ⟨e377, l377⟩ := good_read (g 267 (.load (.n (val% «verify_bus_gkr» "cursor@2")) (.n (val% «verify_bus_gkr» "last")) 5) (by decide +kernel) rfl)
    (by decide +kernel) (ld 5 _ hcurF)
  have c378 : σ (.n (val% «verify_bus_gkr» "final_point_row~0")) = word 2 0 := g 268 (.const (.n (val% «verify_bus_gkr» "final_point_row~0")) (word 2 0)) (by decide +kernel) rfl
  have m379 := good_mul (g 269 (.mul (.n (val% «verify_bus_gkr» "final_point_row~1")) (.n (val% «verify_bus_gkr» "n_pairs")) (.n (val% «verify_bus_gkr» "final_point_row~0"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m380 := good_mul (g 270 (.mul (.n (val% «verify_bus_gkr» "final_point_row~2")) (.n (val% «verify_bus_gkr» "final_point_row~1")) (.n (val% «verify_bus_gkr» "final_point_row~1"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m381 := good_mul (g 271 (.mul (.n (val% «verify_bus_gkr» "final_point_row~3")) (.n (val% «verify_bus_gkr» "final_point_row~2")) (.n (val% «verify_bus_gkr» "final_point_row~2"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m382 := good_mul (g 272 (.mul (.n (val% «verify_bus_gkr» "final_point_row~4")) (.n (val% «verify_bus_gkr» "final_point_row~3")) (.n (val% «verify_bus_gkr» "final_point_row~1"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m383 := good_mul (g 273 (.mul (.n (val% «verify_bus_gkr» "final_point_row~5")) (.n (val% «verify_bus_gkr» "final_point_row~4")) (.n (val% «verify_bus_gkr» "final_point_row~4"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m384 := good_mul (g 274 (.mul (.n (val% «verify_bus_gkr» "final_point_row~6")) (.n (val% «verify_bus_gkr» "final_point_row~5")) (.n (val% «verify_bus_gkr» "final_point_row~5"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m385 := good_mul (g 275 (.mul (.n (val% «verify_bus_gkr» "final_point_row~7")) (.n (val% «verify_bus_gkr» "final_point_row~6")) (.n (val% «verify_bus_gkr» "final_point_row~6"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have m386 := good_mul (g 276 (.mul (.n (val% «verify_bus_gkr» "final_point_row")) (.n (val% «verify_bus_gkr» "gkr_pts")) (.n (val% «verify_bus_gkr» "final_point_row~7"))) (by decide +kernel) rfl)
    (by omega) (by omega)
  have e386 : σ (.n (val% «verify_bus_gkr» "final_point_row")) = rows * gen ^ (40 * (m + 1)) := by
    rw [m386, m385, m384, m383, m382, m381, m380, m379, c378, tb_word_gen, e366, e18, ← pow_succ]
    ring
  have c387 : σ (.n (val% «verify_bus_gkr» "s34#0")) = word 1 0 := g 277 (.const (.n (val% «verify_bus_gkr» "s34#0")) (word 1 0)) (by decide +kernel) rfl
  have a388 : σ (.n (val% «verify_bus_gkr» "s34#1")) = σ (.n (val% «verify_bus_gkr» "s34#0")) + σ (.n (val% «verify_bus_gkr» "g_bus_mu")) :=
    g 278 (.add (.n (val% «verify_bus_gkr» "s34#1")) (.n (val% «verify_bus_gkr» "s34#0")) (.n (val% «verify_bus_gkr» "g_bus_mu"))) (by decide +kernel) rfl
  have c389 : σ (.n (val% «verify_bus_gkr» "s34#2")) = word 1 0 := g 279 (.const (.n (val% «verify_bus_gkr» "s34#2")) (word 1 0)) (by decide +kernel) rfl
  have e390 : σ (.n (val% «verify_bus_gkr» "leaves")) = vals := by
    have h : σ (.n (val% «verify_bus_gkr» "leaves")) = W 423 := g 281 (.hint (.alloc (.n (val% «verify_bus_gkr» "leaves")) 3)) (by decide +kernel) rfl
    rw [h]; simp [hW, vbgW]
  obtain ⟨v0, v1, v2, hv3⟩ := tb_list3_eq hvlF
  have hvk : ∀ k < 3, LoadHolds rd vals k (stF.values.getD k 0) := fun k hk => by
    have := hv k (by rw [hvlF]; exact hk)
    rwa [← List.getD_eq_getElem _ 0] at this
  obtain ⟨e391, l391⟩ := good_read (g 282 (.load (.n (val% «verify_bus_gkr» "s36.u0.s0#0")) (.n (val% «verify_bus_gkr» "last")) 6) (by decide +kernel) rfl)
    (by decide +kernel) (ld 6 _ (hvalF 0 (by omega)))
  obtain ⟨e392, l392⟩ := good_read (g 284 (.load (.n (val% «verify_bus_gkr» "s36.u1.s0#0")) (.n (val% «verify_bus_gkr» "last")) 7) (by decide +kernel) rfl)
    (by decide +kernel) (ld 7 _ (hvalF 1 (by omega)))
  obtain ⟨e393, l393⟩ := good_read (g 286 (.load (.n (val% «verify_bus_gkr» "s36.u2.s0#0")) (.n (val% «verify_bus_gkr» "last")) 8) (by decide +kernel) rfl)
    (by decide +kernel) (ld 8 _ (hvalF 2 (by omega)))
  have gC := vb_goodB hG 288 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n ((val% «verify_bus_gkr» "s37#0") + k)) (.n (val% «verify_bus_gkr» "last")) k)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have kC : ∀ k < 5, some (427 + k, 409, k) ∉ vbgS.map loadKey := by decide +kernel
  have rC : ∀ k < 5, σ (.n ((val% «verify_bus_gkr» "s37#0") + k)) = sF.cap.getD k 0 ∧
      LoadHolds rd (σ (.n (val% «verify_bus_gkr» "last"))) k (σ (.n ((val% «verify_bus_gkr» "s37#0") + k))) := fun k hk =>
    good_readS (gC _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (kC k hk)
      (ld k _ (hcapF k hk))
  have q399 : σ (.n (val% «verify_bus_gkr» "s37#0[5]")) = σ (.n (val% «verify_bus_gkr» "cursor@2")) := g 293 (.copy (.n (val% «verify_bus_gkr» "s37#0[5]")) (.n (val% «verify_bus_gkr» "cursor@2"))) (by decide +kernel) rfl
  have q400 : σ (.n (val% «verify_bus_gkr» "s37#0[6]")) = σ (.n (val% «verify_bus_gkr» "leaves")) := g 294 (.copy (.n (val% «verify_bus_gkr» "s37#0[6]")) (.n (val% «verify_bus_gkr» "leaves"))) (by decide +kernel) rfl
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
      IsEmpty.forall_iff, implies_true, and_true, and_assoc, keccakA]
    exact ⟨c37, a38, trivial,
      show σ (.n (val% «verify_bus_gkr» "s12#3")) = σ (.n (val% «verify_bus_gkr» "s12#1")) * σ (.n (val% «verify_bus_gkr» "s12#2")) ∧ σ (.n (val% «verify_bus_gkr» "s12#3")) = 1 from
        ⟨m40, by rw [m40, i39, mul_inv_cancel₀ (by rw [e38]; exact hcnt)]⟩,
      c41, c42, c43, c44, c45, k35, m60, a61, m62, a63⟩
  have R5 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR5 True
      (fun rs => rs = sF.cap ++ [curF, vals]) :=
    holdsList_straightN _ (by decide +kernel) (fun s hs ↦ by
      rcases List.mem_append.mp hs with h | h
      · exact T0 s h
      · exact forall_flatten_range TB s h) trivial
  have R6 : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbR6 True
      (fun rs => rs = sF.cap ++ [curF, vals]) := by
    refine holdsList_straightN _ (by decide +kernel) ?_ trivial
    simp only [vbR6, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    exact ⟨m132, l133, c134, show σ (.n (val% «verify_bus_gkr» "start_g~0")) = σ (.n (val% «verify_bus_gkr» "start_g")) * σ (.n (val% «verify_bus_gkr» "odd_g")) by
        rw [d135, mul_assoc, inv_mul_cancel₀ (by rw [e133]; exact gen_pow_ne_zero _), mul_one],
      m136, m137, m138, m139, m140, c141, a142⟩
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
    · show coreProgram.Rel rd name% «verify_bus_gkr_loop0» (List.map σ [.n (val% «verify_bus_gkr» "s34#2"), .n (val% «verify_bus_gkr» "g_bus_mu"), .n (val% «verify_bus_gkr» "zeta"),
        .n (val% «verify_bus_gkr» "final_point_row")]) []
      simp only [List.map_cons, List.map_nil]
      rw [c389, tb_word_one, e6, e7, e386]
      exact l8_complete (by omega) (by omega) hplF hptF hz
    · show LoadHolds rd (σ (.n (val% «verify_bus_gkr» "leaves"))) 0 (σ (.n (val% «verify_bus_gkr» "s36.u0.s0#0")))
      rw [e390, e391]; exact hvk 0 (by omega)
    · show LoadHolds rd (σ (.n (val% «verify_bus_gkr» "leaves"))) 1 (σ (.n (val% «verify_bus_gkr» "s36.u1.s0#0")))
      rw [e390, e392]; exact hvk 1 (by omega)
    · show LoadHolds rd (σ (.n (val% «verify_bus_gkr» "leaves"))) 2 (σ (.n (val% «verify_bus_gkr» "s36.u2.s0#0")))
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
  · have hc : ∀ k < 5, σ (.n ((val% «verify_bus_gkr» "s37#0") + k)) = sF.cap.getD k 0 := fun k hk => (rC k hk).1
    rw [hf5] at hc
    have h0 := hc 0 (by omega)
    have h1 := hc 1 (by omega)
    have h2 := hc 2 (by omega)
    have h3 := hc 3 (by omega)
    have h4 := hc 4 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3 h4
    show [σ (.n (val% «verify_bus_gkr» "s37#0")), σ (.n (val% «verify_bus_gkr» "s37#0[1]")), σ (.n (val% «verify_bus_gkr» "s37#0[2]")), σ (.n (val% «verify_bus_gkr» "s37#0[3]")), σ (.n (val% «verify_bus_gkr» "s37#0[4]")), σ (.n (val% «verify_bus_gkr» "s37#0[5]")), σ (.n (val% «verify_bus_gkr» "s37#0[6]"))] =
      sF.cap ++ [curF, vals]
    rw [hf5, h0, h1, h2, h3, h4, q399, q400, e377, e390]
    rfl

end Body

end
end LeanVM.Guest.B1.Tables
