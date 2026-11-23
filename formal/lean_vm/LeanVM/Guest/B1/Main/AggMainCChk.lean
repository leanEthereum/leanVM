/-
  LeanVM.Guest.B1.Main.AggMainCChk

  `aggregate_claims`' body, evaluated (by kernel evaluation), for its completeness.
-/

module

public import LeanVM.Guest.B1.Main.AggCMath
public import LeanVM.Guest.B1.Main.AggBody
public import LeanVM.Guest.B1.Bits.GrindFwd
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims»

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `aggregate_claims`' stores: the first absorbing row (the seed, the packed count and zeros),
the first record of `bc_chain` (the power `1`, the claim `0`), `bc_point1`, the first weight `0`,
the claim at `defer_stmt`. -/
def aggStores : List Atom :=
  (List.range 5).map (fun i => .load (.n ((val% «aggregate_claims» "seed[0]") + i)) (.n (val% «aggregate_claims» "absorb")) i) ++
    (List.range 4).flatMap (fun j => [.load (.n (15 + 2 * j)) (.n (val% «aggregate_claims» "absorb")) (5 + 2 * j),
      .load (.n (16 + 2 * j)) (.n (val% «aggregate_claims» "absorb")) (6 + 2 * j)]) ++
    [.load (.n (val% «aggregate_claims» "s20#0")) (.n (val% «aggregate_claims» "bc_chain")) 0, .load (.n (val% «aggregate_claims» "s21#0")) (.n (val% «aggregate_claims» "bc_chain")) 1] ++
    (List.range 23).map (fun k => .load (.n (180 + 3 * k)) (.n (val% «aggregate_claims» "bc_point1")) k) ++ [.load (.n (val% «aggregate_claims» "s30#0")) (.n (val% «aggregate_claims» "bc_wsum")) 0] ++
    (List.range 23).map (fun k => .load (.n ((val% «aggregate_claims» "s33.u0.s0#0") + k)) (.n (val% «aggregate_claims» "defer_stmt")) k) ++ [.load (.n (val% «aggregate_claims» "bytecode_star")) (.n (val% «aggregate_claims» "defer_stmt")) 23]

/-- `aggregate_claims`' loads: the last absorbing row, the nonce, the last record's claim, the
sumcheck's point (for `bc_point1`), the last weight, the sumcheck's point (for `defer_stmt`). -/
def aggLoads : List Atom :=
  (List.range 13).map (fun k => .load (.n ((val% «aggregate_claims» "sp[0]") + k)) (.n (val% «aggregate_claims» "absorbed")) k) ++ [.load (.n (val% «aggregate_claims» "s16.e.s1#0")) (.n (val% «aggregate_claims» "bc_msgs")) 0] ++
    [.load (.n (val% «aggregate_claims» "bc_running@1")) (.n (val% «aggregate_claims» "bc_end")) 1] ++
    (List.range 23).map (fun k => .load (.n (179 + 3 * k)) (.n (val% «aggregate_claims» "bc_point")) k) ++
    [.load (.n (val% «aggregate_claims» "s32#1")) (.n (val% «aggregate_claims» "s32#0")) 0] ++ (List.range 23).map (fun k => .load (.n ((val% «aggregate_claims» "s33.u0.s0#0") + k)) (.n (val% «aggregate_claims» "bc_point")) k)

/-- `aggregate_claims`' hints: the buffers and `bc_star_hint`. -/
def aggHintsA : List Atom :=
  [.hint (.alloc (.n (val% «aggregate_claims» "bc_msgs")) 47), .hint (.witness "bc_star_hint" (.stack [.n (val% «aggregate_claims» "bytecode_star")])),
    .hint (.allocDyn (.n (val% «aggregate_claims» "fresh_row")) (.n (val% «aggregate_claims» "n_children_g"))), .hint (.allocDyn (.n (val% «aggregate_claims» "carried_row")) (.n (val% «aggregate_claims» "n_children_g"))),
    .hint (.allocDyn (.n (val% «aggregate_claims» "absorb")) (.n (val% «aggregate_claims» "absorb~6"))), .hint (.allocDyn (.n (val% «aggregate_claims» "bc_chain")) (.n (val% «aggregate_claims» "bc_chain~2"))),
    .hint (.alloc (.n (val% «aggregate_claims» "bc_point")) 23), .hint (.alloc (.n (val% «aggregate_claims» "bc_point1")) 23), .hint (.allocDyn (.n (val% «aggregate_claims» "bc_wsum")) (.n (val% «aggregate_claims» "bc_wsum~1")))]

/-- `aggregate_claims`' packs (`fs_pack` of the count and three zeros). -/
def aggPacks : List (V × ℕ) := [(.n (val% «aggregate_claims» "n_children_g"), 15), (.n (val% «aggregate_claims» "rate[2]"), 17), (.n (val% «aggregate_claims» "rate[4]"), 19), (.n (val% «aggregate_claims» "rate[6]"), 21)]

/-- `aggregate_claims`' calls. -/
def aggCalls : List Stmt :=
  [.callIf (.n (val% «aggregate_claims» "s12#1")) name% «aggregate_claims_loop0» [.n (val% «aggregate_claims» "s12#2"), .n (val% «aggregate_claims» "n_children_g"), .n (val% «aggregate_claims» "absorb"), .n (val% «aggregate_claims» "child_fresh"), .n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "child_carried"), .n (val% «aggregate_claims» "carried_row"),
      .n (val% «aggregate_claims» "child_pi")],
    .callIf (.n (val% «aggregate_claims» "s22#1")) name% «aggregate_claims_loop1» [.n (val% «aggregate_claims» "s22#2"), .n (val% «aggregate_claims» "n_children_g"), .n (val% «aggregate_claims» "bc_chain"), .n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "carried_row"), .n (val% «aggregate_claims» "lam_sq"), .n (val% «aggregate_claims» "fs_perm.nxt[0]")],
    .call "batch_sumcheck__L23" [.n (val% «aggregate_claims» "fs_perm.nxt[8]"), .n (val% «aggregate_claims» "fs_perm.nxt[9]"), .n (val% «aggregate_claims» "fs_perm.nxt[10]"), .n (val% «aggregate_claims» "fs_perm.nxt[11]"), .n (val% «aggregate_claims» "fs_perm.nxt[12]"), .n (val% «aggregate_claims» "fs0~7"), .n (val% «aggregate_claims» "bc_running@1"), .n (val% «aggregate_claims» "bc_point"), .n (val% «aggregate_claims» "tabs")]
      [.n (val% «aggregate_claims» "fs0"), .n (val% «aggregate_claims» "fs1"), .n (val% «aggregate_claims» "fs2"), .n (val% «aggregate_claims» "fs3"), .n (val% «aggregate_claims» "fs4"), .n (val% «aggregate_claims» "bc_running@2")],
    .callIf (.n (val% «aggregate_claims» "s31#1")) name% «aggregate_claims_loop2» [.n (val% «aggregate_claims» "s31#2"), .n (val% «aggregate_claims» "n_children_g"), .n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "carried_row"), .n (val% «aggregate_claims» "bc_point1"), .n (val% «aggregate_claims» "bc_chain"),
        .n (val% «aggregate_claims» "bc_wsum"), .n (val% «aggregate_claims» "fs_perm.nxt[0]")]]

/-- `aggregate_claims`' atoms but its stores. -/
noncomputable def aggA : List Atom := (atomsIn aggP).filter fun a => decide (a ∉ aggStores)

theorem mem_aggA {a : Atom} : a ∈ aggA ↔ a ∈ atomsIn aggP ∧ a ∉ aggStores := by
  simp [aggA]

set_option maxRecDepth 100000 in
theorem agg_stores : storesOf 6 (Fn.body fn% «aggregate_claims») = aggStores := by decide +kernel

/-- **`aggregate_claims`' body, evaluated**: its values defined in order, its atoms but its stores
holding from its loads, the final check and the inlined grind's, its statements atoms or its calls, the sums of
`bc_point1` and the products pure. -/
noncomputable def aggCOk : Bool :=
  let A := atomsIn aggP
  let P := A.filter pureB
  (chk 6 (Fn.body fn% «aggregate_claims»)).isSome &&
  aggA.all (fun a => !needsSide a || decide (a ∈ aggLoads) || decide (a = .assertEq (.n (val% «aggregate_claims» "bc_running@2")) (.n (val% «aggregate_claims» "s32#2"))) ||
    decide (a ∈ aggGrindA)) &&
  aggPacks.all (fun p => packIn aggA p.1 p.2) &&
  aggLoads.all (fun a => decide (a ∈ aggA)) && aggHintsA.all (fun a => decide (a ∈ A)) &&
  aggP.all (fun s => match s with | .atom _ => true | _ => aggCalls.any (stmtEqb s)) &&
  aggCalls.all (fun c => aggP.any (stmtEqb · c)) &&
  monoIs P (.n (val% «aggregate_claims» "absorbed")) (.n (val% «aggregate_claims» "absorb")) (.n (val% «aggregate_claims» "n_children_g")) 13 && monoIs P (.n (val% «aggregate_claims» "bc_end")) (.n (val% «aggregate_claims» "bc_chain")) (.n (val% «aggregate_claims» "n_children_g")) 2 &&
  isMul P (.n (val% «aggregate_claims» "s32#0")) (.n (val% «aggregate_claims» "bc_wsum")) (.n (val% «aggregate_claims» "n_children_g")) && isMul P (.n (val% «aggregate_claims» "s32#2")) (.n (val% «aggregate_claims» "bytecode_star")) (.n (val% «aggregate_claims» "s32#1")) && genMulOk P (.n (val% «aggregate_claims» "fs0~7")) (.n (val% «aggregate_claims» "bc_msgs")) &&
  isMul P (.n (val% «aggregate_claims» "lam_sq")) (.n (val% «aggregate_claims» "fs_perm.nxt[0]")) (.n (val% «aggregate_claims» "fs_perm.nxt[0]")) &&
  (List.range 23).all (fun k => P.any (isAddAt (.n (180 + 3 * k)) (.n (178 + 3 * k)) (.n (179 + 3 * k))))

set_option maxRecDepth 100000 in
theorem aggc_ok : aggCOk = true := by decide +kernel

/-- `aggregate_claims`' atoms but the inlined grind's. -/
noncomputable def aggA0 : List Atom := (atomsIn aggP).filter fun a => decide (a ∉ aggGrindA)

theorem mem_aggA0 {a : Atom} : a ∈ aggA0 ↔ a ∈ atomsIn aggP ∧ a ∉ aggGrindA := by
  simp [aggA0]

/-- The permutations and the nonce, found among the atoms but the inlined grind's (which reads
the nonce's permutation). -/
noncomputable def aggOk0 : Bool :=
  aggA0.any (isKeccakAt aggKi aggKo false false) && rowInOk aggA0 (.n (val% «aggregate_claims» "absorbed")) aggKi &&
  allIn aggA0 aggNonceA && aggA0.any (isKeccakAt aggNi aggNo false false)

set_option maxRecDepth 100000 in
theorem agg_ok0 : aggOk0 = true := by decide +kernel

/-- The inlined grind's values are not stored into. -/
theorem agg_stores_grind : ∀ a ∈ aggStores, loadInto aggGo (aggGo + (gcLen 2 - 2)) a = false := by
  decide +kernel

end
end LeanVM.Guest.B1.Main
