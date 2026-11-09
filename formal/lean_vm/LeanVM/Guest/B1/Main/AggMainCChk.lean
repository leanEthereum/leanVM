/-
  LeanVM.Guest.B1.Main.AggMainCChk

  `aggregate_claims`' body, evaluated (by kernel evaluation), for its completeness.
-/

module

public import LeanVM.Guest.B1.Main.AggCMath

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `aggregate_claims`' stores: the first absorbing row (the seed, the packed count and zeros),
the first record of `bc_chain` (the power `1`, the claim `0`), `bc_point1`, the first weight `0`,
the claim at `defer_stmt`. -/
def aggStores : List Atom :=
  (List.range 5).map (fun i => .load (.n (9 + i)) (.n 60) i) ++
    [.load (.n 20) (.n 60) 5, .load (.n 22) (.n 60) 6, .load (.n 30) (.n 60) 7,
      .load (.n 32) (.n 60) 8, .load (.n 40) (.n 60) 9, .load (.n 42) (.n 60) 10,
      .load (.n 50) (.n 60) 11, .load (.n 52) (.n 60) 12] ++
    [.load (.n 112) (.n 111) 0, .load (.n 113) (.n 111) 1] ++
    (List.range 23).map (fun k => .load (.n (130 + 3 * k)) (.n 127) k) ++ [.load (.n 200) (.n 199) 0] ++
    (List.range 23).map (fun k => .load (.n (207 + k)) (.n 4) k) ++ [.load (.n 6) (.n 4) 23]

/-- `aggregate_claims`' loads: the last absorbing row, the last record's claim, the sumcheck's
point (for `bc_point1`), the last weight, the sumcheck's point (for `defer_stmt`). -/
def aggLoads : List Atom :=
  (List.range 13).map (fun k => .load (.n (70 + k)) (.n 69) k) ++ [.load (.n 119) (.n 118) 1] ++
    (List.range 23).map (fun k => .load (.n (129 + 3 * k)) (.n 120) k) ++
    [.load (.n 205) (.n 204) 0] ++ (List.range 23).map (fun k => .load (.n (207 + k)) (.n 120) k)

/-- `aggregate_claims`' hints: the buffers and `bc_star_hint`. -/
def aggHintsA : List Atom :=
  [.hint (.alloc (.n 5) 46), .hint (.witness "bc_star_hint" (.stack [.n 6])),
    .hint (.allocDyn (.n 7) (.n 0)), .hint (.allocDyn (.n 8) (.n 0)),
    .hint (.allocDyn (.n 60) (.n 59)), .hint (.allocDyn (.n 111) (.n 110)),
    .hint (.alloc (.n 120) 23), .hint (.alloc (.n 127) 23), .hint (.allocDyn (.n 199) (.n 198))]

/-- `aggregate_claims`' packs (`fs_pack` of the count and three zeros): its limb hints but `λ`'s
(`challenge_from_state`'s on `.n 88`). -/
def aggPacks : List (V × ℕ) := [(.n 0, 14), (.n 23, 24), (.n 33, 34), (.n 43, 44)]

/-- `aggregate_claims`' calls. -/
def aggCalls : List Stmt :=
  [.callIf (.n 62) "__loop33" [.n 63, .n 0, .n 60, .n 2, .n 7, .n 3, .n 8, .n 1],
    .callIf (.n 115) "__loop34" [.n 116, .n 0, .n 111, .n 7, .n 8, .n 107, .n 106],
    .call "batch_sumcheck__L23" [.n 95, .n 96, .n 97, .n 98, .n 99, .n 5, .n 119, .n 120]
      [.n 121, .n 122, .n 123, .n 124, .n 125, .n 126],
    .callIf (.n 202) "__loop35" [.n 203, .n 0, .n 7, .n 8, .n 127, .n 111, .n 199, .n 106]]

/-- `aggregate_claims`' atoms but its stores. -/
noncomputable def aggA : List Atom := (atomsIn aggP).filter fun a => decide (a ∉ aggStores)

theorem mem_aggA {a : Atom} : a ∈ aggA ↔ a ∈ atomsIn aggP ∧ a ∉ aggStores := by
  simp [aggA]

set_option maxRecDepth 100000 in
theorem agg_stores : storesOf 5 (Fn.body Data.core33) = aggStores := by decide +kernel

/-- **`aggregate_claims`' body, evaluated**: its values defined in order, its atoms but its stores
holding from its loads, its packs and the final check, its statements atoms or its calls, the
sums of `bc_point1` pure. -/
noncomputable def aggCOk : Bool :=
  let A := atomsIn aggP
  let P := A.filter pureB
  (chk 5 (Fn.body Data.core33)).isSome && canonChk ((List.range 13).map (70 + ·)) aggA &&
  aggA.all (fun a => !needsSide a || isPackInK aggPacks a || decide (a ∈ aggLoads) ||
    decide (a = .assertInK (.n 100) (.n 103)) || decide (a = .assertEq (.n 126) (.n 206))) &&
  aggPacks.all (fun p => packIn aggA p.1 p.2) &&
  aggLoads.all (fun a => decide (a ∈ aggA)) && aggHintsA.all (fun a => decide (a ∈ A)) &&
  aggP.all (fun s => match s with | .atom _ => true | _ => aggCalls.any (stmtEqb s)) &&
  aggCalls.all (fun c => aggP.any (stmtEqb · c)) &&
  monoIs P (.n 69) (.n 60) (.n 0) 13 && monoIs P (.n 118) (.n 111) (.n 0) 2 &&
  isMul P (.n 204) (.n 199) (.n 0) && isMul P (.n 206) (.n 6) (.n 205) &&
  (List.range 23).all (fun k => P.any (isAddAt (.n (130 + 3 * k)) (.n (128 + 3 * k)) (.n (129 + 3 * k))))

set_option maxRecDepth 100000 in
theorem aggc_ok : aggCOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
