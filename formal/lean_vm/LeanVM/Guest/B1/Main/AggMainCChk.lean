/-
  LeanVM.Guest.B1.Main.AggMainCChk

  `aggregate_claims`' body, evaluated (by kernel evaluation), for its completeness.
-/

module

public import LeanVM.Guest.B1.Main.AggCMath
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `aggregate_claims`' stores: the first absorbing row (the seed, the packed count and zeros),
the first record of `bc_chain` (the power `1`, the claim `0`), `bc_point1`, the first weight `0`,
the claim at `defer_stmt`. -/
def aggStores : List Atom :=
  (List.range 5).map (fun i => .load (.n (10 + i)) (.n 30) i) ++
    (List.range 4).flatMap (fun j => [.load (.n (15 + 2 * j)) (.n 30) (5 + 2 * j),
      .load (.n (16 + 2 * j)) (.n 30) (6 + 2 * j)]) ++
    [.load (.n 96) (.n 95) 0, .load (.n 97) (.n 95) 1] ++
    (List.range 23).map (fun k => .load (.n (116 + 3 * k)) (.n 113) k) ++ [.load (.n 186) (.n 185) 0] ++
    (List.range 23).map (fun k => .load (.n (193 + k)) (.n 4) k) ++ [.load (.n 7) (.n 4) 23]

/-- `aggregate_claims`' loads: the last absorbing row, the nonce, the last record's claim, the
sumcheck's point (for `bc_point1`), the last weight, the sumcheck's point (for `defer_stmt`). -/
def aggLoads : List Atom :=
  (List.range 13).map (fun k => .load (.n (40 + k)) (.n 39) k) ++ [.load (.n 70) (.n 6) 0] ++
    [.load (.n 103) (.n 102) 1] ++
    (List.range 23).map (fun k => .load (.n (115 + 3 * k)) (.n 104) k) ++
    [.load (.n 191) (.n 190) 0] ++ (List.range 23).map (fun k => .load (.n (193 + k)) (.n 104) k)

/-- `aggregate_claims`' hints: the buffers and `bc_star_hint`. -/
def aggHintsA : List Atom :=
  [.hint (.alloc (.n 6) 47), .hint (.witness "bc_star_hint" (.stack [.n 7])),
    .hint (.allocDyn (.n 8) (.n 0)), .hint (.allocDyn (.n 9) (.n 0)),
    .hint (.allocDyn (.n 30) (.n 29)), .hint (.allocDyn (.n 95) (.n 94)),
    .hint (.alloc (.n 104) 23), .hint (.alloc (.n 113) 23), .hint (.allocDyn (.n 185) (.n 184))]

/-- `aggregate_claims`' packs (`fs_pack` of the count and three zeros). -/
def aggPacks : List (V × ℕ) := [(.n 0, 15), (.n 17, 17), (.n 19, 19), (.n 21, 21)]

/-- `aggregate_claims`' calls. -/
def aggCalls : List Stmt :=
  [.callIf (.n 32) name% «aggregate_claims_loop0» [.n 33, .n 0, .n 30, .n 2, .n 8, .n 3, .n 9,
      .n 1],
    .call "grind_check__L2" [.n 79, .n 5] [],
    .callIf (.n 99) name% «aggregate_claims_loop1» [.n 100, .n 0, .n 95, .n 8, .n 9, .n 91, .n 78],
    .call "batch_sumcheck__L23" [.n 86, .n 87, .n 88, .n 89, .n 90, .n 106, .n 103, .n 104, .n 5]
      [.n 107, .n 108, .n 109, .n 110, .n 111, .n 112],
    .callIf (.n 188) name% «aggregate_claims_loop2» [.n 189, .n 0, .n 8, .n 9, .n 113, .n 95,
        .n 185, .n 78]]

/-- `aggregate_claims`' atoms but its stores. -/
noncomputable def aggA : List Atom := (atomsIn aggP).filter fun a => decide (a ∉ aggStores)

theorem mem_aggA {a : Atom} : a ∈ aggA ↔ a ∈ atomsIn aggP ∧ a ∉ aggStores := by
  simp [aggA]

set_option maxRecDepth 100000 in
theorem agg_stores : storesOf 6 (Fn.body fn% «aggregate_claims») = aggStores := by decide +kernel

/-- **`aggregate_claims`' body, evaluated**: its values defined in order, its atoms but its stores
holding from its loads and the final check, its statements atoms or its calls, the sums of
`bc_point1` and the products pure. -/
noncomputable def aggCOk : Bool :=
  let A := atomsIn aggP
  let P := A.filter pureB
  (chk 6 (Fn.body fn% «aggregate_claims»)).isSome &&
  aggA.all (fun a => !needsSide a || decide (a ∈ aggLoads) || decide (a = .assertEq (.n 112) (.n 192))) &&
  aggPacks.all (fun p => packIn aggA p.1 p.2) &&
  aggLoads.all (fun a => decide (a ∈ aggA)) && aggHintsA.all (fun a => decide (a ∈ A)) &&
  aggP.all (fun s => match s with | .atom _ => true | _ => aggCalls.any (stmtEqb s)) &&
  aggCalls.all (fun c => aggP.any (stmtEqb · c)) &&
  monoIs P (.n 39) (.n 30) (.n 0) 13 && monoIs P (.n 102) (.n 95) (.n 0) 2 &&
  isMul P (.n 190) (.n 185) (.n 0) && isMul P (.n 192) (.n 7) (.n 191) && genMulOk P (.n 106) (.n 6) &&
  isMul P (.n 91) (.n 78) (.n 78) &&
  (List.range 23).all (fun k => P.any (isAddAt (.n (116 + 3 * k)) (.n (114 + 3 * k)) (.n (115 + 3 * k))))

set_option maxRecDepth 100000 in
theorem aggc_ok : aggCOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
