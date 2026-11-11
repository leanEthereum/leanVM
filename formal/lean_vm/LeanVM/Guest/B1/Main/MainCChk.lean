/-
  LeanVM.Guest.B1.Main.MainCChk

  `main`'s body as one evaluated block (by kernel evaluation), for its completeness.
-/

module

public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# `main`'s body, evaluated

`mFlat` is `main`'s body with both branches of the direct DA check and the leaf's branch inlined
(`mPre`, `mDa`, `mDaZ`, `mMid`, `mLeaf`, `mPost`), every value defined at its first occurrence
(`chk`); the batching's branch defines nothing. The atoms needing a side condition are the range
checks, the loads through `main`'s buffers and the header, the touches through the counts
(`assert_gpow`), and the four equality checks
(`mSideOk`); the only `KECCAK` is the own DA claim's digest, on `da_verify`'s returns
(`canonChk`), each block checked on its own.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `main`'s body, both branches of each conditional block inlined. -/
noncomputable def mFlat : List Stmt := mPre ++ mDa ++ mDaZ ++ mMid ++ mLeaf ++ mPost

/-- The evaluated block: `mFlat` itself (`main` hints no inverse). -/
noncomputable def mFlatE : List Stmt := mFlat

/-- `main`'s stores: the byte table, the own DA digest (both branches), the first running count,
the leaf's deferred claim. -/
def mStoresL : List Atom :=
  (List.range 256).map (fun v => .load (.n (48 + v)) (.n 47) v) ++
    [.load (.n 379) (.n 366) 0, .load (.n 380) (.n 366) 1, .load (.n 381) (.n 366) 0,
      .load (.n 382) (.n 366) 1, .load (.n 400) (.n 399) 0] ++
    (List.range 23).map (fun k => .load (.n (421 + k)) (.n 417) k) ++ [.load (.n 420) (.n 417) 23]

/-- `main`'s loads, by their words' numbers: the five reads, then the stores. -/
def mLoadOk (d p o : ℕ) : Bool :=
  decide ((d, p, o) ∈ [(405, 404, 0), (444, 416, 0), (445, 416, 1), (449, 448, 0),
    (453, 452, 0)]) ||
  (decide (p = 47) && decide (d = 48 + o) && decide (o < 256)) ||
  decide ((d, p, o) ∈ [(379, 366, 0), (380, 366, 1), (381, 366, 0), (382, 366, 1),
    (400, 399, 0)]) ||
  (decide (p = 417) && (decide (o < 23 ∧ d = 421 + o) || decide (o = 23 ∧ d = 420)))

/-- The range checks: the checked value and the bound's constant. -/
def rcPairs : List (ℕ × ℕ) :=
  [(6, 14), (7, 18), (406, 6)]

/-- The atoms of `main` whose side conditions its completeness discharges. -/
def mSideOk : Atom → Bool
  | .rangeCheck x y _ _ k => decide ((x.idx, k.idx) ∈ rcPairs) && decide (x = .n x.idx) &&
      decide (k = .n k.idx) && decide (k.idx < y.idx)
  | .load d p o => decide (d = .n d.idx) && decide (p = .n p.idx) && mLoadOk d.idx p.idx o
  | .touch t p => decide (t = .n t.idx) && decide (p = .n p.idx) &&
      decide ((t.idx, p.idx) ∈ [(8, 0), (9, 1), (10, 2), (11, 3), (12, 4), (13, 5), (25, 24)])
  | .assertEq x y => decide ((x, y) ∈ [(V.n 405, V.n 24), (.n 413, .n 414), (.n 449, .n 446),
      (.n 453, .n 447)])
  | _ => false

/-- The stores of `main`'s body. -/
noncomputable def mStores : List Atom := storesOf 0 mFlatE

/-- A block's atoms but the stores. -/
noncomputable def noStores (P : List Stmt) : List Atom :=
  (atomsIn P).filter fun a => decide (a ∉ mStores)

/-- **`main`'s body, evaluated.** -/
noncomputable def mainCOk : Bool :=
  (chk 0 mFlatE).isSome &&
  canonChk [] (noStores (mPre ++ mMid ++ mPost)) &&
  canonChk [369, 370, 371, 372] (noStores mDa) && canonChk [] (noStores mDaZ) &&
  canonChk [] (noStores mLeaf) &&
  (atomsIn mFlat).all (fun a => !needsSide a || mSideOk a)

set_option maxRecDepth 100000 in
theorem mainc_ok : mainCOk = true := by decide +kernel

/-- The statements defining `main`'s oracle values: hints, `HeapBuf`s, calls' returns. -/
def mOrcStmts : List Stmt :=
  [.atom (.hint (.witness "meta" (.stack [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]))),
    .atom (.hint (.witness "fs_seed" (.stack [.n 26, .n 27]))),
    .call "exponent_tables" [] [.n 28], .atom (.hint (.allocDyn (.n 31) (.n 30))),
    .atom (.hint (.allocDyn (.n 34) (.n 33))),
    .call "claim_list_digest" [.n 31, .n 0] [.n 35, .n 36],
    .call "claim_list_digest" [.n 34, .n 3] [.n 37, .n 38],
    .atom (.hint (.allocDyn (.n 45) (.n 24))), .atom (.hint (.alloc (.n 47) 256)),
    .atom (.hint (.allocDyn (.n 364) (.n 363))),
    .call "da_verify" [.n 28] [.n 369, .n 370, .n 371, .n 372],
    .atom (.hint (.allocDyn (.n 384) (.n 383))), .atom (.hint (.allocDyn (.n 390) (.n 389))),
    .atom (.hint (.allocDyn (.n 396) (.n 395))), .atom (.hint (.allocDyn (.n 399) (.n 398))),
    .atom (.hint (.witness "da_pick" (.stack [.n 406]))),
    .atom (.hint (.alloc (.n 417) 24)), .atom (.hint (.witness "leaf_defer" (.stack [.n 420]))),
    .call "statement_digest" [.n 26, .n 27, .n 35, .n 36, .n 37, .n 38, .n 444, .n 445, .n 417]
      [.n 446, .n 447]]

/-- The atoms defining `main`'s words the proof reads. -/
def mDefAtoms : List Atom :=
  [.mul (.n 22) (.n 0) (.n 1), .mul (.n 23) (.n 3) (.n 4), .mul (.n 24) (.n 22) (.n 23),
    .mul (.n 29) (.n 22) (.n 22), .mul (.n 30) (.n 29) (.n 29),
    .mul (.n 32) (.n 23) (.n 23), .mul (.n 33) (.n 32) (.n 32), .mul (.n 46) (.n 45) (.n 22),
    .const (.n 39) (word 1 0 0), .add (.n 40) (.n 39) (.n 1), .const (.n 41) (word 1 0 0),
    .const (.n 42) (word 1 0 0), .add (.n 43) (.n 42) (.n 4), .const (.n 44) (word 1 0 0),
    .const (.n 355) (word 1 0 0), .add (.n 356) (.n 355) (.n 2), .const (.n 357) (word 1 0 0),
    .const (.n 358) (word 1 0 0), .add (.n 359) (.n 358) (.n 5), .const (.n 360) (word 1 0 0),
    .const (.n 361) (word 2 0 0), .mul (.n 362) (.n 6) (.n 361), .mul (.n 363) (.n 362) (.n 362),
    .mul (.n 365) (.n 6) (.n 6), .mul (.n 366) (.n 364) (.n 365),
    .const (.n 367) (word 2 0 0), .add (.n 368) (.n 7) (.n 367),
    .mul (.n 383) (.n 6) (.n 6), .mul (.n 385) (.n 6) (.n 6), .mul (.n 386) (.n 385) (.n 6),
    .mul (.n 387) (.n 386) (.n 386), .mul (.n 388) (.n 387) (.n 387),
    .mul (.n 389) (.n 388) (.n 388), .mul (.n 391) (.n 6) (.n 6), .mul (.n 392) (.n 391) (.n 6),
    .mul (.n 393) (.n 392) (.n 392), .mul (.n 394) (.n 393) (.n 393),
    .mul (.n 395) (.n 394) (.n 394), .const (.n 397) (word 2 0 0), .mul (.n 398) (.n 6) (.n 397),
    .mul (.n 400) (.n 2) (.n 5), .const (.n 401) (word 1 0 0), .add (.n 402) (.n 401) (.n 6),
    .const (.n 403) (word 1 0 0), .mul (.n 404) (.n 399) (.n 6),
    .add (.n 410) (.n 406) (.n 6), .const (.n 411) (word 1 0 0), .add (.n 412) (.n 7) (.n 411),
    .mul (.n 413) (.n 410) (.n 412), .const (.n 414) (word 0 0 0),
    .mul (.n 415) (.n 406) (.n 406), .mul (.n 416) (.n 364) (.n 415),
    .const (.n 418) (word 1 0 0), .add (.n 419) (.n 6) (.n 418),
    .const (.n 448) (word 1 0 0), .const (.n 450) (word 1 0 0), .const (.n 451) (word 2 0 0),
    .mul (.n 452) (.n 450) (.n 451),
    .const (.n 14) (word 65536 0 0), .const (.n 18) (word 2 0 0),
    .load (.n 405) (.n 404) 0, .load (.n 444) (.n 416) 0, .load (.n 445) (.n 416) 1,
    .load (.n 449) (.n 448) 0, .load (.n 453) (.n 452) 0] ++
  (List.range 51).map fun j => .const (.n (304 + j)) (word (lxTagVals.getD j 0) 0 0)

end
end LeanVM.Guest.B1.Main
