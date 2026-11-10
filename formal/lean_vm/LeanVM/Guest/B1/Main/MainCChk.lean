/-
  LeanVM.Guest.B1.Main.MainCChk

  `main`'s body as one evaluated block (by kernel evaluation), for its completeness.
-/

module

public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# `main`'s body, evaluated

`mFlat` is `main`'s body with both branches of each conditional block inlined (`mPre`, `mDa`,
`mDaZ`, `mMid`, `mLeaf`, `mAgg`, `mPost`), every value defined at its first occurrence (`chk`).
The atoms needing a side condition are the range checks, the loads through `main`'s buffers and
the header, and the four equality checks (`mSideOk`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- `main`'s body, both branches of each conditional block inlined. -/
noncomputable def mFlat : List Stmt := mPre ++ mDa ++ mDaZ ++ mMid ++ mLeaf ++ mAgg ++ mPost

/-- The evaluated block: `mFlat` itself (`main` hints no inverse). -/
noncomputable def mFlatE : List Stmt := mFlat

/-- `main`'s stores: the byte table, the own DA digest (both branches), the first running count,
the leaf's deferred claim. -/
def mStoresL : List Atom :=
  (List.range 256).map (fun v => .load (.n (69 + v)) (.n 68) v) ++
    [.load (.n 399) (.n 387) 0, .load (.n 400) (.n 387) 1, .load (.n 401) (.n 387) 0,
      .load (.n 402) (.n 387) 1, .load (.n 420) (.n 419) 0] ++
    (List.range 23).map (fun k => .load (.n (441 + k)) (.n 437) k) ++ [.load (.n 440) (.n 437) 23]

/-- `main`'s loads, by their words' numbers: the five reads, then the stores. -/
def mLoadOk (d p o : ℕ) : Bool :=
  decide ((d, p, o) ∈ [(425, 424, 0), (466, 436, 0), (467, 436, 1), (471, 470, 0),
    (475, 474, 0)]) ||
  (decide (p = 68) && decide (d = 69 + o) && decide (o < 256)) ||
  decide ((d, p, o) ∈ [(399, 387, 0), (400, 387, 1), (401, 387, 0), (402, 387, 1),
    (420, 419, 0)]) ||
  (decide (p = 437) && (decide (o < 23 ∧ d = 441 + o) || decide (o = 23 ∧ d = 440)))

/-- The range checks: the checked value and the bound's constant. -/
def rcPairs : List (ℕ × ℕ) :=
  [(0, 8), (1, 12), (2, 16), (3, 20), (4, 24), (5, 28), (6, 32), (7, 36), (42, 43), (426, 6)]

/-- The atoms of `main` whose side conditions its completeness discharges. -/
def mSideOk : Atom → Bool
  | .rangeCheck x y _ _ k => decide ((x.idx, k.idx) ∈ rcPairs) && decide (x = .n x.idx) &&
      decide (k = .n k.idx) && decide (k.idx < y.idx)
  | .load d p o => decide (d = .n d.idx) && decide (p = .n p.idx) && mLoadOk d.idx p.idx o
  | .assertEq x y => decide ((x, y) ∈ [(V.n 425, V.n 42), (.n 433, .n 434), (.n 471, .n 468),
      (.n 475, .n 469)])
  | _ => false

/-- The stores of `main`'s body. -/
noncomputable def mStores : List Atom := storesOf 0 mFlatE

/-- A block's atoms but the stores. -/
noncomputable def noStores (P : List Stmt) : List Atom :=
  (atomsIn P).filter fun a => decide (a ∉ mStores)

/-- **`main`'s body, evaluated.** -/
noncomputable def mainCOk : Bool :=
  (chk 0 mFlatE).isSome &&
  (atomsIn mFlat).all (fun a => !needsSide a || mSideOk a)

set_option maxRecDepth 100000 in
theorem mainc_ok : mainCOk = true := by decide +kernel

/-- The statements defining `main`'s oracle values: hints, `HeapBuf`s, calls' returns. -/
def mOrcStmts : List Stmt :=
  [.atom (.hint (.witness "meta" (.stack [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]))),
    .atom (.hint (.witness "fs_seed" (.stack [.n 47, .n 48]))),
    .call "exponent_tables" [] [.n 49], .atom (.hint (.allocDyn (.n 52) (.n 51))),
    .atom (.hint (.allocDyn (.n 55) (.n 54))),
    .call "claim_list_digest" [.n 52, .n 0] [.n 56, .n 57],
    .call "claim_list_digest" [.n 55, .n 3] [.n 58, .n 59],
    .atom (.hint (.allocDyn (.n 66) (.n 42))), .atom (.hint (.alloc (.n 68) 256)),
    .atom (.hint (.allocDyn (.n 385) (.n 384))),
    .call "da_verify" [.n 49] [.n 390, .n 391, .n 392],
    .atom (.hint (.allocDyn (.n 404) (.n 403))), .atom (.hint (.allocDyn (.n 410) (.n 409))),
    .atom (.hint (.allocDyn (.n 416) (.n 415))), .atom (.hint (.allocDyn (.n 419) (.n 418))),
    .atom (.hint (.witness "da_pick" (.stack [.n 426]))),
    .atom (.hint (.alloc (.n 437) 24)), .atom (.hint (.witness "leaf_defer" (.stack [.n 440]))),
    .call "statement_digest" [.n 47, .n 48, .n 56, .n 57, .n 58, .n 59, .n 466, .n 467, .n 437]
      [.n 468, .n 469]]

/-- The atoms defining `main`'s words the proof reads. -/
def mDefAtoms : List Atom :=
  [.mul (.n 40) (.n 0) (.n 1), .mul (.n 41) (.n 3) (.n 4), .mul (.n 42) (.n 40) (.n 41),
    .mul (.n 50) (.n 40) (.n 40), .mul (.n 51) (.n 50) (.n 50),
    .mul (.n 53) (.n 41) (.n 41), .mul (.n 54) (.n 53) (.n 53), .mul (.n 67) (.n 66) (.n 40),
    .const (.n 60) (word 1 0), .add (.n 61) (.n 60) (.n 1), .const (.n 62) (word 1 0),
    .const (.n 63) (word 1 0), .add (.n 64) (.n 63) (.n 4), .const (.n 65) (word 1 0),
    .const (.n 376) (word 1 0), .add (.n 377) (.n 376) (.n 2), .const (.n 378) (word 1 0),
    .const (.n 379) (word 1 0), .add (.n 380) (.n 379) (.n 5), .const (.n 381) (word 1 0),
    .const (.n 382) (word 2 0), .mul (.n 383) (.n 6) (.n 382), .mul (.n 384) (.n 383) (.n 383),
    .mul (.n 386) (.n 6) (.n 6), .mul (.n 387) (.n 385) (.n 386),
    .const (.n 388) (word 2 0), .add (.n 389) (.n 7) (.n 388), .const (.n 394) (word 0 0),
    .mul (.n 403) (.n 6) (.n 6), .mul (.n 405) (.n 6) (.n 6), .mul (.n 406) (.n 405) (.n 6),
    .mul (.n 407) (.n 406) (.n 406), .mul (.n 408) (.n 407) (.n 407),
    .mul (.n 409) (.n 408) (.n 408), .mul (.n 411) (.n 6) (.n 6), .mul (.n 412) (.n 411) (.n 6),
    .mul (.n 413) (.n 412) (.n 412), .mul (.n 414) (.n 413) (.n 413),
    .mul (.n 415) (.n 414) (.n 414), .const (.n 417) (word 2 0), .mul (.n 418) (.n 6) (.n 417),
    .mul (.n 420) (.n 2) (.n 5), .const (.n 421) (word 1 0), .add (.n 422) (.n 421) (.n 6),
    .const (.n 423) (word 1 0), .mul (.n 424) (.n 419) (.n 6),
    .add (.n 430) (.n 426) (.n 6), .const (.n 431) (word 1 0), .add (.n 432) (.n 7) (.n 431),
    .mul (.n 433) (.n 430) (.n 432), .const (.n 434) (word 0 0),
    .mul (.n 435) (.n 426) (.n 426), .mul (.n 436) (.n 385) (.n 435),
    .const (.n 438) (word 1 0), .add (.n 439) (.n 6) (.n 438),
    .const (.n 464) (word 133823759239872512 0), .mul (.n 465) (.n 49) (.n 464),
    .const (.n 470) (word 1 0), .const (.n 472) (word 1 0), .const (.n 473) (word 2 0),
    .mul (.n 474) (.n 472) (.n 473),
    .const (.n 8) (word 9272771591053052074 0), .const (.n 12) (word 9272771591053052074 0),
    .const (.n 16) (word 9272771591053052074 0), .const (.n 20) (word 9272771591053052074 0),
    .const (.n 24) (word 9272771591053052074 0), .const (.n 28) (word 9272771591053052074 0),
    .const (.n 32) (word 65536 0), .const (.n 36) (word 2 0),
    .const (.n 43) (word 9272771591053052074 0),
    .load (.n 425) (.n 424) 0, .load (.n 466) (.n 436) 0, .load (.n 467) (.n 436) 1,
    .load (.n 471) (.n 470) 0, .load (.n 475) (.n 474) 0] ++
  (List.range 51).map fun j => .const (.n (325 + j)) (word (lxTagVals.getD j 0) 0)

end
end LeanVM.Guest.B1.Main
