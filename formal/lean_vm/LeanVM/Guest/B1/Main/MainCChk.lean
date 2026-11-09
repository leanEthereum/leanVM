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
checks, the loads through `main`'s buffers and the header, and the four equality checks
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
  (List.range 256).map (fun v => .load (.n (69 + v)) (.n 68) v) ++
    [.load (.n 400) (.n 387) 0, .load (.n 401) (.n 387) 1, .load (.n 402) (.n 387) 0,
      .load (.n 403) (.n 387) 1, .load (.n 421) (.n 420) 0] ++
    (List.range 23).map (fun k => .load (.n (442 + k)) (.n 438) k) ++ [.load (.n 441) (.n 438) 23]

/-- `main`'s loads, by their words' numbers: the five reads, then the stores. -/
def mLoadOk (d p o : ℕ) : Bool :=
  decide ((d, p, o) ∈ [(426, 425, 0), (465, 437, 0), (466, 437, 1), (470, 469, 0),
    (474, 473, 0)]) ||
  (decide (p = 68) && decide (d = 69 + o) && decide (o < 256)) ||
  decide ((d, p, o) ∈ [(400, 387, 0), (401, 387, 1), (402, 387, 0), (403, 387, 1),
    (421, 420, 0)]) ||
  (decide (p = 438) && (decide (o < 23 ∧ d = 442 + o) || decide (o = 23 ∧ d = 441)))

/-- The range checks: the checked value and the bound's constant. -/
def rcPairs : List (ℕ × ℕ) :=
  [(0, 8), (1, 12), (2, 16), (3, 20), (4, 24), (5, 28), (6, 32), (7, 36), (42, 43), (427, 6)]

/-- The atoms of `main` whose side conditions its completeness discharges. -/
def mSideOk : Atom → Bool
  | .rangeCheck x y _ _ k => decide ((x.idx, k.idx) ∈ rcPairs) && decide (x = .n x.idx) &&
      decide (k = .n k.idx) && decide (k.idx < y.idx)
  | .load d p o => decide (d = .n d.idx) && decide (p = .n p.idx) && mLoadOk d.idx p.idx o
  | .assertEq x y => decide ((x, y) ∈ [(V.n 426, V.n 42), (.n 434, .n 435), (.n 470, .n 467),
      (.n 474, .n 468)])
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
  canonChk [390, 391, 392, 393] (noStores mDa) && canonChk [] (noStores mDaZ) &&
  canonChk [] (noStores mLeaf) &&
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
    .call "da_verify" [.n 49] [.n 390, .n 391, .n 392, .n 393],
    .atom (.hint (.allocDyn (.n 405) (.n 404))), .atom (.hint (.allocDyn (.n 411) (.n 410))),
    .atom (.hint (.allocDyn (.n 417) (.n 416))), .atom (.hint (.allocDyn (.n 420) (.n 419))),
    .atom (.hint (.witness "da_pick" (.stack [.n 427]))),
    .atom (.hint (.alloc (.n 438) 24)), .atom (.hint (.witness "leaf_defer" (.stack [.n 441]))),
    .call "statement_digest" [.n 47, .n 48, .n 56, .n 57, .n 58, .n 59, .n 465, .n 466, .n 438]
      [.n 467, .n 468]]

/-- The atoms defining `main`'s words the proof reads. -/
def mDefAtoms : List Atom :=
  [.mul (.n 40) (.n 0) (.n 1), .mul (.n 41) (.n 3) (.n 4), .mul (.n 42) (.n 40) (.n 41),
    .mul (.n 50) (.n 40) (.n 40), .mul (.n 51) (.n 50) (.n 50),
    .mul (.n 53) (.n 41) (.n 41), .mul (.n 54) (.n 53) (.n 53), .mul (.n 67) (.n 66) (.n 40),
    .const (.n 60) (word 1 0 0), .add (.n 61) (.n 60) (.n 1), .const (.n 62) (word 1 0 0),
    .const (.n 63) (word 1 0 0), .add (.n 64) (.n 63) (.n 4), .const (.n 65) (word 1 0 0),
    .const (.n 376) (word 1 0 0), .add (.n 377) (.n 376) (.n 2), .const (.n 378) (word 1 0 0),
    .const (.n 379) (word 1 0 0), .add (.n 380) (.n 379) (.n 5), .const (.n 381) (word 1 0 0),
    .const (.n 382) (word 2 0 0), .mul (.n 383) (.n 6) (.n 382), .mul (.n 384) (.n 383) (.n 383),
    .mul (.n 386) (.n 6) (.n 6), .mul (.n 387) (.n 385) (.n 386),
    .const (.n 388) (word 2 0 0), .add (.n 389) (.n 7) (.n 388),
    .mul (.n 404) (.n 6) (.n 6), .mul (.n 406) (.n 6) (.n 6), .mul (.n 407) (.n 406) (.n 6),
    .mul (.n 408) (.n 407) (.n 407), .mul (.n 409) (.n 408) (.n 408),
    .mul (.n 410) (.n 409) (.n 409), .mul (.n 412) (.n 6) (.n 6), .mul (.n 413) (.n 412) (.n 6),
    .mul (.n 414) (.n 413) (.n 413), .mul (.n 415) (.n 414) (.n 414),
    .mul (.n 416) (.n 415) (.n 415), .const (.n 418) (word 2 0 0), .mul (.n 419) (.n 6) (.n 418),
    .mul (.n 421) (.n 2) (.n 5), .const (.n 422) (word 1 0 0), .add (.n 423) (.n 422) (.n 6),
    .const (.n 424) (word 1 0 0), .mul (.n 425) (.n 420) (.n 6),
    .add (.n 431) (.n 427) (.n 6), .const (.n 432) (word 1 0 0), .add (.n 433) (.n 7) (.n 432),
    .mul (.n 434) (.n 431) (.n 433), .const (.n 435) (word 0 0 0),
    .mul (.n 436) (.n 427) (.n 427), .mul (.n 437) (.n 385) (.n 436),
    .const (.n 439) (word 1 0 0), .add (.n 440) (.n 6) (.n 439),
    .const (.n 469) (word 1 0 0), .const (.n 471) (word 1 0 0), .const (.n 472) (word 2 0 0),
    .mul (.n 473) (.n 471) (.n 472),
    .const (.n 8) (word 9272771591053052074 0 0), .const (.n 12) (word 9272771591053052074 0 0),
    .const (.n 16) (word 9272771591053052074 0 0), .const (.n 20) (word 9272771591053052074 0 0),
    .const (.n 24) (word 9272771591053052074 0 0), .const (.n 28) (word 9272771591053052074 0 0),
    .const (.n 32) (word 65536 0 0), .const (.n 36) (word 2 0 0),
    .const (.n 43) (word 9272771591053052074 0 0),
    .load (.n 426) (.n 425) 0, .load (.n 465) (.n 437) 0, .load (.n 466) (.n 437) 1,
    .load (.n 470) (.n 469) 0, .load (.n 474) (.n 473) 0] ++
  (List.range 51).map fun j => .const (.n (325 + j)) (word (lxTagVals.getD j 0) 0 0)

end
end LeanVM.Guest.B1.Main
