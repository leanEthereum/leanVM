/-
  LeanVM.Guest.B1.Stack.CertifyT

  `certify_stack`'s core IR, as a template over the stack's block groups.
-/

module

public import LeanVM.Guest.B1.Whir.Loops
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

/-!
# `certify_stack`'s template

`certify_stack(kappa_base, g_squares)` (`guests/lean_ethereum.py`) works on the stack's block
groups (`csGroups`: each group's kappa source, adjustment, first block and length, the guest's
`STK_SRC`, `STK_ADJ`, `STK_GROUP_START`). Its expansion, `csBody`:

* `csLoads`: the eight kappa sources at `kappa_base`, values `2 ..< 10`; the key and size tables'
  buffers at `10`, `11`;
* `csKey gi`: group `gi`'s `κ = kb[src]·g^adj` (its value `csKap`), range checked below `g^33`
  (`SIZE_BITS = 34`), its rank key `κ^53·g^(-b0)` stored at `group_key[gi]`, and its size
  `g_squares[κ]^len`, stored at `group_size[gi]`;
* `csRank r`: rank `r`'s hinted group, range checked below `g^7` (`N_STK_GROUPS = 8`), its key, the
  check that the key falls (`prev / key · g⁻¹` range checked below `g^1801`, `STK_KEY_BOUND = 1802`),
  `group_at[gi]` the running total, the total times the group's size;
* `log2_ceil_in_the_exponent__L16_L34` of the total, the stack's log;
* `csOut gi`: per block of group `gi`, `g^offset` at `outs[b]` and `g^κ` at `outs[52 + b]`;
* the returns `gmv`, `outs`, `outs·g^52`.

`certify_stack_body`: the core IR is the template, by kernel evaluation.
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## The block groups -/

/-- A block group: its kappa source (an index of `kappa_base`), its adjustment, its first block,
its length. -/
structure CsGroup where
  src : ℕ
  adj : ℕ
  b0 : ℕ
  len : ℕ
  /-- `g^(-b0)`'s word, the rank key's shift (`0` for `b0 = 0`). -/
  inv : ℕ
  deriving Inhabited, DecidableEq

/-- The guest's block groups (`STK_SRC`, `STK_ADJ`, `STK_GROUP_START`). -/
def csGroups : List CsGroup :=
  [⟨1, 0, 0, 2, 0⟩, ⟨7, 6, 2, 1, 13835058055282163723⟩, ⟨2, 0, 3, 7, 16140901064495857672⟩,
    ⟨3, 0, 10, 9, 8196551321814302724⟩, ⟨4, 0, 19, 5, 10248187242686185485⟩,
    ⟨5, 0, 24, 10, 2049638108244213761⟩, ⟨6, 0, 34, 14, 8198552921529384964⟩,
    ⟨7, 0, 48, 4, 2049638230412165121⟩]

/-- Group `gi`. -/
def csG (gi : ℕ) : CsGroup := csGroups.getD gi default

/-! ## The template -/

/-- `g^e`'s word, for the small exponents the template names. -/
def csW (e : ℕ) : E := word (2 ^ e) 0

/-- A range check `log x < log (g·k)`, its three hinted values from `h`. -/
def csRc (x h k : ℕ) : Stmt := .atom (.rangeCheck (.n x) (.n h) (.n (h + 1)) (.n (h + 2)) (.n k))

/-- The kappa sources' loads and the two tables' buffers. -/
def csLoads : List Stmt :=
  ((List.range 8).map fun i ↦ .atom (.load (.n (2 + i)) (.n 0) i)) ++
    [.atom (.hint (.alloc (.n 10) 8)), .atom (.hint (.alloc (.n 11) 8))]

/-- Group `g`'s `κ`, from `s`: the statements, its value and the next free value. -/
def csKappa (g : CsGroup) (s : ℕ) : List Stmt × ℕ × ℕ :=
  if g.adj = 0 then ([], 2 + g.src, s)
  else ([osCst s (csW g.adj), osMul (s + 1) (2 + g.src) s], s + 1, s + 2)

/-- Group `gi`'s key and size, from `s`: the statements and the next free value. -/
def csKey (gi s : ℕ) : List Stmt × ℕ :=
  let g := csG gi
  let kp := csKappa g s
  let v := kp.2.1
  let s := kp.2.2
  let ch := osPowSteps v (osPowDigits 53) v (s + 4)
  let key := if g.b0 = 0 then ([], ch.2, s + 4 + osPowLen 53)
    else ([osCst (s + 4 + osPowLen 53) (word g.inv 0),
      osMul (s + 5 + osPowLen 53) ch.2 (s + 4 + osPowLen 53)], s + 5 + osPowLen 53,
      s + 6 + osPowLen 53)
  let m := key.2.2
  let sz := osPowSteps (m + 1) (osPowDigits g.len) (m + 1) (m + 2)
  (kp.1 ++ [osCst s (csW 33), csRc v (s + 1) s] ++ ch.1 ++ key.1 ++
      [.atom (.load (.n key.2.1) (.n 10) gi), osMul m 1 v, .atom (.load (.n (m + 1)) (.n m) 0)] ++
      sz.1 ++ [.atom (.load (.n sz.2) (.n 11) gi)],
    m + 2 + osPowLen g.len)

/-- Groups `gi ..< gi + n` from `s`. -/
def csKeys : ℕ → ℕ → ℕ → List Stmt × ℕ
  | _, 0, s => ([], s)
  | gi, n + 1, s =>
    let k := csKey gi s
    let r := csKeys (gi + 1) n k.2
    (k.1 ++ r.1, r.2)

/-- The key bound's word, `g^1802`. -/
def csBound : E := word 1681003845738829664 0

/-- `g⁻¹`'s word. -/
def csInvGen : E := word 9223372036854775821 0

/-- Rank `r ≥ 1`, from `s`, after the key `pk` and the total `tot`, the order at `ord` and
`group_at` at `at`. -/
def csRank (ord at_ s pk tot r : ℕ) : List Stmt :=
  [.atom (.load (.n s) (.n ord) r), osCst (s + 1) (csW 7), csRc s (s + 2) (s + 1),
    osMul (s + 5) 10 s, .atom (.load (.n (s + 6)) (.n (s + 5)) 0), osCst (s + 7) csBound,
    osMul pk (s + 8) (s + 6), osCst (s + 9) csInvGen, osMul (s + 10) (s + 8) (s + 9),
    csRc (s + 10) (s + 11) (s + 7), osMul (s + 14) at_ s, .atom (.load (.n tot) (.n (s + 14)) 0),
    osMul (s + 15) 11 s, .atom (.load (.n (s + 16)) (.n (s + 15)) 0), osMul (s + 17) tot (s + 16)]

/-- The ranks: the order's buffer at `ord`, `group_at` at `at`, rank `0` at `s0`. -/
def csRanks (ord at_ s0 : ℕ) : List Stmt :=
  [.atom (.load (.n s0) (.n ord) 0), osCst (s0 + 1) (csW 7), csRc s0 (s0 + 2) (s0 + 1),
    osMul (s0 + 5) 10 s0, .atom (.load (.n (s0 + 6)) (.n (s0 + 5)) 0), osCst (s0 + 7) (word 1 0),
    osMul (s0 + 8) at_ s0, .atom (.load (.n (s0 + 7)) (.n (s0 + 8)) 0), osMul (s0 + 9) 11 s0,
    .atom (.load (.n (s0 + 10)) (.n (s0 + 9)) 0)] ++
  ((List.range 7).map fun r ↦
    csRank ord at_ (s0 + 11 + 18 * r) (if r = 0 then s0 + 6 else s0 + 11 + 18 * (r - 1) + 6)
      (if r = 0 then s0 + 10 else s0 + 11 + 18 * (r - 1) + 17) (r + 1)).flatten

/-- Group `gi`'s blocks, from `s`, the outputs at `out`: its step `g_squares[κ]`, `group_at[gi]`,
then per block `g^offset` and `g^κ`. -/
def csOut (out at_ gi s : ℕ) : List Stmt × ℕ :=
  let g := csG gi
  let kp := csKappa g s
  let v := kp.2.1
  let s := kp.2.2
  (kp.1 ++ [osMul s 1 v, .atom (.load (.n (s + 1)) (.n s) 0), .atom (.load (.n (s + 2)) (.n at_) gi),
      .atom (.load (.n (s + 2)) (.n out) g.b0), .atom (.load (.n v) (.n out) (52 + g.b0))] ++
      ((List.range (g.len - 1)).map fun j ↦
        [osMul (s + 3 + j) (s + 2 + j) (s + 1), .atom (.load (.n (s + 3 + j)) (.n out) (g.b0 + 1 + j)),
          .atom (.load (.n v) (.n out) (52 + g.b0 + 1 + j))]).flatten,
    s + 2 + g.len)

/-- Groups `gi ..< gi + n`' blocks from `s`. -/
def csOuts (out at_ : ℕ) : ℕ → ℕ → ℕ → List Stmt × ℕ
  | _, 0, s => ([], s)
  | gi, n + 1, s =>
    let k := csOut out at_ gi s
    let r := csOuts out at_ (gi + 1) n k.2
    (k.1 ++ r.1, r.2)

/-- **The expansion of `certify_stack`.** -/
def csBody : List Stmt :=
  let ks := csKeys 0 8 12
  let ord := ks.2
  let at_ := ord + 1
  let s0 := ord + 2
  let tot := s0 + 11 + 18 * 6 + 17
  let gmv := tot + 1
  let out := tot + 2
  let os := csOuts out at_ 0 8 (tot + 3)
  csLoads ++ ks.1 ++
    [.atom (.hint (.alloc (.n ord) 8)), .atom (.hint (.witness "stk_group_order" (.heap (.n ord) 0 8))),
      .atom (.hint (.alloc (.n at_) 8))] ++
    csRanks ord at_ s0 ++
    [.call "log2_ceil_in_the_exponent__L16_L34" [.n tot, .n 1] [.n gmv],
      .atom (.hint (.alloc (.n out) 104))] ++ os.1 ++
    [.atom (.copy (.n os.2) (.n gmv)), .atom (.copy (.n (os.2 + 1)) (.n out)),
      osCst (os.2 + 2) (csW 52), osMul (os.2 + 3) out (os.2 + 2),
      .ret [.n os.2, .n (os.2 + 1), .n (os.2 + 3)]]

theorem certify_stack_body : Fn.body fn% «certify_stack» = csBody := stmtsEqb_sound (by decide +kernel)

theorem find_certify_stack : coreProgram.find? "certify_stack" = some fn% «certify_stack» :=
  coreProgram_find?_at (j := idx% «certify_stack») rfl

theorem certify_stack_params : Fn.params fn% «certify_stack» = [.n 0, .n 1] := rfl

end
end LeanVM.Guest.B1.Stack

