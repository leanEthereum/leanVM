/-
  LeanVM.Guest.B1.Link.Rounds

  The link's sum-check rounds in the circuit: `link_round`'s expansion as a template.
-/

module

public import LeanVM.Guest.B1.Link.Terminal
public import LeanVM.Guest.B1.Bits.GrindT
public import LeanVM.Guest.B1.Fs.Templates

/-!
# `link_round`, `link_rounds_last`

`link_round(sp, cur, cl, out, tabs, n_tail, bits)` (G, inlined into `link_rounds`' loop and
`link_rounds_last`) reads `c0` and `n_tail` coefficients from the cursor, absorbing each (a
permutation before every fifth), grinds `bits` (its nonce one more word, `grind_check` inlined)
and squeezes `y`; the next claim is the round polynomial at `y`. `lrRound nt bits o cap cur cl tabs
pad` is its expansion from the value `o`, on the capacity values `cap` and the cursor and claim
values; `pad` is the zero run a caller's earlier permutation made, if any.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- Scalar `i`'s first value in a round from `0`. -/
def lrSb (i : ℕ) : ℕ := if i = 0 then 0 else 3 + 4 * (i - 1) + 13 * (i / 4)

/-- Scalar `i`: its word, its two rate cells, and (a tail coefficient) its copy. -/
def lrScalar (o cur i : ℕ) : List Stmt :=
  let b := o + lrSb i
  if i = 0 then
    [.atom (.load (.n b) (.n cur) 0), .atom (.copy (.n (b + 1)) (.n b)),
      .atom (.const (.n (b + 2)) (word 0 1))]
  else
    [.atom (.load (.n b) (.n cur) i), .atom (.copy (.n (b + 1)) (.n b)),
      .atom (.const (.n (b + 2)) (word 0 1)), .atom (.copy (.n (b + 3)) (.n b))]

/-- The rate cells of scalars `j .. j + k - 1`. -/
def lrCells (o j k : ℕ) : List V :=
  (List.range k).flatMap fun i ↦ [.n (o + lrSb (j + i) + 1), .n (o + lrSb (j + i) + 2)]

/-- The first output of the permutation before scalar `4 m` (`m ≥ 1`). -/
def lrPermOut (o m : ℕ) : ℕ := o + lrSb (4 * m) - 13

/-- The capacity values at scalar `i`: the input's below `4`, else the last permutation's. -/
def lrCap (o : ℕ) (cap : List ℕ) (i : ℕ) : List ℕ :=
  if i < 4 then cap else (List.range 5).map fun j ↦ lrPermOut o (i / 4) + 8 + j

/-- The permutation before scalar `4 m`. -/
def lrPerm (o : ℕ) (cap : List ℕ) (m : ℕ) : Stmt :=
  .atom (.keccak (lrCells o (4 * m - 4) 4 ++ (lrCap o cap (4 * m - 1)).map V.n)
    ((List.range 13).map fun j ↦ .n (lrPermOut o m + j)) false false)

/-- Scalar `i`, the permutation before it if `i` is a positive multiple of `4`. -/
def lrStep (o : ℕ) (cap : List ℕ) (cur i : ℕ) : List Stmt :=
  (if i ≠ 0 ∧ i % 4 = 0 then [lrPerm o cap (i / 4)] else []) ++ lrScalar o cur i

/-- The padding of a permutation of `k` waiting scalars from `P`: its zero cells, the values it
makes, the first value after them, and the zero run it leaves. -/
def lrPadCells (P k : ℕ) (pad : Option ℕ) : List V × List Stmt × ℕ × Option ℕ :=
  if k = 4 then ([], [], P, pad)
  else if k = 3 then ([.n P, .n (P + 1)],
    [.atom (.const (.n P) (word 0 0)), .atom (.const (.n (P + 1)) (word 0 0))], P + 2, pad)
  else match pad with
    | some z => ((if k = 1 then [.n z, .n z] else []) ++ [.n z, .n (z + 1), .n (z + 2), .n (z + 3)],
        [], P, pad)
    | none => ((if k = 1 then [.n (P + 1), .n (P + 1)] else []) ++
        [.n (P + 1), .n (P + 2), .n (P + 3), .n (P + 4)],
        [.atom (.const (.n P) (word 1 0)), .atom (.const (.n (P + 1)) (word 0 0)),
          .atom (.const (.n (P + 2)) (word 0 0)), .atom (.const (.n (P + 3)) (word 0 0)),
          .atom (.const (.n (P + 4)) (word 0 0))], P + 5, some (P + 1))

/-- The first value after the scalars. -/
def lrE (o nt : ℕ) : ℕ := o + lrSb nt + 4

/-- The waiting scalars at the end, `nt % 4 + 1`, and with the nonce. -/
def lrK (nt bits : ℕ) : ℕ := nt % 4 + 1 + if bits = 0 then 0 else 1

/-- The final permutation's padding start: after the nonce's three values when grinding. -/
def lrP (o nt bits : ℕ) : ℕ := lrE o nt + if bits = 0 then 0 else 3

/-- The final permutation's first output. -/
def lrF (o nt bits : ℕ) (pad : Option ℕ) : ℕ := (lrPadCells (lrP o nt bits) (lrK nt bits) pad).2.2.1

/-- The grind's length, `grind_check` at `bits` inlined. -/
def lrG (bits : ℕ) : ℕ := if bits = 0 then 0 else gcLen bits - 2

/-- The claim chain's first value. -/
def lrC (o nt bits : ℕ) (pad : Option ℕ) : ℕ := lrF o nt bits pad + 13 + lrG bits

/-- Tail coefficient `j`'s copy. -/
def lrTail (o j : ℕ) : ℕ := o + lrSb (j + 1) + 3

/-- The Horner value and the tail's sum after `j` steps. -/
def lrAcc (o nt C j : ℕ) : ℕ := if j = 0 then lrTail o (nt - 1) else C + 3 * (j - 1) + 1

def lrTs (o nt C j : ℕ) : ℕ := if j = 0 then lrTail o (nt - 1) else C + 3 * (j - 1) + 2

/-- The round's last nine values' first, `D`. -/
def lrD (o nt bits : ℕ) (pad : Option ℕ) : ℕ := lrC o nt bits pad + 3 * (nt - 1)

/-- **`link_round`'s expansion** from `o`: `nt ≥ 1` tail coefficients, `bits` of grind. -/
def lrRound (nt bits o : ℕ) (cap : List ℕ) (cur cl tabs : ℕ) (pad : Option ℕ) : List Stmt :=
  let E := lrE o nt
  let pc := lrPadCells (lrP o nt bits) (lrK nt bits) pad
  let F := pc.2.2.1
  let C := lrC o nt bits pad
  let D := lrD o nt bits pad
  let k := nt % 4 + 1
  ((List.range (nt + 1)).map (lrStep o cap cur)).flatten ++
  (if bits = 0 then []
    else (if k = 4 then [lrPerm o cap ((nt + 1) / 4)] else []) ++
      [.atom (.load (.n E) (.n cur) (nt + 1)), .atom (.copy (.n (E + 1)) (.n E)),
        .atom (.const (.n (E + 2)) (word 0 4))]) ++
  pc.2.1 ++
  [.atom (.keccak (lrCells o (nt + 1 - k) k ++ (if bits = 0 then [] else [.n (E + 1), .n (E + 2)]) ++
      pc.1 ++ (lrCap o cap nt).map V.n) ((List.range 13).map fun j ↦ .n (F + j)) false false)] ++
  (if bits = 0 then [] else gcInlineT bits (F + 13) (.n (F + 1)) (.n tabs)) ++
  ((List.range (nt - 1)).map fun j' ↦
    let j := j' + 1
    let B := C + 3 * (j - 1)
    [.atom (.mul (.n B) (.n (lrAcc o nt C (j - 1))) (.n F)),
      .atom (.add (.n (B + 1)) (.n B) (.n (lrTail o (nt - 1 - j)))),
      .atom (.add (.n (B + 2)) (.n (lrTs o nt C (j - 1))) (.n (lrTail o (nt - 1 - j))))]).flatten ++
  [.atom (.mul (.n D) (.n (lrAcc o nt C (nt - 1))) (.n F)),
    .atom (.add (.n (D + 1)) (.n cl) (.n (lrTs o nt C (nt - 1)))),
    .atom (.add (.n (D + 2)) (.n D) (.n (D + 1))), .atom (.copy (.n (D + 3)) (.n F)),
    .atom (.const (.n (D + 4)) (word (2 ^ (nt + 1 + if bits = 0 then 0 else 1)) 0)),
    .atom (.mul (.n (D + 5)) (.n cur) (.n (D + 4))), .atom (.copy (.n (D + 6)) (.n (D + 5))),
    .atom (.mul (.n (D + 7)) (.n (D + 2)) (.n F)), .atom (.add (.n (D + 8)) (.n (D + 7)) (.n o))]

/-- The round's outputs: the capacity, `y`, the cursor, the claim; its next value and zero run. -/
def lrOutCap (nt bits o : ℕ) (pad : Option ℕ) : List ℕ :=
  (List.range 5).map fun j ↦ lrF o nt bits pad + 8 + j

def lrNext (nt bits o : ℕ) (pad : Option ℕ) : ℕ := lrD o nt bits pad + 9

def lrPad (nt bits o : ℕ) (pad : Option ℕ) : Option ℕ :=
  (lrPadCells (lrP o nt bits) (lrK nt bits) pad).2.2.2

/-- `k` rounds from `o`, each storing its challenge at `pts[r]`: their atoms, and the round state
after them (capacity, cursor, claim, next value, zero run). -/
def lrRounds (nt bits pts tabs : ℕ) : ℕ → ℕ → List ℕ → ℕ → ℕ → Option ℕ →
    List Stmt × List ℕ × ℕ × ℕ × ℕ × Option ℕ
  | 0, o, cap, cur, cl, pad => ([], cap, cur, cl, o, pad)
  | r + 1, o, cap, cur, cl, pad =>
    let prev := lrRounds nt bits pts tabs r o cap cur cl pad
    let o' := prev.2.2.2.2.1
    let pad' := prev.2.2.2.2.2
    let D := lrD o' nt bits pad'
    (prev.1 ++ lrRound nt bits o' prev.2.1 prev.2.2.1 prev.2.2.2.1 tabs pad' ++
        [.atom (.load (.n (D + 3)) (.n pts) r)],
      lrOutCap nt bits o' pad', D + 6, D + 8, lrNext nt bits o' pad', lrPad nt bits o' pad')

/-- **`link_rounds_last__L{nt}_L{bits}_L{k}`**: the record's capacity, cursor and claim read,
`k` rounds, the record after them stored. -/
def lrLastBody (nt bits k : ℕ) : List Stmt :=
  if k = 0 then
    [.atom (.load (.n 4) (.n 0) 0), .atom (.load (.n 5) (.n 0) 1), .atom (.load (.n 6) (.n 0) 2),
      .atom (.load (.n 7) (.n 0) 3), .atom (.load (.n 8) (.n 0) 4),
      .atom (.load (.n 4) (.n 1) 0), .atom (.load (.n 5) (.n 1) 1), .atom (.load (.n 6) (.n 1) 2),
      .atom (.load (.n 7) (.n 1) 3), .atom (.load (.n 8) (.n 1) 4),
      .atom (.load (.n 9) (.n 0) 5), .atom (.load (.n 9) (.n 1) 5),
      .atom (.load (.n 10) (.n 0) 6), .atom (.load (.n 10) (.n 1) 6),
      .atom (.const (.n 11) (word 0 0)), .ret [.n 11]]
  else
    let rs := lrRounds nt bits 2 3 k 11 [4, 5, 6, 7, 8] 9 10 none
    [.atom (.load (.n 4) (.n 0) 0), .atom (.load (.n 5) (.n 0) 1), .atom (.load (.n 6) (.n 0) 2),
      .atom (.load (.n 7) (.n 0) 3), .atom (.load (.n 8) (.n 0) 4), .atom (.load (.n 9) (.n 0) 5),
      .atom (.load (.n 10) (.n 0) 6)] ++ rs.1 ++
    ((List.range 5).map fun j ↦ .atom (.load (.n (rs.2.1.getD j 0)) (.n 1) j)) ++
    [.atom (.load (.n rs.2.2.1) (.n 1) 5), .atom (.load (.n rs.2.2.2.1) (.n 1) 6),
      .atom (.const (.n rs.2.2.2.2.1) (word 0 0)), .ret [.n rs.2.2.2.2.1]]

/-! ## The bodies -/

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L0_body :
    Fn.body (fn% «link_rounds_last__L1_L0_L0») = lrLastBody 1 0 0 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L1_body :
    Fn.body (fn% «link_rounds_last__L1_L0_L1») = lrLastBody 1 0 1 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L2_body :
    Fn.body (fn% «link_rounds_last__L1_L0_L2») = lrLastBody 1 0 2 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L1_L0_L3_body :
    Fn.body (fn% «link_rounds_last__L1_L0_L3») = lrLastBody 1 0 3 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L0_body :
    Fn.body (fn% «link_rounds_last__L7_L0_L0») = lrLastBody 7 0 0 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L1_body :
    Fn.body (fn% «link_rounds_last__L7_L0_L1») = lrLastBody 7 0 1 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L2_body :
    Fn.body (fn% «link_rounds_last__L7_L0_L2») = lrLastBody 7 0 2 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L7_L0_L3_body :
    Fn.body (fn% «link_rounds_last__L7_L0_L3») = lrLastBody 7 0 3 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L0_body :
    Fn.body (fn% «link_rounds_last__L6_L0_L0») = lrLastBody 6 0 0 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L1_body :
    Fn.body (fn% «link_rounds_last__L6_L0_L1») = lrLastBody 6 0 1 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L2_body :
    Fn.body (fn% «link_rounds_last__L6_L0_L2») = lrLastBody 6 0 2 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L6_L0_L3_body :
    Fn.body (fn% «link_rounds_last__L6_L0_L3») = lrLastBody 6 0 3 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L0_body :
    Fn.body (fn% «link_rounds_last__L8_L1_L0») = lrLastBody 8 1 0 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L1_body :
    Fn.body (fn% «link_rounds_last__L8_L1_L1») = lrLastBody 8 1 1 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L2_body :
    Fn.body (fn% «link_rounds_last__L8_L1_L2») = lrLastBody 8 1 2 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L3_body :
    Fn.body (fn% «link_rounds_last__L8_L1_L3») = lrLastBody 8 1 3 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L0_body :
    Fn.body (fn% «link_rounds_last__L9_L1_L0») = lrLastBody 9 1 0 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L1_body :
    Fn.body (fn% «link_rounds_last__L9_L1_L1») = lrLastBody 9 1 1 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L2_body :
    Fn.body (fn% «link_rounds_last__L9_L1_L2») = lrLastBody 9 1 2 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L3_body :
    Fn.body (fn% «link_rounds_last__L9_L1_L3») = lrLastBody 9 1 3 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L0_body :
    Fn.body (fn% «link_rounds_last__L10_L1_L0») = lrLastBody 10 1 0 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L1_body :
    Fn.body (fn% «link_rounds_last__L10_L1_L1») = lrLastBody 10 1 1 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L2_body :
    Fn.body (fn% «link_rounds_last__L10_L1_L2») = lrLastBody 10 1 2 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L3_body :
    Fn.body (fn% «link_rounds_last__L10_L1_L3») = lrLastBody 10 1 3 :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Link
