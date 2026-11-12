/-
  LeanVM.Guest.B1.Fs.MessageT

  `opening_message`'s expansion as a template over its length and nonce, checked against every
  deployed specialization by kernel evaluation, and the absorption of its words by groups.
-/

module

public import LeanVM.Guest.B1.Fs.SqueezePoint

/-!
# `opening_message`'s body

`opening_message__L{n}_L{nonce}` is straight-line (`omBody n nonce`): the capacity copied into
`7 .. 11`; word `p` read at `cursor[p]` into `omW p`, packed (`omW p + 1`, `omW p + 2`) and stored
at `out[p]`; after each full group of four but the last, the permutation of the group with the
previous capacity (`omKeccak g`, written from `omO g`, its capacity read from `omCap g`); then the
tail (`omTail`), by the words left `r` and the nonce: the last permutation of the words left
(`nonce = 0`), or the nonce `cursor[n]` packed with `dsPowNonce` and its permutation, after the
last full group's or with the words left (`nonce = 1`); then the last permutation's cells `0`, `1` and its capacity
copied out, and the cursor stepped by `g^(n + nonce)`.

`absorbAll_groups`: the words absorbed on the capacity leave the capacity of the last full
group's permutation (`stCap`) and the words after it waiting.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- Where word `p` is read. -/
def omW (p : ℕ) : ℕ := 12 + 3 * p + 13 * (p / 4)

/-- Where group `g`'s permutation writes. -/
def omO (g : ℕ) : ℕ := 24 + 25 * g

/-- Where group `g`'s permutation reads the capacity. -/
def omCap : ℕ → ℕ
  | 0 => 7
  | g + 1 => omO g + 8

/-- Word `p`'s atoms: read, packed, stored at `out[p]`. -/
def omWordAs (p : ℕ) : List Atom :=
  [.load (.n (omW p)) (.n 5) p, .copy (.n (omW p + 1)) (.n (omW p)),
    .const (.n (omW p + 2)) (word 0 dsObserve), .load (.n (omW p)) (.n 6) p]

/-- Group `g`'s rate cells. -/
def omRate (g : ℕ) : List V :=
  [.n (omW (4 * g) + 1), .n (omW (4 * g) + 2), .n (omW (4 * g + 1) + 1), .n (omW (4 * g + 1) + 2),
    .n (omW (4 * g + 2) + 1), .n (omW (4 * g + 2) + 2), .n (omW (4 * g + 3) + 1),
    .n (omW (4 * g + 3) + 2)]

/-- Group `g`'s permutation. -/
def omKeccak (g : ℕ) : Atom := .keccak (omRate g ++ run5 (omCap g)) (run13 (omO g)) false false

/-- The full groups but the last: `(n - 1) / 4`. -/
def omK (n : ℕ) : ℕ := (n - 1) / 4

/-- The words, each group's permutation after it but the last's. -/
def omWords (n : ℕ) : List Atom :=
  (List.range n).flatMap fun p ↦
    omWordAs p ++ if p % 4 = 3 ∧ p + 1 < n then [omKeccak (p / 4)] else []

/-- Where the tail starts. -/
def omE (n : ℕ) : ℕ := 12 + 3 * n + 13 * omK n

/-- The pad run's atoms from `b`. -/
def padAs (b : ℕ) : List Atom :=
  [.const (.n b) (word 1 0), .const (.n (b + 1)) (word 0 0), .const (.n (b + 2)) (word 0 0),
    .const (.n (b + 3)) (word 0 0), .const (.n (b + 4)) (word 0 0)]

/-- The tail by the words left (`n - 4 omK n`) and the nonce, with where its last permutation
writes and where the copies start: `(atoms, O, f)`. -/
def omTail (n nonce : ℕ) : List Atom × ℕ × ℕ :=
  let K := omK n
  let e := omE n
  if nonce = 0 then
    if n - 4 * K = 4 then ([omKeccak K], omO K, e + 13)
    else
      (padAs e ++ [.keccak ([.n (omW (4 * K) + 1), .n (omW (4 * K) + 2), .n (omW (4 * K + 1) + 1),
          .n (omW (4 * K + 1) + 2), .n (e + 1), .n (e + 2), .n (e + 3), .n (e + 4)] ++
          run5 (omCap K)) (run13 (e + 5)) false false], e + 5, e + 18)
  else if n - 4 * K = 4 then
    ([omKeccak K, .load (.n (e + 13)) (.n 5) n, .copy (.n (e + 14)) (.n (e + 13)),
      .const (.n (e + 15)) (word 0 dsPowNonce)] ++ padAs (e + 16) ++
      [.keccak ([.n (e + 14), .n (e + 15), .n (e + 17), .n (e + 17), .n (e + 17), .n (e + 18),
        .n (e + 19), .n (e + 20)] ++ run5 (e + 8)) (run13 (e + 21)) false false], e + 21, e + 34)
  else if n - 4 * K = 2 then
    ([.load (.n e) (.n 5) n, .copy (.n (e + 1)) (.n e), .const (.n (e + 2)) (word 0 dsPowNonce),
      .const (.n (e + 3)) (word 0 0), .const (.n (e + 4)) (word 0 0)] ++
      [.keccak ([.n (omW (4 * K) + 1), .n (omW (4 * K) + 2), .n (omW (4 * K + 1) + 1),
        .n (omW (4 * K + 1) + 2), .n (e + 1), .n (e + 2), .n (e + 3), .n (e + 4)] ++ run5 (omCap K))
        (run13 (e + 5)) false false], e + 5, e + 18)
  else
    ([.load (.n e) (.n 5) n, .copy (.n (e + 1)) (.n e), .const (.n (e + 2)) (word 0 dsPowNonce)] ++
      padAs (e + 3) ++
      [.keccak ([.n (omW (4 * K) + 1), .n (omW (4 * K) + 2), .n (e + 1), .n (e + 2), .n (e + 4),
        .n (e + 5), .n (e + 6), .n (e + 7)] ++ run5 (omCap K)) (run13 (e + 8)) false false],
      e + 8, e + 21)

/-- The copies out and the cursor's step, from `f`, the last permutation writing from `O`. -/
def omFinal (n nonce O f : ℕ) : List Atom :=
  [.copy (.n f) (.n O), .copy (.n (f + 1)) (.n (O + 1)), .copy (.n (f + 2)) (.n (O + 8)),
    .copy (.n (f + 3)) (.n (O + 9)), .copy (.n (f + 4)) (.n (O + 10)),
    .copy (.n (f + 5)) (.n (O + 11)), .copy (.n (f + 6)) (.n (O + 12)),
    .const (.n (f + 7)) (word (2 ^ (n + nonce)) 0), .mul (.n (f + 8)) (.n 5) (.n (f + 7)),
    .copy (.n (f + 9)) (.n (f + 8))]

/-- The atoms of `opening_message__L{n}_L{nonce}`. -/
def omAtoms (n nonce : ℕ) : List Atom :=
  [.copy (.n 7) (.n 0), .copy (.n 8) (.n 1), .copy (.n 9) (.n 2), .copy (.n 10) (.n 3),
    .copy (.n 11) (.n 4)] ++ omWords n ++ (omTail n nonce).1 ++
    omFinal n nonce (omTail n nonce).2.1 (omTail n nonce).2.2

/-- What it returns. -/
def omRets (n nonce : ℕ) : List V :=
  let f := (omTail n nonce).2.2
  [.n f, .n (f + 1), .n (f + 2), .n (f + 3), .n (f + 4), .n (f + 5), .n (f + 6), .n (f + 9)]

/-- **The expansion of `opening_message__L{n}_L{nonce}`.** -/
def omBody (n nonce : ℕ) : List Stmt := (omAtoms n nonce).map Stmt.atom ++ [.ret (omRets n nonce)]

set_option maxRecDepth 100000 in
theorem om_found_1_1 : coreProgram.find? (omName (1, 1)) = some Data.core319 ∧
    Data.core319.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core319.body = omBody 1 1 :=
  ⟨coreProgram_find?_at (j := 319) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem om_found_6_1 : coreProgram.find? (omName (6, 1)) = some Data.core471 ∧
    Data.core471.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core471.body = omBody 6 1 :=
  ⟨coreProgram_find?_at (j := 471) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem om_found_8_1 : coreProgram.find? (omName (8, 1)) = some Data.core461 ∧
    Data.core461.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core461.body = omBody 8 1 :=
  ⟨coreProgram_find?_at (j := 461) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem om_found_12_1 : coreProgram.find? (omName (12, 1)) = some Data.core536 ∧
    Data.core536.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core536.body = omBody 12 1 :=
  ⟨coreProgram_find?_at (j := 536) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem om_found_20_1 : coreProgram.find? (omName (20, 1)) = some Data.core578 ∧
    Data.core578.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core578.body = omBody 20 1 :=
  ⟨coreProgram_find?_at (j := 578) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem om_found_36_1 : coreProgram.find? (omName (36, 1)) = some Data.core621 ∧
    Data.core621.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
      Data.core621.body = omBody 36 1 :=
  ⟨coreProgram_find?_at (j := 621) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

end
end LeanVM.Guest.B1
