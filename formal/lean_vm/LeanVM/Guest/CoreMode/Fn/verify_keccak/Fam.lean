/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.Fam

  `verify_keccak`'s own residual family (`CoreMode/FnReg.lean`): its exponent facts, its rule file's `arg_bound`s,
  `sel_bound` and `fact`, its equation residual (`RES_EQ`), its runs and its stream (`fn/verify_keccak.py`).
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.CoreMode.Own.verify_keccak

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The values `x` and their exponent bounds `n`, `e(x) < n`: `pack_g` (`18`), `step_g` (`29`), `rem_g` (`48`),
`tau_g` (`6`). -/
def expB : List (ℕ × ℕ) := [(18, 21), (29, 2), (48, 16), (6, 25)]

/-- **Its exponent facts**: `e(x) < n`, `(x, m) ∈ expB`, `m ≤ n < capE`; `c < e(tau_g)`, `c < 9` (value `6`). -/
def expFam (r : CRes) : Bool :=
  match r with
  | .lt (.val x) (.num n) => Nat.blt n capE && expB.any fun p ↦ Nat.beq p.1 x && Nat.ble p.2 n
  | .lt (.num c) (.val x) => Nat.beq x 6 && Nat.blt c 9
  | _ => false

/-- **Its equation residual**: step `0`'s claim point (value `443`, loaded from `claims·g^KC_POINT`) is the point
(value `62`) loaded there before. -/
def ptEq : CRes := .eq ⟨[(443, 1)], 0⟩ ⟨[(62, 1)], 0⟩

/-- `pack_g = tau_g·g^-4` as a monomial (values `6`, `17`). -/
def pM : List (ℕ × ℕ) := [(6, 1), (17, 1)]

/-- `rem_g` as the product of its bit factors (values `33`, `37`, `42`, `47`). -/
def remM : List (ℕ × ℕ) := [(33, 1), (37, 1), (42, 1), (47, 1)]

/-- `y_g = step_g^16·rem_g` (`step_g` value `29`). -/
def yC : CCell := ⟨(29, 16) :: remM, 0⟩

/-- A run past one base. -/
def run1 (b o S : ℕ) (lo hi : CIdx) : CRun := ⟨⟨[(b, 1)], o⟩, S, lo, hi⟩

/-- **Its runs over the head's exponents**: loop0's run `chi·g^4·[0, e(pack_g))` inside `chi[0, e(tau_g))`; the point's
(value `62`) residue runs over `step_g` and its run past `step_g^16` inside its whole run `[0, e(y_g))`; loop2's reads
of the last layer's point (value `1740`) `[0, e(pack_g))` inside its whole run; `z_vals`' (value `9`) pack coordinates
`[4, e(tau_g))` at offsets `0` and `QKECCAK_VARS_CAP = 39`, as loops 1 and 2 write them. -/
def vkRuns : List CRes :=
  [.subR (run1 7 4 1 (.num 0) (.mono ⟨pM, 0⟩)) (run1 7 0 1 (.num 0) (.val 6)),
    .subR ⟨⟨[(29, 16), (62, 1)], 0⟩, 1, .num 0, .mono ⟨remM, 0⟩⟩ (run1 62 0 1 (.num 0) (.mono yC)),
    .subR (run1 1740 0 1 (.num 0) (.mono ⟨pM, 0⟩)) (run1 1740 0 1 (.num 0) (.mono yC)),
    .subR (run1 9 0 1 (.num 4) (.val 6)) (run1 9 4 1 (.num 0) (.mono ⟨pM, 0⟩)),
    .subR (run1 9 39 1 (.num 4) (.val 6)) (run1 9 43 1 (.num 0) (.mono ⟨pM, 0⟩))] ++
  (List.range 16).map fun d ↦ .subR (run1 62 d 16 (.num 0) (.val 29)) (run1 62 0 1 (.num 0) (.mono yC))

/-- **Its runs** (`vkRuns`), under any conditions; `e(pack_g) < n`, `21 ≤ n`; `c < e(pack_g·g^k)`, `c < 5 + k`. -/
def runFam (r : CRes) : Bool :=
  decide (r ∈ vkRuns) || match r with
    | .under _ r' => decide (r' ∈ vkRuns)
    | .lt (.mono c) (.num n) => decide (c = ⟨pM, 0⟩) && Nat.ble 21 n && Nat.blt n capE
    | .lt (.num c) (.mono m) => decide (m.bases = pM) && Nat.blt c (5 + m.off) && Nat.blt m.off 4294967296
    | _ => false

/-! ## The proof stream -/

/-- **The exponents at height `h`** (`tau_g = g^h`, `y = h - 3`) of its head's values: `tau_g` (`6`), `step_g = g^(y / 16)`
(`29`), `rem_g = g^(y % 16)` (`48`) and `rem_g`'s bit factors `g^(2^j·b_j)` (`33`, `37`, `42`, `47`). -/
def stEx (h v : ℕ) : Option ℕ :=
  if v = 6 then some h else if v = 29 then some ((h - 3) / 16) else if v = 48 then some ((h - 3) % 16)
  else if v = 33 then some ((h - 3) % 2) else if v = 37 then some (2 * ((h - 3) / 2 % 2))
  else if v = 42 then some (4 * ((h - 3) / 4 % 2)) else if v = 47 then some (8 * ((h - 3) / 8 % 2)) else none

/-- A product of the head's values' powers, its exponent at height `h`. -/
def stSum (h : ℕ) : List (ℕ × ℕ) → Option ℕ
  | [] => some 0
  | (v, a) :: l => match stEx h v, stSum h l with
    | some e, some s => some (a * e + s)
    | _, _ => none

/-- An index's exponent at height `h`. -/
def stIdx (h : ℕ) : CIdx → Option ℕ
  | .num n => some n
  | .val v => stEx h v
  | .mono c => (stSum h c.bases).map (· + c.off)

/-- **The stream's run**: its `24` residue runs `⟨cursor·g^d, 24, 0, e(tau_g) + 44⟩` merged (`cursor` value `5`),
`cursor·g^j`, `j < 24·(e(tau_g) + 44)`. -/
def stQ : CRun := ⟨⟨[(5, 1)], 0⟩, 1, .num 0, .mono ⟨[(6, 24)], 1056⟩⟩

/-- **A run over `cursor` inside the stream's at height `h`**: its base `cursor·M·g^o`, `M` and its bounds over the
head's values, its last cell's exponent below `24·(h + 44)`. -/
def stRunAt (q : CRun) (h : ℕ) : Bool :=
  decide (q.base.bases.head? = some (5, 1)) &&
  match stSum h q.base.bases.tail, stIdx h q.lo, stIdx h q.hi with
  | some t, some l, some u => Nat.blt u 4294967296 && Nat.blt l 4294967296 &&
      (Nat.ble u l || Nat.blt (t + q.base.off + q.stride * (u - 1)) (24 * (h + 44)))
  | _, _, _ => false

/-- At every height `9 ≤ h ≤ 24`. -/
def stRunOk (q : CRun) : Bool := (List.range 16).all fun i ↦ stRunAt q (9 + i)

/-- A bound over the head's values below a constant at every height (the stream runs' `e(tau_g) + 44`). -/
def stLt : CIdx → CIdx → Bool
  | .mono c, .num n => Nat.blt n 4611686018427387904 && (List.range 16).all fun i ↦
      match stIdx (9 + i) (.mono c) with
      | some t => Nat.blt t n
      | none => false
  | _, _ => false

/-- **The stream family**: a read `sub c stQ` and a callee's run `subR q stQ` inside the stream at every height, and
a bound `stLt`, under any conditions. -/
def stFam : CRes → Bool
  | .lt a b => stLt a b
  | .sub c r => decide (r = stQ) && stRunOk ⟨c, 1, .num 0, .num 1⟩
  | .subR q r => decide (r = stQ) && stRunOk q
  | .under _ r => stFam r
  | _ => false

/-- **Its family**: its exponent facts (`expFam`), its equation residual (`ptEq`), its runs (`runFam`), its stream
(`stFam`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) :=
  [(name% «verify_keccak», fun _ r ↦ expFam r || decide (r = ptEq) || runFam r || stFam r)]

end

end LeanVM.Guest.CoreMode.Own.verify_keccak
