module

public import NativeRustcVmX64.Ring.Seq
public meta import NativeRustcVmX64.Ring.Seq
public import NativeRustcVmX64.Code.Vm.RingWeight
public import NativeRustcVmX64.Transcript.Glue
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `ring_weight`'s templates (x86-64)

Region `0` the 672-byte frame (the six pushes from `624`, the 36 powers from `48`, the spills:
the high limb at `8`, the coefficients' address at `16`, the output's at `24`, the coefficient's
offset at `32`, the low limb at `40`; a callee's return address at `0`) and the return address.
A template's region sizes `sz` and aliases `al` are parameters: the arrays a block reads are the
windows of region `1`. The variables: `0` to `5` the pushed registers, `6`, `7` RAX, RDX (a
product, a square), `8` the output's address, `9` the coefficients', `10` `r`'s, `11` `|r|`, `12`
`r'`'s, `13` `|r'|`, `14` `16 |r|`, `15` the powers' end, `16` `min(|r|, |r'|)`, `17` its `16`-fold,
`19` the coefficient's offset, `20`, `21` the total, `23`, `24` the spilled limbs (high, low),
`25` `|r|`'s even part. A loop's index is a literal of its template (`tC t`, `tP i`, `tS j`, …).
`JOk`, `COk`, `missR`, `storeOk`, `SwOk`: what the kernel checks of a block run (`Facts*`).
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Vm.RingWeight
open NativeRustcVmX64.Transcript (after)

@[expose] public section

/-- The pushes: RBP, R15, R14, R13, R12, RBX from offset `664` down, the variables `0` to `5`. -/
def pushW : List Write :=
  [⟨0, 664, 8, .var 0⟩, ⟨0, 656, 8, .var 1⟩, ⟨0, 648, 8, .var 2⟩, ⟨0, 640, 8, .var 3⟩,
    ⟨0, 632, 8, .var 4⟩, ⟨0, 624, 8, .var 5⟩]

/-- The output's address. -/
def oW : Write := ⟨0, 24, 8, .var 8⟩
/-- The coefficients' address. -/
def cW : Write := ⟨0, 16, 8, .var 9⟩
/-- The coefficient's offset. -/
def kW : Write := ⟨0, 32, 8, .var 19⟩
/-- The spilled high limb. -/
def hW : Write := ⟨0, 8, 8, .var 23⟩
/-- The spilled low limb. -/
def lW : Write := ⟨0, 40, 8, .var 24⟩

/-- The frame alone. -/
def sz0 : List Nat := [680]
/-- The frame and a window of `n` bytes. -/
def sz1 (n : Nat) : List Nat := [680, n]

/-- A template of the body: RSP at the frame's offset `8`, the pushes. -/
def wt (sz : List Nat) (known : List (Reg64 × Sym)) (ws : List Write)
    (al : List (Sym × Nat × Int)) : SState :=
  tpl sz ((.rsp, .ptr 0 8) :: known) (ws ++ pushW) [] al

/-- At the entry. -/
def t0 : SState := tpl sz0 [(.rsp, .ptr 0 672)] []

/-- `b1`, `b3`: the arguments. -/
def tA (sz : List Nat) (al : List (Sym × Nat × Int)) : SState :=
  wt sz [(.rsi, .var 10), (.rdx, .var 11), (.rcx, .var 12), (.r8, .var 13), (.r9, .var 9)] [oW] al

/-- `b2`, `b6`. -/
def tB (sz : List Nat) (al : List (Sym × Nat × Int)) : SState :=
  wt sz [(.rsi, .var 10), (.r12, .var 11), (.rax, .var 14), (.r8, .var 13), (.r9, .var 9),
    (.r15, .var 12)] [oW] al

/-- `r` through RSI. -/
def rAl : List (Sym × Nat × Int) := [(.var 10, 1, 0)]
/-- `r'` through R15. -/
def qAl : List (Sym × Nat × Int) := [(.var 12, 1, 0)]
/-- The coefficients through R9. -/
def cAl : List (Sym × Nat × Int) := [(.var 9, 1, 0)]
/-- A coefficient's window through R9 plus its offset. -/
def kAl : List (Sym × Nat × Int) := [(.bin .add .W64 (.var 9) (.var 19), 1, 0)]
/-- The output through its spilled address. -/
def oAl : List (Sym × Nat × Int) := [(.var 8, 1, 0)]

/-- `b7`, `b8`: the pairs' copy at turn `t`. -/
def tC (sz : List Nat) (al : List (Sym × Nat × Int)) (t : Nat) : SState :=
  wt sz [(.rdi, .lit (24 + 32 * t)), (.rcx, .lit (2 * t)), (.rdx, .var 25), (.rsi, .var 10),
    (.r12, .var 11), (.rax, .var 14), (.r8, .var 13), (.r9, .var 9), (.r15, .var 12)] [oW] al

/-- `b9`: the last element `c`. -/
def tL (sz : List Nat) (al : List (Sym × Nat × Int)) (c : Nat) : SState :=
  wt sz [(.rcx, .lit c), (.rsi, .var 10), (.rax, .var 14), (.r8, .var 13), (.r12, .var 11),
    (.r9, .var 9), (.r15, .var 12)] [oW] al

/-- `b10`. -/
def tD (sz : List Nat) (al : List (Sym × Nat × Int)) : SState :=
  wt sz [(.rax, .var 14), (.r8, .var 13), (.r12, .var 11), (.r9, .var 9), (.r15, .var 12)] [oW] al

/-- `b11`, `b20`. -/
def tF (sz : List Nat) (al : List (Sym × Nat × Int)) : SState :=
  wt sz [(.rbx, .var 15), (.r12, .var 16), (.r15, .var 12), (.r9, .var 9)] [oW, cW] al

/-- `b12`, the coefficients' loop. -/
def tO (sz : List Nat) (al : List (Sym × Nat × Int)) : SState :=
  wt sz [(.r9, .var 9), (.rcx, .var 19), (.rbp, .var 20), (.r13, .var 21), (.r15, .var 12),
    (.r12, .var 17), (.rbx, .var 15)] [oW, cW] al

/-- `b13`, `b14`, `b15`: factor `i` of the product. -/
def tP (sz : List Nat) (al : List (Sym × Nat × Int)) (i : Nat) : SState :=
  wt sz [(.rax, .var 6), (.rdx, .var 7), (.r14, .lit (16 * i)), (.r15, .var 12), (.r12, .var 17),
    (.rbx, .var 15), (.rbp, .var 20), (.r13, .var 21)] [oW, cW, kW] al

/-- `b16`, `b18`: power `j`. -/
def tS (sz : List Nat) (j : Nat) : SState :=
  wt sz [(.r14, .ptr 0 ((48 + 16 * j : Nat) : Int)), (.rbx, .var 15), (.rbp, .var 20),
    (.r13, .var 21), (.r15, .var 12), (.r12, .var 17)] [hW, oW, cW, kW, lW] []

/-- `b17`: power `j`'s square in RAX, RDX. -/
def tSA (sz : List Nat) (j : Nat) : SState :=
  wt sz [(.rax, .var 6), (.rdx, .var 7), (.r14, .ptr 0 ((48 + 16 * j : Nat) : Int)),
    (.rbx, .var 15), (.rbp, .var 20), (.r13, .var 21), (.r15, .var 12), (.r12, .var 17)]
    [hW, oW, cW, kW, lW] []

/-- `b5`, `b19`, `b25`: the total. -/
def tE (sz : List Nat) (al : List (Sym × Nat × Int)) : SState :=
  wt sz [(.rbp, .var 20), (.r13, .var 21)] [oW] al

/-- `b21`: the coefficients' loop, `r'` empty. -/
def tO2 (sz : List Nat) (al : List (Sym × Nat × Int)) : SState :=
  wt sz [(.r9, .var 9), (.r15, .var 19), (.rbp, .var 20), (.r13, .var 21), (.rbx, .var 15)]
    [oW, cW] al

/-- `b22`, `b24`: power `j`, `r'` empty. -/
def tS2 (sz : List Nat) (j : Nat) : SState :=
  wt sz [(.r12, .ptr 0 ((48 + 16 * j : Nat) : Int)), (.r14, .var 24), (.r15, .var 19),
    (.rbx, .var 15), (.rbp, .var 20), (.r13, .var 21)] [hW, oW, cW] []

/-- `b23`. -/
def tSA2 (sz : List Nat) (j : Nat) : SState :=
  wt sz [(.rax, .var 6), (.rdx, .var 7), (.r12, .ptr 0 ((48 + 16 * j : Nat) : Int)),
    (.r14, .var 24), (.r15, .var 19), (.rbx, .var 15), (.rbp, .var 20), (.r13, .var 21)]
    [hW, oW, cW] []

/-- `b4`: the coefficients' sum at turn `t`, `r` empty. -/
def tZ (sz : List Nat) (al : List (Sym × Nat × Int)) (t : Nat) : SState :=
  wt sz [(.r9, .var 9), (.rax, .lit (64 * t)), (.rbp, .var 20), (.r13, .var 21)] [oW] al

end

@[expose] public section

/-! ## Values the blocks compute -/

/-- Four coefficients' limbs summed into the variable `v` (`b4`), from offset `o`. -/
def sumX (v o : Nat) : Sym :=
  .bin .xor .W64 (.bin .xor .W64 (.bin .xor .W64 (.bin .xor .W64 (.var v) (.load 1 o 8))
    (.load 1 (o + 16) 8)) (.load 1 (o + 32) 8)) (.load 1 (o + 48) 8)

/-- `|r|`'s even part (`b6`). -/
def and25 : Sym := .bin .and .W32 (.un .trunc .W32 (.var 11)) (.lit 62)
/-- The powers' end (`b10`). -/
def end15 : Sym := .bin .add .W64 (.lit 40) (.bin .add .W64 (.ptr 0 8) (.var 14))
/-- `min(|r|, |r'|)` (`b10`). -/
def min16 : Sym := .ite (.cmp .ult .W64 (.var 13) (.var 11)) (.var 13) (.var 11)
/-- The next coefficient's offset (`b18`, `b24`). -/
def k16 : Sym := .bin .add .W64 (.lit 16) (.var 19)
/-- The total plus the spilled pair (`b18`, `b24`). -/
def t20 : Sym := .bin .xor .W64 (.var 20) (.var 24)
def t21 : Sym := .bin .xor .W64 (.var 21) (.var 23)
/-- Factor `i`'s limbs: `1 + P_i + r'_i` (`b13`). -/
def fA (i : Nat) : Sym :=
  .bin .xor .W64 (.bin .xor .W64 (.load 0 (48 + 16 * i) 8) (.load 1 (16 * i) 8)) (.lit 1)
def fB (i : Nat) : Sym := .bin .xor .W64 (.load 1 (16 * i + 8) 8) (.load 0 (56 + 16 * i) 8)

/-! ## Links -/

/-- The pushes. -/
def pL : List (Nat × Sym) :=
  [(0, .var 0), (1, .var 1), (2, .var 2), (3, .var 3), (4, .var 4), (5, .var 5)]
def oL : List (Nat × Sym) := (8, .var 8) :: pL
def ocL : List (Nat × Sym) := (8, .var 8) :: (9, .var 9) :: pL
def ockL : List (Nat × Sym) := (8, .var 8) :: (9, .var 9) :: (19, .var 19) :: pL
def sL : List (Nat × Sym) :=
  (23, .var 23) :: (8, .var 8) :: (9, .var 9) :: (19, .var 19) :: (24, .var 24) :: pL
def s2L : List (Nat × Sym) := (23, .var 23) :: ocL
/-- The registers the squaring loop keeps. -/
def qkL : List (Nat × Sym) := [(15, .var 15), (20, .var 20), (17, .var 17), (21, .var 21), (12, .var 12)]
def q2L : List (Nat × Sym) := [(15, .var 15), (20, .var 20), (21, .var 21), (24, .var 24), (19, .var 19)]
/-- The copy's registers. -/
def cpL : List (Nat × Sym) := [(14, .var 14), (10, .var 10), (13, .var 13), (9, .var 9), (11, .var 11), (12, .var 12)]

/-! ## Checks of a block -/

/-- A block without a call from `T`, ending in `x`, its writes in the frame or the writable windows
(`sizes`, `wr`), linked to the template `T'` by `L`, `LW`. -/
def JOk (ds : List Directive) (T T' : SState) (x : Exit) (sizes : List Nat) (wr : Nat → Bool)
    (L LW : List (Nat × Sym)) : Bool :=
  decide (exec ds T = some (after ds T, x)) &&
    (after ds T).mem.all (writeOk 672 sizes wr) &&
    decide (rlinks false (after ds T) T' = some L) && decide (wlinks (after ds T) T'.mem = some LW)

/-- A block ending in a call of `EW::mul`, RSP at the call slot, writing in the frame. -/
def COk (ds : List Directive) (T T' : SState) (sizes : List Nat) (L LW : List (Nat × Sym)) : Bool :=
  decide (exec ds T = some (after ds T, .call NativeRustcVmX64.Vm.EWMul.entryLabel)) &&
    (after ds T).mem.all (writeOk 672 sizes (fun _ ↦ false)) &&
    decide ((after ds T).reg .rsp = some (.ptr 0 0)) &&
    decide (rlinks true (after ds T) T' = some L) && decide (wlinks (after ds T) T'.mem = some LW)

/-- The block's writes miss the frame's bytes from `lo` to `hi`, all in the frame. -/
def missR (lo hi : Nat) (S : SState) : Bool :=
  S.mem.all fun w ↦ w.r == 0 && (decide (w.off + w.n ≤ lo) || decide (hi ≤ w.off))

/-- The block stores the words `a`, `b` at the frame's offset `o`, `o + 8`. -/
def storeOk (S : SState) (o : Nat) (a b : Sym) : Bool :=
  (List.range 8).all fun u ↦ findWrite 0 (o + u) S.mem == some (a, u) &&
    findWrite 0 (o + 8 + u) S.mem == some (b, u)

/-- Switching templates: `T'`'s registers and writes are `T`'s (identity links), its flags atoms,
no labels or bounds. -/
def SwOk (T T' : SState) : Bool :=
  tplOk T' && T'.flags == atomFlags && T'.labels.isEmpty && T'.bounds.isEmpty &&
    (match rlinks false T T', wlinks T T'.mem with
      | some L, some LW => (L ++ LW).all fun p ↦ p.2 == .var p.1
      | _, _ => false)

end

end NativeRustcVmX64.Ring.Weight
