module

public import NativeRustcX64.KeccakF.Inv
public import NativeRustcX64.KeccakF.Blocks

/-!
# Each half of the unrolled loop computes `permute`'s round (x86-64)

The cut at `firstHalf.length` exposes a completed round before the second round starts.
The scalar lane and parity summaries use a proved bitvector representation of `roundCL` and
normalize XOR reassociation under rotations and AND-NOT. The current pair of constants is a
16-byte region, so both indexed constant loads have fixed offsets.
-/

namespace NativeRustcX64.KeccakF

open NativeRustcX64.Sym NativeRustc.Keccak LeanVM.Semantics

public section

/-- A rotation count of a literal below 64 is the literal. -/
theorem shiftCount_lit {n : Nat} (h : n < 64) : shiftCount .W64 (BitVec.ofNat 64 n) = n := by
  have h8 : Width.W8.bits = 8 := rfl
  simp only [shiftCount, shiftMask, low, BitVec.toNat_setWidth, BitVec.toNat_ofNat, h8]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) (by omega)

@[expose] def thetaBV (c : Nat → BitVec 64) (x : Nat) : BitVec 64 :=
  c ((x + 4) % 5) ^^^ (c ((x + 1) % 5)).rotateLeft 1

@[expose] def tBV (a c : Nat → BitVec 64) (i : Nat) : BitVec 64 :=
  a i ^^^ thetaBV c (i % 5)

@[expose] def bBV (a c : Nat → BitVec 64) : Nat → BitVec 64
  | 0 => tBV a c 0
  | 1 => (tBV a c 6).rotateLeft 44
  | 2 => (tBV a c 12).rotateLeft 43
  | 3 => (tBV a c 18).rotateLeft 21
  | 4 => (tBV a c 24).rotateLeft 14
  | 5 => (tBV a c 3).rotateLeft 28
  | 6 => (tBV a c 9).rotateLeft 20
  | 7 => (tBV a c 10).rotateLeft 3
  | 8 => (tBV a c 16).rotateLeft 45
  | 9 => (tBV a c 22).rotateLeft 61
  | 10 => (tBV a c 1).rotateLeft 1
  | 11 => (tBV a c 7).rotateLeft 6
  | 12 => (tBV a c 13).rotateLeft 25
  | 13 => (tBV a c 19).rotateLeft 8
  | 14 => (tBV a c 20).rotateLeft 18
  | 15 => (tBV a c 4).rotateLeft 27
  | 16 => (tBV a c 5).rotateLeft 36
  | 17 => (tBV a c 11).rotateLeft 10
  | 18 => (tBV a c 17).rotateLeft 15
  | 19 => (tBV a c 23).rotateLeft 56
  | 20 => (tBV a c 2).rotateLeft 62
  | 21 => (tBV a c 8).rotateLeft 55
  | 22 => (tBV a c 14).rotateLeft 39
  | 23 => (tBV a c 15).rotateLeft 41
  | 24 => (tBV a c 21).rotateLeft 2
  | _ => 0

@[expose] def roundBV (a c : Nat → BitVec 64) (rc : BitVec 64) (j : Nat) : BitVec 64 :=
  if j = 0 then (bBV a c 0 ^^^ (~~~ bBV a c 1 &&& bBV a c 2)) ^^^ rc
  else bBV a c j ^^^
    (~~~ bBV a c (j - j % 5 + (j + 1) % 5) &&& bBV a c (j - j % 5 + (j + 2) % 5))


theorem tC_toBV (a c : Nat → UInt64) (i : Nat) :
    (tC a c i).toBitVec = tBV (fun j => (a j).toBitVec) (fun j => (c j).toBitVec) i := by
  simp only [tC, tBV, thetaD, thetaBV, UInt64.toBitVec_xor,
    toBitVec_rot_left _ (by decide : 1 < 64)]

theorem bC_toBV (a c : Nat → UInt64) (j : Nat) :
    (bC a c j).toBitVec = bBV (fun k => (a k).toBitVec) (fun k => (c k).toBitVec) j := by
  by_cases hj : j < 25
  · interval_cases j <;>
      simp (disch := decide) only [bC, bBV, rot_zero, toBitVec_rot_left, tC_toBV]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 25 := ⟨j - 25, by omega⟩
    rfl

theorem roundCL_toBV (a c : Nat → UInt64) (rc : UInt64) (j : Nat) :
    (roundCL a c rc j).toBitVec =
      roundBV (fun k => (a k).toBitVec) (fun k => (c k).toBitVec) rc.toBitVec j := by
  unfold roundCL roundBV
  split <;> simp only [chi, UInt64.toBitVec_xor, UInt64.toBitVec_and,
    UInt64.toBitVec_not, bC_toBV]


/-- Unfolds a lane of `permute`'s round to 64-bit vector operations on its inputs. -/
macro "round_simp" : tactic => `(tactic| (
  simp only [roundCL_toBV]
  simp only [roundBV, bBV, tBV, thetaBV, Nat.reduceMod,
    Nat.reduceAdd, Nat.reduceSub, reduceIte, OfNat.ofNat_ne_zero, Nat.succ_ne_zero]))

theorem wordAt_eq {m : MachineData} {b : BitVec 64} {o : Nat} {v w : BitVec 64}
    (hv : WordAt m.dmem (b + BitVec.ofNat 64 o) v)
    (hw : WordAt m.dmem (b + BitVec.ofNat 64 o) w) : v = w :=
  (load_of_wordAt (env := Env.ofMachine m [(b, 296)]) (r := 0) (off := o) hv).symm.trans
    (load_of_wordAt (env := Env.ofMachine m [(b, 296)]) (r := 0) (off := o) hw)

theorem eval_xor [Labels] (env : Env) (x y : Sym) :
    (Sym.bin .xor .W64 x y).eval env = x.eval env ^^^ y.eval env := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

theorem eval_rol_one [Labels] (env : Env) (x : Sym) :
    (Sym.bin .rol .W64 x (.lit 1)).eval env = (x.eval env).rotateLeft 1 := by
  simp (disch := decide) only [Sym.eval, BinOp.apply, low_W64, ext_W64, shiftCount_lit]

macro "first_lane" hx:ident hm:ident hb:ident hregs:ident hslots:ident hpar:ident
    hrc:ident kind:ident : tactic => do
  let projection ← if kind.getId == `slot then
    `(tactic| refine wordAt_of_eq (wordAt_write $hm $hb (by decide) rfl) ?_)
    else `(tactic| refine (($hm).regs _ _ rfl).trans ?_)
  `(tactic| (
    rw [firstBody] at $hx:ident
    cases ($hx)
    simp only [AllOf, laneRegs, laneSlots, parRegs] at $hregs:ident $hslots:ident $hpar:ident
    obtain ⟨h3, h4, h12, h18, h20, h22, h24, -⟩ := $hregs
    obtain ⟨h0, h1, h2, h5, h6, h7, h8, h9, h10, h11, h13, h14, h15, h16, h17, h19, h21, h23, -⟩ := $hslots
    obtain ⟨c0, c1, c2, c3, c4, -⟩ := $hpar
    $projection:tactic
    clear $hm:ident
    simp +instances (disch := decide) only [Sym.eval, SBool.eval, BinOp.apply, UnOp.apply, TernOp.apply,
      CmpOp.apply, low_W64, ext_W64, bytesOf, shiftCount_lit, Width.bits]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, c0, c1, c2, c3, c4, ($hrc)]
    round_simp
    simp +instances only [Width.bits, BitVec.xor_comm, BitVec.and_comm]
    all_goals ac_rfl))

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_reg_rsi [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .rsi = (roundCL a c rc 6).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_reg_r10 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .r10 = (roundCL a c rc 20).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_reg_rdi [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .rdi = (roundCL a c rc 21).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_reg_rbp [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .rbp = (roundCL a c rc 22).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_reg_r14 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .r14 = (roundCL a c rc 23).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_reg_r12 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .r12 = (roundCL a c rc 24).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_232 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 232) (roundCL a c rc 0).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_208 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 208) (roundCL a c rc 1).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_200 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 200) (roundCL a c rc 2).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_136 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 136) (roundCL a c rc 3).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_128 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 128) (roundCL a c rc 4).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_80 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 80) (roundCL a c rc 5).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_32 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 32) (roundCL a c rc 7).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_24 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 24) (roundCL a c rc 8).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_8 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 8) (roundCL a c rc 9).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_64 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 64) (roundCL a c rc 10).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_176 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 176) (roundCL a c rc 11).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_16 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 16) (roundCL a c rc 12).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_0 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 0) (roundCL a c rc 13).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_88 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 88) (roundCL a c rc 14).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_72 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 72) (roundCL a c rc 15).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_40 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 40) (roundCL a c rc 16).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_104 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 104) (roundCL a c rc 17).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_120 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 120) (roundCL a c rc 18).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_56 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 56) (roundCL a c rc 19).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_184 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 184) (roundCL a c rc 20).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_112 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 112) (roundCL a c rc 21).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_slot_96 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    WordAt m.dmem (b + BitVec.ofNat 64 96) (roundCL a c rc 23).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_reg_rdx [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .rdx = (roundCL a c rc 0).toBitVec := by
  first_lane hx hm hb hregs hslots hpar hrc reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_parity_r9 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .r9 = (newPar a c rc 0).toBitVec := by
  have h0 := first_slot_232 hx hm hb hregs hslots hpar hrc
  have h5 := first_slot_80 hx hm hb hregs hslots hpar hrc
  have h10 := first_slot_64 hx hm hb hregs hslots hpar hrc
  have h15 := first_slot_72 hx hm hb hregs hslots hpar hrc
  have h20 := first_reg_r10 hx hm hb hregs hslots hpar hrc
  rw [firstBody] at hx
  cases hx
  have e0 := wordAt_eq (wordAt_write hm hb (o := 232) (by decide) rfl) h0
  have e5 := wordAt_eq (wordAt_write hm hb (o := 80) (by decide) rfl) h5
  have e10 := wordAt_eq (wordAt_write hm hb (o := 64) (by decide) rfl) h10
  have e15 := wordAt_eq (wordAt_write hm hb (o := 72) (by decide) rfl) h15
  have e20 := (hm.regs .r10 _ rfl).symm.trans h20
  refine (hm.regs .r9 _ rfl).trans ?_
  simp only [newPar, UInt64.toBitVec_xor]
  rw [← e0, ← e5, ← e10, ← e15, ← e20]
  clear hm
  simp only [eval_xor]
  ac_rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_parity_r13 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .r13 = (newPar a c rc 1).toBitVec := by
  have h1 := first_slot_208 hx hm hb hregs hslots hpar hrc
  have h6 := first_reg_rsi hx hm hb hregs hslots hpar hrc
  have h11 := first_slot_176 hx hm hb hregs hslots hpar hrc
  have h16 := first_slot_40 hx hm hb hregs hslots hpar hrc
  have h21 := first_reg_rdi hx hm hb hregs hslots hpar hrc
  rw [firstBody] at hx
  cases hx
  have e1 := wordAt_eq (wordAt_write hm hb (o := 208) (by decide) rfl) h1
  have e6 := (hm.regs .rsi _ rfl).symm.trans h6
  have e11 := wordAt_eq (wordAt_write hm hb (o := 176) (by decide) rfl) h11
  have e16 := wordAt_eq (wordAt_write hm hb (o := 40) (by decide) rfl) h16
  have e21 := (hm.regs .rdi _ rfl).symm.trans h21
  refine (hm.regs .r13 _ rfl).trans ?_
  simp only [newPar, UInt64.toBitVec_xor]
  rw [← e1, ← e6, ← e11, ← e16, ← e21]
  clear hm
  simp only [eval_xor]
  ac_rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_parity_r11 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .r11 = (newPar a c rc 2).toBitVec := by
  have h2 := first_slot_200 hx hm hb hregs hslots hpar hrc
  have h7 := first_slot_32 hx hm hb hregs hslots hpar hrc
  have h12 := first_slot_16 hx hm hb hregs hslots hpar hrc
  have h17 := first_slot_104 hx hm hb hregs hslots hpar hrc
  have h22 := first_reg_rbp hx hm hb hregs hslots hpar hrc
  rw [firstBody] at hx
  cases hx
  have e2 := wordAt_eq (wordAt_write hm hb (o := 200) (by decide) rfl) h2
  have e7 := wordAt_eq (wordAt_write hm hb (o := 32) (by decide) rfl) h7
  have e12 := wordAt_eq (wordAt_write hm hb (o := 16) (by decide) rfl) h12
  have e17 := wordAt_eq (wordAt_write hm hb (o := 104) (by decide) rfl) h17
  have e22 := (hm.regs .rbp _ rfl).symm.trans h22
  refine (hm.regs .r11 _ rfl).trans ?_
  simp only [newPar, UInt64.toBitVec_xor]
  rw [← e2, ← e7, ← e12, ← e17, ← e22]
  clear hm
  simp only [eval_xor]
  ac_rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_parity_r15 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .r15 = (newPar a c rc 3).toBitVec := by
  have h3 := first_slot_136 hx hm hb hregs hslots hpar hrc
  have h8 := first_slot_24 hx hm hb hregs hslots hpar hrc
  have h13 := first_slot_0 hx hm hb hregs hslots hpar hrc
  have h18 := first_slot_120 hx hm hb hregs hslots hpar hrc
  have h23 := first_reg_r14 hx hm hb hregs hslots hpar hrc
  rw [firstBody] at hx
  cases hx
  have e3 := wordAt_eq (wordAt_write hm hb (o := 136) (by decide) rfl) h3
  have e8 := wordAt_eq (wordAt_write hm hb (o := 24) (by decide) rfl) h8
  have e13 := wordAt_eq (wordAt_write hm hb (o := 0) (by decide) rfl) h13
  have e18 := wordAt_eq (wordAt_write hm hb (o := 120) (by decide) rfl) h18
  have e23 := (hm.regs .r14 _ rfl).symm.trans h23
  refine (hm.regs .r15 _ rfl).trans ?_
  simp only [newPar, UInt64.toBitVec_xor]
  rw [← e3, ← e8, ← e13, ← e18, ← e23]
  clear hm
  simp only [eval_xor]
  ac_rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_parity_r8 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .r8 = (newPar a c rc 4).toBitVec := by
  have h4 := first_slot_128 hx hm hb hregs hslots hpar hrc
  have h9 := first_slot_8 hx hm hb hregs hslots hpar hrc
  have h14 := first_slot_88 hx hm hb hregs hslots hpar hrc
  have h19 := first_slot_56 hx hm hb hregs hslots hpar hrc
  have h24 := first_reg_r12 hx hm hb hregs hslots hpar hrc
  rw [firstBody] at hx
  cases hx
  have e4 := wordAt_eq (wordAt_write hm hb (o := 128) (by decide) rfl) h4
  have e9 := wordAt_eq (wordAt_write hm hb (o := 8) (by decide) rfl) h9
  have e14 := wordAt_eq (wordAt_write hm hb (o := 88) (by decide) rfl) h14
  have e19 := wordAt_eq (wordAt_write hm hb (o := 56) (by decide) rfl) h19
  have e24 := (hm.regs .r12 _ rfl).symm.trans h24
  refine (hm.regs .r8 _ rfl).trans ?_
  simp only [newPar, UInt64.toBitVec_xor]
  rw [← e4, ← e9, ← e14, ← e19, ← e24]
  clear hm
  simp only [eval_xor]
  ac_rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem first_rot_rbx [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    m.regs.get64 .rbx = (newPar a c rc 3).toBitVec.rotateLeft 1 := by
  have hc := first_parity_r15 hx hm hb hregs hslots hpar hrc
  rw [firstBody] at hx
  cases hx
  rw [← hc, hm.regs .rbx _ rfl, hm.regs .r15 _ rfl]
  exact eval_rol_one env _

theorem first_regs [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    AllOf (fun p : Reg64 × Nat => m.regs.get64 p.1 = (roundCL a c rc p.2).toBitVec) midLaneRegs :=
  ⟨first_reg_rsi hx hm hb hregs hslots hpar hrc,
    first_reg_r10 hx hm hb hregs hslots hpar hrc,
    first_reg_rdi hx hm hb hregs hslots hpar hrc,
    first_reg_rbp hx hm hb hregs hslots hpar hrc,
    first_reg_r14 hx hm hb hregs hslots hpar hrc,
    first_reg_r12 hx hm hb hregs hslots hpar hrc,
    first_reg_rdx hx hm hb hregs hslots hpar hrc,
    trivial⟩

theorem first_slots [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    AllOf (fun p : Nat × Nat => WordAt m.dmem (b + BitVec.ofNat 64 p.1)
      (roundCL a c rc p.2).toBitVec) midLaneSlots :=
  ⟨first_slot_232 hx hm hb hregs hslots hpar hrc,
    first_slot_208 hx hm hb hregs hslots hpar hrc,
    first_slot_200 hx hm hb hregs hslots hpar hrc,
    first_slot_136 hx hm hb hregs hslots hpar hrc,
    first_slot_128 hx hm hb hregs hslots hpar hrc,
    first_slot_80 hx hm hb hregs hslots hpar hrc,
    first_slot_32 hx hm hb hregs hslots hpar hrc,
    first_slot_24 hx hm hb hregs hslots hpar hrc,
    first_slot_8 hx hm hb hregs hslots hpar hrc,
    first_slot_64 hx hm hb hregs hslots hpar hrc,
    first_slot_176 hx hm hb hregs hslots hpar hrc,
    first_slot_16 hx hm hb hregs hslots hpar hrc,
    first_slot_0 hx hm hb hregs hslots hpar hrc,
    first_slot_88 hx hm hb hregs hslots hpar hrc,
    first_slot_72 hx hm hb hregs hslots hpar hrc,
    first_slot_40 hx hm hb hregs hslots hpar hrc,
    first_slot_104 hx hm hb hregs hslots hpar hrc,
    first_slot_120 hx hm hb hregs hslots hpar hrc,
    first_slot_56 hx hm hb hregs hslots hpar hrc,
    first_slot_184 hx hm hb hregs hslots hpar hrc,
    first_slot_112 hx hm hb hregs hslots hpar hrc,
    first_slot_96 hx hm hb hregs hslots hpar hrc,
    trivial⟩

theorem first_par [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec firstHalf startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 0 8 = rc.toBitVec) :
    AllOf (fun p : Reg64 × Nat => m.regs.get64 p.1 = (newPar a c rc p.2).toBitVec) midParRegs :=
  ⟨first_parity_r9 hx hm hb hregs hslots hpar hrc,
    first_parity_r13 hx hm hb hregs hslots hpar hrc,
    first_parity_r11 hx hm hb hregs hslots hpar hrc,
    first_parity_r15 hx hm hb hregs hslots hpar hrc,
    first_parity_r8 hx hm hb hregs hslots hpar hrc,
    trivial⟩


macro "second_lane" hx:ident hm:ident hb:ident hregs:ident hslots:ident hpar:ident
    hrc:ident hrot:ident kind:ident : tactic => do
  let projection ← if kind.getId == `slot then
    `(tactic| refine wordAt_of_eq (wordAt_write $hm $hb (by decide) rfl) ?_)
    else `(tactic| refine (($hm).regs _ _ rfl).trans ?_)
  `(tactic| (
    rw [secondBody] at $hx:ident
    cases ($hx)
    simp only [AllOf, midLaneRegs, midLaneSlots, midParRegs] at $hregs:ident $hslots:ident $hpar:ident
    obtain ⟨h6, h20, h21, h22, h23, h24, h0r, -⟩ := $hregs
    obtain ⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, s20, s21, s23, -⟩ := $hslots
    obtain ⟨c0, c1, c2, c3, c4, -⟩ := $hpar
    $projection:tactic
    clear $hm:ident
    simp +instances (disch := decide) only [Sym.eval, SBool.eval, BinOp.apply, UnOp.apply, TernOp.apply,
      CmpOp.apply, low_W64, ext_W64, bytesOf, shiftCount_lit, Width.bits]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, c0, c1, c2, c3, c4, ($hrc), ($hrot), s20, s21, s23, h0r]
    round_simp
    simp +instances only [Width.bits, BitVec.xor_comm, BitVec.and_comm]
    all_goals ac_rfl))

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_reg_r11 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    m.regs.get64 .r11 = (roundCL a c rc 3).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_reg_r15 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    m.regs.get64 .r15 = (roundCL a c rc 4).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_reg_rsi [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    m.regs.get64 .rsi = (roundCL a c rc 12).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_reg_r8 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    m.regs.get64 .r8 = (roundCL a c rc 18).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_reg_r10 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    m.regs.get64 .r10 = (roundCL a c rc 20).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_reg_rax [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    m.regs.get64 .rax = (roundCL a c rc 22).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_reg_rbx [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    m.regs.get64 .rbx = (roundCL a c rc 24).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot reg

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_88 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 88) (roundCL a c rc 0).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_144 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 144) (roundCL a c rc 1).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_152 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 152) (roundCL a c rc 2).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_40 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 40) (roundCL a c rc 5).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_8 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 8) (roundCL a c rc 6).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_16 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 16) (roundCL a c rc 7).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_160 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 160) (roundCL a c rc 8).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_48 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 48) (roundCL a c rc 9).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_32 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 32) (roundCL a c rc 10).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_56 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 56) (roundCL a c rc 11).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_64 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 64) (roundCL a c rc 13).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_24 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 24) (roundCL a c rc 14).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_168 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 168) (roundCL a c rc 15).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_80 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 80) (roundCL a c rc 16).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_72 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 72) (roundCL a c rc 17).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_0 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 0) (roundCL a c rc 19).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_112 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 112) (roundCL a c rc 21).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_slot_104 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    WordAt m.dmem (b + BitVec.ofNat 64 104) (roundCL a c rc 23).toBitVec := by
  second_lane hx hm hb hregs hslots hpar hrc hrot slot

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_parity_r14 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    m.regs.get64 .r14 = (newPar a c rc 0).toBitVec := by
  have h0 := second_slot_88 hx hm hb hregs hslots hpar hrc hrot
  have h5 := second_slot_40 hx hm hb hregs hslots hpar hrc hrot
  have h10 := second_slot_32 hx hm hb hregs hslots hpar hrc hrot
  have h15 := second_slot_168 hx hm hb hregs hslots hpar hrc hrot
  have h20 := second_reg_r10 hx hm hb hregs hslots hpar hrc hrot
  rw [secondBody] at hx
  cases hx
  have e0 := wordAt_eq (wordAt_write hm hb (o := 88) (by decide) rfl) h0
  have e5 := wordAt_eq (wordAt_write hm hb (o := 40) (by decide) rfl) h5
  have e10 := wordAt_eq (wordAt_write hm hb (o := 32) (by decide) rfl) h10
  have e15 := wordAt_eq (wordAt_write hm hb (o := 168) (by decide) rfl) h15
  have e20 := (hm.regs .r10 _ rfl).symm.trans h20
  refine (hm.regs .r14 _ rfl).trans ?_
  simp only [newPar, UInt64.toBitVec_xor]
  rw [← e0, ← e5, ← e10, ← e15, ← e20]
  clear hm
  simp only [eval_xor]
  ac_rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_parity_r9 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    m.regs.get64 .r9 = (newPar a c rc 1).toBitVec := by
  have h1 := second_slot_144 hx hm hb hregs hslots hpar hrc hrot
  have h6 := second_slot_8 hx hm hb hregs hslots hpar hrc hrot
  have h11 := second_slot_56 hx hm hb hregs hslots hpar hrc hrot
  have h16 := second_slot_80 hx hm hb hregs hslots hpar hrc hrot
  have h21 := second_slot_112 hx hm hb hregs hslots hpar hrc hrot
  rw [secondBody] at hx
  cases hx
  have e1 := wordAt_eq (wordAt_write hm hb (o := 144) (by decide) rfl) h1
  have e6 := wordAt_eq (wordAt_write hm hb (o := 8) (by decide) rfl) h6
  have e11 := wordAt_eq (wordAt_write hm hb (o := 56) (by decide) rfl) h11
  have e16 := wordAt_eq (wordAt_write hm hb (o := 80) (by decide) rfl) h16
  have e21 := wordAt_eq (wordAt_write hm hb (o := 112) (by decide) rfl) h21
  refine (hm.regs .r9 _ rfl).trans ?_
  simp only [newPar, UInt64.toBitVec_xor]
  rw [← e1, ← e6, ← e11, ← e16, ← e21]
  clear hm
  simp only [eval_xor]
  ac_rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_parity_r13 [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    m.regs.get64 .r13 = (newPar a c rc 2).toBitVec := by
  have h2 := second_slot_152 hx hm hb hregs hslots hpar hrc hrot
  have h7 := second_slot_16 hx hm hb hregs hslots hpar hrc hrot
  have h12 := second_reg_rsi hx hm hb hregs hslots hpar hrc hrot
  have h17 := second_slot_72 hx hm hb hregs hslots hpar hrc hrot
  have h22 := second_reg_rax hx hm hb hregs hslots hpar hrc hrot
  rw [secondBody] at hx
  cases hx
  have e2 := wordAt_eq (wordAt_write hm hb (o := 152) (by decide) rfl) h2
  have e7 := wordAt_eq (wordAt_write hm hb (o := 16) (by decide) rfl) h7
  have e12 := (hm.regs .rsi _ rfl).symm.trans h12
  have e17 := wordAt_eq (wordAt_write hm hb (o := 72) (by decide) rfl) h17
  have e22 := (hm.regs .rax _ rfl).symm.trans h22
  refine (hm.regs .r13 _ rfl).trans ?_
  simp only [newPar, UInt64.toBitVec_xor]
  rw [← e2, ← e7, ← e12, ← e17, ← e22]
  clear hm
  simp only [eval_xor]
  ac_rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_parity_rbp [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    m.regs.get64 .rbp = (newPar a c rc 3).toBitVec := by
  have h3 := second_reg_r11 hx hm hb hregs hslots hpar hrc hrot
  have h8 := second_slot_160 hx hm hb hregs hslots hpar hrc hrot
  have h13 := second_slot_64 hx hm hb hregs hslots hpar hrc hrot
  have h18 := second_reg_r8 hx hm hb hregs hslots hpar hrc hrot
  have h23 := second_slot_104 hx hm hb hregs hslots hpar hrc hrot
  rw [secondBody] at hx
  cases hx
  have e3 := (hm.regs .r11 _ rfl).symm.trans h3
  have e8 := wordAt_eq (wordAt_write hm hb (o := 160) (by decide) rfl) h8
  have e13 := wordAt_eq (wordAt_write hm hb (o := 64) (by decide) rfl) h13
  have e18 := (hm.regs .r8 _ rfl).symm.trans h18
  have e23 := wordAt_eq (wordAt_write hm hb (o := 104) (by decide) rfl) h23
  refine (hm.regs .rbp _ rfl).trans ?_
  simp only [newPar, UInt64.toBitVec_xor]
  rw [← e3, ← e8, ← e13, ← e18, ← e23]
  clear hm
  simp only [eval_xor]
  ac_rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem second_parity_rcx [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    m.regs.get64 .rcx = (newPar a c rc 4).toBitVec := by
  have h4 := second_reg_r15 hx hm hb hregs hslots hpar hrc hrot
  have h9 := second_slot_48 hx hm hb hregs hslots hpar hrc hrot
  have h14 := second_slot_24 hx hm hb hregs hslots hpar hrc hrot
  have h19 := second_slot_0 hx hm hb hregs hslots hpar hrc hrot
  have h24 := second_reg_rbx hx hm hb hregs hslots hpar hrc hrot
  rw [secondBody] at hx
  cases hx
  have e4 := (hm.regs .r15 _ rfl).symm.trans h4
  have e9 := wordAt_eq (wordAt_write hm hb (o := 48) (by decide) rfl) h9
  have e14 := wordAt_eq (wordAt_write hm hb (o := 24) (by decide) rfl) h14
  have e19 := wordAt_eq (wordAt_write hm hb (o := 0) (by decide) rfl) h19
  have e24 := (hm.regs .rbx _ rfl).symm.trans h24
  refine (hm.regs .rcx _ rfl).trans ?_
  simp only [newPar, UInt64.toBitVec_xor]
  rw [← e4, ← e9, ← e14, ← e19, ← e24]
  clear hm
  simp only [eval_xor]
  ac_rfl

theorem second_regs [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    AllOf (fun p : Reg64 × Nat => m.regs.get64 p.1 = (roundCL a c rc p.2).toBitVec) laneRegs :=
  ⟨second_reg_r11 hx hm hb hregs hslots hpar hrc hrot,
    second_reg_r15 hx hm hb hregs hslots hpar hrc hrot,
    second_reg_rsi hx hm hb hregs hslots hpar hrc hrot,
    second_reg_r8 hx hm hb hregs hslots hpar hrc hrot,
    second_reg_r10 hx hm hb hregs hslots hpar hrc hrot,
    second_reg_rax hx hm hb hregs hslots hpar hrc hrot,
    second_reg_rbx hx hm hb hregs hslots hpar hrc hrot,
    trivial⟩

theorem second_slots [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    AllOf (fun p : Nat × Nat => WordAt m.dmem (b + BitVec.ofNat 64 p.1)
      (roundCL a c rc p.2).toBitVec) laneSlots :=
  ⟨second_slot_88 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_144 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_152 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_40 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_8 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_16 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_160 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_48 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_32 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_56 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_64 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_24 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_168 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_80 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_72 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_0 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_112 hx hm hb hregs hslots hpar hrc hrot,
    second_slot_104 hx hm hb hregs hslots hpar hrc hrot,
    trivial⟩

theorem second_par [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec secondHalf startMid = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 296)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) midLaneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) midLaneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) midParRegs)
    (hrc : env.load 1 8 8 = rc.toBitVec)
    (hrot : env.regs .rbx = (c 3).toBitVec.rotateLeft 1) :
    AllOf (fun p : Reg64 × Nat => m.regs.get64 p.1 = (newPar a c rc p.2).toBitVec) parRegs :=
  ⟨second_parity_r14 hx hm hb hregs hslots hpar hrc hrot,
    second_parity_r9 hx hm hb hregs hslots hpar hrc hrot,
    second_parity_r13 hx hm hb hregs hslots hpar hrc hrot,
    second_parity_rbp hx hm hb hregs hslots hpar hrc hrot,
    second_parity_rcx hx hm hb hregs hslots hpar hrc hrot,
    trivial⟩



end

end NativeRustcX64.KeccakF
