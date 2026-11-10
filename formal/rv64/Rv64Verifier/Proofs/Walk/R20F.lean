import Rv64Verifier.Proofs.Walk.R20E

/-!
# `walk` R20, the outputs' claim: to R21's entry

`AtR21m`: at `0x80003ff8`, `ring_switch`'s call ahead, the claims `cl` (the outputs' included) in
the `Vec` at `S - 1632` (buffer also in `s2`, count in `s9`), the inputs' point `Vec` at
`S - 1728` and slices `Vec` at `S - 904` (pointer and length in `a2`, `a3`). `r20none`: the outputs
are `None` (`0x80003ff4`). `r20some`: room for the outputs' claim (`0x80003f5c`), after
`grow_one` (`0x80003f68`, `0x80003f7c`) if the `Vec` is full: `AtStore`, at `0x80003f84`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus Rv64Verifier.Gkr Rv64Verifier.Model.Gkr Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x80003ff8`: `ring_switch` on the openings' inputs, then `afterRing`. -/
structure AtR21m (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t u : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (P C : Word) (M : Nat)
    (cl : List ColumnClaim) (o : KeccakOpenings) (ks ke : Nat) : Prop where
  core : CoreT OI s u₀ w t u layout lir evs P C M cl
    (Pcs.ringSwitchRust o.inputs.1 o.inputs.2 >>= afterRing layout rows lir bus cl ks ke)
  pc : u.pc = 0x80003ff8
  x12 : u.getReg .x12 = vecPtr u (s.getReg .x2 - 904)
  x13 : u.getReg .x13 = vecLen u (s.getReg .x2 - 904)
  x18 : u.getReg .x18 = P
  x22 : u.getReg .x22 = lir
  x23 : u.getReg .x23 = s.getReg .x10
  x24 : u.getReg .x24 = s.getReg .x2 - 512
  x25 : u.getReg .x25 = BitVec.ofNat 64 M
  in1 : NewVecE t u (s.getReg .x2 - 1728) o.inputs.1
  in2 : NewVecE t u (s.getReg .x2 - 904) o.inputs.2

/-- A `Vec<E>` allocated from `c` on, ending by `N`. -/
@[rv_addr] def VecBy (y c : MachineState) (a : Word) (N : Nat) : Prop :=
  (vecLen y a).toNat = 0 ∨ heapNext c ≤ (vecPtr y a).toNat ∧
    (vecPtr y a).toNat + 24 * (vecLen y a).toNat ≤ N

/-- At `0x80003f84`, room for the outputs' claim `(p, wd)`; what `verify_keccak` allocated ends by
`N`, below the claims' buffer unless it was there before. -/
structure AtStore (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t c y : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (P C L : Word)
    (cl : List ColumnClaim) (o : KeccakOpenings) (ks ke : Nat) (p : List E) (wd : E) (N : Nat) :
    Prop where
  core : CoreT OI s u₀ w t y layout lir evs P C L.toNat cl
    (afterKeccak layout rows lir bus cl (o, ks, ke))
  pc : y.pc = 0x80003f84
  room : L.toNat < C.toNat
  some : o.outputs = some (p, wd)
  x12 : y.getReg .x12 = vecPtr y (s.getReg .x2 - 904)
  x13 : y.getReg .x13 = vecLen y (s.getReg .x2 - 904)
  x19 : y.getReg .x19 = y.getMem (s.getReg .x2 - 880)
  x20 : y.getReg .x20 = s.getReg .x2 - 1752
  x22 : y.getReg .x22 = lir
  x23 : y.getReg .x23 = s.getReg .x10
  x24 : y.getReg .x24 = s.getReg .x2 - 512
  x25 : y.getReg .x25 = L
  x26 : y.getReg .x26 + 1 = L
  before : heapNext t ≤ heapNext c
  bufN : P.toNat + 56 * C.toNat ≤ heapNext c ∨ N ≤ P.toNat
  heapN : N ≤ heapNext y
  in1 : NewVecE c y (s.getReg .x2 - 1728) o.inputs.1
  in2 : NewVecE c y (s.getReg .x2 - 904) o.inputs.2
  outv : NewVecE c y (s.getReg .x2 - 880) p
  outw : eAt y (s.getReg .x2 - 856) = wd
  in1N : VecBy y c (s.getReg .x2 - 1728) N
  in2N : VecBy y c (s.getReg .x2 - 904) N
  outN : VecBy y c (s.getReg .x2 - 880) N
  copy : y.getMem (s.getReg .x2 - 1768) = y.getMem (s.getReg .x2 - 872) ∧
    y.getMem (s.getReg .x2 - 1760) = y.getMem (s.getReg .x2 - 864) ∧
    y.getMem (s.getReg .x2 - 1752) = y.getMem (s.getReg .x2 - 856) ∧
    y.getMem (s.getReg .x2 - 1744) = y.getMem (s.getReg .x2 - 848) ∧
    y.getMem (s.getReg .x2 - 1736) = y.getMem (s.getReg .x2 - 840)

theorem vecBy_of {c y : MachineState} {a : Word} {xs : List E} (h : NewVecE c y a xs) :
    VecBy y c a (heapNext y) := by
  obtain ⟨-, -, f⟩ := newVecE_facts h
  exact f

section Out
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t c x : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word} {cl : List ColumnClaim}
  {o : KeccakOpenings} {ks ke : Nat}

set_option maxRecDepth 8192 in
/-- No outputs: on to `ring_switch`'s call. -/
theorem r20none (hpre : WalkPre s)
    (A : AtOut OI s u₀ w t c x layout rows lir bus evs P C L cl o ks ke)
    (hn : o.outputs = none) :
    ∃ y, Reaches Image.code x y ∧ AtR21m OI s u₀ w t y layout rows lir bus evs P C L.toNat cl o ks ke := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp := A.core.rest.inv.sp
  have hpc : x.pc = 0x80003ff4 := by
    rcases A.pcs with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd hn h
  obtain ⟨y, hr, h₁⟩ := Sym.BlockSpec.reaches b80003ff4_spec hpc (by
    rv_eval [sp]; valid_access hval [hb1])
  have m := b80003ff4_mem_same h₁
  have k := b80003ff4_keeps h₁
  have hm : heapNext t ≤ heapNext c := A.before.1
  refine ⟨y, hr, {
    core := (A.core.same hpre m (k .x2 (by decide))).congr rfl (by
      simp only [afterKeccak, hn, Option.toList, List.map_nil, List.append_nil])
    pc := b80003ff4_pc h₁
    x12 := by rw [k .x12 (by decide), A.x12]; simp only [vecPtr, m]
    x13 := by rw [k .x13 (by decide), A.x13]; simp only [vecLen, m]
    x18 := by
      rw [b80003ff4_x18 h₁, sp, show s.getReg .x2 - 2656 + 1032 = s.getReg .x2 - 1624 by bv_omega]
      exact A.core.ptrSlot
    x22 := by rw [k .x22 (by decide), A.x22]
    x23 := by rw [k .x23 (by decide), A.x23]
    x24 := by rw [k .x24 (by decide), A.x24]
    x25 := by rw [k .x25 (by decide), A.x25]; apply BitVec.eq_of_toNat_eq; simp
    in1 := NewVecE.keep (NewVecE.widen' A.in1 hm) m
    in2 := NewVecE.keep (NewVecE.widen' A.in2 hm) m }⟩

end Out

end Rv64Verifier.Proofs.Walk
