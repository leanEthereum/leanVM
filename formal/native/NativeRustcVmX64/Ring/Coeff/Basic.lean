module

public import NativeRustcVmX64.Ring.Coeff.Exec
public import NativeRustcVmX64.Spec.Ring
public import NativeRustcVm.Ring.Math
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `ring_coefficients`: the model's state and the templates' values (x86-64)

From the entry state `m0` (`f` RDI, `g` RSI, `out` RDX): the loop's model state after `p` turns
(`rc`), `G`'s elements (`gG`), `f_p` (`fE`), the row's products (`prods`); the values of the head
template's variables at turn `p` (`hv`), and after block `j` of the turn (`bv`), each an update of
the previous (`upd`).
-/

namespace NativeRustcVmX64.Ring.Coeff

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring

@[expose] public section

abbrev fA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
abbrev gA (m0 : MachineData) : BitVec 64 := reg m0 .rsi
abbrev oA (m0 : MachineData) : BitVec 64 := reg m0 .rdx

def fl (m0 : MachineData) : List EW := NativeRustcVm.ewsOf m0.dmem (fA m0) 8
def gl (m0 : MachineData) : List EW := NativeRustcVm.ewsOf m0.dmem (gA m0) 8

/-- `f_p`. -/
def fE (m0 : MachineData) (p : Nat) : EW :=
  NativeRustcVm.ewOf m0.dmem (fA m0 + BitVec.ofNat 64 (16 * p))

/-- The loop's state after `p` turns. -/
def rc (m0 : MachineData) (p : Nat) : Array EW × Array EW := rcAt (fl m0) (gl m0).toArray p

/-- `G`'s element `b` after `p` turns. -/
def gG (m0 : MachineData) (p b : Nat) : EW := (rc m0 p).2.getD b 0

/-- Turn `p`'s first `b` products. -/
def prods (m0 : MachineData) (p b : Nat) : List EW :=
  (List.range b).map fun i ↦ fE m0 p * gG m0 p i

abbrev c0 (x : EW) : BitVec 64 := x.c0.toBitVec
abbrev c1 (x : EW) : BitVec 64 := x.c1.toBitVec

/-- Values updated at the listed variables. -/
def upd (f : Nat → BitVec 64) (l : List (Nat × BitVec 64)) : Nat → BitVec 64 :=
  fun i ↦ (l.lookup i).getD (f i)

/-- The head's values at turn `p`, `g` the elements of `G`. -/
def hvG (m0 : MachineData) (p : Nat) (g : Nat → EW) : Nat → BitVec 64 :=
  upd (fun _ ↦ 0)
    [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
      (5, reg m0 .rbx), (6, c0 (g 7)), (7, c1 (g 7)), (8, BitVec.ofNat 64 (16 * p)),
      (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)), (15, c1 (g 5)),
      (16, c1 (g 0)), (17, c0 (g 0)), (18, c0 (g 1)), (19, c1 (g 1)), (20, c0 (g 2)),
      (21, c1 (g 2)), (22, c0 (g 3)), (23, c1 (g 3)), (24, c0 (g 4)), (25, c1 (g 4)), (28, fA m0)]

/-- The head's values at turn `p`. -/
abbrev hv (m0 : MachineData) (p : Nat) : Nat → BitVec 64 := hvG m0 p (gG m0 p)

/-- `frobenius8 · 1`. -/
abbrev fr1 (x : EW) : EW := frobenius8 x 1

/-- The values after block `j` of turn `p`, `F` being `f_p`, `g` the elements of `G`, `G'` their
Frobenius images (each level listed in full, the images abstract: the kernel then reads a value
without going through the previous levels or unfolding a Frobenius image). -/
def bvG (m0 : MachineData) (p : Nat) (F : EW) (g G' : Nat → EW) : Nat → Nat → BitVec 64
  | 0 => hvG m0 p g
  | 1 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (F * g 0)), (7, c1 (F * g 0)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (g 0)), (17, c0 (g 0)), (18, c0 (g 1)), (19, c1 (g 1)),
        (20, c0 (g 2)), (21, c1 (g 2)), (22, c0 (g 3)), (23, c1 (g 3)), (24, c0 (g 4)),
        (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0)]
  | 2 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (F * g 1)), (7, c1 (F * g 1)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (g 0)), (17, c0 (g 0)), (18, c0 (g 1)), (19, c1 (g 1)),
        (20, c0 (g 2)), (21, c1 (g 2)), (22, c0 (g 3)), (23, c1 (g 3)), (24, c0 (g 4)),
        (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0), (29, c0 (F * g 0)),
        (30, c1 (F * g 0))]
  | 3 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (F * g 2)), (7, c1 (F * g 2)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (g 0)), (17, c0 (g 0)), (18, c0 (g 1)), (19, c1 (g 1)),
        (20, c0 (g 2)), (21, c1 (g 2)), (22, c0 (g 3)), (23, c1 (g 3)), (24, c0 (g 4)),
        (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0), (29, c0 (F * g 0)),
        (30, c1 (F * g 0)), (31, c0 (F * g 1)), (32, c1 (F * g 1))]
  | 4 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (F * g 3)), (7, c1 (F * g 3)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (g 0)), (17, c0 (g 0)), (18, c0 (g 1)), (19, c1 (g 1)),
        (20, c0 (g 2)), (21, c1 (g 2)), (22, c0 (g 3)), (23, c1 (g 3)), (24, c0 (g 4)),
        (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0), (29, c0 (F * g 0)),
        (30, c1 (F * g 0)), (31, c0 (F * g 1)), (32, c1 (F * g 1)), (33, c0 (F * g 2)),
        (34, c1 (F * g 2))]
  | 5 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (F * g 4)), (7, c1 (F * g 4)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (g 0)), (17, c0 (g 0)), (18, c0 (g 1)), (19, c1 (g 1)),
        (20, c0 (g 2)), (21, c1 (g 2)), (22, c0 (g 3)), (23, c1 (g 3)), (24, c0 (g 4)),
        (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0), (29, c0 (F * g 0)),
        (30, c1 (F * g 0)), (31, c0 (F * g 1)), (32, c1 (F * g 1)), (33, c0 (F * g 2)),
        (34, c1 (F * g 2)), (35, c0 (F * g 3)), (36, c1 (F * g 3))]
  | 6 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (F * g 5)), (7, c1 (F * g 5)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (g 0)), (17, c0 (g 0)), (18, c0 (g 1)), (19, c1 (g 1)),
        (20, c0 (g 2)), (21, c1 (g 2)), (22, c0 (g 3)), (23, c1 (g 3)), (24, c0 (g 4)),
        (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0), (29, c0 (F * g 0)),
        (30, c1 (F * g 0)), (31, c0 (F * g 1)), (32, c1 (F * g 1)), (33, c0 (F * g 2)),
        (34, c1 (F * g 2)), (35, c0 (F * g 3)), (36, c1 (F * g 3)), (37, c0 (F * g 4)),
        (38, c1 (F * g 4))]
  | 7 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (F * g 6)), (7, c1 (F * g 6)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (g 0)), (17, c0 (g 0)), (18, c0 (g 1)), (19, c1 (g 1)),
        (20, c0 (g 2)), (21, c1 (g 2)), (22, c0 (g 3)), (23, c1 (g 3)), (24, c0 (g 4)),
        (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0), (29, c0 (F * g 0)),
        (30, c1 (F * g 0)), (31, c0 (F * g 1)), (32, c1 (F * g 1)), (33, c0 (F * g 2)),
        (34, c1 (F * g 2)), (35, c0 (F * g 3)), (36, c1 (F * g 3)), (37, c0 (F * g 4)),
        (38, c1 (F * g 4)), (39, c0 (F * g 5)), (40, c1 (F * g 5))]
  | 8 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (F * g 7)), (7, c1 (F * g 7)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (g 0)), (17, c0 (g 0)), (18, c0 (g 1)), (19, c1 (g 1)),
        (20, c0 (g 2)), (21, c1 (g 2)), (22, c0 (g 3)), (23, c1 (g 3)), (24, c0 (g 4)),
        (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0), (29, c0 (F * g 0)),
        (30, c1 (F * g 0)), (31, c0 (F * g 1)), (32, c1 (F * g 1)), (33, c0 (F * g 2)),
        (34, c1 (F * g 2)), (35, c0 (F * g 3)), (36, c1 (F * g 3)), (37, c0 (F * g 4)),
        (38, c1 (F * g 4)), (39, c0 (F * g 5)), (40, c1 (F * g 5)), (41, c0 (F * g 6)),
        (42, c1 (F * g 6))]
  | 9 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (G' 0)), (7, c1 (G' 0)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (g 0)), (17, c0 (g 0)), (18, c0 (g 1)), (19, c1 (g 1)),
        (20, c0 (g 2)), (21, c1 (g 2)), (22, c0 (g 3)), (23, c1 (g 3)), (24, c0 (g 4)),
        (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0), (29, c0 (F * g 0)),
        (30, c1 (F * g 0)), (31, c0 (F * g 1)), (32, c1 (F * g 1)), (33, c0 (F * g 2)),
        (34, c1 (F * g 2)), (35, c0 (F * g 3)), (36, c1 (F * g 3)), (37, c0 (F * g 4)),
        (38, c1 (F * g 4)), (39, c0 (F * g 5)), (40, c1 (F * g 5)), (41, c0 (F * g 6)),
        (42, c1 (F * g 6)), (43, c0 (F * g 7)), (44, c1 (F * g 7))]
  | 10 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (G' 1)), (7, c1 (G' 1)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (G' 0)), (17, c0 (G' 0)), (18, c0 (g 1)), (19, c1 (g 1)),
        (20, c0 (g 2)), (21, c1 (g 2)), (22, c0 (g 3)), (23, c1 (g 3)), (24, c0 (g 4)),
        (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0), (29, c0 (F * g 0)),
        (30, c1 (F * g 0)), (31, c0 (F * g 1)), (32, c1 (F * g 1)), (33, c0 (F * g 2)),
        (34, c1 (F * g 2)), (35, c0 (F * g 3)), (36, c1 (F * g 3)), (37, c0 (F * g 4)),
        (38, c1 (F * g 4)), (39, c0 (F * g 5)), (40, c1 (F * g 5)), (41, c0 (F * g 6)),
        (42, c1 (F * g 6)), (43, c0 (F * g 7)), (44, c1 (F * g 7))]
  | 11 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (G' 2)), (7, c1 (G' 2)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (G' 0)), (17, c0 (G' 0)), (18, c0 (G' 1)),
        (19, c1 (G' 1)), (20, c0 (g 2)), (21, c1 (g 2)), (22, c0 (g 3)), (23, c1 (g 3)),
        (24, c0 (g 4)), (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0),
        (29, c0 (F * g 0)), (30, c1 (F * g 0)), (31, c0 (F * g 1)), (32, c1 (F * g 1)),
        (33, c0 (F * g 2)), (34, c1 (F * g 2)), (35, c0 (F * g 3)), (36, c1 (F * g 3)),
        (37, c0 (F * g 4)), (38, c1 (F * g 4)), (39, c0 (F * g 5)), (40, c1 (F * g 5)),
        (41, c0 (F * g 6)), (42, c1 (F * g 6)), (43, c0 (F * g 7)), (44, c1 (F * g 7))]
  | 12 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (G' 3)), (7, c1 (G' 3)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (G' 0)), (17, c0 (G' 0)), (18, c0 (G' 1)),
        (19, c1 (G' 1)), (20, c0 (G' 2)), (21, c1 (G' 2)), (22, c0 (g 3)),
        (23, c1 (g 3)), (24, c0 (g 4)), (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)),
        (28, fA m0), (29, c0 (F * g 0)), (30, c1 (F * g 0)), (31, c0 (F * g 1)),
        (32, c1 (F * g 1)), (33, c0 (F * g 2)), (34, c1 (F * g 2)), (35, c0 (F * g 3)),
        (36, c1 (F * g 3)), (37, c0 (F * g 4)), (38, c1 (F * g 4)), (39, c0 (F * g 5)),
        (40, c1 (F * g 5)), (41, c0 (F * g 6)), (42, c1 (F * g 6)), (43, c0 (F * g 7)),
        (44, c1 (F * g 7))]
  | 13 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (G' 4)), (7, c1 (G' 4)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (G' 0)), (17, c0 (G' 0)), (18, c0 (G' 1)),
        (19, c1 (G' 1)), (20, c0 (G' 2)), (21, c1 (G' 2)), (22, c0 (G' 3)),
        (23, c1 (G' 3)), (24, c0 (g 4)), (25, c1 (g 4)), (26, c1 (g 7)), (27, c0 (g 7)),
        (28, fA m0), (29, c0 (F * g 0)), (30, c1 (F * g 0)), (31, c0 (F * g 1)),
        (32, c1 (F * g 1)), (33, c0 (F * g 2)), (34, c1 (F * g 2)), (35, c0 (F * g 3)),
        (36, c1 (F * g 3)), (37, c0 (F * g 4)), (38, c1 (F * g 4)), (39, c0 (F * g 5)),
        (40, c1 (F * g 5)), (41, c0 (F * g 6)), (42, c1 (F * g 6)), (43, c0 (F * g 7)),
        (44, c1 (F * g 7))]
  | 14 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (G' 5)), (7, c1 (G' 5)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (g 5)),
        (15, c1 (g 5)), (16, c1 (G' 0)), (17, c0 (G' 0)), (18, c0 (G' 1)),
        (19, c1 (G' 1)), (20, c0 (G' 2)), (21, c1 (G' 2)), (22, c0 (G' 3)),
        (23, c1 (G' 3)), (24, c0 (G' 4)), (25, c1 (G' 4)), (26, c1 (g 7)),
        (27, c0 (g 7)), (28, fA m0), (29, c0 (F * g 0)), (30, c1 (F * g 0)), (31, c0 (F * g 1)),
        (32, c1 (F * g 1)), (33, c0 (F * g 2)), (34, c1 (F * g 2)), (35, c0 (F * g 3)),
        (36, c1 (F * g 3)), (37, c0 (F * g 4)), (38, c1 (F * g 4)), (39, c0 (F * g 5)),
        (40, c1 (F * g 5)), (41, c0 (F * g 6)), (42, c1 (F * g 6)), (43, c0 (F * g 7)),
        (44, c1 (F * g 7))]
  | 15 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (G' 6)), (7, c1 (G' 6)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (g 6)), (12, c0 (g 6)), (13, oA m0), (14, c0 (G' 5)),
        (15, c1 (G' 5)), (16, c1 (G' 0)), (17, c0 (G' 0)), (18, c0 (G' 1)),
        (19, c1 (G' 1)), (20, c0 (G' 2)), (21, c1 (G' 2)), (22, c0 (G' 3)),
        (23, c1 (G' 3)), (24, c0 (G' 4)), (25, c1 (G' 4)), (26, c1 (g 7)),
        (27, c0 (g 7)), (28, fA m0), (29, c0 (F * g 0)), (30, c1 (F * g 0)), (31, c0 (F * g 1)),
        (32, c1 (F * g 1)), (33, c0 (F * g 2)), (34, c1 (F * g 2)), (35, c0 (F * g 3)),
        (36, c1 (F * g 3)), (37, c0 (F * g 4)), (38, c1 (F * g 4)), (39, c0 (F * g 5)),
        (40, c1 (F * g 5)), (41, c0 (F * g 6)), (42, c1 (F * g 6)), (43, c0 (F * g 7)),
        (44, c1 (F * g 7))]
  | 16 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (G' 7)), (7, c1 (G' 7)), (8, BitVec.ofNat 64 (16 * p)),
        (9, c0 F), (10, c1 F), (11, c1 (G' 6)), (12, c0 (G' 6)), (13, oA m0),
        (14, c0 (G' 5)), (15, c1 (G' 5)), (16, c1 (G' 0)), (17, c0 (G' 0)),
        (18, c0 (G' 1)), (19, c1 (G' 1)), (20, c0 (G' 2)), (21, c1 (G' 2)),
        (22, c0 (G' 3)), (23, c1 (G' 3)), (24, c0 (G' 4)), (25, c1 (G' 4)),
        (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0), (29, c0 (F * g 0)), (30, c1 (F * g 0)),
        (31, c0 (F * g 1)), (32, c1 (F * g 1)), (33, c0 (F * g 2)), (34, c1 (F * g 2)),
        (35, c0 (F * g 3)), (36, c1 (F * g 3)), (37, c0 (F * g 4)), (38, c1 (F * g 4)),
        (39, c0 (F * g 5)), (40, c1 (F * g 5)), (41, c0 (F * g 6)), (42, c1 (F * g 6)),
        (43, c0 (F * g 7)), (44, c1 (F * g 7))]
  | 17 => upd (fun _ ↦ 0)
      [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13), (4, reg m0 .r12),
        (5, reg m0 .rbx), (6, c0 (G' 7)), (7, c1 (G' 7)),
        (8, BitVec.ofNat 64 (16 * (p + 1))), (9, c0 F), (10, c1 F), (11, c1 (G' 6)),
        (12, c0 (G' 6)), (13, oA m0), (14, c0 (G' 5)), (15, c1 (G' 5)),
        (16, c1 (G' 0)), (17, c0 (G' 0)), (18, c0 (G' 1)), (19, c1 (G' 1)),
        (20, c0 (G' 2)), (21, c1 (G' 2)), (22, c0 (G' 3)), (23, c1 (G' 3)),
        (24, c0 (G' 4)), (25, c1 (G' 4)), (26, c1 (g 7)), (27, c0 (g 7)), (28, fA m0),
        (29, c0 (F * g 0)), (30, c1 (F * g 0)), (31, c0 (F * g 1)), (32, c1 (F * g 1)),
        (33, c0 (F * g 2)), (34, c1 (F * g 2)), (35, c0 (F * g 3)), (36, c1 (F * g 3)),
        (37, c0 (F * g 4)), (38, c1 (F * g 4)), (39, c0 (F * g 5)), (40, c1 (F * g 5)),
        (41, c0 (F * g 6)), (42, c1 (F * g 6)), (43, c0 (F * g 7)), (44, c1 (F * g 7))]
  | _ => fun _ ↦ 0

/-- The arrays of turn `p`: the row of `out` it writes, `f_p`. -/
abbrev rsP (m0 : MachineData) (p : Nat) : List (BitVec 64 × Nat) :=
  [(oA m0 + BitVec.ofNat 64 (128 * p), 128), (fA m0 + BitVec.ofNat 64 (16 * p), 16)]

/-- Only the row is written. -/
abbrev wrRow : Nat → Bool := fun i ↦ i == 1

/-- The entry's registers over a state's memory: the frame's owner in turn `p`'s layout. -/
abbrev own (m0 m : MachineData) : MachineData := { m with regs := m0.regs }

end

public section

variable {m0 : MachineData}

theorem fl_length : (fl m0).length = 8 := NativeRustcVm.length_ewsOf ..

theorem gl_size : (gl m0).toArray.size = 8 := by simp [gl]

theorem fl_getElem {p : Nat} (hp : p < (fl m0).length) : (fl m0)[p] = fE m0 p :=
  NativeRustcVm.getElem_ewsOf ..

theorem rc_succ {p : Nat} (hp : p < 8) : rc m0 (p + 1) = coeffStep (rc m0 p) (fE m0 p) := by
  unfold rc
  rw [rcAt_succ _ _ (by rw [fl_length]; exact hp), fl_getElem]

theorem rc_size2 {p : Nat} (hp : p ≤ 8) : (rc m0 p).2.size = 8 := by
  unfold rc
  rw [rcAt_size2 _ _ _ (by rw [fl_length]; exact hp), gl_size]

theorem rc_size1 {p : Nat} (hp : p ≤ 8) : (rc m0 p).1.size = 8 * p := by
  unfold rc
  rw [rcAt_size1 _ _ _ (by rw [fl_length]; exact hp), gl_size]

theorem rc_succ_fst {p : Nat} (hp : p < 8) :
    (rc m0 (p + 1)).1.toList = (rc m0 p).1.toList ++ prods m0 p 8 := by
  rw [rc_succ hp]
  simp only [coeffStep, Array.toList_append, Array.toList_map]
  congr 1
  apply List.ext_getElem (by simp [prods, rc_size2 (m0 := m0) (p := p) (by omega)])
  intro i h1 h2
  simp only [List.getElem_map, prods, List.getElem_range, gG, Array.getElem_toList]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem
    (by rw [rc_size2 (by omega)]; simpa [prods] using h2)]
  rfl

theorem gG_succ {p b : Nat} (hp : p < 8) (hb : b < 8) :
    gG m0 (p + 1) b = frobenius8 (gG m0 p b) 1 := by
  unfold gG
  rw [rc_succ hp]
  simp only [coeffStep]
  have hs := rc_size2 (m0 := m0) (p := p) (by omega)
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem (by rw [hs]; exact hb)]
  rfl

theorem gG_zero {b : Nat} (hb : b < 8) :
    gG m0 0 b = NativeRustcVm.ewOf m0.dmem (gA m0 + BitVec.ofNat 64 (16 * b)) := by
  unfold gG rc
  rw [rcAt_zero]
  simp only
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, gl,
    List.getElem?_eq_getElem (by rw [NativeRustcVm.length_ewsOf]; exact hb),
    NativeRustcVm.getElem_ewsOf]
  rfl

theorem rc_final : (rc m0 8).1 = ringCoefficients (arr m0 (fA m0) ringWidth)
    (arr m0 (gA m0) ringWidth) := by
  unfold rc arr
  rw [← fl_length (m0 := m0), rcAt_length]
  rfl

theorem rc_zero_fst : (rc m0 0).1.toList = [] := rfl

end

end NativeRustcVmX64.Ring.Coeff
