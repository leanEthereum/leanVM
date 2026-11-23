module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Tpl
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Areas
public import NativeRustcVmX64.Ring.Stack

/-!
# `verify_keccak`: its layout, its values, its goal (x86-64)

The regions the function writes (`rsOf`: the `TState`, the scratch, the column claims, the
`KeccakOutW`), the layout `LayZ` of its precondition (`lay_of`), the footprint as numbers (`Ctx`),
the values its templates name (`vv`), the state before a block (`At`) and the contract's goal
(`Goal`). Bytes apart from the stack and the written regions stay the entry's (`same_ro`), the
stack arguments too (`argLoad`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVm (Region)

@[expose] public section

/-- The regions `verify_keccak` writes: regions `1` to `4`. -/
def rsOf (m0 : MachineData) : List (BitVec 64 × Nat) :=
  [(reg m0 .rdi, 760), (reg m0 .r9, 205824), (keccakClaims m0, 97288), (keccakOutArg m0, 1608)]

/-- Every array is written. -/
def wrAll (_ : Nat) : Bool := true

/-- `logSteps - 4`, saturating (`b0`'s RBX). -/
def packS : Sym := .ite (.cmp .ult .W64 (.reg .rsi) (.lit 4)) (.lit 0) (.bin .sub .W64 (.reg .rsi) (.lit 4))
/-- `|inst| - 4`, saturating (`b0`'s R12). -/
def hiS : Sym := .ite (.cmp .ult .W64 (.reg .rcx) (.lit 4)) (.lit 0) (.bin .sub .W64 (.reg .rcx) (.lit 4))
/-- `min |inst| 4` (`b0`'s spill at `144`). -/
def min4S : Sym := .ite (.cmp .ult .W64 (.reg .rcx) (.lit 4)) (.reg .rcx) (.lit 4)
/-- `inst`'s coordinates past the fourth, or a dangling address (`b0`'s spill at `136`). -/
def rHighS : Sym :=
  .ite (.not (.cmp .ult .W64 (.reg .rcx) (.lit 4))) (.bin .add .W64 (.reg .rdx) (.lit 64)) (.lit 8)

/-- The values the code computes from the transcript's and the callees' results. -/
structure Vs where
  c0 : BitVec 64 := 0
  c1 : BitVec 64 := 0
  fl : BitVec 64 := 0
  o0 : BitVec 64 := 0
  o1 : BitVec 64 := 0
  w0 : BitVec 64 := 0
  w1 : BitVec 64 := 0
  pl : BitVec 64 := 0
  pp : BitVec 64 := 0
  f0 : BitVec 64 := 0
  f1 : BitVec 64 := 0
  e0 : BitVec 64 := 0
  e1 : BitVec 64 := 0
  d0 : BitVec 64 := 0
  d1 : BitVec 64 := 0
  fin : BitVec 64 := 0

/-- **The templates' variables** (`Tpl`'s list). -/
def vv [Labels] (m0 : MachineData) (V : Vs) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => reg m0 .rbp
  | 1 => reg m0 .r15
  | 2 => reg m0 .r14
  | 3 => reg m0 .r13
  | 4 => reg m0 .r12
  | 5 => reg m0 .rbx
  | 6 => reg m0 .rdi
  | 7 => reg m0 .rsi
  | 8 => reg m0 .rdx
  | 9 => reg m0 .rcx
  | 10 => reg m0 .r8
  | 11 => reg m0 .r9
  | 12 => packS.eval (Env.ofMachine m0 [])
  | 13 => hiS.eval (Env.ofMachine m0 [])
  | 14 => min4S.eval (Env.ofMachine m0 [])
  | 15 => rHighS.eval (Env.ofMachine m0 [])
  | 16 => V.c0
  | 17 => V.c1
  | 18 => V.fl
  | 19 => BinOp.apply .add .W64 (reg m0 .r9) (BitVec.ofNat 64 25600)
  | 20 => BinOp.apply .add .W64 (reg m0 .r9) (BitVec.ofNat 64 140288)
  | 21 => V.o0
  | 22 => V.o1
  | 23 => V.w0
  | 24 => V.w1
  | 25 => V.pl
  | 26 => V.pp
  | 27 => V.f0
  | 28 => V.f1
  | 29 => BinOp.apply .add .W64 (keccakOutArg m0) (BitVec.ofNat 64 584)
  | 30 => V.e0
  | 31 => V.e1
  | 32 => 3#64
  | 33 => V.d0
  | 34 => V.d1
  | 35 => V.fin
  | _ => 0

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 3344

/-- The contract's goal from the entry `m0`. -/
def Goal [Labels] (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (inst output : Array EW)
    (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ VerifyKeccakPost a s cs inst output m0 st.data

/-- **Before the block at `off`**: the template `T` with the values `vals`. -/
def At [Host] (m0 : MachineData) (k off : Nat) (wr : Nat → Bool) (T : SState)
    (vals : Nat → BitVec 64) (st : MachineState) : Prop :=
  st.pc = Host.addrOf (k + off) ∧
    BndZ m0 3344 3368 verifyKeccakStack (rsOf m0) wr T vals st.data

/-- Before the column claims are pushed: the `TState` and the scratch written. -/
def wrA (i : Nat) : Bool := i == 1 || i == 2

/-- Before the output point is written: the claims too. -/
def wrB (i : Nat) : Bool := i == 1 || i == 2 || i == 3

/-- **The footprint as numbers**: `t`, `s`, `c`, `o` the written regions (the `TState`, the
scratch, the claims, the `KeccakOutW`); `w`, `i`, `p`, `rc`, `pj`, `rh`, `ar` the read ones (the
decoded area, `inst`, the output lanes, the three tables, the stack arguments); `K` the stack's
base. -/
structure Ctx [Labels] (a : DecArea) (inst : Array EW) (m0 : MachineData) : Prop where
  sp : verifyKeccakStack ≤ (rspOf m0).toNat
  top : (rspOf m0).toNat + 24 ≤ 2 ^ 64
  K : (stackBelow m0 verifyKeccakStack).toNat = (rspOf m0).toNat - verifyKeccakStack
  ar : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8
  tW : (reg m0 .rdi).toNat + 760 ≤ 2 ^ 64
  sW : (reg m0 .r9).toNat + 205824 ≤ 2 ^ 64
  cW : (keccakClaims m0).toNat + 97288 ≤ 2 ^ 64
  oW : (keccakOutArg m0).toNat + 1608 ≤ 2 ^ 64
  wW : a.words.toNat + 8 * a.len ≤ 2 ^ 64
  iW : (reg m0 .rdx).toNat + 16 * inst.size ≤ 2 ^ 64
  pW : (reg m0 .r8).toNat + 400 ≤ 2 ^ 64
  rcW : rcAddr.toNat + 192 ≤ 2 ^ 64
  pjW : projectAddr.toNat + 128 ≤ 2 ^ 64
  rhW : rhoAddr.toNat + 100 ≤ 2 ^ 64
  tS : Sep (reg m0 .rdi).toNat 760 (stackBelow m0 verifyKeccakStack).toNat (verifyKeccakStack + 8)
  sS : Sep (reg m0 .r9).toNat 205824 (stackBelow m0 verifyKeccakStack).toNat
    (verifyKeccakStack + 8)
  cS : Sep (keccakClaims m0).toNat 97288 (stackBelow m0 verifyKeccakStack).toNat
    (verifyKeccakStack + 8)
  oS : Sep (keccakOutArg m0).toNat 1608 (stackBelow m0 verifyKeccakStack).toNat
    (verifyKeccakStack + 8)
  wS : Sep a.words.toNat (8 * a.len) (stackBelow m0 verifyKeccakStack).toNat
    (verifyKeccakStack + 8)
  iS : Sep (reg m0 .rdx).toNat (16 * inst.size) (stackBelow m0 verifyKeccakStack).toNat
    (verifyKeccakStack + 8)
  pS : Sep (reg m0 .r8).toNat 400 (stackBelow m0 verifyKeccakStack).toNat (verifyKeccakStack + 8)
  rcS : Sep rcAddr.toNat 192 (stackBelow m0 verifyKeccakStack).toNat (verifyKeccakStack + 8)
  pjS : Sep projectAddr.toNat 128 (stackBelow m0 verifyKeccakStack).toNat (verifyKeccakStack + 8)
  rhS : Sep rhoAddr.toNat 100 (stackBelow m0 verifyKeccakStack).toNat (verifyKeccakStack + 8)
  ts : Sep (reg m0 .rdi).toNat 760 (reg m0 .r9).toNat 205824
  tc : Sep (reg m0 .rdi).toNat 760 (keccakClaims m0).toNat 97288
  tou : Sep (reg m0 .rdi).toNat 760 (keccakOutArg m0).toNat 1608
  sc : Sep (reg m0 .r9).toNat 205824 (keccakClaims m0).toNat 97288
  so : Sep (reg m0 .r9).toNat 205824 (keccakOutArg m0).toNat 1608
  co : Sep (keccakClaims m0).toNat 97288 (keccakOutArg m0).toNat 1608
  tw : Sep (reg m0 .rdi).toNat 760 a.words.toNat (8 * a.len)
  ti : Sep (reg m0 .rdi).toNat 760 (reg m0 .rdx).toNat (16 * inst.size)
  tp : Sep (reg m0 .rdi).toNat 760 (reg m0 .r8).toNat 400
  trc : Sep (reg m0 .rdi).toNat 760 rcAddr.toNat 192
  tpj : Sep (reg m0 .rdi).toNat 760 projectAddr.toNat 128
  trh : Sep (reg m0 .rdi).toNat 760 rhoAddr.toNat 100
  tar : Sep (reg m0 .rdi).toNat 760 (rspOf m0 + 8#64).toNat 16
  sw : Sep (reg m0 .r9).toNat 205824 a.words.toNat (8 * a.len)
  si : Sep (reg m0 .r9).toNat 205824 (reg m0 .rdx).toNat (16 * inst.size)
  spp : Sep (reg m0 .r9).toNat 205824 (reg m0 .r8).toNat 400
  src : Sep (reg m0 .r9).toNat 205824 rcAddr.toNat 192
  spj : Sep (reg m0 .r9).toNat 205824 projectAddr.toNat 128
  srh : Sep (reg m0 .r9).toNat 205824 rhoAddr.toNat 100
  sar : Sep (reg m0 .r9).toNat 205824 (rspOf m0 + 8#64).toNat 16
  cw : Sep (keccakClaims m0).toNat 97288 a.words.toNat (8 * a.len)
  ci : Sep (keccakClaims m0).toNat 97288 (reg m0 .rdx).toNat (16 * inst.size)
  cp : Sep (keccakClaims m0).toNat 97288 (reg m0 .r8).toNat 400
  crc : Sep (keccakClaims m0).toNat 97288 rcAddr.toNat 192
  cpj : Sep (keccakClaims m0).toNat 97288 projectAddr.toNat 128
  crh : Sep (keccakClaims m0).toNat 97288 rhoAddr.toNat 100
  car : Sep (keccakClaims m0).toNat 97288 (rspOf m0 + 8#64).toNat 16
  ow : Sep (keccakOutArg m0).toNat 1608 a.words.toNat (8 * a.len)
  oi : Sep (keccakOutArg m0).toNat 1608 (reg m0 .rdx).toNat (16 * inst.size)
  op : Sep (keccakOutArg m0).toNat 1608 (reg m0 .r8).toNat 400
  orc : Sep (keccakOutArg m0).toNat 1608 rcAddr.toNat 192
  opj : Sep (keccakOutArg m0).toNat 1608 projectAddr.toNat 128
  orh : Sep (keccakOutArg m0).toNat 1608 rhoAddr.toNat 100
  oar : Sep (keccakOutArg m0).toNat 1608 (rspOf m0 + 8#64).toNat 16
  wM : NativeRustcVm.Mapped m0.dmem a.words (8 * a.len)
  iM : NativeRustcVm.Mapped m0.dmem (reg m0 .rdx) (16 * inst.size)
  pM : NativeRustcVm.Mapped m0.dmem (reg m0 .r8) 400
  rcM : NativeRustcVm.Mapped m0.dmem rcAddr 192
  pjM : NativeRustcVm.Mapped m0.dmem projectAddr 128
  rhM : NativeRustcVm.Mapped m0.dmem rhoAddr 100
  got : GotAt m0 verifyKeccakStack
    [(reg m0 .rdi, 760), (reg m0 .r9, 205824), (keccakClaims m0, 97288),
      (keccakOutArg m0, 1608), (a.region.addr, a.region.size),
      (reg m0 .rdx, 16 * inst.size), (reg m0 .r8, 400), (rcAddr, 192),
      (projectAddr, 128), (rhoAddr, 100), (rspOf m0 + 8#64, 16)] ["memcpy"]

end

public section

theorem vk_eq : verifyKeccakStack = 6544 := by decide

/-- A region apart from the stack and from the stack arguments is apart from region `0`'s span. -/
theorem sep_stack {t n K R N : Nat} (hn : 0 < n) (hN : N = 6544) (h1 : Sep t n K (N + 8)) (h2 : Sep t n R 16)
    (hK : K + N + 8 = R) : t + n ≤ K ∨ K + (N - 3344 + 3368) ≤ t := by
  subst hN; unfold Sep at h1 h2; omega

theorem tsz : tstateBytes = 760 := rfl
theorem ssz : NativeRustcVm.KeccakGkr.scratchBytes = 205824 := rfl
theorem csz : NativeRustcVm.Layout.claimsBytes = 97288 := rfl
theorem osz : NativeRustcVm.KeccakGkr.outBytes = 1608 := rfl

variable [Labels] {m0 : MachineData} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW}

/-- **The footprint as numbers**, from the precondition. -/
theorem ctx_of (h : VerifyKeccakPre a s cs inst output m0) : Ctx a inst m0 := by
  obtain ⟨hS, hargs, -, -, -, -, -, -, -, -, -, -, -, -, hA, hgot⟩ := h
  have h3 := hS.1
  have h4 := hargs.2
  have hK : (stackBelow m0 verifyKeccakStack).toNat = (rspOf m0).toNat - verifyKeccakStack :=
    stackBelow_toNat h3
  have har : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
    rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl]
    omega
  obtain ⟨hNW, hwS, hrS, hww, hwr⟩ := Areas.nat hA
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, DecArea.region, rcRegion, projectRegion, rhoRegion, ewsRegion, argsRegion, or_assoc,
    tsz, ssz, csz, osz] at hNW hwS hrS hwr
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, tsz, ssz, csz, osz] at hww
  obtain ⟨tW, sW, cW, oW, wW, iW, pW, rcW, pjW, rhW, -⟩ := hNW
  obtain ⟨tS, sS, cS, oS⟩ := hwS
  obtain ⟨wS, iS, pS, rcS, pjS, rhS, -⟩ := hrS
  obtain ⟨⟨ts, tc, tou⟩, ⟨sc, so⟩, co, -⟩ := hww
  obtain ⟨⟨tw, ti, tp, trc, tpj, trh, tar⟩, ⟨sw, si, spp, src, spj, srh, sar⟩,
    ⟨cw, ci, cp, crc, cpj, crh, car⟩, ⟨ow, oi, op, orc, opj, orh, oar⟩⟩ := hwr
  have hm := fun r (hr : r ∈ [a.region, ewsRegion (reg m0 .rdx) inst.size, ewsRegion (reg m0 .r8) 25,
      rcRegion, projectRegion, rhoRegion, argsRegion m0 2]) ↦ Areas.mapped hA (.inr hr)
  exact ⟨h3, by omega, hK, har, tW, sW, cW, oW, wW, iW, pW, rcW, pjW, rhW, tS, sS, cS, oS, wS, iS,
    pS, rcS, pjS, rhS, ts, tc, tou, sc, so, co, tw, ti, tp, trc, tpj, trh, tar, sw, si, spp, src, spj,
    srh, sar, cw, ci, cp, crc, cpj, crh, car, ow, oi, op, orc, opj, orh, oar,
    hm _ List.mem_cons_self, hm _ (List.mem_cons_of_mem _ List.mem_cons_self),
    hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))),
    hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))),
    hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))), hgot⟩

/-- **The layout** of the precondition. -/
theorem lay_of (h : VerifyKeccakPre a s cs inst output m0) :
    LayZ m0 3344 3368 verifyKeccakStack (rsOf m0) := by
  have c := ctx_of h
  obtain ⟨hS, hargs, -, -, -, -, -, -, -, -, -, -, -, -, hA, -⟩ := h
  have hvk := vk_eq
  have h3 := hS.1
  have hb : (stackBelow m0 3344).toNat = (rspOf m0).toNat - 3344 := stackBelow_toNat (by omega)
  have hK := c.K
  have har := c.ar
  have ht := c.top
  refine ⟨hS, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hi' : i < 3352
    · have := NativeRustcVmX64.Transcript.frame_mapped hS (F := 3344) (by omega) i hi'
      exact this
    · have := hargs.1 (i - 3352) (by omega)
      rwa [BitVec.add_assoc, ← BitVec.ofNat_add,
        show 8 + (i - 3352) = i - 3344 by omega, ← NativeRustcVmX64.Field.frame_add (m0 := m0) 3344 (i - 3344),
        show 3344 + (i - 3344) = i by omega] at this
  · show _ + _ ≤ _
    omega
  · have m1 : NativeRustcVm.Mapped m0.dmem (reg m0 .rdi) 760 :=
      Areas.mapped hA (r := ⟨reg m0 .rdi, tstateBytes⟩) (.inl List.mem_cons_self)
    have m2 : NativeRustcVm.Mapped m0.dmem (reg m0 .r9) 205824 :=
      Areas.mapped hA (r := ⟨reg m0 .r9, NativeRustcVm.KeccakGkr.scratchBytes⟩)
        (.inl (List.mem_cons_of_mem _ List.mem_cons_self))
    have m3 : NativeRustcVm.Mapped m0.dmem (keccakClaims m0) 97288 :=
      Areas.mapped hA (r := ⟨keccakClaims m0, NativeRustcVm.Layout.claimsBytes⟩)
        (.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    have m4 : NativeRustcVm.Mapped m0.dmem (keccakOutArg m0) 1608 :=
      Areas.mapped hA (r := ⟨keccakOutArg m0, NativeRustcVm.KeccakGkr.outBytes⟩)
        (.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self))))
    have hKR : (stackBelow m0 verifyKeccakStack).toNat + verifyKeccakStack + 8 =
        (rspOf m0 + 8#64).toNat := by
      rw [hK, har]; omega
    refine ⟨⟨m1, c.tW, ?_⟩, ⟨m2, c.sW, ?_⟩, ⟨m3, c.cW, ?_⟩, ⟨m4, c.oW, ?_⟩, trivial⟩ <;>
      show _ ∨ _
    · exact sep_stack (Nat.zero_lt_succ _) vk_eq c.tS c.tar hKR
    · exact sep_stack (Nat.zero_lt_succ _) vk_eq c.sS c.sar hKR
    · exact sep_stack (Nat.zero_lt_succ _) vk_eq c.cS c.car hKR
    · exact sep_stack (Nat.zero_lt_succ _) vk_eq c.oS c.oar hKR
  · have h1 := c.ts; have h2 := c.tc; have h3 := c.tou; have h4 := c.sc; have h5 := c.so
    have h6 := c.co
    unfold Sep at h1 h2 h3 h4 h5 h6
    simp only [rsOf, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, Apart, false_implies, implies_true]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega

omit [Labels] in
/-- **What the function may write**, from the template's frame. -/
theorem writes_of {wr : Nat → Bool} {d : MachineData}
    (hs : SameOutside m0.dmem d.dmem
      (fun q ↦ InRange (stackBelow m0 verifyKeccakStack) verifyKeccakStack q ∨
        outsOf (rsOf m0) wr q)) :
    Writes m0 d verifyKeccakStack
      [⟨reg m0 .rdi, tstateBytes⟩, ⟨reg m0 .r9, NativeRustcVm.KeccakGkr.scratchBytes⟩,
        ⟨keccakClaims m0, NativeRustcVm.Layout.claimsBytes⟩,
        ⟨keccakOutArg m0, NativeRustcVm.KeccakGkr.outBytes⟩] := by
  intro q hq
  refine hs q fun h ↦ hq ?_
  rcases h with h | ⟨i, e, -, he, h⟩
  · exact ⟨_, List.mem_cons_self, h⟩
  · refine ⟨⟨e.1, e.2⟩, ?_, h⟩
    simp only [rsOf] at he
    rcases i with _ | _ | _ | _ | i <;> simp at he <;> subst he <;> simp [tsz, ssz, csz, osz]

/-- **Bytes apart from the stack and the written regions** stay the entry's. -/
theorem same_ro (c : Ctx a inst m0) {wr : Nat → Bool} {d : MachineData}
    (hs : SameOutside m0.dmem d.dmem
      (fun q ↦ InRange (stackBelow m0 verifyKeccakStack) verifyKeccakStack q ∨
        outsOf (rsOf m0) wr q))
    {A : BitVec 64} {n : Nat} (hA : A.toNat + n ≤ 2 ^ 64)
    (hst : Sep A.toNat n (stackBelow m0 verifyKeccakStack).toNat (verifyKeccakStack + 8))
    (ht : wr 1 = true → Sep A.toNat n (reg m0 .rdi).toNat 760)
    (hsc : wr 2 = true → Sep A.toNat n (reg m0 .r9).toNat 205824)
    (hc : wr 3 = true → Sep A.toNat n (keccakClaims m0).toNat 97288)
    (ho : wr 4 = true → Sep A.toNat n (keccakOutArg m0).toNat 1608) :
    NativeRustcVm.Layout.Same m0.dmem d.dmem A n := by
  intro j hj
  have hq : (A + BitVec.ofNat 64 j).toNat = A.toNat + j := toNat_add_ofNat _ _ (by omega)
  refine hs _ fun h ↦ ?_
  have hK := c.K
  have := c.sp
  rcases h with h | ⟨i, e, hw, he, h⟩
  · rw [NativeRustcX64.Sym.inRange_iff (by omega), hq] at h
    unfold Sep at hst
    omega
  · simp only [rsOf] at he
    rcases i with _ | _ | _ | _ | i <;> simp at he <;> subst he <;> simp only at h
    · have := ht hw; rw [NativeRustcX64.Sym.inRange_iff c.tW, hq] at h; unfold Sep at this; omega
    · have := hsc hw; rw [NativeRustcX64.Sym.inRange_iff c.sW, hq] at h; unfold Sep at this; omega
    · have := hc hw; rw [NativeRustcX64.Sym.inRange_iff c.cW, hq] at h; unfold Sep at this; omega
    · have := ho hw; rw [NativeRustcX64.Sym.inRange_iff c.oW, hq] at h; unfold Sep at this; omega

omit [Labels] in
/-- Fewer regions written: more bytes kept. -/
theorem same_mono {wr wr' : Nat → Bool} (hw : ∀ i, wr i = true → wr' i = true) {d : MachineData}
    (hs : SameOutside m0.dmem d.dmem
      (fun q ↦ InRange (stackBelow m0 verifyKeccakStack) verifyKeccakStack q ∨
        outsOf (rsOf m0) wr q)) :
    SameOutside m0.dmem d.dmem
      (fun q ↦ InRange (stackBelow m0 verifyKeccakStack) verifyKeccakStack q ∨
        outsOf (rsOf m0) wr' q) :=
  fun q hq ↦ hs q fun h ↦ hq (h.imp id fun ⟨i, e, h1, h2, h3⟩ ↦ ⟨i, e, hw _ h1, h2, h3⟩)

/-- **The stack arguments**, loaded from region `0` (`3352 + 8 i`). -/
theorem argLoad (c : Ctx a inst m0) {wr : Nat → Bool} {d : MachineData}
    (hs : SameOutside m0.dmem d.dmem
      (fun q ↦ InRange (stackBelow m0 verifyKeccakStack) verifyKeccakStack q ∨
        outsOf (rsOf m0) wr q))
    {vals : Nat → BitVec 64} {ret : BitVec 64} {i : Nat} (hi : i < 2) :
    (envZ m0 d 3344 3368 (rsOf m0) vals ret).load 0 (3352 + 8 * i) 8 = stackArg m0 i := by
  rw [load_eq_wordOf]
  unfold stackArg
  have he : (envZ m0 d 3344 3368 (rsOf m0) vals ret).base 0 + BitVec.ofNat 64 (3352 + 8 * i) =
      rspOf m0 + BitVec.ofNat 64 (8 + 8 * i) := by
    rw [show 3352 + 8 * i = 3344 + (8 + 8 * i) by omega]
    exact NativeRustcVmX64.Field.frame_add (m0 := m0) 3344 _
  rw [he]
  refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun j hj ↦ ?_)
  have hx : (rspOf m0 + BitVec.ofNat 64 (8 + 8 * i)).toNat = (rspOf m0).toNat + (8 + 8 * i) :=
    toNat_add_ofNat (rspOf m0) (8 + 8 * i) (by have := c.top; omega)
  have hK := c.K
  have := c.sp
  have := c.top
  have har := c.ar
  have h1 := c.tar
  have h2 := c.sar
  have h3 := c.car
  have h4 := c.oar
  unfold Sep at h1 h2 h3 h4
  have hsame : NativeRustcVm.Layout.Same m0.dmem d.dmem (rspOf m0 + BitVec.ofNat 64 (8 + 8 * i)) 8 :=
    same_ro c hs (by rw [hx]; omega) (by unfold Sep; rw [hx]; omega)
      (fun _ ↦ by unfold Sep; rw [hx]; omega) (fun _ ↦ by unfold Sep; rw [hx]; omega)
      (fun _ ↦ by unfold Sep; rw [hx]; omega) (fun _ ↦ by unfold Sep; rw [hx]; omega)
  exact hsame j hj

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
