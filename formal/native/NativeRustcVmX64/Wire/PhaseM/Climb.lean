module

public import NativeRustcVmX64.Wire.PhaseM.Hash
public import NativeRustcVm.Wire.ClimbFacts
public import NativeRustcVmX64.Code.Vm.ClimbLevel.Names

/-!
# `phase_m`: the climb (x86-64)

`ClimbSt l`: at level `l`'s head (`b30`), the levels read so far `acc` (their siblings from the
working area's byte `24832`, their counts from `24576`), the level's nodes `ns` at the working
area's byte `4096 + 10240 (l % 2)`, the rest of the climb in the model (`climb_acc`). `Pre36`: at
`write_openings`' arguments (`b36`), every level read. `climb_entry`: from `Climb0`, the climb's
set-up (`b28`, `b29`) to level 0, or with height zero (`b35`) to `Pre36`. `climb_step`: a level
(`b30` to `b33`, `climb_level` by contract), to the next level, or after the last (`b34`) to
`Pre36`. `climb_run`: the climb.
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk wordAt_write load_ofMachine
  stackOk_callee mapped_off RcAt.callee)
open NativeRustcVmX64.Sumcheck (wordAt_written)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off Mapped.keeps)
open NativeRustcVmX64.Wire.Decode (eqv_eval ult_eval)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **At level `l`'s head** (`b30`). -/
structure ClimbSt [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8)
    (c k count : Nat) (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 l : Nat)
    (acc : List (List (Nat × Digest))) (ns : List (Nat × Digest)) (cl : Nat) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b30Offset)
  bod : Bod m0 8 st.data
  mid : Mid m0 B c count qs height lw rows c6 st.data.dmem
  accl : acc.length = l
  model : climbM B height (nodes0 qs lw rows) c6 =
    (climbM B (height - l) ns cl).map fun q ↦ (acc ++ q.1, q.2)
  ll : l < height
  nsl : ns.length ≤ 256
  sibs : SibsAt st.data.dmem (wa m0 24832) (wa m0 24576) acc
  nodes : NodesAt st.data.dmem (wa m0 (4096 + 10240 * (l % 2))) ns
  rd : ReaderAt st.data.dmem (RD m0) bp B cl
  rbp : (reg st.data .rbp).toNat = (sortD qs).length
  rbx : reg st.data .rbx = wa m0 2048
  rdx : (reg st.data .rdx).toNat = ns.length
  rdi : (reg st.data .rdi).toNat = 10240 * l
  r11 : reg st.data .r11 = wa m0 24832
  r13 : (reg st.data .r13).toNat = l

/-- **At `write_openings`' arguments** (`b36`), every level read. -/
structure Pre36 [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8)
    (c k count : Nat) (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 : Nat)
    (sl : List (List (Nat × Digest))) (cf : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b36Offset)
  bod : Bod m0 8 st.data
  mid : Mid m0 B c count qs height lw rows c6 st.data.dmem
  model : climbM B height (nodes0 qs lw rows) c6 = some (sl, cf)
  sll : sl.length = height
  sibs : SibsAt st.data.dmem (wa m0 24832) (wa m0 24576) sl
  rd : ReaderAt st.data.dmem (RD m0) bp B cf
  rbp : (reg st.data .rbp).toNat = (sortD qs).length
  rcx : reg st.data .rcx = wa m0 2048
  r9 : (reg st.data .r9).toNat = lw
  r10 : (reg st.data .r10).toNat = height
  r11 : reg st.data .r11 = wa m0 24832
  r15 : reg st.data .r15 = OUT m0


/-- **After `climb_level`** (`b32`), at level `l`. -/
structure Lev [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8)
    (c k count : Nat) (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 l : Nat)
    (acc : List (List (Nat × Digest))) (ns : List (Nat × Digest)) (cl : Nat) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b32Offset)
  bod : Bod m0 8 st.data
  mid : Mid m0 B c count qs height lw rows c6 st.data.dmem
  accl : acc.length = l
  model : climbM B height (nodes0 qs lw rows) c6 =
    (climbM B (height - l) ns cl).map fun q ↦ (acc ++ q.1, q.2)
  ll : l < height
  nsl : ns.length ≤ 256
  sibs : SibsAt st.data.dmem (wa m0 24832) (wa m0 24576) acc
  rbp : (reg st.data .rbp).toNat = (sortD qs).length
  rbx : reg st.data .rbx = wa m0 2048
  r13 : (reg st.data .r13).toNat = l
  r15 : (reg st.data .r15).toNat = ns.length
  f24 : FW m0 st.data.dmem 24 (10240 * l).toUInt64
  res : match sibsM B ns ns cl with
    | some (sl, c') => reg st.data .rax = 1 ∧
        (reg st.data .rdx).toNat = (parentsOf ns sl).length ∧
        NodesAt st.data.dmem (wa m0 (24832 + 10240 * l)) (sl.map fun s ↦ (s.1, s.2.1)) ∧
        NodesAt st.data.dmem (wa m0 (4096 + 10240 * ((l + 1) % 2))) (parentsOf ns sl) ∧
        ReaderAt st.data.dmem (RD m0) bp B c'
    | none => reg st.data .rax = 0


/-- **At `climb_level`'s entry**, at level `l`. -/
structure CallSt [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8)
    (c k count : Nat) (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 l : Nat)
    (acc : List (List (Nat × Digest))) (ns : List (Nat × Digest)) (cl : Nat) (st : MachineState) :
    Prop where
  pc : st.pc = Labels.label NativeRustcVmX64.Vm.ClimbLevel.entryLabel
  ret : retOf st.data = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b32Offset)
  bod : Bod m0 0 st.data
  mid : Mid m0 B c count qs height lw rows c6 st.data.dmem
  accl : acc.length = l
  model : climbM B height (nodes0 qs lw rows) c6 =
    (climbM B (height - l) ns cl).map fun q ↦ (acc ++ q.1, q.2)
  ll : l < height
  nsl : ns.length ≤ 256
  sibs : SibsAt st.data.dmem (wa m0 24832) (wa m0 24576) acc
  nodes : NodesAt st.data.dmem (wa m0 (4096 + 10240 * (l % 2))) ns
  rd : ReaderAt st.data.dmem (RD m0) bp B cl
  rbp : (reg st.data .rbp).toNat = (sortD qs).length
  rbx : reg st.data .rbx = wa m0 2048
  r13 : (reg st.data .r13).toNat = l
  r15 : (reg st.data .r15).toNat = ns.length
  rdi : reg st.data .rdi = RD m0
  rsi : reg st.data .rsi = wa m0 (4096 + 10240 * (l % 2))
  rcx : reg st.data .rcx = wa m0 (24832 + 10240 * l)
  r8 : reg st.data .r8 = wa m0 (4096 + 10240 * ((l + 1) % 2))
  rdx : (reg st.data .rdx).toNat = ns.length
  f24 : FW m0 st.data.dmem 24 (10240 * l).toUInt64

end

public section

theorem climbFin_none {B : List UInt8} {qs : List Nat} {height lw : Nat} {rows : List (List K)}
    {c6 : Nat} (h : climbM B height (nodes0 qs lw rows) c6 = none) :
    climbFin B qs height lw rows c6 = none := by
  unfold climbFin; rw [h]

theorem and1_eq (x : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) =
      decide (x.toNat % 2 = 0) := by
  simp only [CmpOp.apply, BinOp.apply, low_ext]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq, BitVec.toNat_and,
    toNat_low, toNat_low, toNat_low]
  have h1 : (BitVec.ofNat 64 1).toNat % 2 ^ Width.W8.bits = 2 ^ 1 - 1 := rfl
  have h0 : (BitVec.ofNat 64 0).toNat % 2 ^ Width.W8.bits = 0 := rfl
  rw [h1, h0, Nat.and_two_pow_sub_one_eq_mod]
  show x.toNat % 256 % 2 = 0 ↔ _
  omega

theorem sel_eq (m0 : MachineData) (l : Nat) :
    (if l % 2 = 0 then wa m0 4096 else wa m0 14336) = wa m0 (4096 + 10240 * (l % 2)) := by
  rcases Nat.mod_two_eq_zero_or_one l with h | h <;> simp [h]

theorem sel_eq' (m0 : MachineData) (l : Nat) :
    (if l % 2 = 0 then wa m0 14336 else wa m0 4096) = wa m0 (4096 + 10240 * ((l + 1) % 2)) := by
  rcases Nat.mod_two_eq_zero_or_one l with h | h <;> simp [h, Nat.add_mod]

/-- Seven regions pairwise apart, by numbers. -/
theorem disjoint7 {a1 a2 a3 a4 a5 a6 a7 : BitVec 64} {n1 n2 n3 n4 n5 n6 n7 : Nat}
    (h12 : a1.toNat + n1 ≤ a2.toNat ∨ a2.toNat + n2 ≤ a1.toNat)
    (h13 : a1.toNat + n1 ≤ a3.toNat ∨ a3.toNat + n3 ≤ a1.toNat)
    (h14 : a1.toNat + n1 ≤ a4.toNat ∨ a4.toNat + n4 ≤ a1.toNat)
    (h15 : a1.toNat + n1 ≤ a5.toNat ∨ a5.toNat + n5 ≤ a1.toNat)
    (h16 : a1.toNat + n1 ≤ a6.toNat ∨ a6.toNat + n6 ≤ a1.toNat)
    (h17 : a1.toNat + n1 ≤ a7.toNat ∨ a7.toNat + n7 ≤ a1.toNat)
    (h23 : a2.toNat + n2 ≤ a3.toNat ∨ a3.toNat + n3 ≤ a2.toNat)
    (h24 : a2.toNat + n2 ≤ a4.toNat ∨ a4.toNat + n4 ≤ a2.toNat)
    (h25 : a2.toNat + n2 ≤ a5.toNat ∨ a5.toNat + n5 ≤ a2.toNat)
    (h26 : a2.toNat + n2 ≤ a6.toNat ∨ a6.toNat + n6 ≤ a2.toNat)
    (h27 : a2.toNat + n2 ≤ a7.toNat ∨ a7.toNat + n7 ≤ a2.toNat)
    (h34 : a3.toNat + n3 ≤ a4.toNat ∨ a4.toNat + n4 ≤ a3.toNat)
    (h35 : a3.toNat + n3 ≤ a5.toNat ∨ a5.toNat + n5 ≤ a3.toNat)
    (h36 : a3.toNat + n3 ≤ a6.toNat ∨ a6.toNat + n6 ≤ a3.toNat)
    (h37 : a3.toNat + n3 ≤ a7.toNat ∨ a7.toNat + n7 ≤ a3.toNat)
    (h45 : a4.toNat + n4 ≤ a5.toNat ∨ a5.toNat + n5 ≤ a4.toNat)
    (h46 : a4.toNat + n4 ≤ a6.toNat ∨ a6.toNat + n6 ≤ a4.toNat)
    (h47 : a4.toNat + n4 ≤ a7.toNat ∨ a7.toNat + n7 ≤ a4.toNat)
    (h56 : a5.toNat + n5 ≤ a6.toNat ∨ a6.toNat + n6 ≤ a5.toNat)
    (h57 : a5.toNat + n5 ≤ a7.toNat ∨ a7.toNat + n7 ≤ a5.toNat)
    (h67 : a6.toNat + n6 ≤ a7.toNat ∨ a7.toNat + n7 ≤ a6.toNat) :
    NativeRustcVm.Disjoint [⟨a1, n1⟩, ⟨a2, n2⟩, ⟨a3, n3⟩, ⟨a4, n4⟩, ⟨a5, n5⟩, ⟨a6, n6⟩,
      ⟨a7, n7⟩] := by
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
    implies_true, NativeRustcVm.Apart]
  exact ⟨⟨h12, h13, h14, h15, h16, h17⟩, ⟨h23, h24, h25, h26, h27⟩, ⟨h34, h35, h36, h37⟩,
    ⟨h45, h46, h47⟩, ⟨h56, h57⟩, h67⟩

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

omit [Host] in
/-- **What holds is kept** by a change in the stack (the frame's words given), the cursor, the
phase and the working area between the positions and the leaves. -/
theorem Mid.keepF [Labels] (G : Geo m0 bp B.length) {count : Nat} {qs : List Nat}
    {height lw : Nat} {rows : List (List K)} {c6 : Nat} {d d' : Mem 64}
    (h : Mid m0 B c count qs height lw rows c6 d) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → (SP0 m0 - 1216 ≤ q.toNat ∧ q.toNat < SP0 m0) ∨
      ((RD m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (RD m0).toNat + 24) ∨
      ((WK m0).toNat + 4096 ≤ q.toNat ∧ q.toNat < (WK m0).toNat + 352512))
    (f16 : FW m0 d' 16 lw.toUInt64) (f32 : FW m0 d' 32 height.toUInt64)
    (f40 : FW m0 d' 40 count.toUInt64) (f56 : FW m0 d' 56 (UInt64.ofBitVec (wa m0 352512))) :
    Mid m0 B c count qs height lw rows c6 d' := by
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hsW := G.sW
  have hrW := G.rW
  have hrn := G.rNw
  have hql := h.len
  have hps := h.ps256
  have hrl := h.rlen
  have hcnt := h.cnt
  have hw0 := G.wa (o := 0) (by omega)
  have hw2 := G.wa (o := 2048) (by omega)
  have hw3 := G.wa (o := 352512) (by omega)
  refine ⟨h.model, hql, h.cnt0, hcnt, h.qlt, h.h32, h.lw64, h.ps0, hps, hrl, h.rw, f16, f32, f40,
    f56, ?_, ?_, ?_⟩
  · refine wordsAt_keep h.qsW hs (by rw [List.length_map, hw0]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw0]
    have := hR q hq
    omega
  · refine wordsAt_keep h.psW hs (by rw [List.length_map, hw2]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw2]
    have := hR q hq
    omega
  · have hl : (leavesOf lw rows).length = (sortD qs).length := by simp [hrl]
    refine leaves_keep h.lvW hs (fun x hx ↦ ?_) (by rw [hl, hw3]; omega) fun q hq ↦ ?_
    · simp only [leavesOf, List.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      rw [length_paddedLeaf (h.rw r hr)]; exact h.lw64
    · rw [hl, hw3]
      have := hR q hq
      omega

omit [Host] in
/-- Part of the working area is a region. -/
theorem wa_ok [Labels] (G : Geo m0 bp B.length) {d : Mem 64} (hk : Kept m0.dmem d) {o n : Nat}
    (ho : o < 483584) (h : o + n ≤ 483584) : NativeRustcVm.Region.Ok d ⟨wa m0 o, n⟩ := by
  have hw := G.wa (o := o) (by omega)
  have := G.wNw
  exact ⟨mapped_off (N := 483584) (Mapped.keeps G.wOk.1 hk) h,
    show (wa m0 o).toNat + n ≤ 2 ^ 64 by rw [hw]; omega⟩

omit [Host] in
/-- `climb_level`'s regions, apart. -/
theorem climb_disj [Labels] (G : Geo m0 bp B.length) {d : MachineData} {l n : Nat}
    (hS : (stackBelow d climbLevelStack).toNat = SP0 m0 - 160 - 1056) (hl : l < 32)
    (hn : n ≤ 256) :
    NativeRustcVm.Disjoint [stackR d climbLevelStack, rcR, ⟨RD m0, 24⟩, ⟨bp, B.length⟩,
      ⟨wa m0 (4096 + 10240 * (l % 2)), 40 * n⟩, ⟨wa m0 (24832 + 10240 * l), nodesBytes⟩,
      ⟨wa m0 (4096 + 10240 * ((l + 1) % 2)), nodesBytes⟩] := by
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hl2 : l % 2 < 2 := Nat.mod_lt _ (by decide)
  have hl2' : (l + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  have hlx : l % 2 + (l + 1) % 2 = 1 := by omega
  have hwN := G.wa (o := 4096 + 10240 * (l % 2)) (by omega)
  have hwX := G.wa (o := 4096 + 10240 * ((l + 1) % 2)) (by omega)
  have hwS := G.wa (o := 24832 + 10240 * l) (by omega)
  have hCS : climbLevelStack = 1056 := rfl
  have hNB : nodesBytes = 10240 := rfl
  exact disjoint7 (by have := G.sC; omega) (by have := G.sR; omega) (by have := G.sB; omega)
    (by have := G.sW; omega) (by have := G.sW; omega) (by have := G.sW; omega)
    (G.cR) (G.cB) (by have := G.cW; omega) (by have := G.cW; omega) (by have := G.cW; omega)
    (G.rB) (by have := G.rW; omega) (by have := G.rW; omega) (by have := G.rW; omega)
    (by have := G.bW; omega) (by have := G.bW; omega) (by have := G.bW; omega)
    (by omega) (by omega) (by omega)

/-- **The climb's set-up.** -/
theorem climb_entry (hp : Placed code k) (G : Geo m0 bp B.length) {count : Nat} {qs : List Nat}
    {height lw : Nat} {rows : List (List K)} {c6 : Nat} {st : MachineState}
    (h : Climb0 m0 bp B c k count qs height lw rows c6 st) :
    Eventually (step1 Host.exe) (fun st' ↦
      (∃ sl cf, Pre36 m0 bp B c k count qs height lw rows c6 sl cf st') ∨
      ClimbSt m0 bp B c k count qs height lw rows c6 0 [] (nodes0 qs lw rows) c6 st') st := by
  obtain ⟨hpc, hbod, hM, hrd, hbp, hbx, h9, hnd⟩ := h
  have h32 := hM.h32
  have hl := hM.rlen
  have hps := hM.ps256
  -- `b28`
  obtain ⟨hok28, h1128, hk28⟩ := ok_b28
  refine fblk hp G b28_in_code (by simp [b28]) exit_b28 nofun hok28 (hk28 .r12 (by simp))
    (hk28 .r14 (by simp)) hpc hbod fun s1 hb1 hd1 hm1 hpc1 ↦ ?_
  have e32 : (frameEnv m0 st.data 160 []).load 0 32 8 = height.toUInt64.toBitVec :=
    load_ofMachine (o := 32) rfl hM.f32
  have hh : height.toUInt64.toBitVec.toNat = height := by
    rw [UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
  have hc : (SBool.cmp .eq .W64 (.load 0 32 8) (.lit 0)).eval (frameEnv m0 st.data 160 []) =
      decide (height = 0) := by
    show CmpOp.apply .eq .W64 ((frameEnv m0 st.data 160 []).load 0 32 8) (BitVec.ofNat 64 0) = _
    rw [eqv_eval, e32, hh]; rfl
  simp only [PcOk, hc] at hpc1
  have r11 : reg s1.data .r11 = wa m0 24832 := by
    rw [show reg s1.data .r11 = _ from hm1.regs .r11 _ h1128]
    show BinOp.apply .add .W64 (reg st.data .r14) (BitVec.ofNat 64 24832) = _
    rw [hbod.r14, add_off]
  have rk1 : ∀ x ∈ [Reg64.rbx, .rbp], reg s1.data x = reg st.data x := fun x hx ↦
    hm1.regs x _ (hk28 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl <;> simp))
  by_cases h0 : height = 0
  · simp only [h0, decide_true, ↓reduceIte] at hpc1
    subst h0
    -- `b35`
    obtain ⟨hok35, hcx35, h1035, h1535, hk35⟩ := ok_b35
    refine fblk hp G b35_in_code (by simp [b35]) exit_b35 nofun hok35 (hk35 .r12 (by simp))
      (hk35 .r14 (by simp)) (hpc1.trans (hp.label NativeRustcVmX64.Vm.PhaseM.label_19_at)) hb1
      fun s2 hb2 hd2 hm2 hpc2 ↦ ?_
    have r9 : reg s1.data .r9 = reg st.data .r9 := hm1.regs .r9 (.reg .r9) (by decide +kernel)
    have hd : s2.data.dmem = st.data.dmem := hd2.trans hd1
    refine .done _ (.inl ⟨[], c6, hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b35_next), hb2,
      by rw [hd]; exact hM, rfl, rfl, fun j hj ↦ absurd hj (by simp), by rw [hd]; exact hrd,
      ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [show reg s2.data .rbp = reg s1.data .rbp from hm2.regs .rbp _ (hk35 .rbp (by simp)),
        rk1 .rbp (by simp)]; exact hbp
    · rw [show reg s2.data .rcx = _ from hm2.regs .rcx _ hcx35, ← hbx]
      exact rk1 .rbx (by simp)
    · rw [show reg s2.data .r9 = reg s1.data .r9 from hm2.regs .r9 _ (hk35 .r9 (by simp)), r9]
      exact h9
    · rw [show reg s2.data .r10 = _ from hm2.regs .r10 _ h1035]; rfl
    · rw [show reg s2.data .r11 = reg s1.data .r11 from hm2.regs .r11 _ (hk35 .r11 (by simp))]
      exact r11
    · rw [show reg s2.data .r15 = _ from hm2.regs .r15 _ h1535]
      exact load_ofMachine (o := 48) rfl (by rw [hd1]; exact hbod.out)
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b29`
  obtain ⟨hok29, hdx29, hdi29, h1329, hk29⟩ := ok_b29
  refine fblk hp G b29_in_code (by simp [b29]) exit_b29 nofun hok29 (hk29 .r12 (by simp))
    (hk29 .r14 (by simp)) (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b28_next)) hb1
    fun s2 hb2 hd2 hm2 hpc2 ↦ ?_
  have hd : s2.data.dmem = st.data.dmem := hd2.trans hd1
  have rk2 : ∀ x ∈ [Reg64.rbx, .rbp, .r11], reg s2.data x = reg s1.data x := fun x hx ↦
    hm2.regs x _ (hk29 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp))
  have ebp : (reg s1.data .rbp).toNat = (sortD qs).length := by rw [rk1 .rbp (by simp)]; exact hbp
  refine .done _ (.inr ⟨hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b29_next), hb2,
    by rw [hd]; exact hM, rfl, by simp, by omega, by rw [length_nodes0 hl]; omega,
    fun j hj ↦ absurd hj (by simp), by rw [hd]; simpa using hnd, by rw [hd]; exact hrd,
    by rw [rk2 .rbp (by simp)]; exact ebp,
    by rw [rk2 .rbx (by simp), rk1 .rbx (by simp)]; exact hbx, ?_, ?_,
    by rw [rk2 .r11 (by simp)]; exact r11, ?_⟩)
  · rw [show reg s2.data .rdx = _ from hm2.regs .rdx _ hdx29, length_nodes0 hl]; exact ebp
  · rw [show reg s2.data .rdi = _ from hm2.regs .rdi _ hdi29]; rfl
  · rw [show reg s2.data .r13 = _ from hm2.regs .r13 _ h1329]; rfl

/-- **A level's arguments**: `b30`, `b31`. -/
theorem climb_args (hp : Placed code k) (G : Geo m0 bp B.length)
    {count : Nat}
    {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 l : Nat}
    {acc : List (List (Nat × Digest))} {ns : List (Nat × Digest)} {cl : Nat} {st : MachineState}
    (h : ClimbSt m0 bp B c k count qs height lw rows c6 l acc ns cl st) :
    Eventually (step1 Host.exe) (CallSt m0 bp B c k count qs height lw rows c6 l acc ns cl) st := by
  obtain ⟨hpc, hbod, hM, hal, hmod, hll, hnsl, hsb, hnd, hrd, hbp, hbx, hdx, hdi, h11, h13⟩ := h
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hsW := G.sW
  have hrn := G.rNw
  have hbn := G.bNw
  have hcn := G.cNw
  have h32 := hM.h32
  have hl2 : l % 2 < 2 := Nat.mod_lt _ (by decide)
  have hl2' : (l + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  have hlx : l % 2 + (l + 1) % 2 = 1 := by omega
  have hwN := G.wa (o := 4096 + 10240 * (l % 2)) (by omega)
  have hwX := G.wa (o := 4096 + 10240 * ((l + 1) % 2)) (by omega)
  have hwS := G.wa (o := 24832 + 10240 * l) (by omega)
  have hwC := G.wa (o := 24576 + 8 * l) (by omega)
  have hwS0 := G.wa (o := 24832) (by omega)
  have hwC0 := G.wa (o := 24576) (by omega)
  -- `b30`: at most 256 nodes.
  obtain ⟨hok30, hk30⟩ := ok_b30
  refine fblk hp G b30_in_code (by simp [b30]) exit_b30 nofun hok30 (hk30 .r12 (by simp))
    (hk30 .r14 (by simp)) hpc hbod fun s1 hb1 hd1 hm1 hpc1 ↦ ?_
  have hc30 : (SBool.cmp .ult .W64 (.reg .rdx) (.lit 257)).not.eval (frameEnv m0 st.data 160 []) =
      false := by
    show (!CmpOp.apply .ult .W64 (reg st.data .rdx) (BitVec.ofNat 64 257)) = false
    rw [ult_eval, hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide), decide_eq_true (by omega)]
    rfl
  simp only [PcOk, hc30, Bool.false_eq_true, ↓reduceIte] at hpc1
  have rk1 : ∀ x ∈ [Reg64.rbx, .rbp, .rdx, .rdi, .r11, .r13], reg s1.data x = reg st.data x :=
    fun x hx ↦ hm1.regs x _ (hk30 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  -- `b31`: `climb_level`'s arguments.
  obtain ⟨hmid31, hw31, h2431, hdi31, hsi31, hr831, hcx31, h1531, hk31⟩ := ok_b31
  refine wblk hp G b31_in_code (by simp [b31]) exit_b31 hmid31
    (fun w hw ↦ by obtain ⟨h1, h2⟩ := hw31 w hw; exact ⟨h1, by omega, by omega⟩)
    (hk31 .r12 (by simp)) (hk31 .r14 (by simp))
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b30_next)) hb1 fun s2 hb2 hs2 hkeep2 hm2 hpc2 ↦ ?_
  have env31 : ∀ x, (frameEnv m0 s1.data 160 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b31Offset + b31.length)).toBitVec).regs x = reg s1.data x := fun _ ↦ rfl
  have e13 : (reg s1.data .r13).toNat = l := by rw [rk1 .r13 (by simp)]; exact h13
  have hsel : CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg s1.data .r13) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 0) = decide (l % 2 = 0) := by rw [and1_eq, e13]
  have ew : ∀ o, BinOp.apply .add .W64 (reg s1.data .r14) (BitVec.ofNat 64 o) = wa m0 o :=
    fun o ↦ by rw [hb1.r14, add_off]
  have hdi2 : reg s2.data .rdi = RD m0 := (hm2.regs .rdi _ hdi31).trans hb1.r12
  have hsi2 : reg s2.data .rsi = wa m0 (4096 + 10240 * (l % 2)) := by
    rw [show reg s2.data .rsi = _ from hm2.regs .rsi _ hsi31]
    simp only [evenSel, Sym.eval, SBool.eval, env31, hsel, ew]
    rw [← sel_eq]
    by_cases h : l % 2 = 0 <;> simp [h]
  have hr82 : reg s2.data .r8 = wa m0 (4096 + 10240 * ((l + 1) % 2)) := by
    rw [show reg s2.data .r8 = _ from hm2.regs .r8 _ hr831]
    simp only [evenSel, Sym.eval, SBool.eval, env31, hsel, ew]
    rw [← sel_eq']
    by_cases h : l % 2 = 0 <;> simp [h]
  have hcx2 : reg s2.data .rcx = wa m0 (24832 + 10240 * l) := by
    rw [show reg s2.data .rcx = _ from hm2.regs .rcx _ hcx31]
    show BinOp.apply .add .W64 (reg s1.data .r11) (reg s1.data .rdi) = _
    have : reg s1.data .rdi = BitVec.ofNat 64 (10240 * l) := by
      apply BitVec.eq_of_toNat_eq
      rw [rk1 .rdi (by simp), hdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [this, rk1 .r11 (by simp), h11, add_off, off_off]
  have hdx2 : (reg s2.data .rdx).toNat = ns.length := by
    rw [show reg s2.data .rdx = _ from hm2.regs .rdx _ (hk31 .rdx (by simp))]
    show (reg s1.data .rdx).toNat = _
    rw [rk1 .rdx (by simp)]
    exact hdx
  have h152 : (reg s2.data .r15).toNat = ns.length := by
    rw [show reg s2.data .r15 = _ from hm2.regs .r15 _ h1531]
    show (reg s1.data .rdx).toNat = _
    rw [rk1 .rdx (by simp)]; exact hdx
  have hf24 : FW m0 s2.data.dmem 24 (UInt64.ofBitVec (reg s1.data .rdi)) := by
    have := wordAt_write hm2 (r := 0) (o := 24) rfl (by omega) h2431
    simp only [Sym.eval, Env.ofMachine_regs] at this
    exact this
  have hmiss : ∀ o, o = 16 ∨ o = 32 ∨ o = 40 ∨ o = 56 → ∀ w ∈ (after b31 frS).mem, w.r = 0 →
      w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o ho w hw _ ↦ by
    have := hw31 w hw; omega
  have hk2 : ∀ o v, o = 16 ∨ o = 32 ∨ o = 40 ∨ o = 56 → FW m0 st.data.dmem o v →
      FW m0 s2.data.dmem o v := fun o v ho hf ↦
    hkeep2 o v (by omega) (hmiss o ho) (by rw [hd1]; exact hf)
  have hM2 : Mid m0 B c count qs height lw rows c6 s2.data.dmem :=
    Mid.keepF G (d := s1.data.dmem) (by rw [hd1]; exact hM) hs2
      (fun q hq ↦ .inl ⟨by omega, by omega⟩)
      (hk2 16 _ (by omega) hM.f16) (hk2 32 _ (by omega) hM.f32) (hk2 40 _ (by omega) hM.f40)
      (hk2 56 _ (by omega) hM.f56)
  have hrd2 : ReaderAt s2.data.dmem (RD m0) bp B cl :=
    reader_sw G (by rw [hd1]; exact hrd) hs2 fun q hq ↦ .inl ⟨by omega, by omega⟩
  have hnd2 : NodesAt s2.data.dmem (wa m0 (4096 + 10240 * (l % 2))) ns := by
    refine nodes_keep (by rw [hd1]; exact hnd) hs2 (by rw [hwN]; omega) fun q hq ↦ ?_
    rw [hwN]; omega
  have hsb2 : SibsAt s2.data.dmem (wa m0 24832) (wa m0 24576) acc := by
    refine sibs_keep (by rw [hd1]; exact hsb) hs2 (by rw [hwS0, hal]; omega)
      (by rw [hwC0, hal]; omega) (fun q hq ↦ ?_) fun q hq ↦ ?_
    · rw [hwS0]; omega
    · rw [hwC0]; omega
  have e24 : UInt64.ofBitVec (reg s1.data .rdi) = (10240 * l).toUInt64 :=
    toNat_reg_eq (by rw [rk1 .rdi (by simp)]; exact hdi)
  rw [e24] at hf24
  have rk2 : ∀ x ∈ [Reg64.rbx, .rbp, .r13], reg s2.data x = reg s1.data x := fun x hx ↦
    hm2.regs x _ (hk31 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp))
  simp only [PcOk] at hpc2
  refine .done _ ⟨hpc2.1, hpc2.2, hb2, hM2, hal, hmod, hll, hnsl, hsb2, hnd2, hrd2, ?_, ?_, ?_,
    h152, hdi2, hsi2, hcx2, hr82, hdx2, hf24⟩
  · rw [rk2 .rbp (by simp), rk1 .rbp (by simp)]; exact hbp
  · rw [rk2 .rbx (by simp), rk1 .rbx (by simp)]; exact hbx
  · rw [rk2 .r13 (by simp)]; exact e13

/-- The numbers of what `climb_level` changes. -/
abbrev ClimbCh (m0 : MachineData) (l : Nat) (q : BitVec 64) : Prop :=
  ((WK m0).toNat + (24832 + 10240 * l) ≤ q.toNat ∧
      q.toNat < (WK m0).toNat + (24832 + 10240 * l) + 10240) ∨
    ((WK m0).toNat + (4096 + 10240 * ((l + 1) % 2)) ≤ q.toNat ∧
      q.toNat < (WK m0).toNat + (4096 + 10240 * ((l + 1) % 2)) + 10240) ∨
    ((RD m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (RD m0).toNat + 24) ∨
    (SP0 m0 - 1216 ≤ q.toNat ∧ q.toNat < SP0 m0 - 160)

omit [Host] in
/-- **What `climb_level` changes**, as numbers. -/
theorem climb_so [Labels] (G : Geo m0 bp B.length) {d d' : MachineData} {l : Nat}
    (hdi : reg d .rdi = RD m0) (hcx : reg d .rcx = wa m0 (24832 + 10240 * l))
    (hr8 : reg d .r8 = wa m0 (4096 + 10240 * ((l + 1) % 2))) (hsp : rspOf d = stackBelow m0 160)
    (hl : l < 32)
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InAny
      [⟨reg d .rcx, nodesBytes⟩, ⟨reg d .r8, nodesBytes⟩, curRegion (reg d .rdi),
        frameR d climbLevelStack])) :
    NativeRustcVm.SameOutside d.dmem d'.dmem (ClimbCh m0 l) := by
  have hsp0 := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hrn := G.rNw
  have hl2' : (l + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  have hwX := G.wa (o := 4096 + 10240 * ((l + 1) % 2)) (by omega)
  have hwS := G.wa (o := 24832 + 10240 * l) (by omega)
  have hCS : climbLevelStack = 1056 := rfl
  obtain ⟨hcs2, -⟩ := callee_toNat (n := climbLevelStack) hsp (by rw [hCS]; omega)
  have h16 : (off (RD m0) 16).toNat = (RD m0).toNat + 16 := toNat_off (by omega)
  refine NativeRustcVm.SameOutside.mono hso fun q ⟨R, hR, hq⟩ ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl | rfl
  · have hq' : NativeRustcVm.InRange (reg d .rcx) nodesBytes q := hq
    rw [hcx, show nodesBytes = 10240 from rfl] at hq'
    have := iv_of_inRange (by rw [hwS]; omega) hq'
    rw [hwS] at this; exact .inl ⟨by omega, by omega⟩
  · have hq' : NativeRustcVm.InRange (reg d .r8) nodesBytes q := hq
    rw [hr8, show nodesBytes = 10240 from rfl] at hq'
    have := iv_of_inRange (by rw [hwX]; omega) hq'
    rw [hwX] at this; exact .inr (.inl ⟨by omega, by omega⟩)
  · have hq' : NativeRustcVm.InRange (off (reg d .rdi) 16) 8 q := hq
    rw [hdi] at hq'
    have := iv_of_inRange (by rw [h16]; omega) hq'
    rw [h16] at this; exact .inr (.inr (.inl ⟨by omega, by omega⟩))
  · have hq' : NativeRustcVm.InRange (stackBelow d climbLevelStack) climbLevelStack q := hq
    have := iv_of_inRange (by rw [hcs2, hCS]; omega) hq'
    rw [hcs2, hCS] at this; exact .inr (.inr (.inr ⟨by omega, by omega⟩))

omit [Host] in
theorem climb_wr [Labels] (G : Geo m0 bp B.length) {l : Nat} (hl : l < 32) :
    ∀ q, ClimbCh m0 l q → Wr m0 q := fun q hq ↦ by
  have := G.sp
  have hl2' : (l + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold Wr
  rcases hq with hq | hq | hq | hq
  · exact .inr (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩))))
  · exact .inr (.inr (.inr (.inl hq)))
  · exact .inl ⟨hq.1, by omega⟩

omit [Host] in
/-- **`climb_level`'s precondition** at level `l`. -/
theorem climb_pre [Labels] (G : Geo m0 bp B.length) {d : MachineData} (hb : Bod m0 0 d) {l : Nat}
    (hl : l < 32) {ns : List (Nat × Digest)} (hnsl : ns.length ≤ 256) {cl : Nat}
    (hrd : ReaderAt d.dmem (RD m0) bp B cl) (hdi : reg d .rdi = RD m0)
    (hsi : reg d .rsi = wa m0 (4096 + 10240 * (l % 2)))
    (hcx : reg d .rcx = wa m0 (24832 + 10240 * l))
    (hr8 : reg d .r8 = wa m0 (4096 + 10240 * ((l + 1) % 2)))
    (hdx : (reg d .rdx).toNat = ns.length) : ClimbLevelPre d := by
  have hsp := G.sp
  have hl2 : l % 2 < 2 := Nat.mod_lt _ (by decide)
  have hl2' : (l + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  have hsp2 : rspOf d = stackBelow m0 160 := by rw [hb.fr.sp, off_zero]
  have hCS : climbLevelStack = 1056 := rfl
  obtain ⟨hcs2, -⟩ := callee_toNat (n := climbLevelStack) hsp2 (by rw [hCS]; omega)
  have hrcs := G.rc_keep hb.chg
  unfold ClimbLevelPre
  rw [hdi, hsi, hcx, hr8, hdx]
  refine ⟨stackOk_callee G.st hb.fr.kept hsp2 (by rw [hCS]),
    RcAt.callee G.rc hrcs hsp2 G.sp (by rw [hCS]), hnsl,
    wa_ok G hb.fr.kept (by omega) (by omega),
    wa_ok G hb.fr.kept (by omega) (by unfold nodesBytes; omega),
    wa_ok G hb.fr.kept (by omega) (by unfold nodesBytes; omega),
    bp, B, cl, hrd, ?_, ?_⟩
  · exact climb_disj G (by rw [hcs2, hCS]) (by omega) hnsl
  · refine G.got.transport (G.got_keep hb.chg) ?_ ?_
    · intro s hs
      have hgs := (G.got.1 s hs).2.2.1
      change Apart (gotAddr s) 8 (stackBelow m0 1216) 1224 at hgs
      change Apart (gotAddr s) 8 (stackBelow d climbLevelStack) (climbLevelStack + 8)
      unfold NativeRustcX64.Apart at hgs ⊢
      rw [stackBelow_toNat G.sp] at hgs
      rw [hcs2, hCS, Nat.sub_sub]
      rcases hgs with hgs | hgs
      · exact Or.inl hgs
      · exact Or.inr (Nat.le_trans
          (Nat.add_le_add_left (by decide : 1056 + 8 ≤ 1224) _) hgs)
    · intro s hs a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact (G.got.1 s hs).2.2.2 (rcAddr, 192) (by simp)
      · exact (G.got.1 s hs).2.2.2 (RD m0, 24) (by simp)
      · have hw := (G.got.1 s hs).2.2.2 (WK m0, 483584) (by simp)
        change Apart (gotAddr s) 8 (wa m0 (24832 + 10240 * l)) nodesBytes
        unfold NativeRustcX64.Apart at hw ⊢
        dsimp only at hw
        rw [G.wa (by omega)]
        change (gotAddr s).toNat + 8 ≤ (WK m0).toNat + (24832 + 10240 * l) ∨
          (WK m0).toNat + (24832 + 10240 * l) + 10240 ≤ (gotAddr s).toNat
        omega
      · have hw := (G.got.1 s hs).2.2.2 (WK m0, 483584) (by simp)
        change Apart (gotAddr s) 8 (wa m0 (4096 + 10240 * ((l + 1) % 2))) nodesBytes
        unfold NativeRustcX64.Apart at hw ⊢
        dsimp only at hw
        rw [G.wa (by omega)]
        change (gotAddr s).toNat + 8 ≤ (WK m0).toNat + (4096 + 10240 * ((l + 1) % 2)) ∨
          (WK m0).toNat + (4096 + 10240 * ((l + 1) % 2)) + 10240 ≤ (gotAddr s).toNat
        omega

omit [Host] in
theorem climb_far [Labels] (G : Geo m0 bp B.length) {l : Nat} (hl : l < 32) :
    ∀ q, ClimbCh m0 l q → q.toNat < SP0 m0 - 160 ∨ SP0 m0 + 8 ≤ q.toNat := fun q hq ↦ by
  have := G.sp
  have hl2' : (l + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  rcases hq with hq | hq | hq | hq
  · have := G.sW; omega
  · have := G.sW; omega
  · have := G.sR; omega
  · omega

omit [Host] in
theorem climb_sib [Labels] (G : Geo m0 bp B.length) {l : Nat} (hl : l < 32) :
    ∀ q, ClimbCh m0 l q →
      (q.toNat < (WK m0).toNat + 24832 ∨ (WK m0).toNat + 24832 + 10240 * l ≤ q.toNat) ∧
      (q.toNat < (WK m0).toNat + 24576 ∨ (WK m0).toNat + 24576 + 8 * l ≤ q.toNat) :=
  fun q hq ↦ by
  have := G.sp
  have hl2' : (l + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  rcases hq with hq | hq | hq | hq
  · omega
  · omega
  · have := G.rW; omega
  · have := G.sW; omega

/-- **A level's call**: `climb_level` by contract. -/
theorem climb_res (G : Geo m0 bp B.length)
    (hcl : Spec (Labels.label NativeRustcVmX64.Vm.ClimbLevel.entryLabel) ClimbLevelPre ClimbLevelPost) {count : Nat}
    {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 l : Nat}
    {acc : List (List (Nat × Digest))} {ns : List (Nat × Digest)} {cl : Nat} {s2 : MachineState}
    (h : CallSt m0 bp B c k count qs height lw rows c6 l acc ns cl s2) :
    Eventually (step1 Host.exe) (Lev m0 bp B c k count qs height lw rows c6 l acc ns cl) s2 := by
  obtain ⟨hpc2, hret2, hb2, hM2, hal, hmod, hll, hnsl, hsb2, hnd2, hrd2, hbp, hbx, e13, h152,
    hdi2, hsi2, hcx2, hr82, hdx2, hf24⟩ := h
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hrn := G.rNw
  have h32 := hM2.h32
  have hl2' : (l + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  have hwX := G.wa (o := 4096 + 10240 * ((l + 1) % 2)) (by omega)
  have hwS := G.wa (o := 24832 + 10240 * l) (by omega)
  have hwS0 := G.wa (o := 24832) (by omega)
  have hwC0 := G.wa (o := 24576) (by omega)
  -- the call
  have hsp2 : rspOf s2.data = stackBelow m0 160 := by rw [hb2.fr.sp, off_zero]
  have hCS : climbLevelStack = 1056 := rfl
  obtain ⟨hcs2, -⟩ := callee_toNat (n := climbLevelStack) hsp2 (by rw [hCS]; omega)
  have hpre := climb_pre G hb2 (l := l) (by omega) hnsl hrd2 hdi2 hsi2 hcx2 hr82 hdx2
  refine Eventually.bind (Spec.apply hcl hpc2 hpre) fun s3 ⟨hpc3, hrsp3, hres3, hso3, hsv3⟩ ↦ ?_
  rw [hret2] at hpc3
  rw [hdi2, hsi2, hcx2, hr82, hdx2] at hres3
  have hso3' := climb_so G (d := s2.data) (d' := s3.data) (l := l) hdi2 hcx2 hr82 hsp2
    (by omega) hso3
  have hW3 := climb_wr G (l := l) (by omega)
  have hfar := climb_far G (l := l) (by omega)
  have hb3 : Bod m0 8 s3.data := Bod.call G hb2 hsv3 hrsp3 hso3' fun q hq ↦
    ⟨Wr.chg G (hW3 q hq), by have := hfar q hq; omega⟩
  have hres := hres3 bp B cl hrd2 ns rfl hnd2
  have rk3 : ∀ x ∈ [Reg64.rbx, .rbp, .r13, .r15], reg s3.data x = reg s2.data x := fun x hx ↦ by
    have hc : calleeSaved x = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> rfl
    exact hsv3.1 x hc
  have hM3 : Mid m0 B c count qs height lw rows c6 s3.data.dmem := Mid.keep G hM2 hso3' hW3
  have hf24' : FW m0 s3.data.dmem 24 (10240 * l).toUInt64 :=
    FW.keep G (by omega) hf24 hso3' fun q hq ↦ by have := hfar q hq; omega
  have hsb3 : SibsAt s3.data.dmem (wa m0 24832) (wa m0 24576) acc := by
    refine sibs_keep hsb2 hso3' (by rw [hwS0, hal]; omega) (by rw [hwC0, hal]; omega)
      (fun q hq ↦ ?_) fun q hq ↦ ?_
    · rw [hwS0, hal]; exact (climb_sib G (by omega) q hq).1
    · rw [hwC0, hal]; exact (climb_sib G (by omega) q hq).2
  refine .done _ ⟨hpc3, hb3, hM3, hal, hmod, hll, hnsl, hsb3, ?_, ?_, ?_, ?_, hf24', hres⟩
  · rw [rk3 .rbp (by simp)]; exact hbp
  · rw [rk3 .rbx (by simp)]; exact hbx
  · rw [rk3 .r13 (by simp)]; exact e13
  · rw [rk3 .r15 (by simp)]; exact h152

/-- **A level's end**: `b32`, `b33`, and after the last level `b34`. -/
theorem climb_tail (hp : Placed code k) (G : Geo m0 bp B.length)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c) {count : Nat}
    {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 l : Nat}
    {acc : List (List (Nat × Digest))} {ns : List (Nat × Digest)} {cl : Nat} {s3 : MachineState}
    (h : Lev m0 bp B c k count qs height lw rows c6 l acc ns cl s3) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (∃ acc' ns' cl', ClimbSt m0 bp B c k count qs height lw rows c6 (l + 1) acc' ns' cl' st') ∨
      ∃ sl cf, Pre36 m0 bp B c k count qs height lw rows c6 sl cf st') s3 := by
  obtain ⟨hpc3, hb3, hM3, hal, hmod, hll, hnsl, hsb3, hbp, hbx, e13, h152, hf24', hres⟩ := h
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have h32 := hM3.h32
  have hl2' : (l + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  have hwX := G.wa (o := 4096 + 10240 * ((l + 1) % 2)) (by omega)
  have hwS := G.wa (o := 24832 + 10240 * l) (by omega)
  have hwC := G.wa (o := 24576 + 8 * l) (by omega)
  have hwS0 := G.wa (o := 24832) (by omega)
  have hwC0 := G.wa (o := 24576) (by omega)
  -- `b32`: the tag.
  obtain ⟨hok32, hdi32, h1132, hk32⟩ := ok_b32
  refine fblk hp G b32_in_code (by simp [b32]) exit_b32 nofun hok32 (hk32 .r12 (by simp))
    (hk32 .r14 (by simp)) hpc3 hb3
    fun s4 hb4 hd4 hm4 hpc4 ↦ ?_
  simp only [PcOk] at hpc4
  have hh1 : height - l = (height - (l + 1)) + 1 := by omega
  rcases hsm : sibsM B ns ns cl with _ | ⟨sl, c'⟩
  · rw [hsm] at hres
    have hc : (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not.eval (frameEnv m0 s3.data 160 []) =
        true := by
      show (!CmpOp.apply .eq .W64 (reg s3.data .rax) (BitVec.ofNat 64 1)) = true
      rw [hres]; rfl
    simp only [hc, ↓reduceIte] at hpc4
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc4
    refine Eventually.mono (none_run hp G hR0 hpc4 hb4 ?_) fun _ h ↦ .inl h
    rw [hM3.model]
    refine climbFin_none ?_
    rw [hmod, hh1, climb_none hsm]
    rfl
  rw [hsm] at hres
  obtain ⟨hrax, hrdx, hsibs, hnext, hrd3⟩ := hres
  have hc : (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not.eval (frameEnv m0 s3.data 160 []) =
      false := by
    show (!CmpOp.apply .eq .W64 (reg s3.data .rax) (BitVec.ofNat 64 1)) = false
    rw [hrax]; rfl
  simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc4
  have hsl := sibsM_len B ns ns cl hsm
  have e32 : (frameEnv m0 s3.data 160 []).load 0 24 8 = BitVec.ofNat 64 (10240 * l) := by
    rw [load_ofMachine (o := 24) rfl hf24']
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, toNat_toUInt64 (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hdi4 : (reg s4.data .rdi).toNat = 10240 * l := by
    rw [show reg s4.data .rdi = _ from hm4.regs .rdi _ hdi32]
    simp only [Sym.eval]
    rw [e32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h114 : reg s4.data .r11 = wa m0 24832 := by
    rw [show reg s4.data .r11 = _ from hm4.regs .r11 _ h1132]
    show BinOp.apply .add .W64 (reg s3.data .r14) (BitVec.ofNat 64 24832) = _
    rw [hb3.r14, add_off]
  have rk4 : ∀ x ∈ [Reg64.rbx, .rbp, .rdx, .r13, .r15], reg s4.data x = reg s3.data x :=
    fun x hx ↦ hm4.regs x _ (hk32 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp))
  have e13' : (reg s4.data .r13).toNat = l := by
    rw [rk4 .r13 (by simp)]; exact e13
  have e15' : (reg s4.data .r15).toNat = ns.length := by
    rw [rk4 .r15 (by simp)]; exact h152
  -- `b33`: the level's count.
  have hm33 : Match (aEnv m0 s4.data (24576 + 8 * l) 8 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b33Offset + b33.length)).toBitVec)
      cntS s4.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb4.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg s4.data .r11)
            (BinOp.apply .mul .W64 (reg s4.data .r13) (BitVec.ofNat 64 8)) =
          wa m0 (24576 + 8 * l) + BitVec.ofInt 64 256
        rw [show BitVec.ofInt 64 256 = BitVec.ofNat 64 256 from rfl]
        apply BitVec.eq_of_toNat_eq
        simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_mul,
          BitVec.toNat_ofNat, h114, e13', hwC, hwS0]
        omega, trivial⟩
  obtain ⟨hmid33, hmem33, hw33, hdi33, h1033, h1333, hk33⟩ := ok_b33
  have hwf33 := aEnv_wf G hb4.fr.kept (o := 24576 + 8 * l) (n := 8) (by omega) (by omega)
    (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b33Offset + b33.length)).toBitVec
  refine ablk hp G b33_in_code (by simp [b33]) exit_b33 (by omega) (by omega) hmid33
    (fun w hw ↦ by rw [hmem33] at hw; simp only [List.mem_singleton] at hw; subst hw; decide)
    (hk33 .r12 (by simp)) (hk33 .r14 (by simp))
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b32_next)) hb4 hm33
    fun s5 hb5 _ _ hsw5 hm5 hpc5 ↦ ?_
  have hs5 : NativeRustcVm.SameOutside s4.data.dmem s5.data.dmem (fun q ↦
      (WK m0).toNat + (24576 + 8 * l) ≤ q.toNat ∧ q.toNat < (WK m0).toNat + (24576 + 8 * l) + 8) :=
    hsw5.mono fun q ⟨w, hw, h⟩ ↦ by
      rw [hmem33] at hw; simp only [List.mem_singleton] at hw; subst hw
      rcases h with ⟨h, -⟩ | ⟨-, h1, h2⟩
      · exact absurd h (by decide)
      · exact ⟨by simpa using h1, by simpa using h2⟩
  have hd4 : s4.data.dmem = s3.data.dmem := hd4
  have hM5 : Mid m0 B c count qs height lw rows c6 s5.data.dmem :=
    Mid.keep G (by rw [hd4]; exact hM3) hs5 fun q hq ↦ by
      unfold Wr
      exact .inr (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩))))
  have hrd5 : ReaderAt s5.data.dmem (RD m0) bp B c' :=
    reader_sw G (by rw [hd4]; exact hrd3) hs5 fun q hq ↦ .inr ⟨by omega, by omega⟩
  have hnext5 : NodesAt s5.data.dmem (wa m0 (4096 + 10240 * ((l + 1) % 2))) (parentsOf ns sl) := by
    have hpl := parentsOf_length_le ns sl
    refine nodes_keep (by rw [hd4]; exact hnext) hs5 (by rw [hwX]; omega) fun q hq ↦ ?_
    rw [hwX]; omega
  have hlev5 : NodesAt s5.data.dmem (wa m0 (24832 + 10240 * l)) (sl.map fun s ↦ (s.1, s.2.1)) := by
    have hml : (sl.map fun s ↦ (s.1, s.2.1)).length ≤ 256 := by
      rw [List.length_map, hsl]; exact hnsl
    refine nodes_keep (by rw [hd4]; exact hsibs) hs5 (by rw [hwS]; omega) fun q hq ↦ ?_
    rw [hwS]; omega
  have hcnt5 : NativeRustcVm.WordAt s5.data.dmem (off (wa m0 24576) (8 * acc.length))
      (sl.map fun s ↦ (s.1, s.2.1)).length.toUInt64 := by
    have := wordAt_write hm5 (r := 1) (o := 0) (b := wa m0 (24576 + 8 * l)) (sz := 8) rfl
      (by omega) hw33
    simp only [Sym.eval, Env.ofMachine_regs, off_zero] at this
    rw [show s4.data.regs.get64 .r15 = reg s4.data .r15 from rfl, toNat_reg_eq e15'] at this
    rw [List.length_map, hsl, hal, off_off]
    exact this
  have hsb5 : SibsAt s5.data.dmem (wa m0 24832) (wa m0 24576)
      (acc ++ [sl.map fun s ↦ (s.1, s.2.1)]) := by
    refine sibs_snoc ?_ (by rw [List.length_map, hsl]; exact hnsl) hcnt5 ?_
    · refine sibs_keep (by rw [hd4]; exact hsb3) hs5 (by rw [hwS0, hal]; omega)
        (by rw [hwC0, hal]; omega) (fun q hq ↦ ?_) fun q hq ↦ ?_
      · rw [hwS0, hal]; omega
      · rw [hwC0, hal]; omega
    · rw [hal, off_off, show nodesBytes * l = 10240 * l from rfl]; exact hlev5
  -- the registers
  have env33 : ∀ x, (aEnv m0 s4.data (24576 + 8 * l) 8
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b33Offset + b33.length)).toBitVec).regs x = reg s4.data x := fun _ ↦ rfl
  have e32' : (aEnv m0 s4.data (24576 + 8 * l) 8
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b33Offset + b33.length)).toBitVec).load 0 32 8 = height.toUInt64.toBitVec :=
    load_ofMachine (o := 32) rfl (by rw [hd4]; exact hM3.f32)
  have hh : height.toUInt64.toBitVec.toNat = height := by
    rw [UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
  have rk5 : ∀ x ∈ [Reg64.rbx, .rbp, .rdx, .r11], reg s5.data x = reg s4.data x := fun x hx ↦
    hm5.regs x _ (hk33 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> simp))
  have ebx : reg s5.data .rbx = wa m0 2048 := by
    rw [rk5 .rbx (by simp), rk4 .rbx (by simp)]; exact hbx
  have ebp : (reg s5.data .rbp).toNat = (sortD qs).length := by
    rw [rk5 .rbp (by simp), rk4 .rbp (by simp)]; exact hbp
  have e10 : (reg s5.data .r10).toNat = height := by
    rw [show reg s5.data .r10 = _ from hm5.regs .r10 _ h1033]
    simp only [Sym.eval]
    rw [e32', hh]
  simp only [PcOk] at hpc5
  have hc5 : (SBool.cmp .eq .W64 (.load 0 32 8) (.bin .add .W64 (.reg .r13) (.lit 1))).not.eval
      (aEnv m0 s4.data (24576 + 8 * l) 8 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b33Offset + b33.length)).toBitVec) =
      !decide (height = l + 1) := by
    show (!CmpOp.apply .eq .W64 ((aEnv m0 s4.data (24576 + 8 * l) 8
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b33Offset + b33.length)).toBitVec).load 0 32 8)
      (BinOp.apply .add .W64 (reg s4.data .r13) (BitVec.ofNat 64 1))) = _
    rw [eqv_eval, e32', hh]
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, e13']
    rw [Nat.mod_eq_of_lt (a := 1) (by decide), Nat.mod_eq_of_lt (by omega)]
  rw [hc5] at hpc5
  have hacc : (acc ++ [sl.map fun s ↦ (s.1, s.2.1)]).length = l + 1 := by simp [hal]
  have hmod' : climbM B height (nodes0 qs lw rows) c6 =
      (climbM B (height - (l + 1)) (parentsOf ns sl) c').map
        fun q ↦ ((acc ++ [sl.map fun s ↦ (s.1, s.2.1)]) ++ q.1, q.2) := by
    rw [hmod, hh1]; exact climb_acc hsm acc
  by_cases hlast : height = l + 1
  · simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc5
    have hfin : climbM B height (nodes0 qs lw rows) c6 =
        some (acc ++ [sl.map fun s ↦ (s.1, s.2.1)], c') := by
      rw [hmod', show height - (l + 1) = 0 by omega]
      simp [climbM]
    -- `b34`
    obtain ⟨hok34, hcx34, hr934, h1534, hk34⟩ := ok_b34
    refine fblk hp G b34_in_code (by simp [b34]) exit_b34 nofun hok34 (hk34 .r12 (by simp))
      (hk34 .r14 (by simp)) (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b33_next)) hb5
      fun s6 hb6 hd6 hm6 hpc6 ↦ ?_
    simp only [PcOk] at hpc6
    have rk6 : ∀ x ∈ [Reg64.rbp, .r10, .r11], reg s6.data x = reg s5.data x := fun x hx ↦
      hm6.regs x _ (hk34 x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl <;> simp))
    refine .done _ (.inr (.inr ⟨_, c', hpc6.trans (hp.label NativeRustcVmX64.Vm.PhaseM.label_20_at), hb6,
      by rw [hd6]; exact hM5, hfin, by rw [hacc, hlast], by rw [hd6]; exact hsb5,
      by rw [hd6]; exact hrd5, by rw [rk6 .rbp (by simp)]; exact ebp, ?_, ?_,
      by rw [rk6 .r10 (by simp)]; exact e10,
      by rw [rk6 .r11 (by simp), rk5 .r11 (by simp)]; exact h114, ?_⟩))
    · rw [show reg s6.data .rcx = _ from hm6.regs .rcx _ hcx34]; exact ebx
    · rw [show reg s6.data .r9 = _ from hm6.regs .r9 _ hr934]
      simp only [Sym.eval]
      rw [load_ofMachine (o := 16) rfl hM5.f16, UInt64.toNat_toBitVec,
        toNat_toUInt64 (by have := hM5.lw64; omega)]
    · rw [show reg s6.data .r15 = _ from hm6.regs .r15 _ h1534]
      exact load_ofMachine (o := 48) rfl hb5.out
  · simp only [hlast, decide_false, Bool.not_false, ↓reduceIte] at hpc5
    refine .done _ (.inr (.inl ⟨_, _, c', hpc5.trans (hp.label NativeRustcVmX64.Vm.PhaseM.label_22_at), hb5, hM5,
      hacc, hmod', by omega, le_trans (parentsOf_length_le ns sl) hnsl, hsb5,
      by rw [show 4096 + 10240 * ((l + 1) % 2) = 4096 + 10240 * ((l + 1) % 2) from rfl]
         exact hnext5, hrd5, ebp, ebx, ?_, ?_, by rw [rk5 .r11 (by simp)]; exact h114, ?_⟩))
    · rw [rk5 .rdx (by simp), rk4 .rdx (by simp)]; exact hrdx
    · rw [show reg s5.data .rdi = _ from hm5.regs .rdi _ hdi33]
      show (BinOp.apply .add .W64 (BitVec.ofNat 64 10240) (reg s4.data .rdi)).toNat = _
      simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, hdi4]
      omega
    · rw [show reg s5.data .r13 = _ from hm5.regs .r13 _ h1333]
      show (BinOp.apply .add .W64 (reg s4.data .r13) (BitVec.ofNat 64 1)).toNat = _
      simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, e13']
      omega

/-- **A level of the climb.** -/
theorem climb_step (hp : Placed code k) (G : Geo m0 bp B.length)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c)
    (hcl : Spec (Labels.label NativeRustcVmX64.Vm.ClimbLevel.entryLabel) ClimbLevelPre ClimbLevelPost) {count : Nat}
    {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 l : Nat}
    {acc : List (List (Nat × Digest))} {ns : List (Nat × Digest)} {cl : Nat} {st : MachineState}
    (h : ClimbSt m0 bp B c k count qs height lw rows c6 l acc ns cl st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (∃ acc' ns' cl', ClimbSt m0 bp B c k count qs height lw rows c6 (l + 1) acc' ns' cl' st') ∨
      ∃ sl cf, Pre36 m0 bp B c k count qs height lw rows c6 sl cf st') st :=
  Eventually.bind (climb_args hp G h) fun _ h' ↦
    Eventually.bind (climb_res G hcl h') fun _ h'' ↦ climb_tail hp G hR0 h''

/-- **The climb.** -/
theorem climb_run (hp : Placed code k) (G : Geo m0 bp B.length)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c)
    (hcl : Spec (Labels.label NativeRustcVmX64.Vm.ClimbLevel.entryLabel) ClimbLevelPre ClimbLevelPost) {count : Nat}
    {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 : Nat} {st : MachineState}
    (h : Climb0 m0 bp B c k count qs height lw rows c6 st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ sl cf, Pre36 m0 bp B c k count qs height lw rows c6 sl cf st') st := by
  refine Eventually.bind (climb_entry hp G h) fun s0 h0 ↦ ?_
  rcases h0 with h0 | h0
  · exact .done _ (.inr h0)
  exact Sym.loop (tr := step1 Host.exe)
    (fun n st ↦ ∃ l acc ns cl, n = height - l ∧
      ClimbSt m0 bp B c k count qs height lw rows c6 l acc ns cl st)
    (fun _ _ ⟨l, acc, ns, cl, hn, hl⟩ ↦ Eventually.mono (climb_step hp G hR0 hcl hl) fun _ h' ↦ by
      rcases h' with h' | ⟨acc', ns', cl', h'⟩ | h'
      · exact .inl (.inl h')
      · exact .inr ⟨_, by have := hl.ll; omega, l + 1, acc', ns', cl', rfl, h'⟩
      · exact .inl (.inr h'))
    ⟨0, [], _, c6, rfl, h0⟩

end

end NativeRustcVmX64.Wire.PhaseM
