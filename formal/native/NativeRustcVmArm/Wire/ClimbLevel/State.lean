module

public import NativeRustcVmArm.Wire.ClimbLevel.Basic

/-!
# `climb_level`'s states

The places from the precondition (`geo_of`). The registers the set-up fixes (`Fix`); the memory
after `i` nodes (`Done`: the siblings `sibsM` read so far, the reader past them, their siblings
and parents written); the loop's head (`Head`, `b5`); node `i`'s step (`Cur`), its scan for the
sibling (`Scan`, `b7`), the sibling written (`Mid`, before the parent's hash).
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

variable (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c : Nat) (ns : List (Nat × Digest))

/-- The registers the set-up fixes: the siblings, `40 n`, the read digest's place, the nodes'
end, the nodes' address less 40. -/
structure Fix (m : MachineData) : Prop where
  x22 : (m.regs.getXReg .X22).toBitVec = sibs m0
  x25 : (m.regs.getXReg .X25).toNat = 40 * cnt m0
  x27 : (m.regs.getXReg .X27).toBitVec = base m0 224 + BitVec.ofNat 64 24
  x28 : (m.regs.getXReg .X28).toBitVec = nd m0 (cnt m0)
  x29 : (m.regs.getXReg .X29).toBitVec + BitVec.ofNat 64 40 = nodes m0

/-- **The memory after `i` nodes**: their siblings read (`sibsM`), the reader past them, the
siblings and the parents written. -/
structure Done (i : Nat) (sl : List (Nat × Digest × Bool)) (ci : Nat) (d : Mem 64) : Prop where
  hs : sibsM B ns (ns.take i) c = some (sl, ci)
  rd : ReaderAt d (rdr m0) bp B ci
  sb : NodesAt d (sibs m0) (sl.map fun s ↦ (s.1, s.2.1))
  nx : NodesAt d (nxt m0) (parentsOf (ns.take i) sl)

/-- Node `i`'s step: its registers and the memory after the nodes before it. -/
structure Cur (i : Nat) (sl : List (Nat × Digest × Bool)) (ci : Nat) (m : MachineData) : Prop where
  fr : Frm m0 m
  fx : Fix m0 m
  dn : Done m0 bp B c ns i sl ci m.dmem
  lt : i < cnt m0
  x19 : (m.regs.getXReg .X19).toNat = (parentsOf (ns.take i) sl).length
  x20 : (m.regs.getXReg .X20).toNat = i + 1
  x23 : (m.regs.getXReg .X23).toBitVec = nd m0 (i + 1)
  x24 : (m.regs.getXReg .X24).toBitVec = nd m0 i
  x26 : (m.regs.getXReg .X26).toNat = i

/-- No node before `j` is node `i`'s sibling. -/
def Miss (i j : Nat) : Prop := ∀ j' (h : j' < j) (hj : j' < ns.length) (hi : i < ns.length),
  ns[j'].1 ≠ ns[i].1 ^^^ 1

/-- Node `i`'s sibling written (`q`, sibling `i`; its digest at SP+64): the parents not yet. -/
structure Mid (i : Nat) (sl : List (Nat × Digest × Bool)) (ci : Nat) (q : Nat × Digest × Bool)
    (m : MachineData) : Prop where
  fr : Frm m0 m
  fx : Fix m0 m
  lt : i < cnt m0
  hs : sibsM B ns (ns.take (i + 1)) c = some (sl ++ [q], ci)
  rd : ReaderAt m.dmem (rdr m0) bp B ci
  sb : NodesAt m.dmem (sibs m0) ((sl ++ [q]).map fun s ↦ (s.1, s.2.1))
  nx : NodesAt m.dmem (nxt m0) (parentsOf (ns.take i) sl)
  hl : sl.length = i
  key : ∀ h : i < ns.length, q.1 = ns[i].1
  dg : WordsAt m.dmem (base m0 224 + BitVec.ofNat 64 64) q.2.1.toList
  x19 : (m.regs.getXReg .X19).toNat = (parentsOf (ns.take i) sl).length
  x20 : (m.regs.getXReg .X20).toNat = i + 1
  x21 : (m.regs.getXReg .X21).toNat = q.1
  x23 : (m.regs.getXReg .X23).toBitVec = nd m0 (i + 1)
  x24 : (m.regs.getXReg .X24).toBitVec = nd m0 i

section
variable [Host] (k : Nat)

/-- **The loop's head** (`b5`) after `i` nodes. -/
structure Head (i : Nat) (sl : List (Nat × Digest × Bool)) (ci : Nat) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b5Offset)
  fr : Frm m0 st.data
  fx : Fix m0 st.data
  dn : Done m0 bp B c ns i sl ci st.data.dmem
  le : i ≤ cnt m0
  x19 : (st.data.regs.getXReg .X19).toNat = (parentsOf (ns.take i) sl).length
  x20 : (st.data.regs.getXReg .X20).toNat = i
  x23 : (st.data.regs.getXReg .X23).toBitVec = nd m0 i

/-- **The scan** (`b7`) for node `i`'s sibling, at node `j`. -/
structure Scan (i : Nat) (sl : List (Nat × Digest × Bool)) (ci j : Nat) (st : MachineState) :
    Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ClimbLevel.b7Offset)
  cur : Cur m0 bp B c ns i sl ci st.data
  le : j ≤ cnt m0
  x8 : (st.data.regs.getXReg .X8).toBitVec + BitVec.ofNat 64 40 = nd m0 j
  x9 : (st.data.regs.getXReg .X9).toNat = 40 * (cnt m0 - j)
  miss : Miss ns i j

end

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

/-- **The places** from the precondition. -/
theorem geo_of [Labels] (h : ClimbLevelPre m0) (hR : ReaderAt m0.dmem (rdr m0) bp B c) :
    Geo m0 bp B := by
  obtain ⟨hst, hrc, hn, ⟨hnm, hnnw⟩, ⟨hsm, hsnw⟩, ⟨hxm, hxnw⟩, bp', B', c', hR', hd⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := hR'.unique hR
  have hbN : (stackBelow m0 climbLevelStack).toNat = m0.regs.SP.toNat - climbLevelStack :=
    Ring.base_toNat hst.2.1
  have hsp := m0.regs.SP.toNat_lt
  have hrNw : (rdr m0).toNat + 24 ≤ 2 ^ 64 := hR.ok.2
  have hbNw : bp.toNat + B.length ≤ 2 ^ 64 := hR.noWrap
  have hnnw' : (nodes m0).toNat + 40 * cnt m0 ≤ 2 ^ 64 := hnnw
  have hsnw' : (sibs m0).toNat + 10240 ≤ 2 ^ 64 := hsnw
  have hxnw' : (nxt m0).toNat + 10240 ≤ 2 ^ 64 := hxnw
  have a02 : NativeRustcVm.Apart (stackBelow m0 climbLevelStack) climbLevelStack (rdr m0) 24 :=
    hd.apart (i := 0) (j := 2) (by simp) (by simp) (by decide)
  have a03 : NativeRustcVm.Apart (stackBelow m0 climbLevelStack) climbLevelStack bp B.length :=
    hd.apart (i := 0) (j := 3) (by simp) (by simp) (by decide)
  have a04 : NativeRustcVm.Apart (stackBelow m0 climbLevelStack) climbLevelStack (nodes m0)
      (40 * cnt m0) := hd.apart (i := 0) (j := 4) (by simp) (by simp) (by decide)
  have a05 : NativeRustcVm.Apart (stackBelow m0 climbLevelStack) climbLevelStack (sibs m0)
      nodesBytes := hd.apart (i := 0) (j := 5) (by simp) (by simp) (by decide)
  have a06 : NativeRustcVm.Apart (stackBelow m0 climbLevelStack) climbLevelStack (nxt m0)
      nodesBytes := hd.apart (i := 0) (j := 6) (by simp) (by simp) (by decide)
  have a12 : NativeRustcVm.Apart rcAddr 192 (rdr m0) 24 :=
    hd.apart (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have a15 : NativeRustcVm.Apart rcAddr 192 (sibs m0) nodesBytes :=
    hd.apart (i := 1) (j := 5) (by simp) (by simp) (by decide)
  have a16 : NativeRustcVm.Apart rcAddr 192 (nxt m0) nodesBytes :=
    hd.apart (i := 1) (j := 6) (by simp) (by simp) (by decide)
  have a23 : NativeRustcVm.Apart (rdr m0) 24 bp B.length :=
    hd.apart (i := 2) (j := 3) (by simp) (by simp) (by decide)
  have a24 : NativeRustcVm.Apart (rdr m0) 24 (nodes m0) (40 * cnt m0) :=
    hd.apart (i := 2) (j := 4) (by simp) (by simp) (by decide)
  have a25 : NativeRustcVm.Apart (rdr m0) 24 (sibs m0) nodesBytes :=
    hd.apart (i := 2) (j := 5) (by simp) (by simp) (by decide)
  have a26 : NativeRustcVm.Apart (rdr m0) 24 (nxt m0) nodesBytes :=
    hd.apart (i := 2) (j := 6) (by simp) (by simp) (by decide)
  have a34 : NativeRustcVm.Apart bp B.length (nodes m0) (40 * cnt m0) :=
    hd.apart (i := 3) (j := 4) (by simp) (by simp) (by decide)
  have a35 : NativeRustcVm.Apart bp B.length (sibs m0) nodesBytes :=
    hd.apart (i := 3) (j := 5) (by simp) (by simp) (by decide)
  have a36 : NativeRustcVm.Apart bp B.length (nxt m0) nodesBytes :=
    hd.apart (i := 3) (j := 6) (by simp) (by simp) (by decide)
  have a45 : NativeRustcVm.Apart (nodes m0) (40 * cnt m0) (sibs m0) nodesBytes :=
    hd.apart (i := 4) (j := 5) (by simp) (by simp) (by decide)
  have a46 : NativeRustcVm.Apart (nodes m0) (40 * cnt m0) (nxt m0) nodesBytes :=
    hd.apart (i := 4) (j := 6) (by simp) (by simp) (by decide)
  have a56 : NativeRustcVm.Apart (sibs m0) nodesBytes (nxt m0) nodesBytes :=
    hd.apart (i := 5) (j := 6) (by simp) (by simp) (by decide)
  have bNw : NativeRustcVm.NoWrap (base m0 climbLevelStack) climbLevelStack :=
    Ring.base_noWrap hst.2.1
  have sNw : NativeRustcVm.NoWrap (sibs m0) nodesBytes := hsnw
  have xNw : NativeRustcVm.NoWrap (nxt m0) nodesBytes := hxnw
  have hwS : ∀ q, W m0 q → ¬InRange (base m0 climbLevelStack) climbLevelStack q := by
    rintro q (hq | hq)
    · exact NativeRustcVm.Apart.not_inRange a05.symm sNw bNw hq
    · exact NativeRustcVm.Apart.not_inRange a06.symm xNw bNw hq
  have hwR : ∀ q, W m0 q → ¬InRange (rdr m0) 24 q := by
    rintro q (hq | hq)
    · exact NativeRustcVm.Apart.not_inRange a25.symm sNw hrNw hq
    · exact NativeRustcVm.Apart.not_inRange a26.symm xNw hrNw hq
  have hwB : ∀ q, W m0 q → ¬InRange bp B.length q := by
    rintro q (hq | hq)
    · exact NativeRustcVm.Apart.not_inRange a35.symm sNw hbNw hq
    · exact NativeRustcVm.Apart.not_inRange a36.symm xNw hbNw hq
  have hN := hst.2.1
  have st : ∀ {x n : Nat}, (m0.regs.SP.toNat - climbLevelStack + climbLevelStack ≤ x ∨
      x + n ≤ m0.regs.SP.toNat - climbLevelStack) →
      x + n ≤ m0.regs.SP.toNat - climbLevelStack ∨ m0.regs.SP.toNat ≤ x := fun h ↦ by omega
  unfold NativeRustcVm.Apart at a02 a03 a04 a05 a06 a12 a15 a16 a23 a24 a25 a26
  unfold NativeRustcVm.Apart at a34 a45 a46 a56
  unfold nodesBytes at a05 a06 a15 a16 a25 a26 a45 a46 a56
  rw [hbN] at a04 a05 a06
  exact ⟨⟨hst, hrNw, hbNw, a02, a03, a23, hwS, hwR, hwB⟩, hrc, hn, hnm, hsm, hxm, hnnw', hsnw',
    hxnw', st a04, st a05, st a06, a24.symm, a25.symm, a26.symm, a34.symm, a45, a46, a56, a12,
    a15, a16⟩

end

end NativeRustcVmArm.Wire.ClimbLevel
