module

public import NativeRustcVmArm.KeccakGkr.VerifyLayer.Exec
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.Model
public import NativeRustcVmArm.Spec.KeccakGkr
public import NativeRustcVmArm.Bus.Common

/-!
# `verify_layer`: the body's context

The entry's arguments (`tA` the `TState`, `cA` the claim, `sA` the scratch), the body (`Body`: a
`Ring.Fr` of the 2032-byte frame, the twelve saved registers' slots at its top, memory as the
entry's but in the stack and the outputs `outs`: the frame's locals, the `TState`, the claim,
the scratch's `layerRegion`), the goal (`Goal`), the addresses as numbers (`Geo`, from the
precondition's `Areas`), a range kept by a change it misses (`same_of`), a call from the body
(`Body.call`), a block of the body that writes nothing (`Body.run0`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (tstateBytes)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)

@[expose] public section

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The claim. -/
abbrev cA (m0 : MachineData) : BitVec 64 := m0.regs.X3.toBitVec
/-- The scratch. -/
abbrev sA (m0 : MachineData) : BitVec 64 := m0.regs.X4.toBitVec

/-- The prologue's slots, at the frame's top. -/
def slots : List (Nat × XReg) :=
  [(1936, .X29), (1944, .X30), (1952, .X28), (1960, .X27), (1968, .X26), (1976, .X25),
    (1984, .X24), (1992, .X23), (2000, .X22), (2008, .X21), (2016, .X20), (2024, .X19)]

/-- What the body writes but its stack: the frame's locals, the `TState`, the claim, the
scratch's `layerRegion`. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (base m0 2032) 1936 q ∨ InRange (tA m0) tstateBytes q ∨ InRange (cA m0) claimBytes q ∨
    InRange (sA m0 + BitVec.ofNat 64 25600) 114688 q

/-- **The body.** -/
abbrev Body (m0 m : MachineData) : Prop := Fr m0 2032 verifyLayerStack slots [] (outs m0) m

/-- The layer's run. -/
abbrev runL (s : TState) (c : KeccakClaimW)
    (m0 : MachineData) : Option (KeccakClaimW × TState) :=
  (verifyKeccakLayer m0.regs.X1.toNat m0.regs.X2.toNat c).run s

/-- **The goal**: back at the caller, the postcondition. -/
def Goal [Labels] (a : NativeRustcVm.Transcript.DecArea) (s : TState) (c : KeccakClaimW)
    (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ VerifyLayerPost a s c m0 st.data

theorem stack_eq : verifyLayerStack = 3648 := by decide

/-- **The addresses as numbers.** -/
structure Geo (m0 : MachineData) : Prop where
  hN : 3648 ≤ m0.regs.SP.toNat
  hal : m0.regs.SP.toNat % 16 = 0
  ht : (tA m0).toNat + 760 ≤ 2 ^ 64
  hc : (cA m0).toNat + 768 ≤ 2 ^ 64
  hs : (sA m0).toNat + 205824 ≤ 2 ^ 64
  hts : (tA m0).toNat + 760 ≤ m0.regs.SP.toNat - 3648 ∨ m0.regs.SP.toNat ≤ (tA m0).toNat
  hcs : (cA m0).toNat + 768 ≤ m0.regs.SP.toNat - 3648 ∨ m0.regs.SP.toNat ≤ (cA m0).toNat
  hss : (sA m0).toNat + 205824 ≤ m0.regs.SP.toNat - 3648 ∨ m0.regs.SP.toNat ≤ (sA m0).toNat
  htc : (tA m0).toNat + 760 ≤ (cA m0).toNat ∨ (cA m0).toNat + 768 ≤ (tA m0).toNat
  htsc : (tA m0).toNat + 760 ≤ (sA m0).toNat ∨ (sA m0).toNat + 205824 ≤ (tA m0).toNat
  hcsc : (cA m0).toNat + 768 ≤ (sA m0).toNat ∨ (sA m0).toNat + 205824 ≤ (cA m0).toNat

theorem Geo.sp_lt (m0 : MachineData) : m0.regs.SP.toNat < 2 ^ 64 := m0.regs.SP.toBitVec.isLt

/-- The frame's base as a number. -/
theorem Geo.bN {m0 : MachineData}
    (g : Geo m0) : (base m0 2032).toNat = m0.regs.SP.toNat - 2032 :=
  base_toNat (by have := g.hN; omega)

/-- A frame address as a number. -/
theorem Geo.fa {m0 : MachineData}
    (g : Geo m0) {o : Nat} (ho : o ≤ 2032) :
    (base m0 2032 + BitVec.ofNat 64 o).toNat = m0.regs.SP.toNat - 2032 + o := by
  have := g.hN; have := Geo.sp_lt m0
  rw [NativeRustcVm.toNat_add_ofNat (by rw [g.bN]; omega), g.bN]

/-- An address of the scratch as a number. -/
theorem Geo.sa {m0 : MachineData}
    (g : Geo m0) {o : Nat} (ho : o < 205824) :
    (sA m0 + BitVec.ofNat 64 o).toNat = (sA m0).toNat + o := by
  have := g.hs
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]

/-- An address of the claim as a number. -/
theorem Geo.ca {m0 : MachineData}
    (g : Geo m0) {o : Nat} (ho : o < 768) :
    (cA m0 + BitVec.ofNat 64 o).toNat = (cA m0).toNat + o := by
  have := g.hc
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]

/-- The callee's stack below the body's SP, as a number. -/
theorem Geo.stk {m0 m : MachineData}
    (g : Geo m0) (hsp : m.regs.SP.toBitVec = base m0 2032) {n : Nat} (hn : n ≤ 1616) :
    (stackBelow m n).toNat = m0.regs.SP.toNat - 2032 - n := by
  have := g.hN
  rw [stackBelow_eq (m0 := m0) (F := 2032) hsp (N' := n) (by omega),
    base_toNat (m0 := m0) (F := 2032 + n) (by omega)]
  omega

end

public section

variable {a : NativeRustcVm.Transcript.DecArea} {s : TState} {c : KeccakClaimW}
  {m0 : MachineData}

theorem areas_ok {m : MachineData} {n : Nat} {ws rs : List Region} (h : Areas m n ws rs)
    {r : Region}
    (hr : r ∈ ws) : r.Ok m.dmem :=
  h.1 r (List.mem_append.mpr (.inl hr))

theorem areas_ws {m : MachineData} {n : Nat} {ws rs : List Region} (h : Areas m n ws rs)
    {i j : Nat} (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j) :
    Apart ws[i].addr ws[i].size ws[j].addr ws[j].size := by
  have h2 := NativeRustcVm.Disjoint.apart h.2.1 (i := i + 1) (j := j + 1) (by simp; omega)
    (by simp; omega) (by omega)
  simp only [List.getElem_cons_succ] at h2
  exact h2

theorem areas_stack {m : MachineData} {n : Nat} {ws rs : List Region} (h : Areas m n ws rs)
    {w : Region} (hw : w ∈ ws) : Apart w.addr w.size (stackBelow m n) n := by
  have h1 := h.2.1
  rw [stackRegion, NativeRustcVm.disjoint_cons_iff] at h1
  exact (h1.1 w hw).symm

/-- **The addresses of the precondition.** -/
theorem geo_of [Labels] (h : VerifyLayerPre a s c m0) : Geo m0 := by
  obtain ⟨hS, -, -, -, -, -, -, -, -, hA⟩ := h
  have hN : 3648 ≤ m0.regs.SP.toNat := by have := hS.2.1; rw [stack_eq] at this; exact this
  have hsb : (stackBelow m0 verifyLayerStack).toNat = m0.regs.SP.toNat - 3648 := by
    rw [stack_eq]; exact NativeRustcVm.toNat_sub_ofNat hN
  have ht := (areas_ok hA (r := ⟨tA m0, tstateBytes⟩) (by simp)).2
  have hc := (areas_ok hA (r := ⟨cA m0, claimBytes⟩) (by simp)).2
  have hs := (areas_ok hA (r := ⟨sA m0, NativeRustcVm.KeccakGkr.scratchBytes⟩) (by simp)).2
  have h1 := areas_stack hA (w := ⟨tA m0, tstateBytes⟩) (by simp)
  have h2 := areas_stack hA (w := ⟨cA m0, claimBytes⟩) (by simp)
  have h3 := areas_stack hA (w := ⟨sA m0, NativeRustcVm.KeccakGkr.scratchBytes⟩) (by simp)
  have h4 := areas_ws hA (i := 0) (j := 1) (by simp) (by simp) (by omega)
  have h5 := areas_ws hA (i := 0) (j := 2) (by simp) (by simp) (by omega)
  have h6 := areas_ws hA (i := 1) (j := 2) (by simp) (by simp) (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h4 h5 h6
  unfold NativeRustcVm.NoWrap at ht hc hs
  unfold Apart at h1 h2 h3
  unfold Apart at h4 h5 h6
  simp only [stack_eq, tstateBytes, claimBytes, NativeRustcVm.KeccakGkr.scratchBytes] at *
  exact ⟨hN, hS.1, ht, hc, hs, by omega, by omega, by omega, h4, h5, h6⟩

/-- **A byte outside a range**, as numbers. -/
theorem notIn {x b : BitVec 64} {n j : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (hb : b.toNat + j < 2 ^ 64) (h : b.toNat + j < x.toNat ∨ x.toNat + n ≤ b.toNat + j) :
    ¬InRange x n (b + BitVec.ofNat 64 j) := by
  rw [Sym.inRange_iff hx, NativeRustcVm.toNat_add_ofNat hb]
  omega

/-- The outputs miss the slots. -/
theorem outs_slot (g : Geo m0) {j : Nat} (hj1 : 1936 ≤ j) (hj2 : j < 2032) :
    ¬outs m0 (base m0 2032 + BitVec.ofNat 64 j) := by
  have := g.hN; have := Geo.sp_lt m0; have hb := g.bN
  have := g.ht; have := g.hc; have := g.hs; have := g.hts; have := g.hcs; have := g.hss
  have hbj : (base m0 2032).toNat + j < 2 ^ 64 := by omega
  rintro (h | h | h | h)
  · exact notIn (by rw [hb]; omega) hbj (by rw [hb]; omega) h
  · exact notIn (by simpa [tstateBytes] using g.ht) hbj (by simp only [tstateBytes]; omega) h
  · exact notIn (by simpa [claimBytes] using g.hc) hbj (by simp only [claimBytes]; omega) h
  · exact notIn (by rw [g.sa (by omega)]; omega) hbj (by rw [g.sa (by omega)]; omega) h

theorem slots_bound : ∀ p ∈ slots, 1936 ≤ p.1 ∧ p.1 + 8 ≤ 2032 := by decide

/-- **A call from the body** to a callee using `n` bytes of stack, writing outputs `W` of the
body's. -/
theorem Body.call {m m' : MachineData} (g : Geo m0) (h : Body m0 m) {n : Nat} (hn : n ≤ 1616)
    {W : BitVec 64 → Prop} (hS : Saved m m')
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m n) n q ∨ W q)
    (hW : ∀ q, W q → outs m0 q) : Body m0 m' := by
  have := g.hN; have := Geo.sp_lt m0; have hb := g.bN
  have hst := g.stk h.sp hn
  refine h.step hS.2.1 (fun r hr ↦ by cases hr) hS.2.2 hs (fun q hq ↦ ?_) ?_
  · rcases hq with hq | hq
    · left
      rw [Sym.inRange_iff (by rw [hst]; omega), hst] at hq
      rw [stack_eq, Sym.inRange_iff (by rw [base_toNat (by omega)]; omega), base_toNat (by omega)]
      omega
    · exact .inr (hW q hq)
  · intro p hp i hi hq
    have hp' := slots_bound p hp
    rw [NativeRustcVm.addr_add_add] at hq
    rcases hq with hq | hq
    · exact notIn (by rw [hst]; omega) (by rw [hb]; omega) (by rw [hst, hb]; omega) hq
    · exact outs_slot g (by omega) (by omega) (hW _ hq)

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
