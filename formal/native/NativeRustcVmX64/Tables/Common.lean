module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Sumcheck.Common

/-!
# The tables' proofs: what they share (x86-64)

`Body.call`: `Arrays.Body.call_mul` for any callee whose contract keeps the callee-saved
registers and changes memory only in the body's outputs and its own stack: from a body, a block
ending in the call, the callee returns to a body with the block's frame bytes kept.
-/

namespace NativeRustcVmX64.Tables

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Arrays
open NativeRustcVmX64.Field (frameEnv)

public section

/-- A body changing nothing but the stack changes nothing but the stack and an output. -/
theorem Body.widen {m0 st : MachineData} {F S : Nat} {slots : List (Nat × Reg64)} {oa : BitVec 64}
    {on : Nat} (h : Body m0 F S slots 0 0 st) : Body m0 F S slots oa on st :=
  ⟨h.rsp, h.frame, h.regs, fun p hp ↦ h.same p fun h' ↦ hp (h'.elim (fun h0 ↦
    absurd h0 (not_inRange_zero p)) Or.inr), h.kept⟩

/-- **A block ending in a call, and the call**: from a body, a block that writes only the frame
(region 0) below offset `L`, keeps the free callee-saved registers and leaves RSP at offset `0`
calls a function whose contract (`P`, `Q`) changes memory only in the body's outputs and its `Nc`
bytes of stack and keeps the callee-saved registers; it returns to a body, the callee-saved
registers and the frame the block's. -/
theorem Body.call [Host] {l : Label} {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : Spec (Labels.label l) P Q)
    {m0 st : MachineData} {F S L Nc : Nat} {slots : List (Nat × Reg64)} {oa : BitVec 64} {on : Nat}
    {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S₀ S₁ : SState} {st1 : MachineState} {next : Int64} {R : MachineState → Prop}
    (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S) (hle : F + Nc ≤ S)
    (hF8 : L ≤ F) (hslots : ∀ p ∈ slots, L ≤ p.1 ∧ p.1 + 8 ≤ F)
    (hout : ∀ p, InRange oa on p → ¬InRange (stackBelow m0 F) (F + 8) p)
    (hwf : (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret).WF)
    (hm₀ : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₀ st)
    (hm : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ st1.data)
    (hpc : PcOk (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) (.call l) next st1)
    (hk : keepsRegs S₀ S₁ (freeRegs slots) = true)
    (hsp : S₁.reg .rsp = some (.ptr 0 0)) (hw : ∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ L)
    (hP : StackOk st1.data Nc → P st1.data)
    (hQ : ∀ m', Q st1.data m' → SameOutside st1.data.dmem m'.dmem
      (fun p ↦ InRange oa on p ∨ InRange (stackBelow st1.data Nc) Nc p) ∧ Saved st1.data m')
    (cont : ∀ st2 : MachineState, st2.pc = next → Body m0 F S slots oa on st2.data →
      Q st1.data st2.data →
      (∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r) →
      (∀ j < F + 8, st2.data.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 j) =
        st1.data.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 j)) →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st1 := by
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hr0 := (rspOf m0).isLt
  have hfb : (stackBelow m0 F).toNat = (rspOf m0).toNat - F := stackBelow_toNat (by omega)
  have hrsp1 : rspOf st1.data = stackBelow m0 F := by
    show st1.data.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    simp [Sym.eval]
  have hk1 : Kept m0.dmem st1.data.dmem := fun p h ↦ hm.kept hwf p (hb.kept p h)
  have hwr : ∀ p, Written (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ p →
      InRange (stackBelow m0 F) L p := fun p h ↦ written_region0 rfl hwf (by omega) hw h
  have hpre : P st1.data := by
    refine hP ⟨by rw [hrsp1, hfb]; omega, by rw [hrsp1, hfb]; omega, fun i hi ↦ ?_⟩
    rw [hrsp1]
    have := hk1 _ (hS.2.2 (S - F - Nc + i) (by omega))
    rwa [show rspOf m0 - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - F - Nc + i) =
      stackBelow m0 F - BitVec.ofNat 64 Nc + BitVec.ofNat 64 i by
        unfold stackBelow
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (show S < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show F < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show Nc < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show S - F - Nc + i < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
        omega] at this
  refine call_then hpc hspec hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hsame, hsaved⟩ := hQ _ hpost
  have hcallee : ∀ p, InRange (stackBelow st1.data Nc) Nc p →
      InRange (stackBelow m0 S) S p := fun p h ↦ by
    unfold stackBelow at h
    rw [hrsp1] at h
    exact inRange_stack (n := Nc) (k := 0) hS1 hle (Nat.zero_le _) (by simpa using h)
  have hblock : ∀ p, InRange (stackBelow m0 F) L p → InRange (stackBelow m0 S) S p := fun p h ↦
    inRange_stack (F := F) (n := 0) (k := L) hS1 (by omega) hF8 (by simpa using h)
  have hfr : ∀ j < F + 8, st2.data.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 j) =
      st1.data.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 j) := fun j hj ↦ by
    refine hsame _ fun h ↦ h.elim (fun h ↦ hout _ h ?_) fun h ↦ ?_
    · rw [Sym.inRange_iff (by omega), toNat_add_ofNat _ _ (by omega)]
      omega
    · unfold stackBelow at h
      rw [hrsp1] at h
      exact not_inRange_below (by omega) (by omega) h
  refine cont st2 hpc2 ⟨?_, fun p hp i hi ↦ ?_, fun r hr hn ↦ ?_, fun p hp ↦ ?_,
    fun p h ↦ hsaved.2 p (hk1 p h)⟩ hpost hsaved.1 hfr
  · rw [hrsp2, hrsp1]; rfl
  · simp only [List.length_map, List.length_range] at hi
    obtain ⟨h8, hF⟩ := hslots p hp
    show st2.data.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i) = _
    rw [addr_add, hfr _ (by omega), hm.get?_mem0 hwf ?_]
    · rw [← addr_add]; exact hb.frame p hp i hi
    · exact fun h ↦ not_inRange_above (k := L) (by omega) (by omega) (hwr _ h)
  · exact (hsaved.1 r hr).trans ((regs_eq_of hm₀ hm hk r (free_mem hr hn)).trans
      (hb.regs r hr hn))
  · rw [hsame p fun h ↦ h.elim (fun h ↦ hp (Or.inl h)) fun h ↦ hp (Or.inr (hcallee p h)),
      hm.get?_mem0 hwf fun h ↦ hp (Or.inr (hblock p (hwr p h)))]
    exact hb.same p hp

/-- A body in a state with the same callee-saved registers, RSP and memory. -/
theorem Body.congr {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × Reg64)}
    {oa : BitVec 64} {on : Nat} (h : Body m0 F S slots oa on st)
    (hr : ∀ r, calleeSaved r = true → reg st' r = reg st r) (hsp : rspOf st' = rspOf st)
    (hd : st'.dmem = st.dmem) : Body m0 F S slots oa on st' :=
  ⟨hsp.trans h.rsp, by rw [hd]; exact h.frame, fun r hc hn ↦ (hr r hc).trans (h.regs r hc hn),
    fun p hp ↦ by rw [hd]; exact h.same p hp, by rw [hd]; exact h.kept⟩

/-- The `n` bytes from `x`, apart from the `N` bytes below the entry's RSP and its return address,
are apart from the `Nc` bytes below a callee's RSP `F` below the entry's and its return address. -/
theorem offStack_callee {m0 st : MachineData} {N F Nc : Nat} (hS : StackOk m0 N)
    {x : BitVec 64} {n : Nat} (hO : OffStack m0 x n N) (hrsp : rspOf st = stackBelow m0 F)
    (hle : F + Nc ≤ N) : OffStack st x n Nc := by
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hr := (rspOf m0).isLt
  unfold OffStack Apart at hO ⊢
  have e1 : (stackBelow st Nc).toNat = (rspOf m0).toNat - F - Nc := by
    have hF : (stackBelow m0 F).toNat = (rspOf m0).toNat - F := stackBelow_toNat (by omega)
    unfold stackBelow
    rw [hrsp, NativeRustcVm.toNat_sub_ofNat (by omega), hF]
  rw [e1]
  rw [stackBelow_toNat hS1] at hO
  omega

/-- A range off the stack misses a frame of `F ≤ N` bytes below RSP and the return address. -/
theorem not_frame {m0 : MachineData} {N F : Nat} (hS : StackOk m0 N) (hF : F ≤ N)
    {x : BitVec 64} {n : Nat} (hnw : NoWrap x n) (hO : OffStack m0 x n N) {p : BitVec 64}
    (hp : InRange x n p) : ¬InRange (stackBelow m0 F) (F + 8) p := by
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hr := (rspOf m0).isLt
  refine NativeRustcVm.Apart.not_inRange ?_ hnw ?_ hp
  · unfold OffStack Apart at hO
    unfold NativeRustcVm.Apart
    rw [stackBelow_toNat (by omega)]
    rw [stackBelow_toNat hS1] at hO
    omega
  · unfold NativeRustcVm.NoWrap; rw [stackBelow_toNat (by omega)]; omega

/-- Every register its atom but those of `rs`: the others kept. -/
theorem keptBut_reg [Labels] {st st' : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S : SState} {rs : List Reg64} (hm : Match (Env.ofMachine st [] vars ret) S st')
    (h : (allRegs.all fun r ↦ rs.any (· == r) || S.reg r == some (.reg r)) = true) {r : Reg64}
    (hr : r ∉ rs) : reg st' r = reg st r := by
  rw [List.all_eq_true] at h
  have := h r (mem_allRegs r)
  have hany : rs.any (· == r) = false := by
    rw [List.any_eq_false]
    intro x hx he
    exact hr (Reg64.eq_of_beq he ▸ hx)
  rw [hany, Bool.false_or, beq_iff_eq] at this
  exact hm.regs r _ this

end

end NativeRustcVmX64.Tables
