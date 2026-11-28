module

public import NativeRustcVmX64.Tables.TableTerms.Blocks
public import NativeRustcVmX64.Code.Vm.TableTerms.Names

/-!
# `table_terms`: the entry (x86-64)

`b0` pushes RBP to RBX, stores the arguments in the frame (`out` at `8`, the evaluations' entries
at `16`, the powers at `24`, `32`, the point at `40`, `48`, the `TState` at `56`), points R13 at
table `0`'s third form's terms, R14 + RBP at `TABLES`' byte `16`, and clears the running sum and
the cursor: the loop head before table `0` (`entry`). Then the labels' addresses.
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableTerms.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.TableTerms.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableTerms.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b1Offset) :=
  hp.label NativeRustcVmX64.Vm.TableTerms.label_1_at
theorem lbl_6 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableTerms.label_6 = Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b15Offset) :=
  hp.label NativeRustcVmX64.Vm.TableTerms.label_6_at
theorem lbl_7 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.TableTerms.label_7 = Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b16Offset) :=
  hp.label NativeRustcVmX64.Vm.TableTerms.label_7_at

theorem addr_eq {i j : Nat} (h : i = j) : Host.addrOf i = Host.addrOf j := by rw [h]

/-- A machine state at an address. -/
theorem at_pc {st : MachineState} {pc : Int64} (h : st.pc = pc) {R : MachineState → Prop}
    (H : Eventually (step1 Host.exe) R ⟨st.data, pc⟩) : Eventually (step1 Host.exe) R st := by
  obtain ⟨d, q⟩ := st
  simp only at h
  subst h
  exact H

/-- An argument word the entry loads: stack argument `j`. -/
theorem ld_arg {ret : BitVec 64} {j : Nat} :
    (Sym.load 1 (8 * j) 8).eval (E m0 m0 [(argA m0, 32)] ret) = stackArg m0 j := by
  show (E m0 m0 [(argA m0, 32)] ret).load 1 (8 * j) 8 = _
  rw [load_eq_wordOf]
  show (wordOf m0.dmem (rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * j))).toBitVec = _
  rw [NativeRustcVm.addr_add_add]
  rfl

/-- **The entry**: `b0`, to the loop head before table `0`. -/
theorem entry (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    {R : MachineState → Prop}
    (cont : ∀ d, Head a s heights forms m0 0 (0, 0, #[]) s d →
      Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b1Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b0Offset)⟩ := by
  have hS := Pre.stack h
  have hwf : (E m0 m0 [(argA m0, 32)] 0).WF := wf_args h (fun _ h ↦ h)
  have hal : ∀ o : Nat, (Sym.ptr 0 ((280 + o : Nat) : Int)).eval (E m0 m0 [(argA m0, 32)] 0) =
      (E m0 m0 [(argA m0, 32)] 0).base 1 + BitVec.ofInt 64 (o : Int) := by
    intro o
    rw [eval_ptr0, show 280 + o = 272 + (8 + o) by omega, frame_add]
    show _ = rspOf m0 + 8#64 + BitVec.ofInt 64 (o : Int)
    rw [BitVec.ofInt_natCast, NativeRustcVm.addr_add_add]
  have hm : Match (E m0 m0 [(argA m0, 32)] 0) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial
      ⟨hal 8, hal 24, trivial⟩
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf nofun hm
    fun st hm' hpc ↦ ?_
  obtain ⟨hpro, hW, w8, w16, w24, w32, w40, w48, w56, r13, r14, rbp, rax, rcx, rdx, r15⟩ := ok_b0
  have hin := writesIn_of_pro hpro
  have hbr := belowRet_of_pro hpro
  have hfr : Frame m0 272 slots 8 st.data :=
    Frame.of_prologue Frame.entry hwf hm' hpro (fun p hp ↦ (slots_le p hp).2) slots_cs
  have hs0 := same_block hwf hm' hin hbr hW (X := fun _ ↦ False) (fun _ h ↦ nomatch h)
  have hFst : ∀ q, NativeRustcVm.InRange (stackBelow m0 272) 272 q →
      NativeRustcVm.InRange (stackBelow m0 N) N q :=
    fun q hq ↦ inRange_frame_stack hS.2.1 hS.1 (by rw [N_eq]; omega) hq
  have hs : NativeRustcVm.SameOutside m0.dmem st.data.dmem
      (fun q ↦ outs m0 q ∨ NativeRustcVm.InRange (stackBelow m0 N) N q) :=
    NativeRustcVm.SameOutside.mono hs0 fun q hq ↦ hq.elim (fun h ↦ .inr (hFst q h)) False.elim
  have c := ctx h
  simp only [PcOk] at hpc
  refine at_pc (hpc.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableTerms.b0_next))) (cont st.data ?_)
  have rg : ∀ {r : Reg64} {v : Sym}, (after b0 entryS).reg r = some v →
      reg st.data r = v.eval (E m0 m0 [(argA m0, 32)] 0) := fun hv ↦ hm'.regs _ _ hv
  refine ⟨⟨hfr, hs⟩, ?_, ?_, (rg r14).trans rfl, (rg rbp).trans rfl, ?_, (rg rax).trans rfl,
    (rg r15).trans rfl, (rg rdx).trans rfl, (rg rcx).trans rfl, rfl, rfl, rfl, ?_,
    fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩
  · intro p hp
    simp only [cws, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact wroteW hm' (by omega) w8 rfl
    · exact wroteW hm' (by omega) w24 rfl
    · exact wroteW hm' (by omega) w32 rfl
    · exact wroteW hm' (by omega) w40 rfl
    · exact wroteW hm' (by omega) w48 rfl
    · exact wroteW hm' (by omega) w56 rfl
  · refine wroteW hm' (by omega) w16 ?_
    show _ = stackArg m0 3 + BitVec.ofNat 64 (1968 * 0)
    rw [Nat.mul_zero, NativeRustcVm.addr_add_zero, ← ld_arg]
  · rw [rg r13]
    show BinOp.apply .add .W64 ((Sym.load 1 (8 * 1) 8).eval (E m0 m0 [(argA m0, 32)] 0))
      (BitVec.ofNat 64 11864) = _
    rw [ld_arg]
    simp only [BinOp.apply, low_W64, ext_W64]
  · exact (Pre.ts h).frame (hm'.kept hwf) (fun q hq ↦ c.stack_not_t (hq.elim (hFst q) False.elim))
      hs0

end

end NativeRustcVmX64.Tables.TableTerms
