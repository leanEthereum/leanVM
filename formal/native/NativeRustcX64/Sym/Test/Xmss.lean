module

public import NativeRustcX64.Code.Common.Memset.Names

public import NativeRustcX64.Sym
public import NativeRustcX64.Code.Xmss.XmssVerify
public meta import NativeRustcX64.Code.Xmss.XmssVerify

/-!
# The executor on `xmss_verify`'s first blocks

Its first block (`NativeRustcX64.Xmss.XmssVerify.b0`: the callee-saved registers pushed, the
5736-byte frame allocated with a stack probe `movq $0, (%rsp)`, `memset`'s arguments in 32-bit
registers, a GOT-indirect `callq`) and its second (`b1`: 64-bit loads from the signature, stack stores,
a 32-bit `movl` to a register and to memory). Region 0 is the stack from the `call`'s return-address
slot up to the entry's return address (5800 bytes, RSP at entry at offset 5792), region 1 the
signature RDI points to, and region 2 the memset GOT slot.
-/

namespace NativeRustcX64.Sym.Test.Xmss

set_option Elab.async false

open NativeRustcX64.Xmss.XmssVerify

/-- At entry: RSP at offset 5792 of the stack, RDI the signature, and the memset slot initialized. -/
def atEntry : SState :=
  (init [5800, 2400, 8] [(.rsp, .ptr 0 5792), (.rdi, .ptr 1 0)] [] []
    [(.gotSlot "memset", 2, 0)]).withKnownBytes 2 0 8 (.label "memset")

sym_block entry_exec := exec b0 atEntry

/-- After `memset` returns: RSP 8 bytes into the stack, R14 the signature. -/
def atReturn : SState := init [5800, 2400] [(.rsp, .ptr 0 8), (.r14, .ptr 1 0)]

sym_block afterMemset_exec := exec b1 atReturn

/-- The second block reads the signature's words at 1024 to 1088 and stores some on the stack;
the low half of the word at 1088 is stored at `928(%rsp)`. -/
example : (exec b1 atReturn).map (fun r => (r.1.reg .r13, r.1.reg .rbp, r.2)) =
    some (some (.load 1 1088 8), some (.un .trunc .W32 (.load 1 1088 8)), .fall) := by
  rw [afterMemset_exec]
  rfl

/-- The prologue calls `memset` with the return address after the block at RSP, RDI the frame at
offset 940, ESI zero, EDX 2400; R14 the signature; the entry's RBX saved below its return
address and the entry's return address kept. -/
theorem entry_spec [Host] {k : Nat} (hk : b0.IsInfixAt Host.prog k) {env : Env}
    (hwf : env.WF) (hret : env.ret = (Host.addrOf (k + b0.length)).toBitVec) {m : MachineData}
    (hm : Match env atEntry m) :
    Eventually (step1 Host.exe) (fun st => st.pc = Labels.label NativeRustcX64.Common.Memset.entryLabel ∧
      retOf st.data = Host.addrOf (k + b0.length) ∧
      st.data.regs.get64 .rdi = env.base 0 + 940#64 ∧
      st.data.regs.get64 .rsi = 0#64 ∧
      st.data.regs.get64 .rdx = 2400#64 ∧
      st.data.regs.get64 .rsp = env.base 0 ∧
      st.data.regs.get64 .r14 = env.base 1 ∧
      Mem.loadInt st.data.dmem (env.base 0 + 5744#64) 8 = some ((env.regs .rbx).toNat : Int) ∧
      Mem.loadInt st.data.dmem (env.base 0 + 5792#64) 8 = some ((env.load 0 5792 8).toNat : Int))
      ⟨m, Host.addrOf k⟩ := by
  refine NativeRustcX64.Eventually.mono
    (exec_sound hk entry_exec hwf (fun _ _ => hret) hm) fun st ⟨hm', hpc⟩ =>
    ⟨hpc.1, hpc.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm'.regs .rdi _ rfl]
    rfl
  · rw [hm'.regs .rsi _ rfl]
    rfl
  · rw [hm'.regs .rdx _ rfl]
    rfl
  · rw [hm'.regs .rsp _ rfl]
    simp [Sym.eval]
  · rw [hm'.regs .r14 _ rfl]
    simp [Sym.eval]
  · rw [hm'.read hwf (r := 0) (o := 5744) (n := 8) rfl (by decide) (by decide)]
    rfl
  · rw [hm'.read hwf (r := 0) (o := 5792) (n := 8) rfl (by decide) (by decide)]
    rfl

end NativeRustcX64.Sym.Test.Xmss
