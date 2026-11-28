module

public import NativeRustcX64.Sym

/-!
# Raw rustc x86 forms

Bit-test flags and widths, base-less effective addresses, symbolic GOT addresses and ordinary
memory contents, indirect calls and jumps, and rejection of unknown or overwritten targets.
-/

namespace NativeRustcX64.Sym.Test.Raw

abbrev ins {w : Width} (op : Operation w) : Directive := .instr (.regular .W64 w op)

abbrev got (l : Label) : AddrExpr :=
  ⟨some .rip, none, .sub (.gotSlot l) .after_current_instruction⟩

def start : SState :=
  (init [32, 8] [(.rsp, .ptr 0 32)] [] [] [(.gotSlot "f", 1, 0)]).withKnownBytes
    1 0 8 (.label "f")

/-- Initial knowledge is not an instruction write. -/
example : start.mem = [] := by rfl

/-- A fresh description cannot resurrect a target overwritten by an actual store. -/
example : ((start.store 1 0 8 (.lit 0)).withKnownBytes 1 0 8 (.label "f")).target
    (.mem (got "f")) = none := by decide +kernel

example : (stepOp (.bt (.low .rax .W16) (.reg (.low .rcx .W16)))
    (init [] [(.rax, .lit 2), (.rcx, .lit 17)])).map (fun x => x.1.flags) =
    some ⟨some (.lit true), some .flagZF, none, none⟩ := by decide +kernel

example : (stepOp (.bts (.low .rax .W16) (.imm (.int64 0x111)))
    (init [] [(.rax, .lit 0x10000)])).map (fun x => (x.1.reg .rax, x.1.flags.cf)) =
    some (some (.lit 0x10002), some (.lit false)) := by decide +kernel

example : (stepOp (.bts (.low .rax .W32) (.imm (.int64 63)))
    (init [] [(.rax, .lit 0x100000000)])).map (fun x => x.1.reg .rax) =
    some (some (.lit 0x80000000)) := by decide +kernel

example : (stepOp (.bts (.low .rax .W64) (.imm (.int64 63)))
    (init [] [(.rax, .lit 0)])).map (fun x => x.1.reg .rax) =
    some (some (.lit 0x8000000000000000)) := by decide +kernel

example : stepOp (.bt (.low .rax .W8) (.imm (.int64 0))) (init []) = none := by rfl
example : stepOp (.bts .ah (.reg .ah)) (init []) = none := by rfl

example : (exec [ins (.bt (.low .rax .W64) (.imm (.int64 1))),
    ins (.jcc .z "yes" : Operation .W64)] (init [])).map Prod.snd =
    some (.cond .flagZF "yes") := by decide +kernel

example : exec [ins (.bt (.low .rax .W64) (.imm (.int64 1))),
    ins (.jcc .o "unknown" : Operation .W64)] (init []) = none := by decide +kernel

example : (stepOp (.lea (.low .rax .W64) ⟨none, some ⟨.rcx, .W64⟩, .int64 16⟩)
    (init [] [(.rcx, .lit 3)])).map (fun x => x.1.reg .rax) =
    some (some (.lit 40)) := by decide +kernel

example : (stepOp (.lea (.low .rax .W64) ⟨none, none, .int64 (-8)⟩)
    (init [])).map (fun x => x.1.reg .rax) =
    some (some (.lit (2 ^ 64 - 8))) := by decide +kernel

example : (stepOp (.mov (.reg (.low .rax .W64)) (.imm (.gotSlot "f")))
    (init [])).map (fun x => x.1.reg .rax) = some (some (.gotSlot "f")) := by decide +kernel

example : (exec [ins (.mov (.reg (.low .r11 .W64)) (.regOrMem (.mem (got "f")))),
    ins (.call (.reg (.low .r11 .W64)) : Operation .W64)] start).map Prod.snd =
    some (.call "f") := by decide +kernel

example : (stepOp (.call (.mem (got "f")) : Operation .W64) start).map Prod.snd =
    some (.call "f") := by decide +kernel

example : (stepOp (.jmp (.mem (got "f")) : Operation .W64) start).map Prod.snd =
    some (.jump "f") := by decide +kernel

example : stepOp (.call (.reg (.low .r11 .W64)) : Operation .W64) start = none := by decide +kernel

example : stepOp (.jmp (.mem (got "f")) : Operation .W64)
    (init [8] [] [] [] [(.gotSlot "f", 0, 0)]) = none := by decide +kernel

example : exec [ins (.mov (.mem (got "f")) (.imm (.int64 0)) : Operation .W64),
    ins (.call (.mem (got "f")) : Operation .W64)] start = none := by decide +kernel

/-- Even a partial overwrite invalidates the original symbolic function address. -/
example : exec [ins (.mov (.mem (got "f")) (.imm (.int64 0)) : Operation .W8),
    ins (.call (.mem (got "f")) : Operation .W64)] start = none := by decide +kernel

/-- GOT contents are ordinary writable memory, not a privileged target oracle. -/
example : (exec [ins (.mov (.mem (got "f")) (.regOrMem (.reg (.low .rax .W64)))),
    ins (.jmp (.mem (got "f")) : Operation .W64)]
    (start.setReg .rax (some (.label "g")))).map Prod.snd = some (.jump "g") := by decide +kernel

/-- A call reads its indirect target before overwriting that stack slot with its return address. -/
example : (stepOp (.call (.mem ⟨some (.reg .rsp), none, .int64 (-8)⟩) : Operation .W64)
    ((init [32] [(.rsp, .ptr 0 32)]).withKnownBytes 0 24 8 (.label "f"))).map
    (fun x => (x.2, x.1.loadOne (.ptr 0 24) 8)) =
    some (.call "f", some .retAddr) := by decide +kernel

example [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r off : Nat} {l : Label}
    (h : ∀ i < 8, env.mem0.get? (env.base r + BitVec.ofNat 64 (off + i)) =
      some (byteOf (Labels.label l).toBitVec i)) :
    Match env (S.withKnownBytes r off 8 (.label l)) m := hm.withKnownBytes h

end NativeRustcX64.Sym.Test.Raw
