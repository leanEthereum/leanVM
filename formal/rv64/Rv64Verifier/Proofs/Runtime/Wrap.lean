import Rv64Verifier.Proofs.Runtime.Inv

/-!
# The `mem*` symbols

`memcpy` (`0x800126e4`), `memmove` (`0x800126ec`) and `memset` (`0x800126f4`) are two words,
`auipc t1` and `jalr zero, t1`: a jump to `compiler_builtins`' function, `ra` untouched. Their
contracts are the functions' (`wrap`): the jump changes `t1` and the pc alone.
-/

namespace Rv64Verifier.Runtime.Wrap
open RiscvZkvm.Rv64 Rv64Verifier.Sym

def others : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

/-- The jump to `target`. -/
def wrapE (target : Word) : Expect where
  steps := 2
  pc := .c target
  regs := others.map fun r ↦ (r, .reg r)
  mem := []
  writes := []
  obl := []

/-- `c` is `s` but for `t1` and the pc. -/
structure Agree (s c : MachineState) : Prop where
  reg : ∀ r, r ≠ .x6 → c.getReg r = s.getReg r
  mem : ∀ a, c.getMem a = s.getMem a

theorem Agree.byteAt {s c : MachineState} (h : Agree s c) (a : Word) : byteAt c a = byteAt s a := by
  simp only [byteAt_eq, h.mem]

theorem Agree.bytesAt {s c : MachineState} (h : Agree s c) (a : Word) (n : Nat) :
    bytesAt c a n = bytesAt s a n :=
  bytesAt_eq_iff.mpr fun _ _ ↦ h.byteAt _

theorem Agree.stackLo {s c : MachineState} (h : Agree s c) (n : Nat) :
    Rv64Verifier.stackLo c n = Rv64Verifier.stackLo s n := by
  simp only [Rv64Verifier.stackLo, h.reg .x2 (by decide)]

theorem Agree.frame {s c t : MachineState} {w : Word → Prop} (h : Agree s c) (hf : ByteFrame c t w) :
    ByteFrame s t w :=
  ⟨fun a ha ↦ (hf.byte a ha).trans (h.byteAt a), fun a ha ↦ (hf.unaligned a ha).trans (h.mem a)⟩

/-- A jump's contract is its target's, given that the contract does not see `t1` and the pc. -/
theorem wrap {e target : Word} {P : MachineState → Prop} {Q : MachineState → MachineState → Prop}
    (hw : Spec e (wrapE target)) (h : FunSpec Image.code target P Q)
    (hP : ∀ s c, Agree s c → P s → P c) (hQ : ∀ s c t, Agree s c → Q c t → Q s t) :
    FunSpec Image.code e P Q := by
  intro s hpc hpre
  obtain ⟨c, hr, hc⟩ := hw.reaches hpc trivial
  have hag : Agree s c := ⟨fun r hr' ↦ by
      by_cases h0 : r = .x0
      · subst h0; rfl
      exact hc.2.1 (r, .reg r) (List.mem_map.mpr ⟨r, by cases r <;> simp_all [others], rfl⟩),
    fun a ↦ hc.frame a (by simp [wrapE])⟩
  obtain ⟨t, ht, hout⟩ := h.call hr hc.pc (hP s c hag hpre)
  refine ⟨t, ht, ?_⟩
  rcases hout with ⟨hpc', hpres, hq⟩ | hd
  · refine Or.inl ⟨?_, fun r hr' ↦ ?_, hQ s c t hag hq⟩
    · rw [hpc', returnAddress, returnAddress, hag.reg .x1 (by decide)]
    · rw [hpres r hr', hag.reg r (by revert hr'; decide +revert)]
  · exact Or.inr hd

theorem memset_wrap (h : MemsetSpec 0x800121f4) : MemsetSpec 0x800126f4 := by
  refine wrap (spec_of 18877 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)) h
    (fun s c hag hp ↦ ?_) fun s c t hag hq ↦ ?_
  · show Mapped _ _
    rw [hag.reg .x10 (by decide), hag.reg .x12 (by decide)]; exact hp
  · obtain ⟨h1, h2, h3⟩ := hq
    rw [hag.reg .x10 (by decide), hag.reg .x11 (by decide), hag.reg .x12 (by decide)] at *
    exact ⟨h1, h2, hag.frame h3⟩

theorem copy_post {s c t : MachineState} (hag : Agree s c) (hq : MemcpyPost c t) :
    MemcpyPost s t := by
  obtain ⟨h1, h2, h3⟩ := hq
  rw [hag.reg .x10 (by decide), hag.reg .x11 (by decide), hag.reg .x12 (by decide),
    hag.bytesAt, hag.stackLo] at *
  exact ⟨h1, h2, hag.frame h3⟩

theorem stackOk {s c : MachineState} (hag : Agree s c) {n : Nat} (h : StackOk s n) : StackOk c n :=
  ⟨by rw [hag.stackLo]; exact h.valid, by rw [hag.reg .x2 (by decide)]; exact h.aligned⟩

theorem memcpy_wrap (h : MemcpySpec 0x80011ff8) : MemcpySpec 0x800126e4 := by
  refine wrap (spec_of 18873 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)) h
    (fun s c hag hp ↦ ?_) fun s c t hag hq ↦ copy_post hag hq
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  refine ⟨?_, ?_, ?_, stackOk hag h4, ?_, ?_⟩ <;>
    simp only [hag.reg .x10 (by decide), hag.reg .x11 (by decide), hag.reg .x12 (by decide),
      hag.stackLo] <;> assumption

theorem memmove_wrap (h : MemmoveSpec 0x8001228c) : MemmoveSpec 0x800126ec := by
  refine wrap (spec_of 18875 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide)) h
    (fun s c hag hp ↦ ?_) fun s c t hag hq ↦ copy_post hag hq
  obtain ⟨h1, h2, h4, h5, h6⟩ := hp
  refine ⟨?_, ?_, stackOk hag h4, ?_, ?_⟩ <;>
    simp only [hag.reg .x10 (by decide), hag.reg .x11 (by decide), hag.reg .x12 (by decide),
      hag.stackLo] <;> assumption

end Rv64Verifier.Runtime.Wrap
