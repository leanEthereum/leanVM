module

public import NativeRustcVmArm.Whir.VerifyStackedOpening.Tail

/-!
# `verify_stacked_opening`'s exits

From a state of the frame with any outputs `O` (`OFr`): `exit_b37`, the epilogue keeps X0 and the
memory and restores the entry's registers and SP; `fail_b36`, `None` (X0 `0`), then the epilogue.
`post_of`: the postcondition from the exit's X0, the `TState`, the frame's footprint and the saved
registers.
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening

@[expose] public section

/-- The frame with outputs `O`. -/
abbrev OFr (m0 : MachineData) (O : BitVec 64 → Prop) (st : MachineData) : Prop :=
  Fr m0 512 verifyStackedOpeningStack slots [] O st

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData} {O : BitVec 64 → Prop}

omit [Host] in
/-- A frame with fewer outputs. -/
theorem Fr.mono_outs {F N : Nat} {sl : List (Nat × XReg)} {kp : List XReg}
    {O O' : BitVec 64 → Prop} {st : MachineData} (hf : Fr m0 F N sl kp O st)
    (hO : ∀ q, O q → O' q) : Fr m0 F N sl kp O' st :=
  ⟨hf.sp, hf.keep, hf.slots, NativeRustcVm.SameOutside.mono hf.same fun q hq ↦
    hq.elim .inl fun hq ↦ .inr (hO q hq),
    hf.kept⟩

omit [Host] in
/-- The frame alone, as an environment. -/
theorem Parts.frame_envO [Labels]
    (h : Parts a s layout target coefficients point slices cs z value m0)
    {st : MachineData} (hf : OFr m0 O st) :
    (Env.ofMachine st [(base m0 512, 512)]).WF ∧
      Match (Env.ofMachine st [(base m0 512, 512)]) frameS st := by
  have hstk := h.wt.1
  have hS := h.hS
  exact ⟨Env.wf_of ⟨⟨fun i hi ↦ hf.kept _ (Ring.frame_mapped hstk (by rw [stack_eq]; decide) i hi),
      base_noWrap (by omega)⟩, trivial⟩ (List.pairwise_singleton _ _),
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by rw [stack_eq]; decide) rfl, trivial⟩
      (by rw [hf.sp]; simp [Sym.eval]) trivial trivial trivial trivial⟩

/-- **The epilogue** `b37`: X0 and the memory kept, the entry's registers and SP restored. -/
theorem exit_b37 (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    {R : MachineState → Prop} {st : MachineData} (hf : OFr m0 O st)
    (cont : ∀ m', m'.regs.X0 = st.regs.X0 → m'.dmem = st.dmem → Saved m0 m' →
      R ⟨m', retOf m0⟩) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b37Offset)⟩ := by
  obtain ⟨hwf, hm⟩ := h.frame_envO hf
  have hk37 : b37.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b37Offset) := b37_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk37 run_b37 hwf hm fun st1 hm1 hpc1 ↦ Eventually.done _ ?_
  obtain ⟨hret, hsaved⟩ := Ring.Fr.exit hf hm1 hwf (by decide)
  have hpc : st1.pc = retOf m0 := hpc1.trans hret
  obtain ⟨d1, pc1⟩ := st1
  simp only at hpc
  subst hpc
  exact cont d1 ((rv hm1 (r := .X0) rfl).trans rfl) (hm1.dmem_eq hwf rfl) hsaved

/-- **`None`**: `b36` sets X0 to `0`, then the epilogue. -/
theorem fail_b36 (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    {R : MachineState → Prop} {st : MachineData} (hf : OFr m0 O st)
    (cont : ∀ m', m'.regs.X0 = 0 → m'.dmem = st.dmem → Saved m0 m' → R ⟨m', retOf m0⟩) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b36Offset)⟩ := by
  have hk36 : b36.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b36Offset) := b36_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine hf.regsBlock (st := ⟨st, _⟩) hk36 run_b36 rfl rfl rfl rfl
    fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hb : b36.length = NativeRustcVmArm.Vm.VerifyStackedOpening.b36Length := NativeRustcVmArm.Vm.VerifyStackedOpening.b36_length
  rw [hb] at hpc1
  obtain ⟨d1, pc1⟩ := st1
  simp only at hpc1
  subst hpc1
  have h0 : d1.regs.X0 = 0 := (rv hm1 (r := .X0) rfl).trans (by sym_simp; rfl)
  exact exit_b37 hp h hf1 fun m' e0 hd hs ↦ cont m' (e0.trans h0) (hd.trans hd1) hs

omit [Host] in
/-- **The postcondition** from the exit. -/
theorem post_of [Labels] {m' : MachineData}
    (h0 : m'.regs.X0 = okWord ((verifyStackedOpening layout.stackLog m0.regs.X2.toNat
      (stackClaims layout target point coefficients cs z value)).run s).isSome)
    (hn : NextAt m'.dmem (tA m0) a ((verifyStackedOpening layout.stackLog m0.regs.X2.toNat
      (stackClaims layout target point coefficients cs z value)).run s))
    (hs : SameOutside m0.dmem m'.dmem fun q ↦
      InRange (base m0 verifyStackedOpeningStack) verifyStackedOpeningStack q ∨ outsF m0 q)
    (hS : Saved m0 m') :
    VerifyStackedOpeningPost a s layout target coefficients point cs z value m0 m' := by
  refine ⟨h0, hn, NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hS⟩
  rcases hq with hq | hq | hq | hq
  · exact .inr hq
  · exact .inl ⟨_, List.mem_cons_self .., hq⟩
  · exact .inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hq⟩
  · exact .inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), hq⟩

omit [Host] in
theorem outs_outsF {q : BitVec 64} (hq : outs m0 q) : outsF m0 q :=
  hq.elim (fun hq ↦ .inl hq.1) .inr

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
