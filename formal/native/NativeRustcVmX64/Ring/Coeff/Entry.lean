module

public import NativeRustcVmX64.Ring.Coeff.Next

/-!
# `ring_coefficients`: the entry block (x86-64)

`enter`: the entry block (`b0`, in the layout of `g`) pushes and spills `G`'s elements, and ends
at the head of turn `0` (`tH`, `g0` the elements as read at the entry, the `gG m0 0` of the model).
-/

namespace NativeRustcVmX64.Ring.Coeff

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingCoefficients

@[expose] public section

/-- `G`'s elements as read at the entry. -/
def g0 (m0 : MachineData) (b : Nat) : EW :=
  ⟨NativeRustcVm.wordOf m0.dmem (gA m0 + BitVec.ofNat 64 (16 * b)),
    NativeRustcVm.wordOf m0.dmem (gA m0 + BitVec.ofNat 64 (16 * b + 8))⟩

end

public section

variable {m0 : MachineData}

theorem g0_eq {b : Nat} (hb : b < 8) : g0 m0 b = gG m0 0 b := by
  rw [gG_zero hb]
  unfold g0 NativeRustcVm.ewOf
  rw [NativeRustcVm.addr_add_add]

/-- `g`'s layout at the entry. -/
theorem layG (h : P m0) : Lay m0 176 NC [(gA m0, 128)] :=
  ⟨h.st, by decide, by decide, ⟨⟨h.gm, h.gw, h.gs⟩, trivial⟩, List.pairwise_singleton _ _⟩

variable [Host] {k : Nat}

/-- **The entry block.** -/
theorem enter (hp : Placed code k) (h : P m0) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.RingCoefficients.b1Offset) ∧ Mem m0 st.data ∧
      Bnd (own m0 st.data) 176 NC (rsP m0 0) wrRow tH (hvG m0 0 (g0 m0)) st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.RingCoefficients.b0Offset)⟩ := by
  have hl := layG h
  have hwf := hl.wf (m := m0) (fun _ h ↦ h) (vals := fun _ ↦ 0) (ret := 0)
  have hB : Bnd m0 176 NC [(gA m0, 128)] (fun _ ↦ false) t0 (fun _ ↦ 0) m0 :=
    start rfl fun ret ↦ ⟨(Field.frame_rsp 176 0).trans (BitVec.add_zero _) |>.symm, by
      show reg m0 .rsi = gA m0 + BitVec.ofInt 64 0
      simp, trivial⟩
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf (fun _ h ↦ by cases h)
    (hB.mt 0) fun st hm hpc ↦ .done _ ⟨hpc, ⟨fun q hq ↦ ?_, fun q hq ↦ hm.kept hwf q hq⟩,
      fun ret ↦ ?_, fun _ _ ↦ rfl, fun _ h ↦ h⟩
  · rw [hm.get?_mem0 hwf fun hW ↦ hq ?_]
    · rfl
    · rcases hl.written (wr := fun _ ↦ false) rfl hW with h1 | ⟨_, _, h2, _⟩
      · exact .inl h1
      · cases h2
  · refine match_links hm (by decide) rfl rfl (fun _ ↦ rfl) rfl rfl rfl ?_ rfl
      (regions_envS rfl) rfl (fun _ _ h ↦ by cases h) (keys_ok rfl rfl rfl rfl st.data ret)
    simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval, load_eq_wordOf]
    and_intros
    all_goals (first | rfl | exact fun _ h ↦ nomatch h)

end

end NativeRustcVmX64.Ring.Coeff
