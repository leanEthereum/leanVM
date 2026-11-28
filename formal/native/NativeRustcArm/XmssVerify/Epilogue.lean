module

public import NativeRustcArm.XmssVerify.Head
meta import NativeRustcArm.Code.Xmss.XmssVerify

/-!
# `xmss_verify`: the epilogue

Block 27: the frame freed, the callee-saved registers restored from the save area, `ret`
(`epilogue`: from `Common` to the contract's frame facts, X0 kept); block 26, `mov x0, xzr`, then
block 27 (`fail`: X0 `0`).
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash

set_option Elab.async false

/-- The symbolic state at block 27: region 0 the frame (SP its base). -/
def stE : SState := init [(5872, true)] (.ptr 0 0)

sym_block b27_exec := exec b27 stE

/-- The symbolic state after block 27. -/
def stE' : SState := ((exec b27 stE).getD (stE, .fall)).1

theorem stE'_facts : stE'.mem = [] ∧ stE'.sp = .ptr 0 5872 ∧ stE'.reg .X0 = some (.reg .X0) ∧
    ∀ j < 12, stE'.reg (saveRegs.getD j .X0) = some (.load 0 (5776 + 8 * j) 8) := by
  decide +kernel

theorem b27_exec' : exec b27 stE = some (stE', .ret) := by
  rw [b27_exec]
  rfl

sym_block b26_exec := exec b26 (init [] .sp)

/-- The symbolic state after block 26. -/
def stF : SState := ((exec b26 (init [] .sp)).getD (init [] .sp, .fall)).1

theorem stF_facts : keeps (init [] .sp) stF = true ∧ stF.mem = [] ∧ stF.reg .X0 = some (.lit 0) ∧
    stF.reg .X29 = some (.reg .X29) := by decide +kernel

theorem b26_exec' : exec b26 (init [] .sp) = some (stF, .fall) := by
  rw [b26_exec]
  rfl

theorem saveRegs_cases (r : XReg) (hr : calleeSaved r = true) : ∃ j < 12, saveRegs.getD j .X0 = r := by
  cases r <;> simp_all [calleeSaved] <;> first
    | exact ⟨11, by decide, rfl⟩ | exact ⟨10, by decide, rfl⟩ | exact ⟨9, by decide, rfl⟩
    | exact ⟨8, by decide, rfl⟩ | exact ⟨7, by decide, rfl⟩ | exact ⟨6, by decide, rfl⟩
    | exact ⟨5, by decide, rfl⟩ | exact ⟨4, by decide, rfl⟩ | exact ⟨3, by decide, rfl⟩
    | exact ⟨2, by decide, rfl⟩ | exact ⟨0, by decide, rfl⟩

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **The epilogue**: from block 27 with `Common`, the return to the entry's return address, X0
kept, the contract's frame facts. -/
public theorem epilogue {k : Nat} (hp : Placed code k) (P : Pre w m₀) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b27Offset)) (C : Common m₀ st.data) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m₀ ∧ st'.data.regs.X0 = st.data.regs.X0 ∧
      SameOutside m₀.dmem st'.data.dmem (InRange (stackBelow m₀ xmssVerifyStack) xmssVerifyStack) ∧
      Saved m₀ st'.data) st := by
  have hwf : (Env.ofMachine st.data [(ad m₀ fb, 5872)]).WF :=
    Env.wf_of ⟨⟨(P.mapped.sub (i := fb) (k := 5872) (by fbo)).kept C.kept,
      P.ad_nw (o := fb) (s := 5872) (by fbo)⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data [(ad m₀ fb, 5872)]) stE st.data := by
    unfold stE
    apply match_ofMachine
    · exact And.intro rfl (And.intro (fun _ => frame16 P) trivial)
    · rw [C.sp]
      simp [Sym.eval]
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
  refine exec_at (b27_in_code.trans hp.1 (List.cons_ne_nil _ _)) b27_exec' hwf hpc hm
    fun st' hm' hpc' => .done _ ?_
  obtain ⟨hmem, hsp, h0, hld⟩ := stE'_facts
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
  have hreg : ∀ j < 12, st'.data.regs.getXReg (saveRegs.getD j .X0) =
      m₀.regs.getXReg (saveRegs.getD j .X0) := fun j hj => by
    apply UInt64.toBitVec_inj.mp
    rw [hm'.regs _ _ (hld j hj)]
    simp only [Sym.eval]
    rw [Env.load_of_bytesAt (length_regBytes _) (by
      have := C.save j hj
      rw [show fb + 5776 + 8 * j = fb + (5776 + 8 * j) by omega, ← ad_add] at this
      exact this), ofBytes_regBytes]
  have hx30 : st'.data.regs.X30 = m₀.regs.X30 := hreg 1 (by omega)
  refine ⟨?_, UInt64.toBitVec_inj.mp (hm'.regs .X0 _ h0), ?_, ?_, ?_, C.kept.trans (hd ▸ Kept.refl _)⟩
  · show st'.pc = _
    rw [show st'.pc = retOf st'.data from hpc']
    unfold retOf
    rw [hx30]
  · rw [hd]
    exact C.same
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := saveRegs_cases r hr
    exact hreg j hj
  · apply UInt64.toBitVec_inj.mp
    rw [hm'.sp, hsp]
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    exact sp_eq m₀

/-- `Common` after a block that writes no memory and keeps SP and X29. -/
theorem Common.nil {m m' : MachineData} (C : Common m₀ m) {S : SState}
    (hm : Match (Env.ofMachine m []) S m') (hs : Saved m m') (hmem : S.mem = []) :
    Common m₀ m' := by
  have hd := hm.dmem_eq (Env.wf_nil m) hmem
  exact C.call hs (R := fun _ => False) (fun p _ => by rw [hd]; rfl) (fun _ h => h.elim)
    (fun _ _ _ h => h)

/-- **The rejection**: from block 26, X0 `0` and the return. -/
public theorem fail {k : Nat} (hp : Placed code k) (P : Pre w m₀) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcArm.Xmss.XmssVerify.b26Offset)) (C : Common m₀ st.data) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m₀ ∧ st'.data.regs.X0 = 0 ∧
      SameOutside m₀.dmem st'.data.dmem (InRange (stackBelow m₀ xmssVerifyStack) xmssVerifyStack) ∧
      Saved m₀ st'.data) st := by
  obtain ⟨hk, hmem, h0, -⟩ := stF_facts
  refine exec_at (b26_in_code.trans hp.1 (List.cons_ne_nil _ _)) b26_exec' (Env.wf_nil _) hpc
    (match_nil st.data) fun st' hm hpc' => ?_
  have hs := Match.saved (match_nil st.data) hm (Env.wf_nil _) rfl hk
  have C' := C.nil hm hs hmem
  refine NativeRustcArm.Eventually.mono (epilogue hp P (hpc'.trans rfl) C') fun s ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, h2.trans (UInt64.toBitVec_inj.mp (hm.regs .X0 _ h0)), h3, h4⟩

end NativeRustcArm.Xmss.XmssVerify
