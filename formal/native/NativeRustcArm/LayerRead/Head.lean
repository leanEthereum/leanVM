module

public import NativeRustcArm.LayerRead.Inv
meta import NativeRustcArm.Code.Xmss.LayerRead

/-!
# `LayerSignature::read`: prologue and chain-loop setup

The first check establishes that the initial randomizer fits. Its bytes are
not copied yet: X21 retains their address until the output is assembled.
-/

namespace NativeRustcArm.Xmss.LayerRead

open NativeRustcArm.Sym NativeRustcArm

set_option Elab.async false

def stA : SState := init [(1936, true), (16, false)] (.ptr 0 1936) [(.X1, .ptr 1 0)]

sym_block b0_execA := exec b0 stA

def stA1 : SState := ((exec b0 stA).getD (stA, .fall)).1

sym_block b1_execA := exec b1 stA1

def stA2 : SState := ((exec b1 stA1).getD (stA, .fall)).1

theorem stA2_save : ∀ j < 10, j ≠ 3 → ∀ i < 8,
    findWrite 0 (1856 + 8 * j + i) stA2.mem = some (.reg (saveRegs.getD j .X0), i) := by
  decide +kernel

theorem stA2_writes : writesIn stA2 [0] = true := by decide +kernel

def envA (m₀ : MachineData) : Env :=
  Env.ofMachine m₀ [(frame m₀, 1936), (cur m₀, 16)]

theorem envA_wf {m₀ : MachineData} (P : Pre m₀) : (envA m₀).WF :=
  Env.wf_of ⟨⟨P.frameMapped, P.frameNW⟩, ⟨P.curMapped, P.curNW⟩, trivial⟩
    (List.pairwise_pair.mpr P.curF.symm)

theorem envA_data {m₀ : MachineData} (P : Pre m₀) :
    (envA m₀).load 1 0 8 = sig m₀ := by
  rw [Env.load_of_bytesAt (bs := bytesOf m₀.dmem (cur m₀) 8) (length_bytesOf _ _ _)
    (by simpa [envA, Env.base] using bytesAt_bytesOf (show Mapped m₀.dmem (cur m₀) 8 from
      fun i hi => P.curMapped i (by omega))),
    ofBytes_eq_leNat]
  rfl

theorem envA_remaining {m₀ : MachineData} (P : Pre m₀) :
    (envA m₀).load 1 8 8 = BitVec.ofNat 64 (remaining m₀) := by
  rw [Env.load_of_bytesAt (bs := bytesOf m₀.dmem (cur m₀ + 8) 8) (length_bytesOf _ _ _)
    (by simpa [envA, Env.base] using bytesAt_bytesOf (P.curMapped.sub (i := 8) (by omega))),
    ofBytes_eq_leNat]
  simpa only [remaining, LayerReadPre.remaining, cur, BitVec.setWidth_eq] using
    (BitVec.ofNat_toNat 64 (BitVec.ofNat 64 (NativeRustc.leNat (bytesOf m₀.dmem (cur m₀ + 8) 8)))).symm

theorem match_envA [Labels] {m₀ : MachineData} (P : Pre m₀) : Match (envA m₀) stA m₀ := by
  unfold envA stA
  apply match_ofMachine
  · refine ⟨rfl, fun _ => ?_, And.intro rfl (And.intro (by simp) trivial)⟩
    rw [P.frameNat]
    have := P.sp16
    have := P.spLe
    unfold layerReadStack at *
    omega
  · simp only [Sym.eval, Env.base, frame, stackBelow, Env.ofMachine_regions]
    rw [show BitVec.ofNat 64 layerReadStack = BitVec.ofInt 64 1936 from rfl]
    simp
  · exact ⟨by simp [Sym.eval, Env.base, cur]; rfl, trivial⟩
  · exact trivial
  · exact trivial
  · exact trivial

theorem frame_add [Labels] (m₀ : MachineData) (o : Nat) :
    (Sym.ptr 0 o).eval (envA m₀) = frame m₀ + BitVec.ofNat 64 o := by
  simp [Sym.eval, Env.base, envA]

theorem shift4 (x : BitVec 64) :
    UnOp.apply (.ubfm 4 63) .W64 x = BitVec.ofNat 64 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp [UnOp.apply, evalUBFM, BitVec.take, BitVec.extractLsb'_toNat,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show x.toNat / 16 < 1152921504606846976 by omega)]

public theorem ofNat_sub (n k : Nat) (h : k ≤ n) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := by
  rw [← Nat.sub_add_cancel h, BitVec.ofNat_add]
  simp

/-- The prologue reaches the chain loop before its first value. -/
public theorem head [Host] {k : Nat} (hp : Placed code k) {m₀ : MachineData}
    (hpre : LayerReadPre m₀) {R : MachineState → Prop}
    (cont : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcArm.Xmss.LayerRead.b2Offset) →
      LoopAt m₀ st.data 0 → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m₀, Host.addrOf k⟩ := by
  have P := pre_of hpre
  have hwf := envA_wf P
  refine exec_then (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) b0_execA hwf (match_envA P)
    fun st₁ hm₁ hpc₁ => ?_
  have hnb : (SBool.or (SBool.cmp .ult .W64 (.load 1 8 8) (.lit 15))
      (SBool.cmp .eq .W64 (.load 1 8 8) (.lit 15))).eval (envA m₀) = false := by
    have := P.remaining
    have := remaining_lt m₀
    simp [SBool.eval, CmpOp.apply, Sym.eval, low_W64, envA_remaining P,
      BitVec.ult, BitVec.toNat_eq]
    omega
  simp only [PcOk, hnb, Bool.false_eq_true, ite_false] at hpc₁
  have hm₁' : Match (envA m₀) stA1 st₁.data := by unfold stA1; rw [b0_execA]; exact hm₁
  refine exec_at (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) b1_execA hwf hpc₁ hm₁'
    fun st₂ hm₂ hpc₂ => ?_
  have hm : Match (envA m₀) stA2 st₂.data := by unfold stA2; rw [b1_execA]; exact hm₂
  refine cont st₂ hpc₂ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hm.kept hwf, ?_⟩,
    ?_, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  · exact hm.regs .X19 (.reg .X0) (by decide +kernel)
  · exact (hm.regs .X20 (.ptr 1 0) (by decide +kernel)).trans
      (by simp [Sym.eval, Env.base, envA, cur])
  · exact (hm.regs .X21 (.load 1 0 8) (by decide +kernel)).trans (envA_data P)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact UInt64.toBitVec_inj.mp (hm.regs _ (.reg _) (by decide +kernel))
  · exact (hm.regs .X29 (.ptr 0 1856) (by decide +kernel)).trans (frame_add m₀ 1856)
  · rw [hm.sp, show stA2.sp = .ptr 0 0 by decide]
    simp [Sym.eval, Env.base, envA]
  · exact (hm.sameOutside_in hwf stA2_writes).mono fun p ⟨r, hr, b, sz, hb, hin⟩ => by
      simp only [List.mem_singleton] at hr
      subst r
      simp only [envA, Env.ofMachine_regions] at hb
      cases hb
      exact Or.inl hin
  · exact fun j hj hj3 => hm.bytesAt_write (r := 0) rfl (by omega) (stA2_save j hj hj3)
  · rw [hm.regs .X8 (.un (.ubfm 4 63) .W64 (.bin .sub .W64 (.load 1 8 8) (.lit 16)))
      (by decide +kernel)]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, envA_remaining P]
    rw [ofNat_sub _ _ (by have := P.remaining; omega), shift4]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (show remaining m₀ - 16 < 2 ^ 64 by have := remaining_lt m₀; omega), Nat.sub_zero]
  · exact (hm.regs .X9 (.ptr 0 928) (by decide +kernel)).trans (frame_add m₀ 928)
  · simpa using (hm.regs .X22 (.load 1 8 8) (by decide +kernel)).trans (envA_remaining P)
  · exact hm.regs .X23 (.lit 0) (by decide +kernel)

end NativeRustcArm.Xmss.LayerRead
