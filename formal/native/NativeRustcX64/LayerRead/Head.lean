module

public import NativeRustcX64.LayerRead.Inv
meta import NativeRustcX64.LayerRead.Inv
meta import NativeRustcX64.Code.Xmss.LayerRead

/-! # The slice parser prologue -/

namespace NativeRustcX64.Xmss.LayerRead

open NativeRustcX64.Sym

set_option Elab.async false

@[expose] public def stA : SState :=
  init [1944, 16] [(.rsp, .ptr 0 1936), (.rsi, .ptr 1 0)]

sym_block b0_execA := exec b0 stA
@[expose] public def stA1 : SState := ((exec b0 stA).getD (stA, .fall)).1
sym_block b1_execA := exec b1 stA1
@[expose] public def stA2 : SState := ((exec b1 stA1).getD (stA1, .fall)).1

@[expose] public def countExpr : Sym :=
  .bin .shr .W64 (.bin .add .W64 (.load 1 8 8) (.lit (2 ^ 64 - 16))) (.lit 4)

theorem stA2_save : ∀ j < 6, ∀ i < 8,
    findWrite 0 (1888 + 8 * j + i) stA2.mem = some (.reg (saveRegs.getD j .rax), i) := by
  decide +kernel
theorem stA2_output : ∀ i < 8,
    findWrite 0 (24 + i) stA2.mem = some (.reg .rdi, i) := by decide +kernel
theorem stA2_writes : writesBelow stA2 [(0, 1936)] = true := by decide +kernel
theorem stA2_regs : stA2.reg .r14 = some (.ptr 1 0) ∧
    stA2.reg .r11 = some (.load 1 0 8) ∧ stA2.reg .r12 = some (.load 1 8 8) ∧
    stA2.reg .rax = some countExpr ∧ stA2.reg .rdx = some countExpr ∧
    stA2.reg .rdi = some (.lit 0) ∧ stA2.reg .rcx = some (.lit 0) ∧
    stA2.reg .rsi = some (.ptr 0 32) ∧ stA2.reg .rsp = some (.ptr 0 8) := by decide +kernel

@[expose] public def envA (m : MachineData) : Env :=
  Env.ofMachine m [(base m, 1944), (cur m, 16)]

theorem envA_wf {m : MachineData} (P : Pre m) : (envA m).WF :=
  Env.wf_of ⟨⟨P.stackMapped, P.baseNW⟩, ⟨P.curMapped, P.curNW⟩, trivial⟩
    (List.pairwise_pair.mpr P.curF.symm)

theorem envA_input {m : MachineData} (P : Pre m) : (envA m).load 1 0 8 = sig m := by
  rw [Env.load_of_bytesAt (bs := NativeRustcX64.bytesOf m.dmem (cur m) 8)
    (length_bytesOf _ _ _)
    (by simpa [envA, Env.base] using bytesAt_bytesOf (P.curMapped.sub (i := 0) (k := 8) (by omega))),
    ofBytes_eq_leNat]
  rfl

theorem envA_length {m : MachineData} (P : Pre m) :
    (envA m).load 1 8 8 = BitVec.ofNat 64 (remaining m) := by
  rw [Env.load_of_bytesAt (bs := NativeRustcX64.bytesOf m.dmem (cur m + 8#64) 8)
    (length_bytesOf _ _ _)
    (by simpa [envA, Env.base] using bytesAt_bytesOf (P.curMapped.sub (i := 8) (k := 8) (by omega))),
    ofBytes_eq_leNat]
  rfl

public theorem sub_nat (n d : Nat) (h : d ≤ n) :
    BitVec.ofNat 64 n + BitVec.ofInt 64 (- (d : Int)) = BitVec.ofNat 64 (n - d) := by
  simp only [← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
  congr 1
  omega

theorem envA_count [Labels] {m : MachineData} (P : Pre m) :
    countExpr.eval (envA m) = BitVec.ofNat 64 ((remaining m - 16) / 16) := by
  simp only [countExpr, Sym.eval, BinOp.apply, low_W64, ext_W64, envA_length P]
  change (BitVec.ofNat 64 (remaining m) + BitVec.ofInt 64 (-16)).ushiftRight 4 = _
  have hs : BitVec.ofNat 64 (remaining m) + BitVec.ofInt 64 (-16) =
      BitVec.ofNat 64 (remaining m - 16) := sub_nat (remaining m) 16 (by have := P.enough; omega)
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 64 (remaining m - 16) >>> 4).toNat = _
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := P.lengthLt
  omega

theorem match_envA [Labels] {m : MachineData} (P : Pre m) : Match (envA m) stA m := by
  unfold envA stA
  apply match_ofMachine
  · exact ⟨rfl, rfl, trivial⟩
  · refine ⟨?_, ?_, trivial⟩
    · show reg m .rsp = _
      rw [show reg m .rsp = rspOf m from rfl, P.rsp_eq]
      simp [Sym.eval, Env.base]
    · simp [Sym.eval, Env.base, cur]
  · exact trivial
  · exact trivial
  · exact trivial

/-- The nonempty slice check and prologue establish the chain loop invariant. -/
public theorem head [Host] {k : Nat} (hp : Placed code k) {m : MachineData}
    (hpre : LayerReadPre m) {R : MachineState → Prop}
    (cont : ∀ st : MachineState, st.pc = Host.addrOf (k + b2Offset) → LoopAt m st.data 0 →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf k⟩ := by
  have P := pre_of hpre
  have hwf := envA_wf P
  have hnb :
      (SBool.or (SBool.cmp .ult .W64 (.load 1 8 8) (.lit 15))
        (SBool.cmp .eq .W64 (.load 1 8 8) (.lit 15))).eval (envA m) = false := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64, envA_length P]
    have := P.enough
    have := P.lengthLt
    simp [BitVec.ult, BitVec.toNat_eq]
    omega
  refine cond_step (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) b0_execA hwf rfl (match_envA P)
    hnb fun st₁ hpc₁ hm₁ => ?_
  refine fall_step (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) b1_execA hwf hpc₁ hm₁
    fun st₂ hpc₂ hm₂ => ?_
  change Match _ stA2 st₂.data at hm₂
  obtain ⟨h14, h11, h12, hax, hdx, hdi, hcx, hsi, hsp⟩ := stA2_regs
  refine cont st₂ hpc₂ ⟨⟨?_, ?_, hm₂.kept hwf, ?_, ?_⟩, by omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => absurd hj (by omega)⟩
  · exact (hm₂.regs .rsp _ hsp).trans (by simp [Sym.eval, Env.base, envA])
  · exact (hm₂.sameOutside_below hwf stA2_writes).mono fun p ⟨rb, hrb, b, sz, hb, hin⟩ => by
      simp only [List.mem_singleton] at hrb
      subst rb
      cases hb
      exact Or.inl hin
  · exact fun j hj => hm₂.bytesAt_write (r := 0) rfl (by omega) (stA2_save j hj)
  · exact hm₂.bytesAt_write (r := 0) rfl (by omega) stA2_output
  · exact (hm₂.regs .r14 _ h14).trans (by simp [Sym.eval, Env.base, envA])
  · exact (hm₂.regs .r11 _ h11).trans (envA_input P)
  · simpa using (hm₂.regs .r12 _ h12).trans (envA_length P)
  · exact (hm₂.regs .rax _ hax).trans (envA_count P)
  · simpa using (hm₂.regs .rdx _ hdx).trans (envA_count P)
  · exact hm₂.regs .rdi _ hdi
  · exact hm₂.regs .rcx _ hcx
  · exact (hm₂.regs .rsi _ hsi).trans (by simp [Sym.eval, Env.base, envA])

end NativeRustcX64.Xmss.LayerRead
