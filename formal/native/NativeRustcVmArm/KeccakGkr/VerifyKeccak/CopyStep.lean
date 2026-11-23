module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.LDefs

/-!
# `verify_keccak`'s copies: tools

A register a block set to a frame address plus a literal (`reg_addL`); an image pushed past a change
of the frame (`Img.chg`); `b15`: `memcpy` of the first claim's bit weights to the scratch's
`weights` (`scrCopy`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)

public section

variable {m0 : MachineData}

/-- A register a block set to another plus a literal, the other a frame address. -/
theorem reg_addL [Labels] {m st : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {x y : XReg} {c o : Nat} (hm : Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S st)
    (hx : S.reg x = some (.bin .add .W64 (.reg y) (.lit c)))
    (hy : (m.regs.getXReg y).toBitVec = loc m0 o) :
    (st.regs.getXReg x).toBitVec = loc m0 (o + c) := by
  rw [hm.regs x _ hx]
  simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, hy]
  rw [NativeRustcVm.addr_add_add]

/-- **An image pushed past a change** missing its destination. -/
theorem Img.chg [Labels] {a : DecArea} {inst : Array EW} (hn : Nums a inst m0)
    {d d1 d2 : Mem 64} {p : BitVec 64} {o n : Nat} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Img d p d1 (loc m0 o) n) (hc : Chg m0 L O d1 d2)
    (hO : okO O = true) (ho : o + n ≤ 3360)
    (hL : L.all (fun p ↦ decide (p.2 ≤ o) || decide (o + n ≤ p.1)) = true) :
    Img d p d2 (loc m0 o) n :=
  h.trans (Img.of_same (hc.frame hn hO ho hL))

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW}

/-- **`b15`**: the first claim's bit weights copied to the scratch's `weights`. -/
theorem scrCopy (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {m : MachineData}
    (hmid : Mid m0 m) {R : MachineState → Prop}
    (cont : ∀ m2 : MachineData, Mid m0 m2 → Chg m0 [] [(1, 25600, 51200)] m.dmem m2.dmem →
      Kept m.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = m.regs.getXReg r) →
      Img m.dmem (scA m0) m2.dmem (scA m0 + BitVec.ofNat 64 25600) 25600 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b16Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b15Offset)⟩ := by
  have hwf := envM_wf hn hmid.fr
  have hN := hn.hN
  have hsW := hn.sW
  have e22 : (m.regs.getXReg .X22).toBitVec = scA m0 := congrArg UInt64.toBitVec hmid.regs.x22
  refine callC hn (b15_in_code.trans hp.1 (by simp [b15])) run_b15 hmid.fr (matchM hn hmid.fr)
    hwf rfl (by decide) (Lb := []) (L := []) (O := [(1, 25600, 51200)]) (lo := 0) (n := 0)
    (by decide) (by decide) (by decide) (by decide) hmemcpy (fun st hm1 hfr1 ↦ ?_)
    (fun st m' hm1 hfr1 hq ↦ ?_) fun st m2 hm1 hfr1 hq hfr2 hcs hb hc hkt ↦ ?_
  all_goals
    have hd : st.dmem = m.dmem := hm1.dmem_eq hwf rfl
    have e0 : st.regs.X0.toBitVec = scA m0 + BitVec.ofNat 64 25600 := by
      rw [show st.regs.X0 = st.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, e22]
    have e1 : st.regs.X1.toBitVec = scA m0 := by
      rw [show st.regs.X1 = st.regs.getXReg .X1 from rfl, hm1.regs .X1 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs, e22]
    have e2 : st.regs.X2.toNat = 25600 := by
      rw [← UInt64.toNat_toBitVec, show st.regs.X2 = st.regs.getXReg .X2 from rfl,
        hm1.regs .X2 _ rfl]
      simp only [Sym.eval, BitVec.toNat_ofNat]
  · have e25 : (scA m0 + BitVec.ofNat 64 25600).toNat = (scA m0).toNat + 25600 :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [e2] <;> (try rw [e0]) <;> (try rw [e1])
    · exact mapped_of (ok_sc h) hfr1 (o := 25600) (k := 25600) (by decide)
    · have := mapped_of (ok_sc h) hfr1 (o := 0) (k := 25600) (by decide)
      rwa [NativeRustcVm.addr_add_zero] at this
    · unfold NoWrap; rw [e25]; omega
    · unfold NoWrap; omega
    · unfold Apart; rw [e25]; omega
  · obtain ⟨-, -, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rw [e0, e2] at hq
    exact ws_ob hn (i := 1) (o := 25600) (n := 25600) (by decide) (by decide) (by decide)
      (by decide) hq
  · obtain ⟨-, hcp, -, -⟩ := hq
    rw [e0, e1, e2, hd] at hcp
    exact cont m2 (Mid.chg hn hmid hfr2 (regs_kept (matchM hn hmid.fr) hm1 (by decide) hcs)
      (hb.trans hc) (by decide) (by decide)) (hb.trans hc) hkt
      (fun r hr ↦ (hcs r hr).trans (cs_block (matchM hn hmid.fr) hm1 (by decide) r hr))
      (Img.of_bytesOf hcp)

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
