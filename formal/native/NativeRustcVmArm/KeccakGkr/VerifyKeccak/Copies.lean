module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.CopyStep

/-!
# `verify_keccak`: the copies before the layers

`b9` to `b14`: the first claim (at 968) through the frame's 2216 (value, `mu`) and 1736 (the
point's elements) to the running claim at 960 and the first claim's point at 480, the words at 48
(the point's address), 56, 64 (its size); `b15`: the first bit weights to the scratch's `weights`.
At `b16`: `AtL` before layer `0` (`stepCopies`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)

public section

/-- A callee-saved register a block keeps, past the call. -/
theorem keep_cs [Labels] {env : Env} {m st m2 : MachineData} {S : SState}
    (hm0 : Match env midS m) (hm : Match env S st)
    (hcs : ∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r) {r : XReg}
    (hr : calleeSaved r = true) (h0 : midS.reg r = some (.reg r)) (hS : S.reg r = some (.reg r)) :
    m2.regs.getXReg r = m.regs.getXReg r :=
  (hcs r hr).trans (Match.reg_eq hm0 hm h0 hS)

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **The copies** (`b9` to `b15`): before layer `0`. -/
theorem stepCopies (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m : MachineData} {s4 : TState} {first : KeccakClaimW} {c : EW}
    (hf : AtF a s cs inst output m0 m s4 first c)
    (cont : ∀ m', AtL a s cs inst output m0 m' 0 s4 first first c →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b16Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b9Offset)⟩ := by
  have hN := hn.hN
  obtain ⟨hval, hmu, hpl, hpw, hpe⟩ := hf.claim
  have hpl' : first.point.toList.length ≤ 30 := hpl
  rw [show NativeRustcVm.KeccakGkr.off (loc m0 968) NativeRustcVm.KeccakGkr.pointOff =
    loc m0 1248 from loc_add m0 968 280] at hpw hpe
  rw [show loc m0 1248 + 8#64 = loc m0 1256 from loc_add m0 1248 8] at hpe
  -- b9: value and `mu` to 2216
  refine cpC hn hmemcpy (b9_in_code.trans hp.1 (by simp [b9])) run_b9 hf.mid rfl
    (L := [(56, 64)]) (dst := 2216) (src := 968) (n := 280) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun st hm ↦ reg_loc hm (r := .X0) (o := 2216) rfl)
    (fun st hm ↦ reg_addL hm (x := .X1) (y := .X28) (o := 960) (c := 8) rfl hf.x28) rfl
    (by decide) (by decide) (by decide) (by decide)
    fun st9 m10 hm9 hmid10 hi9 hb9 hc9 hk9 hcs9 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b9Offset + b9.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b9_next]]
  have x28a : (m10.regs.getXReg .X28).toBitVec = loc m0 960 := by
    rw [keep_cs (matchM hn hf.mid.fr) hm9 hcs9 (r := .X28) rfl rfl rfl]; exact hf.x28
  have w56 : NativeRustcVm.WordAt st9.dmem (loc m0 56) c.c1 := by
    have := Sumcheck.Match.wordAt_write hm9 (r := 0) (o := 56) (v := .reg .X29) rfl (by decide)
      (by decide)
    simp only [Sym.eval, Env.ofMachine_regs, hf.x29] at this; exact this
  have pw10 := (hb9.trans hc9).word hn (by decide) (o := 1248) (by decide) (by decide) hpw
  have pe10 := (hb9.trans hc9).ews hn (by decide) (o := 1256) (k := 480) (by decide)
    (by decide) (by omega) hpe
  -- b10: the point's elements to 1736, its size into X29
  refine cpC hn hmemcpy (b10_in_code.trans hp.1 (by simp [b10])) run_b10 hmid10 rfl
    (L := []) (dst := 1736) (src := 1256) (n := 480) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun st hm ↦ reg_loc hm (r := .X0) (o := 1736) rfl)
    (fun st hm ↦ reg_addL hm (x := .X1) (y := .X28) (o := 960) (c := 296) rfl x28a) rfl
    (by decide) (by decide) (by decide) (by decide)
    fun st10 m11 hm10 hmid11 hi10 hb10 hc10 hk10 hcs10 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b10Offset + b10.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b11Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b10_next]]
  have x29a : st10.regs.getXReg .X29 = first.point.toList.length.toUInt64 :=
    reg_of hm10 (r := .X29) (v := .load 0 1248 8) rfl
      (Sumcheck.load_word (env := envM m0 m10) (r := 0) (off := 1248) pw10)
  have x28b : (m11.regs.getXReg .X28).toBitVec = loc m0 960 := by
    rw [keep_cs (matchM hn hmid10.fr) hm10 hcs10 (r := .X28) rfl rfl rfl]; exact x28a
  have pt11 : NativeRustcVm.EWsAt m11.dmem (loc m0 1736) first.point.toList :=
    hi10.bytesAt0 pe10 (by rw [NativeRustcVm.length_ewsBytes]; omega)
  -- b11: value and `mu` to 192
  refine cpC hn hmemcpy (b11_in_code.trans hp.1 (by simp [b11])) run_b11 hmid11 rfl
    (L := []) (dst := 192) (src := 2216) (n := 280) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun st hm ↦ reg_loc hm (r := .X0) (o := 192) rfl)
    (fun st hm ↦ reg_loc hm (r := .X1) (o := 2216) rfl) rfl
    (by decide) (by decide) (by decide) (by decide)
    fun st11 m12 hm11 hmid12 hi11 hb11 hc11 hk11 hcs11 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b11Offset + b11.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b11_next]]
  have x19a : (m12.regs.getXReg .X19).toBitVec = loc m0 192 := by
    rw [hcs11 .X19 rfl]; exact reg_loc hm11 (r := .X19) (o := 192) rfl
  have x28c : (m12.regs.getXReg .X28).toBitVec = loc m0 960 := by
    rw [keep_cs (matchM hn hmid11.fr) hm11 hcs11 (r := .X28) rfl rfl rfl]; exact x28b
  have x29b : m12.regs.getXReg .X29 = first.point.toList.length.toUInt64 := by
    rw [keep_cs (matchM hn hmid11.fr) hm11 hcs11 (r := .X29) rfl rfl rfl, hcs10 .X29 rfl]
    exact x29a
  have pt12 := (hb11.trans hc11).ews hn (by decide) (o := 1736) (k := 480) (by decide)
    (by decide) (by omega) pt11
  -- b12: the point's elements to 480, its address at 48
  refine cpC hn hmemcpy (b12_in_code.trans hp.1 (by simp [b12])) run_b12 hmid12 rfl
    (L := [(48, 56), (472, 480)]) (dst := 480) (src := 1736) (n := 480) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (fun st hm ↦ reg_addL hm (x := .X0) (y := .X19) (o := 192) (c := 288) rfl x19a)
    (fun st hm ↦ reg_loc hm (r := .X1) (o := 1736) rfl) rfl
    (by decide) (by decide) (by decide) (by decide)
    fun st12 m13 hm12 hmid13 hi12 hb12 hc12 hk12 hcs12 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b12Offset + b12.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b12_next]]
  have w48 : NativeRustcVm.WordAt st12.dmem (loc m0 48) (UInt64.ofBitVec (loc m0 480)) := by
    have := Sumcheck.Match.wordAt_write hm12 (r := 0) (o := 48)
      (v := .bin .add .W64 (.reg .X19) (.lit 288)) rfl (by decide) (by decide)
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs, x19a,
      NativeRustcVm.addr_add_add] at this
    exact this
  have x28d : (m13.regs.getXReg .X28).toBitVec = loc m0 960 := by
    rw [keep_cs (matchM hn hmid12.fr) hm12 hcs12 (r := .X28) rfl rfl rfl]; exact x28c
  have x29c : m13.regs.getXReg .X29 = first.point.toList.length.toUInt64 := by
    rw [keep_cs (matchM hn hmid12.fr) hm12 hcs12 (r := .X29) rfl rfl rfl]; exact x29b
  have fp13 : NativeRustcVm.EWsAt m13.dmem (loc m0 480) first.point.toList :=
    hi12.bytesAt0 pt12 (by rw [NativeRustcVm.length_ewsBytes]; omega)
  have pt13 := (hb12.trans hc12).ews hn (by decide) (o := 1736) (k := 480) (by decide)
    (by decide) (by omega) pt12
  have iv13 : Img m.dmem (loc m0 968) m13.dmem (loc m0 2216) 280 :=
    ((hi9.chg hn (hb10.trans hc10) (by decide) (by decide) (by decide)).chg hn
      (hb11.trans hc11) (by decide) (by decide) (by decide)).chg hn (hb12.trans hc12)
      (by decide) (by decide) (by decide)
  -- b13: value and `mu` to 960
  refine cpC hn hmemcpy (b13_in_code.trans hp.1 (by simp [b13])) run_b13 hmid13 rfl
    (L := []) (dst := 960) (src := 2216) (n := 280) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun st hm ↦ reg_loc hm (r := .X0) (o := 960) rfl)
    (fun st hm ↦ reg_loc hm (r := .X1) (o := 2216) rfl) rfl
    (by decide) (by decide) (by decide) (by decide)
    fun st13 m14 hm13 hmid14 hi13 hb13 hc13 hk13 hcs13 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b13Offset + b13.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b13_next]]
  have x28e : (m14.regs.getXReg .X28).toBitVec = loc m0 960 := by
    rw [keep_cs (matchM hn hmid13.fr) hm13 hcs13 (r := .X28) rfl rfl rfl]; exact x28d
  have x29d : m14.regs.getXReg .X29 = first.point.toList.length.toUInt64 := by
    rw [keep_cs (matchM hn hmid13.fr) hm13 hcs13 (r := .X29) rfl rfl rfl]; exact x29c
  have pt14 := (hb13.trans hc13).ews hn (by decide) (o := 1736) (k := 480) (by decide)
    (by decide) (by omega) pt13
  have cv14 : Img m.dmem (loc m0 968) m14.dmem (loc m0 960) 280 := iv13.trans hi13
  -- b14: the point's elements to 1248, its size at 1240 and 64
  refine cpC hn hmemcpy (b14_in_code.trans hp.1 (by simp [b14])) run_b14 hmid14 rfl
    (L := [(1240, 1248), (64, 72)]) (dst := 1248) (src := 1736) (n := 480) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun st hm ↦ reg_addL hm (x := .X0) (y := .X28) (o := 960) (c := 288) rfl x28e)
    (fun st hm ↦ reg_loc hm (r := .X1) (o := 1736) rfl) rfl
    (by decide) (by decide) (by decide) (by decide)
    fun st14 m15 hm14 hmid15 hi14 hb14 hc14 hk14 hcs14 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b14Offset + b14.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b15Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b14_next]]
  have wsz : ∀ o, o + 8 ≤ 3360 → (∀ i < 8, findWrite 0 (o + i) (match exec b14 midS with
      | some (S, _) => S.mem | none => []) = some (.reg .X29, i)) →
      NativeRustcVm.WordAt st14.dmem (loc m0 o) first.point.toList.length.toUInt64 := by
    intro o ho hw
    have := Sumcheck.Match.wordAt_write hm14 (r := 0) (o := o) (v := .reg .X29) rfl ho
      (by rw [run_b14] at hw; exact hw)
    simp only [Sym.eval, Env.ofMachine_regs, x29d] at this; exact this
  have w1240 := wsz 1240 (by decide) (by rw [run_b14]; decide)
  have w64 := wsz 64 (by decide) (by rw [run_b14]; decide)
  have x19b : (m15.regs.getXReg .X19).toBitVec = loc m0 1248 := by
    rw [hcs14 .X19 rfl]
    exact reg_addL hm14 (x := .X19) (y := .X28) (o := 960) (c := 288) rfl x28e
  have pe15 : NativeRustcVm.EWsAt m15.dmem (loc m0 1248) first.point.toList :=
    hi14.bytesAt0 pt14 (by rw [NativeRustcVm.length_ewsBytes]; omega)
  have P15 := (hb9.trans hc9).trans ((hb10.trans hc10).trans ((hb11.trans hc11).trans
    ((hb12.trans hc12).trans ((hb13.trans hc13).trans (hb14.trans hc14)))))
  have fw15 := P15.wts hn (by decide) (by decide) (o := 0) (by decide) (by decide)
    (by rw [NativeRustcVm.addr_add_zero]; exact hf.wts)
  rw [NativeRustcVm.addr_add_zero] at fw15
  -- b15: the first bit weights to the scratch's `weights`
  refine scrCopy hp h hn hmemcpy hmid15 fun m16 hmid16 hc15 hk15 hcs15 hiw ↦ ?_
  have T := P15.trans hc15
  have hk : Kept m.dmem m16.dmem :=
    kept_tr hk9 (kept_tr hk10 (kept_tr hk11 (kept_tr hk12 (kept_tr hk13 (kept_tr hk14 hk15)))))
  have T13 := ((hb13.trans hc13).trans (hb14.trans hc14)).trans hc15
  have cv16 := cv14.chg hn ((hb14.trans hc14).trans hc15) (by decide) (by decide) (by decide)
  refine cont m16 ⟨⟨hmid16, ?_, T.cls hn (by decide) (by decide) (by decide) hf.cls, ?_, ?_,
    T.wts hn (by decide) (by decide) (o := 0) (by decide) (by decide)
      (by rw [NativeRustcVm.addr_add_zero]; exact hf.wts), ?_, ?_, ?_, ?_, ?_⟩,
    T.ts hn hk (by decide) (by decide) (by decide) hf.ts, ?_, ?_, rfl, hf.hfirst, ?_⟩
  · rw [hcs15 .X19 rfl]; exact x19b
  · exact hpl'
  · exact T13.ews hn (by decide) (o := 480) (k := 480) (by decide) (by decide) (by omega) fp13
  · exact ((hc12.trans (hb13.trans hc13)).trans ((hb14.trans hc14).trans hc15)).word hn
      (by decide) (by decide) (by decide) w48
  · exact (hc9.trans ((hb10.trans hc10).trans ((hb11.trans hc11).trans ((hb12.trans hc12).trans
      T13)))).word hn (by decide) (by decide) (by decide) w56
  · exact (hc14.trans hc15).word hn (by decide) (by decide) (by decide) w64
  · exact T.word hn (by decide) (by decide) (by decide) hf.w72
  · exact T.word hn (by decide) (by decide) (by decide) hf.w80
  · refine ⟨cv16.bytesAt0 hval (by rw [NativeRustcVm.length_ewBytes]; omega),
      cv16.bufEWAt hmu (by decide), hpl, ?_, ?_⟩
    · rw [show NativeRustcVm.KeccakGkr.off (loc m0 960) NativeRustcVm.KeccakGkr.pointOff =
        loc m0 1240 from loc_add m0 960 280]
      exact (hc14.trans hc15).word hn (by decide) (by decide) (by decide) w1240
    · rw [show NativeRustcVm.KeccakGkr.off (loc m0 960) NativeRustcVm.KeccakGkr.pointOff +
        8#64 = loc m0 1248 from
        (congrArg (· + 8#64) (loc_add m0 960 280)).trans (loc_add m0 1240 8)]
      exact hc15.ews hn (by decide) (o := 1248) (k := 480) (by decide) (by decide) (by omega)
        pe15
  · exact ⟨hf.wts.1, hiw.bytesAt0 fw15.2 (by
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hf.wts.1]; decide)⟩
  · rw [hf.run, afterCommitted, keccakLayers_eq]

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
