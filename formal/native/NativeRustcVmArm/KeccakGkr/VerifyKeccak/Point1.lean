module

public import NativeRustcVmArm.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.PExt

/-!
# `verify_keccak`: the output point, `inst`

`b47`: the frame's `Buf<EW, 36>` at 2592 emptied, X19 its address, extended by `inst`'s low four
coordinates; `b48`: its verdict; `b49`: extended by the rest; `b50`: its verdict. At `b51`
(`AtP`): the buffer holds `inst`.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)

@[expose] public section

/-- **The buffer holds `inst`** (`b51`). -/
structure AtP [Labels] (a : DecArea) (s : TState) (cs : Array ColumnClaimW)
    (inst output : Array EW) (m0 m : MachineData) (s' : TState) (cj : KeccakClaimW)
    (sl : Array EW) (w : EW) : Prop where
  mid : Mid m0 m
  x19 : (m.regs.getXReg .X19).toBitVec = loc m0 2592
  x28 : m.regs.getXReg .X28 = w.c0
  buf : NativeRustcVm.BufEWAt m.dmem (loc m0 2592) 36
    (inst.extract 0 4 ++ inst.extract 4 inst.size).toList
  w80 : NativeRustcVm.WordAt m.dmem (loc m0 80) w.c1
  w40 : NativeRustcVm.WordAt m.dmem (loc m0 40) (UInt64.ofBitVec (loc m0 1248))
  w64 : NativeRustcVm.WordAt m.dmem (loc m0 64) (UInt64.ofBitVec (scA m0 + BitVec.ofNat 64 140288))
  w72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7
  ts : TStateAt m.dmem (tA m0) a s'
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) cs
  claim : ClaimAt m.dmem (loc m0 960) cj
  wts : WeightsAt m.dmem (scA m0 + BitVec.ofNat 64 25600) cj
  psz : cj.point.size = inst.size - 4 + 1
  slsz : sl.size = 6
  slot : NativeRustcVm.EWsAt m.dmem (loc m0 2496) sl.toList
  run : run0 s inst output m0 = (restSum m0.regs.X1.toNat cj (outsOf inst sl w)).run s'

end

public section

/-- Part of a region the entry makes data memory: readable. -/
theorem readable_of {m0 st : MachineData} {A : BitVec 64} {N : Nat} (hm : Mapped m0.dmem A N)
    (hw : A.toNat + N ≤ 2 ^ 64) (hk : Kept m0.dmem st.dmem) {o n : Nat} (hn : o + n ≤ N) :
    Readable st (A + BitVec.ofNat 64 o) n := by
  refine ⟨Mapped.kept' (NativeRustcVm.Mapped.sub hm hn) hk, ?_⟩
  unfold NoWrap
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · have := (A + BitVec.ofNat 64 o).isLt; omega
  · rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- The entry's `inst` in a state of the frame. -/
theorem inst_at (h : P0 a s cs inst output m0) (hn : Nums a inst m0) {st : MachineData}
    (hfr : VFr m0 st) : NativeRustcVm.EWsAt st.dmem (ipA m0) inst.toList :=
  bytes_m0 hn hfr h.insts (by rw [ews16, Array.length_toList]; exact hn.iW)
    (by rw [ews16, Array.length_toList]; exact hn.iS) fun q hq ↦ by
      rw [ews16, Array.length_toList]
      have := hn.t_i; have := hn.s_i; have := hn.c_i; have := hn.o_i
      rcases outs_nat hn hq with _ | _ | _ | _ <;> omega

/-- **The output point, `inst`** (`b47` to `b50`). -/
theorem stepPoint1 (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {m : MachineData} {s1 : TState} {cj : KeccakClaimW} {sl : Array EW} {w : EW}
    (hw : AtW a s cs inst output m0 m s1 cj sl w)
    (cont : ∀ m', AtP a s cs inst output m0 m' s1 cj sl w →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b51Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b47Offset)⟩ := by
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have n3 := h.n3
  have n30 := h.n30
  have hiW := hn.iW
  have l2592 := loc_toNat (m0 := m0) hn.hN (o := 2592) (by decide)
  -- `b47`
  refine extC hn hext (b47_in_code.trans hp.1 (by simp [b47])) run_b47 hw.mid rfl
    (Lb := [(2592, 3176)]) (L := []) (xs := (inst.extract 0 4).toList) (A := ipA m0)
    (by decide) (by decide) (by decide) (by decide) rfl (fun st hm1 hfr1 ↦ ?_)
    (by simp only [List.length_nil, Array.length_toList, Array.size_extract]; omega)
    fun st m2 hm1 hmid2 hbuf2 hx2 hb2 hc2 hk2 hcs2 ↦ ?_
  · refine ⟨congrArg UInt64.toBitVec
      ((reg_of hm1 (r := .X1) (v := .reg .X24) rfl rfl).trans hw.mid.regs.x24), ?_,
      ⟨by simp, ?_, NativeRustcVm.ewsAt_nil _ _⟩, (split_ews (inst_at h hn hfr1)).1, ?_, ?_⟩
    · rw [show st.regs.X2 = m.regs.getXReg .X27 from
        reg_of hm1 (r := .X2) (v := .reg .X27) rfl rfl, hw.mid.regs.x27]
      simp only [Array.length_toList, Array.size_extract]
      omega
    · exact Sumcheck.Match.wordAt_write hm1 (r := 0) (o := 2592) (v := .lit 0) rfl (by decide)
        (by decide)
    · have := readable_of (ok_ip h) hn.iW hfr1.kept (o := 0)
        (n := 16 * (inst.extract 0 4).toList.length)
            (by simp only [Array.length_toList, Array.size_extract]; omega)
      rwa [NativeRustcVm.addr_add_zero] at this
    · unfold Apart; rw [l2592]; simp only [Array.length_toList, Array.size_extract]
      obtain h1 | h1 := hn.iS <;> omega
  have x19 : (m2.regs.getXReg .X19).toBitVec = loc m0 2592 := by
    rw [hcs2 .X19 rfl]; exact reg_loc hm1 (r := .X19) (o := 2592) rfl
  have x28 : m2.regs.getXReg .X28 = w.c0 := by
    rw [hcs2 .X28 rfl, Match.reg_eq (matchM hn hw.mid.fr) hm1 (r := .X28) rfl rfl]; exact hw.x28
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b47Offset + b47.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b48Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b47_next]]
  refine failBranch hp hn (b48_in_code.trans hp.1 (by simp [b48])) run_b48 hmid2 rfl rfl
    (by decide) (by decide) (b := true)
    (condW0 (by rw [Env.ofMachine_regs, gx0, hx2]; rfl)) (fun hf ↦ nomatch hf)
    fun _ m3 hmid3 hd3 hcs3 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b48Offset + b48.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b49Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b48_next]]
  -- `b49`
  have hwf3 := envM_wf hn hmid3.fr
  refine extC hn hext (b49_in_code.trans hp.1 (by simp [b49])) run_b49 hmid3 rfl
    (Lb := []) (L := (inst.extract 0 4).toList) (xs := (inst.extract 4 inst.size).toList)
    (A := if inst.size < 4 then 8#64 else ipA m0 + 64#64)
    (by decide) (by decide) (by decide) (by decide) rfl (fun st hm1 hfr1 ↦ ?_)
    (by simp only [Array.length_toList, Array.size_extract]; omega)
    fun st m4 hm4 hmid4 hbuf4 hx4 hb4 hc4 hk4 hcs4 ↦ ?_
  · have hd : st.dmem = m3.dmem := hm1.dmem_eq hwf3 rfl
    refine ⟨?_, ?_, by rw [hd, hd3]; simpa using hbuf2,
      (split_ews (inst_at h hn hfr1)).2, ?_, ?_⟩
    · rw [show st.regs.X1 = st.regs.getXReg .X1 from rfl, hm1.regs .X1 _ rfl]
      have := hmid3.regs.x26; rw [← n3] at this; exact this
    · rw [show st.regs.X2 = st.regs.getXReg .X2 from rfl, ← UInt64.toNat_toBitVec,
        hm1.regs .X2 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs, UInt64.toNat_toBitVec, hmid3.regs.x25,
        Array.length_toList, Array.size_extract, Nat.min_self]
      omega
    · split
      · simp only [Array.length_toList, Array.size_extract]
        refine ⟨fun i hi ↦ absurd hi (by omega), ?_⟩
        unfold NoWrap; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
      · exact readable_of (ok_ip h) hn.iW hfr1.kept (o := 64) (by simp; omega)
    · unfold Apart; rw [l2592]; simp only [Array.length_toList, Array.size_extract]
      split
      · simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
      · rcases NativeRustcVm.toNat_add_ofNat_le (a := ipA m0) (i := 64) (by omega) with e | e
        · rw [e]
          obtain h1 | h1 := hn.iS <;> omega
        · rw [e.1]; omega
  have x19' : (m4.regs.getXReg .X19).toBitVec = loc m0 2592 := by
    rw [hcs4 .X19 rfl, Match.reg_eq (matchM hn hmid3.fr) hm4 (r := .X19) rfl rfl, hcs3 .X19 rfl]
    exact x19
  have x28' : m4.regs.getXReg .X28 = w.c0 := by
    rw [hcs4 .X28 rfl, Match.reg_eq (matchM hn hmid3.fr) hm4 (r := .X28) rfl rfl, hcs3 .X28 rfl]
    exact x28
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b49Offset + b49.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b50Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b49_next]]
  refine failBranch hp hn (b50_in_code.trans hp.1 (by simp [b50])) run_b50 hmid4 rfl rfl
    (by decide) (by decide) (b := true)
    (condX0 (by rw [Env.ofMachine_regs, gx0, hx4]; rfl)) (fun hf ↦ nomatch hf)
    fun _ m5 hmid5 hd5 hcs5 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b50Offset + b50.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b51Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b50_next]]
  have hb4' : Chg m0 [] [] m2.dmem st.dmem := hd3 ▸ hb4
  have T : Chg m0 [(2592, 3176)] [] m.dmem m5.dmem := by
    rw [hd5]
    exact ((hb2.trans hc2).trans (hb4'.trans hc4)).mono (fun p hp ↦ by
      simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, false_or,
        or_self] at hp ⊢; exact hp) (fun o ho ↦ by simp at ho)
  have hkt : Kept m.dmem m5.dmem := by
    rw [hd5]; exact kept_tr hk2 (hd3 ▸ hk4)
  refine cont m5 ⟨hmid5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hw.psz, hw.slsz, ?_, hw.run⟩
  · rw [hcs5 .X19 rfl]; exact x19'
  · rw [hcs5 .X28 rfl]; exact x28'
  · rw [hd5, Array.toList_append]; exact hbuf4
  · exact T.word hn (by decide) (by decide) (by decide) hw.w80
  · exact T.word hn (by decide) (by decide) (by decide) hw.w40
  · exact T.word hn (by decide) (by decide) (by decide) hw.w64
  · exact T.word hn (by decide) (by decide) (by decide) hw.w72
  · exact T.ts hn hkt (by decide) (by decide) (by decide) hw.ts
  · exact T.cls hn (by decide) (by decide) (by decide) hw.cls
  · exact T.claim hn (by decide) (by decide) (by decide) hw.claim
  · exact T.wts hn (by decide) (by decide) (by decide) (by decide) hw.wts
  · exact T.ews hn (by decide) (o := 2496) (k := 96) (by decide) (by decide)
      (by simp [Array.length_toList, hw.slsz]) hw.slot

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
