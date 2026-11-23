module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldBase

/-!
# `keccak_open`'s fold: a row copied

A block from `pS ks` that calls `memcpy` of row `r` of the rows into the buffer at the frame's `D`
(`copyRow`): the buffer then holds the row, the rows and the frame's other bytes are kept.
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

@[expose] public section

/-- A copy block's result: `memcpy` of `1024` bytes from `v` to the frame's `D`, nothing written,
the known registers `ks'` after it. -/
def CopyOk (t : Nat) (ks' : List (XReg × Sym)) (D : Nat) (v : Sym) (S : SState) : Bool :=
  S.reg .X0 == some (.ptr 0 D) && S.reg .X1 == some v && S.reg .X2 == some (.lit 1024) &&
    stable v && S.mem.isEmpty && regsOk t S ks'

end

public section

variable [NativeRustcArm.Host] {k : Nat} {c : Cx} {m0 : MachineData}

/-- **A row copied** into the buffer at the frame's `D`. -/
theorem copyRow (hp : Placed code k)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    {ks ks' : List (XReg × Sym)} (hw : wfK ks = true) {t : Nat} (ht : t < c.sl.size)
    {vars : Nat → BitVec 64} (hv0 : vars 0 = (c.sl.getD t 0).c0.toBitVec)
    (hv1 : vars 1 = (c.sl.getD t 0).c1.toBitVec)
    {bC : List Directive} {kC : Nat} (hin : bC.IsInfixAt code kC) (hne : bC ≠ [])
    {SC : SState} (hx : exec bC (pS ks) = some (SC, .call NativeRustcVmArm.Vm.Memcpy.entryLabel)) {D : Nat}
    (hD : 56 ≤ D ∧ D + 1024 ≤ 2128) {v : Sym} (hok : CopyOk t ks' D v SC = true) {r : Nat}
    (hr : r < 64) (hv : v.eval (Env.ofMachine m0 (envR m0) vars) =
      rwA m0 + BitVec.ofNat 64 (1024 * r))
    {G : Nat → EW} {s : MachineState} (hpc : s.pc = Host.addrOf (k + kC))
    (hmid : Mid c m0 s.data) (hk : KAt m0 vars ks s.data)
    (hrows : ElemsAt s.data.dmem (rwA m0) G 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + kC + bC.length) ∧
      Mid c m0 s'.data ∧ KAt m0 vars ks' s'.data ∧ ElemsAt s'.data.dmem (rwA m0) G 4096 ∧
      ElemsAt s'.data.dmem (fbA m0 + BitVec.ofNat 64 D) (fun z ↦ G (64 * r + z)) 64 ∧
      ∀ (o' : Nat) (f : Nat → EW), o' + 1024 ≤ D ∨ D + 1024 ≤ o' → o' + 1024 ≤ 2224 →
        ElemsAt s.data.dmem (fbA m0 + BitVec.ofNat 64 o') f 64 →
        ElemsAt s'.data.dmem (fbA m0 + BitVec.ofNat 64 o') f 64) s := by
  have hn := ok.nums
  have hN := hn.hN
  have hrS := hn.rS
  have hrW := hn.rW
  have hsl := spN_lt m0
  have hfb := fbA_toNat hn
  simp only [CopyOk, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hok
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, hvs⟩, hmem⟩, hk'⟩ := hok
  have hsp : SC.sp = .ptr 0 0 := by
    simp only [regsOk, Bool.and_eq_true, beq_iff_eq] at hk'; exact hk'.2
  have hwf := wf_fold (vars := vars) ok hmid.body
  have hm := match_pS ok hk hw hmid.sw
  refine exec_at (hin.trans hp.1 hne) hx hwf hpc hm fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    hmid.body.of_block hm hm1 hwf rfl all_slots (by simp [keepsAll, hmem, hsp, pS, init])
  have hd1 : s1.data.dmem = s.data.dmem := hm1.dmem_eq hwf hmem
  have hmid1 := hmid.of_dmem hb1 hd1
  have hk1 : KAt m0 vars ks' s1.data := KAt.after hm1 ht hv0 hv1 hmid hk'
  have e0 : s1.data.regs.X0.toBitVec = fbA m0 + BitVec.ofNat 64 D := by
    show (s1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1.regs .X0 _ h0]
    show fbA m0 + BitVec.ofInt 64 (D : Int) = _
    rw [BitVec.ofInt_natCast]
  have e1 : s1.data.regs.X1.toBitVec = rwA m0 + BitVec.ofNat 64 (1024 * r) := by
    show (s1.data.regs.getXReg .X1).toBitVec = _
    rw [hm1.regs .X1 _ h1, eval_of s.data m0 hvs, hv]
  have e2 : s1.data.regs.X2.toNat = 1024 := by
    show (s1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm1.regs .X2 _ h2]; rfl
  have eD : (fbA m0 + BitVec.ofNat 64 D).toNat = spN m0 - 2224 + D := fbA_add hn (by omega)
  have eR : (rwA m0 + BitVec.ofNat 64 (1024 * r)).toNat = (rwA m0).toNat + 1024 * r :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  obtain ⟨hfm, hfw, -⟩ := frame_ok ok.stack (show 2224 ≤ keccakOpenStack by decide)
  have hfok : NativeRustcVm.Region.Ok s1.data.dmem ⟨fbA m0, 2224⟩ :=
    ⟨Mapped.kept' hfm hb1.kept, hfw⟩
  obtain ⟨hdm, hdw⟩ := sub_ok hfok (o := D) (n := 1024) (by omega)
  obtain ⟨hsm, hsw⟩ := rows_ok ok hb1 (o := 1024 * r) (n := 1024) (by omega)
  refine call_then hpc1 hmemcpy ⟨?_, ?_, ?_, ?_, ?_⟩ fun s2 hpc2 hpost ↦ ?_
  · rw [e0, e2]; exact hdm
  · rw [e1, e2]; exact hsm
  · rw [e0, e2]; exact hdw
  · rw [e1, e2]; exact hsw
  · rw [e0, e1, e2]
    unfold Apart
    rw [eD, eR]
    omega
  obtain ⟨-, hcp, hso, hsv⟩ := hpost
  rw [e0, e1, e2] at hcp
  rw [e0, e2] at hso
  have hR : ∀ q, InRange (fbA m0 + BitVec.ofNat 64 D) 1024 q →
      spN m0 - 2224 + D ≤ q.toNat ∧ q.toNat < spN m0 - 2224 + D + 1024 := fun q h ↦ by
    rw [inRange_nat (by rw [eD]; omega), eD] at h
    exact h
  have hb2 : Body m0 s2.data :=
    hb1.call_local (n := 0) (lo := 2128) ok.stack (by decide) slots_le (by decide) ok.wsOff hso
      (fun q h ↦ Or.inr (Or.inr (inRange_mono h (by omega)))) hsv
  have hmid2 : Mid c m0 s2.data :=
    hmid1.keep hn hb2 hsv.2.2 hso fun q h ↦ by
      have := hR q h
      unfold Safe
      omega
  have hso' : SameOutside s.data.dmem s2.data.dmem
      (fun q ↦ spN m0 - 2224 + D ≤ q.toNat ∧ q.toNat < spN m0 - 2224 + D + 1024) := by
    rw [← hd1]; exact NativeRustcVm.SameOutside.mono hso hR
  refine .done _ ⟨hpc2, hmid2, hk1.call (wfK_of_regsOk hk') hsv, ?_, ?_, ?_⟩
  · exact ElemsAt.keepN hrows hso' (by omega) fun q hq ↦ by omega
  · intro z hz
    have h := hrows (64 * r + z) (by omega)
    rw [show 16 * (64 * r + z) = 1024 * r + 16 * z by omega, ← NativeRustcVm.addr_add_add,
      ← hd1] at h
    exact bytes_copy h hcp (by rw [NativeRustcVm.length_ewBytes]; omega)
  · intro o' f ho ho' h
    have e := fbA_add hn (o := o') (by omega)
    exact ElemsAt.keepN h hso' (by rw [e]; omega) fun q hq ↦ by rw [e]; omega

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
