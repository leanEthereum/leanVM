module

public import NativeRustcVmArm.Code.Vm.RingTarget.Names
public import NativeRustcVmArm.Ring.Switch.Body

/-!
# `ring_switch`: the target and its store

`stepTarget` (`b4`): `ring_target(s, f, g)` (`G4`); `stepStore` (`b5`): the target at the
`RingW`'s byte `0`, `Some(())` in X0 (`G5`).
-/

namespace NativeRustcVmArm.Ring.Switch

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.RingSwitch

@[expose] public section

/-- `s`, read at the entry. -/
def sOf (m0 : MachineData) : Array EW := arr m0 m0.regs.X1 coeffCount

/-- **After the target**: it in X0, X1. -/
structure G4 (a : DecArea) (s2 : TState) (xs : Array EW) (m0 m : MachineData) : Prop where
  fr : SFr m0 m
  x19 : m.regs.getXReg .X19 = m0.regs.X2
  x22 : m.regs.getXReg .X22 = 1
  ts : TStateAt m.dmem (tA m0) a s2
  coef : NativeRustcVm.EWsAt m.dmem (oA m0 + 16#64) (ringCoefficients (fOf xs) (gOf xs)).toList
  tgt : (⟨m.regs.X0, m.regs.X1⟩ : EW) = ringTarget (sOf m0) (fOf xs) (gOf xs)

/-- **After the store**: the `RingW` and the `TState` written, `Some(())` in X0. -/
structure G5 (a : DecArea) (s2 : TState) (xs : Array EW) (m0 m : MachineData) : Prop where
  fr : SFr m0 m
  x0 : m.regs.X0 = okWord true
  ts : TStateAt m.dmem (tA m0) a s2
  ring : RingWAt m.dmem (oA m0) (ringTarget (sOf m0) (fOf xs) (gOf xs))
    (ringCoefficients (fOf xs) (gOf xs))

end

public section

variable {m0 : MachineData} {a : DecArea} {s : TState}

theorem fOf_size {xs : Array EW} (h : xs.size = 16) : (fOf xs).size = 8 := by
  simp [fOf, h]

theorem gOf_size {xs : Array EW} (h : xs.size = 16) : (gOf xs).size = 8 := by
  simp [gOf, h]

theorem coef_size {xs : Array EW} (h : xs.size = 16) :
    (ringCoefficients (fOf xs) (gOf xs)).size = coeffCount := by
  have := ringCoefficients_size (fOf xs).toList (gOf xs)
  rw [Array.toArray_toList, gOf_size h, Array.length_toList, fOf_size h] at this
  exact this

/-- A byte the store wrote: in region 1's first `16` bytes. -/
theorem written_r1 [Labels] {env : Env} {S : SState} {q b : BitVec 64} {n : Nat}
    (hq : Written env S q) (h1 : env.regions[1]? = some (b, n))
    (hm : S.mem.all (fun w ↦ w.r == 1 && decide (w.off + w.n ≤ 16)) = true) :
    b.toNat ≤ q.toNat ∧ q.toNat < b.toNat + 16 := by
  obtain ⟨w, hw, b', sz, hb, h1', h2⟩ := hq
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨hr, hn⟩ := hm w hw
  rw [hr, h1] at hb
  cases hb
  omega

section
variable [Labels]

/-- `s`'s bytes are the entry's in every state of the frame. -/
theorem s_same (h : RingSwitchPre a s m0) {m : MachineData} (hfr : SFr m0 m) {j : Nat}
    (hj : j < 16 * coeffCount) :
    m.dmem.get? (sA m0 + BitVec.ofNat 64 j) = m0.dmem.get? (sA m0 + BitVec.ofNat 64 j) := by
  have hsw := h.2.2.2.2.2.1.1.2
  refine hfr.same _ fun hq ↦ ?_
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange_add h.2.2.2.2.2.1.2 hsw (nw_stack h) hj hq
  · exact NativeRustcVm.Apart.not_inRange_add h.2.2.2.2.2.2.2 hsw (o_noWrap h) hj hq
  · exact NativeRustcVm.Apart.not_inRange_add h.2.2.2.2.2.2.1 hsw (t_noWrap h) hj hq

/-- The store's writes: region 1's first `16` bytes, the outputs. -/
theorem writeOk_r1 (h : RingSwitchPre a s m0) {m : MachineData} {S : SState}
    (hall : S.mem.all (fun w ↦ w.r == 1 && decide (w.off + w.n ≤ 16)) = true) :
    ∀ w ∈ S.mem, WriteOk (Env.ofMachine m [(fb m0, 432), (oA m0, 16)]) 432 slots (outs m0) w := by
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hall
  intro w hw
  obtain ⟨hr, hn⟩ := hall w hw
  refine .inr ⟨by rw [hr]; decide, fun b sz hb ↦ ?_⟩
  rw [hr] at hb
  change some (oA m0, 16) = some (b, sz) at hb
  cases hb
  have := o_noWrap h
  unfold NoWrap ringWBytes coeffCount at this
  exact ⟨hn, fun i hi ↦ .inl (NativeRustcVm.inRange_add (by unfold ringWBytes coeffCount; omega)
    (by unfold ringWBytes coeffCount; omega))⟩

/-- The store's words: X0, X1 at region 1's bytes `0`, `8`. -/
def storeOk (S : SState) : Bool :=
  (List.range 8).all fun i ↦ findWrite 1 (0 + i) S.mem == some (.reg .X0, i) &&
    findWrite 1 (8 + i) S.mem == some (.reg .X1, i)

theorem store_ewAt {m st : MachineData} {S : SState}
    (hm1 : Match (Env.ofMachine m [(fb m0, 432), (oA m0, 16)]) S st) (hc : storeOk S = true) :
    NativeRustcVm.EWAt st.dmem (oA m0) ⟨m.regs.getXReg .X0, m.regs.getXReg .X1⟩ := by
  simp only [storeOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hc
  have w0 := hm1.bytesAt_write (r := 1) (o := 0) (n := 8) (b := oA m0) (sz := 16) rfl (by omega)
    (v := .reg .X0) fun i hi ↦ (hc i hi).1
  have w1 := hm1.bytesAt_write (r := 1) (o := 8) (n := 8) (b := oA m0) (sz := 16) rfl (by omega)
    (v := .reg .X1) fun i hi ↦ (hc i hi).2
  rw [wordBytes_reg] at w0 w1
  rw [NativeRustcVm.addr_add_zero] at w0
  rw [NativeRustcVm.ewAt_iff]
  exact ⟨w0, w1⟩

end

variable [Host] {k : Nat}

/-- **The target** (`b4`). -/
theorem stepTarget (hp : Placed code k) (h : RingSwitchPre a s m0)
    (hrt : Spec (Labels.label NativeRustcVmArm.Vm.RingTarget.entryLabel) RingTargetPre RingTargetPost)
    {s2 : TState} {xs : Array EW} {m : MachineData} (hG : G3 a s2 xs m0 m)
    {R : MachineState → Prop}
    (cont : ∀ m', G4 a s2 xs m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b5Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b4Offset)⟩ := by
  have hwf := envM_wf h hG.fr
  have hm := matchM h hG.fr
  refine exec_then (hb b4_in_code (by simp [b4]) hp) run_b4 hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : SFr m0 st.data :=
    hG.fr.ofBlock hm hm1 hwf rfl rfl rfl (keep_ok (by decide) (by decide))
  have hd : st.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
  have hfw := fbw h
  have hfN := fbN h
  have hN' := hN h
  rw [stack_eq] at hN'
  have hSP := m0.regs.SP.toNat_lt
  unfold NoWrap at hfw
  have e0 : st.data.regs.X0 = m0.regs.X1 :=
    reg_of hm1 (r := .X0) (v := .reg .X20) rfl (by simp [Sym.eval, hG.x20])
  have e1 : st.data.regs.X1.toBitVec = fb m0 := by
    rw [show st.data.regs.X1 = st.data.regs.getXReg .X1 from rfl, hm1.regs .X1 (.ptr 0 0) rfl]
    simp [Sym.eval]
  have e2 : st.data.regs.X2.toBitVec = fb m0 + BitVec.ofNat 64 256 := by
    rw [show st.data.regs.X2 = st.data.regs.getXReg .X2 from rfl, hm1.regs .X2 (.ptr 0 256) rfl]
    simp only [Sym.eval]
    rw [show ((256 : Int)) = ((256 : Nat) : Int) from rfl, BitVec.ofInt_natCast]
    rfl
  have hf256 : (fb m0 + BitVec.ofNat 64 256).toNat = (fb m0).toNat + 256 :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have hpre : RingTargetPre st.data := by
    simp only [RingTargetPre, ArrOk, Readable, OffStack, e0, e1, e2, ringWidth]
    refine ⟨hfr1.stackOk h.1 (by decide) (by decide), ⟨⟨fun j hj ↦ ?_, ?_⟩, ?_⟩,
      ⟨⟨fun j hj ↦ ?_, ?_⟩, ?_⟩, ⟨⟨fun j hj ↦ ?_, ?_⟩, ?_⟩⟩
    · exact hfr1.kept _ (h.2.2.2.2.2.1.1.1 j hj)
    · exact h.2.2.2.2.2.1.1.2
    · exact s_callee h hfr1 (by decide)
    · exact hfr1.kept _ (frame_mapped h.1 (by decide) j (by omega))
    · unfold NoWrap; omega
    · have := apart_callee h hfr1 (o := 0) (n := 128) (N' := ringTargetStack) (by decide)
        (by decide)
      rwa [NativeRustcVm.addr_add_zero] at this
    · rw [NativeRustcVm.addr_add_add]
      exact hfr1.kept _ (frame_mapped h.1 (by decide) _ (by omega))
    · unfold NoWrap; omega
    · exact apart_callee h hfr1 (by decide) (by decide)
  have hnil : ∀ q, ¬InRange (0 : BitVec 64) 0 q := fun q hq ↦ by unfold InRange at hq; omega
  refine Fr.leafAt hfr1 (hN h) (N' := ringTargetStack) (by decide) keep_cs slots_le
    (outs_frame h) hrt hpc hpre
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ hq.elim
      (fun hq ↦ absurd hq (hnil q)) .inl, hq.2.2⟩)
    fun m2 hfr2 hq hcs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingSwitch.b4Offset + b4.length = k + NativeRustcVmArm.Vm.RingSwitch.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingSwitch.b4_next]]
  obtain ⟨htgt, hchg, hS⟩ := hq
  have hs : SameOutside st.data.dmem m2.dmem fun q ↦
      InRange (stackBelow st.data ringTargetStack) ringTargetStack q :=
    NativeRustcVm.SameOutside.mono hchg fun q hq ↦ hq.elim (fun hq ↦ absurd hq (hnil q)) id
  have hch : NativeRustcVm.EWsAt st.data.dmem (fb m0) xs.toList := by rw [hd]; exact hG.ch
  have hgc : NativeRustcVm.ewsOf st.data.dmem (fb m0 + BitVec.ofNat 64 256) 8 =
      xs.toList.drop 8 := by rw [hd]; exact hG.gc
  refine cont m2 {
    fr := hfr2
    x19 := (hcs .X19 rfl).trans ((Match.reg_eq hm hm1 (r := .X19) rfl rfl).trans hG.x19)
    x22 := (hcs .X22 rfl).trans ((Match.reg_eq hm hm1 (r := .X22) rfl rfl).trans hG.x22)
    ts := ts_keep h (by rw [hd]; exact hG.ts) hS.2.2 hs fun q hq ↦
      stack_within h hfr1 (by decide) hq
    coef := by
      have := out_keep h hfr1 (N' := ringTargetStack) (by decide) hs (o := 16)
        (bs := (ringCoefficients (fOf xs) (gOf xs)).toList.flatMap NativeRustcVm.ewBytes)
        (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, coef_size hG.sz]; decide)
        (by rw [hd]; exact hG.coef)
      exact this
    tgt := by
      show ewRet m2 = _
      rw [htgt]
      unfold arr
      rw [e0, e1, e2, ringWidth, arrF hch hG.sz, arrG hgc hG.sz, sOf, arr,
        NativeRustcVm.ewsOf_congr (d := m0.dmem) (a := m0.regs.X1.toBitVec) fun j hj ↦ s_same h hfr1 hj] }

/-- **The store** (`b5`). -/
theorem stepStore (hp : Placed code k) (h : RingSwitchPre a s m0) {s2 : TState} {xs : Array EW}
    {m : MachineData} (hG : G4 a s2 xs m0 m) (hsz : xs.size = 16) {R : MachineState → Prop}
    (cont : ∀ m', G5 a s2 xs m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b6Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b5Offset)⟩ := by
  have hfw := fbw h
  have how := o_noWrap h
  have hoF := o_frame h
  unfold NoWrap ringWBytes coeffCount at how
  unfold ringWBytes coeffCount at hoF
  have hwf : (Env.ofMachine m [(fb m0, 432), (oA m0, 16)]).WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hG.fr.kept _ (frame_mapped h.1 (by decide) i hi), hfw⟩,
      ⟨fun i hi ↦ hG.fr.kept _ (h.2.2.2.2.1.1 i (by unfold ringWBytes coeffCount; omega)),
        show (oA m0).toNat + 16 ≤ 2 ^ 64 by omega⟩, trivial⟩
      (List.pairwise_pair.mpr (show Apart (fb m0) 432 (oA m0) 16 by unfold Apart at *; omega))
  have hm : Match (Env.ofMachine m [(fb m0, 432), (oA m0, 16)]) storeS m :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1 (by decide) (by decide), rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hG.fr.sp]; simp [Sym.eval])
      ⟨by show (m.regs.getXReg .X19).toBitVec = _; rw [hG.x19]; simp [Sym.eval]; rfl, trivial⟩
      trivial trivial trivial
  refine exec_then (hb b5_in_code (by simp [b5]) hp) run_b5 hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : SFr m0 st.data :=
    hG.fr.ofBlockW hm hm1 hwf rfl rfl (keep_ok (by decide) (by decide)) rfl (by decide) (hN h)
      slots_le (writeOk_r1 h (by decide))
  have hd0 : st.data.regs.X0 = okWord true :=
    reg_of hm1 (r := .X0) (v := .un .trunc .W32 (.reg .X22)) rfl (by
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [hG.x22]
      rfl)
  simp only [PcOk] at hpc
  obtain ⟨d, pc⟩ := st
  simp only at hpc hfr1 hd0 hm1
  subst hpc
  rw [show k + NativeRustcVmArm.Vm.RingSwitch.b5Offset + b5.length = k + NativeRustcVmArm.Vm.RingSwitch.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingSwitch.b5_next]]
  refine cont d ⟨hfr1, hd0, ?_, ?_⟩
  · exact ts_keep h hG.ts (hm1.kept hwf) (hm1.sameOutside hwf) fun q hq ↦ .inr (by
      have := written_r1 hq rfl (by decide)
      rw [Sym.inRange_iff (o_noWrap h)]
      unfold ringWBytes coeffCount
      omega)
  · refine ⟨?_, coef_size hsz, ?_⟩
    · rw [← hG.tgt]
      exact store_ewAt hm1 (by decide)
    · refine NativeRustcVm.BytesAt.of_sameOutside hG.coef (hm1.sameOutside hwf) fun j hj hq ↦ ?_
      have := written_r1 hq rfl (by decide)
      rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by
        rw [NativeRustcVm.length_ewsBytes, Array.length_toList, coef_size hsz] at hj
        unfold coeffCount at hj
        omega)] at this
      omega

end

end NativeRustcVmArm.Ring.Switch
