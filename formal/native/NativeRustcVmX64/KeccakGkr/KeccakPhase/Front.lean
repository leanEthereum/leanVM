module

public import NativeRustcVmX64.KeccakGkr.KeccakPhase.Nums
public import NativeRustcX64.Spec.Mem
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Got

/-!
# `keccak_phase` up to `verify_keccak`

`b0` (the prologue, the 25 lanes zeroed at frame offset `32`, the values' bounds: the lanes never
past the slice), `b1` (`memcpy`'s arguments: the present lanes from the values' `KECCAK_OUT`) and
`memcpy`: at `b2` (`AtVK`), the output lanes at `32`, the arguments in the callee-saved registers,
memory changed only in the frame.
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.KeccakPhase NativeRustcVmX64.Transcript
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVmX64.KeccakGkr.Fn

@[expose] public section

/-- **At `verify_keccak`'s arguments** (`b2`). -/
structure AtVK (m0 : MachineData) (values : Array EW) (d : MachineData) : Prop where
  body : Body m0 480 488 slots (W1 m0) 24 d
  rbx : reg d .rbx = reg m0 .rdx
  rbp : reg d .rbp = reg m0 .rsi
  r12 : reg d .r12 = reg m0 .r9
  r13 : reg d .r13 = reg m0 .rdi
  r14 : reg d .r14 = reg m0 .rcx
  r15 : reg d .r15 = reg m0 .r8
  lanes : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 480) 32) (lanes values).toList

end

public section

variable [Host] {k : Nat} {m0 : MachineData}

/-- **`keccak_phase` up to `verify_keccak`.** -/
theorem front (hp : Placed code k) (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {a : DecArea} (hS : StackOk m0 keccakPhaseStack) (hn : Nums a m0)
    (hevm : NativeRustcVm.Mapped m0.dmem (reg m0 .rdx) 11808) {values : Array EW}
    (hgot : GotAt m0 keccakPhaseStack [(reg m0 .rdx, 11808)] ["memcpy"])
    (h40 : 40 ≤ values.size) (h92 : values.size ≤ 92)
    (hv0 : NativeRustcVm.BufEWAt m0.dmem (off (reg m0 .rdx) 10328) 92 values.toList) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakPhase.b2Offset) ∧ AtVK m0 values st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.KeccakPhase.b0Offset)⟩ := by
  have g := geo1 hS
  have hB := hn.hB
  have hTop := hn.top
  have heW := hn.eW
  have heS : (stackBelow m0 480).toNat + 488 ≤ (reg m0 .rdx).toNat ∨
      (reg m0 .rdx).toNat + 11808 ≤ (stackBelow m0 480).toNat := by
    have h1 := hn.eS; have h2 := hn.hK; have hKV := kps_eq; unfold Sep at h1; omega
  have hoffB : ∀ j, j < 488 → (off (stackBelow m0 480) j).toNat = (stackBelow m0 480).toNat + j :=
    fun j hj ↦ toNat_off (by omega)
  have hoffE : ∀ j, j < 11808 → (off (reg m0 .rdx) j).toNat = (reg m0 .rdx).toNat + j :=
    fun j hj ↦ toNat_off (by omega)
  have hlv : values.toList.length = values.size := Array.length_toList
  have hg := hgot.1 "memcpy" (by simp)
  have hgf : NativeRustcVm.Apart (gotAddr "memcpy") 8 (stackBelow m0 480) 488 :=
    apart_frame hg.2.2.1 hS.1 (by rw [kps_eq]; omega)
  have hge := hg.2.2.2 (reg m0 .rdx, 11808) (by simp)
  have hwf0 : (fenv m0 m0 480 488 [(reg m0 .rdx, 11808), (gotAddr "memcpy", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakPhase.b1Offset + b1.length)).toBitVec).WF := by
    apply Env.wf_of
    · exact ⟨⟨g.map, by change (stackBelow m0 480).toNat + 488 ≤ 2 ^ 64; omega⟩,
        ⟨hevm, heW⟩, ⟨hgot.mapped (by simp), hg.2.1⟩, trivial⟩
    · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_pair.mpr (Apart.symm' hge)⟩
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact heS
      · exact Apart.symm' hgf
  have hm0 : Match (fenv m0 m0 480 488 [(reg m0 .rdx, 11808), (gotAddr "memcpy", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakPhase.b1Offset + b1.length)).toBitVec) entryS m0 := by
    apply Match.withKnownBytes
    · exact match_ofMachine ⟨rfl, rfl, rfl, trivial⟩
        ⟨((eval_ptr0' 480).trans off_frame_F).symm, known_ptr rfl rfl, trivial⟩
        trivial trivial ⟨by simp [Sym.eval, Env.base, gotAddr], trivial⟩
    · intro i hi
      simp only [Nat.zero_add]
      change m0.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) =
        some (byteOf (Labels.label "memcpy").toBitVec i)
      exact hgot.byte (l := "memcpy") (by simp) hi
  have hlen0 : (lenS.eval (fenv m0 m0 480 488 [(reg m0 .rdx, 11808), (gotAddr "memcpy", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakPhase.b1Offset + b1.length)).toBitVec)).toNat = values.size := by
    show (Env.load _ 1 10328 8).toNat = _
    rw [load_ofMachine (b := reg m0 .rdx) rfl hv0.2.1]
    simp only [Array.length_toList, Nat.toUInt64_eq]
    show (UInt64.ofNat values.size).toNat = _
    rw [UInt64.toNat_ofNat']
    omega
  obtain ⟨hc0, hsrc, hnS⟩ := chain hlen0 h40 (by omega)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun st0 hm0' hpc0 ↦ ?_
  simp only [PcOk, hc0, Bool.false_eq_true, ↓reduceIte] at hpc0
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf0 (fun _ _ ↦ rfl)
    (hpc0.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakPhase.b0_next)) hm0' fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hs1sp, hs1di, hs1si, hs1dx, hs1bx, hs1bp, hs1r12, hs1r13, hs1r14, hs1r15, hs1sl, hs1z,
    hs1w⟩ := ok_s1
  have hb1 : Body m0 480 488 slots (W1 m0) 16 st1.data :=
    Body.prologue g hwf0 hm1 (o := 16) hs1sp hs1sl fun w hw ↦ ⟨(hs1w w hw).1, (hs1w w hw).2.2⟩
  have rdi1 : reg st1.data .rdi = off (stackBelow m0 480) 32 :=
    (hm1.regs .rdi _ hs1di).trans (eval_ptr0' 32)
  have rsi1 : reg st1.data .rsi = off (reg m0 .rdx) 10976 := (hm1.regs .rsi _ hs1si).trans hsrc
  have rdx1 : (reg st1.data .rdx).toNat = 16 * min (values.size - 40) 25 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hs1dx]; exact hnS
  have hmf1 : NativeRustcVm.Mapped st1.data.dmem (stackBelow m0 480) 488 :=
    NativeRustcVm.Transcript.Mapped.keeps g.map hb1.kept
  have hme1 : NativeRustcVm.Mapped st1.data.dmem (reg m0 .rdx) 11808 :=
    NativeRustcVm.Transcript.Mapped.keeps hevm hb1.kept
  have hsp1 : rspOf st1.data = off (stackBelow m0 480) 16 := hb1.sp
  have hn400 : 16 * min (values.size - 40) 25 ≤ 400 := by omega
  have hpre1 : MemcpyPre st1.data := by
    unfold MemcpyPre
    dsimp only
    rw [rdi1, rsi1, rdx1]
    refine ⟨⟨Nat.zero_le _, by rw [hsp1, hoffB 16 (by omega)]; omega, ?_⟩,
      mapped_off hmf1 (by omega), mapped_off hme1 (by omega), ?_, ?_, ?_, ?_⟩
    · rw [show rspOf st1.data - BitVec.ofNat 64 0 = off (stackBelow m0 480) 16 by
        rw [hsp1]; exact BitVec.sub_zero _]
      exact mapped_off hmf1 (by omega)
    · show _ ≤ _; rw [hoffB 32 (by omega)]; omega
    · show _ ≤ _; rw [hoffE 10976 (by omega)]; omega
    · show _ ∨ _; rw [hoffB 32 (by omega), hoffE 10976 (by omega)]; omega
    · show _ ∨ _; rw [hoffB 32 (by omega), hsp1, hoffB 16 (by omega)]; omega
  refine call_then hpc1 hmemcpy hpre1 fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨-, hcp, hso, hsv⟩ := hpost
  rw [rdi1, rsi1, rdx1] at hcp
  rw [rdi1, rdx1] at hso
  have hb2 : Body m0 480 488 slots (W1 m0) 24 st2.data :=
    Body.call (o := 16) g hb1 hsv hrsp2 hso fun q hq ↦ by
      have := inR_nat (by rw [hoffB 32 (by omega)]; omega) hq
      rw [hoffB 32 (by omega)] at this
      unfold Fn.Top
      constructor <;> omega
  -- The output lanes.
  have hz : ∀ i < 50, NativeRustcVm.WordAt st1.data.dmem
      (off (stackBelow m0 480) 32 + BitVec.ofNat 64 (8 * i)) 0 := by
    intro i hi
    have := wordAt_write hm1 (r := 0) (b := stackBelow m0 480) (sz := 488) (o := 32 + 8 * i) rfl
      (by omega) (v := .lit 0) fun t ht ↦ by
        have h := hs1z (8 * i + t) (by omega)
        rwa [show 32 + (8 * i + t) = 32 + 8 * i + t by omega,
          show (8 * i + t) % 8 = t by omega] at h
    rw [off_add]
    exact this
  have hv1 : NativeRustcVm.EWsAt st1.data.dmem (off (reg m0 .rdx) 10336) values.toList := by
    have h := hv0.2.2
    rw [show off (reg m0 .rdx) 10328 + 8#64 = off (reg m0 .rdx) 10336 from off_add _ _ _] at h
    refine ews_keep h hb1.same (by rw [hoffE 10336 (by omega), hlv]; omega) fun q hq ↦ ?_
    rw [hoffE 10336 (by omega), hlv]
    obtain ⟨h1, h2⟩ := hq
    omega
  have hlanes := lanes_at (d := st1.data.dmem) (d' := st2.data.dmem) (fb0 := off (stackBelow m0 480) 32)
    (vb := off (reg m0 .rdx) 10336) (by rw [hoffB 32 (by omega)]; omega) hz hv1 h40
    (by rw [off_add]; exact hcp) hso
  refine .done _ ⟨hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakPhase.b1_next), ⟨hb2, ?_, ?_, ?_, ?_, ?_, ?_,
    hlanes⟩⟩
  · exact (hsv.1 .rbx rfl).trans ((hm1.regs .rbx _ hs1bx).trans (eval_ptr rfl))
  · exact (hsv.1 .rbp rfl).trans (hm1.regs .rbp _ hs1bp)
  · exact (hsv.1 .r12 rfl).trans (hm1.regs .r12 _ hs1r12)
  · exact (hsv.1 .r13 rfl).trans (hm1.regs .r13 _ hs1r13)
  · exact (hsv.1 .r14 rfl).trans (hm1.regs .r14 _ hs1r14)
  · exact (hsv.1 .r15 rfl).trans (hm1.regs .r15 _ hs1r15)

end

end NativeRustcVmX64.KeccakGkr.KeccakPhase
