module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.ClaimMem
public import NativeRustcVmX64.KeccakGkr.FirstClaim.Keep
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-! # Storing the new value and copying the instance weights -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea off)

public section

variable [Host] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW} {k : Nat}

theorem claim_copy (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (hpt : pt.size ≤ 30)
    {d : MachineData} (hb : Body m0 (outs m0) 24 d) (h : TailLive m0 a c ch b pt lp t s6 d.dmem)
    (hv : ewArg (reg d .rax) (reg d .rdx) = b * (t.getD 1 0 + b * t.getD 2 0))
    {R : MachineState → Prop}
    (cont : ∀ d', Body m0 (outs m0) 24 d' → TailLive m0 a c ch b pt lp t s6 d'.dmem →
      reg d' .rbx = cA m0 →
      NativeRustcVm.EWAt d'.dmem (cA m0) (t.getD 0 0 + b * (t.getD 1 0 + b * t.getD 2 0)) →
      NativeRustcVm.BufEWAt d'.dmem (cA m0 + BitVec.ofNat 64 16) 16
        (keccakInstanceWeights ch).toList →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b83Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b82Offset)⟩ := by
  have g := geo_of hpre
  have cx := ctx hpre (F := 2000) (by decide)
  have h96 := h.fw (96, .ofBitVec (cA m0)) (by apply List.mem_append_left; fw_mem)
  have h224 := h.fw (224, .ofBitVec (cA m0 + BitVec.ofNat 64 16))
    (by apply List.mem_append_left; fw_mem)
  have h192 := h.fw (192, (t.getD 0 0).c0) (by apply List.mem_append_right; fw_mem)
  have h200 := h.fw (200, (t.getD 0 0).c1) (by apply List.mem_append_right; fw_mem)
  have hgot := pre_got hpre
  have hg := hgot.1 "memcpy" (by simp)
  have hgf : Apart (gotAddr "memcpy") 8 (stackBelow m0 2016) 2024 :=
    apart_frame hg.2.2.1 hpre.1.1 (by rw [stack_eq]; decide)
  have hgc : Apart (gotAddr "memcpy") 8 (cA m0) 768 := hg.2.2.2 (cA m0, 768) (by simp)
  have hf := frame_ok (pre_stack hpre) hb.fr.kept
  have hc := areas_ok (pre_areas hpre) (r := ⟨cA m0, 768⟩) (.inl (by simp))
  have hwf : (envB m0 d [(cA m0, 768), (gotAddr "memcpy", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b82Offset + b82.length)).toBitVec).WF := by
    apply frame_wf hf
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨NativeRustcVm.Transcript.Mapped.keeps hc.1 hb.fr.kept, hc.2⟩
      · exact ⟨NativeRustcVm.Transcript.Mapped.keeps (hgot.mapped (by simp)) hb.fr.kept, hg.2.1⟩
    · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_pair.mpr (Apart.symm' hgc)⟩
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact claim_apart g
      · exact Apart.symm' hgf
  have hm : Match (envB m0 d [(cA m0, 768), (gotAddr "memcpy", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b82Offset + b82.length)).toBitVec) claimCopyS d := by
    apply Match.withKnownBytes
    · exact match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial
        ⟨by show Env.load _ 0 96 8 = cA m0 + BitVec.ofInt 64 0
            rw [fload8 h96]; simp,
          by simp [Sym.eval, Env.base, gotAddr], trivial⟩
    · intro i hi
      simp only [Nat.zero_add, Sym.eval, Env.base_ofMachine_eq, Env.ofMachine_mem0]
      change d.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) = _
      rw [hb.got_bytes hpre (fun _ h ↦ h) "memcpy" (by simp) i hi]
      exact hgot.byte (by simp) hi
  refine Body.blk (o' := 16) g hb hwf (blk hp b82_in_code (by simp [b82])) e82
    (fun _ _ ↦ rfl) hm (by decide +kernel)
    (fun w hw hr p n he q h1 h2 ↦ Or.inr (Or.inl
      (hexClaim g (by decide +kernel) w hw hr p n he q h1 h2)))
    fun st hm1 hpc1 hb1 _ ↦ ?_
  have h1 := h.claimBlk hpre hpt hwf hm1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hbxx := (hm1.regs .rbx _ rfl).trans (fload8 h96)
  have hdi : reg st.data .rdi = cA m0 + 16#64 :=
    (hm1.regs .rdi _ rfl).trans (fload8 h224)
  have hsi : reg st.data .rsi = off (stackBelow m0 2016) 1704 :=
    hm1.regs .rsi (.ptr 0 1704) rfl
  have hdx : reg st.data .rdx = BitVec.ofNat 64 264 := hm1.regs .rdx (.lit 264) rfl
  have hew : ewArg
      (BinOp.apply .xor .W64 (reg d .rax) (t.getD 0 0).c0.toBitVec)
      (BinOp.apply .xor .W64 (reg d .rdx) (t.getD 0 0).c1.toBitVec) =
      t.getD 0 0 + b * (t.getD 1 0 + b * t.getD 2 0) := by
    rw [NativeRustcVmX64.Arrays.xor_eval, NativeRustcVmX64.Arrays.xor_eval,
      NativeRustcVmX64.Arrays.ewArg_xor, ewArg_ew, hv, ew_add_comm']
  have hval1 : NativeRustcVm.EWAt st.data.dmem (cA m0)
      (t.getD 0 0 + b * (t.getD 1 0 + b * t.getD 2 0)) := by
    rw [NativeRustcVm.ewAt_iff]
    constructor
    · have hw := NativeRustcVmX64.Sumcheck.wordAt_written hm1 (r := 1) rfl
        (o := 0) (v := .bin .xor .W64 (.reg .rax) (.load 0 192 8)) (by decide) (by decide +kernel)
        (w := (t.getD 0 0 + b * (t.getD 1 0 + b * t.getD 2 0)).c0) (by
          simp only [Sym.eval]
          rw [fload8 h192]
          exact ewArg_c0 hew)
      simpa using hw
    · exact NativeRustcVmX64.Sumcheck.wordAt_written hm1 (r := 1) rfl
        (o := 8) (v := .bin .xor .W64 (.reg .rdx) (.load 0 200 8)) (by decide) (by decide +kernel)
        (w := (t.getD 0 0 + b * (t.getD 1 0 + b * t.getD 2 0)).c1) (by
          simp only [Sym.eval]
          rw [fload8 h200]
          exact ewArg_c1 hew)
  have hd := claimSlice hpre (fun _ h ↦ h) hb1 (Sk := 0) (by decide)
    (o := 16) (n := 264) (by decide) (by decide)
  have hs := frame_ok (pre_stack hpre) hb1.fr.kept
  have hsrc : NativeRustcVm.Mapped st.data.dmem (off (stackBelow m0 2016) 1704) 264 := by
    intro i hi
    rw [NativeRustcVm.Transcript.off_add]
    exact hs.1 (1704 + i) (by omega)
  have hpre1 : MemcpyPre st.data := by
    dsimp only [MemcpyPre]
    rw [hdi, hsi, hdx]
    refine ⟨cx.stackOk (hb1.at_ hpre (fun _ h ↦ h) (by decide)) (by decide),
      hd.1, hsrc, hd.2.1, ?_, ?_, ?_⟩
    · have hn := g.top
      change (stackBelow m0 2016 + BitVec.ofNat 64 1704).toNat + 264 ≤ 2 ^ 64
      rw [g.fa (by decide)]
      omega
    · have hn := g.hN
      have ha := g.hcs
      unfold Apart
      change (cA m0 + BitVec.ofNat 64 16).toNat + 264 ≤
          (stackBelow m0 2016 + BitVec.ofNat 64 1704).toNat ∨
        (stackBelow m0 2016 + BitVec.ofNat 64 1704).toNat + 264 ≤
          (cA m0 + BitVec.ofNat 64 16).toNat
      rw [g.ca (by decide), g.fa (by decide)]
      omega
    · simpa [NativeRustcVm.Apart, Apart, stackBelow] using hd.2.2
  refine call_then hpc1 hmemcpy hpre1 fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨_, hcopy, hs2, hsv2⟩ := hq2
  rw [hdi, hsi, hdx] at hcopy
  rw [hdi, hdx] at hs2
  have hso := NativeRustcVm.SameOutside.mono hs2
    (fun q hq ↦ Or.inr hq : ∀ q, InRange (cA m0 + BitVec.ofNat 64 16) 264 q →
      InRange (stackBelow st.data 0) 0 q ∨ InRange (cA m0 + BitVec.ofNat 64 16) 264 q)
  have hb2 := Body.callX hpre (fun _ h ↦ h) hb1 hsv2 hrsp2 (by decide) hso
    (fun _ hq ↦ Or.inl (Or.inr (Or.inl (claim_subrange g (by decide) hq))))
  have hf2 := frSame_call g hb1 (Sk := 0) (o := 24) (n := 1944)
    (by decide) hso (by decide) (by decide)
    (by
      intro q hq hf
      apply claim_not_fr hpre (claim_subrange g (by decide) hq)
      have hn := g.hN
      have ht := g.top
      rw [Sym.inRange_iff (by rw [g.fa (by decide)]; omega), g.fa (by decide)] at hf
      rw [Sym.inRange_iff (by rw [g.fbN]; omega), g.fbN]
      omega)
  have h2 := h1.claim hpre hpt (hf2.sub (by decide) (by decide)) hsv2.2
    (NativeRustcVm.SameOutside.mono hs2
      fun _ hq ↦ Or.inr (claim_subrange g (by decide) hq))
  have hv2 := NativeRustcVm.Layout.EWAt.of_same hval1
    (by simpa using (claim_same hpre (o := 16) (n := 264) (p := 0) (len := 16)
      (by decide) (by decide) (Or.inl (by decide))
      (NativeRustcVm.SameOutside.mono hs2 fun _ hq ↦ Or.inr hq)))
    (by decide)
  have hmu2 := NativeRustcVmX64.KeccakGkr.FirstClaim.BufEWAt.copy h1.mu hcopy
  exact at_pc hpc2 (cont st2.data hb2 h2 ((hsv2.1 .rbx rfl).trans hbxx) hv2 hmu2)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
