module

public import NativeRustcVmX64.Top.Seed.Exec
public import NativeRustcVmX64.Top.Basic
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfFiatShamirIv.Names
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Got

/-!
# `seed` up to `memset` (x86-64)

`stage1`: from the entry, the prologue (`b0`), `keccak256_words` writing the IV at the frame's
byte 16, `b1` and `memset` zeroing its bytes 80 to 215: the state `S1`.
-/

namespace NativeRustcVmX64.Top.Seed

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Seed NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Top NativeVm.Model

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 240 := by decide
theorem slots_ge : ∀ p ∈ slots, 216 ≤ p.1 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 240

/-- After `memset`: the frame, RSP at offset `8`, the memory changed only in the stack, the IV at
the frame's byte 16, zeros at its bytes 80 to 215, the output, the state and the public input's
addresses in RBX, R14, R15. -/
structure S1 [Labels] (m0 d : MachineData) : Prop where
  frame : Frame m0 240 slots 8 d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem
    (NativeRustcVm.InRange (stackBelow m0 seedStack) seedStack)
  iv : ∀ w : List UInt64, w.length = (reg m0 .rdx).toNat →
    NativeRustcVm.WordsAt m0.dmem (reg m0 .rsi) w →
    NativeRustcVm.WordsAt d.dmem (off (fb m0) 16) (fiatShamirIv w.toArray).toList
  zeros : NativeRustcVm.BytesAt d.dmem (off (fb m0) 80) (List.replicate 136 0)
  rbx : reg d .rbx = reg m0 .rdi
  r14 : reg d .r14 = off (fb m0) 16
  r15 : reg d .r15 = reg m0 .rcx

variable [Host] {k : Nat}

/-- Loader slots are outside the whole local frame, including the return address. -/
theorem got_frame_apart {m0 : MachineData} {areas : List (BitVec 64 × Nat)}
    {symbols : List Label} (hst : StackOk m0 seedStack)
    (hg : GotAt m0 seedStack areas symbols) {l : Label} (hl : l ∈ symbols) :
    NativeRustcVm.Apart (gotAddr l) 8 (fb m0) 248 := by
  have hs := (hg.1 l hl).2.2.1
  change NativeRustcVm.Apart (gotAddr l) 8 (stackBelow m0 seedStack) (seedStack + 8) at hs
  have hn := hst.1
  have hb := stackBelow_toNat (m := m0) (n := 240) (by change 1008 ≤ _ at hn; omega)
  have hsb := stackBelow_toNat hn
  unfold NativeRustcVm.Apart at hs ⊢
  change 1008 ≤ _ at hn
  have hss : seedStack = 1008 := rfl
  rw [hss] at hsb hs
  change (gotAddr l).toNat + 8 ≤ (stackBelow m0 240).toNat ∨
    (stackBelow m0 240).toNat + 248 ≤ (gotAddr l).toNat
  omega

/-- Every intermediate seed write is below the entry stack pointer. -/
theorem got_keep {m0 d d' : MachineData} {areas : List (BitVec 64 × Nat)}
    {symbols : List Label} {writes : BitVec 64 → Prop}
    (hst : StackOk m0 seedStack) (hg : GotAt m0 seedStack areas symbols)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem writes)
    (hw : ∀ q, writes q →
      (stackBelow m0 seedStack).toNat ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat) :
    ∀ l ∈ symbols, ∀ i < 8,
      d'.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  intro l hl i hi
  apply hs
  intro h
  have hq := hw _ h
  obtain ⟨_, hgn, hgs, _⟩ := hg.1 l hl
  change NativeRustcVm.Apart (gotAddr l) 8 (stackBelow m0 seedStack) (seedStack + 8) at hgs
  have hb := stackBelow_toNat hst.1
  have hgn' : (gotAddr l).toNat + 8 ≤ 2 ^ 64 := hgn
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at hq
  unfold NativeRustcVm.Apart at hgs
  omega

/-- Both Keccak leaves use a subframe and a state inside seed's protected stack. -/
theorem got_leaf {m0 d : MachineData} {areas : List (BitVec 64 × Nat)}
    {symbols : List Label} {n bytes : Nat}
    (hst : StackOk m0 seedStack) (hg : GotAt m0 seedStack areas symbols)
    (hrc : (rcAddr, 192) ∈ areas) (hsp : rspOf d = fb m0)
    (hn : n ≤ 768) (hbytes : bytes ≤ 200)
    (hkeep : ∀ l ∈ symbols, ∀ i < 8,
      d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i)) :
    GotAt d n [(off (fb m0) 16, bytes), (rcAddr, 192)] symbols := by
  have hstn := hst.1
  have hst8 := hst.2.1
  have hsb := stackBelow_toNat hstn
  have hfb : (fb m0).toNat = (rspOf m0).toNat - 240 :=
    stackBelow_toNat (m := m0) (n := 240) (by change 1008 ≤ _ at hstn; omega)
  have hdn := stackBelow_callee hsp (show 240 + n ≤ (rspOf m0).toNat by
    change 1008 ≤ _ at hstn; omega)
  have hdb := stackBelow_toNat (m := m0) (n := 240 + n) (by
    change 1008 ≤ _ at hstn; omega)
  have ha : (off (fb m0) 16).toNat = (fb m0).toNat + 16 :=
    toNat_off (by change 1008 ≤ _ at hstn; omega)
  apply hg.transport hkeep
  · intro l hl
    have hs := (hg.1 l hl).2.2.1
    change NativeRustcVm.Apart (gotAddr l) 8 (stackBelow m0 seedStack) (seedStack + 8) at hs
    change NativeRustcVm.Apart (gotAddr l) 8 (stackBelow d n) (n + 8)
    rw [hdn]
    unfold NativeRustcVm.Apart at hs ⊢
    have hss : seedStack = 1008 := rfl
    rw [hss] at hsb hs
    omega
  · intro l hl a ha'
    rcases List.mem_cons.mp ha' with rfl | ha'
    · have hs := got_frame_apart hst hg hl
      change NativeRustcVm.Apart (gotAddr l) 8 (off (fb m0) 16) bytes
      unfold NativeRustcVm.Apart at hs ⊢
      omega
    · have he := List.mem_singleton.mp ha'
      subst a
      exact (hg.1 l hl).2.2.2 _ hrc

theorem lenSym_eval {env : Env} (h : 9 + 8 * (env.regs .rdx).toNat < 2 ^ 32) :
    (lenSym.eval env).toNat = 9 + 8 * (env.regs .rdx).toNat := by
  simp only [lenSym, Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add,
    BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- **`seed` up to `memset`.** -/
theorem stage1 (hp : Placed code k)
    (hkiv : Spec (Labels.label NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.entryLabel) Keccak256WordsIvPre Keccak256WordsIvPost)
    (hmemset : Spec (Labels.label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost) {m0 : MachineData}
    (hpre : SeedPre m0) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Seed.b2Offset) ∧ S1 m0 st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.Seed.b0Offset)⟩ := by
  obtain ⟨hst, hrc, hn32, ⟨hbcM, hbcN⟩, -, -, -, -, hbcA, hgot⟩ := hpre
  have hbcN' : (reg m0 .rsi).toNat + 8 * (reg m0 .rdx).toNat ≤ 2 ^ 64 := hbcN
  have hss : seedStack = 1008 := rfl
  have hks : keccak256WordsStack = 768 := rfl
  have hn : seedStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfnw := frame_noWrap (F := 240) hst (by decide)
  have hBn : (fb m0).toNat = (rspOf m0).toNat - 240 := stackBelow_toNat (by omega)
  have hoff : ∀ j, j < 248 → (off (fb m0) j).toNat = (rspOf m0).toNat - 240 + j := fun j hj ↦ by
    rw [toNat_off (by omega), hBn]
  have hsbn : (stackBelow m0 seedStack).toNat = (rspOf m0).toNat - 1008 :=
    stackBelow_toNat (by omega)
  have hrcN := hrc.2.1
  have hrcA := hrc.2.2
  unfold NativeRustcVm.Apart at hrcA
  unfold NativeRustcVm.NoWrap at hrcN
  rw [hsbn, hss] at hrcA
  -- `b0`: the prologue, `call keccak256_words`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 240) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Seed.b0Offset + b0.length)).toBitVec) ⟨frame_mapped hst (by decide), hfnw⟩
    (by simp) (List.pairwise_singleton _ _)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw1, hrdi, hrsi, hrdx, hrcx, hr8, hrbx, hr14, hr15⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 240 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le slots_cs
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (fb m0) 240) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hw1
  have hsp1 : rspOf st1.data = fb m0 := by rw [hf1.sp, off_zero]
  have eRdi : reg st1.data .rdi = off (fb m0) 16 := (hm1.regs .rdi _ hrdi).trans (eval_ptr0 16)
  have eRcx : reg st1.data .rcx = reg m0 .rsi := hm1.regs .rcx _ hrcx
  have eR8 : reg st1.data .r8 = reg m0 .rdx := hm1.regs .r8 _ hr8
  have eRsi : (reg st1.data .rsi).toNat = (reg m0 .rdx).toNat + 2 := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat]
    have : 9 + 8 * (m0.regs.get64 .rdx).toNat < 2 ^ 32 := hn32
    show _ = (m0.regs.get64 .rdx).toNat + 2
    simp only [Env.ofMachine_regs]
    omega
  have eRdx : (reg st1.data .rdx).toNat = 9 + 8 * (reg m0 .rdx).toNat := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hrdx]
    exact lenSym_eval hn32
  have eRbx : reg st1.data .rbx = reg m0 .rdi := hm1.regs .rbx _ hrbx
  have eR14 : reg st1.data .r14 = off (fb m0) 16 := (hm1.regs .r14 _ hr14).trans (eval_ptr0 16)
  have eR15 : reg st1.data .r15 = reg m0 .rcx := hm1.regs .r15 _ hr15
  have hrc1 : ∀ i < 192, st1.data.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) :=
    rc_keep hs1 fun q hq h ↦ by
      rw [inR (by unfold NativeRustcVm.NoWrap; omega), hBn] at hq
      rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at h
      omega
  have hFm : ∀ d : MachineData, Kept m0.dmem d.dmem →
      NativeRustcVm.Mapped d.dmem (fb m0) (240 + 8) :=
    fun d hk ↦ Mapped.keeps (frame_mapped hst (by decide)) hk
  have hg1 := got_keep hst hgot hs1 (fun q h ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hBn] at h
    rw [hsbn]
    omega)
  have hpre1 : Keccak256WordsIvPre st1.data := by
    unfold Keccak256WordsIvPre
    simp only [eRdi, eRcx, eR8]
    refine ⟨stackOk_callee hst hf1.kept hsp1 (by omega),
      RcAt.callee hrc hrc1 hsp1 hn (by omega),
      by rw [eRsi], eRdx, hn32, Mapped.keeps hbcM hf1.kept, hbcN,
      mapped_off (hFm _ hf1.kept) (by decide), by unfold NativeRustcX64.NoWrap; rw [hoff 16 (by decide)]; omega,
      fun h ↦ apart_callee (hbcA h) hsp1 hn (by omega), ?_, ?_, ?_⟩
    · rw [stackBelow_callee hsp1 (by omega)]
      unfold NativeRustcX64.Apart
      rw [hoff 16 (by decide), stackBelow_toNat (by omega)]
      omega
    · unfold NativeRustcX64.Apart
      rw [hoff 16 (by decide)]
      omega
    · exact got_leaf hst hgot (by simp) hsp1 (by decide) (by decide) hg1
  refine call_then hpc1 hkiv hpre1 fun st2 hpc2 hrsp2 hpost2 ↦ ?_
  obtain ⟨hiv2, hs2, hsv2⟩ := hpost2
  simp only [eRdi, eRcx, eR8] at hiv2 hs2
  have hR2 : ∀ q, (NativeRustcVm.InRange (off (fb m0) 16) 32 q ∨
      NativeRustcVm.InRange (stackBelow st1.data keccak256WordsStack) keccak256WordsStack q) →
      (rspOf m0).toNat - 1008 ≤ q.toNat ∧ q.toNat < (fb m0).toNat + 48 := by
    rintro q (h | h)
    · rw [inR (by unfold NativeRustcVm.NoWrap; rw [hoff 16 (by decide)]; omega),
        hoff 16 (by decide)] at h
      omega
    · have := callee_nat hsp1 (by omega) h
      omega
  have hf2 : Frame m0 240 slots 8 st2.data :=
    Frame.call_low hf1 hsv2 hrsp2 hs2 (fun q h ↦ Or.inl (hR2 q h).2) (by decide) (by decide) hfnw
      slots_le
  -- `b1`: `call memset`.
  have hg2 := got_keep hst hgot hs2 (fun q h ↦ by
    have hh := hR2 q h
    rw [hsbn]
    omega)
  have hwf2 := frame_wf (m0 := m0) (d := st2.data) (F := 240)
    (rest := [(gotAddr "memset", 8)]) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Seed.b1Offset + b1.length)).toBitVec)
    ⟨hFm _ hf2.kept, hfnw⟩
    (by
      intro x hx
      obtain rfl := List.mem_singleton.mp hx
      exact ⟨Mapped.keeps (hgot.mapped (by simp)) hf2.kept, (hgot.1 "memset" (by simp)).2.1⟩)
    (List.pairwise_pair.mpr (got_frame_apart hst hgot (by simp)).symm)
  have hm2 : Match
      (frameEnv m0 st2.data 240 [(gotAddr "memset", 8)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.Seed.b1Offset + b1.length)).toBitVec)
      (gotS "memset") st2.data := by
    apply Match.withKnownBytes
    · exact match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf2.rsp_eval, trivial⟩ trivial trivial
        ⟨(BitVec.add_zero _).symm, trivial⟩
    · intro i hi
      have hb := (hg2 "memset" (by simp) i hi).trans
        ((hg1 "memset" (by simp) i hi).trans (hgot.byte (by simp) hi))
      simpa [frameEnv, Env.base, Sym.eval] using hb
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2 (fun _ _ ↦ rfl)
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Seed.b0_next))
    hm2
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hw3, hrdi3, hrdx3, hrsi3, hrbx3, hr143, hr153⟩ := after_eq run_b1 ▸ ok_b1
  have hf3 : Frame m0 240 slots 0 st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  have hs3 : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem
      (NativeRustcVm.InRange (fb m0) 8) :=
    sameOutside_low hwf2 hm3 (r := 0) rfl (by decide) hw3
  have hsp3 : rspOf st3.data = fb m0 := by rw [hf3.sp, off_zero]
  have eRdi3 : reg st3.data .rdi = off (fb m0) 80 := (hm3.regs .rdi _ hrdi3).trans (eval_ptr0 80)
  have eRdx3 : reg st3.data .rdx = BitVec.ofNat 64 136 := hm3.regs .rdx _ hrdx3
  have eRsi3 : reg st3.data .rsi = BitVec.ofNat 64 0 := hm3.regs .rsi _ hrsi3
  have hpre3 : MemsetPre st3.data := by
    unfold MemsetPre
    simp only [eRdi3, eRdx3, show (BitVec.ofNat 64 136).toNat = 136 from rfl]
    refine ⟨stackOk_callee hst hf3.kept hsp3 (by omega), mapped_off (hFm _ hf3.kept)
      (by decide), by unfold NativeRustcX64.NoWrap; rw [hoff 80 (by decide)]; omega, ?_⟩
    rw [hsp3]
    unfold NativeRustcX64.Apart
    rw [hoff 80 (by decide), hBn]
    omega
  refine call_then hpc3 hmemset hpre3 fun st4 hpc4 hrsp4 hpost4 ↦ ?_
  obtain ⟨-, hz4, hs4, hsv4⟩ := hpost4
  simp only [eRdi3, eRdx3, eRsi3] at hz4 hs4
  have hR4 : ∀ q, NativeRustcVm.InRange (off (fb m0) 80) (BitVec.ofNat 64 136).toNat q →
      (fb m0).toNat + 80 ≤ q.toNat ∧ q.toNat < (fb m0).toNat + 216 := by
    intro q h
    rw [show (BitVec.ofNat 64 136).toNat = 136 from rfl,
      inR (by unfold NativeRustcVm.NoWrap; rw [hoff 80 (by decide)]; omega),
      hoff 80 (by decide)] at h
    omega
  have hf4 : Frame m0 240 slots 8 st4.data :=
    Frame.call_low hf3 hsv4 hrsp4 hs4 (fun q h ↦ Or.inl (hR4 q h).2) (by decide) (by decide) hfnw
      slots_le
  refine .done _ ⟨hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Seed.b1_next), ⟨hf4, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- every change in the stack
    have hst' : ∀ q, (fb m0).toNat ≤ q.toNat → q.toNat < (fb m0).toNat + 240 →
        NativeRustcVm.InRange (stackBelow m0 seedStack) seedStack q := by
      intro q h1 h2
      rw [inR (by unfold NativeRustcVm.NoWrap; omega), hsbn, hss]
      omega
    intro q hq
    have hq' : ¬ ((fb m0).toNat ≤ q.toNat ∧ q.toNat < (fb m0).toNat + 240) ∧
        ¬ ((rspOf m0).toNat - 1008 ≤ q.toNat ∧ q.toNat < (fb m0).toNat + 240) := by
      refine ⟨fun h ↦ hq (hst' q h.1 h.2), fun h ↦ hq ?_⟩
      rw [inR (by unfold NativeRustcVm.NoWrap; omega), hsbn, hss]
      omega
    rw [hs4 q fun h ↦ hq'.1 (by have := hR4 q h; omega),
      hs3 q fun h ↦ hq'.1 (by
        rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at h
        omega),
      hs2 q fun h ↦ hq'.2 (by have := hR2 q h; omega),
      hs1 q fun h ↦ hq'.1 (by
        rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at h
        omega)]
  · intro w hw hbc
    have hbc1 : NativeRustcVm.WordsAt st1.data.dmem (reg m0 .rsi) w := by
      rcases Nat.eq_zero_or_pos (reg m0 .rdx).toNat with h0 | h0
      · rw [List.length_eq_zero_iff.mp (hw.trans h0)]
        exact NativeRustcVm.wordsAt_nil _ _
      · refine hbc.of_sameOutside hs1 fun i hi h ↦ ?_
        have hA := hbcA h0
        unfold NativeRustcVm.Apart at hA
        rw [hsbn, hss] at hA
        rw [NativeRustcVm.length_wordsBytes, hw] at hi
        rw [inR (by unfold NativeRustcVm.NoWrap; omega), hBn,
          NativeRustcVm.toNat_add_ofNat (by omega)] at h
        omega
    have h2 := hiv2 w hw hbc1
    have keep : ∀ j, 16 ≤ j → j < 16 + (List.flatMap NativeRustcVm.wordBytes
        (fiatShamirIv w.toArray).toList).length → (fb m0).toNat + 16 ≤ (off (fb m0) j).toNat ∧
        (off (fb m0) j).toNat < (fb m0).toNat + 48 := by
      intro j h1 h2
      rw [NativeRustcVm.length_wordsBytes] at h2
      simp only [Vector.length_toList] at h2
      rw [hoff j (by omega)]
      omega
    refine keep_off (keep_off h2 hs3 fun j h1 h2 h ↦ ?_) hs4 fun j h1 h2 h ↦ ?_
    · have := keep j h1 h2
      rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at h
      omega
    · have := keep j h1 h2
      have := hR4 _ h
      omega
  · have hz : List.replicate (BitVec.ofNat 64 136).toNat (UInt8.ofNat (BitVec.ofNat 64 0).toNat) =
        List.replicate 136 (0 : UInt8) := rfl
    rw [hz] at hz4
    exact hz4
  · exact (hsv4.1 .rbx rfl).trans ((hm3.regs .rbx _ hrbx3).trans ((hsv2.1 .rbx rfl).trans eRbx))
  · exact (hsv4.1 .r14 rfl).trans ((hm3.regs .r14 _ hr143).trans ((hsv2.1 .r14 rfl).trans eR14))
  · exact (hsv4.1 .r15 rfl).trans ((hm3.regs .r15 _ hr153).trans ((hsv2.1 .r15 rfl).trans eR15))

end

end NativeRustcVmX64.Top.Seed
