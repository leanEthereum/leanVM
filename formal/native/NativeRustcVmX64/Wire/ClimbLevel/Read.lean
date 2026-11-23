module

public import NativeRustcVmX64.Wire.ClimbLevel.Found
public import NativeRustcVmX64.Code.Vm.HashPair.Names
public import NativeRustcVmX64.Code.Vm.ReaderDigest.Names

/-!
# `climb_level`'s sibling read (x86-64)

No node is node `i`'s sibling: `Reader::digest` into the frame's `120` (`b10`, `digest_call`); its
tag tested (`b11`): none, the return of `0` (`b23`, `b24`); else the sibling written (`b12`) and
the parent, in order for an even key (`b13`), the sibling's first for an odd (`b17`)
(`read_spec`).
-/

namespace NativeRustcVmX64.Wire.ClimbLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ClimbLevel
open NativeRustcVmX64.Transcript (Frame frameEnv Frame.of_block Frame.call_slots stackOk_callee
  stackBelow_callee after after_eq MidOk sameOutside_low)
open NativeRustcVm.Transcript (Mapped.keeps off off_zero off_add off_off toNat_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open NativeRustcVmX64.Wire (pc_cond ite_t ite_f eq64)
open NativeRustcVmX64.Sumcheck (WordW WordsW wordAt_written wordsAt_written writesIn_of_mid)

public section

/-- `cmpb $0, m; je`. -/
theorem eq8_zero (x : BitVec 64) :
    CmpOp.apply .eq .W8 x (BitVec.ofNat 64 0) = decide (x.toNat % 256 = 0) := by
  simp only [CmpOp.apply]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp [low, BitVec.toNat_setWidth]

/-- The tag of an `Option<Digest>`, its low byte. -/
theorem tag_load {env : Env} {o : Nat} {w : UInt64} (hw : w = 0 ∨ w = 1)
    (h : WordAt env.mem0 (env.base 0 + BitVec.ofNat 64 o) w) :
    (env.load 0 o 1).toNat % 256 = w.toNat := by
  have h0 := h 0 (by rw [NativeRustcVm.length_wordBytes]; decide)
  rw [NativeRustcVm.addr_add_zero] at h0
  rw [Wire.load_byte h0]
  rcases hw with rfl | rfl <;> rfl

/-- What `Reader::digest`'s call changes, within what a run may. -/
theorem rd_R {s r q : Nat} {X Y : Prop}
    (hq : (s - 256 ≤ q ∧ q < s - 200) ∨ (s - 88 ≤ q ∧ q < s - 48) ∨ (r + 16 ≤ q ∧ q < r + 24)) :
    (s - 1056 ≤ q ∧ q < s) ∨ (r + 16 ≤ q ∧ q < r + 24) ∨ X ∨ Y := by
  rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
  · exact Or.inl ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide) s) h1,
      Nat.lt_of_lt_of_le h2 (Nat.sub_le s 200)⟩
  · exact Or.inl ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide) s) h1,
      Nat.lt_of_lt_of_le h2 (Nat.sub_le s 48)⟩
  · exact Or.inr (Or.inl h)

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} {ns : List (Nat × Digest)}

variable [Host] {k : Nat}

section
variable (hp : Placed code k) (g : Geo m0 bp B.length) (hl : ns.length = cnt m0)
include hp g hl

omit hl in
/-- **The call of `Reader::digest`** (`b10`) into the frame's `120`, the reader at `ci`: back in
the frame after it, the callee-saved registers kept, memory changed at most in the callee's
stack, the return address's slot, the output and the cursor; the read's outcome. -/
theorem digest_call (hd : Spec (Labels.label NativeRustcVmX64.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost)
    {ci : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b10Offset))
    (hf : Frame m0 208 slots 8 st.data) (hloc : Loc m0 st.data.dmem)
    (hR : ReaderAt st.data.dmem (rdr m0) bp B ci) {Q : MachineState → Prop}
    (cont : ∀ m2, Frame m0 208 slots 8 m2 →
      (∀ r ∈ loopRegs, reg m2 r = reg st.data r) →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem (fun q ↦
        (sp m0 - 256 ≤ q.toNat ∧ q.toNat < sp m0 - 200) ∨
        (sp m0 - 88 ≤ q.toNat ∧ q.toNat < sp m0 - 48) ∨
        ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24)) →
      (match rdDigest B ci with
        | some (dg, c') => WordAt m2.dmem (off (fb m0) 120) 1 ∧
            WordsAt m2.dmem (off (fb m0) 128) dg.toList ∧ ReaderAt m2.dmem (rdr m0) bp B c'
        | none => WordAt m2.dmem (off (fb m0) 120) 0) →
      Eventually (step1 Host.exe) Q ⟨m2, Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b11Offset)⟩) :
    Eventually (step1 Host.exe) Q st := by
  have h0 := g.s0
  have hspe := sp_eq m0
  have hfb := g.fb_toNat
  obtain ⟨hok, hlow, hdi, hsi, hK⟩ := ok_b10
  let ret := (Host.addrOf (k + NativeRustcVmX64.Vm.ClimbLevel.b10Offset + b10.length)).toBitVec
  have hwf := fr_wf g hf (vars := fun _ ↦ 0) (ret := ret)
  have hm := fr_match hf (vars := fun _ ↦ 0) (ret := ret)
  refine exec_at (Wire.infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf (fun _ _ ↦ rfl) hpc
    hm fun st1 hm1 hpc1 ↦ ?_
  have hf1 : Frame m0 208 slots 0 st1.data := Frame.of_block hf hwf hm1 hok slots_le
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 208) 8) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hlow
  have hs1n : ∀ q, NativeRustcVm.InRange (stackBelow m0 208) 8 q →
      sp m0 - 208 ≤ q.toNat ∧ q.toNat < sp m0 - 200 := fun q hq ↦ by
    rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [hfb]; omega), hfb] at hq
    omega
  have hsp : rspOf st1.data = stackBelow m0 208 := by rw [hf1.sp, off_zero]
  have hcb : stackBelow st1.data readerDigestStack = stackBelow m0 256 := by
    rw [stackBelow_callee hsp (by rw [rds_eq]; omega), rds_eq]
  have hcb48 : stackBelow st1.data 48 = stackBelow m0 256 := by rw [← rds_eq]; exact hcb
  have hcbn : (stackBelow m0 256).toNat = sp m0 - 256 := NativeRustcVmX64.stackBelow_toNat (by omega)
  have hdi1 : reg st1.data .rdi = off (fb m0) 120 := (hm1.regs .rdi _ hdi).trans rfl
  have hsi1 : reg st1.data .rsi = rdr m0 :=
    (hm1.regs .rsi _ hsi).trans (Wire.load_word hloc.rd)
  have ho120 := g.fo (o := 120) (by omega)
  have hR1 : ReaderAt st1.data.dmem (rdr m0) bp B ci :=
    g.reader hR hs1 fun q hq ↦ .inl (by have := hs1n q hq; omega)
  have hrS := g.rS
  have hgS := g.g.sb
  have hrb := g.g.rb
  have hbN := g.g.bpNw
  unfold NativeRustcVm.Apart at hgS hrb
  unfold NativeRustcVm.NoWrap at hbN
  have hsb := NativeRustcVmX64.stackBelow_toNat (m := m0) (n := climbLevelStack)
    (by rw [stack_eq]; omega)
  rw [hsb, stack_eq] at hgS
  have hP : ReaderDigestPre st1.data := by
    refine ⟨stackOk_callee g.g.st hf1.kept hsp (by rw [stack_eq, rds_eq]; omega),
      ⟨fun t ht ↦ ?_, ?_⟩, bp, B, ci, by rw [hsi1]; exact hR1, ?_⟩
    · have ht' : t < 40 := ht
      show (st1.data.dmem.get? (reg st1.data .rdi + BitVec.ofNat 64 t)).isSome
      rw [hdi1, off_add]
      exact hf1.kept _ (NativeRustcVmX64.Transcript.frame_mapped g.g.st (by decide) _ (by omega))
    · show (reg st1.data .rdi).toNat + 40 ≤ 2 ^ 64
      rw [hdi1, ho120]; omega
    · simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, stackR, rds_eq, hcb48, List.Pairwise.nil, and_true,
        hdi1, hsi1]
      unfold NativeRustcVm.Apart
      rw [ho120, hcbn]
      refine ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, fun _ h ↦ h.elim⟩
  refine NativeRustcX64.Sym.call_then hpc1 hd hP fun st' hpc' hrsp' ⟨hres, hso, hsv⟩ ↦ ?_
  rw [hdi1, hsi1] at hres hso
  have hRn : ∀ q, NativeRustcVm.InAny [⟨off (fb m0) 120, 40⟩, curRegion (rdr m0),
      frameR st1.data readerDigestStack] q →
      (sp m0 - 256 ≤ q.toNat ∧ q.toNat < sp m0 - 208) ∨
      (sp m0 - 88 ≤ q.toNat ∧ q.toNat < sp m0 - 48) ∨
      ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) := by
    intro q ⟨r, hr, hq⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine .inr (.inl ?_)
      have hq' : NativeRustcVm.InRange (off (fb m0) 120) 40 q := hq
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [ho120]; omega),
        ho120] at hq'
      omega
    · refine .inr (.inr ?_)
      have hrN := g.rNw
      have ht : (rdr m0 + BitVec.ofNat 64 16).toNat = (rdr m0).toNat + 16 :=
        NativeRustcVm.toNat_add_ofNat (by omega)
      have hq' : NativeRustcVm.InRange (rdr m0 + BitVec.ofNat 64 16) 8 q := hq
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [ht]; omega), ht] at hq'
      exact hq'
    · refine .inl ?_
      have hq' : NativeRustcVm.InRange (stackBelow m0 256) 48 q := by
        have : frameR st1.data readerDigestStack = ⟨stackBelow m0 256, 48⟩ := by
          rw [frameR, rds_eq, ← rds_eq, hcb, rds_eq]
        rw [this] at hq
        exact hq
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [hcbn]; omega),
        hcbn] at hq'
      omega
  have hf' : Frame m0 208 slots 8 st'.data := by
    refine Frame.call_slots hf1 hsv hrsp' hso (fun p hp i hi hq ↦ ?_) (fun i hi hq ↦ ?_)
    · have := hRn _ hq
      have hp' := slots_le p hp
      have hp'' : 160 ≤ p.1 := by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hrS' := g.rS
      rw [g.fo (by omega)] at this
      omega
    · have := hRn _ hq
      rw [g.fo (by omega)] at this
      omega
  obtain ⟨m2, pc2⟩ := st'
  simp only at hpc'
  subst hpc'
  have hk1 := regs_kept hK fun r v h ↦ hm1.regs r v h
  have hres' := hres bp B ci hR1
  refine cont m2 hf' (fun r hr ↦ (hsv.1 r (by
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (hk1 r hr)) ?_ ?_
  · intro q hq
    rw [← hs1 q fun h ↦ hq (.inl (by have := hs1n q h; omega))]
    exact hso q fun h ↦ hq (by
      rcases hRn q h with h' | h' | h'
      · exact .inl (by omega)
      · exact .inr (.inl h')
      · exact .inr (.inr h'))
  · revert hres'
    cases rdDigest B ci with
    | none => exact id
    | some p =>
      intro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, h3⟩
      rw [off_off] at h2
      exact h2


/-- **The sibling read** (`Rd`): the read's tag none, the return of `0`; else the sibling written
and the parent; the next node's check. -/
theorem read_spec (hh : Spec (Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
    (hd : Spec (Labels.label NativeRustcVmX64.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost)
    (hR0 : ReaderAt m0.dmem (rdr m0) bp B c) (hns : NodesAt m0.dmem (nodes m0) ns)
    {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat} {st : MachineState}
    (hI : Rd k m0 bp B c ns i sl ci st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ Post m0 st' ∨ ∃ sl' ci', Nxt k m0 bp B c ns (i + 1) sl' ci' st') st := by
  have hcur := hI.cur
  have h0 := g.s0
  have hspe := sp_eq m0
  have hn := g.n256
  have hlt := hcur.lt
  have hi : i < ns.length := by omega
  have hsl : sl.length = i := by
    rw [sibsM_length B ns _ c hcur.hs, List.length_take]; omega
  have hkey := (hcur.mm.nd i hi).1
  have hrS := g.rS
  have hsR := g.sR
  have hxR := g.xR
  have hnR := g.nR
  have hsS := g.sS
  have hxS := g.xS
  have hnS := g.nS
  have hsN := g.sN
  have hxN := g.xN
  have hnN := g.nN
  have hls := hcur.mm.ls
  have hlp := hcur.mm.lp
  refine digest_call hp g hd hI.pc hcur.fr hcur.mm.loc hcur.mm.rd fun m2 hf2 hk2 hs2 hres ↦ ?_
  have hR2 : ∀ q : BitVec 64, (sp m0 - 256 ≤ q.toNat ∧ q.toNat < sp m0 - 200) ∨
      (sp m0 - 88 ≤ q.toNat ∧ q.toNat < sp m0 - 48) ∨
      ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) →
      (sp m0 - 1056 ≤ q.toNat ∧ q.toNat < sp m0) ∨
      ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) ∨
      ((sibs m0).toNat ≤ q.toNat ∧ q.toNat < (sibs m0).toNat + 10240) ∨
      ((nxt m0).toNat ≤ q.toNat ∧ q.toNat < (nxt m0).toNat + 10240) := fun q hq ↦
    rd_R hq
  have hchg2 : Chg m0 m2.dmem := chg_trans hcur.mm.chg hs2 hR2
  have hloc2 : Loc m0 m2.dmem := hcur.mm.loc.keep g hs2 fun q hq ↦ by omega
  have hnx2 : Nx m0 (i + 1) m2.dmem := hcur.nx.keep g hs2 fun q hq ↦ by omega
  have hsb2 := nodesAt_keep hcur.mm.sb (by omega) hs2 fun q hq ↦ by omega
  have hpa2 := nodesAt_keep hcur.mm.nx (by omega) hs2 fun q hq ↦ by omega
  have hnd2 := nodesAt_keep hcur.mm.nd (by rw [hl]; exact hnN) hs2 fun q hq ↦ by omega
  have hrbp := (hk2 .rbp (by simp [loopRegs])).trans hcur.rbp
  have hr12 := (hk2 .r12 (by simp [loopRegs])).trans hcur.r12
  have hrbx := (hk2 .rbx (by simp [loopRegs])).trans hcur.rbx
  have hr14 := (hk2 .r14 (by simp [loopRegs])).trans hcur.r14
  have hr15 := (hk2 .r15 (by simp [loopRegs])).trans hcur.r15
  -- `b11`: the tag.
  refine fr_step hp g (j := NativeRustcVmX64.Vm.ClimbLevel.b11Offset) b11_in_code (by simp [b11]) exit_b11 nofun ok_b11.1 rfl hf2
    fun s3 hf3 hd3 hr3 hpc3 ↦ ?_
  have hk3 := regs_kept ok_b11.2 hr3
  cases hrd : rdDigest B ci with
  | none =>
    rw [hrd] at hres
    have hnone := sibsM_none hcur.hs hi (by rw [sibStep_read hi hI.miss, hrd]; rfl)
    have hpc4 := pc_cond hpc3 (P := True) (by
      show CmpOp.apply .eq .W8 ((frameEnv m0 m2 208 []).load 0 120 1) (BitVec.ofNat 64 0) = _
      rw [eq8_zero, tag_load (.inl rfl) hres]; rfl)
    rw [ite_t trivial, hp.label NativeRustcVmX64.Vm.ClimbLevel.label_10_at] at hpc4
    refine fr_step hp g (j := NativeRustcVmX64.Vm.ClimbLevel.b23Offset) b23_in_code (by simp [b23]) exit_b23 nofun ok_b23.1 hpc4 hf3
      fun s4 hf4 hd4 hr4 hpc5 ↦ ?_
    simp only [PcOk] at hpc5
    refine Eventually.mono (fin hp g hR0 hns hl (hpc5.trans (congrArg Host.addrOf rfl)) hf4 ?_
      (by rw [hd4, hd3]; exact hchg2)) fun _ h ↦ .inl h
    unfold Res
    rw [hnone]
    exact hr4 .rax _ ok_b23.2
  | some p =>
    obtain ⟨dg, c'⟩ := p
    rw [hrd] at hres
    obtain ⟨htag, hdg, hrd2⟩ := hres
    have hs' := sibsM_step hcur.hs hi (q := ((ns[i]).1, dg, false)) (ci' := c')
      (by rw [sibStep_read hi hI.miss, hrd]; rfl)
    have hpc4 := pc_cond hpc3 (P := False) (by
      show CmpOp.apply .eq .W8 ((frameEnv m0 m2 208 []).load 0 120 1) (BitVec.ofNat 64 0) = _
      rw [eq8_zero, tag_load (.inr rfl) htag]; rfl)
    rw [ite_f not_false] at hpc4
    have hmm3 : MemS m0 bp B ns (sn sl) (parentsOf (ns.take i) sl) c' s3.data.dmem := by
      rw [hd3]; exact ⟨hrd2, hsb2, hpa2, hnd2, hloc2, hchg2, hls, hlp⟩
    have hnx3 : Nx m0 (i + 1) s3.data.dmem := by rw [hd3]; exact hnx2
    have hdg3 : WordsAt s3.data.dmem (off (fb m0) 128) dg.toList := by rw [hd3]; exact hdg
    -- `b12`: the sibling written.
    obtain ⟨hmid, hfr, hin, hdw, hkw, hww, h13, hK⟩ := ok_b12
    have hiA := g.nd_area hf3 (o := 40 * i) (n := 8) (by omega) (by omega)
    have hsA := g.sb_area hf3 (o := 40 * i) (n := 40) (by omega) (by omega)
    have hti := g.nd_toNat (o := 40 * i) (by omega)
    have hts := g.sb_toNat (o := 40 * i) (by omega)
    have hnX := g.nX
    have hwf : (frameEnv m0 s3.data 208 [(nd m0 i, 8), (off (sibs m0) (40 * i), 40)]).WF :=
      g.wf_rest hf3 (fun x hx ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hiA
          · exact hsA)
        (List.pairwise_pair.mpr (by dsimp only; rw [hti, hts]; omega))
    have hk3' : ∀ x ∈ loopRegs, reg s3.data x = reg m2 x := fun x hx ↦ hk3 x hx
    have hm : Match (frameEnv m0 s3.data 208 [(nd m0 i, 8), (off (sibs m0) (40 * i), 40)]) rdS
        s3.data :=
      match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf3.rsp_eval, trivial⟩ trivial trivial
        ⟨by
          show reg s3.data .rbp = nd m0 i + BitVec.ofInt 64 0
          rw [NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero,
            hk3' .rbp (by simp [loopRegs])]
          exact hrbp,
         sib_alias ((hk3' .r15 (by simp [loopRegs])).trans hr15)
          ((hk3' .r12 (by simp [loopRegs])).trans hr12), trivial⟩
    have hkl : (frameEnv m0 s3.data 208 [(nd m0 i, 8), (off (sibs m0) (40 * i), 40)]).load 1 0 8 =
        BitVec.ofNat 64 (ns[i]).1 := by
      have hw := (hmm3.nd i hi).2.1
      rw [← NativeRustcVm.addr_add_zero (off (nodes m0) (40 * i))] at hw
      rw [Wire.load_word hw]
      exact toBitVec_toUInt64 hkey
    refine exec_at (Wire.infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf nofun
      (hpc4.trans (congrArg Host.addrOf rfl)) hm fun s5 hm5 hpc5 ↦ ?_
    obtain ⟨hf5, hmm5, hnx5, hdg5⟩ := sib_mem g hl hf3 hmm3 hnx3 hlt hsl hi hwf hm5 hmid hfr hin
      hdw hkw hww (D := dg) (fun t ht ↦ by
        have hw' := (NativeRustcVm.wordsAt_iff.mp hdg3) t (by simpa using ht)
        rw [off_add] at hw'
        exact Wire.load_word hw') hkl false
    have hk5 := regs_kept hK fun r v h ↦ hm5.regs r v h
    have hr13 : reg s5.data .r13 = BitVec.ofNat 64 (ns[i]).1 := (hm5.regs .r13 _ h13).trans hkl
    have hM : Mid m0 bp B c ns i sl c' ((ns[i]).1, dg, false) s5.data :=
      ⟨hf5, hs', hmm5, hnx5, hdg5, hlt, hsl, fun _ ↦ rfl,
        (hk5 .rbp (by simp [loopRegs])).trans ((hk3' .rbp (by simp [loopRegs])).trans hrbp), hr13,
        (hk5 .r12 (by simp [loopRegs])).trans ((hk3' .r12 (by simp [loopRegs])).trans hr12),
        (hk5 .rbx (by simp [loopRegs])).trans ((hk3' .rbx (by simp [loopRegs])).trans hrbx),
        (hk5 .r14 (by simp [loopRegs])).trans ((hk3' .r14 (by simp [loopRegs])).trans hr14),
        (hk5 .r15 (by simp [loopRegs])).trans ((hk3' .r15 (by simp [loopRegs])).trans hr15)⟩
    have hpc6 := pc_cond hpc5 (P := (ns[i]).1 % 2 = 1) (by
      show (!CmpOp.apply .eq .W8 (BinOp.apply .and .W8
        ((frameEnv m0 s3.data 208 [(nd m0 i, 8), (off (sibs m0) (40 * i), 40)]).load 1 0 8)
        (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0)) = _
      exact odd_cond hkey hkl)
    by_cases hod : (ns[i]).1 % 2 = 1
    · rw [ite_t hod, hp.label NativeRustcVmX64.Vm.ClimbLevel.label_16_at] at hpc6
      exact Eventually.mono (pair_spec hp g hl hh hM hi (.inr ⟨hpc6, hod, rfl⟩))
        fun _ h ↦ .inr ⟨_, _, h⟩
    · rw [ite_f hod] at hpc6
      exact Eventually.mono (pair_spec hp g hl hh hM hi
        (.inl ⟨hpc6.trans (congrArg Host.addrOf rfl), by omega⟩)) fun _ h ↦ .inr ⟨_, _, h⟩

end

end

end NativeRustcVmX64.Wire.ClimbLevel
