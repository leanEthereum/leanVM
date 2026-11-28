module

public import NativeRustcVmX64.KeccakGkr.KeccakPhase.Call
public import NativeRustcVmX64.Code.Vm.KeccakPhase.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.VerifyKeccak.Names

/-!
# `keccak_phase` on x86-64

**`keccakPhase_spec`**: `b0`, `b1` and `memcpy` (`front`: the output lanes in the frame), `b2` and
`verify_keccak` (its precondition from the entry's facts kept, its postcondition the phase's: the
model's `keccakPhase` is `verifyKeccak` of `KECCAK`'s point and the lanes), `b3`, `b4` (the
epilogue, AL `verify_keccak`'s).
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.KeccakPhase NativeRustcVmX64.Transcript
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVmX64.KeccakGkr.Fn
open NativeRustcVm (Region InAny)
open NativeRustcVm.KeccakGkr (scratchBytes outBytes)
open LeanVM.Protocol.Verifier (opKeccak keccakOut)

public section

variable [Host] {k : Nat}

/-- **`keccak_phase`'s contract.** -/
theorem keccakPhase_spec (hp : Placed code k)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hvk : ∀ a s cs inst output, Spec (Labels.label NativeRustcVmX64.Vm.VerifyKeccak.entryLabel)
      (VerifyKeccakPre a s cs inst output) (VerifyKeccakPost a s cs inst output))
    (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (layout : LayoutW)
    (evals : Array (Array EW × Array EW)) :
    Spec (Labels.label NativeRustcVmX64.Vm.KeccakPhase.entryLabel) (KeccakPhasePre a s cs layout evals)
      (KeccakPhasePost a s cs layout evals) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmX64.Vm.KeccakPhase.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakPhase.b0Offset) from hp.label NativeRustcVmX64.Vm.KeccakPhase.entry_at]
  obtain ⟨hS, hrc, hpj, hrh, hts, hcls, hcs, hev, hlog, hpt, h40, hA, hgot⟩ := hpre
  have hn := nums_of hS hA
  have g := geo1 hS
  have g2 := geo2 hS hn
  have hevm : NativeRustcVm.Mapped m0.dmem (reg m0 .rdx) 11808 :=
    Areas.mapped hA (r := ⟨reg m0 .rdx, NativeRustcVm.Tables.tableEvalsBytes⟩) (Or.inr (by simp))
  -- `KECCAK`'s entry.
  have h5 : 5 < evals.size := by rw [hev.1]; decide
  have hgetD : evals.getD opKeccak (#[], #[]) = evals[5] := by
    rw [opKeccak_eq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h5, Option.getD_some]
  rw [hgetD] at hpt h40
  rw [keccakOut_eq] at h40
  have hE := hev.2 5 h5
  have hpt0 : NativeRustcVm.BufEWAt m0.dmem (off (reg m0 .rdx) 9840) 30 evals[5].1.toList := hE.1
  have hv0 : NativeRustcVm.BufEWAt m0.dmem (off (reg m0 .rdx) 10328) 92 evals[5].2.toList := by
    have := hE.2
    rw [NativeRustcVm.addr_add_add] at this
    exact this
  have hv92 : evals[5].2.size ≤ 92 := by simpa using hv0.1
  have hp30 : evals[5].1.size ≤ 30 := by simpa using hpt0.1
  -- The numbers.
  have hB := hn.hB; have hK := hn.hK; have hTop := hn.top; have hKV := kps_eq
  have heW := hn.eW; have heS := hn.eS
  have hoffB : ∀ j, j < 488 → (off (stackBelow m0 480) j).toNat = (stackBelow m0 480).toNat + j :=
    fun j hj ↦ toNat_off (by omega)
  have hoffE : ∀ j, j < 11808 → (off (reg m0 .rdx) j).toNat = (reg m0 .rdx).toNat + j :=
    fun j hj ↦ toNat_off (by omega)
  refine Eventually.bind (front hp hmemcpy hS hn hevm
    (hgot.areas (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      simp [show NativeRustcVm.Tables.tableEvalsBytes = 11808 from rfl]))
    h40 hv92 hv0) fun st hst ↦ ?_
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hat⟩ := hst
  dsimp only at hpc hat
  subst hpc
  -- `b2`.
  have hwf2 : (fenv m0 d 480 488 [(reg m0 .rdx, 11808)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakPhase.b2Offset + b2.length)).toBitVec).WF :=
    fenv_wf1 g hat.body.kept (NativeRustcVm.Transcript.Mapped.keeps hevm hat.body.kept) heW
      (by unfold Sep at heS; omega)
  have hm2 : Match (fenv m0 d 480 488 [(reg m0 .rdx, 11808)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakPhase.b2Offset + b2.length)).toBitVec) retS d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hat.body.sp.trans (eval_ptr0' 24).symm, hat.rbx.trans (eval_ptr (i := 1) (n := 11808) rfl).symm, trivial⟩
      trivial trivial trivial
  refine exec_then (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf2 (fun _ _ ↦ rfl) hm2
    fun e hme hpce ↦ ?_
  obtain ⟨hs2sp, hs2di, hs2si, hs2dx, hs2cx, hs2r8, hs2r9, hs2w8, hs2w16, hs2w⟩ := ok_s2
  have hbe : Body m0 480 488 slots (W1 m0) 0 e.data :=
    Body.block g hat.body hwf2 hme hs2sp (written_low g hwf2 fun w hw ↦ by
      have := hs2w w hw; exact ⟨this.1, by omega⟩)
  have hspe : rspOf e.data = stackBelow m0 480 := by rw [hbe.sp]; exact off_zero _
  -- Memory at `e`: the entry's but the frame.
  have hsame : NativeRustcVm.SameOutside m0.dmem e.data.dmem (W1 m0) := hbe.same
  have hke : Kept m0.dmem e.data.dmem := hbe.kept
  -- `KECCAK`'s point in `d` and the `TState`, the claims.
  have hptd : NativeRustcVm.BufEWAt d.dmem (off (reg m0 .rdx) 9840) 30 evals[5].1.toList :=
    buf_keep hpt0 hat.body.same (by rw [hoffE 9840 (by omega)]; omega) fun q ⟨h1, h2⟩ ↦ by
      rw [hoffE 9840 (by omega)]; unfold Sep at heS; omega
  have hlenp : (ptS.eval (fenv m0 d 480 488 [(reg m0 .rdx, 11808)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakPhase.b2Offset + b2.length)).toBitVec)).toNat = evals[5].1.size := by
    show (Env.load _ 1 9840 8).toNat = _
    rw [load_ofMachine (b := reg m0 .rdx) rfl hptd.2.1]
    simp only [Array.length_toList, Nat.toUInt64_eq]
    show (UInt64.ofNat evals[5].1.size).toNat = _
    rw [UInt64.toNat_ofNat']
    omega
  obtain ⟨hinst, hninst⟩ := inst_eval hlenp hp30
  -- The registers at the call.
  have rdi : reg e.data .rdi = reg m0 .rdi := (hme.regs .rdi _ hs2di).trans hat.r13
  have rsi : reg e.data .rsi = reg m0 .rsi := (hme.regs .rsi _ hs2si).trans hat.rbp
  have rdx : reg e.data .rdx = off (reg m0 .rdx) 9848 := (hme.regs .rdx _ hs2dx).trans hinst
  have rcx : (reg e.data .rcx).toNat = evals[5].1.size := by
    rw [show reg e.data .rcx = _ from hme.regs .rcx _ hs2cx]; exact hninst
  have r8 : reg e.data .r8 = off (stackBelow m0 480) 32 :=
    (hme.regs .r8 _ hs2r8).trans (eval_ptr0' 32)
  have r9 : reg e.data .r9 = reg m0 .rcx := (hme.regs .r9 _ hs2r9).trans hat.r14
  have hcl : keccakClaims e.data = reg m0 .r8 := by
    have h := wordAt_write hme (r := 0) (b := stackBelow m0 480) (sz := 488) (o := 8) rfl
      (by omega) hs2w8
    rw [Sym.eval, Env.ofMachine_regs, show d.regs.get64 .r15 = reg m0 .r8 from hat.r15] at h
    unfold keccakClaims stackArg
    rw [hspe, show stackBelow m0 480 + BitVec.ofNat 64 (8 + 8 * 0) = off (stackBelow m0 480) 8
      from rfl, NativeRustcVm.wordOf_of_wordAt h]
  have hout : keccakOutArg e.data = reg m0 .r9 := by
    have h := wordAt_write hme (r := 0) (b := stackBelow m0 480) (sz := 488) (o := 16) rfl
      (by omega) hs2w16
    rw [Sym.eval, Env.ofMachine_regs, show d.regs.get64 .r12 = reg m0 .r9 from hat.r12] at h
    unfold keccakOutArg stackArg
    rw [hspe, show stackBelow m0 480 + BitVec.ofNat 64 (8 + 8 * 1) = off (stackBelow m0 480) 16
      from rfl, NativeRustcVm.wordOf_of_wordAt h]
  -- `verify_keccak`'s precondition.
  have hlanes : NativeRustcVm.EWsAt e.data.dmem (off (stackBelow m0 480) 32)
      (lanes evals[5].2).toList :=
    ews_keep hat.lanes (hme.sameOutside hwf2)
      (by rw [hoffB 32 (by omega), Array.length_toList, lanes_size]; omega) fun q hq ↦ by
        have := written_lt (n := 24) (fun w hw ↦ by have := hs2w w hw; exact ⟨this.1, this.2⟩) hq
        rw [hoffB 32 (by omega)]; omega
  have hinstE : NativeRustcVm.EWsAt e.data.dmem (off (reg m0 .rdx) 9848) evals[5].1.toList := by
    have h := (buf_keep hpt0 hsame (by rw [hoffE 9840 (by omega)]; omega) fun q ⟨h1, h2⟩ ↦ by
      rw [hoffE 9840 (by omega)]; unfold Sep at heS; omega).2.2
    rwa [show off (reg m0 .rdx) 9840 + 8#64 = off (reg m0 .rdx) 9848 from off_add _ _ _] at h
  have hvkS : verifyKeccakStack ≤ keccakPhaseStack := by omega
  have hsbe : (stackBelow e.data verifyKeccakStack).toNat =
      (stackBelow m0 keccakPhaseStack).toNat := by
    rw [stackBelow_callee hspe (by omega), show 480 + verifyKeccakStack = keccakPhaseStack from
      kps_eq.symm]
  have hpre : VerifyKeccakPre a s cs evals[5].1 (lanes evals[5].2) e.data := by
    unfold VerifyKeccakPre
    dsimp only
    rw [rdi, rsi, rdx, r8, r9, hcl, hout]
    refine ⟨stackOk_callee hS hke hspe (by omega), ⟨?_, ?_⟩,
      RcAt.callee hrc (fun i hi ↦ same_m0 hn hsame (A := rcAddr) (n := 192) hn.rcW hn.rcS i hi)
        hspe hS.1 (by omega),
      bytes_m0 hn hsame hpj (by rw [pj_len]; exact hn.pjW) (by rw [pj_len]; exact hn.pjS),
      bytes_m0 hn hsame hrh (by rw [rh_len]; exact hn.rhW) (by rw [rh_len]; exact hn.rhS),
      ts_keep hts hke hsame hn.tW hn.wW fun q ⟨h1, h2⟩ ↦ by
        have := hn.tS; have := hn.wS; unfold Sep at *; constructor <;> omega,
      cls_keep hcls hsame hn.cW fun q ⟨h1, h2⟩ ↦ by have := hn.cS; unfold Sep at *; omega,
      hcs, rcx.symm, hpt, hp30, hinstE, lanes_size _, hlanes, ?_, ?_⟩
    · rw [hspe]
      exact mapped_off (b := stackBelow m0 480) (o := 8) (Mapped.keeps g.map hke) (by omega)
    · rw [hspe]; omega
    · unfold argsRegion
      rw [hspe]
      exact areas_vk (N := verifyKeccakStack) hn hA hke hsbe ((Nat.add_comm _ _).trans kps_eq.symm)
        (hoffE 9848 (by omega)) hp30
        (mapped_off (Mapped.keeps hevm hke) (by omega)) (hoffB 32 (by omega))
        (mapped_off (Mapped.keeps g.map hke) (by omega)) (hoffB 8 (by omega))
        (mapped_off (b := stackBelow m0 480) (o := 8) (Mapped.keeps g.map hke) (by omega))
    · have hbytes : ∀ l ∈ ["memcpy"], ∀ i < 8,
          e.data.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
            m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
        intro l hl i hi
        have hg := hgot.1 l hl
        apply hsame
        have ha : Apart (gotAddr l) 8 (stackBelow m0 keccakPhaseStack)
            (keccakPhaseStack + 8) := hg.2.2.1
        have hp := NativeRustcX64.Sym.toNat_add_ofNat (gotAddr l) i
          (by have := hg.2.1; unfold NoWrap at this; omega)
        unfold W1
        rw [hp]
        unfold Apart at ha
        omega
      apply NativeRustcVmX64.GotAt.callee hgot hbytes
      · rw [hsbe]
      · rw [hsbe]
        have : verifyKeccakStack ≤ keccakPhaseStack := by omega
        omega
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨_, by simp, le_rfl, le_rfl⟩
        · exact ⟨_, by simp, le_rfl, le_rfl⟩
        · exact ⟨_, by simp, le_rfl, le_rfl⟩
        · exact ⟨_, by simp, le_rfl, le_rfl⟩
        · exact ⟨_, by simp, le_rfl, le_rfl⟩
        · refine ⟨(reg m0 .rdx, NativeRustcVm.Tables.tableEvalsBytes), by simp, ?_, ?_⟩
          all_goals
            dsimp only [Prod.fst, Prod.snd]
            rw [hoffE 9848 (by omega)]
            have : NativeRustcVm.Tables.tableEvalsBytes = 11808 := rfl
            omega
        · refine ⟨(stackBelow m0 keccakPhaseStack, keccakPhaseStack + 8), by simp, ?_, ?_⟩
          all_goals
            dsimp only [Prod.fst, Prod.snd]
            rw [hoffB 32 (by omega)]
            omega
        · exact ⟨_, by simp, le_rfl, le_rfl⟩
        · exact ⟨_, by simp, le_rfl, le_rfl⟩
        · exact ⟨_, by simp, le_rfl, le_rfl⟩
        · refine ⟨(stackBelow m0 keccakPhaseStack, keccakPhaseStack + 8), by simp, ?_, ?_⟩
          all_goals
            dsimp only [Prod.fst, Prod.snd]
            rw [hspe, show stackBelow m0 480 + 8#64 = off (stackBelow m0 480) 8 from rfl,
              hoffB 8 (by omega)]
            omega
  -- The call.
  refine call_then hpce (hvk a s cs evals[5].1 (lanes evals[5].2)) hpre fun e' hpc' hrsp' hpost ↦ ?_
  obtain ⟨hok, hres, hwr, hsv⟩ := hpost
  rw [rsi] at hok hres
  rw [rdi, hcl, hout] at hres
  rw [rdi, r9, hcl, hout] at hwr
  have hb' : Body m0 480 488 slots (W2 m0) (0 + 8) e'.data := by
    refine Body.call g2 (hbe.weaken (w12 hn)) hsv hrsp' hwr fun q ⟨r, hr, hq⟩ ↦ ?_
    have hn' := hn
    obtain ⟨-, -, -, tW, sW, cW, oW, -, -, -, -, -, tS, sS, cS, oS, -⟩ := hn'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · have h1 := inR_nat (by simp only; omega) hq
      simp only [hsbe] at h1
      refine ⟨⟨_, List.mem_cons_self, ?_⟩, by unfold Fn.Top; omega⟩
      show NativeRustcVm.InRange (stackBelow m0 keccakPhaseStack) keccakPhaseStack q
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; omega)]
      omega
    · refine ⟨⟨_, by simp [wsOf], hq⟩, ?_⟩
      have h1 := inR_nat (by simp only [tsz]; omega) hq
      simp only [tsz] at h1
      unfold Fn.Top; unfold Sep at tS; omega
    · refine ⟨⟨_, by simp [wsOf], hq⟩, ?_⟩
      have h1 := inR_nat (by simp only [ssz]; omega) hq
      simp only [ssz] at h1
      unfold Fn.Top; unfold Sep at sS; omega
    · refine ⟨⟨_, by simp [wsOf], hq⟩, ?_⟩
      have h1 := inR_nat (by simp only [csz]; omega) hq
      simp only [csz] at h1
      unfold Fn.Top; unfold Sep at cS; omega
    · refine ⟨⟨_, by simp [wsOf], hq⟩, ?_⟩
      have h1 := inR_nat (by simp only [osz]; omega) hq
      simp only [osz] at h1
      unfold Fn.Top; unfold Sep at oS; omega
  -- The epilogue.
  have hwf3 : (fenv m0 e'.data 480 488 [] (fun _ ↦ 0) 0).WF := fenv_wf0 g2 hb'.kept
  have hm3 : Match (fenv m0 e'.data 480 488 [] (fun _ ↦ 0) 0) vkS e'.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb'.sp.trans (eval_ptr0' 8).symm, trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf3 nofun
    (hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakPhase.b2_next)) hm3 fun st3 hm3' hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf3 nofun
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakPhase.b3_next)) hm3' fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hld, hsp4, hrax, hmem4⟩ := ok_s4
  obtain ⟨hsv4, hrsp4⟩ := Body.epilogue g2 hb' hwf3 hm4 hld hsp4
  have hd4 : st4.data.dmem = e'.data.dmem := hm4.dmem_eq hwf3 hmem4
  have hax : reg st4.data .rax = reg e'.data .rax := hm4.regs .rax _ hrax
  simp only [PcOk, Sym.eval] at hpc4
  have hrun : (NativeVm.Model.keccakPhase layout evals).run s =
      (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat evals[5].1 (lanes evals[5].2)).run s := by
    rw [keccakPhase_eq, hgetD, ← hlog]
  refine .done _ ⟨hpc4.trans (Body.load_ret g2 hb'), hrsp4, ?_⟩
  unfold KeccakPhasePost
  dsimp only
  rw [hrun]
  refine ⟨?_, by rw [hd4]; exact hres, by unfold Writes; rw [hd4]; exact hb'.same, hsv4⟩
  have e1 : boolRet st4.data = boolRet e'.data := by unfold boolRet; rw [hax]
  unfold OkAl at hok ⊢
  rw [e1]
  exact hok

end

end NativeRustcVmX64.KeccakGkr.KeccakPhase
