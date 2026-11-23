module

public import NativeRustcVmArm.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmArm.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Out1

/-!
# `verify_keccak`: the output point, the pack's coordinates and the slot; the return

`b68`: `out.point` extended by the claim's first `logSteps - 4` coordinates; `b69`: its verdict;
`b70`: extended by the slot point; `b71`: to the epilogue (`b73`) with X0 `1`. `extO`: a block
without writes, then `extend` of `out.point`.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt KeccakOutAt)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **A block without writes, then `extend` of `out.point`.** -/
theorem extO (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {ds : List Directive} {i : Nat} {S' : SState} {m : MachineData}
    {R : MachineState → Prop} {A : BitVec 64} {L xs : List EW}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.BufEW36Extend.entryLabel))
    (hfr : VFr m0 m) (hsp : S'.sp = .ptr 0 0) (hmem : S'.mem = [])
    (h72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7)
    (hx0 : S'.reg .X0 = some (.load 0 72 8))
    (hst : ∀ st, Match (envM m0 m) S' st → VFr m0 st →
      st.regs.X1.toBitVec = A ∧ st.regs.X2.toNat = xs.length ∧ NativeRustcVm.EWsAt st.dmem A xs ∧
      Readable st A (16 * xs.length) ∧ Apart (oA m0) 584 A (16 * xs.length))
    (hbuf : NativeRustcVm.BufEWAt m.dmem (oA m0) 36 L) (hfit : L.length + xs.length ≤ 36)
    (cont : ∀ st m2 : MachineData, Match (envM m0 m) S' st → VFr m0 m2 →
      NativeRustcVm.BufEWAt m2.dmem (oA m0) 36 (L ++ xs) → m2.regs.X0 = 1 →
      Chg m0 [] [(3, 0, 584)] m.dmem m2.dmem → Kept m.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := envM_wf hn hfr
  refine callC hn hk hrun hfr (matchM hn hfr) hwf hsp (by rw [hmem]; rfl) (Lb := []) (L := [])
    (O := [(3, 0, 584)]) (lo := 0) (n := 0) (by decide) (by decide) (by decide) (by decide) hext
    (fun st hm1 hfr1 ↦ ?_) (fun st m' hm1 hfr1 hq ↦ ?_)
    fun st m2 hm1 hfr1 hq hfr2 hcs hb hc hkt ↦ ?_
  all_goals
    have hd : st.dmem = m.dmem := hm1.dmem_eq hwf hmem
    have e0 : st.regs.X0.toBitVec = oA m0 := by
      rw [show st.regs.X0 = st.regs.getXReg .X0 from rfl, hm1.regs .X0 _ hx0]
      exact Sumcheck.load_word h72
  · obtain ⟨e1, e2, -, hrd, hap⟩ := hst st hm1 hfr1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e0, hd, NativeRustcVm.wordOf_of_wordAt hbuf.2.1, u64_toNat' (by have := hbuf.1; omega)]
      exact hbuf.1
    · rw [e0]
      have := readable_of (ok_out h) hn.oW hfr1.kept (o := 0) (n := 584) (by decide)
      rwa [NativeRustcVm.addr_add_zero] at this
    · rw [e1, e2]; exact hrd
    · rw [e0, e1, e2]; exact hap
  · obtain ⟨-, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rw [e0] at hq
    rcases hq with hq | hq
    · exact ws_ob0 hn (i := 3) (n := 584) (by decide) (by decide) (by decide) (by decide) hq
    · exact (inRange_zero hq).elim
  · obtain ⟨e1, e2, hxs, -, -⟩ := hst st hm1 hfr1
    obtain ⟨hpost, -, -⟩ := hq
    have hb' : NativeRustcVm.BufEWAt st.dmem (oA m0) 36 L := by rw [hd]; exact hbuf
    rw [e0, NativeRustcVm.wordOf_of_wordAt hb'.2.1, u64_toNat' (by have := hb'.1; omega), e2,
      KeccakGkr.bufEWOf_eq hb' (by decide)] at hpost
    simp only [hfit, ↓reduceIte] at hpost
    obtain ⟨hx, hbuf2⟩ := hpost
    unfold slice at hbuf2
    rw [e1, e2, NativeRustcVm.ewsOf_of_ewsAt hxs, List.toList_toArray] at hbuf2
    exact cont st m2 hm1 hfr2 hbuf2 hx ((hb.trans hc).mono (fun p hp ↦ by simp at hp)
      (fun o ho ↦ by simpa using ho)) hkt hcs

omit [Host] in
/-- The claim's first `n` coordinates. -/
theorem prefix_ews {d : Mem 64} {p : BitVec 64} {xs : Array EW} {n : Nat}
    (h : NativeRustcVm.EWsAt d p xs.toList) : NativeRustcVm.EWsAt d p (xs.extract 0 n).toList := by
  have e : xs.toList = (xs.extract 0 n).toList ++ (xs.extract n xs.size).toList := by
    rw [← Array.toList_append, Array.extract_append_extract, show min 0 n = 0 from rfl,
      Array.extract_eq_self_of_le (Nat.le_max_right _ _)]
  rw [e, NativeRustcVm.ewsAt_append] at h
  exact h.1

/-- **The rest of the output point and the return** (`b68` to `b73`). -/
theorem stepOut2 (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {m : MachineData} {s3 : TState} {cj : KeccakClaimW} {outs : Array ColumnClaimW}
    {low sl xs : Array EW} (hz : AtZ a s cs inst output m0 m s3 cj outs low sl xs) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b68Offset)⟩ := by
  have hN := hn.hN
  have n1 := h.n1
  have n30 := h.n30
  have hpsz := hz.psz
  have hwf := envM_wf hn hz.fr
  have hpe := hz.claim.2.2.2.2
  rw [show NativeRustcVm.KeccakGkr.off (loc m0 960) NativeRustcVm.KeccakGkr.pointOff + 8#64 =
    loc m0 1248 from (congrArg (· + 8#64) (loc_add m0 960 280)).trans (loc_add m0 1240 8)] at hpe
  have hpre := prefix_ews (n := m0.regs.X1.toNat - 4) hpe
  have hplen : (cj.point.extract 0 (m0.regs.X1.toNat - 4)).toList.length =
      m0.regs.X1.toNat - 4 := by
    simp only [Array.length_toList, Array.size_extract]; omega
  have l88 : (envM m0 m).load 0 88 8 = (packW m0).toBitVec := Sumcheck.load_word hz.pk
  have hpk : (packW m0).toNat = m0.regs.X1.toNat - 4 := by
    unfold packW; exact u64_toNat' (by omega)
  -- `b68`
  refine extO h hn hext (b68_in_code.trans hp.1 (by simp [b68])) run_b68 hz.fr rfl rfl hz.w72 rfl
    (A := loc m0 1248) (xs := (cj.point.extract 0 (m0.regs.X1.toNat - 4)).toList)
    (fun st hm1 hfr1 ↦ ?_) hz.obuf (by rw [hplen]; simp [hz.lowsz]; omega)
    fun st m2 hm1 hfr2 hbuf2 hx2 hc2 hk2 hcs2 ↦ ?_
  · have hd : st.dmem = m.dmem := hm1.dmem_eq hwf rfl
    refine ⟨by rw [show st.regs.X1 = st.regs.getXReg .X1 from rfl,
        hm1.regs .X1 _ rfl]; exact hz.x23,
      ?_, by rw [hd]; exact hpre, ?_, ?_⟩
    · rw [hplen, ← UInt64.toNat_toBitVec, show st.regs.X2 = st.regs.getXReg .X2 from rfl,
        hm1.regs .X2 _ rfl]
      have hlt : m0.regs.X1.toNat - 4 < (m.regs.getXReg .X24).toNat := by rw [hz.x24]; omega
      simp only [Sym.eval, SBool.eval, CmpOp.apply, Sym.low_W64, Env.ofMachine_regs, l88,
        BitVec.ult, UInt64.toNat_toBitVec, hpk]
      rw [ite_eq_left (decide_eq_true hlt), UInt64.toNat_toBitVec, hpk]
    · rw [hplen]; exact ⟨frame_mapped' hn hfr1 (by omega), loc_noWrap hn (by omega)⟩
    · rw [hplen]; unfold Apart; rw [loc_toNat hn.hN (by decide)]
      obtain h1 | h1 := hn.oS <;> omega
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b68Offset + b68.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b69Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b68_next]]
  refine failBranchF hp hn (b69_in_code.trans hp.1 (by simp [b69])) run_b69 hfr2 rfl rfl
    (L := []) (by decide) (b := true)
    (condW0 (by rw [Env.ofMachine_regs, gx0, hx2]; rfl)) (fun hf ↦ nomatch hf)
    fun _ m3 hfr3 hd3 _ ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b69Offset + b69.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b70Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b69_next]]
  have hwf3 := envM_wf hn hfr3
  have w72 : NativeRustcVm.WordAt m3.dmem (loc m0 72) m0.regs.X7 := by
    rw [hd3]; exact hc2.word hn (by decide) (by decide) (by decide) hz.w72
  -- `b70`
  refine extO h hn hext (b70_in_code.trans hp.1 (by simp [b70])) run_b70 hfr3 rfl rfl w72 rfl
    (A := loc m0 2496) (xs := sl.toList) (fun st hm1 hfr1 ↦ ?_) (by rw [hd3]; exact hbuf2)
    (by simp only [List.length_append, hplen, Array.length_toList, hz.lowsz, hz.slsz]; omega)
    fun st4 m4 hm4 hfr4 hbuf4 hx4 hc4 hk4 hcs4 ↦ ?_
  · have hd : st.dmem = m3.dmem := hm1.dmem_eq hwf3 rfl
    refine ⟨reg_loc hm1 (r := .X1) (o := 2496) rfl, ?_, ?_, ?_, ?_⟩
    · rw [show st.regs.X2 = (6 : UInt64) from reg_of hm1 (r := .X2) (v := .lit 6) rfl rfl,
        Array.length_toList, hz.slsz]; rfl
    · rw [hd, hd3]
      exact hc2.ews hn (by decide) (o := 2496) (k := 96) (by decide) (by decide)
        (by simp [Array.length_toList, hz.slsz]) hz.slot
    · exact ⟨frame_mapped' hn hfr1 (by simp [hz.slsz]), loc_noWrap hn (by simp [hz.slsz])⟩
    · unfold Apart; rw [loc_toNat hn.hN (by decide)]; simp only [Array.length_toList, hz.slsz]
      obtain h1 | h1 := hn.oS <;> omega
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b70Offset + b70.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b71Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b70_next]]
  have T : Chg m0 [] [(3, 0, 584)] m.dmem m4.dmem :=
    (hc2.trans (hd3 ▸ hc4)).mono (fun p hp ↦ by simp at hp) (fun o ho ↦ by simpa using ho)
  have hk : Kept m.dmem m4.dmem := kept_tr hk2 (hd3 ▸ hk4)
  -- `b71`
  refine blockStep hn (b71_in_code.trans hp.1 (by simp [b71])) run_b71 hfr4 rfl rfl
    fun st hm5 hfr5 hd5 hpc ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only [PcOk] at hpc
  rw [show Labels.label NativeRustcVmArm.Vm.VerifyKeccak.label_32 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b73Offset) from
    hp.label (j := NativeRustcVmArm.Vm.VerifyKeccak.b73Offset) NativeRustcVmArm.Vm.VerifyKeccak.label_32_at] at hpc
  subst hpc
  refine goal_exit hp hn hfr5 ?_ fun outs' pt sl' s' hr ↦ ?_
  · rw [show d.regs.X0 = d.regs.getXReg .X0 from rfl,
      Match.reg_eq (matchM hn hfr4) hm5 (r := .X0) rfl rfl, gx0, hx4, hz.run]; rfl
  · rw [hz.run, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hr
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hr
    simp only at hd5
    rw [hd5]
    refine ⟨T.ts hn hk (by decide) (by decide) (by decide) hz.ts,
      T.cls hn (by decide) (by decide) (by decide) hz.cls, ?_, hz.xsz, ?_⟩
    · rw [Array.toList_append, Array.toList_append]; exact hbuf4
    · exact T.ewsOut hn (by decide) (by decide) (i := 3) (o := 584) (k := 1024)
        (by decide) (by decide) (by decide) (by decide) (by simp [Array.length_toList, hz.xsz])
        hz.slices

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
