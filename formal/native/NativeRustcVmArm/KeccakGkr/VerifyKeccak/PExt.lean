module

public import NativeRustcVmArm.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Word

/-!
# `verify_keccak`: extending the output point

`extC`: a block writing the frame's ranges `Lb`, then `Buf<EW, 36>::extend` of the frame's buffer
at 2592 by elements `xs` that fit: the buffer holds its elements then `xs`, X0 `1`. `inst`'s low
four coordinates and the rest (`inst_split`, `split_ews`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak

public section

theorem inst_split (xs : Array EW) : xs.extract 0 4 ++ xs.extract 4 xs.size = xs := by
  rw [Array.extract_append_extract, show min 0 4 = 0 from rfl]
  exact Array.extract_eq_self_of_le (Nat.le_max_right _ _)

/-- `inst`'s low four coordinates at its address, the rest at the address `b0` computes. -/
theorem split_ews {d : Mem 64} {ip : BitVec 64} {xs : Array EW}
    (h : NativeRustcVm.EWsAt d ip xs.toList) :
    NativeRustcVm.EWsAt d ip (xs.extract 0 4).toList ∧
      NativeRustcVm.EWsAt d (if xs.size < 4 then 8#64 else ip + 64#64)
        (xs.extract 4 xs.size).toList := by
  have e : xs.toList = (xs.extract 0 4).toList ++ (xs.extract 4 xs.size).toList := by
    rw [← Array.toList_append, inst_split]
  rw [e, NativeRustcVm.ewsAt_append] at h
  refine ⟨h.1, ?_⟩
  split
  · have : (xs.extract 4 xs.size).toList = [] :=
      List.eq_nil_of_length_eq_zero (by simp; omega)
    rw [this]; exact NativeRustcVm.ewsAt_nil _ _
  · have hl : (xs.extract 0 4).toList.length = 4 := by simp; omega
    have := h.2
    rw [hl] at this
    exact this

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **A block writing the frame's ranges `Lb`, then `extend` of the buffer at 2592.** -/
theorem extC (hn : Nums a inst m0)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {ds : List Directive} {i : Nat} {S' : SState} {m : MachineData} {Lb : List (Nat × Nat)}
    {R : MachineState → Prop} {A : BitVec 64} {L xs : List EW}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.BufEW36Extend.entryLabel))
    (hmid : Mid m0 m) (hsp : S'.sp = .ptr 0 0)
    (hw : S'.mem.all (fun w ↦ w.r == 0 &&
      Lb.any (fun p ↦ decide (p.1 ≤ w.off) && decide (w.off + w.n ≤ p.2))) = true)
    (hLb : okL Lb = true)
    (hL88 : (Lb ++ [(2592, 3176)]).all (fun p ↦ decide (p.2 ≤ 88) || decide (96 ≤ p.1)) = true)
    (hrk : regsL.all (fun r ↦ (midS.reg r).isSome && S'.reg r == midS.reg r) = true)
    (hx0 : S'.reg .X0 = some (.ptr 0 2592))
    (hst : ∀ st, Match (envM m0 m) S' st → VFr m0 st →
      st.regs.X1.toBitVec = A ∧ st.regs.X2.toNat = xs.length ∧
      NativeRustcVm.BufEWAt st.dmem (loc m0 2592) 36 L ∧ NativeRustcVm.EWsAt st.dmem A xs ∧
      Readable st A (16 * xs.length) ∧ Apart (loc m0 2592) 584 A (16 * xs.length))
    (hfit : L.length + xs.length ≤ 36)
    (cont : ∀ st m2 : MachineData, Match (envM m0 m) S' st → Mid m0 m2 →
      NativeRustcVm.BufEWAt m2.dmem (loc m0 2592) 36 (L ++ xs) → m2.regs.X0 = 1 →
      Chg m0 Lb [] m.dmem st.dmem → Chg m0 [(2592, 3176)] [] st.dmem m2.dmem →
      Kept m.dmem m2.dmem →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := envM_wf hn hmid.fr
  refine callC hn hk hrun hmid.fr (matchM hn hmid.fr) hwf hsp hw hLb (L := [(2592, 3176)])
    (O := []) (lo := 2592) (n := 584) (by decide) (by decide) rfl hext
    (fun st hm1 hfr1 ↦ ?_) (fun st m' hm1 hfr1 hq ↦ ?_)
    fun st m2 hm1 hfr1 hq hfr2 hcs hb hc hkt ↦ ?_
  all_goals have e0 : st.regs.X0.toBitVec = loc m0 2592 := reg_loc hm1 hx0
  · obtain ⟨e1, e2, hbuf, -, hrd, hap⟩ := hst st hm1 hfr1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e0, NativeRustcVm.wordOf_of_wordAt hbuf.2.1,
        u64_toNat' (by have := hbuf.1; omega)]
      exact hbuf.1
    · rw [e0]; exact ⟨frame_mapped' hn hfr1 (by decide), loc_noWrap hn (by decide)⟩
    · rw [e1, e2]; exact hrd
    · rw [e0, e1, e2]; exact hap
  · obtain ⟨-, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rw [e0] at hq
    rcases hq with hq | hq
    · exact ws_loc hn (o := 2592) (n := 584) (List.mem_singleton_self _) (by decide) hq
    · exact ws_stk hn hfr1 (by decide) hq
  · obtain ⟨e1, e2, hbuf, hxs, -, -⟩ := hst st hm1 hfr1
    obtain ⟨hpost, -, -⟩ := hq
    rw [e0, NativeRustcVm.wordOf_of_wordAt hbuf.2.1,
      u64_toNat' (by have := hbuf.1; omega), e2,
      KeccakGkr.bufEWOf_eq hbuf (by decide)] at hpost
    simp only [hfit, ↓reduceIte] at hpost
    obtain ⟨hx, hbuf2⟩ := hpost
    unfold slice at hbuf2
    rw [e1, e2, NativeRustcVm.ewsOf_of_ewsAt hxs, List.toList_toArray] at hbuf2
    exact cont st m2 hm1
      (Mid.chg hn hmid hfr2 (regs_kept (matchM hn hmid.fr) hm1 hrk hcs) (hb.trans hc) rfl hL88)
      hbuf2 hx hb hc hkt hcs

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
