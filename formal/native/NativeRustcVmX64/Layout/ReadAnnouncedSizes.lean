module

public import NativeRustcVmX64.Layout.ReadAnnouncedSizes.Rows
public import NativeRustcVmX64.Code.Vm.BuildLayout.Names
public import NativeRustcVmX64.Code.Vm.ReadAnnouncedSizes.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-!
# `read_announced_sizes` on x86-64

**`readAnnouncedSizes_spec`**: rustc's `read_announced_sizes(t, bytecode_len, layout)`, placed
anywhere in the program, meets `ReadAnnouncedSizesPre`/`Post` given `read_scalars`' and
`build_layout`'s contracts. The prologue (`b0`) pushes R15, R14, RBX below a 176-byte frame
(`F = 208`), keeps `layout` in RBX and `bytecode_len` in R14, zeroes `announced` and reads the
eight scalars into it (the frame's bytes `8`-`136`); `b1` returns `0` on `None`; `b2`-`b9` check
the high limbs (`check`), then `from10` (the rate, `build_layout`, the stack's log-size). The
model is `NativeVm.Math.Layout.readAnnouncedSizes_run` with `tailP`.
-/

namespace NativeRustcVmX64.Layout.ReadAnnouncedSizes

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ReadAnnouncedSizes NativeVm.Model
open NativeRustcVm.Layout NativeRustcVm.Transcript NativeRustcVmX64.Transcript
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck
open NativeVm.Math.Layout (readAnnouncedSizes_run)

public section

section
variable [Labels] {bc : Array UInt64} {a : DecArea} {s : TState} {m0 : MachineData}

/-- What `read_scalars` changes misses the frame from offset `136` and the return address. -/
theorem rs_out (h : ReadAnnouncedSizesPre bc a s m0) {d : MachineData} (hb : Bod m0 0 d) {j : Nat}
    (hj1 : 136 ≤ j) (hj : j < 216) :
    ¬ (NativeRustcVm.InRange (off (fb m0) 8) (16 * 8) (off (fb m0) j) ∨
      NativeRustcVm.InRange (tA m0) tstateBytes (off (fb m0) j) ∨
      NativeRustcVm.InRange (stackBelow d readScalarsStack) readScalarsStack (off (fb m0) j)) := by
  have hnw := (ctx h).noWrap_frame
  unfold NativeRustcVm.NoWrap at hnw
  rintro (hq | hq | hq)
  · rw [inRange_off_iff (by omega) (by omega)] at hq
    omega
  · exact outs_frame h hj (.inr hq)
  · exact not_callee h hb le_rs hj hq

end

variable [Host] {k : Nat}

/-- **`read_announced_sizes`' contract.** -/
theorem readAnnouncedSizes_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hbl : ∀ bc, Spec (Labels.label NativeRustcVmX64.Vm.BuildLayout.entryLabel) (BuildLayoutPre bc) (BuildLayoutPost bc))
    (bc : Array UInt64) (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmX64.Vm.ReadAnnouncedSizes.entryLabel) (ReadAnnouncedSizesPre bc a s)
      (ReadAnnouncedSizesPost bc a s) := by
  intro m0 h
  show Eventually (step1 Host.exe) (Goal bc a s m0) _
  obtain ⟨-, -, -, hts0, -⟩ := pre_parts h
  have c := ctx h
  rw [lbl_entry hp]
  -- `b0`: the prologue, `announced` zeroed, `read_scalars(t, announced, 8)`.
  let ra := (Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b0Offset + b0.length)).toBitVec
  have hwf := wf0 h (d := m0) (fun _ h ↦ h) ra
  have hm : Match (frameEnv m0 m0 208 [] (fun _ ↦ 0) ra) entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf (fun _ _ ↦ rfl) hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hW, xsi, xdx, xdi, xbx, x14⟩ := ok_b0
  have hfr : Frame m0 208 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf hm1 hpro slots_le slots_cs
  have hs0 := same_block hwf hm1 (writesIn_of_pro hpro) (belowRet_of_pro hpro) hW
    (X := fun _ ↦ False) (fun _ h ↦ nomatch h)
  have hb1 : Bod m0 0 st1.data :=
    ⟨hfr, NativeRustcVm.SameOutside.mono hs0 fun q hq ↦
      hq.elim (fun h ↦ .inr (c.inRange_frame h)) False.elim⟩
  have hx0 : reg st1.data .rdi = tA m0 := hm1.regs .rdi _ xdi
  have hx1 : reg st1.data .rsi = off (fb m0) 8 := (hm1.regs .rsi _ xsi).trans (eval_ptr0 8)
  have hx2 : (reg st1.data .rdx).toNat = 8 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ xdx]; rfl
  have hbx : reg st1.data .rbx = lA m0 := hm1.regs .rbx _ xbx
  have h14 : reg st1.data .r14 = reg m0 .rsi := hm1.regs .r14 _ x14
  have hat := at0 h hb1
  have hts1 : TStateAt st1.data.dmem (tA m0) a s :=
    ts_keep h hts0 (hm1.kept hwf) hs0 fun q hq ↦ .inl (hq.elim c.inRange_frame False.elim)
  have hpre : ReadScalarsPre a s st1.data := by
    simp only [ReadScalarsPre]
    rw [hx0, hx1, hx2]
    refine ⟨c.stackOk hat le_rs, c.rcAt hat le_rs, hts1, c.tstateOk hat le_rs,
      c.outOk_frame hat le_rs (o := 8) (n := 16 * 8) (by omega) (by omega), ?_⟩
    apply got_callee ((pre_got h).symbols (by decide : ["memcpy"].Sublist ["memcpy", "memset"]))
      (fun l hl => got_bytes h hb1 l (by simp_all)) hat.sp c.spN le_rs
    intro l hl a' ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ((pre_got h).1 l (by simp_all)).2.2.2 _ (by simp)
    · exact ((pre_got h).1 l (by simp_all)).2.2.2 _ (by simp)
    · exact got_apart_frame (pre_got h) c.stack (by simp_all) F_le (by dsimp only; decide)
    · exact ((pre_got h).1 l (by simp_all)).2.2.2 _ (by simp)
  refine call_then hpc1 (hrs a s) hpre fun st2 hpc2 hrsp2 hq2 ↦ ?_
  simp only [ReadScalarsPost] at hq2
  rw [hx0, hx1, hx2] at hq2
  obtain ⟨hok2, hxs2, hnext2, hso2, hsv2⟩ := hq2
  have hso2' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      NativeRustcVm.InRange (off (fb m0) 8) (16 * 8) q ∨
        NativeRustcVm.InRange (tA m0) tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow st1.data readScalarsStack) readScalarsStack q) := hso2
  have hfnw : NativeRustcVm.NoWrap (stackBelow m0 208) 208 := by
    have := c.noWrap_frame; unfold NativeRustcVm.NoWrap at this ⊢; omega
  have hb2 : Bod m0 8 st2.data := by
    refine hb1.call_at hsv2 hrsp2 hso2' (fun q hq ↦ ?_)
      (fun p hp i hi ↦ rs_out h hb1 (by have := slots_ge p hp; omega)
        (by have := slots_ge p hp; omega))
      (fun j hj ↦ rs_out h hb1 (by omega) (by omega))
    rcases hq with hq | hq | hq
    · exact .inr (c.inRange_frame (inRange_of_off hfnw (by omega) hq))
    · exact .inl (.inr hq)
    · exact .inr (callee_stack h hb1 le_rs hq)
  -- `b1`: `None` returns `0`.
  have hwf2 := wf0 h hb2.fr.kept 0
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf2 nofun
    (hpc2.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b0_next]))) (match_mid hb2 0)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hax3, hk3⟩ := ok_b1
  obtain ⟨hb3, hd3⟩ := step0 h hb2 hwf2 hm3 hmid3 hmem3
  have hok' : (reg st2.data .rax).toNat % 256 = (okWord ((readScalars 8).run s).isSome).toNat :=
    hok2
  have hc : c1.eval (frameEnv m0 st2.data 208 [] (fun _ ↦ 0) 0) =
      !((readScalars 8).run s).isSome := by
    rw [c1_eval]
    show decide ((reg st2.data .rax).toNat % 256 = 0) = _
    rw [hok', okWord_test]
  have hrax3 : reg st3.data .rax = 0 := hm3.regs .rax _ hax3
  simp only [PcOk] at hpc3
  cases hr : (readScalars 8).run s with
  | none =>
    refine fail78 hp h hb3 ((pc_true hpc3 (by rw [hc, hr]; rfl)).trans (lbl_21 hp)) hrax3 ?_
    rw [readAnnouncedSizes_run, show 2 + nTables = 8 from rfl, hr]; rfl
  | some p =>
  obtain ⟨xs, s1⟩ := p
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b2Offset) :=
    (pc_false hpc3 (by rw [hc, hr]; rfl)).trans
      (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b1_next]))
  have hM : Mid a m0 xs s1 st3.data :=
    ⟨hb3, hrax3, (keeps_reg hm3 hk3 (r := .rbx) (by simp)).trans ((hsv2.1 .rbx rfl).trans hbx),
      (keeps_reg hm3 hk3 (r := .r14) (by simp)).trans ((hsv2.1 .r14 rfl).trans h14),
      by rw [hd3]; exact hxs2 xs s1 hr, NativeRustcVm.Sumcheck.readScalars_size hr,
      by rw [hd3]; exact hnext2 xs s1 hr⟩
  have hsz := hM.size
  -- `b2`-`b9`: the high limbs.
  obtain ⟨o2, o3, o4, o5, o6, o7, o8, o9⟩ := ok_b2_b9
  refine check h (infix_of b2_in_code (by simp [b2]) hp) exit_b2 o2 hpc3' hM
    (hM.word (i := 0) (by omega)).2 (fun st' hpc' hM' hv ↦ fail78 hp h hM'.bd
      (hpc'.trans (lbl_21 hp)) hM'.rax (run_none_c1 hr (by omega) hv)) fun st hpc hM h0 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b3Offset) :=
    hpc.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b2_next]))
  refine check h (infix_of b3_in_code (by simp [b3]) hp) exit_b3 o3 hpc hM
    (hM.word (i := 1) (by omega)).2 (fun st' hpc' hM' hv ↦ fail78 hp h hM'.bd
      (hpc'.trans (lbl_21 hp)) hM'.rax (run_none_c1 hr (by omega) hv)) fun st hpc hM h1 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b4Offset) :=
    hpc.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b3_next]))
  refine check h (infix_of b4_in_code (by simp [b4]) hp) exit_b4 o4 hpc hM
    (hM.word (i := 2) (by omega)).2 (fun st' hpc' hM' hv ↦ fail78 hp h hM'.bd
      (hpc'.trans (lbl_21 hp)) hM'.rax (run_none_c1 hr (by omega) hv)) fun st hpc hM h2 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b5Offset) :=
    hpc.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b4_next]))
  refine check h (infix_of b5_in_code (by simp [b5]) hp) exit_b5 o5 hpc hM
    (hM.word (i := 3) (by omega)).2 (fun st' hpc' hM' hv ↦ fail78 hp h hM'.bd
      (hpc'.trans (lbl_21 hp)) hM'.rax (run_none_c1 hr (by omega) hv)) fun st hpc hM h3 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b6Offset) :=
    hpc.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b5_next]))
  refine check h (infix_of b6_in_code (by simp [b6]) hp) exit_b6 o6 hpc hM
    (hM.word (i := 4) (by omega)).2 (fun st' hpc' hM' hv ↦ fail78 hp h hM'.bd
      (hpc'.trans (lbl_21 hp)) hM'.rax (run_none_c1 hr (by omega) hv)) fun st hpc hM h4 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b7Offset) :=
    hpc.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b6_next]))
  refine check h (infix_of b7_in_code (by simp [b7]) hp) exit_b7 o7 hpc hM
    (hM.word (i := 5) (by omega)).2 (fun st' hpc' hM' hv ↦ fail78 hp h hM'.bd
      (hpc'.trans (lbl_21 hp)) hM'.rax (run_none_c1 hr (by omega) hv)) fun st hpc hM h5 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b8Offset) :=
    hpc.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b7_next]))
  refine check h (infix_of b8_in_code (by simp [b8]) hp) exit_b8 o8 hpc hM
    (hM.word (i := 6) (by omega)).2 (fun st' hpc' hM' hv ↦ fail78 hp h hM'.bd
      (hpc'.trans (lbl_21 hp)) hM'.rax (run_none_c1 hr (by omega) hv)) fun st hpc hM h6 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b9Offset) :=
    hpc.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b8_next]))
  refine check h (infix_of b9_in_code (by simp [b9]) hp) exit_b9 o9 hpc hM
    (hM.word (i := 7) (by omega)).2 (fun st' hpc' hM' hv ↦ fail79 hp h hM'.bd
      (hpc'.trans (lbl_22 hp)) hM'.rax (run_none_c1 hr (by omega) hv)) fun st hpc hM h7 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b10Offset) :=
    hpc.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b9_next]))
  have hc1 : ∀ i (hi : i < xs.size), xs[i].c1 = 0 := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption
  exact from10 hp hbl h hr (all_c1 hc1) hpc hM

end

end NativeRustcVmX64.Layout.ReadAnnouncedSizes
