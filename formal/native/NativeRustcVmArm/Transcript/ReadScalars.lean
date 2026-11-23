module

public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Transcript.Callee
public import NativeRustcVmArm.Transcript.ReadScalars.Exec
public import NativeRustcVm.Transcript.Loop

/-!
# `TState::read_scalars` on AArch64

**`readScalars_spec`**: X0 becomes `readScalars n`'s `Some`/`None`, the `n` elements at X1 its
elements and the `TState` at X0 its state, given `read_scalar`'s contract. `n = 0` returns `1` at
once (`b0`, `b6`). Otherwise `b1` saves X30, X21, X20, X19 and sets the output's cursor and end; the
loop (`b2` to `b4`, `step`, invariant `Inv`) reads a scalar into the frame and stores it at the
cursor until the end (`b5` returns `1`) or a rejection (`b7` returns `0`).
-/

namespace NativeRustcVmArm.Transcript.ReadScalars

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateReadScalars
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm

@[expose] public section

/-- At the loop's head, `i` elements read and stored: the frame, the `TState` (X20), the output's
end (X21) and cursor (X19), the first `i` elements and the state after them, nothing changed but
the output, the `TState` and the stack. -/
structure Inv (m0 : MachineData) (a : DecArea) (s : TState) (i : Nat) (d : MachineData) : Prop where
  frame : Frame m0 64 slots d
  x20 : d.regs.X20.toBitVec = m0.regs.X0.toBitVec
  x21 : d.regs.X21.toBitVec = off m0.regs.X1.toBitVec (16 * m0.regs.X2.toNat)
  x19 : d.regs.X19.toBitVec = off m0.regs.X1.toBitVec (16 * i)
  run : ∃ xs s', (pushes readScalar i).run s = some (xs, s') ∧
    NativeRustcVm.EWsAt d.dmem m0.regs.X1.toBitVec xs.toList ∧
    TStateAt d.dmem m0.regs.X0.toBitVec a s'
  same : SameOutside m0.dmem d.dmem (fun q ↦
    NativeRustcVm.InRange m0.regs.X1.toBitVec (16 * m0.regs.X2.toNat) q ∨
      NativeRustcVm.InRange m0.regs.X0.toBitVec tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q)

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 64 := by decide

theorem run_b5' : ∃ S', exec b5 doneS = some (S', .ret) ∧ EpiOk 64 slots S' = true ∧
    S'.mem = [] ∧ S'.reg .X0 = some (.lit 1) :=
  ⟨_, run_b5, after_eq run_b5 ▸ ok_b5⟩

theorem run_b7' : ∃ S', exec b7 doneS = some (S', .ret) ∧ EpiOk 64 slots S' = true ∧
    S'.mem = [] ∧ S'.reg .X0 = some (.lit 0) :=
  ⟨_, run_b7, after_eq run_b7 ▸ ok_b7⟩

variable [Host] {k : Nat}

/-- An epilogue returning X0 = `v` (`b5`, `b7`). -/
theorem finish {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j) (hne : b ≠ [])
    {v : Nat} (hrun : ∃ S', exec b doneS = some (S', .ret) ∧ EpiOk 64 slots S' = true ∧
      S'.mem = [] ∧ S'.reg .X0 = some (.lit v))
    (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 readScalarsStack)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hf : Frame m0 64 slots st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ st'.data.regs.X0.toBitVec =
      BitVec.ofNat 64 v ∧ st'.data.dmem = st.data.dmem ∧ Saved m0 st'.data) st := by
  obtain ⟨S', hx, hepi, hmem, hx0⟩ := hrun
  have hfnw := frame_noWrap (m := m0) (F := 64) (by
    have := hst.2.1; have : readScalarsStack = 608 := rfl; omega)
  have hwf : (frameEnv m0 st.data 64 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 64 []) doneS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of hb hne hp) hx hwf hpc hm fun st1 hm1 hpc1 => ?_
  obtain ⟨hsv, hsl⟩ := Frame.epilogue hf hwf hm1 hepi
  have hx30 : st1.data.regs.X30 = m0.regs.X30 := hsl (32, .X30) (List.mem_cons_self ..)
  exact .done _ ⟨by simp only [PcOk] at hpc1; rw [hpc1]; simp only [retOf, hx30],
    hm1.regs .X0 _ hx0, hm1.dmem_eq hwf hmem, hsv⟩

/-- **One round of the loop**: a scalar read and stored; the loop goes on, returns `1` at the end
or `0` on a rejection. -/
theorem step (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {a : DecArea} {s : TState} {m0 : MachineData} (hpre : ReadScalarsPre a s m0) {i : Nat}
    (hi : i < m0.regs.X2.toNat) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateReadScalars.b2Offset))
    (hI : Inv m0 a s i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      (st'.pc = retOf m0 ∧ ReadScalarsPost a s m0 st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateReadScalars.b2Offset) ∧ i + 1 < m0.regs.X2.toNat ∧ Inv m0 a s (i + 1) st'.data))
      st := by
  obtain ⟨hst, hrc, hts, htok, ⟨hom, hon, hoT, hoA, hoS, hoR⟩⟩ := hpre
  set t := m0.regs.X0.toBitVec with htdef
  set o := m0.regs.X1.toBitVec with hodef
  set n := m0.regs.X2.toNat with hndef
  set fb := frameBase m0 64 with hfb
  have hS : readScalarsStack = 608 := rfl
  have hn : readScalarsStack ≤ m0.regs.SP.toNat := hst.2.1
  have hfnw : fb.toNat + 64 ≤ 2 ^ 64 := frame_noWrap (m := m0) (F := 64) (by omega)
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hon' : o.toNat + 16 * n ≤ 2 ^ 64 := hon
  have hsnw : NativeRustcVm.NoWrap (stackBelow m0 readScalarsStack) readScalarsStack := by
    show _ + readScalarsStack ≤ _
    rw [toNat_stackBelow hn]; have := m0.regs.SP.toNat_lt; omega
  have hTF : NativeRustcVm.Apart t 760 fb 64 := apart_frame htok.1 hn (by decide)
  have hoF : NativeRustcVm.Apart o (16 * n) fb 64 := apart_frame hoS hn (by decide)
  have hslot : ∀ p ∈ slots, ∀ j < 8, NativeRustcVm.InRange fb 64 (off fb (p.1 + j)) :=
    fun p hp j hj ↦ inRange_off_self (by have := slots_le p hp; omega) (by omega)
  obtain ⟨hf, hx20, hx21, hx19, ⟨xs, s', hrun, hews, hts'⟩, hsame⟩ := hI
  have hxs : xs.size = i := pushes_size hrun
  -- `b2`: `bl read_scalar`, its output at `fb + 8`.
  have hwf : (frameEnv m0 st.data 64 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 64 []) callS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf hpc hm fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hmem3, hx0₃, hx1₃, hx19₃, hx20₃, hx21₃⟩ := after_eq run_b2 ▸ ok_b2
  have hf3 : Frame m0 64 slots st3.data := Frame.of_block hf hwf hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st.data.dmem := hm3.dmem_eq hwf hmem3
  have hX0₃ : st3.data.regs.X0.toBitVec = off fb 8 := by
    show (st3.data.regs.getXReg .X0).toBitVec = _
    rw [hm3.regs .X0 _ hx0₃]; rfl
  have hX1₃ : st3.data.regs.X1.toBitVec = t := by
    show (st3.data.regs.getXReg .X1).toBitVec = _
    rw [hm3.regs .X1 _ hx1₃]; exact hx20
  have hX19₃ : st3.data.regs.X19 = st.data.regs.X19 := Match.reg_eq hm hm3 rfl hx19₃
  have hX20₃ : st3.data.regs.X20 = st.data.regs.X20 := Match.reg_eq hm hm3 rfl hx20₃
  have hX21₃ : st3.data.regs.X21 = st.data.regs.X21 := Match.reg_eq hm hm3 rfl hx21₃
  -- `read_scalar`.
  have h3sp : st3.data.regs.SP.toNat = m0.regs.SP.toNat - 64 := by
    rw [← UInt64.toNat_toBitVec, hf3.sp, frameBase_toNat hn (by decide)]
  have hrcOut : ∀ q, (NativeRustcVm.InRange o (16 * n) q ∨ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q) →
      ¬ NativeRustcVm.InRange rcAddr 192 q := by
    rintro q (hq | hq | hq) h
    · exact not_inRange_of_apart (Apart.symm' hoR) hrc.2.1 hon h hq
    · exact not_inRange_of_apart (Apart.symm' htok.2.2) hrc.2.1 hTn h hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 hsnw h hq
  have hso3 : SameOutside m0.dmem st3.data.dmem (fun q ↦ NativeRustcVm.InRange o (16 * n) q ∨
      NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q) := by
    rw [hd3]; exact hsame
  have hts3 : TStateAt st3.data.dmem t a s' := by rw [hd3]; exact hts'
  have hpre3 : ReadScalarPre a s' st3.data := by
    unfold ReadScalarPre
    rw [hX1₃, hX0₃]
    exact ⟨stackOk_callee hst hf3.kept hf3.sp (by decide) (by decide) (by decide),
      RcAt.callee hrc (rc_keep hso3 hrcOut) hn (by decide) h3sp (by decide), hts3,
      TStateOk.callee htok hf3.sp hn (by decide) (by decide),
      OutOk.frame hst (by decide) (by decide) hf3.sp hf3.kept (by decide) htok hrc⟩
  refine call_then hpc3 (hrs a s') hpre3 fun st4 hpc4 ⟨hout4, hnext4, hs4, hsv4⟩ => ?_
  rw [hX0₃] at hout4
  rw [hX1₃] at hnext4
  rw [hX0₃, hX1₃] at hs4
  have hcal4 : ∀ q, NativeRustcVm.InRange (stackBelow st3.data readScalarStack) readScalarStack q →
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q ∧
        ¬ NativeRustcVm.InRange fb 64 q :=
    fun q hq ↦ inRange_callee hf3.sp hn (by decide) (by decide) hq
  have hf4 : Frame m0 64 slots st4.data := by
    refine Frame.call_slots hf3 hsv4 hs4 fun p hp j hj h ↦ ?_
    rcases h with h | h | h
    · exact not_slot_out hfnw (by decide) slots_le (by decide) p hp j hj h
    · exact not_inRange_of_apart hTF hTn hfnw h (hslot p hp j hj)
    · exact (hcal4 _ h).2 (hslot p hp j hj)
  have hso4 : SameOutside m0.dmem st4.data.dmem (fun q ↦ NativeRustcVm.InRange o (16 * n) q ∨
      NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q) :=
    fun q hq ↦ by
      simp only [not_or] at hq
      have hqf : ¬ NativeRustcVm.InRange fb 64 q :=
        fun h ↦ hq.2.2 (inRange_frame_stack hn (by decide) h)
      rw [hs4 q (by
        rintro (h | h | h)
        · exact hqf (inRange_of_off hfnw (by decide) h)
        · exact hq.2.1 h
        · exact hq.2.2 (hcal4 q h).1)]
      exact hso3 q (by simp only [not_or]; exact hq)
  have hlen : 16 * xs.toList.length ≤ 16 * n := by
    rw [Array.length_toList, hxs]; omega
  have hews4 : NativeRustcVm.EWsAt st4.data.dmem o xs.toList := by
    refine ewsAt_keep hs4 (by omega) (fun q hq hr ↦ ?_) (hd3 ▸ hews)
    have hq' : NativeRustcVm.InRange o (16 * n) q := inRange_mono hq hlen
    rcases hr with hr | hr | hr
    · exact not_inRange_of_apart hoF hon hfnw hq' (inRange_of_off hfnw (by decide) hr)
    · exact not_inRange_of_apart hoT hon hTn hq' hr
    · exact not_inRange_of_apart hoS hon hsnw hq' (hcal4 q hr).1
  have hX19₄ : st4.data.regs.X19.toBitVec = off o (16 * i) := by
    rw [show st4.data.regs.X19 = st.data.regs.X19 from (hsv4.1 .X19 rfl).trans hX19₃]
    exact hx19
  have hX20₄ : st4.data.regs.X20.toBitVec = t := by
    rw [show st4.data.regs.X20 = st.data.regs.X20 from (hsv4.1 .X20 rfl).trans hX20₃]
    exact hx20
  have hX21₄ : st4.data.regs.X21.toBitVec = off o (16 * n) := by
    rw [show st4.data.regs.X21 = st.data.regs.X21 from (hsv4.1 .X21 rfl).trans hX21₃]
    exact hx21
  -- `b3`: the tag.
  have hwf4 : (frameEnv m0 st4.data 64 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst (by decide)) hf4.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm4 : Match (frameEnv m0 st4.data 64 []) tagS st4.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf4.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf4
    (hpc4.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadScalars.b2_next])) hm4 fun st5 hm5 hpc5 => ?_
  obtain ⟨hmid5, hmem5, hx19₅, hx20₅, hx21₅⟩ := after_eq run_b3 ▸ ok_b3
  have hf5 : Frame m0 64 slots st5.data := Frame.of_block hf4 hwf4 hm5 hmid5 slots_le
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf4 hmem5
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  cases hr : readScalar.run s' with
  | none =>
    -- A rejection: `0`.
    rw [hr] at hout4
    have h0 : NativeRustcVm.WordAt st4.data.dmem (off fb 8) 0 := hout4
    rw [load_ofMachine (o := 8) rfl h0] at hpc5
    simp (config := { decide := true }) only [↓reduceIte] at hpc5
    have hnone : (readScalars n).run s = none := pushes_none_of hrun hr n hi
    refine Eventually.mono (finish b7_in_code (by simp [b7]) run_b7' hp hst
      (hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.TStateReadScalars.b7Offset) NativeRustcVmArm.Vm.TStateReadScalars.label_6_at)) hf5) fun st' ⟨hpc', hx0', hd', hsv'⟩ ↦
        Or.inl ⟨hpc', ?_, ?_, ?_, ?_, hsv'⟩
    · show st'.data.regs.X0 = okWord ((readScalars n).run s).isSome
      rw [hnone]
      exact UInt64.toBitVec_inj.mp hx0'
    · intro xs' s'' h; rw [hnone] at h; cases h
    · intro x' s'' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd', hd5]; exact hso4 q hq
  | some p =>
  obtain ⟨x, s''⟩ := p
  rw [hr] at hout4
  obtain ⟨ht1, hel⟩ := (hout4 : OptEWAt st4.data.dmem (off fb 8) (some x))
  rw [ewAt_iff, off_off, off_off] at hel
  have hts4 : TStateAt st4.data.dmem t a s'' := hnext4 x s'' hr
  rw [load_ofMachine (o := 8) rfl ht1] at hpc5
  simp (config := { decide := true }) only [↓reduceIte] at hpc5
  -- `b4`: the element stored at the cursor, the cursor advanced.
  set w := off o (16 * i) with hw
  have hwn : w.toNat = o.toNat + 16 * i := toNat_off (by omega)
  have hwF : NativeRustcVm.Apart fb 64 w 16 := by
    have h : o.toNat + 16 * n ≤ fb.toNat ∨ fb.toNat + 64 ≤ o.toNat := hoF
    show fb.toNat + 64 ≤ w.toNat ∨ w.toNat + 16 ≤ fb.toNat
    omega
  have hwf5 : (frameEnv m0 st5.data 64 [(w, 16)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst (by decide)) hf5.kept, hfnw⟩,
      ⟨Mapped.keeps (mapped_off hom (by omega)) hf5.kept, by show w.toNat + 16 ≤ 2 ^ 64; omega⟩,
      trivial⟩ (List.pairwise_pair.mpr hwF)
  have hX19₅ : st5.data.regs.X19.toBitVec = w := by
    rw [show st5.data.regs.X19 = st4.data.regs.X19 from Match.reg_eq hm4 hm5 rfl hx19₅]
    exact hX19₄
  have hm5' : Match (frameEnv m0 st5.data 64 [(w, 16)]) storeS st5.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      (by rw [hf5.sp]; exact (eval_ptr rfl).symm) ⟨known_ptr rfl hX19₅, trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf5
    (hpc5.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadScalars.b3_next])) hm5' fun st6 hm6 hpc6 => ?_
  obtain ⟨hmid6, hw0, hw1, hws6, hx19₆, hx20₆, hx21₆⟩ := after_eq run_b4 ▸ ok_b4
  have hf6 : Frame m0 64 slots st6.data := Frame.of_block hf5 hwf5 hm6 hmid6 slots_le
  have hs6 : SameOutside st5.data.dmem st6.data.dmem (NativeRustcVm.InRange w 16) :=
    sameOutside_region hwf5 hm6 (r := 1) rfl hws6
  have hel6 : NativeRustcVm.EWAt st6.data.dmem w x := by
    refine ewAt_iff.mpr ⟨?_, ?_⟩
    · have := wordAt_write hm6 (r := 1) (o := 0) (b := w) (sz := 16) rfl (by decide) hw0
      rwa [off_zero, show (Sym.load 0 16 8).eval (frameEnv m0 st5.data 64 [(w, 16)]) = _ from
        load_ofMachine (o := 16) rfl (hd5 ▸ hel.1)] at this
    · have := wordAt_write hm6 (r := 1) (o := 8) (b := w) (sz := 16) rfl (by decide) hw1
      rwa [show (Sym.load 0 24 8).eval (frameEnv m0 st5.data 64 [(w, 16)]) = _ from
        load_ofMachine (o := 24) rfl (hd5 ▸ hel.2)] at this
  have hews6 : NativeRustcVm.EWsAt st6.data.dmem o (xs.push x).toList := by
    refine ewsAt_push.mpr ⟨ewsAt_keep hs6 (by omega) (fun q hq hr ↦ ?_) (hd5 ▸ hews4), ?_⟩
    · rw [Array.length_toList, hxs] at hq
      have hwnw : NativeRustcVm.NoWrap w 16 := by show w.toNat + 16 ≤ 2 ^ 64; omega
      have hon16 : NativeRustcVm.NoWrap o (16 * i) := by show o.toNat + 16 * i ≤ 2 ^ 64; omega
      rw [inRange_iff' hon16] at hq
      rw [inRange_iff' hwnw] at hr
      omega
    · rw [hxs]; exact hel6
  have hR6 : ∀ q, NativeRustcVm.InRange w 16 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q := by
    intro q hq
    have hq' : NativeRustcVm.InRange o (16 * n) q := inRange_sub hon (by omega) (by omega) hq
    exact ⟨fun h ↦ not_inRange_of_apart hoT hon hTn hq' h,
      fun h ↦ not_inRange_of_apart hoA hon hAn hq' h⟩
  have hts6 : TStateAt st6.data.dmem t a s'' := (hd5 ▸ hts4).frame (hm6.kept hwf5) hR6 hs6
  have hso6 : SameOutside m0.dmem st6.data.dmem (fun q ↦ NativeRustcVm.InRange o (16 * n) q ∨
      NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarsStack) readScalarsStack q) :=
    fun q hq ↦ by
      rw [hs6 q fun h ↦ hq (Or.inl (inRange_sub hon (by omega) (by omega) h)), hd5]
      exact hso4 q hq
  have hrun' : (pushes readScalar (i + 1)).run s = some (xs.push x, s'') := by
    rw [pushes_succ, hrun]
    show (readScalar.run s').map _ = _
    rw [hr]; rfl
  have hX19₆ : st6.data.regs.X19.toBitVec = off o (16 * (i + 1)) := by
    show (st6.data.regs.getXReg .X19).toBitVec = _
    rw [hm6.regs .X19 _ hx19₆]
    show w + BitVec.ofInt 64 16 = _
    rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, hw, off_add,
      show 16 * i + 16 = 16 * (i + 1) by omega]
  have hX20₆ : st6.data.regs.X20.toBitVec = t := by
    rw [show st6.data.regs.X20 = st4.data.regs.X20 from
      (Match.reg_eq hm5' hm6 rfl hx20₆).trans (Match.reg_eq hm4 hm5 rfl hx20₅)]
    exact hX20₄
  have hX21₆ : st5.data.regs.X21.toBitVec = off o (16 * n) := by
    rw [show st5.data.regs.X21 = st4.data.regs.X21 from Match.reg_eq hm4 hm5 rfl hx21₅]
    exact hX21₄
  -- The cursor against the end.
  have hcond : (SBool.cmp .eq .W64 (.ptr 1 16) (.reg .X21)).not.eval
      (frameEnv m0 st5.data 64 [(w, 16)]) = decide (i + 1 ≠ n) := by
    simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, Env.ofMachine_regs]
    rw [show (frameEnv m0 st5.data 64 [(w, 16)]).base 1 = w from rfl,
      show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, hw, off_add,
      show 16 * i + 16 = 16 * (i + 1) by omega, show (st5.data.regs.getXReg .X21).toBitVec =
        off o (16 * n) from hX21₆,
      show (off o (16 * (i + 1)) == off o (16 * n)) = decide (i + 1 = n) from by
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; exact off_eq_iff hon' hi]
    by_cases h : i + 1 = n <;> simp [h]
  simp only [PcOk] at hpc6
  rw [hcond] at hpc6
  by_cases hlast : i + 1 = n
  · -- The end: `1`.
    simp only [hlast, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc6
    have hrn : (readScalars n).run s = some (xs.push x, s'') := by
      rw [readScalars_eq, show n = i + 1 from hlast.symm]; exact hrun'
    refine Eventually.mono (finish b5_in_code (by simp [b5]) run_b5' hp hst
      (hpc6.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadScalars.b4_next])) hf6) fun st' ⟨hpc', hx0', hd', hsv'⟩ ↦
        Or.inl ⟨hpc', ?_, ?_, ?_, ?_, hsv'⟩
    · show st'.data.regs.X0 = okWord ((readScalars n).run s).isSome
      rw [hrn]
      exact UInt64.toBitVec_inj.mp hx0'
    · intro xs' s3 h
      rw [hrn] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hd']; exact hews6
    · intro xs' s3 h
      rw [hrn] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hd']; exact hts6
    · intro q hq; rw [hd']; exact hso6 q hq
  · simp only [hlast, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hpc6
    exact .done _ (Or.inr ⟨hpc6.trans (hp.label (j := NativeRustcVmArm.Vm.TStateReadScalars.b2Offset) NativeRustcVmArm.Vm.TStateReadScalars.label_2_at), by omega,
      ⟨hf6, hX20₆, by
        rw [show st6.data.regs.X21 = st5.data.regs.X21 from Match.reg_eq hm5' hm6 rfl hx21₆]
        exact hX21₆, hX19₆,
        ⟨_, _, hrun', hews6, hts6⟩, hso6⟩⟩)


/-- **`TState::read_scalars` meets its contract.** -/
theorem readScalars_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s) := by
  intro m0 hpre
  obtain ⟨hst, hrc, hts, htok, ⟨hom, hon, hoT, hoA, hoS, hoR⟩⟩ := id hpre
  set t := m0.regs.X0.toBitVec with htdef
  set o := m0.regs.X1.toBitVec with hodef
  set n := m0.regs.X2.toNat with hndef
  set fb := frameBase m0 64 with hfb
  have hn : readScalarsStack ≤ m0.regs.SP.toNat := hst.2.1
  have hfnw : fb.toNat + 64 ≤ 2 ^ 64 :=
    frame_noWrap (m := m0) (F := 64) (by have : readScalarsStack = 608 := rfl; omega)
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTF : NativeRustcVm.Apart t 760 fb 64 := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb 64 := apart_frame htok.2.1 hn (by decide)
  -- `b0`: `n = 0`?
  unfold NativeRustcVmArm.Vm.TStateReadScalars.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.TStateReadScalars.entryOffset) NativeRustcVmArm.Vm.TStateReadScalars.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 (Env.wf_nil m0) (match_nil m0)
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hmem1, hk1⟩ := after_eq run_b0 ▸ ok_b0
  have hd1 : st1.data.dmem = m0.dmem := hm1.dmem_eq (Env.wf_nil _) hmem1
  have hsv1 : Saved m0 st1.data := Match.saved (match_nil m0) hm1 (Env.wf_nil _) rfl hk1
  have hX0 : st1.data.regs.X0 = m0.regs.X0 := Match.reg_eq (r := .X0) (match_nil m0) hm1 rfl rfl
  have hX1 : st1.data.regs.X1 = m0.regs.X1 := Match.reg_eq (r := .X1) (match_nil m0) hm1 rfl rfl
  have hX2 : st1.data.regs.X2 = m0.regs.X2 := Match.reg_eq (r := .X2) (match_nil m0) hm1 rfl rfl
  have hX30 : st1.data.regs.X30 = m0.regs.X30 :=
    Match.reg_eq (r := .X30) (match_nil m0) hm1 rfl rfl
  simp only [PcOk] at hpc1
  split at hpc1
  · -- `n = 0`: `1`.
    rename_i hc
    have hn0 : n = 0 := by
      sym_simp at hc
      simp only [Env.ofMachine_regs, beq_iff_eq] at hc
      show m0.regs.X2.toBitVec.toNat = 0
      exact (congrArg BitVec.toNat hc).trans rfl
    have hr0 : (readScalars n).run s = some (#[], s) := by
      rw [readScalars_eq, show n = 0 from hn0]; rfl
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 (Env.wf_nil _)
      (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.TStateReadScalars.b6Offset) NativeRustcVmArm.Vm.TStateReadScalars.label_5_at)) (match_nil _) fun st2 hm2 hpc2 => ?_
    obtain ⟨hmem2, hk2, h30, hx0⟩ := after_eq run_b6 ▸ ok_b6
    have hd2 : st2.data.dmem = m0.dmem := (hm2.dmem_eq (Env.wf_nil _) hmem2).trans hd1
    have hx30 : st2.data.regs.X30 = m0.regs.X30 :=
      (Match.reg_eq (match_nil _) hm2 rfl h30).trans hX30
    refine .done _ ⟨by simp only [PcOk] at hpc2; rw [hpc2]; simp only [retOf, hx30], ?_, ?_, ?_,
      fun q _ ↦ by rw [hd2], hsv1.trans (Match.saved (match_nil _) hm2 (Env.wf_nil _) rfl hk2)⟩
    · show st2.data.regs.X0 = okWord ((readScalars n).run s).isSome
      rw [hr0]
      exact UInt64.toBitVec_inj.mp (hm2.regs .X0 _ hx0)
    · intro xs s' h
      rw [hr0] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact ewsAt_nil _ _
    · intro xs s' h
      rw [hr0] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hd2]; exact hts
  rename_i hc
  have hn0 : n ≠ 0 := by
    intro h0
    apply hc
    sym_simp
    simp only [Env.ofMachine_regs, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    exact h0
  -- `b1`: the prologue, the output's cursor and end.
  have hwf1 : (frameEnv m0 st1.data 64 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst (by decide)) hsv1.2.2, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm1' : Match (frameEnv m0 st1.data 64 []) proS st1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [show st1.data.regs.SP = m0.regs.SP from hsv1.2.1]; exact frameBase_add.symm)
      trivial trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1
    (hpc1.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.TStateReadScalars.b0Offset + NativeRustcVmArm.Vm.TStateReadScalars.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.TStateReadScalars.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadScalars.b0_next])) hm1' fun st2 hm2 hpc2 => ?_
  obtain ⟨hpro, hws2, hx19, hx20, hx21⟩ := after_eq run_b1 ▸ ok_b1
  have hf2 : Frame m0 64 slots st2.data :=
    Frame.of_prologue_from hsv1 (fun p hp ↦ by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact hX30
      all_goals exact hsv1.1 _ rfl) hwf1 hm2 hpro slots_le
  have hs2 : SameOutside st1.data.dmem st2.data.dmem (NativeRustcVm.InRange fb 64) :=
    sameOutside_region hwf1 hm2 rfl hws2
  have hr0 : (st1.data.regs.getXReg .X0).toBitVec = t := by
    show st1.data.regs.X0.toBitVec = _; rw [hX0]
  have hr1 : (st1.data.regs.getXReg .X1).toBitVec = o := by
    show st1.data.regs.X1.toBitVec = _; rw [hX1]
  have hr2 : (st1.data.regs.getXReg .X2).toBitVec.toNat = n := by
    show st1.data.regs.X2.toBitVec.toNat = _; rw [hX2]; rfl
  have hX19 : st2.data.regs.X19.toBitVec = off o (16 * 0) := by
    show (st2.data.regs.getXReg .X19).toBitVec = _
    rw [hm2.regs .X19 _ hx19, Nat.mul_zero, off_zero]
    exact hr1
  have hX20 : st2.data.regs.X20.toBitVec = t := by
    show (st2.data.regs.getXReg .X20).toBitVec = _
    rw [hm2.regs .X20 _ hx20]
    exact hr0
  have hX21 : st2.data.regs.X21.toBitVec = off o (16 * n) := by
    show (st2.data.regs.getXReg .X21).toBitVec = _
    rw [hm2.regs .X21 _ hx21]
    simp only [endSym]
    sym_simp
    rw [Env.ofMachine_regs, Env.ofMachine_regs, hr1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, hr2,
      MemWidth.bits]
    omega
  have hsame2 : SameOutside m0.dmem st2.data.dmem (NativeRustcVm.InRange fb 64) := fun q hq ↦ by
    rw [hs2 q hq, hd1]
  have hInv : Inv m0 a s 0 st2.data := by
    refine ⟨hf2, hX20, hX21, hX19, ⟨#[], s, pushes_zero _ _, ewsAt_nil _ _, ?_⟩, fun q hq ↦ ?_⟩
    · exact hts.frame hf2.kept (fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
        fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩) hsame2
    · exact hsame2 q fun h ↦ hq (Or.inr (Or.inr (inRange_frame_stack hn (by decide) h)))
  refine loop (I := fun j st ↦ ∃ i, j = n - i ∧ i < n ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateReadScalars.b2Offset) ∧
      Inv m0 a s i st.data)
    (fun j st ⟨i, hj, hi, hpc, hI⟩ ↦ Eventually.mono (step hp hrs hpre hi hpc hI) fun st' h ↦ ?_)
    ⟨0, rfl, by omega, hpc2.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadScalars.b1_next]), hInv⟩
  rcases h with h | ⟨hpc', hlt, hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨n - (i + 1), by omega, i + 1, rfl, hlt, hpc', hI'⟩

end

end NativeRustcVmArm.Transcript.ReadScalars
