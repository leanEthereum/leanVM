module

public import NativeRustcVmArm.Code.Vm.PlacementsOf.Names
public import NativeRustcVmArm.Layout.BuildLayout.Kappas

/-!
# `build_layout`: `placements_of`, the stack's log-size, the return (`b16` to `b18`)

`b16` calls `placements_of` on the frame's `kappas` and the layout's placements; `b17` tests its
result (always `Some`); `b18` stores the stack's log-size and the epilogue returns `1`
(`finish`). The words stored then make the layout the model's (`layoutWAt_of`).
-/

namespace NativeRustcVmArm.Layout.BuildLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BuildLayout
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)
open NativeRustcVm.Transcript (off)

public section

/-! ## The layout from its words -/

theorem Ws.tail {d : Mem 64} {b : BitVec 64} {x : Nat × UInt64} {ws : List (Nat × UInt64)}
    (h : Ws d b (x :: ws)) : Ws d b ws := fun p hp ↦ h p (List.mem_cons_of_mem _ hp)

theorem PlacementWAt.of_same {d d' : Mem 64} {a : BitVec 64} {p : Option Placement}
    (h : PlacementWAt d a p) (hs : Same d d' a 24) : PlacementWAt d' a p := by
  cases p with
  | none => exact WordAt.of_same (n := 24) h hs (by decide)
  | some q =>
    obtain ⟨h0, h1, h2, h3, h4⟩ := h
    exact ⟨WordAt.of_same h0 hs (by decide), h1, h2,
      WordAt.of_same h3 (hs.sub (o := 8) (k := 8) (by decide)) (Nat.le_refl _),
      WordAt.of_same h4 (hs.sub (o := 16) (k := 8) (by decide)) (Nat.le_refl _)⟩

theorem getElem_getD {xs : Array Nat} {t : Nat} (h : t < xs.size) : xs[t] = xs.getD t 0 := by
  simp [Array.getD, h]

/-- **The layout** from the words `build_layout` stored. -/
theorem layoutWAt_of {d : Mem 64} {a : BitVec 64} {bc : Array UInt64} {lm lb : Nat}
    {rows : Array Nat} (hrs : rows.size = 6) (hlm : lm ≤ 30) (hlb : lb ≤ 30)
    (hr : ∀ t < 6, rows.getD t 0 ≤ 2 ^ 30)
    (hW : Ws d a ((16, (layoutF bc lm lb rows).stackLog.toUInt64) :: wsK lm lb rows))
    (hsl : (layoutF bc lm lb rows).stackLog < 2 ^ 64)
    (hpl : ∀ c (h : c < (layoutF bc lm lb rows).placements.size),
      PlacementWAt d (off a (120 + placementBytes * c)) (layoutF bc lm lb rows).placements[c]) :
    LayoutWAt d a (layoutF bc lm lb rows) := by
  obtain ⟨f1, f2, -, f4, f5, f6, -, -⟩ := layoutF_facts bc lm lb rows
  have hK := hW.tail
  refine ⟨f1 ▸ hlm, ?_, f2 ▸ hlb, ?_, hsl, ?_, by rw [f4]; exact heightsF_size hrs, ?_, ?_, ?_,
    by rw [f6]; rfl, hpl⟩
  · rw [f1, ← addr_add_zero a]; exact hK.get (by simp)
  · rw [f2]; exact hK.get (by simp)
  · exact hW.get (by simp)
  · rw [f4]
    intro h hh
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hh
    have hi' : i < 6 := by rw [heightsF_size hrs] at hi; exact hi
    rw [getElem_getD hi]
    exact heights_le hrs hr hi'
  · rw [f4]
    exact heights_words hrs hK
  · refine ⟨rows, hrs, fun x hx ↦ ?_, ?_, by rw [f4]; exact f5⟩
    · obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
      rw [getElem_getD hi]
      exact hr i (by omega)
    · refine wordsAt_natWords fun t ht ↦ ?_
      rw [addr_add_add, getElem_getD ht]
      rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hK.get (by simp)

/-! ## The end -/

variable [Host] {k : Nat}

omit [Host] in
theorem pS_le : 1360 + placementsOfStack ≤ SS := by decide

omit [Host] in
/-- The callee's stack below the frame is off the stack's top `96` bytes. -/
theorem callee_not_top {m0 st : MachineData} {n' : Nat} (hsp1 : 1360 ≤ m0.regs.SP.toNat)
    (hn : 1360 + n' ≤ m0.regs.SP.toNat)
    (hsp : st.regs.SP.toBitVec = m0.regs.SP.toBitVec - BitVec.ofNat 64 1360) {p : BitVec 64}
    (h : InRange (stackBelow st n') n' p) :
    ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 96) 96 p := by
  have e1 := sp_toNat_sub (m0 := m0) hsp1
  have e2 : (stackBelow st n').toNat = m0.regs.SP.toNat - 1360 - n' := by
    unfold stackBelow
    rw [hsp, Arrays.toNat_sub_ofNat (by rw [e1]; omega), e1]
  have hnw : NoWrap (stackBelow st n') n' := by
    unfold NoWrap; rw [e2]; have := m0.regs.SP.toNat_lt; omega
  exact not_top_of_low (by omega) hnw (by rw [e2]; omega) h

omit [Host] in
theorem cols_lt {lm lb : Nat} {rows : Array Nat} (hrs : rows.size = 6) (hlm : lm ≤ 30)
    (hlb : lb ≤ 30) (hr : ∀ t < 6, rows.getD t 0 ≤ 2 ^ 30) :
    ∀ x ∈ columnKappas lm lb (heightsF rows), x ≤ 36 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
  have hi' : i < 158 := by rw [columnKappas_size'] at hi; exact hi
  rw [getElem_getD hi, columnKappas_getD _ _ _ hi']
  exact kapF_le hlm hlb (fun t ht ↦ heights_le hrs hr ht) i

/-- **`placements_of`, the stack's log-size, the return.** -/
theorem finish (hp : Placed code k)
    (hpl : Spec (Labels.label NativeRustcVmArm.Vm.PlacementsOf.entryLabel) PlacementsOfPre PlacementsOfPost)
    {bc : Array UInt64} {m0 : MachineData} (hF : Facts bc m0) {lm lb : Nat} {rows : Array Nat}
    (hrs : rows.size = 6) (hlm : lm ≤ 30) (hlb : lb ≤ 30) (hr : ∀ t < 6, rows.getD t 0 ≤ 2 ^ 30)
    (hres : buildLayout bc m0.regs.X1.toNat (rowsOf m0) = some (layoutF bc lm lb rows))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BuildLayout.b16Offset)) (hbd : Bd m0 st.data)
    (h22 : st.data.regs.getXReg .X22 = m0.regs.X3)
    (h21 : (st.data.regs.getXReg .X21).toBitVec = ll m0 + BitVec.ofInt 64 24)
    (hW : Ws st.data.dmem (ll m0) (wsK lm lb rows))
    (hK : WordsAt st.data.dmem (fb m0) (natWords (columnKappas lm lb (heightsF rows)))) :
    Eventually (step1 Host.exe) (Post bc m0) st := by
  have hS := hF.stack
  have hsp := hF.sp
  have hle := pS_le
  -- `b16`
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) run_b16 (Env.wf_nil _) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hb1 := hbd.of_block (match_nil _) hm1 (Env.wf_nil _) rfl (Arrays.after_eq run_b16 ▸ b16_keeps).1
  have hk1 := Arrays.regs_eq_of (match_nil _) hm1 _ (Arrays.after_eq run_b16 ▸ b16_keeps).2
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) rfl
  have hx0 : st1.data.regs.X0.toBitVec = fb m0 := (hm1.regs .X0 _ rfl).trans hbd.sp
  have hx1 : st1.data.regs.X1.toBitVec = ll m0 + BitVec.ofNat 64 120 := by
    have := hm1.regs .X1 _ rfl
    sym_simp at this
    show (st1.data.regs.getXReg .X1).toBitVec = _
    rw [this, Env.ofMachine_regs, h21, show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl,
      addr_add_add]
  have hn : natsOf st1.data st1.data.regs.X0 columnCountW = columnKappas lm lb (heightsF rows) :=
    natsOf_of_words (by rw [hx0, hd1]; exact hK)
      (fun x hx ↦ by have := cols_lt hrs hlm hlb hr x hx; omega) (columnKappas_size' _ _ _)
  have hfr := Arrays.frame_ok hS (F := 1360) (by decide)
  have hlay := hF.lay_apart (o := 120) (n := 3792) (by decide) (by decide)
  have e120 := hF.lay_toNat (o := 120) (by decide)
  have hpre : PlacementsOfPre st1.data := by
    refine ⟨stackOk_body hS hb1 (by decide) hle, rodataAt_body hS hF.rod hb1 hF.lrod hF.lr.2 hle,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx0]; exact Layout.readable_prefix ⟨hfr.1, hfr.2.1⟩ hb1.kept (by decide)
    · rw [hx0]
      have := frame_apart_callee hS hb1.sp hle (o := 0) (k := kappasBytes) (by decide)
      rwa [addr_add_zero] at this
    · rw [hx1]; exact Layout.readable_sub hF.lr hb1.kept (by decide)
    · rw [hx1]; exact apart_callee hS hb1.sp hle hlay
    · rw [hx1]
      intro t
      have := hF.lrod t
      unfold NativeRustcVm.Apart at this ⊢
      rw [e120]
      unfold layoutBytes placementBytes columnCountW at this
      unfold placementsBytes placementBytes columnCountW
      omega
    · rw [hx0, hx1]
      have := apart_frame_sub hS (F := 1360) (by decide) hlay (o := 0) (k := kappasBytes) (by decide)
      rwa [addr_add_zero] at this
    · rw [hn]; exact cols_lt hrs hlm hlb hr
  refine call_then hpc1 hpl hpre fun st2 hpc2 hpost ↦ ?_
  obtain ⟨h0, h1, hsz, hpw, hch, hs2⟩ := hpost
  rw [hn] at h1 hsz hpw
  rw [hx1] at hch hpw
  have hR : ∀ p, (InRange (ll m0 + BitVec.ofNat 64 120) placementsBytes p ∨
      InRange (stackBelow st1.data placementsOfStack) placementsOfStack p) →
      (InRange (ll m0) layoutBytes p ∨ InRange (stackBelow m0 SS) SS p) ∧
        ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 96) 96 p := by
    intro p hp
    rcases hp with hp | hp
    · have hin := NativeRustcVm.InRange.of_sub hp hF.lr.2 (by decide)
      exact ⟨.inl hin, not_top_of_apart hS (by decide) hF.lo hF.lr.2 hin⟩
    · exact ⟨.inr (callee_stack hS hb1.sp hle hp), callee_not_top hsp (by have := hS.2.1; omega)
        hb1.sp hp⟩
  have hb2 : Bd m0 st2.data := Body.of_call_stack (G := 96) hb1 hch (fun p hp ↦ hR p hp) hs2
    slots_top (by decide) hsp
  have hW2 : Ws st2.data.dmem (ll m0) (wsK lm lb rows) := by
    refine Ws.of_same (hd1 ▸ hW) fun p hp j hj ↦ hch _ fun h ↦ ?_
    have hle' : p.1 + 8 ≤ 120 := (show ∀ q ∈ wsK lm lb rows, q.1 + 8 ≤ 120 by simp) p hp
    rcases h with h | h
    · have e := hF.lay_toNat (o := p.1 + j) (by unfold layoutBytes placementBytes columnCountW; omega)
      rw [inRange_iff (NativeRustcVm.NoWrap.sub hF.lr.2 (by decide)), e, e120] at h
      omega
    · exact hF.lay_off (o := p.1 + j) (by unfold layoutBytes placementBytes columnCountW; omega)
        (callee_stack hS hb1.sp hle h)
  -- `b17`
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) run_b17 (Env.wf_nil _) (pc_of hpc2 rfl)
    (match_nil _) fun st3 hm3 hpc3 ↦ ?_
  have hb3 := hb2.of_block (match_nil _) hm3 (Env.wf_nil _) rfl (Arrays.after_eq run_b17 ▸ b17_keeps).1
  have hk3 := Arrays.regs_eq_of (match_nil _) hm3 _ (Arrays.after_eq run_b17 ▸ b17_keeps).2
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (Env.wf_nil _) rfl
  have k30 : st3.data.regs.X0 = st2.data.regs.X0 := Match.reg_eq (match_nil _) hm3 (r := .X0) rfl rfl
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  have e0 : (Env.ofMachine st2.data []).regs .X0 = 1#64 := congrArg UInt64.toBitVec h0
  rw [e0] at hpc3
  have hpc4 := pc_of ((Arrays.pc_cond hpc3).2 (by decide)) (show k + NativeRustcVmArm.Vm.BuildLayout.b17Offset + b17.length = k + NativeRustcVmArm.Vm.BuildLayout.b18Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b17_next])
  -- `b18`
  have h22' : st3.data.regs.getXReg .X22 = m0.regs.X3 := by
    rw [hk3 .X22 (by simp [cs]), hs2.1 .X22 rfl, hk1 .X22 (by simp [cs])]; exact h22
  have h21' : (st3.data.regs.getXReg .X21).toBitVec = ll m0 + BitVec.ofInt 64 24 := by
    rw [hk3 .X21 (by simp), hs2.1 .X21 rfl, hk1 .X21 (by simp)]; exact h21
  obtain ⟨k18, i18, w18, m18⟩ := Arrays.after_eq run_b18 ▸ b18_facts
  have hwf := hF.wf_lay hb3
  have hm := lay_match h22' h21'
  refine exec_at (infix_of b18_in_code (by simp [b18]) hp) run_b18 hwf hpc4 hm fun st4 hm4 hpc5 ↦ ?_
  simp only [InR0, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at i18
  have hb4 : Bd m0 st4.data := Layout.Body.of_write' hb3 hS hm hm4 hwf
    (fun p hp ↦ NativeRustcVm.InRange.mono hp (NativeRustcVm.NoWrap.mono hF.lr.2 (by decide)) hF.lr.2
      (Nat.le_refl _) (by unfold layoutBytes placementBytes columnCountW; omega))
    k18 i18 (by have := hF.lay_apart (o := 0) (n := 120) (by decide) (by decide); rwa [addr_add_zero] at this)
    slots_le (by decide)
  have hsl : st2.data.regs.getXReg .X1 = (layoutF bc lm lb rows).stackLog.toUInt64 := by
    rw [(layoutF_placements bc lm lb rows).2]; exact u64_eq h1
  have hW4 : Ws st4.data.dmem (ll m0) ((16, (layoutF bc lm lb rows).stackLog.toUInt64) ::
      wsK lm lb rows) := by
    refine Ws.cons ?_ (Ws.keep hm4 hwf (by simp) (hd3 ▸ hW2) (by exact m18))
    have := Arrays.wordAt_of_write hm4 (by omega) w18
    rwa [hk3 .X1 (by simp), hsl] at this
  have hsame4 := Layout.same_of_region hm4 hwf (r := 0) (b := ll m0) (sz := 120) rfl i18
  have k40 : st4.data.regs.X0 = st3.data.regs.X0 := Match.reg_eq hm hm4 (r := .X0) rfl rfl
  simp only [PcOk] at hpc5
  -- the epilogue
  refine Eventually.mono (epi hp hF (hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.BuildLayout.b21Offset) NativeRustcVmArm.Vm.BuildLayout.label_12_at)) hb4
    (.inr (k40.trans (k30.trans h0)))) fun s ⟨hs1, hsx, hsc, hss, hsd⟩ ↦ ⟨hs1, ?_, ?_, hsc, hss⟩
  · rw [hsx, k40, k30, h0, hres]; rfl
  · intro L hL
    rw [hres] at hL
    cases hL
    rw [hsd]
    refine layoutWAt_of hrs hlm hlb hr hW4 (by rw [(layoutF_placements bc lm lb rows).2, ← h1]; exact UInt64.toNat_lt _)
      fun c hc ↦ ?_
    have hc' : c < 158 := by have := hsz; obtain ⟨-, -, -, -, -, f6, -, -⟩ := layoutF_facts bc lm lb rows
                             rw [f6] at hc; exact hc
    have := hpw c (by rw [hsz]; exact hc')
    simp only [off] at this ⊢
    rw [addr_add_add] at this
    refine PlacementWAt.of_same (hd3 ▸ this) fun j hj ↦ ?_
    rw [addr_add_add]
    refine hsame4 _ fun h ↦ ?_
    have e := hF.lay_toNat (o := 120 + placementBytes * c + j)
      (by unfold layoutBytes placementBytes columnCountW; omega)
    rw [inRange_iff (NativeRustcVm.NoWrap.mono hF.lr.2 (by decide)), e] at h
    omega

end

end NativeRustcVmArm.Layout.BuildLayout
