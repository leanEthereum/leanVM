module

public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Layout.PlacementsOf.Exec
public import NativeRustcVmArm.Layout.PlacementsOf.Model
public import NativeRustcVmArm.Layout.BuildLayout.Lemmas

/-!
# `placements_of`: the state, the frame's areas, reads, writes and calls in a body

The frame (`fb`, 5136 bytes): `block_cols` (`0`), `block_sizes` (`1264`), `block_offsets`
(`2528`), `offsets` (`3792`), the saved registers (`5056`, the top 80 bytes). A body (`Bd`)
changes only the placements and the stack.

- Reads: a log-size `kappas[c]` (`kap_word`), a byte of the read-only data (`rod_get`,
  `load_byte`).
- Writes: a block writing only in the frame below the slots, or in the placements
  (`Bd.of_write`).
- Calls: `memset` on a part of the frame below the slots (`memset_call`).
- The epilogue (`epi`).
-/

namespace NativeRustcVmArm.Layout.PlacementsOf

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PlacementsOf
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)
open NativeRustcVmArm.Layout.BuildLayout (Body.of_call_stack stackOk_body rodataAt_body
  natsOf_of_words wordsAt_natWords sp_toNat_sub not_top not_top_of_apart not_top_of_low kap_in)

public section

section
variable [Labels]

/-! ## The state -/

abbrev SS : Nat := placementsOfStack
/-- The log-sizes. -/
abbrev kk (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The placements. -/
abbrev pp (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 5136
/-- A body of `placements_of`. -/
abbrev Bd (m0 st : MachineData) : Prop := Body m0 5136 SS slots (pp m0) placementsBytes st
/-- Column `c`'s log-size. -/
abbrev κ (m0 : MachineData) (c : Nat) : Nat := (natsOf m0 m0.regs.X0 columnCountW).getD c 0

omit [Labels] in
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 5136 := by decide
omit [Labels] in
theorem slots_top : ∀ p ∈ slots, 5136 - 80 ≤ p.1 ∧ p.1 + 8 ≤ 5136 := by decide
omit [Labels] in
theorem SS_ge : 5136 + stackOffsetsStack ≤ SS := by decide

/-- The facts of the precondition the blocks use. -/
structure Facts (m0 : MachineData) : Prop where
  stack : StackOk m0 SS
  rod : RodataAt m0 SS
  kr : Readable m0 (kk m0) kappasBytes
  ko : OffStack m0 (kk m0) kappasBytes SS
  pr : Readable m0 (pp m0) placementsBytes
  po : OffStack m0 (pp m0) placementsBytes SS
  prod : RodataApart (pp m0) placementsBytes
  ap : Apart (kk m0) kappasBytes (pp m0) placementsBytes
  kle : ∀ x ∈ natsOf m0 m0.regs.X0 columnCountW, x ≤ 36

theorem Facts.of_pre {m0 : MachineData} (h : PlacementsOfPre m0) : Facts m0 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem Facts.sp {m0 : MachineData} (hF : Facts m0) : 5136 ≤ m0.regs.SP.toNat := by
  have := hF.stack.2.1
  have : 5136 ≤ SS := by decide
  omega

theorem Facts.κ_le {m0 : MachineData} (hF : Facts m0) {c : Nat} (hc : c < 158) : κ m0 c ≤ 36 := by
  have hs : (natsOf m0 m0.regs.X0 columnCountW).size = 158 := by simp [natsOf, columnCountW]
  have := hF.kle _ (Array.getElem_mem (xs := natsOf m0 m0.regs.X0 columnCountW) (i := c)
    (by rw [hs]; exact hc))
  simpa [Array.getD, hs, hc] using this

/-! ## The frame's areas -/

theorem fb_toNat {m0 : MachineData} (hF : Facts m0) : (fb m0).toNat = m0.regs.SP.toNat - 5136 :=
  sp_toNat_sub hF.sp

theorem fb_noWrap {m0 : MachineData} (hF : Facts m0) : NoWrap (fb m0) 5136 := by
  unfold NoWrap; rw [fb_toNat hF]; have := m0.regs.SP.toNat_lt; omega

theorem fb_add {m0 : MachineData} (hF : Facts m0) {o : Nat} (ho : o ≤ 5136) :
    (fb m0 + BitVec.ofNat 64 o).toNat = m0.regs.SP.toNat - 5136 + o := by
  have := m0.regs.SP.toNat_lt
  rw [Arrays.toNat_add_ofNat' (by rw [fb_toNat hF]; have := hF.sp; omega), fb_toNat hF]

/-- A part of the frame below the slots: in the stack, off its top 80 bytes. -/
theorem frame_low {m0 : MachineData} (hF : Facts m0) {o n : Nat} (hon : o + n ≤ 5056)
    {p : BitVec 64}
    (h : InRange (fb m0 + BitVec.ofNat 64 o) n p) :
    InRange (stackBelow m0 SS) SS p ∧ ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 80) 80 p := by
  have hnw := NativeRustcVm.NoWrap.sub (fb_noWrap hF) (o := o) (m := n) (by omega)
  have := NativeRustcVm.InRange.mono h hnw
    (NativeRustcVm.NoWrap.mono (fb_noWrap hF) (m := o + n) (by omega))
    (by rw [fb_add hF (by omega), fb_toNat hF]; omega)
    (by rw [fb_add hF (by omega), fb_toNat hF]; omega)
  exact kap_in hF.stack (F := 5136) (K := o + n) (G := 80) (by decide) (by omega) this

/-- A part of the frame below the slots is readable in a body. -/
theorem frame_readable {m0 st : MachineData} (hF : Facts m0) (hb : Bd m0 st) {o n : Nat}
    (hon : o + n ≤ 5136) : Readable st (fb m0 + BitVec.ofNat 64 o) n := by
  have hfr := Arrays.frame_ok hF.stack (F := 5136) (by decide)
  exact Layout.readable_sub ⟨hfr.1, hfr.2.1⟩ hb.kept hon

/-- Two parts of the frame apart. -/
theorem frame_apart {m0 : MachineData} (hF : Facts m0) {o n o' n' : Nat} (h : o + n ≤ 5136)
    (h' : o' + n' ≤ 5136) (hd : o + n ≤ o' ∨ o' + n' ≤ o) :
    Apart (fb m0 + BitVec.ofNat 64 o) n (fb m0 + BitVec.ofNat 64 o') n' :=
  NativeRustcVm.apart_of_le (fb_noWrap hF) h h' hd

/-- A part of the frame and a region off the stack apart. -/
theorem frame_apart_off {m0 : MachineData} (hF : Facts m0) {o n : Nat} (h : o + n ≤ 5136)
    {a : BitVec 64} {k : Nat} (ho : OffStack m0 a k SS) :
    Apart (fb m0 + BitVec.ofNat 64 o) n a k :=
  apart_frame_sub hF.stack (F := 5136) (by decide) ho h

/-! ## Reads -/

/-- The log-sizes are as at the entry. -/
theorem kap_same {m0 st : MachineData} (hF : Facts m0) (hb : Bd m0 st) {c : Nat} (hc : c < 158) :
    wordOf st.dmem (kk m0 + BitVec.ofNat 64 (8 * c)) =
      wordOf m0.dmem (kk m0 + BitVec.ofNat 64 (8 * c)) :=
  NativeRustcVm.wordOf_congr fun i hi ↦ by
    rw [addr_add_add]
    exact Arrays.same_of_apart hb.same hF.stack hF.kr.2 hF.ko hF.ap hF.pr.2 _
      (by unfold kappasBytes columnCountW; omega)

omit [Labels] in
theorem κ_eq (m0 : MachineData) {c : Nat} (hc : c < 158) :
    κ m0 c = (wordOf m0.dmem (kk m0 + BitVec.ofNat 64 (8 * c))).toNat :=
  Layout.natsOf_getD m0 m0.regs.X0 hc

omit [Labels] in
/-- An 8-byte load is the word there. -/
theorem load_word' (env : Env) (r o : Nat) :
    env.load r o 8 = (wordOf env.mem0 (env.base r + BitVec.ofNat 64 o)).toBitVec :=
  Arrays.load8_eq env r o

/-- A byte of the read-only data, in a body. -/
theorem rod_get {m0 st : MachineData} (hF : Facts m0) (hb : Bd m0 st) (t : NativeRustcVm.Data.Item)
    {i : Nat} (hi : i < t.bytes.length) :
    st.dmem.get? (rodataAddr t + BitVec.ofNat 64 i) = some t.bytes[i] := by
  have h := hF.rod.bytesAt t i hi
  rw [← h]
  refine hb.same _ fun hr ↦ ?_
  have hnw := hF.rod.noWrap t
  have hin : InRange (rodataAddr t) t.bytes.length (rodataAddr t + BitVec.ofNat 64 i) :=
    NativeRustcVm.inRange_add hi (by unfold NativeRustcVm.NoWrap at hnw; omega)
  rcases hr with hr | hr
  · exact (hF.prod t).symm.not_inRange hnw hF.pr.2 hin hr
  · exact (hF.rod.apart t).not_inRange hnw (Arrays.stack_noWrap hF.stack) hin hr

omit [Labels] in
/-- **A one-byte load** is the byte. -/
theorem load_byte {env : Env} {r : Nat} {b : UInt8}
    (h : env.mem0.get? (env.base r + BitVec.ofNat 64 0) = some b) :
    env.load r 0 1 = BitVec.ofNat 64 b.toNat := by
  rw [Env.load_of_bytesAt (bs := [b]) (n := 1) rfl (fun i hi ↦ by
    simp only [List.length_singleton] at hi
    obtain rfl : i = 0 := by omega
    simpa using h), ofBytes_natCast]
  simp [Nat.ofBytes]

/-! ## Writes -/

omit [Labels] in
/-- A write of a block, inside its region. -/
theorem written_in {env : Env} {S : SState} (hwf : env.WF) {p : BitVec 64} (h : Written env S p)
    (hS : ∀ w ∈ S.mem, ∀ b sz, env.regions[w.r]? = some (b, sz) → w.off + w.n ≤ sz) :
    ∃ w ∈ S.mem, ∃ b sz, env.regions[w.r]? = some (b, sz) ∧ InRange b sz p := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := h
  have := hS w hw b sz hb
  have hnw := hwf.noWrap _ _ _ hb
  exact ⟨w, hw, b, sz, hb, (inRange_iff hnw).mpr ⟨by omega, by omega⟩⟩

/-- **A block** writing only in the frame below the slots or in the placements keeps a body. -/
theorem Bd.of_write {m0 st st' : MachineData} (hF : Facts m0) (hb : Bd m0 st) {env : Env}
    {S₀ S₁ : SState} (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF)
    (hd : env.mem0 = st.dmem)
    (hk : keepsAll S₀ { S₁ with mem := [] } keptRegs = true)
    (hR : ∀ p, Written env S₁ p →
      (InRange (pp m0) placementsBytes p ∨ InRange (stackBelow m0 SS) SS p) ∧
      ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 80) 80 p) : Bd m0 st' := by
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk
  obtain ⟨⟨hr, hsp⟩, -⟩ := hk
  have hsame : NativeRustcVm.SameOutside st.dmem st'.dmem (Written env S₁) :=
    hd ▸ hm.sameOutside hwf
  have hsp' := hF.sp
  refine ⟨(Match.sp_eq hm₀ hm hsp) ▸ hb.sp, fun p hp i hi ↦ ?_, fun r hr' hn ↦ ?_, fun p hp ↦ ?_,
    fun p hp ↦ hm.kept hwf p (hd ▸ hb.kept p hp)⟩
  · rw [hsame _ fun h ↦ (hR _ h).2 ?_]
    · exact hb.frame p hp i hi
    · simp only [List.length_map, List.length_range] at hi
      have := slots_top p hp
      unfold InRange
      rw [show m0.regs.SP.toBitVec - BitVec.ofNat 64 5136 + BitVec.ofNat 64 p.1 +
          BitVec.ofNat 64 i -
          (m0.regs.SP.toBitVec - BitVec.ofNat 64 80) = BitVec.ofNat 64 (p.1 + i - 5056) by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
        have := m0.regs.SP.toNat_lt
        have : m0.regs.SP.toBitVec.toNat = m0.regs.SP.toNat := rfl
        omega, BitVec.toNat_ofNat]
      omega
  · obtain ⟨hs, he⟩ := hr r (List.mem_filter.mpr ⟨Arrays.mem_calleeRegs hr', by
      rw [Arrays.inSlots_false hn]; rfl⟩)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    rw [Match.reg_eq hm₀ hm hv (he.trans hv)]
    exact hb.regs r hr' hn
  · rw [hsame p fun h ↦ hp (hR p h).1]
    exact hb.same p hp
end

/-! ## Calls -/

variable [Host] {k : Nat}

theorem pc_of {pc : Int64} {a b : Nat} (h : pc = Host.addrOf a) (e : a = b) : pc = Host.addrOf b :=
  e ▸ h

/-- **`memset` on a part of the frame below the slots** keeps a body. -/
theorem memset_call (hms : Spec (Labels.label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost) {m0 : MachineData}
    (hF : Facts m0) {env : Env} {st : MachineState} {next : Int64}
    (hpc : PcOk env (.call NativeRustcVmArm.Vm.Memset.entryLabel) next st) (hb : Bd m0 st.data) {o n : Nat} (hon : o + n ≤ 5056)
    (h0 : st.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 o) (h2 : st.data.regs.X2.toNat = n)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next → Bd m0 st'.data →
      (∀ r, calleeSaved r = true → st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      (∀ p, ¬InRange (fb m0 + BitVec.ofNat 64 o) n p → st'.data.dmem.get? p = st.data.dmem.get? p) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hrd := frame_readable hF hb (o := o) (n := n) (by omega)
  refine call_then hpc hms ⟨by rw [h0, h2]; exact hrd.1, by rw [h0, h2]; exact hrd.2⟩
    fun st' hpc' hpost ↦ ?_
  obtain ⟨-, -, hsame, hsaved⟩ := hpost
  rw [h0, h2] at hsame
  refine cont st' hpc' (Body.of_call_stack (G := 80) hb hsame (fun p hp ↦ ?_) hsaved slots_top
    (by decide) hF.sp) hsaved.1 hsame
  obtain ⟨h1, h2⟩ := frame_low hF hon hp
  exact ⟨.inr h1, h2⟩

omit [Host] in
theorem init_reg (rs : List (Nat × Bool)) (sp₀ : Sym) (al : List (Sym × Nat × Int)) (r : XReg) :
    (init rs sp₀ [] [] [] al).reg r = some (.reg r) := by
  unfold SState.reg init
  rw [allXRegs_map_getElem?]
  rfl

/-- **A block without memory** from `regsS`. -/
theorem regs_step {b : List Directive} {kb : Nat} {S' : SState} {x : Exit}
    (hk : b.IsInfixAt Host.prog kb) (hx : exec b regsS = some (S', x))
    (hkeep : keepsAll regsS S' keptRegs = true) {m0 : MachineData} {st : MachineState}
    (hb : Bd m0 st.data) (hpc : st.pc = Host.addrOf kb) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, Match (Env.ofMachine st.data []) S' st'.data →
      PcOk (Env.ofMachine st.data []) x (Host.addrOf (kb + b.length)) st' → Bd m0 st'.data →
      st'.data.dmem = st.data.dmem →
      (∀ r, S'.reg r = some (.reg r) → st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  exec_at hk hx (Env.wf_nil _) hpc (match_nil _) fun st' hm hpc' ↦
    cont st' hm hpc' (hb.of_block (match_nil _) hm (Env.wf_nil _) rfl hkeep)
      (hm.dmem_eq (Env.wf_nil _) (by
        simp only [keepsAll, Bool.and_eq_true, List.isEmpty_iff] at hkeep; exact hkeep.2))
      fun r h ↦ Match.reg_eq (match_nil _) hm (init_reg [] .sp [] r) h

/-- **A one-byte load** of a read-only data item's byte `c`, from `byteS p i`. -/
theorem byte_step {b : List Directive} {kb : Nat} {p i : XReg} {S' : SState} {x : Exit}
    (hk : b.IsInfixAt Host.prog kb) (hx : exec b (byteS p i) = some (S', x))
    (hkeep : keepsAll (byteS p i) S' keptRegs = true) {m0 : MachineData} (hF : Facts m0)
    {st : MachineState} (hb : Bd m0 st.data) (hpc : st.pc = Host.addrOf kb)
    (t : NativeRustcVm.Data.Item) {c : Nat} (hc : c < t.bytes.length)
    (hp : (st.data.regs.getXReg p).toBitVec = rodataAddr t)
    (hi : (st.data.regs.getXReg i).toNat = c)
    (hidx : ∀ env : Env, (idxB p i).eval env = env.regs p + BitVec.ofNat 64 (env.regs i).toNat)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState,
      PcOk (Env.ofMachine st.data [(rodataAddr t + BitVec.ofNat 64 c, 1)]) x
        (Host.addrOf (kb + b.length)) st' → Bd m0 st'.data → st'.data.dmem = st.data.dmem →
      (∀ r, S'.reg r = some (.reg r) → st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      (Env.ofMachine st.data [(rodataAddr t + BitVec.ofNat 64 c, 1)]).load 0 0 1 =
        BitVec.ofNat 64 (t.bytes[c]).toNat →
      (∀ {r v}, S'.reg r = some v → v = .load 0 0 1 →
        (st'.data.regs.getXReg r).toBitVec = BitVec.ofNat 64 (t.bytes[c]).toNat) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hg := rod_get hF hb t hc
  have hnw : NoWrap (rodataAddr t + BitVec.ofNat 64 c) 1 :=
    NativeRustcVm.NoWrap.sub (hF.rod.noWrap t) (by omega)
  have hwf := Arrays.wf_one (m := st.data) (fun j hj ↦ by
    obtain rfl : j = 0 := by omega
    rw [addr_add_zero, hg]; rfl) hnw
  have hm : Match (Env.ofMachine st.data [(rodataAddr t + BitVec.ofNat 64 c, 1)]) (byteS p i)
      st.data := match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial ⟨by
        show (idxB p i).eval _ = _
        rw [hidx]
        simp only [Env.ofMachine_regs, Env.base_ofMachine_eq, List.getElem?_cons_zero,
          Option.map_some, Option.getD_some, Layout.ofInt_zero, BitVec.add_zero, hp]
        rw [show (st.data.regs.getXReg i).toBitVec.toNat = c from hi], trivial⟩
  have hl : (Env.ofMachine st.data [(rodataAddr t + BitVec.ofNat 64 c, 1)]).load 0 0 1 =
      BitVec.ofNat 64 (t.bytes[c]).toNat := load_byte (by
        simp only [Env.ofMachine_mem0, Env.base_ofMachine_eq, List.getElem?_cons_zero,
          Option.map_some, Option.getD_some, addr_add_zero]
        exact hg)
  refine exec_at hk hx hwf hpc hm fun st' hm' hpc' ↦ cont st' hpc'
    (hb.of_block hm hm' hwf rfl hkeep)
    (hm'.dmem_eq hwf (by
      simp only [keepsAll, Bool.and_eq_true, List.isEmpty_iff] at hkeep; exact hkeep.2))
    (fun r h ↦ Match.reg_eq hm hm' (init_reg _ _ _ r) h) hl fun {r v} h hv ↦ by
      subst hv
      rw [hm'.regs r _ h]
      exact hl

/-- **The epilogue** `b30`: X0 and X1 returned, the frame popped. -/
theorem epi (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b30Offset)) (hb : Bd m0 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ s.data.regs.X0 = st.data.regs.X0 ∧
      s.data.regs.X1 = st.data.regs.X1 ∧ Changes m0 s.data SS (pp m0) placementsBytes ∧
      Saved m0 s.data ∧ s.data.dmem = st.data.dmem) st := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hF.stack (by decide) (by decide)
  refine exec_at (infix_of b30_in_code (by simp [b30]) hp) run_b30 hwf hpc hm
    fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf
    (List.mem_map.mpr ⟨(5064, .X30), by simp [slots], rfl⟩)
    (Arrays.after_eq run_b30 ▸ b30_restores).1 (Arrays.after_eq run_b30 ▸ b30_restores).2
  refine ⟨?_, UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl),
    UInt64.toBitVec_inj.mp (hm'.regs .X1 _ rfl),
    fun q hq ↦ by rw [hdm]; exact hb.same q hq, hsaved, hdm⟩
  simp only [PcOk] at hpc'
  rw [hpc']
  simp only [retOf, hx30]

end

end NativeRustcVmArm.Layout.PlacementsOf
