module

public import NativeRustcVmX64.Layout.ReadAnnouncedSizes.Model
public import NativeRustcVmX64.Code.Vm.ReadAnnouncedSizes.Names

/-!
# `read_announced_sizes`: the body (x86-64)

The body (`Bod`, `Tables.Body.Bd` with `F = 208`): the frame, memory changed only in the outputs
(the layout at RDX, the `TState` at RDI, `outs`) and the stack. A callee entered at the frame's
offset `0` gets its stack (`ctx`, `at0`), the read-only data (`rodata_call`); the `TState` stays
across changes of the stack and the layout (`ts_keep`). The epilogue (`b15` from either label,
`fin`) returns RAX, R15 as RDX; the failures (`fail78`, `fail79`, `fail75`) return RAX = `0`.
After the scalars (`Mid`) the high limbs' checks keep the body (`check`).
-/

namespace NativeRustcVmX64.Layout.ReadAnnouncedSizes

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ReadAnnouncedSizes NativeVm.Model
open NativeRustcVm.Layout NativeRustcVm.Transcript NativeRustcVmX64.Transcript
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The stack. -/
abbrev NS : Nat := readAnnouncedSizesStack
/-- The `TState`. -/
abbrev tA (m : MachineData) : BitVec 64 := reg m .rdi
/-- The layout. -/
abbrev lA (m : MachineData) : BitVec 64 := reg m .rdx
/-- The frame's base. -/
abbrev fb (m : MachineData) : BitVec 64 := stackBelow m 208

/-- The outputs: the layout and the `TState`. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (lA m0) layoutBytes q ∨ NativeRustcVm.InRange (tA m0) tstateBytes q

/-- The body, RSP at the frame's offset `o`. -/
abbrev Bod (m0 : MachineData) (o : Nat) (d : MachineData) : Prop := Bd m0 208 NS slots (outs m0) o d

/-- The contract's postcondition, reached. -/
abbrev Goal [Labels] (bc : Array UInt64) (a : DecArea) (s : TState) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ ReadAnnouncedSizesPost bc a s m0 st.data

/-- **After the scalars**: the body, RAX `0`, the layout in RBX, the bytecode's length in R14,
the scalars in `announced` (the frame's bytes from `8`), the `TState` after them. -/
structure Mid (a : DecArea) (m0 : MachineData) (xs : Array EW) (s1 : TState)
    (d : MachineData) : Prop where
  bd : Bod m0 8 d
  rax : reg d .rax = 0
  rbx : reg d .rbx = lA m0
  r14 : reg d .r14 = reg m0 .rsi
  ann : NativeRustcVm.EWsAt d.dmem (off (fb m0) 8) xs.toList
  size : xs.size = 8
  ts : TStateAt d.dmem (tA m0) a s1

end

public section

theorem F_le : 208 ≤ NS := by show _ ≤ 208 + max _ _; omega
theorem le_rs : 208 + readScalarsStack ≤ NS := by show _ ≤ 208 + max _ _; omega
theorem le_bl : 208 + buildLayoutStack ≤ NS := by show _ ≤ 208 + max _ _; omega
theorem slots_ge : ∀ p ∈ slots, 184 ≤ p.1 ∧ p.1 + 8 ≤ 208 := by decide

/-- `test` of an `Option<()>`'s AL against zero. -/
theorem okWord_test (b : Bool) : decide ((okWord b).toNat = 0) = !b := by cases b <;> rfl

theorem pc_true {pc x y : Int64} {b : Bool} (h : pc = if b = true then x else y) (hb : b = true) :
    pc = x := by subst hb; simpa using h

theorem pc_false {pc x y : Int64} {b : Bool} (h : pc = if b = true then x else y)
    (hb : b = false) : pc = y := by subst hb; simpa using h

section
variable [Labels] {bc : Array UInt64} {a : DecArea} {s : TState} {m0 : MachineData}

theorem pre_parts (h : ReadAnnouncedSizesPre bc a s m0) :
    StackOk m0 NS ∧ RcAt m0 NS ∧ RodataAt m0 NS ∧ TStateAt m0.dmem (tA m0) a s ∧
      TStateOk m0 (tA m0) a NS ∧ RodataApart (tA m0) tstateBytes ∧ (reg m0 .rsi).toNat = bc.size ∧
      Readable m0 (lA m0) layoutBytes ∧ OffStack m0 (lA m0) layoutBytes NS ∧
      RodataApart (lA m0) layoutBytes ∧ Apart (lA m0) layoutBytes rcAddr 192 ∧
      Apart (lA m0) layoutBytes (tA m0) tstateBytes ∧
      Apart (lA m0) layoutBytes a.words (8 * a.len) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem ctx (h : ReadAnnouncedSizesPre bc a s m0) : Ctx m0 (tA m0) a NS 208 :=
  let p := pre_parts h
  ⟨p.1, p.2.1, p.2.2.2.2.1, p.2.2.2.1.footprint, F_le⟩

/-- The precise loader slots used by the transcript and layout callees. -/
theorem pre_got (h : ReadAnnouncedSizesPre bc a s m0) :
    GotAt m0 NS [(tA m0, tstateBytes), (a.words, 8 * a.len), (lA m0, layoutBytes), (rcAddr, 192)]
      ["memcpy", "memset"] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hg⟩ := h
  exact hg

/-- Body writes preserve both slots. -/
theorem got_bytes (h : ReadAnnouncedSizesPre bc a s m0) {d : MachineData} {o : Nat}
    (hb : Bod m0 o d) :
    ∀ l ∈ ["memcpy", "memset"], ∀ i < 8,
      d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) = m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  obtain ⟨hst, -, -, hts, -, -, -, hlr, -⟩ := pre_parts h
  exact got_keep (pre_got h) hst (writes := [(lA m0, layoutBytes), (tA m0, tstateBytes)])
    (by simp) (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hlr.2
      · exact hts.footprint.1.2)
    (hb.same.mono (by intro q hq; simpa [outs] using hq))

/-- The outputs are apart from the frame and the return address. -/
theorem outs_not_frame (h : ReadAnnouncedSizesPre bc a s m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬ NativeRustcVm.InRange (fb m0) (208 + 8) q := by
  obtain ⟨-, -, -, hts0, htok, -, -, hlr, hlo, -⟩ := pre_parts h
  have c := ctx h
  rcases hq with hq | hq
  · exact not_inRange_of_apart (apart_frame hlo c.spN F_le) hlr.2 c.noWrap_frame hq
  · exact not_inRange_of_apart (apart_frame htok.1 c.spN F_le) hts0.footprint.1.2 c.noWrap_frame
      hq

/-- A byte of the frame or the return address is not an output. -/
theorem outs_frame (h : ReadAnnouncedSizesPre bc a s m0) {j : Nat} (hj : j < 216) :
    ¬ outs m0 (off (fb m0) j) :=
  fun hq ↦ outs_not_frame h hq (frame_in (ctx h).stack F_le hj)

theorem outs_not_rc (h : ReadAnnouncedSizesPre bc a s m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬ NativeRustcVm.InRange rcAddr 192 q := by
  obtain ⟨-, -, -, -, -, -, -, hlr, -, -, hlrc, -⟩ := pre_parts h
  have c := ctx h
  rcases hq with hq | hq
  · exact not_inRange_of_apart hlrc hlr.2 c.rc.2.1 hq
  · exact c.not_rc_tstate hq

/-- **At a call** from the body. -/
theorem at0 (h : ReadAnnouncedSizesPre bc a s m0) {d : MachineData} (hb : Bod m0 0 d) :
    At m0 208 d :=
  ⟨by rw [hb.rsp_at (by omega)], hb.fr.kept, fun i hi ↦ hb.same _ fun hq ↦ by
    have hin : NativeRustcVm.InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i) :=
      inRange_off_self hi (by omega)
    rcases hq with hq | hq
    · exact outs_not_rc h hq hin
    · exact (ctx h).not_rc_stack hq hin⟩

/-- The callee's stack is in the function's. -/
theorem callee_stack (h : ReadAnnouncedSizesPre bc a s m0) {d : MachineData} (hb : Bod m0 0 d)
    {Nc : Nat} (hle : 208 + Nc ≤ NS) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow d Nc) Nc q) :
    NativeRustcVm.InRange (stackBelow m0 NS) NS q :=
  (hb.callee_in (ctx h).stack (Nat.zero_le _) (by simpa using hle) hq).1

/-- A byte of the frame or the return address is not in a callee's stack. -/
theorem not_callee (h : ReadAnnouncedSizesPre bc a s m0) {d : MachineData} (hb : Bod m0 0 d)
    {Nc : Nat} (hle : 208 + Nc ≤ NS) {j : Nat} (hj : j < 216) :
    ¬ NativeRustcVm.InRange (stackBelow d Nc) Nc (off (fb m0) j) := fun hq ↦
  (hb.callee_in (ctx h).stack (Nat.zero_le _) (by simpa using hle) hq).2
    (by rw [off_zero]; exact frame_in (ctx h).stack F_le hj)

/-- **The `TState` kept** where memory changed in the stack and the layout. -/
theorem ts_keep (h : ReadAnnouncedSizesPre bc a s m0) {d d' : MachineData} {s1 : TState}
    (hts : TStateAt d.dmem (tA m0) a s1) (hk : Kept d.dmem d'.dmem) {W : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem W)
    (hW : ∀ q, W q → NativeRustcVm.InRange (stackBelow m0 NS) NS q ∨
      NativeRustcVm.InRange (lA m0) layoutBytes q) :
    TStateAt d'.dmem (tA m0) a s1 := by
  obtain ⟨-, -, -, -, -, -, -, hlr, -, -, -, hlt, hla⟩ := pre_parts h
  have c := ctx h
  refine hts.frame hk (fun q hq ↦ ?_) hs
  rcases hW q hq with hq' | hq'
  · exact c.stack_not_t hq'
  · exact ⟨not_inRange_of_apart hlt hlr.2 c.fp.1.2 hq',
      not_inRange_of_apart hla hlr.2 c.fp.2.1.2 hq'⟩

/-- **The read-only data** for a callee entered at the frame's offset `0`. -/
theorem rodata_call (h : ReadAnnouncedSizesPre bc a s m0) {d : MachineData} (hb : Bod m0 0 d)
    {Nc : Nat} (hle : 208 + Nc ≤ NS) : RodataAt d Nc := by
  obtain ⟨-, -, hrod, hts0, -, htr, -, hlr, -, hlrod, -⟩ := pre_parts h
  have c := ctx h
  have hat := at0 h hb
  have hT : NativeRustcVm.RodataAt m0.dmem rodataAddr (stackBelow m0 NS) (NS + 8) := hrod
  intro t
  obtain ⟨hbt, hnw, hap⟩ := hT t
  refine ⟨fun i hi ↦ ?_, hnw, apart_callee hap hat.sp c.spN hle⟩
  rw [hb.same _ fun hq ↦ ?_]
  · exact hbt i hi
  rcases hq with (hq | hq) | hq
  · exact NativeRustcVm.Apart.not_inRange_add (NativeRustcVm.Apart.symm (hlrod t)) hnw hlr.2 hi hq
  · exact NativeRustcVm.Apart.not_inRange_add (NativeRustcVm.Apart.symm (htr t)) hnw
      hts0.footprint.1.2 hi hq
  · exact NativeRustcVm.Apart.not_inRange_add hap hnw c.noWrap_stack hi (inRange_mono hq (by omega))

/-- The frame's environment. -/
theorem wf0 (h : ReadAnnouncedSizesPre bc a s m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (ret : BitVec 64) : (frameEnv m0 d 208 [] (fun _ ↦ 0) ret).WF :=
  frame_wf' (ctx h).stack F_le hk (by simp) (List.pairwise_singleton _ _)

omit [Labels] in
theorem ld0 {d : MachineData} {ret : BitVec 64} {rest : List (BitVec 64 × Nat)} {o : Nat}
    {w : UInt64} (hw : NativeRustcVm.WordAt d.dmem (off (fb m0) o) w) :
    (frameEnv m0 d 208 rest (fun _ ↦ 0) ret).load 0 o 8 = w.toBitVec :=
  load_ofMachine rfl hw

/-- A body block's start. -/
theorem match_mid {d : MachineData} (hb : Bod m0 8 d) (ret : BitVec 64) :
    Match (frameEnv m0 d 208 [] (fun _ ↦ 0) ret) frS d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial trivial

/-- A body block writing nothing. -/
theorem step0 (h : ReadAnnouncedSizesPre bc a s m0) {d d' : MachineData} {o o' : Nat}
    (hb : Bod m0 o d) {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {Sy : SState}
    (hwf : (frameEnv m0 d 208 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 208 rest (fun _ ↦ 0) ret) Sy d')
    (hmid : MidOk 208 o' slots Sy = true) (hmem : Sy.mem = []) :
    Bod m0 o' d' ∧ d'.dmem = d.dmem :=
  ⟨hb.step (ctx h).stack F_le hwf hm hmid slots_le (outs := []) (by rw [WrOk, hmem]; rfl) nofun,
    hm.dmem_eq hwf hmem⟩

omit [Labels] in
/-- Limb words of scalar `i`. -/
theorem Mid.word {s1 : TState} {xs : Array EW} {d : MachineData} (hM : Mid a m0 xs s1 d) {i : Nat}
    (hi : i < 8) :
    NativeRustcVm.WordAt d.dmem (off (fb m0) (16 * i + 8))
        (xs[i]'(by rw [hM.size]; exact hi)).c0 ∧
      NativeRustcVm.WordAt d.dmem (off (fb m0) (16 * i + 16))
        (xs[i]'(by rw [hM.size]; exact hi)).c1 := by
  have := NativeRustcVm.ewsAt_getElem hM.ann (i := i)
    (by simp only [Array.length_toList, hM.size]; exact hi)
  rw [NativeRustcVm.ewAt_iff] at this
  simp only [Array.getElem_toList] at this
  rw [off_add, off_add] at this
  exact ⟨by rw [show 16 * i + 8 = 8 + 16 * i by omega]; exact this.1,
    by rw [show 16 * i + 16 = 8 + 16 * i + 8 by omega]; exact this.2⟩

end

variable [Host] {k : Nat} {bc : Array UInt64} {a : DecArea} {s : TState} {m0 : MachineData}

theorem lbl_entry (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.ReadAnnouncedSizes.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b0Offset) := hp.label NativeRustcVmX64.Vm.ReadAnnouncedSizes.entry_at
theorem lbl_13 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_13 = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b14Offset) := hp.label NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_13_at
theorem lbl_21 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_21 = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b15Offset) := hp.label NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_21_at
theorem lbl_22 (hp : Placed code k) :
    Labels.label NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_22 = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_22Offset) := hp.label NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_22_at

theorem addr_eq {i j : Nat} (h : i = j) : Host.addrOf i = Host.addrOf j := by rw [h]

/-- **The epilogue** (`b15` from either label): RAX, R15 as RDX, the body's memory. -/
theorem fin {ds : List Directive} {kk : Nat} (hk : ds.IsInfixAt Host.prog kk)
    (hx : exec ds frS = some (after ds frS, .ret (.load 0 208 8)))
    (hE : EpiOk 208 slots (after ds frS) = true) (hmem : (after ds frS).mem = [])
    (hax : (after ds frS).reg .rax = some (.reg .rax))
    (hdx : (after ds frS).reg .rdx = some (.reg .r15))
    (h : ReadAnnouncedSizesPre bc a s m0) {st : MachineState} (hb : Bod m0 8 st.data)
    (hpc : st.pc = Host.addrOf kk)
    (hrax : reg st.data .rax = (okWord ((readAnnouncedSizes bc).run s).isSome).toBitVec)
    (hsome : ∀ L rate s', (readAnnouncedSizes bc).run s = some ((L, rate), s') →
      (reg st.data .r15).toNat = rate ∧ LayoutWAt st.data.dmem (lA m0) L ∧
        TStateAt st.data.dmem (tA m0) a s') :
    Eventually (step1 Host.exe) (Goal bc a s m0) st := by
  have c := ctx h
  refine Bd.done' hb c.stack F_le hk hx hpc (match_mid hb 0) hE hmem
    fun st' hm' hpc' hrsp' hsv' hd' ↦ ?_
  have e0 : reg st'.data .rax = reg st.data .rax := hm'.regs .rax _ hax
  have e2 : reg st'.data .rdx = reg st.data .r15 := hm'.regs .rdx _ hdx
  refine ⟨hpc', hrsp', by rw [e0]; exact hrax, fun L rate s' hr ↦ ?_, fun q hq ↦ ?_, hsv'⟩
  · obtain ⟨h1, h2, h3⟩ := hsome L rate s' hr
    exact ⟨by rw [e2]; exact h1, by rw [hd']; exact h2, by rw [hd']; exact h3⟩
  · rw [hd']
    exact hb.same q fun h' ↦ hq (Or.elim h' (fun h'' ↦ Or.elim h'' Or.inl fun x ↦ .inr (.inl x))
      fun x ↦ .inr (.inr x))

/-- `b15` from `NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_21` with RAX = `0`. -/
theorem fail78 (hp : Placed code k) (h : ReadAnnouncedSizesPre bc a s m0) {st : MachineState}
    (hb : Bod m0 8 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b15Offset)) (hrax : reg st.data .rax = 0)
    (hr : (readAnnouncedSizes bc).run s = none) :
    Eventually (step1 Host.exe) (Goal bc a s m0) st :=
  fin (infix_of b15_in_code (by simp [b15]) hp) exit_b15 ok_b15.1 ok_b15.2.1 ok_b15.2.2.1
    ok_b15.2.2.2 h hb hpc (by rw [hrax, hr]; rfl) fun _ _ _ h' ↦ by rw [hr] at h'; cases h'

/-- `b15` from `NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_22` with RAX = `0`. -/
theorem fail79 (hp : Placed code k) (h : ReadAnnouncedSizesPre bc a s m0) {st : MachineState}
    (hb : Bod m0 8 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_22Offset)) (hrax : reg st.data .rax = 0)
    (hr : (readAnnouncedSizes bc).run s = none) :
    Eventually (step1 Host.exe) (Goal bc a s m0) st :=
  fin (infix_of ((infix_drop b15 1).trans b15_in_code (by simp [b15])) (by simp [b15]) hp)
    exit_b15d ok_b15d.1 ok_b15d.2.1 ok_b15d.2.2.1 ok_b15d.2.2.2 h hb hpc (by rw [hrax, hr]; rfl)
    fun _ _ _ h' ↦ by rw [hr] at h'; cases h'

/-- `b14` (`NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_13`): RAX = `0`, then `b15`. -/
theorem fail75 (hp : Placed code k) (h : ReadAnnouncedSizesPre bc a s m0) {st : MachineState}
    (hb : Bod m0 8 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b14Offset))
    (hr : (readAnnouncedSizes bc).run s = none) :
    Eventually (step1 Host.exe) (Goal bc a s m0) st := by
  have hwf := wf0 h hb.fr.kept 0
  refine exec_at (infix_of b14_in_code (by simp [b14]) hp) exit_b14 hwf nofun hpc (match_mid hb 0)
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hmid, hmem, hax⟩ := ok_b14
  have hb' := (step0 h hb hwf hm' hmid hmem).1
  simp only [PcOk] at hpc'
  exact fail79 hp h hb' (hpc'.trans (lbl_22 hp)) (hm'.regs .rax _ hax) hr

/-- **A high limb's check** (`cmpq $0, o(%rsp)`, `jne l`). -/
theorem check (h : ReadAnnouncedSizesPre bc a s m0) {ds : List Directive} {kk o : Nat} {l : Label}
    {S1 : SState} (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds frS = some (S1, .cond (cnz o) l))
    (hok : OkC S1) {xs : Array EW} {s1 : TState} {st : MachineState}
    (hpc : st.pc = Host.addrOf kk) (hM : Mid a m0 xs s1 st.data) {v : UInt64}
    (hw : NativeRustcVm.WordAt st.data.dmem (off (fb m0) o) v) {R : MachineState → Prop}
    (hne : ∀ st', st'.pc = Labels.label l → Mid a m0 xs s1 st'.data → v ≠ 0 →
      Eventually (step1 Host.exe) R st')
    (heq : ∀ st', st'.pc = Host.addrOf (kk + ds.length) → Mid a m0 xs s1 st'.data → v = 0 →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := wf0 h hM.bd.fr.kept 0
  refine exec_at hk hx hwf nofun hpc (match_mid hM.bd 0) fun st' hm' hpc' ↦ ?_
  obtain ⟨hmid, hmem, hkp⟩ := hok
  obtain ⟨hb', hd⟩ := step0 h hM.bd hwf hm' hmid hmem
  have hM' : Mid a m0 xs s1 st'.data :=
    ⟨hb', (keeps_reg hm' hkp (by simp)).trans hM.rax, (keeps_reg hm' hkp (by simp)).trans hM.rbx,
      (keeps_reg hm' hkp (by simp)).trans hM.r14, hd ▸ hM.ann, hM.size, hd ▸ hM.ts⟩
  simp only [PcOk] at hpc'
  rw [cnz_eval _ (ld0 hw)] at hpc'
  by_cases hv : v = 0
  · exact heq st' (by rw [hpc']; simp [hv]) hM' hv
  · exact hne st' (by rw [hpc']; simp [hv]) hM' hv

end

end NativeRustcVmX64.Layout.ReadAnnouncedSizes
