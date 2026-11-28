module

public import NativeRustcVmArm.Code.Vm.FoldRound.Names
public import NativeRustcVmArm.Code.Vm.FoldRounds.Names
public import NativeRustcVmArm.Whir.FoldRounds.Basic
public import NativeRustcVmArm.Whir.FoldRounds.Exec
public import NativeRustcVmArm.Whir.State

/-!
# A round of `fold_rounds`

`Inv i`: after `i` rounds, the frame, the registers (`t` in X20, `s` in X19, the buffer in X21,
`n` in X22, `fold_round`'s output in X23), `foldRounds i`'s state, rounds and transcript in
memory, memory changed only in the outputs and the stack. `round`: from `fold_round`'s call, its
tag tested (`T`), its `α`, `β` stored (`S`, `StoreOk`): `Inv (i + 1)` at the store's exit, or the
rejection (`b23`). `done`, `done7`: the returns with `1`.
-/

namespace NativeRustcVmArm.Whir.FoldRounds

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FoldRounds NativeRustcVmArm.Transcript
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm NativeRustcVm.Whir NativeRustcVmArm.Whir

@[expose] public section

/-- `fold_rounds`' outputs: the rounds' buffer, the state, the `TState`. -/
def outs (m0 : MachineData) : List NativeRustcVm.Region :=
  [⟨m0.regs.X3.toBitVec, 8 + roundBytes * roundCap⟩, ⟨m0.regs.X2.toBitVec, stateBytes⟩,
    ⟨m0.regs.X0.toBitVec, tstateBytes⟩]

/-- **After `i` rounds.** -/
structure Inv (m0 : MachineData) (a : DecArea) (s : TState) (w : WhirStateW) (i : Nat)
    (d : MachineData) : Prop where
  frame : Frame m0 160 slots d
  x19 : d.regs.X19.toBitVec = m0.regs.X2.toBitVec
  x20 : d.regs.X20.toBitVec = m0.regs.X0.toBitVec
  x21 : d.regs.X21.toBitVec = m0.regs.X3.toBitVec
  x22 : d.regs.X22 = m0.regs.X1
  x23 : d.regs.X23.toBitVec = off (frameBase m0 160) 40
  run : ∃ w' rs s', (foldRounds i w).run s = some ((w', rs), s') ∧ rs.size = i ∧
    w'.alphas.size = w.alphas.size + i ∧ WhirStateAt d.dmem m0.regs.X2.toBitVec w' ∧
    BufRoundsAt d.dmem m0.regs.X3.toBitVec rs.toList ∧ TStateAt d.dmem m0.regs.X0.toBitVec a s'
  same : ChangesIn m0 d foldRoundsStack (outs m0)

/-- What the proof of `fold_rounds` ends in. -/
abbrev Goal (a : DecArea) (s : TState) (w : WhirStateW) (m0 : MachineData) (st : MachineState) :
    Prop :=
  st.pc = retOf m0 ∧ FoldRoundsPost a s w m0 st.data

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 160 := by decide

theorem stack_eq : foldRoundsStack = 960 := rfl

theorem length_roundEWs (rs : List FoldRoundW) : (roundEWs rs).length = 2 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [roundEWs, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢; omega

theorem bufRoundsAt_agree {d d' : Mem 64} {r : BitVec 64} {rs : List FoldRoundW}
    (h : BufRoundsAt d r rs) (hA : Agree d d' r 200 (fun _ ↦ False)) : BufRoundsAt d' r rs := by
  obtain ⟨hl, hw, he⟩ := h
  have h0 := agree_sub hA (o := 0) (k := 8) (by omega) fun _ _ ↦ id
  rw [off_zero] at h0
  refine ⟨hl, wordAt_of_agree h0 le_rfl hw,
    bytesAt_of_agree (agree_sub hA (o := 8) (k := 192) (by omega) fun _ _ ↦ id) ?_ he⟩
  rw [NativeRustcVm.length_ewsBytes, length_roundEWs]
  unfold roundCap at hl
  omega

/-- **A round pushed** on the buffer. -/
theorem bufRoundsAt_push {d d' : Mem 64} {r : BitVec 64} {rs : List FoldRoundW}
    (h : BufRoundsAt d r rs) (hlt : rs.length < roundCap)
    (hA : Agree d d' r 200 (fun j ↦ j < 8 ∨ (8 + 32 * rs.length ≤ j ∧ j < 40 + 32 * rs.length)))
    (hn : NativeRustcVm.WordAt d' r (rs.length + 1).toUInt64) {ρ : FoldRoundW}
    (hx : NativeRustcVm.EWsAt d' (off r (8 + 32 * rs.length)) [ρ.alpha, ρ.beta]) :
    BufRoundsAt d' r (rs ++ [ρ]) := by
  obtain ⟨-, -, he⟩ := h
  unfold roundCap at hlt
  refine ⟨by simp [roundCap]; omega, by simpa using hn, ?_⟩
  unfold RoundsAt
  rw [show roundEWs (rs ++ [ρ]) = roundEWs rs ++ [ρ.alpha, ρ.beta] by simp [roundEWs],
    NativeRustcVm.ewsAt_append_iff]
  refine ⟨bytesAt_of_agree (agree_sub hA (o := 8) (k := 32 * rs.length) (by omega)
    fun j hj hw ↦ by omega) ?_ he, ?_⟩
  · rw [NativeRustcVm.length_ewsBytes, length_roundEWs]; omega
  · rw [length_roundEWs, off_add, show 8 + 16 * (2 * rs.length) = 8 + 32 * rs.length by omega]
    exact hx

variable [Host] {k : Nat}

/-- `b23`: `0`, the epilogue. -/
theorem fail (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 foldRoundsStack)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRounds.b23Offset)) (hf : Frame m0 160 slots st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ st'.data.regs.X0 = 0 ∧
      st'.data.dmem = st.data.dmem ∧ Saved m0 st'.data) st := by
  have hfnw := frame_noWrap (m := m0) (F := 160) (by have := hst.2.1; rw [stack_eq] at this; omega)
  have hwf : (frameEnv m0 st.data 160 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 160) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 160 []) epiS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b23_in_code (by simp [b23]) hp) run_b23 hwf hpc hm fun st1 hm1 hpc1 => ?_
  obtain ⟨hepi, hmem, hx0⟩ := after_eq run_b23 ▸ ok_b23
  obtain ⟨hsv, hsl⟩ := Frame.epilogue hf hwf hm1 hepi
  have hx30 : st1.data.regs.X30 = m0.regs.X30 := hsl (112, .X30) (List.mem_cons_self ..)
  exact .done _ ⟨by simp only [PcOk] at hpc1; rw [hpc1]; simp only [retOf, hx30],
    UInt64.toBitVec_inj.mp (hm1.regs .X0 _ hx0), hm1.dmem_eq hwf hmem, hsv⟩

/-- `b8`: the epilogue, X0 kept. -/
theorem done (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 foldRoundsStack)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRounds.b8Offset)) (hf : Frame m0 160 slots st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ st'.data.regs.X0 = st.data.regs.X0 ∧
      st'.data.dmem = st.data.dmem ∧ Saved m0 st'.data) st := by
  have hfnw := frame_noWrap (m := m0) (F := 160) (by have := hst.2.1; rw [stack_eq] at this; omega)
  have hwf : (frameEnv m0 st.data 160 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 160) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 160 []) epiS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf hpc hm fun st1 hm1 hpc1 => ?_
  obtain ⟨hepi, hmem, hx0⟩ := after_eq run_b8 ▸ ok_b8
  obtain ⟨hsv, hsl⟩ := Frame.epilogue hf hwf hm1 hepi
  have hx30 : st1.data.regs.X30 = m0.regs.X30 := hsl (112, .X30) (List.mem_cons_self ..)
  exact .done _ ⟨by simp only [PcOk] at hpc1; rw [hpc1]; simp only [retOf, hx30],
    UInt64.toBitVec_inj.mp (hm1.regs .X0 _ hx0), hm1.dmem_eq hwf hmem, hsv⟩

/-- `b7`, `b8`: `1`, the epilogue. -/
theorem done7 (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 foldRoundsStack)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRounds.b7Offset)) (hf : Frame m0 160 slots st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ st'.data.regs.X0 = 1 ∧
      st'.data.dmem = st.data.dmem ∧ Saved m0 st'.data) st := by
  have hfnw := frame_noWrap (m := m0) (F := 160) (by have := hst.2.1; rw [stack_eq] at this; omega)
  have hwf : (frameEnv m0 st.data 160 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 160) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 160 []) epiS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf hpc hm fun st1 hm1 hpc1 => ?_
  obtain ⟨hmid, hmem, hx0⟩ := after_eq run_b7 ▸ ok_b7
  have hf1 : Frame m0 160 slots st1.data := Frame.of_block hf hwf hm1 hmid slots_le
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem
  have hX0 : st1.data.regs.X0 = 1 := UInt64.toBitVec_inj.mp (hm1.regs .X0 _ hx0)
  refine Eventually.mono (done hp hst (hpc1.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FoldRounds.b7_next])) hf1)
    fun st' ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, h2.trans hX0, h3.trans hd1, h4⟩

omit [Host] in
theorem apart_nat {a b : BitVec 64} {n m : Nat} (h : NativeRustcVm.Apart a n b m) :
    a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat := h

omit [Host] in
theorem inR {a q : BitVec 64} {n : Nat} (h : NativeRustcVm.NoWrap a n)
    (hq : NativeRustcVm.InRange a n q) : a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + n :=
  (inRange_iff' h).mp hq

omit [Host] in
theorem three_iff {a b c q : BitVec 64} {n m l : Nat} :
    NativeRustcVm.InAny [⟨a, n⟩, ⟨b, m⟩, ⟨c, l⟩] q ↔ NativeRustcVm.InRange a n q ∨
      NativeRustcVm.InRange b m q ∨ NativeRustcVm.InRange c l q := by
  simp only [NativeRustcVm.inAny_cons_iff, NativeRustcVm.inAny_nil, or_false,
    NativeRustcVm.Region.Holds]

omit [Host] in
theorem outs_iff {m0 : MachineData} {q : BitVec 64} :
    NativeRustcVm.InAny (outs m0) q ↔ NativeRustcVm.InRange m0.regs.X3.toBitVec 200 q ∨
      NativeRustcVm.InRange m0.regs.X2.toBitVec stateBytes q ∨
      NativeRustcVm.InRange m0.regs.X0.toBitVec tstateBytes q := by
  simp only [outs, NativeRustcVm.inAny_cons_iff, NativeRustcVm.inAny_nil, or_false,
    NativeRustcVm.Region.Holds]
  rfl

/-- The areas' positions as numbers: the `TState`, the area, the state and the buffer apart from the
stack and from each other. -/
structure Geo (t p r : BitVec 64) (sp aw al : Nat) : Prop where
  aTS : t.toNat + 760 ≤ sp - 960 ∨ sp ≤ t.toNat
  aAS : aw + al ≤ sp - 960 ∨ sp ≤ aw
  aPS : p.toNat + 61152 ≤ sp - 960 ∨ sp ≤ p.toNat
  aRS : r.toNat + 200 ≤ sp - 960 ∨ sp ≤ r.toNat
  aRP : r.toNat + 200 ≤ p.toNat ∨ p.toNat + 61152 ≤ r.toNat
  aRT : r.toNat + 200 ≤ t.toNat ∨ t.toNat + 760 ≤ r.toNat
  aRA : r.toNat + 200 ≤ aw ∨ aw + al ≤ r.toNat
  aPT : p.toNat + 61152 ≤ t.toNat ∨ t.toNat + 760 ≤ p.toNat

omit [Host] in
theorem geo [Labels] {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}
    (hpre : FoldRoundsPre a s w m0) :
    Geo m0.regs.X0.toBitVec m0.regs.X2.toBitVec m0.regs.X3.toBitVec m0.regs.SP.toNat a.words.toNat
      (8 * a.len) := by
  obtain ⟨⟨hst, -, -, htok, -⟩, -, -, -, -, ⟨hpo, -⟩, ⟨hro, -⟩, hrp⟩ := hpre
  have hn : 960 ≤ m0.regs.SP.toNat := hst.2.1
  have hsb : (stackBelow m0 960).toNat = m0.regs.SP.toNat - 960 := toNat_stackBelow hn
  have h1 := apart_nat htok.1
  have h2 := apart_nat htok.2.1
  have h3 := apart_nat hpo.2.2.2.2.1
  have h4 := apart_nat hro.2.2.2.2.1
  have h5 := apart_nat hrp
  have h6 := apart_nat hro.2.2.1
  have h7 := apart_nat hro.2.2.2.1
  have h8 := apart_nat hpo.2.2.1
  rw [stack_eq, hsb] at h1 h2 h3 h4
  simp only [tstateBytes, stateBytes, roundBytes, roundCap] at h1 h3 h4 h5 h6 h7 h8
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **One round**: from `fold_round`'s call, its tag tested (`T`), its `α`, `β` stored (`S`). -/
theorem round (hp : Placed code k)
    (hfr : ∀ a s w, Spec (Labels.label NativeRustcVmArm.Vm.FoldRound.entryLabel) (FoldRoundPre a s w) (FoldRoundPost a s w))
    {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData} (hpre : FoldRoundsPre a s w m0)
    {T S : List Directive} {kt i : Nat} {ST SS : SState} {cT : SBool} {xS : Exit}
    (hT : T.IsInfixAt code kt) (hTne : T ≠ [])
    (hrunT : exec T tagS = some (ST, .cond cT NativeRustcVmArm.Vm.FoldRounds.label_17)) (hokT : TagOk ST)
    (hc0 : ∀ d : MachineData, NativeRustcVm.WordAt d.dmem (off (frameBase m0 160) 40) 0 →
      cT.eval (frameEnv m0 d 160 []) = true)
    (hc1 : ∀ d : MachineData, NativeRustcVm.WordAt d.dmem (off (frameBase m0 160) 40) 1 →
      cT.eval (frameEnv m0 d 160 []) = false)
    (hS : S.IsInfixAt code (kt + T.length)) (hSne : S ≠ [])
    (hrunS : exec S storeS = some (SS, xS)) (hokS : StoreOk (i + 1) SS)
    (hi : i < m0.regs.X1.toNat) {st : MachineState}
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.FoldRound.entryLabel ∧ retOf st.data = Host.addrOf (k + kt))
    (hI : Inv m0 a s w i st.data) (hx0 : st.data.regs.X0.toBitVec = off (frameBase m0 160) 40)
    (hx1 : st.data.regs.X1.toBitVec = m0.regs.X0.toBitVec)
    (hx2 : st.data.regs.X2.toBitVec = m0.regs.X2.toBitVec)
    (cont : ∀ st' : MachineState, Inv m0 a s w (i + 1) st'.data →
      (∃ env : Env, env.regs .X22 = m0.regs.X1.toBitVec ∧
        PcOk env xS (Host.addrOf (k + (kt + T.length) + S.length)) st' ∧
        ∀ v, SS.reg .X0 = some v → st'.data.regs.X0.toBitVec = v.eval env) →
      Eventually (step1 Host.exe) (Goal a s w m0) st') :
    Eventually (step1 Host.exe) (Goal a s w m0) st := by
  have hpre' := hpre
  have g := geo hpre
  obtain ⟨⟨hst, hrc, hrod, htok, hrt⟩, hts, hws, hn6, hal, ⟨hpo, hpr⟩, ⟨hro, hrr⟩, hrp⟩ := hpre
  set t := m0.regs.X0.toBitVec with htdef
  set p := m0.regs.X2.toBitVec with hpdef
  set r := m0.regs.X3.toBitVec with hrdef
  set fb := frameBase m0 160 with hfbdef
  obtain ⟨hf, h19, h20, h21, h22, h23, ⟨w1, rs, s1, hrun, hrs, hal1, hws1, hbr1, hts1⟩, hsame⟩ :=
    hI
  -- Geometry.
  have hn : 960 ≤ m0.regs.SP.toNat := hst.2.1
  have hlt := m0.regs.SP.toNat_lt
  have hfnw : fb.toNat + 160 ≤ 2 ^ 64 := frame_noWrap (m := m0) (F := 160) (by omega)
  have hfb : fb.toNat = m0.regs.SP.toNat - 160 := frameBase_toNat (n := 960) hn (by decide)
  have hsb : (stackBelow m0 960).toNat = m0.regs.SP.toNat - 960 := toNat_stackBelow hn
  have hsnw : NativeRustcVm.NoWrap (stackBelow m0 960) 960 := by
    show _ + 960 ≤ _; omega
  have hTn : t.toNat + 760 ≤ 2 ^ 64 := hts.footprint.1.2
  have hAn : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hts.footprint.2.1.2
  have hpn : p.toNat + 61152 ≤ 2 ^ 64 := hpo.2.1
  have hrn : r.toNat + 200 ≤ 2 ^ 64 := hro.2.1
  have hrcOut : ∀ q, (NativeRustcVm.InAny (outs m0) q ∨
      NativeRustcVm.InRange (stackBelow m0 foldRoundsStack) foldRoundsStack q) →
      ¬ NativeRustcVm.InRange rcAddr 192 q := by
    intro q hq hrq
    have hrcn : rcAddr.toNat + 192 ≤ 2 ^ 64 := hrc.2.1
    have aCS := apart_nat hrc.2.2; rw [stack_eq, hsb] at aCS
    have aCT := apart_nat htok.2.2; simp only [tstateBytes] at aCT
    have aCP := apart_nat hpo.2.2.2.2.2; simp only [stateBytes] at aCP
    have aCR := apart_nat hro.2.2.2.2.2; simp only [roundBytes, roundCap] at aCR
    have := inR hrcn hrq
    rw [outs_iff, stack_eq] at hq
    rcases hq with (hq | hq | hq) | hq
    · have := inR hrn hq; omega
    · have := inR hpn hq; omega
    · have := inR hTn hq; omega
    · have := inR hsnw hq; omega
  have hrodOut : ∀ q, (NativeRustcVm.InAny (outs m0) q ∨
      NativeRustcVm.InRange (stackBelow m0 foldRoundsStack) foldRoundsStack q) →
      ∀ it : NativeRustcVm.Data.Item, ¬ NativeRustcVm.InRange (rodataAddr it) it.bytes.length q := by
    intro q hq it hq'
    have hin := (hrod it).2.1
    have hin' : (rodataAddr it).toNat + it.bytes.length ≤ 2 ^ 64 := hin
    have aIS := apart_nat (hrod it).2.2; rw [stack_eq, hsb] at aIS
    have aIT := apart_nat (hrt it); simp only [tstateBytes] at aIT
    have aIP := apart_nat (hpr it); simp only [stateBytes] at aIP
    have aIR := apart_nat (hrr it); simp only [roundBytes, roundCap] at aIR
    have := inR hin' hq'
    rw [outs_iff, stack_eq] at hq
    rcases hq with (hq | hq | hq) | hq
    · have := inR hrn hq; omega
    · have := inR hpn hq; omega
    · have := inR hTn hq; omega
    · have := inR hsnw hq; omega
  -- `fold_round`.
  have hsp : st.data.regs.SP.toNat = m0.regs.SP.toNat - 160 := by
    rw [← UInt64.toNat_toBitVec, hf.sp, hfb]
  have ho : (off fb 40).toNat = m0.regs.SP.toNat - 160 + 40 := by rw [toNat_off (by omega), hfb]
  have hpre1 : FoldRoundPre a s1 w1 st.data := by
    unfold FoldRoundPre
    rw [hx0, hx1, hx2]
    refine ⟨⟨stackOk_callee hst hf.kept hf.sp (by decide) (by decide) (by decide),
      RcAt.callee hrc (rc_keep hsame hrcOut) hn (F := 160) (by decide) hsp (by decide),
      rodataAt_callee hrod hsame hrodOut hf.sp hn (by decide) (by decide), 
      TStateOk.callee htok hf.sp hn (by decide) (by decide), hrt⟩, hts1, hws1,
      by rw [hal1]; unfold stackCap at hal ⊢; omega,
      ⟨OutOk.callee hpo hf.kept hf.sp hn (by decide) (by decide), hpr⟩,
      ⟨OutOk.frame hst (by decide) (by decide) hf.sp hf.kept (by decide) htok hrc,
        rodataApart_stack hrod (by rw [ho, stack_eq, hsb]; omega)
          (by rw [ho, stack_eq, hsb]; omega)⟩, ?_⟩
    show (off fb 40).toNat + 40 ≤ p.toNat ∨ p.toNat + stateBytes ≤ (off fb 40).toNat
    rw [ho]; simp only [stateBytes]; have := g.aPS; omega
  refine call_then (env := frameEnv m0 st.data 160 []) hpc (hfr a s1 w1) hpre1 fun st2 hpc2 ⟨hout2, hch2, hsv2⟩ => ?_
  rw [hx0] at hout2
  rw [hx2] at hout2
  rw [hx1] at hout2
  rw [hx0, hx1, hx2] at hch2
  have hon : NativeRustcVm.NoWrap (off fb 40) 40 := by show _ + 40 ≤ _; rw [ho]; omega
  have hR2 : ∀ q, (NativeRustcVm.InAny [⟨off fb 40, 40⟩, ⟨p, stateBytes⟩, ⟨t, tstateBytes⟩] q ∨
      NativeRustcVm.InRange (stackBelow st.data foldRoundStack) foldRoundStack q) →
      NativeRustcVm.InRange (off fb 40) 40 q ∨ NativeRustcVm.InRange p stateBytes q ∨
        NativeRustcVm.InRange t tstateBytes q ∨
        (NativeRustcVm.InRange (stackBelow m0 960) 960 q ∧ ¬ NativeRustcVm.InRange fb 160 q) := by
    intro q h
    rw [three_iff] at h
    rcases h with (h | h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (inRange_callee hf.sp hst.2.1 (by decide) (by decide) h)))
  have hf2 : Frame m0 160 slots st2.data := by
    refine Frame.call_slots hf hsv2 hch2 fun p' hp' j hj h ↦ ?_
    rw [← hfbdef] at h
    have := slots_le p' hp'
    have hsl : (off fb (p'.1 + j)).toNat = fb.toNat + (p'.1 + j) := toNat_off (by omega)
    rcases hR2 _ h with h | h | h | h
    · exact not_slot_out hfnw (by decide) slots_le (by decide) p' hp' j hj h
    · have := inR hpn h; have := g.aPS; omega
    · have := inR hTn h; have := g.aTS; omega
    · exact h.2 (inRange_off_self (by omega) (by omega))
  have hnot : ∀ q, ¬ (NativeRustcVm.InAny (outs m0) q ∨
      NativeRustcVm.InRange (stackBelow m0 foldRoundsStack) foldRoundsStack q) →
      ¬ NativeRustcVm.InRange r 200 q ∧ ¬ NativeRustcVm.InRange p stateBytes q ∧
        ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange (stackBelow m0 960) 960 q := by
    intro q hq
    rw [outs_iff, stack_eq] at hq
    simp only [not_or] at hq
    exact ⟨hq.1.1, hq.1.2.1, hq.1.2.2, hq.2⟩
  have hstk : ∀ q, NativeRustcVm.InRange fb 160 q → NativeRustcVm.InRange (stackBelow m0 960) 960 q :=
    fun q h ↦ inRange_frame_stack (n := 960) hn (by decide) h
  have hsame2 : ChangesIn m0 st2.data foldRoundsStack (outs m0) := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hnot q hq
    rw [hch2 q fun h ↦ by
      rcases hR2 q h with h | h | h | h
      · refine h4 ((inRange_iff' hsnw).mpr ?_)
        have := inR hon h; rw [ho] at this; rw [hsb]; omega
      · exact h2 h
      · exact h3 h
      · exact h4 h.1]
    exact hsame q hq
  have hA2 : Agree st.data.dmem st2.data.dmem r 200 (fun _ ↦ False) := by
    refine NativeRustcVmArm.Whir.agree_of_sameOutside hch2 fun j hj _ h ↦ ?_
    have hj' : (off r j).toNat = r.toNat + j := toNat_off (by omega)
    generalize hq : off r j = q at h hj'
    rcases hR2 q h with h | h | h | h
    · have := (inRange_iff' hon).mp h; rw [ho] at this; have := g.aRS; omega
    · have := (inRange_iff' (n := stateBytes) hpn).mp h; simp only [stateBytes] at this
      have := g.aRP; omega
    · have := (inRange_iff' (n := tstateBytes) hTn).mp h; simp only [tstateBytes] at this
      have := g.aRT; omega
    · have := (inRange_iff' hsnw).mp h.1; rw [hsb] at this; have := g.aRS; omega
  have hbr2 : BufRoundsAt st2.data.dmem r rs.toList := bufRoundsAt_agree hbr1 hA2
  -- `T`: the tag.
  have hwf2 : (frameEnv m0 st2.data 160 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 160) hst (by decide)) hf2.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm2 : Match (frameEnv m0 st2.data 160 []) tagS st2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf2.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of hT hTne hp) hrunT hwf2 hpc2 hm2 fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hmem3, t19, t20, t21, t22, t23⟩ := hokT
  have hf3 : Frame m0 160 slots st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have g19 : st3.data.regs.X19 = st.data.regs.X19 :=
    (Match.reg_eq hm2 hm3 rfl t19).trans (hsv2.1 .X19 rfl)
  have g20 : st3.data.regs.X20 = st.data.regs.X20 :=
    (Match.reg_eq hm2 hm3 rfl t20).trans (hsv2.1 .X20 rfl)
  have g21 : st3.data.regs.X21 = st.data.regs.X21 :=
    (Match.reg_eq hm2 hm3 rfl t21).trans (hsv2.1 .X21 rfl)
  have g22 : st3.data.regs.X22 = st.data.regs.X22 :=
    (Match.reg_eq hm2 hm3 rfl t22).trans (hsv2.1 .X22 rfl)
  have g23 : st3.data.regs.X23 = st.data.regs.X23 :=
    (Match.reg_eq hm2 hm3 rfl t23).trans (hsv2.1 .X23 rfl)
  simp only [PcOk] at hpc3
  cases hfr2 : (foldRound w1).run s1 with
  | none =>
    rw [hfr2] at hout2
    rw [hc0 st2.data hout2] at hpc3
    simp only [↓reduceIte] at hpc3
    have hnone : (foldRounds m0.regs.X1.toNat w).run s = none := foldRounds_none_of hrun hfr2 _ hi
    refine Eventually.mono (fail hp hst (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.FoldRounds.b23Offset) NativeRustcVmArm.Vm.FoldRounds.label_17_at)) hf3)
      fun st' ⟨hpc', hx0', hd', hsv'⟩ ↦ ⟨hpc', ?_, ?_, ?_, hsv'⟩
    · show st'.data.regs.X0 = okWord ((foldRounds m0.regs.X1.toNat w).run s).isSome
      rw [hnone, hx0']; rfl
    · intro w' rs' s' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd', hd3]; exact hsame2 q hq
  | some q2 =>
  obtain ⟨⟨w2, ρ⟩, s2⟩ := q2
  rw [hfr2] at hout2
  obtain ⟨ht1, hab, hws2, hts2⟩ := hout2
  rw [hc1 st2.data ht1] at hpc3
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc3
  -- `S`: `α`, `β` stored.
  have hiS : i < 6 := by have : m0.regs.X1.toNat ≤ 6 := hn6; omega
  have hwf3 : (frameEnv m0 st3.data 160 [(r, 200)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 160) hst (by decide)) hf3.kept, hfnw⟩,
      ⟨Mapped.keeps hro.1 hf3.kept, hro.2.1⟩, trivial⟩ (List.pairwise_pair.mpr (by
        show fb.toNat + 160 ≤ r.toNat ∨ r.toNat + 200 ≤ fb.toNat
        have := g.aRS; omega))
  have hX23 : (st3.data.regs.getXReg .X23).toBitVec = fb + BitVec.ofInt 64 40 := by
    show st3.data.regs.X23.toBitVec = _
    rw [g23, h23]; rfl
  have hm3' : Match (frameEnv m0 st3.data 160 [(r, 200)]) storeS st3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      (by rw [hf3.sp]; exact (eval_ptr rfl).symm)
      ⟨known_ptr rfl (by show st3.data.regs.X21.toBitVec = _; rw [g21, h21]), hX23, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of hS hSne hp) hrunS hwf3 (hpc3.trans (by rw [Nat.add_assoc])) hm3'
    fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hw0, hwa, hwb, hwc, hwd, hws4, s19, s20, s21, s22, s23⟩ := hokS
  simp only [Nat.add_sub_cancel] at hwa hwb hwc hwd hws4
  have hf4 : Frame m0 160 slots st4.data := Frame.of_block hf3 hwf3 hm4 hmid4 slots_le
  have hs4 : SameOutside st2.data.dmem st4.data.dmem (fun q ↦
      Touch r 200 (fun j ↦ j < 8 ∨ (8 + 32 * i ≤ j ∧ j < 40 + 32 * i)) q ∨
        NativeRustcVm.InRange fb 160 q) := fun q hq ↦ by
    rw [← hd3]
    refine hm4.get?_mem0 hwf3 fun hW ↦ hq ?_
    obtain ⟨wr, hwr, b, sz, hb, j, h1, h2, rfl⟩ := written_off hwf3 hW
    rcases hws4 wr hwr with ⟨hr1, hle⟩ | ⟨hr1, hlo, hhi⟩ | ⟨hr0, hle⟩
    · rw [hr1] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact Or.inl ⟨j, by omega, Or.inl (by omega), rfl⟩
    · rw [hr1] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact Or.inl ⟨j, by omega, Or.inr ⟨by omega, by omega⟩, rfl⟩
    · rw [hr0] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact Or.inr (inRange_off_self (by omega) (by omega))
  -- The buffer.
  have hc := wordAt_write hm4 (r := 1) (o := 0) (b := r) (sz := 200) rfl (by decide) hw0
  rw [off_zero] at hc
  have hab' := hab
  rw [off_off, ewsAt_cons, ewsAt_cons, ewAt_iff, ewAt_iff, off_off, off_off, off_off] at hab'
  obtain ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩, -⟩ := hab'
  have hl0 : (frameEnv m0 st3.data 160 [(r, 200)]).load 0 48 8 = ρ.alpha.c0.toBitVec :=
    load_ofMachine (o := 48) rfl (by rw [hd3]; exact ha0)
  have hl1 : (frameEnv m0 st3.data 160 [(r, 200)]).load 0 56 8 = ρ.alpha.c1.toBitVec :=
    load_ofMachine (o := 56) rfl (by rw [hd3]; exact ha1)
  have hl2 : (frameEnv m0 st3.data 160 [(r, 200)]).load 0 64 8 = ρ.beta.c0.toBitVec :=
    load_ofMachine (o := 64) rfl (by rw [hd3]; exact hb0)
  have hl3 : (frameEnv m0 st3.data 160 [(r, 200)]).load 0 72 8 = ρ.beta.c1.toBitVec :=
    load_ofMachine (o := 72) rfl (by rw [hd3]; exact hb1)
  have hv0 := wordAt_write hm4 (r := 1) (o := 8 + 32 * i) (b := r) (sz := 200) rfl (by omega) hwa
  have hv1 := wordAt_write hm4 (r := 1) (o := 16 + 32 * i) (b := r) (sz := 200) rfl (by omega) hwb
  have hv2 := wordAt_write hm4 (r := 1) (o := 24 + 32 * i) (b := r) (sz := 200) rfl (by omega) hwc
  have hv3 := wordAt_write hm4 (r := 1) (o := 32 + 32 * i) (b := r) (sz := 200) rfl (by omega) hwd
  rw [show (Sym.load 0 48 8).eval (frameEnv m0 st3.data 160 [(r, 200)]) = _ from hl0] at hv0
  rw [show (Sym.load 0 56 8).eval (frameEnv m0 st3.data 160 [(r, 200)]) = _ from hl1] at hv1
  rw [show (Sym.load 0 64 8).eval (frameEnv m0 st3.data 160 [(r, 200)]) = _ from hl2] at hv2
  rw [show (Sym.load 0 72 8).eval (frameEnv m0 st3.data 160 [(r, 200)]) = _ from hl3] at hv3
  have hab4 : NativeRustcVm.EWsAt st4.data.dmem (off r (8 + 32 * i)) [ρ.alpha, ρ.beta] := by
    refine ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨hv0, ?_⟩, ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨?_, ?_⟩,
      ewsAt_nil _ _⟩⟩
    · rw [off_off, show 8 + 32 * i + 8 = 16 + 32 * i by omega]; exact hv1
    · rw [off_off, show 8 + 32 * i + 16 = 24 + 32 * i by omega]; exact hv2
    · rw [off_off, off_off, show 8 + 32 * i + 16 + 8 = 32 + 32 * i by omega]; exact hv3
  have hA4 : Agree st2.data.dmem st4.data.dmem r 200
      (fun j ↦ j < 8 ∨ (8 + 32 * i ≤ j ∧ j < 40 + 32 * i)) :=
    NativeRustcVm.Transcript.agree_of_sameOutside hrn (fun q hq h ↦ by
      have := inR hrn h; have := inR hfnw hq; have := g.aRS; omega) hs4
  have hbr4 : BufRoundsAt st4.data.dmem r (rs.toList ++ [ρ]) := by
    refine bufRoundsAt_push hbr2 (by rw [Array.length_toList, hrs]; unfold roundCap; omega)
      (by rw [Array.length_toList, hrs]; exact hA4) (by rw [Array.length_toList, hrs]; exact hc)
      (by rw [Array.length_toList, hrs]; exact hab4)
  -- The state and the `TState`.
  have hws4 : WhirStateAt st4.data.dmem p w2 :=
    hws2.agree (NativeRustcVmArm.Whir.agree_of_sameOutside hs4 fun j hj _ h ↦ by
      have hj' : (off p j).toNat = p.toNat + j := toNat_off (by simp only [stateBytes] at hj; omega)
      generalize off p j = q at h hj'
      have := g.aRP; have := g.aPS
      rcases h with h | h
      · have := inR hrn (inRange_of_touch hrn h); simp only [stateBytes] at hj; omega
      · have := inR hfnw h; simp only [stateBytes] at hj; omega)
  have hts4 : TStateAt st4.data.dmem t a s2 := by
    refine hts2.frame (by rw [← hd3]; exact hm4.kept hwf3) (fun q h ↦ ?_) hs4
    have := g.aRT; have := g.aRA; have := g.aTS; have := g.aAS
    rcases h with h | h
    · have := inR hrn (inRange_of_touch hrn h)
      exact ⟨fun h' ↦ by have := inR hTn h'; omega,
        fun h' ↦ by have := inR hAn h'; omega⟩
    · have := inR hfnw h
      exact ⟨fun h' ↦ by have := inR hTn h'; omega,
        fun h' ↦ by have := inR hAn h'; omega⟩
  -- `Inv (i + 1)`.
  refine cont st4 ⟨hf4, ?_, ?_, ?_, ?_, ?_, ⟨w2, rs.push ρ, s2, foldRounds_some hrun hfr2,
    by rw [Array.size_push, hrs], by rw [foldRound_alphas hfr2, hal1]; omega, hws4,
    by rw [Array.toList_push]; exact hbr4, hts4⟩, ?_⟩
    ⟨frameEnv m0 st3.data 160 [(r, 200)], ?_, hpc4, fun v hv ↦ hm4.regs .X0 v hv⟩
  · rw [show st4.data.regs.X19 = st3.data.regs.X19 from Match.reg_eq hm3' hm4 rfl s19, g19]
    exact h19
  · rw [show st4.data.regs.X20 = st3.data.regs.X20 from Match.reg_eq hm3' hm4 rfl s20, g20]
    exact h20
  · show (st4.data.regs.getXReg .X21).toBitVec = _
    rw [hm4.regs .X21 _ s21]; exact eval_ptr rfl
  · rw [show st4.data.regs.X22 = st3.data.regs.X22 from Match.reg_eq hm3' hm4 rfl s22, g22]
    exact h22
  · show (st4.data.regs.getXReg .X23).toBitVec = _
    rw [hm4.regs .X23 _ s23]; rfl
  · intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hnot q hq
    rw [hs4 q fun h ↦ by
      rcases h with h | h
      · exact h1 (inRange_of_touch hrn h)
      · exact h4 (hstk q h)]
    exact hsame2 q hq
  · show (st3.data.regs.getXReg .X22).toBitVec = _
    rw [show st3.data.regs.getXReg .X22 = st3.data.regs.X22 from rfl, g22, h22]

end

end NativeRustcVmArm.Whir.FoldRounds
