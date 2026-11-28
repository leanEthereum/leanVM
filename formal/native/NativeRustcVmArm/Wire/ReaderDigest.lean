module

public import NativeRustcVmArm.Code.Vm.ReaderDigest.Names
public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Wire.ReaderDigest.Exec
public import NativeRustcVmArm.Wire.Frame

/-!
# `Reader::digest` meets its contract

`readerDigest_spec`: four calls of `Reader::le` for eight bytes each (`b0`, `b2`, `b4`, `b6`), each
checked (`b1`, `b3`, `b5`, `b7`, `check`): all succeed, the digest's words stored with the tag `1`
(`b8`); one fails, the tag `0` (`b9`). Between the prologue and the epilogue the state is the
frame's (`Ring.Fr`), X19 the output, X20 the reader (`Mid`).
-/

namespace NativeRustcVmArm.Wire.ReaderDigest

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVm.Transcript (off)
open NativeRustcVmArm.Vm.ReaderDigest

@[expose] public section

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(40, .X19), (32, .X20), (24, .X21), (16, .X22), (8, .X23), (0, .X30)]

/-- The callee-saved registers it does not save. -/
def keep : List XReg := [.X24, .X25, .X26, .X27, .X28, .X29]

/-- What it writes besides its frame: the reader's cursor and the output. -/
abbrev outs (m0 : MachineData) : BitVec 64 → Prop :=
  Wire.outs m0.regs.X1.toBitVec (InRange m0.regs.X0.toBitVec 40)

/-- Between the prologue and the epilogue: the frame, X19 the output, X20 the reader. -/
structure Mid (m0 m : MachineData) : Prop where
  fr : Fr m0 48 48 slots keep (outs m0) m
  x19 : m.regs.X19 = m0.regs.X0
  x20 : m.regs.X20 = m0.regs.X1

/-- The environment between the calls: the frame (region 0) and the output (region 1). -/
abbrev midEnv (m0 m : MachineData) : Env :=
  Env.ofMachine m [(base m0 48, 48), (m0.regs.X0.toBitVec, 40)]

/-- What `Reader::digest` reaches. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ ReaderDigestPost m0 st.data

end

public section

/-- `ReaderDigestPre`'s places, as numbers. -/
structure Geo (m0 : MachineData) (bp : BitVec 64) (L : Nat) : Prop where
  st : StackOk m0 48
  out : NativeRustcVm.Mapped m0.dmem m0.regs.X0.toBitVec 40
  outNw : NoWrap m0.regs.X0.toBitVec 40
  rNw : NoWrap m0.regs.X1.toBitVec 24
  bpNw : NoWrap bp L
  sr : Apart (base m0 48) 48 m0.regs.X1.toBitVec 24
  sb : Apart (base m0 48) 48 bp L
  so : Apart (base m0 48) 48 m0.regs.X0.toBitVec 40
  rb : Apart m0.regs.X1.toBitVec 24 bp L
  ro : Apart m0.regs.X1.toBitVec 24 m0.regs.X0.toBitVec 40
  bo : Apart bp L m0.regs.X0.toBitVec 40

theorem geo_of [Labels] {m0 : MachineData} (h : ReaderDigestPre m0) {bp : BitVec 64}
    {B : List UInt8} {c : Nat} (hR : ReaderAt m0.dmem m0.regs.X1.toBitVec bp B c) :
    Geo m0 bp B.length := by
  obtain ⟨hst, ⟨hom, honw⟩, bp', B', c', hR', hd⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := hR'.unique hR
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hd
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := hd
  exact ⟨hst, hom, honw, hR.ok.2, hR.noWrap, h1, h2, h3, h4, h5, h6⟩

section
variable {m0 : MachineData} {bp : BitVec 64} {L : Nat}

theorem base_eq_stackBelow : base m0 48 = stackBelow m0 48 := rfl

theorem not_frame_of_outs (g : Geo m0 bp L) {q : BitVec 64} (h : outs m0 q) :
    ¬InRange (base m0 48) 48 q := by
  have hb := Ring.base_noWrap (m0 := m0) (F := 48) g.st.2.1
  rcases h with h | h
  · have hr : InRange m0.regs.X1.toBitVec 24 q := NativeRustcVm.InRange.of_sub (o := 16) (m := 8) h g.rNw (by omega)
    exact NativeRustcVm.Apart.not_inRange g.sr.symm g.rNw hb hr
  · exact NativeRustcVm.Apart.not_inRange g.so.symm g.outNw hb h

/-- The reader's bytes are neither the frame nor the outputs. -/
theorem bytes_not (g : Geo m0 bp L) {i : Nat} (hi : i < L) :
    ¬(InRange (base m0 48) 48 (bp + BitVec.ofNat 64 i) ∨ outs m0 (bp + BitVec.ofNat 64 i)) := by
  have hb := Ring.base_noWrap (m0 := m0) (F := 48) g.st.2.1
  have hin : InRange bp L (bp + BitVec.ofNat 64 i) :=
    NativeRustcVm.inRange_add hi (by have := g.bpNw; unfold NoWrap at this; omega)
  rintro (h | h | h)
  · exact NativeRustcVm.Apart.not_inRange g.sb.symm g.bpNw hb hin h
  · exact NativeRustcVm.Apart.not_inRange g.rb.symm g.bpNw g.rNw hin
      (NativeRustcVm.InRange.of_sub (o := 16) (m := 8) h g.rNw (by omega))
  · exact NativeRustcVm.Apart.not_inRange g.bo g.bpNw g.outNw hin h

/-- The reader's first 16 bytes are neither the frame nor the outputs. -/
theorem reader_not (g : Geo m0 bp L) {i : Nat} (hi : i < 16) :
    ¬(InRange (base m0 48) 48 (m0.regs.X1.toBitVec + BitVec.ofNat 64 i) ∨
      outs m0 (m0.regs.X1.toBitVec + BitVec.ofNat 64 i)) := by
  have hb := Ring.base_noWrap (m0 := m0) (F := 48) g.st.2.1
  have hin : InRange m0.regs.X1.toBitVec 24 (m0.regs.X1.toBitVec + BitVec.ofNat 64 i) :=
    NativeRustcVm.inRange_add (by omega) (by have := g.rNw; unfold NoWrap at this; omega)
  rintro (h | h | h)
  · exact NativeRustcVm.Apart.not_inRange g.sr.symm g.rNw hb hin h
  · exact NativeRustcVm.not_inRange_sub g.rNw (by omega) (by omega) (.inl hi) h
  · exact NativeRustcVm.Apart.not_inRange g.ro g.rNw g.outNw hin h

/-- A reader survives what the frame allows, its cursor aside. -/
theorem reader_frame {d d' : DataMem} {B : List UInt8} {c : Nat} (g : Geo m0 bp B.length)
    (hR : ReaderAt d m0.regs.X1.toBitVec bp B c)
    (hs : SameOutside d d' fun q ↦ InRange (base m0 48) 48 q ∨ InRange m0.regs.X0.toBitVec 40 q) :
    ReaderAt d' m0.regs.X1.toBitVec bp B c := by
  refine hR.frame hs (fun i hi hq ↦ ?_) (fun i hi hq ↦ bytes_not g hi ?_)
  · by_cases h16 : i < 16
    · exact reader_not g h16 (hq.elim .inl fun h ↦ .inr (.inr h))
    · have hb := Ring.base_noWrap (m0 := m0) (F := 48) g.st.2.1
      have hin : InRange m0.regs.X1.toBitVec 24 (m0.regs.X1.toBitVec + BitVec.ofNat 64 i) :=
        NativeRustcVm.inRange_add (by omega) (by have := g.rNw; unfold NoWrap at this; omega)
      rcases hq with h | h
      · exact NativeRustcVm.Apart.not_inRange g.sr.symm g.rNw hb hin h
      · exact NativeRustcVm.Apart.not_inRange g.ro g.rNw g.outNw hin h
  · exact hq.elim .inl fun h ↦ .inr (.inr h)

theorem midEnv_wf (g : Geo m0 bp L) {m : MachineData} (hM : Mid m0 m) : (midEnv m0 m).WF := by
  refine Env.wf_of ⟨⟨fun i hi ↦ hM.fr.kept _ (g.st.2.2 i hi),
    Ring.base_noWrap g.st.2.1⟩, ⟨fun i hi ↦ hM.fr.kept _ (g.out i hi), g.outNw⟩, trivial⟩
    (List.pairwise_pair.mpr g.so)

theorem midEnv_match [Labels] (g : Geo m0 bp L) {m : MachineData} (hM : Mid m0 m) :
    Match (midEnv m0 m) callS m := by
  have hal : (base m0 48).toNat % 16 = 0 := by
    rw [Ring.base_toNat g.st.2.1]; have := g.st.1; omega
  refine match_ofMachine ⟨rfl, fun _ ↦ hal, rfl, nofun, trivial⟩ ?_ ⟨?_, trivial⟩ trivial trivial
    trivial
  · rw [hM.fr.sp]; simp [Sym.eval]
  · show m.regs.X19.toBitVec = _
    rw [hM.x19]; simp [Sym.eval]

end

/-- The postcondition from the reader's bytes and cursor, and the frame's changes. -/
theorem post_of [Labels] {m0 m m' : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (hR : ReaderAt m0.dmem m0.regs.X1.toBitVec bp B c)
    (hres : match rdDigest B c with
      | some (dg, c') => WordAt m'.dmem m0.regs.X0.toBitVec 1 ∧
          WordsAt m'.dmem (off m0.regs.X0.toBitVec 8) dg.toList ∧
          ReaderAt m'.dmem m0.regs.X1.toBitVec bp B c'
      | none => WordAt m'.dmem m0.regs.X0.toBitVec 0)
    (hs0 : SameOutside m0.dmem m.dmem fun q ↦ InRange (base m0 48) 48 q ∨ outs m0 q)
    (hs1 : SameOutside m.dmem m'.dmem (InRange m0.regs.X0.toBitVec 40)) (hsv : Saved m0 m') :
    ReaderDigestPost m0 m' := by
  refine ⟨fun bp' B' c' hR' ↦ ?_, fun p hp ↦ ?_, hsv⟩
  · obtain ⟨rfl, rfl, rfl⟩ := hR.unique hR'
    exact hres
  · rw [hs1 p fun h ↦ hp ⟨_, List.mem_cons_self, h⟩, hs0 p ?_]
    rintro (h | h | h)
    · exact hp ⟨stackR m0 readerDigestStack, by simp, h⟩
    · exact hp ⟨curRegion m0.regs.X1.toBitVec, by simp, h⟩
    · exact hp ⟨_, List.mem_cons_self, h⟩

theorem rdDigest_none {B : List UInt8} {c : Nat} (h : ¬c + 32 ≤ B.length) : rdDigest B c = none := by
  simp [rdDigest, h]

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

theorem wordsAt4 {d : DataMem} {a : BitVec 64} {w0 w1 w2 w3 : UInt64}
    (h0 : WordAt d (a + BitVec.ofNat 64 8) w0) (h1 : WordAt d (a + BitVec.ofNat 64 16) w1)
    (h2 : WordAt d (a + BitVec.ofNat 64 24) w2) (h3 : WordAt d (a + BitVec.ofNat 64 32) w3) :
    WordsAt d (off a 8) [w0, w1, w2, w3] := by
  rw [NativeRustcVm.wordsAt_iff]
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rw [NativeRustcVm.addr_add_add]
  interval_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

variable [Host] {k : Nat}

theorem lbl (hp : Placed code k) {j : Nat} {l : Label} (h : Vm.ReaderDigest.code[j]? = some (.label l)) :
    Labels.label l = Host.addrOf (k + j) :=
  hp.label h

/-- **A call of `Reader::le` for eight bytes** from a state of the frame. -/
theorem le_call (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) {m0 : MachineData}
    {bp : BitVec 64} {B : List UInt8} {c : Nat} (g : Geo m0 bp B.length) {st : MachineState}
    {next : Int64} {R : MachineState → Prop} (hM : Mid m0 st.data)
    (hR : ReaderAt st.data.dmem m0.regs.X1.toBitVec bp B c)
    (hx0 : st.data.regs.X0 = m0.regs.X1) (hx1 : st.data.regs.X1.toNat = 8)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel ∧ retOf st.data = next)
    (cont : ∀ m2, Mid m0 m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      ReadRes m0.regs.X1.toBitVec bp B c m2 → Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Wire.le_call hle (RGeo.of_apart g.st g.rNw g.bpNw g.outNw g.sr g.sb g.so g.rb g.ro g.bo)
    (by decide) (by omega) (by decide) (by decide) hM.fr hR (by rw [hx0]) hx1 hpc
    fun m2 hfr hcs _ hres ↦ cont m2 ⟨hfr, (hcs .X19 rfl).trans hM.x19, (hcs .X20 rfl).trans hM.x20⟩
      hcs hres

omit [Host] in
theorem x0_eq_one {m : MachineData} (h : m.regs.X0 = 1) :
    (m.regs.getXReg .X0).toBitVec = BitVec.ofNat 64 1 := by
  rw [show m.regs.getXReg .X0 = m.regs.X0 from rfl, h]; rfl

omit [Host] in
theorem x0_eq_zero {m : MachineData} (h : m.regs.X0 = 0) :
    (m.regs.getXReg .X0).toBitVec = BitVec.ofNat 64 0 := by
  rw [show m.regs.getXReg .X0 = m.regs.X0 from rfl, h]; rfl

/-- **A check of a read** (`b1`, `b3`, `b5`, `b7`): to `None` (`b9`) if it failed, else on. -/
theorem check (hp : Placed code k) {ds : List Directive} {j : Nat} (hds : ds.IsInfixAt code j)
    (hne : ds ≠ []) (hrun : exec ds callS = exec b1 callS) (hlen : ds.length = 2)
    {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c0 : Nat} (g : Geo m0 bp B.length)
    (hR0 : ReaderAt m0.dmem m0.regs.X1.toBitVec bp B c0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + j)) (hM : Mid m0 st.data)
    (hx0 : st.data.regs.X0 = 0 ∨ st.data.regs.X0 = 1)
    (hnone : st.data.regs.X0 = 0 → ¬c0 + 32 ≤ B.length)
    (cont : st.data.regs.X0 = 1 → ∀ st', st'.pc = Host.addrOf (k + j + 2) → Mid m0 st'.data →
      st'.data.dmem = st.data.dmem →
      (∀ r ∈ [XReg.X1, .X21, .X22, .X23], st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) (Post m0) st') :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hwf := midEnv_wf g hM
  have hm := midEnv_match g hM
  refine exec_at (infix_of hds hne hp) (hrun.trans run_b1) hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, hlen] at hpc1
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  rcases hx0 with h0 | h1
  · have hc : (SBool.not (SBool.cmp .eq .W64 (.reg .X0) (.lit 1))).eval (midEnv m0 st.data) =
        true := by
      simp only [SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, Env.ofMachine_regs, x0_eq_zero h0]
      decide
    simp only [hc, ↓reduceIte, lbl hp (j := 37) rfl] at hpc1
    have r9 := run_b9
    rw [after_eq run_b1] at r9
    refine exec_at (infix_of b9_in_code (by simp [b9]) hp) r9 hwf hpc1 hm1 fun st2 hm2 hpc2 ↦ ?_
    rw [← after_eq r9] at hm2
    have w9 := b9_writes
    have m9 := b9_mem
    rw [after_eq run_b1] at w9 m9
    obtain ⟨hret, hsv⟩ := hM.fr.exit hm2 hwf (by decide)
    refine .done _ ⟨by simp only [PcOk] at hpc2; rw [hpc2, hret], post_of hR0 ?_ hM.fr.same ?_ hsv⟩
    · rw [rdDigest_none (hnone h0)]
      have hw := hm2.bytesAt_write (r := 1) (o := 0) (n := 8) (b := m0.regs.X0.toBitVec) (sz := 40)
        rfl (by omega) (v := .lit 0) w9
      rw [byteOf_range, NativeRustcVm.addr_add_zero] at hw
      exact hw
    · have := Match.sameOutside_in hm2 hwf (r0 := 1) (o := 0) (n := 40) rfl (by omega)
        m9
      rwa [NativeRustcVm.addr_add_zero] at this
  · have hc : (SBool.not (SBool.cmp .eq .W64 (.reg .X0) (.lit 1))).eval (midEnv m0 st.data) =
        false := by
      simp only [SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, Env.ofMachine_regs, x0_eq_one h1]
      decide
    rw [hc] at hpc1
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
    refine cont h1 st1 hpc1 ⟨Fr.ofBlock hM.fr hm hm1 hwf rfl rfl rfl
      (fun r hr ↦ ⟨.reg r, by simp [keep] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl,
        by simp [keep] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl⟩),
      (Match.reg_eq (r := .X19) hm hm1 rfl rfl).trans hM.x19,
      (Match.reg_eq (r := .X20) hm hm1 rfl rfl).trans hM.x20⟩ hd1 fun r hr ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl

/-- **A read's call** (`b2`, `b4`, `b6`): `Reader::le` for eight bytes from the reader (X20). -/
theorem call_step (hp : Placed code k) (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    {ds : List Directive} {j : Nat} (hds : ds.IsInfixAt code j) (hne : ds ≠ []) {S' : SState}
    (hrun : exec ds callS = some (S', .call NativeRustcVmArm.Vm.ReaderLe.entryLabel))
    (h0 : S'.reg .X0 = some (.reg .X20)) (h1 : S'.reg .X1 = some (.lit 8)) (hmem : S'.mem = [])
    (hsp : S'.sp = .ptr 0 0) (h19 : S'.reg .X19 = some (.ptr 1 0))
    (h20 : S'.reg .X20 = some (.reg .X20)) (hk : ∀ r ∈ keep, S'.reg r = some (.reg r))
    {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} (g : Geo m0 bp B.length)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hM : Mid m0 st.data)
    (hR : ReaderAt st.data.dmem m0.regs.X1.toBitVec bp B c) {R : MachineState → Prop}
    (cont : ∀ m2, Mid m0 m2 → (∀ r, calleeSaved r = true → ∀ v, S'.reg r = some v →
      (m2.regs.getXReg r).toBitVec = v.eval (midEnv m0 st.data)) →
      ReadRes m0.regs.X1.toBitVec bp B c m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + j + ds.length)⟩) :
    Eventually (step1 Host.exe) R st := by
  have hwf := midEnv_wf g hM
  have hm := midEnv_match g hM
  refine exec_at (infix_of hds hne hp) hrun hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem
  have hM1 : Mid m0 st1.data :=
    ⟨Fr.ofBlock hM.fr hm hm1 hwf rfl hmem hsp (fun r hr ↦ ⟨.reg r, by
        simp [keep] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, hk r hr⟩),
      (Match.reg_eq (r := .X19) hm hm1 rfl h19).trans hM.x19,
      (Match.reg_eq (r := .X20) hm hm1 rfl h20).trans hM.x20⟩
  have hx0 : st1.data.regs.X0 = m0.regs.X1 := by
    rw [← hM.x20]
    exact UInt64.toBitVec_inj.mp ((hm1.regs .X0 _ h0).trans rfl)
  have hx1 : st1.data.regs.X1.toNat = 8 := by
    have := hm1.regs .X1 _ h1
    show (st1.data.regs.getXReg .X1).toBitVec.toNat = 8
    rw [this]
    rfl
  refine le_call hle g hM1 (by rw [hd1]; exact hR) hx0 hx1 hpc1 fun m2 hM2 hcs hres ↦
    cont m2 hM2 (fun r hr v hv ↦ ?_) hres
  rw [hcs r hr]
  exact hm1.regs r v hv

/-- **All four read** (`b8`): the tag `1`, the digest's words, the reader past them. -/
theorem finish (hp : Placed code k) {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
    (g : Geo m0 bp B.length) (hR0 : ReaderAt m0.dmem m0.regs.X1.toBitVec bp B c)
    (hfit : c + 32 ≤ B.length) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReaderDigest.b8Offset))
    (hM : Mid m0 st.data) (hR : ReaderAt st.data.dmem m0.regs.X1.toBitVec bp B (c + 32))
    (h22 : st.data.regs.getXReg .X22 = leAt B c 8) (h23 : st.data.regs.getXReg .X23 = leAt B (c + 8) 8)
    (h21 : st.data.regs.getXReg .X21 = leAt B (c + 16) 8)
    (h1 : st.data.regs.getXReg .X1 = leAt B (c + 24) 8) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hwf := midEnv_wf g hM
  have hm := midEnv_match g hM
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8c hwf hpc hm fun st2 hm2 hpc2 ↦ ?_
  rw [← after_eq run_b8c] at hm2
  obtain ⟨hret, hsv⟩ := hM.fr.exit hm2 hwf (by decide)
  have hs := Match.sameOutside_in hm2 hwf (r0 := 1) (o := 0) (n := 40) rfl (by omega) b8_mem
  rw [NativeRustcVm.addr_add_zero] at hs
  have hw : ∀ (o : Nat) (v : Sym), o + 8 ≤ 40 → (∀ i < 8, findWrite 1 (o + i) (after b8 callS).mem = some (v, i)) →
      WordAt st2.data.dmem (m0.regs.X0.toBitVec + BitVec.ofNat 64 o)
        (UInt64.ofBitVec (v.eval (midEnv m0 st.data))) := fun o v ho hf ↦ by
    have := hm2.bytesAt_write (r := 1) (o := o) (n := 8) (b := m0.regs.X0.toBitVec) (sz := 40) rfl ho hf
    rwa [byteOf_range] at this
  refine .done _ ⟨by simp only [PcOk] at hpc2; rw [hpc2, hret], post_of hR0 ?_ hM.fr.same hs hsv⟩
  simp only [rdDigest, hfit, ↓reduceIte]
  refine ⟨?_, ?_, reader_frame g hR (NativeRustcVm.SameOutside.mono hs fun _ h ↦ .inr h)⟩
  · have := hw 0 (.lit 1) (by omega) fun i hi ↦ (b8_writes i hi).1
    rwa [NativeRustcVm.addr_add_zero] at this
  · have e : ∀ x : XReg, UInt64.ofBitVec ((Sym.reg x).eval (midEnv m0 st.data)) = st.data.regs.getXReg x :=
      fun _ ↦ rfl
    have w0 := hw 8 (.reg .X22) (by omega) fun i hi ↦ (b8_writes i hi).2.1
    have w1 := hw 16 (.reg .X23) (by omega) fun i hi ↦ (b8_writes i hi).2.2.1
    have w2 := hw 24 (.reg .X21) (by omega) fun i hi ↦ (b8_writes i hi).2.2.2.1
    have w3 := hw 32 (.reg .X1) (by omega) fun i hi ↦ (b8_writes i hi).2.2.2.2
    rw [e, h22] at w0
    rw [e, h23] at w1
    rw [e, h21] at w2
    rw [e, h1] at w3
    exact wordsAt4 w0 w1 w2 w3

omit [Host] in
theorem regs_eq {m m' : MachineData} {r r' : XReg}
    (h : (m'.regs.getXReg r).toBitVec = (m.regs.getXReg r').toBitVec) :
    m'.regs.getXReg r = m.regs.getXReg r' := UInt64.toBitVec_inj.mp h

/-- **`Reader::digest` meets its contract.** -/
theorem readerDigest_spec (hp : Placed code k)
    (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost) :
    Spec (Labels.label NativeRustcVmArm.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost := by
  intro m0 hpre
  obtain ⟨-, -, bp, B, c, hR, -⟩ := id hpre
  have g := geo_of hpre hR
  rw [lbl hp (j := 0) (l := NativeRustcVmArm.Vm.ReaderDigest.entryLabel) rfl]
  have hal : (base m0 48).toNat % 16 = 0 := by
    rw [Ring.base_toNat g.st.2.1]; have := g.st.1; omega
  let env0 := Env.ofMachine m0 [(base m0 48, 48)]
  have hwf0 : env0.WF :=
    Env.wf_of ⟨⟨g.st.2.2, Ring.base_noWrap g.st.2.1⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match env0 entryS m0 := match_ofMachine ⟨rfl, fun _ ↦ hal, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]
        rw [show BitVec.ofInt 64 48 = BitVec.ofNat 64 48 from rfl]
        exact Ring.base_add_eq.symm) trivial trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun s1 hm1 hpc1 ↦ ?_
  rw [← after_eq run_b0] at hm1
  have hM1 : Mid m0 s1.data :=
    ⟨Fr.ofPrologue g.st.2.1 (Nat.le_refl _) hm1 hwf0 (by decide) (by decide +kernel) (by decide)
      (by decide +kernel) (by decide),
      UInt64.toBitVec_inj.mp (hm1.regs .X19 (.reg .X0) (by decide)),
      UInt64.toBitVec_inj.mp (hm1.regs .X20 (.reg .X1) (by decide))⟩
  have hs1 := Match.sameOutside_in hm1 hwf0 (r0 := 0) (o := 0) (n := 48) rfl (by omega)
    (by decide +kernel)
  rw [NativeRustcVm.addr_add_zero] at hs1
  have hR1 : ReaderAt s1.data.dmem m0.regs.X1.toBitVec bp B c :=
    reader_frame g hR (NativeRustcVm.SameOutside.mono hs1 fun _ h ↦ .inl h)
  have hx0 : s1.data.regs.X0 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X0 (.reg .X1) (by decide))
  have hx1 : s1.data.regs.X1.toNat = 8 := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = 8
    rw [hm1.regs .X1 (.lit 8) (by decide)]; rfl
  refine le_call hle g hM1 hR1 hx0 hx1 hpc1 fun m2 hM2 _ hres2 ↦ ?_
  -- read 1, checked at `b1`
  rcases readRes_cases hres2 with ⟨h20, hf0⟩ | ⟨h21, hv0, hR2, hf0⟩
  · exact check hp b1_in_code (by simp [b1]) rfl rfl g hR (by simpa only [b0Offset, Nat.add_zero, Nat.zero_add] using congrArg (fun j => Host.addrOf (k + j)) b0_next) hM2 (.inl h20)
      (fun _ ↦ by omega) fun h ↦ by rw [h20] at h; cases h
  refine check hp b1_in_code (by simp [b1]) rfl rfl g hR
    (by simpa only [b0Offset, Nat.add_zero, Nat.zero_add] using congrArg (fun j => Host.addrOf (k + j)) b0_next) hM2 (.inr h21) (fun h ↦ by
    rw [h21] at h; cases h) fun _ s3 hpc3 hM3 hd3 hr3 ↦ ?_
  refine call_step hp hle b2_in_code (by simp [b2]) run_b2 rfl rfl rfl rfl rfl rfl
    (by decide) g hpc3 hM3 (by rw [hd3]; exact hR2) fun m4 hM4 hcs4 hres4 ↦ ?_
  have h22 : m4.regs.getXReg .X22 = leAt B c 8 :=
    (regs_eq (hcs4 .X22 rfl _ rfl)).trans ((hr3 .X1 (by simp)).trans hv0)
  rcases readRes_cases hres4 with ⟨h40, hf1⟩ | ⟨h41, hv1, hR4, hf1⟩
  · exact check hp b3_in_code (by simp [b3]) (run_b3.trans run_b1.symm) rfl g hR rfl hM4 (.inl h40)
      (fun _ ↦ by omega) fun h ↦ by rw [h40] at h; cases h
  refine check hp b3_in_code (by simp [b3]) (run_b3.trans run_b1.symm) rfl g hR rfl hM4 (.inr h41)
    (fun h ↦ by rw [h41] at h; cases h) fun _ s5 hpc5 hM5 hd5 hr5 ↦ ?_
  refine call_step hp hle b4_in_code (by simp [b4]) run_b4 rfl rfl rfl rfl rfl rfl
    (by decide) g hpc5 hM5 (by rw [hd5]; exact hR4) fun m6 hM6 hcs6 hres6 ↦ ?_
  have h22' : m6.regs.getXReg .X22 = leAt B c 8 :=
    (regs_eq (hcs6 .X22 rfl _ rfl)).trans ((hr5 .X22 (by simp)).trans h22)
  have h23 : m6.regs.getXReg .X23 = leAt B (c + 8) 8 :=
    (regs_eq (hcs6 .X23 rfl _ rfl)).trans ((hr5 .X1 (by simp)).trans hv1)
  rcases readRes_cases hres6 with ⟨h60, hf2⟩ | ⟨h61, hv2, hR6, hf2⟩
  · exact check hp b5_in_code (by simp [b5]) (run_b5.trans run_b1.symm) rfl g hR rfl hM6 (.inl h60)
      (fun _ ↦ by omega) fun h ↦ by rw [h60] at h; cases h
  refine check hp b5_in_code (by simp [b5]) (run_b5.trans run_b1.symm) rfl g hR rfl hM6 (.inr h61)
    (fun h ↦ by rw [h61] at h; cases h) fun _ s7 hpc7 hM7 hd7 hr7 ↦ ?_
  refine call_step hp hle b6_in_code (by simp [b6]) run_b6 rfl rfl rfl rfl rfl rfl
    (by decide) g hpc7 hM7 (by rw [hd7]; exact hR6) fun m8 hM8 hcs8 hres8 ↦ ?_
  have h22'' : m8.regs.getXReg .X22 = leAt B c 8 :=
    (regs_eq (hcs8 .X22 rfl _ rfl)).trans ((hr7 .X22 (by simp)).trans h22')
  have h23' : m8.regs.getXReg .X23 = leAt B (c + 8) 8 :=
    (regs_eq (hcs8 .X23 rfl _ rfl)).trans ((hr7 .X23 (by simp)).trans h23)
  have h21' : m8.regs.getXReg .X21 = leAt B (c + 16) 8 :=
    (regs_eq (hcs8 .X21 rfl _ rfl)).trans ((hr7 .X1 (by simp)).trans hv2)
  rcases readRes_cases hres8 with ⟨h80, hf3⟩ | ⟨h81, hv3, hR8, hf3⟩
  · exact check hp b7_in_code (by simp [b7]) (run_b7.trans run_b1.symm) rfl g hR rfl hM8 (.inl h80)
      (fun _ ↦ by omega) fun h ↦ by rw [h80] at h; cases h
  refine check hp b7_in_code (by simp [b7]) (run_b7.trans run_b1.symm) rfl g hR rfl hM8 (.inr h81)
    (fun h ↦ by rw [h81] at h; cases h) fun _ s9 hpc9 hM9 hd9 hr9 ↦ ?_
  refine finish hp g hR (by omega) hpc9 hM9 (by rw [hd9]; exact hR8) ((hr9 .X22 (by simp)).trans h22'')
    ((hr9 .X23 (by simp)).trans h23') ((hr9 .X21 (by simp)).trans h21') ((hr9 .X1 (by simp)).trans hv3)

end

end NativeRustcVmArm.Wire.ReaderDigest
