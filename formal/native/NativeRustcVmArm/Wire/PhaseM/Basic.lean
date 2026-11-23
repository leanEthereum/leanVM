module

public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Wire.PhaseM.Exec
public import NativeRustcVmArm.Wire.PhaseM.Model
public import NativeRustcVmArm.Wire.Frame
public import NativeRustcVmArm.Wire.Common
public import NativeRustcVmArm.Spec.Wire
public import NativeRustcVmArm.Keccak.Common

/-!
# `phase_m`'s places and states

The reader at `r` (X0), the phase's words at `out` (X1, `phaseBytes`), the working area at `w`
(X2, `workBytes`, its parts at `wa o`); the frame (`Frm`, 192 bytes, every callee-saved register
in a slot) in the 1184 bytes of stack the function uses. `Geo`: the places pairwise apart, from
the precondition (`geo_of`). A call of `Reader::le` for four bytes (`le4_call`, its outcome
`Read4` in the model's `rdU32`).
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The prologue's slots. -/
def slots : List (Nat × XReg) := [(96, .X29), (104, .X30), (112, .X28), (120, .X27),
  (128, .X26), (136, .X25), (144, .X24), (152, .X23), (160, .X22), (168, .X21), (176, .X20),
  (184, .X19)]

/-- The reader's address. -/
abbrev rdr (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The phase's address. -/
abbrev outA (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
/-- The working area's address. -/
abbrev wk (m0 : MachineData) : BitVec 64 := m0.regs.X2.toBitVec
/-- Byte `o` of the working area. -/
abbrev wa (m0 : MachineData) (o : Nat) : BitVec 64 := wk m0 + BitVec.ofNat 64 o

/-- The outputs: the phase and the working area. -/
abbrev W (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (outA m0) phaseBytes q ∨ InRange (wk m0) workBytes q

/-- The state between the prologue and the epilogue. -/
abbrev Frm (m0 m : MachineData) : Prop := Fr m0 192 1184 slots [] (outs (rdr m0) (W m0)) m

/-- What `phase_m` reaches. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ PhaseMPost m0 st.data

/-- The environment of the frame. -/
abbrev frEnv (m0 m : MachineData) : Sym.Env := Env.ofMachine m [(base m0 192, 192)]

/-- The environment of the frame and `n` bytes at `a`. -/
abbrev alEnv (m0 m : MachineData) (a : BitVec 64) (n : Nat) : Sym.Env :=
  Env.ofMachine m [(base m0 192, 192), (a, n)]

/-- **The places**, pairwise apart: the stack, the round constants, the reader, its bytes, the
phase, the working area. -/
structure Geo [Labels] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) : Prop where
  st : StackOk m0 1184
  rc : NativeRustcVmArm.RcAt m0 1184
  rNw : NoWrap (rdr m0) 24
  bNw : NoWrap bp B.length
  oOk : Region.Ok m0.dmem ⟨outA m0, phaseBytes⟩
  wOk : Region.Ok m0.dmem ⟨wk m0, workBytes⟩
  cS : NativeRustcVm.Apart rcAddr 192 (base m0 1184) 1184
  cR : NativeRustcVm.Apart rcAddr 192 (rdr m0) 24
  cB : NativeRustcVm.Apart rcAddr 192 bp B.length
  cO : NativeRustcVm.Apart rcAddr 192 (outA m0) phaseBytes
  cW : NativeRustcVm.Apart rcAddr 192 (wk m0) workBytes
  sR : NativeRustcVm.Apart (base m0 1184) 1184 (rdr m0) 24
  sB : NativeRustcVm.Apart (base m0 1184) 1184 bp B.length
  sO : NativeRustcVm.Apart (base m0 1184) 1184 (outA m0) phaseBytes
  sW : NativeRustcVm.Apart (base m0 1184) 1184 (wk m0) workBytes
  rB : NativeRustcVm.Apart (rdr m0) 24 bp B.length
  rO : NativeRustcVm.Apart (rdr m0) 24 (outA m0) phaseBytes
  rW : NativeRustcVm.Apart (rdr m0) 24 (wk m0) workBytes
  bO : NativeRustcVm.Apart bp B.length (outA m0) phaseBytes
  bW : NativeRustcVm.Apart bp B.length (wk m0) workBytes
  oW : NativeRustcVm.Apart (outA m0) phaseBytes (wk m0) workBytes

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

/-- The outcome of a read of four bytes at `c`. -/
def Read4 (r bp : BitVec 64) (B : List UInt8) (c : Nat) (m : MachineData) : Prop :=
  match rdU32 B c with
  | some (v, c') => m.regs.X0 = 1 ∧ m.regs.X1.toNat = v ∧ ReaderAt m.dmem r bp B c'
  | none => m.regs.X0 = 0

end

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

theorem phaseBytes_eq : phaseBytes = 395288 := rfl
theorem workBytes_eq : workBytes = 483584 := rfl
theorem nodesBytes_eq : nodesBytes = 10240 := rfl

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

theorem geo_of [Labels] (h : PhaseMPre m0) (hR : ReaderAt m0.dmem (rdr m0) bp B c) :
    Geo m0 bp B := by
  obtain ⟨hst, hrc, hoOk, hwOk, bp', B', c', hR', hd⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := hR'.unique hR
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hd
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15⟩ := hd
  exact ⟨hst, hrc, hR.ok.2, hR.noWrap, hoOk, hwOk, h1.symm, h6, h7, h8, h9, h2, h3, h4, h5,
    h10, h11, h12, h13, h14, h15.1⟩

theorem base_aligned (hst : StackOk m0 1184) : (base m0 192).toNat % 16 = 0 := by
  rw [Ring.base_toNat (by have := hst.2.1; omega)]; have := hst.1; omega

theorem frEnv_wf (hst : StackOk m0 1184) {m : MachineData} (hfr : Frm m0 m) : (frEnv m0 m).WF :=
  Env.wf_of ⟨⟨fun j hj ↦ hfr.kept _ (Ring.frame_mapped hst (by omega) j hj),
    Ring.base_noWrap (by have := hst.2.1; omega)⟩, trivial⟩ (List.pairwise_singleton _ _)

theorem frEnv_match [Labels] (hst : StackOk m0 1184) {m : MachineData} (hfr : Frm m0 m) :
    Match (frEnv m0 m) frS m :=
  match_ofMachine ⟨rfl, fun _ ↦ base_aligned hst, trivial⟩ (by rw [hfr.sp]; simp [Sym.eval])
    trivial trivial trivial trivial

section
variable [Labels]

theorem Geo.sp (G : Geo m0 bp B) : 1184 ≤ m0.regs.SP.toNat := G.st.2.1

theorem Geo.base_toNat (G : Geo m0 bp B) {F : Nat} (hF : F ≤ 1184) :
    (base m0 F).toNat = m0.regs.SP.toNat - F := Ring.base_toNat (by have := G.sp; omega)

theorem Geo.wNw (G : Geo m0 bp B) : (wk m0).toNat + workBytes ≤ 2 ^ 64 := G.wOk.2

theorem Geo.wa_toNat (G : Geo m0 bp B) {o : Nat} (ho : o < workBytes) :
    (wa m0 o).toNat = (wk m0).toNat + o := by
  have := G.wNw
  exact NativeRustcVm.toNat_add_ofNat (by omega)

/-- **The outputs miss the frame and the stack.** -/
theorem Geo.rgeo (G : Geo m0 bp B) : RGeo m0 1184 (rdr m0) bp B.length (W m0) := by
  have hb := Ring.base_noWrap (m0 := m0) (F := 1184) G.sp
  refine ⟨G.st, G.rNw, G.bNw, G.sR, G.sB, G.rB, fun q hq ↦ ?_, fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · rcases hq with h | h
    · exact NativeRustcVm.Apart.not_inRange G.sO.symm G.oOk.2 hb h
    · exact NativeRustcVm.Apart.not_inRange G.sW.symm G.wOk.2 hb h
  · rcases hq with h | h
    · exact NativeRustcVm.Apart.not_inRange G.rO.symm G.oOk.2 G.rNw h
    · exact NativeRustcVm.Apart.not_inRange G.rW.symm G.wOk.2 G.rNw h
  · rcases hq with h | h
    · exact NativeRustcVm.Apart.not_inRange G.bO.symm G.oOk.2 G.bNw h
    · exact NativeRustcVm.Apart.not_inRange G.bW.symm G.wOk.2 G.bNw h

/-- **The frame and part of the working area**: a well formed environment. -/
theorem Geo.al_wf (G : Geo m0 bp B) {o n : Nat} (hon : o + n ≤ workBytes) (hn : 0 < n)
    {m : MachineData}
    (hfr : Frm m0 m) : (alEnv m0 m (wa m0 o) n).WF := by
  have hst := G.st
  have hb := Ring.base_noWrap (m0 := m0) (F := 192) (by have := G.sp; omega)
  have hw := G.wa_toNat (o := o) (by omega)
  have := G.wNw
  have hbt := G.base_toNat (F := 192) (by omega)
  have hbN := G.base_toNat (F := 1184) le_rfl
  have hsW := G.sW
  refine Env.wf_of ⟨⟨fun j hj ↦ hfr.kept _ (Ring.frame_mapped hst (by omega) j hj), hb⟩,
    ⟨fun j hj ↦ ?_, ?_⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  · rw [NativeRustcVm.addr_add_add]
    exact hfr.kept _ (G.wOk.1 _ (by show o + j < workBytes; have : j < n := hj; omega))
  · show NativeRustcArm.NoWrap _ _
    unfold NativeRustcArm.NoWrap; rw [hw]; omega
  · show NativeRustcArm.Apart _ _ _ _
    unfold NativeRustcArm.Apart
    unfold NativeRustcVm.Apart at hsW
    rw [hbt, hw]
    rw [hbN] at hsW
    omega

/-- A state at an alias of part of the working area, in the frame. -/
theorem Geo.al_match (G : Geo m0 bp B) {o n : Nat} {m : MachineData} (hfr : Frm m0 m)
    {a : Sym} {k : Int} (ha : a.eval (alEnv m0 m (wa m0 o) n) = wa m0 o + BitVec.ofInt 64 k) :
    Match (alEnv m0 m (wa m0 o) n) (alS a n k) m :=
  match_ofMachine ⟨rfl, fun _ ↦ base_aligned G.st, rfl, fun h ↦ absurd h (by decide), trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial ⟨ha, trivial⟩

/-- **The round constants** for a callee using `N'` bytes of stack below the frame. -/
theorem Geo.rcAt (G : Geo m0 bp B) {m : MachineData} (hfr : Frm m0 m) {N' : Nat}
    (hN' : 192 + N' ≤ 1184) : NativeRustcVmArm.RcAt m N' := by
  obtain ⟨hw, hnw, hap⟩ := G.rc
  have hb := Ring.base_noWrap (m0 := m0) (F := 1184) G.sp
  have hbN := G.base_toNat (F := 1184) le_rfl
  refine ⟨NativeRustcVm.BytesAt.of_sameOutside hw hfr.same fun i hi hq ↦ ?_, hnw,
    hfr.apart G.sp hap hN'⟩
  have hi' : i < 192 := by
    rw [show LeanVM.Parameters.keccakRC.flatMap NativeRustcVm.wordBytes = rcBytes from rfl,
      NativeRustcVmArm.Keccak.length_rcBytes] at hi
    exact hi
  have hin : InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i) :=
    NativeRustcVm.inRange_add hi' (by unfold NoWrap at hnw; omega)
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange G.cS hnw hb hin hq
  · rcases hq with hq | hq | hq
    · exact NativeRustcVm.Apart.not_inRange G.cR hnw G.rNw hin
        (NativeRustcVm.InRange.of_sub (o := 16) (m := 8) hq G.rNw (by omega))
    · exact NativeRustcVm.Apart.not_inRange G.cO hnw G.oOk.2 hin hq
    · exact NativeRustcVm.Apart.not_inRange G.cW hnw G.wOk.2 hin hq

/-- A part of the working area is apart from what the area is apart from. -/
theorem Geo.wa_apart (G : Geo m0 bp B) {o n : Nat} (hon : o + n ≤ workBytes) (hn : 0 < n)
    {b : BitVec 64}
    {k : Nat} (h : NativeRustcVm.Apart (wk m0) workBytes b k) :
    NativeRustcVm.Apart (wa m0 o) n b k := by
  have hw := G.wa_toNat (o := o) (by omega)
  unfold NativeRustcVm.Apart at *
  rw [hw]
  omega

theorem Geo.wa_ok (G : Geo m0 bp B) {o n : Nat} (hon : o + n ≤ workBytes) {d : Mem 64}
    (hk : Kept m0.dmem d) : Region.Ok d ⟨wa m0 o, n⟩ := by
  have := G.wNw
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · show (d.get? (wa m0 o + BitVec.ofNat 64 j)).isSome
    rw [NativeRustcVm.addr_add_add]
    exact hk _ (G.wOk.1 _ (by show o + j < workBytes; have : j < n := hj; omega))
  · show (wa m0 o).toNat + n ≤ 2 ^ 64
    by_cases hn : n = 0
    · subst hn; have := (wa m0 o).isLt; omega
    have hw := G.wa_toNat (o := o) (by omega)
    rw [hw]; omega

/-- Two parts of the working area apart. -/
theorem Geo.wa_wa (G : Geo m0 bp B) {o n o' n' : Nat} (h : o + n ≤ workBytes)
    (h' : o' + n' ≤ workBytes) (hle : o + n ≤ o' ∨ o' + n' ≤ o) :
    NativeRustcVm.Apart (wa m0 o) n (wa m0 o') n' :=
  NativeRustcVm.apart_of_le G.wOk.2 h h' hle

/-- **A part of the working area kept**: bytes from `wa o'` survive a change of memory in the
stack below the frame, the reader's cursor, the phase and parts of the working area apart from
them. -/
theorem Geo.keep_wa (G : Geo m0 bp B) {d d' : Mem 64} {R : BitVec 64 → Prop}
    {L : List (Nat × Nat)}
    (hs : NativeRustcVm.SameOutside d d' R) {o' : Nat} {bs : List UInt8}
    (ho' : o' + bs.length ≤ workBytes) (hb : BytesAt d (wa m0 o') bs)
    (hR : ∀ q, R q → InRange (base m0 1184) 1184 q ∨ InRange (rdr m0 + BitVec.ofNat 64 16) 8 q ∨
      InRange (outA m0) phaseBytes q ∨ ∃ p ∈ L, InRange (wa m0 p.1) p.2 q)
    (hL : ∀ p ∈ L, p.1 + p.2 ≤ workBytes ∧ (p.1 + p.2 ≤ o' ∨ o' + bs.length ≤ p.1)) :
    BytesAt d' (wa m0 o') bs := by
  refine NativeRustcVm.BytesAt.of_sameOutside hb hs fun i hi hq ↦ ?_
  have hw := G.wa_toNat (o := o') (by omega)
  have hnw : NoWrap (wa m0 o') bs.length := by
    unfold NoWrap; rw [hw]; have := G.wNw; omega
  have hin : InRange (wa m0 o') bs.length (wa m0 o' + BitVec.ofNat 64 i) :=
    NativeRustcVm.inRange_add hi (by unfold NoWrap at hnw; omega)
  rcases hR _ hq with h | h | h | ⟨p, hp, h⟩
  · exact NativeRustcVm.Apart.not_inRange (G.wa_apart ho' (by omega) G.sW.symm) hnw
      (Ring.base_noWrap G.sp) hin h
  · exact NativeRustcVm.Apart.not_inRange (G.wa_apart ho' (by omega) G.rW.symm) hnw G.rNw hin
      (NativeRustcVm.InRange.of_sub (o := 16) (m := 8) h G.rNw (by omega))
  · exact NativeRustcVm.Apart.not_inRange (G.wa_apart ho' (by omega) G.oW.symm) hnw G.oOk.2 hin h
  · obtain ⟨h1, h2⟩ := hL p hp
    have hpn : NoWrap (wa m0 p.1) p.2 := by
      by_cases hn : p.2 = 0
      · rw [hn] at h; unfold InRange at h; omega
      unfold NoWrap; rw [G.wa_toNat (by omega)]; have := G.wNw; omega
    exact NativeRustcVm.Apart.not_inRange (G.wa_wa ho' h1 (by omega)) hnw hpn hin h

end

variable [Host]

/-- **A call of `Reader::le` for four bytes** from a state of the frame. -/
theorem le4_call (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (G : Geo m0 bp B) {c : Nat} {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : Frm m0 st.data) (hR : ReaderAt st.data.dmem (rdr m0) bp B c)
    (hx0 : st.data.regs.X0.toBitVec = rdr m0) (hx1 : st.data.regs.X1.toNat = 4)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel ∧ retOf st.data = next)
    (cont : ∀ m2, Frm m0 m2 →
      (∀ x, calleeSaved x = true → m2.regs.getXReg x = st.data.regs.getXReg x) →
      SameOutside st.data.dmem m2.dmem (InRange (rdr m0 + BitVec.ofNat 64 16) 8) →
      Read4 (rdr m0) bp B c m2 → Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have g := G.rgeo
  have hN := g.st.2.1
  have hP : ReaderLePre st.data :=
    ⟨hfr.stackOk g.st (by decide) (by unfold readerLeStack; omega), .inl hx1, bp, B, c,
      by rw [hx0]; exact hR⟩
  refine Fr.leaf (N' := readerLeStack) hfr hN (by unfold readerLeStack; omega) (by simp)
    (by decide) (fun q hq ↦ g.not_frame (by omega) hq)
    (Spec.carry hle fun m ↦ m.regs.X0.toBitVec = rdr m0)
    (fun m m' ⟨⟨_, hs, hsv⟩, h0⟩ ↦ ⟨?_, hsv⟩) hpc ⟨hP, hx0⟩ ?_
  · exact NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inr (.inl (by rw [← h0]; exact hq))
  · intro m2 hfr2 ⟨hq, h0⟩ hcs
    refine cont m2 hfr2 hcs (by rw [← h0]; exact hq.2.1) ?_
    have := hq.1 bp B c (by rw [hx0]; exact hR)
    rw [hx1, hx0, rdLe_four] at this
    unfold Read4
    rcases h : rdU32 B c with _ | ⟨v, c'⟩
    · rw [h] at this; exact this
    · rw [h] at this
      obtain ⟨h0, h1, h2⟩ := this
      refine ⟨h0, ?_, h2⟩
      rw [h1]
      exact toNat_toUInt64_of_lt (by have := rdU32_lt h; omega)

end

end NativeRustcVmArm.Wire.PhaseM
