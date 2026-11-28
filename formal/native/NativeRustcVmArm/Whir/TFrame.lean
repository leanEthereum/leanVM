module

public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Whir.Block
public import NativeRustcVmArm.Spec.Whir
public import NativeRustcVmArm.Sumcheck.Common
public import NativeRustcVm.Whir.Sample
public import NativeRustcVm.Transcript.Update

/-!
# Calls from a frame holding a `TState`

`TCtx m0 F N t a outs`: the entry `m0` of a function keeping a `F`-byte frame of its `N` bytes of
stack, with the `TState` at `t` (reading the decoded area `a`) among its outputs `outs`, which are
apart from the frame, the round constants and the decoded area. In a state of the frame (`Fr`) a
callee using `N'` bytes below the frame gets its stack (`stackOk`), the round constants (`rcAt`),
the `TState`'s footprint (`tstateOk`), an output in the frame (`localOk`) or among the caller's
(`outOk`). `Fr.callW`: a call whose writes are its stack, a range of the frame off the slots, and
the outputs. `tsqueeze`: `SpongeW::squeeze` on the `TState`'s sponge.
-/

namespace NativeRustcVmArm.Whir

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring

public section

/-- **A call** whose writes are its stack (`N'` bytes below the frame), the frame's `n` bytes at
`o` (off the slots), and the outputs: the frame kept. -/
theorem _root_.NativeRustcVmArm.Ring.Fr.callW [Host] {m0 : MachineData} {F N : Nat}
    {slots : List (Nat × XReg)} {keep : List XReg} {outs : BitVec 64 → Prop} {l : Label}
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop} {N' : Nat}
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (h : Fr m0 F N slots keep outs st.data) (hN : N ≤ m0.regs.SP.toNat) (hle : F + N' ≤ N)
    (hkeep : ∀ r ∈ keep, calleeSaved r = true) (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q) {o n : Nat} (hon : o + n ≤ F)
    (hos : ∀ p ∈ slots, o + n ≤ p.1 ∨ p.1 + 8 ≤ o) (hspec : Spec (Labels.label l) P Q)
    (hQ : ∀ m m', Q m m' → SameOutside m.dmem m'.dmem (fun q ↦
      InRange (stackBelow m N') N' q ∨ InRange (base m0 F + BitVec.ofNat 64 o) n q ∨ outs q) ∧
      Saved m m')
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (cont : ∀ m2, Fr m0 F N slots keep outs m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Eventually.bind (Spec.apply hspec hpc.1 hP) fun ⟨m2, pc⟩ ⟨hpc', hq⟩ ↦ by
    simp only at hpc' hq
    rw [hpc', hpc.2]
    obtain ⟨hs, hS⟩ := hQ _ _ hq
    have hsb := stackBelow_eq h.sp (N' := N') (by omega)
    have hnw : NoWrap (base m0 (F + N')) N' := by
      unfold NoWrap; rw [base_toNat (by omega)]; have := m0.regs.SP.toNat_lt; omega
    have hnwN := base_noWrap (m0 := m0) (F := N) hN
    have hF := base_noWrap (m0 := m0) (F := F) (by omega)
    have hbF := base_toNat (m0 := m0) (F := F) (by omega)
    have hlo : NoWrap (base m0 F + BitVec.ofNat 64 o) n := NativeRustcVm.NoWrap.sub hF hon
    refine cont m2 (h.step hS.2.1 (fun r hr ↦ hS.1 r (hkeep r hr)) hS.2.2 hs (fun q hq ↦ ?_) ?_)
      hq hS.1
    · rcases hq with hq | hq | hq
      · left
        rw [hsb, Sym.inRange_iff hnw] at hq
        rw [Sym.inRange_iff hnwN, base_toNat hN]
        rw [base_toNat (by omega)] at hq
        omega
      · left
        have := NativeRustcVm.InRange.of_sub hq hF hon
        rw [NativeRustcVm.inRange_iff hF] at this
        rw [Sym.inRange_iff hnwN, base_toNat hN]
        rw [hbF] at this
        omega
      · exact .inr hq
    · intro p hp i hi hq
      have hp8 := hsl p hp
      have hq' : base m0 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i =
          base m0 F + BitVec.ofNat 64 (p.1 + i) := NativeRustcVm.addr_add_add _ _ _
      have hin : InRange (base m0 F) F (base m0 F + BitVec.ofNat 64 (p.1 + i)) :=
        NativeRustcVm.inRange_add (by omega) (by unfold NoWrap at hF; omega)
      rw [hq'] at hq
      rcases hq with hq | hq | hq
      · rw [hsb, Sym.inRange_iff hnw] at hq
        rw [Sym.inRange_iff hF] at hin
        rw [base_toNat (by omega)] at hq
        rw [hbF] at hin
        omega
      · rw [Sym.inRange_iff hlo, NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hF; omega),
          NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hF; omega)] at hq
        rcases hos p hp with h1 | h1 <;> omega
      · exact hfr _ hq hin

section
variable [Labels]

/-- **A function's context** with a `TState` at `t`. -/
structure TCtx (m0 : MachineData) (F N : Nat) (t : BitVec 64) (a : DecArea)
    (outs : BitVec 64 → Prop) : Prop where
  stack : StackOk m0 N
  rc : RcAt m0 N
  tok : TStateOk m0 t a N
  fp : Footprint m0.dmem t a
  hF : F ≤ N
  h16 : F % 16 = 0
  rc_outs : ∀ q, outs q → ¬InRange rcAddr 192 q
  dec_outs : ∀ q, outs q → ¬InRange a.words (8 * a.len) q
  t_outs : ∀ q, InRange t tstateBytes q → outs q
  frame_outs : ∀ q, outs q → ¬InRange (base m0 F) F q

namespace TCtx

variable {m0 : MachineData} {F N : Nat} {t : BitVec 64} {a : DecArea} {outs : BitVec 64 → Prop}
  {slots : List (Nat × XReg)} {keep : List XReg} {st : MachineData}

theorem hN (c : TCtx m0 F N t a outs) : N ≤ m0.regs.SP.toNat := c.stack.2.1

theorem stackOk (c : TCtx m0 F N t a outs) (h : Fr m0 F N slots keep outs st) {N' : Nat}
    (hle : F + N' ≤ N) : StackOk st N' := h.stackOk c.stack c.h16 hle

theorem rcAt (c : TCtx m0 F N t a outs) (h : Fr m0 F N slots keep outs st) {N' : Nat}
    (hle : F + N' ≤ N) : RcAt st N' := by
  have hrc := c.rc
  have hN := c.hN
  refine Sumcheck.RcAt.sub hrc h.sp hle hN fun p hp ↦ h.same p fun hq ↦ ?_
  have hnrc : NoWrap rcAddr 192 := hrc.2.1
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange hrc.2.2 hnrc (base_noWrap hN) hp hq
  · exact c.rc_outs _ hq hp

theorem tstateOk (c : TCtx m0 F N t a outs) (h : Fr m0 F N slots keep outs st) {N' : Nat}
    (hle : F + N' ≤ N) : TStateOk st t a N' :=
  ⟨h.apart c.hN c.tok.1 hle, h.apart c.hN c.tok.2.1 hle, c.tok.2.2⟩

/-- An output among the caller's. -/
theorem outOk (c : TCtx m0 F N t a outs) (h : Fr m0 F N slots keep outs st) {N' : Nat}
    (hle : F + N' ≤ N) {o : BitVec 64} {n : Nat} (ho : OutOk m0 t a o n N) : OutOk st t a o n N' :=
  ⟨fun i hi ↦ h.kept _ (ho.1 i hi), ho.2.1, ho.2.2.1, ho.2.2.2.1, h.apart c.hN ho.2.2.2.2.1 hle,
    ho.2.2.2.2.2⟩

/-- An output in the frame, `n` bytes at `o`. -/
theorem localOk (c : TCtx m0 F N t a outs) (h : Fr m0 F N slots keep outs st) {N' : Nat}
    (hle : F + N' ≤ N) {o n : Nat} (hon : o + n ≤ F) :
    OutOk st t a (base m0 F + BitVec.ofNat 64 o) n N' := by
  have hN := c.hN
  have hbF := base_toNat (m0 := m0) (F := F) (by have := c.hF; omega)
  have hbN : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
  have hF := base_noWrap (m0 := m0) (F := F) (by have := c.hF; omega)
  have hlo : (base m0 F + BitVec.ofNat 64 o).toNat = m0.regs.SP.toNat - F + o := by
    have := m0.regs.SP.toNat_lt
    rw [NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hF; omega), hbF]
  have hsb : (stackBelow st N').toNat = m0.regs.SP.toNat - F - N' := by
    rw [stackBelow_eq h.sp (N' := N') (by omega), base_toNat (by omega)]; omega
  obtain ⟨hto, hda, -⟩ := c.tok
  have hrc := c.rc.2.2
  unfold Apart at hto hda hrc
  rw [hbN] at hto hda hrc
  refine ⟨fun i hi ↦ ?_, NativeRustcVm.NoWrap.sub hF hon, ?_, ?_, ?_, ?_⟩
  · have := h.kept _ (frame_mapped c.stack c.hF (o + i) (by omega))
    rwa [← NativeRustcVm.addr_add_add] at this
  all_goals unfold Apart
  all_goals rw [hlo]
  · omega
  · omega
  · rw [hsb]; omega
  · omega

end TCtx

end

/-- A contract with a condition on the entry carried to the exit. -/
theorem spec_with [NativeRustcArm.Host] {e : Int64} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} (h : Spec e P Q) (C : MachineData → Prop) :
    Spec e (fun m ↦ P m ∧ C m) (fun m m' ↦ Q m m' ∧ C m) := by
  intro m hpc
  exact Eventually.mono (h m hpc.1) fun _ hh ↦ ⟨hh.1, hh.2, hpc.2⟩

theorem sponge_le' : spongeBytes ≤ tstateBytes := by decide

/-- **`SpongeW::squeeze` on the `TState`'s sponge**: the challenge `(sq s).1` in X0, X1, the
`TState` then `(sq s).2`. -/
theorem tsqueeze [Host] {m0 : MachineData} {F N : Nat} {t : BitVec 64} {a : DecArea}
    {outs : BitVec 64 → Prop} {slots : List (Nat × XReg)} {keep : List XReg}
    (c : TCtx m0 F N t a outs)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hf : Fr m0 F N slots keep outs st.data) (hle : F + squeezeStack ≤ N)
    (hkeep : ∀ r ∈ keep, calleeSaved r = true) (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel ∧ retOf st.data = next)
    (hx0 : st.data.regs.X0.toBitVec = t) {s : TState} (hts : TStateAt st.data.dmem t a s)
    (cont : ∀ m2 : MachineData, Fr m0 F N slots keep outs m2 →
      TStateAt m2.dmem t a (NativeRustcVm.Whir.sq s).2 →
      m2.regs.X0 = (NativeRustcVm.Whir.sq s).1.c0 → m2.regs.X1 = (NativeRustcVm.Whir.sq s).1.c1 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦ InRange t spongeBytes q ∨
        InRange (stackBelow st.data squeezeStack) squeezeStack q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hN := c.hN
  have hfp := hts.footprint
  have htok := c.tstateOk hf hle
  have hnwt : NoWrap t spongeBytes := NativeRustcVm.NoWrap.mono hfp.1.2 sponge_le'
  have hnws : NoWrap (stackBelow st.data squeezeStack) squeezeStack := by
    rw [stackBelow_eq hf.sp (by have := c.hF; omega)]
    exact NativeRustcVm.NoWrap.mono (base_noWrap (m0 := m0) (F := F + squeezeStack) (by omega))
      (by omega)
  have hpre : SqueezePre s.sponge st.data := by
    have sl := sponge_le'
    refine ⟨c.stackOk hf hle, c.rcAt hf hle, ⟨?_, by rw [hx0]; exact hnwt, ?_, ?_⟩, ?_⟩
    · rw [hx0]; exact NativeRustcVm.Mapped.mono hfp.1.1 sl
    · rw [hx0]
      exact NativeRustcVm.Apart.mono htok.1 (Nat.le_refl _) (by omega) (Nat.le_refl _)
        (Nat.le_refl _)
    · rw [hx0]
      exact NativeRustcVm.Apart.mono htok.2.2 (Nat.le_refl _) (by omega) (Nat.le_refl _)
        (Nat.le_refl _)
    · rw [hx0]; exact hts.sponge
  refine Fr.leaf hf hN hle hkeep hsl c.frame_outs
    (spec_with (hsq s.sponge) fun m ↦ m.regs.X0.toBitVec = t) (fun m m' hq ↦ ?_) hpc ⟨hpre, hx0⟩
    fun m2 hf2 hq hcs ↦ ?_
  · obtain ⟨⟨-, -, -, hs, hsv⟩, hx⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rcases hq with hq | hq
    · right
      rw [hx] at hq
      exact c.t_outs _ (NativeRustcVm.InRange.mono hq hnwt hfp.1.2 (Nat.le_refl _)
        (Nat.add_le_add_left sponge_le' _))
    · exact Or.inl hq
  · obtain ⟨⟨h0, h1, hsp, hs, hsv⟩, -⟩ := hq
    rw [hx0] at hsp hs
    refine cont m2 hf2 ?_ h0 h1 hcs hs
    refine hts.with_sponge (R := fun q ↦ InRange (stackBelow st.data squeezeStack) squeezeStack q)
      hsv.2.2 (fun q hq ↦ ⟨?_, ?_⟩) (NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_) hsp
    · exact NativeRustcVm.Apart.not_inRange (NativeRustcVm.Apart.symm htok.1) hnws hfp.1.2 hq
    · exact NativeRustcVm.Apart.not_inRange (NativeRustcVm.Apart.symm htok.2.1) hnws
        hfp.2.1.2 hq
    · rcases hq with hq | hq
      · left
        obtain ⟨i, hi, rfl⟩ := NativeRustcVm.InRange.exists hq
        exact ⟨i, by have := sponge_le'; omega, hi, rfl⟩
      · exact Or.inr hq

/-- **Frame bytes across a call** writing its stack, another range of the frame and the
outputs. -/
theorem _root_.NativeRustcVmArm.Ring.Fr.bytes_keep {m0 : MachineData} {F N : Nat}
    {slots : List (Nat × XReg)} {keep : List XReg} {outs : BitVec 64 → Prop} {st : MachineData}
    (h : Fr m0 F N slots keep outs st) (hN : N ≤ m0.regs.SP.toNat)
    (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q) {N' o' n' : Nat} (hle : F + N' ≤ N)
    (ho' : o' + n' ≤ F)
    {d' : Mem 64} (hs : SameOutside st.dmem d' fun q ↦ InRange (stackBelow st N') N' q ∨
      InRange (base m0 F + BitVec.ofNat 64 o') n' q ∨ outs q)
    {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ F)
    (hd : o + bs.length ≤ o' ∨ o' + n' ≤ o)
    (hb : NativeRustcVm.BytesAt st.dmem (base m0 F + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d' (base m0 F + BitVec.ofNat 64 o) bs := by
  have hF := base_noWrap (m0 := m0) (F := F) (by omega)
  have hbF := base_toNat (m0 := m0) (F := F) (by omega)
  have hsp := m0.regs.SP.toNat_lt
  refine hb.of_sameOutside hs fun i hi hq ↦ ?_
  rw [NativeRustcVm.addr_add_add] at hq
  have hq0 : (base m0 F + BitVec.ofNat 64 (o + i)).toNat = m0.regs.SP.toNat - F + (o + i) := by
    rw [NativeRustcVm.toNat_add_ofNat (by omega), hbF]
  rcases hq with hq | hq | hq
  · have hnw : NoWrap (base m0 (F + N')) N' := by
      unfold NoWrap; rw [base_toNat (by omega)]; omega
    rw [stackBelow_eq h.sp (N' := N') (by omega), Sym.inRange_iff hnw, base_toNat (by omega),
      hq0] at hq
    omega
  · have hlo : NoWrap (base m0 F + BitVec.ofNat 64 o') n' := NativeRustcVm.NoWrap.sub hF ho'
    rw [Sym.inRange_iff hlo, NativeRustcVm.toNat_add_ofNat (by omega), hbF, hq0] at hq
    omega
  · exact hfr _ hq (by
      rw [Sym.inRange_iff hF, hq0, hbF]; omega)

/-- The writes of a block: in region `r` apart from `[o, o + n)`, or in another region within its
size. -/
@[expose] def missAt (S : SState) (r o n : Nat) : Bool :=
  S.mem.all fun w ↦ (w.r == r && (decide (w.off + w.n ≤ o) || decide (o + n ≤ w.off))) ||
    (w.r != r && match S.regions[w.r]? with
      | some (sz, _) => decide (w.off + w.n ≤ sz)
      | none => false)

/-- The writes of a block missing `[o, o + n)` of the frame (region 0). -/
abbrev missFrame (S : SState) (o n : Nat) : Bool := missAt S 0 o n

/-- **Bytes of a region across a block** whose writes miss them. -/
theorem bytes_region [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hwf : env.WF) {r : Nat} {b : BitVec 64} {F : Nat} (h0 : env.regions[r]? = some (b, F))
    {o n : Nat} (hmem : missAt S r o n = true) (ho : o + n ≤ F) {bs : List UInt8}
    (hl : bs.length = n) (hb : NativeRustcVm.BytesAt env.mem0 (b + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt m.dmem (b + BitVec.ofNat 64 o) bs := by
  have hnw := hwf.noWrap r b F h0
  refine hb.of_sameOutside (hm.sameOutside hwf) fun i hi ⟨w, hw, b', sz, hb', h1, h2⟩ ↦ ?_
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)] at h1 h2
  simp only [missAt, List.all_eq_true] at hmem
  have := hmem w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    bne_iff_ne, ne_eq] at this
  rcases this with ⟨hr, hd⟩ | ⟨hr, hsz⟩
  · rw [hr, h0] at hb'
    cases hb'
    omega
  · split at hsz
    · rename_i sz' al hreg
      obtain ⟨b'', hb'', -⟩ := hm.regions _ _ _ hreg
      rw [hb'] at hb''
      cases hb''
      have := hwf.disjoint w.r r b' b sz F hr hb' h0
      simp only [decide_eq_true_eq] at hsz
      omega
    · cases hsz

/-- **Frame bytes across a block** whose writes miss them. -/
theorem bytes_block [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hwf : env.WF) {b : BitVec 64} {F : Nat} (h0 : env.regions[0]? = some (b, F)) {o n : Nat}
    (hmem : missFrame S o n = true) (ho : o + n ≤ F) {bs : List UInt8} (hl : bs.length = n)
    (hb : NativeRustcVm.BytesAt env.mem0 (b + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt m.dmem (b + BitVec.ofNat 64 o) bs :=
  bytes_region hm hwf h0 hmem ho hl hb

end

end NativeRustcVmArm.Whir
