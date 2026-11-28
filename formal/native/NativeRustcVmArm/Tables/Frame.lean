module

public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Bus.GkrCommon
public import NativeRustcVmArm.Spec.Tables
public import NativeRustcVm.Tables.Same
public import NativeRustcVm.Transcript.Update

/-!
# The phases' frames and their calls on the transcript

The phases' functions keep a frame `NativeRustcVmArm.Ring.Fr` and take the callees' stacks from
`NativeRustcVmArm.Sumcheck.Ctx`. Here: the callee's stack within the function's and apart from the
frame (`callee_in`); an input apart from the stack and the outputs keeps its bytes (`same_in`);
`SpongeW::squeeze` on the `TState`'s sponge (`squeeze_call`: the challenge in X0, X1, the
`TState` then the model's `sampleChallenge` state).
-/

namespace NativeRustcVmArm.Tables

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

theorem sponge_le : spongeBytes ≤ tstateBytes := by decide

section
variable [Labels] {m0 : MachineData} {t : BitVec 64} {a : DecArea} {N F : Nat}
  {slots : List (Nat × XReg)} {keep : List XReg} {outs : BitVec 64 → Prop}

/-- **A callee's stack** below a state at the frame: within the function's, apart from the
frame. -/
theorem callee_in (c : Ctx m0 t a N F) {m : MachineData} (h : At m0 F m) {Nc : Nat}
    (hle : F + Nc ≤ N) {q : BitVec 64} (hq : InRange (stackBelow m Nc) Nc q) :
    InRange (stackBelow m0 N) N q ∧ ¬InRange (base m0 F) F q := by
  have hspN := c.spN
  have hs := c.spN' h
  have hl := m0.regs.SP.toNat_lt
  have e : (stackBelow m Nc).toNat = m.regs.SP.toNat - Nc :=
    Sumcheck.toNat_stackBelow (by omega)
  have ef : (base m0 F).toNat = m0.regs.SP.toNat - F := base_toNat (by omega)
  rw [Sym.inRange_iff (by rw [e]; omega), e] at hq
  refine ⟨?_, fun hin ↦ ?_⟩
  · rw [Sym.inRange_iff (by rw [c.stk]; omega), c.stk]
    omega
  · rw [Sym.inRange_iff (by rw [ef]; omega), ef] at hin
    omega

/-- The callee's stack does not wrap. -/
theorem callee_noWrap (c : Ctx m0 t a N F) {m : MachineData} (h : At m0 F m) {Nc : Nat}
    (hle : F + Nc ≤ N) : NoWrap (stackBelow m Nc) Nc := by
  have hspN := c.spN
  have hs := c.spN' h
  have hl := m0.regs.SP.toNat_lt
  unfold NoWrap
  rw [Sumcheck.toNat_stackBelow (by omega)]
  omega

omit [Labels] in
/-- A range apart from the callee's stack: none of the callee's stack. -/
theorem not_callee {m : MachineData} {Nc : Nat} (hnw : NoWrap (stackBelow m Nc) Nc) {x : BitVec 64}
    {n : Nat} (hx : NoWrap x n) (hA : Apart x n (stackBelow m Nc) Nc) {q : BitVec 64}
    (hq : InRange (stackBelow m Nc) Nc q) : ¬InRange x n q :=
  NativeRustcVm.Apart.not_inRange (NativeRustcVm.Apart.symm hA) hnw hx hq

end

/-- **An input** apart from the stack and from the outputs keeps its bytes in the frame's
states. -/
theorem same_in {m0 m : MachineData} {F N : Nat} {slots : List (Nat × XReg)} {keep : List XReg}
    {outs : BitVec 64 → Prop} (h : Fr m0 F N slots keep outs m) (hS : StackOk m0 N)
    {x : BitVec 64} {n : Nat} (hna : NoWrap x n) (ha : OffStack m0 x n N)
    (ho : ∀ j < n, ¬outs (x + BitVec.ofNat 64 j)) :
    NativeRustcVm.Layout.Same m0.dmem m.dmem x n :=
  Bus.Fr.bytes_eq h hS hna ha ho

/-- **`SpongeW::squeeze` on the `TState`'s sponge**: the challenge in X0, X1, the `TState` then
`sampleChallenge`'s, nothing else changed but the sponge and the callee's stack. -/
theorem squeeze_call [Host] {m0 : MachineData} {t : BitVec 64} {a : DecArea} {N F : Nat}
    {slots : List (Nat × XReg)} {keep : List XReg} {outs : BitVec 64 → Prop}
    (c : Ctx m0 t a N F)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hf : Fr m0 F N slots keep outs st.data) (hrc : ∀ q, outs q → ¬InRange rcAddr 192 q)
    (hle : F + squeezeStack ≤ N) (hkeep : ∀ r ∈ keep, calleeSaved r = true)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F) (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q)
    (hto : ∀ q, InRange t tstateBytes q → outs q)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel ∧ retOf st.data = next)
    (hx0 : st.data.regs.X0.toBitVec = t) {s : TState} (hts : TStateAt st.data.dmem t a s)
    (cont : ∀ m2 : MachineData, Fr m0 F N slots keep outs m2 →
      TStateAt m2.dmem t a { s with sponge := s.sponge.squeeze.2 } →
      m2.regs.X0 = s.sponge.squeeze.1.c0 → m2.regs.X1 = s.sponge.squeeze.1.c1 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦ InRange t spongeBytes q ∨
        InRange (stackBelow st.data squeezeStack) squeezeStack q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hat := Bus.Gkr.Fr.at_ c hf hrc
  have hfp := hts.footprint
  have htok := c.tstateOk hat hle
  have hnws := callee_noWrap c hat hle
  have hnwt : NoWrap t spongeBytes := NativeRustcVm.NoWrap.mono hfp.1.2 sponge_le
  have hpre : SqueezePre s.sponge st.data := by
    unfold SqueezePre
    rw [hx0]
    exact ⟨c.stackOk hat hle, c.rcAt hat hle, c.spongeOk hat hle, hts.sponge⟩
  refine Bus.Gkr.Fr.callSpec hf c.spN hle hkeep hsl hfr (hsq s.sponge) hpc hpre
    (fun m' hq ↦ ?_) fun m2 hf2 hq hcs ↦ ?_
  · obtain ⟨-, -, -, hs, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rcases hq with hq | hq
    · right
      rw [hx0] at hq
      exact hto q (NativeRustcVm.InRange.mono hq hnwt hfp.1.2 (Nat.le_refl _)
        (by have := sponge_le; omega))
    · exact Or.inl hq
  · obtain ⟨h0, h1, hsp, hs, hsv⟩ := hq
    rw [hx0] at hsp hs
    refine cont m2 hf2 ?_ h0 h1 hcs hs
    refine hts.with_sponge (R := fun q ↦ InRange (stackBelow st.data squeezeStack) squeezeStack q)
      hsv.2.2 (fun q hq ↦ ⟨not_callee hnws hfp.1.2 htok.1 hq,
        not_callee hnws hfp.2.1.2 htok.2.1 hq⟩)
      (NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_) hsp
    rcases hq with hq | hq
    · left
      obtain ⟨i, hi, rfl⟩ := NativeRustcVm.InRange.exists hq
      exact ⟨i, by have := sponge_le; omega, hi, rfl⟩
    · exact Or.inr hq

/-! ## A new start for the frame

After a call that changed an output, the frame goes on from the entry with the memory of that
state (`reb`): the later steps change no output until the next call that does (`Fr.rebase`); the
entry's contract follows from the pieces (`Saved.rebase`). -/

/-- The entry `m0` with the memory `d` of a later state. -/
@[expose] def reb (m0 : MachineData) (d : DataMem) : MachineData := { m0 with dmem := d }

/-- **The frame from a later state** on, no output changed since. -/
theorem Fr.rebase {m0 m : MachineData} {F N : Nat} {slots : List (Nat × XReg)} {keep : List XReg}
    {outs : BitVec 64 → Prop} (h : Fr m0 F N slots keep outs m) :
    Fr (reb m0 m.dmem) F N slots keep (fun _ ↦ False) m where
  sp := h.sp
  keep := h.keep
  slots := h.slots
  same := fun _ _ ↦ rfl
  kept := fun _ hp ↦ hp

theorem Saved.rebase {m0 m' : MachineData} {d : DataMem} (hk : Kept m0.dmem d)
    (h : Saved (reb m0 d) m') : Saved m0 m' :=
  ⟨h.1, h.2.1, fun p hp ↦ h.2.2 p (hk p hp)⟩

theorem StackOk.rebase {m0 : MachineData} {N : Nat} {d : DataMem} (h : StackOk m0 N)
    (hk : Kept m0.dmem d) : StackOk (reb m0 d) N :=
  ⟨h.1, h.2.1, fun i hi ↦ hk _ (h.2.2 i hi)⟩

/-- **The context** from a later state's memory, the entry's bytes and round constants kept. -/
theorem Ctx.rebase [Labels] {m0 : MachineData} {t : BitVec 64} {a : DecArea} {N F : Nat}
    (c : Ctx m0 t a N F) {d : DataMem} (hk : Kept m0.dmem d)
    (hrc : ∀ p, InRange rcAddr 192 p → d.get? p = m0.dmem.get? p) : Ctx (reb m0 d) t a N F where
  stack := StackOk.rebase c.stack hk
  rc := Sumcheck.RcAt.sub c.rc (m' := reb m0 d) (f := 0) (by simp [reb]) (by omega) c.spN hrc
  tok := c.tok
  fp := ⟨Region.Ok.keeps c.fp.1 hk, Region.Ok.keeps c.fp.2.1 hk, c.fp.2.2⟩
  le := c.le
  al := c.al

/-- An input apart from the stack keeps its bytes in a frame with no output. -/
theorem same_fr {m0 m : MachineData} {F N : Nat} {slots : List (Nat × XReg)} {keep : List XReg}
    (h : Fr m0 F N slots keep (fun _ ↦ False) m) (hS : StackOk m0 N) {x : BitVec 64} {n : Nat}
    (hna : NoWrap x n) (ha : OffStack m0 x n N) : NativeRustcVm.Layout.Same m0.dmem m.dmem x n :=
  same_in h hS hna ha fun _ _ h ↦ h

/-- **The `TState`** in a frame whose outputs are apart from it and its decoded area. -/
theorem tstate_fr [Labels] {m0 m : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} (h : Fr m0 F N slots keep outs m)
    (hS : StackOk m0 N) {t : BitVec 64} {a : DecArea} {s : TState} (htok : TStateOk m0 t a N)
    (ho : ∀ q, outs q → ¬InRange t tstateBytes q ∧ ¬InRange a.words (8 * a.len) q)
    (hts : TStateAt m0.dmem t a s) : TStateAt m.dmem t a s := by
  have hnw : NoWrap (base m0 N) N := base_noWrap hS.2.1
  refine hts.frame h.kept (R := fun q ↦ InRange (base m0 N) N q ∨ outs q) (fun q hq ↦ ?_) h.same
  rcases hq with hq | hq
  · exact ⟨NativeRustcVm.Apart.not_inRange htok.1.symm hnw hts.footprint.1.2 hq,
      NativeRustcVm.Apart.not_inRange htok.2.1.symm hnw hts.footprint.2.1.2 hq⟩
  · exact ho q hq

/-- An output apart from the `TState` and its decoded area misses both. -/
theorem out_not_ts [Labels] {m0 : MachineData} {t : BitVec 64} {a : DecArea} {o : BitVec 64}
    {n N : Nat} {s : TState} {d : DataMem} (hts : TStateAt d t a s) (h : OutOk m0 t a o n N) :
    ∀ q, InRange o n q → ¬InRange t tstateBytes q ∧ ¬InRange a.words (8 * a.len) q :=
  fun _ hq ↦ ⟨NativeRustcVm.Apart.not_inRange h.2.2.1 h.2.1 hts.footprint.1.2 hq,
    NativeRustcVm.Apart.not_inRange h.2.2.2.1 h.2.1 hts.footprint.2.1.2 hq⟩

/-! ## Inputs and the read-only data for a callee -/

/-- **Part of an input**: `k` bytes at offset `o`. -/
theorem ReadIn.sub {m : MachineData} {x : BitVec 64} {n N : Nat} {ws : List NativeRustcVm.Region}
    (h : ReadIn m x n N ws) {o k : Nat} (hk : o < n) (hok : o + k ≤ n) :
    ReadIn m (x + BitVec.ofNat 64 o) k N ws := by
  obtain ⟨⟨hm, hnw⟩, hst, hws⟩ := h
  unfold NoWrap at hnw
  have e : (x + BitVec.ofNat 64 o).toNat = x.toNat + o := NativeRustcVm.toNat_add_ofNat (by omega)
  refine ⟨⟨fun i hi ↦ ?_, by unfold NoWrap; rw [e]; omega⟩, ?_, fun w hw ↦ ?_⟩
  · rw [NativeRustcVm.addr_add_add]; exact hm _ (by omega)
  · exact NativeRustcVm.Apart.mono hst (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)
  · exact NativeRustcVm.Apart.mono (hws w hw) (by omega) (by omega) (Nat.le_refl _)
      (Nat.le_refl _)

/-- **An input for a callee** using `N'` bytes of stack below a state of the frame. -/
theorem ReadIn.fr {m0 m : MachineData} {F N N' : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} (hf : Fr m0 F N slots keep outs m)
    (hS : StackOk m0 N) (hle : F + N' ≤ N) {x : BitVec 64} {n : Nat}
    {ws : List NativeRustcVm.Region} (h : ReadIn m0 x n N ws) : ReadIn m x n N' ws :=
  ⟨Bus.Fr.readable hf h.1, Bus.Fr.offStack hf hS h.2.1 hle, h.2.2⟩

/-- **The read-only data for a callee** below a state of the frame whose outputs are apart from
it. -/
theorem tablesAt_fr [Labels] {m0 m : MachineData} {F N N' : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} (hf : Fr m0 F N slots keep outs m)
    (hS : StackOk m0 N) (hle : F + N' ≤ N) (hT : TablesAt m0 N)
    (ho : ∀ q, outs q → ∀ t : NativeRustcVm.Data.Item,
      ¬InRange (rodataAddr t) t.bytes.length q) : TablesAt m N' := fun t ↦ by
  obtain ⟨hb, hnw, hap⟩ := hT t
  have hN := hS.2.1
  have hnwN : NoWrap (base m0 N) N := base_noWrap hN
  refine ⟨fun i hi ↦ ?_, hnw, ?_⟩
  · rw [hf.same _ fun hq ↦ hq.elim (fun hq ↦ ?_) (fun hq ↦ ho _ hq t ?_)]
    · exact hb i hi
    · exact NativeRustcVm.Apart.not_inRange_add hap hnw hnwN hi hq
    · exact NativeRustcVm.inRange_add hi (by unfold NativeRustcVm.NoWrap at hnw; omega)
  · rw [stackBelow_eq hf.sp (by omega)]
    have h1 := base_toNat (m0 := m0) (F := F + N') (by omega)
    have h2 : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
    unfold NativeRustcVm.Apart at hap ⊢
    omega

/-- A range apart from the read-only data misses it. -/
theorem not_rodata [Labels] {x : BitVec 64} {n : Nat} (hx : NoWrap x n) (h : RodataApart x n)
    (hT : ∀ t : NativeRustcVm.Data.Item, NoWrap (rodataAddr t) t.bytes.length) {q : BitVec 64}
    (hq : InRange x n q) (t : NativeRustcVm.Data.Item) : ¬InRange (rodataAddr t) t.bytes.length q :=
  NativeRustcVm.Apart.not_inRange (h t) hx (hT t) hq

end

end NativeRustcVmArm.Tables
