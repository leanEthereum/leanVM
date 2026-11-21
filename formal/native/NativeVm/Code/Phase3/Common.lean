module

public import NativeVm.Code.Contracts
public import NativeVm.Code.Gadgets
public import NativeVm.Field

/-!
# Phase 3's conventions

Phase 3 (`Model.verifyBusBalance`) keeps its intermediate values in parts of `scratchR` (`sreg`):
the slot weights (`wR`), `β` (`betaR`), the GKR point (`pointR`), the trees' values (`treeR`), ...;
each part of the code says which parts it writes.

A part's run from `s` to `s'` is a `Step3 env regs ws s s'`: `rdi` and every register outside
`regs` kept, every word outside the transcript's (`Foot`) and the regions `ws` kept, which words
exist kept. Code that runs no transcript step writes no word of the transcript's either: its runs
are `Wrote env ws s s'` (every word outside `ws` kept), and they keep `CodeRel` (`CodeRel.wrote3`).
A region phase 3 may write is inside `busR`, `claimsR` or `scratchR` (`Ok3`).

The transcript's loops: `readsTo k` reads `r12` scalars into the words from `k` of the working
area (`readsTo_spec`, against `readScalars`), `samplesTo k` samples `r12` challenges there
(`samplesTo_spec`, against `sampleChallenges`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters

/-! ## The scratch's parts -/

/-- Words `off .. off + size` of the scratch. -/
def sreg (off size : Nat) : Region := ⟨scratchR.off + off, size⟩

/-- The slot weights, `2^busBits` elements. -/
def wR : Region := sreg 0 32
/-- `β`. -/
def betaR : Region := sreg 32 2
/-- The GKR point, at most `busPointCap` coordinates. -/
def pointR : Region := sreg 34 128
/-- The three trees' values. -/
def treeR : Region := sreg 162 6
/-- The count root. -/
def countR : Region := sreg 168 2
/-- The memory's two limbs. -/
def memR : Region := sreg 170 4
/-- The memory's final counter. -/
def memFinalR : Region := sreg 174 2
/-- The bytecode's final counter. -/
def bcFinalR : Region := sreg 176 2
/-- The bytecode share. -/
def shareR : Region := sreg 178 2
/-- The bytecode share's value. -/
def valueR : Region := sreg 180 2
/-- The bytecode share's slot point, `busBits` coordinates. -/
def slotR : Region := sreg 182 8
/-- The fingerprints: the push side's three, then the pull side's. -/
def fpR : Region := sreg 190 12
/-- The three sides' totals. -/
def totalsR : Region := sreg 202 6
/-- The push side's depth, one word. -/
def depthR : Region := sreg 209 1
/-- Phase 3's own values (`P3.Main`'s slots). -/
def valsR : Region := sreg 210 46
/-- A side's placements, in the layout code's format (`P3.Layout`). -/
def placeR (side : Nat) : Region := sreg (256 + 512 * side) 256
/-- A side's table blocks' selectors, one element per block. -/
def tselR (side : Nat) : Region := sreg (512 + 512 * side) 102
/-- A side's table blocks' padding weights, one element per block. -/
def padWR (side : Nat) : Region := sreg (614 + 512 * side) 102
/-- A side's framework selectors, at most three elements. -/
def fselR (side : Nat) : Region := sreg (716 + 512 * side) 6
/-- A side's padding rows' sum and its framework values. -/
def sumR (side : Nat) : Region := sreg (1792 + 8 * side) 8
/-- Temporaries of any part. -/
def tmpR : Region := sreg 2048 6144
/-- The forms' temporaries: the block form, the protocol's block data. -/
def formTmpR : Region := sreg 8192 24576

theorem scratchR_off : scratchR.off = 52670 := by decide
theorem scratchR_size : scratchR.size = 32768 := (rfl)
theorem busR_off : busR.off = 622 := by decide
theorem busR_size : busR.size = 13471 := by decide
theorem claimsR_off : claimsR.off = 15569 := by decide
theorem claimsR_size : claimsR.size = 12161 := by decide
theorem layoutR_off : layoutR.off = 69 := by decide
theorem dataEnd_eq : dataEnd = 85438 := dataEnd_val

/-! ## Regions phase 3 may write -/

/-- `r` lies inside `q`. -/
def Within (r q : Region) : Prop := q.off ≤ r.off ∧ r.stop ≤ q.stop

instance (r q : Region) : Decidable (Within r q) := inferInstanceAs (Decidable (_ ∧ _))

/-- Phase 3's regions. -/
abbrev rs3 : List Region := [busR, claimsR, scratchR]

/-- A region phase 3 may write. -/
def Ok3 (r : Region) : Prop := Within r busR ∨ Within r claimsR ∨ Within r scratchR

theorem ok3_sreg {off size : Nat} (h : off + size ≤ 32768) : Ok3 (sreg off size) :=
  .inr (.inr ⟨by simp [sreg], by simp only [sreg, Region.stop, scratchR_size]; omega⟩)

theorem ok3_busR : Ok3 busR := .inl ⟨le_refl _, le_refl _⟩
theorem ok3_claimsR : Ok3 claimsR := .inr (.inl ⟨le_refl _, le_refl _⟩)
theorem ok3_scratchR : Ok3 scratchR := .inr (.inr ⟨le_refl _, le_refl _⟩)

theorem Ok3.bounds {r : Region} (h : Ok3 r) : layoutR.off ≤ r.off ∧ r.stop ≤ dataEnd := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> unfold Region.stop at * <;>
    simp only [busR_off, busR_size, claimsR_off, claimsR_size, scratchR_off, scratchR_size,
      layoutR_off, dataEnd_eq] at * <;> omega

theorem in_within {env : Env} {r q : Region} {a : UInt64} (h : r.In env.work a)
    (hw : Within r q) : q.In env.work a := by
  obtain ⟨k, hk, rfl⟩ := h
  have h1 := hw.1
  have h2 := hw.2
  unfold Region.stop at h2
  refine ⟨r.off - q.off + k, by omega, ?_⟩
  congr 1
  omega

theorem _root_.NativeVm.Code.Kept.ok3 {env : Env} {ws : List Region} {s s' : QState} (h : Kept env ws s s')
    (hws : ∀ r ∈ ws, Ok3 r) : Kept env rs3 s s' := by
  refine ⟨h.1, fun a hf hr ↦ h.2 a hf fun r hm hin ↦ ?_⟩
  rcases hws r hm with hw | hw | hw
  · exact hr busR (by simp) (in_within hin hw)
  · exact hr claimsR (by simp) (in_within hin hw)
  · exact hr scratchR (by simp) (in_within hin hw)

/-! ## A part's run -/

/-- A part's run from `s` to `s'`: `rdi` and the registers outside `regs` kept, the words outside
the transcript's and the regions `ws` kept, which words exist kept. -/
structure Step3 (env : Env) (regs : List Reg64) (ws : List Region) (s s' : QState) : Prop where
  rdi : s'.reg .rdi = s.reg .rdi
  regs : RegsFrame regs s s'
  mem : ∀ a, ¬ Foot env a → (∀ r ∈ ws, ¬ r.In env.work a) → s'.mem a = s.mem a
  dom : ∀ a, (s'.mem a).isSome = (s.mem a).isSome

theorem Step3.refl (env : Env) (regs : List Reg64) (ws : List Region) (s : QState) :
    Step3 env regs ws s s :=
  ⟨rfl, fun _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ ↦ rfl⟩

theorem Step3.trans {env : Env} {regs : List Reg64} {ws : List Region} {s₁ s₂ s₃ : QState}
    (h₁ : Step3 env regs ws s₁ s₂) (h₂ : Step3 env regs ws s₂ s₃) : Step3 env regs ws s₁ s₃ :=
  ⟨h₂.rdi.trans h₁.rdi, fun r hr ↦ (h₂.regs r hr).trans (h₁.regs r hr),
    fun a hf hr ↦ (h₂.mem a hf hr).trans (h₁.mem a hf hr), fun a ↦ (h₂.dom a).trans (h₁.dom a)⟩

theorem Step3.mono {env : Env} {regs regs' : List Reg64} {ws ws' : List Region} {s s' : QState}
    (h : Step3 env regs ws s s') (hr : regs ⊆ regs') (hw : ∀ r ∈ ws, r ∈ ws') :
    Step3 env regs' ws' s s' :=
  ⟨h.rdi, fun r h' ↦ h.regs r fun m ↦ h' (hr m), fun a hf h' ↦ h.mem a hf fun r m ↦ h' r (hw r m),
    h.dom⟩

theorem Step3.kept {env : Env} {regs : List Reg64} {ws : List Region} {s s' : QState}
    (h : Step3 env regs ws s s') (hrdi : s.reg .rdi = env.ctx) : Kept env ws s s' :=
  ⟨h.rdi.trans hrdi, h.mem⟩

/-- A gadget's run is a part's run writing no region. -/
theorem Step3.ofKeeps {env : Env} {s s' : QState} (h : Keeps clobbers (Foot env) s s')
    (hd : ∀ a, (s'.mem a).isSome = (s.mem a).isSome) : Step3 env clobbers [] s s' :=
  ⟨h.rdi, h.regs, fun a hf _ ↦ h.mem a hf, hd⟩

/-- The run of code that writes no transcript word: `rdi` kept, every word outside the regions
`ws` kept, which words exist kept. -/
structure Wrote (env : Env) (ws : List Region) (s s' : QState) : Prop where
  rdi : s'.reg .rdi = s.reg .rdi
  mem : ∀ a, (∀ r ∈ ws, ¬ r.In env.work a) → s'.mem a = s.mem a
  dom : ∀ a, (s'.mem a).isSome = (s.mem a).isSome

theorem Wrote.refl (env : Env) (ws : List Region) (s : QState) : Wrote env ws s s :=
  ⟨rfl, fun _ _ ↦ rfl, fun _ ↦ rfl⟩

theorem Wrote.trans {env : Env} {ws : List Region} {s₁ s₂ s₃ : QState}
    (h₁ : Wrote env ws s₁ s₂) (h₂ : Wrote env ws s₂ s₃) : Wrote env ws s₁ s₃ :=
  ⟨h₂.rdi.trans h₁.rdi, fun a hr ↦ (h₂.mem a hr).trans (h₁.mem a hr),
    fun a ↦ (h₂.dom a).trans (h₁.dom a)⟩

theorem Wrote.mono {env : Env} {ws ws' : List Region} {s s' : QState} (h : Wrote env ws s s')
    (hw : ∀ r ∈ ws, r ∈ ws') : Wrote env ws' s s' :=
  ⟨h.rdi, fun a h' ↦ h.mem a fun r m ↦ h' r (hw r m), h.dom⟩

/-- Every register of the machine. -/
def allRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rsp, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem Wrote.step {env : Env} {ws : List Region} {s s' : QState} (h : Wrote env ws s s') :
    Step3 env allRegs ws s s' :=
  ⟨h.rdi, fun r hr ↦ absurd (by cases r <;> simp [allRegs]) hr, fun a _ hr ↦ h.mem a hr, h.dom⟩

/-- A store to a word of a region. -/
theorem Wrote.setMem {env : Env} {ws : List Region} {s s' : QState} (h : Wrote env ws s s')
    {r : Region} (hr : r ∈ ws) {k : Nat} (hk : k < r.size) (hs : (s'.mem (wd env.work (r.off + k))).isSome)
    (v : UInt64) : Wrote env ws s (s'.setMem (wd env.work (r.off + k)) v) := by
  refine ⟨h.rdi, fun a ha ↦ ?_, fun a ↦ ?_⟩
  · have hne : a ≠ wd env.work (r.off + k) := by
      rintro rfl
      exact ha r hr ⟨k, hk, rfl⟩
    rw [QState.setMem_mem, ite_eq_right_of_eq_false _ _ (eq_false hne), h.mem a ha]
  · rw [QState.setMem_mem]
    split
    · subst a; rw [← h.dom]; exact hs.symm
    · exact h.dom a

theorem Wrote.step' {env : Env} {ws : List Region} {regs : List Reg64} {s s' : QState}
    (h : Wrote env ws s s') (hr : RegsFrame regs s s') : Step3 env regs ws s s' :=
  ⟨h.rdi, hr, fun a _ ha ↦ h.mem a ha, h.dom⟩

theorem Wrote.setReg {env : Env} {ws : List Region} {s s' : QState} (h : Wrote env ws s s')
    {r : Reg64} (hr : r ≠ .rdi) (v : UInt64) : Wrote env ws s (s'.setReg r v) :=
  ⟨by rw [QState.setReg_reg, ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hr))]; exact h.rdi, h.mem, h.dom⟩

/-! ## The working area -/

variable {env : Env} {inp : Input} {t : TState} {s s' : QState}

theorem _root_.NativeVm.Code.Inputs.ok3_some' {mem : UInt64 → Option UInt64} (h : Inputs env inp mem)
    {r : Region} (hr : Ok3 r) {a : Nat} (ha' : a < r.stop) :
    (mem (wd env.work a)).isSome := by
  have hb := hr.bounds
  have := dataEnd_le inp.bytecode.size
  unfold Region.stop at hb ha'
  exact h.workSome _ (by omega)

theorem _root_.NativeVm.Code.Inputs.ok3_some {mem : UInt64 → Option UInt64} (h : Inputs env inp mem) {r : Region}
    (hr : Ok3 r) {k : Nat} (hk : k < r.size) : (mem (wd env.work (r.off + k))).isSome := by
  have hb := hr.bounds
  have := dataEnd_le inp.bytecode.size
  unfold Region.stop at hb
  exact h.workSome _ (by omega)

/-- A word of a region phase 3 writes is not the transcript's. -/
theorem _root_.NativeVm.Code.Inputs.ok3_not_foot {mem : UInt64 → Option UInt64} (h : Inputs env inp mem) {r : Region}
    (hr : Ok3 r) {a : UInt64} (ha : r.In env.work a) : ¬ Foot env a := by
  obtain ⟨k, hk, rfl⟩ := ha
  have hb := hr.bounds
  have := dataEnd_le inp.bytecode.size
  have hl : Transcript.workWords ≤ layoutR.off := (regions_bounds layoutR (by simp [regions])).1
  unfold Region.stop at hb
  exact h.not_foot_work (by omega) (by omega)

/-- A region phase 3 writes is apart from the decoded proof. -/
theorem _root_.NativeVm.Code.Inputs.ok3_ne_dec {mem : UInt64 → Option UInt64} (h : Inputs env inp mem)
    (hd : Fits env.dec (decodedWords env.L)) {r : Region} (hr : Ok3 r) {a : UInt64}
    (ha : r.In env.work a) {k : Nat} (hk : k < decodedWords env.L) : a ≠ wd env.dec k := by
  obtain ⟨j, hj, rfl⟩ := ha
  have hb := hr.bounds
  have := dataEnd_le inp.bytecode.size
  unfold Region.stop at hb
  exact (wd_ne_of_disj hd h.fitWork h.disjDec hk (by omega)).symm

/-- **`CodeRel` through code that writes no transcript word.** -/
theorem _root_.NativeVm.Code.CodeRel.wrote3 {ws : List Region} (h : CodeRel env t s) (hi : Inputs env inp s.mem)
    (hws : ∀ r ∈ ws, Ok3 r) (hw : Wrote env ws s s') : CodeRel env t s' := by
  obtain ⟨st, hr, hs, h1, h2⟩ := h
  refine ⟨st, hr, hs.congrW (hw.rdi.trans hs.rdi) hw.dom ?_ ?_ ?_, h1, h2⟩
  · intro k hk
    refine hw.mem _ fun r hm hin ↦ ?_
    obtain ⟨j, hj, e⟩ := hin
    have hb := (hws r hm).bounds
    have := dataEnd_le inp.bytecode.size
    unfold Region.stop at hb
    refine hi.ctx_ne_work (j := k) (k := r.off + j) ?_ (by omega) e
    rcases hk with hk | ⟨-, hk⟩ <;> lay_omega
  · intro k hk
    exact hw.mem _ fun r hm hin ↦ hi.ok3_ne_dec hs.layout.fitDec (hws r hm) hin hk rfl
  · intro k hk
    refine hw.mem _ fun r hm hin ↦ hi.ok3_not_foot (hws r hm) hin (foot_work hk)

theorem _root_.NativeVm.Code.CodeRel.setReg3 (h : CodeRel env t s) {r : Reg64} (hr : r ≠ .rdi)
    (v : UInt64) : CodeRel env t (s.setReg r v) := by
  obtain ⟨st, h1, h2, h3, h4⟩ := h
  exact ⟨st, h1, h2.setReg hr v, h3, h4⟩

/-- The inputs through a part's run. -/
theorem _root_.NativeVm.Code.Inputs.step3 {regs : List Reg64} {ws : List Region} (h : Inputs env inp s.mem)
    (hws : ∀ r ∈ ws, Ok3 r) (hs : Step3 env regs ws s s') (hrdi : s.reg .rdi = env.ctx) :
    Inputs env inp s'.mem :=
  h.kept ((hs.kept hrdi).ok3 hws) (fun r hr ↦ by
    simp only [rs3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact stop_le_of_mem (by simp [regions]) _) hs.dom

/-- The working area's address, for the code's loads and stores. -/
theorem _root_.NativeVm.Code.CodeRel.workPtr3 (h : CodeRel env t s) :
    s.mem (wd env.ctx ctxWork) = some env.work :=
  h.layout.workPtr

/-- An address from the working area's. -/
theorem eval_work {b : Reg64} (h : s.reg b = env.work) (k : Nat) :
    (at_ b (wdisp k)).eval s = wd env.work k :=
  eval_wd (j := 0) (by rw [h, wd_zero]) k |>.trans (by rw [Nat.zero_add])

/-! ## The sides (`accumulateSide`'s arguments, by side) -/

/-- The framework blocks' log-sizes of the push and pull sides. -/
def frameworkLogRows (layout : LayoutW) : Array Nat := #[0, layout.logMemory, layout.logBytecode]

/-- A side's table blocks: push, pull, count. -/
def sideBlocks (layout : LayoutW) (side : Nat) : Array BusBlockW :=
  if side = 0 then layout.push else if side = 1 then layout.pull else layout.count

/-- A side's placements: the push and pull sides after the framework blocks, the count side
alone. -/
def sideLayout (layout : LayoutW) (side : Nat) : BusLayoutW :=
  if side = 2 then busLayout #[] layout.count
  else busLayout (frameworkLogRows layout) (sideBlocks layout side)

/-- A side's slot weights: the challenges, or `#[1]` on the count side. -/
def sideWeights (weights : Array EW) (side : Nat) : Array EW := if side = 2 then #[1] else weights

/-- A side's `β`: the challenge, or `0` on the count side. -/
def sideBeta (beta : EW) (side : Nat) : EW := if side = 2 then 0 else beta

/-- The table blocks' padding weights at the point. -/
def padWeights (blocks : Array BusBlockW) (point : Array EW) : Array EW :=
  blocks.map fun b ↦ paddingWeight (point.extract 0 b.logRows) b.rows

/-- **`accumulateSide`'s fold** over the table blocks, from their selectors `sels` and padding
weights `pws`: the forms with the side's blocks added, and the padding rows' sum. -/
def sideFold (forms : Array (Array FormW)) (side : Nat) (blocks : Array BusBlockW)
    (sels pws : Array EW) (ws : Array EW) (β : EW) : Array (Array FormW) × EW :=
  ((sels.zip pws).zip blocks).foldl (fun (acc : Array (Array FormW) × EW) x ↦
      let form := blockForm x.2 ws β
      let padding := (tablesW.getD x.2.owner default).padding
      (acc.1.modify x.2.owner fun row ↦ row.modify side fun f ↦ f.addScaled form x.1.1,
        acc.2 + x.1.1 * x.1.2 * (form.evaluate padding + 1))) (forms, 0)

/-- The bus's forms at `p` (`BusAt`'s first part): table `t`'s on side `side` at
`formOff t side`. -/
def FormsAt (mem : UInt64 → Option UInt64) (p : UInt64) (forms : Array (Array FormW)) : Prop :=
  forms.size = nTables ∧ (∀ t < nTables, (forms.getD t #[]).size = 3) ∧
    ∀ t < nTables, ∀ side < 3, FormAt mem (wd p (formOff t side)) ((forms.getD t #[]).getD side #[])

theorem FormsAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {forms : Array (Array FormW)}
    (h : Same mem mem' p (formWords * (3 * nTables))) (hx : FormsAt mem p forms) :
    FormsAt mem' p forms := by
  refine ⟨hx.1, hx.2.1, fun t ht side hs ↦ (hx.2.2 t ht side hs).congr (h.sub ?_)⟩
  have : formWords * (3 * t + side) + formWords ≤ formWords * (3 * nTables) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by unfold nTables at ht ⊢; omega)
  unfold formOff; omega

/-! ## What a run keeps of a region -/

/-- A region of the working area after the transcript's words. -/
def Ok0 (q : Region) : Prop := Transcript.workWords ≤ q.off ∧ q.stop ≤ dataEnd

theorem Ok3.ok0 {r : Region} (h : Ok3 r) : Ok0 r := by
  have := h.bounds
  have hl : Transcript.workWords ≤ layoutR.off := (regions_bounds layoutR (by simp [regions])).1
  exact ⟨by omega, this.2⟩

theorem ok0_of_mem {q : Region} (h : q ∈ regions) : Ok0 q := regions_bounds q h

/-- **A run keeps a region apart from the ones it writes.** -/
theorem Step3.same {regs : List Reg64} {ws : List Region} {q : Region} (hs : Step3 env regs ws s s')
    (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r) (hq : Ok0 q) (hap : ∀ r ∈ ws, q.Apart r) :
    Same s.mem s'.mem (q.at env.work) q.size := by
  intro k hk
  have hdl := dataEnd_le inp.bytecode.size
  have hww := workWords_lt hi
  have hq' := hq
  unfold Ok0 Region.stop at hq'
  rw [Region.at, wd_wd]
  refine hs.mem _ (hi.not_foot_work (by omega) (by omega)) fun r hr ⟨j, hj, e⟩ ↦ ?_
  have hb := (hws r hr).bounds
  have ha := hap r hr
  unfold Region.stop at hb
  unfold Region.Apart Region.stop at ha
  rw [wd_inj (by omega) (by omega)] at e
  omega

theorem Wrote.same {ws : List Region} {q : Region} (hs : Wrote env ws s s')
    (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r) (hq : Ok0 q) (hap : ∀ r ∈ ws, q.Apart r) :
    Same s.mem s'.mem (q.at env.work) q.size :=
  hs.step.same hi hws hq hap

/-! ## Elements in registers -/

theorem eOf_eq_toE {a b : UInt64} {x : EW} : Field.eOf a b = x.toE ↔ a = x.c0 ∧ b = x.c1 := by
  rw [show x.toE = Field.eOf x.c0 x.c1 from rfl, Field.eOf_inj]

/-! ## The transcript's loops -/

/-- Run `g` `r12` times, storing each result (`r9`, `r10`) as the next element from word `k` of the
working area: the count left in `r12`, the next element's address in `r13`. -/
def loopTo (g : Stmt) (k : Nat) : Stmt := blk [
  I (.load .r13 (cw ctxWork)), I (.addi .r13 (wdisp k)),
  .loop (.cmp .ne .r12 (.imm 0)) (blk [g,
    I (.store (at_ .r13 0) .r9), I (.store (at_ .r13 8) .r10),
    I (.addi .r13 16), I (.subi .r12 1)])]

/-- `readScalars r12` into the words from `k`. -/
def readsTo (k : Nat) : Stmt := loopTo Transcript.readScalar k

/-- `sampleChallenges r12` into the words from `k`. -/
def samplesTo (k : Nat) : Stmt := loopTo Transcript.sampleChallenge k

/-- Run `g` once, storing its result (`r9`, `r10`) at words `k`, `k + 1` of the working area. -/
def oneTo (g : Stmt) (k : Nat) : Stmt := blk [g, I (.load .r11 (cw ctxWork)),
  I (.addi .r11 (wdisp k)), I (.store (at_ .r11 0) .r9), I (.store (at_ .r11 8) .r10)]

/-- `readScalar` into words `k`, `k + 1`. -/
def readTo (k : Nat) : Stmt := oneTo Transcript.readScalar k

/-- `sampleChallenge` into words `k`, `k + 1`. -/
def sampleTo (k : Nat) : Stmt := oneTo Transcript.sampleChallenge k

/-- The registers the loops write. -/
abbrev clob3 : List Reg64 := clobbers ++ [.r12, .r13]

theorem ewarr_push {mem : UInt64 → Option UInt64} {p : UInt64} {xs : Array EW} {x : EW}
    (h : EWArr mem p xs) (hx : EWAt mem (wd p (2 * xs.size)) x) : EWArr mem p (xs.push x) := by
  intro i hi
  rw [Array.size_push] at hi
  rw [Array.getElem_push]
  split
  · exact h i (by omega)
  · rw [show i = xs.size by omega]
    exact hx

/-- A word from `k` inside the region. -/
theorem in_word {r : Region} {k i : Nat} (hk : r.off ≤ k) (hi : k + i < r.stop) :
    r.In env.work (wd env.work (k + i)) :=
  ⟨k + i - r.off, by unfold Region.stop at hi; omega, by congr 1; omega⟩

/-- A run keeping the words outside the transcript's and `ws` keeps an array of a region apart. -/
theorem ewarr_step {regs : List Reg64} {ws : List Region} {r : Region} (hi : Inputs env inp s.mem)
    (hr : Ok3 r) (hs : Step3 env regs ws s s') (hap : ∀ q ∈ ws, ∀ a, r.In env.work a → ¬ q.In env.work a)
    {k : Nat} {xs : Array EW} (hk : r.off ≤ k) (hkn : k + 2 * xs.size ≤ r.stop)
    (h : EWArr s.mem (wd env.work k) xs) : EWArr s'.mem (wd env.work k) xs := by
  refine h.congr (n := 2 * xs.size) (fun i hi' ↦ ?_) le_rfl
  rw [wd_wd]
  have hin := in_word (env := env) hk (show k + i < r.stop by omega)
  exact hs.mem _ (hi.ok3_not_foot hr hin) fun q hq ↦ hap q hq _ hin

/-- **Two stores of an element**, `r9` and `r10` at words `a`, `a + 1` of a region, through the
address in `b`. -/
theorem wp_storePair {b : Reg64} {a : Nat} {r : Region} {xs : List Stmt} {P E : QState → Prop}
    (hr : Ok3 r) (ha : r.off ≤ a) (ha2 : a + 2 ≤ r.stop) (hb : s.reg b = wd env.work a)
    (hi : Inputs env inp s.mem)
    (k : ∀ s', Wrote env [r] s s' → EWAt s'.mem (wd env.work a) ⟨s.reg .r9, s.reg .r10⟩ →
      s'.reg = s.reg → WP (blk xs) s' P E) :
    WP (blk (I (.store (at_ b 0) .r9) :: I (.store (at_ b 8) .r10) :: xs)) s P E := by
  have hbd := hr.bounds
  have hdl := dataEnd_le inp.bytecode.size
  have hww := workWords_lt hi
  unfold Region.stop at ha2 hbd
  have hs0 := hi.ok3_some' hr (a := a) (by unfold Region.stop; omega)
  have hs1 := hi.ok3_some' hr (a := a + 1) (by unfold Region.stop; omega)
  have e0 : (at_ b 0).eval s = wd env.work a := by rw [eval_at, hb, Field.int64Zero_toUInt64, UInt64.add_zero]
  refine wp_store e0 hs0 ?_
  have e1 : (at_ b 8).eval (s.setMem (wd env.work a) (s.reg .r9)) = wd env.work (a + 1) := by
    rw [eval_at, QState.setMem_reg, hb, show (8 : Int64).toUInt64 = (8 * 1 : Nat).toUInt64 from rfl, wd_add]
  have hne : wd env.work (a + 1) ≠ wd env.work a := fun e ↦ by
    rw [wd_inj (by omega) (by omega)] at e; omega
  have hs1' : ((s.setMem (wd env.work a) (s.reg .r9)).mem (wd env.work (a + 1))).isSome := by
    rw [QState.setMem_mem]; simp only [hne, ↓reduceIte]; exact hs1
  refine wp_store e1 hs1' ?_
  have hw := ((Wrote.refl env [r] s).setMem (r := r) (by simp) (k := a - r.off) (by omega)
    (by rwa [show r.off + (a - r.off) = a by omega]) (s.reg .r9)).setMem (r := r) (by simp)
    (k := a + 1 - r.off) (by omega)
    (by rw [show r.off + (a + 1 - r.off) = a + 1 by omega, show r.off + (a - r.off) = a by omega]
        exact hs1')
    ((s.setMem (wd env.work a) (s.reg .r9)).reg .r10)
  rw [show r.off + (a - r.off) = a by omega, show r.off + (a + 1 - r.off) = a + 1 by omega] at hw
  refine k _ hw ⟨?_, ?_⟩ (by simp)
  · simp only [QState.setMem_mem, Ne.symm hne, ↓reduceIte]
  · simp only [wd_wd, QState.setMem_mem, ↓reduceIte, QState.setMem_reg]

/-- `n` results of `m`, in order (`readScalars`, `sampleChallenges`). -/
def pushes (m : VM EW) (n : Nat) : VM (Array EW) :=
  (List.range n).foldlM (fun (acc : Array EW) _ ↦ do pure (acc.push (← m))) #[]

theorem readScalars_eq (n : Nat) : readScalars n = pushes Model.readScalar n := (rfl)

theorem sampleChallenges_eq (n : Nat) : sampleChallenges n = pushes Model.sampleChallenge n := (rfl)

/-- **The loop of a gadget into the working area.** -/
theorem loopTo_spec {g : Stmt} {m : VM EW}
    (hg : ∀ t s, CodeRel env t s → WP g s
      (fun s' ↦ ∃ x t', m.run t = some (x, t') ∧ CodeRel env t' s' ∧ s'.reg .r9 = x.c0 ∧
        s'.reg .r10 = x.c1 ∧ Keeps clobbers (Foot env) s s')
      (fun s' ↦ m.run t = none ∧ Keeps clobbers (Foot env) s s'))
    {n k : Nat} {r : Region} (hr : Ok3 r) (hk : r.off ≤ k) (hkn : k + 2 * n ≤ r.stop)
    (h : CodeRel env t s) (hi : Inputs env inp s.mem) (h12 : s.reg .r12 = n.toUInt64) :
    WP (loopTo g k) s
      (fun s' ↦ ∃ xs t', (pushes m n).run t = some (xs, t') ∧ CodeRel env t' s' ∧
        xs.size = n ∧ EWArr s'.mem (wd env.work k) xs ∧ Step3 env clob3 [r] s s')
      (fun s' ↦ (pushes m n).run t = none ∧ Step3 env clob3 [r] s s') := by
  have hb := hr.bounds
  have hdl := dataEnd_le inp.bytecode.size
  have hww := workWords_lt hi
  unfold Region.stop at hkn hb
  have hrdi := h.rdi
  unfold loopTo
  refine wp_load (eval_cw hrdi ctxWork) h.workPtr3 ?_
  refine wp_reg rfl ?_
  show WP (Stmt.loop _ _) _ _ _
  have key := Refines.foldlM (l := List.range n)
    (f := fun (acc : Array EW) (_ : Nat) ↦ do pure (acc.push (← m)))
    (cond := .cmp .ne .r12 (.imm 0)) (body := blk [g,
      I (.store (at_ .r13 0) .r9), I (.store (at_ .r13 8) .r10),
      I (.addi .r13 16), I (.subi .r12 1)]) (E := fun s' ↦ Step3 env clob3 [r] s s')
    (Inv := fun j acc t' s' ↦ CodeRel env t' s' ∧ Inputs env inp s'.mem ∧ acc.size = j ∧
      EWArr s'.mem (wd env.work k) acc ∧ s'.reg .r12 = (n - j).toUInt64 ∧
      s'.reg .r13 = wd env.work (k + 2 * j) ∧ Step3 env clob3 [r] s s') ?_ ?_ (init := #[])
  · refine WP.mono (key t _ ⟨(h.setReg3 (by decide) _).setReg3 (by decide) _, hi, rfl, fun i hi' ↦ absurd hi' (by simp), ?_, ?_, ?_⟩) ?_ ?_
    · rsimp; simpa using h12
    · rsimp; rfl
    · refine ⟨by rsimp, fun r' hr' ↦ ?_, fun _ _ _ ↦ by rsimp, fun _ ↦ by rsimp⟩
      rsimp
      have : r' ≠ .r13 := fun e ↦ hr' (by simp [e, clob3])
      simp [this]
    · rintro s' ⟨xs, t', hrun, hc, hin, hsz, harr, -, -, hst⟩
      rw [List.length_range] at hsz
      exact ⟨xs, t', hrun, hc, hsz, harr, hst⟩
    · rintro s' ⟨hrun, hst⟩
      exact ⟨hrun, hst⟩
  · rintro j acc t' s' ⟨-, -, -, -, h12', -⟩
    rw [List.length_range, cond_ne, rhs_imm, h12', Field.int64Zero_toUInt64, bne_iff_ne, ne_eq]
    constructor
    · intro hne
      by_contra hjn
      exact hne (by rw [show n - j = 0 by omega]; rfl)
    · intro hjn e
      have := Field.toUInt64_eq_zero (show n - j < 2 ^ 64 by omega) e
      omega
  · intro j hj acc
    rw [List.length_range] at hj
    show Refines _ _ (m >>= fun x ↦ pure (acc.push x)) _ _
    refine Refines.blk_cons (Q₁ := fun x t' s' ↦ CodeRel env t' s' ∧ Inputs env inp s'.mem ∧
      acc.size = j ∧ EWArr s'.mem (wd env.work k) acc ∧ s'.reg .r12 = (n - j).toUInt64 ∧
      s'.reg .r13 = wd env.work (k + 2 * j) ∧ s'.reg .r9 = x.c0 ∧ s'.reg .r10 = x.c1 ∧
      Step3 env clob3 [r] s s') ?_ fun x ↦ Refines.pure ?_
    · rintro t' s' ⟨hc, hin, hsz, harr, h12', h13', hst⟩
      refine WP.mono (WP.frame (hg t' s' hc)) ?_ ?_
      · rintro s'' ⟨⟨x, t'', hrun, hc'', h9, h10, hkp⟩, hdom, -⟩
        have hs3 : Step3 env clobbers [] s' s'' := Step3.ofKeeps hkp hdom
        refine ⟨x, t'', hrun, hc'', hin.step3 (by simp) hs3 hc.rdi, hsz,
          ewarr_step hin hr hs3 (by simp) hk (by unfold Region.stop; omega) harr, ?_, ?_, h9, h10,
          hst.trans (hs3.mono (by simp [clob3]) (by simp))⟩
        · rw [hkp.regs .r12 (by simp [clobbers])]; exact h12'
        · rw [hkp.regs .r13 (by simp [clobbers])]; exact h13'
      · rintro s'' ⟨⟨hrun, hkp⟩, hdom, -⟩
        exact ⟨hrun, hst.trans ((Step3.ofKeeps hkp hdom).mono (by simp [clob3]) (by simp))⟩
    · rintro t' s' ⟨hc, hin, hsz, harr, h12', h13', h9, h10, hst⟩
      have hj2 : k + 2 * j + 1 < r.stop := by unfold Region.stop; omega
      have hs0 := hin.ok3_some' hr (a := k + 2 * j) (by unfold Region.stop; omega)
      have hs1 := hin.ok3_some' hr (a := k + 2 * j + 1) hj2
      refine wp_store (by rw [eval_at, h13', Field.int64Zero_toUInt64, UInt64.add_zero]) hs0 ?_
      have e1 : (at_ .r13 8).eval (s'.setMem (wd env.work (k + 2 * j)) (s'.reg .r9)) =
          wd env.work (k + 2 * j + 1) := by
        rw [eval_at, QState.setMem_reg, h13',
          show (8 : Int64).toUInt64 = (8 * 1 : Nat).toUInt64 from rfl, wd_add]
      refine wp_store e1 (by rw [QState.setMem_mem]; split <;> simp_all) ?_
      refine wp_reg rfl (wp_reg rfl (WP.blk_nil ?_))
      have hw := ((Wrote.refl env [r] s').setMem (r := r) (by simp) (k := k + 2 * j - r.off)
          (by omega) (by rwa [show r.off + (k + 2 * j - r.off) = k + 2 * j by omega])
          (s'.reg .r9)).setMem (r := r) (by simp) (k := k + 2 * j + 1 - r.off)
          (by unfold Region.stop at hj2; omega) ?_
          ((s'.setMem (wd env.work (k + 2 * j)) (s'.reg .r9)).reg .r10)
      rotate_left
      · rw [show r.off + (k + 2 * j + 1 - r.off) = k + 2 * j + 1 by omega, QState.setMem_mem]
        split <;> simp_all
      rw [show r.off + (k + 2 * j - r.off) = k + 2 * j by omega,
        show r.off + (k + 2 * j + 1 - r.off) = k + 2 * j + 1 by omega] at hw
      have hne : ∀ i < 2 * j, wd env.work (k + i) ≠ wd env.work (k + 2 * j) ∧
          wd env.work (k + i) ≠ wd env.work (k + 2 * j + 1) := fun i hi ↦
        ⟨fun e ↦ by rw [wd_inj (by omega) (by omega)] at e; omega,
          fun e ↦ by rw [wd_inj (by omega) (by omega)] at e; omega⟩
      set s3 : QState := (s'.setMem (wd env.work (k + 2 * j)) (s'.reg .r9)).setMem
        (wd env.work (k + 2 * j + 1)) ((s'.setMem (wd env.work (k + 2 * j)) (s'.reg .r9)).reg .r10)
        with hs3
      have hst' : Step3 env [.r12, .r13] [r] s'
          ((s3.setReg .r13 (s3.reg .r13 + (16 : Int64).toUInt64)).setReg .r12
            ((s3.setReg .r13 (s3.reg .r13 + (16 : Int64).toUInt64)).reg .r12 - (1 : Int64).toUInt64)) :=
        (hw.setReg (r := .r13) (by decide) _).setReg (r := .r12) (by decide) _ |>.step' (fun r' hr' ↦ by
          have h1 : r' ≠ .r12 := fun e ↦ hr' (by simp [e])
          have h2 : r' ≠ .r13 := fun e ↦ hr' (by simp [e])
          simp [h1, h2, hs3])
      refine ⟨((hc.wrote3 hin (by simpa using hr) hw).setReg3 (by decide) _).setReg3 (by decide) _,
        hin.step3 (by simpa using hr) hst' hc.rdi, by rw [Array.size_push, hsz], ?_, ?_, ?_,
        hst.trans (hst'.mono (by simp [clob3]) (by simp))⟩
      · have a0 : ∀ a, a < k + 2 * j → s3.mem (wd env.work a) = s'.mem (wd env.work a) := fun a ha ↦ by
          rw [hs3, setMem_wd_ne (k := k + 2 * j + 1) (k' := a) _ _ (by omega) (by omega) (by omega),
            setMem_wd_ne (k := k + 2 * j) (k' := a) _ _ (by omega) (by omega) (by omega)]
        refine ewarr_push (fun i hi' ↦ ?_) ?_
        · have := harr i hi'
          rw [EWAt, wd_wd, wd_wd] at this ⊢
          simp only [QState.setReg_mem]
          rw [a0 _ (by omega), a0 _ (by omega)]
          exact this
        · rw [EWAt, wd_wd, wd_wd, hsz]
          simp only [QState.setReg_mem]
          rw [hs3, setMem_wd_ne (k := k + 2 * j + 1) (k' := k + 2 * j) _ _ (by omega) (by omega)
            (by omega), setMem_wd_eq _ _ rfl, setMem_wd_eq _ _ rfl, QState.setMem_reg, h9, h10]
          exact ⟨rfl, rfl⟩
      · rsimp
        rw [hs3, QState.setMem_reg, QState.setMem_reg, h12', show n - j = (n - (j + 1)) + 1 by omega,
          Field.toUInt64_succ_sub]
      · rsimp
        rw [hs3, QState.setMem_reg, QState.setMem_reg, h13',
          show (16 : UInt64) = (8 * 2 : Nat).toUInt64 from rfl, wd_add]
        congr 1

/-- `sampleChallenge`'s steps never fail. -/
theorem foldl_sample_some (l : List Nat) (acc : Array EW) (t : TState) :
    ((l.foldlM (fun (acc : Array EW) _ ↦ do pure (acc.push (← Model.sampleChallenge))) acc).run t).isSome := by
  induction l generalizing acc t with
  | nil => rfl
  | cons _ l ih =>
    rw [List.foldlM_cons, StateT.run_bind, StateT.run_bind, NativeVm.Equiv.sampleChallenge_run]
    exact ih _ _

theorem sample_spec' (h : CodeRel env t s) : WP Transcript.sampleChallenge s
    (fun s' ↦ ∃ x t', Model.sampleChallenge.run t = some (x, t') ∧ CodeRel env t' s' ∧
      s'.reg .r9 = x.c0 ∧ s'.reg .r10 = x.c1 ∧ Keeps clobbers (Foot env) s s')
    (fun s' ↦ Model.sampleChallenge.run t = none ∧ Keeps clobbers (Foot env) s s') :=
  WP.mono (sampleChallengeM_spec h) (fun _ h ↦ h) fun _ h ↦ h.elim

/-- **One gadget into the working area.** -/
theorem oneTo_spec {g : Stmt} {m : VM EW}
    (hg : ∀ t s, CodeRel env t s → WP g s
      (fun s' ↦ ∃ x t', m.run t = some (x, t') ∧ CodeRel env t' s' ∧ s'.reg .r9 = x.c0 ∧
        s'.reg .r10 = x.c1 ∧ Keeps clobbers (Foot env) s s')
      (fun s' ↦ m.run t = none ∧ Keeps clobbers (Foot env) s s'))
    {k : Nat} {r : Region} (hr : Ok3 r) (hk : r.off ≤ k) (hk2 : k + 2 ≤ r.stop)
    (h : CodeRel env t s) (hi : Inputs env inp s.mem) :
    WP (oneTo g k) s
      (fun s' ↦ ∃ x t', m.run t = some (x, t') ∧ CodeRel env t' s' ∧
        EWAt s'.mem (wd env.work k) x ∧ Step3 env clobbers [r] s s')
      (fun s' ↦ m.run t = none ∧ Step3 env clobbers [r] s s') := by
  have hb := hr.bounds
  have hdl := dataEnd_le inp.bytecode.size
  have hww := workWords_lt hi
  unfold Region.stop at hk2 hb
  unfold oneTo
  refine WP.blk_cons (WP.mono (WP.frame (hg t s h)) ?_ ?_)
  · rintro s1 ⟨⟨x, t', hrun, hc, h9, h10, hkp⟩, hdom, -⟩
    have hs3 : Step3 env clobbers [] s s1 := Step3.ofKeeps hkp hdom
    have hin := hi.step3 (by simp) hs3 h.rdi
    have hs0 := hin.ok3_some' hr (a := k) (by unfold Region.stop; omega)
    have hs1 := hin.ok3_some' hr (a := k + 1) (by unfold Region.stop; omega)
    refine wp_load (eval_cw hc.rdi ctxWork) hc.workPtr3 ?_
    refine wp_reg rfl ?_
    refine wp_storePair (env := env) hr hk (by unfold Region.stop; omega) (by rsimp; rfl) (by simpa using hin)
      fun s2 hw he hreg ↦ WP.blk_nil ⟨x, t', hrun, ?_, ?_, ?_⟩
    · exact ((hc.setReg3 (by decide) _).setReg3 (by decide) _).wrote3 (by simpa using hin)
        (by simpa using hr) hw
    · rsimp at he; rw [h9, h10] at he; exact he
    · have hw1 : Wrote env [r] s1 s2 := (((Wrote.refl env [r] s1).setReg (r := .r11) (by decide)
        env.work).setReg (r := .r11) (by decide)
        ((s1.setReg .r11 env.work).reg .r11 + (wdisp k).toUInt64)).trans hw
      have hs4 : Step3 env [.r11] [r] s1 s2 := hw1.step' fun r' hr' ↦ by
        rw [hreg]; rsimp
        have : r' ≠ .r11 := fun e ↦ hr' (by simp [e])
        simp [this]
      exact (hs3.mono (regs' := clobbers) (ws' := [r]) (by simp) (by simp)).trans
        (hs4.mono (by simp [clobbers]) (by simp))
  · rintro s1 ⟨⟨hrun, hkp⟩, hdom, -⟩
    exact ⟨hrun, (Step3.ofKeeps hkp hdom).mono (by simp) (by simp)⟩

/-- **`readsTo k`**: `readScalars n`, `n` in `r12`, the scalars from word `k` of the working area,
inside the region `r`. -/
theorem readsTo_spec {n k : Nat} {r : Region} (hr : Ok3 r) (hk : r.off ≤ k) (hkn : k + 2 * n ≤ r.stop)
    (h : CodeRel env t s) (hi : Inputs env inp s.mem) (h12 : s.reg .r12 = n.toUInt64) :
    WP (readsTo k) s
      (fun s' ↦ ∃ xs t', (readScalars n).run t = some (xs, t') ∧ CodeRel env t' s' ∧
        xs.size = n ∧ EWArr s'.mem (wd env.work k) xs ∧ Step3 env clob3 [r] s s')
      (fun s' ↦ (readScalars n).run t = none ∧ Step3 env clob3 [r] s s') := by
  rw [readScalars_eq]
  exact loopTo_spec (fun _ _ h ↦ readScalarM_spec h) hr hk hkn h hi h12

/-- **`samplesTo k`**: `sampleChallenges n`, `n` in `r12`, the challenges from word `k` of the
working area, inside the region `r`; it never fails. -/
theorem samplesTo_spec {n k : Nat} {r : Region} (hr : Ok3 r) (hk : r.off ≤ k)
    (hkn : k + 2 * n ≤ r.stop) (h : CodeRel env t s) (hi : Inputs env inp s.mem)
    (h12 : s.reg .r12 = n.toUInt64) :
    WP (samplesTo k) s
      (fun s' ↦ ∃ xs t', (sampleChallenges n).run t = some (xs, t') ∧ CodeRel env t' s' ∧
        xs.size = n ∧ EWArr s'.mem (wd env.work k) xs ∧ Step3 env clob3 [r] s s')
      (fun _ ↦ False) := by
  rw [sampleChallenges_eq]
  refine WP.mono (loopTo_spec (fun _ _ h ↦ sample_spec' h) hr hk hkn h hi h12) (fun _ h ↦ h) ?_
  rintro _ ⟨hn, -⟩
  have := foldl_sample_some (List.range n) #[] t
  rw [show (List.range n).foldlM _ _ = pushes Model.sampleChallenge n from rfl, hn] at this
  exact absurd this (by simp)

/-- **`readTo k`**: `readScalar`, the scalar at words `k`, `k + 1` of the working area, inside the
region `r`. -/
theorem readTo_spec {k : Nat} {r : Region} (hr : Ok3 r) (hk : r.off ≤ k) (hk2 : k + 2 ≤ r.stop)
    (h : CodeRel env t s) (hi : Inputs env inp s.mem) :
    WP (readTo k) s
      (fun s' ↦ ∃ x t', Model.readScalar.run t = some (x, t') ∧ CodeRel env t' s' ∧
        EWAt s'.mem (wd env.work k) x ∧ Step3 env clobbers [r] s s')
      (fun s' ↦ Model.readScalar.run t = none ∧ Step3 env clobbers [r] s s') :=
  oneTo_spec (fun _ _ h ↦ readScalarM_spec h) hr hk hk2 h hi

/-- **`sampleTo k`**: `sampleChallenge`, the challenge at words `k`, `k + 1` of the working area,
inside the region `r`; it never fails. -/
theorem sampleTo_spec {k : Nat} {r : Region} (hr : Ok3 r) (hk : r.off ≤ k) (hk2 : k + 2 ≤ r.stop)
    (h : CodeRel env t s) (hi : Inputs env inp s.mem) :
    WP (sampleTo k) s
      (fun s' ↦ ∃ x t', Model.sampleChallenge.run t = some (x, t') ∧ CodeRel env t' s' ∧
        EWAt s'.mem (wd env.work k) x ∧ Step3 env clobbers [r] s s')
      (fun _ ↦ False) :=
  WP.mono (oneTo_spec (fun _ _ h ↦ sample_spec' h) hr hk hk2 h hi) (fun _ h ↦ h)
    fun _ ⟨hn, _⟩ ↦ by rw [NativeVm.Equiv.sampleChallenge_run] at hn; cases hn

end NativeVm.Code.P3
