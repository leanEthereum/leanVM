module

public import NativeRustcVmArm.Bus.AccumulateSide.Facts
public import NativeRustcVm.Tables.Same

/-!
# `accumulate_side`: the blocks' environments, the forms beside them

The regions a block of the body reads besides the frame (`ROk`): readable, apart from the stack
and, where the block also reads the stack arguments, from them; the environment is well formed
(`wfB`). The forms (`FormsAt` at X1) over bytes that stayed the same (`FormsAt.of_same`):
through a block writing the frame (`forms_block`), through a call writing its stack
(`forms_call`).
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

theorem allOf_of {α : Type} {P : α → Prop} : ∀ {l : List α}, (∀ a ∈ l, P a) → AllOf P l
  | [], _ => trivial
  | a :: _, h => ⟨h a (List.mem_cons_self ..), allOf_of fun b hb ↦ h b (List.mem_cons_of_mem _ hb)⟩

/-- The forms over bytes that stayed the same. -/
theorem FormsAt.of_same {d d' : Mem 64} {a : BitVec 64} {G : Array (Array FormW)}
    (h : FormsAt d a G) (hs : Same d d' a formsBytes) : FormsAt d' a G := by
  have hf : formBufBytes = 5928 := rfl
  have hb : formsBytes = 106704 := rfl
  refine ⟨h.size, h.row_size, fun t ht s hs' ↦ ?_⟩
  have h1 := h.row_size t ht
  have h2 := h.size
  exact NativeRustcVm.Tables.FormBufAt.of_same (h.forms t ht s hs')
    (hs.sub (by rw [hb, hf]; unfold nTables at h2; omega))

/-- A region a block reads besides the frame and `A` bytes above it. -/
@[expose] def ROk (m0 : MachineData) (A : Nat) (e : BitVec 64 × Nat) : Prop :=
  0 < e.2 ∧ Readable m0 e.1 e.2 ∧ OffStack m0 e.1 e.2 N ∧
    (0 < A → Apart e.1 e.2 m0.regs.SP.toBitVec A)

section
variable [Labels] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

/-- **A block's environment**: the frame and `A` (`0` or `72`) bytes above it, regions `rs`
apart. -/
theorem wfB (h : Pre L rows bl Fm SL m0) {m : MachineData} (hk : Kept m0.dmem m.dmem) {A : Nat}
    (hA : A = 0 ∨ A = 72) {rs : List (BitVec 64 × Nat)} (hrs : ∀ e ∈ rs, ROk m0 A e)
    (hd : rs.Pairwise fun e e' ↦ Apart e.1 e.2 e'.1 e'.2) :
    (Env.ofMachine m ((base m0 F, F + A) :: rs)).WF := by
  have hN := h.stack.2.1
  have hb := base_toNat (m0 := m0) (F := F) (by rw [N_eq] at hN; show 12096 ≤ _; omega)
  have hsb : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
  have hsp := sp_toNat m0
  have hF : F = 12096 := rfl
  have hNe := N_eq
  refine Env.wf_of ⟨?_, allOf_of fun e he ↦
    ⟨fun i hi ↦ hk _ ((hrs e he).2.1.1 i hi), (hrs e he).2.1.2⟩⟩
    (List.Pairwise.cons (fun e he ↦ ?_) hd)
  · rcases hA with rfl | rfl
    · have := Bus.frame_mapped h.stack (show F ≤ N by decide)
      exact ⟨fun i hi ↦ hk _ (this.1 i hi), this.2⟩
    · exact mappedA h hk
  · obtain ⟨hpos, -, hoff, hsa⟩ := hrs e he
    unfold OffStack Apart at hoff
    show Apart (base m0 F) (F + A) e.1 e.2
    unfold Apart
    rcases hA with rfl | rfl
    · omega
    · have := hsa (by omega)
      unfold Apart at this
      omega

theorem forms_nw (h : Pre L rows bl Fm SL m0) : NoWrap m0.regs.X1.toBitVec formsBytes :=
  h.formsOk.1.2

/-- **The forms through a block** writing only the frame and the stack arguments. -/
theorem forms_block (h : Pre L rows bl Fm SL m0) {m st : MachineData} {A : Nat}
    (hA : A = 0 ∨ A = 72) {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S st)
    (hwf : (Env.ofMachine m ((base m0 F, F + A) :: rs)).WF)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F + A) {G : Array (Array FormW)}
    (hG : FormsAt m.dmem m0.regs.X1.toBitVec G) : FormsAt st.dmem m0.regs.X1.toBitVec G := by
  have hN := h.stack.2.1
  have hNe := N_eq
  have hF : F = 12096 := rfl
  have hb := base_toNat (m0 := m0) (F := F) (by rw [N_eq] at hN; show 12096 ≤ _; omega)
  have hsb : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
  have hsp := sp_toNat m0
  have hoff := h.formsOk.2
  have hfa := h.fArgs
  have hnw := forms_nw h
  have hbnw : NoWrap (base m0 F) (F + A) := by
    unfold NoWrap; rw [hb]; have := argsNW h; rcases hA with rfl | rfl <;> omega
  refine FormsAt.of_same hG (Same.of_sameOutside (hm.sameOutside hwf) fun j hj hq ↦ ?_)
  have hin := Written.inRange (r := 0) rfl hbnw hw hq
  rw [Sym.inRange_iff hbnw, hb] at hin
  unfold OffStack Apart at hoff
  unfold Apart at hfa
  unfold NoWrap at hnw
  have : formsBytes = 106704 := rfl
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at hin
  rcases hA with rfl | rfl <;> omega

/-- The forms through a block of the body (`wrOk`). -/
theorem forms_wrOk (h : Pre L rows bl Fm SL m0) {m st : MachineData} {A : Nat}
    (hA : A = 0 ∨ A = 72) {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S st)
    (hwf : (Env.ofMachine m ((base m0 F, F + A) :: rs)).WF) (hw : wrOk S = true)
    {G : Array (Array FormW)} (hG : FormsAt m.dmem m0.regs.X1.toBitVec G) :
    FormsAt st.dmem m0.regs.X1.toBitVec G :=
  forms_block h hA hm hwf (fun w hw' ↦ by
    have := List.all_eq_true.mp hw w hw'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1, by have hF : F = 12096 := rfl; omega⟩) hG

/-- **The forms through a call** writing its `N'` bytes of stack below the frame. -/
theorem forms_call (h : Pre L rows bl Fm SL m0) {st m2 : MachineData}
    (hsp : st.regs.SP.toBitVec = base m0 F) {N' : Nat} (hle : F + N' ≤ N)
    (hs : SameOutside st.dmem m2.dmem (InRange (stackBelow st N') N'))
    {G : Array (Array FormW)} (hG : FormsAt st.dmem m0.regs.X1.toBitVec G) :
    FormsAt m2.dmem m0.regs.X1.toBitVec G := by
  have hN := h.stack.2.1
  have hoff := h.formsOk.2
  have hnw := forms_nw h
  have hsb : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
  have hsb' : (stackBelow st N').toNat = m0.regs.SP.toNat - (F + N') := by
    rw [stackBelow_eq hsp (by omega)]; exact base_toNat (by omega)
  have hcnw : NoWrap (stackBelow st N') N' := by
    unfold NoWrap; rw [hsb']; have := m0.regs.SP.toNat_lt; omega
  refine FormsAt.of_same hG (Same.of_sameOutside hs fun j hj hq ↦ ?_)
  rw [Sym.inRange_iff hcnw, hsb'] at hq
  unfold OffStack Apart at hoff
  unfold NoWrap at hnw
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at hq
  omega

/-! ## Evaluating symbolic values -/

/-- A location of a description evaluates to its value. -/
theorem ev_of {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64} {D : List (Sym × Nat)}
    {m : MachineData} (hH : Holds rs V D m) {s : Sym} {i : Nat} (hp : (s, i) ∈ D) :
    s.eval (Env.ofMachine m rs) = (V i).toBitVec := by
  rw [← hH _ hp]
  rfl

/-- A word of region `r`. -/
theorem load_rk {m : MachineData} {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {r o n : Nat} {b : BitVec 64} (hb : rs[r]? = some (b, n)) :
    (Sym.load r o 8).eval (Env.ofMachine m rs vars) =
      (NativeRustcVm.wordOf m.dmem (b + BitVec.ofNat 64 o)).toBitVec := by
  show Env.load _ r o 8 = _
  rw [load_eq_wordOf, Env.base_ofMachine m rs vars hb]
  rfl

theorem cmp_eq_lit (env : Env) {s : Sym} {x : UInt64} (hs : s.eval env = x.toBitVec) {c : Nat}
    (hc : c < 2 ^ 64) : SBool.eval env (.cmp .eq .W64 s (.lit c)) = decide (x.toNat = c) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, hs, Sym.eval]
  by_cases h : x.toNat = c
  · simp only [h, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat]
    omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he
    have := congrArg BitVec.toNat he
    simp only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat] at this
    omega

theorem cmp_ult_lit (env : Env) {s : Sym} {x : UInt64} (hs : s.eval env = x.toBitVec) {c : Nat}
    (hc : c < 2 ^ 64) : SBool.eval env (.cmp .ult .W64 s (.lit c)) = decide (x.toNat < c) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, hs, Sym.eval, BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hc]
  rfl

theorem cmp_ult (env : Env) {s t : Sym} {x y : UInt64} (hs : s.eval env = x.toBitVec)
    (ht : t.eval env = y.toBitVec) :
    SBool.eval env (.cmp .ult .W64 s t) = decide (x.toNat < y.toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, hs, ht, BitVec.ult]
  rfl

/-- A register a block computed, a location of a description. -/
theorem holds_reg {rs rs' : List (BitVec 64 × Nat)} {m st : MachineData} {S : SState}
    (hm : Match (Env.ofMachine m rs) S st) {r : XReg} {s : Sym} (h : S.reg r = some s)
    {V : Nat → UInt64} {i : Nat} (hv : UInt64.ofBitVec (s.eval (Env.ofMachine m rs)) = V i) :
    Holds rs' V [(.reg r, i)] st :=
  holds_one ((tval_reg_of hm h).trans hv)

end

end

end NativeRustcVmArm.Bus.AccumulateSide
