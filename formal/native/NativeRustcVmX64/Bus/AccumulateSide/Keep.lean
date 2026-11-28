module

public import NativeRustcVmX64.Bus.AccumulateSide.TKit

/-!
# `accumulate_side`: the forms and the frame's `FormBuf` kept (x86-64)

A block writing the frame below its offset `6056` changes neither the forms nor the frame's
`FormBuf` (`run_keep`); a callee changing its stack, a part of the frame below `6056` and outputs
apart from the frame keeps the frame's `FormBuf` (`call_fbuf`), and the forms if it writes no
output (`call_forms`).
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

/-- The frame's `FormBuf`. -/
abbrev FB [Labels] (m0 : MachineData) (d : Mem 64) (g : FormW) : Prop :=
  FormBufAt d (off (fb m0) 6056) g

end

public section

variable [Labels] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData}

/-- Bytes outside the frame and the frame's from `6056` kept. -/
def KeepF (m0 : MachineData) (d d' : Mem 64) : Prop :=
  (∀ q, ¬ NativeRustcVm.InRange (fb m0) (F + 8) q → d'.get? q = d.get? q) ∧
    ∀ j, 6056 ≤ j → j < F + 8 → d'.get? (off (fb m0) j) = d.get? (off (fb m0) j)

/-- **A block writing the frame below `6056`.** -/
theorem run_keep {rest : List (BitVec 64 × Nat)}
    {vs : Nat → BitVec 64} {ret : BitVec 64} {S : SState} {m m' : MachineData}
    (hwf : (frameEnv m0 m F rest vs ret).WF) (hm : Match (frameEnv m0 m F rest vs ret) S m')
    (hw : lowW' S) (hin : writesIn S = true) : KeepF m0 m.dmem m'.dmem := by
  have hw' : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 6056 := fun w hw1 ↦ by
    have := List.all_eq_true.mp hw w hw1
    simpa using this
  have hbr : belowRet F S = true := List.all_eq_true.mpr fun w hw1 ↦ by
    have := hw' w hw1
    simp [this.1]; have hF : F = 12032 := rfl; omega
  refine ⟨fun q hq ↦ hm.get?_mem0 hwf fun hW ↦ hq (Ring.inRange_le
    (written_low hwf (fun w hw1 ↦ (hw' w hw1).1) hbr hW) (by omega)), fun j hj1 hj2 ↦ ?_⟩
  exact hm.get?_mem0 hwf (not_written0 hwf hm hin hj2 fun w hw1 _ ↦ .inl (by
    have := hw' w hw1; omega))

omit [Labels] in
theorem KeepF.trans {d d' d'' : Mem 64} (h : KeepF m0 d d') (h' : KeepF m0 d' d'') :
    KeepF m0 d d'' :=
  ⟨fun q hq ↦ (h'.1 q hq).trans (h.1 q hq), fun j h1 h2 ↦ (h'.2 j h1 h2).trans (h.2 j h1 h2)⟩

/-- **A callee** changing its stack, frame bytes below `6056` and outputs apart from the frame. -/
theorem call_fbuf (h : Pre L rows bl Fm SL m0) {st m2 : MachineData} (hsp : rspOf st = fb m0)
    {Nc lo n : Nat} (hle : F + Nc ≤ N) (hlo : lo + n ≤ 6056) {W : BitVec 64 → Prop}
    (hW : ∀ q, W q → ¬ NativeRustcVm.InRange (fb m0) (F + 8) q)
    (hso : NativeRustcVm.SameOutside st.dmem m2.dmem (fun q ↦
      NativeRustcVm.InRange (stackBelow st Nc) Nc q ∨
        NativeRustcVm.InRange (off (fb m0) lo) n q ∨ W q)) :
    ∀ j, 6056 ≤ j → j < F + 8 →
      m2.dmem.get? (off (fb m0) j) = st.dmem.get? (off (fb m0) j) := fun j h1 h2 ↦
  hso _ fun hq ↦ by
    rcases hq with hq | hq | hq
    · exact h.not_callee hsp hle h2 hq
    · exact h.not_loc h2 (by omega) (.inr (by omega)) hq
    · exact hW _ hq (inRange_off_self h2
        (by have := h.frame_nw; unfold NativeRustcVm.NoWrap at this; omega))

/-- **A callee writing no output** keeps the bytes outside the frame and the stack. -/
theorem call_out (h : Pre L rows bl Fm SL m0) {st m2 : MachineData} (hsp : rspOf st = fb m0)
    {Nc lo n : Nat} (hle : F + Nc ≤ N) (hlo : lo + n ≤ F + 8)
    (hso : NativeRustcVm.SameOutside st.dmem m2.dmem (fun q ↦
      NativeRustcVm.InRange (stackBelow st Nc) Nc q ∨
        NativeRustcVm.InRange (off (fb m0) lo) n q ∨ Z q)) {q : BitVec 64}
    (hq : ¬ NativeRustcVm.InRange (stackBelow m0 N) N q)
    (hqf : ¬ NativeRustcVm.InRange (fb m0) (F + 8) q) : m2.dmem.get? q = st.dmem.get? q :=
  hso _ fun hq' ↦ by
    rcases hq' with hq' | hq' | hq'
    · exact hq (inRange_callee hsp h.sp8 h.spN hle hq').1
    · exact hqf (inRange_of_off h.frame_nw hlo hq')
    · exact hq'.elim

/-- A byte of the forms is outside the frame and the stack. -/
theorem forms_out (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < formsBytes) :
    ¬ NativeRustcVm.InRange (fb m0) (F + 8) (reg m0 .rsi + BitVec.ofNat 64 j) ∧
      ¬ NativeRustcVm.InRange (stackBelow m0 N) N (reg m0 .rsi + BitVec.ofNat 64 j) :=
  ⟨h.outs_frame (NativeRustcVm.inRange_add hj (by have := h.forms_nw; unfold NativeRustcVm.NoWrap at this; omega)),
    fun hq ↦ NativeRustcVm.Apart.not_inRange_add h.formsOk.2 h.forms_nw (noWrap_stackBelow h.stack)
      hj (Ring.inRange_le hq (by omega))⟩

/-- **The forms** across a block writing the frame. -/
theorem KeepF.forms (h : Pre L rows bl Fm SL m0) {d d' : Mem 64} (hk : KeepF m0 d d')
    {G : Array (Array FormW)} (hG : FormsAt d (reg m0 .rsi) G) : FormsAt d' (reg m0 .rsi) G :=
  FormsAt.of_same hG fun _ hj ↦ hk.1 _ (forms_out h hj).1

/-- **The frame's `FormBuf`** across a block writing the frame below `6056`. -/
theorem KeepF.fbuf {d d' : Mem 64} (hk : KeepF m0 d d') {g : FormW} (hg : FB m0 d g) :
    FB m0 d' g :=
  NativeRustcVm.Tables.FormBufAt.of_same hg fun _ hj ↦ by
    have hb : formBufBytes = 5928 := rfl
    rw [off_add]
    exact hk.2 _ (by omega) (by rw [hb] at hj; have hF : F = 12032 := rfl; omega)

/-- **The forms** across a callee writing no output. -/
theorem call_forms (h : Pre L rows bl Fm SL m0) {st m2 : MachineData} (hsp : rspOf st = fb m0)
    {Nc lo n : Nat} (hle : F + Nc ≤ N) (hlo : lo + n ≤ F + 8)
    (hso : NativeRustcVm.SameOutside st.dmem m2.dmem (fun q ↦
      NativeRustcVm.InRange (stackBelow st Nc) Nc q ∨
        NativeRustcVm.InRange (off (fb m0) lo) n q ∨ Z q))
    {G : Array (Array FormW)} (hG : FormsAt st.dmem (reg m0 .rsi) G) :
    FormsAt m2.dmem (reg m0 .rsi) G :=
  FormsAt.of_same hG fun _ hj ↦
    call_out h hsp hle hlo hso (forms_out h hj).2 (forms_out h hj).1

/-- **The frame's `FormBuf`** across a callee. -/
theorem call_fb (h : Pre L rows bl Fm SL m0) {st m2 : MachineData} (hsp : rspOf st = fb m0)
    {Nc lo n : Nat} (hle : F + Nc ≤ N) (hlo : lo + n ≤ 6056) {W : BitVec 64 → Prop}
    (hW : ∀ q, W q → ¬ NativeRustcVm.InRange (fb m0) (F + 8) q)
    (hso : NativeRustcVm.SameOutside st.dmem m2.dmem (fun q ↦
      NativeRustcVm.InRange (stackBelow st Nc) Nc q ∨
        NativeRustcVm.InRange (off (fb m0) lo) n q ∨ W q))
    {g : FormW} (hg : FB m0 st.dmem g) : FB m0 m2.dmem g :=
  NativeRustcVm.Tables.FormBufAt.of_same hg fun _ hj ↦ by
    have hb : formBufBytes = 5928 := rfl
    rw [off_add]
    exact call_fbuf h hsp hle hlo hW hso _ (by omega)
      (by rw [hb] at hj; have hF : F = 12032 := rfl; omega)

/-- **Frame bytes from `o ≥ 8`** for a callee: readable, apart from its stack. -/
theorem frame_inOk (h : Pre L rows bl Fm SL m0) {m : MachineData} (hk : Kept m0.dmem m.dmem)
    (hsp : rspOf m = fb m0) {Nc : Nat} (hle : F + Nc ≤ N) {o n : Nat} (h8 : 8 ≤ o)
    (hon : o + n ≤ F + 8) (hn : 0 < n) : InOk m (off (fb m0) o) n Nc := by
  have hnw := h.frame_nw
  unfold NativeRustcVm.NoWrap at hnw
  have hfbN := h.fbN
  have hF : F = 12032 := rfl
  have := h.spN
  have := h.sp8
  have hoN : (off (fb m0) o).toNat = (fb m0).toNat + o := toNat_off (by omega)
  refine ⟨⟨mapped_off (Mapped.keeps (frame_mapped h.stack le_F) hk) hon, ?_⟩, ?_⟩
  · show NativeRustcVm.NoWrap _ _
    unfold NativeRustcVm.NoWrap; omega
  · show NativeRustcVm.Apart _ _ _ _
    rw [stackBelow_callee hsp (by have := h.spN; omega)]
    unfold NativeRustcVm.Apart
    have hs := stackBelow_toNat (m := m0) (n := F + Nc) (by omega)
    rw [hoN, hs]
    omega

end

end NativeRustcVmX64.Bus.AccumulateSide
