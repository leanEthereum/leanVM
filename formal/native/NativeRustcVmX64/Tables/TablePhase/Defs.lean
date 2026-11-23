module

public import NativeRustcVmX64.Tables.TablePhase.Exec
public import NativeRustcVmX64.Bus.GkrCommon
public import NativeRustcVmX64.Spec.Tables
public import NativeRustcVm.Tables.Phase
public import NativeRustcVm.Tables.Same

/-!
# `table_phase`'s frame (x86-64)

The frame (`Bus.Gkr.Fr`, `F = 160`) with the outputs the `TState` (RDI) and the evaluations (RCX,
`outs`). A callee entered with RSP at the frame's offset `c` uses `Nc` bytes below it,
`160 - c + Nc ≤ tablePhaseStack`: an input for it (`readIn_call`), the read-only data
(`rodata_call`); an input kept (`same_in`); the `TState` kept across changes apart from it
(`tstate_keep`).
-/

namespace NativeRustcVmX64.Tables.TablePhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmX64.Bus.Gkr (Fr)
open NativeRustcVm.Layout (LayoutWAt layoutBytes Same)
open NativeRustcVm.Bus (BusWAt busBytes)

@[expose] public section

/-- The stack. -/
abbrev N : Nat := tablePhaseStack

/-- The outputs: the `TState` (RDI) and the evaluations (RCX). -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
    NativeRustcVm.InRange (reg m0 .rcx) tableEvalsBytes q

/-- The written regions. -/
def wsOf (m0 : MachineData) : List NativeRustcVm.Region :=
  [⟨reg m0 .rdi, tstateBytes⟩, ⟨reg m0 .rcx, tableEvalsBytes⟩]

/-- The frame. -/
abbrev St (m0 : MachineData) (o : Nat) (d : MachineData) : Prop := Fr m0 160 N slots (outs m0) o d

end

public section

theorem N_ge : 160 ≤ N := by decide
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 160 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

section
variable [Labels] {a : DecArea} {s : TState} {L : LayoutW} {bus : BusResultW} {m0 : MachineData}

theorem pre_parts (h : TablePhasePre a s L bus m0) :
    StackOk m0 N ∧ RcAt m0 N ∧ TablesAt m0 N ∧ TStateAt m0.dmem (reg m0 .rdi) a s ∧
      TStateOk m0 (reg m0 .rdi) a N ∧ OutOk m0 (reg m0 .rdi) a (reg m0 .rcx) tableEvalsBytes N ∧
      RodataApart (reg m0 .rdi) tstateBytes ∧ RodataApart (reg m0 .rcx) tableEvalsBytes ∧
      ReadIn m0 (reg m0 .rsi) layoutBytes N (wsOf m0) ∧ LayoutWAt m0.dmem (reg m0 .rsi) L ∧
      ReadIn m0 (reg m0 .rdx) busBytes N (wsOf m0) ∧ BusWAt m0.dmem (reg m0 .rdx) bus := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem got (h : TablePhasePre a s L bus m0) :
    GotAt m0 N [(reg m0 .rdi, tstateBytes), (a.words, 8 * a.len),
      (reg m0 .rcx, tableEvalsBytes), (reg m0 .rsi, layoutBytes), (reg m0 .rdx, busBytes),
      (rcAddr, 192), (rodataAddr .tables, NativeRustcVm.Data.Item.tables.bytes.length)] ["memcpy"] :=
  h.2.2.2.2.2.2.2.2.2.2.2.2

theorem ctx (h : TablePhasePre a s L bus m0) {F : Nat} (hF : F ≤ N) : Ctx m0 (reg m0 .rdi) a N F :=
  let p := pre_parts h
  ⟨p.1, p.2.1, p.2.2.2.2.1, p.2.2.2.1.footprint, hF⟩

/-- The outputs are apart from the frame. -/
theorem outs_not_frame (h : TablePhasePre a s L bus m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬NativeRustcVm.InRange (stackBelow m0 160) (160 + 8) q := by
  have p := pre_parts h
  have c := ctx h N_ge
  have hfr : NativeRustcVm.NoWrap (stackBelow m0 160) (160 + 8) := c.noWrap_frame
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange
      (apart_frame p.2.2.2.2.1.1 c.spN N_ge) p.2.2.2.1.footprint.1.2 hfr hq
  · exact NativeRustcVm.Apart.not_inRange
      (apart_frame p.2.2.2.2.2.1.2.2.2.2.1 c.spN N_ge) p.2.2.2.2.2.1.2.1 hfr hq

theorem outs_not_rc (h : TablePhasePre a s L bus m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬NativeRustcVm.InRange rcAddr 192 q := by
  have c := ctx h N_ge
  rcases hq with hq | hq
  · exact c.not_rc_tstate hq
  · exact c.out_not_rc (pre_parts h).2.2.2.2.2.1 hq

/-- **An input kept** in the frame's states. -/
theorem same_in (h : TablePhasePre a s L bus m0) {o : Nat} {d : MachineData} (fr : St m0 o d)
    {x : BitVec 64} {n : Nat} (hx : ReadIn m0 x n N (wsOf m0)) : Same m0.dmem d.dmem x n := by
  have c := ctx h N_ge
  obtain ⟨⟨-, hnw⟩, hO, hW⟩ := hx
  intro j hj
  refine fr.same _ fun hq ↦ ?_
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange_add hO hnw c.noWrap_stack hj (inRange_mono hq (by omega))
  · exact NativeRustcVm.Apart.not_inRange_add (hW ⟨reg m0 .rdi, tstateBytes⟩ (by simp [wsOf])) hnw
      (pre_parts h).2.2.2.1.footprint.1.2 hj hq
  · exact NativeRustcVm.Apart.not_inRange_add (hW ⟨reg m0 .rcx, tableEvalsBytes⟩ (by simp [wsOf]))
      hnw (pre_parts h).2.2.2.2.2.1.2.1 hj hq

/-- At a call from the frame's offset `o`. -/
theorem at_call (h : TablePhasePre a s L bus m0) {o : Nat} {d : MachineData} (fr : St m0 o d)
    (ho : o ≤ 160) : At m0 (160 - o) d :=
  fr.at_ (ctx h N_ge) ho (fun _ hq ↦ outs_not_rc h hq)

theorem got_call (h : TablePhasePre a s L bus m0) {o Nc : Nat} {d : MachineData}
    (fr : St m0 o d) (ho : o ≤ 160) (hle : 160 - o + Nc ≤ N)
    {areas : List (BitVec 64 × Nat)}
    (ha : ∀ l ∈ ["memcpy"], ∀ b ∈ areas, Apart (gotAddr l) 8 b.1 b.2) :
    GotAt d Nc areas ["memcpy"] := by
  have p := pre_parts h
  refine got_callee (got h) (got_keep (got h) p.1
    (writes := [(reg m0 .rdi, tstateBytes), (reg m0 .rcx, tableEvalsBytes)])
    (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;> simp)
    (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact p.2.2.2.1.footprint.1.2
      · exact p.2.2.2.2.2.1.2.1)
    (by
      intro q hq
      apply fr.same q
      rintro (hs | ht | he)
      · exact hq (Or.inr hs)
      · exact hq (Or.inl ⟨(reg m0 .rdi, tstateBytes), by simp, ht⟩)
      · exact hq (Or.inl ⟨(reg m0 .rcx, tableEvalsBytes), by simp, he⟩)))
    (at_call h fr ho).sp p.1.1 hle ha

/-- **An input for a callee** at the frame's offset `c`. -/
theorem readIn_call (h : TablePhasePre a s L bus m0) {o : Nat} {d : MachineData} (fr : St m0 o d)
    (ho : o ≤ 160) {Nc : Nat} (hle : 160 - o + Nc ≤ N) {x : BitVec 64} {n : Nat}
    (hx : ReadIn m0 x n N (wsOf m0)) : ReadIn d x n Nc (wsOf m0) := by
  have hat := at_call h fr ho
  exact ⟨⟨Mapped.keeps hx.1.1 fr.frame.kept, hx.1.2⟩,
    (ctx h (F := 160 - o) (by omega)).apart hat hle hx.2.1, hx.2.2⟩

/-- **The `TState` kept** where the memory changed apart from it and its area. -/
theorem tstate_keep (h : TablePhasePre a s L bus m0) {d d' : DataMem} {R : BitVec 64 → Prop}
    {s' : TState} (hts : TStateAt d (reg m0 .rdi) a s') (hk : Kept d d')
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 N) N q ∨
      NativeRustcVm.InRange (reg m0 .rcx) tableEvalsBytes q) :
    TStateAt d' (reg m0 .rdi) a s' := by
  have c := ctx h N_ge
  have ho := (pre_parts h).2.2.2.2.2.1
  refine hts.frame hk (fun q hq ↦ ?_) hs
  rcases hR q hq with hq' | hq'
  · exact c.stack_not_t hq'
  · exact c.out_not_t ho hq'

/-- **The read-only data** for a callee at the frame's offset `o`. -/
theorem rodata_call (h : TablePhasePre a s L bus m0) {o : Nat} {d : MachineData} (fr : St m0 o d)
    (ho : o ≤ 160) {Nc : Nat} (hle : 160 - o + Nc ≤ N) : RodataAt d Nc := by
  have p := pre_parts h
  have c := ctx h N_ge
  have hat := at_call h fr ho
  have hT : NativeRustcVm.RodataAt m0.dmem rodataAddr (stackBelow m0 N) (N + 8) := p.2.2.1
  intro t
  obtain ⟨hb, hnw, hap⟩ := hT t
  refine ⟨fun i hi ↦ ?_, hnw, apart_callee hap hat.sp c.spN hle⟩
  rw [fr.same _ fun hq ↦ ?_]
  · exact hb i hi
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange_add hap hnw c.noWrap_stack hi (inRange_mono hq (by omega))
  · exact NativeRustcVm.Apart.not_inRange_add (NativeRustcVm.Apart.symm (p.2.2.2.2.2.2.1 t)) hnw
      p.2.2.2.1.footprint.1.2 hi hq
  · exact NativeRustcVm.Apart.not_inRange_add (NativeRustcVm.Apart.symm (p.2.2.2.2.2.2.2.1 t)) hnw
      p.2.2.2.2.2.1.2.1 hi hq

end

end

end NativeRustcVmX64.Tables.TablePhase
