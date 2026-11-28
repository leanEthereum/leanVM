module

public import NativeRustcVmArm.Spec.Whir
public import NativeRustcVmArm.Transcript.Callee
public import NativeRustcVm.Whir.Fold

/-!
# What `fold_rounds`, `next_level` and `final_level` share

The model: `foldRounds` one round more (`foldRounds_succ`), rejecting from a rejected round on
(`foldRounds_none_of`), a round's `α` pushed (`foldRound_alphas`). The calls from a frame of a
function holding WHIR's areas: the read-only data for a callee (`rodataAt_callee`), an output in
the frame apart from it (`rodataApart_frame`), a caller's output for the callee (`OutOk.callee`).
-/

namespace NativeRustcVmArm.Whir

open NativeRustcArm NativeVm.Model NativeRustcVm.Transcript NativeRustcVmArm.Transcript
open NativeRustcVm.Whir

public section

/-! ## The model -/

theorem foldRounds_zero (w : WhirStateW) (s : TState) :
    (foldRounds 0 w).run s = some ((w, #[]), s) := rfl

theorem foldRounds_succ (n : Nat) (w : WhirStateW) (s : TState) :
    (foldRounds (n + 1) w).run s = ((foldRounds n w).run s).bind fun p ↦
      ((foldRound p.1.1).run p.2).map fun q ↦ ((q.1.1, p.1.2.push q.1.2), q.2) := by
  unfold foldRounds
  rw [List.range_succ, List.foldlM_append, StateT.run_bind]
  show Option.bind _ _ = Option.bind _ _
  congr 1
  funext p
  rcases hm : (foldRound p.1.1).run p.2 with _ | ⟨⟨w', r⟩, s'⟩ <;>
    simp [List.foldlM_cons, List.foldlM_nil, hm]

theorem foldRounds_none_of {i : Nat} {w w' : WhirStateW} {rs : Array FoldRoundW} {s s' : TState}
    (h : (foldRounds i w).run s = some ((w', rs), s')) (hm : (foldRound w').run s' = none) :
    ∀ n, i < n → (foldRounds n w).run s = none := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rw [foldRounds_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
    · rw [ih hlt]; rfl
    · subst heq
      rw [h]
      show ((foldRound w').run s').map _ = none
      rw [hm]; rfl

theorem foldRounds_some {i : Nat} {w w' w'' : WhirStateW} {rs : Array FoldRoundW} {r : FoldRoundW}
    {s s' s'' : TState} (h : (foldRounds i w).run s = some ((w', rs), s'))
    (hm : (foldRound w').run s' = some ((w'', r), s'')) :
    (foldRounds (i + 1) w).run s = some ((w'', rs.push r), s'') := by
  rw [foldRounds_succ, h]
  show ((foldRound w').run s').map _ = _
  rw [hm]; rfl

theorem foldRound_alphas {w w' : WhirStateW} {r : FoldRoundW} {s s' : TState}
    (h : (foldRound w).run s = some ((w', r), s')) : w'.alphas.size = w.alphas.size + 1 := by
  rw [foldRound_run] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := h
  cases h
  simp [foldW]

/-! ## Calls -/

variable [Labels]

/-- The read-only data for a callee using `N'` bytes below an `F`-byte frame, memory changed only
apart from it. -/
theorem rodataAt_callee {m0 d : MachineData} {N F N' : Nat} {R : BitVec 64 → Prop}
    (h : RodataAt m0 N) (hs : SameOutside m0.dmem d.dmem R)
    (hR : ∀ q, R q → ∀ t : NativeRustcVm.Data.Item,
      ¬ NativeRustcVm.InRange (rodataAddr t) t.bytes.length q)
    (hsp : d.regs.SP.toBitVec = frameBase m0 F) (hn : N ≤ m0.regs.SP.toNat) (hF : F ≤ N)
    (hn' : N' ≤ N - F) : RodataAt d N' := fun t ↦ by
  obtain ⟨hb, hnw, hap⟩ := h t
  have hnw' : (rodataAddr t).toNat + t.bytes.length ≤ 2 ^ 64 := hnw
  refine ⟨bytesAt_congr hb fun i hi ↦ hs _ fun hr ↦ hR _ hr t (inRange_off_self hi (by omega)), hnw,
    apart_callee hap hsp hn hF hn'⟩

/-- Bytes inside the `N` bytes of stack are apart from the read-only data. -/
theorem rodataApart_stack {m0 : MachineData} {N : Nat} (h : RodataAt m0 N) {o : BitVec 64}
    {n : Nat} (h1 : (stackBelow m0 N).toNat ≤ o.toNat)
    (h2 : o.toNat + n ≤ (stackBelow m0 N).toNat + N) :
    NativeRustcVm.RodataApart rodataAddr o n := fun t ↦ by
  have := (h t).2.2
  unfold NativeRustcVm.Apart at this ⊢
  omega

/-- Bytes apart from the stack and the read-only data are apart from what a callee changes. -/
theorem rodata_not_stack {m0 : MachineData} {N : Nat} (h : RodataAt m0 N) (hn : N ≤ m0.regs.SP.toNat)
    (t : NativeRustcVm.Data.Item) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow m0 N) N q) :
    ¬ NativeRustcVm.InRange (rodataAddr t) t.bytes.length q := by
  have hsn : NativeRustcVm.NoWrap (stackBelow m0 N) N := by
    show _ + N ≤ _
    rw [toNat_stackBelow hn]; have := m0.regs.SP.toNat_lt; omega
  exact fun h' ↦ not_inRange_of_apart (h t).2.2 (h t).2.1 hsn h' hq

/-- An area apart from the read-only data holds none of its bytes. -/
theorem rodata_not_out {o : BitVec 64} {n : Nat} (h : NativeRustcVm.RodataApart rodataAddr o n)
    (hn : NativeRustcVm.NoWrap o n) (t : NativeRustcVm.Data.Item) {q : BitVec 64}
    (hq : NativeRustcVm.InRange o n q) (hr : NativeRustcVm.NoWrap (rodataAddr t) t.bytes.length) :
    ¬ NativeRustcVm.InRange (rodataAddr t) t.bytes.length q :=
  fun h' ↦ not_inRange_of_apart (h t) hn hr hq h'

/-- A caller's output for a callee using `N'` bytes below an `F`-byte frame. -/
theorem OutOk.callee {m0 d : MachineData} {t : BitVec 64} {a : DecArea} {o : BitVec 64}
    {n N F N' : Nat} (h : OutOk m0 t a o n N) (hk : Kept m0.dmem d.dmem)
    (hsp : d.regs.SP.toBitVec = frameBase m0 F) (hn : N ≤ m0.regs.SP.toNat) (hF : F ≤ N)
    (hn' : N' ≤ N - F) : OutOk d t a o n N' :=
  ⟨Mapped.keeps h.1 hk, h.2.1, h.2.2.1, h.2.2.2.1, apart_callee h.2.2.2.2.1 hsp hn hF hn',
    h.2.2.2.2.2⟩

end

end NativeRustcVmArm.Whir
