module

public import NativeRustcVmArm.Whir.SampleQueries.Calls

/-!
# `sample_queries`: the entry

`b0` clears the output's count word and returns at once for no position (`b6`); else the prologue
(`b1`) saves X19 to X30 in the 112-byte frame (`fr_entry`, the frame relative to the entry).
-/

namespace NativeRustcVmArm.Whir.SampleQueries

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.SampleQueries
open NativeRustcVm (BufWordsAt WordsAt WordAt)

public section

variable [Labels] {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- The entry's environment: the frame, the output's count word. -/
abbrev entryEnv (m0 : MachineData) : Env :=
  Env.ofMachine m0 [(base m0 112, 112), (oA m0, 8)]

omit [Labels] in
theorem eight_le : 8 ≤ queryBufBytes := by decide
omit [Labels] in
theorem N_val : sampleQueriesStack = 544 := rfl

theorem entry_wf (h : SampleQueriesPre a s0 m0) : (entryEnv m0).WF := by
  have hN := pre_N h
  have hNv := N_val
  obtain ⟨⟨hmo, hno, hot, hod, hos, hor⟩, -⟩ := h.2.2.2
  refine Env.wf_of ⟨⟨?_, base_noWrap (by omega)⟩, ⟨?_, ?_⟩, trivial⟩ ?_
  · have hmap := (pre_stack h).2.2
    intro i hi
    have := hmap (sampleQueriesStack - 112 + i) (by omega)
    rwa [show m0.regs.SP.toBitVec - BitVec.ofNat 64 sampleQueriesStack +
      BitVec.ofNat 64 (sampleQueriesStack - 112 + i) = base m0 112 + BitVec.ofNat 64 i by
      rw [← base_add (F := 112) (by omega) hN, NativeRustcVm.addr_add_add]; rfl] at this
  · exact NativeRustcVm.Mapped.mono hmo eight_le
  · exact NativeRustcVm.NoWrap.mono hno eight_le
  · refine List.pairwise_pair.mpr ?_
    have e1 := base_toNat (m0 := m0) (F := 112) (by omega)
    have e2 := base_toNat (m0 := m0) (F := sampleQueriesStack) hN
    have := hos
    unfold Apart at this ⊢
    simp only [stackBelow] at this
    show (base m0 112).toNat + 112 ≤ m0.regs.X3.toBitVec.toNat ∨
      m0.regs.X3.toBitVec.toNat + 8 ≤ (base m0 112).toNat
    rw [show m0.regs.SP.toBitVec - BitVec.ofNat 64 sampleQueriesStack = base m0 sampleQueriesStack
      from rfl, e2] at this
    have : queryBufBytes = 1848 := rfl
    omega

/-- **The frame after the prologue**, from the entry's environment: the slots written, the other
writes in the frame or the count word. -/
theorem fr_entry (h : SampleQueriesPre a s0 m0) {S : SState} {st : MachineData}
    (hm : Match (entryEnv m0) S st) (hsp : S.sp = .ptr 0 0) (hok : slotsOk S slots = true)
    (hmem : ∀ w ∈ S.mem, (w.r = 0 ∧ w.off + w.n ≤ 112) ∨ (w.r = 1 ∧ w.off + w.n ≤ 8)) :
    SFr m0 st where
  sp := by rw [hm.sp, hsp]; simp [Sym.eval]
  keep r hr := by cases hr
  slots p hp := by
    have hw := hm.bytesAt_write (r := 0) (o := p.1) (n := 8) (b := base m0 112) (sz := 112) rfl
      (by simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            decide)
      (v := .reg p.2) fun i hi ↦ slotsOk_iff hok p hp i hi
    rw [wordBytes_reg] at hw
    exact hw
  same q hq := by
    have hN := pre_N h
    have hwf := entry_wf h
    obtain ⟨⟨hmo, hno, -⟩, -⟩ := h.2.2.2
    refine hm.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hq ?_
    rcases hmem w hw with ⟨hr, hn⟩ | ⟨hr, hn⟩
    · rw [hr] at hb
      cases hb
      left
      have e1 := base_toNat (m0 := m0) (F := 112) (by have := N_val; omega)
      rw [Sym.inRange_iff (base_noWrap hN), base_toNat hN]
      rw [e1] at h1 h2
      have := N_val
      omega
    · rw [hr] at hb
      cases hb
      right; left
      rw [Sym.inRange_iff hno]
      have := eight_le
      change (oA m0).toNat + w.off ≤ q.toNat at h1
      change q.toNat < (oA m0).toNat + w.off + w.n at h2
      show (oA m0).toNat ≤ q.toNat ∧ q.toNat < (oA m0).toNat + queryBufBytes
      omega
  kept := hm.kept (entry_wf h)

end

end NativeRustcVmArm.Whir.SampleQueries
