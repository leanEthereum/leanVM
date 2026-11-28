module

public import NativeRustcVmX64.Whir.SampleQueries.Exit

/-!
# `sample_queries` on x86-64: the entry

From the entry, region 0 the frame and region 1 the buffer's count word (`entryEnv`): `b0` pushes
the registers and clears the count; an empty count returns at once (`b19`, `ret0`); `b1` keeps the
count, the depth and the `TState` (a depth above `128` on to the squeezes' loop, `big0`); `b2`
the outer loop's start (`outer0`).
-/

namespace NativeRustcVmX64.Whir.SampleQueries

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.SampleQueries
open NativeRustcVmX64.Transcript (Frame frameEnv)
open NativeRustcVm (BufWordsAt WordsAt WordAt)

@[expose] public section

/-- The entry's environment: the frame, the buffer's count word. -/
abbrev entryEnv (m0 : MachineData) : Env := frameEnv m0 m0 128 [(oA m0, 8)]

/-- Every write in the frame or the count word. -/
def entryW (S : SState) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 128)) || (w.r == 1 && decide (w.off + w.n ≤ 8))

end

public section

section
variable [Labels] {a : DecArea} {s0 : TState} {m0 : MachineData}

theorem entry_wf (h : SampleQueriesPre a s0 m0) : (entryEnv m0).WF := by
  have hon : (oA m0).toNat + 1848 ≤ 2 ^ 64 := (pre_out h).2.1
  have hoS : Apart (oA m0) 1848 (stackBelow m0 128) (128 + 8) :=
    Transcript.apart_frame (pre_out h).2.2.2.2.1 (pre_hn h) N_ge
  refine Transcript.frame_wf ⟨Transcript.frame_mapped (pre_S h) N_ge, fb_noWrap h⟩ ?_
    (List.pairwise_pair.mpr ?_)
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨fun i hi ↦ (pre_out h).1 i (by rw [qbb_eq]; omega), show (oA m0).toNat + 8 ≤ 2 ^ 64 by omega⟩
  · show NativeRustcVm.Apart (stackBelow m0 128) (128 + 8) (oA m0) 8
    unfold Apart at hoS
    unfold NativeRustcVm.Apart
    omega

theorem entry_match : Match (entryEnv m0) entryS m0 :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨Transcript.match_rsp, Transcript.known_ptr rfl rfl, trivial⟩
    trivial trivial trivial

/-- **The entry's writes** change memory only in the frame and the count word. -/
theorem entry_same (h : SampleQueriesPre a s0 m0) {S : SState} {d : MachineData}
    (hm : Match (entryEnv m0) S d) (hw : entryW S = true) :
    SameOutside m0.dmem d.dmem (fun q ↦ InRange (fb m0) 128 q ∨ InRange (oA m0) 8 q) := by
  have hwf := entry_wf h
  have hon : (oA m0).toNat + 1848 ≤ 2 ^ 64 := (pre_out h).2.1
  have hfnw := fb_noWrap h
  intro q hq
  refine hm.get?_mem0 hwf fun hW ↦ hq ?_
  obtain ⟨w, hwm, b, sz, hb, jj, h1, h2, rfl⟩ := Transcript.written_off hwf hW
  unfold entryW at hw
  rw [List.all_eq_true] at hw
  have := hw w hwm
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this with ⟨hr, hle⟩ | ⟨hr, hle⟩ <;> rw [hr] at hb <;> cases hb
  · exact .inl (inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hfnw; omega))
  · exact .inr (inRange_off_self (by omega) (by omega))

theorem entry_outs (h : SampleQueriesPre a s0 m0) {q : BitVec 64}
    (hq : InRange (fb m0) 128 q ∨ InRange (oA m0) 8 q) : Outs m0 q := by
  rcases hq with hq | hq
  · exact frame_outs h le_rfl hq
  · exact .inl (Transcript.inRange_mono hq (by decide))

theorem entry_ts (h : SampleQueriesPre a s0 m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (hs : SameOutside m0.dmem d.dmem (fun q ↦ InRange (fb m0) 128 q ∨ InRange (oA m0) 8 q)) :
    TStateAt d.dmem (tA m0) a s0 :=
  (pre_ts h).frame hk (fun q hq ↦ by
    rcases hq with hq | hq
    · exact frame_not_t h (Transcript.inRange_mono hq (by omega))
    · exact o_not_t h (Transcript.inRange_mono hq (by decide))) hs

theorem count0 {d : MachineData} {S : SState} (hm : Match (entryEnv m0) S d)
    (hw : wrote S 1 0 (.lit 0) = true) : WordAt d.dmem (oA m0) 0 := by
  have := Transcript.wordAt_write hm (r := 1) (o := 0) rfl (by omega) (wrote_spec hw)
  rwa [off_zero] at this

end

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- **The empty count**: `b19` from the entry's chain. -/
theorem ret0 (h : SampleQueriesPre a s0 m0) (h0 : cnt m0 = 0) {st : MachineState} {nx : Int64}
    (hm : Match (entryEnv m0) (after b19 S0) st.data)
    (hpc : PcOk (entryEnv m0) (.ret (.load 0 128 8)) nx st) : Post a s0 m0 st := by
  obtain ⟨he, -, hw0, hw, hax⟩ := ok_b0z
  have hwf := entry_wf h
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue Frame.entry hwf hm he
  have hs := entry_same h hm hw
  refine ⟨?_, hrsp, ?_, ⟨#[], s0, ?_, bufWords_nil (count0 hm hw0), entry_ts h hsv.2 hs⟩,
    fun q hq ↦ hs q fun h' ↦ hq ?_, hsv⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    exact Frame.entry.load_ret (pre_S h) N_ge
  · show (reg st.data .rax).toNat % 256 = 1
    rw [show reg st.data .rax = _ from hm.regs .rax _ hax]
    exact al_one _
  · rw [sampleQueries_run, show (reg m0 .rdx).toNat = 0 from h0, auxP_zero_left]
  · rcases entry_outs h h' with ho | ho | ho
    · exact .inl ⟨_, List.mem_cons_self .., ho⟩
    · exact .inl ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ho⟩
    · exact .inr ho

/-- **A depth above `128`**: the squeezes' loop's start. -/
theorem big0 (h : SampleQueriesPre a s0 m0) (h0 : cnt m0 ≠ 0) (hd : 129 ≤ dep m0) {d : MachineData}
    (hm : Match (entryEnv m0) S1 d) : Big a s0 m0 0 s0 d := by
  obtain ⟨hpro, h72, hw0, hw, hbx, h14, h13⟩ := ok_b1
  have hwf := entry_wf h
  have hfr := Frame.of_prologue Frame.entry hwf hm hpro slots_le slots_cs
  have hs := entry_same h hm hw
  have hk := hm.kept hwf
  refine ⟨⟨hfr, ?_, fun q hq ↦ hs q fun h' ↦ hq (entry_outs h h'), hm.regs .r13 _ h13⟩,
    hm.regs .rbx _ hbx, ?_, Nat.pos_of_ne_zero h0, hd, entry_ts h hk hs, count0 hm hw0, by simp⟩
  · have := loc_write hm (by omega) h72
    rwa [show (Sym.ptr 1 0).eval (entryEnv m0) = oA m0 from Transcript.eval_ptr rfl] at this
  · rw [show reg d .r14 = _ from hm.regs .r14 _ h14]
    show (reg m0 .rdx).toNat = (reg m0 .rdx).toNat - 0
    simp

/-- **The outer loop's start** (`b2`). -/
theorem outer0 (h : SampleQueriesPre a s0 m0) (h0 : cnt m0 ≠ 0) (hd : dep m0 < 129) {d : MachineData}
    (hm : Match (entryEnv m0) (after b2 S1) d) : Outer a s0 m0 0 (cnt m0) s0 [] d := by
  obtain ⟨hpro, h72, h24, hw0, hw, hbx, h14, h13, h15, h12, hax, hbp⟩ := ok_b2
  have hwf := entry_wf h
  have hfr := Frame.of_prologue Frame.entry hwf hm hpro slots_le slots_cs
  have hs := entry_same h hm hw
  have hk := hm.kept hwf
  refine ⟨⟨hfr, ?_, fun q hq ↦ hs q fun h' ↦ hq (entry_outs h h'), hm.regs .r13 _ h13⟩, ?_,
    by rw [show reg d .rax = _ from hm.regs .rax _ hax]; rfl, hm.regs .rbx _ hbx,
    by rw [show reg d .r15 = _ from hm.regs .r15 _ h15]; rfl,
    by rw [show reg d .r14 = _ from hm.regs .r14 _ h14]; rfl,
    by rw [show reg d .r12 = _ from hm.regs .r12 _ h12]; rfl,
    by rw [show reg d .rbp = _ from hm.regs .rbp _ hbp]; rfl, Nat.pos_of_ne_zero h0, by simp, hd,
    entry_ts h hk hs, bufWords_nil (count0 hm hw0), by simp⟩
  · have := loc_write hm (by omega) h72
    rwa [show (Sym.ptr 1 0).eval (entryEnv m0) = oA m0 from Transcript.eval_ptr rfl] at this
  · have := loc_write hm (by omega) h24
    rwa [show (Sym.reg .rdi).eval (entryEnv m0) = tA m0 from rfl] at this

end

end NativeRustcVmX64.Whir.SampleQueries
