module

public import NativeRustcVmX64.Whir.FoldRounds.Basic

/-!
# `fold_rounds` on x86-64: tests, writes, apartness

The tag tests (`tag8_*`, `tag32_*`), the rounds' count test (`cnt_eq`), the entry's test
(`test0`); what a round's store changes (`storeR`, `store_written`) and what it misses (the state,
the `TState`); what `fold_round`'s call misses (the buffer, `r_not_call`); the entry's writes
(`entryEnv`, `entry_same`) and what they keep.
-/

namespace NativeRustcVmX64.Whir.FoldRounds

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRounds
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (wrote wrote_spec)
open NativeRustcVm (WordAt EWAt EWsAt)

@[expose] public section

/-- Round `i`'s bytes of the buffer: the count, its item. -/
def Wi (i j : Nat) : Prop := j < 8 ∨ (8 + 32 * i ≤ j ∧ j < 40 + 32 * i)

/-- What round `i`'s store changes: its bytes of the buffer, the frame. -/
def storeR (m0 : MachineData) (i : Nat) (q : BitVec 64) : Prop :=
  Touch (rA m0) 200 (Wi i) q ∨ InRange (fb m0) 160 q

/-- The entry's environment: the frame, the buffer's count word. -/
abbrev entryEnv (m0 : MachineData) (r : BitVec 64) : Env :=
  frameEnv m0 m0 160 [(rA m0, 8)] (fun _ ↦ 0) r

end

public section

theorem cs_of {r : Reg64} (h : calleeSaved r = true) : r ∈ cs := by
  cases r <;> simp [calleeSaved, cs] at h ⊢

theorem beq_ofNat' {x : BitVec 64} {j : Nat} (hj : j < 2 ^ 64) :
    (x == BitVec.ofNat 64 j) = decide (x.toNat = j) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  have e : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hj
  constructor
  · intro h; rw [h, e]
  · intro h; apply BitVec.eq_of_toNat_eq; rw [e]; exact h

theorem three_iff {a b c q : BitVec 64} {n m l : Nat} :
    NativeRustcVm.InAny [⟨a, n⟩, ⟨b, m⟩, ⟨c, l⟩] q ↔ NativeRustcVm.InRange a n q ∨
      NativeRustcVm.InRange b m q ∨ NativeRustcVm.InRange c l q := by
  simp only [NativeRustcVm.inAny_cons_iff, NativeRustcVm.inAny_nil, or_false,
    NativeRustcVm.Region.Holds]

section
variable [Labels] {m0 d : MachineData}

/-- The frame with RSP at its offset `8`, matched by `midS`. -/
theorem mid {vars : Nat → BitVec 64} {ret : BitVec 64} (hf : Frame m0 160 slots 8 d) :
    Match (frameEnv m0 d 160 [] vars ret) midS d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial

/-- A round's store, matched by `store0S` (the first) or `storeS` (RBP the output's `α`). -/
theorem store_match {S0 : SState} {i : Nat} (hS0 : S0 = store0S ∨ (S0 = storeS ∧ 0 < i))
    (hf : Frame m0 160 slots 8 d) (h12 : reg d .r12 = rA m0)
    (hbp : 0 < i → reg d .rbp = off (fb m0) 48) :
    Match (frameEnv m0 d 160 [(rA m0, 200)]) S0 d := by
  rcases hS0 with rfl | ⟨rfl, hi⟩
  · exact match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, Transcript.known_ptr rfl h12, trivial⟩
      trivial trivial trivial
  · exact match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, Transcript.known_ptr rfl h12,
      (hbp hi).trans (Transcript.eval_ptr0 48).symm, trivial⟩ trivial trivial trivial

theorem tag8_0 (hw : WordAt d.dmem (off (fb m0) 40) 0) :
    (SBool.cmp .eq .W8 (.load 0 40 1) (.lit 0)).eval (frameEnv m0 d 160 []) = true := by
  simp only [SBool.eval, Sym.eval]
  rw [Transcript.load1_of_tag (env := frameEnv m0 d 160 []) (r := 0) (o := 40) (Or.inl rfl) hw]
  rfl

theorem tag8_1 (hw : WordAt d.dmem (off (fb m0) 40) 1) :
    (SBool.cmp .eq .W8 (.load 0 40 1) (.lit 0)).eval (frameEnv m0 d 160 []) = false := by
  simp only [SBool.eval, Sym.eval]
  rw [Transcript.load1_of_tag (env := frameEnv m0 d 160 []) (r := 0) (o := 40) (Or.inr rfl) hw]
  rfl

theorem tag32_0 (hw : WordAt d.dmem (off (fb m0) 40) 0) :
    (SBool.cmp .eq .W32 (.load 0 40 4) (.lit 1)).not.eval (frameEnv m0 d 160 []) = true := by
  simp only [SBool.eval, Sym.eval]
  rw [Transcript.load4_of_tag (env := frameEnv m0 d 160 []) (r := 0) (o := 40) (Or.inl rfl) hw]
  rfl

theorem tag32_1 (hw : WordAt d.dmem (off (fb m0) 40) 1) :
    (SBool.cmp .eq .W32 (.load 0 40 4) (.lit 1)).not.eval (frameEnv m0 d 160 []) = false := by
  simp only [SBool.eval, Sym.eval]
  rw [Transcript.load4_of_tag (env := frameEnv m0 d 160 []) (r := 0) (o := 40) (Or.inr rfl) hw]
  rfl

/-- `cmpq $j, %r13; je`. -/
theorem cnt_eq {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64} {ret : BitVec 64} {j : Nat}
    (hj : j < 2 ^ 64) :
    (SBool.cmp .eq .W64 (.reg .r13) (.lit j)).eval (Env.ofMachine d rs vs ret) =
      decide ((reg d .r13).toNat = j) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64]
  exact beq_ofNat' hj

/-- `testq %rsi, %rsi; je`. -/
theorem test0 {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64} {ret : BitVec 64} :
    (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rsi) (.reg .rsi)) (.lit 0)).eval
      (Env.ofMachine d rs vs ret) = decide ((reg d .rsi).toNat = 0) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self]
  exact beq_ofNat' (by decide)

end

section
variable [Labels] {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}

/-- The frame holds no byte of the buffer. -/
theorem r_not_frame (h : FoldRoundsPre a s w m0) {q : BitVec 64} (hq : InRange (fb m0) 168 q) :
    ¬ InRange (rA m0) 200 q :=
  fun hr ↦ (ctx h).ofr q (.inl hr) hq

/-- The buffer holds no byte of the `TState` and the decoded area. -/
theorem t_not_r (h : FoldRoundsPre a s w m0) {q : BitVec 64} (hq : InRange (rA m0) 200 q) :
    ¬ InRange (tA m0) tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q := by
  have c := ctx h
  have hr := pre_r h
  exact ⟨not_inRange_of_apart hr.2.2.1 hr.2.1 c.fp.1.2 hq,
    not_inRange_of_apart hr.2.2.2.1 hr.2.1 c.fp.2.1.2 hq⟩

/-- The frame holds no byte of the `TState` and the decoded area. -/
theorem t_not_frame (h : FoldRoundsPre a s w m0) {q : BitVec 64} (hq : InRange (fb m0) 168 q) :
    ¬ InRange (tA m0) tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q := by
  have c := ctx h
  exact ⟨fun ht ↦ c.ofr _ (.inr (.inr ht)) hq, fun ha ↦ not_inRange_of_apart
    (Transcript.apart_frame c.tok.2.1 c.hN c.hF) c.fp.2.1.2 c.fnw ha hq⟩

/-- A byte of the state is in neither the frame nor the buffer. -/
theorem p_not (h : FoldRoundsPre a s w m0) {j : Nat} (hj : j < stateBytes) :
    ¬ InRange (fb m0) 168 (off (pA m0) j) ∧ ¬ InRange (rA m0) 200 (off (pA m0) j) := by
  have hp := pre_p h
  have hpn : (pA m0).toNat + stateBytes ≤ 2 ^ 64 := hp.2.1
  have hin : InRange (pA m0) stateBytes (off (pA m0) j) := inRange_off_self hj (by omega)
  exact ⟨fun hq ↦ (ctx h).ofr _ (.inr (.inl hin)) hq,
    fun hq ↦ not_inRange_of_apart (pre_rp h) (pre_r h).2.1 hp.2.1 hq hin⟩

omit [Labels] in
/-- **Round `i`'s store's writes**: its bytes of the buffer, the frame. -/
theorem store_written {d : MachineData} {S : SState} {i : Nat}
    (hi : i < 6) (hwf : (frameEnv m0 d 160 [(rA m0, 200)]).WF) (hsw : storeW S i = true)
    {q : BitVec 64} (hW : Written (frameEnv m0 d 160 [(rA m0, 200)]) S q) : storeR m0 i q := by
  obtain ⟨wr, hwr, b, sz, hb, j, h1, h2, rfl⟩ := Transcript.written_off hwf hW
  unfold storeW at hsw
  rw [List.all_eq_true] at hsw
  have := hsw wr hwr
  have key : (wr.r = 1 ∧ wr.off + wr.n ≤ 8) ∨
      (wr.r = 1 ∧ 8 + 32 * i ≤ wr.off ∧ wr.off + wr.n ≤ 40 + 32 * i) ∨
      (wr.r = 0 ∧ 8 ≤ wr.off ∧ wr.off + wr.n ≤ 40) := by
    simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc,
      or_assoc] using this
  rcases key with ⟨hr, hle⟩ | ⟨hr, hlo, hhi⟩ | ⟨hr, hlo, hhi⟩ <;> rw [hr] at hb <;> cases hb
  · exact .inl ⟨j, by omega, .inl (by omega), rfl⟩
  · exact .inl ⟨j, by omega, .inr ⟨by omega, by omega⟩, rfl⟩
  · exact .inr (inRange_off_self (by omega) (by omega))

/-- What a store changes is in the outputs or the stack. -/
theorem storeR_sm (h : FoldRoundsPre a s w m0) {i : Nat} {q : BitVec 64} (hq : storeR m0 i q) :
    InRange (stackBelow m0 160) 160 q ∨ outs m0 q :=
  hq.elim (fun hq ↦ .inr (.inl (Transcript.inRange_of_touch (pre_r h).2.1 hq))) .inl

/-- A store misses the `TState` and the decoded area. -/
theorem t_not_store (h : FoldRoundsPre a s w m0) {i : Nat} {q : BitVec 64} (hq : storeR m0 i q) :
    ¬ InRange (tA m0) tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q :=
  hq.elim (fun hq ↦ t_not_r h (Transcript.inRange_of_touch (pre_r h).2.1 hq))
    fun hq ↦ t_not_frame h (Transcript.inRange_mono hq (by omega))

/-- A store misses the state. -/
theorem p_not_store (h : FoldRoundsPre a s w m0) {i j : Nat} (hj : j < stateBytes) :
    ¬ storeR m0 i (off (pA m0) j) := by
  rintro (hq | hq)
  · exact (p_not h hj).2 (Transcript.inRange_of_touch (pre_r h).2.1 hq)
  · exact (p_not h hj).1 (Transcript.inRange_mono hq (by omega))

/-- **`fold_round`'s changes miss the buffer**: its output in the frame, the state, the
`TState`, its stack below the frame. -/
theorem r_not_call (h : FoldRoundsPre a s w m0) {d : MachineData}
    (hsp : rspOf d = stackBelow m0 160) (hdi : reg d .rdi = off (fb m0) 40)
    (hsi : reg d .rsi = tA m0) (hdx : reg d .rdx = pA m0) {q : BitVec 64}
    (hq : InRange (rA m0) 200 q) :
    ¬ (NativeRustcVm.InAny [⟨reg d .rdi, 40⟩, ⟨reg d .rdx, stateBytes⟩, ⟨reg d .rsi, tstateBytes⟩] q ∨
      InRange (stackBelow d foldRoundStack) foldRoundStack q) := by
  have c := ctx h
  have hr := pre_r h
  rw [three_iff, hdi, hdx, hsi]
  rintro ((h1 | h1 | h1) | h1)
  · exact r_not_frame h (Transcript.inRange_of_off (N := 168) c.fnw (by omega) h1) hq
  · exact not_inRange_of_apart (pre_rp h) hr.2.1 (pre_p h).2.1 hq h1
  · exact (t_not_r h hq).1 h1
  · exact not_inRange_of_apart hr.2.2.2.2.1 hr.2.1 (noWrap_stackBelow c.stack) hq
      (Transcript.inRange_mono (Transcript.inRange_callee hsp c.h8 c.hN call_le h1).1 (by omega))

/-! ## The entry -/

theorem entry_wf (h : FoldRoundsPre a s w m0) {r : BitVec 64} : (entryEnv m0 r).WF := by
  have hrn : (rA m0).toNat + 200 ≤ 2 ^ 64 := (pre_r h).2.1
  have hap : NativeRustcVm.Apart (stackBelow m0 160) (160 + 8) (rA m0) 200 :=
    Transcript.Apart.symm' (Transcript.apart_frame (pre_r h).2.2.2.2.1 (pre_S h).1 F_le)
  refine Transcript.frame_wf ⟨Transcript.frame_mapped (pre_S h) F_le,
    Transcript.frame_noWrap (pre_S h) F_le⟩ (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr (Transcript.Apart.sub (b' := rA m0) (N' := 8) hap le_rfl (by omega)))
  rw [List.mem_singleton] at hx
  subst hx
  exact ⟨fun i hi ↦ (pre_r h).1 i (by omega), show (rA m0).toNat + 8 ≤ 2 ^ 64 by omega⟩

theorem entry_match {r : BitVec 64} : Match (entryEnv m0 r) entryS m0 :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨Transcript.match_rsp, Transcript.known_ptr rfl rfl, trivial⟩
    trivial trivial trivial

/-- **The entry's writes** change memory only in the frame and the count word. -/
theorem entry_same (h : FoldRoundsPre a s w m0) {r : BitVec 64} {S : SState} {d : MachineData}
    (hm : Match (entryEnv m0 r) S d) (hw : entryW S = true) :
    SameOutside m0.dmem d.dmem (fun q ↦ InRange (fb m0) 160 q ∨ InRange (rA m0) 8 q) := by
  have hwf := entry_wf h (r := r)
  have hrn : (rA m0).toNat + 200 ≤ 2 ^ 64 := (pre_r h).2.1
  intro q hq
  refine hm.get?_mem0 hwf fun hW ↦ hq ?_
  obtain ⟨wr, hwm, b, sz, hb, jj, h1, h2, rfl⟩ := Transcript.written_off hwf hW
  unfold entryW at hw
  rw [List.all_eq_true] at hw
  have := hw wr hwm
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this with ⟨hr, hle⟩ | ⟨hr, hle⟩ <;> rw [hr] at hb <;> cases hb
  · exact .inl (inRange_off_self (by omega) (by omega))
  · exact .inr (inRange_off_self (by omega) (by omega))

theorem entry_sm (h : FoldRoundsPre a s w m0) {d : MachineData}
    (hs : SameOutside m0.dmem d.dmem (fun q ↦ InRange (fb m0) 160 q ∨ InRange (rA m0) 8 q)) :
    Sm m0 d := fun q hq ↦ hs q fun h' ↦ hq (h'.elim (fun h' ↦ .inr ((ctx h).frame_stack h'))
  fun h' ↦ .inl (.inl (Transcript.inRange_mono h' (by omega))))

theorem entry_ws (h : FoldRoundsPre a s w m0) {d : MachineData}
    (hs : SameOutside m0.dmem d.dmem (fun q ↦ InRange (fb m0) 160 q ∨ InRange (rA m0) 8 q)) :
    WhirStateAt d.dmem (pA m0) w :=
  WhirStateAt.agree (pre_ws h) fun j hj _ ↦ hs _ fun hq ↦ hq.elim
    (fun hq ↦ (p_not h hj).1 (Transcript.inRange_mono hq (by omega)))
    fun hq ↦ (p_not h hj).2 (Transcript.inRange_mono hq (by omega))

theorem entry_ts (h : FoldRoundsPre a s w m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (hs : SameOutside m0.dmem d.dmem (fun q ↦ InRange (fb m0) 160 q ∨ InRange (rA m0) 8 q)) :
    TStateAt d.dmem (tA m0) a s :=
  (pre_ts h).frame hk (fun q hq ↦ hq.elim
    (fun hq ↦ t_not_frame h (Transcript.inRange_mono hq (by omega)))
    fun hq ↦ t_not_r h (Transcript.inRange_mono hq (by omega))) hs

theorem count0 {r : BitVec 64} {S : SState} {d : MachineData}
    (hm : Match (entryEnv m0 r) S d) (hw : wrote S 1 0 (.lit 0) = true) :
    WordAt d.dmem (rA m0) 0 := by
  have := Transcript.wordAt_write hm (r := 1) (o := 0) rfl (by omega) (wrote_spec hw)
  rwa [off_zero] at this

end

end

end NativeRustcVmX64.Whir.FoldRounds
