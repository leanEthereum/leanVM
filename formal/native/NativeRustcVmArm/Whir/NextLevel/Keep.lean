module

public import NativeRustcVmArm.Whir.NextLevel.Exit
public import NativeRustcVmArm.Whir.FoldRounds.Round

/-!
# `next_level`: what is kept

The level and the `WhirW`'s state and rounds, apart from the stack and the outputs, are kept in
every state of the frame (`level_keep`, `whir_keep`). Frame bytes across a call (`keepC`) or a
block (`keepB`); the `TState` across a block (`tsB`).
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel

public section

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

/-- A frame byte is apart from the `TState` and the decoded area. -/
theorem frame_not_t (h : NextLevelPre a s level w rounds m0) {q : BitVec 64}
    (hq : InRange (base m0 8192) 8192 q) :
    ¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have g := geo h
  have hb := base_nat (m0 := m0) (F := 8192) (hN8 h)
  have r := inr (by rw [hb]; have := g.hsp; omega) hq
  rw [hb] at r
  have := g.tS; have := g.aS; have := g.hN
  exact ⟨nin g.tW (by unfold tstateBytes; omega), nin g.aW (by omega)⟩

/-- Bytes apart from the stack and the outputs agree with the entry's. -/
theorem keepR (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st)
    {b : BitVec 64} {N : Nat} (hbw : b.toNat + N ≤ 2 ^ 64)
    (hap : b.toNat + N ≤ m0.regs.SP.toNat - 11424 ∨ m0.regs.SP.toNat ≤ b.toNat)
    (ht : b.toNat + N ≤ (tA m0).toNat ∨ (tA m0).toNat + 760 ≤ b.toNat)
    (hq : b.toNat + N ≤ (pA m0).toNat + 61352 ∨ (pA m0).toNat + 63200 ≤ b.toNat) :
    Agree m0.dmem st.dmem b N (fun _ ↦ False) := by
  have g := geo h
  have hqn := qA_toNat (m0 := m0) g.pW
  have hbN := base_nat (m0 := m0) (F := nextLevelStack) (by rw [stack_eq]; exact g.hN)
  rw [stack_eq] at hbN
  have hbw' : (base m0 11424).toNat + 11424 ≤ 2 ^ 64 := by rw [hbN]; have := g.hsp; omega
  have hqw : (qA m0).toNat + queryBufBytes ≤ 2 ^ 64 := by
    rw [hqn]; have := g.pW; unfold queryBufBytes queryCap; omega
  refine fun j hj _ ↦ hf.same _ fun hr ↦ ?_
  have hj' : (off b j).toNat = b.toNat + j := toNat_off (by omega)
  rcases hr with hr | hr | hr
  · have := inr (n := 11424) hbw' hr
    rw [hbN, hj'] at this
    have := g.hN
    omega
  · have := inr (n := tstateBytes) g.tW hr; rw [hj'] at this; unfold tstateBytes at this; omega
  · have := inr hqw hr
    rw [hj', hqn] at this; unfold queryBufBytes queryCap at this; omega

/-- **The level kept.** -/
theorem level_keep (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st) :
    LevelAt st.dmem (lA m0) level := by
  have g := geo h
  obtain ⟨h1, h2, h3, hw⟩ := h.2.2.2.2.1
  refine ⟨h1, h2, h3, bytesAt_of_agree (keepR h hf (N := 24) g.lW (by have := g.lS; omega)
    (by have := g.lT; omega) (by have := g.lP; omega)) (by simp [NativeRustcVm.length_wordBytes])
    hw⟩

/-- **The `WhirW`'s state and rounds kept.** -/
theorem whir_keep (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st) :
    WhirAt st.dmem (pA m0) w rounds := by
  have g := geo h
  obtain ⟨hws, hbr⟩ := h.2.2.2.1
  have hA := keepR h hf (N := 61352) (b := pA m0) (by have := g.pW; omega)
    (by have := g.pS; omega) (by have := g.pT; omega) (by omega)
  have hA0 := agree_sub hA (o := 0) (k := 61152) (by omega) fun _ _ ↦ id
  rw [off_zero] at hA0
  refine ⟨hws.agree hA0, FoldRounds.bufRoundsAt_agree hbr
    (agree_sub hA (o := 61152) (k := 200) (by omega) fun _ _ ↦ id)⟩

/-- **The `TState` across a block** writing the frame. -/
theorem tsB (h : NextLevelPre a s level w rounds m0) {d d' : Mem 64} {s' : TState}
    (hk : Kept d d') (hs : SameOutside d d' (InRange (base m0 8192) 8192))
    (hts : TStateAt d (tA m0) a s') : TStateAt d' (tA m0) a s' :=
  hts.frame hk (fun _ hq ↦ frame_not_t h hq) hs

/-- **Frame bytes across a call** writing its stack, the frame's `n'` bytes at `o'` and the
outputs. -/
theorem keepC (c : TCtx m0 8192 nextLevelStack (tA m0) a (outs m0)) {st : MachineData}
    (hf : NFr m0 st) {N' o' n' : Nat} (hle : 8192 + N' ≤ nextLevelStack) (ho' : o' + n' ≤ 8192)
    {d' : Mem 64} (hs : SameOutside st.dmem d' fun q ↦ InRange (stackBelow st N') N' q ∨
      InRange (loc m0 o') n' q ∨ outs m0 q)
    {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 8192)
    (hd : o + bs.length ≤ o' ∨ o' + n' ≤ o) (hb : NativeRustcVm.BytesAt st.dmem (loc m0 o) bs) :
    NativeRustcVm.BytesAt d' (loc m0 o) bs :=
  hf.bytes_keep c.hN c.frame_outs hle ho' hs ho hd hb

end

/-- **Frame bytes across a block** whose writes miss them. -/
theorem keepB [Labels] {m0 st m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine st ((base m0 8192, 8192) :: rs)) S m)
    (hwf : (Env.ofMachine st ((base m0 8192, 8192) :: rs)).WF) {o n : Nat}
    (hmiss : missFrame S o n = true) (ho : o + n ≤ 8192) {bs : List UInt8} (hl : bs.length = n)
    (hb : NativeRustcVm.BytesAt st.dmem (loc m0 o) bs) :
    NativeRustcVm.BytesAt m.dmem (loc m0 o) bs :=
  bytes_block hm hwf rfl hmiss ho hl hb

end

end NativeRustcVmArm.Whir.NextLevel
