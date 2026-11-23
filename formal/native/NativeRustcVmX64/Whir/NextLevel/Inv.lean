module

public import NativeRustcVmX64.Whir.NextLevel.Steps

/-!
# `next_level`: what every state of the body keeps (x86-64)

`K o d`: the frame (RSP at offset `o`), `μ` at the frame's word `80`, the level and the state `w`
with its rounds. Kept by a block writing the frame off `80` (`Ctx.K_blk` in the frame's region with
the argument word, `Ctx.K_blkF` without it and with the level) and by a call changing its stack,
the `TState`, a range of the frame and the query buffer (`Ctx.K_call`).
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The query buffer. -/
abbrev qA (m0 : MachineData) : BitVec 64 := pA m0 + BitVec.ofNat 64 61352

/-- **What the body keeps**, RSP at offset `o`. -/
structure K [Labels] (level : Whir.Level) (w : WhirStateW) (rounds : Array FoldRoundW)
    (m0 : MachineData) (o : Nat) (d : MachineData) : Prop where
  fr : Fr m0 o d
  w80 : NativeRustcVm.WordAt d.dmem (loc m0 80) (.ofBitVec (reg m0 .r9))
  lv : LevelAt d.dmem (lA m0) level
  wa : WhirAt d.dmem (pA m0) w rounds

end

public section

theorem whirAt_of_same {d d' : Mem 64} {p : BitVec 64} {w : WhirStateW} {rs : Array FoldRoundW}
    (h : WhirAt d p w rs) (hs : NativeRustcVm.Layout.Same d d' p 61352) : WhirAt d' p w rs :=
  ⟨WhirStateAt.of_same h.1 fun j hj ↦ hs j (by unfold stateBytes at hj; omega),
    bufRoundsAt_of_same h.2 (hs.sub (o := roundsOff) (k := 8 + roundBytes * roundCap) (by decide))⟩

/-- Bytes of the frame a block in `frameEnv` does not write. -/
theorem bytes_blkF [Labels] {m0 d d' : MachineData} {rest : List (BitVec 64 × Nat)} {S : SState}
    {ret : BitVec 64} (hwf : (frameEnv m0 d 8176 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 8176 rest (fun _ ↦ 0) ret) S d')
    (hin : writesIn S = true) {rs : List (Nat × Nat)} (hW : Wr rs S) {j : Nat} {bs : List UInt8}
    (hj : j + bs.length ≤ 8184) (hmiss : ∀ p ∈ rs, p.2 ≤ j ∨ j + bs.length ≤ p.1)
    (h : NativeRustcVm.BytesAt d.dmem (loc m0 j) bs) :
    NativeRustcVm.BytesAt d'.dmem (loc m0 j) bs := by
  intro i hi
  have := h i hi
  rw [off_add] at this ⊢
  rw [hm.get?_mem0 hwf (not_written0 hwf hm hin (by omega) fun w hw _ ↦ ?_)]
  · exact this
  · obtain ⟨-, p, hp, h1, h2⟩ := hW w hw
    rcases hmiss p hp with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s level w rounds m0)
include c

/-- The frame (without the argument word) and the level. -/
theorem wfL {d : MachineData} (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} :
    (frameEnv m0 d 8176 [(lA m0, 24)] (fun _ ↦ 0) ret).WF := by
  have g := c.geo
  have hf := c.fa_toNat
  refine frame_wf ⟨(c.region_ok hk).1.mono (by omega), (c.region_ok hk).2.mono (by omega)⟩
    (fun y hy ↦ ?_) (List.pairwise_pair.mpr ?_)
  · rw [List.mem_singleton] at hy; subst hy
    exact ⟨Mapped.keeps c.lin.1.1 hk, c.lin.1.2⟩
  · show (fa m0).toNat + (8176 + 8) ≤ (lA m0).toNat ∨ (lA m0).toNat + 24 ≤ (fa m0).toNat
    rw [hf]; have := g.lS; have := g.hN; omega

/-- **A body block in `frameEnv`** keeps the frame; it writes the frame below `hi ≤ 8128`. -/
theorem blkF {o o' : Nat} {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {S : SState}
    {ret : BitVec 64} (hf : Fr m0 o d) (hwf : (frameEnv m0 d 8176 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 8176 rest (fun _ ↦ 0) ret) S d') (hmid : MidOk 8176 o' slots S = true)
    {hi : Nat} (hhi : hi ≤ 8128) (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ hi) :
    Fr m0 o' d' ∧ NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) hi) := by
  have hs : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) hi) :=
    sameOutside_low hwf hm (r := 0) rfl (by omega) hw
  refine ⟨⟨Frame.of_block hf.frame hwf hm hmid slots_le, NativeRustcVm.SameOutside.mono
    (hf.same.trans hs) fun q hq ↦ ?_⟩, hs⟩
  rcases hq with hq | hq
  · exact hq
  · left
    obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hq
    exact c.loc_stk (j := j) (by omega)

/-- `K` across a change of the frame below `hi`, the word `80` kept. -/
theorem K_frame {o o' : Nat} {d d' : MachineData} (hK : K level w rounds m0 o d)
    (hf : Fr m0 o' d') {hi : Nat} (hhi : hi ≤ 8176)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) hi))
    (h80 : NativeRustcVm.WordAt d'.dmem (loc m0 80) (.ofBitVec (reg m0 .r9))) :
    K level w rounds m0 o' d' :=
  ⟨hf, h80, LevelAt.of_same hK.lv (c.l_frame hhi hs),
    WhirAt.of_same hK.wa (c.p_frame hhi hs)⟩

/-- **A call** from RSP offset `64` changing its stack, the `TState`, the frame's `n` bytes from
`lo ≥ 88` and the query buffer: `K` and the frame's other bytes from `72` kept. -/
theorem K_call {d d' : MachineData} (hK : K level w rounds m0 64 d) {N' : Nat}
    (hle : 8112 + N' ≤ nextLevelStack) (hsv : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64)
    {R : BitVec 64 → Prop} {lo n : Nat} (hlo : 88 ≤ lo) (hn : lo + n ≤ 8128)
    (hR : ∀ q, R q → NativeRustcVm.InRange (tA m0) tstateBytes q ∨
      NativeRustcVm.InRange (loc m0 lo) n q ∨ NativeRustcVm.InRange (qA m0) 1848 q)
    (hch : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d N') N' q)) :
    K level w rounds m0 72 d' ∧ ∀ j, 72 ≤ j → j < 8192 → (j < lo ∨ lo + n ≤ j) →
      d'.dmem.get? (loc m0 j) = d.dmem.get? (loc m0 j) := by
  have g := c.geo
  have hqa : (qA m0).toNat = (pA m0).toNat + 61352 :=
    NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)
  have hat := c.at_call (by omega) hK.fr
  have hsb : (stackBelow d N').toNat = (rspOf m0).toNat - 8112 - N' := by
    rw [stackBelow_callee hat.sp (by have := g.hN; rw [stack_eq] at hle; omega),
      stackBelow_toNat (by have := g.hN; rw [stack_eq] at hle; omega)]
    omega
  have hle' : 8112 + N' ≤ 11312 := by rw [stack_eq] at hle; exact hle
  obtain ⟨hf', hkeep⟩ := c.call (o := 64) (by omega) hK.fr (by omega) hsv hrsp (by omega) hn
    (fun q hq ↦ by
      rcases hR q hq with hq | hq | hq
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq
      · left; left
        rw [c.inP]
        rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hqa]; have := g.pW; omega), hqa]
          at hq
        omega) hch
  -- a byte of the region `x` (`m` bytes) apart from all the changes is kept
  have hsame : ∀ {x : BitVec 64} {mm : Nat}, x.toNat + mm ≤ 2 ^ 64 →
      (x.toNat + mm ≤ (tA m0).toNat ∨ (tA m0).toNat + 760 ≤ x.toNat) →
      (x.toNat + mm ≤ (rspOf m0).toNat - 11312 ∨ (rspOf m0).toNat + 8 ≤ x.toNat) →
      (x.toNat + mm ≤ (qA m0).toNat ∨ (qA m0).toNat + 1848 ≤ x.toNat) →
      NativeRustcVm.Layout.Same d.dmem d'.dmem x mm := by
    intro x mm hxw ht hs hq
    refine NativeRustcVm.Layout.Same.of_sameOutside hch fun j hj hq' ↦ ?_
    have hx : (x + BitVec.ofNat 64 j).toNat = x.toNat + j := NativeRustcVm.toNat_add_ofNat (by omega)
    have := g.hN
    rcases hq' with hq' | hq'
    · rcases hR _ hq' with h' | h' | h'
      · rw [c.inT, hx] at h'; omega
      · rw [c.inLc (by omega) (by omega), hx] at h'; omega
      · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hqa]; have := g.pW; omega), hqa,
          hx] at h'
        rw [hqa] at hq; omega
    · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hsb]; omega), hsb, hx] at hq'
      omega
  have hlb : levelBytes = 24 := rfl
  refine ⟨⟨hf', ?_, ?_, ?_⟩, hkeep⟩
  · exact bytes_call hkeep (j := 80) (by omega) (by simp [NativeRustcVm.length_wordBytes])
      (by simp [NativeRustcVm.length_wordBytes]; omega) hK.w80
  · refine LevelAt.of_same hK.lv (hsame g.lW ?_ ?_ ?_)
    · have := g.lT; omega
    · have := g.lS; omega
    · rw [hqa]; have := g.lP; omega
  · refine whirAt_of_same hK.wa (hsame (by have := g.pW; omega) ?_ ?_ ?_)
    · have := g.pT; omega
    · have := g.pS; omega
    · rw [hqa]; omega

end Ctx

end

end

end NativeRustcVmX64.Whir.Levels.NL
