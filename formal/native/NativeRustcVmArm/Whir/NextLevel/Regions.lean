module

public import NativeRustcVmArm.Whir.NextLevel.Calls

/-!
# `next_level`: the areas as numbers

A callee's stack (`stack_nat`), a frame range (`loc_nat`), the `TState` (`t_nat`), the `WhirW`
(`p_nat`), the decoded area (`a_nat`) as ranges of numbers. What changes apart from them keeps the
query buffer (`qbuf_keep`), the `TState` (`ts_keep`), words of the decoded area (`words_keep`).
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel

public section

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {q : BitVec 64}

theorem stack_nat (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st)
    {N' : Nat} (hle : 8192 + N' ≤ nextLevelStack) (hq : InRange (stackBelow st N') N' q) :
    m0.regs.SP.toNat - 11424 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 8192 := by
  have g := geo h
  have hN : 8192 + N' ≤ m0.regs.SP.toNat := by have := g.hN; rw [stack_eq] at hle; omega
  rw [stackBelow_eq hf.sp hN] at hq
  have hnw : (base m0 (8192 + N')).toNat + N' ≤ 2 ^ 64 := by
    rw [base_toNat hN]; have := g.hsp; omega
  rw [Sym.inRange_iff hnw, base_toNat hN] at hq
  rw [stack_eq] at hle
  omega

theorem loc_nat (h : NextLevelPre a s level w rounds m0) {o n : Nat} (hon : o + n ≤ 8192)
    (hq : InRange (loc m0 o) n q) :
    m0.regs.SP.toNat - 8192 + o ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 8192 + o + n := by
  have g := geo h
  have hl := loc_toNat (m0 := m0) (o := o) (hN8 h) (by omega)
  rw [Sym.inRange_iff (by rw [hl]; have := g.hsp; omega), hl] at hq
  omega

theorem t_nat (h : NextLevelPre a s level w rounds m0) (hq : InRange (tA m0) tstateBytes q) :
    (tA m0).toNat ≤ q.toNat ∧ q.toNat < (tA m0).toNat + 760 :=
  inr (geo h).tW hq

theorem p_nat (h : NextLevelPre a s level w rounds m0) {n : Nat} (hn : n ≤ whirBytes)
    (hq : InRange (pA m0) n q) : (pA m0).toNat ≤ q.toNat ∧ q.toNat < (pA m0).toNat + n :=
  inr (by have := (geo h).pW; unfold whirBytes at hn; omega) hq

theorem a_nat (h : NextLevelPre a s level w rounds m0) (hq : InRange a.words (8 * a.len) q) :
    a.words.toNat ≤ q.toNat ∧ q.toNat < a.words.toNat + 8 * a.len :=
  inr (geo h).aW hq

theorem frame_nat (h : NextLevelPre a s level w rounds m0)
    (hq : InRange (base m0 8192) 8192 q) :
    m0.regs.SP.toNat - 8192 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat := by
  have g := geo h
  have hb := base_nat (m0 := m0) (F := 8192) (hN8 h)
  have := inr (by rw [hb]; have := g.hsp; omega) hq
  rw [hb] at this
  have := g.hN
  omega

theorem sponge_t (h : NextLevelPre a s level w rounds m0) (hq : InRange (tA m0) spongeBytes q) :
    InRange (tA m0) tstateBytes q := by
  have g := geo h
  have := inr (n := spongeBytes) (by have := g.tW; unfold spongeBytes; omega) hq
  show InRange (tA m0) 760 q
  rw [Sym.inRange_iff g.tW]
  unfold spongeBytes at this
  omega

/-- **The query buffer kept** by a change outside it. -/
theorem qbuf_keep (h : NextLevelPre a s level w rounds m0) {d d' : Mem 64}
    {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    (hR : ∀ q, R q → q.toNat < (pA m0).toNat + 61352 ∨ (pA m0).toNat + 63200 ≤ q.toNat)
    {qs : List UInt64} (hb : NativeRustcVm.BufWordsAt d (qA m0) queryCap qs) :
    NativeRustcVm.BufWordsAt d' (qA m0) queryCap qs := by
  have g := geo h
  have hq := qA_toNat (m0 := m0) g.pW
  obtain ⟨hl, hw, hws⟩ := hb
  have hlen : qs.length ≤ 230 := hl
  refine ⟨hl, NativeRustcVm.BytesAt.of_sameOutside hw hs fun i hi hr ↦ ?_,
    NativeRustcVm.BytesAt.of_sameOutside hws hs fun i hi hr ↦ ?_⟩
  · rw [NativeRustcVm.length_wordBytes] at hi
    have e : (qA m0 + BitVec.ofNat 64 i).toNat = (pA m0).toNat + 61352 + i := by
      rw [toNat_off' (by rw [hq]; have := g.pW; omega), hq]
    have := hR _ hr
    rw [e] at this
    omega
  · rw [NativeRustcVm.length_wordsBytes] at hi
    have e : (qA m0 + 8#64 + BitVec.ofNat 64 i).toNat = (pA m0).toNat + 61352 + (8 + i) := by
      rw [show qA m0 + 8#64 = qA m0 + BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add,
        toNat_off' (by rw [hq]; have := g.pW; omega), hq]
    have := hR _ hr
    rw [e] at this
    omega

/-- **The `TState` kept** by a change apart from it and the decoded area. -/
theorem ts_keep (h : NextLevelPre a s level w rounds m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hk : Kept d d') (hs : SameOutside d d' R)
    (hR : ∀ q, R q → (q.toNat < (tA m0).toNat ∨ (tA m0).toNat + 760 ≤ q.toNat) ∧
      (q.toNat < a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ q.toNat))
    {s' : TState} (hts : TStateAt d (tA m0) a s') : TStateAt d' (tA m0) a s' :=
  hts.frame hk (fun q hq ↦ ⟨nin (geo h).tW (hR q hq).1, nin (geo h).aW (hR q hq).2⟩) hs

/-- **Words of the decoded area kept** by a change apart from it. -/
theorem words_keep (h : NextLevelPre a s level w rounds m0) {d d' : Mem 64}
    {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    (hR : ∀ q, R q → q.toNat < a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ q.toNat)
    {x : BitVec 64} {ws : List UInt64}
    (hx : a.words.toNat ≤ x.toNat ∧ x.toNat + 8 * ws.length ≤ a.words.toNat + 8 * a.len)
    (hb : NativeRustcVm.WordsAt d x ws) : NativeRustcVm.WordsAt d' x ws := by
  have g := geo h
  refine NativeRustcVm.BytesAt.of_sameOutside hb hs fun i hi hr ↦ ?_
  rw [NativeRustcVm.length_wordsBytes] at hi
  have e : (x + BitVec.ofNat 64 i).toNat = x.toNat + i :=
    toNat_off' (by have := g.aW; omega)
  have := hR _ hr
  rw [e] at this
  omega

end

end

end NativeRustcVmArm.Whir.NextLevel
