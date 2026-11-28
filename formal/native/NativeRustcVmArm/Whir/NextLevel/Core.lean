module

public import NativeRustcVmArm.Whir.NextLevel.Head
public import NativeRustcVmArm.Bus.GkrModel

/-!
# `next_level`: what lasts from `b7` on

`Base`: the registers kept to the end (the `WhirW` X19, the index X20, the fold X21, the
`TState` X22). `Facts`: frame bytes at offsets, kept by blocks missing a range of the frame
holding them (`Facts.block`) and calls writing elsewhere (`Facts.call`). Words a block writes
(`word_of`), a branch on a loaded word (`cbz_load`), bytes outside the frame and the outputs
(`out_keep`).
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel

@[expose] public section

/-- The registers kept to the end. -/
structure Base (level : Whir.Level) (m0 st : MachineData) : Prop where
  x19 : st.regs.X19 = m0.regs.X6
  x20 : st.regs.X20 = m0.regs.X1
  x21 : st.regs.X21 = level.fold.toUInt64
  x22 : st.regs.X22 = m0.regs.X0

/-- Frame bytes: `bs` at the frame's offset `o` for each `(o, bs)`. -/
def Facts (m0 : MachineData) (d : Mem 64) (l : List (Nat × List UInt8)) : Prop :=
  ∀ p ∈ l, NativeRustcVm.BytesAt d (loc m0 p.1) p.2

/-- The facts' bytes are in the frame's `[lo, lo + n)`. -/
def Within (l : List (Nat × List UInt8)) (lo n : Nat) : Prop :=
  ∀ p ∈ l, lo ≤ p.1 ∧ p.1 + p.2.length ≤ lo + n

end

public section

theorem Base.of_cs {level : Whir.Level} {m0 st st' : MachineData} (h : Base level m0 st)
    (hcs : ∀ r, calleeSaved r = true → st'.regs.getXReg r = st.regs.getXReg r) :
    Base level m0 st' :=
  ⟨(hcs .X19 rfl).trans h.x19, (hcs .X20 rfl).trans h.x20, (hcs .X21 rfl).trans h.x21,
    (hcs .X22 rfl).trans h.x22⟩

theorem Base.of_all {level : Whir.Level} {m0 st st' : MachineData} (h : Base level m0 st)
    (hr : ∀ r : XReg, st'.regs.getXReg r = st.regs.getXReg r) : Base level m0 st' :=
  h.of_cs fun r _ ↦ hr r

theorem Base.block [Labels] {level : Whir.Level} {m0 st st' : MachineData} {env : Env}
    {S0 S : SState} (h : Base level m0 st) (hm0 : Match env S0 st) (hm : Match env S st')
    (hr : sameRegs [.X19, .X20, .X21, .X22] S0 S = true) : Base level m0 st' := by
  have e := sameRegs_ok hm0 hm hr
  exact ⟨(e .X19 (by simp)).trans h.x19, (e .X20 (by simp)).trans h.x20,
    (e .X21 (by simp)).trans h.x21, (e .X22 (by simp)).trans h.x22⟩

theorem Facts.get {m0 : MachineData} {d : Mem 64} {l : List (Nat × List UInt8)}
    (h : Facts m0 d l) {o : Nat} {bs : List UInt8} (hp : (o, bs) ∈ l) :
    NativeRustcVm.BytesAt d (loc m0 o) bs :=
  h _ hp

theorem Facts.cons {m0 : MachineData} {d : Mem 64} {l : List (Nat × List UInt8)} {o : Nat}
    {bs : List UInt8} (hb : NativeRustcVm.BytesAt d (loc m0 o) bs) (h : Facts m0 d l) :
    Facts m0 d ((o, bs) :: l) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hb
  · exact h p hp

theorem Facts.sub {m0 : MachineData} {d : Mem 64} {l l' : List (Nat × List UInt8)}
    (h : Facts m0 d l) (hs : ∀ p ∈ l', p ∈ l) : Facts m0 d l' :=
  fun p hp ↦ h p (hs p hp)

theorem Within.mono {l : List (Nat × List UInt8)} {lo n lo' n' : Nat} (h : Within l lo n)
    (h1 : lo' ≤ lo) (h2 : lo + n ≤ lo' + n') : Within l lo' n' := fun p hp ↦ by
  have := h p hp; omega

theorem missAt_mono {S : SState} {r o n o' n' : Nat} (h : missAt S r o n = true) (ho : o ≤ o')
    (hn : o' + n' ≤ o + n) : missAt S r o' n' = true := by
  simp only [missAt, List.all_eq_true] at h ⊢
  intro w hw
  have := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this ⊢
  rcases this with ⟨h1, h2⟩ | h3
  · exact .inl ⟨h1, by omega⟩
  · exact .inr h3

theorem within_nil {lo n : Nat} : Within [] lo n := fun _ h ↦ by cases h

/-- A word in `[lo, lo + n)`. -/
theorem within_word {o lo n : Nat} {v : UInt64} {l : List (Nat × List UInt8)} (h1 : lo ≤ o)
    (h2 : o + 8 ≤ lo + n) (h : Within l lo n) :
    Within ((o, NativeRustcVm.wordBytes v) :: l) lo n := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨h1, by rw [NativeRustcVm.length_wordBytes]; exact h2⟩
  · exact h p hp

/-- Elements of `E` in `[lo, lo + n)`. -/
theorem within_ews {o lo n : Nat} {xs : Array EW} {l : List (Nat × List UInt8)} (h1 : lo ≤ o)
    (h2 : o + 16 * xs.size ≤ lo + n) (h : Within l lo n) :
    Within ((o, xs.toList.flatMap NativeRustcVm.ewBytes) :: l) lo n := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨h1, by rw [NativeRustcVm.length_ewsBytes, Array.length_toList]; exact h2⟩
  · exact h p hp

/-- **Facts across a block** whose writes miss the frame's `[lo, lo + n)` holding them. -/
theorem Facts.block [Labels] {m0 st m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine st ((base m0 8192, 8192) :: rs)) S m)
    (hwf : (Env.ofMachine st ((base m0 8192, 8192) :: rs)).WF) {lo n : Nat}
    (hmiss : missFrame S lo n = true) (hn : lo + n ≤ 8192) {l : List (Nat × List UInt8)}
    (hl : Within l lo n) (h : Facts m0 st.dmem l) : Facts m0 m.dmem l := fun p hp ↦ by
  have := hl p hp
  exact keepB hm hwf (missAt_mono hmiss this.1 this.2) (by omega) rfl (h p hp)

/-- **Facts across a call** writing its stack, the frame's `n'` bytes at `o'` and the outputs. -/
theorem Facts.call [Labels] {a : DecArea} {m0 st : MachineData}
    (c : TCtx m0 8192 nextLevelStack (tA m0) a (outs m0)) (hf : NFr m0 st) {N' o' n' : Nat}
    (hle : 8192 + N' ≤ nextLevelStack) (ho' : o' + n' ≤ 8192) {d' : Mem 64}
    (hs : SameOutside st.dmem d' fun q ↦ InRange (stackBelow st N') N' q ∨
      InRange (loc m0 o') n' q ∨ outs m0 q)
    {l : List (Nat × List UInt8)} {lo n : Nat} (hl : Within l lo n) (hn : lo + n ≤ 8192)
    (hd : lo + n ≤ o' ∨ o' + n' ≤ lo) (h : Facts m0 st.dmem l) : Facts m0 d' l := fun p hp ↦ by
  have := hl p hp
  exact keepC c hf hle ho' hs (by omega) (by omega) (h p hp)

/-- A word a block wrote: `v`'s value at `o` of region `r`. -/
theorem word_of [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o sz : Nat} {b : BitVec 64} (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz)
    {s : Sym} {v : UInt64} (hv : s.eval env = v.toBitVec)
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (s, i)) :
    NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) v := by
  have := hm.bytesAt_write hb hle hw
  rw [wordBytes_reg, hv] at this
  exact this

/-- `cbz x` on a word loaded from the frame. -/
theorem cbz_load [Labels] {env : Env} {o : Nat} {v : UInt64} (h : env.load 0 o 8 = v.toBitVec) :
    SBool.eval env (.cmp .eq .W64 (.load 0 o 8) (.lit 0)) = (v == 0) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, h]
  by_cases hv : v = 0
  · subst hv; rfl
  · have : v.toBitVec ≠ 0#64 := fun e ↦ hv (UInt64.toBitVec_inj.mp e)
    simp [hv, this]

/-- **Bytes kept** where a change misses them. -/
theorem out_keep {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    {b : BitVec 64} {bs : List UInt8} (hb : NativeRustcVm.BytesAt d b bs)
    (hR : ∀ i < bs.length, ¬R (b + BitVec.ofNat 64 i)) : NativeRustcVm.BytesAt d' b bs :=
  hb.of_sameOutside hs hR

end

end NativeRustcVmArm.Whir.NextLevel
