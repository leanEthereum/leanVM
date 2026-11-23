module

public import NativeRustcVmX64.Whir.FinalLevel.Sum
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names

/-!
# `final_level`: a `Buf<EW, 30>::extend` call and its test (x86-64)

`ext_call`: from a call to `extend` at RSP offset `32` (the buffer in the frame at `j`, holding
`xs`; the slice `ys` at `src`, apart from it; `xs ++ ys` fits), the call and the test of its
`bool` (a block equal to `b5`): to the next block with the buffer holding `xs ++ ys`, the
callee-saved registers, the frame's bytes off the buffer and the `TState` kept.
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel

public section

theorem bufEWOf_eq {d : Mem 64} {p : BitVec 64} {xs : List EW}
    (h : NativeRustcVm.BufEWAt d p 30 xs) : NativeRustcVm.bufEWOf d p = xs := by
  unfold NativeRustcVm.bufEWOf
  have hl : xs.length ≤ 30 := h.1
  rw [NativeRustcVm.wordOf_of_wordAt h.2.1, Nat.toUInt64, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega), NativeRustcVm.ewsOf_of_ewsAt h.2.2]

theorem slice_eq {m : MachineData} {u n : BitVec 64} {xs : List EW} (hn : n.toNat = xs.length)
    (h : NativeRustcVm.EWsAt m.dmem u xs) : slice m u n = xs.toArray := by
  unfold slice
  rw [hn, NativeRustcVm.ewsOf_of_ewsAt h]

/-- Frame bytes from `40` kept but `[lo, lo + n)`: the form of a call's `hkeep` at RSP `32`. -/
abbrev KeepF (m0 : MachineData) (d d' : Mem 64) (lo n : Nat) : Prop :=
  ∀ j, 32 + 8 ≤ j → j < 2688 → (j < lo ∨ lo + n ≤ j) → d'.get? (loc m0 j) = d.get? (loc m0 j)

theorem KeepF.bytes {m0 : MachineData} {d d' : Mem 64} {lo n : Nat} (h : KeepF m0 d d' lo n)
    {j : Nat} {bs : List UInt8} (hj : 40 ≤ j) (hjn : j + bs.length ≤ 2688)
    (hmiss : j + bs.length ≤ lo ∨ lo + n ≤ j) (hb : NativeRustcVm.BytesAt d (loc m0 j) bs) :
    NativeRustcVm.BytesAt d' (loc m0 j) bs := by
  intro i hi
  have := hb i hi
  rw [off_add] at this ⊢
  rw [h (j + i) (by omega) (by omega) (by omega)]
  exact this

theorem KeepF.word {m0 : MachineData} {d d' : Mem 64} {lo n : Nat} (h : KeepF m0 d d' lo n)
    {j : Nat} {u : UInt64} (hj : 40 ≤ j) (hjn : j + 8 ≤ 2688) (hmiss : j + 8 ≤ lo ∨ lo + n ≤ j)
    (hb : NativeRustcVm.WordAt d (loc m0 j) u) : NativeRustcVm.WordAt d' (loc m0 j) u :=
  h.bytes hj (by simp [NativeRustcVm.length_wordBytes]; omega)
    (by simp [NativeRustcVm.length_wordBytes]; omega) hb

theorem KeepF.ews {m0 : MachineData} {d d' : Mem 64} {lo n : Nat} (h : KeepF m0 d d' lo n)
    {j : Nat} {xs : List EW} (hj : 40 ≤ j) (hjn : j + 16 * xs.length ≤ 2688)
    (hmiss : j + 16 * xs.length ≤ lo ∨ lo + n ≤ j) (hb : NativeRustcVm.EWsAt d (loc m0 j) xs) :
    NativeRustcVm.EWsAt d' (loc m0 j) xs :=
  h.bytes hj (by rw [NativeRustcVm.length_ewsBytes]; omega)
    (by rw [NativeRustcVm.length_ewsBytes]; omega) hb

theorem KeepF.buf {m0 : MachineData} {d d' : Mem 64} {lo n : Nat} (h : KeepF m0 d d' lo n)
    {j : Nat} {xs : List EW} (hj : 40 ≤ j) (hjn : j + 488 ≤ 2688)
    (hmiss : j + 488 ≤ lo ∨ lo + n ≤ j) (hb : NativeRustcVm.BufEWAt d (loc m0 j) 30 xs) :
    NativeRustcVm.BufEWAt d' (loc m0 j) 30 xs := by
  have hl : xs.length ≤ 30 := hb.1
  refine ⟨hl, h.word hj (by omega) (by omega) hb.2.1, ?_⟩
  have e : loc m0 j + 8#64 = loc m0 (j + 8) := off_add _ _ _
  have := hb.2.2
  rw [e] at this ⊢
  exact h.ews (by omega) (by omega) (by omega) this

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s level ba b w rounds m0)
include c

/-- An input of the entry apart from the frame's bytes. -/
theorem apart_in {x : BitVec 64} {n : Nat} (h : WhirIn m0 x n finalLevelStack) {j len : Nat}
    (hj : j + len ≤ 2680) : NativeRustcVm.Apart x n (loc m0 j) len := by
  have g := c.geo
  have h1 : NativeRustcVm.Apart x n (stackBelow m0 finalLevelStack) (finalLevelStack + 8) := h.2
  unfold NativeRustcVm.Apart at h1 ⊢
  rw [c.stk_toNat, stack_eq] at h1
  rw [c.loc_toNat (by omega)]
  have := g.hN
  omega

/-- The empty slice at `8` for a callee entered at RSP offset `o`. -/
theorem in8 {o : Nat} (ho : o ≤ 2672) {d : MachineData} (hf : Fr m0 o d) {N' : Nat}
    (hle : 2672 - o + N' + 8 ≤ finalLevelStack) : WhirIn d (BitVec.ofNat 64 8) 0 N' := by
  have g := c.geo
  have hat := c.at_call ho hf
  have h1 := g.hN
  rw [stack_eq] at hle
  have hsb : (stackBelow d N').toNat = (rspOf m0).toNat - 2672 + o - N' := by
    rw [stackBelow_callee hat.sp (by omega), stackBelow_toNat (by omega)]
    omega
  refine ⟨⟨fun i hi ↦ absurd hi (by omega),
    show (BitVec.ofNat 64 8).toNat + 0 ≤ 2 ^ 64 by simp⟩, ?_⟩
  show NativeRustcVm.Apart _ _ _ _
  unfold NativeRustcVm.Apart
  rw [hsb]
  left
  simp only [BitVec.toNat_ofNat]
  omega

end Ctx

end

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **An `extend` call and its test.** -/
theorem ext_call (hp : Placed code k) (c : Ctx a s level ba b w rounds m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    {st : MachineState} {jt : Nat} (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel)
    (hret : retOf st.data = Host.addrOf (k + jt)) {bt : List Directive}
    (hbt : bt.IsInfixAt code jt) (hb5 : bt = b5)
    (hf : Fr m0 32 st.data) {j : Nat} (hj : 40 ≤ j) (hjn : j + 488 ≤ 2624)
    (hdi : reg st.data .rdi = loc m0 j) {xs ys : List EW}
    (hbuf : NativeRustcVm.BufEWAt st.data.dmem (loc m0 j) 30 xs) {src : BitVec 64}
    (hsi : reg st.data .rsi = src) (hdx : (reg st.data .rdx).toNat = ys.length)
    (hys : NativeRustcVm.EWsAt st.data.dmem src ys)
    (hin : WhirIn st.data src (16 * ys.length) bufEWExtendStack)
    (hap : NativeRustcVm.Apart (loc m0 j) 488 src (16 * ys.length))
    (hfit : xs.length + ys.length ≤ 30) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + jt + 2) → Fr m0 40 st'.data →
      NativeRustcVm.BufEWAt st'.data.dmem (loc m0 j) 30 (xs ++ ys) →
      (∀ r, calleeSaved r = true → reg st'.data r = reg st.data r) →
      KeepF m0 st.data.dmem st'.data.dmem j 488 →
      (∀ {s' : TState}, TStateAt st.data.dmem (tA m0) a s' →
        TStateAt st'.data.dmem (tA m0) a s') →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hat := c.at_call (o := 32) (by omega) hf
  have hle : 2672 - 32 + bufEWExtendStack ≤ finalLevelStack := by decide
  have hbin := c.inLoc (o := 32) (by omega) hf hle (j := j) (n := 488) (by omega) (by omega)
  have hlx : xs.length ≤ 30 := hbuf.1
  have hw : (NativeRustcVm.wordOf st.data.dmem (loc m0 j)).toNat = xs.length := by
    rw [NativeRustcVm.wordOf_of_wordAt hbuf.2.1, Nat.toUInt64, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)]
  have hpre : BufEWExtendPre 30 st.data := by
    refine ⟨(c.sctx (by decide)).stackOk hat hle, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (NativeRustcVm.wordOf st.data.dmem (reg st.data .rdi)).toNat ≤ 30
      rw [hdi, hw]; exact hlx
    · show Readable st.data (reg st.data .rdi) (8 + 16 * 30)
      rw [hdi]; exact hbin.1
    · show Readable st.data (reg st.data .rsi) (16 * (reg st.data .rdx).toNat)
      rw [hsi, hdx]; exact hin.1
    · show NativeRustcVm.Apart (reg st.data .rdi) (8 + 16 * 30) (reg st.data .rsi)
        (16 * (reg st.data .rdx).toNat)
      rw [hdi, hsi, hdx]; exact hap
    · show OffStack st.data (reg st.data .rdi) (8 + 16 * 30) bufEWExtendStack
      rw [hdi]; exact hbin.2
    · show OffStack st.data (reg st.data .rsi) (16 * (reg st.data .rdx).toNat) bufEWExtendStack
      rw [hsi, hdx]; exact hin.2
  refine call_then (env := Env.ofMachine st.data []) (next := Host.addrOf (k + jt))
    ⟨hpc, hret⟩ hext hpre fun st1 hpc1 hrsp1 hq ↦ ?_
  obtain ⟨hr, hch, hsv⟩ := hq
  have hch' : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem (fun q ↦
      NativeRustcVm.InRange (loc m0 j) 488 q ∨
        NativeRustcVm.InRange (stackBelow st.data bufEWExtendStack) bufEWExtendStack q) :=
    NativeRustcVm.SameOutside.mono hch fun q hq ↦ by
      rcases hq with hq | hq
      · left; rw [hdi] at hq; exact hq
      · exact Or.inr hq
  obtain ⟨hf1, hkeep1⟩ := c.call (o := 32) (by omega) hf hle hsv hrsp1
    (R := NativeRustcVm.InRange (loc m0 j) 488) (lo := j) (n := 488) (by omega) (by omega)
    (fun q hq ↦ Or.inr hq) hch'
  have hts1 : ∀ {s' : TState}, TStateAt st.data.dmem (tA m0) a s' →
      TStateAt st1.data.dmem (tA m0) a s' := fun h ↦
    c.ts_call (o := 32) (by omega) hf hle hsv (fun q hq ↦ c.loc_not_t (by omega) hq) hch' h
  rw [hdi, hw, hdx] at hr
  simp only [hfit, ite_true] at hr
  obtain ⟨hal, hbuf1⟩ := hr
  rw [bufEWOf_eq hbuf, hsi, slice_eq hdx hys] at hbuf1
  subst hb5
  refine Eventually.bind (test_spec hp c hbt rfl exit_b5 ok_b5 hf1 hpc1 (x := true) hal)
    fun st2 ⟨hr2, hd2, hpc2⟩ ↦ ?_
  simp only [ite_true] at hpc2
  exact cont st2 hpc2 (hf1.congr hr2 hd2) (by rw [hd2]; exact hbuf1)
    (fun r hr' ↦ (hr2 r).trans (hsv.1 r hr'))
    (fun jj h1 h2 h3 ↦ by rw [hd2]; exact hkeep1 jj (by omega) h2 h3)
    (fun h ↦ by rw [hd2]; exact hts1 h)

end

end NativeRustcVmX64.Whir.Levels.FL
