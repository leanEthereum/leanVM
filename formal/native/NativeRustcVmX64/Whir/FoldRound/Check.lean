module

public import NativeRustcVmX64.Whir.FoldRound.Exit
public import NativeRustcVmX64.Code.Vm.FoldRound.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names

/-!
# `fold_round` on x86-64: a read and its check

`readCheck`: from a state before a call of `read_scalar` into the frame's words `8` to `32`, the
call and the next block's test of the tag: on `None` the `None` exit, on `Some x` a body state
with `x` at the frame's words `16`, `24`, the frame's words from `32` on and the callee-saved
registers kept. `b1`'s and the later blocks' tests (`c_b1`, `c_b3`).
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRound
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk load4_of_tag load1_of_tag)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept wrote_spec kept_spec wr0_spec
  miss_spec midOk_writesIn)
open NativeRustcVm (WordAt EWAt EWsAt)

public section

section
variable [Labels]

/-- `b1`'s test. -/
theorem c_b1 (e : Env) (v : UInt64) (hv : v = 0 ∨ v = 1)
    (h4 : e.load 0 8 4 = BitVec.ofNat 64 v.toNat) (_ : e.load 0 8 1 = BitVec.ofNat 64 v.toNat) :
    (SBool.not (.cmp .eq .W32 (.load 0 8 4) (.lit 1))).eval e = (v == 0) := by
  rcases hv with rfl | rfl <;> simp only [SBool.eval, Sym.eval, h4] <;> decide

/-- The later reads' test. -/
theorem c_b3 (e : Env) (v : UInt64) (hv : v = 0 ∨ v = 1)
    (_ : e.load 0 8 4 = BitVec.ofNat 64 v.toNat) (h1 : e.load 0 8 1 = BitVec.ofNat 64 v.toNat) :
    (SBool.cmp .eq .W8 (.load 0 8 1) (.lit 0)).eval e = (v == 0) := by
  rcases hv with rfl | rfl <;> simp only [SBool.eval, Sym.eval, h1] <;> decide

end

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}

/-- **`read_scalar` and the tag's test.** -/
theorem readCheck (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {s : TState} {st1 : MachineState}
    (h1 : AtCall m0 176 foldRoundStack slots (outs m0) (tA m0) a s st1.data)
    (hmem1 : SameOutside m0.dmem st1.data.dmem (Pre18 m0))
    (hrdi : reg st1.data .rdi = off (fb m0) 8) (hrsi : reg st1.data .rsi = tA m0)
    (hbx : reg st1.data .rbx = oA m0) (h14 : reg st1.data .r14 = pA m0) {j : Nat}
    (hpc : st1.pc = Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel ∧ retOf st1.data = Host.addrOf (k + j))
    {b : List Directive} (hb : b.IsInfixAt code j) (hne : b ≠ []) {S : SState} {c : SBool}
    (hrun : exec b midS = some (S, .cond c NativeRustcVmX64.Vm.FoldRound.label_7))
    (hok : MidOk 176 8 slots S = true ∧ S.mem = [] ∧ kept S cs = true)
    (hc : ∀ (e : Env) (v : UInt64), (v = 0 ∨ v = 1) → e.load 0 8 4 = BitVec.ofNat 64 v.toNat →
      e.load 0 8 1 = BitVec.ofNat 64 v.toNat → c.eval e = (v == 0))
    (hnone : readScalar.run s = none → (foldRound w).run s0 = none)
    (cont : ∀ (x : EW) (s' : TState) (st : MachineState), readScalar.run s = some (x, s') →
      st.pc = Host.addrOf (k + j + b.length) → Bd m0 a s' st.data →
      WordAt st.data.dmem (off (fb m0) 16) x.c0 → WordAt st.data.dmem (off (fb m0) 24) x.c1 →
      (∀ o, 32 ≤ o → o + 8 ≤ 176 → ∀ v, WordAt st1.data.dmem (off (fb m0) o) v →
        WordAt st.data.dmem (off (fb m0) o) v) →
      (∀ r, calleeSaved r = true → reg st.data r = reg st1.data r) →
      Eventually (step1 Host.exe) (Goal a s0 w m0) st) :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st1 := by
  have cx := ctx h
  have hfnw : (fb m0).toNat + (176 + 8) ≤ 2 ^ 64 := cx.fnw
  have hfnw' : (stackBelow m0 176).toNat + (176 + 8) ≤ 2 ^ 64 := cx.fnw
  refine h1.readScalar cx hrs slots_le rs_le (ob := 8) (by omega) (by omega) slots_32 hrdi hrsi
    hpc fun st2 hpc2 hw2 hopt hnext hcs hso ↦ ?_
  have hR : ∀ x, 32 ≤ x → x < 184 → ¬ ((InRange (stackBelow m0 foldRoundStack) foldRoundStack
      (off (fb m0) x) ∧ ¬ InRange (stackBelow m0 176) (176 + 8) (off (fb m0) x)) ∨
      InRange (off (stackBelow m0 176) 8) 24 (off (fb m0) x) ∨
      InRange (tA m0) tstateBytes (off (fb m0) x)) := by
    intro x hx1 hx2 hq
    have hn := frame_not_call h hx2
    rcases hq with hq | hq | hq
    · exact hn.1 hq
    · exact off_not_in (N := 184) hfnw hx2 (by omega) (by omega) hq
    · exact hn.2 hq
  have hmem2 : SameOutside m0.dmem st2.data.dmem (Pre18 m0) := by
    refine mem_trans hmem1 hso fun q hq ↦ ?_
    rcases hq with hq | hq | hq
    · exact .inl hq.1
    · exact .inl (cx.frame_stack (Transcript.inRange_of_off (N := 176)
        (by unfold NativeRustcVm.NoWrap; omega) (by omega) hq))
    · exact .inr hq
  have hwf := cx.wf0 (vars := fun _ ↦ 0) (ret := 0) hw2.fr.kept
  refine exec_at (inf hp hb hne) hrun hwf (by intro l h; cases h) hpc2 hw2.mid
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid, hmem, hk⟩ := hok
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf hmem
  have hw3 := WFr.block cx hw2 hwf hm3 hmid slots_le fun q hq ↦ absurd hq (no_written hmem)
  have hcs3 : ∀ r, calleeSaved r = true → reg st3.data r = reg st1.data r := fun r hr ↦
    (hm3.regs r _ (kept_spec hk (cs_of hr))).trans (hcs r hr)
  simp only [PcOk] at hpc3
  cases hr : readScalar.run s with
  | none =>
    have h0 : WordAt st2.data.dmem (off (fb m0) 8) 0 := by rw [hr] at hopt; exact hopt
    have hce := hc (frameEnv m0 st2.data 176 [] (fun _ ↦ 0) 0) 0 (.inl rfl)
      (load4_of_tag (.inl rfl) h0) (load1_of_tag (.inl rfl) h0)
    rw [hce] at hpc3
    simp only [show ((0 : UInt64) == 0) = true from rfl, ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.FoldRound.label_7_at] at hpc3
    exact none20 hp h hpc3 hw3 ((hcs3 .rbx rfl).trans hbx) (hnone hr)
  | some y =>
    obtain ⟨x, s'⟩ := y
    have h1' : OptEWAt st2.data.dmem (off (fb m0) 8) (some x) := by rw [hr] at hopt; exact hopt
    obtain ⟨ht, hx⟩ := h1'
    rw [ewAt_iff, off_off, off_off] at hx
    have hce := hc (frameEnv m0 st2.data 176 [] (fun _ ↦ 0) 0) 1 (.inr rfl)
      (load4_of_tag (.inr rfl) ht) (load1_of_tag (.inr rfl) ht)
    rw [hce] at hpc3
    simp only [show ((1 : UInt64) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hpc3
    refine cont x s' st3 hr hpc3 ⟨hw3, hd3 ▸ hmem2, hd3 ▸ hnext x s' hr,
      (hcs3 .rbx rfl).trans hbx, (hcs3 .r14 rfl).trans h14⟩ (hd3 ▸ hx.1) (hd3 ▸ hx.2)
      (fun o ho1 ho2 v hv ↦ hd3 ▸ frame_keep hso (fun i hi ↦ hR (o + i) (by omega) (by omega)) hv)
      hcs3

end

end NativeRustcVmX64.Whir.FoldRound
