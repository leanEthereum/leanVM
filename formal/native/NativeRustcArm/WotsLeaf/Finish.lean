module

public import NativeRustcArm.WotsLeaf.Epilogue
public import NativeRustcArm.WotsLeaf.Input
public import NativeRustcArm.WotsLeaf.Codeword.Exec

/-!
# Returning the result

`finish`: from `b12` (directive 164) with SP the frame's base, the saved registers in place, the
entry's mapped bytes kept, memory changed only at `out` and in the stack area, and the result at
`out` (`WotsLeafOut`), the function returns with its postcondition (`Run.Done`). `fail_path`:
from `b11` (directive 162, `.LWotsLeaf_5`) the tag `0` stored at `out`, then `finish`. The frame's
environment with `out` as region 1 (`Run.outEnv`, `outEnv_wf`, `match_out`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym

public section

theorem length_savedBytes' (m : MachineData) : (savedBytes m).length = 96 := by
  rw [savedBytes, Native.Keccak.Proof.length_wordsBytes]
  rfl

section
variable {r : Run} [Labels]

/-- The frame's environment with `out` as region 1 is well formed. -/
theorem outEnv_wf (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) (vars : Nat → BitVec 64) :
    (r.envR m [(r.out, 75)] vars).WF := by
  have hout := r.pre_out hpre
  refine r.frame_wfR hpre hF (rest := [(r.out, 75)])
    ⟨⟨r.input_mapped hF.2.2.2.2 hout, hout.2.1⟩, trivial⟩ ?_
    (List.pairwise_singleton _ _) vars
  intro e he
  simp only [List.mem_singleton] at he
  subst he
  have := r.apart_input hpre (a := 0) (n' := 2752) (by decide) hout
  rwa [Run.off_zero] at this

/-- A fresh symbolic state with `out` as region 1. -/
theorem match_out (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {known : List (XReg × Sym)}
    (hk : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.envR m [(r.out, 75)])) known) :
    Match (r.envR m [(r.out, 75)]) (init [(2752, true), (75, false)] (.ptr 0 0) known) m :=
  r.match_frameR hpre hF (rest := [(r.out, 75)]) (srest := [(75, false)])
    ⟨rfl, ⟨fun h ↦ absurd h (by decide), trivial⟩⟩ hk trivial
    trivial trivial

theorem eval_ptr1 (m : MachineData) (o : Nat) :
    (Sym.ptr 1 o).eval (r.envR m [(r.out, 75)]) = r.out + BitVec.ofNat 64 o := by
  simp only [Sym.eval, BitVec.ofInt_natCast]
  rfl

/-- The writes of a block all in `out` change only `out`'s bytes. -/
theorem sameOutside_out (hpre : r.Pre) {m m' : MachineData} {S : SState}
    (hm : Match (r.envR m [(r.out, 75)]) S m') (hwf : (r.envR m [(r.out, 75)]).WF)
    (hall : S.mem.all (fun w ↦ w.r == 1 && decide (w.off + w.n ≤ 75)) = true) :
    SameOutside m.dmem m'.dmem (InRange r.out 75) := by
  have hnw := (r.pre_out hpre).2.1
  intro p hp
  apply hm.get?_mem0 hwf
  rintro ⟨w, hw, b, sz, hb, h1, h2⟩
  have := List.all_eq_true.mp hall w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  obtain ⟨hr, hn⟩ := this
  rw [hr] at hb
  simp only [Run.envR, Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  apply hp
  unfold NoWrap at hnw
  rw [inRange_iff (by omega)]
  omega

end

variable [NativeRustcArm.Host]

/-- **Returning the result** from `b12`. -/
theorem finish (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) (m : MachineData)
    (hsp : m.regs.SP.toBitVec = r.base) (hsv : BytesAt m.dmem (r.off 2656) (savedBytes r.m0))
    (hk : Kept r.m0.dmem m.dmem)
    (hso : SameOutside r.m0.dmem m.dmem (fun p ↦ InRange r.out 75 p ∨ r.StackArea p))
    (hout : WotsLeafOut (bytesOf m.dmem r.out 75) r.result) :
    Eventually (step1 NativeRustcArm.Host.exe) r.Done ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b12Offset⟩ :=
  NativeRustcArm.Eventually.mono (epilogue r hp hpre m hsp hsv hk) fun st ⟨hpc, hS, hmem⟩ ↦ by
    have hb : bytesOf st.data.dmem r.out 75 = bytesOf m.dmem r.out 75 := by
      unfold bytesOf
      simp only [hmem]
    refine ⟨hpc, ?_, fun p hp' ↦ (hmem p).trans (hso p hp'), hS⟩
    show WotsLeafOut (bytesOf st.data.dmem r.out 75) r.result
    rw [hb]
    exact hout

/-- **No codeword**: from `b11`, the tag `0` at `out`, then the return. -/
theorem fail_path (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) (m : MachineData)
    (hF : r.Frame m) (h19 : Run.RegIs m .X19 r.out) (hnone : r.result = none) :
    Eventually (step1 NativeRustcArm.Host.exe) r.Done ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b11Offset⟩ := by
  have hwf := outEnv_wf hpre hF (fun _ ↦ 0)
  have hm := match_out hpre hF (known := [(.X19, .ptr 1 0)])
    ⟨by show (m.regs.getXReg .X19).toBitVec = r.out + BitVec.ofInt 64 0
        simpa [Run.RegIs] using h19, trivial⟩
  refine blk r hp Xmss.WotsLeaf.b11_in_code (List.cons_ne_nil _ _) Codeword.run_b11 hwf hm
    fun st hm' hpc ↦ pc_at hpc ?_
  have hso1 := sameOutside_out hpre hm' hwf (by decide)
  have h0 := bytesAt_write_val hm' (r := 1) (o := 0) (n := 1) (b := r.out) (sz := 75) rfl
    (by decide) (v := .lit 0) (by decide)
  refine finish r hp hpre st.data ?_ ?_ ?_ ?_ ?_
  · rw [hm'.sp]
    show r.base + BitVec.ofInt 64 0 = r.base
    simp
  · refine r.bytesAt_keptR hpre hm' hwf (by decide) (by rw [length_savedBytes'])
      hF.2.2.1 ?_
    rw [length_savedBytes']
    decide
  · exact fun p h ↦ hm'.kept hwf p (hF.2.2.2.2 p h)
  · intro p hp'
    rw [hso1 p fun h ↦ hp' (.inl h), hF.2.2.2.1 p fun h ↦ hp' (.inr h)]
  · rw [hnone]
    show (bytesOf st.data.dmem r.out 75).head? = some 0
    have := h0 0 (by simp)
    rw [addr_add_add] at this
    simp only [bytesOf, List.range_succ_eq_map, List.map_cons, List.head?_cons, this]
    simp [Sym.eval, byteOf]

end

end NativeRustcArm.WotsLeafProof
