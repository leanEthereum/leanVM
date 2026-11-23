module

public import NativeRustcVmArm.Tables.TableTerms.Blocks
public import NativeRustcVmArm.Tables.TableTerms.Regions

/-!
# `table_terms`: the iteration over table `i`, what it keeps

After table `i`'s evaluations `xs` were read (the `TState` then at `s'`): the frame, the frame's
argument words, the registers walking the tables, the `TState`, the evaluations' `Buf` at entry
`i`'s byte `488`, the finished entries (`It`). `It.step`: across a block or a call that changes
only the stack and entry `i`'s first `488` bytes. `wok_frame`: a block whose writes are all in the
frame; `written_stack`: they are in the stack.
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout
open NativeRustcVm (wordOf ewsOf BufEWAt)

@[expose] public section

/-- **During table `i`**, its evaluations `xs` read, the `TState` at `s'`, the entries before it
`o`. -/
structure It [Labels] (a : DecArea) (m0 : MachineData) (i : Nat) (o : Array (Array EW × Array EW))
    (xs : Array EW) (s' : TState) (m : MachineData) : Prop where
  fr : Fr m0 288 N slots [] (outs m0) m
  cw : FW m0 m (cws m0)
  x21 : rg m .X21 = T + BitVec.ofNat 64 (8 + 40 * (i + 1))
  x20 : rg m .X20 = rg m0 .X7 + BitVec.ofNat 64 (17784 * i)
  x27 : rg m .X27 = evi m0 i
  x29 : rg m .X29 = BitVec.ofNat 64 (240 - 40 * i)
  x26 : rg m .X26 = BitVec.ofNat 64 (cursorAt i)
  ts : TStateAt m.dmem m0.regs.X1.toBitVec a s'
  vals : BufEWAt m.dmem (evi m0 i + BitVec.ofNat 64 488) 92 xs.toList
  evs : ∀ j (h : j < o.size), TableEvalAt m.dmem (evi m0 j) o[j]
  osz : o.size = i

end

public section

/-- A block's writes, all in the frame. -/
theorem wok_frame {S : SState} {szs : List Nat} {outR : List Bool}
    (hL : outR.all (· == false) = true) (h : wok S szs outR = true) :
    ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 288 := by
  intro w hw
  have := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this with ⟨⟨hr, hle⟩, -⟩ | ⟨-, ho⟩
  · exact ⟨hr, hle⟩
  · exfalso
    rw [List.getD_eq_getElem?_getD] at ho
    cases hv : outR[w.r]? with
    | none => rw [hv] at ho; cases ho
    | some v =>
      rw [hv] at ho
      have := List.all_eq_true.mp hL v (List.mem_of_getElem? hv)
      simp only [Option.getD_some] at ho
      rw [ho] at this
      cases this

/-- Writes in the frame are in the stack. -/
theorem written_stack {m0 m : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hN : N ≤ m0.regs.SP.toNat) (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 288) {q : BitVec 64}
    (hq : Written (Env.ofMachine m ((base m0 288, 288) :: rs)) S q) :
    InRange (stackBelow m0 N) N q :=
  Bus.frame_inRange hN (by rw [N_eq]; omega)
    (Bus.Written.inRange (r := 0) rfl (base_noWrap (by rw [N_eq] at hN; omega)) hw hq)

theorem cs_saved : ∀ r ∈ cs, calleeSaved r = true := by decide

/-- The frame's words depend on the memory only. -/
theorem FW.of_dmem {m0 m m' : MachineData} {L : List (Nat × BitVec 64)} (hd : m'.dmem = m.dmem)
    (h : FW m0 m L) : FW m0 m' L := fun p hp ↦ by rw [← h p hp]; unfold fw; rw [hd]

theorem cl_offs (m0 : MachineData) (i : Nat) :
    (cws m0 ++ lws m0 i).map Prod.fst = [16, 24, 32, 40, 48, 56, 96, 104] := rfl

theorem cl_mem {m0 : MachineData} {i : Nat} {p : Nat × BitVec 64} (hp : p ∈ cws m0 ++ lws m0 i) :
    p.1 ∈ [16, 24, 32, 40, 48, 56, 96, 104] := by
  rw [← cl_offs m0 i]; exact List.mem_map_of_mem hp

theorem cl_le {m0 : MachineData} {i : Nat} {p : Nat × BitVec 64} (hp : p ∈ cws m0 ++ lws m0 i) :
    p.1 + 8 ≤ 288 := by
  have := cl_mem hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  omega

/-- `cbz w0` of an `Option<()>`. -/
theorem okWord_eq0 (b : Bool) :
    CmpOp.eq.apply .W32 (okWord b).toBitVec (BitVec.ofNat 64 0) = !b := by
  cases b <;> decide

section
variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

theorem e488_in (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {q : BitVec 64}
    (hq : InRange (evi m0 i) 488 q) : InRange (evi m0 i) 1968 q :=
  NativeRustcVm.InRange.mono hq (NativeRustcVm.NoWrap.mono (evi_noWrap h hi) (by omega))
    (evi_noWrap h hi) le_rfl (by omega)

/-- A byte from entry `i`'s byte `488` is not one of its first `488`. -/
theorem not_e488 (h : TableTermsPre a s heights forms m0) {i j : Nat} (hi : i < 6) (hj : j < 1480) :
    ¬InRange (evi m0 i) 488 (evi m0 i + BitVec.ofNat 64 488 + BitVec.ofNat 64 j) := by
  rw [NativeRustcVm.addr_add_add]
  have := NativeRustcVm.not_inRange_sub (a := evi m0 i) (o := 0) (m := 488) (evi_noWrap h hi)
    (by omega) (show 488 + j < 1968 by omega) (.inr (by omega))
  rwa [NativeRustcVm.addr_add_zero] at this

/-- **Across a change** of the stack and entry `i`'s first `488` bytes. -/
theorem It.step (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6)
    {o : Array (Array EW × Array EW)} {xs : Array EW} {s' : TState} {m m' : MachineData}
    (H : It a m0 i o xs s' m) (hfr : Fr m0 288 N slots [] (outs m0) m')
    (hk : Kept m.dmem m'.dmem) {W : BitVec 64 → Prop} (hs : SameOutside m.dmem m'.dmem W)
    (hW : ∀ q, W q → InRange (stackBelow m0 N) N q ∨ InRange (evi m0 i) 488 q)
    (cw : FW m0 m' (cws m0)) (r : ∀ x ∈ [XReg.X20, .X21, .X26, .X27, .X29],
      m'.regs.getXReg x = m.regs.getXReg x) : It a m0 i o xs s' m' := by
  have hch : ∀ q, W q → Ch m0 i q := fun q hq ↦
    (hW q hq).elim .inl fun h' ↦ .inr (.inl (e488_in h hi h'))
  refine ⟨hfr, cw, ?_, ?_, ?_, ?_, ?_, ts_keep h hi hk hs hch H.ts, ?_, fun j hj ↦ ?_, H.osz⟩
  · rw [rg, r .X21 (by simp)]; exact H.x21
  · rw [rg, r .X20 (by simp)]; exact H.x20
  · rw [rg, r .X27 (by simp)]; exact H.x27
  · rw [rg, r .X29 (by simp)]; exact H.x29
  · rw [rg, r .X26 (by simp)]; exact H.x26
  · refine BufEWAt.of_same H.vals (n := 1480) (Same.of_sameOutside hs fun j hj hq ↦ ?_) (by omega)
    rcases hW _ hq with hq | hq
    · have hin : InRange (evi m0 i) 1968 (evi m0 i + BitVec.ofNat 64 488 + BitVec.ofNat 64 j) := by
        rw [NativeRustcVm.addr_add_add]
        exact NativeRustcVm.inRange_add (by omega) (by norm_num)
      exact NativeRustcVm.Apart.not_inRange (evi_out h hi).2.2.2.2.1 (evi_noWrap h hi)
        (Bus.stack_noWrap (Pre.stack h)) hin hq
    · exact not_e488 h hi hj hq
  · exact ev_keep h hi (by rw [← H.osz]; exact hj) hs (fun q hq ↦ .inl (hch q hq)) (H.evs j hj)

end

end

end NativeRustcVmArm.Tables.TableTerms
