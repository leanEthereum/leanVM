module

public import NativeRustcVmArm.Tables.TableTerms.Iter
public import NativeRustcVmArm.Bus.Frame

/-!
# `table_terms`: what the body of table `i` uses

`It` across a call (`It.call`); a slice the memory holds (`slice_of_ewsAt`); a slice of an input
read as at the entry (`ewsOf_in`); a part of an array (`extract_toArray`); the values of `b5`'s
arguments (`cpS_eval`, `nc_eval`); the frame's words across a call (`FW.out`, `FW.stack`); the
callee-saved registers of the body (`it_cs`, `body_cs`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout
open NativeRustcVm (wordOf ewsOf BufEWAt)

public section

theorem it_cs : ∀ r ∈ [XReg.X20, .X21, .X26, .X27, .X29], r ∈ cs := by simp [cs]

theorem body_cs : ∀ r ∈ [XReg.X19, .X20, .X21, .X24, .X25, .X26, .X27, .X28, .X29], r ∈ cs := by
  simp [cs]

/-- `add x, #c`. -/
theorem eval_add_lit [Labels] (env : Env) (x : Sym) (c : Nat) :
    (Sym.bin .add .W64 x (.lit c)).eval env = x.eval env + BitVec.ofNat 64 c := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]

/-- `cmp x, y; csel lo`: the smaller. -/
theorem eval_min [Labels] (env : Env) (x y : Sym) :
    (Sym.ite (.cmp .ult .W64 x y) x y).eval env =
      if (x.eval env).toNat < (y.eval env).toNat then x.eval env else y.eval env := by
  show (if (low .W64 (x.eval env)).ult (low .W64 (y.eval env)) = true then x.eval env
    else y.eval env) = _
  rw [low_W64, low_W64, Bus.ult_toNat]
  by_cases hlt : (x.eval env).toNat < (y.eval env).toNat <;> simp [hlt]

/-- A slice the memory holds. -/
theorem slice_of_ewsAt {m : MachineData} {p n : UInt64} {xs : Array EW}
    (h : NativeRustcVm.EWsAt m.dmem p.toBitVec xs.toList) (hn : n.toNat = xs.size) :
    slice m p n = xs := by
  unfold slice
  rw [hn, ← Array.length_toList, NativeRustcVm.ewsOf_of_ewsAt h]

/-- A part of an array of a list. -/
theorem extract_toArray {α : Type} (l : List α) (c n : Nat) :
    l.toArray.extract c (c + n) = ((l.drop c).take n).toArray := by
  apply Array.toList_inj.mp
  simp

/-- `b5`'s first argument: the constraint powers from the cursor `c ≤ 2`. -/
theorem cpS_eval [Labels] {env : Env} {c : Nat} (hc : c ≤ 2)
    (h26 : env.regs .X26 = BitVec.ofNat 64 c) :
    cpS.eval env = (Sym.load 0 24 8).eval env + BitVec.ofNat 64 (16 * c) := by
  simp only [Sym.eval, SBool.eval, h26, BinOp.apply, UnOp.apply, shiftW, low_W64, ext_W64]
  interval_cases c <;> rfl

/-- `b5`'s second argument: the table's constraints, `c + n ≤ 2`. -/
theorem nc_eval [Labels] {env : Env} {c n : Nat} (hcn : c + n ≤ 2)
    (h26 : env.regs .X26 = BitVec.ofNat 64 c)
    (hl : (Sym.load 1 16 8).eval env = BitVec.ofNat 64 n) :
    (Sym.ite (.cmp .ult .W64 (.load 1 16 8) restS) (.load 1 16 8) restS).eval env =
      BitVec.ofNat 64 n := by
  have hl' : env.load 1 16 8 = BitVec.ofNat 64 n := hl
  simp only [Sym.eval, SBool.eval, h26, hl', BinOp.apply, low_W64, ext_W64]
  have hc : c ≤ 2 := by omega
  have hn : n ≤ 2 - c := by omega
  interval_cases c <;> interval_cases n <;> rfl

section
variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

/-- **`It` across a call** using `N'` bytes of stack and writing `X`. -/
theorem It.call (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6)
    {o : Array (Array EW × Array EW)} {xs : Array EW} {s' : TState} {m m' : MachineData}
    (H : It a m0 i o xs s' m) (hfr : Fr m0 288 N slots [] (outs m0) m') {N' : Nat}
    (hle : 288 + N' ≤ N) {X : BitVec 64 → Prop}
    (hs : SameOutside m.dmem m'.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨ X q))
    (hX : ∀ q, X q → InRange (stackBelow m0 N) N q ∨ InRange (evi m0 i) 488 q)
    (hXc : ∀ p ∈ cws m0, ∀ j < 8, ¬X (base m0 288 + BitVec.ofNat 64 (p.1 + j)))
    (hS : Saved m m') : It a m0 i o xs s' m' := by
  have hat := Bus.Gkr.Fr.at_ (ctx h) H.fr (outs_rc h)
  have hN := spN h
  refine It.step h hi H hfr hS.2.2 hs (fun q hq ↦ hq.elim
    (fun hq ↦ .inl ((ctx h).inRange_stack hat hle hq)) (hX q)) ?_ fun r hr ↦ ?_
  · exact FW.call H.fr.sp (by omega) hs
      (fun p hp ↦ cl_le (i := 0) (List.mem_append_left (lws m0 0) hp)) hXc H.cw
  · refine hS.1 r (cs_saved r ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [cs]

/-- **The frame's words across a call** writing its stack and outputs. -/
theorem FW.out (h : TableTermsPre a s heights forms m0) {m m' : MachineData}
    (hfr : Fr m0 288 N slots [] (outs m0) m) {N' : Nat} (hle : 288 + N' ≤ N)
    {L : List (Nat × BitVec 64)} (hL : ∀ p ∈ L, p.1 + 8 ≤ 288)
    (hs : SameOutside m.dmem m'.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨ outs m0 q))
    (hw : FW m0 m L) : FW m0 m' L :=
  FW.call hfr.sp (by have := spN h; omega) hs hL
    (fun p hp j hj ↦ outs_frame_add h (by have := hL p hp; omega)) hw

/-- **The frame's words across a call** writing its stack only. -/
theorem FW.stack (h : TableTermsPre a s heights forms m0) {m m' : MachineData}
    (hfr : Fr m0 288 N slots [] (outs m0) m) {N' : Nat} (hle : 288 + N' ≤ N)
    {L : List (Nat × BitVec 64)} (hL : ∀ p ∈ L, p.1 + 8 ≤ 288)
    (hs : SameOutside m.dmem m'.dmem (fun q ↦ InRange (stackBelow m N') N' q))
    (hw : FW m0 m L) : FW m0 m' L :=
  FW.out h hfr hle hL (NativeRustcVm.SameOutside.mono hs fun _ h ↦ .inl h) hw

/-- **A slice of an input** in a state of the frame: the entry's elements. -/
theorem ewsOf_in (h : TableTermsPre a s heights forms m0) {m : MachineData}
    (hfr : Fr m0 288 N slots [] (outs m0) m) {x : BitVec 64} {n : Nat}
    (hr : ReadIn m0 x (16 * n) N (wsL m0)) : ewsOf m.dmem x n = ewsOf m0.dmem x n :=
  NativeRustcVm.ewsOf_congr (readIn_same h hfr hr)

end

end

end NativeRustcVmArm.Tables.TableTerms
