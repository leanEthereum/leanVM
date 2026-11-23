module

public import NativeRustcVmArm.Bus.AccumulateSide.Desc

/-!
# `accumulate_side`: the blocks' starting states, the frame's `FormBuf`

`matchR`: a state of the body as a block's literal start state, the frame and `A` bytes above it
region `0`, one more region, a register its alias. `ROk.sub`: a part of an input as a block's
region. `holds_ret`: a call's result added to a description. The `FormBuf` `block_form` writes
at frame byte `152` through blocks writing below it (`fb_block`) and calls (`fb_call`).
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

section
variable [Labels] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

theorem sp_eval {m : MachineData} (hsp : m.regs.SP.toBitVec = base m0 F) {A : Nat}
    (rs : List (BitVec 64 × Nat)) (vars : Nat → BitVec 64) :
    m.regs.SP.toBitVec = (Sym.ptr 0 0).eval (Env.ofMachine m ((base m0 F, F + A) :: rs) vars) := by
  simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
    Option.getD_some]
  rw [hsp]; simp

/-- **The frame and `A` bytes above it**, a block's start. -/
theorem matchF (h : Pre L rows bl Fm SL m0) {m : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 F) :
    Match (Env.ofMachine m [(base m0 F, F + 0)]) sF m :=
  match_ofMachine (sregions := [(F + 0, true)]) (regions := [(base m0 F, F + 0)])
    ⟨rfl, fun _ ↦ Bus.base_aligned h.stack (by decide) rfl, trivial⟩ (sp_eval hsp _ _)
    trivial trivial trivial trivial

/-- **The frame and another region**, register `r` its byte `o`. -/
theorem matchR (h : Pre L rows bl Fm SL m0) {m : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 F) {a : BitVec 64} {n : Nat} {r : XReg} {o : Nat}
    (hr : (m.regs.getXReg r).toBitVec = a + BitVec.ofNat 64 o) :
    Match (Env.ofMachine m [(base m0 F, F + 0), (a, n)])
      (init [(F + 0, true), (n, false)] (.ptr 0 0) [(r, .ptr 1 o)]) m :=
  match_ofMachine (sregions := [(F + 0, true), (n, false)])
    (regions := [(base m0 F, F + 0), (a, n)])
    ⟨rfl, fun _ ↦ Bus.base_aligned h.stack (by decide) rfl, rfl, nofun, trivial⟩
    (sp_eval hsp _ _)
    ⟨by simp only [Sym.eval, Env.base_ofMachine_eq]; rw [hr]; simp, trivial⟩
    trivial trivial trivial

omit [Labels] in
/-- A part of an input, a block's region. -/
theorem ROk.sub {a : BitVec 64} {n o n' : Nat} (hok : InOk m0 a n N) (ho : o + n' ≤ n)
    (hpos : 0 < n') : ROk m0 0 (a + BitVec.ofNat 64 o, n') := by
  obtain ⟨⟨hm, hnw⟩, hap⟩ := hok
  unfold NoWrap at hnw
  unfold OffStack Apart at hap
  have e : (a + BitVec.ofNat 64 o).toNat = a.toNat + o := NativeRustcVm.toNat_add_ofNat (by omega)
  refine ⟨hpos, ⟨fun i hi ↦ ?_, ?_⟩, ?_, by omega⟩
  · rw [NativeRustcVm.addr_add_add]; exact hm _ (by omega)
  · unfold NoWrap; rw [e]; omega
  · unfold OffStack Apart; rw [e]; omega

omit [Labels] in
theorem ROk.whole {a : BitVec 64} {n : Nat} (hok : InOk m0 a n N) (hpos : 0 < n) :
    ROk m0 0 (a, n) := by
  have := ROk.sub (o := 0) (n' := n) hok (by omega) hpos
  rwa [add_zero'] at this

/-- An environment of the frame and one more region. -/
theorem wf1 (h : Pre L rows bl Fm SL m0) {m : MachineData} (hk : Kept m0.dmem m.dmem)
    {e : BitVec 64 × Nat} (he : ROk m0 0 e) : (Env.ofMachine m [(base m0 F, F + 0), e]).WF :=
  wfB h hk (.inl rfl) (fun e' he' ↦ by rw [List.mem_singleton.mp he']; exact he)
    (List.pairwise_singleton _ _)

/-- An environment of the frame alone. -/
theorem wf0 (h : Pre L rows bl Fm SL m0) {m : MachineData} (hk : Kept m0.dmem m.dmem) :
    (Env.ofMachine m [(base m0 F, F + 0)]).WF :=
  wfB h hk (.inl rfl) (fun _ he ↦ nomatch he) List.Pairwise.nil

end

/-! ## Descriptions -/

section
variable [Labels] {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64} {D : List (Sym × Nat)}
  {m : MachineData}

/-- **A call's result** added to a description. -/
theorem holds_ret (hH : Holds rs V D m) {r0 r1 : Nat} (h0 : m.regs.getXReg .X0 = V r0)
    (h1 : m.regs.getXReg .X1 = V r1) : Holds rs V ((.reg .X0, r0) :: (.reg .X1, r1) :: D) m := by
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · exact h0
  · exact h1
  · exact hH p hp

/-- An `E` element returned is two entries of the table. -/
theorem holds_ewRet (hH : Holds rs V D m) {r0 : Nat} {x : EW} (hx : ewRet m = x)
    (h0 : x.c0 = V r0) (h1 : x.c1 = V (r0 + 1)) :
    Holds rs V ((.reg .X0, r0) :: (.reg .X1, r0 + 1) :: D) m :=
  holds_ret hH (by rw [← h0, ← hx]; rfl) (by rw [← h1, ← hx]; rfl)

theorem Holds.cons {s : Sym} {i : Nat} (h : Holds rs V D m) (hs : tval rs m s = V i) :
    Holds rs V ((s, i) :: D) m := fun p hp ↦ by
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hs
  · exact h p hp

theorem Holds.sub {D' : List (Sym × Nat)} (h : Holds rs V D m) (hs : D'.all (D.contains ·) = true) :
    Holds rs V D' m :=
  h.mono fun p hp ↦ List.contains_iff_mem.mp (List.all_eq_true.mp hs p hp)

/-- A register's value in a description. -/
theorem Holds.regv (h : Holds rs V D m) {r : XReg} {i : Nat}
    (hp : D.contains (.reg r, i) = true) : m.regs.getXReg r = V i :=
  h _ (List.contains_iff_mem.mp hp)

/-- A location's value in a description. -/
theorem Holds.evc (h : Holds rs V D m) {s : Sym} {i : Nat} (hp : D.contains (s, i) = true) :
    s.eval (Env.ofMachine m rs) = (V i).toBitVec :=
  ev_of h (List.contains_iff_mem.mp hp)

end

/-! ## The frame's `FormBuf` -/

section
variable {m0 : MachineData}

/-- Frame bytes `[o, o + n)` the same through a block writing frame bytes off them. -/
theorem same_block [Labels] {m st : MachineData} {A : Nat} {rs : List (BitVec 64 × Nat)}
    {S : SState} (hSP : F ≤ m0.regs.SP.toNat)
    (hm : Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S st)
    (hwf : (Env.ofMachine m ((base m0 F, F + A) :: rs)).WF) {o n : Nat} (hon : o + n ≤ F)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ (w.off + w.n ≤ o ∨ o + n ≤ w.off)) :
    Same m.dmem st.dmem (base m0 F + BitVec.ofNat 64 o) n := by
  have hb := base_toNat (m0 := m0) (F := F) hSP
  have hlt := m0.regs.SP.toNat_lt
  refine Same.of_sameOutside (hm.sameOutside hwf) fun j hj hq ↦ ?_
  obtain ⟨w, hw', b, sz, hbr, h1, h2⟩ := hq
  obtain ⟨hr, hd⟩ := hw w hw'
  rw [hr] at hbr
  cases hbr
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)] at h1 h2
  rcases hd with hd | hd <;> omega

/-- Frame bytes `[o, o + n)` the same through a call writing its stack, frame bytes off them and
bytes apart from the frame. -/
theorem same_call {st m2 : MachineData} (hsp : st.regs.SP.toBitVec = base m0 F) {N' : Nat}
    (hle : F + N' ≤ m0.regs.SP.toNat) {X : BitVec 64 → Prop}
    (hX : ∀ q, X q → ¬InRange (base m0 F) F q) {lo n' : Nat}
    (hs : SameOutside st.dmem m2.dmem (fun q ↦ InRange (stackBelow st N') N' q ∨
      InRange (base m0 F + BitVec.ofNat 64 lo) n' q ∨ X q)) {o n : Nat} (hon : o + n ≤ F)
    (hlo : lo + n' ≤ F) (hd : o + n ≤ lo ∨ lo + n' ≤ o) :
    Same st.dmem m2.dmem (base m0 F + BitVec.ofNat 64 o) n := by
  have hb := base_toNat (m0 := m0) (F := F) (by omega)
  have hlt := m0.regs.SP.toNat_lt
  refine Same.of_sameOutside hs fun j hj hq ↦ ?_
  rcases hq with hq | hq | hq
  · exact Bus.slot_not_callee (m0 := m0) (m := st) hle hsp (by omega) hq
  · rw [NativeRustcVm.addr_add_add] at hq
    exact Gkr.not_loc (m0 := m0) (F := F) (by omega) (by omega) (by omega) (by omega) hq
  · refine hX _ hq ?_
    rw [NativeRustcVm.addr_add_add]
    exact NativeRustcVm.inRange_add (by omega) (by omega)

end

end

end NativeRustcVmArm.Bus.AccumulateSide
