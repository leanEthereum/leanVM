module

public import NativeRustcVmArm.Bus.AccumulateSide.Entry

/-!
# `accumulate_side`: a step of the body

The body's state (`St`): the frame, a description of the values it keeps (`Holds` over the frame
alone, `rs0`). A block whose writes are frame bytes below the slots (`wrOk`) and whose regions
are the frame (maybe with the stack arguments) and others: `St.run`. A call writing its stack, the
frame's `n` bytes from `lo` and the forms, the description's locations kept (`callOk`):
`St.call`.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

/-- A block's writes: frame bytes below the slots. -/
def wrOk (S : SState) : Bool := S.mem.all fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 12000)

/-- A location a call writing the frame's `n` bytes from `lo` keeps. -/
def callOk (lo n : Nat) : Sym → Bool
  | .reg r => calleeSaved r
  | .load 0 o 8 => decide (o + 8 ≤ lo ∨ lo + n ≤ o) && decide (o + 8 ≤ F)
  | _ => false

/-- **The body's state**: the frame, the description `D` of the table `V`. -/
structure St [Labels] (m0 : MachineData) (V : Nat → UInt64) (D : List (Sym × Nat))
    (m : MachineData) : Prop where
  fr : Fr m0 F N slots keep (outs m0) m
  hd : Holds (rs0 m0) V D m

end

public section

theorem slots_ge : ∀ p ∈ slots, 12000 ≤ p.1 := by decide

/-- A description's other table. -/
theorem Holds.congrV [Labels] {rs : List (BitVec 64 × Nat)} {V V' : Nat → UInt64}
    {D : List (Sym × Nat)} {m : MachineData} (h : Holds rs V D m)
    (hV : ∀ p ∈ D, V p.2 = V' p.2) : Holds rs V' D m := fun p hp ↦ (h p hp).trans (hV p hp)

/-- **A description kept** where its registers and its words of region `0` are. -/
theorem Holds.keep [Labels] {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {m m2 : MachineData} (h : Holds rs V D m)
    (hD : D.all (fun p ↦ loc0 p.1) = true)
    (hr : ∀ p ∈ D, ∀ r, p.1 = .reg r → m2.regs.getXReg r = m.regs.getXReg r)
    (hw : ∀ p ∈ D, ∀ o, p.1 = .load 0 o 8 → ∀ j < 8,
      m2.dmem.get? ((((rs[0]?).map (·.1)).getD 0) + BitVec.ofNat 64 (o + j)) =
        m.dmem.get? ((((rs[0]?).map (·.1)).getD 0) + BitVec.ofNat 64 (o + j))) :
    Holds rs V D m2 := by
  intro p hp
  rw [← h p hp]
  have hl : loc0 p.1 = true := List.all_eq_true.mp hD p hp
  unfold tval
  congr 1
  match hs : p.1, hl with
  | .reg r, _ =>
    show (m2.regs.getXReg r).toBitVec = (m.regs.getXReg r).toBitVec
    rw [hr p hp r hs]
  | .load 0 o 8, _ =>
    simp only [Sym.eval, Env.load, Env.base_ofMachine_eq]
    congr 2
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    show (m2.dmem.get? _).getD 0 = (m.dmem.get? _).getD 0
    rw [hw p hp o hs j hj]

theorem loc0_of_callOk {lo n : Nat} (s : Sym) (h : callOk lo n s = true) : loc0 s = true := by
  unfold callOk at h
  split at h
  · rfl
  · rfl
  · cases h

section
variable [Labels]

/-- One location's value. -/
theorem holds_one {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64} {m : MachineData} {s : Sym}
    {i : Nat} (h : tval rs m s = V i) : Holds rs V [(s, i)] m := fun p hp ↦ by
  simp only [List.mem_singleton] at hp
  subst hp
  exact h

theorem holds_nil (rs : List (BitVec 64 × Nat)) (V : Nat → UInt64) (m : MachineData) :
    Holds rs V [] m := fun _ h ↦ by cases h

/-- A register's value after a block, from its symbolic value. -/
theorem tval_reg_of {rs rs' : List (BitVec 64 × Nat)} {m st : MachineData} {S : SState}
    (hm : Match (Env.ofMachine m rs) S st) {r : XReg} {s : Sym} (h : S.reg r = some s) :
    tval rs' st (.reg r) = UInt64.ofBitVec (s.eval (Env.ofMachine m rs)) :=
  congrArg UInt64.ofBitVec (hm.regs r s h)

/-- A register's value after a block, a location of a description. -/
theorem reg_of {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64} {D : List (Sym × Nat)}
    {m st : MachineData} {S : SState} (hH : Holds rs V D m) (hm : Match (Env.ofMachine m rs) S st)
    {r : XReg} {s : Sym} {i : Nat} (h : S.reg r = some s) (hp : (s, i) ∈ D) :
    st.regs.getXReg r = V i :=
  (tval_reg_of (rs' := rs) hm h).trans (hH _ hp)

/-- `eor`'s value. -/
theorem ofBitVec_eor (env : Env) (a b : Sym) :
    UInt64.ofBitVec ((Sym.bin .eor .W64 a b).eval env) =
      UInt64.ofBitVec (a.eval env) ^^^ UInt64.ofBitVec (b.eval env) := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
  rfl

/-- A register's `eor` of two locations of a description, after a block. -/
theorem reg_eor {rs : List (BitVec 64 × Nat)} {V : Nat → UInt64} {D : List (Sym × Nat)}
    {m st : MachineData} {S : SState} (hH : Holds rs V D m) (hm : Match (Env.ofMachine m rs) S st)
    {r : XReg} {a b : Sym} {i j : Nat} (h : S.reg r = some (.bin .eor .W64 a b))
    (ha : (a, i) ∈ D) (hb : (b, j) ∈ D) : st.regs.getXReg r = V i ^^^ V j := by
  show tval rs st (.reg r) = _
  rw [tval_reg_of hm h, ofBitVec_eor]
  exact congrArg₂ _ (hH _ ha) (hH _ hb)

/-- A word a block wrote, a location of region `0`. -/
theorem tval_write {rs rs' : List (BitVec 64 × Nat)} {m st : MachineData} {S : SState}
    (hm : Match (Env.ofMachine m rs) S st) {b : BitVec 64} {sz sz' o : Nat}
    (h0 : rs[0]? = some (b, sz)) (h0' : rs'[0]? = some (b, sz')) (hle : o + 8 ≤ sz) {v : Sym}
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (v, i)) :
    tval rs' st (.load 0 o 8) = UInt64.ofBitVec (v.eval (Env.ofMachine m rs)) := by
  have hW := Bus.wordAt_write hm h0 hle hw
  unfold tval
  rw [Sym.eval, load_word (v := UInt64.ofBitVec (v.eval (Env.ofMachine m rs)))]
  rw [Env.ofMachine_mem0, Env.base_ofMachine st rs' _ h0']
  exact hW

/-- A word of region `r`. -/
theorem tval_load {rs : List (BitVec 64 × Nat)} {m : MachineData} {r o n : Nat} {b : BitVec 64}
    (hb : rs[r]? = some (b, n)) {w : UInt64}
    (hw : NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) w) : tval rs m (.load r o 8) = w := by
  unfold tval
  rw [Sym.eval, load_word (v := w)]
  rw [Env.ofMachine_mem0, Env.base_ofMachine m rs _ hb]
  exact hw

end

variable [Host] {m0 : MachineData}

/-- The description of a state of the body over the regions of a block. -/
theorem St.lift {V : Nat → UInt64} {D : List (Sym × Nat)} {m : MachineData} (hst : St m0 V D m)
    (hD : D.all (fun p ↦ loc0 p.1) = true) (A : Nat) (rs : List (BitVec 64 × Nat)) :
    Holds ((base m0 F, F + A) :: rs) V D m :=
  Holds.reg0 hst.hd hD rfl

/-- **A block of the body**: region `0` the frame and `A` bytes above it, the other regions
`rs`; the locations it tracks (`D'`) and the ones it computes (`E`). -/
theorem St.run (hS : StackOk m0 N) {A : Nat} {rs : List (BitVec 64 × Nat)} {sz : List Nat}
    (hsz : ((base m0 F, F + A) :: rs).map Prod.snd = sz) {S S' : SState} {ds : List Directive}
    {i : Nat} {x : Exit} {R : MachineState → Prop} {m : MachineData} {V : Nat → UInt64}
    {D D' E : List (Sym × Nat)} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds S = some (S', x))
    (hfr : Fr m0 F N slots keep (outs m0) m) (hH : Holds ((base m0 F, F + A) :: rs) V D m)
    (hwf : (Env.ofMachine m ((base m0 F, F + A) :: rs)).WF)
    (hm : Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S m)
    (hsp : S'.sp = .ptr 0 0) (hw : wrOk S' = true)
    (hD' : (D' ++ E).all (fun p ↦ loc0 p.1) = true) (htr : trackOk sz S' D D' = true)
    (hE : ∀ st : MachineData, Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      Holds ((base m0 F, F + A) :: rs) V E st)
    (cont : ∀ st, Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st.data →
      PcOk (Env.ofMachine m ((base m0 F, F + A) :: rs)) x (Host.addrOf (i + ds.length)) st →
      St m0 V (D' ++ E) st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ :=
  exec_then hk hrun hwf hm fun st hm' hpc ↦ cont st hm' hpc
    ⟨Fr.blockA hfr hS.2.1 (by decide) hm' hwf hsp (fun w hw' ↦ by
        have := List.all_eq_true.mp hw w hw'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
        exact ⟨this.1, by have hF : F = 12096 := rfl; omega,
          fun p hp ↦ .inl (by have := slots_ge p hp; omega)⟩),
      Holds.reg0 (Holds.append (Holds.after hsz hH hm' htr) (hE _ hm')) hD' rfl⟩

omit [Host] in
/-- The forms are apart from the frame. -/
theorem outs_frame [Labels] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
    {Fm : Array (Array FormW)} {SL : BusLayoutW} (h : Pre L rows bl Fm SL m0) :
    ∀ q, outs m0 q → ¬InRange (base m0 F) F q := by
  intro q hq hq'
  change InRange m0.regs.X1.toBitVec formsBytes q at hq
  have hA := apart_frame h.stack.2.1 (show F ≤ N by decide) h.formsOk.2
  rw [Sym.inRange_iff h.formsOk.1.2] at hq
  rw [Sym.inRange_iff (Bus.frame_mapped h.stack (show F ≤ N by decide)).2] at hq'
  unfold Apart at hA
  omega

/-- **A call from the body**: its stack, the frame's `n` bytes from `lo` and the forms written,
the description's locations kept. -/
theorem St.call {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
    {Fm : Array (Array FormW)} {SL : BusLayoutW} (h : Pre L rows bl Fm SL m0) {l : Label}
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop} {N' lo n : Nat}
    {st : MachineState} {next : Int64} {R : MachineState → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} (hst : St m0 V D st.data) (hle : F + N' ≤ N) (hlo : lo + n ≤ 12000)
    (hD : D.all (fun p ↦ callOk lo n p.1) = true) (hspec : Spec (Labels.label l) P Q)
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (hQ : ∀ m', Q st.data m' → SameOutside st.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow st.data N') N' q ∨ InRange (base m0 F + BitVec.ofNat 64 lo) n q ∨
        outs m0 q) ∧ Saved st.data m')
    (cont : ∀ m2, St m0 V D m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hN := h.stack.2.1
  have hSP := m0.regs.SP.toNat_lt
  have hF0 : F = 12096 := rfl
  refine Fr.leafIn hst.fr hN hle (by omega) keep_callee
    (fun p hp ↦ ⟨slots_le p hp, .inr (by have := slots_ge p hp; omega)⟩) (outs_frame h) hspec hpc
    hP hQ fun m2 hfr2 hq hcs ↦ cont m2 ⟨hfr2, ?_⟩ hq hcs
  have hs := (hQ m2 hq).1
  refine Holds.keep hst.hd (List.all_eq_true.mpr fun p hp ↦ ?_) (fun p hp r hr ↦ ?_)
    fun p hp o ho j hj ↦ ?_
  · exact loc0_of_callOk _ (List.all_eq_true.mp hD p hp)
  · have hc : callOk lo n p.1 = true := List.all_eq_true.mp hD p hp
    rw [hr] at hc
    exact hcs r hc
  · have hc : callOk lo n p.1 = true := List.all_eq_true.mp hD p hp
    rw [ho] at hc
    simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hc1, hc2⟩ := hc
    show m2.dmem.get? (base m0 F + BitVec.ofNat 64 (o + j)) =
      st.data.dmem.get? (base m0 F + BitVec.ofNat 64 (o + j))
    have hF := base_toNat (m0 := m0) (F := F) (by omega)
    refine hs _ fun hq' ↦ ?_
    rcases hq' with hq' | hq' | hq'
    · have := Bus.slot_not_callee (m0 := m0) (m := st.data) (F := F) (N' := N') (p := o) (i := j)
        (by omega) hst.fr.sp (by omega)
      rw [NativeRustcVm.addr_add_add] at this
      exact this hq'
    · exact Gkr.not_loc (m0 := m0) (F := F) (by omega) (by omega) (by omega) (by omega) hq'
    · exact outs_frame h _ hq' (NativeRustcVm.inRange_add (by omega) (by omega))

/-- **A block of the body ending in a call.** -/
theorem St.runCall {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
    {Fm : Array (Array FormW)} {SL : BusLayoutW} (h : Pre L rows bl Fm SL m0) {A : Nat}
    {rs : List (BitVec 64 × Nat)} {sz : List Nat}
    (hsz : ((base m0 F, F + A) :: rs).map Prod.snd = sz) {S S' : SState} {ds : List Directive}
    {i : Nat} {l : Label} {R : MachineState → Prop} {m : MachineData} {V : Nat → UInt64}
    {D D' E : List (Sym × Nat)} {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    {N' lo n : Nat} (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds S = some (S', .call l))
    (hfr : Fr m0 F N slots keep (outs m0) m) (hH : Holds ((base m0 F, F + A) :: rs) V D m)
    (hwf : (Env.ofMachine m ((base m0 F, F + A) :: rs)).WF)
    (hm : Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S m)
    (hsp : S'.sp = .ptr 0 0) (hw : wrOk S' = true)
    (hD' : (D' ++ E).all (fun p ↦ loc0 p.1) = true) (htr : trackOk sz S' D D' = true)
    (hE : ∀ st : MachineData, Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      Holds ((base m0 F, F + A) :: rs) V E st)
    (hle : F + N' ≤ N) (hlo : lo + n ≤ 12000)
    (hok : (D' ++ E).all (fun p ↦ callOk lo n p.1) = true) (hspec : Spec (Labels.label l) P Q)
    (hP : ∀ st : MachineData, Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      St m0 V (D' ++ E) st → P st)
    (hQ : ∀ st m' : MachineData, Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      Q st m' → SameOutside st.dmem m'.dmem (fun q ↦ InRange (stackBelow st N') N' q ∨
        InRange (base m0 F + BitVec.ofNat 64 lo) n q ∨ outs m0 q) ∧ Saved st m')
    (cont : ∀ st m2 : MachineData, Match (Env.ofMachine m ((base m0 F, F + A) :: rs)) S' st →
      St m0 V (D' ++ E) st → St m0 V (D' ++ E) m2 → Q st m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ :=
  St.run h.stack hsz hk hrun hfr hH hwf hm hsp hw hD' htr hE fun _ hm' hpc hst ↦
    St.call h hst hle hlo hok hspec hpc (hP _ hm' hst) (fun m' hq ↦ hQ _ m' hm' hq)
      fun m2 hst2 hq hcs ↦ cont _ m2 hm' hst hst2 hq hcs

end

end NativeRustcVmArm.Bus.AccumulateSide
