module

public import NativeRustcVmArm.Tables.TableTerms.Facts
public import NativeRustcVmArm.Tables.TableTerms.Run

/-!
# `table_terms`: running a block from a state of the frame

The environments of the blocks (`E0`: the frame; `E1`: the frame and one region), their start
states' matches (`match0`, `match1`) and well-formedness (`wf0`, `wf1`), the loads there (`ld0`,
`ld1`), the frame after a block (`fr_block`), the goal (`Goal`, `R`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout
open NativeRustcVm (wordOf ewsOf)

@[expose] public section

/-- The frame alone. -/
abbrev E0 (m0 m : MachineData) : Env := Env.ofMachine m [(base m0 288, 288)]

/-- The frame and the `n` bytes at `b`. -/
abbrev E1 (m0 m : MachineData) (b : BitVec 64) (n : Nat) : Env :=
  Env.ofMachine m [(base m0 288, 288), (b, n)]

/-- The model's run. -/
abbrev R (heights : Array Nat) (forms : Array (Array FormW)) (m0 : MachineData) (s : TState) :
    Option ((EW × Array (Array EW × Array EW)) × TState) :=
  (tableTerms (cpw m0) (fpw m0) (ptw m0) (tableRows heights forms (wts m0))).run s

/-- What `table_terms` reaches. -/
abbrev Goal [Labels] (a : DecArea) (s : TState) (heights : Array Nat) (forms : Array (Array FormW))
    (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ TableTermsPost a s heights forms m0 st.data

end

public section

variable [Labels] {m0 m : MachineData}

theorem match0 (hS : StackOk m0 N) (hsp : m.regs.SP.toBitVec = base m0 288) :
    Match (E0 m0 m) sF m :=
  Bus.match_frame hS (by decide) rfl hsp

omit [Labels] in
theorem wf0 (hS : StackOk m0 N) (hk : Kept m0.dmem m.dmem) : (E0 m0 m).WF :=
  Bus.wf_frame hS (by decide) hk

/-- **The start state with a second region**, `x` at its byte `o`. -/
theorem match1 (hS : StackOk m0 N) (hsp : m.regs.SP.toBitVec = base m0 288) {b : BitVec 64}
    {n : Nat} {x : Sym} {o : Int} (hx : x.eval (E1 m0 m b n) = b + BitVec.ofInt 64 o) :
    Match (E1 m0 m b n) (init [(288, true), (n, false)] (.ptr 0 0) [] [] [] [(x, (1, o))]) m :=
  match_ofMachine (sregions := [(288, true), (n, false)]) (regions := [(base m0 288, 288), (b, n)])
    ⟨rfl, fun _ ↦ Bus.base_aligned hS (by decide) rfl, rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hsp]; simp)
    trivial trivial trivial ⟨hx, trivial⟩

omit [Labels] in
theorem wf1 (hS : StackOk m0 N) (hk : Kept m0.dmem m.dmem) {b : BitVec 64} {n : Nat}
    (hr : Readable m0 b n) (ho : OffStack m0 b n N) : (E1 m0 m b n).WF :=
  Bus.wf_frame2 hS (by decide) hk hr ho

/-- A word of the frame the block's environment loads. -/
theorem ld0 (rs : List (BitVec 64 × Nat)) (o : Nat) :
    (Sym.load 0 o 8).eval (Env.ofMachine m ((base m0 288, 288) :: rs)) = fw m0 m o := by
  show Env.load _ 0 o 8 = _
  rw [load_eq_wordOf]
  rfl

/-- A word of region 1 the block's environment loads. -/
theorem ld1 (b : BitVec 64) (n o : Nat) :
    (Sym.load 1 o 8).eval (E1 m0 m b n) = (wordOf m.dmem (b + BitVec.ofNat 64 o)).toBitVec := by
  show Env.load _ 1 o 8 = _
  rw [load_eq_wordOf]
  rfl

/-- A register after a block. -/
theorem rv {env : Env} {S : SState} {m' : MachineData} (hm : Match env S m') {r : XReg} {v : Sym}
    (h : S.reg r = some v) : rg m' r = v.eval env :=
  hm.regs r v h

/-- A register a block kept. -/
theorem rk {rs : List (BitVec 64 × Nat)} {S : SState} {m' : MachineData}
    (hm : Match (Env.ofMachine m rs) S m') {r : XReg} (h : S.reg r = some (.reg r)) :
    m'.regs.getXReg r = m.regs.getXReg r :=
  UInt64.toBitVec_inj.mp (hm.regs r _ h)

/-- **The frame after a block** whose writes `wok` allows. -/
theorem fr_block {rs : List (BitVec 64 × Nat)} {S S' : SState} {m' : MachineData}
    {szs : List Nat} {outR : List Bool}
    (h : Fr m0 288 N slots [] (outs m0) m) (hN : N ≤ m0.regs.SP.toNat)
    (hm : Match (Env.ofMachine m ((base m0 288, 288) :: rs)) S m)
    (hm' : Match (Env.ofMachine m ((base m0 288, 288) :: rs)) S' m')
    (hwf : (Env.ofMachine m ((base m0 288, 288) :: rs)).WF) (hsp : S'.sp = S.sp)
    (hsz : ((base m0 288, 288) :: rs).map Prod.snd = szs)
    (hout : ∀ r b sz, outR.getD r false = true → ((base m0 288, 288) :: rs)[r]? = some (b, sz) →
      ∀ i < sz, outs m0 (b + BitVec.ofNat 64 i))
    (hW : wok S' szs outR = true) : Fr m0 288 N slots [] (outs m0) m' :=
  Fr.ofBlockW h hm hm' hwf rfl hsp (fun _ h ↦ nomatch h) rfl (by rw [N_eq]; omega) hN slots_le
    (writeOk_of hsz hout hW)

/-- **The frame after a block without writes.** -/
theorem fr_block0 {rs : List (BitVec 64 × Nat)} {S S' : SState} {m' : MachineData}
    (h : Fr m0 288 N slots [] (outs m0) m)
    (hm : Match (Env.ofMachine m ((base m0 288, 288) :: rs)) S m)
    (hm' : Match (Env.ofMachine m ((base m0 288, 288) :: rs)) S' m')
    (hwf : (Env.ofMachine m ((base m0 288, 288) :: rs)).WF) (hmem : S'.mem = [])
    (hsp : S'.sp = S.sp) : Fr m0 288 N slots [] (outs m0) m' :=
  Fr.ofBlock h hm hm' hwf rfl hmem hsp (fun _ h ↦ nomatch h)

/-- A block without writes keeps memory. -/
theorem dmem_block {rs : List (BitVec 64 × Nat)} {S' : SState} {m' : MachineData}
    (hm' : Match (Env.ofMachine m rs) S' m') (hwf : (Env.ofMachine m rs).WF) (hmem : S'.mem = []) :
    m'.dmem = m.dmem :=
  hm'.dmem_eq hwf hmem

/-- **A word after a block**: its symbolic load's value. -/
theorem wordAt_of_load {env : Env} {S : SState} {m' : MachineData} (hm : Match env S m')
    (hwf : env.WF) {r o : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    (hle : o + 8 ≤ sz) {v : Sym} (hv : loadSym S.mem r o 8 = v) :
    NativeRustcVm.WordAt m'.dmem (b + BitVec.ofNat 64 o) (UInt64.ofBitVec (v.eval env)) := by
  have hmp : NativeRustcVm.Mapped m'.dmem (b + BitVec.ofNat 64 o) 8 := fun i hi ↦ by
    rw [NativeRustcVm.addr_add_add]
    exact hm.kept hwf _ (hwf.mapped r b sz hb _ (by omega))
  have := NativeRustcVm.wordAt_of_mapped hmp
  rwa [show NativeRustcVm.wordOf m'.dmem (b + BitVec.ofNat 64 o) = UInt64.ofBitVec (v.eval env) from
    UInt64.toBitVec_inj.mp (by rw [match_wordOf hm hwf hb hle, hv])] at this

omit [Labels] in
/-- No region but the frame is written. -/
theorem hout_none {rs : List (BitVec 64 × Nat)} {L : List Bool} (hL : L.all (· == false) = true) :
    ∀ r b sz, L.getD r false = true → ((base m0 288, 288) :: rs)[r]? = some (b, sz) →
      ∀ i < sz, outs m0 (b + BitVec.ofNat 64 i) := by
  intro r b sz hr
  exfalso
  rw [List.getD_eq_getElem?_getD] at hr
  cases hv : L[r]? with
  | none => rw [hv] at hr; cases hr
  | some v =>
    rw [hv] at hr
    have := List.all_eq_true.mp hL v (List.mem_of_getElem? hv)
    simp only [Option.getD_some] at hr
    rw [hr] at this
    cases this

omit [Labels] in
/-- Region 1 of two is outputs. -/
theorem hout_one {b : BitVec 64} {n : Nat} (hb : ∀ i < n, outs m0 (b + BitVec.ofNat 64 i)) :
    ∀ r b' sz, [false, true].getD r false = true →
      [(base m0 288, 288), (b, n)][r]? = some (b', sz) →
      ∀ i < sz, outs m0 (b' + BitVec.ofNat 64 i) := by
  intro r b' sz hr hb'
  rcases r with _ | _ | r
  · cases hr
  · cases hb'; exact hb
  · simp at hb'

omit [Labels] in
/-- Region 1 of three is outputs. -/
theorem hout_mid {b c : BitVec 64} {n p : Nat} (hb : ∀ i < n, outs m0 (b + BitVec.ofNat 64 i)) :
    ∀ r b' sz, [false, true, false].getD r false = true →
      [(base m0 288, 288), (b, n), (c, p)][r]? = some (b', sz) →
      ∀ i < sz, outs m0 (b' + BitVec.ofNat 64 i) := by
  intro r b' sz hr hb'
  rcases r with _ | _ | _ | r
  · cases hr
  · cases hb'; exact hb
  · cases hr
  · simp at hb'

end

end NativeRustcVmArm.Tables.TableTerms
