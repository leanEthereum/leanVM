module

public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Entry0

/-!
# `keccak_open`: the return

`b95` stores the tag in X8 at the result and restores the entry's registers (`tail_run`). `None`
from the plain sumcheck: `b1` branches there with tag `0` (`none_exit`). After the fold, `b93`
writes the value into the result and jumps there with tag `1` (`some_exit`). The model's run of
`keccakOpen` after the plain sumcheck (`open_none`, `open_some`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm (Region InAny)
open NativeRustcVm.Transcript (DecArea tstateBytes TStateAt)

@[expose] public section

/-- **What `keccak_open` must reach**: the return address, its postcondition. -/
def Goal [Host] (a : DecArea) (s : TState) (c : KeccakClaimW) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ KeccakOpenPost a s c m0 st.data

end

public section

/-! ## The model -/

theorem open_none {L f n : Nat} {c : KeccakClaimW} {v : EW} {s : TState}
    (h : (sumcheckPlain v 3 qkeccakSlotBits).run s = none) :
    (NativeVm.Model.keccakOpen L c f n v).run s = none := by
  rw [NativeVm.Model.keccakOpen, StateT.run_bind, h]
  rfl

theorem open_some {L f n : Nat} {c : KeccakClaimW} {v v' : EW} {s s' : TState} {sl : Array EW}
    (h : (sumcheckPlain v 3 qkeccakSlotBits).run s = some ((sl, v'), s')) :
    (NativeVm.Model.keccakOpen L c f n v).run s = some ((sl, (NativeRustcVm.KeccakGkr.openRows sl
      (NativeVm.Model.keccakSlotWeights L c f n) sl.size).getD 0 #[], v'), s') := by
  rw [← NativeRustcVm.KeccakGkr.keccakOpen_rows, NativeVm.Model.keccakOpen, StateT.run_bind, h]
  rfl

/-! ## Blocks -/

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- A block's label is at its index. -/
theorem label_at (hp : Placed code k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j)
    {l : Label} (h0 : b[0]? = some (.label l)) : Labels.label l = Host.addrOf (k + j) := by
  refine hp.label ?_
  obtain ⟨t, ht⟩ := hb
  have : (code.drop j)[0]? = some (.label l) := by
    rw [← ht, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h0).1]
    exact h0
  rwa [List.getElem?_drop, Nat.add_zero] at this

omit [Host] in
theorem pc_true [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond c l) next st) (hc : c.eval env = true) : st.pc = Labels.label l := by
  simp only [PcOk, hc, ↓reduceIte] at h
  exact h

omit [Host] in
theorem pc_false [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond c l) next st) (hc : c.eval env = false) : st.pc = next := by
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at h
  exact h

/-- **The return** from `b95` with the tag in X8 and the result's address in X19: the tag
stored, the entry's registers restored. -/
theorem tail_run (hp : Placed code k) (h : KeccakOpenPre a s c m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b95Offset)) (hb : Body m0 st.data)
    (h19 : st.data.regs.X19 = m0.regs.X0) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ Saved m0 st'.data ∧
      Writes m0 st'.data keccakOpenStack (wsOf m0) ∧
      NativeRustcVm.WordAt st'.data.dmem (oA m0) st.data.regs.X8 ∧
      SameOutside st.data.dmem st'.data.dmem (InRange (oA m0) 8) ∧
      Kept st.data.dmem st'.data.dmem) st := by
  have hS := h.1
  have hA := pre_areas h
  have h2224 : 2224 ≤ keccakOpenStack := by rw [stack_eq]; decide
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS h2224
  have hro := Areas.ok hA (.inl (mem_out (m0 := m0)))
  have hwfR : (Env.ofMachine st.data [(oA m0, 24)]).WF :=
    wf_one (m := st.data) (Mapped.kept' hro.1 hb.kept) hro.2
  have hmR : Match (Env.ofMachine st.data [(oA m0, 24)]) resS st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show st.data.regs.X19.toBitVec = oA m0 + BitVec.ofInt 64 0
        rw [h19, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
      trivial trivial trivial
  have i95 := b95_in_code.trans hp.1 (by simp [b95])
  refine exec_at (List.IsInfixAt.trans (⟨b95.drop 2, by
    rw [List.drop_zero, List.take_append_drop]⟩ : (b95.take 2).IsInfixAt b95 0) i95
    (by simp [b95])) run_b95a hwfR hpc hmR fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, show (b95.take 2).length = 2 from rfl] at hpc1
  have hb1 : Body m0 s1.data :=
    hb.write hS h2224 slots_le' (wsOff h) hmR hm1 hwfR rfl all_slots (by decide) fun p hw ↦
      ⟨_, mem_out, Sumcheck.Written.inRange (r := 0) (b := oA m0) (sz := 24) rfl hro.2
        (by decide +kernel) hw⟩
  have htag : NativeRustcVm.WordAt s1.data.dmem (oA m0) st.data.regs.X8 := by
    have := Sumcheck.Match.wordAt_write hm1 (r := 0) (o := 0) (v := .reg .X8) rfl (by decide)
      (by decide +kernel)
    rw [NativeRustcVm.addr_add_zero] at this
    exact this
  have hso1 : SameOutside st.data.dmem s1.data.dmem (InRange (oA m0) 8) :=
    fun p hp ↦ hm1.sameOutside hwfR p fun hw ↦ hp (KeccakGkr.Written.inRange_le (r := 0)
      (b := oA m0) (sz := 24) rfl hro.2 (L := 8) (by decide) (by decide +kernel) hw)
  -- the epilogue
  have hwfE := wf_one (m := s1.data) (Mapped.kept' hmap hb1.kept) hnw
  have hmE : Match (Env.ofMachine s1.data [(fbA m0, 2224)]) epiS s1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h2224 rfl, trivial⟩
      (by rw [hb1.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (List.IsInfixAt.trans (⟨[], List.append_nil _⟩ :
    (b95.drop 2).IsInfixAt b95 2) i95 (by simp [b95])) run_b95b hwfE hpc1 hmE
    fun s2 hm2 hpc2 ↦ .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb1.saved hm2 hwfE
    (List.mem_map.mpr ⟨(2136, .X30), by simp [slots], rfl⟩) (by decide +kernel) rfl
  simp only [PcOk] at hpc2
  refine ⟨by rw [hpc2]; simp only [retOf, hx30], hsaved,
    fun p hp ↦ by rw [hdm]; exact hb1.same p hp, by rw [hdm]; exact htag,
    by rw [hdm]; exact hso1, ?_⟩
  rw [hdm]
  exact hm1.kept hwfR

/-- **`None` from the plain sumcheck**: `b1` branches to the return with tag `0`. -/
theorem none_exit (hp : Placed code k) (h : KeccakOpenPre a s c m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b1Offset)) (hsc : Sc a s m0 st.data) (hn : scRun s m0 = none) :
    Eventually (step1 Host.exe) (Goal a s c m0) st := by
  obtain ⟨hwf, hm⟩ := argS_match h hsc.body
  refine exec_at (b1_in_code.trans hp.1 (by simp [b1])) run_b1 hwf hpc hm fun s1 hm1 hpc1 ↦ ?_
  have htag : NativeRustcVm.WordAt st.data.dmem (fbA m0 + BitVec.ofNat 64 56) 0 := by
    have := hsc.out.1
    rw [hn] at this
    exact this
  have hl := Sumcheck.load_word (env := Env.ofMachine st.data [(fbA m0, 2256)]) (r := 0)
    (off := 56) htag
  have hpc1' := pc_true hpc1 (by
    show CmpOp.apply .eq .W64 ((Env.ofMachine st.data [(fbA m0, 2256)]).load 0 56 8) _ = true
    rw [hl]
    rfl)
  rw [label_at hp b95_in_code rfl] at hpc1'
  have hb1 : Body m0 s1.data := hsc.body.of_block hm hm1 hwf rfl all_slots (by decide)
  have h8 : s1.data.regs.X8 = 0 := UInt64.toBitVec_inj.mp ((hm1.regs .X8 _ rfl).trans hl)
  have h19 : s1.data.regs.X19 = m0.regs.X0 :=
    (regEq (r := .X19) (r' := .X19) hm1 rfl).trans hsc.x19
  refine (tail_run hp h hpc1' hb1 h19).mono fun st' ⟨hpc', hsv, hwr, htag', _, _⟩ ↦ ?_
  have hr : (NativeVm.Model.keccakOpen m0.regs.X2.toNat c m0.regs.X6.toNat m0.regs.X7.toNat
      (openValue m0)).run s = none := open_none hn
  refine ⟨hpc', ?_, fun sl ws v s' e ↦ ?_, hwr, hsv⟩
  · rw [hr]
    rw [h8] at htag'
    exact htag'
  · rw [hr] at e
    cases e

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
