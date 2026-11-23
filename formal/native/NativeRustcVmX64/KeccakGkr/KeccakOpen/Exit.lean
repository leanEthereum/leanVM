module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Step
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExecE

/-!
# `keccak_open`: the return boundary

The output tag is written before restoring the saved registers and returning through the
entry stack's return address. Only the tag's eight bytes change during this epilogue.
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr DecArea tstateBytes TStateAt Touch)

@[expose] public section

def Goal [Host] (a : DecArea) (s : TState) (c : KeccakClaimW) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ KeccakOpenPost a s c m0 st.data

end

public section

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

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem wf_out (h : PreOk a s c m0) {d : MachineData} (hk : Kept m0.dmem d.dmem) :
    (frameEnv m0 d 2208 [(oA m0, 24)] (fun _ ↦ 0) 0).WF := by
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.o; have := hn.so
  have hfb := fbA_toNat h
  have ho := Areas.ok h.areas (List.mem_append_left _ (List.mem_cons_self (a :=
    (⟨oA m0, 24⟩ : NativeRustcVm.Region))))
  refine frame_wf ⟨Mapped.keeps (frame_mapped h.st (by rw [stack_eq]; decide)) hk,
    frame_noWrap h.st (by rw [stack_eq]; decide)⟩ (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr ?_)
  · rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Mapped.keeps ho.1 hk, ho.2⟩
  · show (fbA m0).toNat + (2208 + 8) ≤ (oA m0).toNat ∨
      (oA m0).toNat + 24 ≤ (fbA m0).toNat
    rw [hfb]
    omega

/-- The output tag, restored registers, return address and exact memory frame. -/
theorem tail_run (hp : Placed code k) (h : PreOk a s c m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b95Offset)) (hf : Frame m0 2208 slots 8 st.data)
    (hs : NativeRustcVm.SameOutside m0.dmem st.data.dmem (Out m0))
    (hbx : reg st.data .rbx = oA m0) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ Saved m0 st'.data ∧
      Writes m0 st'.data keccakOpenStack (wsOf m0) ∧
      NativeRustcVm.WordAt st'.data.dmem (oA m0) (UInt64.ofBitVec (reg st.data .rax)) ∧
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange (oA m0) 8) ∧
      Kept st.data.dmem st'.data.dmem) st := by
  have hwf := wf_out h hf.kept
  have hm : Match (frameEnv m0 st.data 2208 [(oA m0, 24)] (fun _ ↦ 0) 0) resS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, by
      show reg st.data .rbx = oA m0 + BitVec.ofInt 64 0
      rw [hbx, ofInt0, BitVec.add_zero], trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b95_in_code (by simp [b95]) hp) x95 hwf nofun hpc hm
    fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hsv, hrsp⟩ := hf.epilogue hwf hm' f95.2.1
  have hso : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (NativeRustcVm.InRange (oA m0) 8) := by
    have ht := sameOutside_touch hwf hm' (r := 1) (b := oA m0) (N := 24)
      (lo := 0) (hi := 8) rfl (by decide) (by
        intro w hw
        rw [f95.2.2] at hw
        simp only [List.mem_singleton] at hw
        subst hw
        exact ⟨rfl, by decide⟩)
    intro q hq
    exact ht q fun ⟨j, hj, hj', he⟩ ↦ hq (by
      subst he
      exact NativeRustcVm.Transcript.inRange_off_self hj'.2 (by have := (nums h).o; omega))
  have htag : NativeRustcVm.WordAt st'.data.dmem (oA m0)
      (UInt64.ofBitVec (reg st.data .rax)) := by
    have ht := wordAt_write hm' (r := 1) (o := 0) (v := .reg .rax) rfl (by decide)
      (by rw [f95.2.2]; decide +kernel)
    rw [off_zero] at ht
    exact ht
  refine ⟨?_, hrsp, hsv, ?_, htag, hso, hm'.kept hwf⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    exact hf.load_ret h.st (by rw [stack_eq]; decide)
  · intro q hq
    rw [hso q (fun htag ↦ hq ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
      inRange_mono htag (show 8 ≤ 24 by decide)⟩)]
    exact hs q hq

omit [Host] in
/-- Row zero of the six-round in-place fold is the postcondition's row. -/
theorem row0_at {d : DataMem} {sl : Array EW} {rows : Array (Array EW)}
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64) (hsl : sl.size = 6)
    {p : BitVec 64} (h : ElemsAt d p (Fr sl rows 6) 4096) :
    NativeRustcVm.EWsAt d p
      ((NativeRustcVm.KeccakGkr.openRows sl rows sl.size).getD 0 #[]).toList := by
  obtain ⟨-, hr6⟩ := openRows_shape hsz hrow (sl := sl) (t := 6) (by omega)
  have hl : ((NativeRustcVm.KeccakGkr.openRows sl rows 6).getD 0 #[]).toList.length = 64 := by
    rw [Array.length_toList]
    exact hr6 0 (by decide)
  rw [hsl]
  refine ElemsAt.ewsAt ?_
  rw [hl]
  intro i hi
  have he := h i (by omega)
  rw [Fr_six hsz hrow hsl hi] at he
  show NativeRustcVm.EWAt d _
    (((NativeRustcVm.KeccakGkr.openRows sl rows 6).getD 0 #[]).toList.getD i 0)
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]
  exact he

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
