module

public import NativeRustcX64.WotsLeaf.Epilogue
public import NativeRustcX64.WotsLeaf.Input

/-!
# Returning the result

`finish`: from `b12` (directive 158) with RSP the frame's base, the saved registers in place, the
entry's mapped bytes kept, memory changed only at `out` and in the stack area, and the result at
`out` (`WotsLeafOut1`), the function returns with its postcondition (`Run.Done`). `fail_path`:
from `b11` (directive 155) the tag `0` stored at `out`, then `finish`. A block with `out` as
region 4 (`match_out`, `outWrites`, `sameOutside_out`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf

@[expose] public section

/-- The writes of a symbolic state are all in `out` (region 4). -/
def outWrites (S : SState) : Bool := S.mem.all fun w ↦ w.r == 4 && decide (w.off + w.n ≤ 75)

end

public section

section
variable {r : Run} [Labels]

/-- `out` as the executor's region 4, the alias of the word at `96` its base. -/
theorem match_out (hpre : r.Pre) {L : List Slot} {m : MachineData} (hK : Keep r L m)
    (h96 : BytesAt m.dmem (r.off 96) (regBytes r.out)) {ret : BitVec 64} {k : List (Reg64 × Sym)}
    (hk : KnownOK r m [(r.out, 75)] ret k) :
    Match (r.envR m [(r.out, 75)] ret) (outS k) m ∧ (r.envR m [(r.out, 75)] ret).WF := by
  refine ⟨match_frameS (fun _ hl _ hi => r.got_byte hpre hK.1.2.2.1 hl hi)
    hK.1.1 (sextra := [75]) (extra := [(r.out, 75)]) (bounds := [])
    (aliases := [(.load 0 96 8, (4, 0))])
    (show 75 = 75 ∧ True from ⟨rfl, trivial⟩) hk trivial ⟨?_, trivial⟩,
    envR_wf hpre hK.1.2.2.2 (r.extraOK_input hpre hK.1.2.2.2 (r.pre_out hpre)
      (fun l hl => ((r.got hpre).1 l hl).2.2.2 (r.out, 75) (by simp))) ret⟩
  show (r.envR m [(r.out, 75)] ret).load 0 96 8 = r.out + BitVec.ofInt 64 0
  rw [r.load_word h96]
  simp

/-- The writes of a block all in `out` change only `out`'s bytes. -/
theorem sameOutside_out {m m' : MachineData} {ret : BitVec 64} {S : SState}
    (hpre : r.Pre) (hm : Match (r.envR m [(r.out, 75)] ret) S m')
    (hwf : (r.envR m [(r.out, 75)] ret).WF) (hall : outWrites S = true) :
    SameOutside m.dmem m'.dmem (InRange r.out 75) := by
  have hnw := (r.pre_out hpre).2.1
  intro p hp
  apply hm.get?_mem0 hwf
  rintro ⟨w, hw, b, sz, hb, h1, h2⟩
  have := List.all_eq_true.mp hall w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  obtain ⟨hr, hn⟩ := this
  rw [hr] at hb
  cases hb
  apply hp
  unfold NoWrap at hnw
  rw [Sym.inRange_iff hnw]
  omega

end

variable [Host]

/-- **Returning the result** from `b12`. -/
theorem finish (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) (m : MachineData)
    (hsp : reg m .rsp = r.base) (hsv : BytesAt m.dmem (r.off 2712) (savedBytes r.m0))
    (hk : Kept r.m0.dmem m.dmem) (hs : SameOutside r.m0.dmem m.dmem r.Changed)
    (hout : WotsLeafOut1 (bytesOf m.dmem r.out 75) r.result) :
    Eventually (step1 Host.exe) r.Done ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b12Offset⟩ :=
  Eventually.mono (epilogue r hp hpre m hsp hsv hk hs) fun st ⟨hpc, hrsp, hS, hmem⟩ ↦ by
    have hb : bytesOf st.data.dmem r.out 75 = bytesOf m.dmem r.out 75 := by
      unfold bytesOf
      simp only [hmem]
    refine ⟨hpc, hrsp, ?_, fun p hp' ↦ (hmem p).trans (hs p hp'), hS⟩
    show WotsLeafOut1 (bytesOf st.data.dmem r.out 75) r.result
    rw [hb]
    exact hout

/-- **No codeword**: from `b11`, the tag `0` at `out`, then the return. -/
theorem fail_path (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) {L : List Slot}
    (m : MachineData) (hK : Keep r L m) (h96 : BytesAt m.dmem (r.off 96) (regBytes r.out))
    (hnone : r.result = none) :
    Eventually (step1 Host.exe) r.Done ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b11Offset⟩ := by
  obtain ⟨hm, hwf⟩ := match_out hpre hK h96 (ret := (r.pc (NativeRustcX64.Xmss.WotsLeaf.b11Offset + b11.length)).toBitVec) (k := [])
    trivial
  refine blk r hp b11_in_code (List.cons_ne_nil _ _) run_b11 hwf rfl hm
    fun st hm' hpc ↦ pc_at hpc ?_
  have hso1 := sameOutside_out hpre hm' hwf (by decide)
  have h0 := bytesAt_write_val hm' (r := 4) (o := 0) (n := 1) (b := r.out) (sz := 75) rfl
    (by decide) (v := .lit 0) (by decide)
  refine finish r hp hpre st.data ?_ ?_ ?_ ?_ ?_
  · unfold reg
    rw [hm'.regs .rsp _ rfl, show (0 : Int) = ((0 : Nat) : Int) from rfl, eval_ptr0, Run.off_zero]
  · refine r.bytesAt_kept hpre hm' hwf (by rw [Run.length_savedBytes]; decide) hK.1.2.1 ?_
    rw [Run.length_savedBytes]
    decide
  · exact fun p h ↦ hm'.kept hwf p (hK.1.2.2.2 p h)
  · intro p hp'
    rw [hso1 p fun h ↦ hp' (.inl h), hK.1.2.2.1 p fun h ↦ hp' (.inr h)]
  · rw [hnone]
    show (bytesOf st.data.dmem r.out 75).head? = some 0
    have := h0 0 (by simp)
    rw [addr_add_add] at this
    simp only [bytesOf, List.range_succ_eq_map, List.map_cons, List.head?_cons, this]
    simp [Sym.eval, byteOf]

end

end NativeRustcX64.WotsLeafProof
