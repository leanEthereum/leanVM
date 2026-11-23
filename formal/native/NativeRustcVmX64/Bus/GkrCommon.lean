module

public import NativeRustcVmX64.Sumcheck.Ctx
public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVmX64.Spec.Bus

/-!
# The GKR walk's proofs: what they share (x86-64)

A function's frame is region 0 of its blocks' environments (`frameEnv`, `Frame`): the `F` bytes
below the entry's RSP and the return address. `Fr m0 F N slots outs o d` adds that `d`'s memory is
the entry's but in the `N` bytes of stack and the outputs `outs`.

- `Frame.call_at`: a call at the frame's offset `c` keeps the frame, RSP then at `c + 8`.
- `Fr.call`: a callee's contract from a state of the frame at offset `c`; its changes in its
  stack below `c`, the outputs and `len` bytes of the frame at `lo` (below the slots).
- `Fr.block`: a block keeps `Fr`, its writes in the frame or the outputs.
- `Fr.exit`: the epilogue, back at the entry's return address.
- Numbers: `fb_off_toNat` (the frame's byte `j`), `inRange_toNat` (a range as an interval).
-/

namespace NativeRustcVmX64.Bus.Gkr

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeRustcVm.Transcript

@[expose] public section

/-- **The frame**, RSP at its offset `o`, the memory the entry's but in the stack and `outs`. -/
structure Fr (m0 : MachineData) (F N : Nat) (slots : Slots) (outs : BitVec 64 → Prop) (o : Nat)
    (d : MachineData) : Prop where
  frame : Frame m0 F slots o d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem
    (fun q ↦ NativeRustcVm.InRange (stackBelow m0 N) N q ∨ outs q)

end

public section

variable {m0 d d' : MachineData} {F N : Nat} {slots : Slots} {outs : BitVec 64 → Prop}

/-! ## Numbers -/

/-- A range that does not wrap, as an interval. -/
theorem inRange_toNat {a q : BitVec 64} {n : Nat} (h : a.toNat + n ≤ 2 ^ 64) :
    NativeRustcVm.InRange a n q ↔ a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + n :=
  inRange_iff' h

/-- The frame's byte `j`. -/
theorem fb_off_toNat (hS : StackOk m0 N) (hF : F ≤ N) {j : Nat} (hj : j < F + 8) :
    (off (stackBelow m0 F) j).toNat = (rspOf m0).toNat - F + j := by
  have := hS.1
  have := hS.2.1
  rw [toNat_off (by rw [stackBelow_toNat (by omega)]; omega), stackBelow_toNat (by omega)]

theorem stackBelow_N_toNat (hS : StackOk m0 N) : (stackBelow m0 N).toNat = (rspOf m0).toNat - N :=
  stackBelow_toNat hS.1

/-- The stack as an interval. -/
theorem inRange_stack (hS : StackOk m0 N) {q : BitVec 64} :
    NativeRustcVm.InRange (stackBelow m0 N) N q ↔
      (rspOf m0).toNat - N ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat := by
  have := hS.1
  rw [inRange_toNat (by rw [stackBelow_N_toNat hS]; have := hS.2.1; omega), stackBelow_N_toNat hS]
  omega

/-- The frame's base `c` bytes up is the stack `F - c` below the entry's RSP. -/
theorem off_fb (hS : StackOk m0 N) (hF : F ≤ N) {c : Nat} (hc : c ≤ F) :
    off (stackBelow m0 F) c = stackBelow m0 (F - c) := by
  apply BitVec.eq_of_toNat_eq
  have := hS.1
  rw [fb_off_toNat hS hF (by omega), stackBelow_toNat (by omega)]
  omega

/-! ## Calls -/

/-- **A call** at the frame's offset `c` keeps the frame where the callee changes none of its
slots' or the return address's bytes. -/
theorem Frame.call_at {c : Nat} (hf : Frame m0 F slots c d) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ p ∈ slots, ∀ i < 8, ¬ R (off (stackBelow m0 F) (p.1 + i)))
    (hRr : ∀ j < 8, ¬ R (off (stackBelow m0 F) (F + j))) : Frame m0 F slots (c + 8) d' := by
  refine ⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept hs.2, fun r hr hsl ↦ ?_⟩
  · rw [hrsp, hf.sp]
    exact off_add _ _ _
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [off_add]
    exact hso _ (hR p hp i hi')
  · rw [hso _ (hRr j hj)]
    exact hf.ret j hj
  · exact (hs.1 r hr).trans (hf.regs r hr hsl)

/-- A state of the frame at offset `c` is at a call of a function with an `F - c`-byte frame. -/
theorem Fr.at_ [Labels] {t : BitVec 64} {a : DecArea} {c : Nat} (cx : Ctx m0 t a N F)
    (h : Fr m0 F N slots outs c d) (hc : c ≤ F)
    (hout : ∀ q, outs q → ¬ NativeRustcVm.InRange rcAddr 192 q) : At m0 (F - c) d :=
  ⟨by rw [h.frame.sp, off_fb cx.stack cx.le hc], h.frame.kept,
    rc_keep h.same fun q hq ↦ hq.elim (fun hq ↦ cx.not_rc_stack hq) (hout q)⟩

/-- **A call from the frame** at offset `c`: the callee's contract, its changes in its stack
below `c`, the outputs and `len` bytes of the frame at `lo`, below the slots. -/
theorem Fr.call [Host] {c Nc lo len : Nat} (hS : StackOk m0 N) (hFN : F ≤ N) (hcF : c ≤ F)
    (hle : F - c + Nc ≤ N) (hsl : ∀ p ∈ slots, c ≤ p.1 ∧ lo + len ≤ p.1 ∧ p.1 + 8 ≤ F)
    (hlo : lo + len ≤ F)
    (houts : ∀ q, outs q → ¬ NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q)
    {X : BitVec 64 → Prop}
    (hX : ∀ q, X q → outs q ∨ NativeRustcVm.InRange (off (stackBelow m0 F) lo) len q)
    {l : Label} {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : Spec (Labels.label l) P Q) {st : MachineState} {next : Int64}
    {R : MachineState → Prop} (h : Fr m0 F N slots outs c st.data)
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (hQ : ∀ m', Q st.data m' → NativeRustcVm.SameOutside st.data.dmem m'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow st.data Nc) Nc q ∨ X q) ∧ Saved st.data m')
    (cont : ∀ m2 : MachineData, Fr m0 F N slots outs (c + 8) m2 → Q st.data m2 →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem
        (fun q ↦ NativeRustcVm.InRange (stackBelow st.data Nc) Nc q ∨ X q) →
      (∀ r, calleeSaved r = true → m2.regs.get64 r = st.data.regs.get64 r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  refine Eventually.bind (Spec.apply hspec hpc.1 hP) fun ⟨m2, pc⟩ ⟨hpc', hrsp', hq⟩ ↦ ?_
  simp only at hpc' hrsp' hq
  rw [hpc', hpc.2]
  obtain ⟨hso, hsv⟩ := hQ _ hq
  have e1 := hS.1
  have e2 := hS.2.1
  have hsp : (rspOf st.data).toNat = (rspOf m0).toNat - F + c := by
    rw [h.frame.sp, fb_off_toNat hS hFN (by omega)]
  have hcb : (stackBelow st.data Nc).toNat = (rspOf m0).toNat - F + c - Nc := by
    rw [stackBelow_toNat (by omega), hsp]
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st.data Nc) Nc q →
      (rspOf m0).toNat - F + c - Nc ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - F + c := by
    intro q hq
    rw [inRange_toNat (by rw [hcb]; omega), hcb] at hq
    omega
  have hloc : ∀ q, NativeRustcVm.InRange (off (stackBelow m0 F) lo) len q →
      (rspOf m0).toNat - F + lo ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - F + lo + len := by
    intro q hq
    rcases Nat.eq_zero_or_pos len with h0 | h0
    · subst h0
      exact absurd hq (by unfold NativeRustcVm.InRange; omega)
    rw [inRange_toNat (by rw [fb_off_toNat hS hFN (by omega)]; omega),
      fb_off_toNat hS hFN (by omega)] at hq
    omega
  have hnot : ∀ j, c ≤ j → lo + len ≤ j → j < F + 8 →
      ¬ (NativeRustcVm.InRange (stackBelow st.data Nc) Nc (off (stackBelow m0 F) j) ∨
        X (off (stackBelow m0 F) j)) := by
    intro j hj1 hj2 hj3 hin
    have hq := fb_off_toNat hS hFN hj3 (m0 := m0)
    rcases hin with hin | hin
    · have := hcal _ hin
      omega
    · rcases hX _ hin with hin | hin
      · exact houts _ hin (inRange_off_self hj3 (by
          have := stackBelow_toNat (m := m0) (n := F) (by omega); omega))
      · have := hloc _ hin
        omega
  have hf' : Frame m0 F slots (c + 8) m2 :=
    Frame.call_at h.frame hsv hrsp' hso
      (fun p hp i hi ↦ hnot _ (by have := hsl p hp; omega) (by have := hsl p hp; omega)
        (by have := hsl p hp; omega))
      (fun j hj ↦ hnot _ (by omega) (by omega) (by omega))
  refine cont m2 ⟨hf', ?_⟩ hq hso hsv.1
  refine NativeRustcVm.SameOutside.mono (h.same.trans hso) fun q hq ↦ ?_
  rcases hq with hq | hq | hq
  · exact hq
  · left
    rw [inRange_stack hS]
    have := hcal q hq
    omega
  · rcases hX q hq with hq | hq
    · exact .inr hq
    · left
      rw [inRange_stack hS]
      have := hloc q hq
      omega

/-! ## Blocks -/

/-- **A block** keeps `Fr`: its writes in the frame below the return address or the outputs. -/
theorem Fr.block [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {o o' : Nat} (h : Fr m0 F N slots outs o d)
    (hS : StackOk m0 N) (hFN : F ≤ N) (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hmid : MidOk F o' slots S = true)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hW : ∀ q, Written (frameEnv m0 d F rest vars ret) S q →
      NativeRustcVm.InRange (stackBelow m0 F) F q ∨ outs q) :
    Fr m0 F N slots outs o' d' ∧ NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow m0 F) F q ∨ outs q) := by
  have hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow m0 F) F q ∨ outs q) :=
    fun q hq ↦ hm.get?_mem0 hwf fun hw ↦ hq (hW q hw)
  refine ⟨⟨Frame.of_block h.frame hwf hm hmid hle,
    NativeRustcVm.SameOutside.mono (h.same.trans hs) fun q hq ↦ ?_⟩, hs⟩
  rcases hq with hq | hq | hq
  · exact hq
  · exact .inl (inRange_frame_stack hS.2.1 hS.1 hFN hq)
  · exact .inr hq

/-- A block's writes, all in region 0 below `F`, are in the frame. -/
theorem written_fb [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hS : StackOk m0 N) (hFN : F ≤ N)
    (h0 : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F) {q : BitVec 64}
    (hq : Written (frameEnv m0 d F rest vars ret) S q) :
    NativeRustcVm.InRange (stackBelow m0 F) F q := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hq
  obtain ⟨hr, hle⟩ := h0 w hw
  rw [hr] at hb
  cases hb
  have := hS.1
  have := hS.2.1
  have hb := stackBelow_toNat (m := m0) (n := F) (by omega)
  rw [inRange_toNat (by omega)]
  omega

/-- A block's writes in region 0 below `F` or in region 1, `x`, of `n` bytes. -/
theorem written_fb1 [Labels] {x : BitVec 64} {n : Nat} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hS : StackOk m0 N) (hFN : F ≤ N)
    (h0 : ∀ w ∈ S.mem, (w.r = 0 ∧ w.off + w.n ≤ F) ∨ (w.r = 1 ∧ w.off + w.n ≤ n))
    (hx : x.toNat + n ≤ 2 ^ 64) {q : BitVec 64}
    (hq : Written (frameEnv m0 d F [(x, n)] vars ret) S q) :
    NativeRustcVm.InRange (stackBelow m0 F) F q ∨ NativeRustcVm.InRange x n q := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hq
  have := hS.1
  have := hS.2.1
  have hfb := stackBelow_toNat (m := m0) (n := F) (by omega)
  rcases h0 w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩
  · rw [hr] at hb
    cases hb
    left
    rw [inRange_toNat (by omega)]
    omega
  · rw [hr] at hb
    cases hb
    right
    rw [inRange_toNat hx]
    omega

/-- **The prologue**, from the entry, writing only the frame. -/
theorem Fr.of_prologue [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {o : Nat} (hS : StackOk m0 N) (hFN : F ≤ N)
    (hwf : (frameEnv m0 m0 F rest vars ret).WF) (hm : Match (frameEnv m0 m0 F rest vars ret) S d)
    (hpro : ProOk F o slots S = true) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hcs : ∀ p ∈ slots, calleeSaved p.2 = true) (h0 : ∀ w ∈ S.mem, w.r = 0) :
    Fr m0 F N slots outs o d := by
  refine ⟨Frame.of_prologue Frame.entry hwf hm hpro hle hcs, fun q hq ↦ ?_⟩
  refine hm.get?_mem0 hwf fun hw ↦ hq (.inl (inRange_frame_stack hS.2.1 hS.1 hFN ?_))
  exact written_fb hS hFN (fun w hw ↦ ⟨h0 w hw,
    belowRet_spec (belowRet_of_pro hpro) w hw (h0 w hw)⟩) hw

/-- **A block writing only the frame** keeps `Fr`. -/
theorem Fr.block0 [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {o o' : Nat} (h : Fr m0 F N slots outs o d)
    (hS : StackOk m0 N) (hFN : F ≤ N) (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hmid : MidOk F o' slots S = true)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) (h0 : ∀ w ∈ S.mem, w.r = 0) :
    Fr m0 F N slots outs o' d' ∧
      NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (stackBelow m0 F) F) := by
  have hW : ∀ q, Written (frameEnv m0 d F rest vars ret) S q →
      NativeRustcVm.InRange (stackBelow m0 F) F q := fun q hw ↦
    written_fb hS hFN (fun w hw ↦ ⟨h0 w hw,
      belowRet_spec (belowRet_of_mid hmid) w hw (h0 w hw)⟩) hw
  exact ⟨(h.block hS hFN hwf hm hmid hle fun q hw ↦ .inl (hW q hw)).1,
    fun q hq ↦ hm.get?_mem0 hwf fun hw ↦ hq (hW q hw)⟩

/-- **The `GkrStateW` kept** where the memory changed apart from it. -/
theorem gkrStateWAt_keep {d d' : Mem 64} {p : BitVec 64} {g : NativeVm.Model.GkrStateW}
    {R : BitVec 64 → Prop} (h : NativeRustcVm.Bus.GkrStateWAt d p g)
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange p NativeRustcVm.Bus.gkrStateBytes q) :
    NativeRustcVm.Bus.GkrStateWAt d' p g := by
  have hb : NativeRustcVm.Bus.gkrStateBytes = 1064 := rfl
  have hin : ∀ j, j < 1064 → ¬ R (off p j) := fun j hj hq ↦
    hR _ hq (inRange_off_self (by rw [hb]; exact hj) (by rw [hb]; omega))
  obtain ⟨hsz, hv, ⟨hl, hw, hx⟩⟩ := h
  refine ⟨hsz, NativeRustcVm.BytesAt.of_sameOutside hv hs fun i hi ↦ hin i ?_,
    hl, NativeRustcVm.BytesAt.of_sameOutside hw hs fun i hi ↦ ?_, ?_⟩
  · rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsz] at hi
    omega
  · rw [off_add]
    exact hin _ (by rw [NativeRustcVm.length_wordBytes] at hi; omega)
  · have e : off p 48 + 8#64 = off p 56 := off_add _ _ _
    rw [e] at hx ⊢
    refine NativeRustcVm.BytesAt.of_sameOutside hx hs fun i hi ↦ ?_
    rw [off_add]
    rw [NativeRustcVm.length_ewsBytes] at hi
    unfold NativeRustcVm.Bus.busPointCap at hl
    exact hin _ (by omega)

/-! ## The exit -/

/-- **The epilogue**, from a state of the frame: back at the entry's return address, RSP 8 above
the entry's, the callee-saved registers the entry's; its writes in the outputs. -/
theorem Fr.exit [Host] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {o : Nat}
    {S S' : SState} {ds : List Directive} {k : Nat} {R : MachineState → Prop}
    (h : Fr m0 F N slots outs o d) (hS : StackOk m0 N) (hFN : F ≤ N)
    (hk : ds.IsInfixAt Host.prog k) (hx : exec ds S = some (S', .ret (.load 0 F 8)))
    (hwf : (frameEnv m0 d F rest vars 0).WF) {st0 : MachineState} (hpc0 : st0.pc = Host.addrOf k)
    (hm : Match (frameEnv m0 d F rest vars 0) S st0.data)
    (hepi : EpiOk F slots S' = true)
    (hW : ∀ q, Written (frameEnv m0 d F rest vars 0) S' q → outs q)
    (cont : ∀ st : MachineState, Match (frameEnv m0 d F rest vars 0) S' st.data →
      st.pc = retOf m0 → rspOf st.data = rspOf m0 + 8#64 →
      NativeRustcVm.SameOutside m0.dmem st.data.dmem
        (fun q ↦ NativeRustcVm.InRange (stackBelow m0 N) N q ∨ outs q) →
      NativeRustcVm.SameOutside d.dmem st.data.dmem outs →
      Saved m0 st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R st0 := by
  refine exec_at hk hx hwf nofun hpc0 hm fun st hm' hpc ↦ ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue h.frame hwf hm' hepi
  have hs : NativeRustcVm.SameOutside d.dmem st.data.dmem outs :=
    fun q hq ↦ hm'.get?_mem0 hwf fun hw ↦ hq (hW q hw)
  simp only [PcOk] at hpc
  refine cont st hm' (by rw [hpc]; exact h.frame.load_ret hS hFN) hrsp
    (NativeRustcVm.SameOutside.mono (h.same.trans hs) fun q hq ↦ ?_) hs hsv
  rcases hq with hq | hq
  · exact hq
  · exact .inr hq

/-- A machine state at an address. -/
theorem at_pc [Host] {st : MachineState} {pc : Int64} (h : st.pc = pc) {R : MachineState → Prop}
    (H : Eventually (step1 Host.exe) R ⟨st.data, pc⟩) : Eventually (step1 Host.exe) R st := by
  obtain ⟨d, q⟩ := st
  simp only at h
  subst h
  exact H

/-- **The epilogue before a tail call**: the slots popped, RSP at the entry's: `Saved`, the entry's
return address at RSP. -/
theorem Frame.tail [Labels] {o : Nat} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hf : Frame m0 F slots o d)
    (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hl : slotsLoaded slots S = true)
    (hk : keepsOthers slots S = true) (hsp : S.reg .rsp = some (.ptr 0 (F : Int))) :
    Saved m0 d' ∧ rspOf d' = rspOf m0 := by
  have hslot : ∀ p ∈ slots, reg d' p.2 = reg m0 p.2 := by
    intro p hp
    unfold slotsLoaded at hl
    rw [List.all_eq_true] at hl
    have := hm.regs p.2 _ (by simpa using hl p hp)
    rw [Sym.eval, load_ofMachine (o := p.1) rfl (hf.slot p hp)] at this
    exact this
  refine ⟨⟨fun r hr ↦ ?_, kept_trans hf.kept (hm.kept hwf)⟩, ?_⟩
  · cases hs : slots.any (·.2 == r)
    · have := hm.regs r _ (keepsOthers_spec hk hr hs)
      rw [Sym.eval, Env.ofMachine_regs] at this
      exact this.trans (hf.regs r hr hs)
    · obtain ⟨p, hp, hpr⟩ := List.any_eq_true.mp hs
      rw [← Reg64.eq_of_beq hpr]
      exact hslot p hp
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp, eval_ptr0, off_frame_F]

/-- The entry's return address, where RSP and its bytes are the entry's. -/
theorem retOf_of [Labels] {o : Nat} (hf : Frame m0 F slots o d) (hd : d'.dmem = d.dmem)
    (hrsp : rspOf d' = rspOf m0) : retOf d' = retOf m0 := by
  unfold retOf
  rw [hrsp, loadInt_congr fun i hi ↦ ?_]
  rw [hd, ← frame_add F i]
  exact hf.ret i hi

/-! ## Results -/

/-- `test %al, %al` of an `Option<()>` in AL: zero exactly on `None`. -/
theorem testAl_okAl {m : MachineData} {b : Bool} (h : OkAl m b) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg m .rax) (reg m .rax)) (BitVec.ofNat 64 0) =
      !b := by
  rw [testAl_eq]
  unfold OkAl boolRet at h
  rw [h]
  cases b <;> rfl

end

end NativeRustcVmX64.Bus.Gkr
