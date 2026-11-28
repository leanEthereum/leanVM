module

public import NativeRustcVmX64.Transcript.Frame

/-!
# `BasisW::eval`'s frame, through its blocks and calls (x86-64)

`NativeRustcVmX64.Bus.Gkr`'s frame (`Fr`: `Transcript.Frame`, RSP at an offset `o` of it, and the
entry's memory but in the `N` bytes of stack and the outputs) with its block, call and exit steps,
copied here so that `BasisW::eval`'s proof does not depend on the GKR walk's: a call at the
frame's offset `c` (`Fr.call`; `BasisW::eval` calls at `16` and, after pushing two argument
words, at `0`), its changes in its stack, the outputs and `len` bytes of the frame at `lo` (an
`Option<EW>`). The words a body keeps in its frame (`FW`): kept by a block that does not write
them (`FW.block`), stored by one (`FW.write`), kept by a call that does not change them
(`FW.keep`).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript

@[expose] public section

/-- **The frame**, RSP at its offset `o`, the memory the entry's but in the stack and `outs`. -/
structure Fr (m0 : MachineData) (F N : Nat) (slots : Slots) (outs : BitVec 64 → Prop) (o : Nat)
    (d : MachineData) : Prop where
  frame : Frame m0 F slots o d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem
    (fun q ↦ NativeRustcVm.InRange (stackBelow m0 N) N q ∨ outs q)

/-- No write of a block into region 0 overlaps the 8 bytes at offset `o`. -/
def missW (o : Nat) (S : SState) : Bool :=
  S.mem.all fun w ↦ w.r != 0 || decide (w.off + w.n ≤ o) || decide (o + 8 ≤ w.off)

/-- No write of a block into region 0 overlaps the 8 bytes at any of the offsets `os`. -/
def missWs (os : List Nat) (S : SState) : Bool := os.all fun o ↦ missW o S

/-- The registers `rs` hold their values at the block's start. -/
def Keeps (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-- The block wrote the 8 bytes of `v` at offset `o` of region `r`. -/
def wrote (S : SState) (r o : Nat) (v : Sym) : Bool :=
  (List.range 8).all fun i ↦ findWrite r (o + i) S.mem == some (v, i)

end

public section

variable {m0 d d' : MachineData} {F N : Nat} {slots : Slots} {outs : BitVec 64 → Prop}

/-! ## Numbers -/

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
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [stackBelow_N_toNat hS]; have := hS.2.1; omega),
    stackBelow_N_toNat hS]
  omega

/-! ## Block checks -/

theorem writesIn_of_mid {o : Nat} {S : SState} (h : MidOk F o slots S = true) :
    writesIn S = true := by
  simp only [MidOk, Bool.and_eq_true] at h
  exact h.1.1.2

theorem belowRet_of_mid {o : Nat} {S : SState} (h : MidOk F o slots S = true) :
    belowRet F S = true := by
  simp only [MidOk, Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem belowRet_of_pro {o : Nat} {S : SState} (h : ProOk F o slots S = true) :
    belowRet F S = true := by
  simp only [ProOk, Bool.and_eq_true] at h
  exact h.1.1.2

theorem writesIn_of_pro {o : Nat} {S : SState} (h : ProOk F o slots S = true) :
    writesIn S = true := by
  simp only [ProOk, Bool.and_eq_true] at h
  exact h.1.2

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
      (∀ j, c ≤ j → j < F + 8 → (j < lo ∨ lo + len ≤ j) →
        m2.dmem.get? (off (stackBelow m0 F) j) = st.data.dmem.get? (off (stackBelow m0 F) j)) →
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
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hcb]; omega), hcb] at hq
    omega
  have hloc : ∀ q, NativeRustcVm.InRange (off (stackBelow m0 F) lo) len q →
      (rspOf m0).toNat - F + lo ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - F + lo + len := by
    intro q hq
    rcases Nat.eq_zero_or_pos len with h0 | h0
    · subst h0
      exact absurd hq (by unfold NativeRustcVm.InRange; omega)
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [fb_off_toNat hS hFN (by omega)]; omega),
      fb_off_toNat hS hFN (by omega)] at hq
    omega
  have hnot : ∀ j, c ≤ j → (j < lo ∨ lo + len ≤ j) → j < F + 8 →
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
  refine cont m2 ⟨hf', ?_⟩ hq (fun j hj1 hj3 hj2 ↦ hso _ (hnot j hj1 hj2 hj3)) hsv.1
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
    Fr m0 F N slots outs o' d' := by
  have hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow m0 F) F q ∨ outs q) :=
    fun q hq ↦ hm.get?_mem0 hwf fun hw ↦ hq (hW q hw)
  refine ⟨Frame.of_block h.frame hwf hm hmid hle,
    NativeRustcVm.SameOutside.mono (h.same.trans hs) fun q hq ↦ ?_⟩
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
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
  omega

/-- **A block writing only the frame** keeps `Fr`. -/
theorem Fr.block0 [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {o o' : Nat} (h : Fr m0 F N slots outs o d)
    (hS : StackOk m0 N) (hFN : F ≤ N) (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hmid : MidOk F o' slots S = true)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) (h0 : ∀ w ∈ S.mem, w.r = 0) :
    Fr m0 F N slots outs o' d' :=
  h.block hS hFN hwf hm hmid hle fun _ hw ↦ .inl (written_fb hS hFN (fun w hw ↦ ⟨h0 w hw,
    belowRet_spec (belowRet_of_mid hmid) w hw (h0 w hw)⟩) hw)

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
      Saved m0 st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R st0 := by
  refine exec_at hk hx hwf nofun hpc0 hm fun st hm' hpc ↦ ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue h.frame hwf hm' hepi
  have hs : NativeRustcVm.SameOutside d.dmem st.data.dmem outs :=
    fun q hq ↦ hm'.get?_mem0 hwf fun hw ↦ hq (hW q hw)
  simp only [PcOk] at hpc
  refine cont st hm' (by rw [hpc]; exact h.frame.load_ret hS hFN) hrsp
    (NativeRustcVm.SameOutside.mono (h.same.trans hs) fun q hq ↦ ?_) hsv
  rcases hq with hq | hq
  · exact hq
  · exact .inr hq

/-! ## Words of the frame -/

/-- The 8 bytes at offset `o` of region 0 are no write's of a block that misses them. -/
theorem not_written_w [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hin : writesIn S = true) {o : Nat}
    (ho : o + 8 ≤ F + 8) (hmiss : missW o S = true) :
    ∀ i < 8, d'.dmem.get? (off (stackBelow m0 F) (o + i)) =
      d.dmem.get? (off (stackBelow m0 F) (o + i)) := by
  intro i hi
  refine hm.get?_mem0 hwf (not_written0 hwf hm hin (by omega) fun w hw hr ↦ ?_)
  unfold missW at hmiss
  rw [List.all_eq_true] at hmiss
  have := hmiss w hw
  simp only [hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at this
  omega

/-- **A frame word kept** by a block that does not write it. -/
theorem wordAt_block [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hin : writesIn S = true) {o : Nat}
    (ho : o + 8 ≤ F + 8) (hmiss : missW o S = true) {w : UInt64}
    (h : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 F) o) w) :
    NativeRustcVm.WordAt d'.dmem (off (stackBelow m0 F) o) w :=
  bytesAt_congr h fun i hi ↦ by
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [off_add]
    exact not_written_w hwf hm hin ho hmiss i hi'

/-- **A frame word kept** across a change that misses it. -/
theorem wordAt_keep {R : BitVec 64 → Prop} (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    {o : Nat} (hR : ∀ i < 8, ¬ R (off (stackBelow m0 F) (o + i))) {w : UInt64}
    (h : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 F) o) w) :
    NativeRustcVm.WordAt d'.dmem (off (stackBelow m0 F) o) w :=
  bytesAt_congr h fun i hi ↦ by
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [off_add]
    exact hso _ (hR i hi')

theorem missWs_spec {os : List Nat} {S : SState} (h : missWs os S = true) :
    ∀ o ∈ os, missW o S = true := by
  unfold missWs at h
  rw [List.all_eq_true] at h
  exact h

theorem wrote_spec {S : SState} {r o : Nat} {v : Sym} (h : wrote S r o v = true) :
    ∀ i < 8, findWrite r (o + i) S.mem = some (v, i) := by
  intro i hi
  unfold wrote at h
  rw [List.all_eq_true] at h
  exact beq_iff_eq.mp (h i (List.mem_range.mpr hi))

/-- A register a block kept. -/
theorem keeps_reg [Labels] {d d' : MachineData} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} {l : List Reg64}
    (hm : Match (Env.ofMachine d rs vars ret) S d') (hk : Keeps S l = true) {r : Reg64}
    (hr : r ∈ l) : reg d' r = reg d r := by
  unfold Keeps at hk
  rw [List.all_eq_true] at hk
  exact hm.regs r _ (beq_iff_eq.mp (hk r hr))

/-- A register a block set to `v`. -/
theorem reg_eval [Labels] {env : Env} {S : SState} {d' : MachineData} (hm : Match env S d')
    {r : Reg64} {v : Sym} (h : S.reg r = some v) : reg d' r = v.eval env :=
  hm.regs r v h

/-- **A frame word a block stored.** -/
theorem wordAt_wrote [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (frameEnv m0 d F rest vars ret) S d') {o : Nat}
    (ho : o + 8 ≤ F + 8) {v : Sym} (hw : wrote S 0 o v = true) :
    NativeRustcVm.WordAt d'.dmem (off (stackBelow m0 F) o)
      (UInt64.ofBitVec (v.eval (frameEnv m0 d F rest vars ret))) :=
  wordAt_write hm (r := 0) rfl ho (wrote_spec hw)

/-- **A frame word loaded.** -/
theorem load_fw [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {o : Nat} {w : UInt64}
    (h : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 F) o) w) :
    (frameEnv m0 d F rest vars ret).load 0 o 8 = w.toBitVec :=
  load_ofMachine (r := 0) rfl h

/-- `Fr` with more outputs. -/
theorem Fr.mono_outs {o : Nat} {outs' : BitVec 64 → Prop} (h : Fr m0 F N slots outs o d)
    (ho : ∀ q, outs q → outs' q) : Fr m0 F N slots outs' o d :=
  ⟨h.frame, NativeRustcVm.SameOutside.mono h.same fun q hq ↦ hq.imp id (ho q)⟩

/-- A machine state at an address. -/
theorem at_pc [Host] {st : MachineState} {pc : Int64} (h : st.pc = pc) {R : MachineState → Prop}
    (H : Eventually (step1 Host.exe) R ⟨st.data, pc⟩) : Eventually (step1 Host.exe) R st := by
  obtain ⟨d, q⟩ := st
  simp only at h
  subst h
  exact H

end

end NativeRustcVmX64.Whir.BasisWEval
