module

public import NativeRustcX64.SphincsVerify.Parse.WordsTurn
public import NativeRustcX64.SphincsVerify.Parse.WordsExec

/-!
# The parse, part 2: the words 8 .. 537 and the first counter (`b2 .. b3`, x86-64)

The loop `b2` copies the words 8 .. 537 to the frame's `11404` (106 turns of 5 words, R15 the
offset); `b3` stores the first layer's counter word big-endian at `15644` and sets up the loop
`b4` (EAX `5360`). Result: `WS P1` at `b4` (directive 60).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
  LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The raw signature's bytes after `b3`. -/
def P1 (w : Nat → UInt64) : List UInt8 := wb w 8 530 ++ be32 (w 538).toUInt32

end

public section

theorem length_P1 (w : Nat → UInt64) : (P1 w).length = 4244 := by
  simp [P1, length_wb, be32]

variable (r : Run) [Host]

theorem pc_next {st : MachineState} {a b : Nat} {ds : List Directive}
    (h : st.pc = Host.addrOf (r.k + a + ds.length)) (hb : a + ds.length = b) : st.pc = r.pc b := by
  rw [h, Nat.add_assoc, hb]
  rfl

/-- `ctxS` describes a state of the frame with RBX the context. -/
theorem ctxS_match {m : MachineData} (hF : r.Frame m) (hrbx : Run.RegIs m .rbx (ctx r))
    (vars : Nat → BitVec 64) (ret : BitVec 64) :
    Match (Env.ofMachine m (regs3 r) vars ret) ctxS m :=
  match_ofMachine ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
    ⟨by
      show rspOf m = r.base + BitVec.ofInt 64 0
      rw [hF.1]
      simp,
    by
      show reg m .rbx = r.input + BitVec.ofInt 64 (-1024)
      rw [input_sub]
      exact hrbx, trivial⟩
    trivial trivial
    ⟨r.alias8, by
      show r.base + BitVec.ofInt 64 (-16) = (r.base - 16#64) + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 (-16) = -16#64 by decide, show BitVec.ofInt 64 0 = 0#64 by decide]
      bv_omega, trivial⟩

/-- **A turn of `b2`**. -/
theorem b2_turn (hp : Placed code r.k) (hpre : r.Pre) {j : Nat} (hj : j < 106) {m : MachineData}
    (h : WS r (wb r.w 8 (5 * j)) m ∧ Run.RegIs m .r15 (BitVec.ofNat 64 (40 * j))) :
    Eventually (step1 Host.exe) (fun st ↦ (st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b3Offset ∧ WS r (wb r.w 8 530) st.data) ∨
      (j + 1 < 106 ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b2Offset ∧ WS r (wb r.w 8 (5 * (j + 1))) st.data ∧
        Run.RegIs st.data .r15 (BitVec.ofNat 64 (40 * (j + 1))))) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b2Offset⟩ := by
  obtain ⟨hw, h12⟩ := h
  have hk : b2.IsInfixAt Host.prog (r.k + NativeRustcX64.Sphincs.SphincsVerify.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := wf_in_frame r hpre hw.1.2.2.2 hw.1.2.2.1 (s := 8 + 5 * j) (k := 8 * 5)
    (a := 11404 + 40 * j) (n := 8 * 5) (by omega) (by decide) (by omega) (fun _ ↦ 0) 0
  have hbx : reg m .rbx = ctx r := hw.2.2.2.1
  have h12' : reg m .r15 = BitVec.ofNat 64 (40 * j) := h12
  have hm : Match (Env.ofMachine m [(r.input + BitVec.ofNat 64 (8 * (8 + 5 * j)), 8 * 5),
      (r.off (11404 + 40 * j), 8 * 5)] (fun _ ↦ 0) 0) (turnS .r15 40 (-1088) (-11404)) m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ trivial trivial trivial
      ⟨by
        sym_simp
        simp only [Env.ofMachine_regs]
        show reg m .rbx + reg m .r15 = r.input + BitVec.ofNat 64 (8 * (8 + 5 * j)) +
          BitVec.ofInt 64 (-((1088 : Nat) : Int))
        rw [hbx, h12']
        refine alias_neg 1088 ?_
        bv_lin, by
        sym_simp
        simp only [Env.ofMachine_regs]
        show reg m .rsp + reg m .r15 = r.off (11404 + 40 * j) + BitVec.ofInt 64 (-((11404 : Nat) : Int))
        rw [show reg m .rsp = r.base from hw.1.1, h12']
        refine alias_neg 11404 ?_
        bv_lin, trivial⟩
  refine exec_then hk run_b2 hwf (fun _ h ↦ nomatch h) hm fun st hm' hpc ↦ ?_
  obtain ⟨hF', hnew, hout, hbx', hkey'⟩ := copy_turn r hpre hw (s := 8 + 5 * j) (q := 5)
    (d := 11404 + 40 * j) (by omega) (by omega) hm hm' hwf (by decide) (by decide) (by decide)
  have hraw : BytesAt st.data.dmem (r.off 11404) (wb r.w 8 (5 * (j + 1))) := by
    rw [show 5 * (j + 1) = 5 * j + 5 by omega, wb_add]
    refine BytesAt.append (fact_keep r hpre hw.2.2.1 hout (length_wb _ _ _) (by left; omega)
      (by omega) (by omega)) ?_
    rw [length_wb, off_add, show 11404 + 8 * (5 * j) = 11404 + 40 * j by omega,
      show 8 + 5 * j = 8 + 5 * j from rfl]
    exact hnew
  have hmsg := fact_keep r hpre hw.2.1 hout (length_msg r) (by left; omega) (by decide) (by omega)
  have hv : Sym.eval (Env.ofMachine m [(r.input + BitVec.ofNat 64 (8 * (8 + 5 * j)), 8 * 5),
      (r.off (11404 + 40 * j), 8 * 5)] (fun _ ↦ 0) 0) (.bin .add .W64 (.lit 40) (.reg .r15)) =
      BitVec.ofNat 64 (40 * (j + 1)) := by
    sym_simp
    simp only [Env.ofMachine_regs]
    show BitVec.ofNat 64 40 + reg m .r15 = _
    rw [h12']
    bv_lin
  have h12'' : Run.RegIs st.data .r15 (BitVec.ofNat 64 (40 * (j + 1))) := (hm'.regs .r15 _ rfl).trans hv
  obtain ⟨hne, heq⟩ := pc_cond hpc hv (by omega) (by decide)
  by_cases hj1 : j + 1 < 106
  · rw [hp.label NativeRustcX64.Sphincs.SphincsVerify.label_1_at] at hne
    exact .done _ (Or.inr ⟨hj1, hne (by omega), ⟨hF', hmsg, hraw, hbx', hkey'⟩, h12''⟩)
  · obtain rfl : j = 105 := by omega
    exact .done _ (Or.inl ⟨pc_next r (heq rfl) rfl, ⟨hF', hmsg, hraw, hbx', hkey'⟩⟩)

/-- **The loop `b2`**: the words 8 .. 537. -/
theorem b2_loop (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData} (h : AtW r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b3Offset ∧ WS r (wb r.w 8 530) st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b2Offset⟩ :=
  count_loop (σ := MachineState) (P := fun j st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b2Offset ∧ WS r (wb r.w 8 (5 * j)) st.data ∧
      Run.RegIs st.data .r15 (BitVec.ofNat 64 (40 * j))) 106
    (fun j st hj ⟨hpc, h⟩ ↦ by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc
      exact b2_turn r hp hpre hj h) (j := 0) (s := ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b2Offset⟩) (by decide)
    ⟨rfl, ⟨h.1, h.2.1.1.2, fun i hi ↦ by simp [wb, Native.Keccak.wordsBytes] at hi, h.2.2.1,
      h.2.2.2.1⟩, h.2.2.2.2⟩

/-- **`b3`**: the first layer's counter; EAX `5360`. -/
theorem b3_spec (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData}
    (h : WS r (wb r.w 8 530) m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b4Offset ∧ WS r (P1 r.w) st.data ∧
      Run.RegIs st.data .rax (BitVec.ofNat 64 5360)) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b3Offset⟩ := by
  have hk : b3.IsInfixAt Host.prog (r.k + NativeRustcX64.Sphincs.SphincsVerify.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := wf3 r hpre h.1.2.2.2 h.1.2.2.1 (fun _ ↦ 0) 0
  have hm := ctxS_match r h.1 h.2.2.2.1 (fun _ ↦ 0) 0
  refine exec_then hk run_b3 hwf (fun _ h ↦ nomatch h) hm fun st hm' hpc ↦ ?_
  obtain ⟨hF', hc, hout⟩ := low4_counter r hpre h (k := 538) (o := 15644) (by decide) (by decide)
    hm' hwf rfl (by decide) (by decide) (by decide)
  have hreg := keepsRegs_regs (rs := wsRegs) hm hm' (by decide)
  obtain ⟨hbx, hkey⟩ := wsRegs_keep hreg h
  refine .done _ ⟨hpc, ⟨hF', ?_, ?_, hbx, hkey⟩, (hm'.regs .rax _ rfl).trans rfl⟩
  · exact fact_keep r hpre h.2.1 hout (length_msg r) (by left; decide) (by decide) (by decide)
  · refine BytesAt.append (fact_keep r hpre h.2.2.1 hout (length_wb _ _ _) (by left; decide)
      (by decide) (by decide)) ?_
    rw [length_wb, off_add]
    exact hc

end

end NativeRustcX64.SphincsVerifyProof.Parse
