module

public import NativeRustcVmX64.Tables.TableTerms.Cons
public import NativeRustcVmX64.Code.Vm.Evaluate.Names

/-!
# `table_terms`: the forms' dot product (x86-64)

A call changing only its stack (`pure_call`); `evaluate` of table `i`'s form `j` on the
evaluations (`eval_call`). `b6` to `b8` save the previous result and evaluate the table's three
forms; `b9` saves the last, loads the table's weight into the frame and calls `dot` of the form
powers with the three values: `dotF` in RAX, RDX (`forms_step`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf ewOf)

public section

theorem addr_sub (x : BitVec 64) {a c : Nat} (h : c ≤ a) (hc : c ≤ 2 ^ 64) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 (2 ^ 64 - c) = x + BitVec.ofNat 64 (a - c) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem inR00 {q : BitVec 64} (hq : NativeRustcVm.InRange 0 0 q) : False := by
  unfold NativeRustcVm.InRange at hq; omega

section
variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

/-- **A call changing only its stack.** -/
theorem pure_call (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6)
    {o : Array (Array EW × Array EW)} {xs : Array EW} {s' : TState} {d d' : MachineData}
    (hb : Bd m0 272 N slots (outs m0) 0 d) {Nc : Nat} (hle : 272 + Nc ≤ N) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64)
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ NativeRustcVm.InRange 0 0 q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    {L : List (Nat × UInt64)} (hL : ∀ p ∈ L, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280) (hfw : FW m0 d L)
    (H : It a m0 i o xs s' d) :
    Bd m0 272 N slots (outs m0) 8 d' ∧ FW m0 d' L ∧ It a m0 i o xs s' d' :=
  ⟨call_bd h hb hle hs hrsp hso fun _ hq ↦ (inR00 hq).elim,
    fw_callO h hb hle hso (fun _ hq ↦ (inR00 hq).elim) hL hfw,
    it_call h hi H hb hle hs hso fun _ hq ↦ (inR00 hq).elim⟩

/-- Table `i`'s form `j`: its `FormBuf` in a body. -/
theorem form_at (h : TableTermsPre a s heights forms m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) o d) {i j : Nat} (hi : i < forms.size)
    (hj : j < forms[i].size) :
    FormBufAt d.dmem (off (fA m0) (formBufBytes * (3 * i + j))) forms[i][j] :=
  FormBufAt.of_same ((Pre.fms h).forms i hi j hj) ((same_readIn h hb (Pre.fs h)).sub (by
    have h1 := (Pre.fms h).size
    have h2 := (Pre.fms h).row_size i hi
    unfold formsBytes formBufBytes termBytes formCap nTables at *
    omega))

theorem forms_size (h : TableTermsPre a s heights forms m0) : forms.size = 6 := (Pre.fms h).size

theorem forms_row (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < forms.size) :
    forms[i].size = 3 := (Pre.fms h).row_size i hi

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **`evaluate` of table `i`'s form `j`** on the evaluations `xs`. -/
theorem eval_call (h : TableTermsPre a s heights forms m0)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmX64.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    {i j : Nat} (hi : i < 6) (hj : j < 3) {o : Array (Array EW × Array EW)} {xs : Array EW}
    {s' : TState} {st : MachineState} {next : Int64}
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.Evaluate.entryLabel ∧ retOf st.data = next)
    (hb : Bd m0 272 N slots (outs m0) 0 st.data) (H : It a m0 i o xs s' st.data)
    (hxs : xs.size = (tb i).width)
    (hrdi : reg st.data .rdi = off (fA m0) (formBufBytes * (3 * i + j)) + BitVec.ofNat 64 8)
    {f : FormW} (hF : FormBufAt st.data.dmem (off (fA m0) (formBufBytes * (3 * i + j))) f)
    (hrsi : (reg st.data .rsi).toNat = f.size)
    (hrdx : reg st.data .rdx = evi m0 i + BitVec.ofNat 64 496)
    (hrcx : reg st.data .rcx = BitVec.ofNat 64 (tb i).width)
    {L : List (Nat × UInt64)} (hL : ∀ p ∈ L, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280) (hfw : FW m0 st.data L)
    {R : MachineState → Prop}
    (cont : ∀ d', Bd m0 272 N slots (outs m0) 8 d' → FW m0 d' L → It a m0 i o xs s' d' →
      ewRet d' = f.evaluate xs →
      (∀ r, calleeSaved r = true → reg d' r = reg st.data r) →
      Eventually (step1 Host.exe) R ⟨d', next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := Pre.stack h
  have hle : 272 + evaluateStack ≤ N := by rw [N_eq]; decide
  have hfr := form_rin h hi
  have hfl := hF.len_le
  unfold formCap at hfl
  have hsub : 17784 * i + (formBufBytes * j + 8) + termBytes * f.size ≤ formsBytes := by
    unfold formsBytes formBufBytes termBytes formCap nTables at *; omega
  have e8 : off (fA m0) (formBufBytes * (3 * i + j)) + BitVec.ofNat 64 8 =
      fA m0 + BitVec.ofNat 64 (17784 * i + (formBufBytes * j + 8)) := by
    unfold off
    rw [NativeRustcVm.addr_add_add]
    congr 2
    unfold formBufBytes termBytes formCap; ring
  have hterm := rin_sub (Pre.fs h) hsub
  have hwl := width_le hi
  have eo := evi_out h hi
  have hsubv : 496 + 16 * (tb i).width ≤ 1968 := by omega
  have hpre : EvaluatePre f st.data := by
    unfold EvaluatePre SliceOk
    rw [hrdi, hrsi, hrdx, hrcx, toNat_ofNat_lt (by omega)]
    refine ⟨hb.stackOk_at hS (Nat.zero_le _) (by simpa using hle), rfl, ?_, ?_, ?_⟩
    · have := hF.terms
      rwa [show off (off (fA m0) (formBufBytes * (3 * i + j))) 8 =
        off (fA m0) (formBufBytes * (3 * i + j)) + BitVec.ofNat 64 8 from rfl] at this
    · rw [e8]
      exact (rd_callee h hb hle hterm.1.1 hterm.1.2 hterm.2.1).1
    · rw [e8]
      exact ⟨(rd_callee h hb hle hterm.1.1 hterm.1.2 hterm.2.1).2, rd_callee h hb hle (NativeRustcVm.Mapped.sub eo.1 hsubv)
        (NativeRustcVm.NoWrap.sub eo.2.1 hsubv) (apart_sub eo.2.1 eo.2.2.2.2.1 hsubv)⟩
  refine call_then (env := Env.ofMachine st.data []) ⟨hpc.1, hpc.2⟩ (hev _) hpre
    fun st' hpc' hrsp hq ↦ ?_
  obtain ⟨q0, q1, q2⟩ := hq
  have hsl : slice st.data (reg st.data .rdx) (reg st.data .rcx) = xs := by
    unfold slice
    rw [hrdx, hrcx, toNat_ofNat_lt (by omega)]
    have e := H.vals.2.2
    rw [show evi m0 i + BitVec.ofNat 64 488 + 8#64 = evi m0 i + BitVec.ofNat 64 496 from
      NativeRustcVm.addr_add_add _ 488 8] at e
    have := NativeRustcVm.ewsOf_of_ewsAt e
    rw [Array.length_toList, hxs] at this
    rw [this, Array.toArray_toList]
  rw [hsl] at q0
  obtain ⟨hb', fw', it'⟩ := pure_call h hi hb hle q2 hrsp q1 hL hfw H
  exact at_pc hpc' (cont st'.data hb' fw' it' q0 q2.1)

end

end NativeRustcVmX64.Tables.TableTerms
