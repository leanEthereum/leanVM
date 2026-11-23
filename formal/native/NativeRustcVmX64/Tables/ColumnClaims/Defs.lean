module

public import NativeRustcVmX64.Tables.ColumnClaims.Exec
public import NativeRustcVmX64.Spec.Tables
public import NativeRustcVm.Tables.Columns
public import NativeRustcVm.Tables.Same

/-!
# `table_column_claims`'s states (x86-64)

From the entry `m0` (the evaluations at RDI, the claims at RSI): table `t`'s values' count
(`cnt`) and point's length (`plen`), its values' address (`valAddr`), its point's (`ptAddr`), its
first column (`base`). `LoopAt R t j`: table `t`'s loop head with `j` values pushed, the claims
`cs` then the tables' claims before and table `t`'s first `j` (`pre`). `Goal`: the contract
reached.
-/

namespace NativeRustcVmX64.Tables.ColumnClaims

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Arrays
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap Same)
open NativeRustcVm (wordOf ewOf ewsOf)

@[expose] public section

/-- The stack. -/
abbrev N : Nat := tableColumnClaimsStack

/-- Table `t`'s entry. -/
def ent (ev : Array (Array EW × Array EW)) (t : Nat) : Array EW × Array EW := ev.getD t (#[], #[])
/-- Table `t`'s values' count. -/
def cnt (ev : Array (Array EW × Array EW)) (t : Nat) : Nat := (ent ev t).2.size
/-- Table `t`'s point's length. -/
def plen (ev : Array (Array EW × Array EW)) (t : Nat) : Nat := (ent ev t).1.size
/-- Table `t`'s first column. -/
def base (t : Nat) : Nat := globalColumnBasesW.getD t 0

/-- Table `t`'s values' address. -/
def valAddr (m0 : MachineData) (t : Nat) : BitVec 64 := reg m0 .rdi + BitVec.ofNat 64 (1968 * t + 496)
/-- Table `t`'s point's address. -/
def ptAddr (m0 : MachineData) (t : Nat) : BitVec 64 := reg m0 .rdi + BitVec.ofNat 64 (1968 * t + 8)

/-- The frame's word at `o`. -/
def fw (m0 st : MachineData) (o : Nat) : BitVec 64 :=
  (wordOf st.dmem (stackBelow m0 64 + BitVec.ofNat 64 o)).toBitVec

/-- A body. -/
abbrev Bd (m0 st : MachineData) : Prop := Body m0 64 N slots (reg m0 .rsi) claimsBytes st

/-- **Table `t`'s loop head**, `j` of its values pushed. -/
structure LoopAt (ev : Array (Array EW × Array EW)) (cs : Array ColumnClaimW) (m0 : MachineData)
    (R : Regs) (t j : Nat) (st : MachineData) : Prop where
  body : Bd m0 st
  ev8 : fw m0 st 8 = reg m0 .rdi
  rbx : reg st .rbx = reg m0 .rsi
  le : j ≤ cnt ev t
  a : reg st R.a = valAddr m0 t + BitVec.ofNat 64 (16 * j)
  n : reg st R.n = BitVec.ofNat 64 (16 * (cnt ev t - j))
  p : reg st R.p = ptAddr m0 t
  l : reg st R.l = BitVec.ofNat 64 (plen ev t)
  c : reg st R.c = BitVec.ofNat 64 (base t - 1 + j)
  claims : ClaimsWAt st.dmem (reg m0 .rsi) (cs ++ (pre ev t j).toArray)

/-- The contract, reached. -/
abbrev Goal [Labels] (ev : Array (Array EW × Array EW)) (cs : Array ColumnClaimW) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ TableColumnClaimsPost ev cs m0 st.data

/-- The claims fit. -/
abbrev Fits (ev : Array (Array EW × Array EW)) (cs : Array ColumnClaimW) : Prop :=
  cs.size + (tableColumnClaims ev).size ≤ claimCap

end

public section

theorem evB_eq : tableEvalsBytes = 11808 := rfl
theorem N_eq : N = 120 := rfl
theorem pushClaimStack_eq : NativeRustcVmX64.pushClaimStack = 56 := rfl

theorem base_ge {t : Nat} (ht : t < 6) : 5 ≤ base t := by
  unfold base; rw [bases_eq]
  match t, ht with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide

theorem base_lt {t : Nat} : base t < 100 := by
  unfold base; rw [bases_eq]
  match t with | 0 | 1 | 2 | 3 | 4 | 5 => decide | _ + 6 => simp [Array.getD]

/-! ## The evaluations -/

variable {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW} {m0 : MachineData}

theorem pre_parts (h : TableColumnClaimsPre ev cs m0) :
    StackOk m0 N ∧ ReadIn m0 (reg m0 .rdi) tableEvalsBytes N [⟨reg m0 .rsi, claimsBytes⟩] ∧
      TableEvalsAt m0.dmem (reg m0 .rdi) ev ∧ Readable m0 (reg m0 .rsi) claimsBytes ∧
      OffStack m0 (reg m0 .rsi) claimsBytes N ∧ ClaimsWAt m0.dmem (reg m0 .rsi) cs := h

theorem size_ev (h : TableColumnClaimsPre ev cs m0) : ev.size = 6 := (pre_parts h).2.2.1.1

theorem ent_eq (h : TableColumnClaimsPre ev cs m0) {t : Nat} (ht : t < 6) :
    ent ev t = ev[t]'(by rw [size_ev h]; exact ht) := by
  simp [ent, Array.getD, size_ev h, ht]

/-- Table `t`'s entry in memory. -/
theorem tableAt (h : TableColumnClaimsPre ev cs m0) {t : Nat} (ht : t < 6) :
    TableEvalAt m0.dmem (reg m0 .rdi + BitVec.ofNat 64 (tableEvalBytes * t)) (ent ev t) := by
  rw [ent_eq h ht]
  exact (pre_parts h).2.2.1.2 t (by rw [size_ev h]; exact ht)

theorem plen_le (h : TableColumnClaimsPre ev cs m0) {t : Nat} (ht : t < 6) : plen ev t ≤ 30 :=
  (tableAt h ht).1.1

theorem cnt_le (h : TableColumnClaimsPre ev cs m0) {t : Nat} (ht : t < 6) : cnt ev t ≤ 92 :=
  (tableAt h ht).2.1

/-- The evaluations' bytes in a body: the entry's. -/
theorem same_ev (h : TableColumnClaimsPre ev cs m0) {st : MachineData} (hb : Bd m0 st) :
    Same m0.dmem st.dmem (reg m0 .rdi) tableEvalsBytes := by
  obtain ⟨hS, ⟨hR, hO, hW⟩, -, hCR, -, -⟩ := pre_parts h
  exact same_of_apart hb.same hS hR.2 hO (hW _ (List.mem_singleton.mpr rfl)) hCR.2

theorem addr_split (t o : Nat) :
    reg m0 .rdi + BitVec.ofNat 64 (1968 * t + o) =
      reg m0 .rdi + BitVec.ofNat 64 (tableEvalBytes * t) + BitVec.ofNat 64 o := by
  rw [addr_add]; rfl

/-- **Table `t`'s values' count word.** -/
theorem cnt_word (h : TableColumnClaimsPre ev cs m0) {d : DataMem}
    (hsd : Same m0.dmem d (reg m0 .rdi) tableEvalsBytes) {t : Nat}
    (ht : t < 6) :
    (wordOf d (reg m0 .rdi + BitVec.ofNat 64 (1968 * t + 488))).toBitVec =
      BitVec.ofNat 64 (cnt ev t) := by
  have hv := (tableAt h ht).2
  have hs := hsd.sub (o := 1968 * t + 488) (k := 8)
    (by rw [evB_eq]; omega)
  have e : reg m0 .rdi + BitVec.ofNat 64 (1968 * t + 488) = reg m0 .rdi +
      BitVec.ofNat 64 (tableEvalBytes * t) + BitVec.ofNat 64 valuesOff := by rw [addr_add]; rfl
  rw [e] at hs ⊢
  rw [NativeRustcVm.wordOf_of_wordAt (NativeRustcVm.Layout.WordAt.of_same hv.2.1 hs le_rfl)]
  simp only [cnt, Array.length_toList]; rfl

/-- **Table `t`'s point's length word.** -/
theorem plen_word (h : TableColumnClaimsPre ev cs m0) {d : DataMem}
    (hsd : Same m0.dmem d (reg m0 .rdi) tableEvalsBytes) {t : Nat}
    (ht : t < 6) :
    (wordOf d (reg m0 .rdi + BitVec.ofNat 64 (1968 * t))).toBitVec =
      BitVec.ofNat 64 (plen ev t) := by
  have hv := (tableAt h ht).1
  have hs := hsd.sub (o := 1968 * t) (k := 8)
    (by rw [evB_eq]; omega)
  have e : reg m0 .rdi + BitVec.ofNat 64 (1968 * t) = reg m0 .rdi +
      BitVec.ofNat 64 (tableEvalBytes * t) := rfl
  rw [e] at hs ⊢
  rw [NativeRustcVm.wordOf_of_wordAt (NativeRustcVm.Layout.WordAt.of_same hv.2.1 hs le_rfl)]
  simp only [plen, Array.length_toList]; rfl

/-- **Table `t`'s value `j`.** -/
theorem val_eq (h : TableColumnClaimsPre ev cs m0) {d : DataMem}
    (hsd : Same m0.dmem d (reg m0 .rdi) tableEvalsBytes) {t j : Nat}
    (ht : t < 6) (hj : j < cnt ev t) :
    ewOf d (valAddr m0 t + BitVec.ofNat 64 (16 * j)) = (ent ev t).2[j]'hj := by
  have hv := (tableAt h ht).2.2.2
  have hj' : j < (ent ev t).2.toList.length := by simpa [cnt] using hj
  have he := NativeRustcVm.EWsAt.getElem hv hj'
  have hs := hsd.sub (o := 1968 * t + 496 + 16 * j) (k := 16)
    (by have := cnt_le h ht; rw [evB_eq]; omega)
  have e1 : reg m0 .rdi + BitVec.ofNat 64 (tableEvalBytes * t) + BitVec.ofNat 64 valuesOff + 8#64 +
      BitVec.ofNat 64 (16 * j) = reg m0 .rdi + BitVec.ofNat 64 (1968 * t + 496 + 16 * j) := by
    rw [show (8#64) = BitVec.ofNat 64 8 from rfl, addr_add, addr_add, addr_add]
    exact congrArg (reg m0 .rdi + BitVec.ofNat 64 ·) (by unfold tableEvalBytes valuesOff; omega)
  rw [e1] at he
  have := NativeRustcVm.Layout.EWAt.of_same he hs le_rfl
  rw [valAddr, addr_add, NativeRustcVm.ewOf_of_ewAt this]
  simp only [Array.getElem_toList]
  rfl

/-- **Table `t`'s point.** -/
theorem point_eq (h : TableColumnClaimsPre ev cs m0) {d : DataMem}
    (hsd : Same m0.dmem d (reg m0 .rdi) tableEvalsBytes) {t : Nat}
    (ht : t < 6) : (ewsOf d (ptAddr m0 t) (plen ev t)).toArray = (ent ev t).1 := by
  have hv := (tableAt h ht).1.2.2
  have hs := hsd.sub (o := 1968 * t + 8) (k := 16 * plen ev t)
    (by have := plen_le h ht; rw [evB_eq]; omega)
  have e1 : reg m0 .rdi + BitVec.ofNat 64 (tableEvalBytes * t) + 8#64 = ptAddr m0 t := by
    rw [show (8#64) = BitVec.ofNat 64 8 from rfl, addr_add]; rfl
  rw [e1] at hv
  have := NativeRustcVm.Tables.EWsAt.of_same hv hs (by simp [plen])
  have h2 := NativeRustcVm.ewsOf_of_ewsAt this
  simp only [Array.length_toList] at h2
  rw [show plen ev t = (ent ev t).1.size from rfl, h2]

end

end NativeRustcVmX64.Tables.ColumnClaims
