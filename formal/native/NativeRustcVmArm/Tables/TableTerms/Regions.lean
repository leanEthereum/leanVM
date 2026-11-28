module

public import NativeRustcVmArm.Tables.TableTerms.Lemmas

/-!
# `table_terms`: the regions of table `i`

Sub-ranges of inputs and outputs (`apart_sub`, `rin_sub`, `outOk_sub`), and for table `i`: its
`TABLES` entry (`tab_rin`, its words `tw_get`), its evaluations' entry (`evi_out`), its three
forms (`form_rin`), its weight (`w_rin`), its height (`h_rin`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout
open NativeRustcVm (wordOf ewsOf)

@[expose] public section

/-- The regions the function writes, as `ReadIn` lists them. -/
def wsL (m0 : MachineData) : List NativeRustcVm.Region :=
  [⟨m0.regs.X0.toBitVec, 24⟩, ⟨m0.regs.X1.toBitVec, tstateBytes⟩, ⟨ev m0, tableEvalsBytes⟩]

end

public section

theorem apart_sub {a b : BitVec 64} {n m o k : Nat} (h : Apart a n b m) (hnw : NoWrap a n)
    (hk : o + k ≤ n) : Apart (a + BitVec.ofNat 64 o) k b m := by
  have := NativeRustcVm.toNat_add_ofNat_le (a := a) (i := o) (by unfold NoWrap at hnw; omega)
  unfold NoWrap at hnw
  unfold Apart at h ⊢
  omega

theorem rin_sub {m : MachineData} {x : BitVec 64} {n N o k : Nat} {ws : List NativeRustcVm.Region}
    (h : ReadIn m x n N ws) (hk : o + k ≤ n) : ReadIn m (x + BitVec.ofNat 64 o) k N ws :=
  ⟨⟨NativeRustcVm.Mapped.sub h.1.1 hk, NativeRustcVm.NoWrap.sub h.1.2 hk⟩, apart_sub h.2.1 h.1.2 hk,
    fun w hw ↦ apart_sub (h.2.2 w hw) h.1.2 hk⟩

theorem outOk_sub [Labels] {m : MachineData} {t : BitVec 64} {a : DecArea} {x : BitVec 64}
    {n N o k : Nat} (h : OutOk m t a x n N) (hk : o + k ≤ n) :
    OutOk m t a (x + BitVec.ofNat 64 o) k N :=
  ⟨NativeRustcVm.Mapped.sub h.1 hk, NativeRustcVm.NoWrap.sub h.2.1 hk, apart_sub h.2.2.1 h.2.1 hk,
    apart_sub h.2.2.2.1 h.2.1 hk, apart_sub h.2.2.2.2.1 h.2.1 hk,
    apart_sub h.2.2.2.2.2 h.2.1 hk⟩

section
variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

/-- `TABLES`, read only. -/
theorem tables_rin (h : TableTermsPre a s heights forms m0) : ReadIn m0 T 240 N (wsL m0) := by
  obtain ⟨hb, hnw, hap⟩ := Pre.tables h .tables
  rw [tables_length] at hnw hap
  refine ⟨⟨fun i hi ↦ hb.mapped i (by rw [tables_length]; exact hi), hnw⟩, hap, fun w hw ↦ ?_⟩
  simp only [wsL, List.mem_cons, List.not_mem_nil, or_false] at hw
  have e := tables_length
  rcases hw with rfl | rfl | rfl
  · have := Pre.ro h .tables; rw [e] at this; exact this.symm
  · have := Pre.rt h .tables; rw [e] at this; exact this.symm
  · have := Pre.re h .tables; rw [e] at this; exact this.symm

/-- Table `i`'s `TABLES` entry. -/
theorem tab_rin (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) :
    ReadIn m0 (T + BitVec.ofNat 64 (40 * i)) 40 N (wsL m0) :=
  rin_sub (tables_rin h) (by omega)

/-- **Word `o` of table `i`'s entry** in a state of the frame. -/
theorem tw_get (h : TableTermsPre a s heights forms m0) {m : MachineData}
    (hfr : Fr m0 288 N slots [] (outs m0) m) {i o : Nat} (hi : i < 6) (ho : o < 5) :
    wordOf m.dmem (T + BitVec.ofNat 64 (40 * i) + BitVec.ofNat 64 (8 * o)) =
      tablesWords.getD (5 * i + o) 0 := by
  rw [NativeRustcVm.addr_add_add, show 40 * i + 8 * o = 8 * (5 * i + o) by omega]
  exact tword h hfr (by omega)

/-- Entry `i` of the evaluations. -/
theorem evi_out (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) :
    OutOk m0 m0.regs.X1.toBitVec a (evi m0 i) 1968 N :=
  outOk_sub (Pre.evs h) (by unfold tableEvalsBytes nTables tableEvalBytes; omega)

/-- Table `i`'s three forms. -/
theorem form_rin (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) :
    ReadIn m0 (m0.regs.X7.toBitVec + BitVec.ofNat 64 (17784 * i)) 17784 N (wsL m0) :=
  rin_sub (Pre.fs h) (by simp only [NativeRustcVm.Bus.formsBytes, formBufBytes_eq, nTables]; omega)

/-- Table `i`'s weight. -/
theorem w_rin (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) :
    ReadIn m0 (wp m0 + BitVec.ofNat 64 (16 * i)) 16 N (wsL m0) :=
  rin_sub (Pre.ws h) (by omega)

/-- Table `i`'s height. -/
theorem h_rin (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) :
    ReadIn m0 (m0.regs.X6.toBitVec + BitVec.ofNat 64 (8 * i)) 8 N (wsL m0) :=
  rin_sub (Pre.hs h) (by omega)

end

end

end NativeRustcVmArm.Tables.TableTerms
