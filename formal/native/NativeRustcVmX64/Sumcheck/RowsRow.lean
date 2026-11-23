module

public import NativeRustcVmX64.Sumcheck.RowsRow.Exec
public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Spec.Sumcheck
public import NativeRustcVmX64.Code.Vm.RowsRow.Names

/-!
# `Rows::row` on x86-64

One block: the slice from word `start = 193 j + 1` of the openings, `width` words, when it fits
in them (no carry, `start + width ≤ len`: `condS`), else the empty slice. For `j` below the count
of rows `RowsAt` describes it fits: the row's words.
-/

namespace NativeRustcVmX64.Sumcheck.RowsRow

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.RowsRow NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck
open NativeVm LeanVM.Protocol.Compile NativeRustcVm.Sumcheck NativeRustcVm.Transcript

public section

section
variable [Labels]

/-- **The row fits**: the end below the slice's length, no carry: CL is zero. -/
theorem condS_eval (env : Env) (h1 : CmpOp.apply .ult .W64 (endS.eval env) (env.load 1 8 8) = true)
    (h2 : CmpOp.apply .addC .W64 (env.load 1 24 8) (startS.eval env) = false) :
    condS.eval env = true := by
  simp only [condS, clS, aboveS, SBool.eval, Sym.eval, h1, h2]
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, CmpOp.apply,
    BinOp.apply, low8_merge, low_ext]
  decide

end

variable [Host] {k : Nat}

/-- **`Rows::row`'s contract.** -/
theorem rowsRow_spec (hp : Placed code k) (p : BitVec 64) (rows : Array (Array UInt64)) :
    Spec (Labels.label NativeRustcVmX64.Vm.RowsRow.entryLabel) (RowsRowPre p rows) (RowsRowPost p rows) := by
  rintro m ⟨hst, ⟨hp0, hsz, w, hw, hhdr, hrow⟩, hnw, hap⟩
  set r := reg m .rdi with hr
  have hfnw := frame_noWrap (m0 := m) (F := 0) hst le_rfl
  have hmap : NativeRustcVm.Mapped m.dmem r 32 := hhdr.mapped
  have hwf := frame_wf (m0 := m) (d := m) (F := 0) (rest := [(r, 32)]) (vars := fun _ ↦ 0)
    (ret := 0) ⟨frame_mapped hst le_rfl, hfnw⟩
    (fun x hx ↦ by rw [List.mem_singleton] at hx; subst hx; exact ⟨hmap, hnw⟩)
    (List.pairwise_pair.mpr (Apart.symm' hap))
  have hm : Match (frameEnv m m 0 [(r, 32)]) entryS m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial
  rw [show Labels.label NativeRustcVmX64.Vm.RowsRow.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.RowsRow.b0Offset) from hp.label NativeRustcVmX64.Vm.RowsRow.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf nofun hm
    fun st hm' hpc ↦ ?_
  obtain ⟨hrax, hrdx, hrsp, hmem, hkeep⟩ := ok_b0
  simp only [PcOk, Sym.eval] at hpc
  refine .done _ ⟨hpc.trans (Frame.entry.load_ret hst le_rfl),
    (hm'.regs .rsp _ hrsp).trans ((eval_ptr0 8).trans (frame_add 0 8)), fun hj ↦ ?_,
    hm'.dmem_eq hwf hmem, Match.saved hm hm' hwf rfl hkeep⟩
  obtain ⟨hlen, hrj⟩ := hrow _ hj
  set env := frameEnv m m 0 [(r, 32)] (fun _ ↦ 0) 0 with henv
  have hws := wordsAt_iff.mp hhdr
  have hl0 : env.load 1 0 8 = p := load_ofMachine (o := 0) rfl (hws 0 (by simp))
  have hl1 : env.load 1 8 8 = BitVec.ofNat 64 openingsWords :=
    load_ofMachine (o := 8) rfl (hws 1 (by simp))
  have hl3 : env.load 1 24 8 = BitVec.ofNat 64 w := load_ofMachine (o := 24) rfl (hws 3 (by simp))
  set j := (reg m .rsi).toNat with hjdef
  have hq : wireMaxQueries = 256 := rfl
  have hl : wireMaxLeafWords = 64 := rfl
  have ho : openingWords = 193 := rfl
  have hos : openingsWords = 49408 := rfl
  have hj256 : j < 256 := by omega
  have hrsi : env.regs .rsi = reg m .rsi := rfl
  have hb : (2 : Nat) ^ Width.W64.bits = 2 ^ 64 := rfl
  have hstart : (startS.eval env).toNat = 193 * j + 1 := by
    simp only [startS, mS, Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add,
      BitVec.toNat_mul, BitVec.toNat_ofNat, hrsi]
    omega
  have hend : (endS.eval env).toNat = w + (193 * j + 1) := by
    simp only [endS, Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, hl3,
      BitVec.toNat_ofNat]
    rw [show Sym.eval env startS = startS.eval env from rfl, hstart]
    omega
  have hc : condS.eval env = true := by
    refine condS_eval env ?_ ?_
    · simp only [CmpOp.apply, low_W64, BitVec.ult, hl1, hend, BitVec.toNat_ofNat,
        decide_eq_true_eq, hos, hb]
      omega
    · simp only [CmpOp.apply, low_W64, BitVec.unsigned, BitVec.toNat_add, hl3, hstart,
        BitVec.toNat_ofNat, bne_eq_false_iff_eq, hb]
      push_cast
      omega
  have hax := hm'.regs .rax _ hrax
  have hdx := hm'.regs .rdx _ hrdx
  simp only [Sym.eval, hc, ite_true] at hax hdx
  have hx0 : reg st.data .rax = off p (8 * (1 + j * openingWords)) := by
    refine hax.trans ?_
    apply BitVec.eq_of_toNat_eq
    simp only [raxS, mS, Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add,
      BitVec.toNat_mul, BitVec.toNat_ofNat, hrsi, hl0, off, ho]
    omega
  refine ⟨?_, hx0, ?_⟩
  · rw [show reg st.data .rdx = _ from hdx, hl3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      hlen]
  · rw [hx0, hm'.dmem_eq hwf hmem]
    exact hrj

end

end NativeRustcVmX64.Sumcheck.RowsRow
