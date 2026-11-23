module

public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Start

/-!
# `each_row` with `final_level`'s closure: inside an iteration (x86-64)

`MidM rows m0 j q d`: the memory of iteration `j`: the locals (`Low`), `j` at 64, query `q` at 72;
kept by a step changing memory in `Hit … lo hi` for `48 ≤ lo` and `hi ≤ 1384` apart from 64 to 80
(`MidM.keep`). The inputs read back: query `j` (`query_word`), the rows (`rowsAt_of_fr`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfFinalLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfFinalLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)
open LeanVM.Protocol.Compile (wireMaxQueries wireMaxLeafWords)
open NativeVm (openingWords)

@[expose] public section

/-- **The memory of an iteration.** -/
structure MidM (m0 : MachineData) (j : Nat) (q : UInt64) (d : DataMem) : Prop where
  low : Low m0 d
  w64 : WordAt d (fb m0 + BitVec.ofNat 64 64) (UInt64.ofBitVec (BitVec.ofNat 64 j))
  w72 : WordAt d (fb m0 + BitVec.ofNat 64 72) q

/-- The registers the lanes' clearing keeps. -/
def keepL : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsi, .rsp]

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat} {q : UInt64}

theorem MidM.keep {lo hi : Nat} {d d' : DataMem} (hl : EachRow.Lay m0 1936 24 eachRowFinalStack)
    (hlh : lo ≤ hi) (hhi : hi ≤ 1384) (hlo : 48 ≤ lo) (h80 : 80 ≤ lo ∨ hi ≤ 64)
    (h : MidM m0 j q d) (hs : SameOutside d d' (EachRow.Hit m0 1936 eachRowFinalStack lo hi)) :
    MidM m0 j q d' :=
  ⟨h.low.keep hl hlh hhi hlo hs, keepW hl hlh (by omega) hs (by decide) (by omega) h.w64,
    keepW hl hlh (by omega) hs (by decide) (by omega) h.w72⟩

/-- The queries' count. -/
theorem qs_size : (qsOf m0).size = (reg m0 .rdx).toNat := size_wordSlice _ _ _

/-- Query `j`, as the entry's memory holds it. -/
theorem query_word [Labels] (hpre : EachRowFinalPre rows op m0) {o : Nat} {m : MachineData}
    (hfr : FR m0 o m) (hj : j < (qsOf m0).size) :
    NativeRustcVm.wordOf m.dmem (reg m0 .rsi + BitVec.ofNat 64 (8 * j)) = (qsOf m0)[j]'hj := by
  have hsz := qs_size (m0 := m0)
  have hs := hfr.input_same (lay hpre) hpre.1.2.2.2.2.2.1 fun _ _ h ↦ h
  rw [NativeRustcVm.wordOf_congr (d := m0.dmem) fun i hi ↦ by
    rw [NativeRustcVm.addr_add_add]; exact hs _ (by omega)]
  simp [qsOf, eachRowArgs, wordSlice]

/-- **The rows**, unchanged in a body. -/
theorem rowsAt_of_fr [Labels] (hpre : EachRowFinalPre rows op m0) {o : Nat} {m : MachineData}
    (hfr : FR m0 o m) : NativeRustcVm.Sumcheck.RowsAt m.dmem (reg m0 .rcx) op rows := by
  obtain ⟨hp0, hsz, w, hw, hhdr, hrow⟩ := hpre.1.2.2.1
  have hr := hfr.input_same (lay hpre) hpre.1.2.2.2.1 fun _ _ h ↦ h
  have ho := hfr.input_same (lay hpre) hpre.1.2.2.2.2.1 fun _ _ h ↦ h
  refine ⟨hp0, hsz, w, hw, NativeRustcVm.Transcript.bytesAt_congr hhdr fun i hi ↦ hr i ?_,
    fun j hj ↦ ⟨(hrow j hj).1, NativeRustcVm.Transcript.bytesAt_congr (hrow j hj).2 fun i hi ↦ ?_⟩⟩
  · rw [NativeRustcVm.length_wordsBytes] at hi
    simpa using hi
  · rw [off, NativeRustcVm.addr_add_add]
    refine ho _ ?_
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList, (hrow j hj).1] at hi
    have : wireMaxQueries = 256 := rfl
    have : wireMaxLeafWords = 64 := rfl
    have : openingWords = 193 := rfl
    have : NativeRustcVm.Sumcheck.openingsWords = 49408 := rfl
    have hj' : j < 256 := by omega
    show _ < 8 * 49408
    have : j * openingWords ≤ 255 * 193 := by
      rw [show openingWords = 193 from rfl]; exact Nat.mul_le_mul_right _ (by omega)
    omega

/-- The queries' bytes, as numbers: they do not wrap, and end below the stack or start above
RSP. -/
theorem qs_bound [Labels] (hpre : EachRowFinalPre rows op m0) :
    (reg m0 .rsi).toNat + 8 * (qsOf m0).size ≤ 2 ^ 64 ∧
      ((reg m0 .rsi).toNat + 8 * (qsOf m0).size ≤ (rspOf m0).toNat - eachRowFinalStack ∨
        (rspOf m0).toNat + 8 ≤ (reg m0 .rsi).toNat) := by
  have hq := hpre.1.2.2.2.2.2.1
  have hl := lay hpre
  have hsb := hl.baseN
  have hN := hl.sp
  rw [qs_size]
  refine ⟨hq.1.2, ?_⟩
  have := hq.2
  unfold OffStack Apart at this
  rw [hsb] at this
  omega

end

end NativeRustcVmX64.Whir.EachRowOfFinalLevel
