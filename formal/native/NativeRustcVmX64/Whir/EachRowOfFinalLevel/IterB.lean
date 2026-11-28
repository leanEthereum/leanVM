module

public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.IterA
public import NativeRustcVmX64.Code.Vm.LanesOf.Names
public import NativeRustcVmX64.Code.Vm.RowsRow.Names

/-!
# `each_row` with `final_level`'s closure: a row's lanes (x86-64)

At `b8` (`AtB8`): `b8` stores `j` at 64 and calls `Rows::row(j)`; `b9` calls `lanes_of` on the
row into the lanes at 104; `b10` checks its `Some`: at `b11` (`AtB11`, `iter_b`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfFinalLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfFinalLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)
open LeanVM.Protocol.Compile (wireMaxQueries wireMaxLeafWords)
open NativeVm (openingWords)

@[expose] public section

/-- Row `j`'s lanes. -/
abbrev lanesJ (m0 : MachineData) (row : Array UInt64) : Array EW :=
  lanesOf (reg m0 .rdi).toNat row

/-- **At `b11`**, in iteration `j`, the row's lanes at 104. -/
structure AtB11 (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 8 m
  hj : j < rows.size
  hjq : j < (qsOf m0).size
  mm : MidM m0 j ((qsOf m0)[j]'hjq) m.dmem
  ok : ∀ i (h1 : i < (qsOf m0).size) (h2 : i < rows.size), i < j →
    okOf m0 (qsOf m0)[i] rows[i] = true
  lanes : EWsAt m.dmem (fb m0 + BitVec.ofNat 64 104) (lanesJ m0 (rows[j]'hj)).toList
  lsize : (lanesJ m0 (rows[j]'hj)).size ≤ 64
  rdx : (reg m .rdx).toNat = (lanesJ m0 (rows[j]'hj)).size
  rbp : reg m .rbp = reg m0 .rsi + BitVec.ofNat 64 (8 * j)
  r13 : reg m .r13 = BitVec.ofNat 64 (rows.size - (j + 1))
  r14 : reg m .r14 = reg m0 .rcx
  r12 : reg m .r12 = BitVec.ofNat 64 (tableOf m0).size
  r15 : reg m .r15 = fb m0 + BitVec.ofNat 64 1392
  rbx : reg m .rbx = fb m0 + BitVec.ofNat 64 104

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

/-- Row `j`'s place in the openings. -/
theorem row_bound [Labels] (hpre : EachRowFinalPre rows op m0) (hj : j < rows.size) :
    8 * (1 + j * openingWords) + 8 * (rows[j]'hj).size ≤ 8 * NativeRustcVm.Sumcheck.openingsWords := by
  obtain ⟨-, hsz, w, hw, -, hrow⟩ := hpre.1.2.2.1
  rw [(hrow j hj).1]
  have : wireMaxQueries = 256 := rfl
  have : wireMaxLeafWords = 64 := rfl
  have : NativeRustcVm.Sumcheck.openingsWords = 49408 := rfl
  have : j * openingWords ≤ 255 * 193 := by
    rw [show openingWords = 193 from rfl]; exact Nat.mul_le_mul_right _ (by omega)
  omega

variable [Host] {k : Nat}

/-- **A row's lanes**: from `b8` to `b11`. -/
theorem iter_b (hp : Placed code k)
    (hrow : Spec (label NativeRustcVmX64.Vm.RowsRow.entryLabel) (RowsRowPre op rows) (RowsRowPost op rows))
    (hlanes : Spec (label NativeRustcVmX64.Vm.LanesOf.entryLabel) LanesOfPre LanesOfPost)
    (hpre : EachRowFinalPre rows op m0) {m : MachineData} (h : AtB8 rows m0 j m)
    (cont : ∀ m', AtB11 rows m0 j m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b11Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b8Offset)⟩ := by
  have hl := lay hpre
  have hsp := hl.sp
  have htop := hl.ok.2.1
  have hstk : eachRowFinalStack = 3088 := rfl
  have hrs : rows.size ≤ 256 := hpre.1.2.2.1.2.1
  have hjr := h.hj
  have hrin := hpre.1.2.2.2.1
  have hOW : NativeRustcVm.Sumcheck.openingsWords = 49408 := rfl
  have hjo : j * openingWords ≤ 255 * 193 := by
    rw [show openingWords = 193 from rfl]; exact Nat.mul_le_mul_right _ (by omega)
  have hopin := hpre.1.2.2.2.2.1
  -- `b8`: `Rows::row(j)`
  obtain ⟨hwf, hm⟩ := frame_env hpre h.fr (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b8Offset + b8.length)).toBitVec
  have hk8 : b8.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b8Offset) := b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk8 run_b8 hwf (fun _ _ ↦ rfl) hm fun st8 hm8 hpc8 ↦ ?_
  have hs8 : SameOutside m.dmem st8.data.dmem (EachRow.Hit m0 1936 eachRowFinalStack 64 72) :=
    EachRow.hit_of_block hl (by decide) (by decide) hm8 hwf (by decide)
  have hfr8 : FR m0 0 st8.data :=
    h.fr.step hl (by decide) (by decide) ((rv hm8 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
      (hm8.kept hwf) hs8 (by decide)
  have w64 : WordAt st8.data.dmem (fb m0 + BitVec.ofNat 64 64)
      (UInt64.ofBitVec (BitVec.ofNat 64 j)) := by
    have := NativeRustcVmX64.Transcript.wordAt_write hm8 (r := 0) (o := 64) rfl (by decide)
      (v := .reg .rsi) (by decide)
    rw [show (Sym.reg .rsi).eval (EachRow.envE m0 m 1936 24 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b8Offset + b8.length)).toBitVec) = _ from h.rsi] at this
    exact this
  have e8 : ∀ r, (after b8 frameS).reg r = some (.reg r) → reg st8.data r = reg m r :=
    fun r hr ↦ rv hm8 (by rw [← after_eq run_b8]; exact hr)
  have e8rdi : reg st8.data .rdi = reg m0 .rcx := (rv hm8 (v := .reg .r14) rfl).trans h.r14
  have e8rsi : (reg st8.data .rsi).toNat = j := by
    rw [e8 .rsi rfl, h.rsi, BitVec.toNat_ofNat]; omega
  have hP8 : RowsRowPre op rows st8.data := by
    unfold RowsRowPre
    rw [e8rdi]
    exact ⟨hfr8.stackOk hl (by decide), rowsAt_of_fr hpre hfr8, hrin.1.2,
      NativeRustcVmX64.Transcript.apart_callee hrin.2 hfr8.rsp0 hsp (by decide)⟩
  refine call_then hpc8 hrow hP8 fun st9 hpc9 hrsp9 hq9 ↦ ?_
  obtain ⟨hres, hd9, hsv9⟩ := hq9
  obtain ⟨hrdx9, hrax9, -⟩ := hres (by rw [e8rsi]; exact hjr)
  simp only [e8rsi] at hrdx9 hrax9
  have hfr9 : FR m0 8 st9.data :=
    EachRow.Fr.call hl (lo := 1384) (hi := 1384) le_rfl (by decide) hfr8 hrsp9 hsv9
      (fun q _ ↦ by rw [hd9]) (by decide)
  obtain ⟨d9, pc9⟩ := st9
  simp only at hpc9 hfr9 hd9 hsv9 hrdx9 hrax9
  subst hpc9
  rw [show k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b8Offset + b8.length = k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b9Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfFinalLevel.b8_next]]
  have hmm9 : MidM m0 j ((qsOf m0)[j]'h.hjq) d9.dmem := by
    rw [hd9]
    exact ⟨h.low.keep hl (by decide) (by decide) (by decide) hs8, w64,
      keepW hl (by decide) (by decide) hs8 (by decide) (by decide) h.w72⟩
  have k9 : ∀ r, calleeSaved r = true → reg d9 r = reg m r := fun r hc ↦ by
    rw [sv hsv9 r hc]
    have := hm8.regs r (.reg r) (by revert hc; cases r <;> decide)
    exact this
  -- `b9`: `lanes_of`
  obtain ⟨hwf9, hm9⟩ := frame_env hpre hfr9 (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b9Offset + b9.length)).toBitVec
  have hk9 : b9.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b9Offset) := b9_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk9 run_b9 hwf9 (fun _ _ ↦ rfl) hm9 fun st10 hm10 hpc10 ↦ ?_
  have hs10 : SameOutside d9.dmem st10.data.dmem (EachRow.Hit m0 1936 eachRowFinalStack 1384 1384) :=
    EachRow.hit_of_block hl le_rfl (by decide) hm10 hwf9 (by decide)
  have hfr10 : FR m0 0 st10.data :=
    hfr9.step hl le_rfl (by decide) ((rv hm10 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
      (hm10.kept hwf9) hs10 (by decide)
  let ra := off op (8 * (1 + j * openingWords))
  have hbound := row_bound hpre hjr
  have hopnw : op.toNat + 8 * NativeRustcVm.Sumcheck.openingsWords ≤ 2 ^ 64 := hopin.1.2
  have hra : ra.toNat = op.toNat + 8 * (1 + j * openingWords) :=
    NativeRustcVm.Transcript.toNat_off (by omega)
  have e10rdi : reg st10.data .rdi = reg m0 .rdi :=
    (rv hm10 (v := .load 0 40 8) rfl).trans (NativeRustcVmX64.Arrays.load_word hmm9.low.w40)
  have e10rsi : reg st10.data .rsi = ra := (rv hm10 (v := .reg .rax) rfl).trans hrax9
  have e10rdx : (reg st10.data .rdx).toNat = (rows[j]'hjr).size :=
    (congrArg BitVec.toNat (rv hm10 (v := .reg .rdx) rfl)).trans hrdx9
  have e10rcx : reg st10.data .rcx = fb m0 + BitVec.ofNat 64 104 :=
    (rv hm10 (v := .reg .rbx) rfl).trans ((k9 .rbx rfl).trans h.rbx)
  have hrows10 := rowsAt_of_fr hpre hfr10
  obtain ⟨-, -, w, hw64, -, hrowW⟩ := hrows10
  have hWj := (hrowW j hjr).2
  have hsb := hfr10.stackBelow_toNat hl (N' := lanesOfStack) (by decide)
  have hopst := hopin.2
  unfold OffStack Apart at hopst
  rw [hl.baseN] at hopst
  have a104 := hl.addr (o := 104) (by decide)
  have hP10 : LanesOfPre st10.data := by
    unfold LanesOfPre
    rw [e10rsi, e10rdx, e10rcx]
    refine ⟨hfr10.stackOk hl (by decide), ⟨⟨?_, show ra.toNat + _ ≤ _ by omega⟩, ?_⟩,
      hfr10.whirIn_frame hl (by decide) (by decide) (by decide), ?_⟩
    · have := NativeRustcVm.WordsAt.mapped hWj
      rwa [Array.length_toList] at this
    · show _ ∨ _
      rw [hsb, hra]
      have : lanesOfStack = 8 := rfl
      omega
    · show _ ∨ _
      rw [a104, hra]
      have : lanesBytes = 1024 := rfl
      omega
  refine call_then hpc10 hlanes hP10 fun st11 hpc11 hrsp11 hq11 ↦ ?_
  simp only [LanesOfPost] at hq11
  obtain ⟨hval, hch, hsv11⟩ := hq11
  have hws : wordSlice st10.data ra (reg st10.data .rdx).toNat = rows[j]'hjr := by
    unfold wordSlice
    rw [e10rdx]
    have := NativeRustcVm.wordsOf_of_wordsAt hWj
    rw [Array.length_toList] at this
    rw [this, Array.toArray_toList]
  rw [e10rsi, hws, e10rdi, e10rcx] at hval
  rw [e10rcx] at hch
  have hls : (lanesJ m0 (rows[j]'hjr)).size ≤ 64 := by
    have h1 : (lanesJ m0 (rows[j]'hjr)).size ≤ (rows[j]'hjr).size := EachRow.lanesOf_size_le _ _
    have h2 := (hrowW j hjr).1
    have : wireMaxLeafWords = 64 := rfl
    omega
  have hls' : (lanesJ m0 (rows[j]'hjr)).size ≤ laneCap := hls
  simp only [hls', ↓reduceIte] at hval
  obtain ⟨hax, hdx, hew⟩ := hval
  have hs11 : SameOutside st10.data.dmem st11.data.dmem
      (EachRow.Hit m0 1936 eachRowFinalStack 104 1128) :=
    EachRow.hit_of_call hl (by decide) (by decide) hfr10.rsp0 (N' := lanesOfStack) (by decide)
      le_rfl (by decide) hch
  have hfr11 : FR m0 8 st11.data :=
    EachRow.Fr.call hl (by decide) (by decide) hfr10 hrsp11 hsv11 hs11 (by decide)
  obtain ⟨d11, pc11⟩ := st11
  simp only at hpc11 hfr11 hs11 hsv11 hax hdx hew
  subst hpc11
  rw [show k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b9Offset + b9.length = k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b10Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfFinalLevel.b9_next]]
  have k11 : ∀ r, calleeSaved r = true → reg d11 r = reg m r := fun r hc ↦ by
    rw [sv hsv11 r hc]
    have := hm10.regs r (.reg r) (by revert hc; cases r <;> decide)
    exact this.trans (k9 r hc)
  -- `b10`
  obtain ⟨hwf11, hm11⟩ := frame_env hpre hfr11 0
  have hk10 : b10.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b10Offset) := b10_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk10 run_b10 hwf11 (fun _ h ↦ by cases h) hm11 fun st12 hm12 hpc12 ↦ ?_
  have hd12 : st12.data.dmem = d11.dmem := hm12.dmem_eq hwf11 rfl
  have hfr12 : FR m0 8 st12.data := hfr11.ofBlock hwf11 hm12 rfl (by decide)
  have hrax : (EachRow.envE m0 d11 1936 24 [] (fun _ ↦ 0) 0).regs .rax = 1#64 := hax
  simp only [PcOk] at hpc12
  split at hpc12
  · rename_i hc
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hrax] at hc
    exact absurd hc (by decide)
  obtain ⟨d12, pc12⟩ := st12
  simp only at hpc12 hfr12 hd12 hm12
  subst hpc12
  have e12 : ∀ r, calleeSaved r = true ∨ r = .rdx → reg d12 r = reg d11 r := fun r hr ↦
    rv hm12 (v := .reg r) (by rcases hr with hr | rfl <;> (try revert hr) <;> (try cases r) <;> decide)
  have hmm12 : MidM m0 j ((qsOf m0)[j]'h.hjq) d12.dmem := by
    rw [hd12]
    refine hmm9.keep hl (by decide) (by decide) (by decide) (by decide)
      (fun q hq ↦ (hs11 q hq).trans (hs10 q fun h' ↦ hq ?_))
    show EachRow.Hit m0 1936 eachRowFinalStack 104 1128 q
    rw [hl.hit_iff (by decide) (by decide)] at h' ⊢
    omega
  refine cont d12 ⟨hfr12, hjr, h.hjq, hmm12, h.ok, by rw [hd12]; exact hew, hls, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e12 .rdx (.inr rfl)]; exact hdx
  · rw [e12 .rbp (.inl rfl), k11 .rbp rfl]; exact h.rbp
  · rw [e12 .r13 (.inl rfl), k11 .r13 rfl]; exact h.r13
  · rw [e12 .r14 (.inl rfl), k11 .r14 rfl]; exact h.r14
  · rw [e12 .r12 (.inl rfl), k11 .r12 rfl]; exact h.r12
  · rw [e12 .r15 (.inl rfl), k11 .r15 rfl]; exact h.r15
  · rw [e12 .rbx (.inl rfl), k11 .rbx rfl]; exact h.rbx

end

end NativeRustcVmX64.Whir.EachRowOfFinalLevel
