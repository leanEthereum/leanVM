module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.Mid
public import NativeRustcVmX64.Code.Vm.LanesOf.Names
public import NativeRustcVmX64.Code.Vm.RowsRow.Names

/-!
# `each_row` with `next_level`'s closure: a row's lanes (x86-64)

At `b12` (`AtB12`): `b12` calls `Rows::row(j)`; `b13` calls `lanes_of` on the row into the lanes
at 152; `b14` checks its `Some` (the lanes fit: always): at `b15` (`AtB15`, `iter_b`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfNextLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)
open LeanVM.Protocol.Compile (wireMaxQueries wireMaxLeafWords)
open NativeVm (openingWords)

@[expose] public section

/-- Row `j`'s lanes. -/
abbrev lanesJ (m0 : MachineData) (row : Array UInt64) : Array EW :=
  lanesOf (reg m0 .rdi).toNat row

/-- **At `b15`**, in iteration `j`, the row's lanes at 152. -/
structure AtB15 (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 8 m
  hj : j < rows.size
  hjq : j < (qsOf m0).size
  mm : MidN rows m0 j m.dmem
  lanes : EWsAt m.dmem (fb m0 + BitVec.ofNat 64 152) (lanesJ m0 (rows[j]'hj)).toList
  lsize : (lanesJ m0 (rows[j]'hj)).size ≤ 64
  rdx : (reg m .rdx).toNat = (lanesJ m0 (rows[j]'hj)).size
  rbp : reg m .rbp = ((qsOf m0)[j]'hjq).toBitVec
  rbx : reg m .rbx = BitVec.ofNat 64 j
  r15 : reg m .r15 = reg m0 .rsi + BitVec.ofNat 64 (8 * j)
  r14 : reg m .r14 = bOf m0
  r13 : reg m .r13 = fb m0 + BitVec.ofNat 64 1440
  r12 : reg m .r12 = fb m0 + BitVec.ofNat 64 152

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

/-- Row `j`'s place in the openings. -/
theorem row_bound [Labels] (c : Ctx rows op m0) (hj : j < rows.size) :
    8 * (1 + j * openingWords) + 8 * (rows[j]'hj).size ≤ 8 * NativeRustcVm.Sumcheck.openingsWords := by
  obtain ⟨-, hsz, w, hw, -, hrow⟩ := c.rowsAt
  rw [(hrow j hj).1]
  have : wireMaxQueries = 256 := rfl
  have : wireMaxLeafWords = 64 := rfl
  have : NativeRustcVm.Sumcheck.openingsWords = 49408 := rfl
  have : j * openingWords ≤ 255 * 193 := by
    rw [show openingWords = 193 from rfl]; exact Nat.mul_le_mul_right _ (by omega)
  omega

variable [Host] {k : Nat}

/-- **A row's lanes**: from `b12` to `b15`. -/
theorem iter_b (hp : Placed code k)
    (hrow : Spec (label NativeRustcVmX64.Vm.RowsRow.entryLabel) (RowsRowPre op rows) (RowsRowPost op rows))
    (hlanes : Spec (label NativeRustcVmX64.Vm.LanesOf.entryLabel) LanesOfPre LanesOfPost)
    (c : Ctx rows op m0) {m : MachineData} (h : AtB12 rows m0 j m)
    (cont : ∀ m', AtB15 rows m0 j m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b15Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b12Offset)⟩ := by
  have hl := lay c
  have hsp := hl.sp
  have htop := hl.ok.2.1
  have hstk : eachRowNextStack = 3136 := rfl
  have hrs : rows.size ≤ 256 := c.rowsAt.2.1
  have hjr := h.hj
  have hrin := c.rin
  have hopin := c.opin
  have hOW : NativeRustcVm.Sumcheck.openingsWords = 49408 := rfl
  have hjo : j * openingWords ≤ 255 * 193 := by
    rw [show openingWords = 193 from rfl]; exact Nat.mul_le_mul_right _ (by omega)
  -- `b12`: `Rows::row(j)`
  obtain ⟨hwf, hm⟩ := frame_env c h.fr (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b12Offset + b12.length)).toBitVec
  have hk12 : b12.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b12Offset) := b12_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk12 run_b12 hwf (fun _ _ ↦ rfl) hm fun st8 hm8 hpc8 ↦ ?_
  have hs8 : SameOutside m.dmem st8.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 1432 1432) :=
    EachRow.hit_of_block hl le_rfl (by decide) hm8 hwf (by decide)
  have hfr8 : FR m0 0 st8.data :=
    h.fr.step hl le_rfl (by decide) ((rv hm8 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
      (hm8.kept hwf) hs8 (by decide)
  have e8rdi : reg st8.data .rdi = reg m0 .rcx := (rv hm8 (v := .reg .rdi) rfl).trans h.rdi
  have e8rsi : (reg st8.data .rsi).toNat = j := by
    rw [rv hm8 (v := .reg .rbx) rfl]
    show (reg m .rbx).toNat = _
    rw [h.rbx, BitVec.toNat_ofNat]; omega
  have hP8 : RowsRowPre op rows st8.data := by
    unfold RowsRowPre
    rw [e8rdi]
    exact ⟨hfr8.stackOk hl (by decide), rowsAt_of_fr c hfr8, hrin.1.2,
      NativeRustcVmX64.Transcript.apart_callee hrin.2 hfr8.rsp0 hsp (by decide)⟩
  refine call_then hpc8 hrow hP8 fun st9 hpc9 hrsp9 hq9 ↦ ?_
  obtain ⟨hres, hd9, hsv9⟩ := hq9
  obtain ⟨hrdx9, hrax9, -⟩ := hres (by rw [e8rsi]; exact hjr)
  simp only [e8rsi] at hrdx9 hrax9
  have hfr9 : FR m0 8 st9.data :=
    EachRow.Fr.call hl (lo := 1432) (hi := 1432) le_rfl (by decide) hfr8 hrsp9 hsv9
      (fun q _ ↦ by rw [hd9]) (by decide)
  obtain ⟨d9, pc9⟩ := st9
  simp only at hpc9 hfr9 hd9 hsv9 hrdx9 hrax9
  subst hpc9
  rw [show k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b12Offset + b12.length = k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b13Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfNextLevel.b12_next]]
  have hmm9 : MidN rows m0 j d9.dmem := by
    rw [hd9]
    exact h.mm.keep c le_rfl (by decide) (by decide) (by decide) hs8
  have k9 : ∀ r, calleeSaved r = true → reg d9 r = reg m r := fun r hc ↦ by
    rw [sv hsv9 r hc]
    exact hm8.regs r (.reg r) (by revert hc; cases r <;> decide)
  -- `b13`: `lanes_of`
  obtain ⟨hwf9, hm9⟩ := frame_env c hfr9 (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b13Offset + b13.length)).toBitVec
  have hk13 : b13.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b13Offset) := b13_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk13 run_b13 hwf9 (fun _ _ ↦ rfl) hm9 fun st10 hm10 hpc10 ↦ ?_
  have hs10 : SameOutside d9.dmem st10.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 1432 1432) :=
    EachRow.hit_of_block hl le_rfl (by decide) hm10 hwf9 (by decide)
  have hfr10 : FR m0 0 st10.data :=
    hfr9.step hl le_rfl (by decide) ((rv hm10 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
      (hm10.kept hwf9) hs10 (by decide)
  let ra := off op (8 * (1 + j * openingWords))
  have hbound := row_bound c hjr
  have hopnw : op.toNat + 8 * NativeRustcVm.Sumcheck.openingsWords ≤ 2 ^ 64 := hopin.1.2
  have hra : ra.toNat = op.toNat + 8 * (1 + j * openingWords) :=
    NativeRustcVm.Transcript.toNat_off (by omega)
  have e10rdi : reg st10.data .rdi = reg m0 .rdi :=
    (rv hm10 (v := .load 0 96 8) rfl).trans (NativeRustcVmX64.Arrays.load_word hmm9.low.w96)
  have e10rsi : reg st10.data .rsi = ra := (rv hm10 (v := .reg .rax) rfl).trans hrax9
  have e10rdx : (reg st10.data .rdx).toNat = (rows[j]'hjr).size :=
    (congrArg BitVec.toNat (rv hm10 (v := .reg .rdx) rfl)).trans hrdx9
  have e10rcx : reg st10.data .rcx = fb m0 + BitVec.ofNat 64 152 :=
    (rv hm10 (v := .ptr 0 152) rfl).trans (EachRow.eval_ptr0 152)
  have e10r12 : reg st10.data .r12 = fb m0 + BitVec.ofNat 64 152 :=
    (rv hm10 (v := .ptr 0 152) rfl).trans (EachRow.eval_ptr0 152)
  have hrows10 := rowsAt_of_fr c hfr10
  obtain ⟨-, -, w, hw64, -, hrowW⟩ := hrows10
  have hWj := (hrowW j hjr).2
  have hsb := hfr10.stackBelow_toNat hl (N' := lanesOfStack) (by decide)
  have hopst := hopin.2
  unfold OffStack Apart at hopst
  rw [hl.baseN] at hopst
  have a152 := hl.addr (o := 152) (by decide)
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
      rw [a152, hra]
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
      (EachRow.Hit m0 1984 eachRowNextStack 152 1176) :=
    EachRow.hit_of_call hl (by decide) (by decide) hfr10.rsp0 (N' := lanesOfStack) (by decide)
      le_rfl (by decide) hch
  have hfr11 : FR m0 8 st11.data :=
    EachRow.Fr.call hl (by decide) (by decide) hfr10 hrsp11 hsv11 hs11 (by decide)
  obtain ⟨d11, pc11⟩ := st11
  simp only at hpc11 hfr11 hs11 hsv11 hax hdx hew
  subst hpc11
  rw [show k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b13Offset + b13.length = k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b14Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfNextLevel.b13_next]]
  have k11 : ∀ r, calleeSaved r = true → r ≠ .r12 → reg d11 r = reg m r := fun r hc hr ↦ by
    rw [sv hsv11 r hc]
    have := hm10.regs r (.reg r) (by revert hc hr; cases r <;> decide)
    exact this.trans (k9 r hc)
  -- `b14`
  obtain ⟨hwf11, hm11⟩ := frame_env c hfr11 0
  have hk14 : b14.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b14Offset) := b14_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk14 run_b14 hwf11 (fun _ h ↦ by cases h) hm11 fun st12 hm12 hpc12 ↦ ?_
  have hd12 : st12.data.dmem = d11.dmem := hm12.dmem_eq hwf11 rfl
  have hfr12 : FR m0 8 st12.data := hfr11.ofBlock hwf11 hm12 rfl (by decide)
  have hrax : (EachRow.envE m0 d11 1984 16 [] (fun _ ↦ 0) 0).regs .rax = 1#64 := hax
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
  have hmm12 : MidN rows m0 j d12.dmem := by
    rw [hd12]
    exact (hmm9.keep c le_rfl (by decide) (by decide) (by decide) hs10).keep c (by decide)
      (by decide) (by decide) (by decide) hs11
  refine cont d12 ⟨hfr12, hjr, h.hjq, hmm12, by rw [hd12]; exact hew, hls, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [e12 .rdx (.inr rfl)]; exact hdx
  · rw [e12 .rbp (.inl rfl), k11 .rbp rfl (by decide)]; exact h.rbp
  · rw [e12 .rbx (.inl rfl), k11 .rbx rfl (by decide)]; exact h.rbx
  · rw [e12 .r15 (.inl rfl), k11 .r15 rfl (by decide)]; exact h.r15
  · rw [e12 .r14 (.inl rfl), k11 .r14 rfl (by decide)]; exact h.r14
  · rw [e12 .r13 (.inl rfl), k11 .r13 rfl (by decide)]; exact h.r13
  · rw [e12 .r12 (.inl rfl), sv hsv11 .r12 rfl]; exact e10r12

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
