module

public import NativeRustcVmX64.Layout.Ladder.Head

/-!
# `ladder`'s query counts and its result (`b9` to `b16`, x86-64)

From `b9` (`R9`), one environment (`envM`: region 0 the frame, region 1 the result, region 2 the
row of `QUERY_TABLE`): `b9`, `b12`, `b17` branch on the count, `b10`, `b13`, `b14`, `b18` load or
zero the counts of the levels past the third, `b15` stores the result, `b16` its tag, restores
the registers and returns (`tail`). Each path's end (`EndOk`) gives the result `Whir.ladder μ r`
(`finish`).
-/

namespace NativeRustcVmX64.Layout.Ladder

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Ladder NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript LeanVM.Parameters NativeRustcVm.Layout
open NativeRustcVmX64.Layout.Stack (WritesW wordAt_writesW wordAt_nat)

@[expose] public section

/-- `QUERY_TABLE`'s row `(r - 1, μ - 16)`. -/
def qtBase [Labels] (m : MachineData) : BitVec 64 :=
  rodataAddr .queryTable +
    BitVec.ofNat 64 (720 * ((reg m .rdx).toNat - 1) + 48 * ((reg m .rsi).toNat - 16))

/-- The environment from `b9`. -/
abbrev envM [Labels] (m d : MachineData) : Env :=
  frameEnv m d 72 [(reg m .rdi, 160), (qtBase m, 48)] (fun _ ↦ 0) 0

end

public section

theorem shl4_toNat (x : BitVec 64) :
    (BinOp.apply .shl .W64 x (BitVec.ofNat 64 4)).toNat = x.toNat * 16 % 2 ^ 64 := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [show shiftCount .W64 (BitVec.ofNat 64 4) = 4 from rfl, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq]

/-- Three words from `p`. -/
theorem words3 {d : DataMem} {p : BitVec 64} {a b c : UInt64} (ha : NativeRustcVm.WordAt d p a)
    (hb : NativeRustcVm.WordAt d (off p 8) b) (hc : NativeRustcVm.WordAt d (off (off p 8) 8) c) :
    NativeRustcVm.WordsAt d p [a, b, c] := by
  rw [wordsAt_cons, wordsAt_cons, wordsAt_cons]
  exact ⟨ha, hb, hc, wordsAt_nil _ _⟩

variable [Labels]

/-- The row of `QUERY_TABLE` the executor's alias names. -/
theorem qtSym_eval {m d : MachineData} (hadm : Whir.Admissible (reg m .rsi).toNat (reg m .rdx).toNat)
    (hR : RodataAt m 72) (h15 : (reg d .r15).toNat = (reg m .rdx).toNat - 1)
    (h14 : (reg d .r14).toNat = (reg m .rsi).toNat - 16) :
    qtSym.eval (envM m d) = (envM m d).base 2 + BitVec.ofInt 64 0 := by
  have hb := admissible_iff.mp hadm
  have hn := hR.noWrap .queryTable
  rw [length_table_bytes] at hn
  have hn' : (rodataAddr .queryTable).toNat + 2880 ≤ 2 ^ 64 := hn
  rw [ofInt_zero64, BitVec.add_zero]
  show BinOp.apply .add .W64 (BinOp.apply .mul .W64 (reg d .r15) (BitVec.ofNat 64 720))
    (BinOp.apply .add .W64 (rodataAddr .queryTable) (BinOp.apply .shl .W64
      (BinOp.apply .add .W64 (reg d .r14) (BinOp.apply .mul .W64 (reg d .r14) (BitVec.ofNat 64 2)))
      (BitVec.ofNat 64 4))) = qtBase m
  have t1 : (BinOp.apply .mul .W64 (reg d .r15) (BitVec.ofNat 64 720)).toNat =
      720 * ((reg m .rdx).toNat - 1) := by
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [BitVec.toNat_mul, h15, BitVec.toNat_ofNat]; omega
  have t2 : (BinOp.apply .shl .W64 (BinOp.apply .add .W64 (reg d .r14)
      (BinOp.apply .mul .W64 (reg d .r14) (BitVec.ofNat 64 2))) (BitVec.ofNat 64 4)).toNat =
      48 * ((reg m .rsi).toNat - 16) := by
    rw [shl4_toNat]
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [BitVec.toNat_add, BitVec.toNat_mul, h14, BitVec.toNat_ofNat]; omega
  apply BitVec.eq_of_toNat_eq
  generalize hA : BinOp.apply .mul .W64 (reg d .r15) (BitVec.ofNat 64 720) = A at t1 ⊢
  generalize hB : BinOp.apply .shl .W64 (BinOp.apply .add .W64 (reg d .r14)
    (BinOp.apply .mul .W64 (reg d .r14) (BitVec.ofNat 64 2))) (BitVec.ofNat 64 4) = B at t2 ⊢
  simp only [BinOp.apply, low_W64, ext_W64, qtBase, BitVec.toNat_add, BitVec.toNat_ofNat, t1, t2]
  omega

/-- `QUERY_TABLE`'s entry's `i`th count, in memory where only the frame changed. -/
theorem table_word' {m : MachineData} {d : DataMem} (hst : StackOk m 72) (hR : RodataAt m 72)
    (hadm : Whir.Admissible (reg m .rsi).toNat (reg m .rdx).toNat)
    (hd : NativeRustcVm.SameOutside m.dmem d (NativeRustcVm.InRange (stackBelow m 72) 72))
    {i : Nat} (hi : i < 6) :
    NativeRustcVm.WordAt d (off (qtBase m) (8 * i)) (qAt (reg m .rsi).toNat (reg m .rdx).toNat i).toUInt64 := by
  have hb := admissible_iff.mp hadm
  have hw := table_word (hR.bytesAt .queryTable) hadm hi
  have e : off (qtBase m) (8 * i) = rodataAddr .queryTable + BitVec.ofNat 64 (720 * ((reg m .rdx).toNat - 1)) +
      BitVec.ofNat 64 (8 * i + 48 * ((reg m .rsi).toNat - 16)) := by
    simp only [qtBase, off, NativeRustcVm.addr_add_add]
    congr 2
    omega
  rw [e]
  have hn := hR.noWrap .queryTable
  have hap := hR.apart .queryTable
  rw [length_table_bytes] at hn hap
  refine NativeRustcVm.BytesAt.of_sameOutside hw hd fun j hj h ↦ ?_
  have hj8 : j < 8 := by simpa [NativeRustcVm.length_wordBytes] using hj
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add] at h
  have hin : NativeRustcVm.InRange (rodataAddr .queryTable) 2880 (rodataAddr .queryTable +
      BitVec.ofNat 64 (720 * ((reg m .rdx).toNat - 1) + (8 * i + 48 * ((reg m .rsi).toNat - 16) + j))) :=
    inRange_off_self (N := 2880) (by omega) (by omega)
  have h' : NativeRustcVm.InRange (stackBelow m 72) 72 (rodataAddr .queryTable +
      BitVec.ofNat 64 (720 * ((reg m .rdx).toNat - 1) + (8 * i + 48 * ((reg m .rsi).toNat - 16) + j))) := h
  exact not_inRange_of_apart hap hn (noWrap_stackBelow hst) hin
    (inRange_mono (k := 72) (k' := 72 + 8) h' (by omega))

/-- **A path's end**: the result `Whir.ladder μ r`, only the result and the frame changed, the
registers restored. -/
theorem finish {m d d' : MachineData} (hpre : LadderPre m)
    (hadm : Whir.Admissible (reg m .rsi).toNat (reg m .rdx).toNat) (hR9 : R9 m d)
    (hwf : (envM m d).WF) {S : SState} (hm : Match (envM m d) S d') {v3 v4 v5 : Sym}
    (hE : EndOk S v3 v4 v5)
    (hv3 : 3 < nOf (reg m .rsi).toNat →
      (v3.eval (envM m d)).toNat = qAt (reg m .rsi).toNat (reg m .rdx).toNat 3)
    (hv4 : 4 < nOf (reg m .rsi).toNat →
      (v4.eval (envM m d)).toNat = qAt (reg m .rsi).toNat (reg m .rdx).toNat 4)
    (hv5 : 5 < nOf (reg m .rsi).toNat →
      (v5.eval (envM m d)).toNat = qAt (reg m .rsi).toNat (reg m .rdx).toNat 5) :
    LadderPost m d' ∧ rspOf d' = rspOf m + 8#64 := by
  obtain ⟨hst, hR, -, -, -⟩ := hpre
  obtain ⟨hepi, hws, hW⟩ := hE
  set o := reg m .rdi with hodef
  set μ := (reg m .rsi).toNat with hμ
  set r := (reg m .rdx).toNat with hr
  have hb := admissible_iff.mp hadm
  have hn := nOf_le μ
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hR9.frame hwf hm hepi
  refine ⟨⟨?_, ?_, hsv⟩, hrsp⟩
  · have W : ∀ (j : Nat) (v : Sym) {x : Nat},
        (j, v) ∈ common ++ [(96, v3), (120, v4), (144, v5)] → j + 8 ≤ 160 →
        (v.eval (envM m d)).toNat = x → NativeRustcVm.WordAt d'.dmem (off o j) x.toUInt64 :=
      fun j v _ hmem hle hx ↦ wordAt_nat (wordAt_writesW hm (r := 1) rfl hW hmem hle) hx
    have hc : ∀ {j : Nat} {v : Sym}, (j, v) ∈ common →
        (j, v) ∈ common ++ [(96, v3), (120, v4), (144, v5)] := fun h ↦ List.mem_append_left _ h
    have hq : ∀ i < 6, ((Sym.load 2 (8 * i) 8).eval (envM m d)).toNat = qAt μ r i := by
      intro i hi
      show ((envM m d).load 2 (8 * i) 8).toNat = _
      rw [load_ofMachine (o := 8 * i) rfl (table_word' hst hR hadm hR9.dmem hi)]
      rw [show (qAt μ r i).toUInt64.toBitVec = BitVec.ofNat 64 (qAt μ r i) from rfl]
      exact toNat_lit (by have := qAt_le μ r i; omega)
    have hdx : (Sym.reg .rdx).eval (envM m d) = reg m .rdx := hR9.rdx
    have hadd : ∀ c ≤ 15, ((addS .rdx c).eval (envM m d)).toNat = r + c := fun c hc ↦ by
      show (BinOp.apply .add .W64 ((Sym.reg .rdx).eval (envM m d)) (BitVec.ofNat 64 c)).toNat = _
      rw [hdx]; exact add_lit_toNat _ c (by omega)
    have hlit : ∀ c < 2 ^ 64, ((Sym.lit c).eval (envM m d)).toNat = c := fun c hc ↦ toNat_lit hc
    have lev : ∀ (j a b c : Nat), NativeRustcVm.WordAt d'.dmem (off o j) a.toUInt64 →
        NativeRustcVm.WordAt d'.dmem (off o (j + 8)) b.toUInt64 →
        NativeRustcVm.WordAt d'.dmem (off o (j + 8 + 8)) c.toUInt64 →
        NativeRustcVm.WordsAt d'.dmem (off o j) [a.toUInt64, b.toUInt64, c.toUInt64] :=
      fun j a b c ha hb' hc' ↦ words3 ha (by rw [off_off]; exact hb')
        (by rw [off_off, off_off]; exact hc')
    rw [ladder_eq hadm]
    refine ⟨?_, by rw [length_ladderW]; exact hn.2, ?_, fun i hi ↦ ?_⟩
    · have := W 0 (.lit 1) (hc (by decide)) (by decide) (hlit 1 (by decide))
      rwa [off_zero] at this
    · rw [length_ladderW]
      exact W 152 (.reg .rcx) (hc (by decide)) (by decide) hR9.rcx
    · rw [length_ladderW] at hi
      simp only [ladderW, List.getElem_map, List.getElem_range]
      refine ⟨show foldAt i < 2 ^ 64 by unfold foldAt; split <;> omega,
        show r + 3 * i < 2 ^ 64 by omega,
        show qAt μ r i < 2 ^ 64 from lt_of_le_of_lt (qAt_le _ _ _) (by decide), ?_⟩
      have hi6 : i < 6 := by omega
      rw [off_off, show NativeRustcVm.Whir.levelBytes = 24 from rfl]
      have hr0 : ((Sym.reg .rdx).eval (envM m d)).toNat = r := by rw [hdx]
      interval_cases i
      · show NativeRustcVm.WordsAt d'.dmem (off o 8)
          [(6 : Nat).toUInt64, r.toUInt64, (qAt μ r 0).toUInt64]
        exact lev 8 _ _ _ (W 8 (.lit 6) (hc (by decide)) (by decide) (hlit 6 (by decide)))
          (W (8 + 8) (.reg .rdx) (hc (by decide)) (by decide) hr0)
          (W (8 + 8 + 8) (.load 2 0 8) (hc (by decide)) (by decide) (hq 0 (by decide)))
      · show NativeRustcVm.WordsAt d'.dmem (off o 32)
          [(4 : Nat).toUInt64, (r + 3).toUInt64, (qAt μ r 1).toUInt64]
        exact lev 32 _ _ _ (W 32 (.lit 4) (hc (by decide)) (by decide) (hlit 4 (by decide)))
          (W (32 + 8) (addS .rdx 3) (hc (by decide)) (by decide) (hadd 3 (by decide)))
          (W (32 + 8 + 8) (.load 2 8 8) (hc (by decide)) (by decide) (hq 1 (by decide)))
      · show NativeRustcVm.WordsAt d'.dmem (off o 56)
          [(4 : Nat).toUInt64, (r + 6).toUInt64, (qAt μ r 2).toUInt64]
        exact lev 56 _ _ _ (W 56 (.lit 4) (hc (by decide)) (by decide) (hlit 4 (by decide)))
          (W (56 + 8) (addS .rdx 6) (hc (by decide)) (by decide) (hadd 6 (by decide)))
          (W (56 + 8 + 8) (.load 2 16 8) (hc (by decide)) (by decide) (hq 2 (by decide)))
      · obtain ⟨h12, h9⟩ := hR9.l3 hi
        show NativeRustcVm.WordsAt d'.dmem (off o 80)
          [(4 : Nat).toUInt64, (r + 9).toUInt64, (qAt μ r 3).toUInt64]
        exact lev 80 _ _ _ (W 80 (.reg .r12) (hc (by decide)) (by decide) h12)
          (W (80 + 8) (.reg .r9) (hc (by decide)) (by decide) h9)
          (W (80 + 8 + 8) v3 (List.mem_append_right _ (by simp)) (by decide) (hv3 hi))
      · obtain ⟨h13, h10⟩ := hR9.l4 hi
        show NativeRustcVm.WordsAt d'.dmem (off o 104)
          [(4 : Nat).toUInt64, (r + 12).toUInt64, (qAt μ r 4).toUInt64]
        exact lev 104 _ _ _ (W 104 (.reg .r13) (hc (by decide)) (by decide) h13)
          (W (104 + 8) (.reg .r10) (hc (by decide)) (by decide) h10)
          (W (104 + 8 + 8) v4 (List.mem_append_right _ (by simp)) (by decide) (hv4 hi))
      · obtain ⟨h11, h3⟩ := hR9.l5 hi
        show NativeRustcVm.WordsAt d'.dmem (off o 128)
          [(4 : Nat).toUInt64, (r + 15).toUInt64, (qAt μ r 5).toUInt64]
        exact lev 128 _ _ _ (W 128 (.reg .r11) (hc (by decide)) (by decide) h11)
          (W (128 + 8) (.reg .rbx) (hc (by decide)) (by decide) h3)
          (W (128 + 8 + 8) v5 (List.mem_append_right _ (by simp)) (by decide) (hv5 hi))
  · have h2 := sameOutside_W2 hwf hm (r := 0) (r' := 1) rfl rfl
      (W := fun j ↦ j < 24) (W' := fun j ↦ j < 160) fun w hw ↦ by
        rcases hws w hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact .inl ⟨h1, by omega, fun j _ hj ↦ by omega⟩
        · exact .inr ⟨h1, by omega, fun j _ hj ↦ by omega⟩
    have hfnw : NativeRustcVm.NoWrap (stackBelow m 72) (72 + 8) := frame_noWrap hst (by decide)
    intro q hq
    rw [h2 q fun hq' ↦ hq ?_]
    · exact hR9.dmem q fun h ↦ hq (.inr h)
    rcases hq' with ⟨j, -, hj, rfl⟩ | ⟨j, -, hj, rfl⟩
    · exact .inr (inRange_off_self (N := 72) (by omega) (by omega))
    · exact .inl (inRange_off_self (N := 160) hj (by omega))

end

public section

variable [Host] {k : Nat}

/-- **`b9` to `b16`**: the counts, the result, the return. -/
theorem tail (hp : Placed code k) {m : MachineData} (hpre : LadderPre m)
    (hadm : Whir.Admissible (reg m .rsi).toNat (reg m .rdx).toNat) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Ladder.b9Offset)) (hR9 : R9 m st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m ∧ rspOf st'.data = rspOf m + 8#64 ∧
      LadderPost m st'.data) st := by
  have hpre' := hpre
  obtain ⟨hst, hR, ⟨hOm, hOn⟩, hOS, hOR⟩ := hpre'
  set o := reg m .rdi with hodef
  set μ := (reg m .rsi).toNat with hμ
  set r := (reg m .rdx).toNat with hr
  have hb := admissible_iff.mp hadm
  have hn := nOf_le μ
  have hf := hR9.frame
  have hfnw : NativeRustcVm.NoWrap (stackBelow m 72) (72 + 8) := frame_noWrap hst (by decide)
  have hTn := hR.noWrap .queryTable
  have hTap := hR.apart .queryTable
  have hTm := (hR.bytesAt .queryTable).mapped
  have hOT := hOR .queryTable
  rw [length_table_bytes] at hTn hTap hTm hOT
  have hsub : 720 * (r - 1) + 48 * (μ - 16) + 48 ≤ 2880 := by omega
  have hqb : (qtBase m).toNat = (rodataAddr .queryTable).toNat + (720 * (r - 1) + 48 * (μ - 16)) :=
    NativeRustcVm.toNat_add_ofNat (by unfold NativeRustcVm.NoWrap at hTn; omega)
  have hwf : (envM m st.data).WF := frame_wf
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩
    (rest2_ok ⟨hOm, hOn⟩ ⟨NativeRustcVm.Mapped.sub hTm hsub, NativeRustcVm.NoWrap.sub hTn hsub⟩
      hf.kept)
    (pairwise3 (Apart.symm' hOS)
      (show NativeRustcVm.Apart (stackBelow m 72) (72 + 8) (qtBase m) 48 from
        NativeRustcVm.Apart.mono (Apart.symm' hTap) le_rfl le_rfl (by omega) (by omega))
      (show NativeRustcVm.Apart o 160 (qtBase m) 48 from
        NativeRustcVm.Apart.mono hOT le_rfl le_rfl (by omega) (by omega)))
  have hm : Match (envM m st.data) midS st.data :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf.rsp_eval, known_ptr rfl hR9.rdi, trivial⟩ trivial
      trivial ⟨qtSym_eval hadm hR hR9.r15 hR9.r14, trivial⟩
  have hq : ∀ i < 6, ((Sym.load 2 (8 * i) 8).eval (envM m st.data)).toNat = qAt μ r i := by
    intro i hi
    show ((envM m st.data).load 2 (8 * i) 8).toNat = _
    rw [load_ofMachine (o := 8 * i) rfl (table_word' hst hR hadm hR9.dmem hi)]
    rw [show (qAt μ r i).toUInt64.toBitVec = BitVec.ofNat 64 (qAt μ r i) from rfl]
    exact toNat_lit (by have := qAt_le μ r i; omega)
  have hcx : (envM m st.data).regs .rcx = BitVec.ofNat 64 (nOf μ) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_lit (by omega)]; exact hR9.rcx
  have done : ∀ {S : SState} {v3 v4 v5 : Sym} {st' : MachineState},
      Match (envM m st.data) S st'.data → EndOk S v3 v4 v5 →
      PcOk (envM m st.data) (.ret (.load 0 72 8)) (Host.addrOf 0) st' →
      (3 < nOf μ → (v3.eval (envM m st.data)).toNat = qAt μ r 3) →
      (4 < nOf μ → (v4.eval (envM m st.data)).toNat = qAt μ r 4) →
      (5 < nOf μ → (v5.eval (envM m st.data)).toNat = qAt μ r 5) →
      Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m ∧
        rspOf st'.data = rspOf m + 8#64 ∧ LadderPost m st'.data) st' :=
    fun hm' hE hpc' h3 h4 h5 ↦ by
      obtain ⟨hpost, hrsp⟩ := finish hpre hadm hR9 hwf hm' hE h3 h4 h5
      simp only [PcOk] at hpc'
      exact .done _ ⟨by rw [hpc']; exact hf.load_ret hst (by decide), hrsp, hpost⟩
  have hpcret : ∀ {x : Int64} {st' : MachineState},
      PcOk (envM m st.data) (.ret (.load 0 72 8)) x st' →
      PcOk (envM m st.data) (.ret (.load 0 72 8)) (Host.addrOf 0) st' := fun h ↦ h
  -- The tail from `b15` and `b16`, the same for every path.
  have fin15 : ∀ {S S' : SState} {v3 v4 v5 : Sym} {st' : MachineState},
      exec b15 S = some (S', .fall) → exec b16 S' = some (after b16 S', .ret (.load 0 72 8)) →
      EndOk (after b16 S') v3 v4 v5 → st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Ladder.b15Offset) →
      Match (envM m st.data) S st'.data →
      (3 < nOf μ → (v3.eval (envM m st.data)).toNat = qAt μ r 3) →
      (4 < nOf μ → (v4.eval (envM m st.data)).toNat = qAt μ r 4) →
      (5 < nOf μ → (v5.eval (envM m st.data)).toNat = qAt μ r 5) →
      Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m ∧
        rspOf st'.data = rspOf m + 8#64 ∧ LadderPost m st'.data) st' := by
    intro S S' v3 v4 v5 st' hx15 hx16 hE hpc' hm' h3 h4 h5
    refine exec_at (infix_of b15_in_code (by simp [b15]) hp) hx15 hwf nofun hpc' hm'
      fun s15 hm15 hpc15 ↦ ?_
    simp only [PcOk] at hpc15
    exact exec_at (infix_of b16_in_code (by simp [b16]) hp) hx16 hwf nofun
      (hpc15.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b15_next)) hm15
      fun s16 hm16 hpc16 ↦ done hm16 hE (hpcret hpc16) h3 h4 h5
  have hl : ∀ i < 6, ∀ {v : Sym}, v = .load 2 (8 * i) 8 →
      (v.eval (envM m st.data)).toNat = qAt μ r i := fun i hi v hv ↦ hv ▸ hq i hi
  -- `b9`: `n = 3`?
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) exit_b9 hwf nofun hpc hm
    fun s9 hm9 hpc9 ↦ ?_
  simp only [PcOk, nm1, SBool.eval, Sym.eval, hcx] at hpc9
  -- `b12` from `b9`, for `n ≥ 4`.
  have at12 : 3 < nOf μ → ∀ {R : MachineState → Prop},
      (nOf μ = 4 → ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Ladder.b12Offset + b12.length) →
        Match (envM m st.data) B12 st'.data → Eventually (step1 Host.exe) R st') →
      (4 < nOf μ → ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Ladder.b17Offset) → Match (envM m st.data) B12 st'.data →
        Eventually (step1 Host.exe) R st') →
      Eventually (step1 Host.exe) R s9 := by
    intro h3 R k4 k5
    have c9 : (!CmpOp.apply .eq .W64 (BinOp.apply .add .W64 (BitVec.ofNat 64 (nOf μ))
        (BitVec.ofNat 64 18446744073709551615)) (BitVec.ofNat 64 2)) = true := by
      rcases (show nOf μ = 4 ∨ nOf μ = 5 ∨ nOf μ = 6 by omega) with h | h | h <;> rw [h] <;>
        decide
    rw [c9] at hpc9
    simp only [↓reduceIte] at hpc9
    refine exec_at (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf nofun
      (hpc9.trans (hp.label NativeRustcVmX64.Vm.Ladder.label_12_at)) hm9 fun s12 hm12 hpc12 ↦ ?_
    simp only [PcOk, nm1, SBool.eval, Sym.eval, hcx] at hpc12
    rcases (show nOf μ = 4 ∨ 4 < nOf μ by omega) with h4 | h4
    · rw [h4] at hpc12
      simp (config := { decide := true }) only [↓reduceIte] at hpc12
      exact k4 h4 s12 hpc12 hm12
    · have c12 : (!CmpOp.apply .eq .W32 (BinOp.apply .add .W64 (BitVec.ofNat 64 (nOf μ))
          (BitVec.ofNat 64 18446744073709551615)) (BitVec.ofNat 64 3)) = true := by
        rcases (show nOf μ = 5 ∨ nOf μ = 6 by omega) with h | h <;> rw [h] <;> decide
      rw [c12] at hpc12
      simp only [↓reduceIte] at hpc12
      exact k5 h4 s12 (hpc12.trans (hp.label NativeRustcVmX64.Vm.Ladder.label_17_at)) hm12
  rcases (show nOf μ = 3 ∨ nOf μ = 4 ∨ nOf μ = 5 ∨ nOf μ = 6 by omega) with h3 | h4 | h5 | h6
  · rw [h3] at hpc9
    simp (config := { decide := true }) only [↓reduceIte] at hpc9
    refine exec_at (infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf nofun
      (hpc9.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b9_next)) hm9 fun s10 hm10 hpc10 ↦ ?_
    simp only [PcOk] at hpc10
    refine exec_at (infix_of b13_in_code (by simp [b13]) hp) exit_b13a hwf nofun
      (hpc10.trans (hp.label NativeRustcVmX64.Vm.Ladder.label_13_at)) hm10 fun s13 hm13 hpc13 ↦ ?_
    simp only [PcOk] at hpc13
    refine exec_at (infix_of b14_in_code (by simp [b14]) hp) exit_b14a hwf nofun
      (hpc13.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b13_next)) hm13 fun s14 hm14 hpc14 ↦ ?_
    simp only [PcOk] at hpc14
    exact fin15 exit_b15a exit_b16a end_a (hpc14.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b14_next))
      hm14 (by omega) (by omega) (by omega)
  · refine at12 (by omega) (fun _ s12 hpc12 hm12 ↦ ?_) (fun h _ _ _ ↦ absurd h (by omega))
    refine exec_at (infix_of b13_in_code (by simp [b13]) hp) exit_b13b hwf nofun
      (hpc12.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b12_next)) hm12 fun s13 hm13 hpc13 ↦ ?_
    simp only [PcOk] at hpc13
    refine exec_at (infix_of b14_in_code (by simp [b14]) hp) exit_b14b hwf nofun
      (hpc13.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b13_next)) hm13 fun s14 hm14 hpc14 ↦ ?_
    simp only [PcOk] at hpc14
    exact fin15 exit_b15b exit_b16b end_b (hpc14.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b14_next))
      hm14 (fun _ ↦ hl 3 (by decide) rfl) (by omega) (by omega)
  all_goals
    refine at12 (by omega) (fun h _ _ _ ↦ absurd h (by omega)) (fun _ s12 hpc12 hm12 ↦ ?_)
    refine exec_at (infix_of b17_in_code (by simp [b17]) hp) exit_b17 hwf nofun hpc12 hm12
      fun s17 hm17 hpc17 ↦ ?_
  all_goals simp only [PcOk, nm1, SBool.eval, Sym.eval, hcx] at hpc17
  · rw [h5] at hpc17
    simp (config := { decide := true }) only [↓reduceIte] at hpc17
    refine exec_at (infix_of b14_in_code (by simp [b14]) hp) exit_b14c hwf nofun
      (hpc17.trans (hp.label NativeRustcVmX64.Vm.Ladder.label_14_at)) hm17 fun s14 hm14 hpc14 ↦ ?_
    simp only [PcOk] at hpc14
    exact fin15 exit_b15c exit_b16c end_c (hpc14.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b14_next))
      hm14 (fun _ ↦ hl 3 (by decide) rfl) (fun _ ↦ hl 4 (by decide) rfl) (by omega)
  · rw [h6] at hpc17
    simp (config := { decide := true }) only [↓reduceIte] at hpc17
    refine exec_at (infix_of b18_in_code (by simp [b18]) hp) exit_b18 hwf nofun
      (hpc17.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b17_next)) hm17 fun s18 hm18 hpc18 ↦ ?_
    simp only [PcOk] at hpc18
    exact fin15 exit_b15d exit_b16d end_d (hpc18.trans (hp.label NativeRustcVmX64.Vm.Ladder.label_15_at)) hm18
      (fun _ ↦ hl 3 (by decide) rfl) (fun _ ↦ hl 4 (by decide) rfl)
      (fun _ ↦ hl 5 (by decide) rfl)


end

end NativeRustcVmX64.Layout.Ladder
