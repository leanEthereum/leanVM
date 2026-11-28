module

public import NativeRustcVmX64.Tables.TableTerms.FormsRun
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names

/-!
# `table_terms`: table `i`'s point (x86-64)

`b10` clears entry `i`'s point and calls `Buf::extend` with the point's first `min h |point|`
coordinates (`h` the table's log-height, at most `30`): it succeeds, the entry's point becomes
`point.extract 0 h`; `b11` goes on (`point_step`, to `b12` at `k + NativeRustcVmX64.Vm.TableTerms.b12Offset`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf ewOf)

@[expose] public section

/-- Table `i`'s point: the point's first `h` coordinates. -/
def ptI (heights : Array Nat) (m0 : MachineData) (i : Nat) : Array EW :=
  (ptw m0).extract 0 (heights.getD i 0)

/-- The frame's words from the loop head on. -/
abbrev LA (m0 : MachineData) (i : Nat) (f : EW) : List (Nat × UInt64) :=
  cws m0 ++ lw m0 i f ++ tw112 i

end

public section

section
variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

/-- Table `i`'s height in a body. -/
theorem height_word (h : TableTermsPre a s heights forms m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) o d) {i : Nat} (hi : i < 6) :
    NativeRustcVm.WordAt d.dmem (hA m0 + BitVec.ofNat 64 (8 * i)) (heights.getD i 0).toUInt64 ∧
      heights.getD i 0 ≤ 30 := by
  have hH := Pre.hts h
  have hsz : heights.size = 6 := hH.1
  have hw := WordsAt.of_same hH.2.2 (same_readIn h hb (Pre.hs h)) (by simp [hsz])
  rw [wordsAt_iff] at hw
  have hl : i < (heights.toList.map Nat.toUInt64).length := by simp [hsz]; exact hi
  have := hw i hl
  simp only [List.getElem_map, Array.getElem_toList] at this
  rw [NativeVm.Math.Tables.getD_eq_getElem' _ _ (by omega)]
  exact ⟨this, hH.2.1 _ (Array.getElem_mem _)⟩

/-- An entry's point and the iteration's outputs, kept across a change of the stack. -/
theorem pt_keep (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6) {d d' : Mem 64}
    {W : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' W)
    (hW : ∀ q, W q → NativeRustcVm.InRange (stackBelow m0 N) N q) {L : List EW}
    (hp : NativeRustcVm.BufEWAt d (evi m0 i) 30 L) : NativeRustcVm.BufEWAt d' (evi m0 i) 30 L :=
  BufEWAt.of_same hp (n := 488) (Same.of_sameOutside hs fun j hj hq ↦
    outs_not_stackN h (.inr (.inr (evi_in h hi (NativeRustcVm.inRange_add (by omega)
      (by norm_num))))) (hW _ hq)) (by omega)

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **Table `i`'s point.** -/
theorem point_step (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    {i : Nat} (hi : i < 6) {acc : Acc} {si : TState} {xs : Array EW} {s' : TState}
    {d : MachineData} (H : Cm a s heights forms m0 i acc si xs s' d) {f g : EW}
    (hfw : FW m0 d (ncW i ++ ewW 80 g ++ wW (wt m0 i)))
    (hrax : reg d .rax = f.c0.toBitVec) (hrdx : reg d .rdx = f.c1.toBitVec)
    (h12 : reg d .r12 = BitVec.ofNat 64 (8 * i))
    (h13 : reg d .r13 = fA m0 + BitVec.ofNat 64 (11864 + 17784 * i))
    (cont : ∀ d', Bd m0 272 N slots (outs m0) 8 d' →
      FW m0 d' (LA m0 i acc.2.1 ++ (ncW i ++ ewW 80 g ++ wW (wt m0 i))) →
      It a m0 i acc.2.2 xs s' d' →
      NativeRustcVm.BufEWAt d'.dmem (evi m0 i) 30 (ptI heights m0 i).toList →
      reg d' .r14 = f.c0.toBitVec → reg d' .r13 = f.c1.toBitVec →
      reg d' .r15 = fA m0 + BitVec.ofNat 64 (11864 + 17784 * i) →
      reg d' .rbx = evi m0 i → reg d' .rbp = BitVec.ofNat 64 (16 + 40 * i) →
      reg d' .r12 = BitVec.ofNat 64 (8 * i) →
      Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b12Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b10Offset)⟩ := by
  have hS := Pre.stack h
  have eo := evi_out h hi
  have fwA : FW m0 d (LA m0 i acc.2.1) := H.fw
  obtain ⟨hw8, hh30⟩ := height_word h H.bd hi
  have hlen := Pre.r9 h
  unfold tablePointCap at hlen
  let ra := (Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b10Offset + b10.length)).toBitVec
  let env := E m0 d [(argA m0, 32), (evi m0 i, 8), (hA m0 + BitVec.ofNat 64 (8 * i), 8)] ra
  have hwf : env.WF := wf_pt h hi H.bd.fr.kept
  have w16 := lw16 (FW.right (FW.left fwA))
  have hm : Match env ptS d := by
    refine match_body H.bd ⟨rfl, rfl, rfl, rfl, trivial⟩ ⟨?_, ?_, ?_, trivial⟩
    · show stackBelow m0 272 + BitVec.ofInt 64 280 = argA m0 + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 280 = BitVec.ofNat 64 (272 + 8) from rfl,
        show stackBelow m0 272 + BitVec.ofNat 64 (272 + 8) = off (stackBelow m0 272) (272 + 8)
          from rfl, frame_add, ofInt_zero64, BitVec.add_zero]
    · show (Sym.load 0 16 8).eval env = evi m0 i + BitVec.ofInt 64 0
      rw [ld0 w16, ofInt_zero64, BitVec.add_zero]
    · show (Sym.bin .add .W64 (.load 1 0 8) (.reg .r12)).eval env =
        hA m0 + BitVec.ofNat 64 (8 * i) + BitVec.ofInt 64 0
      rw [eval_add', eval_reg, h12, ofInt_zero64, BitVec.add_zero]
      show env.load 1 (8 * 0) 8 + _ = _
      rw [load_eq_wordOf]
      exact congrArg (· + _) (arg_word h H.bd (j := 0) (by omega))
  refine exec_then (infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf (fun _ _ ↦ rfl) hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨miss1, mid1, W1, -, w0, rbx1, rbp1, r14_1, r15_1, r13_1, rdi1, rsi1, rdx1, k1⟩ := ok_b10
  have hR2 : ∀ r ∈ [2], ∀ x, [(argA m0, 32), (evi m0 i, 8), (hA m0 + BitVec.ofNat 64 (8 * i), 8)][r - 1]? =
      some x → ∀ q, NativeRustcVm.InRange x.1 x.2 q → NativeRustcVm.InRange (evi m0 i) 8 q := by
    intro r hr x hx q hq
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [Nat.add_one_sub_one, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hx
    subst hx
    exact hq
  have hev8 : ∀ q, NativeRustcVm.InRange (evi m0 i) 8 q → NativeRustcVm.InRange (evi m0 i) 1968 q :=
    fun q hq ↦ inRange_mono hq (by omega)
  have hb1 := (blockB h H.bd hwf hm1 mid1 W1 fun r hr x hx q hq ↦
    .inr (.inr (evi_in h hi (hev8 q (hR2 r hr x hx q hq))))).1
  have hs1 := same_block hwf hm1 (writesIn_of_mid mid1) (belowRet_of_mid mid1) W1 hR2
  have it1 : It a m0 i acc.2.2 xs s' st1.data :=
    H.it.step h hi (hm1.kept hwf) hs1 fun q hq ↦ hq.elim (fun h' ↦ .inl (fr_stack h h'))
      fun h' ↦ .inr (inRange_mono h' (by omega))
  have fw1 : FW m0 st1.data (LA m0 i acc.2.1 ++ (ncW i ++ ewW 80 g ++ wW (wt m0 i))) :=
    fw_blockU hwf hm1 (writesIn_of_mid mid1) miss1 rfl
      (fun p hp ↦ by
        rcases List.mem_append.mp hp with hp | hp
        · exact (fwL_le p hp).2.1
        · simp only [List.mem_append, ncW, ewW, wW, List.mem_cons, List.not_mem_nil,
            or_false] at hp
          rcases hp with ((rfl | rfl) | rfl | rfl) | rfl | rfl <;> simp)
      (FW.append fwA hfw)
  have rg : ∀ {r : Reg64} {v : Sym}, (after b10 ptS).reg r = some v →
      reg st1.data r = v.eval env := fun hv ↦ hm1.regs _ _ hv
  have erdi : reg st1.data .rdi = evi m0 i := by rw [rg rdi1]; exact ld0 w16
  have ersi : reg st1.data .rsi = reg m0 .r8 := by
    rw [rg rsi1]; exact ld0 (cws40 (FW.left (FW.left fwA)))
  have ehgt : (Sym.load 3 0 8).eval env = BitVec.ofNat 64 (heights.getD i 0) := by
    show env.load 3 0 8 = _
    rw [load_eq_wordOf, show env.base 3 = hA m0 + BitVec.ofNat 64 (8 * i) from rfl,
      NativeRustcVm.addr_add_zero]
    show (wordOf d.dmem (hA m0 + BitVec.ofNat 64 (8 * i))).toBitVec = _
    rw [NativeRustcVm.wordOf_of_wordAt hw8]
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, toNat_toUInt64' (by omega), toNat_ofNat_lt (by omega)]
  have elen : (Sym.load 0 48 8).eval env = reg m0 .r9 := ld0 (cws48 (FW.left (FW.left fwA)))
  have hmin : (reg st1.data .rdx).toNat = min (heights.getD i 0) (reg m0 .r9).toNat := by
    rw [rg rdx1]
    unfold rdx10
    rw [eval_ite, eval_not', eval_ult, ehgt, elen, toNat_ofNat_lt (by omega)]
    by_cases hc : heights.getD i 0 < (reg m0 .r9).toNat
    · simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [toNat_ofNat_lt (by omega)]; omega
    · simp only [hc, decide_false, Bool.not_false, ↓reduceIte]; omega
  have hz : NativeRustcVm.WordAt st1.data.dmem (evi m0 i) 0 := by
    have := wordAt_written hm1 (r := 2) (o := 0) rfl (by omega) w0 (w := 0) rfl
    rwa [off_zero] at this
  -- `Buf::extend`.
  have hle : 272 + bufEWExtendStack ≤ N := by rw [N_eq]; decide
  have hnp := min_le_right (heights.getD i 0) (reg m0 .r9).toNat
  have hpt := rin_sub (o := 0) (k := 16 * min (heights.getD i 0) (reg m0 .r9).toNat) (Pre.pt h)
    (by omega)
  rw [NativeRustcVm.addr_add_zero] at hpt
  have hap : NativeRustcVm.Apart (evi m0 i) (8 + 16 * 30) (reg m0 .r8)
      (16 * min (heights.getD i 0) (reg m0 .r9).toNat) :=
    apart_sub (ev_noWrap h) (Apart.symm' (hpt.2.2 ⟨ev m0, tableEvalsBytes⟩ (by simp [wsL])))
      (show 1968 * i + (8 + 16 * 30) ≤ tableEvalsBytes by
        unfold tableEvalsBytes nTables tableEvalBytes; omega)
  have hb1' : Bd m0 272 N slots (outs m0) 0 st1.data := hb1
  have hsub : 8 + 16 * 30 ≤ 1968 := by omega
  have hpre : BufEWExtendPre 30 st1.data := by
    unfold BufEWExtendPre
    rw [erdi, ersi, hmin, NativeRustcVm.wordOf_of_wordAt hz]
    have r1 := rd_callee h hb1' hle (x := evi m0 i) (n := 8 + 16 * 30) (fun j hj ↦ eo.1 j (by omega))
      (NativeRustcVm.NoWrap.mono eo.2.1 hsub) (NativeRustcVm.Apart.mono (n' := 8 + 16 * 30)
        eo.2.2.2.2.1 le_rfl (by omega) le_rfl le_rfl)
    have r2 := rd_callee h hb1' hle hpt.1.1 hpt.1.2 hpt.2.1
    exact ⟨hb1'.stackOk_at hS (Nat.zero_le _) (by simpa using hle), by decide, r1.1, r2.1, hap,
      r1.2, r2.2⟩
  simp only [PcOk] at hpc1
  refine call_then (env := env) hpc1 hext hpre fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨q0, q1, q2⟩ := hq2
  rw [erdi, NativeRustcVm.wordOf_of_wordAt hz, hmin] at q0
  have hc0 : (0 : UInt64).toNat + min (heights.getD i 0) (reg m0 .r9).toNat ≤ 30 := by
    simp; omega
  simp only [hc0, ↓reduceIte] at q0
  obtain ⟨al, hbuf⟩ := q0
  unfold Changes at q1
  rw [erdi] at q1
  have hRo : ∀ q, NativeRustcVm.InRange (evi m0 i) (8 + 16 * 30) q → outs m0 q :=
    fun q hq ↦ .inr (.inr (evi_in h hi (inRange_mono hq (by omega))))
  have q1' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem
      (fun q ↦ NativeRustcVm.InRange (evi m0 i) (8 + 16 * 30) q ∨
        NativeRustcVm.InRange (stackBelow st1.data bufEWExtendStack) bufEWExtendStack q) := q1
  have hb2 := call_bd h hb1' hle q2 hrsp2 q1' hRo
  have fw2 := fw_callO h hb1' hle q1' hRo (fun p hp ↦ by
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨(fwL_le p hp).1, (fwL_le p hp).2.1⟩
    · simp only [List.mem_append, ncW, ewW, wW, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with ((rfl | rfl) | rfl | rfl) | rfl | rfl <;> exact ⟨by simp, by simp⟩) fw1
  have it2 := it_call h hi it1 hb1' hle q2 q1' fun q hq ↦ .inr hq
  have hbuf' : NativeRustcVm.BufEWAt st2.data.dmem (evi m0 i) 30 (ptI heights m0 i).toList := by
    have e : (slice st1.data (reg m0 .r8) (reg st1.data .rdx)).toList = (ptI heights m0 i).toList := by
      unfold slice
      rw [hmin, NativeRustcVm.ewsOf_congr (d := m0.dmem) fun j hj ↦
        same_readIn h hb1 (Pre.pt h) j (by omega)]
      unfold ptI ptw slice
      rw [Array.toList_extract, List.toList_toArray, List.toList_toArray, List.extract_eq_take_drop,
        List.drop_zero, Nat.sub_zero, ← ewsOf_take]
    have := hbuf
    rw [ersi] at this
    unfold NativeRustcVm.bufEWOf at this
    rw [NativeRustcVm.wordOf_of_wordAt hz] at this
    rw [show (0 : UInt64).toNat = 0 from rfl, show ewsOf st1.data.dmem (evi m0 i + 8#64) 0 = []
      from rfl, List.nil_append, e] at this
    exact this
  have cs2 : ∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r := q2.1
  -- `b11`: the result.
  let ra3 := (Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b11Offset + b11.length)).toBitVec
  have hwf3 : (E m0 st2.data [] ra3).WF := wf_nil h hb2.fr.kept
  have hm3 : Match (E m0 st2.data [] ra3) sF st2.data := match_body hb2 ⟨rfl, trivial⟩ trivial
  refine at_pc (hpc2.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableTerms.b10_next)))
    (exec_then (infix_of b11_in_code (by simp [b11]) hp) exit_b11 hwf3 nofun hm3
      fun st3 hm3' hpc3 ↦ ?_)
  obtain ⟨mid3, mem3, k3⟩ := ok_b11
  have hd3 : st3.data.dmem = st2.data.dmem := hm3'.dmem_eq hwf3 mem3
  have hb3 := (blockB h hb2 hwf3 hm3' mid3 (os := []) (by rw [WrOk, mem3]; rfl) nofun).1
  have hc : cAl.eval (E m0 st2.data [] ra3) = false := by
    have := cAl_eval (env := E m0 st2.data [] ra3) (b := true) (by
      show (reg st2.data .rax).toNat % 256 = _
      exact al)
    simpa using this
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc3
  have kr : ∀ r ∈ csR, reg st3.data r = reg st1.data r := fun r hr ↦ by
    rw [keeps_reg hm3' k3 hr]
    exact cs2 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine at_pc (hpc3.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableTerms.b11_next)))
    (cont st3.data hb3 (FW.of_dmem hd3 fw2) ?_ (by rw [hd3]; exact hbuf') ?_ ?_ ?_ ?_ ?_ ?_)
  · exact ⟨by rw [hd3]; exact it2.ts, by rw [hd3]; exact it2.vals,
      fun j hj ↦ by rw [hd3]; exact it2.evs j hj, it2.osz⟩
  · rw [kr .r14 (by simp), rg r14_1]; exact hrax
  · rw [kr .r13 (by simp), rg r13_1]; exact hrdx
  · rw [kr .r15 (by simp), rg r15_1]; exact h13
  · rw [kr .rbx (by simp), rg rbx1]; exact ld0 w16
  · rw [kr .rbp (by simp), rg rbp1]
    exact ld0 (fwA (112, _) (List.mem_append_right _ (List.mem_singleton_self _)))
  · rw [kr .r12 (by simp), keeps_reg hm1 k1 (by simp)]; exact h12

end

end NativeRustcVmX64.Tables.TableTerms
