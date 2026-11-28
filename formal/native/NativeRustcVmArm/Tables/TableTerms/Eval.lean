module

public import NativeRustcVmArm.Code.Vm.Evaluate.Names
public import NativeRustcVmArm.Tables.TableTerms.Body

/-!
# `table_terms`: one of table `i`'s forms

`b6`, `b7`, `b8` each save two words in the frame and call `evaluate` on form `j` of table `i`
(`fm`, its `FormBuf` at `form_at`) and the table's evaluations (`eval_step`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVmArm.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf BufEWAt)
open NativeRustcVmArm.Bus (after)

@[expose] public section

/-- Form `j` of table `i`. -/
def fm (forms : Array (Array FormW)) (i j : Nat) : FormW := (forms.getD i #[]).getD j #[]

end

public section

theorem ev_le : 288 + evaluateStack ≤ N := Nat.le_refl _

/-- An offset `fok` lists is a word of the frame. -/
theorem fok_le {S : SState} {os : List Nat} (hos : fok S os = true) {o : Nat} (ho : o ∈ os) :
    o + 8 ≤ 288 := by
  have := List.all_eq_true.mp hos o ho
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

theorem mem_of_all {L : List (Nat × BitVec 64)} {os : List Nat}
    (h : (L.map Prod.fst).all (fun o ↦ os.contains o) = true) {p : Nat × BitVec 64}
    (hp : p ∈ L) : p.1 ∈ os := by
  have := List.all_eq_true.mp h p.1 (List.mem_map_of_mem hp)
  simpa using this

section
variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

/-- **Form `j` of table `i`** at the entry. -/
theorem form_at (h : TableTermsPre a s heights forms m0) {i j : Nat} (hi : i < 6) (hj : j < 3) :
    FormBufAt m0.dmem (m0.regs.X7.toBitVec + BitVec.ofNat 64 (17784 * i) +
      BitVec.ofNat 64 (5928 * j)) (fm forms i j) := by
  have hF := Pre.fms h
  have hi' : i < forms.size := by rw [hF.size]; exact hi
  have hj' : j < forms[i].size := by rw [hF.row_size i hi']; exact hj
  have := hF.forms i hi' j hj'
  have e1 : forms.getD i #[] = forms[i] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some]
  have e2 : forms[i].getD j #[] = forms[i][j] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj', Option.getD_some]
  rw [fm, e1, e2]
  rw [NativeRustcVm.addr_add_add, show 17784 * i + 5928 * j = formBufBytes * (3 * i + j) by
    rw [formBufBytes_eq]; ring]
  exact this

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **A call of `evaluate`** on form `j` of table `i` (`b6`, `b7`, `b8`): the block saves
`r1`, `r2` at `o1`, `o2`. -/
theorem eval_step (h : TableTermsPre a s heights forms m0)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmArm.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    {ds : List Directive} {j0 : Nat} {S' : SState} (hb : ds.IsInfixAt Host.prog j0)
    (hx : exec ds formS = some (S', .call NativeRustcVmArm.Vm.Evaluate.entryLabel)) {j : Nat} (hj : j < 3)
    (ha : evalArgs (after ds formS) (5928 * j))
    (hW : wok (after ds formS) [288, 17784] [false, false] = true)
    {os : List Nat} (hos : fok (after ds formS) os = true)
    (hcos : ([16, 24, 32, 40, 48, 56] : List Nat).all (fun o ↦ os.contains o) = true)
    {o1 o2 : Nat} {r1 r2 : XReg} (ho1 : o1 + 8 ≤ 288) (ho2 : o2 + 8 ≤ 288)
    (l1 : loadSym (after ds formS).mem 0 o1 8 = .reg r1)
    (l2 : loadSym (after ds formS).mem 0 o2 8 = .reg r2)
    {R : MachineState → Prop} {i : Nat} (hi : i < 6) {o : Array (Array EW × Array EW)}
    {xs : Array EW} {s' : TState} {m : MachineData} (H : It a m0 i o xs s' m)
    {L : List (Nat × BitVec 64)} (hL : (L.map Prod.fst).all (fun o ↦ os.contains o) = true)
    (hw : FW m0 m L) (x28 : (m.regs.X28).toNat = (tb i).width) (hxs : xs.size = (tb i).width)
    (cont : ∀ m', It a m0 i o xs s' m' → FW m0 m' (L ++ [(o1, rg m r1), (o2, rg m r2)]) →
      (∀ r ∈ cs, m'.regs.getXReg r = m.regs.getXReg r) →
      ewRet m' = (fm forms i j).evaluate xs →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (j0 + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf j0⟩ := by
  have hS := Pre.stack h
  have hN := spN h
  have fr := form_rin h hi
  have hwf : (E1 m0 m (m0.regs.X7.toBitVec + BitVec.ofNat 64 (17784 * i)) 17784).WF :=
    wf1 hS H.fr.kept fr.1 fr.2.1
  have hm : Match (E1 m0 m (m0.regs.X7.toBitVec + BitVec.ofNat 64 (17784 * i)) 17784) formS m :=
    match1 hS H.fr.sp (by show rg m .X20 = _; rw [H.x20]; exact (BitVec.add_zero _).symm)
  refine exec_then hb hx hwf hm fun st hma0 hpc ↦ ?_
  have hma : Match (E1 m0 m (m0.regs.X7.toBitVec + BitVec.ofNat 64 (17784 * i)) 17784)
      (after ds formS) st.data := by rw [Bus.after_eq hx]; exact hma0
  obtain ⟨sp1, kc, a0, a1, a2, a3⟩ := ha
  have hfr1 := fr_block (szs := [288, 17784]) H.fr hN hm hma hwf (sp1.trans rfl) rfl
    (hout_none (L := [false, false]) (by decide)) hW
  have kr : ∀ r ∈ cs, st.data.regs.getXReg r = m.regs.getXReg r :=
    fun r hr ↦ rk hma (keeps_get kc hr)
  have It1 : It a m0 i o xs s' st.data :=
    It.step h hi H hfr1 (hma.kept hwf) (hma.sameOutside hwf)
      (fun q hq ↦ .inl (written_stack hN (wok_frame (by decide) hW) hq))
      (FW.block hma hwf (fun p hp ↦ by
        have := List.all_eq_true.mp hcos p.1 (by
          simp only [cws, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        simpa using this) hos H.cw)
      fun r hr ↦ kr r (it_cs r hr)
  have fw1 : FW m0 st.data (L ++ [(o1, rg m r1), (o2, rg m r2)]) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact FW.block hma hwf (fun p hp ↦ mem_of_all hL hp) hos hw p hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · show fw m0 st.data o1 = _
        rw [fw_write hma hwf ho1, l1]; rfl
      · show fw m0 st.data o2 = _
        rw [fw_write hma hwf ho2, l2]; rfl
  -- The form.
  have hfj : 5928 * j + 5928 ≤ 17784 := by omega
  have hform := form_at h hi hj
  have hfm : FormBufAt m.dmem (m0.regs.X7.toBitVec + BitVec.ofNat 64 (17784 * i) +
      BitVec.ofNat 64 (5928 * j)) (fm forms i j) :=
    FormBufAt.of_same hform (readIn_same h H.fr (rin_sub fr hfj))
  have hfs : FormBufAt st.data.dmem (m0.regs.X7.toBitVec + BitVec.ofNat 64 (17784 * i) +
      BitVec.ofNat 64 (5928 * j)) (fm forms i j) :=
    FormBufAt.of_same hform (readIn_same h hfr1 (rin_sub fr hfj))
  have hsz : (fm forms i j).size ≤ 148 := hfm.len_le
  have hcnt : (Sym.load 1 (5928 * j) 8).eval
      (E1 m0 m (m0.regs.X7.toBitVec + BitVec.ofNat 64 (17784 * i)) 17784) =
      (fm forms i j).size.toUInt64.toBitVec := by
    rw [ld1, NativeRustcVm.wordOf_of_wordAt hfm.len]
  have hlt : SBool.eval (E1 m0 m (m0.regs.X7.toBitVec + BitVec.ofNat 64 (17784 * i)) 17784)
      (.cmp .ult .W64 (.load 1 (5928 * j) 8) (.lit 149)) = true := by
    show CmpOp.ult.apply .W64 ((Sym.load 1 (5928 * j) 8).eval _) (BitVec.ofNat 64 149) = true
    rw [hcnt, cmp_ult_lit _ _ (by norm_num), toNat_toUInt64 (by omega)]
    exact decide_eq_true (by omega)
  have e0 : st.data.regs.X0.toBitVec = m0.regs.X7.toBitVec + BitVec.ofNat 64 (17784 * i) +
      BitVec.ofNat 64 (5928 * j) + BitVec.ofNat 64 8 := by
    show rg st.data .X0 = _
    rw [rv hma a0]
    simp only [Sym.eval, hlt, ↓reduceIte, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    show rg m .X20 + _ = _
    rw [H.x20, NativeRustcVm.addr_add_add _ (5928 * j) 8]
    rfl
  have e1 : st.data.regs.X1.toNat = (fm forms i j).size := by
    show (rg st.data .X1).toNat = _
    rw [rv hma a1]
    simp only [Sym.eval, hlt, ↓reduceIte]
    rw [show (E1 m0 m (m0.regs.X7.toBitVec + BitVec.ofNat 64 (17784 * i)) 17784).load 1
      (5928 * j) 8 = (fm forms i j).size.toUInt64.toBitVec from hcnt]
    exact toNat_toUInt64 (by omega)
  have e2 : st.data.regs.X2.toBitVec = evi m0 i + BitVec.ofNat 64 496 := by
    show rg st.data .X2 = _
    rw [rv hma a2]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    exact congrArg (· + BitVec.ofNat 64 496) H.x27
  have e3 : st.data.regs.X3.toNat = (tb i).width := by
    show (rg st.data .X3).toNat = _
    rw [rv hma a3]
    exact x28
  have hle := ev_le
  have hsub : 496 + 16 * (tb i).width ≤ 1968 := by have := width_le hi; omega
  have eos := outOk_sub (evi_out h hi) hsub
  have hterm : 5928 * j + 8 + termBytes * (fm forms i j).size ≤ 17784 := by
    unfold termBytes; omega
  have tr := rin_sub fr hterm
  rw [← NativeRustcVm.addr_add_add] at tr
  have hpre : EvaluatePre (fm forms i j) st.data := by
    simp only [EvaluatePre]
    rw [e0, e1, SliceOk, e2, e3]
    exact ⟨hfr1.stackOk hS rfl hle, rfl, hfs.terms, Bus.Fr.readable hfr1 tr.1,
      Bus.Fr.offStack hfr1 hS tr.2.1 hle, Bus.Fr.readable hfr1 ⟨eos.1, eos.2.1⟩,
      Bus.Fr.offStack hfr1 hS eos.2.2.2.2.1 hle⟩
  have hsl : slice st.data st.data.regs.X2 st.data.regs.X3 = xs := by
    refine slice_of_ewsAt ?_ (e3.trans hxs.symm)
    rw [e2]
    have := It1.vals.2.2
    rwa [show evi m0 i + BitVec.ofNat 64 488 + 8#64 = evi m0 i + BitVec.ofNat 64 496 from
      NativeRustcVm.addr_add_add _ 488 8] at this
  refine Bus.Gkr.Fr.callSpec hfr1 hN hle (fun _ h ↦ nomatch h) slots_le (outs_frame h)
    (hev (fm forms i j)) ⟨hpc.1, hpc.2⟩ hpre (fun m' hq ↦ ⟨Bus.changes_zero hq.2.1, hq.2.2⟩)
    fun m2 hfr2 hq2 hcs2 ↦ ?_
  have hs2 : SameOutside st.data.dmem m2.dmem
      (fun q ↦ InRange (stackBelow st.data evaluateStack) evaluateStack q ∨ False) :=
    Bus.changes_zero hq2.2.1
  refine cont m2 (It.call h hi It1 hfr2 hle hs2 (fun _ h ↦ h.elim) (fun _ _ _ _ h ↦ h) hq2.2.2)
    (FW.call hfr1.sp (le_trans hle hN) hs2
      (fun p hp ↦ by
        rcases List.mem_append.mp hp with hp | hp
        · exact fok_le hos (mem_of_all hL hp)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact ho1
          · exact ho2)
      (fun _ _ _ _ h ↦ h) fw1)
    (fun r hr ↦ by rw [hcs2 r (cs_saved r hr), kr r hr]) ?_
  rw [hq2.1, hsl]

end

end NativeRustcVmArm.Tables.TableTerms
