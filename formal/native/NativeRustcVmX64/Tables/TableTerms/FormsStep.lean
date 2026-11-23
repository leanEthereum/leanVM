module

public import NativeRustcVmX64.Tables.TableTerms.Forms
public import NativeRustcVmX64.Code.Vm.Evaluate.Names

/-!
# `table_terms`: the forms' dot product, run (x86-64)

`b6` to `b8` each save the previous call's result in the frame and call `evaluate` on one of
table `i`'s three forms (`form_blk`); `b9` saves the last, loads the table's weight into the frame
and calls `dot` of the form powers with the three values (`forms_step`): `dotF` in RAX, RDX.
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf ewOf)

@[expose] public section

/-- Table `i`'s forms' region. -/
abbrev fR (m0 : MachineData) (i : Nat) : BitVec 64 := fA m0 + BitVec.ofNat 64 (17784 * i)

/-- Table `i`'s weight. -/
def wt (m0 : MachineData) (i : Nat) : EW := (wts m0).getD i 0

/-- Two words of an `E` element. -/
def ewW (o : Nat) (x : EW) : List (Nat × UInt64) := [(o, x.c0), (o + 8, x.c1)]

end

public section

theorem toNat_toUInt64' {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simpa [Nat.toUInt64] using h

theorem fR_off (m0 : MachineData) (i j : Nat) :
    off (fA m0) (formBufBytes * (3 * i + j)) = fR m0 i + BitVec.ofNat 64 (5928 * j) := by
  unfold off
  rw [NativeRustcVm.addr_add_add]
  congr 2
  unfold formBufBytes termBytes formCap
  ring

theorem ewW_le {o : Nat} {x : EW} (h1 : 8 ≤ o) (h2 : o + 16 ≤ 280) :
    ∀ p ∈ ewW o x, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280 := by
  intro p hp
  simp only [ewW, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨h1, by omega⟩
  · exact ⟨by omega, by omega⟩

/-- The frame's `E` element from its two words. -/
theorem ewAt_of_ewW {m0 d : MachineData} {o : Nat} {x : EW} (h : FW m0 d (ewW o x)) :
    NativeRustcVm.EWAt d.dmem (off (fb m0) o) x := by
  rw [ewAt_iff, off_off]
  exact ⟨h (o, x.c0) (List.mem_cons_self), h (o + 8, x.c1) (List.mem_cons_of_mem _
    (List.mem_singleton_self _))⟩

/-- The frame's two `E` element words, written. -/
theorem ewW_wrote [Labels] {m0 d d' : MachineData} {rest : List (BitVec 64 × Nat)}
    {ret : BitVec 64} {Sy : SState} (hm : Match (E m0 d rest ret) Sy d') {o : Nat}
    (hle : o + 16 ≤ 280) {v0 v1 : Sym} (h0 : WordW 0 o v0 Sy) (h1 : WordW 0 (o + 8) v1 Sy)
    {x : EW} (e0 : v0.eval (E m0 d rest ret) = x.c0.toBitVec)
    (e1 : v1.eval (E m0 d rest ret) = x.c1.toBitVec) : FW m0 d' (ewW o x) := by
  intro p hp
  simp only [ewW, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact wroteW hm (by omega) h0 e0
  · exact wroteW hm (by omega) h1 e1

section
variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

/-- The forms' region of table `i` in a block's environment: the alias of R13. -/
theorem r13_alias {d : MachineData} {i : Nat} {ret : BitVec 64}
    (h13 : reg d .r13 = fA m0 + BitVec.ofNat 64 (11864 + 17784 * i)) :
    (Sym.reg .r13).eval (E m0 d [(fR m0 i, 17784)] ret) =
      (E m0 d [(fR m0 i, 17784)] ret).base 1 + BitVec.ofInt 64 11864 := by
  show reg d .r13 = fR m0 i + BitVec.ofInt 64 11864
  rw [h13, show BitVec.ofInt 64 11864 = BitVec.ofNat 64 11864 from rfl, NativeRustcVm.addr_add_add,
    Nat.add_comm]

/-- **A form's length**, loaded from its region. -/
theorem ld_form (h : TableTermsPre a s heights forms m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) o d) {i j : Nat} (hi : i < forms.size)
    (hj : j < forms[i].size) {ret : BitVec 64} :
    (Sym.load 1 (5928 * j) 8).eval (E m0 d [(fR m0 i, 17784)] ret) =
      BitVec.ofNat 64 forms[i][j].size := by
  have hF := form_at h hb hi hj
  have hl := hF.len_le
  unfold formCap at hl
  rw [fR_off] at hF
  show (E m0 d [(fR m0 i, 17784)] ret).load 1 (5928 * j) 8 = _
  rw [load_of_wordAt' hF.len]
  apply BitVec.eq_of_toNat_eq
  rw [UInt64.toNat_toBitVec, toNat_ofNat_lt (by omega)]
  exact toNat_toUInt64' (by omega)

/-- `cF o` of a form's length: false. -/
theorem cF_false (h : TableTermsPre a s heights forms m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) o d) {i j : Nat} (hi : i < forms.size)
    (hj : j < forms[i].size) {ret : BitVec 64} :
    (cF (5928 * j)).eval (E m0 d [(fR m0 i, 17784)] ret) = false := by
  have hl := (form_at h hb hi hj).len_le
  unfold formCap at hl
  unfold cF
  rw [eval_not', eval_ult, ld_form h hb hi hj]
  simp only [Sym.eval, toNat_ofNat_lt (show forms[i][j].size < 2 ^ 64 by omega),
    toNat_ofNat_lt (show 149 < 2 ^ 64 by omega), decide_eq_true (show forms[i][j].size < 149 by omega),
    Bool.not_true]

/-- **The weight words**, loaded from the weight's region. -/
theorem ld_wt (h : TableTermsPre a s heights forms m0) {o : Nat} {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) o d) {i : Nat} (hi : i < 6) {ret : BitVec 64} :
    (Sym.load 2 0 8).eval (E m0 d [(argA m0, 32), (wA m0 + BitVec.ofNat 64 (16 * i), 16)] ret) =
      (wt m0 i).c0.toBitVec ∧
    (Sym.load 2 8 8).eval (E m0 d [(argA m0, 32), (wA m0 + BitVec.ofNat 64 (16 * i), 16)] ret) =
      (wt m0 i).c1.toBitVec := by
  have hs := same_readIn h hb (w_rin h hi)
  have hw : wt m0 i = ewOf d.dmem (wA m0 + BitVec.ofNat 64 (16 * i)) := by
    unfold wt wts
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_eq_getElem (by simp [nTables]; omega), Option.getD_some,
      NativeRustcVm.getElem_ewsOf]
    exact (NativeRustcVm.ewOf_congr fun j hj ↦ hs j hj).symm
  have hb2 : (E m0 d [(argA m0, 32), (wA m0 + BitVec.ofNat 64 (16 * i), 16)] ret).base 2 =
      wA m0 + BitVec.ofNat 64 (16 * i) := rfl
  rw [hw]
  constructor
  · show (E m0 d _ ret).load 2 0 8 = _
    rw [load_eq_wordOf, hb2, NativeRustcVm.addr_add_zero]
    rfl
  · show (E m0 d _ ret).load 2 8 8 = _
    rw [load_eq_wordOf, hb2]
    rfl

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **A form block** (`b6`, `b7`, `b8`): from the body, the forms' region in its environment,
`evaluate` of form `j`, the previous result saved at `o`. -/
theorem form_blk (h : TableTermsPre a s heights forms m0)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmX64.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    {i j : Nat} (hi : i < 6) (hj : j < 3) {o0 : Array (Array EW × Array EW)} {xs : Array EW}
    {s' : TState} {ds : List Directive} {kk : Nat} (hk : ds.IsInfixAt Host.prog kk)
    {Sy : SState} (hx : exec ds formS = some (Sy, .call NativeRustcVmX64.Vm.Evaluate.entryLabel))
    {ex : List Nat} (hmiss : missO Sy (UW ex) = true) (hmid : MidOk 272 0 slots Sy = true)
    (hW : WrOk Sy [] = true) {o : Nat} (ho : 8 ≤ o ∧ o + 16 ≤ 280)
    (h0 : WordW 0 o (.reg .rax) Sy) (h1 : WordW 0 (o + 8) (.reg .rdx) Sy)
    {vdi vsi : Sym} (hdi : Sy.reg .rdi = some vdi) (hsi : Sy.reg .rsi = some vsi)
    (hdx : Sy.reg .rdx = some (.reg .rbx)) (hcx : Sy.reg .rcx = some (.reg .r12))
    (hcs : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13], Sy.reg r = some (.reg r))
    {d : MachineData} (hb : Bd m0 272 N slots (outs m0) 8 d) (H : It a m0 i o0 xs s' d)
    (hxs : xs.size = (tb i).width)
    (h13 : reg d .r13 = fA m0 + BitVec.ofNat 64 (11864 + 17784 * i))
    (hbx : reg d .rbx = evi m0 i + BitVec.ofNat 64 496)
    (h12 : reg d .r12 = BitVec.ofNat 64 (tb i).width)
    (hvdi : vdi.eval (E m0 d [(fR m0 i, 17784)] (Host.addrOf (kk + ds.length)).toBitVec) =
      off (fA m0) (formBufBytes * (3 * i + j)) + BitVec.ofNat 64 8)
    (hvsi : ∀ (hi' : i < forms.size) (hj' : j < forms[i].size),
      vsi.eval (E m0 d [(fR m0 i, 17784)] (Host.addrOf (kk + ds.length)).toBitVec) =
        BitVec.ofNat 64 forms[i][j].size)
    {L : List (Nat × UInt64)} (hL : ∀ p ∈ L, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280)
    (hLU : (L.map Prod.fst).all (fun o ↦ (UW ex).contains o) = true) (hfw : FW m0 d L)
    {x : EW} (hrax : reg d .rax = x.c0.toBitVec) (hrdx : reg d .rdx = x.c1.toBitVec)
    {R : MachineState → Prop}
    (cont : ∀ d', Bd m0 272 N slots (outs m0) 8 d' → FW m0 d' (L ++ ewW o x) →
      It a m0 i o0 xs s' d' →
      ewRet d' = ((forms.getD i #[]).getD j #[]).evaluate xs →
      reg d' .r13 = reg d .r13 → reg d' .rbx = reg d .rbx → reg d' .r12 = reg d .r12 →
      reg d' .rbp = reg d .rbp →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (kk + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf kk⟩ := by
  have hi' : i < forms.size := by rw [forms_size h]; exact hi
  have hj' : j < forms[i].size := by rw [forms_row h hi']; exact hj
  let ra := (Host.addrOf (kk + ds.length)).toBitVec
  have hwf : (E m0 d [(fR m0 i, 17784)] ra).WF := wf_form h hi hb.fr.kept
  have hm : Match (E m0 d [(fR m0 i, 17784)] ra) formS d :=
    match_body hb ⟨rfl, rfl, trivial⟩ ⟨r13_alias h13, trivial⟩
  refine exec_then hk hx hwf (fun _ _ ↦ rfl) hm fun st hm' hpc ↦ ?_
  have hb1 := (blockB h hb hwf hm' hmid hW nofun).1
  have it1 := it_block h hi H hwf hm' hmid hW
  have rg : ∀ {r : Reg64} {v : Sym}, Sy.reg r = some v →
      reg st.data r = v.eval (E m0 d [(fR m0 i, 17784)] ra) := fun hv ↦ hm'.regs _ _ hv
  have fw1 : FW m0 st.data (L ++ ewW o x) :=
    FW.append (fw_blockU hwf hm' (writesIn_of_mid hmid) hmiss hLU (fun p hp ↦ (hL p hp).2) hfw)
      (ewW_wrote hm' ho.2 h0 h1 hrax hrdx)
  have kr : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13], reg st.data r = reg d r := fun r hr ↦ by
    rw [rg (hcs r hr)]; rfl
  simp only [PcOk] at hpc
  have hF := form_at h hb1 hi' hj'
  refine eval_call h hev hi hj hpc hb1 it1 hxs (by rw [rg hdi]; exact hvdi) hF
    (by rw [rg hsi, hvsi hi' hj', toNat_ofNat_lt]; have := hF.len_le; unfold formCap at this; omega)
    (by rw [rg hdx]; exact hbx) (by rw [rg hcx]; exact h12)
    (fun p hp ↦ by
      rcases List.mem_append.mp hp with hp | hp
      · exact hL p hp
      · exact ewW_le ho.1 ho.2 p hp) fw1 fun d' hb' fw' it' hev' hcs' ↦ ?_
  refine cont d' hb' fw' it' ?_ ?_ ?_ ?_ ?_
  · rw [hev', NativeVm.Math.Tables.getD_eq_getElem' _ _ hi',
      NativeVm.Math.Tables.getD_eq_getElem' _ _ hj']
  · rw [hcs' .r13 rfl, kr .r13 (by simp)]
  · rw [hcs' .rbx rfl, kr .rbx (by simp)]
  · rw [hcs' .r12 rfl, kr .r12 (by simp)]
  · rw [hcs' .rbp rfl, kr .rbp (by simp)]

end

end NativeRustcVmX64.Tables.TableTerms
