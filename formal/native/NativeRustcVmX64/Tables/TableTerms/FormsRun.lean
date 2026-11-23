module

public import NativeRustcVmX64.Tables.TableTerms.FormsStep
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.Evaluate.Names

/-!
# `table_terms`: the three forms and their dot product (x86-64)

`forms_step`: from after the constraints' dot product (`b6` at `k + NativeRustcVmX64.Vm.TableTerms.b6Offset`), `b6` to `b8` evaluate
table `i`'s three forms, `b9` saves the table's weight and calls `dot` of the form powers with the
three values; at `b10` (`k + NativeRustcVmX64.Vm.TableTerms.b10Offset`) RAX, RDX hold `dotF`, the frame the constraints' dot product
(`80`), the weight (`72`, `64`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf ewOf)

@[expose] public section

/-- The frame's words for the constraint count and the cursor. -/
def ncW (i : Nat) : List (Nat × UInt64) :=
  [(96, .ofBitVec (BitVec.ofNat 64 (tb i).nConstraints)),
    (104, .ofBitVec (BitVec.ofNat 64 (cursorAt i)))]

/-- The weight's words: limb `0` at `72`, limb `1` at `64`. -/
def wW (w : EW) : List (Nat × UInt64) := [(72, w.c0), (64, w.c1)]

end

public section

theorem FW.sub {m0 d : MachineData} {L L' : List (Nat × UInt64)} (h : FW m0 d L)
    (hs : ∀ p ∈ L', p ∈ L) : FW m0 d L' := fun p hp ↦ h p (hs p hp)

theorem form_rdi (m0 : MachineData) (i j : Nat) :
    off (fA m0) (formBufBytes * (3 * i + j)) + BitVec.ofNat 64 8 =
      fA m0 + BitVec.ofNat 64 (17784 * i + 5928 * j + 8) := by
  rw [fR_off, NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add, Nat.add_assoc]

theorem r13_sub (x : BitVec 64) (i c : Nat) (hc : c ≤ 11864) :
    x + BitVec.ofNat 64 (11864 + 17784 * i) + BitVec.ofNat 64 (2 ^ 64 - c) =
      x + BitVec.ofNat 64 (11864 + 17784 * i - c) :=
  addr_sub x (by omega) (by omega)

/-- The three values of a form row `fs` of three forms. -/
theorem map3 {fs : Array FormW} (h : fs.size = 3) (g : FormW → EW) :
    fs.map g = #[g (fs.getD 0 #[]), g (fs.getD 1 #[]), g (fs.getD 2 #[])] := by
  rcases fs with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, l⟩⟩⟩⟩⟩
  all_goals simp at h
  simp

theorem mapL0 (m0 : MachineData) (i : Nat) (f : EW) :
    (cws m0 ++ lw m0 i f ++ tw112 i ++ ncW i).map Prod.fst =
      [8, 24, 32, 40, 48, 56, 16, 120, 128, 136, 112, 96, 104] := rfl

theorem map_ewW (o : Nat) (x : EW) : (ewW o x).map Prod.fst = [o, o + 8] := rfl

theorem ofNat_mul2 (n : Nat) :
    BitVec.ofNat 64 (8 * n) * BitVec.ofNat 64 2 = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem ewRet_c0 {d : MachineData} {x : EW} (h : ewRet d = x) : reg d .rax = x.c0.toBitVec := by
  rw [← h]; rfl

theorem ewRet_c1 {d : MachineData} {x : EW} (h : ewRet d = x) : reg d .rdx = x.c1.toBitVec := by
  rw [← h]; rfl

theorem le_app {L : List (Nat × UInt64)} {o : Nat} {x : EW}
    (hL : ∀ p ∈ L, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280) (h1 : 8 ≤ o) (h2 : o + 16 ≤ 280) :
    ∀ p ∈ L ++ ewW o x, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280 := fun p hp ↦ by
  rcases List.mem_append.mp hp with hp | hp
  · exact hL p hp
  · exact ewW_le h1 h2 p hp

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **The forms' dot product.** -/
theorem forms_step (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmX64.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    {i : Nat} (hi : i < 6) {acc : Acc} {si : TState} {xs : Array EW} {s' : TState}
    {d : MachineData} (H : Cm a s heights forms m0 i acc si xs s' d)
    (hrax : reg d .rax = (dotC m0 i (cursorAt i) xs).c0.toBitVec)
    (hrdx : reg d .rdx = (dotC m0 i (cursorAt i) xs).c1.toBitVec)
    (hnc : FW m0 d (ncW i))
    (h12 : reg d .r12 = BitVec.ofNat 64 (tb i).width)
    (hbx : reg d .rbx = evi m0 i + BitVec.ofNat 64 496)
    (h13 : reg d .r13 = fA m0 + BitVec.ofNat 64 (11864 + 17784 * i))
    (cont : ∀ d', Cm a s heights forms m0 i acc si xs s' d' →
      FW m0 d' (ncW i ++ ewW 80 (dotC m0 i (cursorAt i) xs) ++ wW (wt m0 i)) →
      reg d' .rax = (dotF m0 (forms.getD i #[]) xs).c0.toBitVec →
      reg d' .rdx = (dotF m0 (forms.getD i #[]) xs).c1.toBitVec →
      reg d' .r12 = BitVec.ofNat 64 (8 * i) →
      reg d' .r13 = fA m0 + BitVec.ofNat 64 (11864 + 17784 * i) →
      Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b10Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b6Offset)⟩ := by
  have hS := Pre.stack h
  have hi' : i < forms.size := by rw [forms_size h]; exact hi
  have hrow := forms_row h hi'
  have hxs : xs.size = (tb i).width := NativeRustcVm.Sumcheck.readScalars_size H.rs
  have L0 : ∀ p ∈ cws m0 ++ lw m0 i acc.2.1 ++ tw112 i ++ ncW i, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨(fwL_le p hp).1, (fwL_le p hp).2.1⟩
    · simp only [ncW, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact ⟨by simp, by simp⟩
  -- `b6`: form `0`.
  obtain ⟨miss6, mid6, W6, -, w80, w88, rsi6, rdi6, rdx6, rcx6, -, k6⟩ := ok_b6
  have kk6 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13], (after b6 formS).reg r = some (.reg r) := by
    intro r hr
    have := List.all_eq_true.mp k6 r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> simp)
    simpa using this
  refine form_blk h hev hi (j := 0) (by omega) (infix_of b6_in_code (by simp [b6]) hp)
    exit_b6 miss6 mid6 W6 (o := 80) ⟨by omega, by omega⟩ w80 w88 rdi6 rsi6 rdx6 rcx6 kk6
    H.bd H.it hxs h13 hbx h12 ?_ ?_ (L := cws m0 ++ lw m0 i acc.2.1 ++ tw112 i ++ ncW i) L0
    (by rw [mapL0]; decide)
    (FW.append H.fw hnc) hrax hrdx fun d1 hb1 fw1 it1 ev1 r13a rbxa r12a _ ↦ ?_
  · rw [eval_ite, show cF 0 = cF (5928 * 0) from rfl, cF_false h H.bd hi' (by omega)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [eval_add_lit, eval_reg, h13, show (18446744073709539760 : Nat) = 2 ^ 64 - 11856 from rfl,
      r13_sub _ _ _ (by omega), form_rdi, show 11864 + 17784 * i - 11856 = 17784 * i + 5928 * 0 + 8
      by omega]
  · intro hi'' hj''
    rw [eval_ite, show cF 0 = cF (5928 * 0) from rfl, cF_false h H.bd hi'' hj'']
    exact ld_form h H.bd hi'' hj''
  -- `b7`: form `1`.
  obtain ⟨miss7, mid7, W7, -, w176, w184, rsi7, rdi7, rdx7, rcx7, k7⟩ := ok_b7
  have kk7 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13], (after b7 formS).reg r = some (.reg r) := by
    intro r hr
    have := List.all_eq_true.mp k7 r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> simp)
    simpa using this
  have h13' : reg d1 .r13 = fA m0 + BitVec.ofNat 64 (11864 + 17784 * i) := r13a.trans h13
  have L1 := le_app (x := dotC m0 i (cursorAt i) xs) L0 (o := 80) (by omega) (by omega)
  rw [Nat.add_assoc, NativeRustcVmX64.Vm.TableTerms.b6_next]
  refine form_blk h hev hi (j := 1) (by omega) (infix_of b7_in_code (by simp [b7]) hp)
    exit_b7 miss7 mid7 W7 (o := 176) ⟨by omega, by omega⟩ w176 w184 rdi7 rsi7 rdx7 rcx7 kk7
    hb1 it1 hxs h13' (rbxa.trans hbx) (r12a.trans h12) ?_ ?_ L1
    (by rw [List.map_append, mapL0, map_ewW]; decide) fw1 (ewRet_c0 ev1)
    (ewRet_c1 ev1) fun d2 hb2 fw2 it2 ev2 r13b rbxb r12b _ ↦ ?_
  · rw [eval_ite, show cF 5928 = cF (5928 * 1) from rfl, cF_false h hb1 hi' (by omega)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [eval_add_lit, eval_reg, h13', show (18446744073709545688 : Nat) = 2 ^ 64 - 5928 from rfl,
      r13_sub _ _ _ (by omega), form_rdi, show 11864 + 17784 * i - 5928 = 17784 * i + 5928 * 1 + 8
      by omega]
  · intro hi'' hj''
    rw [eval_ite, show cF 5928 = cF (5928 * 1) from rfl, cF_false h hb1 hi'' hj'']
    exact ld_form h hb1 hi'' hj''
  -- `b8`: form `2`.
  obtain ⟨miss8, mid8, W8, -, w192, w200, rsi8, rdi8, rdx8, rcx8, k8⟩ := ok_b8
  have kk8 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13], (after b8 formS).reg r = some (.reg r) := by
    intro r hr
    have := List.all_eq_true.mp k8 r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> simp)
    simpa using this
  have h13'' : reg d2 .r13 = fA m0 + BitVec.ofNat 64 (11864 + 17784 * i) := r13b.trans h13'
  have L2 := le_app (x := ((forms.getD i #[]).getD 0 #[]).evaluate xs) L1 (o := 176)
    (by omega) (by omega)
  rw [Nat.add_assoc, NativeRustcVmX64.Vm.TableTerms.b7_next]
  refine form_blk h hev hi (j := 2) (by omega) (infix_of b8_in_code (by simp [b8]) hp)
    exit_b8 miss8 mid8 W8 (o := 192) ⟨by omega, by omega⟩ w192 w200 rdi8 rsi8 rdx8 rcx8 kk8
    hb2 it2 hxs h13'' (rbxb.trans (rbxa.trans hbx)) (r12b.trans (r12a.trans h12)) ?_ ?_ L2
    (by rw [List.map_append, List.map_append, mapL0, map_ewW, map_ewW]; decide) fw2
    (ewRet_c0 ev2) (ewRet_c1 ev2) fun d3 hb3 fw3 it3 ev3 r13c rbxc r12c _ ↦ ?_
  · have hc : (SBool.cmp .ult .W64 (.load 1 11856 8) (.lit 149)).eval
        (E m0 d2 [(fR m0 i, 17784)] (Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b8Offset + b8.length)).toBitVec) = true := by
      have := cF_false h hb2 hi' (j := 2) (by omega)
        (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b8Offset + b8.length)).toBitVec)
      unfold cF at this
      rw [eval_not'] at this
      simpa using this
    rw [eval_ite, hc]
    simp only [↓reduceIte]
    rw [eval_reg, h13'', form_rdi, show 11864 + 17784 * i = 17784 * i + 5928 * 2 + 8 by omega]
  · intro hi'' hj''
    rw [eval_ite, show cF 11856 = cF (5928 * 2) from rfl, cF_false h hb2 hi'' hj'']
    exact ld_form h hb2 hi'' hj''
  -- `b9`: the last value, the weight, `dot`.
  have L3 := le_app (x := ((forms.getD i #[]).getD 1 #[]).evaluate xs) L2 (o := 192)
    (by omega) (by omega)
  rw [Nat.add_assoc, NativeRustcVmX64.Vm.TableTerms.b8_next]
  let ra := (Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b9Offset + b9.length)).toBitVec
  have hwf9 : (E m0 d3 [(argA m0, 32), (wA m0 + BitVec.ofNat 64 (16 * i), 16)] ra).WF :=
    wf_w h hi hb3.fr.kept
  have fwA : FW m0 d3 (cws m0 ++ lw m0 i acc.2.1) :=
    FW.left (FW.left (FW.left (FW.left (FW.left fw3))))
  have w136 : NativeRustcVm.WordAt d3.dmem (off (fb m0) 136) (.ofBitVec (BitVec.ofNat 64 (8 * i))) :=
    lw136 (FW.right fwA)
  have w32 : NativeRustcVm.WordAt d3.dmem (off (fb m0) 32) (.ofBitVec (reg m0 .rcx)) :=
    cws32 (FW.left fwA)
  have l136 : (Sym.load 0 136 8).eval
      (E m0 d3 [(argA m0, 32), (wA m0 + BitVec.ofNat 64 (16 * i), 16)] ra) =
      BitVec.ofNat 64 (8 * i) := ld0 w136
  have hm9 : Match (E m0 d3 [(argA m0, 32), (wA m0 + BitVec.ofNat 64 (16 * i), 16)] ra) wS d3 := by
    refine match_body hb3 ⟨rfl, rfl, rfl, trivial⟩ ⟨?_, ?_, trivial⟩
    · show stackBelow m0 272 + BitVec.ofInt 64 296 = argA m0 + BitVec.ofInt 64 16
      rw [show BitVec.ofInt 64 296 = BitVec.ofNat 64 (272 + 24) from rfl,
        show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl]
      rw [show stackBelow m0 272 + BitVec.ofNat 64 (272 + 24) = off (stackBelow m0 272) (272 + 24)
        from rfl, frame_add]
      unfold argA
      rw [NativeRustcVm.addr_add_add]
    · show (Sym.bin .add .W64 (.load 1 16 8) (.bin .mul .W64 (.load 0 136 8) (.lit 2))).eval _ =
        wA m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 0
      rw [eval_add']
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [show (E m0 d3 [(argA m0, 32), (wA m0 + BitVec.ofNat 64 (16 * i), 16)] ra).load 0 136 8 =
        BitVec.ofNat 64 (8 * i) from l136, ofNat_mul2, ofInt_zero64, BitVec.add_zero]
      show (E m0 d3 _ ra).load 1 (8 * 2) 8 + _ = _
      rw [load_eq_wordOf]
      exact congrArg (· + _) (arg_word h hb3 (j := 2) (by omega))
  refine exec_then (infix_of b9_in_code (by simp [b9]) hp) exit_b9 hwf9 (fun _ _ ↦ rfl) hm9
    fun st9 hm9' hpc9 ↦ ?_
  obtain ⟨miss9, mid9, W9, -, w208, w216, w72, w64, rdi9, rsi9, rdx9, rcx9, r12_9, k9⟩ := ok_b9
  have hb9 := (blockB h hb3 hwf9 hm9' mid9 W9 nofun).1
  have it9 := it_block h hi it3 hwf9 hm9' mid9 W9
  have rg9 : ∀ {r : Reg64} {v : Sym}, (after b9 wS).reg r = some v →
      reg st9.data r = v.eval (E m0 d3 [(argA m0, 32), (wA m0 + BitVec.ofNat 64 (16 * i), 16)] ra) :=
    fun hv ↦ hm9'.regs _ _ hv
  obtain ⟨lw0, lw1⟩ := ld_wt h hb3 hi (ret := ra)
  have L4 := le_app (x := ((forms.getD i #[]).getD 2 #[]).evaluate xs) L3 (o := 208)
    (by omega) (by omega)
  have fw9 : FW m0 st9.data
      ((cws m0 ++ lw m0 i acc.2.1 ++ tw112 i ++ ncW i ++ ewW 80 (dotC m0 i (cursorAt i) xs) ++
        ewW 176 (((forms.getD i #[]).getD 0 #[]).evaluate xs) ++
        ewW 192 (((forms.getD i #[]).getD 1 #[]).evaluate xs)) ++
        ewW 208 (((forms.getD i #[]).getD 2 #[]).evaluate xs) ++ wW (wt m0 i)) := by
    have hU : ((cws m0 ++ lw m0 i acc.2.1 ++ tw112 i ++ ncW i ++
        ewW 80 (dotC m0 i (cursorAt i) xs) ++
        ewW 176 (((forms.getD i #[]).getD 0 #[]).evaluate xs) ++
        ewW 192 (((forms.getD i #[]).getD 1 #[]).evaluate xs)).map Prod.fst).all
        (fun o ↦ (UW [64, 72]).contains o) = true := by
      rw [List.map_append, List.map_append, List.map_append, mapL0, map_ewW, map_ewW, map_ewW]
      decide
    refine FW.append (FW.append (fw_blockU hwf9 hm9' (writesIn_of_mid mid9) miss9 hU
      (fun p hp ↦ (L3 p hp).2) fw3)
      (ewW_wrote hm9' (by omega) w208 w216 (ewRet_c0 ev3) (ewRet_c1 ev3))) ?_
    intro p hp
    simp only [wW, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact wroteW hm9' (by omega) w72 lw0
    · exact wroteW hm9' (by omega) w64 lw1
  -- `dot`.
  have hS9 := hb9
  have hle : 272 + dotStack ≤ N := by rw [N_eq]; decide
  have erdi : reg st9.data .rdi = reg m0 .rcx := by
    rw [rg9 rdi9]; exact ld0 w32
  have ersi : reg st9.data .rsi = BitVec.ofNat 64 3 := by rw [rg9 rsi9]; rfl
  have erdx : reg st9.data .rdx = off (fb m0) 176 := by rw [rg9 rdx9]; exact eval_ptr0 176
  have ercx : reg st9.data .rcx = BitVec.ofNat 64 3 := by rw [rg9 rcx9]; rfl
  have hpre : DotPre st9.data := by
    unfold DotPre SliceOk
    rw [erdi, ersi, erdx, ercx, show (BitVec.ofNat 64 3).toNat = 3 from rfl]
    exact ⟨hb9.stackOk_at hS (Nat.zero_le _) (by simpa using hle),
      rd_callee h hb9 hle (Pre.fp h).1.1 (Pre.fp h).1.2 (Pre.fp h).2.1,
      fr_callee h hb9 hle (j := 176) (l := 48) (by omega) (by omega) (by omega)⟩
  simp only [PcOk] at hpc9
  refine call_then (env := E m0 d3 [(argA m0, 32), (wA m0 + BitVec.ofNat 64 (16 * i), 16)] ra)
    hpc9 hdot hpre fun st10 hpc10 hrsp10 hq10 ↦ ?_
  obtain ⟨p0, p1, p2⟩ := hq10
  unfold Changes at p1
  have hL5 := le_app (x := ((forms.getD i #[]).getD 2 #[]).evaluate xs) L3 (o := 208)
    (by omega) (by omega)
  have hL6 : ∀ p ∈ (cws m0 ++ lw m0 i acc.2.1 ++ tw112 i ++ ncW i ++
      ewW 80 (dotC m0 i (cursorAt i) xs) ++
      ewW 176 (((forms.getD i #[]).getD 0 #[]).evaluate xs) ++
      ewW 192 (((forms.getD i #[]).getD 1 #[]).evaluate xs)) ++
      ewW 208 (((forms.getD i #[]).getD 2 #[]).evaluate xs) ++ wW (wt m0 i),
      8 ≤ p.1 ∧ p.1 + 8 ≤ 280 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hL5 p hp
    · simp only [wW, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact ⟨by simp, by simp⟩
  have hb9' : Bd m0 272 N slots (outs m0) 0 st9.data := hb9
  obtain ⟨hb10, fw10, it10⟩ := pure_call h hi hb9' hle p2 hrsp10 p1 hL6 fw9 it9
  have hfr : slice st9.data (reg m0 .rcx) (BitVec.ofNat 64 3) = fpw m0 := by
    rw [slice_same (same_readIn h hb9 (Pre.fp h)) (by decide)]
    rfl
  have hfv : slice st9.data (off (fb m0) 176) (BitVec.ofNat 64 3) =
      #[((forms.getD i #[]).getD 0 #[]).evaluate xs, ((forms.getD i #[]).getD 1 #[]).evaluate xs,
        ((forms.getD i #[]).getD 2 #[]).evaluate xs] := by
    have e : NativeRustcVm.EWsAt st9.data.dmem (off (fb m0) 176)
        [((forms.getD i #[]).getD 0 #[]).evaluate xs, ((forms.getD i #[]).getD 1 #[]).evaluate xs,
          ((forms.getD i #[]).getD 2 #[]).evaluate xs] := by
      rw [ewsAt_cons, ewsAt_cons, ewsAt_cons, off_off, off_off]
      exact ⟨ewAt_of_ewW fw9.left.left.left.right, ewAt_of_ewW fw9.left.left.right,
        ewAt_of_ewW fw9.left.right, ewsAt_nil _ _⟩
    unfold slice
    have := NativeRustcVm.ewsOf_of_ewsAt e
    rw [show (BitVec.ofNat 64 3).toNat = 3 from rfl]
    rw [show (3 : Nat) = [((forms.getD i #[]).getD 0 #[]).evaluate xs,
      ((forms.getD i #[]).getD 1 #[]).evaluate xs,
      ((forms.getD i #[]).getD 2 #[]).evaluate xs].length from rfl, this]
  rw [erdi, ersi, erdx, ercx, hfr, hfv] at p0
  have hdf : dotF m0 (forms.getD i #[]) xs = ewRet st10.data := by
    rw [p0]
    unfold dotF
    rw [map3 (by rw [NativeVm.Math.Tables.getD_eq_getElem' _ _ hi']; exact hrow)]
  have cs10 : ∀ r, calleeSaved r = true → reg st10.data r = reg st9.data r := p2.1
  refine at_pc (hpc10.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableTerms.b9_next)))
    (cont st10.data ⟨hb10, fw10.left.left.left.left.left.left, it10, H.run, H.cur, H.rs⟩
      (FW.append (FW.append fw10.left.left.left.left.left.right fw10.left.left.left.left.right)
        fw10.right) (by rw [hdf]; rfl) (by rw [hdf]; rfl) ?_ ?_)
  · rw [cs10 .r12 rfl, rg9 r12_9]; exact l136
  · rw [cs10 .r13 rfl, keeps_reg hm9' k9 (by simp)]
    exact r13c.trans h13''

end

end NativeRustcVmX64.Tables.TableTerms
