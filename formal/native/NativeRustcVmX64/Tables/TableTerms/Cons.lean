module

public import NativeRustcVmX64.Tables.TableTerms.Mid
public import NativeRustcVmX64.Code.Vm.ConstraintsW.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names

/-!
# `table_terms`: the constraints' dot product (x86-64)

From table `i`'s evaluations read (`Rd`): `b4` saves the `TABLES` walk, clears the constraints'
buffer and calls `constraints_w(opcode, values, width, buffer)`; `b5` saves the constraint count
and the cursor and calls `dot` of the constraint powers from the cursor with the constraints:
`dotC` in RAX, RDX (`cons_step`). Helpers: the iteration's outputs across a block of the frame
(`it_block`) and a call (`it_call`); a region apart from the stack, or of the frame, for a callee
(`rd_callee`, `fr_callee`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf)

public section

section
variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)}
  {m0 : MachineData}

/-- **The iteration's outputs across a block** writing only the frame. -/
theorem it_block (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6)
    {o : Array (Array EW × Array EW)} {xs : Array EW} {s' : TState} {d d' : MachineData}
    (H : It a m0 i o xs s' d) {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {Sy : SState}
    {o' : Nat} (hwf : (E m0 d rest ret).WF) (hm : Match (E m0 d rest ret) Sy d')
    (hmid : MidOk 272 o' slots Sy = true) (hW : WrOk Sy [] = true) : It a m0 i o xs s' d' :=
  H.step h hi (hm.kept hwf) (same_block hwf hm (writesIn_of_mid hmid) (belowRet_of_mid hmid) hW
    (X := fun _ ↦ False) nofun) fun _ hq ↦ hq.elim (fun h' ↦ .inl (fr_stack h h')) False.elim

/-- **The iteration's outputs across a call** changing its stack and `Ro`. -/
theorem it_call (h : TableTermsPre a s heights forms m0) {i : Nat} (hi : i < 6)
    {o : Array (Array EW × Array EW)} {xs : Array EW} {s' : TState} {d d' : MachineData}
    (H : It a m0 i o xs s' d) (hb : Bd m0 272 N slots (outs m0) 0 d) {Nc : Nat}
    (hle : 272 + Nc ≤ N) (hk : Saved d d') {Ro : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ Ro q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    (hRo : ∀ q, Ro q → NativeRustcVm.InRange (stackBelow m0 N) N q ∨
      NativeRustcVm.InRange (evi m0 i) 488 q) : It a m0 i o xs s' d' :=
  H.step h hi hk.2 hso fun q hq ↦ hq.elim (hRo q) fun h' ↦ .inl (callee_stack h hb hle h')

/-- **A region apart from the stack, for a callee.** -/
theorem rd_callee (h : TableTermsPre a s heights forms m0) {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) 0 d) {Nc : Nat} (hle : 272 + Nc ≤ N) {x : BitVec 64}
    {n : Nat} (hm : NativeRustcVm.Mapped m0.dmem x n) (hnw : NativeRustcVm.NoWrap x n)
    (hA : NativeRustcVm.Apart x n (stackBelow m0 N) (N + 8)) :
    Readable d x n ∧ OffStack d x n Nc :=
  ⟨⟨Mapped.keeps hm hb.fr.kept, hnw⟩,
    hb.apart_at (Pre.stack h) (Nat.zero_le _) (by simpa using hle) hA⟩

/-- **A region of the frame from offset `8`, for a callee.** -/
theorem fr_callee (h : TableTermsPre a s heights forms m0) {d : MachineData}
    (hb : Bd m0 272 N slots (outs m0) 0 d) {Nc : Nat} (hle : 272 + Nc ≤ N) {j l : Nat}
    (hj : 8 ≤ j) (hjl : j + l ≤ 272) (hl : 0 < l) :
    Readable d (off (fb m0) j) l ∧ OffStack d (off (fb m0) j) l Nc := by
  have hS := Pre.stack h
  have hnw : (fb m0).toNat + (272 + 8) ≤ 2 ^ 64 := frame_noWrap (F := 272) hS (by rw [N_eq]; omega)
  refine ⟨⟨mapped_off (Mapped.keeps (frame_mapped hS (by rw [N_eq]; omega)) hb.fr.kept)
    (by omega), ?_⟩, frame_apart_callee hb hS (by rw [N_eq]; omega) (Nat.zero_le _)
    (by simpa using hle) (by omega) (by omega) hl⟩
  unfold NoWrap
  rw [toNat_off (by omega)]
  omega

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **The constraints' dot product.** -/
theorem cons_step (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hcw : Spec (Labels.label NativeRustcVmX64.Vm.ConstraintsW.entryLabel) ConstraintsWPre ConstraintsWPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    {i : Nat} (hi : i < 6) {acc : Acc} {si : TState} {xs : Array EW} {s' : TState}
    {d : MachineData} (H : Rd a s heights forms m0 i acc si xs s' d)
    (cont : ∀ d', Cm a s heights forms m0 i acc si xs s' d' →
      reg d' .rax = (dotC m0 i (cursorAt i) xs).c0.toBitVec →
      reg d' .rdx = (dotC m0 i (cursorAt i) xs).c1.toBitVec →
      FW m0 d' [(96, .ofBitVec (BitVec.ofNat 64 (tb i).nConstraints)),
        (104, .ofBitVec (BitVec.ofNat 64 (cursorAt i)))] →
      reg d' .r12 = BitVec.ofNat 64 (tb i).width → reg d' .rbx = evi m0 i + BitVec.ofNat 64 496 →
      reg d' .r13 = fA m0 + BitVec.ofNat 64 (11864 + 17784 * i) →
      Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b6Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b4Offset)⟩ := by
  have hS := Pre.stack h
  have c0 := ctx h
  have eo := evi_out h hi
  have hcl := cursor_le hi
  have hwl := width_le hi
  have hxs : xs.size = (tb i).width := NativeRustcVm.Sumcheck.readScalars_size H.rs
  -- `b4`: `constraints_w`'s arguments.
  let ra4 := (Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b4Offset + b4.length)).toBitVec
  have hwf1 : (E m0 d [(T + BitVec.ofNat 64 (40 * i), 40)] ra4).WF := wf_tab h hi H.bd.fr.kept
  have hm1 : Match (E m0 d [(T + BitVec.ofNat 64 (40 * i), 40)] ra4) tabS d :=
    match_body H.bd ⟨rfl, rfl, trivial⟩ ⟨tabA_eval H.r14 H.rbp, trivial⟩
  refine exec_then (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf1 (fun _ _ ↦ rfl) hm1
    fun st1 hm1' hpc1 ↦ ?_
  obtain ⟨miss1, mid1, W1, -, w112, -, -, -, -, rdi1, r14_1, rsi1, rdx1, rcx1, rbp1, k1⟩ := ok_b4
  have hb1 := (blockB h H.bd hwf1 hm1' mid1 W1 nofun).1
  have it1 := it_block h hi H.it hwf1 hm1' mid1 W1
  have rg1 : ∀ {r : Reg64} {v : Sym}, (after b4 tabS).reg r = some v →
      reg st1.data r = v.eval (E m0 d [(T + BitVec.ofNat 64 (40 * i), 40)] ra4) :=
    fun hv ↦ hm1'.regs _ _ hv
  have fw1 : FW m0 st1.data (cws m0 ++ lw m0 i acc.2.1 ++ tw112 i) := by
    refine FW.append (fw_blockU hwf1 hm1' (writesIn_of_mid mid1) miss1 rfl
      (fun p hp ↦ (fwL_le p (List.mem_append_left _ hp)).2.1) (FW.append H.fw H.fl))
      (fw_wrote hm1' (by omega) w112 ?_)
    show reg d .r14 = _
    rw [H.r14]
  have kr1 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r15], reg st1.data r = reg d r :=
    fun r hr ↦ keeps_reg hm1' k1 hr
  have ld1 : ∀ o, o < 5 → (Sym.load 1 (8 * o) 8).eval
      (E m0 d [(T + BitVec.ofNat 64 (40 * i), 40)] ra4) =
      (tablesWords.getD (5 * i + o) 0).toBitVec := fun o ho ↦ by
    show (E m0 d [(T + BitVec.ofNat 64 (40 * i), 40)] ra4).load 1 (8 * o) 8 = _
    rw [load_eq_wordOf]
    exact congrArg UInt64.toBitVec (tw_get h H.bd hi ho)
  have eop : (reg st1.data .rdi).toNat = (tb i).opcode := by
    rw [rg1 rdi1, show (0 : Nat) = 8 * 0 from rfl, ld1 0 (by omega), UInt64.toNat_toBitVec,
      Nat.add_zero]
    exact tw_opcode hi
  have enc : reg st1.data .r14 = BitVec.ofNat 64 (tb i).nConstraints := by
    rw [rg1 r14_1, show (16 : Nat) = 8 * 2 from rfl, ld1 2 (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, tw_nc hi, toNat_ofNat_lt (by omega)]
  have ersi : reg st1.data .rsi = evi m0 i + BitVec.ofNat 64 496 := by
    rw [rg1 rsi1]; exact H.rbx
  have erdx : reg st1.data .rdx = BitVec.ofNat 64 (tb i).width := by
    rw [rg1 rdx1]; exact H.r12
  have ercx : reg st1.data .rcx = off (fb m0) 144 := by
    rw [rg1 rcx1]; exact eval_ptr0 144
  -- `constraints_w`.
  have hle1 : 272 + constraintsWStack ≤ N := by rw [N_eq]; decide
  have hsub : 496 + 16 * (tb i).width ≤ 1968 := by omega
  have hvals := rd_callee h hb1 hle1 (NativeRustcVm.Mapped.sub eo.1 hsub)
    (NativeRustcVm.NoWrap.sub eo.2.1 hsub) (apart_sub eo.2.1 eo.2.2.2.2.1 hsub)
  have hloc := fr_callee h hb1 hle1 (j := 144) (l := 32) (by omega) (by omega) (by omega)
  have hpre1 : ConstraintsWPre st1.data := by
    unfold ConstraintsWPre SliceOk
    rw [ersi, erdx, ercx, toNat_ofNat_lt (by omega)]
    exact ⟨hb1.stackOk_at hS (Nat.zero_le _) (by simpa using hle1), hvals, hloc⟩
  simp only [PcOk] at hpc1
  refine call_then (env := E m0 d [(T + BitVec.ofNat 64 (40 * i), 40)] ra4) hpc1 hcw hpre1
    fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨q0, q1, q2, q3⟩ := hq2
  unfold Changes at q2
  rw [ercx] at q1 q2
  rw [ersi, erdx] at q0 q1
  have hslx : slice st1.data (evi m0 i + BitVec.ofNat 64 496) (BitVec.ofNat 64 (tb i).width) = xs := by
    unfold slice
    rw [toNat_ofNat_lt (by omega)]
    have e := it1.vals.2.2
    rw [show evi m0 i + BitVec.ofNat 64 488 + 8#64 = evi m0 i + BitVec.ofNat 64 496 from
      NativeRustcVm.addr_add_add _ 488 8] at e
    have := NativeRustcVm.ewsOf_of_ewsAt e
    rw [Array.length_toList, hxs] at this
    rw [this, Array.toArray_toList]
  rw [hslx, eop] at q0 q1
  have q2' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem
      (fun q ↦ loc m0 q ∨ NativeRustcVm.InRange (stackBelow st1.data constraintsWStack)
        constraintsWStack q) := q2
  have hb2 := callL h hb1 hle1 q3 hrsp2 q2'
  have fw2 := fw_callL h hb1 hle1 q2' fwL_le fw1
  have it2 := it_call h hi it1 hb1 hle1 q3 q2' fun q hq ↦ .inl (fr_stack h (by
    unfold loc at hq
    have hnw : (fb m0).toNat + (272 + 8) ≤ 2 ^ 64 := frame_noWrap (F := 272) hS (by rw [N_eq]; omega)
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega),
      toNat_off (by omega)] at hq
    show NativeRustcVm.InRange (fb m0) 272 q
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
    omega))
  have cs2 : ∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r := q3.1
  -- `b5`: `dot`'s arguments.
  let ra5 := (Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b5Offset + b5.length)).toBitVec
  have hwf3 : (E m0 st2.data [] ra5).WF := wf_nil h hb2.fr.kept
  have hm3 : Match (E m0 st2.data [] ra5) sF st2.data := match_body hb2 ⟨rfl, trivial⟩ trivial
  refine at_pc (hpc2.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableTerms.b4_next)))
    (exec_then (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf3 (fun _ _ ↦ rfl) hm3
      fun st3 hm3' hpc3 ↦ ?_)
  obtain ⟨miss3, missR3, mid3, W3, -, w96, w104, rdi3, rsi3, rdx3, rcx3, r15_3, k3⟩ := ok_b5
  have hb3 := (blockB h hb2 hwf3 hm3' mid3 W3 nofun).1
  have it3 := it_block h hi it2 hwf3 hm3' mid3 W3
  have rg3 : ∀ {r : Reg64} {v : Sym}, (after b5 sF).reg r = some v →
      reg st3.data r = v.eval (E m0 st2.data [] ra5) := fun hv ↦ hm3'.regs _ _ hv
  have e15 : reg st2.data .r15 = BitVec.ofNat 64 (cursorAt i) := by
    rw [cs2 .r15 rfl, kr1 .r15 (by simp)]; exact H.r15
  have e14 : reg st2.data .r14 = BitVec.ofNat 64 (tb i).nConstraints := by
    rw [cs2 .r14 rfl]; exact enc
  have fw3 : FW m0 st3.data (cws m0 ++ lw m0 i acc.2.1 ++ tw112 i) :=
    fw_blockU hwf3 hm3' (writesIn_of_mid mid3) miss3 rfl
      (fun p hp ↦ (fwL_le p hp).2.1) fw2
  have fw96 : FW m0 st3.data [(96, .ofBitVec (BitVec.ofNat 64 (tb i).nConstraints)),
      (104, .ofBitVec (BitVec.ofNat 64 (cursorAt i)))] := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact wroteW hm3' (by omega) w96 e14
    · exact wroteW hm3' (by omega) w104 e15
  have hcons : NativeRustcVm.EWsAt st3.data.dmem (off (fb m0) 144)
      (constraintsW (tb i).opcode xs).toList := by
    have hsz := constraintsW_size (tb i).opcode xs
    have hl : (constraintsW (tb i).opcode xs).toList.length = (constraintsW (tb i).opcode xs).size :=
      Array.length_toList
    exact keepR hwf3 hm3' (writesIn_of_mid mid3) (by rw [NativeRustcVm.length_ewsBytes, hl]; omega)
      (missR_sub missR3 (by rw [NativeRustcVm.length_ewsBytes, hl]; omega)) q1
  have cp_eq : (Sym.load 0 24 8).eval (E m0 st2.data [] ra5) = reg m0 .rdx :=
    ld0 (fw2 (24, .ofBitVec (reg m0 .rdx)) (by simp [cws]))
  have erdi : reg st3.data .rdi = reg m0 .rdx + BitVec.ofNat 64 (16 * cursorAt i) := by
    rw [rg3 rdi3]
    exact eval_rdi5 (by omega) e15 cp_eq
  have ersi3 : reg st3.data .rsi = BitVec.ofNat 64 (tb i).nConstraints := by
    rw [rg3 rsi3]
    exact eval_rsi5 hcl e15 e14
  have erdx3 : reg st3.data .rdx = off (fb m0) 144 := by
    rw [rg3 rdx3]
    show reg st2.data .rbp = _
    rw [cs2 .rbp rfl, rg1 rbp1]
    exact eval_ptr0 144
  have ercx3 : (reg st3.data .rcx).toNat = (constraintsW (tb i).opcode xs).size := by
    rw [rg3 rcx3]
    exact q0
  -- `dot`.
  have hle3 : 272 + dotStack ≤ N := by rw [N_eq]; decide
  have hcp := rin_sub (Pre.cp h) (o := 16 * cursorAt i) (k := 16 * (tb i).nConstraints)
    (by omega)
  have hsz := constraintsW_size (tb i).opcode xs
  have hpre3 : DotPre st3.data := by
    unfold DotPre SliceOk
    rw [erdi, ersi3, erdx3, ercx3, toNat_ofNat_lt (by omega)]
    refine ⟨hb3.stackOk_at hS (Nat.zero_le _) (by simpa using hle3),
      rd_callee h hb3 hle3 hcp.1.1 hcp.1.2 hcp.2.1, ?_⟩
    rcases Nat.eq_zero_or_pos (constraintsW (tb i).opcode xs).size with h0 | h0
    · rw [h0]
      have := fr_callee h hb3 hle3 (j := 144) (l := 1) (by omega) (by omega) (by omega)
      exact ⟨⟨fun _ h ↦ absurd h (by omega), NativeRustcVm.NoWrap.mono this.1.2 (by omega)⟩,
        NativeRustcVm.Apart.mono this.2 le_rfl (by omega) le_rfl le_rfl⟩
    · have := fr_callee h hb3 hle3 (j := 144) (l := 16 * (constraintsW (tb i).opcode xs).size)
        (by omega) (by omega) (by omega)
      exact this
  simp only [PcOk] at hpc3
  refine call_then (env := E m0 st2.data [] ra5) hpc3 hdot hpre3 fun st4 hpc4 hrsp4 hq4 ↦ ?_
  obtain ⟨p0, p1, p2⟩ := hq4
  unfold Changes at p1
  have hsl1 : slice st3.data (reg st3.data .rdi) (reg st3.data .rsi) =
      (cpw m0).extract (cursorAt i) (cursorAt i + (tb i).nConstraints) := by
    rw [erdi, ersi3, slice_same (same_readIn h hb3 hcp) (by rw [toNat_ofNat_lt (by omega)]),
      toNat_ofNat_lt (by omega)]
    unfold cpw arrE
    apply Array.ext'
    rw [List.toList_toArray, Array.toList_extract, List.toList_toArray, List.extract_eq_take_drop,
      ← ewsOf_sub _ _ (by omega)]
    congr 1
    omega
  have hsl2 : slice st3.data (reg st3.data .rdx) (reg st3.data .rcx) =
      constraintsW (tb i).opcode xs := by
    unfold slice
    rw [erdx3, ercx3]
    have := NativeRustcVm.ewsOf_of_ewsAt hcons
    rw [Array.length_toList] at this
    rw [this, Array.toArray_toList]
  rw [hsl1, hsl2] at p0
  have p1' : NativeRustcVm.SameOutside st3.data.dmem st4.data.dmem
      (fun q ↦ NativeRustcVm.InRange 0 0 q ∨
        NativeRustcVm.InRange (stackBelow st3.data dotStack) dotStack q) := p1
  have hR0 : ∀ q, NativeRustcVm.InRange 0 0 q → False := fun q hq ↦ by
    unfold NativeRustcVm.InRange at hq; omega
  have hb4 := call_bd h hb3 hle3 p2 hrsp4 p1' fun q hq ↦ (hR0 q hq).elim
  have fw4 := fw_callO h hb3 hle3 p1' (fun q hq ↦ (hR0 q hq).elim)
    (fun p hp ↦ ⟨(fwL_le p hp).1, (fwL_le p hp).2.1⟩) fw3
  have fw96' := fw_callO h hb3 hle3 p1' (fun q hq ↦ (hR0 q hq).elim)
    (fun p hp ↦ by simp at hp; rcases hp with rfl | rfl <;> simp) fw96
  have it4 := it_call h hi it3 hb3 hle3 p2 p1' fun q hq ↦ (hR0 q hq).elim
  have cs4 : ∀ r, calleeSaved r = true → reg st4.data r = reg st3.data r := p2.1
  have kr3 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14], reg st3.data r = reg st2.data r :=
    fun r hr ↦ keeps_reg hm3' k3 hr
  unfold ewRet ewArg at p0
  refine at_pc (hpc4.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableTerms.b5_next)))
    (cont st4.data ⟨hb4, fw4, it4, H.run, H.cur, H.rs⟩ ?_ ?_ fw96' ?_ ?_ ?_)
  · have := congrArg EW.c0 p0
    simp only at this
    unfold dotC
    rw [← this]
  · have := congrArg EW.c1 p0
    simp only at this
    unfold dotC
    rw [← this]
  · rw [cs4 .r12 rfl, kr3 .r12 (by simp), cs2 .r12 rfl, kr1 .r12 (by simp)]; exact H.r12
  · rw [cs4 .rbx rfl, kr3 .rbx (by simp), cs2 .rbx rfl, kr1 .rbx (by simp)]; exact H.rbx
  · rw [cs4 .r13 rfl, kr3 .r13 (by simp), cs2 .r13 rfl, kr1 .r13 (by simp)]; exact H.r13

end

end NativeRustcVmX64.Tables.TableTerms
