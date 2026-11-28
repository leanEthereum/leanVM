module

public import NativeRustcVmX64.Tables.TableTerms.Calls
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-!
# `table_terms`: table `i`'s evaluations (x86-64)

From the loop head before table `i`: `b1` reads the table's width (at most `92`, so it goes on),
`b2` stores the running sum and `8 i` in the frame, the width as the length of entry `i`'s
`values` and calls `read_scalars` into them, `b3` leaves with `None` when it failed (the model's
run fails too, `exit_none`) and goes on otherwise (`read_step`, to `Rd`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf)

@[expose] public section

/-- The frame's words for table `i`: its entry, the running sum, `8 i`. -/
def lw (m0 : MachineData) (i : Nat) (f : EW) : List (Nat × UInt64) :=
  [(16, .ofBitVec (evi m0 i)), (120, f.c0), (128, f.c1), (136, .ofBitVec (BitVec.ofNat 64 (8 * i)))]

/-- **After table `i`'s evaluations** (`b4`): the body, the frame's words, the registers, the
iteration's outputs, the model's fold so far and the evaluations read. -/
structure Rd [Labels] (a : DecArea) (s : TState) (heights : Array Nat)
    (forms : Array (Array FormW)) (m0 : MachineData) (i : Nat) (acc : Acc) (si : TState)
    (xs : Array EW) (s' : TState) (d : MachineData) : Prop where
  bd : Bd m0 272 N slots (outs m0) 8 d
  fw : FW m0 d (cws m0)
  fl : FW m0 d (lw m0 i acc.2.1)
  r14 : reg d .r14 = BitVec.ofNat 64 (16 + 40 * i)
  rbp : reg d .rbp = (Labels.label tablesL).toBitVec
  r13 : reg d .r13 = fA m0 + BitVec.ofNat 64 (11864 + 17784 * i)
  r15 : reg d .r15 = BitVec.ofNat 64 (cursorAt i)
  r12 : reg d .r12 = BitVec.ofNat 64 (tb i).width
  rbx : reg d .rbx = evi m0 i + BitVec.ofNat 64 496
  it : It a m0 i acc.2.2 xs s' d
  run : preRun heights forms m0 i s = some (acc, si)
  cur : acc.1 = cursorAt i
  rs : (readScalars (tb i).width).run si = some (xs, s')

end

public section

theorem ult_lit (x : BitVec 64) {v : Nat} (hv : v < 2 ^ 64) :
    CmpOp.apply .ult .W64 x (BitVec.ofNat 64 v) = decide (x.toNat < v) := by
  simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

theorem lw_le {m0 : MachineData} {i : Nat} {f : EW} :
    ∀ p ∈ lw m0 i f, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280 ∧ (p.1 + 8 ≤ 144 ∨ 176 ≤ p.1) := by
  intro p hp
  simp only [lw, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp

theorem lw136 {m0 d : MachineData} {i : Nat} {f : EW} (h : FW m0 d (lw m0 i f)) :
    NativeRustcVm.WordAt d.dmem (off (fb m0) 136) (.ofBitVec (BitVec.ofNat 64 (8 * i))) :=
  h (136, _) (by simp [lw])

theorem cws32 {m0 d : MachineData} (h : FW m0 d (cws m0)) :
    NativeRustcVm.WordAt d.dmem (off (fb m0) 32) (.ofBitVec (reg m0 .rcx)) :=
  h (32, _) (by simp [cws])

theorem cws8 {m0 d : MachineData} (h : FW m0 d (cws m0)) :
    NativeRustcVm.WordAt d.dmem (off (fb m0) 8) (.ofBitVec (oA m0)) :=
  h (8, _) (by simp [cws])

theorem cws24 {m0 d : MachineData} (h : FW m0 d (cws m0)) :
    NativeRustcVm.WordAt d.dmem (off (fb m0) 24) (.ofBitVec (reg m0 .rdx)) :=
  h (24, _) (by simp [cws])

theorem cws40 {m0 d : MachineData} (h : FW m0 d (cws m0)) :
    NativeRustcVm.WordAt d.dmem (off (fb m0) 40) (.ofBitVec (reg m0 .r8)) :=
  h (40, _) (by simp [cws])

theorem cws48 {m0 d : MachineData} (h : FW m0 d (cws m0)) :
    NativeRustcVm.WordAt d.dmem (off (fb m0) 48) (.ofBitVec (reg m0 .r9)) :=
  h (48, _) (by simp [cws])

theorem cws56 {m0 d : MachineData} (h : FW m0 d (cws m0)) :
    NativeRustcVm.WordAt d.dmem (off (fb m0) 56) (.ofBitVec (tA m0)) :=
  h (56, _) (by simp [cws])

theorem lw16 {m0 d : MachineData} {i : Nat} {f : EW} (h : FW m0 d (lw m0 i f)) :
    NativeRustcVm.WordAt d.dmem (off (fb m0) 16) (.ofBitVec (evi m0 i)) :=
  h (16, _) (by simp [lw])

theorem lw120 {m0 d : MachineData} {i : Nat} {f : EW} (h : FW m0 d (lw m0 i f)) :
    NativeRustcVm.WordAt d.dmem (off (fb m0) 120) (f.c0) :=
  h (120, _) (by simp [lw])

theorem lw128 {m0 d : MachineData} {i : Nat} {f : EW} (h : FW m0 d (lw m0 i f)) :
    NativeRustcVm.WordAt d.dmem (off (fb m0) 128) (f.c1) :=
  h (128, _) (by simp [lw])

theorem cws_le {m0 : MachineData} :
    ∀ p ∈ cws m0, 8 ≤ p.1 ∧ p.1 + 8 ≤ 280 ∧ (p.1 + 8 ≤ 144 ∨ 176 ≤ p.1) := by
  intro p hp
  simp only [cws, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

theorem T_eq : T = (Labels.label tablesL).toBitVec := rfl

/-- R14 + RBP in the loop: byte `16` of table `i`'s entry. -/
theorem tabA_eval {d : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {i : Nat}
    (hr14 : reg d .r14 = BitVec.ofNat 64 (16 + 40 * i))
    (hrbp : reg d .rbp = (Labels.label tablesL).toBitVec) :
    tabA.eval (E m0 d rest ret) = T + BitVec.ofNat 64 (40 * i) + BitVec.ofInt 64 16 := by
  show BinOp.apply .add .W64 (reg d .r14) (reg d .rbp) = _
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [hr14, hrbp, ← T_eq, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl,
    NativeRustcVm.addr_add_add, BitVec.add_comm, Nat.add_comm]

omit [Host] in
/-- A failed table: the whole run fails. -/
theorem R_none (hh : heights.size = 6) (hf : forms.size = 6) {i : Nat} (hi : i < 6) {c : Nat}
    {f : EW} {o : Array (Array EW × Array EW)} {si : TState}
    (hrun : preRun heights forms m0 i s = some ((c, f, o), si))
    (hr : (readScalars (tb i).width).run si = none) : R heights forms m0 s = none := by
  have h1 : preRun heights forms m0 (i + 1) s = none := by
    rw [preRun_succ hh hf hi, hrun]
    show (stp m0 (c, f, o) _).run si = none
    rw [stp_run, hr]
    rfl
  rw [R_eq hh hf, preRun_none hh hf h1]
  rfl

/-- **Table `i`'s evaluations.** -/
theorem read_step (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hh : heights.size = 6) (hf : forms.size = 6)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    {i : Nat} (hi : i < 6) {acc : Acc} {si : TState} {d : MachineData}
    (H : Head a s heights forms m0 i acc si d)
    (cont : ∀ xs s' d', Rd a s heights forms m0 i acc si xs s' d' →
      Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b4Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b1Offset)⟩ := by
  have hS := Pre.stack h
  have c0 := ctx h
  have hwl := width_le hi
  -- `b1`: the width.
  have hwf1 : (E m0 d [(T + BitVec.ofNat 64 (40 * i), 40)] 0).WF := wf_tab h hi H.bd.fr.kept
  have hm1 : Match (E m0 d [(T + BitVec.ofNat 64 (40 * i), 40)] 0) tabS d :=
    match_body H.bd ⟨rfl, rfl, trivial⟩ ⟨tabA_eval H.r14 H.rbp, trivial⟩
  refine exec_then (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf1 nofun hm1
    fun st1 hm1' hpc1 ↦ ?_
  obtain ⟨hmid1, hmem1, r12, k1⟩ := ok_b1
  have hd1 : st1.data.dmem = d.dmem := hm1'.dmem_eq hwf1 hmem1
  have hwd : (wordOf d.dmem (T + BitVec.ofNat 64 (40 * i) + BitVec.ofNat 64 8)).toNat =
      (tb i).width := by
    have := tw_get h H.bd hi (o := 1) (by omega)
    rw [Nat.mul_one] at this
    rw [this, tw_width hi]
  have e12 : reg st1.data .r12 = BitVec.ofNat 64 (tb i).width := by
    show st1.data.regs.get64 .r12 = _
    rw [hm1'.regs _ _ r12]
    show (E m0 d [(T + BitVec.ofNat 64 (40 * i), 40)] 0).load 1 8 8 = _
    rw [load_eq_wordOf]
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hwd
  have hc1 : c1.eval (E m0 d [(T + BitVec.ofNat 64 (40 * i), 40)] 0) = false := by
    show (!(CmpOp.apply .ult .W64 ((E m0 d [(T + BitVec.ofNat 64 (40 * i), 40)] 0).load 1 8 8)
      (BitVec.ofNat 64 93))) = false
    rw [ult_lit _ (by norm_num), load_eq_wordOf]
    show (!decide ((wordOf d.dmem (T + BitVec.ofNat 64 (40 * i) + BitVec.ofNat 64 8)).toBitVec.toNat
      < 93)) = false
    rw [UInt64.toNat_toBitVec, hwd]
    simp only [decide_eq_true (show (tb i).width < 93 by omega), Bool.not_true]
  simp only [PcOk, hc1, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hb1 : Bd m0 272 N slots (outs m0) 8 st1.data :=
    (blockB h H.bd hwf1 hm1' hmid1 (os := []) (by rw [WrOk, hmem1]; rfl) nofun).1
  have kr1 : ∀ r ∈ [Reg64.rax, .rcx, .rdx, .rbx, .rbp, .r13, .r14, .r15],
      reg st1.data r = reg d r := fun r hr ↦ keeps_reg hm1' k1 hr
  have fw1 : FW m0 st1.data (cws m0) := fun p hp ↦ by rw [hd1]; exact H.fw p hp
  have w16 : NativeRustcVm.WordAt st1.data.dmem (off (fb m0) 16) (.ofBitVec (evi m0 i)) := by
    rw [hd1]; exact H.w16
  -- `b2`: the sum and `8 i` saved, the length, `read_scalars`.
  have eo := evi_out h hi
  let ra := (Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b2Offset + b2.length)).toBitVec
  have hwf2 : (E m0 st1.data [(evi m0 i, 1968)] ra).WF := wf_ev h hi hb1.fr.kept
  have hm2 : Match (E m0 st1.data [(evi m0 i, 1968)] ra) evS st1.data :=
    match_body hb1 ⟨rfl, rfl, trivial⟩ ⟨by
      show (Sym.load 0 16 8).eval _ = evi m0 i + BitVec.ofInt 64 0
      rw [ld0 w16, ofInt_zero64, BitVec.add_zero], trivial⟩
  refine at_pc (hpc1.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableTerms.b1_next)))
    (exec_then (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf2 (fun _ _ ↦ rfl) hm2
      fun st2 hm2' hpc2 ↦ ?_)
  obtain ⟨hmiss2, hmid2, hW2, -, w136, w128, w120, w488, rdi2, rsi2, rbx2, rdx2, k2⟩ := ok_b2
  have hin2 := writesIn_of_mid hmid2
  have hRev : ∀ r ∈ [1], ∀ x, [(evi m0 i, 1968)][r - 1]? = some x →
      ∀ q, NativeRustcVm.InRange x.1 x.2 q → NativeRustcVm.InRange (evi m0 i) 1968 q := by
    intro r hr x hx q hq
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    exact hq
  obtain ⟨hb2, hs2⟩ := blockB h hb1 hwf2 hm2' hmid2 hW2 fun r hr x hx q hq ↦
    .inr (.inr (evi_in h hi (hRev r hr x hx q hq)))
  have hs2' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow m0 N) N q ∨
        NativeRustcVm.InRange (evi m0 i) 1968 q) :=
    NativeRustcVm.SameOutside.mono hs2 fun q hq ↦ hq.imp_right fun ⟨r, hr, x, hx, hq⟩ ↦
      hRev r hr x hx q hq
  have rg2 : ∀ {r : Reg64} {v : Sym}, (after b2 evS).reg r = some v →
      reg st2.data r = v.eval (E m0 st1.data [(evi m0 i, 1968)] ra) := fun hv ↦ hm2'.regs _ _ hv
  have fw2 : FW m0 st2.data (cws m0) := fw_blockU hwf2 hm2' hin2 hmiss2 rfl
    (fun p hp ↦ (cws_le p hp).2.1) fw1
  have w16' : FW m0 st2.data [(16, .ofBitVec (evi m0 i))] :=
    fw_blockU hwf2 hm2' hin2 hmiss2 rfl (by simp) (fun p hp ↦ by
      rw [List.mem_singleton] at hp; subst hp; exact w16)
  have fl2 : FW m0 st2.data (lw m0 i acc.2.1) := by
    intro p hp
    simp only [lw, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact w16' _ (List.mem_singleton_self _)
    · exact wroteW hm2' (by omega) w120 ((kr1 .rdx (by simp)).trans H.rdx)
    · exact wroteW hm2' (by omega) w128 ((kr1 .rcx (by simp)).trans H.rcx)
    · exact wroteW hm2' (by omega) w136 ((kr1 .rax (by simp)).trans H.rax)
  have hlen2 : NativeRustcVm.WordAt st2.data.dmem (evi m0 i + BitVec.ofNat 64 488)
      (.ofBitVec (BitVec.ofNat 64 (tb i).width)) :=
    wordAt_written hm2' (r := 1) (o := 488) rfl (by omega) w488 e12
  have hts2 : TStateAt st2.data.dmem (tA m0) a si :=
    ts_keep h hi (hm2'.kept hwf2 : Kept st1.data.dmem st2.data.dmem) hs2' (fun q hq ↦ hq)
      (show TStateAt st1.data.dmem (tA m0) a si by rw [hd1]; exact H.ts)
  have evs2 : ∀ j (hj : j < acc.2.2.size), TableEvalAt st2.data.dmem (evi m0 j) acc.2.2[j] :=
    evs_keep h hi hs2' (fun q hq ↦ hq.imp_right .inl) (by rw [H.osz])
      (fun j hj ↦ by rw [hd1]; exact H.evs j hj)
  -- `read_scalars`.
  have hb2' : Bd m0 272 N slots (outs m0) 0 st2.data := hb2
  have hat := Bd.at0 h hb2'
  have hle : 272 + readScalarsStack ≤ N := by rw [N_eq]; decide
  have ex0 : reg st2.data .rdi = tA m0 := by
    rw [rg2 rdi2, ld0 (fw1 (56, .ofBitVec (tA m0)) (by simp [cws]))]
  have ex1 : reg st2.data .rsi = evi m0 i + BitVec.ofNat 64 496 := by
    rw [rg2 rsi2]
    show BinOp.apply .add .W64 ((Sym.load 0 16 8).eval _) (BitVec.ofNat 64 496) = _
    rw [ld0 w16]
    simp only [BinOp.apply, low_W64, ext_W64]
  have ex2 : (reg st2.data .rdx).toNat = (tb i).width := by
    rw [rg2 rdx2]
    show (reg st1.data .r12).toNat = _
    rw [e12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : 496 + 16 * (tb i).width ≤ 1968 := by omega
  have hpre : ReadScalarsPre a si st2.data := by
    simp only [ReadScalarsPre]
    rw [ex0, ex1, ex2]
    refine ⟨hb2'.stackOk_at hS (Nat.zero_le _) (by simpa using hle), c0.rcAt hat hle, hts2,
      c0.tstateOk hat hle, c0.outOk hat hle (outOk_sub eo hsub), ?_⟩
    refine got_callee (Pre.got h) (got_keep (Pre.got h) hS
      (writes := [(oA m0, 24), (tA m0, tstateBytes), (ev m0, tableEvalsBytes)])
      (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl <;> simp)
      (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl
        · exact (Pre.out h).2.1
        · exact (Pre.ts h).footprint.1.2
        · exact (Pre.evs h).2.1)
      (by simpa [outs, or_assoc] using hb2'.same))
      hat.sp hS.1 hle ?_
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ((Pre.got h).1 l hl).2.2.2 (tA m0, tstateBytes) (by simp)
    · exact ((Pre.got h).1 l hl).2.2.2 (a.words, 8 * a.len) (by simp)
    · change Apart (gotAddr l) 8 (evi m0 i + BitVec.ofNat 64 496) (16 * (tb i).width)
      have he : (evi m0 i).toNat = (ev m0).toNat + 1968 * i := by
        unfold evi
        exact NativeRustcVm.toNat_add_ofNat (by
          have hn : (ev m0).toNat + tableEvalsBytes ≤ 2 ^ 64 := (Pre.evs h).2.1
          unfold tableEvalsBytes nTables tableEvalBytes at hn
          omega)
      have ha : (evi m0 i + BitVec.ofNat 64 496).toNat = (evi m0 i).toNat + 496 :=
        NativeRustcVm.toNat_add_ofNat (by
          have hn := evi_noWrap h hi
          unfold NativeRustcVm.NoWrap at hn
          omega)
      have hg : Apart (gotAddr l) 8 (ev m0) tableEvalsBytes :=
        ((Pre.got h).1 l hl).2.2.2 (ev m0, tableEvalsBytes) (by simp)
      refine Apart.sub hg ?_ ?_
      · rw [ha, he]; omega
      · rw [ha, he]
        unfold tableEvalsBytes nTables tableEvalBytes
        omega
    · exact ((Pre.got h).1 l hl).2.2.2 (rcAddr, 192) (by simp)
  simp only [PcOk] at hpc2
  refine call_then (env := E m0 st1.data [(evi m0 i, 1968)] 0) hpc2 (hrs a si) hpre
    fun st3 hpc3 hrsp3 hq3 ↦ ?_
  simp only [ReadScalarsPost] at hq3
  rw [ex0, ex1, ex2] at hq3
  obtain ⟨q0, q1, q2, q3, q4⟩ := hq3
  have hRo : ∀ q, (NativeRustcVm.InRange (evi m0 i + BitVec.ofNat 64 496) (16 * (tb i).width) q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q) → outs m0 q := fun q hq ↦ by
    rcases hq with hq | hq
    · exact .inr (.inr (evi_in h hi (NativeRustcVm.InRange.of_sub hq (evi_noWrap h hi) hsub)))
    · exact .inr (.inl hq)
  have hso3 : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem
      (fun q ↦ (NativeRustcVm.InRange (evi m0 i + BitVec.ofNat 64 496) (16 * (tb i).width) q ∨
        NativeRustcVm.InRange (tA m0) tstateBytes q) ∨
        NativeRustcVm.InRange (stackBelow st2.data readScalarsStack) readScalarsStack q) :=
    NativeRustcVm.SameOutside.mono q3 fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inl (.inl hq)
      · exact .inl (.inr hq)
      · exact .inr hq
  have hb3 := call_bd h hb2' hle q4 hrsp3 hso3 hRo
  have fw3 := fw_callO h hb2' hle hso3 hRo (fun p hp ↦ ⟨(cws_le p hp).1, (cws_le p hp).2.1⟩) fw2
  have fl3 := fw_callO h hb2' hle hso3 hRo (fun p hp ↦ ⟨(lw_le p hp).1, (lw_le p hp).2.1⟩) fl2
  have hW3 : ∀ q, ((NativeRustcVm.InRange (evi m0 i + BitVec.ofNat 64 496) (16 * (tb i).width) q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q) ∨
      NativeRustcVm.InRange (stackBelow st2.data readScalarsStack) readScalarsStack q) →
      NativeRustcVm.InRange (stackBelow m0 N) N q ∨ NativeRustcVm.InRange (evi m0 i) 1968 q ∨
        NativeRustcVm.InRange (tA m0) tstateBytes q := fun q hq ↦ by
    rcases hq with (hq | hq) | hq
    · exact .inr (.inl (NativeRustcVm.InRange.of_sub hq (evi_noWrap h hi) hsub))
    · exact .inr (.inr hq)
    · exact .inl (callee_stack h hb2' hle hq)
  have evs3 := evs_keep h hi hso3 hW3 (by rw [H.osz]) evs2
  -- The length word, kept by the call.
  have hlen3 : NativeRustcVm.WordAt st3.data.dmem (evi m0 i + BitVec.ofNat 64 488)
      (.ofBitVec (BitVec.ofNat 64 (tb i).width)) := by
    refine NativeRustcVm.BytesAt.of_sameOutside hlen2 hso3 fun j hj hq ↦ ?_
    have hj8 : j < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hj
    rw [NativeRustcVm.addr_add_add] at hq
    have hj' : 488 + j < 1968 := by omega
    rcases hq with (hq | hq) | hq
    · exact NativeRustcVm.not_inRange_sub (evi_noWrap h hi) hsub hj' (.inl (by omega)) hq
    · exact NativeRustcVm.Apart.not_inRange_add eo.2.2.1 (evi_noWrap h hi)
        (Pre.ts h).footprint.1.2 hj' hq
    · exact outs_not_stackN h (.inr (.inr (evi_in h hi (NativeRustcVm.inRange_add hj'
        (by norm_num))))) (callee_stack h hb2' hle hq)
  -- `b3`: the result.
  have hwf4 : (E m0 st3.data [] 0).WF := wf_nil h hb3.fr.kept
  have hm4 : Match (E m0 st3.data [] 0) sF st3.data := match_body hb3 ⟨rfl, trivial⟩ trivial
  refine at_pc (hpc3.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableTerms.b2_next)))
    (exec_then (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf4 nofun hm4
      fun st4 hm4' hpc4 ↦ ?_)
  obtain ⟨hmid4, hmem4, k4⟩ := ok_b3
  have hd4 : st4.data.dmem = st3.data.dmem := hm4'.dmem_eq hwf4 hmem4
  have hb4 := (blockB h hb3 hwf4 hm4' hmid4 (os := []) (by rw [WrOk, hmem4]; rfl) nofun).1
  have hc : cAl.eval (E m0 st3.data [] 0) = !((readScalars (tb i).width).run si).isSome :=
    cAl_eval q0
  simp only [PcOk, hc] at hpc4
  have kr : ∀ r ∈ [Reg64.rbp, .r12, .r13, .r14, .r15], reg st4.data r = reg st1.data r := by
    intro r hr
    have hcs : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
    have e1 : reg st4.data r = reg st3.data r := keeps_reg hm4' k4 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
    have e2 : reg st3.data r = reg st2.data r := q4.1 r hcs
    have e3 : reg st2.data r = reg st1.data r := keeps_reg hm2' k2 hr
    exact e1.trans (e2.trans e3)
  cases hr : (readScalars (tb i).width).run si with
  | none =>
    simp only [hr, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc4
    obtain ⟨c, f, o⟩ := acc
    exact at_pc (hpc4.trans (lbl_6 hp)) (exit_none hp h hb4 (FW.of_dmem hd4 fw3)
      (R_none hh hf hi H.run hr))
  | some p =>
    obtain ⟨xs, s'⟩ := p
    simp only [hr, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
    have hxs : xs.size = (tb i).width := NativeRustcVm.Sumcheck.readScalars_size hr
    refine at_pc (hpc4.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableTerms.b3_next)))
      (cont xs s' st4.data ⟨hb4, FW.of_dmem hd4 fw3, FW.of_dmem hd4 fl3, ?_, ?_, ?_, ?_, ?_, ?_,
        ⟨by rw [hd4]; exact q2 xs s' hr, ?_, fun j hj ↦ by rw [hd4]; exact evs3 j hj, H.osz⟩,
        H.run, H.cur, hr⟩)
    · rw [kr .r14 (by simp), kr1 .r14 (by simp)]; exact H.r14
    · rw [kr .rbp (by simp), kr1 .rbp (by simp)]; exact H.rbp
    · rw [kr .r13 (by simp), kr1 .r13 (by simp)]; exact H.r13
    · rw [kr .r15 (by simp), kr1 .r15 (by simp)]; exact H.r15
    · rw [kr .r12 (by simp)]; exact e12
    · have e1 : reg st4.data .rbx = reg st3.data .rbx := keeps_reg hm4' k4 (by simp)
      have e2 : reg st3.data .rbx = reg st2.data .rbx := q4.1 .rbx rfl
      rw [e1, e2, rg2 rbx2]
      show BinOp.apply .add .W64 ((Sym.load 0 16 8).eval _) (BitVec.ofNat 64 496) = _
      rw [ld0 w16]
      simp only [BinOp.apply, low_W64, ext_W64]
    · rw [hd4]
      refine ⟨by rw [Array.length_toList, hxs]; exact hwl, ?_, ?_⟩
      · have : (BitVec.ofNat 64 (tb i).width) = xs.toList.length.toUInt64.toBitVec := by
          rw [Array.length_toList, hxs]; rfl
        rw [← UInt64.ofBitVec_toBitVec xs.toList.length.toUInt64, ← this]
        exact hlen3
      · rw [show evi m0 i + BitVec.ofNat 64 488 + 8#64 = evi m0 i + BitVec.ofNat 64 496 from
          NativeRustcVm.addr_add_add _ 488 8]
        exact q1 xs s' hr

end

end NativeRustcVmX64.Tables.TableTerms
