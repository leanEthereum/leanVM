module

public import NativeRustcArm.SphincsVerify.Parse.OpenBasic
public import NativeRustcArm.SphincsVerify.Parse.OpenExec

/-!
# The parse, part 2: the openings' loop (`b3 .. b6`)

Turn `c` (`open_turn`): `b3` copies opening `c`'s path (160 bytes at `r.sigPtr + 32 + 176 c`) to
the frame's `19008`, `memcpy`s it to `484`; `b4` puts the secret (16 bytes at `r.sigPtr + 16 +
176 c`) after it, `memcpy`s the 176 bytes back to `19008`; `b5` `memcpy`s them to `8640 + 176 c`;
`b6` counts. From `AtOpen 0` at `b3` the loop reaches `AtOpen 24` at `b7` (`open_loop`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcArm.Sym
  NativeRustcArm.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

public section

section
variable (r : Run) [Labels]

/-- **The frame's invariant after a block** whose region 0 is the frame from its byte `d`,
writing there only bytes `lo .. hi` below the saved registers, keeping SP and X29. -/
theorem frame_block (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {regions : List (BitVec 64 × Nat)} {d n lo hi : Nat} (hb : regions[0]? = some (r.off d, n))
    (hn : hi ≤ n) (hlo : lo ≤ hi) (hhi : d + hi ≤ 21520) {S₀ S' : SState}
    (hm : Match (Env.ofMachine m regions) S₀ m) (hm' : Match (Env.ofMachine m regions) S' m')
    (hwf : (Env.ofMachine m regions).WF) (hk : keepsRegs [.X29] S₀ S' = true)
    (hw : writesIn S' lo hi = true) :
    r.Frame m' ∧ SameOutside m.dmem m'.dmem (InRange (r.off (d + lo)) (hi - lo)) := by
  have hout := sameOutside_hull hm' hwf hb (lo := lo) (hi := hi) hn hw
  rw [off_add] at hout
  obtain ⟨hsp, hreg⟩ := keepsRegs_regs hm hm' hk
  refine ⟨hF.of_block (by rw [hsp]; exact hF.1)
    (by rw [hreg .X29 (by simp)]; exact hF.2.1) hout (fun _ h => r.inRange_off hpre (by omega) h)
    (hm'.kept hwf), hout⟩

omit [Labels] in
/-- **The frame's invariant** in a state with the same memory, SP and X29. -/
theorem frame_of_same {m m' : MachineData} (hF : r.Frame m) (hd : m'.dmem = m.dmem)
    (hsp : m'.regs.SP = m.regs.SP) (h29 : m'.regs.getXReg .X29 = m.regs.getXReg .X29) :
    r.Frame m' :=
  hF.of_block (by rw [hsp]; exact hF.1) (by rw [h29]; exact hF.2.1)
    (R := fun _ => False) (fun p _ => by rw [hd]) (fun _ h => h.elim) (fun p h => by rw [hd]; exact h)

theorem sp_frame480 {m : MachineData} (hF : r.Frame m) {regions : List (BitVec 64 × Nat)}
    {n : Nat} (hb : regions[0]? = some (r.off 480, n)) :
    m.regs.SP.toBitVec = Sym.eval (Env.ofMachine m regions) (.ptr 0 (-480)) := by
  rw [hF.1, eval_ptr hb]
  exact alias_neg 480 rfl

end

variable (r : Run) [NativeRustcArm.Host]

/-- The turn's environment: the frame from `480` and the raw opening `c` in `r.sigPtr`. -/
abbrev openEnv (m : MachineData) (c : Nat) : Env :=
  Env.ofMachine m [(r.off 480, 21136), (r.sigPtr + BitVec.ofNat 64 (16 + 176 * c), 176)]

omit [NativeRustcArm.Host] in
/-- A frame address plus a negative offset `j - k` and plus `k`. -/
theorem off_wrap (a k j : Nat) (hk : k ≤ 2 ^ 64) :
    r.off a + BitVec.ofNat 64 (2 ^ 64 - k + j) + BitVec.ofNat 64 k = r.off (a + j) := by
  unfold Run.off
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem pc_next {st : MachineState} {a b : Nat} {ds : List Directive} (h : st.pc = NativeRustcArm.Host.addrOf (r.k + a + ds.length))
    (hb : a + ds.length = b) : st.pc = r.pc b := by
  rw [h, Nat.add_assoc, hb]
  rfl

/-- After `b3` and its `memcpy`: the path at `484`, X28 opening `c`'s address less 4144. -/
@[expose] def Mid1 (c : Nat) (st : MachineState) : Prop :=
  st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b4Offset ∧ r.Frame st.data ∧ OpenMem r c st.data.dmem ∧ OpenRegs r c st.data ∧
    BytesAt st.data.dmem (r.off 484) (slice r.sigBytes (32 + 176 * c) 160) ∧
    (st.data.regs.getXReg .X28).toBitVec = r.sigPtr + BitVec.ofNat 64 (16 + 176 * c) + BitVec.ofInt 64 (-4144)

/-- After `b4` and its `memcpy`: opening `c` at `19008`. -/
@[expose] def Mid2 (c : Nat) (st : MachineState) : Prop :=
  st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b5Offset ∧ r.Frame st.data ∧ OpenMem r c st.data.dmem ∧ OpenRegs r c st.data ∧
    BytesAt st.data.dmem (r.off 19008) (obytesB r.sigBytes c)

/-- After `b5` and its `memcpy`: the first `c + 1` openings. -/
@[expose] def Mid3 (c : Nat) (st : MachineState) : Prop :=
  st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b6Offset ∧ r.Frame st.data ∧ OpenMem r (c + 1) st.data.dmem ∧ OpenRegs r c st.data

/-- **`b3`** and its `memcpy`. -/
theorem open_b3 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {c : Nat} (hc24 : c < 24)
    {m : MachineData} (h : AtOpen r c m) :
    Eventually (step1 NativeRustcArm.Host.exe) (Mid1 r c) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset⟩ := by
  obtain ⟨hF, hM, hR⟩ := h
  have h23 : (m.regs.getXReg .X23).toBitVec = r.sigPtr + BitVec.ofNat 64 96 := hR.2.2.2.2.1
  have h24 : (m.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (2 ^ 64 - 4224 + 176 * c) :=
    hR.2.2.2.2.2.1
  have h27 : (m.regs.getXReg .X27).toBitVec = r.off 19008 := hR.2.2.2.2.2.2.2.2
  have hk3 : b3.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b3Offset) :=
    b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf1 : (openEnv r m c).WF := wf_frame_sig r hpre hF.2.2.2.1 hF.2.2.2.2 (a := 480)
    (n := 21136) (s := 16 + 176 * c) (k := 176) (by decide) (by omega) (by decide) _
  have hx28 : Sym.eval (openEnv r m c) (.bin .add .W64 (.reg .X23) (.reg .X24)) =
      (openEnv r m c).base 1 + BitVec.ofInt 64 (-4144) := by
    sym_simp
    simp only [Env.ofMachine_regs, h23, h24]
    show _ = r.sigPtr + BitVec.ofNat 64 (16 + 176 * c) + BitVec.ofInt 64 (-((4144 : Nat) : Int))
    refine alias_neg 4144 ?_
    bv_lin
  have hm1 : Match (openEnv r m c) openS m :=
    match_ofMachine ⟨rfl, fun _ ↦ off_aligned r hpre (by decide) (by decide),
        ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩⟩
      (sp_frame480 r hF rfl) ⟨h27.trans (eval_ptr_off r (i := 0) rfl 18528).symm, trivial⟩
      trivial trivial ⟨hx28, trivial⟩
  refine exec_then hk3 run_b3 hwf1 hm1 fun st1 hm1' hpc1 ↦ ?_
  obtain ⟨hF1, hout1⟩ := frame_block r hpre hF (d := 480) (lo := 18528) (hi := 18688) rfl
    (by decide) (by decide) (by decide) hm1 hm1' hwf1 (by decide) (by decide)
  have hpath : BytesAt st1.data.dmem (r.off 19008) (slice r.sigBytes (32 + 176 * c) 160) := by
    have := copy hm1' (r := 0) (o := 18528) (r' := 1) (o' := 16) (n := 160) rfl (by decide)
      (by decide) (length_slice_sigB r (a := 32 + 176 * c) (n := 160) (by omega))
      (by
        show BytesAt m.dmem (r.sigPtr + BitVec.ofNat 64 (16 + 176 * c) + BitVec.ofNat 64 16) _
        rw [addr_add, show 16 + 176 * c + 16 = 32 + 176 * c by omega]
        exact bytesAt_sig_sub r hpre hF.2.2.2.1 (by omega))
    rwa [off_add] at this
  have hM1 : OpenMem r c st1.data.dmem :=
    hM.keep r hpre (by omega) hout1 (by decide) (by decide) (by left; omega)
  have hR1 : OpenRegs r c st1.data :=
    OpenRegs.of_eq r (keepsRegs_regs (rs := openRegs) hm1 hm1' (by decide)).2 hR
  have h28 : (st1.data.regs.getXReg .X28).toBitVec =
      r.sigPtr + BitVec.ofNat 64 (16 + 176 * c) + BitVec.ofInt 64 (-4144) :=
    (hm1'.regs .X28 _ rfl).trans hx28
  refine memcpy_frame r hpre hc hpc1 hF1 (a := 484) (b := 19008) (n := 160)
    ((hm1'.regs .X0 _ rfl).trans (eval_ptr_off r (i := 0) rfl 4))
    ((hm1'.regs .X1 _ rfl).trans (eval_ptr_off r (i := 0) rfl 18528))
    (by show (st1.data.regs.getXReg .X2).toBitVec.toNat = 160; rw [hm1'.regs .X2 _ rfl]; rfl)
    (by decide) (by decide) (by decide) fun st2 hpc2 hF2 hS2 hb2 hout2 ↦ ?_
  have hp1 := hpath.bytesOf
  rw [length_slice_sigB r (a := 32 + 176 * c) (n := 160) (by omega)] at hp1
  rw [hp1] at hb2
  exact .done _ ⟨pc_next r hpc2 rfl, hF2, hM1.keep r hpre (by omega) hout2 (by decide) (by decide)
    (by right; decide), hR1.of_saved r hS2, hb2, by rw [hS2.1 .X28 rfl]; exact h28⟩

/-- **`b4`** and its `memcpy`. -/
theorem open_b4 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {c : Nat} (hc24 : c < 24)
    {st2 : MachineState} (h : Mid1 r c st2) :
    Eventually (step1 NativeRustcArm.Host.exe) (Mid2 r c) st2 := by
  obtain ⟨hpc2, hF2, hM2, hR2, hb2, h28⟩ := h
  have hk4 : b4.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b4Offset) :=
    b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf2 : (openEnv r st2.data c).WF := wf_frame_sig r hpre hF2.2.2.2.1 hF2.2.2.2.2
    (a := 480) (n := 21136) (s := 16 + 176 * c) (k := 176) (by decide) (by omega) (by decide) _
  have hm2 : Match (openEnv r st2.data c) open4S st2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ off_aligned r hpre (by decide) (by decide),
        ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩⟩
      (sp_frame480 r hF2 rfl) ⟨hR2.2.2.2.1.trans (eval_ptr_off r (i := 0) rfl 4).symm, trivial⟩
      trivial trivial ⟨h28, trivial⟩
  refine exec_at hk4 run_b4 hwf2 hpc2 hm2 fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hF3, hout3⟩ := frame_block r hpre hF2 (d := 480) (lo := 164) (hi := 180) rfl
    (by decide) (by decide) (by decide) hm2 hm3 hwf2 (by decide) (by decide)
  have hsec : BytesAt st3.data.dmem (r.off (484 + 160)) (slice r.sigBytes (16 + 176 * c) 16) := by
    have := copy hm3 (r := 0) (o := 164) (r' := 1) (o' := 0) (n := 16) rfl (by decide)
      (by decide) (length_slice_sigB r (a := 16 + 176 * c) (n := 16) (by omega))
      (by
        show BytesAt st2.data.dmem (r.sigPtr + BitVec.ofNat 64 (16 + 176 * c) + BitVec.ofNat 64 0) _
        rw [add_ofNat_zero]
        exact bytesAt_sig_sub r hpre hF2.2.2.2.1 (by omega))
    rwa [off_add] at this
  have hob : BytesAt st3.data.dmem (r.off 484) (obytesB r.sigBytes c) := by
    refine BytesAt.append (keep r hpre hb2 hout3 (length_slice_sigB r (a := 32 + 176 * c) (n := 160)
      (by omega)) (by left; decide) (by decide) (by decide)) ?_
    rw [length_slice_sigB r (a := 32 + 176 * c) (n := 160) (by omega), off_add]
    exact hsec
  have hM3 := hM2.keep r hpre (by omega) hout3 (by decide) (by decide) (by right; decide)
  have hR3 : OpenRegs r c st3.data :=
    OpenRegs.of_eq r (keepsRegs_regs (rs := openRegs) hm2 hm3 (by decide)).2 hR2
  refine memcpy_frame r hpre hc hpc3 hF3 (a := 19008) (b := 484) (n := 176)
    ((hm3.regs .X0 _ rfl).trans (eval_ptr_off r (i := 0) rfl 18528))
    ((hm3.regs .X1 _ rfl).trans (eval_ptr_off r (i := 0) rfl 4))
    (by show (st3.data.regs.getXReg .X2).toBitVec.toNat = 176; rw [hm3.regs .X2 _ rfl]; rfl)
    (by decide) (by decide) (by decide) fun st4 hpc4 hF4 hS4 hb4 hout4 ↦ ?_
  have hp2 := hob.bytesOf
  rw [length_obytesB r.hsig hc24] at hp2
  rw [hp2] at hb4
  exact .done _ ⟨pc_next r hpc4 rfl, hF4, hM3.keep r hpre (by omega) hout4 (by decide) (by decide)
    (by left; omega), hR3.of_saved r hS4, hb4⟩

/-- **`b5`** and its `memcpy`. -/
theorem open_b5 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {c : Nat} (hc24 : c < 24)
    {st4 : MachineState} (h : Mid2 r c st4) :
    Eventually (step1 NativeRustcArm.Host.exe) (Mid3 r c) st4 := by
  obtain ⟨hpc4, hF4, hM4, hR4, hb4⟩ := h
  have hk5 : b5.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b5Offset) :=
    b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk5 run_b5 (Env.wf_nil _) hpc4 (match_nil _) fun st5 hm5 hpc5 ↦ ?_
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq (Env.wf_nil _) rfl
  obtain ⟨hsp5, hreg5⟩ := keepsRegs_regs (rs := openRegs) (match_nil _) hm5 (by decide)
  have hF5 := frame_of_same r hF4 hd5 hsp5 (hreg5 .X29 (by simp))
  have hR5 := OpenRegs.of_eq r hreg5 hR4
  have h0 : (st5.data.regs.getXReg .X0).toBitVec = r.off (8640 + 176 * c) := by
    have h24' : (st4.data.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (2 ^ 64 - 4224 + 176 * c) :=
      hR4.2.2.2.2.2.1
    have h25' : (st4.data.regs.getXReg .X25).toBitVec = r.off 8640 := hR4.2.2.2.2.2.2.1
    have h26' : (st4.data.regs.getXReg .X26).toBitVec = BitVec.ofNat 64 4224 := hR4.2.2.2.2.2.2.2.1
    rw [hm5.regs .X0 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs, h24', h25', h26']
    exact off_wrap r 8640 4224 (176 * c) (by decide)
  have h1 : (st5.data.regs.getXReg .X1).toBitVec = r.off 19008 := by
    rw [hm5.regs .X1 _ rfl]
    sym_simp
    show st4.data.regs.SP.toBitVec + _ = _
    rw [hF4.1]
    rfl
  refine memcpy_frame r hpre hc hpc5 hF5 (a := 8640 + 176 * c) (b := 19008) (n := 176) h0 h1
    (by show (st5.data.regs.getXReg .X2).toBitVec.toNat = 176; rw [hm5.regs .X2 _ rfl]; rfl)
    (by omega) (by decide) (by left; omega) fun st6 hpc6 hF6 hS6 hb6 hout6 ↦ ?_
  have hp3 := hb4.bytesOf
  rw [length_obytesB r.hsig hc24] at hp3
  rw [hd5, hp3] at hb6
  have hM6 := (hd5 ▸ hM4).keep r hpre (by omega) hout6 (by omega) (by omega) (by left; omega)
  have hopen : BytesAt st6.data.dmem (r.off 8640) ((List.range (c + 1)).map (obytesB r.sigBytes)).flatten := by
    rw [List.range_succ, List.map_append, List.flatten_append]
    refine BytesAt.append hM6.2.2 ?_
    rw [length_openingsB r.hsig (by omega), off_add]
    simpa using hb6
  exact .done _ ⟨pc_next r hpc6 rfl, hF6, ⟨hM6.1, hM6.2.1, hopen⟩, hR5.of_saved r hS6⟩

/-- **`b6`**: the count. -/
theorem open_b6 (hp : Placed code r.k) {c : Nat} (hc24 : c < 24) {st6 : MachineState}
    (h : Mid3 r c st6) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ (st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b7Offset ∧ AtOpen r 24 st.data) ∨
      (c + 1 < 24 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset ∧ AtOpen r (c + 1) st.data)) st6 := by
  obtain ⟨hpc6, hF6, hM6, hR6⟩ := h
  have hk6 : b6.IsInfixAt NativeRustcArm.Host.prog (r.k + NativeRustcArm.Sphincs.SphincsVerify.b6Offset) :=
    b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk6 run_b6 (Env.wf_nil _) hpc6 (match_nil _) fun st7 hm7 hpc7 ↦ ?_
  have hd7 : st7.data.dmem = st6.data.dmem := hm7.dmem_eq (Env.wf_nil _) rfl
  obtain ⟨hsp7, hreg7⟩ := keepsRegs_regs (rs := [.X19, .X20, .X21, .X22, .X23, .X25, .X26, .X27, .X29])
    (match_nil _) hm7 (by decide)
  have hF7 := frame_of_same r hF6 hd7 hsp7 (hreg7 .X29 (by simp))
  have h24' : (st6.data.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (2 ^ 64 - 4224 + 176 * c) :=
    hR6.2.2.2.2.2.1
  have hR7 : OpenRegs r (c + 1) st7.data := by
    obtain ⟨g19, g20, g21, g22, g23, -, g25, g26, g27⟩ := hR6
    have e : ∀ x ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X26, .X27, .X29], ∀ v,
        Run.RegIs st6.data x v → Run.RegIs st7.data x v := fun x hx v h' => by
      unfold Run.RegIs at *
      rw [hreg7 x hx]
      exact h'
    refine ⟨e .X19 (by simp) _ g19, e .X20 (by simp) _ g20, e .X21 (by simp) _ g21,
      e .X22 (by simp) _ g22, e .X23 (by simp) _ g23, ?_, e .X25 (by simp) _ g25,
      e .X26 (by simp) _ g26, e .X27 (by simp) _ g27⟩
    rw [Run.RegIs, hm7.regs .X24 _ rfl]
    sym_simp
    rw [Env.ofMachine_regs, h24']
    bv_lin
  have hM7 : OpenMem r (c + 1) st7.data.dmem := hd7 ▸ hM6
  simp only [PcOk] at hpc7
  sym_simp at hpc7
  rw [Env.ofMachine_regs, h24'] at hpc7
  split at hpc7
  · rename_i hcond
    have hc1 : c + 1 < 24 := by
      by_contra hcon
      obtain rfl : c = 23 := by omega
      revert hcond
      decide
    rw [hp.label NativeRustcArm.Sphincs.SphincsVerify.label_3_at] at hpc7
    exact .done _ (Or.inr ⟨hc1, hpc7, hF7, hM7, hR7⟩)
  · rename_i hcond
    have hc1 : c = 23 := by
      have hc' : BitVec.ofNat 64 (2 ^ 64 - 4224 + 176 * c) + 176#64 = 0#64 := by simpa using hcond
      have := congrArg BitVec.toNat hc'
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
    subst hc1
    exact .done _ (Or.inl ⟨pc_next r hpc7 rfl, hF7, hM7, hR7⟩)

/-- **Turn `c` of the openings' loop.** -/
theorem open_turn (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {c : Nat} (hc24 : c < 24)
    {m : MachineData} (h : AtOpen r c m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ (st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b7Offset ∧ AtOpen r 24 st.data) ∨
      (c + 1 < 24 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset ∧ AtOpen r (c + 1) st.data)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset⟩ :=
  Eventually.bind (open_b3 r hp hc hpre hc24 h) fun _ h1 ↦
    Eventually.bind (open_b4 r hp hc hpre hc24 h1) fun _ h2 ↦
      Eventually.bind (open_b5 r hp hc hpre hc24 h2) fun _ h3 ↦ open_b6 r hp hc24 h3

/-- **The openings' loop**: from `AtOpen 0` at `b3`, `AtOpen 24` at `b7`. -/
theorem open_loop (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {st : MachineState}
    (h : st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset ∧ AtOpen r 0 st.data) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b7Offset ∧ AtOpen r 24 st.data) st :=
  count_loop (P := fun c st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b3Offset ∧ AtOpen r c st.data) 24
    (fun c st hc24 ⟨hpc, h⟩ ↦ by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc
      exact open_turn r hp hc hpre hc24 h) (by decide) h

end

end NativeRustcArm.SphincsVerifyProof.Parse
