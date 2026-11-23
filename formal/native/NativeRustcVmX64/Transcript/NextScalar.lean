module

public import NativeRustcVmX64.Transcript.NextScalar.Exec
public import NativeVm.Equiv.Transcript
public import NativeRustcVmX64.Code.Vm.DecodedStreamElement.Names
public import NativeRustcVmX64.Code.Vm.TStateNextScalar.Names

/-!
# `TState::next_scalar` on x86-64

**`nextScalar_spec`**: the `Option<EW>` at RDI becomes `nextScalar`'s element and the `TState` at
RSI its state, given `stream_element`'s contract. `b0` pushes R15, R14, RBX and tests the ground
challenge's tag: one waiting, `b4`, `b5` store the tag `0`. Otherwise `b1` calls `stream_element`
on the area, its length and the cursor, its output in the frame; `b2` tests its tag: `0`, `b4`,
`b5` store it; `1`, `b3`, `b5` advance the cursor and copy the element to the output.
-/

namespace NativeRustcVmX64.Transcript.NextScalar

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateNextScalar
open NativeRustcVm.Transcript NativeVm.Model

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 64 := by decide

theorem run_ground {s : TState} {c : EW} (h : s.sponge.ground = some c) :
    nextScalar.run s = none := by
  rw [NativeVm.Equiv.nextScalar_run, h]; rfl

theorem run_some {s : TState} (h : s.sponge.ground = none) {x : EW}
    (hx : s.stream[s.cursor]? = some x) :
    nextScalar.run s = some (x, { s with cursor := s.cursor + 1 }) := by
  rw [NativeVm.Equiv.nextScalar_run, h, hx]; rfl

theorem run_none {s : TState} (h : s.sponge.ground = none) (hx : s.stream[s.cursor]? = none) :
    nextScalar.run s = none := by
  rw [NativeVm.Equiv.nextScalar_run, h, hx]; rfl

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

variable [Host] {k : Nat}

/-- **`TState::next_scalar` meets its contract.** -/
theorem nextScalar_spec (hp : Placed code k)
    (hse : ∀ a stream openings, Spec (Labels.label NativeRustcVmX64.Vm.DecodedStreamElement.entryLabel)
      (StreamElementPre a stream openings) (StreamElementPost stream))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmX64.Vm.TStateNextScalar.entryLabel) (NextScalarPre a s) (NextScalarPost a s) := by
  rintro m0 ⟨hst, hts, ⟨hapT, hapA, -⟩, ⟨hom, hon, hoT, hoA, hoS, -⟩⟩
  set t := reg m0 .rsi with htdef
  set o := reg m0 .rdi with hodef
  set fb := stackBelow m0 64 with hfb
  have hn : nextScalarStack ≤ (rspOf m0).toNat := hst.1
  have hN0 : nextScalarStack = 64 + streamElementStack := rfl
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfnw : NativeRustcVm.NoWrap fb (64 + 8) := frame_noWrap hst le_rfl
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hAn' : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hAn
  have hon' : o.toNat + 24 ≤ 2 ^ 64 := hon
  have hfb' : fb.toNat + 72 ≤ 2 ^ 64 := hfnw
  have hTF : NativeRustcVm.Apart t 760 fb (64 + 8) := hapT
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb (64 + 8) := hapA
  have hoF : NativeRustcVm.Apart o 24 fb (64 + 8) := hoS
  have hRF : ∀ q, NativeRustcVm.InRange fb 64 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h (inRange_mono hq (by omega)),
      fun h ↦ not_inRange_of_apart hAF hAn hfnw h (inRange_mono hq (by omega))⟩
  have hpw := pairwise3 (R := fun x y : BitVec 64 × Nat ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2)
    (x := (fb, 64 + 8)) (y := (t, 760)) (z := (o, 24)) (Apart.symm' hTF) (Apart.symm' hoF)
    (Apart.symm' hoT)
  -- `b0`: the prologue, the ground tag.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 64) (rest := [(t, 760), (o, 24)])
    (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TStateNextScalar.b1Offset + b1.length)).toBitVec)
    ⟨frame_mapped hst le_rfl, hfnw⟩ (rest2_ok ⟨hTm, hTn⟩ ⟨hom, hon⟩ fun _ h ↦ h) hpw
  have hm0 : Match (frameEnv m0 m0 64 [(t, 760), (o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateNextScalar.b1Offset + b1.length)).toBitVec) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩
      ⟨match_rsp, known_ptr rfl rfl, known_ptr rfl rfl, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmX64.Vm.TStateNextScalar.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.TStateNextScalar.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 => ?_
  have hgr := hts.sponge.ground
  simp only [PcOk] at hpc1
  sym_simp_at hpc1
  have hstack : ∀ q, NativeRustcVm.InRange fb 64 q →
      NativeRustcVm.InRange (stackBelow m0 nextScalarStack) nextScalarStack q := fun _ h ↦ h
  cases hg : s.sponge.ground with
  | some c =>
    -- A ground challenge waits: `None`.
    rw [hg] at hgr
    have htag : (frameEnv m0 m0 64 [(t, 760), (o, 24)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.TStateNextScalar.b1Offset + b1.length)).toBitVec).load 1 304 1 = BitVec.ofNat 64 1 :=
      load1_of_tag (Or.inr rfl) hgr.1
    simp only [htag] at hpc1
    simp (config := { decide := true }) only [↓reduceIte] at hpc1
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4a hwf0 nofun
      (hpc1.trans (hp.label NativeRustcVmX64.Vm.TStateNextScalar.label_3_at)) hm1 fun st2 hm2 hpc2 => ?_
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b4a exit_a) hwf0 nofun
      (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateNextScalar.b4_next)) hm2 fun st3 hm3 hpc3 => ?_
    obtain ⟨hk3, hrsp3, hw3, hws3⟩ := ok_a
    have hs3 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem (fun q ↦
        Touch o 24 (fun _ ↦ True) q ∨ Touch fb (64 + 8) (fun j ↦ j < 64) q) :=
      sameOutside_W2 hwf0 hm3 (r := 2) (r' := 0) rfl rfl fun w hw ↦ by
        rcases hws3 w hw with ⟨hr, h⟩ | ⟨hr, h⟩
        · exact Or.inl ⟨hr, h, fun _ _ _ ↦ trivial⟩
        · exact Or.inr ⟨hr, by omega, fun _ _ _ ↦ by omega⟩
    simp only [PcOk] at hpc3
    refine .done _ ⟨by rw [hpc3]; exact Frame.entry.load_ret hst le_rfl, ?_, ?_, ?_, ?_,
      Match.saved hm0 hm3 hwf0 rfl hk3⟩
    · exact (hm3.regs .rsp _ hrsp3).trans ((eval_ptr0 (o := 72)).trans (frame_add 64 8))
    · rw [run_ground hg]
      have := wordAt_write hm3 (r := 2) (o := 0) rfl (by decide) fun i hi ↦ by
        rw [Nat.zero_add]; exact hw3 i hi
      rwa [off_zero] at this
    · rw [run_ground hg]; intro x s' h; cases h
    · intro q hq
      refine hs3 q fun h ↦ hq ?_
      rcases h with h | ⟨j, hj, hj', rfl⟩
      · exact Or.inl (inRange_of_touch hon h)
      · exact Or.inr (Or.inr (hstack _ (inRange_off_self hj' (by omega))))
  | none =>
  rw [hg] at hgr
  have htag : (frameEnv m0 m0 64 [(t, 760), (o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateNextScalar.b1Offset + b1.length)).toBitVec).load 1 304 1 = BitVec.ofNat 64 0 :=
    load1_of_tag (Or.inl rfl) hgr
  simp only [htag] at hpc1
  simp (config := { decide := true }) only [↓reduceIte] at hpc1
  -- `b1`: `call stream_element`.
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf0 (fun _ _ ↦ rfl)
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateNextScalar.b0_next)) hm1 fun st2 hm2 hpc2 => ?_
  obtain ⟨hpro, hws2, hx7, hx6, hx2, hx1, hx14, hx15, hx3⟩ := after_eq run_b1 ▸ ok_b1
  have hf2 : Frame m0 64 slots 0 st2.data :=
    Frame.of_prologue Frame.entry hwf0 hm2 hpro slots_le (by decide)
  have hs2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem (NativeRustcVm.InRange fb 64) :=
    sameOutside_low hwf0 hm2 (r := 0) rfl (by decide) hws2
  have hsp2 : rspOf st2.data = fb := by rw [hf2.sp, off_zero]
  have hlen64 : a.len < 2 ^ 64 := by
    have := hts.decoded.len
    have := streamEnd_lt a.l
    omega
  have hcur64 : s.cursor < 2 ^ 64 := by
    have := hts.cursor_le
    have := hts.decoded.stream_le
    simp only [NativeVm.maxStream] at this
    have := hts.decoded.l_lt
    omega
  have hd0 := hts.dec
  have hX7 : reg st2.data .rdi = off fb 16 := (hm2.regs .rdi _ hx7).trans (eval_ptr0 16)
  have hX6 : reg st2.data .rsi = a.words :=
    (hm2.regs .rsi _ hx6).trans (load_ofMachine (o := 328) rfl hd0.1)
  have hX2 : (reg st2.data .rdx).toNat = a.len := by
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ hx2, Sym.eval,
      load_ofMachine (o := 336) rfl (by have := hd0.2.1; rwa [off_off] at this),
      UInt64.toNat_toBitVec, toNat_toUInt64 hlen64]
  have hX1 : (reg st2.data .rcx).toNat = s.cursor := by
    rw [show reg st2.data .rcx = _ from hm2.regs .rcx _ hx1, Sym.eval,
      load_ofMachine (o := 352) rfl hts.cursor, UInt64.toNat_toBitVec, toNat_toUInt64 hcur64]
  have hX14 : reg st2.data .r14 = s.cursor.toUInt64.toBitVec :=
    (hm2.regs .r14 _ hx14).trans (load_ofMachine (o := 352) rfl hts.cursor)
  have hX15 : reg st2.data .r15 = t := (hm2.regs .r15 _ hx15).trans (eval_ptr rfl)
  have hX3 : reg st2.data .rbx = o := (hm2.regs .rbx _ hx3).trans (eval_ptr rfl)
  have hts2 : TStateAt st2.data.dmem t a s := hts.frame hf2.kept hRF hs2
  -- `stream_element`, its output at `fb + 16`.
  have h16 : (off fb 16).toNat = fb.toNat + 16 := toNat_off (by omega)
  have hpre2 : StreamElementPre a s.stream s.openings st2.data := by
    unfold StreamElementPre
    rw [hX7]
    refine ⟨stackOk_callee hst hf2.kept hsp2 (by decide), hX6, hX2,
      Region.Ok.keeps ⟨hAm, hAn⟩ hf2.kept, hts2.decoded,
      Mapped.keeps (mapped_off (frame_mapped hst le_rfl) (by decide)) hf2.kept, ?_, ?_, ?_⟩
    · show (off fb 16).toNat + 24 ≤ 2 ^ 64
      omega
    · have h : a.words.toNat + 8 * a.len ≤ fb.toNat ∨ fb.toNat + 72 ≤ a.words.toNat := hAF
      show (off fb 16).toNat + 24 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (off fb 16).toNat
      omega
    · rw [stackBelow_callee hsp2 (n' := streamElementStack) (by rw [hN0] at hn; exact hn)]
      show (off fb 16).toNat + 24 ≤ fb.toNat ∨ fb.toNat + 8 ≤ (off fb 16).toNat
      omega
  refine call_then hpc2 (hse a s.stream s.openings) hpre2
    fun st3 hpc3 hrsp3 ⟨hout3, hs3, hsv3⟩ => ?_
  rw [hX7, hX1] at hout3
  rw [hX7] at hs3
  have hnot : ∀ j, j < 64 + 8 → (j < 16 ∨ 40 ≤ j) →
      ¬ NativeRustcVm.InRange (off fb 16) 24 (off fb j) := fun j hj hj' h ↦ by
    rw [inRange_off_iff (by omega) (by omega)] at h
    omega
  have hf3 : Frame m0 64 slots 8 st3.data :=
    Frame.call_slots hf2 hsv3 hrsp3 hs3
      (fun p hp i hi ↦ hnot _ (by have := slots_le p hp; omega) (by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> simp <;> omega))
      (fun j hj ↦ hnot _ (by omega) (by omega))
  have h3 : reg st3.data .rbx = o := (hsv3.1 .rbx rfl).trans hX3
  have h15 : reg st3.data .r15 = t := (hsv3.1 .r15 rfl).trans hX15
  have h14 : reg st3.data .r14 = s.cursor.toUInt64.toBitVec := (hsv3.1 .r14 rfl).trans hX14
  -- What changed so far: the frame.
  have hfnw64 : NativeRustcVm.NoWrap fb 64 := by unfold NativeRustcVm.NoWrap; omega
  have hs13 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem (NativeRustcVm.InRange fb 64) :=
    fun q hq ↦ by
      rw [hs3 q fun h ↦ hq (inRange_of_off hfnw64 (by decide) h)]
      exact hs2 q hq
  -- `b2`: the tag, from one environment to the end.
  have hwf3 := frame_wf (m0 := m0) (d := st3.data) (F := 64) (rest := [(t, 760), (o, 24)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst le_rfl) hf3.kept, hfnw⟩
    (rest2_ok ⟨hTm, hTn⟩ ⟨hom, hon⟩ hf3.kept) hpw
  have hm3 : Match (frameEnv m0 st3.data 64 [(t, 760), (o, 24)] (fun _ ↦ 0) 0) midS st3.data :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩
      ⟨hf3.rsp_eval, known_ptr rfl h15, known_ptr rfl h3, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf3 nofun
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateNextScalar.b1_next)) hm3 fun st4 hm4 hpc4 => ?_
  simp only [PcOk] at hpc4
  sym_simp_at hpc4
  -- The end of a path: the frame restored.
  have hR : ∀ q, (NativeRustcVm.InRange o 24 q ∨ NativeRustcVm.InRange fb 64 q) →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q := by
    rintro q (hq | hq)
    · exact ⟨fun h ↦ not_inRange_of_apart hoT hon hTn hq h,
        fun h ↦ not_inRange_of_apart hoA hon hAn hq h⟩
    · exact hRF q hq
  cases hx : s.stream[s.cursor]? with
  | none =>
    -- `stream_element` returned `None`: the tag `0` stored.
    rw [hx] at hout3
    have ht0 : (frameEnv m0 st3.data 64 [(t, 760), (o, 24)] (fun _ ↦ 0) 0).load 0 16 4 =
        BitVec.ofNat 64 0 := load4_of_tag (Or.inl rfl) hout3
    simp only [ht0] at hpc4
    simp (config := { decide := true }) only [↓reduceIte] at hpc4
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4b hwf3 nofun
      (hpc4.trans (hp.label NativeRustcVmX64.Vm.TStateNextScalar.label_3_at)) hm4 fun st5 hm5 hpc5 => ?_
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b4b run_b5b) hwf3 nofun
      (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateNextScalar.b4_next)) hm5 fun st6 hm6 hpc6 => ?_
    obtain ⟨hepi, hw6, hws6⟩ := after_eq run_b5b ▸ ok_b
    obtain ⟨hsv6, hrsp6⟩ := Frame.epilogue hf3 hwf3 hm6 hepi
    have hs6 := sameOutside_region hwf3 hm6 (r := 2) rfl hws6
    simp only [PcOk] at hpc6
    refine .done _ ⟨by rw [hpc6]; exact hf3.load_ret hst le_rfl, hrsp6, ?_, ?_, ?_, hsv6⟩
    · rw [run_none hg hx]
      have := wordAt_write hm6 (r := 2) (o := 0) rfl (by decide) fun i hi ↦ by
        rw [Nat.zero_add]; exact hw6 i hi
      rwa [off_zero] at this
    · rw [run_none hg hx]; intro x s' h; cases h
    · intro q hq
      rw [hs6 q fun h ↦ hq (Or.inl h)]
      exact hs13 q fun h ↦ hq (Or.inr (Or.inr (hstack q h)))
  | some x =>
  -- `b3`: the cursor advanced, the element copied.
  rw [hx] at hout3
  obtain ⟨ht1, hel⟩ := hout3
  have ht1' : (frameEnv m0 st3.data 64 [(t, 760), (o, 24)] (fun _ ↦ 0) 0).load 0 16 4 =
      BitVec.ofNat 64 1 := load4_of_tag (Or.inr rfl) ht1
  simp only [ht1'] at hpc4
  simp (config := { decide := true }) only [↓reduceIte] at hpc4
  obtain ⟨hlt, hxv⟩ := Array.getElem?_eq_some_iff.mp hx
  rw [ewAt_iff, off_off, off_off] at hel
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf3 nofun
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateNextScalar.b2_next)) hm4 fun st5 hm5 hpc5 => ?_
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b3 run_b5c) hwf3 nofun
    (hpc5.trans (hp.label NativeRustcVmX64.Vm.TStateNextScalar.label_4_at)) hm5 fun st6 hm6 hpc6 => ?_
  obtain ⟨hepi, hwt, hw0, hw1, hwc, hws6⟩ := after_eq run_b5c ▸ ok_c
  obtain ⟨hsv6, hrsp6⟩ := Frame.epilogue hf3 hwf3 hm6 hepi
  have hs6 : NativeRustcVm.SameOutside st3.data.dmem st6.data.dmem (fun q ↦
      Touch t 760 (fun j ↦ 352 ≤ j ∧ j < 360) q ∨ Touch o 24 (fun _ ↦ True) q) :=
    sameOutside_W2 hwf3 hm6 (r := 1) (r' := 2) rfl rfl fun w hw ↦ by
      rcases hws6 w hw with ⟨hr, h1, h2⟩ | ⟨hr, h⟩
      · exact Or.inl ⟨hr, by omega, fun _ _ _ ↦ by omega⟩
      · exact Or.inr ⟨hr, h, fun _ _ _ ↦ trivial⟩
  have hsz64 : s.stream.size < 2 ^ 64 := by
    have := hts.decoded.stream_le
    simp only [NativeVm.maxStream] at this
    have := hts.decoded.l_lt
    omega
  have hv : (Sym.bin .add .W64 (.reg .r14) (.lit 1)).eval
      (frameEnv m0 st3.data 64 [(t, 760), (o, 24)] (fun _ ↦ 0) 0) =
        (s.cursor + 1).toUInt64.toBitVec := by
    sym_simp
    show reg st3.data .r14 + BitVec.ofNat 64 1 = _
    rw [h14]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec s.cursor.toUInt64,
      toNat_toUInt64 hcur64, UInt64.toNat_toBitVec (s.cursor + 1).toUInt64,
      toNat_toUInt64 (by omega)]
    omega
  have hc := wordAt_write hm6 (r := 1) (o := 352) (b := t) (sz := 760) rfl (by decide) hwc
  rw [hv] at hc
  have ht := wordAt_write hm6 (r := 2) (o := 0) (b := o) (sz := 24) rfl (by decide)
    (fun i hi ↦ by rw [Nat.zero_add]; exact hwt i hi)
  rw [off_zero, show UInt64.ofBitVec ((Sym.lit 1).eval
    (frameEnv m0 st3.data 64 [(t, 760), (o, 24)] (fun _ ↦ 0) 0)) = 1 from rfl] at ht
  have hc0 := wordAt_write hm6 (r := 2) (o := 8) (b := o) (sz := 24) rfl (by decide) hw0
  rw [show (Sym.load 0 24 8).eval (frameEnv m0 st3.data 64 [(t, 760), (o, 24)] (fun _ ↦ 0) 0) = _
    from load_ofMachine (o := 24) rfl hel.1] at hc0
  have hc1 := wordAt_write hm6 (r := 2) (o := 16) (b := o) (sz := 24) rfl (by decide) hw1
  rw [show (Sym.load 0 32 8).eval (frameEnv m0 st3.data 64 [(t, 760), (o, 24)] (fun _ ↦ 0) 0) = _
    from load_ofMachine (o := 32) rfl hel.2] at hc1
  have hsAll : NativeRustcVm.SameOutside m0.dmem st6.data.dmem (fun q ↦
      Touch t tstateBytes (fun j ↦ 352 ≤ j ∧ j < 360) q ∨
        (NativeRustcVm.InRange o 24 q ∨ NativeRustcVm.InRange fb 64 q)) := fun q hq ↦ by
    simp only [not_or] at hq
    rw [hs6 q (by
      simp only [not_or]
      exact ⟨hq.1, fun h ↦ hq.2.1 (inRange_of_touch hon h)⟩)]
    exact hs13 q hq.2.2
  simp only [PcOk] at hpc6
  refine .done _ ⟨by rw [hpc6]; exact hf3.load_ret hst le_rfl, hrsp6, ?_, ?_, ?_, hsv6⟩
  · rw [run_some hg hx]
    exact ⟨ht, ewAt_iff.mpr ⟨hc0, by rw [off_off]; exact hc1⟩⟩
  · rw [run_some hg hx]
    intro x' s' h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hts.with_cursor hsv6.2 hR hsAll (by omega) hc
  · intro q hq
    simp only [not_or] at hq
    rw [hs6 q (by
      simp only [not_or]
      exact ⟨fun h ↦ hq.2.1 (inRange_of_touch hTn h), fun h ↦ hq.1 (inRange_of_touch hon h)⟩)]
    exact hs13 q fun h ↦ hq.2.2 (hstack q h)

end

end NativeRustcVmX64.Transcript.NextScalar
