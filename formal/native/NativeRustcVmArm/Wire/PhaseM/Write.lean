module

public import NativeRustcVmArm.Code.Vm.ClimbLevel.Names
public import NativeRustcVmArm.Code.Vm.WriteOpenings.Names
public import NativeRustcVmArm.Wire.PhaseM.ClimbStep

/-!
# `phase_m`: the openings written

`write_run`: from `write_openings`' call (`Pre36`), the queries, the positions, the leaves, the
levels of siblings and their counts passed (`b36`, the counts' and the phase's addresses at SP),
`write_openings`' contract writes the phase at `out`, to the way out (`AtDone`).
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

public section

theorem disjoint_cons {r : Region} {rs : List Region} (h : ∀ r' ∈ rs, NativeRustcVm.Apart r.addr
    r.size r'.addr r'.size) (hrs : NativeRustcVm.Disjoint rs) : NativeRustcVm.Disjoint (r :: rs) :=
  List.Pairwise.cons h hrs

theorem disjoint8 {a1 a2 a3 a4 a5 a6 a7 a8 : BitVec 64} {n1 n2 n3 n4 n5 n6 n7 n8 : Nat}
    (h12 : NativeRustcVm.Apart a1 n1 a2 n2) (h13 : NativeRustcVm.Apart a1 n1 a3 n3)
    (h14 : NativeRustcVm.Apart a1 n1 a4 n4) (h15 : NativeRustcVm.Apart a1 n1 a5 n5)
    (h16 : NativeRustcVm.Apart a1 n1 a6 n6) (h17 : NativeRustcVm.Apart a1 n1 a7 n7)
    (h18 : NativeRustcVm.Apart a1 n1 a8 n8)
    (h23 : NativeRustcVm.Apart a2 n2 a3 n3) (h24 : NativeRustcVm.Apart a2 n2 a4 n4)
    (h25 : NativeRustcVm.Apart a2 n2 a5 n5) (h26 : NativeRustcVm.Apart a2 n2 a6 n6)
    (h27 : NativeRustcVm.Apart a2 n2 a7 n7) (h28 : NativeRustcVm.Apart a2 n2 a8 n8)
    (h34 : NativeRustcVm.Apart a3 n3 a4 n4) (h35 : NativeRustcVm.Apart a3 n3 a5 n5)
    (h36 : NativeRustcVm.Apart a3 n3 a6 n6) (h37 : NativeRustcVm.Apart a3 n3 a7 n7)
    (h38 : NativeRustcVm.Apart a3 n3 a8 n8)
    (h45 : NativeRustcVm.Apart a4 n4 a5 n5) (h46 : NativeRustcVm.Apart a4 n4 a6 n6)
    (h47 : NativeRustcVm.Apart a4 n4 a7 n7) (h48 : NativeRustcVm.Apart a4 n4 a8 n8)
    (h56 : NativeRustcVm.Apart a5 n5 a6 n6) (h57 : NativeRustcVm.Apart a5 n5 a7 n7)
    (h58 : NativeRustcVm.Apart a5 n5 a8 n8)
    (h67 : NativeRustcVm.Apart a6 n6 a7 n7) (h68 : NativeRustcVm.Apart a6 n6 a8 n8)
    (h78 : NativeRustcVm.Apart a7 n7 a8 n8) :
    NativeRustcVm.Disjoint [⟨a1, n1⟩, ⟨a2, n2⟩, ⟨a3, n3⟩, ⟨a4, n4⟩, ⟨a5, n5⟩, ⟨a6, n6⟩, ⟨a7, n7⟩,
      ⟨a8, n8⟩] := by
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
    implies_true]
  exact ⟨⟨h12, h13, h14, h15, h16, h17, h18⟩, ⟨h23, h24, h25, h26, h27, h28⟩,
    ⟨h34, h35, h36, h37, h38⟩, ⟨h45, h46, h47, h48⟩, ⟨h56, h57, h58⟩, ⟨h67, h68⟩, h78⟩

theorem mem_sortD_of {qs : List Nat} {q : Nat} (h : q ∈ qs) : q ∈ sortD qs := by
  have := ((sortD_aux qs [] List.Pairwise.nil).2 q).2 (.inl h)
  exact this

theorem apart_weak {a b : BitVec 64} {N n m : Nat} (h : NativeRustcVm.Apart a N b m) (hn : n ≤ N) :
    NativeRustcVm.Apart a n b m := by
  unfold NativeRustcVm.Apart at *; omega

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

/-- A part of the working area, possibly empty, apart from what the area is apart from. -/
theorem Geo.wa_apart0 [Labels] (G : Geo m0 bp B) {o n : Nat} (ho : o < workBytes)
    (hon : o + n ≤ workBytes) {b : BitVec 64} {m : Nat}
    (h : NativeRustcVm.Apart (wk m0) workBytes b m) : NativeRustcVm.Apart (wa m0 o) n b m := by
  have hw := G.wa_toNat ho
  unfold NativeRustcVm.Apart at *
  rw [hw]; omega

/-- The frame's first bytes apart from what the stack is apart from. -/
theorem Geo.frame_apart [Labels] (G : Geo m0 bp B) {b : BitVec 64} {m : Nat}
    (h : NativeRustcVm.Apart (base m0 1184) 1184 b m) :
    NativeRustcVm.Apart (base m0 192) 16 b m := by
  have h1 := G.base_toNat (F := 192) (by omega)
  have h2 := G.base_toNat (F := 1184) le_rfl
  have := G.sp
  unfold NativeRustcVm.Apart at *
  rw [h1]; rw [h2] at h; omega

variable [Host] {k : Nat}

/-- **The openings written.** -/
theorem write_run (hp : Placed code k) (G : Geo m0 bp B)
    (hwo : Spec (Labels.label NativeRustcVmArm.Vm.WriteOpenings.entryLabel) WriteOpeningsPre WriteOpeningsPost) {count : Nat}
    {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 : Nat}
    {sl : List (List (Nat × Digest))} {cf : Nat} {st : MachineState}
    (h : Pre36 m0 bp B c k count qs height lw rows c6 sl cf st) :
    Eventually (step1 Host.exe) (AtDone m0 bp B c k) st := by
  obtain ⟨hpc, hb, hM, hmod, hsll, hsb, hrd, x21, x24, x26, x5, x8, x29⟩ := h
  have hst := G.st
  have hW : workBytes = 483584 := workBytes_eq
  have hql := hM.len
  have hps := hM.ps256
  have hc0 := hM.cnt0
  have hcnt := hM.cnt
  have h32 := hM.h32
  have h64 := hM.lw64
  have hps0 := hM.ps0
  -- `b36`
  refine blkW hp b36_in_code (by simp [b36]) run_b36 (by decide) rfl hst hb.fr hpc
    fun s1 hfr1 hs1 hm1 hpc1 ↦ ?_
  have hm := frEnv_match hst hb.fr
  have hwf := frEnv_wf hst hb.fr
  have r1 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X24, .X26], s1.data.regs.getXReg r =
      st.data.regs.getXReg r := regs_of hm hm1 (by decide)
  have hb1 : Base m0 s1.data := hb.of_regs hfr1 fun r hr ↦ r1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)
  have hs16 := Match.sameOutside_in hm1 hwf (r0 := 0) (o := 0) (n := 16) rfl (by omega)
    (by decide)
  have hsC : SameOutside st.data.dmem s1.data.dmem (Chg m0 []) :=
    NativeRustcVm.SameOutside.mono hs16 fun q hq ↦ frame_chg hst (by omega) hq
  have hM1 : Mid m0 B c count qs height lw rows c6 s1.data.dmem :=
    hM.keep G hsC (by simp)
      (FW.frame hst hs16 (by omega) (by omega) (.inr (by omega)) hM.f56)
      (FW.frame hst hs16 (by omega) (by omega) (.inr (by omega)) hM.f48)
      (FW.frame hst hs16 (by omega) (by omega) (.inr (by omega)) hM.f40)
      (FW.frame hst hs16 (by omega) (by omega) (.inr (by omega)) hM.f32)
  have hrd1 : ReaderAt s1.data.dmem (rdr m0) bp B cf := reader_fr G hs16 (by omega) hrd
  have hsb1 : SibsAt s1.data.dmem (sibA m0) (cntA m0) sl :=
    sibs_keep hsb hsC (fun i hi ↦ by
        rw [hsll, nodesBytes_eq] at hi
        exact G.not_chg (L := []) (o := 24832) (n := 10240 * height) (by rw [hW]; omega)
          (by simp) i hi)
      (fun i hi ↦ by
        rw [hsll] at hi
        exact G.not_chg (L := []) (o := 24576) (n := 8 * height) (by rw [hW]; omega)
          (by simp) i hi)
  -- the arguments
  have e48 : (frEnv m0 st.data).load 0 48 8 = wa m0 2048 := load_fw hM.f48
  have e40 : (frEnv m0 st.data).load 0 40 8 = wa m0 352512 := load_fw hM.f40
  have x0 : s1.data.regs.X0.toBitVec = wa m0 0 := by
    show (s1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1.regs .X0 _ rfl]; show (st.data.regs.getXReg .X19).toBitVec = _
    rw [hb.x19]; simp [wa]
  have x1 : s1.data.regs.X1.toNat = count := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm1.regs .X1 _ rfl]; exact x21
  have x2 : s1.data.regs.X2.toBitVec = wa m0 2048 := by
    show (s1.data.regs.getXReg .X2).toBitVec = _
    rw [hm1.regs .X2 _ rfl]; exact e48
  have x3 : s1.data.regs.X3.toNat = (sortD qs).length := by
    show (s1.data.regs.getXReg .X3).toBitVec.toNat = _
    rw [hm1.regs .X3 _ rfl]; exact x26
  have x4 : s1.data.regs.X4.toBitVec = wa m0 352512 := by
    show (s1.data.regs.getXReg .X4).toBitVec = _
    rw [hm1.regs .X4 _ rfl]; exact e40
  have x5' : s1.data.regs.X5.toNat = lw := by
    show (s1.data.regs.getXReg .X5).toBitVec.toNat = _
    rw [hm1.regs .X5 _ rfl]; exact x5
  have x6 : s1.data.regs.X6.toNat = height := by
    show (s1.data.regs.getXReg .X6).toBitVec.toNat = _
    rw [hm1.regs .X6 _ rfl]; exact x24
  have x7 : s1.data.regs.X7.toBitVec = sibA m0 := by
    show (s1.data.regs.getXReg .X7).toBitVec = _
    rw [hm1.regs .X7 _ rfl]; exact x29
  have hsp1 : s1.data.regs.SP.toBitVec = base m0 192 := hfr1.sp
  have wc : WordAt s1.data.dmem s1.data.regs.SP.toBitVec (UInt64.ofBitVec (cntA m0)) := by
    have := hm1.bytesAt_write (r := 0) (o := 0) (n := 8) (b := base m0 192) (sz := 192) rfl
      (by omega) (v := .reg .X8) (by decide)
    have hw := wordAt_reg this
    simp only [Sym.eval, Env.ofMachine_regs, NativeRustcVm.addr_add_zero] at hw
    rw [x8] at hw
    rw [hsp1]; exact hw
  have wo : WordAt s1.data.dmem (s1.data.regs.SP.toBitVec + BitVec.ofNat 64 8)
      (UInt64.ofBitVec (outA m0)) := by
    have := hm1.bytesAt_write (r := 0) (o := 8) (n := 8) (b := base m0 192) (sz := 192) rfl
      (by omega) (v := .reg .X20) (by decide)
    have hw := wordAt_reg this
    simp only [Sym.eval, Env.ofMachine_regs] at hw
    rw [hb.x20] at hw
    rw [hsp1]; exact hw
  have hNs : 192 + writeOpeningsStack ≤ 1184 := by unfold writeOpeningsStack findStack; omega
  have hsp := G.sp
  have hb0 := G.base_toNat (F := 192) (by omega)
  have hSPl := m0.regs.SP.toNat_lt
  have hpre : WriteOpeningsPre s1.data := by
    refine ⟨hfr1.stackOk hst (by decide) hNs, by rw [x1]; exact hcnt, by rw [x3]; exact hps,
      by rw [x5']; exact h64, by rw [x6]; exact h32, by rw [x1]; exact hc0, by rw [x3]; exact hps0,
      cntA m0, outA m0, wc, wo, ?_, ?_⟩
    · intro R hR
      simp only [writeOpeningsRegions, List.mem_cons, List.not_mem_nil, or_false] at hR
      rw [x0, x1, x2, x3, x4, x6, x7] at hR
      rcases hR with rfl | rfl | rfl | rfl | rfl | rfl
      · exact G.wa_ok (by rw [hW]; omega) hfr1.kept
      · exact G.wa_ok (by rw [hW]; omega) hfr1.kept
      · exact G.wa_ok (by rw [hW]; omega) hfr1.kept
      · exact G.wa_ok (by rw [nodesBytes_eq, hW]; omega) hfr1.kept
      · exact G.wa_ok (by rw [hW]; omega) hfr1.kept
      · exact ⟨fun i hi ↦ hfr1.kept _ (G.oOk.1 i hi), G.oOk.2⟩
    · simp only [writeOpeningsRegions]
      rw [x0, x1, x2, x3, x4, x6, x7, nodesBytes_eq, hsp1]
      have hSw : ∀ {o n : Nat}, o < workBytes → o + n ≤ workBytes →
          NativeRustcVm.Apart (stackBelow s1.data writeOpeningsStack) writeOpeningsStack
            (wa m0 o) n := fun ho hon ↦
        (hfr1.apart hsp (G.wa_apart0 ho hon G.sW.symm) hNs).symm
      have hFw : ∀ {o n : Nat}, o < workBytes → o + n ≤ workBytes →
          NativeRustcVm.Apart (base m0 192) 16 (wa m0 o) n := fun ho hon ↦
        G.frame_apart (G.wa_apart0 ho hon G.sW.symm).symm
      have hOw : ∀ {o n : Nat}, o < workBytes → o + n ≤ workBytes →
          NativeRustcVm.Apart (wa m0 o) n (outA m0) phaseBytes := fun ho hon ↦
        G.wa_apart0 ho hon G.oW.symm
      have hSF : NativeRustcVm.Apart (stackBelow s1.data writeOpeningsStack) writeOpeningsStack
          (base m0 192) 16 := by
        rw [Ring.stackBelow_eq hfr1.sp (by omega)]
        unfold NativeRustcVm.Apart
        rw [Ring.base_toNat (by omega), hb0]
        unfold writeOpeningsStack findStack; omega
      have hSO := (hfr1.apart hsp G.sO.symm hNs).symm
      have hFO := G.frame_apart G.sO
      have hww : ∀ {o n o' n' : Nat}, o + n ≤ workBytes → o' + n' ≤ workBytes →
          o + n ≤ o' ∨ o' + n' ≤ o → NativeRustcVm.Apart (wa m0 o) n (wa m0 o') n' :=
        fun h1 h2 h3 ↦ G.wa_wa h1 h2 h3
      have w0 : (0 : Nat) < workBytes := by rw [hW]; omega
      have w2 : (2048 : Nat) < workBytes := by rw [hW]; omega
      have w3 : (352512 : Nat) < workBytes := by rw [hW]; omega
      have w4 : (24832 : Nat) < workBytes := by rw [hW]; omega
      have w5 : (24576 : Nat) < workBytes := by rw [hW]; omega
      have l1 : 0 + 8 * count ≤ workBytes := by rw [hW]; omega
      have l2 : 2048 + 8 * (sortD qs).length ≤ workBytes := by rw [hW]; omega
      have l3 : 352512 + 512 * (sortD qs).length ≤ workBytes := by rw [hW]; omega
      have l4 : 24832 + 10240 * height ≤ workBytes := by rw [hW]; omega
      have l5 : 24576 + 8 * height ≤ workBytes := by rw [hW]; omega
      exact disjoint8 hSF (hSw w0 l1) (hSw w2 l2) (hSw w3 l3) (hSw w4 l4) (hSw w5 l5) hSO
        (hFw w0 l1) (hFw w2 l2) (hFw w3 l3) (hFw w4 l4) (hFw w5 l5) hFO
        (hww l1 l2 (by omega)) (hww l1 l3 (by omega)) (hww l1 l4 (by omega)) (hww l1 l5 (by omega))
        (hOw w0 l1)
        (hww l2 l3 (by omega)) (hww l2 l4 (by omega)) (hww l2 l5 (by omega)) (hOw w2 l2)
        (hww l3 l4 (by omega)) (hww l3 l5 (by omega)) (hOw w3 l3)
        (hww l4 l5 (by omega)) (hOw w4 l4) (hOw w5 l5)
  simp only [PcOk] at hpc1
  have hQ : ∀ m', WriteOpeningsPost s1.data m' → SameOutside s1.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow s1.data writeOpeningsStack) writeOpeningsStack q ∨
      outs (rdr m0) (W m0) q) ∧ Saved s1.data m' := by
    intro m' hq
    obtain ⟨-, hs, hsv⟩ := hq (cntA m0) (outA m0) wc wo
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q ⟨R, hR, hq⟩ ↦ ?_, hsv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact .inr (.inr (.inl hq))
    · exact .inl hq
  refine Fr.leafAt (N' := writeOpeningsStack) hfr1 hst.2.1 hNs (by simp) (by decide)
    (fun q hq ↦ G.rgeo.not_frame (by omega) hq) hwo hpc1 hpre hQ fun m3 hfr3 hq3 hcs ↦ .done _ ?_
  obtain ⟨hres, hs3, -⟩ := hq3 (cntA m0) (outA m0) wc wo
  have hlen : (leavesOf lw rows).length = (sortD qs).length := by simp [hM1.rlen]
  have hres' := hres qs (sortD qs) (leavesOf lw rows) sl (by rw [x1, hql])
    (fun q hq ↦ ⟨hM1.qlt q hq, mem_sortD_of hq⟩) (by rw [x0]; exact hM1.qsW) (by rw [x3])
    (fun p hp ↦ by have := sortD_lt hM1.qlt p hp; omega) (by rw [x2]; exact hM1.psW) hlen
    (fun x hx ↦ by
      simp only [leavesOf, List.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      rw [x5']; exact length_paddedLeaf (hM1.rw r hr))
    (by rw [x4]; exact hM1.lvW) (by rw [x6]; exact hsll) (by rw [x7]; exact hsb1)
  rw [x5', x6] at hres'
  refine ⟨by simp only; rfl, hb1.call hfr3 hcs, hres'.1, _, cf,
    by rw [hM1.model]; exact climbFin_some hmod, hres'.2, ?_⟩
  exact G.rgeo.reader_frame rfl hrd1 (NativeRustcVm.SameOutside.mono hs3 fun q ⟨R, hR, hq⟩ ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact .inr (.inl hq)
    · exact .inl (stack_sub hst hfr1 hNs hq))


/-- **The climb.** -/
theorem climb_run (hp : Placed code k) (G : Geo m0 bp B)
    (hcl : Spec (Labels.label NativeRustcVmArm.Vm.ClimbLevel.entryLabel) ClimbLevelPre ClimbLevelPost) {count : Nat}
    {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 : Nat} {st : MachineState}
    (h : Climb0 m0 bp B c k count qs height lw rows c6 st) :
    Eventually (step1 Host.exe) (fun st' ↦ AtNone m0 B c k st' ∨
      ∃ sl cf, Pre36 m0 bp B c k count qs height lw rows c6 sl cf st') st :=
  Eventually.bind (climb_entry hp G h) fun _ h0 ↦ by
    rcases h0 with h0 | h0
    · exact .done _ (.inr h0)
    · exact Sym.loop (tr := step1 Host.exe)
        (fun n st ↦ ∃ l acc ns cl, n = height - l ∧
          ClimbSt m0 bp B c k count qs height lw rows c6 l acc ns cl st)
        (fun _ _ ⟨l, acc, ns, cl, hn, hi⟩ ↦ Eventually.mono (climb_step hp G hcl hi) fun _ h' ↦ by
          rcases h' with h' | ⟨acc', ns', cl', h'⟩ | h'
          · exact .inl (.inl h')
          · exact .inr ⟨_, by have := hi.ll; omega, l + 1, acc', ns', cl', rfl, h'⟩
          · exact .inl (.inr h'))
        ⟨0, [], _, c6, rfl, h0⟩

end

end NativeRustcVmArm.Wire.PhaseM
