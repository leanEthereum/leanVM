module

public import NativeRustcVmArm.Code.Vm.ClimbLevel.Names
public import NativeRustcVmArm.Wire.PhaseM.Climb

/-!
# `phase_m`: a level of the climb

`climb_step`: from level `l`'s head (`ClimbSt`), the count's check (`b31`), `climb_level`'s call
(`b32`) reading the level's siblings and writing its parents to the other half of the nodes, its
result's check (`b33`), the level's count stored (`b34`), to level `l + 1`'s head, or after the
last level (`b35`) to `write_openings`' call (`Pre36`).
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

public section

theorem disjoint7 {a b c d e f g : Region}
    (hab : NativeRustcVm.Apart a.addr a.size b.addr b.size)
    (hac : NativeRustcVm.Apart a.addr a.size c.addr c.size)
    (had : NativeRustcVm.Apart a.addr a.size d.addr d.size)
    (hae : NativeRustcVm.Apart a.addr a.size e.addr e.size)
    (haf : NativeRustcVm.Apart a.addr a.size f.addr f.size)
    (hag : NativeRustcVm.Apart a.addr a.size g.addr g.size)
    (hbc : NativeRustcVm.Apart b.addr b.size c.addr c.size)
    (hbd : NativeRustcVm.Apart b.addr b.size d.addr d.size)
    (hbe : NativeRustcVm.Apart b.addr b.size e.addr e.size)
    (hbf : NativeRustcVm.Apart b.addr b.size f.addr f.size)
    (hbg : NativeRustcVm.Apart b.addr b.size g.addr g.size)
    (hcd : NativeRustcVm.Apart c.addr c.size d.addr d.size)
    (hce : NativeRustcVm.Apart c.addr c.size e.addr e.size)
    (hcf : NativeRustcVm.Apart c.addr c.size f.addr f.size)
    (hcg : NativeRustcVm.Apart c.addr c.size g.addr g.size)
    (hde : NativeRustcVm.Apart d.addr d.size e.addr e.size)
    (hdf : NativeRustcVm.Apart d.addr d.size f.addr f.size)
    (hdg : NativeRustcVm.Apart d.addr d.size g.addr g.size)
    (hef : NativeRustcVm.Apart e.addr e.size f.addr f.size)
    (heg : NativeRustcVm.Apart e.addr e.size g.addr g.size)
    (hfg : NativeRustcVm.Apart f.addr f.size g.addr g.size) :
    NativeRustcVm.Disjoint [a, b, c, d, e, f, g] := by
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
    implies_true]
  exact ⟨⟨hab, hac, had, hae, haf, hag⟩, ⟨hbc, hbd, hbe, hbf, hbg⟩, ⟨hcd, hce, hcf, hcg⟩,
    ⟨hde, hdf, hdg⟩, ⟨hef, heg⟩, hfg⟩

theorem and1_apply (l : Nat) :
    CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (BitVec.ofNat 64 l) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 0) = decide (l % 2 = 0) := by
  rw [eq_apply]
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.zero_mod, decide_eq_decide]
  omega

theorem half_eq (l : Nat) : (if l % 2 = 0 then 4096 else 14336) = 4096 + 10240 * (l % 2) := by
  split <;> omega

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

omit [Host] in
theorem wa_apart' [Labels] (G : Geo m0 bp B) {o n o' n' : Nat} (h : o + n ≤ workBytes)
    (h' : o' + n' ≤ workBytes) (hle : o + n ≤ o' ∨ o' + n' ≤ o) :
    NativeRustcVm.Apart (wa m0 o) n (wa m0 o') n' := G.wa_wa h h' hle

/-- **A level of the climb.** -/
theorem climb_step (hp : Placed code k) (G : Geo m0 bp B)
    (hcl : Spec (Labels.label NativeRustcVmArm.Vm.ClimbLevel.entryLabel) ClimbLevelPre ClimbLevelPost) {count : Nat}
    {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 l : Nat}
    {acc : List (List (Nat × Digest))} {ns : List (Nat × Digest)} {cl : Nat} {st : MachineState}
    (h : ClimbSt m0 bp B c k count qs height lw rows c6 l acc ns cl st) :
    Eventually (step1 Host.exe) (fun st' ↦ AtNone m0 B c k st' ∨
      (∃ acc' ns' cl', ClimbSt m0 bp B c k count qs height lw rows c6 (l + 1) acc' ns' cl' st') ∨
      ∃ sl cf, Pre36 m0 bp B c k count qs height lw rows c6 sl cf st') st := by
  obtain ⟨hpc, hb, hM, hal, hmod, hll, hnsl, hsb, hnd, hrd, f24, x21, x24, x26, x25, x23, x27,
    x28, x29⟩ := h
  have hst := G.st
  have hW : workBytes = 483584 := workBytes_eq
  have h32 := hM.h32
  have hl2 : l % 2 < 2 := Nat.mod_lt _ (by decide)
  have hl2' : (l + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  have hlx : l % 2 + (l + 1) % 2 = 1 := by omega
  -- `b31`
  refine blk hp b31_in_code (by simp [b31]) run_b31 rfl rfl hst hb.fr hpc
    fun s1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have hm := frEnv_match hst hb.fr
  have r1 : ∀ r, s1.data.regs.getXReg r = st.data.regs.getXReg r := fun r ↦
    Match.reg_eq (v := .reg r) hm hm1 (by cases r <;> rfl) (by cases r <;> rfl)
  have hb1 : Base m0 s1.data := hb.of_regs hfr1 fun r _ ↦ r1 r
  have hc1 : (SBool.cmp .ult .W64 (.reg .X28) (.lit 257)).not.eval (frEnv m0 st.data) =
      false := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [ult_apply, show (st.data.regs.getXReg .X28).toBitVec.toNat = _ from x28]
    simp only [BitVec.toNat_ofNat]
    rw [decide_eq_true (by omega)]; rfl
  simp only [PcOk, hc1, Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b32`
  refine blk hp b32_in_code (by simp [b32]) run_b32 rfl rfl hst hfr1 hpc1
    fun s2 hfr2 hd2 hm2 hpc2 ↦ ?_
  have hm1' := frEnv_match hst hfr1
  have r2 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      s2.data.regs.getXReg r = s1.data.regs.getXReg r := regs_of hm1' hm2 (by decide)
  have hb2 : Base m0 s2.data := hb1.of_regs hfr2 fun r hr ↦ r2 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)
  have hd12 : s2.data.dmem = st.data.dmem := hd2.trans hd1
  have e25 : (s1.data.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 l := by
    rw [r1]; exact ofNat_toNat_bv x25
  have hite : CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (s1.data.regs.getXReg .X25).toBitVec
      (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) = decide (l % 2 = 0) := by
    rw [e25, and1_apply]
  have x0 : s2.data.regs.X0.toBitVec = rdr m0 := by
    show (s2.data.regs.getXReg .X0).toBitVec = _
    rw [hm2.regs .X0 _ rfl]; exact hb1.x22
  have x1 : s2.data.regs.X1.toBitVec = wa m0 (4096 + 10240 * (l % 2)) := by
    show (s2.data.regs.getXReg .X1).toBitVec = _
    rw [hm2.regs .X1 _ rfl]
    simp only [Sym.eval, SBool.eval, Env.ofMachine_regs, hite]
    rw [hb1.x19, r1 .X27, x27, add_lit]
    by_cases h2 : l % 2 = 0
    · simp only [h2, decide_true, ↓reduceIte]
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [show l % 2 = 1 by omega]
  have x2 : s2.data.regs.X2.toNat = ns.length := by
    show (s2.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm2.regs .X2 _ rfl]; show (s1.data.regs.getXReg .X28).toBitVec.toNat = _
    rw [r1]; exact x28
  have x3 : s2.data.regs.X3.toBitVec = wa m0 (24832 + 10240 * l) := by
    show (s2.data.regs.getXReg .X3).toBitVec = _
    rw [hm2.regs .X3 _ rfl]; show (s1.data.regs.getXReg .X29).toBitVec = _
    rw [r1]; exact x29
  have x4 : s2.data.regs.X4.toBitVec = wa m0 (4096 + 10240 * ((l + 1) % 2)) := by
    show (s2.data.regs.getXReg .X4).toBitVec = _
    rw [hm2.regs .X4 _ rfl]
    simp only [Sym.eval, SBool.eval, Env.ofMachine_regs, hite]
    rw [hb1.x19, r1 .X27, x27, add_lit]
    by_cases h2 : l % 2 = 0
    · simp only [h2, decide_true, ↓reduceIte]
      rw [show (l + 1) % 2 = 1 by omega]
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [show (l + 1) % 2 = 0 by omega]
  have hNs : 192 + climbLevelStack ≤ 1184 := by
    unfold climbLevelStack hashPairStack keccak256WordsStack keccakFStack; omega
  have hsp := G.sp
  have hpre : ClimbLevelPre s2.data := by
    refine ⟨hfr2.stackOk hst (by decide) hNs, G.rcAt hfr2 hNs, by rw [x2]; exact hnsl, ?_, ?_, ?_,
      bp, B, cl, by rw [x0, hd12]; exact hrd, ?_⟩
    · rw [x1, x2]; exact G.wa_ok (by rw [hW]; omega) hfr2.kept
    · rw [x3]; exact G.wa_ok (by rw [nodesBytes_eq, hW]; omega) hfr2.kept
    · rw [x4]; exact G.wa_ok (by rw [nodesBytes_eq, hW]; omega) hfr2.kept
    · rw [x0, x1, x2, x3, x4, nodesBytes_eq]
      have hSr := hfr2.apart hsp G.sR.symm hNs
      have hSb := hfr2.apart hsp G.sB.symm hNs
      have hSc := hfr2.apart hsp G.cS hNs
      have hSw : ∀ {o n : Nat}, o + n ≤ workBytes → 0 < n →
          NativeRustcVm.Apart (wa m0 o) n (stackBelow s2.data climbLevelStack) climbLevelStack :=
        fun ho hn ↦ hfr2.apart hsp (G.wa_apart ho hn G.sW.symm) hNs
      have hcw : ∀ {o n : Nat}, o + n ≤ workBytes → 0 < n →
          NativeRustcVm.Apart rcAddr 192 (wa m0 o) n := fun ho hn ↦
        (G.wa_apart ho hn G.cW.symm).symm
      have hrw : ∀ {o n : Nat}, o + n ≤ workBytes → 0 < n →
          NativeRustcVm.Apart (rdr m0) 24 (wa m0 o) n := fun ho hn ↦
        (G.wa_apart ho hn G.rW.symm).symm
      have hbw : ∀ {o n : Nat}, o + n ≤ workBytes → 0 < n →
          NativeRustcVm.Apart bp B.length (wa m0 o) n := fun ho hn ↦
        (G.wa_apart ho hn G.bW.symm).symm
      have hwk : ∀ {a b : BitVec 64} {N n m : Nat}, NativeRustcVm.Apart a N b m → n ≤ N →
          NativeRustcVm.Apart a n b m := by
        intro a b N n m h hn; unfold NativeRustcVm.Apart at *; omega
      have hs1 := hSw (o := 24832 + 10240 * l) (n := 10240) (by rw [hW]; omega) (by omega)
      have hs2' := hSw (o := 4096 + 10240 * ((l + 1) % 2)) (n := 10240) (by rw [hW]; omega)
        (by omega)
      have hc1 := hcw (o := 24832 + 10240 * l) (n := 10240) (by rw [hW]; omega) (by omega)
      have hc2 := hcw (o := 4096 + 10240 * ((l + 1) % 2)) (n := 10240) (by rw [hW]; omega)
        (by omega)
      have hr1 := hrw (o := 24832 + 10240 * l) (n := 10240) (by rw [hW]; omega) (by omega)
      have hr2 := hrw (o := 4096 + 10240 * ((l + 1) % 2)) (n := 10240) (by rw [hW]; omega)
        (by omega)
      have hb1' := hbw (o := 24832 + 10240 * l) (n := 10240) (by rw [hW]; omega) (by omega)
      have hb2' := hbw (o := 4096 + 10240 * ((l + 1) % 2)) (n := 10240) (by rw [hW]; omega)
        (by omega)
      have hsx := wa_apart' G (o := 24832 + 10240 * l) (n := 10240)
        (o' := 4096 + 10240 * ((l + 1) % 2)) (n' := 10240) (by rw [hW]; omega) (by rw [hW]; omega)
        (by omega)
      have hn1 := hwk (hSw (o := 4096 + 10240 * (l % 2)) (n := 10240) (by rw [hW]; omega)
        (by omega)) (n := 40 * ns.length) (by omega)
      have hnc := (hwk (hcw (o := 4096 + 10240 * (l % 2)) (n := 10240) (by rw [hW]; omega)
        (by omega)).symm (n := 40 * ns.length) (by omega)).symm
      have hnr := (hwk (hrw (o := 4096 + 10240 * (l % 2)) (n := 10240) (by rw [hW]; omega)
        (by omega)).symm (n := 40 * ns.length) (by omega)).symm
      have hnb := (hwk (hbw (o := 4096 + 10240 * (l % 2)) (n := 10240) (by rw [hW]; omega)
        (by omega)).symm (n := 40 * ns.length) (by omega)).symm
      have hns := wa_apart' G (o := 4096 + 10240 * (l % 2)) (n := 40 * ns.length)
        (o' := 24832 + 10240 * l) (n' := 10240) (by rw [hW]; omega) (by rw [hW]; omega)
        (by omega)
      have hnx := wa_apart' G (o := 4096 + 10240 * (l % 2)) (n := 40 * ns.length)
        (o' := 4096 + 10240 * ((l + 1) % 2)) (n' := 10240) (by rw [hW]; omega)
        (by rw [hW]; omega) (by omega)
      exact disjoint7 hSc.symm hSr.symm hSb.symm hn1.symm hs1.symm hs2'.symm G.cR G.cB hnc hc1
        hc2 G.rB hnr hr1 hr2 hnb hb1' hb2' hns hnx hsx
  simp only [PcOk] at hpc2
  have hQ : ∀ m', ClimbLevelPost s2.data m' → SameOutside s2.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow s2.data climbLevelStack) climbLevelStack q ∨ outs (rdr m0) (W m0) q) ∧
      Saved s2.data m' := by
    rintro m' ⟨-, hs, hsv⟩
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q ⟨R, hR, hq⟩ ↦ ?_, hsv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl
    · change InRange s2.data.regs.X3.toBitVec nodesBytes q at hq
      rw [x3, nodesBytes_eq] at hq
      exact .inr (.inr (.inr (NativeRustcVm.InRange.of_sub hq G.wOk.2 (by rw [hW]; omega))))
    · change InRange s2.data.regs.X4.toBitVec nodesBytes q at hq
      rw [x4, nodesBytes_eq] at hq
      exact .inr (.inr (.inr (NativeRustcVm.InRange.of_sub hq G.wOk.2 (by rw [hW]; omega))))
    · change InRange (s2.data.regs.X0.toBitVec + BitVec.ofNat 64 16) 8 q at hq
      rw [x0] at hq; exact .inr (.inl hq)
    · exact .inl hq
  refine Fr.leafAt (N' := climbLevelStack) hfr2 hst.2.1 hNs (by simp) (by decide)
    (fun q hq ↦ G.rgeo.not_frame (by omega) hq) hcl hpc2 hpre hQ fun m3 hfr3 hq3 hcs ↦ ?_
  have hsc3 : SameOutside s2.data.dmem m3.dmem fun q ↦ InRange (stackBelow s2.data climbLevelStack)
      climbLevelStack q ∨ InRange (base m0 192 + BitVec.ofNat 64 0) 0 q ∨ outs (rdr m0) (W m0) q :=
    NativeRustcVm.SameOutside.mono (hQ m3 hq3).1 fun q hq ↦ hq.elim .inl (.inr ∘ .inr)
  obtain ⟨hpost, hsK, -⟩ := hq3
  have hsC : SameOutside st.data.dmem m3.dmem
      (Chg m0 [(24832 + 10240 * l, 10240), (4096 + 10240 * ((l + 1) % 2), 10240)]) := by
    rw [← hd12]
    refine NativeRustcVm.SameOutside.mono hsK fun q ⟨R, hR, hq⟩ ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl
    · change InRange s2.data.regs.X3.toBitVec nodesBytes q at hq
      rw [x3, nodesBytes_eq] at hq
      exact .inr (.inr (.inr ⟨_, List.mem_cons_self, hq⟩))
    · change InRange s2.data.regs.X4.toBitVec nodesBytes q at hq
      rw [x4, nodesBytes_eq] at hq
      exact .inr (.inr (.inr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩))
    · change InRange (s2.data.regs.X0.toBitVec + BitVec.ofNat 64 16) 8 q at hq
      rw [x0] at hq; exact .inr (.inl hq)
    · exact .inl (stack_sub hst hfr2 hNs hq)
  have hpost' := hpost bp B cl (by rw [x0, hd12]; exact hrd) ns (by rw [x2])
    (by rw [x1, hd12]; exact hnd)
  rw [x0, x3, x4] at hpost'
  have hb3 : Base m0 m3 := hb2.call hfr3 hcs
  have rr3 : ∀ r ∈ [XReg.X21, .X24, .X25, .X26, .X27, .X28], m3.regs.getXReg r =
      st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hcr : calleeSaved r = true := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    have hr2 : r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29] := by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    rw [hcs r hcr, r2 r hr2, r1]
  have hh1 : height - l = (height - (l + 1)) + 1 := by omega
  -- `b33`
  refine blk hp b33_in_code (by simp [b33]) run_b33 rfl rfl hst hfr3 rfl
    fun s4 hfr4 hd4 hm4 hpc4 ↦ ?_
  have hm3 := frEnv_match hst hfr3
  have r4 : ∀ r, s4.data.regs.getXReg r = m3.regs.getXReg r := fun r ↦
    Match.reg_eq (v := .reg r) hm3 hm4 (by cases r <;> rfl) (by cases r <;> rfl)
  have hb4 : Base m0 s4.data := hb3.of_regs hfr4 fun r _ ↦ r4 r
  rcases hsib : sibsM B ns ns cl with _ | ⟨sl, c'⟩
  · rw [hsib] at hpost'
    have hc : (SBool.cmp .eq .W64 (.reg .X0) (.lit 1)).not.eval (frEnv m0 m3) = true := by
      rw [SBool.eval, cmp_eq_lit (v := 0) (by decide)
        (by simp only [Env.ofMachine_regs]; rw [x0_bv hpost']; rfl)]; rfl
    simp only [PcOk, hc, ↓reduceIte] at hpc4
    refine .done _ (.inl ⟨hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b18Offset) NativeRustcVmArm.Vm.PhaseM.label_12_at), hb4, ?_⟩)
    rw [hM.model]
    apply climbFin_none
    rw [hmod, hh1, climb_none hsib]; rfl
  rw [hsib] at hpost'
  obtain ⟨h0, hx1', hsibN, hnxt, hrd3⟩ := hpost'
  have hc : (SBool.cmp .eq .W64 (.reg .X0) (.lit 1)).not.eval (frEnv m0 m3) = false := by
    rw [SBool.eval, cmp_eq_lit (v := 1) (by decide)
      (by simp only [Env.ofMachine_regs]; rw [x0_bv h0]; rfl)]; rfl
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc4
  have hd4 : s4.data.dmem = m3.dmem := hd4
  have hsl := sibsM_len B ns ns cl hsib
  have hpl : (parentsOf ns sl).length ≤ ns.length := climb_parentsOf_length ns sl
  -- `b34`
  have hoc : 24576 + 8 * l + 8 ≤ workBytes := by rw [hW]; omega
  have hwf5 := G.al_wf (o := 24576 + 8 * l) (n := 8) hoc (by omega) hb4.fr
  have x23' : (s4.data.regs.getXReg .X23).toBitVec = wa m0 (24576 + 8 * l) := by
    rw [r4, hcs .X23 rfl, r2 .X23 (by simp), r1]; exact x23
  have hmB := G.al_match (o := 24576 + 8 * l) (n := 8) (a := .reg .X23) (k := 0) hb4.fr (by
    simp only [Sym.eval, Env.ofMachine_regs]; rw [x23']; simp)
  refine exec_at (infix_of b34_in_code (by simp [b34]) hp) run_b34 hwf5 hpc4 hmB
    fun s5 hm5 hpc5 ↦ ?_
  have hfr5 : Frm m0 s5.data := Fr.ofBlockW hb4.fr hmB hm5 hwf5 rfl rfl
    (fun x hx ↦ absurd hx (by simp)) rfl (by omega) hst.2.1 (by decide) fun w hw ↦ by
      simp only [List.mem_singleton] at hw
      subst hw
      right
      refine ⟨by decide, fun b sz hb ↦ ?_⟩
      simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨by decide, fun j hj ↦ .inr (.inr ?_)⟩
      rw [NativeRustcVm.addr_add_add]
      have := G.wNw
      exact NativeRustcVm.inRange_add (by rw [hW] at hoc; omega) (by omega)
  have hs5 := Match.sameOutside_in hm5 hwf5 (r0 := 1) (o := 0) (n := 8) rfl (by omega) (by decide)
  rw [NativeRustcVm.addr_add_zero] at hs5
  have hs5c : SameOutside m3.dmem s5.data.dmem (Chg m0 [(24576 + 8 * l, 8)]) := by
    rw [← hd4]
    exact NativeRustcVm.SameOutside.mono hs5 fun q hq ↦
      .inr (.inr (.inr ⟨_, List.mem_cons_self, hq⟩))
  have r5 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X24, .X26, .X27], s5.data.regs.getXReg r =
      s4.data.regs.getXReg r := regs_of hmB hm5 (by decide)
  have hb5 : Base m0 s5.data := hb4.of_regs hfr5 fun r hr ↦ r5 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)
  -- what memory keeps
  have hsC' : SameOutside st.data.dmem m3.dmem _ := hsC
  have fw3 : ∀ {f : Nat} {v : UInt64}, f + 8 ≤ 192 → FW m0 st.data.dmem f v →
      FW m0 m3.dmem f v := fun hf h ↦
    FW.call G hfr2 (lo := 0) (n := 0) hNs hsc3 hf (.inr (by omega)) (by omega)
      (show FW m0 s2.data.dmem _ _ by rw [hd12]; exact h)
  have fw5 : ∀ {f : Nat} {v : UInt64}, f + 8 ≤ 192 → FW m0 m3.dmem f v →
      FW m0 s5.data.dmem f v := fun hf h ↦
    FW.wa G hoc hs5 hf (show FW m0 s4.data.dmem _ _ by rw [hd4]; exact h)
  have fwc : ∀ {f : Nat} {v : UInt64}, f + 8 ≤ 192 → FW m0 st.data.dmem f v →
      FW m0 s5.data.dmem f v := fun hf h ↦ fw5 hf (fw3 hf h)
  have hM5 : Mid m0 B c count qs height lw rows c6 s5.data.dmem :=
    (hM.keep G hsC (by simp; omega) (fw3 (by omega) hM.f56) (fw3 (by omega) hM.f48)
      (fw3 (by omega) hM.f40) (fw3 (by omega) hM.f32)).keep G hs5c (by simp; omega)
      (fwc (by omega) hM.f56) (fwc (by omega) hM.f48) (fwc (by omega) hM.f40)
      (fwc (by omega) hM.f32)
  have hrd5 : ReaderAt s5.data.dmem (rdr m0) bp B c' :=
    G.rgeo.reader_frame rfl (show ReaderAt s4.data.dmem _ _ _ _ by rw [hd4]; exact hrd3)
      (NativeRustcVm.SameOutside.mono hs5 fun q hq ↦
      .inr (.inr (NativeRustcVm.InRange.of_sub hq G.wOk.2 hoc)))
  have hacc' : SibsAt s5.data.dmem (sibA m0) (cntA m0)
      (acc ++ [sl.map fun s ↦ (s.1, s.2.1)]) := by
    have hkeep := sibs_keep (sibs_keep hsb hsC (fun i hi ↦ by
        rw [hal, nodesBytes_eq] at hi
        exact G.not_chg (o := 24832) (n := 10240 * l) (by rw [hW]; omega)
          (fun p hp ↦ by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl <;> refine ⟨by rw [hW]; omega, ?_⟩ <;> omega) i hi)
      (fun i hi ↦ by
        rw [hal] at hi
        exact G.not_chg (o := 24576) (n := 8 * l) (by rw [hW]; omega)
          (fun p hp ↦ by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl <;> refine ⟨by rw [hW]; omega, ?_⟩ <;> omega) i hi))
      hs5c (fun i hi ↦ by
        rw [hal, nodesBytes_eq] at hi
        exact G.not_chg (o := 24832) (n := 10240 * l) (by rw [hW]; omega)
          (fun p hp ↦ by
            simp only [List.mem_singleton] at hp; subst hp
            exact ⟨by rw [hW]; omega, .inl (by omega)⟩) i hi)
      (fun i hi ↦ by
        rw [hal] at hi
        exact G.not_chg (o := 24576) (n := 8 * l) (by rw [hW]; omega)
          (fun p hp ↦ by
            simp only [List.mem_singleton] at hp; subst hp
            exact ⟨by rw [hW]; omega, .inr (by omega)⟩) i hi)
    refine sibs_snoc hkeep (by rw [List.length_map, hsl]; exact hnsl) ?_ ?_
    · have := hm5.bytesAt_write (r := 1) (o := 0) (n := 8) (b := wa m0 (24576 + 8 * l)) (sz := 8)
        rfl (by omega) (v := .reg .X28) (by decide)
      have hw := wordAt_reg this
      simp only [Sym.eval, Env.ofMachine_regs, NativeRustcVm.addr_add_zero] at hw
      rw [r4, rr3 .X28 (by simp), ofBitVec_eq x28, ← hsl,
        ← List.length_map (f := fun s ↦ (s.1, s.2.1))] at hw
      rw [hal, cntA, wa, NativeRustcVm.addr_add_add]; exact hw
    · rw [hal, sibA, wa, NativeRustcVm.addr_add_add, nodesBytes_eq]
      exact nodes_keep hsibN hs5c fun i hi ↦ by
        rw [List.length_map, hsl] at hi
        exact G.not_chg (o := 24832 + 10240 * l) (n := 40 * ns.length) (by rw [hW]; omega)
          (fun p hp ↦ by
            simp only [List.mem_singleton] at hp; subst hp
            exact ⟨by rw [hW]; omega, .inl (by omega)⟩) i hi
  have hnd5 : NodesAt s5.data.dmem (wa m0 (4096 + 10240 * ((l + 1) % 2))) (parentsOf ns sl) :=
    nodes_keep hnxt hs5c fun i hi ↦
      G.not_chg (o := 4096 + 10240 * ((l + 1) % 2)) (n := 40 * (parentsOf ns sl).length)
        (by rw [hW]; omega) (fun p hp ↦ by
          simp only [List.mem_singleton] at hp; subst hp
          exact ⟨by rw [hW]; omega, .inr (by omega)⟩) i hi
  have hf24 : FW m0 s5.data.dmem 24 (UInt64.ofBitVec (sibA m0)) := fwc (by omega) f24
  have hmod5 : climbM B height (nodes0 qs lw rows) c6 =
      (climbM B (height - (l + 1)) (parentsOf ns sl) c').map
        fun q ↦ ((acc ++ [sl.map fun s ↦ (s.1, s.2.1)]) ++ q.1, q.2) := by
    rw [hmod, hh1, climb_acc hsib]
  -- the exit
  have e24 : (s4.data.regs.getXReg .X24).toNat = height := by
    rw [r4, rr3 .X24 (by simp)]; exact x24
  have e25 : (s4.data.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 l := by
    rw [r4, rr3 .X25 (by simp)]; exact ofNat_toNat_bv x25
  have hcond : (SBool.cmp .eq .W64 (.reg .X24) (.bin .add .W64 (.reg .X25) (.lit 1))).not.eval
      (alEnv m0 s4.data (wa m0 (24576 + 8 * l)) 8) = !decide (height = l + 1) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [eq_apply, e25, add_lit, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), show (s4.data.regs.getXReg .X24).toBitVec.toNat = _ from e24]
  simp only [PcOk, hcond] at hpc5
  have ex21 : (s5.data.regs.getXReg .X21).toNat = count := by
    rw [r5 .X21 (by simp), r4, rr3 .X21 (by simp)]; exact x21
  have ex24 : (s5.data.regs.getXReg .X24).toNat = height := by
    rw [r5 .X24 (by simp)]; exact e24
  have ex26 : (s5.data.regs.getXReg .X26).toNat = (sortD qs).length := by
    rw [r5 .X26 (by simp), r4, rr3 .X26 (by simp)]; exact x26
  by_cases hlast : height = l + 1
  · simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc5
    -- `b35`
    refine blk hp b35_in_code (by simp [b35]) run_b35 rfl rfl hst hfr5 hpc5
      fun s6 hfr6 hd6 hm6 hpc6 ↦
        .done _ (.inr (.inr ⟨acc ++ [sl.map fun s ↦ (s.1, s.2.1)], c', ?_⟩))
    have hm5' := frEnv_match hst hfr5
    have r6 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X24, .X26], s6.data.regs.getXReg r =
        s5.data.regs.getXReg r := regs_of hm5' hm6 (by decide)
    simp only [PcOk] at hpc6
    refine ⟨hpc6, hb5.of_regs hfr6 fun r hr ↦ r6 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl <;> simp), by rw [hd6]; exact hM5, ?_, by simp [hal]; omega,
      by rw [hd6]; exact hacc', by rw [hd6]; exact hrd5, by rw [r6 .X21 (by simp)]; exact ex21,
      by rw [r6 .X24 (by simp)]; exact ex24, by rw [r6 .X26 (by simp)]; exact ex26, ?_, ?_, ?_⟩
    · rw [hmod5, show height - (l + 1) = 0 by omega, climbM_zero]; simp
    · show (s6.data.regs.getXReg .X5).toBitVec.toNat = _
      rw [hm6.regs .X5 _ rfl]; show ((frEnv m0 s5.data).load 0 56 8).toNat = _
      rw [load_fw hM5.f56, UInt64.toNat_toBitVec, toNat_toUInt64_of_lt (by have := hM5.lw64; omega)]
    · rw [hm6.regs .X8 _ rfl]; simp only [Sym.eval, Env.ofMachine_regs]; rw [hb5.x19, add_lit]
    · rw [hm6.regs .X29 _ rfl]; show (frEnv m0 s5.data).load 0 24 8 = _
      rw [load_fw hf24]
  · simp only [hlast, decide_false, Bool.not_false, ↓reduceIte] at hpc5
    refine .done _ (.inr (.inl ⟨_, _, c', hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b31Offset) NativeRustcVmArm.Vm.PhaseM.label_23_at), hb5, hM5,
      by simp [hal], hmod5, by omega, by omega, hacc', hnd5, hrd5, hf24, ex21, ex24, ex26, ?_, ?_,
      ?_, ?_, ?_⟩))
    · show (s5.data.regs.getXReg .X25).toBitVec.toNat = _
      rw [hm5.regs .X25 _ rfl]; simp only [Sym.eval, Env.ofMachine_regs]
      rw [e25, add_lit, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]; omega
    · rw [hm5.regs .X23 _ rfl]; simp only [Sym.eval, Env.ofMachine_regs]
      rw [x23', wa_add, show 24576 + 8 * l + 8 = 24576 + 8 * (l + 1) by omega]
    · rw [r5 .X27 (by simp), r4, rr3 .X27 (by simp)]; exact x27
    · show (s5.data.regs.getXReg .X28).toBitVec.toNat = _
      rw [hm5.regs .X28 _ rfl]; show (s4.data.regs.getXReg .X1).toBitVec.toNat = _
      rw [r4]; exact hx1'
    · rw [hm5.regs .X29 _ rfl]; simp only [Sym.eval, Env.ofMachine_regs]
      rw [r4, hcs .X29 rfl, r2 .X29 (by simp), r1, x29, wa_add,
        show 24832 + 10240 * l + 10240 = 24832 + 10240 * (l + 1) by omega]



end

end NativeRustcVmArm.Wire.PhaseM
