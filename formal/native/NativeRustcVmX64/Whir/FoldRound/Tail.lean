module

public import NativeRustcVmX64.Whir.FoldRound.Fin

/-!
# `fold_round` on x86-64: from `b18` to the return

`tail`: `b18` writes the folded claim and loads the `α`s' count (below `30`: no jump); `b19`
pushes `α`, bumps the count and writes `α`, `β` to the output; `b21` writes the tag `1` and
returns. The state is `foldW`'s (`WhirStateAt.fold`), the `TState` the round's.
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRound
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept wrote_spec kept_spec wr0_spec
  miss_spec midOk_writesIn miss_of_wr0)
open NativeRustcVm (WordAt EWAt EWsAt)

public section

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}
  {x1 x2 x3 x4 : EW} {s5 : TState}

/-- Continue from a state at `pc`. -/
theorem at_pc {R : MachineState → Prop} {pc : Int64} {d : MachineData}
    (h : Eventually (step1 Host.exe) R ⟨d, pc⟩) {s : MachineState} (hd : s.data = d)
    (hpc : s.pc = pc) : Eventually (step1 Host.exe) R s := by
  obtain ⟨d', pc'⟩ := s
  simp only at hd hpc
  subst hd hpc
  exact h

/-- **From `b18` to the return.** -/
theorem tail (hp : Placed code k) (h : FoldRoundPre a s0 w m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b18Offset))
    (hP : Pt a s0 w m0 x1 x2 x3 x4 s5 (sq (sq s5).2).2
      [(88, (p3 s5 x2).c0), (64, (p3 s5 x2).c1), (96, (p1 w s5 x1).c0),
        (104, (p1 w s5 x1).c1), (48, (beA s5).c0), (40, (beA s5).c1), (56, (alA s5).c0),
        (32, (alA s5).c1)] st.data)
    (h15 : reg st.data .r15 = (p4 s5 x3).c0.toBitVec)
    (h13 : reg st.data .r13 = (p4 s5 x3).c1.toBitVec)
    (hax : reg st.data .rax = (p6 s5 x3 x4).c0.toBitVec)
    (hdx : reg st.data .rdx = (p6 s5 x3 x4).c1.toBitVec) :
    Eventually (step1 Host.exe) (Goal a s0 w m0) st := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := geo h
  have hSB : stateBytes = 61152 := rfl
  have hc : w.alphas.size < 30 := h.2.2.2.1
  have hws := ws_of_mem h hP.bd.mem
  have hcnt : WordAt st.data.dmem (off (pA m0) 16) w.alphas.size.toUInt64 := by
    have := hws.alphas.2.1
    rwa [Array.length_toList] at this
  /- `b18`: the claim, the count. -/
  have hwf := st_wf (vars := fun _ ↦ 0) (ret := 0) h hP.bd.fr.fr.kept
  have hm0 := st_match (vars := fun _ ↦ 0) (ret := 0) hP.bd.fr hP.bd.r14
  refine exec_at (inf hp b18_in_code (by simp [b18])) run_b18 hwf (by intro l h; cases h) hpc hm0
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hwr, hc0, hc1, hrax, hk⟩ := after_eq run_b18 ▸ ok_b18
  have hl16 : (stEnv m0 st.data (fun _ ↦ 0) 0).load 1 16 8 = BitVec.ofNat 64 w.alphas.size :=
    Transcript.load_ofMachine (o := 16) rfl hcnt
  simp only [PcOk] at hpc1
  rw [cnt_test _ hc hl16] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  have hs1 : SameOutside st.data.dmem st1.data.dmem (InRange (pA m0) 16) :=
    Transcript.sameOutside_low hwf hm1 (r := 1) rfl (by omega) (wrR_spec hwr)
  have hw1 : Fr m0 st1.data := fr_of_low hP.bd.fr hwf hm1 hmid hs1
    fun q hq ↦ .inr (.inl (Transcript.inRange_mono hq (by omega)))
  have er : ∀ r, (Sym.reg r).eval (stEnv m0 st.data (fun _ ↦ 0) 0) = reg st.data r := fun _ ↦ rfl
  have el : ∀ {o : Nat} {v : UInt64}, (o, v) ∈ [(88, (p3 s5 x2).c0), (64, (p3 s5 x2).c1),
      (96, (p1 w s5 x1).c0), (104, (p1 w s5 x1).c1)] →
      (Sym.load 0 o 8).eval (stEnv m0 st.data (fun _ ↦ 0) 0) = v.toBitVec :=
    fun hp' ↦ loc_load ((hP.fw.sub (L' := [(88, (p3 s5 x2).c0), (64, (p3 s5 x2).c1),
      (96, (p1 w s5 x1).c0), (104, (p1 w s5 x1).c1)]) (by simp)).get hp')
  have ec0 : WordAt st1.data.dmem (off (pA m0) 0)
      (foldW w x1 x2 x3 x4 (alA s5) (beA s5)).claim.c0 := by
    have := Transcript.wordAt_write hm1 (r := 1) (o := 0) rfl (by omega) (wrote_spec hc0)
    rw [claim0S, NativeRustcVmX64.Arrays.eval_xor, NativeRustcVmX64.Arrays.eval_xor,
      NativeRustcVmX64.Arrays.eval_xor, NativeRustcVmX64.Arrays.eval_xor, er, er, er, hax, hP.r12,
      h15, el (o := 88) (v := (p3 s5 x2).c0) (by simp),
      el (o := 96) (v := (p1 w s5 x1).c0) (by simp)] at this
    rw [foldW_claim]
    show WordAt _ _ (x1.c0 ^^^ (p1 w s5 x1).c0 ^^^ (p3 s5 x2).c0 ^^^ (p4 s5 x3).c0 ^^^
      (p6 s5 x3 x4).c0)
    rw [← xor5]
    exact this
  have ec1 : WordAt st1.data.dmem (off (pA m0) 8)
      (foldW w x1 x2 x3 x4 (alA s5) (beA s5)).claim.c1 := by
    have := Transcript.wordAt_write hm1 (r := 1) (o := 8) rfl (by omega) (wrote_spec hc1)
    rw [claim1S, NativeRustcVmX64.Arrays.eval_xor, NativeRustcVmX64.Arrays.eval_xor,
      NativeRustcVmX64.Arrays.eval_xor, NativeRustcVmX64.Arrays.eval_xor, er, er, er, hdx, hP.rbp,
      h13, el (o := 64) (v := (p3 s5 x2).c1) (by simp),
      el (o := 104) (v := (p1 w s5 x1).c1) (by simp)] at this
    rw [foldW_claim]
    show WordAt _ _ (x1.c1 ^^^ (p1 w s5 x1).c1 ^^^ (p3 s5 x2).c1 ^^^ (p4 s5 x3).c1 ^^^
      (p6 s5 x3 x4).c1)
    rw [← xor5]
    exact this
  have hfw1 : FW st1.data.dmem m0 [(48, (beA s5).c0), (40, (beA s5).c1), (56, (alA s5).c0),
      (32, (alA s5).c1)] :=
    FW.call (fun ho hv ↦ wkeep hs1 (fun i hi hq ↦ (fb_not h (x := _ + i) (by omega)).1
      (Transcript.inRange_mono hq (by omega))) hv) (by simp) (hP.fw.sub (by simp))
  /- `b19`: the push, the output. -/
  have hrax1 : reg st1.data .rax = BitVec.ofNat 64 w.alphas.size := (hm1.regs .rax _ hrax).trans hl16
  have hbx1 : reg st1.data .rbx = oA m0 :=
    (hm1.regs .rbx _ ((keptI_spec hk (by simp)).trans rfl)).trans hP.bd.rbx
  have h141 : reg st1.data .r14 = pA m0 :=
    (hm1.regs .r14 _ ((keptI_spec hk (by simp)).trans rfl)).trans (Transcript.eval_ptr rfl)
  have hwf2 := push_wf h hw1.fr.kept hc
  refine exec_at (inf hp b19_in_code (by simp [b19])) run_b19 hwf2 (by intro l h; cases h)
    (hpc1.trans rfl) (push_match hw1 hbx1 h141 hrax1) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨-, hwa0, hwa1, hwn, hwo8, hwo16, hwo24, hwo32, hwr2, hrax2, hk2⟩ :=
    after_eq run_b19 ▸ ok_b19
  have hmid2 : MidOk 176 8 slots (after b19 pushS) = true := (after_eq run_b19 ▸ ok_b19).1
  simp only [PcOk] at hpc2
  rw [hp.label NativeRustcVmX64.Vm.FoldRound.label_8_at] at hpc2
  have hsl : (off (pA m0) (24 + 16 * w.alphas.size)).toNat = (pA m0).toNat + (24 + 16 * w.alphas.size) :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have hs2 : SameOutside st1.data.dmem st2.data.dmem (fun q ↦ InRange (off (pA m0) 16) 8 q ∨
      InRange (off (pA m0) (24 + 16 * w.alphas.size)) 16 q ∨ InRange (off (oA m0) 8) 32 q) := by
    intro q hq
    refine hm2.get?_mem0 hwf2 fun hW ↦ hq ?_
    obtain ⟨w', hw', b, sz, hb, j, h1, h2, rfl⟩ := Transcript.written_off hwf2 hW
    rcases hwr2 w' hw' with ⟨hr, ho1, ho2⟩ | ⟨hr, ho⟩ | ⟨hr, ho1, ho2⟩ <;> rw [hr] at hb <;>
      cases hb
    · exact .inl ((in_off (N := 24) (by omega) (by omega) (by omega)).mpr ⟨by omega, by omega⟩)
    · exact .inr (.inl (inRange_off_self (by omega) (by omega)))
    · exact .inr (.inr ((in_off (N := 40) g2 (by omega) (by omega)).mpr ⟨by omega, by omega⟩))
  have hR2 : ∀ q, (InRange (off (pA m0) 16) 8 q ∨
      InRange (off (pA m0) (24 + 16 * w.alphas.size)) 16 q ∨ InRange (off (oA m0) 8) 32 q) →
      InRange (pA m0) stateBytes q ∨ InRange (oA m0) 40 q := by
    rintro q (hq | hq | hq)
    · exact .inl (Transcript.inRange_of_off (N := stateBytes) g1 (by omega) hq)
    · exact .inl (Transcript.inRange_of_off (N := stateBytes) g1 (by omega) hq)
    · exact .inr (Transcript.inRange_of_off (N := 40) g2 (by omega) hq)
  have hw2 : Fr m0 st2.data := fr_of_low hw1 hwf2 hm2 hmid2 hs2 fun q hq ↦
    (hR2 q hq).elim (fun h ↦ .inr (.inl h)) .inl
  have hbx2 : reg st2.data .rbx = oA m0 :=
    (hm2.regs .rbx _ ((keptI_spec hk2 (by simp [cs])).trans rfl)).trans (Transcript.eval_ptr rfl)
  have ld : ∀ {o : Nat} {v : UInt64}, (o, v) ∈ [(48, (beA s5).c0), (40, (beA s5).c1),
      (56, (alA s5).c0), (32, (alA s5).c1)] →
      (Sym.load 0 o 8).eval (pushEnv m0 st1.data w.alphas.size) = v.toBitVec :=
    fun hp' ↦ loc_load (hfw1.get hp')
  have wr2 : ∀ {r o : Nat} {b : BitVec 64} {sz : Nat} {v : Sym} {u : UInt64},
      ([(fb m0, 176 + 8), (pA m0, 24), (off (pA m0) (24 + 16 * w.alphas.size), 16),
        (oA m0, 40)] : List (BitVec 64 × Nat))[r]? = some (b, sz) → o + 8 ≤ sz →
      wrote (after b19 pushS) r o v = true →
      v.eval (pushEnv m0 st1.data w.alphas.size) = u.toBitVec → WordAt st2.data.dmem (off b o) u :=
    fun hb hle hw hv ↦ by
      have := Transcript.wordAt_write hm2 hb hle (wrote_spec hw)
      rwa [hv, UInt64.ofBitVec_toBitVec] at this
  have wa0 := wr2 (r := 2) (o := 0) rfl (by omega) hwa0 (ld (o := 56) (v := (alA s5).c0) (by simp))
  have wa1 := wr2 (r := 2) (o := 8) rfl (by omega) hwa1 (ld (o := 32) (v := (alA s5).c1) (by simp))
  have wo8 := wr2 (r := 3) (o := 8) rfl (by omega) hwo8 (ld (o := 56) (v := (alA s5).c0) (by simp))
  have wo16 := wr2 (r := 3) (o := 16) rfl (by omega) hwo16
    (ld (o := 32) (v := (alA s5).c1) (by simp))
  have wo24 := wr2 (r := 3) (o := 24) rfl (by omega) hwo24
    (ld (o := 48) (v := (beA s5).c0) (by simp))
  have wo32 := wr2 (r := 3) (o := 32) rfl (by omega) hwo32
    (ld (o := 40) (v := (beA s5).c1) (by simp))
  have wn := wr2 (r := 1) (o := 16) (u := (w.alphas.size + 1).toUInt64) rfl (by omega) hwn (by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [show (pushEnv m0 st1.data w.alphas.size).regs .rax = BitVec.ofNat 64 w.alphas.size
      from hrax1, ← BitVec.ofNat_add]
    rfl)
  /- `b21`: the tag, the return. -/
  refine at_pc (exit21 hp h hw2 hbx2 (v := 1) ((hm2.regs .rax _ hrax2).trans rfl)
    (Q := fun d' ↦ EWsAt d' (off (oA m0) 8) [alA s5, beA s5] ∧
      WhirStateAt d' (pA m0) (foldW w x1 x2 x3 x4 (alA s5) (beA s5)) ∧
      TStateAt d' (tA m0) a (sq (sq s5).2).2) (fun d' hk3 hs3 ↦ ?_) ?_) rfl hpc2
  · have hno : ∀ {j : Nat}, j < stateBytes → ¬ InRange (oA m0) 8 (off (pA m0) j) :=
      fun hj hq ↦ p_not_o h hj (Transcript.inRange_mono hq (by omega))
    have hoo : ∀ {x : Nat}, 8 ≤ x → x < 40 → ¬ InRange (oA m0) 8 (off (oA m0) x) :=
      fun h1 h2 ↦ not_lo g2 h1 h2 (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [ewsAt_cons, ewsAt_cons, off_off, ewAt_iff, ewAt_iff, off_off, off_off]
      refine ⟨⟨wkeep hs3 (fun i hi ↦ hoo (by omega) (by omega)) wo8,
        wkeep hs3 (fun i hi ↦ hoo (by omega) (by omega)) wo16⟩,
        ⟨wkeep hs3 (fun i hi ↦ hoo (by omega) (by omega)) wo24,
        wkeep hs3 (fun i hi ↦ hoo (by omega) (by omega)) wo32⟩, ?_⟩
      exact fun i hi ↦ absurd hi (by simp)
    · have hA : Agree st.data.dmem d' (pA m0) stateBytes fun j ↦ j < 24 ∨
          (24 + 16 * w.alphas.size ≤ j ∧ j < 40 + 16 * w.alphas.size) := by
        intro j hj hW
        have hj24 : 24 ≤ j := by omega
        rw [hs3 _ (hno hj), hs2 _ ?_, hs1 _ fun hq ↦ not_lo (N := stateBytes) g1 (by omega) hj
          (by omega) hq]
        rintro (hq | hq | hq)
        · have := (in_off (N := stateBytes) g1 hj (by omega)).mp hq
          omega
        · have := (in_off (N := stateBytes) g1 hj (by omega)).mp hq
          omega
        · exact p_not_o h hj (Transcript.inRange_of_off (N := 40) g2 (by omega) hq)
      have hnot2 : ∀ {x : Nat}, x < 16 → ¬ (InRange (off (pA m0) 16) 8 (off (pA m0) x) ∨
          InRange (off (pA m0) (24 + 16 * w.alphas.size)) 16 (off (pA m0) x) ∨
          InRange (off (oA m0) 8) 32 (off (pA m0) x)) := by
        intro x hx hq
        rcases hq with hq | hq | hq
        · have := (in_off (N := stateBytes) g1 (by omega) (by omega)).mp hq
          omega
        · have := (in_off (N := stateBytes) g1 (by omega) (by omega)).mp hq
          omega
        · exact p_not_o h (by omega) (Transcript.inRange_of_off (N := 40) g2 (by omega) hq)
      have hcl : EWAt d' (pA m0) (foldW w x1 x2 x3 x4 (alA s5) (beA s5)).claim := by
        rw [ewAt_iff]
        refine ⟨?_, wkeep hs3 (fun i hi ↦ hno (by omega))
          (wkeep hs2 (fun i hi ↦ hnot2 (by omega)) ec1)⟩
        have := wkeep hs3 (fun i hi ↦ hno (by omega))
          (wkeep hs2 (fun i hi ↦ hnot2 (by omega)) ec0)
        rwa [off_zero] at this
      have hn : WordAt d' (off (pA m0) 16) (w.alphas.size + 1).toUInt64 :=
        wkeep hs3 (fun i hi ↦ hno (by omega)) wn
      have hx : EWAt d' (off (pA m0) (24 + 16 * w.alphas.size)) (alA s5) := by
        rw [ewAt_iff]
        have hR : ∀ o, o ≤ 8 → ∀ i < 8, ¬ InRange (oA m0) 8
            (off (off (pA m0) (24 + 16 * w.alphas.size)) (o + i)) := fun o ho i hi ↦ by
          rw [off_off]
          exact hno (j := 24 + 16 * w.alphas.size + (o + i)) (by omega)
        refine ⟨?_, wkeep hs3 (hR 8 le_rfl) wa1⟩
        have := wkeep hs3 (o := 0) (hR 0 (by omega)) wa0
        rwa [off_zero] at this
      exact NativeRustcVmX64.Whir.WhirStateAt.fold hws (by unfold stackCap; omega) hA hcl hn hx
    · have ht := hP.bd.ts.frame (hm1.kept hwf) (fun q hq ↦ po_not_t h
        (.inl (Transcript.inRange_mono hq (by omega)))) hs1
      have ht2 := ht.frame (hm2.kept hwf2) (fun q hq ↦ po_not_t h (hR2 q hq)) hs2
      exact ht2.frame hk3 (fun q hq ↦ po_not_t h (.inr (Transcript.inRange_mono hq (by omega)))) hs3
  · intro d' hw' hQ'
    unfold Res
    rw [hP.model]
    exact ⟨hw', hQ'⟩

end

end NativeRustcVmX64.Whir.FoldRound
