module

public import NativeRustcVmX64.Wire.WriteOpenings.A.Defs

/-!
# `write_openings`' leaf copy (`h > 0`, x86-64)

From the query's position (`FoundA`, `b7`): the frame words saved, then no leaf word (`LeafA`),
fewer than four (`PreRemA`, `b8`) or four at a time (`ChunkA`, `b9`). Four words copied
(`chunk_step`, `b10`, then `b11`); the remaining words one at a time (`rem_start`, `b12`;
`rem_step`, `b13`).
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 hiding InRange SameOutside
open NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.WriteOpenings
open NativeRustcVm (WordAt WordsAt wordOf InRange SameOutside)

public section

variable {R : Run} {j i : Nat} [Host]

/-- **The query found** (`b7`, `b8`, `b9`): the frame words saved, then the leaf's copy. -/
theorem found_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : FoundA R j i st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ LeafA R j i st' ∨ ChunkA R j i 0 st' ∨ PreRemA R j i st') st := by
  have hlw := G.lw64
  have hq4d : q4 R.lw = R.lw / 4 * 4 := rfl
  have hwf := G.wf0 H.F.fr.kept (ret := 0)
  refine blk hp b7_in_code (by simp [b7]) run_b7 H.F H.pc hwf (frMatch H.F.fr) nofun (o := 8)
    (by decide +kernel) (by decide +kernel) fun s1 F1 hm1 hpc1 hs1 ↦ ?_
  have hk1 := fwK_of hwf hm1 (o' := 8) (by decide +kernel) (os := ((wA R j).map Prod.fst) ++ [104])
    (by kdecA) (by kdecA)
  have hW : ∀ p, InRange R.out phaseBytes p → ¬InRange R.fb 160 p := G.frame_out
  have hfw : FWs R s1.data.dmem (wB R j) := by
    refine FWs.append (H.w.keep (hk1.sub (by simp))) ?_
    refine FWs.cons (hk1 104 (by simp) _ H.w104) (FWs.cons ?_ (FWs.cons ?_ (FWs.cons ?_
      (FWs.nil _))))
    · exact fw_write hm1 (o := 56) (by omega) (v := .reg .r14) (by decide +kernel) |>.congr
        (by rw [show (Sym.reg .r14).eval _ = reg st.data .r14 from rfl,
          H.rg.get (v := R.qe) (by simp)])
    · exact fw_write hm1 (o := 64) (by omega) (v := .reg .rdi) (by decide +kernel) |>.congr
        (by rw [show (Sym.reg .rdi).eval _ = reg st.data .rdi from rfl,
          H.rg.get (v := R.qa + BitVec.ofNat 64 (8 * (j + 1))) (by simp)])
    · exact fw_write hm1 (o := 80) (by omega) (v := .reg .rcx) (by decide +kernel) |>.congr
        (by rw [show (Sym.reg .rcx).eval _ = reg st.data .rcx from rfl,
          H.rg.get (v := BitVec.ofNat 64 (8 * R.np)) (by simp)])
  have K1 : KA R j i s1.data :=
    ⟨F1, H.lt, H.h0, H.ilt, H.pos, G.begun_keepW hs1 hW H.lt H.mem, hfw, by
      keep_regs hm1 H.rg⟩
  have hax1 : reg s1.data .rax = R.lv + BitVec.ofNat 64 (512 * i) := kreg hm1 rfl H.rax
  have hr91 : reg s1.data .r9 = R.lv + BitVec.ofNat 64 (512 * i + 24) := kreg hm1 rfl H.r9
  have hr10 : reg s1.data .r10 = BitVec.ofNat 64 R.lw :=
    kreg hm1 rfl (H.rg.get (v := BitVec.ofNat 64 R.lw) (by simp))
  have hpc1' := pc_cond hpc1 (b := decide (R.lw = 0)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, and_self_eval, envRegs]
    rw [H.rg.get (v := BitVec.ofNat 64 R.lw) (by simp), beq_ofNat (by omega) (by decide +kernel),
      beq_decide])
  by_cases h0 : R.lw = 0
  · rw [decide_eq_true h0, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_12_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    refine .done _ (.inl ⟨hpc1', K1, ?_⟩)
    rw [h0]
    exact leaf_zero
  rw [decide_eq_false h0] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  -- `b8`.
  have hwf2 := G.wf0 F1.fr.kept (ret := 0)
  refine blk hp b8_in_code (by simp [b8]) run_b8 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 (frMatch F1.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf2 rfl
  have K2 : KA R j i s2.data := K1.next F2 hd2 (K1.rg.keep hm2 (by kdec))
  have hrcx2 : reg s2.data .rcx = BitVec.ofNat 64 0 := hm2.regs .rcx _ rfl
  have hax2 : reg s2.data .rax = R.lv + BitVec.ofNat 64 (512 * i) := kreg hm2 rfl hax1
  have hr92 : reg s2.data .r9 = R.lv + BitVec.ofNat 64 (512 * i + 24) := kreg hm2 rfl hr91
  have hpc2' := pc_cond hpc2 (b := decide (R.lw < 4)) (by
    simp only [SBool.eval, Sym.eval, ult_eval, envRegs]
    rw [hr10, toNat_ofNat (by omega), toNat_ofNat (by decide +kernel)])
  by_cases h4 : R.lw < 4
  · rw [decide_eq_true h4, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_10_at] at hpc2'
    simp only [↓reduceIte] at hpc2'
    have hq : q4 R.lw = 0 := by omega
    refine .done _ (.inr (.inr ⟨hpc2', K2, by rw [hq]; exact leaf_zero, by omega,
      by rw [hrcx2, hq], hax2⟩))
  rw [decide_eq_false h4] at hpc2'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc2'
  -- `b9`.
  have hwf3 := G.wf0 F2.fr.kept (ret := 0)
  refine blk hp b9_in_code (by simp [b9]) run_b9 F2 (hpc2'.trans (congrArg Host.addrOf rfl))
    hwf3 (frMatch F2.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s3 F3 hm3 hpc3 _ ↦ ?_
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq hwf3 rfl
  refine .done _ (.inr (.inl ⟨(pc_fall hpc3).trans (congrArg Host.addrOf rfl),
    K2.next F3 hd3 (K2.rg.keep hm3 (by kdec)), leaf_zero, rfl, by omega, kreg hm3 rfl hrcx2,
    ?_, kreg hm3 rfl hax2, by rw [kreg hm3 rfl hr92]⟩))
  refine (hm3.regs .rdi _ rfl).trans ?_
  exact fw_load (K2.w.get (by simp))

/-- **Four leaf words copied** (`b10`, then `b11`): four more, or the rest. -/
theorem chunk_step (hp : Placed code R.k) (G : Geo R) {t : Nat} {st : MachineState}
    (H : ChunkA R j i t st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ ChunkA R j i (t + 4) st' ∨ LeafA R j i st' ∨ PreRemA R j i st') st := by
  have K := H.k
  have hlw := G.lw64
  have hq4d : q4 R.lw = R.lw / 4 * 4 := rfl
  have hnq := G.nq256
  have hi := K.ilt
  have hj := K.lt
  have hob := ob_le (j := j) (by omega)
  have hob' : 24 + 1544 * j + 1544 ≤ phaseBytes := hob
  have htq := H.tq
  have ht4 := H.t4
  have hq4 : q4 R.lw ≤ R.lw := Nat.div_mul_le_self _ _
  have hin2 : Inside (R.lv + BitVec.ofNat 64 (512 * i + 8 * t)) 32 (R.big 4) :=
    G.l_in hi (by omega) (by omega)
  have hin3 : Inside (R.oa (ob j + 8 + 8 * t)) 32 (R.big 7) := G.o_in (by omega) (by omega)
  have hwf := G.wf2 K.F.fr.kept (i := 4) (j := 7) (by omega) (by omega) (by omega) (by omega)
    (by omega) hin2 hin3 (ret := 0)
  have hm : Match (envOf R st.data [(R.lv + BitVec.ofNat 64 (512 * i + 8 * t), 32),
      (R.oa (ob j + 8 + 8 * t), 32)] 0) (cS .r9 .r12 .rcx) st.data :=
    match_fS K.F.fr (csz := [32, 32]) (cs := [(R.lv + BitVec.ofNat 64 (512 * i + 8 * t), 32),
      (R.oa (ob j + 8 + 8 * t), 32)]) ⟨rfl, rfl, trivial⟩
      ⟨alN (o := 24) (by
        show reg st.data .r9 = R.lv + BitVec.ofNat 64 (512 * i + 8 * t) + BitVec.ofNat 64 24
        rw [H.r9]
        exact (addr_add rfl).symm), alN (o := 24) (by
        show (ix .r12 .rcx 8).eval _ = R.oa (ob j + 8 + 8 * t) + BitVec.ofNat 64 24
        rw [ix_eval, K.rg.get (v := R.oa (ob j + 32)) (by simp), H.rcx, ixs_ofNat, oa_add,
          oa_add]
        congr 1
        omega), trivial⟩
  refine blkW G hp b10_in_code (by simp [b10]) run_b10 K.F H.pc hwf hm nofun (o := 8)
    (by decide +kernel) (ro := 3) rfl (lo := 0) (a := R.oa (ob j + 8 + 8 * t)) (n := 32)
    (NativeRustcVm.addr_add_zero _) hin3 (by decide +kernel) fun s1 F1 hm1 hpc1 hs1 ↦ ?_
  have hw : ∀ u, u < 4 → WordAt s1.data.dmem (R.oa (ob j + 8 + 8 * (t + u))) (R.lfw i (t + u)) := by
    intro u hu
    have hl := G.lfw_load K.F.chg (m := st.data) (rest := [(R.oa (ob j + 8 + 8 * t), 32)])
      (ret := 0) (n := 32) hi (t := t) (u := u) (by omega)
    rcases (by omega : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3) with rfl | rfl | rfl | rfl
    · exact word_at (stored_load hm1 (r := 3) (o := 0) (sz := 32) rfl (by omega) (r' := 2)
        (o' := 0) (by decide +kernel) hl) (by omega)
    · exact word_at (stored_load hm1 (r := 3) (o := 8) (sz := 32) rfl (by omega) (r' := 2)
        (o' := 8) (by decide +kernel) hl) (by omega)
    · exact word_at (stored_load hm1 (r := 3) (o := 16) (sz := 32) rfl (by omega) (r' := 2)
        (o' := 16) (by decide +kernel) hl) (by omega)
    · exact word_at (stored_load hm1 (r := 3) (o := 24) (sz := 32) rfl (by omega) (r' := 2)
        (o' := 24) (by decide +kernel) hl) (by omega)
  have hleaf : R.LeafPart s1.data.dmem j i (t + 4) :=
    leaf_succ (leaf_succ (leaf_succ (leaf_succ (G.leaf_keep hs1 (by omega) hj H.leaf
      (by omega)) (hw 0 (by omega))) (hw 1 (by omega))) (hw 2 (by omega))) (hw 3 (by omega))
  have K1 : KA R j i s1.data := K.write G F1 hs1 (by omega) (by omega)
    (fwK_of hwf hm1 (o' := 8) (by decide +kernel) (os := (wB R j).map Prod.fst) (by kdecA) (by kdecA))
    (K.rg.keep hm1 (by kdec))
  have hrcx : reg s1.data .rcx = BitVec.ofNat 64 (t + 4) := by
    refine (hm1.regs .rcx _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [H.rcx, ofNat_add, Nat.add_comm]
  have hpc1' := pc_cond hpc1 (b := decide (q4 R.lw ≠ 4 + t)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, add_eval, envRegs]
    rw [H.rdi, H.rcx, ofNat_add, beq_ofNat (by omega) (by omega), not_beq_decide])
  by_cases hl : q4 R.lw ≠ 4 + t
  · rw [decide_eq_true hl, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_8_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    refine .done _ (.inl ⟨hpc1', K1, hleaf, by omega, by omega, hrcx, kreg hm1 rfl H.rdi,
      kreg hm1 rfl H.rax, ?_⟩)
    refine (hm1.regs .r9 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [H.r9]
    exact lit_add (by omega)
  rw [decide_eq_false hl] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  have hq : q4 R.lw = t + 4 := by omega
  -- `b11`.
  have hwf2 := G.wf0 F1.fr.kept (ret := 0)
  refine blk hp b11_in_code (by simp [b11]) run_b11 F1 (hpc1'.trans (congrArg Host.addrOf rfl))
    hwf2 (frMatch F1.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s2 F2 hm2 hpc2 _ ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf2 rfl
  have K2 : KA R j i s2.data := K1.next F2 hd2 (K1.rg.keep hm2 (by kdec))
  have hpc2' := pc_cond hpc2 (b := decide (R.lw % 4 = 0)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, and_self_eval, envRegs]
    rw [K1.rg.get (v := BitVec.ofNat 64 (R.lw % 4)) (by simp), beq_ofNat (by omega) (by decide +kernel),
      beq_decide])
  by_cases h0 : R.lw % 4 = 0
  · rw [decide_eq_true h0, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_12_at] at hpc2'
    simp only [↓reduceIte] at hpc2'
    refine .done _ (.inr (.inl ⟨hpc2', K2, ?_⟩))
    rw [hd2, show R.lw = t + 4 by omega]
    exact hleaf
  rw [decide_eq_false h0] at hpc2'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc2'
  refine .done _ (.inr (.inr ⟨hpc2'.trans (congrArg Host.addrOf rfl), K2, by
    rw [hd2, hq]; exact hleaf, by omega, by rw [kreg hm2 rfl hrcx, hq], kreg hm2 rfl
    (kreg hm1 rfl H.rax)⟩))

/-- **Before the remaining words** (`b12`). -/
theorem rem_start (hp : Placed code R.k) (G : Geo R) {st : MachineState}
    (H : PreRemA R j i st) : Eventually (step1 Host.exe) (RemA R j i 0) st := by
  have K := H.k
  have hwf := G.wf0 K.F.fr.kept (ret := 0)
  refine blk hp b12_in_code (by simp [b12]) run_b12 K.F H.pc hwf (frMatch K.F.fr) nofun (o := 8)
    (by decide +kernel) (by decide +kernel) fun s1 F1 hm1 hpc1 _ ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  refine .done _ ⟨(pc_fall hpc1).trans (congrArg Host.addrOf rfl),
    K.next F1 hd1 (K.rg.keep hm1 (by kdec)), by rw [hd1]; exact H.leaf, H.pos,
    hm1.regs .rdi _ rfl, ?_, ?_⟩
  · refine (hm1.regs .rax _ rfl).trans ?_
    show (ix .rax .rcx 8).eval _ = _
    rw [ix_eval, H.rax, H.rcx, ixs_ofNat]
    exact addr_add (by omega)
  · refine (hm1.regs .rcx _ rfl).trans ?_
    simp only [Sym.eval, add_eval, mul_eval, envRegs]
    rw [fw_load (K.w.get (v := R.oa (ob j + 8)) (by simp)), H.rcx, ofNat_mul, oa_add]
    congr 1
    omega

/-- **One remaining leaf word copied** (`b13`). -/
theorem rem_step (hp : Placed code R.k) (G : Geo R) {u : Nat} {st : MachineState}
    (H : RemA R j i u st) :
    Eventually (step1 Host.exe) (fun st' ↦ RemA R j i (u + 1) st' ∨ LeafA R j i st') st := by
  have K := H.k
  have hlw := G.lw64
  have hq4d : q4 R.lw = R.lw / 4 * 4 := rfl
  have hnq := G.nq256
  have hi := K.ilt
  have hj := K.lt
  have hob := ob_le (j := j) (by omega)
  have hob' : 24 + 1544 * j + 1544 ≤ phaseBytes := hob
  have hu := H.ult
  have hq4 : q4 R.lw + R.lw % 4 = R.lw := by omega
  have hin2 : Inside (R.lv + BitVec.ofNat 64 (512 * i + 8 * (q4 R.lw + u))) 8 (R.big 4) :=
    G.l_in hi (by omega) (by omega)
  have hin3 : Inside (R.oa (ob j + 8 + 8 * (q4 R.lw + u))) 8 (R.big 7) :=
    G.o_in (by omega) (by omega)
  have hwf := G.wf2 K.F.fr.kept (i := 4) (j := 7) (by omega) (by omega) (by omega) (by omega)
    (by omega) hin2 hin3 (ret := 0)
  have hm : Match (envOf R st.data [(R.lv + BitVec.ofNat 64 (512 * i + 8 * (q4 R.lw + u)), 8),
      (R.oa (ob j + 8 + 8 * (q4 R.lw + u)), 8)] 0) (rS .rax .rcx .rdi) st.data :=
    match_fS K.F.fr (csz := [8, 8]) (cs := [(R.lv + BitVec.ofNat 64 (512 * i + 8 * (q4 R.lw + u)), 8),
      (R.oa (ob j + 8 + 8 * (q4 R.lw + u)), 8)]) ⟨rfl, rfl, trivial⟩
      ⟨al0 (by
        show (ix .rax .rdi 8).eval _ = R.lv + BitVec.ofNat 64 (512 * i + 8 * (q4 R.lw + u))
        rw [ix_eval, H.rax, H.rdi, ixs_ofNat]
        exact addr_add (by omega)), al0 (by
        show (ix .rcx .rdi 8).eval _ = R.oa (ob j + 8 + 8 * (q4 R.lw + u))
        rw [ix_eval, H.rcx, H.rdi, ixs_ofNat, oa_add]
        congr 1
        omega), trivial⟩
  refine blkW G hp b13_in_code (by simp [b13]) run_b13 K.F H.pc hwf hm nofun (o := 8)
    (by decide +kernel) (ro := 3) rfl (lo := 0) (a := R.oa (ob j + 8 + 8 * (q4 R.lw + u))) (n := 8)
    (NativeRustcVm.addr_add_zero _) hin3 (by decide +kernel) fun s1 F1 hm1 hpc1 hs1 ↦ ?_
  have hw : WordAt s1.data.dmem (R.oa (ob j + 8 + 8 * (q4 R.lw + u))) (R.lfw i (q4 R.lw + u)) :=
    word_at (stored_load hm1 (r := 3) (o := 0) (sz := 8) rfl (by omega) (r' := 2) (o' := 0)
      (by decide +kernel) (G.lfw_load K.F.chg (m := st.data)
        (rest := [(R.oa (ob j + 8 + 8 * (q4 R.lw + u)), 8)]) (ret := 0) (n := 8) hi
        (t := q4 R.lw + u) (u := 0) (by omega))) (by omega)
  have hleaf : R.LeafPart s1.data.dmem j i (q4 R.lw + u + 1) :=
    leaf_succ (G.leaf_keep hs1 (by omega) hj H.leaf (by omega)) hw
  have K1 : KA R j i s1.data := K.write G F1 hs1 (by omega) (by omega)
    (fwK_of hwf hm1 (o' := 8) (by decide +kernel) (os := (wB R j).map Prod.fst) (by kdecA) (by kdecA))
    (K.rg.keep hm1 (by kdec))
  have hpc1' := pc_cond hpc1 (b := decide (R.lw % 4 ≠ u + 1)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, add_eval, envRegs]
    rw [K.rg.get (v := BitVec.ofNat 64 (R.lw % 4)) (by simp), H.rdi, ofNat_add,
      beq_ofNat (by omega) (by omega), not_beq_decide])
  by_cases hl : R.lw % 4 ≠ u + 1
  · rw [decide_eq_true hl, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_11_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    refine .done _ (.inl ⟨hpc1', K1, hleaf, by omega, ?_, kreg hm1 rfl H.rax,
      kreg hm1 rfl H.rcx⟩)
    refine (hm1.regs .rdi _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [H.rdi, ofNat_add]
  rw [decide_eq_false hl] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  refine .done _ (.inr ⟨hpc1'.trans (congrArg Host.addrOf rfl), K1, ?_⟩)
  rw [show R.lw = q4 R.lw + u + 1 by omega]
  exact hleaf

end

end NativeRustcVmX64.Wire.WriteOpenings
