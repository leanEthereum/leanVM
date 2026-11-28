module

public import NativeRustcVmArm.Code.Vm.HashPair.Names
public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmArm.Keccak.HashPair.Blocks
public import NativeRustcVmArm.Keccak.Common
public import NativeRustcVm.MemLemmas

/-!
# `hash_pair` meets its contract

`hashPair_spec`: `hash_pair(out, left, right)` stores `left`'s and `right`'s words in its 80-byte
frame (`partL`, `partR`, the entry block in two parts as `left` and `right` may overlap), saves
X30 there, calls `keccak256_words::<hash_words's closure>` on the 8 words (count 8, 64 bytes), and
returns (`ret`) with `hashWords` of them at `out`, which is `hashPair left right`.
-/

namespace NativeRustcVmArm.HashPairRun

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep load_of_wordAt
  same_region)
open NativeRustcVmArm.Keccak (bytesAt_words load_wordAt bytesAt_of_same not_inRange_of_apart)
open Vm.HashPair

@[expose] public section

/-- The frame's base: SP in the body. -/
def frame (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 80

end

public section

theorem addr_eq {a b : BitVec 64} {i j : Nat} (h : a.toNat + i = b.toNat + j)
    (ha : a.toNat + i < 2 ^ 64) : a + BitVec.ofNat 64 i = b + BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_add_ofNat _ _ ha, toNat_add_ofNat _ _ (by omega)]
  exact h

theorem bv_sub_toNat {a : BitVec 64} {n : Nat} (h : n ≤ a.toNat) :
    (a - BitVec.ofNat 64 n).toNat = a.toNat - n := by
  have := a.isLt
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hn]; exact h), hn]

/-- The callee-saved registers a block keeps. -/
theorem regs_kept [Labels] {env : Env} {S0 S : SState} {m m' : MachineData}
    (hm0 : Match env S0 m) (hm : Match env S m')
    (h : (allXRegs.all fun r => !calleeSaved r || ((S0.reg r).isSome && S.reg r == S0.reg r)) =
      true) :
    ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r := by
  simp only [List.all_eq_true] at h
  intro r hr
  have := h r (mem_allXRegs r)
  simp only [hr, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    Option.isSome_iff_exists] at this
  obtain ⟨⟨v, hv⟩, hS⟩ := this
  exact Match.reg_eq hm0 hm hv (hS.trans hv)

/-- Word `i` of a digest, loaded from a region holding it. -/
theorem load_digest {env : Env} {r : Nat} {D : LeanVM.Protocol.Digest}
    (h : NativeRustcVm.WordsAt env.mem0 (env.base r) D.toList) {i : Nat} (hi : i < 4) :
    env.load r (8 * i) 8 = (D.toList.getD i 0).toBitVec := by
  apply load_wordAt
  have := NativeRustcVm.WordsAt.getElem h (i := i) (by simpa using hi)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi), Option.getD_some]

variable [Host]

/-- **`hash_pair` meets its contract.** -/
theorem _root_.NativeRustcVmArm.hashPair_spec {k : Nat} (hp : Placed Vm.HashPair.code k)
    (hkw : Spec (Labels.label NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre
      Keccak256WordsHashPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost := by
  intro m0 hpre
  obtain ⟨hstk, hrc, hml, hnl, hmr, hnr, hmo, hno, hapl, hapr, hapo, hapor⟩ := hpre
  rw [show Labels.label NativeRustcVmArm.Vm.HashPair.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.HashPair.b0Offset) from hp.label NativeRustcVmArm.Vm.HashPair.entry_at]
  have hK : hashPairStack = 768 := rfl
  have hK' : keccak256WordsStack = 688 := rfl
  obtain ⟨hal, hle, hsm⟩ := hstk
  rw [hK] at hle hsm hapl hapr hapo
  obtain ⟨hrcw, hrcnw, hrcap⟩ := hrc
  rw [hK] at hrcap
  have hSlt := m0.regs.SP.toNat_lt
  have hle' : 768 ≤ m0.regs.SP.toBitVec.toNat := hle
  have hF : (frame m0).toNat = m0.regs.SP.toNat - 80 := bv_sub_toNat (by omega)
  have hB : (stackBelow m0 768).toNat = m0.regs.SP.toNat - 768 := bv_sub_toNat hle
  have hfm : ∀ d : DataMem, Kept m0.dmem d → Mapped d (frame m0) 80 := fun d hk i hi => by
    rw [addr_eq (b := stackBelow m0 768) (j := 688 + i) (by rw [hF, hB]; omega)
      (by rw [hF]; omega)]
    exact hk _ (hsm _ (by omega))
  have hfnw : NoWrap (frame m0) 80 := by unfold NoWrap; omega
  have hfal : (frame m0).toNat % 16 = 0 := by rw [hF]; omega
  have hlf : Apart (frame m0) 80 m0.regs.X1.toBitVec 32 := by
    unfold Apart at hapl ⊢; rw [hB] at hapl; rw [hF]; omega
  have hrf : Apart (frame m0) 80 m0.regs.X2.toBitVec 32 := by
    unfold Apart at hapr ⊢; rw [hB] at hapr; rw [hF]; omega
  -- a byte of the frame is a byte of the stack
  have hfs : ∀ p, InRange (frame m0) 80 p → InRange (stackBelow m0 768) 768 p := fun p h => by
    rw [inRange_iff hfnw, hF] at h
    rw [inRange_iff (by rw [hB]; omega), hB]
    omega
  -- Interior cut: the first seven directives load the left input before the right-input window.
  have hb0 := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  rw [show b0 = partLCode ++ partRCode from (List.take_append_drop 7 b0).symm] at hb0
  obtain ⟨hbL, hbR⟩ := List.IsInfixAt.append hb0
  rw [show k + NativeRustcVmArm.Vm.HashPair.b0Offset + partLCode.length = k + (NativeRustcVmArm.Vm.HashPair.b0Offset + 7) from rfl] at hbR
  -- `partL`
  let envA := Env.ofMachine m0 [(frame m0, 80), (m0.regs.X1.toBitVec, 32)]
  have hwfA : envA.WF :=
    Env.wf_of ⟨⟨hfm _ fun _ h => h, hfnw⟩, ⟨hml, hnl⟩, trivial⟩ (List.pairwise_pair.mpr hlf)
  have hmA : Match envA startL m0 :=
    match_ofMachine ⟨rfl, fun _ => hfal, rfl, fun h => absurd h (by decide), trivial⟩
      (by
        show _ = frame m0 + BitVec.ofInt 64 80
        simp only [frame]
        exact (BitVec.sub_add_cancel _ _).symm)
      ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial trivial
  have hb0A : envA.regions[0]? = some (frame m0, 80) := rfl
  have hb1A : envA.regions[1]? = some (m0.regs.X1.toBitVec, 32) := rfl
  refine exec_then hbL partL hwfA hmA fun st1 hm1 hpc1 => ?_
  simp only [PcOk, show partLCode.length = 7 from rfl] at hpc1
  have hsame1 : SameOutside m0.dmem st1.data.dmem (InRange (frame m0) 80) :=
    same_region hm1 hwfA hb0A (by decide)
  have hk1 : Kept m0.dmem st1.data.dmem := hm1.kept hwfA
  have hsp1 : st1.data.regs.SP.toBitVec = frame m0 := hm1.sp.trans (by simp [Sym.eval, envA])
  -- `partR`
  let envB := Env.ofMachine st1.data [(frame m0, 80), (m0.regs.X2.toBitVec, 32)]
  have hwfB : envB.WF :=
    Env.wf_of ⟨⟨hfm _ hk1, hfnw⟩, ⟨fun i hi => hk1 _ (hmr i hi), hnr⟩, trivial⟩
      (List.pairwise_pair.mpr hrf)
  have hx2 : (st1.data.regs.getXReg .X2).toBitVec = m0.regs.X2.toBitVec := hm1.regs .X2 _ rfl
  have hmB : Match envB startR st1.data :=
    match_ofMachine ⟨rfl, fun _ => hfal, rfl, fun h => absurd h (by decide), trivial⟩
      (by rw [hsp1]; simp [Sym.eval]) ⟨by show (st1.data.regs.getXReg .X2).toBitVec = _; rw [hx2]; simp [Sym.eval], trivial⟩ trivial trivial
      trivial
  have hb0B : envB.regions[0]? = some (frame m0, 80) := rfl
  have hb1B : envB.regions[1]? = some (m0.regs.X2.toBitVec, 32) := rfl
  refine exec_at hbR partR hwfB hpc1 hmB fun st2 hm2 hpc2 => ?_
  have hsame2 : SameOutside st1.data.dmem st2.data.dmem (InRange (frame m0) 80) :=
    same_region hm2 hwfB hb0B (by decide)
  have hk2 : Kept st1.data.dmem st2.data.dmem := hm2.kept hwfB
  have hsp2 : st2.data.regs.SP.toBitVec = frame m0 := hm2.sp.trans (by simp [Sym.eval, envB])
  have hsame12 : SameOutside m0.dmem st2.data.dmem (InRange (frame m0) 80) :=
    fun p hp => (hsame2 p hp).trans (hsame1 p hp)
  have hk12 : Kept m0.dmem st2.data.dmem := fun p h => hk2 p (hk1 p h)
  -- the call's arguments
  have hx0 : st2.data.regs.X0 = m0.regs.X0 :=
    (Match.reg_eq hmB hm2 (r := .X0) rfl rfl).trans (Match.reg_eq hmA hm1 (r := .X0) rfl rfl)
  have hx3 : st2.data.regs.X3.toBitVec = frame m0 :=
    (hm2.regs .X3 _ rfl).trans ((hm1.regs .X3 _ rfl).trans (by simp [Sym.eval, envA]))
  have hx4 : st2.data.regs.X4.toNat = 8 := by
    show (st2.data.regs.getXReg .X4).toBitVec.toNat = 8
    rw [hm2.regs .X4 _ rfl]
    show (st1.data.regs.getXReg .X4).toBitVec.toNat = 8
    rw [hm1.regs .X4 _ rfl]
    rfl
  have hx1 : st2.data.regs.X1.toNat = 8 := by
    show (st2.data.regs.getXReg .X1).toBitVec.toNat = 8
    rw [hm2.regs .X1 _ rfl]
    rfl
  have hx2' : st2.data.regs.X2.toNat = 64 := by
    show (st2.data.regs.getXReg .X2).toBitVec.toNat = 64
    rw [hm2.regs .X2 _ rfl]
    rfl
  have hsb : st2.data.regs.SP.toBitVec - BitVec.ofNat 64 688 = stackBelow m0 768 := by
    apply BitVec.eq_of_toNat_eq
    rw [hsp2, bv_sub_toNat (by rw [hF]; omega), hF, hB]
    omega
  have hrcf : Apart rcAddr 192 (frame m0) 80 := by
    unfold Apart at hrcap ⊢; rw [hB] at hrcap; rw [hF]; omega
  have hsb' : stackBelow st2.data keccak256WordsStack = stackBelow m0 768 := hK' ▸ hsb
  have hpre : Keccak256WordsHashPre st2.data := by
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, hrcnw, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hx0]; exact hapor⟩
    · show st2.data.regs.SP.toBitVec.toNat % 16 = 0
      rw [hsp2, hF]; omega
    · show keccak256WordsStack ≤ st2.data.regs.SP.toBitVec.toNat
      rw [hsp2, hF, hK']; omega
    · rw [hK']
      intro i hi
      rw [show st2.data.regs.SP.toBitVec - BitVec.ofNat 64 688 = stackBelow m0 768 from hsb]
      exact hk12 _ (hsm i (by omega))
    · exact bytesAt_of_same hsame12 hrcw fun i hi => not_inRange_of_apart hrcnw hfnw hrcf (by
        have : (LeanVM.Parameters.keccakRC.flatMap NativeRustcVm.wordBytes).length = 192 :=
          Keccak.length_rcBytes
        omega)
    · rw [hsb', hK']; unfold Apart at hrcap ⊢; omega
    · rw [hx1, hx4]
    · rw [hx2', hx4]
    · rw [hx4, hx3]
      intro i hi
      exact hfm _ hk12 i (by omega)
    · rw [hx4, hx3]; unfold NoWrap at hfnw ⊢; omega
    · rw [hx0]; exact fun i hi => hk12 _ (hmo i hi)
    · rw [hx0]; exact hno
    · intro _
      rw [hx4, hx3, hsb', hK']
      unfold Apart
      rw [hB, hF]
      omega
    · rw [hx0, hsb', hK']; unfold Apart at hapo ⊢; omega
  refine call_then hpc2 hkw hpre fun st3 hpc3 hpost => ?_
  obtain ⟨hw3, hsame3, hsaved3⟩ := hpost
  rw [hsb', hK', hx0] at hsame3
  have hk3 : Kept m0.dmem st3.data.dmem := fun p h => hsaved3.2.2 p (hk12 p h)
  -- `ret`
  let envC := Env.ofMachine st3.data [(frame m0, 80)]
  have hwfC : envC.WF :=
    Env.wf_of ⟨⟨hfm _ hk3, hfnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hsp3 : st3.data.regs.SP.toBitVec = frame m0 := by
    rw [hsaved3.2.1]; exact hsp2
  have hmC : Match envC startRet st3.data :=
    match_ofMachine ⟨rfl, fun _ => hfal, trivial⟩ (by rw [hsp3]; simp [Sym.eval]) trivial trivial
      trivial trivial
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.HashPair.b1Offset) := by
    rw [hpc3, show partRCode.length = 9 from rfl, ← b0_next]
    simp only [b0_length, b0Length, Nat.add_assoc]
  refine exec_at (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) ret hwfC hpc3' hmC
    fun st4 hm4 hpc4 => .done _ ⟨?_, ?_, ?_, ?_⟩
  · -- X30 restored from the frame
    have hw30 : WordAt st2.data.dmem (frame m0 + BitVec.ofNat 64 64) m0.regs.X30.toBitVec :=
      wordAt_of_eq (wordAt_write hm2 hb0B (by decide) rfl)
        ((hm1.regs .X30 _ rfl).trans rfl)
    have hw30' : WordAt st3.data.dmem (frame m0 + BitVec.ofNat 64 64) m0.regs.X30.toBitVec :=
      bytesAt_of_same hsame3 hw30 fun i hi h => by
        simp only [List.length_map, List.length_range] at hi
        have e : (frame m0 + BitVec.ofNat 64 64 + BitVec.ofNat 64 i).toNat =
            m0.regs.SP.toNat - 16 + i := by
          rw [addr_add, toNat_add_ofNat _ _ (by omega), hF]
          omega
        rcases h with h | h
        · unfold Apart at hapo
          rw [inRange_iff hno, e] at h
          rw [hB] at hapo
          omega
        · rw [inRange_iff (by rw [hB]; omega), e, hB] at h
          omega
    have hx30 : st4.data.regs.X30 = m0.regs.X30 := by
      apply UInt64.toBitVec_inj.mp
      rw [show st4.data.regs.X30 = st4.data.regs.getXReg .X30 from rfl, hm4.regs .X30 _ rfl]
      exact load_of_wordAt (r := 0) hw30'
    simp only [PcOk] at hpc4
    rw [hpc4, retOf, retOf, hx30]
  · -- the digest
    intro L R hL hR
    have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwfC rfl
    rw [hd4]
    have hLA : NativeRustcVm.WordsAt envA.mem0 (envA.base 1) L.toList := hL
    have hRB : NativeRustcVm.WordsAt envB.mem0 (envB.base 1) R.toList :=
      bytesAt_of_same hsame1 hR fun i hi => not_inRange_of_apart hnr hfnw
        (by unfold Apart at hrf ⊢; omega)
        (by rw [NativeRustcVm.length_wordsBytes] at hi; simpa using hi)
    have hws : NativeRustcVm.WordsAt st2.data.dmem st2.data.regs.X3.toBitVec
        (L.toList ++ R.toList) := by
      rw [hx3]
      refine bytesAt_words fun j hj => ?_
      simp only [List.length_append, Vector.length_toList] at hj
      have hl : ∀ i < 4, (L.toList ++ R.toList).getD i 0 = L.toList.getD i 0 := fun i hi => by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by simpa using hi)]
      have hr : ∀ i < 4, (L.toList ++ R.toList).getD (4 + i) 0 = R.toList.getD i 0 :=
        fun i hi => by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by simp), Vector.length_toList, Nat.add_sub_cancel_left]
      have wL : ∀ i < 4, envA.load 1 (8 * i) 8 = (L.toList.getD i 0).toBitVec :=
        fun i hi => load_digest hLA hi
      have wR : ∀ i < 4, envB.load 1 (8 * i) 8 = (R.toList.getD i 0).toBitVec :=
        fun i hi => load_digest hRB hi
      interval_cases j
      · rw [hl 0 (by decide)]
        exact wordAt_keep hm2 hb0B (by decide) rfl
          (wordAt_of_eq (wordAt_write hm1 hb0A (by decide) rfl) (wL 0 (by decide)))
      · rw [hl 1 (by decide)]
        exact wordAt_keep hm2 hb0B (by decide) rfl
          (wordAt_of_eq (wordAt_write hm1 hb0A (by decide) rfl) (wL 1 (by decide)))
      · rw [hl 2 (by decide)]
        exact wordAt_of_eq (wordAt_write hm2 hb0B (by decide) rfl)
          ((hm1.regs .X8 _ rfl).trans (wL 2 (by decide)))
      · rw [hl 3 (by decide)]
        exact wordAt_of_eq (wordAt_write hm2 hb0B (by decide) rfl)
          ((hm1.regs .X10 _ rfl).trans (wL 3 (by decide)))
      · rw [show (L.toList ++ R.toList).getD 4 0 = R.toList.getD 0 0 from hr 0 (by decide)]
        exact wordAt_of_eq (wordAt_write hm2 hb0B (by decide) rfl) (wR 0 (by decide))
      · rw [show (L.toList ++ R.toList).getD 5 0 = R.toList.getD 1 0 from hr 1 (by decide)]
        exact wordAt_of_eq (wordAt_write hm2 hb0B (by decide) rfl) (wR 1 (by decide))
      · rw [show (L.toList ++ R.toList).getD 6 0 = R.toList.getD 2 0 from hr 2 (by decide)]
        exact wordAt_of_eq (wordAt_write hm2 hb0B (by decide) rfl) (wR 2 (by decide))
      · rw [show (L.toList ++ R.toList).getD 7 0 = R.toList.getD 3 0 from hr 3 (by decide)]
        exact wordAt_of_eq (wordAt_write hm2 hb0B (by decide) rfl) (wR 3 (by decide))
    have h3 := hw3 (L.toList ++ R.toList) (by rw [hx4]; simp) hws
    rw [hx0] at h3
    have e : (L.toList ++ R.toList).toArray = L.toArray ++ R.toArray := by simp; rfl
    rw [hashPair, ← e]
    exact h3
  · intro p hp
    rw [hm4.dmem_eq hwfC rfl]
    refine (hsame3 p fun h => hp ?_).trans (hsame12 p fun h => hp (.inr (hfs p h)))
    rcases h with h | h
    · exact .inl h
    · refine .inr (show InRange (stackBelow m0 768) 768 p from ?_)
      rw [inRange_iff (by rw [hB]; omega), hB] at h ⊢
      omega
  · refine ⟨fun r hr => ?_, ?_, fun p h => hm4.kept hwfC p (hk3 p h)⟩
    · rw [regs_kept hmC hm4 (by decide +kernel) r hr, hsaved3.1 r hr,
        regs_kept hmB hm2 (by decide +kernel) r hr, regs_kept hmA hm1 (by decide +kernel) r hr]
    · apply UInt64.toBitVec_inj.mp
      rw [hm4.sp]
      show frame m0 + BitVec.ofInt 64 80 = _
      simp only [frame]
      exact BitVec.sub_add_cancel _ _

end

end NativeRustcVmArm.HashPairRun
