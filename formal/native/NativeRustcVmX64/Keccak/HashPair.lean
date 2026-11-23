module

public import NativeRustcVmX64.Keccak.HashPair.Blocks
public import NativeRustcVmX64.Keccak.Common
public import NativeRustcVm.MemLemmas
public import NativeRustcVmX64.Code.Vm.HashPair.Names
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfHashWords.Names

/-!
# `hash_pair` meets its contract (x86-64)

`hashPair_spec`: `hash_pair(out, left, right)` loads `left`'s words (`partL`) and `right`'s
(`partR`, as `left` and `right` may overlap), stores the 8 words in its frame (`partS`), calls
`keccak256_words::<hash_words's closure>` on them (count 8, 64 bytes), and returns (`ret`) with
`hashWords` of them at `out`, which is `hashPair left right`.
-/

namespace NativeRustcVmX64.HashPairRun

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq wordAt_write same_region)
open NativeRustcVmX64.Keccak (load_wordAt bytesAt_of_same not_inRange_of_apart)
open Vm.HashPair

@[expose] public section

/-- The frame's base: 80 bytes below the entry's RSP. -/
def frame (m0 : MachineData) : BitVec 64 := rspOf m0 - BitVec.ofNat 64 80

end

public section

theorem bv_sub_toNat {a : BitVec 64} {n : Nat} (h : n ≤ a.toNat) :
    (a - BitVec.ofNat 64 n).toNat = a.toNat - n := by
  have := a.isLt
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hn]; exact h), hn]

/-- Word `i` of a digest, loaded from a region holding it. -/
theorem load_digest [Labels] {env : Env} {r : Nat} {D : LeanVM.Protocol.Digest}
    (h : NativeRustcVm.WordsAt env.mem0 (env.base r) D.toList) {i : Nat} (hi : i < 4) :
    env.load r (8 * i) 8 = (D.toList.getD i 0).toBitVec := by
  apply load_wordAt
  have := NativeRustcVm.WordsAt.getElem h (i := i) (by simpa using hi)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi), Option.getD_some]

/-- Words' bytes from their words. -/
theorem bytesAt_words {d : DataMem} {a : BitVec 64} {ws : List UInt64}
    (h : ∀ j < ws.length, WordAt d (a + BitVec.ofNat 64 (8 * j)) (ws.getD j 0).toBitVec) :
    NativeRustcVm.WordsAt d a ws := by
  intro p hp
  rw [NativeRustcVm.length_wordsBytes] at hp
  have := h (p / 8) (by omega) (p % 8) (by simp; omega)
  rw [addr_add, show 8 * (p / 8) + p % 8 = p by omega] at this
  rw [this, List.getElem_map, List.getElem_range, KeccakF.byteOf_toBitVec _ (by omega),
    KeccakF.getElem_eq_getD', show ws.flatMap NativeRustcVm.wordBytes =
      Native.Keccak.wordsBytes ws from rfl, Native.Keccak.Proof.getD_wordsBytes]

theorem keeps_saved [Labels] {env : Env} {S0 S : SState} {m0 m m' : MachineData}
    (hs0 : Saved m0 m) (hm0 : Match env S0 m) (hm : Match env S m') (hwf : env.WF)
    (hd : m.dmem = env.mem0) (hk : keeps S0 S = true) : Saved m0 m' := by
  have hs := Match.saved hm0 hm hwf hd hk
  exact ⟨fun r hr => (hs.1 r hr).trans (hs0.1 r hr), fun p h => hs.2 p (hs0.2 p h)⟩

variable [Host]

set_option linter.unusedSimpArgs false in
/-- **`hash_pair` meets its contract.** -/
theorem hashPair_spec {k : Nat} (hp : Placed Vm.HashPair.code k)
    (hkw : Spec (Labels.label NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre
      Keccak256WordsHashPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost := by
  intro m0 hpre
  obtain ⟨hstk, hrc, hml, hnl, hmr, hnr, hmo, hno, hapl, hapr, hapo, hapor, hgot⟩ := hpre
  rw [show Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.HashPair.b0Offset) from hp.label NativeRustcVmX64.Vm.HashPair.entry_at]
  have hK : hashPairStack = 848 := rfl
  have hK' : keccak256WordsStack = 768 := rfl
  obtain ⟨hle, hsnw, hsm⟩ := hstk
  rw [hK] at hle hsm hapl hapr hapo
  obtain ⟨hrcw, hrcnw, hrcap⟩ := hrc
  rw [hK] at hrcap
  have hSlt := (rspOf m0).isLt
  have hF : (frame m0).toNat = (rspOf m0).toNat - 80 := bv_sub_toNat (by omega)
  have hB : (stackBelow m0 848).toNat = (rspOf m0).toNat - 848 := bv_sub_toNat hle
  have hFo : ∀ o, o < 88 → (frame m0 + BitVec.ofNat 64 o).toNat = (frame m0).toNat + o :=
    fun o ho => Hasher.toNat_add_ofNat' (by omega)
  have hfm : ∀ d : DataMem, Kept m0.dmem d → Mapped d (frame m0) 88 := fun d hk i hi => by
    have e : frame m0 + BitVec.ofNat 64 i = stackBelow m0 848 + BitVec.ofNat 64 (768 + i) := by
      apply BitVec.eq_of_toNat_eq
      rw [hFo i hi, Hasher.toNat_add_ofNat' (by rw [hB]; omega), hF, hB]
      omega
    rw [e]
    exact hk _ (hsm _ (by omega))
  have hfnw : NoWrap (frame m0) 88 := by unfold NoWrap; omega
  have hapl' := hapl
  have hapr' := hapr
  have hapo' := hapo
  have hrcap' := hrcap
  have hnl' := hnl
  have hnr' := hnr
  have hno' := hno
  have hrcnw' := hrcnw
  simp only [Apart, NativeRustcVm.Apart, hB, NativeRustcX64.reg] at hapl' hapr' hapo' hrcap'
  simp only [NoWrap, NativeRustcVm.NoWrap, NativeRustcX64.reg] at hnl' hnr' hno' hrcnw'
  -- `partL`
  have hb0 := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  rw [show b0 = partLCode ++ (partRCode ++ partSCode) from rfl] at hb0
  obtain ⟨hbL, hbRS⟩ := List.IsInfixAt.append hb0
  obtain ⟨hbR, hbS⟩ := List.IsInfixAt.append hbRS
  rw [show k + NativeRustcVmX64.Vm.HashPair.b0Offset + partLCode.length = k + NativeRustcVmX64.Vm.HashPair.b0Offset + partLCode.length from rfl] at hbR hbS
  rw [show k + NativeRustcVmX64.Vm.HashPair.b0Offset + partLCode.length + partRCode.length = k + NativeRustcVmX64.Vm.HashPair.b0Offset + partLCode.length + partRCode.length from rfl] at hbS
  let envA := Env.ofMachine m0 [(reg m0 .rsi, 32)]
  have hwfA : envA.WF := Env.wf_of ⟨⟨hml, hnl⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hmA : Match envA startL m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨(BitVec.add_zero _).symm.trans rfl, trivial⟩
      trivial trivial trivial
  refine exec_then hbL partL hwfA nofun hmA fun st1 hm1 hpc1 => ?_
  simp only [PcOk, show partLCode.length = 6 from rfl] at hpc1
  have hd1 : st1.data.dmem = m0.dmem := hm1.dmem_eq hwfA rfl
  have hs1 : Saved m0 st1.data :=
    keeps_saved ⟨fun _ _ => rfl, fun _ h => h⟩ hmA hm1 hwfA rfl (by decide +kernel)
  -- `partR`
  let envB := Env.ofMachine st1.data [(reg m0 .rdx, 32)]
  have hwfB : envB.WF := Env.wf_of ⟨⟨by rw [Env.ofMachine_mem0, hd1]; exact hmr, hnr⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have hrdx1 : st1.data.regs.get64 .rdx = m0.regs.get64 .rdx :=
    Match.reg_eq hmA hm1 (r := .rdx) rfl rfl
  have hmB : Match envB startR st1.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hrdx1.trans ((BitVec.add_zero _).symm.trans rfl), trivial⟩
      trivial trivial trivial
  refine exec_at hbR partR hwfB nofun hpc1 hmB fun st2 hm2 hpc2 => ?_
  simp only [PcOk, show partRCode.length = 4 from rfl] at hpc2
  have hd2 : st2.data.dmem = m0.dmem := (hm2.dmem_eq hwfB rfl).trans hd1
  have hs2 : Saved m0 st2.data := keeps_saved hs1 hmB hm2 hwfB rfl (by decide +kernel)
  have hrsp2 : st2.data.regs.get64 .rsp = frame m0 + BitVec.ofInt 64 8 := by
    rw [Match.reg_eq hmB hm2 (r := .rsp) rfl rfl, hm1.regs .rsp _ rfl]
    show BinOp.apply .sub .W64 (rspOf m0) (BitVec.ofNat 64 72) = _
    simp only [BinOp.apply, low_W64, ext_W64, frame]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt,
      Width.bits]
    omega
  -- `partS`
  let retA := (Host.addrOf (k + NativeRustcVmX64.Vm.HashPair.b0Offset + partLCode.length + partRCode.length + partSCode.length)).toBitVec
  let envC := Env.ofMachine st2.data [(frame m0, 88)] (fun _ => 0) retA
  have hwfC : envC.WF := Env.wf_of ⟨⟨hfm _ (fun p h => hs2.2 p h), hfnw⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have hmC : Match envC startS st2.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hrsp2, trivial⟩ trivial trivial trivial
  have hb0C : envC.regions[0]? = some (frame m0, 88) := rfl
  refine exec_at hbS partS hwfC (fun _ _ => rfl) hpc2 hmC fun st3 hm3 hpc3 => ?_
  have hsame3 : SameOutside m0.dmem st3.data.dmem (InRange (frame m0) 80) := by
    rw [← hd2]
    exact same_region hm3 hwfC hb0C (by decide) (by decide)
  have hs3 : Saved m0 st3.data := keeps_saved hs2 hmC hm3 hwfC rfl (by decide +kernel)
  -- the call's arguments
  have hrdi : st3.data.regs.get64 .rdi = m0.regs.get64 .rdi :=
    (Match.reg_eq hmC hm3 (r := .rdi) rfl rfl).trans
      ((Match.reg_eq hmB hm2 (r := .rdi) rfl rfl).trans (Match.reg_eq hmA hm1 (r := .rdi) rfl rfl))
  have hrcx : st3.data.regs.get64 .rcx = frame m0 + BitVec.ofNat 64 16 := by
    rw [hm3.regs .rcx _ rfl]
    simp only [Sym.eval, envC, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    rfl
  have hrsi : (st3.data.regs.get64 .rsi).toNat = 8 := by rw [hm3.regs .rsi _ rfl]; rfl
  have hrdx : (st3.data.regs.get64 .rdx).toNat = 64 := by rw [hm3.regs .rdx _ rfl]; rfl
  have hr8 : (st3.data.regs.get64 .r8).toNat = 8 := by rw [hm3.regs .r8 _ rfl]; rfl
  have hrsp3 : rspOf st3.data = frame m0 := by
    rw [rspOf, hm3.regs .rsp _ rfl]
    simp only [Sym.eval, envC, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    exact BitVec.add_zero _
  have hsb : stackBelow st3.data keccak256WordsStack = stackBelow m0 848 := by
    apply BitVec.eq_of_toNat_eq
    rw [show stackBelow st3.data keccak256WordsStack =
        rspOf st3.data - BitVec.ofNat 64 768 from rfl,
      hrsp3, bv_sub_toNat (by rw [hF]; omega), hF, hB]
    omega
  have hk3 : Kept m0.dmem st3.data.dmem := hs3.2
  -- the round constants, untouched by `partS`
  have hrc3 : NativeRustcVm.WordsAt st3.data.dmem rcAddr LeanVM.Parameters.keccakRC :=
    bytesAt_of_same hsame3 hrcw fun i hi => not_inRange_of_apart hrcnw
      (by unfold NoWrap at hfnw ⊢; omega) (by unfold Apart; rw [hF]; omega) (by
        have : (LeanVM.Parameters.keccakRC.flatMap NativeRustcVm.wordBytes).length = 192 :=
          Keccak.length_rcBytes
        omega)
  have hpre : Keccak256WordsHashPre st3.data := by
    refine ⟨⟨?_, ?_, ?_⟩, ⟨hrc3, hrcnw, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show 768 ≤ (rspOf st3.data).toNat
      rw [hrsp3, hF]; omega
    · rw [hrsp3, hF]; omega
    · intro i hi
      rw [show rspOf st3.data - BitVec.ofNat 64 keccak256WordsStack = stackBelow m0 848 from hsb]
      exact hk3 _ (hsm i (by rw [hK'] at hi; omega))
    · rw [hsb]
      unfold NativeRustcVm.Apart
      rw [hK', hB]
      omega
    · show (st3.data.regs.get64 .rsi).toNat = (st3.data.regs.get64 .r8).toNat
      rw [hrsi, hr8]
    · show (st3.data.regs.get64 .rdx).toNat = 8 * (st3.data.regs.get64 .r8).toNat
      rw [hrdx, hr8]
    · show Mapped st3.data.dmem (st3.data.regs.get64 .rcx) (8 * (st3.data.regs.get64 .r8).toNat)
      rw [hrcx, hr8]
      intro i hi
      rw [addr_add]
      exact hfm _ hk3 _ (by omega)
    · show NoWrap (st3.data.regs.get64 .rcx) (8 * (st3.data.regs.get64 .r8).toNat)
      rw [hrcx, hr8]
      unfold NoWrap
      rw [hFo 16 (by omega)]
      omega
    · show Mapped st3.data.dmem (st3.data.regs.get64 .rdi) 32
      rw [hrdi]
      exact fun i hi => hk3 _ (hmo i hi)
    · show NoWrap (st3.data.regs.get64 .rdi) 32
      rw [hrdi]
      exact hno
    · intro _
      show Apart (st3.data.regs.get64 .rcx) (8 * (st3.data.regs.get64 .r8).toNat)
        (stackBelow st3.data keccak256WordsStack) (keccak256WordsStack + 8)
      rw [hrcx, hr8, hsb, hK']
      unfold Apart
      rw [hFo 16 (by omega), hB, hF]
      omega
    · show Apart (st3.data.regs.get64 .rdi) 32
        (stackBelow st3.data keccak256WordsStack) (keccak256WordsStack + 8)
      rw [hrdi, hsb, hK']
      unfold Apart
      rw [hB]
      omega
    · show Apart (st3.data.regs.get64 .rdi) 32 rcAddr 192
      rw [hrdi]
      exact hapor
    · refine hgot.transport ?_ ?_ ?_
      · intro l hl i hi
        apply hsame3
        have hs := (hgot.1 l hl).2.2.1
        change Apart (gotAddr l) 8 (stackBelow m0 848) 856 at hs
        have hg : Apart (gotAddr l) 8 (frame m0) 80 := by
          unfold Apart at hs ⊢
          rw [hB] at hs
          omega
        exact hg.not_inRange ((hgot.1 l hl).2.1)
          (by unfold NoWrap at hfnw ⊢; omega) hi
      · intro l hl
        have hs := (hgot.1 l hl).2.2.1
        change Apart (gotAddr l) 8 (stackBelow m0 848) 856 at hs
        change Apart (gotAddr l) 8 (stackBelow st3.data keccak256WordsStack)
          (keccak256WordsStack + 8)
        rw [hsb, hK']
        unfold Apart at hs ⊢
        omega
      · intro l hl a ha
        simp only [NativeRustcX64.reg, hrdi] at ha
        exact (hgot.1 l hl).2.2.2 a ha
  refine call_then hpc3 hkw hpre fun st4 hpc4 hrsp4 hpost => ?_
  obtain ⟨hw4, hsame4, hsaved4⟩ := hpost
  have hsb' : stackBelow st3.data 768 = stackBelow m0 848 := hsb
  have hsame4' : SameOutside st3.data.dmem st4.data.dmem (fun p =>
      InRange (m0.regs.get64 .rdi) 32 p ∨ InRange (stackBelow m0 848) 768 p) := by
    have := hsame4
    simp only [NativeRustcX64.reg, hrdi, hK', hsb'] at this
    exact this
  have hs4 : Saved m0 st4.data :=
    ⟨fun r hr => (hsaved4.1 r hr).trans (hs3.1 r hr), fun p h => hsaved4.2 p (hs3.2 p h)⟩
  -- `ret`
  let envD := Env.ofMachine st4.data [(frame m0, 88)]
  have hwfD : envD.WF := Env.wf_of ⟨⟨hfm _ hs4.2, hfnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hmD : Match envD startS st4.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨show rspOf st4.data = _ by rw [hrsp4, hrsp3]; rfl, trivial⟩
      trivial trivial trivial
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.HashPair.b1Offset) := hpc4
  -- the return address, as at the entry
  have hslot : ∀ i < 8, st4.data.dmem.get? (rspOf m0 + BitVec.ofNat 64 i) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 i) := fun i hi => by
    have e : (rspOf m0 + BitVec.ofNat 64 i).toNat = (rspOf m0).toNat + i :=
      Hasher.toNat_add_ofNat' (by omega)
    refine (hsame4' _ ?_).trans (hsame3 _ ?_)
    · rintro (h | h)
      · rw [inRange_iff hno', e] at h
        omega
      · rw [inRange_iff (by rw [hB]; omega), e, hB] at h
        omega
    · rw [inRange_iff (by unfold NoWrap at hfnw; omega), e, hF]
      omega
  have hread := hmD.read hwfD (r := 0) (o := 80) (n := 8) rfl (by decide) (by decide)
  have hb80 : envD.base 0 + BitVec.ofNat 64 80 = rspOf m0 := by
    show frame m0 + BitVec.ofNat 64 80 = _
    exact BitVec.sub_add_cancel _ _
  rw [hb80, loadInt_congr hslot] at hread
  refine exec_at (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) ret hwfD nofun hpc4' hmD
    fun st5 hm5 hpc5 => .done _ ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc5
    rw [hpc5]
    exact (retOf_of_loadInt hread).symm
  · rw [rspOf, hm5.regs .rsp _ rfl]
    show frame m0 + BitVec.ofInt 64 88 = _
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat, hF]
    omega
  · -- the digest
    intro L R hL hR
    have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwfD rfl
    have hLA : NativeRustcVm.WordsAt envA.mem0 (envA.base 0) L.toList := hL
    have hRB : NativeRustcVm.WordsAt envB.mem0 (envB.base 0) R.toList := by
      show NativeRustcVm.WordsAt st1.data.dmem (reg m0 .rdx) R.toList
      rw [hd1]
      exact hR
    have eA : ∀ r : Reg64, r ∈ [Reg64.rax, .rcx, .r8, .rsi] →
        st2.data.regs.get64 r = st1.data.regs.get64 r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Match.reg_eq hmB hm2 rfl rfl
    have w0 : st2.data.regs.get64 .rax = (L.toList.getD 0 0).toBitVec :=
      (eA _ (by simp)).trans ((hm1.regs .rax _ rfl).trans (load_digest hLA (i := 0) (by decide)))
    have w1 : st2.data.regs.get64 .rcx = (L.toList.getD 1 0).toBitVec :=
      (eA _ (by simp)).trans ((hm1.regs .rcx _ rfl).trans (load_digest hLA (i := 1) (by decide)))
    have w2 : st2.data.regs.get64 .r8 = (L.toList.getD 2 0).toBitVec :=
      (eA _ (by simp)).trans ((hm1.regs .r8 _ rfl).trans (load_digest hLA (i := 2) (by decide)))
    have w3 : st2.data.regs.get64 .rsi = (L.toList.getD 3 0).toBitVec :=
      (eA _ (by simp)).trans ((hm1.regs .rsi _ rfl).trans (load_digest hLA (i := 3) (by decide)))
    have w4 : st2.data.regs.get64 .r9 = (R.toList.getD 0 0).toBitVec :=
      (hm2.regs .r9 _ rfl).trans (load_digest hRB (i := 0) (by decide))
    have w5 : st2.data.regs.get64 .r10 = (R.toList.getD 1 0).toBitVec :=
      (hm2.regs .r10 _ rfl).trans (load_digest hRB (i := 1) (by decide))
    have w6 : st2.data.regs.get64 .r11 = (R.toList.getD 2 0).toBitVec :=
      (hm2.regs .r11 _ rfl).trans (load_digest hRB (i := 2) (by decide))
    have w7 : st2.data.regs.get64 .rdx = (R.toList.getD 3 0).toBitVec :=
      (hm2.regs .rdx _ rfl).trans (load_digest hRB (i := 3) (by decide))
    have hl : ∀ i < 4, (L.toList ++ R.toList).getD i 0 = L.toList.getD i 0 := fun i hi => by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by simpa using hi)]
    have hr : ∀ i < 4, (L.toList ++ R.toList).getD (4 + i) 0 = R.toList.getD i 0 :=
      fun i hi => by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by simp), Vector.length_toList, Nat.add_sub_cancel_left]
    have hws : NativeRustcVm.WordsAt st3.data.dmem (reg st3.data .rcx) (L.toList ++ R.toList) := by
      show NativeRustcVm.WordsAt st3.data.dmem (st3.data.regs.get64 .rcx) _
      rw [hrcx]
      refine bytesAt_words fun j hj => ?_
      simp only [List.length_append, Vector.length_toList] at hj
      rw [addr_add]
      interval_cases j
      · rw [hl 0 (by decide)]
        exact wordAt_of_eq (wordAt_write hm3 hb0C (by decide) rfl) w0
      · rw [hl 1 (by decide)]
        exact wordAt_of_eq (wordAt_write hm3 hb0C (by decide) rfl) w1
      · rw [hl 2 (by decide)]
        exact wordAt_of_eq (wordAt_write hm3 hb0C (by decide) rfl) w2
      · rw [hl 3 (by decide)]
        exact wordAt_of_eq (wordAt_write hm3 hb0C (by decide) rfl) w3
      · rw [show (L.toList ++ R.toList).getD 4 0 = R.toList.getD 0 0 from hr 0 (by decide)]
        exact wordAt_of_eq (wordAt_write hm3 hb0C (by decide) rfl) w4
      · rw [show (L.toList ++ R.toList).getD 5 0 = R.toList.getD 1 0 from hr 1 (by decide)]
        exact wordAt_of_eq (wordAt_write hm3 hb0C (by decide) rfl) w5
      · rw [show (L.toList ++ R.toList).getD 6 0 = R.toList.getD 2 0 from hr 2 (by decide)]
        exact wordAt_of_eq (wordAt_write hm3 hb0C (by decide) rfl) w6
      · rw [show (L.toList ++ R.toList).getD 7 0 = R.toList.getD 3 0 from hr 3 (by decide)]
        exact wordAt_of_eq (wordAt_write hm3 hb0C (by decide) rfl) w7
    have h4 := hw4 (L.toList ++ R.toList) (by rw [hr8]; simp) hws
    simp only [NativeRustcX64.reg, hrdi] at h4
    have e : (L.toList ++ R.toList).toArray = L.toArray ++ R.toArray := by simp; rfl
    rw [hd5, hashPair, ← e]
    exact h4
  · intro p hp
    rw [hm5.dmem_eq hwfD rfl]
    have hpn : ¬ InRange (reg m0 .rdi) 32 p := fun h => hp (.inl h)
    have hps : ¬ InRange (stackBelow m0 hashPairStack) hashPairStack p := fun h => hp (.inr h)
    rw [hK, inRange_iff (by rw [hB]; omega), hB] at hps
    refine (hsame4' p ?_).trans (hsame3 p ?_)
    · rintro (h | h)
      · exact hpn h
      · rw [inRange_iff (by rw [hB]; omega), hB] at h
        omega
    · rw [inRange_iff (by unfold NoWrap at hfnw; omega), hF]
      omega
  · exact keeps_saved hs4 hmD hm5 hwfD rfl (by decide +kernel)

end

end NativeRustcVmX64.HashPairRun
