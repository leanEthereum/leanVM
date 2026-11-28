module

public import NativeRustcVmX64.Bus.BlockForm.Exec
public import NativeRustcVmX64.Bus.Common
public import NativeRustcVm.Bus.Tuples
public import NativeRustcVm.Tables.Same

/-!
# `block_form`'s proof: what its blocks need (x86-64)

Memory changed only in an output `b` (`n` bytes) and the stack (`Same`): kept by a block writing
its frame (`Same.block`) and by a callee writing the output and its stack (`Same.call`); the
read-only data stays at its labels for a callee (`rodataAt_callee`). A form's terms in `TERMS`
are readable and apart from the stack and from what is apart from the data (`terms_ok`). Values:
comparisons of registers known as numbers (`beq_of_toNat`, `ult_of_toNat`), span words of
`TUPLES` (`load_spanWord`).
-/

namespace NativeRustcVmX64.Bus.BlockForm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Bus NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

@[expose] public section

/-- Memory changed only in the `n` bytes from `b` and the `N` bytes of stack. -/
def Same (m0 : MachineData) (N : Nat) (b : BitVec 64) (n : Nat) (d : DataMem) : Prop :=
  NativeRustcVm.SameOutside m0.dmem d
    (fun q ↦ NativeRustcVm.InRange b n q ∨ NativeRustcVm.InRange (stackBelow m0 N) N q)

end

public section

variable {m0 d d' : MachineData} {F N n : Nat} {b : BitVec 64}

/-- **A block writing its frame** keeps `Same`. -/
theorem Same.block [Labels] (hst : StackOk m0 N) (hF : F ≤ N) (hs : Same m0 N b n d.dmem)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 d F rest vars ret).WF) (hm : Match (frameEnv m0 d F rest vars ret) S d')
    (hw : ∀ w ∈ S.mem, w.r = 0) (hbr : belowRet F S = true) : Same m0 N b n d'.dmem :=
  fun q hq ↦ (hm.get?_mem0 hwf fun hW ↦ hq (.inr (inRange_frame_stack hst.2.1 hst.1 hF
    (written_low hwf hw hbr hW)))).trans (hs q hq)

/-- **A callee writing the output and its stack below the frame** keeps `Same`. -/
theorem Same.call (hst : StackOk m0 N) (hsp : rspOf d = stackBelow m0 F) {S' : Nat}
    (hFS : F + S' ≤ N) (hs : Same m0 N b n d.dmem) {o : BitVec 64} {l : Nat}
    (hch : Changes d d' S' o l) (ho : ∀ q, NativeRustcVm.InRange o l q → NativeRustcVm.InRange b n q) :
    Same m0 N b n d'.dmem :=
  fun q hq ↦ (hch q fun h ↦ hq (h.elim (fun h ↦ .inl (ho q h))
    fun h ↦ .inr (inRange_callee hsp hst.2.1 hst.1 hFS h).1)).trans (hs q hq)

/-- **The read-only data for a callee** below the frame, where memory changed only in an output
apart from the data and in the stack. -/
theorem rodataAt_callee [Labels] (hst : StackOk m0 N) (hR : RodataAt m0 N)
    (hs : Same m0 N b n d.dmem) (hA : RodataApart b n) (hnw : NativeRustcVm.NoWrap b n)
    (hsp : rspOf d = stackBelow m0 F) {S' : Nat} (hFS : F + S' ≤ N) : RodataAt d S' := by
  intro t
  have hsb := noWrap_stackBelow hst
  refine ⟨(hR.bytesAt t).of_sameOutside hs fun i hi hq ↦ hq.elim (fun h ↦ ?_) fun h ↦ ?_,
    hR.noWrap t, ?_⟩
  · exact (hA t).symm.not_inRange_add (hR.noWrap t) hnw hi h
  · exact (hR.apart t).not_inRange_add (hR.noWrap t) hsb hi (inRange_le h (by omega))
  · rw [stackBelow_callee hsp (by have := hst.1; omega)]
    have h1 := stackBelow_toNat (m := m0) (n := F + S') (by have := hst.1; omega)
    have h2 := stackBelow_toNat (m := m0) (n := N) hst.1
    exact (hR.apart t).mono_right (by rw [h1, h2]; omega) (by rw [h1, h2]; omega)

/-- An item of the read-only data kept where memory changed only in an output apart from the
data and in the stack. -/
theorem rodata_keep [Labels] (hst : StackOk m0 N) (hR : RodataAt m0 N)
    (hs : Same m0 N b n d.dmem) (hA : RodataApart b n) (hnw : NativeRustcVm.NoWrap b n)
    (t : NativeRustcVm.Data.Item) : NativeRustcVm.BytesAt d.dmem (rodataAddr t) t.bytes :=
  (hR.bytesAt t).of_sameOutside hs fun i hi hq ↦ hq.elim
    (fun h ↦ (hA t).symm.not_inRange_add (hR.noWrap t) hnw hi h)
    fun h ↦ (hR.apart t).not_inRange_add (hR.noWrap t) (noWrap_stackBelow hst) hi
      (inRange_le h (by omega))

/-- **A block writing its frame and the output** (region `1`) keeps `Same`. -/
theorem Same.block2 [Labels] (hst : StackOk m0 N) (hF : F ≤ N) (hs : Same m0 N b n d.dmem)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 d F [(b, n)] vars ret).WF)
    (hm : Match (frameEnv m0 d F [(b, n)] vars ret) S d')
    (hw : ∀ w ∈ S.mem, w.r = 0 ∨ (w.r = 1 ∧ w.off + w.n ≤ n)) (hbr : belowRet F S = true) :
    Same m0 N b n d'.dmem := by
  intro q hq
  refine (hm.get?_mem0 hwf fun hW ↦ hq ?_).trans (hs q hq)
  obtain ⟨w, hwm, b', sz, hb', j, h1, h2, rfl⟩ := written_off hwf hW
  rcases hw w hwm with h0 | ⟨h0, hn⟩
  · rw [h0] at hb'
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    have := belowRet_spec hbr w hwm h0
    exact .inr (inRange_frame_stack hst.2.1 hst.1 hF
      (inRange_off_self (by omega) (by have := hst.1; have := hst.2.1; omega)))
  · rw [h0] at hb'
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    have hnw := hwf.noWrap 1 b n rfl
    exact .inl (inRange_off_self (by omega) (by omega))

/-- **A form kept** by a block writing its frame only. -/
theorem formBuf_keep [Labels] (hst : StackOk m0 N) (hF : F ≤ N)
    (hap : NativeRustcVm.Apart b formBufBytes (stackBelow m0 N) (N + 8))
    (hnw : NativeRustcVm.NoWrap b formBufBytes)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 d F rest vars ret).WF) (hm : Match (frameEnv m0 d F rest vars ret) S d')
    (hw : ∀ w ∈ S.mem, w.r = 0) (hbr : belowRet F S = true) {f : FormW}
    (h : FormBufAt d.dmem b f) : FormBufAt d'.dmem b f := by
  have hapF := apart_frame hap hst.1 hF
  have hnwF := frame_noWrap hst hF
  have hsame : NativeRustcVm.SameOutside d.dmem d'.dmem
      (NativeRustcVm.InRange (stackBelow m0 F) F) := fun q hq ↦
    hm.get?_mem0 hwf fun hW' ↦ hq (written_low hwf hw hbr hW')
  exact NativeRustcVm.Tables.FormBufAt.of_same h (NativeRustcVm.Layout.Same.of_sameOutside hsame
    fun j hj hq ↦ NativeRustcVm.Apart.not_inRange_add hapF hnw hnwF hj (inRange_le hq (by omega)))

/-- **A form's terms in `TERMS`**: readable, apart from the stack and from what is apart from the
read-only data. -/
theorem terms_ok [Labels] {m : MachineData} {N : Nat} (hR : RodataAt m N) {a : BitVec 64}
    {n k : Nat} (hn : 0 < n) (hk : k + n ≤ NativeRustcVm.Data.terms.length)
    (ha : a = rodataAddr .terms + BitVec.ofNat 64 (termBytes * k))
    {b : BitVec 64} {nb : Nat} (hb : RodataApart b nb) :
    Readable m a (termBytes * n) ∧ OffStack m a (termBytes * n) N ∧
      NativeRustcVm.Apart b nb a (termBytes * n) := by
  have hT := hR.bytesAt .terms
  have hTn := hR.noWrap .terms
  have hTa := hR.apart .terms
  have hTb := hb .terms
  have hlen : (NativeRustcVm.Data.Item.terms).bytes.length = termBytes * NativeRustcVm.Data.terms.length := by
    show (NativeRustcVm.Data.terms.flatMap NativeRustcVm.Data.Term.bytes).length = _
    exact NativeRustcVm.length_flatMap_const length_term_bytes _
  have hmap := hT.mapped
  rw [hlen] at hTn hTa hTb hmap
  have h40 : termBytes = 40 := rfl
  rw [h40] at ha hTn hTa hTb hmap ⊢
  rw [terms_length] at hTn hTa hTb hmap hk
  unfold NativeRustcVm.NoWrap at hTn
  have hat : a.toNat = (rodataAddr .terms).toNat + 40 * k := by
    rw [ha, NativeRustcVm.toNat_add_ofNat (by omega)]
  refine ⟨⟨fun i hi ↦ ?_, ?_⟩, ?_, ?_⟩
  · rw [ha, NativeRustcVm.addr_add_add]; exact hmap _ (by omega)
  · show NativeRustcVm.NoWrap _ _
    unfold NativeRustcVm.NoWrap; rw [hat]; omega
  · show NativeRustcVm.Apart _ _ _ _
    exact hTa.mono (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)
  · exact hTb.mono_right (by omega) (by omega)

/-- A form's terms kept where memory changed elsewhere. -/
theorem termsAt_keep {d d' : DataMem} {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    {p : BitVec 64} {f : FormW} (h : TermsAt d p f)
    (hR : ∀ i < termBytes * f.size, ¬R (p + BitVec.ofNat 64 i)) : TermsAt d' p f := by
  intro i hi
  refine NativeRustcVm.Tables.TermWAt.of_same (h i hi) fun j hj ↦ ?_
  rw [off, NativeRustcVm.addr_add_add]
  refine hs _ (hR _ ?_)
  have : termBytes * (i + 1) ≤ termBytes * f.size := Nat.mul_le_mul_left _ hi
  rw [Nat.mul_succ] at this
  omega

/-- Element `j` of `n` readable elements apart from the stack: readable, apart from the stack. -/
theorem elem_ok {m : MachineData} {a : BitVec 64} {n j N : Nat} (hr : Readable m a (16 * n))
    (ho : OffStack m a (16 * n) N) (hj : j < n) :
    Readable m (a + BitVec.ofNat 64 (16 * j)) 16 ∧
      NativeRustcVm.Apart (a + BitVec.ofNat 64 (16 * j)) 16 (stackBelow m N) (N + 8) := by
  have hnw : a.toNat + 16 * n ≤ 2 ^ 64 := hr.2
  have he : (a + BitVec.ofNat 64 (16 * j)).toNat = a.toNat + 16 * j :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  refine ⟨⟨fun i hi ↦ ?_, ?_⟩, ?_⟩
  · rw [NativeRustcVm.addr_add_add]; exact hr.1 _ (by omega)
  · show NativeRustcVm.NoWrap _ _
    unfold NativeRustcVm.NoWrap; rw [he]; omega
  · have h' : NativeRustcVm.Apart a (16 * n) (stackBelow m N) (N + 8) := ho
    unfold NativeRustcVm.Apart at h' ⊢
    rw [he]; omega

/-! ## Values -/

theorem beq_of_toNat {a c : BitVec 64} {x y : Nat} (ha : a.toNat = x) (hc : c.toNat = y) :
    (a == c) = decide (x = y) := by
  by_cases h : x = y
  · subst h
    have : a = c := BitVec.eq_of_toNat_eq (ha.trans hc.symm)
    simp [this]
  · have : a ≠ c := fun e ↦ h (by rw [← ha, ← hc, e])
    simp [this, h]

theorem ult_of_toNat {a c : BitVec 64} {x y : Nat} (ha : a.toNat = x) (hc : c.toNat = y) :
    a.ult c = decide (x < y) := by
  rw [BitVec.ult, ha, hc]

/-- `test al, al`, `je`: AL is `0`. -/
theorem test_al (x : BitVec 64) :
    CmpOp.eq.apply .W8 (BinOp.and.apply .W8 x x) (BitVec.ofNat 64 0) = decide (x.toNat % 256 = 0) := by
  simp only [CmpOp.apply, BinOp.apply, low, ext, Width.bits, BitVec.and_self]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- **A span word of `TUPLES`**, at the tuple RDI below `147`. -/
theorem eval_spanWord [Labels] {env : Env} {o : Nat}
    (hx : (Sym.reg .rdi).eval env = BitVec.ofNat 64 ((Sym.reg .rdi).eval env).toNat)
    (hX : ((Sym.reg .rdi).eval env).toNat < 147) :
    (spanWord o).eval env = env.load 1 (o + 16 * ((Sym.reg .rdi).eval env).toNat) 8 := by
  unfold spanWord
  rw [eval_slotLoad hx (by omega) 146 0 (Nat.zero_le _) (by omega)]
  rfl

end

end NativeRustcVmX64.Bus.BlockForm
