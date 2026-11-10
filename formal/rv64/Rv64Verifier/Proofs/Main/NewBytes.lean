import Rv64Verifier.Proofs.Main.NewPlace

/-!
# `Bytecode::new`'s blocks: the buckets

`bstep`: one byte of a word, `used` and `bytes` after it (`buckets_fold`: a word's buckets are its
eight bytes in turn); `ufold`: after the first `k` distinct words, `bfold`: and `m` bytes of the
next. `UB`: past the placement, `used` (`2048` bytes at `U`, freshly allocated) and the `Vec`s
hold a `(used, bytes)`. `used_alloc`: `0x800008a0` allocates and zeroes `used`, into the loop over
the distinct words (`BO`, at `0x800008f0`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

/-! ## The model -/

/-- Byte `j` of a word: its bucket, pushed if not yet `used`. -/
def bstep (w : BitVec 64) (u : List Bool × List (BitVec 16)) (j : Nat) :
    List Bool × List (BitVec 16) :=
  if (Model.toLeBytes w).getD j 0 ≠ 0 then
    Model.usedStep u (256#16 * BitVec.ofNat 16 j + ((Model.toLeBytes w).getD j 0).setWidth 16)
  else u

theorem buckets_fold (w : BitVec 64) (u : List Bool × List (BitVec 16)) :
    (Model.byteBucketsRust w).foldl Model.usedStep u = (List.range 8).foldl (bstep w) u := by
  have hz : (Model.toLeBytes w).zipIdx =
      (List.range 8).map fun j ↦ ((Model.toLeBytes w).getD j 0, j) := by
    apply List.ext_getElem (by simp [Model.toLeBytes])
    intro j h1 h2
    simp only [List.length_zipIdx, Model.toLeBytes, List.length_map, List.length_range] at h1
    simp [Model.toLeBytes, List.getElem_zipIdx, h1]
  rw [Model.byteBucketsRust, hz]
  suffices ∀ (l : List Nat) u, (((l.map fun j ↦ ((Model.toLeBytes w).getD j 0, j)).filter
      fun e ↦ e.1 != 0#8).map fun e ↦ 256#16 * BitVec.ofNat 16 e.2 + e.1.setWidth 16).foldl
      Model.usedStep u = l.foldl (bstep w) u from this _ u
  intro l
  induction l with
  | nil => intro u; rfl
  | cons j l ih =>
    intro u
    simp only [List.map_cons, List.filter_cons, List.foldl_cons]
    by_cases hj : (Model.toLeBytes w).getD j 0 = 0
    · have e : bstep w u j = u := by simp only [bstep, hj, ne_eq, not_true_eq_false, ↓reduceIte]
      have e0 : ((0 : BitVec 8) != 0#8) = false := by decide
      simp only [hj, e0, Bool.false_eq_true, ↓reduceIte]
      rw [ih, e]
    · have e : ((Model.toLeBytes w).getD j 0 != 0#8) = true := by simpa using hj
      have e2 : bstep w u j = Model.usedStep u
          (256#16 * BitVec.ofNat 16 j + ((Model.toLeBytes w).getD j 0).setWidth 16) := by
        simp only [bstep, ne_eq, hj, not_false_eq_true, ↓reduceIte]
      simp only [e, ↓reduceIte, List.map_cons, List.foldl_cons]
      rw [ih, e2]

/-- `used` and `bytes` after the first `k` distinct words. -/
def ufold (g : GrpSt) (st : Model.NewState) (k : Nat) : List Bool × List (BitVec 16) :=
  (g.2.2.take k).foldl (fun u word ↦ (Model.byteBucketsRust word).foldl Model.usedStep u)
    (List.replicate 2048 false, st.bytes)

/-- And the first `m` bytes of the next. -/
def bfold (g : GrpSt) (st : Model.NewState) (k m : Nat) : List Bool × List (BitVec 16) :=
  (List.range m).foldl (bstep (g.2.2.getD k 0)) (ufold g st k)

section
variable (g : GrpSt) (st : Model.NewState)

theorem bfold_succ (k m : Nat) : bfold g st k (m + 1) = bstep (g.2.2.getD k 0) (bfold g st k m) m := by
  simp only [bfold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bfold_zero (k : Nat) : bfold g st k 0 = ufold g st k := rfl

theorem ufold_succ {k : Nat} (hk : k < g.2.2.length) : ufold g st (k + 1) = bfold g st k 8 := by
  simp only [ufold, bfold, List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hk,
    Option.toList_some, List.foldl_cons, List.foldl_nil, buckets_fold,
    List.getD_eq_getElem?_getD, Option.getD_some]

theorem ufold_all : ufold g st g.2.2.length =
    g.2.2.foldl (fun u word ↦ (Model.byteBucketsRust word).foldl Model.usedStep u)
      (List.replicate 2048 false, st.bytes) := by
  simp only [ufold, List.take_length]

theorem usedStep_len (u : List Bool × List (BitVec 16)) (c : BitVec 16) :
    (Model.usedStep u c).1.length = u.1.length := by
  unfold Model.usedStep; split <;> simp

theorem bfold_len : ∀ k m, (bfold g st k m).1.length = 2048 := by
  have hu : ∀ k, (ufold g st k).1.length = 2048 := by
    intro k
    simp only [ufold]
    generalize g.2.2.take k = l
    suffices ∀ (l : List (BitVec 64)) u, u.1.length = 2048 →
        (l.foldl (fun u word ↦ (Model.byteBucketsRust word).foldl Model.usedStep u) u).1.length =
          2048 from this l _ (by simp only [List.length_replicate])
    intro l
    induction l with
    | nil => intro u hu; exact hu
    | cons w l ih =>
      intro u hu
      simp only [List.foldl_cons]
      refine ih _ ?_
      generalize Model.byteBucketsRust w = bs
      induction bs generalizing u with
      | nil => exact hu
      | cons c bs ih' => simp only [List.foldl_cons]; exact ih' _ (by rw [usedStep_len]; exact hu)
  intro k m
  induction m with
  | zero => exact hu k
  | succ m ih =>
    rw [bfold_succ, bstep]
    split
    · rw [usedStep_len]; exact ih
    · exact ih

end

/-! ## The state -/

/-- Past the placement, `used` at `U` and the `Vec`s holding `u`. -/
structure UB (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C : Word) (H1 U : Nat) (u : List Bool × List (BitVec 16))
    (t : MachineState) : Prop where
  rc : RC s words u₀ i L Hb st g D C H1 t
  m24 : t.getMem (msp + 24) = BitVec.ofNat 64 ((words.getD 0 0).toNat - 2 ^ 14 * i - L)
  vs : VS u₀ Hb H1 U 2048 { { { st with words := (rfold words i L g st g.2.2.length).2.2 } with
    positions := (pfold words i L g st L).1 } with bytes := u.2 } t
  used : ∀ b < 2048, byteAt t (BitVec.ofNat 64 (U + b)) = if u.1.getD b false then 1 else 0
  ulen : u.1.length = 2048
  hU1 : H1 ≤ U
  hU2 : U + 2048 ≤ heapNext t
  x8 : t.getReg .x8 = u₀.getReg .x8
  x9 : t.getReg .x9 = BitVec.ofNat 64 (rfold words i L g st g.2.2.length).2.2.length
  x18 : t.getReg .x18 = BitVec.ofNat 64 U
  x24 : t.getReg .x24 = msp + 120
  x25 : t.getReg .x25 = D + BitVec.ofNat 64 (8 * g.2.2.length)
  x26 : t.getReg .x26 = msp + 121
  x27 : t.getReg .x27 = 1

/-- At `0x800008f0` (`0x800008ec` once `k` may be the end), the first `k` distinct words done. -/
structure BO (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C : Word) (H1 U k : Nat) (t : MachineState) : Prop where
  ub : UB s words u₀ i L Hb st g D C H1 U (ufold g st k) t
  hk : k ≤ g.2.2.length
  x15 : t.getReg .x15 = 8
  x23 : t.getReg .x23 = D + BitVec.ofNat 64 (8 * k)

section
variable {s u₀ t t' : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C : Word} {H1 U : Nat} {u : List Bool × List (BitVec 16)}

/-- A frame of `main`'s slots `104..136` keeps `UB`. -/
theorem UB.slots {W : Word → Prop} (h : UB s words u₀ i L Hb st g D C H1 U u t) (hf : BFrame t t' W)
    (hW : ∀ a, W a → Within a (msp + 104) 32)
    (hr : ∀ r ∈ ([.x2, .x8, .x9, .x18, .x24, .x25, .x26, .x27] : List Reg), t'.getReg r = t.getReg r) :
    UB s words u₀ i L Hb st g D C H1 U u t' := by
  have hhi := h.rc.k.ng.heap.hi
  have hU2 := h.hU2
  simp only [heapNext, heapEnd] at hhi hU2
  have hn : heapNext t' = heapNext t := by
    simp only [heapNext]
    rw [hf.getMem (a := nextAddr) (by decide) fun j hj hw ↦ by have := hW _ hw; addr_omega [this, hj]]
  have hsp : t'.getReg .x2 = msp := (hr .x2 (by simp)).trans h.rc.k.ng.sp
  have hheap : HeapOk t' := ⟨by rw [hn]; exact h.rc.k.ng.heap.lo, by rw [hn]; exact h.rc.k.ng.heap.hi⟩
  refine ⟨h.rc.frame hf (fun a ha ↦ Or.inr (Or.inl (hW a ha))) hsp hheap (le_of_eq hn.symm),
    ?_, h.vs.frame hf (fun a ha ↦ by
      have := hW a ha
      exact ⟨by addr_omega [this], by addr_omega [this], Or.inr (Or.inl (by
        simp only [heapNext]; addr_omega [this, hhi]))⟩) (le_of_eq hn.symm) hheap.hi,
    fun b hb ↦ by rw [hf _ fun hw ↦ by have := hW _ hw; addr_omega [this, hb, hU2, hhi]]; exact h.used b hb,
    h.ulen, h.hU1, by rw [hn]; exact h.hU2, (hr .x8 (by simp)).trans h.x8, (hr .x9 (by simp)).trans h.x9,
    (hr .x18 (by simp)).trans h.x18, (hr .x24 (by simp)).trans h.x24,
    (hr .x25 (by simp)).trans h.x25, (hr .x26 (by simp)).trans h.x26,
    (hr .x27 (by simp)).trans h.x27⟩
  rw [← h.m24]
  exact hf.getMem (by decide) fun j hj hw ↦ by have := hW _ hw; addr_omega [this, hj]

/-- A step that writes no memory. -/
theorem UB.same (h : UB s words u₀ i L Hb st g D C H1 U u t) (hm : ∀ a, t'.getMem a = t.getMem a)
    (hr : ∀ r ∈ ([.x2, .x8, .x9, .x18, .x24, .x25, .x26, .x27] : List Reg), t'.getReg r = t.getReg r) :
    UB s words u₀ i L Hb st g D C H1 U u t' :=
  h.slots (BFrame.of_same hm (fun _ ↦ False)) (fun _ h ↦ h.elim) hr

end

/-- `VS` with `used` at `NEXT`. -/
theorem VS.addU {u₀ t : MachineState} {Hb H1 : Nat} {st' : Model.NewState}
    (h : VS u₀ Hb H1 0 0 st' t) : VS u₀ Hb H1 (heapNext t) 2048 st' t := by
  have o : ∀ {a : Word} {size al : Nat}, VecIn t a size al (heapNext u₀) (heapNext t) →
      VMiss t a size Hb H1 0 0 → VMiss t a size Hb H1 (heapNext t) 2048 := fun hin hm ↦
    ⟨hm.1, by rcases hin.buf with h0 | ⟨_, h2⟩ <;> simp only [Out] <;> omega⟩
  exact ⟨h.vecs, h.bufs, o h.bufs.b h.mb, o h.bufs.w h.mw, o h.bufs.p h.mp, o h.bufs.y h.my⟩

/-- Byte `j` of the word at `msp + 120`. -/
theorem byte_w {t : MachineState} {w : Word} (h : t.getMem (msp + 120) = w) {j : Nat} (hj : j < 8) :
    byteAt t (msp + 120 + BitVec.ofNat 64 j) = (Model.toLeBytes w).getD j 0 := by
  rw [byteAt_add (by decide) hj, h]
  simp [Model.toLeBytes, extractByte, hj, Nat.mul_comm]

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C : Word} {H1 : Nat}

/-- `0x800008a0`: `used` allocated at `NEXT` (`U`) and zeroed, into the loop over the distinct
words. -/
theorem used_alloc (h : PX s words u₀ i L Hb st g D C H1 t) (hpc : t.pc = 0x800008a0) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x800008f0 ∧ BO s words u₀ i L Hb st g D C H1 (heapNext t) 0 v)) := by
  have rc := h.rc
  have hsp := rc.k.ng.sp
  have hhi := rc.k.ng.heap.hi
  have hlo := rc.k.ng.heap.lo
  have hh1 := rc.h1
  have hdc := rc.dc
  have hchi := rc.chi
  have hdlo := rc.dlo
  have hb0 := rc.k.hb0
  have hl0 := rc.k.a.inv.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hhi hlo hh1 hb0 hl0
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b800008a0_spec hpc (by rv_eval [hsp, msp]; decide)
  have k₁ := b800008a0_keeps h₁
  have hm₁ := b800008a0_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = msp := (k₁ .x2 (by decide)).trans hsp
  by_cases hfull : (t.getMem (t.getReg .x2 + 16)).toNat ≤ (t.getMem 0xa0000f30).toNat
  · obtain ⟨w, rw', hw⟩ := abort (u := t₁) (by rw [b800008a0_pc_taken h₁ hfull]; decide)
    exact ⟨w, r₁.trans rw', Or.inl hw⟩
  have hpc₁ := b800008a0_pc_not_taken h₁ (by omega)
  rw [hsp, rc.k.bm.m16] at hfull
  have hU : (t.getMem nextAddr).toNat < 0x77fff801 := by
    have : ((0x77fff801 : Word)).toNat = 0x77fff801 := rfl
    simp only [nextAddr]; omega
  have x18₁ : t₁.getReg .x18 = t.getMem nextAddr := b800008a0_x18 h₁
  have x10₁ : t₁.getReg .x10 = 0xa00008a0 := b800008a0_x10 h₁
  -- `0x800008b0`: `NEXT` advanced
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b800008b0_spec hpc₁ (by
    rv_eval [x10₁]; decide)
  have k₂ := b800008b0_keeps h₂
  have hsp₂ : t₂.getReg .x2 = msp := (k₂ .x2 (by decide)).trans hsp₁
  have hx18 : t₁.getReg .x18 ≠ 0 := by
    rw [x18₁]; intro e
    have h0 : (t.getMem nextAddr).toNat = 0 := by rw [e]; rfl
    simp only [nextAddr] at h0 hlo
    omega
  have hpc₂ := b800008b0_pc_not_taken h₂ hx18
  have hf₂ : BFrame t₁ t₂ (Within · nextAddr 8) := by
    have e := BFrame.of_memFrame (b800008b0_frame h₂ (by rw [x10₁]; decide)) (by rw [x10₁]; decide)
      (by decide)
    rw [x10₁] at e
    exact e
  have hn₂ : heapNext t₂ = (t.getMem nextAddr).toNat + 2048 := by
    have e := b800008b0_m_x10_1680 h₂
    rw [x10₁, x18₁] at e
    have e' : t₂.getMem nextAddr = t.getMem nextAddr + 2048 := e
    simp only [heapNext]
    rw [e']
    addr_omega [hU]
  -- `0x800008cc`: `memset(used, 0, 2048)`
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b800008cc_spec hpc₂ trivial
  have k₃ := b800008cc_keeps h₃
  have hm₃ := b800008cc_mem_same h₃
  have x10₃ : t₃.getReg .x10 = t.getMem nextAddr := by
    rw [b800008cc_x10 h₃, k₂ .x18 (by decide), x18₁]
  have x12₃ : t₃.getReg .x12 = 2048 := by rw [b800008cc_x12 h₃, b800008b0_x27 h₂]; rfl
  have pre : MemsetPre t₃ := by
    show Mapped _ _
    rw [x10₃, x12₃]
    left; simp only [nextAddr] at hlo hU ⊢; constructor <;> addr_omega [hlo, hU]
  obtain ⟨t₄, r₄, ⟨hpc₄, hpv, post⟩ | hd⟩ := memset.call r₃ (b800008cc_pc h₃) pre
  swap
  · exact ⟨t₄, r₁.trans (r₂.trans r₄), Or.inl hd⟩
  have hpc₄' : t₄.pc = 0x800008e0 := by rw [hpc₄, returnAddress, b800008cc_x1 h₃]; decide
  have hsp₄ : t₄.getReg .x2 = msp := (hpv.reg .x2).trans ((k₃ .x2 (by decide)).trans hsp₂)
  obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b800008e0_spec hpc₄' (by rv_eval [hsp₄, msp]; decide)
  have k₅ := b800008e0_keeps h₅
  have hm₅ := b800008e0_mem_same h₅
  have hsp₅ : t₅.getReg .x2 = msp := (k₅ .x2 (by decide)).trans hsp₄
  have pfr := post.frame
  have pby := post.bytes
  rw [x10₃, x12₃] at pfr
  rw [x10₃, x12₃, b800008cc_x11 h₃] at pby
  have hf : BFrame t t₅ fun a ↦ Within a nextAddr 8 ∨ Within a (t.getMem nextAddr) 2048 := fun a ha ↦ by
    have e1 : byteAt t₅ a = byteAt t₄ a := by rw [byteAt_eq, byteAt_eq, hm₅]
    have e2 : byteAt t₃ a = byteAt t₂ a := by rw [byteAt_eq, byteAt_eq, hm₃]
    have e3 : byteAt t₁ a = byteAt t a := by rw [byteAt_eq, byteAt_eq, hm₁]
    rw [e1, pfr.byte a fun h' ↦ ha (Or.inr h'), e2, hf₂ a fun h' ↦ ha (Or.inl h'), e3]
  have hn₅ : heapNext t₅ = (t.getMem nextAddr).toNat + 2048 := by
    rw [← hn₂]
    simp only [heapNext]
    rw [hm₅, pfr.getMem fun j hj hw ↦ by simp only [nextAddr] at hU hw; addr_omega [hw, hj, hU], hm₃]
  have hheap₅ : HeapOk t₅ := ⟨by rw [hn₅]; simp only [nextAddr, heapStart] at hlo ⊢; omega,
    by rw [hn₅]; simp only [nextAddr, heapEnd] at hU ⊢; omega⟩
  have hmono : heapNext t ≤ heapNext t₅ := by rw [hn₅]; simp only [heapNext]; omega
  have hW : ∀ a, (Within a nextAddr 8 ∨ Within a (t.getMem nextAddr) 2048) →
      Wr (heapNext u₀) D C g.2.2.length a ∧ (¬ Within a (msp + 240) 24 ∧
        ¬ Within a (msp + 400) 72 ∧ (a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨
          (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
          (heapNext t ≤ a.toNat ∧ a.toNat < heapNext t + 2048))) := by
    intro a ha
    simp only [heapNext]
    simp only [nextAddr] at hU hh1
    rcases ha with ha | ha
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))), by addr_omega [ha],
        by addr_omega [ha], Or.inr (Or.inl (by addr_omega [ha, hU]))⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hb0, hdlo, hdc,
        hchi, hh1], by simp only [heapEnd]; addr_omega [ha, hU],
        fun h' ↦ by addr_omega [h', ha, hdc, hchi, hh1],
        fun h' ↦ by addr_omega [h', ha, hchi, hh1]⟩))))), by addr_omega [ha, hU],
        by addr_omega [ha, hU], Or.inr (Or.inl (by addr_omega [ha]))⟩
  have R : ∀ r ∈ ([.x8, .x9, .x18, .x24, .x25, .x26, .x27] : List Reg), t₅.getReg r = t₂.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₅ _ (by decide)).trans ((hpv.reg _ (by decide)).trans (k₃ _ (by decide)))
  have R1 : ∀ r ∈ ([.x8, .x9, .x25] : List Reg), t₂.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (k₂ _ (by decide)).trans (k₁ _ (by decide))
  refine ⟨t₅, r₁.trans (r₂.trans (r₄.trans r₅)), Or.inr ⟨b800008e0_pc h₅,
    ⟨⟨rc.frame hf (fun a ha ↦ (hW a ha).1) hsp₅ hheap₅ hmono, ?_,
      (h.vs.addU).frame hf (fun a ha ↦ (hW a ha).2) hmono hheap₅.hi, fun b hb ↦ ?_,
      bfold_len g st 0 0, hh1, by rw [hn₅]; rfl,
      (R .x8 (by simp)).trans ((R1 .x8 (by simp)).trans h.x8),
      (R .x9 (by simp)).trans ((R1 .x9 (by simp)).trans h.x9), ?_, ?_,
      (R .x25 (by simp)).trans ((R1 .x25 (by simp)).trans h.x25), ?_,
      by rw [R .x27 (by simp), b800008b0_x27 h₂]⟩, Nat.zero_le _, b800008e0_x15 h₅, ?_⟩⟩⟩
  · rw [← h.m24]
    exact hf.getMem (by decide) fun j hj hw ↦ by
      simp only [nextAddr] at hU
      rcases hw with hw | hw <;> addr_omega [hw, hj, hU]
  · have e1 : byteAt t₅ (BitVec.ofNat 64 (heapNext t + b)) = byteAt t₄ (BitVec.ofNat 64 (heapNext t + b)) := by
      rw [byteAt_eq, byteAt_eq, hm₅]
    have e := List.getElem_of_eq pby (i := b) (by rw [bytesAt_length]; exact hb)
    rw [bytesAt_getElem, List.getElem_replicate] at e
    have ea : t.getMem nextAddr + BitVec.ofNat 64 b = BitVec.ofNat 64 (heapNext t + b) := by
      simp only [heapNext]; rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [ea] at e
    rw [e1, e]
    have hu0 : (ufold g st 0).1 = List.replicate 2048 false := rfl
    rw [hu0, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp only [hb, ↓reduceIte, Option.getD_some, Bool.false_eq_true]
    rfl
  · rw [R .x18 (by simp), k₂ .x18 (by decide), x18₁]
    simp only [heapNext]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [R .x24 (by simp), b800008b0_x24 h₂, hsp₁]
  · rw [R .x26 (by simp), b800008b0_x26 h₂, hsp₁]
  · rw [b800008e0_x23 h₅, hsp₄, ← hm₅, hf.getMem (by decide) fun j hj hw ↦ by
      simp only [nextAddr] at hU
      rcases hw with hw | hw <;> addr_omega [hw, hj, hU], h.rc.m72, Nat.mul_zero]
    exact (BitVec.add_zero D).symm

end

/-! ## A word's bytes -/

theorem bucket_all : ∀ m < 8, ∀ b < 256,
    ((BitVec.ofNat 64 m * 256) ||| BitVec.ofNat 64 b) = BitVec.ofNat 64 (256 * m + b) ∧
    (((BitVec.ofNat 64 m * 256) ||| BitVec.ofNat 64 b) * 0x1000000000000) >>> 48 =
      BitVec.ofNat 64 (256 * m + b) := by
  decide +kernel

theorem shr59 : ∀ m < 8, (BitVec.ofNat 64 m * 0x100000000000000) >>> 59 = 0 := by
  decide +kernel

theorem zext8 (b : BitVec 8) : b.zeroExtend 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- Byte `m` of distinct word `k`. -/
abbrev wbyte (g : GrpSt) (k m : Nat) : BitVec 8 := (Model.toLeBytes (g.2.2.getD k 0)).getD m 0

/-- At `0x8000092c`, byte `m` of distinct word `k` next. -/
structure BI (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C : Word) (H1 U k m : Nat) (t : MachineState) : Prop where
  ub : UB s words u₀ i L Hb st g D C H1 U (bfold g st k m) t
  hk : k < g.2.2.length
  hm : m < 8
  w : t.getMem (msp + 120) = g.2.2.getD k 0
  x15 : t.getReg .x15 = 8
  x19 : t.getReg .x19 = BitVec.ofNat 64 m
  x20 : t.getReg .x20 = BitVec.ofNat 64 m
  x23 : t.getReg .x23 = D + BitVec.ofNat 64 (8 * (k + 1))

/-- At `0x80000958`, byte `m` zero and skipped. -/
structure BZ (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C : Word) (H1 U k m : Nat) (t : MachineState) : Prop where
  ub : UB s words u₀ i L Hb st g D C H1 U (bfold g st k (m + 1)) t
  hk : k < g.2.2.length
  hm : m < 8
  w : t.getMem (msp + 120) = g.2.2.getD k 0
  x10 : t.getReg .x10 = BitVec.ofNat 64 m
  x12 : t.getReg .x12 = msp + 121 + BitVec.ofNat 64 m
  x13 : t.getReg .x13 = BitVec.ofNat 64 m - 7
  x15 : t.getReg .x15 = 8
  x20 : t.getReg .x20 = BitVec.ofNat 64 (m + 1)
  x23 : t.getReg .x23 = D + BitVec.ofNat 64 (8 * (k + 1))

/-- At `0x80000974`, byte `m` nonzero, its bucket next. -/
structure BN (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C : Word) (H1 U k m : Nat) (t : MachineState) : Prop where
  ub : UB s words u₀ i L Hb st g D C H1 U (bfold g st k m) t
  hk : k < g.2.2.length
  hm : m < 8
  w : t.getMem (msp + 120) = g.2.2.getD k 0
  nz : wbyte g k m ≠ 0
  x10 : t.getReg .x10 = BitVec.ofNat 64 m
  x11 : t.getReg .x11 = BitVec.ofNat 64 (wbyte g k m).toNat
  x15 : t.getReg .x15 = 8
  x20 : t.getReg .x20 = BitVec.ofNat 64 (m + 1)
  x23 : t.getReg .x23 = D + BitVec.ofNat 64 (8 * (k + 1))

/-- At `0x80000928`, byte `m` done. -/
structure BD (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C : Word) (H1 U k m : Nat) (t : MachineState) : Prop where
  ub : UB s words u₀ i L Hb st g D C H1 U (bfold g st k (m + 1)) t
  hk : k < g.2.2.length
  hm : m < 8
  w : t.getMem (msp + 120) = g.2.2.getD k 0
  x15 : t.getReg .x15 = 8
  x19 : t.getReg .x19 = BitVec.ofNat 64 (m + 1)
  x20 : t.getReg .x20 = BitVec.ofNat 64 (m + 1)
  x23 : t.getReg .x23 = D + BitVec.ofNat 64 (8 * (k + 1))

theorem bfold_zero_byte {g : GrpSt} {st : Model.NewState} {k m : Nat} (hz : wbyte g k m = 0) :
    bfold g st k (m + 1) = bfold g st k m := by
  rw [bfold_succ, bstep]
  simp only [wbyte] at hz
  simp only [hz, ne_eq, not_true_eq_false, ↓reduceIte]

theorem regs8 {t t' : MachineState} {l : List Reg} (hk : ∀ r ∈ l, t'.getReg r = t.getReg r)
    (hsub : ([.x2, .x8, .x9, .x18, .x24, .x25, .x26, .x27] : List Reg) ⊆ l) :
    ∀ r ∈ ([.x2, .x8, .x9, .x18, .x24, .x25, .x26, .x27] : List Reg), t'.getReg r = t.getReg r :=
  fun r hr ↦ hk r (hsub hr)

theorem zext8_eq_zero {b : BitVec 8} : b.zeroExtend 64 = 0 ↔ b = 0 := by
  rw [zext8]
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    have hb := b.isLt
    apply BitVec.eq_of_toNat_eq
    have h0 : (0 : BitVec 8).toNat = 0 := rfl
    have h0' : (0 : Word).toNat = 0 := rfl
    omega
  · rintro rfl; rfl

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C : Word} {H1 U k m : Nat}

/-- `0x800008f0`: distinct word `k` spilled to `msp + 120`, into its bytes. -/
theorem bytes_word (h : BO s words u₀ i L Hb st g D C H1 U k t) (hpc : t.pc = 0x800008f0)
    (hk : k < g.2.2.length) :
    ∃ v, Reaches Image.code t v ∧ v.pc = 0x8000092c ∧ BI s words u₀ i L Hb st g D C H1 U k 0 v := by
  have ub := h.ub
  have rc := ub.rc
  have hsp := rc.k.ng.sp
  have hdal := rc.dal
  have hdlo := rc.dlo
  have hdc := rc.dc
  have hchi := rc.chi
  have hh1 := rc.h1
  have hhi := rc.k.ng.heap.hi
  have hb0 := rc.k.hb0
  have hl0 := rc.k.a.inv.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hh1 hhi hb0 hl0
  have hDk : (D + BitVec.ofNat 64 (8 * k)).toNat = D.toNat + 8 * k := by
    addr_omega [hdc, hchi, hh1, hhi, hk]
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b800008f0_spec hpc (by
    rv_eval []
    simp only [hsp, h.x23]
    and_intros
    all_goals first
      | decide
      | (refine (Sym.validAccess_eight _).mpr ⟨Or.inl ⟨?_, ?_⟩, ?_⟩ <;>
          addr_omega [hDk, hdal, hdlo, hb0, hl0, hdc, hchi, hh1, hhi, hk]))
  have kv := b800008f0_keeps hv
  have hf := holds_slots hv hsp [128, 120, 112] (by decide) (by decide)
  have ub' := ub.slots hf (fun a ⟨c, hc, hin⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> addr_omega [hin])
    (regs8 kv (by decide))
  refine ⟨v, rv, b800008f0_pc hv, ⟨ub', hk, by omega, ?_, (kv .x15 (by decide)).trans h.x15,
    by rw [b800008f0_x19 hv]; rfl, by rw [b800008f0_x20 hv]; rfl, ?_⟩⟩
  · have e := b800008f0_m_x2_120 hv
    rw [hsp, h.x23] at e
    rw [e, ← rwords_getD hk, rc.dist]
  · rw [b800008f0_x23 hv, h.x23]
    apply BitVec.eq_of_toNat_eq
    addr_omega [hDk, hdc, hchi, hh1, hhi, hk]

/-- `0x8000092c`: byte `m` loaded; zero (`0x80000958`) or not (`0x80000974`). -/
theorem bytes_byte (h : BI s words u₀ i L Hb st g D C H1 U k m t) (hpc : t.pc = 0x8000092c) :
    ∃ v, Reaches Image.code t v ∧ ((v.pc = 0x80000958 ∧ BZ s words u₀ i L Hb st g D C H1 U k m v) ∨
      (v.pc = 0x80000974 ∧ BN s words u₀ i L Hb st g D C H1 U k m v)) := by
  have ub := h.ub
  have hm := h.hm
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches NB.g8000092c_spec hpc trivial
  have k₁ := NB.g8000092c_keeps h₁
  have hm₁ := NB.g8000092c_mem_same h₁
  have x10₁ : t₁.getReg .x10 = msp + 120 + BitVec.ofNat 64 m := by
    rw [NB.g8000092c_x10 h₁, ub.x24, h.x20]
  obtain ⟨t₂, r₂, hpc₂, hr₂, hm₂⟩ := step_lbu (code := Image.code) (s := t₁) (rd := .x11)
    (rs1 := .x10) (off := 0) (by rw [NB.g8000092c_pc h₁]; exact fetch_of (by decide +kernel))
    (by rw [off0, x10₁]; exact validMem_of (Or.inr (by constructor <;> addr_omega [hm])))
  rw [off0, x10₁] at hr₂
  have hb : byteAt t₁ (msp + 120 + BitVec.ofNat 64 m) = wbyte g k m :=
    byte_w (w := g.2.2.getD k 0) (by rw [hm₁]; exact h.w) hm
  have x11₂ : t₂.getReg .x11 = (wbyte g k m).zeroExtend 64 := by rw [hr₂, hb]; simp
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches NB.g80000934_spec (by rw [hpc₂, NB.g8000092c_pc h₁]; rfl)
    trivial
  have k₃ := NB.g80000934_keeps h₃
  have hm₃ := NB.g80000934_mem_same h₃
  have R₂ : ∀ r, r ≠ .x11 → t₂.getReg r = t₁.getReg r := fun r hr ↦ by rw [hr₂]; simp [hr]
  have hm03 : ∀ a, t₃.getMem a = t.getMem a := fun a ↦ by rw [hm₃, hm₂, hm₁]
  have R03 : ∀ r ∈ ([.x2, .x8, .x9, .x15, .x18, .x19, .x20, .x23, .x24, .x25, .x26, .x27] : List Reg),
      t₃.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₃ _ (by decide)).trans ((R₂ _ (by decide)).trans (k₁ _ (by decide)))
  have x14₃ : t₃.getReg .x14 = BitVec.ofNat 64 (m + 1) := by
    rw [NB.g80000934_x14 h₃, R₂ _ (by decide), k₁ .x20 (by decide), h.x20, BitVec.ofNat_add]; rfl
  have w₃ : t₃.getMem (msp + 120) = g.2.2.getD k 0 := by rw [hm03]; exact h.w
  by_cases hz : wbyte g k m = 0
  · have hpc₃ := NB.g80000934_pc_taken h₃ (by rw [x11₂, hz]; rfl)
    obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b80000948_spec hpc₃ trivial
    have kv := b80000948_keeps hv
    have hmv := b80000948_mem_same hv
    have ubv := ub.same (fun a ↦ by rw [hmv, hm03]) fun r hr ↦ by
      rw [kv _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
      exact R03 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    rw [← bfold_zero_byte hz] at ubv
    refine ⟨v, r₁.trans ((show Reaches Image.code t₁ t₂ from ⟨1, r₂⟩).trans (r₃.trans rv)),
      Or.inl ⟨b80000948_pc hv, ubv, h.hk, hm, by rw [hmv]; exact w₃, ?_, ?_, ?_,
      by rw [kv .x15 (by decide), R03 .x15 (by simp)]; exact h.x15, by rw [b80000948_x20 hv, x14₃],
      by rw [kv .x23 (by decide), R03 .x23 (by simp)]; exact h.x23⟩⟩
    · rw [b80000948_x10 hv, R03 .x19 (by simp), h.x19]
    · rw [b80000948_x12 hv, R03 .x26 (by simp), R03 .x20 (by simp), ub.x26, h.x20]
    · rw [b80000948_x13 hv, R03 .x20 (by simp), h.x20]
  · have hpc₃ := NB.g80000934_pc_not_taken h₃ (by
      rw [x11₂]; exact fun e ↦ hz (zext8_eq_zero.mp e))
    obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b8000093c_spec hpc₃ trivial
    have kv := b8000093c_keeps hv
    have hmv := b8000093c_mem_same hv
    have ubv := ub.same (fun a ↦ by rw [hmv, hm03]) fun r hr ↦ by
      rw [kv _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
      exact R03 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    refine ⟨v, r₁.trans ((show Reaches Image.code t₁ t₂ from ⟨1, r₂⟩).trans (r₃.trans rv)),
      Or.inr ⟨b8000093c_pc hv, ubv, h.hk, hm, by rw [hmv]; exact w₃, hz, ?_, ?_,
      by rw [kv .x15 (by decide), R03 .x15 (by simp)]; exact h.x15, by rw [b8000093c_x20 hv, x14₃],
      by rw [kv .x23 (by decide), R03 .x23 (by simp)]; exact h.x23⟩⟩
    · rw [b8000093c_x10 hv, R03 .x19 (by simp), h.x19]
    · rw [kv .x11 (by decide), k₃ .x11 (by decide), x11₂, zext8]

end

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C : Word} {H1 U k m : Nat}

theorem ub_regs {t' : MachineState} (k : ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10,
    .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
    .x27, .x28, .x29, .x30, .x31] : List Reg), t'.getReg r = t.getReg r) :
    ∀ r ∈ ([.x2, .x8, .x9, .x18, .x24, .x25, .x26, .x27] : List Reg), t'.getReg r = t.getReg r :=
  regs8 k (by decide)

/-- `0x80000958`: past a zero byte; the word done, or the next byte loaded. -/
theorem bytes_skip (h : BZ s words u₀ i L Hb st g D C H1 U k m t) (hpc : t.pc = 0x80000958) :
    ∃ v, Reaches Image.code t v ∧
      ((v.pc = 0x800008ec ∧ BO s words u₀ i L Hb st g D C H1 U (k + 1) v) ∨
        (v.pc = 0x80000958 ∧ m + 1 < 8 ∧ BZ s words u₀ i L Hb st g D C H1 U k (m + 1) v) ∨
        (v.pc = 0x80000974 ∧ m + 1 < 8 ∧ BN s words u₀ i L Hb st g D C H1 U k (m + 1) v)) := by
  have hm := h.hm
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000958_spec hpc trivial
  have k₁ := b80000958_keeps h₁
  have hm₁ := b80000958_mem_same h₁
  have ub₁ := h.ub.same hm₁ (ub_regs k₁)
  by_cases h7 : m = 7
  · subst h7
    refine ⟨t₁, r₁, Or.inl ⟨b80000958_pc_taken h₁ (by rw [h.x13]; rfl), ?_, by have := h.hk; omega,
      (k₁ .x15 (by decide)).trans h.x15, (k₁ .x23 (by decide)).trans h.x23⟩⟩
    rw [ufold_succ g st h.hk]
    exact ub₁
  have hpc₁ := b80000958_pc_not_taken h₁ (by
    rw [h.x13]; intro e; have := congrArg BitVec.toNat e
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    have h7' : (7 : Word).toNat = 7 := rfl
    have h0 : (0 : Word).toNat = 0 := rfl
    rw [h7', h0] at this
    omega)
  -- `0x8000095c`: byte `m + 1`
  have x12₁ : t₁.getReg .x12 = msp + 120 + BitVec.ofNat 64 (m + 1) := by
    rw [k₁ .x12 (by decide), h.x12]
    apply BitVec.eq_of_toNat_eq
    addr_omega [hm]
  obtain ⟨t₂, r₂, hpc₂, hr₂, hm₂⟩ := step_lbu (code := Image.code) (s := t₁) (rd := .x11)
    (rs1 := .x12) (off := 0) (by rw [hpc₁]; exact fetch_of (by decide +kernel))
    (by rw [off0, x12₁]; exact validMem_of (Or.inr (by constructor <;> addr_omega [hm, h7])))
  rw [off0, x12₁] at hr₂
  have hb : byteAt t₁ (msp + 120 + BitVec.ofNat 64 (m + 1)) = wbyte g k (m + 1) :=
    byte_w (w := g.2.2.getD k 0) (by rw [hm₁]; exact h.w) (by omega)
  have x11₂ : t₂.getReg .x11 = (wbyte g k (m + 1)).zeroExtend 64 := by rw [hr₂, hb]; simp
  have R₂ : ∀ r, r ≠ .x11 → t₂.getReg r = t₁.getReg r := fun r hr ↦ by rw [hr₂]; simp [hr]
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches NB.g80000960_spec (by rw [hpc₂, hpc₁]; rfl) trivial
  have kv := NB.g80000960_keeps hv
  have hmv := NB.g80000960_mem_same hv
  have hm0 : ∀ a, v.getMem a = t.getMem a := fun a ↦ by rw [hmv, hm₂, hm₁]
  have R : ∀ r ∈ ([.x2, .x8, .x9, .x15, .x18, .x23, .x24, .x25, .x26, .x27] : List Reg),
      v.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (kv _ (by decide)).trans ((R₂ _ (by decide)).trans (k₁ _ (by decide)))
  have ubv := h.ub.same hm0 fun r hr ↦ R r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have x10v : v.getReg .x10 = BitVec.ofNat 64 (m + 1) := by
    rw [NB.g80000960_x10 hv, R₂ _ (by decide), k₁ .x10 (by decide), h.x10]
    apply BitVec.eq_of_toNat_eq; addr_omega [hm]
  have x20v : v.getReg .x20 = BitVec.ofNat 64 (m + 1 + 1) := by
    rw [NB.g80000960_x20 hv, R₂ _ (by decide), k₁ .x20 (by decide), h.x20]
    apply BitVec.eq_of_toNat_eq; addr_omega [hm]
  have r₁₂ : Reaches Image.code t v :=
    r₁.trans ((show Reaches Image.code t₁ t₂ from ⟨1, r₂⟩).trans rv)
  by_cases hz : wbyte g k (m + 1) = 0
  · rw [← bfold_zero_byte hz] at ubv
    refine ⟨v, r₁₂, Or.inr (Or.inl ⟨NB.g80000960_pc_taken hv (by rw [x11₂, hz]; rfl), by omega,
      ⟨ubv, h.hk, by omega, by rw [hm0]; exact h.w, x10v, ?_, ?_, (R .x15 (by simp)).trans h.x15,
      x20v, (R .x23 (by simp)).trans h.x23⟩⟩)⟩
    · rw [NB.g80000960_x12 hv, R₂ _ (by decide), k₁ .x12 (by decide), h.x12, BitVec.add_assoc,
        BitVec.ofNat_add]; rfl
    · rw [NB.g80000960_x13 hv, R₂ _ (by decide), k₁ .x13 (by decide), h.x13,
        show BitVec.ofNat 64 (m + 1) = BitVec.ofNat 64 m + 1 from by rw [BitVec.ofNat_add]; rfl]
      ring
  · refine ⟨v, r₁₂, Or.inr (Or.inr ⟨NB.g80000960_pc_not_taken hv (by
      rw [x11₂]; exact fun e ↦ hz (zext8_eq_zero.mp e)), by omega,
      ⟨h.ub.same hm0 fun r hr ↦ R r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp), h.hk, by omega,
      by rw [hm0]; exact h.w, hz, x10v, ?_, (R .x15 (by simp)).trans h.x15, x20v,
      (R .x23 (by simp)).trans h.x23⟩⟩)⟩
    rw [kv .x11 (by decide), x11₂, zext8]

/-- `0x80000928`: on to the next byte, or the word done. -/
theorem bytes_next (h : BD s words u₀ i L Hb st g D C H1 U k m t) (hpc : t.pc = 0x80000928) :
    ∃ v, Reaches Image.code t v ∧
      ((v.pc = 0x800008ec ∧ BO s words u₀ i L Hb st g D C H1 U (k + 1) v) ∨
        (v.pc = 0x8000092c ∧ m + 1 < 8 ∧ BI s words u₀ i L Hb st g D C H1 U k (m + 1) v)) := by
  have hm := h.hm
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b80000928_spec hpc trivial
  have kv := b80000928_keeps hv
  have hmv := b80000928_mem_same hv
  have ubv := h.ub.same hmv (ub_regs kv)
  by_cases h7 : m + 1 = 8
  · refine ⟨v, rv, Or.inl ⟨b80000928_pc_taken hv (by rw [h.x20, h.x15, h7]; rfl), ?_,
      by have := h.hk; omega, (kv .x15 (by decide)).trans h.x15, (kv .x23 (by decide)).trans h.x23⟩⟩
    rw [ufold_succ g st h.hk, ← h7]
    exact ubv
  · refine ⟨v, rv, Or.inr ⟨b80000928_pc_not_taken hv (by
      rw [h.x20, h.x15]; intro e; have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      have h8 : (8 : Word).toNat = 8 := rfl
      omega), by omega, ⟨ubv, h.hk, by omega, by rw [hmv]; exact h.w,
      (kv .x15 (by decide)).trans h.x15, (kv .x19 (by decide)).trans h.x19,
      (kv .x20 (by decide)).trans h.x20, (kv .x23 (by decide)).trans h.x23⟩⟩⟩

/-- `0x800008ec`: on to the next distinct word, or the buckets done (`0x800009c8`). -/
theorem bytes_outer (h : BO s words u₀ i L Hb st g D C H1 U k t) (hpc : t.pc = 0x800008ec) :
    ∃ v, Reaches Image.code t v ∧ BO s words u₀ i L Hb st g D C H1 U k v ∧
      ((k < g.2.2.length ∧ v.pc = 0x800008f0) ∨ (k = g.2.2.length ∧ v.pc = 0x800009c8)) := by
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b800008ec_spec hpc trivial
  have kv := b800008ec_keeps hv
  have hmv := b800008ec_mem_same hv
  have bo : BO s words u₀ i L Hb st g D C H1 U k v := ⟨h.ub.same hmv (ub_regs kv), h.hk,
    (kv .x15 (by decide)).trans h.x15, (kv .x23 (by decide)).trans h.x23⟩
  have rc := h.ub.rc
  have hdc := rc.dc
  have hchi := rc.chi
  have hh1 := rc.h1
  have hhi := rc.k.ng.heap.hi
  simp only [heapNext, heapEnd] at hh1 hhi
  have hk := h.hk
  by_cases he : k = g.2.2.length
  · exact ⟨v, rv, bo, Or.inr ⟨he, b800008ec_pc_taken hv (by rw [h.x23, h.ub.x25, he])⟩⟩
  · refine ⟨v, rv, bo, Or.inl ⟨by omega, b800008ec_pc_not_taken hv fun e ↦ he ?_⟩⟩
    rw [h.x23, h.ub.x25] at e
    have := congrArg BitVec.toNat e
    addr_omega [this, hdc, hchi, hh1, hhi, hk]

end

/-- The bucket of byte `m` of distinct word `k`. -/
abbrev wbucket (g : GrpSt) (k m : Nat) : BitVec 16 :=
  256#16 * BitVec.ofNat 16 m + (wbyte g k m).setWidth 16

theorem wbucket_toNat {g : GrpSt} {k m : Nat} (hm : m < 8) :
    (wbucket g k m).toNat = 256 * m + (wbyte g k m).toNat := by
  have hb := (wbyte g k m).isLt
  simp only [wbucket, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega

theorem bfold_nz {g : GrpSt} {st : Model.NewState} {k m : Nat} (hz : wbyte g k m ≠ 0) :
    bfold g st k (m + 1) = Model.usedStep (bfold g st k m) (wbucket g k m) := by
  rw [bfold_succ, bstep]
  simp only [wbyte] at hz
  simp only [hz, ne_eq, not_false_eq_true, ↓reduceIte]

/-- At `0x800009a4`, byte `m`'s bucket not yet `used`: `a0` its byte of `used`, `s5` the bucket. -/
structure BP (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C : Word) (H1 U k m : Nat) (t : MachineState) : Prop where
  ub : UB s words u₀ i L Hb st g D C H1 U (bfold g st k m) t
  hk : k < g.2.2.length
  hm : m < 8
  w : t.getMem (msp + 120) = g.2.2.getD k 0
  nz : wbyte g k m ≠ 0
  fresh : (bfold g st k m).1.getD (wbucket g k m).toNat false = false
  x10 : t.getReg .x10 = BitVec.ofNat 64 (U + (wbucket g k m).toNat)
  x15 : t.getReg .x15 = 8
  x19 : t.getReg .x19 = BitVec.ofNat 64 (m + 1)
  x20 : t.getReg .x20 = BitVec.ofNat 64 (m + 1)
  x21 : t.getReg .x21 = BitVec.ofNat 64 (wbucket g k m).toNat
  x23 : t.getReg .x23 = D + BitVec.ofNat 64 (8 * (k + 1))

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C : Word} {H1 U k m : Nat}

/-- `0x80000974`: byte `m`'s bucket looked up in `used`; done if there (`0x80000928`). -/
theorem bytes_bucket (h : BN s words u₀ i L Hb st g D C H1 U k m t) (hpc : t.pc = 0x80000974) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x80000928 ∧ BD s words u₀ i L Hb st g D C H1 U k m v) ∨
      (v.pc = 0x800009a4 ∧ BP s words u₀ i L Hb st g D C H1 U k m v)) := by
  have ub := h.ub
  have hm := h.hm
  have hsp := ub.rc.k.ng.sp
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000974_spec hpc (by rv_eval [hsp, msp]; decide)
  have k₁ := b80000974_keeps h₁
  have hf₁ := holds_slots h₁ hsp [128] (by decide) (by decide)
  have ub₁ := ub.slots hf₁ (fun a ⟨c, hc, hin⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; addr_omega [hin]) (regs8 k₁ (by decide))
  have hpc₁ := b80000974_pc_not_taken h₁ (by rw [h.x10]; exact shr59 m hm)
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches NB.g80000988_spec hpc₁ trivial
  have k₂ := NB.g80000988_keeps h₂
  have hm₂ := NB.g80000988_mem_same h₂
  have hbl := (wbyte g k m).isLt
  have hct := wbucket_toNat (g := g) (k := k) hm
  obtain ⟨e1, e2⟩ := bucket_all m hm (wbyte g k m).toNat hbl
  have x10₁ : t₁.getReg .x10 = BitVec.ofNat 64 m := (k₁ .x10 (by decide)).trans h.x10
  have x11₁ : t₁.getReg .x11 = BitVec.ofNat 64 (wbyte g k m).toNat := (k₁ .x11 (by decide)).trans h.x11
  have x10₂ : t₂.getReg .x10 = BitVec.ofNat 64 (U + (wbucket g k m).toNat) := by
    rw [NB.g80000988_x10 h₂, x10₁, x11₁, e2, k₁ .x18 (by decide), ub.x18, ← BitVec.ofNat_add, hct]
  have x21₂ : t₂.getReg .x21 = BitVec.ofNat 64 (wbucket g k m).toNat := by
    rw [NB.g80000988_x21 h₂, x10₁, x11₁, e1, hct]
  -- `0x8000099c`: `used[bucket]`
  have hU1 := ub₁.hU1
  have hU2 := ub₁.hU2
  have hhi := ub₁.rc.k.ng.heap.hi
  have hh1 := ub₁.rc.h1
  have hb0 := ub₁.rc.k.hb0
  have hl0 := ub₁.rc.k.a.inv.heap.lo
  have hdlo := ub₁.rc.dlo
  have hdc := ub₁.rc.dc
  have hchi := ub₁.rc.chi
  simp only [heapNext, heapEnd, heapStart] at hU2 hhi hh1 hb0 hl0
  obtain ⟨t₃, r₃, hpc₃, hr₃, hm₃⟩ := step_lbu (code := Image.code) (s := t₂) (rd := .x11)
    (rs1 := .x10) (off := 0) (by rw [NB.g80000988_pc h₂]; exact fetch_of (by decide +kernel))
    (by rw [off0, x10₂]; exact validMem_of (Or.inl (by constructor <;>
      addr_omega [hct, hm, hbl, hU1, hU2, hhi, hh1, hb0, hl0, hdlo, hdc, hchi])))
  rw [off0, x10₂] at hr₃
  have hu : byteAt t₂ (BitVec.ofNat 64 (U + (wbucket g k m).toNat)) =
      if (bfold g st k m).1.getD (wbucket g k m).toNat false then 1 else 0 := by
    have e : byteAt t₂ (BitVec.ofNat 64 (U + (wbucket g k m).toNat)) =
        byteAt t₁ (BitVec.ofNat 64 (U + (wbucket g k m).toNat)) := by
      rw [byteAt_eq, byteAt_eq, hm₂]
    rw [e]
    exact ub₁.used _ (by omega)
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches NB.g800009a0_spec (by
    rw [hpc₃, NB.g80000988_pc h₂]; rfl) trivial
  have kv := NB.g800009a0_keeps hv
  have hmv := NB.g800009a0_mem_same hv
  have R₃ : ∀ r, r ≠ .x11 → t₃.getReg r = t₂.getReg r := fun r hr ↦ by rw [hr₃]; simp [hr]
  have hm1v : ∀ a, v.getMem a = t₁.getMem a := fun a ↦ by rw [hmv, hm₃, hm₂]
  have R : ∀ r ∈ ([.x2, .x8, .x9, .x15, .x18, .x19, .x20, .x23, .x24, .x25, .x26, .x27] : List Reg),
      v.getReg r = t₁.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (kv _ (by decide)).trans ((R₃ _ (by decide)).trans (k₂ _ (by decide)))
  have ubv := ub₁.same hm1v fun r hr ↦ R r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have wv : v.getMem (msp + 120) = g.2.2.getD k 0 := by
    rw [hm1v, ← h.w]
    exact hf₁.getMem (by decide) fun j hj ⟨c, hc, hin⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; addr_omega [hin, hj]
  have x19v : v.getReg .x19 = BitVec.ofNat 64 (m + 1) := by
    rw [R .x19 (by simp), b80000974_x19 h₁, h.x10, BitVec.ofNat_add]; rfl
  have x20v : v.getReg .x20 = BitVec.ofNat 64 (m + 1) := by
    rw [R .x20 (by simp), k₁ .x20 (by decide), h.x20]
  have x15v : v.getReg .x15 = 8 := by rw [R .x15 (by simp), k₁ .x15 (by decide), h.x15]
  have x23v : v.getReg .x23 = D + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [R .x23 (by simp), k₁ .x23 (by decide), h.x23]
  have rv' : Reaches Image.code t v :=
    r₁.trans (r₂.trans ((show Reaches Image.code t₂ t₃ from ⟨1, r₃⟩).trans rv))
  have x11₃ : t₃.getReg .x11 = (byteAt t₂ (BitVec.ofNat 64 (U + (wbucket g k m).toNat))).zeroExtend 64 := by
    rw [hr₃]; simp
  by_cases hus : (bfold g st k m).1.getD (wbucket g k m).toNat false = true
  · have e : bfold g st k (m + 1) = bfold g st k m := by
      rw [bfold_nz h.nz, Model.usedStep, hus]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [← e] at ubv
    exact ⟨v, rv', Or.inr (Or.inl ⟨NB.g800009a0_pc_taken hv (by rw [x11₃, hu, hus]; decide),
      ubv, h.hk, hm, wv, x15v, x19v, x20v, x23v⟩)⟩
  · have hf : (bfold g st k m).1.getD (wbucket g k m).toNat false = false := by simpa using hus
    refine ⟨v, rv', Or.inr (Or.inr ⟨NB.g800009a0_pc_not_taken hv (by rw [x11₃, hu, hf]; decide),
      ubv, h.hk, hm, wv, h.nz, hf, ?_, x15v, x19v, x20v, ?_, x23v⟩)⟩
    · rw [kv .x10 (by decide), R₃ _ (by decide), x10₂]
    · rw [kv .x21 (by decide), R₃ _ (by decide), x21₂]

end

/-- At `0x80000910`, byte `m`'s bucket marked `used`, room in `bytes` for it. -/
structure BQ (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C : Word) (H1 U k m : Nat) (t : MachineState) : Prop where
  ub : UB s words u₀ i L Hb st g D C H1 U
    (((bfold g st k m).1.set (wbucket g k m).toNat true, (bfold g st k m).2)) t
  hk : k < g.2.2.length
  hm : m < 8
  w : t.getMem (msp + 120) = g.2.2.getD k 0
  nz : wbyte g k m ≠ 0
  fresh : (bfold g st k m).1.getD (wbucket g k m).toNat false = false
  room : (vecLen t (msp + 240)).toNat < (vecCap t (msp + 240)).toNat
  x15 : t.getReg .x15 = 8
  x19 : t.getReg .x19 = BitVec.ofNat 64 (m + 1)
  x20 : t.getReg .x20 = BitVec.ofNat 64 (m + 1)
  x21 : t.getReg .x21 = BitVec.ofNat 64 (wbucket g k m).toNat
  x22 : t.getReg .x22 = vecLen t (msp + 240)
  x23 : t.getReg .x23 = D + BitVec.ofNat 64 (8 * (k + 1))

section
variable {s u₀ t t' : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C : Word} {H1 U : Nat} {u : List Bool × List (BitVec 16)}

/-- One byte of `used` set. -/
theorem UB.mark (h : UB s words u₀ i L Hb st g D C H1 U u t) {c : Nat} (hc : c < 2048)
    (hf : BFrame t t' fun a ↦ a = BitVec.ofNat 64 (U + c)) (hb : byteAt t' (BitVec.ofNat 64 (U + c)) = 1)
    (hr : ∀ r ∈ ([.x2, .x8, .x9, .x18, .x24, .x25, .x26, .x27] : List Reg), t'.getReg r = t.getReg r) :
    UB s words u₀ i L Hb st g D C H1 U ((u.1.set c true, u.2)) t' := by
  have hU1 := h.hU1
  have hU2 := h.hU2
  have hhi := h.rc.k.ng.heap.hi
  have hh1 := h.rc.h1
  have hdc := h.rc.dc
  have hchi := h.rc.chi
  have hdlo := h.rc.dlo
  have hb0 := h.rc.k.hb0
  have hl0 := h.rc.k.a.inv.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hU2 hhi hh1 hb0 hl0
  have hn : heapNext t' = heapNext t := by
    simp only [heapNext]
    rw [hf.getMem (a := nextAddr) (by decide) fun j hj hw ↦ by
      have := congrArg BitVec.toNat hw; addr_omega [this, hj, hc, hU2, hhi]]
  have hsp : t'.getReg .x2 = msp := (hr .x2 (by simp)).trans h.rc.k.ng.sp
  have hheap : HeapOk t' := ⟨by rw [hn]; exact h.rc.k.ng.heap.lo, by rw [hn]; exact h.rc.k.ng.heap.hi⟩
  refine ⟨h.rc.frame hf (fun a ha ↦ ?_) hsp hheap (le_of_eq hn.symm), ?_,
    h.vs.frame hf (fun a ha ↦ ?_) (le_of_eq hn.symm) hheap.hi, fun b hb' ↦ ?_,
    by rw [List.length_set]; exact h.ulen, hU1, by rw [hn]; exact h.hU2,
    (hr .x8 (by simp)).trans h.x8, (hr .x9 (by simp)).trans h.x9,
    (hr .x18 (by simp)).trans h.x18, (hr .x24 (by simp)).trans h.x24,
    (hr .x25 (by simp)).trans h.x25, (hr .x26 (by simp)).trans h.x26,
    (hr .x27 (by simp)).trans h.x27⟩
  · subst ha
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
    · simp only [heapNext]; addr_omega [hc, hU1, hU2, hhi, hh1, hdc, hchi, hdlo, hb0]
    · simp only [heapEnd]; addr_omega [hc, hU2, hhi]
    · intro h'; addr_omega [h', hc, hU1, hU2, hhi, hh1, hdc, hchi]
    · intro h'; addr_omega [h', hc, hU1, hU2, hhi, hh1, hchi]
  · rw [← h.m24]
    exact hf.getMem (by decide) fun j hj hw ↦ by
      have := congrArg BitVec.toNat hw; addr_omega [this, hj, hc, hU2, hhi]
  · subst ha
    exact ⟨by addr_omega [hc, hU2, hhi], by addr_omega [hc, hU2, hhi],
      Or.inr (Or.inr (Or.inr ⟨by addr_omega [hc, hU2, hhi], by addr_omega [hc, hU2, hhi]⟩))⟩
  · by_cases hbc : b = c
    · subst hbc
      rw [hb, List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [h.ulen]; exact hb')]
      rfl
    · rw [hf _ fun hw ↦ hbc (by have := congrArg BitVec.toNat hw; addr_omega [this, hb', hc, hU2, hhi]),
        h.used b hb', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (Ne.symm hbc)]

end

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C : Word} {H1 U k m : Nat}

/-- `0x800009a4`: the bucket marked `used`; `bytes` grown if full (`grow_one`). -/
theorem bytes_mark (h : BP s words u₀ i L Hb st g D C H1 U k m t) (hpc : t.pc = 0x800009a4) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x80000910 ∧ BQ s words u₀ i L Hb st g D C H1 U k m v)) := by
  have ub := h.ub
  have hm := h.hm
  have hsp := ub.rc.k.ng.sp
  have hct := wbucket_toNat (g := g) (k := k) hm
  have hbl := (wbyte g k m).isLt
  have hc : (wbucket g k m).toNat < 2048 := by omega
  have hU1 := ub.hU1
  have hU2 := ub.hU2
  have hhi := ub.rc.k.ng.heap.hi
  have hh1 := ub.rc.h1
  have hb0 := ub.rc.k.hb0
  have hl0 := ub.rc.k.a.inv.heap.lo
  have hdlo := ub.rc.dlo
  have hdc := ub.rc.dc
  have hchi := ub.rc.chi
  simp only [heapNext, heapEnd, heapStart] at hU2 hhi hh1 hb0 hl0
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches NB.g800009a4_spec hpc (by rv_eval [hsp, msp]; decide)
  have k₁ := NB.g800009a4_keeps h₁
  have hm₁ := NB.g800009a4_mem_same h₁
  have x10₁ : t₁.getReg .x10 = BitVec.ofNat 64 (U + (wbucket g k m).toNat) :=
    (k₁ .x10 (by decide)).trans h.x10
  -- `0x800009ac`: `used[bucket] = true`
  obtain ⟨t₂, r₂, hpc₂, hr₂, hb₂, -⟩ := step_sb (code := Image.code) (s := t₁) (rs1 := .x10)
    (rs2 := .x27) (off := 0) (by rw [NB.g800009a4_pc h₁]; exact fetch_of (by decide +kernel))
    (by rw [off0, x10₁]; exact validMem_of (Or.inl (by constructor <;>
      addr_omega [hc, hU1, hU2, hhi, hh1, hb0, hl0, hdlo, hdc, hchi])))
  rw [off0, x10₁, k₁ .x27 (by decide), ub.x27] at hb₂
  have ub₂ := ub.mark hc (t' := t₂) (fun a ha ↦ by
      rw [hb₂ a]; simp only [ha, ↓reduceIte]; rw [byteAt_eq, byteAt_eq, hm₁])
    (by rw [hb₂]; simp only [↓reduceIte]; rfl) (fun r hr ↦ by rw [hr₂ r]; exact k₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  have hK : ∀ c' : Nat, c' % 8 = 0 → c' < 4096 →
      t₂.getMem (msp + BitVec.ofNat 64 c') = t.getMem (msp + BitVec.ofNat 64 c') := fun c' h8 hc' ↦
    getMem_eq_of_bytes (by addr_omega [h8, hc']) (by addr_omega [h8, hc']) fun j hj ↦ by
      show byteAt t₂ (msp + BitVec.ofNat 64 c' + BitVec.ofNat 64 j) =
        byteAt t (msp + BitVec.ofNat 64 c' + BitVec.ofNat 64 j)
      rw [hb₂]
      have hne : ¬ (msp + BitVec.ofNat 64 c' + BitVec.ofNat 64 j =
          BitVec.ofNat 64 (U + (wbucket g k m).toNat)) := fun e ↦ by
        have := congrArg BitVec.toNat e; addr_omega [this, hj, hc', hc, hU2, hhi]
      simp only [hne, ↓reduceIte]
      rw [byteAt_eq, byteAt_eq, hm₁]
  have hn2 : heapNext t₂ = heapNext t := by
    simp only [heapNext]
    rw [getMem_eq_of_bytes (s := t) (t := t₂) (a := nextAddr) (b := nextAddr) (by decide) (by decide)
      fun j hj ↦ by
      show byteAt t₂ (nextAddr + BitVec.ofNat 64 j) = byteAt t (nextAddr + BitVec.ofNat 64 j)
      rw [hb₂]
      have hne : ¬ (nextAddr + BitVec.ofNat 64 j = BitVec.ofNat 64 (U + (wbucket g k m).toNat)) :=
        fun e ↦ by have := congrArg BitVec.toNat e; addr_omega [this, hj, hc, hU2, hhi]
      simp only [hne, ↓reduceIte]
      rw [byteAt_eq, byteAt_eq, hm₁]]
  have l2 : vecLen t₂ (msp + 240) = vecLen t (msp + 240) := hK 256 (by decide) (by decide)
  have c2 : vecCap t₂ (msp + 240) = vecCap t (msp + 240) := hK 240 (by decide) (by decide)
  have p2 : vecPtr t₂ (msp + 240) = vecPtr t (msp + 240) := hK 248 (by decide) (by decide)
  have x11₂ : t₂.getReg .x11 = vecCap t (msp + 240) := by
    rw [hr₂, NB.g800009a4_x11 h₁, hsp]; rfl
  have x22₂ : t₂.getReg .x22 = vecLen t (msp + 240) := by
    rw [hr₂, NB.g800009a4_x22 h₁, hsp]; rfl
  have R₂ : ∀ r ∈ ([.x15, .x19, .x20, .x21, .x23] : List Reg), t₂.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact (hr₂ _).trans (k₁ _ (by decide))
  have w₂ : t₂.getMem (msp + 120) = g.2.2.getD k 0 := (hK 120 (by decide) (by decide)).trans h.w
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches NB.g800009b0_spec (by
    rw [hpc₂, NB.g800009a4_pc h₁]; rfl) trivial
  have k₃ := NB.g800009b0_keeps h₃
  have hm₃ := NB.g800009b0_mem_same h₃
  have ub₃ := ub₂.same hm₃ (ub_regs k₃)
  have hlc := ub.vs.bufs.y.len
  have r₀₃ : Reaches Image.code t t₃ :=
    r₁.trans ((show Reaches Image.code t₁ t₂ from ⟨1, r₂⟩).trans r₃)
  by_cases hfull : vecLen t (msp + 240) = vecCap t (msp + 240)
  swap
  · refine ⟨t₃, r₀₃, Or.inr ⟨NB.g800009b0_pc_taken h₃ (by rw [x22₂, x11₂]; exact hfull), ub₃, h.hk,
      hm, by rw [hm₃]; exact w₂, h.nz, h.fresh, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · show (t₃.getMem (msp + 240 + 16)).toNat < (t₃.getMem (msp + 240)).toNat
      rw [hm₃, hm₃]
      show (vecLen t₂ (msp + 240)).toNat < (vecCap t₂ (msp + 240)).toNat
      rw [l2, c2]
      exact lt_of_le_of_ne hlc fun e ↦ hfull (BitVec.eq_of_toNat_eq e)
    · rw [k₃ .x15 (by decide), R₂ .x15 (by simp)]; exact h.x15
    · rw [k₃ .x19 (by decide), R₂ .x19 (by simp)]; exact h.x19
    · rw [k₃ .x20 (by decide), R₂ .x20 (by simp)]; exact h.x20
    · rw [k₃ .x21 (by decide), R₂ .x21 (by simp)]; exact h.x21
    · rw [k₃ .x22 (by decide), x22₂, ← l2]; exact (hm₃ _).symm
    · rw [k₃ .x23 (by decide), R₂ .x23 (by simp)]; exact h.x23
  -- `0x800009b4`: `grow_one`
  have hpc₃ := NB.g800009b0_pc_not_taken h₃ (by rw [x22₂, x11₂]; exact hfull)
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b800009b4_spec hpc₃ trivial
  have k₄ := b800009b4_keeps h₄
  have hm₄ := b800009b4_mem_same h₄
  have hsp₃ : t₃.getReg .x2 = msp := ub₃.rc.k.ng.sp
  have hsp₄ : t₄.getReg .x2 = msp := (k₄ .x2 (by decide)).trans hsp₃
  have x10₄ : t₄.getReg .x10 = msp + 240 := by rw [b800009b4_x10 h₄, hsp₃]
  have hm42 : ∀ a, t₄.getMem a = t₂.getMem a := fun a ↦ by rw [hm₄, hm₃]
  have hn₄ : heapNext t₄ = heapNext t₂ := by simp only [heapNext, hm42]
  have p4 : vecPtr t₄ (msp + 240) = vecPtr t (msp + 240) := (hm42 _).trans p2
  have c4 : vecCap t₄ (msp + 240) = vecCap t (msp + 240) := (hm42 _).trans c2
  have by' := ub.vs.bufs.y
  have pre : GrowOnePre 2 2 t₄ := {
    heap := ⟨by rw [hn₄]; exact ub₂.rc.k.ng.heap.lo, by rw [hn₄]; exact ub₂.rc.k.ng.heap.hi⟩
    self := by rw [x10₄]; exact validRange_of (by decide) (by decide) (by decide)
    raw := by
      rw [x10₄]
      simp only [RawVecOk, Buf, p4, c4]
      refine ⟨by'.al, by'.buf.imp_right fun hb' ↦ ⟨?_, ?_⟩⟩
      · simp only [heapStart, heapNext] at hb' ⊢; omega
      · rw [hn₄, hn2]; exact hb'.2
    stack := rtStack_msp hsp₄ (by decide) (by decide)
    selfFree := by
      rw [x10₄]
      exact ⟨Or.inr (by simp only [heapEnd]; decide), by addr_omega []⟩
    selfStack := by rw [x10₄]; simp only [stackLo, hsp₄, growOneStack]; addr_omega [] }
  obtain ⟨t₅, r₅, ⟨hpc₅, hpv, post, hfresh⟩ | hd⟩ :=
    growOneFresh_80011f88.call r₄ (b800009b4_pc h₄) pre
  swap
  · exact ⟨t₅, r₀₃.trans r₅, Or.inl hd⟩
  have hpc₅' : t₅.pc = 0x800009c0 := by rw [hpc₅, returnAddress, b800009b4_x1 h₄]; decide
  have hsp₅ : t₅.getReg .x2 = msp := (hpv.reg .x2).trans hsp₄
  obtain ⟨t₆, r₆, h₆⟩ := Sym.BlockSpec.reaches b800009c0_spec hpc₅' trivial
  have k₆ := b800009c0_keeps h₆
  have hm₆ := b800009c0_mem_same h₆
  have hsp₆ : t₆.getReg .x2 = msp := (k₆ .x2 (by decide)).trans hsp₅
  have pf := post.frame
  have pcap := post.cap
  have pby := post.bytes
  rw [x10₄] at pf pcap pby hfresh
  have hhi₅ := post.heap.hi
  have hmo₅ := post.mono
  simp only [heapNext, heapEnd] at hhi₅ hmo₅
  have hn42 := hn₄
  simp only [heapNext] at hn42
  have hf : BFrame t₃ t₆ fun a ↦ Within a (msp + 240) 16 ∨
      Within a (stackLo t₄ growOneStack) growOneStack ∨ Within a nextAddr 8 ∨ Fresh t₄ t₅ a :=
    fun a ha ↦ by
      rw [byteAt_eq, byteAt_eq, hm₆, ← hm₄, ← byteAt_eq, ← byteAt_eq]
      exact pf.byte a ha
  have hn₆ : heapNext t₆ = heapNext t₅ := by simp only [heapNext, hm₆]
  have hheap₆ : HeapOk t₆ := ⟨by rw [hn₆]; exact post.heap.lo, by rw [hn₆]; exact post.heap.hi⟩
  have hn3 : heapNext t₃ = heapNext t := by
    rw [← hn2]; simp only [heapNext, hm₃]
  have hmono : heapNext t₃ ≤ heapNext t₆ := by
    rw [hn₆]; simp only [heapNext] at hmo₅ ⊢; rw [← hm₄]; exact hmo₅
  have hU2' := ub₃.hU2
  have hhi3 := ub₃.rc.k.ng.heap.hi
  simp only [heapNext, heapEnd] at hU2' hhi3
  have hW : ∀ a, (Within a (msp + 240) 16 ∨ Within a (stackLo t₄ growOneStack) growOneStack ∨
      Within a nextAddr 8 ∨ Fresh t₄ t₅ a) →
      Wr (heapNext u₀) D C g.2.2.length a ∧ ¬ (U ≤ a.toNat ∧ a.toNat < U + 2048) ∧
        ¬ Within a (msp + 400) 24 ∧ ¬ Within a (msp + 424) 24 ∧ ¬ Within a (msp + 448) 24 ∧
        (a.toNat < heapNext u₀ ∨ heapNext t₃ ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
          (U ≤ a.toNat ∧ a.toNat < U + 2048) ∨
          Within a (vecPtr t₃ (msp + 240)) ((vecCap t₃ (msp + 240)).toNat * 2)) := by
    intro a ha
    simp only [heapNext]
    rcases ha with ha | ha | ha | ⟨ha1, ha2⟩
    · exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [ha]))), by addr_omega [ha, hU2', hhi3], by addr_omega [ha],
        by addr_omega [ha], by addr_omega [ha], Or.inr (Or.inl (by addr_omega [ha, hU2', hhi3]))⟩
    · simp only [stackLo, hsp₄, growOneStack] at ha
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha]))))), by addr_omega [ha, hU2', hhi3],
        by addr_omega [ha], by addr_omega [ha], by addr_omega [ha],
        Or.inr (Or.inl (by addr_omega [ha, hU2', hhi3]))⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))), by addr_omega [ha, hU2', hhi3],
        by addr_omega [ha], by addr_omega [ha], by addr_omega [ha],
        Or.inr (Or.inl (by addr_omega [ha, hU2', hhi3]))⟩
    · simp only [heapNext] at ha1 ha2
      rw [hn42] at ha1
      have h3 : (t₃.getMem nextAddr).toNat = (t₂.getMem nextAddr).toNat := by rw [hm₃]
      have := ub₃.rc.k.ng.mono
      simp only [heapNext] at this
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapEnd]; omega,
        fun h' ↦ by addr_omega [h', ha1, hU2', h3, hU1, hdc, hchi, hh1],
        fun h' ↦ by addr_omega [h', ha1, hU2', h3, hU1, hchi, hh1]⟩))))), by omega,
        by addr_omega [ha2, hhi₅], by addr_omega [ha2, hhi₅], by addr_omega [ha2, hhi₅],
        Or.inr (Or.inl (by omega))⟩
  have hK6 : ∀ c' : Nat, c' % 8 = 0 → c' < 4096 → (c' + 8 ≤ 240 ∨ 256 ≤ c') →
      t₆.getMem (msp + BitVec.ofNat 64 c') = t₃.getMem (msp + BitVec.ofNat 64 c') := fun c' h8 hc' hr ↦
    hf.getMem (by addr_omega [h8, hc']) fun j hj hw ↦ by
      rcases hw with hw | hw | hw | ⟨hw1, hw2⟩
      · rcases hr with hr | hr <;> addr_omega [hw, hj, hc', hr]
      · simp only [stackLo, hsp₄, growOneStack] at hw; addr_omega [hw, hj, hc']
      · addr_omega [hw, hj, hc']
      · simp only [heapNext] at hw2; addr_omega [hw2, hj, hc', hhi₅]
  have l6 : vecLen t₆ (msp + 240) = vecLen t₃ (msp + 240) := hK6 256 (by decide) (by decide) (by omega)
  have p6 : vecPtr t₆ (msp + 240) = vecPtr t₅ (msp + 240) := hm₆ _
  have c6 : vecCap t₆ (msp + 240) = vecCap t₅ (msp + 240) := hm₆ _
  have l3 : vecLen t₃ (msp + 240) = vecLen t (msp + 240) := (hm₃ _).trans l2
  have c3' : vecCap t₄ (msp + 240) = vecCap t (msp + 240) := c4
  rw [c3'] at pcap
  rw [p4, c4] at pby
  have hlc' : (vecLen t (msp + 240)).toNat = (vecCap t (msp + 240)).toNat := by rw [hfull]
  have hroom : (vecLen t₆ (msp + 240)).toNat < (vecCap t₆ (msp + 240)).toNat := by
    rw [l6, l3, c6]; omega
  have hn43 : heapNext t₄ = heapNext t₃ := by simp only [heapNext, hm₄]
  have hlo0 := ub₃.rc.k.a.inv.heap.lo
  have hmo0 := ub₃.rc.k.ng.mono
  simp only [heapNext, heapStart] at hlo0 hmo0
  have hy := ub₃.vs.vecs.bytes
  simp only at hy
  have hin : VecIn t₆ (msp + 240) 2 2 (heapNext u₀) (heapNext t₆) := by
    refine ⟨le_of_lt hroom, by rw [p6]; exact hfresh.1, ?_, fun h0 ↦ absurd h0 (by omega)⟩
    rw [p6, c6, hn₆]
    rcases hfresh.2 with h0 | ⟨h1, h2⟩
    · exact Or.inl h0
    · right; rw [hn43] at h1; simp only [heapNext] at h1 h2 ⊢; omega
  have vs₆ := ub₃.vs.setY (l := (bfold g st k m).2) hf (fun a ha ↦ (hW a ha).2.2) hmono hheap₆.hi hin
    (by
      simp only [VMiss, p6, c6]
      rcases hfresh.2 with h0 | ⟨h1, _⟩
      · exact ⟨Or.inl h0, Or.inl h0⟩
      · rw [hn43] at h1
        simp only [heapNext] at h1
        exact ⟨Or.inr (Or.inr (Or.inl (by omega))), Or.inr (Or.inr (Or.inl (by omega)))⟩)
    (by
      rw [p6, c6]
      rcases hfresh.2 with h0 | ⟨h1, _⟩
      · exact Or.inr (Or.inl h0)
      · rw [hn43] at h1; exact Or.inr (Or.inr h1))
    (by
      rw [p6, l6, l3]
      have e1 : halvesAt t₆ (vecPtr t₅ (msp + 240)) (vecLen t (msp + 240)).toNat =
          halvesAt t₅ (vecPtr t₅ (msp + 240)) (vecLen t (msp + 240)).toNat := by
        simp only [halvesAt, getHalfword_same hm₆]
      have e2 : halvesAt t₄ (vecPtr t (msp + 240)) (vecLen t (msp + 240)).toNat =
          halvesAt t₃ (vecPtr t₃ (msp + 240)) (vecLen t₃ (msp + 240)).toNat := by
        rw [l3, show vecPtr t₃ (msp + 240) = vecPtr t (msp + 240) from (hm₃ _).trans p2]
        simp only [halvesAt, getHalfword_same hm₄]
      rw [e1, halvesAt_of_bytes pby (by omega) hfresh.1 by'.al ?_ ?_, e2, hy]
      · rcases hfresh.2 with h0 | ⟨_, h2⟩
        · omega
        · simp only [heapNext] at h2; omega
      · rcases by'.buf with h0 | ⟨_, h2⟩
        · omega
        · simp only [heapNext] at h2; omega)
  have R : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
      t₆.getReg r = t₃.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₆ _ (by decide)).trans ((hpv.reg _ (by decide)).trans (k₄ _ (by decide)))
  have hU2₃ := ub₃.hU2
  refine ⟨t₆, r₀₃.trans (r₅.trans r₆), Or.inr ⟨b800009c0_pc h₆,
    ⟨ub₃.rc.frame hf (fun a ha ↦ (hW a ha).1) hsp₆ hheap₆ hmono,
      (hK6 24 (by decide) (by decide) (by omega)).trans ub₃.m24, vs₆, fun b hb ↦ ?_, ub₃.ulen,
      ub₃.hU1, le_trans hU2₃ hmono, (R .x8 (by simp)).trans ub₃.x8, (R .x9 (by simp)).trans ub₃.x9,
      (R .x18 (by simp)).trans ub₃.x18, (R .x24 (by simp)).trans ub₃.x24,
      (R .x25 (by simp)).trans ub₃.x25, (R .x26 (by simp)).trans ub₃.x26,
      (R .x27 (by simp)).trans ub₃.x27⟩, h.hk, hm,
    (hK6 120 (by decide) (by decide) (by omega)).trans ((hm₃ _).trans w₂), h.nz, h.fresh, hroom,
    b800009c0_x15 h₆, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hf _ fun hw ↦ (hW _ hw).2.1 ⟨by addr_omega [hb, hU2', hhi3], by addr_omega [hb, hU2', hhi3]⟩]
    exact ub₃.used b hb
  · rw [R .x19 (by simp), k₃ .x19 (by decide), R₂ .x19 (by simp)]; exact h.x19
  · rw [R .x20 (by simp), k₃ .x20 (by decide), R₂ .x20 (by simp)]; exact h.x20
  · rw [R .x21 (by simp), k₃ .x21 (by decide), R₂ .x21 (by simp)]; exact h.x21
  · rw [R .x22 (by simp), k₃ .x22 (by decide), x22₂, l6, l3]
  · rw [R .x23 (by simp), k₃ .x23 (by decide), R₂ .x23 (by simp)]; exact h.x23

end

/-- `n` `u16`s from `p` and one more. -/
theorem halvesAt_snoc {t t' : MachineState} {p : Word} {n : Nat} {v : BitVec 16}
    (hp : p.toNat % 2 = 0) (hb : p.toNat + 2 * (n + 1) < 2 ^ 64)
    (hk : ∀ x : Word, p.toNat ≤ x.toNat → x.toNat < p.toNat + 2 * n → byteAt t' x = byteAt t x)
    (hv : t'.getHalfword (p + BitVec.ofNat 64 (2 * n)) = v) :
    halvesAt t' p (n + 1) = halvesAt t p n ++ [v] := by
  unfold halvesAt
  rw [List.range_succ, List.map_append, List.map_singleton, hv]
  congr 1
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  exact getHalfword_eq_of_bytes (by addr_omega [hp, hb, hj])
    (hk _ (by addr_omega [hb, hj]) (by addr_omega [hb, hj]))
    (hk _ (by addr_omega [hb, hj]) (by addr_omega [hb, hj]))

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C : Word} {H1 U k m : Nat}

/-- `0x80000910`: the bucket pushed onto `bytes`, to `0x80000928`. -/
theorem bytes_push (h : BQ s words u₀ i L Hb st g D C H1 U k m t) (hpc : t.pc = 0x80000910) :
    ∃ v, Reaches Image.code t v ∧ v.pc = 0x80000928 ∧ BD s words u₀ i L Hb st g D C H1 U k m v := by
  have ub := h.ub
  have hm := h.hm
  have hsp := ub.rc.k.ng.sp
  have hhi := ub.rc.k.ng.heap.hi
  have hU1 := ub.hU1
  have hU2 := ub.hU2
  have hh1 := ub.rc.h1
  have hdc := ub.rc.dc
  have hchi := ub.rc.chi
  have hdlo := ub.rc.dlo
  simp only [heapNext, heapEnd] at hhi hU2 hh1
  have by' := ub.vs.bufs.y
  have my := ub.vs.my
  have hroom := h.room
  obtain ⟨hP1, hP2⟩ := by'.buf.resolve_left (by omega)
  simp only [heapNext] at hP1 hP2
  have hpal := by'.al
  have hP : vecPtr t (msp + 240) = t.getMem (msp + 248) := rfl
  rw [hP] at hP1 hP2 hpal
  simp only [VMiss, Out] at my
  rw [hP] at my
  have hlo0 := ub.rc.k.a.inv.heap.lo
  simp only [heapStart, heapNext] at hlo0
  have hm16 : (vecLen t (msp + 240)).toNat * 2 + 2 ≤ (vecCap t (msp + 240)).toNat * 2 := by omega
  have hE : (t.getMem (msp + 248) + BitVec.ofNat 64 (2 * (vecLen t (msp + 240)).toNat)).toNat =
      (t.getMem (msp + 248)).toNat + 2 * (vecLen t (msp + 240)).toNat := by
    addr_omega [hP2, hm16, hhi]
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches NB.g80000910_spec hpc (by rv_eval [hsp, msp]; decide)
  have k₁ := NB.g80000910_keeps h₁
  have hm₁ := NB.g80000910_mem_same h₁
  have x10₁ : t₁.getReg .x10 = t.getMem (msp + 248) + BitVec.ofNat 64 (2 * (vecLen t (msp + 240)).toNat) := by
    rw [NB.g80000910_x10 h₁, hsp, h.x22]
    apply BitVec.eq_of_toNat_eq
    rw [hE]
    addr_omega [hP2, hm16, hhi]
  -- `0x80000920`: `bytes[len] = bucket`
  have hf₁ : Image.code.fetch t₁.pc = some (.base (.SH .x10 .x21 0)) := by
    rw [NB.g80000910_pc h₁]; exact fetch_of (by decide +kernel)
  obtain ⟨t₂, r₂, hpc₂, hr₂, hh₂, hfr₂⟩ := step_sh hf₁ (by
    rw [off0, x10₁]
    exact valid2_of (by addr_omega [hE, hP1, hlo0]) (by addr_omega [hE, hP2, hm16, hhi])
      (by addr_omega [hE, hpal]))
  rw [off0, x10₁] at hh₂ hfr₂
  rw [k₁ .x21 (by decide), h.x21, setWidth16_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hh₂
  -- `0x80000924`: `bytes.len += 1`
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches NB.g80000924_spec (by
    rw [hpc₂, NB.g80000910_pc h₁]; rfl) (by rv_eval [hr₂, k₁ .x2 (by decide), hsp, msp]; decide)
  have k₃ := NB.g80000924_keeps h₃
  have hsp₂ : t₂.getReg .x2 = msp := by rw [hr₂, k₁ .x2 (by decide), hsp]
  have hf₃ : BFrame t₂ t₃ (Within · (msp + 256) 8) := by
    have e := BFrame.of_memFrame (NB.g80000924_frame h₃ (by rw [hsp₂]; decide)) (by rw [hsp₂]; decide)
      (by decide)
    rw [hsp₂] at e
    exact e
  have hf : BFrame t t₃ fun a ↦ Within a (t.getMem (msp + 248) +
      BitVec.ofNat 64 (2 * (vecLen t (msp + 240)).toNat)) 2 ∨ Within a (msp + 256) 8 := fun a ha ↦ by
    rw [hf₃ a fun h' ↦ ha (Or.inr h'), hfr₂.byte a fun h' ↦ ha (Or.inl (by
      rcases h' with h' | h' <;> rw [h'] <;> addr_omega [hE, hP2, hm16, hhi])),
      byteAt_eq, byteAt_eq, hm₁]
  have hW : ∀ a, (Within a (t.getMem (msp + 248) +
      BitVec.ofNat 64 (2 * (vecLen t (msp + 240)).toNat)) 2 ∨ Within a (msp + 256) 8) →
      Wr (heapNext u₀) D C g.2.2.length a ∧ ¬ (U ≤ a.toNat ∧ a.toNat < U + 2048) ∧
        ¬ Within a (msp + 400) 24 ∧ ¬ Within a (msp + 424) 24 ∧ ¬ Within a (msp + 448) 24 ∧
        (a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
          (U ≤ a.toNat ∧ a.toNat < U + 2048) ∨
          Within a (vecPtr t (msp + 240)) ((vecCap t (msp + 240)).toNat * 2)) := by
    intro a ha
    simp only [heapNext]
    rcases ha with ha | ha
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hE, hP1],
        by simp only [heapEnd]; addr_omega [ha, hE, hP2, hm16, hhi],
        fun h' ↦ by addr_omega [h', ha, hE, my, hP2, hm16, hdlo, hdc, hchi],
        fun h' ↦ by addr_omega [h', ha, hE, my, hP2, hm16, hdlo, hdc, hchi]⟩))))),
        fun h' ↦ by addr_omega [h', ha, hE, my, hP2, hm16],
        by addr_omega [ha, hE, hP2, hm16, hhi], by addr_omega [ha, hE, hP2, hm16, hhi],
        by addr_omega [ha, hE, hP2, hm16, hhi],
        Or.inr (Or.inr (Or.inr (Or.inr (by rw [hP]; addr_omega [ha, hE, hP2, hm16]))))⟩
    · exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [ha]))), by addr_omega [ha, hU2, hhi],
        by addr_omega [ha], by addr_omega [ha], by addr_omega [ha],
        Or.inr (Or.inl (by addr_omega [ha, hhi]))⟩
  have hK3 : ∀ c' : Nat, c' % 8 = 0 → c' < 4096 → (c' + 8 ≤ 256 ∨ 264 ≤ c') →
      t₃.getMem (msp + BitVec.ofNat 64 c') = t.getMem (msp + BitVec.ofNat 64 c') := fun c' h8 hc' hr ↦
    hf.getMem (by addr_omega [h8, hc']) fun j hj hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hw, hj, hc', hE, hP2, hm16, hhi]
      · rcases hr with hr | hr <;> addr_omega [hw, hj, hc', hr]
  have hn : heapNext t₃ = heapNext t := by
    simp only [heapNext]
    rw [hf.getMem (a := nextAddr) (by decide) fun j hj hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hw, hj, hE, hP2, hm16, hhi]
      · addr_omega [hw, hj]]
  have hsp₃ : t₃.getReg .x2 = msp := (k₃ .x2 (by decide)).trans hsp₂
  have hheap : HeapOk t₃ := ⟨by rw [hn]; exact ub.rc.k.ng.heap.lo, by rw [hn]; exact ub.rc.k.ng.heap.hi⟩
  have p3 : vecPtr t₃ (msp + 240) = vecPtr t (msp + 240) := hK3 248 (by decide) (by decide) (by omega)
  have c3 : vecCap t₃ (msp + 240) = vecCap t (msp + 240) := hK3 240 (by decide) (by decide) (by omega)
  have l3 : vecLen t₃ (msp + 240) = vecLen t (msp + 240) + 1 := by
    have e := NB.g80000924_m_x2_256 h₃
    rw [hsp₂, hr₂, NB.g80000910_x22 h₁, h.x22] at e
    exact e
  have l3' : (vecLen t₃ (msp + 240)).toNat = (vecLen t (msp + 240)).toNat + 1 := by
    rw [l3]; addr_omega [hP2, hm16, hhi]
  have hy := ub.vs.vecs.bytes
  simp only at hy
  have hl : halvesAt t₃ (vecPtr t₃ (msp + 240)) (vecLen t₃ (msp + 240)).toNat =
      (bfold g st k m).2 ++ [wbucket g k m] := by
    rw [p3, l3', hP, halvesAt_snoc (t := t) (v := wbucket g k m) hpal (by omega)
      (fun x hx1 hx2 ↦ hf x fun hw ↦ by
        rcases hw with hw | hw
        · addr_omega [hw, hx1, hx2, hE]
        · addr_omega [hw, hx2, hP2, hm16, hhi])
      ((getHalfword_eq_of_bytes (by addr_omega [hE, hpal])
          (hf₃ _ fun hw ↦ by addr_omega [hw, hE, hP2, hm16, hhi])
          (hf₃ _ fun hw ↦ by addr_omega [hw, hE, hP2, hm16, hhi])).trans hh₂), ← hP, hy]
  have hbf : bfold g st k (m + 1) =
      ((bfold g st k m).1.set (wbucket g k m).toNat true, (bfold g st k m).2 ++ [wbucket g k m]) := by
    rw [bfold_nz h.nz, Model.usedStep, h.fresh]
    rfl
  have vs₃ := ub.vs.setY (l := (bfold g st k m).2 ++ [wbucket g k m]) hf (fun a ha ↦ (hW a ha).2.2)
    (le_of_eq hn.symm) hheap.hi ⟨by rw [l3', c3]; omega, by rw [p3]; exact by'.al,
      by rw [p3, c3, hn]; exact by'.buf, by rw [p3, c3]; exact by'.dang⟩
    (by simp only [VMiss, p3, c3]; exact ub.vs.my)
    (Or.inl ⟨p3, c3⟩) hl
  have R : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x22 → t₃.getReg r = t.getReg r := fun r h10 h11 h22 ↦ by
    have e : t₃.getReg r = t₂.getReg r := by
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
      all_goals first | exact k₃ _ (by decide) | rfl
    rw [e, hr₂]
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | contradiction | exact k₁ _ (by decide) | rfl
  refine ⟨t₃, r₁.trans ((show Reaches Image.code t₁ t₂ from ⟨1, r₂⟩).trans r₃), NB.g80000924_pc h₃,
    ⟨?_, h.hk, hm, (hK3 120 (by decide) (by decide) (by omega)).trans h.w,
      by rw [R _ (by decide) (by decide) (by decide)]; exact h.x15,
      by rw [R _ (by decide) (by decide) (by decide)]; exact h.x19,
      by rw [R _ (by decide) (by decide) (by decide)]; exact h.x20,
      by rw [R _ (by decide) (by decide) (by decide)]; exact h.x23⟩⟩
  rw [hbf]
  exact ⟨ub.rc.frame hf (fun a ha ↦ (hW a ha).1) hsp₃ hheap (le_of_eq hn.symm),
    (hK3 24 (by decide) (by decide) (by omega)).trans ub.m24, vs₃,
    fun b hb ↦ by rw [hf _ fun hw ↦ (hW _ hw).2.1 ⟨by addr_omega [hb, hU2, hhi],
      by addr_omega [hb, hU2, hhi]⟩]; exact ub.used b hb, ub.ulen, hU1, by rw [hn]; exact ub.hU2,
    by rw [R _ (by decide) (by decide) (by decide)]; exact ub.x8,
    by rw [R _ (by decide) (by decide) (by decide)]; exact ub.x9,
    by rw [R _ (by decide) (by decide) (by decide)]; exact ub.x18,
    by rw [R _ (by decide) (by decide) (by decide)]; exact ub.x24,
    by rw [R _ (by decide) (by decide) (by decide)]; exact ub.x25,
    by rw [R _ (by decide) (by decide) (by decide)]; exact ub.x26,
    by rw [R _ (by decide) (by decide) (by decide)]; exact ub.x27⟩

end

section
variable {s u₀ : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C : Word} {H1 U k : Nat}

/-- A nonzero byte, from `0x80000974` past its bucket to the next byte or the word's end. -/
theorem bytes_bn {m : Nat} {t : MachineState} (h : BN s words u₀ i L Hb st g D C H1 U k m t)
    (hpc : t.pc = 0x80000974) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x800008ec ∧ BO s words u₀ i L Hb st g D C H1 U (k + 1) v) ∨
      (v.pc = 0x8000092c ∧ m + 1 < 8 ∧ BI s words u₀ i L Hb st g D C H1 U k (m + 1) v)) := by
  have next : ∀ t₁, Reaches Image.code t t₁ → t₁.pc = 0x80000928 →
      BD s words u₀ i L Hb st g D C H1 U k m t₁ →
      ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
        (v.pc = 0x800008ec ∧ BO s words u₀ i L Hb st g D C H1 U (k + 1) v) ∨
        (v.pc = 0x8000092c ∧ m + 1 < 8 ∧ BI s words u₀ i L Hb st g D C H1 U k (m + 1) v)) := by
    intro t₁ r₁ hpc₁ h₁
    obtain ⟨v, rv, hv⟩ := bytes_next h₁ hpc₁
    exact ⟨v, r₁.trans rv, Or.inr hv⟩
  obtain ⟨t₁, r₁, hd | ⟨hpc₁, h₁⟩ | ⟨hpc₁, h₁⟩⟩ := bytes_bucket h hpc
  · exact ⟨t₁, r₁, Or.inl hd⟩
  · exact next t₁ r₁ hpc₁ h₁
  obtain ⟨t₂, r₂, hd | ⟨hpc₂, h₂⟩⟩ := bytes_mark h₁ hpc₁
  · exact ⟨t₂, r₁.trans r₂, Or.inl hd⟩
  obtain ⟨t₃, r₃, hpc₃, h₃⟩ := bytes_push h₂ hpc₂
  exact next t₃ (r₁.trans (r₂.trans r₃)) hpc₃ h₃

/-- A word's bytes, from byte `m` (`0x8000092c`, or `0x80000958` past a zero byte `m`) to the
word's end at `0x800008ec`. -/
theorem bytes_inner : ∀ n m (t : MachineState),
    ((t.pc = 0x8000092c ∧ 2 * (8 - m) ≤ n ∧ BI s words u₀ i L Hb st g D C H1 U k m t) ∨
      (t.pc = 0x80000958 ∧ 2 * (8 - m) ≤ n + 1 ∧ BZ s words u₀ i L Hb st g D C H1 U k m t)) →
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x800008ec ∧ BO s words u₀ i L Hb st g D C H1 U (k + 1) v)) := by
  intro n
  induction n with
  | zero =>
    intro m t h
    rcases h with ⟨_, hn, h⟩ | ⟨_, hn, h⟩ <;> (have := h.hm; omega)
  | succ n ih =>
    intro m t h
    have bn : ∀ m' t₁, 2 * (8 - (m' + 1)) ≤ n → Reaches Image.code t t₁ → t₁.pc = 0x80000974 →
        BN s words u₀ i L Hb st g D C H1 U k m' t₁ →
        ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
          (v.pc = 0x800008ec ∧ BO s words u₀ i L Hb st g D C H1 U (k + 1) v)) := by
      intro m' t₁ hm' r₁ hpc₁ h₁
      obtain ⟨t₂, r₂, hd | hd | ⟨hpc₂, hm₂, h₂⟩⟩ := bytes_bn h₁ hpc₁
      · exact ⟨t₂, r₁.trans r₂, Or.inl hd⟩
      · exact ⟨t₂, r₁.trans r₂, Or.inr hd⟩
      · obtain ⟨v, rv, hv⟩ := ih (m' + 1) t₂ (Or.inl ⟨hpc₂, hm', h₂⟩)
        exact ⟨v, r₁.trans (r₂.trans rv), hv⟩
    rcases h with ⟨hpc, hn, h⟩ | ⟨hpc, hn, h⟩
    · have hm := h.hm
      obtain ⟨t₁, r₁, ⟨hpc₁, h₁⟩ | ⟨hpc₁, h₁⟩⟩ := bytes_byte h hpc
      · obtain ⟨v, rv, hv⟩ := ih m t₁ (Or.inr ⟨hpc₁, by omega, h₁⟩)
        exact ⟨v, r₁.trans rv, hv⟩
      · exact bn m t₁ (by omega) r₁ hpc₁ h₁
    · have hm := h.hm
      obtain ⟨t₁, r₁, hd | ⟨hpc₁, hm₁, h₁⟩ | ⟨hpc₁, hm₁, h₁⟩⟩ := bytes_skip h hpc
      · exact ⟨t₁, r₁, Or.inr hd⟩
      · obtain ⟨v, rv, hv⟩ := ih (m + 1) t₁ (Or.inr ⟨hpc₁, by omega, h₁⟩)
        exact ⟨v, r₁.trans rv, hv⟩
      · exact bn (m + 1) t₁ (by omega) r₁ hpc₁ h₁

/-- The buckets, from distinct word `k` at `0x800008f0` to `0x800009c8`. -/
theorem bytes_loop : ∀ n k (t : MachineState), g.2.2.length - k = n → k < g.2.2.length →
    t.pc = 0x800008f0 → BO s words u₀ i L Hb st g D C H1 U k t →
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x800009c8 ∧ BO s words u₀ i L Hb st g D C H1 U g.2.2.length v)) := by
  intro n
  induction n with
  | zero => intro k t hn hk; omega
  | succ n ih =>
    intro k t hn hk hpc h
    obtain ⟨t₁, r₁, hpc₁, h₁⟩ := bytes_word h hpc hk
    obtain ⟨t₂, r₂, hd | ⟨hpc₂, h₂⟩⟩ := bytes_inner 16 0 t₁ (Or.inl ⟨hpc₁, by omega, h₁⟩)
    · exact ⟨t₂, r₁.trans r₂, Or.inl hd⟩
    obtain ⟨t₃, r₃, h₃, ⟨hk₃, hpc₃⟩ | ⟨hk₃, hpc₃⟩⟩ := bytes_outer h₂ hpc₂
    · obtain ⟨v, rv, hv⟩ := ih (k + 1) t₃ (by omega) hk₃ hpc₃ h₃
      exact ⟨v, r₁.trans (r₂.trans (r₃.trans rv)), hv⟩
    · rw [← hk₃]
      exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inr ⟨hpc₃, h₃⟩⟩

/-- `used` and the buckets, from the placement's exit (`0x800008a0`) to `0x800009c8`. -/
theorem bytes_phase {t : MachineState} (h : PX s words u₀ i L Hb st g D C H1 t)
    (hpc : t.pc = 0x800008a0) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ U, v.pc = 0x800009c8 ∧
      BO s words u₀ i L Hb st g D C H1 U g.2.2.length v) := by
  obtain ⟨t₁, r₁, hd | ⟨hpc₁, h₁⟩⟩ := used_alloc h hpc
  · exact ⟨t₁, r₁, Or.inl hd⟩
  have hpos : 0 < g.2.2.length := List.length_pos_iff.mpr h.rc.ne
  obtain ⟨v, rv, hd | ⟨hpcv, hv⟩⟩ := bytes_loop _ 0 t₁ rfl hpos hpc₁ h₁
  · exact ⟨v, r₁.trans rv, Or.inl hd⟩
  · exact ⟨v, r₁.trans rv, Or.inr ⟨_, hpcv, hv⟩⟩

end

end Rv64Verifier.Proofs.Main
