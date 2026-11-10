import Rv64Verifier.Proofs.Main.NewCount

/-!
# `Bytecode::new`'s blocks: past the count

`RC`: past the count in block `i`, what the block keeps: `distinct` at `D` and `counts` at `C`,
both scratch in `[Hb, H1)`, `group_of` and `main`'s slots (`RC.frame`, for writes in `Wr`). `VS`:
the four `Vec`s hold `st'`'s, their buffers apart from the scratch `[Hb, H1)` and from `used`
(`[U, U + Un)`) (`VS.frame` for writes that miss them, `VS.setW` and its kin for a write to one).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

/-- What a block writes past the count: `main`'s scratch slots `24..40` and `104..136`, the `Vec`s'
headers, callees' stacks, `NEXT` and the heap from `H0` on but `distinct` and `counts`. -/
@[rv_addr] def Wr (H0 : Nat) (D C : Word) (n : Nat) (a : Word) : Prop :=
  Within a (msp + 24) 16 ∨ Within a (msp + 104) 32 ∨ Within a (msp + 240) 80 ∨
    Within a (msp + 352) 120 ∨ Within a (msp - 4096) 4096 ∨ Within a nextAddr 8 ∨
    (H0 ≤ a.toNat ∧ a.toNat < heapEnd ∧ ¬ Within a D (8 * n) ∧ ¬ Within a C (8 * n))

theorem BK.frame2 {s : MachineState} {words : List Word} {u₀ t t' : MachineState} {i L Hb : Nat}
    {st : Model.NewState} {W : Word → Prop} {D C : Word} {n : Nat}
    (h : BK s words u₀ i L Hb st t) (hf : BFrame t t' W)
    (hW : ∀ a, W a → Wr (heapNext u₀) D C n a) (hsp : t'.getReg .x2 = msp) (hheap : HeapOk t')
    (hmono : heapNext t ≤ heapNext t') : BK s words u₀ i L Hb st t' := by
  have hlo0 := h.a.inv.heap.lo
  simp only [heapStart, heapNext] at hlo0
  have hW' : ∀ a, W a → Wg a := by
    intro a ha
    rcases hW a ha with h1 | h1 | h1 | h1 | h1 | h1 | ⟨h1, h2, -⟩
    · exact Or.inl (by addr_omega [h1])
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, h2⟩)))))
      simp only [heapStart, heapNext] at h1 ⊢; omega
  have K : ∀ c : Nat, c % 8 = 0 → (8 ≤ c ∧ c + 8 ≤ 24 ∨ 40 ≤ c ∧ c + 8 ≤ 72) →
      t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 hc
    refine hf.getMem (by addr_omega [h8, hc]) fun j hj hw ↦ ?_
    rcases hW _ hw with h1 | h1 | h1 | h1 | h1 | h1 | ⟨h1, h2, -⟩
    · rcases hc with hc | hc <;> addr_omega [h1, hj, hc]
    · rcases hc with hc | hc <;> addr_omega [h1, hj, hc]
    · rcases hc with hc | hc <;> addr_omega [h1, hj, hc]
    · rcases hc with hc | hc <;> addr_omega [h1, hj, hc]
    · rcases hc with hc | hc <;> addr_omega [h1, hj, hc]
    · rcases hc with hc | hc <;> addr_omega [h1, hj, hc]
    · simp only [heapEnd] at h2; rcases hc with hc | hc <;> addr_omega [h2, hj, hc]
  have bm := h.bm
  exact ⟨h.a, h.lt, h.hL, h.fold, h.slotsLen, h.hb0, h.ng.step hf hW' hsp hheap hmono,
    le_trans h.hb hmono,
    ⟨(K 8 (by decide) (by decide)).trans bm.m8, (K 16 (by decide) (by decide)).trans bm.m16,
      (K 40 (by decide) (by decide)).trans bm.m40, (K 48 (by decide) (by decide)).trans bm.m48,
      (K 56 (by decide) (by decide)).trans bm.m56, (K 64 (by decide) (by decide)).trans bm.m64⟩⟩

/-- Past the count in block `i`: `distinct` at `D` and `counts` at `C`, both in `[Hb, H1)`. -/
structure RC (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C : Word) (H1 : Nat) (t : MachineState) : Prop where
  k : BK s words u₀ i L Hb st t
  go : halvesAt t (u₀.getReg .x9) 0x4000 = g.2.1
  fold : gfold words i st L = some g
  ne : g.2.2 ≠ []
  dist : t.readWords D g.2.2.length = g.2.2
  cnt : t.readWords C g.2.2.length = (cfold words i g L).map (BitVec.ofNat 64)
  dal : D.toNat % 8 = 0
  cal : C.toNat % 8 = 0
  dlo : Hb ≤ D.toNat
  dc : D.toNat + 8 * g.2.2.length ≤ C.toNat
  chi : C.toNat + 8 * g.2.2.length ≤ H1
  h1 : H1 ≤ heapNext t
  m72 : t.getMem (msp + 72) = D
  m80 : t.getMem (msp + 80) = C

theorem rwords_keep {t t' : MachineState} {D : Word} {n : Nat} (hal : D.toNat % 8 = 0)
    (hb : D.toNat + 8 * n ≤ 2 ^ 64) (hk : ∀ a : Word, Within a D (8 * n) → byteAt t' a = byteAt t a) :
    t'.readWords D n = t.readWords D n :=
  readWords_bframe (W := fun a ↦ ¬ Within a D (8 * n)) (fun a ha ↦ hk a (Classical.not_not.mp ha))
    hal (fun _ h ↦ h) hb

section
variable {s u₀ t t' : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C : Word} {H1 : Nat}

theorem RC.frame {W : Word → Prop} (h : RC s words u₀ i L Hb st g D C H1 t) (hf : BFrame t t' W)
    (hW : ∀ a, W a → Wr (heapNext u₀) D C g.2.2.length a) (hsp : t'.getReg .x2 = msp)
    (hheap : HeapOk t') (hmono : heapNext t ≤ heapNext t') : RC s words u₀ i L Hb st g D C H1 t' := by
  have hGO := h.k.a.groupOf
  have hhi := h.k.ng.heap.hi
  have hdlo := h.dlo
  have hdc := h.dc
  have hchi := h.chi
  have hh1 := h.h1
  have hmo := h.k.ng.mono
  simp only [heapNext, heapEnd] at hGO hhi hh1 hmo
  have hk : ∀ a : Word, (a.toNat < (u₀.getMem nextAddr).toNat ∨ Within a D (8 * g.2.2.length) ∨
      Within a C (8 * g.2.2.length)) → byteAt t' a = byteAt t a := fun a ha ↦ hf a fun hw ↦ by
    rcases hW a hw with h1 | h1 | h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4⟩
    · rcases ha with ha | ha | ha <;> addr_omega [h1, ha, hdc, hchi, hh1, hhi, hGO, hmo]
    · rcases ha with ha | ha | ha <;> addr_omega [h1, ha, hdc, hchi, hh1, hhi, hGO, hmo]
    · rcases ha with ha | ha | ha <;> addr_omega [h1, ha, hdc, hchi, hh1, hhi, hGO, hmo]
    · rcases ha with ha | ha | ha <;> addr_omega [h1, ha, hdc, hchi, hh1, hhi, hGO, hmo]
    · rcases ha with ha | ha | ha <;> addr_omega [h1, ha, hdc, hchi, hh1, hhi, hGO, hmo]
    · rcases ha with ha | ha | ha <;> addr_omega [h1, ha, hdc, hchi, hh1, hhi, hGO, hmo]
    · simp only [heapNext] at h1
      rcases ha with ha | ha | ha
      · omega
      · exact h3 ha
      · exact h4 ha
  have hK : ∀ c : Nat, c = 72 ∨ c = 80 →
      t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) :=
    fun c hc ↦ hf.getMem (by rcases hc with rfl | rfl <;> decide) fun j hj hw ↦ by
      rcases hW _ hw with h1 | h1 | h1 | h1 | h1 | h1 | ⟨h1, h2, -⟩
      all_goals first
        | (rcases hc with rfl | rfl <;> addr_omega [h1, hj])
        | (simp only [heapEnd] at h2; rcases hc with rfl | rfl <;> addr_omega [h2, hj])
  refine ⟨h.k.frame2 hf hW hsp hheap hmono, ?_, h.fold, h.ne, ?_, ?_, h.dal, h.cal, hdlo, hdc,
    hchi, le_trans h.h1 hmono, (hK 72 (Or.inl rfl)).trans h.m72, (hK 80 (Or.inr rfl)).trans h.m80⟩
  · rw [← h.go]
    exact halvesAt_keep hGO.1 (fun a h1 h2 ↦ hk a (Or.inl (by omega))) (by omega)
  · rw [rwords_keep h.dal (by omega) fun a ha ↦ hk a (Or.inr (Or.inl ha))]
    exact h.dist
  · rw [rwords_keep h.cal (by omega) fun a ha ↦ hk a (Or.inr (Or.inr ha))]
    exact h.cnt

end

/-! ## The `Vec`s -/

/-- `n` bytes from `p` miss `[lo, hi)`. -/
@[rv_addr] def Out (p : Word) (n lo hi : Nat) : Prop :=
  n = 0 ∨ p.toNat + n ≤ lo ∨ hi ≤ p.toNat ∨ hi ≤ lo

/-- The buffer of the `Vec` at `a` misses the scratch `[Hb, H1)` and `used`. -/
def VMiss (t : MachineState) (a : Word) (size Hb H1 U Un : Nat) : Prop :=
  Out (vecPtr t a) ((vecCap t a).toNat * size) Hb H1 ∧
    Out (vecPtr t a) ((vecCap t a).toNat * size) U (U + Un)

/-- The four `Vec`s hold `st'`'s, their buffers allocated from `NewA`'s `NEXT` on, apart from the
scratch. -/
structure VS (u₀ : MachineState) (Hb H1 U Un : Nat) (st' : Model.NewState) (t : MachineState) :
    Prop where
  vecs : VecsAt t st'
  bufs : VecBufs t (heapNext u₀) (heapNext t)
  mb : VMiss t (msp + 400) 24 Hb H1 U Un
  mw : VMiss t (msp + 424) 16 Hb H1 U Un
  mp : VMiss t (msp + 448) 2 Hb H1 U Un
  my : VMiss t (msp + 240) 2 Hb H1 U Un

theorem VecIn.keep {t t' : MachineState} {a : Word} {size al H H' H'' : Nat}
    (h : VecIn t a size al H H') (hc : vecCap t' a = vecCap t a) (hp : vecPtr t' a = vecPtr t a)
    (hl : vecLen t' a = vecLen t a) (hH : H' ≤ H'') : VecIn t' a size al H H'' :=
  ⟨by rw [hl, hc]; exact h.len, by rw [hp]; exact h.al, by rw [hp, hc]; exact (h.mono hH).buf⟩

theorem wordsAt_vec {t t' : MachineState} {a : Word} {H H' : Nat} (h : VecIn t a 16 8 H H')
    (hH : H' ≤ heapEnd) (hp : vecPtr t' a = vecPtr t a) (hl : vecLen t' a = vecLen t a)
    (hb : ∀ x : Word, (vecPtr t a).toNat ≤ x.toNat →
      x.toNat < (vecPtr t a).toNat + (vecCap t a).toNat * 16 → byteAt t' x = byteAt t x) :
    wordsAt t' (vecPtr t' a) (vecLen t' a).toNat = wordsAt t (vecPtr t a) (vecLen t a).toNat := by
  rw [hp, hl]
  have hlc := h.len
  simp only [heapEnd] at hH
  rcases h.buf with h0 | ⟨_, h2⟩
  · have : (vecLen t a).toNat = 0 := by rcases Nat.mul_eq_zero.mp h0 with h0 | h0 <;> omega
    rw [this]; rfl
  · have hm : (vecLen t a).toNat * 16 ≤ (vecCap t a).toNat * 16 := Nat.mul_le_mul_right _ hlc
    exact wordsAt_keep h.al (fun x h8 hx1 hx2 ↦ getMem_eq_of_bytes h8 h8 fun j hj ↦
      hb _ (by addr_omega [hx1, hx2, hj, hm, h2, hH]) (by addr_omega [hx1, hx2, hj, hm, h2, hH]))
      (by omega)

theorem blocksAt_vec {t t' : MachineState} {a : Word} {H H' : Nat} (h : VecIn t a 24 8 H H')
    (hH : H' ≤ heapEnd) (hp : vecPtr t' a = vecPtr t a) (hl : vecLen t' a = vecLen t a)
    (hb : ∀ x : Word, (vecPtr t a).toNat ≤ x.toNat →
      x.toNat < (vecPtr t a).toNat + (vecCap t a).toNat * 24 → byteAt t' x = byteAt t x) :
    blocksAt t' (vecPtr t' a) (vecLen t' a).toNat = blocksAt t (vecPtr t a) (vecLen t a).toNat := by
  rw [hp, hl]
  have hlc := h.len
  simp only [heapEnd] at hH
  rcases h.buf with h0 | ⟨_, h2⟩
  · have : (vecLen t a).toNat = 0 := by rcases Nat.mul_eq_zero.mp h0 with h0 | h0 <;> omega
    rw [this]; rfl
  · have hm : (vecLen t a).toNat * 24 ≤ (vecCap t a).toNat * 24 := Nat.mul_le_mul_right _ hlc
    exact blocksAt_keep h.al (fun x h8 hx1 hx2 ↦ getMem_eq_of_bytes h8 h8 fun j hj ↦
      hb _ (by addr_omega [hx1, hx2, hj, hm, h2, hH]) (by addr_omega [hx1, hx2, hj, hm, h2, hH]))
      (by omega)

theorem halvesAt_vec {t t' : MachineState} {a : Word} {H H' : Nat} (h : VecIn t a 2 2 H H')
    (hH : H' ≤ heapEnd) (hp : vecPtr t' a = vecPtr t a) (hl : vecLen t' a = vecLen t a)
    (hb : ∀ x : Word, (vecPtr t a).toNat ≤ x.toNat →
      x.toNat < (vecPtr t a).toNat + (vecCap t a).toNat * 2 → byteAt t' x = byteAt t x) :
    halvesAt t' (vecPtr t' a) (vecLen t' a).toNat = halvesAt t (vecPtr t a) (vecLen t a).toNat := by
  rw [hp, hl]
  have hlc := h.len
  simp only [heapEnd] at hH
  rcases h.buf with h0 | ⟨_, h2⟩
  · have : (vecLen t a).toNat = 0 := by rcases Nat.mul_eq_zero.mp h0 with h0 | h0 <;> omega
    rw [this]; rfl
  · exact halvesAt_keep h.al (fun x hx1 hx2 ↦ hb _ hx1 (by omega)) (by omega)

/-- A buffer allocated past every other. -/
theorem apart_fresh {p q : Word} {n m Hx : Nat} (hq : m = 0 ∨ q.toNat + m ≤ Hx)
    (hp : n = 0 ∨ Hx ≤ p.toNat) : Apart p n q m := by
  simp only [Apart]; omega

theorem apart_upd {p q p' : Word} {n m n' Hx : Nat} (h : Apart p n q m)
    (hs : (p' = p ∧ n' = n) ∨ n' = 0 ∨ Hx ≤ p'.toNat) (hq : m = 0 ∨ q.toNat + m ≤ Hx) :
    Apart p' n' q m := by
  rcases hs with ⟨rfl, rfl⟩ | hs
  · exact h
  · exact apart_fresh hq (by omega)

theorem Apart.symm' {a b : Word} {n m : Nat} (h : Apart a n b m) : Apart b m a n := by
  simp only [Apart] at h ⊢; omega

section
variable {u₀ t t' : MachineState} {Hb H1 U Un : Nat} {st' : Model.NewState}

/-- A buffer of `VS` misses every write in the scratch, below `NewA`'s `NEXT` or past `t`'s. -/
theorem VS.byte {W : Word → Prop} (hf : BFrame t t' W)
    (hW : ∀ a, W a → a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨
      (Hb ≤ a.toNat ∧ a.toNat < H1) ∨ (U ≤ a.toNat ∧ a.toNat < U + Un))
    {p : Word} {n : Nat} (hpn : n = 0 ∨ heapNext u₀ ≤ p.toNat ∧ p.toNat + n ≤ heapNext t)
    (o1 : Out p n Hb H1) (o2 : Out p n U (U + Un)) (x : Word) (hx1 : p.toNat ≤ x.toNat)
    (hx2 : x.toNat < p.toNat + n) : byteAt t' x = byteAt t x :=
  hf x fun hw ↦ by
    have := hW x hw
    simp only [Out] at o1 o2
    omega

theorem VS.frame {W : Word → Prop} (h : VS u₀ Hb H1 U Un st' t) (hf : BFrame t t' W)
    (hW : ∀ a, W a → ¬ Within a (msp + 240) 24 ∧ ¬ Within a (msp + 400) 72 ∧
      (a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
        (U ≤ a.toNat ∧ a.toNat < U + Un)))
    (hmono : heapNext t ≤ heapNext t') (hH : heapNext t' ≤ heapEnd) :
    VS u₀ Hb H1 U Un st' t' := by
  have hk : ∀ c : Nat, c % 8 = 0 → (240 ≤ c ∧ c + 8 ≤ 264 ∨ 400 ≤ c ∧ c + 8 ≤ 472) →
      t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 hc
    refine hf.getMem (by addr_omega [h8, hc]) fun i hi hw ↦ ?_
    obtain ⟨h1, h2, -⟩ := hW _ hw
    rcases hc with hc | hc
    · exact h1 (by addr_omega [hc, hi])
    · exact h2 (by addr_omega [hc, hi])
  have hHt : heapNext t ≤ heapEnd := le_trans hmono hH
  have p0 : vecPtr t' (msp + 400) = vecPtr t (msp + 400) := hk 408 (by decide) (by decide)
  have l0 : vecLen t' (msp + 400) = vecLen t (msp + 400) := hk 416 (by decide) (by decide)
  have c0 : vecCap t' (msp + 400) = vecCap t (msp + 400) := hk 400 (by decide) (by decide)
  have p1 : vecPtr t' (msp + 424) = vecPtr t (msp + 424) := hk 432 (by decide) (by decide)
  have l1 : vecLen t' (msp + 424) = vecLen t (msp + 424) := hk 440 (by decide) (by decide)
  have c1 : vecCap t' (msp + 424) = vecCap t (msp + 424) := hk 424 (by decide) (by decide)
  have p2 : vecPtr t' (msp + 448) = vecPtr t (msp + 448) := hk 456 (by decide) (by decide)
  have l2 : vecLen t' (msp + 448) = vecLen t (msp + 448) := hk 464 (by decide) (by decide)
  have c2 : vecCap t' (msp + 448) = vecCap t (msp + 448) := hk 448 (by decide) (by decide)
  have p3 : vecPtr t' (msp + 240) = vecPtr t (msp + 240) := hk 248 (by decide) (by decide)
  have l3 : vecLen t' (msp + 240) = vecLen t (msp + 240) := hk 256 (by decide) (by decide)
  have c3 : vecCap t' (msp + 240) = vecCap t (msp + 240) := hk 240 (by decide) (by decide)
  have hW' := fun a ha ↦ (hW a ha).2.2
  have hv := h.vecs
  have hb := h.bufs
  obtain ⟨_, _, _, _, bw, bp, bY, wp, wy, py⟩ := h.bufs
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨hb.b.keep c0 p0 l0 hmono, hb.w.keep c1 p1 l1 hmono,
    hb.p.keep c2 p2 l2 hmono, hb.y.keep c3 p3 l3 hmono, by rw [p0, c0, p1, c1]; exact bw,
    by rw [p0, c0, p2, c2]; exact bp, by rw [p0, c0, p3, c3]; exact bY,
    by rw [p1, c1, p2, c2]; exact wp, by rw [p1, c1, p3, c3]; exact wy,
    by rw [p2, c2, p3, c3]; exact py⟩, ?_, ?_, ?_, ?_⟩
  · rw [← hv.blocks]; exact blocksAt_vec hb.b hHt p0 l0 (VS.byte hf hW' hb.b.buf h.mb.1 h.mb.2)
  · rw [← hv.words]; exact wordsAt_vec hb.w hHt p1 l1 (VS.byte hf hW' hb.w.buf h.mw.1 h.mw.2)
  · rw [← hv.positions]; exact halvesAt_vec hb.p hHt p2 l2 (VS.byte hf hW' hb.p.buf h.mp.1 h.mp.2)
  · rw [← hv.bytes]; exact halvesAt_vec hb.y hHt p3 l3 (VS.byte hf hW' hb.y.buf h.my.1 h.my.2)
  · simp only [VMiss, p0, c0]; exact h.mb
  · simp only [VMiss, p1, c1]; exact h.mw
  · simp only [VMiss, p2, c2]; exact h.mp
  · simp only [VMiss, p3, c3]; exact h.my

/-- A write to the `blocks` `Vec` alone: its header, its old buffer, or past `t`'s `NEXT`. -/
theorem VS.setB {W : Word → Prop} {l : List Model.BlockRust} (h : VS u₀ Hb H1 U Un st' t)
    (hf : BFrame t t' W)
    (hW : ∀ a, W a → ¬ Within a (msp + 424) 24 ∧
      ¬ Within a (msp + 448) 24 ∧
      ¬ Within a (msp + 240) 24 ∧
      (a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
        (U ≤ a.toNat ∧ a.toNat < U + Un) ∨
        Within a (vecPtr t (msp + 400)) ((vecCap t (msp + 400)).toNat * 24)))
    (hmono : heapNext t ≤ heapNext t') (hH : heapNext t' ≤ heapEnd)
    (hin : VecIn t' (msp + 400) 24 8 (heapNext u₀) (heapNext t'))
    (hm : VMiss t' (msp + 400) 24 Hb H1 U Un)
    (hs : (vecPtr t' (msp + 400) = vecPtr t (msp + 400) ∧ vecCap t' (msp + 400) = vecCap t (msp + 400)) ∨
      (vecCap t' (msp + 400)).toNat * 24 = 0 ∨ heapNext t ≤ (vecPtr t' (msp + 400)).toNat)
    (hl : blocksAt t' (vecPtr t' (msp + 400)) (vecLen t' (msp + 400)).toNat = l) :
    VS u₀ Hb H1 U Un { st' with blocks := l } t' := by
  have hk : ∀ c : Nat, c % 8 = 0 → (424 ≤ c ∧ c + 8 ≤ 448 ∨ 448 ≤ c ∧ c + 8 ≤ 472 ∨ 240 ≤ c ∧ c + 8 ≤ 264) →
      t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 hc
    refine hf.getMem (by addr_omega [h8, hc]) fun i hi hw ↦ ?_
    obtain ⟨h1, h2, h3, -⟩ := hW _ hw
    rcases hc with hc | hc | hc
    · exact h1 (by addr_omega [hc, hi])
    · exact h2 (by addr_omega [hc, hi])
    · exact h3 (by addr_omega [hc, hi])
  have hHt : heapNext t ≤ heapEnd := le_trans hmono hH
  have p1 : vecPtr t' (msp + 424) = vecPtr t (msp + 424) := hk 432 (by decide) (by decide)
  have l1 : vecLen t' (msp + 424) = vecLen t (msp + 424) := hk 440 (by decide) (by decide)
  have c1 : vecCap t' (msp + 424) = vecCap t (msp + 424) := hk 424 (by decide) (by decide)
  have p2 : vecPtr t' (msp + 448) = vecPtr t (msp + 448) := hk 456 (by decide) (by decide)
  have l2 : vecLen t' (msp + 448) = vecLen t (msp + 448) := hk 464 (by decide) (by decide)
  have c2 : vecCap t' (msp + 448) = vecCap t (msp + 448) := hk 448 (by decide) (by decide)
  have p3 : vecPtr t' (msp + 240) = vecPtr t (msp + 240) := hk 248 (by decide) (by decide)
  have l3 : vecLen t' (msp + 240) = vecLen t (msp + 240) := hk 256 (by decide) (by decide)
  have c3 : vecCap t' (msp + 240) = vecCap t (msp + 240) := hk 240 (by decide) (by decide)
  have hb := h.bufs
  obtain ⟨_, _, _, _, bw, bp, bY, wp, wy, py⟩ := h.bufs
  have hB : ∀ {p : Word} {n : Nat}, (n = 0 ∨ heapNext u₀ ≤ p.toNat ∧ p.toNat + n ≤ heapNext t) →
      Out p n Hb H1 → Out p n U (U + Un) →
      Apart (vecPtr t (msp + 400)) ((vecCap t (msp + 400)).toNat * 24) p n →
      ∀ x : Word, p.toNat ≤ x.toNat → x.toNat < p.toNat + n → byteAt t' x = byteAt t x := by
    intro p n hpn o1 o2 ha x hx1 hx2
    refine hf x fun hw ↦ ?_
    have := (hW x hw).2.2.2
    simp only [Out, Apart, Within] at o1 o2 ha this
    omega
  have fr : ∀ {q : Word} {m : Nat}, (m = 0 ∨ q.toNat + m ≤ heapNext t) →
      Apart (vecPtr t (msp + 400)) ((vecCap t (msp + 400)).toNat * 24) q m →
      Apart (vecPtr t' (msp + 400)) ((vecCap t' (msp + 400)).toNat * 24) q m := fun hq ha ↦ by
    rcases hs with ⟨e1, e2⟩ | hs
    · rw [e1, e2]; exact ha
    · exact apart_fresh hq hs
  have q1 := hb.w.buf.imp_right fun h ↦ h.2
  have q2 := hb.p.buf.imp_right fun h ↦ h.2
  have q3 := hb.y.buf.imp_right fun h ↦ h.2
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨hin, hb.w.keep c1 p1 l1 hmono, hb.p.keep c2 p2 l2 hmono, hb.y.keep c3 p3 l3 hmono,
    by rw [p1, c1]; exact fr q1 bw,
    by rw [p2, c2]; exact fr q2 bp,
    by rw [p3, c3]; exact fr q3 bY,
    by rw [p1, c1, p2, c2]; exact wp,
    by rw [p1, c1, p3, c3]; exact wy,
    by rw [p2, c2, p3, c3]; exact py⟩, ?_, ?_, ?_, ?_⟩
  · exact hl
  · exact (wordsAt_vec hb.w hHt p1 l1 (hB hb.w.buf h.mw.1 h.mw.2 bw)).trans h.vecs.words
  · exact (halvesAt_vec hb.p hHt p2 l2 (hB hb.p.buf h.mp.1 h.mp.2 bp)).trans h.vecs.positions
  · exact (halvesAt_vec hb.y hHt p3 l3 (hB hb.y.buf h.my.1 h.my.2 bY)).trans h.vecs.bytes
  · exact hm
  · simp only [VMiss, p1, c1]; exact h.mw
  · simp only [VMiss, p2, c2]; exact h.mp
  · simp only [VMiss, p3, c3]; exact h.my

/-- A write to the `words` `Vec` alone: its header, its old buffer, or past `t`'s `NEXT`. -/
theorem VS.setW {W : Word → Prop} {l : List (BitVec 64 × Nat)} (h : VS u₀ Hb H1 U Un st' t)
    (hf : BFrame t t' W)
    (hW : ∀ a, W a → ¬ Within a (msp + 400) 24 ∧
      ¬ Within a (msp + 448) 24 ∧
      ¬ Within a (msp + 240) 24 ∧
      (a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
        (U ≤ a.toNat ∧ a.toNat < U + Un) ∨
        Within a (vecPtr t (msp + 424)) ((vecCap t (msp + 424)).toNat * 16)))
    (hmono : heapNext t ≤ heapNext t') (hH : heapNext t' ≤ heapEnd)
    (hin : VecIn t' (msp + 424) 16 8 (heapNext u₀) (heapNext t'))
    (hm : VMiss t' (msp + 424) 16 Hb H1 U Un)
    (hs : (vecPtr t' (msp + 424) = vecPtr t (msp + 424) ∧ vecCap t' (msp + 424) = vecCap t (msp + 424)) ∨
      (vecCap t' (msp + 424)).toNat * 16 = 0 ∨ heapNext t ≤ (vecPtr t' (msp + 424)).toNat)
    (hl : wordsAt t' (vecPtr t' (msp + 424)) (vecLen t' (msp + 424)).toNat = l) :
    VS u₀ Hb H1 U Un { st' with words := l } t' := by
  have hk : ∀ c : Nat, c % 8 = 0 → (400 ≤ c ∧ c + 8 ≤ 424 ∨ 448 ≤ c ∧ c + 8 ≤ 472 ∨ 240 ≤ c ∧ c + 8 ≤ 264) →
      t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 hc
    refine hf.getMem (by addr_omega [h8, hc]) fun i hi hw ↦ ?_
    obtain ⟨h1, h2, h3, -⟩ := hW _ hw
    rcases hc with hc | hc | hc
    · exact h1 (by addr_omega [hc, hi])
    · exact h2 (by addr_omega [hc, hi])
    · exact h3 (by addr_omega [hc, hi])
  have hHt : heapNext t ≤ heapEnd := le_trans hmono hH
  have p0 : vecPtr t' (msp + 400) = vecPtr t (msp + 400) := hk 408 (by decide) (by decide)
  have l0 : vecLen t' (msp + 400) = vecLen t (msp + 400) := hk 416 (by decide) (by decide)
  have c0 : vecCap t' (msp + 400) = vecCap t (msp + 400) := hk 400 (by decide) (by decide)
  have p2 : vecPtr t' (msp + 448) = vecPtr t (msp + 448) := hk 456 (by decide) (by decide)
  have l2 : vecLen t' (msp + 448) = vecLen t (msp + 448) := hk 464 (by decide) (by decide)
  have c2 : vecCap t' (msp + 448) = vecCap t (msp + 448) := hk 448 (by decide) (by decide)
  have p3 : vecPtr t' (msp + 240) = vecPtr t (msp + 240) := hk 248 (by decide) (by decide)
  have l3 : vecLen t' (msp + 240) = vecLen t (msp + 240) := hk 256 (by decide) (by decide)
  have c3 : vecCap t' (msp + 240) = vecCap t (msp + 240) := hk 240 (by decide) (by decide)
  have hb := h.bufs
  obtain ⟨_, _, _, _, bw, bp, bY, wp, wy, py⟩ := h.bufs
  have hB : ∀ {p : Word} {n : Nat}, (n = 0 ∨ heapNext u₀ ≤ p.toNat ∧ p.toNat + n ≤ heapNext t) →
      Out p n Hb H1 → Out p n U (U + Un) →
      Apart (vecPtr t (msp + 424)) ((vecCap t (msp + 424)).toNat * 16) p n →
      ∀ x : Word, p.toNat ≤ x.toNat → x.toNat < p.toNat + n → byteAt t' x = byteAt t x := by
    intro p n hpn o1 o2 ha x hx1 hx2
    refine hf x fun hw ↦ ?_
    have := (hW x hw).2.2.2
    simp only [Out, Apart, Within] at o1 o2 ha this
    omega
  have fr : ∀ {q : Word} {m : Nat}, (m = 0 ∨ q.toNat + m ≤ heapNext t) →
      Apart (vecPtr t (msp + 424)) ((vecCap t (msp + 424)).toNat * 16) q m →
      Apart (vecPtr t' (msp + 424)) ((vecCap t' (msp + 424)).toNat * 16) q m := fun hq ha ↦ by
    rcases hs with ⟨e1, e2⟩ | hs
    · rw [e1, e2]; exact ha
    · exact apart_fresh hq hs
  have q0 := hb.b.buf.imp_right fun h ↦ h.2
  have q2 := hb.p.buf.imp_right fun h ↦ h.2
  have q3 := hb.y.buf.imp_right fun h ↦ h.2
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨hb.b.keep c0 p0 l0 hmono, hin, hb.p.keep c2 p2 l2 hmono, hb.y.keep c3 p3 l3 hmono,
    by rw [p0, c0]; exact Apart.symm' (fr q0 (Apart.symm' bw)),
    by rw [p0, c0, p2, c2]; exact bp,
    by rw [p0, c0, p3, c3]; exact bY,
    by rw [p2, c2]; exact fr q2 wp,
    by rw [p3, c3]; exact fr q3 wy,
    by rw [p2, c2, p3, c3]; exact py⟩, ?_, ?_, ?_, ?_⟩
  · exact (blocksAt_vec hb.b hHt p0 l0 (hB hb.b.buf h.mb.1 h.mb.2 (Apart.symm' bw))).trans h.vecs.blocks
  · exact hl
  · exact (halvesAt_vec hb.p hHt p2 l2 (hB hb.p.buf h.mp.1 h.mp.2 wp)).trans h.vecs.positions
  · exact (halvesAt_vec hb.y hHt p3 l3 (hB hb.y.buf h.my.1 h.my.2 wy)).trans h.vecs.bytes
  · simp only [VMiss, p0, c0]; exact h.mb
  · exact hm
  · simp only [VMiss, p2, c2]; exact h.mp
  · simp only [VMiss, p3, c3]; exact h.my

/-- A write to the `positions` `Vec` alone: its header, its old buffer, or past `t`'s `NEXT`. -/
theorem VS.setP {W : Word → Prop} {l : List (BitVec 16)} (h : VS u₀ Hb H1 U Un st' t)
    (hf : BFrame t t' W)
    (hW : ∀ a, W a → ¬ Within a (msp + 400) 24 ∧
      ¬ Within a (msp + 424) 24 ∧
      ¬ Within a (msp + 240) 24 ∧
      (a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
        (U ≤ a.toNat ∧ a.toNat < U + Un) ∨
        Within a (vecPtr t (msp + 448)) ((vecCap t (msp + 448)).toNat * 2)))
    (hmono : heapNext t ≤ heapNext t') (hH : heapNext t' ≤ heapEnd)
    (hin : VecIn t' (msp + 448) 2 2 (heapNext u₀) (heapNext t'))
    (hm : VMiss t' (msp + 448) 2 Hb H1 U Un)
    (hs : (vecPtr t' (msp + 448) = vecPtr t (msp + 448) ∧ vecCap t' (msp + 448) = vecCap t (msp + 448)) ∨
      (vecCap t' (msp + 448)).toNat * 2 = 0 ∨ heapNext t ≤ (vecPtr t' (msp + 448)).toNat)
    (hl : halvesAt t' (vecPtr t' (msp + 448)) (vecLen t' (msp + 448)).toNat = l) :
    VS u₀ Hb H1 U Un { st' with positions := l } t' := by
  have hk : ∀ c : Nat, c % 8 = 0 → (400 ≤ c ∧ c + 8 ≤ 424 ∨ 424 ≤ c ∧ c + 8 ≤ 448 ∨ 240 ≤ c ∧ c + 8 ≤ 264) →
      t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 hc
    refine hf.getMem (by addr_omega [h8, hc]) fun i hi hw ↦ ?_
    obtain ⟨h1, h2, h3, -⟩ := hW _ hw
    rcases hc with hc | hc | hc
    · exact h1 (by addr_omega [hc, hi])
    · exact h2 (by addr_omega [hc, hi])
    · exact h3 (by addr_omega [hc, hi])
  have hHt : heapNext t ≤ heapEnd := le_trans hmono hH
  have p0 : vecPtr t' (msp + 400) = vecPtr t (msp + 400) := hk 408 (by decide) (by decide)
  have l0 : vecLen t' (msp + 400) = vecLen t (msp + 400) := hk 416 (by decide) (by decide)
  have c0 : vecCap t' (msp + 400) = vecCap t (msp + 400) := hk 400 (by decide) (by decide)
  have p1 : vecPtr t' (msp + 424) = vecPtr t (msp + 424) := hk 432 (by decide) (by decide)
  have l1 : vecLen t' (msp + 424) = vecLen t (msp + 424) := hk 440 (by decide) (by decide)
  have c1 : vecCap t' (msp + 424) = vecCap t (msp + 424) := hk 424 (by decide) (by decide)
  have p3 : vecPtr t' (msp + 240) = vecPtr t (msp + 240) := hk 248 (by decide) (by decide)
  have l3 : vecLen t' (msp + 240) = vecLen t (msp + 240) := hk 256 (by decide) (by decide)
  have c3 : vecCap t' (msp + 240) = vecCap t (msp + 240) := hk 240 (by decide) (by decide)
  have hb := h.bufs
  obtain ⟨_, _, _, _, bw, bp, bY, wp, wy, py⟩ := h.bufs
  have hB : ∀ {p : Word} {n : Nat}, (n = 0 ∨ heapNext u₀ ≤ p.toNat ∧ p.toNat + n ≤ heapNext t) →
      Out p n Hb H1 → Out p n U (U + Un) →
      Apart (vecPtr t (msp + 448)) ((vecCap t (msp + 448)).toNat * 2) p n →
      ∀ x : Word, p.toNat ≤ x.toNat → x.toNat < p.toNat + n → byteAt t' x = byteAt t x := by
    intro p n hpn o1 o2 ha x hx1 hx2
    refine hf x fun hw ↦ ?_
    have := (hW x hw).2.2.2
    simp only [Out, Apart, Within] at o1 o2 ha this
    omega
  have fr : ∀ {q : Word} {m : Nat}, (m = 0 ∨ q.toNat + m ≤ heapNext t) →
      Apart (vecPtr t (msp + 448)) ((vecCap t (msp + 448)).toNat * 2) q m →
      Apart (vecPtr t' (msp + 448)) ((vecCap t' (msp + 448)).toNat * 2) q m := fun hq ha ↦ by
    rcases hs with ⟨e1, e2⟩ | hs
    · rw [e1, e2]; exact ha
    · exact apart_fresh hq hs
  have q0 := hb.b.buf.imp_right fun h ↦ h.2
  have q1 := hb.w.buf.imp_right fun h ↦ h.2
  have q3 := hb.y.buf.imp_right fun h ↦ h.2
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨hb.b.keep c0 p0 l0 hmono, hb.w.keep c1 p1 l1 hmono, hin, hb.y.keep c3 p3 l3 hmono,
    by rw [p0, c0, p1, c1]; exact bw,
    by rw [p0, c0]; exact Apart.symm' (fr q0 (Apart.symm' bp)),
    by rw [p0, c0, p3, c3]; exact bY,
    by rw [p1, c1]; exact Apart.symm' (fr q1 (Apart.symm' wp)),
    by rw [p1, c1, p3, c3]; exact wy,
    by rw [p3, c3]; exact fr q3 py⟩, ?_, ?_, ?_, ?_⟩
  · exact (blocksAt_vec hb.b hHt p0 l0 (hB hb.b.buf h.mb.1 h.mb.2 (Apart.symm' bp))).trans h.vecs.blocks
  · exact (wordsAt_vec hb.w hHt p1 l1 (hB hb.w.buf h.mw.1 h.mw.2 (Apart.symm' wp))).trans h.vecs.words
  · exact hl
  · exact (halvesAt_vec hb.y hHt p3 l3 (hB hb.y.buf h.my.1 h.my.2 py)).trans h.vecs.bytes
  · simp only [VMiss, p0, c0]; exact h.mb
  · simp only [VMiss, p1, c1]; exact h.mw
  · exact hm
  · simp only [VMiss, p3, c3]; exact h.my

/-- A write to the `bytes` `Vec` alone: its header, its old buffer, or past `t`'s `NEXT`. -/
theorem VS.setY {W : Word → Prop} {l : List (BitVec 16)} (h : VS u₀ Hb H1 U Un st' t)
    (hf : BFrame t t' W)
    (hW : ∀ a, W a → ¬ Within a (msp + 400) 24 ∧
      ¬ Within a (msp + 424) 24 ∧
      ¬ Within a (msp + 448) 24 ∧
      (a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
        (U ≤ a.toNat ∧ a.toNat < U + Un) ∨
        Within a (vecPtr t (msp + 240)) ((vecCap t (msp + 240)).toNat * 2)))
    (hmono : heapNext t ≤ heapNext t') (hH : heapNext t' ≤ heapEnd)
    (hin : VecIn t' (msp + 240) 2 2 (heapNext u₀) (heapNext t'))
    (hm : VMiss t' (msp + 240) 2 Hb H1 U Un)
    (hs : (vecPtr t' (msp + 240) = vecPtr t (msp + 240) ∧ vecCap t' (msp + 240) = vecCap t (msp + 240)) ∨
      (vecCap t' (msp + 240)).toNat * 2 = 0 ∨ heapNext t ≤ (vecPtr t' (msp + 240)).toNat)
    (hl : halvesAt t' (vecPtr t' (msp + 240)) (vecLen t' (msp + 240)).toNat = l) :
    VS u₀ Hb H1 U Un { st' with bytes := l } t' := by
  have hk : ∀ c : Nat, c % 8 = 0 → (400 ≤ c ∧ c + 8 ≤ 424 ∨ 424 ≤ c ∧ c + 8 ≤ 448 ∨ 448 ≤ c ∧ c + 8 ≤ 472) →
      t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 hc
    refine hf.getMem (by addr_omega [h8, hc]) fun i hi hw ↦ ?_
    obtain ⟨h1, h2, h3, -⟩ := hW _ hw
    rcases hc with hc | hc | hc
    · exact h1 (by addr_omega [hc, hi])
    · exact h2 (by addr_omega [hc, hi])
    · exact h3 (by addr_omega [hc, hi])
  have hHt : heapNext t ≤ heapEnd := le_trans hmono hH
  have p0 : vecPtr t' (msp + 400) = vecPtr t (msp + 400) := hk 408 (by decide) (by decide)
  have l0 : vecLen t' (msp + 400) = vecLen t (msp + 400) := hk 416 (by decide) (by decide)
  have c0 : vecCap t' (msp + 400) = vecCap t (msp + 400) := hk 400 (by decide) (by decide)
  have p1 : vecPtr t' (msp + 424) = vecPtr t (msp + 424) := hk 432 (by decide) (by decide)
  have l1 : vecLen t' (msp + 424) = vecLen t (msp + 424) := hk 440 (by decide) (by decide)
  have c1 : vecCap t' (msp + 424) = vecCap t (msp + 424) := hk 424 (by decide) (by decide)
  have p2 : vecPtr t' (msp + 448) = vecPtr t (msp + 448) := hk 456 (by decide) (by decide)
  have l2 : vecLen t' (msp + 448) = vecLen t (msp + 448) := hk 464 (by decide) (by decide)
  have c2 : vecCap t' (msp + 448) = vecCap t (msp + 448) := hk 448 (by decide) (by decide)
  have hb := h.bufs
  obtain ⟨_, _, _, _, bw, bp, bY, wp, wy, py⟩ := h.bufs
  have hB : ∀ {p : Word} {n : Nat}, (n = 0 ∨ heapNext u₀ ≤ p.toNat ∧ p.toNat + n ≤ heapNext t) →
      Out p n Hb H1 → Out p n U (U + Un) →
      Apart (vecPtr t (msp + 240)) ((vecCap t (msp + 240)).toNat * 2) p n →
      ∀ x : Word, p.toNat ≤ x.toNat → x.toNat < p.toNat + n → byteAt t' x = byteAt t x := by
    intro p n hpn o1 o2 ha x hx1 hx2
    refine hf x fun hw ↦ ?_
    have := (hW x hw).2.2.2
    simp only [Out, Apart, Within] at o1 o2 ha this
    omega
  have fr : ∀ {q : Word} {m : Nat}, (m = 0 ∨ q.toNat + m ≤ heapNext t) →
      Apart (vecPtr t (msp + 240)) ((vecCap t (msp + 240)).toNat * 2) q m →
      Apart (vecPtr t' (msp + 240)) ((vecCap t' (msp + 240)).toNat * 2) q m := fun hq ha ↦ by
    rcases hs with ⟨e1, e2⟩ | hs
    · rw [e1, e2]; exact ha
    · exact apart_fresh hq hs
  have q0 := hb.b.buf.imp_right fun h ↦ h.2
  have q1 := hb.w.buf.imp_right fun h ↦ h.2
  have q2 := hb.p.buf.imp_right fun h ↦ h.2
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨hb.b.keep c0 p0 l0 hmono, hb.w.keep c1 p1 l1 hmono, hb.p.keep c2 p2 l2 hmono, hin,
    by rw [p0, c0, p1, c1]; exact bw,
    by rw [p0, c0, p2, c2]; exact bp,
    by rw [p0, c0]; exact Apart.symm' (fr q0 (Apart.symm' bY)),
    by rw [p1, c1, p2, c2]; exact wp,
    by rw [p1, c1]; exact Apart.symm' (fr q1 (Apart.symm' wy)),
    by rw [p2, c2]; exact Apart.symm' (fr q2 (Apart.symm' py))⟩, ?_, ?_, ?_, ?_⟩
  · exact (blocksAt_vec hb.b hHt p0 l0 (hB hb.b.buf h.mb.1 h.mb.2 (Apart.symm' bY))).trans h.vecs.blocks
  · exact (wordsAt_vec hb.w hHt p1 l1 (hB hb.w.buf h.mw.1 h.mw.2 (Apart.symm' wy))).trans h.vecs.words
  · exact (halvesAt_vec hb.p hHt p2 l2 (hB hb.p.buf h.mp.1 h.mp.2 (Apart.symm' py))).trans h.vecs.positions
  · exact hl
  · simp only [VMiss, p0, c0]; exact h.mb
  · simp only [VMiss, p1, c1]; exact h.mw
  · simp only [VMiss, p2, c2]; exact h.mp
  · exact hm

end

end Rv64Verifier.Proofs.Main
