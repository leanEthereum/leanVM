import Rv64Verifier.Proofs.Main.NewRest

/-!
# `Bytecode::new`'s blocks: the runs

`rfold`: `runs` after the first `k` distinct words. `runs_entry`: `0x800006dc` allocates `next` at
`N`, scratch past `counts`, into the loop (`RN`, at `0x80000758`). `runs_head` loads a word and its
count and pushes `next`, `runs_grow` grows `words` (`grow_one`), `runs_push` pushes onto it;
`runs_phase`: to the loop's exit (`RE`, at `0x800007b8`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

/-! ## The model -/

/-- `runs` after the first `k` distinct words. -/
def rfold (words : List Word) (i L : Nat) (g : GrpSt) (st : Model.NewState) (k : Nat) :
    List Nat × Nat × List (BitVec 64 × Nat) :=
  (List.range k).foldl (fun r j ↦ Model.runStep r (g.2.2.getD j 0, (cfold words i g L).getD j 0))
    ([], st.positions.length, st.words)

section
variable (words : List Word) (i L : Nat) (g : GrpSt) (st : Model.NewState)

theorem rfold_succ (k : Nat) : rfold words i L g st (k + 1) =
    Model.runStep (rfold words i L g st k) (g.2.2.getD k 0, (cfold words i g L).getD k 0) := by
  simp only [rfold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem rfold_spec : ∀ k, (rfold words i L g st k).1.length = k ∧
    (rfold words i L g st k).2.1 = st.positions.length + ((cfold words i g L).take k).sum ∧
    (rfold words i L g st k).2.2.length = st.words.length + k
  | 0 => by simp [rfold]
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := rfold_spec k
    rw [rfold_succ]
    simp only [Model.runStep, List.length_append, List.length_singleton, h1, h2, h3]
    refine ⟨trivial, ?_, by omega⟩
    by_cases hk : k < (cfold words i g L).length
    · rw [List.sum_take_succ _ _ hk]
      simp [List.getD_eq_getElem?_getD, hk]
      omega
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp [List.getD_eq_getElem?_getD, hk]

theorem runs_rfold : (g.2.2.zip (cfold words i g L)).foldl Model.runStep
    ([], st.positions.length, st.words) = rfold words i L g st g.2.2.length := by
  have hz : g.2.2.zip (cfold words i g L) = (List.range g.2.2.length).map fun j ↦
      (g.2.2.getD j 0, (cfold words i g L).getD j 0) := by
    apply List.ext_getElem
    · simp [cfold_length]
    · intro j h1 h2
      simp only [List.length_zip, cfold_length, Nat.min_self] at h1
      simp [List.getD_eq_getElem?_getD, h1, cfold_length]
  rw [hz, List.foldl_map]
  rfl

end

theorem sum_set_succ : ∀ (l : List Nat) (j : Nat), (l.set j (l.getD j 0 + 1)).sum ≤ l.sum + 1
  | [], _ => by simp
  | a :: l, 0 => by simp; omega
  | a :: l, j + 1 => by
    simp only [List.set_cons_succ, List.sum_cons, List.getD_cons_succ]
    have := sum_set_succ l j
    omega

theorem cfold_sum (words : List Word) (i : Nat) (g : GrpSt) : ∀ p, (cfold words i g p).sum ≤ p
  | 0 => by simp [cfold]
  | p + 1 => by
    have ih := cfold_sum words i g p
    rw [cfold_succ, Model.countStep]
    split
    · have := sum_set_succ (cfold words i g p) ((g.2.1.getD p 0).toNat)
      omega
    · omega

theorem rfold_end_le (words : List Word) (i L : Nat) (g : GrpSt) (st : Model.NewState) (k : Nat) :
    (rfold words i L g st k).2.1 ≤ st.positions.length + L := by
  rw [(rfold_spec words i L g st k).2.1]
  have h1 := cfold_sum words i g L
  have h2 : ((cfold words i g L).take k).sum ≤ (cfold words i g L).sum :=
    List.Sublist.sum_le_sum (List.take_sublist _ _) (fun _ _ ↦ Nat.zero_le _)
  omega

/-- `n` `(u64, usize)`s from `p` and one more. -/
theorem wordsAt_snoc {t t' : MachineState} {p : Word} {n : Nat} {w e : Word}
    (hk : ∀ j < n, t'.getMem (p + BitVec.ofNat 64 (16 * j)) = t.getMem (p + BitVec.ofNat 64 (16 * j)) ∧
      t'.getMem (p + BitVec.ofNat 64 (16 * j) + 8) = t.getMem (p + BitVec.ofNat 64 (16 * j) + 8))
    (h0 : t'.getMem (p + BitVec.ofNat 64 (16 * n)) = w)
    (h1 : t'.getMem (p + BitVec.ofNat 64 (16 * n) + 8) = e) :
    wordsAt t' p (n + 1) = wordsAt t p n ++ [(w, e.toNat)] := by
  unfold wordsAt
  rw [List.range_succ, List.map_append, List.map_singleton, h0, h1]
  congr 1
  apply List.map_congr_left
  intro j hj
  obtain ⟨e0, e1⟩ := hk j (List.mem_range.mp hj)
  rw [e0, e1]

/-! ## The loop's state -/

/-- The runs' loop past its setup: `next` at `N`, scratch past `counts`; `main`'s slots `24` (the
words left after the block) and `32` (`positions`' length before it); `next`'s header at
`msp + 272`. -/
structure RB (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C N : Word) (H1 : Nat) (t : MachineState) : Prop where
  rc : RC s words u₀ i L Hb st g D C H1 t
  nal : N.toNat % 8 = 0
  nlo : C.toNat + 8 * g.2.2.length ≤ N.toNat
  nhi : N.toNat + 8 * g.2.2.length ≤ H1
  m24 : t.getMem (msp + 24) = BitVec.ofNat 64 ((words.getD 0 0).toNat - 2 ^ 14 * i - L)
  m32 : t.getMem (msp + 32) = BitVec.ofNat 64 st.positions.length
  m272 : t.getMem (msp + 272) = BitVec.ofNat 64 g.2.2.length
  m280 : t.getMem (msp + 280) = N
  x8 : t.getReg .x8 = u₀.getReg .x8
  x18 : t.getReg .x18 = BitVec.ofNat 64 g.2.2.length
  x20 : t.getReg .x20 = BitVec.ofNat 64 (8 * L)
  x21 : t.getReg .x21 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i))
  x22 : t.getReg .x22 = N
  x26 : t.getReg .x26 = BitVec.ofNat 64 g.2.2.length

/-- At `0x80000758`, the head of the runs' loop, at the `k`th distinct word. -/
structure RN (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C N : Word) (H1 k : Nat) (t : MachineState) : Prop where
  rb : RB s words u₀ i L Hb st g D C N H1 t
  vs : VS u₀ Hb H1 0 0 { st with words := (rfold words i L g st k).2.2 } t
  hk : k < g.2.2.length
  next : t.readWords N k = (rfold words i L g st k).1.map (BitVec.ofNat 64)
  m288 : t.getMem (msp + 288) = BitVec.ofNat 64 k
  x12 : t.getReg .x12 = D
  x19 : t.getReg .x19 = BitVec.ofNat 64 (8 * k)
  x23 : t.getReg .x23 = BitVec.ofNat 64 k
  x27 : t.getReg .x27 = BitVec.ofNat 64 (rfold words i L g st k).2.1

section
variable {s u₀ t t' : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 : Nat}

theorem RB.frame {W : Word → Prop} (h : RB s words u₀ i L Hb st g D C N H1 t) (hf : BFrame t t' W)
    (hW : ∀ a, W a → Wr (heapNext u₀) D C g.2.2.length a ∧ ¬ Within a (msp + 24) 16 ∧
      ¬ Within a (msp + 272) 16)
    (hr : ∀ r ∈ ([.x2, .x8, .x18, .x20, .x21, .x22, .x26] : List Reg), t'.getReg r = t.getReg r)
    (hheap : HeapOk t') (hmono : heapNext t ≤ heapNext t') : RB s words u₀ i L Hb st g D C N H1 t' := by
  have K : ∀ c : Nat, c = 24 ∨ c = 32 ∨ c = 272 ∨ c = 280 →
      t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) :=
    fun c hc ↦ hf.getMem (by rcases hc with rfl | rfl | rfl | rfl <;> decide) fun j hj hw ↦ by
      obtain ⟨-, h2, h3⟩ := hW _ hw
      rcases hc with rfl | rfl | rfl | rfl
      · exact h2 (by addr_omega [hj])
      · exact h2 (by addr_omega [hj])
      · exact h3 (by addr_omega [hj])
      · exact h3 (by addr_omega [hj])
  have hsp : t'.getReg .x2 = msp := (hr .x2 (by simp)).trans h.rc.k.ng.sp
  exact ⟨h.rc.frame hf (fun a ha ↦ (hW a ha).1) hsp hheap hmono, h.nal, h.nlo, h.nhi,
    (K 24 (by simp)).trans h.m24, (K 32 (by simp)).trans h.m32, (K 272 (by simp)).trans h.m272,
    (K 280 (by simp)).trans h.m280, (hr .x8 (by simp)).trans h.x8, (hr .x18 (by simp)).trans h.x18,
    (hr .x20 (by simp)).trans h.x20, (hr .x21 (by simp)).trans h.x21,
    (hr .x22 (by simp)).trans h.x22, (hr .x26 (by simp)).trans h.x26⟩

theorem RC.raise {H1' : Nat} (h : RC s words u₀ i L Hb st g D C H1 t) (h1 : H1 ≤ H1')
    (h2 : H1' ≤ heapNext t) : RC s words u₀ i L Hb st g D C H1' t :=
  ⟨h.k, h.go, h.fold, h.ne, h.dist, h.cnt, h.dal, h.cal, h.dlo, h.dc, le_trans h.chi h1, h2, h.m72,
    h.m80⟩

/-- The `Vec`s of a block, buffers below `Hb`: apart from the scratch from `Hb` on. -/
theorem VS.init {U Un : Nat} (hv : VecsAt t st) (hb : VecBufs t (heapNext u₀) Hb)
    (hHb : Hb ≤ heapNext t) (hU : Un = 0) : VS u₀ Hb H1 U Un st t := by
  have o : ∀ {a : Word} {size al : Nat}, VecIn t a size al (heapNext u₀) Hb →
      VMiss t a size Hb H1 U Un := fun hin ↦
    ⟨by rcases hin.buf with h | h <;> simp only [Out] <;> omega, by simp only [Out]; omega⟩
  exact ⟨hv, hb.mono hHb, o hb.b, o hb.w, o hb.p, o hb.y⟩

end

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D : Word} {H : Nat} {C : Word}

/-- `0x800006dc`: `next` allocated at `N`, into the runs' loop. -/
theorem runs_entry (h : CL s words u₀ i L Hb st g D H C L (cfold words i g L) t)
    (hpc : t.pc = 0x800006dc) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ N, v.pc = 0x80000758 ∧
      RN s words u₀ i L Hb st g D C N (heapNext v) 0 v) := by
  have qs := h.qs
  have hsp := qs.k.ng.sp
  have hpos : 0 < g.2.2.length := List.length_pos_iff.mpr qs.ne
  have hhi := qs.k.ng.heap.hi
  have hchi := h.chi
  simp only [heapNext, heapEnd] at hhi hchi
  have hdl : g.2.2.length < 2 ^ 28 := by omega
  -- `0x800006dc`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b800006dc_spec hpc trivial
  have k₁ := b800006dc_keeps h₁
  have hm₁ := b800006dc_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = msp := (k₁ .x2 (by decide)).trans hsp
  have hn₁ : heapNext t₁ = heapNext t := by simp only [heapNext, hm₁]
  have x10₁ : t₁.getReg .x10 = msp + 104 := by rw [b800006dc_x10 h₁, hsp]
  have pre : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨by rw [hn₁]; exact qs.k.ng.heap.lo, by rw [hn₁]; exact qs.k.ng.heap.hi⟩
    out := by rw [x10₁]; exact validRange_of (by decide) (by decide) (by decide)
    align := by rw [b800006dc_x13 h₁]; decide
    size := by rw [b800006dc_x14 h₁]; decide
    stack := rtStack_msp hsp₁ (by decide) (by decide)
    outFree := by
      rw [x10₁]
      exact ⟨Or.inr (by simp only [heapEnd]; decide), by addr_omega []⟩
    outStack := by rw [x10₁]; simp only [stackLo, hsp₁, tryAllocStack]; addr_omega [] }
  obtain ⟨t₂, r₂, ⟨hpc₂, hpv, post, -⟩ | hd⟩ :=
    tryAllocZeroed.call r₁ (b800006dc_pc h₁) pre
  swap
  · exact ⟨t₂, r₂, Or.inl hd⟩
  have hpc₂' : t₂.pc = 0x800006f8 := by rw [hpc₂, returnAddress, b800006dc_x1 h₁]; decide
  have hsp₂ : t₂.getReg .x2 = msp := (hpv.reg .x2).trans hsp₁
  have pf := post.frame
  rw [x10₁] at pf
  -- `0x800006f8`
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b800006f8_spec hpc₂' (by rv_eval [hsp₂, msp]; decide)
  have k₃ := b800006f8_keeps h₃
  have hm₃ := b800006f8_mem_same h₃
  by_cases htag : t₂.getMem (msp + 104) = 0
  swap
  · obtain ⟨w, rw', hw⟩ := abort (u := t₃) (by
      rw [b800006f8_pc_taken h₃ (by rw [hsp₂]; exact htag)]; decide)
    exact ⟨w, r₂.trans (r₃.trans rw'), Or.inl hw⟩
  have hpc₃ := b800006f8_pc_not_taken h₃ (by rw [hsp₂]; exact htag)
  have hsp₃ : t₃.getReg .x2 = msp := (k₃ .x2 (by decide)).trans hsp₂
  -- `0x80000700`
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b80000700_spec hpc₃ (by rv_eval [hsp₃, msp]; decide)
  have k₄ := b80000700_keeps h₄
  have hf₄ := holds_slots h₄ hsp₃ [32, 288, 280, 272, 24] (by decide) (by decide)
  have hsp₄ : t₄.getReg .x2 = msp := (k₄ .x2 (by decide)).trans hsp₃
  have hn₄ : heapNext t₄ = heapNext t₂ := by
    simp only [heapNext]
    rw [hf₄.getMem (a := nextAddr) (by decide) fun j hj ⟨c, hc, hin⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> addr_omega [hin, hj], hm₃]
  -- what the allocation gives
  have e112 : (msp + 104 + 8 : Word) = msp + 112 := by decide
  have e120 : (msp + 104 + 16 : Word) = msp + 120 := by decide
  obtain ⟨hcap, hnb⟩ := post.ok (by rw [x10₁]; exact htag)
  rw [x10₁, e112, b800006dc_x11 h₁, h.x18] at hcap
  rw [x10₁, e120, b800006dc_x11 h₁, b800006dc_x13 h₁, b800006dc_x14 h₁,
    h.x18] at hnb
  simp only [BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl] at hnb
  rw [Nat.mod_eq_of_lt (by omega)] at hnb
  obtain ⟨hnal, hnb'⟩ := hnb
  have hnb'' := hnb'.resolve_left (by omega)
  have hhi₂ := post.heap.hi
  have hmo₂ := post.mono
  simp only [heapNext, heapEnd] at hnb'' hhi₂ hmo₂ hn₁
  -- the slots the allocation keeps
  have K₂ : ∀ c : Nat, c % 8 = 0 → c < 4096 → (c + 8 ≤ 104 ∨ 128 ≤ c) →
      t₂.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 hc hc'
    rw [pf.getMem fun j hj hw ↦ by
        rcases hw with hw | hw | hw | ⟨hw1, hw2⟩
        · rcases hc' with hc' | hc' <;> addr_omega [hw, hj, hc, hc']
        · simp only [stackLo, hsp₁, tryAllocStack] at hw; addr_omega [hw, hj, hc]
        · addr_omega [hw, hj, hc]
        · simp only [heapNext] at hw2; addr_omega [hw2, hhi₂, hj, hc], hm₁]
  have K₄ : ∀ c : Nat, c % 8 = 0 ∧ c < 4096 ∧
      ([32, 288, 280, 272, 24].all fun c' ↦ (c' + 8 ≤ c || c + 8 ≤ c') && c' < 4096) = true →
      t₄.getMem (msp + BitVec.ofNat 64 c) = t₃.getMem (msp + BitVec.ofNat 64 c) :=
    fun c hc ↦ slots_keepMsp hf₄ hc
  -- the frame from `t`
  have hf : BFrame t t₄ fun a ↦ (Within a (msp + 104) 24 ∨
      Within a (stackLo t₁ tryAllocStack) tryAllocStack ∨ Within a nextAddr 8 ∨ Fresh t₁ t₂ a) ∨
      (∃ c ∈ [32, 288, 280, 272, 24], Within a (msp + BitVec.ofNat 64 c) 8) := fun a ha ↦ by
    have e1 := hf₄ a fun h ↦ ha (Or.inr h)
    have e2 : byteAt t₃ a = byteAt t₂ a := by rw [byteAt_eq, byteAt_eq, hm₃]
    have e3 := pf.byte a fun h ↦ ha (Or.inl h)
    have e4 : byteAt t₁ a = byteAt t a := by rw [byteAt_eq, byteAt_eq, hm₁]
    rw [e1, e2, e3, e4]
  have hlo0 := qs.k.a.inv.heap.lo
  have hmo0 := qs.k.ng.mono
  have hdhi := qs.dhi
  have hclo := h.clo
  have hHt := qs.hH
  simp only [heapNext, heapStart] at hlo0 hmo0 hHt
  have hWr : ∀ a, ((Within a (msp + 104) 24 ∨
      Within a (stackLo t₁ tryAllocStack) tryAllocStack ∨ Within a nextAddr 8 ∨ Fresh t₁ t₂ a) ∨
      (∃ c ∈ [32, 288, 280, 272, 24], Within a (msp + BitVec.ofNat 64 c) 8)) →
      Wr (heapNext u₀) D C g.2.2.length a ∧ (¬ Within a (msp + 240) 24 ∧
        ¬ Within a (msp + 400) 72 ∧ (a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨
          (Hb ≤ a.toNat ∧ a.toNat < heapNext t₄) ∨ (0 ≤ a.toNat ∧ a.toNat < 0 + 0))) := by
    intro a ha
    simp only [heapNext]
    rcases ha with (ha | ha | ha | ⟨ha1, ha2⟩) | ⟨c, hc, ha⟩
    · exact ⟨Or.inr (Or.inl (by addr_omega [ha])), by addr_omega [ha], by addr_omega [ha],
        Or.inr (Or.inl (by addr_omega [ha, hhi]))⟩
    · simp only [stackLo, hsp₁, tryAllocStack] at ha
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha]))))), by addr_omega [ha],
        by addr_omega [ha], Or.inr (Or.inl (by addr_omega [ha, hhi]))⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))), by addr_omega [ha],
        by addr_omega [ha], Or.inr (Or.inl (by addr_omega [ha, hhi]))⟩
    · simp only [heapNext] at ha1 ha2
      refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by
          simp only [heapEnd]; omega, fun h' ↦ by addr_omega [h', ha1, hn₁, hdhi, hclo, hHt],
          fun h' ↦ by addr_omega [h', ha1, hn₁, hchi]⟩))))), fun h' ↦ by addr_omega [h', ha2, hhi₂],
        fun h' ↦ by addr_omega [h', ha2, hhi₂], Or.inr (Or.inl (by omega))⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      refine ⟨?_, by rcases hc with rfl | rfl | rfl | rfl | rfl <;> addr_omega [ha],
        by rcases hc with rfl | rfl | rfl | rfl | rfl <;> addr_omega [ha],
        Or.inr (Or.inl (by rcases hc with rfl | rfl | rfl | rfl | rfl <;> addr_omega [ha, hhi]))⟩
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by addr_omega [ha])
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha])))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha])))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha])))
      · exact Or.inl (by addr_omega [ha])
  have hheap₄ : HeapOk t₄ := ⟨by rw [hn₄]; exact post.heap.lo, by rw [hn₄]; exact post.heap.hi⟩
  have hmono₄ : heapNext t ≤ heapNext t₄ := by rw [hn₄]; simp only [heapNext]; omega
  have rc₀ : RC s words u₀ i L Hb st g D C (heapNext t) t :=
    ⟨qs.k, qs.go, qs.fold, qs.ne, qs.dist, h.cnt, qs.dal, h.cal, qs.dlo, by omega, h.chi, le_rfl,
      h.m72, h.m80⟩
  have rc₄ := (rc₀.frame hf (fun a ha ↦ (hWr a ha).1) hsp₄ hheap₄ hmono₄).raise hmono₄ le_rfl
  have vs₄ := (VS.init (H1 := heapNext t₄) (U := 0) qs.vecs qs.bufs qs.k.hb rfl).frame hf
    (fun a ha ↦ (hWr a ha).2) hmono₄ hheap₄.hi
  -- the slots
  have hP : t.getMem (msp + BitVec.ofNat 64 464) = BitVec.ofNat 64 st.positions.length := by
    have e := congrArg List.length qs.vecs.positions
    simp only [halvesAt, List.length_map, List.length_range] at e
    rw [← e, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl
  have m464 : t₃.getMem (msp + 464) = BitVec.ofNat 64 st.positions.length := by
    rw [hm₃]; exact (K₂ 464 (by decide) (by decide) (by omega)).trans hP
  have m112 : t₃.getMem (msp + 112) = BitVec.ofNat 64 g.2.2.length := by rw [hm₃, hcap]
  have R : ∀ r ∈ ([.x8, .x18, .x20, .x21] : List Reg), t₄.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (k₄ _ (by decide)).trans ((k₃ _ (by decide)).trans ((hpv.reg _ (by decide)).trans
        (k₁ _ (by decide))))
  refine ⟨t₄, r₂.trans (r₃.trans r₄), Or.inr ⟨t₂.getMem (msp + 120), b80000700_pc h₄,
    ⟨⟨rc₄, hnal, by omega, by rw [hn₄]; simp only [heapNext]; omega, ?_, ?_, ?_, ?_,
      (R .x8 (by simp)).trans h.x8, (R .x18 (by simp)).trans h.x18,
      (R .x20 (by simp)).trans h.x20, (R .x21 (by simp)).trans h.x21, ?_, ?_⟩,
      vs₄, hpos, rfl, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · rw [← hsp₃, b80000700_m_x2_24 h₄, k₃ .x26 (by decide), hpv.reg .x26 (by decide),
      k₁ .x26 (by decide), h.x26]
  · rw [← hsp₃, b80000700_m_x2_32 h₄, hsp₃, m464]
  · rw [← hsp₃, b80000700_m_x2_272 h₄, hsp₃, m112]
  · rw [← hsp₃, b80000700_m_x2_280 h₄, hsp₃, hm₃]
  · rw [b80000700_x22 h₄, hsp₃, hm₃]
  · rw [b80000700_x26 h₄, hsp₃, m112]
  · rw [← hsp₃, b80000700_m_x2_288 h₄]; rfl
  · rw [b80000700_x12 h₄, hsp₃, hm₃, ← h.m72]
    exact K₂ 72 (by decide) (by decide) (by omega)
  · rw [b80000700_x19 h₄]; rfl
  · rw [b80000700_x23 h₄]; rfl
  · rw [b80000700_x27 h₄, hsp₃, m464]; rfl

end

/-- Inside the runs' loop at the `k`th distinct word, `next` pushed: the word and its count loaded. -/
structure RQ (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C N : Word) (H1 k : Nat) (t : MachineState) : Prop where
  rb : RB s words u₀ i L Hb st g D C N H1 t
  vs : VS u₀ Hb H1 0 0 { st with words := (rfold words i L g st k).2.2 } t
  hk : k < g.2.2.length
  next : t.readWords N (k + 1) = (rfold words i L g st (k + 1)).1.map (BitVec.ofNat 64)
  m288 : t.getMem (msp + 288) = BitVec.ofNat 64 (k + 1)
  x9 : t.getReg .x9 = vecLen t (msp + 424)
  x12 : t.getReg .x12 = D
  x19 : t.getReg .x19 = BitVec.ofNat 64 (8 * k)
  x23 : t.getReg .x23 = BitVec.ofNat 64 (k + 1)
  x24 : t.getReg .x24 = g.2.2.getD k 0
  x25 : t.getReg .x25 = BitVec.ofNat 64 ((cfold words i g L).getD k 0)
  x27 : t.getReg .x27 = BitVec.ofNat 64 (rfold words i L g st k).2.1

/-- The bounds of the scratch. -/
theorem RB.bounds {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
    {g : GrpSt} {D C N : Word} {H1 : Nat} (h : RB s words u₀ i L Hb st g D C N H1 t) :
    (u₀.getMem nextAddr).toNat ≤ Hb ∧ Hb ≤ D.toNat ∧ D.toNat + 8 * g.2.2.length ≤ C.toNat ∧
      C.toNat + 8 * g.2.2.length ≤ N.toNat ∧ N.toNat + 8 * g.2.2.length ≤ H1 ∧
      H1 ≤ (t.getMem nextAddr).toNat ∧ (t.getMem nextAddr).toNat ≤ 0x78000000 ∧
      0x20000000 ≤ (u₀.getMem nextAddr).toNat ∧ 0 < g.2.2.length ∧ g.2.2.length < 2 ^ 28 := by
  have h1 := h.rc.k.hb0
  have h2 := h.rc.h1
  have h3 := h.rc.k.ng.heap.hi
  have h4 := h.rc.k.a.inv.heap.lo
  have h5 := h.rc.dlo
  have h6 := h.rc.dc
  have h7 := h.nlo
  have h8 := h.nhi
  have hpos : 0 < g.2.2.length := List.length_pos_iff.mpr h.rc.ne
  simp only [heapNext, heapEnd, heapStart] at h1 h2 h3 h4
  refine ⟨h1, h5, h6, h7, h8, h2, h3, h4, hpos, by omega⟩

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 k : Nat}

/-- `0x80000758`: the `k`th word and its count loaded, `next` pushed; on to the `words` push
(`0x80000730`), or to its growth first (`0x800007a4`). -/
theorem runs_head (h : RN s words u₀ i L Hb st g D C N H1 k t) (hpc : t.pc = 0x80000758) :
    ∃ v, Reaches Image.code t v ∧ RQ s words u₀ i L Hb st g D C N H1 k v ∧
      ((v.pc = 0x80000730 ∧ vecLen v (msp + 424) ≠ vecCap v (msp + 424)) ∨
        (v.pc = 0x800007a4 ∧ vecLen v (msp + 424) = vecCap v (msp + 424))) := by
  have rb := h.rb
  have rc := rb.rc
  have hsp := rc.k.ng.sp
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := rb.bounds
  have hk := h.hk
  have dal := rc.dal
  have cal := rc.cal
  have nal := rb.nal
  -- `0x80000758`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000758_spec hpc (by
    rv_eval []
    simp only [hsp, h.x12, h.x19, rc.m80]
    refine ⟨?_, ?_, ?_⟩ <;> refine (Sym.validAccess_eight _).mpr ⟨?_, ?_⟩ <;>
      addr_omega [b0, b1, b2, b3, b4, b5, b6, b7, b9, hk, dal, cal])
  have k₁ := b80000758_keeps h₁
  have hm₁ := b80000758_mem_same h₁
  have hpc₁ : t₁.pc = 0x80000788 := b80000758_pc_taken h₁ (by
    rw [h.x23, rb.x26]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    omega)
  have hsp₁ : t₁.getReg .x2 = msp := (k₁ .x2 (by decide)).trans hsp
  have x24₁ : t₁.getReg .x24 = g.2.2.getD k 0 := by
    rw [b80000758_x24 h₁, h.x12, h.x19, ← rwords_getD hk, rc.dist]
  have x25₁ : t₁.getReg .x25 = BitVec.ofNat 64 ((cfold words i g L).getD k 0) := by
    rw [b80000758_x25 h₁, hsp, rc.m80, h.x19, ← rwords_getD hk, rc.cnt,
      getD_map_ofNat (by rw [cfold_length]; exact hk)]
  -- `0x80000788`
  have x22₁ : t₁.getReg .x22 = N := (k₁ .x22 (by decide)).trans rb.x22
  have x19₁ : t₁.getReg .x19 = BitVec.ofNat 64 (8 * k) := (k₁ .x19 (by decide)).trans h.x19
  have hNk : (N + BitVec.ofNat 64 (8 * k)).toNat = N.toNat + 8 * k := by
    addr_omega [b4, b5, b6, hk]
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b80000788_spec hpc₁ (by
    rv_eval []
    simp only [hsp₁, x22₁, x19₁]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | decide
      | (refine (Sym.validAccess_eight _).mpr ⟨?_, ?_⟩ <;> addr_omega [b0, b1, b2, b3, b4, b5, b6, b7, b9, hk, nal])
      | (intro e; have := congrArg BitVec.toNat e; addr_omega [this, b4, b5, b6, hk]))
  have k₂ := b80000788_keeps h₂
  have hf₂ : BFrame t₁ t₂ fun a ↦ Within a (msp + 288) 8 ∨
      Within a (N + BitVec.ofNat 64 (8 * k)) 8 := by
    refine (holds_bframe h₂ ?_).mono fun a ha ↦ ?_
    · intro w hw
      simp only [b80000788, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rv_eval []; rw [hsp₁]; decide
      · rv_eval []; rw [x22₁, x19₁]; addr_omega [nal, hNk]
    · simp only [b80000788, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left] at ha
      rv_eval [] at ha
      rw [hsp₁, x22₁, x19₁] at ha
      exact ha
  have hf : BFrame t t₂ fun a ↦ Within a (msp + 288) 8 ∨
      Within a (N + BitVec.ofNat 64 (8 * k)) 8 := fun a ha ↦ by
    rw [hf₂ a ha, byteAt_eq, byteAt_eq, hm₁]
  have hWb : ∀ a, (Within a (msp + 288) 8 ∨ Within a (N + BitVec.ofNat 64 (8 * k)) 8) →
      Wr (heapNext u₀) D C g.2.2.length a ∧ ¬ Within a (msp + 24) 16 ∧
        ¬ Within a (msp + 272) 16 := by
    intro a ha
    rcases ha with ha | ha
    · exact ⟨Or.inr (Or.inr (Or.inl (by addr_omega [ha]))), by addr_omega [ha], by addr_omega [ha]⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hNk, b0, b1, b2, b3],
        by addr_omega [ha, hNk, b4, b5, b6, hk], fun h' ↦ by addr_omega [h', ha, hNk, b2, b3, hk],
        fun h' ↦ by addr_omega [h', ha, hNk, b2, b3, hk]⟩))))),
        by addr_omega [ha, hNk, b4, b5, b6, hk], by addr_omega [ha, hNk, b4, b5, b6, hk]⟩
  have hWv : ∀ a, (Within a (msp + 288) 8 ∨ Within a (N + BitVec.ofNat 64 (8 * k)) 8) →
      ¬ Within a (msp + 240) 24 ∧ ¬ Within a (msp + 400) 72 ∧ (a.toNat < heapNext u₀ ∨
        heapNext t ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨ (0 ≤ a.toNat ∧ a.toNat < 0 + 0)) := by
    intro a ha
    rcases ha with ha | ha
    · exact ⟨by addr_omega [ha], by addr_omega [ha], Or.inr (Or.inl (by addr_omega [ha, b6]))⟩
    · exact ⟨by addr_omega [ha, hNk, b4, b5, b6, hk], by addr_omega [ha, hNk, b4, b5, b6, hk],
        Or.inr (Or.inr (Or.inl ⟨by addr_omega [ha, hNk, b1, b2, b3], by addr_omega [ha, hNk, b4, hk]⟩))⟩
  have hn₂ : heapNext t₂ = heapNext t := by
    simp only [heapNext]
    rw [hf.getMem (a := nextAddr) (by decide) fun j hj hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hw, hj]
      · addr_omega [hw, hj, hNk, b4, b5, b6, hk]]
  have hheap₂ : HeapOk t₂ := ⟨by rw [hn₂]; exact rc.k.ng.heap.lo, by rw [hn₂]; exact rc.k.ng.heap.hi⟩
  have rb₂ := rb.frame hf hWb (fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₂ _ (by decide)).trans (k₁ _ (by decide))) hheap₂ (le_of_eq hn₂.symm)
  have vs₂ := h.vs.frame hf hWv (le_of_eq hn₂.symm) hheap₂.hi
  have K : ∀ c : Nat, c = 424 ∨ c = 440 →
      t₂.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) :=
    fun c hc ↦ hf.getMem (by rcases hc with rfl | rfl <;> decide) fun j hj hw ↦ by
      rcases hc with rfl | rfl <;> rcases hw with hw | hw <;>
        addr_omega [hw, hj, hNk, b4, b5, b6, hk]
  have hv₂ : t₂.getMem (N + BitVec.ofNat 64 (8 * k)) = BitVec.ofNat 64 (rfold words i L g st k).2.1 := by
    have e := b80000788_m1 h₂
    rw [x22₁, x19₁] at e
    rw [e, k₁ .x27 (by decide), h.x27]
  have next₂ : t₂.readWords N (k + 1) = (rfold words i L g st (k + 1)).1.map (BitVec.ofNat 64) := by
    rw [rw_snoc (t := t) (fun j hj ↦ hf.getMem (by addr_omega [nal, hj, hk, b4, b5, b6])
      fun x hx hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hx, hj, hNk, hk, b4, b5, b6])
      hv₂, h.next, rfold_succ]
    simp [Model.runStep]
  refine ⟨t₂, r₁.trans r₂, ⟨rb₂, vs₂, hk, next₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← hsp₁, b80000788_m_x2_288 h₂, k₁ .x23 (by decide), h.x23, BitVec.ofNat_add]; rfl
  · rw [b80000788_x9 h₂, hsp₁, hm₁]
    exact (K 440 (Or.inr rfl)).symm
  · rw [k₂ .x12 (by decide), k₁ .x12 (by decide), h.x12]
  · rw [k₂ .x19 (by decide), x19₁]
  · rw [b80000788_x23 h₂, k₁ .x23 (by decide), h.x23, BitVec.ofNat_add]; rfl
  · rw [k₂ .x24 (by decide), x24₁]
  · rw [k₂ .x25 (by decide), x25₁]
  · rw [k₂ .x27 (by decide), k₁ .x27 (by decide), h.x27]
  · have e : vecLen t₂ (msp + 424) = vecCap t₂ (msp + 424) ↔
        t₁.getMem (t₁.getReg .x2 + 440) = t₁.getMem (t₁.getReg .x2 + 424) := by
      rw [hsp₁, hm₁, hm₁]
      exact ⟨fun e ↦ (K 440 (Or.inr rfl)).symm.trans (e.trans (K 424 (Or.inl rfl))),
        fun e ↦ (K 440 (Or.inr rfl)).trans (e.trans (K 424 (Or.inl rfl)).symm)⟩
    by_cases hfull : vecLen t₂ (msp + 424) = vecCap t₂ (msp + 424)
    · exact Or.inr ⟨b80000788_pc_not_taken h₂ (e.mp hfull), hfull⟩
    · exact Or.inl ⟨b80000788_pc_taken h₂ fun e' ↦ hfull (e.mpr e'), hfull⟩

end

/-- `n` `(u64, usize)`s from two byte ranges with equal bytes, both aligned. -/
theorem wordsAt_of_bytes {t s : MachineState} {a b : Word} {n m : Nat}
    (h : bytesAt t a m = bytesAt s b m) (hm : n * 16 ≤ m) (ha : a.toNat % 8 = 0)
    (hb : b.toNat % 8 = 0) : wordsAt t a n = wordsAt s b n := by
  have e : ∀ (x : Word) (j : Nat), x + BitVec.ofNat 64 (16 * j) + 8 = x + BitVec.ofNat 64 (16 * j + 8) :=
    fun x j ↦ by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  unfold wordsAt
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  rw [e, e, getMem_eq_of_bytesAt h ha hb (k := 16 * j) (by omega) (by omega),
    getMem_eq_of_bytesAt h ha hb (k := 16 * j + 8) (by omega) (by omega)]

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 k : Nat}

/-- `0x800007a4`: `words` full, `grow_one` makes room for one more. -/
theorem runs_grow (h : RQ s words u₀ i L Hb st g D C N H1 k t) (hpc : t.pc = 0x800007a4)
    (hfull : vecLen t (msp + 424) = vecCap t (msp + 424)) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (RQ s words u₀ i L Hb st g D C N H1 k v ∧
      v.pc = 0x80000730 ∧ vecLen v (msp + 424) ≠ vecCap v (msp + 424))) := by
  have rb := h.rb
  have rc := rb.rc
  have hsp := rc.k.ng.sp
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := rb.bounds
  have bw := h.vs.bufs.w
  have hk := h.hk
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b800007a4_spec hpc trivial
  have k₁ := b800007a4_keeps h₁
  have hm₁ := b800007a4_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = msp := (k₁ .x2 (by decide)).trans hsp
  have x10₁ : t₁.getReg .x10 = msp + 424 := by rw [b800007a4_x10 h₁, hsp]
  have hn₁ : heapNext t₁ = heapNext t := by simp only [heapNext, hm₁]
  have hheap₁ : HeapOk t₁ := ⟨by rw [hn₁]; exact rc.k.ng.heap.lo, by rw [hn₁]; exact rc.k.ng.heap.hi⟩
  have vp : vecPtr t₁ (msp + 424) = vecPtr t (msp + 424) := hm₁ _
  have vc : vecCap t₁ (msp + 424) = vecCap t (msp + 424) := hm₁ _
  have pre : GrowOnePre 16 8 t₁ := {
    heap := hheap₁
    self := by rw [x10₁]; exact validRange_of (by decide) (by decide) (by decide)
    raw := by
      rw [x10₁]
      simp only [RawVecOk, Buf, vp, vc]
      refine ⟨bw.al, bw.buf.imp_right fun hb' ↦ ⟨?_, ?_⟩⟩
      · simp only [heapStart, heapNext] at hb' b7 ⊢; omega
      · rw [hn₁]; exact hb'.2
    stack := rtStack_msp hsp₁ (by decide) (by decide)
    selfFree := by
      rw [x10₁]
      exact ⟨Or.inr (by simp only [heapEnd]; decide), by addr_omega []⟩
    selfStack := by rw [x10₁]; simp only [stackLo, hsp₁, growOneStack]; addr_omega [] }
  obtain ⟨v, rv, ⟨hpcv, hpv, post, hfresh⟩ | hd⟩ :=
    growOneFresh_80011fc0.call r₁ (b800007a4_pc h₁) pre
  swap
  · exact ⟨v, rv, Or.inl hd⟩
  have hpcv' : v.pc = 0x800007b0 := by rw [hpcv, returnAddress, b800007a4_x1 h₁]; decide
  have hspv : v.getReg .x2 = msp := (hpv.reg .x2).trans hsp₁
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b800007b0_spec hpcv' (by rv_eval [hspv, msp]; decide)
  have k₂ := b800007b0_keeps h₂
  have hm₂ := b800007b0_mem_same h₂
  have hsp₂ : t₂.getReg .x2 = msp := (k₂ .x2 (by decide)).trans hspv
  have pf := post.frame
  have pcap := post.cap
  have pby := post.bytes
  rw [x10₁] at pf pcap pby hfresh
  have hhiv := post.heap.hi
  have hmov := post.mono
  have hn₁w := hn₁
  simp only [heapNext, heapEnd] at hhiv hmov hn₁
  have hf : BFrame t t₂ fun a ↦ Within a (msp + 424) 16 ∨
      Within a (stackLo t₁ growOneStack) growOneStack ∨ Within a nextAddr 8 ∨ Fresh t₁ v a :=
    fun a ha ↦ by
      rw [byteAt_eq, byteAt_eq, hm₂, ← hm₁, ← byteAt_eq, ← byteAt_eq]
      exact pf.byte a ha
  have hn₂ : heapNext t₂ = heapNext v := by simp only [heapNext, hm₂]
  have hheap₂ : HeapOk t₂ := ⟨by rw [hn₂]; exact post.heap.lo, by rw [hn₂]; exact post.heap.hi⟩
  have hmono₂ : heapNext t ≤ heapNext t₂ := by rw [hn₂]; simp only [heapNext]; omega
  have hWb : ∀ a, (Within a (msp + 424) 16 ∨ Within a (stackLo t₁ growOneStack) growOneStack ∨
      Within a nextAddr 8 ∨ Fresh t₁ v a) →
      (Wr (heapNext u₀) D C g.2.2.length a ∧ ¬ Within a (msp + 24) 16 ∧
        ¬ Within a (msp + 272) 16) ∧ (¬ Within a (msp + 400) 24 ∧ ¬ Within a (msp + 448) 24 ∧
        ¬ Within a (msp + 240) 24 ∧ (a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨
          (Hb ≤ a.toNat ∧ a.toNat < H1) ∨ (0 ≤ a.toNat ∧ a.toNat < 0 + 0) ∨
          Within a (vecPtr t (msp + 424)) ((vecCap t (msp + 424)).toNat * 16))) := by
    intro a ha
    simp only [heapNext]
    rcases ha with ha | ha | ha | ⟨ha1, ha2⟩
    · exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha])))), by addr_omega [ha],
        by addr_omega [ha]⟩, by addr_omega [ha], by addr_omega [ha], by addr_omega [ha],
        Or.inr (Or.inl (by addr_omega [ha, b6]))⟩
    · simp only [stackLo, hsp₁, growOneStack] at ha
      exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha]))))), by addr_omega [ha],
        by addr_omega [ha]⟩, by addr_omega [ha], by addr_omega [ha], by addr_omega [ha],
        Or.inr (Or.inl (by addr_omega [ha, b6]))⟩
    · exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))), by addr_omega [ha],
        by addr_omega [ha]⟩, by addr_omega [ha], by addr_omega [ha], by addr_omega [ha],
        Or.inr (Or.inl (by addr_omega [ha, b6]))⟩
    · simp only [heapNext] at ha1 ha2
      rw [hn₁] at ha1
      exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapEnd]; omega,
        fun h' ↦ by addr_omega [h', ha1, b2, b3, b4, b5],
        fun h' ↦ by addr_omega [h', ha1, b3, b4, b5]⟩))))), by addr_omega [ha2, hhiv],
        by addr_omega [ha2, hhiv]⟩, by addr_omega [ha2, hhiv], by addr_omega [ha2, hhiv],
        by addr_omega [ha2, hhiv], Or.inr (Or.inl ha1)⟩
  have R : ∀ r ∈ ([.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg), t₂.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₂ _ (by decide)).trans ((hpv.reg _ (by decide)).trans (k₁ _ (by decide)))
  have rb₂ := rb.frame hf (fun a ha ↦ (hWb a ha).1) (fun r hr ↦ R r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)) hheap₂ hmono₂
  have l440 : vecLen t₂ (msp + 424) = vecLen t (msp + 424) :=
    hf.getMem (by decide) fun j hj hw ↦ by
      rcases hw with hw | hw | hw | ⟨hw1, hw2⟩
      · addr_omega [hw, hj]
      · simp only [stackLo, hsp₁, growOneStack] at hw; addr_omega [hw, hj]
      · addr_omega [hw, hj]
      · simp only [heapNext] at hw2; addr_omega [hw2, hj, hhiv]
  have p2 : vecPtr t₂ (msp + 424) = vecPtr v (msp + 424) := hm₂ _
  have c2 : vecCap t₂ (msp + 424) = vecCap v (msp + 424) := hm₂ _
  have hlc : (vecLen t (msp + 424)).toNat = (vecCap t (msp + 424)).toNat := by rw [hfull]
  have hroom : (vecLen t₂ (msp + 424)).toNat < (vecCap t₂ (msp + 424)).toNat := by
    rw [l440, c2]; rw [vc] at pcap; omega
  have hlen : (vecLen t (msp + 424)).toNat = (rfold words i L g st k).2.2.length := by
    have e := congrArg List.length h.vs.vecs.words
    simp only [wordsAt, List.length_map, List.length_range] at e
    exact e
  have hin : VecIn t₂ (msp + 424) 16 8 (heapNext u₀) (heapNext t₂) := by
    refine ⟨by omega, by rw [p2]; exact hfresh.1, ?_⟩
    rw [p2, c2, hn₂]
    rcases hfresh.2 with h0 | ⟨h1, h2⟩
    · exact Or.inl h0
    · right; rw [hn₁w] at h1; simp only [heapNext] at b0 h1 h2 ⊢; omega
  have vs₂ := h.vs.setW (l := (rfold words i L g st k).2.2) hf (fun a ha ↦ (hWb a ha).2) hmono₂ hheap₂.hi hin
    (by
      simp only [VMiss, p2, c2]
      rcases hfresh.2 with h0 | ⟨h1, _⟩
      · exact ⟨Or.inl h0, Or.inl h0⟩
      · rw [hn₁w] at h1
        exact ⟨Or.inr (Or.inr (Or.inl (by simp only [heapNext] at h1; omega))),
          Or.inr (Or.inr (Or.inr (by omega)))⟩)
    (by
      rw [p2, c2]
      rcases hfresh.2 with h0 | ⟨h1, _⟩
      · exact Or.inr (Or.inl h0)
      · rw [hn₁w] at h1; exact Or.inr (Or.inr h1))
    (by
      rw [p2, l440]
      have e1 : wordsAt t₂ (vecPtr v (msp + 424)) (vecLen t (msp + 424)).toNat =
          wordsAt v (vecPtr v (msp + 424)) (vecLen t (msp + 424)).toNat := by
        simp only [wordsAt, hm₂]
      have e2 : wordsAt t₁ (vecPtr t (msp + 424)) (vecLen t (msp + 424)).toNat =
          wordsAt t (vecPtr t (msp + 424)) (vecLen t (msp + 424)).toNat := by
        simp only [wordsAt, hm₁]
      rw [e1, wordsAt_of_bytes pby (by rw [vc, hlc]) hfresh.1 (by rw [vp]; exact bw.al), vp, e2]
      exact h.vs.vecs.words)
  refine ⟨t₂, rv.trans r₂, Or.inr ⟨⟨rb₂, vs₂, h.hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    b800007b0_pc h₂, fun e ↦ by rw [e] at hroom; omega⟩⟩
  · rw [rwords_keep rb.nal (by omega) fun a ha ↦ hf a fun hw ↦ by
      rcases hw with hw | hw | hw | ⟨hw1, hw2⟩
      · addr_omega [hw, ha, b4, b5, b6, hk]
      · simp only [stackLo, hsp₁, growOneStack] at hw; addr_omega [hw, ha, b4, b5, b6, hk]
      · addr_omega [hw, ha, b4, b5, b6, hk]
      · simp only [heapNext] at hw1; rw [← hn₁] at b5; addr_omega [hw1, ha, b4, b5, b6, h.hk]]
    exact h.next
  · rw [← h.m288]
    exact hf.getMem (by decide) fun j hj hw ↦ by
      rcases hw with hw | hw | hw | ⟨hw1, hw2⟩
      · addr_omega [hw, hj]
      · simp only [stackLo, hsp₁, growOneStack] at hw; addr_omega [hw, hj]
      · addr_omega [hw, hj]
      · simp only [heapNext] at hw2; addr_omega [hw2, hj, hhiv]
  · rw [R .x9 (by simp), h.x9, l440]
  · rw [b800007b0_x12 h₂, hspv, ← hm₂]; exact rb₂.rc.m72
  · rw [R .x19 (by simp), h.x19]
  · rw [R .x23 (by simp), h.x23]
  · rw [R .x24 (by simp), h.x24]
  · rw [R .x25 (by simp), h.x25]
  · rw [R .x27 (by simp), h.x27]

end

/-- Past the runs' loop, at `0x800007b8`: `runs` in `words` and `next`. -/
structure RE (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C N : Word) (H1 : Nat) (t : MachineState) : Prop where
  rb : RB s words u₀ i L Hb st g D C N H1 t
  vs : VS u₀ Hb H1 0 0 { st with words := (rfold words i L g st g.2.2.length).2.2 } t
  next : t.readWords N g.2.2.length =
    (rfold words i L g st g.2.2.length).1.map (BitVec.ofNat 64)
  x9 : t.getReg .x9 = BitVec.ofNat 64 (rfold words i L g st g.2.2.length).2.2.length
  x12 : t.getReg .x12 = D
  x27 : t.getReg .x27 = BitVec.ofNat 64 (rfold words i L g st g.2.2.length).2.1

/-- A `Vec`'s length is below `2 ^ 31`. -/
theorem VecIn.len_lt {t : MachineState} {a : Word} {size al H H' : Nat} (h : VecIn t a size al H H')
    (hs : 0 < size) (hH : H' ≤ heapEnd) : (vecLen t a).toNat < 2 ^ 31 := by
  have h1 := h.len
  have h2 := Nat.mul_le_mul_right size h1
  simp only [heapEnd] at hH
  rcases h.buf with h0 | ⟨_, h3⟩
  · rcases Nat.mul_eq_zero.mp h0 with h0 | h0 <;> omega
  · have : (vecCap t a).toNat ≤ (vecCap t a).toNat * size := Nat.le_mul_of_pos_right _ hs
    omega

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 k : Nat}

/-- `0x80000730`: `(word, end)` pushed onto `words`; on to the next word, or out of the loop. -/
theorem runs_push (h : RQ s words u₀ i L Hb st g D C N H1 k t) (hpc : t.pc = 0x80000730)
    (hroom : vecLen t (msp + 424) ≠ vecCap t (msp + 424)) :
    ∃ v, Reaches Image.code t v ∧ ((v.pc = 0x80000758 ∧ RN s words u₀ i L Hb st g D C N H1 (k + 1) v) ∨
      (v.pc = 0x800007b8 ∧ k + 1 = g.2.2.length ∧ RE s words u₀ i L Hb st g D C N H1 v)) := by
  have rb := h.rb
  have rc := rb.rc
  have hsp := rc.k.ng.sp
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := rb.bounds
  have hk := h.hk
  have bw := h.vs.bufs.w
  have mw := h.vs.mw
  have hlen : (vecLen t (msp + 424)).toNat = (rfold words i L g st k).2.2.length := by
    have e := congrArg List.length h.vs.vecs.words
    simp only [wordsAt, List.length_map, List.length_range] at e
    exact e
  have hPl : st.positions.length < 2 ^ 31 := by
    have e := congrArg List.length h.vs.vecs.positions
    simp only [halvesAt, List.length_map, List.length_range] at e
    rw [← e]; exact h.vs.bufs.p.len_lt (by decide) (by simp only [heapNext, heapEnd]; omega)
  have hlc := bw.len
  have hlt : (vecLen t (msp + 424)).toNat < (vecCap t (msp + 424)).toNat :=
    lt_of_le_of_ne hlc fun e ↦ hroom (BitVec.eq_of_toNat_eq e)
  have hm16 : (vecLen t (msp + 424)).toNat * 16 + 16 ≤ (vecCap t (msp + 424)).toNat * 16 := by omega
  obtain ⟨hP1, hP2⟩ := bw.buf.resolve_left (by omega)
  have hpal := bw.al
  have hP : vecPtr t (msp + 424) = t.getMem (msp + 432) := rfl
  rw [hP] at hP1 hP2 hpal
  simp only [heapNext] at hP1 hP2
  have hEe : t.getMem (msp + 432) + vecLen t (msp + 424) * 16 =
      t.getMem (msp + 432) + BitVec.ofNat 64 (16 * (vecLen t (msp + 424)).toNat) := by
    apply BitVec.eq_of_toNat_eq
    addr_omega [hP2, hm16, b6]
  have hE : (t.getMem (msp + 432) + BitVec.ofNat 64 (16 * (vecLen t (msp + 424)).toNat)).toNat =
      (t.getMem (msp + 432)).toNat + 16 * (vecLen t (msp + 424)).toNat := by
    addr_omega [hP2, hm16, b6]
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b80000730_spec hpc (by
    rv_eval []
    simp only [hsp, h.x9, hEe]
    and_intros
    all_goals first
      | decide
      | (refine (Sym.validAccess_eight _).mpr ⟨?_, ?_⟩ <;> addr_omega [hE, hP1, hP2, hm16, b0, b6, b7, hpal])
      | (intro e; have := congrArg BitVec.toNat e; addr_omega [this, hE, hP2, hm16, b6]))
  have kv := b80000730_keeps hv
  have hspv : v.getReg .x2 = msp := (kv .x2 (by decide)).trans hsp
  have hf : BFrame t v fun a ↦
      Within a (t.getMem (msp + 432) + BitVec.ofNat 64 (16 * (vecLen t (msp + 424)).toNat) + 8) 8 ∨
      Within a (t.getMem (msp + 432) + BitVec.ofNat 64 (16 * (vecLen t (msp + 424)).toNat)) 8 ∨
      Within a (msp + 440) 8 := by
    refine (holds_bframe hv ?_).mono fun a ha ↦ ?_
    · intro w hw
      simp only [b80000730, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · rv_eval []; rw [hsp, h.x9, hEe]; addr_omega [hE, hpal, hP2, hm16, b6]
      · rv_eval []; rw [hsp, h.x9, hEe]; addr_omega [hE, hpal, hP2, hm16, b6]
      · rv_eval []; rw [hsp]; decide
    · simp only [b80000730, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left] at ha
      rv_eval [] at ha
      rw [hsp, h.x9, hEe] at ha
      exact ha
  have mo := mw.1
  rw [hP] at mo
  have hWb : ∀ a, (Within a (t.getMem (msp + 432) +
      BitVec.ofNat 64 (16 * (vecLen t (msp + 424)).toNat) + 8) 8 ∨
      Within a (t.getMem (msp + 432) + BitVec.ofNat 64 (16 * (vecLen t (msp + 424)).toNat)) 8 ∨
      Within a (msp + 440) 8) →
      (Wr (heapNext u₀) D C g.2.2.length a ∧ ¬ Within a (msp + 24) 16 ∧
        ¬ Within a (msp + 272) 16) ∧ (¬ Within a (msp + 400) 24 ∧ ¬ Within a (msp + 448) 24 ∧
        ¬ Within a (msp + 240) 24 ∧ (a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨
          (Hb ≤ a.toNat ∧ a.toNat < H1) ∨ (0 ≤ a.toNat ∧ a.toNat < 0 + 0) ∨
          Within a (vecPtr t (msp + 424)) ((vecCap t (msp + 424)).toNat * 16))) := by
    intro a ha
    rw [hP]
    rcases ha with ha | ha | ha
    · exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hE, hP1, hP2, hm16, b6],
        by addr_omega [ha, hE, hP2, hm16, b6], fun h' ↦ by addr_omega [h', ha, hE, mo, hP2, hm16, b1, b2, b3, b4, b8],
        fun h' ↦ by addr_omega [h', ha, hE, mo, hP2, hm16, b1, b2, b3, b4, b8]⟩))))),
        by addr_omega [ha, hE, hP2, hm16, b6], by addr_omega [ha, hE, hP2, hm16, b6]⟩,
        by addr_omega [ha, hE, hP2, hm16, b6], by addr_omega [ha, hE, hP2, hm16, b6],
        by addr_omega [ha, hE, hP2, hm16, b6], Or.inr (Or.inr (Or.inr (Or.inr
          (by addr_omega [ha, hE, hP2, hm16, b6]))))⟩
    · exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hE, hP1, hP2, hm16, b6],
        by addr_omega [ha, hE, hP2, hm16, b6], fun h' ↦ by addr_omega [h', ha, hE, mo, hP2, hm16, b1, b2, b3, b4, b8],
        fun h' ↦ by addr_omega [h', ha, hE, mo, hP2, hm16, b1, b2, b3, b4, b8]⟩))))),
        by addr_omega [ha, hE, hP2, hm16, b6], by addr_omega [ha, hE, hP2, hm16, b6]⟩,
        by addr_omega [ha, hE, hP2, hm16, b6], by addr_omega [ha, hE, hP2, hm16, b6],
        by addr_omega [ha, hE, hP2, hm16, b6], Or.inr (Or.inr (Or.inr (Or.inr
          (by addr_omega [ha, hE, hP2, hm16, b6]))))⟩
    · exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha])))), by addr_omega [ha],
        by addr_omega [ha]⟩, by addr_omega [ha], by addr_omega [ha], by addr_omega [ha],
        Or.inr (Or.inl (by addr_omega [ha, b6]))⟩
  have K : ∀ c : Nat, c = 424 ∨ c = 432 ∨ c = 288 →
      v.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) :=
    fun c hc ↦ hf.getMem (by rcases hc with rfl | rfl | rfl <;> decide) fun j hj hw ↦ by
      rcases hc with rfl | rfl | rfl <;> rcases hw with hw | hw | hw <;>
        addr_omega [hw, hj, hE, hP2, hm16, b6]
  have hn : heapNext v = heapNext t := by
    simp only [heapNext]
    rw [hf.getMem (a := nextAddr) (by decide) fun j hj hw ↦ by
      rcases hw with hw | hw | hw <;> addr_omega [hw, hj, hE, hP2, hm16, b6]]
  have hheap : HeapOk v := ⟨by rw [hn]; exact rc.k.ng.heap.lo, by rw [hn]; exact rc.k.ng.heap.hi⟩
  have rb' := rb.frame hf (fun a ha ↦ (hWb a ha).1) (fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact kv _ (by decide)) hheap
    (le_of_eq hn.symm)
  have pv : vecPtr v (msp + 424) = vecPtr t (msp + 424) := K 432 (by simp)
  have cv : vecCap v (msp + 424) = vecCap t (msp + 424) := K 424 (by simp)
  have lv : vecLen v (msp + 424) = vecLen t (msp + 424) + 1 := by
    have e := b80000730_m_x2_440 hv
    rw [hsp, h.x9] at e
    exact e
  have lv' : (vecLen v (msp + 424)).toNat = (vecLen t (msp + 424)).toNat + 1 := by
    rw [lv]; addr_omega [hlt, hP2, hm16, b6]
  have hc31 := rfold_end_le words i L g st (k + 1)
  have hLle : L ≤ 2 ^ 14 := by have := rc.k.hL; omega
  have x25' : t.getReg .x25 + t.getReg .x27 = BitVec.ofNat 64 (rfold words i L g st (k + 1)).2.1 := by
    rw [h.x25, h.x27, rfold_succ, ← BitVec.ofNat_add]
    simp only [Model.runStep]
    rw [Nat.add_comm]
  have m1' : v.getMem (t.getMem (msp + 432) + BitVec.ofNat 64 (16 * (vecLen t (msp + 424)).toNat)) =
      t.getReg .x24 := by
    have e := b80000730_m1 hv; rw [hsp, h.x9, hEe] at e; exact e
  have m0' : v.getMem (t.getMem (msp + 432) +
      BitVec.ofNat 64 (16 * (vecLen t (msp + 424)).toNat) + 8) = t.getReg .x25 + t.getReg .x27 := by
    have e := b80000730_m0 hv; rw [hsp, h.x9, hEe] at e; exact e
  have hl : wordsAt v (vecPtr v (msp + 424)) (vecLen v (msp + 424)).toNat =
      (rfold words i L g st (k + 1)).2.2 := by
    rw [pv, lv', hP, wordsAt_snoc (t := t)
      (fun j hj ↦ ⟨hf.getMem (by addr_omega [hpal, hj, hE, hP2, hm16, b6]) fun x hx hw ↦ by
          rcases hw with hw | hw | hw <;> addr_omega [hw, hx, hj, hE, hP2, hm16, b6],
        hf.getMem (by addr_omega [hpal, hj, hE, hP2, hm16, b6]) fun x hx hw ↦ by
          rcases hw with hw | hw | hw <;> addr_omega [hw, hx, hj, hE, hP2, hm16, b6]⟩)
      m1' m0', ← hP]
    have e := h.vs.vecs.words
    simp only at e
    rw [e, rfold_succ, h.x24, x25', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [rfold_succ, Model.runStep]
  have vs' := h.vs.setW (l := (rfold words i L g st (k + 1)).2.2) hf (fun a ha ↦ (hWb a ha).2)
    (le_of_eq hn.symm) hheap.hi
    ⟨by rw [lv', cv]; omega, by rw [pv]; exact bw.al, by rw [pv, cv, hn]; exact bw.buf⟩
    (by simp only [VMiss, pv, cv]; exact mw) (Or.inl ⟨pv, cv⟩) hl
  have next' : v.readWords N (k + 1) = (rfold words i L g st (k + 1)).1.map (BitVec.ofNat 64) := by
    rw [rwords_keep rb.nal (by omega) fun a ha ↦ hf a fun hw ↦ by
      rcases hw with hw | hw | hw
      · addr_omega [hw, ha, hE, mo, hP2, hm16, b1, b2, b3, b4, b8, hk]
      · addr_omega [hw, ha, hE, mo, hP2, hm16, b1, b2, b3, b4, b8, hk]
      · addr_omega [hw, ha, b4, b5, b6, hk]]
    exact h.next
  have x27' : v.getReg .x27 = BitVec.ofNat 64 (rfold words i L g st (k + 1)).2.1 := by
    rw [b80000730_x27 hv]; exact x25'
  by_cases hkn : k + 1 = g.2.2.length
  · refine ⟨v, rv, Or.inr ⟨b80000730_pc_taken hv (by rw [rb.x18, h.x23, hkn]), hkn, ?_⟩⟩
    refine ⟨rb', by rw [← hkn]; exact vs', by rw [← hkn]; exact next', ?_,
      by rw [kv .x12 (by decide), h.x12], by rw [← hkn]; exact x27'⟩
    rw [b80000730_x9 hv, h.x9, ← hkn]
    apply BitVec.eq_of_toNat_eq
    rw [← lv, lv', hlen, rfold_succ, BitVec.toNat_ofNat]
    simp only [Model.runStep, List.length_append, List.length_singleton]
    have : (rfold words i L g st k).2.2.length < 2 ^ 31 := by
      rw [← hlen]; exact bw.len_lt (by decide) (by simp only [heapNext, heapEnd]; omega)
    omega
  · refine ⟨v, rv, Or.inl ⟨b80000730_pc_not_taken hv fun e ↦ hkn ?_, rb', vs', by omega, next', ?_,
      ?_, ?_, ?_, x27'⟩⟩
    · rw [rb.x18, h.x23] at e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      omega
    · rw [← h.m288]; exact K 288 (by simp)
    · rw [kv .x12 (by decide), h.x12]
    · rw [b80000730_x19 hv, h.x19, show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add]; rfl
    · rw [kv .x23 (by decide), h.x23]

end

section
variable {s u₀ : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 : Nat}

/-- The runs' loop, from the `k`th word to its exit at `0x800007b8`. -/
theorem runs_loop : ∀ m k (t : MachineState), g.2.2.length - k = m →
    RN s words u₀ i L Hb st g D C N H1 k t → t.pc = 0x80000758 →
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x800007b8 ∧ RE s words u₀ i L Hb st g D C N H1 v)) := by
  intro m
  induction m with
  | zero => intro k t hm h _; have := h.hk; omega
  | succ m ih =>
    intro k t hm h hpc
    have push : ∀ t₁, Reaches Image.code t t₁ → RQ s words u₀ i L Hb st g D C N H1 k t₁ →
        t₁.pc = 0x80000730 → vecLen t₁ (msp + 424) ≠ vecCap t₁ (msp + 424) →
        ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
          (v.pc = 0x800007b8 ∧ RE s words u₀ i L Hb st g D C N H1 v)) := by
      intro t₁ r₁ h₁ hpc₁ hr
      obtain ⟨t₂, r₂, ⟨hpc₂, h₂⟩ | ⟨hpc₂, -, h₂⟩⟩ := runs_push h₁ hpc₁ hr
      · obtain ⟨v, rv, hv⟩ := ih (k + 1) t₂ (by omega) h₂ hpc₂
        exact ⟨v, r₁.trans (r₂.trans rv), hv⟩
      · exact ⟨t₂, r₁.trans r₂, Or.inr ⟨hpc₂, h₂⟩⟩
    obtain ⟨t₁, r₁, h₁, ⟨hpc₁, hr⟩ | ⟨hpc₁, hfull⟩⟩ := runs_head h hpc
    · exact push t₁ r₁ h₁ hpc₁ hr
    · obtain ⟨t₂, r₂, hd | ⟨h₂, hpc₂, hr⟩⟩ := runs_grow h₁ hpc₁ hfull
      · exact ⟨t₂, r₁.trans r₂, Or.inl hd⟩
      · exact push t₂ (r₁.trans r₂) h₂ hpc₂ hr

/-- The runs, from `0x800006dc` to `0x800007b8`. -/
theorem runs_phase {t : MachineState} {H : Nat}
    (h : CL s words u₀ i L Hb st g D H C L (cfold words i g L) t) (hpc : t.pc = 0x800006dc) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ N H1, v.pc = 0x800007b8 ∧
      RE s words u₀ i L Hb st g D C N H1 v) := by
  obtain ⟨t₁, r₁, hd | ⟨N, hpc₁, h₁⟩⟩ := runs_entry h hpc
  · exact ⟨t₁, r₁, Or.inl hd⟩
  obtain ⟨v, rv, hd | ⟨hpcv, hv⟩⟩ := runs_loop _ 0 t₁ rfl h₁ hpc₁
  · exact ⟨v, r₁.trans rv, Or.inl hd⟩
  · exact ⟨v, r₁.trans rv, Or.inr ⟨N, _, hpcv, hv⟩⟩

end

end Rv64Verifier.Proofs.Main
