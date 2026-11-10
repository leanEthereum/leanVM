import Rv64Verifier.Proofs.Main.NewResize

/-!
# `Bytecode::new`'s blocks: the placement

`pfold`: `positions` and `next` after the placement's first `q` positions. `resize_end`:
`0x8000082c` sets `positions`' length to `end`, into the placement's loop (`PL`, at
`0x8000085c`); `place_step` places one position, `place_adv` moves on; `place_phase`: from the
runs' exit to the loop's (`0x800008a0`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

/-- `positions` and `next` after the placement's first `q` positions. -/
def pfold (words : List Word) (i L : Nat) (g : GrpSt) (st : Model.NewState) (q : Nat) :
    List (BitVec 16) × List Nat :=
  (List.range q).foldl (Model.placeStep (blk words i) g.2.1)
    (Model.resizeRust st.positions (rend words i L g st), (rfold words i L g st g.2.2.length).1)

section
variable (words : List Word) (i L : Nat) (g : GrpSt) (st : Model.NewState)

theorem pfold_succ (q : Nat) : pfold words i L g st (q + 1) =
    Model.placeStep (blk words i) g.2.1 (pfold words i L g st q) q := by
  simp only [pfold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem pfold_len : ∀ q, (pfold words i L g st q).1.length = rend words i L g st ∧
    (pfold words i L g st q).2.length = g.2.2.length
  | 0 => by
    refine ⟨?_, by simp only [pfold, List.range_zero, List.foldl_nil]
                   exact (rfold_spec words i L g st g.2.2.length).1⟩
    simp only [pfold, List.range_zero, List.foldl_nil, Model.resizeRust, List.length_append,
      List.length_take, List.length_replicate]
    omega
  | q + 1 => by
    obtain ⟨h1, h2⟩ := pfold_len q
    rw [pfold_succ, Model.placeStep]
    split
    · refine ⟨?_, ?_⟩ <;> simp [h1, h2]
    · exact ⟨h1, h2⟩

end

/-- In the placement's loop at position `p`, the first `q` placed (`q = p` at its head
`0x8000085c`, `q = p + 1` at `0x80000848`). -/
structure PL (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C N : Word) (H1 p q : Nat) (t : MachineState) : Prop where
  rc : RC s words u₀ i L Hb st g D C H1 t
  nal : N.toNat % 8 = 0
  nlo : C.toNat + 8 * g.2.2.length ≤ N.toNat
  nhi : N.toNat + 8 * g.2.2.length ≤ H1
  m24 : t.getMem (msp + 24) = BitVec.ofNat 64 ((words.getD 0 0).toNat - 2 ^ 14 * i - L)
  vs : VS u₀ Hb H1 0 0 { { st with words := (rfold words i L g st g.2.2.length).2.2 } with
    positions := (pfold words i L g st q).1 } t
  next : t.readWords N g.2.2.length = (pfold words i L g st q).2.map (BitVec.ofNat 64)
  hp : p < L
  x8 : t.getReg .x8 = u₀.getReg .x8
  x9 : t.getReg .x9 = BitVec.ofNat 64 (rfold words i L g st g.2.2.length).2.2.length
  x10 : t.getReg .x10 = BitVec.ofNat 64 p
  x11 : t.getReg .x11 = N
  x12 : t.getReg .x12 = u₀.getReg .x9 + BitVec.ofNat 64 (2 * p)
  x18 : t.getReg .x18 = BitVec.ofNat 64 g.2.2.length
  x19 : t.getReg .x19 = vecPtr t (msp + 448)
  x20 : t.getReg .x20 = BitVec.ofNat 64 (8 * (L - p))
  x21 : t.getReg .x21 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i + p))
  x25 : t.getReg .x25 = D + BitVec.ofNat 64 (8 * g.2.2.length)
  x27 : t.getReg .x27 = BitVec.ofNat 64 (rend words i L g st)

section
variable {s u₀ t₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 : Nat}

/-- `0x8000082c`: `positions`' length set to `end`, into the placement's loop. -/
theorem resize_end (h : RY s words u₀ i L Hb st g D C N H1 t₀ t) (hpc : t.pc = 0x8000082c) :
    ∃ v, Reaches Image.code t v ∧ v.pc = 0x8000085c ∧ PL s words u₀ i L Hb st g D C N H1 0 0 v := by
  have re := h.re
  have rc := re.rb.rc
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := re.rb.bounds
  have hsp := h.x2
  have bp := re.vs.bufs.p
  have hmo := h.mono
  have hhi := h.heap.hi
  simp only [heapNext, heapEnd] at hmo hhi
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b8000082c_spec hpc (by rv_eval [hsp, msp]; decide)
  have kv := b8000082c_keeps hv
  have hfv := holds_slots hv hsp [464] (by decide) (by decide)
  have hspv : v.getReg .x2 = msp := (kv .x2 (by decide)).trans hsp
  -- the frame from `t₀`
  have hWz : ∀ a, Wz (heapNext t₀) (vecPtr t₀ (msp + 448)) ((vecCap t₀ (msp + 448)).toNat * 2) a →
      (Wr (heapNext u₀) D C g.2.2.length a ∧ ¬ Within a (msp + 24) 8 ∧ ¬ Within a (msp + 280) 8) ∧
      (¬ Within a (msp + 400) 24 ∧ ¬ Within a (msp + 424) 24 ∧ ¬ Within a (msp + 240) 24 ∧
        (a.toNat < heapNext u₀ ∨ heapNext t₀ ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
          (0 ≤ a.toNat ∧ a.toNat < 0 + 0) ∨
          Within a (vecPtr t₀ (msp + 448)) ((vecCap t₀ (msp + 448)).toNat * 2))) := by
    intro a ha
    have mo := re.vs.mp.1
    simp only [heapNext]
    rcases ha with ha | ha | ha | ⟨ha1, ha2⟩ | ha
    · exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha])))), by addr_omega [ha],
        by addr_omega [ha]⟩, by addr_omega [ha], by addr_omega [ha], by addr_omega [ha],
        Or.inr (Or.inl (by addr_omega [ha, b6]))⟩
    · exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))), by addr_omega [ha],
        by addr_omega [ha]⟩, by addr_omega [ha], by addr_omega [ha], by addr_omega [ha],
        Or.inr (Or.inl (by addr_omega [ha, b6]))⟩
    · exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))), by addr_omega [ha],
        by addr_omega [ha]⟩, by addr_omega [ha], by addr_omega [ha], by addr_omega [ha],
        Or.inr (Or.inl (by addr_omega [ha, b6]))⟩
    · simp only [heapNext] at ha1
      simp only [heapEnd] at ha2
      exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapEnd]; omega,
        fun h' ↦ by addr_omega [h', ha1, b2, b3, b4, b5],
        fun h' ↦ by addr_omega [h', ha1, b3, b4, b5]⟩))))), by addr_omega [ha2],
        by addr_omega [ha2]⟩, by addr_omega [ha2], by addr_omega [ha2], by addr_omega [ha2],
        Or.inr (Or.inl ha1)⟩
    · rcases bp.buf with h0 | ⟨h1, h2⟩
      · simp only [Within] at ha; omega
      · simp only [heapNext] at h1 h2
        exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, h1],
          by simp only [heapEnd]; addr_omega [ha, h2, b6],
          fun h' ↦ by addr_omega [h', ha, mo, b1, b2, b3, b4, b8],
          fun h' ↦ by addr_omega [h', ha, mo, b1, b2, b3, b4, b8]⟩))))),
          by addr_omega [ha, h2, b6], by addr_omega [ha, h2, b6]⟩,
          by addr_omega [ha, h2, b6], by addr_omega [ha, h2, b6], by addr_omega [ha, h2, b6],
          Or.inr (Or.inr (Or.inr (Or.inr ha)))⟩
  have hW : ∀ a, (Wz (heapNext t₀) (vecPtr t₀ (msp + 448)) ((vecCap t₀ (msp + 448)).toNat * 2) a ∨
      ∃ c ∈ [464], Within a (msp + BitVec.ofNat 64 c) 8) →
      (Wr (heapNext u₀) D C g.2.2.length a ∧ ¬ Within a (msp + 24) 8 ∧ ¬ Within a (msp + 280) 8) ∧
      (¬ Within a (msp + 400) 24 ∧ ¬ Within a (msp + 424) 24 ∧ ¬ Within a (msp + 240) 24 ∧
        (a.toNat < heapNext u₀ ∨ heapNext t₀ ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
          (0 ≤ a.toNat ∧ a.toNat < 0 + 0) ∨
          Within a (vecPtr t₀ (msp + 448)) ((vecCap t₀ (msp + 448)).toNat * 2))) := by
    intro a ha
    rcases ha with ha | ⟨c, hc, ha⟩
    · exact hWz a ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp only [heapNext]
      exact ⟨⟨Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha])))), by addr_omega [ha],
        by addr_omega [ha]⟩, by addr_omega [ha], by addr_omega [ha], by addr_omega [ha],
        Or.inr (Or.inl (by addr_omega [ha, b6]))⟩
  have hf : BFrame t₀ v fun a ↦
      Wz (heapNext t₀) (vecPtr t₀ (msp + 448)) ((vecCap t₀ (msp + 448)).toNat * 2) a ∨
      ∃ c ∈ [464], Within a (msp + BitVec.ofNat 64 c) 8 := fun a ha ↦ by
    rw [hfv a fun h' ↦ ha (Or.inr h')]; exact h.frame a fun h' ↦ ha (Or.inl h')
  have hK : ∀ c : Nat, c % 8 = 0 → c < 4096 → c ≠ 464 →
      v.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := fun c h8 hc hne ↦
    slots_keepMsp hfv ⟨h8, hc, by simp only [List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; omega⟩
  have hn : heapNext v = heapNext t := by
    simp only [heapNext]
    rw [hfv.getMem (a := nextAddr) (by decide) fun j hj ⟨c, hc, hin⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; addr_omega [hin, hj]]
  have hheap : HeapOk v := ⟨by rw [hn]; exact h.heap.lo, by rw [hn]; exact h.heap.hi⟩
  have hmono : heapNext t₀ ≤ heapNext v := by rw [hn]; exact h.mono
  have p1 : vecPtr v (msp + 448) = vecPtr t (msp + 448) := hK 456 (by decide) (by decide) (by decide)
  have c1 : vecCap v (msp + 448) = vecCap t (msp + 448) := hK 448 (by decide) (by decide) (by decide)
  have l1 : vecLen v (msp + 448) = BitVec.ofNat 64 (rend words i L g st) := by
    have e := b8000082c_m_x2_464 hv
    rw [hsp, h.x27] at e
    exact e
  have hE := h.capE
  have hE32 : rend words i L g st < 2 ^ 32 := by
    have := re.posFacts; simp only [rend] at this ⊢; omega
  have l1' : (vecLen v (msp + 448)).toNat = rend words i L g st := by
    rw [l1, BitVec.toNat_ofNat]; omega
  have vin := h.vin
  have hl : halvesAt v (vecPtr v (msp + 448)) (vecLen v (msp + 448)).toNat =
      (pfold words i L g st 0).1 := by
    rw [p1, l1']
    refine Eq.trans ?_ h.pos
    rcases vin.buf with h0 | ⟨hP1, hP2⟩
    · have : rend words i L g st = 0 := by omega
      rw [this]; rfl
    simp only [heapNext] at hP2
    exact halvesAt_keep vin.al (fun x hx1 hx2 ↦ hfv x fun ⟨c, hc, hin⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; addr_omega [hin, hx1, hx2, hP2, hE, hhi]) (by omega)
  have vs' := re.vs.setP (l := (pfold words i L g st 0).1) hf (fun a ha ↦ (hW a ha).2) hmono
    hheap.hi ⟨by rw [l1', c1]; exact hE, by rw [p1]; exact vin.al, by
      rw [p1, c1, hn]; exact vin.buf⟩
    (by
      simp only [VMiss, p1, c1]
      rcases h.sf with ⟨e1, e2⟩ | h0 | hfr
      · rw [e1, e2]; exact re.vs.mp
      · exact ⟨Or.inl h0, Or.inl h0⟩
      · simp only [heapNext] at hfr
        exact ⟨Or.inr (Or.inr (Or.inl (by omega))), Or.inr (Or.inr (Or.inr (by omega)))⟩)
    (by rw [p1, c1]; exact h.sf) hl
  have hm280 : t.getMem (msp + 280) = N := by
    rw [← re.rb.m280]
    exact h.frame.getMem (by decide) fun j hj hw ↦ (hWz _ hw).1.2.2 (by addr_omega [hj])
  have R : ∀ r ∈ ([.x8, .x9, .x18, .x20, .x21, .x27] : List Reg), v.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact kv _ (by decide)
  refine ⟨v, rv, b8000082c_pc hv, ⟨rc.frame hf (fun a ha ↦ (hW a ha).1.1) hspv hheap hmono,
    re.rb.nal, re.rb.nlo, re.rb.nhi, ?_, vs', ?_,
    by have := rc.k.hL; have := rc.k.lt; omega, (R .x8 (by simp)).trans h.x8,
    (R .x9 (by simp)).trans h.x9, by rw [b8000082c_x10 hv]; rfl, by rw [b8000082c_x11 hv, hsp, hm280],
    by rw [b8000082c_x12 hv, h.x15]; simp, (R .x18 (by simp)).trans h.x18,
    by rw [kv .x19 (by decide), h.x19, p1], by rw [R .x20 (by simp), h.x20, Nat.sub_zero],
    by rw [R .x21 (by simp), h.x21, Nat.add_zero], ?_, (R .x27 (by simp)).trans h.x27⟩⟩
  · rw [← re.rb.m24]
    exact hf.getMem (by decide) fun j hj hw ↦ (hW _ hw).1.2.1 (by addr_omega [hj])
  · rw [rwords_keep re.rb.nal (by omega) fun a ha ↦ hf a fun hw ↦ by
      have mo := re.vs.mp.1
      rcases hw with (h1 | h1 | h1 | ⟨h1, h2⟩ | h1) | ⟨c, hc, h1⟩
      · addr_omega [h1, ha, b4, b5, b6, b8]
      · addr_omega [h1, ha, b4, b5, b6, b8]
      · addr_omega [h1, ha, b4, b5, b6, b8]
      · simp only [heapNext] at h1; addr_omega [h1, ha, b4, b5, b8]
      · addr_omega [h1, ha, mo, b1, b2, b3, b4, b8]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc; addr_omega [h1, ha, b4, b5, b6, b8]]
    exact re.next
  · rw [b8000082c_x25 hv, h.x12, h.x18]
    apply BitVec.eq_of_toNat_eq
    addr_omega [b2, b3, b4, b5, b6, b9]

end

section
variable (words : List Word) (i L : Nat) (g : GrpSt) (st : Model.NewState)

theorem rfold_next_le : ∀ k, ∀ x ∈ (rfold words i L g st k).1, x ≤ (rfold words i L g st k).2.1
  | 0 => by simp [rfold]
  | k + 1 => by
    intro x hx
    rw [rfold_succ] at hx ⊢
    simp only [Model.runStep, List.mem_append, List.mem_singleton] at hx ⊢
    rcases hx with hx | rfl
    · have := rfold_next_le k x hx; omega
    · omega

theorem getD_le_of_forall {l : List Nat} {b j : Nat} (h : ∀ x ∈ l, x ≤ b) : l.getD j 0 ≤ b := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hj : j < l.length
  · rw [List.getElem?_eq_getElem hj]; exact h _ (List.getElem_mem hj)
  · rw [List.getElem?_eq_none (by omega)]; exact Nat.zero_le _

theorem pfold_next_le : ∀ q, ∀ x ∈ (pfold words i L g st q).2, x ≤ rend words i L g st + q
  | 0 => fun x hx ↦ rfold_next_le words i L g st _ x hx
  | q + 1 => by
    intro x hx
    have ih := pfold_next_le q
    rw [pfold_succ, Model.placeStep] at hx
    split at hx
    · rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · have := ih x hx; omega
      · have := getD_le_of_forall (j := ((g.2.1.getD q 0).toNat)) ih; omega
    · have := ih x hx; omega

end

section
variable {s u₀ t t' : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 p q : Nat}

/-- A step that writes no memory and changes no register `PL` names. -/
theorem PL.same (h : PL s words u₀ i L Hb st g D C N H1 p q t) (hm : ∀ a, t'.getMem a = t.getMem a)
    (hr : ∀ r, r ≠ .x13 → r ≠ .x14 → t'.getReg r = t.getReg r) :
    PL s words u₀ i L Hb st g D C N H1 p q t' := by
  have hn : heapNext t' = heapNext t := by simp only [heapNext, hm]
  have hsp : t'.getReg .x2 = msp := (hr .x2 (by decide) (by decide)).trans h.rc.k.ng.sp
  have hf : BFrame t t' (fun _ ↦ False) := BFrame.of_same hm _
  have hhi := h.rc.k.ng.heap.hi
  refine ⟨h.rc.frame hf (fun _ h ↦ h.elim) hsp ⟨by rw [hn]; exact h.rc.k.ng.heap.lo,
    by rw [hn]; exact hhi⟩ (le_of_eq hn.symm), h.nal, h.nlo, h.nhi, by rw [hm]; exact h.m24,
    h.vs.frame hf (fun _ h ↦ h.elim) (le_of_eq hn.symm) (by rw [hn]; exact hhi),
    by rw [rwords_same hm]; exact h.next, h.hp, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hr _ (by decide) (by decide), h.x19]; exact (hm _).symm, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [hr _ (by decide) (by decide)]; first
        | exact h.x8 | exact h.x9 | exact h.x10 | exact h.x11 | exact h.x12 | exact h.x18
        | exact h.x20 | exact h.x21 | exact h.x25 | exact h.x27)

end

theorem PL.congr {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat}
    {st : Model.NewState} {g : GrpSt} {D C N : Word} {H1 p q q' : Nat}
    (h : PL s words u₀ i L Hb st g D C N H1 p q t)
    (e : pfold words i L g st q = pfold words i L g st q') :
    PL s words u₀ i L Hb st g D C N H1 p q' t :=
  ⟨h.rc, h.nal, h.nlo, h.nhi, h.m24, by rw [← e]; exact h.vs, by rw [← e]; exact h.next, h.hp,
    h.x8, h.x9, h.x10, h.x11, h.x12, h.x18, h.x19, h.x20, h.x21, h.x25, h.x27⟩

/-- At `0x8000088c`, position `p` with a nonzero word, before its store: `next[g]` at `a3`,
`&positions[next[g]]` at `a4`. -/
structure PF (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C N : Word) (H1 p : Nat) (t : MachineState) : Prop where
  pl : PL s words u₀ i L Hb st g D C N H1 p p t
  nz : (blk words i).getD p 0 ≠ 0
  gl : (g.2.1.getD p 0).toNat < g.2.2.length
  lt : (pfold words i L g st p).2.getD (g.2.1.getD p 0).toNat 0 < rend words i L g st
  x13 : t.getReg .x13 = N + BitVec.ofNat 64 (8 * (g.2.1.getD p 0).toNat)
  x14 : t.getReg .x14 = vecPtr t (msp + 448) +
    BitVec.ofNat 64 (2 * (pfold words i L g st p).2.getD (g.2.1.getD p 0).toNat 0)

theorem setWidth16_ofNat (p : Nat) : (BitVec.ofNat 64 p).truncate 16 = BitVec.ofNat 16 p := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 p : Nat}

/-- `0x8000085c`: position `p` placed, to `0x80000848`. -/
theorem place_front (h : PL s words u₀ i L Hb st g D C N H1 p p t) (hpc : t.pc = 0x8000085c) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x80000848 ∧ PL s words u₀ i L Hb st g D C N H1 p (p + 1) v) ∨
      (v.pc = 0x8000088c ∧ PF s words u₀ i L Hb st g D C N H1 p v)) := by
  have rc := h.rc
  have hfit := rc.k.a.inv.fits
  simp only [inputWords] at hfit
  have hlen := rc.k.a.len
  have hlt := rc.k.lt
  have hL := rc.k.hL
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hp := h.hp
  have hL14 : L ≤ 2 ^ 14 := by omega
  have hGO := rc.k.a.groupOf
  have hSL := rc.k.a.slots
  have hhi := rc.k.ng.heap.hi
  have hH0 := rc.k.ng.mono
  simp only [heapStart] at hSL
  simp only [heapNext, heapEnd] at hGO hhi hH0
  have hw : t.getMem (t.getReg .x21) = (blk words i).getD p 0 := by
    rw [h.x21, blk_getD (by omega) (by omega) hlen, ← (rc.k.ng.minv rc.k.a).input _ (by omega)]
  -- `0x8000085c`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000085c_spec hpc (by
    rv_eval []
    rw [h.x21]
    exact (Sym.validAccess_eight _).mpr ⟨Or.inl ⟨by addr_omega [hib, hfit, hlen, hlt, hL, hp],
      by addr_omega [hib, hfit, hlen, hlt, hL, hp]⟩, by addr_omega [hib, hfit, hlen, hlt, hL, hp]⟩)
  have pl₁ := h.same (b8000085c_mem_same h₁) fun r h13 h14 ↦ by
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | contradiction | exact b8000085c_keeps h₁ _ (by decide) | rfl
  by_cases hz : (blk words i).getD p 0 = 0
  · have e : pfold words i L g st p = pfold words i L g st (p + 1) := by
      simp only [pfold_succ, Model.placeStep, ne_eq, hz, not_true_eq_false, ↓reduceIte]
    exact ⟨t₁, r₁, Or.inr (Or.inl ⟨b8000085c_pc_taken h₁ (by rw [hw, hz]), pl₁.congr e⟩)⟩
  -- `0x80000864`
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b80000864_spec
    (b8000085c_pc_not_taken h₁ (by rw [hw]; exact hz)) trivial
  have pl₂ := pl₁.same (b80000864_mem_same h₂) fun r h13 h14 ↦ by
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | contradiction | exact b80000864_keeps h₂ _ (by decide) | rfl
  have hpc₂ := b80000864_pc_not_taken h₂ (by rw [pl₁.x10]; exact shr14_eq_zero (by omega))
  -- `0x8000086c`: `group_of[p]`
  obtain ⟨t₃, r₃, hpc₃, hr₃, hm₃⟩ := step_lhu (code := Image.code) (s := t₂) (rd := .x13)
    (rs1 := .x12) (off := 0) (by rw [hpc₂]; exact fetch_of (by decide +kernel))
    (by
      rw [off0, pl₂.x12]
      exact valid2_of (by addr_omega [hSL, hGO, hp, hL14]) (by addr_omega [hGO, hp, hL14, hhi, hH0])
        (by addr_omega [hGO, hp, hL14]))
  rw [off0, pl₂.x12] at hr₃
  have hgo : t₂.getHalfword (u₀.getReg .x9 + BitVec.ofNat 64 (2 * p)) = g.2.1.getD p 0 := by
    rw [← pl₂.rc.go, halvesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega)]
    rfl
  have x13₃ : t₃.getReg .x13 = (g.2.1.getD p 0).zeroExtend 64 := by rw [hr₃]; simp [hgo]
  have pl₃ := pl₂.same hm₃ fun r h13 _ ↦ by rw [hr₃]; simp [h13]
  have hgvn : ((g.2.1.getD p 0).zeroExtend 64 : Word).toNat = (g.2.1.getD p 0).toNat := by
    simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
    have := (g.2.1.getD p 0).isLt
    omega
  -- `0x80000870`
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches NB.g80000870_spec (by rw [hpc₃, hpc₂]; rfl) trivial
  have pl₄ := pl₃.same (NB.g80000870_mem_same h₄) fun r _ _ ↦ by
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | exact NB.g80000870_keeps h₄ _ (by decide) | rfl
  have x13₄ : t₄.getReg .x13 = (g.2.1.getD p 0).zeroExtend 64 :=
    (NB.g80000870_keeps h₄ .x13 (by decide)).trans x13₃
  have bnd := pl₄.rc
  obtain ⟨b0, b1, b2, b3, b8, b9⟩ : (u₀.getMem nextAddr).toNat ≤ Hb ∧ Hb ≤ D.toNat ∧
      D.toNat + 8 * g.2.2.length ≤ C.toNat ∧ C.toNat + 8 * g.2.2.length ≤ H1 ∧
      0 < g.2.2.length ∧ g.2.2.length < 2 ^ 28 := by
    have h1 := rc.k.hb0
    have h2 := rc.h1
    have hpos : 0 < g.2.2.length := List.length_pos_iff.mpr rc.ne
    simp only [heapNext] at h1 h2
    exact ⟨h1, rc.dlo, rc.dc, rc.chi, hpos, by have := rc.chi; omega⟩
  have b4 := h.nlo
  have b5 := h.nhi
  by_cases hb : (t₃.getReg .x18).toNat ≤ (t₃.getReg .x13).toNat
  · obtain ⟨w, rw', hw'⟩ := abort (u := t₄) (by rw [NB.g80000870_pc_taken h₄ hb]; decide)
    exact ⟨w, r₁.trans (r₂.trans ((show Reaches Image.code t₂ t₃ from ⟨1, r₃⟩).trans
      (r₄.trans rw'))), Or.inl hw'⟩
  have hgl : (g.2.1.getD p 0).toNat < g.2.2.length := by
    rw [x13₃, hgvn, pl₃.x18, BitVec.toNat_ofNat] at hb
    omega
  have hpc₄ := NB.g80000870_pc_not_taken h₄ (by omega)
  have hm04 : ∀ a, t₄.getMem a = t.getMem a := fun a ↦ by
    rw [NB.g80000870_mem_same h₄, hm₃, b80000864_mem_same h₂, b8000085c_mem_same h₁]
  -- `0x80000874`: `next[g]`
  have hNg : (N + BitVec.ofNat 64 (8 * (g.2.1.getD p 0).toNat)).toNat =
      N.toNat + 8 * (g.2.1.getD p 0).toNat := by addr_omega [hgl, b5, rc.h1, hhi]
  have hA : t₄.getReg .x11 + t₄.getReg .x13 * 8 = N + BitVec.ofNat 64 (8 * (g.2.1.getD p 0).toNat) := by
    rw [pl₄.x11, x13₄]
    apply BitVec.eq_of_toNat_eq
    rw [hNg]
    addr_omega [hgvn, hgl, b5, rc.h1, hhi]
  have hnal := h.nal
  have hh1 := rc.h1
  simp only [heapNext] at hh1
  obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b80000874_spec hpc₄ (by
    rv_eval []
    rw [hA]
    exact (Sym.validAccess_eight _).mpr ⟨Or.inl ⟨by addr_omega [hNg, b0, b1, b2, b3, b4, hgl,
      rc.k.a.inv.heap.lo], by addr_omega [hNg, b5, hgl, hh1, hhi]⟩, by addr_omega [hNg, hnal]⟩)
  have hm₅ := b80000874_mem_same h₅
  have hnxl := (pfold_len words i L g st p).2
  have hat : t₄.getMem (N + BitVec.ofNat 64 (8 * (g.2.1.getD p 0).toNat)) =
      BitVec.ofNat 64 ((pfold words i L g st p).2.getD (g.2.1.getD p 0).toNat 0) := by
    rw [← rwords_getD hgl, pl₄.next, getD_map_ofNat (by rw [hnxl]; exact hgl)]
  have hatb := getD_le_of_forall (j := (g.2.1.getD p 0).toNat) (pfold_next_le words i L g st p)
  have hE : rend words i L g st < 2 ^ 31 := by
    have e := congrArg List.length h.vs.vecs.positions
    simp only [halvesAt, List.length_map, List.length_range] at e
    rw [(pfold_len words i L g st p).1] at e
    rw [← e]; exact h.vs.bufs.p.len_lt (by decide) (by simp only [heapNext, heapEnd]; omega)
  by_cases hab : (t₄.getReg .x27).toNat ≤
      (t₄.getMem (t₄.getReg .x11 + t₄.getReg .x13 * 8)).toNat
  · obtain ⟨w, rw', hw'⟩ := abort (u := t₅) (by rw [b80000874_pc_taken h₅ hab]; decide)
    exact ⟨w, r₁.trans (r₂.trans ((show Reaches Image.code t₂ t₃ from ⟨1, r₃⟩).trans
      (r₄.trans (r₅.trans rw')))), Or.inl hw'⟩
  have hlt' : (pfold words i L g st p).2.getD (g.2.1.getD p 0).toNat 0 < rend words i L g st := by
    rw [hA, hat, pl₄.x27, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hab
    omega
  have hpc₅ := b80000874_pc_not_taken h₅ (by omega)
  -- `positions`' buffer
  have vin := h.vs.bufs.p
  have hEl : (vecLen t (msp + 448)).toNat = rend words i L g st := by
    have e := congrArg List.length h.vs.vecs.positions
    simp only [halvesAt, List.length_map, List.length_range] at e
    rw [e, (pfold_len words i L g st p).1]
  have hlc := vin.len
  rw [hEl] at hlc
  obtain ⟨hP1, hP2⟩ := vin.buf.resolve_left (by omega)
  simp only [heapNext] at hP1 hP2
  have hpal := vin.al
  have hlo0 := rc.k.a.inv.heap.lo
  simp only [heapStart, heapNext] at hlo0
  have hPA : (vecPtr t (msp + 448) +
      BitVec.ofNat 64 (2 * (pfold words i L g st p).2.getD (g.2.1.getD p 0).toNat 0)).toNat =
      (vecPtr t (msp + 448)).toNat + 2 * (pfold words i L g st p).2.getD (g.2.1.getD p 0).toNat 0 := by
    addr_omega [hP2, hlc, hlt', hhi]
  have mo := h.vs.mp.1
  simp only [Out] at mo
  -- `0x80000884`
  obtain ⟨t₆, r₆, h₆⟩ := Sym.BlockSpec.reaches NB.g80000884_spec hpc₅ trivial
  have hm06 : ∀ a, t₆.getMem a = t.getMem a := fun a ↦ by
    rw [NB.g80000884_mem_same h₆, hm₅, hm04]
  have pl₆ := pl₄.same (fun a ↦ by rw [NB.g80000884_mem_same h₆, hm₅]) fun r h13 h14 ↦ by
    have e2 : t₆.getReg r = t₅.getReg r := by
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
      all_goals first | contradiction | exact NB.g80000884_keeps h₆ _ (by decide) | rfl
    have e3 : t₅.getReg r = t₄.getReg r := by
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
      all_goals first | contradiction | exact b80000874_keeps h₅ _ (by decide) | rfl
    rw [e2, e3]
  refine ⟨t₆, r₁.trans (r₂.trans ((show Reaches Image.code t₂ t₃ from ⟨1, r₃⟩).trans (r₄.trans
    (r₅.trans r₆)))), Or.inr (Or.inr ⟨NB.g80000884_pc h₆, pl₆, hz, hgl, hlt', ?_, ?_⟩)⟩
  · rw [NB.g80000884_keeps h₆ .x13 (by decide), b80000874_x13 h₅, hA]
  · rw [NB.g80000884_x14 h₆, b80000874_keeps h₅ .x19 (by decide), pl₄.x19, b80000874_x14 h₅, hA,
      hat]
    have e1 : vecPtr t₄ (msp + 448) = vecPtr t (msp + 448) := hm04 _
    have e2 : vecPtr t₆ (msp + 448) = vecPtr t (msp + 448) := hm06 _
    rw [e1, e2]
    apply BitVec.eq_of_toNat_eq
    rw [hPA]
    addr_omega [hP2, hlc, hlt', hhi]

end

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 p : Nat}

/-- `0x8000088c`: `positions[next[g]] = p`, `next[g] += 1`, to `0x80000848`. -/
theorem place_back (h : PF s words u₀ i L Hb st g D C N H1 p t) (hpc : t.pc = 0x8000088c) :
    ∃ v, Reaches Image.code t v ∧ v.pc = 0x80000848 ∧
      PL s words u₀ i L Hb st g D C N H1 p (p + 1) v := by
  have pl := h.pl
  have rc := pl.rc
  have hp := pl.hp
  have hz := h.nz
  have hgl := h.gl
  have hlt' := h.lt
  have hhi := rc.k.ng.heap.hi
  simp only [heapNext, heapEnd] at hhi
  obtain ⟨b0, b1, b2, b3, b8, b9⟩ : (u₀.getMem nextAddr).toNat ≤ Hb ∧ Hb ≤ D.toNat ∧
      D.toNat + 8 * g.2.2.length ≤ C.toNat ∧ C.toNat + 8 * g.2.2.length ≤ H1 ∧
      0 < g.2.2.length ∧ g.2.2.length < 2 ^ 28 := by
    have h1 := rc.k.hb0
    have h2 := rc.h1
    have hpos : 0 < g.2.2.length := List.length_pos_iff.mpr rc.ne
    simp only [heapNext] at h1 h2
    exact ⟨h1, rc.dlo, rc.dc, rc.chi, hpos, by have := rc.chi; omega⟩
  have b4 := pl.nlo
  have b5 := pl.nhi
  have hnal := pl.nal
  have hh1 := rc.h1
  simp only [heapNext] at hh1
  have hNg : (N + BitVec.ofNat 64 (8 * (g.2.1.getD p 0).toNat)).toNat =
      N.toNat + 8 * (g.2.1.getD p 0).toNat := by addr_omega [hgl, b5, hh1, hhi]
  have hnxl := (pfold_len words i L g st p).2
  have hat : t.getMem (N + BitVec.ofNat 64 (8 * (g.2.1.getD p 0).toNat)) =
      BitVec.ofNat 64 ((pfold words i L g st p).2.getD (g.2.1.getD p 0).toNat 0) := by
    rw [← rwords_getD hgl, pl.next, getD_map_ofNat (by rw [hnxl]; exact hgl)]
  have vin := pl.vs.bufs.p
  have hEl : (vecLen t (msp + 448)).toNat = rend words i L g st := by
    have e := congrArg List.length pl.vs.vecs.positions
    simp only [halvesAt, List.length_map, List.length_range] at e
    rw [e, (pfold_len words i L g st p).1]
  have hlc := vin.len
  rw [hEl] at hlc
  obtain ⟨hP1, hP2⟩ := vin.buf.resolve_left (by omega)
  simp only [heapNext] at hP1 hP2
  have hpal := vin.al
  have hlo0 := rc.k.a.inv.heap.lo
  simp only [heapStart, heapNext] at hlo0
  have hPA : (vecPtr t (msp + 448) +
      BitVec.ofNat 64 (2 * (pfold words i L g st p).2.getD (g.2.1.getD p 0).toNat 0)).toNat =
      (vecPtr t (msp + 448)).toNat + 2 * (pfold words i L g st p).2.getD (g.2.1.getD p 0).toNat 0 := by
    addr_omega [hP2, hlc, hlt', hhi]
  have mo := pl.vs.mp.1
  simp only [Out] at mo
  -- `0x8000088c`: `positions[at] = position`
  have hf₆ : Image.code.fetch t.pc = some (.base (.SH .x14 .x10 0)) := by
    rw [hpc]; exact fetch_of (by decide +kernel)
  obtain ⟨t₇, ht₇, hpc₇, hr₇, hh₇, hf₇⟩ := step_sh hf₆ (by
    rw [off0, h.x14]
    exact valid2_of (by addr_omega [hPA, hP1, hlo0]) (by addr_omega [hPA, hP2, hlc, hlt', hhi])
      (by addr_omega [hPA, hpal]))
  rw [off0, h.x14] at hh₇ hf₇
  rw [pl.x10, setWidth16_ofNat] at hh₇
  -- `0x80000890`: `next[g] += 1`
  have x13₇ : t₇.getReg .x13 = N + BitVec.ofNat 64 (8 * (g.2.1.getD p 0).toNat) := by
    rw [hr₇, h.x13]
  obtain ⟨t₈, r₈, h₈⟩ := Sym.BlockSpec.reaches NB.g80000890_spec (by
    rw [hpc₇, hpc]; rfl) (by
    rv_eval []
    rw [x13₇]
    exact (Sym.validAccess_eight _).mpr ⟨Or.inl ⟨by addr_omega [hNg, b0, b1, b2, b3, b4, hgl,
      hlo0], by addr_omega [hNg, b5, hgl, hh1, hhi]⟩, by addr_omega [hNg, hnal]⟩)
  have hf₈ : BFrame t₇ t₈ (Within · (N + BitVec.ofNat 64 (8 * (g.2.1.getD p 0).toNat)) 8) := by
    have e := BFrame.of_memFrame (NB.g80000890_frame h₈ (by rw [x13₇]; addr_omega [hNg, b5, hgl, hh1, hhi]))
      (by rw [x13₇]; addr_omega [hNg, hnal]) (by decide)
    rw [x13₇] at e
    exact e
  have hf : BFrame t t₈ fun a ↦ Within a (vecPtr t (msp + 448) +
      BitVec.ofNat 64 (2 * (pfold words i L g st p).2.getD (g.2.1.getD p 0).toNat 0)) 2 ∨
      Within a (N + BitVec.ofNat 64 (8 * (g.2.1.getD p 0).toNat)) 8 := fun a ha ↦ by
    have e1 := hf₈ a fun h' ↦ ha (Or.inr h')
    have e2 := hf₇.byte a fun h' ↦ ha (Or.inl (by
      rcases h' with h' | h' <;> rw [h'] <;> addr_omega [hPA, hP2, hlc, hlt', hhi]))
    rw [e1, e2]
  have hW : ∀ a, (Within a (vecPtr t (msp + 448) +
      BitVec.ofNat 64 (2 * (pfold words i L g st p).2.getD (g.2.1.getD p 0).toNat 0)) 2 ∨
      Within a (N + BitVec.ofNat 64 (8 * (g.2.1.getD p 0).toNat)) 8) →
      Wr (heapNext u₀) D C g.2.2.length a ∧ (¬ Within a (msp + 400) 24 ∧
        ¬ Within a (msp + 424) 24 ∧ ¬ Within a (msp + 240) 24 ∧
        (a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
          (0 ≤ a.toNat ∧ a.toNat < 0 + 0) ∨
          Within a (vecPtr t (msp + 448)) ((vecCap t (msp + 448)).toNat * 2))) := by
    intro a ha
    simp only [heapNext]
    rcases ha with ha | ha
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hPA, hP1],
        by simp only [heapEnd]; addr_omega [ha, hPA, hP2, hlc, hlt', hhi],
        fun h' ↦ by addr_omega [h', ha, hPA, mo, hP2, hlc, hlt', b1, b2, b3, b8],
        fun h' ↦ by addr_omega [h', ha, hPA, mo, hP2, hlc, hlt', b1, b2, b3, b8]⟩))))),
        by addr_omega [ha, hPA, hP2, hlc, hlt', hhi], by addr_omega [ha, hPA, hP2, hlc, hlt', hhi],
        by addr_omega [ha, hPA, hP2, hlc, hlt', hhi],
        Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hPA, hP2, hlc, hlt']))))⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hNg, b0, b1, b2, b4],
        by simp only [heapEnd]; addr_omega [ha, hNg, b5, hgl, hh1, hhi],
        fun h' ↦ by addr_omega [h', ha, hNg, b2, b4, hgl],
        fun h' ↦ by addr_omega [h', ha, hNg, b4, hgl]⟩))))),
        by addr_omega [ha, hNg, b5, hgl, hh1, hhi], by addr_omega [ha, hNg, b5, hgl, hh1, hhi],
        by addr_omega [ha, hNg, b5, hgl, hh1, hhi],
        Or.inr (Or.inr (Or.inl ⟨by addr_omega [ha, hNg, b1, b2, b4], by addr_omega [ha, hNg, b5, hgl]⟩))⟩
  have hK : ∀ c : Nat, c % 8 = 0 → c < 4096 →
      t₈.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := fun c h8 hc ↦
    hf.getMem (by addr_omega [h8, hc]) fun j hj hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hw, hj, hc, hPA, hP2, hlc, hlt', hhi]
      · addr_omega [hw, hj, hc, hNg, b5, hgl, hh1, hhi]
  have hn : heapNext t₈ = heapNext t := by
    simp only [heapNext]
    rw [hf.getMem (a := nextAddr) (by decide) fun j hj hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hw, hj, hPA, hP2, hlc, hlt', hhi]
      · addr_omega [hw, hj, hNg, b5, hgl, hh1, hhi]]
  have hheap : HeapOk t₈ := ⟨by rw [hn]; exact rc.k.ng.heap.lo, by rw [hn]; exact rc.k.ng.heap.hi⟩
  have p8 : vecPtr t₈ (msp + 448) = vecPtr t (msp + 448) := hK 456 (by decide) (by decide)
  have c8 : vecCap t₈ (msp + 448) = vecCap t (msp + 448) := hK 448 (by decide) (by decide)
  have l8 : vecLen t₈ (msp + 448) = vecLen t (msp + 448) := hK 464 (by decide) (by decide)
  have hl : halvesAt t₈ (vecPtr t₈ (msp + 448)) (vecLen t₈ (msp + 448)).toNat =
      (pfold words i L g st (p + 1)).1 := by
    rw [p8, l8, hEl]
    have e1 : halvesAt t₈ (vecPtr t (msp + 448)) (rend words i L g st) =
        halvesAt t₇ (vecPtr t (msp + 448)) (rend words i L g st) :=
      halvesAt_keep hpal (fun x hx1 hx2 ↦ hf₈ x fun h' ↦ by
        addr_omega [h', hx1, hx2, mo, hNg, b1, b2, b4, b5, hgl, hP2, hlc, b8]) (by omega)
    have e2 := halvesAt_set (t := t) (n := rend words i L g st) hpal (by omega) hlt'
      (fun a ha ↦ hf₇.byte a fun h' ↦ ha (by
        rcases h' with h' | h' <;> rw [h'] <;> addr_omega [hPA, hP2, hlc, hlt', hhi])) hh₇
    have e3 : halvesAt t (vecPtr t (msp + 448)) (rend words i L g st) = (pfold words i L g st p).1 := by
      have e := pl.vs.vecs.positions
      simp only at e
      rw [hEl] at e
      exact e
    rw [e1, e2, e3]
    simp only [pfold_succ, Model.placeStep, ne_eq, hz, not_false_eq_true, ↓reduceIte]
  have vs' := pl.vs.setP (l := (pfold words i L g st (p + 1)).1) hf (fun a ha ↦ (hW a ha).2)
    (le_of_eq hn.symm) hheap.hi (vin.keep c8 p8 l8 (le_of_eq hn.symm))
    (by simp only [VMiss, p8, c8]; exact pl.vs.mp) (Or.inl ⟨p8, c8⟩) hl
  have next' : t₈.readWords N g.2.2.length = (pfold words i L g st (p + 1)).2.map (BitVec.ofNat 64) := by
    have hv : t₈.getMem (N + BitVec.ofNat 64 (8 * (g.2.1.getD p 0).toNat)) =
        BitVec.ofNat 64 ((pfold words i L g st p).2.getD (g.2.1.getD p 0).toNat 0 + 1) := by
      have e := NB.g80000890_m_x13_0 h₈
      rw [x13₇] at e
      rw [e, BitVec.ofNat_add, ← hat, hf₇.getMem fun j hj hw ↦ by
        rcases hw with hw | hw <;> have := congrArg BitVec.toNat hw <;>
          addr_omega [this, hj, hNg, hPA, mo, hP2, hlc, hlt', b1, b2, b4, b5, hgl, b8, hh1, hhi]]
      rfl
    rw [rwords_set (t := t) hv fun j hj hne ↦ hf.getMem (by addr_omega [hnal, hj, b5, hh1, hhi])
      fun x hx hw ↦ by
        rcases hw with hw | hw
        · addr_omega [hw, hx, hj, hPA, mo, hP2, hlc, hlt', b1, b2, b4, b5, b8, hh1, hhi]
        · addr_omega [hw, hx, hj, hne, hNg, b5, hgl, hh1, hhi], pl.next, ← List.map_set]
    simp only [pfold_succ, Model.placeStep, ne_eq, hz, not_false_eq_true, ↓reduceIte]
  have R : ∀ r, r ≠ .x14 → t₈.getReg r = t.getReg r := fun r h14 ↦ by
    have e1 : t₈.getReg r = t₇.getReg r := by
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
      all_goals first | contradiction | exact NB.g80000890_keeps h₈ _ (by decide) | rfl
    rw [e1, hr₇]
  have hsp₈ : t₈.getReg .x2 = msp := (R .x2 (by decide)).trans rc.k.ng.sp
  refine ⟨t₈, (show Reaches Image.code t t₇ from ⟨1, ht₇⟩).trans r₈, NB.g80000890_pc h₈,
    ⟨rc.frame hf (fun a ha ↦ (hW a ha).1) hsp₈ hheap (le_of_eq hn.symm),
    pl.nal, pl.nlo, pl.nhi, (hK 24 (by decide) (by decide)).trans pl.m24, vs', next', hp,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals first
    | (rw [R _ (by decide)]; first
        | exact pl.x8 | exact pl.x9 | exact pl.x10 | exact pl.x11 | exact pl.x12
        | exact pl.x18 | exact pl.x20 | exact pl.x21 | exact pl.x25 | exact pl.x27
        | (rw [pl.x19, p8]))

end

/-- Past the placement, at `0x800008a0`: `positions` placed. -/
structure PX (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C : Word) (H1 : Nat) (t : MachineState) : Prop where
  rc : RC s words u₀ i L Hb st g D C H1 t
  m24 : t.getMem (msp + 24) = BitVec.ofNat 64 ((words.getD 0 0).toNat - 2 ^ 14 * i - L)
  vs : VS u₀ Hb H1 0 0 { { st with words := (rfold words i L g st g.2.2.length).2.2 } with
    positions := (pfold words i L g st L).1 } t
  x8 : t.getReg .x8 = u₀.getReg .x8
  x9 : t.getReg .x9 = BitVec.ofNat 64 (rfold words i L g st g.2.2.length).2.2.length
  x25 : t.getReg .x25 = D + BitVec.ofNat 64 (8 * g.2.2.length)

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C N : Word} {H1 p : Nat}

/-- `0x80000848`: on to position `p + 1`, or out of the loop. -/
theorem place_adv (h : PL s words u₀ i L Hb st g D C N H1 p (p + 1) t) (hpc : t.pc = 0x80000848) :
    ∃ v, Reaches Image.code t v ∧
      ((p + 1 < L ∧ v.pc = 0x8000085c ∧ PL s words u₀ i L Hb st g D C N H1 (p + 1) (p + 1) v) ∨
        (p + 1 = L ∧ v.pc = 0x800008a0 ∧ PX s words u₀ i L Hb st g D C H1 v)) := by
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b80000848_spec hpc trivial
  have kv := b80000848_keeps hv
  have hm := b80000848_mem_same hv
  have rc := h.rc
  have hn : heapNext v = heapNext t := by simp only [heapNext, hm]
  have hsp : v.getReg .x2 = msp := (kv .x2 (by decide)).trans rc.k.ng.sp
  have hf : BFrame t v (fun _ ↦ False) := BFrame.of_same hm _
  have hhi := rc.k.ng.heap.hi
  have rc' := rc.frame hf (fun _ h ↦ h.elim) hsp ⟨by rw [hn]; exact rc.k.ng.heap.lo,
    by rw [hn]; exact hhi⟩ (le_of_eq hn.symm)
  have vs' := h.vs.frame hf (fun _ h ↦ h.elim) (le_of_eq hn.symm) (by rw [hn]; exact hhi)
  have hp := h.hp
  have hL : L ≤ 2 ^ 14 := by have := rc.k.hL; omega
  have hfit := rc.k.a.inv.fits
  simp only [inputWords] at hfit
  have hlen := rc.k.a.len
  have hlt := rc.k.lt
  have hLL := rc.k.hL
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hGO := rc.k.a.groupOf
  have hH0 := rc.k.ng.mono
  simp only [heapNext, heapEnd] at hGO hH0 hhi
  have x20 : t.getReg .x20 - 8 = BitVec.ofNat 64 (8 * (L - (p + 1))) := by
    rw [h.x20]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl]
    omega
  by_cases he : p + 1 = L
  · have e : pfold words i L g st (p + 1) = pfold words i L g st L := by rw [he]
    rw [e] at vs'
    refine ⟨v, rv, Or.inr ⟨he, b80000848_pc_taken hv (by rw [x20, ← he, Nat.sub_self]; rfl),
      rc', by rw [hm]; exact h.m24, vs', (kv .x8 (by decide)).trans h.x8,
      (kv .x9 (by decide)).trans h.x9, (kv .x25 (by decide)).trans h.x25⟩⟩
  refine ⟨v, rv, Or.inl ⟨by omega, b80000848_pc_not_taken hv fun e ↦ he ?_, ⟨rc', h.nal, h.nlo,
    h.nhi, by rw [hm]; exact h.m24, vs', by rw [rwords_same hm]; exact h.next, by omega,
    (kv .x8 (by decide)).trans h.x8, (kv .x9 (by decide)).trans h.x9, ?_,
    (kv .x11 (by decide)).trans h.x11, ?_, (kv .x18 (by decide)).trans h.x18,
    by rw [kv .x19 (by decide), h.x19]; exact (hm _).symm, by rw [b80000848_x20 hv, x20], ?_,
    (kv .x25 (by decide)).trans h.x25, (kv .x27 (by decide)).trans h.x27⟩⟩⟩
  · rw [x20] at e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    have h0 : (0 : Word).toNat = 0 := rfl
    omega
  · rw [b80000848_x10 hv, h.x10, BitVec.ofNat_add]; rfl
  · rw [b80000848_x12 hv, h.x12]
    apply BitVec.eq_of_toNat_eq
    addr_omega [hGO, hhi, hH0, hp, hL]
  · rw [b80000848_x21 hv, h.x21]
    apply BitVec.eq_of_toNat_eq
    addr_omega [hib, hfit, hlen, hlt, hLL, hp]

/-- The placement's loop, from position `p` to its exit at `0x800008a0`. -/
theorem place_loop : ∀ m p (t : MachineState), L - p = m →
    PL s words u₀ i L Hb st g D C N H1 p p t → t.pc = 0x8000085c →
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x800008a0 ∧ PX s words u₀ i L Hb st g D C H1 v)) := by
  intro m
  induction m with
  | zero => intro p t hm h _; have := h.hp; omega
  | succ m ih =>
    intro p t hm h hpc
    have adv : ∀ t₁, Reaches Image.code t t₁ → t₁.pc = 0x80000848 →
        PL s words u₀ i L Hb st g D C N H1 p (p + 1) t₁ →
        ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
          (v.pc = 0x800008a0 ∧ PX s words u₀ i L Hb st g D C H1 v)) := by
      intro t₁ r₁ hpc₁ h₁
      obtain ⟨t₂, r₂, ⟨_, hpc₂, h₂⟩ | ⟨_, hpc₂, h₂⟩⟩ := place_adv h₁ hpc₁
      · obtain ⟨v, rv, hv⟩ := ih (p + 1) t₂ (by omega) h₂ hpc₂
        exact ⟨v, r₁.trans (r₂.trans rv), hv⟩
      · exact ⟨t₂, r₁.trans r₂, Or.inr ⟨hpc₂, h₂⟩⟩
    obtain ⟨t₁, r₁, hd | ⟨hpc₁, h₁⟩ | ⟨hpc₁, h₁⟩⟩ := place_front h hpc
    · exact ⟨t₁, r₁, Or.inl hd⟩
    · exact adv t₁ r₁ hpc₁ h₁
    · obtain ⟨t₂, r₂, hpc₂, h₂⟩ := place_back h₁ hpc₁
      exact adv t₂ (r₁.trans r₂) hpc₂ h₂

/-- The resize and the placement, from the runs' exit (`0x800007b8`) to `0x800008a0`. -/
theorem place_phase {t₀ : MachineState} (h : RE s words u₀ i L Hb st g D C N H1 t₀)
    (hpc : t₀.pc = 0x800007b8) :
    ∃ v, Reaches Image.code t₀ v ∧ (Dead Image.code v ∨
      (v.pc = 0x800008a0 ∧ PX s words u₀ i L Hb st g D C H1 v)) := by
  obtain ⟨t₁, r₁, hd | ⟨hpc₁, h₁⟩⟩ := resize_phase h hpc
  · exact ⟨t₁, r₁, Or.inl hd⟩
  obtain ⟨t₂, r₂, hpc₂, h₂⟩ := resize_end h₁ hpc₁
  obtain ⟨v, rv, hv⟩ := place_loop L 0 t₂ (by omega) h₂ hpc₂
  exact ⟨v, r₁.trans (r₂.trans rv), hv⟩

end

end Rv64Verifier.Proofs.Main
