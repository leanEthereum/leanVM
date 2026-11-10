import Rv64Verifier.Proofs.Walk.CountLoop10

/-!
# `walk`: the bus blocks' loop (R10)

`countLoop` runs the count loop to its end; `zipTail` stores `count`'s length and branches back to
the header or out; `zipStep` is one table; `r10` runs the loop from `AtR10` to `0x80003038`
(`AtR11`), the three `Vec`s holding `busBlocksRust` of the tables, their heights and rows.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem countLoop (hAS : AllocSpec) (hCol : ColSpec) (hCl : CloneSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo i : Nat}
    {P : List BusBlockRust × List BusBlockRust × List BusBlockRust} {p : Word} {c L0 : Nat}
    (hpre : WalkPre s) :
    ∀ d j u, nCols i - j = d → j < nCols i → u.pc = 0x80002f9c →
      CountAt OI s u A k R Q B lo i P p c L0 j →
      ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
        (t.pc = 0x80003024 ∧ CountAt OI s t A k R Q B lo i P p c L0 (nCols i))) := by
  intro d
  induction d with
  | zero => intro j u hd hj; omega
  | succ d ih =>
    intro j u hd hj hpc h
    obtain ⟨t₁, hr₁, hd₁ | ⟨hpc₁, N0, h₁⟩⟩ := countA hAS hCol hCl hpre hpc h hj
    · exact ⟨t₁, hr₁, Or.inl hd₁⟩
    obtain ⟨t₂, hr₂, hpc₂, h₂⟩ := countB hpre hpc₁ h₁
    by_cases hc : j + 1 < nCols i
    · simp only [hc, ↓reduceIte] at hpc₂
      obtain ⟨t, hr, ht⟩ := ih (j + 1) t₂ (by omega) hc hpc₂ h₂
      exact ⟨t, hr₁.trans (hr₂.trans hr), ht⟩
    · simp only [hc, ↓reduceIte] at hpc₂
      have e : j + 1 = nCols i := by omega
      rw [e] at h₂
      exact ⟨t₂, hr₁.trans hr₂, Or.inr ⟨hpc₂, h₂⟩⟩

/-- `count`'s header `{c, p, n}` back in place: `VecsC` is `Vecs10`. -/
theorem VecsC.toVecs10 {s u : MachineState} {lo : Nat} {P1 P2 P3 : List BusBlockRust} {p : Word}
    {c n : Nat} (V : VecsC s u lo P1 P2 P3 p c n) (hc : c < 2 ^ 64) (hn : n < 2 ^ 64)
    (h0 : u.getMem (s.getReg .x2 - 512) = BitVec.ofNat 64 c)
    (h8 : u.getMem (s.getReg .x2 - 512 + 8) = p)
    (h16 : u.getMem (s.getReg .x2 - 512 + 16) = BitVec.ofNat 64 n) :
    Vecs10 s u lo (P1, P2, P3) := by
  have ec : (vecCap u (s.getReg .x2 - 512)).toNat = c := by
    simp only [vecCap, h0, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hc
  have ep : vecPtr u (s.getReg .x2 - 512) = p := h8
  have el : (vecLen u (s.getReg .x2 - 512)).toNat = n := by
    simp only [vecLen, h16, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hf : blocksFoot u (s.getReg .x2 - 512) = cFoot u p c n := by
    funext x; simp only [blocksFoot, cFoot, ec, ep, el]
  refine ⟨V.push, V.pull, ?_, V.pushV, V.pullV, ?_, ?_, V.d1, ?_, ?_⟩
  · simp only [BlocksOk, ec, ep, el]; exact V.count
  · simp only [blocksOf, ep, el]; exact V.countV
  · rw [hf]; exact V.fresh
  · rw [hf]; exact V.d2
  · rw [hf]; exact V.d3

theorem heights_length (A : List E) (hl : (rowsOf A).length = 6) :
    (tableLogHeightsRust (rowsOf A)).length = 6 := by
  simp [tableLogHeightsRust, hl, tableLogFloorsRust]

theorem zip_get (A : List E) (hl : (rowsOf A).length = 6) {i : Nat} {tb : TableRust}
    (htb : tablesRust[i]? = some tb) :
    ((tablesRust.zip (tableLogHeightsRust (rowsOf A))).zip (rowsOf A))[i]? =
      some ((tb, (tableLogHeightsRust (rowsOf A)).getD i 0), (rowsOf A).getD i 0) := by
  have hi := tablesRust_some htb
  have hH := heights_length A hl
  rw [List.getElem?_zip_eq_some, List.getElem?_zip_eq_some]
  refine ⟨⟨htb, ?_⟩, ?_⟩
  · rw [List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
  · rw [List.getElem?_eq_getElem (by omega)]
    simp only [List.getD_eq_getElem _ _ (show i < (rowsOf A).length by omega)]

theorem zipPre_succ (A : List E) (hl : (rowsOf A).length = 6) {i : Nat} {tb : TableRust}
    (htb : tablesRust[i]? = some tb) :
    zipPre A (i + 1) = ((zipPre A i).1 ++ tb.flushes.push.map (blkOf A i),
      (zipPre A i).2.1 ++ tb.flushes.pull.map (blkOf A i), (zipPre A i).2.2 ++ countPre A i (nCols i)) := by
  rw [zipPre, List.take_add_one, zip_get A hl htb, List.foldl_append]
  simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
  rw [← zipPre]
  have ho := tablesRust_opcode_eq htb
  simp only [busStep, blkOf, countPre, TableRust.countColumns, ho, List.take_length]
  rfl

theorem zipPre_six (A : List E) (hl : (rowsOf A).length = 6) :
    zipPre A 6 = busBlocksRust tablesRust (tableLogHeightsRust (rowsOf A)) (rowsOf A) := by
  rw [busBlocksRust_foldl, zipPre, List.take_of_length_le]
  have : tablesRust.length = 6 := rfl
  simp [List.length_zip, this, heights_length A hl, hl]

/-- At `0x80003038`, past the bus blocks' loop. -/
structure AtR11 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo : Nat) : Prop where
  base : Base10 OI s u A k R Q B lo
  op5 : u.getMem (B + 472) = 5
  vecs : Vecs10 s u lo (busBlocksRust tablesRust (tableLogHeightsRust (rowsOf A)) (rowsOf A))

set_option maxRecDepth 8192 in
/-- `count`'s length stored, and the loop's branch. -/
theorem zipTail {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo i : Nat} {tb : TableRust}
    {p : Word} {c L0 : Nat} (hpre : WalkPre s) (htb : tablesRust[i]? = some tb)
    (hpc : u.pc = 0x80003024)
    (h : CountAt OI s u A k R Q B lo i ((zipPre A i).1 ++ tb.flushes.push.map (blkOf A i),
      (zipPre A i).2.1 ++ tb.flushes.pull.map (blkOf A i), (zipPre A i).2.2) p c L0 (nCols i)) :
    ∃ t, Reaches Image.code u t ∧ ((i + 1 < 6 ∧ t.pc = 0x80002e94 ∧ Zip10 OI s t A k R Q B lo (i + 1)) ∨
      (i + 1 = 6 ∧ t.pc = 0x80003038 ∧ AtR11 OI s t A k R Q B lo)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have H := h.base
  have hi := h.lt
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := H.inv.sp
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b80003024_spec hpc (by
    rv_eval [sp]
    simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hb1, hb2, hb3])
  have e2160 : u.getReg .x2 + 2160 = s.getReg .x2 - 496 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e184 : u.getReg .x2 + 184 = s.getReg .x2 - 2472 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr : MemFrame u t (s.getReg .x2 - 496) 8 := by
    rw [← e2160]; exact b80003024_frame ht (by rw [sp]; addr_omega [hb1])
  have m (x : Word) (hx : ¬ Within x (s.getReg .x2 - 496) 8) : t.getMem x = u.getMem x := fr x hx
  have hn : heapNext t = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (m _ (by simp only [Within, nextAddr]; addr_omega [hb1]))
  have hv : HeapOk t := ⟨hn ▸ H.inv.heap.lo, hn ▸ H.inv.heap.hi⟩
  have kt := b80003024_keeps ht
  have frw : ∀ x, Within x (s.getReg .x2 - 496) 8 → (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧
      x.toNat < (s.getReg .x2 - 104).toNat ∧ ¬ Within x (s.getReg .x2 - 416) 24 ∧
      ¬ Within x (s.getReg .x2 - 224) 24 := fun x hx ↦ by
    simp only [Within] at hx ⊢
    exact ⟨by addr_omega [hx, hb1], by addr_omega [hx, hb1], by addr_omega [hx, hb1],
      by addr_omega [hx, hb1]⟩
  have B' : Base10 OI s t A k R Q B lo := H.keep hpre (MemFrame.dframe fr) (fun x hx ↦ by
      simp only [Within] at hx
      exact Or.inl (Or.inl ⟨by addr_omega [hx, hb1], by addr_omega [hx, hb1]⟩)) hv hn.ge
    (kt .x2 (by decide))
  have VC := h.vecs.keepFrame hpre H.inv.heap hn.ge (MemFrame.dframe fr) frw
  have hroom := h.room
  have hbd := BlocksSound.bounds h.vecs.count
  have hNp := nCols_pos hi
  have hc64 : c < 2 ^ 64 := by
    rcases hbd.2 with h0 | h0
    · omega
    · have := H.inv.heap.hi; simp only [heapEnd] at this; omega
  obtain ⟨a1, a2, a3⟩ := h.hdr
  have V := VC.toVecs10 hc64 (by omega)
    (by rw [m _ (by simp only [Within]; addr_omega [hb1])]; exact a1)
    (by
      have e : s.getReg .x2 - 512 + 8 = s.getReg .x2 - 504 := by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      rw [e, m _ (by simp only [Within]; addr_omega [hb1])]; exact a2)
    (by
      have e : s.getReg .x2 - 512 + 16 = s.getReg .x2 - 496 := by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      rw [e, ← e2160, b80003024_m_x2_2160 ht]; exact h.x23)
  rw [← zipPre_succ A H.rowsLen htb] at V
  have n6 : t.getMem (s.getReg .x2 - 2472) = 6 := by
    rw [m _ (by simp only [Within]; addr_omega [hb1])]; exact h.n
  have op : t.getMem (B + 472) = 5 := by
    have hB := H.bufB; have hl := H.loLe; have hh := H.inv.heap.hi; simp only [heapEnd] at hh
    rw [m _ (by simp only [Within]; addr_omega [hB, hl, hh, hb1])]; exact h.op5
  by_cases hc : i + 1 < 6
  · refine ⟨t, hr, Or.inl ⟨hc, b80003024_pc_taken ht ?_, {
      base := B'
      op5 := op
      vecs := V
      lt := hc
      x9 := by rw [kt .x9 (by decide)]; exact h.x9
      x18 := by rw [kt .x18 (by decide)]; exact h.x18
      x19 := by rw [kt .x19 (by decide)]; exact h.x19
      x20 := by rw [b80003024_x20 ht, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      x21 := by rw [kt .x21 (by decide)]; exact h.x21
      n := n6 }⟩⟩
    rw [h.x9, e184, h.n]
    intro he; have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    have : (6 : Word).toNat = 6 := rfl
    omega
  · have e6 : i + 1 = 6 := by omega
    rw [e6, zipPre_six A H.rowsLen] at V
    refine ⟨t, hr, Or.inr ⟨e6, b80003024_pc_not_taken ht ?_, ⟨B', op, V⟩⟩⟩
    rw [h.x9, e184, h.n, e6]
    rfl

/-- One table of the bus blocks' loop. -/
theorem zipStep (hE : ExtendBlocksSpec) (hRes : ReserveFreshSpec 0x800060bc 48 8)
    (hAS : AllocSpec) (hCol : ColSpec) (hCl : CloneSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo i : Nat} (hpre : WalkPre s) (hpc : u.pc = 0x80002e94)
    (h : Zip10 OI s u A k R Q B lo i) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (i + 1 < 6 ∧ t.pc = 0x80002e94 ∧ Zip10 OI s t A k R Q B lo (i + 1)) ∨
      (t.pc = 0x80003038 ∧ AtR11 OI s t A k R Q B lo)) := by
  obtain ⟨t₁, hr₁, hd | ⟨hpc₁, tb, htb, h₁⟩⟩ := zipExt hE hpre hpc h
  · exact ⟨t₁, hr₁, Or.inl hd⟩
  obtain ⟨t₂, hr₂, hd | ⟨hpc₂, p, c, L0, h₂⟩⟩ := countPrep hRes hpre hpc₁ h₁
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  obtain ⟨t₃, hr₃, hd | ⟨hpc₃, h₃⟩⟩ := countLoop hAS hCol hCl hpre (nCols i) 0 t₂ (by omega)
    (nCols_pos h.lt) hpc₂ h₂
  · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inl hd⟩
  obtain ⟨t₄, hr₄, ⟨hc, hpc₄, h₄⟩ | ⟨-, hpc₄, h₄⟩⟩ := zipTail hpre htb hpc₃ h₃
  · exact ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inl ⟨hc, hpc₄, h₄⟩)⟩
  · exact ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inr ⟨hpc₄, h₄⟩)⟩

/-- R10: from `0x80002e40` to `0x80003038`, the bus blocks built. -/
theorem r10 (hE : ExtendBlocksSpec) (hRes : ReserveFreshSpec 0x800060bc 48 8)
    (hAS : AllocSpec) (hCol : ColSpec) (hCl : CloneSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} (hpre : WalkPre s) (h : AtR10 OI s u A k R Q B) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x80003038 ∧ AtR11 OI s t A k R Q B (heapNext u))) := by
  obtain ⟨u₀, hr₀, hpc₀, h₀⟩ := r10head hpre h
  have key : ∀ d i v, 6 - i = d → v.pc = 0x80002e94 → Zip10 OI s v A k R Q B (heapNext u) i →
      ∃ t, Reaches Image.code v t ∧ (Dead Image.code t ∨
        (t.pc = 0x80003038 ∧ AtR11 OI s t A k R Q B (heapNext u))) := by
    intro d
    induction d with
    | zero => intro i v hd _ hv; have := hv.lt; omega
    | succ d ih =>
      intro i v hd hpc hv
      obtain ⟨t, hr, hd' | ⟨-, hpct, ht⟩ | hdone⟩ := zipStep hE hRes hAS hCol hCl hpre hpc hv
      · exact ⟨t, hr, Or.inl hd'⟩
      · obtain ⟨t', hr', ht'⟩ := ih (i + 1) t (by omega) hpct ht
        exact ⟨t', hr.trans hr', ht'⟩
      · exact ⟨t, hr, Or.inr hdone⟩
  obtain ⟨t, hr, ht⟩ := key 6 0 u₀ rfl hpc₀ h₀
  exact ⟨t, hr₀.trans hr, ht⟩

end Rv64Verifier.Proofs.Walk
