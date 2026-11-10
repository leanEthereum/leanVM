import Rv64Verifier.Proofs.Main.NewClear

/-!
# `Bytecode::new`'s blocks: into `group`

From the head of the blocks' loop (`NewL`): `0x80000518` and `clear_loop` clear the slots,
`0x8000052c` takes the block's length `L = min (s10, 2^14)`, `0x8000053c` empties `distinct` and
stores the index, the next index and the block's end (`block_entry`, to `GH` at position `0`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

/-- A frame of `main`'s scratch slots keeps any doubleword below `msp`. -/
theorem slots_keepMsp_any {t t' : MachineState} {cs : List Nat}
    (hf : BFrame t t' fun a ↦ ∃ c ∈ cs, Within a (msp + BitVec.ofNat 64 c) 8)
    (hcs : (cs.all fun c ↦ c < 4096) = true) {a : Word} (ha : a.toNat + 8 ≤ msp.toNat) :
    t'.getMem (a &&& ~~~7#64) = t.getMem (a &&& ~~~7#64) := by
  have h1 := toNat_alignDown a
  exact getMem_eq_of_bytes (by rw [h1]; omega) (by rw [h1]; omega) fun i hi ↦
    slots_keepB hf hcs (by addr_omega [h1, ha, hi])

/-- `0x8000052c`: `a0 = min (s10, 2^14)`. -/
theorem min_step {w : MachineState} (hpc : w.pc = 0x8000052c) :
    ∃ v, Reaches Image.code w v ∧ v.pc = 0x8000053c ∧
      v.getReg .x10 = BitVec.ofNat 64 (min (w.getReg .x26).toNat (2 ^ 14)) ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → v.getReg r = w.getReg r) ∧ ∀ a, v.getMem a = w.getMem a := by
  obtain ⟨t, r, h⟩ := Sym.BlockSpec.reaches b8000052c_spec hpc trivial
  have k := b8000052c_keeps h
  have kr : ∀ r, r ≠ .x10 → r ≠ .x11 → t.getReg r = w.getReg r := by
    intro r h10 h11
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | contradiction | exact k _ (by decide) | rfl
  by_cases hc : (w.getReg .x26).toNat < (16384 : Word).toNat
  · refine ⟨t, r, b8000052c_pc_taken h hc, ?_, kr, b8000052c_mem_same h⟩
    rw [b8000052c_x10 h, Nat.min_eq_left (by have : (16384 : Word).toNat = 2 ^ 14 := rfl; omega)]
    simp
  · obtain ⟨t', r', h'⟩ := Sym.BlockSpec.reaches b80000538_spec
      (b8000052c_pc_not_taken h (by omega)) trivial
    have k' := b80000538_keeps h'
    refine ⟨t', r.trans r', b80000538_pc h', ?_, fun r h10 h11 ↦ ?_,
      fun a ↦ (b80000538_mem_same h' a).trans (b8000052c_mem_same h a)⟩
    · rw [b80000538_x10 h', Nat.min_eq_right (by have : (16384 : Word).toNat = 2 ^ 14 := rfl; omega)]
      rfl
    · rw [← kr r h10 h11]
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
      all_goals first | contradiction | exact k' _ (by decide) | rfl

section
variable {s u₀ t : MachineState} {words : List Word} {i : Nat} {st : Model.NewState}

/-- **Into `group`**: from the blocks' loop's head to `group`'s, at position `0`. -/
theorem block_entry (h : NewL s words u₀ i st t) :
    ∃ v, Reaches Image.code t v ∧
      GH s words u₀ i (min ((words.getD 0 0).toNat - 2 ^ 14 * i) (2 ^ 14)) (heapNext t) st 0
        (st.slots.map fun _ ↦ none, st.groupOf, []) v := by
  set n := (words.getD 0 0).toNat with hn
  set L := min (n - 2 ^ 14 * i) (2 ^ 14) with hL
  have hsp := h.ng.sp
  have ha := h.a
  obtain ⟨hS2, hS1, hSG⟩ := ha.slots
  obtain ⟨hG2, hGn⟩ := ha.groupOf
  have hm0 := h.ng.mono
  have hhi := h.ng.heap.hi
  simp only [heapNext, heapEnd, heapStart] at hS1 hGn hm0 hhi
  set SL := u₀.getReg .x8 with hSL
  set GO := u₀.getReg .x9 with hGO
  -- `0x80000518`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000518_spec h.pc trivial
  have k₁ := b80000518_keeps h₁
  -- the slots cleared
  obtain ⟨t₂, r₂, hpc₂, hk₂, hf₂, hz₂⟩ := clear_loop (SL := SL) ⟨hS2, hS1, by omega⟩ 0x8000 0 t₁
    rfl (by decide) (b80000518_pc h₁) (by rw [b80000518_x10 h₁, h.x8, hSL]; simp)
    (by rw [k₁ .x25 (by decide), h.x25]) fun j hj ↦ absurd hj (Nat.not_lt_zero _)
  -- the length
  obtain ⟨t₃, r₃, hpc₃, x10₃, hk₃, hm₃⟩ := min_step hpc₂
  -- `0x8000053c`
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000053c_spec hpc₃ (by
    have : t₃.getReg .x2 = msp := by
      rw [hk₃ _ (by decide) (by decide), hk₂ _ (by decide), k₁ .x2 (by decide), hsp]
    rv_eval [this, msp]; decide)
  have k₄ := b8000053c_keeps h₄
  have R : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x21 → t₃.getReg r = t.getReg r := by
    intro r h10 h11 h21
    rw [hk₃ r h10 h11, hk₂ r h10]
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | contradiction | exact k₁ _ (by decide) | rfl
  have hsp₃ : t₃.getReg .x2 = msp := (R .x2 (by decide) (by decide) (by decide)).trans hsp
  have hsp₄ : t₄.getReg .x2 = msp := (k₄ .x2 (by decide)).trans hsp₃
  have x21₃ : t₃.getReg .x21 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i)) := by
    rw [hk₃ _ (by decide) (by decide), hk₂ _ (by decide), b80000518_x21 h₁, h.x15]
  have x26₃ : (t₃.getReg .x26).toNat = n - 2 ^ 14 * i := by
    rw [R .x26 (by decide) (by decide) (by decide), h.x26]
  have hlt := h.lt
  have hLpos : 0 < L := by omega
  have hL14 : L ≤ 2 ^ 14 := by omega
  have x10₃' : t₃.getReg .x10 = BitVec.ofNat 64 L := by
    rw [x10₃, ← hk₃ .x26 (by decide) (by decide), x26₃]
  -- the frames
  have hf₄ := holds_slots h₄ hsp₃ [64, 120, 112, 104, 56, 48] (by decide) (by decide)
  have hf₁₂ : BFrame t t₂ (Within · SL 0x20000) := fun a ha ↦ by
    rw [hf₂ a ha, byteAt_eq, byteAt_eq, b80000518_mem_same h₁]
  have hf₂₃ : BFrame t₂ t₃ (fun _ ↦ False) := BFrame.of_same hm₃ _
  let W : Word → Prop := fun a ↦ Within a SL 0x20000 ∨
    ∃ c ∈ [64, 120, 112, 104, 56, 48], Within a (msp + BitVec.ofNat 64 c) 8
  have hf : BFrame t t₄ W :=
    ((hf₁₂.mono fun a ha ↦ Or.inl ha).trans hf₂₃ fun _ h ↦ h.elim).trans hf₄ fun a ha ↦ Or.inr ha
  have hn₄ : heapNext t₄ = heapNext t := by
    simp only [heapNext]
    rw [hf.getMem (a := nextAddr) (by decide) fun j hj hw ↦ by
      rcases hw with hw | ⟨c, hc, hw⟩
      · addr_omega [hw, hj, hSG, hGn, hm0, hhi]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> addr_omega [hw, hj]]
  have hheap₄ : HeapOk t₄ := ⟨by rw [hn₄]; exact h.ng.heap.lo, by rw [hn₄]; exact h.ng.heap.hi⟩
  have ng₄ : NG u₀ t₄ := h.ng.step hf (fun a ha ↦ by
    rcases ha with ha | ⟨c, hc, ha⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))))) <;>
        simp only [heapStart, heapEnd] <;> addr_omega [ha, hSG, hGn, hS1, hm0, hhi]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by addr_omega [ha])
      · exact Or.inr (Or.inl (by addr_omega [ha]))
      · exact Or.inr (Or.inl (by addr_omega [ha]))
      · exact Or.inr (Or.inl (by addr_omega [ha]))
      · exact Or.inl (by addr_omega [ha])
      · exact Or.inl (by addr_omega [ha])) hsp₄ hheap₄ (le_of_eq hn₄.symm)
  obtain ⟨vecs₄, bufs₄⟩ := VecsAt.frame h.vecs h.bufs hf (fun a ha ↦ by
    rcases ha with ha | ⟨c, hc, ha⟩
    · refine ⟨fun h' ↦ ?_, fun h' ↦ ?_, fun h' ↦ ?_⟩
      · addr_omega [ha, h', hSG, hGn, hm0, hhi]
      · addr_omega [ha, h', hSG, hGn, hm0, hhi]
      · have h1 := h'.1
        simp only [heapNext] at h1
        addr_omega [ha, h1, hSG, hGn]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      refine ⟨fun h' ↦ ?_, fun h' ↦ ?_, fun h' ↦ ?_⟩
      · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> addr_omega [ha, h']
      · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> addr_omega [ha, h']
      · have h2 := h'.2
        simp only [heapNext] at h2
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> addr_omega [ha, h2, hhi])
    (by rw [← hn₄]; exact ng₄.heap.hi)
  -- memory read back
  have K : ∀ d : Nat, d % 8 = 0 ∧ d < 4096 ∧
      ([64, 120, 112, 104, 56, 48].all fun c ↦ (c + 8 ≤ d || d + 8 ≤ c) && c < 4096) = true →
      t₄.getMem (msp + BitVec.ofNat 64 d) = t.getMem (msp + BitVec.ofNat 64 d) := by
    intro d hd
    rw [slots_keepMsp hf₄ hd, hm₃]
    refine hf₁₂.getMem (by addr_omega [hd.1, hd.2.1]) fun j hj hw ↦ ?_
    addr_omega [hw, hj, hSG, hGn, hm0, hhi, hd.2.1]
  have m64 : t₄.getMem (msp + 64) = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i + L)) := by
    have e := b8000053c_m_x2_64 h₄
    rw [hsp₃, x21₃, x10₃'] at e
    rw [e]
    apply BitVec.eq_of_toNat_eq
    have hfit := ha.inv.fits
    simp only [inputWords] at hfit
    have hib : inputBase.toNat = 0x10000000 := rfl
    have hlen := ha.len
    addr_omega [hib, hL14, hlt, hfit, hlen]
  have R4 : ∀ r ∈ ([.x8, .x16, .x22, .x25, .x27] : List Reg), t₄.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (k₄ _ (by decide)).trans (R _ (by decide) (by decide) (by decide))
  have x13₃ : t₃.getReg .x13 = BitVec.ofNat 64 i := (R .x13 (by decide) (by decide) (by decide)).trans h.x13
  have m48 : t₄.getMem (msp + 48) = BitVec.ofNat 64 i := by
    have e := b8000053c_m_x2_48 h₄; rw [hsp₃, x13₃] at e; exact e
  have m56 : t₄.getMem (msp + 56) = BitVec.ofNat 64 i + 1 := by
    have e := b8000053c_m_x2_56 h₄; rw [hsp₃, x13₃] at e; exact e
  have m120 : t₄.getMem (msp + 120) = 0 := by
    have e := b8000053c_m_x2_120 h₄; rw [hsp₃] at e; exact e
  have m112 : t₄.getMem (msp + 112) = 8 := by
    have e := b8000053c_m_x2_112 h₄; rw [hsp₃] at e; exact e
  have m104 : t₄.getMem (msp + 104) = 0 := by
    have e := b8000053c_m_x2_104 h₄; rw [hsp₃] at e; exact e
  have hfit := ha.inv.fits
  simp only [inputWords] at hfit
  have hlen := ha.len
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hGOk : ∀ a : Word, GO.toNat ≤ a.toNat → a.toNat < GO.toNat + 2 * 0x4000 →
      byteAt t₄ a = byteAt t a := fun a h1 h2 ↦ hf a fun hw ↦ by
    rcases hw with hw | ⟨c, hc, hw⟩
    · addr_omega [hw, h1, h2, hSG]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> addr_omega [hw, h1, h2, hGn, hm0, hhi]
  refine ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), ⟨⟨⟨ha, h.lt, rfl, h.fold, h.slots, h.ng.mono, ng₄,
    le_of_eq hn₄.symm, ⟨(K 8 (by decide)).trans h.m8, (K 16 (by decide)).trans h.m16,
      (K 40 (by decide)).trans h.m40, m48, m56, m64⟩⟩, vecs₄, bufs₄, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    Nat.zero_le _, R4 .x8 (by decide) |>.trans h.x8, by rw [b8000053c_x9 h₄]; rfl,
    by rw [b8000053c_x10 h₄, m112], by rw [b8000053c_x15 h₄, ← b8000053c_m_x2_64 h₄, hsp₃]; exact m64,
    R4 .x16 (by decide) |>.trans h.x16, by rw [b8000053c_x18 h₄]; rfl, ?_,
    by rw [k₄ .x21 (by decide), x21₃], R4 .x22 (by decide) |>.trans h.x22,
    by rw [b8000053c_x23 h₄, R .x16 (by decide) (by decide) (by decide), h.x16],
    by rw [b8000053c_x24 h₄, x21₃]; simp, R4 .x25 (by decide) |>.trans h.x25, ?_,
    R4 .x27 (by decide) |>.trans h.x27⟩, b8000053c_pc h₄, rfl, hLpos⟩⟩
  · intro j hj
    have e : (st.slots.map fun _ ↦ (none : Option (BitVec 16))).getD j none = none := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases st.slots[j]? <;> rfl
    refine ⟨fun _ ↦ ?_, fun g hg ↦ by rw [e] at hg; cases hg⟩
    rw [← hz₂ j hj]
    simp only [MachineState.getHalfword, alignToDword]
    rw [slots_keepMsp_any hf₄ (by decide), hm₃]
    · rw [← hSL]; addr_omega [hj, hSG, hGn, hm0, hhi]
  · exact (halvesAt_keep hG2 hGOk (by addr_omega [hGn, hm0, hhi])).trans h.groupOf
  · rw [m120]; rfl
  · exact Nat.zero_le _
  · rw [m112]; rfl
  · left; rw [m104]; rfl
  · rfl
  · rw [b8000053c_x20 h₄, x10₃']
    apply BitVec.eq_of_toNat_eq
    addr_omega [hL14]
  · rw [b8000053c_x26 h₄, x10₃']
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, x26₃]
    simp only [BitVec.toNat_ofNat]
    omega

end

end Rv64Verifier.Proofs.Main
