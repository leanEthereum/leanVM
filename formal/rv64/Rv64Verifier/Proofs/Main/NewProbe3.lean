import Rv64Verifier.Proofs.Main.NewProbe2

/-!
# `group`'s probe, to the word's group

`GP`: at `0x80000594`, the word's group in `a1`, the slots and `distinct` as `probeRust` leaves
them. `probe_new` (a free slot), `probe_loop` (an occupied one, by induction on the fuel) and
`probe_first` (from `slot_of(word)`, `0x800005bc`) reach it, or a dead end.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

/-- At `0x80000594`, the group of position `q`'s word known: `a1` holds it, the slots and
`distinct` as the probe `r` left them, `group_of` as before. -/
structure GP (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (q : Nat) (g : GrpSt)
    (r : List (Option (BitVec 16)) × List (BitVec 64) × BitVec 16) (t : MachineState) : Prop where
  gs : GS s words u₀ i L Hb st q (r.1, g.2.1, r.2.1) t
  pc : t.pc = 0x80000594
  x11 : (t.getReg .x11).setWidth 16 = r.2.2

theorem newGroup_eq (n : Nat) :
    (BitVec.ofNat 64 n).setWidth 16 = BitVec.ofNat 16 (n + 1) - 1#16 := by
  rw [BitVec.ofNat_add]
  simp only [BitVec.add_sub_cancel]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb q : Nat} {st : Model.NewState}
  {g : GrpSt}

/-- `0x80000620`: a free slot `j` takes the next group, the word pushed onto `distinct`. -/
theorem probe_new (h : GS s words u₀ i L Hb st q g t) (hpc : t.pc = 0x80000620) {j : Nat}
    (hj : j < 2 ^ 15) (hx11 : t.getReg .x11 = u₀.getReg .x8 + BitVec.ofNat 64 (4 * j))
    (hlen : g.1.length = 2 ^ 15) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ GP s words u₀ i L Hb st q g
      (g.1.set j (some (BitVec.ofNat 16 g.2.2.length)), g.2.2 ++ [t.getReg .x19],
        BitVec.ofNat 16 (g.2.2.length + 1) - 1#16) v) := by
  obtain ⟨t₃, r₃, gs₃, x19₃, hpc₃ | hpc₃⟩ := slot_store h hpc hj hx11 hlen
  · obtain ⟨v, rv, gsv, hpcv, x11v⟩ := push_57c gs₃ hpc₃.1 hpc₃.2
    refine ⟨v, r₃.trans rv, Or.inr ⟨?_, hpcv, by rw [x11v]; exact newGroup_eq _⟩⟩
    rw [x19₃] at gsv
    exact gsv
  · obtain ⟨t₄, r₄, hd | ⟨gs₄, hpc₄, hroom, x19₄⟩⟩ := grow_distinct gs₃ hpc₃.1 hpc₃.2
    · exact ⟨t₄, r₃.trans r₄, Or.inl hd⟩
    obtain ⟨v, rv, gsv, hpcv, x11v⟩ := push_57c gs₄ hpc₄ (by omega)
    refine ⟨v, r₃.trans (r₄.trans rv), Or.inr ⟨?_, hpcv, by rw [x11v]; exact newGroup_eq _⟩⟩
    rw [x19₄, x19₃] at gsv
    exact gsv

/-- An occupied slot: tag nonzero; a free one: tag zero. -/
theorem SlotsRel.tag {t : MachineState} {SL : Word} {sl : List (Option (BitVec 16))}
    (h : SlotsRel t SL sl) {j : Nat} (hj : j < 2 ^ 15) :
    (sl.getD j none).isSome = true ↔ t.getHalfword (SL + BitVec.ofNat 64 (4 * j)) ≠ 0 := by
  constructor
  · intro hs
    obtain ⟨gv, hgv⟩ := Option.isSome_iff_exists.mp hs
    exact ((h j hj).2 gv hgv).1
  · intro hn
    cases e : sl.getD j none with
    | none => exact absurd ((h j hj).1 e) hn
    | some _ => rfl

/-- `0x800005e0`: slot `j` holds group `gv`: the word's (to `0x80000594`), or another's (to
`0x800005f8`). -/
theorem probe_read (h : GS s words u₀ i L Hb st q g t) {j : Nat} (hj : j < 2 ^ 15)
    (hpc : t.pc = 0x800005e0) (hx13 : t.getReg .x13 = u₀.getReg .x8 + BitVec.ofNat 64 (4 * j) + 2)
    {gv : BitVec 16} (hgv : g.1.getD j none = some gv) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (g.2.2.getD gv.toNat 0 = t.getReg .x19 ∧ GP s words u₀ i L Hb st q g (g.1, g.2.2, gv) v) ∨
      (g.2.2.getD gv.toNat 0 ≠ t.getReg .x19 ∧ GS s words u₀ i L Hb st q g v ∧
        v.pc = 0x800005f8 ∧ v.getReg .x12 = t.getReg .x12 ∧ v.getReg .x19 = t.getReg .x19)) := by
  have hSL := h.k.a.slots
  have hGO := h.k.a.groupOf
  have hhi := h.k.ng.heap.hi
  have hH0 := h.k.ng.mono
  simp only [heapStart] at hSL
  simp only [heapNext, heapEnd] at hGO hhi hH0
  have m := h.mem
  have hval := ((m.slots j hj).2 gv hgv).2
  obtain ⟨t₁, r₁, hpc₁, hr₁, hm₁⟩ := step_lhu (code := Image.code) (rd := .x11) (rs1 := .x13)
    (off := 0) (by rw [hpc]; exact fetch_of (by decide +kernel))
    (by
      rw [off0, hx13]
      exact valid2_of (by addr_omega [hSL, hj]) (by addr_omega [hSL, hj, hGO, hhi, hH0])
        (by addr_omega [hSL, hj]))
  rw [off0, hx13, hval] at hr₁
  have hr₁' : ∀ r, r ≠ .x11 → t₁.getReg r = t.getReg r := fun r hr ↦ by
    rw [hr₁]; simp [hr]
  have x11₁ : t₁.getReg .x11 = gv.zeroExtend 64 := by rw [hr₁]; simp
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches NB.g800005e4_spec (by rw [hpc₁, hpc]; rfl) trivial
  have k₂ := NB.g800005e4_keeps h₂
  have hm₂ := NB.g800005e4_mem_same h₂
  have hgvn : (gv.zeroExtend 64 : Word).toNat = gv.toNat := by
    simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
    have := gv.isLt
    omega
  by_cases hb : (t₁.getReg .x18).toNat ≤ (t₁.getReg .x11).toNat
  · obtain ⟨w, hw, hd⟩ := abort (u := t₂) (by rw [NB.g800005e4_pc_taken h₂ hb]; decide)
    exact ⟨w, (show Reaches Image.code t t₁ from ⟨1, r₁⟩).trans (r₂.trans hw), Or.inl hd⟩
  have hlt : gv.toNat < g.2.2.length := by
    rw [hr₁' _ (by decide), h.x18, x11₁, hgvn] at hb
    simp only [BitVec.toNat_ofNat] at hb
    have := m.cap
    omega
  have hcap := m.cap
  have hbuf : Hb ≤ (t.getMem (msp + 112)).toNat ∧
      (t.getMem (msp + 112)).toNat + (t.getMem (msp + 104)).toNat * 8 ≤ heapNext t :=
    m.buf.resolve_left (by omega)
  simp only [heapNext] at hbuf
  have hb0 := h.k.hb0
  have hl0 := h.k.a.inv.heap.lo
  simp only [heapNext, heapStart] at hb0 hl0
  have hal := m.al
  have hx10 : t₂.getReg .x10 = t.getMem (msp + 112) := by
    rw [k₂ .x10 (by decide), hr₁' _ (by decide), h.x10]
  have hx11 : t₂.getReg .x11 = gv.zeroExtend 64 := by rw [k₂ .x11 (by decide), x11₁]
  have hA : t.getMem (msp + 112) + gv.zeroExtend 64 * 8 =
      t.getMem (msp + 112) + BitVec.ofNat 64 (8 * gv.toNat) := by
    apply BitVec.eq_of_toNat_eq
    addr_omega [hgvn, hlt, hbuf, hcap, hhi]
  have hdk : g.2.2.getD gv.toNat 0 = t.getMem (t.getMem (msp + 112) + BitVec.ofNat 64 (8 * gv.toNat)) := by
    have e := m.dist
    rw [readWords_eq_map] at e
    rw [← e, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
    rfl
  have hm12 : ∀ a, t₂.getMem a = t.getMem a := fun a ↦ (hm₂ a).trans (hm₁ a)
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b800005e8_spec (NB.g800005e4_pc_not_taken h₂
    (by omega)) (by
      rv_eval []
      rw [hx10, hx11, hA]
      exact (Sym.validAccess_eight _).mpr ⟨Or.inl ⟨by addr_omega [hlt, hbuf, hcap, hhi, hb0, hl0],
        by addr_omega [hlt, hbuf, hcap, hhi]⟩, by addr_omega [hal, hlt, hbuf, hcap, hhi]⟩)
  have k₃ := b800005e8_keeps h₃
  have hm₃ := b800005e8_mem_same h₃
  have hm : ∀ a, t₃.getMem a = t.getMem a := fun a ↦ (hm₃ a).trans (hm12 a)
  have hr : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x19 →
      t₃.getReg r = t.getReg r := by
    intro r h11 h12 h13 h14 h19
    rw [← hr₁' r h11]
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | contradiction | exact (k₃ _ (by decide)).trans (k₂ _ (by decide)) | rfl
  have x12₃ : t₃.getReg .x12 = t.getReg .x12 := by
    rw [k₃ .x12 (by decide), k₂ .x12 (by decide), hr₁' _ (by decide)]
  have x19₃ : t₃.getReg .x19 = t.getReg .x19 := by
    rw [k₃ .x19 (by decide), k₂ .x19 (by decide), hr₁' _ (by decide)]
  have gs := h.same hm hr
  have R : Reaches Image.code t t₃ :=
    (show Reaches Image.code t t₁ from ⟨1, r₁⟩).trans (r₂.trans r₃)
  have e19 : t₂.getReg .x19 = t.getReg .x19 := by rw [k₂ .x19 (by decide), hr₁' _ (by decide)]
  by_cases e : t₂.getMem (t₂.getReg .x10 + t₂.getReg .x11 * 8) = t₂.getReg .x19
  · rw [hx10, hx11, hA, hm12, e19, ← hdk] at e
    refine ⟨t₃, R, Or.inr (Or.inl ⟨e, gs, b800005e8_pc_taken h₃ (by
      rw [hx10, hx11, hA, hm12, e19, ← hdk]; exact e), ?_⟩)⟩
    rw [k₃ .x11 (by decide), hx11]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
    have := gv.isLt
    omega
  · have e' := e
    rw [hx10, hx11, hA, hm12, e19, ← hdk] at e'
    exact ⟨t₃, R, Or.inr (Or.inr ⟨e', gs, b800005e8_pc_not_taken h₃ e, x12₃, x19₃⟩)⟩

/-- `0x800005f8`: on to the next slot, `(j + 1) % 2^15`, and its tag. -/
theorem probe_next (h : GS s words u₀ i L Hb st q g t) (hpc : t.pc = 0x800005f8) {j : Nat}
    (hj : j < 2 ^ 15) (hx12 : t.getReg .x12 = BitVec.ofNat 64 j) :
    ∃ v, Reaches Image.code t v ∧ GS s words u₀ i L Hb st q g v ∧
      v.getReg .x19 = t.getReg .x19 ∧ v.getReg .x12 = BitVec.ofNat 64 ((j + 1) % 2 ^ 15) ∧
      ((v.pc = 0x800005e0 ∧
          v.getReg .x13 = u₀.getReg .x8 + BitVec.ofNat 64 (4 * ((j + 1) % 2 ^ 15)) + 2 ∧
          (g.1.getD ((j + 1) % 2 ^ 15) none).isSome = true) ∨
        (v.pc = 0x80000620 ∧ v.getReg .x11 = u₀.getReg .x8 + BitVec.ofNat 64 (4 * ((j + 1) % 2 ^ 15)) ∧
          g.1.getD ((j + 1) % 2 ^ 15) none = none)) := by
  have hSL := h.k.a.slots
  have hGO := h.k.a.groupOf
  have hhi := h.k.ng.heap.hi
  have hH0 := h.k.ng.mono
  simp only [heapStart] at hSL
  simp only [heapNext, heapEnd] at hGO hhi hH0
  set j' := (j + 1) % 2 ^ 15 with hj'
  have hj'l : j' < 2 ^ 15 := Nat.mod_lt _ (by decide)
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches NB.g800005f8_spec hpc trivial
  have k₁ := NB.g800005f8_keeps h₁
  have x12₁ : t₁.getReg .x12 = BitVec.ofNat 64 j' := by
    rw [h₁.reg .x12 rfl]
    rv_eval []
    simp only [hx12, h.x22]
    exact wrap_slot hj
  have x11₁ : t₁.getReg .x11 = u₀.getReg .x8 + BitVec.ofNat 64 (4 * j') := by
    have e : t₁.getReg .x11 = t.getReg .x8 + t₁.getReg .x12 * 4 := by
      rw [h₁.reg .x11 rfl, h₁.reg .x12 rfl]
      rv_eval []
    rw [e, x12₁, h.x8, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul,
      Nat.mul_comm]
  obtain ⟨t₂, r₂, hpc₂, hr₂, hm₂⟩ := step_lhu (code := Image.code) (s := t₁) (rd := .x14)
    (rs1 := .x11) (off := 0) (by rw [NB.g800005f8_pc h₁]; exact fetch_of (by decide +kernel))
    (by
      rw [off0, x11₁]
      exact valid2_of (by addr_omega [hSL, hj'l]) (by addr_omega [hSL, hj'l, hGO, hhi, hH0])
        (by addr_omega [hSL, hj'l]))
  rw [off0, x11₁] at hr₂
  have hr₂' : ∀ r, r ≠ .x14 → t₂.getReg r = t₁.getReg r := fun r hr ↦ by rw [hr₂]; simp [hr]
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches NB.g80000618_spec (by
    rw [hpc₂, NB.g800005f8_pc h₁]; rfl) trivial
  have k₃ := NB.g80000618_keeps h₃
  have hm : ∀ a, t₃.getMem a = t.getMem a := fun a ↦ by
    rw [NB.g80000618_mem_same h₃, hm₂, NB.g800005f8_mem_same h₁]
  have hr : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → t₃.getReg r = t.getReg r := by
    intro r h11 h12 h13 h14
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first
      | contradiction
      | rw [k₃ _ (by decide), hr₂' _ (by decide), k₁ _ (by decide)]
      | rfl
  have x14₂ : t₂.getReg .x14 = (t₁.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j'))).zeroExtend 64 := by
    rw [hr₂]; simp
  have htag : t₁.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j')) =
      t.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j')) :=
    getHalfword_same (NB.g800005f8_mem_same h₁) _
  have hz : t₂.getReg .x14 = 0 ↔ t.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j')) = 0 := by
    rw [x14₂, htag]
    constructor
    · intro e
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat e
      simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth] at this
      have := (t.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j'))).isLt
      have h0 : (0 : Word).toNat = 0 := rfl
      have h0' : (0 : BitVec 16).toNat = 0 := rfl
      omega
    · intro e; rw [e]; rfl
  have x13₃ : t₃.getReg .x13 = u₀.getReg .x8 + BitVec.ofNat 64 (4 * j') + 2 := by
    rw [NB.g80000618_x13 h₃, hr₂' _ (by decide), x11₁]
  have x11₃ : t₃.getReg .x11 = u₀.getReg .x8 + BitVec.ofNat 64 (4 * j') := by
    rw [k₃ .x11 (by decide), hr₂' _ (by decide), x11₁]
  have R : Reaches Image.code t t₃ := r₁.trans ((show Reaches Image.code t₁ t₂ from ⟨1, r₂⟩).trans r₃)
  have x19₃ : t₃.getReg .x19 = t.getReg .x19 := hr .x19 (by decide) (by decide) (by decide)
    (by decide)
  have gs := h.same hm fun r a b c d _ ↦ hr r a b c d
  have x12₃ : t₃.getReg .x12 = BitVec.ofNat 64 j' := by
    rw [k₃ .x12 (by decide), hr₂' _ (by decide), x12₁]
  have tg := h.mem.slots.tag hj'l
  by_cases hc : t₂.getReg .x14 = 0
  · have hn : g.1.getD j' none = none := by
      cases e : g.1.getD j' none with
      | none => rfl
      | some _ => exact absurd (hz.mp hc) (tg.mp (by rw [e]; rfl))
    exact ⟨t₃, R, gs, x19₃, x12₃, Or.inr ⟨NB.g80000618_pc_not_taken h₃ hc, x11₃, hn⟩⟩
  · exact ⟨t₃, R, gs, x19₃, x12₃, Or.inl ⟨NB.g80000618_pc_taken h₃ hc, x13₃,
      tg.mpr fun e ↦ hc (hz.mpr e)⟩⟩

/-- `0x800005e0`: slot `j` occupied, `probeRust` from it with `fuel + 1` probes. -/
theorem probe_loop {w : Word} (hlen : g.1.length = 2 ^ 15) :
    ∀ fuel j (t : MachineState) r, GS s words u₀ i L Hb st q g t → t.getReg .x19 = w →
      j < 2 ^ 15 → t.pc = 0x800005e0 →
      t.getReg .x13 = u₀.getReg .x8 + BitVec.ofNat 64 (4 * j) + 2 →
      t.getReg .x12 = BitVec.ofNat 64 j → (g.1.getD j none).isSome = true →
      Model.probeRust w g.2.2 g.1 (fuel + 1) j = some r →
      ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ GP s words u₀ i L Hb st q g r v) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j t r h hw hj hpc hx13 _ hs hp
    obtain ⟨gv, hgv⟩ := Option.isSome_iff_exists.mp hs
    rw [Model.probeRust, hgv] at hp
    obtain ⟨v, rv, hd | ⟨he, hgp⟩ | ⟨hne, -⟩⟩ := probe_read h hj hpc hx13 hgv
    · exact ⟨v, rv, Or.inl hd⟩
    · rw [hw] at he
      simp only [he, ↓reduceIte, Option.some.injEq] at hp
      subst hp
      exact ⟨v, rv, Or.inr hgp⟩
    · rw [hw] at hne
      simp only [hne, ↓reduceIte, Model.probeRust] at hp
      cases hp
  | succ f ih =>
    intro j t r h hw hj hpc hx13 hx12 hs hp
    obtain ⟨gv, hgv⟩ := Option.isSome_iff_exists.mp hs
    rw [Model.probeRust, hgv] at hp
    obtain ⟨v, rv, hd | ⟨he, hgp⟩ | ⟨hne, gs, hpcv, x12v, x19v⟩⟩ := probe_read h hj hpc hx13 hgv
    · exact ⟨v, rv, Or.inl hd⟩
    · rw [hw] at he
      simp only [he, ↓reduceIte, Option.some.injEq] at hp
      subst hp
      exact ⟨v, rv, Or.inr hgp⟩
    · rw [hw] at hne
      simp only [hne, ↓reduceIte, hlen] at hp
      obtain ⟨v', rv', gs', x19', x12', hnext | hnext⟩ := probe_next gs hpcv hj (by rw [x12v, hx12])
      · obtain ⟨hpc', hx13', hs'⟩ := hnext
        obtain ⟨u, ru, hu⟩ := ih ((j + 1) % 2 ^ 15) v' r gs' (by rw [x19', x19v, hw])
          (Nat.mod_lt _ (by decide)) hpc' hx13' x12' hs' hp
        exact ⟨u, rv.trans (rv'.trans ru), hu⟩
      · obtain ⟨hpc', hx11', hn'⟩ := hnext
        rw [Model.probeRust, hn'] at hp
        simp only [Option.some.injEq] at hp
        subst hp
        obtain ⟨u, ru, hu⟩ := probe_new gs' hpc' (Nat.mod_lt _ (by decide)) hx11' hlen
        rw [x19', x19v, hw] at hu
        exact ⟨u, rv.trans (rv'.trans ru), hu⟩

/-- `0x800005bc`: the probe from `slot_of(word)`. -/
theorem probe_first (h : GS s words u₀ i L Hb st q g t) (hpc : t.pc = 0x800005bc)
    (hlen : g.1.length = 2 ^ 15) {r : List (Option (BitVec 16)) × List (BitVec 64) × BitVec 16}
    (hp : Model.probeRust (t.getReg .x19) g.2.2 g.1 g.1.length
      (Model.slotOfRust (t.getReg .x19)) = some r) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ GP s words u₀ i L Hb st q g r v) := by
  have hSL := h.k.a.slots
  have hGO := h.k.a.groupOf
  have hhi := h.k.ng.heap.hi
  have hH0 := h.k.ng.mono
  simp only [heapStart] at hSL
  simp only [heapNext, heapEnd] at hGO hhi hH0
  set w := t.getReg .x19 with hw
  set j := Model.slotOfRust w with hj
  have hjl : j < 2 ^ 15 := Model.slotOfRust_lt w
  have hC : t.getMem 0xa0000018 = 0x9e3779b97f4a7c15 := (h.k.ng.minv h.k.a).rodata.word
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches NB.g800005bc_spec hpc trivial
  have k₁ := NB.g800005bc_keeps h₁
  have x12₁ : t₁.getReg .x12 = BitVec.ofNat 64 j := by
    rw [NB.g800005bc_x12 h₁, hC, ← hw, hj, Model.slotOfRust, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl
  have x11₁ : t₁.getReg .x11 = u₀.getReg .x8 + BitVec.ofNat 64 (4 * j) := by
    rw [NB.g800005bc_x11 h₁, ← NB.g800005bc_x12 h₁, x12₁, h.x8,
      show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul, Nat.mul_comm]
  obtain ⟨t₂, r₂, hpc₂, hr₂, hm₂⟩ := step_lhu (code := Image.code) (s := t₁) (rd := .x13)
    (rs1 := .x11) (off := 0) (by rw [NB.g800005bc_pc h₁]; exact fetch_of (by decide +kernel))
    (by
      rw [off0, x11₁]
      exact valid2_of (by addr_omega [hSL, hjl]) (by addr_omega [hSL, hjl, hGO, hhi, hH0])
        (by addr_omega [hSL, hjl]))
  rw [off0, x11₁] at hr₂
  have hr₂' : ∀ r, r ≠ .x13 → t₂.getReg r = t₁.getReg r := fun r hr ↦ by rw [hr₂]; simp [hr]
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches NB.g800005d8_spec (by
    rw [hpc₂, NB.g800005bc_pc h₁]; rfl) trivial
  have hm : ∀ a, t₂.getMem a = t.getMem a := fun a ↦ by rw [hm₂, NB.g800005bc_mem_same h₁]
  have hm₃ : ∀ a, t₃.getMem a = t.getMem a := fun a ↦ by rw [NB.g800005d8_mem_same h₃, hm]
  have k₃ := NB.g800005d8_keeps h₃
  have hr : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → t₃.getReg r = t.getReg r := by
    intro r h11 h12 h13
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first
      | contradiction
      | rw [k₃ _ (by decide), hr₂' _ (by decide), k₁ _ (by decide)]
      | rfl
  have gs := h.same hm₃ fun r a b c _ _ ↦ hr r a b c
  have x13₂ : t₂.getReg .x13 = (t.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j))).zeroExtend 64 := by
    rw [hr₂, getHalfword_same (NB.g800005bc_mem_same h₁)]; simp
  have tg := h.mem.slots.tag hjl
  have R : Reaches Image.code t t₃ := r₁.trans ((show Reaches Image.code t₁ t₂ from ⟨1, r₂⟩).trans r₃)
  have hfuel : g.1.length = (2 ^ 15 - 1) + 1 := by omega
  rw [hfuel] at hp
  have x19₃ : t₃.getReg .x19 = w := hr .x19 (by decide) (by decide) (by decide)
  have x11₃ : t₃.getReg .x11 = u₀.getReg .x8 + BitVec.ofNat 64 (4 * j) := by
    rw [k₃ .x11 (by decide), hr₂' _ (by decide), x11₁]
  by_cases hc : t₂.getReg .x13 = 0
  · have hn : g.1.getD j none = none := by
      cases e : g.1.getD j none with
      | none => rfl
      | some _ =>
        refine absurd ?_ (tg.mp (by rw [e]; rfl))
        rw [x13₂] at hc
        apply BitVec.eq_of_toNat_eq
        have := congrArg BitVec.toNat hc
        simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth] at this
        have := (t.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j))).isLt
        have h0 : (0 : Word).toNat = 0 := rfl
        have h0' : (0 : BitVec 16).toNat = 0 := rfl
        omega
    rw [Model.probeRust, hn] at hp
    simp only [Option.some.injEq] at hp
    subst hp
    obtain ⟨v, rv, hv⟩ := probe_new gs (NB.g800005d8_pc_taken h₃ hc) hjl x11₃ hlen
    rw [x19₃] at hv
    exact ⟨v, R.trans rv, hv⟩
  · have hs : (g.1.getD j none).isSome = true := tg.mpr fun e ↦ hc (by rw [x13₂, e]; rfl)
    obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b800005dc_spec (NB.g800005d8_pc_not_taken h₃ hc)
      trivial
    have k₄ := b800005dc_keeps h₄
    have gs₄ := gs.same (fun a ↦ b800005dc_mem_same h₄ a) fun r _ _ h13 _ _ ↦ by
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
      all_goals first | contradiction | exact k₄ _ (by decide) | rfl
    obtain ⟨v, rv, hv⟩ := probe_loop hlen (2 ^ 15 - 1) j t₄ r gs₄
      (by rw [k₄ .x19 (by decide), x19₃]) hjl (b800005dc_pc h₄)
      (by rw [b800005dc_x13 h₄, x11₃]) (by rw [k₄ .x12 (by decide), k₃ .x12 (by decide), hr₂' _ (by decide), x12₁])
      hs hp
    exact ⟨v, R.trans (r₄.trans rv), hv⟩

end

end Rv64Verifier.Proofs.Main
