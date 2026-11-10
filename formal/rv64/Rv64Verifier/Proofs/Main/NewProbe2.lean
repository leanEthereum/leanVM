import Rv64Verifier.Proofs.Main.NewProbe

/-!
# `group`'s probe, slot by slot

A free slot takes the next group (`slot_store`, `0x80000620`, then `grow_distinct` and `push_57c`:
`probe_new`); an occupied one holding another word moves to the next (`probe_loop`, by induction on
`probeRust`'s fuel); the first slot is `slot_of(word)`'s (`probe_first`). Each ends at `0x80000594`
with the word's group in `a1` (`GP`), or at a dead end.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

section
variable {s u₀ t t' : MachineState} {words : List Word} {i L Hb q : Nat} {st : Model.NewState}
  {g : GrpSt}

/-- A step that writes only the four bytes of slot `j`. -/
theorem GS.slotWrite (h : GS s words u₀ i L Hb st q g t) {j : Nat} (hj : j < 2 ^ 15)
    (hf : BFrame t t' (Within · (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j)) 4))
    (hr : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x19 → t'.getReg r = t.getReg r)
    {sl : List (Option (BitVec 16))} (hs : SlotsRel t' (u₀.getReg .x8) sl) :
    GS s words u₀ i L Hb st q (sl, g.2.1, g.2.2) t' := by
  have hSL := h.k.a.slots
  have hGO := h.k.a.groupOf
  have hH0 := h.k.hb0
  have hhb := h.k.hb
  have hhi := h.k.ng.heap.hi
  simp only [heapStart] at hSL
  simp only [heapNext, heapEnd] at hGO hH0 hhb hhi
  have hlow : ∀ a : Word, (u₀.getReg .x8).toNat + 0x20000 ≤ a.toNat → byteAt t' a = byteAt t a :=
    fun a ha ↦ hf a fun hw ↦ by addr_omega [hw, ha, hj]
  have hmsp : ∀ c : Nat, c % 8 = 0 → c + 8 ≤ 4096 →
      t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := fun c h8 hc ↦
    hf.getMem (by addr_omega [h8, hc]) fun k hk hw ↦ by addr_omega [hw, hk, hc, hj, hSL, hGO, hH0, hhb, hhi]
  have hn : heapNext t' = heapNext t := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hf.getMem (a := nextAddr) (by decide) fun k hk hw ↦ by
      addr_omega [hw, hk, hj, hSL, hGO, hH0, hhb, hhi])
  have hsp : t'.getReg .x2 = msp := (hr .x2 (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans h.k.ng.sp
  have hW : ∀ a, Within a (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j)) 4 → WB (heapNext u₀) Hb a :=
    fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by
      simp only [heapStart]; addr_omega [ha, hSL, hj], by
      simp only [heapNext]; addr_omega [ha, hSL, hGO, hj]⟩))))))
  have hHb : Hb ≤ heapEnd := by simp only [heapEnd]; omega
  obtain ⟨vecs, bufs⟩ := VecsAt.frame h.vecs h.bufs hf (fun a ha ↦ WB.vec h.k.hb0 hHb (hW a ha))
    hHb
  have m := h.mem
  have v104 : t'.getMem (msp + 104) = t.getMem (msp + 104) := hmsp 104 (by decide) (by decide)
  have v112 : t'.getMem (msp + 112) = t.getMem (msp + 112) := hmsp 112 (by decide) (by decide)
  have v120 : t'.getMem (msp + 120) = t.getMem (msp + 120) := hmsp 120 (by decide) (by decide)
  have hD : ∀ k < g.2.2.length, t'.getMem (t.getMem (msp + 112) + BitVec.ofNat 64 (8 * k)) =
      t.getMem (t.getMem (msp + 112) + BitVec.ofNat 64 (8 * k)) := by
    intro k hk
    have hc := m.cap
    have hal := m.al
    rcases m.buf with h0 | ⟨h1, h2⟩
    · omega
    · exact getMem_eq_of_bytes (by addr_omega [hal, hk, h1, h2, hhi, hc])
        (by addr_omega [hal, hk, h1, h2, hhi, hc]) fun x hx ↦ hlow _ (by
          addr_omega [h1, h2, hk, hx, hhi, hH0, hGO, hSL, hc])
  refine ⟨h.k.frame hf hW hsp ⟨by rw [hn]; exact h.k.ng.heap.lo, by rw [hn]; exact h.k.ng.heap.hi⟩
    (le_of_eq hn.symm), vecs, bufs, ⟨hs, ?_, by rw [v120]; exact m.len, by rw [v104]; exact m.cap,
    by rw [v112]; exact m.al, by rw [v112, v104, hn]; exact m.buf, ?_⟩, h.hq, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show halvesAt t' _ _ = g.2.1
    rw [← m.groupOf]
    exact halvesAt_keep hGO.1 (fun a h1 _ ↦ hlow a (by omega)) (by addr_omega [hGO, hhi, hH0, hhb])
  · show t'.readWords _ g.2.2.length = g.2.2
    have e := m.dist
    rw [v112, readWords_eq_map]
    rw [readWords_eq_map] at e
    exact (List.map_congr_left fun k hk ↦ hD k (List.mem_range.mp hk)).trans e
  all_goals first
    | (rw [hr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; first
        | exact h.x8 | exact h.x9 | exact h.x15 | exact h.x16 | exact h.x18 | exact h.x20
        | exact h.x21 | exact h.x22 | exact h.x23 | exact h.x24 | exact h.x25 | exact h.x26
        | exact h.x27 | (rw [v112]; exact h.x10))

end

theorem SlotsRel.set {t t' : MachineState} {SL : Word} {sl : List (Option (BitVec 16))} {j : Nat}
    {v : BitVec 16} (h : SlotsRel t SL sl) (hS : SL.toNat % 2 = 0 ∧ SL.toNat + 0x20000 < 2 ^ 64)
    (hj : j < 2 ^ 15) (hlen : sl.length = 2 ^ 15)
    (hf : BFrame t t' (Within · (SL + BitVec.ofNat 64 (4 * j)) 4))
    (h0 : t'.getHalfword (SL + BitVec.ofNat 64 (4 * j)) ≠ 0)
    (h2 : t'.getHalfword (SL + BitVec.ofNat 64 (4 * j) + 2) = v) :
    SlotsRel t' SL (sl.set j (some v)) := by
  intro k hk
  rw [Model.getD_set_eq]
  by_cases e : j = k
  · subst e
    rw [ite_eq_left ⟨rfl, by omega⟩]
    refine ⟨fun hn ↦ ?_, fun g hg ↦ ?_⟩
    · cases hn
    · cases hg; exact ⟨h0, h2⟩
  · rw [ite_eq_right fun h' ↦ e h'.1]
    have k0 : t'.getHalfword (SL + BitVec.ofNat 64 (4 * k)) = t.getHalfword (SL + BitVec.ofNat 64 (4 * k)) :=
      getHalfword_eq_of_bytes (by addr_omega [hS.1, hS.2, hk])
        (hf _ fun hw ↦ by addr_omega [hw, hS.2, hk, hj, e])
        (hf _ fun hw ↦ by addr_omega [hw, hS.2, hk, hj, e])
    have k2 : t'.getHalfword (SL + BitVec.ofNat 64 (4 * k) + 2) =
        t.getHalfword (SL + BitVec.ofNat 64 (4 * k) + 2) :=
      getHalfword_eq_of_bytes (by addr_omega [hS.1, hS.2, hk])
        (hf _ fun hw ↦ by addr_omega [hw, hS.2, hk, hj, e])
        (hf _ fun hw ↦ by addr_omega [hw, hS.2, hk, hj, e])
    rw [k0, k2]
    exact h k hk

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb q : Nat} {st : Model.NewState}
  {g : GrpSt}

/-- `0x80000620`: slot `j` free, it takes the next group: tag `1`, group `distinct.len()`. -/
theorem slot_store (h : GS s words u₀ i L Hb st q g t) (hpc : t.pc = 0x80000620) {j : Nat}
    (hj : j < 2 ^ 15) (hx11 : t.getReg .x11 = u₀.getReg .x8 + BitVec.ofNat 64 (4 * j))
    (hlen : g.1.length = 2 ^ 15) :
    ∃ v, Reaches Image.code t v ∧
      GS s words u₀ i L Hb st q (g.1.set j (some (BitVec.ofNat 16 g.2.2.length)), g.2.1, g.2.2) v ∧
      v.getReg .x19 = t.getReg .x19 ∧
      ((v.pc = 0x8000057c ∧ g.2.2.length < (v.getMem (msp + 104)).toNat) ∨
        (v.pc = 0x80000630 ∧ v.getReg .x18 = v.getMem (msp + 104))) := by
  have hSL := h.k.a.slots
  have hGO := h.k.a.groupOf
  have hhi := h.k.ng.heap.hi
  have hH0 := h.k.ng.mono
  simp only [heapStart] at hSL
  simp only [heapNext, heapEnd] at hGO hhi hH0
  set p := u₀.getReg .x8 + BitVec.ofNat 64 (4 * j) with hp
  have hpn : p.toNat = (u₀.getReg .x8).toNat + 4 * j := by
    rw [hp]; addr_omega [hSL, hj, hGO, hhi, hH0]
  have hpb : p.toNat + 4 ≤ 0x78000000 := by rw [hpn]; omega
  have hp0 : 0x20000000 ≤ p.toNat := by rw [hpn]; omega
  have hp2 : p.toNat % 2 = 0 := by rw [hpn]; omega
  obtain ⟨t₁, r₁, hpc₁, hr₁, hh₁, hf₁⟩ := step_sh (code := Image.code) (rs1 := .x11) (rs2 := .x27)
    (off := 0) (by rw [hpc]; exact fetch_of (by decide +kernel))
    (by rw [off0, hx11]; exact valid2_of (by omega) (by omega) (by omega))
  rw [off0, hx11] at hh₁ hf₁
  have hoff2 : signExtend12 (2 : BitVec 12) = 2 := by decide
  obtain ⟨t₂, r₂, hpc₂, hr₂, hh₂, hf₂⟩ := step_sh (code := Image.code) (s := t₁) (rs1 := .x11)
    (rs2 := .x18) (off := 2) (by rw [hpc₁, hpc]; exact fetch_of (by decide +kernel))
    (by rw [hoff2, hr₁, hx11]
        exact valid2_of (by addr_omega [hpb, hp0]) (by addr_omega [hpb, hp0])
          (by addr_omega [hpb, hp0, hp2]))
  rw [hoff2, hr₁, hx11] at hh₂ hf₂
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches NB.g80000628_spec (by rw [hpc₂, hpc₁, hpc]; rfl) (by
    rv_eval []
    rw [hr₂, hr₁, h.k.ng.sp]
    decide)
  have k₃ := NB.g80000628_keeps h₃
  have hm₃ := NB.g80000628_mem_same h₃
  have hf : BFrame t t₃ (Within · p 4) := fun a ha ↦ by
    rw [byteAt_eq, hm₃, ← byteAt_eq]
    refine (hf₂.byte a fun h' ↦ ha ?_).trans (hf₁.byte a fun h' ↦ ha ?_)
    · rcases h' with h' | h' <;> rw [h'] <;> addr_omega [hpb]
    · rcases h' with h' | h' <;> rw [h'] <;> addr_omega [hpb]
  have hr : ∀ r, r ≠ .x11 → t₃.getReg r = t.getReg r := by
    intro r hr
    rw [← hr₁ r, ← hr₂ r]
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | contradiction | exact k₃ _ (by decide) | rfl
  have e0 : t₃.getHalfword p ≠ 0 := by
    rw [getHalfword_same hm₃,
      getHalfword_eq_of_bytes hp2 (hf₂.byte _ fun h' ↦ by
        rcases h' with h' | h' <;> have := congrArg BitVec.toNat h' <;> addr_omega [this, hpb])
        (hf₂.byte _ fun h' ↦ by
          rcases h' with h' | h' <;> have := congrArg BitVec.toNat h' <;> addr_omega [this, hpb]),
      hh₁, h.x27]
    decide
  have e2 : t₃.getHalfword (p + 2) = BitVec.ofNat 16 g.2.2.length := by
    rw [getHalfword_same hm₃, hh₂, hr₁, h.x18]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have gs := h.slotWrite hj hf (fun r h11 _ _ _ _ ↦ hr r h11)
    (SlotsRel.set h.mem.slots ⟨hSL.1, by omega⟩ hj hlen hf e0 e2)
  refine ⟨t₃, (show Reaches Image.code t t₁ from ⟨1, r₁⟩).trans
    ((show Reaches Image.code t₁ t₂ from ⟨1, r₂⟩).trans r₃), gs, hr .x19 (by decide), ?_⟩
  have m3 : t₃.getMem (msp + 104) = t.getMem (msp + 104) := by
    exact (hf.getMem (a := msp + 104) (by decide) fun k hk hw ↦ by addr_omega [hw, hk, hpb])
  by_cases e : t₂.getReg .x18 = t₂.getMem (t₂.getReg .x2 + 104)
  · right
    refine ⟨NB.g80000628_pc_not_taken h₃ e, ?_⟩
    rw [hr _ (by decide), m3]
    rw [hr₂ .x18, hr₂ .x2, hr₁ .x18, hr₁ .x2, h.k.ng.sp, ← hm₃, m3] at e
    exact e
  · left
    refine ⟨NB.g80000628_pc_taken h₃ e, ?_⟩
    rw [hr₂ .x18, hr₂ .x2, hr₁ .x18, hr₁ .x2, h.k.ng.sp, ← hm₃, m3, h.x18] at e
    have hc := h.mem.cap
    rw [m3]
    refine lt_of_le_of_ne hc fun he ↦ e ?_
    apply BitVec.eq_of_toNat_eq
    rw [← he, BitVec.toNat_ofNat]
    omega

end

end Rv64Verifier.Proofs.Main
