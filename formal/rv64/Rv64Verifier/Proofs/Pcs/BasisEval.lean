import Rv64Verifier.Proofs.Pcs.BasisBase

/-!
# `<StackBasis>::evaluate`: the dispatch on the claim's tag, and the `Eq` weight
-/

namespace Rv64Verifier.Proofs.Pcs.Basis
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F55
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-! ## What the loop keeps -/

/-- A word of a region read keeps its value. -/
theorem Inv.word {s u : MachineState} {nx : Word} (h : Inv s u nx) {a : Word} {n : Nat}
    (hs : Src s basisStack a n) {x : Word} (h1 : a.toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ a.toNat + n) :
    u.getMem x = s.getMem x := by
  have hb := hs.bound
  rcases hb with h0 | h0
  · omega
  · exact DFrame.word h.mem (fun y hy ↦ Inv.src h hs y (by addr_omega [hy, h1, h2, h0]))
      (by addr_omega [h1, h2, h0])

/-- `E`s of a region read keep their values. -/
theorem Inv.eList {s u : MachineState} {nx : Word} (h : Inv s u nx) {a : Word} {n : Nat}
    (hs : Src s basisStack a (24 * n)) : eListAt u a n = eListAt s a n :=
  DFrame.eList h.mem (Inv.src h hs) (by
    rcases hs.bound with h0 | h0
    · left; omega
    · right; omega)

theorem claims_region {s : MachineState} (hpre : BasisPre s) {k : Nat} (hk : k < ncl s) :
    Region (clp s) (88 * ncl s) :=
  hpre.claims.region.resolve_left (by simp only [basisClaimsLen] at *; simp only [ncl] at hk; omega)

/-- A word of claim `k`, at offset `o`, keeps its value. -/
theorem Inv.claim {s u : MachineState} {nx : Word} (hpre : BasisPre s) (h : Inv s u nx) {k : Nat}
    (hk : k < ncl s) {o : Nat} (ho : o + 8 ≤ 88) :
    u.getMem (claimAddr s k + BitVec.ofNat 64 o) = s.getMem (claimAddr s k + BitVec.ofNat 64 o) := by
  have hC := Region.bounds (claims_region hpre hk)
  exact Inv.word h hpre.claims (by simp only [claimAddr]; addr_omega [hC, hk, ho])
    (by simp only [claimAddr, basisClaimsLen, basisClaimsPtr]; addr_omega [hC, hk, ho])

/-- The weights pushed are kept by a callee writing the stack, `NEXT` and the heap from `nx`. -/
theorem ws_keep {s u v : MachineState} {nx WP : Word} {k : Nat} (hpre : BasisPre s)
    (hh : BufOk s WP nx) (hfit : nx.toNat ≤ heapEnd) (hk : k < ncl s) {X : Word → Prop} (hX : DFrame u v X)
    (hXsub : ∀ a, X a → Within a (stackLo s basisStack) basisStack ∨ Within a nextAddr 8 ∨
      nx.toNat ≤ a.toNat) (l : Nat) (hl : l < k) :
    eAt v (WP + BitVec.ofNat 64 (24 * l)) = eAt u (WP + BitVec.ofNat 64 (24 * l)) := by
  have hb := bounds hpre
  have hPr := hh.range.resolve_left (by omega)
  have hab := hpre.stack.above
  have hnx8 := hpre.stack.next
  simp only [ncl] at hPr hk
  refine DFrame.eAt' hX (fun x hx hXx ↦ ?_) (by addr_omega [hPr, hl, hk])
  rcases hXsub x hXx with h | h | h
  · addr_omega [hx, h, hPr, hl, hk, hab, hb, hfit]
  · addr_omega [hx, h, hPr, hl, hk, hfit]
  · addr_omega [hx, h, hPr, hl, hk]

theorem Regs.of_eq {s u v : MachineState} {WP : Word} {k : Nat} (h : Regs s u WP k)
    (hr : ∀ r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26],
      v.getReg r = u.getReg r) : Regs s v WP k where
  x8 := (hr _ (by decide)).trans h.x8
  x9 := (hr _ (by decide)).trans h.x9
  x18 := (hr _ (by decide)).trans h.x18
  x19 := (hr _ (by decide)).trans h.x19
  x20 := (hr _ (by decide)).trans h.x20
  x21 := (hr _ (by decide)).trans h.x21
  x22 := (hr _ (by decide)).trans h.x22
  x23 := (hr _ (by decide)).trans h.x23
  x24 := (hr _ (by decide)).trans h.x24
  x25 := (hr _ (by decide)).trans h.x25
  x26 := (hr _ (by decide)).trans h.x26

/-- A block that writes nothing. -/
theorem Head.same {s u v : MachineState} {nx WP : Word} {k : Nat} {pc pc' : Word}
    (h : Head s u nx WP k pc) (hm : ∀ a, v.getMem a = u.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
      v.getReg r = u.getReg r) (hpc : v.pc = pc') : Head s v nx WP k pc' where
  toRegs := h.toRegs.of_eq fun r hr' ↦ hr r (Runtime.mem_of_mem hr' _)
  inv := h.inv.same hm (hr _ (by decide)) (fun r hr' ↦ by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hr _ (by decide))
  pc := hpc
  lt := h.lt
  buf := h.buf
  ws := fun l hl ↦ by rw [h.ws l hl]; simp only [eAt, hm]

/-! ## The dispatch -/

theorem xor_tag_zero (x : Word) : x ^^^ 0x8000000000000000 = 0 ↔ x = eqTag := by
  constructor
  · intro h
    have := congrArg (· ^^^ (0x8000000000000000 : Word)) h
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
    exact this
  · rintro rfl; decide

theorem xor_tag_one (x : Word) : x ^^^ 0x8000000000000000 = 1 ↔ x = ringTag := by
  constructor
  · intro h
    have := congrArg (· ^^^ (0x8000000000000000 : Word)) h
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
    rw [this]; decide
  · rintro rfl; decide

theorem dispatch {s u : MachineState} {nx WP : Word} {k : Nat} (hpre : BasisPre s)
    (hh : Head s u nx WP k 0x8000d1ac) :
    ∃ v, Reaches Image.code u v ∧
      ((s.getMem (claimAddr s k) = eqTag ∧ Head s v nx WP k 0x8000d164) ∨
       (s.getMem (claimAddr s k) = ringTag ∧ Head s v nx WP k 0x8000d1cc) ∨
       (s.getMem (claimAddr s k) ≠ eqTag ∧ s.getMem (claimAddr s k) ≠ ringTag ∧
         Head s v nx WP k 0x8000d1e8)) := by
  have hk := hh.lt
  have hCr := claims_region hpre hk
  have hC := Region.bounds hCr
  have htag : u.getMem (claimAddr s k) = s.getMem (claimAddr s k) := by
    have := Inv.claim hpre hh.inv hk (o := 0) (by decide)
    simpa using this
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000d1ac_spec hh.pc (by
    rv_eval [hh.x20]
    exact Region.valid hCr (by simp only [claimAddr]; addr_omega [hC, hk])
      (by simp only [claimAddr, ncl] at hk ⊢; addr_omega [hC, hk])
      (by simp only [claimAddr]; addr_omega [hC, hk]))
  have k₁ := b8000d1ac_keeps h₁
  have hd₁ := hh.same (b8000d1ac_mem_same h₁) (fun r hr ↦ k₁ r (Runtime.mem_of_mem hr _)) rfl
  set T := s.getMem (claimAddr s k) with hT
  cases hslt : BitVec.slt T 0
  · -- not negative: `PlacedRing`
    have hne : T ≠ eqTag ∧ T ≠ ringTag := by
      constructor <;> (intro h; rw [h] at hslt; revert hslt; decide)
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000d1b4_spec
      (b8000d1ac_pc_not_taken h₁ (by rw [hh.x20, htag]; exact hslt)) trivial
    have k₂ := b8000d1b4_keeps h₂
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000d1c8_spec (b8000d1b4_pc h₂) trivial
    have k₃ := b8000d1c8_keeps h₃
    have hpc₃ := b8000d1c8_pc_taken h₃ (by
      rw [b8000d1b4_x10 h₂, k₂ .x26 (by decide), k₁ .x26 (by decide), hh.x26]; decide)
    refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inr ⟨hne.1, hne.2,
      (hd₁.same (b8000d1b4_mem_same h₂) (fun r hr ↦ k₂ r (Runtime.mem_of_mem hr _)) rfl).same
        (b8000d1c8_mem_same h₃) (fun r hr ↦ k₃ r (Runtime.mem_of_mem hr _)) hpc₃⟩)⟩
  · -- negative: the niche
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000d1c0_spec
      (b8000d1ac_pc_taken h₁ (by rw [hh.x20, htag]; exact hslt)) trivial
    have k₂ := b8000d1c0_keeps h₂
    have hx10 : t₁.getReg .x10 ^^^ t₁.getReg .x24 = T ^^^ 0x8000000000000000 := by
      rw [b8000d1ac_x10 h₁, k₁ .x24 (by decide), hh.x24, hh.x20, htag]
    have hd₂ := hd₁.same (b8000d1c0_mem_same h₂) (fun r hr ↦ k₂ r (Runtime.mem_of_mem hr _)) rfl
    by_cases he : T = eqTag
    · refine ⟨t₂, hr₁.trans hr₂, Or.inl ⟨he, hd₂.same (fun _ ↦ rfl) (fun _ _ ↦ rfl)
        (b8000d1c0_pc_taken h₂ (by rw [hx10]; exact (xor_tag_zero T).mpr he))⟩⟩
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000d1c8_spec
      (b8000d1c0_pc_not_taken h₂ (by rw [hx10]; exact fun h ↦ he ((xor_tag_zero T).mp h))) trivial
    have k₃ := b8000d1c8_keeps h₃
    have hx10' : t₂.getReg .x10 = T ^^^ 0x8000000000000000 := by rw [b8000d1c0_x10 h₂, hx10]
    have hx26 : t₂.getReg .x26 = 1 := by rw [k₂ .x26 (by decide), k₁ .x26 (by decide), hh.x26]
    have hd₃ (pc' : Word) (hpc : t₃.pc = pc') : Head s t₃ nx WP k pc' :=
      hd₂.same (b8000d1c8_mem_same h₃) (fun r hr ↦ k₃ r (Runtime.mem_of_mem hr _)) hpc
    by_cases hr : T = ringTag
    · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inl ⟨hr, hd₃ _
        (b8000d1c8_pc_not_taken h₃ (by rw [hx10', hx26]; exact (xor_tag_one T).mpr hr))⟩)⟩
    · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inr ⟨he, hr, hd₃ _
        (b8000d1c8_pc_taken h₃ (by rw [hx10', hx26]; exact fun h ↦ hr ((xor_tag_one T).mp h)))⟩)⟩

end Rv64Verifier.Proofs.Pcs.Basis
