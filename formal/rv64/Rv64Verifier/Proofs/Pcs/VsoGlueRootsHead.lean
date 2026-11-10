import Rv64Verifier.Proofs.Pcs.VsoGlueRootsSetup

/-!
# `verify_stacked_opening`'s final level: the subspace roots' loop, its head and exits

`RH`: at `0x8000bd1c`, `k` of the `n` rounds done, the model's state `st` (the roots so far, a
`Vec<K>` at `S - 128`, and the layer at `L`). `RX`: at `0x8000bdb4`, the rounds done. With `n = 0`,
`0x8000bc38` reserves nothing and `0x8000bc48` goes on at `0x8000bdc0` with the roots `[1]`;
`0x8000bdb4` reloads the counts and the roots' pointer (`rootsZero`, `rootsExit`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000bd1c`, `k` rounds of `n` done: the roots `st.1` in the `Vec` at `S - 128`, the layer
`st.2` at `L`. -/
structure RH (s v w t : MachineState) (a : Word) (n k : ℕ) (st : List K × List K) (L : Word) :
    Prop where
  pf : RPF s v w t
  sl : RSL s w t a n L
  pc : t.pc = 0x8000bd1c
  klt : k < n
  loop : Model.Pcs.subspaceRootsRust n = (Model.Pcs.subspaceRootsLoop (n - k) st).map (·.1)
  len1 : st.1.length = k + 1
  len2 : st.2.length = n - k
  x9 : t.getReg .x9 = BitVec.ofNat 64 (n - k)
  x13 : t.getReg .x13 = BitVec.ofNat 64 k
  x19 : t.getReg .x19 = BitVec.ofNat 64 (8 * (n - k))
  x20 : t.getReg .x20 = BitVec.ofNat 64 (k + 1)
  x21 : t.getReg .x21 = t.getMem (s.getReg .x2 - 120)
  Lb : L.toNat % 8 = 0 ∧ heapNext w ≤ L.toNat ∧ L.toNat + 8 * n ≤ heapNext t
  lay : kListAt t L (n - k) = st.2
  rcap : k + 1 ≤ (t.getMem (s.getReg .x2 - 128)).toNat
  rlen : t.getMem (s.getReg .x2 - 112) = BitVec.ofNat 64 (k + 1)
  Rb : (t.getMem (s.getReg .x2 - 120)).toNat % 8 = 0 ∧
    heapNext w ≤ (t.getMem (s.getReg .x2 - 120)).toNat ∧
    (t.getMem (s.getReg .x2 - 120)).toNat + 8 * (t.getMem (s.getReg .x2 - 128)).toNat ≤ heapNext t
  RL : (t.getMem (s.getReg .x2 - 120)).toNat + 8 * (t.getMem (s.getReg .x2 - 128)).toNat ≤ L.toNat ∨
    L.toNat + 8 * n ≤ (t.getMem (s.getReg .x2 - 120)).toNat
  rts : kListAt t (t.getMem (s.getReg .x2 - 120)) (k + 1) = st.1

/-- At `0x8000bdb4`, the rounds done: the roots `rs` in the `Vec` at `S - 128`. -/
structure RX (s v w t : MachineState) (a : Word) (n : ℕ) (rs : List K) (L : Word) : Prop where
  pf : RPF s v w t
  sl : RSL s w t a n L
  pc : t.pc = 0x8000bdb4
  roots : Model.Pcs.subspaceRootsRust n = some rs
  rlen : rs.length = n + 1
  x20 : t.getReg .x20 = BitVec.ofNat 64 (n + 1)
  x26 : t.getReg .x26 = BitVec.ofNat 64 n
  Rb : (t.getMem (s.getReg .x2 - 120)).toNat % 8 = 0 ∧
    heapNext w ≤ (t.getMem (s.getReg .x2 - 120)).toNat ∧
    (t.getMem (s.getReg .x2 - 120)).toNat + 8 * (n + 1) ≤ heapNext t
  rts : kListAt t (t.getMem (s.getReg .x2 - 120)) (n + 1) = rs

theorem kListAt_one (t : MachineState) (p : Word) (h : t.getMem p = 1) : kListAt t p 1 = [1] := by
  simp only [kListAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, add_ofNat_zero, h]
  rfl

/-- **No rounds**: `n = 0`, the roots `[1]`. -/
theorem rootsZero (hRF : ReserveFastSpec 0x8000d628) {s v w t : MachineState} {a R L : Word}
    (hpre : VsoPre s) (h : RA s v w t a 0 R L) :
    ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨ ∃ rs, QR s v w t' a 0 rs) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have sp := h.pf.sp
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bc38_spec (by rw [h.pc]; rfl) trivial
  have hm₁ := b8000bc38_mem_same h₁
  have k₁ := b8000bc38_keeps h₁
  have P₁ := h.pf.same hpre hm₁ (k₁ .x2 (by decide))
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 160 := by rw [b8000bc38_x10 h₁, sp]; rv_eval []
  obtain ⟨t₂, r₂, ⟨hpc₂, hpres₂, hx₂, hm₂⟩ | hd₂⟩ := hRF.call (Reaches.refl t₁) (b8000bc38_pc h₁) ⟨by
      rw [x10₁]; valid_sub hst.valid [hb], by
      rw [x10₁, b8000bc38_x11 h₁]; simp only [vecLen, vecCap]; rv_eval [hm₁, h.m144, h.m160]
      decide⟩
  swap
  · exact ⟨t₂, r₁.trans r₂, Or.inl hd₂⟩
  have P₂ := P₁.same hpre hm₂ (hpres₂ .x2 (by decide))
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000bc48_spec
    (by rw [hpc₂, returnAddress_eq, b8000bc38_x1 h₁]; decide) trivial
  have hm₃ := b8000bc48_mem_same h₃
  have k₃ := b8000bc48_keeps h₃
  have P₃ := P₂.same hpre hm₃ (k₃ .x2 (by decide))
  have hm (y : Word) : t₃.getMem y = t.getMem y := by rw [hm₃, hm₂, hm₁]
  have hr (r : Reg) (h1 : r ∈ calleeSaved) (h3 : t₃.getReg r = t₂.getReg r)
      (h0 : t₁.getReg r = t.getReg r) : t₃.getReg r = t.getReg r := by
    rw [h3, hpres₂ r h1, h0]
  have hn : heapNext t₃ = heapNext t := by simp only [heapNext, hm]
  obtain ⟨hR8, hRw, hRt⟩ := h.Rb
  refine ⟨t₃, r₁.trans (r₂.trans r₃), Or.inr ⟨[1], {
    gs := P₃.gs
    fr := P₃.fr
    pc := b8000bc48_pc h₃
    roots := rfl
    rlen := rfl
    x20 := b8000bc48_x20 h₃
    x21 := by
      rw [hr .x21 (by decide) (k₃ .x21 (by decide)) (k₁ .x21 (by decide)), h.x21, hn]
      exact ⟨hR8, hRw, hRt⟩
    rmem := by
      rw [hr .x21 (by decide) (k₃ .x21 (by decide)) (k₁ .x21 (by decide)), h.x21]
      exact kListAt_one _ _ (by rw [hm]; exact h.r0)
    x19 := by rw [hr .x19 (by decide) (k₃ .x19 (by decide)) (k₁ .x19 (by decide)), h.x19]
    x23 := by rw [hr .x23 (by decide) (k₃ .x23 (by decide)) (k₁ .x23 (by decide)), h.x23]
    x26 := by rw [hr .x26 (by decide) (k₃ .x26 (by decide)) (k₁ .x26 (by decide)), h.x26]
    m856 := by rw [hm]; exact h.m856
    m824 := by rw [hm]; exact h.m824
    m816 := by rw [hm]; exact h.m816
    m808 := by rw [hm]; exact h.m808
    keep := fun y hy ↦ by rw [hm]; exact h.keep y hy }⟩⟩

/-- **The rounds done**: `0x8000bdb4` reloads the counts and the roots' pointer. -/
theorem rootsExit {s v w t : MachineState} {a L : Word} {n : ℕ} {rs : List K}
    (hpre : VsoPre s) (h : RX s v w t a n rs L) :
    ∃ t', Reaches Image.code t t' ∧ QR s v w t' a n rs := by
  have hb := bounds hpre
  have hst := hpre.stack
  have sp := h.pf.sp
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bdb4_spec h.pc (by
    rv_eval [sp]; and_intros <;> valid_access hst.valid [hb])
  have hm₁ := b8000bdb4_mem_same h₁
  have k₁ := b8000bdb4_keeps h₁
  have P₁ := h.pf.same hpre hm₁ (k₁ .x2 (by decide))
  have hn : heapNext t₁ = heapNext t := by simp only [heapNext, hm₁]
  have x21 : t₁.getReg .x21 = t.getMem (s.getReg .x2 - 120) := by
    rw [b8000bdb4_x21 h₁, sp]; rv_eval []
  refine ⟨t₁, r₁, {
    gs := P₁.gs
    fr := P₁.fr
    pc := b8000bdb4_pc h₁
    roots := h.roots
    rlen := h.rlen
    x20 := by rw [k₁ .x20 (by decide), h.x20]
    x21 := by rw [x21, hn]; exact h.Rb
    rmem := by rw [x21, ← h.rts]; exact kListAt_congr fun i _ ↦ hm₁ _
    x19 := by rw [b8000bdb4_x19 h₁, sp, ← h.sl.m800]; rv_eval []
    x23 := by rw [b8000bdb4_x23 h₁, sp, ← h.sl.m888]; rv_eval []
    x26 := by rw [k₁ .x26 (by decide), h.x26]
    m856 := by rw [hm₁]; exact h.sl.m856
    m824 := by rw [hm₁]; exact h.sl.m824
    m816 := by rw [hm₁]; exact h.sl.m816
    m808 := by rw [hm₁]; exact h.sl.m808
    keep := fun y hy ↦ by rw [hm₁]; exact h.sl.keep y hy }⟩

end Rv64Verifier.Proofs.Pcs.Vso
