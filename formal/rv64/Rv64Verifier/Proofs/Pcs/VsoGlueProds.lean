import Rv64Verifier.Proofs.Pcs.VsoGlueProdsQuery

/-!
# `verify_stacked_opening`'s final level: the queries' products, summed (`ProdsSpec`)

`0x8000be44` takes the count `min(query weights, queries)` in `s3`; with none `0x8000bfc4` sums to
zero, else `0x8000be50` keeps the count, the roots' pointer, `24 n` and `n + 2` and clears the sum,
and the queries run (`prOuter`) to `0x8000baf8`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  Rv64Verifier.FieldContracts LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem pr_ofLimbs_zero :
    E.ofLimbs (BF64.ofBitVec 0) (BF64.ofBitVec 0) (BF64.ofBitVec 0) = 0 := by
  apply eq_of_limbs
  rw [limbs_ofLimbs, Model.limbs_zero]
  rfl

/-- The queries, from `i` on. -/
theorem prOuter (hBM : BaseMulSpec) (hMK : MulKSpec) (hM : MulSpec) (hSq : KSquareSpec)
    {s v w : MachineState} {n cnt : ℕ} {rs : List K} {xs : List E}
    {qs : List (BitVec 64)} {qw : List E} (hpre : VsoPre s) (hc : QC s v w n rs xs qs qw)
    (hcnt : cnt ≤ (w.getReg .x19).toNat ∧ cnt ≤ (w.getReg .x23).toNat)
    (hcl : (qw.zip qs).length = cnt) (hc64 : cnt < 2 ^ 64) : ∀ k i t, cnt - i = k →
      PrQ s v w t n cnt i (((qw.zip qs).take i).foldl (prSum rs xs) 0) →
      ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨ (t'.pc = 0x8000baf8 ∧
        PrX s v w t' n cnt ∧ E.ofLimbs (BF64.ofBitVec (t'.getReg .x23))
          (BF64.ofBitVec (t'.getReg .x25)) (BF64.ofBitVec (t'.getReg .x24)) =
            (qw.zip qs).foldl (prSum rs xs) 0)) := by
  intro k
  induction k with
  | zero => intro i t hk h; have := h.ilt; omega
  | succ k ih =>
    intro i t hk h
    have hil := h.ilt
    have hi : i < (qw.zip qs).length := by omega
    have e := pr_foldl_take_succ (prSum rs xs) 0 (qw.zip qs) hi
    have hz : (qw.zip qs)[i] = (qw.getD i 0, qs.getD i 0) := by
      rw [List.getElem_zip, List.getD_eq_getElem _ _ (by simp at hi; omega),
        List.getD_eq_getElem _ _ (by simp at hi; omega)]
    rw [hz] at e
    obtain ⟨t₁, r₁, h₁⟩ := prQuery hBM hMK hM hSq hpre hc hcnt h
    rcases h₁ with hd | h₁
    · exact ⟨t₁, r₁, Or.inl hd⟩
    obtain ⟨t₂, r₂, h₂⟩ := prNext hpre hc64 h₁
    rcases h₂ with ⟨hlt, h₂⟩ | ⟨heq, pc₂, P₂, v₂⟩
    · have h₂' : PrQ s v w t₂ n cnt (i + 1) (((qw.zip qs).take (i + 1)).foldl (prSum rs xs) 0) := by
        rw [e]; exact h₂
      obtain ⟨t₃, r₃, h₃⟩ := ih (i + 1) t₂ (by omega) h₂'
      exact ⟨t₃, r₁.trans (r₂.trans r₃), h₃⟩
    · refine ⟨t₂, r₁.trans r₂, Or.inr ⟨pc₂, P₂, ?_⟩⟩
      have hfull : (qw.zip qs).take (i + 1) = qw.zip qs := List.take_of_length_le (by omega)
      rw [v₂]
      conv_rhs => rw [← hfull]
      exact e.symm

/-- **The queries' products, summed**: `0x8000be44` to `0x8000baf8`. -/
theorem prods_spec (hBM : BaseMulSpec) (hMK : MulKSpec) (hM : MulSpec) (hSq : KSquareSpec) :
    ProdsSpec := by
  intro s v w n rs xs qs qw hpre hc
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := hc.gs.sp
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hhw := hc.gs.heap.hi
  simp only [heapEnd] at hhw
  have hrl := hc.ip.2.2
  have hn64 : n < 2 ^ 60 := by omega
  have hqwl : qw.length = (w.getReg .x19).toNat := by rw [← hc.qw, eListAt_length]
  have hqsl : qs.length = (w.getReg .x23).toNat := by rw [← hc.qs, readWords_length]
  -- `0x8000be44`, `0x8000be48`: the count
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000be44_spec hc.pc trivial
  have k₁ := b8000be44_keeps h₁
  have G₁ := hc.gs.same hpre (b8000be44_mem_same h₁) (k₁ .x2 (by decide))
  have hcnt : ∃ t₂, Reaches Image.code w t₂ ∧ t₂.pc = 0x8000be4c ∧ GS s v t₂ ∧
      (∀ a, t₂.getMem a = w.getMem a) ∧
      t₂.getReg .x19 = BitVec.ofNat 64 (min (w.getReg .x19).toNat (w.getReg .x23).toNat) ∧
      ∀ r ∈ ([.x2, .x8, .x20, .x21, .x22, .x23, .x24, .x25, .x26] : List Reg),
        t₂.getReg r = w.getReg r := by
    by_cases hlt : (w.getReg .x19).toNat < (w.getReg .x23).toNat
    · refine ⟨t₁, r₁, b8000be44_pc_taken h₁ hlt, G₁, b8000be44_mem_same h₁, ?_, ?_⟩
      · rw [k₁ .x19 (by decide), Nat.min_eq_left (by omega)]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₁ _ (by decide)
    · obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000be48_spec
        (b8000be44_pc_not_taken h₁ (by omega)) trivial
      have k₂ := b8000be48_keeps h₂
      refine ⟨t₂, r₁.trans r₂, b8000be48_pc h₂,
        G₁.same hpre (b8000be48_mem_same h₂) (k₂ .x2 (by decide)),
        fun a ↦ by rw [b8000be48_mem_same h₂, b8000be44_mem_same h₁], ?_, ?_⟩
      · rw [b8000be48_x19 h₂, k₁ .x23 (by decide), Nat.min_eq_right (by omega)]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [k₂ _ (by decide), k₁ _ (by decide)]
  obtain ⟨t₂, r₂, pc₂, G₂, m₂, x19₂, k₂⟩ := hcnt
  generalize hcd : min (w.getReg .x19).toNat (w.getReg .x23).toNat = cnt at x19₂
  have hcl : (qw.zip qs).length = cnt := by rw [List.length_zip, hqwl, hqsl, hcd]
  have hc64 : cnt < 2 ^ 64 := by rw [← hcd]; have := (w.getReg .x19).isLt; omega
  have hcnt : cnt ≤ (w.getReg .x19).toNat ∧ cnt ≤ (w.getReg .x23).toNat := by omega
  -- `0x8000be4c`: no query
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000be4c_spec pc₂ trivial
  have k₃ := b8000be4c_keeps h₃
  have G₃ := G₂.same hpre (b8000be4c_mem_same h₃) (k₃ .x2 (by decide))
  by_cases hz : cnt = 0
  · obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000bfc4_spec
      (b8000be4c_pc_taken h₃ (by rw [x19₂, hz]; rfl)) trivial
    have k₄ := b8000bfc4_keeps h₄
    have hnil : qw.zip qs = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨t₄, r₂.trans (r₃.trans r₄), Or.inr {
      gs := G₃.same hpre (b8000bfc4_mem_same h₄) (k₄ .x2 (by decide))
      pc := b8000bfc4_pc h₄
      value := by
        rw [b8000bfc4_x23 h₄, b8000bfc4_x24 h₄, b8000bfc4_x25 h₄, pr_ofLimbs_zero, prFold_eq, hnil]
        rfl
      keep := fun y _ ↦ by rw [b8000bfc4_mem_same h₄, b8000be4c_mem_same h₃, m₂] }⟩
  -- `0x8000be50`: the loop's constants
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000be50_spec
    (b8000be4c_pc_not_taken h₃ (by
      rw [x19₂]; intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc64] at this
      exact hz this)) (by
      rv_eval [k₃ .x2 (by decide), k₂ .x2 (by decide), hsp]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b8000be50_keeps h₄
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₃.sp
  have F₄ : DFrame t₃ t₄ fun y ↦ Within y (s.getReg .x2 - 840) 16 ∨
      Within y (s.getReg .x2 - 800) 16 :=
    (holds_dframe h₄).mono fun y ⟨k, hk, hw⟩ ↦ by
      simp only [b8000be50, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> rv_eval [sp₃] at hw <;>
        first
          | exact Or.inl (by addr_omega [hw, hb])
          | exact Or.inr (by addr_omega [hw, hb])
  have hPW (a : Word) (ha : Within a (s.getReg .x2 - 840) 16 ∨ Within a (s.getReg .x2 - 800) 16) :
      PrW s a := by
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
  obtain ⟨G₄, n₄⟩ := G₃.stepS hpre F₄ (fun a ha ↦ (hPW a ha).gls hpre) (k₄ .x2 (by decide))
  have reg (r : Reg) (h4 : t₄.getReg r = t₃.getReg r) (h3 : t₃.getReg r = t₂.getReg r)
      (h2 : t₂.getReg r = w.getReg r) : t₄.getReg r = w.getReg r := by rw [h4, h3, h2]
  have m3 (y : Word) : t₃.getMem y = w.getMem y := by rw [b8000be4c_mem_same h₃, m₂]
  have hx26 : t₃.getReg .x26 = BitVec.ofNat 64 n := by
    rw [k₃ .x26 (by decide), k₂ .x26 (by decide), hc.x26]
  have hx20 : t₃.getReg .x20 = BitVec.ofNat 64 (n + 1) := by
    rw [k₃ .x20 (by decide), k₂ .x20 (by decide), hc.x20]
  have P₄ : PrX s v w t₄ n cnt := {
    gs := G₄
    fr := (DFrame.of_same m3 (PrW s)).trans F₄ hPW
    nx := by simp only [heapNext, n₄, m3]
    m800 := by
      have := b8000be50_m_x2_240 h₄
      rw [sp₃] at this; rv_eval [] at this
      rw [this, k₃ .x19 (by decide), x19₂]
    m792 := by
      have := b8000be50_m_x2_248 h₄
      rw [sp₃] at this; rv_eval [] at this
      rw [this, k₃ .x21 (by decide), k₂ .x21 (by decide)]
    m832 := by
      have := b8000be50_m_x2_208 h₄
      rw [sp₃] at this; rv_eval [] at this
      rw [this, hx26, pr_mul24, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    m840 := by
      have := b8000be50_m_x2_200 h₄
      rw [sp₃] at this; rv_eval [] at this
      rw [this, hx20, show (1 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
    x22 := by rw [reg .x22 (k₄ .x22 (by decide)) (k₃ .x22 (by decide)) (k₂ .x22 (by decide)), hc.x22] }
  have hQ : PrQ s v w t₄ n cnt 0 (((qw.zip qs).take 0).foldl (prSum rs xs) 0) := {
    toPrX := P₄
    pc := b8000be50_pc h₄
    ilt := by omega
    x8 := b8000be50_x8 h₄
    tot := by rw [b8000be50_x23 h₄, b8000be50_x24 h₄, b8000be50_x25 h₄, pr_ofLimbs_zero]; rfl }
  obtain ⟨t₅, r₅, h₅⟩ := prOuter hBM hMK hM hSq hpre hc hcnt hcl hc64 cnt 0 t₄ (by omega) hQ
  rcases h₅ with hd | ⟨pc₅, P₅, v₅⟩
  · exact ⟨t₅, r₂.trans (r₃.trans (r₄.trans r₅)), Or.inl hd⟩
  refine ⟨t₅, r₂.trans (r₃.trans (r₄.trans r₅)), Or.inr {
    gs := P₅.gs
    pc := pc₅
    value := by rw [v₅, prFold_eq]
    keep := fun y hy ↦ P₅.keep hpre (by
      simp only [GK] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)
        | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)))) }⟩

end Rv64Verifier.Proofs.Pcs.Vso
