import Rv64Verifier.Proofs.Bus.TsWeights

/-!
# `table_sumcheck`: the loop over the point

From `0x800082b4` (`OuterAt`), one variable at a time: `equality_point[variable]` traps past its
end, the heights loop (`innerLoop`) updates the weights, `0x80008298` moves the point's cursor.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
  Rv64Verifier.MultilinearContracts Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The loop over the point -/

/-- What the point loop writes: the heights loop's and the point's cursor at `sp + 168`. -/
def OW (s : MachineState) (W : Word) (n : ℕ) (a : Word) : Prop :=
  IW s W n a ∨ Within a (s.getReg .x2 - 328) 8

/-- What the point loop reads, in the state `u₀` it starts from. -/
structure OuterCtx (s u₀ : MachineState) (P W EP hp : Word) (L n hlen eqlen : ℕ) (pt : List E)
    (hs : List ℕ) (eqs : List E) : Prop where
  ro : RodataOk u₀
  wb : n = 0 ∨ (0x20000000 ≤ W.toNat ∧ W.toNat + 24 * n ≤ 0x78000000)
  w3 : W.toNat % 8 = 0
  hr : ValidMemRange hp hlen
  hW : Apart hp (8 * hlen) W (24 * n)
  hS : Apart hp (8 * hlen) (s.getReg .x2 - 2128) 2128
  hv : ∀ i < hlen, (u₀.getMem (hp + BitVec.ofNat 64 (8 * i))).toNat = hs.getD i 0
  pr : ValidMemRange P (3 * L)
  pW : Apart P (24 * L) W (24 * n)
  pS : Apart P (24 * L) (s.getReg .x2 - 2128) 2128
  pv : ∀ v < L, eAt u₀ (P + BitVec.ofNat 64 (24 * v)) = pt.getD v 0
  er : ValidMemRange EP (3 * eqlen)
  eW : Apart EP (24 * eqlen) W (24 * n)
  eS : Apart EP (24 * eqlen) (s.getReg .x2 - 2128) 2128
  ev : ∀ v < eqlen, eAt u₀ (EP + BitVec.ofNat 64 (24 * v)) = eqs.getD v 0
  eqSlot : u₀.getMem (s.getReg .x2) = BitVec.ofNat 64 eqlen
  epSlot : u₀.getMem (s.getReg .x2 - 360) = EP
  hpSlot : u₀.getMem (s.getReg .x2 - 352) = hp
  endSlot : u₀.getMem (s.getReg .x2 - 344) = P + BitVec.ofNat 64 (24 * L)
  hlenSlot : u₀.getMem (s.getReg .x2 - 336) = BitVec.ofNat 64 hlen
  countSlot : u₀.getMem (s.getReg .x2 - 376) = BitVec.ofNat 64 (n + 1)
  wSlot : u₀.getMem (s.getReg .x2 - 368) = W
  ptLen : pt.length = L
  hsLen : hs.length = hlen
  bounds : L < 2 ^ 32 ∧ n < 2 ^ 32 ∧ hlen < 2 ^ 32 ∧ eqlen < 2 ^ 32

/-- The point loop's head, `0x800082b4`, `v` variables done. -/
structure OuterAt (s u₀ u : MachineState) (P W hp : Word) (n hlen eqlen m v : ℕ) (pt : List E)
    (hs : List ℕ) (eqs : List E) : Prop where
  pc : u.pc = 0x800082b4
  x2 : u.getReg .x2 = s.getReg .x2 - 496
  x19 : u.getReg .x19 = BitVec.ofNat 64 v
  x26 : u.getReg .x26 = BitVec.ofNat 64 hlen
  x24 : 1 ≤ hlen → u.getReg .x24 = hp + BitVec.ofNat 64 (8 * (m + 1))
  veq : v ≤ eqlen
  cursor : u.getMem (s.getReg .x2 - 328) = P + BitVec.ofNat 64 (24 * v)
  frame : DFrame u₀ u (OW s W n)
  elems : ∀ j < n, eAt u (W + BitVec.ofNat 64 (24 * j)) = (twPre n hs eqs pt v).getD j 0

/-- One variable's weights, from the heights loop's. -/
theorem twPre_getD_succ (n : ℕ) (hs : List ℕ) (eqs pt : List E) (v j : ℕ) (hv : v < pt.length)
    (hl : hs.length ≤ n) :
    (twPre n hs eqs pt (v + 1)).getD j 0 =
      if j < hs.length then (twPre n hs eqs pt v).getD j 0 *
        factorOf v (hs.getD j 0) (pt.getD v 0) (eqs.getD v 0)
      else (twPre n hs eqs pt v).getD j 0 := by
  rw [twPre_succ n hs eqs pt v hv]
  have := modifyFold_getD (fun h w ↦ w * if h > v then 1 + eqs.getD v 0 + pt[v] else pt[v]) hs
    (twPre n hs eqs pt v) (by rw [twPre_length]; exact hl) j
  rw [this, show pt.getD v 0 = pt[v] by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]; rfl]
  rfl

theorem twPre_succ_nil (n : ℕ) (eqs pt : List E) (v : ℕ) (hv : v < pt.length) :
    twPre n [] eqs pt (v + 1) = twPre n [] eqs pt v := by
  rw [twPre_succ n [] eqs pt v hv]
  rfl

theorem mul24 (v : ℕ) :
    BitVec.ofNat 64 v * 16 + BitVec.ofNat 64 v * 8 = BitVec.ofNat 64 (24 * v) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Sym.wordToNatLit]
  omega

/-- The point loop: it traps where `equality_point` or `weights` is too short, or reaches
`0x80008384` with the weights of every variable. -/
theorem outerLoop (hMul : MulSpec) {s u₀ : MachineState} {P W EP hp : Word}
    {L n hlen eqlen m : ℕ} {pt eqs : List E} {hs : List ℕ} (hpre : TableSumcheckPre s)
    (hc : OuterCtx s u₀ P W EP hp L n hlen eqlen pt hs eqs) (hm : m = min n (hlen - 1)) :
    ∀ k v u, L - v = k → v < L → OuterAt s u₀ u P W hp n hlen eqlen m v pt hs eqs →
      ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80008384 ∧
        t.getReg .x2 = s.getReg .x2 - 496 ∧ t.getReg .x26 = BitVec.ofNat 64 hlen ∧
        DFrame u₀ t (OW s W n) ∧
        ∀ j < n, eAt t (W + BitVec.ofNat 64 (24 * j)) = (twPre n hs eqs pt L).getD j 0) ∨
        Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hrs := hpre.stack.rodata
  simp only [stack_eq] at hrs
  obtain ⟨hL32, hn32, hl32, he32⟩ := hc.bounds
  have hA := hpre.args.region
  intro k
  induction k with
  | zero => intro v u hk hv; omega
  | succ k ih =>
    intro v u hk hv h
    -- what the loop has not written is `u₀`'s
    have keep (a : Word) (ha : ∀ i < 8, ¬ OW s W n (a + BitVec.ofNat 64 i)) :
        u.getMem a = u₀.getMem a := h.frame a ha
    -- `0x800082b4`: `equality_point[variable]`
    obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800082b4_spec h.pc (by
      rv_eval [h.x2]
      rcases hA with h0 | h0
      · omega
      · exact Region.valid h0 (by addr_omega [h0]) (by addr_omega [h0]) (by addr_omega [h0]))
    have hm₁ := b800082b4_mem_same h₁
    have k₁ := b800082b4_keeps h₁
    have hS : u.getMem (u.getReg .x2 + 496) = BitVec.ofNat 64 eqlen := by
      rw [h.x2, show s.getReg .x2 - 496 + 496 = s.getReg .x2 by addr_omega [hb1, hb2], ← hc.eqSlot]
      exact keep _ fun i hi hw ↦ by
        rcases hw with (hw | hw | hw) | hw <;>
          addr_omega [hw, hi, hb1, hb2, hc.wb]
    by_cases hve : v = eqlen
    · exact ⟨u₁, hr₁, Or.inr (trap (b800082b4_pc_taken h₁ (by rw [hS, h.x19, hve])))⟩
    have hve' : v < eqlen := lt_of_le_of_ne h.veq hve
    have hpc₁ := b800082b4_pc_not_taken h₁ (by rw [hS, h.x19]; addr_omega [hve, hL32, he32, hv])
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800082bc_spec hpc₁ trivial
    have hm₂ := b800082bc_mem_same h₂
    have k₂ := b800082bc_keeps h₂
    have hx26₂ : u₁.getReg .x26 = BitVec.ofNat 64 hlen := (k₁ .x26 (by decide)).trans h.x26
    have hx2₂ : u₂.getReg .x2 = s.getReg .x2 - 496 := by
      rw [k₂ .x2 (by decide), k₁ .x2 (by decide), h.x2]
    have hmu (a : Word) : u₂.getMem a = u.getMem a := (hm₂ a).trans (hm₁ a)
    have hpb := ValidMemRange.bounds hc.pr (by omega)
    have heb := ValidMemRange.bounds hc.er (by omega)
    have hWb := hc.wb
    have hpS := hc.pS
    have hpW := hc.pW
    have heS := hc.eS
    have heW := hc.eW
    -- the challenge and `equality_point[variable]` are the entry's
    have hcv : eAt u₂ (P + BitVec.ofNat 64 (24 * v)) = pt.getD v 0 := by
      rw [eAt_of_same hmu, h.frame.eAt fun i hi hw ↦ by
        rcases hw with (hw | hw | hw) | hw <;> addr_omega [hw, hi, hpb, hv, hpS, hpW, hb1]]
      exact hc.pv v hv
    have hev : eAt u₂ (EP + BitVec.ofNat 64 (24 * v)) = eqs.getD v 0 := by
      rw [eAt_of_same hmu, h.frame.eAt fun i hi hw ↦ by
        rcases hw with (hw | hw | hw) | hw <;> addr_omega [hw, hi, heb, hve', heS, heW, hb1]]
      exact hc.ev v hve'
    -- the heights loop, or none
    obtain ⟨t₄, hr₄, ⟨hpc₄, hx2₄, hx19₄, hx24₄, hfr₄, hel₄⟩ | hd⟩ : ∃ t₄, Reaches Image.code u₂ t₄ ∧
        ((t₄.pc = 0x80008298 ∧ t₄.getReg .x2 = s.getReg .x2 - 496 ∧
          t₄.getReg .x19 = BitVec.ofNat 64 v ∧
          (1 ≤ hlen → t₄.getReg .x24 = hp + BitVec.ofNat 64 (8 * (m + 1))) ∧
          DFrame u t₄ (IW s W n) ∧
          ∀ j < n, eAt t₄ (W + BitVec.ofNat 64 (24 * j)) = (twPre n hs eqs pt (v + 1)).getD j 0) ∨
          Dead Image.code t₄) := by
      by_cases hl0 : hlen = 0
      · have hnil : hs = [] := List.eq_nil_of_length_eq_zero (hc.hsLen.trans hl0)
        refine ⟨u₂, Reaches.refl _, Or.inl ⟨b800082bc_pc_taken h₂ (by rw [hx26₂, hl0]; rfl), hx2₂,
          by rw [k₂ .x19 (by decide), k₁ .x19 (by decide), h.x19], fun h1 ↦ absurd h1 (by omega),
          DFrame.of_same hmu _, fun j hj ↦ ?_⟩⟩
        rw [eAt_of_same hmu, h.elems j hj, hnil, twPre_succ_nil _ _ _ _ (by rw [hc.ptLen]; exact hv)]
      have hl1 : 1 ≤ hlen := by omega
      have slot (a : Word) (h1 : (s.getReg .x2).toNat - 496 ≤ a.toNat)
          (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 328) : u₂.getMem a = u₀.getMem a := by
        rw [hmu]; exact keep a fun i hi hw ↦ by
          rcases hw with (hw | hw | hw) | hw <;> addr_omega [hw, hi, h1, h2, hb1, hWb]
      have e136 : u₂.getMem (s.getReg .x2 - 360) = EP :=
        (slot _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans hc.epSlot
      have e168 : u₂.getMem (s.getReg .x2 - 328) = P + BitVec.ofNat 64 (24 * v) := by
        rw [hmu]; exact h.cursor
      have hPv : ValidMemRange (P + BitVec.ofNat 64 (24 * v)) 3 :=
        ValidMemRange.sub hc.pr (by addr_omega [hpb, hv]) (by addr_omega [hpb, hv])
          (by addr_omega [hpb, hv])
      have hEv : ValidMemRange (EP + BitVec.ofNat 64 (24 * v)) 3 :=
        ValidMemRange.sub hc.er (by addr_omega [heb, hve']) (by addr_omega [heb, hve'])
          (by addr_omega [heb, hve'])
      have hx19₂ : u₂.getReg .x19 = BitVec.ofNat 64 v := by
        rw [k₂ .x19 (by decide), k₁ .x19 (by decide), h.x19]
      obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800082c0_spec
        (b800082bc_pc_not_taken h₂ (by rw [hx26₂]; addr_omega [hl1, hl32])) (by
          rv_eval [hx2₂, e136, e168, hx19₂, mul24]
          and_intros <;> first
            | valid_access hval [hb1]
            | valid_access hPv [hpb, hv]
            | valid_access hEv [heb, hve'])
      have hm₃ := b800082c0_mem_same h₃
      have k₃ := b800082c0_keeps h₃
      have hmu₃ (a : Word) : u₃.getMem a = u.getMem a := (hm₃ a).trans (hmu a)
      have hc₃ : Model.limbs (eAt u₂ (P + BitVec.ofNat 64 (24 * v))) = _ := limbs_eAt _ _
      have he₃ : Model.limbs (eAt u₂ (EP + BitVec.ofNat 64 (24 * v))) = _ := limbs_eAt _ _
      have hfr₃ : DFrame u₀ u₃ (OW s W n) :=
        h.frame.trans (DFrame.of_same hmu₃ fun _ ↦ False) fun _ h ↦ h.elim
      obtain ⟨t₄, hr₄, ht₄⟩ := innerLoop hMul (uv := u₃) (ws := twPre n hs eqs pt v) (v := v)
        (n := n) (hlen := hlen) (m := m) (hs := hs) (c := eAt u₂ (P + BitVec.ofNat 64 (24 * v)))
        (e := eAt u₂ (EP + BitVec.ofNat 64 (24 * v))) hpre
        (hc.ro.dframe hfr₃ fun a ha hw ↦ by
          rcases hw with (hw | hw | hw) | hw <;> addr_omega [ha, hw, hrs, hb1, hWb])
        hWb hc.w3 hc.hr hc.hW hc.hS (fun i hi ↦ by
          rw [hfr₃ _ fun j hj hw ↦ by
            have hhb := ValidMemRange.bounds hc.hr (by omega)
            have hHW' := hc.hW
            have hHS' := hc.hS
            rcases hw with (hw | hw | hw) | hw <;>
              addr_omega [hw, hj, hhb, hi, hb1, hWb, hHW', hHS']]
          exact hc.hv i hi) hm hl1 (by omega) hn32
        (m + 1) 0 u₃ (by omega) (Nat.zero_le _) {
          pc := b800082c0_pc h₃
          x2 := by rw [k₃ .x2 (by decide), hx2₂]
          x9 := by
            rw [b800082c0_x9 h₃, hx2₂, show s.getReg .x2 - 496 + 128 = s.getReg .x2 - 368 by
              addr_omega [hb1], slot _ (by addr_omega [hb1]) (by addr_omega [hb1]), hc.wSlot]
            simp
          x18 := by
            rw [b800082c0_x18 h₃, hx2₂, show s.getReg .x2 - 496 + 144 = s.getReg .x2 - 352 by
              addr_omega [hb1], slot _ (by addr_omega [hb1]) (by addr_omega [hb1]), hc.hpSlot]
            simp
          x19 := by rw [k₃ .x19 (by decide), hx19₂]
          x26 := by
            rw [b800082c0_x26 h₃, hx2₂, show s.getReg .x2 - 496 + 120 = s.getReg .x2 - 376 by
              addr_omega [hb1], slot _ (by addr_omega [hb1]) (by addr_omega [hb1]), hc.countSlot]
            rfl
          x8 := by
            rw [b800082c0_x8 h₃, hc₃, hx2₂, show s.getReg .x2 - 496 + 168 = s.getReg .x2 - 328 by
              addr_omega [hb1], e168]
          x25 := by
            rw [b800082c0_x25 h₃, hc₃, hx2₂, show s.getReg .x2 - 496 + 168 = s.getReg .x2 - 328 by
              addr_omega [hb1], e168]
          x20 := by
            rw [b800082c0_x20 h₃, hc₃, hx2₂, show s.getReg .x2 - 496 + 168 = s.getReg .x2 - 328 by
              addr_omega [hb1], e168]
          x21 := by
            rw [b800082c0_x21 h₃, hc₃, he₃, hx2₂, hx19₂, mul24,
              show s.getReg .x2 - 496 + 168 = s.getReg .x2 - 328 by addr_omega [hb1],
              show s.getReg .x2 - 496 + 136 = s.getReg .x2 - 360 by addr_omega [hb1], e168, e136]
          x22 := by
            rw [b800082c0_x22 h₃, he₃, hx2₂, hx19₂, mul24,
              show s.getReg .x2 - 496 + 136 = s.getReg .x2 - 360 by addr_omega [hb1], e136]
          x23 := by
            rw [b800082c0_x23 h₃, he₃, hx2₂, hx19₂, mul24,
              show s.getReg .x2 - 496 + 136 = s.getReg .x2 - 360 by addr_omega [hb1], e136]
          x24 := by rw [k₃ .x24 (by decide), k₂ .x24 (by decide), k₁ .x24 (by decide), h.x24 hl1]
          frame := DFrame.refl _ _
          elems := fun j hj ↦ by
            rw [eAt_of_same hmu₃, h.elems j hj]
            simp }
      refine ⟨t₄, hr₃.trans hr₄, ?_⟩
      rcases ht₄ with ⟨hpc₄, hln, hx2₄, hx19₄, hx24₄, hfr₄, hel₄⟩ | hd
      · refine Or.inl ⟨hpc₄, hx2₄, hx19₄, fun _ ↦ hx24₄,
          (DFrame.of_same hmu₃ _).trans hfr₄ fun _ h ↦ h, fun j hj ↦ ?_⟩
        rw [hel₄ j hj, hcv, hev, twPre_getD_succ n hs eqs pt v j (by rw [hc.ptLen]; exact hv)
          (by rw [hc.hsLen]; exact hln), hc.hsLen]
      · exact Or.inr hd
    swap
    · exact ⟨t₄, hr₁.trans (hr₂.trans hr₄), Or.inr hd⟩
    -- `0x80008298`: the next variable
    obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80008298_spec hpc₄ (by
      rv_eval [hx2₄]; and_intros <;> valid_access hval [hb1])
    have k₅ := b80008298_keeps h₅
    have hf₅ := DFrame.of_memFrame (b80008298_frame h₅ (by rw [hx2₄]; addr_omega [hb1]))
    rw [hx2₄, show s.getReg .x2 - 496 + 168 = s.getReg .x2 - 328 by addr_omega [hb1]] at hf₅
    have hfr : DFrame u₀ t₅ (OW s W n) :=
      ((h.frame.trans hfr₄ fun a ha ↦ Or.inl ha).trans hf₅) fun a ha ↦ Or.inr ha
    have hold (a : Word) (h1 : (s.getReg .x2).toNat - 496 ≤ a.toNat)
        (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 328) : t₄.getMem a = u₀.getMem a := by
      rw [hfr₄ a fun i hi hw ↦ by rcases hw with hw | hw | hw <;>
        addr_omega [hw, hi, h1, h2, hb1, hWb]]
      exact keep a fun i hi hw ↦ by
        rcases hw with (hw | hw | hw) | hw <;> addr_omega [hw, hi, h1, h2, hb1, hWb]
    have hcur₄ : t₄.getMem (s.getReg .x2 - 328) = P + BitVec.ofNat 64 (24 * v) := by
      rw [hfr₄ _ fun i hi hw ↦ by rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb1, hWb]]
      exact h.cursor
    have hcur₅ : t₅.getMem (s.getReg .x2 - 328) = P + BitVec.ofNat 64 (24 * (v + 1)) := by
      have := b80008298_m_x2_168 h₅
      rw [hx2₄, show s.getReg .x2 - 496 + 168 = s.getReg .x2 - 328 by addr_omega [hb1], hcur₄]
        at this
      rw [this]; addr_omega [hpb, hv]
    have hend : t₄.getMem (t₄.getReg .x2 + 152) = P + BitVec.ofNat 64 (24 * L) := by
      rw [hx2₄, show s.getReg .x2 - 496 + 152 = s.getReg .x2 - 344 by addr_omega [hb1],
        hold _ (by addr_omega [hb1]) (by addr_omega [hb1]), hc.endSlot]
    have hcur168 : t₄.getMem (t₄.getReg .x2 + 168) = P + BitVec.ofNat 64 (24 * v) := by
      rw [hx2₄, show s.getReg .x2 - 496 + 168 = s.getReg .x2 - 328 by addr_omega [hb1], hcur₄]
    have hx26₅ : t₅.getReg .x26 = BitVec.ofNat 64 hlen := by
      rw [b80008298_x26 h₅, hx2₄, show s.getReg .x2 - 496 + 160 = s.getReg .x2 - 336 by
        addr_omega [hb1], hold _ (by addr_omega [hb1]) (by addr_omega [hb1]), hc.hlenSlot]
    have hreach := hr₁.trans (hr₂.trans (hr₄.trans hr₅))
    by_cases hlast : v + 1 = L
    · refine ⟨t₅, hreach, Or.inl ⟨b80008298_pc_taken h₅ (by
        rw [hend, hcur168]; addr_omega [hpb, hlast]), by rw [k₅ .x2 (by decide), hx2₄], hx26₅,
        hfr, fun j hj ↦ ?_⟩⟩
      rw [hf₅.eAt fun i hi hw ↦ by addr_omega [hw, hi, hb1, hWb, hj], hel₄ j hj, hlast]
    · obtain ⟨t, hrt, ht⟩ := ih (v + 1) t₅ (by omega) (by omega) {
        pc := b80008298_pc_not_taken h₅ (by rw [hend, hcur168]; addr_omega [hpb, hlast, hv])
        x2 := by rw [k₅ .x2 (by decide), hx2₄]
        x19 := by rw [b80008298_x19 h₅, hx19₄]; addr_omega [hv, hL32]
        x26 := hx26₅
        x24 := fun h1 ↦ by rw [k₅ .x24 (by decide), hx24₄ h1]
        veq := by omega
        cursor := hcur₅
        frame := hfr
        elems := fun j hj ↦ by
          rw [hf₅.eAt fun i hi hw ↦ by addr_omega [hw, hi, hb1, hWb, hj], hel₄ j hj] }
      exact ⟨t, hreach.trans hrt, ht⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
