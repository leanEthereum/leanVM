/-
  LeanVM.Guest.B1.Tables.VtC.SPads

  The tables' height statements (`vtPadT`, `vtPad5T`) hold on the honest valuation: each height
  `g^τ` at `kappa_base[2 + t]`, the rows from `table_rows`, `padding_weight` dispatched on `τ`, and
  its `lead`, `rest` checked when `τ` is not the floor.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SBase

/-!
# The tables' heights (G:2195-2209)

`pad_ok` (`t < 5`, floor `0`) and `pad5_ok` (`KECCAK`, floor `9`): from the template's equations,
its two reads not stores, a memory holding `g^τ` and the rows `n` with `τ = max (log2Ceil n)
floor < 33`, the bus point's first `τ` coordinates `zs` at `zeta`, and the oracle's returns of
`padding_weight` (`paddingWeight zs n`, `lead`, `rest`), every statement holds and the padding
weight is `paddingWeight zs n`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader} {w : ℕ → E} {σ : Val}

/-- The dispatch on `g^τ` to `padding_weight__L{τ}`. -/
theorem pad_dispatch {x r a b c τ n : ℕ} {zs : List E} (hτ : τ < 33) (hv : σ (.n x) = gen ^ τ)
    (hrow : σ (.n r) = eOfNat n) (hz : TbReadsAt rd (σ (.n 8)) zs) (hzl : zs.length = τ)
    (hn : n ≤ 2 ^ τ) (h6 : σ (.n a) = paddingWeight zs n) (h7 : σ (.n b) = PadLead τ n)
    (h8 : σ (.n c) = PadRest τ n) :
    VSH (coreProgram.Rel rd) rd σ
      (.dispatch (.n x) vtPadNames [.n r, .n 8] [.n a, .n b, .n c]) := by
  rw [vsh_dispatch]
  refine ⟨τ, by simp [vtPadNames]; exact hτ, by rw [hv, gen_pow_eq_ofK], ?_⟩
  simp only [vtPadNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil]
  exact padding_weight_complete_holds τ hτ rd _ _ ⟨n, zs, hn, hrow, hzl, hz, h6, h7, h8⟩

/-- **Table `t < 5`'s height**: its `τ` at `kappa_base[2 + t]` (frame variable `30 + t`). -/
theorem pad_ok {v t τ n : ℕ} {zs : List E} (hlow : LowDefB 14 rd)
    (hg : GoodL rd w σ (vtPadT v t))
    (s4 : Atom.load (.n (v + 4)) (.n 11) t ∉ vtSL)
    (hkb : σ (.n (30 + t)) = gen ^ τ)
    (hrow : LoadHolds rd (σ (.n 11)) t (eOfNat n))
    (hz : TbReadsAt rd (σ (.n 8)) zs) (hzl : zs.length = τ) (hτ : τ < 33) (hlog : log2Ceil n = τ)
    (hw5 : w (v + 5) = paddingWeight zs n) (hw6 : w (v + 6) = PadLead τ n)
    (hw7 : w (v + 7) = PadRest τ n) :
    (∀ st ∈ vtPadT v t, VSH (coreProgram.Rel rd) rd σ st) ∧
      σ (.n (v + 5)) = paddingWeight zs n := by
  simp only [vtPadT, GoodL, GoodS, fixNe, Good, and_true, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hg
  obtain ⟨g0, g1, g2, ⟨g5, g6, g7⟩, g8, -, g9, g10, g11, g12⟩ := hg
  simp only [show v < v + 1 by omega, show v + 10 < v + 12 ∧ v + 11 < v + 12 from
    ⟨by omega, by omega⟩, ↓reduceIte] at g1 g12
  have hn : n ≤ 2 ^ τ := log2Ceil_le_iff.mp (le_of_eq hlog)
  obtain ⟨hlr1, hlr2⟩ := (lead_rest_iff (by omega) hn).mpr hlog
  obtain ⟨r1, r2, r3⟩ := g1
  obtain ⟨hrc, -⟩ := rc_holds (κ := 14) hlow r1 r2 r3 hkb (by rw [g0, vtW32_gen]) (by omega)
    (by norm_num)
  obtain ⟨e4, l2⟩ := read_of (g2.resolve_left s4) hrow
  have e5 : σ (.n (v + 5)) = paddingWeight zs n := by rw [g5, hw5]
  have e6 : σ (.n (v + 6)) = PadLead τ n := by rw [g6, hw6]
  have e7 : σ (.n (v + 7)) = PadRest τ n := by rw [g7, hw7]
  have e10 : σ (.n (v + 10)) = PadRest τ n := by rw [g10, e7, g9, tb_word_zero, add_zero]
  refine ⟨?_, e5⟩
  simp only [vtPadT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, vsh_atom]
  refine ⟨g0, hrc, l2, pad_dispatch hτ hkb e4 hz hzl hn e5 e6 e7, g8, ?_, g9, g10, trivial, ?_⟩
  · show σ _ + σ _ = 0
    rw [e6, g8, tb_word_one, ← pwLead, hlr1, e_add_self]
  · show σ _ = σ _ * σ _ ∧ σ _ = 1
    refine ⟨g12, ?_⟩
    rw [g12, g11, mul_inv_cancel₀ (by rw [e10]; exact hlr2)]

/-- **The `KECCAK` table's height**, its floor `9`. -/
theorem pad5_ok {v τ n : ℕ} {zs : List E} (hlow : LowDefB 14 rd) (hv : 36 ≤ v)
    (hg : GoodL rd w σ (vtPad5T v))
    (hgb : GoodL rd w σ [.atom (.const (.n (v + 16)) (word 1 0 0)),
      .atom (.assertEq (.n (v + 6)) (.n (v + 16))), .atom (.const (.n (v + 17)) (word 0 0 0)),
      .atom (.add (.n (v + 18)) (.n (v + 7)) (.n (v + 17))),
      .atom (.hint (.inverse (.n (v + 18)) (.n (v + 19)))),
      .atom (.assertNe (.n (v + 18)) (.n (v + 19)) (.n (v + 20)))])
    (s4 : Atom.load (.n (v + 4)) (.n 11) 5 ∉ vtSL)
    (hkb : σ (.n 35) = gen ^ τ)
    (hrow : LoadHolds rd (σ (.n 11)) 5 (eOfNat n))
    (hz : TbReadsAt rd (σ (.n 8)) zs) (hzl : zs.length = τ) (hτ : τ < 33)
    (hlog : τ = max (log2Ceil n) 9)
    (hw5 : w (v + 5) = paddingWeight zs n) (hw6 : w (v + 6) = PadLead τ n)
    (hw7 : w (v + 7) = PadRest τ n) :
    (∀ st ∈ vtPad5T v, VSH (coreProgram.Rel rd) rd σ st) ∧
      σ (.n (v + 5)) = paddingWeight zs n := by
  simp only [vtPad5T, GoodL, GoodS, fixNe, Good, and_true, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hg
  obtain ⟨g0, g1, g2, ⟨g5, g6, g7⟩, g8, g9, g10, g11, g14, g15⟩ := hg
  simp only [GoodL, GoodS, fixNe, Good, and_true] at hgb
  obtain ⟨b16, -, b17, b18, b19, b20⟩ := hgb
  simp only [show v < v + 1 by omega, show v + 8 < v + 11 by omega,
    show ¬ (v + 10 < 35 ∧ v + 9 < 35) from fun h => by omega,
    show v + 18 < v + 20 ∧ v + 19 < v + 20 from ⟨by omega, by omega⟩, ↓reduceIte] at g1 g10 g11 b20
  have hn : n ≤ 2 ^ τ := by
    have := log2Ceil_le_iff.mp (show log2Ceil n ≤ τ by omega)
    exact this
  obtain ⟨r1, r2, r3⟩ := g1
  obtain ⟨hrc, -⟩ := rc_holds (κ := 14) hlow r1 r2 r3 hkb (by rw [g0, vtW32_gen]) (by omega)
    (by norm_num)
  obtain ⟨e4, l2⟩ := read_of (g2.resolve_left s4) hrow
  have e5 : σ (.n (v + 5)) = paddingWeight zs n := by rw [g5, hw5]
  have e6 : σ (.n (v + 6)) = PadLead τ n := by rw [g6, hw6]
  have e7 : σ (.n (v + 7)) = PadRest τ n := by rw [g7, hw7]
  have w512 : word 512 0 0 = gen ^ 9 := by
    rw [show (512 : ℕ) = 2 ^ 9 by norm_num, tb_word_two_pow (by norm_num)]
  have e9 : σ (.n (v + 9)) = gen ^ 9 := by rw [g9, w512]
  have e10 : σ (.n (v + 10)) = gen ^ (τ - 9) := by rw [g10, hkb, e9, gen_pow_div (by omega)]
  obtain ⟨q1, q2, q3⟩ := g11
  obtain ⟨hrc10, -⟩ := rc_holds (κ := 14) hlow q1 q2 q3 e10 (by rw [g8, vtW32_gen]) (by omega)
    (by norm_num)
  refine ⟨?_, e5⟩
  simp only [vtPad5T, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, vsh_atom, vsh_ite]
  refine ⟨g0, hrc, l2, pad_dispatch hτ hkb e4 hz hzl hn e5 e6 e7, g8, g9,
    mulDiv_holds g10 (by rw [e9]; exact gen_pow_ne_zero _), hrc10, g14, g15,
    by rw [g15, hkb, g14, w512]; exact tb_isInK_add (isInK_gpow' _) (isInK_gpow' _), trivial,
    fun h0 => ?_⟩
  -- not at the floor: τ = log2Ceil n
  have h9 : τ ≠ 9 := fun h => h0 (by rw [g15, hkb, g14, w512, h, e_add_self])
  have hlog' : log2Ceil n = τ := by omega
  obtain ⟨hlr1, hlr2⟩ := (lead_rest_iff (by omega) hn).mpr hlog'
  have e18 : σ (.n (v + 18)) = PadRest τ n := by rw [b18, e7, b17, tb_word_zero, add_zero]
  refine ⟨b16, ?_, b17, b18, trivial, ?_⟩
  · show σ _ + σ _ = 0
    rw [e6, b16, tb_word_one, ← pwLead, hlr1, e_add_self]
  · show σ _ = σ _ * σ _ ∧ σ _ = 1
    refine ⟨b20, ?_⟩
    rw [b20, b19, mul_inv_cancel₀ (by rw [e18]; exact hlr2)]

end
end LeanVM.Guest.B1.Tables
