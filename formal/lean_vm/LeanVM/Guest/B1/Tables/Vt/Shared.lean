/-
  LeanVM.Guest.B1.Tables.Vt.Shared

  `verify_tables`' selector tables: the index MLE's factors, `1 + ζ`, and each table's shared
  nibble tables over the bus point above its height.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Pads
public import LeanVM.Guest.B1.Tables.Vt.SharedT
public import LeanVM.Guest.B1.Tables.Squares
public import LeanVM.Guest.B1.Eq.PlusOne
public import LeanVM.Guest.B1.Selectors.SharedTables

/-!
# The selector tables (G:2210-2228)

* `vt_idxc`: `idxc_tab[g^t] = 1 + g^(2^t)`, `t < 34` (statements 629-696);
* `vt_zeta1`: `zeta1` holds `1 + ζ_k` for the bus point's `μ` coordinates (`plus_one_run`, 698);
* `vt_shared`: table `t`'s run `μ - τ_t` long (`shared_len[t] = g^(μ - τ_t)`) has its nibble
  tables at `shared_eq·g^(288 t)`, `shared_g·g^(144 t)` (`vt_sh{t}`), over the coordinates above `τ_t`, their
  complements and their shares (`shared_selector_tables`, 701-768).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `idxc_tab`'s stores. -/
def vtIdxcT : List Stmt :=
  ((List.range 34).map fun t ↦ [.atom (.const (.n (669 + t))
    (word (tbGSquaresBits.getD t 0 ^^^ 1) 0)), .atom (.load (.n (669 + t)) (.n 668) t)]).flatten

theorem vtIdxc_check : tbStmtsEqb vtIdxcT ((vtAt 629).take vtIdxcT.length) = true := by
  decide +kernel

theorem vtZeta1_check : tbStmtsEqb [.dispatch (.n 9) plusOneRunNames [.n 703, .n 8] [.n 704]]
    ((vtAt 698).take 1) = true := by
  decide +kernel

/-- Table `t`'s `shared_len` value. -/
def vtShLen (t : ℕ) : ℕ := [708, 717, 730, 743, 756, 769].getD t 0

theorem vt_word_g33 : vtW33 = ofK (Parameters.addressOfIndex 33) := by
  rw [vtW33, show (8589934592 : ℕ) = 2 ^ 33 by norm_num, tb_word_two_pow (by norm_num),
    gen_pow_eq_ofK]

theorem vt_idxc {rd : Reader} {σ : Val} (h : VtH rd σ) :
    ∀ t < 34, LoadHolds rd (σ (.n 668)) t (1 + gen ^ 2 ^ t) := by
  obtain ⟨k, hs⟩ := h.sliceAt 629 vtIdxcT vtIdxc_check
  rw [vtIdxcT, tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hs
  intro t ht
  have := hs t ht
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
  obtain ⟨e1, e2⟩ := this
  rw [e1] at e2
  have e : word (tbGSquaresBits.getD t 0 ^^^ 1) 0 = 1 + gen ^ 2 ^ t := by
    rw [tb_word_eOfNat, eOfNat_xor, eOfNat_one, gen_pow_two_pow_eq ht, add_comm]
  rw [← e]
  exact e2

theorem vt_zeta1 {rd : Reader} {σ : Val} (h : VtH rd σ) {point : List E}
    (hz : TbReadsAt rd (σ (.n 8)) point) (hmu : σ (.n 9) = gen ^ point.length)
    (hml : point.length < 34) : TbReadsAt rd (σ (.n 703)) (point.map (1 + ·)) := by
  obtain ⟨j, hj, hjv, hrel⟩ := h.dispatchAt 698 _ _ _ _ vtZeta1_check
  have hj34 : j ≤ 33 := by simp [plusOneRunNames] at hj; omega
  rw [hmu, ← gen_pow_eq_ofK] at hjv
  obtain rfl : point.length = j := gen_pow_inj (by omega) (by omega) hjv
  have hm := (plus_one_run_holds _ hj34 rd _ _).mp
    (by rw [List.getD_eq_getElem _ _ hj]; exact hrel)
  simp only [List.map_cons, List.map_nil, MeaningPlusOneRun] at hm
  obtain ⟨⟨xs, hxl, hxs, hout⟩, -⟩ := hm
  obtain rfl := tbReadsAt_unique hxs hz hxl
  exact hout

theorem tbReadsAt_drop {rd : Reader} {p : E} {l : List E} (h : TbReadsAt rd p l) (a : ℕ) :
    TbReadsAt rd (p * gen ^ a) (l.drop a) := by
  rw [tbReadsAt_gen_pow_mul]
  intro k hk
  rw [List.getElem_drop]
  exact h _ _

theorem tbReadsAt_take {rd : Reader} {p : E} {l : List E} (h : TbReadsAt rd p l) (a : ℕ) :
    TbReadsAt rd p (l.take a) := fun k hk => by
  rw [List.getElem_take]; exact h _ _

theorem vt_shared_raw {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {σ : Val} (h : VtH Lm.read σ)
    {t : ℕ} (ht : t < 6) :
    σ (.n 9) = σ (.n (vtShLen t)) * σ (.n (30 + t)) ∧ (∃ d < 34, σ (.n (vtShLen t)) = gen ^ d) ∧
      coreProgram.Rel Lm.read "shared_selector_tables"
        [σ (.n 705) * gen ^ (288 * t), σ (.n 706) * gen ^ (144 * t), σ (.n 8) * σ (.n (30 + t)),
          σ (.n 703) * σ (.n (30 + t)), σ (.n 12) * σ (.n (30 + t)), σ (.n (vtShLen t))] [] := by
  have rc : ∀ {x y t1 t2 k : V}, σ k = vtW33 → (Atom.rangeCheck x y t1 t2 k).Holds Lm.read σ →
      ∃ d < 34, σ x = gen ^ d := fun hk hr =>
    vt_rc hμ Lm (K := 34) (by omega) (by norm_num) (by rw [hk]; exact vt_word_g33) hr
  interval_cases t
  · obtain ⟨a, b, c, d, -⟩ := vt_sh0 h; exact ⟨a, rc c b, d⟩
  · obtain ⟨a, b, c, d, -⟩ := vt_sh1 h; exact ⟨a, rc c b, d⟩
  · obtain ⟨a, b, c, d, -⟩ := vt_sh2 h; exact ⟨a, rc c b, d⟩
  · obtain ⟨a, b, c, d, -⟩ := vt_sh3 h; exact ⟨a, rc c b, d⟩
  · obtain ⟨a, b, c, d, -⟩ := vt_sh4 h; exact ⟨a, rc c b, d⟩
  · obtain ⟨a, b, c, d, -⟩ := vt_sh5 h; exact ⟨a, rc c b, d⟩

/-- Table `t`'s shared tables' pointers, as the shared tables' statements step them. -/
def vtEqV (t : ℕ) : ℕ := [705, 723, 736, 749, 762, 775].getD t 0
def vtGV (t : ℕ) : ℕ := [706, 725, 738, 751, 764, 777].getD t 0

theorem vt_ptrs {rd : Reader} {σ : Val} (h : VtH rd σ) : ∀ t < 6,
    σ (.n (vtEqV t)) = σ (.n 705) * gen ^ (288 * t) ∧
      σ (.n (vtGV t)) = σ (.n 706) * gen ^ (144 * t) := by
  intro t ht
  interval_cases t
  · exact (vt_sh0 h).2.2.2.2
  · exact (vt_sh1 h).2.2.2.2
  · exact (vt_sh2 h).2.2.2.2
  · exact (vt_sh3 h).2.2.2.2
  · exact (vt_sh4 h).2.2.2.2
  · exact (vt_sh5 h).2.2.2.2

/-- **Table `t`'s shared tables.** -/
theorem vt_shared {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {σ : Val} (h : VtH Lm.read σ)
    {point : List E} (hz : TbReadsAt Lm.read (σ (.n 8)) point)
    (hmu : σ (.n 9) = gen ^ point.length) (hml : point.length < 33)
    (hz1 : TbReadsAt Lm.read (σ (.n 703)) (point.map (1 + ·)))
    (hsq : TbReadsAt Lm.read (σ (.n 12)) gSquaresList)
    {t τ : ℕ} (ht : t < 6) (hτ : τ < 29) (hkbt : σ (.n (30 + t)) = gen ^ τ) :
    ∃ d, σ (.n (vtShLen t)) = gen ^ d ∧ point.length = d + τ ∧
      RunTables Lm.read (σ (.n 705) * gen ^ (288 * t)) (σ (.n 706) * gen ^ (144 * t)) d
        (point.drop τ) ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take d) := by
  obtain ⟨m1, ⟨d, hd, hdv⟩, hcall⟩ := vt_shared_raw hμ Lm h ht
  have ev := hkbt
  rw [hmu, hdv, ev, ← pow_add] at m1
  have hμd := gen_pow_inj (by omega) (by omega) m1
  refine ⟨d, hdv, hμd, ?_⟩
  have hs := shared_selector_tables_holds _ _ _ hcall
  simp only [SharedSelOut] at hs
  obtain ⟨n, hn, hnv, hrun⟩ := hs
  rw [hdv] at hnv
  obtain rfl := gen_pow_inj (by omega) (by omega) hnv
  rw [ev] at hrun
  have hsql : gSquaresList.length = 34 := by simp [gSquaresList]
  exact hrun _ _ _ (by simp; omega) (by simp; omega) (by simp [hsql]; omega)
    (tbReadsAt_drop hz τ) (tbReadsAt_drop hz1 τ) (tbReadsAt_take (tbReadsAt_drop hsq τ) d)

end
end LeanVM.Guest.B1.Tables
