/-
  LeanVM.Guest.B1.VerifySub.Known

  The control-flow obligation at `verify_sub`'s terminal call: once the body has run up to it,
  every committed column's log in `col_kappas` is below `29`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Sound
public import LeanVM.Guest.B1.Tables.Kappas
public import LeanVM.Guest.B1.Main.Basic

/-!
# `col_kappas` is in range at `check_opening_terminal` (G:2263)

`check_opening_terminal` dispatches on each committed column's `col_kappas` entry, which the
checker must know to lie among its `N_COLUMN_LOGS = 29` arms. `vs_known`: when `verify_sub`'s
first `1927` statements hold (everything before the terminal call) on a memory image, over the
exponent tables, the entries are `g^e`, `e < 29`.

The entries are `certify_placement`'s (`soundPlace`), and `hypKappa` bounds them once the stack's
log is at most `28`, which the stack-size range check before the dispatch gives
(G:2240-2244). `certify_placement` needs the tables' log-heights below `29`, which only
`verify_tables`' soundness gives (`dims_g[1..7]` are hinted), so the lemma rests on `SoundGkr`
and `SoundTables` (groups 5a's).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem vsPre_length : vsPre.length = 2136 := by decide +kernel

theorem body_take_1927 : (Fn.body Data.core15).take 1927 = vsPre.take 1927 := by
  rw [core15_body, List.take_append_of_le_length (by rw [vsPre_length]; omega)]

/-- **`col_kappas` is in range at the terminal call** (the checker's `VsKnown`). -/
theorem vs_known {bytecode : List K}
    {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop} {κ : ℕ} (hκ : κ ≤ 32)
    (hκ6 : 6 ≤ κ) (Lm : MemImage κ) (hgkr : SoundGkr Lm.read)
    (htab : SoundTables bytecode TCtx Lm.read) (σ : Val)
    (ht : ExpTables Lm.read (σ (.n 4)) (σ (.n 5)))
    (h : Stmt.HoldsList (coreProgram.Rel Lm.read) Lm.read σ ((Fn.body Data.core15).take 1927) True
      (fun _ ↦ True)) :
    ∀ c < 92, ∃ e < 29, LoadHolds Lm.read (σ (.n 1631)) c (ofK (gpow e)) := by
  have hv : VsHoldsTo 1927 Lm.read σ := by rw [body_take_1927] at h; exact h
  -- the public input, the memory's log, the kappas
  obtain ⟨-, pi, -, hpi, -⟩ := vs_seed hv (by decide)
  obtain ⟨m, hm1, hm2, -, h144⟩ := vs_logMem hκ hκ6 Lm hv (by decide) ht
  obtain ⟨hdims, hbase, hbk⟩ := vs_kappas hv (by decide)
  -- the bus challenges, as stored
  have hst : ∀ k < 4, LoadHolds Lm.read (σ (.n 451)) k (σ (.n (452 + 14 * k + 13))) := by
    have hs : ∀ k < 4, (decide (551 + 15 * k + 1 ≤ 1927) && stmtsEqb
        [.atom (.load (.n (452 + 14 * k + 13)) (.n 451) k)] ((vsPre.drop (551 + 15 * k)).take 1)) =
          true := by decide +kernel
    exact fun k hk => hv.atom' _ _ (hs k hk)
  set alphas := [σ (.n 465), σ (.n 479), σ (.n 493), σ (.n 507)]
  have har : ReadsAt Lm.read (σ (.n 451)) alphas := fun k hk => by
    simp only [alphas, List.length_cons, List.length_nil] at hk
    match k, hk with
    | 0, _ => exact hst 0 (by omega)
    | 1, _ => exact hst 1 (by omega)
    | 2, _ => exact hst 2 (by omega)
    | 3, _ => exact hst 3 (by omega)
  have hfpw := vs_fpw hv (by decide) (alphas := alphas) rfl har
  -- GKR
  have cG := hv.call' 806 "verify_bus_gkr" [.n 690, .n 691, .n 700, .n 417, .n 418]
    [.n 701, .n 702, .n 703, .n 704, .n 705, .n 706] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cG
  obtain ⟨-, depth, xsG, gr, cvG, -, h417, hdepth, -, -, hptl, -, hzeta, hretsG⟩ :=
    hgkr _ _ _ _ _ _ cG
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hretsG
  obtain ⟨-, -, -, hgr⟩ := hretsG
  -- the tables
  have cT := hv.call' 810 "verify_tables" [.n 707, .n 708, .n 703, .n 0, .n 1, .n 418, .n 417,
    .n 143, .n 30, .n 163, .n 5, .n 508, .n 698, .n 7, .n 8, .n 709, .n 704, .n 705, .n 706]
    [.n 710, .n 711, .n 712, .n 713, .n 714, .n 715] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cT
  rw [h144] at hdims hbk hbase
  have hpre : TablesPre Lm.read (σ (.n 4)) pi m alphas gr.2.1 gr.2.2
      [σ (.n 707), σ (.n 708), σ (.n 703), σ (.n 0), σ (.n 1), σ (.n 418), σ (.n 417),
        σ (.n 143), σ (.n 30), σ (.n 163), σ (.n 5), σ (.n 508), σ (.n 698), σ (.n 7), σ (.n 8),
        σ (.n 709), σ (.n 704), σ (.n 705), σ (.n 706)] :=
    ⟨hpi, hzeta, by rw [h417, hptl], by omega, hm1, hm2,
      ⟨dimsWords σ, by simp [dimsWords], hdims, hbk⟩, ht, rfl, hfpw, hgr.symm⟩
  obtain ⟨-, -, -, rowsN, -, -, -, hrl, -, hdimsR, hlogs, -⟩ := htab _ _ _ _ _ _ _ _ hpre cT
  have hdw : dimsWords σ = (rowsN.map log2Ceil).map (gen ^ ·) := by
    have := readsAt_unique (by simp [dimsWords, hrl]) hdims hdimsR
    rw [List.cons.injEq] at this
    rw [this.2, List.map_map]
    rfl
  have hhs : ∀ h ∈ rowsN.map log2Ceil, h < 29 := by
    intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx; exact hlogs n hn
  have hhl : (rowsN.map log2Ceil).length = 6 := by simp [hrl]
  -- the placement
  have cP := hv.call' 1913 "certify_placement" [.n 155, .n 5] [.n 1629, .n 1630, .n 1631]
    (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cP
  rw [hdw] at hbase
  obtain ⟨off, kap, hretsP, hpctx⟩ := soundPlace hκ Lm _ _ _ m _ _ ht hm2 hhl hhs hbase cP
  simp only [List.cons.injEq] at hretsP
  obtain ⟨r1629, -, r1631, -⟩ := hretsP
  -- the stack's log, from the range check before the dispatch
  have cL := hv.call' 1914 "log2_ceil_in_the_exponent__L15_L34" [.n 1629, .n 4, .n 5] [.n 1632]
    (by decide +kernel)
  obtain ⟨N, hN, hg, hl34, -, -, hr⟩ := (log2_ceil_in_the_exponent_L15_L34_iff hκ hκ6 Lm ht _).mp cL
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hr
  have hs := hv.slice' 1915 [.atom (.const (.n 1633) (word 8198552432976855044 0 0)),
    .atom (.mul (.n 1634) (.n 1632) (.n 1633)), .atom (.const (.n 1635) (word 64 0 0)),
    .atom (.rangeCheck (.n 1634) (.n 1636) (.n 1637) (.n 1638) (.n 1635))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
  obtain ⟨e1633, e1634, e1635, ⟨q1, q2, q3⟩⟩ := hs
  obtain ⟨e, he, hxe⟩ := rc_gen hκ hκ6 Lm (K := 7) (by decide) (by decide)
    (by rw [e1635]; exact word_two_pow (a := 6) (by decide)) q1 q2 q3
  have hμ : gen ^ max 15 (log2Ceil N) = gen ^ (e + 22) := by
    rw [← hr, pow_add, ← hxe, e1634, e1633, mul_assoc, minShiftInv, mul_one]
  have hμe := gen_pow_inj (by omega) (by omega) hμ
  have hST := stackTotal_lt m (rowsN.map log2Ceil) hm2 hhs
  rw [r1629] at hg
  have eST := gen_pow_inj (by omega) (by omega) hg
  -- the columns' logs
  have hkb := hypKappa Lm.read _ _ _ hpctx (by rw [eST]; omega)
  intro c hc
  obtain ⟨k, hk, hl⟩ := hkb c hc
  exact ⟨k, hk, by rw [r1631, ← gen_pow_eq_ofK]; exact hl⟩

/-- The checker's obligation at `verify_sub`'s terminal call: on every memory image, over the
exponent tables at `verify_sub`'s arguments `4`, `5`, the first `1927` statements put
`col_kappas`' entries among the `29` arms. -/
def VsKnown : Prop :=
  ∀ rd : Reader, Main.MemOk rd → ∀ σ : Val, ExpTables rd (σ (.n 4)) (σ (.n 5)) →
    Stmt.HoldsList (coreProgram.Rel rd) rd σ ((Fn.body Data.core15).take 1927) True (fun _ ↦ True) →
      ∀ c < 92, ∃ e < 29, LoadHolds rd (σ (.n 1631)) c (ofK (gpow e))

/-- **`VsKnown`**, from `verify_sub`'s first two callees' soundness. -/
theorem vsKnown {bytecode : List K}
    {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    (hgkr : ∀ rd, Main.MemOk rd → SoundGkr rd)
    (htab : ∀ rd, Main.MemOk rd → SoundTables bytecode TCtx rd) : VsKnown := by
  intro rd hm σ ht h
  obtain ⟨κ, h16, h32, L, rfl⟩ := hm
  exact vs_known h32 (by omega) L (hgkr _ ⟨κ, h16, h32, L, rfl⟩) (htab _ ⟨κ, h16, h32, L, rfl⟩) σ ht h

end
end LeanVM.Guest.B1.VerifySub
