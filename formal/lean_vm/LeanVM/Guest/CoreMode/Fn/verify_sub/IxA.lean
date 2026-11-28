/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.IxA

  `verify_sub`'s residuals over its dispatches' blocks (`ixFam`), sound at the honest instances of b2c's aligned tree:
  from its shape checks, `g_w = g^w`, `19 ≤ w ≤ 24`, at least `g_log_mem` (`log(g_w / g_log_mem) < 24`), and
  `g_n = g^n` at least every table's height word (`log(g_n / kb[2 + t]) < 24`).
-/

module

public import LeanVM.Guest.EndExecExpCA
public import LeanVM.Guest.CoreMode.Fn.verify_sub.Ix
public import LeanVM.Guest.CoreMode.Fn.verify_sub.ChalA
public import LeanVM.Guest.B1.VerifySub.PhLinkShape
public import LeanVM.Guest.B1.VerifySub.Reads
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

namespace LeanVM.Guest.CoreMode.Own.verify_sub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Guest.CoreMode
open LeanVM.Protocol.Verifier (gen)

public section

/-- **The dispatches' facts** at an instance: `g_w = g^w`, `19 ≤ w ≤ 24`, `[108]·[460]·g = g_w`,
`795 = g^-19`, the selectors `796`, `2893` (`g_w·g^-19`) `g^(w - 19)`; `g_log_mem = g^L`, `L ≤ w`;
`kb[2]·[412] = g^n`, `n ≤ 48`, each `kb[2 + t] = g^h`, `h ≤ n`; `gmv = g^m`, `m ≤ 30`, `488 = g^-16`. -/
def IxFacts (σ : Val) : Prop :=
  ∃ w L n, 19 ≤ w ∧ w ≤ 24 ∧ σ (.n 409) = gen ^ w ∧ σ (.n 108) * σ (.n 460) * gen = σ (.n 409) ∧
    σ (.n 795) = word 10248187242686185485 0 ∧ σ (.n 796) = gen ^ (w - 19) ∧ σ (.n 2893) = gen ^ (w - 19) ∧
    L ≤ w ∧ σ (.n 101) = gen ^ L ∧ n ≤ 48 ∧ σ (.n 115) * σ (.n 412) = gen ^ n ∧
    (∀ t < 6, ∃ h ≤ n, σ (.n (115 + t)) = gen ^ h) ∧ (∃ m ≤ 30, σ (.n 485) = gen ^ m) ∧
    σ (.n 488) = word 8198521646651277316 0

/-- An atom of `verify_sub`'s body before its return holds. -/
theorem vs_atom {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ B1.VerifySub.vsPre True kret) {a : Atom}
    (hm : B1.VerifySub.membB (.atom a) B1.VerifySub.vsPre = true) : a.Holds rd σ := by
  have := B1.VerifySub.holds_of_noRetList _ B1.VerifySub.vsPre_noRet h _ (B1.VerifySub.membB_sound hm)
  simp only [Stmt.Holds] at this
  exact this.1

/-- Table `t`'s height word `kb[2 + t]`: `g^h`, `h` its log height. -/
theorem vsHeightT {bytecode : List K} {rd : Reader} {σ : Val} (S : B1.VerifySub.SizesOk bytecode rd σ) {t : ℕ}
    (ht : t < 6) : σ (.n (115 + t)) = gen ^ (B1.VerifySub.vsLayout bytecode σ).tableLogHeights.getD t 0 := by
  have hn6 : LeanVM.Protocol.Verifier.nTables = 6 := by decide
  have hlen : (B1.VerifySub.vsLayout bytecode σ).tableLogHeights.length = 6 := by
    obtain ⟨-, -, -, hth, -⟩ := B1.Stack.buildLayout_some S.build
    rw [hth, List.length_zipWith]
    simp [B1.VerifySub.vsRows, B1.VerifySub.vsAnnounced, Protocol.Verifier.tableLogFloors, Protocol.Verifier.nTables]
  have := congrArg (fun l ↦ l.getD t 0) S.heights
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show t < Protocol.Verifier.nTables by rw [hn6]; exact ht), Option.map_some,
    Option.getD_some] at this
  rw [this, List.getElem?_eq_getElem (by rw [hlen]; exact ht), List.getD_eq_getElem _ _ (by rw [hlen]; exact ht)]
  rfl

/-- A range checked quotient: `g^n = x·g^h`, `log x < 24`, so `h ≤ n`. -/
theorem le_of_over {rd : Reader} (hm : B1.Digest.MemOk rd) {x y t1 t2 k z : E} {n h : ℕ}
    (hk : k = word 16777216 0) (hrc : LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2)
    (hz : gen ^ n = x * z) (hh : z = gen ^ h) (hh48 : h ≤ 48) (hn : n ≤ 48) : h ≤ n := by
  obtain ⟨f, hf, hx⟩ := B1.Digest.rc_const hm (c := 24) (by norm_num)
    (hk.trans (B1.word_two_pow (a := 24) (by norm_num))) hrc
  have e : gen ^ n = gen ^ (f + h) := by rw [hz, hx, hh, pow_add]
  have := B1.Digest.gen_pow_inj' (by omega) (by omega) e
  omega

/-- **The dispatches' facts at an honest instance** of `verify_sub`, from its shape checks (`vsShapeAT`), its certified
sizes and `g_w = g^(e + 19)`, `g_n = g^n`. -/
theorem ixFacts_of {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} {bytecode : List K}
    (hm : B1.Digest.MemOk rd) (hpre : Stmt.HoldsList C rd σ B1.VerifySub.vsPre True kret)
    (hA : Stmt.HoldsList C rd σ B1.VerifySub.vsShapeAT True kret) (S : B1.VerifySub.SizesOk bytecode rd σ)
    {e n : ℕ} (he : e ≤ 5) (h409 : σ (.n 409) = gen ^ (e + 19)) (hn : n ≤ 48) (h408 : σ (.n 408) = gen ^ n) :
    IxFacts σ := by
  simp only [B1.VerifySub.vsShapeAT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hA
  obtain ⟨-, -, -, -, s4, s5, s6, -, s8, s9, s10, -, -, s13, s14, s15, -, -, s18, s19, s20, -, -, s23, s24, s25, -, -,
    s28, s29, s30, -, -, -, -, -, -, -, -, s39, s40, s41, -⟩ := hA
  have a107 : σ (.n 107) = word 2 0 := vs_atom hpre (a := .const (.n 107) (word 2 0)) (by decide +kernel)
  have a101 : σ (.n 101) = σ (.n 108) * σ (.n 107) :=
    vs_atom hpre (a := .mul (.n 101) (.n 108) (.n 107)) (by decide +kernel)
  have a795 : σ (.n 795) = word 10248187242686185485 0 :=
    vs_atom hpre (a := .const (.n 795) (word 10248187242686185485 0)) (by decide +kernel)
  have a796 : σ (.n 796) = σ (.n 409) * σ (.n 795) :=
    vs_atom hpre (a := .mul (.n 796) (.n 409) (.n 795)) (by decide +kernel)
  have a2892 : σ (.n 2892) = word 10248187242686185485 0 :=
    vs_atom hpre (a := .const (.n 2892) (word 10248187242686185485 0)) (by decide +kernel)
  have a2893 : σ (.n 2893) = σ (.n 409) * σ (.n 2892) :=
    vs_atom hpre (a := .mul (.n 2893) (.n 409) (.n 2892)) (by decide +kernel)
  have s796 : σ (.n 796) = gen ^ (e + 19 - 19) := by
    rw [a796, a795, h409, B1.VerifySub.pow_mul_winv19 (by omega)]
  have s2893 : σ (.n 2893) = gen ^ (e + 19 - 19) := by
    rw [a2893, a2892, h409, B1.VerifySub.pow_mul_winv19 (by omega)]
  have h107 : σ (.n 107) = gen := by
    rw [a107, show (2 : ℕ) = 2 ^ 1 from rfl, B1.VerifySub.gen_word 1 (by decide), pow_one]
  obtain ⟨hlm, hlm30, -⟩ := B1.Stack.buildLayout_some S.build
  have hL := S.logMem
  have hL30 : (B1.VerifySub.vsLayout bytecode σ).logMemory ≤ 30 := hlm ▸ hlm30
  have hLw : (B1.VerifySub.vsLayout bytecode σ).logMemory ≤ e + 19 :=
    le_of_over hm s39 s41 (by rw [← h409, s40]) hL (by omega) (by omega)
  have hH : ∀ t < 6, (B1.VerifySub.vsLayout bytecode σ).tableLogHeights.getD t 0 ≤ 24 := fun t ht ↦
    S.heights24 t (by have : LeanVM.Protocol.Verifier.nTables = 6 := by decide
                      rw [this]; exact ht)
  have a488 : σ (.n 488) = word 8198521646651277316 0 :=
    vs_atom hpre (a := .const (.n 488) (word 8198521646651277316 0)) (by decide +kernel)
  refine ⟨e + 19, _, n, by omega, by omega, h409, ?_, a795, s796, s2893, hLw, hL, hn, ?_, ?_,
    ⟨_, S.st2, S.placed.1⟩, a488⟩
  · rw [s40, a101, h107]; ring
  · rw [mul_comm, ← s5, h408]
  · intro t ht
    refine ⟨_, ?_, vsHeightT S ht⟩
    have h24 := hH t ht
    interval_cases t
    · exact le_of_over hm s4 s6 (by rw [← h408, s5]) (vsHeightT S (t := 0) (by decide)) (by omega) hn
    · exact le_of_over hm s8 s10 (by rw [← h408, s9]) (vsHeightT S (t := 1) (by decide)) (by omega) hn
    · exact le_of_over hm s13 s15 (by rw [← h408, s14]) (vsHeightT S (t := 2) (by decide)) (by omega) hn
    · exact le_of_over hm s18 s20 (by rw [← h408, s19]) (vsHeightT S (t := 3) (by decide)) (by omega) hn
    · exact le_of_over hm s23 s25 (by rw [← h408, s24]) (vsHeightT S (t := 4) (by decide)) (by omega) hn
    · exact le_of_over hm s28 s30 (by rw [← h408, s29]) (vsHeightT S (t := 5) (by decide)) (by omega) hn

/-- An `lt` residual from its two sides' exponents. -/
theorem lt_holds {σ : Val} {a b : CIdx} {x y : ℕ} (ha : (idxC a).valW (vw σ) = gen ^ x)
    (hb : (idxC b).valW (vw σ) = gen ^ y) (hy : y < capE) (h : x < y) : (CRes.lt a b).Holds σ := by
  refine ⟨x, y, ?_, ?_, h⟩
  · rw [ha, Value.gen_pow_eq_ofK]; exact rep_of (by omega)
  · rw [hb, Value.gen_pow_eq_ofK]; exact rep_of hy

theorem valW_num {σ : Val} (k : ℕ) : (idxC (.num k)).valW (vw σ) = gen ^ k := by
  rw [show idxC (.num k) = ⟨[], k⟩ from rfl, valW_gen]
  simp [prodW]

theorem valW_val {σ : Val} (v : ℕ) : (idxC (.val v)).valW (vw σ) = σ (.n v) := by
  simp only [idxC, valW_baseC, vw]

/-- `g_w·g` (`ixGw`, `ixGwSel`) is `g^(w + 1)`. -/
theorem ixGw_val {σ : Val} {w : ℕ} (hw : 19 ≤ w) (h409 : σ (.n 409) = gen ^ w)
    (hg : σ (.n 108) * σ (.n 460) * gen = σ (.n 409)) (h795 : σ (.n 795) = word 10248187242686185485 0) :
    (idxC (.mono ixGw)).valW (vw σ) = gen ^ (w + 1) ∧ (idxC (.mono ixGwSel)).valW (vw σ) = gen ^ (w + 1) := by
  constructor
  · rw [show idxC (.mono ixGw) = ⟨[(108, 1), (460, 1)], 2⟩ from rfl, valW_gen]
    simp only [prodW, vw, pow_one, mul_one]
    calc _ = (σ (.n 108) * σ (.n 460) * gen) * gen := by ring
      _ = gen ^ (w + 1) := by rw [hg, h409, pow_succ]
  · rw [show idxC (.mono ixGwSel) = ⟨[(108, 1), (460, 1), (795, 1)], 21⟩ from rfl, valW_gen]
    simp only [prodW, vw, pow_one, mul_one]
    calc _ = (σ (.n 108) * σ (.n 460) * gen) * σ (.n 795) * gen ^ 20 := by ring
      _ = gen ^ w * word 10248187242686185485 0 * gen ^ 20 := by rw [hg, h409, h795]
      _ = gen ^ (w - 19) * gen ^ 20 := by rw [B1.VerifySub.pow_mul_winv19 hw]
      _ = gen ^ (w + 1) := by rw [← pow_add]; congr 1; omega

/-- `g_n·g` (`ixGn`) is `g^(n + 1)`. -/
theorem ixGn_val {σ : Val} {n : ℕ} (hgn : σ (.n 115) * σ (.n 412) = gen ^ n) :
    (idxC (.mono ixGn)).valW (vw σ) = gen ^ (n + 1) := by
  rw [show idxC (.mono ixGn) = ⟨[(115, 1), (412, 1)], 1⟩ from rfl, valW_gen]
  simp only [prodW, vw, pow_one, mul_one]
  calc _ = (σ (.n 115) * σ (.n 412)) * gen := by ring
    _ = gen ^ (n + 1) := by rw [hgn, pow_succ]

/-- `gmv·g` (`ixGmv`) is `g^(m + 1)`. -/
theorem ixGmv_val {σ : Val} {m : ℕ} (h485 : σ (.n 485) = gen ^ m) (h488 : σ (.n 488) = word 8198521646651277316 0) :
    (idxC (.mono ixGmv)).valW (vw σ) = gen ^ (m + 1) := by
  rw [show idxC (.mono ixGmv) = ⟨[(485, 1), (488, 1)], 17⟩ from rfl, valW_gen]
  simp only [prodW, vw, pow_one, mul_one]
  calc _ = σ (.n 485) * (σ (.n 488) * gen ^ 16) * gen := by ring
    _ = gen ^ (m + 1) := by rw [h488, B1.VerifySub.word_ginv16_mul, h485, pow_succ]; ring

/-- **`ixFam` holds** where the dispatches' facts do. -/
theorem ixFam_holds {σ : Val} (F : IxFacts σ) : ∀ {x : CRes}, ixFam x = true → x.Holds σ := by
  obtain ⟨w, L, n, hw19, hw24, h409, hg, h795, h796, h2893, hLw, h101, hn, hgn, hH, ⟨m, hm, h485⟩, h488⟩ := F
  obtain ⟨hgw, hgws⟩ := ixGw_val hw19 h409 hg h795
  have hcap : w + 1 < capE := by unfold capE; omega
  intro x hx
  match x, hx with
  | .lt (.num k) (.val v), hx =>
    simp only [ixFam, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hx
    obtain ⟨rfl, hk⟩ := hx
    exact lt_holds (valW_num k) ((valW_val 409).trans h409) (by unfold capE; omega) (by omega)
  | .lt (.num k) (.mono c), hx =>
    simp only [ixFam, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Nat.ble_eq] at hx
    obtain ⟨hc | hc, hk⟩ := hx <;> subst hc
    · exact lt_holds (valW_num k) hgw hcap (by omega)
    · exact lt_holds (valW_num k) hgws hcap (by omega)
  | .lt (.val v) (.mono c), hx =>
    simp only [ixFam, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Nat.beq_eq, Nat.ble_eq] at hx
    rcases hx with (⟨rfl | rfl, rfl⟩ | ⟨⟨rfl, h1⟩, h2⟩) | ⟨rfl, rfl⟩
    · exact lt_holds ((valW_val 101).trans h101) hgws hcap (by omega)
    · exact lt_holds ((valW_val 101).trans h101) hgw hcap (by omega)
    · obtain ⟨h, hh, hv⟩ := hH (v - 115) (by omega)
      rw [show 115 + (v - 115) = v by omega] at hv
      exact lt_holds ((valW_val v).trans hv) (ixGn_val hgn) (by unfold capE; omega) (by omega)
    · exact lt_holds ((valW_val 485).trans h485) (ixGmv_val h485 h488) (by unfold capE; omega) (by omega)
  | .under g r, hx =>
    simp only [ixFam] at hx
    split at hx
    · rename_i x j k c
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Nat.beq_eq, Nat.ble_eq] at hx
      intro hc
      have hs : σ (.n x) = ofK (addressOfIndex j) := hc _ (List.mem_singleton_self _)
      rcases hx with ⟨⟨⟨hx, rfl⟩, hj⟩, hk⟩ | ⟨⟨⟨⟨h1, h2⟩, rfl⟩, hj⟩, hk⟩
      · have hsel : σ (.n x) = gen ^ (w - 19) := by rcases hx with rfl | rfl <;> assumption
        have hj' : w - 19 = j := by
          refine B1.Digest.gen_pow_inj' (by omega) (by omega) ?_
          rw [← hsel, hs, Value.gen_pow_eq_ofK]
        exact lt_holds (valW_num k) hgw hcap (by omega)
      · obtain ⟨h, hh, hv⟩ := hH (x - 115) (by omega)
        rw [show 115 + (x - 115) = x by omega] at hv
        have hj' : h = j := by
          refine B1.Digest.gen_pow_inj' (by omega) (by omega) ?_
          rw [← hv, hs, Value.gen_pow_eq_ofK]
        exact lt_holds (valW_num k) (ixGn_val hgn) (by unfold capE; omega) (by omega)
    · cases hx
  | .eq a b, hx =>
    simp only [ixFam, decide_eq_true_eq] at hx
    subst hx
    exact rfl
  | .lt (.num _) (.num _), hx | .lt (.val _) (.num _), hx | .lt (.val _) (.val _), hx
  | .lt (.mono _) _, hx | .nz _, hx | .sub _ _, hx | .subR _ _, hx | .subP _ _, hx => simp [ixFam] at hx

end

end LeanVM.Guest.CoreMode.Own.verify_sub
