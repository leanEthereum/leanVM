/-
  LeanVM.Guest.CoreMode.Fn.verify_tables.EndExecCoreVt

  `verify_tables`' exponent facts at its honest instances, on core names: the bus point's length `μ`, the memory's
  log-size, the tables' log-heights `τ`, the table sumcheck's rounds `n`, their order, and the ranks' groups.
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_tables.ResVtG
public import LeanVM.Guest.B1.Tables.Vt.ZcCert
public import LeanVM.Guest.B1.Tables.Vt.SelsAll
public import LeanVM.Guest.CoreMode.CoreRes
public import LeanVM.Guest.CoreMode.Fn.verify_tables.Fam
public import LeanVM.Guest.EndExecCoreFn
public import LeanVM.Guest.CoreMode.HeapCSound
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# `verify_tables`' exponents

`vt_exps`: at an honest instance, `g_bus_mu = g^μ` (`19 ≤ μ < 33`), `dims_g[0] = g^lm` (`lm ≤ μ`), `dims_g[1 + t] =
g^τ_t` (`τ_t < 31`), `g_zc_n = g^n` (`τ_t ≤ n ≤ μ`): `TablesPre` (`vt_inst`), `vt_pads`, `vt_sels`, `vt_zc_n`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 hiding lmax
open LeanVM.Guest.B1.Tables
open LeanVM.Protocol LeanVM.Protocol.Verifier

public section

/-- **`verify_tables`' exponents.** -/
structure VtExps (σ : Core.Val) (μ lm n : ℕ) (τ : ℕ → ℕ) : Prop where
  mu : σ (.n (val% «verify_tables» "g_bus_mu")) = gen ^ μ
  lmw : σ (.n (val% «verify_tables» "kb[1]")) = gen ^ lm
  tau : ∀ t < 6, σ (.n ((val% «verify_tables» "kb[1]") + 1 + t)) = gen ^ τ t
  zc : σ (.n (val% «verify_tables» "g_zc_n")) = gen ^ n
  mu19 : 19 ≤ μ
  mu33 : μ < 33
  lmμ : lm ≤ μ
  tau31 : ∀ t < 6, τ t < 31
  taun : ∀ t < 6, τ t ≤ n
  nμ : n ≤ μ

variable {r : Ref}

/-- **`verify_tables`' exponents at an honest instance.** -/
theorem vt_exps (hr : r.Ok) {J : Inst} (hJ : J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (hJt : J.t = .node "verify_tables" σ bufs kids) :
    ∃ μ lm n τ, VtExps σ μ lm n τ := by
  obtain ⟨h, pi, lm, w, pt, vals, hP⟩ := vt_inst hr hJ hJt
  rw [show (List.range 21).map (fun k ↦ σ (.n k)) = [σ (.n (val% «verify_tables» "fs0")), σ (.n (val% «verify_tables» "fs1")), σ (.n (val% «verify_tables» "fs2")), σ (.n (val% «verify_tables» "fs3")), σ (.n (val% «verify_tables» "fs4")),
    σ (.n (val% «verify_tables» "cursor@1")), σ (.n (val% «verify_tables» "pi_0")), σ (.n (val% «verify_tables» "pi_1")), σ (.n (val% «verify_tables» "zeta")), σ (.n (val% «verify_tables» "g_bus_mu")), σ (.n (val% «verify_tables» "dims_g")), σ (.n (val% «verify_tables» "table_rows")), σ (.n (val% «verify_tables» "g_squares")), σ (.n (val% «verify_tables» "fp_w")),
    σ (.n (val% «verify_tables» "beta")), σ (.n (val% «verify_tables» "claim_pool")), σ (.n (val% «verify_tables» "chi")), σ (.n (val% «verify_tables» "gkr_leaves")), σ (.n (val% «verify_tables» "tabs")), σ (.n (val% «verify_tables» "bc_point")), σ (.n (val% «verify_tables» "stream"))] from rfl] at hP
  obtain ⟨-, hz, hmu, hml, -, hlm, ⟨ds, -, hds⟩, hE, -⟩ := hP
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hμ : r.κ ≤ 32 := by omega
  obtain ⟨k0, kl⟩ := vt_kb h
  have hpads := vt_pads hμ r.img σ h
  obtain ⟨τ, hτ⟩ := tb_exists_fun_of_forall (α := ℕ) (n := 6)
    (P := fun t τ ↦ τ < 31 ∧ σ (.n ((val% «verify_tables» "kb[1]") + 1 + t)) = gen ^ τ) (fun t ht ↦ by
      obtain ⟨τ, n, zs, h1, h2, -⟩ := hpads t ht
      refine ⟨τ, h1, ?_⟩
      have := kl (t + 1) (by omega)
      rw [show (val% «verify_tables» "kb[1]") + 1 + t = (val% «verify_tables» "kb[1]") + (t + 1) by omega]
      exact LeanVM.Guest.B1.loadHolds_unique this h2)
  have k1 : σ (.n (val% «verify_tables» "kb[1]")) = gen ^ lm := by
    have := LeanVM.Guest.B1.loadHolds_unique (kl 0 (by omega)) (hds 0 (by simp))
    simpa using this
  have hkb : ∀ i < 8, σ (.n (val% «verify_tables» "kb[0]" + i)) = gen ^ ([0, lm] ++ vtTauList τ).getD i 0 := by
    intro i hi
    match i, hi with
    | 0, _ => simpa using k0
    | 1, _ => simpa using k1
    | t + 2, hi =>
      have ht : t < 6 := by omega
      rw [show val% «verify_tables» "kb[0]" + (t + 2) = (val% «verify_tables» "kb[1]") + 1 + t by omega, (hτ t ht).2]
      simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
      rw [List.getD_eq_getElem _ _ (by simp [vtTauList]; omega)]
      simp [vtTauList]
  have hτ33 : ∀ t < 6, τ t < 33 := fun t ht ↦ by have := (hτ t ht).1; omega
  obtain ⟨hl1, hl2, -⟩ := vt_sels hμ r.img h hz hmu hml hE hlm hτ33 hkb
  obtain ⟨n, hn, htn, -, hnm⟩ := vt_zc_n hμ r.img h hτ33 (fun t ht ↦ (hτ t ht).2) hml hmu
  exact ⟨pt.length, lm, n, τ, hmu, k1, fun t ht ↦ (hτ t ht).2, hn, hl2, hml, hl1, fun t ht ↦ (hτ t ht).1, htn,
    hnm⟩

theorem vtRvC_eq (v0 r : ℕ) : CoreMode.vtRvC v0 r = vtRv v0 r := rfl

/-- `[B]·[v]` and `[B]·g^e` name one address when `σ v = g^e`. -/
theorem vt_addr_eq {σ : Core.Val} {B v e : ℕ} (h : σ (.n v) = gen ^ e) :
    (⟨[(B, 1), (v, 1)], 0⟩ : CoreMode.CCell).addrW (CoreMode.vw σ) =
      (⟨[(B, 1)], e⟩ : CoreMode.CCell).addrW (CoreMode.vw σ) := by
  show (σ (.n B) ^ 1 * (σ (.n v) ^ 1 * 1) * ofK (addressOfIndex 0)).limb 0 =
    (σ (.n B) ^ 1 * 1 * ofK (addressOfIndex e)).limb 0
  rw [h, show addressOfIndex 0 = (1 : K) from pow_zero _, show ofK (1 : K) = 1 from _root_.map_one (algebraMap K E),
    ← ofK_gpow]
  ring_nf

/-- **`verify_tables`' buffers through its hinted order** (`vtPerm`) at an honest instance: `vt_groups_at`. -/
theorem vtPerm_inst (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {x : CoreMode.CRes} (h : CoreMode.vtPerm fn x = true) : x.Holds σ := by
  match x, h with
  | .subP c cs, h =>
    simp only [CoreMode.vtPerm, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
    obtain ⟨hn, p, hp, hc⟩ := h
    have hf' : f = name% «verify_tables» := by rw [← find_name' hf, hn]
    subst hf'
    obtain ⟨hPs, hCs, -, -, hPr, hCr⟩ := vt_groups_at hr hI ht
    -- each side: its ranks' values name groups in `[lo, hi)`, and every group there is some rank's
    have hside : ∀ p ∈ CoreMode.vtSides, (∀ v ∈ p.1, ∃ e, p.2.1 ≤ e ∧ e < p.2.2 ∧ σ (.n v) = gen ^ e) ∧
        ∀ e, p.2.1 ≤ e → e < p.2.2 → ∃ v ∈ p.1, σ (.n v) = gen ^ e := by
      intro p hp
      simp only [CoreMode.vtSides, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only
      · refine ⟨fun v hv ↦ ?_, fun e _ he ↦ ?_⟩
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
          obtain ⟨e, he, hσ⟩ := hPr r (List.mem_range.mp hr)
          exact ⟨e, Nat.zero_le _, he, hσ⟩
        · obtain ⟨r, hr, hσ⟩ := hPs e he
          exact ⟨_, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩, hσ⟩
      · refine ⟨fun v hv ↦ ?_, fun e he1 he2 ↦ ?_⟩
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
          exact hCr r (List.mem_range.mp hr)
        · obtain ⟨r, hr, hσ⟩ := hCs (e - 18) (by omega)
          refine ⟨_, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩, ?_⟩
          rw [vtRvC_eq, hσ, show 18 + (e - 18) = e by omega]
    obtain ⟨hto, hfrom⟩ := hside p hp
    obtain ⟨cb, co⟩ := c
    split at hc
    · rename_i B v hcb
      simp only [Bool.and_eq_true, Nat.beq_eq, List.contains_iff_mem, List.all_eq_true, List.mem_range'_1] at hc
      obtain ⟨⟨hco, hv⟩, hall⟩ := hc
      simp only at hcb hco
      subst hcb hco
      obtain ⟨e, he1, he2, hσ⟩ := hto v hv
      exact ⟨_, hall e ⟨he1, by omega⟩, vt_addr_eq hσ⟩
    · rename_i B hcb
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, List.all_eq_true, List.contains_iff_mem] at hc
      obtain ⟨⟨h1, h2⟩, hall⟩ := hc
      simp only at hcb h1 h2
      subst hcb
      obtain ⟨v, hv, hσ⟩ := hfrom co h1 h2
      exact ⟨_, hall v hv, (vt_addr_eq hσ).symm⟩
    · cases hc
  | .lt _ _, h | .nz _, h | .sub _ _, h | .subR _ _, h | .under _ _, h => simp [CoreMode.vtPerm] at h

/-! ## The exponent family -/

open LeanVM.Guest.CoreMode (VtL ladd lmin lmax vtUB vtBaseN vtF vtM vtI vtArms vtExpR)

/-- `Σ x_i·s_i`. -/
def ldot : List ℤ → List ℤ → ℤ
  | x :: xs, y :: ys => x * y + ldot xs ys
  | [], _ => 0
  | _ :: _, [] => 0

/-- A form's value at the slacks `s`. -/
def vtEv (f : VtL) (s : List ℤ) : ℤ := f.1 + ldot f.2 s

theorem ldot_lscale (k : ℤ) : ∀ (g s : List ℤ), ldot (CoreMode.lscale k g) s = k * ldot g s
  | y :: ys, a :: ss => by simp only [CoreMode.lscale, ldot, ldot_lscale k ys ss]; ring
  | [], s => by simp [CoreMode.lscale, ldot]
  | _ :: _, [] => by simp [CoreMode.lscale, ldot]

theorem ldot_ladd (k : ℤ) : ∀ (f g s : List ℤ), ldot (ladd k f g) s = ldot f s + k * ldot g s
  | x :: xs, y :: ys, a :: ss => by simp only [ladd, ldot, ldot_ladd k xs ys ss]; ring
  | x :: xs, [], a :: ss => by simp only [ladd, ldot, ldot_ladd k xs [] ss]; ring
  | [], gs, s => by simp only [ladd, ldot, ldot_lscale]; ring
  | _ :: _, _ :: _, [] => by simp [ladd, ldot]
  | _ :: _, [], [] => by simp [ladd, ldot]

theorem vtEv_add (f g : VtL) (k : ℤ) (s : List ℤ) : vtEv (f.add g k) s = vtEv f s + k * vtEv g s := by
  simp only [vtEv, VtL.add, ldot_ladd]; ring

theorem vtEv_nil (c : ℤ) (s : List ℤ) : vtEv (c, []) s = c := by simp [vtEv, ldot]

/-- The slacks in the box `0 ≤ s_i ≤ u_i`. -/
def VtBox : List ℤ → List ℤ → Prop
  | s :: ss, u :: us => 0 ≤ s ∧ s ≤ u ∧ VtBox ss us
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False

theorem box_le : ∀ (f s u : List ℤ), VtBox s u → lmin f u ≤ ldot f s ∧ ldot f s ≤ lmax f u
  | [], s, u, _ => by cases u <;> simp [lmin, lmax, ldot]
  | x :: xs, a :: ss, b :: us, ⟨h0, h1, h⟩ => by
    obtain ⟨i1, i2⟩ := box_le xs ss us h
    simp only [lmin, lmax, ldot]
    have e1 : min 0 (x * b) ≤ x * a := by
      rcases le_or_gt 0 x with hx | hx
      · exact le_trans (min_le_left _ _) (mul_nonneg hx h0)
      · exact le_trans (min_le_right _ _) (by nlinarith)
    have e2 : x * a ≤ max 0 (x * b) := by
      rcases le_or_gt 0 x with hx | hx
      · exact le_trans (by nlinarith) (le_max_right _ _)
      · exact le_trans (by nlinarith) (le_max_left _ _)
    constructor <;> linarith
  | _ :: _, [], [], _ => by simp [lmin, lmax, ldot]
  | _ :: _, [], _ :: _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

theorem minv_le {s : List ℤ} (hb : VtBox s vtUB) (f : VtL) : f.minv ≤ vtEv f s ∧ vtEv f s ≤ f.maxv := by
  obtain ⟨h1, h2⟩ := box_le f.2 s vtUB hb
  simp only [VtL.minv, VtL.maxv, vtEv]; constructor <;> linarith

/-- **A word's form at the slacks**: its value nonnegative, the word `g` to it. -/
def VtV (σ : Core.Val) (s : List ℤ) (v : V) (F : VtL) : Prop := 0 ≤ vtEv F s ∧ σ v = gen ^ (vtEv F s).toNat

/-- The instance's slacks. -/
def vtS (μ lm n : ℕ) (τ : ℕ → ℕ) : List ℤ :=
  [(μ : ℤ) - 19, (μ : ℤ) - n, (n : ℤ) - τ 0, (n : ℤ) - τ 1, (n : ℤ) - τ 2, (n : ℤ) - τ 3, (n : ℤ) - τ 4,
    (n : ℤ) - τ 5, (μ : ℤ) - lm]

theorem vtS_box {σ : Core.Val} {μ lm n : ℕ} {τ : ℕ → ℕ} (hE : VtExps σ μ lm n τ) : VtBox (vtS μ lm n τ) vtUB := by
  have h0 := hE.taun 0 (by norm_num); have h1 := hE.taun 1 (by norm_num); have h2 := hE.taun 2 (by norm_num)
  have h3 := hE.taun 3 (by norm_num); have h4 := hE.taun 4 (by norm_num); have h5 := hE.taun 5 (by norm_num)
  have := hE.mu19; have := hE.mu33; have := hE.lmμ; have := hE.nμ
  simp only [vtS, vtUB, VtBox, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **The slacks' words**, at a valuation whose ghost `GB + j` is `dims_g[j]`'s word. -/
theorem vtBaseN_sound {σ : Core.Val} {μ lm n : ℕ} {τ : ℕ → ℕ} (hE : VtExps σ μ lm n τ)
    {σ' : Core.Val} (hag : ∀ v : V, v.idx < CoreMode.GB → σ' v = σ v)
    (hg : ∀ j < 7, σ' (V.n (CoreMode.GB + j)) = σ (V.n ((val% «verify_tables» "kb[1]") + j))) {x : ℕ} {F : VtL} (h : vtBaseN x = some F) :
    VtV σ' (vtS μ lm n τ) (V.n x) F := by
  unfold vtBaseN at h
  dsimp only at h
  -- the word at `x`: its own, or for a ghost `dims_g[j]`'s
  have hy : ∀ y, (if CoreMode.GB ≤ x ∧ x < CoreMode.GB + 7 then x - CoreMode.GB + (val% «verify_tables» "kb[1]") else x) = y →
      y < CoreMode.GB → σ' (V.n x) = σ (V.n y) := by
    intro y hy hyG
    by_cases hx : CoreMode.GB ≤ x ∧ x < CoreMode.GB + 7
    · simp only [hx, and_self, ↓reduceIte] at hy
      have e1 : CoreMode.GB + (x - CoreMode.GB) = x := by omega
      have := hg (x - CoreMode.GB) (by omega)
      rw [e1] at this
      rw [this, ← hy, Nat.add_comm]
    · simp only [hx, ↓reduceIte] at hy
      subst hy; exact hag _ hyG
  generalize hY : (if CoreMode.GB ≤ x ∧ x < CoreMode.GB + 7 then x - CoreMode.GB + (val% «verify_tables» "kb[1]") else x) = y at h hy
  have hGmu : val% «verify_tables» "g_bus_mu" < CoreMode.GB := by unfold CoreMode.GB; decide
  have hGzc : val% «verify_tables» "g_zc_n" < CoreMode.GB := by unfold CoreMode.GB; decide
  have hGkb : (val% «verify_tables» "kb[1]") + 7 < CoreMode.GB := by unfold CoreMode.GB; decide
  have h0 := hE.taun 0 (by norm_num); have h1 := hE.taun 1 (by norm_num); have h2 := hE.taun 2 (by norm_num)
  have h3 := hE.taun 3 (by norm_num); have h4 := hE.taun 4 (by norm_num); have h5 := hE.taun 5 (by norm_num)
  have := hE.mu19; have := hE.lmμ; have := hE.nμ
  unfold VtV
  split_ifs at h with c9 c25 c27 cτ
  · obtain rfl := Option.some.inj h
    subst c9
    have e : vtEv (19, [1, 0, 0, 0, 0, 0, 0, 0, 0]) (vtS μ lm n τ) = (μ : ℤ) := by
      simp only [vtEv, ldot, vtS]; ring
    rw [hy _ rfl (by omega), hE.mu, e]
    exact ⟨by positivity, by simp⟩
  · obtain rfl := Option.some.inj h
    subst c25
    have e : vtEv (19, [1, -1, 0, 0, 0, 0, 0, 0, 0]) (vtS μ lm n τ) = (n : ℤ) := by
      simp only [vtEv, ldot, vtS]; ring
    rw [hy _ rfl (by omega), hE.zc, e]
    exact ⟨by positivity, by simp⟩
  · obtain rfl := Option.some.inj h
    subst c27
    have e : vtEv (19, [1, 0, 0, 0, 0, 0, 0, 0, -1]) (vtS μ lm n τ) = (lm : ℤ) := by
      simp only [vtEv, ldot, vtS]; ring
    rw [hy _ rfl (by omega), hE.lmw, e]
    exact ⟨by positivity, by simp⟩
  · obtain rfl := Option.some.inj h
    obtain ⟨t, ht, rfl⟩ : ∃ t < 6, y = (val% «verify_tables» "kb[1]") + 1 + t := ⟨y - ((val% «verify_tables» "kb[1]") + 1), by omega, by omega⟩
    rw [hy _ rfl (by omega), hE.tau t ht]
    have hev : vtEv (19, (List.range 9).map fun i ↦
        if i = 0 then (1 : ℤ) else if i = 1 then -1 else if i = (val% «verify_tables» "kb[1]") + 1 + t - (val% «verify_tables» "kb[1]") + 1 then -1 else 0)
        (vtS μ lm n τ) =
        (τ t : ℤ) := by
      interval_cases t <;> simp [vtEv, ldot, vtS, List.range_succ]
    rw [hev]
    exact ⟨by positivity, by simp⟩

/-- **A word's form is its exponent** (`vtF`), the top-level atoms holding. -/
theorem vtF_sound {rd : Reader} {σ : Core.Val} {s : List ℤ} {as : List Atom} (hall : ∀ a ∈ as, a.Holds rd σ)
    (hbase : ∀ x F, vtBaseN x = some F → VtV σ s (V.n x) F) (hb : VtBox s vtUB) :
    ∀ f v F, vtF as f v = some F → VtV σ s v F
  | 0, v, F, h => by simp [vtF] at h
  | f + 1, v, F, h => by
    unfold vtF at h
    rcases hd : (if v.path = [] ∧ v.tag = 0 then vtBaseN v.idx else none) with _ | b
    swap
    · rw [hd] at h
      simp only [Option.some.injEq] at h
      subst h
      by_cases hv : v.path = [] ∧ v.tag = 0
      · simp only [hv, and_self, ↓reduceIte] at hd
        have : v = V.n v.idx := by obtain ⟨p, t, i⟩ := v; simp only at hv; obtain ⟨rfl, rfl⟩ := hv; rfl
        rw [this]
        exact hbase _ _ hd
      · simp only [hv, ↓reduceIte] at hd; cases hd
    · rw [hd] at h
      simp only at h
      obtain ⟨a, ha, hs⟩ := List.exists_of_findSome?_eq_some h
      have hH := hall a ha
      cases a
      case const d w =>
        dsimp only at hs
        split_ifs at hs with hd
        subst hd
        split at hs
        · rename_i k hk
          obtain rfl := Option.some.inj hs
          simp only [Atom.Holds] at hH
          refine ⟨by rw [vtEv_nil]; positivity, ?_⟩
          rw [hH, powOf1_sound hk, vtEv_nil, ofK_gpow]; simp
        · cases hs
      case copy d a' =>
        dsimp only at hs
        split_ifs at hs with hd
        subst hd
        simp only [Atom.Holds] at hH
        obtain ⟨h1, h2⟩ := vtF_sound hall hbase hb f a' F hs
        exact ⟨h1, by rw [hH, h2]⟩
      case mul d a' b' =>
        simp only [Atom.Holds] at hH
        dsimp only at hs
        split_ifs at hs with hd ha' hb''
        · subst hd
          split at hs
          · rename_i p q hp hq
            obtain rfl := Option.some.inj hs
            obtain ⟨p0, p1⟩ := vtF_sound hall hbase hb f a' p hp
            obtain ⟨q0, q1⟩ := vtF_sound hall hbase hb f b' q hq
            unfold VtV
            rw [vtEv_add, one_mul]
            refine ⟨by omega, ?_⟩
            rw [hH, p1, q1, ← pow_add]; congr 1; omega
          · cases hs
        · subst ha'
          split at hs
          · rename_i p q hp hq
            split_ifs at hs with hm
            obtain rfl := Option.some.inj hs
            have hm' := (minv_le hb (p.add q (-1))).1
            obtain ⟨p0, p1⟩ := vtF_sound hall hbase hb f d p hp
            obtain ⟨q0, q1⟩ := vtF_sound hall hbase hb f b' q hq
            unfold VtV
            rw [vtEv_add] at hm' ⊢
            refine ⟨by omega, ?_⟩
            rw [p1, q1] at hH
            have e : gen ^ (vtEv p s).toNat = gen ^ (vtEv p s + -1 * vtEv q s).toNat * gen ^ (vtEv q s).toNat := by
              rw [← pow_add]; congr 1; omega
            rw [e] at hH
            exact (mul_right_cancel₀ (Value.gen_pow_ne_zero _) hH).symm
          · cases hs
        · subst hb''
          split at hs
          · rename_i p q hp hq
            split_ifs at hs with hm
            obtain rfl := Option.some.inj hs
            have hm' := (minv_le hb (p.add q (-1))).1
            obtain ⟨p0, p1⟩ := vtF_sound hall hbase hb f d p hp
            obtain ⟨q0, q1⟩ := vtF_sound hall hbase hb f a' q hq
            unfold VtV
            rw [vtEv_add] at hm' ⊢
            refine ⟨by omega, ?_⟩
            rw [p1, q1] at hH
            have e : gen ^ (vtEv p s).toNat = gen ^ (vtEv q s).toNat * gen ^ (vtEv p s + -1 * vtEv q s).toNat := by
              rw [← pow_add]; congr 1; omega
            rw [e] at hH
            exact (mul_left_cancel₀ (Value.gen_pow_ne_zero _) hH).symm
          · cases hs
      all_goals simp at hs

/-- **A cell's form**: its bases' product is `g` to the form less the offset. -/
theorem vtM_sound {σ : Core.Val} {s : List ℤ} {as : List Atom}
    (hF : ∀ v F, vtF as CoreMode.vtFuel v = some F → VtV σ s v F) :
    ∀ (bs : List (ℕ × ℕ)) (o : ℤ) (F : VtL), vtM as bs o = some F →
      0 ≤ vtEv F s - o ∧ CoreMode.prodW (CoreMode.vw σ) bs = gen ^ (vtEv F s - o).toNat
  | [], o, F, h => by
    simp only [vtM, Option.some.injEq] at h; subst h
    simp [vtEv_nil, CoreMode.prodW]
  | (b, e) :: bs, o, F, h => by
    simp only [vtM] at h
    split at h
    · rename_i p q hp hq
      obtain rfl := Option.some.inj h
      obtain ⟨p0, p1⟩ := hF _ _ hp
      obtain ⟨q0, q1⟩ := vtM_sound hF bs o q hq
      obtain ⟨P, hP⟩ := Int.eq_ofNat_of_zero_le p0
      obtain ⟨Q, hQ⟩ := Int.eq_ofNat_of_zero_le q0
      have hev : vtEv (q.add p e) s - o = ((Q + e * P : ℕ) : ℤ) := by
        rw [vtEv_add]; push_cast; rw [← hP, ← hQ]; ring
      rw [hev]
      refine ⟨by positivity, ?_⟩
      simp only [CoreMode.prodW, CoreMode.vw]
      rw [p1, q1, hP, hQ, Int.toNat_natCast, Int.toNat_natCast, Int.toNat_natCast, ← pow_mul, ← pow_add]
      ring_nf
    · cases h

/-- **An index's exponent** (`vtI`): its word `g` to its form, below `2^62`. -/
theorem vtI_sound {σ : Core.Val} {s : List ℤ} {as : List Atom} (hb : VtBox s vtUB)
    (hF : ∀ v F, vtF as CoreMode.vtFuel v = some F → VtV σ s v F) {i : CoreMode.CIdx} {F : VtL}
    (h : vtI as i = some F) (hs : CoreMode.vtSmall F = true) :
    0 ≤ vtEv F s ∧ CoreMode.rep ((CoreMode.idxC i).valW (CoreMode.vw σ)) = some (vtEv F s).toNat := by
  obtain ⟨h0, h1⟩ := vtM_sound hF _ _ _ h
  have hmax := (minv_le hb F).2
  simp only [CoreMode.vtSmall, decide_eq_true_eq] at hs
  have hoff : (0 : ℤ) ≤ ((CoreMode.idxC i).off : ℤ) := by positivity
  refine ⟨by omega, ?_⟩
  rw [CoreMode.CCell.valW, h1, ← ofK_gpow, ← LeanVM.Parameters.ofK_mul]
  rw [show Parameters.g ^ (vtEv F s - ((CoreMode.idxC i).off : ℤ)).toNat * addressOfIndex (CoreMode.idxC i).off =
      addressOfIndex (vtEv F s).toNat by
    rw [addressOfIndex, addressOfIndex, ← pow_add]; congr 1; omega]
  exact CoreMode.rep_of (by unfold CoreMode.capE at hs ⊢; omega)

/-- **The arms' equations keep a form's value** where the arms hold. -/
theorem vtArms_ev {σ : Core.Val} {s : List ℤ} {as : List Atom} (hb : VtBox s vtUB)
    (hF : ∀ v F, vtF as CoreMode.vtFuel v = some F → VtV σ s v F) :
    ∀ (arms : List (ℕ × ℕ)), (∀ p ∈ arms, σ (V.n p.1) = ofK (addressOfIndex p.2)) →
      ∀ f, vtEv (vtArms as arms f) s = vtEv f s
  | [], _, f => rfl
  | (x, j) :: arms, h, f => by
    simp only [vtArms]
    rw [vtArms_ev hb hF arms (fun p hp ↦ h p (List.mem_cons_of_mem _ hp))]
    split
    · rename_i F hFx
      split_ifs with hc
      · -- the arm's form is `j`
        obtain ⟨hj, hm⟩ := hc
        obtain ⟨F0, F1⟩ := hF _ _ hFx
        have hmax := (minv_le hb F).2
        have hx := h (x, j) List.mem_cons_self
        have hxj : (vtEv F s).toNat = j :=
          Value.gen_pow_inj (by unfold CoreMode.capE at hm; omega) (by unfold CoreMode.capE at hj; omega)
            (by rw [← F1, hx]; exact ofK_gpow j)
        have hev : vtEv F s = j := by omega
        have key : ∀ k, vtEv (f.add (F.add ((j : ℤ), []) (-1)) k) s = vtEv f s := fun k ↦ by
          rw [vtEv_add, vtEv_add, vtEv_nil, hev]; ring
        split
        · split_ifs
          · exact key _
          · rfl
        · rfl
      · rfl
    · rfl

theorem vtNN_le {σ : Core.Val} {s : List ℤ} {as : List Atom} (hb : VtBox s vtUB)
    (hF : ∀ v F, vtF as CoreMode.vtFuel v = some F → VtV σ s v F)
    (hbase : ∀ x F, vtBaseN x = some F → VtV σ s (V.n x) F) {arms : List (ℕ × ℕ)}
    (ha : ∀ p ∈ arms, σ (V.n p.1) = ofK (addressOfIndex p.2)) {f : VtL} (h : CoreMode.vtNN as arms f = true) :
    0 ≤ vtEv f s := by
  simp only [CoreMode.vtNN, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  have e := vtArms_ev hb hF arms ha f
  rcases h with h | ⟨x, -, hx⟩
  · have := (minv_le hb (vtArms as arms f)).1
    omega
  · split at hx
    · rename_i F hF'
      simp only [decide_eq_true_eq] at hx
      have h1 := (minv_le hb ((vtArms as arms f).add F (-1))).1
      rw [vtEv_add] at h1
      have h2 := (hbase _ _ hF').1
      omega
    · cases hx

theorem vtLt_sound {σ : Core.Val} {s : List ℤ} {as : List Atom} (hb : VtBox s vtUB)
    (hF : ∀ v F, vtF as CoreMode.vtFuel v = some F → VtV σ s v F)
    (hbase : ∀ x F, vtBaseN x = some F → VtV σ s (V.n x) F) {arms : List (ℕ × ℕ)}
    (ha : ∀ p ∈ arms, σ (V.n p.1) = ofK (addressOfIndex p.2)) {a b : CoreMode.CIdx}
    (h : CoreMode.vtLt as arms a b = true) :
    ∃ A B : VtL, vtI as a = some A ∧ vtI as b = some B ∧ 0 ≤ vtEv A s ∧ vtEv A s < vtEv B s ∧
      CoreMode.rep ((CoreMode.idxC a).valW (CoreMode.vw σ)) = some (vtEv A s).toNat ∧
      CoreMode.rep ((CoreMode.idxC b).valW (CoreMode.vw σ)) = some (vtEv B s).toNat := by
  simp only [CoreMode.vtLt] at h
  split at h
  · rename_i A B hA hB
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨sA, sB⟩, hn⟩ := h
    obtain ⟨a0, a1⟩ := vtI_sound hb hF hA sA
    obtain ⟨b0, b1⟩ := vtI_sound hb hF hB sB
    have hd := vtNN_le hb hF hbase ha hn
    rw [vtEv_add, vtEv_add, vtEv_nil] at hd
    exact ⟨A, B, hA, hB, a0, by omega, a1, b1⟩
  · cases h

theorem mul_gpow_congr (X : E) {a b : ℕ} (h : a = b) :
    X * ofK (Parameters.g ^ a) = X * ofK (Parameters.g ^ b) := by rw [h]

theorem prodW_append (w : ℕ → E) : ∀ (l l' : List (ℕ × ℕ)),
    CoreMode.prodW w (l ++ l') = CoreMode.prodW w l * CoreMode.prodW w l'
  | [], l' => by simp [CoreMode.prodW]
  | (b, e) :: l, l' => by simp only [List.cons_append, CoreMode.prodW, prodW_append w l l']; ring

/-- **`vtSubP1`**: `[B]·[J]·g^o` is one of `cs` where the arms hold. -/
theorem vtSubP1_sound {σ : Core.Val} {s : List ℤ} {as : List Atom} (hb : VtBox s vtUB)
    (hF : ∀ v F, vtF as CoreMode.vtFuel v = some F → VtV σ s v F)
    (hbase : ∀ x F, vtBaseN x = some F → VtV σ s (V.n x) F) {arms : List (ℕ × ℕ)}
    (ha : ∀ p ∈ arms, σ (V.n p.1) = ofK (addressOfIndex p.2)) {co B J : ℕ} {cs : List CoreMode.CCell}
    (h : CoreMode.vtSubP1 as arms co B J cs = true) :
    ∃ c' ∈ cs, (⟨[(B, 1), (J, 1)], co⟩ : CoreMode.CCell).addrW (CoreMode.vw σ) = c'.addrW (CoreMode.vw σ) := by
  simp only [CoreMode.vtSubP1, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.contains_iff_mem] at h
  obtain ⟨hall, hl⟩ := h
  obtain ⟨A, Bn, -, hBn, a0, hab, a1, -⟩ := vtLt_sound hb hF hbase ha hl
  have eB : Bn = ((cs.length : ℤ), []) := by
    simp only [CoreMode.vtI, CoreMode.vtM, CoreMode.idxC, Option.some.injEq] at hBn; exact hBn.symm
  rw [eB, vtEv_nil] at hab
  -- `σ J = g^e`, `e < |cs|`
  have hJ : CoreMode.vw σ J = gen ^ (vtEv A s).toNat := by
    have := (CoreMode.rep_spec a1).2
    simp only [CoreMode.idxC, CoreMode.baseC, CoreMode.CCell.valW, CoreMode.prodW, pow_one, mul_one] at this
    rw [show (addressOfIndex 0 : K) = 1 from pow_zero _,
      show ofK (1 : K) = 1 from _root_.map_one (algebraMap K E), mul_one] at this
    rw [this, ← ofK_gpow]
  refine ⟨⟨[(B, 1)], co + (vtEv A s).toNat⟩, hall (vtEv A s).toNat (by omega), ?_⟩
  simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, pow_one, mul_one, hJ,
    Parameters.addressOfIndex, ← ofK_gpow, mul_assoc, ← LeanVM.Parameters.ofK_mul, ← pow_add]
  refine congrArg (·.limb 0) (mul_gpow_congr _ ?_)
  omega

/-- **The exponent family holds** where its arms hold (`vtExpR`). -/
theorem vtExpR_sound {σ : Core.Val} {s : List ℤ} {as : List Atom} (hb : VtBox s vtUB)
    (hF : ∀ v F, vtF as CoreMode.vtFuel v = some F → VtV σ s v F)
    (hbase : ∀ x F, vtBaseN x = some F → VtV σ s (V.n x) F) :
    ∀ (r : CoreMode.CRes) (arms : List (ℕ × ℕ)), (∀ p ∈ arms, σ (V.n p.1) = ofK (addressOfIndex p.2)) →
      vtExpR as arms r = true → r.Holds σ
  | .lt a b, arms, ha, h => by
    simp only [vtExpR] at h
    obtain ⟨A, B, -, -, a0, hab, a1, b1⟩ := vtLt_sound hb hF hbase ha h
    exact ⟨_, _, a1, b1, by omega⟩
  | .subP c cs, arms, ha, h => by
    simp only [vtExpR] at h
    obtain ⟨cb, co⟩ := c
    unfold CoreMode.vtSubP at h
    simp only at h
    split at h
    · rename_i _ B J
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact vtSubP1_sound hb hF hbase ha h
      · obtain ⟨c', hc', e⟩ := vtSubP1_sound hb hF hbase ha h
        refine ⟨c', hc', ?_⟩
        rw [← e]
        simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW]
        exact congrArg (fun e : E ↦ e.limb 0) (by ring)
    · cases h
  | .subR q r, arms, ha, h => by
    simp only [vtExpR, Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hq1, hr1⟩, htk⟩, h⟩ := h
    split at h
    · rename_i m ql qh rl rh hm hql hqh hrl hrh
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨sm, sql⟩, sqh⟩, srl⟩, srh⟩, n1⟩, n2⟩ := h
      obtain ⟨m0, m1⟩ := vtM_sound hF _ _ _ hm
      obtain ⟨ql0, ql1⟩ := vtI_sound hb hF hql sql
      obtain ⟨qh0, qh1⟩ := vtI_sound hb hF hqh sqh
      obtain ⟨rl0, rl1⟩ := vtI_sound hb hF hrl srl
      obtain ⟨rh0, rh1⟩ := vtI_sound hb hF hrh srh
      have d1 := vtNN_le hb hF hbase ha n1
      have d2 := vtNN_le hb hF hbase ha n2
      simp only [vtEv_add] at d1 d2
      intro x hx
      obtain ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩ := CoreMode.runSet_iff.mp hx
      rw [ql1, Option.some.injEq] at h1
      rw [qh1, Option.some.injEq] at h2
      subst h1 h2
      have hmo := (minv_le hb m).2
      refine CoreMode.runSet_iff.mpr ⟨_, _, (vtEv m s + j).toNat, rl1, rh1, by omega, by omega, ?_⟩
      -- `q`'s cell is `r`'s base times `g` to `F_m + j`
      refine congrArg (fun e : E ↦ e.limb 0) ?_
      have hbs : q.base.bases = r.base.bases ++ q.base.bases.drop r.base.bases.length := by
        conv_lhs => rw [← List.take_append_drop r.base.bases.length q.base.bases]
        rw [htk]
      rw [hq1, hr1, CoreMode.CCell.valW, CoreMode.CCell.valW, hbs, prodW_append, m1]
      simp only [one_mul, ← ofK_gpow, Parameters.addressOfIndex, mul_assoc, ← LeanVM.Parameters.ofK_mul, ← pow_add]
      refine mul_gpow_congr _ ?_
      omega
    · cases h
  | .under cs r, arms, ha, h => by
    intro hg
    simp only [vtExpR] at h
    refine vtExpR_sound hb hF hbase r _ (fun p hp ↦ ?_) h
    rcases List.mem_append.mp hp with hp | hp
    · exact ha p hp
    · obtain ⟨c, hc, hcp⟩ := List.mem_filterMap.mp hp
      cases c with
      | arm x j =>
        simp only [Option.some.injEq] at hcp
        subst hcp
        exact hg _ hc
      | zero _ => cases hcp
      | nonzero _ => cases hcp
  | .nz _, _, _, h | .sub _ _, _, _, h => by simp [vtExpR] at h

/-- The top-level atoms' values are among the body's. -/
theorem topAtoms_uses : ∀ {ss : List Stmt} {a : Atom}, a ∈ Res.topAtoms ss →
    ∀ v ∈ Memory.atomUses a ++ Memory.atomTmps a, v ∈ Memory.Stmt.usesList ss ++ Memory.Stmt.tmpsList ss
  | [], _, h => by simp [Res.topAtoms] at h
  | s :: ss, a, h => by
    intro v hv
    have hrest : a ∈ Res.topAtoms ss → v ∈ Memory.Stmt.usesList (s :: ss) ++ Memory.Stmt.tmpsList (s :: ss) :=
      fun h' ↦ by
        have := topAtoms_uses h' v hv
        simp only [Memory.Stmt.usesList, Memory.Stmt.tmpsList, List.mem_append] at this ⊢
        tauto
    cases s with
    | atom a' =>
      simp only [Res.topAtoms, List.mem_cons] at h
      rcases h with rfl | h
      · simp only [Memory.Stmt.usesList, Memory.Stmt.tmpsList, Memory.Stmt.uses, Memory.Stmt.tmps,
          List.mem_append] at hv ⊢
        tauto
      · exact hrest h
    | _ =>
      simp only [Res.topAtoms] at h
      split_ifs at h
      · exact hrest h
      · cases h

theorem vtAtoms_top : ∀ a ∈ CoreMode.vtAtoms, a ∈ Res.topAtoms (fn% «verify_tables»).body := by decide +kernel

/-- **`verify_tables`' exponent family at an honest instance**, at a valuation `σ'` agreeing with its own below `GB`
whose ghost slots hold its own parameter words (`GwR`), the body naming no ghost (`ngB`). -/
theorem vtExp_inst (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) {σ' : Core.Val} (hag : ∀ v : V, v.idx < CoreMode.GB → σ' v = σ v)
    (hng : CoreMode.ngB fn = true) {G : CoreMode.HSig} (hgw : CoreMode.GwR r.img G σ') {x : CoreMode.CRes}
    (h : CoreMode.vtExp fn G.gw x = true) : x.Holds σ' := by
  simp only [CoreMode.vtExp, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hn, hG⟩, h⟩ := h
  have hf' : f = name% «verify_tables» := by rw [← find_name' hf, hn]
  subst hf'
  obtain ⟨μ, lm, n, τ, hE⟩ := vt_exps hr hI ht
  obtain ⟨args, rets, fn', hf'', -, es, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf'')
  obtain rfl : fn = fn% «verify_tables» := Option.some.inj (hf.symm.trans B1.VerifySub.find_vt)
  have hall : ∀ a ∈ Res.topAtoms (fn% «verify_tables»).body, a.Holds r.img.read σ :=
    fun a ha ↦ hh _ (topAtoms_on_path hw ha)
  -- the family's atoms hold at `σ'`: they name no ghost
  have hng' := hng
  simp only [CoreMode.ngB, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at hng'
  have hall' : ∀ a ∈ CoreMode.vtAtoms, a.Holds r.img.read σ' := fun a ha ↦ by
    have ha' := vtAtoms_top a ha
    exact (Memory.atom_holds_congr a fun v hv ↦ hag v (hng'.1.2 v (topAtoms_uses ha' v hv))).mpr (hall a ha')
  -- ghost `GB + j` is `dims_g[j]`'s word
  obtain ⟨-, hkl⟩ := vt_kb (vt_inst hr hI ht).1
  have hg : ∀ j < 7, σ' (V.n (CoreMode.GB + j)) = σ (V.n ((val% «verify_tables» "kb[1]") + j)) := fun j hj ↦ by
    have hmem : ((⟨[(val% «verify_tables» "dims_g", 1)], j⟩ : CoreMode.CCell), j) ∈ G.gw := by
      rw [hG]; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have e1 := hgw _ _ hmem
    obtain ⟨hK, hrd⟩ := hkl j hj
    simp only [CoreMode.vw] at e1
    rw [e1]
    simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, CoreMode.vw, pow_one, mul_one,
      Mode.limb_mul_ofK, hag (V.n (val% «verify_tables» "dims_g")) (by unfold CoreMode.GB; norm_num), hrd, Option.getD_some]
  have hb := vtS_box hE
  have hbase := fun x F (hx : vtBaseN x = some F) ↦ vtBaseN_sound hE hag hg hx
  exact vtExpR_sound hb (vtF_sound hall' hbase hb CoreMode.vtFuel) hbase x [] (by simp) h

end

end LeanVM.Guest.EndExec
