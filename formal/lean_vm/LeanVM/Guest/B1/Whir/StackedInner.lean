/-
  LeanVM.Guest.B1.Whir.StackedInner

  The glued claims' weight at the terminal point: a level's residual chain is its query claim's
  induced weight, an out-of-domain weight is its claim's `eqEval`.
-/

module

public import LeanVM.Guest.B1.Whir.StackedEnd

/-!
# The glued weight (TRIAGE #36)

`osInner` collects the terminal's `inner` (V:1752-1754) from the guest's two sums: per level its
residual chain times its scalar (G:1270-1296), which `os_rc_eq_inducedWeight` shows is the level's
query claim's `inducedWeight` (V:1643) given the vanishing tables (the subspace polynomial values
and their inverses, `subspaceRoots`, V:984), and the out-of-domain weights (G:1298-1310), each its
claim's `eqEval` (V:703).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The inverses `_induced_weight` takes (V:1648). -/
def osIwInverses (ml : ℕ) : List E := (subspaceRoots ml).map fun v ↦ if v = 0 then 0 else v⁻¹

/-- A level's tables are the subspace polynomial's values and their inverses. -/
def OsTablesOk (lv : OsLvl) : Prop :=
  (∀ t < lv.logCols - 1, eOfNat (lv.vals.getD t 0) = (subspaceRoots lv.logCols).getD t 0) ∧
    ∀ t < lv.logCols, eOfNat (lv.invs.getD t 0) = (osIwInverses lv.logCols).getD t 0

/-! ### The tables in `K` -/

/-- `_subspace_roots`' layers over `K` (V:987-989). -/
def osKRootsAux : ℕ → K → List K → List K
  | 0, _, _ => []
  | n + 1, last, layer =>
    match layer.map fun value ↦ value ^ 2 + last * value with
    | [] => []
    | root :: rest => root :: osKRootsAux n root rest

/-- `_subspace_roots(log_n)` over `K` (V:984-990). -/
def osKRoots (logN : ℕ) : List K :=
  1 :: osKRootsAux logN 1 ((List.range logN).map fun i ↦ K.ofBits (2 ^ (i + 1)))

private theorem subspaceRootsAux_ofK : ∀ (n : ℕ) (last : K) (layer : List K),
    subspaceRootsAux n (ofK last) (layer.map ofK) = (osKRootsAux n last layer).map ofK
  | 0, _, _ => rfl
  | n + 1, last, layer => by
    have hl : (layer.map ofK).map (fun value ↦ value ^ 2 + ofK last * value) =
        (layer.map fun value ↦ value ^ 2 + last * value).map ofK := by
      simp only [List.map_map]
      exact List.map_congr_left fun v _ => by simp [Function.comp, ofK_add, ofK_mul, pow_two]
    simp only [subspaceRootsAux, osKRootsAux, hl]
    cases layer.map fun value ↦ value ^ 2 + last * value with
    | nil => rfl
    | cons root rest => simp [subspaceRootsAux_ofK n root rest]

private theorem subspaceRoots_eq (logN : ℕ) : subspaceRoots logN = (osKRoots logN).map ofK := by
  unfold subspaceRoots osKRoots
  rw [List.map_cons, ← subspaceRootsAux_ofK, List.map_map]
  congr 1

/-- A level's tables in `K`: the subspace polynomial's values, and their inverses by their
products, as the kernel decides them. -/
def OsTablesOkK (lv : OsLvl) : Prop :=
  (∀ t < lv.logCols - 1, K.ofBits (lv.vals.getD t 0) = (osKRoots lv.logCols).getD t 0) ∧
    ∀ t < lv.logCols, (osKRoots lv.logCols).getD t 0 * K.ofBits (lv.invs.getD t 0) = 1

instance (lv : OsLvl) : Decidable (OsTablesOkK lv) := by unfold OsTablesOkK; exact inferInstance

private theorem getD_map_zero {α : Type} [Zero α] {β : Type} [Zero β] (f : α → β) (hf : f 0 = 0) (l : List α)
    (t : ℕ) : (l.map f).getD t 0 = f (l.getD t 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[t]? <;> simp [hf]

theorem OsTablesOkK.ok {lv : OsLvl} (h : OsTablesOkK lv) : OsTablesOk lv := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [subspaceRoots_eq, getD_map_zero _ ofK_zero, ← h.1 t ht]; rfl
  · have hm := h.2 t ht
    unfold osIwInverses
    rw [subspaceRoots_eq, List.map_map, getD_map_zero _ (by simp)]
    simp only [Function.comp]
    have hne : ofK ((osKRoots lv.logCols).getD t 0) ≠ 0 := by
      intro h0
      have := congrArg ofK hm
      rw [ofK_mul, h0, zero_mul, ofK_one] at this
      exact zero_ne_one this
    rw [ite_neg' hne]
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    show ofK _ * ofK _ = 1
    rw [← ofK_mul, hm, ofK_one]

theorem resChain_eq_iwChain {lv : OsLvl} (ht : OsTablesOk lv) (ch0 : E) :
    ∀ t < lv.logCols, resChain lv.vals ch0 t = osIwChain (subspaceRoots lv.logCols) 0 ch0 t := by
  intro t ht'
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [resChain, osIwChain, ih (by omega), Nat.zero_add, ← ht.1 t (by omega)]
    ring

/-- **A level's residual chain is its query claim's induced weight** at the terminal point
`P.drop F ++ T` (`F` the fold challenges through the level, `P` all of them, `T` the tail's). -/
theorem os_rc_eq_inducedWeight {cfg : OsCfg} {i ba bb tch yrLog : ℕ} {F : ℕ} {P T : List E}
    (hT : T.length = yrLog) (hFP : F ≤ P.length)
    (hpre : (cfg.lv i).prefixLen = P.length - F) (hrfo : (cfg.lv i).resFoldOff = F)
    (hml : (cfg.lv i).prefixLen + yrLog = (cfg.lv i).logCols)
    (htab : OsTablesOk (cfg.lv i))
    (hfch : ∀ j < P.length, LoadHolds rd (σ (.n osFch)) j (P.getD j 0))
    (htch : ∀ j < yrLog, LoadHolds rd (σ (.n tch)) j (T.getD j 0))
    (hbasis : ∀ it ∈ osBasisCoords yrLog tch i (cfg.lv i), OsBasisOk rd σ ba bb it)
    {r : OsRec} (hrec : OsRecOk rd σ cfg i r) {rc res : E}
    (hres : ∀ x < (cfg.lv i).queries, ResBody rd (cfg.lv i).posOff (i * 22) (cfg.lv i).logCols
      (i * cfg.maxQ) (cfg.lv i).vals (σ (.n osQpos)) (σ (.n ba)) (σ (.n bb)) rc (σ (.n osQw)) (gen ^ x))
    (h0 : LoadHolds rd rc 0 0) (hN : LoadHolds rd rc (cfg.lv i).queries res) :
    res = inducedWeight (cfg.lv i).logCols r.queries (powers r.lam r.queries.length) (P.drop F ++ T) := by
  obtain ⟨hql, hqpos, hqw, -, -, -⟩ := hrec
  set lv := cfg.lv i
  set pt := P.drop F ++ T
  have hptl : pt.length = lv.logCols := by simp [pt, hT]; omega
  -- the basis rows
  have hAB : ∀ t < lv.logCols, memAt rd (σ (.n ba)) (i * 22 + t) = 1 + pt.getD t 0 ∧
      memAt rd (σ (.n bb)) (i * 22 + t) = pt.getD t 0 * eOfNat (lv.invs.getD t 0) := by
    intro t ht
    have hmem : (i * 22 + t, (if t < lv.prefixLen then (osFch, lv.resFoldOff + t) else (tch, t - lv.prefixLen)),
        lv.invs.getD t 0) ∈ osBasisCoords yrLog tch i lv :=
      List.mem_map.mpr ⟨t, List.mem_range.mpr (by omega), rfl⟩
    obtain ⟨c, lc, la, lb⟩ := hbasis _ hmem
    have hc : c = pt.getD t 0 := by
      by_cases h1 : t < lv.prefixLen
      · simp only [h1, ↓reduceIte, hrfo] at lc
        rw [loadHolds_unique lc (hfch _ (by omega)), os_getD_append_lt (by simp; omega), os_getD_drop']
      · simp only [h1, ↓reduceIte] at lc
        rw [loadHolds_unique lc (htch _ (by omega)), os_getD_append_ge (by simp; omega)]
        congr 1; simp; omega
    subst hc
    exact ⟨memAt_of_load la, memAt_of_load lb⟩
  -- one query's product
  have hprod : ∀ x < lv.queries, ∀ ch0 : E, ch0 = eOfNat (r.queries.getD x 0) →
      resProd (fun t => memAt rd (σ (.n ba)) (i * 22 + t)) (fun t => memAt rd (σ (.n bb)) (i * 22 + t))
        lv.vals ch0 lv.logCols = ∏ t ∈ Finset.range pt.length, (1 + pt.getD t 0 *
          (1 + osIwChain (subspaceRoots lv.logCols) 0 (eOfNat (r.queries.getD x 0)) t *
            (osIwInverses lv.logCols).getD t 0)) := by
    intro x hx ch0 hch
    subst hch
    unfold resProd
    rw [hptl]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    simp only
    rw [(hAB t ht').1, (hAB t ht').2, resChain_eq_iwChain htab _ t ht', ← htab.2 t ht']
    ring
  -- the chain
  have hchain : ∀ x ≤ lv.queries, LoadHolds rd rc x (∑ x' ∈ Finset.range x, r.lam ^ x' *
      ∏ t ∈ Finset.range pt.length, (1 + pt.getD t 0 *
        (1 + osIwChain (subspaceRoots lv.logCols) 0 (eOfNat (r.queries.getD x' 0)) t *
          (osIwInverses lv.logCols).getD t 0))) := by
    intro x hx
    induction x with
    | zero => simpa using h0
    | succ x ih =>
      obtain ⟨ch0, lch, -, r0, wq, lr0, lwq, lr1⟩ := hres x (by omega)
      rw [loadHolds_mul_gen_pow, Nat.add_comm] at lch lwq
      rw [loadHolds_mul_gen_pow, Nat.add_zero] at lr0
      rw [loadHolds_mul_gen_pow] at lr1
      have e1 := loadHolds_unique lch (hqpos x (by omega))
      have e2 := loadHolds_unique lwq (hqw x (by omega))
      have e3 := loadHolds_unique lr0 (ih (by omega))
      rw [hprod x (by omega) ch0 e1, e2, e3] at lr1
      rw [Finset.sum_range_succ]
      exact lr1
  rw [loadHolds_unique hN (hchain _ le_rfl), os_inducedWeight_eq _ _ _ _ (by simp [os_length_powersFrom, powers])]
  rw [hql]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x < lv.queries := Finset.mem_range.mp hx
  rw [os_powers_getD hx']
  rfl

/-! ## The glued claims' weight -/

/-- Level `r`'s glued claims' weight at the point `pt`, after `F` fold challenges. -/
def osRecInner (logN F : ℕ) (r : OsRec) (pt : List E) : E :=
  match r.ood with
  | none => 1 * r.lam * inducedWeight (logN - F) r.queries (powers r.lam r.queries.length) pt
  | some z => 1 * r.lam * eqEval z pt +
      1 * r.lam * r.lam * inducedWeight (logN - F) r.queries (powers r.lam r.queries.length) pt

private theorem foldl_add_map {α : Type} (g : α → E) : ∀ (l : List α) (c : E),
    l.foldl (fun w x => w + g x) c = c + (l.map g).sum
  | [], c => by simp
  | x :: l, c => by rw [List.foldl_cons, foldl_add_map g l, List.map_cons, List.sum_cons, add_assoc]

private theorem sum_map_zipIdx {α : Type} (h : α × ℕ → E) (d : α) : ∀ (l : List α) (s : ℕ),
    ((l.zipIdx s).map h).sum = ∑ i ∈ Finset.range l.length, h (l.getD i d, s + i)
  | [], _ => by simp
  | x :: l, s => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_map_zipIdx h d l (s + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero,
      show ∀ i, s + 1 + i = s + (i + 1) from fun i => by ring]
    rw [add_comm]

/-- **The glued claims' weight** (V:1752-1754) over the records' claims, level by level. -/
theorem os_gluedOf_inner (logN : ℕ) (cfg : OsCfg) (recs : List OsRec) (P T : List E) :
    (osGluedOf logN cfg recs).foldl (fun w c ↦ w + c.scalar * c.weightAt (P.drop c.foldStart ++ T)) 0 =
      ∑ i ∈ Finset.range recs.length,
        osRecInner logN (osLevelF cfg i) (recs.getD i default) (P.drop (osLevelF cfg i) ++ T) := by
  rw [foldl_add_map (fun c : GluedClaim ↦ c.scalar * c.weightAt (P.drop c.foldStart ++ T)), zero_add,
    osGluedOf, List.map_flatten, List.sum_flatten]
  simp only [List.map_map]
  rw [sum_map_zipIdx _ default recs 0]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp, Nat.zero_add, osRecGlued, osRecInner]
  cases hh : (recs.getD i default).ood <;> simp

end
end LeanVM.Guest.B1
