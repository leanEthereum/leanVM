/-
  LeanVM.Guest.Backend.Sound.Obl.Os

  The obligations of `open_stacked__L0` to `__L10`: at each level, the dispatch into
  `level_queries` gets the callee's windows from the dispatch into `level_positions` before it.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.GuestU
public import LeanVM.Guest.B1.Whir.LpSound
public import LeanVM.Guest.B1.Whir.HelperAll
public import LeanVM.Guest.B1.Bits.QueryWindowsAll
public import LeanVM.Guest.B1.Opening.QueriesWalk

/-!
# `open_stacked`

`open_stacked__L{m}` (eleven parameters, the window table `tabs` its argument `10`, in relation `1`)
dispatches, at each level, on the rate `σ 0` into `level_positions` (statement `k`) and then into
`level_queries` (statement `i`). At arm `r`, `level_positions`' meaning (B1's `lp_sound`,
`MeaningLevelPositions`) puts the windows of the queries it decodes at its argument `7`, the
window pointers, which the `level_queries` arm gets as its argument `5` (the same value, or the
same product of one value by a constant: `sameVal`): B1's `QueryWinsOk`, so
`OqMainWins` at `g^n` (`oqMainWins_of_queryWinsOk`), the callee's `XSpec.lq n w`, when the
decodes cover the walk (`lpCovers`). `osSiteOk` decides a pair of sites, `os_obl` gives `OblFn`.
-/

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `level_positions`' windows -/

/-- The decode's numbers a walk of `oqCount odd base n` queries at depth `d` and cap depth `cd`
needs of `sq` squeezes. -/
def lpCovers (sq n odd base d cd : ℕ) : Bool :=
  Nat.ble (oqCount odd base n) (sq * (128 / d)) && Nat.ble 1 (128 / d) &&
    digitsVal (osPowDigits (128 / d)) 1 == 128 / d && Nat.blt 0 sq && Nat.blt sq ordG &&
    Nat.blt (sq * 5) u128Bound && queryWindowsShapes.contains (dqwName d cd, d, cd)

/-- **The window pointers name windows**: every query `S·128/d` decodes covers, its pointer at
`qbp` a frame run of its windows at a position below `2^d`. -/
theorem queryWinsOk_of_lp {rd : Reader} {S d cd q : ℕ} (hd : 1 ≤ 128 / d)
    (hq : q ≤ S * (128 / d)) {args rets : List E} (h : MeaningLevelPositions S d cd rd args rets) :
    QueryWinsOk rd (args.getD 7 0) q d cd := by
  intro k hk bp hbp
  set per := 128 / d
  have hjj : k / per < S := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact lt_of_lt_of_le hk hq
  have ht : k % per < per := Nat.mod_lt _ (by omega)
  have hk' : k = k / per * per + k % per := by
    have := Nat.div_add_mod k per; rw [Nat.mul_comm] at this; omega
  have hw := h.1 (k / per) hjj
  simp only [MeaningDecodeQueryWindows] at hw
  obtain ⟨-, hall⟩ := hw
  obtain ⟨-, p, hptr, hrun⟩ := hall (k % per) ht
  rw [loadHolds_mul_gen_pow, ← hk'] at hptr
  rw [loadHolds_unique hbp hptr]
  exact ⟨_, by unfold qwPosOf; exact Nat.mod_lt _ (by positivity), hrun⟩

/-- **A call of `level_positions`** of `lpTable` at `[w0, fs0..fs4, qpos, qbp, tabs]`, the table
at `tabs`: its window pointers at `qbp` name windows for the walk of `oqCount odd base n` queries
it covers. -/
theorem lp_walk {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {e : String × ℕ × String × ℕ × ℕ}
    (he : e ∈ lpTable) {n odd base : ℕ} (hodd : odd = 1 → base = 1)
    (hcov : lpCovers e.2.1 n odd base e.2.2.2.1 e.2.2.2.2 = true)
    {args rets : List E} (hwt : WinTabs L.read (args.getD 8 0))
    (hrel : coreProgram.Rel L.read e.1 args rets) :
    OqMainWins L.read e.2.2.2.1 e.2.2.2.2 odd base (args.getD 7 0) (gen ^ n) := by
  obtain ⟨hf, hl⟩ := lpTable_ok e he
  simp only [lpCovers, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq,
    List.contains_iff_mem] at hcov
  obtain ⟨⟨⟨⟨⟨⟨hq, hper⟩, hpw⟩, hs0⟩, hso⟩, hs5⟩, hshape⟩ := hcov
  have hm := Whir.lp_sound hf hl hpw hs0 hso hs5
    (fun a r ha hc ↦ decode_query_windows_all_holds _ hshape hκ L a r ha hc) hwt hrel
  exact oqMainWins_of_queryWinsOk hodd (queryWinsOk_of_lp hper hq hm)

/-! ## The sites -/

/-- Arm `r`: the `level_queries` arm `q` takes `XSpec.lq n w`, and the `level_positions` arm `p`
is one of `lpTable` covering that walk. -/
def armOk (p q : String) : Bool :=
  match xSpecOf q with
  | some (.lq n w) =>
      (w.odd != 1 || w.base == 1) && lpTable.any fun e =>
        nameKey e.1 == nameKey p && e.2.2.2.1 == w.d && e.2.2.2.2 == w.cd &&
          lpCovers e.2.1 n w.odd w.base w.d w.cd
  | _ => false

theorem armOk_spec {p q : String} {sp : XSpec} (h : armOk p q = true) (hq : xSpecOf q = some sp) :
    ∃ n w, sp = .lq n w ∧ (w.odd = 1 → w.base = 1) ∧ ∃ e ∈ lpTable, e.1 = p ∧
      e.2.2.2.1 = w.d ∧ e.2.2.2.2 = w.cd ∧ lpCovers e.2.1 n w.odd w.base w.d w.cd = true := by
  unfold armOk at h
  rw [hq] at h
  split at h
  · rename_i n w heq
    obtain rfl := Option.some.inj heq
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
      List.any_eq_true] at h
    obtain ⟨ho, e, he, ⟨⟨hk, hd⟩, hcd⟩, hc⟩ := h
    exact ⟨n, w, rfl, fun h1 => ho.resolve_left (not_not.mpr h1), e, he, nameKey_inj hk, hd, hcd, hc⟩
  · exact absurd h (by simp)

/-- The product `a · c` an atom of `pre` puts at `u`. -/
def defMul (pre : List Stmt) (u : V) : Option (V × V) :=
  pre.findSome? fun s => match s with
    | .atom (.mul d a c) => if veq d u then some (a, c) else none
    | _ => none

/-- The constant's low bits an atom of `pre` puts at `u`. -/
def defConst (pre : List Stmt) (u : V) : Option Nat :=
  pre.findSome? fun s => match s with
    | .atom (.const d c) => if veq d u then lowBits c else none
    | _ => none

/-- `u` and `v` are one value, or products of one value by equal constants, by atoms of `pre`. -/
def sameVal (pre : List Stmt) (u v : V) : Bool :=
  veq u v || match defMul pre u, defMul pre v with
    | some (a1, c1), some (a2, c2) => veq a1 a2 && match defConst pre c1, defConst pre c2 with
        | some w1, some w2 => w1 == w2
        | _, _ => false
    | _, _ => false

theorem defMul_spec {pre : List Stmt} {u a c : V} (h : defMul pre u = some (a, c)) :
    Stmt.atom (.mul u a c) ∈ pre := by
  obtain ⟨s, hs, hf⟩ := List.exists_of_findSome?_eq_some h
  split at hf
  · split at hf
    · rename_i hd
      obtain rfl := eq_of_veq hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact hs
    · exact absurd hf (by simp)
  · exact absurd hf (by simp)

theorem defConst_spec {pre : List Stmt} {u : V} {w : Nat} (h : defConst pre u = some w) :
    ∃ c, Stmt.atom (.const u c) ∈ pre ∧ c = ofK (K.ofBits w) := by
  obtain ⟨s, hs, hf⟩ := List.exists_of_findSome?_eq_some h
  split at hf
  · rename_i c
    split at hf
    · rename_i hd
      obtain rfl := eq_of_veq hd
      exact ⟨c, hs, lowBits_spec hf⟩
    · exact absurd hf (by simp)
  · exact absurd hf (by simp)

theorem sameVal_spec {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} {pre : List Stmt}
    {u v : V} (hnr : Stmt.noRetList pre = true) (h : Stmt.HoldsList C rd σ pre True kret)
    (hs : sameVal pre u v = true) : σ u = σ v := by
  unfold sameVal at hs
  rcases Bool.or_eq_true_iff.mp hs with hs | hs
  · rw [eq_of_veq hs]
  split at hs
  · rename_i a1 c1 a2 c2 hu hv
    simp only [Bool.and_eq_true] at hs
    obtain ⟨ha, hs⟩ := hs
    split at hs
    · rename_i w1 w2 h1 h2
      obtain rfl := eq_of_beq hs
      obtain rfl := eq_of_veq ha
      obtain ⟨k1, hk1, e1⟩ := defConst_spec h1
      obtain ⟨k2, hk2, e2⟩ := defConst_spec h2
      have m1 := atom_of_mem hnr h (defMul_spec hu)
      have m2 := atom_of_mem hnr h (defMul_spec hv)
      have d1 := atom_of_mem hnr h hk1
      have d2 := atom_of_mem hnr h hk2
      simp only [Atom.Holds] at m1 m2 d1 d2
      rw [m1, m2, d1, d2, e1, e2]
    · exact absurd hs (by simp)
  · exact absurd hs (by simp)

/-- **A pair of sites**: statement `k` dispatches on `x` into `level_positions` on `argsP`, with the
window table `σ 10` and the window pointers `argsP[7]`; statement `i > k` dispatches on `x` into
`level_queries` on `argsQ`, its argument `5` the same window pointers, each arm `armOk`; the
statements before `i` return nowhere. -/
def osSiteOk (body : List Stmt) (i k : ℕ) : Bool :=
  decide (k < i) && Stmt.noRetList (body.take i) &&
    match body.drop k, body.drop i with
    | .dispatch x fsP argsP _ :: _, .dispatch y fsQ argsQ _ :: _ =>
        decide (y = x) && decide (fsQ.length = fsP.length) && decide (fsQ.length < 64) &&
          decide (9 ≤ argsP.length) && decide (6 ≤ argsQ.length) &&
          decide (argsP.getD 8 default = .n 10) &&
          sameVal (body.take i) (argsQ.getD 5 default) (argsP.getD 7 default) &&
          (List.range fsQ.length).all fun r => armOk (fsP.getD r "") (fsQ.getD r "")
    | _, _ => false

theorem osSiteOk_spec {body : List Stmt} {i k : ℕ} (h : osSiteOk body i k = true) :
    k < i ∧ Stmt.noRetList (body.take i) = true ∧
    ∃ x fsP argsP retsP r1 fsQ argsQ retsQ r2,
      body.drop k = .dispatch x fsP argsP retsP :: r1 ∧ body.drop i = .dispatch x fsQ argsQ retsQ :: r2 ∧
      fsQ.length = fsP.length ∧ fsQ.length < 64 ∧ 9 ≤ argsP.length ∧ 6 ≤ argsQ.length ∧
      argsP.getD 8 default = .n 10 ∧
      sameVal (body.take i) (argsQ.getD 5 default) (argsP.getD 7 default) = true ∧
      ∀ r < fsQ.length, armOk (fsP.getD r "") (fsQ.getD r "") = true := by
  unfold osSiteOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hki, hnr⟩, h⟩ := h
  refine ⟨hki, hnr, ?_⟩
  split at h
  · rename_i x fsP argsP retsP r1 y fsQ argsQ retsQ r2 hk hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨rfl, hl⟩, h64⟩, hp⟩, hq⟩, h8⟩, h5⟩, harm⟩ := h
    exact ⟨y, fsP, argsP, retsP, r1, fsQ, argsQ, retsQ, r2, hk, hi, hl, h64, hp, hq, h8, h5, harm⟩
  · exact absurd h (by simp)

/-- **`open_stacked`'s decided check**: function `j` has eleven parameters and the window table
at argument `10` in its precondition, each pair of `sites` (`level_queries`' dispatch, then
`level_positions'`) is `osSiteOk`, and the analysis accepts it with the `level_queries`
dispatches as sites. -/
def osOkF (g : Fn) (sites : List (ℕ × ℕ)) : Bool :=
  decide (g.params = (List.range 11).map V.n) && decide ((10, 1) ∈ (guestTab.sig g.name).xpre) &&
    sites.all (fun p => osSiteOk g.body p.1 p.2) && chkFnX guestTab [] (sites.map (·.1)) g

/-- `osOkF` of function `j`. -/
noncomputable def osOk (j : ℕ) (sites : List (ℕ × ℕ)) : Bool :=
  osOkF (coreProgram.getD j default) sites

/-- **`open_stacked`'s obligations**, from its decided check. -/
theorem os_obl {j : ℕ} {sites : List (ℕ × ℕ)} (hok : osOk j sites = true) :
    OblFn (coreProgram.getD j default) := by
  simp only [osOk, osOkF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨hp, hx⟩, hs⟩, hc⟩ := hok
  apply oblFn_of_chkX hc (fun _ _ _ _ _ _ _ p hp => absurd hp List.not_mem_nil)
  intro κ L _ h2 C σ hC hpre i hi st ss hd hl
  obtain ⟨⟨i', k⟩, hik, rfl⟩ := List.mem_map.mp hi
  obtain ⟨hki, hnr, x, fsP, argsP, retsP, r1, fsQ, argsQ, retsQ, r2, hdk, hdi, hlen, h64, hlP, hlQ,
    h8, h5, harm⟩ := osSiteOk_spec (hs _ hik)
  rw [hdi] at hd
  obtain ⟨rfl, -⟩ := List.cons.inj hd
  have hwt : WinTabs L.read (σ (.n 10)) := by
    have := hpre.1.2.2 (10, 1) hx (by rw [hp]; simp)
    rw [hp, getD_range_map (by norm_num : 10 < 11)] at this
    exact this.2.1 rfl
  have hdisp := holds_at hki hnr hdk hl
  simp only [Stmt.HoldsList, Stmt.Holds, and_true] at hdisp
  obtain ⟨r', hr', hxr', hCr⟩ := hdisp
  intro r hr hxr _ sp hsp
  obtain ⟨n, w, rfl, hodd, e, he, he1, hd, hcd, hcov⟩ :=
    armOk_spec (harm r hr) (by rw [List.getD_eq_getElem _ _ hr]; exact hsp)
  have hrr : r' = r := by
    rw [← gen_pow_eq_ofK] at hxr' hxr
    exact gen_pow_inj (by omega) (by omega) (hxr'.symm.trans hxr)
  subst hrr
  have hrel := (hC _ _ _ hCr).1
  rw [List.getElem_eq_getD (fallback := ""), ← he1] at hrel
  rw [← hd, ← hcd] at hcov
  have hw := lp_walk (h2.trans maxLogMem_le) L he hodd hcov
    (by rw [getD_map_lt (by omega), h8]; exact hwt) hrel
  simp only [XSpec.Holds]
  rw [getD_map_lt (by omega), sameVal_spec hnr hl h5, ← getD_map_lt (σ := σ) (l := argsP) (i := 7)
    (by omega), ← hd, ← hcd]
  exact hw

end
end LeanVM.Guest.Backend.Obl
