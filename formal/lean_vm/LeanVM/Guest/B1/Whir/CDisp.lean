/-
  LeanVM.Guest.B1.Whir.CDisp

  A dispatch on the rate's selector, honestly: the rate's arm called at fixed returns; `level_rate`'s
  block (`osRates`); the positions' dispatch into `level_positions` (`osPositions`).
-/

module

public import LeanVM.Guest.B1.Whir.CAtoms
public import LeanVM.Guest.B1.Whir.RateCfg
public import LeanVM.Guest.B1.Whir.CLvCommit

/-!
# The rate's dispatches, honestly

* `stmtOk_dispatch_of`: a dispatch at the selector `g^i`, `i` below its arms' count, holds when its
  `i`-th arm's relation does.
* `rateDisp_blk`: a dispatch on the rate's selector (`LvRate`) over `(c.lvAt lvl).map f`, its
  returns listed from `r`, holds at those returns when `C (f lv)` does.
* `osRates_complete`: `level_rate`'s block, its values listed by `rateF` at the rate's row: the
  hoisted `0x80`, the row's `g^posOff`, `g^squeezes`, `g^(n / resBatch)`, `g^(n % resBatch)` (the
  state's new `rts` entry, `osRateVals`), the level's positions and window pointers (`lp`, `lw`).
* `sqCapD`: the capacity after squeezes; `osSqCell`: the cell of the level's `g^squeezes`.
* `osPosCall s`, `osPosCall_map`: the dispatch into `level_positions`' arguments (the first word, the
  sponge, `lp`, `lw`, the table, `g^squeezes`) and returns; `osPositions_complete`: the dispatch at
  its returns `capR`, the sponge's capacity `capR`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : Reader → Prop} {H : CallRel → Reader → Prop}

/-- **A dispatch at the selector `g^i`** holds when its `i`-th arm's relation does. -/
theorem stmtOk_dispatch_of {C : CallRel} {rd : Reader} {σ : Val} {x : V} {fs : List String}
    {args rets : List V} {i : ℕ} (hx : σ x = ofK (addressOfIndex i)) (hi : i < fs.length)
    (hc : C (fs.getD i "") (args.map σ) (rets.map σ)) :
    StmtOk C rd σ (.dispatch x fs args rets) :=
  ⟨i, hi, hx, by rwa [List.getD_eq_getElem _ _ hi] at hc⟩

/-- **A dispatch on the rate's selector at its returns**: the returns listed from `r`. -/
theorem rateDisp_blk {σ : Val} {c : OsCfg} {lvl : ℕ} {lv : OsLv} {r n : ℕ} (f : OsLv → String)
    {args : List ℕ} (rets : List E) (hl : rets.length = n) (hargs : ∀ i ∈ args, i < r) (h0 : 0 < r)
    (hrate : ∀ C rd, HM M H C rd → LvRate σ c lvl lv)
    (hC : ∀ C rd, HM M H C rd → C (f lv) (args.map fun i ↦ σ (.n i)) rets) :
    BlkA M H σ r (r + n) [.dispatch (.n osRate) ((c.lvAt lvl).map f) (args.map V.n) (osRun r n)]
      (fun σ' ↦ ∀ j < n, σ' (.n (r + j)) = rets.getD j 0) := by
  refine BlkA.ofHM (lstF r rets) fun C rd hH σ' ha hr ↦ ?_
  have hv : ∀ j < n, σ' (.n (r + j)) = rets.getD j 0 := fun j hj ↦
    lstF_at hr (by omega) j (by omega)
  refine ⟨?_, hv⟩
  simp only [allOk_cons, allOk_nil, and_true]
  obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C rd hH
  have e1 : (args.map V.n).map σ' = args.map fun i ↦ σ (.n i) := by
    simp only [List.map_map]
    exact List.map_congr_left fun i hi ↦ ha i (hargs i hi)
  have e2 : (osRun r n).map σ' = rets := by
    rw [osRun_map]
    refine List.ext_getElem (by simp [hl]) fun j h1 h2 ↦ ?_
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [hv j h1, List.getD_eq_getElem _ _ h2]
  have hx' : σ' (.n osRate) = ofK (addressOfIndex ri) := by rw [ha 0 h0]; exact hx
  have hlt : ri < ((c.lvAt lvl).map f).length := by simp [hlen, hri]
  refine stmtOk_dispatch_of hx' hlt ?_
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_map,
    ← List.getD_eq_getElem _ default (by simpa using hlt), hlv, e1, e2]
  exact hC C rd hH

/-! ## `level_rate`'s values -/

/-- The values `osRates` writes from `k - 1` (`k` its first arm's), at the rate `ri`'s row `lv`; `q`, `b`
the level's positions and window pointers. -/
def rateF (k ri : ℕ) (lv : OsLv) (q b : E) : ℕ → E := fun i ↦
  if i < k then word (2 ^ 63) 0
  else if i < k + 8 then
    (if (i - k) % 2 = 1 ∨ ri = 0 then gw ((osRateVals lv).getD ((i - k) / 2) 0) else 0)
  else if i < k + 8 + 4 * (ligNRates - 1) then
    (if ri ≠ 0 ∧ (i - k - 8) / 4 = ri - 1 then gw ((osRateVals lv).getD ((i - k - 8) % 4) 0) else 0)
  else if i = k + 8 + 4 * (ligNRates - 1) then q else b

/-- **`level_rate`, honestly**: the rate's row's values as words, the level's positions and window
pointers `query_positions·g^posOff`, `query_win_ptrs·g^posOff`. -/
theorem osRates_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, HM M H C rd → st.Ok σ) (hrate : ∀ C rd, HM M H C rd → LvRate σ c lvl lv) :
    BlkA M H σ st.k (osRates c lvl st).2.k (osRates c lvl st).1 (fun σ' ↦
      OsStep σ σ' st (osRates c lvl st).2 ∧
      (∀ j < 4, σ' (.n (st.k + 1 + 2 * j + 1)) = gw ((osRateVals lv).getD j 0)) ∧
      σ' (.n (osRates c lvl st).2.lp) = σ (.n osQpos) * gw lv.posOff ∧
      σ' (.n (osRates c lvl st).2.lw) = σ (.n osQbp) * gw lv.posOff) := by
  refine BlkA.of_ne fun ⟨C0, rd0, hH0⟩ ↦ ?_
  obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate C0 rd0 hH0
  have hn4 : ligNRates = 4 := rfl
  have k33 := hsf.k
  set k := st.k + 1 with hk
  set m := k + 8 + 4 * (ligNRates - 1) with hm
  set q := σ (.n osQpos) * gw lv.posOff
  set b := σ (.n osQbp) * gw lv.posOff
  have hvl : (osRateVals lv).length = 4 := rfl
  refine BlkA.ofHM (rateF k ri lv q b) (fun C rd hH σ' ha hr ↦ ?_) (osRates_noWin _ _ _)
  have ek : (osRates c lvl st).2.k = m + 2 := rfl
  rw [ek] at hr
  have hodd : ∀ j < 4, σ' (.n (k + 2 * j + 1)) = gw ((osRateVals lv).getD j 0) := fun j hj ↦ by
    rw [hr _ (by omega) (by omega)]
    simp only [rateF]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (Or.inl (by omega)),
      show (k + 2 * j + 1 - k) / 2 = j by omega]
  set addr : ℕ → ℕ := fun i ↦ if ri = 0 then k + 2 * i else k + 8 + 4 * (ri - 1) + i with haddrD
  have haddr : ∀ i < 4, σ' (.n (addr i)) = gw ((osRateVals lv).getD i 0) := fun i hi ↦ by
    simp only [haddrD]
    split_ifs with h0
    · rw [hr _ (by omega) (by omega)]
      simp only [rateF]
      rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (Or.inr h0), show (k + 2 * i - k) / 2 = i by omega]
    · rw [hr _ (by omega) (by omega)]
      simp only [rateF]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left ⟨h0, by omega⟩,
        show (k + 8 + 4 * (ri - 1) + i - k - 8) % 4 = i by omega]
  have hmem : ∀ a, Stmt.atom a ∈ osRateArm k ri lv → ∃ i < 4,
      a = .const (.n (addr i)) (gw ((osRateVals lv).getD i 0)) ∨
        a = .copy (.n (k + 2 * i + 1)) (.n (addr i)) := by
    intro a h
    simp only [osRateArm, List.mem_flatten, List.mem_map] at h
    obtain ⟨l, ⟨⟨e, i⟩, hei, rfl⟩, hal⟩ := h
    rw [List.mem_iff_getElem] at hei
    obtain ⟨n, hn, he⟩ := hei
    simp only [List.length_zipIdx] at hn
    simp only [List.getElem_zipIdx, Nat.zero_add, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨n, by omega, ?_⟩
    rw [List.getD_eq_getElem _ _ hn]
    simpa [haddrD] using hal
  have hst : σ' (.n osQpos) = σ (.n osQpos) := ha _ (by show 36 < st.k; omega)
  have hsb : σ' (.n osQbp) = σ (.n osQbp) := ha _ (by show 37 < st.k; omega)
  have h0 := hodd 0 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at h0
  have hq : σ' (.n m) = q := by
    rw [hr _ (by omega) (by omega)]; simp only [rateF]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  have hb : σ' (.n (m + 1)) = b := by
    rw [hr _ (by omega) (by omega)]; simp only [rateF]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  have hok' := hok C rd hH
  refine ⟨?_, ⟨⟨⟨hsf.fs, ⟨fun f hf ↦ by have := hsf.below.fs f hf; show f < m + 2; omega,
    by have := hsf.below.cb; show st.cb < m + 2; omega,
    by have := hsf.below.claim; show st.claim < m + 2; omega, ?_⟩, hsf.co,
    fun p hp ↦ by have := hsf.padB p hp; show p + 4 < m + 2; omega, by show 43 ≤ m + 2; omega⟩,
    matsOk_agree hok'.mats hsf.below.mats fun i hi ↦ ha i hi, ?_⟩, by show st.k ≤ m + 2; omega, ha⟩,
    hodd, ?_, ?_⟩
  · rw [osRates_eq]
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, holds_mul, osMul, holds_const, osCst]
    refine ⟨?_, ⟨ri, by simpa [hlen] using hri, by rw [ha 0 (by omega)]; exact hx, ?_⟩, ?_, ?_⟩
    · rw [hr _ (by omega) (by omega)]; simp only [rateF]; rw [ite_eq_left (by omega)]
    · have harm : ((c.lvAt lvl).zipIdx.map fun (lv, r) ↦ osRateArm k r lv)[ri]'(by simpa [hlen] using hri) =
          osRateArm k ri lv := by
        rw [List.getElem_map, List.getElem_zipIdx]
        simp only [Nat.zero_add]
        rw [← hlv, List.getD_eq_getElem _ _ (by omega)]
      rw [harm]
      intro a ha'
      obtain ⟨i, hi, rfl | rfl⟩ := hmem a ha'
      · rw [holds_const]; exact haddr i hi
      · rw [holds_copy, hodd i hi, haddr i hi]
    · show σ' (.n m) = σ' (.n osQpos) * σ' (.n (k + 1))
      rw [hq, hst, h0]; rfl
    · show σ' (.n (m + 1)) = σ' (.n osQbp) * σ' (.n (k + 1))
      rw [hb, hsb, h0]; rfl
  · intro mm hmm; obtain ⟨a1, a2, a3⟩ := hsf.below.mats mm hmm
    exact ⟨by have : mm.out < st.k := a1; show mm.out < m + 2; omega,
      by have : mm.src < st.k := a2; show mm.src < m + 2; omega,
      by have : mm.base < st.k := a3; show mm.base < m + 2; omega⟩
  · intro p hp
    have hb' := hsf.padB p hp
    obtain ⟨z1, z2, z3, z4⟩ := hok'.pad p hp
    rw [ha _ (by omega), ha _ (by omega), ha _ (by omega), ha _ (by omega)]
    exact ⟨z1, z2, z3, z4⟩
  · exact hq
  · exact hb

/-- The capacity after `n` squeezes from `cap`. -/
def sqCapD (cap : List E) (n : ℕ) : List E := ((⟨cap, []⟩ : Fs).squeezeN n).2.cap

theorem sqCapD_length {cap : List E} (h : cap.length = 5) (n : ℕ) : (sqCapD cap n).length = 5 :=
  squeezeN_cap_length n _ h

/-- The cell of `g^squeezes`, the last level's second `level_rate` value. -/
def osSqCell (s : OsSt) : ℕ := (s.rts.getLast?.getD []).getD 1 0

/-- The arguments and returns of `osPositions c lvl s`'s dispatch into `level_positions`. -/
def osPosCall (s : OsSt) : List V × List V :=
  ((s.word0 :: s.fs ++ [s.lp, s.lw, osTabs, osSqCell s]).map V.n, osRun s.k 5)

theorem osPosCall_map (σ : Val) (s : OsSt) : (osPosCall s).1.map σ =
    σ (.n s.word0) :: s.fsv σ ++ [σ (.n s.lp), σ (.n s.lw), σ (.n osTabs), σ (.n (osSqCell s))] := by
  simp [osPosCall, OsSt.fsv]

/-- **The positions, honestly**: the dispatch into `level_positions` at its returns `capR`, the
sponge's capacity `capR`. -/
theorem osPositions_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, HM M H C rd → st.Ok σ) (hw0 : st.word0 < st.k) (hlp : st.lp < st.k) (hlw : st.lw < st.k)
    (hsq : osSqCell st < st.k) (capR : List E) (hcl : capR.length = 5)
    (hrate : ∀ C rd, HM M H C rd → LvRate σ c lvl lv)
    (hC : ∀ C rd, HM M H C rd → C (osPositionsName lv) ((osPosCall st).1.map σ) capR) :
    BlkA M H σ st.k (osPositions c lvl st).2.k (osPositions c lvl st).1 (fun σ' ↦
      OsStep σ σ' st (osPositions c lvl st).2 ∧
      (osPositions c lvl st).2.F σ' = ⟨capR, []⟩ ∧
      (osPositions c lvl st).2.cur σ' = st.cur σ ∧
      (osPosCall st).1.map σ' = (osPosCall st).1.map σ ∧
      (osPosCall st).2.map σ' = capR) := by
  set k := st.k with hk
  have k33 : 43 ≤ k := hsf.k
  have hfb : ∀ f ∈ st.fs, f < k := hsf.below.fs
  set args := st.word0 :: st.fs ++ [st.lp, st.lw, osTabs, osSqCell st] with hargsD
  have hargs : ∀ i ∈ args, i < k := fun i hi ↦ by
    simp only [hargsD, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | hi | rfl | rfl | rfl | rfl
    · exact hw0
    · exact hfb i hi
    · exact hlp
    · exact hlw
    · show 10 < k; omega
    · exact hsq
  have eA : (osPosCall st).1.map σ = args.map fun i ↦ σ (.n i) := by
    simp only [osPosCall, List.map_map]; rfl
  have h := rateDisp_blk (M := M) (H := H) (σ := σ) (c := c) (lvl := lvl) (lv := lv) (r := k) (n := 5)
    osPositionsName (args := args) capR hcl hargs (by omega) hrate
    (fun C rd hH ↦ by rw [← eA]; exact hC C rd hH)
  have ek : (osPositions c lvl st).2.k = k + 5 := rfl
  rw [ek]
  refine BlkA.congr (BlkA.monoH h.agree fun C rd hH σ' ha ⟨e4, _⟩ ↦ ?_) rfl
  have hok' := hok C rd hH
  have eA' : (osPosCall st).1.map σ' = (osPosCall st).1.map σ := by
    simp only [osPosCall, List.map_map]
    exact List.map_congr_left fun i hi ↦ ha _ (hargs i hi)
  refine ⟨⟨⟨⟨rfl, ⟨?_, ?_, ?_, ?_⟩, hsf.co, fun p hp ↦ by have := hsf.padB p hp; omega,
    by omega⟩, matsOk_agree hok'.mats hsf.below.mats fun i hi ↦ ha i hi, ?_⟩, by omega, ha⟩, ?_, ?_,
    eA', ?_⟩
  · intro f hf
    have hf' : f ∈ [k, k + 1, k + 2, k + 3, k + 4] := hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl | rfl | rfl <;> omega
  · show st.cb < k + 5; have := hsf.below.cb; omega
  · show st.claim < k + 5; have := hsf.below.claim; omega
  · intro m hm; obtain ⟨a, b, d⟩ := hsf.below.mats m hm
    exact ⟨by have : m.out < k := a; omega, by have : m.src < k := b; omega,
      by have : m.base < k := d; omega⟩
  · intro p hp
    have hb' := hsf.padB p hp
    obtain ⟨z1, z2, z3, z4⟩ := hok'.pad p hp
    rw [ha _ (by omega), ha _ (by omega), ha _ (by omega), ha _ (by omega)]
    exact ⟨z1, z2, z3, z4⟩
  · show (⟨[k, k + 1, k + 2, k + 3, k + 4].map (fun i ↦ σ' (.n i)), []⟩ : Fs) = _
    rw [five_getD hcl]
    simp only [List.map_cons, List.map_nil]
    rw [show k = k + 0 from rfl, e4 0 (by omega), e4 1 (by omega), e4 2 (by omega), e4 3 (by omega),
      e4 4 (by omega)]
  · show σ' (.n st.cb) * gen ^ st.co = σ (.n st.cb) * gen ^ st.co
    rw [ha _ hsf.below.cb]
  · show (osRun k 5).map σ' = capR
    rw [osRun_map, five_getD hcl, show List.range 5 = [0, 1, 2, 3, 4] from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [e4 0 (by omega), e4 1 (by omega), e4 2 (by omega), e4 3 (by omega), e4 4 (by omega)]

end
end LeanVM.Guest.B1.Whir
