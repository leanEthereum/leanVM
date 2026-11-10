/-
  LeanVM.Guest.B1.Terminal.TermKids

  `check_opening_terminal`'s callees on the honest words: the prefix chains, the public input's
  chain, the selector tables, the column selectors, the outputs' chain, the ring switch's weight,
  each complete, placed.
-/

module

public import LeanVM.Guest.B1.Terminal.SelComplete
public import LeanVM.Guest.B1.Terminal.KidsDep
public import LeanVM.Guest.B1.Terminal.EqPrefixIn
public import LeanVM.Guest.B1.Terminal.Loop15Complete
public import LeanVM.Guest.B1.Ring.WeightComplete
public import LeanVM.Guest.B1.Terminal.Holds

/-!
# The terminal's callees

The caller's words: `TermBases` names the bases of the pointer arguments (`termArgs`), `TermRegion`
the words the terminal and its callees read there. `TermData` gathers the honest data: the bus
point `zs`, the tables' point `chis`, the outputs' point, the ring switch's point and
coefficients, the terminal point `x`, the committed columns' logs `KC` and offsets `OF`, the memory's
log `m` and `KECCAK`'s `τ`.

The honest buffers: `eqChain as bs`, the prefix products `eq_prefix_chain` writes; `piW`, the public
input's chain. `termKids`: the 107 callees in order, each column selector reading the selector
tables' result (`selKid`); `termKids_complete`: each is complete, placed (`eqc_kid_complete`,
`l15_kid_complete`, B1-c's `selector_tables_completeAt`, `cs_completeAt`, `rsw_completeAt`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)
open Finset

@[expose] public section

/-! ## The caller's words -/

/-- The bases of `check_opening_terminal`'s pointer arguments. -/
structure TermBases where
  gsq : ℕ
  zeta : ℕ
  chi : ℕ
  kb : ℕ
  off : ℕ
  zv : ℕ
  ct : ℕ
  pt : ℕ
  pt1 : ℕ

/-- `check_opening_terminal`'s arguments, its pointers at their bases (G:3234). -/
def termArgs (B : TermBases) (rm gmu gzcn glm gtau lamCl inner yr target : E) : List E :=
  [ofK (addressOfIndex B.gsq), ofK (addressOfIndex B.zeta), ofK (addressOfIndex B.chi), rm, gmu,
    gzcn, glm, gtau, ofK (addressOfIndex B.kb), lamCl, ofK (addressOfIndex B.off),
    ofK (addressOfIndex B.zv), ofK (addressOfIndex B.ct), ofK (addressOfIndex B.pt),
    ofK (addressOfIndex B.pt1), inner, yr, target]

/-- **The caller's words the terminal reads**: the bus point (`nz` words) and the tables' point
(`nc`), the base `kappa_base`, the columns' offsets, the selector's nibble shares at
`g_squares·g^34`, the outputs' point and the ring switch's (`τ + 6` words each, the latter at
`z_vals·g^39`), the ring map's coefficients, the terminal point and its complements. -/
def TermRegion (B : TermBases) (nz nc τ : ℕ) (i : ℕ) : Prop :=
  (B.zeta ≤ i ∧ i < B.zeta + nz) ∨ (B.chi ≤ i ∧ i < B.chi + nc) ∨
    (B.kb ≤ i ∧ i < B.kb + 8) ∨ (B.off ≤ i ∧ i < B.off + 101) ∨
    (B.gsq + 34 ≤ i ∧ i < B.gsq + 34 + 128) ∨
    (B.zv ≤ i ∧ i < B.zv + (τ + 6)) ∨ (B.zv + 39 ≤ i ∧ i < B.zv + 39 + (τ + 6)) ∨
    (B.ct ≤ i ∧ i < B.ct + 64) ∨ (B.pt ≤ i ∧ i < B.pt + 40) ∨ (B.pt1 ≤ i ∧ i < B.pt1 + 40)

/-- The honest data the terminal's callees use. -/
structure TermData where
  B : TermBases
  rm : E
  gmu : E
  gzcn : E
  glm : E
  gtau : E
  zs : List E
  chis : List E
  outPt : List E
  ringPoint : List E
  coeffs : List E
  x : List E
  KC : List ℕ
  OF : List ℕ
  m : ℕ
  τ : ℕ

/-! ## The honest buffers -/

/-- `1 + x`, zero-padded: the words at `point1`. -/
def p1Of (x : List E) : List E := (padPoint x).map (1 + ·)

/-- The selector tables' point. -/
def pt32 (x : List E) : List E := (padPoint x).take 32

/-- The selector tables' complements. -/
def pt132 (x : List E) : List E := (p1Of x).take 32

/-- The prefix products `eq_prefix_chain(chain, 1, a, b1, g^|as|)` writes. -/
def eqChain (as bs : List E) : List E := (List.range (as.length + 1)).map (prefixProd 1 as bs)

/-- The public input's chain: `1`, then `(rm + ps[0])·Π_{0 < i < k} ps[i]`, `1 ≤ k ≤ m`. -/
def piW (rm : E) (ps : List E) (m : ℕ) : List E :=
  (List.range (m + 1)).map fun k => if k = 0 then 1 else (rm + ps.getD 0 0) * ∏ i ∈ Ico 1 k, ps.getD i 0

theorem p1Of_length {x : List E} (h : x.length ≤ termPointCap) : (p1Of x).length = 40 := by
  simp [p1Of, padPoint_length h]

theorem eqChain_length (as bs : List E) : (eqChain as bs).length = as.length + 1 := by simp [eqChain]

theorem piW_length (rm : E) (ps : List E) (m : ℕ) : (piW rm ps m).length = m + 1 := by simp [piW]

theorem piW_getD {rm : E} {ps : List E} {m k : ℕ} (hk : k ≤ m) :
    (piW rm ps m).getD k 0 = if k = 0 then 1 else (rm + ps.getD 0 0) * ∏ i ∈ Ico 1 k, ps.getD i 0 := by
  rw [List.getD_eq_getElem _ _ (by simp [piW]; omega)]
  simp [piW]

theorem ofK_gpow_mul_gen (b c : ℕ) : ofK (addressOfIndex b) * gen ^ c = ofK (addressOfIndex (b +
    c)) := by
  rw [gen_pow_eq_ofK, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, pow_add]

theorem regionL_cons {L : Main.Layout} (q : ℕ × List E) {i : ℕ} (h : RegionL L i) :
    RegionL (q :: L) i := by
  obtain ⟨q', hq, h⟩ := h
  exact ⟨q', List.mem_cons_of_mem _ hq, h⟩

theorem regionL_head {L : Main.Layout} {b : ℕ} {xs : List E} {i : ℕ} (h1 : b ≤ i)
    (h2 : i < b + xs.length) : RegionL ((b, xs) :: L) i :=
  ⟨(b, xs), List.mem_cons_self, h1, h2⟩

/-! ## The callees -/

/-- The value of committed column `c`'s selector: the eq weight of its offset's bits above its log
against the point's. -/
def selRet (x : List E) (KC OF : List ℕ) (c : ℕ) : E :=
  Tables.bitsEq ((List.range (32 - KC.getD c 0)).map fun i => (OF.getD c 0).testBit (KC.getD c 0 + i))
    ((pt32 x).drop (KC.getD c 0)) ((pt132 x).drop (KC.getD c 0))

/-- `selector_tables`' result among the results before. -/
def stRes (pv : List (List E × Main.Layout)) : List E × Main.Layout := pv.getD 3 ([], [])

/-- **Committed column `c`'s selector**, on `selector_tables`' result (entered when it is one). -/
noncomputable def selKid (D : TermData) (c : ℕ) : KidD := fun pv =>
  open Classical in
  ⟨Tables.lName "column_selector" (D.KC.getD c 0),
    decide (Tables.stOut D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x) (stRes pv).1 (stRes pv).2),
    [gen ^ D.OF.getD c 0, (stRes pv).1.getD 0 0, ofK (addressOfIndex (D.B.gsq + 34))],
    if Tables.stOut D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x) (stRes pv).1 (stRes pv).2 then
      (stRes pv).2 ++ Tables.stLin D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x) ++
        [(D.B.gsq + 34, gTabW)] else [],
    Returns [selRet D.x D.KC D.OF c]⟩

/-- **`check_opening_terminal`'s callees, in order**, its buffers from `b0`. -/
noncomputable def termKids (Lin : Main.Layout) (D : TermData) (b0 : ℕ) : List KidD :=
  [fun _ => ⟨"eq_prefix_chain", true,
      [ofK (addressOfIndex b0), word 1 0 0, ofK (addressOfIndex D.B.zeta), ofK (addressOfIndex
          D.B.pt1), D.gmu],
      (b0, eqChain D.zs ((p1Of D.x).take D.zs.length)) :: Lin, Returns []⟩,
    fun _ => ⟨"eq_prefix_chain", true,
      [ofK (addressOfIndex (b0 + 35)), word 1 0 0, ofK (addressOfIndex D.B.chi), ofK (addressOfIndex
          D.B.pt1), D.gzcn],
      (b0 + 35, eqChain D.chis ((p1Of D.x).take D.chis.length)) :: Lin, Returns []⟩,
    fun _ => ⟨"__loop14", decide (word 2 0 0 + D.glm ≠ 0),
      [word 2 0 0, D.glm, ofK (addressOfIndex (b0 + 70)), ofK (addressOfIndex D.B.pt1)],
      (b0 + 70, piW D.rm (p1Of D.x) D.m) :: Lin, Returns []⟩,
    fun _ => ⟨"selector_tables", true, [ofK (addressOfIndex D.B.pt), ofK (addressOfIndex D.B.pt1)],
      Tables.stLin D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x),
      Tables.stOut D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x)⟩] ++
  (List.range Tables.nCommittedCols).map (selKid D) ++
  [fun _ => ⟨"eq_prefix_chain", true,
      [ofK (addressOfIndex (b0 + 105)), word 1 0 0, ofK (addressOfIndex D.B.zv), ofK (addressOfIndex D.B.pt1), D.gtau * word 64 0 0],
      (b0 + 105, eqChain D.outPt ((p1Of D.x).take D.outPt.length)) :: Lin, Returns []⟩,
    fun _ => ⟨"ring_switch_weight", true,
      [ofK (addressOfIndex D.B.zv) * word 549755813888 0 0, ofK (addressOfIndex D.B.pt1), ofK
          (addressOfIndex D.B.ct),
        D.gtau * word 64 0 0],
      [(D.B.zv + 39, D.ringPoint), (D.B.pt1, (p1Of D.x).take (D.τ + 6)), (D.B.ct, D.coeffs)],
      Returns [ringWeight D.ringPoint (((p1Of D.x).take (D.τ + 6)).map (1 + ·)) D.coeffs]⟩]

theorem termKids_length (Lin : Main.Layout) (D : TermData) (b0 : ℕ) :
    (termKids Lin D b0).length = 107 := by
  simp [termKids, Tables.nCommittedCols]

/-! ## Each callee, complete -/

theorem eqc_pure : coreProgram.PureIn ("eq_prefix_chain" :: eqPrefixRunNames) :=
  Tables.pureIn_of_pureInB (by decide +kernel)

theorem l15_pure : coreProgram.PureIn ["__loop14"] := Tables.pureIn_of_pureInB (by decide +kernel)

theorem low_rc {κ : ℕ} (hκ : 6 ≤ κ) {rd : Reader} (hl : LowDef κ rd) {n : ℕ} (hn : n ≤ 40) :
    RangeChecked rd (gen ^ n) (gen ^ 40) := by
  have h40 : 40 < 2 ^ κ := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
  have l1 := hl n (by omega)
  have l2 := hl (40 - n) (by omega)
  have a : ∀ a, (gen ^ a).limb 0 * addressOfIndex 0 = addressOfIndex a := fun a => by
    rw [gen_pow_eq_ofK, Main.addr_ofK, Nat.add_zero]
  obtain ⟨t1, h1⟩ := Option.isSome_iff_exists.mp l1
  obtain ⟨t2, h2⟩ := Option.isSome_iff_exists.mp l2
  exact ⟨gen ^ (40 - n), t1, t2, ⟨gen_pow_isInK n, by rw [a]; exact h1⟩,
    by rw [← pow_add, Nat.add_sub_cancel' hn], ⟨gen_pow_isInK _, by rw [a]; exact h2⟩⟩

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A prefix chain, complete, placed**: on the runs `as` at `g^ba` and `bs` at `g^bb`, its
chain `eqChain as bs` at `g^b`. -/
theorem eqc_kid_complete (κ : ℕ) (hκ : 6 ≤ κ) {b ba bb : ℕ} {as bs : List E} {cg : E}
    {L : Main.Layout} (hn : as.length ≤ 40) (hbs : bs.length = as.length) (hcg : cg = gen ^ as.length)
    (hrd : ∀ rd, LowDef κ rd → MemL rd L → ReadsAt rd (ofK (addressOfIndex ba)) as ∧ ReadsAt rd (ofK (addressOfIndex bb)) bs)
    (hR : ∀ i, (ba ≤ i ∧ i < ba + as.length) ∨ (bb ≤ i ∧ i < bb + as.length) → RegionL L i) :
    CompleteAtD fs cert κ "eq_prefix_chain" ((b, eqChain as bs) :: L)
      [ofK (addressOfIndex b), word 1 0 0, ofK (addressOfIndex ba), ofK (addressOfIndex bb), cg]
          (Returns []) := by
  refine Lift.completeAtD_of_relIn eqc_pure List.mem_cons_self fun rd hl hm => ?_
  have hm0 : ReadsAt rd (ofK (addressOfIndex b)) (eqChain as bs) := hm _ List.mem_cons_self
  have hmL : MemL rd L := fun q hq => hm q (List.mem_cons_of_mem _ hq)
  obtain ⟨ha, hb⟩ := hrd rd hl hmL
  subst hcg
  refine eqc_relIn hn (fun i hi => ?_) ((eq_prefix_chain_holds rd _ _).mpr
    ⟨rfl, low_rc hκ hl hn, as.length, by omega, rfl, as, bs, rfl, hbs, ha, hb, fun j hj => ?_⟩)
  · rcases hi with hi | hi
    · exact regionL_head hi.1 (by rw [eqChain_length]; omega)
    · exact regionL_cons _ (hR i hi)
  · have := hm0 j (by rw [eqChain_length]; omega)
    simpa [eqChain, word_one] using this

/-- **The public input's chain's loop, complete, placed**: from `g`, over the chain `piW` at `g^b`
and the point's complements `ps` at `g^bp`. -/
theorem l15_kid_complete (κ : ℕ) {b bp m : ℕ} {rm glm : E} {ps : List E} {L : Main.Layout}
    (hm2 : 2 ≤ m) (hglm : glm = gen ^ m) (hps : m ≤ ps.length)
    (hrd : ∀ rd, LowDef κ rd → MemL rd L → ReadsAt rd (ofK (addressOfIndex bp)) ps)
    (hR : ∀ i, bp ≤ i ∧ i < bp + m → RegionL L i) :
    CompleteAtD fs cert κ "__loop14" ((b, piW rm ps m) :: L)
      [word 2 0 0, glm, ofK (addressOfIndex b), ofK (addressOfIndex bp)] (Returns []) := by
  refine Lift.completeAtD_of_relIn l15_pure List.mem_cons_self fun rd hl hm => ?_
  have hm0 : ReadsAt rd (ofK (addressOfIndex b)) (piW rm ps m) := hm _ List.mem_cons_self
  have hmL : MemL rd L := fun q hq => hm q (List.mem_cons_of_mem _ hq)
  have hstep : ∀ k, 1 ≤ k → k < m →
      (piW rm ps m).getD (k + 1) 0 = (piW rm ps m).getD k 0 * (ps.take m).getD k 0 := by
    intro k hk1 hkm
    have e : (ps.take m).getD k 0 = ps.getD k 0 := by
      simp [List.getD_eq_getElem?_getD, hkm]
    rw [piW_getD (by omega), piW_getD (by omega), ite_neg' (by omega), ite_neg' (by omega),
      prod_Ico_succ_top (by omega), e, mul_assoc]
  have h := l15_relIn (piW_length rm ps m) (by simp; omega) hm0 (readsAt_take (hrd rd hl hmL) m) hstep
    (R := RegionL ((b, piW rm ps m) :: L)) (fun i hi => by
      rcases hi with hi | hi
      · exact regionL_head hi.1 (by rw [piW_length]; omega)
      · exact regionL_cons _ (hR i hi)) (m - 2) 1 (by omega) le_rfl
  rw [← hglm, pow_one, ← word_gen] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **The terminal's callees are complete, placed**, on the honest data. -/
theorem termKids_complete (κ : ℕ) (hκ : 6 ≤ κ) (Lin : Main.Layout) (D : TermData) (b0 : ℕ)
    (hreg : ∀ i, TermRegion D.B D.zs.length D.chis.length D.τ i → RegionL Lin i)
    (hzl : D.zs.length ≤ 34) (hcl : D.chis.length ≤ 34) (hxl : D.x.length ≤ 32)
    (hτ : D.τ + 6 ≤ 34) (hol : D.outPt.length = D.τ + 6) (hrl : D.ringPoint.length = D.τ + 6)
    (hcf : D.coeffs.length = 64) (hgmu : D.gmu = gen ^ D.zs.length)
    (hgz : D.gzcn = gen ^ D.chis.length) (hglm : D.glm = gen ^ D.m) (hgtau : D.gtau = gen ^ D.τ)
    (hm1 : 1 ≤ D.m) (hm : D.m ≤ 32) (hKC : ∀ c < Tables.nCommittedCols, D.KC.getD c 0 < 33)
    (hOF : ∀ c < Tables.nCommittedCols, D.OF.getD c 0 < 2 ^ 32 ∧ 2 ^ D.KC.getD c 0 ∣ D.OF.getD c 0)
    (hrd : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (addressOfIndex D.B.zeta)) D.zs ∧
      ReadsAt rd (ofK (addressOfIndex D.B.chi)) D.chis ∧ ReadsAt rd (ofK (addressOfIndex D.B.zv))
          D.outPt ∧
      ReadsAt rd (ofK (addressOfIndex D.B.pt1)) (p1Of D.x)) :
    ∀ k ∈ termKids Lin D b0, ∀ pv, (k pv).taken = true →
      CompleteAtD fs cert κ (k pv).f (k pv).Lin (k pv).args (k pv).Out := by
  have hpl : (p1Of D.x).length = 40 := p1Of_length (by simp only [termPointCap]; omega)
  have hpt : (padPoint D.x).length = 40 := padPoint_length (by simp only [termPointCap]; omega)
  have hw64 : word 64 0 0 = gen ^ 6 := word_two_pow (a := 6) (by decide)
  intro k hk pv ht
  simp only [termKids, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hk
  rcases hk with ((rfl | rfl | rfl | rfl) | ⟨c, hc, rfl⟩) | rfl | rfl
  · exact eqc_kid_complete κ hκ (by omega) (by simp; omega) hgmu
      (fun rd hl hm => ⟨(hrd rd hl hm).1, readsAt_take (hrd rd hl hm).2.2.2 _⟩)
      (fun i hi => hreg i (by
        rcases hi with hi | hi
        · exact Or.inl hi
        · simp only [TermRegion]; omega))
  · exact eqc_kid_complete κ hκ (by omega) (by simp; omega) hgz
      (fun rd hl hm => ⟨(hrd rd hl hm).2.1, readsAt_take (hrd rd hl hm).2.2.2 _⟩)
      (fun i hi => hreg i (by simp only [TermRegion]; omega))
  · have hne : word 2 0 0 + D.glm ≠ 0 := by simpa using ht
    have hm2 : 2 ≤ D.m := by
      by_contra h
      apply hne
      rw [hglm, show D.m = 1 by omega, word_gen, pow_one]
      exact e_add_self _
    exact l15_kid_complete κ hm2 hglm (by omega) (fun rd hl hm => (hrd rd hl hm).2.2.2)
      (fun i hi => hreg i (by simp only [TermRegion]; omega))
  · exact Tables.selector_tables_completeAt fs cert κ _ _ _ _ (by simp [pt32]; omega)
      (by simp [pt132]; omega)
  · have hst : Tables.stOut D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x) (stRes pv).1 (stRes pv).2 :=
      @of_decide_eq_true _ (Classical.propDecidable _) ht
    obtain ⟨ese, h1, h2⟩ := hst
    have hL : (selKid D c pv).Lin =
        csLin D.B.pt D.B.pt1 ese (D.B.gsq + 34) (pt32 D.x) (pt132 D.x) := by
      show @ite _ _ (Classical.propDecidable _) _ _ = _
      rw [@ite_pos' _ _ (Classical.propDecidable _) _ _ ⟨ese, h1, h2⟩, h2]; rfl
    have ha : (selKid D c pv).args = [gen ^ D.OF.getD c 0, ofK (addressOfIndex ese), ofK
        (addressOfIndex (D.B.gsq + 34))] := by
      show [_, (stRes pv).1.getD 0 0, _] = _
      rw [h1]; rfl
    rw [hL, ha]
    exact cs_completeAt κ (by omega) (hKC c hc) (hOF c hc).1 (hOF c hc).2 (by simp [pt32]; omega)
      (by simp [pt132]; omega)
  · have e : D.gtau * word 64 0 0 = gen ^ D.outPt.length := by rw [hgtau, hw64, ← pow_add, hol]
    show CompleteAtD fs cert κ "eq_prefix_chain" _
      [ofK (addressOfIndex (b0 + 105)), word 1 0 0, ofK (addressOfIndex D.B.zv), ofK (addressOfIndex D.B.pt1), D.gtau * word 64 0 0]
      (Returns [])
    exact eqc_kid_complete κ hκ (by omega) (by simp; omega) e
      (fun rd hl hm => ⟨(hrd rd hl hm).2.2.1, readsAt_take (hrd rd hl hm).2.2.2 _⟩)
      (fun i hi => hreg i (by simp only [TermRegion]; omega))
  · have e1 : ofK (addressOfIndex D.B.zv) * word 549755813888 0 0 = ofK (addressOfIndex (D.B.zv +
      39)) := by
      rw [show (549755813888 : ℕ) = 2 ^ 39 by norm_num, word_two_pow (by decide), ofK_gpow_mul_gen]
    have e2 : D.gtau * word 64 0 0 = gen ^ (D.τ + 6) := by rw [hgtau, hw64, ← pow_add]
    show CompleteAtD fs cert κ "ring_switch_weight" _
      [ofK (addressOfIndex D.B.zv) * word 549755813888 0 0, ofK (addressOfIndex D.B.pt1), ofK
          (addressOfIndex D.B.ct),
        D.gtau * word 64 0 0] _
    rw [e1, e2]
    exact rsw_completeAt κ (by omega) hrl (by simp; omega) hcf

/-! ## The callees' words -/

/-- The terminal's buffers' honest words. -/
def termOwn (D : TermData) : List (List E) :=
  [eqChain D.zs ((p1Of D.x).take D.zs.length), eqChain D.chis ((p1Of D.x).take D.chis.length),
    piW D.rm (p1Of D.x) D.m, eqChain D.outPt ((p1Of D.x).take D.outPt.length)]

theorem termBuf_eq (D : TermData) (b0 : ℕ) : bufL b0 [35, 35, 35, 41] (termOwn D) =
    [(b0, eqChain D.zs ((p1Of D.x).take D.zs.length)),
      (b0 + 35, eqChain D.chis ((p1Of D.x).take D.chis.length)),
      (b0 + 70, piW D.rm (p1Of D.x) D.m),
      (b0 + 105, eqChain D.outPt ((p1Of D.x).take D.outPt.length))] := by
  simp [bufL, bases, termOwn, Nat.add_assoc]

theorem kid_getD_mem {l : List KidD} {j : ℕ} (h : j < l.length) : l.getD j noKid ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem stRes_take (outs : List (List E × Main.Layout)) (j : ℕ) :
    stRes (outs.take j) = if 3 < j then stRes outs else ([], []) := by
  unfold stRes
  split
  · simp [List.getD_eq_getElem?_getD, *]
  · simp [List.getD_eq_getElem?_getD, *]

theorem stOut_nil {a b : ℕ} {p p1 : List E} : ¬ Tables.stOut a b p p1 [] [] := by
  rintro ⟨_, h, -⟩; simp at h

theorem selKid_taken {D : TermData} {c : ℕ} {outs : List (List E × Main.Layout)} {j : ℕ}
    (ht : (selKid D c (outs.take j)).taken = true) :
    3 < j ∧ stRes (outs.take j) = stRes outs ∧
      Tables.stOut D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x) (stRes outs).1 (stRes outs).2 := by
  have hst : Tables.stOut D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x) (stRes (outs.take j)).1
      (stRes (outs.take j)).2 := @of_decide_eq_true _ (Classical.propDecidable _) ht
  rw [stRes_take] at hst ⊢
  split at hst
  · rename_i h; exact ⟨h, by rw [ite_pos' h], hst⟩
  · exact absurd hst stOut_nil

theorem selKid_lin {D : TermData} {c : ℕ} {outs : List (List E × Main.Layout)} {j : ℕ}
    (ht : (selKid D c (outs.take j)).taken = true) :
    (selKid D c (outs.take j)).Lin =
      (stRes outs).2 ++ Tables.stLin D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x) ++
        [(D.B.gsq + 34, gTabW)] := by
  obtain ⟨-, e, hst⟩ := selKid_taken ht
  show @ite _ _ (Classical.propDecidable _) _ _ = _
  rw [e, @ite_pos' _ _ (Classical.propDecidable _) _ _ hst]

theorem regionL_append {L L' : Main.Layout} {i : ℕ} (h : RegionL (L ++ L') i) :
    RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h⟩
  · exact Or.inr ⟨q, hq, h⟩

theorem regionL_cons_iff {q : ℕ × List E} {L : Main.Layout} {i : ℕ} (h : RegionL (q :: L) i) :
    (q.1 ≤ i ∧ i < q.1 + q.2.length) ∨ RegionL L i := by
  obtain ⟨q', hq, h⟩ := h
  rcases List.mem_cons.mp hq with rfl | hq
  · exact Or.inl h
  · exact Or.inr ⟨q', hq, h⟩

theorem termKid3 (Lin : Main.Layout) (D : TermData) (b0 : ℕ) (outs : List (List E × Main.Layout)) :
    kidAt (termKids Lin D b0) [] outs 3 = ⟨"selector_tables", true,
      [ofK (addressOfIndex D.B.pt), ofK (addressOfIndex D.B.pt1)], Tables.stLin D.B.pt D.B.pt1 (pt32
          D.x) (pt132 D.x),
      Tables.stOut D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x)⟩ := rfl

/-- **The callees read the caller's words, the buffers and `selector_tables`' result.** -/
theorem termKids_regions (Lin : Main.Layout) (D : TermData) (b0 : ℕ)
    (hreg : ∀ i, TermRegion D.B D.zs.length D.chis.length D.τ i → RegionL Lin i)
    (hτ : D.τ + 6 ≤ 34) (hrl : D.ringPoint.length = D.τ + 6) (hcf : D.coeffs.length = 64)
    (hxl : D.x.length ≤ 32) (outs : List (List E × Main.Layout)) :
    RegionsOk (fun i => RegionL Lin i ∨ RegionL (bufL b0 [35, 35, 35, 41] (termOwn D)) i)
      (fun _ => False) (kidsAt (termKids Lin D b0) [] outs) outs := by
  have hpl : (p1Of D.x).length = 40 := p1Of_length (by simp only [termPointCap]; omega)
  have hpt : (padPoint D.x).length = 40 := padPoint_length (by simp only [termPointCap]; omega)
  have hst : ∀ i, RegionL (Tables.stLin D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x)) i → RegionL Lin i := by
    intro i hi
    obtain ⟨q, hq, h⟩ := hi
    simp only [Tables.stLin, List.mem_cons, List.not_mem_nil, or_false] at hq
    refine hreg i ?_
    rcases hq with rfl | rfl
    · simp only [pt32, List.length_take, hpt] at h; simp only [TermRegion]; omega
    · simp only [pt132, List.length_take, hpl] at h; simp only [TermRegion]; omega
  rw [termBuf_eq]
  refine regionsOk_kidsAt _ _ _ _ fun j hj _ ht i hi => ?_
  unfold kidAt at ht hi
  simp only [List.nil_append] at ht hi
  have hmem : (termKids Lin D b0).getD j noKid ∈ termKids Lin D b0 := kid_getD_mem hj
  generalize (termKids Lin D b0).getD j noKid = k at ht hi hmem
  simp only [termKids, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hmem
  have buf : ∀ q, q ∈ [(b0, eqChain D.zs ((p1Of D.x).take D.zs.length)),
      (b0 + 35, eqChain D.chis ((p1Of D.x).take D.chis.length)),
      (b0 + 70, piW D.rm (p1Of D.x) D.m),
      (b0 + 105, eqChain D.outPt ((p1Of D.x).take D.outPt.length))] →
      q.1 ≤ i ∧ i < q.1 + q.2.length → RegionL Lin i ∨ RegionL [(b0, eqChain D.zs ((p1Of D.x).take D.zs.length)),
      (b0 + 35, eqChain D.chis ((p1Of D.x).take D.chis.length)),
      (b0 + 70, piW D.rm (p1Of D.x) D.m),
      (b0 + 105, eqChain D.outPt ((p1Of D.x).take D.outPt.length))] i :=
    fun q hq h => Or.inr ⟨q, hq, h⟩
  rcases hmem with ((rfl | rfl | rfl | rfl) | ⟨c, hc, rfl⟩) | rfl | rfl
  · rcases regionL_cons_iff hi with h | h
    · exact Or.inl (buf _ (by simp) h)
    · exact Or.inl (Or.inl h)
  · rcases regionL_cons_iff hi with h | h
    · exact Or.inl (buf _ (by simp) h)
    · exact Or.inl (Or.inl h)
  · rcases regionL_cons_iff hi with h | h
    · exact Or.inl (buf _ (by simp) h)
    · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inl (hst i hi))
  · obtain ⟨h3, -, -⟩ := selKid_taken ht
    rw [selKid_lin ht] at hi
    rcases regionL_append hi with h | h
    · rcases regionL_append h with h | h
      · refine Or.inr (Or.inr ⟨3, h3, by rw [termKid3], ?_⟩)
        simpa [stRes] using h
      · exact Or.inl (Or.inl (hst i h))
    · refine Or.inl (Or.inl (hreg i ?_))
      obtain ⟨q, hq, h⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      simp only [gTabW_length] at h
      simp only [TermRegion]; omega
  · rcases regionL_cons_iff hi with h | h
    · exact Or.inl (buf _ (by simp) h)
    · exact Or.inl (Or.inl h)
  · refine Or.inl (Or.inl (hreg i ?_))
    obtain ⟨q, hq, h⟩ := hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · simp only [hrl] at h; simp only [TermRegion]; omega
    · simp only [List.length_take, hpl] at h; simp only [TermRegion]; omega
    · simp only [hcf] at h; simp only [TermRegion]; omega

/-- **The callees' words are in memory**, given the caller's, the buffers and the entered callees'
results. -/
theorem termKids_mem (Lin : Main.Layout) (D : TermData) (b0 : ℕ) {rd : Reader}
    (outs : List (List E × Main.Layout))
    (hB : MemL rd (bufL b0 [35, 35, 35, 41] (termOwn D))) (hL : MemL rd Lin)
    (hO : MemL rd (outsL (kidsAt (termKids Lin D b0) [] outs) outs))
    (hst : MemL rd (Tables.stLin D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x)))
    (hgt : MemL rd [(D.B.gsq + 34, gTabW)])
    (hrs : MemL rd [(D.B.zv + 39, D.ringPoint), (D.B.pt1, (p1Of D.x).take (D.τ + 6)),
      (D.B.ct, D.coeffs)]) :
    MemL rd (Kid.lins (kidsAt (termKids Lin D b0) [] outs)) := by
  rw [termBuf_eq] at hB
  refine memL_lins_kidsAt _ _ _ fun j hj ho => ?_
  have hmem : (termKids Lin D b0).getD j noKid ∈ termKids Lin D b0 := kid_getD_mem hj
  have hmem' := hmem
  unfold kidAt
  simp only [List.nil_append]
  generalize (termKids Lin D b0).getD j noKid = k at hmem ⊢
  simp only [termKids, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hmem
  have cons : ∀ q, q ∈ [(b0, eqChain D.zs ((p1Of D.x).take D.zs.length)),
      (b0 + 35, eqChain D.chis ((p1Of D.x).take D.chis.length)),
      (b0 + 70, piW D.rm (p1Of D.x) D.m),
      (b0 + 105, eqChain D.outPt ((p1Of D.x).take D.outPt.length))] → MemL rd (q :: Lin) :=
    fun q hq q' hq' => by
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact hB _ hq
      · exact hL _ hq'
  rcases hmem with ((rfl | rfl | rfl | rfl) | ⟨c, hc, rfl⟩) | rfl | rfl
  · exact cons _ (by simp)
  · exact cons _ (by simp)
  · exact cons _ (by simp)
  · exact hst
  · by_cases ht : (selKid D c (outs.take j)).taken = true
    · rw [selKid_lin ht]
      obtain ⟨h3, -, -⟩ := selKid_taken ht
      have := memL_outsL_at hO 3 (by rw [termKids_length]; omega) (by omega)
        (by rw [termKid3])
      exact Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨by simpa [stRes] using this, hst⟩, hgt⟩
    · have hn : ¬ Tables.stOut D.B.pt D.B.pt1 (pt32 D.x) (pt132 D.x) (stRes (outs.take j)).1
          (stRes (outs.take j)).2 := fun h => ht (@decide_eq_true _ (Classical.propDecidable _) h)
      show MemL rd (@ite _ _ (Classical.propDecidable _) _ _)
      rw [@ite_neg' _ _ (Classical.propDecidable _) _ _ hn]
      intro q hq; simp at hq
  · exact cons _ (by simp)
  · exact hrs

end
end LeanVM.Guest.B1.VerifySub
