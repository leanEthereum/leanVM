/-
  LeanVM.Guest.B1.Whir.CLevelBN

  A level that is not the last, after its grinding check, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CLevelB

/-!
# A level that is not the last, after its grinding check, honestly

`osLevelB_nonfinal_complete`: as `osLevelB_final_complete`, the out-of-domain claim glued with
`λ` before the batch is glued with `β = λ²`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The values of a level's part after its grinding check, at a level that is not the last. -/
def lvBNonF (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) (σ : Val)
    (sqz wp r0 r1 sum ic0 ic2 y oc0 oc2 : E) :
    ℕ → E :=
  let sq := osSqueezes c lvl lv st
  let lam := sq.2.k - 1
  let lp := osLamPow lvl lam lv.queries sq.2.k
  let lamN := lp.2.1
  let s2 : OsSt := { sq.2 with k := lp.2.2 }
  let q := osQueries c lvl lv lam lamN s2
  let s1 : OsSt := { sq.2 with k := q.2.1, w0 := q.2.2.2.1, w1 := q.2.2.2.2.2, co := sq.2.co + 2,
                               mats := osQueriesMats c lv s2 }
  let o := osOodGlue lvl lam s1
  seqF σ st.k sq.2.k (fun i ↦ segLookup (sqzSegs c lv st sqz ⟨st.fsv σ, []⟩) (i - st.k)) fun σ1 ↦
  seqF σ1 sq.2.k s2.k (lamPowVals (σ1 (.n lam)) lv.queries sq.2.k) fun σ2 ↦
  seqF σ2 s2.k q.2.1 (queriesF c lvl lv s2 σ2 wp r0 r1 sum ic0 ic2) fun σ3 ↦
  seqF σ3 q.2.1 o.2.k (fun i ↦ (oodGlueVals σ3 s1 lam y oc0 oc2).getD (i - s1.k) 0) fun σ4 ↦
  seqF σ4 o.2.k (o.2.k + 1) (fun _ ↦ σ4 (.n (s1.k + 12)) * σ4 (.n lamN)) fun σ5 ↦
  fun i ↦ (glueVals σ5 { o.2 with k := o.2.k + 1 } (s1.k + 12) q.2.2.1 q.2.2.2.1 q.2.2.2.2.1
    q.2.2.2.2.2).getD (i - (o.2.k + 1)) 0

/-- **A level that is not the last, after its grinding check, honestly.** -/
theorem osLevelB_nonfinal_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val)
    (hnf : lvl ≠ c.yrLevel)
    (hn0 : 0 < lv.squeezes) (hn5 : lv.squeezes * 5 < u128Bound)
    (hfs : st.fs.length = 5) (hb : st.Below) (hk : 164 ≤ st.k) (hcan : AllCanonical (st.fsv σ))
    (hpad : PadOk σ st.pad) (hpk : ∀ p, st.pad = some p → p + 4 < st.k)
    (hmo : MatsOk σ st.mats) (hmob : MatsBelow st.k st.mats)
    (sqz : E) (h0 : ∀ i < 5, LoadHolds rd sqz i ((st.fsv σ).getD i 0))
    (hm : ∀ j < lv.squeezes, SqNextMem rd sqz (gen ^ j) ((⟨st.fsv σ, []⟩ : Fs).squeezeN j).2.cap)
    (hL : IsInK (1 + gen ^ lv.squeezes) ∧ (1 + gen ^ lv.squeezes ≠ 0 →
      C (c.sqLoop lvl) [1, gen ^ lv.squeezes, sqz, σ (.n osQpos), σ (.n osQbp), σ (.n osWin)] []))
    (hqd : digitsVal (osPowDigits lv.queries) 1 = lv.queries)
    (hl0 : ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 ≠ 0)
    (hmu : LoadHolds rd (σ (.n osMus)) lvl ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1⁻¹)
    (hbo : lv.foldsOff < u128Bound ∧ 4 * lv.capOff < u128Bound ∧ lv.capOff < u128Bound ∧
      lv.posOff < u128Bound ∧ lv.queries / (1 + if lvl = 0 then 1 else 0) < u128Bound)
    (wp r0 r1 sum ic0 ic2 : E)
    (hRW : C ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
      [σ (.n osFch) * gen ^ lv.foldsOff, wp] [])
    (hCap : C ("verify_merkle_cap__L" ++ natStr lv.capDepth)
      [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff] [r0, r1])
    (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) r0)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) r1)
    (hQ : C (osQueriesName lvl lv) [σ (.n osCaps) * gen ^ (4 * lv.capOff),
      σ (.n osFlags) * gen ^ lv.capOff, ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1, ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 ^ lv.queries,
      σ (.n osQbp) * gen ^ lv.posOff, wp,
      gen ^ (lv.queries / (1 + if lvl = 0 then 1 else 0))] [sum])
    (hi0 : LoadHolds rd (σ (.n st.cb)) st.co ic0) (hi2 : LoadHolds rd (σ (.n st.cb)) (st.co + 1) ic2)
    {y oc0 oc2 : E}
    (hy : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 1) y)
    (hc0 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 2) oc0)
    (hc2 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 3) oc2)
    (hlo : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots) ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1)
    (hbeta : LoadHolds rd (σ (.n osBetas)) lvl (((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 ^ lv.queries)) :
    BlkF C rd σ st.k (osLevelB c lvl lv st).2.k
      (lvBNonF c lvl lv st σ sqz wp r0 r1 sum ic0 ic2 y oc0 oc2)
      (osLevelB c lvl lv st).1
      (fun σ' ↦ LvBOut σ' st (osLevelB c lvl lv st).2
        ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2 ic0 ic2
        [σ (.n st.c) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * oc0 + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ic0,
          σ (.n st.b) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * (y + oc2) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * (sum + ic2),
          σ (.n st.a) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * oc2 + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ic2]
        (σ (.n st.t) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * y + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * sum) ∧
        AgreeBelow st.k σ σ') := by
  obtain ⟨hb1, hb2, hb3, hb4, hb6⟩ := hbo
  unfold lvBNonF
  set Fq := ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2 with hFq
  set lv0 := Fq.squeeze.1 with hlv0
  set sq := osSqueezes c lvl lv st with hsq
  set K1 := sq.2.k with hK1
  set lam := K1 - 1 with hlam
  set lp := osLamPow lvl lam lv.queries K1 with hlp
  set lamN := lp.2.1 with hlamN
  set s2 : OsSt := { sq.2 with k := lp.2.2 } with hs2
  set q := osQueries c lvl lv lam lamN s2 with hq
  set s1 : OsSt := { sq.2 with k := q.2.1, w0 := q.2.2.2.1, w1 := q.2.2.2.2.2, co := sq.2.co + 2,
                               mats := osQueriesMats c lv s2 } with hs1
  set o := osOodGlue lvl lam s1 with ho
  set o' : OsSt := { o.2 with k := o.2.k + 1 } with ho'
  set gl := osGlue (s1.k + 12) q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 o' with hgl
  have hc : (lvl = c.yrLevel) = False := eq_false hnf
  have e : osLevelB c lvl lv st = (sq.1 ++ (lp.1 ++ (q.1 ++ (o.1 ++
      ([.atom (.mul (.n o.2.k) (.n (s1.k + 12)) (.n lamN)), .atom (.load (.n o.2.k) (.n osBetas) lvl)] ++
        gl.1)))), gl.2) := by
    rw [osLevelB_eq]
    simp only [hc, ↓reduceIte, List.append_assoc]
    rfl
  rw [e]
  dsimp only
  obtain ⟨g, hqr, hqk⟩ := osQueries_rets c lvl lv lam lamN s2
  have hKs : st.k + 34 ≤ K1 := by
    show st.k + 34 ≤ (osPad st.pad (st.k + 14)).2.2 + 20
    have := osPad_next st.pad (st.k + 14); omega
  have hs2k : s2.k = K1 + osPowLen lv.queries + 2 := rfl
  have hlNlt : lamN < K1 + osPowLen lv.queries := osLamPow_lt (by omega)
  have eq1 : q.2.1 = g + 5 := by rw [hqr]
  have eq2 : q.2.2.1 = g + 1 := by rw [hqr]
  have eq3 : q.2.2.2.1 = g + 2 := by rw [hqr]
  have eq4 : q.2.2.2.2.1 = g + 4 := by rw [hqr]
  have eq5 : q.2.2.2.2.2 = g + 3 := by rw [hqr]
  have hs1k : s1.k = q.2.1 := rfl
  have ho2k : o.2.k = q.2.1 + 13 := rfl
  have hend : gl.2.k = g + 27 := by
    show q.2.1 + 13 + 1 + 8 = g + 27
    rw [eq1]
  -- the squeezes
  have hA := osSqueezes_completeC (C := C) (rd := rd) (c := c) (lvl := lvl) (lv := lv) σ hn0 hn5 hfs
    hb hk hcan hpad hpk sqz h0 hm hL
  refine BlkF.then (k1 := K1) (k2 := gl.2.k) (by omega) (by rw [hend]; omega) hA
    fun σ1 ha1 ⟨so, ha1'⟩ ↦ ?_
  have hb1' := so.below
  have el1 : σ1 (.n lam) = lv0 := so.lam
  have hmu1 : σ1 (.n osMus) = σ (.n osMus) := ha1' _ (by unfold osMus; omega)
  -- λ^n and μ
  have hB := osLamPow_complete (C := C) (rd := rd) (lvl := lvl) (lam := lam) (n := lv.queries)
    (k := K1) hqd σ1 (by omega) (by unfold osMus; omega) (by rw [el1]; exact hl0)
    (by rw [hmu1, el1]; exact hmu)
  refine BlkF.then (k1 := s2.k) (k2 := gl.2.k) (by omega) (by rw [hend]; omega) hB
    fun σ2 ha2 ⟨hlN, ha2'⟩ ↦ ?_
  -- the queries
  have hK1le : K1 ≤ s2.k := by rw [hs2k]; omega
  have hs2b : s2.Below :=
    ⟨fun f hf ↦ Nat.lt_of_lt_of_le (hb1'.fs f hf) hK1le, Nat.lt_of_lt_of_le hb1'.w0 hK1le,
      Nat.lt_of_lt_of_le hb1'.w1 hK1le, Nat.lt_of_lt_of_le hb1'.cb hK1le,
      Nat.lt_of_lt_of_le hb1'.c hK1le, Nat.lt_of_lt_of_le hb1'.b hK1le,
      Nat.lt_of_lt_of_le hb1'.a hK1le, Nat.lt_of_lt_of_le hb1'.t hK1le⟩
  have hag12 : AgreeBelow st.k σ σ2 := fun i hi ↦ (ha2' i (by omega)).trans (ha1' i hi)
  have e2 : ∀ v, v < st.k → σ2 (.n v) = σ (.n v) := fun v hv ↦ hag12 v hv
  have el2 : σ2 (.n lam) = lv0 := (ha2' lam (by omega)).trans el1
  have elN2 : σ2 (.n lamN) = lv0 ^ lv.queries := by rw [hlN, el1]
  have hcb2 : σ2 (.n s2.cb) = σ (.n st.cb) := by
    rw [show s2.cb = st.cb from so.cb]; exact e2 _ hb.cb
  have hm2 : MatsOk σ2 s2.mats := matsOk_agree hmo hmob hag12
  have hmb2 : MatsBelow s2.k s2.mats := matsBelow_mono hmob (by rw [hs2k]; omega)
  have hC := osQueries_complete (C := C) (rd := rd) (c := c) (lvl := lvl) (lv := lv) (lam := lam)
    (lamN := lamN) (s := s2) σ2 hs2b (by rw [hs2k]; omega) (by rw [hs2k]; omega)
    (by rw [hs2k]; omega) hm2 hmb2 ⟨hb1, hb2, hb3, hb4, hb6⟩ wp r0 r1 sum ic0 ic2
    (by rw [e2 osFch (by unfold osFch; omega)]; exact hRW)
    (by rw [e2 osCaps (by unfold osCaps; omega), e2 osFlags (by unfold osFlags; omega)]; exact hCap)
    (by rw [e2 osRoots (by unfold osRoots; omega)]; exact hr0)
    (by rw [e2 osRoots (by unfold osRoots; omega)]; exact hr1)
    (by rw [e2 osCaps (by unfold osCaps; omega), e2 osFlags (by unfold osFlags; omega),
          e2 osQbp (by unfold osQbp; omega), el2, elN2]; exact hQ)
    (by rw [hcb2, show s2.co = st.co from so.co]; exact hi0)
    (by rw [hcb2, show s2.co = st.co from so.co]; exact hi2)
  have hqk' : s2.k + 2 ≤ g := hqk
  refine BlkF.then (k1 := q.2.1) (k2 := gl.2.k) (by rw [eq1]; omega) (by rw [hend, eq1]; omega)
    hC fun σ3 ha3 ⟨q1, q2, q3, q4, ha3', qm, qmb⟩ ↦ ?_
  have bfs : ∀ f ∈ sq.2.fs, f < K1 := hb1'.fs
  have bc : sq.2.c < K1 := hb1'.c
  have bb : sq.2.b < K1 := hb1'.b
  have ba : sq.2.a < K1 := hb1'.a
  have bt : sq.2.t < K1 := hb1'.t
  have bcb : sq.2.cb < K1 := hb1'.cb
  have hs1b : s1.Below :=
    ⟨fun f hf ↦ by show f < q.2.1; have := bfs f hf; rw [eq1]; omega,
      by show q.2.2.2.1 < q.2.1; rw [eq1, eq3]; omega,
      by show q.2.2.2.2.2 < q.2.1; rw [eq1, eq5]; omega,
      by show sq.2.cb < q.2.1; rw [eq1]; omega,
      by show sq.2.c < q.2.1; rw [eq1]; omega,
      by show sq.2.b < q.2.1; rw [eq1]; omega,
      by show sq.2.a < q.2.1; rw [eq1]; omega,
      by show sq.2.t < q.2.1; rw [eq1]; omega⟩
  have hag13 : AgreeBelow st.k σ σ3 := fun i hi ↦ (ha3' i (by omega)).trans (hag12 i hi)
  have el3 : σ3 (.n lam) = lv0 := (ha3' lam (by omega)).trans el2
  have elN3 : σ3 (.n lamN) = lv0 ^ lv.queries := (ha3' lamN (by omega)).trans elN2
  -- the out-of-domain glue
  have eO : σ3 (.n osOod) = σ (.n osOod) := hag13 osOod (by unfold osOod; omega)
  have hO := osOodGlue_complete (C := C) (rd := rd) (lvl := lvl) (lam := lam) (s := s1) σ3 hs1b
    (by rw [hs1k, eq1]; omega) (by rw [hs1k, eq1]; omega) (y := y) (c0 := oc0) (c2 := oc2)
    (by rw [eO]; exact hy) (by rw [eO]; exact hc0) (by rw [eO]; exact hc2)
    (by rw [eO, el3]; exact hlo)
  refine BlkF.then (k1 := o.2.k) (k2 := gl.2.k) (by rw [ho2k]; omega) (by rw [hend, ho2k, eq1]; omega)
    hO fun σ4 ha4 ⟨oq, ot, ol2, ob, ha4'⟩ ↦ ?_
  have tr4 : ∀ i, i < q.2.1 → σ4 (.n i) = σ3 (.n i) := fun i hi ↦ ha4' i hi
  have hag14 : AgreeBelow st.k σ σ4 := fun i hi ↦ (tr4 i (by rw [eq1]; omega)).trans (hag13 i hi)
  rw [el3] at oq ot ol2
  simp only [OsSt.quad, List.cons.injEq, and_true] at oq
  obtain ⟨oc, obb, oa⟩ := oq
  -- the batching scalar
  have hBe := osBeta_complete (C := C) (rd := rd) (σ := σ4) (bk := o.2.k) (beta := s1.k + 12)
    (lamN := lamN) (lvl := lvl) (by rw [ho2k, hs1k]; omega) (by rw [ho2k, eq1]; omega)
    (by rw [ho2k, eq1]; unfold osBetas; omega)
    (by rw [hag14 osBetas (by unfold osBetas; omega), ol2, tr4 lamN (by rw [eq1]; omega), elN3]
        exact hbeta)
  refine BlkF.then (k1 := o.2.k + 1) (k2 := gl.2.k) (by omega) (by rw [hend, ho2k, eq1]; omega)
    hBe fun σ5 ha5 ha5' ↦ ?_
  -- the glue
  have hob : o'.Below :=
    ⟨fun f hf ↦ Nat.lt_succ_of_lt (ob.fs f hf), Nat.lt_succ_of_lt ob.w0, Nat.lt_succ_of_lt ob.w1,
      Nat.lt_succ_of_lt ob.cb, Nat.lt_succ_of_lt ob.c, Nat.lt_succ_of_lt ob.b,
      Nat.lt_succ_of_lt ob.a, Nat.lt_succ_of_lt ob.t⟩
  have hD := osGlue_complete (C := C) (rd := rd) (beta := s1.k + 12) (v := q.2.2.1) (c0 := q.2.2.2.1)
    (c1 := q.2.2.2.2.1) (c2 := q.2.2.2.2.2) (s := o') σ5 hob
    (by show _ < o.2.k + 1 ∧ _ < o.2.k + 1 ∧ _ < o.2.k + 1 ∧ _ < o.2.k + 1 ∧ _ < o.2.k + 1
        rw [ho2k, hs1k, eq1, eq2, eq3, eq4, eq5]
        refine ⟨by omega, by omega, by omega, by omega, by omega⟩)
  have tr5 : ∀ i, i < o.2.k → σ5 (.n i) = σ4 (.n i) := fun i hi ↦ ha5' i hi
  have tr3' : ∀ i, i < q.2.1 → ∀ σ', AgreeBelow o'.k σ5 σ' → σ' (.n i) = σ3 (.n i) :=
    fun i hi σ' ha6 ↦ (ha6 i (by show i < o.2.k + 1; rw [ho2k]; omega)).trans
      ((tr5 i (by rw [ho2k]; omega)).trans (tr4 i hi))
  have tr : ∀ i, i < K1 → ∀ σ', AgreeBelow o'.k σ5 σ' → σ' (.n i) = σ1 (.n i) := fun i hi σ' ha6 ↦
    (tr3' i (by rw [eq1]; omega) σ' ha6).trans ((ha3' i (by omega)).trans (ha2' i hi))
  have hfsv' : ∀ σ', AgreeBelow o'.k σ5 σ' → o'.fsv σ' = sq.2.fsv σ1 := fun σ' ha6 ↦ by
    show sq.2.fs.map (fun i ↦ σ' (.n i)) = sq.2.fs.map (fun i ↦ σ1 (.n i))
    exact List.map_congr_left fun f hf ↦ tr f (bfs f hf) σ' ha6
  have e5 : ∀ i, i < q.2.1 → σ5 (.n i) = σ3 (.n i) := fun i hi ↦
    (tr5 i (by rw [ho2k]; omega)).trans (tr4 i hi)
  have q1' : σ5 (.n q.2.2.1) = sum := by rw [e5 _ (by rw [eq1, eq2]; omega), q1]
  have q2' : σ5 (.n q.2.2.2.1) = ic0 := by rw [e5 _ (by rw [eq1, eq3]; omega), q2]
  have q3' : σ5 (.n q.2.2.2.2.2) = ic2 := by rw [e5 _ (by rw [eq1, eq5]; omega), q3]
  have q4' : σ5 (.n q.2.2.2.2.1) = sum + ic2 := by rw [e5 _ (by rw [eq1, eq4]; omega), q4]
  have ol5 : σ5 (.n (s1.k + 12)) = lv0 * lv0 := by
    rw [tr5 _ (by rw [ho2k, hs1k]; omega), ol2]
  have oc5 : σ5 (.n o'.c) = σ3 (.n s1.c) + lv0 * oc0 := by
    rw [tr5 _ (by show s1.k + 4 < s1.k + 13; omega)]; exact oc
  have ob5 : σ5 (.n o'.b) = σ3 (.n s1.b) + lv0 * (y + oc2) := by
    rw [tr5 _ (by show s1.k + 7 < s1.k + 13; omega)]; exact obb
  have oa5 : σ5 (.n o'.a) = σ3 (.n s1.a) + lv0 * oc2 := by
    rw [tr5 _ (by show s1.k + 9 < s1.k + 13; omega)]; exact oa
  have ot5 : σ5 (.n o'.t) = σ3 (.n s1.t) + lv0 * y := by
    rw [tr5 _ (by show s1.k + 11 < s1.k + 13; omega)]; exact ot
  refine BlkF.mono hD fun σ' ⟨gq, gt, gb, ha6⟩ ↦
    ⟨⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, so.fs, ?_, gb, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (hfsv' σ' ha6).trans so.fsv
  · show σ' (.n q.2.2.2.1) = ic0
    rw [tr3' _ (by rw [eq1, eq3]; omega) σ' ha6, q2]
  · show σ' (.n q.2.2.2.2.2) = ic2
    rw [tr3' _ (by rw [eq1, eq5]; omega) σ' ha6, q3]
  · rw [gq, ol5, q2', q4', q3', oc5, ob5, oa5]
    have ec : σ3 (.n s1.c) = σ (.n st.c) := hag13 _ hb.c
    have eb : σ3 (.n s1.b) = σ (.n st.b) := hag13 _ hb.b
    have ea : σ3 (.n s1.a) = σ (.n st.a) := hag13 _ hb.a
    rw [ec, eb, ea]
  · rw [gt, ol5, q1', ot5]
    have et : σ3 (.n s1.t) = σ (.n st.t) := hag13 _ hb.t
    rw [et]
  · show sq.2.co + 2 = st.co + 2
    rw [so.co]
  · show AllCanonical (o'.fsv σ')
    rw [hfsv' σ' ha6]; exact so.can
  · obtain ⟨p, hp, hp4⟩ := so.padSome
    have hp4' : p + 4 < K1 := hp4
    have hpo := so.pad
    rw [hp] at hpo
    show PadOk σ' sq.2.pad
    rw [hp]
    obtain ⟨z1, z2, z3, z4⟩ := hpo
    exact ⟨by rw [tr _ (by omega) σ' ha6]; exact z1, by rw [tr _ (by omega) σ' ha6]; exact z2,
      by rw [tr _ (by omega) σ' ha6]; exact z3, by rw [tr _ (by omega) σ' ha6]; exact z4⟩
  · obtain ⟨p, hp, hp4⟩ := so.padSome
    have hp4' : p + 4 < K1 := hp4
    refine ⟨p, hp, ?_⟩
    rw [hend]; omega
  · rw [hend]; omega
  · show MatsOk σ' (osQueriesMats c lv s2)
    exact matsOk_agree qm qmb fun i hi ↦ tr3' i hi σ' ha6
  · show MatsBelow gl.2.k (osQueriesMats c lv s2)
    exact matsBelow_mono qmb (by rw [hend, eq1]; omega)
  · intro i hi
    exact (tr3' i (by rw [eq1]; omega) σ' ha6).trans (hag13 i hi)

/-- A level's part after its grinding check ends past its start. -/
theorem osLevelB_k_le (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) :
    st.k ≤ (osLevelB c lvl lv st).2.k := by
  obtain ⟨g, hg, hgk⟩ := osQueries_rets c lvl lv (bLam c lvl lv st) (bLamN c lvl lv st)
    { bSq c lvl lv st with k := (bLp c lvl lv st).2.2 }
  have hd := osPad_next st.pad (st.k + 14)
  have h1 : (bSq c lvl lv st).k = (osPad st.pad (st.k + 14)).2.2 + 20 := rfl
  have h2 : (bLp c lvl lv st).2.2 = (bSq c lvl lv st).k + osPowLen lv.queries + 2 := rfl
  have h3 : (bQ c lvl lv st).2.1 = g + 5 := by rw [hg]
  simp only at hgk
  rw [osLevelB_eq]
  split_ifs
  · show st.k ≤ (bQ c lvl lv st).2.1 + 1 + 8
    omega
  · show st.k ≤ (bQ c lvl lv st).2.1 + 13 + 1 + 8
    omega

end
end LeanVM.Guest.B1.Whir
