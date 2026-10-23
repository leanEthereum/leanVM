/-
  LeanVM.Guest.B1.Whir.StackedC7

  A level of `open_stacked` at its honest values: its positions, query weights, queries and glue.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC6

/-!
# A level, honestly: the second part (TRIAGE #36)

`osLevelB_complete`: after the nonce, the positions' squeezes, the query weights, the queries, the
out-of-domain claim's glue, the stored scalar and the queries' glue hold at the values `osLvValsB`,
and the guest's state after them is at the specification's (`osHWEnd`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The pointers of `open_stacked`'s fixed buffers. -/
structure OsPtrs where
  caps : E
  flags : E
  fmsg : E
  roots : E
  fch : E
  betas : E
  qw : E
  qpos : E
  qbp : E
  oodz : E
  ood : E

/-- The fixed buffers' pointers at their values. -/
structure OsPtrsAt (σ : Val) (P : OsPtrs) : Prop where
  caps : σ (.n osCaps) = P.caps
  flags : σ (.n osFlags) = P.flags
  fmsg : σ (.n osFmsg) = P.fmsg
  roots : σ (.n osRoots) = P.roots
  fch : σ (.n osFch) = P.fch
  betas : σ (.n osBetas) = P.betas
  qw : σ (.n osQw) = P.qw
  qpos : σ (.n osQpos) = P.qpos
  qbp : σ (.n osQbp) = P.qbp
  oodz : σ (.n osOodz) = P.oodz
  ood : σ (.n osOod) = P.ood

/-- The positions' squeezes after the nonce. -/
def osLvSq (cfg : OsCfg) (lvl : ℕ) (sg : OsSt) : List Stmt × OsSt :=
  osSqueezes cfg.maxSq (cfg.lv lvl).squeezes osQpos osQbp (cfg.lv lvl).sqLoop sg

/-- The query weights. -/
def osLvL (cfg : OsCfg) (lvl : ℕ) (sg : OsSt) : List Stmt :=
  osLamPows ((osLvSq cfg lvl sg).2.k - 1) osQw (lvl * cfg.maxQ) (osLvSq cfg lvl sg).2.k (cfg.lv lvl).queries

/-- The queries. -/
def osLvQ (cfg : OsCfg) (lvl : ℕ) (sg : OsSt) : List Stmt × OsSt × ℕ × ℕ × ℕ × ℕ :=
  osQueries cfg (cfg.lv lvl) lvl { (osLvSq cfg lvl sg).2 with k := (osLvSq cfg lvl sg).2.k + (cfg.lv lvl).queries }

/-- The out-of-domain claim's glue (none at the last level), the scalar of the queries' claim. -/
def osLvO (cfg : OsCfg) (lvl : ℕ) (sg : OsSt) : List Stmt × OsSt × ℕ :=
  if lvl = cfg.yrLevel then (([] : List Stmt), (osLvQ cfg lvl sg).2.1, (osLvSq cfg lvl sg).2.k - 1)
  else osOodGlues lvl ((osLvSq cfg lvl sg).2.k - 1) 0 (cfg.lv lvl).oodNext ((osLvSq cfg lvl sg).2.k - 1)
    (osLvQ cfg lvl sg).2.1

/-- The queries' glue. -/
def osLvGl (cfg : OsCfg) (lvl : ℕ) (sg : OsSt) : List Stmt × OsSt :=
  osGlue (osLvO cfg lvl sg).2.2 (osLvQ cfg lvl sg).2.2.1 (osLvQ cfg lvl sg).2.2.2.1 (osLvQ cfg lvl sg).2.2.2.2.1
    (osLvQ cfg lvl sg).2.2.2.2.2 (osLvO cfg lvl sg).2.1

/-- The statements of the level's second part. -/
def osLvStB (cfg : OsCfg) (lvl : ℕ) (sg : OsSt) : List Stmt :=
  (osLvSq cfg lvl sg).1 ++ osLvL cfg lvl sg ++ (osLvQ cfg lvl sg).1 ++ (osLvO cfg lvl sg).1 ++
    [.atom (.load (.n (osLvO cfg lvl sg).2.2) (.n osBetas) lvl)] ++ (osLvGl cfg lvl sg).1

/-- The second part after the positions' squeezes. -/
def osLvRestB (cfg : OsCfg) (lvl : ℕ) (sg : OsSt) : List Stmt :=
  osLvL cfg lvl sg ++ (osLvQ cfg lvl sg).1 ++ (osLvO cfg lvl sg).1 ++
    [.atom (.load (.n (osLvO cfg lvl sg).2.2) (.n osBetas) lvl)] ++ (osLvGl cfg lvl sg).1

theorem osLvStB_eq (cfg : OsCfg) (lvl : ℕ) (sg : OsSt) :
    osLvStB cfg lvl sg = (osLvSq cfg lvl sg).1 ++ osLvRestB cfg lvl sg := by
  simp only [osLvStB, osLvRestB, List.append_assoc]

/-- The values a level's second part allocates and enters its loop with: the squeezes' buffer, its
size, the loop's guard, the row weights' buffer and its size. -/
structure OsLvSig (σ : Val) (cfg : OsCfg) (lvl : ℕ) (sg : OsSt) (sqzv rewv : E) : Prop where
  sqSize : σ (.n sg.k) = osGw (2 * (cfg.maxSq + 1))
  sqPtr : σ (.n (sg.k + 1)) = sqzv
  guard : σ (.n (sg.k + 4)) = 1 + osGw (cfg.lv lvl).squeezes
  one : σ (.n (sg.k + 5)) = 1
  count : σ (.n (sg.k + 6)) = osGw (cfg.lv lvl).squeezes
  rwSize : σ (.n ((osLvSq cfg lvl sg).2.k + (cfg.lv lvl).queries)) = osGw cfg.maxIl
  rwPtr : σ (.n ((osLvSq cfg lvl sg).2.k + (cfg.lv lvl).queries + 1)) = rewv

/-- The level, in its two parts. -/
theorem osLevel_parts (cfg : OsCfg) (lvl : ℕ) (s : OsSt) :
    osLevel cfg lvl (cfg.lv lvl) s = ((osLvF cfg lvl s).1 ++ (osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1 ++
      osLvStB cfg lvl (osLvG cfg lvl s).2, (osLvGl cfg lvl (osLvG cfg lvl s).2).2) := by
  simp only [osLevel, osLvStB, osLvF, osLvM, osLvG, osLvSq, osLvL, osLvQ, osLvO, osLvGl, List.append_assoc]

/-- The values of the level's second part from its first. -/
def osLvValsB (cfg : OsCfg) (lvl : ℕ) (xs : List E) (p : ℕ) (H : OsLvH) (rt : Digest) (P : OsPtrs)
    (sqzv rewv : E) : List E :=
  let lv := cfg.lv lvl
  let lam := osHLam cfg lvl xs p H.cv1
  let enf := osHEnf cfg lvl xs p H
  let c0 := osHC cfg lvl xs p 0
  let c2 := osHC cfg lvl xs p 1
  let q0 := H.w1.quad.getD 0 0
  let q1 := H.w1.quad.getD 1 0
  let q2 := H.w1.quad.getD 2 0
  let t := H.w1.target
  let y := osHW cfg lvl xs p 2
  let c0o := osHW cfg lvl xs p 3
  let c2o := osHW cfg lvl xs p 4
  osSqueezesVals cfg.maxSq lv.squeezes sqzv (osHCv3 cfg lvl xs p H.cv1) ++
    (osLamPowsVals lam lv.queries).take lv.queries ++
    (osQueriesSegs cfg lv lvl rewv P.fch P.caps P.flags P.qw P.qbp rt enf c0 c2
      (sqCv (osHCv4 cfg lvl xs p H.cv1))).flatten ++
    (if lvl = cfg.yrLevel then osGlueVals lam enf c0 (enf + c2) c2 q0 q1 q2 t
    else osOodGlueVals y c0o c2o lam lam q0 q1 q2 t ++
      osGlueVals (lam * lam) enf c0 (enf + c2) c2 (q0 + lam * c0o) (q1 + lam * (y + c2o)) (q2 + lam * c2o)
        (t + lam * y))

theorem os_look_app {k : ℕ} {A B : List E}
    (hv : ∀ j < (A ++ B).length, σ (.n (k + j)) = (A ++ B).getD j 0) :
    (∀ j < A.length, σ (.n (k + j)) = A.getD j 0) ∧
      ∀ j < B.length, σ (.n (k + A.length + j)) = B.getD j 0 :=
  ⟨fun j hj => by rw [hv j (by simp; omega), oq_getD_app_lt hj],
    fun j hj => by rw [Nat.add_assoc, hv _ (by simp; omega), os_skip]⟩

/-- **A level's second part** at its honest values (G:1144-1213). -/
theorem osLevelB_complete {cfg : OsCfg} {μ lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg μ lvl L rest) {xs : List E} {p : ℕ} {H : OsLvH} {rt : Digest} {P : OsPtrs}
    {sqzv rewv cur : E} {sg : OsSt} (hP : OsPtrsAt σ P)
    (hat : OsAt σ sg (osHCv3 cfg lvl xs p H.cv1) cur (osHP2 cfg lvl p + 1))
    (hqd : H.w1.quad = [σ (.n sg.c), σ (.n sg.b), σ (.n sg.a)]) (htg : H.w1.target = σ (.n sg.t))
    (hc0 : LoadHolds rd cur (osHP2 cfg lvl p + 1) (osHC cfg lvl xs p 0))
    (hc2 : LoadHolds rd cur (osHP2 cfg lvl p + 1 + 1) (osHC cfg lvl xs p 1))
    (l0 : LoadHolds rd sqzv 0 (digestScalars (osHCv3 cfg lvl xs p H.cv1)).1)
    (l1 : LoadHolds rd sqzv 1 (digestScalars (osHCv3 cfg lvl xs p H.cv1)).2)
    (l2 : LoadHolds rd sqzv (2 * (cfg.lv lvl).squeezes) (digestScalars (osHCv4 cfg lvl xs p H.cv1)).1)
    (l3 : LoadHolds rd sqzv (2 * (cfg.lv lvl).squeezes + 1) (digestScalars (osHCv4 cfg lvl xs p H.cv1)).2)
    (hqw : ∀ i < (cfg.lv lvl).queries,
      LoadHolds rd P.qw (lvl * cfg.maxQ + i) (osHLam cfg lvl xs p H.cv1 ^ i))
    (sr0 : LoadHolds rd P.roots (2 * lvl) (digestScalars rt).1)
    (sr1 : LoadHolds rd P.roots (2 * lvl + 1) (digestScalars rt).2)
    (hood : lvl ≠ cfg.yrLevel → LoadHolds rd P.ood ((lvl + 1) * 4) (osHLam cfg lvl xs p H.cv1) ∧
      LoadHolds rd P.ood ((lvl + 1) * 4 + 1) (osHW cfg lvl xs p 2) ∧
      LoadHolds rd P.ood ((lvl + 1) * 4 + 2) (osHW cfg lvl xs p 3) ∧
      LoadHolds rd P.ood ((lvl + 1) * 4 + 3) (osHW cfg lvl xs p 4))
    (hbeta : LoadHolds rd P.betas lvl (if lvl = cfg.yrLevel then osHLam cfg lvl xs p H.cv1
      else osHLam cfg lvl xs p H.cv1 * osHLam cfg lvl xs p H.cv1))
    {kret : List E → Prop} {Csq : CallRel}
    (hcsq : 1 + osGw (cfg.lv lvl).squeezes ≠ 0 →
      Csq (cfg.lv lvl).sqLoop [1, osGw (cfg.lv lvl).squeezes, sqzv, P.qpos, P.qbp] [])
    (hcrw : C (cfg.lv lvl).rowWeights [P.fch * gen ^ (cfg.lv lvl).foldsOff, rewv] [])
    (hccap : C (cfg.lv lvl).verifyCap [P.caps * gen ^ (4 * (cfg.lv lvl).capOff), P.flags * gen ^ (cfg.lv lvl).capOff]
      [(digestScalars rt).1, (digestScalars rt).2])
    (hcq : C (cfg.lv lvl).queriesFn [P.caps * gen ^ (4 * (cfg.lv lvl).capOff), P.flags * gen ^ (cfg.lv lvl).capOff,
      P.qw * gen ^ (lvl * cfg.maxQ), P.qbp * gen ^ (cfg.lv lvl).posOff, rewv, osGw (cfg.lv lvl).queries]
      [osHEnf cfg lvl xs p H])
    (hv : ∀ j < (osLvValsB cfg lvl xs p H rt P sqzv rewv).length,
      σ (.n (sg.k + j)) = (osLvValsB cfg lvl xs p H rt P sqzv rewv).getD j 0) :
    (Stmt.HoldsList Csq rd σ (osLvSq cfg lvl sg).1 True kret ∧ Stmt.HoldsList C rd σ (osLvRestB cfg lvl sg) True kret ∧
      OsLvSig σ cfg lvl sg sqzv rewv) ∧
      OsAt σ (osLvGl cfg lvl sg).2 (osHCvEnd cfg lvl xs p H.cv1) cur (osHPEnd cfg lvl p) ∧
      (osLvGl cfg lvl sg).2.co = sg.co + 2 ∧
      (osHWEnd cfg lvl xs p H).quad = [σ (.n (osLvGl cfg lvl sg).2.c), σ (.n (osLvGl cfg lvl sg).2.b),
        σ (.n (osLvGl cfg lvl sg).2.a)] ∧
      (osHWEnd cfg lvl xs p H).target = σ (.n (osLvGl cfg lvl sg).2.t) ∧
      (osLvGl cfg lvl sg).2.k = sg.k + (osLvValsB cfg lvl xs p H rt P sqzv rewv).length := by
  obtain ⟨hf, hf0, hqq, hml0, hml1, hlc, hdep, hgr, hper, hs1, hs2, hs3, hs4, hdig, hcd1, hcd2, hb1,
    hb2, hb4, hb5, hnq, hb6, hlast, hyr, hnext⟩ := hspec
  set lv := cfg.lv lvl
  set lam := osHLam cfg lvl xs p H.cv1 with hlamd
  set enf := osHEnf cfg lvl xs p H
  set c0 := osHC cfg lvl xs p 0
  set c2 := osHC cfg lvl xs p 1
  set S1 := osSqueezesVals cfg.maxSq lv.squeezes sqzv (osHCv3 cfg lvl xs p H.cv1) with hS1
  set S2 := (osLamPowsVals lam lv.queries).take lv.queries with hS2
  set S3 := (osQueriesSegs cfg lv lvl rewv P.fch P.caps P.flags P.qw P.qbp rt enf c0 c2
      (sqCv (osHCv4 cfg lvl xs p H.cv1))).flatten with hS3
  set S4 := (if lvl = cfg.yrLevel then osGlueVals lam enf c0 (enf + c2) c2 (H.w1.quad.getD 0 0)
      (H.w1.quad.getD 1 0) (H.w1.quad.getD 2 0) H.w1.target
    else osOodGlueVals (osHW cfg lvl xs p 2) (osHW cfg lvl xs p 3) (osHW cfg lvl xs p 4) lam lam
      (H.w1.quad.getD 0 0) (H.w1.quad.getD 1 0) (H.w1.quad.getD 2 0) H.w1.target ++
      osGlueVals (lam * lam) enf c0 (enf + c2) c2 (H.w1.quad.getD 0 0 + lam * osHW cfg lvl xs p 3)
        (H.w1.quad.getD 1 0 + lam * (osHW cfg lvl xs p 2 + osHW cfg lvl xs p 4))
        (H.w1.quad.getD 2 0 + lam * osHW cfg lvl xs p 4) (H.w1.target + lam * osHW cfg lvl xs p 2)) with hS4
  have hVB : osLvValsB cfg lvl xs p H rt P sqzv rewv = S1 ++ S2 ++ S3 ++ S4 := rfl
  rw [hVB] at hv ⊢
  have hl1 : S1.length = 25 := by simp [hS1, osSqueezesVals]
  have hl2 : S2.length = lv.queries := by
    simp only [hS2, List.length_take, osLamPowsVals, List.length_cons, List.length_map, List.length_range]; omega
  -- the squeezes
  obtain ⟨hS, hatS, hlamS, hcoS, hcbS, hkS⟩ := osSqueezes_complete (C := Csq) (rd := rd) (σ := σ) (kret := kret)
    (maxSq := cfg.maxSq) (qpos := osQpos) (qbp := osQbp) (loop := lv.sqLoop) (by omega) hat l0 l1 l2 l3
    (by rw [hP.qpos, hP.qbp]; exact hcsq) (fun j hj => by rw [hv j (by simp only [List.length_append]; omega), List.append_assoc, List.append_assoc,
      oq_getD_app_lt (by omega)])
  set sq := (osLvSq cfg lvl sg).2 with hsq
  have hsq' : (osSqueezes cfg.maxSq lv.squeezes osQpos osQbp lv.sqLoop sg).2 = sq := rfl
  rw [hsq'] at hatS hlamS hcoS hcbS hkS
  replace hlamS : σ (.n (sq.k - 1)) = lam := hlamS
  obtain ⟨hv123, g4⟩ := os_look_app hv
  obtain ⟨hv12, g3⟩ := os_look_app hv123
  obtain ⟨-, g2⟩ := os_look_app hv12
  rw [hl1] at g2
  simp only [List.length_append, hl1, hl2] at g3 g4
  -- the query weights
  have hL := osLamPows_complete (C := C) (rd := rd) (σ := σ) (lam := sq.k - 1) (qw := osQw) (base := lvl * cfg.maxQ)
    (k := sq.k) (kret := kret) lv.queries (fun i hi => by rw [hP.qw, hlamS]; exact hqw i hi)
    (fun j hj => by
      rw [hlamS, hkS, g2 j (by rw [hl2]; exact hj), hS2, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj,
        ← List.getD_eq_getElem?_getD])
  -- the queries
  set sq' : OsSt := { sq with k := sq.k + lv.queries }
  have hatq : OsAt σ sq' (sqCv (osHCv4 cfg lvl xs p H.cv1)) cur (osHP2 cfg lvl p + 1) := ⟨hatS.fs, hatS.cursor⟩
  obtain ⟨hQ, hatQ, hcoQ, hcbQ, eq1, eq2, eq3, eq4, eq5, hkQ⟩ := osQueries_complete (rd := rd) (σ := σ)
    (cfg := cfg) (lv := lv) (lvl := lvl) (kret := kret) hb1 hb2 (by omega) hb4 hb5 hatq hc0 hc2
    (by rw [hP.roots]; exact sr0) (by rw [hP.roots]; exact sr1) (rewv := rewv) (qsum := enf)
    (by rw [hP.fch]; exact hcrw) (by rw [hP.caps, hP.flags]; exact hccap)
    (by rw [hP.caps, hP.flags, hP.qw, hP.qbp]; exact hcq) (fun j hj => by
      rw [hP.fch, hP.caps, hP.flags, hP.qw, hP.qbp] at hj ⊢
      rw [show sq'.k + j = sg.k + (25 + lv.queries) + j by simp only [sq', hkS]; ring]
      exact g3 j hj)
  set q := osQueries cfg lv lvl sq' with hqdef
  have eQ : osLvQ cfg lvl sg = q := rfl
  have kq : q.2.1.c = sg.c ∧ q.2.1.b = sg.b ∧ q.2.1.a = sg.a ∧ q.2.1.t = sg.t := ⟨rfl, rfl, rfl, rfl⟩
  rw [hP.fch, hP.caps, hP.flags, hP.qw, hP.qbp] at hkQ
  have hkq : q.2.1.k = sg.k + (25 + lv.queries + S3.length) := by
    rw [hkQ, ← hS3]; simp only [sq', hkS]; ring
  rw [← hkq] at g4
  have hq0 : H.w1.quad.getD 0 0 = σ (.n sg.c) := by rw [hqd]; rfl
  have hq1 : H.w1.quad.getD 1 0 = σ (.n sg.b) := by rw [hqd]; rfl
  have hq2 : H.w1.quad.getD 2 0 = σ (.n sg.a) := by rw [hqd]; rfl
  have hP3 : osHPEnd cfg lvl p = osHP2 cfg lvl p + 1 + 2 := by rw [osHPEnd]
  have hstB : osLvRestB cfg lvl sg = osLvL cfg lvl sg ++ q.1 ++ (osLvO cfg lvl sg).1 ++
      [.atom (.load (.n (osLvO cfg lvl sg).2.2) (.n osBetas) lvl)] ++ (osLvGl cfg lvl sg).1 := rfl
  have hsig : OsLvSig σ cfg lvl sg sqzv rewv := by
    have v0 := hv 0 (by simp [hl1])
    have v1 := hv 1 (by simp [hl1]; omega)
    have v4 := hv 4 (by simp [hl1]; omega)
    have v5 := hv 5 (by simp [hl1]; omega)
    have v6 := hv 6 (by simp [hl1]; omega)
    have hS3l : 2 ≤ S3.length := by simp [hS3, osQueriesSegs]
    have w0 := g3 0 (by omega)
    have w1 := g3 1 (by omega)
    simp only [List.append_assoc] at v0 v1 v4 v5 v6
    rw [oq_getD_app_lt (by omega)] at v0 v1 v4 v5 v6
    refine ⟨by simpa [hS1, osSqueezesVals] using v0, by simpa [hS1, osSqueezesVals] using v1,
      by rw [v4]; simp [hS1, osSqueezesVals]; rfl, by rw [v5]; simp [hS1, osSqueezesVals],
      by rw [v6]; simp [hS1, osSqueezesVals]; rfl, ?_, ?_⟩
    · rw [show (osLvSq cfg lvl sg).2.k + lv.queries = sg.k + (25 + lv.queries) + 0 by rw [← hsq, hkS]; ring, w0]
      simp [hS3, osQueriesSegs]
    · rw [show (osLvSq cfg lvl sg).2.k + lv.queries + 1 = sg.k + (25 + lv.queries) + 1 by rw [← hsq, hkS]; ring, w1]
      simp [hS3, osQueriesSegs]
  by_cases hl : lvl = cfg.yrLevel
  · have eO : osLvO cfg lvl sg = ([], q.2.1, sq.k - 1) := by rw [osLvO, ite_pos' hl]; rfl
    have hS4' : S4 = osGlueVals lam enf c0 (enf + c2) c2 (H.w1.quad.getD 0 0) (H.w1.quad.getD 1 0)
        (H.w1.quad.getD 2 0) H.w1.target := by rw [hS4, ite_pos' hl]
    have hl4 : S4.length = 8 := by rw [hS4']; rfl
    rw [hl4, hS4'] at g4
    have eGl : osLvGl cfg lvl sg = osGlue (sq.k - 1) q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 q.2.1 := by
      rw [osLvGl, eO, eQ]
    obtain ⟨hG, gc, gb, ga, gt, gk, -, -, -, gco⟩ := osGlue_complete (C := C) (rd := rd) (σ := σ) (kret := kret)
      (sc := sq.k - 1) (v := q.2.2.1) (c0 := q.2.2.2.1) (c1 := q.2.2.2.2.1) (c2 := q.2.2.2.2.2) (s := q.2.1)
      (fun j hj => by
        rw [g4 j hj, hlamS, eq1, eq2, eq3, eq4, kq.1, kq.2.1, kq.2.2.1, kq.2.2.2, hq0, hq1, hq2, htg])
    rw [← eGl] at hG gc gb ga gt gk gco
    refine ⟨⟨hS, ?_, hsig⟩, ⟨by rw [eGl]; exact hatQ.fs, by rw [eGl, hP3]; exact hatQ.cursor⟩, ?_, ?_, ?_, ?_⟩
    · rw [hstB, eO]
      simp only [holdsList_append]
      refine (holdsList_noRet _ (osLamPows_noRet _ _ _ _ _) _ _).mpr ⟨hL,
        (holdsList_noRet _ (osQueries_noRet _ _ _ _) _ _).mpr ⟨hQ, (holdsList_noRet _ rfl _ _).mpr ⟨trivial,
        (holdsList_noRet _ rfl _ _).mpr ⟨?_, hG⟩⟩⟩⟩
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      rw [hlamS, hP.betas]
      rw [ite_pos' hl] at hbeta
      exact hbeta
    · rw [gco, hcoQ]; show sq.co + 2 = _; rw [hcoS]
    · simp only [osHWEnd, osHPending, ite_pos' hl, List.nil_append, os_glue_one]
      rw [gc, gb, ga]
      show List.zipWith _ H.w1.quad _ = [σ (.n q.2.1.c) + σ (.n (sq.k - 1)) * σ (.n q.2.2.2.1),
        σ (.n q.2.1.b) + σ (.n (sq.k - 1)) * σ (.n q.2.2.2.2.1), σ (.n q.2.1.a) + σ (.n (sq.k - 1)) * σ (.n q.2.2.2.2.2)]
      rw [hqd, hlamS, eq2, eq3, eq4, kq.1, kq.2.1, kq.2.2.1]
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right, one_mul]; rfl
    · simp only [osHWEnd, osHPending, ite_pos' hl, List.nil_append, os_glue_one]
      rw [gt]
      show H.w1.target + 1 * _ * _ = σ (.n q.2.1.t) + σ (.n (sq.k - 1)) * σ (.n q.2.2.1)
      rw [htg, hlamS, eq1, kq.2.2.2, one_mul]
    · rw [gk, hkq]; simp only [List.length_append, hl1, hl2, hl4]; ring
  · obtain ⟨next, rest', rfl⟩ : ∃ next rest', rest = next :: rest' := by
      cases rest with
      | nil => exact absurd (hlast.mp rfl) hl
      | cons a b => exact ⟨a, b, rfl⟩
    have hood1 := (hnext next rfl).1
    obtain ⟨o0, o1, o2, o3⟩ := hood hl
    set O := osOodGlue ((lvl + 1) * 4) (sq.k - 1) (sq.k - 1) q.2.1 with hO
    have eO : osLvO cfg lvl sg = (O.1, O.2, O.2.k - 1) := by
      rw [osLvO, ite_neg' hl, hood1, osOodGlues_one]; rfl
    have hS4' : S4 = osOodGlueVals (osHW cfg lvl xs p 2) (osHW cfg lvl xs p 3) (osHW cfg lvl xs p 4) lam lam
        (H.w1.quad.getD 0 0) (H.w1.quad.getD 1 0) (H.w1.quad.getD 2 0) H.w1.target ++
        osGlueVals (lam * lam) enf c0 (enf + c2) c2 (H.w1.quad.getD 0 0 + lam * osHW cfg lvl xs p 3)
          (H.w1.quad.getD 1 0 + lam * (osHW cfg lvl xs p 2 + osHW cfg lvl xs p 4))
          (H.w1.quad.getD 2 0 + lam * osHW cfg lvl xs p 4) (H.w1.target + lam * osHW cfg lvl xs p 2) := by
      rw [hS4, ite_neg' hl]
    rw [hS4'] at g4
    obtain ⟨g4a, g4b⟩ := os_look_app g4
    have hla : (osOodGlueVals (osHW cfg lvl xs p 2) (osHW cfg lvl xs p 3) (osHW cfg lvl xs p 4) lam lam
        (H.w1.quad.getD 0 0) (H.w1.quad.getD 1 0) (H.w1.quad.getD 2 0) H.w1.target).length = 13 := rfl
    rw [hla] at g4a g4b
    obtain ⟨hOh, oc, ob, oa, ot, ok1, ok, -, -, -, oco⟩ := osOodGlue_complete (C := C) (rd := rd) (σ := σ)
      (so := (lvl + 1) * 4) (sc := sq.k - 1) (lam := sq.k - 1) (s := q.2.1) (kret := kret)
      (by rw [hP.ood]; exact o1) (by rw [hP.ood]; exact o2) (by rw [hP.ood]; exact o3)
      (by rw [hP.ood, hlamS]; exact o0)
      (fun j hj => by rw [g4a j hj, hlamS, kq.1, kq.2.1, kq.2.2.1, kq.2.2.2, hq0, hq1, hq2, htg])
    rw [← hO] at hOh oc ob oa ot ok1 ok oco
    have eGl : osLvGl cfg lvl sg = osGlue (O.2.k - 1) q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 O.2 := by
      rw [osLvGl, eO, eQ]
    rw [hlamS, kq.1] at oc
    rw [hlamS, kq.2.1] at ob
    rw [hlamS, kq.2.2.1] at oa
    rw [hlamS, kq.2.2.2] at ot
    rw [hlamS] at ok1
    obtain ⟨hG, gc, gb, ga, gt, gk, -, -, -, gco⟩ := osGlue_complete (C := C) (rd := rd) (σ := σ) (kret := kret)
      (sc := O.2.k - 1) (v := q.2.2.1) (c0 := q.2.2.2.1) (c1 := q.2.2.2.2.1) (c2 := q.2.2.2.2.2) (s := O.2)
      (fun j hj => by
        rw [show O.2.k + j = q.2.1.k + 13 + j by rw [ok]]
        rw [g4b j hj, ok1, eq1, eq2, eq3, eq4, oc, ob, oa, ot, hq0, hq1, hq2, htg])
    rw [← eGl] at hG gc gb ga gt gk gco
    refine ⟨⟨hS, ?_, hsig⟩, ⟨by rw [eGl]; exact hatQ.fs, by rw [eGl, hP3]; exact hatQ.cursor⟩, ?_, ?_, ?_, ?_⟩
    · rw [hstB, eO]
      simp only [holdsList_append]
      refine (holdsList_noRet _ (osLamPows_noRet _ _ _ _ _) _ _).mpr ⟨hL,
        (holdsList_noRet _ (osQueries_noRet _ _ _ _) _ _).mpr ⟨hQ,
        (holdsList_noRet _ (by simp [hO, osOodGlue, Stmt.noRetList, Stmt.noRet]) _ _).mpr ⟨hOh,
        (holdsList_noRet _ rfl _ _).mpr ⟨?_, hG⟩⟩⟩⟩
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      rw [ok1, hP.betas]
      rw [ite_neg' hl] at hbeta
      exact hbeta
    · rw [gco, oco, hcoQ]; show sq.co + 2 = _; rw [hcoS]
    · simp only [osHWEnd, osHPending, ite_neg' hl, List.singleton_append, os_glue_two]
      rw [gc, gb, ga, ok1, eq2, eq3, eq4, oc, ob, oa, hqd]
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right, one_mul]; rfl
    · simp only [osHWEnd, osHPending, ite_neg' hl, List.singleton_append, os_glue_two]
      rw [gt, ok1, eq1, ot, htg, one_mul]
    · have hl4' : S4.length = 21 := by rw [hS4']; rfl
      rw [gk, ok, hkq]; simp only [List.length_append, hl1, hl2, hl4']; ring



end
end LeanVM.Guest.B1
