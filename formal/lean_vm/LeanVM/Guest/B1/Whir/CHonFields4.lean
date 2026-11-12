/-
  LeanVM.Guest.B1.Whir.CHonFields4

  Each level's commitment and openings on the honest run, and OsHonest's memory fields.
-/

module

public import LeanVM.Guest.B1.Whir.CHonFields3
public import LeanVM.Guest.B1.Whir.CCaps
public import LeanVM.Guest.B1.Whir.CHonBodyRun0
public import LeanVM.Guest.B1.Whir.CHonBodyRun

/-!
# The levels' openings, and OsHonest's memory fields

`HonRun.roots`: level `l`'s commitment is the `l`-th root, at the level's depth and row width.
`HonRun.opens`: its phase opens its positions against it. `HonRun.capv`: its cap cells and flags
(`capCellH`, `capFlH`) at its positions' nodes are the climbed digests and `1`.
`HonRun.fld_rowsMem`, `fld_posMem`, `fld_qMem`: OsHonest's memory fields.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem getElem?_snoc {α : Type} (A : List α) (x : α) {n : ℕ} (h : A.length = n) : (A ++ [x])[n]? = some x := by
  rw [List.getElem?_append_right (by omega), h, Nat.sub_self]; rfl

theorem getD_snoc {α : Type} (A : List α) (x d : α) {n : ℕ} (h : A.length = n) : (A ++ [x]).getD n d = x := by
  rw [List.getD_eq_getElem?_getD, getElem?_snoc _ _ h]; rfl

theorem sqPositions_lt {d : ℕ} {w : ℕ → E} {n q : ℕ} (h : q ∈ sqPositions d w n) : q < 2 ^ d := by
  simp only [sqPositions, List.mem_map, List.mem_range] at h
  obtain ⟨k, -, rfl⟩ := h
  exact Nat.mod_lt _ (by positivity)

theorem map_getD_eq {α β : Type} (f : α → β) (l : List α) (d : β) {k : ℕ} (hk : k < l.length) :
    (l.map f).getD k d = f l[k] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]

/-- The cap's node and flag indices of a position. -/
theorem cap_idx {q pd cd : ℕ} (hq : q < 2 ^ (pd + cd)) (hcd : 2 ≤ cd) :
    2 * (2 ^ cd + q / 2 ^ pd) + 1 < 4 * 2 ^ cd ∧ 2 ^ (cd - 1) + q / 2 ^ (pd + 1) < 2 ^ cd := by
  have hd1 : q / 2 ^ pd < 2 ^ cd := Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hq)
  have hd2 : q / 2 ^ (pd + 1) < 2 ^ (cd - 1) :=
    Nat.div_lt_of_lt_mul (by rw [← pow_add, show pd + 1 + (cd - 1) = pd + cd by omega]; exact hq)
  have hc1 : 2 ^ cd = 2 * 2 ^ (cd - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ cd)]
  omega

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **Level `l`'s commitment**: the `l`-th root, at the level's depth and row width. -/
theorem roots : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length,
    (Ls.getD l default).R.length = l + 1 ∧
      (Ls.getD l default).R[l]? = some (((Ls.getD l default).R.getD l default).1,
        (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth, lvWidth l (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)))
  | 0, _ => by
    have hst := hR.start
    obtain ⟨-, hsh, -⟩ := hR.cand
    have hn := hR.n2
    rw [List.headD_eq_head?_getD, List.head?_eq_getElem?] at hsh
    have e : (osCfgR (μ - minOpenLog) (r - 1)).levels[0]?.getD default = ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD 0 default) := by
      simp [List.getD_eq_getElem?_getD]
    rw [e] at hsh
    rw [hst.2.2.1]
    simp [hsh]
  | l + 1, hl => by
    have hy := hR.yr
    obtain ⟨hlen, hRl⟩ := roots l (by omega)
    obtain ⟨rw, W, hd, -, -, -, -, -, -, -, hR'⟩ := hR.step (l := l) (by omega)
    have hB := hR.lvb (l := l) (by omega)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hshape, -⟩ := hR.mid (l := l) (by omega)
    have hrw : (Ls.getD l default).rw = rw := by unfold LvAt.rw; rw [hd]
    have hmu := hB.mu
    simp only [LvAt.mu, LvAt.s1, hrw] at hmu
    rw [hR', NextW.roots, hmu, hshape]
    refine ⟨by rw [List.length_append, hlen]; rfl, ?_⟩
    rw [getElem?_snoc _ _ hlen, getD_snoc _ _ _ hlen]

/-- **Level `l`'s phase opens its positions** against its commitment. -/
theorem opens {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    ∃ (qs : List ℕ) (ph : List Opening), (Ls.getD l default).qs μ = qs ∧ (Ls.getD l default).phase = ph ∧
      ph.length = qs.length ∧ ∀ k (hk : k < qs.length) (ho : k < ph.length),
        Id.run (Compile.openOneWithHash (m := Id) keccak256 ((Ls.getD l default).R.getD l default).1
          (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth (lvWidth l (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default))) qs[k] ph[k]) =
          true := by
  have hy := hR.yr
  have hRl := (hR.roots l hl).2
  by_cases hlt : l < (osCfgR (μ - minOpenLog) (r - 1)).yrLevel
  · obtain ⟨rw, W, hd, -, -, -, -, hnext, -⟩ := hR.step hlt
    have hrw : (Ls.getD l default).rw = rw := by unfold LvAt.rw; rw [hd]
    have hqs : (Ls.getD l default).qs μ = W.qs (rsF (Ls.getD l default).level (Ls.getD l default).cap rw)
        (μ - (rsSt (Ls.getD l default).level (Ls.getD l default).s (Ls.getD l default).cap rw).alphas.length)
        (μ - (rsSt (Ls.getD l default).level (Ls.getD l default).s (Ls.getD l default).cap rw).alphas.length +
          (Ls.getD l default).level.logInvRate) (Ls.getD l default).level.queries := by
      unfold LvAt.qs; rw [hd]; simp only [LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hrw]
    have hph : (Ls.getD l default).phase = W.phase := by unfold LvAt.phase; rw [hd]
    obtain ⟨rt, ht, wd, hR', hok⟩ := hnext.root
    rw [hRl] at hR'
    simp only [Option.some.injEq, Prod.mk.injEq] at hR'
    obtain ⟨e1, e2, e3⟩ := hR'
    refine ⟨_, _, hqs, hph, hnext.plen, fun k hk ho ↦ ?_⟩
    rw [e1, e2, e3]
    exact hok k hk ho
  · have he : l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel := by omega
    subst he
    obtain ⟨rw, W, hd, -, -, -, -, hfin, -⟩ := hR.last
    have hrw : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).rw = rw := by unfold LvAt.rw; rw [hd]
    have hqs : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).qs μ =
        W.qs (rsF (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).level
          (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).cap rw)
        (μ - (rsSt (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).level
          (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).s
          (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).cap rw).alphas.length +
          (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).level.logInvRate)
        (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).level.queries := by
      unfold LvAt.qs; rw [hd]; simp only [LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hrw]
    have hph : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).phase = W.phase := by
      unfold LvAt.phase; rw [hd]
    obtain ⟨rt, ht, wd, hR', hok⟩ := hfin.root
    rw [hRl] at hR'
    simp only [Option.some.injEq, Prod.mk.injEq] at hR'
    obtain ⟨e1, e2, e3⟩ := hR'
    refine ⟨_, _, hqs, hph, hfin.plen, fun k hk ho ↦ ?_⟩
    rw [e1, e2, e3]
    exact hok k hk ho

theorem qs_lt {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    ∀ q ∈ (Ls.getD l default).qs μ, q < 2 ^ (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth := by
  intro q hq
  rw [LvAt.qs_eq_sq] at hq
  rw [(hR.lvb hl).dep]
  exact sqPositions_lt hq

theorem height_eq {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    heightAt Ls l = (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth := by
  unfold heightAt
  rw [List.getD_eq_getElem?_getD, (hR.roots l hl).2]
  rfl

/-- The shape's cap depth and path depth. -/
theorem cdpd {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd = (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).capDepth ∧
      (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd =
        (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth - (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).capDepth ∧
      2 ≤ (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).capDepth ∧
      (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).capDepth ≤ (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth ∧
      oqQA (osCfgR (μ - minOpenLog) (r - 1)) l = ((Ls.getD l default).qs μ).length := by
  obtain ⟨-, -, -, -, hdepth, hcd, -, hcd2, -, hcdd, hcount⟩ := (hR.lvb hl).qsh
  rw [hcd, hdepth] at hcdd
  rw [hcd] at hcd2
  refine ⟨by rw [oqSA, oq_cd, hcd], by rw [oqSA, oq_pd, hdepth, hcd], hcd2, hcdd, ?_⟩
  simp only [oqQA, oqOddA, oqSA, oq_base, oqNA, lvBase, osLvA]
  rw [hcount, LvAt.qs_length, (hR.lvb hl).q]

/-- **Level `l`'s cap cells and flags at its positions' nodes.** -/
theorem capv {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    ∀ k < oqQA (osCfgR (μ - minOpenLog) (r - 1)) l,
      (hdOf μ r Ls).cv l (2 * (2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd +
          ((Ls.getD l default).qs μ).getD k 0 / 2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd)) =
        (digestHalves (climbD (merkleLeafDigest (((Ls.getD l default).phase.map (·.leaf)).getD k []))
          (((Ls.getD l default).qs μ).getD k 0)
          (((Ls.getD l default).phase.map (fun o ↦ o.path.take ((((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth -
            (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).capDepth))).getD k []))).1 ∧
      (hdOf μ r Ls).cv l (2 * (2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd +
          ((Ls.getD l default).qs μ).getD k 0 / 2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd) + 1) =
        (digestHalves (climbD (merkleLeafDigest (((Ls.getD l default).phase.map (·.leaf)).getD k []))
          (((Ls.getD l default).qs μ).getD k 0)
          (((Ls.getD l default).phase.map (fun o ↦ o.path.take ((((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth -
            (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).capDepth))).getD k []))).2 ∧
      (hdOf μ r Ls).fv l (2 ^ ((oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd - 1) +
          ((Ls.getD l default).qs μ).getD k 0 / 2 ^ ((oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd + 1)) = 1 := by
  intro k hk
  obtain ⟨hcdq, hpd, hcd2, hcdd, hQ⟩ := hR.cdpd hl
  have hag := hR.agree l (by rw [hR.len]; exact hl) _ _ _ (hR.roots l hl).2
  have hps := hR.qs_lt hl
  obtain ⟨qs, ph, hq, hp, hlen, hok⟩ := hR.opens hl
  rw [hq, hp] at hag
  rw [hq] at hps hQ
  have hk' : k < qs.length := by omega
  obtain ⟨c1, c2, c3, -, -, -⟩ := capH_query hlen hok hps hag hcd2 hcdd k hk'
  have hcv : (hdOf μ r Ls).cv l = capCellH (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth qs ph := by
    show capCellH (heightAt Ls l) _ _ = _
    rw [hR.height_eq hl, hq, hp]
  have hfv : (hdOf μ r Ls).fv l =
      capFlH (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).capDepth qs ph := by
    show capFlH (heightAt Ls l) _ _ _ = _
    rw [hR.height_eq hl, hq, hp]
  rw [hcv, hfv, hcdq, hpd, hq, hp, List.getD_eq_getElem _ _ hk', map_getD_eq _ _ _ (by omega),
    map_getD_eq _ _ _ (by omega)]
  exact ⟨c1, c2, c3⟩

/-- Level `l`'s hinted cap cells. -/
noncomputable def capW (Ls : List LvAt) (μ r l : ℕ) : List E :=
  (List.range (4 * 2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd)).map ((hdOf μ r Ls).cv l)

/-- Level `l`'s hinted cap flags. -/
noncomputable def flW (Ls : List LvAt) (μ r l : ℕ) : List E :=
  (List.range (2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd)).map ((hdOf μ r Ls).fv l)

/-- **OsHonestA's `caps`.** -/
theorem fld_caps : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length,
    (capW Ls μ r l).length = 4 * 2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd ∧
    (flW Ls μ r l).length = 2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd ∧
    (∀ (rd : Reader) (CAP FL : E), ReadsAt rd CAP (capW Ls μ r l) → ReadsAt rd FL (flW Ls μ r l) →
      MeaningVerifyMerkleCap (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd rd [CAP, FL]
        [(osRootA (hdOf μ r Ls).own l).1, (osRootA (hdOf μ r Ls).own l).2]) ∧
    ∀ k < oqQA (osCfgR (μ - minOpenLog) (r - 1)) l,
      (capW Ls μ r l).getD (2 * (2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd +
          ((Ls.getD l default).qs μ).getD k 0 / 2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd)) 0 =
        (digestHalves (climbD (merkleLeafDigest (((Ls.getD l default).phase.map (·.leaf)).getD k []))
          (((Ls.getD l default).qs μ).getD k 0)
          (((Ls.getD l default).phase.map (fun o ↦ o.path.take
            (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth -
              ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).capDepth))).getD k []))).1 ∧
      (capW Ls μ r l).getD (2 * (2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd +
          ((Ls.getD l default).qs μ).getD k 0 / 2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd) + 1) 0 =
        (digestHalves (climbD (merkleLeafDigest (((Ls.getD l default).phase.map (·.leaf)).getD k []))
          (((Ls.getD l default).qs μ).getD k 0)
          (((Ls.getD l default).phase.map (fun o ↦ o.path.take
            (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth -
              ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).capDepth))).getD k []))).2 ∧
      (flW Ls μ r l).getD (2 ^ ((oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd - 1) +
          ((Ls.getD l default).qs μ).getD k 0 / 2 ^ ((oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd + 1)) 0 = 1 := by
  intro l hl
  have hS : HonStatic (hdOf μ r Ls).c := honStatic_all _ _ hR.m11 hR.r4
  obtain ⟨hcdq, hpd, hcd2, hcdd, hQ⟩ := hR.cdpd hl
  have hrootA := (hdOf μ r Ls).rootA hS hl
  have e4 : 2 ^ ((oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd + 2) =
      4 * 2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd := by rw [pow_add]; ring
  have hcapG : ∀ k < 4 * 2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd,
      (capW Ls μ r l).getD k 0 = (hdOf μ r Ls).cv l k := fun k hk ↦ by
    unfold capW; rw [getD_mapRange _ hk]
  have hflG : ∀ k < 2 ^ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd,
      (flW Ls μ r l).getD k 0 = (hdOf μ r Ls).fv l k := fun k hk ↦ by
    unfold flW; rw [getD_mapRange _ hk]
  refine ⟨by simp [capW], by simp [flW], fun rd CAP FL hc hf ↦ ?_, fun k hk ↦ ?_⟩
  · obtain ⟨qs, ph, hq, hp, hlen, hok⟩ := hR.opens hl
    have hag := hR.agree l (by rw [hR.len]; exact hl) _ _ _ (hR.roots l hl).2
    have hps := hR.qs_lt hl
    have hne := hR.br_q0 l hl
    rw [hq, hp] at hag
    rw [hq] at hps hne
    rw [hrootA, hcdq]
    have hcv : (hdOf μ r Ls).cv l =
        capCellH ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth qs ph := by
      show capCellH (heightAt Ls l) _ _ = _
      rw [hR.height_eq hl, hq, hp]
    have hfv : (hdOf μ r Ls).fv l = capFlH ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth
        ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).capDepth qs ph := by
      show capFlH (heightAt Ls l) _ _ _ = _
      rw [hR.height_eq hl, hq, hp]
    refine capH_meaning hlen hok hps hag hcd2 hcdd hne (fun k _ hk ↦ ?_) (fun k _ hk ↦ ?_)
    · rw [← hcdq, e4] at hk
      have := readsAt_getD' hc (j := k) (by simp only [capW, List.length_map, List.length_range]; exact hk)
      rwa [hcapG k hk, hcv] at this
    · rw [← hcdq] at hk
      have := readsAt_getD' hf (j := k) (by simp only [flW, List.length_map, List.length_range]; exact hk)
      rwa [hflG k hk, hfv] at this
  · have hk' : k < ((Ls.getD l default).qs μ).length := by omega
    have hqlt : ((Ls.getD l default).qs μ).getD k 0 <
        2 ^ ((oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd + (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd) := by
      rw [show (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd + (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd =
        ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth by omega,
        List.getD_eq_getElem _ _ hk']
      exact hR.qs_lt hl _ (List.getElem_mem hk')
    obtain ⟨b1, b2⟩ := cap_idx hqlt (by omega)
    obtain ⟨c1, c2, c3⟩ := hR.capv hl k hk
    exact ⟨by rw [hcapG _ (by omega)]; exact c1, by rw [hcapG _ b1]; exact c2, by rw [hflG _ b2]; exact c3⟩

/-- **OsHonestA's `qMem`.** -/
theorem fld_qMem : ∀ b rd, OsMemA rd (osCfgR (μ - minOpenLog) (r - 1)) b (hdOf μ r Ls).own →
    ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length,
    RoundsAt rd (osPtrA (osCfgR (μ - minOpenLog) (r - 1)) b osIxCoefsA *
      gen ^ (2 * (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).foldsOff)) (Ls.getD l default).rounds ∧
    ((oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).final = 1 → WordsAt rd (osHsPtrA (osCfgR (μ - minOpenLog) (r - 1)) b l)
      (if l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel then (hdOf μ r Ls).hsFC else [])) := by
  intro b rd hm l hl
  have hS : HonStatic (hdOf μ r Ls).c := honStatic_all _ _ hR.m11 hR.r4
  obtain ⟨-, -, -, -, -, -, hfinal, -⟩ := (hR.lvb hl).qsh
  have hrl : ∀ i < (hdOf μ r Ls).c.levels.length,
      ((hdOf μ r Ls).L i).rounds.length = ((hdOf μ r Ls).c.levels.getD i default).folds := fun i hi ↦ by
    show (Ls.getD i default).rounds.length = _
    rw [LvAt.rounds, roundsSpec_rounds_length, (hR.lvb hi).fold]
    rfl
  obtain ⟨k1, k2⟩ := (hdOf μ r Ls).qMem_at hS hm hR.len hrl hl
  refine ⟨k1, fun hf ↦ ?_⟩
  have hfl : l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel := by
    rw [oqSA, oq_final, hfinal] at hf
    by_contra hne
    simp [hne] at hf
  have k3 := k2 hfl
  simp only [hfl, ↓reduceIte]
  rw [hfl] at k3
  exact k3

omit hR in
/-- A level's samples from its first word and capacity. -/
theorem sqSample_word (L : LvAt) (logN j : ℕ) :
    sqSample (L.word logN 0) (capOf (L.qS logN)) j = L.word logN j := by
  rcases j with _ | j
  · simp [sqSample]
  · simp [LvAt.word, sqSample]

/-- **OsHonestA's `posW`.** -/
theorem fld_posW : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length,
    ∀ j < (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).squeezes, ∀ i < osPerA (osCfgR (μ - minOpenLog) (r - 1)) l,
      (osOwnA (hdOf μ r Ls).own osIxQposA).getD
          ((osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).posOff + j * osPerA (osCfgR (μ - minOpenLog) (r - 1)) l + i) 0 =
        eOfNat (qwPosOf (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth
          (sqSample ((hdOf μ r Ls).D l).w0 ((hdOf μ r Ls).D l).capL j) i) := by
  intro l hl j hj i hi
  have hS : HonStatic (hdOf μ r Ls).c := honStatic_all _ _ hR.m11 hR.r4
  have := (hdOf μ r Ls).posW_at hS hl hj hi
  have ew : ((hdOf μ r Ls).D l).w0 = (Ls.getD l default).word μ 0 := by simp [OsHD.D, OsHD.word]; rfl
  have ec : ((hdOf μ r Ls).D l).capL = capOf ((Ls.getD l default).qS μ) := by simp [OsHD.D, OsHD.capL]; rfl
  rw [ew, ec, sqSample_word]
  exact this

end HonRun

end
end LeanVM.Guest.B1.Whir
