/-
  LeanVM.Guest.B1.Whir.CHonFields4

  Each level's commitment and openings on the honest run, and OsHonest's memory fields.
-/

module

public import LeanVM.Guest.B1.Whir.CHonFields3
public import LeanVM.Guest.B1.Whir.CCaps

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

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **Level `l`'s commitment**: the `l`-th root, at the level's depth and row width. -/
theorem roots : ∀ l < (osCfg (candidate μ r)).levels.length,
    (Ls.getD l default).R.length = l + 1 ∧
      (Ls.getD l default).R[l]? = some (((Ls.getD l default).R.getD l default).1,
        (osLvAt (osCfg (candidate μ r)) l).depth, lvWidth l (osLvAt (osCfg (candidate μ r)) l))
  | 0, _ => by
    have hst := hR.start
    obtain ⟨-, hsh, -⟩ := hR.cand
    have hn := hR.n2
    rw [List.headD_eq_head?_getD, List.head?_eq_getElem?] at hsh
    have e : (osCfg (candidate μ r)).levels[0]?.getD default = osLvAt (osCfg (candidate μ r)) 0 := by
      simp [osLvAt, List.getD_eq_getElem?_getD]
    rw [e] at hsh
    rw [hst.2.2.1]
    simp [hsh]
  | l + 1, hl => by
    have hy := hR.yr
    obtain ⟨hlen, hRl⟩ := roots l (by omega)
    obtain ⟨rw, W, hd, -, -, -, -, -, -, -, hR'⟩ := hR.step (l := l) (by omega)
    have hB := hR.lvb (l := l) (by omega)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hshape, -⟩ := hR.mid (l := l) (by omega)
    have hrw : (Ls.getD l default).rw = rw := by unfold LvAt.rw; rw [hd]
    have hmu := hB.mu
    simp only [LvAt.mu, LvAt.s1, hrw] at hmu
    rw [hR', NextW.roots, hmu, hshape]
    refine ⟨by rw [List.length_append, hlen]; rfl, ?_⟩
    rw [getElem?_snoc _ _ hlen, getD_snoc _ _ _ hlen]

/-- **Level `l`'s phase opens its positions** against its commitment. -/
theorem opens {l : ℕ} (hl : l < (osCfg (candidate μ r)).levels.length) :
    ∃ (qs : List ℕ) (ph : List Opening), (Ls.getD l default).qs μ = qs ∧ (Ls.getD l default).phase = ph ∧
      ph.length = qs.length ∧ ∀ k (hk : k < qs.length) (ho : k < ph.length),
        Id.run (Compile.openOneWithHash (m := Id) keccak256 ((Ls.getD l default).R.getD l default).1
          (osLvAt (osCfg (candidate μ r)) l).depth (lvWidth l (osLvAt (osCfg (candidate μ r)) l)) qs[k] ph[k]) =
          true := by
  have hy := hR.yr
  have hRl := (hR.roots l hl).2
  by_cases hlt : l < (osCfg (candidate μ r)).yrLevel
  · obtain ⟨rw, W, hd, -, -, -, -, hnext, -⟩ := hR.step hlt
    have hrw : (Ls.getD l default).rw = rw := by unfold LvAt.rw; rw [hd]
    have hqs : (Ls.getD l default).qs μ = W.qs (rsF (Ls.getD l default).level (Ls.getD l default).cap rw)
        (μ - (rsSt (Ls.getD l default).level (Ls.getD l default).s (Ls.getD l default).cap rw).gammas.length)
        (μ - (rsSt (Ls.getD l default).level (Ls.getD l default).s (Ls.getD l default).cap rw).gammas.length +
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
  · have he : l = (osCfg (candidate μ r)).yrLevel := by omega
    subst he
    obtain ⟨rw, W, hd, -, -, -, -, hfin, -⟩ := hR.last
    have hrw : (Ls.getD (osCfg (candidate μ r)).yrLevel default).rw = rw := by unfold LvAt.rw; rw [hd]
    have hqs : (Ls.getD (osCfg (candidate μ r)).yrLevel default).qs μ =
        W.qs (rsF (Ls.getD (osCfg (candidate μ r)).yrLevel default).level
          (Ls.getD (osCfg (candidate μ r)).yrLevel default).cap rw)
        (μ - (rsSt (Ls.getD (osCfg (candidate μ r)).yrLevel default).level
          (Ls.getD (osCfg (candidate μ r)).yrLevel default).s
          (Ls.getD (osCfg (candidate μ r)).yrLevel default).cap rw).gammas.length +
          (Ls.getD (osCfg (candidate μ r)).yrLevel default).level.logInvRate)
        (Ls.getD (osCfg (candidate μ r)).yrLevel default).level.queries := by
      unfold LvAt.qs; rw [hd]; simp only [LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hrw]
    have hph : (Ls.getD (osCfg (candidate μ r)).yrLevel default).phase = W.phase := by
      unfold LvAt.phase; rw [hd]
    obtain ⟨rt, ht, wd, hR', hok⟩ := hfin.root
    rw [hRl] at hR'
    simp only [Option.some.injEq, Prod.mk.injEq] at hR'
    obtain ⟨e1, e2, e3⟩ := hR'
    refine ⟨_, _, hqs, hph, hfin.plen, fun k hk ho ↦ ?_⟩
    rw [e1, e2, e3]
    exact hok k hk ho

theorem qs_lt {l : ℕ} (hl : l < (osCfg (candidate μ r)).levels.length) :
    ∀ q ∈ (Ls.getD l default).qs μ, q < 2 ^ (osLvAt (osCfg (candidate μ r)) l).depth := by
  intro q hq
  rw [LvAt.qs_eq_sq] at hq
  rw [(hR.lvb hl).dep]
  exact sqPositions_lt hq

theorem height_eq {l : ℕ} (hl : l < (osCfg (candidate μ r)).levels.length) :
    heightAt Ls l = (osLvAt (osCfg (candidate μ r)) l).depth := by
  unfold heightAt
  rw [List.getD_eq_getElem?_getD, (hR.roots l hl).2]
  rfl

/-- The shape's cap depth and path depth. -/
theorem cdpd {l : ℕ} (hl : l < (osCfg (candidate μ r)).levels.length) :
    (oqS (osCfg (candidate μ r)) l).cd = (osLvAt (osCfg (candidate μ r)) l).capDepth ∧
      (oqS (osCfg (candidate μ r)) l).pd =
        (osLvAt (osCfg (candidate μ r)) l).depth - (osLvAt (osCfg (candidate μ r)) l).capDepth ∧
      2 ≤ (osLvAt (osCfg (candidate μ r)) l).capDepth ∧
      (osLvAt (osCfg (candidate μ r)) l).capDepth ≤ (osLvAt (osCfg (candidate μ r)) l).depth ∧
      oqQ (osCfg (candidate μ r)) l = ((Ls.getD l default).qs μ).length := by
  obtain ⟨-, -, -, -, hdepth, hcd, -, hcd2, -, hcdd, hcount⟩ := (hR.lvb hl).qsh
  rw [hcd, hdepth] at hcdd
  rw [hcd] at hcd2
  refine ⟨by rw [oqS, oq_cd, hcd], by rw [oqS, oq_pd, hdepth, hcd], hcd2, hcdd, ?_⟩
  rw [oqQ, oqOdd, oqS, oq_base, oqN, hcount, LvAt.qs_length, (hR.lvb hl).q]

/-- **Level `l`'s cap cells and flags at its positions' nodes.** -/
theorem capv {l : ℕ} (hl : l < (osCfg (candidate μ r)).levels.length) :
    ∀ k < oqQ (osCfg (candidate μ r)) l,
      (hdOf μ r Ls).cv l (2 * (2 ^ (oqS (osCfg (candidate μ r)) l).cd +
          ((Ls.getD l default).qs μ).getD k 0 / 2 ^ (oqS (osCfg (candidate μ r)) l).pd)) =
        (digestHalves (climbD (merkleLeafDigest (((Ls.getD l default).phase.map (·.leaf)).getD k []))
          (((Ls.getD l default).qs μ).getD k 0)
          (((Ls.getD l default).phase.map (fun o ↦ o.path.take ((osLvAt (osCfg (candidate μ r)) l).depth -
            (osLvAt (osCfg (candidate μ r)) l).capDepth))).getD k []))).1 ∧
      (hdOf μ r Ls).cv l (2 * (2 ^ (oqS (osCfg (candidate μ r)) l).cd +
          ((Ls.getD l default).qs μ).getD k 0 / 2 ^ (oqS (osCfg (candidate μ r)) l).pd) + 1) =
        (digestHalves (climbD (merkleLeafDigest (((Ls.getD l default).phase.map (·.leaf)).getD k []))
          (((Ls.getD l default).qs μ).getD k 0)
          (((Ls.getD l default).phase.map (fun o ↦ o.path.take ((osLvAt (osCfg (candidate μ r)) l).depth -
            (osLvAt (osCfg (candidate μ r)) l).capDepth))).getD k []))).2 ∧
      (hdOf μ r Ls).fv l (2 ^ ((oqS (osCfg (candidate μ r)) l).cd - 1) +
          ((Ls.getD l default).qs μ).getD k 0 / 2 ^ ((oqS (osCfg (candidate μ r)) l).pd + 1)) = 1 := by
  intro k hk
  obtain ⟨hcdq, hpd, hcd2, hcdd, hQ⟩ := hR.cdpd hl
  have hag := hR.agree l (by rw [hR.len]; exact hl) _ _ _ (hR.roots l hl).2
  have hps := hR.qs_lt hl
  obtain ⟨qs, ph, hq, hp, hlen, hok⟩ := hR.opens hl
  rw [hq, hp] at hag
  rw [hq] at hps hQ
  have hk' : k < qs.length := by omega
  obtain ⟨c1, c2, c3, -, -, -⟩ := capH_query hlen hok hps hag hcd2 hcdd k hk'
  have hcv : (hdOf μ r Ls).cv l = capCellH (osLvAt (osCfg (candidate μ r)) l).depth qs ph := by
    show capCellH (heightAt Ls l) _ _ = _
    rw [hR.height_eq hl, hq, hp]
  have hfv : (hdOf μ r Ls).fv l =
      capFlH (osLvAt (osCfg (candidate μ r)) l).depth (osLvAt (osCfg (candidate μ r)) l).capDepth qs ph := by
    show capFlH (heightAt Ls l) _ _ _ = _
    rw [hR.height_eq hl, hq, hp]
  rw [hcv, hfv, hcdq, hpd, hq, hp, List.getD_eq_getElem _ _ hk', map_getD_eq _ _ _ (by omega),
    map_getD_eq _ _ _ (by omega)]
  exact ⟨c1, c2, c3⟩

/-- **OsHonest's `rowsMem`.** -/
theorem fld_rowsMem : ∀ b rd, OsMemF rd (osCfg (candidate μ r)) b (hdOf μ r Ls).own →
    ∀ l < (osCfg (candidate μ r)).levels.length, ∀ j, 1 ≤ j → j < (osLvAt (osCfg (candidate μ r)) l).squeezes →
    (∀ i < 5, LoadHolds rd (osPtrF (osCfg (candidate μ r)) b (osIxSqz (osCfg (candidate μ r)) l) * (gen ^ j) ^ 5) i
      (((Ls.getD l default).capSq μ j).getD i 0)) ∧
    ∀ i < 5, LoadHolds rd (osPtrF (osCfg (candidate μ r)) b (osIxSqz (osCfg (candidate μ r)) l) * (gen ^ j) ^ 5)
      (5 + i) (((⟨(Ls.getD l default).capSq μ j, []⟩ : Fs).squeeze.2.cap).getD i 0) := by
  intro b rd hm l hl j hj1 hj
  have hS : HonStatic (hdOf μ r Ls).c := honStatic_all _ hR.m28
  exact (hdOf μ r Ls).rowsMem_at hS hm hl hj1 hj

/-- **OsHonest's `posMem`.** -/
theorem fld_posMem : ∀ b rd, OsMemF rd (osCfg (candidate μ r)) b (hdOf μ r Ls).own →
    ∀ l < (osCfg (candidate μ r)).levels.length, ∀ j < (osLvAt (osCfg (candidate μ r)) l).squeezes,
    ∀ i < sqPer (osLvAt (osCfg (candidate μ r)) l),
      LoadHolds rd (osPtrF (osCfg (candidate μ r)) b 11 * gen ^ (osLvAt (osCfg (candidate μ r)) l).posOff *
        (gen ^ j) ^ sqPer (osLvAt (osCfg (candidate μ r)) l)) i
        (eOfNat (qwPosOf (osLvAt (osCfg (candidate μ r)) l).depth ((Ls.getD l default).word μ j) i)) := by
  intro b rd hm l hl j hj i hi
  have hS : HonStatic (hdOf μ r Ls).c := honStatic_all _ hR.m28
  exact (hdOf μ r Ls).posMem_at hS hm hl hj hi

/-- **OsHonest's `qMem`.** -/
theorem fld_qMem : ∀ b rd, OsMemF rd (osCfg (candidate μ r)) b (hdOf μ r Ls).own →
    ∀ l < (osCfg (candidate μ r)).levels.length,
    RoundsAt rd (osPtrF (osCfg (candidate μ r)) b 5 * gen ^ (3 * (osLvAt (osCfg (candidate μ r)) l).foldsOff))
      (Ls.getD l default).rounds ∧
    ((oqS (osCfg (candidate μ r)) l).final = 1 → WordsAt rd (osHsPtr (osCfg (candidate μ r)) b l)
      (if l = (osCfg (candidate μ r)).yrLevel then (hdOf μ r Ls).hsFC else [])) ∧
    ∀ k < oqQ (osCfg (candidate μ r)) l,
      LoadHolds rd (osPtrF (osCfg (candidate μ r)) b 0 * gen ^ (4 * (osLvAt (osCfg (candidate μ r)) l).capOff))
        (2 * (2 ^ (oqS (osCfg (candidate μ r)) l).cd +
          ((Ls.getD l default).qs μ).getD k 0 / 2 ^ (oqS (osCfg (candidate μ r)) l).pd))
        (digestHalves (climbD (merkleLeafDigest (((Ls.getD l default).phase.map (·.leaf)).getD k []))
          (((Ls.getD l default).qs μ).getD k 0)
          (((Ls.getD l default).phase.map (fun o ↦ o.path.take ((osLvAt (osCfg (candidate μ r)) l).depth -
            (osLvAt (osCfg (candidate μ r)) l).capDepth))).getD k []))).1 ∧
      LoadHolds rd (osPtrF (osCfg (candidate μ r)) b 0 * gen ^ (4 * (osLvAt (osCfg (candidate μ r)) l).capOff))
        (2 * (2 ^ (oqS (osCfg (candidate μ r)) l).cd +
          ((Ls.getD l default).qs μ).getD k 0 / 2 ^ (oqS (osCfg (candidate μ r)) l).pd) + 1)
        (digestHalves (climbD (merkleLeafDigest (((Ls.getD l default).phase.map (·.leaf)).getD k []))
          (((Ls.getD l default).qs μ).getD k 0)
          (((Ls.getD l default).phase.map (fun o ↦ o.path.take ((osLvAt (osCfg (candidate μ r)) l).depth -
            (osLvAt (osCfg (candidate μ r)) l).capDepth))).getD k []))).2 ∧
      LoadHolds rd (osPtrF (osCfg (candidate μ r)) b 1 * gen ^ (osLvAt (osCfg (candidate μ r)) l).capOff)
        (2 ^ ((oqS (osCfg (candidate μ r)) l).cd - 1) +
          ((Ls.getD l default).qs μ).getD k 0 / 2 ^ ((oqS (osCfg (candidate μ r)) l).pd + 1)) 1 := by
  intro b rd hm l hl
  have hS : HonStatic (hdOf μ r Ls).c := honStatic_all _ hR.m28
  have hy := hR.yr
  obtain ⟨hcdq, hpd, hcd2, hcdd, hQ⟩ := hR.cdpd hl
  obtain ⟨-, -, -, -, -, -, hfinal, -⟩ := (hR.lvb hl).qsh
  have hrl : ∀ i < (hdOf μ r Ls).c.levels.length,
      ((hdOf μ r Ls).L i).rounds.length = (osLvAt (hdOf μ r Ls).c i).folds := fun i hi ↦ by
    show (Ls.getD i default).rounds.length = _
    rw [LvAt.rounds, roundsSpec_rounds_length, (hR.lvb hi).fold]
    rfl
  have hfin : (oqS (hdOf μ r Ls).c l).final = 1 → l = (hdOf μ r Ls).c.yrLevel := fun hf ↦ by
    change (oqS (osCfg (candidate μ r)) l).final = 1 at hf
    rw [oqS, oq_final, hfinal] at hf
    by_contra hne
    change ¬ l = (osCfg (candidate μ r)).yrLevel at hne
    simp [hne] at hf
  have hq : ∀ k < oqQ (hdOf μ r Ls).c l, ((Ls.getD l default).qs μ).getD k 0 <
      2 ^ ((oqS (hdOf μ r Ls).c l).pd + (oqS (hdOf μ r Ls).c l).cd) := fun k hk ↦ by
    change k < oqQ (osCfg (candidate μ r)) l at hk
    change _ < 2 ^ ((oqS (osCfg (candidate μ r)) l).pd + (oqS (osCfg (candidate μ r)) l).cd)
    rw [hpd, hcdq, Nat.sub_add_cancel hcdd]
    have hk' : k < ((Ls.getD l default).qs μ).length := by omega
    rw [List.getD_eq_getElem _ _ hk']
    exact hR.qs_lt hl _ (List.getElem_mem hk')
  have hc : (hdOf μ r Ls).c = osCfg (candidate μ r) := rfl
  have key := (hdOf μ r Ls).qMem_at hS hm hR.len hrl hl hfin (by rw [hc]; exact hcdq)
    (by rw [hc]; omega)
    (fun k ↦ ((Ls.getD l default).qs μ).getD k 0)
    (fun k ↦ ((Ls.getD l default).phase.map (·.leaf)).getD k [])
    (fun k ↦ ((Ls.getD l default).phase.map (fun o ↦ o.path.take ((osLvAt (osCfg (candidate μ r)) l).depth -
      (osLvAt (osCfg (candidate μ r)) l).capDepth))).getD k []) hq (by rw [hc]; exact hR.capv hl)
  rw [hc] at key
  exact key

end HonRun

end
end LeanVM.Guest.B1.Whir
