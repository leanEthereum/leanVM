/-
  LeanVM.Guest.B1.Whir.BrFit

  The honest trace of an accepting run against a candidate's configuration.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.BrCont

/-!
# The trace against the configuration

* `chain_end`: the end of a chain, its words after the levels named (`ChainEndP`);
* `chain_glued`: the last level's glued claims are the levels' records' claims;
* `chain_foldsNz`: no fold challenge is zero;
* `levelsOk_at`: `LevelsOk` level by level;
* `TrFit`, `trFit_of_run`: on an accepting run with no zero challenge, at a candidate's facts, the
  trace's levels fit the candidate's rows level by level, and the run's end is the trace's.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {logN lane : ℕ}

/-- The end of a chain, without memory. -/
structure ChainEndP (lane : ℕ) (Lf : SpLv) (xsR : List E) (res : WhirEnd × FSt) : Prop where
  fin : Lf.fin = true
  len : 2 * (Lf.ml - 1) ≤ xsR.length
  nz : ∀ c ∈ (tailTr Lf.ml Lf.Fend Lf.wsEnd.quad Lf.wsEnd.target xsR).2.1, c ≠ 0
  res : ∃ (osR : List (List Opening)) (R : List (Digest × ℕ × ℕ)), Lf.Ok R (Vector.replicate 4 0) ∧
    res = (Lf.wend lane xsR, ⟨(tailTr Lf.ml Lf.Fend Lf.wsEnd.quad Lf.wsEnd.target xsR).1,
      xsR.drop (2 * (Lf.ml - 1)), osR, R⟩)

theorem chain_end : ∀ (cfg : List Whir.Level) (lvl : ℕ) (ws : WhirStateT) (F : Fs) (xs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) (Ls : List SpLv) (res : WhirEnd × FSt),
    SpChain logN lane lvl cfg ws F xs os R Ls res →
    ChainEndP lane (Ls.getLastD default) (xs.drop (Ls.map SpLv.words).flatten.length) res
  | [level], lvl, ws, F, xs, os, R, [L], res, h => by
    obtain ⟨-, -, -, e4, -, -, hOk, xsR, osR, hxs, -, htl, htnz, hres⟩ := h
    have hdr : xs.drop ([L].map SpLv.words).flatten.length = xsR := by rw [hxs]; simp
    rw [hdr]
    exact ⟨e4, htl, htnz, osR, R, hOk, hres⟩
  | level :: next :: cfg, lvl, ws, F, xs, os, R, L :: Ls, res, h => by
    obtain ⟨-, -, -, -, -, -, d, xsR, osR, -, hxs, -, h'⟩ := h
    have hdr : xs.drop ((L :: Ls).map SpLv.words).flatten.length =
        xsR.drop (Ls.map SpLv.words).flatten.length := by
      rw [hxs]; simp [List.drop_append]
    rw [hdr]
    have hl := (chain_at _ _ _ _ _ _ _ _ _ h').1
    have hlast : (L :: Ls).getLastD default = Ls.getLastD default := by
      cases Ls with
      | nil => simp at hl
      | cons _ _ => rfl
    rw [hlast]
    exact chain_end _ _ _ _ _ _ _ _ _ h'
  | [], _, _, _, _, _, _, _, _, h => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, [], _, h => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, _ :: _ :: _, _, h => by simp [SpChain] at h
  | _ :: _ :: _, _, _, _, _, _, _, [], _, h => by simp [SpChain] at h

theorem wsEnd_glued (L : SpLv) : L.wsEnd.glued = L.ws.glued ++ recClaims (recOf L) := by
  cases h : L.fin
  · simp [SpLv.wsEnd, SpLv.pending, h, glue_two, recOf, recClaims, SpLv.ws1]
  · simp [SpLv.wsEnd, SpLv.pending, h, glue_one, recOf, recClaims, SpLv.ws1]

theorem chain_glued : ∀ (cfg : List Whir.Level) (lvl : ℕ) (ws : WhirStateT) (F : Fs) (xs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) (Ls : List SpLv) (res : WhirEnd × FSt),
    SpChain logN lane lvl cfg ws F xs os R Ls res →
    (Ls.getLastD default).wsEnd.glued = ws.glued ++ (Ls.map recOf).flatMap recClaims
  | [level], lvl, ws, F, xs, os, R, [L], res, h => by
    obtain ⟨-, -, -, -, e5, -⟩ := h
    simp [wsEnd_glued, e5]
  | level :: next :: cfg, lvl, ws, F, xs, os, R, L :: Ls, res, h => by
    obtain ⟨-, -, -, -, e5, -, d, xsR, osR, -, -, -, h'⟩ := h
    have hl := (chain_at _ _ _ _ _ _ _ _ _ h').1
    have hlast : (L :: Ls).getLastD default = Ls.getLastD default := by
      cases Ls with
      | nil => simp at hl
      | cons _ _ => rfl
    rw [hlast, chain_glued _ _ _ _ _ _ _ _ _ h', wsEnd_glued, e5]
    simp
  | [], _, _, _, _, _, _, _, _, h => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, [], _, h => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, _ :: _ :: _, _, h => by simp [SpChain] at h
  | _ :: _ :: _, _, _, _, _, _, _, [], _, h => by simp [SpChain] at h

theorem chain_foldsNz : ∀ (cfg : List Whir.Level) (lvl : ℕ) (ws : WhirStateT) (F : Fs) (xs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) (Ls : List SpLv) (res : WhirEnd × FSt),
    SpChain logN lane lvl cfg ws F xs os R Ls res → (∀ x ∈ ws.folds, x ≠ 0) →
    ∀ x ∈ (Ls.getLastD default).wsEnd.folds, x ≠ 0
  | [level], lvl, ws, F, xs, os, R, [L], res, h, h0 => by
    obtain ⟨-, -, -, -, e5, -, hOk, -⟩ := h
    intro x hx
    simp only [List.getLastD_cons, List.getLastD_nil, SpLv.wsEnd_folds, e5, List.mem_append] at hx
    rcases hx with hx | hx
    · exact h0 x hx
    · exact hOk.chs x hx
  | level :: next :: cfg, lvl, ws, F, xs, os, R, L :: Ls, res, h, h0 => by
    obtain ⟨-, -, -, -, e5, -, d, xsR, osR, hOk, -, -, h'⟩ := h
    have hl := (chain_at _ _ _ _ _ _ _ _ _ h').1
    have hlast : (L :: Ls).getLastD default = Ls.getLastD default := by
      cases Ls with
      | nil => simp at hl
      | cons _ _ => rfl
    rw [hlast]
    refine chain_foldsNz _ _ _ _ _ _ _ _ _ h' fun x hx ↦ ?_
    rw [SpLv.wsEnd_folds, e5, List.mem_append] at hx
    rcases hx with hx | hx
    · exact h0 x hx
    · exact hOk.chs x hx
  | [], _, _, _, _, _, _, _, _, h, _ => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, [], _, h, _ => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, _ :: _ :: _, _, h, _ => by simp [SpChain] at h
  | _ :: _ :: _, _, _, _, _, _, _, [], _, h, _ => by simp [SpChain] at h

/-- A level's facts `LevelsOk` gives. -/
structure LvOkAt (c : OsCfg) (logN lvl : ℕ) (lv : OsLv) (level : Whir.Level) : Prop where
  b : LvB c lvl lv level lv.logCols
  fold : level.fold = lv.folds
  grind : level.foldGrinding = lv.foldGrind
  f1 : 1 ≤ lv.folds
  ml : logN - (lv.foldsOff + lv.folds) = lv.logCols

theorem levelsOk_at {c : OsCfg} : ∀ (lvl : ℕ) (lvs : List OsLv) (cfg : List Whir.Level),
    LevelsOk c logN lvl lvs cfg → lvs.length = cfg.length ∧
      ∀ i < lvs.length, LvOkAt c logN (lvl + i) (lvs.getD i default) (cfg.getD i ⟨0, 0, 0, 0⟩) ∧
        (i + 1 < lvs.length → lvl + i ≠ c.yrLevel ∧ (lvl + i + 1) * ligColsCap < u128Bound) ∧
        (i + 1 = lvs.length → lvl + i = c.yrLevel ∧ 2 ^ (lvs.getD i default).logCols = c.yrLen)
  | lvl, [lv], [level], h => by
    obtain ⟨hcfg, hfold, hgr, h4, hml, hlen, hfin⟩ := h
    refine ⟨rfl, fun i hi ↦ ?_⟩
    obtain rfl : i = 0 := by simpa using hi
    exact ⟨⟨hcfg, hfold, hgr, h4, hml⟩, fun h ↦ absurd h (by simp), fun _ ↦ ⟨hfin, hlen⟩⟩
  | lvl, lv :: lv' :: lvs, level :: next :: cfg, h => by
    obtain ⟨hcfg, hfold, hgr, h4, hml, hm, hlvl, hnf, hoff', hshape, hrest⟩ := h
    obtain ⟨hl, hat⟩ := levelsOk_at (lvl + 1) (lv' :: lvs) (next :: cfg) hrest
    refine ⟨by simp only [List.length_cons] at hl ⊢; omega, fun i hi ↦ ?_⟩
    rcases i with _ | i
    · exact ⟨⟨hcfg, hfold, hgr, h4, hml⟩, fun _ ↦ ⟨hnf, hlvl⟩, fun h ↦ absurd h (by simp)⟩
    · obtain ⟨a, b, d⟩ := hat i (by simpa using hi)
      simp only [List.getD_cons_succ, List.length_cons] at a b d ⊢
      rw [show lvl + (i + 1) = lvl + 1 + i by ring]
      exact ⟨a, fun h ↦ b (by omega), fun h ↦ d (by omega)⟩
  | _, [], _, h => by simp [LevelsOk] at h
  | _, [_], [], h => by simp [LevelsOk] at h
  | _, [_], _ :: _ :: _, h => by simp [LevelsOk] at h
  | _, _ :: _ :: _, [], h => by simp [LevelsOk] at h
  | _, _ :: _ :: _, [_], h => by simp [LevelsOk] at h

/-- **The trace fits the candidate**, level by level. -/
structure TrFit (c : OsCfg) (tr : OsTr) : Prop where
  len : tr.Ls.length = c.levels.length
  fit : ∀ i < c.levels.length, SpLvFit c i (lvAt c i) (tr.L i)
  lvb : ∀ i < c.levels.length, LvB c i (lvAt c i) (tr.L i).level (lvAt c i).logCols
  off : ∀ i < c.levels.length, (tr.L i).ws.folds.length = (lvAt c i).foldsOff
  ok : ∀ i < c.levels.length, ∃ R d, (tr.L i).Ok R d
  pre : ∀ i < c.levels.length, (tr.L i).wsEnd.folds <+: tr.Fall
  roots : ∀ i, i + 1 < c.levels.length → (tr.L (i + 1)).root = (tr.L i).dn
  lf : tr.Lf = tr.L (c.levels.length - 1)
  tcLen : tr.Tc.length = c.yrLog
  tcNz : ∀ x ∈ tr.Tc, x ≠ 0
  fallNz : ∀ x ∈ tr.Fall, x ≠ 0
  glued : tr.Lf.wsEnd.glued = tr.rs.flatMap recClaims

theorem getLastD_eq_getD {α : Type} [Inhabited α] : ∀ (l : List α), l ≠ [] →
    l.getLastD default = l.getD (l.length - 1) default
  | [a], _ => rfl
  | a :: b :: l, _ => by
    rw [show (a :: b :: l).getLastD default = (b :: l).getLastD default from rfl,
      getLastD_eq_getD (b :: l) (by simp)]
    simp

/-- **The trace of an accepting run with no zero challenge fits the candidate.** -/
theorem trFit_of_run {c : OsCfg} {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg)
    {target : E} {q0 : List E} {F0 : Fs} {xs : List E} {os : List (List Opening)} {root : Digest}
    {Ls : List SpLv} {res : WhirEnd × FSt}
    (hch : SpChain μ ((cfg.head?.map (·.fold)).getD 0) 0 cfg ⟨target, q0, [], []⟩ F0 xs os
      [(root, stackShape μ r)] Ls res) :
    TrFit c ⟨Ls, xs.drop (Ls.map SpLv.words).flatten.length⟩ ∧ (Ls.getD 0 default).root = root ∧
      ChainEndP ((cfg.head?.map (·.fold)).getD 0) (Ls.getLastD default)
        (xs.drop (Ls.map SpLv.words).flatten.length) res := by
  set tr : OsTr := ⟨Ls, xs.drop (Ls.map SpLv.words).flatten.length⟩ with htr
  obtain ⟨hlc, hat, hws0, -, ⟨d0, hok0⟩, hnext⟩ := chain_at _ _ _ _ _ _ _ _ _ hch
  obtain ⟨hll, hlv⟩ := levelsOk_at 0 c.levels cfg hF.lok
  have hn := hF.n2
  have hlen : Ls.length = c.levels.length := by rw [hlc, hll]
  have hE := chain_end _ _ _ _ _ _ _ _ _ hch
  have hne : Ls ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
  have hlf : tr.Lf = tr.L (c.levels.length - 1) := by
    simp only [OsTr.Lf, OsTr.L, htr]; rw [getLastD_eq_getD _ hne, hlen]
  -- the folds before each level
  have hoff : ∀ i < c.levels.length, (tr.L i).ws.folds.length = (lvAt c i).foldsOff := by
    intro i hi
    induction i with
    | zero =>
      simp only [OsTr.L, htr, hws0]
      have := hF.off0
      rw [List.headD_eq_head?_getD, List.head?_eq_getElem?] at this
      simpa [lvAt, List.getD_eq_getElem?_getD] using this.symm
    | succ i ih =>
      have h1 := hnext i (by omega)
      simp only [OsTr.L, htr] at ih ⊢
      rw [h1.1, SpLv.wsEnd_folds, List.length_append, ih (by omega), SpLv.chs_length,
        (hat i (by omega)).level, (hlv i (by omega)).1.fold, hF.next i hi]
  have hfit : ∀ i < c.levels.length, SpLvFit c i (lvAt c i) (tr.L i) := by
    intro i hi
    obtain ⟨hk, hb, hd⟩ := hlv i hi
    rw [Nat.zero_add] at hk hb hd
    have ha : SpAt μ cfg 0 Ls.length i (tr.L i) := hat i (by omega)
    have hml' : (tr.L i).ml = (lvAt c i).logCols := by
      simp only [SpLv.ml, SpLv.ws1, List.length_append, SpLv.chs_length, ha.logN, ha.level,
        hk.fold, hoff i hi, hk.ml]
    refine ⟨by rw [ha.level, hk.fold], by rw [ha.level, hk.grind], hk.f1, hml', ?_, ?_⟩
    · simp only [SpLv.nsq, SpLv.D, hml', ha.level, ← hk.b.depth, hk.b.queries, hk.b.squeezes]
    · rw [ha.fin, hlen]
      constructor
      · intro h; exact (hd (by omega)).1
      · intro h
        by_contra h'
        exact (hb (by omega)).1 h
  refine ⟨⟨hlen, hfit, fun i hi ↦ ?_, hoff, fun i hi ↦ (hat i (by omega)).ok, fun i hi ↦ ?_,
    fun i hi ↦ chain_roots _ _ _ _ _ _ _ _ _ hch rfl i (by omega), hlf, ?_, ?_, ?_, ?_⟩,
    ?_, hE⟩
  · have ha : SpAt μ cfg 0 Ls.length i (tr.L i) := hat i (by omega)
    have hk := (hlv i hi).1
    rw [Nat.zero_add] at hk
    rw [ha.level]; exact hk.b
  · exact chain_folds _ _ _ _ _ _ _ _ _ hch i (by omega)
  · simp only [OsTr.Tc, tailChs_length]
    rw [hlf, (hfit _ (by omega)).ml]
    have := hF.last
    rwa [getLastD_eq_getD _ (by intro h; rw [h] at hn; simp at hn)] at this
  · exact hE.nz
  · exact chain_foldsNz _ _ _ _ _ _ _ _ _ hch (by simp)
  · simp only [OsTr.Lf, OsTr.rs, htr]
    rw [chain_glued _ _ _ _ _ _ _ _ _ hch]; simp
  · have := hok0.root
    have hi0 := (hat 0 (by omega)).index
    rw [hi0] at this
    simp only [Nat.zero_add, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at this
    exact this.1.symm

end
end LeanVM.Guest.B1.Whir
