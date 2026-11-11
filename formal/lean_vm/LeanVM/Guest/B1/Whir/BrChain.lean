/-
  LeanVM.Guest.B1.Whir.BrChain

  The Spec's honest chain of levels gives the guest's levels' hypotheses.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.BrLevelH

/-!
# The chain of levels

`spDats Ls lvl wp`: the levels' data from the trace's levels `Ls` (level `i`'s row weights buffer
at `wp i`). `LvMemB`: a level's memory but its words. `lvsH_sp`: a chain
of the trace (`SpChain`) whose words memory holds from `cur`, each level's memory and calls given,
gives the levels' hypotheses `LvsH`, and what the levels leave is the last level's: its sponge,
quadratic and claim, the cursor at the tail's words (`ChainEnd`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

instance : Inhabited Fs := ⟨⟨[], []⟩⟩

instance : Inhabited SpLv :=
  ⟨{ logN := 0, index := 0, level := ⟨0, 0, 0⟩, fin := false, ws := ⟨0, [], [], []⟩, F := ⟨[], []⟩,
     xf := [], ra := 0, rb := 0, y := 0, c0 := 0, c2 := 0, ms := [], nonce := 0, os := [],
     ic0 := 0, ic2 := 0, root := Vector.replicate 4 0, height := 0, width := 0 }⟩

/-- The next commitment's digest a level reads (any, at the last level). -/
def SpLv.dn (L : SpLv) : Digest := (digestFromHalves (L.ra, L.rb)).getD (Vector.replicate 4 0)

theorem SpLv.dn_of {L : SpLv} {d : Digest} (h : digestFromHalves (L.ra, L.rb) = some d) :
    digestFromHalves (L.ra, L.rb) = some L.dn := by
  rw [SpLv.dn, h]; rfl

/-- The levels' data from the trace's levels. -/
def spDats : List SpLv → ℕ → (ℕ → E) → List LvDat
  | [], _, _ => []
  | L :: Ls, i, wp => spDat L L.dn (wp i) :: spDats Ls (i + 1) wp

/-- A level's memory, but its words. -/
structure LvMemB (rd : Reader) (P : OsPtrs) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (L : SpLv) :
    Prop where
  fch : ∀ j < lv.folds, LoadHolds rd P.fch (lv.foldsOff + j) (L.chs.getD j 0)
  r0 : LoadHolds rd P.roots (2 * lvl) (digestHalves L.root).1
  r1 : LoadHolds rd P.roots (2 * lvl + 1) (digestHalves L.root).2
  mu : LoadHolds rd P.mus lvl L.lam⁻¹
  beta : LoadHolds rd P.betas lvl
    ((if lvl = c.yrLevel then L.lam else L.lam * L.lam) * L.lam ^ lv.queries)
  r0' : lvl ≠ c.yrLevel → LoadHolds rd P.roots (2 * lvl + 2) L.ra
  r1' : lvl ≠ c.yrLevel → LoadHolds rd P.roots (2 * lvl + 3) L.rb
  oodz : lvl ≠ c.yrLevel →
    ReadsAt rd (P.oodz * gen ^ ((lvl + 1) * ligColsCap)) (oodZ L.F1 L.ra L.rb L.ml)
  ood : lvl ≠ c.yrLevel →
    ReadsAt rd (P.ood * gen ^ ((lvl + 1) * oodSlots)) [L.lam, L.y, L.c0, L.c2]
  fmsg : lvl = c.yrLevel → ReadsAt rd P.fmsg L.ms

theorem LvMemB.withWords {rd : Reader} {P : OsPtrs} {c : OsCfg} {lvl : ℕ} {lv : OsLv} {L : SpLv}
    {cur : E} (h : LvMemB rd P c lvl lv L) (hw : ReadsAt rd cur L.words) :
    LvMem rd P c lvl lv L cur :=
  ⟨hw, h.fch, h.r0, h.r1, h.mu, h.beta, h.r0', h.r1', h.oodz, h.ood, h.fmsg⟩

/-- What the levels leave: the last level's sponge, quadratic and claim, the cursor at the tail's
words, the run's end. -/
structure ChainEnd (rd : Reader) (lane : ℕ) (O : Fs × List E × E × E) (Lf : SpLv) (xsR : List E)
    (res : WhirEnd × FSt) : Prop where
  F : O.1 = Lf.Fend
  quad : O.2.1 = Lf.wsEnd.quad
  t : O.2.2.1 = Lf.wsEnd.target
  reads : ReadsAt rd O.2.2.2 xsR
  fin : Lf.fin = true
  len : 2 * (Lf.ml - 1) ≤ xsR.length
  nz : ∀ c ∈ (tailTr Lf.ml Lf.Fend Lf.wsEnd.quad Lf.wsEnd.target xsR).2.1, c ≠ 0
  res : ∃ (osR : List (List Opening)) (R : List (Digest × ℕ × ℕ)), Lf.Ok R (Vector.replicate 4 0) ∧
    res = (Lf.wend lane xsR, ⟨(tailTr Lf.ml Lf.Fend Lf.wsEnd.quad Lf.wsEnd.target xsR).1,
      xsR.drop (2 * (Lf.ml - 1)), osR, R⟩)

theorem words_length {c : OsCfg} {lvl : ℕ} {lv : OsLv} {L : SpLv} (h : SpLvFit c lvl lv L)
    {R : List (Digest × ℕ × ℕ)} {d : Digest} (hOk : L.Ok R d)
    (hyl : lvl = c.yrLevel → 2 ^ lv.logCols = c.yrLen) : L.words.length = lvWords c lvl lv := by
  unfold SpLv.words lvWords
  by_cases hf : lvl = c.yrLevel
  · have hL : L.fin = true := h.fin.mpr hf
    simp only [hL, hf, ↓reduceIte, List.length_append, List.length_cons, List.length_nil,
      hOk.xf, h.fold, hOk.ms hL, h.ml, hyl hf]
  · have hL : L.fin = false := by
      cases e : L.fin
      · rfl
      · exact absurd (h.fin.mp e) hf
    simp only [hL, hf, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_cons,
      List.length_nil, hOk.xf, h.fold]

/-- **The chain of levels gives the levels' hypotheses.** -/
theorem lvsH_sp {C : CallRel} {rd : Reader} {P : OsPtrs} {Rs : E} {c : OsCfg} {logN lane : ℕ}
    (wp : ℕ → E) : ∀ (lvs : List OsLv) (cfg : List Whir.Level) (lvl : ℕ) (ws : WhirStateT)
    (F : Fs) (xs : List E) (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) (Ls : List SpLv)
    (res : WhirEnd × FSt) (cur : E),
    LevelsOk c logN lvl lvs cfg → SpChain logN lane lvl cfg ws F xs os R Ls res →
    ws.folds.length = (lvs.headD default).foldsOff → ReadsAt rd cur xs →
    (∀ i < lvs.length, LvMemB rd P c (lvl + i) (lvs.getD i default) (Ls.getD i default)) →
    (∀ i < lvs.length, LvCallsOk C rd P Rs c (lvl + i) (lvs.getD i default) (Ls.getD i default)
      (wp (lvl + i))) →
    LvsH C rd P Rs c lvl lvs (spDats Ls lvl wp) F ws.quad ws.target cur ∧
      ChainEnd rd lane (lvsOut c lvl lvs (spDats Ls lvl wp) F ws.quad ws.target cur)
        (Ls.getLastD default) (xs.drop (Ls.map SpLv.words).flatten.length) res
  | [lv], [level], lvl, ws, F, xs, os, R, [L], res, cur, hok, hch, hfo, hrd, hmem, hcal => by
    obtain ⟨hcfg, hfold, h4, hml, hlen, hfin⟩ := hok
    obtain ⟨e1, e2, e3, e4, e5, e6, hOk, xsR, osR, hxs, hos, htl, htnz, hres⟩ := hch
    subst e5 e6
    simp only [List.headD_cons] at hfo
    have hfit : SpLvFit c lvl lv L := by
      refine ⟨by rw [e3, hfold], h4, ?_, ?_, ⟨fun _ ↦ hfin, fun _ ↦ e4⟩⟩
      · simp only [SpLv.ml, SpLv.ws1, List.length_append, SpLv.chs_length, e1, e3, hfo, hfold, hml]
      · have hml' : L.ml = lv.logCols := by
          simp only [SpLv.ml, SpLv.ws1, List.length_append, SpLv.chs_length, e1, e3, hfo, hfold, hml]
        simp only [SpLv.nsq, SpLv.D, hml', e3, ← hcfg.depth, hcfg.queries, hcfg.squeezes]
    have hm0 := hmem 0 (by simp)
    have hcl := hcal 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at hm0 hcl
    have hm := hm0.withWords (cur := cur) (readsAt_left (xs := L.words) (by rw [← hxs]; exact hrd))
    have hH := lvH_sp (d := L.dn) (wp := wp lvl) hfit (e3 ▸ hcfg) (fun h ↦ absurd hfin h) (fun _ ↦ hlen) hOk
      (fun h ↦ by rw [e4] at h; cases h) hm hcl
    have hdr : xs.drop ([L].map SpLv.words).flatten.length = xsR := by
      rw [hxs]; simp
    rw [hdr]
    refine ⟨⟨hH, trivial⟩, ?_⟩
    have hO := lvOut_sp hfit L.dn (wp lvl)
    simp only [spDats, lvsOut]
    rw [hO, show [L].getLastD default = L from rfl]
    refine ⟨rfl, rfl, rfl, ?_, e4, htl, htnz, ⟨osR, R, hOk, hres⟩⟩
    have := readsAt_right (by rw [← hxs]; exact hrd)
    rwa [words_length hfit hOk (fun _ ↦ hlen)] at this
  | lv :: lv' :: lvs, level :: next :: cfg, lvl, ws, F, xs, os, R, L :: Ls, res, cur, hok, hch,
      hfo, hrd, hmem, hcal => by
    obtain ⟨hcfg, hfold, h4, hml, hm1, hlvl, hnf, hoff', hshape, hrest⟩ := hok
    obtain ⟨e1, e2, e3, e4, e5, e6, d, xsR, osR, hOk, hxs, hos, hch'⟩ := hch
    subst e5 e6
    simp only [List.headD_cons] at hfo
    have hml' : L.ml = lv.logCols := by
      simp only [SpLv.ml, SpLv.ws1, List.length_append, SpLv.chs_length, e1, e3, hfo, hfold, hml]
    have hfit : SpLvFit c lvl lv L := by
      refine ⟨by rw [e3, hfold], h4, hml', ?_, ⟨fun h ↦ (by rw [e4] at h; cases h),
        fun h ↦ absurd h hnf⟩⟩
      simp only [SpLv.nsq, SpLv.D, hml', e3, ← hcfg.depth, hcfg.queries, hcfg.squeezes]
    have hm0 := hmem 0 (by simp)
    have hcl := hcal 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at hm0 hcl
    have hm := hm0.withWords (cur := cur) (readsAt_left (xs := L.words) (by rw [← hxs]; exact hrd))
    have hH := lvH_sp (d := L.dn) (wp := wp lvl) hfit (e3 ▸ hcfg) (fun _ ↦ hlvl) (fun h ↦ absurd h hnf) hOk
      (fun h ↦ SpLv.dn_of (hOk.digest h)) hm hcl
    have hO := lvOut_sp hfit L.dn (wp lvl)
    have hwl := words_length hfit hOk (fun h ↦ absurd h hnf)
    have hfo' : L.wsEnd.folds.length = ((lv' :: lvs).headD default).foldsOff := by
      rw [SpLv.wsEnd_folds, List.length_append, SpLv.chs_length, hfo, e3, hfold, List.headD_cons,
        hoff']
    have hrd' : ReadsAt rd (cur * gen ^ lvWords c lvl lv) xsR := by
      have := readsAt_right (by rw [← hxs]; exact hrd); rwa [hwl] at this
    obtain ⟨hH', hE⟩ := lvsH_sp wp (lv' :: lvs) (next :: cfg) (lvl + 1) L.wsEnd L.Fend xsR
      osR _ Ls res (cur * gen ^ lvWords c lvl lv) hrest hch' hfo' hrd'
      (fun i hi ↦ by
        have := hmem (i + 1) (by simp at hi ⊢; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      (fun i hi ↦ by
        have := hcal (i + 1) (by simp at hi ⊢; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    have hdr : xs.drop ((L :: Ls).map SpLv.words).flatten.length =
        xsR.drop (Ls.map SpLv.words).flatten.length := by
      rw [hxs]; simp [List.drop_append]
    rw [hdr]
    refine ⟨⟨hH, ?_⟩, ?_⟩
    · rw [hO]; exact hH'
    · simp only [spDats, lvsOut]
      rw [hO]
      have hl : (L :: Ls).getLastD default = Ls.getLastD default := by
        cases Ls with
        | nil => simp [SpChain] at hch'
        | cons _ _ => rfl
      rw [hl]; exact hE
  | [], _, _, _, _, _, _, _, _, _, _, hok, _, _, _, _, _ => by simp [LevelsOk] at hok
  | [_], [], _, _, _, _, _, _, _, _, _, hok, _, _, _, _, _ => by simp [LevelsOk] at hok
  | [_], _ :: _ :: _, _, _, _, _, _, _, _, _, _, hok, _, _, _, _, _ => by simp [LevelsOk] at hok
  | _ :: _ :: _, [], _, _, _, _, _, _, _, _, _, hok, _, _, _, _, _ => by simp [LevelsOk] at hok
  | _ :: _ :: _, [_], _, _, _, _, _, _, _, _, _, hok, _, _, _, _, _ => by simp [LevelsOk] at hok
  | [_], [_], _, _, _, _, _, _, [], _, _, _, hch, _, _, _, _ => by simp [SpChain] at hch
  | [_], [_], _, _, _, _, _, _, _ :: _ :: _, _, _, _, hch, _, _, _, _ => by simp [SpChain] at hch
  | _ :: _ :: _, _ :: _ :: _, _, _, _, _, _, _, [], _, _, _, hch, _, _, _, _ => by
    simp [SpChain] at hch

end
end LeanVM.Guest.B1.Whir
