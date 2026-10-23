/-
  LeanVM.Guest.B1.Whir.OsLayout

  The levels of the stacked opening's run as a list, and the facts the chain gives each.
-/

module

public import LeanVM.Guest.B1.Whir.OsData
public import LeanVM.Guest.B1.Whir.OsCapRun
public import LeanVM.Guest.B1.Whir.OsSeg

/-!
# The levels as a list (TRIAGE #36)

`osLvsList`: each level's index, start (chain state, stream position, spec state, openings,
roots) and data, from the levels' data; the chain's, the memory's and the calls' recursive facts
are facts about its members.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- A level: its index, its start and its data. -/
structure OsLvP where
  lvl : ℕ
  cv : Digest
  p : ℕ
  w : WhirState
  osp : List Opening
  roots : List (Digest × ℕ × ℕ)
  H : OsLvH

/-- The levels from level `lvl`. -/
def osLvsList (cfg : OsCfg) (xs : List E) :
    ℕ → Digest → ℕ → WhirState → List Opening → List (Digest × ℕ × ℕ) → List OsLvH → List OsLvP
  | _, _, _, _, _, _, [] => []
  | lvl, cv, p, w, osp, roots, H :: Hs =>
    ⟨lvl, cv, p, w, osp, roots, H⟩ :: osLvsList cfg xs (lvl + 1) (osHCvEnd cfg lvl xs p H.cv1) (osHPEnd cfg lvl p)
      (osHWEnd cfg lvl xs p H) H.osq (osHRootsEnd cfg lvl roots H) Hs

theorem os_lvsList_length (cfg : OsCfg) (xs : List E) : ∀ (Hs : List OsLvH) lvl cv p w osp roots,
    (osLvsList cfg xs lvl cv p w osp roots Hs).length = Hs.length
  | [], _, _, _, _, _, _ => rfl
  | H :: Hs, lvl, cv, p, w, osp, roots => by
    simp only [osLvsList, List.length_cons, os_lvsList_length cfg xs Hs]

/-- A level's memory facts, from the levels'. -/
theorem os_lvsMem_mem {rd : Reader} {cfg : OsCfg} {xs : List E} {cur : E} {P : OsPtrs} {sqz : ℕ → E} :
    ∀ (Hs : List OsLvH) lvl cv p w osp roots,
      (∀ L ∈ osLvsList cfg xs lvl cv p w osp roots Hs,
        OsLvMem rd cfg L.lvl xs L.p L.H (L.roots.getD L.lvl default).1 P (sqz L.lvl) cur) →
      OsLvsMem rd cfg xs cur P sqz lvl cv p w roots Hs
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: Hs, _, _, _, _, _, _, h =>
    ⟨h _ List.mem_cons_self, os_lvsMem_mem Hs _ _ _ _ _ _ fun L hL => h L (List.mem_cons_of_mem _ hL)⟩

/-- A level's call hypotheses, from the levels'. -/
theorem os_lvsCallH_mem {CA CB Csq : ℕ → CallRel} {cfg : OsCfg} {xs : List E} {cur : E} {P : OsPtrs}
    {sqz rew : ℕ → E} : ∀ (Hs : List OsLvH) lvl cv p w osp roots,
      (∀ L ∈ osLvsList cfg xs lvl cv p w osp roots Hs,
        OsLvCallH (CA L.lvl) (CB L.lvl) (Csq L.lvl) cfg L.lvl xs L.p L.H (L.roots.getD L.lvl default).1 P (sqz L.lvl)
          (rew L.lvl) cur) →
      OsLvsCallH CA CB Csq cfg xs cur P sqz rew lvl p w roots Hs
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: Hs, _, _, _, _, _, _, h =>
    ⟨h _ List.mem_cons_self, os_lvsCallH_mem Hs _ _ _ _ _ _ fun L hL => h L (List.mem_cons_of_mem _ hL)⟩

/-- What the chain says of a level. -/
structure OsLvFacts (cfg : OsCfg) (μ : ℕ) (xs : List E) (Lall : List Whir.Level)
    (Q : List (ℕ × List (ℕ × Opening))) (L : OsLvP) : Prop where
  ok : OsLvOk cfg L.lvl xs L.p μ (Lall.getD L.lvl default) L.cv L.w L.osp L.roots L.H
  root : ∃ rt, L.roots[L.lvl]? = some (rt, (cfg.lv L.lvl).depth,
    oqR (if L.lvl = 0 then 1 else 0) (2 ^ (cfg.lv L.lvl).folds))
  step : ((cfg.lv L.lvl).depth, (osHQs cfg L.lvl xs L.p L.H.cv1).zip L.osp) ∈ Q

/-- **The chain's facts of each level.** -/
theorem os_chain_mem {cfg : OsCfg} {μ lane : ℕ} {xs : List E} {Lall : List Whir.Level} {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))} : ∀ (Hs : List OsLvH) lvl cv p w osp roots,
      OsChain cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs →
      ∀ L ∈ osLvsList cfg xs lvl cv p w osp roots Hs, OsLvFacts cfg μ xs Lall Q L
  | [], _, _, _, _, _, _, h => h.elim
  | H :: Hs, lvl, cv, p, w, osp, roots, h => by
    obtain ⟨hok, ⟨rt, hrt, hq⟩, hl, hn⟩ := h
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL'
    · exact ⟨hok, ⟨rt, hrt⟩, hq⟩
    · by_cases hy : lvl = cfg.yrLevel
      · obtain ⟨rfl, -⟩ := hl hy
        simp [osLvsList] at hL'
      · exact os_chain_mem Hs _ _ _ _ _ _ (hn hy) L hL'

/-- The levels' indices. -/
theorem os_lvsList_lvl (cfg : OsCfg) (xs : List E) : ∀ (Hs : List OsLvH) lvl cv p w osp roots,
    ∀ i (hi : i < (osLvsList cfg xs lvl cv p w osp roots Hs).length),
      ((osLvsList cfg xs lvl cv p w osp roots Hs)[i]).lvl = lvl + i
  | [], _, _, _, _, _, _, i, hi => absurd hi (by simp [osLvsList])
  | H :: Hs, lvl, cv, p, w, osp, roots, i, hi => by
    rcases i with _ | i
    · rfl
    · simp only [osLvsList, List.getElem_cons_succ]
      rw [os_lvsList_lvl cfg xs Hs _ _ _ _ _ _ i (by simpa [osLvsList] using hi)]
      ring

end
end LeanVM.Guest.B1
