/-
  LeanVM.Guest.B1.VsC.Os.LeftOs

  `open_stacked`'s honest data tied to the run's openings.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftPre

/-!
# The honest data's openings are the run's

`LvsAtRun.os_drop`: level `i` of a run starts at the openings `os.drop i`; `LvsAtRun.phase_eq`: its
phase is `os`'s `i`-th; `LvsAtRun.os_length`: `os` has a phase a level; `LvsAtRun.phase_idx`: its
openings sit at its positions. `HonRun.rows_os`, `HonRun.sibs_os`, `HonRun.qs_os`: the honest
data's rows, siblings and positions are the run's openings' leaves, paths below the cap and leaf
indices. `osHonest_of_openOs`: `osHonest_of_open` with these equations, which the pops need.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace LvsAtRun

variable {logN lane index : ℕ} {levels : List Whir.Level} {s : WhirState} {cap : List E}
  {R : List (Digest × ℕ × ℕ)} {xs : List E} {os : List (List Opening)} {w : WhirEnd} {L : List LvAt}
  (h : LvsAtRun logN lane index levels s cap R xs os w L)
include h

/-- **Level `i` starts at the openings `os.drop i`.** -/
theorem os_drop (i : ℕ) (hi : i < L.length) : (L.getD i default).os = os.drop i := by
  induction i with
  | zero => exact (h.start hi).2.2.2.2
  | succ i ih =>
    obtain ⟨_, _, -, -, -, -, hos, -⟩ := h.next i hi
    have ih := ih (by omega)
    rw [hos] at ih
    rw [← List.tail_drop, ← ih]
    rfl

/-- **Level `i`'s phase is `os`'s `i`-th.** -/
theorem phase_eq (i : ℕ) (hi : i < L.length) : (L.getD i default).phase = os.getD i [] := by
  have hd := os_drop h i hi
  by_cases hn : i + 1 < L.length
  · obtain ⟨_, W, hdd, -, -, -, hos, -⟩ := h.next i hn
    rw [hos] at hd
    rw [LvAt.phase, hdd, List.getD_eq_getElem?_getD, ← List.head?_drop, ← hd]
    rfl
  · have hl : i = L.length - 1 := by omega
    obtain ⟨_, W, hdd, -, -, -, hos, -⟩ := h.fin (by omega)
    rw [← hl] at hdd hos
    rw [hos] at hd
    rw [LvAt.phase, hdd, List.getD_eq_getElem?_getD, ← List.head?_drop, ← hd]
    rfl

/-- **`os` has a phase a level.** -/
theorem os_length (hpos : 0 < L.length) : os.length = L.length := by
  obtain ⟨_, _, -, -, -, -, hos, -⟩ := h.fin hpos
  have hd := os_drop h (L.length - 1) (by omega)
  rw [hos] at hd
  have := congrArg List.length hd
  simp only [List.length_cons, List.length_nil, List.length_drop] at this
  omega

/-- **Level `i`'s openings sit at its positions** (`openPhase`'s acceptance). -/
theorem phase_idx (i : ℕ) (hi : i < L.length) :
    (L.getD i default).phase.map Opening.leafIndex = (L.getD i default).qs logN := by
  by_cases hn : i + 1 < L.length
  · obtain ⟨rw, W, hd, -, -, -, -, hok, -⟩ := h.next i hn
    have hrw : (L.getD i default).rw = rw := by unfold LvAt.rw; rw [hd]
    have e : ∀ x, x = rw → W.phase.map Opening.leafIndex =
        W.qs (rsF (L.getD i default).level (L.getD i default).cap x)
          (logN - (rsSt (L.getD i default).level (L.getD i default).s (L.getD i default).cap x).alphas.length)
          (logN - (rsSt (L.getD i default).level (L.getD i default).s (L.getD i default).cap x).alphas.length +
            (L.getD i default).level.logInvRate) (L.getD i default).level.queries := by
      rintro x rfl; exact hok.idx
    have := e _ hrw
    unfold LvAt.phase LvAt.qs
    rw [hd]
    exact this
  · obtain rfl : i = L.length - 1 := by omega
    obtain ⟨rw, W, hd, -, -, -, -, hok, -⟩ := h.fin (by omega)
    have hrw : (L.getD (L.length - 1) default).rw = rw := by unfold LvAt.rw; rw [hd]
    have e : ∀ x, x = rw → W.phase.map Opening.leafIndex =
        W.qs (rsF (L.getD (L.length - 1) default).level (L.getD (L.length - 1) default).cap x)
          (logN - (rsSt (L.getD (L.length - 1) default).level (L.getD (L.length - 1) default).s
            (L.getD (L.length - 1) default).cap x).alphas.length +
            (L.getD (L.length - 1) default).level.logInvRate) (L.getD (L.length - 1) default).level.queries := by
      rintro x rfl; exact hok.idx
    have := e _ hrw
    unfold LvAt.phase LvAt.qs
    rw [hd]
    exact this

end LvsAtRun

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **`os` has a phase a level.** -/
theorem os_len : os.length = (osCfgR (μ - minOpenLog) (r - 1)).levels.length := by
  rw [hR.run.os_length (by rw [hR.len]; have := hR.n2; omega), hR.len]

/-- **The honest data's rows are the run's openings' leaves.** -/
theorem rows_os {cur tabs : E} {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) (k : ℕ) :
    (hR.osHonest (cur := cur) (tabs := tabs)).rows l k = ((os.getD l []).map (·.leaf)).getD k [] := by
  rw [hR.osHonest_fields.2.2.2.1]
  dsimp only
  rw [hR.run.phase_eq l (by rw [hR.len]; exact hl)]

/-- **The honest data's siblings are the run's openings' paths below the cap.** -/
theorem sibs_os {cur tabs : E} {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) (k : ℕ) :
    (hR.osHonest (cur := cur) (tabs := tabs)).sibs l k = ((os.getD l []).map (fun o ↦
      o.path.take (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth -
        ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).capDepth))).getD k [] := by
  rw [hR.osHonest_fields.2.2.2.2]
  dsimp only
  rw [hR.run.phase_eq l (by rw [hR.len]; exact hl)]

/-- **Level `l`'s positions are its openings' leaf indices**, one a query. -/
theorem qs_os {cur tabs : E} {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    (os.getD l []).length = oqQA (osCfgR (μ - minOpenLog) (r - 1)) l ∧
      ∀ k < oqQA (osCfgR (μ - minOpenLog) (r - 1)) l,
        (hR.osHonest (cur := cur) (tabs := tabs)).qs l k = ((os.getD l []).getD k ⟨0, [], []⟩).leafIndex := by
  have hlL : l < Ls.length := by rw [hR.len]; exact hl
  have hB := hR.lvb hl
  obtain ⟨-, hbase, -⟩ := hB.qsh
  have hcount : oqQA (osCfgR (μ - minOpenLog) (r - 1)) l =
      ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).queries := by
    simp only [oqQA]
    rw [oqSA, oq_base, hbase]
    simp only [oqCount, oqOddA, oqNA, lqOdd, lqIters, osLvA, lvBase]
    split_ifs <;> omega
  have hidx := hR.run.phase_idx l hlL
  rw [hR.run.phase_eq l hlL] at hidx
  have hlen : (os.getD l []).length = oqQA (osCfgR (μ - minOpenLog) (r - 1)) l := by
    have := congrArg List.length hidx
    rw [List.length_map, LvAt.qs_length, hB.q] at this
    rw [this, hcount]
  refine ⟨hlen, fun k hk => ?_⟩
  rw [hR.osHonest_fields.2.2.1]
  dsimp only
  have hk' : k < (os.getD l []).length := by omega
  rw [← hidx, List.getD_eq_getElem ((os.getD l []).map Opening.leafIndex) 0 (by simpa using hk'),
    List.getElem_map, List.getD_eq_getElem (os.getD l []) ⟨0, [], []⟩ hk']

end HonRun

end
end LeanVM.Guest.B1.Whir

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **The run's honest levels at a call of `open_stacked__L{m}`**: the capacity cells a Keccak
state's and `HonRun`, on which `HonRun.osHonest` and the `HonRun.lq*_os` lemmas apply. -/
theorem osHonRun_of_open {m r : ℕ} {root : Digest} {fsv : List E} {target : E} {xs : List E}
    {os : List (List Opening)} {w : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    {qs : List (ℕ × List ℕ)} (hm : m ≤ 14) (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (hcar : ∃ sp : Sponge, (⟨fsv, []⟩ : Fs).Carries sp)
    (hrun : RunsWith (whirOpen (minOpenLog + m) r target) ⟨fsv, []⟩ xs os
      [(root, stackShape (minOpenLog + m) r)] w s' roots')
    (hq : OpenRunQueries (minOpenLog + m) r root target ⟨fsv, []⟩ xs os qs) :
    ∃ (S : KeccakState) (cfg : List Whir.Level) (Ls : List LvAt), fsv = capOf S ∧
      HonRun (minOpenLog + m) r target S root xs os w cfg Ls := by
  obtain ⟨⟨st, pe, gr⟩, hc, hp, hg⟩ := hcar
  change capOf st = fsv at hc
  change pe = [] at hp
  change gr = none at hg
  subst hc hp hg
  have hca : CapsAgree (minOpenLog + m) r target st xs os root := by
    intro b hb
    have h := (hq ⟨st, [], none⟩ ⟨rfl, rfl, rfl⟩ [] []).1
    simp only [List.append_nil] at h
    exact h b hb
  obtain ⟨cfg, Ls, hR⟩ := honRun_of (by omega) (by show 16 + m ≤ 30; omega) hr1 hr4 hrun hca
  exact ⟨st, cfg, Ls, rfl, hR⟩

/-- **The body's honest data at a call of `open_stacked__L{m}`, its rows and siblings the run's
openings'.** -/
theorem osHonest_of_openOs {m r : ℕ} {root : Digest} {fsv : List E} {target : E} {xs : List E}
    {os : List (List Opening)} {w : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    {qs : List (ℕ × List ℕ)} (cur tabs : E) (hm : m ≤ 14) (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (hcar : ∃ sp : Sponge, (⟨fsv, []⟩ : Fs).Carries sp)
    (hrun : RunsWith (whirOpen (minOpenLog + m) r target) ⟨fsv, []⟩ xs os
      [(root, stackShape (minOpenLog + m) r)] w s' roots')
    (hq : OpenRunQueries (minOpenLog + m) r root target ⟨fsv, []⟩ xs os qs) :
    ∃ S : KeccakState, fsv = capOf S ∧ os.length = (osCfgR m (r - 1)).levels.length ∧
      ∃ H : OsHonestA (osCfgR m (r - 1))
        (rateSel r :: fsv ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs])
        cur tabs xs w.target w.inner w.residual (w.point ++ List.replicate (pointCap - (minOpenLog + m)) 0)
        (w.point.map (1 + ·) ++ List.replicate (pointCap - (minOpenLog + m)) 1),
      ∀ l < (osCfgR m (r - 1)).levels.length, (∀ k,
        H.rows l k = ((os.getD l []).map (·.leaf)).getD k [] ∧
        H.sibs l k = ((os.getD l []).map (fun o ↦
          o.path.take (((osCfgR m (r - 1)).levels.getD l default).depth -
            ((osCfgR m (r - 1)).levels.getD l default).capDepth))).getD k []) ∧
        (os.getD l []).length = oqQA (osCfgR m (r - 1)) l ∧
        ∀ k < oqQA (osCfgR m (r - 1)) l, H.qs l k = ((os.getD l []).getD k ⟨0, [], []⟩).leafIndex := by
  obtain ⟨⟨st, pe, gr⟩, hc, hp, hg⟩ := hcar
  change capOf st = fsv at hc
  change pe = [] at hp
  change gr = none at hg
  subst hc hp hg
  have hca : CapsAgree (minOpenLog + m) r target st xs os root := by
    intro b hb
    have h := (hq ⟨st, [], none⟩ ⟨rfl, rfl, rfl⟩ [] []).1
    simp only [List.append_nil] at h
    exact h b hb
  obtain ⟨cfg, Ls, hR⟩ := honRun_of (by omega) (by show 16 + m ≤ 30; omega) hr1 hr4 hrun hca
  have e : minOpenLog + m - minOpenLog = m := Nat.add_sub_cancel_left _ _
  have hlen := hR.os_len
  rw [e] at hlen
  refine ⟨st, rfl, hlen, ?_⟩
  have key := fun l (hl : l < (osCfgR (minOpenLog + m - minOpenLog) (r - 1)).levels.length) =>
    And.intro (fun k => And.intro (hR.rows_os (cur := cur) (tabs := tabs) hl k)
      (hR.sibs_os (cur := cur) (tabs := tabs) hl k)) (hR.qs_os (cur := cur) (tabs := tabs) hl)
  revert key
  generalize hR.osHonest (cur := cur) (tabs := tabs) = H
  revert H
  rw [e]
  exact fun H key => ⟨H, key⟩

end
end LeanVM.Guest.B1.VsC
