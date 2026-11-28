/-
  LeanVM.Guest.B1.VsC.Oq.LqHints

  `level_queries`' pops are a level's `levelHints`, stream by stream.
-/

module

public import LeanVM.Guest.B1.VsC.Oq.LqMain
public import LeanVM.Guest.B1.VsC.Oq.QueryPops

/-!
# `level_queries`' pops against `levelHints`

`LqA`'s pops are `LqCall.pops`: the cap's cells, the flags, then each query's `oqQE`. At the honest
call of a level (`lqCapW`, `lqFlW` the cap and flags `levelHints` builds, query `k`'s witness its
opening's leaf index, leaf and path below the cap, `lqWs`), they are `levelHints`' entries stream by
stream (`lq_pops_sameStreams`): each query's entries its opening's (`oqQE_entries`, memory-free),
the cap's moved before the queries' (`level_sameStreams`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A query's row cells are its leaf's cells**, at every valuation. -/
theorem QD.rowVals_eq (d : QD) {first : Bool} (hfirst : d.s.base = 1 ↔ first = true)
    (hrow : d.row.length = rowLen d.s.base d.s.folds) : d.rowVals = Hints.leafCells first d.row := by
  unfold QD.rowVals
  by_cases hb : d.s.base = 1
  · have hf : first = true := hfirst.mp hb
    subst hf
    rw [Hints.leafCells, ite_eq_left rfl]
    rw [rowLen, ite_eq_left hb] at hrow
    refine List.ext_getElem (by simp [Oq.I, hrow]) fun i h1 h2 => ?_
    simp [QD.cell, hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < d.row.length by simpa using h2)]
  · have hf : first = false := by cases first <;> simp_all
    subst hf
    rw [Hints.leafCells, ite_eq_right (by simp)]
    rw [rowLen, ite_eq_right hb] at hrow
    refine List.ext_getElem (by simp [Oq.I, hrow]) fun i h1 h2 => ?_
    simp [QD.cell, hb]

/-- **A query's entries are its opening's**: its witness the opening's leaf index, leaf and path
below the cap, in a tree of any height `D`. -/
theorem oqQE_entries (s : Oq) (D : ℕ) {first : Bool} (o : Opening) (hfirst : s.base = 1 ↔ first = true)
    (hrow : o.leaf.length = rowLen s.base s.folds) (hl : s.pd ≤ o.path.length) :
    oqQE s (o.leafIndex, o.leaf, o.path.take s.pd) = queryEntries first D s.pd o := by
  unfold oqQE
  rw [QD.rowVals_eq _ hfirst hrow,
    WD.wpPops_eq (oqQD s 0 0 true 0 0 0 0 [] [] (o.leafIndex, o.leaf, o.path.take s.pd)).wd (D := D)
      (path := o.path) rfl hl]
  rfl

end

end LeanVM.Guest.B1

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem flatMap_map' {α β γ : Type} (g : α → β) (f : β → List γ) :
    ∀ l : List α, (l.map g).flatMap f = l.flatMap fun a => f (g a)
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.flatMap_cons, flatMap_map' g f l]

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr' fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem flatMap_range_getD {α β : Type} (d : α) (f : α → List β) :
    ∀ L : List α, (List.range L.length).flatMap (fun k => f (L.getD k d)) = L.flatMap f
  | [] => rfl
  | x :: L => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, flatMap_map', List.flatMap_cons]
    congr 1
    exact flatMap_range_getD d f L

/-- A phase's opening `k`. -/
def opAt (phase : List Opening) (k : ℕ) : Opening := phase.getD k ⟨0, [], []⟩

/-- Query `k`'s witness at a level whose paths run `pd` levels below the cap: its opening's leaf
index, leaf and path below the cap. -/
def lqWs (pd : ℕ) (phase : List Opening) (k : ℕ) : QW :=
  ((opAt phase k).leafIndex, (opAt phase k).leaf, (opAt phase k).path.take pd)

/-- The cap's cells `levelHints` pushes (`merkle_caps`). -/
def lqCapW (depth count : ℕ) (phase : List Opening) : List E :=
  ((levelCapPushes depth count phase).headD ("", [])).2

/-- The flags `levelHints` pushes (`merkle_cap_active`). -/
def lqFlW (depth count : ℕ) (phase : List Opening) : List E :=
  ((levelCapPushes depth count phase).getD 1 ("", [])).2

theorem levelCapPushes_eq (depth count : ℕ) (phase : List Opening) :
    levelCapPushes depth count phase =
      [("merkle_caps", lqCapW depth count phase), ("merkle_cap_active", lqFlW depth count phase)] := rfl

/-- **`level_queries`' pops are its level's `levelHints`**, stream by stream, at the honest cap,
flags and witnesses. -/
theorem lq_pops_sameStreams {l : LqCall} {s : Oq} {first : Bool} {depth : ℕ} {phase : List Opening}
    (hcap : l.capW = lqCapW depth phase.length phase) (hfl : l.flW = lqFlW depth phase.length phase)
    (hws : ∀ k < phase.length, l.ws k = lqWs s.pd phase k)
    (hpd : s.pd = depth - Hints.capDepthOf phase.length depth) (hfirst : s.base = 1 ↔ first = true)
    (hrow : ∀ o ∈ phase, o.leaf.length = rowLen s.base s.folds) (hl : ∀ o ∈ phase, s.pd ≤ o.path.length) :
    SameStreams (l.pops phase.length s) (Hints.levelHints first depth phase.length phase) := by
  have hq : (List.range phase.length).flatMap (fun k => oqQE s (l.ws k)) =
      levelPushes first depth phase.length phase := by
    have e1 : (List.range phase.length).flatMap (fun k => oqQE s (l.ws k)) =
        (List.range phase.length).flatMap (fun k => queryEntries first depth s.pd (phase.getD k ⟨0, [], []⟩)) := by
      refine flatMap_congr' fun k hk => ?_
      have hk' := List.mem_range.mp hk
      have hm : phase.getD k ⟨0, [], []⟩ ∈ phase := by
        rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk'
      rw [hws k hk']
      exact oqQE_entries s depth _ hfirst (hrow _ hm) (hl _ hm)
    rw [e1, levelPushes, ← hpd]
    exact flatMap_range_getD _ (queryEntries first depth s.pd) phase
  have hpops : l.pops phase.length s =
      levelCapPushes depth phase.length phase ++ levelPushes first depth phase.length phase := by
    rw [levelCapPushes_eq, ← hcap, ← hfl, ← hq]; rfl
  rw [hpops]
  exact level_sameStreams first depth phase.length phase

/-! ## The honest call and its cap -/

/-- **A level's honest `level_queries` call**: the cap and flags `levelHints` builds, query `k`'s
witness its opening's leaf index, leaf and path below the cap (`pd` levels). -/
def lqCall (lam : E) (root : Digest) (depth pd : ℕ) (phase : List Opening) (rounds : List FoldRound)
    (hsv : List E) (wp : ℕ → ℕ) (icf ihs ipos iptr : ℕ) : LqCall :=
  ⟨lam, root, lqCapW depth phase.length phase, lqFlW depth phase.length phase, rounds, hsv, lqWs pd phase, wp,
    icf, ihs, ipos, iptr⟩

/-- **The cap and flags `levelHints` builds are honest**: of `4·2^cd` cells and `2^cd` flags,
checking to `root` (`CapOk`), each query's cap leaf (node `2^cd + q/2^pd`) its climb's node after
`pd` levels and its parent flagged. -/
def LqCapOk (depth : ℕ) (phase : List Opening) (root : Digest) (pd cd : ℕ) : Prop :=
  (lqCapW depth phase.length phase).length = 4 * 2 ^ cd ∧ (lqFlW depth phase.length phase).length = 2 ^ cd ∧
    CapOk cd (lqCapW depth phase.length phase) (lqFlW depth phase.length phase) root ∧
    ∀ k < phase.length,
      (lqCapW depth phase.length phase).getD (2 ^ (cd + 1) + 2 * ((opAt phase k).leafIndex / 2 ^ pd)) 0 =
        (digestHalves (climbD (merkleLeafDigest (opAt phase k).leaf) (opAt phase k).leafIndex
          ((opAt phase k).path.take pd))).1 ∧
      (lqCapW depth phase.length phase).getD (2 ^ (cd + 1) + 2 * ((opAt phase k).leafIndex / 2 ^ pd) + 1) 0 =
        (digestHalves (climbD (merkleLeafDigest (opAt phase k).leaf) (opAt phase k).leafIndex
          ((opAt phase k).path.take pd))).2 ∧
      (lqFlW depth phase.length phase).getD (2 ^ (cd - 1) + (opAt phase k).leafIndex / 2 ^ (pd + 1)) 0 = 1

/-- A phase whose openings climb to `root` and agree wherever they meet (`Limits.OpeningsAgree`)
has an honest cap at its cap depth (`lqCapHonest`, `LqCap.lean`). -/
def LqCapHonest : Prop :=
  ∀ (depth : ℕ) (phase : List Opening) (root : Digest), phase ≠ [] →
    2 ≤ Hints.capDepthOf phase.length depth → Hints.capDepthOf phase.length depth ≤ depth →
    (∀ o ∈ phase, o.leafIndex < 2 ^ depth ∧ o.path.length = depth ∧
      climbD (merkleLeafDigest o.leaf) o.leafIndex o.path = root) →
    Limits.OpeningsAgree depth (phase.map fun o => (o.leafIndex, o)) →
    LqCapOk depth phase root (depth - Hints.capDepthOf phase.length depth) (Hints.capDepthOf phase.length depth)

/-- **The honest call's static facts**, from its cap's (`LqCapOk`) and each opening's. -/
theorem lqCall_static {lam : E} {root : Digest} {depth cd : ℕ} {phase : List Opening} {rounds : List FoldRound}
    {hsv : List E} {wp : ℕ → ℕ} {icf ihs ipos iptr : ℕ} {s : Oq} (hcap : LqCapOk depth phase root s.pd cd)
    (hrl : rounds.length = s.folds) (hnh : s.final = 1 → hsv.length = s.nHs)
    (ho : ∀ o ∈ phase, o.leafIndex < 2 ^ (s.pd + cd) ∧ o.leaf.length = rowLen s.base s.folds ∧
      s.pd ≤ o.path.length ∧ (s.final = 1 → foldRow (lanesOf s.base o.leaf) (K.ofBits o.leafIndex) rounds =
        novelSum hsv (wsChain (s.vs.map K.ofBits) (eOfNat o.leafIndex)) s.nHs s.hsBits)) :
    (lqCall lam root depth s.pd phase rounds hsv wp icf ihs ipos iptr).Static phase.length cd s := by
  obtain ⟨h1, h2, h3, h4⟩ := hcap
  refine ⟨h1, h2, h3, hrl, hnh, fun k hk => ?_⟩
  have hm : opAt phase k ∈ phase := by
    unfold opAt; rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  obtain ⟨o1, o2, o3, o4⟩ := ho _ hm
  obtain ⟨c0, c1, cf⟩ := h4 k hk
  exact ⟨o1, o2, by simp only [lqCall, lqWs, List.length_take]; omega, o4, c0, c1, cf⟩

/-- **The honest call's pops are its level's `levelHints`**, stream by stream. -/
theorem lqCall_sameStreams {lam : E} {root : Digest} {depth : ℕ} {phase : List Opening}
    {rounds : List FoldRound} {hsv : List E} {wp : ℕ → ℕ} {icf ihs ipos iptr : ℕ} {s : Oq} {first : Bool}
    (hpd : s.pd = depth - Hints.capDepthOf phase.length depth) (hfirst : s.base = 1 ↔ first = true)
    (hrow : ∀ o ∈ phase, o.leaf.length = rowLen s.base s.folds) (hl : ∀ o ∈ phase, s.pd ≤ o.path.length) :
    SameStreams ((lqCall lam root depth s.pd phase rounds hsv wp icf ihs ipos iptr).pops phase.length s)
      (Hints.levelHints first depth phase.length phase) :=
  lq_pops_sameStreams rfl rfl (fun _ _ => rfl) hpd hfirst hrow hl

end
end LeanVM.Guest.B1.VsC
