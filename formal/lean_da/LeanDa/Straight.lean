module

public import LeanDa.StraightBad
public import LeanDa.KsRpm
public import LeanDa.AdvX
public import LeanDa.WithHash

@[expose] public section

/-!
# Code binding by a straight-line argument

The simulated world of code binding (`codeBindingExpG`: `H` and the challenges `G` random
oracles, the adversary's permutation calls simulated, `LeanDa.RpmCodeBinding`) is bounded without
Benedikt Wagner's forking step. After the adversary and the challenges of its root, the
straight-line verdict (`tailH`) commits to the extracted matrix `w` with `H` and, when the
argument's proof verifies and `w` satisfies the relation, returns whether `w` is not a codeword,
or else whether the first opening that disagrees with `w` verifies.

* **A code-binding win is a knowledge-soundness break or a straight-line verdict**
  (`postP_imp`): with `H` from a table, a win whose proof verifies and whose extracted matrix
  satisfies the relation has an opening that disagrees with a codeword `w`, and it verifies; or
  `w` is not a codeword. So `Pr[code binding] ≤ Pr[knowledge soundness] + Pr[verdict]`
  (`prT_cbIdealG_le`), the three read through Wagner's world for each table (`idealT_evalDistEq`).
* **The verdict is a bad cache** (`not_good_of_tail`): in the world of `LeanDa.StraightBad`, a
  true verdict leaves a cache that is not good: either the root's challenges were drawn when the
  one matrix committed to it was not a codeword and passes, or `H` collides (the disagreeing
  opening verifies, `verifyCell_agree`), or a fresh answer of `H` hit a digest already carried
  (the matrix's tree completed after its challenges).
* **The bad cache's probability** is `N · 65 N / 2^256 + Q_G · (2^14 - 1) / 2^192` for the world's `N`
  queries and `Q_G` queries of `G` (`prob_not_good_le`): `N ≤ 2 Q + 2^20` and `Q_G ≤ Q + 2`
  (`codeBindingExpG_le`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA. The
straight-line argument replaces his forking step; it is built on his framework, his games, his
knowledge-soundness reduction and his membership test's soundness.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex PqDas
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace LeanDa

/-- A code-binding adversary's output: a commitment with its proof, and the opened cells. -/
abbrev CbOut (r : ℕ) (Proof : Type) := (Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)

/-! ## The straight-line verdict -/

section Tail

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)

/-- The first opened cell that disagrees with a matrix. -/
def firstBad (w : Fin (r * 128) → Cell) (l : List (Fin (r * 128) × Cell × CellOpening)) :
    Option (Fin (r * 128) × Cell × CellOpening) :=
  l.find? fun o ↦ decide (o.2.1 ≠ w o.1)

open Classical in
/-- **The straight-line verdict**, `H` an oracle: the extracted matrix's root; when the proof
verifies and the matrix satisfies the relation, whether it is not a codeword, or else whether the
first opening that disagrees with it verifies (with a path of the tree's height). -/
noncomputable def tailH (crs : Crs) (out : CbOut r Proof) (l : MembershipChallenge) :
    OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) Bool := do
  let root ← commitCellsMWithHash hH (ext crs ((), out.1.1, l) out.1.2)
  if ps.verify crs ((), out.1.1, l) out.1.2 = true ∧ root = out.1.1 ∧
      membershipCheckOpt (selectChal l) (ext crs ((), out.1.1, l) out.1.2) = true then
    if ext crs ((), out.1.1, l) out.1.2 ∈ (leanDaErasureCode r).code then
      match firstBad r (ext crs ((), out.1.1, l) out.1.2) out.2 with
      | some o =>
        if o.2.2.path.length = 7 + logPaddedRowCount r then verifyCellMWithHash hH r out.1.1 o.1 o.2.1 o.2.2
        else pure false
      | none => pure false
    else pure true
  else pure false

open Classical in
/-- The straight-line verdict with the hash of the table `h`. -/
noncomputable def tailP (h : HTab) (crs : Crs) (out : CbOut r Proof) (l : MembershipChallenge) :
    Bool :=
  if ps.verify crs ((), out.1.1, l) out.1.2 = true ∧
      commitCellsWithHash (Hh h) (ext crs ((), out.1.1, l) out.1.2) = out.1.1 ∧
      membershipCheckOpt (selectChal l) (ext crs ((), out.1.1, l) out.1.2) = true then
    if ext crs ((), out.1.1, l) out.1.2 ∈ (leanDaErasureCode r).code then
      match firstBad r (ext crs ((), out.1.1, l) out.1.2) out.2 with
      | some o =>
        if o.2.2.path.length = 7 + logPaddedRowCount r then verifyCell (Hh h) r out.1.1 o.1 o.2.1 o.2.2
        else false
      | none => false
    else true
  else false

theorem run_tailH_phiG (h : HTab) (crs : Crs) (out : CbOut r Proof) (l : MembershipChallenge) (s :
    HCache) :
    (simulateQ (phiG h) (simulateQ embG (tailH r ps ext crs out l))).run s =
      pure (tailP r ps ext h crs out l, s) := by
  classical
  rw [← QueryImpl.simulateQ_compose]
  have hp : ∀ {α} (a : α), simulateQ (phiG h ∘ₛ embG) (pure a :
      OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α) = pure a :=
    fun a ↦ simulateQ_pure _ a
  have hb : ∀ {α β} (x : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α)
      (f : α → OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) β),
      simulateQ (phiG h ∘ₛ embG) (x >>= f) =
        simulateQ (phiG h ∘ₛ embG) x >>= fun a ↦ simulateQ (phiG h ∘ₛ embG) (f a) :=
    fun x f ↦ simulateQ_bind _ x f
  have hHs : ∀ a, shortP a → simulateQ (phiG h ∘ₛ embG) (LeanDa.hH a) =
      (pure (Hh h a) : StateT HCache (OracleComp WSpec) Common.DigestBytes) := by
    intro a ha
    rw [LeanDa.hH, simulateQ_spec_query, QueryImpl.apply_compose]
    simp only [embG]
    rw [hP, simulateQ_spec_query]
    ext s
    rw [phiG_H_run h a ha]
    rfl
  rw [tailH, hb, commitCellsM_map (fun x ↦ simulateQ (phiG h ∘ₛ embG) x) hp hb,
    commitCellsM_congr hHs,
    commitCellsM_eval (fun x ↦ x) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun a ↦ pure (Hh h a)) (Hh h)
      (fun _ ↦ rfl), pure_bind]
  unfold tailP
  set w := ext crs ((), out.1.1, l) out.1.2
  by_cases hc : ps.verify crs ((), out.1.1, l) out.1.2 = true ∧ commitCellsWithHash (Hh h) w = out.1.1 ∧
      membershipCheckOpt (selectChal l) w = true
  · rw [ite_eq_left hc, ite_eq_left hc]
    by_cases hw : w ∈ (leanDaErasureCode r).code
    · rw [ite_eq_left hw, ite_eq_left hw]
      rcases firstBad r w out.2 with _ | o
      · simp only [hp]; rfl
      · by_cases hlen : o.2.2.path.length = 7 + logPaddedRowCount r
        · simp only [ite_eq_left hlen]
          rw [verifyCellM_map (fun x ↦ simulateQ (phiG h ∘ₛ embG) x) hp hb, verifyCellM_congr hHs,
            verifyCellM_pure]
          rfl
        · simp only [ite_eq_right hlen, hp]; rfl
    · rw [ite_eq_right hw, ite_eq_right hw, hp]; rfl
  · rw [ite_eq_right hc, ite_eq_right hc, hp]; rfl

/-- **A code-binding win is a knowledge-soundness break or a true straight-line verdict**, with
`H` from a table. -/
theorem postP_imp (h : HTab) (crs : Crs) (out : CbOut r Proof) (l : MembershipChallenge)
    (hwin : postP r ps h crs out l = true) :
    ksP r ps ext h crs out l = true ∨ tailP r ps ext h crs out l = true := by
  classical
  by_cases hk : ksP r ps ext h crs out l = true
  · exact Or.inl hk
  right
  set w := ext crs ((), out.1.1, l) out.1.2 with hwdef
  simp only [postP, cbWin, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hwin
  obtain ⟨⟨hall, hver⟩, hinc⟩ := hwin
  simp only [ksP, hver, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true,
    decide_eq_true_eq, ← hwdef] at hk
  obtain ⟨hcom, hm⟩ := hk
  unfold tailP
  rw [← hwdef, ite_eq_left ⟨hver, hcom, hm⟩]
  by_cases hw : w ∈ (leanDaErasureCode r).code
  · rw [ite_eq_left hw]
    rcases hfb : firstBad r w out.2 with _ | o
    · exfalso
      simp only [firstBad] at hfb
      refine hinc ((leanDaErasureCode r).consistent_iff_exists_codeword _
          |>.mpr ⟨w, hw, fun p hp ↦ ?_⟩)
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hp
      have := List.find?_eq_none.mp hfb o ho
      exact (by simpa using this : o.2.1 = w o.1).symm
    · simp only [firstBad] at hfb
      have ho := List.mem_of_find?_eq_some hfb
      have hv := hall o ho
      have hlen : o.2.2.path.length = 7 + logPaddedRowCount r := by
        simp only [verifyCell, Bool.and_eq_true, decide_eq_true_eq] at hv
        exact hv.1
      simp only [ite_eq_left hlen]
      exact hv
  · rw [ite_eq_right hw]

/-! ### Coin-free -/

variable {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
  [∀ t : hs.Domain, SampleableType (hs.Range t)]

theorem noCoins_mapM {β γ : Type} (F : β → OracleComp (unifSpec + hs) γ) (hF : ∀ b, NoCoins (F b))
    (l : List β) : NoCoins (l.mapM F) := by
  induction l with
  | nil => exact noCoins_pure _
  | cons b l ih =>
    rw [List.mapM_cons]
    exact noCoins_bind (hF b) fun _ ↦ noCoins_bind ih fun _ ↦ noCoins_pure _

variable (H : List UInt8 → OracleComp (unifSpec + hs) Common.DigestBytes) (hHc : ∀ a, NoCoins (H a))
include hHc

theorem noCoins_merkleRootM (d : ℕ) :
    ∀ L : ℕ → OracleComp (unifSpec + hs) Common.DigestBytes, (∀ i, NoCoins (L i)) →
      NoCoins (merkleRootMWithHash H d L) := by
  induction d with
  | zero => intro L hL; exact hL 0
  | succ d ih =>
    intro L hL
    exact ih _ fun i ↦ noCoins_bind (hL _) fun _ ↦ noCoins_bind (hL _) fun _ ↦ hHc _

theorem noCoins_commitCellsM {r : ℕ} (c : Fin (r * 128) → Cell) : NoCoins (commitCellsMWithHash H c) :=
  noCoins_merkleRootM H hHc _ _ fun _ ↦ noCoins_merkleRootM H hHc _ _ fun _ ↦ hHc _

theorem noCoins_walkM (path : List Common.DigestBytes) :
    ∀ (idx : ℕ) (node : Common.DigestBytes), NoCoins (walkMWithHash H idx node path) := by
  induction path with
  | nil => intro idx node; exact noCoins_pure _
  | cons s rest ih => intro idx node; exact noCoins_bind (hHc _) fun _ ↦ ih _ _

theorem noCoins_verifyCellM (r : ℕ) (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ : CellOpening) :
    NoCoins (verifyCellMWithHash H r com p x τ) :=
  noCoins_bind (hHc _) fun _ ↦ noCoins_bind (noCoins_walkM H hHc _ _ _) fun _ ↦ noCoins_pure _

omit hHc

theorem noCoins_hH (a : List UInt8) : NoCoins (LeanDa.hH a) := fun _ ↦ trivial

theorem noCoins_tailH (crs : Crs) (out : CbOut r Proof) (l : MembershipChallenge) :
    NoCoins (tailH r ps ext crs out l) := by
  classical
  unfold tailH
  refine noCoins_bind (noCoins_commitCellsM _ noCoins_hH _) fun root ↦ ?_
  split_ifs
  · split
    · split_ifs
      · exact noCoins_verifyCellM _ noCoins_hH _ _ _ _ _
      · exact noCoins_pure _
    · exact noCoins_pure _
  · exact noCoins_pure _
  · exact noCoins_pure _

end Tail

/-! ## The straight-line world -/

section World

/-- Queries of `H` or of the challenges in the simulated world, one each. -/
def hgCalls : (unifSpec + GSpec (List UInt8) DigestBytes Common.DigestBytes Draw nLabels).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- `H` as the simulated world queries it, the challenges one oracle of vectors. -/
theorem noCoins_toV_embG {α : Type} (Y : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α)
    (hY : NoCoins Y) : NoCoins (simulateQ (toV (Msg := List UInt8) (Dg := DigestBytes) (Root := Common.DigestBytes)
      (Z := Draw) (n := nLabels)) (simulateQ embG Y)) := by
  induction Y using OracleComp.inductionOn with
  | pure a => exact noCoins_pure _
  | query_bind t k ih =>
    rcases t with n | a
    · exact hY.elim
    have hk : ∀ u, NoCoins (k u) := hY
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query]
    simp only [embG, hP, simulateQ_spec_query, toV]
    exact (noCoins_hq_bind (hs := VS) (.inl a) _).mpr fun u ↦ ih u (hk u)

theorem noCoins_toV_readVec (d : Common.DigestBytes) :
    NoCoins (simulateQ toV (readVec (Msg := List UInt8) (Dg := DigestBytes) (Z := Draw) (n := nLabels) d)) := by
  rw [readVec, simulateQ_map]
  refine noCoins_map _ ?_
  rw [mapM_map (fun x ↦ simulateQ toV x) (fun a ↦ simulateQ_pure _ a)
    (fun x f ↦ simulateQ_bind _ x f)]
  refine noCoins_mapM _ (fun j ↦ ?_) _
  simp only [gaP, simulateQ_spec_query, toV]
  exact noCoins_map _ (noCoins_hq (hs := VS) (.inr d))

/-- A cache's `H` as a partial function on the simulated world's computations with coins and
`H`. -/
def lookupH (c : VCache) : QueryImpl (unifSpec + roSpec (List UInt8) DigestBytes) Option
  | .inl _ => none
  | .inr a => c (.inl a)

theorem replay_toV_embG (c : VCache) {α : Type}
    (Y : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α) :
    simulateQ (replayImpl c) (simulateQ toV (simulateQ embG Y)) = simulateQ (lookupH c) Y := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with n | a
  · simp only [QueryImpl.apply_compose, embG, simulateQ_spec_query, toV]
    rfl
  · simp only [QueryImpl.apply_compose, embG, hP, simulateQ_spec_query, toV]
    simp [replayImpl, lookupH]

theorem replay_toV_readVec (c : VCache) (d : Common.DigestBytes) (l : MembershipChallenge)
    (h : simulateQ (replayImpl c) (simulateQ toV (readVec (Msg := List UInt8) (Dg := DigestBytes)
      (n := nLabels) d)) = some l) : c (.inr d) = some l := by
  rw [readVec, simulateQ_map, simulateQ_map,
    mapM_map (fun x ↦ simulateQ toV x) (fun a ↦ simulateQ_pure _ a)
      (fun x f ↦ simulateQ_bind _ x f),
    mapM_map (fun x ↦ simulateQ (replayImpl c) x) (fun a ↦ simulateQ_pure _ a)
      (fun x f ↦ simulateQ_bind _ x f)] at h
  have hq : ∀ j : Fin 2, simulateQ (replayImpl c) (simulateQ toV
      (gaP (Msg := List UInt8) (Dg := DigestBytes) (Z := E) d j)) = (fun v : MembershipChallenge ↦ v j) <$> c (.inr d) := by
    intro j
    simp only [gaP, simulateQ_spec_query, toV, simulateQ_map]
    rfl
  simp only [hq] at h
  rcases hd : c (.inr d) with _ | v
  · rw [hd] at h
    simp [List.finRange_succ] at h
  · rw [hd] at h
    have hm : ∀ l : List (Fin 2), l.mapM (fun j : Fin 2 ↦ (fun v : MembershipChallenge ↦ v j) <$>
        some v) =
        some (l.map fun j ↦ v j) := by
      intro l
      induction l with
      | nil => rfl
      | cons j l ih => rw [List.mapM_cons, ih]; rfl
    rw [hm] at h
    injection h with h'
    subst h'
    congr 1
    funext j
    dsimp only
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_finRange]; omega), List.getElem_map, List.getElem_finRange]
    rfl

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)

/-- The tail of the simulated world: the challenges of the root, then the straight-line verdict. -/
noncomputable def tailV (crs : Crs) (out : CbOut r Proof) :
    OracleComp (unifSpec + GSpec (List UInt8) DigestBytes Common.DigestBytes Draw nLabels) Bool :=
  readVec (Msg := List UInt8) (Dg := DigestBytes) out.1.1 >>= fun l ↦
    simulateQ embG (tailH r ps ext crs out l)

/-- **A true verdict leaves a bad cache.** -/
theorem not_good_of_tail (crs : Crs) (out : CbOut r Proof) (c : VCache) {z : Bool × VCache}
    (hz : z ∈ support ((simulateQ VS.romImpl (simulateQ toV (tailV r ps ext crs out))).run c))
    (htrue : z.1 = true) : ¬ Good r z.2 := by
  classical
  intro hgood
  have hnc : NoCoins (simulateQ toV (tailV r ps ext crs out)) := by
    rw [tailV, simulateQ_bind]
    exact noCoins_bind (noCoins_toV_readVec _) fun l ↦
      noCoins_toV_embG _ (noCoins_tailH r ps ext crs out l)
  obtain ⟨-, hrep⟩ := replay_of_mem_support _ hnc c hz
  rw [htrue, tailV, simulateQ_bind, simulateQ_bind] at hrep
  simp only [Option.bind_eq_bind', Option.bind_eq_some_iff] at hrep
  obtain ⟨l, hl, hrep⟩ := hrep
  have hd := replay_toV_readVec z.2 out.1.1 l hl
  rw [replay_toV_embG] at hrep
  set g : List UInt8 → Option Common.DigestBytes := fun a ↦ z.2 (.inl a)
  have hg : ∀ a u, g a = some u → u = fOf z.2 a := fun a u hu ↦ (fOf_of_mem hu).symm
  have hHg : ∀ a, simulateQ (lookupH z.2) (LeanDa.hH a) = g a := fun a ↦ by
    rw [LeanDa.hH, simulateQ_spec_query]; rfl
  have hpO : ∀ {α} (a : α), simulateQ (lookupH z.2) (pure a :
      OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α) = pure a := fun a ↦ simulateQ_pure _ a
  have hbO : ∀ {α β} (x : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α)
      (f : α → OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) β),
      simulateQ (lookupH z.2) (x >>= f) =
        simulateQ (lookupH z.2) x >>= fun a ↦ simulateQ (lookupH z.2) (f a) :=
    fun x f ↦ simulateQ_bind _ x f
  rw [tailH, hbO, commitCellsM_map (fun x ↦ simulateQ (lookupH z.2) x) hpO hbO] at hrep
  simp only [hHg] at hrep
  change (commitCellsMWithHash g (ext crs ((), out.1.1, l) out.1.2) >>= fun root ↦ _) = some true at hrep
  simp only [Option.bind_eq_bind', Option.bind_eq_some_iff] at hrep
  obtain ⟨root, hroot, hrep⟩ := hrep
  set w := ext crs ((), out.1.1, l) out.1.2 with hwd
  obtain ⟨hroot', hin⟩ := commitCellsM_some (fOf z.2) hg w root hroot
  have hin' : commitIn (fOf z.2) w ⊆ domH z.2 := fun a ha ↦ hin a ha
  by_cases hc : ps.verify crs ((), out.1.1, l) out.1.2 = true ∧ root = out.1.1 ∧
      membershipCheckOpt (selectChal l) w = true
  · rw [ite_eq_left hc] at hrep
    have hcode := hgood.2 out.1.1 l hd w hin' (hroot'.symm.trans hc.2.1) hc.2.2
    rw [ite_eq_left hcode] at hrep
    rcases hfb : firstBad r w out.2 with _ | o
    · simp [hfb, hpO] at hrep
    · simp only [hfb] at hrep
      by_cases hlen : o.2.2.path.length = 7 + logPaddedRowCount r
      · rw [ite_eq_left hlen, verifyCellM_map (fun x ↦ simulateQ (lookupH z.2) x) hpO hbO] at hrep
        simp only [hHg] at hrep
        obtain ⟨hb, hvin⟩ := verifyCellM_some (fOf z.2) hg out.1.1 o.1 o.2.1 o.2.2 true hrep
        have hag := verifyCell_agree hgood.1 hin' (fun a ha ↦ hvin a ha)
          (by rw [← hroot', hc.2.1]; exact hb.symm)
        have hne := List.find?_some (by simpa only [firstBad] using hfb)
        simp only [decide_eq_true_eq] at hne
        exact hne hag
      · rw [ite_eq_right hlen] at hrep
        simp [hpO] at hrep
  · rw [ite_eq_right hc] at hrep
    simp [hpO] at hrep

end World

end LeanDa
