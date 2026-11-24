module

public import LeanDa.StraightBad
public import LeanDa.RelCheck
public import LeanDa.SimWorld
public import LeanDa.WithHash

@[expose] public section

/-!
# The membership test's soundness by a straight-line argument

The simulated world (`idealT`, `LeanDa.StraightBound`: `H` and the challenges random oracles, the
adversary's permutation calls simulated) is bounded without Benedikt Wagner's forking step. It is
stated for a code-binding adversary, an oracle-free argument `ps` and an extractor `ext`; the
membership game is the case of an adversary that opens no cell, the argument that accepts
everything and the extractor that returns its proof (`LeanDa.End`). After the adversary
and the challenges of its root, the straight-line verdict (`tailH`) commits to the extracted
matrix `w` with `H` and, when the argument's proof verifies and `w` satisfies the relation, returns
whether `w` is not a codeword, or else whether the first opening that disagrees with `w` verifies.

* **The verdict is a bad cache** (`not_good_of_tail`): in the world of `LeanDa.StraightBad`, a
  true verdict leaves a cache that is not good: either the draw the nonce search selects was drawn
  when the one matrix committed to the root was not a codeword and passes (with no valid nonce the
  check is on every challenge, which only codewords pass), or `H` collides (the disagreeing
  opening verifies, `verifyCell_agree`), or a fresh answer of `H` hit a digest already carried
  (the matrix's tree completed after the root's draws).
* **The bad cache's probability** is at most `N · 65 N / 2^256 + Q · 2^-10 · (2^13 - 1) / 2^128 +
  (2^13 - 1) / 2^128` (`prT_idealT_tailH_le`, `LeanDa.StraightBound`), `N = 2 Q + 2^20`.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA. The
straight-line argument replaces his forking step; it is built on his framework and his games.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex PqDas
open Common.Duplex (GSpec hP gaP)
open scoped ENNReal

namespace LeanDa

attribute [local irreducible] logMaxRows

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
        if o.2.2.path.length = 7 + logMaxRows then verifyCellMWithHash hH r out.1.1 o.1 o.2.1 o.2.2
        else pure false
      | none => pure false
    else pure true
  else pure false

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
  noCoins_bind (noCoins_merkleRootM H hHc _ _ fun _ ↦ noCoins_merkleRootM H hHc _ _ fun _ ↦ hHc _)
    fun _ ↦ hHc _

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

/-- `H` as the straight-line world queries it. -/
theorem noCoins_embG {α : Type} (Y : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α)
    (hY : NoCoins Y) : NoCoins (simulateQ (embG (Root := Common.DigestBytes) (Z := Draw)
      (n := nLabels)) Y : OracleComp (unifSpec + GW) α) := by
  induction Y using OracleComp.inductionOn with
  | pure a => exact noCoins_pure _
  | query_bind t k ih =>
    rcases t with n | a
    · exact hY.elim
    have hk : ∀ u, NoCoins (k u) := hY
    rw [simulateQ_bind, simulateQ_spec_query]
    simp only [embG, hP]
    exact (noCoins_hq_bind (hs := GW) (.inl a) _).mpr fun u ↦ ih u (hk u)

theorem noCoins_readL (L : List (Fin nLabels)) (d : Common.DigestBytes) : NoCoins (readL L d) := by
  rw [readL]
  refine noCoins_map _ (noCoins_mapM _ (fun j ↦ ?_) _)
  exact noCoins_hq (hs := GW) (.inr (d, j))

/-- A cache's `H` as a partial function on the simulated world's computations with coins and
`H`. -/
def lookupH (c : GCache) : QueryImpl (unifSpec + roSpec (List UInt8) DigestBytes) Option
  | .inl _ => none
  | .inr a => c (.inl a)

theorem replay_embG (c : GCache) {α : Type}
    (Y : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α) :
    simulateQ (replayImpl c) (simulateQ (embG (Root := Common.DigestBytes) (Z := Draw)
      (n := nLabels)) Y) = simulateQ (lookupH c) Y := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with n | a
  · simp only [QueryImpl.apply_compose, embG, simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose, embG, hP, simulateQ_spec_query]
    simp [replayImpl, lookupH]

/-- **The draws a replay reads** are the cache's. -/
theorem replay_mapM_gaP (c : GCache) (d : Common.DigestBytes) : ∀ (L : List (Fin nLabels))
    (ls : List Draw), simulateQ (replayImpl c) (L.mapM (gaP (Msg := List UInt8)
      (Dg := DigestBytes) d)) = some ls →
      ∃ h : ls.length = L.length, ∀ i (hi : i < L.length), c (.inr (d, L[i])) = some (ls[i]'(h ▸ hi))
  | [], ls, h => by
    simp only [List.mapM_nil, simulateQ_pure] at h
    cases h
    exact ⟨rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | j :: L, ls, h => by
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure] at h
    rw [show simulateQ (replayImpl c) (gaP (Msg := List UInt8) (Dg := DigestBytes) d j) =
      c (.inr (d, j)) from by simp [gaP, replayImpl]] at h
    simp only [Option.bind_eq_bind', Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hj, ls', hL, rfl⟩ := h
    obtain ⟨hlen, hval⟩ := replay_mapM_gaP c d L ls' hL
    refine ⟨by simp [hlen], fun i hi ↦ ?_⟩
    cases i with
    | zero => simpa using hj
    | succ i => simpa using hval i (by simpa using hi)

/-- **A replay of the reading of all labels** reads the cache's draws. -/
theorem replay_readL (c : GCache) (d : Common.DigestBytes) (L : List (Fin nLabels))
    (hlen : L.length = nLabels) (hidx : ∀ i (hi : i < L.length), (L[i]).val = i)
    (l : MembershipChallenge) (h : simulateQ (replayImpl c) (readL L d) = some l) :
    ∀ j : Fin nLabels, c (.inr (d, j)) = some (l j) := by
  rw [readL, simulateQ_map] at h
  rcases hL : simulateQ (replayImpl c) (L.mapM (gaP (Msg := List UInt8) (Dg := DigestBytes) d))
    with _ | ls
  · rw [hL] at h; cases h
  · rw [hL] at h
    simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨hl, hval⟩ := replay_mapM_gaP c d L ls hL
    intro j
    have hj : j.val < L.length := by rw [hlen]; exact j.isLt
    have hLj : L[j.val] = j := Fin.ext (hidx j.val hj)
    have := hval j.val hj
    rw [hLj] at this
    rw [this]
    show some ls[j.val] = some (ls.getD j.val default)
    rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]

/-- **A cached draw selected by the nonce search is the first cached valid one.** -/
theorem firstValid_of_selectChal {c : GCache} {d : Common.DigestBytes} {l : MembershipChallenge}
    (hall : ∀ j : Fin nLabels, c (.inr (d, j)) = some (l j)) {z : E} (hs : selectChal l = some z) :
    ∃ j x, FirstValid c d j x ∧ x.1 = z := by
  rw [selectChal, selectFrom_eq] at hs
  rcases hsi : selIdxFrom (fun j ↦ (l j).2) 0 nonceCount with _ | j₀
  · rw [hsi] at hs; cases hs
  · rw [hsi] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    obtain ⟨h1, h2, h3, h4⟩ := selIdxFrom_spec _ nonceCount 0 j₀ hsi
    have hj : j₀ < nLabels := by simp only [nLabels]; omega
    have hpow : ∀ i (hi : i < nLabels), powAt (fun j ↦ (l j).2) i = (l ⟨i, hi⟩).2 := fun i hi ↦ by
      simp [powAt, hi]
    refine ⟨⟨j₀, hj⟩, l ⟨j₀, hj⟩, ⟨by simp only; omega, hall _, by rw [← hpow]; exact h3,
      fun i hi0 hij y hy ↦ ?_⟩, ?_⟩
    · rw [hall i] at hy
      cases hy
      have := h4 i.val (by omega) hij
      rw [hpow i.val i.isLt] at this
      exact this
    · rw [← hs]
      simp [drawAt, hj]

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)

/-- The tail of the simulated world, the draws read at the labels `L`: then the straight-line
verdict. -/
noncomputable def tailL (L : List (Fin nLabels)) (crs : Crs) (out : CbOut r Proof) :
    OracleComp (unifSpec + GW) Bool :=
  readL L out.1.1 >>= fun l ↦ simulateQ embG (tailH r ps ext crs out l)

/-- **A true verdict leaves a bad cache**, the draws read at all labels. -/
theorem not_good_of_tail (hr : r ≤ maxRows) (L : List (Fin nLabels)) (hlen : L.length = nLabels)
    (hidx : ∀ i (hi : i < L.length), (L[i]).val = i) (crs : Crs) (out : CbOut r Proof)
    (c : GCache) {z : Bool × GCache}
    (hz : z ∈ support ((simulateQ GW.romImpl (tailL r ps ext L crs out)).run c))
    (htrue : z.1 = true) : ¬ Good r z.2 := by
  classical
  intro hgood
  have hnc : NoCoins (tailL r ps ext L crs out) :=
    noCoins_bind (noCoins_readL L _) fun l ↦ noCoins_embG _ (noCoins_tailH r ps ext crs out l)
  obtain ⟨-, hrep⟩ := replay_of_mem_support _ hnc c hz
  rw [htrue, tailL, simulateQ_bind] at hrep
  simp only [Option.bind_eq_bind', Option.bind_eq_some_iff] at hrep
  obtain ⟨l, hl, hrep⟩ := hrep
  have hall := replay_readL z.2 out.1.1 L hlen hidx l hl
  rw [replay_embG] at hrep
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
    have hcode : w ∈ (leanDaErasureCode r).code := by
      have hm := hc.2.2
      generalize hs : selectChal l = o at hm
      cases o with
      | none => exact mem_code_of_forall_check ((membershipCheckOpt_none w).mp hm)
      | some zz =>
        obtain ⟨j, x, hfv, hx⟩ := firstValid_of_selectChal hall hs
        exact hgood.2 out.1.1 j x hfv w hin' (hroot'.symm.trans hc.2.1) (hx ▸ hm)
    rw [ite_eq_left hcode] at hrep
    rcases hfb : firstBad r w out.2 with _ | o
    · simp [hfb, hpO] at hrep
    · simp only [hfb] at hrep
      by_cases hlen' : o.2.2.path.length = 7 + logMaxRows
      · rw [ite_eq_left hlen', verifyCellM_map (fun x ↦ simulateQ (lookupH z.2) x) hpO hbO] at hrep
        simp only [hHg] at hrep
        obtain ⟨hb, hvin⟩ := verifyCellM_some (fOf z.2) hg out.1.1 o.1 o.2.1 o.2.2 true hrep
        have hag := verifyCell_agree hr hgood.1 hin' (fun a ha ↦ hvin a ha)
          (by rw [← hroot', hc.2.1]; exact hb.symm)
        have hne := List.find?_some (by simpa only [firstBad] using hfb)
        simp only [decide_eq_true_eq] at hne
        exact hne hag
      · rw [ite_eq_right hlen'] at hrep
        simp [hpO] at hrep
  · rw [ite_eq_right hc] at hrep
    simp [hpO] at hrep

end World

end LeanDa
