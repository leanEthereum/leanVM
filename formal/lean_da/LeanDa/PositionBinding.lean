module

public import LeanDa.HashOracle
public import LeanDa.RomHash
public import LeanDa.MerkleM
public import LeanDa.WithHash

@[expose] public section

/-!
# LeanDA's position binding with an argument that queries the oracles

The argument (`NarkRpmH`) queries the random-permutation model's oracles. Its verification in the
game runs right after the adversary, so in the two-oracle form of the game (`Common.rpmGame2`) it
belongs to the adversary's part (`advP`), and the verifier's part is the openings' climbs, with `H`
alone (`posPostV`). A win is then a collision of `H` among the climbs' cached inputs
(`leanDa_positionBinding_rpmH`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex PqDas
open Common.Duplex (GSpec hP gaP)
open scoped ENNReal

namespace LeanDa

/-! ## Weights through a map -/

theorem advS2_map {α β : Type} (f : α → β) (X : OracleComp KSpecB α) :
    advS2 keccakPadding KState.zero (f <$> X) = f <$> advS2 keccakPadding KState.zero X := by
  rw [advS2, advS2, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map,
    Functor.map_map, Functor.map_map]

/-! ## The virtual argument -/

section Virtual

variable (r : ℕ) {Crs Proof : Type} (ps : ArgumentRpmH r Crs Proof)

/-- **The position-binding adversary followed by the argument's verification.** -/
noncomputable def advP (A : PosBindingAdvRpmH r Crs Proof) (ck : Unit × Crs) :
    OracleComp KSpecH ((Common.DigestBytes × (Proof × Bool)) × Fin (r * 128) × Cell × ByteOpening × Cell × ByteOpening) := do
  let (com, p, x, τ, x', τ') ← A ck
  let ok ← ps.verify ck.2 com.1 com.2
  pure ((com.1, (com.2, ok)), p, x, τ, x', τ')

/-- The climbs of the position-binding game, with the argument's verdict. -/
def posPostV (_ : Crs)
    (out : (Common.DigestBytes × (Proof × Bool)) × Fin (r * 128) × Cell × ByteOpening × Cell × ByteOpening) :
    OracleComp Rom2 Bool := do
  let b ← verifyCellMWithHash hR r out.1.1 out.2.1 out.2.2.1 out.2.2.2.1
  let b' ← verifyCellMWithHash hR r out.1.1 out.2.1 out.2.2.2.2.1 out.2.2.2.2.2
  pure (decide (out.2.2.1 ≠ out.2.2.2.2.1) && out.1.2.2 && b && b')

theorem relabel_posBindingGame (A : PosBindingAdvRpmH r Crs Proof) :
    simulateQ relabel (posBindingGameH r ps A) =
      simulateQ (toOne (E := KRest) (C := KCap)) (rpmGame2 (liftM ps.setup)
        (fun crs ↦ relabelAdv (advP r ps A) ((), crs)) (posPostV r)) := by
  rw [toOne_rpmGame2]
  unfold posBindingGameH
  rw [simulateQ_bind, simulateQ_liftM_of_coins _ (fun n ↦ rfl)]
  refine bind_congr fun crs ↦ ?_
  simp only [relabelAdv, advP, simulateQ_bind, bind_assoc]
  refine bind_congr fun out ↦ ?_
  obtain ⟨com, p, x, τ, x', τ'⟩ := out
  simp only [simulateQ_pure, pure_bind]
  refine bind_congr fun ok ↦ ?_
  simp only [posPostV, simulateQ_bind, simulateQ_pure, relabel_verifyCellM,
    verifyCellM_map (fun x ↦ simulateQ toK x) (fun _ ↦ simulateQ_pure _ _)
      (fun _ _ ↦ simulateQ_bind _ _ _), toK_hR]

end Virtual

/-! ## Position binding -/

section PositionBinding

variable (r : ℕ) {Crs Proof : Type} (ps : ArgumentRpmH r Crs Proof)

theorem duplex_posPostV (crs : Crs)
    (out : (Common.DigestBytes × (Proof × Bool)) × Fin (r * 128) × Cell × ByteOpening × Cell × ByteOpening) :
    Duplex KState.zero keccakNF (posPostV r crs out) [] :=
  duplex_of_duplexP (Q := fun _ _ ↦ True) <|
    duplexP_bind (duplexP_verifyCellM r _ _ _ _ []) fun _ hist _ ↦
      duplexP_bind (duplexP_verifyCellM r _ _ _ _ hist) fun _ _ _ ↦ duplexP_pure trivial

/-- **A win of the climbs is a collision of `H` in the final cache.** -/
theorem posPostV_win (crs : Crs)
    (out : (Common.DigestBytes × (Proof × Bool)) × Fin (r * 128) × Cell × ByteOpening × Cell ×
        ByteOpening)
    (c : Cache2) {z : Bool × Cache2}
    (hz : z ∈ support ((simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
      (posPostV r crs out)).run c)) (hwin : z.1 = true) : HCollision z.2 := by
  obtain ⟨com, p, x, τ, x', τ'⟩ := out
  simp only [posPostV, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨⟨⟨hx, -⟩, hb⟩, hb'⟩ := hwin
  obtain ⟨hc2, hv2⟩ := run_verifyCellM r com.1 p x' τ' _ hw₂
  obtain ⟨-, hv1⟩ := run_verifyCellM r com.1 p x τ _ hw₁
  obtain ⟨hτ, hin⟩ := hv1 w₂.2 hc2
  obtain ⟨hτ', hin'⟩ := hv2 w₂.2 le_rfl
  rw [hτ] at hb
  rw [hτ'] at hb'
  obtain ⟨hne, heq⟩ := openingsCollision_spec (hOf w₂.2) hx hb hb'
  simp only [openingsCollision] at hne heq
  obtain ⟨ha, hb⟩ := findCollision_mem _ _ _ hne
  show HCollision w₂.2
  have hca := hin _ ha
  have hcb := hin' _ hb
  exact ⟨_, _, hne, hca, by rw [cache_eq_hOf hca, cache_eq_hOf hcb, heq]⟩

/-- **LeanDA is position binding in the random-permutation model.** For every argument `ps` and
every adversary whose game, the argument's verification included, makes at most `Q` calls of the
permutation on every path, the probability of opening a position to two different cells is at
most `Q² / 2^256 + Q² / 2^508`, so at most `(Q + 1)² · 2^-256` for `Q ≤ 2^128`
(`Common.sq_add_sq_le`), and for every `Q`, the bound being at least one past `2^128`: the adversary followed by the argument's verification is an adversary of
the two-oracle transfer, and a win of the climbs is a collision of `H` (`posPostV_win`,
`prob_hCollision_le`). -/
theorem leanDa_positionBinding_rpmH : PositionBindingRpmH := by
  intro r Crs Proof ps A Q hQ
  rcases le_or_gt Q (2 ^ 128) with hcap | hcap
  swap
  · -- past `2^128` the bound is at least one
    refine (prEvent_le_one _).trans (Common.one_le_mul_inv_two_pow ?_)
    calc (2 : ℝ≥0∞) ^ 256 = ((2 : ℝ≥0∞) ^ 128) ^ 2 := by rw [← pow_mul]
      _ ≤ ((Q : ℝ≥0∞) + 1) ^ 2 := by
        gcongr
        calc (2 : ℝ≥0∞) ^ 128 ≤ (Q : ℝ≥0∞) := by exact_mod_cast hcap.le
          _ ≤ (Q : ℝ≥0∞) + 1 := le_self_add
  have e := relabel_posBindingGame r ps A
  replace hQ : QueryCostAtMost (rpmGame2 (liftM ps.setup)
      (fun crs ↦ relabelAdv (advP r ps A) ((), crs)) (posPostV r)) permCalls2 Q := by
    rw [← isWeightBound_toOne_iff, ← e]; exact isWeightBound_relabel hQ
  rw [(runK_relabel _).prEvent_eq, e]
  generalize relabelAdv (advP r ps A) = A at hQ ⊢
  change Pr{let b ← realGame2 keccakPadding KState.zero _}[b = true] ≤ _
  rw [permCalls2_eq] at hQ
  obtain ⟨h1, -⟩ := keccak256_transfer2 (liftM ps.setup) (fun crs ↦ A ((), crs))
    (posPostV r) (fun x a ↦ duplex_posPostV r x a) Q hQ (· = true)
  refine h1.trans ((add_le_add ?_ le_rfl).trans (Common.sq_add_sq_le hcap))
  have hX : QueryCostAtMost (simulateQ (hInF (E := KRest) (C := KCap)) (liftM ps.setup) >>= fun x ↦
      advS2 keccakPadding KState.zero (A ((), x)) >>= fun a ↦ posPostV r x a) hCalls Q := by
    rw [← shadow_rpmGame2, StateT.run'_eq]
    exact isWeightBound_map _ (isWeightBound_run_simulateQ _ _ _ isWeightBound_shadowImpl hQ _)
  have hwin : ∀ z ∈ support ((simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
      (simulateQ (hInF (E := KRest) (C := KCap)) (liftM ps.setup) >>= fun x ↦
        advS2 keccakPadding KState.zero (A ((), x)) >>= fun a ↦ posPostV r x a)).run ∅),
      z.1 = true → HCollision z.2 := by
    intro z hz
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w₁, -, w₂, -, hz⟩ := hz
    exact posPostV_win r _ _ _ hz
  rw [romRun2, StateT.run'_eq, prEvent_map]
  calc _ ≤ _ := prEvent_mono_of_support _ _ _ hwin
    _ ≤ Q * ((Q : ℝ≥0∞) / 2 ^ 256) := prob_hCollision_le _ Q hX
    _ = (Q ^ 2 : ℝ≥0∞) / 2 ^ 256 := by rw [← mul_div_assoc, ← pow_two]

end PositionBinding

/-! ## Query budgets through a map -/

section Calls

variable (r : ℕ) {Crs Proof : Type} (ps : ArgumentRpmH r Crs Proof)

/-- **A game's weight bound holds with the adversary's output mapped** and a verifier's part
that makes no call. -/
theorem isWeightBound_rpmGame2_map {β γ γ' δ δ' : Type} (p : ProbComp β)
    (A : β → OracleComp KSpecB γ) (post : β → γ → OracleComp Rom2 δ) (f : γ → γ')
    (post' : β → γ' → OracleComp Rom2 δ') (Q : ℕ)
    (h : QueryCostAtMost (rpmGame2 (liftM p) A post) permCalls2 Q)
    (h0 : ∀ x a, QueryCostAtMost (simulateQ (hfEmbed (Msg := List UInt8) (Dg := DigestBytes)
      (E := KRest) (C := KCap)) (post' x (f a))) permCalls2 0) :
    QueryCostAtMost (rpmGame2 (liftM p) (fun x ↦ f <$> A x) post') permCalls2 Q := by
  unfold rpmGame2 at h ⊢
  have e : (simulateQ (hEmbed2 (E := KRest) (C := KCap)) (liftM p : OracleComp (unifSpec +
      roSpec (List UInt8) DigestBytes) β) >>= fun x ↦ simulateQ (advEmbed (Msg := List UInt8)) (A x) >>=
        fun a ↦ simulateQ (hfEmbed (Msg := List UInt8)) (post x a)) =
      (simulateQ (hEmbed2 (E := KRest) (C := KCap)) (liftM p : OracleComp (unifSpec +
        roSpec (List UInt8) DigestBytes) β) >>= fun x ↦ simulateQ (advEmbed (Msg := List UInt8)) (A x) >>=
          fun a ↦ pure (x, a)) >>= fun xa ↦ simulateQ (hfEmbed (Msg := List UInt8)) (post xa.1 xa.2) := by
    simp only [bind_assoc, pure_bind]
  rw [e] at h
  have e' : (simulateQ (hEmbed2 (E := KRest) (C := KCap)) (liftM p : OracleComp (unifSpec +
      roSpec (List UInt8) DigestBytes) β) >>= fun x ↦ simulateQ (advEmbed (Msg := List UInt8))
        (f <$> A x) >>= fun a ↦ simulateQ (hfEmbed (Msg := List UInt8)) (post' x a)) =
      (simulateQ (hEmbed2 (E := KRest) (C := KCap)) (liftM p : OracleComp (unifSpec +
        roSpec (List UInt8) DigestBytes) β) >>= fun x ↦ simulateQ (advEmbed (Msg := List UInt8)) (A x) >>=
          fun a ↦ pure (x, a)) >>= fun xa ↦ simulateQ (hfEmbed (Msg := List UInt8))
            (post' xa.1 (f xa.2)) := by
    simp only [simulateQ_map, bind_map_left, bind_assoc, pure_bind]
  rw [e']
  exact (h.of_bind.bind fun xa ↦ h0 xa.1 xa.2).mono (by omega)

end Calls

end LeanDa
