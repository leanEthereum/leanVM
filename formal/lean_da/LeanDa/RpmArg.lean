module

public import LeanDa.StraightBound
public import LeanDa.RpmComplete
public import LeanDa.WithHash

@[expose] public section

/-!
# LeanDA's binding with an argument that queries the oracles

The end statements' argument (`NarkRpmH`) queries the random-permutation model's oracles, and its
extractor reads the adversary's transcript (`ksGameH`, the adversary's queries logged by
`loggedKH`). Its verification in the games runs right after the adversary, so in the two-oracle
form of a game (`Common.rpmGame2`) it belongs to the adversary's part, and the verifier's part is
the openings' climbs, with `H` alone.

* **Position binding** (`leanDa_positionBinding_rpmH`): the adversary followed by the argument's
  verification is an adversary of the two-oracle transfer; a win is a collision of `H` among the
  climbs' cached inputs, as before.
* **Code binding** (`leanDa_codeBinding_rpm_boundH`), by the straight-line argument of
  `LeanDa.StraightBound`, which is stated for an oracle-free argument: the adversary followed by
  the argument's verification, its proof carrying the argument's proof, the adversary's
  transcript and the verification's verdict (`advV`), is the adversary of the same games for an
  oracle-free argument that reads the verdict (`psV`) and an extractor that reads the proof and
  the transcript (`extV`). The code-binding game moves to the two-oracle form, where the
  challenges of the root, unused, are inserted before the climbs (`run'_bind_const`), and the
  knowledge-soundness term is the statement's game of the code-binding adversary itself, its
  transcript handed to the extractor (`ksB`, `relabel_ksGame`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA; the
straight-line argument is built on his framework and games.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex PqDas
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace LeanDa

/-! ## Logging -/

theorem run_loggedK_query (t : KSpecH.Domain) (s : TranscriptH) :
    (loggedKH t).run s = (fun u ↦ (u, s ++ [⟨t, u⟩])) <$> liftM (KSpecH.query t) := by
  simp [loggedKH]

/-- **Logging changes no answer.** -/
theorem fst_run_loggedK {α : Type} (X : OracleComp KSpecH α) (s : TranscriptH) :
    Prod.fst <$> (simulateQ loggedKH X).run s = X := by
  induction X using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [run_loggedK_query, bind_map_left, map_bind]
    exact bind_congr fun u ↦ ih u _

theorem run_loggedK_map {α β : Type} (f : α → β) (X : OracleComp KSpecH α) (s : TranscriptH) :
    (simulateQ loggedKH (f <$> X)).run s = (fun p ↦ (f p.1, p.2)) <$> (simulateQ loggedKH X).run s := by
  rw [simulateQ_map, StateT.run_map]

/-! ## Weights through a map -/

theorem isWeightBound_map_iff {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type} (f : α → β)
    (X : OracleComp spec α) (w : ι → ℕ) (Q : ℕ) :
    QueryCostAtMost (f <$> X) w Q ↔ QueryCostAtMost X w Q := by
  induction X using OracleComp.inductionOn generalizing Q with
  | pure a => exact Iff.rfl
  | query_bind t k ih =>
    rw [map_bind, isWeightBound_query_bind_iff, isWeightBound_query_bind_iff]
    exact and_congr Iff.rfl (forall_congr' fun u ↦ ih u _)

theorem advS2_map {α β : Type} (f : α → β) (X : OracleComp KSpecB α) :
    advS2 keccakPadding KState.zero (f <$> X) = f <$> advS2 keccakPadding KState.zero X := by
  rw [advS2, advS2, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map,
    Functor.map_map, Functor.map_map]

/-! ## The virtual argument -/

section Virtual

variable (r : ℕ) {Crs Proof : Type} (ps : ArgumentRpmH r Crs Proof)
  (ext : ExtractorRpmH Common.DigestBytes (Fin (r * 128) → Cell) Crs Proof)

/-- The proof of the virtual argument: the argument's proof, the adversary's transcript and the
argument's verdict. -/
abbrev PrfV (Proof : Type) := Option Proof × TranscriptH × Bool

/-- **The virtual oracle-free argument**: it reads the verdict its proof carries. -/
def psV : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
    (PrfV Proof)
    (fun _ _ ↦ true) where
  setup := ps.setup
  prove _ _ _ := (none, [], false)
  verify _ _ p := p.2.2

/-- **The virtual extractor**: the extractor on the proof and the transcript the virtual proof
carries. -/
def extV : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs (PrfV Proof) :=
  fun crs stmt p ↦ match p.1 with
    | some proof => ext crs stmt.2.1 proof p.2.1
    | none => fun _ _ ↦ 0

/-- **The adversary followed by the argument's verification**, its queries logged: the virtual
proof carries the proof, the transcript and the verdict. -/
noncomputable def advV (A : CodeBindingAdvRpmH r Crs Proof) (ck : Unit × Crs) :
    OracleComp KSpecH (CbOut r (PrfV Proof)) := do
  let (out, log) ← (simulateQ loggedKH (A ck)).run []
  let ok ← ps.verify ck.2 out.1.1 out.1.2
  pure ((out.1.1, (some out.1.2, log, ok)), out.2)

/-- The same without the openings. -/
noncomputable def advV0 (A : CodeBindingAdvRpmH r Crs Proof) (ck : Unit × Crs) :
    OracleComp KSpecH (CbOut r (PrfV Proof)) :=
  (fun out ↦ (out.1, [])) <$> advV r ps A ck

/-- **The knowledge-soundness adversary of a code-binding adversary**: the adversary itself, its
root and proof. -/
def ksB (A : CodeBindingAdvRpmH r Crs Proof) : KsAdvRpmH Crs Proof :=
  fun crs ↦ (fun out ↦ (out.1.1, out.1.2)) <$> A ((), crs)

/-- The climbs of the code-binding game, with the virtual argument's verdict. -/
noncomputable def cbPostV (crs : Crs) (out : CbOut r (PrfV Proof)) : OracleComp Rom2 Bool :=
  simulateQ embH (postV r (psV r ps) crs out default)

theorem toK_hR' (a : List UInt8) : simulateQ toK (hR a) = hKB a := toK_hR a

theorem toK_cbPostV (crs : Crs) (out : CbOut r (PrfV Proof)) :
    simulateQ toK (cbPostV r ps crs out) = (do
      let vs ← out.2.mapM fun o ↦ verifyCellMWithHash hKB r out.1.1 o.1 o.2.1 o.2.2
      pure (cbWin r out vs out.1.2.2.2)) := by
  rw [cbPostV, simulateQ_embH_postV, simulateQ_bind,
    mapM_map (fun x ↦ simulateQ toK x) (fun _ ↦ simulateQ_pure _ _)
      (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [verifyCellM_map (fun x ↦ simulateQ toK x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _), toK_hR, simulateQ_pure]
  rfl

/-- **The code-binding game is its two-oracle form** with the adversary followed by the
argument's verification. -/
theorem relabel_codeBindingGame (A : CodeBindingAdvRpmH r Crs Proof) :
    simulateQ relabel (codeBindingGameH r ps A) =
      simulateQ (toOne (E := KRest) (C := KCap)) (rpmGame2 (liftM ps.setup)
        (fun crs ↦ relabelAdv (advV r ps A) ((), crs)) (cbPostV r ps)) := by
  rw [toOne_rpmGame2]
  unfold codeBindingGameH
  rw [simulateQ_bind, simulateQ_liftM_of_coins _ (fun n ↦ rfl)]
  refine bind_congr fun crs ↦ ?_
  conv_lhs => rw [← fst_run_loggedK (A ((), crs)) []]
  simp only [relabelAdv, advV, simulateQ_bind, bind_map_left, bind_assoc]
  refine bind_congr fun p ↦ ?_
  obtain ⟨⟨⟨root, proof⟩, opened⟩, log⟩ := p
  simp only [simulateQ_pure, pure_bind]
  refine bind_congr fun ok ↦ ?_
  rw [toK_cbPostV, mapM_map (fun x ↦ simulateQ relabel x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [relabel_verifyCellM]
  refine bind_congr fun vs ↦ ?_
  cases ok <;> simp [cbWin, Bool.and_comm]

/-- **The knowledge-soundness game of the code-binding adversary** is the two-oracle game of the
virtual argument against the adversary without its openings, with the deployed challenge by the
nonce search (`postKG`). -/
theorem relabel_ksGame (A : CodeBindingAdvRpmH r Crs Proof) :
    simulateQ relabel (ksGameH r ps ext (ksB r A)) =
      simulateQ (toOne (E := KRest) (C := KCap))
        (rpmGame2 (liftM (psV r ps).setup) (fun crs ↦ relabelAdv (advV0 r ps A) ((), crs))
          (postKG r (psV r ps) (extV r ext))) := by
  rw [toOne_rpmGame2]
  unfold ksGameH
  rw [simulateQ_bind, simulateQ_liftM_of_coins _ (fun n ↦ rfl)]
  refine bind_congr fun crs ↦ ?_
  simp only [ksB, relabelAdv, advV0, advV, simulateQ_map, StateT.run_map, simulateQ_bind,
    bind_map_left, map_bind, bind_assoc, simulateQ_pure, pure_bind, map_pure]
  refine bind_congr fun p ↦ ?_
  refine bind_congr fun ok ↦ ?_
  simp only [relationMWithHash, simulateQ_bind, relabel_membershipChallengeM, postKG,
    toK_membershipChallengeM, bind_assoc]
  refine bind_congr fun z ↦ ?_
  simp only [ksPostG, simulateQ_bind, toK_commitCellsM, relabel_commitCellsM, simulateQ_pure,
    pure_bind]
  rfl

/-- **The position-binding adversary followed by the argument's verification.** -/
noncomputable def advP (A : PosBindingAdvRpmH r Crs Proof) (ck : Unit × Crs) :
    OracleComp KSpecH ((Common.DigestBytes × (Proof × Bool)) × Fin (r * 128) × Cell × CellOpening × Cell × CellOpening) := do
  let (com, p, x, τ, x', τ') ← A ck
  let ok ← ps.verify ck.2 com.1 com.2
  pure ((com.1, (com.2, ok)), p, x, τ, x', τ')

/-- The climbs of the position-binding game, with the argument's verdict. -/
def posPostV (_ : Crs)
    (out : (Common.DigestBytes × (Proof × Bool)) × Fin (r * 128) × Cell × CellOpening × Cell × CellOpening) :
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
    (out : (Common.DigestBytes × (Proof × Bool)) × Fin (r * 128) × Cell × CellOpening × Cell × CellOpening) :
    Duplex KState.zero keccakNF (posPostV r crs out) [] :=
  duplex_of_duplexP (Q := fun _ _ ↦ True) <|
    duplexP_bind (duplexP_verifyCellM r _ _ _ _ []) fun _ hist _ ↦
      duplexP_bind (duplexP_verifyCellM r _ _ _ _ hist) fun _ _ _ ↦ duplexP_pure trivial

/-- **A win of the climbs is a collision of `H` in the final cache.** -/
theorem posPostV_win (crs : Crs)
    (out : (Common.DigestBytes × (Proof × Bool)) × Fin (r * 128) × Cell × CellOpening × Cell ×
        CellOpening)
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

/-! ## Code binding -/

section CodeBinding

variable (r : ℕ) {Crs Proof : Type} (ps : ArgumentRpmH r Crs Proof)
  (ext : ExtractorRpmH Common.DigestBytes (Fin (r * 128) → Cell) Crs Proof)

theorem duplex_cbPostV (crs : Crs) (out : CbOut r (PrfV Proof)) :
    Duplex KState.zero keccakNF (cbPostV r ps crs out) [] :=
  duplex_of_duplexP (Q := fun _ _ ↦ True) (duplexP_embH _ _)

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

theorem relabelAdv_advV0 (A : CodeBindingAdvRpmH r Crs Proof) :
    relabelAdv (advV0 r ps A) =
      fun ck ↦ (fun out ↦ (out.1, [])) <$> relabelAdv (advV r ps A) ck := by
  funext ck
  simp only [relabelAdv, advV0, simulateQ_map]

theorem advSim_map {P' : Type} (A : CodeBindingAdvB r Crs P')
    (f : CbOut r P' → CbOut r P') (crs : Crs) :
    advSim r (fun ck ↦ f <$> A ck) crs = f <$> advSim r A crs := by
  simp only [advSim, advS2_map, ← map_bind, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

/-- **The weights of the code-binding game without the openings** follow from the game's. -/
theorem isWeightBound_codeBindingGame2_advV0 (A : CodeBindingAdvRpmH r Crs Proof) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGameH r ps A) permCallsH Q) :
    QueryCostAtMost (codeBindingGame2 r (psV r ps) (relabelAdv (advV0 r ps A))) permCalls2 Q := by
  have hQ' : QueryCostAtMost (rpmGame2 (liftM ps.setup)
      (fun crs ↦ relabelAdv (advV r ps A) ((), crs)) (cbPostV r ps)) permCalls2 Q := by
    rw [← isWeightBound_toOne_iff, ← relabel_codeBindingGame]; exact isWeightBound_relabel hQ
  rw [codeBindingGame2, relabelAdv_advV0]
  refine isWeightBound_rpmGame2_map ps.setup _ _ _ _ Q hQ' fun x a ↦ ?_
  simp only [codeBindingPost, List.map_nil, List.mapM_nil, pure_bind, simulateQ_pure]
  exact isWeightBound_pure _ _ _

theorem ksIdealG_advV0 (A : CodeBindingAdvRpmH r Crs Proof) (crs : Crs) :
    ksIdealG r (psV r ps) (extV r ext) (relabelAdv (advV0 r ps A)) crs =
      ksIdealG r (psV r ps) (extV r ext) (relabelAdv (advV r ps A)) crs := by
  unfold ksIdealG
  rw [← advSim, ← advSim, relabelAdv_advV0, advSim_map, bind_map_left]
  rfl

/-- **From the random-permutation model to the simulated world**, the argument's verification
with the adversary: the two-oracle transfer, the challenges of the root inserted unused before the
climbs (`run'_bind_const`), and the duplex lemma. -/
theorem codeBindingGame_le_G (A : CodeBindingAdvRpmH r Crs Proof) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGameH r ps A) permCallsH Q) :
    Pr{let b ← runKH (codeBindingGameH r ps A)}[b = true] ≤
      prT (codeBindingExpG r (psV r ps) (relabelAdv (advV r ps A))) + (Q ^ 2 : ℝ≥0∞) / 2 ^ 508 +
        dupTerm Q := by
  have hQ0 := isWeightBound_codeBindingGame2_advV0 r ps A Q hQ
  have e := relabel_codeBindingGame r ps A
  have hQ' : QueryCostAtMost (rpmGame2 (liftM ps.setup)
      (fun crs ↦ relabelAdv (advV r ps A) ((), crs)) (cbPostV r ps)) permCalls2 Q := by
    rw [← isWeightBound_toOne_iff, ← e]; exact isWeightBound_relabel hQ
  rw [(runK_relabel _).prEvent_eq, e]
  change Pr{let b ← realGame2 keccakPadding KState.zero _}[b = true] ≤ _
  rw [permCalls2_eq] at hQ'
  obtain ⟨h1, -⟩ := keccak256_transfer2 (liftM ps.setup)
    (fun crs ↦ relabelAdv (advV r ps A) ((), crs)) (cbPostV r ps)
    (fun x a ↦ duplex_cbPostV r ps x a) Q hQ' (· = true)
  refine h1.trans ?_
  rw [add_right_comm]
  refine add_le_add ?_ le_rfl
  have hsplit : Pr{let b ← romRun2 (simulateQ (hInF (E := KRest) (C := KCap)) (liftM ps.setup) >>=
        fun x ↦ advS2 keccakPadding KState.zero (relabelAdv (advV r ps A) ((), x)) >>= fun a ↦
          cbPostV r ps x a)}[b = true] =
      Pr{let b ← ps.setup >>= fun crs ↦ romRun2 (advS2 keccakPadding KState.zero
        (relabelAdv (advV r ps A) ((), crs)) >>= fun out ↦ cbPostV r ps crs out)}[b = true] := by
    rw [romRun2, simulateQ_liftM_of_coins _ (fun _ ↦ rfl), simulateQ_bind,
      StateT.run'_eq, StateT.run_bind, simulateQ_romImpl_liftM_run, bind_map_left, map_bind]
    rfl
  rw [hsplit, codeBindingExpG]
  refine prEvent_bind_le_add_const_of_support _ _ _ _ _ _ fun crs hcrs ↦ ?_
  have hB : QueryCostAtMost (advS2 keccakPadding KState.zero (relabelAdv (advV r ps A) ((), crs)))
      (fCalls (Msg := List UInt8) (Dg := DigestBytes) (St := KState)) Q := by
    have := isWeightBound_advS2 r (psV r ps) _ Q hQ0 crs hcrs
    rw [relabelAdv_advV0] at this
    simp only [advS2_map] at this
    exact (isWeightBound_map_iff _ _ _ _).mp this
  have h1 : Pr{let b ← romRun2 (advS2 keccakPadding KState.zero
        (relabelAdv (advV r ps A) ((), crs)) >>= fun out ↦ cbPostV r ps crs out)}[b = true] =
      Pr{let b ← (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
        (advS2 keccakPadding KState.zero (relabelAdv (advV r ps A) ((), crs)) >>= fun out ↦
          chalR out.1.1 >>= fun zs ↦
            simulateQ embH (postV r (psV r ps) crs out (toVec zs)))).run' ∅}[b = true] := by
    have e : ∀ K : CbOut r (PrfV Proof) → OracleComp Rom2 Bool,
        (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl (advS2 keccakPadding KState.zero
          (relabelAdv (advV r ps A) ((), crs)) >>= K)).run' ∅ =
        (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl (advS2 keccakPadding KState.zero
          (relabelAdv (advV r ps A) ((), crs)))).run ∅ >>= fun z ↦
            (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl (K z.1)).run' z.2 := by
      intro K
      simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind]
    rw [romRun2, e, e]
    refine Common.prEvent_bind_congr _ _ _ _ _ fun z ↦ ?_
    exact ((run'_bind_const (chalR z.1.1.1) (cbPostV r ps crs z.1) z.2).prEvent_eq _).symm
  rw [h1]
  exact duplex_le (D := daDuplex) daDuplex_cap _ Q hB (fun out ↦ out.1.1)
    (fun out l ↦ postV r (psV r ps) crs out l)

/-- **LeanDA is code binding in the random-permutation model, for an argument knowledge sound in
it**, by the straight-line argument built on Benedikt Wagner's framework and games
(`LeanDa.StraightBound`), for the virtual oracle-free argument that reads the verdict of the
argument's verification (`psV`, `extV`): the transfer to the two-oracle model and the duplex lemma
(`codeBindingGame_le_G`), then a win is a break of the argument's knowledge soundness, the
statement's game of the code-binding adversary itself (`relabel_ksGame`, through
`ksIdealG_le_rpmG`: the draws read as the nonce search reads them), or a bad cache of the world
with `H` and the draws lazily sampled (`codeBindingExpG_le`: the hash's bad events, a selected
accepting draw among the adversary's, and the verifier's one fresh try). -/
theorem leanDa_codeBinding_rpm_bound_at (c k : ℕ) (A : CodeBindingAdvRpmH r Crs Proof)
    (hks : ∀ q : ℕ, QueryCostAtMost (ksGameH r ps ext (ksB r A)) permCallsH q → q ≤ 2 ^ 128 →
      Pr{let b ← runKH (ksGameH r ps ext (ksB r A))}[b = true] ≤
        ((q : ℝ≥0∞) + c) * (2 : ℝ≥0∞)⁻¹ ^ k)
    (hrM : r ≤ maxRows) (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGameH r ps A) permCallsH Q) :
    Pr{let b ← runKH (codeBindingGameH r ps A)}[b = true] ≤
      ((Q : ℝ≥0∞) + c + 2 ^ 65) * (2 : ℝ≥0∞)⁻¹ ^ k + ((Q : ℝ≥0∞) + 2 ^ 10) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 247 := by
  rcases le_or_gt Q (2 ^ 127) with hQcap | hQcap
  swap
  · -- past `2^127` the last term is at least one
    refine (prEvent_le_one _).trans (le_add_left (Common.one_le_mul_inv_two_pow ?_))
    calc (2 : ℝ≥0∞) ^ 247 ≤ ((2 : ℝ≥0∞) ^ 127) ^ 2 := by
          rw [← pow_mul]; exact pow_le_pow_right₀ one_le_two (by norm_num)
      _ ≤ ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 := by
        gcongr
        calc (2 : ℝ≥0∞) ^ 127 ≤ (Q : ℝ≥0∞) := by exact_mod_cast hQcap.le
          _ ≤ (Q : ℝ≥0∞) + 2 ^ 22 := le_self_add
  have hQ0 := isWeightBound_codeBindingGame2_advV0 r ps A Q hQ
  have hL := logPaddedRowCount_le_logMaxRows hrM
  have hN := paddedRowCount_le_maxRows hrM
  norm_num [maxRows, logMaxRows] at hL hN
  have hK : ksCalls r Q ≤ Q + 2 ^ 65 := by
    unfold ksCalls relCalls nLabels nonceCount; omega
  -- the argument's knowledge soundness, against the code-binding adversary itself
  have hε : prT (realGame2 keccakPadding KState.zero
      (rpmGame2 (liftM (psV r ps).setup) (fun crs ↦ relabelAdv (advV0 r ps A) ((), crs))
        (postKG r (psV r ps) (extV r ext)))) ≤
      ((Q : ℝ≥0∞) + c + 2 ^ 65) * (2 : ℝ≥0∞)⁻¹ ^ k := by
    have e := relabel_ksGame r ps ext A
    have hW : QueryCostAtMost (ksGameH r ps ext (ksB r A)) permCallsH (ksCalls r Q) := by
      rw [← isWeightBound_relabel_iff, e, isWeightBound_toOne_iff]
      exact isWeightBound_postKGGame r (psV r ps) (extV r ext) _ Q hQ0
    have h := hks (ksCalls r Q) hW (by omega)
    rw [(runK_relabel _).prEvent_eq, e] at h
    refine h.trans (mul_le_mul_left ?_ _)
    have : ((ksCalls r Q : ℕ) : ℝ≥0∞) ≤ (Q : ℝ≥0∞) + 2 ^ 65 := by exact_mod_cast hK
    calc ((ksCalls r Q : ℕ) : ℝ≥0∞) + c ≤ (Q : ℝ≥0∞) + 2 ^ 65 + c := by gcongr
      _ = (Q : ℝ≥0∞) + c + 2 ^ 65 := by ring
  have hG := codeBindingGame_le_G r ps A Q hQ
  have hA : ∀ crs ∈ support (psV r ps).setup,
      QueryCostAtMost (advSim r (relabelAdv (advV r ps A)) crs) hgCalls (2 * Q + 1) ∧
        QueryCostAtMost (advSim r (relabelAdv (advV r ps A)) crs) gwCalls Q := by
    intro crs hcrs
    obtain ⟨h1, h2⟩ := isWeightBound_advSim r (psV r ps) _ Q hQ0 crs hcrs
    rw [relabelAdv_advV0, advSim_map] at h1 h2
    exact ⟨(isWeightBound_map_iff _ _ _ _).mp h1, (isWeightBound_map_iff _ _ _ _).mp h2⟩
  have hS := codeBindingExpG_le r (psV r ps) (extV r ext) (relabelAdv (advV r ps A)) Q hrM hA
  have hKS : prT ((psV r ps).setup >>=
      ksIdealG r (psV r ps) (extV r ext) (relabelAdv (advV r ps A))) ≤
      prT (realGame2 keccakPadding KState.zero
        (rpmGame2 (liftM (psV r ps).setup) (fun crs ↦ relabelAdv (advV0 r ps A) ((), crs))
          (postKG r (psV r ps) (extV r ext)))) +
        ((ksCalls r Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 + dupTerm Q := by
    rw [show ksIdealG r (psV r ps) (extV r ext) (relabelAdv (advV r ps A)) =
      ksIdealG r (psV r ps) (extV r ext) (relabelAdv (advV0 r ps A)) from
        funext fun crs ↦ (ksIdealG_advV0 r ps ext A crs).symm]
    exact ksIdealG_le_rpmG r (psV r ps) (extV r ext) _ (fun _ _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)
      Q hQ0
  have hR := straight_rest_le Q (ksCalls r Q) hK
  calc Pr{let b ← runKH (codeBindingGameH r ps A)}[b = true]
      ≤ prT (codeBindingExpG r (psV r ps) (relabelAdv (advV r ps A))) +
          (Q ^ 2 : ℝ≥0∞) / 2 ^ 508 + dupTerm Q := hG
    _ ≤ prT (realGame2 keccakPadding KState.zero
            (rpmGame2 (liftM (psV r ps).setup) (fun crs ↦ relabelAdv (advV0 r ps A) ((), crs))
              (postKG r (psV r ps) (extV r ext)))) +
          ((((ksCalls r Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 + dupTerm Q +
            (((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) * (65 * ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
              ((Q : ℝ≥0∞) * ((2 ^ 13 - 1) / 2 ^ 138) + (2 ^ 13 - 1) / 2 ^ 128))) +
            ((Q : ℝ≥0∞) ^ 2 / 2 ^ 508 + dupTerm Q)) := by
        refine (add_le_add (add_le_add (hS.trans (add_le_add hKS le_rfl)) le_rfl) le_rfl).trans
          (le_of_eq ?_)
        ring
    _ ≤ ((Q : ℝ≥0∞) + c + 2 ^ 65) * (2 : ℝ≥0∞)⁻¹ ^ k +
          (((Q : ℝ≥0∞) + 2 ^ 10) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
            ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 247) := add_le_add hε hR
    _ = _ := by ring

/-- **Code binding with the hash oracle**, from knowledge soundness against every adversary. -/
theorem leanDa_codeBinding_rpm_boundH : CodeBindingRpmH :=
  fun r _ _ ps ext c k hks _ hrM A ↦
    leanDa_codeBinding_rpm_bound_at r ps ext c k A (hks (ksB r A)) hrM

end CodeBinding

end LeanDa
