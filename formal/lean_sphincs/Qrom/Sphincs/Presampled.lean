module

public import Qrom.Sphincs.Honest

@[expose] public section

/-!
# The presampled game

On the hash `override (proc seed) G h`, which answers the honest positions with the data `h` and the
rest with `G`, the labels of the canonical graph are consistent, so key generation and every
signature are functions of `h` alone (`Qrom.Sphincs.keysOf_override`,
`Qrom.Sphincs.signOf_override`).
-/

open OracleComp OracleSpec FORS FORS.Security FORS.Security.Graph FORS.Security.GraphCorrectness
  FORS.Security.GraphView Concrete

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Qrom.Sphincs

variable [Params] (seed : MasterSeed) (h : Key → HashOutput)

/-- The hash answering the honest positions with `h` and the rest with `G`, on byte strings. -/
def ovFun (G : Input → HashOutput) : HashInput → HashOutput := extend (override (proc seed) G h)

theorem ovFun_input (G : Input → HashOutput) (k : Key) : ovFun seed h G (input h seed k) = h k := by
  rw [ovFun, show input h seed k = ((proc seed).pt h k).1 from rfl, extend_val, override_pt]

theorem otsSecrets_ovFun (G : Input → HashOutput) :
    otsSecrets (QueryImpl.ofFn (ovFun seed h G)) (param h) seed = otsS h := by
  funext lay tree leaf c
  rw [otsSecrets, Completeness.otsSecret_eq]
  exact congrArg truncateHash (ovFun_input seed h G (.ots lay tree leaf c))

theorem ftsSecrets_ovFun (G : Input → HashOutput) :
    ftsSecrets (QueryImpl.ofFn (ovFun seed h G)) (param h) seed = ftsS h := by
  funext index κ leaf
  rw [ftsSecrets, Completeness.forsSecretValue_eq]
  exact congrArg truncateHash (ovFun_input seed h G (.fts index κ leaf))

theorem consistent_ovFun (G : Input → HashOutput) :
    Consistent (QueryImpl.ofFn (ovFun seed h G)) (param h) seed (labelsOf h) := by
  intro p _
  rw [otsSecrets_ovFun, ftsSecrets_ovFun]
  exact (ovFun_input seed h G (.pos p)).symm

theorem keptHeight_top_full : keptHeight topLayer = maxLayerHeight := by
  unfold keptHeight maxLayerHeight heightBelow
  simp [topLayer, Params.full]

theorem boundaryCorrect_ovFun (G : Input → HashOutput) :
    BoundaryCorrect (QueryImpl.ofFn (ovFun seed h G)) (param h) seed (labelsOf h) := by
  intro p v hb
  exfalso
  have hpos := maxLayerHeight_pos
  cases p <;> simp only [PrunedGraph.boundary, keptHeight_top_full, reduceCtorEq] at hb
  · split_ifs at hb with hc
    exact absurd hc.2.2.1 (by omega)
  · split_ifs at hb with h1 hc
    exact absurd hc.2.2.1 (by omega)

/-- The public key and the secret key read from the data. -/
def keysH : PublicKey × Seeded.SecretKey :=
  (⟨(dataOf h).root, param h⟩, ⟨seed, h .prf, param h, (dataOf h).root⟩)

theorem dataCorrect_ovFun (G : Input → HashOutput) :
    DataCorrect (QueryImpl.ofFn (ovFun seed h G)) (param h) seed (dataOf h) :=
  publicData_correct _ _ seed _ (consistent_ovFun seed h G) (boundaryCorrect_ovFun seed h G) _

theorem keysOf_override (G : Input → HashOutput) :
    keysOf seed (override (proc seed) G h) = keysH seed h := by
  have hroot := (dataCorrect_ovFun seed h G).root
  have h0 := ovFun_input seed h G .pkSeed
  have h1 := ovFun_input seed h G .prf
  simp only [input] at h0 h1
  show evalWithAnswerFn (QueryImpl.ofFn (ovFun seed h G)) (Seeded.keygen seed) = keysH seed h
  simp only [Seeded.keygen, Seeded.keygenFromSeed, derivePublicSeed, derivePrf,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, Completeness.eval_oracleHash, QueryImpl.ofFn_apply,
    h0, h1]
  rw [show truncateHash (h Key.pkSeed) = param h from rfl, ← hroot]
  rfl

/-- A full key signs at the randomizer of the message. -/
theorem eval_sign_full (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (m : Message) :
    evalWithAnswerFn f (Seeded.sign sk m : OracleComp HashSpec (Option Signature)) =
      evalWithAnswerFn f (Seeded.finishSign sk m
        (truncateHash (f (randomizerHashInput sk.prf sk.parameter m)))) := by
  have hloop : ∀ step n start, evalWithAnswerFn f (Seeded.signDigestLoop sk m step (n + 1) start :
      OracleComp HashSpec (Option (Randomness × Index))) = some (start, blockIndex
        (evalWithAnswerFn f (messageDigestCall sk.parameter sk.root m start firstCall :
          OracleComp HashSpec HashOutput))) := by
    intro step n start
    rw [Seeded.signDigestLoop, evalWithAnswerFn_bind]
    simp only [Seeded.signAttempt, evalWithAnswerFn_bind, landed_full, ite_true, evalWithAnswerFn_pure]
  have hlim : digestAttemptLimit = (digestAttemptLimit - 1) + 1 := by
    unfold digestAttemptLimit
    decide
  rw [Seeded.sign, evalWithAnswerFn_bind, evalWithAnswerFn_bind, hlim, hloop]
  simp only [Seeded.finishSign, deriveRandomizer, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    Completeness.eval_oracleHash]
  rfl

theorem firstEncoding_congr (f g : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput)
    (h : ∀ counter : Counter, f (Wots.encodingInput parameter lay tree leaf message counter) =
      g (Wots.encodingInput parameter lay tree leaf message counter)) :
    ∀ attempts start, Prefix.firstEncoding f parameter lay tree leaf message attempts start =
      Prefix.firstEncoding g parameter lay tree leaf message attempts start := by
  have hencode : ∀ counter : Counter,
      evalWithAnswerFn f (encode parameter lay tree leaf message counter :
        OracleComp HashSpec (Option Encoding)) =
      evalWithAnswerFn g (encode parameter lay tree leaf message counter :
        OracleComp HashSpec (Option Encoding)) := by
    intro counter
    simp only [encode, evalWithAnswerFn_bind, Completeness.eval_tweakableHash, evalWithAnswerFn_pure]
    rw [show f (tweakableHashInput parameter (.encoding lay tree leaf) (message ++ bytesBE 4 counter)) =
      g (tweakableHashInput parameter (.encoding lay tree leaf) (message ++ bytesBE 4 counter)) from
      h counter]
  intro attempts
  induction attempts with
  | zero => intro start; rfl
  | succ attempts ih =>
      intro start
      simp only [Prefix.firstEncoding, hencode, ih]

/-- The assembled signature reads the hash only at the digest calls and the encoding counters. -/
theorem assembled_congr (f f' : QueryImpl HashSpec Id) (p : PublicParameter) (d : PublicData)
    (t : HiddenGraph.Table) (m : Message) (R : Randomness)
    (hdig : ∀ call, f (messageDigestInput p d.root m R call) = f' (messageDigestInput p d.root m R call))
    (henc : ∀ lay tree leaf c, f (Wots.encodingInput p lay tree leaf (d.keyMessage lay tree leaf) c) =
      f' (Wots.encodingInput p lay tree leaf (d.keyMessage lay tree leaf) c)) :
    assembled f p d t m R = assembled f' p d t m R := by
  have hd : evalWithAnswerFn f (messageDigest p d.root m R : OracleComp HashSpec MessageDigest) =
      evalWithAnswerFn f' (messageDigest p d.root m R : OracleComp HashSpec MessageDigest) := by
    simp only [messageDigest, messageDigestCall, evalWithAnswerFn_bind, Completeness.eval_sequenceFin,
      Completeness.eval_oracleHash, evalWithAnswerFn_pure, hdig]
  have he : ∀ index : Index, (fun lay : Layer ↦ Prefix.firstEncoding f p lay (treeIndexAt index lay)
      (leafIndexAt index lay) (d.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay))
      encodingAttemptLimit 0) = fun lay ↦ Prefix.firstEncoding f' p lay (treeIndexAt index lay)
      (leafIndexAt index lay) (d.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay))
      encodingAttemptLimit 0 :=
    fun index ↦ funext fun lay ↦ firstEncoding_congr f f' p lay _ _ _ (henc lay _ _) _ _
  unfold assembled assembledEncodings
  dsimp only
  rw [hd, he]

/-- The coordinates of the chains and FORS leaves read from the data. -/
def tableOf : HiddenGraph.Table := HiddenGraph.coordinates (otsS h) (ftsS h) (labelsOf h)

/-- The signature of a message read from the data. -/
def signH (m : Message) : Option Signature :=
  assembled (QueryImpl.ofFn (ovFun seed h fun _ ↦ 0)) (param h) (dataOf h) (tableOf h) m (rndOf h m)

theorem signOf_override (G : Input → HashOutput) (m : Message) :
    signOf seed (override (proc seed) G h) m = signH seed h m := by
  unfold signOf
  rw [keysOf_override]
  show evalWithAnswerFn (QueryImpl.ofFn (ovFun seed h G)) (Seeded.sign (keysH seed h).2 m) = _
  rw [eval_sign_full]
  have hR : truncateHash (QueryImpl.ofFn (ovFun seed h G)
      (randomizerHashInput (keysH seed h).2.prf (keysH seed h).2.parameter m)) = rndOf h m :=
    congrArg truncateHash (ovFun_input seed h G (.rnd m))
  rw [hR]
  have htable := coordinates_correct (QueryImpl.ofFn (ovFun seed h G)) (param h) seed (labelsOf h)
    (consistent_ovFun seed h G)
  rw [otsSecrets_ovFun, ftsSecrets_ovFun] at htable
  rw [show (keysH seed h).2 = ⟨seed, h .prf, param h, (dataOf h).root⟩ from rfl,
    eval_finishSign_assembled _ (param h) seed (dataOf h) (tableOf h) (dataCorrect_ovFun seed h G)
      htable (h .prf) m (rndOf h m) (landed_full _ _)]
  exact assembled_congr _ _ _ _ _ _ _
    (fun call ↦ (ovFun_input seed h G (.dig m call)).trans (ovFun_input seed h _ (.dig m call)).symm)
    fun lay tree leaf c ↦ (ovFun_input seed h G (.enc lay tree leaf c)).trans
      (ovFun_input seed h _ (.enc lay tree leaf c)).symm

/-! ## The presampled game -/

/-- The data: `SK.seed` at `none`, the value of each honest position at `some k`. -/
abbrev Data := Option Key → HashOutput

/-- The data of `SK.seed` and the honest values. -/
def combine (seed : MasterSeed) (h : Key → HashOutput) : Data := fun o ↦ o.elim seed h

/-- The presampled game: the honest positions answered from the data, the classical ports read from
it. -/
def presGame (d : Data) : OvGame Input HashOutput Log Port Res where
  init := Log.empty
  ov := fun _ x ↦ if hx : ∃ k, (proc (d none)).pt (fun k ↦ d (some k)) k = x then
    some (d (some (Classical.choose hx))) else none
  trans := portTrans (keysH (d none) fun k ↦ d (some k)).1 (signH (d none) fun k ↦ d (some k))

theorem presGame_answer (s : Log) (G : Input → HashOutput) (x : Input) :
    (presGame (combine seed h)).answer s G x = override (proc seed) G h x := by
  unfold OvGame.answer presGame override
  show (if hx : ∃ k, (proc seed).pt h k = x then some (h (Classical.choose hx)) else none).getD (G x) =
    if hx : ∃ k, (proc seed).pt h k = x then h (Classical.choose hx) else G x
  split <;> rfl

theorem sampled_realGame (G : Input → HashOutput) :
    (realGame seed (override (proc seed) G h)).sampled (override (proc seed) G h) =
      (presGame (combine seed h)).sampled G := by
  refine OvGame.sampled_congr (fun s x ↦ ?_) ?_ rfl
  · rw [presGame_answer]
    rfl
  · simp only [realGame, presGame, keysOf_override]
    congr 1
    funext m
    exact signOf_override seed h G m

theorem sideW_realGame (G : Input → HashOutput) {A : Quantum.QReg} {α : Type}
    (x : Quantum.QComp Spec A (Quantum.QReg.of Unit) α) (ρ : Quantum.SubState A)
    (ev : (Σ u, Quantum.QuantumComp₂.Leaf (Quantum.QReg.of Unit) α u) → Log → Bool) :
    OvGame.sideW (realGame seed (override (proc seed) G h)) (override (proc seed) G h) .instruments
        x ρ ev = OvGame.sideW (presGame (combine seed h)) G .instruments x ρ ev := by
  refine OvGame.sideW_congr (g := realGame seed (override (proc seed) G h))
    (g' := presGame (combine seed h)) (G := override (proc seed) G h) (G' := G)
    (fun s x ↦ ?_) ?_ rfl _ x ρ ev
  · rw [presGame_answer]
    rfl
  · simp only [realGame, presGame, keysOf_override]
    congr 1
    funext m
    exact signOf_override seed h G m

open scoped ENNReal in
/-- **Presampling.** The probability that the adversary wins is its average over the data in the
presampled game. -/
theorem winProb_eq {A : Quantum.QReg} (adv : Adversary A) (ρ : Quantum.SubState A) :
    winProb adv ρ = OvGame.avgSide presGame .instruments (gameProg adv) ρ
      (fun _ _ p s ↦ win p.2.2 s) := by
  set W : MasterSeed → (Input → HashOutput) → ℝ≥0∞ := fun seed H ↦
    OvGame.sideW (realGame seed H) H .instruments (gameProg adv) ρ (fun p s ↦ win p.2.2 s)
  set V : Data → (Input → HashOutput) → ℝ≥0∞ := fun d G ↦
    OvGame.sideW (presGame d) G .instruments (gameProg adv) ρ (fun p s ↦ win p.2.2 s)
  have hY0 : ((Fintype.card HashOutput : ℝ≥0∞) ^ Fintype.card Key) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hYt : ((Fintype.card HashOutput : ℝ≥0∞) ^ Fintype.card Key) ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hpres : ∀ seed, ∑ H, W seed H =
      ((Fintype.card HashOutput : ℝ≥0∞) ^ Fintype.card Key)⁻¹ *
        ∑ h, ∑ G, V (combine seed h) G := by
    intro seed
    have := sum_eq_sum_override (proc seed) (W seed)
    simp only [W, sideW_realGame] at this
    rw [← this, ← mul_assoc, ENNReal.inv_mul_cancel hY0 hYt, one_mul]
  unfold winProb OvGame.avgSide
  rw [← (Equiv.piOptionEquivProd (β := fun _ ↦ HashOutput)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun seed _ ↦ ?_
  rw [← Finset.mul_sum]
  change _ * ∑ H, W seed H = _
  rw [hpres seed, Finset.mul_sum]
  have hcomb : ∀ y, (Equiv.piOptionEquivProd (β := fun _ ↦ HashOutput)).symm (seed, y) =
      combine seed y := fun y ↦ funext fun o ↦ by cases o <;> rfl
  simp only [hcomb]
  rw [← Finset.mul_sum]
  simp only [← Finset.mul_sum]
  rw [← mul_assoc]
  congr 1
  have hinv : ∀ a b : ℝ≥0∞, a ≠ ⊤ → b ≠ ⊤ → (a * b)⁻¹ = a⁻¹ * b⁻¹ := fun a b ha hb ↦
    ENNReal.mul_inv (Or.inr hb) (Or.inl ha)
  have hms : Fintype.card MasterSeed = Fintype.card HashOutput := rfl
  rw [hms]
  simp only [Fintype.card_fun, Fintype.card_option, pow_succ, Nat.cast_mul, Nat.cast_pow]
  have ha : (Fintype.card HashOutput : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hb : (Fintype.card HashOutput : ℝ≥0∞) ^ Fintype.card Input ≠ ⊤ := ENNReal.pow_ne_top ha
  rw [hinv _ _ ha hb, hinv _ _ (ENNReal.mul_ne_top hYt ha) hb, hinv _ _ hYt ha]
  ring

end Qrom.Sphincs
