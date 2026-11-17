module

public import Quantum.StdModel.Qrom.SphincsItsrGame
public import Quantum.StdModel.Sphincs.Hybrid

@[expose] public section

/-!
# B3's ITSR game in runtime 1: the hardwired cells and the averages

Runtime 1 of B3's ITSR game hardwires the cells of the honest table's **non-secret** positions
only (`IsSecret`: the key expansion, the chain starts, the FORS secrets, the randomizers); the
secret values stay external. The non-secret positions form a lazy table (`tableI S0 σ`, positions
`NPos`) whose cells are those of the table `mergeT σ w` of the secret values `σ` and the
non-secret values `w`.

* `hwI θ`: the cells of the non-secret positions of `tabOf θ` at `seedOf θ`, holding their
  values; `covers_hwI` (they are hidden cells), `progsOf_hwI` (every program of the realized
  template hardwires a cell of `hwI θ` with its value), `honest_tabOf` (a function holding the
  values of `tabOf θ` at those cells regroups to a hash under which `tabOf θ` is honest).
* `mkTable_congr_sec`, `digTable_congr_sec`: the table of given secrets reads only the secrets in
  use (`KDIn`).
* `uavg_hwI_eq`: averaging over the hidden values `θ` and the functions `t` a statistic of the
  regrouped function `regroup hmsgRoute (overwrite (hwI θ) t).1` and of the digests of the secrets
  of `tabOf θ` (`digsOf`) is averaging over uniform `H`, `PK.seed`, secrets and randomizers: the
  lazy table law (`sum_sum_fill`), regrouping (`sum_regroup`) and the uniform truncation of the
  secrets (`unifAvg_digs`).
-/

open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open scoped ENNReal

namespace Quantum.StdModel.Sphincs.SphItsr

open Quantum Quantum.Qrom.Sphincs
open Quantum.Qrom (LazyTable regroup sum_regroup regroupEquiv regroup_apply_of_fixed
  regroup_apply_of_second sum_inv_card_smul_fst)
open Quantum.Sponge (Hw overwrite)
open Quantum.Xmss.Hybrid (Covers uavg)
open Quantum.Xmss.Assembly (ProgOf)

/-! ## Secret and non-secret positions -/

instance instDecidablePredIsSecretRt1 : DecidablePred IsSecret := fun p ↦ by
  cases p <;> first | exact isTrue trivial | exact isFalse id

/-- The secret positions. -/
abbrev SPos : Type :=
  {p : Pos // IsSecret p.1}

/-- The non-secret positions. -/
abbrev NPos : Type :=
  {p : Pos // ¬IsSecret p.1}

/-- **The table of the secret values `σ` and the non-secret values `w`.** -/
def mergeT (σ : SPos → PairOut) (w : NPos → PairOut) : QTable :=
  fun p ↦ if h : IsSecret p.1 then σ ⟨p, h⟩ else w ⟨p, h⟩

/-- The secret values of a table. -/
def secPart (v : QTable) : SPos → PairOut :=
  fun s ↦ v s.1

/-- The non-secret values of a table. -/
def nsPart (v : QTable) : NPos → PairOut :=
  fun s ↦ v s.1

theorem mergeT_parts (v : QTable) : mergeT (secPart v) (nsPart v) = v := by
  funext p
  unfold mergeT
  split_ifs <;> rfl

theorem secPart_mergeT (σ : SPos → PairOut) (w : NPos → PairOut) : secPart (mergeT σ w) = σ :=
  funext fun s ↦ dite_eq_left s.2

theorem nsPart_mergeT (σ : SPos → PairOut) (w : NPos → PairOut) : nsPart (mergeT σ w) = w :=
  funext fun s ↦ dite_eq_right s.2

theorem mergeT_secret (σ : SPos → PairOut) (w w' : NPos → PairOut) {p : Pos}
    (hs : IsSecret p.1) : mergeT σ w p = mergeT σ w' p :=
  by unfold mergeT; simp only [hs, ↓reduceDIte]

/-- A structural position is no secret. -/
theorem not_isSecret_of_isStruct {q : RawPos} (h : q.IsStruct) : ¬IsSecret q := by
  cases q <;> first | exact (h : False).elim | exact id

/-! ## The lazy table of the non-secret positions -/

/-- **The lazy table of the non-secret positions** at `SK.seed = S0`, the secret values `σ`
external: the cell of a position is its cell in the table `mergeT σ w`. -/
def tableI (S0 : MasterSeed) (σ : SPos → PairOut) : LazyTable NPos Qrom.HashDomain PairOut where
  cell s w := cellOf S0 s.1 (mergeT σ w)
  pre s s' := s.1.1.rank < s'.1.1.rank
  wf := (measure fun s : NPos ↦ s.1.1.rank).wf
  dep s w w' h := cellOf_congr S0 fun q hq ↦ by
    unfold mergeT
    split_ifs with hs
    · rfl
    · exact h ⟨q, hs⟩ hq
  inj w s s' e := Subtype.ext ((table S0).inj (mergeT σ w) e)

/-- **The hardwired cells of runtime 1 at the hidden values `θ`**: the cells of the non-secret
positions of the table `tabOf θ` at the master seed `seedOf θ`, with their values. -/
noncomputable def hwI (θ : TVals) : Hw PairOut Qrom.HashDomain :=
  (tableI (seedOf θ) (secPart (tabOf θ))).hwOf (nsPart (tabOf θ))

/-- The cell of a non-secret position holds its value. -/
theorem hwI_apply (θ : TVals) (p : Pos) (hp : ¬IsSecret p.1) :
    (hwI θ).1 (cellOf (seedOf θ) p (tabOf θ)) = some (tabOf θ p) := by
  have h := (tableI (seedOf θ) (secPart (tabOf θ))).tableDb_cell (nsPart (tabOf θ))
    (nsPart (tabOf θ)) ⟨p, hp⟩
  change (tableI (seedOf θ) (secPart (tabOf θ))).tableDb (nsPart (tabOf θ)) (nsPart (tabOf θ))
    (cellOf (seedOf θ) p (mergeT (secPart (tabOf θ)) (nsPart (tabOf θ)))) = some (tabOf θ p) at h
  rw [mergeT_parts] at h
  exact h

/-- **The hardwired cells are hidden cells.** -/
theorem covers_hwI (θ : TVals) : Covers (hwI θ) (hidCells θ) ∅ ∅ := by
  refine ⟨fun z hz ↦ ?_, fun _ hx ↦ absurd rfl hx, fun _ hx ↦ absurd rfl hx⟩
  by_contra h
  refine hz ((tableI (seedOf θ) (secPart (tabOf θ))).tableDb_of_forall_ne fun s hs ↦
    h ⟨s.1, ?_⟩)
  change cellOf (seedOf θ) s.1 (tabOf θ) = z
  rw [← mergeT_parts (tabOf θ)]
  exact hs

/-- **Every program of the realized template at `msgPol` hardwires a cell of `hwI θ`** with its
value: the structural positions and the digest cells are no secrets. -/
theorem progsOf_hwI (θ : TVals) : ProgsOfQ (hwI θ) θ := by
  refine ⟨fun p hp ↦ ?_, fun msg ↦ ?_⟩
  · rw [realize_progT hp (seedOf θ) θ]
    exact hwI_apply θ p (not_isSecret_of_isStruct hp)
  · rw [realize_digPort_msgPol ∅ msg (seedOf θ) θ]
    exact hwI_apply θ (digPos msg) id

/-- A function overwritten at the cells of `hwI θ` holds the non-secret values there. -/
theorem overwrite_hwI (θ : TVals)
    (t : (Qrom.HashDomain → PairOut) × (PairOut → Qrom.HashDomain) × (PairOut → Qrom.HashDomain))
    (p : Pos) (hp : ¬IsSecret p.1) :
    (overwrite (hwI θ) t).1 (cellOf (seedOf θ) p (tabOf θ)) = tabOf θ p := by
  change ((hwI θ).1 (cellOf (seedOf θ) p (tabOf θ))).getD _ = _
  rw [hwI_apply θ p hp]
  rfl

/-- **The table is honest under the regrouped function** holding its non-secret values at their
cells. -/
theorem honest_tabOf (θ : TVals) {F : Qrom.HashDomain → PairOut}
    (hF : ∀ p : Pos, ¬IsSecret p.1 → F (cellOf (seedOf θ) p (tabOf θ)) = tabOf θ p) :
    Honest (romWorld.hashOf (regroup hmsgRoute F)) (tabOf θ) where
  out p hs := by
    change (tabOf θ p).1 =
      (Qrom.encodeInput (posInput 0 (tabOf θ) p.1)).elim 0 (regroup hmsgRoute F)
    rw [posInput_seed 0 (seedOf θ) (tabOf θ) hs, encodeInput_posInput]
    change (tabOf θ p).1 = regroup hmsgRoute F (cellOf (seedOf θ) p (tabOf θ))
    rw [regroup_apply_of_fixed (hmsgRoute_of_ne (hmsgCall_cellOf_ne _ _ p)), hF p hs]
  call1 M := by
    have h₀ := encodeInput_digestCell (tabOf θ).publicSeed (tabOf θ).root
      ((tabOf θ).randomizer M) M 0
    have h₁ := encodeInput_digestCell (tabOf θ).publicSeed (tabOf θ).root
      ((tabOf θ).randomizer M) M 1
    rw [show ∀ l, romWorld.hashOf (regroup hmsgRoute F) l =
        (Qrom.encodeInput l).elim 0 (regroup hmsgRoute F) from fun _ ↦ rfl, h₁, Option.elim_some,
      regroup_apply_of_second (hmsgRoute_messageDigestInput _ _ _ _ h₀ h₁)]
    exact (congrArg Prod.snd (hF (digPos M) id)).symm

/-! ## The secrets in use -/

/-- The position of a `PRF` secret. -/
def kdRaw : KeygenDomain → RawPos
  | .oneTimeChain l τ e i => .chainStart l τ e i
  | .forsSecret idx κ s => .forsSecret idx κ s

/-- **A secret in use**: its position is in range. -/
def KDIn (d : KeygenDomain) : Prop :=
  (kdRaw d).InRange

instance instDecidablePredKDIn : DecidablePred KDIn :=
  fun d ↦ inferInstanceAs (Decidable (kdRaw d).InRange)

/-- **The table of given secrets reads only the secrets in use.** -/
theorem mkTable_congr_sec (h : HashInput → HashOutput) (a b : HashOutput)
    {sec sec' : KeygenDomain → HashOutput} (rnd : Message → HashOutput)
    (hs : ∀ d, KDIn d → sec d = sec' d) : mkTable h a b sec rnd = mkTable h a b sec' rnd := by
  funext p
  refine (measure fun p : Pos ↦ p.1.rank).wf.induction
    (C := fun p ↦ mkTable h a b sec rnd p = mkTable h a b sec' rnd p) p fun p ih ↦ ?_
  rw [mkTable_eq, mkTable_eq, mkStep_congr h a b sec rnd p (v' := mkTable h a b sec' rnd) ih]
  obtain ⟨p, hp⟩ := p
  cases p with
  | chainStart l τ e i =>
    exact congrArg (fun y ↦ (y, (0 : HashOutput))) (hs (.oneTimeChain l τ e i) hp)
  | forsSecret idx κ s =>
    exact congrArg (fun y ↦ (y, (0 : HashOutput))) (hs (.forsSecret idx κ s) trivial)
  | _ => rfl

/-- **The table of given digests reads only the secrets in use.** -/
theorem digTable_congr_sec (h : HashInput → HashOutput) (P : PublicParameter)
    {s s' : KeygenDomain → Digest} (r : Message → Digest) (hs : ∀ d, KDIn d → s d = s' d) :
    digTable h P s r = digTable h P s' r :=
  mkTable_congr_sec h 0 (embedDigest P) (embedDigest ∘ r) fun d hd ↦
    congrArg embedDigest (hs d hd)

/-! ## The uniform law of the secrets' digests -/

/-- The digests of a table's secrets: `PK.seed`, the `PRF` secrets, the randomizers. -/
def digsOf (v : QTable) : PublicParameter × (KeygenDomain → Digest) × (Message → Digest) :=
  (v.publicSeed, secDig v, v.randomizer)

/-- The digests of the secrets read only the secret values. -/
theorem digsOf_mergeT (σ : SPos → PairOut) (w : NPos → PairOut) :
    digsOf (mergeT σ w) = digsOf (mergeT σ 0) := by
  have hd : ∀ q : RawPos, IsSecret q → (mergeT σ w).dig q = (mergeT σ 0).dig q := fun q hq ↦
    QTable.dig_congr fun _ ↦ mergeT_secret σ w 0 hq
  refine Prod.ext (hd _ trivial) (Prod.ext (funext fun d ↦ ?_) (funext fun M ↦ hd _ trivial))
  cases d <;> exact hd _ trivial

/-- A secret in use. -/
abbrev InKD : Type :=
  {d : KeygenDomain // KDIn d}

/-- The secret position of a secret in use. -/
def kdPos (d : InKD) : SPos :=
  ⟨⟨kdRaw d.1, d.2⟩, by cases d with | mk d _ => cases d <;> trivial⟩

/-- The positions of the digests of the secrets: `PK.seed`, the `PRF` secrets in use, the
randomizers. -/
def digPosI : Unit ⊕ (InKD ⊕ Message) → SPos
  | .inl _ => ⟨⟨.publicSeed, trivial⟩, trivial⟩
  | .inr (.inl d) => kdPos d
  | .inr (.inr M) => ⟨⟨.prfMsg M, trivial⟩, trivial⟩

theorem digPosI_injective : Function.Injective digPosI := by
  rintro (⟨⟩ | (⟨d, hd⟩ | M)) (⟨⟩ | (⟨d', hd'⟩ | M')) h
  all_goals have h' := congrArg (fun s : SPos ↦ s.1.1) h
  all_goals (try cases d) <;> (try cases d') <;> cases h' <;> rfl

/-- A function on the secrets in use, extended by the digest of `0`. -/
def extKD (g : InKD → Digest) : KeygenDomain → Digest :=
  fun d ↦ if h : KDIn d then g ⟨d, h⟩ else truncateHash 0

/-- The truncation of a pair's first component. -/
def truncFst (u : PairOut) : Digest :=
  truncateHash u.1

theorem card_fiber_truncFst (d : Digest) :
    Fintype.card {u : PairOut // truncFst u = d} =
      Fintype.card (BitVec 128) * Fintype.card HashOutput := by
  rw [← card_fiber_truncateHash d, ← Fintype.card_prod]
  exact Fintype.card_congr
    { toFun := fun u ↦ (⟨u.1.1, u.2⟩, u.1.2)
      invFun := fun p ↦ ⟨(p.1.1, p.2), p.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

theorem digsOf_mergeT_zero (σ : SPos → PairOut) :
    digsOf (mergeT σ 0) = ((truncFst (σ (digPosI (.inl ()))) : PublicParameter),
      extKD (fun d ↦ truncFst (σ (digPosI (.inr (.inl d))))),
      fun M ↦ truncFst (σ (digPosI (.inr (.inr M))))) := by
  have hd : ∀ (q : RawPos) (hq : q.InRange) (hs : IsSecret q),
      (mergeT σ 0).dig q = truncFst (σ ⟨⟨q, hq⟩, hs⟩) := fun q hq hs ↦ by
    unfold QTable.dig
    rw [QTable.out_of_inRange _ hq]
    exact congrArg (fun u : PairOut ↦ truncateHash u.1) (dite_eq_left hs)
  refine Prod.ext (hd .publicSeed trivial trivial) (Prod.ext (funext fun d ↦ ?_)
    (funext fun M ↦ hd (.prfMsg M) trivial trivial))
  change secDig (mergeT σ 0) d = extKD (fun d ↦ truncFst (σ (digPosI (.inr (.inl d))))) d
  unfold extKD
  by_cases h : KDIn d
  · rw [dite_eq_left h]
    cases d with
    | oneTimeChain l τ e i => exact hd _ h trivial
    | forsSecret idx κ s => exact hd _ h trivial
  · rw [dite_eq_right h]
    cases d with
    | oneTimeChain l τ e i =>
      exact congrArg truncateHash
        (dite_eq_right (show ¬(RawPos.chainStart l τ e i).InRange from h))
    | forsSecret idx κ s => exact (h trivial).elim

/-- **The digests of uniform secret values are uniform**: `PK.seed`, the `PRF` secrets (for a
statistic insensitive to the secrets out of use) and the randomizers. -/
theorem unifAvg_digs (Ψ : PublicParameter × (KeygenDomain → Digest) × (Message → Digest) → ℝ≥0∞)
    (hΨ : ∀ P s s' r, (∀ d, KDIn d → s d = s' d) → Ψ (P, s, r) = Ψ (P, s', r)) :
    unifAvg (SPos → PairOut) (fun σ ↦ Ψ (digsOf (mergeT σ 0))) =
      unifAvg PublicParameter fun P ↦ unifAvg (KeygenDomain → Digest) fun s ↦
        unifAvg (Message → Digest) fun r ↦ Ψ (P, s, r) := by
  let e : (Unit ⊕ (InKD ⊕ Message) → Digest) ≃ Digest × ((InKD → Digest) × (Message → Digest)) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Equiv.funUnique Unit Digest) (Equiv.sumArrowEquivProdArrow _ _ _))
  let Ψ₃ : Digest × ((InKD → Digest) × (Message → Digest)) → ℝ≥0∞ :=
    fun x ↦ Ψ (x.1, extKD x.2.1, x.2.2)
  have h1 : (fun σ : SPos → PairOut ↦ Ψ (digsOf (mergeT σ 0))) =
      fun σ ↦ Ψ₃ (e fun x ↦ truncFst (σ (digPosI x))) := by
    funext σ
    rw [digsOf_mergeT_zero]
    rfl
  rw [h1, unifAvg_restrictTrunc truncFst (k := Fintype.card (BitVec 128) *
      Fintype.card HashOutput) (mul_ne_zero Fintype.card_ne_zero Fintype.card_ne_zero)
      card_fiber_truncFst digPosI digPosI_injective (fun g ↦ Ψ₃ (e g)),
    unifAvg_equiv e Ψ₃, unifAvg_prod]
  refine unifAvg_congr fun P ↦ ?_
  rw [unifAvg_prod]
  have h2 := unifAvg_restrict Subtype.val Subtype.val_injective
    (fun g : InKD → Digest ↦ unifAvg (Message → Digest) fun r ↦ Ψ (P, extKD g, r))
  refine h2.symm.trans (unifAvg_congr fun s ↦ unifAvg_congr fun r ↦ hΨ P _ _ r fun d hd ↦ ?_)
  unfold extKD
  rw [dite_eq_left hd]

/-! ## Averages over the lazy table and the regrouped function -/

/-- **The lazy table law, as averages**: overwriting a uniform function at the cells of uniform
values by those values gives a uniform function. -/
theorem unifAvg_fill {Pos' D Y : Type} [Fintype Pos'] [DecidableEq Pos'] [Fintype D]
    [DecidableEq D] [Fintype Y] [Zero Y] (T : LazyTable Pos' D Y) (Ψ : (D → Y) → ℝ≥0∞) :
    unifAvg (Pos' → Y) (fun w ↦ unifAvg (D → Y) fun H ↦ Ψ (T.fill w w H)) =
      unifAvg (D → Y) Ψ := by
  have h : ∑ w, ∑ H, Ψ (T.fill w w H) = Fintype.card (Pos' → Y) • ∑ H, Ψ H :=
    T.sum_sum_fill fun _ H ↦ Ψ H
  unfold unifAvg
  simp only [← Finset.mul_sum]
  rw [h, nsmul_eq_mul, mul_left_comm, ← mul_assoc ((Fintype.card (Pos' → Y) : ℝ≥0∞)⁻¹),
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

/-- **Regrouping, as averages**: a uniform `F` regroups to a uniform `H`. -/
theorem unifAvg_regroup (g : (Qrom.HashDomain → HashOutput) → ℝ≥0∞) :
    unifAvg (Qrom.HashDomain → PairOut) (fun F ↦ g (regroup hmsgRoute F)) =
      unifAvg (Qrom.HashDomain → HashOutput) g := by
  unfold unifAvg
  rw [sum_regroup hmsgRoute g, nsmul_eq_mul, Fintype.card_congr (regroupEquiv hmsgRoute),
    Fintype.card_prod]
  exact inv_mul_mul_cancel Fintype.card_ne_zero _

/-- The functions of runtime 1's classical reads. -/
abbrev TFun : Type :=
  (Qrom.HashDomain → PairOut) × (PairOut → Qrom.HashDomain) × (PairOut → Qrom.HashDomain)

/-- **The average over the hidden values and the functions of runtime 1's reads**: a statistic of
the regrouped function overwritten at the cells of `hwI θ` and of the digests of the secrets of
`tabOf θ`, averaged over uniform `θ` and `t`, is its average over uniform `H`, `PK.seed`, secrets
and randomizers, when it reads only the secrets in use. -/
theorem uavg_hwI_eq
    (Φ : (Qrom.HashDomain → HashOutput) →
      PublicParameter × (KeygenDomain → Digest) × (Message → Digest) → ℝ≥0∞)
    (hΦ : ∀ H P s s' r, (∀ d, KDIn d → s d = s' d) → Φ H (P, s, r) = Φ H (P, s', r)) :
    uavg (fun θ : TVals ↦ ∑ t : TFun, (Fintype.card TFun : ℝ≥0∞)⁻¹ *
        Φ (regroup hmsgRoute (overwrite (hwI θ) t).1) (digsOf (tabOf θ))) =
      unifAvg (Qrom.HashDomain → HashOutput) fun H ↦ unifAvg PublicParameter fun P ↦
        unifAvg (KeygenDomain → Digest) fun s ↦ unifAvg (Message → Digest) fun r ↦
          Φ H (P, s, r) := by
  let G : MasterSeed → QTable → ℝ≥0∞ := fun S0 v ↦
    unifAvg (Qrom.HashDomain → PairOut) fun F ↦
      Φ (regroup hmsgRoute ((tableI S0 (secPart v)).fill (nsPart v) (nsPart v) F)) (digsOf v)
  have h1 : ∀ θ : TVals, ∑ t : TFun, (Fintype.card TFun : ℝ≥0∞)⁻¹ *
      Φ (regroup hmsgRoute (overwrite (hwI θ) t).1) (digsOf (tabOf θ)) =
        G (seedOf θ) (tabOf θ) := fun θ ↦ by
    have h := sum_inv_card_smul_fst (B := (PairOut → Qrom.HashDomain) ×
      (PairOut → Qrom.HashDomain)) fun F : Qrom.HashDomain → PairOut ↦
        Φ (regroup hmsgRoute ((tableI (seedOf θ) (secPart (tabOf θ))).fill (nsPart (tabOf θ))
          (nsPart (tabOf θ)) F)) (digsOf (tabOf θ))
    simp only [smul_eq_mul] at h
    exact h
  rw [show (fun θ : TVals ↦ ∑ t : TFun, (Fintype.card TFun : ℝ≥0∞)⁻¹ *
      Φ (regroup hmsgRoute (overwrite (hwI θ) t).1) (digsOf (tabOf θ))) =
        fun θ ↦ G (seedOf θ) (tabOf θ) from funext h1, uavg_seedOf_tabOf G]
  change unifAvg (MasterSeed × QTable) (fun x ↦ G x.1 x.2) = _
  rw [unifAvg_prod]
  have h2 : ∀ S0 : MasterSeed, unifAvg QTable (G S0) =
      unifAvg (Qrom.HashDomain → HashOutput) fun H ↦ unifAvg PublicParameter fun P ↦
        unifAvg (KeygenDomain → Digest) fun s ↦ unifAvg (Message → Digest) fun r ↦
          Φ H (P, s, r) := fun S0 ↦ by
    let e : (SPos → PairOut) × (NPos → PairOut) ≃ QTable :=
      (Equiv.piEquivPiSubtypeProd (fun p : Pos ↦ IsSecret p.1) fun _ ↦ PairOut).symm
    rw [← unifAvg_equiv e (G S0), unifAvg_prod]
    have h3 : ∀ σ : SPos → PairOut, (unifAvg (NPos → PairOut) fun w ↦ G S0 (e (σ, w))) =
        unifAvg (Qrom.HashDomain → HashOutput) fun H ↦ Φ H (digsOf (mergeT σ 0)) := fun σ ↦ by
      change (unifAvg (NPos → PairOut) fun w ↦ G S0 (mergeT σ w)) = _
      simp only [G, secPart_mergeT, nsPart_mergeT, digsOf_mergeT σ]
      rw [unifAvg_fill (tableI S0 σ) fun F ↦ Φ (regroup hmsgRoute F) (digsOf (mergeT σ 0))]
      exact unifAvg_regroup fun H ↦ Φ H (digsOf (mergeT σ 0))
    rw [unifAvg_congr h3, unifAvg_comm]
    exact unifAvg_congr fun H ↦ unifAvg_digs (Φ H) fun P s s' r h ↦ hΦ H P s s' r h
  rw [unifAvg_congr h2, unifAvg_const]

end Quantum.StdModel.Sphincs.SphItsr

end
