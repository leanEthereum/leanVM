module

public import Quantum.Xmss.Assembly.RecBadMass
public import Quantum.Xmss.Assembly.EncRefined
public import Quantum.Xmss.Assembly.TrialHit
public import Quantum.Xmss.Assembly.HTrial
public import Quantum.Xmss.Assembly.GoodTables

@[expose] public section

/-!
# The off-path and re-grind parts of the `RecBad` mass

RecBadMass reduces `RecBadAvg` to three averaged bounds. Two of them are here.

* **Off the trial's path** (`recOffW_le_miss`, `recOff_step`, `recOffPre_le`, `recOffAvg`):
  EncRefined's refined trial modes (`HMode`) remember the trial's block and its `k`, `k'`
  outcomes; a trial's `h`-read is `RecOff` only where the union misses one of those outcomes
  (`trialOf` names the program's trial up to its rate's digest, `trialUpd_inj`, which `TrialOn`
  allows), which a read leaves with weight at most `2/|Z|` (EncRefined's leak bound). Hence
  `RecOffAvg A good (2/|Z| · clsCap)`.
* **The searches stop at a codeword** (`dwOut`, `dwRdNx`, `dwModedP_prefixR`): CwRec's search
  modes with the mode after a trial's `h`-read depending on its outcome: free after a codeword,
  the next trial otherwise (the challenge prefix is moded so).
* **The persistence invariant** (`DInv`, `dInv_step`, `forallQueries_dInv`): in the decompressed
  basis a read returns the view's cell and keeps the databases, and a program in the table moves
  the view only at table cells (PrefixRun). Every call of the prefix is presented a decompressed
  operator supported on: no `⊥`, hardwired cells in the table, and either some trial of some
  label reads a table cell (`LabHit`) or every selection is the view's first codeword of a search
  of a label of its key (`SelCons`); within a search before trial `j`, the view's digests of the
  earlier trials are no codewords; after the trial's `k`-, `k'`-reads the view holds their
  outcomes.
* **No re-grind hit** (`labHit_of_hitG`, `decHitAW_le_potential`): on the invariant a re-grind
  trial's hit of its key's selected digest is `LabHit`: `j < j'` contradicts the selection's
  earlier non-codewords, `j' < j` the search's, `j = j'` makes the trial the selected input.
* **The trial event, counted** (`tsum_potential_labQ_le`, `decHitAPre_le_labQ`,
  `potential_labQ_initR_le`): `LabHit` is a database event determined off the table, so its
  decompressed weight does not grow along the prefix (DecUniform) and starts at its table
  fraction; with `TrialsOffAll` (no trial block a table `k`-cell) at most
  `|labBlocks| (18 |k'Cells| + |hCells|) / |Z|` (TrialHit's count over the `2^321` trial blocks of
  all labels). `decHitAPre ≤ clsCap · 2^-142 ≤ 2^-75` (`decHitAPre_le_keccak`), `decHitAvg`.
* **Security's good tables** (`trialsOffAll_of_r0G`, `trialsOffAll_frac_le_keccak`,
  `decHitAvg_goodL`): on ReparamR0's good set `TrialHidGood` gives `TrialsOffAll`, which fails
  for at most `2^-173` of the tables (`decHitAPre ≤ clsCap` there): `DecHitAvg A GoodL 2^-74`.
-/

universe u v w

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## Off the trial's path -/

section recOff

theorem recOffW_not_trial (L : HonestTable) {c : HwRead X Z Mem} (hc : ∀ z u, c ≠ .readH z u)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : recOffW L c σ = 0 := by
  unfold recOffW
  exact ite_eq_right fun ⟨_, h⟩ ↦ hc _ _ h

/-- **A trial `h` read in the refined mode `afK' x a c` is off its path only where the union
misses the `k` or the `k'` outcome.** -/
theorem recOffW_le_miss (L : HonestTable) {x : X} {a c z : Z} {u : Mem → Option X → Mem}
    (hz : z = (L.perm (x, a)).2 + c) {l : Layer} {e : KeyIndex}
    (hu : u = liftW cwUpd l e x (L.perm (x, a)).1)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    recOffW L (.readH z u) σ ≤
      diagMass {q : Unit × HwReg X Z Mem | q.2 ∈
        {s | KMiss x a s ∨ K'Miss (L.perm (x, a)).1 c s}} σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  set xi := (L.perm (x, a)).1
  have htr : IsTrial trialUpd (.readH z u : HwRead X Z Mem) := ⟨(z, ⟨l, e, x, xi⟩), by rw [hu]; rfl⟩
  have hc := eq_readH_trialOf trialUpd htr
  obtain ⟨hz', hu'⟩ := HwRead.readH.inj hc
  obtain ⟨-, -, hx, hxi⟩ := trialUpd_inj (t := ⟨l, e, x, xi⟩) (t' := (trialOf trialUpd
    (.readH z u : HwRead X Z Mem)).2) (by rw [← hu', hu]; rfl)
  rw [diagMass_eq_dW _ hσ]
  unfold recOffW
  rw [ite_eq_left htr]
  refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ ?_)
  dsimp only
  by_cases hm : q.2 ∈ {s : HwReg X Z Mem | KMiss x a s ∨ K'Miss xi c s}
  · rw [ite_eq_left hm, one_mul]
    split_ifs
    exacts [le_rfl, hre q]
  · rw [ite_eq_right hm, zero_mul]
    have hka : (union q.2.2.1 q.2.1).k x = some a := not_not.1 fun h ↦ hm (.inl h)
    have hkc : (union q.2.2.1 q.2.1).k' xi = some c := not_not.1 fun h ↦ hm (.inr h)
    refine (ite_eq_right fun h ↦ h.2.2 ⟨xi, hxi.symm, ?_⟩).le
    rw [hx, ← hz']
    exact ⟨[], 0, x, a, (L.perm (x, a)).2, c, rfl, IsTail.nil, hka, by rw [zero_add], hkc, hz⟩

/-- **The step condition of the refined trial modes at a read port, for `recOffW`.** -/
theorem recOff_step_read (L : HonestTable) (μ : HMode) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hok : rdOkH L.perm L.param (liftW cwUpd) μ c) :
    recOffW L c σ + ∑' r, ∑ j, potential (hpot L.perm (rdNxH μ c r) j)
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      ∑ j, potential (hpot L.perm μ j) σ + leakW c σ := by
  rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with _ | ⟨x₀, a⟩ | ⟨x₀, a, c₀⟩
  all_goals try exact False.elim hok
  · obtain ⟨hz, -, l, e, -, hu⟩ := hok
    have h0 : ∀ r, ∑ j, potential (hpot L.perm (rdNxH (HMode.afK' x₀ a c₀)
        (.readH z u : HwRead X Z Mem) r) j) (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) = 0 :=
      fun r ↦ sum_potential_hpot_free L.perm _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero, Fintype.sum_unique]
    show recOffW L (.readH z u) σ ≤ potential (setProj {s | KMiss x₀ a s ∨
      K'Miss (L.perm (x₀, a)).1 c₀ s}) σ + 0
    rw [add_zero, potential_setProj _ hσ]
    exact recOffW_le_miss L hz hu hσ
  · have h := offHead_step_read L .free (.readK x u) hσ hok
    rwa [offHeadW_not_trial (c := .readK x u) L (fun _ _ h ↦ by cases h),
      ← recOffW_not_trial (c := .readK x u) L (fun _ _ h ↦ by cases h) σ] at h
  · have h := offHead_step_read L (.afK x₀ a) (.readK' y u) hσ hok
    rwa [offHeadW_not_trial (c := .readK' y u) L (fun _ _ h ↦ by cases h),
      ← recOffW_not_trial (c := .readK' y u) L (fun _ _ h ↦ by cases h) σ] at h

/-- **The step condition of the refined trial modes for `recOffW`.** -/
theorem recOff_step (L : HonestTable) (μ : HMode) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ)
    (hσ : σ.PosSemidef) (hok : okZH L.perm L.param (liftW cwUpd) μ i) :
    extWeight (hwCost (recOffW L) fun _ _ ↦ 0) i σ +
        ∑' r, ∑ j, potential (hpot L.perm (nxZH μ i r) j) (((runtimeR m0R).step i).branch r σ) ≤
      ∑ j, potential (hpot L.perm μ j) σ + extWeight (hwCost leakW fun _ _ ↦ 0) i σ := by
  rcases i with ((p | c) | c) | T
  · obtain rfl : μ = .free := hok
    have h0 : ∀ r, ∑ j, potential (hpot L.perm (nxZH HMode.free (.inl (.inl (.inl p))) r) j)
        (((runtimeR m0R).step (.inl (.inl (.inl p)))).branch r σ) = 0 :=
      fun r ↦ sum_potential_hpot_free L.perm _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero]
    exact zero_le
  · have hb : ∀ r, ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    simp only [hb]
    exact recOff_step_read L μ c hσ hok
  · obtain rfl : μ = .free := hok
    have h0 : ∀ r, ∑ j, potential (hpot L.perm (nxZH HMode.free (.inl (.inr c)) r) j)
        (((runtimeR m0R).step (.inl (.inr c))).branch r σ) = 0 :=
      fun r ↦ sum_potential_hpot_free L.perm _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero]
    exact zero_le
  · obtain rfl : μ = .free := hok
    have h0 : ∀ r, ∑ j, potential (hpot L.perm (nxZH HMode.free (.inr T) r) j)
        (((runtimeR m0R).step (.inr T)).branch r σ) = 0 :=
      fun r ↦ sum_potential_hpot_free L.perm _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero]
    exact zero_le

variable {q : ℕ} {A : Adversary (X × Z)}

/-- **The off-path mass moves onto the leaks of the trials' `k`, `k'` reads.** -/
theorem recOffPre_le_leak (A : Adversary (X × Z)) (L : HonestTable) :
    recOffPre A L ≤ (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost leakW fun _ _ ↦ 0)) (prefixR A L) initR :=
  totalWeight_le_moded_of_zero (runtimeR m0R) .instruments (hpot L.perm) _ _
    (fun μ i σ hσ hok ↦ recOff_step L μ i σ hσ hok) (prefixR A L) .free (fun _ ↦ rfl)
    (modedEH_realizeT cwUpd (valueAt L) _ (tFreeH_prefixT cwUpd (pubOf L) A)) initR_posSemidef

variable (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The off-path mass of the trial reads along the prefix**: `recOffPre ≤ 2/|Z| · clsCap`. -/
theorem recOffPre_le (L : HonestTable) :
    recOffPre A L ≤ ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞) :=
  (recOffPre_le_leak A L).trans (totalWeight_leakW_le hperm hsign L)

/-- **`RecOffAvg`**: `τO = 2/|Z| · clsCap` (`|Z| = 2^512`), for every good set. -/
theorem recOffAvg (good : HonestTable → Prop) [DecidablePred good] :
    RecOffAvg A good (ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞)) := by
  unfold RecOffAvg
  refine (uavg_mono fun L ↦ ?_).trans (uavg_const_le _)
  by_cases hL : good L
  · rw [ite_eq_left hL]
    exact recOffPre_le hperm hsign L
  · rw [ite_eq_right hL]
    exact zero_le

end recOff

/-! ## The search modes stopping at a codeword -/

section dwModes

open HashSig.OverPermutation

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter)

/-- The mode after a trial with hash output `out`: free if its digest is a codeword (the search
stops), the next trial otherwise. -/
noncomputable def dwOut (lab : RLabel) (base : Randomizer) (j : ℕ) (out : HashOutput) : CwMode :=
  if Codeword.Valid (truncateHash out) then .free else .grd lab base (j + 1)

/-- The mode after a read (CwRec's `cwRdNx`), the search stopping at a codeword. -/
noncomputable def dwRdNx {M' : Type} : CwMode → (c : HwRead X Z M') → c.Result → CwMode
  | .grd lab base j, .readK _ _, r => .afK lab base j (r.1.getD 0)
  | .afK lab base j a, .readK' _ _, r => .afK' lab base j (π (cwBlk P lab base j, a)).1
      ((π (cwBlk P lab base j, a)).2 + r.1.getD 0)
  | .afK' lab base j xi _, .readH _ _, r => dwOut lab base j (out256 (xi + r.1.getD 0))
  | _, _, _ => .free

/-- The mode after a call of runtime 1. -/
noncomputable def dwNxR {M : Type} :
    CwMode → (i : (hwReadSpec X Z M).Port) → (hwReadSpec X Z M).Result i → CwMode
  | _, .inl _, _ => .free
  | μ, .inr c, r => dwRdNx π P μ c r

/-- The mode after a call of the template: a reveal of a single randomizer base starts its
search. -/
noncomputable def dwNxT {M : Type} : CwMode → (i : (XSpec M).Port) → (XSpec M).Result i → CwMode
  | μ, .inl (.inl (.inr c)), r => dwRdNx π P μ c.1 r
  | _, .inr T, r => cwRevNx T fun lab ↦ extendBase r.1 lab
  | _, _, _ => .free

/-- The mode after a call of runtime 2 with record ports, at the hidden values `v`. -/
noncomputable def dwNxZ {M : Type} (v : HPos → Digest) :
    CwMode → (i : (recHwSpec X Z HPos M).Port) → (recHwSpec X Z HPos M).Result i → CwMode
  | μ, .inl (.inl (.inr c)), r => dwRdNx π P μ c r
  | _, .inr T, _ => cwRevNx T fun lab ↦ v (.inr lab)
  | _, _, _ => .free

variable {M : Type} [Fintype M] [DecidableEq M]

/-! ### Runtime 1's searches -/

variable {π P}

omit [Fintype M] [DecidableEq M] in
theorem dwModedP_readCall {hu : RLabel → X → X → M → Option X → M} {μ : CwMode}
    {c : HwRead X Z M} (h : cwRdOk π P hu μ c) (B : QReg) :
    ModedP (L := LocalSig.instruments) (cwOkR π P hu) (dwNxR π P)
      (fun p μ' ↦ μ' = dwRdNx π P μ c p.2.2) μ (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

variable (π P) in
/-- A stateful program of runtime 1 that is moded from every state. -/
def DSMod (hu : RLabel → X → X → M → Option X → M) {B : QReg} {σ α : Type} (μ : CwMode)
    (F : α → CwMode → Prop) (x : StateT σ (QComp (hwReadSpec X Z M) B B) α) : Prop :=
  ∀ s, ModedP (L := LocalSig.instruments) (cwOkR π P hu) (dwNxR π P)
    (fun p μ' ↦ F p.2.2.1 μ') μ (x.run s)

section smod

variable {hu : RLabel → X → X → M → Option X → M} {B : QReg} {σ α β : Type}

omit [Fintype M] [DecidableEq M] in
theorem dSMod_bind {x : StateT σ (QComp (hwReadSpec X Z M) B B) α}
    {k : α → StateT σ (QComp (hwReadSpec X Z M) B B) β} {μ : CwMode} {F : α → CwMode → Prop}
    {G : β → CwMode → Prop} (hx : DSMod π P hu μ F x)
    (hk : ∀ a μ', F a μ' → DSMod π P hu μ' G (k a)) : DSMod π P hu μ G (x >>= k) := by
  intro s
  rw [StateT.run_bind]
  exact modedP₂_bind (F := fun (q : α × σ) μ ↦ F q.1 μ) (F' := fun (q : β × σ) μ ↦ G q.1 μ) _ _
    (hx s)
    fun p μ' h ↦ hk p.1 μ' h p.2

omit [Fintype M] [DecidableEq M] in
theorem dSMod_pure (a : α) {F : α → CwMode → Prop} {μ : CwMode} (h : F a μ) :
    DSMod π P hu μ F (pure a : StateT σ (QComp (hwReadSpec X Z M) B B) α) := by
  intro s
  rw [StateT.run_pure]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem dSMod_map {x : StateT σ (QComp (hwReadSpec X Z M) B B) α} (g : α → β) {μ : CwMode}
    {F : β → CwMode → Prop} (hx : DSMod π P hu μ (fun a ↦ F (g a)) x) :
    DSMod π P hu μ F (g <$> x) := by
  intro s
  rw [StateT.run_map]
  exact modedP_map (F := fun q : β × σ ↦ F q.1) (fun p : α × σ ↦ (g p.1, p.2)) (hx s)

omit [Fintype M] [DecidableEq M] in
theorem dSMod_rdK {lab : RLabel} {base : Randomizer} {j : ℕ} {x : X}
    (hj : j < randomizerAttemptLimit) (hx : x = cwBlk P lab base j) :
    DSMod π P hu (.grd lab base j) (fun a (μ : CwMode) ↦ μ = .afK lab base j a)
      (rdK (M := M) B x) :=
  fun s ↦ modedP₂_bind
    (F := fun r : Option Z × M ↦ fun (μ : CwMode) ↦ μ = .afK lab base j (r.1.getD 0))
    (F' := fun q : Z × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦ μ = .afK lab base j q.1)
    (readCall (.readK x keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k x (r.1.getD 0)]))
    (dwModedP_readCall (μ := .grd lab base j) (c := .readK x keepMem) ⟨hj, hx, rfl⟩ B)
    fun _ _ h ↦ h

omit [Fintype M] [DecidableEq M] in
theorem dSMod_rdK' {lab : RLabel} {base : Randomizer} {j : ℕ} {a : Z} {y : X}
    (hy : y = (π (cwBlk P lab base j, a)).1) :
    DSMod π P hu (.afK lab base j a) (fun c (μ : CwMode) ↦
      μ = .afK' lab base j (π (cwBlk P lab base j, a)).1 ((π (cwBlk P lab base j, a)).2 + c))
      (rdK' (M := M) B y) :=
  fun s ↦ modedP₂_bind (F := fun r : Option Z × M ↦ fun (μ : CwMode) ↦ μ = .afK' lab base j
      (π (cwBlk P lab base j, a)).1 ((π (cwBlk P lab base j, a)).2 + r.1.getD 0))
    (F' := fun q : Z × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦ μ = .afK' lab base j
      (π (cwBlk P lab base j, a)).1 ((π (cwBlk P lab base j, a)).2 + q.1))
    (readCall (.readK' y keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k' y (r.1.getD 0)]))
    (dwModedP_readCall (μ := .afK lab base j a) (c := .readK' y keepMem) ⟨hy, rfl⟩ B)
    fun _ _ h ↦ h

omit [Fintype M] [DecidableEq M] in
theorem dSMod_rdHU {lab : RLabel} {base : Randomizer} {j : ℕ} {xi : X} {z z' : Z}
    {u : M → Option X → M} (hz : z' = z) (hu' : u = hu lab (cwBlk P lab base j) xi) :
    DSMod π P hu (.afK' lab base j xi z)
      (fun w (μ : CwMode) ↦ μ = dwOut lab base j (out256 (xi + w))) (rdHU M B z' u) :=
  fun s ↦ modedP₂_bind (F := fun r : Option X × M ↦ fun (μ : CwMode) ↦
      μ = dwOut lab base j (out256 (xi + r.1.getD 0)))
    (F' := fun q : X × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦
      μ = dwOut lab base j (out256 (xi + q.1)))
    (readCall (.readH z' u) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.h z' (r.1.getD 0)]))
    (dwModedP_readCall (μ := .afK' lab base j xi z) (c := .readH z' u) ⟨hz, hu'⟩ B)
    fun _ _ h ↦ h

end smod

omit [Fintype M] [DecidableEq M] in
/-- **A trial's round of reads.** -/
theorem dSMod_rdRoundU (upd : TrialUpd M) {B : QReg} {lab : RLabel} {base : Randomizer} {j : ℕ}
    (hj : j < randomizerAttemptLimit) {b : X} (hb : b = cwBlk P lab base j) :
    DSMod π P (cwHu1 upd) (.grd lab base j)
      (fun q (μ : CwMode) ↦ μ = dwOut lab base j (out256 q.1))
      (rdRoundU M (upd lab.layer lab.key) π B (0, 0) b) := by
  unfold rdRoundU
  refine dSMod_bind (dSMod_rdK hj (by simp [hb])) fun a μ ha ↦ ?_
  subst ha
  refine dSMod_bind (dSMod_rdK' (a := a) (by simp [hb])) fun c μ hc ↦ ?_
  subst hc
  refine dSMod_bind (dSMod_rdHU (by simp [hb]) (by simp [cwHu1, hb])) fun w μ hw ↦ ?_
  refine dSMod_pure _ ?_
  rw [hw, hb]
  simp only [zero_add]

omit [Fintype M] [DecidableEq M] in
/-- **A trial's hash** of a one-block input whose block is the trial's. -/
theorem dwModedP_hashTrial (upd : TrialUpd M) {B : QReg} {lab : RLabel} {base : Randomizer}
    {j : ℕ} (hj : j < randomizerAttemptLimit) (input : HashInput)
    (hb : blocks input = [cwBlk P lab base j]) :
    ModedP (L := LocalSig.instruments) (cwOkR π P (cwHu1 upd)) (dwNxR π P)
      (fun p (μ : CwMode) ↦ μ = dwOut lab base j p.2.2) (.grd lab base j)
      (hashTrial M (upd lab.layer lab.key) π B input) := by
  have hfold : DSMod π P (cwHu1 upd) (B := B) (.grd lab base j)
      (fun q (μ : CwMode) ↦ μ = dwOut lab base j (out256 q.1))
      ((blocks input).foldlM (rdRoundU M (upd lab.layer lab.key) π B) (0, 0)) := by
    rw [hb]
    exact dSMod_bind (dSMod_rdRoundU upd hj rfl) fun s' μ h ↦ dSMod_pure s' h
  exact modedP_map (F := fun out (μ : CwMode) ↦ μ = dwOut lab base j out) Prod.fst
    (dSMod_map (F := fun out (μ : CwMode) ↦ μ = dwOut lab base j out) (out256 : X → HashOutput)
      (dSMod_map (F := fun x (μ : CwMode) ↦ μ = dwOut lab base j (out256 x)) (fun s : X × Z ↦ s.1)
        hfold) [])

omit [Fintype M] [DecidableEq M] in
/-- **The randomizer search** of a label from its base, from its trial `trial`, ends between
trials. -/
theorem dwModedP_grindR (upd : TrialUpd M) (pub : Pub) {B : QReg} (lab : RLabel)
    (base : Randomizer) :
    ∀ n trial, trial + n ≤ randomizerAttemptLimit →
      ModedP (L := LocalSig.instruments) (cwOkR pub.perm pub.param (cwHu1 upd))
      (dwNxR pub.perm pub.param) (fun _ (μ : CwMode) ↦ μ.Idle) (.grd lab base trial)
      (grindR M upd pub B lab.layer lab.key lab.msg base n trial)
  | 0, _, _ => trivial
  | n + 1, trial, hn => by
    rw [grindR]
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (length_blocks_trial pub.param
      (hashDomainFields (.message lab.layer lab.key)) (RLabel.length_msg_le lab) base trial)
    have hbk : cwBlk pub.param lab base trial = b := by simp [cwBlk, hb]
    refine modedP₂_bind (F := fun out (μ : CwMode) ↦ μ = dwOut lab base trial out)
      (F' := fun _ (μ : CwMode) ↦ μ.Idle) _ _
      (dwModedP_hashTrial upd (by omega) _ (hb.trans (by rw [hbk]))) fun out μ hμ ↦ ?_
    subst hμ
    show ModedP _ _ _ _ (match Codeword.decode (truncateHash out) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindR M upd pub B lab.layer lab.key lab.msg base n (trial + 1))
    split
    · unfold dwOut
      split_ifs <;> trivial
    · rename_i hd
      have hv : ¬ Codeword.Valid (truncateHash out) := fun h ↦ by
        rw [Codeword.decode, ite_eq_left h] at hd
        exact Option.some_ne_none _ hd
      rw [dwOut, ite_eq_right hv]
      exact dwModedP_grindR upd pub lab base n (trial + 1) (by omega)

/-! ### Lifting the modes to the template and to runtime 2 -/

omit [Fintype M] [DecidableEq M] in
/-- **Lifting runtime 1's moded programs to templates.** -/
theorem dwModedP_readLift {hu : RLabel → X → X → M → Option X → M} {Ω : QReg → Type} {A : QReg}
    {fin : (Σ u, Ω u) → CwMode → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec X Z M) Ω A) {μ : CwMode}
    (hy : ModedP (cwOkR π P hu) (dwNxR π P) fin μ y) :
    ModedP (cwOkT π P (cwLiftHu hu)) (dwNxT π P) fin μ (readLift goodAll y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨cwRdOk_liftRead hy.1, fun b ↦ ?_⟩
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;>
        rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z'⟩ <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

omit [Fintype M] [DecidableEq M] in
/-- A sponge program of runtime 1 is moded between trials. -/
theorem dwModedP_liftOrdinary {hu : RLabel → X → X → M → Option X → M} {Ω : QReg → Type}
    {A : QReg} (y : QuantumComp LocalSig.instruments (spongeSpec X Z) Ω A) :
    ∀ μ : CwMode, μ.Idle → ModedP (cwOkR π P hu) (dwNxR π P) (fun _ (μ : CwMode) ↦ μ.Idle) μ
      (y.liftOrdinary (t := hwReadCmdSpec X Z M)) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => exact fun _ h ↦ h
  | liftBind _ c next ih =>
    intro μ hμ
    show ModedP _ _ _ _ (IFreeM.mapLens QuantumComp.ordinaryLens (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ μ hμ⟩
    · exact ⟨hμ, fun b ↦ ih _ .free trivial⟩

omit [Fintype M] [DecidableEq M] in
theorem dwNxZ_rec_eq (v : HPos → Digest) (μ : CwMode) (T : Finset HPos)
    (m : Finset HPos × M) :
    dwNxZ (M := M) π P v μ (.inr T) m = dwNxT π P μ (.inr T) (restrictTo T v, m) :=
  cwRevNx_congr fun lab hl ↦ (extendBase_restrictTo
    (by rw [cwRevLab_spec hl]; exact Finset.mem_singleton_self _) v).symm

omit [Fintype M] [DecidableEq M] in
/-- **Realizing keeps the modes.** -/
theorem dwModedP_realizeT {hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M}
    (v : HPos → Digest) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → CwMode → Prop} (y : QuantumComp L (XSpec M) Ω A)
    {μ : CwMode} (hy : ModedP (cwOkT π P hu) (dwNxT π P) fin μ y) :
    ModedP (cwOkZ π P hu) (dwNxZ π P v) fin μ (realizeT v y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (tmplLens v) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · cases p <;> exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hy.1, fun b ↦ ?_⟩
      have h := ih _ (hy.2 (ULift.up (restrictTo T v, b.down)))
      exact (congrArg (fun μ' ↦ ModedP (cwOkZ π P hu) (dwNxZ π P v) fin μ' _)
        (dwNxZ_rec_eq (π := π) (P := P) v μ T b.down)).mpr h

/-! ### The challenge prefix is moded -/

section trialPrefix

variable (π P) in
/-- A template moded between trials: from every mode between trials, it ends between trials. -/
def DIdle (hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M)
    {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments (XSpec M) Ω A) : Prop :=
  ∀ μ : CwMode, μ.Idle → ModedP (cwOkT π P hu) (dwNxT π P) (fun _ (μ : CwMode) ↦ μ.Idle) μ y

variable {hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M}

omit [Fintype M] [DecidableEq M] in
theorem dIdle_bind {A B B' : QReg} {α β : Type} (x : QComp (XSpec M) A B α)
    (g : α → QComp (XSpec M) B B' β) (hx : DIdle π P hu x) (hg : ∀ a, DIdle π P hu (g a)) :
    DIdle π P hu (x.bind g) :=
  fun μ hμ ↦ modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Idle) (F' := fun _ (μ : CwMode) ↦ μ.Idle)
    x g (hx μ hμ) fun a μ' h ↦ hg a μ' h

omit [Fintype M] [DecidableEq M] in
theorem dIdle_pure {A : QReg} {α : Type} (a : α) :
    DIdle π P hu (QuantumComp₂.pure (L := LocalSig.instruments) (spec := XSpec M) (A := A) a) :=
  fun _ h ↦ h

omit [Fintype M] [DecidableEq M] in
theorem dIdle_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    DIdle π P hu (QComp.act (spec := XSpec M) p) :=
  fun _ hμ ↦ ⟨trivial, fun _ ↦ hμ⟩

omit [Fintype M] [DecidableEq M] in
theorem dwNxT_rec_idle (μ : CwMode) (T : Finset HPos)
    (r : (XSpec M).Result (.inr T)) : (dwNxT π P μ (.inr T) r).Idle :=
  cwRevNx_idle T _

omit [Fintype M] [DecidableEq M] in
theorem dIdle_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B B' α)
    (hk : ∀ r, DIdle π P hu (k r)) : DIdle π P hu (revealThen goodAll T k) :=
  fun μ hμ ↦ ⟨hμ, fun b ↦ dIdle_bind _ _ (dIdle_act _) (fun _ ↦ hk b.down) _
    (dwNxT_rec_idle (π := π) (P := P) μ T b.down)⟩

omit [Fintype M] [DecidableEq M] in
/-- The reveal of a label's randomizer base starts its search. -/
theorem dIdle_revealLab {B B' : QReg} {α : Type} (lab : RLabel)
    (k : RevealVals XD {.inr lab} × (Finset HPos × M) → QComp (XSpec M) B B' α)
    (hk : ∀ r, ModedP (cwOkT π P hu) (dwNxT π P) (fun _ (μ : CwMode) ↦ μ.Idle)
      (.grd lab (extendBase r.1 lab) 0) (k r)) :
    DIdle π P hu (revealThen goodAll {.inr lab} k) := by
  intro μ hμ
  refine ⟨hμ, fun b ↦ ?_⟩
  have he : dwNxT (M := M) π P μ (.inr {.inr lab}) b.down =
      .grd lab (extendBase b.down.1 lab) 0 :=
    cwRevNx_lab lab _
  rw [show modeCmdNx (dwNxT (M := M) π P) (QuantumComp.Cmd.query (L := LocalSig.instruments)
    (.inr {.inr lab}) B _) μ b = dwNxT (M := M) π P μ (.inr {.inr lab}) b.down from rfl, he]
  exact modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ = .grd lab (extendBase b.down.1 lab) 0)
    (F' := fun _ (μ : CwMode) ↦ μ.Idle) _ _ ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ h ▸ hk b.down

omit [Fintype M] [DecidableEq M] in
theorem dIdle_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec M) B B' α) (hk : DIdle π P hu k) : DIdle π P hu (progThen p hp k) :=
  fun _ hμ ↦ ⟨hμ, fun _ ↦ dIdle_bind _ _ (dIdle_act _) (fun _ ↦ hk) _ trivial⟩

omit [Fintype M] [DecidableEq M] in
theorem dIdle_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    DIdle π P hu (progPorts M B ps) := by
  induction ps with
  | nil => exact dIdle_pure _
  | cons p ps ih => exact dIdle_progThen p trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem dIdle_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    DIdle π P hu (progSlots M pub B ss) := by
  induction ss with
  | nil => exact dIdle_pure _
  | cons s ss ih => exact dIdle_bind _ _ (dIdle_progPorts B _) fun _ ↦ ih

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
theorem dIdle_signLayerT (pub : Pub) (B : QReg) (lab : RLabel) :
    DIdle pub.perm pub.param (cwLiftHu (cwHu1 upd)) (signLayerT M upd pub B lab) := by
  refine dIdle_revealLab lab _ fun r₀ ↦ ?_
  refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Idle) (F' := fun _ (μ : CwMode) ↦ μ.Idle) _ _
    (dwModedP_readLift _ (dwModedP_grindR upd pub lab _ _ _ (by omega))) fun g μ hμ ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · exact hμ
  · exact dIdle_revealThen _ _ (fun r ↦ dIdle_bind _ _ (dIdle_progSlots pub B _)
      fun _ ↦ dIdle_pure _) μ hμ

omit [Fintype M] [DecidableEq M] in
theorem dIdle_signT (pub : Pub) (B : QReg) (r : SigningRequest) :
    DIdle pub.perm pub.param (cwLiftHu (cwHu1 upd)) (signT M upd pub B r) := by
  refine dIdle_bind _ _ (dIdle_signLayerT upd pub B _) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · exact dIdle_pure _
  · refine dIdle_bind _ _ (dIdle_signLayerT upd pub B _) fun t ↦ ?_
    rcases t with _ | ⟨top, _⟩ <;> exact dIdle_pure _

omit [Fintype M] [DecidableEq M] in
theorem dIdle_challengeT (pub : Pub) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    ∀ μ : CwMode, μ.Idle → ModedP (cwOkT pub.perm pub.param (cwLiftHu (cwHu1 upd)))
      (dwNxT pub.perm pub.param) (fun _ (μ : CwMode) ↦ μ.Idle) μ (challengeT M upd pub A c) := by
  intro μ hμ
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact dwModedP_readLift _ (dwModedP_liftOrdinary _ μ hμ)
  · exact dwModedP_readLift _ (dwModedP_liftOrdinary _ μ hμ)
  · exact modedP_bind _ _ (dIdle_bind _ _ (dIdle_act _) (fun _ ↦ dIdle_signT upd pub _ r) μ hμ)
      fun _ _ μ' h ↦ h

omit [Fintype M] [DecidableEq M] in
/-- Substituting trees moded between trials. -/
theorem dwModedP_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (XSpec M)))
    (hσ : ∀ A c, ∀ μ : CwMode, μ.Idle → ModedP (cwOkT π P hu) (dwNxT π P)
      (fun _ (μ : CwMode) ↦ μ.Idle) μ (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ∀ μ : CwMode, μ.Idle → ModedP (cwOkT π P hu) (dwNxT π P) (fun _ (μ : CwMode) ↦ μ.Idle) μ
      (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact fun _ h ↦ h
  | liftBind s c next ih =>
    intro μ hμ
    rw [IFreeM.substitute_liftBind]
    exact modedP_bind _ _ (hσ s c μ hμ) fun u ans μ' h ↦ (modedP_cast ans.2 _ _).mpr
      (ih ans.1 μ' h)

omit [Fintype M] [DecidableEq M] in
/-- **The challenge prefix is moded**: its reads are the searches' trials. -/
theorem dIdle_prefixT (pub : Pub) (A : Adversary (X × Z)) :
    DIdle pub.perm pub.param (cwLiftHu (cwHu1 upd)) (prefixT M upd pub A) :=
  dIdle_revealThen _ _ fun _ ↦ dIdle_bind _ _
    (dwModedP_substitute _ (dIdle_challengeT upd pub) _) fun _ ↦ dIdle_pure _

omit [Fintype M] [DecidableEq M] in
/-- **The realized challenge prefix is moded** with the searches stopping at a codeword, from the
free mode. -/
theorem dwModedP_prefixR (pub : Pub) (A : Adversary (X × Z)) (v : HPos → Digest) :
    ModedP (cwOkZ pub.perm pub.param (cwLiftHu (cwHu1 upd))) (dwNxZ pub.perm pub.param v)
      (fun _ (μ : CwMode) ↦ μ.Idle) .free (realizeT v (prefixT M upd pub A)) :=
  dwModedP_realizeT v _ (dIdle_prefixT upd pub A .free trivial)

end trialPrefix

end dwModes

/-! ## Support invariants and potentials along runs -/

section dwGeneric

variable {spec : QuantumOracleSpec.{0, 0}} {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}
  (R : QuantumRuntime spec) (I : Λ.Interp)

/-- **A support invariant per mode, on the calls of guarded ports**: if every allowed call of a
port satisfying `G` keeps the support in the invariant of its mode, a moded program whose calls
are all of such ports, run from an operator supported on the invariant of its first mode,
presents every call an operator supported on the invariant of a mode allowing it. -/
theorem forallQueries_of_modedP_guard {Mode : Type} {ok : Mode → spec.Port → Prop}
    {nx : Mode → (i : spec.Port) → spec.Result i → Mode} (Inv : Mode → Set R.D)
    (G : spec.Port → Prop)
    (hstep : ∀ μ i r (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ), ok μ i → G i →
      QuerySupportedOn (fun m : spec.In i × R.D ↦ m.2) (Inv μ) σ →
      QuerySupportedOn (fun m : spec.Out i × R.D ↦ m.2) (Inv (nx μ i r)) ((R.step i).branch r σ))
    {fin : (Σ u, Ω u) → Mode → Prop} {A : QReg} (x : QuantumComp Λ spec Ω A) :
    ∀ μ, ModedP ok nx fin μ x → ∀ {ρ : Matrix (A × R.D) (A × R.D) ℂ},
      R.ForallQueries I (fun i _ _ ↦ G i) x ρ →
      QuerySupportedOn (fun m : A × R.D ↦ m.2) (Inv μ) ρ →
      R.ForallQueries I (fun i E σ ↦ ∃ μ, ok μ i ∧
        QuerySupportedOn (fun m : (spec.In i × R.D) × E ↦ m.1.2) (Inv μ) σ) x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro μ hx ρ hg hρ
    rw [QuantumRuntime.forallQueries_primBind_iff] at hg ⊢
    exact fun b ↦ ih b μ (hx.2 (ULift.up b)) (hg b)
      (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro μ hx ρ hg hρ
    rw [QuantumRuntime.forallQueries_queryBind_iff] at hg ⊢
    refine ⟨⟨μ, hx.1, ?_⟩, fun r ↦ ih r _ (hx.2 (ULift.up r)) (hg.2 r)
      (Hybrid.querySupportedOn_queryStep R (fun s ↦ s) i r
        (fun σ h ↦ hstep μ i r σ hx.1 hg.1 h) E ℓ hρ)⟩
    exact (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
      (q' := fun m : (spec.In i × R.D) × E ↦ m.1.2) (S' := Inv μ) fun m hm ↦ by
        obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
        rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

/-- A port commuting with `conj Q` does not raise the potential of `Q`. -/
theorem tsum_potential_branch_le (i : spec.Port) (Q : Matrix R.D R.D ℂ)
    (hc : ∀ r, (R.step i).branch r ∘ₗ (MatrixMap.conj Q).amplifyLeft (spec.In i) =
      (MatrixMap.conj Q).amplifyLeft (spec.Out i) ∘ₗ (R.step i).branch r)
    {σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ} (hσ : σ.PosSemidef) :
    ∑' r, potential Q ((R.step i).branch r σ) ≤ potential Q σ := by
  have h : ∀ r, (MatrixMap.conj Q).amplifyLeft (spec.Out i) ((R.step i).branch r σ) =
      (R.step i).branch r ((MatrixMap.conj Q).amplifyLeft (spec.In i) σ) := fun r ↦
    (LinearMap.congr_fun (hc r) σ).symm
  simp only [potential, h]
  refine (R.step i).isCPTNIFamily.tsum_ofReal_trace_re_le ?_
  rw [MatrixMap.amplifyLeft_conj]
  exact hσ.mul_mul_conjTranspose_same _

/-- **A charged weight below a non-increasing potential**: if every call of a guarded port
weighs at most its charge times the potential of `K`, and does not raise that potential, a
program of charge at most `n` whose calls are all guarded weighs at most `n` times the initial
potential. -/
theorem totalWeight_le_charge_potential {Zp : Type} [Fintype Zp] (K : Matrix Zp R.D ℂ)
    (κ : spec.Port → ℕ) (G : spec.Port → Prop)
    (w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (hw : ∀ i σ, σ.PosSemidef → G i → w i σ ≤ κ i * potential K σ)
    (hd : ∀ i, G i → ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ, σ.PosSemidef →
      ∑' r, potential K ((R.step i).branch r σ) ≤ potential K σ)
    {A : QReg} (x : QuantumComp Λ spec Ω A) :
    ∀ {n : ℕ}, IFreeM.IsChargeBound x (portCharge κ) n →
      ∀ {ρ : Matrix (A × R.D) (A × R.D) ℂ}, ρ.PosSemidef →
        R.ForallQueries I (fun i _ _ ↦ G i) x ρ → R.totalWeight I w x ρ ≤ n * potential K ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ =>
    intro n _ ρ _ _
    simp
  | primBind _ o k ih =>
    intro n hx ρ hρ hG
    rw [isChargeBound_portCharge_primBind_iff] at hx
    rw [totalWeight_primBind]
    calc ∑' b, R.totalWeight I w (k b) (((I o).frame R.D).branch b ρ)
        ≤ ∑' b, (n : ℝ≥0∞) * potential K (((I o).frame R.D).branch b ρ) :=
          ENNReal.tsum_le_tsum fun b ↦
            ih b (hx b) (((I o).frame R.D).posSemidef_branch_apply b hρ) (hG b)
      _ = n * ∑' b, potential K (((I o).frame R.D).branch b ρ) := ENNReal.tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left (tsum_potential_frame_le K (I o) hρ) zero_le
  | queryBind _ i E ℓ k ih =>
    intro n hx ρ hρ hG
    rw [isChargeBound_portCharge_queryBind_iff] at hx
    rw [QuantumRuntime.forallQueries_queryBind_iff] at hG
    rw [totalWeight_queryBind]
    have hσ := posSemidef_callInput ℓ hρ
    have hs : ∑' r, R.totalWeight I w (k r) ((R.queryStep i E ℓ).branch r ρ) ≤
        ((n - κ i : ℕ) : ℝ≥0∞) * potential K ρ := by
      refine (ENNReal.tsum_le_tsum fun r ↦ ih r (hx.2 r)
        ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ) (hG.2 r)).trans ?_
      rw [ENNReal.tsum_mul_left]
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      simp only [potential_queryStep]
      rw [← potential_callInput K ℓ ρ]
      exact hd i hG.1 _ hσ
    calc w i (callInput ℓ R.D ρ) + ∑' r, R.totalWeight I w (k r) ((R.queryStep i E ℓ).branch r ρ)
        ≤ κ i * potential K ρ + ((n - κ i : ℕ) : ℝ≥0∞) * potential K ρ :=
          add_le_add (by rw [← potential_callInput K ℓ ρ]; exact hw i _ hσ hG.1) hs
      _ = n * potential K ρ := by rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hx.1]

end dwGeneric

/-! ## Decompressed event weights as diagonal sums -/

section dwTrace

variable {X₁ Z₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [AddCommGroup X₁] [AddCommGroup Z₁] {M₁ : Type} [Fintype M₁] [DecidableEq M₁]
  {n : Type} [Fintype n] [DecidableEq n]

omit [AddCommGroup X₁] [AddCommGroup Z₁] in
/-- **The weight of a decompressed event** is the decompressed diagonal summed over the event. -/
theorem re_trace_hwDecProj_eq (E : Set (HwReg X₁ Z₁ M₁)) {_ : DecidablePred (· ∈ E)}
    (σ : Matrix (n × HwReg X₁ Z₁ M₁) (n × HwReg X₁ Z₁ M₁) ℂ) :
    (((1 : Matrix n n ℂ) ⊗ₖ hwDecProj E) * σ).trace.re =
      ∑ a, if a.2 ∈ E then
        (MatrixMap.conj ((1 : Matrix n n ℂ) ⊗ₖ compressReg X₁ Z₁ M₁) σ a a).re else 0 := by
  set C : Matrix (n × HwReg X₁ Z₁ M₁) (n × HwReg X₁ Z₁ M₁) ℂ :=
    (1 : Matrix n n ℂ) ⊗ₖ compressReg X₁ Z₁ M₁ with hC
  set D : Matrix (n × HwReg X₁ Z₁ M₁) (n × HwReg X₁ Z₁ M₁) ℂ :=
    diagonal (fun a : n × HwReg X₁ Z₁ M₁ ↦ if a.2 ∈ E then (1 : ℂ) else 0) with hD
  have hdec : (1 : Matrix n n ℂ) ⊗ₖ hwDecProj E = C * D * C := by
    rw [hwDecProj, hC, hD, ← rb_one_kron_diagonal (fun s : HwReg X₁ Z₁ M₁ ↦
      if s ∈ E then (1 : ℂ) else 0), ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
      Matrix.one_mul]
  have hconj : MatrixMap.conj C σ = C * σ * C := by
    rw [MatrixMap.conj_apply, hC, conjTranspose_one_kron_compressReg]
  rw [hdec, hconj, show C * D * C * σ = C * (D * (C * σ)) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm C, show D * (C * σ) * C = D * (C * σ * C) by
      simp only [Matrix.mul_assoc], hD, rb_trace_diagonal_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases h : a.2 ∈ E <;> simp [h]

omit [AddCommGroup X₁] [AddCommGroup Z₁] in
/-- **Comparing decompressed event weights on a support**: on an operator whose decompressed form
is supported on `S`, the weight of `E` is at most that of `E'` if `E ∩ S ⊆ E'`. -/
theorem re_trace_hwDecProj_le (E E' S : Set (HwReg X₁ Z₁ M₁)) {_ : DecidablePred (· ∈ E)}
    {_ : DecidablePred (· ∈ E')} {σ : Matrix (n × HwReg X₁ Z₁ M₁) (n × HwReg X₁ Z₁ M₁) ℂ}
    (hσ : σ.PosSemidef)
    (hS : QuerySupportedOn (fun m : n × HwReg X₁ Z₁ M₁ ↦ m.2) S
      (MatrixMap.conj ((1 : Matrix n n ℂ) ⊗ₖ compressReg X₁ Z₁ M₁) σ))
    (hE : ∀ s ∈ S, s ∈ E → s ∈ E') :
    (((1 : Matrix n n ℂ) ⊗ₖ hwDecProj E) * σ).trace.re ≤
      (((1 : Matrix n n ℂ) ⊗ₖ hwDecProj E') * σ).trace.re := by
  rw [re_trace_hwDecProj_eq, re_trace_hwDecProj_eq]
  have hpsd : (MatrixMap.conj ((1 : Matrix n n ℂ) ⊗ₖ compressReg X₁ Z₁ M₁) σ).PosSemidef := by
    rw [MatrixMap.conj_apply]
    exact hσ.mul_mul_conjTranspose_same _
  refine Finset.sum_le_sum fun a _ ↦ ?_
  have hre := (Complex.nonneg_iff.1 (hpsd.diag_nonneg (i := a))).1
  by_cases h0 : MatrixMap.conj ((1 : Matrix n n ℂ) ⊗ₖ compressReg X₁ Z₁ M₁) σ a a = 0
  · rw [h0, Complex.zero_re]
    split_ifs <;> exact le_rfl
  · by_cases hE1 : a.2 ∈ E
    · rw [ite_eq_left hE1, ite_eq_left (hE _ (hS a a h0).1 hE1)]
    · rw [ite_eq_right hE1]
      split_ifs
      exacts [hre, le_rfl]

/-- A decompressed event weighs at most the trace. -/
theorem re_trace_hwDecProj_le_trace (E : Set (HwReg X₁ Z₁ M₁)) {_ : DecidablePred (· ∈ E)}
    {σ : Matrix (n × HwReg X₁ Z₁ M₁) (n × HwReg X₁ Z₁ M₁) ℂ} (hσ : σ.PosSemidef) :
    (((1 : Matrix n n ℂ) ⊗ₖ hwDecProj E) * σ).trace.re ≤ σ.trace.re := by
  rw [re_trace_hwDecProj_eq]
  set C : Matrix (n × HwReg X₁ Z₁ M₁) (n × HwReg X₁ Z₁ M₁) ℂ :=
    (1 : Matrix n n ℂ) ⊗ₖ compressReg X₁ Z₁ M₁ with hC
  have hpsd : (MatrixMap.conj C σ).PosSemidef := by
    rw [MatrixMap.conj_apply]
    exact hσ.mul_mul_conjTranspose_same _
  have htr : (MatrixMap.conj C σ).trace = σ.trace := by
    rw [MatrixMap.conj_apply, hC, conjTranspose_one_kron_compressReg, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self,
      one_kronecker_one, Matrix.one_mul]
  calc ∑ a, (if a.2 ∈ E then (MatrixMap.conj C σ a a).re else 0)
      ≤ ∑ a, (MatrixMap.conj C σ a a).re := Finset.sum_le_sum fun a _ ↦ by
        split_ifs
        · exact le_rfl
        · exact (Complex.nonneg_iff.1 (hpsd.diag_nonneg (i := a))).1
    _ = (MatrixMap.conj C σ).trace.re := by rw [Matrix.trace, Complex.re_sum]; rfl
    _ = σ.trace.re := by rw [htr]

end dwTrace

/-! ## The persistence invariant in the decompressed basis -/

section dwInv

variable (L : HonestTable)

/-- The view's digest of the one-block trial on the block `b`. -/
def trialDg (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (b : X) : Digest :=
  trunc128 (trialRate t π b)

/-- The block of trial `n` of the search of the label `lab` from the table's base. -/
noncomputable def labBlk (lab : RLabel) (n : ℕ) : X :=
  cwBlk L.param lab (valueAt L (.inr lab)) n

/-- **A trial reads a programmable cell**: against the view `t`, a trial of some label's search
reads a cell of `tableHw L`. -/
def LabHit (t : SpongeKeys X Z) : Prop :=
  ∃ (lab : RLabel) (n : ℕ), n < randomizerAttemptLimit ∧
    ∃ rd ∈ spongeReads L.perm t.1 t.2.1 t.2.2 [labBlk L lab n], InHw (tableHw L) rd.point

/-- **The selections are the view's first codewords**: a recorded selection of a key is trial `j`
of the search of a label of the key, whose digest in the view is the recorded codeword, the
earlier trials' digests not codewords. -/
def SelCons (s : HwReg X Z Mem) : Prop :=
  ∀ l e sel, s.2.2.2 l e = some sel → ∃ lab : RLabel, lab.layer = l ∧ lab.key = e ∧
    ∃ j < randomizerAttemptLimit, sel.1 = labBlk L lab j ∧
      sel.2 = trialDg (regFns s) L.perm sel.1 ∧ Codeword.Valid sel.2 ∧
      ∀ i < j, ¬ Codeword.Valid (trialDg (regFns s) L.perm (labBlk L lab i))

/-- **The invariant between searches**: no decompressed `⊥`, hardwired cells in the table, and the
selections the view's first codewords unless a trial reads a programmable cell. -/
def DGlob (s : HwReg X Z Mem) : Prop :=
  NoBot s ∧ Quantum.Sponge.HwLe s.2.1 (tableHw L) ∧ (LabHit L (regFns s) ∨ SelCons L s)

/-- The invariant within the search of `lab` from `base` before trial `j`: the base is the
table's, the earlier trials' digests in the view are no codewords. -/
def DPre (lab : RLabel) (base : Randomizer) (j : ℕ) (s : HwReg X Z Mem) : Prop :=
  DGlob L s ∧ base = valueAt L (.inr lab) ∧
    ∀ i < j, ¬ Codeword.Valid (trialDg (regFns s) L.perm (cwBlk L.param lab base i))

/-- **The invariant of a search mode**: after the `k`-read the view holds its outcome, after the
`k'`-read the trial's rate and `h`-cell are the view's. -/
def DInv : CwMode → Set (HwReg X Z Mem)
  | .free => {s | DGlob L s}
  | .grd lab base j => {s | DPre L lab base j s}
  | .afK lab base j a => {s | DPre L lab base j s ∧ j < randomizerAttemptLimit ∧
      (regFns s).2.1 (cwBlk L.param lab base j) = a}
  | .afK' lab base j xi z => {s | DPre L lab base j s ∧ j < randomizerAttemptLimit ∧
      (trialMid (regFns s) L.perm (cwBlk L.param lab base j)).1 = xi ∧
      z = (trialMid (regFns s) L.perm (cwBlk L.param lab base j)).2 +
        (regFns s).2.2 (trialMid (regFns s) L.perm (cwBlk L.param lab base j)).1}

variable {L}

theorem dGlob_of_dInv {μ : CwMode} {s : HwReg X Z Mem} (h : s ∈ DInv L μ) : DGlob L s := by
  rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z⟩
  · exact h
  · exact h.1
  · exact h.1.1
  · exact h.1.1

theorem regFns_congr {s s' : HwReg X Z Mem} (h1 : s'.1 = s.1) (h2 : s'.2.1 = s.2.1) :
    regFns s' = regFns s := by
  unfold regFns
  rw [h1, h2]

/-- The databases, the hardwired cells and the selections determine the invariant. -/
theorem dGlob_congr {s s' : HwReg X Z Mem} (h1 : s'.1 = s.1) (h2 : s'.2.1 = s.2.1)
    (h3 : s'.2.2.2 = s.2.2.2) (h : DGlob L s) : DGlob L s' := by
  obtain ⟨hn, hw, hc⟩ := h
  have hr := regFns_congr h1 h2
  refine ⟨show NoBotDb s'.1 by rw [h1]; exact hn, by rw [h2]; exact hw, ?_⟩
  rw [hr]
  rcases hc with hc | hc
  · exact .inl hc
  · refine .inr fun l e sel hs ↦ ?_
    rw [h3] at hs
    rw [hr]
    exact hc l e sel hs

theorem hwView_k_of_noBot {s : HwReg X Z Mem} (hs : NoBot s) (x : X) :
    (hwView s.2.1 s.1).2.1 x = some ((regFns s).2.1 x) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (or_isSome (s.2.1.2.1 x) (hs.2.1 x))
  show (s.2.1.2.1 x).or (s.1.2.1 x) = some (((s.2.1.2.1 x).or (s.1.2.1 x)).getD 0)
  rw [ha]
  rfl

theorem hwView_k'_of_noBot {s : HwReg X Z Mem} (hs : NoBot s) (x : X) :
    (hwView s.2.1 s.1).2.2 x = some ((regFns s).2.2 x) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (or_isSome (s.2.1.2.2 x) (hs.2.2 x))
  show (s.2.1.2.2 x).or (s.1.2.2 x) = some (((s.2.1.2.2 x).or (s.1.2.2 x)).getD 0)
  rw [ha]
  rfl

/-- **A trial reading no programmable cell reads alike** in views agreeing off the table. -/
theorem trialDg_eq_of_offAgree {t t' : SpongeKeys X Z} (h : OffAgree (tableHw L) t t') {b : X}
    (hn : ∀ rd ∈ spongeReads L.perm t.1 t.2.1 t.2.2 [b], ¬InHw (tableHw L) rd.point) :
    trialDg t' L.perm b = trialDg t L.perm b := by
  have e := (spongeReads_congr L.perm [b] fun e he ↦
    answeredBy_of_offAgree h (spongeReads_answeredBy L.perm t _ e he) (hn e he)).2
  have e' : (absorb (spongePerm t' L.perm) [b]).1 = (absorb (spongePerm t L.perm) [b]).1 := by
    rw [e]
  exact congrArg trunc128 e'

theorem labHit_of_offAgree {t t' : SpongeKeys X Z} (h : OffAgree (tableHw L) t t')
    (ht' : LabHit L t') : LabHit L t := by
  obtain ⟨lab, n, hn, rd, hrd, hin⟩ := ht'
  by_contra hs
  have hav : ∀ rd ∈ spongeReads L.perm t.1 t.2.1 t.2.2 [labBlk L lab n],
      ¬InHw (tableHw L) rd.point := fun rd hrd hin ↦ hs ⟨lab, n, hn, rd, hrd, hin⟩
  rw [(spongeReads_congr L.perm [labBlk L lab n] fun e he ↦ answeredBy_of_offAgree h
    (spongeReads_answeredBy L.perm t _ e he) (hav e he)).1] at hrd
  exact hav rd hrd hin

/-- **The selections stay the view's first codewords** when the view moves only at programmable
cells that no trial reads. -/
theorem selCons_of_offAgree {s s' : HwReg X Z Mem} (h : OffAgree (tableHw L) (regFns s) (regFns s'))
    (hn : ¬LabHit L (regFns s)) (hm : s'.2.2.2 = s.2.2.2) (hs : SelCons L s) : SelCons L s' := by
  have hd : ∀ (lab : RLabel) (n : ℕ), n < randomizerAttemptLimit →
      trialDg (regFns s') L.perm (labBlk L lab n) = trialDg (regFns s) L.perm (labBlk L lab n) :=
    fun lab n hlt ↦ trialDg_eq_of_offAgree h fun rd hrd hin ↦ hn ⟨lab, n, hlt, rd, hrd, hin⟩
  intro l e sel hsel
  rw [hm] at hsel
  obtain ⟨lab, hl, he, j, hj, h1, h2, h3, h4⟩ := hs l e sel hsel
  refine ⟨lab, hl, he, j, hj, h1, ?_, h3, fun i hi ↦ ?_⟩
  · rw [h1, hd lab j hj, ← h1]
    exact h2
  · rw [hd lab i (hi.trans hj)]
    exact h4 i hi

/- Instance search for the run families over the register `PReg` exceeds the default size
(as in PrefixRun). -/
set_option synthInstance.maxSize 2000

/-! ### The ports keep the invariant -/

theorem dInv_sponge (μ : CwMode) (p : SpongePort)
    (r : (recHwSpec X Z HPos Selections).Result (.inl (.inl (.inl p))))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inl p))) × PReg)
      ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inl p))) × PReg) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In (.inl (.inl (.inl p))) ×
      PReg ↦ m.2) (DInv L μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out (.inl (.inl (.inl p))) ×
      PReg ↦ m.2) (DInv L .free)
      (((decR (X := X) (Z := Z) m0R).step (.inl (.inl (.inl p)))).branch r σ) :=
  (decR_sponge_supp m0R p r _ σ hσ).mono fun _ hs ↦ dGlob_of_dInv hs

theorem dInv_rec (μ : CwMode) (T : Finset HPos)
    (mem : (recHwSpec X Z HPos Selections).Result (.inr T))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In (.inr T) × PReg)
      ((recHwSpec X Z HPos Selections).In (.inr T) × PReg) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In (.inr T) × PReg ↦ m.2)
      (DInv L μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out (.inr T) × PReg ↦ m.2)
      (DInv L (cwRevNx T fun lab ↦ valueAt L (.inr lab)))
      (((decR (X := X) (Z := Z) m0R).step (.inr T)).branch mem σ) := by
  refine (decR_rec_supp m0R T mem _ σ hσ).mono ?_
  rintro s' ⟨s, hs, -, rfl⟩
  have hg : DGlob L (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) :=
    dGlob_congr (s := s) rfl rfl rfl (dGlob_of_dInv hs)
  unfold cwRevNx cwOptNx
  cases cwRevLab T with
  | none => exact hg
  | some lab => exact ⟨hg, rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩

theorem dInv_prog (μ : CwMode) (c : HwProg X Z) (hc : ProgOf (tableHw L) c)
    (r : (recHwSpec X Z HPos Selections).Result (.inl (.inr c)))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In (.inl (.inr c)) × PReg)
      ((recHwSpec X Z HPos Selections).In (.inl (.inr c)) × PReg) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In (.inl (.inr c)) × PReg ↦
      m.2) (DInv L μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out (.inl (.inr c)) × PReg ↦ m.2)
      (DInv L .free) (((decR (X := X) (Z := Z) m0R).step (.inl (.inr c))).branch r σ) := by
  refine (decR_prog_supp m0R c r _ σ hσ).mono ?_
  rintro s' ⟨s, hs, hrel⟩
  obtain ⟨hn, hw, hsel⟩ := dGlob_of_dInv hs
  have hin : InHw (tableHw L) (progPt c) := by
    cases c with
    | programH z a => exact fun h ↦ Option.some_ne_none a ((show (tableHw L).1 z = some a from
        hc).symm.trans h)
    | programK x a => exact fun h ↦ Option.some_ne_none a ((show (tableHw L).2.1 x = some a from
        hc).symm.trans h)
    | programK' x a => exact fun h ↦ Option.some_ne_none a ((show (tableHw L).2.2 x = some a from
        hc).symm.trans h)
  have hoff := hrel.offAgree hin
  have hW : s'.2.1 = progUpdate c s.2.1 := congrArg Prod.fst hrel.1
  have hm : s'.2.2.2 = s.2.2.2 := by rw [hrel.1]
  refine ⟨hrel.2.1 hn, by rw [hW]; exact hwLe_progUpdate hw hc, ?_⟩
  by_cases hh : LabHit L (regFns s)
  · exact .inl (labHit_of_offAgree hoff.symm hh)
  · rcases hsel with hsel | hsel
    · exact absurd hsel hh
    · exact .inr (selCons_of_offAgree hoff hh hm hsel)

theorem dInv_readK {lab : RLabel} {base : Randomizer} {j : ℕ} (hj : j < randomizerAttemptLimit)
    (r : (recHwSpec X Z HPos Selections).Result
      (.inl (.inl (.inr (liftRead (.readK (cwBlk L.param lab base j) keepMem))))))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In
      (.inl (.inl (.inr (liftRead (.readK (cwBlk L.param lab base j) keepMem))))) × PReg)
      ((recHwSpec X Z HPos Selections).In
        (.inl (.inl (.inr (liftRead (.readK (cwBlk L.param lab base j) keepMem))))) × PReg) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In
      (.inl (.inl (.inr (liftRead (.readK (cwBlk L.param lab base j) keepMem))))) × PReg ↦ m.2)
      (DInv L (.grd lab base j)) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out
      (.inl (.inl (.inr (liftRead (.readK (cwBlk L.param lab base j) keepMem))))) × PReg ↦ m.2)
      (DInv L (.afK lab base j (r.1.getD 0)))
      (((decR (X := X) (Z := Z) m0R).step
        (.inl (.inl (.inr (liftRead (.readK (cwBlk L.param lab base j) keepMem)))))).branch r σ) := by
  refine (decR_readU_supp m0R (.readK (cwBlk L.param lab base j) keepMem) r _ σ hσ).mono ?_
  rintro s' ⟨s, hs, rfl, rfl⟩
  refine ⟨⟨dGlob_congr (s := s) rfl rfl rfl hs.1, hs.2.1, hs.2.2⟩, hj, ?_⟩
  show (regFns s).2.1 (cwBlk L.param lab base j) =
    ((hwView s.2.1 s.1).2.1 (cwBlk L.param lab base j)).getD 0
  rw [hwView_k_of_noBot hs.1.1]
  rfl

theorem dInv_readK' {lab : RLabel} {base : Randomizer} {j : ℕ} {a : Z}
    (r : (recHwSpec X Z HPos Selections).Result
      (.inl (.inl (.inr (liftRead (.readK' (L.perm (cwBlk L.param lab base j, a)).1 keepMem))))))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In
      (.inl (.inl (.inr (liftRead (.readK' (L.perm (cwBlk L.param lab base j, a)).1 keepMem))))) ×
        PReg)
      ((recHwSpec X Z HPos Selections).In
        (.inl (.inl (.inr (liftRead (.readK' (L.perm (cwBlk L.param lab base j, a)).1
          keepMem))))) × PReg) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In
      (.inl (.inl (.inr (liftRead (.readK' (L.perm (cwBlk L.param lab base j, a)).1
        keepMem))))) × PReg ↦ m.2) (DInv L (.afK lab base j a)) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out
      (.inl (.inl (.inr (liftRead (.readK' (L.perm (cwBlk L.param lab base j, a)).1
        keepMem))))) × PReg ↦ m.2)
      (DInv L (.afK' lab base j (L.perm (cwBlk L.param lab base j, a)).1
        ((L.perm (cwBlk L.param lab base j, a)).2 + r.1.getD 0)))
      (((decR (X := X) (Z := Z) m0R).step
        (.inl (.inl (.inr (liftRead (.readK' (L.perm (cwBlk L.param lab base j, a)).1
          keepMem)))))).branch r σ) := by
  refine (decR_readU_supp m0R (.readK' (L.perm (cwBlk L.param lab base j, a)).1 keepMem) r _ σ
    hσ).mono ?_
  rintro s' ⟨s, hs, rfl, rfl⟩
  obtain ⟨hpre, hj, ha⟩ := hs
  have hmid : trialMid (regFns s) L.perm (cwBlk L.param lab base j) =
      L.perm (cwBlk L.param lab base j, a) := by
    rw [trialMid, zero_add, zero_add, ha]
  refine ⟨⟨dGlob_congr (s := s) rfl rfl rfl hpre.1, hpre.2.1, hpre.2.2⟩, hj, ?_, ?_⟩
  · show (trialMid (regFns s) L.perm (cwBlk L.param lab base j)).1 = _
    rw [hmid]
  · show _ = (trialMid (regFns s) L.perm (cwBlk L.param lab base j)).2 +
      (regFns s).2.2 (trialMid (regFns s) L.perm (cwBlk L.param lab base j)).1
    rw [hmid]
    show _ + ((hwView s.2.1 s.1).2.2 (L.perm (cwBlk L.param lab base j, a)).1).getD 0 = _
    rw [hwView_k'_of_noBot hpre.1.1]
    rfl

/-- **The trial's `h`-read keeps the invariant**: it reads the view's cell, so a selection it
records is the view's digest of the trial, a codeword after non-codewords; the search stops at a
codeword and goes on to the next trial otherwise. -/
theorem dInv_readH {lab : RLabel} {base : Randomizer} {j : ℕ} {xi : X} {z : Z}
    (r : (recHwSpec X Z HPos Selections).Result (.inl (.inl (.inr (liftRead
      (.readH z (cwUpd lab.layer lab.key (cwBlk L.param lab base j) xi)))))))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inr (liftRead
      (.readH z (cwUpd lab.layer lab.key (cwBlk L.param lab base j) xi)))))) × PReg)
      ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inr (liftRead
        (.readH z (cwUpd lab.layer lab.key (cwBlk L.param lab base j) xi)))))) × PReg) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In (.inl (.inl (.inr (liftRead
      (.readH z (cwUpd lab.layer lab.key (cwBlk L.param lab base j) xi)))))) × PReg ↦ m.2)
      (DInv L (.afK' lab base j xi z)) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out (.inl (.inl (.inr (liftRead
      (.readH z (cwUpd lab.layer lab.key (cwBlk L.param lab base j) xi)))))) × PReg ↦ m.2)
      (DInv L (dwOut lab base j (out256 (xi + r.1.getD 0))))
      (((decR (X := X) (Z := Z) m0R).step (.inl (.inl (.inr (liftRead
        (.readH z (cwUpd lab.layer lab.key (cwBlk L.param lab base j) xi))))))).branch r σ) := by
  refine (decR_readU_supp m0R (.readH z (cwUpd lab.layer lab.key (cwBlk L.param lab base j) xi)) r
    _ σ hσ).mono ?_
  rintro s' ⟨s, hs, rfl, rfl⟩
  obtain ⟨⟨⟨hn, hw, hsel⟩, hb, hlow⟩, hj, hxi, hz⟩ := hs
  subst hb
  have hr : ((hwView s.2.1 s.1).1 z).getD 0 = (regFns s).1 z := by
    rw [hwView_h_of_noBot hn]
    rfl
  have hdg : trialDg (regFns s) L.perm (cwBlk L.param lab (valueAt L (.inr lab)) j) =
      trunc128 (xi + (regFns s).1 z) := by
    unfold trialDg trialRate
    rw [← hz, hxi]
  show readFin s _ ∈ DInv L (dwOut lab _ j (out256 (xi + ((hwView s.2.1 s.1).1 z).getD 0)))
  rw [hr]
  have hreg : regFns (readFin s (.readH z (cwUpd lab.layer lab.key (labBlk L lab j) xi))) =
      regFns s := rfl
  have hglob : DGlob L (readFin s (.readH z (cwUpd lab.layer lab.key (labBlk L lab j) xi))) := by
    refine ⟨hn, hw, ?_⟩
    rw [hreg]
    rcases hsel with hsel | hsel
    · exact .inl hsel
    refine .inr fun l e sel hm ↦ ?_
    rw [hreg]
    change cwUpd lab.layer lab.key (labBlk L lab j) xi s.2.2.2 ((hwView s.2.1 s.1).1 z) l e =
      some sel at hm
    rw [hwView_h_of_noBot hn] at hm
    by_cases h0 : s.2.2.2 lab.layer lab.key = none
    · rw [cwUpd_some_of_none _ _ _ _ h0] at hm
      unfold cwSel at hm
      split_ifs at hm with hv
      · rw [select_apply] at hm
        split_ifs at hm with hle
        · obtain ⟨rfl, rfl⟩ := hle
          obtain rfl := (Option.some_inj.mp hm).symm
          exact ⟨lab, rfl, rfl, j, hj, rfl, hdg.symm, hv, hlow⟩
        · exact hsel l e sel hm
      · exact hsel l e sel hm
    · have hm' : cwUpd lab.layer lab.key (labBlk L lab j) xi s.2.2.2 (some ((regFns s).1 z)) =
          s.2.2.2 := by
        show (if s.2.2.2 lab.layer lab.key = none then _ else s.2.2.2) = s.2.2.2
        exact ite_eq_right h0
      rw [hm'] at hm
      exact hsel l e sel hm
  unfold dwOut
  split_ifs with hv
  · exact hglob
  · refine ⟨hglob, rfl, fun i hi ↦ ?_⟩
    change ¬Codeword.Valid (trialDg (regFns s) L.perm (cwBlk L.param lab (valueAt L (.inr lab)) i))
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hlow i hi
    · rw [hdg]
      exact hv

/-- **Every allowed call of a program in the table keeps the invariant of its mode.** -/
theorem dInv_step (μ : CwMode) (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × PReg)
      ((recHwSpec X Z HPos Selections).In i × PReg) ℂ)
    (hok : cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i)
    (hin : PortIn Selections (tableHw L) i)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2)
      (DInv L μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i × PReg ↦ m.2)
      (DInv L (dwNxZ L.perm L.param (valueAt L) μ i r))
      (((decR (X := X) (Z := Z) m0R).step i).branch r σ) := by
  rcases i with ((p | c) | c) | T
  · exact dInv_sponge μ p r σ hσ
  · rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z⟩ <;>
      rcases c with ⟨z', u⟩ | ⟨x, u⟩ | ⟨y, u⟩
    all_goals try exact False.elim hok
    · obtain ⟨hj, rfl, rfl⟩ := hok
      exact dInv_readK hj r σ hσ
    · obtain ⟨rfl, rfl⟩ := hok
      exact dInv_readK' r σ hσ
    · obtain ⟨rfl, rfl⟩ := hok
      exact dInv_readH r σ hσ
  · exact dInv_prog μ c hin r σ hσ
  · exact dInv_rec μ T r σ hσ

/-! ### A re-grind trial's hit -/

theorem blocks_cwBlk (P : PublicParameter) (lab : RLabel) (b : Randomizer) (j : ℕ) :
    blocks (thInput P (hashDomainFields (.message lab.layer lab.key))
      (lab.msg ++ littleEndianBytes 16 (b + BitVec.ofNat digestBits j))) = [cwBlk P lab b j] := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp (length_blocks_trial P
    (hashDomainFields (.message lab.layer lab.key)) (RLabel.length_msg_le lab) b j)
  rw [hc]
  simp [cwBlk, hc]

/-- Equal trial blocks have the same message. -/
theorem cwBlk_msg_eq {P : PublicParameter} {lab lab' : RLabel} {b b' : Randomizer} {i i' : ℕ}
    (h : cwBlk P lab b i = cwBlk P lab' b' i') : lab.msg = lab'.msg := by
  have hb : blocks (thInput P (hashDomainFields (.message lab.layer lab.key))
      (lab.msg ++ littleEndianBytes 16 (b + BitVec.ofNat digestBits i))) =
      blocks (thInput P (hashDomainFields (.message lab'.layer lab'.key))
        (lab'.msg ++ littleEndianBytes 16 (b' + BitVec.ofNat digestBits i'))) := by
    rw [blocks_cwBlk, blocks_cwBlk, h]
  obtain ⟨-, hpay⟩ := thInput_injective P (blocks_injective hb)
  exact (List.append_inj' hpay (by simp only [littleEndianBytes, List.length_ofFn])).1

/-- A label is its layer, key and message. -/
theorem rlabel_eq_of {lab lab' : RLabel} (hl : lab'.layer = lab.layer) (hk : lab'.key = lab.key)
    (hm : lab'.msg = lab.msg) : lab' = lab := by
  rcases lab with ⟨e, m⟩ | ⟨e, d⟩ <;> rcases lab' with ⟨e', m'⟩ | ⟨e', d'⟩
  · obtain rfl : e' = e := hk
    obtain rfl : m' = m := littleEndianBytes_injective 32 hm
    rfl
  · exact absurd hl.symm bottomLayer_ne_topLayer
  · exact absurd hl bottomLayer_ne_topLayer
  · obtain rfl : e' = e := hk
    obtain rfl : d' = d := littleEndianBytes_injective 16 hm
    rfl

/-- **Two blocks of the same randomizer search are blocks of one label** (of a given key). -/
theorem rlabel_eq_of_sameGrind {P : PublicParameter} {lab lab' : RLabel} {b b' : Randomizer}
    {i i' : ℕ} (hl : lab'.layer = lab.layer) (hk : lab'.key = lab.key)
    (h : SameGrind P (cwBlk P lab b i) (cwBlk P lab' b' i')) : lab' = lab := by
  obtain ⟨lab0, base0, i0, j0, h1, h2⟩ := h
  exact rlabel_eq_of hl hk ((cwBlk_msg_eq h2).trans (cwBlk_msg_eq h1).symm)

/-- A trial block names its key's message slot. -/
theorem slotOf_cwBlk (P : PublicParameter) (lab : RLabel) (b : Randomizer) (j : ℕ) :
    slotOf P [cwBlk P lab b j] = some (.msg lab.layer lab.key) := by
  have hb := blocks_cwBlk P lab b j
  have hlen : (thInput P (hashDomainFields (.message lab.layer lab.key))
      (lab.msg ++ littleEndianBytes 16 (b + BitVec.ofNat digestBits j))).length < 136 := by
    have h1 := length_blocks (thInput P (hashDomainFields (.message lab.layer lab.key))
      (lab.msg ++ littleEndianBytes 16 (b + BitVec.ofNat digestBits j)))
    rw [hb, List.length_singleton] at h1
    omega
  rw [← hb, ← absorbTail_blocks_of_lt (Equiv.refl (X × Z)) hlen]
  exact slotOf_msg (Equiv.refl (X × Z)) P lab.layer lab.key lab.msg (RLabel.length_msg_ge lab) _

/-- **The target of a trial's tail** is the selected digest of its key, unless the trial's block
is the selected one. -/
theorem xmssTgtHw_cwBlk {W : Hw X Z} {m : Selections} {lab : RLabel} {b : Randomizer} {i : ℕ}
    {y : Digest} (h : xmssTgtHw L W m [cwBlk L.param lab b i] = some y) :
    ∃ sel, m lab.layer lab.key = some sel ∧ cwBlk L.param lab b i ≠ sel.1 ∧ y = sel.2 := by
  unfold xmssTgtHw xmssTgt at h
  rw [slotOf_cwBlk L.param lab b i, Option.bind_some] at h
  change (m.toMemory lab.layer lab.key).bind _ = some y at h
  rcases hm : m lab.layer lab.key with _ | sel
  · rw [Selections.toMemory_eq_none hm] at h
    exact absurd h (by simp)
  · have hmem : m.toMemory lab.layer lab.key = some (blockInput sel.1, sel.2) := by
      simp [Selections.toMemory, hm]
    rw [hmem, Option.bind_some] at h
    dsimp only at h
    split_ifs at h with hc
    refine ⟨sel, rfl, fun he ↦ hc ?_, (Option.some_inj.mp h).symm⟩
    show [cwBlk L.param lab b i] = blocks (blockInput sel.1)
    rw [← he, blocks_blockInput (blocks_cwBlk L.param lab b i)]

/-- The trial event on the databases alone. -/
def LabHitD (L : HonestTable) (D : DbReg X Z) : Prop :=
  LabHit L D.toDbs.fill

/-- On a register whose hardwired cells lie in the table, the trial event is the databases'. -/
theorem labHitD_of_labHit {s : HwReg X Z Mem} (hle : Quantum.Sponge.HwLe s.2.1 (tableHw L))
    (h : LabHit L (regFns s)) : LabHitD L s.1 := by
  refine labHit_of_offAgree ⟨fun z hz ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩ h
  · have hW : s.2.1.1 z = none := by
      rcases hw : s.2.1.1 z with _ | a
      · rfl
      · rw [hle.1 z a hw] at hz
        cases hz
    show (s.1.1 z).getD 0 = ((s.2.1.1 z).or (s.1.1 z)).getD 0
    rw [hW]
    rfl
  · have hW : s.2.1.2.1 x = none := by
      rcases hw : s.2.1.2.1 x with _ | a
      · rfl
      · rw [hle.2.1 x a hw] at hx
        cases hx
    show (s.1.2.1 x).getD 0 = ((s.2.1.2.1 x).or (s.1.2.1 x)).getD 0
    rw [hW]
    rfl
  · have hW : s.2.1.2.2 x = none := by
      rcases hw : s.2.1.2.2 x with _ | a
      · rfl
      · rw [hle.2.2 x a hw] at hx
        cases hx
    show (s.1.2.2 x).getD 0 = ((s.2.1.2.2 x).or (s.1.2.2 x)).getD 0
    rw [hW]
    rfl

/-- **The trial event is determined off the table.** -/
theorem offHw_labHitD : OffHw (tableHw L) (LabHitD L) := fun D D' h1 h2 h3 ↦ by
  have hO : OffAgree (tableHw L) D.toDbs.fill D'.toDbs.fill :=
    ⟨fun z hz ↦ congrArg (fun o ↦ Option.getD o 0) (h1 z hz),
      fun x hx ↦ congrArg (fun o ↦ Option.getD o 0) (h2 x hx),
      fun x hx ↦ congrArg (fun o ↦ Option.getD o 0) (h3 x hx)⟩
  exact ⟨labHit_of_offAgree hO.symm, labHit_of_offAgree hO⟩

/-- **No re-grind trial hits its key's selected digest**, unless a trial reads a programmable
cell: at trial `j` of `lab` the view's digests of the earlier trials are no codewords and the
trial's digest is the view's; the selection of the key, by the same label (`RegrindSel`), is the
view's first codeword at a trial `j'`. The hit makes the trial's digest that codeword: `j < j'`
contradicts the selection's earlier non-codewords, `j' < j` the search's, `j = j'` makes the
trial the selected input, whose tail has no target. -/
theorem labHit_of_hitG {lab : RLabel} {base : Randomizer} {j : ℕ} {xi : X} {z : Z} {t : TrialPt}
    (hl : t.l = lab.layer) (he : t.e = lab.key) (hx : t.x = cwBlk L.param lab base j)
    (hxi : trunc128 t.xi = trunc128 xi) {s : HwReg X Z Mem}
    (hs : s ∈ DInv L (.afK' lab base j xi z)) (h : hitG L z t s.2 (s.1.1 z)) :
    LabHit L (regFns s) := by
  obtain ⟨⟨⟨-, -, hsel⟩, hb, hlow⟩, -, hmid, hz⟩ := hs
  subst hb
  rcases hsel with hh | hsel
  · exact hh
  exfalso
  obtain ⟨hW, ⟨sel, hm, hsame⟩, v, hv, htgt⟩ := h
  rw [hl, he] at hm
  obtain ⟨lab', hl', he', j', -, h1, h2, h3, h4⟩ := hsel _ _ sel hm
  rw [hx, h1] at hsame
  obtain rfl := (rlabel_eq_of_sameGrind hl' he' hsame).symm
  rw [hx] at htgt
  obtain ⟨sel', hm', hne, hy⟩ := xmssTgtHw_cwBlk htgt
  rw [hm] at hm'
  obtain rfl := Option.some_inj.mp hm'
  have hvz : (regFns s).1 z = v := by
    show ((s.2.1.1 z).or (s.1.1 z)).getD 0 = v
    rw [hW, hv]
    rfl
  have hdg : trialDg (regFns s) L.perm (cwBlk L.param lab (valueAt L (.inr lab)) j) = sel.2 := by
    unfold trialDg trialRate
    rw [← hz, hmid, hvz, ← hy]
    exact (trunc128_add_congr hxi v).symm
  have hv3 : Codeword.Valid
      (trialDg (regFns s) L.perm (cwBlk L.param lab (valueAt L (.inr lab)) j)) := by
    rw [hdg]
    exact h3
  rcases lt_trichotomy j j' with hlt | rfl | hgt
  · exact h4 j hlt hv3
  · exact hne h1.symm
  · have h5 := h2 ▸ h3
    rw [h1] at h5
    exact hlow j' hgt h5

/-! ### The invariant along the challenge prefix -/

theorem dInv_init :
    QuerySupportedOn (fun m : QReg.of Unit × PReg ↦ m.2) (DInv L .free)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ compressReg X Z Mem)
        initR) := by
  refine (init_dec m0R).mono ?_
  rintro s ⟨hn, hs⟩
  have hW : s.2.1 = hwEmpty X Z := congrArg Prod.fst hs
  have hm : s.2.2.2 = m0 := congrArg (fun p ↦ p.2.2) hs
  refine ⟨hn, ?_, .inr fun l e sel h ↦ ?_⟩
  · rw [hW]
    exact ⟨fun z v h ↦ (by cases h), fun x v h ↦ (by cases h), fun x v h ↦ (by cases h)⟩
  · rw [hm] at h
    cases h

/-- The calls of the prefix in the decompressed basis program cells of the table. -/
theorem forallQueries_portIn_dec (A : Adversary (X × Z)) :
    (decR (X := X) (Z := Z) m0R).ForallQueries .instruments
      (fun i _ _ ↦ PortIn Selections (tableHw L) i) (prefixR A L)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ compressReg X Z Mem)
        initR) := by
  have hC : compressReg X Z Mem * compressReg X Z Mem = 1 := compressReg_mul_self
  have h := ForallQueries.of_simulation .instruments (R₁ := runtimeRH (X := X) (Z := Z) m0R)
    (R₂ := decR m0R) (V := MatrixMap.conj (compressReg X Z Mem)) (fun i r ↦ by
      simp only [MatrixMap.amplifyLeft_conj]
      rw [conjReg_branch (runtimeRH m0R) (compressReg X Z Mem) compressReg_mul_self
          conjTranspose_compressReg, LinearMap.comp_assoc, LinearMap.comp_assoc,
        conj_one_kronecker_comp_self (runtimeRH m0R) _ hC, LinearMap.comp_id])
    (P₂ := fun i _ _ ↦ PortIn Selections (tableHw L) i) (fun _ _ _ h ↦ h.1)
    (forallQueries_hwSupp_prefixR A L)
  rwa [MatrixMap.amplifyLeft_conj] at h

/-- **The invariant at the calls of the prefix, in the decompressed basis.** -/
theorem forallQueries_dInv_dec (A : Adversary (X × Z)) :
    (decR (X := X) (Z := Z) m0R).ForallQueries .instruments (fun i E σ ↦ ∃ μ,
      cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i ∧
        QuerySupportedOn (fun m : ((recHwSpec X Z HPos Selections).In i × PReg) × E ↦ m.1.2)
          (DInv L μ) σ) (prefixR A L)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ compressReg X Z Mem)
        initR) :=
  forallQueries_of_modedP_guard (decR m0R) .instruments (DInv L) (PortIn Selections (tableHw L))
    (fun μ i r σ hok hin hσ ↦ dInv_step μ i r σ hok hin hσ) (prefixR A L) .free
    (dwModedP_prefixR cwUpd (pubOf L) A (valueAt L)) (forallQueries_portIn_dec A) dInv_init

/-- **The invariant at the calls of the prefix**: every call is presented an operator whose
decompressed form is supported on the invariant of a mode allowing it. -/
theorem forallQueries_dInv (A : Adversary (X × Z)) :
    (runtimeR m0R).ForallQueries .instruments (fun i E τ ↦ ∃ μ,
      cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i ∧
        QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2) (DInv L μ)
          (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
            ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem)
            (MatrixMap.traceRight _ E τ))) (prefixR A L) initR := by
  have hC : compressReg X Z Mem * compressReg X Z Mem = 1 := compressReg_mul_self
  have hstep : ∀ i r, ((runtimeRH (X := X) (Z := Z) m0R).step i).branch r ∘ₗ
      (MatrixMap.conj (compressReg X Z Mem)).amplifyLeft ((recHwSpec X Z HPos Selections).In i) =
      (MatrixMap.conj (compressReg X Z Mem)).amplifyLeft ((recHwSpec X Z HPos Selections).Out i) ∘ₗ
        ((decR m0R).step i).branch r := fun i r ↦ by
    rw [conjReg_branch (runtimeRH m0R) (compressReg X Z Mem) compressReg_mul_self
      conjTranspose_compressReg i r]
    simp only [MatrixMap.amplifyLeft_conj]
    rw [← LinearMap.comp_assoc, conj_one_kronecker_comp_self (runtimeRH m0R) _ hC,
      LinearMap.id_comp]
  have h2 := ForallQueries.of_simulation .instruments (R₁ := decR m0R)
    (R₂ := runtimeRH (X := X) (Z := Z) m0R) (V := MatrixMap.conj (compressReg X Z Mem)) hstep
    (P₂ := fun i E τ ↦ ∃ μ, cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2) (DInv L μ)
        (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
          ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem)
          (MatrixMap.traceRight _ E τ)))
    (fun i E τ ⟨μ, hok, hτ⟩ ↦ ⟨μ, hok, by
      rw [MatrixMap.amplifyLeft_conj,
        ← LinearMap.comp_apply (MatrixMap.conj _) (MatrixMap.traceRight _ E),
        ← MatrixMap.traceRight_comp_amplify, LinearMap.comp_apply,
        ← LinearMap.comp_apply (MatrixMap.amplify _ E) (MatrixMap.amplify _ E),
        ← MatrixMap.amplify_comp, conj_one_kronecker_comp_self (runtimeRH m0R) _ hC,
        MatrixMap.amplify_id, LinearMap.id_apply]
      exact querySupportedOn_traceRight
        (q := fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2) hτ⟩)
    (forallQueries_dInv_dec A)
  have hρ' : (MatrixMap.conj (compressReg X Z Mem)).amplifyLeft (QReg.of Unit)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ compressReg X Z Mem)
        initR) = initR := by
    rw [MatrixMap.amplifyLeft_conj,
      ← LinearMap.comp_apply (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z Mem)), conj_one_kronecker_comp_self (runtimeRH m0R) _ hC,
      LinearMap.id_apply]
  rw [hρ'] at h2
  exact h2

open scoped Classical in
/-- **The projector on the trial event** in the decompressed basis. -/
noncomputable def labQ (L : HonestTable) : Matrix (HwReg X Z Mem) (HwReg X Z Mem) ℂ :=
  hwDecProj {s : HwReg X Z Mem | LabHitD L s.1}

/-- **A call's decompressed re-grind hit weight is at most its trial-event weight**
(`labHit_of_hitG`). -/
theorem decHitAW_le_potential {μ : CwMode} {c : HwRead X Z Mem}
    (hok : cwRdOk L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ c)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hs : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) (DInv L μ)
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z Mem) σ)) :
    decHitAW L c σ ≤ potential (labQ L) σ := by
  rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z⟩ <;>
    rcases c with ⟨z', u⟩ | ⟨x, u⟩ | ⟨y, u⟩
  all_goals try exact False.elim hok
  · unfold decHitAW
    rw [ite_eq_right fun ⟨_, h⟩ ↦ by cases h]
    exact zero_le
  · unfold decHitAW
    rw [ite_eq_right fun ⟨_, h⟩ ↦ by cases h]
    exact zero_le
  · obtain ⟨hzz, rfl⟩ := hok
    subst z'
    have htr : IsTrial trialUpd
        (.readH z (cwLiftHu (cwHu1 cwUpd) lab (cwBlk L.param lab base j) xi) : HwRead X Z Mem) :=
      ⟨(z, ⟨lab.layer, lab.key, cwBlk L.param lab base j, xi⟩), rfl⟩
    have hc := eq_readH_trialOf trialUpd htr
    obtain ⟨hz', hu'⟩ := HwRead.readH.inj hc
    obtain ⟨hl, he, hx, hxi⟩ := trialUpd_inj (t := ⟨lab.layer, lab.key, cwBlk L.param lab base j, xi⟩)
      (t' := (trialOf trialUpd
        (.readH z (cwLiftHu (cwHu1 cwUpd) lab (cwBlk L.param lab base j) xi) : HwRead X Z Mem)).2)
      (by rw [← hu']; rfl)
    unfold decHitAW labQ
    rw [ite_eq_left htr, potential_eq, conjTranspose_hwDecProj, hwDecProj_mul_self]
    refine ENNReal.ofReal_le_ofReal (re_trace_hwDecProj_le _ _ (DInv L (.afK' lab base j xi z))
      hσ hs fun s hsI hsE ↦ ?_)
    have hsE' : hitG L z (trialOf trialUpd
        (.readH z (cwLiftHu (cwHu1 cwUpd) lab (cwBlk L.param lab base j) xi) : HwRead X Z Mem)).2
        s.2 (s.1.1 z) := by
      have h := hsE
      rw [← hz'] at h
      exact h
    exact labHitD_of_labHit (dGlob_of_dInv hsI).2.1 (labHit_of_hitG hl he hx hxi hsI hsE')

/-- **The ports in the table do not raise the trial event's weight** (DecUniform: the event is
determined off the table). -/
theorem tsum_potential_labQ_le (i : (recHwSpec X Z HPos Selections).Port)
    (hin : PortIn Selections (tableHw L) i)
    {σ : Matrix ((recHwSpec X Z HPos Selections).In i × PReg)
      ((recHwSpec X Z HPos Selections).In i × PReg) ℂ} (hσ : σ.PosSemidef) :
    ∑' r, potential (labQ L) (((runtimeR m0R).step i).branch r σ) ≤ potential (labQ L) σ := by
  let _ : DecidablePred (LabHitD L) := fun _ ↦ Classical.propDecidable _
  refine tsum_potential_branch_le (runtimeR m0R) i _ (fun r ↦ ?_) hσ
  have hE : ∀ s : HwReg X Z Mem, s ∈ {s : HwReg X Z Mem | LabHitD L s.1} ↔ LabHitD L s.1 :=
    fun _ ↦ Iff.rfl
  unfold labQ
  rcases i with ((p | c) | c) | T
  · cases p <;> exact branch_comm_of_commute
      (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m0R _ r) (hwPort_commute_hwDecProj _ _)
  · exact branch_comm_of_commute (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r)
      (hwReadKraus_commute_hwDecProj _ (LabHitD L) hE c r)
  · have hci : c.CellIn (tableHw L) := by
      cases c with
      | programH z a => exact fun h ↦ Option.some_ne_none a ((show (tableHw L).1 z = some a from
          hin).symm.trans h)
      | programK x a => exact fun h ↦ Option.some_ne_none a ((show (tableHw L).2.1 x = some a from
          hin).symm.trans h)
      | programK' x a => exact fun h ↦ Option.some_ne_none a ((show (tableHw L).2.2 x = some a
          from hin).symm.trans h)
    exact branch_comm_of_commute (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m0R c r)
      (hwProgKraus_commute_hwDecProj _ offHw_labHitD hE hci r)
  · let _ : DecidablePred fun b : Hw X Z × Mem ↦ b.2 = r := fun b ↦ winMemDecEq b.2 r
    exact branch_comm_of_commute (recStep_branch T r)
      (clsKraus_one_commute_hwDecProj _ (LabHitD L) hE (fun b : Hw X Z × Mem ↦ b.2 = r) _)

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The decompressed re-grind hit weight along the prefix** is at most `clsCap` times the
initial weight of the trial event. -/
theorem decHitAPre_le_labQ : decHitAPre A L ≤ clsCap * potential (labQ L) initR := by
  have hG : (runtimeR m0R).ForallQueries .instruments
      (fun i _ _ ↦ PortIn Selections (tableHw L) i) (prefixR A L) initR :=
    QuantumRuntime.ForallQueries.mono .instruments (fun _ _ _ h ↦ h.1)
      (forallQueries_hwSupp_prefixR A L)
  calc decHitAPre A L ≤ (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ σ ↦ potential (labQ L) σ) fun _ _ ↦ 0)) (prefixR A L) initR :=
        totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
          (fun i σ ↦ ∃ μ, cwOkZ L.perm L.param (cwLiftHu (cwHu1 cwUpd)) μ i ∧
            QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × PReg ↦ m.2)
              (DInv L μ) (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
                ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem) σ))
          (fun _ _ _ h ↦ h)
          (fun i σ hσ hI ↦ by
            rcases i with ((p | c) | c) | T
            · exact zero_le
            · obtain ⟨μ, hok, hs⟩ := hI
              exact decHitAW_le_potential hok hσ hs
            · exact zero_le
            · exact zero_le) (prefixR A L) initR_posSemidef (forallQueries_dInv A)
    _ ≤ clsCap * potential (labQ L) initR :=
        totalWeight_le_charge_potential (runtimeR m0R) .instruments (labQ L) _
          (PortIn Selections (tableHw L)) _ (fun i σ _ _ ↦ by
            rcases i with ((p | c) | c) | T
            · exact zero_le
            · show potential (labQ L) σ ≤ ((if extCls X Z Mem (recSpec HPos Selections)
                (.inl (.inl (.inr c))) then 1 else 0 : ℕ) : ℝ≥0∞) * potential (labQ L) σ
              simp [extCls, hwCls]
            · exact zero_le
            · exact zero_le)
          (fun i hi σ hσ ↦ tsum_potential_labQ_le i hi hσ) (prefixR A L)
          (clsCalls_prefixR hperm hsign L) initR_posSemidef hG

end dwInv

/-! ## The trial event, counted -/

section dwCount

/-- **No trial block of any label is a `k`-cell of the table** (TrialsOff's `TrialsOff` for the
trial blocks of both layers). -/
def TrialsOffAll (L : HonestTable) : Prop :=
  ∀ (lab : RLabel) (n : ℕ), n < randomizerAttemptLimit → (tableHw L).2.1 (labBlk L lab n) = none

/-- The trial blocks of all labels. -/
noncomputable def labBlocks (L : HonestTable) : Finset X :=
  Finset.univ.image fun q : RLabel × Fin randomizerAttemptLimit ↦ labBlk L q.1 q.2

theorem card_sum_prod_prod {A B C N : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype N]
    {a b c n : ℕ} (ha : Fintype.card A = a) (hb : Fintype.card B = b) (hc : Fintype.card C = c)
    (hn : Fintype.card N = n) : Fintype.card ((A × B ⊕ A × C) × N) = (a * b + a * c) * n := by
  rw [Fintype.card_prod, Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, ha, hb, hc, hn]

theorem card_message : Fintype.card Message = 2 ^ 256 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

theorem card_digest' : Fintype.card Digest = 2 ^ 128 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  norm_num [digestBits]

set_option exponentiation.threshold 4096 in
/-- **At most `2^321` trial blocks** of all labels. -/
theorem card_labBlocks_le (L : HonestTable) : (labBlocks L).card ≤ 2 ^ 321 := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, card_sum_prod_prod card_keyIndex card_message card_digest'
    (Fintype.card_fin randomizerAttemptLimit)]
  unfold randomizerAttemptLimit
  norm_num

variable {L : HonestTable}

/-- **A trial event of the tables is a hit of a `k'` or `h` cell at a trial block**
(`TrialsOffAll`: no trial block is a `k` cell of the table). -/
theorem badBlk_of_labHit (hoff : TrialsOffAll L) {t : SpongeKeys X Z} (h : LabHit L t) :
    ∃ x ∈ labBlocks L, BadBlk L.perm (k'Cells L) (hCells L) x t := by
  obtain ⟨lab, n, hn, rd, hrd, hin⟩ := h
  refine ⟨labBlk L lab n, ?_, ?_⟩
  · simp only [labBlocks, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨(lab, ⟨n, hn⟩), rfl⟩
  · rcases point_of_mem_spongeReads_single L.perm t.1 t.2.1 t.2.2 _ hrd with hp | hp | hp <;>
      rw [hp] at hin
    · exact absurd (hoff lab n hn) hin
    · exact Or.inl (mem_k'Cells hin)
    · exact Or.inr (mem_hCells hin)

/-- **The initial weight of the trial event**: at most
`|labBlocks| (18 |k'Cells| + |hCells|) / |Z|` (DecUniform's uniform initial databases). -/
theorem potential_labQ_initR_le (hoff : TrialsOffAll L) (hπ : PermGood L.perm 18) :
    potential (labQ L) initR ≤ (((labBlocks L).card * (18 * (k'Cells L).card +
      (hCells L).card) : ℕ) : ℝ≥0∞) / Fintype.card Z := by
  classical
  have h1 : potential (labQ L) initR = ENNReal.ofReal
      (((Finset.univ.filter fun t ↦ LabHitD L (ofFunDbs t)).card : ℝ) /
        Fintype.card ((Z → X) × (X → Z) × (X → Z))) := by
    unfold potential labQ
    rw [MatrixMap.amplifyLeft_conj]
    change ENNReal.ofReal (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
      hwDecProj _) ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty,
        Database.empty, Database.empty), hwEmpty X Z, m0R) : HwReg X Z Mem)).matrix)).trace.re = _
    simp only [SubState.matrix_basis]
    rw [trace_conj_hwDecProj_basis {s : HwReg X Z Mem | LabHitD L s.1} (LabHitD L)
      (fun _ ↦ Iff.rfl) (hwEmpty X Z, m0R),
      Matrix.trace_single_eq_same, Complex.one_re, one_mul]
  rw [h1, ← natCast_div_eq_ofReal _ _ Fintype.card_pos]
  exact natCast_div_le_div_of_mul_le Fintype.card_pos Fintype.card_pos
    (card_mul_card_filter_le_of_blocks hπ (k'Cells L) (hCells L) (labBlocks L)
      (fun t ↦ LabHitD L (ofFunDbs t)) fun _ ht ↦ badBlk_of_labHit hoff ht)

set_option exponentiation.threshold 4096 in
/-- The count at Keccak's sizes, times the classical calls: `2^67 · 2^370 / 2^512`. -/
theorem decHitTerm_le {b k h : ℕ} (hb : b ≤ 2 ^ 321) (hk : k ≤ 8 * (498 * 2 ^ 32))
    (hh : h ≤ 8 * (498 * 2 ^ 32)) :
    (clsCap : ℝ≥0∞) * (((b * (18 * k + h) : ℕ) : ℝ≥0∞) / Fintype.card Z) ≤
      ENNReal.ofReal (1 / 2 ^ 75) := by
  have hK : b * (18 * k + h) ≤ 2 ^ 370 :=
    calc b * (18 * k + h) ≤ 2 ^ 321 * (18 * (8 * (498 * 2 ^ 32)) + 8 * (498 * 2 ^ 32)) := by
          gcongr
      _ ≤ 2 ^ 370 := by norm_num
  have hc : (clsCap : ℝ) ≤ 2 ^ 67 := by
    rw [clsCap, verifyBlocks_eq, signBlocks_eq, progCap_eq]
    norm_num [lifetime, layerCount, layerHeight]
  rw [rnCard_Z, natCast_div_eq_ofReal _ (2 ^ 512) (by positivity), ← ENNReal.ofReal_natCast clsCap,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc (clsCap : ℝ) * (((b * (18 * k + h) : ℕ) : ℝ) / ((2 ^ 512 : ℕ) : ℝ))
      ≤ 2 ^ 67 * (2 ^ 370 / 2 ^ 512) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact mul_le_mul hc (div_le_div_of_nonneg_right (by exact_mod_cast hK) (by positivity))
          (by positivity) (by positivity)
    _ = 1 / 2 ^ 75 := by norm_num

theorem clsCap_le_real : (clsCap : ℝ) ≤ 2 ^ 67 := by
  rw [clsCap, verifyBlocks_eq, signBlocks_eq, progCap_eq]
  norm_num [lifetime, layerCount, layerHeight]

set_option exponentiation.threshold 4096 in
/-- The bound on the good tables: `2^-75 + clsCap · 2^-173 ≤ 2^-74`. -/
theorem decHitTau_le :
    ENNReal.ofReal (1 / 2 ^ 75) + (clsCap : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 173) ≤
      ENNReal.ofReal (1 / 2 ^ 74) := by
  rw [← ENNReal.ofReal_natCast clsCap, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc 1 / 2 ^ 75 + (clsCap : ℝ) * (1 / 2 ^ 173) ≤ 1 / 2 ^ 75 + 2 ^ 67 * (1 / 2 ^ 173) := by
        gcongr
        exact clsCap_le_real
    _ ≤ 1 / 2 ^ 74 := by norm_num

/-- A trial's block is a trial block. -/
theorem trialBlock_labBlk (L : HonestTable) (lab : RLabel) (n : ℕ) :
    TrialBlock L.param (labBlk L lab n) :=
  ⟨lab.layer, lab.key, lab.msg, _, RLabel.length_msg_le lab, blocks_cwBlk _ _ _ _⟩

open scoped Classical in
/-- **On ReparamR0's good set, `TrialHidGood` gives `TrialsOffAll`**: the table's `k` cells are
the template's hidden `k`-cells (`r0E_hpath`), which `TrialHidGood` keeps off the trial blocks. -/
theorem trialsOffAll_of_r0G {t : HonestTable × RE} (ht : r0G treeQ 18 t)
    (hg : TrialHidGood (pubR (r0E t).1) (r0E t).2.1) : TrialsOffAll t.1 := by
  intro lab n _
  by_contra hne
  have hk : labBlk t.1 lab n ∈ pathK t.1 := by
    by_contra hk
    apply hne
    unfold tableHw
    dsimp only
    exact ite_eq_right hk
  have hT : TrialBlock (pubR (r0E t).1).param (labBlk t.1 lab n) := by
    have h := trialBlock_labBlk t.1 lab n
    rw [← parR_r0E ht] at h
    exact h
  exact hg.2 _ hT ((r0E_hpath hashesSlots_treeQ ht).2.1 hk)

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The honest tables violating `TrialsOffAll`** at Keccak's sizes: at most `2^-173` (the tables
outside `r0G treeQ 18`, `2^-174`, and the good ones violating `TrialHidGood`, `2^-400`). -/
theorem trialsOffAll_frac_le_keccak :
    (Fintype.card HonestTable : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun L : HonestTable ↦ ¬TrialsOffAll L).card ≤
      ENNReal.ofReal (1 / 2 ^ 173) := by
  have hE := inv_card_mul_card_filter_comp_fst (Equiv.refl (HonestTable × RE))
    fun L ↦ ¬TrialsOffAll L
  have hsub := card_filter_le_add_of_imp (fun t : HonestTable × RE ↦ ¬TrialsOffAll t.1)
    (fun t ↦ ¬r0G treeQ 18 t)
    (fun t ↦ r0G treeQ 18 t ∧ ¬TrialHidGood (pubR (r0E t).1) (r0E t).2.1) fun t ht ↦ by
      by_cases hg : r0G treeQ 18 t
      · exact Or.inr ⟨hg, fun h ↦ ht (trialsOffAll_of_r0G hg h)⟩
      · exact Or.inl hg
  rw [mul_comm, ← div_eq_mul_inv, ← hE]
  calc (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t : HonestTable × RE ↦ ¬TrialsOffAll t.1).card
      ≤ (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun t ↦ ¬r0G treeQ 18 t).card : ℝ≥0∞) +
            (Finset.univ.filter fun t ↦ r0G treeQ 18 t ∧
              ¬TrialHidGood (pubR (r0E t).1) (r0E t).2.1).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun t ↦ ¬r0G treeQ 18 t).card +
        (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun t ↦ r0G treeQ 18 t ∧
            ¬TrialHidGood (pubR (r0E t).1) (r0E t).2.1).card := mul_add _ _ _
    _ ≤ ENNReal.ofReal (1 / 2 ^ 174) + ENNReal.ofReal (1 / 2 ^ 400) :=
        add_le_add r0G_frac_le_keccak trialHidGood_r0G_frac_le_keccak
    _ ≤ _ := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- A trial read's decompressed re-grind hit weight is at most its trace. -/
theorem decHitAW_le_trace (L : HonestTable) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    decHitAW L c σ ≤ ENNReal.ofReal σ.trace.re := by
  unfold decHitAW
  split_ifs
  · exact ENNReal.ofReal_le_ofReal (re_trace_hwDecProj_le_trace _ hσ)
  · exact zero_le

end dwCount

/-! ## The averaged bound -/

section dwAvg

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The decompressed re-grind hit weight of a table** at Keccak's sizes: at most `2^-75` on a
table with `TrialsOffAll` and `PermGood 18`. -/
theorem decHitAPre_le_keccak {L : HonestTable} (hoff : TrialsOffAll L)
    (hπ : PermGood L.perm 18) : decHitAPre A L ≤ ENNReal.ofReal (1 / 2 ^ 75) :=
  (decHitAPre_le_labQ hperm hsign).trans ((mul_le_mul_of_nonneg_left
    (potential_labQ_initR_le hoff hπ) zero_le).trans
      (decHitTerm_le (card_labBlocks_le L) (card_k'Cells_le L) (card_hCells_le L)))

/-- **`DecHitAvg`**: `τA = 2^-75` on every good set of tables with `TrialsOffAll` and
`PermGood 18`. -/
theorem decHitAvg (good : HonestTable → Prop) [DecidablePred good]
    (hg : ∀ L, good L → TrialsOffAll L ∧ PermGood L.perm 18) :
    DecHitAvg A good (ENNReal.ofReal (1 / 2 ^ 75)) := by
  unfold DecHitAvg
  refine (uavg_mono fun L ↦ ?_).trans (uavg_const_le _)
  by_cases hL : good L
  · rw [ite_eq_left hL]
    exact decHitAPre_le_keccak hperm hsign (hg L hL).1 (hg L hL).2
  · rw [ite_eq_right hL]
    exact zero_le

/-- The decompressed re-grind hit weight of any table is at most `clsCap`. -/
theorem decHitAPre_le_clsCap (L : HonestTable) : decHitAPre A L ≤ clsCap :=
  (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
      fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (fun i σ hσ ↦ by
        rcases i with ((p | c) | c) | T
        · exact zero_le
        · exact decHitAW_le_trace L c hσ
        · exact zero_le
        · exact zero_le) (prefixR A L) initR_posSemidef).trans
    (totalWeight_calls_le (prefixR A L) (clsCalls_prefixR hperm hsign L))

open scoped Classical in
/-- **`DecHitAvg` on Security's good tables**: `τA = 2^-74` (`2^-75` on the tables with
`TrialsOffAll`, `clsCap` on the `2^-173` others). -/
theorem decHitAvg_goodL : DecHitAvg A GoodL (ENNReal.ofReal (1 / 2 ^ 74)) := by
  unfold DecHitAvg
  calc uavg (fun L ↦ if GoodL L then decHitAPre A L else 0)
      ≤ uavg (fun L ↦ ENNReal.ofReal (1 / 2 ^ 75) +
          (clsCap : ℝ≥0∞) * (if TrialsOffAll L then (0 : ℝ≥0∞) else 1)) :=
        uavg_mono fun L ↦ by
          by_cases hL : GoodL L
          · rw [ite_eq_left hL]
            by_cases ho : TrialsOffAll L
            · rw [ite_eq_left ho, mul_zero, add_zero]
              exact decHitAPre_le_keccak hperm hsign ho hL.1.1
            · rw [ite_eq_right ho, mul_one]
              exact (decHitAPre_le_clsCap hperm hsign L).trans le_add_self
          · rw [ite_eq_right hL]
            exact zero_le
    _ = uavg (fun _ : HonestTable ↦ ENNReal.ofReal (1 / 2 ^ 75)) +
          (clsCap : ℝ≥0∞) * uavg (fun L ↦ if TrialsOffAll L then (0 : ℝ≥0∞) else 1) := by
        rw [uavg_add, uavg_const_mul]
    _ ≤ ENNReal.ofReal (1 / 2 ^ 75) + (clsCap : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 173) := by
        refine add_le_add (uavg_const_le _) (mul_le_mul_of_nonneg_left ?_ zero_le)
        rw [uavg_ite_zero_one]
        exact trialsOffAll_frac_le_keccak
    _ ≤ _ := decHitTau_le

end dwAvg

end Quantum.Xmss.Assembly

end
