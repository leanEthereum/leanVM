module

public import Quantum.Sphincs.Assembly.RecBadMass
public import Quantum.Sphincs.Assembly.TrialHitUniform
public import Quantum.Xmss.Assembly.RecOffDecHit

@[expose] public section

/-!
# The off-path and re-grind parts of leanSPHINCS's `RecBad` mass

RecBadMass reduces `RecBadAvg` to `DecHitAvg` (the decompressed re-grind hits) and `RecOffAvg` (the
cells off the trial's path). Both are proved here, mirroring leanXMSS's
`Quantum.Xmss.Assembly.RecOffDecHit`. leanSPHINCS re-grinds a key on every request reaching it
(the deterministic signer re-runs on a repeated message; the top and middle keys sign for many
messages), always on the one value the key signs (KeyMsg).

* **Trial blocks** (`tBlk`, `tBlk_inj`): the block of trial `j` of key `K` on the value `m`; it
  determines `K`, `m` and `j` (counters below `2^32`).
* **The search modes** (`GrMode`, `gRdOk`, `gRdNx`, `GrReady`, `gModed_grindK`, `gIdle_signT`,
  `gModed_prefixR`): idle remembering the values of the last reveal; between trials after a
  trial's block; after a trial's `k`-read with its outcome; after its `k'`-read with both
  outcomes. The mode after a trial's `h`-read depends on its digest (`grOut`): idle after a
  codeword (the search stops), the next trial otherwise. The challenge prefix is moded so, from
  the idle mode.
* **Off the trial's path** (`grPot`, `grLeakW`, `recOffW_le_miss`, `recOff_step`, `recOffPre_le`,
  `recOffAvg`): after the `k`-read the union misses its outcome, after the `k'`-read one of the
  two; a trial's `h`-read is `RecOff` only there (`trialUpd_xi`: `trialOf` names the trial up to
  its rate's untruncated bits), and a read leaves a miss with weight at most `2/|Z|` (EncRefined's
  leak bounds). Hence `RecOffAvg (2/|Z| · clsCap)`, at most `2^-443` (`recOffTau_le`).
* **The persistence invariant** (`DInv`, `dInv_step`, `forallQueries_dInv`): in the decompressed
  basis a read returns the view's cell and keeps the databases, and a program at a programmable
  cell moves the view only there. Every call of the prefix is presented a decompressed operator
  supported on: no `⊥`, hardwired cells programmable, and either a trial of a key on its value
  reads a programmable cell (PrefixFacts' `TrialHit`) or every selection is the view's first
  codeword of its key's search (`SelCons`); within a search before trial `j`, the view's digests
  of the earlier trials are no codewords; after the trial's `k`-, `k'`-reads the view holds their
  outcomes.
* **No re-grind hit** (`trialHit_of_hitG`, `decHitAW_le_potential`): on the invariant a re-grind
  trial's hit of its key's selected digest is `TrialHit`: `j < j'` contradicts the selection's
  earlier non-codewords, `j' < j` the search's, `j = j'` makes the trial the selected input.
* **The trial event, counted** (`trialQ`, `tsum_potential_trialQ_le`, `decHitAPre_le_trialQ`,
  `potential_trialQ_initR_le`): the trial event of the databases (TrialHit's `HitView`) is
  determined off the programmable cells, so its decompressed weight does not grow along the prefix
  (DecUniform) and starts at its fraction of the tables, at most `2^-189` on data with `TrialsOff`
  and `PermGood 18` (TrialHit's count). `decHitAPre ≤ clsCap · 2^-189 ≤ 2^-121`
  (`decHitAPre_le_keccak`); `decHitAvg`, and `decHitAvg_of_frac` where `TrialsOff` fails for a
  fraction `ε` (`τA = 2^-121 + clsCap · ε`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest Message)
open Quantum.Xmss (X Z blocks trunc128 blocks_injective)
open Quantum.Xmss.Hybrid (LazyProg restrictTo setProj diagMass uavg uavg_mono uavg_add
  uavg_const_mul uavg_ite_zero_one totalWeight_const_mul_weight totalWeight_le_totalWeight
  progUpdate)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT tmplLens readLift readLens
  readLiftQ revealThen progThen RevealVals hashTrial rdRoundU rdHU liftRead ModedP modedP_bind
  modedP₂_bind modedP_map modeCmdNx KMiss K'Miss readK_leak_le readK'_leak_le readK'_keep_kMiss
  totalWeight_le_modedP trunc128_add_congr dW_nonneg potential_zero potential_setProj
  totalWeight_le_of_forallQueries extWeight uavg_const_le rnCard_Z regFns NoBot trialRate
  trialMid hwView_h_of_noBot or_isSome readFin decR runtimeRH decR_sponge_supp decR_rec_supp
  decR_prog_supp decR_readU_supp ProgRel init_dec conjReg_branch conj_one_kronecker_comp_self
  querySupportedOn_traceRight forallQueries_of_modedP_guard totalWeight_le_charge_potential
  tsum_potential_branch_le re_trace_hwDecProj_le re_trace_hwDecProj_le_trace extCls
  card_mul_card_filter_le_of_blocks natCast_div_le_div_of_mul_le NoBotDb recStep_branch
  natCast_div_eq_ofReal)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default
size. -/
set_option synthInstance.maxSize 2000

/-! ## Trial blocks at a counter -/

section blocks

variable (pub : Pub)

/-- The block of key `K`'s trial at the counter `j` on the value `m`. -/
def tBlk (K : Key) (m : Digest) (j : ℕ) : X :=
  encBlk pub K m (BitVec.ofNat counterBits j)

theorem blocks_trialInput (K : Key) (m : Digest) (j : ℕ) :
    blocks (trialInput pub K m j) = [tBlk pub K m j] :=
  blocks_encIn pub K m _

variable {pub}

/-- **A trial block determines its key, value and counter** (counters below `2^32`). -/
theorem tBlk_inj {K K' : Key} {m m' : Digest} {j j' : ℕ} (hj : j < encodingAttemptLimit)
    (hj' : j' < encodingAttemptLimit) (h : tBlk pub K m j = tBlk pub K' m' j') :
    K = K' ∧ m = m' ∧ j = j' := by
  have hb : blocks (encIn pub K m (BitVec.ofNat counterBits j)) =
      blocks (encIn pub K' m' (BitVec.ofNat counterBits j')) := by
    rw [blocks_encIn pub K m, blocks_encIn pub K' m']
    exact congrArg (fun x ↦ [x]) h
  have he := blocks_injective hb
  unfold encIn at he
  obtain ⟨ha, hp⟩ := addressedHashInput_injective _ he
  have hd := hashDomainFields_injOn (d := .encoding K.1 K.2.1 K.2.2)
    (d' := .encoding K'.1 K'.2.1 K'.2.2) trivial trivial ha
  injection hd with h1 h2 h3
  obtain ⟨hm, hc⟩ := List.append_inj' hp (by simp [bigEndianBytes])
  have hc' := bigEndianBytes_injective 4 hc
  have hjj : j = j' := by
    have h1 : j < 2 ^ counterBits := hj
    have h2 : j' < 2 ^ counterBits := hj'
    have := congrArg BitVec.toNat hc'
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
    exact this
  exact ⟨Prod.ext h1 (Prod.ext h2 h3), littleEndianBytes_injective 16 hm, hjj⟩

end blocks

/-! ## The search modes -/

section modes

/-- **The modes of the counter searches**: idle, remembering the values of the last reveal at the
value positions; between trials, after the trial on the block `x`; after a trial's `k`-read at the
block `x` with outcome `a`; after its `k'`-read, with outcome `c`. -/
inductive GrMode
  | free (τ : KMode)
  | grd (x : X)
  | afK (x : X) (a : Z)
  | afK' (x : X) (a c : Z)

/-- A mode between trials. -/
def GrMode.Idle : GrMode → Prop
  | .free _ => True
  | .grd _ => True
  | _ => False

/-- The idle mode remembering no value. -/
def GrMode.none : GrMode :=
  .free fun _ ↦ Option.none

/-- **The mode after a trial with digest `d`** on the block `x`: idle after a codeword (the search
stops), between trials otherwise. -/
noncomputable def grOut (x : X) (d : Digest) : GrMode :=
  @ite _ (Codeword.Valid d) (Classical.propDecidable _) GrMode.none (.grd x)

theorem grOut_idle (x : X) (d : Digest) : (grOut x d).Idle := by
  unfold grOut
  split_ifs
  · exact trivial
  · exact trivial

theorem grOut_of_not_valid {x : X} {d : Digest} (h : ¬Codeword.Valid d) : grOut x d = .grd x := by
  unfold grOut
  split_ifs
  rfl

variable (pub : Pub)

/-- **The reads a mode allows**: idle with the remembered value `m` at `msgPos K` of a key
`K = K_l(idx)`, the `k`-read of `K`'s first trial on `m`; between trials after trial `j` of `K` on
`m`, the `k`-read of trial `j + 1`; after the `k`-read at `x` with outcome `a`, the `k'`-read at
`π (x, a)`; after the `k'`-read with outcome `c`, the `h`-read at `π (x, a) + c` with the update of
the block's key. -/
def gRdOk : GrMode → HwRead X Z (Mem HPos) → Prop
  | .free τ, c => ∃ l idx m, τ (msgPos (keyOf l idx)) = some m ∧
      c = readKPort (tBlk pub (keyOf l idx) m 0)
  | .grd x, c => ∃ l idx m j, j + 1 < encodingAttemptLimit ∧ x = tBlk pub (keyOf l idx) m j ∧
      c = readKPort (tBlk pub (keyOf l idx) m (j + 1))
  | .afK x a, c => c = readK'Port (pub.perm (x, a)).1
  | .afK' x a c', c => ∃ K m j, j < encodingAttemptLimit ∧ x = tBlk pub K m j ∧
      c = .readH ((pub.perm (x, a)).2 + c') (trialUpd ⟨K, x, (pub.perm (x, a)).1⟩)

/-- **The mode after a read.** -/
noncomputable def gRdNx {M' : Type} : GrMode → (c : HwRead X Z M') → c.Result → GrMode
  | .free _, .readK x _, r => .afK x (r.1.getD 0)
  | .grd _, .readK x _, r => .afK x (r.1.getD 0)
  | .afK x a, .readK' _ _, r => .afK' x a (r.1.getD 0)
  | .afK' x a _, .readH _ _, r => grOut x (trunc128 ((pub.perm (x, a)).1 + r.1.getD 0))
  | _, _, _ => GrMode.none

/-- The calls the modes allow, on runtime 1's ports. -/
def gOkR : GrMode → (hwReadSpec X Z Selections).Port → Prop
  | μ, .inl _ => μ.Idle
  | μ, .inr c => gRdOk pub μ (liftRead (S := HPos) c)

/-- The mode after a call of runtime 1. -/
noncomputable def gNxR :
    GrMode → (i : (hwReadSpec X Z Selections).Port) → (hwReadSpec X Z Selections).Result i →
      GrMode
  | _, .inl _, _ => GrMode.none
  | μ, .inr c, r => gRdNx pub μ c r

/-- The calls the modes allow, on the template's ports. -/
def gOkT : GrMode → (SSpec Selections).Port → Prop
  | μ, .inl (.inl (.inr c)) => gRdOk pub μ c.1
  | μ, _ => μ.Idle

/-- The mode after a call of the template: a reveal remembers its values. -/
noncomputable def gNxT : GrMode → (i : (SSpec Selections).Port) → (SSpec Selections).Result i →
    GrMode
  | μ, .inl (.inl (.inr c)), r => gRdNx pub μ c.1 r
  | _, .inr _, r => .free (kOpt r.1)
  | _, _, _ => GrMode.none

/-- The calls the modes allow, on runtime 2's ports with record ports. -/
def gOkZ : GrMode → (recHwSpec X Z HPos Selections).Port → Prop
  | μ, .inl (.inl (.inr c)) => gRdOk pub μ c
  | μ, _ => μ.Idle

/-- The mode after a call of runtime 2 with record ports, at the hidden values `v`. -/
noncomputable def gNxZ (v : (s : HPos) → XD s) :
    GrMode → (i : (recHwSpec X Z HPos Selections).Port) →
      (recHwSpec X Z HPos Selections).Result i → GrMode
  | μ, .inl (.inl (.inr c)), r => gRdNx pub μ c r
  | _, .inr T, _ => .free (kOpt (restrictTo T v))
  | _, _, _ => GrMode.none

/-- **A mode ready for trial `j` of key `K` on the value `m`**: idle remembering `m` at `msgPos K`
for the first trial, between trials after trial `j - 1` otherwise. -/
def GrReady (K : Key) (m : Digest) : ℕ → GrMode → Prop
  | 0, μ => ∃ τ, μ = .free τ ∧ τ (msgPos K) = some m
  | j + 1, μ => μ = .grd (tBlk pub K m j)

variable {pub}

theorem GrReady.idle {K : Key} {m : Digest} {j : ℕ} {μ : GrMode} (h : GrReady pub K m j μ) :
    μ.Idle := by
  cases j with
  | zero =>
    obtain ⟨τ, rfl, -⟩ := h
    exact trivial
  | succ j =>
    change μ = _ at h
    subst h
    exact trivial

theorem GrReady.ok {l : Layer} {idx : Index} {m : Digest} {j : ℕ} {μ : GrMode}
    (h : GrReady pub (keyOf l idx) m j μ) (hj : j < encodingAttemptLimit) :
    gRdOk pub μ (readKPort (tBlk pub (keyOf l idx) m j)) := by
  cases j with
  | zero =>
    obtain ⟨τ, rfl, hτ⟩ := h
    exact ⟨l, idx, m, hτ, rfl⟩
  | succ j =>
    change μ = _ at h
    subst h
    exact ⟨l, idx, m, j, hj, rfl, rfl⟩

end modes

/-! ## Runtime 1's searches are moded -/

section grind

variable (pub : Pub)

theorem gModed_readCall {μ : GrMode} {c : HwRead X Z Selections}
    (h : gRdOk pub μ (liftRead (S := HPos) c)) (B : QReg) :
    ModedP (L := LocalSig.instruments) (gOkR pub) (gNxR pub)
      (fun p μ' ↦ μ' = gRdNx pub μ c p.2.2) μ (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

/-- A stateful program of runtime 1 moded from every state. -/
def GSMod {B : QReg} {σ α : Type} (μ : GrMode) (F : α → GrMode → Prop)
    (x : StateT σ (QComp (hwReadSpec X Z Selections) B B) α) : Prop :=
  ∀ s, ModedP (L := LocalSig.instruments) (gOkR pub) (gNxR pub) (fun p μ' ↦ F p.2.2.1 μ') μ
    (x.run s)

variable {pub} {B : QReg} {σ α β : Type}

theorem gSMod_bind {x : StateT σ (QComp (hwReadSpec X Z Selections) B B) α}
    {k : α → StateT σ (QComp (hwReadSpec X Z Selections) B B) β} {μ : GrMode}
    {F : α → GrMode → Prop} {G : β → GrMode → Prop} (hx : GSMod pub μ F x)
    (hk : ∀ a μ', F a μ' → GSMod pub μ' G (k a)) : GSMod pub μ G (x >>= k) := by
  intro s
  rw [StateT.run_bind]
  exact modedP₂_bind (F := fun (q : α × σ) μ ↦ F q.1 μ) (F' := fun (q : β × σ) μ ↦ G q.1 μ) _ _
    (hx s) fun p μ' h ↦ hk p.1 μ' h p.2

theorem gSMod_pure (a : α) {F : α → GrMode → Prop} {μ : GrMode} (h : F a μ) :
    GSMod pub μ F (pure a : StateT σ (QComp (hwReadSpec X Z Selections) B B) α) := by
  intro s
  rw [StateT.run_pure]
  exact h

theorem gSMod_map {x : StateT σ (QComp (hwReadSpec X Z Selections) B B) α} (g : α → β)
    {μ : GrMode} {F : β → GrMode → Prop} (hx : GSMod pub μ (fun a ↦ F (g a)) x) :
    GSMod pub μ F (g <$> x) := by
  intro s
  rw [StateT.run_map]
  exact modedP_map (F := fun q : β × σ ↦ F q.1) (fun p : α × σ ↦ (g p.1, p.2)) (hx s)

theorem gSMod_rdK {μ : GrMode} (hμ : μ.Idle) {x : X} (h : gRdOk pub μ (readKPort x)) :
    GSMod pub μ (fun a (μ' : GrMode) ↦ μ' = .afK x a) (rdK (M := Selections) B x) :=
  fun s ↦ modedP₂_bind
    (F := fun r : Option Z × Selections ↦ fun (μ' : GrMode) ↦ μ' = .afK x (r.1.getD 0))
    (F' := fun q : Z × List (SpongeRead X Z) ↦ fun (μ' : GrMode) ↦ μ' = .afK x q.1)
    (readCall (.readK x keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k x (r.1.getD 0)]))
    (by
      refine ⟨h, fun r ↦ ⟨trivial, fun _ ↦ ?_⟩⟩
      cases μ with
      | free τ => rfl
      | grd x₀ => rfl
      | afK _ _ => exact hμ.elim
      | afK' _ _ _ => exact hμ.elim)
    fun _ _ h ↦ h

theorem gSMod_rdK' {x : X} {a : Z} {y : X} (hy : y = (pub.perm (x, a)).1) :
    GSMod pub (.afK x a) (fun c (μ' : GrMode) ↦ μ' = .afK' x a c)
      (rdK' (M := Selections) B y) :=
  fun s ↦ modedP₂_bind
    (F := fun r : Option Z × Selections ↦ fun (μ' : GrMode) ↦ μ' = .afK' x a (r.1.getD 0))
    (F' := fun q : Z × List (SpongeRead X Z) ↦ fun (μ' : GrMode) ↦ μ' = .afK' x a q.1)
    (readCall (.readK' y keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k' y (r.1.getD 0)]))
    ⟨by rw [hy]; rfl, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩
    fun _ _ h ↦ h

theorem gSMod_rdHU {x : X} {a c : Z} {z : Z} {K : Key} {m : Digest} {j : ℕ}
    (hj : j < encodingAttemptLimit) (hx : x = tBlk pub K m j) (hz : z = (pub.perm (x, a)).2 + c) :
    GSMod pub (.afK' x a c)
      (fun w (μ' : GrMode) ↦ μ' = grOut x (trunc128 ((pub.perm (x, a)).1 + w)))
      (rdHU Selections B z (cwUpd K x (pub.perm (x, a)).1)) :=
  fun s ↦ modedP₂_bind (F := fun r : Option X × Selections ↦ fun (μ' : GrMode) ↦
      μ' = grOut x (trunc128 ((pub.perm (x, a)).1 + r.1.getD 0)))
    (F' := fun q : X × List (SpongeRead X Z) ↦ fun (μ' : GrMode) ↦
      μ' = grOut x (trunc128 ((pub.perm (x, a)).1 + q.1)))
    (readCall (.readH z (cwUpd K x (pub.perm (x, a)).1)) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.h z (r.1.getD 0)]))
    ⟨⟨K, m, j, hj, hx, by rw [hz]; rfl⟩, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩
    fun _ _ h ↦ h

/-- **A trial's round of reads** from a mode allowing its `k`-read. -/
theorem gSMod_rdRoundU {μ : GrMode} (hμ : μ.Idle) {K : Key} {m : Digest} {j : ℕ} {b : X}
    (hj : j < encodingAttemptLimit) (hb : b = tBlk pub K m j) (hok : gRdOk pub μ (readKPort b)) :
    GSMod pub μ (fun q (μ' : GrMode) ↦ μ' = grOut b (trunc128 q.1))
      (rdRoundU Selections (cwUpd K) pub.perm B (0, 0) b) := by
  have e : ((0, 0) : X × Z).1 + b = b := zero_add b
  unfold rdRoundU
  refine gSMod_bind (gSMod_rdK hμ (x := ((0, 0) : X × Z).1 + b) (by rw [e]; exact hok))
    fun a μ ha ↦ ?_
  subst ha
  refine gSMod_bind (gSMod_rdK' (x := ((0, 0) : X × Z).1 + b) (a := a)
    (by rw [show ((0, 0) : X × Z).2 + a = a from zero_add a])) fun c μ hc ↦ ?_
  subst hc
  have hu : cwUpd K b (pub.perm (((0, 0) : X × Z).1 + b, ((0, 0) : X × Z).2 + a)).1 =
      cwUpd K (((0, 0) : X × Z).1 + b) (pub.perm (((0, 0) : X × Z).1 + b, a)).1 := by
    rw [e, show ((0, 0) : X × Z).2 + a = a from zero_add a]
  rw [hu]
  refine gSMod_bind (gSMod_rdHU (K := K) (m := m) (j := j) hj (by rw [e]; exact hb)
    (by rw [show ((0, 0) : X × Z).2 + a = a from zero_add a])) fun w μ hw ↦ ?_
  refine gSMod_pure _ ?_
  rw [hw, e, show ((0, 0) : X × Z).2 + a = a from zero_add a]

/-- **A trial's hash** of a one-block input whose block is the trial's. -/
theorem gModed_hashTrial {μ : GrMode} (hμ : μ.Idle) {K : Key} {m : Digest} {j : ℕ}
    (hj : j < encodingAttemptLimit) {input : HashSig.HashInput} {b : X} (hb : b = tBlk pub K m j)
    (hin : blocks input = [b])
    (hok : gRdOk pub μ (readKPort b)) :
    ModedP (L := LocalSig.instruments) (gOkR pub) (gNxR pub)
      (fun p (μ' : GrMode) ↦ μ' = grOut b (HashSig.truncateHash p.2.2)) μ
      (hashTrial Selections (cwUpd K) pub.perm B input) := by
  have hfold : GSMod pub (B := B) μ (fun q (μ' : GrMode) ↦ μ' = grOut b (trunc128 q.1))
      ((blocks input).foldlM (rdRoundU Selections (cwUpd K) pub.perm B) (0, 0)) := by
    rw [hin]
    exact gSMod_bind (gSMod_rdRoundU hμ hj hb hok) fun s' μ h ↦ gSMod_pure s' h
  exact modedP_map (F := fun out (μ' : GrMode) ↦ μ' = grOut b (HashSig.truncateHash out))
    Prod.fst (gSMod_map (F := fun out (μ' : GrMode) ↦ μ' = grOut b (HashSig.truncateHash out))
      (Quantum.Xmss.out256 : X → HashSig.HashOutput)
      (gSMod_map (F := fun x (μ' : GrMode) ↦ μ' = grOut b (trunc128 x)) (fun s : X × Z ↦ s.1)
        hfold) [])

/-- **The counter search** of a key `K_l(idx)` on `m`, from a mode ready for its trial `c`, ends
idle. -/
theorem gModed_grindK (l : Layer) (idx : Index) (m : Digest) :
    ∀ n c μ, c + n ≤ encodingAttemptLimit → GrReady pub (keyOf l idx) m c μ →
      ModedP (L := LocalSig.instruments) (gOkR pub) (gNxR pub) (fun _ (μ' : GrMode) ↦ μ'.Idle) μ
        (grindK Selections cwUpd pub B (keyOf l idx) m n c)
  | 0, _, _, _, h => h.idle
  | n + 1, c, μ, hn, h => by
    have hrec : ∀ μ', GrReady pub (keyOf l idx) m (c + 1) μ' →
        ModedP (L := LocalSig.instruments) (gOkR pub) (gNxR pub) (fun _ (μ' : GrMode) ↦ μ'.Idle)
          μ' (grindK Selections cwUpd pub B (keyOf l idx) m n (c + 1)) :=
      fun μ' h' ↦ gModed_grindK l idx m n (c + 1) μ' (by omega) h'
    have hok := h.ok (show c < encodingAttemptLimit by omega)
    have hh := gModed_hashTrial (B := B) h.idle (show c < encodingAttemptLimit by omega) rfl
      (blocks_trialInput pub _ m c) hok
    rw [grindK]
    refine modedP₂_bind
      (F := fun out (μ' : GrMode) ↦ μ' = grOut (tBlk pub (keyOf l idx) m c)
        (HashSig.truncateHash out))
      (F' := fun _ (μ' : GrMode) ↦ μ'.Idle) _ _ hh fun out μ' hμ' ↦ ?_
    subst hμ'
    rcases hd : TargetSum.decodeDigest (HashSig.truncateHash out) with _ | x
    · have hv : ¬Codeword.Valid (HashSig.truncateHash out) := Codeword.decode_eq_none_iff.1 hd
      exact hrec _ (grOut_of_not_valid hv)
    · exact grOut_idle _ _

end grind

/-! ## The challenge prefix is moded -/

section template

variable (pub : Pub)

/-- **Lifting runtime 1's moded programs to templates.** -/
theorem gModed_readLift {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → GrMode → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec X Z Selections) Ω A) {μ : GrMode}
    (hy : ModedP (gOkR pub) (gNxR pub) fin μ y) :
    ModedP (gOkT pub) (gNxT pub) fin μ (readLift goodAll y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hy.1, fun b ↦ ?_⟩
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;>
        rcases μ with τ | x₀ | ⟨x₀, a⟩ | ⟨x₀, a, c₀⟩ <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

/-- A sponge program of runtime 1 is moded between trials. -/
theorem gModed_liftOrdinary {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (spongeSpec X Z) Ω A) :
    ∀ μ : GrMode, μ.Idle → ModedP (gOkR pub) (gNxR pub) (fun _ (μ : GrMode) ↦ μ.Idle) μ
      (y.liftOrdinary (t := hwReadCmdSpec X Z Selections)) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => exact fun _ h ↦ h
  | liftBind _ c next ih =>
    intro μ hμ
    show ModedP _ _ _ _ (IFreeM.mapLens QuantumComp.ordinaryLens (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ μ hμ⟩
    · exact ⟨hμ, fun b ↦ ih _ _ trivial⟩

/-- **Realizing keeps the modes**, the remembered values becoming those of `v`. -/
theorem gModed_realizeT (v : (s : HPos) → XD s) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → GrMode → Prop} (y : QuantumComp L (SSpec Selections) Ω A)
    {μ : GrMode} (hy : ModedP (gOkT pub) (gNxT pub) fin μ y) :
    ModedP (gOkZ pub) (gNxZ pub v) fin μ (realizeT v y) := by
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
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 (ULift.up (restrictTo T v, b.down)))⟩

/-- A template moded between trials: from every mode between trials, it ends between trials. -/
def GIdle {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (SSpec Selections) Ω A) : Prop :=
  ∀ μ : GrMode, μ.Idle → ModedP (gOkT pub) (gNxT pub) (fun _ (μ : GrMode) ↦ μ.Idle) μ y

theorem gIdle_bind {A B B' : QReg} {α β : Type} (x : QComp (SSpec Selections) A B α)
    (g : α → QComp (SSpec Selections) B B' β) (hx : GIdle pub x) (hg : ∀ a, GIdle pub (g a)) :
    GIdle pub (x.bind g) :=
  fun μ hμ ↦ modedP₂_bind (F := fun _ (μ : GrMode) ↦ μ.Idle) (F' := fun _ (μ : GrMode) ↦ μ.Idle)
    x g (hx μ hμ) fun a μ' h ↦ hg a μ' h

theorem gIdle_pure {A : QReg} {α : Type} (a : α) :
    GIdle pub
      (QuantumComp₂.pure (L := LocalSig.instruments) (spec := SSpec Selections) (A := A) a) :=
  fun _ h ↦ h

theorem gIdle_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    GIdle pub (QComp.act (spec := SSpec Selections) p) :=
  fun _ hμ ↦ ⟨trivial, fun _ ↦ hμ⟩

/-- **A reveal** moves to the idle mode remembering its values. -/
theorem gModed_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × Selections) → QComp (SSpec Selections) B B' α)
    {F : α → GrMode → Prop} {μ : GrMode} (hμ : μ.Idle)
    (hk : ∀ r, ModedP (gOkT pub) (gNxT pub) (fun p μ' ↦ F p.2.2 μ') (.free (kOpt r.1)) (k r)) :
    ModedP (gOkT pub) (gNxT pub) (fun p μ' ↦ F p.2.2 μ') μ (revealThen goodAll T k) :=
  ⟨hμ, fun b ↦ modedP₂_bind (F := fun _ (μ' : GrMode) ↦ μ' = .free (kOpt b.down.1)) _ _
    ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ by subst h; exact hk b.down⟩

theorem gIdle_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × Selections) → QComp (SSpec Selections) B B' α)
    (hk : ∀ r, GIdle pub (k r)) : GIdle pub (revealThen goodAll T k) :=
  fun _ hμ ↦ gModed_revealThen pub T k (F := fun _ (μ : GrMode) ↦ μ.Idle) hμ fun r ↦
    hk r _ trivial

theorem gIdle_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec Selections) B B' α) (hk : GIdle pub k) : GIdle pub (progThen p hp k) :=
  fun _ hμ ↦ ⟨hμ, fun _ ↦ gIdle_bind pub _ _ (gIdle_act pub _) (fun _ ↦ hk) _ trivial⟩

theorem gIdle_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    GIdle pub (progPorts Selections B ps) := by
  induction ps with
  | nil => exact gIdle_pure pub _
  | cons p ps ih => exact gIdle_progThen pub p trivial _ ih

theorem gIdle_progSlots (B : QReg) (ss : List Slot) :
    GIdle pub (progSlots Selections pub B ss) := by
  induction ss with
  | nil => exact gIdle_pure pub _
  | cons s ss ih => exact gIdle_bind pub _ _ (gIdle_progPorts pub B _) fun _ ↦ ih

theorem gIdle_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    GIdle pub (forsOpenT Selections pub B idx lv) := by
  unfold forsOpenT
  exact gIdle_revealThen pub _ _ fun _ ↦
    gIdle_bind pub _ _ (gIdle_progSlots pub B _) fun _ ↦ gIdle_pure pub _

/-- **A layer signature by a key `K_l(idx)`**: its counter search runs right after the reveal of
`msgPos K`, from the idle mode remembering the revealed value. -/
theorem gIdle_signLayerT (B : QReg) (l : Layer) (idx : Index) :
    GIdle pub (signLayerT Selections cwUpd pub B (keyOf l idx)) := by
  intro μ hμ
  unfold signLayerT
  refine gModed_revealThen pub _ _ (F := fun _ (μ : GrMode) ↦ μ.Idle) hμ fun r₀ ↦ ?_
  refine modedP₂_bind (F := fun _ (μ' : GrMode) ↦ μ'.Idle) (F' := fun _ (μ' : GrMode) ↦ μ'.Idle)
    _ _ (gModed_readLift pub _ (gModed_grindK l idx _ _ 0 _ (Nat.zero_add _).le
      ⟨_, rfl, kOpt_of_mem r₀.1 (Finset.mem_singleton_self _)⟩)) fun g μ' hμ' ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · exact hμ'
  · exact gIdle_revealThen pub _ _ (fun r ↦ gIdle_bind pub _ _ (gIdle_progSlots pub B _)
      fun _ ↦ gIdle_pure pub _) μ' hμ'

/-- **A signature** is moded between trials, for every digest policy. -/
theorem gIdle_signT (pol : DigestPolicy) (B : QReg) (msg : Message) :
    GIdle pub (signT Selections cwUpd pol pub B msg) := by
  unfold signT
  refine gIdle_revealThen pub _ _ fun _ ↦ gIdle_revealThen pub _ _ fun _ ↦ ?_
  refine gIdle_bind pub _ _ (gIdle_progPorts pub B _) fun _ ↦ ?_
  refine gIdle_bind pub _ _ (gIdle_forsOpenT pub B _ _) fun _ ↦ ?_
  refine gIdle_bind pub _ _ (gIdle_signLayerT pub B _ _) fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · exact gIdle_pure pub _
  · refine gIdle_bind pub _ _ (gIdle_signLayerT pub B _ _) fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · exact gIdle_pure pub _
    · refine gIdle_bind pub _ _ (gIdle_signLayerT pub B _ _) fun s₂ ↦ ?_
      rcases s₂ with _ | top <;> exact gIdle_pure pub _

/-- **The challenger** is moded between trials, for every digest policy. -/
theorem gIdle_challengeT (pol : DigestPolicy) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) (μ : GrMode) (hμ : μ.Idle) :
    ModedP (gOkT pub) (gNxT pub) (fun _ (μ : GrMode) ↦ μ.Idle) μ
      (challengeT Selections cwUpd pol pub A cmd) := by
  rcases cmd with o | ⟨q | msg, E, ℓ⟩
  · exact gModed_readLift pub _ (gModed_liftOrdinary pub _ μ hμ)
  · exact gModed_readLift pub _ (gModed_liftOrdinary pub _ μ hμ)
  · exact modedP_bind _ _ (gIdle_bind pub _ _ (gIdle_act pub _)
      (fun _ ↦ gIdle_signT pub pol _ msg) μ hμ) fun _ _ μ' h ↦ h

theorem gModed_cast {spec : QuantumOracleSpec.{0, 0}} {ok : GrMode → spec.Port → Prop}
    {nx : GrMode → (i : spec.Port) → spec.Result i → GrMode} {Ω : QReg → Type w}
    {fin : (Σ u, Ω u) → GrMode → Prop} {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) (μ : GrMode) :
    ModedP ok nx fin μ (e ▸ y) ↔ ModedP ok nx fin μ y := by
  subst e
  rfl

/-- Substituting trees moded between trials. -/
theorem gIdle_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (SSpec Selections)))
    (hσ : ∀ A c, ∀ μ : GrMode, μ.Idle → ModedP (gOkT pub) (gNxT pub)
      (fun _ (μ : GrMode) ↦ μ.Idle) μ (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ∀ μ : GrMode, μ.Idle → ModedP (gOkT pub) (gNxT pub) (fun _ (μ : GrMode) ↦ μ.Idle) μ
      (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact fun _ h ↦ h
  | liftBind s c next ih =>
    intro μ hμ
    rw [IFreeM.substitute_liftBind]
    exact modedP_bind _ _ (hσ s c μ hμ) fun u ans μ' h ↦ (gModed_cast ans.2 _ _).mpr
      (ih ans.1 μ' h)

/-- **The challenge prefix is moded between trials**, for every digest policy. -/
theorem gIdle_prefixT (pol : DigestPolicy) (A : SAdversary) :
    GIdle pub (prefixT Selections cwUpd pol pub A) := by
  unfold prefixT challengedT
  exact gIdle_revealThen pub _ _ fun _ ↦
    gIdle_bind pub _ _ (gIdle_substitute pub _ (gIdle_challengeT pub pol) _) fun _ ↦
      gIdle_pure pub _

/-- **The realized challenge prefix is moded** by the search modes, from the idle mode. -/
theorem gModed_prefixR (pol : DigestPolicy) (A : SAdversary) (v : (s : HPos) → XD s) :
    ModedP (gOkZ pub) (gNxZ pub v) (fun _ (μ : GrMode) ↦ μ.Idle) GrMode.none
      (prefixR pol A pub v) :=
  gModed_realizeT pub v _ (gIdle_prefixT pub pol A GrMode.none trivial)

end template

/-! ## Off the trial's path -/

section recOff

set_option exponentiation.threshold 1024 in
/-- **A trial's update determines its rate's digest** (with KeyMsg's `trialUpd_inj`: its key and
block), so `trialOf` names the program's trial up to the rate's untruncated bits. -/
theorem trialUpd_xi {t t' : TrialPt} (h : trialUpd t' = trialUpd t) :
    trunc128 t'.xi = trunc128 t.xi := by
  have hc : 0 < cwCount := Nat.pos_of_ne_zero fun h0 ↦ by
    have := rhoCw_pos
    simp [rhoCw, h0] at this
  obtain ⟨w, hw⟩ := exists_of_card_filter_eq_mul (card_codeword_trunc128 t.xi) hc
    (Nat.two_pow_pos _)
  obtain ⟨hK, -⟩ := trialUpd_inj h
  set m₀ : Mem HPos := (∅, fun _ ↦ none) with hm₀
  have h1 : (trialUpd t' m₀ (some w)).2 t.K = (trialUpd t m₀ (some w)).2 t.K :=
    congrArg (fun m' : Mem HPos ↦ m'.2 t.K) (congrFun (congrFun h m₀) (some w))
  have hR : (trialUpd t m₀ (some w)).2 t.K = some (t.x, trunc128 (t.xi + w)) := by
    rw [show trialUpd t m₀ (some w) = (m₀.1, cwUpd t.K t.x t.xi m₀.2 (some w)) from rfl,
      snd_pair, cwUpd_some_of_none t.K t.x t.xi (show m₀.2 t.K = none from rfl), cwSel,
      ite_eq_left hw, Selections.select_self]
  have hL : (trialUpd t' m₀ (some w)).2 t.K = cwSel m₀.2 t'.K t'.x t'.xi w t.K := by
    rw [show trialUpd t' m₀ (some w) = (m₀.1, cwUpd t'.K t'.x t'.xi m₀.2 (some w)) from rfl,
      snd_pair, cwUpd_some_of_none t'.K t'.x t'.xi (show m₀.2 t'.K = none from rfl)]
  rw [hR, hL] at h1
  rcases cwSel_eq m₀.2 t'.K t'.x t'.xi w with he | he
  · rw [he] at h1
    exact absurd h1 (by simp [hm₀])
  · rw [he, hK, Selections.select_self] at h1
    have h2 := trunc128_add_congr (Prod.mk.inj (Option.some.inj h1)).2 (-w)
    rwa [add_neg_cancel_right, add_neg_cancel_right] at h2

variable (p : Pub)

/-- **The potentials of the search modes**: after a trial's `k`-read, the union misses its outcome;
after the `k'`-read, it misses the `k` or the `k'` outcome. -/
noncomputable def grPot : GrMode → Unit → Matrix (HwReg X Z (Mem HPos)) (HwReg X Z (Mem HPos)) ℂ
  | .afK x a, _ => setProj {s | KMiss x a s}
  | .afK' x a c, _ => setProj {s | KMiss x a s ∨ K'Miss (p.perm (x, a)).1 c s}
  | _, _ => 0

/-- **The leak charge of a read port**: after a `k` or `k'` read, the weight of the states whose
union misses the read's outcome (`0` at the `h` reads). -/
noncomputable def grLeakW : (c : HwRead X Z (Mem HPos)) →
    Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ → ℝ≥0∞
  | .readK x u, σ => ENNReal.ofReal (∑ r : Option Z × Mem HPos,
      dW (fun q ↦ if KMiss x (r.1.getD 0) q.2 then (1 : ℝ) else 0)
        (MatrixMap.conj (hwReadKraus (.readK x u) r) σ))
  | .readK' y u, σ => ENNReal.ofReal (∑ r : Option Z × Mem HPos,
      dW (fun q ↦ if K'Miss y (r.1.getD 0) q.2 then (1 : ℝ) else 0)
        (MatrixMap.conj (hwReadKraus (.readK' y u) r) σ))
  | .readH _ _, _ => 0

theorem grPot_grOut (x : X) (d : Digest) (j : Unit) : grPot p (grOut x d) j = 0 := by
  unfold grOut
  split_ifs <;> rfl

theorem sum_potential_grPot_zero {μ : GrMode} (hμ : ∀ j, grPot p μ j = 0) {A : Type} [Fintype A]
    [DecidableEq A] (σ : Matrix (A × HwReg X Z (Mem HPos)) (A × HwReg X Z (Mem HPos)) ℂ) :
    ∑ j, potential (grPot p μ j) σ = 0 :=
  Finset.sum_eq_zero fun j _ ↦ by rw [hμ j]; exact potential_zero σ

/-- A diagonal mass as a weighted diagonal. -/
theorem grDiagMass_eq_dW (S : Set (HwReg X Z (Mem HPos))) [DecidablePred (· ∈ S)]
    {τ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hτ : τ.PosSemidef) :
    diagMass {q : Unit × HwReg X Z (Mem HPos) | q.2 ∈ S} τ =
      ENNReal.ofReal (dW (fun q ↦ if q.2 ∈ S then (1 : ℝ) else 0) τ) := by
  have hre : ∀ q, 0 ≤ (τ q q).re := fun q ↦ (Complex.nonneg_iff.1 hτ.diag_nonneg).1
  unfold diagMass dW
  rw [ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hre q)]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases h : q.2 ∈ S
  · rw [Set.indicator_of_mem (show q ∈ {q : Unit × HwReg X Z (Mem HPos) | q.2 ∈ S} from h),
      ite_eq_left h, one_mul]
  · rw [Set.indicator_of_notMem (show q ∉ {q : Unit × HwReg X Z (Mem HPos) | q.2 ∈ S} from h),
      ite_eq_right h, zero_mul, ENNReal.ofReal_zero]

theorem recOffW_not_trial {c : HwRead X Z (Mem HPos)} (hc : ∀ z u, c ≠ .readH z u)
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) :
    recOffW p c σ = 0 := by
  unfold recOffW
  exact ite_eq_right fun ⟨_, h⟩ ↦ hc _ _ h

/-- **A trial `h`-read after its `k`-read with outcome `a` and `k'`-read with outcome `c` is off
its path only where the union misses one of the outcomes.** -/
theorem recOffW_le_miss {x : X} {a c z : Z} {K : Key} (hz : z = (p.perm (x, a)).2 + c)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    recOffW p (.readH z (trialUpd ⟨K, x, (p.perm (x, a)).1⟩)) σ ≤
      diagMass {q : Unit × HwReg X Z (Mem HPos) | q.2 ∈
        {s | KMiss x a s ∨ K'Miss (p.perm (x, a)).1 c s}} σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  set xi := (p.perm (x, a)).1
  have htr : IsTrial trialUpd (.readH z (trialUpd ⟨K, x, xi⟩) : HwRead X Z (Mem HPos)) :=
    ⟨(z, ⟨K, x, xi⟩), rfl⟩
  have hc := eq_readH_trialOf trialUpd htr
  obtain ⟨hz', hu'⟩ := HwRead.readH.inj hc
  obtain ⟨-, hx⟩ := trialUpd_inj hu'.symm
  have hxi := trialUpd_xi hu'.symm
  rw [grDiagMass_eq_dW _ hσ]
  unfold recOffW
  rw [ite_eq_left htr]
  refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ ?_)
  dsimp only
  by_cases hm : q.2 ∈ {s : HwReg X Z (Mem HPos) | KMiss x a s ∨ K'Miss xi c s}
  · rw [ite_eq_left hm, one_mul]
    split_ifs
    exacts [le_rfl, hre q]
  · rw [ite_eq_right hm, zero_mul]
    have hka : (union q.2.2.1 q.2.1).k x = some a := not_not.1 fun h ↦ hm (.inl h)
    have hkc : (union q.2.2.1 q.2.1).k' xi = some c := not_not.1 fun h ↦ hm (.inr h)
    refine (ite_eq_right fun h ↦ h.2.2 ⟨xi, hxi.symm, ?_⟩).le
    rw [hx, ← hz']
    exact ⟨[], 0, x, a, (p.perm (x, a)).2, c, rfl, IsTail.nil, hka, by rw [zero_add], hkc, hz⟩

/-- The step condition at a `k`-read from a mode without potential. -/
theorem recOff_step_readK {μ : GrMode} (hμ : ∀ j, grPot p μ j = 0) (x : X)
    (u : Mem HPos → Option Z → Mem HPos)
    (hnx : ∀ r, gRdNx p μ (.readK x u) r = .afK x (r.1.getD 0))
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    recOffW p (.readK x u) σ + ∑' r, ∑ j, potential (grPot p (gRdNx p μ (.readK x u) r) j)
        (MatrixMap.conj (hwReadKraus (.readK x u) r) σ) ≤
      ∑ j, potential (grPot p μ j) σ + grLeakW (.readK x u) σ := by
  have hpos : ∀ r, (MatrixMap.conj (hwReadKraus (.readK x u) r) σ).PosSemidef :=
    fun r ↦ posSemidef_conj _ hσ
  have hL : ∀ r : Option Z × Mem HPos, ∑ j, potential (grPot p (gRdNx p μ (.readK x u) r) j)
      (MatrixMap.conj (hwReadKraus (.readK x u) r) σ) =
      ENNReal.ofReal (dW (fun q ↦ if KMiss x (r.1.getD 0) q.2 then (1 : ℝ) else 0)
        (MatrixMap.conj (hwReadKraus (.readK x u) r) σ)) := fun r ↦ by
    rw [hnx r, Fintype.sum_unique]
    exact (potential_setProj _ (hpos r)).trans (grDiagMass_eq_dW _ (hpos r))
  rw [recOffW_not_trial p (fun _ _ h ↦ by cases h), zero_add, tsum_fintype,
    Finset.sum_congr rfl fun r _ ↦ hL r, sum_potential_grPot_zero p hμ, zero_add]
  show _ ≤ ENNReal.ofReal _
  rw [ENNReal.ofReal_sum_of_nonneg fun r _ ↦ dW_nonneg (fun q ↦ by split_ifs <;> norm_num)
    (hpos r)]

/-- The step condition at the `k'`-read after the `k`-read at `x` with outcome `a`. -/
theorem recOff_step_readK' (x : X) (a : Z) (u : Mem HPos → Option Z → Mem HPos)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    recOffW p (.readK' (p.perm (x, a)).1 u) σ + ∑' r, ∑ j, potential (grPot p
        (gRdNx p (.afK x a) (.readK' (p.perm (x, a)).1 u) r) j)
        (MatrixMap.conj (hwReadKraus (.readK' (p.perm (x, a)).1 u) r) σ) ≤
      ∑ j, potential (grPot p (.afK x a) j) σ + grLeakW (.readK' (p.perm (x, a)).1 u) σ := by
  have hpos : ∀ r, (MatrixMap.conj (hwReadKraus (.readK' (p.perm (x, a)).1 u) r) σ).PosSemidef :=
    fun r ↦ posSemidef_conj _ hσ
  have hnn : ∀ (f : Unit × HwReg X Z (Mem HPos) → ℝ), (∀ q, 0 ≤ f q) → ∀ r : Option Z × Mem HPos,
      0 ≤ dW f (MatrixMap.conj (hwReadKraus (.readK' (p.perm (x, a)).1 u) r) σ) :=
    fun f hf r ↦ dW_nonneg hf (hpos r)
  have hi : ∀ q : Unit × HwReg X Z (Mem HPos), (0 : ℝ) ≤ if KMiss x a q.2 then 1 else 0 :=
    fun q ↦ by split_ifs <;> norm_num
  have hi' : ∀ (r : Option Z × Mem HPos) (q : Unit × HwReg X Z (Mem HPos)),
      (0 : ℝ) ≤ if K'Miss (p.perm (x, a)).1 (r.1.getD 0) q.2 then 1 else 0 := fun r q ↦ by
    split_ifs <;> norm_num
  have hL : ∀ r : Option Z × Mem HPos, ∑ j, potential (grPot p (gRdNx p (.afK x a)
      (.readK' (p.perm (x, a)).1 u) r) j)
        (MatrixMap.conj (hwReadKraus (.readK' (p.perm (x, a)).1 u) r) σ) =
      ENNReal.ofReal (dW (fun q ↦ if q.2 ∈ {s | KMiss x a s ∨
        K'Miss (p.perm (x, a)).1 (r.1.getD 0) s} then (1 : ℝ) else 0)
        (MatrixMap.conj (hwReadKraus (.readK' (p.perm (x, a)).1 u) r) σ)) := fun r ↦ by
    rw [Fintype.sum_unique]
    exact (potential_setProj _ (hpos r)).trans (grDiagMass_eq_dW _ (hpos r))
  have hR : ∑ j, potential (grPot p (.afK x a) j) σ =
      ENNReal.ofReal (dW (fun q ↦ if KMiss x a q.2 then (1 : ℝ) else 0) σ) := by
    rw [Fintype.sum_unique]
    exact (potential_setProj _ hσ).trans (grDiagMass_eq_dW _ hσ)
  rw [recOffW_not_trial p (fun _ _ h ↦ by cases h), zero_add, tsum_fintype,
    Finset.sum_congr rfl fun r _ ↦ hL r, hR, ← readK'_keep_kMiss (p.perm (x, a)).1 u x a σ]
  show _ ≤ _ + ENNReal.ofReal _
  rw [← ENNReal.ofReal_add (Finset.sum_nonneg fun r _ ↦ hnn _ hi r)
      (Finset.sum_nonneg fun r _ ↦ hnn _ (hi' r) r), ← Finset.sum_add_distrib,
    ENNReal.ofReal_sum_of_nonneg fun r _ ↦ add_nonneg (hnn _ hi r) (hnn _ (hi' r) r)]
  refine Finset.sum_le_sum fun r _ ↦ ENNReal.ofReal_le_ofReal ?_
  rw [← dW_add]
  unfold dW
  refine Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right ?_
    ((Complex.nonneg_iff.1 (hpos r).diag_nonneg).1)
  dsimp only
  by_cases h1 : KMiss x a q.2
  · have : q.2 ∈ {s | KMiss x a s ∨ K'Miss (p.perm (x, a)).1 (r.1.getD 0) s} := .inl h1
    rw [ite_eq_left this, ite_eq_left h1]
    linarith [hi' r q]
  · by_cases h2 : K'Miss (p.perm (x, a)).1 (r.1.getD 0) q.2
    · have : q.2 ∈ {s | KMiss x a s ∨ K'Miss (p.perm (x, a)).1 (r.1.getD 0) s} := .inr h2
      rw [ite_eq_left this, ite_eq_right h1, ite_eq_left h2, zero_add]
    · have : q.2 ∉ {s | KMiss x a s ∨ K'Miss (p.perm (x, a)).1 (r.1.getD 0) s} :=
        fun h ↦ h.elim h1 h2
      rw [ite_eq_right this, ite_eq_right h1, ite_eq_right h2, add_zero]

/-- **The step condition of the search modes at a read port.** -/
theorem recOff_step_read (μ : GrMode) (c : HwRead X Z (Mem HPos))
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hok : gRdOk p μ c) :
    recOffW p c σ + ∑' r, ∑ j, potential (grPot p (gRdNx p μ c r) j)
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      ∑ j, potential (grPot p μ j) σ + grLeakW c σ := by
  rcases μ with τ | x₀ | ⟨x, a⟩ | ⟨x, a, c₀⟩
  · obtain ⟨-, -, -, -, rfl⟩ := hok
    exact recOff_step_readK p (fun _ ↦ rfl) _ _ (fun _ ↦ rfl) hσ
  · obtain ⟨-, -, -, -, -, -, rfl⟩ := hok
    exact recOff_step_readK p (fun _ ↦ rfl) _ _ (fun _ ↦ rfl) hσ
  · subst hok
    exact recOff_step_readK' p x a _ hσ
  · obtain ⟨K, -, -, -, -, rfl⟩ := hok
    have h0 : ∀ r, ∑ j, potential (grPot p (gRdNx p (.afK' x a c₀)
        (.readH ((p.perm (x, a)).2 + c₀) (trialUpd ⟨K, x, (p.perm (x, a)).1⟩) :
          HwRead X Z (Mem HPos)) r) j)
        (MatrixMap.conj (hwReadKraus (.readH ((p.perm (x, a)).2 + c₀)
          (trialUpd ⟨K, x, (p.perm (x, a)).1⟩)) r) σ) = 0 :=
      fun r ↦ sum_potential_grPot_zero p (grPot_grOut p _ _) _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero, Fintype.sum_unique]
    show recOffW p _ σ ≤ potential (setProj {s | KMiss x a s ∨
      K'Miss (p.perm (x, a)).1 c₀ s}) σ + 0
    rw [add_zero, potential_setProj _ hσ]
    exact recOffW_le_miss p rfl hσ

/-- **The step condition of the search modes for `recOffW`.** -/
theorem recOff_step (μ : GrMode) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ)
    (hσ : σ.PosSemidef) (hok : gOkZ p μ i) (v : (s : HPos) → XD s) :
    extWeight (hwCost (recOffW p) fun _ _ ↦ 0) i σ +
        ∑' r, ∑ j, potential (grPot p (gNxZ p v μ i r) j) (((runtimeR m0R).step i).branch r σ) ≤
      ∑ j, potential (grPot p μ j) σ + extWeight (hwCost grLeakW fun _ _ ↦ 0) i σ := by
  rcases i with ((q | c) | c) | T
  · have h0 : ∀ r, ∑ j, potential (grPot p (gNxZ p v μ (.inl (.inl (.inl q))) r) j)
        (((runtimeR m0R).step (.inl (.inl (.inl q)))).branch r σ) = 0 :=
      fun r ↦ Finset.sum_eq_zero fun _ _ ↦ potential_zero _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero]
    exact zero_le
  · have hb : ∀ r, ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    simp only [hb]
    exact recOff_step_read p μ c hσ hok
  · have h0 : ∀ r, ∑ j, potential (grPot p (gNxZ p v μ (.inl (.inr c)) r) j)
        (((runtimeR m0R).step (.inl (.inr c))).branch r σ) = 0 :=
      fun r ↦ Finset.sum_eq_zero fun _ _ ↦ potential_zero _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero]
    exact zero_le
  · have h0 : ∀ r, ∑ j, potential (grPot p (gNxZ p v μ (.inr T) r) j)
        (((runtimeR m0R).step (.inr T)).branch r σ) = 0 :=
      fun r ↦ Finset.sum_eq_zero fun _ _ ↦ potential_zero _
    rw [ENNReal.tsum_eq_zero.2 h0, add_zero]
    exact zero_le

variable (v : (s : HPos) → XD s)

/-- **The off-path mass moves onto the leaks of the trials' `k`, `k'` reads** (the search modes of
the prefix, from the idle mode without potential). -/
theorem recOffPre_le_leak (pol : DigestPolicy) (A : SAdversary) :
    recOffPre p v pol A ≤ (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost grLeakW fun _ _ ↦ 0)) (prefixR pol A p v) initR := by
  have h := totalWeight_le_modedP (runtimeR m0R) .instruments (grPot p)
    (extWeight (hwCost (recOffW p) fun _ _ ↦ 0)) (extWeight (hwCost grLeakW fun _ _ ↦ 0))
    (fun μ i σ hσ hok ↦ recOff_step p μ i σ hσ hok v) (prefixR pol A p v) GrMode.none
    (gModed_prefixR p pol A v) initR_posSemidef
  have h0 : ∑ j, potential (grPot p GrMode.none j) initR = 0 :=
    Finset.sum_eq_zero fun _ _ ↦ potential_zero _
  exact h.trans ((add_le_add (le_of_eq h0) le_rfl).trans (le_of_eq (zero_add _)))

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The leaks along the prefix**: at most `2/|Z|` per read call (`readK_leak_le`,
`readK'_leak_le` on the prefix's states, which have no decompressed `⊥`). -/
theorem totalWeight_grLeakW_le (pol : DigestPolicy) :
    (runtimeR m0R).totalWeight .instruments (extWeight (hwCost grLeakW fun _ _ ↦ 0))
      (prefixR pol A p v) initR ≤ ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞) := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign pol p v
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w' := fun i σ ↦ ENNReal.ofReal (2 / Fintype.card Z) * extWeight (hwCost
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR pol A p v) initR_posSemidef hx).trans ?_
  · rcases i with ((i | c) | c) | T
    · exact zero_le
    · show grLeakW c σ ≤ ENNReal.ofReal (2 / Fintype.card Z) * ENNReal.ofReal σ.trace.re
      have hnb : ReadNoBot c σ := readNoBot_of_noBot c hI.2.2
      have htr : σ.trace.re = ∑ a, (σ a a).re := by rw [Matrix.trace, Complex.re_sum]; rfl
      rw [← ENNReal.ofReal_mul (by positivity), htr]
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
      · exact zero_le
      · exact ENNReal.ofReal_le_ofReal (readK_leak_le x u hσ hnb)
      · exact ENNReal.ofReal_le_ofReal (readK'_leak_le y u hσ hnb)
    · exact zero_le
    · exact zero_le
  · refine (le_of_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments _
      (extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
        fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (prefixR pol A p v) initR)).trans ?_
    exact mul_le_mul_of_nonneg_left (totalWeight_calls_le (prefixR pol A p v)
      (clsCalls_prefixR hperm hsign pol p v)) zero_le

/-- **The off-path mass of the trial reads along the prefix**: `recOffPre ≤ 2/|Z| · clsCap`, for
every digest policy and template data. -/
theorem recOffPre_le (pol : DigestPolicy) :
    recOffPre p v pol A ≤ ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞) :=
  (recOffPre_le_leak p v pol A).trans (totalWeight_grLeakW_le p v hperm hsign pol)

end recOff

set_option exponentiation.threshold 1024 in
/-- `2/|Z| · clsCap ≤ 2^-443` (`clsCap ≤ 2^68`). -/
theorem recOffTau_le : ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞) ≤
    ENNReal.ofReal (1 / 2 ^ 443) := by
  have hc : (clsCap : ℝ) ≤ 2 ^ 68 := by
    have := progCap_add_le (q := 0) (Nat.zero_le _)
    exact_mod_cast (by omega : clsCap ≤ 2 ^ 68)
  rw [rnCard_Z, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hc (by positivity)).trans ?_)
  norm_num

/-- **`RecOffAvg`**: `τO = 2/|Z| · clsCap` (at most `2^-443`, `recOffTau_le`), for every digest
policy, family of template data and good set. -/
theorem recOffAvg {q : ℕ} {A : SAdversary}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
    (pol : DigestPolicy) {Θ : Type} [Fintype Θ] (P : Θ → Pub) (V : Θ → (s : HPos) → XD s)
    (good : Θ → Prop) [DecidablePred good] :
    RecOffAvg pol A P V good (ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞)) := by
  unfold RecOffAvg
  refine (uavg_mono fun θ ↦ ?_).trans (uavg_const_le _)
  by_cases hθ : good θ
  · rw [ite_eq_left hθ]
    exact recOffPre_le (P θ) (V θ) hperm hsign pol
  · rw [ite_eq_right hθ]
    exact zero_le

/-! ## The persistence invariant in the decompressed basis -/

section dInv

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- The view's digest of trial `j` of key `K` on the value it signs. -/
def kDg (t : SpongeKeys X Z) (K : Key) (j : ℕ) : Digest :=
  encDigest pub t K (kVal v K) (BitVec.ofNat counterBits j)

theorem kDg_eq (t : SpongeKeys X Z) (K : Key) (j : ℕ) :
    kDg pub v t K j = trunc128 (trialRate t pub.perm (tBlk pub K (kVal v K) j)) :=
  encDigest_eq pub (blocks_encIn pub K _ _)

/-- **The selections are the view's first codewords**: a stored selection of a key is the trial
`j` of a key `K_l(idx)` on the value it signs, whose digest in the view is the stored codeword,
the earlier trials' digests not codewords. -/
def SelCons (s : SReg) : Prop :=
  ∀ K sel, s.2.2.2 K = some sel → ∃ l idx, K = keyOf l idx ∧ ∃ j < encodingAttemptLimit,
    sel.1 = tBlk pub K (kVal v K) j ∧ sel.2 = kDg pub v (regFns s) K j ∧
      Codeword.Valid sel.2 ∧ ∀ i < j, ¬Codeword.Valid (kDg pub v (regFns s) K i)

/-- **The invariant between searches**: no decompressed `⊥`, hardwired cells programmable, and the
selections the view's first codewords unless a trial reads a programmable cell (`TrialHit`). -/
def DGlob (s : SReg) : Prop :=
  NoBot s ∧ GoodW (ProgCell pub v) s.2.1 ∧ (s ∈ TrialHit pub v ∨ SelCons pub v s)

/-- **A search position**: the block `x` is trial `j` of a key `K_l(idx)` on the value it signs,
and the view's digests of its trials before `j + n` are no codewords. -/
def DPos (x : X) (n : ℕ) (s : SReg) : Prop :=
  ∃ l idx j, j < encodingAttemptLimit ∧ x = tBlk pub (keyOf l idx) (kVal v (keyOf l idx)) j ∧
    ∀ i < j + n, ¬Codeword.Valid (kDg pub v (regFns s) (keyOf l idx) i)

/-- **The invariant of a search mode**: the remembered values are `v`'s; between trials, the
earlier trials' view digests are no codewords; after the `k`-read the view holds its outcome,
after the `k'`-read the view holds both outcomes. -/
def DInv : GrMode → Set SReg
  | .free τ => {s | DGlob pub v s ∧ KAgree τ (valsOf v)}
  | .grd x => {s | DGlob pub v s ∧ DPos pub v x 1 s}
  | .afK x a => {s | DGlob pub v s ∧ DPos pub v x 0 s ∧ (regFns s).2.1 x = a}
  | .afK' x a c => {s | DGlob pub v s ∧ DPos pub v x 0 s ∧ (regFns s).2.1 x = a ∧
      (regFns s).2.2 (pub.perm (x, a)).1 = c}

variable {pub v}

theorem dGlob_of_dInv {μ : GrMode} {s : SReg} (h : s ∈ DInv pub v μ) : DGlob pub v s := by
  rcases μ with τ | x | ⟨x, a⟩ | ⟨x, a, c⟩
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1

theorem dInv_none {s : SReg} (h : DGlob pub v s) : s ∈ DInv pub v GrMode.none :=
  ⟨h, fun _ _ h' ↦ by cases h'⟩

/-- The databases, the hardwired cells and the selections determine `DGlob`. -/
theorem dGlob_congr {s s' : SReg} (h1 : s'.1 = s.1) (h2 : s'.2.1 = s.2.1)
    (h3 : s'.2.2.2 = s.2.2.2) (h : DGlob pub v s) : DGlob pub v s' := by
  obtain ⟨hn, hw, hc⟩ := h
  have hr : regFns s' = regFns s := by
    show (union s'.2.1 s'.1).fill = (union s.2.1 s.1).fill
    rw [h1, h2]
  refine ⟨show NoBotDb s'.1 by rw [h1]; exact hn, by rw [h2]; exact hw, ?_⟩
  rcases hc with hc | hc
  · exact .inl ((trialHit_iff_of_offAgree (by rw [hr]; exact offAgree_refl _ _)).1 hc)
  · refine .inr fun K sel hs ↦ ?_
    rw [h3] at hs
    rw [hr]
    exact hc K sel hs

theorem dPos_congr {x : X} {n : ℕ} {s s' : SReg} (h : regFns s' = regFns s)
    (hp : DPos pub v x n s) : DPos pub v x n s' := by
  unfold DPos
  rw [h]
  exact hp

theorem hwView_k_noBotS {s : SReg} (hs : NoBot s) (x : X) :
    (hwView s.2.1 s.1).2.1 x = some ((regFns s).2.1 x) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (or_isSome (s.2.1.2.1 x) (hs.2.1 x))
  show (s.2.1.2.1 x).or (s.1.2.1 x) = some (((s.2.1.2.1 x).or (s.1.2.1 x)).getD 0)
  rw [ha]
  rfl

theorem hwView_k'_noBotS {s : SReg} (hs : NoBot s) (x : X) :
    (hwView s.2.1 s.1).2.2 x = some ((regFns s).2.2 x) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (or_isSome (s.2.1.2.2 x) (hs.2.2 x))
  show (s.2.1.2.2 x).or (s.1.2.2 x) = some (((s.2.1.2.2 x).or (s.1.2.2 x)).getD 0)
  rw [ha]
  rfl

/-- **A program call moves the view only at its cell.** -/
theorem progRel_offAgree {c : HwProg X Z} {s s' : SReg} (h : ProgRel c s s')
    {P : SpongeQuery X Z → Prop} (hc : P (progPt c)) : OffAgree P (regFns s) (regFns s') := by
  obtain ⟨hs2, -, hh, hk, hk'⟩ := h
  have hW : s'.2.1 = progUpdate c s.2.1 := congrArg Prod.fst hs2
  refine ⟨fun z hz ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have nh : ∀ a, c ≠ .programH z a := by
      rintro a rfl
      exact hz hc
    show ((s.2.1.1 z).or (s.1.1 z)).getD 0 = ((s'.2.1.1 z).or (s'.1.1 z)).getD 0
    rw [hW, progUpdate_h_of_ne nh, hh z nh]
  · have nk : ∀ a, c ≠ .programK x a := by
      rintro a rfl
      exact hx hc
    show ((s.2.1.2.1 x).or (s.1.2.1 x)).getD 0 = ((s'.2.1.2.1 x).or (s'.1.2.1 x)).getD 0
    rw [hW, progUpdate_k_of_ne nk, hk x nk]
  · have nk' : ∀ a, c ≠ .programK' x a := by
      rintro a rfl
      exact hx hc
    show ((s.2.1.2.2 x).or (s.1.2.2 x)).getD 0 = ((s'.2.1.2.2 x).or (s'.1.2.2 x)).getD 0
    rw [hW, progUpdate_k'_of_ne nk', hk' x nk']

/-- **The selections stay the view's first codewords** when the view moves only at programmable
cells and no trial reads one. -/
theorem selCons_of_offAgree {s s' : SReg} (h : OffAgree (ProgCell pub v) (regFns s) (regFns s'))
    (hn : s ∉ TrialHit pub v) (hm : s'.2.2.2 = s.2.2.2) (hs : SelCons pub v s) :
    SelCons pub v s' := by
  intro K sel hsel
  rw [hm] at hsel
  obtain ⟨l, idx, rfl, j, hj, h1, h2, h3, h4⟩ := hs K sel hsel
  have hd : ∀ i < encodingAttemptLimit, kDg pub v (regFns s') (keyOf l idx) i =
      kDg pub v (regFns s) (keyOf l idx) i := fun i hi ↦ encDigest_congr hn h l idx hi
  refine ⟨l, idx, rfl, j, hj, h1, by rw [hd j hj]; exact h2, h3, fun i hi ↦ ?_⟩
  rw [hd i (hi.trans hj)]
  exact h4 i hi

/-! ### The ports keep the invariant -/

theorem dInv_sponge (μ : GrMode) (p : SpongePort)
    (r : (recHwSpec X Z HPos Selections).Result (.inl (.inl (.inl p))))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inl p))) × SReg)
      ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inl p))) × SReg) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In (.inl (.inl (.inl p))) ×
      SReg ↦ m.2) (DInv pub v μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out (.inl (.inl (.inl p))) ×
      SReg ↦ m.2) (DInv pub v GrMode.none)
      (((decR (X := X) (Z := Z) m0R).step (.inl (.inl (.inl p)))).branch r σ) :=
  (decR_sponge_supp m0R p r _ σ hσ).mono fun _ hs ↦ dInv_none (dGlob_of_dInv hs)

theorem dInv_rec (μ : GrMode) (T : Finset HPos)
    (mem : (recHwSpec X Z HPos Selections).Result (.inr T))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In (.inr T) × SReg)
      ((recHwSpec X Z HPos Selections).In (.inr T) × SReg) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In (.inr T) × SReg ↦ m.2)
      (DInv pub v μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out (.inr T) × SReg ↦ m.2)
      (DInv pub v (.free (kOpt (restrictTo T v))))
      (((decR (X := X) (Z := Z) m0R).step (.inr T)).branch mem σ) := by
  refine (decR_rec_supp m0R T mem _ σ hσ).mono ?_
  rintro s' ⟨s, hs, -, rfl⟩
  exact ⟨dGlob_congr (s := s) rfl rfl rfl (dGlob_of_dInv hs), kAgree_kOpt v T⟩

theorem dInv_prog (μ : GrMode) (c : HwProg X Z) (hc : ProgCell pub v (progPt c))
    (r : (recHwSpec X Z HPos Selections).Result (.inl (.inr c)))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In (.inl (.inr c)) × SReg)
      ((recHwSpec X Z HPos Selections).In (.inl (.inr c)) × SReg) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In (.inl (.inr c)) × SReg ↦
      m.2) (DInv pub v μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out (.inl (.inr c)) × SReg ↦ m.2)
      (DInv pub v GrMode.none)
      (((decR (X := X) (Z := Z) m0R).step (.inl (.inr c))).branch r σ) := by
  refine (decR_prog_supp m0R c r _ σ hσ).mono ?_
  rintro s' ⟨s, hs, hrel⟩
  obtain ⟨hn, hw, hsel⟩ := dGlob_of_dInv hs
  have hoff := progRel_offAgree hrel hc
  have hW : s'.2.1 = progUpdate c s.2.1 := congrArg Prod.fst hrel.1
  have hm : s'.2.2.2 = s.2.2.2 := by rw [hrel.1]
  refine dInv_none ⟨hrel.2.1 hn, by rw [hW]; exact goodW_progUpdate hw hc, ?_⟩
  by_cases hh : s ∈ TrialHit pub v
  · exact .inl ((trialHit_iff_of_offAgree hoff).1 hh)
  · rcases hsel with hsel | hsel
    · exact absurd hsel hh
    · exact .inr (selCons_of_offAgree hoff hh hm hsel)

/-- **A trial's `k`-read keeps the invariant**: from a mode at a search position, it moves to the
mode after the `k`-read with the view's outcome. -/
theorem dInv_readK {μ : GrMode} {y : X} (hμ : ∀ s ∈ DInv pub v μ, DPos pub v y 0 s)
    (r : (recHwSpec X Z HPos Selections).Result (.inl (.inl (.inr (readKPort y)))))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inr (readKPort y)))) × SReg)
      ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inr (readKPort y)))) × SReg) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In
      (.inl (.inl (.inr (readKPort y)))) × SReg ↦ m.2) (DInv pub v μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out
      (.inl (.inl (.inr (readKPort y)))) × SReg ↦ m.2)
      (DInv pub v (.afK y (r.1.getD 0)))
      (((decR (X := X) (Z := Z) m0R).step (.inl (.inl (.inr (readKPort y))))).branch r σ) := by
  refine (decR_readU_supp m0R (.readK y keepMem) r _ σ hσ).mono ?_
  rintro s' ⟨s, hs, rfl, rfl⟩
  have hg := dGlob_of_dInv hs
  refine ⟨dGlob_congr (s := s) rfl rfl rfl hg, dPos_congr rfl (hμ s hs), ?_⟩
  show (regFns s).2.1 y = ((hwView s.2.1 s.1).2.1 y).getD 0
  rw [hwView_k_noBotS hg.1]
  rfl

theorem dInv_readK' {x : X} {a : Z}
    (r : (recHwSpec X Z HPos Selections).Result
      (.inl (.inl (.inr (readK'Port (pub.perm (x, a)).1)))))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In
      (.inl (.inl (.inr (readK'Port (pub.perm (x, a)).1)))) × SReg)
      ((recHwSpec X Z HPos Selections).In
        (.inl (.inl (.inr (readK'Port (pub.perm (x, a)).1)))) × SReg) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In
      (.inl (.inl (.inr (readK'Port (pub.perm (x, a)).1)))) × SReg ↦ m.2)
      (DInv pub v (.afK x a)) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out
      (.inl (.inl (.inr (readK'Port (pub.perm (x, a)).1)))) × SReg ↦ m.2)
      (DInv pub v (.afK' x a (r.1.getD 0)))
      (((decR (X := X) (Z := Z) m0R).step
        (.inl (.inl (.inr (readK'Port (pub.perm (x, a)).1))))).branch r σ) := by
  refine (decR_readU_supp m0R (.readK' (pub.perm (x, a)).1 keepMem) r _ σ hσ).mono ?_
  rintro s' ⟨s, ⟨hg, hp, ha⟩, rfl, rfl⟩
  refine ⟨dGlob_congr (s := s) rfl rfl rfl hg, dPos_congr rfl hp, ha, ?_⟩
  show (regFns s).2.2 (pub.perm (x, a)).1 = ((hwView s.2.1 s.1).2.2 (pub.perm (x, a)).1).getD 0
  rw [hwView_k'_noBotS hg.1]
  rfl

/-- The view's digest at the `h`-read of a trial whose `k`, `k'` outcomes the view holds. -/
theorem kDg_of_outcomes {s : SReg} {l : Layer} {idx : Index} {j : ℕ} {x : X} {a c : Z}
    (hx : x = tBlk pub (keyOf l idx) (kVal v (keyOf l idx)) j) (ha : (regFns s).2.1 x = a)
    (hc : (regFns s).2.2 (pub.perm (x, a)).1 = c) :
    kDg pub v (regFns s) (keyOf l idx) j =
      trunc128 ((pub.perm (x, a)).1 + (regFns s).1 ((pub.perm (x, a)).2 + c)) := by
  rw [kDg_eq, ← hx]
  unfold trialRate trialMid
  rw [zero_add, zero_add, ha, hc]

/-- **The trial's `h`-read keeps the invariant**: it reads the view's cell, so a selection it
records is the view's digest of the trial, a codeword after non-codewords; the search stops at a
codeword and goes on to the next trial otherwise. -/
theorem dInv_readH {x : X} {a c : Z} {K : Key} {m : Digest} {j' : ℕ}
    (hj' : j' < encodingAttemptLimit) (hx' : x = tBlk pub K m j')
    (r : (recHwSpec X Z HPos Selections).Result (.inl (.inl (.inr (liftRead (S := HPos)
      (.readH ((pub.perm (x, a)).2 + c) (cwUpd K x (pub.perm (x, a)).1)))))))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inr (liftRead (S := HPos)
      (.readH ((pub.perm (x, a)).2 + c) (cwUpd K x (pub.perm (x, a)).1)))))) × SReg)
      ((recHwSpec X Z HPos Selections).In (.inl (.inl (.inr (liftRead (S := HPos)
        (.readH ((pub.perm (x, a)).2 + c) (cwUpd K x (pub.perm (x, a)).1)))))) × SReg) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In (.inl (.inl (.inr
      (liftRead (S := HPos) (.readH ((pub.perm (x, a)).2 + c)
        (cwUpd K x (pub.perm (x, a)).1)))))) × SReg ↦ m.2) (DInv pub v (.afK' x a c)) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out (.inl (.inl (.inr
      (liftRead (S := HPos) (.readH ((pub.perm (x, a)).2 + c)
        (cwUpd K x (pub.perm (x, a)).1)))))) × SReg ↦ m.2)
      (DInv pub v (grOut x (trunc128 ((pub.perm (x, a)).1 + r.1.getD 0))))
      (((decR (X := X) (Z := Z) m0R).step (.inl (.inl (.inr (liftRead (S := HPos)
        (.readH ((pub.perm (x, a)).2 + c) (cwUpd K x (pub.perm (x, a)).1))))))).branch r σ) := by
  refine (decR_readU_supp m0R (.readH ((pub.perm (x, a)).2 + c) (cwUpd K x (pub.perm (x, a)).1))
    r _ σ hσ).mono ?_
  rintro s' ⟨s, ⟨⟨hn, hw, hsel⟩, ⟨l, idx, j, hj, hx, hlow⟩, ha, hc⟩, rfl, rfl⟩
  obtain ⟨hK, -, -⟩ := tBlk_inj hj' hj (hx'.symm.trans hx)
  subst hK
  have hr : ((hwView s.2.1 s.1).1 ((pub.perm (x, a)).2 + c)).getD 0 =
      (regFns s).1 ((pub.perm (x, a)).2 + c) := by
    rw [hwView_h_of_noBot hn]
    rfl
  have hdg := kDg_of_outcomes (pub := pub) (v := v) hx ha hc
  have hreg : regFns (readFin s (.readH ((pub.perm (x, a)).2 + c)
      (cwUpd (keyOf l idx) x (pub.perm (x, a)).1))) = regFns s := rfl
  have hmem : (readFin s (.readH ((pub.perm (x, a)).2 + c)
      (cwUpd (keyOf l idx) x (pub.perm (x, a)).1))).2.2.2 =
      cwUpd (keyOf l idx) x (pub.perm (x, a)).1 s.2.2.2
        (some ((regFns s).1 ((pub.perm (x, a)).2 + c))) := by
    show cwUpd (keyOf l idx) x (pub.perm (x, a)).1 s.2.2.2
      ((hwView s.2.1 s.1).1 ((pub.perm (x, a)).2 + c)) = _
    rw [hwView_h_of_noBot hn]
  have hglob : DGlob pub v (readFin s (.readH ((pub.perm (x, a)).2 + c)
      (cwUpd (keyOf l idx) x (pub.perm (x, a)).1))) := by
    refine ⟨hn, hw, ?_⟩
    rcases hsel with hsel | hsel
    · exact .inl ((trialHit_iff_of_offAgree (by rw [hreg]; exact offAgree_refl _ _)).1 hsel)
    refine .inr fun K' sel hm ↦ ?_
    rw [hreg]
    rw [hmem] at hm
    rcases cwUpd_some (keyOf l idx) x (pub.perm (x, a)).1 s.2.2.2
      ((regFns s).1 ((pub.perm (x, a)).2 + c)) with he | he
    · rw [he] at hm
      exact hsel K' sel hm
    rw [he] at hm
    unfold cwSel at hm
    split_ifs at hm with hv
    · by_cases hK' : K' = keyOf l idx
      · subst hK'
        rw [Selections.select_self] at hm
        obtain rfl := (Option.some_inj.mp hm).symm
        exact ⟨l, idx, rfl, j, hj, hx, hdg.symm, hv, fun i hi ↦ hlow i (by omega)⟩
      · rw [Selections.select_of_ne _ _ _ hK'] at hm
        exact hsel K' sel hm
    · exact hsel K' sel hm
  show readFin s _ ∈ DInv pub v (grOut x (trunc128 ((pub.perm (x, a)).1 +
    ((hwView s.2.1 s.1).1 ((pub.perm (x, a)).2 + c)).getD 0)))
  rw [hr]
  unfold grOut
  split_ifs with hv
  · exact dInv_none hglob
  · refine ⟨hglob, l, idx, j, hj, hx, fun i hi ↦ ?_⟩
    rw [hreg]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hlow i (by omega)
    · rw [hdg]
      exact hv

/-- **Every allowed call of a port programming a programmable cell keeps the invariant of its
mode.** -/
theorem dInv_step (μ : GrMode) (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × SReg)
      ((recHwSpec X Z HPos Selections).In i × SReg) ℂ)
    (hok : gOkZ pub μ i) (hin : CellPortIn (ProgCell pub v) i)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × SReg ↦ m.2)
      (DInv pub v μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i × SReg ↦ m.2)
      (DInv pub v (gNxZ pub v μ i r)) (((decR (X := X) (Z := Z) m0R).step i).branch r σ) := by
  rcases i with ((p | c) | c) | T
  · exact dInv_sponge μ p r σ hσ
  · rcases μ with τ | x₀ | ⟨x, a⟩ | ⟨x, a, c₀⟩
    · obtain ⟨l, idx, m, hτ, rfl⟩ := hok
      exact dInv_readK (fun s hs ↦ ⟨l, idx, 0, Nat.two_pow_pos _,
        by rw [← hs.2 _ _ hτ]; rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩) r σ hσ
    · obtain ⟨l, idx, m, j, hj, rfl, rfl⟩ := hok
      refine dInv_readK (fun s hs ↦ ?_) r σ hσ
      obtain ⟨-, l', idx', j', hj', hx', hlow⟩ := hs
      obtain ⟨hK, hm, rfl⟩ := tBlk_inj (by omega) hj' hx'
      exact ⟨l', idx', j + 1, hj, by rw [hm, hK], fun i hi ↦ hlow i (by omega)⟩
    · subst hok
      exact dInv_readK' r σ hσ
    · obtain ⟨K, m, j, hj, hx, rfl⟩ := hok
      exact dInv_readH hj hx r σ hσ
  · exact dInv_prog μ c hin r σ hσ
  · exact dInv_rec μ T r σ hσ

/-! ### A re-grind trial's hit -/

/-- **No re-grind trial hits its key's selected digest**, unless a trial reads a programmable
cell: at trial `j` of a key the view's digests of the earlier trials are no codewords and the
trial's digest is the view's; the key's selection is the view's first codeword at a trial `j'` of
the same search (each key signs one value). The hit makes the trial's digest that codeword:
`j < j'` contradicts the selection's earlier non-codewords, `j' < j` the search's, `j = j'` makes
the trial the selected input, whose tail has no target. -/
theorem trialHit_of_hitG {x : X} {a c : Z} {K : Key} {m : Digest} {j' : ℕ}
    (hj' : j' < encodingAttemptLimit) (hx' : x = tBlk pub K m j') {t : TrialPt} (hK : t.K = K)
    (htx : t.x = x) (hxi : trunc128 t.xi = trunc128 (pub.perm (x, a)).1) {s : SReg}
    (hs : s ∈ DInv pub v (.afK' x a c))
    (h : hitG pub v ((pub.perm (x, a)).2 + c) t s.2 (s.1.1 ((pub.perm (x, a)).2 + c))) :
    s ∈ TrialHit pub v := by
  obtain ⟨⟨-, -, hsel⟩, ⟨l, idx, j, hj, hx, hlow⟩, ha, hc⟩ := hs
  rcases hsel with hh | hsel
  · exact hh
  exfalso
  obtain ⟨hK', -, -⟩ := tBlk_inj hj' hj (hx'.symm.trans hx)
  subst hK'
  obtain ⟨hW, -, y, hy, htgt⟩ := h
  rw [htx] at htgt
  have hslot : slotOf (evData pub v).pk [x] = some (.enc t.K.1 t.K.2.1 t.K.2.2) := by
    rw [hx, hK]
    exact slotOf_encBlk pub v _ _ _
  obtain ⟨s', hs', hst | hst⟩ := sphTgt_eq_some_iff.1 htgt
  · obtain rfl := Option.some.inj (hslot.symm.trans hs')
    exact (structTgt_eq_some_iff.1 hst).1.1.elim
  obtain ⟨l', τ, e, x', rfl, hsl, hne⟩ := encTgt_eq_some_iff.1 hst
  obtain ⟨h1, h2, h3⟩ := Slot.enc.inj (Option.some.inj (hslot.symm.trans hs'))
  have hKe : (l', τ, e) = keyOf l idx := by
    rw [← hK]
    exact (Prod.ext h1 (Prod.ext h2 h3)).symm
  rw [hKe] at hsl
  obtain ⟨l₂, idx₂, -, j₂, hj₂, e1, e2, e3, e4⟩ := hsel _ _ hsl
  have hvz : (regFns s).1 ((pub.perm (x, a)).2 + c) = y := by
    show ((s.2.1.1 _).or (s.1.1 _)).getD 0 = y
    rw [hW, hy]
    rfl
  have hdg : kDg pub v (regFns s) (keyOf l idx) j = trunc128 (t.xi + y) := by
    rw [kDg_of_outcomes hx ha hc, hvz]
    exact (trunc128_add_congr hxi y).symm
  dsimp only at e1 e2 e3
  rcases lt_trichotomy j j₂ with hlt | rfl | hgt
  · exact e4 j hlt (by rw [hdg]; exact e3)
  · exact hne (by rw [hx, e1])
  · exact hlow j₂ (by omega) (by rw [← e2]; exact e3)

end dInv

/-! ## The invariant along the challenge prefix -/

section dRun

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **The challenge prefix's program ports program programmable cells** in batch order. -/
theorem hbCell_prefixT (pol : DigestPolicy) (A : SAdversary) :
    HB (cellOk (M := Selections) (ProgCell pub v)) v (prefixT Selections cwUpd pol pub A) ∅ ∅ :=
  hb_revealThen _ v _ _ fun _ ↦
    hb₂_bind _ v _ _ (hb_substitute _ v _ (hb_challengeT _ v pub
      (fun _ hs ↦ batchOk_slotCell pub v hs) (fun msg i y ↦ batchOk_hmsgCall pub v msg i y)
      cwUpd pol) _) fun _ ↦ subset_rfl

/-- **The realized prefix calls only program ports of programmable cells.** -/
theorem forallQueries_cellPortIn_prefixR (pol : DigestPolicy) (A : SAdversary) :
    (runtimeR m0R).ForallQueries .instruments (fun j _ _ ↦ CellPortIn (ProgCell pub v) j)
      (prefixR pol A pub v) initR :=
  forallQueries_cellPortIn_of_hb m0R _ _ v _ ∅ ∅ (hbCell_prefixT pub v pol A) heldCompat_empty _

variable {pub v}

theorem dInv_init :
    QuerySupportedOn (fun m : QReg.of Unit × SReg ↦ m.2) (DInv pub v GrMode.none)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z (Mem HPos)) initR) := by
  refine (init_dec m0R).mono ?_
  rintro s ⟨hn, hs⟩
  have hW : s.2.1 = hwEmpty X Z := congrArg Prod.fst hs
  have hm : s.2.2.2 = m0 := congrArg (fun p ↦ p.2.2) hs
  refine dInv_none ⟨hn, ?_, .inr fun K sel h ↦ ?_⟩
  · rw [hW]
    intro q hq
    cases q <;> exact absurd rfl hq
  · rw [hm] at h
    cases h

variable (pub v)

/-- The calls of the prefix in the decompressed basis program programmable cells. -/
theorem forallQueries_cellPortIn_dec (pol : DigestPolicy) (A : SAdversary) :
    (decR (X := X) (Z := Z) m0R).ForallQueries .instruments
      (fun i _ _ ↦ CellPortIn (ProgCell pub v) i) (prefixR pol A pub v)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z (Mem HPos)) initR) := by
  have hC : compressReg X Z (Mem HPos) * compressReg X Z (Mem HPos) = 1 := compressReg_mul_self
  have h := ForallQueries.of_simulation .instruments
    (R₁ := runtimeRH (X := X) (Z := Z) m0R)
    (R₂ := decR m0R) (V := MatrixMap.conj (compressReg X Z (Mem HPos))) (fun i r ↦ by
      simp only [MatrixMap.amplifyLeft_conj]
      rw [conjReg_branch (runtimeRH m0R) (compressReg X Z (Mem HPos)) compressReg_mul_self
          conjTranspose_compressReg, LinearMap.comp_assoc, LinearMap.comp_assoc,
        conj_one_kronecker_comp_self (runtimeRH m0R) _ hC, LinearMap.comp_id])
    (P₂ := fun i _ _ ↦ CellPortIn (ProgCell pub v) i) (fun _ _ _ h ↦ h)
    (forallQueries_cellPortIn_prefixR pub v pol A)
  rwa [MatrixMap.amplifyLeft_conj] at h

/-- **The invariant at the calls of the prefix, in the decompressed basis.** -/
theorem forallQueries_dInv_dec (pol : DigestPolicy) (A : SAdversary) :
    (decR (X := X) (Z := Z) m0R).ForallQueries .instruments (fun i E σ ↦ ∃ μ,
      gOkZ pub μ i ∧
        QuerySupportedOn (fun m : ((recHwSpec X Z HPos Selections).In i × SReg) × E ↦ m.1.2)
          (DInv pub v μ) σ) (prefixR pol A pub v)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z (Mem HPos)) initR) :=
  forallQueries_of_modedP_guard (decR m0R) .instruments (DInv pub v)
    (CellPortIn (ProgCell pub v))
    (fun μ i r σ hok hin hσ ↦ dInv_step μ i r σ hok hin hσ) (prefixR pol A pub v) GrMode.none
    (gModed_prefixR pub pol A v) (forallQueries_cellPortIn_dec pub v pol A) dInv_init

/-- **The invariant at the calls of the prefix**: every call is presented an operator whose
decompressed form is supported on the invariant of a mode allowing it. -/
theorem forallQueries_dInv (pol : DigestPolicy) (A : SAdversary) :
    (runtimeR m0R).ForallQueries .instruments (fun i E τ ↦ ∃ μ, gOkZ pub μ i ∧
        QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × SReg ↦ m.2)
          (DInv pub v μ)
          (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
            ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z (Mem HPos))
            (MatrixMap.traceRight _ E τ))) (prefixR pol A pub v) initR := by
  have hC : compressReg X Z (Mem HPos) * compressReg X Z (Mem HPos) = 1 := compressReg_mul_self
  have hstep : ∀ i r, ((runtimeRH (X := X) (Z := Z) m0R).step i).branch r ∘ₗ
      (MatrixMap.conj (compressReg X Z (Mem HPos))).amplifyLeft
        ((recHwSpec X Z HPos Selections).In i) =
      (MatrixMap.conj (compressReg X Z (Mem HPos))).amplifyLeft
        ((recHwSpec X Z HPos Selections).Out i) ∘ₗ ((decR m0R).step i).branch r := fun i r ↦ by
    rw [conjReg_branch (runtimeRH m0R) (compressReg X Z (Mem HPos)) compressReg_mul_self
      conjTranspose_compressReg i r]
    simp only [MatrixMap.amplifyLeft_conj]
    rw [← LinearMap.comp_assoc, conj_one_kronecker_comp_self (runtimeRH m0R) _ hC,
      LinearMap.id_comp]
  have h2 := ForallQueries.of_simulation .instruments (R₁ := decR m0R)
    (R₂ := runtimeRH (X := X) (Z := Z) m0R) (V := MatrixMap.conj (compressReg X Z (Mem HPos)))
    hstep
    (P₂ := fun i E τ ↦ ∃ μ, gOkZ pub μ i ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × SReg ↦ m.2)
        (DInv pub v μ)
        (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
          ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z (Mem HPos))
          (MatrixMap.traceRight _ E τ)))
    (fun i E τ ⟨μ, hok, hτ⟩ ↦ ⟨μ, hok, by
      rw [MatrixMap.amplifyLeft_conj,
        ← LinearMap.comp_apply (MatrixMap.conj _) (MatrixMap.traceRight _ E),
        ← MatrixMap.traceRight_comp_amplify, LinearMap.comp_apply,
        ← LinearMap.comp_apply (MatrixMap.amplify _ E) (MatrixMap.amplify _ E),
        ← MatrixMap.amplify_comp, conj_one_kronecker_comp_self (runtimeRH m0R) _ hC,
        MatrixMap.amplify_id, LinearMap.id_apply]
      exact querySupportedOn_traceRight
        (q := fun m : (recHwSpec X Z HPos Selections).In i × SReg ↦ m.2) hτ⟩)
    (forallQueries_dInv_dec pub v pol A)
  have hρ' : (MatrixMap.conj (compressReg X Z (Mem HPos))).amplifyLeft (QReg.of Unit)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z (Mem HPos)) initR) = initR := by
    rw [MatrixMap.amplifyLeft_conj,
      ← LinearMap.comp_apply (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z (Mem HPos))), conj_one_kronecker_comp_self (runtimeRH m0R) _ hC,
      LinearMap.id_apply]
  rw [hρ'] at h2
  exact h2

end dRun

/-! ## The trial event, counted -/

section dCount

variable (pub : Pub) (v : (s : HPos) → XD s)

open scoped Classical in
/-- **The projector on the trial event** of the databases, in the decompressed basis. -/
noncomputable def trialQ : Matrix SReg SReg ℂ :=
  hwDecProj (trialEventP pub v)

variable {pub v}

/-- **A call's decompressed re-grind hit weight is at most its trial-event weight**
(`trialHit_of_hitG`). -/
theorem decHitAW_le_potential {μ : GrMode} {c : HwRead X Z (Mem HPos)} (hok : gRdOk pub μ c)
    {σ : Matrix (Unit × SReg) (Unit × SReg) ℂ} (hσ : σ.PosSemidef)
    (hs : QuerySupportedOn (fun m : Unit × SReg ↦ m.2) (DInv pub v μ)
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Mem HPos)) σ)) :
    decHitAW pub v c σ ≤ potential (trialQ pub v) σ := by
  rcases μ with τ | x₀ | ⟨x, a⟩ | ⟨x, a, c₀⟩
  · obtain ⟨-, -, -, -, rfl⟩ := hok
    unfold decHitAW
    rw [ite_eq_right fun ⟨_, h⟩ ↦ by cases h]
    exact zero_le
  · obtain ⟨-, -, -, -, -, -, rfl⟩ := hok
    unfold decHitAW
    rw [ite_eq_right fun ⟨_, h⟩ ↦ by cases h]
    exact zero_le
  · subst hok
    unfold decHitAW
    rw [ite_eq_right fun ⟨_, h⟩ ↦ by cases h]
    exact zero_le
  · obtain ⟨K, m, j, hj, hx, rfl⟩ := hok
    have htr : IsTrial trialUpd (.readH ((pub.perm (x, a)).2 + c₀)
        (trialUpd ⟨K, x, (pub.perm (x, a)).1⟩) : HwRead X Z (Mem HPos)) :=
      ⟨((pub.perm (x, a)).2 + c₀, ⟨K, x, (pub.perm (x, a)).1⟩), rfl⟩
    have hc := eq_readH_trialOf trialUpd htr
    obtain ⟨hz', hu'⟩ := HwRead.readH.inj hc
    obtain ⟨hK, htx⟩ := trialUpd_inj hu'.symm
    have hxi := trialUpd_xi hu'.symm
    unfold decHitAW trialQ
    rw [ite_eq_left htr, potential_eq, conjTranspose_hwDecProj, hwDecProj_mul_self]
    refine ENNReal.ofReal_le_ofReal (re_trace_hwDecProj_le _ _ (DInv pub v (.afK' x a c₀))
      hσ hs fun s hsI hsE ↦ ?_)
    have hsE' : hitG pub v ((pub.perm (x, a)).2 + c₀) (trialOf trialUpd
        (.readH ((pub.perm (x, a)).2 + c₀) (trialUpd ⟨K, x, (pub.perm (x, a)).1⟩) :
          HwRead X Z (Mem HPos))).2 s.2 (s.1.1 ((pub.perm (x, a)).2 + c₀)) := by
      have h := hsE
      rw [← hz'] at h
      exact h
    exact hitView_of_trialHit (dGlob_of_dInv hsI).2.1
      (trialHit_of_hitG hj hx hK htx hxi hsI hsE')

/-- **The ports of programmable cells do not raise the trial event's weight** (DecUniform: the
event is determined off the programmable cells). -/
theorem tsum_potential_trialQ_le (i : (recHwSpec X Z HPos Selections).Port)
    (hin : CellPortIn (ProgCell pub v) i)
    {σ : Matrix ((recHwSpec X Z HPos Selections).In i × SReg)
      ((recHwSpec X Z HPos Selections).In i × SReg) ℂ} (hσ : σ.PosSemidef) :
    ∑' r, potential (trialQ pub v) (((runtimeR m0R).step i).branch r σ) ≤
      potential (trialQ pub v) σ := by
  let _ : DecidablePred (· ∈ trialEventP pub v) := Classical.decPred _
  refine tsum_potential_branch_le (runtimeR m0R) i _ (fun r ↦ ?_) hσ
  have hE : ∀ s : SReg, s ∈ trialEventP pub v ↔
      (fun D : DbReg X Z ↦ HitView pub v D.toDbs.fill) s.1 := fun _ ↦ Iff.rfl
  unfold trialQ
  rcases i with ((p | c) | c) | T
  · cases p <;> exact branch_comm_of_commute
      (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m0R _ r) (hwPort_commute_hwDecProj _ _)
  · exact branch_comm_of_commute (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r)
      (hwReadKraus_commute_hwDecProj _ (fun D : DbReg X Z ↦ HitView pub v D.toDbs.fill) hE c r)
  · exact branch_comm_of_commute (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m0R c r)
      (hwProgKraus_commute_hwDecProj _ hitView_congr hE (cellIn_cellsHw hin) r)
  · let _ : DecidablePred fun b : Hw X Z × Mem HPos ↦ b.2 = r := fun b ↦ instDecidableEqProd b.2 r
    exact branch_comm_of_commute (recStep_branch T r)
      (clsKraus_one_commute_hwDecProj _ (fun D : DbReg X Z ↦ HitView pub v D.toDbs.fill) hE
        (fun b : Hw X Z × Mem HPos ↦ b.2 = r) _)

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The decompressed re-grind hit weight along the prefix** is at most `clsCap` times the
initial weight of the trial event, for every digest policy. -/
theorem decHitAPre_le_trialQ (pol : DigestPolicy) :
    decHitAPre pub v pol A ≤ clsCap * potential (trialQ pub v) initR := by
  calc decHitAPre pub v pol A ≤ (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ σ ↦ potential (trialQ pub v) σ) fun _ _ ↦ 0))
          (prefixR pol A pub v) initR :=
        totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
          (fun i σ ↦ ∃ μ, gOkZ pub μ i ∧
            QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × SReg ↦ m.2)
              (DInv pub v μ) (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
                ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z (Mem HPos)) σ))
          (fun _ _ _ h ↦ h)
          (fun i σ hσ hI ↦ by
            rcases i with ((p' | c) | c) | T
            · exact zero_le
            · obtain ⟨μ, hok, hs⟩ := hI
              exact decHitAW_le_potential hok hσ hs
            · exact zero_le
            · exact zero_le) (prefixR pol A pub v) initR_posSemidef (forallQueries_dInv pub v pol A)
    _ ≤ clsCap * potential (trialQ pub v) initR :=
        totalWeight_le_charge_potential (runtimeR m0R) .instruments (trialQ pub v) _
          (CellPortIn (ProgCell pub v)) _ (fun i σ _ _ ↦ by
            rcases i with ((p' | c) | c) | T
            · exact zero_le
            · show potential (trialQ pub v) σ ≤ ((if extCls X Z (Mem HPos) (recSpec HPos Selections)
                (.inl (.inl (.inr c))) then 1 else 0 : ℕ) : ℝ≥0∞) * potential (trialQ pub v) σ
              simp [extCls, hwCls]
            · exact zero_le
            · exact zero_le)
          (fun i hi σ hσ ↦ tsum_potential_trialQ_le i hi hσ) (prefixR pol A pub v)
          (clsCalls_prefixR hperm hsign pol pub v) initR_posSemidef
          (forallQueries_cellPortIn_prefixR pub v pol A)

omit hperm hsign in
/-- **The initial weight of the trial event**: at most
`|trialBlocksP| (18 |k'CellsP| + |hCellsP|) / |Z|` (the uniform initial databases). -/
theorem potential_trialQ_initR_le (hoff : TrialsOff pub.xw pub.keys.1 (valsOf v))
    (hπ : PermGood pub.perm 18) :
    potential (trialQ pub v) initR ≤ (((trialBlocksP pub v).card * (18 * (k'CellsP pub v).card +
      (hCellsP pub v).card) : ℕ) : ℝ≥0∞) / Fintype.card Z := by
  classical
  have h1 : potential (trialQ pub v) initR = ENNReal.ofReal
      (((Finset.univ.filter fun t ↦ HitView pub v (ofFunDbs t).toDbs.fill).card : ℝ) /
        Fintype.card ((Z → X) × (X → Z) × (X → Z))) := by
    unfold potential trialQ
    rw [MatrixMap.amplifyLeft_conj]
    change ENNReal.ofReal (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
      hwDecProj _) ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty,
        Database.empty, Database.empty), hwEmpty X Z, m0R) : SReg)).matrix)).trace.re = _
    simp only [SubState.matrix_basis]
    rw [trace_conj_hwDecProj_basis (trialEventP pub v) (fun D ↦ HitView pub v D.toDbs.fill)
      (fun _ ↦ Iff.rfl) (hwEmpty X Z, m0R),
      Matrix.trace_single_eq_same, Complex.one_re, one_mul]
  rw [h1, ← natCast_div_eq_ofReal _ _ Fintype.card_pos]
  exact natCast_div_le_div_of_mul_le Fintype.card_pos Fintype.card_pos
    (card_mul_card_filter_le_of_blocks hπ (k'CellsP pub v) (hCellsP pub v) (trialBlocksP pub v)
      (fun t ↦ HitView pub v (ofFunDbs t).toDbs.fill) fun _ ht ↦ badBlk_of_hitView hoff ht)

omit hperm hsign in
set_option exponentiation.threshold 1024 in
/-- `clsCap · 2^-189 ≤ 2^-121` (`clsCap ≤ 2^68`). -/
theorem decHitTerm_le : (clsCap : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 189) ≤
    ENNReal.ofReal (1 / 2 ^ 121) := by
  have hc : (clsCap : ℝ) ≤ 2 ^ 68 := by
    have := progCap_add_le (q := 0) (Nat.zero_le _)
    exact_mod_cast (by omega : clsCap ≤ 2 ^ 68)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right hc (by positivity)).trans ?_)
  norm_num

/-- **The decompressed re-grind hit weight at Keccak's sizes**: at most `2^-121` on template data
with `TrialsOff` and `PermGood 18`, for every digest policy. -/
theorem decHitAPre_le_keccak (pol : DigestPolicy) (hoff : TrialsOff pub.xw pub.keys.1 (valsOf v))
    (hπ : PermGood pub.perm 18) : decHitAPre pub v pol A ≤ ENNReal.ofReal (1 / 2 ^ 121) :=
  (decHitAPre_le_trialQ hperm hsign pol).trans ((mul_le_mul_of_nonneg_left
    ((potential_trialQ_initR_le hoff hπ).trans (trialHitTermP_le (card_trialBlocksP_le pub v)
      (card_k'CellsP_le pub v) (card_hCellsP_le pub v) rnCard_Z)) zero_le).trans decHitTerm_le)

omit hperm hsign in
/-- A trial read's decompressed re-grind hit weight is at most its trace. -/
theorem decHitAW_le_trace (c : HwRead X Z (Mem HPos))
    {σ : Matrix (Unit × SReg) (Unit × SReg) ℂ} (hσ : σ.PosSemidef) :
    decHitAW pub v c σ ≤ ENNReal.ofReal σ.trace.re := by
  unfold decHitAW
  split_ifs
  · exact ENNReal.ofReal_le_ofReal (re_trace_hwDecProj_le_trace _ hσ)
  · exact zero_le

/-- The decompressed re-grind hit weight of any template data is at most `clsCap`. -/
theorem decHitAPre_le_clsCap (pol : DigestPolicy) : decHitAPre pub v pol A ≤ clsCap :=
  (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
      fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (fun i σ hσ ↦ by
        rcases i with ((p' | c) | c) | T
        · exact zero_le
        · exact decHitAW_le_trace c hσ
        · exact zero_le
        · exact zero_le) (prefixR pol A pub v) initR_posSemidef).trans
    (totalWeight_calls_le (prefixR pol A pub v) (clsCalls_prefixR hperm hsign pol pub v))

end dCount

/-! ## The averaged bound -/

section dAvg

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **`DecHitAvg`**: `τA = 2^-121` on every good set of template data with `TrialsOff` and
`PermGood 18`, for every digest policy. -/
theorem decHitAvg (pol : DigestPolicy) {Θ : Type} [Fintype Θ] (P : Θ → Pub)
    (V : Θ → (s : HPos) → XD s) (good : Θ → Prop) [DecidablePred good]
    (hg : ∀ θ, good θ → TrialsOff (P θ).xw (P θ).keys.1 (valsOf (V θ)) ∧ PermGood (P θ).perm 18) :
    DecHitAvg pol A P V good (ENNReal.ofReal (1 / 2 ^ 121)) := by
  unfold DecHitAvg
  refine (uavg_mono fun θ ↦ ?_).trans (uavg_const_le _)
  by_cases hθ : good θ
  · rw [ite_eq_left hθ]
    exact decHitAPre_le_keccak hperm hsign pol (hg θ hθ).1 (hg θ hθ).2
  · rw [ite_eq_right hθ]
    exact zero_le

open scoped Classical in
/-- **`DecHitAvg` with a bad fraction**: on a good set with `PermGood 18`, if `TrialsOff` fails
for a fraction at most `ε` of the template data, `τA = 2^-121 + clsCap · ε` (`clsCap` bounds the
weight where it fails). -/
theorem decHitAvg_of_frac (pol : DigestPolicy) {Θ : Type} [Fintype Θ] (P : Θ → Pub)
    (V : Θ → (s : HPos) → XD s) (good : Θ → Prop) [DecidablePred good]
    (hg : ∀ θ, good θ → PermGood (P θ).perm 18) {ε : ℝ≥0∞}
    (hε : (Fintype.card Θ : ℝ≥0∞)⁻¹ *
      (Finset.univ.filter fun θ ↦ ¬TrialsOff (P θ).xw (P θ).keys.1 (valsOf (V θ))).card ≤ ε) :
    DecHitAvg pol A P V good (ENNReal.ofReal (1 / 2 ^ 121) + clsCap * ε) := by
  unfold DecHitAvg
  calc uavg (fun θ ↦ if good θ then decHitAPre (P θ) (V θ) pol A else 0)
      ≤ uavg (fun θ ↦ ENNReal.ofReal (1 / 2 ^ 121) + (clsCap : ℝ≥0∞) *
          (if TrialsOff (P θ).xw (P θ).keys.1 (valsOf (V θ)) then (0 : ℝ≥0∞) else 1)) :=
        uavg_mono fun θ ↦ by
          by_cases hθ : good θ
          · rw [ite_eq_left hθ]
            by_cases ho : TrialsOff (P θ).xw (P θ).keys.1 (valsOf (V θ))
            · rw [ite_eq_left ho, mul_zero, add_zero]
              exact decHitAPre_le_keccak hperm hsign pol ho (hg θ hθ)
            · rw [ite_eq_right ho, mul_one]
              exact (decHitAPre_le_clsCap hperm hsign pol).trans le_add_self
          · rw [ite_eq_right hθ]
            exact zero_le
    _ = uavg (fun _ : Θ ↦ ENNReal.ofReal (1 / 2 ^ 121)) + (clsCap : ℝ≥0∞) *
          uavg (fun θ ↦ if TrialsOff (P θ).xw (P θ).keys.1 (valsOf (V θ)) then (0 : ℝ≥0∞)
            else 1) := by
        rw [uavg_add, uavg_const_mul]
    _ ≤ ENNReal.ofReal (1 / 2 ^ 121) + clsCap * ε := by
        refine add_le_add (uavg_const_le _) (mul_le_mul_of_nonneg_left ?_ zero_le)
        rw [uavg_ite_zero_one]
        exact hε

end dAvg

end Quantum.Sphincs.Assembly

end
