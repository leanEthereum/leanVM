module

public import Quantum.Sphincs.Assembly.CwRev
public import Quantum.Xmss.Assembly.CwReFail

@[expose] public section

/-!
# The failed searches of leanSPHINCS's counter searches

CwRev's hypothesis `CwReView pol A p ε`, proved here for digest policies revealing no value
position (`msgPol`, `strPol`) on permutations with `PermGood p.perm 18`, at `ε = cfEps = 2^-157`:
the mass at the repeated disclosures of a value whose key is still unselected. As leanXMSS's
`Quantum.Xmss.Assembly.CwReFail`, keyed by keys.

* **Modes that see the stop** (`stRdNx`, `CwMode.Rest`, `CwMode.Calm`, `RevOk`,
  `modedP_prefixR_st`): CwRec's search modes, except that a trial's `h`-read whose digest is a
  codeword ends the search, the sponge calls happen only between searches (free, or after the last
  trial), the programs also with a disclosed key's search next (`pend`), and the reveals disclose
  at most one key's value from between searches, or start the pending search.
* **The invariant in the decompressed basis** (`TB`, `FInv`, `fInv_step`, `init_fInv`): no empty
  cell, the hardwired cells inside the static `W₀ = cellsHw (ProgCell p v)`, and every key whose
  value is disclosed and which is unselected has every trial already run touching `W₀` or failing,
  on the decompressed databases. The program cells are in `W₀` by TrialHit's port condition
  (`modedP_and_port`).
* **The repeated disclosures** (`reRevW_le`, `totalWeight_reRevW_le`): a repeated disclosure with
  the key unselected lies in the database event `failSet` (some key fails all its trials); its
  decompressed projector commutes with every called port, so the reveal charges against it add up
  to the reveal bound `1 + 9 · signatureLimit` times its fraction of the total tables.
* **Counting** (`frac_failDb_le`): XMSS's `frac_fail_le` per key `K_l(idx)`, with TrialHit's cell
  counts (`k'CellsP`, `hCellsP`, at most `2^50 + 2^257` each) and the codeword fraction
  `ρ ≥ 2^-14` of `2^32` trials.
* **The bound** (`cwReView_cf`, `uavg_cwRecPre_le`): `CwReView pol A p cfEps`, and the averaged
  codeword-recorded mass at most `cwRevTau q cfEps`.
-/

universe u v w

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest PublicParameter HashInput HashOutput Message truncateHash)
open Quantum.Xmss (X Z blocks trunc128 out256)
open Quantum.Xmss.Hybrid (LazyProg restrictTo totalWeight_le_totalWeight setProj diagMass
  diagMass_mono progUpdate uavg runtime2_branch)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT tmplLens readLift readLiftQ
  readLens revealThen progThen RevealVals hashTrial rdRoundU rdHU liftRead ModedP
  modedP_bind modedP₂_bind modedP_map modeCmdOk modeCmdNx recStep_branch
  totalWeight_le_of_forallQueries NoBot NoBotDb noBot_init decR decR_branch_apply
  dec_clsKraus_ne_zero dec_dbs_ne_zero compressAll_one_ne_zero compressDbs_one_ne_zero
  or_eq_of_hwIn compressAll_mul_cellDiscard_mul_compressAll_ne_zero
  one_kron_mul_hwPort_mul_one_kron forallQueries_dec_moded PortCw runtimeR_commute_hwDecProj
  diagMass_le_potential_hwDecProj potential_hwDecProj_init totalWeight_charge_potential_le
  frac_fail_le tY tZ natCast_pow_sub_div_le_exp sum_not_eq rnCard_Z natCast_div_eq_ofReal
  isChargeBound_of_bind₂ realizeT_bind₂)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default
size. -/
set_option synthInstance.maxSize 2000

/- Membership in the concrete FORS opening's sets is otherwise decided by evaluating them. -/
attribute [local irreducible] forsNeed forsSlots

/-! ## The keys a reveal discloses -/

section revKeys

/-- **At most one key of the signatures has its value in `T`.** -/
def OneKey (T : Finset HPos) : Prop :=
  ∀ K K', InRange K → InRange K' → HPos.val (msgPos K) ∈ T → HPos.val (msgPos K') ∈ T → K = K'

theorem oneKey_of_noKey {T : Finset HPos} (h : ∀ K, InRange K → HPos.val (msgPos K) ∉ T) :
    OneKey T :=
  fun K _ hK _ hm _ ↦ absurd hm (h K hK)

theorem cwSingKey_eq_none_of_noKey {T : Finset HPos}
    (h : ∀ K, InRange K → HPos.val (msgPos K) ∉ T) : cwSingKey T = none :=
  cwSingKey_eq_none fun K hK hT ↦ h K hK (by rw [hT]; exact Finset.mem_singleton_self _)

theorem cwDiscKey_eq_none_of_noKey {T : Finset HPos}
    (h : ∀ K, InRange K → HPos.val (msgPos K) ∉ T) : cwDiscKey T = none := by
  unfold cwDiscKey
  split_ifs with h'
  · exact absurd h'.choose_spec.2.1 (h _ h'.choose_spec.1)
  · rfl

/-- A reveal of no single key's value and of no key's value among others discloses no key's
value. -/
theorem noKey_of_none {T : Finset HPos} (hs : cwSingKey T = none) (hd : cwDiscKey T = none) :
    ∀ K, InRange K → HPos.val (msgPos K) ∉ T := by
  intro K hK hm
  by_cases hT : T = {.val (msgPos K)}
  · rw [hT, cwSingKey_eq hK] at hs
    cases hs
  · unfold cwDiscKey at hd
    split_ifs at hd with h'
    · exact h' ⟨K, hK, hm, hT⟩

theorem cwRevNx_free {T : Finset HPos} (hs : cwSingKey T = none) (hd : cwDiscKey T = none)
    (μ : CwMode) (val : ValPos → Digest) : cwRevNx μ T val = .free := by
  unfold cwRevNx
  rw [hs, hd]

/-- The value a key of the signatures signs is not the public root. -/
theorem msgPos_ne_rootPos {K : Key} (hK : InRange K) : msgPos K ≠ rootPos := by
  obtain ⟨l, idx, rfl⟩ := hK
  intro h
  unfold rootPos tpos at h
  rcases layer_cases l with rfl | rfl | rfl
  · rw [cwMsgPos_keyOf_zero] at h
    cases h
  · rw [cwMsgPos_keyOf_one] at h
    unfold tpos at h
    injection h with h1
    exact absurd h1 (by decide)
  · rw [cwMsgPos_keyOf_two] at h
    unfold tpos at h
    injection h with h1
    exact absurd h1 (by decide)

theorem noKey_root : ∀ K, InRange K → HPos.val (msgPos K) ∉ ({.val rootPos} : Finset HPos) :=
  fun _ hK hm ↦ msgPos_ne_rootPos hK (HPos.val.inj (Finset.mem_singleton.mp hm))

theorem noKey_root_rnd (msg : Message) :
    ∀ K, InRange K → HPos.val (msgPos K) ∉ ({.val rootPos, .rnd msg} : Finset HPos) := by
  intro K hK hm
  rcases Finset.mem_insert.mp hm with h | h
  · exact msgPos_ne_rootPos hK (HPos.val.inj h)
  · cases Finset.mem_singleton.mp h

theorem noKey_need {pol : DigestPolicy} (hpol : pol.ValFree) (T : Finset HPos) (msg : Message) :
    ∀ K, InRange K → HPos.val (msgPos K) ∉ pol.need T msg :=
  fun K _ ↦ hpol T msg (msgPos K)

/-- A FORS opening discloses the value of `K_0(idx)` only. -/
theorem oneKey_forsNeed (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    OneKey (valSet (forsNeed idx lv)) := fun _ _ hK hK' hm hm' ↦
  (eq_keyOf_of_fPos hK (fPos_of_mem_forsNeed _ (val_mem_valSet.mp hm))).trans
    (eq_keyOf_of_fPos hK' (fPos_of_mem_forsNeed _ (val_mem_valSet.mp hm'))).symm

/-- A layer signature discloses the value of one key at most: its tree's root. -/
theorem oneKey_layerNeed (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (x : Encoding) :
    OneKey (valSet (layerNeed l τ e x)) := fun _ _ hK hK' hm hm' ↦
  msgPos_injOn hK hK' ((msgPos_of_lPos hK (lPos_of_mem_layerNeed _ (val_mem_valSet.mp hm))).trans
    (msgPos_of_lPos hK' (lPos_of_mem_layerNeed _ (val_mem_valSet.mp hm'))).symm)

/-- **The top layer's signature discloses no key's value.** -/
theorem noKey_layerNeed_top {l : Layer} (hl : l.val = 2) (τ : TreeIndex) (e : TreeLeafIndex)
    (x : Encoding) : ∀ K, InRange K → HPos.val (msgPos K) ∉ valSet (layerNeed l τ e x) := by
  intro K hK hm
  have h := msgPos_of_lPos hK (lPos_of_mem_layerNeed _ (val_mem_valSet.mp hm))
  obtain ⟨l', idx, rfl⟩ := hK
  rcases layer_cases l' with rfl | rfl | rfl
  · rw [cwMsgPos_keyOf_zero] at h
    unfold tpos at h
    cases h
  · rw [cwMsgPos_keyOf_one] at h
    have h1 := congrArg Fin.val (tpos_inj h).1
    rw [hl] at h1
    exact absurd h1 (by decide)
  · rw [cwMsgPos_keyOf_two] at h
    have h1 := congrArg Fin.val (tpos_inj h).1
    rw [hl] at h1
    exact absurd h1 (by decide)

end revKeys

/-! ## Modes that see the stop -/

section stModes

/-- A mode between searches: free, or after the last trial of a search. -/
def CwMode.Rest : CwMode → Prop
  | .free => True
  | .grd _ _ j => j = encodingAttemptLimit
  | _ => False

/-- A mode allowing programs: between searches, or with a disclosed key's search next. -/
def CwMode.Calm : CwMode → Prop
  | .free => True
  | .pend .. => True
  | .grd _ _ j => j = encodingAttemptLimit
  | _ => False

theorem CwMode.Rest.calm {μ : CwMode} (h : μ.Rest) : μ.Calm := by
  rcases μ with _ | ⟨K, m⟩ | ⟨K, m, j⟩ | ⟨K, m, j, a⟩ | ⟨K, m, j, xi, z⟩
  · trivial
  · exact h.elim
  · exact h
  · exact h.elim
  · exact h.elim

theorem cwProgNx_rest {μ : CwMode} (h : μ.Rest) : (cwProgNx μ).Rest := by
  rcases μ with _ | ⟨K, m⟩ | ⟨K, m, j⟩ | ⟨K, m, j, a⟩ | ⟨K, m, j, xi, z⟩
  · trivial
  · exact h.elim
  · trivial
  · exact h.elim
  · exact h.elim

/-- **The reveals the searches allow**: from a disclosed key's search next, the reveal of its
value; between searches, a reveal of no single key's value disclosing at most one key's value. -/
def RevOk : CwMode → Finset HPos → Prop
  | .pend K _, T => InRange K ∧ T = {.val (msgPos K)}
  | μ, T => μ.Rest ∧ cwSingKey T = none ∧ OneKey T

theorem revOk_of_rest {μ : CwMode} (hμ : μ.Rest) {T : Finset HPos} (hs : cwSingKey T = none)
    (h1 : OneKey T) : RevOk μ T := by
  rcases μ with _ | ⟨K, m⟩ | ⟨K, m, j⟩ | ⟨K, m, j, a⟩ | ⟨K, m, j, xi, z⟩
  · exact ⟨hμ, hs, h1⟩
  · exact hμ.elim
  · exact ⟨hμ, hs, h1⟩
  · exact hμ.elim
  · exact hμ.elim

theorem RevOk.rest_or {μ : CwMode} {T : Finset HPos} (h : RevOk μ T) :
    (∃ K m, μ = .pend K m ∧ InRange K ∧ T = {.val (msgPos K)}) ∨
      (μ.Rest ∧ cwSingKey T = none ∧ OneKey T) := by
  rcases μ with _ | ⟨K, m⟩ | ⟨K, m, j⟩ | ⟨K, m, j, a⟩ | ⟨K, m, j, xi, z⟩
  · exact .inr h
  · exact .inl ⟨K, m, rfl, h⟩
  · exact .inr h
  · exact .inr h
  · exact .inr h

/-- The mode after a trial's `h`-read with value `w`: free if its digest is a codeword. -/
noncomputable def stopMode (K : Key) (m : Digest) (j : ℕ) (d : X) : CwMode :=
  if Codeword.Valid (trunc128 d) then .free else .grd K m (j + 1)

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter)

/-- The mode after a read: as CwRec's `cwRdNx`, except that a trial's `h`-read whose digest is a
codeword ends the search. -/
noncomputable def stRdNx {M' : Type} : CwMode → (c : HwRead X Z M') → c.Result → CwMode
  | .grd K m j, .readK _ _, r => .afK K m j (r.1.getD 0)
  | .afK K m j a, .readK' _ _, r => .afK' K m j (π (cwBlk P K m j, a)).1
      ((π (cwBlk P K m j, a)).2 + r.1.getD 0)
  | .afK' K m j xi _, .readH _ _, r => stopMode K m j (xi + r.1.getD 0)
  | _, _, _ => .free

/-- The calls the modes allow, on runtime 1's ports. -/
noncomputable def stOkR {M : Type} (hu : Key → X → X → M → Option X → M) :
    CwMode → (hwReadSpec X Z M).Port → Prop
  | μ, .inl _ => μ.Rest
  | μ, .inr c => cwRdOk π P hu μ c

/-- The mode after a call of runtime 1. -/
noncomputable def stNxR {M : Type} :
    CwMode → (i : (hwReadSpec X Z M).Port) → (hwReadSpec X Z M).Result i → CwMode
  | _, .inl _, _ => .free
  | μ, .inr c, r => stRdNx π P μ c r

/-- The calls the modes allow, on the template's ports. -/
noncomputable def stOkT {M : Type}
    (hu : Key → X → X → Finset HPos × M → Option X → Finset HPos × M) :
    CwMode → (SSpec M).Port → Prop
  | μ, .inl (.inl (.inl _)) => μ.Rest
  | μ, .inl (.inl (.inr c)) => cwRdOk π P hu μ c.1
  | μ, .inl (.inr _) => μ.Calm
  | μ, .inr T => RevOk μ T

/-- The mode after a call of the template. -/
noncomputable def stNxT {M : Type} : CwMode → (i : (SSpec M).Port) → (SSpec M).Result i → CwMode
  | μ, .inl (.inl (.inr c)), r => stRdNx π P μ c.1 r
  | μ, .inl (.inr _), _ => cwProgNx μ
  | μ, .inr T, r => cwRevNx μ T (extendVals r.1)
  | _, _, _ => .free

/-- The calls the modes allow, on runtime 2's ports with record ports. -/
noncomputable def stOkZ {M : Type}
    (hu : Key → X → X → Finset HPos × M → Option X → Finset HPos × M) :
    CwMode → (recHwSpec X Z HPos M).Port → Prop
  | μ, .inl (.inl (.inl _)) => μ.Rest
  | μ, .inl (.inl (.inr c)) => cwRdOk π P hu μ c
  | μ, .inl (.inr _) => μ.Calm
  | μ, .inr T => RevOk μ T

/-- The mode after a call of runtime 2 with record ports, at the hidden values `v`. -/
noncomputable def stNxZ {M : Type} (v : (s : HPos) → XD s) :
    CwMode → (i : (recHwSpec X Z HPos M).Port) → (recHwSpec X Z HPos M).Result i → CwMode
  | μ, .inl (.inl (.inr c)), r => stRdNx π P μ c r
  | μ, .inl (.inr _), _ => cwProgNx μ
  | μ, .inr T, _ => cwRevNx μ T (valsOf v)
  | _, _, _ => .free

variable {M : Type} {π P}

theorem modedP_readCall_st {hu : Key → X → X → M → Option X → M} {μ : CwMode}
    {c : HwRead X Z M} (h : cwRdOk π P hu μ c) (B : QReg) :
    ModedP (L := LocalSig.instruments) (stOkR π P hu) (stNxR π P)
      (fun p μ' ↦ μ' = stRdNx π P μ c p.2.2) μ (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

variable (π P) in
/-- A stateful program of runtime 1 that is moded from every state. -/
def SSMod (hu : Key → X → X → M → Option X → M) {B : QReg} {σ α : Type} (μ : CwMode)
    (F : α → CwMode → Prop) (x : StateT σ (QComp (hwReadSpec X Z M) B B) α) : Prop :=
  ∀ s, ModedP (L := LocalSig.instruments) (stOkR π P hu) (stNxR π P)
    (fun p μ' ↦ F p.2.2.1 μ') μ (x.run s)

section smod

variable {hu : Key → X → X → M → Option X → M} {B : QReg} {σ α β : Type}

theorem sSMod_bind {x : StateT σ (QComp (hwReadSpec X Z M) B B) α}
    {k : α → StateT σ (QComp (hwReadSpec X Z M) B B) β} {μ : CwMode} {F : α → CwMode → Prop}
    {G : β → CwMode → Prop} (hx : SSMod π P hu μ F x)
    (hk : ∀ a μ', F a μ' → SSMod π P hu μ' G (k a)) : SSMod π P hu μ G (x >>= k) := by
  intro s
  rw [StateT.run_bind]
  exact modedP₂_bind (F := fun (q : α × σ) μ ↦ F q.1 μ) (F' := fun (q : β × σ) μ ↦ G q.1 μ) _ _
    (hx s) fun p μ' h ↦ hk p.1 μ' h p.2

theorem sSMod_pure (a : α) {F : α → CwMode → Prop} {μ : CwMode} (h : F a μ) :
    SSMod π P hu μ F (pure a : StateT σ (QComp (hwReadSpec X Z M) B B) α) := by
  intro s
  rw [StateT.run_pure]
  exact h

theorem sSMod_map {x : StateT σ (QComp (hwReadSpec X Z M) B B) α} (g : α → β) {μ : CwMode}
    {F : β → CwMode → Prop} (hx : SSMod π P hu μ (fun a ↦ F (g a)) x) :
    SSMod π P hu μ F (g <$> x) := by
  intro s
  rw [StateT.run_map]
  exact modedP_map (F := fun q : β × σ ↦ F q.1) (fun p : α × σ ↦ (g p.1, p.2)) (hx s)

theorem sSMod_rdK {K : Key} {m : Digest} {j : ℕ} {x : X}
    (hj : j < encodingAttemptLimit) (hx : x = cwBlk P K m j) :
    SSMod π P hu (.grd K m j) (fun a (μ : CwMode) ↦ μ = .afK K m j a) (rdK (M := M) B x) :=
  fun s ↦ modedP₂_bind
    (F := fun r : Option Z × M ↦ fun (μ : CwMode) ↦ μ = .afK K m j (r.1.getD 0))
    (F' := fun q : Z × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦ μ = .afK K m j q.1)
    (readCall (.readK x keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k x (r.1.getD 0)]))
    (modedP_readCall_st (μ := .grd K m j) (c := .readK x keepMem) ⟨hj, hx, rfl⟩ B)
    fun _ _ h ↦ h

theorem sSMod_rdK' {K : Key} {m : Digest} {j : ℕ} {a : Z} {y : X}
    (hy : y = (π (cwBlk P K m j, a)).1) :
    SSMod π P hu (.afK K m j a) (fun c (μ : CwMode) ↦ μ = .afK' K m j
      (π (cwBlk P K m j, a)).1 ((π (cwBlk P K m j, a)).2 + c)) (rdK' (M := M) B y) :=
  fun s ↦ modedP₂_bind (F := fun r : Option Z × M ↦ fun (μ : CwMode) ↦ μ = .afK' K m j
      (π (cwBlk P K m j, a)).1 ((π (cwBlk P K m j, a)).2 + r.1.getD 0))
    (F' := fun q : Z × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦ μ = .afK' K m j
      (π (cwBlk P K m j, a)).1 ((π (cwBlk P K m j, a)).2 + q.1))
    (readCall (.readK' y keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k' y (r.1.getD 0)]))
    (modedP_readCall_st (μ := .afK K m j a) (c := .readK' y keepMem) ⟨hy, rfl⟩ B)
    fun _ _ h ↦ h

theorem sSMod_rdHU {K : Key} {m : Digest} {j : ℕ} {xi : X} {z z' : Z}
    {u : M → Option X → M} (hz : z' = z) (hu' : u = hu K (cwBlk P K m j) xi) :
    SSMod π P hu (.afK' K m j xi z) (fun w (μ : CwMode) ↦ μ = stopMode K m j (xi + w))
      (rdHU M B z' u) :=
  fun s ↦ modedP₂_bind
    (F := fun r : Option X × M ↦ fun (μ : CwMode) ↦ μ = stopMode K m j (xi + r.1.getD 0))
    (F' := fun q : X × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦
      μ = stopMode K m j (xi + q.1))
    (readCall (.readH z' u) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.h z' (r.1.getD 0)]))
    (modedP_readCall_st (μ := .afK' K m j xi z) (c := .readH z' u) ⟨hz, hu'⟩ B)
    fun _ _ h ↦ h

end smod

/-- **A trial's round of reads**, ending in the stop mode of its digest. -/
theorem sSMod_rdRoundU (upd : TrialUpd M) {B : QReg} {K : Key} {m : Digest} {j : ℕ}
    (hj : j < encodingAttemptLimit) {b : X} (hb : b = cwBlk P K m j) :
    SSMod π P upd (.grd K m j) (fun s (μ : CwMode) ↦ μ = stopMode K m j s.1)
      (rdRoundU M (upd K) π B (0, 0) b) := by
  subst hb
  unfold rdRoundU
  refine sSMod_bind (sSMod_rdK hj (zero_add _)) fun a μ ha ↦ ?_
  subst ha
  refine sSMod_bind (sSMod_rdK' (a := a) (by rw [zero_add, zero_add])) fun c μ hc ↦ ?_
  subst hc
  refine sSMod_bind (sSMod_rdHU (by rw [zero_add, zero_add]) (by rw [zero_add, zero_add]))
    fun w μ hw ↦ ?_
  refine sSMod_pure _ ?_
  show μ = stopMode K m j ((π (0 + cwBlk P K m j, 0 + a)).1 + w)
  rw [hw, zero_add, zero_add]

/-- **A trial's hash** of a one-block input whose block is the trial's, ending in the stop mode
of its output's digest. -/
theorem modedP_hashTrial_st (upd : TrialUpd M) {B : QReg} {K : Key} {m : Digest}
    {j : ℕ} (hj : j < encodingAttemptLimit) (input : HashInput)
    (hb : blocks input = [cwBlk P K m j]) :
    ModedP (L := LocalSig.instruments) (stOkR π P upd) (stNxR π P)
      (fun p (μ : CwMode) ↦ μ = if Codeword.Valid (truncateHash p.2.2) then .free
        else .grd K m (j + 1)) (.grd K m j)
      (hashTrial M (upd K) π B input) := by
  have hfold : SSMod π P upd (B := B) (.grd K m j)
      (fun s (μ : CwMode) ↦ μ = stopMode K m j s.1)
      ((blocks input).foldlM (rdRoundU M (upd K) π B) (0, 0)) := by
    rw [hb]
    exact sSMod_bind (sSMod_rdRoundU upd hj rfl) fun s' μ h ↦ sSMod_pure s' h
  exact modedP_map (F := fun out (μ : CwMode) ↦ μ = if Codeword.Valid (truncateHash out) then
      .free else .grd K m (j + 1)) Prod.fst
    (sSMod_map (F := fun out (μ : CwMode) ↦ μ = if Codeword.Valid (truncateHash out) then
      .free else .grd K m (j + 1)) (out256 : X → HashOutput)
      (sSMod_map (F := fun x (μ : CwMode) ↦ μ = if Codeword.Valid (truncateHash (out256 x)) then
        .free else .grd K m (j + 1)) (fun s : X × Z ↦ s.1) hfold) [])

/-- **The counter search** of key `K` on the value `m`, from its trial `c` to the last, ends
between searches: free after a codeword, after the last trial otherwise. -/
theorem modedP_grindK_st (upd : TrialUpd M) (pub : Pub) {B : QReg} (K : Key) (m : Digest) :
    ∀ n c, c + n = encodingAttemptLimit →
      ModedP (L := LocalSig.instruments) (stOkR pub.perm pub.seed upd)
      (stNxR pub.perm pub.seed) (fun _ (μ : CwMode) ↦ μ.Rest) (.grd K m c)
      (grindK M upd pub B K m n c)
  | 0, c, hn => by
    show CwMode.Rest (.grd K m c)
    exact (Nat.add_zero c).symm.trans hn
  | n + 1, c, hn => by
    rw [grindK]
    refine modedP₂_bind (F := fun out (μ : CwMode) ↦ μ = if Codeword.Valid (truncateHash out)
        then .free else .grd K m (c + 1))
      (F' := fun _ (μ : CwMode) ↦ μ.Rest) _ _
      (modedP_hashTrial_st upd (by omega) _ (blocks_encTrialIn_eq pub.seed K m c))
      fun out μ hμ ↦ ?_
    split
    · next x hx =>
      rw [hμ, ite_eq_left (Codeword.valid_of_decode hx)]
      trivial
    · next hx =>
      rw [hμ, ite_eq_right (Codeword.decode_eq_none_iff.mp hx)]
      exact modedP_grindK_st upd pub K m n (c + 1) (by omega)

/-- **Lifting runtime 1's moded programs to templates.** -/
theorem modedP_readLift_st {hu : Key → X → X → M → Option X → M} {Ω : QReg → Type}
    {A : QReg} {fin : (Σ u, Ω u) → CwMode → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec X Z M) Ω A) {μ : CwMode}
    (hy : ModedP (stOkR π P hu) (stNxR π P) fin μ y) :
    ModedP (stOkT π P (cwLiftHu hu)) (stNxT π P) fin μ (readLift goodAll y) := by
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
        rcases μ with _ | ⟨K, m⟩ | ⟨K, m, j⟩ | ⟨K, m, j, a⟩ | ⟨K, m, j, xi, z'⟩ <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

/-- A sponge program of runtime 1 is moded between searches. -/
theorem modedP_liftOrdinary_st {hu : Key → X → X → M → Option X → M} {Ω : QReg → Type}
    {A : QReg} (y : QuantumComp LocalSig.instruments (spongeSpec X Z) Ω A) :
    ∀ μ : CwMode, μ.Rest → ModedP (stOkR π P hu) (stNxR π P) (fun _ (μ : CwMode) ↦ μ.Rest) μ
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

theorem stNxZ_rec_eq (v : (s : HPos) → XD s) (μ : CwMode) (T : Finset HPos)
    (m : Finset HPos × M) :
    stNxZ (M := M) π P v μ (.inr T) m = stNxT π P μ (.inr T) (restrictTo T v, m) :=
  cwRevNx_congr μ T fun _ hp ↦ (extendVals_restrictTo hp v).symm

/-- **Realizing keeps the modes.** -/
theorem modedP_realizeT_st {hu : Key → X → X → Finset HPos × M → Option X → Finset HPos × M}
    (v : (s : HPos) → XD s) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → CwMode → Prop} (y : QuantumComp L (SSpec M) Ω A)
    {μ : CwMode} (hy : ModedP (stOkT π P hu) (stNxT π P) fin μ y) :
    ModedP (stOkZ π P hu) (stNxZ π P v) fin μ (realizeT v y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (tmplLens v) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨_, _⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hy.1, fun b ↦ ?_⟩
      have h := ih _ (hy.2 (ULift.up (restrictTo T v, b.down)))
      exact (congrArg (fun μ' ↦ ModedP (stOkZ π P hu) (stNxZ π P v) fin μ' _)
        (stNxZ_rec_eq (π := π) (P := P) v μ T b.down)).mpr h

end stModes

/-! ### The challenge prefix is moded -/

section stPrefix

variable {M : Type} {π : Equiv.Perm (X × Z)} {P : PublicParameter}

variable (π P) in
/-- A template moded between searches: from every mode between searches, it ends between
searches. -/
def SRest (hu : Key → X → X → Finset HPos × M → Option X → Finset HPos × M)
    {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments (SSpec M) Ω A) : Prop :=
  ∀ μ : CwMode, μ.Rest → ModedP (stOkT π P hu) (stNxT π P) (fun _ (μ : CwMode) ↦ μ.Rest) μ y

variable (π P) in
/-- A template keeping a disclosed key's search next. -/
def SPend (hu : Key → X → X → Finset HPos × M → Option X → Finset HPos × M)
    {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments (SSpec M) Ω A) : Prop :=
  ∀ K m, ModedP (stOkT π P hu) (stNxT π P) (fun _ (μ : CwMode) ↦ μ = .pend K m) (.pend K m) y

variable {hu : Key → X → X → Finset HPos × M → Option X → Finset HPos × M}

theorem sRest_bind {A B B' : QReg} {α β : Type} (x : QComp (SSpec M) A B α)
    (g : α → QComp (SSpec M) B B' β) (hx : SRest π P hu x) (hg : ∀ a, SRest π P hu (g a)) :
    SRest π P hu (x.bind g) :=
  fun μ hμ ↦ modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Rest)
    (F' := fun _ (μ : CwMode) ↦ μ.Rest) x g (hx μ hμ) fun a μ' h ↦ hg a μ' h

theorem sPend_bind {A B B' : QReg} {α β : Type} (x : QComp (SSpec M) A B α)
    (g : α → QComp (SSpec M) B B' β) (hx : SPend π P hu x) (hg : ∀ a, SPend π P hu (g a)) :
    SPend π P hu (x.bind g) :=
  fun K m ↦ modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ = .pend K m)
    (F' := fun _ (μ : CwMode) ↦ μ = .pend K m) x g (hx K m) fun a _ h ↦ h ▸ hg a K m

theorem sRest_pure {A : QReg} {α : Type} (a : α) :
    SRest π P hu (QuantumComp₂.pure (L := LocalSig.instruments) (spec := SSpec M) (A := A) a) :=
  fun _ h ↦ h

theorem sPend_pure {A : QReg} {α : Type} (a : α) :
    SPend π P hu (QuantumComp₂.pure (L := LocalSig.instruments) (spec := SSpec M) (A := A) a) :=
  fun _ _ ↦ rfl

theorem sRest_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    SRest π P hu (QComp.act (spec := SSpec M) p) :=
  fun _ hμ ↦ ⟨trivial, fun _ ↦ hμ⟩

/-- **A reveal** the mode allows: its continuation from the mode it leads to. -/
theorem modedP_revealThen_st {B B' : QReg} {α : Type} {fin : α → CwMode → Prop}
    (T : Finset HPos) (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B B' α)
    {μ : CwMode} (hok : RevOk μ T)
    (hk : ∀ r, ModedP (stOkT π P hu) (stNxT π P) (fun p μ ↦ fin p.2.2 μ)
      (cwRevNx μ T (extendVals r.1)) (k r)) :
    ModedP (stOkT π P hu) (stNxT π P) (fun p μ ↦ fin p.2.2 μ) μ (revealThen goodAll T k) := by
  refine ⟨hok, fun b ↦ ?_⟩
  rw [show modeCmdNx (stNxT (M := M) π P) (QuantumComp.Cmd.query (L := LocalSig.instruments)
    (.inr T) B _) μ b = cwRevNx μ T (extendVals b.down.1) from rfl]
  exact modedP₂_bind (F := fun _ (μ' : CwMode) ↦ μ' = cwRevNx μ T (extendVals b.down.1))
    (F' := fin) _ _ ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ h ▸ hk b.down

/-- A reveal disclosing no key's value keeps the searches free. -/
theorem sRest_revealThen_free {B B' : QReg} {α : Type} (T : Finset HPos)
    (hs : cwSingKey T = none) (hd : cwDiscKey T = none)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B B' α)
    (hk : ∀ r, SRest π P hu (k r)) : SRest π P hu (revealThen goodAll T k) :=
  fun μ hμ ↦ modedP_revealThen_st (fin := fun _ (μ : CwMode) ↦ μ.Rest) T k
    (revOk_of_rest hμ hs (oneKey_of_noKey (noKey_of_none hs hd))) fun r ↦ by
      rw [cwRevNx_free hs hd]
      exact hk r _ trivial

theorem sRest_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec M) B B' α) (hk : SRest π P hu k) : SRest π P hu (progThen p hp k) :=
  fun _ hμ ↦ ⟨hμ.calm, fun _ ↦ sRest_bind _ _ (sRest_act _) (fun _ ↦ hk) _ (cwProgNx_rest hμ)⟩

theorem sPend_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec M) B B' α) (hk : SPend π P hu k) : SPend π P hu (progThen p hp k) :=
  fun K m ↦ ⟨trivial, fun _ ↦ modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ = .pend K m)
    (F' := fun _ (μ : CwMode) ↦ μ = .pend K m) _ _ ⟨trivial, fun _ ↦ rfl⟩
    fun _ _ h ↦ h ▸ hk K m⟩

theorem sRest_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    SRest π P hu (progPorts M B ps) := by
  induction ps with
  | nil => exact sRest_pure _
  | cons p ps ih => exact sRest_progThen p trivial _ ih

theorem sPend_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    SPend π P hu (progPorts M B ps) := by
  induction ps with
  | nil => exact sPend_pure _
  | cons p ps ih => exact sPend_progThen p trivial _ ih

theorem sRest_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    SRest π P hu (progSlots M pub B ss) := by
  induction ss with
  | nil => exact sRest_pure _
  | cons s ss ih => exact sRest_bind _ _ (sRest_progPorts B _) fun _ ↦ ih

theorem sPend_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    SPend π P hu (progSlots M pub B ss) := by
  induction ss with
  | nil => exact sPend_pure _
  | cons s ss ih => exact sPend_bind _ _ (sPend_progPorts B _) fun _ ↦ ih

variable (upd : TrialUpd M)

/-- **The FORS opening of instance `idx`**, from between searches, ends with `K_0(idx)`'s search
next. -/
theorem modedP_forsOpenT_st (pub : Pub) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) {μ : CwMode} (hμ : μ.Rest) :
    ModedP (stOkT pub.perm pub.seed (cwLiftHu upd)) (stNxT pub.perm pub.seed)
      (fun _ (μ : CwMode) ↦ ∃ m, μ = .pend (keyOf 0 idx) m) μ (forsOpenT M pub B idx lv) := by
  obtain ⟨hs, hd⟩ := cwKeys_forsNeed idx lv
  refine modedP_revealThen_st (fin := fun _ (μ : CwMode) ↦ ∃ m, μ = .pend (keyOf 0 idx) m) _ _
    (revOk_of_rest hμ hs (oneKey_forsNeed idx lv)) fun r ↦ ?_
  rw [cwRevNx_disc hs hd]
  exact modedP₂_bind (F := fun _ (μ : CwMode) ↦
      μ = .pend (keyOf 0 idx) (extendVals r.1 (msgPos (keyOf 0 idx))))
    (F' := fun _ (μ : CwMode) ↦ ∃ m, μ = .pend (keyOf 0 idx) m) _ _
    (sPend_progSlots pub B _ _ _) fun _ _ h ↦ ⟨_, h⟩

/-- **A layer signature** by a key of the signatures, from its search next: the reveal of its
value starts the search, which ends between searches; the continuation `k` from there. -/
theorem modedP_signLayerT_of_st (pub : Pub) (B : QReg) {K : Key} (hK : InRange K) (m : Digest)
    {fin : Option (LayerSignature K.1) → CwMode → Prop} (hnone : ∀ μ, μ.Rest → fin none μ)
    (hsome : ∀ (c : EncodingCounter) (x : Encoding) μ, μ.Rest →
      ModedP (stOkT pub.perm pub.seed (cwLiftHu upd)) (stNxT pub.perm pub.seed)
        (fun p μ ↦ fin p.2.2 μ) μ
        (revealThen goodAll (valSet (layerNeed K.1 K.2.1 K.2.2 x)) fun r ↦
          (progSlots M pub B (layerSlots K.1 K.2.1 K.2.2 x)).bind fun _ ↦
            QuantumComp₂.pure (some ⟨c, fun i ↦ extendVals r.1 (cpos K.1 K.2.1 K.2.2 i (x i).val),
              fun z ↦ extendVals r.1 (siblingPos K.1 K.2.1 K.2.2 z)⟩))) :
    ModedP (stOkT pub.perm pub.seed (cwLiftHu upd)) (stNxT pub.perm pub.seed)
      (fun p μ ↦ fin p.2.2 μ) (.pend K m) (signLayerT M upd pub B K) := by
  refine modedP_revealThen_st _ _ ⟨hK, rfl⟩ fun r₀ ↦ ?_
  rw [cwRevNx_sing hK]
  refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Rest) _ _
    (modedP_readLift_st _ (modedP_grindK_st upd pub K _ _ _ (by omega))) fun g μ hμ ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · exact hnone μ hμ
  · exact hsome c x μ hμ

/-- The final modes of a layer signature below the top: when it signs, the next key's search
next; otherwise between searches. -/
def StNext {α : Type} (K' : Key) : Option α → CwMode → Prop
  | some _, μ => ∃ m', μ = .pend K' m'
  | none, μ => μ.Rest

/-- **A layer signature by `K_l(idx)` below the top** ends, when it signs, with `K_{l+1}(idx)`'s
search next. -/
theorem modedP_signLayerT_next_st (pub : Pub) (B : QReg) {l l' : Layer} (hl : l.val < 2)
    (hl' : l'.val = l.val + 1) (idx : Index) (m : Digest) :
    ModedP (stOkT pub.perm pub.seed (cwLiftHu upd)) (stNxT pub.perm pub.seed)
      (fun p μ ↦ StNext (keyOf l' idx) p.2.2 μ) (.pend (keyOf l idx) m)
      (signLayerT M upd pub B (keyOf l idx)) := by
  refine modedP_signLayerT_of_st upd pub B (inRange_keyOf l idx) m (fin := StNext (keyOf l' idx))
    (fun μ hμ ↦ hμ) fun c x μ hμ ↦ ?_
  obtain ⟨hs, hd⟩ := cwKeys_layerNeed hl hl' idx x
  refine modedP_revealThen_st (fin := StNext (keyOf l' idx)) _ _
    (revOk_of_rest hμ hs (oneKey_layerNeed _ _ _ x)) fun r ↦ ?_
  rw [show cwRevNx μ (valSet (layerNeed (keyOf l idx).1 (keyOf l idx).2.1 (keyOf l idx).2.2 x))
    (extendVals r.1) = .pend (keyOf l' idx) (extendVals r.1 (msgPos (keyOf l' idx))) from
    cwRevNx_disc hs hd μ _]
  exact modedP₂_bind (F := fun _ (μ : CwMode) ↦
      μ = .pend (keyOf l' idx) (extendVals r.1 (msgPos (keyOf l' idx))))
    (F' := StNext (keyOf l' idx)) _ _
    (sPend_progSlots pub B _ _ _) fun _ _ h ↦ ⟨_, h⟩

/-- **The top layer's signature**, from its search next, ends between searches. -/
theorem modedP_signLayerT_top_st (pub : Pub) (B : QReg) (idx : Index) (m : Digest) :
    ModedP (stOkT pub.perm pub.seed (cwLiftHu upd)) (stNxT pub.perm pub.seed)
      (fun _ (μ : CwMode) ↦ μ.Rest) (.pend (keyOf 2 idx) m)
      (signLayerT M upd pub B (keyOf 2 idx)) :=
  modedP_signLayerT_of_st upd pub B (inRange_keyOf 2 idx) m (fin := fun _ μ ↦ μ.Rest)
    (fun _ h ↦ h) fun _ x μ hμ ↦ sRest_revealThen_free _
      (cwSingKey_eq_none_of_noKey (noKey_layerNeed_top rfl _ _ x))
      (cwDiscKey_eq_none_of_noKey (noKey_layerNeed_top rfl _ _ x)) _
      (fun _ ↦ sRest_bind _ _ (sRest_progSlots pub B _) fun _ ↦ sRest_pure _) μ hμ

/-- **A signature is moded between searches**, for a digest policy revealing no value. -/
theorem sRest_signT (pol : DigestPolicy) (hpol : pol.ValFree) (pub : Pub) (B : QReg)
    (msg : Message) : SRest pub.perm pub.seed (cwLiftHu upd) (signT M upd pol pub B msg) := by
  refine sRest_revealThen_free _ (cwSingKey_eq_none_of_noKey (noKey_root_rnd msg))
    (cwDiscKey_eq_none_of_noKey (noKey_root_rnd msg)) _ fun r₁ ↦ ?_
  refine sRest_revealThen_free _ (cwSingKey_eq_none_of_noKey (noKey_need hpol _ msg))
    (cwDiscKey_eq_none_of_noKey (noKey_need hpol _ msg)) _ fun r₂ ↦ ?_
  intro μ hμ
  refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Rest) (F' := fun _ (μ : CwMode) ↦ μ.Rest) _ _
    (sRest_progPorts B _ μ hμ) fun _ μ₁ h₁ ↦ ?_
  refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ ∃ m, μ = .pend (keyOf 0 _) m)
    (F' := fun _ (μ : CwMode) ↦ μ.Rest) _ _ (modedP_forsOpenT_st upd pub B _ _ h₁)
    fun _ μ₂ h₂ ↦ ?_
  obtain ⟨m₂, rfl⟩ := h₂
  refine modedP₂_bind (F := StNext (keyOf 1 _)) (F' := fun _ (μ : CwMode) ↦ μ.Rest) _ _
    (modedP_signLayerT_next_st upd pub B (l := 0) (l' := 1) (by decide) rfl _ m₂)
    fun s₀ μ₃ h₃ ↦ ?_
  rcases s₀ with _ | bottom
  · exact h₃
  obtain ⟨m₃, rfl⟩ := h₃
  refine modedP₂_bind (F := StNext (keyOf 2 _)) (F' := fun _ (μ : CwMode) ↦ μ.Rest) _ _
    (modedP_signLayerT_next_st upd pub B (l := 1) (l' := 2) (by decide) rfl _ m₃)
    fun s₁ μ₄ h₄ ↦ ?_
  rcases s₁ with _ | middle
  · exact h₄
  obtain ⟨m₄, rfl⟩ := h₄
  refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Rest) (F' := fun _ (μ : CwMode) ↦ μ.Rest) _ _
    (modedP_signLayerT_top_st upd pub B _ m₄) fun s₂ μ₅ h₅ ↦ ?_
  rcases s₂ with _ | top
  · exact h₅
  · exact h₅

theorem sRest_challengeT (pol : DigestPolicy) (hpol : pol.ValFree) (pub : Pub) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    ∀ μ : CwMode, μ.Rest → ModedP (stOkT pub.perm pub.seed (cwLiftHu upd))
      (stNxT pub.perm pub.seed) (fun _ (μ : CwMode) ↦ μ.Rest) μ
      (challengeT M upd pol pub A c) := by
  intro μ hμ
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact modedP_readLift_st _ (modedP_liftOrdinary_st _ μ hμ)
  · exact modedP_readLift_st _ (modedP_liftOrdinary_st _ μ hμ)
  · exact modedP_bind (fin := fun _ (μ : CwMode) ↦ μ.Rest) _ _ (sRest_bind _ _ (sRest_act _)
      (fun _ ↦ sRest_signT upd pol hpol pub _ msg) μ hμ) fun _ _ _ h ↦ h

omit upd in
/-- Substituting trees moded between searches. -/
theorem modedP_substitute_st {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (SSpec M)))
    (hσ : ∀ A c, ∀ μ : CwMode, μ.Rest → ModedP (stOkT π P hu) (stNxT π P)
      (fun _ (μ : CwMode) ↦ μ.Rest) μ (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ∀ μ : CwMode, μ.Rest → ModedP (stOkT π P hu) (stNxT π P) (fun _ (μ : CwMode) ↦ μ.Rest) μ
      (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact fun _ h ↦ h
  | liftBind s c next ih =>
    intro μ hμ
    rw [IFreeM.substitute_liftBind]
    exact modedP_bind _ _ (hσ s c μ hμ) fun u ans μ' h ↦ (modedP_cast ans.2 _ _).mpr
      (ih ans.1 μ' h)

/-- **The challenge prefix is moded between searches.** -/
theorem sRest_prefixT (pol : DigestPolicy) (hpol : pol.ValFree) (pub : Pub) (A : SAdversary) :
    SRest pub.perm pub.seed (cwLiftHu upd) (prefixT M upd pol pub A) :=
  sRest_revealThen_free _ (cwSingKey_eq_none_of_noKey noKey_root)
    (cwDiscKey_eq_none_of_noKey noKey_root) _ fun _ ↦ sRest_bind _ _
      (modedP_substitute_st _ (sRest_challengeT upd pol hpol pub) _) fun _ ↦ sRest_pure _

omit upd in
/-- **The realized challenge prefix is moded**, from the free mode. -/
theorem modedP_prefixR_st (pol : DigestPolicy) (hpol : pol.ValFree) (pub : Pub) (A : SAdversary)
    (v : (s : HPos) → XD s) :
    ModedP (stOkZ pub.perm pub.seed (cwLiftHu cwUpd)) (stNxZ pub.perm pub.seed v)
      (fun _ (μ : CwMode) ↦ μ.Rest) .free (prefixR pol A pub v) :=
  modedP_realizeT_st v _ (sRest_prefixT cwUpd pol hpol pub A .free trivial)

end stPrefix

/-! ## The trials on the decompressed databases -/

section chain

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter) (W₀ : Hw X Z)

/-- The `k`-value of trial `j` of the search of `K` on `m` on the databases `D`. -/
noncomputable def trA (K : Key) (m : Digest) (j : ℕ) (D : DbReg X Z) : Z :=
  (D.2.1 (cwBlk P K m j)).getD 0

/-- The rate of the trial after `π`: its `k'`-cell. -/
noncomputable def trY (K : Key) (m : Digest) (j : ℕ) (D : DbReg X Z) : X :=
  (π (cwBlk P K m j, trA P K m j D)).1

/-- The `h`-cell of the trial. -/
noncomputable def trZ (K : Key) (m : Digest) (j : ℕ) (D : DbReg X Z) : Z :=
  (π (cwBlk P K m j, trA P K m j D)).2 + (D.2.2 (trY π P K m j D)).getD 0

/-- The `h`-value of the trial. -/
noncomputable def trW (K : Key) (m : Digest) (j : ℕ) (D : DbReg X Z) : X :=
  (D.1 (trZ π P K m j D)).getD 0

/-- **Trial `j` touches `W₀` or fails**: its `k`-, `k'`- or `h`-cell is a cell of `W₀`, or its
digest is no codeword. -/
def TB (K : Key) (m : Digest) (j : ℕ) (D : DbReg X Z) : Prop :=
  W₀.2.1 (cwBlk P K m j) ≠ none ∨ W₀.2.2 (trY π P K m j D) ≠ none ∨
    W₀.1 (trZ π P K m j D) ≠ none ∨
      ¬ Codeword.Valid (trunc128 (trY π P K m j D + trW π P K m j D))

/-- Two database triples agree at every cell outside `W₀`. -/
def DbOffAgree (D D' : DbReg X Z) : Prop :=
  (∀ z, W₀.1 z = none → D.1 z = D'.1 z) ∧ (∀ x, W₀.2.1 x = none → D.2.1 x = D'.2.1 x) ∧
    ∀ x, W₀.2.2 x = none → D.2.2 x = D'.2.2 x

/-- `TB` looks at the databases outside `W₀` only. -/
theorem tB_of_offAgree {D D' : DbReg X Z} (h : DbOffAgree W₀ D D') {K : Key} {m : Digest}
    {j : ℕ} (hT : TB π P W₀ K m j D) : TB π P W₀ K m j D' := by
  unfold TB at hT ⊢
  by_cases hk : W₀.2.1 (cwBlk P K m j) = none
  swap
  · exact Or.inl hk
  have ha : trA P K m j D' = trA P K m j D := by
    unfold trA
    rw [h.2.1 _ hk]
  have hy : trY π P K m j D' = trY π P K m j D := by
    unfold trY
    rw [ha]
  rw [hy]
  by_cases hk' : W₀.2.2 (trY π P K m j D) = none
  swap
  · exact Or.inr (Or.inl hk')
  have hz : trZ π P K m j D' = trZ π P K m j D := by
    unfold trZ
    rw [ha, hy, ← h.2.2 _ hk']
  rw [hz]
  by_cases hh : W₀.1 (trZ π P K m j D) = none
  swap
  · exact Or.inr (Or.inr (Or.inl hh))
  have hw : trW π P K m j D' = trW π P K m j D := by
    unfold trW
    rw [hz, ← h.1 _ hh]
  rw [hw]
  rcases hT with hT | hT | hT | hT
  · exact absurd hk hT
  · exact absurd hk' hT
  · exact absurd hh hT
  · exact Or.inr (Or.inr (Or.inr hT))

/-- The hardwired cells lie in `W₀`. -/
def HwIn (W : Hw X Z) : Prop :=
  (∀ z, W.1 z ≠ none → W₀.1 z ≠ none) ∧ (∀ x, W.2.1 x ≠ none → W₀.2.1 x ≠ none) ∧
    ∀ x, W.2.2 x ≠ none → W₀.2.2 x ≠ none

/-- The trials of `K` already run in the mode `μ`: those before the current trial of its search,
none with its search next, all of them otherwise. -/
def doneN (μ : CwMode) (K : Key) : ℕ :=
  match μ with
  | .free => encodingAttemptLimit
  | .pend K' _ => if K' = K then 0 else encodingAttemptLimit
  | .grd K' _ j => if K' = K then j else encodingAttemptLimit
  | .afK K' _ j _ => if K' = K then j else encodingAttemptLimit
  | .afK' K' _ j _ _ => if K' = K then j else encodingAttemptLimit

theorem doneN_of_rest {μ : CwMode} (h : μ.Rest) (K : Key) :
    doneN μ K = encodingAttemptLimit := by
  rcases μ with _ | ⟨K', m⟩ | ⟨K', m, j⟩ | ⟨K', m, j, a⟩ | ⟨K', m, j, xi, z⟩
  · rfl
  · exact h.elim
  · have hj : j = encodingAttemptLimit := h
    subst hj
    show (if K' = K then encodingAttemptLimit else encodingAttemptLimit) = _
    split_ifs <;> rfl
  · exact h.elim
  · exact h.elim

theorem doneN_cwProgNx {μ : CwMode} (h : μ.Calm) (K : Key) : doneN (cwProgNx μ) K = doneN μ K := by
  rcases μ with _ | ⟨K', m⟩ | ⟨K', m, j⟩ | ⟨K', m, j, a⟩ | ⟨K', m, j, xi, z⟩
  · rfl
  · rfl
  · exact (doneN_of_rest (μ := .grd K' m j) h K).symm
  · exact h.elim
  · exact h.elim

/-- The mode's data agree with the register: the search's value is the hidden one, and after the
trial's reads their outcomes are the decompressed values (unless the trial touched `W₀`). -/
def ModeOk (v : (s : HPos) → XD s) : CwMode → HwReg X Z (Mem HPos) → Prop
  | .free, _ => True
  | .pend .., _ => True
  | .grd K m _, _ => m = valsOf v (msgPos K)
  | .afK K m j a, s => m = valsOf v (msgPos K) ∧
      (W₀.2.1 (cwBlk P K m j) ≠ none ∨ a = trA P K m j s.1)
  | .afK' K m j xi z, s => m = valsOf v (msgPos K) ∧
      (W₀.2.1 (cwBlk P K m j) ≠ none ∨ W₀.2.2 (trY π P K m j s.1) ≠ none ∨
        (xi = trY π P K m j s.1 ∧ z = trZ π P K m j s.1))

/-- **The invariant of the failed searches**, in the decompressed basis: no empty cell, the
hardwired cells in `W₀`, the mode's data, and for every key of the signatures whose value is
disclosed and which is unselected, every trial already run touched `W₀` or failed. -/
def FInv (v : (s : HPos) → XD s) (μ : CwMode) : Set (HwReg X Z (Mem HPos)) :=
  {s | NoBot s ∧ HwIn W₀ s.2.1 ∧ ModeOk π P W₀ v μ s ∧
    ∀ K, InRange K → HPos.val (msgPos K) ∈ s.2.2.1 → cwU K s.2.2 →
      ∀ j < doneN μ K, TB π P W₀ K (valsOf v (msgPos K)) j s.1}

variable {π P W₀}

theorem modeOk_cwProgNx (v : (s : HPos) → XD s) (μ : CwMode) (s : HwReg X Z (Mem HPos)) :
    ModeOk π P W₀ v (cwProgNx μ) s := by
  rcases μ with _ | ⟨K', m⟩ | ⟨K', m, j⟩ | ⟨K', m, j, a⟩ | ⟨K', m, j, xi, z⟩ <;> trivial

theorem fInv_free_of_rest {v : (s : HPos) → XD s} {μ : CwMode} (hμ : μ.Rest)
    {s : HwReg X Z (Mem HPos)} (hs : s ∈ FInv π P W₀ v μ) : s ∈ FInv π P W₀ v .free :=
  ⟨hs.1, hs.2.1, trivial, fun K hK hl hu j hj ↦
    hs.2.2.2 K hK hl hu j (by rw [doneN_of_rest hμ]; exact hj)⟩

/-- A trial read never removes a selection. -/
theorem cwUpd_eq_none_of {K K' : Key} {x xi : X} {m : Selections} {o : Option X}
    (h : cwUpd K x xi m o K' = none) : m K' = none := by
  rcases hm : m K' with _ | c
  · rfl
  · rw [le_cwUpd K x xi m o K' c hm] at h
    cases h

/-- A trial read whose digest is a codeword leaves its key selected. -/
theorem cwUpd_ne_none_of {K : Key} {x xi w : X} {m : Selections}
    (hv : Codeword.Valid (trunc128 (xi + w))) : cwUpd K x xi m (some w) K ≠ none := by
  by_cases hm : m K = none
  · rw [cwUpd_some_of_none K x xi hm]
    exact fun h ↦ (cwSel_eq_none_iff hm x xi w).mp h hv
  · exact fun h ↦ hm (cwUpd_eq_none_of h)

end chain

/-! ## The invariant along the realized prefix, in the decompressed basis -/

section decStep

theorem cwLiftHu_fst {M : Type} (hu : Key → X → X → M → Option X → M) (K : Key) (b xi : X)
    (m : Finset HPos × M) (o : Option X) : (cwLiftHu hu K b xi m o).1 = m.1 :=
  rfl

theorem cwLiftHu_snd {M : Type} (hu : Key → X → X → M → Option X → M) (K : Key) (b xi : X)
    (m : Finset HPos × M) (o : Option X) : (cwLiftHu hu K b xi m o).2 = hu K b xi m.2 o :=
  rfl

/-- A sponge port in the decompressed basis keeps the register. -/
theorem decHwPort_snd {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] (read : HwReg X Z (Mem HPos) → A → Y)
    (m' m : (A × Y) × HwReg X Z (Mem HPos))
    (h : (((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z (Mem HPos)) * hwPort read *
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z (Mem HPos))) m' m ≠ 0) :
    m'.2 = m.2 := by
  rw [one_kron_mul_hwPort_mul_one_kron, tableOracle_apply] at h
  split_ifs at h with he
  · rw [he]
    rfl
  · exact absurd rfl h

variable {π : Equiv.Perm (X × Z)} {P : PublicParameter} {W₀ : Hw X Z} {v : (s : HPos) → XD s}

/-- **A record**: the reveal of a pending key's value starts its search with no trial run; a
reveal from between searches discloses at most one key's value, which makes its search next. -/
theorem fInv_rec {μ : CwMode} {T : Finset HPos} (hok : RevOk μ T)
    {s s' : HwReg X Z (Mem HPos)} (hs : s ∈ FInv π P W₀ v μ) (hD : s'.1 = s.1)
    (hb : s'.2 = (s.2.1, (s.2.2.1 ∪ T, s.2.2.2))) :
    s' ∈ FInv π P W₀ v (cwRevNx μ T (valsOf v)) := by
  obtain ⟨hnb, hw, -, hl⟩ := hs
  have hnb' : NoBot s' := by
    show NoBotDb s'.1
    rw [hD]
    exact hnb
  have hw' : HwIn W₀ s'.2.1 := by
    rw [hb]
    exact hw
  have hmem : ∀ K : Key, HPos.val (msgPos K) ∈ s'.2.2.1 →
      HPos.val (msgPos K) ∈ s.2.2.1 ∨ HPos.val (msgPos K) ∈ T := fun K h ↦ by
    rw [hb] at h
    exact Finset.mem_union.mp h
  have hu : ∀ K, cwU K s'.2.2 → cwU K s.2.2 := fun K h ↦ by
    rw [hb] at h
    exact h
  rcases hok.rest_or with ⟨K, m, rfl, hK, rfl⟩ | ⟨hμ, hs1, h1⟩
  · rw [cwRevNx_sing hK]
    refine ⟨hnb', hw', rfl, fun K' hK' hl' hu' j hj ↦ ?_⟩
    have hd : doneN (.grd K (valsOf v (msgPos K)) 0) K' =
        if K = K' then 0 else encodingAttemptLimit := rfl
    by_cases he : K = K'
    · rw [hd, ite_eq_left he] at hj
      exact absurd hj (Nat.not_lt_zero j)
    · rw [hd, ite_eq_right he] at hj
      have hl1 : HPos.val (msgPos K') ∈ s.2.2.1 := by
        rcases hmem K' hl' with h | h
        · exact h
        · exact absurd (msgPos_injOn hK hK' (HPos.val.inj (Finset.mem_singleton.mp h)).symm) he
      have hd' : doneN (.pend K m) K' = encodingAttemptLimit := by
        show (if K = K' then 0 else encodingAttemptLimit) = _
        rw [ite_eq_right he]
      rw [hD]
      exact hl K' hK' hl1 (hu K' hu') j (by rw [hd']; exact hj)
  · rcases hdk : cwDiscKey T with _ | K
    · rw [cwRevNx_free hs1 hdk]
      refine ⟨hnb', hw', trivial, fun K' hK' hl' hu' j hj ↦ ?_⟩
      have hl1 : HPos.val (msgPos K') ∈ s.2.2.1 := by
        rcases hmem K' hl' with h | h
        · exact h
        · exact absurd h (noKey_of_none hs1 hdk K' hK')
      rw [hD]
      exact hl K' hK' hl1 (hu K' hu') j (by rw [doneN_of_rest hμ]; exact hj)
    · rw [cwRevNx_disc hs1 hdk]
      obtain ⟨hK, hKT⟩ := cwDiscKey_spec hdk
      refine ⟨hnb', hw', trivial, fun K' hK' hl' hu' j hj ↦ ?_⟩
      have hd : doneN (.pend K (valsOf v (msgPos K))) K' =
          if K = K' then 0 else encodingAttemptLimit := rfl
      by_cases he : K = K'
      · rw [hd, ite_eq_left he] at hj
        exact absurd hj (Nat.not_lt_zero j)
      · rw [hd, ite_eq_right he] at hj
        have hl1 : HPos.val (msgPos K') ∈ s.2.2.1 := by
          rcases hmem K' hl' with h | h
          · exact h
          · exact absurd (h1 K K' hK hK' hKT h) he
        rw [hD]
        exact hl K' hK' hl1 (hu K' hu') j (by rw [doneN_of_rest hμ]; exact hj)

/-- **A program at a cell of `W₀`** keeps the invariant: the databases change at its cell only. -/
theorem fInv_prog {μ : CwMode} (hμ : μ.Calm) {c : HwProg X Z} (hc : c.CellIn W₀)
    {s s' : HwReg X Z (Mem HPos)} (hs : s ∈ FInv π P W₀ v μ) (hag : DbOffAgree W₀ s.1 s'.1)
    (hnb : NoBot s') (hb : s'.2 = (progUpdate c s.2.1, s.2.2)) :
    s' ∈ FInv π P W₀ v (cwProgNx μ) := by
  obtain ⟨-, hw, -, hl⟩ := hs
  refine ⟨hnb, ?_, modeOk_cwProgNx v μ s', fun K hK hl' hu j hj ↦ ?_⟩
  · rw [hb]
    obtain ⟨h1, h2, h3⟩ := hw
    rcases c with ⟨z, a⟩ | ⟨x, a⟩ | ⟨x, a⟩
    · refine ⟨fun z' hz' ↦ ?_, h2, h3⟩
      by_cases he : z' = z
      · subst he
        exact hc
      · exact h1 z' (by simpa [progUpdate, Function.update_of_ne he] using hz')
    · refine ⟨h1, fun x' hx' ↦ ?_, h3⟩
      by_cases he : x' = x
      · subst he
        exact hc
      · exact h2 x' (by simpa [progUpdate, Function.update_of_ne he] using hx')
    · refine ⟨h1, h2, fun x' hx' ↦ ?_⟩
      by_cases he : x' = x
      · subst he
        exact hc
      · exact h3 x' (by simpa [progUpdate, Function.update_of_ne he] using hx')
  · have hl1 : HPos.val (msgPos K) ∈ s.2.2.1 := by
      rw [hb] at hl'
      exact hl'
    have hu1 : cwU K s.2.2 := by
      rw [hb] at hu
      exact hu
    exact tB_of_offAgree π P W₀ hag (hl K hK hl1 hu1 j (by rw [← doneN_cwProgNx hμ]; exact hj))

/-- **The `k`-read of a trial**: its outcome is the decompressed value unless the block is in
`W₀`. -/
theorem fInv_readK {K : Key} {m : Digest} {j : ℕ} {s s' : HwReg X Z (Mem HPos)}
    (hs : s ∈ FInv π P W₀ v (.grd K m j)) (hD : s'.1 = s.1) (hb : s'.2 = s.2) {o : Option Z}
    (ho : (s.2.1.2.1 (cwBlk P K m j)).or (s.1.2.1 (cwBlk P K m j)) = o) :
    s' ∈ FInv π P W₀ v (.afK K m j (o.getD 0)) := by
  obtain ⟨hnb, hw, hm, hl⟩ := hs
  have hm' : ModeOk π P W₀ v (.afK K m j (o.getD 0)) s' := by
    refine ⟨hm, ?_⟩
    by_cases hk : W₀.2.1 (cwBlk P K m j) = none
    · refine .inr ?_
      rw [← ho, or_eq_of_hwIn (hw.2.1 _) hk, hD]
      rfl
    · exact .inl hk
  refine ⟨?_, ?_, hm', fun K' hK' hl' hu j' hj' ↦ ?_⟩
  · show NoBotDb s'.1
    rw [hD]
    exact hnb
  · rw [hb]
    exact hw
  · rw [hb] at hl' hu
    rw [hD]
    exact hl K' hK' hl' hu j' hj'

/-- **The `k'`-read of a trial.** -/
theorem fInv_readK' {K : Key} {m : Digest} {j : ℕ} {a : Z} {s s' : HwReg X Z (Mem HPos)}
    (hs : s ∈ FInv π P W₀ v (.afK K m j a)) (hD : s'.1 = s.1) (hb : s'.2 = s.2) {o : Option Z}
    (ho : (s.2.1.2.2 (π (cwBlk P K m j, a)).1).or (s.1.2.2 (π (cwBlk P K m j, a)).1) = o) :
    s' ∈ FInv π P W₀ v (.afK' K m j (π (cwBlk P K m j, a)).1
      ((π (cwBlk P K m j, a)).2 + o.getD 0)) := by
  obtain ⟨hnb, hw, ⟨hbase, hm⟩, hl⟩ := hs
  have hm' : ModeOk π P W₀ v (.afK' K m j (π (cwBlk P K m j, a)).1
      ((π (cwBlk P K m j, a)).2 + o.getD 0)) s' := by
    refine ⟨hbase, ?_⟩
    rcases hm with hm | ha
    · exact .inl hm
    · rw [hD]
      have hy : (π (cwBlk P K m j, a)).1 = trY π P K m j s.1 := by
        unfold trY
        rw [ha]
      by_cases hk' : W₀.2.2 (trY π P K m j s.1) = none
      · refine .inr (.inr ⟨hy, ?_⟩)
        rw [← ho, hy, or_eq_of_hwIn (hw.2.2 _) hk']
        unfold trZ
        rw [ha]
      · exact .inr (.inl hk')
  refine ⟨?_, ?_, hm', fun K' hK' hl' hu j' hj' ↦ ?_⟩
  · show NoBotDb s'.1
    rw [hD]
    exact hnb
  · rw [hb]
    exact hw
  · rw [hb] at hl' hu
    rw [hD]
    exact hl K' hK' hl' hu j' hj'

/-- **The `h`-read of a trial**: a codeword digest selects the key and ends the search; otherwise
the trial failed (or touched `W₀`). -/
theorem fInv_readH {K : Key} {m : Digest} {j : ℕ} {xi : X} {z : Z}
    {s s' : HwReg X Z (Mem HPos)} (hs : s ∈ FInv π P W₀ v (.afK' K m j xi z)) (hD : s'.1 = s.1)
    {o : Option X} (hb1 : s'.2.1 = s.2.1) (hb2 : s'.2.2.1 = s.2.2.1)
    (hb3 : s'.2.2.2 = cwUpd K (cwBlk P K m j) xi s.2.2.2 o)
    (ho : (s.2.1.1 z).or (s.1.1 z) = o) :
    s' ∈ FInv π P W₀ v (stopMode K m j (xi + o.getD 0)) := by
  obtain ⟨hnb, hw, ⟨hbase, hm⟩, hl⟩ := hs
  obtain ⟨w, hwo⟩ : ∃ w, o = some w := by
    rcases hz : s.2.1.1 z with _ | w
    · rw [hz] at ho
      exact Option.isSome_iff_exists.mp (ho ▸ hnb.1 z)
    · rw [hz] at ho
      exact ⟨w, ho.symm⟩
  subst hwo
  have hnb' : NoBot s' := by
    show NoBotDb s'.1
    rw [hD]
    exact hnb
  have hw' : HwIn W₀ s'.2.1 := by
    rw [hb1]
    exact hw
  have hrev : s'.2.2.1 = s.2.2.1 := hb2
  have hu : ∀ K' : Key, cwU K' s'.2.2 → cwU K' s.2.2 := fun K' h ↦
    cwUpd_eq_none_of (K := K) (x := cwBlk P K m j) (xi := xi) (o := some w)
      (show cwUpd K (cwBlk P K m j) xi s.2.2.2 (some w) K' = none by rw [← hb3]; exact h)
  show s' ∈ FInv π P W₀ v (stopMode K m j (xi + w))
  unfold stopMode
  split_ifs with hv
  · refine ⟨hnb', hw', trivial, fun K' hK' hl' hu' j' hj' ↦ ?_⟩
    by_cases hk : K' = K
    · subst hk
      exfalso
      have h1 : s'.2.2.2 K' = none := hu'
      rw [hb3] at h1
      exact cwUpd_ne_none_of hv h1
    · have hne : K ≠ K' := fun he ↦ hk he.symm
      have hd : doneN (.afK' K m j xi z) K' = encodingAttemptLimit := by
        show (if K = K' then j else encodingAttemptLimit) = _
        rw [ite_eq_right hne]
      rw [hrev] at hl'
      rw [hD]
      exact hl K' hK' hl' (hu K' hu') j' (by rw [hd]; exact hj')
  · refine ⟨hnb', hw', hbase, fun K' hK' hl' hu' j' hj' ↦ ?_⟩
    rw [hrev] at hl'
    rw [hD]
    by_cases hne : K = K'
    · subst hne
      have hj : j' < j + 1 := by
        have h1 : doneN (.grd K m (j + 1)) K = j + 1 := by
          show (if K = K then j + 1 else encodingAttemptLimit) = _
          rw [ite_eq_left rfl]
        rwa [h1] at hj'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · have h1 : doneN (.afK' K m j xi z) K = j := by
          show (if K = K then j else encodingAttemptLimit) = _
          rw [ite_eq_left rfl]
        exact hl K hK' hl' (hu K hu') j' (by rw [h1]; exact hj)
      · subst hj
        subst hbase
        unfold TB
        rcases hm with hm | hm | ⟨hxi, hz⟩
        · exact .inl hm
        · exact .inr (.inl hm)
        · by_cases hh : W₀.1 (trZ π P K (valsOf v (msgPos K)) j' s.1) = none
          · refine .inr (.inr (.inr ?_))
            have hwv : trW π P K (valsOf v (msgPos K)) j' s.1 = w := by
              unfold trW
              rw [← hz, ← or_eq_of_hwIn (hw.1 _) (hz ▸ hh) (s.1.1 z), ho]
              rfl
            rw [← hxi, hwv]
            exact hv
          · exact .inr (.inr (.inl hh))
    · have h1 : doneN (.grd K m (j + 1)) K' = doneN (.afK' K m j xi z) K' := by
        show (if K = K' then j + 1 else encodingAttemptLimit) =
          (if K = K' then j else encodingAttemptLimit)
        rw [ite_eq_right hne, ite_eq_right hne]
      exact hl K' hK' hl' (hu K' hu') j' (by rw [← h1]; exact hj')

/-- **Every allowed call keeps the invariant**, in the decompressed basis. -/
theorem fInv_step (μ : CwMode) (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × HwReg X Z (Mem HPos))
      ((recHwSpec X Z HPos Selections).In i × HwReg X Z (Mem HPos)) ℂ)
    (hok : stOkZ π P (cwLiftHu cwUpd) μ i) (hc : PortCw (S := HPos) (M := Selections) W₀ i)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
      HwReg X Z (Mem HPos) ↦ m.2) (FInv π P W₀ v μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i ×
      HwReg X Z (Mem HPos) ↦ m.2) (FInv π P W₀ v (stNxZ π P v μ i r))
      (((decR (X := X) (Z := Z) m0R).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · rw [decR_branch_apply m0R _ r _ (runtime2_branch m0R (.inl (.inl i)) r)]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    have he : m'.2 = m.2 := by
      cases i <;> exact decHwPort_snd _ m' m hK
    show m'.2 ∈ FInv π P W₀ v .free
    rw [he]
    exact fInv_free_of_rest hok hm
  · rw [decR_branch_apply m0R _ r _ (runtime2_branch m0R (.inl (.inr c)) r)]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    rcases μ with _ | ⟨K, mv⟩ | ⟨K, mv, j⟩ | ⟨K, mv, j, a⟩ | ⟨K, mv, j, xi, z⟩ <;>
      rcases c with ⟨z', u⟩ | ⟨x, u⟩ | ⟨y, u⟩
    all_goals try exact hok.elim
    · obtain ⟨-, hx, rfl⟩ := hok
      subst hx
      obtain ⟨hp, hφ, hR⟩ := dec_clsKraus_ne_zero
        (p := fun b' : Hw X Z × Mem HPos ↦ b'.2 = r.2)
        (φ := fun b' ↦ (b'.1, r.2))
        (R := fun b' ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
          (cellRead b'.1.2.1 (cwBlk P K mv j) r.1 ⊗ₖ
            (1 : Matrix (Database X Z) (Database X Z) ℂ))) hK
      obtain ⟨hD, ho⟩ := compressDbs_readK_ne_zero hR
      exact fInv_readK hm hD (hφ.trans (Prod.ext rfl hp.symm)) ho
    · obtain ⟨hy, rfl⟩ := hok
      subst hy
      obtain ⟨hp, hφ, hR⟩ := dec_clsKraus_ne_zero
        (p := fun b' : Hw X Z × Mem HPos ↦ b'.2 = r.2)
        (φ := fun b' ↦ (b'.1, r.2))
        (R := fun b' ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
          ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ
            cellRead b'.1.2.2 (π (cwBlk P K mv j, a)).1 r.1)) hK
      obtain ⟨hD, ho⟩ := compressDbs_readK'_ne_zero hR
      exact fInv_readK' hm hD (hφ.trans (Prod.ext rfl hp.symm)) ho
    · obtain ⟨hz, rfl⟩ := hok
      obtain ⟨hp, hφ, hR⟩ := dec_clsKraus_ne_zero
        (p := fun b' : Hw X Z × Mem HPos ↦ b'.2 = r.2)
        (φ := fun b' ↦ (b'.1, cwLiftHu cwUpd K (cwBlk P K mv j) xi r.2 r.1))
        (R := fun b' ↦ cellRead b'.1.1 z' r.1 ⊗ₖ
          (1 : Matrix (Database X Z × Database X Z) (Database X Z × Database X Z) ℂ)) hK
      obtain ⟨hD, ho⟩ := compressDbs_readH_ne_zero hR
      rw [hz] at ho
      show m'.2 ∈ FInv π P W₀ v (stopMode K mv j (xi + r.1.getD 0))
      exact fInv_readH (o := r.1) hm hD (congrArg (fun t ↦ t.1) hφ)
        ((congrArg (fun t ↦ t.2.1) hφ).trans ((cwLiftHu_fst cwUpd K (cwBlk P K mv j) xi r.2
          r.1).trans (congrArg Prod.fst hp.symm)))
        ((congrArg (fun t ↦ t.2.2) hφ).trans ((cwLiftHu_snd cwUpd K (cwBlk P K mv j) xi r.2
          r.1).trans (congrArg (fun t ↦ cwUpd K (cwBlk P K mv j) xi t.2 r.1) hp.symm))) ho
  · rw [decR_branch_apply m0R _ r _ (runtime2_branch m0R (.inr c) r)]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    show m'.2 ∈ FInv π P W₀ v (cwProgNx μ)
    have hnb := hm.1
    rcases c with ⟨z, a⟩ | ⟨x, a⟩ | ⟨x, a⟩
    · obtain ⟨-, hφ, hR⟩ := dec_clsKraus_ne_zero
        (p := fun b' : Hw X Z × Mem HPos ↦ b'.1.1 z = r.2)
        (φ := fun b' ↦ ((Function.update b'.1.1 z (some a), b'.1.2), b'.2))
        (R := fun _ ↦ cellDiscard z r.1 ⊗ₖ
          (1 : Matrix (Database X Z × Database X Z) (Database X Z × Database X Z) ℂ)) hK
      rw [← one_kronecker_one] at hR
      obtain ⟨h1, h2, h3⟩ := dec_dbs_ne_zero hR
      obtain ⟨h1a, h1b⟩ := compressAll_mul_cellDiscard_mul_compressAll_ne_zero h1
      have h2' := compressAll_one_ne_zero h2
      have h3' := compressAll_one_ne_zero h3
      have hc' : W₀.1 z ≠ none := hc
      have hag : DbOffAgree W₀ m.2.1 m'.2.1 :=
        ⟨fun z' hz' ↦ (h1a z' fun he ↦ hc' (he ▸ hz')).symm,
          fun x' _ ↦ (congrFun h2' x').symm, fun x' _ ↦ (congrFun h3' x').symm⟩
      have hnb' : NoBot m'.2 := by
        refine (show NoBotDb m'.2.1 from ⟨fun z' ↦ ?_, fun x' ↦ ?_, fun x' ↦ ?_⟩)
        · by_cases he : z' = z
          · subst he
            exact h1b
          · rw [h1a z' he]
            exact hnb.1 z'
        · rw [h2']
          exact hnb.2.1 x'
        · rw [h3']
          exact hnb.2.2 x'
      exact fInv_prog (c := .programH z a) hok hc' hm hag hnb' hφ
    · obtain ⟨-, hφ, hR⟩ := dec_clsKraus_ne_zero
        (p := fun b' : Hw X Z × Mem HPos ↦ b'.1.2.1 x = r.2)
        (φ := fun b' ↦ ((b'.1.1, Function.update b'.1.2.1 x (some a), b'.1.2.2), b'.2))
        (R := fun _ ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
          (cellDiscard x r.1 ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ))) hK
      obtain ⟨h1, h2, h3⟩ := dec_dbs_ne_zero hR
      obtain ⟨h2a, h2b⟩ := compressAll_mul_cellDiscard_mul_compressAll_ne_zero h2
      have h1' := compressAll_one_ne_zero h1
      have h3' := compressAll_one_ne_zero h3
      have hc' : W₀.2.1 x ≠ none := hc
      have hag : DbOffAgree W₀ m.2.1 m'.2.1 :=
        ⟨fun z' _ ↦ (congrFun h1' z').symm,
          fun x' hx' ↦ (h2a x' fun he ↦ hc' (he ▸ hx')).symm,
          fun x' _ ↦ (congrFun h3' x').symm⟩
      have hnb' : NoBot m'.2 := by
        refine (show NoBotDb m'.2.1 from ⟨fun z' ↦ ?_, fun x' ↦ ?_, fun x' ↦ ?_⟩)
        · rw [h1']
          exact hnb.1 z'
        · by_cases he : x' = x
          · subst he
            exact h2b
          · rw [h2a x' he]
            exact hnb.2.1 x'
        · rw [h3']
          exact hnb.2.2 x'
      exact fInv_prog (c := .programK x a) hok hc' hm hag hnb' hφ
    · obtain ⟨-, hφ, hR⟩ := dec_clsKraus_ne_zero
        (p := fun b' : Hw X Z × Mem HPos ↦ b'.1.2.2 x = r.2)
        (φ := fun b' ↦ ((b'.1.1, b'.1.2.1, Function.update b'.1.2.2 x (some a)), b'.2))
        (R := fun _ ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
          ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellDiscard x r.1)) hK
      obtain ⟨h1, h2, h3⟩ := dec_dbs_ne_zero hR
      obtain ⟨h3a, h3b⟩ := compressAll_mul_cellDiscard_mul_compressAll_ne_zero h3
      have h1' := compressAll_one_ne_zero h1
      have h2' := compressAll_one_ne_zero h2
      have hc' : W₀.2.2 x ≠ none := hc
      have hag : DbOffAgree W₀ m.2.1 m'.2.1 :=
        ⟨fun z' _ ↦ (congrFun h1' z').symm, fun x' _ ↦ (congrFun h2' x').symm,
          fun x' hx' ↦ (h3a x' fun he ↦ hc' (he ▸ hx')).symm⟩
      have hnb' : NoBot m'.2 := by
        refine (show NoBotDb m'.2.1 from ⟨fun z' ↦ ?_, fun x' ↦ ?_, fun x' ↦ ?_⟩)
        · rw [h1']
          exact hnb.1 z'
        · rw [h2']
          exact hnb.2.1 x'
        · by_cases he : x' = x
          · subst he
            exact h3b
          · rw [h3a x' he]
            exact hnb.2.2 x'
      exact fInv_prog (c := .programK' x a) hok hc' hm hag hnb' hφ
  · rw [decR_branch_apply m0R _ r _ (recStep_branch T r)]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    obtain ⟨-, hφ, hR⟩ := dec_clsKraus_ne_zero
      (φ := fun b' ↦ (b'.1, (b'.2.1 ∪ T, b'.2.2)))
      (R := fun _ ↦ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) hK
    exact fInv_rec hok hm (compressDbs_one_ne_zero hR) hφ

/-- The initial register in the decompressed basis: no empty cell, nothing hardwired, nothing
revealed. -/
theorem init_fInv :
    QuerySupportedOn (fun m : QReg.of Unit × HwReg X Z (Mem HPos) ↦ m.2) (FInv π P W₀ v .free)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        compressReg X Z (Mem HPos)) initR) := by
  have hnb := noBot_init (X := X) (Z := Z) m0R
    ((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ)
  have h0 : QuerySupportedOn (fun m : QReg.of Unit × HwReg X Z (Mem HPos) ↦ m.2)
      {s | s.2 = (hwEmpty X Z, m0R)}
      (((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        (runtimeR (X := X) (Z := Z) m0R).init.matrix) := by
    intro m m' hm
    change (((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
      (SubState.basis (((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m0R) :
        HwReg X Z (Mem HPos))).matrix) m m' ≠ 0 at hm
    rw [kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [SubState.matrix_basis, Matrix.single_apply] at h
    split_ifs at h with he
    · refine ⟨?_, ?_⟩
      · show m.2.2 = _
        rw [← he.1]
      · show m'.2.2 = _
        rw [← he.2]
    · exact absurd rfl h
  have h1 := QuerySupportedOn.conj h0
    (K := (1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ compressReg X Z (Mem HPos))
    (q' := fun m : QReg.of Unit × HwReg X Z (Mem HPos) ↦ m.2)
    (S' := {s | s.2 = (hwEmpty X Z, m0R)})
    fun m' m hK hm ↦ by
      have hK' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) hK).2
      rw [compressReg, kroneckerMap_apply] at hK'
      have he : m'.2.2 = m.2.2 := by
        by_contra hne
        exact right_ne_zero_of_mul hK' (Matrix.one_apply_ne hne)
      show m'.2.2 = _
      rw [he]
      exact hm
  have hmem : ∀ s : HwReg X Z (Mem HPos), NoBot s → s.2 = (hwEmpty X Z, m0R) →
      s ∈ FInv π P W₀ v .free := fun s hs he ↦ by
    refine ⟨hs, ?_, trivial, fun K _ hl _ _ _ ↦ ?_⟩
    · rw [he]
      exact ⟨fun _ h ↦ absurd rfl h, fun _ h ↦ absurd rfl h, fun _ h ↦ absurd rfl h⟩
    · rw [he] at hl
      exact absurd hl (Finset.notMem_empty _)
  intro a b hab
  exact ⟨hmem _ (hnb a b hab).1 (h1 a b hab).1, hmem _ (hnb a b hab).2 (h1 a b hab).2⟩

end decStep

/-! ## Port conditions as moded conditions -/

section port

variable {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig.{u, v}} {Ω : QReg → Type w}
  {Mode : Type} {ok : Mode → spec.Port → Prop}
  {nx : Mode → (i : spec.Port) → spec.Result i → Mode}

/-- **A port condition holding at every call of a run is a moded condition**: every call of the
program, on every branch, satisfies it. -/
theorem modedP_and_port (R : QuantumRuntime spec) (I : L.Interp) (Q : spec.Port → Prop)
    {fin : (Σ u, Ω u) → Mode → Prop} {A : QReg} (x : QuantumComp L spec Ω A) :
    ∀ μ, ModedP ok nx fin μ x → ∀ {ρ : Matrix (A × R.D) (A × R.D) ℂ},
      R.ForallQueries I (fun i _ _ ↦ Q i) x ρ →
        ModedP (fun μ i ↦ ok μ i ∧ Q i) nx fin μ x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => intro _ hx _ _; exact hx
  | primBind _ o k ih =>
    intro μ hx ρ hq
    rw [QuantumRuntime.forallQueries_primBind_iff] at hq
    exact ⟨trivial, fun b ↦ ih b.down μ (hx.2 b) (hq b.down)⟩
  | queryBind _ i E ℓ k ih =>
    intro μ hx ρ hq
    rw [QuantumRuntime.forallQueries_queryBind_iff] at hq
    exact ⟨⟨hx.1, hq.1⟩, fun b ↦ ih b.down _ (hx.2 b) (hq.2 b.down)⟩

end port

/-! ## The failed searches against a database event -/

section prefixInv

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter) (W₀ : Hw X Z) (v : (s : HPos) → XD s)

/-- **Some key's search fails on the databases**: every trial of a key `K_l(idx)` on the value it
signs touches `W₀` or fails. -/
def FailDb (D : DbReg X Z) : Prop :=
  ∃ l : Layer, ∃ idx : Index, ∀ j < encodingAttemptLimit,
    TB π P W₀ (keyOf l idx) (valsOf v (msgPos (keyOf l idx))) j D

/-- The registers whose databases fail a search. -/
def failSet : Set (HwReg X Z (Mem HPos)) := {s | FailDb π P W₀ v s.1}

/-- `failSet`, decided classically. -/
noncomputable instance instDecidableFailSetCf : DecidablePred (· ∈ failSet π P W₀ v) :=
  Classical.decPred _

/-- `FailDb` looks at the databases outside `W₀` only. -/
theorem offHw_failDb : OffHw W₀ (FailDb π P W₀ v) := by
  intro D D' h1 h2 h3
  have hag : DbOffAgree W₀ D D' := ⟨h1, h2, h3⟩
  have hag' : DbOffAgree W₀ D' D :=
    ⟨fun z hz ↦ (h1 z hz).symm, fun x hx ↦ (h2 x hx).symm, fun x hx ↦ (h3 x hx).symm⟩
  exact ⟨fun ⟨l, idx, h⟩ ↦ ⟨l, idx, fun j hj ↦ tB_of_offAgree π P W₀ hag (h j hj)⟩,
    fun ⟨l, idx, h⟩ ↦ ⟨l, idx, fun j hj ↦ tB_of_offAgree π P W₀ hag' (h j hj)⟩⟩

/-- A reveal's drop key is the key whose value it discloses among others. -/
theorem dropKey_some {T : Finset HPos} {K : Key} (h : dropKey T = some K) :
    cwSingKey T = none ∧ cwDiscKey T = some K := by
  unfold dropKey at h
  rcases hs : cwSingKey T with _ | K'
  · rw [hs] at h
    exact ⟨rfl, h⟩
  · rw [hs] at h
    cases h

/-- **A repeated disclosure with the key unselected is in the failure event**: at a record call
allowed by a mode, on the invariant, the reveal comes from between searches, where a key whose
value is disclosed and which is unselected has run all its trials. -/
theorem reRevW_le {Q : (recHwSpec X Z HPos Selections).Port → Prop}
    (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ)
    (hσ : σ.PosSemidef)
    (h : ∃ μ : CwMode, (stOkZ π P (cwLiftHu cwUpd) μ i ∧ Q i) ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × HwReg X Z (Mem HPos) ↦
        m.2) (FInv π P W₀ v μ) (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
          ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z (Mem HPos)) σ)) :
    reRevW i σ ≤ (rCharge Selections 0 0 0 1 i : ℝ≥0∞) *
      potential (hwDecProj (failSet π P W₀ v)) σ := by
  rcases i with ((i | c) | c) | T
  · exact zero_le
  · exact zero_le
  · exact zero_le
  · obtain ⟨μ, ⟨hok, -⟩, hS⟩ := h
    show reRevO (dropKey T) σ ≤ ((1 : ℕ) : ℝ≥0∞) * _
    rw [Nat.cast_one, one_mul]
    rcases hT : dropKey T with _ | K
    · exact zero_le
    · obtain ⟨hs, hd⟩ := dropKey_some hT
      obtain ⟨⟨l, idx, rfl⟩, -⟩ := cwDiscKey_spec hd
      have hrest : μ.Rest := by
        rcases hok.rest_or with ⟨K', m, -, hK', hT'⟩ | ⟨hμ, -, -⟩
        · rw [hT', cwSingKey_eq hK'] at hs
          cases hs
        · exact hμ
      classical
      show diagMass {q : Unit × HwReg X Z (Mem HPos) | ReRev (keyOf l idx) q.2} σ ≤ _
      exact diagMass_le_potential_hwDecProj
        (fun b : Hw X Z × Mem HPos ↦ HPos.val (msgPos (keyOf l idx)) ∈ b.2.1 ∧
          cwU (keyOf l idx) b.2) _ _ hσ hS
        fun s hs hP ↦ ⟨l, idx, fun j hj ↦ hs.2.2.2 (keyOf l idx) (inRange_keyOf l idx) hP.1 hP.2
          j (by rw [doneN_of_rest hrest]; exact hj)⟩

end prefixInv

section total

theorem portCw_of_cellPortIn {Pc : SpongeQuery X Z → Prop}
    {i : (recHwSpec X Z HPos Selections).Port} (h : CellPortIn Pc i) :
    PortCw (S := HPos) (M := Selections) (cellsHw Pc) i := by
  rcases i with ((i | c) | c) | T
  · trivial
  · trivial
  · exact cellIn_cellsHw h
  · trivial

/-- **The repeated-disclosure masses of the realized prefix are at most the reveal charge bound
times the initial weight of the failure event** off `W₀ = cellsHw (ProgCell pub v)`. -/
theorem totalWeight_reRevW_le (pol : DigestPolicy) (hpol : pol.ValFree) (pub : Pub)
    (v : (s : HPos) → XD s) (A : SAdversary) {R : ℕ}
    (hR : IFreeM.IsChargeBound (prefixR pol A pub v) (portCharge (rCharge Selections 0 0 0 1)) R) :
    (runtimeR m0R).totalWeight .instruments reRevW (prefixR pol A pub v) initR ≤
      R * potential (hwDecProj (failSet pub.perm pub.seed (cellsHw (ProgCell pub v)) v)) initR := by
  have hq := forallQueries_dec_moded m0R
    (ok := fun μ i ↦ stOkZ pub.perm pub.seed (cwLiftHu cwUpd) μ i ∧ CellPortIn (ProgCell pub v) i)
    (nx := stNxZ pub.perm pub.seed v)
    (fun μ : CwMode ↦ FInv pub.perm pub.seed (cellsHw (ProgCell pub v)) v μ)
    (fun μ i r σ hok hσ ↦ fInv_step μ i r σ hok.1 (portCw_of_cellPortIn hok.2) hσ)
    LocalSig.Interp.instruments (prefixR pol A pub v) CwMode.free
    (modedP_and_port (runtimeR m0R) .instruments (CellPortIn (ProgCell pub v)) _ CwMode.free
      (modedP_prefixR_st pol hpol pub A v) (cwCellPortIn_prefixR pub v pol A initR))
    init_fInv
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments _ (fun i E σ h ↦ h)
    (w' := fun i σ ↦ (rCharge Selections 0 0 0 1 i : ℝ≥0∞) *
      potential (hwDecProj (failSet pub.perm pub.seed (cellsHw (ProgCell pub v)) v)) σ)
    (fun i σ hσ hok ↦ reRevW_le pub.perm pub.seed _ v i σ hσ hok) _ initR_posSemidef
    hq).trans ?_
  exact totalWeight_charge_potential_le (runtimeR m0R) .instruments _ _
    (PortCw (S := HPos) (M := Selections) (cellsHw (ProgCell pub v)))
    (fun i hi r ↦ runtimeR_commute_hwDecProj m0R
      (offHw_failDb pub.perm pub.seed (cellsHw (ProgCell pub v)) v)
      (failSet pub.perm pub.seed (cellsHw (ProgCell pub v)) v) (fun _ ↦ Iff.rfl) i hi r)
    (fun i E σ h ↦ portCw_of_cellPortIn (Exists.choose_spec h).1.2) _ hR initR_posSemidef hq

end total

/-! ## Counting the failed searches over the total tables -/

section count

theorem progCell_of_cellsHw_k {Pc : SpongeQuery X Z → Prop} {x : X}
    (h : (cellsHw Pc).2.1 x ≠ none) : Pc (.k x) := by
  classical
  by_contra hc
  exact h (ite_eq_right hc)

theorem progCell_of_cellsHw_k' {Pc : SpongeQuery X Z → Prop} {x : X}
    (h : (cellsHw Pc).2.2 x ≠ none) : Pc (.k' x) := by
  classical
  by_contra hc
  exact h (ite_eq_right hc)

theorem progCell_of_cellsHw_h {Pc : SpongeQuery X Z → Prop} {z : Z}
    (h : (cellsHw Pc).1 z ≠ none) : Pc (.h z) := by
  classical
  by_contra hc
  exact h (ite_eq_right hc)

theorem trY_ofFunDbs (π : Equiv.Perm (X × Z)) (P : PublicParameter) (K : Key) (m : Digest)
    (j : ℕ) (t : (Z → X) × (X → Z) × (X → Z)) :
    trY π P K m j (ofFunDbs t) = tY π (cwBlk P K m j) t := rfl

theorem trZ_ofFunDbs (π : Equiv.Perm (X × Z)) (P : PublicParameter) (K : Key) (m : Digest)
    (j : ℕ) (t : (Z → X) × (X → Z) × (X → Z)) :
    trZ π P K m j (ofFunDbs t) = tZ π (cwBlk P K m j) t := rfl

theorem trW_ofFunDbs (π : Equiv.Perm (X × Z)) (P : PublicParameter) (K : Key) (m : Digest)
    (j : ℕ) (t : (Z → X) × (X → Z) × (X → Z)) :
    trW π P K m j (ofFunDbs t) = t.1 (tZ π (cwBlk P K m j) t) := rfl

/-- The non-codeword values of a trial cell. -/
theorem sum_not_codeword_le_sph (y : X) :
    ∑ w : X, (if ¬ Codeword.Valid (trunc128 (y + w)) then 1 else 0) ≤
      Fintype.card X - cwCount * 2 ^ 960 := by
  rw [sum_not_eq, card_codeword_trunc128 y]

/-- The codeword values of a trial cell are at most all its values. -/
theorem cwCount_mul_le_card_X_sph : cwCount * 2 ^ 960 ≤ Fintype.card X := by
  rw [← card_codeword_trunc128 0]
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- **The failure fraction of one search** (`frac_fail_le`'s bound) at `k` and `h` cells,
`cZ` capacities, `cX` rates of which `cw` give codewords. Stated over numbers: a definition
holding concrete card terms would carry abstracted instance proofs that block unification. -/
noncomputable def cfFracOf (k h cZ cX cw : ℕ) : ℝ≥0∞ :=
  ((encodingAttemptLimit * (18 * k + h) + encodingAttemptLimit * encodingAttemptLimit : ℕ) :
    ℝ≥0∞) / cZ + (((cX - cw) ^ encodingAttemptLimit : ℕ) : ℝ≥0∞) /
      ((cX ^ encodingAttemptLimit : ℕ) : ℝ≥0∞)

/-- Every trial of the key `K_l(idx)` on the value it signs touches `W₀` or fails, on the tables
`t`. -/
def KeyFailT (π : Equiv.Perm (X × Z)) (P : PublicParameter) (W₀ : Hw X Z)
    (v : (s : HPos) → XD s) (q : Layer × Index) (t : (Z → X) × (X → Z) × (X → Z)) : Prop :=
  ∀ j < encodingAttemptLimit, TB π P W₀ (keyOf q.1 q.2) (valsOf v (msgPos (keyOf q.1 q.2))) j
    (ofFunDbs t)

open scoped Classical in
/-- **The failure fraction**: a union over the keys `K_l(idx)` of `frac_fail_le`, the trial blocks
off the programmable cells (`TrialsOff`) and `PermGood π 18`. -/
theorem frac_failDb_le (pub : Pub) (v : (s : HPos) → XD s) (hπ : PermGood pub.perm 18)
    (hoff : TrialsOff pub.xw pub.keys.1 (valsOf v)) :
    ((Finset.univ.filter fun t ↦
        FailDb pub.perm pub.seed (cellsHw (ProgCell pub v)) v (ofFunDbs t)).card : ℝ≥0∞) /
      Fintype.card ((Z → X) × (X → Z) × (X → Z)) ≤
        Fintype.card (Layer × Index) * cfFracOf (k'CellsP pub v).card (hCellsP pub v).card
          (Fintype.card Z) (Fintype.card X) (cwCount * 2 ^ 960) := by
  have hkey : ∀ q : Layer × Index, ((Finset.univ.filter
      (KeyFailT pub.perm pub.seed (cellsHw (ProgCell pub v)) v q)).card : ℝ≥0∞) /
        Fintype.card ((Z → X) × (X → Z) × (X → Z)) ≤ cfFracOf (k'CellsP pub v).card
          (hCellsP pub v).card (Fintype.card Z) (Fintype.card X) (cwCount * 2 ^ 960) := fun q ↦
    frac_fail_le hπ (k'CellsP pub v) (hCellsP pub v)
      (fun j ↦ cwBlk pub.seed (keyOf q.1 q.2) (valsOf v (msgPos (keyOf q.1 q.2))) j)
      encodingAttemptLimit (fun i hi j hj he ↦ (cwBlk_inj pub.seed hi hj he).2.2)
      (fun y ↦ Codeword.Valid (trunc128 y)) _ sum_not_codeword_le_sph _ fun t ht j hj ↦ by
        have h0 := ht j hj
        unfold TB at h0
        rw [trY_ofFunDbs, trZ_ofFunDbs, trW_ofFunDbs] at h0
        rcases h0 with h | h | h | h
        · exact absurd (progCell_of_cellsHw_k h) (not_progCell_cwBlk pub v hoff _ _ j)
        · exact .inl (.inl (mem_k'CellsP (progCell_of_cellsHw_k' h)))
        · exact .inl (.inr (mem_hCellsP (progCell_of_cellsHw_h h)))
        · exact .inr h
  have hcard : (Finset.univ.filter fun t ↦
      FailDb pub.perm pub.seed (cellsHw (ProgCell pub v)) v (ofFunDbs t)).card ≤
      ∑ q : Layer × Index, (Finset.univ.filter
        (KeyFailT pub.perm pub.seed (cellsHw (ProgCell pub v)) v q)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun t _ ↦ ?_
    by_cases hF : FailDb pub.perm pub.seed (cellsHw (ProgCell pub v)) v (ofFunDbs t)
    · rw [ite_eq_left hF]
      obtain ⟨l, idx, h⟩ := hF
      have h' : KeyFailT pub.perm pub.seed (cellsHw (ProgCell pub v)) v (l, idx) t := h
      exact le_trans (by rw [ite_eq_left h']) (Finset.single_le_sum
        (f := fun q : Layer × Index ↦
          if KeyFailT pub.perm pub.seed (cellsHw (ProgCell pub v)) v q t then 1 else 0)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (l, idx)))
    · rw [ite_eq_right hF]
      exact Nat.zero_le _
  calc ((Finset.univ.filter fun t ↦
        FailDb pub.perm pub.seed (cellsHw (ProgCell pub v)) v (ofFunDbs t)).card : ℝ≥0∞) /
        Fintype.card ((Z → X) × (X → Z) × (X → Z))
      ≤ ((∑ q : Layer × Index, (Finset.univ.filter
          (KeyFailT pub.perm pub.seed (cellsHw (ProgCell pub v)) v q)).card : ℕ) : ℝ≥0∞) /
          Fintype.card ((Z → X) × (X → Z) × (X → Z)) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hcard) _
    _ = ∑ q : Layer × Index, ((Finset.univ.filter
          (KeyFailT pub.perm pub.seed (cellsHw (ProgCell pub v)) v q)).card : ℝ≥0∞) /
          Fintype.card ((Z → X) × (X → Z) × (X → Z)) := by
        push_cast
        rw [ENNReal.div_eq_inv_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ (ENNReal.div_eq_inv_mul).symm
    _ ≤ ∑ _q : Layer × Index, cfFracOf (k'CellsP pub v).card (hCellsP pub v).card
          (Fintype.card Z) (Fintype.card X) (cwCount * 2 ^ 960) :=
        Finset.sum_le_sum fun q _ ↦ hkey q
    _ = Fintype.card (Layer × Index) * cfFracOf (k'CellsP pub v).card (hCellsP pub v).card
          (Fintype.card Z) (Fintype.card X) (cwCount * 2 ^ 960) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end count

/-! ## The failed searches at Keccak's sizes -/

section numbers

set_option exponentiation.threshold 4096 in
/-- `2^32` trials at codeword fraction `2^-14` all fail with probability at most `2^-2048`. -/
theorem exp_neg_trials_le_sph :
    Real.exp (-((2 ^ 14 : ℝ)⁻¹ * (encodingAttemptLimit : ℝ))) ≤ 1 / 2 ^ 2048 := by
  have h1 : (2 ^ 14 : ℝ)⁻¹ * (encodingAttemptLimit : ℝ) = 262144 := by
    norm_num [encodingAttemptLimit]
  rw [h1, Real.exp_neg, one_div]
  refine inv_anti₀ (by positivity) ?_
  calc (2 : ℝ) ^ 2048 ≤ Real.exp 1 ^ 2048 :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
    _ = Real.exp 2048 := by
        rw [← Real.exp_nat_mul]
        norm_num
    _ ≤ Real.exp 262144 := Real.exp_le_exp.mpr (by norm_num)

set_option exponentiation.threshold 4096 in
/-- The cell term of one search at Keccak's sizes: `2^32 · 19 · (2^50 + 2^257) + 2^64` over
`2^512`, at most `20 · 2^-223`. -/
theorem cfTerm_le {k h cZ : ℕ} (hk : k ≤ 2 ^ 50 + 2 ^ 257) (hh : h ≤ 2 ^ 50 + 2 ^ 257)
    (hZ : cZ = 2 ^ 512) :
    ((encodingAttemptLimit * (18 * k + h) + encodingAttemptLimit * encodingAttemptLimit : ℕ) :
      ℝ≥0∞) / cZ ≤ ENNReal.ofReal (20 / 2 ^ 223) := by
  subst hZ
  have hK : encodingAttemptLimit * (18 * k + h) + encodingAttemptLimit * encodingAttemptLimit ≤
      20 * 2 ^ 289 :=
    calc encodingAttemptLimit * (18 * k + h) + encodingAttemptLimit * encodingAttemptLimit
        ≤ 2 ^ 32 * (18 * (2 ^ 50 + 2 ^ 257) + (2 ^ 50 + 2 ^ 257)) + 2 ^ 32 * 2 ^ 32 := by
          rw [show encodingAttemptLimit = 2 ^ 32 from rfl]
          gcongr
      _ ≤ 20 * 2 ^ 289 := by norm_num
  rw [natCast_div_eq_ofReal _ (2 ^ 512) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc ((encodingAttemptLimit * (18 * k + h) + encodingAttemptLimit * encodingAttemptLimit : ℕ) :
        ℝ) / ((2 ^ 512 : ℕ) : ℝ) ≤ (20 * 2 ^ 289) / 2 ^ 512 := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hK) (by positivity)
    _ = 20 / 2 ^ 223 := by norm_num

/-- **One search's failure fraction at Keccak's sizes**, for at most `2^50 + 2^257` cells of each
kind, `2^512` capacities and a codeword fraction at least `2^-14`. -/
theorem cfFracOf_le {k h cZ cX cw : ℕ} (hk : k ≤ 2 ^ 50 + 2 ^ 257) (hh : h ≤ 2 ^ 50 + 2 ^ 257)
    (hZ : cZ = 2 ^ 512) (hcw : cw ≤ cX) (hX : 0 < cX) (hρ : (2 ^ 14 : ℝ)⁻¹ ≤ (cw : ℝ) / cX) :
    cfFracOf k h cZ cX cw ≤ ENNReal.ofReal (20 / 2 ^ 223) + ENNReal.ofReal (1 / 2 ^ 2048) :=
  add_le_add (cfTerm_le hk hh hZ) ((natCast_pow_sub_div_le_exp cX cw encodingAttemptLimit hcw hX
    (2 ^ 14 : ℝ)⁻¹ hρ).trans (ENNReal.ofReal_le_ofReal exp_neg_trials_le_sph))

/-- The reveals of the challenge prefix: one for the root, nine per signing request. -/
theorem gameCalls_reveals (q : ℕ) : gameCalls 0 0 0 1 q = 1 + 9 * signatureLimit := by
  simp only [gameCalls, signCalls, forsCalls, layerCalls]
  ring

theorem card_prod_fin (a b : ℕ) : Fintype.card (Fin a × Fin b) = a * b := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- The keys of the signatures: `3 · 2^26`. -/
theorem card_layer_index : Fintype.card (Layer × Index) = 3 * 2 ^ 26 :=
  card_prod_fin layerCount (2 ^ indexBits)

/-- **The failed-search constant**: `2^-157` per hidden value. -/
noncomputable def cfEps : ℝ≥0∞ := ENNReal.ofReal (1 / 2 ^ 157)

set_option exponentiation.threshold 4096 in
/-- **The failure fraction at Keccak's sizes**: `1 + 9 · signatureLimit` reveals times the
`3 · 2^26` keys' failure fractions, each at most `20 · 2^-223 + 2^-2048`: at most `2^-157`. -/
theorem failFrac_le_keccak_sph {a : ℝ≥0∞}
    (ha : a ≤ ENNReal.ofReal (20 / 2 ^ 223) + ENNReal.ofReal (1 / 2 ^ 2048)) :
    ((1 + 9 * signatureLimit : ℕ) : ℝ≥0∞) * (((3 * 2 ^ 26 : ℕ) : ℝ≥0∞) * a) ≤ cfEps := by
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl ha)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_natCast (1 + 9 * signatureLimit), ← ENNReal.ofReal_natCast (3 * 2 ^ 26),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), cfEps]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num [signatureLimit]

end numbers

/-! ## The failed searches and the averaged codeword-recorded mass -/

section final

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- The reveals of the realized challenge prefix: at most `1 + 9 · signatureLimit`. -/
theorem hR_prefixR (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (prefixR pol A p v) (portCharge (rCharge Selections 0 0 0 1))
      (1 + 9 * signatureLimit) := by
  have h := chg_realizeT_gameT (M := Selections) 0 0 0 1 cwUpd pol A hperm hsign p v
  rw [gameT_eq_prefixT_bind, realizeT_bind₂, gameCalls_reveals] at h
  exact isChargeBound_of_bind₂ h

open scoped Classical in
/-- **The repeated-disclosure masses at one hidden value**: at most `1 + 9 · signatureLimit` times
the fraction of the total tables failing a search off the programmable cells. -/
theorem totalWeight_reRevW_le_frac (pol : DigestPolicy) (hpol : pol.ValFree) (p : Pub)
    (v : (s : HPos) → XD s) :
    (runtimeR m0R).totalWeight .instruments reRevW (prefixR pol A p v) initR ≤
      ((1 + 9 * signatureLimit : ℕ) : ℝ≥0∞) *
        (((Finset.univ.filter fun t ↦
          FailDb p.perm p.seed (cellsHw (ProgCell p v)) v (ofFunDbs t)).card : ℝ≥0∞) /
            Fintype.card ((Z → X) × (X → Z) × (X → Z))) := by
  refine (totalWeight_reRevW_le pol hpol p v A (hR_prefixR hperm hsign pol p v)).trans
    (mul_le_mul' le_rfl ?_)
  refine (le_of_eq (potential_hwDecProj_init m0R
    (failSet p.perm p.seed (cellsHw (ProgCell p v)) v)
    (FailDb p.perm p.seed (cellsHw (ProgCell p v)) v) (fun _ ↦ Iff.rfl) _ ?_)).trans ?_
  · exact (SubState.basis _).posSemidef
  · exact (mul_le_mul' (ENNReal.ofReal_le_one.mpr (SubState.basis _).trace_re_le_one)
      le_rfl).trans_eq (one_mul _)

open scoped Classical in
/-- **The failed searches** (`CwReView` at `cfEps = 2^-157`), for a digest policy revealing no
value and `PermGood p.perm 18`: per hidden value off trial blocks, `totalWeight_reRevW_le_frac`,
`frac_failDb_le` and `failFrac_le_keccak_sph`. -/
theorem cwReView_cf (pol : DigestPolicy) (hpol : pol.ValFree) (p : Pub)
    (hπ : PermGood p.perm 18) : CwReView pol A p cfEps := by
  unfold CwReView
  calc ∑ v : (s : HPos) → XD s, (if TrialsOff p.xw p.keys.1 (valsOf v) then
        (runtimeR m0R).totalWeight .instruments reRevW (prefixR pol A p v) initR else 0)
      ≤ ∑ _v : (s : HPos) → XD s, cfEps := Finset.sum_le_sum fun v _ ↦ by
        split_ifs with hoff
        · refine (totalWeight_reRevW_le_frac hperm hsign pol hpol p v).trans
            ((mul_le_mul' le_rfl (frac_failDb_le p v hπ hoff)).trans ?_)
          rw [card_layer_index]
          exact failFrac_le_keccak_sph (cfFracOf_le (card_k'CellsP_le p v) (card_hCellsP_le p v)
            rnCard_Z cwCount_mul_le_card_X_sph Fintype.card_pos
            (inv_two_pow_14_le_rhoCw.trans_eq cwCount_mul_div_card_X.symm))
        · exact zero_le
    _ = cfEps * Fintype.card ((s : HPos) → XD s) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

open scoped Classical in
/-- **The averaged codeword-recorded mass** over the hidden values off trial blocks: at most
`cwRevTau q cfEps`, for a digest policy revealing no value (`msgPol`, `strPol`) and
`PermGood p.perm 18`. -/
theorem uavg_cwRecPre_le (pol : DigestPolicy) (hpol : pol.ValFree) (p : Pub)
    (hπ : PermGood p.perm 18) :
    uavg (fun v : (s : HPos) → XD s ↦ if TrialsOff p.xw p.keys.1 (valsOf v) then
      cwRecPre pol A p v else 0) ≤ cwRevTau q cfEps :=
  uavg_cwRecPre_le_rev hperm hsign pol p (cwReView_cf hperm hsign pol hpol p hπ)

end final

end Quantum.Sphincs.Assembly

end
