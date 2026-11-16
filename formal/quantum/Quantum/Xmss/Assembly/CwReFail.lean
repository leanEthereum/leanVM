module

public import Quantum.Xmss.Assembly.CwRev
public import Quantum.Xmss.Assembly.TrialHitUniform
public import Quantum.Sponge.Oracle.Hardwired.Persistence

@[expose] public section

/-!
# The failed searches

CwRev's remaining hypothesis `CwReView A ε`: the mass at the repeated reveals of a label whose key
is still unselected.

* **Modes that see the stop** (`stRdNx`, `CwMode.Rest`, `RevOk`, `modedP_prefixR_st`): CwRec's
  search modes, except that a trial's `h`-read whose digest is a codeword ends the search (the
  search returns), and that the calls between searches (sponge, program and record calls) happen
  only in a rest mode (free, or after the last trial), the reveals revealing one randomizer base
  or none.
* **The invariant in the decompressed basis** (`TB`, `FInv`, `fInv_step`, `init_fInv`,
  `forallQueries_dec_moded`): no empty cell, the hardwired cells inside a static `W₀`, and every
  revealed label whose key is unselected has every trial already run touching `W₀` or failing,
  on the decompressed databases (which only programs change, at cells of `W₀`).
* **The repeated reveals** (`reRevW_le`, `totalWeight_reRevW_le`): a repeated reveal with the key
  unselected lies in the database event `failSet` (some label fails all its trials); the
  decompressed projector of that event commutes with every called port
  (`runtimeR_commute_hwDecProj`), so the record charges against it add up to the record bound times
  its initial weight (`totalWeight_charge_potential_le`), which is its fraction of the total tables
  (`potential_hwDecProj_init`).
* **Counting** (`frac_fail_le`): one search fails on at most
  `N (G |K'| + |H|) / |Z| + N² / |Z| + (g / |X|)^N` of the tables, `g = |X| - cwCount 2^960`.
* **The in-table cells** (`slotHw`, `k'CellsV`, `hCellsV`, `card_k'CellsV_le`, `card_hCellsV_le`):
  the intended `W₀`, at most `8 · 498 · 2^32` cells of each kind.
-/

universe u v w w' w₁

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid

/-! ## Modes that see the stop -/

section stModes

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- A mode between searches: free, or after the last trial of a search. -/
def CwMode.Rest : CwMode → Prop
  | .free => True
  | .grd _ _ j => j = randomizerAttemptLimit
  | _ => False

/-- A reveal the searches allow: one randomizer base, or none. -/
def RevOk (T : Finset HPos) : Prop :=
  (∃ lab : RLabel, T = {.inr lab}) ∨ ∀ lab : RLabel, (Sum.inr lab : HPos) ∉ T

theorem cwRevLab_eq_none {T : Finset HPos} (h : ∀ lab : RLabel, (Sum.inr lab : HPos) ∉ T) :
    cwRevLab T = none := by
  rcases hT : cwRevLab T with _ | lab
  · rfl
  · exact absurd (by rw [cwRevLab_spec hT]; exact Finset.mem_singleton_self _) (h lab)

theorem cwRevNx_none {T : Finset HPos} (h : ∀ lab : RLabel, (Sum.inr lab : HPos) ∉ T)
    (bse : RLabel → Randomizer) : cwRevNx T bse = .free := by
  unfold cwRevNx
  rw [cwRevLab_eq_none h]
  rfl

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter)

/-- The mode after a read: as CwRec's `cwRdNx`, except that a trial's `h`-read whose digest is a
codeword ends the search. -/
noncomputable def stRdNx {M' : Type} : CwMode → (c : HwRead X Z M') → c.Result → CwMode
  | .grd lab base j, .readK _ _, r => .afK lab base j (r.1.getD 0)
  | .afK lab base j a, .readK' _ _, r => .afK' lab base j (π (cwBlk P lab base j, a)).1
      ((π (cwBlk P lab base j, a)).2 + r.1.getD 0)
  | .afK' lab base j xi _, .readH _ _, r =>
      if Codeword.Valid (trunc128 (xi + r.1.getD 0)) then .free else .grd lab base (j + 1)
  | _, _, _ => .free

/-- The calls the modes allow, on runtime 1's ports. -/
noncomputable def stOkR {M : Type} (hu : RLabel → X → X → M → Option X → M) :
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
    (hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M) :
    CwMode → (XSpec M).Port → Prop
  | μ, .inl (.inl (.inr c)) => cwRdOk π P hu μ c.1
  | μ, .inr T => μ.Rest ∧ RevOk T
  | μ, _ => μ.Rest

/-- The mode after a call of the template. -/
noncomputable def stNxT {M : Type} :
    CwMode → (i : (XSpec M).Port) → (XSpec M).Result i → CwMode
  | μ, .inl (.inl (.inr c)), r => stRdNx π P μ c.1 r
  | _, .inr T, r => cwRevNx T fun lab ↦ extendBase r.1 lab
  | _, _, _ => .free

/-- The calls the modes allow, on runtime 2's ports with record ports. -/
noncomputable def stOkZ {M : Type}
    (hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M) :
    CwMode → (recHwSpec X Z HPos M).Port → Prop
  | μ, .inl (.inl (.inr c)) => cwRdOk π P hu μ c
  | μ, .inr T => μ.Rest ∧ RevOk T
  | μ, _ => μ.Rest

/-- The mode after a call of runtime 2 with record ports, at the hidden values `v`. -/
noncomputable def stNxZ {M : Type} (v : HPos → Digest) :
    CwMode → (i : (recHwSpec X Z HPos M).Port) → (recHwSpec X Z HPos M).Result i → CwMode
  | μ, .inl (.inl (.inr c)), r => stRdNx π P μ c r
  | _, .inr T, _ => cwRevNx T fun lab ↦ v (.inr lab)
  | _, _, _ => .free

variable {M : Type} {π P}

theorem modedP_readCall_st {hu : RLabel → X → X → M → Option X → M} {μ : CwMode}
    {c : HwRead X Z M} (h : cwRdOk π P hu μ c) (B : QReg) :
    ModedP (L := LocalSig.instruments) (stOkR π P hu) (stNxR π P)
      (fun p μ' ↦ μ' = stRdNx π P μ c p.2.2) μ (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

variable (π P) in
/-- A stateful program of runtime 1 that is moded from every state. -/
def SSMod (hu : RLabel → X → X → M → Option X → M) {B : QReg} {σ α : Type} (μ : CwMode)
    (F : α → CwMode → Prop) (x : StateT σ (QComp (hwReadSpec X Z M) B B) α) : Prop :=
  ∀ s, ModedP (L := LocalSig.instruments) (stOkR π P hu) (stNxR π P)
    (fun p μ' ↦ F p.2.2.1 μ') μ (x.run s)

section smod

variable {hu : RLabel → X → X → M → Option X → M} {B : QReg} {σ α β : Type}

theorem sSMod_bind {x : StateT σ (QComp (hwReadSpec X Z M) B B) α}
    {k : α → StateT σ (QComp (hwReadSpec X Z M) B B) β} {μ : CwMode} {F : α → CwMode → Prop}
    {G : β → CwMode → Prop} (hx : SSMod π P hu μ F x)
    (hk : ∀ a μ', F a μ' → SSMod π P hu μ' G (k a)) : SSMod π P hu μ G (x >>= k) := by
  intro s
  rw [StateT.run_bind]
  exact modedP₂_bind (F := fun (q : α × σ) μ ↦ F q.1 μ) (F' := fun (q : β × σ) μ ↦ G q.1 μ) _ _
    (hx s)
    fun p μ' h ↦ hk p.1 μ' h p.2

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

theorem sSMod_rdK {lab : RLabel} {base : Randomizer} {j : ℕ} {x : X}
    (hj : j < randomizerAttemptLimit) (hx : x = cwBlk P lab base j) :
    SSMod π P hu (.grd lab base j) (fun a (μ : CwMode) ↦ μ = .afK lab base j a)
      (rdK (M := M) B x) :=
  fun s ↦ modedP₂_bind
    (F := fun r : Option Z × M ↦ fun (μ : CwMode) ↦ μ = .afK lab base j (r.1.getD 0))
    (F' := fun q : Z × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦ μ = .afK lab base j q.1)
    (readCall (.readK x keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k x (r.1.getD 0)]))
    (modedP_readCall_st (μ := .grd lab base j) (c := .readK x keepMem) ⟨hj, hx, rfl⟩ B)
    fun _ _ h ↦ h

theorem sSMod_rdK' {lab : RLabel} {base : Randomizer} {j : ℕ} {a : Z} {y : X}
    (hy : y = (π (cwBlk P lab base j, a)).1) :
    SSMod π P hu (.afK lab base j a) (fun c (μ : CwMode) ↦
      μ = .afK' lab base j (π (cwBlk P lab base j, a)).1 ((π (cwBlk P lab base j, a)).2 + c))
      (rdK' (M := M) B y) :=
  fun s ↦ modedP₂_bind (F := fun r : Option Z × M ↦ fun (μ : CwMode) ↦ μ = .afK' lab base j
      (π (cwBlk P lab base j, a)).1 ((π (cwBlk P lab base j, a)).2 + r.1.getD 0))
    (F' := fun q : Z × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦ μ = .afK' lab base j
      (π (cwBlk P lab base j, a)).1 ((π (cwBlk P lab base j, a)).2 + q.1))
    (readCall (.readK' y keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k' y (r.1.getD 0)]))
    (modedP_readCall_st (μ := .afK lab base j a) (c := .readK' y keepMem) ⟨hy, rfl⟩ B)
    fun _ _ h ↦ h

/-- The mode after a trial's `h`-read with value `w`: free if its digest is a codeword. -/
noncomputable def stopMode (lab : RLabel) (base : Randomizer) (j : ℕ) (d : X) : CwMode :=
  if Codeword.Valid (trunc128 d) then .free else .grd lab base (j + 1)

theorem sSMod_rdHU {lab : RLabel} {base : Randomizer} {j : ℕ} {xi : X} {z z' : Z}
    {u : M → Option X → M} (hz : z' = z) (hu' : u = hu lab (cwBlk P lab base j) xi) :
    SSMod π P hu (.afK' lab base j xi z) (fun w (μ : CwMode) ↦ μ = stopMode lab base j (xi + w))
      (rdHU M B z' u) :=
  fun s ↦ modedP₂_bind
    (F := fun r : Option X × M ↦ fun (μ : CwMode) ↦ μ = stopMode lab base j (xi + r.1.getD 0))
    (F' := fun q : X × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦
      μ = stopMode lab base j (xi + q.1))
    (readCall (.readH z' u) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.h z' (r.1.getD 0)]))
    (modedP_readCall_st (μ := .afK' lab base j xi z) (c := .readH z' u) ⟨hz, hu'⟩ B)
    fun _ _ h ↦ h

end smod

/-- **A trial's round of reads**, ending in the stop mode of its digest. -/
theorem sSMod_rdRoundU (upd : TrialUpd M) {B : QReg} {lab : RLabel} {base : Randomizer} {j : ℕ}
    (hj : j < randomizerAttemptLimit) {b : X} (hb : b = cwBlk P lab base j) :
    SSMod π P (cwHu1 upd) (.grd lab base j) (fun s (μ : CwMode) ↦ μ = stopMode lab base j s.1)
      (rdRoundU M (upd lab.layer lab.key) π B (0, 0) b) := by
  unfold rdRoundU
  refine sSMod_bind (sSMod_rdK hj (by simp [hb])) fun a μ ha ↦ ?_
  subst ha
  refine sSMod_bind (sSMod_rdK' (a := a) (by simp [hb])) fun c μ hc ↦ ?_
  subst hc
  refine sSMod_bind (sSMod_rdHU (by simp [hb]) (by simp [cwHu1, hb])) fun w μ hw ↦ ?_
  refine sSMod_pure _ ?_
  rw [hw]
  simp [hb]

/-- **A trial's hash** of a one-block input whose block is the trial's, ending in the stop mode
of its output's digest. -/
theorem modedP_hashTrial_st (upd : TrialUpd M) {B : QReg} {lab : RLabel} {base : Randomizer}
    {j : ℕ} (hj : j < randomizerAttemptLimit) (input : HashInput)
    (hb : blocks input = [cwBlk P lab base j]) :
    ModedP (L := LocalSig.instruments) (stOkR π P (cwHu1 upd)) (stNxR π P)
      (fun p (μ : CwMode) ↦ μ = if Codeword.Valid (truncateHash p.2.2) then .free
        else .grd lab base (j + 1)) (.grd lab base j)
      (hashTrial M (upd lab.layer lab.key) π B input) := by
  have hfold : SSMod π P (cwHu1 upd) (B := B) (.grd lab base j)
      (fun s (μ : CwMode) ↦ μ = stopMode lab base j s.1)
      ((blocks input).foldlM (rdRoundU M (upd lab.layer lab.key) π B) (0, 0)) := by
    rw [hb]
    exact sSMod_bind (sSMod_rdRoundU upd hj rfl) fun s' μ h ↦ sSMod_pure s' h
  exact modedP_map (F := fun out (μ : CwMode) ↦ μ = if Codeword.Valid (truncateHash out) then
      .free else .grd lab base (j + 1)) Prod.fst
    (sSMod_map (F := fun out (μ : CwMode) ↦ μ = if Codeword.Valid (truncateHash out) then
      .free else .grd lab base (j + 1)) (out256 : X → HashOutput)
      (sSMod_map (F := fun x (μ : CwMode) ↦ μ = if Codeword.Valid (truncateHash (out256 x)) then
        .free else .grd lab base (j + 1)) (fun s : X × Z ↦ s.1) hfold) [])

theorem codeword_decode_eq_none {d : Digest} (h : Codeword.decode d = none) :
    ¬ Codeword.Valid d := fun hv ↦ by
  unfold Codeword.decode at h
  rw [ite_eq_left hv] at h
  exact Option.some_ne_none _ h

theorem codeword_valid_of_decode {d : Digest} {x : Encoding} (h : Codeword.decode d = some x) :
    Codeword.Valid d := by
  by_contra hv
  unfold Codeword.decode at h
  rw [ite_eq_right hv] at h
  exact Option.some_ne_none x h.symm

/-- **The randomizer search** of a label from its base, from its trial `trial` to the last,
ends in a rest mode: free after a codeword, after the last trial otherwise. -/
theorem modedP_grindR_st (upd : TrialUpd M) (pub : Pub) {B : QReg} (lab : RLabel)
    (base : Randomizer) :
    ∀ n trial, trial + n = randomizerAttemptLimit →
      ModedP (L := LocalSig.instruments) (stOkR pub.perm pub.param (cwHu1 upd))
      (stNxR pub.perm pub.param) (fun _ (μ : CwMode) ↦ μ.Rest) (.grd lab base trial)
      (grindR M upd pub B lab.layer lab.key lab.msg base n trial)
  | 0, trial, hn => by
    show CwMode.Rest (.grd lab base trial)
    exact (Nat.add_zero trial).symm.trans hn
  | n + 1, trial, hn => by
    rw [grindR]
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp (length_blocks_trial pub.param
      (hashDomainFields (.message lab.layer lab.key)) (RLabel.length_msg_le lab) base trial)
    have hbk : cwBlk pub.param lab base trial = b := by simp [cwBlk, hb]
    refine modedP₂_bind (F := fun out (μ : CwMode) ↦ μ = if Codeword.Valid (truncateHash out)
        then .free else .grd lab base (trial + 1))
      (F' := fun _ (μ : CwMode) ↦ μ.Rest) _ _
      (modedP_hashTrial_st upd (by omega) _ (hb.trans (by rw [hbk]))) fun out μ hμ ↦ ?_
    show ModedP _ _ _ _ (match Codeword.decode (truncateHash out) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindR M upd pub B lab.layer lab.key lab.msg base n (trial + 1))
    split
    · next x hx =>
      rw [hμ, ite_eq_left (codeword_valid_of_decode hx)]
      trivial
    · next hx =>
      rw [hμ, ite_eq_right (codeword_decode_eq_none hx)]
      exact modedP_grindR_st upd pub lab base n (trial + 1) (by omega)

/-- **Lifting runtime 1's moded programs to templates.** -/
theorem modedP_readLift_st {hu : RLabel → X → X → M → Option X → M} {Ω : QReg → Type}
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
        rcases μ with _ | ⟨lab, base, j⟩ | ⟨lab, base, j, a⟩ | ⟨lab, base, j, xi, z'⟩ <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

/-- A sponge program of runtime 1 is moded between searches. -/
theorem modedP_liftOrdinary_st {hu : RLabel → X → X → M → Option X → M} {Ω : QReg → Type}
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

theorem stNxZ_rec_eq (v : HPos → Digest) (μ : CwMode) (T : Finset HPos)
    (m : Finset HPos × M) :
    stNxZ (M := M) π P v μ (.inr T) m = stNxT π P μ (.inr T) (restrictTo T v, m) :=
  cwRevNx_congr fun lab hl ↦ (extendBase_restrictTo
    (by rw [cwRevLab_spec hl]; exact Finset.mem_singleton_self _) v).symm

/-- **Realizing keeps the modes.** -/
theorem modedP_realizeT_st {hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M}
    (v : HPos → Digest) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → CwMode → Prop} (y : QuantumComp L (XSpec M) Ω A)
    {μ : CwMode} (hy : ModedP (stOkT π P hu) (stNxT π P) fin μ y) :
    ModedP (stOkZ π P hu) (stNxZ π P v) fin μ (realizeT v y) := by
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
      exact (congrArg (fun μ' ↦ ModedP (stOkZ π P hu) (stNxZ π P v) fin μ' _)
        (stNxZ_rec_eq (π := π) (P := P) v μ T b.down)).mpr h

/-! ### The challenge prefix is moded -/

variable (π P) in
/-- A template moded between searches: from every rest mode, it ends in a rest mode. -/
def SRest (hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M)
    {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments (XSpec M) Ω A) : Prop :=
  ∀ μ : CwMode, μ.Rest → ModedP (stOkT π P hu) (stNxT π P) (fun _ (μ : CwMode) ↦ μ.Rest) μ y

variable {hu : RLabel → X → X → Finset HPos × M → Option X → Finset HPos × M}

theorem sRest_bind {A B B' : QReg} {α β : Type} (x : QComp (XSpec M) A B α)
    (g : α → QComp (XSpec M) B B' β) (hx : SRest π P hu x) (hg : ∀ a, SRest π P hu (g a)) :
    SRest π P hu (x.bind g) :=
  fun μ hμ ↦ modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Rest) (F' := fun _ (μ : CwMode) ↦ μ.Rest)
    x g (hx μ hμ) fun a μ' h ↦ hg a μ' h

theorem sRest_pure {A : QReg} {α : Type} (a : α) :
    SRest π P hu (QuantumComp₂.pure (L := LocalSig.instruments) (spec := XSpec M) (A := A) a) :=
  fun _ h ↦ h

theorem sRest_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    SRest π P hu (QComp.act (spec := XSpec M) p) :=
  fun _ hμ ↦ ⟨trivial, fun _ ↦ hμ⟩

/-- A reveal of no randomizer base keeps the search modes free. -/
theorem sRest_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (hT : ∀ lab : RLabel, (Sum.inr lab : HPos) ∉ T)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B B' α)
    (hk : ∀ r, SRest π P hu (k r)) : SRest π P hu (revealThen goodAll T k) := by
  intro μ hμ
  refine ⟨⟨hμ, .inr hT⟩, fun b ↦ ?_⟩
  have he : stNxT (M := M) π P μ (.inr T) b.down = .free := cwRevNx_none hT _
  rw [show modeCmdNx (stNxT (M := M) π P) (QuantumComp.Cmd.query (L := LocalSig.instruments)
    (.inr T) B _) μ b = stNxT (M := M) π P μ (.inr T) b.down from rfl, he]
  exact sRest_bind _ _ (sRest_act _) (fun _ ↦ hk b.down) _ trivial

/-- The reveal of a label's randomizer base starts its search. -/
theorem sRest_revealLab {B B' : QReg} {α : Type} (lab : RLabel)
    (k : RevealVals XD {.inr lab} × (Finset HPos × M) → QComp (XSpec M) B B' α)
    (hk : ∀ r, ModedP (stOkT π P hu) (stNxT π P) (fun _ (μ : CwMode) ↦ μ.Rest)
      (.grd lab (extendBase r.1 lab) 0) (k r)) :
    SRest π P hu (revealThen goodAll {.inr lab} k) := by
  intro μ hμ
  refine ⟨⟨hμ, .inl ⟨lab, rfl⟩⟩, fun b ↦ ?_⟩
  have he : stNxT (M := M) π P μ (.inr {.inr lab}) b.down =
      .grd lab (extendBase b.down.1 lab) 0 :=
    cwRevNx_lab lab _
  rw [show modeCmdNx (stNxT (M := M) π P) (QuantumComp.Cmd.query (L := LocalSig.instruments)
    (.inr {.inr lab}) B _) μ b = stNxT (M := M) π P μ (.inr {.inr lab}) b.down from rfl, he]
  exact modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ = .grd lab (extendBase b.down.1 lab) 0)
    (F' := fun _ (μ : CwMode) ↦ μ.Rest) _ _ ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ h ▸ hk b.down

theorem sRest_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec M) B B' α) (hk : SRest π P hu k) : SRest π P hu (progThen p hp k) :=
  fun _ hμ ↦ ⟨hμ, fun _ ↦ sRest_bind _ _ (sRest_act _) (fun _ ↦ hk) _ trivial⟩

theorem sRest_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    SRest π P hu (progPorts M B ps) := by
  induction ps with
  | nil => exact sRest_pure _
  | cons p ps ih => exact sRest_progThen p trivial _ ih

theorem sRest_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    SRest π P hu (progSlots M pub B ss) := by
  induction ss with
  | nil => exact sRest_pure _
  | cons s ss ih => exact sRest_bind _ _ (sRest_progPorts B _) fun _ ↦ ih

variable (upd : TrialUpd M)

theorem sRest_signLayerT (pub : Pub) (B : QReg) (lab : RLabel) :
    SRest pub.perm pub.param (cwLiftHu (cwHu1 upd)) (signLayerT M upd pub B lab) := by
  refine sRest_revealLab lab _ fun r₀ ↦ ?_
  refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Rest) (F' := fun _ (μ : CwMode) ↦ μ.Rest) _ _
    (modedP_readLift_st _ (modedP_grindR_st upd pub lab _ _ _ (by omega))) fun g μ hμ ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · exact hμ
  · exact sRest_revealThen _ (fun _ ↦ inr_not_mem_inlSet) _ (fun r ↦ sRest_bind _ _
      (sRest_progSlots pub B _) fun _ ↦ sRest_pure _) μ hμ

theorem sRest_signT (pub : Pub) (B : QReg) (r : SigningRequest) :
    SRest pub.perm pub.param (cwLiftHu (cwHu1 upd)) (signT M upd pub B r) := by
  refine sRest_bind _ _ (sRest_signLayerT upd pub B _) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · exact sRest_pure _
  · refine sRest_bind _ _ (sRest_signLayerT upd pub B _) fun t ↦ ?_
    rcases t with _ | ⟨top, _⟩ <;> exact sRest_pure _

theorem sRest_challengeT (pub : Pub) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    ∀ μ : CwMode, μ.Rest → ModedP (stOkT pub.perm pub.param (cwLiftHu (cwHu1 upd)))
      (stNxT pub.perm pub.param) (fun _ (μ : CwMode) ↦ μ.Rest) μ (challengeT M upd pub A c) := by
  intro μ hμ
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact modedP_readLift_st _ (modedP_liftOrdinary_st _ μ hμ)
  · exact modedP_readLift_st _ (modedP_liftOrdinary_st _ μ hμ)
  · exact modedP_bind _ _ (sRest_bind _ _ (sRest_act _) (fun _ ↦ sRest_signT upd pub _ r) μ hμ)
      fun _ _ μ' h ↦ h

/-- Substituting trees moded between searches. -/
theorem modedP_substitute_st {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (XSpec M)))
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
theorem sRest_prefixT (pub : Pub) (A : Adversary (X × Z)) :
    SRest pub.perm pub.param (cwLiftHu (cwHu1 upd)) (prefixT M upd pub A) :=
  sRest_revealThen _ (fun _ h ↦ by simp at h) _ fun _ ↦ sRest_bind _ _
    (modedP_substitute_st _ (sRest_challengeT upd pub) _) fun _ ↦ sRest_pure _

/-- **The realized challenge prefix is moded**, from the free mode. -/
theorem modedP_prefixR_st (pub : Pub) (A : Adversary (X × Z)) (v : HPos → Digest) :
    ModedP (stOkZ pub.perm pub.param (cwLiftHu (cwHu1 upd))) (stNxZ pub.perm pub.param v)
      (fun _ (μ : CwMode) ↦ μ.Rest) .free (realizeT v (prefixT M upd pub A)) :=
  modedP_realizeT_st v _ (sRest_prefixT upd pub A .free trivial)

end stModes

/-! ## The trials on the decompressed databases -/

section chain

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter) (W₀ : Hw X Z)

/-- The `k`-value of trial `j` of the search of `lab` from `b` on the databases `D`. -/
noncomputable def trA (lab : RLabel) (b : Randomizer) (j : ℕ) (D : DbReg X Z) : Z :=
  (D.2.1 (cwBlk P lab b j)).getD 0

/-- The rate of the trial after `π`: its `k'`-cell. -/
noncomputable def trY (lab : RLabel) (b : Randomizer) (j : ℕ) (D : DbReg X Z) : X :=
  (π (cwBlk P lab b j, trA P lab b j D)).1

/-- The `h`-cell of the trial. -/
noncomputable def trZ (lab : RLabel) (b : Randomizer) (j : ℕ) (D : DbReg X Z) : Z :=
  (π (cwBlk P lab b j, trA P lab b j D)).2 + (D.2.2 (trY π P lab b j D)).getD 0

/-- The `h`-value of the trial. -/
noncomputable def trW (lab : RLabel) (b : Randomizer) (j : ℕ) (D : DbReg X Z) : X :=
  (D.1 (trZ π P lab b j D)).getD 0

/-- **Trial `j` touches `W₀` or fails**: its `k`-, `k'`- or `h`-cell is a cell of `W₀`, or its
digest is no codeword. -/
def TB (lab : RLabel) (b : Randomizer) (j : ℕ) (D : DbReg X Z) : Prop :=
  W₀.2.1 (cwBlk P lab b j) ≠ none ∨ W₀.2.2 (trY π P lab b j D) ≠ none ∨
    W₀.1 (trZ π P lab b j D) ≠ none ∨
      ¬ Codeword.Valid (trunc128 (trY π P lab b j D + trW π P lab b j D))

/-- Two database triples agree at every cell outside `W₀`. -/
def DbOffAgree (D D' : DbReg X Z) : Prop :=
  (∀ z, W₀.1 z = none → D.1 z = D'.1 z) ∧ (∀ x, W₀.2.1 x = none → D.2.1 x = D'.2.1 x) ∧
    ∀ x, W₀.2.2 x = none → D.2.2 x = D'.2.2 x

/-- `TB` looks at the databases outside `W₀` only. -/
theorem tB_of_offAgree {D D' : DbReg X Z} (h : DbOffAgree W₀ D D') {lab : RLabel}
    {b : Randomizer} {j : ℕ} (hT : TB π P W₀ lab b j D) : TB π P W₀ lab b j D' := by
  unfold TB at hT ⊢
  by_cases hk : W₀.2.1 (cwBlk P lab b j) = none
  swap
  · exact Or.inl hk
  have ha : trA P lab b j D' = trA P lab b j D := by
    unfold trA
    rw [h.2.1 _ hk]
  have hy : trY π P lab b j D' = trY π P lab b j D := by
    unfold trY
    rw [ha]
  rw [hy]
  by_cases hk' : W₀.2.2 (trY π P lab b j D) = none
  swap
  · exact Or.inr (Or.inl hk')
  have hz : trZ π P lab b j D' = trZ π P lab b j D := by
    unfold trZ
    rw [ha, hy, ← h.2.2 _ hk']
  rw [hz]
  by_cases hh : W₀.1 (trZ π P lab b j D) = none
  swap
  · exact Or.inr (Or.inr (Or.inl hh))
  have hw : trW π P lab b j D' = trW π P lab b j D := by
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

/-- The trials of `lab` already run in the mode `μ`: those before the current trial of its search,
all of them otherwise. -/
def doneN (μ : CwMode) (lab : RLabel) : ℕ :=
  match μ with
  | .free => randomizerAttemptLimit
  | .grd l _ j => if l = lab then j else randomizerAttemptLimit
  | .afK l _ j _ => if l = lab then j else randomizerAttemptLimit
  | .afK' l _ j _ _ => if l = lab then j else randomizerAttemptLimit

theorem doneN_of_rest {μ : CwMode} (h : μ.Rest) (lab : RLabel) :
    doneN μ lab = randomizerAttemptLimit := by
  rcases μ with _ | ⟨l, b, j⟩ | ⟨l, b, j, a⟩ | ⟨l, b, j, xi, z⟩
  · rfl
  · have hj : j = randomizerAttemptLimit := h
    subst hj
    show (if l = lab then randomizerAttemptLimit else randomizerAttemptLimit) = _
    split_ifs <;> rfl
  · exact h.elim
  · exact h.elim

/-- The mode's data agree with the register: the search's base is the hidden one, and after the
trial's reads their outcomes are the decompressed values (unless the trial touched `W₀`). -/
def ModeOk (v : HPos → Digest) : CwMode → HwReg X Z Mem → Prop
  | .free, _ => True
  | .grd lab b _, _ => b = v (.inr lab)
  | .afK lab b j a, s => b = v (.inr lab) ∧
      (W₀.2.1 (cwBlk P lab b j) ≠ none ∨ a = trA P lab b j s.1)
  | .afK' lab b j xi z, s => b = v (.inr lab) ∧
      (W₀.2.1 (cwBlk P lab b j) ≠ none ∨ W₀.2.2 (trY π P lab b j s.1) ≠ none ∨
        (xi = trY π P lab b j s.1 ∧ z = trZ π P lab b j s.1))

/-- **The invariant of the failed searches**, in the decompressed basis: no empty cell, the
hardwired cells in `W₀`, the mode's data, and for every revealed label whose key is unselected,
every trial already run touched `W₀` or failed. -/
def FInv (v : HPos → Digest) (μ : CwMode) : Set (HwReg X Z Mem) :=
  {s | NoBot s ∧ HwIn W₀ s.2.1 ∧ ModeOk π P W₀ v μ s ∧
    ∀ lab : RLabel, (Sum.inr lab : HPos) ∈ s.2.2.1 → cwU lab s.2.2 →
      ∀ j < doneN μ lab, TB π P W₀ lab (v (.inr lab)) j s.1}

variable {π P W₀}

theorem fInv_free_of_rest {v : HPos → Digest} {μ : CwMode} (hμ : μ.Rest) {s : HwReg X Z Mem}
    (hs : s ∈ FInv π P W₀ v μ) : s ∈ FInv π P W₀ v .free :=
  ⟨hs.1, hs.2.1, trivial, fun lab hl hu j hj ↦
    hs.2.2.2 lab hl hu j (by rw [doneN_of_rest hμ]; exact hj)⟩

/-- A selection only goes from none to some. -/
theorem select_eq_none {m : Selections} {l l' : Layer} {e e' : KeyIndex} {x : X} {d : Digest}
    (h : m.select l e x d l' e' = none) : m l' e' = none := by
  unfold Selections.select at h
  by_cases hl : l' = l
  · subst hl
    rw [Function.update_self] at h
    by_cases he : e' = e
    · subst he
      rw [Function.update_self] at h
      exact absurd h (Option.some_ne_none _)
    · rwa [Function.update_of_ne he] at h
  · rwa [Function.update_of_ne hl] at h

theorem cwUpd_eq_none {l l' : Layer} {e e' : KeyIndex} {x xi : X} {m : Selections}
    {o : Option X} (h : cwUpd l e x xi m o l' e' = none) : m l' e' = none := by
  rcases o with _ | w
  · exact h
  · rcases cwUpd_some l e x xi m w with h' | h'
    · rwa [h'] at h
    · rw [h'] at h
      unfold cwSel at h
      split_ifs at h
      · exact select_eq_none h
      · exact h

/-- A trial read whose digest is a codeword leaves its key selected. -/
theorem cwUpd_ne_none {l : Layer} {e : KeyIndex} {x xi w : X} {m : Selections}
    (hv : Codeword.Valid (trunc128 (xi + w))) : cwUpd l e x xi m (some w) l e ≠ none := by
  by_cases hm : m l e = none
  · rw [cwUpd_some_of_none _ _ _ _ hm]
    exact fun h ↦ (cwSel_eq_none_iff hm x xi w).mp h hv
  · show (if m l e = none then cwSel m l e x xi w else m) l e ≠ none
    rw [ite_eq_right hm]
    exact hm

end chain

/-! ## The invariant along the realized prefix, in the decompressed basis -/

section decStep

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- A classical Kraus operator in the decompressed basis: a nonzero entry moves the classical
data by `φ` and the databases by the decompressed database operator. -/
theorem dec_clsKraus_ne_zero {M' : Type} [Fintype M'] [DecidableEq M']
    {p : Hw X Z × M' → Prop} {_ : DecidablePred p} {φ : Hw X Z × M' → Hw X Z × M'}
    {R : Hw X Z × M' → Matrix (DbReg X Z) (DbReg X Z) ℂ} {m' m : Unit × HwReg X Z M'}
    (h : (((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M') *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsKraus p φ R) *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M')) m' m ≠ 0) :
    p m.2.2 ∧ m'.2.2 = φ m.2.2 ∧
      (compressDbs X Z * R m.2.2 * compressDbs X Z) m'.2.1 m.2.1 ≠ 0 := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul, compressReg,
    kron_one_mul_clsKraus_mul_kron_one] at h
  have h' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) h).2
  rw [clsKraus_apply] at h'
  split_ifs at h' with hc
  · exact ⟨hc.1, hc.2, h'⟩
  · exact absurd rfl h'

/-- A sponge port in the decompressed basis keeps the register. -/
theorem dec_hwPort_snd {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] (read : HwReg X Z Mem → A → Y) (m' m : (A × Y) × HwReg X Z Mem)
    (h : (((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z Mem) * hwPort read *
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z Mem)) m' m ≠ 0) : m'.2 = m.2 := by
  rw [one_kron_mul_hwPort_mul_one_kron, tableOracle_apply] at h
  split_ifs at h with he
  · rw [he]
    rfl
  · exact absurd rfl h

theorem compressAll_one_ne_zero {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [Nonempty Y] {D' D : Database A Y}
    (h : (compressAll A Y * (1 : Matrix (Database A Y) (Database A Y) ℂ) * compressAll A Y) D' D ≠
      0) : D' = D := by
  rw [Matrix.mul_one, compressAll_mul_self] at h
  by_contra hne
  exact h (Matrix.one_apply_ne hne)

theorem dec_dbs_ne_zero {N₁ : Matrix (Database Z X) (Database Z X) ℂ}
    {N₂ N₃ : Matrix (Database X Z) (Database X Z) ℂ} {D' D : DbReg X Z}
    (h : (compressDbs X Z * (N₁ ⊗ₖ (N₂ ⊗ₖ N₃)) * compressDbs X Z) D' D ≠ 0) :
    (compressAll Z X * N₁ * compressAll Z X) D'.1 D.1 ≠ 0 ∧
      (compressAll X Z * N₂ * compressAll X Z) D'.2.1 D.2.1 ≠ 0 ∧
        (compressAll X Z * N₃ * compressAll X Z) D'.2.2 D.2.2 ≠ 0 := by
  rw [compressDbs_mul_kron_mul_compressDbs, kroneckerMap_apply, kroneckerMap_apply] at h
  exact ⟨left_ne_zero_of_mul h, left_ne_zero_of_mul (right_ne_zero_of_mul h),
    right_ne_zero_of_mul (right_ne_zero_of_mul h)⟩

theorem compressDbs_one_ne_zero {D' D : DbReg X Z}
    (h : (compressDbs X Z * (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ) * compressDbs X Z) D' D ≠ 0) :
    D' = D := by
  rw [Matrix.mul_one, compressDbs_mul_self] at h
  by_contra hne
  exact h (Matrix.one_apply_ne hne)

theorem or_eq_of_hwIn {α β : Type} {w w₀ : α → Option β} {a : α} (hw : w a ≠ none → w₀ a ≠ none)
    (h₀ : w₀ a = none) (d : Option β) : (w a).or d = d := by
  have : w a = none := by
    by_contra hne
    exact hw hne h₀
  rw [this]
  rfl

variable {π : Equiv.Perm (X × Z)} {P : PublicParameter} {W₀ : Hw X Z} {v : HPos → Digest}

/-- **A record**: a reveal of one randomizer base starts its search with no trial run; a reveal
of no randomizer base reveals no label. -/
theorem fInv_rec {μ : CwMode} (hμ : μ.Rest) {T : Finset HPos} (hT : RevOk T)
    {s s' : HwReg X Z Mem} (hs : s ∈ FInv π P W₀ v μ) (hD : s'.1 = s.1)
    (hb : s'.2 = (s.2.1, (s.2.2.1 ∪ T, s.2.2.2))) :
    s' ∈ FInv π P W₀ v (cwRevNx T fun lab ↦ v (.inr lab)) := by
  obtain ⟨hnb, hw, -, hl⟩ := hs
  have hnb' : NoBot s' := by
    show NoBotDb s'.1
    rw [hD]
    exact hnb
  have hw' : HwIn W₀ s'.2.1 := by
    rw [hb]
    exact hw
  have hmem : ∀ lab : RLabel, (Sum.inr lab : HPos) ∈ s'.2.2.1 →
      (Sum.inr lab : HPos) ∈ s.2.2.1 ∨ (Sum.inr lab : HPos) ∈ T := fun lab h ↦ by
    rw [hb] at h
    exact Finset.mem_union.mp h
  have hu : ∀ lab : RLabel, cwU lab s'.2.2 → cwU lab s.2.2 := fun lab h ↦ by
    rw [hb] at h
    exact h
  rcases hT with ⟨lab, rfl⟩ | hT
  · rw [cwRevNx_lab]
    refine ⟨hnb', hw', rfl, fun lab' hl' hu' j hj ↦ ?_⟩
    have hd : doneN (.grd lab (v (.inr lab)) 0) lab' =
        if lab = lab' then 0 else randomizerAttemptLimit := rfl
    by_cases he : lab = lab'
    · rw [hd, ite_eq_left he] at hj
      exact absurd hj (Nat.not_lt_zero j)
    · rw [hd, ite_eq_right he] at hj
      have hl1 : (Sum.inr lab' : HPos) ∈ s.2.2.1 := by
        rcases hmem lab' hl' with h | h
        · exact h
        · exact absurd (Sum.inr_injective (Finset.mem_singleton.mp h)).symm he
      rw [hD]
      exact hl lab' hl1 (hu lab' hu') j (by rw [doneN_of_rest hμ]; exact hj)
  · rw [cwRevNx_none hT]
    refine ⟨hnb', hw', trivial, fun lab' hl' hu' j hj ↦ ?_⟩
    have hl1 : (Sum.inr lab' : HPos) ∈ s.2.2.1 := by
      rcases hmem lab' hl' with h | h
      · exact h
      · exact absurd h (hT lab')
    rw [hD]
    exact hl lab' hl1 (hu lab' hu') j (by rw [doneN_of_rest hμ]; exact hj)

/-- **A program at a cell of `W₀`** keeps the invariant: the databases change at its cell only. -/
theorem fInv_prog {μ : CwMode} (hμ : μ.Rest) {c : HwProg X Z} (hc : c.CellIn W₀)
    {s s' : HwReg X Z Mem} (hs : s ∈ FInv π P W₀ v μ) (hag : DbOffAgree W₀ s.1 s'.1)
    (hnb : NoBot s') (hb : s'.2 = (progUpdate c s.2.1, s.2.2)) : s' ∈ FInv π P W₀ v .free := by
  obtain ⟨-, hw, -, hl⟩ := hs
  refine ⟨hnb, ?_, trivial, fun lab hl' hu j hj ↦ ?_⟩
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
  · have hl1 : (Sum.inr lab : HPos) ∈ s.2.2.1 := by
      rw [hb] at hl'
      exact hl'
    have hu1 : cwU lab s.2.2 := by
      rw [hb] at hu
      exact hu
    exact tB_of_offAgree π P W₀ hag (hl lab hl1 hu1 j (by rw [doneN_of_rest hμ]; exact hj))

/-- **The `k`-read of a trial**: its outcome is the decompressed value unless the block is in
`W₀`. -/
theorem fInv_readK {lab : RLabel} {b : Randomizer} {j : ℕ} {s s' : HwReg X Z Mem}
    (hs : s ∈ FInv π P W₀ v (.grd lab b j)) (hD : s'.1 = s.1) (hb : s'.2 = s.2) {o : Option Z}
    (ho : (s.2.1.2.1 (cwBlk P lab b j)).or (s.1.2.1 (cwBlk P lab b j)) = o) :
    s' ∈ FInv π P W₀ v (.afK lab b j (o.getD 0)) := by
  obtain ⟨hnb, hw, hm, hl⟩ := hs
  have hm' : ModeOk π P W₀ v (.afK lab b j (o.getD 0)) s' := by
    refine ⟨hm, ?_⟩
    by_cases hk : W₀.2.1 (cwBlk P lab b j) = none
    · refine .inr ?_
      rw [← ho, or_eq_of_hwIn (hw.2.1 _) hk, hD]
      rfl
    · exact .inl hk
  refine ⟨?_, ?_, hm', fun lab' hl' hu j' hj' ↦ ?_⟩
  · show NoBotDb s'.1
    rw [hD]
    exact hnb
  · rw [hb]
    exact hw
  · rw [hb] at hl' hu
    rw [hD]
    exact hl lab' hl' hu j' hj'

/-- **The `k'`-read of a trial.** -/
theorem fInv_readK' {lab : RLabel} {b : Randomizer} {j : ℕ} {a : Z} {s s' : HwReg X Z Mem}
    (hs : s ∈ FInv π P W₀ v (.afK lab b j a)) (hD : s'.1 = s.1) (hb : s'.2 = s.2) {o : Option Z}
    (ho : (s.2.1.2.2 (π (cwBlk P lab b j, a)).1).or (s.1.2.2 (π (cwBlk P lab b j, a)).1) = o) :
    s' ∈ FInv π P W₀ v (.afK' lab b j (π (cwBlk P lab b j, a)).1
      ((π (cwBlk P lab b j, a)).2 + o.getD 0)) := by
  obtain ⟨hnb, hw, ⟨hbase, hm⟩, hl⟩ := hs
  have hm' : ModeOk π P W₀ v (.afK' lab b j (π (cwBlk P lab b j, a)).1
      ((π (cwBlk P lab b j, a)).2 + o.getD 0)) s' := by
    refine ⟨hbase, ?_⟩
    rcases hm with hm | ha
    · exact .inl hm
    · rw [hD]
      have hy : (π (cwBlk P lab b j, a)).1 = trY π P lab b j s.1 := by
        unfold trY
        rw [ha]
      by_cases hk' : W₀.2.2 (trY π P lab b j s.1) = none
      · refine .inr (.inr ⟨hy, ?_⟩)
        rw [← ho, hy, or_eq_of_hwIn (hw.2.2 _) hk']
        unfold trZ
        rw [ha]
      · exact .inr (.inl hk')
  refine ⟨?_, ?_, hm', fun lab' hl' hu j' hj' ↦ ?_⟩
  · show NoBotDb s'.1
    rw [hD]
    exact hnb
  · rw [hb]
    exact hw
  · rw [hb] at hl' hu
    rw [hD]
    exact hl lab' hl' hu j' hj'

/-- **The `h`-read of a trial**: a codeword digest selects the key and ends the search; otherwise
the trial failed (or touched `W₀`). -/
theorem fInv_readH {lab : RLabel} {b : Randomizer} {j : ℕ} {xi : X} {z : Z}
    {s s' : HwReg X Z Mem} (hs : s ∈ FInv π P W₀ v (.afK' lab b j xi z)) (hD : s'.1 = s.1)
    {o : Option X}
    (hb : s'.2 = (s.2.1, (s.2.2.1, cwUpd lab.layer lab.key (cwBlk P lab b j) xi s.2.2.2 o)))
    (ho : (s.2.1.1 z).or (s.1.1 z) = o) :
    s' ∈ FInv π P W₀ v (if Codeword.Valid (trunc128 (xi + o.getD 0)) then .free
      else .grd lab b (j + 1)) := by
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
    rw [hb]
    exact hw
  have hrev : s'.2.2.1 = s.2.2.1 := by rw [hb]
  have hu : ∀ lab' : RLabel, cwU lab' s'.2.2 → cwU lab' s.2.2 := fun lab' h ↦ by
    rw [hb] at h
    have h2 : cwUpd lab.layer lab.key (cwBlk P lab b j) xi s.2.2.2 (some w) lab'.layer lab'.key =
      none := h
    exact cwUpd_eq_none h2
  show s' ∈ FInv π P W₀ v (if Codeword.Valid (trunc128 (xi + w)) then .free
    else .grd lab b (j + 1))
  split_ifs with hv
  · refine ⟨hnb', hw', trivial, fun lab' hl' hu' j' hj' ↦ ?_⟩
    by_cases hk : lab'.layer = lab.layer ∧ lab'.key = lab.key
    · exfalso
      have h0 : cwUpd lab.layer lab.key (cwBlk P lab b j) xi s.2.2.2 (some w) lab.layer lab.key =
          none := by
        have h1 : s'.2.2.2 lab'.layer lab'.key = none := hu'
        rw [hb, hk.1, hk.2] at h1
        exact h1
      exact cwUpd_ne_none hv h0
    · have hne : lab ≠ lab' := fun he ↦ hk ⟨he ▸ rfl, he ▸ rfl⟩
      have hd : doneN (.afK' lab b j xi z) lab' = randomizerAttemptLimit := by
        show (if lab = lab' then j else randomizerAttemptLimit) = _
        rw [ite_eq_right hne]
      rw [hrev] at hl'
      rw [hD]
      exact hl lab' hl' (hu lab' hu') j' (by rw [hd]; exact hj')
  · refine ⟨hnb', hw', hbase, fun lab' hl' hu' j' hj' ↦ ?_⟩
    rw [hrev] at hl'
    rw [hD]
    by_cases hne : lab = lab'
    · subst hne
      have hj : j' < j + 1 := by
        have h1 : doneN (.grd lab b (j + 1)) lab = j + 1 := by
          show (if lab = lab then j + 1 else randomizerAttemptLimit) = _
          rw [ite_eq_left rfl]
        rwa [h1] at hj'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · have h1 : doneN (.afK' lab b j xi z) lab = j := by
          show (if lab = lab then j else randomizerAttemptLimit) = _
          rw [ite_eq_left rfl]
        exact hl lab hl' (hu lab hu') j' (by rw [h1]; exact hj)
      · subst hj
        subst hbase
        unfold TB
        rcases hm with hm | hm | ⟨hxi, hz⟩
        · exact .inl hm
        · exact .inr (.inl hm)
        · by_cases hh : W₀.1 (trZ π P lab (v (.inr lab)) j' s.1) = none
          · refine .inr (.inr (.inr ?_))
            have hwv : trW π P lab (v (.inr lab)) j' s.1 = w := by
              unfold trW
              rw [← hz, ← or_eq_of_hwIn (hw.1 _) (hz ▸ hh) (s.1.1 z), ho]
              rfl
            rw [← hxi, hwv]
            exact hv
          · exact .inr (.inr (.inl hh))
    · have h1 : doneN (.grd lab b (j + 1)) lab' = doneN (.afK' lab b j xi z) lab' := by
        show (if lab = lab' then j + 1 else randomizerAttemptLimit) =
          (if lab = lab' then j else randomizerAttemptLimit)
        rw [ite_eq_right hne, ite_eq_right hne]
      exact hl lab' hl' (hu lab' hu') j' (by rw [← h1]; exact hj')


/-- The calls programming cells of `W₀` only. -/
def PortC (W₀ : Hw X Z) : (recHwSpec X Z HPos Selections).Port → Prop
  | .inl (.inr c) => c.CellIn W₀
  | _ => True

/-- Runtime 2 with record ports in the decompressed basis, from the initial memory. -/
noncomputable def decRM : QuantumRuntime (recHwSpec X Z HPos Selections) :=
  decR (X := X) (Z := Z) m0R

theorem decRM_branch_apply (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i)
    (K : Matrix ((recHwSpec X Z HPos Selections).Out i × HwReg X Z Mem)
      ((recHwSpec X Z HPos Selections).In i × HwReg X Z Mem) ℂ)
    (hK : ((runtimeR (X := X) (Z := Z) m0R).step i).branch r = MatrixMap.conj K)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × HwReg X Z Mem)
      ((recHwSpec X Z HPos Selections).In i × HwReg X Z Mem) ℂ) :
    (decRM.step i).branch r σ = MatrixMap.conj
      (((1 : Matrix ((recHwSpec X Z HPos Selections).Out i)
        ((recHwSpec X Z HPos Selections).Out i) ℂ) ⊗ₖ compressReg X Z Mem) * K *
        ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
          ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem)) σ :=
  decR_branch_apply m0R i r K hK σ

theorem decRM_branch (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i) :
    (decRM.step i).branch r =
      MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).Out i)
        ((recHwSpec X Z HPos Selections).Out i) ℂ) ⊗ₖ compressReg X Z Mem) ∘ₗ
        ((runtimeR (X := X) (Z := Z) m0R).step i).branch r ∘ₗ
          MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
            ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem) :=
  conjReg_branch (runtimeRH m0R) (compressReg X Z Mem) compressReg_mul_self
    conjTranspose_compressReg i r

/-- **Every allowed call keeps the invariant**, in the decompressed basis. -/
theorem fInv_step (μ : CwMode) (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × HwReg X Z Mem)
      ((recHwSpec X Z HPos Selections).In i × HwReg X Z Mem) ℂ)
    (hok : stOkZ π P (cwLiftHu (cwHu1 cwUpd)) μ i) (hc : PortC W₀ i)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
      HwReg X Z Mem ↦ m.2) (FInv π P W₀ v μ) σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).Out i ×
      HwReg X Z Mem ↦ m.2) (FInv π P W₀ v (stNxZ π P v μ i r))
      ((decRM.step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · rw [decRM_branch_apply _ r _ (runtime2_branch m0R (.inl (.inl i)) r)]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    have he : m'.2 = m.2 := by
      cases i <;> exact dec_hwPort_snd _ m' m hK
    show m'.2 ∈ FInv π P W₀ v .free
    rw [he]
    exact fInv_free_of_rest hok hm
  · rw [decRM_branch_apply _ r _ (runtime2_branch m0R (.inl (.inr c)) r)]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    rcases μ with _ | ⟨lab, b, j⟩ | ⟨lab, b, j, a⟩ | ⟨lab, b, j, xi, z⟩ <;>
      rcases c with ⟨z', u⟩ | ⟨x, u⟩ | ⟨y, u⟩
    all_goals try exact hok.elim
    · obtain ⟨-, hx, rfl⟩ := hok
      subst hx
      obtain ⟨hp, hφ, hR⟩ := dec_clsKraus_ne_zero (p := fun b' : Hw X Z × Mem ↦ b'.2 = r.2)
        (φ := fun b' ↦ (b'.1, r.2))
        (R := fun b' ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
          (cellRead b'.1.2.1 (cwBlk P lab b j) r.1 ⊗ₖ
            (1 : Matrix (Database X Z) (Database X Z) ℂ))) hK
      obtain ⟨hD, ho⟩ := compressDbs_readK_ne_zero hR
      exact fInv_readK hm hD (hφ.trans (Prod.ext rfl hp.symm)) ho
    · obtain ⟨hy, rfl⟩ := hok
      subst hy
      obtain ⟨hp, hφ, hR⟩ := dec_clsKraus_ne_zero (p := fun b' : Hw X Z × Mem ↦ b'.2 = r.2)
        (φ := fun b' ↦ (b'.1, r.2))
        (R := fun b' ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
          ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ
            cellRead b'.1.2.2 (π (cwBlk P lab b j, a)).1 r.1)) hK
      obtain ⟨hD, ho⟩ := compressDbs_readK'_ne_zero hR
      exact fInv_readK' hm hD (hφ.trans (Prod.ext rfl hp.symm)) ho
    · obtain ⟨hz, rfl⟩ := hok
      obtain ⟨hp, hφ, hR⟩ := dec_clsKraus_ne_zero (p := fun b' : Hw X Z × Mem ↦ b'.2 = r.2)
        (φ := fun b' ↦ (b'.1, cwLiftHu (cwHu1 cwUpd) lab (cwBlk P lab b j) xi r.2 r.1))
        (R := fun b' ↦ cellRead b'.1.1 z' r.1 ⊗ₖ
          (1 : Matrix (Database X Z × Database X Z) (Database X Z × Database X Z) ℂ)) hK
      obtain ⟨hD, ho⟩ := compressDbs_readH_ne_zero hR
      rw [hz] at ho
      refine fInv_readH hm hD ?_ ho
      rw [hφ, ← hp]
      rfl
  · rw [decRM_branch_apply _ r _ (runtime2_branch m0R (.inr c) r)]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    show m'.2 ∈ FInv π P W₀ v .free
    have hnb := hm.1
    rcases c with ⟨z, a⟩ | ⟨x, a⟩ | ⟨x, a⟩
    · obtain ⟨-, hφ, hR⟩ := dec_clsKraus_ne_zero
        (p := fun b' : Hw X Z × Mem ↦ b'.1.1 z = r.2)
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
        (p := fun b' : Hw X Z × Mem ↦ b'.1.2.1 x = r.2)
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
        (p := fun b' : Hw X Z × Mem ↦ b'.1.2.2 x = r.2)
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
  · rw [decRM_branch_apply _ r _ (recStep_branch T r)]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    obtain ⟨-, hφ, hR⟩ := dec_clsKraus_ne_zero
      (φ := fun b' ↦ (b'.1, (b'.2.1 ∪ T, b'.2.2)))
      (R := fun _ ↦ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) hK
    exact fInv_rec hok.1 hok.2 hm (compressDbs_one_ne_zero hR) hφ

/-- The initial register in the decompressed basis: no empty cell, nothing hardwired, nothing
revealed. -/
theorem init_fInv :
    QuerySupportedOn (fun m : QReg.of Unit × HwReg X Z Mem ↦ m.2) (FInv π P W₀ v .free)
      (MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ compressReg X Z Mem)
        initR) := by
  have hnb := noBot_init (X := X) (Z := Z) m0R
    ((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ)
  have h0 : QuerySupportedOn (fun m : QReg.of Unit × HwReg X Z Mem ↦ m.2)
      {s | s.2 = (hwEmpty X Z, m0R)}
      (((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
        (runtimeR (X := X) (Z := Z) m0R).init.matrix) := by
    intro m m' hm
    change (((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
      (SubState.basis (((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m0R) :
        HwReg X Z Mem)).matrix) m m' ≠ 0 at hm
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
    (K := (1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ compressReg X Z Mem)
    (q' := fun m : QReg.of Unit × HwReg X Z Mem ↦ m.2) (S' := {s | s.2 = (hwEmpty X Z, m0R)})
    fun m' m hK hm ↦ by
      have hK' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) hK).2
      rw [compressReg, kroneckerMap_apply] at hK'
      have he : m'.2.2 = m.2.2 := by
        by_contra hne
        exact right_ne_zero_of_mul hK' (Matrix.one_apply_ne hne)
      show m'.2.2 = _
      rw [he]
      exact hm
  have hmem : ∀ s : HwReg X Z Mem, NoBot s → s.2 = (hwEmpty X Z, m0R) →
      s ∈ FInv π P W₀ v .free := fun s hs he ↦ by
    refine ⟨hs, ?_, trivial, fun lab hl _ _ _ ↦ ?_⟩
    · rw [he]
      exact ⟨fun _ h ↦ absurd rfl h, fun _ h ↦ absurd rfl h, fun _ h ↦ absurd rfl h⟩
    · rw [he] at hl
      exact absurd hl (Finset.notMem_empty _)
  intro a b hab
  exact ⟨hmem _ (hnb a b hab).1 (h1 a b hab).1, hmem _ (hnb a b hab).2 (h1 a b hab).2⟩

end decStep

/-! ## Moded programs, jointly -/

section prod

variable {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig.{u, v}} {Ω : QReg → Type w}
  {Mode₁ Mode₂ : Type} {ok₁ : Mode₁ → spec.Port → Prop}
  {nx₁ : Mode₁ → (i : spec.Port) → spec.Result i → Mode₁} {ok₂ : Mode₂ → spec.Port → Prop}
  {nx₂ : Mode₂ → (i : spec.Port) → spec.Result i → Mode₂}

/-- **Two moded properties of one program**, on the product of the modes. -/
theorem modedP_prod {fin₁ : (Σ u, Ω u) → Mode₁ → Prop} {fin₂ : (Σ u, Ω u) → Mode₂ → Prop}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor L spec) Ω A) :
    ∀ μ₁ μ₂, ModedP ok₁ nx₁ fin₁ μ₁ x → ModedP ok₂ nx₂ fin₂ μ₂ x →
      ModedP (fun μ i ↦ ok₁ μ.1 i ∧ ok₂ μ.2 i) (fun μ i r ↦ (nx₁ μ.1 i r, nx₂ μ.2 i r))
        (fun p μ ↦ fin₁ p μ.1 ∧ fin₂ p μ.2) (μ₁, μ₂) x := by
  induction x using IFreeM.inductionOn with
  | pure _ a => exact fun _ _ h₁ h₂ ↦ ⟨h₁, h₂⟩
  | liftBind _ c next ih =>
    intro μ₁ μ₂ h₁ h₂
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih b μ₁ μ₂ (h₁.2 b) (h₂.2 b)⟩
    · exact ⟨⟨h₁.1, h₂.1⟩, fun b ↦ ih b _ _ (h₁.2 b) (h₂.2 b)⟩

end prod

/-! ## The challenge prefix programs cells of `W₀` only -/

section tree

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

variable {M : Type} {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}

variable (M) in
/-- The condition of `ProgsC` on a command: a program port programs a cell of `W₀`. -/
def CmdC (W₀ : Hw X Z) (v : HPos → Digest) {A : QReg} :
    QuantumComp.Cmd Λ (XSpec M) A → Prop
  | .query (.inl (.inr p)) _ _ => (p.1.realize v).CellIn W₀
  | _ => True

/-- **A template programming cells of `W₀` only**, realized at `v`. -/
def ProgsC (W₀ : Hw X Z) (v : HPos → Digest) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor Λ (XSpec M)) Ω A → Prop
  | _, .pure _ => True
  | _, .liftBind c next => CmdC M W₀ v c ∧ ∀ b, ProgsC W₀ v (next b)

variable (W₀ : Hw X Z) (v : HPos → Digest)

theorem progsC_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor Λ (XSpec M)) Ω A) :
    ProgsC W₀ v (e ▸ y) ↔ ProgsC W₀ v y := by
  subst e
  rfl

theorem progsC_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor Λ (XSpec M)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor Λ (XSpec M)) Y u)
    (hx : ProgsC W₀ v x) (hg : ∀ u a, ProgsC W₀ v (g u a)) : ProgsC W₀ v (x.bind g) := by
  induction x using IFreeM.inductionOn with
  | pure _ a => exact hg _ a
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem progsC₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ Λ (XSpec M) A B α) (g : α → QuantumComp₂ Λ (XSpec M) B B' β)
    (hx : ProgsC W₀ v x) (hg : ∀ a, ProgsC W₀ v (g a)) : ProgsC W₀ v (x.bind g) := by
  refine progsC_bind W₀ v x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

theorem progsC_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor Λ spec)
      (QuantumComp.toIPFunctor Λ (XSpec M)))
    (hσ : ∀ A c, ProgsC W₀ v (σ A c)) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor Λ spec) Ω A) : ProgsC W₀ v (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact progsC_bind W₀ v _ _ (hσ s c) fun u ans ↦ (progsC_cast W₀ v ans.2 _).mpr (ih ans.1)

theorem progsC_readLift {A : QReg} (y : QuantumComp Λ (hwReadSpec X Z M) Ω A) :
    ProgsC W₀ v (readLift goodAll y) := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind _ c next ih =>
    show ProgsC W₀ v (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _

theorem progsC_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    ProgsC W₀ v (QComp.act (spec := XSpec M) p) :=
  ⟨trivial, fun _ ↦ trivial⟩

theorem progsC_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B B' α)
    (hk : ∀ r, ProgsC W₀ v (k r)) : ProgsC W₀ v (revealThen goodAll T k) :=
  ⟨trivial, fun r ↦ progsC₂_bind W₀ v _ _ (progsC_act W₀ v _) fun _ ↦ hk r.down⟩

theorem progsC_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec M) B B' α) (hpC : (p.realize v).CellIn W₀) (hk : ProgsC W₀ v k) :
    ProgsC W₀ v (progThen p hp k) :=
  ⟨hpC, fun _ ↦ progsC₂_bind W₀ v _ _ (progsC_act W₀ v _) fun _ ↦ hk⟩

theorem progsC_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD))
    (h : ∀ p ∈ ps, (p.realize v).CellIn W₀) : ProgsC W₀ v (progPorts M B ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact progsC_progThen W₀ v p trivial _ (h p List.mem_cons_self)
      (ih fun p' hp' ↦ h p' (List.mem_cons_of_mem _ hp'))

theorem progsC_progSlots (pub : Pub) (B : QReg) (ss : List Slot)
    (h : ∀ s ∈ ss, ∀ p ∈ slotPorts pub s, (p.realize v).CellIn W₀) :
    ProgsC W₀ v (progSlots M pub B ss) := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    exact progsC₂_bind W₀ v _ _ (progsC_progPorts W₀ v B _ (h s List.mem_cons_self)) fun _ ↦
      ih fun s' hs' ↦ h s' (List.mem_cons_of_mem _ hs')

variable (upd : TrialUpd M) {pub : Pub}
  (hC : ∀ (l : Layer) (e : KeyIndex) (x : Encoding), e.val < keyCount l →
    ∀ s ∈ layerSlots l e x, ∀ p ∈ slotPorts pub s, (p.realize v).CellIn W₀)
include hC

theorem progsC_signLayerT (B : QReg) (lab : RLabel) (he : lab.key.val < keyCount lab.layer) :
    ProgsC W₀ v (signLayerT M upd pub B lab) := by
  refine progsC_revealThen W₀ v _ _ fun _ ↦
    progsC₂_bind W₀ v _ _ (progsC_readLift W₀ v _) ?_
  rintro (_ | ⟨ρ, x⟩)
  · trivial
  · exact progsC_revealThen W₀ v _ _ fun _ ↦ progsC₂_bind W₀ v _ _
      (progsC_progSlots W₀ v pub B _ (hC lab.layer lab.key x he)) fun _ ↦ trivial

theorem progsC_signT (B : QReg) (r : SigningRequest) : ProgsC W₀ v (signT M upd pub B r) := by
  refine progsC₂_bind W₀ v _ _ (progsC_signLayerT W₀ v upd hC B (botLabel r)
    (keyIndexOnLayer_lt r.leafIndex bottomLayer)) ?_
  rintro (_ | ⟨bottom, f⟩)
  · trivial
  · refine progsC₂_bind W₀ v _ _ (progsC_signLayerT W₀ v upd hC B (topLabel r _)
      (keyIndexOnLayer_lt r.leafIndex topLayer)) ?_
    rintro (_ | ⟨top, _⟩) <;> trivial

theorem progsC_challengeT (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    ProgsC W₀ v (challengeT M upd pub A c) := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact progsC_readLift W₀ v _
  · exact progsC_readLift W₀ v _
  · exact progsC_bind W₀ v _ _ (progsC₂_bind W₀ v _ _ (progsC_act W₀ v _) fun _ ↦
      progsC_signT W₀ v upd hC _ r) fun _ _ ↦ trivial

/-- **The challenge prefix programs cells of `W₀` only.** -/
theorem progsC_prefixT (A : Adversary (X × Z)) : ProgsC W₀ v (prefixT M upd pub A) :=
  progsC_revealThen W₀ v _ _ fun _ ↦
    progsC₂_bind W₀ v _ _ (progsC_substitute W₀ v _ (progsC_challengeT W₀ v upd hC) _) fun _ ↦
      trivial

end tree

section transfer

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- **Realizing keeps the programs in `W₀`**, as a moded program with one mode. -/
theorem modedP_realizeT_progsC {W₀ : Hw X Z} (v : HPos → Digest) {L : LocalSig.{u, v}}
    {Ω : QReg → Type w} {A : QReg} (y : QuantumComp L (XSpec Selections) Ω A)
    (hy : ProgsC W₀ v y) :
    ModedP (fun _ : Unit ↦ PortC W₀) (fun _ _ _ ↦ ()) (fun _ _ ↦ True) () (realizeT v y) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => trivial
  | liftBind _ c next ih =>
    show ModedP _ _ _ () (IFreeM.mapLens (tmplLens v) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 (ULift.up (restrictTo T v, b.down)))⟩
end transfer

section decTransfer

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]

/-- **A moded invariant of the decompressed basis, at the calls of `runtimeR`**: if every allowed
call of the decompressed runtime keeps the invariant of the modes, every call of a moded run of
`runtimeR` is allowed by a mode whose invariant holds of the decompressed input. -/
theorem forallQueries_dec_moded (m₀ : Finset S × M) {Mode : Type}
    {ok : Mode → (recHwSpec X Z S M).Port → Prop}
    {nx : Mode → (i : (recHwSpec X Z S M).Port) → (recHwSpec X Z S M).Result i → Mode}
    (Inv : Mode → Set (HwReg X Z (Finset S × M)))
    (hstep : ∀ μ i r (σ : Matrix ((recHwSpec X Z S M).In i × HwReg X Z (Finset S × M))
        ((recHwSpec X Z S M).In i × HwReg X Z (Finset S × M)) ℂ), ok μ i →
      QuerySupportedOn (fun m : (recHwSpec X Z S M).In i × HwReg X Z (Finset S × M) ↦ m.2)
        (Inv μ) σ →
      QuerySupportedOn (fun m : (recHwSpec X Z S M).Out i × HwReg X Z (Finset S × M) ↦ m.2)
        (Inv (nx μ i r)) (((decR m₀).step i).branch r σ))
    {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} {fin : (Σ u, Ω u) → Mode → Prop}
    {A : QReg} (x : QuantumComp L (recHwSpec X Z S M) Ω A) (μ : Mode)
    (hx : ModedP ok nx fin μ x)
    {ρ : Matrix (A × HwReg X Z (Finset S × M)) (A × HwReg X Z (Finset S × M)) ℂ}
    (hρ : QuerySupportedOn (fun m : A × HwReg X Z (Finset S × M) ↦ m.2) (Inv μ)
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z (Finset S × M)) ρ)) :
    (runtimeR m₀).ForallQueries I (fun i E τ ↦ ∃ μ, ok μ i ∧
      QuerySupportedOn (fun m : (recHwSpec X Z S M).In i × HwReg X Z (Finset S × M) ↦ m.2)
        (Inv μ) (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z S M).In i)
          ((recHwSpec X Z S M).In i) ℂ) ⊗ₖ compressReg X Z (Finset S × M))
            (MatrixMap.traceRight _ E τ))) x ρ := by
  have hC : compressReg X Z (Finset S × M) * compressReg X Z (Finset S × M) = 1 :=
    compressReg_mul_self
  have h1 := forallQueries_of_modedP (decR m₀) I Inv hstep x μ hx hρ
  have hstep' : ∀ i r, ((runtimeRH m₀).step i).branch r ∘ₗ
      (MatrixMap.conj (compressReg X Z (Finset S × M))).amplifyLeft ((recHwSpec X Z S M).In i) =
      (MatrixMap.conj (compressReg X Z (Finset S × M))).amplifyLeft
        ((recHwSpec X Z S M).Out i) ∘ₗ ((decR m₀).step i).branch r := fun i r ↦ by
    rw [conjReg_branch (runtimeRH m₀) (compressReg X Z (Finset S × M)) compressReg_mul_self
      conjTranspose_compressReg i r]
    simp only [MatrixMap.amplifyLeft_conj]
    rw [← LinearMap.comp_assoc, conj_one_kronecker_comp_self (runtimeRH m₀) _ hC,
      LinearMap.id_comp]
  have h2 := ForallQueries.of_simulation I (R₁ := decR m₀) (R₂ := runtimeRH m₀)
    (V := MatrixMap.conj (compressReg X Z (Finset S × M))) hstep'
    (P₂ := fun i E τ ↦ ∃ μ, ok μ i ∧
      QuerySupportedOn (fun m : (recHwSpec X Z S M).In i × HwReg X Z (Finset S × M) ↦ m.2)
        (Inv μ) (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z S M).In i)
          ((recHwSpec X Z S M).In i) ℂ) ⊗ₖ compressReg X Z (Finset S × M))
            (MatrixMap.traceRight _ E τ)))
    (fun i E τ hτ ↦ by
      obtain ⟨μ', hok, hsupp⟩ := hτ
      refine ⟨μ', hok, ?_⟩
      rw [MatrixMap.amplifyLeft_conj,
        ← LinearMap.comp_apply (MatrixMap.conj _) (MatrixMap.traceRight _ E),
        ← MatrixMap.traceRight_comp_amplify, LinearMap.comp_apply,
        ← LinearMap.comp_apply (MatrixMap.amplify _ E) (MatrixMap.amplify _ E),
        ← MatrixMap.amplify_comp, conj_one_kronecker_comp_self (runtimeRH m₀) _ hC,
        MatrixMap.amplify_id, LinearMap.id_apply]
      exact querySupportedOn_traceRight (q := fun m : (recHwSpec X Z S M).In i ×
        HwReg X Z (Finset S × M) ↦ m.2) hsupp) h1
  have hρ' : (MatrixMap.conj (compressReg X Z (Finset S × M))).amplifyLeft A
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z (Finset S × M)) ρ) = ρ := by
    rw [MatrixMap.amplifyLeft_conj,
      ← LinearMap.comp_apply (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ
        compressReg X Z (Finset S × M))), conj_one_kronecker_comp_self (runtimeRH m₀) _ hC,
      LinearMap.id_apply]
  rw [hρ'] at h2
  exact h2

/-- The calls programming cells of `W` only, on runtime 2 with record ports. -/
def PortCw (W : Hw X Z) : (recHwSpec X Z S M).Port → Prop
  | .inl (.inr c) => c.CellIn W
  | _ => True

omit [Nonempty X] [Nonempty Z] in
/-- `clsKraus_one_commute_hwDecProj` with the decidability of the classical condition found by
unification. -/
theorem clsKraus_one_commute_hwDecProj' {n : Type} [Fintype n] [DecidableEq n]
    (E : Set (HwReg X Z (Finset S × M))) [DecidablePred (· ∈ E)] (F : DbReg X Z → Prop)
    (hE : ∀ s, s ∈ E ↔ F s.1) {p : Hw X Z × (Finset S × M) → Prop} {_ : DecidablePred p}
    (φ : Hw X Z × (Finset S × M) → Hw X Z × (Finset S × M)) :
    ((1 : Matrix n n ℂ) ⊗ₖ hwDecProj E) *
        ((1 : Matrix n n ℂ) ⊗ₖ clsKraus p φ fun _ ↦ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) =
      ((1 : Matrix n n ℂ) ⊗ₖ clsKraus p φ fun _ ↦ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) *
        ((1 : Matrix n n ℂ) ⊗ₖ hwDecProj E) :=
  clsKraus_one_commute_hwDecProj E F hE p φ

/-- **The ports programming cells of `W` commute with the decompressed projector** of an event
determined off `W` (DecUniform's commutations, on `runtimeR`). -/
theorem runtimeR_commute_hwDecProj (m₀ : Finset S × M) {W : Hw X Z} {F : DbReg X Z → Prop}
    (hF : OffHw W F) (E : Set (HwReg X Z (Finset S × M))) [DecidablePred (· ∈ E)]
    (hE : ∀ s, s ∈ E ↔ F s.1) (i : (recHwSpec X Z S M).Port) (hi : PortCw (S := S) (M := M) W i)
    (r : (recHwSpec X Z S M).Result i) :
    ((runtimeR m₀).step i).branch r ∘ₗ
        (MatrixMap.conj (hwDecProj E)).amplifyLeft ((recHwSpec X Z S M).In i) =
      (MatrixMap.conj (hwDecProj E)).amplifyLeft ((recHwSpec X Z S M).Out i) ∘ₗ
        ((runtimeR m₀).step i).branch r := by
  rcases i with ((i | c) | c) | T
  · cases i <;> exact branch_comm_of_commute (runtime2_branch m₀ (.inl (.inl _)) r)
      (hwPort_commute_hwDecProj E _)
  · exact branch_comm_of_commute (runtime2_branch m₀ (.inl (.inr c)) r)
      (hwReadKraus_commute_hwDecProj E F hE c r)
  · exact branch_comm_of_commute (runtime2_branch m₀ (.inr c) r)
      (hwProgKraus_commute_hwDecProj E hF hE hi r)
  · exact branch_comm_of_commute (recStep_branch T r)
      (clsKraus_one_commute_hwDecProj' E F hE _)

omit [Nonempty X] [Nonempty Z] in
/-- The projector of an event of the classical data is the same in the decompressed basis. -/
theorem compressReg_mul_diagonal_snd (P : Hw X Z × M → Prop) [DecidablePred P] :
    compressReg X Z M * diagonal (fun s : HwReg X Z M ↦ if P s.2 then (1 : ℂ) else 0) *
      compressReg X Z M = diagonal (fun s : HwReg X Z M ↦ if P s.2 then (1 : ℂ) else 0) := by
  have h : diagonal (fun s : HwReg X Z M ↦ if P s.2 then (1 : ℂ) else 0) =
      (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ) ⊗ₖ
        diagonal (fun b : Hw X Z × M ↦ if P b then (1 : ℂ) else 0) :=
    (one_kronecker_diagonal_eq (fun b : Hw X Z × M ↦ if P b then (1 : ℂ) else 0)).symm
  rw [h, compressReg, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one,
    compressDbs_mul_self, Matrix.one_mul, Matrix.mul_one]

omit [Nonempty X] [Nonempty Z] in
/-- **A diagonal mass of the classical data below a decompressed event**: on an operator whose
decompressed form is supported on `S`, where the classical event implies the database event. -/
theorem diagMass_le_potential_hwDecProj (P : Hw X Z × M → Prop) [DecidablePred P]
    (F : Set (HwReg X Z M)) [DecidablePred (· ∈ F)] (S : Set (HwReg X Z M))
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hS : QuerySupportedOn (fun m : Unit × HwReg X Z M ↦ m.2) S
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M) σ))
    (h12 : ∀ s ∈ S, P s.2 → s ∈ F) :
    diagMass {q : Unit × HwReg X Z M | P q.2.2} σ ≤ potential (hwDecProj F) σ := by
  have h := re_trace_conj_kron_proj_le (compressReg X Z M) compressReg_mul_self
    conjTranspose_compressReg (fun s : HwReg X Z M ↦ P s.2) (· ∈ F)
    (d₁ := fun s ↦ ‹DecidablePred P› s.2) (d₂ := fun s ↦ ‹DecidablePred (· ∈ F)› s) S hσ hS h12
  rw [compressReg_mul_diagonal_snd] at h
  have e1 : diagMass {q : Unit × HwReg X Z M | P q.2.2} σ =
      potential (setProj {s : HwReg X Z M | P s.2}) σ :=
    (potential_setProj {s : HwReg X Z M | P s.2} hσ).symm
  have e2 : setProj {s : HwReg X Z M | P s.2} =
      diagonal (fun s : HwReg X Z M ↦ if P s.2 then (1 : ℂ) else 0) := by
    unfold setProj
    congr 1
    funext s
    by_cases hs : P s.2
    · rw [Set.indicator_of_mem (show s ∈ {s : HwReg X Z M | P s.2} from hs), ite_eq_left hs]
      rfl
    · rw [Set.indicator_of_notMem (show s ∉ {s : HwReg X Z M | P s.2} from hs),
        ite_eq_right hs]
  rw [e1, e2, potential, potential, MatrixMap.amplifyLeft_conj, MatrixMap.amplifyLeft_conj]
  exact ENNReal.ofReal_le_ofReal h

open scoped Classical in
/-- **The initial potential of a decompressed database event**: its fraction of the total tables
(DecUniform's `trace_conj_hwDecProj_basis`). -/
theorem potential_hwDecProj_init (m₀ : Finset S × M) (E : Set (HwReg X Z (Finset S × M)))
    [DecidablePred (· ∈ E)] (F : DbReg X Z → Prop) (hE : ∀ s, s ∈ E ↔ F s.1) {A : Type}
    [Fintype A] [DecidableEq A] (ρ : Matrix A A ℂ) (hρ : ρ.PosSemidef) :
    potential (hwDecProj E) (ρ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) =
      ENNReal.ofReal ρ.trace.re * (((Finset.univ.filter fun t ↦ F (ofFunDbs t)).card : ℝ≥0∞) /
        Fintype.card ((Z → X) × (X → Z) × (X → Z))) := by
  rw [potential, MatrixMap.amplifyLeft_conj]
  change ENNReal.ofReal (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ hwDecProj E)
    (ρ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) :
      HwReg X Z (Finset S × M))).matrix)).trace.re = _
  rw [SubState.matrix_basis, trace_conj_hwDecProj_basis E F hE (hwEmpty X Z, m₀) ρ,
    ENNReal.ofReal_mul hρ.trace_re_nonneg, ENNReal.ofReal_div_of_pos
      (Nat.cast_pos.mpr Fintype.card_pos), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

end decTransfer

/-! ## Charges against a commuting potential -/

section chargePot

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w}

/-- A port whose branches commute with `conj Q` does not raise the potential of `Q`. -/
theorem tsum_potential_le_of_commute (Q : Matrix R.D R.D ℂ) (i : spec.Port)
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

/-- **The charged calls against a commuting potential**: if every call is of a port commuting
with `conj Q`, the calls' charges times their potentials add up to at most the charge bound times
the initial potential. -/
theorem totalWeight_charge_potential_le (Q : Matrix R.D R.D ℂ) (κ : spec.Port → ℕ)
    (good : spec.Port → Prop)
    (hc : ∀ i, good i → ∀ r, (R.step i).branch r ∘ₗ (MatrixMap.conj Q).amplifyLeft (spec.In i) =
      (MatrixMap.conj Q).amplifyLeft (spec.Out i) ∘ₗ (R.step i).branch r)
    {P : ∀ (i : spec.Port) (E : QReg),
      Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop}
    (hP : ∀ i E σ, P i E σ → good i) {A : QReg} (x : QuantumComp L spec Ω A) :
    ∀ {n : ℕ}, IFreeM.IsChargeBound x (portCharge κ) n →
      ∀ {ρ : Matrix (A × R.D) (A × R.D) ℂ}, ρ.PosSemidef → R.ForallQueries I P x ρ →
        R.totalWeight I (fun i σ ↦ κ i * potential Q σ) x ρ ≤ n * potential Q ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ =>
    intro n _ ρ _ _
    rw [totalWeight_pure]
    exact zero_le
  | primBind _ o k ih =>
    intro n hx ρ hρ hq
    rw [isChargeBound_portCharge_primBind_iff] at hx
    rw [QuantumRuntime.forallQueries_primBind_iff] at hq
    rw [totalWeight_primBind]
    calc ∑' b, R.totalWeight I (fun i σ ↦ κ i * potential Q σ) (k b)
          (((I o).frame R.D).branch b ρ)
        ≤ ∑' b, (n : ℝ≥0∞) * potential Q (((I o).frame R.D).branch b ρ) :=
          ENNReal.tsum_le_tsum fun b ↦
            ih b (hx b) (((I o).frame R.D).posSemidef_branch_apply b hρ) (hq b)
      _ = n * ∑' b, potential Q (((I o).frame R.D).branch b ρ) := ENNReal.tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left (tsum_potential_frame_le Q (I o) hρ) zero_le
  | queryBind _ i E ℓ k ih =>
    intro n hx ρ hρ hq
    rw [isChargeBound_portCharge_queryBind_iff] at hx
    rw [QuantumRuntime.forallQueries_queryBind_iff] at hq
    rw [totalWeight_queryBind, potential_callInput]
    have hσ := posSemidef_callInput ℓ hρ
    have hs : ∑' r, R.totalWeight I (fun i σ ↦ κ i * potential Q σ) (k r)
        ((R.queryStep i E ℓ).branch r ρ) ≤ ((n - κ i : ℕ) : ℝ≥0∞) * potential Q ρ := by
      calc ∑' r, R.totalWeight I (fun i σ ↦ κ i * potential Q σ) (k r)
            ((R.queryStep i E ℓ).branch r ρ)
          ≤ ∑' r, ((n - κ i : ℕ) : ℝ≥0∞) * potential Q ((R.queryStep i E ℓ).branch r ρ) :=
            ENNReal.tsum_le_tsum fun r ↦ ih r (hx.2 r)
              ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ) (hq.2 r)
        _ = ((n - κ i : ℕ) : ℝ≥0∞) *
            ∑' r, potential Q ((R.step i).branch r (callInput ℓ R.D ρ)) := by
            rw [ENNReal.tsum_mul_left]
            simp only [potential_queryStep]
        _ ≤ ((n - κ i : ℕ) : ℝ≥0∞) * potential Q (callInput ℓ R.D ρ) :=
            mul_le_mul_of_nonneg_left (tsum_potential_le_of_commute R Q i
              (hc i (hP i E _ hq.1)) hσ) zero_le
        _ = _ := by rw [potential_callInput]
    calc κ i * potential Q ρ + ∑' r, R.totalWeight I (fun i σ ↦ κ i * potential Q σ) (k r)
          ((R.queryStep i E ℓ).branch r ρ)
        ≤ κ i * potential Q ρ + ((n - κ i : ℕ) : ℝ≥0∞) * potential Q ρ := add_le_add le_rfl hs
      _ = n * potential Q ρ := by rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hx.1]

end chargePot

/-! ## The failed searches against a database event -/

section prefixInv

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter) (W₀ : Hw X Z) (v : HPos → Digest)

/-- **Some label's search fails on the databases**: every trial of a label, from its hidden base,
touches `W₀` or fails. -/
def FailDb (D : DbReg X Z) : Prop :=
  ∃ lab : RLabel, ∀ j < randomizerAttemptLimit, TB π P W₀ lab (v (.inr lab)) j D

/-- The registers whose databases fail a search. -/
def failSet : Set (HwReg X Z Mem) := {s | FailDb π P W₀ v s.1}

/-- `failSet`, decided classically. -/
noncomputable instance instDecidableFailSet : DecidablePred (· ∈ failSet π P W₀ v) :=
  Classical.decPred _

/-- `FailDb` looks at the databases outside `W₀` only. -/
theorem offHw_failDb : OffHw W₀ (FailDb π P W₀ v) := by
  intro D D' h1 h2 h3
  have hag : DbOffAgree W₀ D D' := ⟨h1, h2, h3⟩
  have hag' : DbOffAgree W₀ D' D :=
    ⟨fun z hz ↦ (h1 z hz).symm, fun x hx ↦ (h2 x hx).symm, fun x hx ↦ (h3 x hx).symm⟩
  exact ⟨fun ⟨lab, h⟩ ↦ ⟨lab, fun j hj ↦ tB_of_offAgree π P W₀ hag (h j hj)⟩,
    fun ⟨lab, h⟩ ↦ ⟨lab, fun j hj ↦ tB_of_offAgree π P W₀ hag' (h j hj)⟩⟩

/-- **A repeated reveal with the key unselected is in the failure event**: at a record call
allowed by a rest mode, on the invariant, a revealed label with its key unselected has run all its
trials. -/
theorem reRevW_le (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z Mem)) ℂ) (hσ : σ.PosSemidef)
    (h : ∃ μ : CwMode × Unit, (stOkZ π P (cwLiftHu (cwHu1 cwUpd)) μ.1 i ∧ PortC W₀ i) ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × HwReg X Z Mem ↦ m.2)
        (FInv π P W₀ v μ.1) (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
          ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z Mem) σ)) :
    reRevW i σ ≤ (candCharge X Z Selections rJ i : ℝ≥0∞) *
      potential (hwDecProj (failSet π P W₀ v)) σ := by
  rcases i with ((i | c) | c) | T
  · exact zero_le
  · exact zero_le
  · exact zero_le
  · obtain ⟨μ, ⟨⟨hrest, -⟩, -⟩, hS⟩ := h
    show reRevO (cwRevLab T) σ ≤ _
    rcases hT : cwRevLab T with _ | lab
    · exact zero_le
    · have hT' := cwRevLab_spec hT
      have hc : (1 : ℝ≥0∞) ≤ (candCharge X Z Selections rJ (.inr T) : ℝ≥0∞) := by
        show (1 : ℝ≥0∞) ≤ ((T ∩ rJ).card : ℝ≥0∞)
        rw [hT']
        exact_mod_cast Finset.card_pos.mpr ⟨_, Finset.mem_inter.mpr
          ⟨Finset.mem_singleton_self _, inr_mem_rJ lab⟩⟩
      classical
      refine le_trans ?_ (le_mul_of_one_le_left zero_le hc)
      show diagMass {q : Unit × HwReg X Z Mem | ReRev lab q.2} σ ≤ _
      exact diagMass_le_potential_hwDecProj
        (fun b : Hw X Z × Mem ↦ (Sum.inr lab : HPos) ∈ b.2.1 ∧ cwU lab b.2) _ _ hσ hS
        fun s hs hP ↦ ⟨lab, fun j hj ↦ hs.2.2.2 lab hP.1 hP.2 j
          (by rw [doneN_of_rest hrest]; exact hj)⟩

end prefixInv

section total

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

variable {W₀ : Hw X Z} {v : HPos → Digest}

theorem portCw_of_portC {i : (recHwSpec X Z HPos Selections).Port} (h : PortC W₀ i) :
    PortCw (S := HPos) (M := Selections) W₀ i := by
  rcases i with ((i | c) | c) | T <;> exact h

/-- **The repeated-reveal masses of the realized prefix are at most the record charge bound times
the initial weight of the failure event.** -/
theorem totalWeight_reRevW_le (pub : Pub) (A : Adversary (X × Z))
    (hC : ProgsC W₀ v (prefixT Selections cwUpd pub A)) {R : ℕ}
    (hR : IFreeM.IsChargeBound (realizeT v (prefixT Selections cwUpd pub A))
      (portCharge (candCharge X Z Selections rJ)) R) :
    (runtimeR m0R).totalWeight .instruments reRevW (realizeT v (prefixT Selections cwUpd pub A))
        initR ≤ R * potential (hwDecProj (failSet pub.perm pub.param W₀ v)) initR := by
  have hq := forallQueries_dec_moded m0R
    (fun μ : CwMode × Unit ↦ FInv pub.perm pub.param W₀ v μ.1)
    (fun μ i r σ hok hσ ↦ fInv_step μ.1 i r σ hok.1 hok.2 hσ) LocalSig.Interp.instruments
    (realizeT v (prefixT Selections cwUpd pub A)) _
    (modedP_prod _ _ _ (modedP_prefixR_st cwUpd pub A v) (modedP_realizeT_progsC v _ hC))
    init_fInv
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments _ (fun i E σ h ↦ h)
    (w' := fun i σ ↦ (candCharge X Z Selections rJ i : ℝ≥0∞) *
      potential (hwDecProj (failSet pub.perm pub.param W₀ v)) σ)
    (fun i σ hσ hok ↦ reRevW_le pub.perm pub.param W₀ v i σ hσ hok) _ initR_posSemidef
    hq).trans ?_
  exact totalWeight_charge_potential_le (runtimeR m0R) .instruments _ _
    (PortCw (S := HPos) (M := Selections) W₀)
    (fun i hi r ↦ runtimeR_commute_hwDecProj m0R (offHw_failDb pub.perm pub.param W₀ v)
      (failSet pub.perm pub.param W₀ v) (fun _ ↦ Iff.rfl) i hi r)
    (fun i E σ h ↦ portCw_of_portC (Exists.choose_spec h).1.2) _ hR initR_posSemidef hq

end total

/-! ## Counting the failed searches over the total tables -/

section count

/-- **Resampling at a fixed cell, relative to a precondition**: if `Pre` ignores the value at `c`
and resampling that value makes `Bad` hold for at most `g` values, then `Pre ∧ Bad` holds for at
most `g / |B|` of the functions satisfying `Pre`. -/
theorem card_mul_sum_and_le {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (Pre Bad : (A → B) → Prop) [DecidablePred Pre] [DecidablePred Bad] (c : A) (g : ℕ)
    (hPre : ∀ f b, Pre (Function.update f c b) ↔ Pre f)
    (hD : ∀ f, ∑ b, (if Bad (Function.update f c b) then 1 else 0) ≤ g) :
    Fintype.card B * ∑ f, (if Pre f ∧ Bad f then 1 else 0) ≤
      g * ∑ f, (if Pre f then 1 else 0) := by
  let φ : (A → B) × B → (A → B) × B := fun p ↦ (Function.update p.1 c p.2, p.1 c)
  have hφ : Function.Involutive φ := by
    rintro ⟨f, b⟩
    simp only [φ, Function.update_idem, Function.update_eq_self, Function.update_self]
  have hsum : ∑ p : (A → B) × B, (if Pre (φ p).1 ∧ Bad (φ p).1 then 1 else 0) =
      ∑ p : (A → B) × B, (if Pre p.1 ∧ Bad p.1 then 1 else 0) :=
    Fintype.sum_equiv hφ.toPerm
      (fun p ↦ if Pre (φ p).1 ∧ Bad (φ p).1 then 1 else 0)
      (fun p ↦ if Pre p.1 ∧ Bad p.1 then 1 else 0) fun _ ↦ rfl
  calc Fintype.card B * ∑ f, (if Pre f ∧ Bad f then 1 else 0)
      = ∑ f : A → B, ∑ _b : B, (if Pre f ∧ Bad f then 1 else 0) := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.mul_sum]
    _ = ∑ p : (A → B) × B, (if Pre p.1 ∧ Bad p.1 then 1 else 0) :=
        (Fintype.sum_prod_type' (fun f (_ : B) ↦ if Pre f ∧ Bad f then 1 else 0)).symm
    _ = ∑ p : (A → B) × B, (if Pre (φ p).1 ∧ Bad (φ p).1 then 1 else 0) := hsum.symm
    _ = ∑ f : A → B, ∑ b : B, (if Pre (Function.update f c b) ∧
          Bad (Function.update f c b) then 1 else 0) :=
        Fintype.sum_prod_type' (fun f b ↦ if Pre (Function.update f c b) ∧
          Bad (Function.update f c b) then 1 else 0)
    _ = ∑ f : A → B, ∑ b : B,
          (if Pre f ∧ Bad (Function.update f c b) then 1 else 0) := by
        simp only [hPre]
    _ ≤ ∑ f : A → B, g * (if Pre f then 1 else 0) := Finset.sum_le_sum fun f _ ↦ by
        by_cases hf : Pre f
        · simp only [hf, true_and, ite_true, mul_one]
          exact hD f
        · simp [hf]
    _ = g * ∑ f, (if Pre f then 1 else 0) := by rw [Finset.mul_sum]

/-- **Independent values at distinct points**: at most `(g / |B|)^n` of the functions take, at
`n` distinct points, values in sets of at most `g` elements. -/
theorem pow_mul_sum_all_le {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] (z : ℕ → A)
    (G : ℕ → B → Prop) [∀ j, DecidablePred (G j)] (g : ℕ)
    (hG : ∀ j, ∑ b, (if G j b then 1 else 0) ≤ g) :
    ∀ n, (∀ i < n, ∀ j < n, z i = z j → i = j) →
      Fintype.card B ^ n * ∑ f : A → B, (if ∀ j < n, G j (f (z j)) then 1 else 0) ≤
        g ^ n * Fintype.card (A → B)
  | 0, _ => by simp
  | n + 1, hz => by
    have ih := pow_mul_sum_all_le z G g hG n fun i hi j hj ↦ hz i (by omega) j (by omega)
    have hne : ∀ j < n, z j ≠ z n := fun j hj he ↦ by
      have := hz j (by omega) n (by omega) he
      omega
    have hstep := card_mul_sum_and_le (fun f : A → B ↦ ∀ j < n, G j (f (z j)))
      (fun f ↦ G n (f (z n))) (z n) g
      (fun f b ↦ by
        constructor
        · intro h j hj
          have := h j hj
          rwa [Function.update_of_ne (hne j hj)] at this
        · intro h j hj
          rw [Function.update_of_ne (hne j hj)]
          exact h j hj)
      (fun f ↦ by simpa only [Function.update_self] using hG n)
    have he : ∀ f : A → B, (if ∀ j < n + 1, G j (f (z j)) then 1 else 0) =
        (if (∀ j < n, G j (f (z j))) ∧ G n (f (z n)) then 1 else 0) := fun f ↦ by
      refine if_congr ⟨fun h ↦ ⟨fun j hj ↦ h j (by omega), h n (by omega)⟩, fun h j hj ↦ ?_⟩
        rfl rfl
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h.1 j hj
      · exact h.2
    simp only [he]
    calc Fintype.card B ^ (n + 1) *
          ∑ f : A → B, (if (∀ j < n, G j (f (z j))) ∧ G n (f (z n)) then 1 else 0)
        = Fintype.card B ^ n * (Fintype.card B *
          ∑ f : A → B, (if (∀ j < n, G j (f (z j))) ∧ G n (f (z n)) then 1 else 0)) := by
          rw [pow_succ, mul_assoc]
      _ ≤ Fintype.card B ^ n * (g * ∑ f : A → B, (if ∀ j < n, G j (f (z j)) then 1 else 0)) :=
          Nat.mul_le_mul_left _ hstep
      _ = g * (Fintype.card B ^ n *
          ∑ f : A → B, (if ∀ j < n, G j (f (z j)) then 1 else 0)) := by ring
      _ ≤ g * (g ^ n * Fintype.card (A → B)) := Nat.mul_le_mul_left _ ih
      _ = g ^ (n + 1) * Fintype.card (A → B) := by ring

variable {X₁ Z₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [AddCommGroup X₁] [AddCommGroup Z₁]

/-- The rate after `π` of a one-block trial at block `x` on the tables `t`. -/
def tY (π : Equiv.Perm (X₁ × Z₁)) (x : X₁) (t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁)) : X₁ :=
  (π (x, t.2.1 x)).1

/-- The `h`-cell of a one-block trial at block `x` on the tables `t`. -/
def tZ (π : Equiv.Perm (X₁ × Z₁)) (x : X₁) (t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁)) : Z₁ :=
  (π (x, t.2.1 x)).2 + t.2.2 (π (x, t.2.1 x)).1

/-- **All trials fail on distinct fresh `h`-cells**: at most `(g / |X|)^N` of the tables, `g` the
non-codeword values of a cell. -/
theorem pow_mul_card_allFail_le (π : Equiv.Perm (X₁ × Z₁)) (B : ℕ → X₁) (N : ℕ)
    (Cw : X₁ → Prop) [DecidablePred Cw] (g : ℕ)
    (hg : ∀ y, ∑ v, (if ¬ Cw (y + v) then 1 else 0) ≤ g) :
    Fintype.card X₁ ^ N * ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
      (if (∀ i < N, ∀ j < N, tZ π (B i) t = tZ π (B j) t → i = j) ∧
        ∀ j < N, ¬ Cw (tY π (B j) t + t.1 (tZ π (B j) t)) then 1 else 0) ≤
      Fintype.card (Z₁ → X₁) * Fintype.card (X₁ → Z₁) * Fintype.card (X₁ → Z₁) * g ^ N := by
  refine card_mul_sum_triple_le₁ (fun h k k' ↦
    if (∀ i < N, ∀ j < N, tZ π (B i) (h, k, k') = tZ π (B j) (h, k, k') → i = j) ∧
      ∀ j < N, ¬ Cw (tY π (B j) (h, k, k') + h (tZ π (B j) (h, k, k'))) then 1 else 0)
    _ _ fun k k' ↦ ?_
  by_cases hD : ∀ i < N, ∀ j < N, tZ π (B i) (0, k, k') = tZ π (B j) (0, k, k') → i = j
  · have h1 := pow_mul_sum_all_le (fun j ↦ tZ π (B j) (0, k, k'))
      (fun j v ↦ ¬ Cw (tY π (B j) (0, k, k') + v)) g (fun j ↦ hg _) N hD
    refine le_of_eq_of_le (congrArg (Fintype.card X₁ ^ N * ·)
      (Finset.sum_congr rfl fun h _ ↦ ?_)) (h1.trans_eq (mul_comm _ _))
    exact if_congr ⟨fun h ↦ h.2, fun h ↦ ⟨hD, h⟩⟩ rfl rfl
  · refine le_of_eq_of_le ?_ (Nat.zero_le _)
    rw [Finset.sum_eq_zero fun h _ ↦ ite_eq_right fun h' ↦ hD h'.1, mul_zero]

omit [AddCommGroup X₁] in
/-- **Two trials at distinct blocks share their `h`-cell** on at most `1 / |Z|` of the tables:
with distinct `k'`-cells the `k'`-value of one is resampled; with the same `k'`-cell, `π` is
injective. -/
theorem card_mul_card_coll_le (π : Equiv.Perm (X₁ × Z₁)) {x₁ x₂ : X₁} (hx : x₁ ≠ x₂) :
    Fintype.card Z₁ * ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
      (if tZ π x₁ t = tZ π x₂ t then 1 else 0) ≤
      Fintype.card (Z₁ → X₁) * Fintype.card (X₁ → Z₁) * Fintype.card (X₁ → Z₁) * 1 := by
  refine card_mul_sum_triple_le₃ (fun h k k' ↦ if tZ π x₁ (h, k, k') = tZ π x₂ (h, k, k') then 1
    else 0) _ _ fun h k ↦ ?_
  by_cases hy : (π (x₁, k x₁)).1 = (π (x₂, k x₂)).1
  · refine le_of_eq_of_le ?_ (Nat.zero_le _)
    rw [Finset.sum_eq_zero fun k' _ ↦ ite_eq_right fun he ↦ ?_, mul_zero]
    have he' : (π (x₁, k x₁)).2 + k' (π (x₁, k x₁)).1 =
        (π (x₂, k x₂)).2 + k' (π (x₂, k x₂)).1 := he
    rw [hy] at he'
    have h2 := add_right_cancel he'
    exact hx (congrArg Prod.fst (π.injective (Prod.ext hy h2)))
  · exact card_mul_sum_le_of_moving
      (fun k' ↦ tZ π x₁ (h, k, k') = tZ π x₂ (h, k, k')) (fun _ ↦ True)
      (fun k' ↦ tZ π x₁ (h, k, k') = tZ π x₂ (h, k, k')) (fun _ ↦ (π (x₁, k x₁)).1) 1
      (fun _ hf ↦ ⟨trivial, hf⟩) (fun _ _ _ ↦ ⟨trivial, rfl⟩) fun k' _ ↦ by
        have e : ∀ b, (tZ π x₁ (h, k, Function.update k' (π (x₁, k x₁)).1 b) =
            tZ π x₂ (h, k, Function.update k' (π (x₁, k x₁)).1 b)) ↔
            (π (x₁, k x₁)).2 + b = (π (x₂, k x₂)).2 + k' (π (x₂, k x₂)).1 := fun b ↦ by
          show (π (x₁, k x₁)).2 + Function.update k' (π (x₁, k x₁)).1 b (π (x₁, k x₁)).1 =
              (π (x₂, k x₂)).2 + Function.update k' (π (x₁, k x₁)).1 b (π (x₂, k x₂)).1 ↔ _
          rw [Function.update_self, Function.update_of_ne (Ne.symm hy)]
        simp only [e]
        exact sum_ite_eq_le_one (fun b ↦ (π (x₁, k x₁)).2 + b) (add_right_injective _) _

/-- **The failure fraction of one search**: on at most `N (G |K'| + |H|) / |Z| + N² / |Z| +
(g / |X|)^N` of the total tables do all `N` trials (at distinct blocks) touch `K'` or `H` or
fail. A touch is charged by `PermGood` and the fresh `k'`-value, a shared `h`-cell by
`card_mul_card_coll_le`, and the rest fail independently on distinct fresh `h`-cells. -/
theorem frac_fail_le {π : Equiv.Perm (X₁ × Z₁)} {G : ℕ} (hπ : PermGood π G) (K' : Finset X₁)
    (H : Finset Z₁) (B : ℕ → X₁) (N : ℕ) (hB : ∀ i < N, ∀ j < N, B i = B j → i = j)
    (Cw : X₁ → Prop) [DecidablePred Cw] (g : ℕ)
    (hg : ∀ y, ∑ v, (if ¬ Cw (y + v) then 1 else 0) ≤ g)
    (F : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁) → Prop) [DecidablePred F]
    (hF : ∀ t, F t → ∀ j < N, (tY π (B j) t ∈ K' ∨ tZ π (B j) t ∈ H) ∨
      ¬ Cw (tY π (B j) t + t.1 (tZ π (B j) t))) :
    ((Finset.univ.filter F).card : ℝ≥0∞) / Fintype.card ((Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁)) ≤
      ((N * (G * K'.card + H.card) + N * N : ℕ) : ℝ≥0∞) / Fintype.card Z₁ +
        ((g ^ N : ℕ) : ℝ≥0∞) / ((Fintype.card X₁ ^ N : ℕ) : ℝ≥0∞) := by
  classical
  set T := Fintype.card ((Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁))
  have hT : T = Fintype.card (Z₁ → X₁) * Fintype.card (X₁ → Z₁) * Fintype.card (X₁ → Z₁) := by
    simp only [T, Fintype.card_prod, mul_assoc]
  have hTpos : 0 < T := Fintype.card_pos
  have hZpos : 0 < Fintype.card Z₁ := Fintype.card_pos
  set Bl : Finset X₁ := (Finset.range N).image B
  set Bad : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁) → Prop := fun t ↦ ∃ x ∈ Bl, BadBlk π K' H x t
  set Coll : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁) → Prop :=
    fun t ↦ ∃ i < N, ∃ j < N, i ≠ j ∧ tZ π (B i) t = tZ π (B j) t
  set AllF : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁) → Prop := fun t ↦
    (∀ i < N, ∀ j < N, tZ π (B i) t = tZ π (B j) t → i = j) ∧
      ∀ j < N, ¬ Cw (tY π (B j) t + t.1 (tZ π (B j) t))
  have hsplit : ∀ t, F t → Bad t ∨ Coll t ∨ AllF t := fun t ht ↦ by
    by_cases hb : Bad t
    · exact .inl hb
    by_cases hc : Coll t
    · exact .inr (.inl hc)
    refine .inr (.inr ⟨fun i hi j hj he ↦ by_contra fun hne ↦ hc ⟨i, hi, j, hj, hne, he⟩,
      fun j hj ↦ ?_⟩)
    rcases hF t ht j hj with h | h
    · exact absurd ⟨B j, Finset.mem_image_of_mem B (Finset.mem_range.mpr hj), h⟩ hb
    · exact h
  have hcard : (Finset.univ.filter F).card ≤ (Finset.univ.filter Bad).card +
      ((Finset.univ.filter Coll).card + (Finset.univ.filter AllF).card) :=
    (card_filter_le_add_of_imp F Bad (fun t ↦ Coll t ∨ AllF t) hsplit).trans
      (Nat.add_le_add_left (card_filter_le_add_of_imp _ Coll AllF fun _ h ↦ h) _)
  have hBl : Bl.card ≤ N := Finset.card_image_le.trans (Finset.card_range N).le
  have h1 : Fintype.card Z₁ * (Finset.univ.filter Bad).card ≤
      T * (N * (G * K'.card + H.card)) :=
    (card_mul_card_filter_le_of_blocks hπ K' H Bl Bad fun _ h ↦ h).trans
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hBl))
  have h2 : Fintype.card Z₁ * (Finset.univ.filter Coll).card ≤ T * (N * N) := by
    have hle : (Finset.univ.filter Coll).card ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ∑ t, (if i ≠ j ∧ tZ π (B i) t = tZ π (B j) t then 1 else 0) := by
      rw [Finset.card_filter]
      calc ∑ t, (if Coll t then 1 else 0)
          ≤ ∑ t, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
              (if i ≠ j ∧ tZ π (B i) t = tZ π (B j) t then 1 else 0) :=
            Finset.sum_le_sum fun t _ ↦ by
              by_cases hc : Coll t
              · rw [ite_eq_left hc]
                obtain ⟨i, hi, j, hj, hne, he⟩ := hc
                exact one_le_sum_sum_of _ (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj)
                  (by rw [ite_eq_left ⟨hne, he⟩])
              · rw [ite_eq_right hc]
                exact Nat.zero_le _
        _ = _ := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
    have hpair : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N, Fintype.card Z₁ *
        ∑ t, (if i ≠ j ∧ tZ π (B i) t = tZ π (B j) t then 1 else 0) ≤ T := by
      intro i hi j hj
      by_cases hne : i = j
      · refine le_of_eq_of_le (by rw [Finset.sum_eq_zero fun t _ ↦ ite_eq_right
          fun h ↦ h.1 hne, mul_zero]) (Nat.zero_le _)
      · have hB' : B i ≠ B j := fun he ↦
          hne (hB i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) he)
        refine le_trans (Nat.mul_le_mul_left _ (sum_ite_le_of_imp _
          (fun t ↦ tZ π (B i) t = tZ π (B j) t) fun t h ↦ h.2)) ?_
        rw [hT]
        exact (card_mul_card_coll_le π hB').trans_eq (mul_one _)
    calc Fintype.card Z₁ * (Finset.univ.filter Coll).card
        ≤ Fintype.card Z₁ * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            ∑ t, (if i ≠ j ∧ tZ π (B i) t = tZ π (B j) t then 1 else 0) :=
          Nat.mul_le_mul_left _ hle
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, Fintype.card Z₁ *
            ∑ t, (if i ≠ j ∧ tZ π (B i) t = tZ π (B j) t then 1 else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ Finset.mul_sum _ _ _
      _ ≤ ∑ _i ∈ Finset.range N, ∑ _j ∈ Finset.range N, T :=
          Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦ hpair i hi j hj
      _ = T * (N * N) := by
          simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
          ring
  have h3 : Fintype.card X₁ ^ N * (Finset.univ.filter AllF).card ≤ T * g ^ N := by
    rw [Finset.card_filter, hT]
    exact pow_mul_card_allFail_le π B N Cw g hg
  have hXpos : 0 < Fintype.card X₁ ^ N := pow_pos Fintype.card_pos N
  calc ((Finset.univ.filter F).card : ℝ≥0∞) / T
      ≤ (((Finset.univ.filter Bad).card + ((Finset.univ.filter Coll).card +
          (Finset.univ.filter AllF).card) : ℕ) : ℝ≥0∞) / T := by
        gcongr
    _ = ((Finset.univ.filter Bad).card : ℝ≥0∞) / T + ((Finset.univ.filter Coll).card : ℝ≥0∞) / T
          + ((Finset.univ.filter AllF).card : ℝ≥0∞) / T := by
        push_cast
        rw [ENNReal.add_div, ENNReal.add_div, add_assoc]
    _ ≤ ((N * (G * K'.card + H.card) : ℕ) : ℝ≥0∞) / Fintype.card Z₁ +
          ((N * N : ℕ) : ℝ≥0∞) / Fintype.card Z₁ +
          ((g ^ N : ℕ) : ℝ≥0∞) / ((Fintype.card X₁ ^ N : ℕ) : ℝ≥0∞) :=
        add_le_add (add_le_add (natCast_div_le_div_of_mul_le hZpos hTpos h1)
          (natCast_div_le_div_of_mul_le hZpos hTpos h2))
          (natCast_div_le_div_of_mul_le hXpos hTpos h3)
    _ = _ := by
        rw [← ENNReal.add_div]
        push_cast
        rfl

end count

/-- A value of a function on a finite type lies in its image (over abstract types). -/
theorem mem_image_univ_of {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) (a : α) :
    f a ∈ Finset.univ.image f :=
  Finset.mem_image_of_mem f (Finset.mem_univ a)

/-! ## The in-table cells and the failure fraction -/

section slotCells

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- The `k'`-cells of the in-table slots at the values `w` (by output position and round). -/
noncomputable def k'CellsV (pub : Pub) (w : ValPos → Digest) : Finset X :=
  Finset.univ.image fun q : ValPos × Fin 8 ↦ srcCellK' pub (outSlot q.1) w q.2

/-- The `h`-cells of the in-table slots at the values `w`. -/
noncomputable def hCellsV (pub : Pub) (w : ValPos → Digest) : Finset Z :=
  Finset.univ.image fun q : ValPos × Fin 8 ↦ srcCellH pub (outSlot q.1) w q.2

open scoped Classical in
/-- **The cells of all in-table slots**, as a hardwiring with a dummy value: every cell a
signature may program. -/
noncomputable def slotHw (pub : Pub) (w : ValPos → Digest) : Hw X Z :=
  (fun z ↦ if z ∈ hCellsV pub w then some 0 else none,
    fun x ↦ if x ∈ slotCellsK pub w then some 0 else none,
    fun x ↦ if x ∈ k'CellsV pub w then some 0 else none)

theorem card_k'CellsV_le (pub : Pub) (w : ValPos → Digest) :
    (k'CellsV pub w).card ≤ 8 * (498 * 2 ^ 32) :=
  Finset.card_image_le.trans (by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    exact (Nat.mul_le_mul_right 8 card_valPos_le).trans_eq (by ring))

theorem card_hCellsV_le (pub : Pub) (w : ValPos → Digest) :
    (hCellsV pub w).card ≤ 8 * (498 * 2 ^ 32) :=
  Finset.card_image_le.trans (by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    exact (Nat.mul_le_mul_right 8 card_valPos_le).trans_eq (by ring))

theorem sum_not_eq {B : Type} [Fintype B] (P : B → Prop) [DecidablePred P] :
    ∑ b : B, (if ¬ P b then 1 else 0) = Fintype.card B - (Finset.univ.filter P).card := by
  rw [← Finset.card_filter]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset B)) P
  rw [Finset.card_univ] at h
  omega

/-- The non-codeword values of a trial cell. -/
theorem sum_not_codeword_le (y : X) :
    ∑ w : X, (if ¬ Codeword.Valid (trunc128 (y + w)) then 1 else 0) ≤
      Fintype.card X - cwCount * 2 ^ 960 := by
  rw [sum_not_eq, card_codeword_trunc128 y]

theorem trY_ofFunDbs (π : Equiv.Perm (X × Z)) (P : PublicParameter) (lab : RLabel)
    (b : Randomizer) (j : ℕ) (t : (Z → X) × (X → Z) × (X → Z)) :
    trY π P lab b j (ofFunDbs t) = tY π (cwBlk P lab b j) t := rfl

theorem trZ_ofFunDbs (π : Equiv.Perm (X × Z)) (P : PublicParameter) (lab : RLabel)
    (b : Randomizer) (j : ℕ) (t : (Z → X) × (X → Z) × (X → Z)) :
    trZ π P lab b j (ofFunDbs t) = tZ π (cwBlk P lab b j) t := rfl

theorem trW_ofFunDbs (π : Equiv.Perm (X × Z)) (P : PublicParameter) (lab : RLabel)
    (b : Randomizer) (j : ℕ) (t : (Z → X) × (X → Z) × (X → Z)) :
    trW π P lab b j (ofFunDbs t) = t.1 (tZ π (cwBlk P lab b j) t) := rfl

end slotCells

end Quantum.Xmss.Assembly

end
