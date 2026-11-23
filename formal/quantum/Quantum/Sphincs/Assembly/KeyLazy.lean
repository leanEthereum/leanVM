module

public import Quantum.Sphincs.Assembly.ProgSafe
public import Quantum.Sphincs.Assembly.RecJ
public import Quantum.Sphincs.Assembly.GameCongr
public import Quantum.Xmss.Assembly.KeyLazy
public import Quantum.Xmss.Hybrid.Mismatch

@[expose] public section

/-!
# The fresh `k`, `k'` program flips of leanSPHINCS's game, averaged over the keys

leanXMSS's `Quantum.Xmss.Assembly.KeyLazy` for leanSPHINCS's template. RecJ's `uavg_recJPre_le`
and EncRefined need the averaged target-free fresh flips `kfPre` (EncPorts' `kfW` along the
challenge prefix), ProgSafe's `uavg_progW_le_kW_gameT` the averaged fresh flips `kW`. Averaged over
the keys `k`, `k'` both are at most `2^-301 progCap`.

* **Lazy sampling of a key cell** (`KRel`, `totalWeight_tcW_eq_of_krel`, generic in the hidden
  coordinates `S` and the memory `M`): realized programs agreeing command by command until a
  program port at the cell, from states agreeing on the block of register states with the cell
  free, give equal weights read at the touched ports (leanXMSS's argument, whose runtime part is
  stated there for leanXMSS's coordinates only).
* **The game at keys differing in one cell** (`prel_pathCells_k`, `prel_pathCells_k'`,
  `krel_gameT`, `krel_prefixT`): every template port is a round of an absorption (`pathCells`:
  structural slots and `H_msg` calls alike); the rounds agree up to the first round at the cell
  (`rnAgree_keysK`), whose port carries the keys' values there. The counter search reads the
  public data only through `PK.seed` and `π` (GameCongr's `grindK_pub`).
* **Averaging over the keys** (`sum_kfTot_le_of_krel`, `sum_kfTot_gameR_le`,
  `sum_kfPre_le`): summed over the keys, cell by cell, the resampled flips are `2^-301` times the
  traces at the `k`, `k'` ports, at most `progCap` program calls (`uavg_kfSet_le`: the
  target-free flip set depends on the table only through `π`, capacity-scale counts at grade
  `2^68`).
* **`kW` is target-free** (`kFlip_le_kfW`, `kW_le_kfTot`): a fresh flip into `Bad` (Struct, Enc or
  coverage, all `HwTargetBad` with antitone targets) is a target-free flip (leanXMSS's
  `flipK_facts`), at low grade along the run.
* **Over the coordinates** (`uavg_kfPre_le`, `uavg_kW_le`): averaged over template data whose keys
  are uniform coordinates (KeysReparam's `pubK`, `valK`), at most `2^-301 progCap`, for every
  digest policy, without bad fraction.
* **Over the tables** (`uavg_kfTot_table_le`, `uavg_kfPre_table_le`, `uavg_kW_table_le`): on a
  good set of padded tables inside `FullG`, `keyE`'s game congruence `hgame_keyE` holds only off
  the charged coordinates `chgB t`, which depend on the table's keys. Mismatch's
  `totalWeight_le_mismatch` moves the flips to the coordinates' hidden values at the price of
  `progCap` times the record mass of the charged set, averaged label by label over the
  never-revealed part (`sum_revW_le`): at most `2^-301 progCap + progCap · R · εB`, where every
  path records at most `R` candidate coordinates of `J` and each candidate is charged for at most
  an `εB` fraction of the never-revealed parts.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe w w₁

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Assembly Quantum.Xmss.Hybrid Sphincs
open HashSig (Digest Message PublicParameter)
open Quantum.Xmss (X Z)

namespace Quantum.Sphincs.Assembly

/-! ## Calls of runtime 2 with record ports on the block of a free cell -/

section block

variable {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]
  (m₀ : Finset S × M) (Fr : Hw X Z → Prop)

/-- **Every port keeps the agreement on the block of `Fr`** when no program creates `Fr`. -/
theorem agr_runtimeR_step (hFr : ∀ c W, Fr (progUpdate c W) → Fr W)
    (i : (recHwSpec X Z S M).Port) (r : (recHwSpec X Z S M).Result i)
    (σ σ' : Matrix ((recHwSpec X Z S M).In i × (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z S M).In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (h : Agr (fun p ↦ Fr p.2.2.1) σ σ') :
    Agr (fun p : (recHwSpec X Z S M).Out i × (runtimeR (X := X) (Z := Z) m₀).D ↦ Fr p.2.2.1)
      (((runtimeR m₀).step i).branch r σ) (((runtimeR m₀).step i).branch r σ') := by
  rcases i with ((i | c) | c) | T
  · have hb : ∀ τ, ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r τ =
        MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U i) τ := fun τ ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m₀ i r) τ
    rw [hb, hb]
    refine agr_conj _ (fun q' q hK hq ↦ ?_) h
    have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m₀ i q.1 q'.1 q.2 q'.2 hK
    rwa [congrArg Prod.fst he] at hq
  · have hb : ∀ τ, ((runtimeR m₀).step (.inl (.inl (.inr c)))).branch r τ =
        MatrixMap.conj (hwReadKraus c r) τ := fun τ ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c r) τ
    rw [hb, hb]
    refine agr_conj _ (fun q' q hK hq ↦ ?_) h
    rwa [Quantum.Xmss.Assembly.hwReadKraus_ne_zero_hw c r (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK] at hq
  · have hb : ∀ τ, ((runtimeR m₀).step (.inl (.inr c))).branch r τ =
        MatrixMap.conj (hwProgKraus c r) τ := fun τ ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) τ
    rw [hb, hb]
    refine agr_conj _ (fun q' q hK hq ↦ ?_) h
    have he := hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK
    rw [congrArg Prod.fst he] at hq
    exact hFr c _ hq
  · refine agr_conj (recKraus T r) (fun q' q hK hq ↦ ?_) h
    rwa [congrArg Prod.fst (recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK)]
      at hq

/-- **A program port destroying `Fr`** makes all its outputs agree on the block. -/
theorem agr_runtimeR_step_out (c : HwProg X Z) (hc : ∀ W, ¬Fr (progUpdate c W))
    (r : c.Result)
    (σ σ' : Matrix ((recHwSpec X Z S M).In (.inl (.inr c)) ×
        (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z S M).In (.inl (.inr c)) × (runtimeR (X := X) (Z := Z) m₀).D) ℂ) :
    Agr (fun p : (recHwSpec X Z S M).Out (.inl (.inr c)) ×
        (runtimeR (X := X) (Z := Z) m₀).D ↦ Fr p.2.2.1)
      (((runtimeR m₀).step (.inl (.inr c))).branch r σ)
      (((runtimeR m₀).step (.inl (.inr c))).branch r σ') := by
  have hb : ∀ τ, ((runtimeR m₀).step (.inl (.inr c))).branch r τ =
      MatrixMap.conj (hwProgKraus c r) τ := fun τ ↦
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) τ
  rw [hb, hb]
  refine agr_conj_out _ (fun q' q hK hq ↦ ?_) _ _
  have he := hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK
  rw [congrArg Prod.fst he] at hq
  exact hc _ hq

end block

/-! ## Programs agreeing until a touched cell

`KRel tc a a' y y'`: the realized programs `y`, `y'` agree command by command until a program port
whose touch value `tc c` is set; there `y` calls a port of touch value `a`, `y'` one of touch value
`a'`, and their continuations are arbitrary. -/

section krel

variable {S M : Type} (tc : HwProg X Z → Option Z)

/-- The touch value of a command: `tc c` at a program port `c`, `none` elsewhere. -/
def cmdTc {A : QReg} : QuantumComp.Cmd LocalSig.instruments.{0} (recHwSpec X Z S M) A →
    Option Z
  | .query (.inl (.inr c)) _ _ => tc c
  | _ => none

/-- **Programs agreeing until a touched cell.** -/
def KRel (a a' : Z) {Ω : QReg → Type w} : {A : QReg} →
    IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z S M)) Ω A →
    IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z S M)) Ω A → Prop
  | _, .pure y, y' => y' = .pure y
  | _, .liftBind c next, y' =>
      (cmdTc tc c = some a ∧ ∃ c' next', cmdTc tc c' = some a' ∧ y' = .liftBind c' next') ∨
        (cmdTc tc c = none ∧ ∃ next', y' = .liftBind c next' ∧
          ∀ b, KRel a a' (next b) (next' b))

/-- **Programs without touched ports.** -/
def NoTc {Ω : QReg → Type w} : {A : QReg} →
    IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z S M)) Ω A → Prop
  | _, .pure _ => True
  | _, .liftBind c next => cmdTc tc c = none ∧ ∀ b, NoTc (next b)

variable {tc} {a a' : Z} {Ω : QReg → Type w} {A : QReg}

theorem krel_primBind (o : LocalSig.instruments.{0}.Op A)
    {k k' : (b : LocalSig.instruments.{0}.Outcome o) →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
        (LocalSig.instruments.{0}.next o b)} (hk : ∀ b, KRel tc a a' (k b) (k' b)) :
    KRel tc a a' (QuantumComp.primBind o k) (QuantumComp.primBind o k') :=
  Or.inr ⟨rfl, _, rfl, fun b ↦ hk b.down⟩

theorem krel_queryBind_same (i : (recHwSpec X Z S M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z S M).In i × E)
    (hi : cmdTc (S := S) (M := M) tc (.query i E ℓ) = none)
    {k k' : (recHwSpec X Z S M).Result i →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
        (QReg.of ((recHwSpec X Z S M).Out i × E))} (hk : ∀ r, KRel tc a a' (k r) (k' r)) :
    KRel tc a a' (QuantumComp.queryBind i E ℓ k) (QuantumComp.queryBind i E ℓ k') :=
  Or.inr ⟨hi, _, rfl, fun r ↦ hk r.down⟩

theorem krel_queryBind_touch (i : (recHwSpec X Z S M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z S M).In i × E) (i' : (recHwSpec X Z S M).Port) (E' : QReg)
    (ℓ' : A ≃ (recHwSpec X Z S M).In i' × E')
    (hi : cmdTc (S := S) (M := M) tc (.query i E ℓ) = some a)
    (hi' : cmdTc (S := S) (M := M) tc (.query i' E' ℓ') = some a')
    (k : (recHwSpec X Z S M).Result i →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
        (QReg.of ((recHwSpec X Z S M).Out i × E)))
    (k' : (recHwSpec X Z S M).Result i' →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
        (QReg.of ((recHwSpec X Z S M).Out i' × E'))) :
    KRel tc a a' (QuantumComp.queryBind i E ℓ k) (QuantumComp.queryBind i' E' ℓ' k') :=
  Or.inl ⟨hi, _, _, hi', rfl⟩

theorem krel_primBind_inv {o : LocalSig.instruments.{0}.Op A}
    {k : (b : LocalSig.instruments.{0}.Outcome o) →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
        (LocalSig.instruments.{0}.next o b)}
    {y' : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A}
    (h : KRel tc a a' (QuantumComp.primBind o k) y') :
    ∃ k', y' = QuantumComp.primBind o k' ∧ ∀ b, KRel tc a a' (k b) (k' b) := by
  rcases h with ⟨h1, -⟩ | ⟨-, next', rfl, hn⟩
  · simp [cmdTc] at h1
  · exact ⟨fun b ↦ next' (ULift.up b), rfl, fun b ↦ hn (ULift.up b)⟩

theorem krel_queryBind_inv {i : (recHwSpec X Z S M).Port} {E : QReg}
    {ℓ : A ≃ (recHwSpec X Z S M).In i × E}
    {k : (recHwSpec X Z S M).Result i →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω
        (QReg.of ((recHwSpec X Z S M).Out i × E))}
    {y' : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A}
    (h : KRel tc a a' (QuantumComp.queryBind i E ℓ k) y') :
    (cmdTc tc (.query i E ℓ) = some a ∧ ∃ c' next', cmdTc tc c' = some a' ∧
        y' = IFreeM.liftBind c' next') ∨
      (cmdTc tc (.query i E ℓ) = none ∧ ∃ k', y' = QuantumComp.queryBind i E ℓ k' ∧
        ∀ r, KRel tc a a' (k r) (k' r)) := by
  rcases h with h | ⟨h1, next', rfl, hn⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, fun r ↦ next' (ULift.up r), rfl, fun r ↦ hn (ULift.up r)⟩

theorem krel_refl {y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0}
    (recHwSpec X Z S M)) Ω A} (h : NoTc tc y) : KRel tc a a' y y := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind _ c next ih => exact Or.inr ⟨h.1, next, rfl, fun b ↦ ih b (h.2 b)⟩

theorem krel_bind {Ω' : QReg → Type w₁}
    {x x' : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z S M)) Ω A}
    {g g' : ∀ u, Ω u →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z S M)) Ω' u}
    (hx : KRel tc a a' x x') (hg : ∀ u y, KRel tc a a' (g u y) (g' u y)) :
    KRel tc a a' (x.bind g) (x'.bind g') := by
  induction x using IFreeM.inductionOn with
  | pure _ y =>
    obtain rfl : x' = IFreeM.pure y := hx
    exact hg _ y
  | liftBind _ c next ih =>
    rcases hx with ⟨hc, c', next', hc', rfl⟩ | ⟨hc, next', rfl, hn⟩
    · exact Or.inl ⟨hc, c', _, hc', rfl⟩
    · exact Or.inr ⟨hc, _, rfl, fun b ↦ ih b (hn b)⟩

theorem krel_cast {A' : QReg} (e : A = A')
    {y y' : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z S M)) Ω A} :
    KRel tc a a' (e ▸ y) (e ▸ y') ↔ KRel tc a a' y y' := by
  subst e
  rfl

theorem krel_bind₂ {B C : QReg} {α β : Type}
    {x x' : QuantumComp₂ LocalSig.instruments.{0} (recHwSpec X Z S M) A B α}
    {g g' : α → QuantumComp₂ LocalSig.instruments.{0} (recHwSpec X Z S M) B C β}
    (hx : KRel tc a a' x x') (hg : ∀ b, KRel tc a a' (g b) (g' b)) :
    KRel tc a a' (x.bind g) (x'.bind g') := by
  refine krel_bind hx fun u p ↦ ?_
  obtain ⟨e, b⟩ := p
  subst e
  exact hg b

theorem krel_substitute {spec₀ : QuantumOracleSpec.{0, 0}}
    {σ σ' : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z S M))}
    (hσ : ∀ A c, KRel tc a a' (σ A c) (σ' A c)) {Ω : QReg → Type}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀) Ω A) :
    KRel tc a a' (x.substitute σ) (x.substitute σ') := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind, IFreeM.substitute_liftBind]
    exact krel_bind (hσ s c) fun u ans ↦ (krel_cast ans.2).mpr (ih ans.1)

end krel

/-! ## Weights read at the touched ports, and their totals on related programs -/

section tcWeight

variable {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]
  (tc : HwProg X Z → Option Z)

/-- **Weights read only at the touched ports**: `g a` at a program port of touch value `a`, `0`
elsewhere. -/
noncomputable def tcW (m₀ : Finset S × M)
    (g : Z → Matrix (Unit × (runtimeR (X := X) (Z := Z) m₀).D)
      (Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞) :
    ∀ i : (recHwSpec X Z S M).Port,
      Matrix ((recHwSpec X Z S M).In i × (runtimeR (X := X) (Z := Z) m₀).D)
        ((recHwSpec X Z S M).In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞ :=
  extWeight (hwCost (fun _ _ ↦ 0) fun c σ ↦ (tc c).elim 0 fun a ↦ g a σ)

/-- **A call of a port destroying `Fr`** makes all its outputs agree on the block (with `0`). -/
theorem agr_queryStep_touch (m₀ : Finset S × M) (Fr : Hw X Z → Prop)
    (htc : ∀ c b, tc c = some b → ∀ W, ¬Fr (progUpdate c W))
    (c : HwProg X Z) (b : Z) (hb : tc c = some b) {A : QReg} (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z S M).In (.inl (.inr c)) × E) (r : c.Result)
    (τ : Matrix (A × (runtimeR (X := X) (Z := Z) m₀).D) (A × (runtimeR (X := X) (Z := Z) m₀).D) ℂ) :
    Agr (fun p ↦ Fr p.2.2.1) (((runtimeR m₀).queryStep (.inl (.inr c)) E ℓ).branch r τ) 0 := by
  have h := agr_queryStep_out (runtimeR m₀) (fun s ↦ Fr s.2.1) (.inl (.inr c)) E ℓ r
    (fun σ σ' ↦ agr_runtimeR_step_out m₀ Fr c (htc c b hb) r σ σ') τ 0
  rwa [map_zero] at h

variable {tc} (m₀ : Finset S × M) {Fr : Hw X Z → Prop}
  (hFr : ∀ c W, Fr (progUpdate c W) → Fr W)

include hFr in
/-- **A touched-port weight vanishes from a state without mass on the block.** -/
theorem totalWeight_tcW_eq_zero
    {g : Z → Matrix (Unit × (runtimeR (X := X) (Z := Z) m₀).D)
      (Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞}
    (hg0 : ∀ b σ, (∀ s : (runtimeR (X := X) (Z := Z) m₀).D, Fr s.2.1 → σ ((), s) ((), s) = 0) →
      g b σ = 0)
    {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A)
    (ρ : Matrix (A × (runtimeR (X := X) (Z := Z) m₀).D) (A × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (hρ : Agr (fun p ↦ Fr p.2.2.1) ρ 0) :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments (tcW tc m₀ g) y ρ = 0 := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => exact totalWeight_pure _ _ _ _
  | primBind _ o k ih =>
    rw [totalWeight_primBind]
    refine ENNReal.tsum_eq_zero.2 fun b ↦ ih b _ ?_
    have h := agr_frame (P := fun s : (runtimeR (X := X) (Z := Z) m₀).D ↦ Fr s.2.1) o b hρ
    rwa [map_zero] at h
  | queryBind _ i E ℓ k ih =>
    rw [totalWeight_queryBind]
    have hr : ∀ r, Agr (fun p ↦ Fr p.2.2.1) (((runtimeR m₀).queryStep i E ℓ).branch r ρ) 0 :=
      fun r ↦ by
        have h := agr_queryStep (runtimeR m₀) (fun s ↦ Fr s.2.1) i E ℓ r
          (agr_runtimeR_step m₀ Fr hFr i r) hρ
        rwa [map_zero] at h
    rw [ENNReal.tsum_eq_zero.2 fun r ↦ ih r _ (hr r), add_zero]
    rcases i with ((i | c) | c) | T
    · rfl
    · rfl
    · show (tc c).elim 0 (fun a ↦ g a (callInput ℓ _ ρ)) = 0
      rcases tc c with _ | b
      · rfl
      · exact hg0 b _ fun s hs ↦ (callInput_unit_diag (runtimeR m₀) ℓ ρ s).trans
          (Finset.sum_eq_zero fun x _ ↦ hρ (x, s) (x, s) hs hs)
    · rfl

include hFr in
/-- **The touched-port weights of related programs agree.** Let `y` and `y'` agree until a
touched port (`KRel`), from states agreeing on the block of `Fr`, every touched port destroying
`Fr`. If `g a` and `g' a'` agree on operators with the same diagonal on the block, and vanish on
operators without diagonal there, the total weights agree. -/
theorem totalWeight_tcW_eq_of_krel
    (htc : ∀ c b, tc c = some b → ∀ W, ¬Fr (progUpdate c W)) {a a' : Z}
    {g g' : Z → Matrix (Unit × (runtimeR (X := X) (Z := Z) m₀).D)
      (Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞}
    (hg0 : ∀ b σ, (∀ s : (runtimeR (X := X) (Z := Z) m₀).D, Fr s.2.1 → σ ((), s) ((), s) = 0) →
      g b σ = 0)
    (hg0' : ∀ b σ, (∀ s : (runtimeR (X := X) (Z := Z) m₀).D, Fr s.2.1 → σ ((), s) ((), s) = 0) →
      g' b σ = 0)
    (hgg : ∀ σ σ', (∀ s : (runtimeR (X := X) (Z := Z) m₀).D, Fr s.2.1 →
      σ ((), s) ((), s) = σ' ((), s) ((), s)) → g a σ = g' a' σ')
    {Ω : QReg → Type} {A : QReg}
    (y y' : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z S M) Ω A)
    (h : KRel tc a a' y y')
    (ρ ρ' : Matrix (A × (runtimeR (X := X) (Z := Z) m₀).D)
      (A × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (hρ : Agr (fun p ↦ Fr p.2.2.1) ρ ρ') :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments (tcW tc m₀ g) y ρ =
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments (tcW tc m₀ g') y' ρ' := by
  induction y using QuantumComp.inductionOn with
  | pure _ x =>
    obtain rfl : y' = QuantumComp.pure x := h
    rw [totalWeight_pure, totalWeight_pure]
  | primBind _ o k ih =>
    obtain ⟨k', rfl, hk⟩ := krel_primBind_inv h
    rw [totalWeight_primBind, totalWeight_primBind]
    exact tsum_congr fun b ↦ ih b (k' b) (hk b) _ _
      (agr_frame (P := fun s : (runtimeR (X := X) (Z := Z) m₀).D ↦ Fr s.2.1) o b hρ)
  | queryBind _ i E ℓ k ih =>
    rcases krel_queryBind_inv h with ⟨hi, c', next', hc', rfl⟩ | ⟨hi, k', rfl, hk⟩
    · rcases i with ((i | c) | c) | T
      · simp [cmdTc] at hi
      · simp [cmdTc] at hi
      swap
      · simp [cmdTc] at hi
      have hi₀ : tc c = some a := hi
      rcases c' with o' | ⟨((i' | c₀) | c₀) | T', E', ℓ'⟩
      · simp [cmdTc] at hc'
      · simp [cmdTc] at hc'
      · simp [cmdTc] at hc'
      swap
      · simp [cmdTc] at hc'
      have hc₀ : tc c₀ = some a' := hc'
      refine (totalWeight_queryBind (runtimeR m₀) LocalSig.Interp.instruments _ _ _ _ _).trans
        (Eq.trans ?_ (totalWeight_queryBind (runtimeR m₀) LocalSig.Interp.instruments
          (w := tcW tc m₀ g') (.inl (.inr c₀)) E' ℓ' (fun r ↦ next' (ULift.up r)) ρ').symm)
      have h1 : ∑' r, (runtimeR m₀).totalWeight LocalSig.Interp.instruments (tcW tc m₀ g) (k r)
          (((runtimeR m₀).queryStep (.inl (.inr c)) E ℓ).branch r ρ) = 0 :=
        ENNReal.tsum_eq_zero.2 fun r ↦ totalWeight_tcW_eq_zero m₀ hFr hg0 (k r) _
          (agr_queryStep_touch tc m₀ Fr htc c a hi₀ E ℓ r ρ)
      have h2 : ∑' r, (runtimeR m₀).totalWeight LocalSig.Interp.instruments (tcW tc m₀ g')
          (next' (ULift.up r)) (((runtimeR m₀).queryStep (.inl (.inr c₀)) E' ℓ').branch r ρ') =
            0 :=
        ENNReal.tsum_eq_zero.2 fun r ↦ totalWeight_tcW_eq_zero m₀ hFr hg0' (next' (ULift.up r)) _
          (agr_queryStep_touch tc m₀ Fr htc c₀ a' hc₀ E' ℓ' r ρ')
      refine (congrArg (_ + ·) h1).trans (Eq.trans ?_ (congrArg (_ + ·) h2).symm)
      rw [add_zero, add_zero]
      show (tc c).elim 0 (fun b ↦ g b (callInput ℓ _ ρ)) =
        (tc c₀).elim 0 (fun b ↦ g' b (callInput ℓ' _ ρ'))
      rw [hi₀, hc₀]
      exact hgg _ _ fun s hs ↦ (callInput_unit_diag (runtimeR m₀) ℓ ρ s).trans
        ((Finset.sum_congr rfl fun x _ ↦ hρ (x, s) (x, s) hs hs).trans
          (callInput_unit_diag (runtimeR m₀) ℓ' ρ' s).symm)
    · rw [totalWeight_queryBind, totalWeight_queryBind]
      have hw : ∀ (gg : Z → Matrix (Unit × (runtimeR (X := X) (Z := Z) m₀).D)
          (Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞) (σ : Matrix
            ((recHwSpec X Z S M).In i × (runtimeR (X := X) (Z := Z) m₀).D)
            ((recHwSpec X Z S M).In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ),
          tcW tc m₀ gg i σ = 0 := by
        intro gg σ
        rcases i with ((i | c) | c) | T
        · rfl
        · rfl
        · show (tc c).elim 0 (fun a ↦ gg a σ) = 0
          rw [show tc c = none from hi]
          rfl
        · rfl
      rw [hw, hw]
      exact congrArg (0 + ·) (tsum_congr fun r ↦ ih r (k' r) (hk r) _ _
        (agr_queryStep (runtimeR m₀) (fun s ↦ Fr s.2.1) i E ℓ r
          (agr_runtimeR_step m₀ Fr hFr i r) hρ))

end tcWeight

/-! ## The rounds of an absorption at keys differing in one cell -/

section rounds

variable {P : PublicParameter} {π : Equiv.Perm (X × Z)} {h : Z → X}

/-- The program ports of round `j` of an absorption of `n` blocks (`pathCells`). -/
def cellPorts (pub : Pub) (b : ℕ → X) (cor : X → X → X) (n j : ℕ) : List (HwProg X Z) :=
  [.programK (cellK pub b j).1 (cellK pub b j).2,
    .programK' (cellK' pub b j).1 (cellK' pub b j).2,
    .programH (cellH pub b (n - 1) cor j).1 (cellH pub b (n - 1) cor j).2]

theorem pathCells_eq (pub : Pub) (b : ℕ → X) (cor : X → X → X) (n : ℕ) :
    pathCells pub b cor n = (List.range' 0 n).flatMap (cellPorts pub b cor n) := by
  rw [pathCells, ← List.range_eq_range']
  rfl

theorem cellPorts_keys (k k' : X → Z) (b : ℕ → X) (cor : X → X → X) (n j : ℕ) :
    cellPorts ⟨P, π, (h, k, k')⟩ b cor n j =
      [.programK (rnK π h k k' b j) (k (rnK π h k k' b j)),
        .programK' (rnR π h k k' b j) (k' (rnR π h k k' b j)),
        .programH (rnZ π h k k' b j) (if j = n - 1 then cor (rnR π h k k' b j)
          (h (rnZ π h k k' b j)) else h (rnZ π h k k' b j))] := by
  unfold cellPorts
  rw [cellH_fst, cellH_snd]
  rfl

section keyK

variable {t t' k' : X → Z} {y : X} (ht : ∀ z, z ≠ y → t z = t' z)
include ht

theorem rnAgree_keysK (b : ℕ → X) {j : ℕ} (hj : ∀ i < j, rnK π h t k' b i ≠ y) :
    RnAgree π h t k' h t' k' b j :=
  fun i hi ↦ ⟨(ht _ (hj i hi)).symm, rfl, rfl⟩

/-- **The rounds of an absorption at keys differing at the `k` cell `y`** agree until the first
`k` port at `y`, which carries the keys' values there. -/
theorem prel_cells_k (b : ℕ → X) (cor : X → X → X) (n : ℕ) : ∀ m j₀,
    (∀ i < j₀, rnK π h t k' b i ≠ y) →
    PRel (tcK y) (t y) (t' y) ((List.range' j₀ m).flatMap (cellPorts ⟨P, π, (h, t, k')⟩ b cor n))
      ((List.range' j₀ m).flatMap (cellPorts ⟨P, π, (h, t', k')⟩ b cor n))
  | 0, _, _ => trivial
  | m + 1, j₀, hj => by
    rw [List.range'_succ, List.flatMap_cons, List.flatMap_cons, cellPorts_keys, cellPorts_keys]
    have hA := rnAgree_keysK ht b hj
    have hK : rnK π h t' k' b j₀ = rnK π h t k' b j₀ := rnK_congr hA
    by_cases hc : rnK π h t k' b j₀ = y
    · refine Or.inl ⟨?_, ?_⟩
      · rw [hc]
        exact tcK_programK_self y _
      · rw [hK, hc]
        exact tcK_programK_self y _
    · have e1 : t' (rnK π h t k' b j₀) = t (rnK π h t k' b j₀) := (ht _ hc).symm
      have hR : rnR π h t' k' b j₀ = rnR π h t k' b j₀ := rnR_congr hA e1
      have hZ : rnZ π h t' k' b j₀ = rnZ π h t k' b j₀ := rnZ_congr hA e1 rfl
      rw [hK, e1, hR, hZ]
      refine Or.inr ⟨rfl, tcK_programK_ne hc _, Or.inr ⟨rfl, rfl, Or.inr ⟨rfl, rfl,
        prel_cells_k b cor n m (j₀ + 1) fun i hi ↦ ?_⟩⟩⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hj i hi
      · exact hc

/-- **An absorption's realized ports at keys differing at the `k` cell `y`.** -/
theorem prel_pathCells_k (b : ℕ → X) (cor : X → X → X) (n : ℕ) :
    PRel (tcK y) (t y) (t' y) (pathCells ⟨P, π, (h, t, k')⟩ b cor n)
      (pathCells ⟨P, π, (h, t', k')⟩ b cor n) := by
  rw [pathCells_eq, pathCells_eq]
  exact prel_cells_k ht b cor n n 0 fun i hi ↦ absurd hi (Nat.not_lt_zero i)

/-- **A structural slot's realized ports at keys differing at the `k` cell `y`.** -/
theorem prel_slotPorts_k (s : Slot) (v : (s : HPos) → XD s) :
    PRel (tcK y) (t y) (t' y) ((slotPorts ⟨P, π, (h, t, k')⟩ s).map (LazyProg.realize v))
      ((slotPorts ⟨P, π, (h, t', k')⟩ s).map (LazyProg.realize v)) := by
  rw [slotPorts, slotPorts, realize_pathPorts, realize_pathPorts]
  exact prel_pathCells_k ht _ _ _

/-- **An `H_msg` call's realized ports at keys differing at the `k` cell `y`.** -/
theorem prel_hmsgPorts_k (pol : DigestPolicy) (T : Finset HPos) (msg : Message) (i : DigestCall)
    (v : (s : HPos) → XD s) :
    PRel (tcK y) (t y) (t' y) ((hmsgPorts ⟨P, π, (h, t, k')⟩ pol T msg i).map (LazyProg.realize v))
      ((hmsgPorts ⟨P, π, (h, t', k')⟩ pol T msg i).map (LazyProg.realize v)) := by
  rw [hmsgPorts, hmsgPorts, realize_pathPorts, realize_pathPorts]
  exact prel_pathCells_k ht _ _ _

end keyK

section keyK'

variable {k t t' : X → Z} {y : X} (ht : ∀ z, z ≠ y → t z = t' z)
include ht

theorem rnAgree_keysK' (b : ℕ → X) {j : ℕ} (hj : ∀ i < j, rnR π h k t b i ≠ y) :
    RnAgree π h k t h k t' b j :=
  fun i hi ↦ ⟨rfl, (ht _ (hj i hi)).symm, rfl⟩

/-- **The rounds of an absorption at keys differing at the `k'` cell `y`.** -/
theorem prel_cells_k' (b : ℕ → X) (cor : X → X → X) (n : ℕ) : ∀ m j₀,
    (∀ i < j₀, rnR π h k t b i ≠ y) →
    PRel (tcK' y) (t y) (t' y) ((List.range' j₀ m).flatMap (cellPorts ⟨P, π, (h, k, t)⟩ b cor n))
      ((List.range' j₀ m).flatMap (cellPorts ⟨P, π, (h, k, t')⟩ b cor n))
  | 0, _, _ => trivial
  | m + 1, j₀, hj => by
    rw [List.range'_succ, List.flatMap_cons, List.flatMap_cons, cellPorts_keys, cellPorts_keys]
    have hA := rnAgree_keysK' ht b hj
    have hK : rnK π h k t' b j₀ = rnK π h k t b j₀ := rnK_congr hA
    have hR : rnR π h k t' b j₀ = rnR π h k t b j₀ := rnR_congr hA rfl
    rw [hK, hR]
    have hk0 : tcK' y (.programK (rnK π h k t b j₀) (k (rnK π h k t b j₀))) = none := rfl
    by_cases hc : rnR π h k t b j₀ = y
    · refine Or.inr ⟨rfl, hk0, Or.inl ⟨?_, ?_⟩⟩
      · rw [hc]
        exact tcK'_programK'_self y _
      · rw [hc]
        exact tcK'_programK'_self y _
    · have e2 : t' (rnR π h k t b j₀) = t (rnR π h k t b j₀) := (ht _ hc).symm
      have hZ : rnZ π h k t' b j₀ = rnZ π h k t b j₀ := rnZ_congr hA rfl e2
      rw [e2, hZ]
      refine Or.inr ⟨rfl, hk0, Or.inr ⟨rfl, tcK'_programK'_ne hc _, Or.inr ⟨rfl, rfl,
        prel_cells_k' b cor n m (j₀ + 1) fun i hi ↦ ?_⟩⟩⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hj i hi
      · exact hc

/-- **An absorption's realized ports at keys differing at the `k'` cell `y`.** -/
theorem prel_pathCells_k' (b : ℕ → X) (cor : X → X → X) (n : ℕ) :
    PRel (tcK' y) (t y) (t' y) (pathCells ⟨P, π, (h, k, t)⟩ b cor n)
      (pathCells ⟨P, π, (h, k, t')⟩ b cor n) := by
  rw [pathCells_eq, pathCells_eq]
  exact prel_cells_k' ht b cor n n 0 fun i hi ↦ absurd hi (Nat.not_lt_zero i)

/-- **A structural slot's realized ports at keys differing at the `k'` cell `y`.** -/
theorem prel_slotPorts_k' (s : Slot) (v : (s : HPos) → XD s) :
    PRel (tcK' y) (t y) (t' y) ((slotPorts ⟨P, π, (h, k, t)⟩ s).map (LazyProg.realize v))
      ((slotPorts ⟨P, π, (h, k, t')⟩ s).map (LazyProg.realize v)) := by
  rw [slotPorts, slotPorts, realize_pathPorts, realize_pathPorts]
  exact prel_pathCells_k' ht _ _ _

/-- **An `H_msg` call's realized ports at keys differing at the `k'` cell `y`.** -/
theorem prel_hmsgPorts_k' (pol : DigestPolicy) (T : Finset HPos) (msg : Message) (i : DigestCall)
    (v : (s : HPos) → XD s) :
    PRel (tcK' y) (t y) (t' y) ((hmsgPorts ⟨P, π, (h, k, t)⟩ pol T msg i).map (LazyProg.realize v))
      ((hmsgPorts ⟨P, π, (h, k, t')⟩ pol T msg i).map (LazyProg.realize v)) := by
  rw [hmsgPorts, hmsgPorts, realize_pathPorts, realize_pathPorts]
  exact prel_pathCells_k' ht _ _ _

end keyK'

/-- Port lists related until a touched port, concatenated. -/
theorem prel_append {tc : HwProg X Z → Option Z} {a a' : Z} :
    ∀ {l₁ l₁' l₂ l₂' : List (HwProg X Z)}, PRel tc a a' l₁ l₁' → PRel tc a a' l₂ l₂' →
      PRel tc a a' (l₁ ++ l₂) (l₁' ++ l₂')
  | [], [], _, _, _, h₂ => h₂
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim
  | p :: ps, p' :: ps', _, _, h, h₂ => by
    rcases h with h | ⟨he, h0, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨he, h0, prel_append h h₂⟩

end rounds

/-! ## The realized games at keys differing in one cell -/

section gameRel

variable {M : Type} {tc : HwProg X Z → Option Z} {a a' : Z} (v : (s : HPos) → XD s)

/-- The condition of `NoProgT` on a command: no program port. -/
def CmdNoProg {A : QReg} :
    QuantumComp.Cmd LocalSig.instruments.{0} (SSpec M) A → Prop
  | .query (.inl (.inr _)) _ _ => False
  | _ => True

/-- **A template without program ports.** -/
def NoProgT {Ω : QReg → Type} :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (SSpec M)) Ω A → Prop
  | _, .pure _ => True
  | _, .liftBind c next => CmdNoProg c ∧ ∀ b, NoProgT (next b)

/-- **A realized template without program ports has no touched port.** -/
theorem noTc_realizeT {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (SSpec M) Ω A) :
    NoProgT y → NoTc tc (realizeT v y) := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _; trivial
  | primBind _ o k ih => exact fun hy ↦ ⟨rfl, fun b ↦ ih b.down (hy.2 (ULift.up b.down))⟩
  | queryBind _ i E ℓ k ih =>
    intro hy
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact ⟨rfl, fun r ↦ ih r.down (hy.2 (ULift.up r.down))⟩
    · exact ⟨rfl, fun r ↦ ih r.down (hy.2 (ULift.up r.down))⟩
    · exact hy.1.elim
    · exact ⟨rfl, fun r ↦ ih (restrictTo T v, r.down) (hy.2 (ULift.up (restrictTo T v, r.down)))⟩

/-- Read programs call no program port. -/
theorem noProgT_readLift {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω A) :
    NoProgT (readLift goodAll y) := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind _ c next ih =>
    show NoProgT (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
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

theorem krel_realizeT_bind₂ {A B C : QReg} {α β : Type} {x x' : QComp (SSpec M) A B α}
    {k k' : α → QComp (SSpec M) B C β} (hx : KRel tc a a' (realizeT v x) (realizeT v x'))
    (hk : ∀ b, KRel tc a a' (realizeT v (k b)) (realizeT v (k' b))) :
    KRel tc a a' (realizeT v (x.bind k)) (realizeT v (x'.bind k')) := by
  rw [realizeT_bind₂, realizeT_bind₂]
  exact krel_bind₂ hx hk

theorem krel_realizeT_revealThen {B C : QReg} {α : Type} (T : Finset HPos)
    {k k' : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B C α}
    (hk : ∀ r, KRel tc a a' (realizeT v (k r)) (realizeT v (k' r))) :
    KRel tc a a' (realizeT v (revealThen goodAll T k)) (realizeT v (revealThen goodAll T k')) := by
  rw [realizeT_revealThen_eq, realizeT_revealThen_eq]
  exact krel_queryBind_same _ B _ rfl fun r ↦ krel_primBind _ fun _ ↦ hk (restrictTo T v, r)

theorem krel_realizeT_bind {Ω Ω' : QReg → Type} {A : QReg}
    {x x' : QuantumComp LocalSig.instruments.{0} (SSpec M) Ω A}
    {g g' : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (SSpec M) Ω' u}
    (hx : KRel tc a a' (realizeT v x) (realizeT v x'))
    (hg : ∀ u y, KRel tc a a' (realizeT v (g u y)) (realizeT v (g' u y))) :
    KRel tc a a' (realizeT v (x.bind g)) (realizeT v (x'.bind g')) := by
  rw [realizeT_bind, realizeT_bind]
  exact krel_bind hx hg

theorem krel_realizeT_readLift {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω A) :
    KRel tc a a' (realizeT v (readLift goodAll y)) (realizeT v (readLift goodAll y)) :=
  krel_refl (noTc_realizeT v _ (noProgT_readLift y))

theorem krel_realizeT_substitute {spec₀ : QuantumOracleSpec.{0, 0}}
    {σ σ' : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (SSpec M))}
    (hσ : ∀ A c, KRel tc a a' (realizeT v (σ A c)) (realizeT v (σ' A c))) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀) Ω A) :
    KRel tc a a' (realizeT v (x.substitute σ)) (realizeT v (x.substitute σ')) := by
  rw [realizeT_substitute, realizeT_substitute]
  exact krel_substitute hσ x

variable (M) in
/-- **Port lists agreeing until a touched port** realize related programs. -/
theorem krel_progPorts (B : QReg) : ∀ ps ps' : List (LazyProg X Z HPos XD),
    PRel tc a a' (ps.map (LazyProg.realize v)) (ps'.map (LazyProg.realize v)) →
      KRel tc a a' (realizeT v (progPorts M B ps)) (realizeT v (progPorts M B ps'))
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | p :: ps, p' :: ps', h => by
    rcases h with ⟨h1, h2⟩ | ⟨he, h1, h⟩
    · rw [progPorts, progPorts]
      show KRel tc a a' (progR B (p.realize v) (realizeT v (progPorts M B ps)))
        (progR B (p'.realize v) (realizeT v (progPorts M B ps')))
      exact krel_queryBind_touch (Sum.inl (Sum.inr (p.realize v))) B _
        (Sum.inl (Sum.inr (p'.realize v))) B _ h1 h2 _ _
    · rw [progPorts, progPorts]
      show KRel tc a a' (progR B (p.realize v) (realizeT v (progPorts M B ps)))
        (progR B (p'.realize v) (realizeT v (progPorts M B ps')))
      rw [progR, progR, ← he]
      exact krel_queryBind_same (Sum.inl (Sum.inr (p.realize v))) B _ h1 fun _ ↦
        krel_primBind _ fun _ ↦ krel_progPorts B ps ps' h

variable (upd : TrialUpd M) (pol : DigestPolicy) {P : PublicParameter}
  {π : Equiv.Perm (X × Z)} {t t' : SpongeKeys X Z}
  (hs : ∀ s, PRel tc a a' ((slotPorts ⟨P, π, t⟩ s).map (LazyProg.realize v))
    ((slotPorts ⟨P, π, t'⟩ s).map (LazyProg.realize v)))

include hs

theorem krel_progSlots (B : QReg) : ∀ ss : List Slot,
    KRel tc a a' (realizeT v (progSlots M ⟨P, π, t⟩ B ss))
      (realizeT v (progSlots M ⟨P, π, t'⟩ B ss))
  | [] => rfl
  | s :: ss => krel_realizeT_bind₂ v (krel_progPorts M v B _ _ (hs s)) fun _ ↦
      krel_progSlots B ss

theorem krel_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    KRel tc a a' (realizeT v (forsOpenT M ⟨P, π, t⟩ B idx lv))
      (realizeT v (forsOpenT M ⟨P, π, t'⟩ B idx lv)) := by
  rw [forsOpenT, forsOpenT]
  exact krel_realizeT_revealThen v _ fun _ ↦
    krel_realizeT_bind₂ v (krel_progSlots v hs B _) fun _ ↦ rfl

theorem krel_signLayerT (B : QReg) (K : Key) :
    KRel tc a a' (realizeT v (signLayerT M upd ⟨P, π, t⟩ B K))
      (realizeT v (signLayerT M upd ⟨P, π, t'⟩ B K)) := by
  rw [signLayerT, signLayerT]
  refine krel_realizeT_revealThen v _ fun r₀ ↦ ?_
  rw [grindK_pub M upd (pub := ⟨P, π, t⟩) (pub' := ⟨P, π, t'⟩) rfl rfl]
  refine krel_realizeT_bind₂ v (krel_realizeT_readLift v _) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · rfl
  · exact krel_realizeT_revealThen v _ fun _ ↦
      krel_realizeT_bind₂ v (krel_progSlots v hs B _) fun _ ↦ rfl

variable (hm : ∀ T msg i, PRel tc a a' ((hmsgPorts ⟨P, π, t⟩ pol T msg i).map (LazyProg.realize v))
    ((hmsgPorts ⟨P, π, t'⟩ pol T msg i).map (LazyProg.realize v)))

include hm

theorem krel_signT (B : QReg) (msg : Message) :
    KRel tc a a' (realizeT v (signT M upd pol ⟨P, π, t⟩ B msg))
      (realizeT v (signT M upd pol ⟨P, π, t'⟩ B msg)) := by
  rw [signT, signT]
  refine krel_realizeT_revealThen v _ fun r₁ ↦ krel_realizeT_revealThen v _ fun r₂ ↦ ?_
  refine krel_realizeT_bind₂ v (krel_progPorts M v B _ _ ?_) fun _ ↦ ?_
  · rw [digestPorts, digestPorts, List.map_append, List.map_append]
    exact prel_append (hm _ _ _) (hm _ _ _)
  refine krel_realizeT_bind₂ v (krel_forsOpenT v hs B _ _) fun _ ↦ ?_
  refine krel_realizeT_bind₂ v (krel_signLayerT v upd hs B _) fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · rfl
  refine krel_realizeT_bind₂ v (krel_signLayerT v upd hs B _) fun s₁ ↦ ?_
  rcases s₁ with _ | middle
  · rfl
  exact krel_realizeT_bind₂ v (krel_signLayerT v upd hs B _) fun s₂ ↦ by
    rcases s₂ with _ | top <;> rfl

theorem krel_challengeT (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).A A) :
    KRel tc a a' (realizeT v (challengeT M upd pol ⟨P, π, t⟩ A c))
      (realizeT v (challengeT M upd pol ⟨P, π, t'⟩ A c)) := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact krel_realizeT_readLift v _
  · exact krel_realizeT_readLift v _
  · refine krel_realizeT_bind v ?_ fun _ _ ↦ rfl
    rw [signAt, signAt]
    exact krel_realizeT_bind₂ v (krel_refl ⟨rfl, fun _ ↦ trivial⟩) fun _ ↦
      krel_signT v upd pol hs hm _ msg

/-- **The realized games at keys related slot by slot and call by call are related.** -/
theorem krel_gameT (A : SAdversary) :
    KRel tc a a' (realizeT v (gameT M upd pol ⟨P, π, t⟩ A))
      (realizeT v (gameT M upd pol ⟨P, π, t'⟩ A)) := by
  refine krel_realizeT_revealThen v _ fun r₀ ↦ ?_
  refine krel_realizeT_bind₂ v ?_ fun _ ↦
    krel_realizeT_bind₂ v (krel_realizeT_readLift v _) fun _ ↦ rfl
  exact krel_realizeT_substitute v (fun A c ↦ krel_challengeT v upd pol hs hm A c) _

/-- **The realized challenge prefixes at keys related slot by slot and call by call.** -/
theorem krel_prefixT (A : SAdversary) :
    KRel tc a a' (realizeT v (prefixT M upd pol ⟨P, π, t⟩ A))
      (realizeT v (prefixT M upd pol ⟨P, π, t'⟩ A)) := by
  refine krel_realizeT_revealThen v _ fun r₀ ↦ ?_
  exact krel_realizeT_bind₂ v
    (krel_realizeT_substitute v (fun A c ↦ krel_challengeT v upd pol hs hm A c) _) fun _ ↦ rfl

end gameRel

/-! ## The target-free flips averaged over the value -/

section kfree

/-- **The target-free `k` flips averaged over the value**: at most `2^-301` per unit of trace, at
grade `2^68`. -/
theorem uavg_kfSet_le {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (P : ℕ) (y : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, diagMass (kfSet π P (2 ^ 68) y a) σ ≤
      (2 ^ 301)⁻¹ * ENNReal.ofReal σ.trace.re :=
  inv_card_Z_mul_le_of_le (C := (2 ^ 68 + 1) * ((2 ^ 68 + 1) * 2 ^ 68 + 2 * 2 ^ 68) * 18)
    (by norm_num) (sum_diagMass_le_card (fun a ↦ kfSet π P (2 ^ 68) y a) _ hσ
      fun q _ t ht a₀ ha₀ ↦ by
        obtain ⟨-, hW, hT⟩ := ht a₀ ha₀
        exact card_flipK_le (W := q.2.2.1) (D := q.2.1) hπ (by omega) t
          (fun a ha ↦ (ht a ha).1) a₀ ha₀)

/-- **The target-free `k'` flips averaged over the value**: at most `2^-301` per unit of trace, at
grade `2^68`. -/
theorem uavg_kfSet'_le {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (P : ℕ) (y : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, diagMass (kfSet' π P (2 ^ 68) y a) σ ≤
      (2 ^ 301)⁻¹ * ENNReal.ofReal σ.trace.re :=
  inv_card_Z_mul_le_of_le (C := (2 ^ 68 + 1) + 2 ^ 68 * ((2 ^ 68 + 1) * 2 ^ 68 + 2 ^ 68 + 1) * 18 +
      2 ^ 68 * 2 ^ 68 * 18 + 2 ^ 68)
    (by norm_num) (sum_diagMass_le_card (fun a ↦ kfSet' π P (2 ^ 68) y a) _ hσ
      fun q _ t ht a₀ ha₀ ↦ by
        obtain ⟨-, hW, hT⟩ := ht a₀ ha₀
        exact card_flipK'_le (W := q.2.2.1) (D := q.2.1) hπ (by omega) t
          (fun a ha ↦ (ht a ha).1) a₀ ha₀)

variable (π : Equiv.Perm (X × Z)) (P T : ℕ) (y : X) (b : Z)

theorem diagMass_kfSet_eq_zero
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ)
    (h : ∀ s : HwReg X Z (Mem HPos), s.2.1.2.1 y = none → σ ((), s) ((), s) = 0) :
    diagMass (kfSet π P T y b) σ = 0 := by
  unfold diagMass
  refine Finset.sum_eq_zero fun q _ ↦ ?_
  by_cases hq : q ∈ kfSet π P T y b
  · obtain ⟨⟨⟩, s⟩ := q
    rw [Set.indicator_of_mem hq, h s hq.1.1, Complex.zero_re, ENNReal.ofReal_zero]
  · exact Set.indicator_of_notMem hq _

theorem diagMass_kfSet'_eq_zero
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ)
    (h : ∀ s : HwReg X Z (Mem HPos), s.2.1.2.2 y = none → σ ((), s) ((), s) = 0) :
    diagMass (kfSet' π P T y b) σ = 0 := by
  unfold diagMass
  refine Finset.sum_eq_zero fun q _ ↦ ?_
  by_cases hq : q ∈ kfSet' π P T y b
  · obtain ⟨⟨⟩, s⟩ := q
    rw [Set.indicator_of_mem hq, h s hq.1.1, Complex.zero_re, ENNReal.ofReal_zero]
  · exact Set.indicator_of_notMem hq _

theorem diagMass_kfSet_congr
    {σ σ' : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (h : ∀ s : HwReg X Z (Mem HPos), s.2.1.2.1 y = none → σ ((), s) ((), s) = σ' ((), s) ((), s)) :
    diagMass (kfSet π P T y b) σ = diagMass (kfSet π P T y b) σ' := by
  unfold diagMass
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases hq : q ∈ kfSet π P T y b
  · obtain ⟨⟨⟩, s⟩ := q
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, h s hq.1.1]
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]

theorem diagMass_kfSet'_congr
    {σ σ' : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (h : ∀ s : HwReg X Z (Mem HPos), s.2.1.2.2 y = none → σ ((), s) ((), s) = σ' ((), s) ((), s)) :
    diagMass (kfSet' π P T y b) σ = diagMass (kfSet' π P T y b) σ' := by
  unfold diagMass
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases hq : q ∈ kfSet' π P T y b
  · obtain ⟨⟨⟩, s⟩ := q
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, h s hq.1.1]
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]

end kfree

/-! ## The target-free flips along a run, cell by cell -/

section cells

variable (π : Equiv.Perm (X × Z)) (P T : ℕ)

/-- The target-free flip weight of a program port, cell by cell. -/
theorem kfW_split_prog (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) :
    kfW π P T c σ = ∑ y, (tcK y c).elim 0 (fun b ↦ diagMass (kfSet π P T y b) σ) +
      ∑ y, (tcK' y c).elim 0 (fun b ↦ diagMass (kfSet' π P T y b) σ) := by
  cases c with
  | programH z u =>
    show (0 : ℝ≥0∞) = ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞)
    simp
  | programK y a =>
    have h2 : ∑ y', (tcK' y' (.programK y a)).elim 0
        (fun b ↦ diagMass (kfSet' π P T y' b) σ) = 0 :=
      Finset.sum_eq_zero fun y' _ ↦ rfl
    rw [Finset.sum_eq_single y (fun y' _ hy' ↦ by rw [tcK_programK_ne (Ne.symm hy')]; rfl)
      (fun h ↦ absurd (Finset.mem_univ y) h), tcK_programK_self, h2, add_zero, Option.elim_some]
    rfl
  | programK' y a =>
    have h1 : ∑ y', (tcK y' (.programK' y a)).elim 0
        (fun b ↦ diagMass (kfSet π P T y' b) σ) = 0 :=
      Finset.sum_eq_zero fun y' _ ↦ rfl
    rw [h1, zero_add,
      Finset.sum_eq_single y (fun y' _ hy' ↦ by rw [tcK'_programK'_ne (Ne.symm hy')]; rfl)
      (fun h ↦ absurd (Finset.mem_univ y) h), tcK'_programK'_self, Option.elim_some]
    rfl

/-- **The target-free flip weight, cell by cell.** -/
theorem kfW_split (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ) :
    extWeight (hwCost (fun _ _ ↦ 0) (kfW π P T)) i σ =
      ∑ y, tcW (tcK y) m0R (fun b ↦ diagMass (kfSet π P T y b)) i σ +
        ∑ y, tcW (tcK' y) m0R (fun b ↦ diagMass (kfSet' π P T y b)) i σ := by
  rcases i with ((p | c) | c) | T'
  · show (0 : ℝ≥0∞) = ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞)
    simp
  · show (0 : ℝ≥0∞) = ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞)
    simp
  · exact kfW_split_prog π P T c σ
  · show (0 : ℝ≥0∞) = ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞)
    simp

omit π P T in
/-- **The traces at the `k` and `k'` ports, cell by cell**, are at most the traces at the program
ports. -/
theorem kTrace_split_le (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ) :
    ∑ y, tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re) i σ +
        ∑ y, tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re) i σ ≤
      extWeight (hwCost (fun _ _ ↦ 0) fun _ τ ↦ ENNReal.ofReal τ.trace.re) i σ := by
  rcases i with ((p | c) | c) | T
  · show ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞) ≤ 0
    simp
  · show ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞) ≤ 0
    simp
  · exact kSplit_prog_le c (fun τ : Matrix (Unit × HwReg X Z (Mem HPos))
      (Unit × HwReg X Z (Mem HPos)) ℂ ↦ ENNReal.ofReal τ.trace.re) σ
  · show ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞) ≤ 0
    simp

variable {Ω : QReg → Type}
  (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))

/-- **The target-free flips along a run, cell by cell.** -/
theorem totalWeight_kfW_eq :
    (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (kfW π P T))) x
        initR =
      ∑ y, (runtimeR m0R).totalWeight .instruments
          (tcW (tcK y) m0R (fun b ↦ diagMass (kfSet π P T y b))) x initR +
        ∑ y, (runtimeR m0R).totalWeight .instruments
          (tcW (tcK' y) m0R (fun b ↦ diagMass (kfSet' π P T y b))) x initR := by
  refine (congrArg (fun w ↦ (runtimeR m0R).totalWeight .instruments w x initR)
    (funext fun i ↦ funext fun σ ↦ kfW_split π P T i σ)).trans
    ((totalWeight_add_weight (runtimeR m0R) .instruments _ _ x initR).trans ?_)
  exact congrArg₂ (· + ·)
    (totalWeight_fintype_sum (runtimeR m0R) .instruments
      (fun y ↦ tcW (tcK y) m0R (fun b ↦ diagMass (kfSet π P T y b))) x initR)
    (totalWeight_fintype_sum (runtimeR m0R) .instruments
      (fun y ↦ tcW (tcK' y) m0R (fun b ↦ diagMass (kfSet' π P T y b))) x initR)

omit π P T in
/-- **The traces at the `k`, `k'` ports along a run with at most `progCap` program calls.** -/
theorem totalWeight_kTrace_le
    (hK : IFreeM.IsChargeBound x (progChargeR HPos Selections) progCap) :
    ∑ y, (runtimeR m0R).totalWeight .instruments
          (tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR +
        ∑ y, (runtimeR m0R).totalWeight .instruments
          (tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR ≤ progCap := by
  refine (Eq.trans (congrArg₂ (· + ·)
    (totalWeight_fintype_sum (runtimeR m0R) .instruments
      (fun y ↦ tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR).symm
    (totalWeight_fintype_sum (runtimeR m0R) .instruments
      (fun y ↦ tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR).symm)
    (totalWeight_add_weight (runtimeR m0R) .instruments _ _ x initR).symm).trans_le ?_
  exact (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (fun i σ _ ↦ kTrace_split_le i σ) x initR_posSemidef).trans (totalWeight_progs_le x hK)

omit P in
variable {π} in
/-- **The resampled `k` flips of a cell along a run**: averaged over the value, at most `2^-301`
times the traces at the `k` ports of the cell. -/
theorem uavg_totalWeight_kfSet_le (hπ : PermGood π 18) (P : ℕ) (y : X) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R (fun _ ↦ diagMass (kfSet π P (2 ^ 68) y a))) x initR ≤
      (2 ^ 301)⁻¹ * (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR := by
  refine ((congrArg ((Fintype.card Z : ℝ≥0∞)⁻¹ * ·) (totalWeight_fintype_sum (runtimeR m0R)
    .instruments (fun a ↦ tcW (tcK y) m0R (fun _ ↦ diagMass (kfSet π P (2 ^ 68) y a))) x
      initR).symm).trans
    (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ _ x initR).symm).trans_le
    ((totalWeight_le_totalWeight (runtimeR m0R) .instruments (fun i σ hσ ↦ ?_) x
      initR_posSemidef).trans_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments
        (2 ^ 301)⁻¹ (tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR))
  rcases i with ((p | c) | c) | T
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ (2 ^ 301)⁻¹ * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ (2 ^ 301)⁻¹ * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · exact elim_avg_le (tcK y c) (fun a ↦ diagMass (kfSet π P (2 ^ 68) y a) σ) _ _
      (uavg_kfSet_le hπ P y hσ)
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ (2 ^ 301)⁻¹ * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]

omit P in
variable {π} in
/-- **The resampled `k'` flips of a cell along a run.** -/
theorem uavg_totalWeight_kfSet'_le (hπ : PermGood π 18) (P : ℕ) (y : X) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R (fun _ ↦ diagMass (kfSet' π P (2 ^ 68) y a))) x initR ≤
      (2 ^ 301)⁻¹ * (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR := by
  refine ((congrArg ((Fintype.card Z : ℝ≥0∞)⁻¹ * ·) (totalWeight_fintype_sum (runtimeR m0R)
    .instruments (fun a ↦ tcW (tcK' y) m0R (fun _ ↦ diagMass (kfSet' π P (2 ^ 68) y a))) x
      initR).symm).trans
    (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ _ x initR).symm).trans_le
    ((totalWeight_le_totalWeight (runtimeR m0R) .instruments (fun i σ hσ ↦ ?_) x
      initR_posSemidef).trans_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments
        (2 ^ 301)⁻¹ (tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR))
  rcases i with ((p | c) | c) | T
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ (2 ^ 301)⁻¹ * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ (2 ^ 301)⁻¹ * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · exact elim_avg_le (tcK' y c) (fun a ↦ diagMass (kfSet' π P (2 ^ 68) y a) σ) _ _
      (uavg_kfSet'_le hπ P y hσ)
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ (2 ^ 301)⁻¹ * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]

end cells

/-! ## The target-free flips summed over the keys -/

section keySum

variable (π : Equiv.Perm (X × Z)) (P : ℕ)

/-- **Resampling the `k` key at one cell**: on programs agreeing until the first `k` port at `y`,
the flips at those ports read with their value are the flips of value `a` on the other. -/
theorem totalWeight_kfSet_update {Ω : QReg → Type} (y : X) (a a' : Z)
    (x x' : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    (h : KRel (tcK y) a a' x x') :
    (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R fun b ↦ diagMass (kfSet π P (2 ^ 68) y b)) x initR =
      (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R fun _ ↦ diagMass (kfSet π P (2 ^ 68) y a)) x' initR :=
  totalWeight_tcW_eq_of_krel m0R (Fr := fun W ↦ W.2.1 y = none) (a := a) (a' := a')
    (fun _ _ ↦ progUpdate_k_none) (fun _ _ hb W ↦ tcK_some hb W)
    (g := fun b ↦ diagMass (kfSet π P (2 ^ 68) y b))
    (g' := fun _ ↦ diagMass (kfSet π P (2 ^ 68) y a))
    (fun b σ h ↦ diagMass_kfSet_eq_zero π P _ y b σ h)
    (fun _ σ h ↦ diagMass_kfSet_eq_zero π P _ y a σ h)
    (fun _ _ h ↦ diagMass_kfSet_congr π P _ y a h)
    _ _ h initR initR fun _ _ _ _ ↦ rfl

/-- **Resampling the `k'` key at one cell.** -/
theorem totalWeight_kfSet'_update {Ω : QReg → Type} (y : X) (a a' : Z)
    (x x' : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    (h : KRel (tcK' y) a a' x x') :
    (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R fun b ↦ diagMass (kfSet' π P (2 ^ 68) y b)) x initR =
      (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R fun _ ↦ diagMass (kfSet' π P (2 ^ 68) y a)) x' initR :=
  totalWeight_tcW_eq_of_krel m0R (Fr := fun W ↦ W.2.2 y = none) (a := a) (a' := a')
    (fun _ _ ↦ progUpdate_k'_none) (fun _ _ hb W ↦ tcK'_some hb W)
    (g := fun b ↦ diagMass (kfSet' π P (2 ^ 68) y b))
    (g' := fun _ ↦ diagMass (kfSet' π P (2 ^ 68) y a))
    (fun b σ h ↦ diagMass_kfSet'_eq_zero π P _ y b σ h)
    (fun _ σ h ↦ diagMass_kfSet'_eq_zero π P _ y a σ h)
    (fun _ _ h ↦ diagMass_kfSet'_congr π P _ y a h)
    _ _ h initR initR fun _ _ _ _ ↦ rfl

variable {π} in
/-- **The target-free flips summed over the keys** along a family of runs related at every key
cell (`KRel`) with at most `progCap` program calls: at most `2^-301 progCap` per key pair, for
`PermGood π 18`. -/
theorem sum_kfTot_le_of_krel {Ω : QReg → Type}
    (F : (X → Z) → (X → Z) →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    (hk : ∀ y k k' a, KRel (tcK y) a (k y) (F (Function.update k y a) k') (F k k'))
    (hk' : ∀ y k k' a, KRel (tcK' y) a (k' y) (F k (Function.update k' y a)) (F k k'))
    (hp : ∀ k k', IFreeM.IsChargeBound (F k k') (progChargeR HPos Selections) progCap)
    (hπ : PermGood π 18) :
    ∑ k, ∑ k', (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) (kfW π P (2 ^ 68)))) (F k k') initR ≤
      (2 ^ 301)⁻¹ * ∑ _k : X → Z, ∑ _k' : X → Z, (progCap : ℝ≥0∞) :=
  sum_two_cells
    (fun k k' ↦ (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfW π P (2 ^ 68)))) (F k k') initR)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK y) m0R fun b ↦ diagMass (kfSet π P (2 ^ 68) y b)) (F k k') initR)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK' y) m0R fun b ↦ diagMass (kfSet' π P (2 ^ 68) y b)) (F k k') initR)
    (fun _ _ ↦ (totalWeight_kfW_eq π P _ _).le)
    (fun y k k' a ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK y) m0R fun _ ↦ diagMass (kfSet π P (2 ^ 68) y a)) (F k k') initR)
    (fun y k k' a ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK' y) m0R fun _ ↦ diagMass (kfSet' π P (2 ^ 68) y a)) (F k k') initR)
    (fun y k k' a ↦ totalWeight_kfSet_update π P y a (k y) _ _ (hk y k k' a))
    (fun y k k' a ↦ totalWeight_kfSet'_update π P y a (k' y) _ _ (hk' y k k' a))
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK y) m0R fun _ τ ↦ ENNReal.ofReal τ.trace.re) (F k k') initR)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK' y) m0R fun _ τ ↦ ENNReal.ofReal τ.trace.re) (F k k') initR)
    (2 ^ 301)⁻¹ progCap
    (fun y _ _ ↦ uavg_totalWeight_kfSet_le _ hπ P y)
    (fun y _ _ ↦ uavg_totalWeight_kfSet'_le _ hπ P y)
    (fun k k' ↦ totalWeight_kTrace_le _ (hp k k'))

end keySum

/-! ## The canonical game and its prefix at keys differing in one cell -/

section canon

variable (pol : DigestPolicy) (A : SAdversary) (P₀ : PublicParameter) (π : Equiv.Perm (X × Z))
  (h₀ : Z → X) (v : (s : HPos) → XD s) (y : X) (k k' : X → Z) (a : Z)

theorem krel_gameT_k (upd : TrialUpd Selections) :
    KRel (tcK y) a (k y)
      (realizeT v (gameT Selections upd pol ⟨P₀, π, (h₀, Function.update k y a, k')⟩ A))
      (realizeT v (gameT Selections upd pol ⟨P₀, π, (h₀, k, k')⟩ A)) := by
  have ht : ∀ z, z ≠ y → Function.update k y a z = k z := fun z hz ↦ Function.update_of_ne hz _ _
  have hr := krel_gameT (M := Selections) v upd pol
    (fun s ↦ prel_slotPorts_k (P := P₀) (π := π) (h := h₀) (k' := k') ht s v)
    (fun T msg i ↦ prel_hmsgPorts_k (P := P₀) (π := π) (h := h₀) (k' := k') ht pol T msg i v) A
  rw [Function.update_self] at hr
  exact hr

theorem krel_gameT_k' (upd : TrialUpd Selections) :
    KRel (tcK' y) a (k' y)
      (realizeT v (gameT Selections upd pol ⟨P₀, π, (h₀, k, Function.update k' y a)⟩ A))
      (realizeT v (gameT Selections upd pol ⟨P₀, π, (h₀, k, k')⟩ A)) := by
  have ht : ∀ z, z ≠ y → Function.update k' y a z = k' z := fun z hz ↦
    Function.update_of_ne hz _ _
  have hr := krel_gameT (M := Selections) v upd pol
    (fun s ↦ prel_slotPorts_k' (P := P₀) (π := π) (h := h₀) (k := k) ht s v)
    (fun T msg i ↦ prel_hmsgPorts_k' (P := P₀) (π := π) (h := h₀) (k := k) ht pol T msg i v) A
  rw [Function.update_self] at hr
  exact hr

theorem krel_prefixR_k :
    KRel (tcK y) a (k y) (prefixR pol A ⟨P₀, π, (h₀, Function.update k y a, k')⟩ v)
      (prefixR pol A ⟨P₀, π, (h₀, k, k')⟩ v) := by
  have ht : ∀ z, z ≠ y → Function.update k y a z = k z := fun z hz ↦ Function.update_of_ne hz _ _
  have hr := krel_prefixT (M := Selections) v cwUpd pol
    (fun s ↦ prel_slotPorts_k (P := P₀) (π := π) (h := h₀) (k' := k') ht s v)
    (fun T msg i ↦ prel_hmsgPorts_k (P := P₀) (π := π) (h := h₀) (k' := k') ht pol T msg i v) A
  rw [Function.update_self] at hr
  exact hr

theorem krel_prefixR_k' :
    KRel (tcK' y) a (k' y) (prefixR pol A ⟨P₀, π, (h₀, k, Function.update k' y a)⟩ v)
      (prefixR pol A ⟨P₀, π, (h₀, k, k')⟩ v) := by
  have ht : ∀ z, z ≠ y → Function.update k' y a z = k' z := fun z hz ↦
    Function.update_of_ne hz _ _
  have hr := krel_prefixT (M := Selections) v cwUpd pol
    (fun s ↦ prel_slotPorts_k' (P := P₀) (π := π) (h := h₀) (k := k) ht s v)
    (fun T msg i ↦ prel_hmsgPorts_k' (P := P₀) (π := π) (h := h₀) (k := k) ht pol T msg i v) A
  rw [Function.update_self] at hr
  exact hr

end canon

/-! ## The target-free flips of the game and of its prefix, summed over the keys -/

/-- **The target-free fresh flips along the realized game** with trial update `upd`, at hardwired
grade `N` and grade `2^68`. -/
noncomputable def kfGame (upd : TrialUpd Selections) (pol : DigestPolicy) (A : SAdversary) (N : ℕ)
    (p : Pub) (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (kfW p.perm N (2 ^ 68))))
    (realizeT v (gameT Selections upd pol p A)) initR

/-- RecJ's `kfPre` is at most the flips of the canonical game. -/
theorem kfPre_le_kfGame (pol : DigestPolicy) (A : SAdversary) (p : Pub) (v : (s : HPos) → XD s) :
    kfPre pol A p v ≤ kfGame cwUpd pol A progCap p v := by
  unfold kfPre kfGame
  rw [show realizeT v (gameT Selections cwUpd pol p A) = gameR pol A p v from rfl, gameR_eq]
  exact totalWeight_le_bind₂ (runtimeR m0R) .instruments _ (prefixR pol A p v) _ initR

section sums

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The target-free flips of the game summed over the keys**: at most `2^-301 progCap` per key
pair, for `PermGood π 18` and every trial update, digest policy and hardwired grade `N`. -/
theorem sum_kfGame_le (upd : TrialUpd Selections) (pol : DigestPolicy) (N : ℕ)
    (P₀ : PublicParameter) {π : Equiv.Perm (X × Z)} (h₀ : Z → X) (v : (s : HPos) → XD s)
    (hπ : PermGood π 18) :
    ∑ k, ∑ k', kfGame upd pol A N ⟨P₀, π, (h₀, k, k')⟩ v ≤
      (2 ^ 301)⁻¹ * ∑ _k : X → Z, ∑ _k' : X → Z, (progCap : ℝ≥0∞) :=
  sum_kfTot_le_of_krel N (fun k k' ↦ realizeT v (gameT Selections upd pol ⟨P₀, π, (h₀, k, k')⟩ A))
    (fun y k k' a ↦ krel_gameT_k pol A P₀ π h₀ v y k k' a upd)
    (fun y k k' a ↦ krel_gameT_k' pol A P₀ π h₀ v y k k' a upd)
    (fun _ _ ↦ hN_prog upd pol A hperm hsign _ v) hπ

/-- **RecJ's `kfPre` summed over the keys**: at most `2^-301 progCap` per key pair, for
`PermGood π 18` and every digest policy. -/
theorem sum_kfPre_le (pol : DigestPolicy) (P₀ : PublicParameter) {π : Equiv.Perm (X × Z)}
    (h₀ : Z → X) (v : (s : HPos) → XD s) (hπ : PermGood π 18) :
    ∑ k, ∑ k', kfPre pol A ⟨P₀, π, (h₀, k, k')⟩ v ≤
      (2 ^ 301)⁻¹ * ∑ _k : X → Z, ∑ _k' : X → Z, (progCap : ℝ≥0∞) :=
  sum_kfTot_le_of_krel progCap (fun k k' ↦ prefixR pol A ⟨P₀, π, (h₀, k, k')⟩ v)
    (fun y k k' a ↦ krel_prefixR_k pol A P₀ π h₀ v y k k' a)
    (fun y k k' a ↦ krel_prefixR_k' pol A P₀ π h₀ v y k k' a)
    (fun _ _ ↦ progCalls_prefixR hperm hsign pol _ v) hπ

end sums

/-! ## The fresh flips of `Bad` are target-free -/

section kW

/-- **A fresh `k`, `k'` flip into `Bad` is a target-free flip** (leanXMSS's `flipK_facts` for
Struct, Enc and coverage, all `HwTargetBad` with antitone targets), at states with
`N + dbGrade D ≤ T`. -/
theorem kFlip_le_kfW (d : EvData) (N T : ℕ) [DecidablePred (· ∈ Bad (S := HPos) d N)]
    (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hg : ∀ q, σ q q ≠ 0 → N + dbGrade q.2.1 ≤ T) :
    kFlip (Bad d N) c σ ≤ kfW d.perm N T c σ := by
  cases c with
  | programH z u =>
    exact (diagMass_mono_supp (S' := ∅) fun q _ h ↦ absurd h (Set.notMem_empty q.2)).trans_eq
      (diagMass_empty σ)
  | programK y a =>
    refine diagMass_mono_supp fun q hq hm ↦ ?_
    obtain ⟨hs, hx, hp⟩ : q.2 ∉ Bad (S := HPos) d N ∧ q.2.2.1.2.1 y = none ∧
        progMap (.programK y a) q.2 ∈ Bad (S := HPos) d N := hm
    rcases hp with hp | hp
    · obtain ⟨hN, hF⟩ := flipK_facts d.tgtAnti_sphTgtHw hx (fun h ↦ hs (.inl h)) hp
      exact ⟨hF, hN, hg q hq⟩
    · obtain ⟨hN, hF⟩ := flipK_facts (tgtAnti_covTgt (EvData.exMono_covEx (d := d))) hx
        (fun h ↦ hs (.inr h)) hp
      exact ⟨hF, hN, hg q hq⟩
  | programK' y a =>
    refine diagMass_mono_supp fun q hq hm ↦ ?_
    obtain ⟨hs, hx, hp⟩ : q.2 ∉ Bad (S := HPos) d N ∧ q.2.2.1.2.2 y = none ∧
        progMap (.programK' y a) q.2 ∈ Bad (S := HPos) d N := hm
    rcases hp with hp | hp
    · obtain ⟨hN, hF⟩ := flipK'_facts d.tgtAnti_sphTgtHw hx (fun h ↦ hs (.inl h)) hp
      exact ⟨hF, hN, hg q hq⟩
    · obtain ⟨hN, hF⟩ := flipK'_facts (tgtAnti_covTgt (EvData.exMono_covEx (d := d))) hx
        (fun h ↦ hs (.inr h)) hp
      exact ⟨hF, hN, hg q hq⟩

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **ProgSafe's `kW` is target-free**: along the realized game every call has database grade at
most `6q + clsCap`, so with `N + 6q + clsCap ≤ 2^68` the fresh flips of `Bad (evData pub v) N` are
at most the target-free flips `kfGame` at hardwired grade `N`. -/
theorem kW_le_kfGame {N : ℕ} (hN : N + (6 * q + clsCap) ≤ 2 ^ 68) (upd : TrialUpd Selections)
    (pol : DigestPolicy) (pub : Pub) (v : (s : HPos) → XD s)
    [DecidablePred (· ∈ Bad (S := HPos) (evData pub v) N)] :
    kW (Bad (evData pub v) N) m0R (realizeT v (gameT Selections upd pol pub A)) initR ≤
      kfGame upd pol A N pub v := by
  set κ : (recHwSpec X Z HPos Selections).Port → ℕ := fun i ↦
    (if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1) +
      (if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 1 else 0) with hκ
  have hκ1 : ∀ i, κ i = 1 := fun i ↦ by
    rw [hκ]
    by_cases h : extCls X Z (Mem HPos) (recSpec HPos Selections) i = true <;> simp [h]
  have hx : IFreeM.IsChargeBound (realizeT v (gameT Selections upd pol pub A)) (portCharge κ)
      (6 * q + clsCap) :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl)
      ((hN_sponge upd pol A hperm hsign pub v).add (hN_cls upd pol A hperm hsign pub v))
  have hfq := forallQueries_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1) κ (fun _ ↦ 0)
    (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_step m0R i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hκ1]))) .instruments _ hx
    (isChargeBound_portCharge_zero _) querySupportedOn_initR
  unfold kW kfGame
  refine totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun _ τ ↦ ∀ a, τ a a ≠ 0 → dbGrade a.2.1 ≤ 6 * q + clsCap)
    (fun i E σ hP a ha ↦ ?_) (fun i τ _ hok ↦ ?_) _ initR_posSemidef hfq
  · obtain ⟨e, he⟩ : ∃ e, σ (a, e) (a, e) ≠ 0 := by
      by_contra h
      exact ha (traceRight_diag_eq_zero fun e ↦ not_not.1 fun he ↦ h ⟨e, he⟩)
    have h := (hP.2 (a, e) (a, e) he).1
    rw [Set.mem_Iic, Nat.zero_add] at h
    exact h
  · rcases i with ((p | c) | c) | T
    · show (0 : ℝ≥0∞) ≤ 0
      exact le_rfl
    · show (0 : ℝ≥0∞) ≤ 0
      exact le_rfl
    · dsimp only [extWeight, sumWeight, hwCost]
      exact kFlip_le_kfW (evData pub v) N _ c fun a ha ↦ by
        have := hok a ha
        omega
    · show (0 : ℝ≥0∞) ≤ 0
      exact le_rfl

end kW

/-! ## Averages over finite families -/

section avg

theorem uavg_le_of_sum_le {Θ : Type*} [Fintype Θ] {f : Θ → ℝ≥0∞} {κ : ℝ≥0∞}
    (h : ∑ θ, f θ ≤ κ * Fintype.card Θ) : uavg f ≤ κ := by
  unfold uavg
  by_cases hΘ : (Fintype.card Θ : ℝ≥0∞) = 0
  · have : IsEmpty Θ := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hΘ)
    simp [Finset.univ_eq_empty]
  · calc (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ θ, f θ
        ≤ (Fintype.card Θ : ℝ≥0∞)⁻¹ * (κ * Fintype.card Θ) := mul_le_mul_of_nonneg_left h zero_le
      _ = κ := by
          rw [mul_comm κ, ← mul_assoc, ENNReal.inv_mul_cancel hΘ (ENNReal.natCast_ne_top _),
            one_mul]

theorem sum_prod_le_card {Q V : Type*} [Fintype Q] [Fintype V] (g : Q × V → ℝ≥0∞) {κ : ℝ≥0∞}
    (h : ∀ q, ∑ x, g (q, x) ≤ κ * Fintype.card V) : ∑ θ, g θ ≤ κ * Fintype.card (Q × V) := by
  rw [Fintype.sum_prod_type]
  calc ∑ q, ∑ x, g (q, x) ≤ ∑ _q : Q, κ * Fintype.card V := Finset.sum_le_sum fun q _ ↦ h q
    _ = κ * Fintype.card (Q × V) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
        ring

/-- **A per-datum sum of a key-averaged term and a record term**: the first summed over everything
at most `c` per point, the second at most `ε` per point on summing the last coordinate. -/
theorem sum_add_revW_le {K2 W K : Type*} [Fintype K2] [Fintype W] [Fintype K]
    (a : K2 → W → ℝ≥0∞) (r : K2 → W → K → ℝ≥0∞) {c : ℝ≥0∞}
    (ha : ∑ x : K2 × (W × K), a x.1 x.2.1 ≤ c * Fintype.card (K2 × (W × K))) {ε : ℝ≥0∞}
    (hr : ∀ kk w, ∑ κ, r kk w κ ≤ Fintype.card K * ε) (N : ℝ≥0∞) :
    ∑ x : K2 × (W × K), (a x.1 x.2.1 + N * r x.1 x.2.1 x.2.2) ≤
      (c + N * ε) * Fintype.card (K2 × (W × K)) := by
  have hr' : ∑ x : K2 × (W × K), r x.1 x.2.1 x.2.2 ≤ ε * Fintype.card (K2 × (W × K)) :=
    sum_prod_le_card (fun x : K2 × (W × K) ↦ r x.1 x.2.1 x.2.2) fun kk ↦
      sum_prod_le_card (fun x : W × K ↦ r kk x.1 x.2) fun w ↦ (hr kk w).trans_eq (mul_comm _ _)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, add_mul, mul_assoc]
  exact add_le_add ha (mul_le_mul_of_nonneg_left hr' zero_le)

/-- **A guarded average through a map injective on the guard**: if `f ≤ g ∘ e` on the guard and
every fiber sum of `g` is at most `κ` per point, the guarded average of `f` is at most `κ`. -/
theorem uavg_ite_le_of_injOn {Θ Q V : Type*} [Fintype Θ] [Fintype Q] [Fintype V]
    (e : Θ → Q × V) (good : Θ → Prop) [DecidablePred good] (hinj : Set.InjOn e {t | good t})
    (hcard : Fintype.card Q * Fintype.card V ≤ Fintype.card Θ) (f : Θ → ℝ≥0∞)
    (g : Q → V → ℝ≥0∞) (hfg : ∀ t, good t → f t ≤ g (e t).1 (e t).2) (κ : ℝ≥0∞)
    (hg : ∀ q, ∑ x, g q x ≤ κ * Fintype.card V) :
    uavg (fun t ↦ if good t then f t else 0) ≤ κ := by
  classical
  refine uavg_le_of_sum_le ?_
  calc ∑ t, (if good t then f t else 0) = ∑ t ∈ Finset.univ.filter good, f t :=
        (Finset.sum_filter _ _).symm
    _ ≤ ∑ t ∈ Finset.univ.filter good, g (e t).1 (e t).2 :=
        Finset.sum_le_sum fun t ht ↦ hfg t (Finset.mem_filter.mp ht).2
    _ = ∑ y ∈ (Finset.univ.filter good).image e, g y.1 y.2 := by
        refine (Finset.sum_image (f := fun y : Q × V ↦ g y.1 y.2) ?_).symm
        intro a ha b hb h
        exact hinj (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
          (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2 h
    _ ≤ ∑ y : Q × V, g y.1 y.2 := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ q, ∑ x, g q x := Fintype.sum_prod_type _
    _ ≤ ∑ _q : Q, κ * Fintype.card V := Finset.sum_le_sum fun q _ ↦ hg q
    _ = κ * ((Fintype.card Q : ℝ≥0∞) * Fintype.card V) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ κ * Fintype.card Θ := by
        gcongr
        exact_mod_cast hcard

end avg

/-! ## Averages over template data with the keys as uniform coordinates -/

section coords

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
  {Q V : Type} [Fintype Q] [Fintype V] (par : Q → PublicParameter) (perm : Q → Equiv.Perm (X × Z))
  (hk : Q → Z → X) (val : Q → V → (s : HPos) → XD s)
  (good : Q × (((X → Z) × (X → Z)) × V) → Prop) [DecidablePred good]
  (hgood : ∀ θ, good θ → PermGood (perm θ.1) 18)
include hperm hsign hgood

/-- **RecJ's `κ`**: over template data whose keys are uniform coordinates (public data `Q`, keys,
hidden data `V`), on a guard implying `PermGood π 18`, the averaged `kfPre` is at most
`2^-301 progCap`, for every digest policy. -/
theorem uavg_kfPre_le (pol : DigestPolicy) :
    uavg (fun θ : Q × (((X → Z) × (X → Z)) × V) ↦ if good θ then
      kfPre pol A ⟨par θ.1, perm θ.1, (hk θ.1, θ.2.1.1, θ.2.1.2)⟩ (val θ.1 θ.2.2) else 0) ≤
      (2 ^ 301)⁻¹ * progCap := by
  refine uavg_le_of_sum_le (sum_prod_le_card _ fun p ↦ ?_)
  by_cases hp : PermGood (perm p) 18
  · calc ∑ x : ((X → Z) × (X → Z)) × V, (if good (p, x) then
          kfPre pol A ⟨par p, perm p, (hk p, x.1.1, x.1.2)⟩ (val p x.2) else 0)
        ≤ ∑ x : ((X → Z) × (X → Z)) × V,
            kfPre pol A ⟨par p, perm p, (hk p, x.1.1, x.1.2)⟩ (val p x.2) :=
          Finset.sum_le_sum fun x _ ↦ by
            by_cases hg : good (p, x)
            · rw [ite_eq_left hg]
            · rw [ite_eq_right hg]
              exact zero_le
      _ ≤ (2 ^ 301)⁻¹ * progCap * Fintype.card (((X → Z) × (X → Z)) × V) :=
          sum_pair_le (fun k k' w ↦ kfPre pol A ⟨par p, perm p, (hk p, k, k')⟩ (val p w)) _ _
            fun w ↦ sum_kfPre_le hperm hsign pol (par p) (hk p) (val p w) hp
  · rw [Finset.sum_eq_zero fun x _ ↦ ite_eq_right fun hg ↦ hp (hgood _ hg)]
    exact zero_le

/-- **ProgSafe's `hk`**: over template data whose keys are uniform coordinates, on a guard
implying `PermGood π 18`, with `N + 6q + clsCap ≤ 2^68`, the averaged fresh flips `kW` of the
realized game are at most `2^-301 progCap`, for every trial update and digest policy. -/
theorem uavg_kW_le {N : ℕ} (hN : N + (6 * q + clsCap) ≤ 2 ^ 68) (upd : TrialUpd Selections)
    (pol : DigestPolicy)
    [∀ θ : Q × (((X → Z) × (X → Z)) × V), DecidablePred (· ∈ Bad (S := HPos)
      (evData ⟨par θ.1, perm θ.1, (hk θ.1, θ.2.1.1, θ.2.1.2)⟩ (val θ.1 θ.2.2)) N)] :
    uavg (fun θ : Q × (((X → Z) × (X → Z)) × V) ↦ if good θ then
      kW (Bad (evData ⟨par θ.1, perm θ.1, (hk θ.1, θ.2.1.1, θ.2.1.2)⟩ (val θ.1 θ.2.2)) N) m0R
        (realizeT (val θ.1 θ.2.2)
          (gameT Selections upd pol ⟨par θ.1, perm θ.1, (hk θ.1, θ.2.1.1, θ.2.1.2)⟩ A)) initR
      else 0) ≤ (2 ^ 301)⁻¹ * progCap := by
  refine uavg_le_of_sum_le (sum_prod_le_card _ fun p ↦ ?_)
  by_cases hp : PermGood (perm p) 18
  · refine (Finset.sum_le_sum fun x _ ↦ ?_).trans (sum_pair_le
      (fun k k' w ↦ kfGame upd pol A N ⟨par p, perm p, (hk p, k, k')⟩ (val p w)) _ _
        fun w ↦ sum_kfGame_le hperm hsign upd pol N (par p) (hk p) (val p w) hp)
    by_cases hg : good (p, x)
    · rw [ite_eq_left hg]
      exact kW_le_kfGame hperm hsign hN upd pol _ _
    · rw [ite_eq_right hg]
      exact zero_le
  · rw [Finset.sum_eq_zero fun x _ ↦ ite_eq_right fun hg ↦ hp (hgood _ hg)]
    exact zero_le

end coords

/-! ## Averages over the padded tables, through the mismatch lemma -/

section table

/-- The target-free flip sets of the ports, as Mismatch's diagonal masses. -/
def kfC (π : Equiv.Perm (X × Z)) (P T : ℕ) : ∀ i : (recHwSpec X Z HPos Selections).Port,
    Set ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Finset HPos × Selections)))
  | .inl (.inr (.programK y a)) => kfSet π P T y a
  | .inl (.inr (.programK' y a)) => kfSet' π P T y a
  | _ => ∅

theorem kfW_eq_diagMass_kfC (π : Equiv.Perm (X × Z)) (P T : ℕ) :
    extWeight (hwCost (fun _ _ ↦ 0) (kfW π P T)) =
      fun i ↦ diagMass (kfC π P T i) := by
  funext i σ
  rcases i with ((p | c) | c) | T'
  · exact (diagMass_empty σ).symm
  · exact (diagMass_empty σ).symm
  · cases c with
    | programH z u => exact (diagMass_empty σ).symm
    | programK y a => rfl
    | programK' y a => rfl
  · exact (diagMass_empty σ).symm

/-- The program ports. -/
def IsProgPort (i : (recHwSpec X Z HPos Selections).Port) : Prop :=
  Quantum.Xmss.extProgCharge X Z (Mem HPos) (recSpec HPos Selections) i = 1

instance isProgPortDec : DecidablePred IsProgPort :=
  fun i ↦ inferInstanceAs
    (Decidable (Quantum.Xmss.extProgCharge X Z (Mem HPos) (recSpec HPos Selections) i = 1))

theorem progCharge_eq_ite :
    (fun i ↦ if IsProgPort i then 1 else 0) =
      Quantum.Xmss.extProgCharge X Z (Mem HPos) (recSpec HPos Selections) := by
  funext i
  rcases i with ((p | c) | c) | T <;> rfl

theorem kfC_eq_empty (π : Equiv.Perm (X × Z)) (P T : ℕ) (i : (recHwSpec X Z HPos Selections).Port)
    (hi : ¬IsProgPort i) : kfC π P T i = ∅ := by
  rcases i with ((p | c) | c) | T'
  · rfl
  · rfl
  · exact absurd (show IsProgPort (.inl (.inr c)) from rfl) hi
  · rfl

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The mismatch step**: the flips of the canonical game at hidden values `v` agreeing with `w`
off `B` are at most those at `w` plus `progCap` times the record mass of `B` at `w`. -/
theorem kfGame_le_mismatch (pol : DigestPolicy) (N : ℕ) (pub : Pub) {v w : (s : HPos) → XD s}
    (B : Finset HPos) (hv : Agree (Finset.univ \ B) v w) :
    kfGame cwUpd pol A N pub v ≤ kfGame cwUpd pol A N pub w +
      progCap * revW m0R .instruments B (gameR pol A pub w) initR := by
  unfold kfGame
  have hN : IFreeM.IsChargeBound (realizeT v (gameT Selections cwUpd pol pub A))
      (portCharge fun i ↦ if IsProgPort i then 1 else 0) progCap := by
    rw [progCharge_eq_ite]
    exact progCalls_gameR hperm hsign pol pub v
  have hs : QuerySupportedOn
      (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × Selections)) ↦ p.2.2.2.1)
      {m0R.1} initR := by
    unfold initR
    exact Quantum.Xmss.Hybrid.querySupportedOn_initR m0R _
  have hm := totalWeight_le_mismatch m0R .instruments (gameT Selections cwUpd pol pub A)
    (disc_gameT Selections cwUpd pol pub A ∅) (keepsLab_gameT Selections cwUpd pol pub A) initR
    initR_posSemidef hs B (Finset.disjoint_empty_left B) IsProgPort _
    (kfC_eq_empty pub.perm N (2 ^ 68)) hv hN
  have e : ∀ u : (s : HPos) → XD s, (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfW pub.perm N (2 ^ 68))))
      (realizeT u (gameT Selections cwUpd pol pub A)) initR =
      (runtimeR m0R).totalWeight .instruments (fun i ↦ diagMass (kfC pub.perm N (2 ^ 68) i))
        (realizeT u (gameT Selections cwUpd pol pub A)) initR := fun u ↦
    congrArg (fun wt ↦ (runtimeR m0R).totalWeight .instruments wt
      (realizeT u (gameT Selections cwUpd pol pub A)) initR)
      (kfW_eq_diagMass_kfC pub.perm N (2 ^ 68))
  rw [e v, e w]
  exact hm

variable {Θ Q W K : Type} [Fintype Θ] [Fintype Q] [Fintype W] [Fintype K]

/-- **The target-free flips of the canonical game averaged over the tables** (`msgPol`). The
tables `Θ` are mapped by `e` into public data `Q`, the keys, hidden data `W` and a never-revealed
part `K`, injectively on the guard `good`, with `|Q| |keys × W × K| ≤ |Θ|`. On the guard the game at
the table (`pubT`, `valT`) is the game at the public datum with the keys, realized at hidden
values agreeing with `val w` off a set `B q kk w κ` (`hgame`), the permutation is the table's
and `PermGood`. Every path records at most `R` coordinates of `J ⊇ B`, each in `B q kk w κ` for at
most an `εB` fraction of the `κ`. Then the averaged flips are at most
`2^-301 progCap + progCap R εB`. -/
theorem uavg_kfGame_table_le (e : Θ → Q × (((X → Z) × (X → Z)) × (W × K))) (good : Θ → Prop)
    [DecidablePred good] (hinj : Set.InjOn e {t | good t})
    (hcard : Fintype.card Q * Fintype.card (((X → Z) × (X → Z)) × (W × K)) ≤ Fintype.card Θ)
    (par : Q → PublicParameter) (perm : Q → Equiv.Perm (X × Z)) (hk : Q → Z → X)
    (val : W → (s : HPos) → XD s) (B : Q → ((X → Z) × (X → Z)) → W → K → Finset HPos)
    (pubT : Θ → Pub) (valT : Θ → (s : HPos) → XD s)
    (hgame : ∀ t, good t → ∃ v : (s : HPos) → XD s,
      Agree (Finset.univ \ B (e t).1 (e t).2.1 (e t).2.2.1 (e t).2.2.2) v (val (e t).2.2.1) ∧
      gameR msgPol A (pubT t) (valT t) =
        gameR msgPol A ⟨par (e t).1, perm (e t).1, (hk (e t).1, (e t).2.1.1, (e t).2.1.2)⟩ v)
    (hπ : ∀ t, good t → perm (e t).1 = (pubT t).perm ∧ PermGood (pubT t).perm 18)
    (J : Finset HPos) (hBJ : ∀ q kk w κ, B q kk w κ ⊆ J) (εB : ℝ≥0∞)
    (hεB : ∀ q kk w, ∀ s ∈ J,
      ((Finset.univ.filter fun κ ↦ s ∈ B q kk w κ).card : ℝ≥0∞) ≤ εB * Fintype.card K)
    {R : ℕ} (hR : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge (candCharge X Z Selections J)) R)
    (N : ℕ) :
    uavg (fun t ↦ if good t then kfGame cwUpd msgPol A N (pubT t) (valT t) else 0) ≤
      (2 ^ 301)⁻¹ * progCap + progCap * (R * εB) := by
  refine uavg_ite_le_of_injOn e good hinj hcard _
    (fun p x ↦ if PermGood (perm p) 18 then
      kfGame cwUpd msgPol A N ⟨par p, perm p, (hk p, x.1.1, x.1.2)⟩ (val x.2.1) +
        progCap * revW m0R .instruments (B p x.1 x.2.1 x.2.2)
          (gameR msgPol A ⟨par p, perm p, (hk p, x.1.1, x.1.2)⟩ (val x.2.1)) initR else 0)
    (fun t ht ↦ ?_) _ (fun p ↦ ?_)
  · obtain ⟨v, hv, hg⟩ := hgame t ht
    obtain ⟨hpe, hpg⟩ := hπ t ht
    rw [ite_eq_left (hpe ▸ hpg)]
    have h1 : kfGame cwUpd msgPol A N (pubT t) (valT t) =
        kfGame cwUpd msgPol A N ⟨par (e t).1, perm (e t).1, (hk (e t).1, (e t).2.1.1,
          (e t).2.1.2)⟩ v := by
      unfold kfGame
      rw [show realizeT (valT t) (gameT Selections cwUpd msgPol (pubT t) A) =
        gameR msgPol A (pubT t) (valT t) from rfl, hg, ← hpe]
      rfl
    rw [h1]
    exact kfGame_le_mismatch hperm hsign msgPol N _ _ hv
  · by_cases hp : PermGood (perm p) 18
    · rw [Finset.sum_congr rfl fun x _ ↦ ite_eq_left hp]
      have ha : ∑ x : ((X → Z) × (X → Z)) × (W × K),
          kfGame cwUpd msgPol A N ⟨par p, perm p, (hk p, x.1.1, x.1.2)⟩ (val x.2.1) ≤
          (2 ^ 301)⁻¹ * progCap * Fintype.card (((X → Z) × (X → Z)) × (W × K)) :=
        sum_pair_le
          (fun k k' (w : W × K) ↦ kfGame cwUpd msgPol A N ⟨par p, perm p, (hk p, k, k')⟩ (val w.1))
          _ _ fun w ↦ sum_kfGame_le hperm hsign cwUpd msgPol N (par p) (hk p) (val w.1) hp
      have hr : ∀ (kk : (X → Z) × (X → Z)) (w : W), ∑ κ : K, revW m0R LocalSig.Interp.instruments
          (B p kk w κ) (gameR msgPol A ⟨par p, perm p, (hk p, kk.1, kk.2)⟩ (val w)) initR ≤
          Fintype.card K * (R * εB) := fun kk w ↦
        (sum_revW_le m0R LocalSig.Interp.instruments
          (gameR msgPol A ⟨par p, perm p, (hk p, kk.1, kk.2)⟩ (val w)) initR_posSemidef
          (B p kk w) J (hBJ p kk w) εB (hεB p kk w) (hR _ _)).trans
            (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right zero_le
              ofReal_trace_initR_le_one) zero_le)
      exact sum_add_revW_le (K2 := (X → Z) × (X → Z)) (W := W) (K := K)
        (fun (kk : (X → Z) × (X → Z)) (w : W) ↦
          kfGame cwUpd msgPol A N ⟨par p, perm p, (hk p, kk.1, kk.2)⟩ (val w))
        (fun (kk : (X → Z) × (X → Z)) (w : W) (κ : K) ↦ revW m0R LocalSig.Interp.instruments
          (B p kk w κ) (gameR msgPol A ⟨par p, perm p, (hk p, kk.1, kk.2)⟩ (val w)) initR)
        ha hr progCap
    · rw [Finset.sum_eq_zero fun x _ ↦ ite_eq_right hp]
      exact zero_le

/-- **RecJ's `κ` over the tables** (`msgPol`): `uavg_kfGame_table_le` for `kfPre`. -/
theorem uavg_kfPre_table_le (e : Θ → Q × (((X → Z) × (X → Z)) × (W × K))) (good : Θ → Prop)
    [DecidablePred good] (hinj : Set.InjOn e {t | good t})
    (hcard : Fintype.card Q * Fintype.card (((X → Z) × (X → Z)) × (W × K)) ≤ Fintype.card Θ)
    (par : Q → PublicParameter) (perm : Q → Equiv.Perm (X × Z)) (hk : Q → Z → X)
    (val : W → (s : HPos) → XD s) (B : Q → ((X → Z) × (X → Z)) → W → K → Finset HPos)
    (pubT : Θ → Pub) (valT : Θ → (s : HPos) → XD s)
    (hgame : ∀ t, good t → ∃ v : (s : HPos) → XD s,
      Agree (Finset.univ \ B (e t).1 (e t).2.1 (e t).2.2.1 (e t).2.2.2) v (val (e t).2.2.1) ∧
      gameR msgPol A (pubT t) (valT t) =
        gameR msgPol A ⟨par (e t).1, perm (e t).1, (hk (e t).1, (e t).2.1.1, (e t).2.1.2)⟩ v)
    (hπ : ∀ t, good t → perm (e t).1 = (pubT t).perm ∧ PermGood (pubT t).perm 18)
    (J : Finset HPos) (hBJ : ∀ q kk w κ, B q kk w κ ⊆ J) (εB : ℝ≥0∞)
    (hεB : ∀ q kk w, ∀ s ∈ J,
      ((Finset.univ.filter fun κ ↦ s ∈ B q kk w κ).card : ℝ≥0∞) ≤ εB * Fintype.card K)
    {R : ℕ} (hR : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge (candCharge X Z Selections J)) R) :
    uavg (fun t ↦ if good t then kfPre msgPol A (pubT t) (valT t) else 0) ≤
      (2 ^ 301)⁻¹ * progCap + progCap * (R * εB) :=
  (uavg_mono fun t ↦ by
    by_cases h : good t
    · rw [ite_eq_left h, ite_eq_left h]
      exact kfPre_le_kfGame msgPol A _ _
    · rw [ite_eq_right h, ite_eq_right h]).trans
    (uavg_kfGame_table_le hperm hsign e good hinj hcard par perm hk val B pubT valT hgame hπ J hBJ
      εB hεB hR progCap)

/-- **ProgSafe's `hk` over the tables** (`msgPol`, `cwUpd`, `N + 6q + clsCap ≤ 2^68`):
`uavg_kfGame_table_le` for `kW`. -/
theorem uavg_kW_table_le {N : ℕ} (hN : N + (6 * q + clsCap) ≤ 2 ^ 68)
    (e : Θ → Q × (((X → Z) × (X → Z)) × (W × K))) (good : Θ → Prop)
    [DecidablePred good] (hinj : Set.InjOn e {t | good t})
    (hcard : Fintype.card Q * Fintype.card (((X → Z) × (X → Z)) × (W × K)) ≤ Fintype.card Θ)
    (par : Q → PublicParameter) (perm : Q → Equiv.Perm (X × Z)) (hk : Q → Z → X)
    (val : W → (s : HPos) → XD s) (B : Q → ((X → Z) × (X → Z)) → W → K → Finset HPos)
    (pubT : Θ → Pub) (valT : Θ → (s : HPos) → XD s)
    (hgame : ∀ t, good t → ∃ v : (s : HPos) → XD s,
      Agree (Finset.univ \ B (e t).1 (e t).2.1 (e t).2.2.1 (e t).2.2.2) v (val (e t).2.2.1) ∧
      gameR msgPol A (pubT t) (valT t) =
        gameR msgPol A ⟨par (e t).1, perm (e t).1, (hk (e t).1, (e t).2.1.1, (e t).2.1.2)⟩ v)
    (hπ : ∀ t, good t → perm (e t).1 = (pubT t).perm ∧ PermGood (pubT t).perm 18)
    (J : Finset HPos) (hBJ : ∀ q kk w κ, B q kk w κ ⊆ J) (εB : ℝ≥0∞)
    (hεB : ∀ q kk w, ∀ s ∈ J,
      ((Finset.univ.filter fun κ ↦ s ∈ B q kk w κ).card : ℝ≥0∞) ≤ εB * Fintype.card K)
    {R : ℕ} (hR : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge (candCharge X Z Selections J)) R)
    [∀ t, DecidablePred (· ∈ Bad (S := HPos) (evData (pubT t) (valT t)) N)] :
    uavg (fun t ↦ if good t then kW (Bad (evData (pubT t) (valT t)) N) m0R
      (realizeT (valT t) (gameT Selections cwUpd msgPol (pubT t) A)) initR else 0) ≤
      (2 ^ 301)⁻¹ * progCap + progCap * (R * εB) :=
  (uavg_mono fun t ↦ by
    by_cases h : good t
    · rw [ite_eq_left h, ite_eq_left h]
      exact kW_le_kfGame hperm hsign hN cwUpd msgPol _ _
    · rw [ite_eq_right h, ite_eq_right h]).trans
    (uavg_kfGame_table_le hperm hsign e good hinj hcard par perm hk val B pubT valT hgame hπ J hBJ
      εB hεB hR N)

end table

end Quantum.Sphincs.Assembly

end
