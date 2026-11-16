module

public import Quantum.Sphincs.Assembly.PrefixFacts
public import Quantum.Sphincs.Assembly.GameR
public import Quantum.Sphincs.Assembly.GameTCalls
public import Quantum.Sphincs.Assembly.TrialsOff
public import Quantum.Xmss.Assembly.TrialHit
public import Quantum.Sponge.Oracle.Hardwired.DecUniform

@[expose] public section

/-!
# The trial-hit mass of leanSPHINCS

PrefixFacts' `TrialHit pub v`: the decompressed registers where some trial (counter below
`encodingAttemptLimit`) of some key `K_l(idx)` on the value it signs, `v (msgPos K)`, read against
the register's view, reads a cell of `ProgCell pub v` (the cells of the in-table slots' honest
paths and of every message's `H_msg` calls at its randomizer). Its mass at the end of the
canonical game `gameR pol A pub v` (`trialHitMassAt`, `trialHitMassP` at `strPol`) is bounded on
template data with `TrialsOff pub.xw pub.keys.1 (valsOf v)` and `PermGood pub.perm 18`, mirroring
leanXMSS's `Quantum.Xmss.Assembly.TrialHit` over `(pub, v)` instead of a table.

* **The program ports program only `ProgCell` cells** (`forallQueries_cellPortIn_gameT`): from
  GameTCalls' batch invariant `HB` (`hb_gameT`) with the register-free condition `cellOk`; the
  held ports along a run stay pairwise compatible (`HeldCompat`), so some hardwired register holds
  them (`exists_allHeld`) and the batch condition holds at the port.
* **A database event on the reachable registers** (`trialHitMassAt_le_eventMass`): cutting the
  other program ports (`cutRP`) changes no run (`run_cutRP`), and along the cut runtime the
  hardwired cells stay in `ProgCell` (`supp_run_cutRP`); there the view agrees with the databases
  off `ProgCell`, so the trial hit is the database event `HitView pub v D.fill`
  (`hitView_of_trialHit`), which depends only on the cells off `ProgCell` (`hitView_congr`).
* **The uniform databases** (`DecUniformHypP`, proved in
  `Quantum.Sphincs.Assembly.TrialHitUniform`):
  the decompressed weight of a database event determined off the static `cellsHw (ProgCell pub v)`
  is at most its fraction of the total tables.
* **Counting** (leanXMSS's `card_mul_card_filter_le_of_blocks`): a trial input is one block; its
  `k` cell is no `ProgCell` cell (`not_progCell_k`: in-table `k`-cells by `TrialsOff`, `H_msg`
  blocks have 84 bytes, trials 68); its `k'` and `h` cells lie in `k'CellsP`, `hCellsP` (at most
  `2^50 + 2^257` each). With at most `2^60` trial blocks: `trialHitMass_le_keccak`, `2^-189`.
-/

open Matrix
open scoped ENNReal Kronecker ComplexOrder

universe u v w

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput HashInput Message Randomizer)
open Quantum.Xmss (X Z blocks length_blocks blocks_injective)
open Quantum.Xmss.Hybrid (LazyProg restrictTo progUpdate querySupportedOn_queryStep)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT regFns rnK_zero
  querySupportedOn_run re_trace_conj_kron_proj_le supp_conj_compressReg BadBlk
  card_mul_card_filter_le_of_blocks natCast_div_le_div_of_mul_le point_of_mem_spongeReads_single
  natCast_div_eq_ofReal rnCard_Z rnZ)

namespace Quantum.Sphincs.Assembly

/- Instance search for the run families over the register `SReg` exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## Compatible held ports -/

section held

variable {X₁ Z₁ : Type}

/-- The held ports agree pairwise on common cells. -/
def HeldCompat (C : Set (HwProg X₁ Z₁)) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, Compat c c'

theorem compat_self (c : HwProg X₁ Z₁) : Compat c c := by
  cases c <;> exact fun _ ↦ rfl

theorem compat_symm {c c' : HwProg X₁ Z₁} (h : Compat c c') : Compat c' c := by
  cases c <;> cases c' <;> first | trivial | exact fun e ↦ (h e.symm).symm

theorem heldCompat_empty : HeldCompat (∅ : Set (HwProg X₁ Z₁)) :=
  fun _ hc ↦ absurd hc (Set.notMem_empty _)

theorem heldCompat_heldNext {C : Set (HwProg X₁ Z₁)} (h : HeldCompat C) (c : HwProg X₁ Z₁) :
    HeldCompat (heldNext c C) := by
  intro a ha b hb
  rcases Set.mem_insert_iff.1 ha with rfl | ⟨ha, hac⟩ <;>
    rcases Set.mem_insert_iff.1 hb with rfl | ⟨hb, hbc⟩
  · exact compat_self _
  · exact hbc
  · exact compat_symm hac
  · exact h a ha b hb

/-- **Compatible ports are held together** by some hardwired register. -/
theorem exists_allHeld {C : Set (HwProg X₁ Z₁)} (h : HeldCompat C) :
    ∃ W : Hw X₁ Z₁, AllHeld C W := by
  classical
  refine ⟨(fun z ↦ if hz : ∃ a, HwProg.programH z a ∈ C then some hz.choose else none,
    fun x ↦ if hx : ∃ a, HwProg.programK x a ∈ C then some hx.choose else none,
    fun x ↦ if hx : ∃ a, HwProg.programK' x a ∈ C then some hx.choose else none), ?_⟩
  intro c hc
  cases c with
  | programH z a =>
    have hz : ∃ a', HwProg.programH z a' ∈ C := ⟨a, hc⟩
    show (if hz : ∃ a, HwProg.programH z a ∈ C then some hz.choose else none) = some a
    rw [dite_eq_left hz]
    exact congrArg some (h _ hc _ hz.choose_spec rfl)
  | programK x a =>
    have hx : ∃ a', HwProg.programK x a' ∈ C := ⟨a, hc⟩
    show (if hx : ∃ a, HwProg.programK x a ∈ C then some hx.choose else none) = some a
    rw [dite_eq_left hx]
    exact congrArg some (h _ hc _ hx.choose_spec rfl)
  | programK' x a =>
    have hx : ∃ a', HwProg.programK' x a' ∈ C := ⟨a, hc⟩
    show (if hx : ∃ a, HwProg.programK' x a ∈ C then some hx.choose else none) = some a
    rw [dite_eq_left hx]
    exact congrArg some (h _ hc _ hx.choose_spec rfl)

theorem progUpdate_h_of [DecidableEq X₁] [DecidableEq Z₁] (c : HwProg X₁ Z₁) (W : Hw X₁ Z₁)
    (z : Z₁) (hc : ∀ a, c ≠ .programH z a) : (progUpdate c W).1 z = W.1 z := by
  cases c with
  | programH z₀ a =>
    exact Function.update_of_ne (fun e : z = z₀ ↦ hc a (by rw [e])) _ _
  | programK => rfl
  | programK' => rfl

theorem progUpdate_k_of [DecidableEq X₁] [DecidableEq Z₁] (c : HwProg X₁ Z₁) (W : Hw X₁ Z₁)
    (x : X₁) (hc : ∀ a, c ≠ .programK x a) : (progUpdate c W).2.1 x = W.2.1 x := by
  cases c with
  | programH => rfl
  | programK x₀ a =>
    exact Function.update_of_ne (fun e : x = x₀ ↦ hc a (by rw [e])) _ _
  | programK' => rfl

theorem progUpdate_k'_of [DecidableEq X₁] [DecidableEq Z₁] (c : HwProg X₁ Z₁) (W : Hw X₁ Z₁)
    (x : X₁) (hc : ∀ a, c ≠ .programK' x a) : (progUpdate c W).2.2 x = W.2.2 x := by
  cases c with
  | programH => rfl
  | programK => rfl
  | programK' x₀ a =>
    exact Function.update_of_ne (fun e : x = x₀ ↦ hc a (by rw [e])) _ _

end held

/-! ## The program ports program cells of `Pc` -/

section ports

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- The register-free condition on a program call: it programs a cell of `Pc`. -/
def cellOk (Pc : SpongeQuery X Z → Prop) (c : HwProg X Z) (_ : HwReg X Z (Finset HPos × M)) :
    Prop :=
  Pc (progPt c)

/-- **A port of runtime 2 programs a cell of `Pc`** (the other ports are free). -/
def CellPortIn (Pc : SpongeQuery X Z → Prop) : (recHwSpec X Z HPos M).Port → Prop
  | .inl (.inr c) => Pc (progPt c)
  | _ => True

/-- One call of a port-level condition. -/
theorem forallQueries_queryBind_cellPortIn (m₀ : Finset HPos × M) (I : L.Interp)
    {Pc : SpongeQuery X Z → Prop} {A : QReg} (i : (recHwSpec X Z HPos M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z HPos M).In i × E)
    (k' : (recHwSpec X Z HPos M).Result i → QuantumComp L (recHwSpec X Z HPos M) Ω
      (QReg.of ((recHwSpec X Z HPos M).Out i × E)))
    (hi : CellPortIn Pc i)
    (hk : ∀ r ρ', (runtimeR m₀).ForallQueries I (fun j _ _ ↦ CellPortIn Pc j) (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ) :
    (runtimeR m₀).ForallQueries I (fun j _ _ ↦ CellPortIn Pc j)
      (QuantumComp.queryBind i E ℓ k') ρ :=
  ⟨hi, fun r ↦ hk r _⟩

/-- **A template whose program ports satisfy `cellOk Pc` in batch order calls only program ports
of cells of `Pc`**, from compatible held ports. -/
theorem forallQueries_cellPortIn_of_hb (m₀ : Finset HPos × M) (I : L.Interp)
    (Pc : SpongeQuery X Z → Prop) (v : (s : HPos) → XD s) {A : QReg}
    (y : QuantumComp L (SSpec M) Ω A) :
    ∀ C C', HB (cellOk (M := M) Pc) v y C C' → HeldCompat C →
      ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
        (runtimeR m₀).ForallQueries I (fun j _ _ ↦ CellPortIn Pc j) (realizeT v y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro C C' hy hC ρ b
    exact ih b C C' (hy.2 (ULift.up b)) hC _
  | queryBind _ i E ℓ k ih =>
    intro C C' hy hC ρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_cellPortIn m₀ I (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT v (k r)) trivial (fun r ↦ ih r C C' (hy.2 (ULift.up r)) hC) ρ
    · exact forallQueries_queryBind_cellPortIn m₀ I (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT v (k r)) trivial (fun r ↦ ih r C C' (hy.2 (ULift.up r)) hC) ρ
    · obtain ⟨W, hW⟩ := exists_allHeld hC
      have hok := hy.1 ((Database.empty, Database.empty, Database.empty), W, m₀) hW
      cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_cellPortIn m₀ I
          (.inl (.inr ((LazyProg.programH T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r)) hok
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r)) (heldCompat_heldNext hC _)) ρ
      | programK T₀ c =>
        exact forallQueries_queryBind_cellPortIn m₀ I
          (.inl (.inr ((LazyProg.programK T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r)) hok
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r)) (heldCompat_heldNext hC _)) ρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_cellPortIn m₀ I
          (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r)) hok
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r)) (heldCompat_heldNext hC _)) ρ
    · exact forallQueries_queryBind_cellPortIn m₀ I (.inr T) E ℓ
        (fun m ↦ realizeT v (k (restrictTo T v, m))) trivial
        (fun m ↦ ih (restrictTo T v, m) C C' (hy.2 (ULift.up (restrictTo T v, m))) hC) ρ

variable (pub : Pub) (v : (s : HPos) → XD s)

omit [Fintype M] [DecidableEq M] in
/-- An in-table slot's ports program cells of its honest path. -/
theorem batchOk_slotCell {s : Slot} (hs : InTable s) :
    BatchOk pub (cellOk (M := M) (ProgCell pub v)) (slotBlk pub.seed s (valsOf v))
      (cor128 (valsOf v (slotOutPos s))) (nBlk pub.seed s) :=
  fun j hj _ _ ↦ ⟨Or.inl ⟨s, hs, j, hj, Or.inl rfl⟩,
    fun _ ↦ ⟨Or.inl ⟨s, hs, j, hj, Or.inr (Or.inl rfl)⟩,
      fun _ ↦ Or.inl ⟨s, hs, j, hj, Or.inr (Or.inr (congrArg SpongeQuery.h
        (cellH_fst pub _ _ _ j)))⟩⟩⟩

omit [Fintype M] [DecidableEq M] in
/-- An `H_msg` call's ports at its randomizer program cells of the call. -/
theorem batchOk_hmsgCall (msg : Message) (i : DigestCall) (y : HashOutput) :
    BatchOk pub (cellOk (M := M) (ProgCell pub v))
      (slotBlk pub.seed (.hmsg (v (.rnd msg)) msg i) (valsOf v)) (cor256 y) 1 :=
  fun j hj _ _ ↦ ⟨Or.inr ⟨msg, i, j, hj, Or.inl rfl⟩,
    fun _ ↦ ⟨Or.inr ⟨msg, i, j, hj, Or.inr (Or.inl rfl)⟩,
      fun _ ↦ Or.inr ⟨msg, i, j, hj, Or.inr (Or.inr (congrArg SpongeQuery.h
        (cellH_fst pub _ _ _ j)))⟩⟩⟩

/-- **The realized game calls only program ports of `ProgCell` cells**, for every digest policy,
from any state. -/
theorem forallQueries_cellPortIn_gameT (m₀ : Finset HPos × M) (upd : TrialUpd M)
    (pol : DigestPolicy) (A : SAdversary)
    (ρ : Matrix (QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D)
      (QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (fun j _ _ ↦ CellPortIn (ProgCell pub v) j) (realizeT v (gameT M upd pol pub A)) ρ :=
  forallQueries_cellPortIn_of_hb m₀ _ _ v _ ∅ ∅
    (hb_gameT (cellOk (ProgCell pub v)) v pub (fun _ hs ↦ batchOk_slotCell pub v hs)
      (fun msg i y ↦ batchOk_hmsgCall pub v msg i y) upd pol A) heldCompat_empty ρ

end ports

/-! ## The reachable registers keep their hardwired cells in `Pc` -/

section reach

variable {M : Type} [Fintype M] [DecidableEq M] {Pc : SpongeQuery X Z → Prop}

/-- Every hardwired cell of `W` is a cell of `Pc`. -/
def GoodW (Pc : SpongeQuery X Z → Prop) (W : Hw X Z) : Prop :=
  ∀ q, InHw W q → Pc q

theorem goodW_progUpdate {W : Hw X Z} (hW : GoodW Pc W) {c : HwProg X Z} (hc : Pc (progPt c)) :
    GoodW Pc (progUpdate c W) := by
  intro q hq
  cases q with
  | h z =>
    have hq' : (progUpdate c W).1 z ≠ none := hq
    rcases em (∃ a, c = .programH z a) with ⟨a, rfl⟩ | hne
    · exact hc
    · rw [progUpdate_h_of c W z fun a e ↦ hne ⟨a, e⟩] at hq'
      exact hW (.h z) hq'
  | k x =>
    have hq' : (progUpdate c W).2.1 x ≠ none := hq
    rcases em (∃ a, c = .programK x a) with ⟨a, rfl⟩ | hne
    · exact hc
    · rw [progUpdate_k_of c W x fun a e ↦ hne ⟨a, e⟩] at hq'
      exact hW (.k x) hq'
  | k' x =>
    have hq' : (progUpdate c W).2.2 x ≠ none := hq
    rcases em (∃ a, c = .programK' x a) with ⟨a, rfl⟩ | hne
    · exact hc
    · rw [progUpdate_k'_of c W x fun a e ↦ hne ⟨a, e⟩] at hq'
      exact hW (.k' x) hq'

/-- A read port keeps the hardwired cells in `Pc`. -/
theorem stepR_good_read (m₀ : Finset HPos × M) (c : HwRead X Z (Finset HPos × M)) :
    StepR m₀ (.inl (.inl (.inr c))) (fun s ↦ GoodW Pc s.2.1) (fun s ↦ GoodW Pc s.2.1) := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c)))).branch r σ =
      MatrixMap.conj (hwReadKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ (congrArg (GoodW Pc ·)
    (hwReadKraus_ne_zero_hw c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK)).mpr hq

variable (Pc) in
/-- Runtime 2 with record ports, with the program ports of cells outside `Pc` cut to the failing
subinstrument. -/
noncomputable def cutStepP (m₀ : Finset HPos × M) (i : (recHwSpec X Z HPos M).Port) :
    SubInstrument ((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z HPos M).Out i × (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z HPos M).Result i) :=
  open Classical in
  if CellPortIn Pc i then (runtimeR m₀).step i else DSubInstrument.fail

variable (Pc) in
/-- The cut runtime. -/
noncomputable def cutRP (m₀ : Finset HPos × M) : QuantumRuntime (recHwSpec X Z HPos M) :=
  ⟨(runtimeR (X := X) (Z := Z) m₀).D, (runtimeR (X := X) (Z := Z) m₀).init, cutStepP Pc m₀⟩

/-- Every step of the cut runtime keeps the hardwired cells in `Pc`. -/
theorem cutStepP_good (m₀ : Finset HPos × M) (i : (recHwSpec X Z HPos M).Port)
    (r : (recHwSpec X Z HPos M).Result i)
    (σ : Matrix ((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (hσ : QuerySupportedOn
      (fun m : (recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | GoodW Pc s.2.1} σ) :
    QuerySupportedOn
      (fun m : (recHwSpec X Z HPos M).Out i × (runtimeR (X := X) (Z := Z) m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | GoodW Pc s.2.1} ((cutStepP Pc m₀ i).branch r σ) := by
  unfold cutStepP
  split_ifs with hi
  · rcases i with ((i | c) | c) | T
    · exact stepR_sponge (P := fun s ↦ GoodW Pc s.2.1) (P' := fun s ↦ GoodW Pc s.2.1) m₀ i
        (fun _ _ he hr ↦ (congrArg (fun t ↦ GoodW Pc t.1) he).mpr hr) r σ hσ
    · exact stepR_good_read m₀ c r σ hσ
    · exact stepR_prog (P := fun s ↦ GoodW Pc s.2.1) (P' := fun s ↦ GoodW Pc s.2.1) m₀ c
        (fun _ _ he hr ↦ (congrArg (fun t ↦ GoodW Pc t.1) he).mpr (goodW_progUpdate hr hi))
        r σ hσ
    · exact stepR_rec (P := fun s ↦ GoodW Pc s.2.1) (P' := fun s ↦ GoodW Pc s.2.1) m₀ T
        (fun _ _ he hr ↦ (congrArg (fun t ↦ GoodW Pc t.1) he).mpr hr) r σ hσ
  · rw [DSubInstrument.branch_fail]
    exact querySupportedOn_zero _ _

/-- **Cutting changes no run** calling only program ports of cells of `Pc`. -/
theorem run_cutRP (m₀ : Finset HPos × M) {Λ : LocalSig.{u, v}} (I : Λ.Interp)
    {Ω : QReg → Type} {A : QReg} (x : QuantumComp Λ (recHwSpec X Z HPos M) Ω A)
    (ρ : Matrix (A × (runtimeR (X := X) (Z := Z) m₀).D) (A × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (hx : (runtimeR m₀).ForallQueries I (fun j _ _ ↦ CellPortIn Pc j) x ρ) (p : Σ u, Ω u) :
    ((runtimeR m₀).run I x).branch p ρ = ((cutRP Pc m₀).run I x).branch p ρ :=
  run_branch_apply_eq_of_forallQueries (σ₁ := (runtimeR (X := X) (Z := Z) m₀).init)
    (s₁ := (runtimeR (X := X) (Z := Z) m₀).step) (σ₂ := (runtimeR (X := X) (Z := Z) m₀).init)
    (s₂ := cutStepP Pc m₀) I (fun i E σ hσ r ↦ by rw [cutStepP, ite_eq_left hσ]) hx p

/-- Every branch of every run of the cut runtime keeps the hardwired cells in `Pc`. -/
theorem supp_run_cutRP (m₀ : Finset HPos × M) {Λ : LocalSig.{u, v}} (I : Λ.Interp)
    {Ω : QReg → Type} {A : QReg} (x : QuantumComp Λ (recHwSpec X Z HPos M) Ω A)
    {ρ : Matrix (A × (runtimeR (X := X) (Z := Z) m₀).D) (A × (runtimeR (X := X) (Z := Z) m₀).D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × (runtimeR (X := X) (Z := Z) m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | GoodW Pc s.2.1} ρ)
    (p : Σ u, Ω u) :
    QuerySupportedOn (fun m : p.1 × (runtimeR (X := X) (Z := Z) m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | GoodW Pc s.2.1} (((cutRP Pc m₀).run I x).branch p ρ) :=
  querySupportedOn_run (cutRP Pc m₀) {s : HwReg X Z (Finset HPos × M) | GoodW Pc s.2.1}
    (fun i r σ hσ ↦ cutStepP_good m₀ i r σ hσ) I x hρ p

/-- The initial state has no hardwired cell. -/
theorem supp_init_good (m₀ : Finset HPos × M) :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | GoodW Pc s.2.1}
      ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty X Z, m₀) : HwReg X Z (Finset HPos × M))).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · have h0 : GoodW Pc (hwEmpty X Z) := fun q hq ↦ by cases q <;> exact absurd rfl hq
    show GoodW Pc m.2.2.1 ∧ GoodW Pc m'.2.2.1
    rw [← he.1, ← he.2]
    exact ⟨h0, h0⟩
  · exact absurd rfl h

end reach

/-! ## The trial hit as a database event -/

section dbEvent

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **Some trial reads a programmable cell** against the view `t` (`TrialHit pub v` is this event
of the register's view `regFns s`). -/
def HitView (t : SpongeKeys X Z) : Prop :=
  ∃ l idx, ∃ c < encodingAttemptLimit, ∃ rd ∈ inputReads t pub.perm
    (encIn pub (keyOf l idx) (valsOf v (msgPos (keyOf l idx))) (BitVec.ofNat counterBits c)),
      ProgCell pub v rd.point

variable {pub v}

theorem hitView_of_offAgree {t t' : SpongeKeys X Z} (h : OffAgree (ProgCell pub v) t t')
    (ht : HitView pub v t') : HitView pub v t := by
  obtain ⟨l, idx, c, hc, rd, hrd, hin⟩ := ht
  by_contra hs
  have hav : ∀ rd ∈ inputReads t pub.perm (encIn pub (keyOf l idx)
      (valsOf v (msgPos (keyOf l idx))) (BitVec.ofNat counterBits c)),
      ¬ProgCell pub v rd.point :=
    fun rd hrd hin ↦ hs ⟨l, idx, c, hc, rd, hrd, hin⟩
  rw [(inputReads_eq_of_offAgree h pub.perm _ hav).1] at hrd
  exact hav rd hrd hin

/-- **On a register whose hardwired cells are programmable, the trial hit is the database
event**: the view agrees with the databases off the programmable cells. -/
theorem hitView_of_trialHit {s : SReg} (hg : GoodW (ProgCell pub v) s.2.1)
    (hs : s ∈ TrialHit pub v) : HitView pub v s.1.toDbs.fill := by
  refine hitView_of_offAgree (t' := regFns s) ⟨fun z hz ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩ hs
  · have hW : s.2.1.1 z = none := by
      by_contra hne
      exact hz (hg (.h z) hne)
    show (s.1.1 z).getD 0 = ((s.2.1.1 z).or (s.1.1 z)).getD 0
    rw [hW]
    rfl
  · have hW : s.2.1.2.1 x = none := by
      by_contra hne
      exact hx (hg (.k x) hne)
    show (s.1.2.1 x).getD 0 = ((s.2.1.2.1 x).or (s.1.2.1 x)).getD 0
    rw [hW]
    rfl
  · have hW : s.2.1.2.2 x = none := by
      by_contra hne
      exact hx (hg (.k' x) hne)
    show (s.1.2.2 x).getD 0 = ((s.2.1.2.2 x).or (s.1.2.2 x)).getD 0
    rw [hW]
    rfl

variable (pub v) in
/-- The registers whose databases hit a trial. -/
def trialEventP : Set SReg :=
  {s | HitView pub v s.1.toDbs.fill}

variable (Pc : SpongeQuery X Z → Prop) in
open Classical in
/-- **The cells of `Pc` as a static hardwired register** (the values are irrelevant). -/
noncomputable def cellsHw : Hw X Z :=
  (fun z ↦ if Pc (.h z) then some 0 else none, fun x ↦ if Pc (.k x) then some 0 else none,
    fun x ↦ if Pc (.k' x) then some 0 else none)

theorem cellIn_cellsHw {Pc : SpongeQuery X Z → Prop} {c : HwProg X Z} (hc : Pc (progPt c)) :
    c.CellIn (cellsHw Pc) := by
  classical
  cases c with
  | programH z a => exact fun h ↦ Option.some_ne_none (0 : X) ((ite_eq_left hc).symm.trans h)
  | programK x a => exact fun h ↦ Option.some_ne_none (0 : Z) ((ite_eq_left hc).symm.trans h)
  | programK' x a => exact fun h ↦ Option.some_ne_none (0 : Z) ((ite_eq_left hc).symm.trans h)

/-- **The database event depends only on the cells off `ProgCell`.** -/
theorem hitView_congr : OffHw (cellsHw (ProgCell pub v)) fun D ↦ HitView pub v D.toDbs.fill := by
  classical
  intro D D' hh hk hk'
  have hO : OffAgree (ProgCell pub v) D.toDbs.fill D'.toDbs.fill :=
    ⟨fun z hz ↦ congrArg (fun o ↦ Option.getD o 0) (hh z (ite_eq_right hz)),
      fun x hx ↦ congrArg (fun o ↦ Option.getD o 0) (hk x (ite_eq_right hx)),
      fun x hx ↦ congrArg (fun o ↦ Option.getD o 0) (hk' x (ite_eq_right hx))⟩
  exact ⟨hitView_of_offAgree hO.symm, hitView_of_offAgree hO⟩

end dbEvent

/-! ## The trial-hit mass -/

section mass

variable (pol : DigestPolicy) (m₀ : Mem HPos) (A : SAdversary) (pub : Pub)
  (v : (s : HPos) → XD s)

/-- **The mass of a decompressed event** at the end of the canonical game. -/
noncomputable def eventMassP (E : Set (HwReg X Z (Mem HPos))) [DecidablePred (· ∈ E)] : ℝ≥0∞ :=
  (runtimeR m₀).eventWeight .instruments (hwDecProj E) (gameR pol A pub v)
    ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)

/-- **The trial-hit mass** at the digest policy `pol`. -/
noncomputable def trialHitMassAt : ℝ≥0∞ :=
  @eventMassP pol m₀ A pub v (TrialHit pub v) (Classical.decPred _)

/-- **The trial-hit mass** of the event side (`strPol`). -/
noncomputable def trialHitMassP : ℝ≥0∞ :=
  trialHitMassAt strPol m₀ A pub v

/-- **The trial-hit mass is at most the mass of the database event.** -/
theorem trialHitMassAt_le_eventMass :
    trialHitMassAt pol m₀ A pub v ≤
      @eventMassP pol m₀ A pub v (trialEventP pub v) (Classical.decPred _) := by
  have hρ := supp_init_good (Pc := ProgCell pub v) m₀
  have hx := forallQueries_cellPortIn_gameT pub v m₀ cwUpd pol A
    ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)
  unfold trialHitMassAt eventMassP QuantumRuntime.eventWeight hwDecProj
  refine ENNReal.tsum_le_tsum fun p ↦ ENNReal.ofReal_le_ofReal ?_
  have hsupp := supp_run_cutRP m₀ .instruments (gameR pol A pub v) hρ p
  rw [← run_cutRP m₀ .instruments (gameR pol A pub v) _ hx p] at hsupp
  exact re_trace_conj_kron_proj_le (compressReg X Z (Mem HPos))
    compressReg_mul_self conjTranspose_compressReg (· ∈ TrialHit pub v) (· ∈ trialEventP pub v)
    {s | GoodW (ProgCell pub v) s.2.1}
    (((runtimeR m₀).run .instruments (gameR pol A pub v)).posSemidef_branch_apply p
      ((SubState.basis ()).prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef)
    (supp_conj_compressReg (P := fun b ↦ GoodW (ProgCell pub v) b.1) hsupp)
    fun _ hs ht ↦ hitView_of_trialHit hs ht

open Classical in
/-- **The decompressed uniformity of the databases** along the canonical game (proved in
`Quantum.Sphincs.Assembly.TrialHitUniform`): an event of the databases determined off the
programmable cells has decompressed weight at most its fraction of the total tables. -/
def DecUniformHypP : Prop :=
  ∀ F : DbReg X Z → Prop, OffHw (cellsHw (ProgCell pub v)) F →
    @eventMassP pol m₀ A pub v {s | F s.1} (Classical.decPred _) ≤
      ((Finset.univ.filter fun t : (Z → X) × (X → Z) × (X → Z) ↦ F (ofFunDbs t)).card : ℝ≥0∞) /
        Fintype.card ((Z → X) × (X → Z) × (X → Z))

end mass

/-! ## The cells and the trial blocks -/

section cells

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- The `k'` cells the template may program: those of the in-table paths (by output position and
round) and of the `H_msg` calls. -/
noncomputable def k'CellsP : Finset X :=
  (Finset.univ.image fun q : ValPos × Fin 8 ↦
    (cellK' pub (slotBlk pub.seed (outSlot q.1) (valsOf v)) q.2).1) ∪
  Finset.univ.image fun q : Message × DigestCall ↦ (cellK' pub (hBlk pub v q.1 q.2) 0).1

/-- The `h` cells the template may program. -/
noncomputable def hCellsP : Finset Z :=
  (Finset.univ.image fun q : ValPos × Fin 8 ↦
    rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
      (slotBlk pub.seed (outSlot q.1) (valsOf v)) q.2) ∪
  Finset.univ.image fun q : Message × DigestCall ↦ hZ pub v q.1 q.2

/-- The blocks of the trials of the keys on the values they sign. -/
noncomputable def trialBlocksP : Finset X :=
  Finset.univ.image fun q : Layer × Index × Fin encodingAttemptLimit ↦
    (blocks (encIn pub (keyOf q.1 q.2.1) (valsOf v (msgPos (keyOf q.1 q.2.1)))
      (BitVec.ofNat counterBits q.2.2))).headD 0

theorem mem_k'CellsP_slot (q : ValPos × Fin 8) :
    (cellK' pub (slotBlk pub.seed (outSlot q.1) (valsOf v)) q.2).1 ∈ k'CellsP pub v := by
  simp only [k'CellsP, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl ⟨q, rfl⟩

theorem mem_k'CellsP_hmsg (q : Message × DigestCall) :
    (cellK' pub (hBlk pub v q.1 q.2) 0).1 ∈ k'CellsP pub v := by
  simp only [k'CellsP, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨q, rfl⟩

theorem mem_hCellsP_slot (q : ValPos × Fin 8) :
    rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
      (slotBlk pub.seed (outSlot q.1) (valsOf v)) q.2 ∈ hCellsP pub v := by
  simp only [hCellsP, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl ⟨q, rfl⟩

theorem mem_hCellsP_hmsg (q : Message × DigestCall) : hZ pub v q.1 q.2 ∈ hCellsP pub v := by
  simp only [hCellsP, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨q, rfl⟩

theorem mem_trialBlocksP_of (q : Layer × Index × Fin encodingAttemptLimit) :
    (blocks (encIn pub (keyOf q.1 q.2.1) (valsOf v (msgPos (keyOf q.1 q.2.1)))
      (BitVec.ofNat counterBits q.2.2))).headD 0 ∈ trialBlocksP pub v := by
  simp only [trialBlocksP, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨q, rfl⟩

set_option exponentiation.threshold 4096 in
theorem card_message_digestCall : Fintype.card (Message × DigestCall) = 2 ^ 257 := by
  rw [Fintype.card_prod, ← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec, Fintype.card_fin]
  norm_num [digestCallCount]

theorem card_valPos_fin8_le : Fintype.card (ValPos × Fin 8) ≤ 2 ^ 50 := by
  rw [Fintype.card_prod, Fintype.card_fin]
  exact (Nat.mul_le_mul_right 8 card_valPos_le).trans_eq (by norm_num)

set_option exponentiation.threshold 4096 in
theorem card_k'CellsP_le : (k'CellsP pub v).card ≤ 2 ^ 50 + 2 ^ 257 := by
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · exact Finset.card_image_le.trans (by rw [Finset.card_univ]; exact card_valPos_fin8_le)
  · exact Finset.card_image_le.trans (by rw [Finset.card_univ, card_message_digestCall])

set_option exponentiation.threshold 4096 in
theorem card_hCellsP_le : (hCellsP pub v).card ≤ 2 ^ 50 + 2 ^ 257 := by
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · exact Finset.card_image_le.trans (by rw [Finset.card_univ]; exact card_valPos_fin8_le)
  · exact Finset.card_image_le.trans (by rw [Finset.card_univ, card_message_digestCall])

theorem card_trialBlocksP_le : (trialBlocksP pub v).card ≤ 2 ^ 60 := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ]
  simp only [Fintype.card_prod, Fintype.card_fin]
  norm_num [layerCount, indexBits, encodingAttemptLimit]

attribute [irreducible] k'CellsP hCellsP trialBlocksP

variable {pub v}

/-- The `k'` cell of a programmable round is in `k'CellsP`. -/
theorem mem_k'CellsP {y : X} (h : ProgCell pub v (.k' y)) : y ∈ k'CellsP pub v := by
  rcases h with ⟨s, hs, j, hj, hq⟩ | ⟨M, i, j, hj, hq⟩
  · rcases hq with hq | hq | hq
    · cases hq
    · injection hq with hy
      have hm := mem_k'CellsP_slot pub v (slotOutPos s, ⟨j, hj.trans_le (nBlk_le _ _)⟩)
      rw [outSlot_slotOutPos hs] at hm
      rw [hy]
      exact hm
    · cases hq
  · obtain rfl : j = 0 := by omega
    rcases hq with hq | hq | hq
    · cases hq
    · injection hq with hy
      rw [hy]
      exact mem_k'CellsP_hmsg pub v (M, i)
    · cases hq

/-- The `h` cell of a programmable round is in `hCellsP`. -/
theorem mem_hCellsP {z : Z} (h : ProgCell pub v (.h z)) : z ∈ hCellsP pub v := by
  rcases h with ⟨s, hs, j, hj, hq⟩ | ⟨M, i, j, hj, hq⟩
  · rcases hq with hq | hq | hq
    · cases hq
    · cases hq
    · injection hq with hy
      have hm := mem_hCellsP_slot pub v (slotOutPos s, ⟨j, hj.trans_le (nBlk_le _ _)⟩)
      rw [outSlot_slotOutPos hs] at hm
      rw [hy]
      exact hm
  · obtain rfl : j = 0 := by omega
    rcases hq with hq | hq | hq
    · cases hq
    · cases hq
    · injection hq with hy
      rw [hy]
      exact mem_hCellsP_hmsg pub v (M, i)

/-- **A trial block is no programmable `k` cell**: not an in-table one (`TrialsOff`), and no
`H_msg` call's block (84 bytes against the trial's 68). -/
theorem not_progCell_k (hoff : TrialsOff pub.xw pub.keys.1 (valsOf v)) {K : Key} {m : Digest}
    {c : EncodingCounter} {x : X} (hx : blocks (encIn pub K m c) = [x]) :
    ¬ProgCell pub v (.k x) := by
  rintro (⟨s, hs, j, hj, hq⟩ | ⟨M, i, j, hj, hq⟩)
  · rcases hq with hq | hq | hq
    · injection hq with hq'
      have e : sCellK pub.xw pub.keys.1 s (valsOf v) j = x := hq'.symm
      exact hoff s hs j hj ⟨pub.seed, K, m, c, by rw [e]; exact hx⟩
    · cases hq
    · cases hq
  · obtain rfl : j = 0 := by omega
    rcases hq with hq | hq | hq
    · injection hq with hq'
      have e1 : (cellK pub (hBlk pub v M i) 0).1 = hBlk pub v M i 0 := rnK_zero ..
      have h84 : (slotInput pub.seed (.hmsg (v (.rnd M)) M i) (valsOf v)).length = 84 :=
        length_messageDigestInput _ _ _ _ _
      obtain ⟨y, hy⟩ : ∃ y,
          blocks (slotInput pub.seed (.hmsg (v (.rnd M)) M i) (valsOf v)) = [y] :=
        List.length_eq_one_iff.mp (by rw [length_blocks, h84])
      have e2 : hBlk pub v M i 0 = y := by
        show (blocks (slotInput pub.seed (.hmsg (v (.rnd M)) M i) (valsOf v))).getD 0 0 = y
        rw [hy]
        rfl
      have hb : blocks (encIn pub K m c) =
          blocks (slotInput pub.seed (.hmsg (v (.rnd M)) M i) (valsOf v)) := by
        rw [hx, hy, hq'.trans (e1.trans e2)]
      have hl := congrArg List.length (blocks_injective hb)
      rw [length_encIn, h84] at hl
      omega
    · cases hq
    · cases hq

/-- **A trial hit of the databases is a hit of a `k'` or `h` cell at a trial block.** -/
theorem badBlk_of_hitView (hoff : TrialsOff pub.xw pub.keys.1 (valsOf v)) {t : SpongeKeys X Z}
    (h : HitView pub v t) :
    ∃ x ∈ trialBlocksP pub v, BadBlk pub.perm (k'CellsP pub v) (hCellsP pub v) x t := by
  obtain ⟨l, idx, c, hc, rd, hrd, hin⟩ := h
  obtain ⟨x, hx⟩ : ∃ x, blocks (encIn pub (keyOf l idx) (valsOf v (msgPos (keyOf l idx)))
      (BitVec.ofNat counterBits c)) = [x] :=
    List.length_eq_one_iff.mp (by rw [length_blocks, length_encIn])
  have hmem : x ∈ trialBlocksP pub v := by
    have h := mem_trialBlocksP_of pub v (l, idx, ⟨c, hc⟩)
    rw [hx] at h
    exact h
  refine ⟨x, hmem, ?_⟩
  have hrd' : rd ∈ spongeReads pub.perm t.1 t.2.1 t.2.2 [x] := by
    have he : inputReads t pub.perm (encIn pub (keyOf l idx) (valsOf v (msgPos (keyOf l idx)))
        (BitVec.ofNat counterBits c)) = spongeReads pub.perm t.1 t.2.1 t.2.2
          (blocks (encIn pub (keyOf l idx) (valsOf v (msgPos (keyOf l idx)))
            (BitVec.ofNat counterBits c))) := rfl
    rw [he, hx] at hrd
    exact hrd
  rcases point_of_mem_spongeReads_single pub.perm t.1 t.2.1 t.2.2 x hrd' with hp | hp | hp <;>
    rw [hp] at hin
  · exact absurd hin (not_progCell_k hoff hx)
  · exact Or.inl (mem_k'CellsP hin)
  · exact Or.inr (mem_hCellsP hin)

variable {pol : DigestPolicy} {m₀ : Mem HPos} {A : SAdversary}

open Classical in
/-- **The trial-hit mass, counted**: at most `|trialBlocksP| (18 |k'CellsP| + |hCellsP|) / |Z|`. -/
theorem trialHitMass_le_frac (hU : DecUniformHypP pol m₀ A pub v)
    (hoff : TrialsOff pub.xw pub.keys.1 (valsOf v)) (hπ : PermGood pub.perm 18) :
    trialHitMassAt pol m₀ A pub v ≤ (((trialBlocksP pub v).card *
      (18 * (k'CellsP pub v).card + (hCellsP pub v).card) : ℕ) : ℝ≥0∞) / Fintype.card Z := by
  refine (trialHitMassAt_le_eventMass pol m₀ A pub v).trans
    ((hU (fun D ↦ HitView pub v D.toDbs.fill) hitView_congr).trans ?_)
  exact natCast_div_le_div_of_mul_le Fintype.card_pos Fintype.card_pos
    (card_mul_card_filter_le_of_blocks hπ (k'CellsP pub v) (hCellsP pub v) (trialBlocksP pub v)
      (fun t ↦ HitView pub v (ofFunDbs t).toDbs.fill) fun _ ht ↦ badBlk_of_hitView hoff ht)

set_option exponentiation.threshold 4096 in
/-- The count at Keccak's sizes: `2^323 / 2^512`. -/
theorem trialHitTermP_le {b k h cZ : ℕ} (hb : b ≤ 2 ^ 60) (hk : k ≤ 2 ^ 50 + 2 ^ 257)
    (hh : h ≤ 2 ^ 50 + 2 ^ 257) (hZ : cZ = 2 ^ 512) :
    ((b * (18 * k + h) : ℕ) : ℝ≥0∞) / cZ ≤ ENNReal.ofReal (1 / 2 ^ 189) := by
  subst hZ
  have hK : b * (18 * k + h) ≤ 2 ^ 323 :=
    calc b * (18 * k + h) ≤ 2 ^ 60 * (18 * (2 ^ 50 + 2 ^ 257) + (2 ^ 50 + 2 ^ 257)) := by
          gcongr
      _ ≤ 2 ^ 323 := by norm_num
  rw [natCast_div_eq_ofReal _ (2 ^ 512) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc ((b * (18 * k + h) : ℕ) : ℝ) / ((2 ^ 512 : ℕ) : ℝ) ≤ 2 ^ 323 / 2 ^ 512 := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hK) (by positivity)
    _ ≤ 1 / 2 ^ 189 := by norm_num

/-- **The trial-hit mass at Keccak's sizes**: at most `2^-189` on template data with `TrialsOff`
and `PermGood pub.perm 18`, given the decompressed uniformity. -/
theorem trialHitMass_le_keccak (hU : DecUniformHypP pol m₀ A pub v)
    (hoff : TrialsOff pub.xw pub.keys.1 (valsOf v)) (hπ : PermGood pub.perm 18) :
    trialHitMassAt pol m₀ A pub v ≤ ENNReal.ofReal (1 / 2 ^ 189) :=
  (trialHitMass_le_frac hU hoff hπ).trans (trialHitTermP_le (card_trialBlocksP_le pub v)
    (card_k'CellsP_le pub v) (card_hCellsP_le pub v) rnCard_Z)

end cells

end Quantum.Sphincs.Assembly

end
