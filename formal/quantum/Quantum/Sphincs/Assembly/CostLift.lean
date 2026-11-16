module

public import Quantum.Sphincs.EncCost
public import Quantum.Xmss.Assembly.CostRun

@[expose] public section

/-!
# The classical costs of leanSPHINCS's event bound, per port

The per-port flip costs of the event bound for leanSPHINCS's event `Bad d N` (Events) on a memory
`M` holding the selections through `get : M → Selections`, as leanXMSS's
`Quantum.Xmss.Assembly.CostLift`, whose generic parts are reused: the reads of `k`, `k'` cells
(`cellRead_readK`, `flipCost_readK_le`), the linearized cross terms (`cost_le_lin`,
`cost_le_lin'`), the weights along a run (`totalWeight_le_lin`, `le_sq_add_of_forall_lin`,
`extWeight_hwCost_le_lin`).

* **Trial reads** (`TrialPt`, `IsTrial`, `trialOf`, `trialSR`, `PRof`, `massW`, `encWt`, `encW`):
  a WOTS+C counter trial of key `K` is the final `h`-read of its one-block input with block `x` and
  rate `xi` after `π`; its selection reads are Events' `SelectRead`; on the other read ports the
  selection reads are the states whose read cell is empty (`cellEmpty`). `PRof` is the projector
  off the selection reads, `massW` the weight off them, `encW` the codeword flips of a selecting
  read, `epsW` the flip terms `ε + ε'` of the other reads (`flipF`).
* **Per port** (`flipCost_le_ports`): on the labelled memory `Mem S` (`get = Prod.snd`), for a
  bad set `B` that is `Bad d N` and trial updates that keep the memory or record a codeword
  selection (`cwSel`), the flip cost of a read port relative to `PRof` is at most
  `(1 + s) (encW + epsW) + (1 + 1/s) massW` for every `s > 0` (`flipCost_selectRead_le`, EncCost's
  codeword-restricted count `card_flip_readCw_le`).
* **Filling a `k`, `k'` cell by a read** (`card_flip_readK_hwTargetBad_le`,
  `card_flip_readK'_hwTargetBad_le` for any target event; `card_flip_readK_bad_le`,
  `card_flip_readK'_bad_le` for `Bad`, twice the capacity-scale counts: Struct and Enc, and
  coverage), and filling keeps the event (`mem_bad_fillK`, `mem_bad_fillK'`).
-/

open Matrix Finset
open scoped ENNReal Kronecker ComplexOrder

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open Quantum.Xmss (X Z)
open Quantum.Xmss.Assembly (card_filter_le_of_imp cost_le_lin cost_le_lin' mem_hwTargetBad_fillK
  mem_hwTargetBad_fillK')

namespace Quantum.Sphincs.Assembly

/-! ## Trial reads -/

section ports

variable {M : Type} [Fintype M] [DecidableEq M]

/-- A WOTS+C counter trial of key `K`: the key, the block `x` and the rate `xi` after `π`. -/
structure TrialPt where
  /-- The key `(l, τ, e)`. -/
  K : Key
  /-- The block. -/
  x : X
  /-- The rate after `π`. -/
  xi : X

variable (get : M → Selections) (updOf : TrialPt → M → Option X → M)

omit [Fintype M] [DecidableEq M] in
/-- The read port `c` is the selecting read of a trial: an `h`-read with the trial's update. -/
def IsTrial (c : HwRead X Z M) : Prop := ∃ zt : Z × TrialPt, c = .readH zt.1 (updOf zt.2)

omit [Fintype M] [DecidableEq M] in
open scoped Classical in
/-- The cell and the trial of a selecting read port (a chosen one). -/
noncomputable def trialOf (c : HwRead X Z M) : Z × TrialPt :=
  if h : IsTrial updOf c then Classical.choose h else
    (0, ⟨(⟨0, by decide⟩, ⟨0, Nat.two_pow_pos _⟩, ⟨0, Nat.two_pow_pos _⟩), 0, 0⟩)

omit [Fintype M] [DecidableEq M] in
/-- The cell a read port reads is neither recorded nor hardwired. -/
def cellEmpty : HwRead X Z M → HwReg X Z M → Prop
  | .readH z _, s => s.1.1 z = none ∧ s.2.1.1 z = none
  | .readK x _, s => s.1.2.1 x = none ∧ s.2.1.2.1 x = none
  | .readK' x _, s => s.1.2.2 x = none ∧ s.2.1.2.2 x = none

omit [Fintype M] [DecidableEq M] in
/-- The selection reads of a port: `SelectRead` of its trial on a selecting read port; on the other
read ports, the states whose read cell is empty (neither recorded nor hardwired). -/
def trialSR (d : EvData) (c : HwRead X Z M) (s : HwReg X Z M) : Prop :=
  (IsTrial updOf c ∧ SelectRead d s.1 s.2.1 (get s.2.2) (trialOf updOf c).1 (trialOf updOf c).2.K
    (trialOf updOf c).2.x (trialOf updOf c).2.xi) ∨
  (¬IsTrial updOf c ∧ cellEmpty c s)

omit [Fintype M] [DecidableEq M] in
theorem trialSR_of_isTrial {d : EvData} {c : HwRead X Z M} (ht : IsTrial updOf c)
    {s : HwReg X Z M} (hs : trialSR get updOf d c s) :
    SelectRead d s.1 s.2.1 (get s.2.2) (trialOf updOf c).1 (trialOf updOf c).2.K
      (trialOf updOf c).2.x (trialOf updOf c).2.xi := by
  rcases hs with ⟨-, h⟩ | ⟨hn, -⟩
  · exact h
  · exact absurd ht hn

omit [Fintype M] [DecidableEq M] in
theorem eq_readH_trialOf {c : HwRead X Z M} (ht : IsTrial updOf c) :
    c = .readH (trialOf updOf c).1 (updOf (trialOf updOf c).2) := by
  have h := Classical.choose_spec ht
  simp only [trialOf, ht, ↓reduceDIte]
  exact h

/-- Decidability of the selection reads, classically. -/
noncomputable instance trialSRDec (d : EvData) (c : HwRead X Z M) :
    DecidablePred (trialSR get updOf d c) :=
  Classical.decPred _

/-- **The read projectors of the flip costs**: off the selection reads of the port. -/
noncomputable def PRof (d : EvData) (c : HwRead X Z M) :
    Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ :=
  readPs (trialSR get updOf d c)

theorem PRof_proj (d : EvData) (c : HwRead X Z M) :
    (PRof get updOf d c)ᴴ = PRof get updOf d c ∧
      PRof get updOf d c * PRof get updOf d c = PRof get updOf d c :=
  readPs_proj _

/-- The recorded mass of a read port: `tr (PRof σ)`, the weight off its selection reads. -/
noncomputable def massW (d : EvData) (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (PRof get updOf d c * σ).trace.re

/-- The Enc term of a selecting read of key `K` (`flipCost_selectReadCw_le`): the codeword flips of
the states of `SR` outside `B`. -/
noncomputable def encWt (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (d : EvData) (K : Key)
    (SR : HwReg X Z M → Prop) [DecidablePred SR]
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, if SR q.2 ∧ q.2 ∉ B then
    ((encCwCount d (union q.2.2.1 q.2.1) K * 2 ^ 960 : ℕ) : ℝ) / Fintype.card X * (σ q q).re
  else 0

open scoped Classical in
/-- The Enc weight of a port: `encWt` on a selecting read port, `0` elsewhere. -/
noncomputable def encW (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (d : EvData)
    (c : HwRead X Z M) (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then
    ENNReal.ofReal (encWt B d (trialOf updOf c).2.K (trialSR get updOf d c) σ)
  else 0

omit [DecidableEq M] in
theorem encWt_nonneg (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (d : EvData) (K : Key)
    (SR : HwReg X Z M → Prop) [DecidablePred SR]
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    0 ≤ encWt B d K SR σ :=
  Finset.sum_nonneg fun q _ ↦ by
    have : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    split_ifs
    · positivity
    · exact le_rfl

/-- The flip operator of a read port for the event `B`: `∑ᵣ K rᴴ Q K r - Q`. -/
noncomputable def flipF (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (c : HwRead X Z M) :
    Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ :=
  ∑ r, (hwReadKraus c r)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector B) * hwReadKraus c r -
    (1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector B

open scoped Classical in
/-- The flip terms `ε + ε'` of a read port other than a selecting read (projector `PRof`, off its
empty cell), `0` on the selecting read ports. -/
noncomputable def epsW (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (d : EvData)
    (c : HwRead X Z M) (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then 0 else
    ENNReal.ofReal ((1 - PRof get updOf d c) * flipF B c * (1 - PRof get updOf d c) * σ).trace.re +
      ENNReal.ofReal ((1 - PRof get updOf d c) * flipF B c * PRof get updOf d c * flipF B c *
        (1 - PRof get updOf d c) * σ).trace.re

end ports

/-! ## Per-port costs on the labelled memory -/

section lift

variable {S : Type} [Fintype (Mem S)] [DecidableEq (Mem S)] {d : EvData} {N : ℕ}

/-- **The flip cost of a codeword-selecting read** (EncCost's `flipCost_selectReadCw_le` for any
`SR` within the selection reads and any `B` that is `Bad d N`): `E + p + 2 √(E p)` with
`E = encWt`, `p = tr (readPs SR σ)`. -/
theorem flipCost_selectRead_le (B : Set (HwReg X Z (Mem S))) [DecidablePred (· ∈ B)]
    (hB : ∀ r, r ∈ B ↔ r ∈ Bad d N) (z : Z) (K : Key) (x xi : X)
    (upd : Mem S → Option X → Mem S)
    (hupd : ∀ m v, upd m (some v) = m ∨ upd m (some v) = (m.1, cwSel m.2 K x xi v))
    (SR : HwReg X Z (Mem S) → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → SelectRead d s.1 s.2.1 s.2.2.2 z K x xi)
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ} (hσ : σ.PosSemidef) :
    flipCost B (hwReadKraus (.readH z upd)) (readPs SR) σ ≤
      ENNReal.ofReal (encWt B d K SR σ) + ENNReal.ofReal (readPs SR * σ).trace.re +
        2 * (ENNReal.ofReal (encWt B d K SR σ) * ENNReal.ofReal (readPs SR * σ).trace.re) ^
          (2⁻¹ : ℝ) := by
  have hout : ∀ s : HwReg X Z (Mem S), s ∉ B → s ∉ Bad d N := fun s hS h ↦ hS ((hB s).2 h)
  refine flipCost_readH_le B z upd (fun (m : Mem S) v ↦ (m.1, cwSel m.2 K x xi v)) SR
    (fun s ↦ encCwCount d (union s.2.1 s.1) K * 2 ^ 960) (fun s hs ↦ ⟨(hSR s hs).hd, (hSR s hs).hw⟩)
    hupd ?_ ?_ ?_ ?_ hσ
  · intro s u hs hS h
    exact not_mem_bad_read_keep (T := s.2.2.1) (hout s hS) (hSR s hs) u ((hB _).1 h)
  · intro s hs hS
    classical
    refine card_filter_le_of_imp (card_flip_readCw_le (T := s.2.2.1) (hout s hS) (hSR s hs))
      fun v ⟨u, hu⟩ ↦ ⟨u, (hB _).1 hu⟩
  · intro s u hs hS
    exact (hB _).2 (mem_bad_fill ((hB s).1 hS) (hSR s hs).hd u s.2.2.1 s.2.2.2 fun _ _ ht ↦ ht)
  · intro s u v hs hS
    refine (hB _).2 (mem_bad_fill ((hB s).1 hS) (hSR s hs).hd u s.2.2.1 (cwSel s.2.2.2 K x xi v)
      fun t y ht ↦ ?_)
    rcases cwSel_eq s.2.2.2 K x xi v with h | h
    · rw [h]
      exact ht
    · rw [h]
      exact sphTgt_select_mono (hSR s hs).hm ht

/-- `flipCost_selectRead_le` at a read port given as an equation. -/
theorem flipCost_readEq_le (B : Set (HwReg X Z (Mem S))) [DecidablePred (· ∈ B)]
    (hB : ∀ r, r ∈ B ↔ r ∈ Bad d N) {c : HwRead X Z (Mem S)} {z : Z} {t : TrialPt}
    {upd : Mem S → Option X → Mem S} (hc : c = .readH z upd)
    (hupd : ∀ m v, upd m (some v) = m ∨ upd m (some v) = (m.1, cwSel m.2 t.K t.x t.xi v))
    (SR : HwReg X Z (Mem S) → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → SelectRead d s.1 s.2.1 s.2.2.2 z t.K t.x t.xi)
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ} (hσ : σ.PosSemidef) :
    flipCost B (hwReadKraus c) (readPs SR) σ ≤
      ENNReal.ofReal (encWt B d t.K SR σ) + ENNReal.ofReal (readPs SR * σ).trace.re +
        2 * (ENNReal.ofReal (encWt B d t.K SR σ) * ENNReal.ofReal (readPs SR * σ).trace.re) ^
          (2⁻¹ : ℝ) := by
  subst hc
  exact flipCost_selectRead_le B hB z t.K t.x t.xi upd hupd SR hSR hσ

variable (updOf : TrialPt → Mem S → Option X → Mem S)

/-- **The flip cost of a read port, linearized**: on a selecting read port the codeword-selecting
read's bound (`flipCost_selectRead_le`), on the other read ports the flip terms off the empty cell,
with the cross terms split by `s`: at most `(1 + s) (E + ε + ε') + (1 + 1/s) p`. -/
theorem flipCost_le_ports (B : Set (HwReg X Z (Mem S))) [DecidablePred (· ∈ B)]
    (hB : ∀ r, r ∈ B ↔ r ∈ Bad d N)
    (hupd : ∀ t m v, updOf t m (some v) = m ∨
      updOf t m (some v) = (m.1, cwSel m.2 t.K t.x t.xi v))
    (c : HwRead X Z (Mem S)) {s : ℝ} (hs : 0 < s)
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ} (hσ : σ.PosSemidef) :
    flipCost B (hwReadKraus c) (PRof Prod.snd updOf d c) σ ≤
      ENNReal.ofReal (1 + s) * (encW Prod.snd updOf B d c σ + epsW Prod.snd updOf B d c σ) +
        ENNReal.ofReal (1 + s⁻¹) * massW Prod.snd updOf d c σ := by
  by_cases ht : IsTrial updOf c
  · simp only [encW, epsW, massW, ht, ↓reduceIte, add_zero]
    have hf := flipCost_readEq_le B hB (eq_readH_trialOf updOf ht) (hupd (trialOf updOf c).2)
      (trialSR Prod.snd updOf d c) (fun s hs ↦ trialSR_of_isTrial Prod.snd updOf ht hs) hσ
    exact hf.trans (cost_le_lin hs (encWt_nonneg B d _ _ hσ) (re_trace_readPs_nonneg _ hσ))
  · simp only [encW, epsW, massW, ht, ↓reduceIte, zero_add]
    exact cost_le_lin' hs (re_trace_readPs_nonneg _ hσ)

end lift

/-! ## Filling a `k`, `k'` cell by a read -/

section readBad

variable {Y M : Type} {π : Equiv.Perm (X × Z)} {out : X → Y}
  {tgt : Hw X Z → M → List X → Option Y} {G T N : ℕ}

open scoped Classical in
/-- **Filling a `k` cell by a read** of a target event, neither recorded nor hardwired: the
capacity-scale count of `card_targetBad_updateK_le` (the memory and the hardwired cells kept). -/
theorem card_flip_readK_hwTargetBad_le (hπ : PermGood π G) {D : DbReg X Z} {W : Hw X Z} {m : M}
    (hs : (D, W, m) ∉ HwTargetBad π out tgt N) (hT : N + dbGrade D ≤ T) {x : X}
    (hD : D.2.1 x = none) (hW : W.2.1 x = none) :
    #(univ.filter fun b : Z ↦
      ((D.1, Function.update D.2.1 x (some b), D.2.2), W, m) ∈ HwTargetBad π out tgt N) ≤
        (T + 1) * ((T + 1) * T + 2 * T) * G := by
  by_cases hN : dbGrade W ≤ N
  swap
  · rw [Finset.filter_false_of_mem fun b _ hb ↦ hN hb.1]
    simp
  have hU : union W D ∉ TargetBad π out (tgt W m) := fun h ↦ hs ⟨hN, h⟩
  have hx : (union W D).k x = none := by
    show (W.2.1 x).or (D.2.1 x) = none
    rw [hW, hD]
    rfl
  refine card_filter_le_of_imp (card_targetBad_updateK_le hπ hU
    ((size_unionK_le W D).trans (by omega)) ((size_unionK'_le W D).trans (by omega)) hx)
    fun b hb ↦ ?_
  have h2 : union W (D.1, Function.update D.2.1 x (some b), D.2.2) ∈
      TargetBad π out (tgt W m) := hb.2
  rwa [union_updateK W hW] at h2

open scoped Classical in
/-- **Filling a `k'` cell by a read** of a target event, neither recorded nor hardwired: the
capacity-scale count of `card_targetBad_updateK'_le`. -/
theorem card_flip_readK'_hwTargetBad_le (hπ : PermGood π G) {D : DbReg X Z} {W : Hw X Z} {m : M}
    (hs : (D, W, m) ∉ HwTargetBad π out tgt N) (hT : N + dbGrade D ≤ T) {x : X}
    (hD : D.2.2 x = none) (hW : W.2.2 x = none) :
    #(univ.filter fun b : Z ↦
      ((D.1, D.2.1, Function.update D.2.2 x (some b)), W, m) ∈ HwTargetBad π out tgt N) ≤
        (T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T := by
  by_cases hN : dbGrade W ≤ N
  swap
  · rw [Finset.filter_false_of_mem fun b _ hb ↦ hN hb.1]
    simp
  have hU : union W D ∉ TargetBad π out (tgt W m) := fun h ↦ hs ⟨hN, h⟩
  have hx : (union W D).k' x = none := by
    show (W.2.2 x).or (D.2.2 x) = none
    rw [hW, hD]
    rfl
  refine card_filter_le_of_imp (card_targetBad_updateK'_le hπ hU
    ((size_unionH_le W D).trans (by omega)) ((size_unionK_le W D).trans (by omega))
    ((size_unionK'_le W D).trans (by omega)) hx) fun b hb ↦ ?_
  have h2 : union W (D.1, D.2.1, Function.update D.2.2 x (some b)) ∈
      TargetBad π out (tgt W m) := hb.2
  rwa [union_updateK' W hW] at h2

variable {S : Type} {d : EvData}

open scoped Classical in
/-- **Filling a `k` cell by a read**, neither recorded nor hardwired: twice the capacity-scale
count (Struct and Enc, and coverage). -/
theorem card_flip_readK_bad_le (hπ : PermGood d.perm G) {D : DbReg X Z} {W : Hw X Z}
    {m : Mem S} (hs : (D, W, m) ∉ Bad d N) (hT : N + dbGrade D ≤ T) {x : X}
    (hD : D.2.1 x = none) (hW : W.2.1 x = none) :
    #(univ.filter fun b : Z ↦
      ((D.1, Function.update D.2.1 x (some b), D.2.2), W, m) ∈ Bad d N) ≤
        2 * ((T + 1) * ((T + 1) * T + 2 * T) * G) :=
  (card_filter_le_add fun _ h ↦ h).trans ((add_le_add
    (card_flip_readK_hwTargetBad_le hπ (fun h ↦ hs (.inl h)) hT hD hW)
    (card_flip_readK_hwTargetBad_le hπ (fun h ↦ hs (.inr h)) hT hD hW)).trans
      (two_mul _).symm.le)

open scoped Classical in
/-- **Filling a `k'` cell by a read**, neither recorded nor hardwired: twice the capacity-scale
count (Struct and Enc, and coverage). -/
theorem card_flip_readK'_bad_le (hπ : PermGood d.perm G) {D : DbReg X Z} {W : Hw X Z}
    {m : Mem S} (hs : (D, W, m) ∉ Bad d N) (hT : N + dbGrade D ≤ T) {x : X}
    (hD : D.2.2 x = none) (hW : W.2.2 x = none) :
    #(univ.filter fun b : Z ↦
      ((D.1, D.2.1, Function.update D.2.2 x (some b)), W, m) ∈ Bad d N) ≤
        2 * ((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T) :=
  (card_filter_le_add fun _ h ↦ h).trans ((add_le_add
    (card_flip_readK'_hwTargetBad_le hπ (fun h ↦ hs (.inl h)) hT hD hW)
    (card_flip_readK'_hwTargetBad_le hπ (fun h ↦ hs (.inr h)) hT hD hW)).trans
      (two_mul _).symm.le)

/-- **Filling an empty `k` cell keeps the event.** -/
theorem mem_bad_fillK {s : HwReg X Z (Mem S)} (hs : s ∈ Bad d N) {x : X}
    (hx : s.1.2.1 x = none) (b : Z) :
    ((s.1.1, Function.update s.1.2.1 x (some b), s.1.2.2), s.2.1, s.2.2) ∈ Bad d N := by
  rcases hs with h | h
  · exact .inl (mem_hwTargetBad_fillK h hx b)
  · exact .inr (mem_hwTargetBad_fillK h hx b)

/-- **Filling an empty `k'` cell keeps the event.** -/
theorem mem_bad_fillK' {s : HwReg X Z (Mem S)} (hs : s ∈ Bad d N) {x : X}
    (hx : s.1.2.2 x = none) (b : Z) :
    ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some b)), s.2.1, s.2.2) ∈ Bad d N := by
  rcases hs with h | h
  · exact .inl (mem_hwTargetBad_fillK' h hx b)
  · exact .inr (mem_hwTargetBad_fillK' h hx b)

end readBad

end Quantum.Sphincs.Assembly

end
