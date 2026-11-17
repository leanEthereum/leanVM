module

public import Quantum.StdModel.Qrom.CpreDrop

@[expose] public section

/-!
# The source invariant and the calls of the CPRE template

At the parameter `P` and the hidden values `θ`, the **source invariant** `SrcInv P θ` of a
register of runtime 2: every honest position whose source coordinate is revealed (in the memory
label) has its cell hardwired. A template keeps it when every reveal is followed by the programs
of the cells whose source it reveals before any sponge or read call (`HPend`, with the pending
cells): an opening reveals the sources of the cells from `μ` and programs them (`hPend_openT`),
the end's reveal reveals no position's source.

* `PendInv`, `revealCells`, `progCellH`, `HPend` and the steps (`stepPend_*`): as leanXMSS's QROM
  game (`Quantum.Qrom.Xmss.GameTCalls`), at the CPRE coordinates.
* `hPend_cpreT`: the template keeps the invariant (the decision's final reveal may leave cells
  pending); `forallQueries_cpreT`: Masses' `hinv` for any ports `Q` other than the program ports,
  from states with an empty memory label.
* **Calls** (`tCharge a b P`, `rCharge a b P`: `a` per sponge call, `b` per read at a step cell
  `stepCells ch P`): the reduction's classical algorithms are charged by the weight `redW P we`
  (`stepW P`, one per hash of a step cell, and `we` on the CPRE queries); `chg_realizeT_cpreT`:
  `b c₀ + (a n + b m k) + (b c₁ + b lenMax)` for setup, handler and output weights `c₀`, `m`,
  `c₁`, an adversary of `n` hash and `k` classical calls, and the decision's walk.
-/

open Matrix IPFunctor OracleComp OracleSpec
open scoped ENNReal Kronecker

universe u v w w₁

namespace Quantum.StdModel.Qrom.CpreQ

open Quantum Quantum.Qrom QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid Props HashSig
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec runtimeR realizeT revealThen progThen
  readLift readLiftQ RevealVals)

variable {Par Tw J Val Fn Out : Type} {Msg : Fn → Type} {ch : Chains Par Tw J Val}

/-! ## The pending invariant -/

section pending

/-- The source coordinate of a position. -/
def srcP (p : CPos ch) : CSrc ch :=
  srcOf p.1 p.2 p.2.isLt.le

/-- **The source invariant** at `P` and `θ`: a position whose source is revealed has its cell
hardwired. -/
def SrcInv (P : Par) (θ : (s : CSrc ch) → CD ch s)
    (r : HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)) : Prop :=
  ∀ p, srcP p ∈ r.2.2.1 → r.2.1.1 (cellOf P θ p) ≠ none

/-- **The source invariant with pending cells `C`.** -/
def PendInv (P : Par) (θ : (s : CSrc ch) → CD ch s) (C : Set HashDomain)
    (r : HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)) : Prop :=
  ∀ p, srcP p ∈ r.2.2.1 → r.2.1.1 (cellOf P θ p) ≠ none ∨ cellOf P θ p ∈ C

/-- The cells whose source a reveal of `T` reveals. -/
def revealCells (P : Par) (θ : (s : CSrc ch) → CD ch s) (T : Finset (CSrc ch)) :
    Set HashDomain :=
  {z | ∃ p, srcP p ∈ T ∧ cellOf P θ p = z}

/-- The `h`-cell a program port hardwires. -/
def progCellH : HwProg HashOutput HashDomain → Set HashDomain
  | .programH z _ => {z}
  | _ => ∅

variable {P : Par} {θ : (s : CSrc ch) → CD ch s}

theorem pendInv_mono {C C' : Set HashDomain} (h : C ⊆ C')
    {r : HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)} (hr : PendInv P θ C r) :
    PendInv P θ C' r :=
  fun p hp ↦ (hr p hp).imp_right fun hc ↦ h hc

theorem pendInv_of_eq {C : Set HashDomain}
    {r r' : HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)}
    (h1 : r'.2.1 = r.2.1) (h2 : r'.2.2.1 = r.2.2.1) (hr : PendInv P θ C r) :
    PendInv P θ C r' := by
  intro p hp
  rw [h1]
  exact hr p (h2 ▸ hp)

theorem pendInv_of_label_empty {C : Set HashDomain}
    {r : HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)} (h : r.2.2.1 = ∅) :
    PendInv P θ C r := by
  intro p hp
  rw [h] at hp
  exact absurd hp (Finset.notMem_empty _)

theorem progUpdate_ne_none (c : HwProg HashOutput HashDomain) (W : Hw HashOutput HashDomain)
    {z : HashDomain} (h : W.1 z ≠ none ∨ z ∈ progCellH c) : (progUpdate c W).1 z ≠ none := by
  cases c with
  | programH z' a =>
    rcases h with h | h
    · change Function.update W.1 z' (some a) z ≠ none
      by_cases hz : z = z'
      · subst hz
        rw [Function.update_self]
        exact Option.some_ne_none a
      · rw [Function.update_of_ne hz]
        exact h
    · rw [Set.mem_singleton_iff.mp h]
      change Function.update W.1 z' (some a) z' ≠ none
      rw [Function.update_self]
      exact Option.some_ne_none a
  | programK => exact h.resolve_right (Set.notMem_empty _)
  | programK' => exact h.resolve_right (Set.notMem_empty _)

theorem pendInv_prog {C : Set HashDomain} (c : HwProg HashOutput HashDomain)
    {r r' : HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)}
    (h : r'.2 = (progUpdate c r.2.1, r.2.2)) (hr : PendInv P θ C r) :
    PendInv P θ (C \ progCellH c) r' := by
  intro p hp
  rw [h] at hp ⊢
  rcases hr p hp with hc | hc
  · exact .inl (progUpdate_ne_none c _ (.inl hc))
  · by_cases hz : cellOf P θ p ∈ progCellH c
    · exact .inl (progUpdate_ne_none c _ (.inr hz))
    · exact .inr ⟨hc, hz⟩

theorem pendInv_reveal [DecidableEq J] {C : Set HashDomain} (T : Finset (CSrc ch))
    {r r' : HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)}
    (h : r'.2 = (r.2.1, (r.2.2.1 ∪ T, r.2.2.2))) (hr : PendInv P θ C r) :
    PendInv P θ (C ∪ revealCells P θ T) r' := by
  intro p hp
  rw [h] at hp ⊢
  rcases Finset.mem_union.1 hp with hp | hp
  · exact (hr p hp).imp_right Or.inl
  · exact .inr (.inr ⟨p, hp, rfl⟩)

theorem srcInv_of_pendInv {r : HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)}
    (h : PendInv P θ ∅ r) : SrcInv P θ r :=
  fun p hp ↦ (h p hp).resolve_right (Set.notMem_empty _)

end pending

/-! ## Templates that keep the source invariant

`HPend P θ y C C'`: run from states on the pending invariant `C`, the template `y` calls the
sponge, read and reveal ports with nothing pending, its reads keep the label, a program port leaves
the pending set, a reveal of `T` adds the cells whose source it reveals; it ends on `C'`. -/

section hp

variable {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- A read port whose memory update keeps the memory label. -/
def LabKeepQ : HwRead HashOutput HashDomain (Finset (CSrc ch) × JMem) → Prop
  | .readH _ u => ∀ m o, (u m o).1 = m.1
  | .readK _ u => ∀ m o, (u m o).1 = m.1
  | .readK' _ u => ∀ m o, (u m o).1 = m.1

theorem labKeepQ_liftRead (c : HwRead HashOutput HashDomain JMem) :
    LabKeepQ (ch := ch) (Quantum.Xmss.Assembly.liftRead (S := CSrc ch) c) := by
  cases c <;> intro _ _ <;> rfl

/-- The condition of `HPend` on the pending set before a call. -/
def portPreQ : (TSpec ch).Port → Set HashDomain → Prop
  | .inl (.inl (.inl _)), C => C = ∅
  | .inl (.inl (.inr c)), C => C = ∅ ∧ LabKeepQ c.1
  | .inl (.inr _), _ => True
  | .inr _, C => C = ∅

/-- The pending set after a call. -/
def portPostQ (P : Par) (θ : (s : CSrc ch) → CD ch s) :
    (TSpec ch).Port → Set HashDomain → Set HashDomain
  | .inl (.inl (.inl _)), C => C
  | .inl (.inl (.inr _)), C => C
  | .inl (.inr p), C => C \ progCellH (p.1.realize θ)
  | .inr T, C => C ∪ revealCells P θ T

/-- The condition before a command. -/
def cmdPreQ {A : QReg} : QuantumComp.Cmd L (TSpec ch) A → Set HashDomain → Prop
  | .prim _, _ => True
  | .query i _ _, C => portPreQ i C

/-- The pending set after a command. -/
def cmdPostQ (P : Par) (θ : (s : CSrc ch) → CD ch s) {A : QReg} :
    QuantumComp.Cmd L (TSpec ch) A → Set HashDomain → Set HashDomain
  | .prim _, C => C
  | .query i _ _, C => portPostQ P θ i C

/-- **A template that keeps the source invariant**, from the pending set `C` to `C'`. -/
def HPend (P : Par) (θ : (s : CSrc ch) → CD ch s) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (TSpec ch)) Ω A → Set HashDomain →
      Set HashDomain → Prop
  | _, .pure _, C, C' => C ⊆ C'
  | _, .liftBind c next, C, C' => cmdPreQ c C ∧ ∀ b, HPend P θ (next b) (cmdPostQ P θ c C) C'

theorem cmdPreQ_anti {A : QReg} (c : QuantumComp.Cmd L (TSpec ch) A) {C D : Set HashDomain}
    (hD : D ⊆ C) (h : cmdPreQ c C) : cmdPreQ c D := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)
  · exact ⟨Set.subset_empty_iff.1 (h.1 ▸ hD), h.2⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)

theorem cmdPostQ_mono (P : Par) (θ : (s : CSrc ch) → CD ch s) {A : QReg}
    (c : QuantumComp.Cmd L (TSpec ch) A) {C D : Set HashDomain} (hD : D ⊆ C) :
    cmdPostQ P θ c D ⊆ cmdPostQ P θ c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · exact hD
  · exact hD
  · exact hD
  · exact Set.sdiff_subset_sdiff_left hD
  · exact Set.union_subset_union_left _ hD

variable (P : Par) (θ : (s : CSrc ch) → CD ch s)

theorem hPend_mono {A : QReg} (y : IFreeM (QuantumComp.toIPFunctor L (TSpec ch)) Ω A)
    {C C' D D' : Set HashDomain} (hy : HPend P θ y C C') (hD : D ⊆ C) (hD' : C' ⊆ D') :
    HPend P θ y D D' := by
  induction y using IFreeM.inductionOn generalizing C D with
  | pure _ _ => exact hD.trans (hy.trans hD')
  | liftBind _ c next ih =>
    exact ⟨cmdPreQ_anti c hD hy.1, fun b ↦ ih b (hy.2 b) (cmdPostQ_mono P θ c hD)⟩

theorem hPend_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor L (TSpec ch)) Ω A) (C C' : Set HashDomain) :
    HPend P θ (e ▸ y) C C' ↔ HPend P θ y C C' := by
  subst e
  rfl

theorem hPend_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor L (TSpec ch)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor L (TSpec ch)) Y u)
    {C D C' : Set HashDomain} (hx : HPend P θ x C D) (hg : ∀ u a, HPend P θ (g u a) D C') :
    HPend P θ (x.bind g) C C' := by
  induction x using IFreeM.inductionOn generalizing C with
  | pure _ a => exact hPend_mono P θ _ (hg _ a) hx subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem hPend₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L (TSpec ch) A B α) (g : α → QuantumComp₂ L (TSpec ch) B B' β)
    {C D C' : Set HashDomain} (hx : HPend P θ x C D) (hg : ∀ a, HPend P θ (g a) D C') :
    HPend P θ (x.bind g) C C' := by
  refine hPend_bind P θ x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

/-- **Runtime 1's programs keep the invariant**: their sponge and read ports (the reads lifted,
keeping the label) leave nothing pending. -/
theorem hPend_readLift {A : QReg} (y : QuantumComp L (hwReadSpec HashOutput HashDomain JMem) Ω A) :
    HPend P θ (readLift (goodC (ch := ch)) y) ∅ ∅ := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind _ c next ih =>
    show HPend P θ (IFreeM.mapLens (Quantum.Xmss.Assembly.readLens goodC)
      (IFreeM.liftBind c next)) ∅ ∅
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨rfl, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨⟨rfl, labKeepQ_liftRead c⟩, fun b ↦ ?_⟩
      dsimp only
      exact ih _

theorem hPend_act {A B : QReg} {α : Type} (p : SubInstrument A B α) (C : Set HashDomain) :
    HPend P θ (QComp.act (spec := TSpec ch) p) C C :=
  ⟨trivial, fun _ ↦ subset_rfl⟩

/-- A reveal with nothing pending makes the cells whose source it reveals pending. -/
theorem hPend_revealThen {B B' : QReg} {α : Type} (T : Finset (CSrc ch))
    (k : RevealVals (CD ch) T × (Finset (CSrc ch) × JMem) → QComp (TSpec ch) B B' α)
    {C' : Set HashDomain} (hk : ∀ r, HPend P θ (k r) (revealCells P θ T) C') :
    HPend P θ (revealThen goodC T k) ∅ C' :=
  ⟨rfl, fun r ↦ hPend₂_bind P θ _ _ (hPend_act P θ _ _) fun _ ↦
    hPend_mono P θ _ (hk r.down) (Set.empty_union _).le subset_rfl⟩

theorem hPend_progThen {B B' : QReg} {α : Type}
    (p : LazyProg HashOutput HashDomain (CSrc ch) (CD ch)) (hp : goodC p)
    (k : QComp (TSpec ch) B B' α) {C C' : Set HashDomain}
    (hk : HPend P θ k (C \ progCellH (p.realize θ)) C') : HPend P θ (progThen p hp k) C C' :=
  ⟨trivial, fun _ ↦ hPend₂_bind P θ _ _ (hPend_act P θ _ _) fun _ ↦ hk⟩

theorem hPend_map {B C : QReg} {α β : Type} (x : QComp (TSpec ch) B C α) (f : α → β)
    {D D' : Set HashDomain} (hx : HPend P θ x D D') : HPend P θ (x.map f) D D' := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact hPend₂_bind P θ _ _ hx fun _ ↦ subset_rfl

end hp

/-! ## The template's pieces keep the invariant -/

section pieces

/-- The honest cells of chain `j` from position `ν` upward. -/
def cellsFrom (P : Par) (θ : (s : CSrc ch) → CD ch s) (j : J) (ν : ℕ) : Set HashDomain :=
  {z | ∃ p : CPos ch, (p.1 = j ∧ ν ≤ p.2.val) ∧ cellOf P θ p = z}

theorem srcP_eq_inl {p : CPos ch} {j : J} (h : srcP p = .inl j) : p.1 = j ∧ p.2.val = 0 := by
  rcases p with ⟨j', ⟨_ | ν, hν⟩⟩
  · exact ⟨Sum.inl.inj h, rfl⟩
  · cases h

theorem srcP_eq_inr {p q : CPos ch} (h : srcP p = .inr q) :
    p.1 = q.1 ∧ p.2.val = q.2.val + 1 := by
  rcases p with ⟨j', ⟨_ | ν, hν⟩⟩
  · cases h
  · cases h
    exact ⟨rfl, rfl⟩

theorem revealCells_openSet_subset [Fintype J] [DecidableEq J] (P : Par)
    (θ : (s : CSrc ch) → CD ch s) (j : J) (μ : ℕ) :
    revealCells P θ (openSet ch j μ) ⊆ cellsFrom P θ j μ := by
  rintro z ⟨p, hp, rfl⟩
  refine ⟨p, ?_, rfl⟩
  simp only [openSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hp
  rcases hp with hp | ⟨q, ⟨hq1, hq2⟩, hq⟩
  · split_ifs at hp with hμ
    · rw [Finset.mem_singleton] at hp
      cases μ with
      | zero =>
        obtain ⟨h1, h2⟩ := srcP_eq_inl hp
        exact ⟨h1, by omega⟩
      | succ μ =>
        obtain ⟨h1, h2⟩ := srcP_eq_inr hp
        exact ⟨h1, by simp only at h2; omega⟩
    · simp at hp
  · obtain ⟨h1, h2⟩ := srcP_eq_inr hq.symm
    exact ⟨h1.trans hq1, by omega⟩

theorem val_lt_len {p : CPos ch} {j : J} (h : p.1 = j) : p.2.val < ch.len j := by
  rcases p with ⟨j', ν, hν⟩
  subst h
  exact hν

theorem srcP_ne_srcOf_ge {p : CPos ch} {j : J} :
    ∀ (n : ℕ) (h : n ≤ ch.len j), ch.len j ≤ n → srcP p ≠ srcOf j n h
  | 0, _, hle, he => by
    obtain ⟨h1, h2⟩ := srcP_eq_inl he
    have hlt := val_lt_len h1
    omega
  | n + 1, h, hle, he => by
    obtain ⟨h1, h2⟩ := srcP_eq_inr he
    have hlt := val_lt_len h1
    simp only at h2 hlt
    omega

theorem revealCells_endSet (P : Par) (θ : (s : CSrc ch) → CD ch s) (j : J) :
    revealCells P θ (endSet ch j) ⊆ ∅ := by
  rintro z ⟨p, hp, rfl⟩
  rw [endSet, Finset.mem_singleton] at hp
  exact srcP_ne_srcOf_ge (ch.len j) le_rfl le_rfl hp

variable [Fintype J] [DecidableEq J] [Inhabited Val] (P : Par) (θ : (s : CSrc ch) → CD ch s)

omit [Fintype J] in
theorem hPend_progFrom (B : QReg) (j : J) :
    ∀ ν C, HPend P θ (progFrom (ch := ch) P B j ν) C (C \ cellsFrom P θ j ν) := by
  intro ν
  induction h : ch.len j - ν generalizing ν with
  | zero =>
    intro C
    rw [progFrom, dite_eq_right (by omega)]
    rintro z hz
    refine ⟨hz, ?_⟩
    rintro ⟨p, ⟨hj, hle⟩, -⟩
    have hlt := val_lt_len hj
    omega
  | succ n ih =>
    intro C
    have hν : ν < ch.len j := by omega
    rw [progFrom, dite_eq_left hν]
    refine hPend_progThen P θ _ trivial _
      (hPend_mono P θ _ (ih (ν + 1) (by omega) _) subset_rfl ?_)
    rintro z ⟨⟨hz, hne⟩, hn⟩
    refine ⟨hz, ?_⟩
    rintro ⟨p, ⟨hj, hle⟩, rfl⟩
    rcases Nat.eq_or_lt_of_le hle with he | hlt
    · apply hne
      have hp : p = ⟨j, ⟨ν, hν⟩⟩ := by
        rcases p with ⟨j', ν', hν'⟩
        simp only at hj he
        subst hj
        subst he
        rfl
      rw [realize_progP, hp]
      exact Set.mem_singleton _
    · exact hn ⟨p, ⟨hj, hlt⟩, rfl⟩

theorem hPend_openT {α : Type} (B : QReg) (j : J) (μ : ℕ)
    (k : RevealVals (CD ch) (openSet ch j μ) → QComp (TSpec ch) B B α)
    (hk : ∀ w, HPend P θ (k w) ∅ ∅) : HPend P θ (openT P B j μ k) ∅ ∅ :=
  hPend_revealThen P θ _ _ fun _ ↦ hPend₂_bind P θ _ _ (hPend_progFrom P θ B j μ _) fun _ ↦
    hPend_mono P θ _ (hk _) (fun _ hz ↦ absurd (revealCells_openSet_subset P θ j μ hz.1) hz.2)
      subset_rfl

omit [Fintype J] [DecidableEq J] [Inhabited Val] in
theorem hPend_keepReads {α : Type} (B : QReg) (oa : OracleComp romWorld.Oracles α) :
    HPend P θ (keepReads (ch := ch) B oa) ∅ ∅ :=
  hPend_readLift P θ _

theorem hPend_ansT (C : TwColl Par Tw Fn Msg Out) (B : QReg) (q : CpreQuery J Tw Fn Msg) :
    HPend P θ (ansT (ch := ch) C P B q) ∅ ∅ := by
  cases q with
  | value j μ =>
    show HPend P θ (valueT P B j μ) ∅ ∅
    unfold valueT
    split_ifs
    · exact hPend_openT P θ B j μ _ fun _ ↦ subset_rfl
    · exact hPend_revealThen P θ _ _ fun _ ↦ revealCells_endSet P θ j
  | eval l t m =>
    show HPend P θ (evalT C P B l t m) ∅ ∅
    unfold evalT
    by_cases h : ch.IsStepTweak t
    · rw [dite_eq_left h]
      exact hPend_openT P θ B _ 0 _ fun _ ↦ hPend_keepReads P θ _ _
    · rw [dite_eq_right h]
      exact hPend_keepReads P θ _ _
  | reveal => exact subset_rfl

theorem hPend_tImplRun {α : Type} (C : TwColl Par Tw Fn Msg Out) (B : QReg)
    (x : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) α)
    (log : QueryLog (CQ Par Tw J Val Fn Msg Out)) :
    HPend P θ ((simulateQ (tImpl (ch := ch) C P B) x).run log) ∅ ∅ := by
  induction x using OracleComp.inductionOn generalizing log with
  | pure a => exact subset_rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with i | q'
    · change HPend P θ (QuantumComp₂.bind ((readLiftQ goodC (toReads updC (mixImpl .red B i))).map
          fun a ↦ (a, log)) fun p ↦ (simulateQ (tImpl (ch := ch) C P B) (k p.1)).run p.2) ∅ ∅
      exact hPend₂_bind P θ _ _ (hPend_map P θ _ _ (hPend_readLift P θ _)) fun _ ↦ ih _ _
    · change HPend P θ (QuantumComp₂.bind ((ansT C P B q').map fun a ↦ (a, log ++ [⟨q', a⟩]))
          fun p ↦ (simulateQ (tImpl (ch := ch) C P B) (k p.1)).run p.2) ∅ ∅
      exact hPend₂_bind P θ _ _ (hPend_map P θ _ _ (hPend_ansT P θ C B q')) fun _ ↦ ih _ _

theorem hPend_tRun {Q St : Type} {R : OracleSpec.{0, 0} Q} {X Y : QReg → Type}
    (C : TwColl Par Tw Fn Msg Out) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (leaf : ∀ u, X u → St × QueryLog (CQ Par Tw J Val Fn Msg Out) → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A)
    (s : St × QueryLog (CQ Par Tw J Val Fn Msg Out)) :
    HPend P θ (tRun (ch := ch) C P σ leaf x s) ∅ ∅ := by
  induction x using IFreeM.inductionOn generalizing s with
  | pure _ _ => rw [tRun]; exact subset_rfl
  | liftBind _ c next ih =>
    rcases c with o | ⟨p | q, E, ℓ⟩
    · rw [tRun]
      refine hPend_bind P θ _ _ (hPend_readLift P θ _) fun _ b ↦ ?_
      obtain ⟨b, e⟩ := b
      subst e
      exact ih b s
    · rw [tRun]
      refine hPend_bind P θ _ _ (hPend_readLift P θ _) fun _ b ↦ ?_
      obtain ⟨b, e⟩ := b
      subst e
      exact ih b s
    · rw [tRun]
      refine hPend_bind P θ _ _ (hPend₂_bind P θ _ _ (hPend_act P θ _ _) fun _ ↦
        hPend_map P θ _ _ (hPend_tImplRun P θ C _ _ _)) fun _ l ↦ ?_
      obtain ⟨e, l⟩ := l
      subst e
      exact ih _ _

omit [Fintype J] in
theorem hPend_judgeT (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)) (out : J × ℕ × Val) :
    HPend P θ (judgeT (ch := ch) P log out) ∅ Set.univ :=
  hPend₂_bind P θ _ _ (hPend_readLift P θ _) fun _ ↦
    hPend_revealThen P θ _ _ fun _ ↦ Set.subset_univ _

/-- **The template game keeps the source invariant**: it starts with nothing pending; only the
decision's reveal, after the last call, may leave cells pending. -/
theorem hPend_cpreT {Q St S0 F : Type} {R : OracleSpec.{0, 0} Q} (C : TwColl Par Tw Fn Msg Out)
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    HPend P θ (cpreT (ch := ch) C P pre adv st0 σ post) ∅ Set.univ :=
  hPend₂_bind P θ _ _ (hPend_tImplRun P θ C _ pre []) fun _ ↦
    hPend₂_bind P θ _ _ (hPend_tRun P θ C σ _ _ _) fun _ ↦
      hPend₂_bind P θ _ _ (hPend_tImplRun P θ C _ _ _) fun _ ↦ hPend_judgeT P θ _ _

end pieces

/-! ## The steps of `runtimeR` on the pending invariant -/

section steps

/-- The register's classical part has decidable equality (instance search does not find the
product on its own). -/
instance instDecidableEqHwMem [DecidableEq J] :
    DecidableEq (Hw HashOutput HashDomain × Finset (CSrc ch) × JMem) :=
  instDecidableEqProd

variable [Fintype J] [DecidableEq J] {P : Par} {θ : (s : CSrc ch) → CD ch s}

omit [Fintype J] in
/-- A read port keeping the label keeps the hardwired cells and the label. -/
theorem hwReadKraus_ne_zero_keepQ {c : HwRead HashOutput HashDomain (Finset (CSrc ch) × JMem)}
    (hc : LabKeepQ c) (r : c.Result) {u u' : Unit}
    {s s' : HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)}
    (h : hwReadKraus c r (u', s') (u, s) ≠ 0) : s'.2.1 = s.2.1 ∧ s'.2.2.1 = s.2.2.1 := by
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact ⟨rfl, (hc _ _).trans (congrArg Prod.fst hp).symm⟩
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact ⟨rfl, (hc _ _).trans (congrArg Prod.fst hp).symm⟩
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact ⟨rfl, (hc _ _).trans (congrArg Prod.fst hp).symm⟩

variable (P θ) in
/-- A step of `runtimeR` at port `i` carries support on the pending invariant `C` to support on
the pending invariant `C'`. -/
def StepPend (m₀ : Finset (CSrc ch) × JMem)
    (i : (recHwSpec HashOutput HashDomain (CSrc ch) JMem).Port) (C C' : Set HashDomain) : Prop :=
  ∀ r σ, QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain (CSrc ch) JMem).In i ×
      (runtimeR m₀).D ↦ m.2) {s | PendInv P θ C s} σ →
    QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain (CSrc ch) JMem).Out i ×
      (runtimeR m₀).D ↦ m.2) {s | PendInv P θ C' s} (((runtimeR m₀).step i).branch r σ)

theorem stepPend_sponge (m₀ : Finset (CSrc ch) × JMem) (i : SpongePort) (C : Set HashDomain) :
    StepPend P θ m₀ (.inl (.inl (.inl i))) C C := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired HashOutput HashDomain
        (hwEmpty HashOutput HashDomain) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty HashOutput HashDomain) m₀ i
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty HashOutput HashDomain) m₀ i q.1 q'.1
      q.2 q'.2 hK
    exact pendInv_of_eq (congrArg Prod.fst he) (congrArg (fun t ↦ t.2.1) he) hq

theorem stepPend_read (m₀ : Finset (CSrc ch) × JMem)
    (c : {c : HwRead HashOutput HashDomain (Finset (CSrc ch) × JMem) //
      ReadMono (Quantum.Xmss.Assembly.memLab HashOutput HashDomain (CSrc ch) JMem) c})
    (hc : LabKeepQ c.1) (C : Set HashDomain) : StepPend P θ m₀ (.inl (.inl (.inr c.1))) C C := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain) m₀ c.1
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    obtain ⟨h1, h2⟩ := hwReadKraus_ne_zero_keepQ hc r (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK
    exact pendInv_of_eq h1 h2 hq

theorem stepPend_prog (m₀ : Finset (CSrc ch) × JMem) (c : HwProg HashOutput HashDomain)
    (C : Set HashDomain) : StepPend P θ m₀ (.inl (.inr c)) C (C \ progCellH c) := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty HashOutput HashDomain) m₀ c
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    pendInv_prog c (hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK) hq

theorem stepPend_rec (m₀ : Finset (CSrc ch) × JMem) (T : Finset (CSrc ch)) (C : Set HashDomain) :
    StepPend P θ m₀ (.inr T) C (C ∪ revealCells P θ T) := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    pendInv_reveal T (Quantum.Xmss.Assembly.recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK) hq

/-- An operator supported on the invariant presents, at a call, no diagonal mass outside it. -/
theorem relabel_diag_eq_zero_srcInv (m₀ : Finset (CSrc ch) × JMem) {A : QReg}
    {i : (recHwSpec HashOutput HashDomain (CSrc ch) JMem).Port} (E : QReg)
    (ℓ : A ≃ (recHwSpec HashOutput HashDomain (CSrc ch) JMem).In i × E)
    {ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | PendInv P θ ∅ s} ρ)
    (a : ((recHwSpec HashOutput HashDomain (CSrc ch) JMem).In i × (runtimeR m₀).D) × E)
    (ha : ¬SrcInv P θ a.1.2) :
    (SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).branch () ρ a a =
      0 := by
  by_contra h
  have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).imp
    (q' := fun m : ((recHwSpec HashOutput HashDomain (CSrc ch) JMem).In i × (runtimeR m₀).D) × E ↦
      m.1.2)
    (S' := {s | PendInv P θ ∅ s}) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  exact ha (srcInv_of_pendInv (h₁ a a h).1)

end steps

/-! ## The invariant at the calls (`hinv`) -/

section hinv

variable [Fintype J] [DecidableEq J] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- One call of a realized program on the pending invariant. -/
theorem forallQueries_queryBind_of_stepPend
    {Q : (recHwSpec HashOutput HashDomain (CSrc ch) JMem).Port → Prop}
    (m₀ : Finset (CSrc ch) × JMem) (I : L.Interp) (P : Par) (θ : (s : CSrc ch) → CD ch s)
    {A : QReg} (i : (recHwSpec HashOutput HashDomain (CSrc ch) JMem).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec HashOutput HashDomain (CSrc ch) JMem).In i × E)
    (k' : (recHwSpec HashOutput HashDomain (CSrc ch) JMem).Result i →
      QuantumComp L (recHwSpec HashOutput HashDomain (CSrc ch) JMem) Ω
        (QReg.of ((recHwSpec HashOutput HashDomain (CSrc ch) JMem).Out i × E)))
    {C C' : Set HashDomain} (hpre : Q i → C = ∅) (hstep : StepPend P θ m₀ i C C')
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of
        ((recHwSpec HashOutput HashDomain (CSrc ch) JMem).Out i × E) × (runtimeR m₀).D ↦ m.2)
        {s | PendInv P θ C' s} ρ' →
      (runtimeR m₀).ForallQueries I
        (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInv P θ)) (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | PendInv P θ C s} ρ) :
    (runtimeR m₀).ForallQueries I (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInv P θ))
      (QuantumComp.queryBind i E ℓ k') ρ :=
  ⟨fun hq a ha ↦ relabel_diag_eq_zero_srcInv (i := i) m₀ E ℓ (hpre hq ▸ hρ) a ha, fun r ↦
    hk r _ (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) i r (hstep r) E ℓ hρ)⟩

/-- **The realized program of a template keeping the source invariant presents, at every call of
the ports `Q` (no program port), only states of the invariant.** -/
theorem forallQueries_of_hPend
    {Q : (recHwSpec HashOutput HashDomain (CSrc ch) JMem).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (m₀ : Finset (CSrc ch) × JMem) (I : L.Interp) (P : Par)
    (θ : (s : CSrc ch) → CD ch s) {A : QReg} (y : QuantumComp L (TSpec ch) Ω A) :
    ∀ C C', HPend P θ y C C' → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | PendInv P θ C s} ρ →
      (runtimeR m₀).ForallQueries I
        (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInv P θ)) (realizeT θ y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro C C' hy ρ hρ b
    exact ih b C C' (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepPend m₀ I P θ (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT θ (k r)) (fun _ ↦ hy.1) (stepPend_sponge m₀ i C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepPend m₀ I P θ (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT θ (k r)) (fun _ ↦ hy.1.1) (stepPend_read m₀ c hy.1.2 C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepPend m₀ I P θ
          (.inl (.inr ((LazyProg.programH T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepPend_prog m₀ _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepPend m₀ I P θ
          (.inl (.inr ((LazyProg.programK T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepPend_prog m₀ _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepPend m₀ I P θ
          (.inl (.inr ((LazyProg.programK' T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepPend_prog m₀ _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepPend m₀ I P θ (.inr T) E ℓ
        (fun m ↦ realizeT θ (k (restrictTo T θ, m))) (fun _ ↦ hy.1) (stepPend_rec m₀ T C)
        (fun m ↦ ih (restrictTo T θ, m) _ C' (hy.2 (ULift.up (restrictTo T θ, m)))) ρ hρ

/-- An initial state whose memory label is empty. -/
theorem querySupportedOn_initQ (m₀ : Finset (CSrc ch) × JMem) (hm₀ : m₀.1 = ∅) {A : QReg}
    (σ : Matrix A A ℂ) :
    QuerySupportedOn
      (fun a : A × QReg.of (HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)) ↦ a.2.2.2.1)
      {∅} (σ ⊗ₖ (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix) := by
  intro a b h
  change (σ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
    hwEmpty HashOutput HashDomain, m₀) :
      HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem))).matrix) a b ≠ 0 at h
  rw [SubState.matrix_basis, kroneckerMap_apply] at h
  have h' := right_ne_zero_of_mul h
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · show a.2.2.2.1 ∈ ({∅} : Set (Finset (CSrc ch))) ∧ b.2.2.2.1 ∈ ({∅} : Set (Finset (CSrc ch)))
    rw [← he.1, ← he.2]
    exact ⟨hm₀, hm₀⟩
  · exact absurd rfl h'

/-- **`hinv` for the realized CPRE template**: from states with an empty memory label, every call
of ports `Q` that are not program ports sees the source invariant. -/
theorem forallQueries_cpreT [Inhabited Val]
    {Q : (recHwSpec HashOutput HashDomain (CSrc ch) JMem).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (m₀ : Finset (CSrc ch) × JMem) {Q' St S0 F : Type}
    {R : OracleSpec.{0, 0} Q'} (C : TwColl Par Tw Fn Msg Out) (P : Par)
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) (θ : (s : CSrc ch) → CD ch s)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)))
      (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem))) ℂ)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit ×
      QReg.of (HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)) ↦ a.2.2.2.1) {∅} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInv P θ))
        (realizeT θ (cpreT (ch := ch) C P pre adv st0 σ post)) ρ :=
  forallQueries_of_hPend hQ m₀ _ P θ _ ∅ Set.univ (hPend_cpreT P θ C pre adv st0 σ post) ρ
    (hρ.imp fun _ ha ↦ pendInv_of_label_empty (Set.mem_singleton_iff.1 ha))

end hinv

/-! ## The calls of the realized template

Two counts, both by `tCharge a b P` (`a` per sponge call, `b` per read at a step cell, programs
and reveals free): the sponge calls are the adversary's hash calls; the reads at step cells are
charged on the reduction's classical algorithms by the weight `redW P we` (`stepW P` on the
world's queries: one per hash of a step cell; `we` on the CPRE queries, bounding the step-cell
reads of the challenger's evaluations), plus the decision's walk, at most `lenMax ch` reads. -/

section charges

variable (ch) in
/-- **The step cells at `P`**: the codes of the chain step inputs at the step tweaks. -/
def stepCells (P : Par) : Set HashDomain :=
  {z | ∃ j ν x, ν < ch.len j ∧ z = (encodeInput (ch.step.layout () P (ch.tweak j ν) x)).getD 0}

theorem cellOf_mem_stepCells (P : Par) (θ : (s : CSrc ch) → CD ch s) (p : CPos ch) :
    cellOf P θ p ∈ stepCells ch P :=
  ⟨p.1, p.2.val, cval θ p.1 p.2, p.2.isLt, rfl⟩

open Classical in
/-- A read at a step cell. -/
noncomputable def stepRead {M' : Type} (P : Par) : HwRead HashOutput HashDomain M' → Bool
  | .readH z _ => decide (z ∈ stepCells ch P)
  | _ => false

theorem stepRead_liftRead (P : Par) (c : HwRead HashOutput HashDomain JMem) :
    stepRead (ch := ch) P (Quantum.Xmss.Assembly.liftRead (S := CSrc ch) c) =
      stepRead (ch := ch) P c := by
  cases c <;> rfl

open Classical in
/-- The weight of the world's queries: one per hash of a step cell. -/
noncomputable def stepW (P : Par) : RomOracles.Domain → ℕ
  | .inl _ => 0
  | .inr z => if z ∈ stepCells ch P then 1 else 0

/-- **The weight of a reduction's queries**: `stepW P` on the world's, `we` on the CPRE ports. -/
noncomputable def redW (P : Par) (we : CpreQuery J Tw Fn Msg → ℕ) :
    RomOracles.Domain ⊕ CpreQuery J Tw Fn Msg → ℕ
  | .inl i => stepW (ch := ch) P i
  | .inr q => we q

variable (ch) in
/-- The longest chain. -/
def lenMax [Fintype J] : ℕ :=
  Finset.univ.sup ch.len

/-- The charge on the template ports: `a` per sponge call, `b` per read at a step cell. -/
noncomputable def tCharge (a b : ℕ) (P : Par) : (TSpec ch).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr r)) => if stepRead (ch := ch) P r.1 then b else 0
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The same charge on runtime 2 with record ports. -/
noncomputable def rCharge (a b : ℕ) (P : Par) :
    (recHwSpec HashOutput HashDomain (CSrc ch) JMem).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr r)) => if stepRead (ch := ch) P r then b else 0
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The charge on runtime 1's read programs. -/
noncomputable def rdCharge (a b : ℕ) (P : Par) : (hwReadSpec HashOutput HashDomain JMem).Port → ℕ
  | .inl _ => a
  | .inr r => if stepRead (ch := ch) P r then b else 0

/-- The charge on mixed programs: `a` per hash call, `b` per tagged hash of a step cell. -/
noncomputable def mixCharge (a b : ℕ) (P : Par) : (MixSpec Caller).Port → ℕ
  | .hash _ => a
  | .call (_, i) => b * stepW (ch := ch) P i

/-- **The reads at step cells**: the ports of the read mass. -/
noncomputable def readStepQ (P : Par) : (recHwSpec HashOutput HashDomain (CSrc ch) JMem).Port → Bool
  | .inl (.inl (.inr r)) => stepRead (ch := ch) P r
  | _ => false

/-- The charge of an adversary's commands: `α` per hash call, `β` per classical call. -/
noncomputable def advCharge {Q : Type} {R : OracleSpec.{0, 0} Q} (α β : ℕ) (A : QReg)
    (cmd : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec romWorld.spec R) A) : ℕ :=
  α * Quantum.StdModel.cmdCharge Quantum.StdModel.hashCharge A cmd +
    β * Quantum.StdModel.cmdCharge Quantum.StdModel.callCharge A cmd

theorem mul_add_sub_le (b : ℕ) {x n : ℕ} (h : x ≤ n) : b * x + b * (n - x) ≤ b * n := by
  rw [← Nat.mul_add, Nat.add_sub_cancel' h]

/-- One step of a charge bound on a command tree: normalize the head, then charge the command. -/
local macro "chg_step" : tactic => `(tactic| (
  (conv => arg 1; whnf);
  refine (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
    ⟨by first
      | exact Nat.zero_le _
      | exact le_rfl
      | (simp only [portCharge, rdCharge, stepRead, Quantum.StdModel.cmdCharge, mixCharge, stepW,
          Nat.sub_zero]
         split_ifs <;> simp_all), fun _ ↦ ?_⟩))

variable {L : LocalSig.{u, v}} {Ω : QReg → Type w} (a b : ℕ) (P : Par)

/-- **The read substitution charges a tagged call by the step cell it reads.** -/
theorem chg_readSub (upd : Caller → HashDomain → JMem → Option HashOutput → JMem) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (MixSpec Caller) A) :
    IFreeM.IsChargeBound (readSub upd A c) (portCharge (rdCharge (ch := ch) a b P))
      (Quantum.StdModel.cmdCharge (mixCharge (ch := ch) a b P) A c) := by
  rcases c with o | ⟨p | ⟨tag, n | z⟩, E, ℓ⟩
  · chg_step
    exact IFreeM.isChargeBound_pure _ _
  · chg_step
    exact IFreeM.isChargeBound_pure _ _
  · chg_step
    chg_step
    exact IFreeM.isChargeBound_pure _ _
  · chg_step
    chg_step
    chg_step
    exact IFreeM.isChargeBound_pure _ _

theorem chg_toReads (upd : Caller → HashDomain → JMem → Option HashOutput → JMem) {A B : QReg}
    {α : Type} {x : QComp (MixSpec Caller) A B α} {n : ℕ}
    (hx : IFreeM.IsChargeBound x (Quantum.StdModel.cmdCharge (mixCharge (ch := ch) a b P)) n) :
    IFreeM.IsChargeBound (toReads upd x) (portCharge (rdCharge (ch := ch) a b P)) n :=
  IFreeM.IsChargeBound.substitute _ (chg_readSub a b P upd) hx

theorem chg_mixImpl (c : Caller) (B : QReg) (i : RomOracles.Domain) :
    IFreeM.IsChargeBound (mixImpl c B i) (Quantum.StdModel.cmdCharge (mixCharge (ch := ch) a b P))
      (b * stepW (ch := ch) P i) := by
  unfold mixImpl callQ
  exact (FreeM₂.isChargeBound_bind (isChargeBound_query₂ (S := romWorld.spec)
    (mixCharge (ch := ch) a b P) (.call (c, i)) B (callSplit romWorld (tagSpec Caller) (c, i) B))
    fun _ ↦ FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (isChargeBound_act _ _ 0) fun _ ↦
      IFreeM.isChargeBound_pure _ 0).mono (le_of_eq (by simp [mixCharge]))

theorem chg_toQuantumAt_mixImpl (c : Caller) (B : QReg) {α : Type}
    {oa : OracleComp romWorld.Oracles α} {n : ℕ}
    (h : Common.QueryCostAtMost oa (stepW (ch := ch) P) n) :
    IFreeM.IsChargeBound (oa.toQuantumAt (mixImpl c B))
      (Quantum.StdModel.cmdCharge (mixCharge (ch := ch) a b P)) (b * n) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => trivial
  | query_bind i k ih =>
    replace h := (Common.isWeightBound_query_bind_iff _ _ _ _).mp h
    rw [toQuantumAt_query_bind]
    refine (FreeM₂.isChargeBound_bind (chg_mixImpl a b P c B i) fun u ↦ ?_).mono
      (mul_add_sub_le b h.1)
    exact ih u (h.2 u)

theorem chg_realizeT (θ : (s : CSrc ch) → CD ch s) {A : QReg}
    {y : QuantumComp L (TSpec ch) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (tCharge (ch := ch) a b P)) n) :
    IFreeM.IsChargeBound (realizeT θ y) (portCharge (rCharge (ch := ch) a b P)) n := by
  refine IFreeM.IsChargeBound.mapLens (Quantum.Xmss.Assembly.tmplLens θ) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (rCharge (ch := ch) a b P) s
      ((Quantum.Xmss.Assembly.tmplLens θ).toFunA s cmd)) =
      portCharge (tCharge (ch := ch) a b P) := by
    funext s cmd
    rcases cmd with o | ⟨((i | r) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

theorem chg_readLift {A : QReg} {y : QuantumComp L (hwReadSpec HashOutput HashDomain JMem) Ω A}
    {n : ℕ} (h : IFreeM.IsChargeBound y (portCharge (rdCharge (ch := ch) a b P)) n) :
    IFreeM.IsChargeBound (readLift (goodC (ch := ch)) y) (portCharge (tCharge (ch := ch) a b P))
      n := by
  refine IFreeM.IsChargeBound.mapLens (Quantum.Xmss.Assembly.readLens goodC) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (tCharge (ch := ch) a b P) s
      ((Quantum.Xmss.Assembly.readLens goodC).toFunA s cmd)) =
      portCharge (rdCharge (ch := ch) a b P) := by
    funext s cmd
    rcases cmd with o | ⟨i | r, E, ℓ⟩
    · rfl
    · rfl
    · cases r <;> rfl
  rw [he]
  exact h

theorem chg_actT {spec : QuantumOracleSpec.{0, 0}} (κ : spec.Port → ℕ) {A B : QReg} {α : Type}
    (p : SubInstrument A B α) (n : ℕ) :
    IFreeM.IsChargeBound (QComp.act (spec := spec) p) (portCharge κ) n :=
  ⟨Nat.zero_le _, fun _ ↦ trivial⟩

theorem chg_mapT {spec : QuantumOracleSpec.{0, 0}} (κ : spec.Port → ℕ) {A B : QReg} {α β : Type}
    {x : QComp spec A B α} (f : α → β) {n : ℕ}
    (h : IFreeM.IsChargeBound x (portCharge κ) n) :
    IFreeM.IsChargeBound (x.map f) (portCharge κ) n := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact FreeM₂.isChargeBound_bind (n₂ := 0) h fun _ ↦ trivial

theorem chg_revealThen {B B' : QReg} {α : Type} (T : Finset (CSrc ch))
    (k : RevealVals (CD ch) T × (Finset (CSrc ch) × JMem) → QComp (TSpec ch) B B' α) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (tCharge (ch := ch) a b P)) n) :
    IFreeM.IsChargeBound (revealThen goodC T k) (portCharge (tCharge (ch := ch) a b P)) n := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.zero_le n, fun r ↦ ?_⟩
  simp only [tCharge, Nat.sub_zero]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0)
    (chg_actT _ _ 0) fun _ ↦ hk r) (Nat.zero_add n).le

theorem chg_progThen {B B' : QReg} {α : Type}
    (p : LazyProg HashOutput HashDomain (CSrc ch) (CD ch)) (hp : goodC p)
    (k : QComp (TSpec ch) B B' α) {n : ℕ}
    (hk : IFreeM.IsChargeBound k (portCharge (tCharge (ch := ch) a b P)) n) :
    IFreeM.IsChargeBound (progThen p hp k) (portCharge (tCharge (ch := ch) a b P)) n := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.zero_le n, fun r ↦ ?_⟩
  simp only [tCharge, Nat.sub_zero]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0)
    (chg_actT _ _ 0) fun _ ↦ hk) (Nat.zero_add n).le

theorem cost_hashQ (l : HashInput) : Common.QueryCostAtMost (hashQ l) (stepW (ch := ch) P) 1 := by
  unfold hashQ
  split
  · refine (Common.isWeightBound_query (stepW (ch := ch) P) (.inr _)).mono ?_
    simp only [stepW]
    split <;> simp
  · exact Common.isWeightBound_pure _ _ _

theorem cost_walk (j : J) :
    ∀ n μ x, Common.QueryCostAtMost (ch.walk romWorld P j μ n x) (stepW (ch := ch) P) n
  | 0, μ, x => by
    simp only [Chains.walk]
    exact Common.isWeightBound_pure _ _ _
  | n + 1, μ, x => by
    simp only [Chains.walk]
    exact ((Common.isWeightBound_map _ (cost_hashQ P _)).bind fun y ↦
      cost_walk j n (μ + 1) y).mono (by omega)

variable [Fintype J] [DecidableEq J] [Inhabited Val]

omit [Fintype J] in
theorem chg_progFrom (B : QReg) (j : J) :
    ∀ ν, IFreeM.IsChargeBound (progFrom (ch := ch) P B j ν)
      (portCharge (tCharge (ch := ch) a b P)) 0 := by
  intro ν
  induction h : ch.len j - ν generalizing ν with
  | zero =>
    rw [progFrom, dite_eq_right (by omega)]
    trivial
  | succ n ih =>
    rw [progFrom, dite_eq_left (show ν < ch.len j by omega)]
    exact chg_progThen a b P _ trivial _ (ih (ν + 1) (by omega))

theorem chg_openT {α : Type} (B : QReg) (j : J) (μ : ℕ)
    (k : RevealVals (CD ch) (openSet ch j μ) → QComp (TSpec ch) B B α) {n : ℕ}
    (hk : ∀ w, IFreeM.IsChargeBound (k w) (portCharge (tCharge (ch := ch) a b P)) n) :
    IFreeM.IsChargeBound (openT P B j μ k) (portCharge (tCharge (ch := ch) a b P)) n :=
  chg_revealThen a b P _ _ fun r ↦
    (FreeM₂.isChargeBound_bind (chg_progFrom a b P B j μ) fun _ ↦ hk r.1).mono (Nat.zero_add n).le

omit [Fintype J] [DecidableEq J] [Inhabited Val] in
theorem chg_keepReads {α : Type} (B : QReg) {oa : OracleComp romWorld.Oracles α} {n : ℕ}
    (h : Common.QueryCostAtMost oa (stepW (ch := ch) P) n) :
    IFreeM.IsChargeBound (keepReads (ch := ch) B oa) (portCharge (tCharge (ch := ch) a b P))
      (b * n) :=
  chg_readLift a b P (chg_toReads a b P updC (chg_toQuantumAt_mixImpl a b P .answer B h))

variable (we : CpreQuery J Tw Fn Msg → ℕ) (C : TwColl Par Tw Fn Msg Out)
  (hC : ∀ l t x, Common.QueryCostAtMost (C.eval romWorld l P t x) (stepW (ch := ch) P)
    (we (.eval l t x)))

include hC in
theorem chg_ansT (B : QReg) (q : CpreQuery J Tw Fn Msg) :
    IFreeM.IsChargeBound (ansT (ch := ch) C P B q) (portCharge (tCharge (ch := ch) a b P))
      (b * we q) := by
  cases q with
  | value j μ =>
    refine IFreeM.IsChargeBound.mono (n₁ := 0) ?_ (Nat.zero_le _)
    show IFreeM.IsChargeBound (valueT P B j μ) _ 0
    unfold valueT
    split_ifs
    · exact chg_openT a b P B j μ _ fun _ ↦ trivial
    · exact chg_revealThen a b P _ _ fun _ ↦ trivial
  | eval l t m =>
    show IFreeM.IsChargeBound (evalT C P B l t m) _ _
    unfold evalT
    by_cases h : ch.IsStepTweak t
    · rw [dite_eq_left h]
      exact chg_openT a b P B _ 0 _ fun _ ↦ chg_keepReads a b P B (hC l t m)
    · rw [dite_eq_right h]
      exact chg_keepReads a b P B (hC l t m)
  | reveal => trivial

include hC in
theorem chg_tImplRun {α : Type} (B : QReg)
    (x : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) α)
    (log : QueryLog (CQ Par Tw J Val Fn Msg Out)) {n : ℕ}
    (hx : Common.QueryCostAtMost x (redW (ch := ch) P we) n) :
    IFreeM.IsChargeBound ((simulateQ (tImpl (ch := ch) C P B) x).run log)
      (portCharge (tCharge (ch := ch) a b P)) (b * n) := by
  induction x using OracleComp.inductionOn generalizing log n with
  | pure x => trivial
  | query_bind t k ih =>
    replace hx := (Common.isWeightBound_query_bind_iff _ _ _ _).mp hx
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with i | q'
    · change IFreeM.IsChargeBound (QuantumComp₂.bind ((readLiftQ goodC (toReads updC
          (mixImpl .red B i))).map fun y ↦ (y, log)) fun p ↦
            (simulateQ (tImpl (ch := ch) C P B) (k p.1)).run p.2) _ _
      refine (FreeM₂.isChargeBound_bind (chg_mapT _ _ (chg_readLift a b P
        (chg_toReads a b P updC (chg_mixImpl a b P .red B i)))) fun p ↦ ?_).mono
          (mul_add_sub_le b hx.1)
      exact ih p.1 p.2 (hx.2 p.1)
    · change IFreeM.IsChargeBound (QuantumComp₂.bind ((ansT C P B q').map
          fun y ↦ (y, log ++ [⟨q', y⟩])) fun p ↦
            (simulateQ (tImpl (ch := ch) C P B) (k p.1)).run p.2) _ _
      refine (FreeM₂.isChargeBound_bind (chg_mapT _ _
        (chg_ansT a b P we C hC B q')) fun p ↦ ?_).mono (mul_add_sub_le b hx.1)
      exact ih p.1 p.2 (hx.2 p.1)

include hC in
/-- **The adversary run by the reduction**: `a` per hash call, the handler's `b · m` per
classical call. -/
theorem chg_tRun {Q St : Type} {R : OracleSpec.{0, 0} Q} {X Y : QReg → Type}
    (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St) {m : ℕ}
    (hσ : ∀ st q, Common.QueryCostAtMost (σ st q) (redW (ch := ch) P we) m)
    (leaf : ∀ u, X u → St × QueryLog (CQ Par Tw J Val Fn Msg Out) → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A)
    (s : St × QueryLog (CQ Par Tw J Val Fn Msg Out)) {N : ℕ}
    (hx : IFreeM.IsChargeBound x (advCharge a (b * m)) N) :
    IFreeM.IsChargeBound (tRun (ch := ch) C P σ leaf x s) (portCharge (tCharge (ch := ch) a b P))
      N := by
  induction x using IFreeM.inductionOn generalizing s N with
  | pure _ _ => rw [tRun]; trivial
  | liftBind A' c next ih =>
    replace hx := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hx
    rcases c with o | ⟨p | q, E, ℓ⟩
    · rw [tRun]
      refine (IFreeM.isChargeBound_bind (n₁ := 0)
        (n₂ := N - advCharge (R := R) a (b * m) A' (.prim o))
        (chg_readLift a b P (chg_readSub a b P updC A' (.prim o))) fun _ bb ↦ ?_).mono
          ((Nat.zero_add _).trans_le (Nat.sub_le _ _))
      obtain ⟨bb, e⟩ := bb
      subst e
      exact ih bb s (hx.2 bb)
    · rw [tRun]
      refine (IFreeM.isChargeBound_bind (n₁ := a)
        (n₂ := N - advCharge (R := R) a (b * m) A' (.query (.hash p) E ℓ))
        (chg_readLift a b P (chg_readSub a b P updC A' (.query (.hash p) E ℓ))) fun _ bb ↦ ?_).mono
          ?_
      · obtain ⟨bb, e⟩ := bb
        subst e
        exact ih bb s (hx.2 bb)
      · have h1 := hx.1
        simp only [advCharge, Quantum.StdModel.cmdCharge, Quantum.StdModel.hashCharge,
          Quantum.StdModel.callCharge, Nat.mul_one, Nat.mul_zero, Nat.add_zero] at h1 ⊢
        omega
    · rw [tRun]
      refine (IFreeM.isChargeBound_bind (n₁ := 0 + b * m)
        (n₂ := N - advCharge (R := R) a (b * m) A' (.query (.call q) E ℓ)) ?_ fun _ l ↦ ?_).mono ?_
      · unfold tTree
        exact FreeM₂.isChargeBound_bind (chg_actT _ _ 0) fun _ ↦
          chg_mapT _ _ (chg_tImplRun a b P we C hC _ (σ s.1 q) s.2 (hσ s.1 q))
      · obtain ⟨e, l⟩ := l
        subst e
        exact ih _ _ (hx.2 _)
      · have h1 := hx.1
        simp only [advCharge, Quantum.StdModel.cmdCharge, Quantum.StdModel.hashCharge,
          Quantum.StdModel.callCharge, Nat.mul_one, Nat.mul_zero, Nat.zero_add] at h1 ⊢
        omega

/-- **The decision's reads**: the forgery's walk, at most `lenMax ch` steps. -/
theorem chg_judgeT (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out))
    (out : J × ℕ × Val) :
    IFreeM.IsChargeBound (judgeT (ch := ch) P log out) (portCharge (tCharge (ch := ch) a b P))
      (b * lenMax ch) := by
  unfold judgeT
  refine (FreeM₂.isChargeBound_bind (n₂ := 0) (chg_readLift a b P (chg_toReads a b P updC
    (chg_toQuantumAt_mixImpl a b P .judge _ (cost_walk P out.1 _ _ _)))) fun _ ↦ ?_).mono ?_
  · exact chg_revealThen a b P _ _ fun _ ↦ trivial
  · rw [Nat.add_zero]
    exact Nat.mul_le_mul_left b ((Nat.sub_le _ _).trans
      (Finset.le_sup (f := ch.len) (Finset.mem_univ _)))

include hC in
/-- **The template game's calls by kind.** -/
theorem chg_cpreT {Q St S0 F : Type} {R : OracleSpec.{0, 0} Q}
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) {c₀ m k c₁ n : ℕ}
    (hpre : Common.QueryCostAtMost pre (redW (ch := ch) P we) c₀)
    (hσ : ∀ st q, Common.QueryCostAtMost (σ st q) (redW (ch := ch) P we) m)
    (hpost : ∀ s0 f st, Common.QueryCostAtMost (post s0 f st) (redW (ch := ch) P we) c₁)
    (hn : ∀ s0, IFreeM.IsChargeBound (adv s0)
      (Quantum.StdModel.cmdCharge Quantum.StdModel.hashCharge) n)
    (hk : ∀ s0, IFreeM.IsChargeBound (adv s0)
      (Quantum.StdModel.cmdCharge Quantum.StdModel.callCharge) k) :
    IFreeM.IsChargeBound (cpreT (ch := ch) C P pre adv st0 σ post)
      (portCharge (tCharge (ch := ch) a b P))
      (b * c₀ + ((a * n + b * m * k) + (b * c₁ + b * lenMax ch))) := by
  unfold cpreT
  exact FreeM₂.isChargeBound_bind (chg_tImplRun a b P we C hC _ pre [] hpre) fun p ↦
    FreeM₂.isChargeBound_bind (chg_tRun a b P we C hC σ hσ _ (adv p.1) (st0 p.1, p.2)
      (((hn p.1).mul a).add ((hk p.1).mul (b * m)))) fun r ↦
      FreeM₂.isChargeBound_bind (chg_tImplRun a b P we C hC _ (post p.1 r.1.1 r.1.2) r.2
        (hpost _ _ _)) fun o ↦ chg_judgeT a b P o.2 o.1

include hC in
/-- **The realized template game's calls by kind**, at all hidden values. -/
theorem chg_realizeT_cpreT {Q St S0 F : Type} {R : OracleSpec.{0, 0} Q}
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) {c₀ m k c₁ n : ℕ}
    (hpre : Common.QueryCostAtMost pre (redW (ch := ch) P we) c₀)
    (hσ : ∀ st q, Common.QueryCostAtMost (σ st q) (redW (ch := ch) P we) m)
    (hpost : ∀ s0 f st, Common.QueryCostAtMost (post s0 f st) (redW (ch := ch) P we) c₁)
    (hn : ∀ s0, IFreeM.IsChargeBound (adv s0)
      (Quantum.StdModel.cmdCharge Quantum.StdModel.hashCharge) n)
    (hk : ∀ s0, IFreeM.IsChargeBound (adv s0)
      (Quantum.StdModel.cmdCharge Quantum.StdModel.callCharge) k)
    (θ : (s : CSrc ch) → CD ch s) :
    IFreeM.IsChargeBound (realizeT θ (cpreT (ch := ch) C P pre adv st0 σ post))
      (portCharge (rCharge (ch := ch) a b P))
      (b * c₀ + ((a * n + b * m * k) + (b * c₁ + b * lenMax ch))) :=
  chg_realizeT a b P θ (chg_cpreT a b P we C hC pre adv st0 σ post hpre hσ hpost hn hk)

end charges

end Quantum.StdModel.Qrom.CpreQ

end
