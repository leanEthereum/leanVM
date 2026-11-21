module

public import Quantum.Xmss.Hybrid.ViewBy
public import Quantum.Xmss.GameReads

@[expose] public section

/-!
# Runtime 2 as a template program

The SUF-CMA game as runtime 2 runs it (design, section 2, G4), written as a template program over
the hidden values `v : (s : S) → D s`, so that the lazy-sampling property `ViewBy` of
`Quantum.Xmss.Hybrid.Disclose` follows from `Quantum.Xmss.Hybrid.ViewBy`'s machinery.

**Why the label lives in the memory** (`need_subset_label_of_selfDisc`, a negative result). A label
read from the hardwired cells that hardwiring never lowers depends only on which cells are
hardwired (`label_progUpdate_eq`), so a self-disclosing program port (`SelfDisc`) forces its
coordinates into the label as soon as its cell, at some hidden values, is hardwired. leanXMSS's
leaf and node `h`-cells range over essentially all of `Z` as the hidden values vary, so the label
would contain every key's chain ends after the first disclosure. Hence `viewByOn_runtime2_realize`
(with `SelfDisc`) does not apply to leanXMSS; the label is recorded in the memory instead.

**Reveal and record ports.** The memory is `Finset S × M`; its first component, the memory label
`memLab`, is the set of disclosed coordinates. The template signature `tmplSpec` is `lazySpec` for
this label plus *reveal ports* (`revealSpec`): a reveal of `T` returns the hidden values on `T` and
records `T` (`revealStep`, Kraus operators `revealKraus`). Its realization at `v` (`realizeT`,
`tmplLens`) calls the *record port* of `T` (`recSpec`, `recStep`: classical, the memory label
grows by `T`, nothing else changes) and continues with the values of `v` on `T`. The realized
programs run against `runtimeR m₀`, runtime 2 extended by the record ports.

* `stepLazy_tmplStep`: the template runtime is lazy in the memory label (runtime 2's ports by
  `stepLazy_lazyStep`, a reveal depends on `v` only through `T`, which it records).
* `queryWeight_realizeT`: for weights vanishing at `0`, running the realization against `runtimeR`
  is running the template against the template runtime (a reveal's branches at other values
  vanish).
* `viewBy_runtimeR_realize`: `ViewBy` for the realized programs, given lazy initial states and the
  support hypothesis that every program port is called on states whose label contains its
  coordinates (`ForallQueries`).
* `Disc y T` (**reveals before it programs**): along every path of `y`, every program port's
  coordinates were recorded by an earlier reveal (or are in `T`). `forallQueries_of_disc` turns it
  into the support hypothesis (every port keeps the label, a reveal adds its coordinates:
  `suppMap_tmplStep`); `viewBy_runtimeR_of_disc` combines both.

The hypotheses of the design, for the memory label: `hlab` holds with equality
(`memLab_progUpdate`: hardwiring keeps the memory); the reads of runtime 1 with an inner memory are
lifted so that their updates keep the label (`liftRead`, `readMono_liftRead`, `readLens`); `SelfDisc`
is replaced by `Disc`, since hardwiring never records anything in the memory; initial states that do
not depend on `v` are lazy (`lazy_const`).

**leanXMSS.** Hidden values: `S = HPos = ValPos ⊕ RLabel`, `D = XD` (a digest per coordinate:
chain values, chain starts included, and tree values at the positions `ValPos`; the randomizer base
`R0` of each label `RLabel`, a key with its message), at the table `L` the function `valueAt L`
(`valuePos L` on `.inl`). Public data (`Pub`, `pubOf L`): the public parameter, `π`, the keys
`(h, k, k')`. At a structural slot (chain step, leaf, node) the honest path's cells are functions
of the public data and the values at `slotNeed s` (payload and output positions, as `.inl`
coordinates `inlSet`): `roundK`, `roundK'` read `k`, `k'`
of the public keys; `roundH` reads `h`, except at the last round, where the value is corrected by
`embed128` so that the output digest is the value at the output position. The rate's group is XOR,
so the correction XORs the wanted digest with the current one: the output digest is then the value
at the output position whatever the public `h` holds there. It vanishes at `pubOf L` and
`valueAt L`, and with the public `h` reparametrized at the honest output capacities (the output
digest zeroed) it gives the table's value back: the reparametrization `Θ ≃ P × V` on the tables
whose honest paths do not share these cells (`Quantum.Xmss.Assembly.Reparam`).

* `gameT M upd pub A`: reveal the root, run the adversary on the public key against `challengeT`
  (local operations and permutation calls simulated given `π`, so the adversary's calls are sponge
  ports; a signing request answered by `signT`), verify the forgery through read ports
  (`readsProgram`), return the winning condition. `signLayerT lab`: reveal the label's
  randomizer base `.inr lab`, the randomizer search from it through read ports (`grindR`; each
  trial's `h`-reads update the memory with `upd l e b xi`, `b` the block and `xi` the rate after
  `π`: EncCost's `cwUpd` at the memory `Selections`, `keepUpd` to keep it), then one reveal of
  `layerNeed` (the coordinates of the slots the signature makes public, `layerSlots`: chain steps
  from the opened positions, the leaf, the nodes on the path; the opened positions; the path) and
  the program ports of those slots' honest paths (`slotPorts`, three per block). `signT` signs the
  labels `botLabel r` and `topLabel r` (the bottom root revealed by the bottom signature). Every
  request reprograms its slots, also those already public.
* `gameT_eq_prefixT_bind`: `gameT` is the challenge prefix `prefixT` (the root's reveal and the
  challenged adversary, returning the public key, the forgery and the transcript) followed by
  `verifyT` (the verification's reads and the winning condition): the event bound runs on the
  prefix, the verification's reads are final reads (`isChargeBound_of_bind₂` bounds the prefix's
  calls by the game's).
* `disc_gameT`, `disc_prefixT`: the game and its prefix reveal before they program.
  `viewBy_gameT`, `viewByOn_gameT`: the lazy-sampling property of the realized games for
  `runtimeR` and the memory label, at every call, for every initial state not depending on `v`.

Not here: that `realizeT (valueAt L) (gameT M upd (pubOf L) A)` is the runtime-2 game of the table
`L`, the reparametrization's good set, and the record ports in runtime 1 (where they act alike) and
in the event bound (where they change neither the databases nor the hardwired cells). `Disclose`'s
runtime-2 mass bounds are stated for `runtime2`; for `runtimeR` use `sum_queryWeight_view_le` with
the hidden sets empty on the record ports.
-/

open Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v w w₁

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid

/-! ## Labels read from the hardwired cells: a negative result -/

section forcing

variable {X Z : Type} [DecidableEq X] [DecidableEq Z]

/-- The cell of a program port is hardwired in `W`. -/
def CellHardwired : HwProg X Z → Hw X Z → Prop
  | .programH z _, W => W.1 z ≠ none
  | .programK x _, W => W.2.1 x ≠ none
  | .programK' x _, W => W.2.2 x ≠ none

/-- Hardwiring an already hardwired cell is undone by hardwiring its old value back. -/
theorem exists_progUpdate_inverse (c : HwProg X Z) (W : Hw X Z) (hc : CellHardwired c W) :
    ∃ c' : HwProg X Z, progUpdate c' (progUpdate c W) = W := by
  cases c with
  | programH z x =>
    obtain ⟨x₀, hx₀⟩ := Option.ne_none_iff_exists'.mp hc
    refine ⟨.programH z x₀, ?_⟩
    show (Function.update (Function.update W.1 z (some x)) z (some x₀), W.2) = W
    rw [Function.update_idem, ← hx₀, Function.update_eq_self]
  | programK y x =>
    obtain ⟨x₀, hx₀⟩ := Option.ne_none_iff_exists'.mp hc
    refine ⟨.programK y x₀, ?_⟩
    show (W.1, Function.update (Function.update W.2.1 y (some x)) y (some x₀), W.2.2) = W
    rw [Function.update_idem, ← hx₀, Function.update_eq_self]
  | programK' y x =>
    obtain ⟨x₀, hx₀⟩ := Option.ne_none_iff_exists'.mp hc
    refine ⟨.programK' y x₀, ?_⟩
    show (W.1, W.2.1, Function.update (Function.update W.2.2 y (some x)) y (some x₀)) = W
    rw [Function.update_idem, ← hx₀, Function.update_eq_self]

variable {M S : Type}

/-- **A label that hardwiring never lowers depends only on which cells are hardwired**: hardwiring
an already hardwired cell to another value keeps the label. -/
theorem label_progUpdate_eq (lab : Hw X Z × M → Finset S)
    (hlab : ∀ (c : HwProg X Z) (b : Hw X Z × M), lab b ⊆ lab (progUpdate c b.1, b.2))
    (c : HwProg X Z) (W : Hw X Z) (m : M) (hc : CellHardwired c W) :
    lab (progUpdate c W, m) = lab (W, m) := by
  obtain ⟨c', hc'⟩ := exists_progUpdate_inverse c W hc
  refine subset_antisymm ?_ (hlab c (W, m))
  have h := hlab c' (progUpdate c W, m)
  dsimp only at h
  rwa [hc'] at h

/-- **Why the label cannot be read from the hardwired cells.** With a label that hardwiring never
lowers, a self-disclosing template program port forces its coordinates into the label of every
classical state in which its cell, at some hidden values `v`, is already hardwired (with any
value). For leanXMSS's leaf and node ports the `h`-cell ranges over essentially all of `Z` as the
hidden values vary, so a single hardwired `h`-cell would put every key's chain ends into the label;
the hidden-mass bounds of `Disclose` then lose their undisclosed sources. The template below
records the label in the memory instead. -/
theorem need_subset_label_of_selfDisc [Fintype M] [DecidableEq M] [DecidableEq S] {D : S → Type}
    (lab : Hw X Z × M → Finset S)
    (hlab : ∀ (c : HwProg X Z) (b : Hw X Z × M), lab b ⊆ lab (progUpdate c b.1, b.2))
    {p : LazyProg X Z S D} (hp : SelfDisc lab p) (v : (s : S) → D s) (W : Hw X Z) (m : M)
    (hc : CellHardwired (p.realize v) W) : p.need ⊆ lab (W, m) := by
  have h := hp v (W, m)
  dsimp only at h
  rwa [label_progUpdate_eq lab hlab _ W m hc] at h

end forcing

/-! ## The record and reveal ports -/

section reveal

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M]

variable (X Z S M) in
/-- **The memory label**: the disclosed coordinates, the first component of the memory. -/
abbrev memLab : Hw X Z × (Finset S × M) → Finset S :=
  fun b ↦ b.2.1

variable (D) in
/-- The values a reveal of the coordinates `T` returns: the hidden values restricted to `T`. -/
abbrev RevealVals (T : Finset S) : Type :=
  (s : {s // s ∈ T}) → D s.1

variable (S M) in
/-- The record ports: record coordinates in the memory label; the result is the memory before. -/
@[reducible]
def recSpec : QuantumOracleSpec.{0, 0} where
  Port := Finset S
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result _ := Finset S × M

variable (S D M) in
/-- The reveal ports of the template: return the hidden values on the coordinates `T` (and the
memory before) and record `T` in the memory label. -/
@[reducible]
def revealSpec : QuantumOracleSpec.{0, 0} where
  Port := Finset S
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result T := RevealVals D T × (Finset S × M)

/-- The Kraus operator of recording `T`, with outcome `m` the memory before. -/
noncomputable def recKraus (T : Finset S) (m : Finset S × M) :
    Matrix (Unit × HwReg X Z (Finset S × M)) (Unit × HwReg X Z (Finset S × M)) ℂ :=
  (1 : Matrix Unit Unit ℂ) ⊗ₖ clsKraus (fun b : Hw X Z × (Finset S × M) ↦ b.2 = m)
    (fun b ↦ (b.1, (b.2.1 ∪ T, b.2.2))) fun _ ↦ 1

theorem sum_recKraus (T : Finset S) :
    ∑ m, (recKraus (X := X) (Z := Z) (M := M) T m)ᴴ * recKraus T m = 1 := by
  refine sum_conjTranspose_clsKraus_mul_self _ _ _
    (fun r b b' hb hb' he ↦ Prod.ext (Prod.mk.inj he).1 (hb.trans hb'.symm)) fun b ↦ ?_
  simp [Finset.sum_ite_eq]

/-- The record port of `T` as a subinstrument. -/
noncomputable def recStep (T : Finset S) :
    SubInstrument (Unit × HwReg X Z (Finset S × M)) (Unit × HwReg X Z (Finset S × M))
      (Finset S × M) :=
  SubInstrument.ofKraus (recKraus T) (sum_recKraus T)

theorem recStep_branch (T : Finset S) (m : Finset S × M) :
    (recStep (X := X) (Z := Z) T).branch m = MatrixMap.conj (recKraus T m) :=
  rfl

/-- The Kraus operator of revealing `T` at the hidden values `v`: the record operator when the
returned values are those of `v` on `T`, zero otherwise. -/
noncomputable def revealKraus (T : Finset S) (v : (s : S) → D s) (r : RevealVals D T × (Finset S × M)) :
    Matrix (Unit × HwReg X Z (Finset S × M)) (Unit × HwReg X Z (Finset S × M)) ℂ :=
  if r.1 = restrictTo T v then recKraus T r.2 else 0

theorem sum_revealKraus (T : Finset S) (v : (s : S) → D s) :
    ∑ r, (revealKraus (X := X) (Z := Z) (M := M) T v r)ᴴ * revealKraus T v r = 1 := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (restrictTo T v)]
  · simpa [revealKraus] using sum_recKraus (X := X) (Z := Z) (M := M) T
  · intro w _ hw
    simp [revealKraus, hw]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The reveal port of `T` at the hidden values `v` as a subinstrument. -/
noncomputable def revealStep (T : Finset S) (v : (s : S) → D s) :
    SubInstrument (Unit × HwReg X Z (Finset S × M)) (Unit × HwReg X Z (Finset S × M))
      (RevealVals D T × (Finset S × M)) :=
  SubInstrument.ofKraus (revealKraus T v) (sum_revealKraus T v)

theorem revealStep_branch (T : Finset S) (v : (s : S) → D s)
    (r : RevealVals D T × (Finset S × M)) :
    (revealStep (X := X) (Z := Z) T v).branch r = MatrixMap.conj (revealKraus T v r) :=
  rfl

omit [Fintype S] [∀ s, Fintype (D s)] [Fintype M] in
/-- A record of `T` moves the memory `m` to `(m.1 ∪ T, m.2)` and keeps the hardwired cells. -/
theorem recKraus_ne_zero {T : Finset S} {m : Finset S × M} {u u' : Unit}
    {s s' : HwReg X Z (Finset S × M)} (h : recKraus T m (u', s') (u, s) ≠ 0) :
    s'.2 = (s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) :=
  (clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2).2

omit [Fintype S] [∀ s, Fintype (D s)] [Fintype M] in
/-- A reveal moves the memory `m` to `(m.1 ∪ T, m.2)` and returns the values of `v` on `T`. -/
theorem revealKraus_ne_zero {T : Finset S} {v : (s : S) → D s}
    {r : RevealVals D T × (Finset S × M)} {u u' : Unit} {s s' : HwReg X Z (Finset S × M)}
    (h : revealKraus T v r (u', s') (u, s) ≠ 0) :
    r.1 = restrictTo T v ∧ s'.2 = (s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) := by
  unfold revealKraus at h
  split_ifs at h with hr
  · exact ⟨hr, (clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2).2⟩
  · exact absurd rfl h

theorem revealStep_branch_self (T : Finset S) (v : (s : S) → D s) (m : Finset S × M) :
    (revealStep (X := X) (Z := Z) T v).branch (restrictTo T v, m) = (recStep T).branch m := by
  rw [revealStep_branch, recStep_branch, revealKraus, ite_eq_left rfl]

theorem revealStep_branch_of_ne (T : Finset S) (v : (s : S) → D s) {w : RevealVals D T}
    (hw : w ≠ restrictTo T v) (m : Finset S × M) :
    (revealStep (X := X) (Z := Z) T v).branch (w, m) = 0 := by
  rw [revealStep_branch, revealKraus, ite_eq_right hw]
  ext ρ a b
  simp

end reveal

/-! ## The template runtime -/

section template

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M]

variable (X Z S D M) in
/-- **The template signature**: runtime 2's template ports (`lazySpec`) for the memory label, then
the reveal ports. -/
@[reducible]
def tmplSpec (good : LazyProg X Z S D → Prop) : QuantumOracleSpec.{0, 0} :=
  (lazySpec X Z (Finset S × M) (memLab X Z S M) D good).sum (revealSpec S D M)

variable (X Z S M) in
/-- The signature of runtime 2 with record ports. -/
@[reducible]
def recHwSpec : QuantumOracleSpec.{0, 0} :=
  (hwSpec X Z (Finset S × M)).sum (recSpec S M)

variable {good : LazyProg X Z S D → Prop}

variable (good) in
/-- The coordinates a template port needs disclosed: those of a program port's cell and value. -/
def tmplNeed : (tmplSpec X Z S D M good).Port → Finset S
  | .inl i => lazyNeed (memLab X Z S M) good i
  | .inr _ => ∅

variable (good) in
/-- The coordinates a template port records: those of a reveal. -/
def tmplGain : (tmplSpec X Z S D M good).Port → Finset S
  | .inl _ => ∅
  | .inr T => T

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]

/-- **Runtime 2 with record ports**: a record port of `T` adds `T` to the memory label. -/
@[reducible]
noncomputable def runtimeR (m₀ : Finset S × M) : QuantumRuntime (recHwSpec X Z S M) :=
  (runtime2 X Z m₀).extend (t := recSpec S M) recStep

/-- The steps of the template runtime at the hidden values `v`: those of runtime 2 at the realized
program ports, and the reveal ports. -/
noncomputable def tmplStep (m₀ : Finset S × M) (v : (s : S) → D s) :
    ∀ i : (tmplSpec X Z S D M good).Port,
      SubInstrument ((tmplSpec X Z S D M good).In i × QReg.of (HwReg X Z (Finset S × M)))
        ((tmplSpec X Z S D M good).Out i × QReg.of (HwReg X Z (Finset S × M)))
        ((tmplSpec X Z S D M good).Result i)
  | .inl i => lazyStep m₀ v i
  | .inr T => revealStep T v

/-- **The template runtime is lazy in the memory label.** The ports of runtime 2 by
`stepLazy_lazyStep` (hardwiring keeps the memory, so the label); a reveal of `T` records `T` and
depends on the hidden values only through their coordinates in `T`. -/
theorem stepLazy_tmplStep (m₀ : Finset S × M) :
    StepLazy (tmplStep (X := X) (Z := Z) (good := good) m₀)
      (fun r : QReg.of (HwReg X Z (Finset S × M)) ↦ r.2.2.1) (tmplNeed good) := by
  intro i r
  rcases i with i | T
  · exact stepLazy_lazyStep m₀ (fun _ _ ↦ subset_rfl) (lazyNeed (memLab X Z S M) good)
      (fun _ _ _ _ h ↦ h) i r
  · refine lazyMap_congr (fun v ↦ revealStep_branch T v r)
      (lazyMap_conj _ (fun v b a hK ↦ ?_) fun v v' b a _ hv ↦ ?_)
    · obtain ⟨u', s'⟩ := b
      obtain ⟨u, s⟩ := a
      show s.2.2.1 ⊆ s'.2.2.1
      rw [(revealKraus_ne_zero hK).2]
      exact Finset.subset_union_left
    · obtain ⟨u', s'⟩ := b
      obtain ⟨u, s⟩ := a
      by_cases hT : T ⊆ s'.2.2.1
      · have he : restrictTo T v = restrictTo T v' := restrictTo_eq (hv.mono hT)
        simp only [revealKraus, he]
      · have h0 : ∀ w, revealKraus (X := X) (Z := Z) T w r (u', s') (u, s) = 0 := fun w ↦ by
          by_contra hne
          refine hT ?_
          rw [(revealKraus_ne_zero hne).2]
          exact Finset.subset_union_right
        exact (h0 v).trans (h0 v').symm

/-- The realization of a template at the hidden values `v`, as a lens: the ports of runtime 2 as
in `realizeLens`, a reveal of `T` becomes the record port of `T`, its values read from `v`. -/
def tmplLens {L : LocalSig.{u, v}} (v : (s : S) → D s) :
    IPFunctor.Lens (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good))
      (QuantumComp.toIPFunctor L (recHwSpec X Z S M)) where
  toFunA _
    | .prim o => .prim o
    | .query (.inl (.inl (.inl i))) E ℓ => .query (.inl (.inl (.inl i))) E ℓ
    | .query (.inl (.inl (.inr c))) E ℓ => .query (.inl (.inl (.inr c.1))) E ℓ
    | .query (.inl (.inr p)) E ℓ => .query (.inl (.inr (p.1.realize v))) E ℓ
    | .query (.inr T) E ℓ => .query (.inr T) E ℓ
  toFunB _ c := by
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact id
    · exact id
    · exact id
    · cases p <;> exact id
    · exact fun b ↦ ULift.up (restrictTo T v, b.down)
  src_eq _ c _ := by
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · rfl
    · rfl
    · rfl
    · cases p <;> rfl
    · rfl

/-- **The realized program**: at the hidden values `v`, every template program port calls the
program port it realizes, and every reveal the record port, continuing with the values of `v`. -/
def realizeT {L : LocalSig.{u, v}} {Ω : QReg → Type w} {A : QReg} (v : (s : S) → D s)
    (y : QuantumComp L (tmplSpec X Z S D M good) Ω A) : QuantumComp L (recHwSpec X Z S M) Ω A :=
  IPFunctor.IFreeM.mapLens (tmplLens v) y

/-- A weight of the runtime with record ports, read on the template ports at `v`. -/
def realizeWeightT (v : (s : S) → D s)
    (wt : ∀ i, Matrix ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M)))
      ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M))) ℂ → ℝ≥0∞) :
    ∀ i : (tmplSpec X Z S D M good).Port,
      Matrix ((tmplSpec X Z S D M good).In i × QReg.of (HwReg X Z (Finset S × M)))
        ((tmplSpec X Z S D M good).In i × QReg.of (HwReg X Z (Finset S × M))) ℂ → ℝ≥0∞
  | .inl (.inl (.inl i)) => wt (.inl (.inl (.inl i)))
  | .inl (.inl (.inr c)) => wt (.inl (.inl (.inr c.1)))
  | .inl (.inr p) => wt (.inl (.inr (p.1.realize v)))
  | .inr T => wt (.inr T)

/-- **Running the realized program.** For weights vanishing at `0`, the weights of the runtime
with record ports running the realization at `v` are those of the template runtime at `v`
running the template: a reveal's branches at other values are zero. -/
theorem queryWeight_realizeT {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w}
    (m₀ : Finset S × M) (v : (s : S) → D s)
    (wt : ∀ i, Matrix ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M)))
      ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M))) ℂ → ℝ≥0∞)
    (hw0 : ∀ i, wt i 0 = 0)
    {A : QReg} (y : QuantumComp L (tmplSpec X Z S D M good) Ω A)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M))) (A × QReg.of (HwReg X Z (Finset S × M))) ℂ)
    (j : ℕ) :
    (runtimeR m₀).queryWeight I wt (realizeT v y) ρ j =
      (famRuntime (initHw X Z m₀) (tmplStep m₀) v).queryWeight I (realizeWeightT v wt) y ρ j := by
  have hw0' : ∀ i, realizeWeightT (good := good) v wt i 0 = 0 := by
    rintro (((i | c) | p) | T) <;> exact hw0 _
  induction y using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rfl
  | primBind _ o k ih => exact tsum_congr fun b ↦ ih b _ j
  | queryBind _ i E ℓ k ih =>
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · cases j with
      | zero => rfl
      | succ j => exact tsum_congr fun r ↦ ih r _ j
    · cases j with
      | zero => rfl
      | succ j => exact tsum_congr fun r ↦ ih r _ j
    · cases p <;> cases j <;> first | rfl | exact tsum_congr fun r ↦ ih r _ _
    · cases j with
      | zero => rfl
      | succ j =>
        have he : ∀ m, ((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep
            (.inr T) E ℓ).branch (restrictTo T v, m) ρ =
              ((runtimeR m₀).queryStep (.inr T) E ℓ).branch m ρ := fun m ↦ by
          refine (queryStep_branch_apply (R := famRuntime (initHw X Z m₀)
            (tmplStep (good := good) m₀) v) (.inr T) E ℓ (restrictTo T v, m) ρ).trans
            (Eq.trans ?_ (queryStep_branch_apply (R := runtimeR m₀) (.inr T) E ℓ m ρ).symm)
          change (SubInstrument.relabel _).branch ()
            (((revealStep (X := X) (Z := Z) T v).branch (restrictTo T v, m)).amplify E _) = _
          rw [revealStep_branch_self]
          rfl
        have hz : ∀ (w : RevealVals D T) m, w ≠ restrictTo T v →
            ((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep
              (.inr T) E ℓ).branch (w, m) ρ = 0 := fun w m hw ↦ by
          refine (queryStep_branch_apply (R := famRuntime (initHw X Z m₀)
            (tmplStep (good := good) m₀) v) (.inr T) E ℓ (w, m) ρ).trans ?_
          change (SubInstrument.relabel _).branch ()
            (((revealStep (X := X) (Z := Z) T v).branch (w, m)).amplify E _) = _
          rw [revealStep_branch_of_ne T v hw m]
          simp only [MatrixMap.amplify_zero]
          exact map_zero _
        let F : Finset S × M → ℝ≥0∞ := fun m ↦
          (runtimeR m₀).queryWeight I wt (realizeT v (k (restrictTo T v, m)))
            (((runtimeR m₀).queryStep (.inr T) E ℓ).branch m ρ) j
        let G : RevealVals D T × (Finset S × M) → ℝ≥0∞ := fun r ↦
          (famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryWeight I
            (realizeWeightT v wt) (k r)
            (((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep
              (.inr T) E ℓ).branch r ρ) j
        have hFG : ∀ m, F m = G (restrictTo T v, m) := fun m ↦
          (ih _ _ j).trans (congrArg (fun σ ↦
            (famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryWeight I
              (realizeWeightT v wt) (k (restrictTo T v, m)) σ j) (he m).symm)
        have hG0 : ∀ w m, w ≠ restrictTo T v → G (w, m) = 0 := fun w m hw ↦
          (congrArg (fun σ ↦
            (famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryWeight I
              (realizeWeightT v wt) (k (w, m)) σ j) (hz w m hw)).trans
            (QuantumRuntime.queryWeight_zero _ I hw0' _ j)
        show ∑' m, F m = ∑' r, G r
        rw [tsum_fintype, tsum_fintype, Fintype.sum_prod_type (f := G),
          Finset.sum_eq_single (restrictTo T v)
            (fun w _ hw ↦ Finset.sum_eq_zero fun m _ ↦ hG0 w m hw)
            (fun h ↦ absurd (Finset.mem_univ _) h)]
        exact Finset.sum_congr rfl fun m _ ↦ hFG m

theorem diagMass_zero {α : Type} [Fintype α] (C : Set α) : diagMass C (0 : Matrix α α ℂ) = 0 := by
  simp [diagMass]

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem diagMass_progT_congr
    (C : ∀ i, Set ((recHwSpec X Z S M).In i × QReg.of (HwReg X Z (Finset S × M))))
    {c c' : HwProg X Z} (h : c = c')
    (σ : Matrix (Unit × HwReg X Z (Finset S × M)) (Unit × HwReg X Z (Finset S × M)) ℂ) :
    diagMass (C (.inl (.inr c))) σ = diagMass (C (.inl (.inr c'))) σ := by
  subst h
  rfl

/-- **The lazy-sampling property for runtime 2 with reveals.** Let `y` be a template whose run
presents every program port only states whose memory label contains its coordinates
(`ForallQueries`, discharged by `forallQueries_of_disc` for a template that reveals before it
programs). If the initial states are lazy, the realized programs satisfy `ViewBy` for the runtime
with record ports and the memory label at every call. -/
theorem viewBy_runtimeR_realize {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w}
    (m₀ : Finset S × M) {A : QReg} (y : QuantumComp L (tmplSpec X Z S D M good) Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × QReg.of (HwReg X Z (Finset S × M)))
      (A × QReg.of (HwReg X Z (Finset S × M))) ℂ)
    (hρ : Lazy (fun p ↦ p.2.2.2.1) ρ)
    (hsupp : ∀ v, (famRuntime (initHw X Z m₀) (tmplStep m₀) v).ForallQueries I
      (CallSupp (fun r : QReg.of (HwReg X Z (Finset S × M)) ↦ r.2.2.1) (tmplNeed good)) y (ρ v))
    (j : ℕ) :
    ViewBy (runtimeR m₀) I (fun r ↦ r.2.2.1) (fun v ↦ realizeT v y) ρ j := by
  intro T v v' hv C hC
  have h0 : ∀ i, diagMass (C i) 0 = 0 := fun i ↦ diagMass_zero _
  rw [queryWeight_realizeT I m₀ v _ h0, queryWeight_realizeT I m₀ v' _ h0]
  refine queryWeight_eq_of_lazy I (stepLazy_tmplStep m₀)
    (fun u ↦ realizeWeightT u fun i ↦ diagMass (C i)) T (fun u u' i σ σ' hu hs hs' hσ ↦ ?_)
    y ρ hρ hsupp j hv
  rcases i with ((i | c) | ⟨p, hp⟩) | T'
  · exact diagMass_eq_of_label (α := (recHwSpec X Z S M).In (.inl (.inl (.inl i))) ×
      QReg.of (HwReg X Z (Finset S × M))) (fun q ↦ q.2.2.2.1) T _ (fun q hq ↦ hC _ q hq) hσ
  · exact diagMass_eq_of_label (α := (recHwSpec X Z S M).In (.inl (.inl (.inr c.1))) ×
      QReg.of (HwReg X Z (Finset S × M))) (fun q ↦ q.2.2.2.1) T _ (fun q hq ↦ hC _ q hq) hσ
  · have hσ₁ : ∀ a b : Unit × HwReg X Z (Finset S × M), a.2.2.2.1 ∪ b.2.2.2.1 ⊆ T →
        σ a b = σ' a b := hσ
    have hs₁ : SuppAt (fun a : Unit × HwReg X Z (Finset S × M) ↦ a.2.2.2.1) p.need σ := hs
    have hs₁' : SuppAt (fun a : Unit × HwReg X Z (Finset S × M) ↦ a.2.2.2.1) p.need σ' := hs'
    have hC₁ : ∀ c, ∀ q ∈ C (.inl (.inr c)),
        (fun a : Unit × HwReg X Z (Finset S × M) ↦ a.2.2.2.1) q = T := fun c q hq ↦ hC _ q hq
    show diagMass (C (.inl (.inr (p.realize u)))) σ = diagMass (C (.inl (.inr (p.realize u')))) σ'
    by_cases hT : p.need ⊆ T
    · exact (diagMass_progT_congr C (p.realize_eq (hu.mono hT)) σ).trans
        (diagMass_eq_of_label (α := Unit × HwReg X Z (Finset S × M)) _ T _ (hC₁ _) hσ₁)
    · exact (diagMass_eq_zero_of_suppAt (α := Unit × HwReg X Z (Finset S × M)) _ T p.need _
        (hC₁ _) hT hs₁).trans (diagMass_eq_zero_of_suppAt (α := Unit × HwReg X Z (Finset S × M))
          _ T p.need _ (hC₁ _) hT hs₁').symm
  · exact diagMass_eq_of_label (α := (recHwSpec X Z S M).In (.inr T') ×
      QReg.of (HwReg X Z (Finset S × M))) (fun q ↦ q.2.2.2.1) T _ (fun q hq ↦ hC _ q hq) hσ

end template

/-! ## Supports -/

section supp

variable {S : Type}

theorem suppAt_mono {α : Type*} {lab : α → Finset S} {T T' : Finset S} {σ : Matrix α α ℂ}
    (h : SuppAt lab T σ) (hT : T' ⊆ T) : SuppAt lab T' σ :=
  fun a b hab ↦ ⟨hT.trans (h a b hab).1, hT.trans (h a b hab).2⟩

/-- A map on the left factor keeps supports labelled on the right factor. -/
theorem suppAt_amplify {α β R : Type*} (Φ : MatrixMap α β) {lab : R → Finset S} {T : Finset S}
    {ρ : Matrix (α × R) (α × R) ℂ} (h : SuppAt (fun p : α × R ↦ lab p.2) T ρ) :
    SuppAt (fun p : β × R ↦ lab p.2) T (Φ.amplify R ρ) := by
  intro a b hab
  rw [MatrixMap.amplify_apply] at hab
  obtain ⟨x, y, hxy⟩ : ∃ x y, ρ (x, a.2) (y, b.2) ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hab ?_
    rw [show ρ.submatrix (·, a.2) (·, b.2) = 0 from Matrix.ext fun x y ↦ hc x y, map_zero]
    rfl
  exact h _ _ hxy

/-- A map that sends supports above `T` to supports above `T'`, framed by an ancilla on the right,
does the same on the left factor's labels. -/
theorem suppAt_amplifyLeft {α β E : Type*} (Φ : MatrixMap α β) {labA : α → Finset S}
    {labB : β → Finset S} {T T' : Finset S}
    (hΦ : ∀ σ, SuppAt labA T σ → SuppAt labB T' (Φ σ)) {ρ : Matrix (α × E) (α × E) ℂ}
    (h : SuppAt (fun p : α × E ↦ labA p.1) T ρ) :
    SuppAt (fun p : β × E ↦ labB p.1) T' (Φ.amplify E ρ) := by
  intro a b hab
  rw [MatrixMap.amplify_apply] at hab
  exact hΦ _ (fun x y hxy ↦ h (x, a.2) (y, b.2) hxy) a.1 b.1 hab

/-- A relabelling that preserves the labels keeps supports. -/
theorem suppAt_relabel {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {labA : α → Finset S} {labB : β → Finset S} (he : ∀ a, labB (e a) = labA a)
    {T : Finset S} {ρ : Matrix α α ℂ} (h : SuppAt labA T ρ) :
    SuppAt labB T ((SubInstrument.relabel e).branch () ρ) := by
  intro a b hab
  rw [SubInstrument.relabel_branch_apply, submatrix_apply] at hab
  obtain ⟨h1, h2⟩ := h _ _ hab
  rw [← e.apply_symm_apply a, ← e.apply_symm_apply b, he, he]
  exact ⟨h1, h2⟩

/-- A map sends the operators supported above `T` to operators supported above `T'`. -/
def SuppMap {α β : Type*} (labA : α → Finset S) (labB : β → Finset S) (T T' : Finset S)
    (Φ : MatrixMap α β) : Prop :=
  ∀ σ, SuppAt labA T σ → SuppAt labB T' (Φ σ)

theorem suppMap_congr {α β : Type*} {labA : α → Finset S} {labB : β → Finset S}
    {T T' : Finset S} {Φ Ψ : MatrixMap α β} (h : Φ = Ψ) (hΨ : SuppMap labA labB T T' Ψ) :
    SuppMap labA labB T T' Φ :=
  h ▸ hΨ

/-- A Kraus map whose nonzero entries carry labels above `T` to labels above `T'`. -/
theorem suppMap_conj {α β : Type*} [Fintype α] {labA : α → Finset S} {labB : β → Finset S}
    {T T' : Finset S} (K : Matrix β α ℂ)
    (hK : ∀ b a, K b a ≠ 0 → T ⊆ labA a → T' ⊆ labB b) :
    SuppMap labA labB T T' (MatrixMap.conj K) := by
  intro σ h b b' hb
  rw [MatrixMap.conj_apply] at hb
  simp only [Matrix.mul_apply, conjTranspose_apply] at hb
  obtain ⟨a', -, ha'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hK' : K b' a' ≠ 0 := fun h0 ↦ ha' (by simp [h0])
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul ha')
  obtain ⟨h1, h2⟩ := h a a' (right_ne_zero_of_mul ha)
  exact ⟨hK b a (left_ne_zero_of_mul ha) h1, hK b' a' hK' h2⟩

end supp

/-! ## Templates that reveal before they program -/

section disc

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [DecidableEq S] {D : S → Type} {M : Type}
  {good : LazyProg X Z S D → Prop} {L : LocalSig.{u, v}}

variable (good) in
/-- The coordinates a command needs disclosed. -/
def cmdNeed {A : QReg} : QuantumComp.Cmd L (tmplSpec X Z S D M good) A → Finset S
  | .prim _ => ∅
  | .query i _ _ => tmplNeed good i

variable (good) in
/-- The coordinates a command records. -/
def cmdGain {A : QReg} : QuantumComp.Cmd L (tmplSpec X Z S D M good) A → Finset S
  | .prim _ => ∅
  | .query i _ _ => tmplGain good i

/-- **A template that reveals before it programs**, from the recorded coordinates `T`: along every
path, every program port's coordinates are recorded (in `T` or by an earlier reveal). -/
def Disc {Ω : QReg → Type w} :
    {A : QReg} → IPFunctor.IFreeM (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good)) Ω A →
      Finset S → Prop
  | _, .pure _, _ => True
  | _, .liftBind c next, T => cmdNeed good c ⊆ T ∧ ∀ b, Disc (next b) (T ∪ cmdGain good c)

variable {Ω : QReg → Type w}

theorem disc_mono {A : QReg}
    (y : IPFunctor.IFreeM (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good)) Ω A)
    {T T' : Finset S} (h : T ⊆ T') (hy : Disc y T) : Disc y T' := by
  induction y using IPFunctor.IFreeM.inductionOn generalizing T T' with
  | pure _ _ => trivial
  | liftBind _ c next ih =>
    exact ⟨hy.1.trans h, fun b ↦ ih b (Finset.union_subset_union h subset_rfl) (hy.2 b)⟩

theorem disc_cast {A A' : QReg} (e : A = A')
    (y : IPFunctor.IFreeM (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good)) Ω A)
    (T : Finset S) : Disc (e ▸ y) T ↔ Disc y T := by
  subst e
  rfl

/-- Sequencing: a continuation that reveals before it programs from every larger set of recorded
coordinates. -/
theorem disc_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good)) Ω A)
    (g : ∀ u, Ω u → IPFunctor.IFreeM (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good)) Y u)
    {T : Finset S} (hx : Disc x T) (hg : ∀ u a T', T ⊆ T' → Disc (g u a) T') :
    Disc (x.bind g) T := by
  induction x using IPFunctor.IFreeM.inductionOn generalizing T with
  | pure _ a => exact hg _ a T subset_rfl
  | liftBind _ c next ih =>
    exact ⟨hx.1, fun b ↦ ih b (hx.2 b) fun u a T' h ↦ hg u a T' (Finset.subset_union_left.trans h)⟩

theorem disc₂_bind {A B C : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L (tmplSpec X Z S D M good) A B α)
    (g : α → QuantumComp₂ L (tmplSpec X Z S D M good) B C β) {T : Finset S} (hx : Disc x T)
    (hg : ∀ a T', T ⊆ T' → Disc (g a) T') : Disc (x.bind g) T := by
  refine disc_bind x _ hx fun u p T' h ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a T' h

theorem disc_primBind {A : QReg} (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L (tmplSpec X Z S D M good) Ω (L.next o b))
    (T : Finset S) : Disc (QuantumComp.primBind o k) T ↔ ∀ b, Disc (k b) T := by
  constructor
  · intro h b
    have h2 : Disc (k b) (T ∪ ∅) := h.2 (ULift.up b)
    rwa [Finset.union_empty] at h2
  · intro h
    refine ⟨Finset.empty_subset _, fun b ↦ ?_⟩
    have h2 : Disc (k b.down) (T ∪ ∅) := by rw [Finset.union_empty]; exact h b.down
    exact h2

theorem disc_queryBind {A : QReg} (i : (tmplSpec X Z S D M good).Port) (E : QReg)
    (ℓ : A ≃ (tmplSpec X Z S D M good).In i × E)
    (k : (tmplSpec X Z S D M good).Result i →
      QuantumComp L (tmplSpec X Z S D M good) Ω (QReg.of ((tmplSpec X Z S D M good).Out i × E)))
    (T : Finset S) :
    Disc (QuantumComp.queryBind i E ℓ k) T ↔
      tmplNeed good i ⊆ T ∧ ∀ r, Disc (k r) (T ∪ tmplGain good i) :=
  ⟨fun h ↦ ⟨h.1, fun r ↦ h.2 (ULift.up r)⟩, fun h ↦ ⟨h.1, fun r ↦ h.2 r.down⟩⟩

/-- Substituting trees that reveal before they program from any recorded coordinates. -/
theorem disc_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor L spec)
      (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good)))
    (hσ : ∀ A c T, Disc (σ A c) T) {A : QReg}
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor L spec) Ω A) (T : Finset S) :
    Disc (x.substitute σ) T := by
  induction x using IPFunctor.IFreeM.inductionOn generalizing T with
  | pure _ _ => trivial
  | liftBind s c next ih =>
    rw [IPFunctor.IFreeM.substitute_liftBind]
    exact disc_bind _ _ (hσ s c T) fun u ans T' _ ↦ (disc_cast ans.2 _ T').mpr (ih ans.1 T')

variable [Fintype S] [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] [Fintype M] [DecidableEq M]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]

omit [Fintype S] in
/-- A Kraus map of runtime 2 that keeps the memory keeps the label. -/
theorem suppMap_conj_keep {α β : Type} [Fintype α] (lA : α → Finset S) (lB : β → Finset S)
    (K : Matrix β α ℂ) (hK : ∀ b a, K b a ≠ 0 → lA a ⊆ lB b) (T : Finset S) :
    SuppMap lA lB T (T ∪ ∅) (MatrixMap.conj K) :=
  suppMap_conj K fun b a h hT ↦ by rw [Finset.union_empty]; exact hT.trans (hK b a h)

theorem suppMap_sponge (m₀ : Finset S × M) (i : SpongePort)
    (r : (hwSpec X Z (Finset S × M)).Result (.inl (.inl i))) (T : Finset S) :
    SuppMap (fun p : spongeIn X Z i × HwReg X Z (Finset S × M) ↦ p.2.2.2.1)
      (fun p : spongeIn X Z i × HwReg X Z (Finset S × M) ↦ p.2.2.2.1) T (T ∪ ∅)
      (((runtime2 X Z m₀).step (.inl (.inl i))).branch r) :=
  suppMap_congr (runtime2_branch m₀ (.inl (.inl i)) r) (suppMap_conj_keep _ _ _ (fun b a hK ↦ by
    obtain ⟨u', s'⟩ := b
    obtain ⟨u, s⟩ := a
    show s.2.2.1 ⊆ s'.2.2.1
    rw [spongeHardwired_U_ne_zero_snd (hwEmpty X Z) m₀ i hK]) T)

theorem suppMap_read (m₀ : Finset S × M) (c : HwRead X Z (Finset S × M))
    (hc : ReadMono (memLab X Z S M) c) (r : c.Result) (T : Finset S) :
    SuppMap (fun p : Unit × HwReg X Z (Finset S × M) ↦ p.2.2.2.1)
      (fun p : Unit × HwReg X Z (Finset S × M) ↦ p.2.2.2.1) T (T ∪ ∅)
      (((runtime2 X Z m₀).step (.inl (.inr c))).branch r) :=
  suppMap_congr (runtime2_branch m₀ (.inl (.inr c)) r) (suppMap_conj_keep _ _ _ (fun b a hK ↦ by
    obtain ⟨u', s'⟩ := b
    obtain ⟨u, s⟩ := a
    exact hwReadKraus_ne_zero_label c hc r hK) T)

theorem suppMap_prog (m₀ : Finset S × M) (c : HwProg X Z) (r : c.Result) (T : Finset S) :
    SuppMap (fun p : Unit × HwReg X Z (Finset S × M) ↦ p.2.2.2.1)
      (fun p : Unit × HwReg X Z (Finset S × M) ↦ p.2.2.2.1) T (T ∪ ∅)
      (((runtime2 X Z m₀).step (.inr c)).branch r) :=
  suppMap_congr (runtime2_branch m₀ (.inr c) r) (suppMap_conj_keep _ _ _ (fun b a hK ↦ by
    obtain ⟨u', s'⟩ := b
    obtain ⟨u, s⟩ := a
    show s.2.2.1 ⊆ s'.2.2.1
    rw [hwProgKraus_ne_zero_snd c r hK]) T)

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem suppMap_reveal (T' : Finset S) (v : (s : S) → D s) (r : RevealVals D T' × (Finset S × M))
    (T : Finset S) :
    SuppMap (fun p : Unit × HwReg X Z (Finset S × M) ↦ p.2.2.2.1)
      (fun p : Unit × HwReg X Z (Finset S × M) ↦ p.2.2.2.1) T (T ∪ T')
      ((revealStep T' v).branch r) :=
  suppMap_congr (revealStep_branch T' v r) (suppMap_conj _ fun b a hK hT ↦ by
    obtain ⟨u', s'⟩ := b
    obtain ⟨u, s⟩ := a
    show T ∪ T' ⊆ s'.2.2.1
    rw [(revealKraus_ne_zero hK).2]
    exact Finset.union_subset_union hT subset_rfl)

/-- **Every port keeps the memory label, and a reveal adds its coordinates.** -/
theorem suppMap_tmplStep (m₀ : Finset S × M) (v : (s : S) → D s)
    (i : (tmplSpec X Z S D M good).Port) (r : (tmplSpec X Z S D M good).Result i)
    (T : Finset S) :
    SuppMap (fun p : (tmplSpec X Z S D M good).In i × QReg.of (HwReg X Z (Finset S × M)) ↦
        p.2.2.2.1)
      (fun p : (tmplSpec X Z S D M good).Out i × QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1)
      T (T ∪ tmplGain good i) ((tmplStep m₀ v i).branch r) := by
  rcases i with ((i | ⟨c, hc⟩) | ⟨p, hp⟩) | T'
  · exact suppMap_sponge m₀ i r T
  · exact suppMap_read m₀ c hc r T
  · cases p with
    | programH T₀ c => exact suppMap_prog m₀ ((LazyProg.programH T₀ c).realize v) r T
    | programK T₀ c => exact suppMap_prog m₀ ((LazyProg.programK T₀ c).realize v) r T
    | programK' T₀ c => exact suppMap_prog m₀ ((LazyProg.programK' T₀ c).realize v) r T
  · exact suppMap_reveal T' v r T

/-- A call of the template runtime keeps the recorded coordinates and adds those of a reveal. -/
theorem suppAt_queryStep (m₀ : Finset S × M) (v : (s : S) → D s) {A : QReg}
    (i : (tmplSpec X Z S D M good).Port) (E : QReg) (ℓ : A ≃ (tmplSpec X Z S D M good).In i × E)
    (r : (tmplSpec X Z S D M good).Result i) {T : Finset S}
    {ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M))) (A × QReg.of (HwReg X Z (Finset S × M))) ℂ}
    (h : SuppAt (fun p : A × QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) T ρ) :
    SuppAt (fun p : QReg.of ((tmplSpec X Z S D M good).Out i × E) ×
        QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) (T ∪ tmplGain good i)
      (((famRuntime (initHw X Z m₀) (tmplStep m₀) v).queryStep i E ℓ).branch r ρ) := by
  rw [queryStep_branch_apply]
  refine suppAt_relabel (labA := fun p : ((tmplSpec X Z S D M good).Out i ×
    QReg.of (HwReg X Z (Finset S × M))) × E ↦ p.1.2.2.2.1) _ (fun _ ↦ rfl) ?_
  exact suppAt_amplifyLeft _ (suppMap_tmplStep m₀ v i r T)
    (suppAt_relabel (labA := fun p : A × QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1)
      (labB := fun p : ((tmplSpec X Z S D M good).In i × QReg.of (HwReg X Z (Finset S × M))) ×
        E ↦ p.1.2.2.2.1) _ (fun _ ↦ rfl) h)

theorem forallQueries_of_disc' {L : LocalSig.{u, v}} (I : L.Interp) (m₀ : Finset S × M)
    (v : (s : S) → D s) {A : QReg} (y : QuantumComp L (tmplSpec X Z S D M good) Ω A) :
    ∀ T, Disc y T → ∀ ρ, SuppAt (fun p : A × QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) T ρ →
      (famRuntime (initHw X Z m₀) (tmplStep m₀) v).ForallQueries I
        (CallSupp (fun r : QReg.of (HwReg X Z (Finset S × M)) ↦ r.2.2.1) (tmplNeed good)) y ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _; trivial
  | primBind _ o k ih =>
    intro T hy ρ hρ
    exact (forallQueries_primBind_iff I o k ρ).mpr fun b ↦ ih b T ((disc_primBind o k T).mp hy b)
      _ (suppAt_amplify (lab := fun r : QReg.of (HwReg X Z (Finset S × M)) ↦ r.2.2.1) _ hρ)
  | queryBind _ i E ℓ k ih =>
    intro T hy ρ hρ
    obtain ⟨h1, h2⟩ := (disc_queryBind i E ℓ k T).mp hy
    refine (forallQueries_queryBind_iff I i E ℓ k ρ).mpr ⟨?_, fun r ↦ ih r _ (h2 r) _
      (suppAt_queryStep m₀ v i E ℓ r hρ)⟩
    exact suppAt_relabel (labA := fun p : _ × QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1)
      (labB := fun p : ((tmplSpec X Z S D M good).In i × QReg.of (HwReg X Z (Finset S × M))) ×
        E ↦ p.1.2.2.2.1) _ (fun _ ↦ rfl) (suppAt_mono hρ h1)

/-- **Revealing before programming gives the support hypothesis** of `viewBy_runtimeR_realize`:
from a state supported on the memory labels containing `T`, a template that reveals before it
programs from `T` presents every program port only states whose label contains its
coordinates. -/
theorem forallQueries_of_disc {L : LocalSig.{u, v}} (I : L.Interp) (m₀ : Finset S × M)
    (v : (s : S) → D s) {A : QReg} (y : QuantumComp L (tmplSpec X Z S D M good) Ω A)
    (T : Finset S) (hy : Disc y T)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M))) (A × QReg.of (HwReg X Z (Finset S × M))) ℂ)
    (hρ : SuppAt (fun p : A × QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) T ρ) :
    (famRuntime (initHw X Z m₀) (tmplStep m₀) v).ForallQueries I
      (CallSupp (fun r : QReg.of (HwReg X Z (Finset S × M)) ↦ r.2.2.1) (tmplNeed good)) y ρ :=
  forallQueries_of_disc' I m₀ v y T hy ρ hρ

/-- **The lazy-sampling property for a template that reveals before it programs**, from lazy
initial states supported on the labels containing `T`; `ViewByOn` follows by
`ViewBy.viewByOn`. -/
theorem viewBy_runtimeR_of_disc {L : LocalSig.{u, v}} (I : L.Interp) (m₀ : Finset S × M)
    {A : QReg} (y : QuantumComp L (tmplSpec X Z S D M good) Ω A) (T : Finset S) (hy : Disc y T)
    (ρ : ((s : S) → D s) → Matrix (A × QReg.of (HwReg X Z (Finset S × M)))
      (A × QReg.of (HwReg X Z (Finset S × M))) ℂ)
    (hρ : Lazy (fun p ↦ p.2.2.2.1) ρ)
    (hT : ∀ v, SuppAt (fun p : A × QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) T (ρ v))
    (j : ℕ) :
    ViewBy (runtimeR m₀) I (fun r ↦ r.2.2.1) (fun v ↦ realizeT v y) ρ j :=
  viewBy_runtimeR_realize I m₀ y ρ hρ (fun v ↦ forallQueries_of_disc I m₀ v y T hy (ρ v) (hT v)) j

end disc

/-! ## Charge bounds of a prefix -/

section prefixCharge

/-- **A charge bound of a sequence bounds its first part**: every path of `x` is the start of a
path of `x.bind k`. -/
theorem isChargeBound_of_bind {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{0, 0}}
    {Ω : QReg → Type w} {Ω' : QReg → Type w₁} {A : QReg} {x : QuantumComp L spec Ω A}
    {k : ∀ u, Ω u → QuantumComp L spec Ω' u}
    {c : (s : QReg) → (QuantumComp.toIPFunctor L spec).A s → ℕ} {n : ℕ}
    (h : IPFunctor.IFreeM.IsChargeBound (x.bind k) c n) : IPFunctor.IFreeM.IsChargeBound x c n := by
  induction x using IPFunctor.IFreeM.inductionOn generalizing n with
  | pure _ _ => trivial
  | liftBind _ _ _ ih => exact ⟨h.1, fun b ↦ ih b (h.2 b)⟩

/-- `isChargeBound_of_bind` for programs with fixed final registers. -/
theorem isChargeBound_of_bind₂ {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{0, 0}}
    {A B C : QReg} {α : Type w} {β : Type w₁} {x : QuantumComp₂ L spec A B α}
    {k : α → QuantumComp₂ L spec B C β}
    {c : (s : QReg) → (QuantumComp.toIPFunctor L spec).A s → ℕ} {n : ℕ}
    (h : IPFunctor.IFreeM.IsChargeBound (x.bind k) c n) :
    IPFunctor.IFreeM.IsChargeBound x c n := by
  induction x using IPFunctor.IFreeM.inductionOn generalizing n with
  | pure _ _ => trivial
  | liftBind _ _ _ ih => exact ⟨h.1, fun b ↦ ih b (h.2 b)⟩

end prefixCharge

/-! ## Calls of the template ports -/

section calls

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [DecidableEq S] {D : S → Type} {M : Type}
  {good : LazyProg X Z S D → Prop}

variable (good) in
/-- **A reveal of `T` beside a held register `B`**, then the continuation with its result (the
values on `T` and the memory before). -/
noncomputable def revealThen {B C : QReg} {α : Type} (T : Finset S)
    (k : RevealVals D T × (Finset S × M) → QComp (tmplSpec X Z S D M good) B C α) :
    QComp (tmplSpec X Z S D M good) B C α :=
  QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := tmplSpec X Z S D M good) (.inr T) B
    (Equiv.uniqueProd B Unit).symm fun r ↦
      (QComp.act (A := QReg.of ((tmplSpec X Z S D M good).Out (.inr T) × B)) (B := B)
        (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦ k r

/-- **A template program port beside a held register `B`**, then the continuation. -/
noncomputable def progThen {B C : QReg} {α : Type} (p : LazyProg X Z S D) (hp : good p)
    (k : QComp (tmplSpec X Z S D M good) B C α) : QComp (tmplSpec X Z S D M good) B C α :=
  QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := tmplSpec X Z S D M good)
    (.inl (.inr ⟨p, hp⟩)) B (Equiv.uniqueProd B Unit).symm fun _ ↦
      (QComp.act (A := QReg.of ((tmplSpec X Z S D M good).Out (.inl (.inr ⟨p, hp⟩)) × B)) (B := B)
        (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦ k

omit [DecidableEq S] in
/-- Sequencing after a reveal sequences its continuation. -/
theorem revealThen_bind {B C E : QReg} {α β : Type} (T : Finset S)
    (k : RevealVals D T × (Finset S × M) → QComp (tmplSpec X Z S D M good) B C α)
    (f : α → QComp (tmplSpec X Z S D M good) C E β) :
    (revealThen good T k).bind f = revealThen good T fun r ↦ (k r).bind f :=
  rfl

/-- A read port of runtime 2 with an inner memory `M`, on the memory `Finset S × M`: the label
stays. -/
def liftRead : HwRead X Z M → HwRead X Z (Finset S × M)
  | .readH z upd => .readH z fun m o ↦ (m.1, upd m.2 o)
  | .readK x upd => .readK x fun m o ↦ (m.1, upd m.2 o)
  | .readK' x upd => .readK' x fun m o ↦ (m.1, upd m.2 o)

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [DecidableEq S] in
/-- **`ReadMono` for the lifted reads**: their memory updates keep the label. -/
theorem readMono_liftRead (c : HwRead X Z M) :
    ReadMono (memLab X Z S M) (liftRead (S := S) c) := by
  cases c <;> intro _ _ _ <;> exact subset_rfl

omit [Fintype X] [Fintype Z] [DecidableEq S] in
/-- **Hardwiring never lowers the memory label** (`hlab`): it keeps the memory. -/
theorem memLab_progUpdate (c : HwProg X Z) (b : Hw X Z × (Finset S × M)) :
    memLab X Z S M b ⊆ memLab X Z S M (progUpdate c b.1, b.2) :=
  subset_rfl

variable (good) in
/-- The programs of runtime 1's ports (sponge and read ports, inner memory `M`) as templates: the
reads lifted to the memory with the label. -/
def readLens {L : LocalSig.{u, v}} :
    IPFunctor.Lens (QuantumComp.toIPFunctor L (hwReadSpec X Z M))
      (QuantumComp.toIPFunctor L (tmplSpec X Z S D M good)) where
  toFunA _
    | .prim o => .prim o
    | .query (.inl i) E ℓ => .query (.inl (.inl (.inl i))) E ℓ
    | .query (.inr c) E ℓ => .query (.inl (.inl (.inr ⟨liftRead c, readMono_liftRead c⟩))) E ℓ
  toFunB _ c := by
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact id
    · exact id
    · cases c <;> exact fun b ↦ ULift.up (b.down.1, b.down.2.2)
  src_eq _ c _ := by
    rcases c with o | ⟨i | c, E, ℓ⟩
    · rfl
    · rfl
    · cases c <;> rfl

variable (good) in
/-- A program of runtime 1's ports as a template. -/
def readLift {L : LocalSig.{u, v}} {Ω : QReg → Type w} {A : QReg}
    (y : QuantumComp L (hwReadSpec X Z M) Ω A) : QuantumComp L (tmplSpec X Z S D M good) Ω A :=
  IPFunctor.IFreeM.mapLens (readLens good) y

variable (good) in
/-- `readLift` for fixed final registers. -/
def readLiftQ {A B : QReg} {α : Type} (y : QComp (hwReadSpec X Z M) A B α) :
    QComp (tmplSpec X Z S D M good) A B α :=
  readLift good y

theorem disc_act {A B : QReg} {α : Type} (p : SubInstrument A B α) (T : Finset S) :
    Disc (QComp.act (spec := tmplSpec X Z S D M good) p) T :=
  (disc_primBind _ _ T).mpr fun _ ↦ trivial

theorem disc_revealThen {B C : QReg} {α : Type} (T₀ : Finset S)
    (k : RevealVals D T₀ × (Finset S × M) → QComp (tmplSpec X Z S D M good) B C α) (T : Finset S)
    (hk : ∀ r, Disc (k r) (T ∪ T₀)) : Disc (revealThen good T₀ k) T :=
  (disc_queryBind (.inr T₀) B _ _ T).mpr ⟨Finset.empty_subset _, fun r ↦
    disc₂_bind _ _ (disc_act _ _) fun _ _ hT' ↦ disc_mono _ hT' (hk r)⟩

theorem disc_progThen {B C : QReg} {α : Type} (p : LazyProg X Z S D) (hp : good p)
    (k : QComp (tmplSpec X Z S D M good) B C α) (T : Finset S) (h : p.need ⊆ T)
    (hk : Disc k T) : Disc (progThen p hp k) T :=
  (disc_queryBind (.inl (.inr ⟨p, hp⟩)) B _ _ T).mpr ⟨h, fun _ ↦
    disc₂_bind _ _ (disc_act _ _) fun _ _ hT' ↦ disc_mono _ (Finset.subset_union_left.trans hT') hk⟩

/-- Runtime 1's programs never program: they reveal before they program from any coordinates. -/
theorem disc_readLift {L : LocalSig.{u, v}} {Ω : QReg → Type w} {A : QReg}
    (y : QuantumComp L (hwReadSpec X Z M) Ω A) (T : Finset S) : Disc (readLift good y) T := by
  induction y using IPFunctor.IFreeM.inductionOn generalizing T with
  | pure _ _ => trivial
  | liftBind _ c next ih =>
    show Disc (IPFunctor.IFreeM.mapLens (readLens good) (IPFunctor.IFreeM.liftBind c next)) T
    rw [IPFunctor.IFreeM.mapLens_liftBind]
    refine ⟨?_, fun b ↦ (disc_cast _ _ _).mpr (ih _ _)⟩
    rcases c with o | ⟨i | c, E, ℓ⟩ <;> exact Finset.empty_subset _

end calls

/-! ## leanXMSS as a template

The hidden coordinates `HPos` are the honest 128-bit values at the positions `ValPos` and the
randomizer bases at the labels `RLabel` (`valueAt L`); the public part of the table is `Pub`. -/

section xmss

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- A randomizer-base label: a bottom key with a request message, or a top key with a bottom
root. -/
abbrev RLabel : Type := (KeyIndex × Message) ⊕ (KeyIndex × Digest)

/-- The layer of a label. -/
def RLabel.layer : RLabel → Layer
  | .inl _ => bottomLayer
  | .inr _ => topLayer

/-- The key of a label. -/
def RLabel.key : RLabel → KeyIndex
  | .inl (e, _) => e
  | .inr (e, _) => e

/-- The message bytes of a label: `32` bytes at the bottom, `16` at the top. -/
def RLabel.msg : RLabel → HashInput
  | .inl (_, m) => littleEndianBytes 32 m
  | .inr (_, d) => littleEndianBytes 16 d

/-- **leanXMSS's hidden coordinates**: the honest 128-bit values and the randomizer bases. -/
abbrev HPos : Type := ValPos ⊕ RLabel

/-- leanXMSS's hidden values: a digest per coordinate. -/
abbrev XD : HPos → Type :=
  fun _ ↦ Digest

/-- **The hidden values of a table**: the honest values at the positions, the randomizer bases at
the labels. -/
def valueAt (L : HonestTable) : HPos → Digest :=
  Sum.elim (valuePos L) fun lab ↦ L.randomizerBase lab.layer lab.key lab.msg

@[simp]
theorem valueAt_inl (L : HonestTable) (p : ValPos) : valueAt L (.inl p) = valuePos L p :=
  rfl

@[simp]
theorem valueAt_inr (L : HonestTable) (lab : RLabel) :
    valueAt L (.inr lab) = L.randomizerBase lab.layer lab.key lab.msg :=
  rfl

/-- Value positions as hidden coordinates. -/
def inlSet (T : Finset ValPos) : Finset HPos :=
  T.map Function.Embedding.inl

@[simp]
theorem inl_mem_inlSet {T : Finset ValPos} {p : ValPos} : (.inl p : HPos) ∈ inlSet T ↔ p ∈ T := by
  simp [inlSet]

@[simp]
theorem inr_not_mem_inlSet {T : Finset ValPos} {lab : RLabel} : (.inr lab : HPos) ∉ inlSet T := by
  simp [inlSet]

theorem inlSet_mono {T T' : Finset ValPos} (h : T ⊆ T') : inlSet T ⊆ inlSet T' :=
  Finset.map_subset_map.mpr h

/-- Every template program port is allowed. -/
def goodAll : LazyProg X Z HPos XD → Prop :=
  fun _ ↦ True

/- Instance search for `HPos` and the registers over `Finset HPos` exceeds the default size: found
once here, the same terms the search would build. -/
set_option synthInstance.maxSize 1000 in
instance hposDecEq : DecidableEq HPos := inferInstance

set_option synthInstance.maxSize 1000 in
instance hwRegHPosDecEq {M : Type} [DecidableEq M] : DecidableEq (HwReg X Z (Finset HPos × M)) :=
  inferInstance

variable (M : Type) [Fintype M] [DecidableEq M]

/-- leanXMSS's template signature, with inner memory `M`. -/
abbrev XSpec : QuantumOracleSpec.{0, 0} :=
  tmplSpec X Z HPos XD M goodAll

/-- **The public part of the table**: the public parameter, the permutation `π`, and the keys
`t = (h, k, k')` (with `h` at the honest output capacities of the structural slots reparametrized,
see `roundH`). The randomizer bases are hidden values (`.inr` coordinates). -/
structure Pub where
  /-- The public parameter `P`. -/
  param : PublicParameter
  /-- The permutation `π` of the sponge decomposition. -/
  perm : Equiv.Perm (X × Z)
  /-- The keys `(h, k, k')`. -/
  keys : SpongeKeys X Z

/-- The public part of a table: the hidden values are `valueAt L`. -/
def pubOf (L : HonestTable) : Pub :=
  ⟨L.param, L.perm, L.keys⟩

/-- Position `j` of chain `i` of key `e` of layer `l` (indices reduced into range). -/
def cpos (l : Layer) (e : KeyIndex) (i : ChainIndex) (j : ℕ) : ValPos :=
  .chain l e i ⟨j % chainLength, Nat.mod_lt _ (by decide)⟩

/-- The tree value of layer `l` at `level`, index `index` (indices reduced into range). -/
def tpos (l : Layer) (level index : ℕ) : ValPos :=
  .tree l ⟨level % (layerHeight + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    ⟨index % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos 32)⟩

/-- The position a structural slot outputs. -/
def slotOutPos : Slot → ValPos
  | .chain l e step i => cpos l e i (step.val + 1)
  | .leaf l e => tpos l 0 e.val
  | .node l level index => tpos l level index
  | _ => tpos bottomLayer 0 0

/-- **The coordinates a structural slot's honest path depends on**: its payload positions and its
output position. -/
def slotNeed : Slot → Finset ValPos
  | .chain l e step i => {cpos l e i step.val, cpos l e i (step.val + 1)}
  | .leaf l e => insert (tpos l 0 e.val) (Finset.univ.image fun i ↦ cpos l e i (chainLength - 1))
  | .node l level index =>
      {tpos l (level - 1) (2 * index), tpos l (level - 1) (2 * index + 1), tpos l level index}
  | _ => ∅

/-- The payload of a structural slot from the values `f` at the positions (as
`HonestTable.payload`). -/
def slotPayload (f : ValPos → Digest) : Slot → HashInput
  | .chain l e step i => Verification.chainPayload i (f (cpos l e i step.val))
  | .leaf l e => digestsPayload fun i : ChainIndex ↦ f (cpos l e i (chainLength - 1))
  | .node l level index =>
      nodePayload (f (tpos l (level - 1) (2 * index))) (f (tpos l (level - 1) (2 * index + 1)))
  | _ => []

/-- The input of a structural slot from the values `f`. -/
def slotInput (pub : Pub) (s : Slot) (f : ValPos → Digest) : HashInput :=
  thInput pub.param (slotFields s) (slotPayload f s)

/-- The number of sponge blocks of a slot's input (it does not depend on the values). -/
def nBlocks (pub : Pub) (s : Slot) : ℕ :=
  (blocks (slotInput pub s fun _ ↦ 0)).length

/-- A digest in the first 128 bits of a rate (the bits `trunc128` reads). -/
def embed128 (d : Digest) : X :=
  fun j ↦ if j.val < 128 then bitOf (d.getLsbD j.val) else 0

/-- The sponge state before round `j` of the absorption of `msg` under the public keys. -/
def stateAt (pub : Pub) (msg : List X) (j : ℕ) : X × Z :=
  (msg.take j).foldl (absorbStep (spongePerm pub.keys pub.perm)) (0, 0)

/-- The state after `π` in a round from state `s` on block `b`. -/
def midAt (pub : Pub) (s : X × Z) (b : X) : X × Z :=
  pub.perm (s.1 + b, s.2 + pub.keys.2.1 (s.1 + b))

/-- The `k`-cell of round `j` of slot `s`'s honest path from the values `f`, with its value. -/
def roundK (pub : Pub) (s : Slot) (f : ValPos → Digest) (j : ℕ) : X × Z :=
  let msg := blocks (slotInput pub s f)
  let x := (stateAt pub msg j).1 + msg.getD j 0
  (x, pub.keys.2.1 x)

/-- The `k'`-cell of round `j`, with its value. -/
def roundK' (pub : Pub) (s : Slot) (f : ValPos → Digest) (j : ℕ) : X × Z :=
  let msg := blocks (slotInput pub s f)
  let p := midAt pub (stateAt pub msg j) (msg.getD j 0)
  (p.1, pub.keys.2.2 p.1)

/-- The `h`-cell of round `j`, with its value: the public `h` value, except at the last round,
where it is corrected (by XOR, the rate's group) so that the digest of the output rate is the value
at the slot's output position. With `pub = pubOf L` and `f = valuePos L` the correction vanishes. -/
def roundH (pub : Pub) (s : Slot) (f : ValPos → Digest) (j : ℕ) : Z × X :=
  let msg := blocks (slotInput pub s f)
  let p := midAt pub (stateAt pub msg j) (msg.getD j 0)
  let z := p.2 + pub.keys.2.2 p.1
  let w := pub.keys.1 z
  if j + 1 = nBlocks pub s then (z, w + embed128 (f (slotOutPos s) ^^^ trunc128 (p.1 + w)))
  else (z, w)

/-- The values revealed on `T` at the value positions, extended by `0`. -/
def extendVals {T : Finset HPos} (w : RevealVals XD T) (p : ValPos) : Digest :=
  if h : .inl p ∈ T then w ⟨.inl p, h⟩ else 0

/-- The randomizer base revealed on `T` at a label, `0` if not revealed. -/
def extendBase {T : Finset HPos} (w : RevealVals XD T) (lab : RLabel) : Digest :=
  if h : .inr lab ∈ T then w ⟨.inr lab, h⟩ else 0

theorem extendVals_restrictTo {T : Finset HPos} {p : ValPos} (h : .inl p ∈ T)
    (f : HPos → Digest) : extendVals (restrictTo T f) p = f (.inl p) := by
  rw [extendVals, dite_eq_left h]
  rfl

theorem extendBase_restrictTo {T : Finset HPos} {lab : RLabel} (h : .inr lab ∈ T)
    (f : HPos → Digest) : extendBase (restrictTo T f) lab = f (.inr lab) := by
  rw [extendBase, dite_eq_left h]
  rfl

/-- **The program ports of a structural slot**: the `k`, `k'`, `h` cells of every round of its
honest path, with their values, functions of the values at `slotNeed s`. -/
def slotPorts (pub : Pub) (s : Slot) : List (LazyProg X Z HPos XD) :=
  (List.range (nBlocks pub s)).flatMap fun j ↦
    [.programK (inlSet (slotNeed s)) fun w ↦ roundK pub s (extendVals w) j,
      .programK' (inlSet (slotNeed s)) fun w ↦ roundK' pub s (extendVals w) j,
      .programH (inlSet (slotNeed s)) fun w ↦ roundH pub s (extendVals w) j]

theorem need_of_mem_slotPorts {pub : Pub} {s : Slot} {p : LazyProg X Z HPos XD}
    (h : p ∈ slotPorts pub s) : p.need = inlSet (slotNeed s) := by
  simp only [slotPorts, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at h
  obtain ⟨j, -, h | h | h⟩ := h <;> subst h <;> rfl

/-- **The slots a layer signature by key `e` with codeword `x` makes public**: the chain steps
from the opened positions, the leaf, and the nodes on the path to the root. -/
def layerSlots (l : Layer) (e : KeyIndex) (x : Encoding) : List Slot :=
  (List.finRange chainCount).flatMap (fun i ↦ ((List.finRange (chainLength - 1)).filter
      fun step ↦ decide ((x i).val ≤ step.val)).map fun step ↦ Slot.chain l e step i) ++
    Slot.leaf l e :: (List.range layerHeight).map fun lev ↦ Slot.node l (lev + 1) (e.val / 2 ^ (lev + 1))

/-- The coordinates of a list of slots. -/
def needUnion : List Slot → Finset ValPos
  | [] => ∅
  | s :: ss => slotNeed s ∪ needUnion ss

theorem slotNeed_subset_needUnion {s : Slot} {ss : List Slot} (h : s ∈ ss) :
    slotNeed s ⊆ needUnion ss := by
  induction ss with
  | nil => exact absurd h List.not_mem_nil
  | cons s' ss ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

/-- The authentication-path sibling at `level` of key `e`. -/
def siblingPos (l : Layer) (e : KeyIndex) (level : Fin layerHeight) : ValPos :=
  tpos l level.val (Nat.xor (e.val / 2 ^ level.val) 1)

/-- **The coordinates a layer signature reveals**: those of the slots it makes public, the opened
chain positions, and the authentication path. -/
def layerNeed (l : Layer) (e : KeyIndex) (x : Encoding) : Finset ValPos :=
  needUnion (layerSlots l e x) ∪ Finset.univ.image (fun i ↦ cpos l e i (x i).val) ∪
    Finset.univ.image (siblingPos l e)

/-- Call the program ports `ps` in order. -/
noncomputable def progPorts (B : QReg) : List (LazyProg X Z HPos XD) → QComp (XSpec M) B B Unit
  | [] => QuantumComp₂.pure ()
  | p :: ps => progThen p trivial (progPorts B ps)

/-- Program the honest paths of the slots `ss`. -/
noncomputable def progSlots (pub : Pub) (B : QReg) : List Slot → QComp (XSpec M) B B Unit
  | [] => QuantumComp₂.pure ()
  | s :: ss => (progPorts M B (slotPorts pub s)).bind fun _ ↦ progSlots pub B ss

/-- **The memory update of a randomizer trial's final `h`-read**, for key `e` of layer `l`, from
the block `b` and the rate `xi` after `π` (EncCost's `cwUpd` at the memory `Selections`). -/
abbrev TrialUpd : Type :=
  Layer → KeyIndex → X → X → M → Option X → M

/-- The trial update that keeps the memory. -/
def keepUpd : TrialUpd M :=
  fun _ _ _ _ ↦ keepMem

/-- Read `h` at `z` through its read port beside `B`, updating the memory with `u`, logged. -/
noncomputable def rdHU (B : QReg) (z : Z) (u : M → Option X → M) :
    StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) X :=
  fun log ↦ (readCall (.readH z u) B).bind fun r ↦
    QuantumComp₂.pure (r.1.getD 0, log ++ [.h z (r.1.getD 0)])

/-- **A sponge round through read ports whose `h`-read updates the memory** with `u b xi`, `b` the
block and `xi` the rate after `π` (as `rdRound`, which keeps the memory). -/
noncomputable def rdRoundU (u : X → X → M → Option X → M) (π : Equiv.Perm (X × Z)) (B : QReg)
    (s : X × Z) (b : X) : StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) (X × Z) := do
  let xp := s.1 + b
  let a ← rdK B xp
  let p := π (xp, s.2 + a)
  let c ← rdK' B p.1
  let w ← rdHU M B (p.2 + c) (u b p.1)
  pure (p.1 + w, p.2 + c)

/-- **A randomizer trial's hash through read ports**: as `readsImpl`, the `h`-reads updating the
memory with `u` (EncCost prices each trial read with this update). -/
noncomputable def hashTrial (u : X → X → M → Option X → M) (π : Equiv.Perm (X × Z)) (B : QReg)
    (input : HashInput) : QComp (hwReadSpec X Z M) B B HashOutput :=
  (out256 <$> (fun s : X × Z ↦ s.1) <$> (blocks input).foldlM (rdRoundU M u π B) (0, 0)).run' []

variable (upd : TrialUpd M)

/-- **The randomizer search through read ports**, as `otsSignFrom` until a codeword: trials
`R0 + c`, message digests read, each trial's `h`-reads updating the memory with `upd l e`. -/
noncomputable def grindR (pub : Pub) (B : QReg) (l : Layer) (e : KeyIndex) (message : HashInput)
    (base : Randomizer) : ℕ → ℕ → QComp (hwReadSpec X Z M) B B (Option (Randomizer × Encoding))
  | 0, _ => QuantumComp₂.pure none
  | n + 1, trial =>
    (hashTrial M (upd l e) pub.perm B (thInput pub.param (hashDomainFields (.message l e))
      (message ++ littleEndianBytes 16 (base + BitVec.ofNat digestBits trial)))).bind fun out ↦
      match Codeword.decode (truncateHash out) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindR pub B l e message base n (trial + 1)

/-- **A layer signature in runtime 2** for the label `lab`: reveal its randomizer base, the
randomizer search from it through reads; then reveal the layer's coordinates, hardwire the honest
paths of the slots it makes public, and read the opened chain values and the path from the
revealed values. Also returns the revealed values. -/
noncomputable def signLayerT (pub : Pub) (B : QReg) (lab : RLabel) :
    QComp (XSpec M) B B (Option (LayerSignature × (ValPos → Digest))) :=
  revealThen goodAll {.inr lab} fun r₀ ↦
  (readLiftQ goodAll (grindR M upd pub B lab.layer lab.key lab.msg (extendBase r₀.1 lab)
    randomizerAttemptLimit 0)).bind fun g ↦
    match g with
    | none => QuantumComp₂.pure none
    | some (ρ, x) => revealThen goodAll (inlSet (layerNeed lab.layer lab.key x)) fun r ↦
        (progSlots M pub B (layerSlots lab.layer lab.key x)).bind fun _ ↦
          QuantumComp₂.pure (some (⟨ρ, fun i ↦ extendVals r.1 (cpos lab.layer lab.key i (x i).val),
            fun level ↦ extendVals r.1 (siblingPos lab.layer lab.key level)⟩, extendVals r.1))

/-- The label of a signing request's bottom layer signature: its key and message. -/
def botLabel (r : SigningRequest) : RLabel :=
  .inl (keyIndexOnLayer r.leafIndex bottomLayer, r.message)

/-- The label of a signing request's top layer signature: its key and the bottom root `d`. -/
def topLabel (r : SigningRequest) (d : Digest) : RLabel :=
  .inr (keyIndexOnLayer r.leafIndex topLayer, d)

/-- The position of the bottom root under a signing request's top key. -/
def botRootPos (r : SigningRequest) : ValPos :=
  tpos bottomLayer layerHeight (keyIndexOnLayer r.leafIndex topLayer).val

/-- **A signature in runtime 2**, as `signWithSchemeSeed`: the bottom layer signs the message, the
top layer the bottom root, read from the bottom layer's revealed values. -/
noncomputable def signT (pub : Pub) (B : QReg) (r : SigningRequest) :
    QComp (XSpec M) B B (Option Signature) :=
  (signLayerT M upd pub B (botLabel r)).bind fun b ↦
    match b with
    | none => QuantumComp₂.pure none
    | some (bottom, f) =>
      (signLayerT M upd pub B (topLabel r (f (botRootPos r)))).bind fun t ↦
        match t with
        | none => QuantumComp₂.pure none
        | some (top, _) => QuantumComp₂.pure
            (some ⟨r.leafIndex, fun l ↦ if l = bottomLayer then bottom else top⟩)

/-- The answer to the signing request `r` with the adversary's register held. -/
noncomputable def signAt (pub : Pub) (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec (X × Z)).In (.sign r) × E) :
    QComp (XSpec M) A (QReg.of ((advSpec (X × Z)).Out (.sign r) × E)) (Option Signature) :=
  (QComp.act (spec := XSpec M) (B := QReg.of ((advSpec (X × Z)).Out (.sign r) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ signT M upd pub _ r

/-- A secret key carrying only the public parameter: the challenger's permutation calls do not
read the key. -/
def noKey (pub : Pub) : SecretKey :=
  ⟨0, pub.param⟩

/-- **The challenger of runtime 2**: a local operation and a permutation call simulated given `π`
(the adversary's calls become sponge ports), a signing request answered by `signT`. -/
noncomputable def challengeT (pub : Pub) :
    IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z)))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (XSpec M))
  | A, .prim o => readLift goodAll ((simulate LocalSig.Interp.instruments pub.perm
      (challenge sufCmaScheme keccakStateEquiv (noKey pub) A (.prim o))).liftOrdinary
        (t := hwReadCmdSpec X Z M))
  | A, .query (.perm p) E ℓ => readLift goodAll ((simulate LocalSig.Interp.instruments pub.perm
      (challenge sufCmaScheme keccakStateEquiv (noKey pub) A (.query (.perm p) E ℓ))).liftOrdinary
        (t := hwReadCmdSpec X Z M))
  | _, .query (.sign r) E ℓ =>
      QuantumComp.bind (signAt M upd pub r E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's program against the challenger of runtime 2. -/
noncomputable def challengedT (pub : Pub) {A B : QReg} {α : Type}
    (x : QComp (advSpec (X × Z)) A B α) : QComp (XSpec M) A B α :=
  IPFunctor.IFreeM.substitute (challengeT M upd pub) x

/-- The position of the public key's root. -/
def rootPos : ValPos :=
  tpos topLayer layerHeight 0

/-- **The SUF-CMA game as runtime 2 runs it, as a template**: reveal the root, run the adversary
on the public key against the challenger of runtime 2 with its signing transcript (the trials'
`h`-reads updating the memory with `upd`), verify the forgery through read ports, and return the
winning condition. `realizeT v (gameT M upd pub A)` is the game at the hidden values `v`. -/
noncomputable def gameT (pub : Pub) (A : Adversary (X × Z)) :
    QComp (XSpec M) (QReg.of Unit) (QReg.of Unit) Bool :=
  revealThen goodAll {.inl rootPos} fun r₀ ↦
    (challengedT M upd pub (withSignLog (A ⟨extendVals r₀.1 rootPos, pub.param⟩))).bind fun run ↦
      (readLiftQ goodAll ((readsProgram M pub.perm _ (schemeWithHashFromSeed.verify
        ⟨extendVals r₀.1 rootPos, pub.param⟩ run.1)).map Prod.fst)).bind fun verified ↦
        QuantumComp₂.pure (sufCmaScheme.winningCondition run.2 run.1 && verified)

/-- **The challenge prefix of the game**: reveal the root and run the adversary on the public key
against the challenger of runtime 2 with its signing transcript; return the public key, the
forgery and the transcript. -/
noncomputable def prefixT (pub : Pub) (A : Adversary (X × Z)) :
    QComp (XSpec M) (QReg.of Unit) (QReg.of Unit) (PublicKey × (Forgery × SignLog)) :=
  revealThen goodAll {.inl rootPos} fun r₀ ↦
    (challengedT M upd pub (withSignLog (A ⟨extendVals r₀.1 rootPos, pub.param⟩))).bind fun run ↦
      QuantumComp₂.pure (⟨extendVals r₀.1 rootPos, pub.param⟩, run)

/-- **The verification of the game**: verify the forgery under the public key through read ports
and return the winning condition. -/
noncomputable def verifyT (pub : Pub) (x : PublicKey × (Forgery × SignLog)) :
    QComp (XSpec M) (QReg.of Unit) (QReg.of Unit) Bool :=
  (readLiftQ goodAll ((readsProgram M pub.perm _ (schemeWithHashFromSeed.verify x.1 x.2.1)).map
    Prod.fst)).bind fun verified ↦
    QuantumComp₂.pure (sufCmaScheme.winningCondition x.2.2 x.2.1 && verified)

omit [Fintype M] [DecidableEq M] in
/-- **The game is its challenge prefix, then the verification.** -/
theorem gameT_eq_prefixT_bind (pub : Pub) (A : Adversary (X × Z)) :
    gameT M upd pub A = (prefixT M upd pub A).bind (verifyT M pub) := by
  simp only [gameT, prefixT, revealThen_bind, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
  rfl

/-! ### The game reveals before it programs -/

omit [Fintype M] [DecidableEq M] in
theorem disc_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) (T : Finset HPos)
    (h : ∀ p ∈ ps, p.need ⊆ T) : Disc (progPorts M B ps) T := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact disc_progThen p trivial _ T (h p List.mem_cons_self)
      (ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

omit [Fintype M] [DecidableEq M] in
theorem disc_progSlots (pub : Pub) (B : QReg) (ss : List Slot) (T : Finset HPos)
    (h : ∀ s ∈ ss, inlSet (slotNeed s) ⊆ T) : Disc (progSlots M pub B ss) T := by
  induction ss generalizing T with
  | nil => trivial
  | cons s ss ih =>
    refine disc₂_bind _ _ (disc_progPorts M B _ T fun p hp ↦ ?_) fun _ T' hT' ↦
      ih T' fun s' hs' ↦ (h s' (List.mem_cons_of_mem _ hs')).trans hT'
    rw [need_of_mem_slotPorts hp]
    exact h s List.mem_cons_self

omit [Fintype M] [DecidableEq M] in
theorem disc_signLayerT (pub : Pub) (B : QReg) (lab : RLabel) (T : Finset HPos) :
    Disc (signLayerT M upd pub B lab) T := by
  refine disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _ (disc_readLift _ _) fun g T' _ ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · trivial
  · refine disc_revealThen _ _ T' fun r ↦ disc₂_bind _ _ (disc_progSlots M pub B _ _ fun s hs ↦ ?_)
      fun _ _ _ ↦ trivial
    exact (inlSet_mono ((slotNeed_subset_needUnion hs).trans (Finset.subset_union_left.trans
      Finset.subset_union_left))).trans Finset.subset_union_right

omit [Fintype M] [DecidableEq M] in
theorem disc_signT (pub : Pub) (B : QReg) (r : SigningRequest) (T : Finset HPos) :
    Disc (signT M upd pub B r) T := by
  refine disc₂_bind _ _ (disc_signLayerT M upd pub B _ T) fun b T' _ ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · trivial
  · refine disc₂_bind _ _ (disc_signLayerT M upd pub B _ T') fun t _ _ ↦ ?_
    rcases t with _ | ⟨top, _⟩ <;> trivial

omit [Fintype M] [DecidableEq M] in
theorem disc_challengeT (pub : Pub) (A : QReg) (c : QuantumComp.Cmd LocalSig.instruments.{0}
    (advSpec (X × Z)) A) (T : Finset HPos) : Disc (challengeT M upd pub A c) T := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact disc_readLift _ _
  · exact disc_readLift _ _
  · exact disc_bind _ _ (disc₂_bind _ _ (disc_act _ _) fun _ T' _ ↦ disc_signT M upd pub _ r T')
      fun _ _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The game reveals before it programs**: every program port hardwires a cell of a slot whose
coordinates the layer signature revealed just before. -/
theorem disc_gameT (pub : Pub) (A : Adversary (X × Z)) (T : Finset HPos) :
    Disc (gameT M upd pub A) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _ (disc_substitute _ (disc_challengeT M upd pub) _ _)
    fun _ _ _ ↦ disc₂_bind _ _ (disc_readLift _ _) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix reveals before it programs. -/
theorem disc_prefixT (pub : Pub) (A : Adversary (X × Z)) (T : Finset HPos) :
    Disc (prefixT M upd pub A) T :=
  disc_revealThen _ _ T fun _ ↦ disc₂_bind _ _ (disc_substitute _ (disc_challengeT M upd pub) _ _)
    fun _ _ _ ↦ trivial

/-- **The lazy-sampling property of the runtime-2 game.** For every initial state that does not
depend on the hidden values, the realized games satisfy `ViewBy` for runtime 2 with record ports
and the memory label, at every call. -/
theorem viewBy_gameT (pub : Pub) (A : Adversary (X × Z)) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (j : ℕ) :
    ViewBy (runtimeR m₀) LocalSig.Interp.instruments (fun r ↦ r.2.2.1)
      (fun v ↦ realizeT v (gameT M upd pub A)) (fun _ ↦ ρ) j :=
  viewBy_runtimeR_of_disc _ m₀ (gameT M upd pub A) ∅ (disc_gameT M upd pub A ∅) (fun _ ↦ ρ)
    (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ) j

/-- **`ViewByOn` for the runtime-2 game**, the `hview` hypothesis of `Disclose`'s mass bounds for
the weights vanishing on the program ports. -/
theorem viewByOn_gameT (pub : Pub) (A : Adversary (X × Z)) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (j : ℕ) :
    ViewByOn (runtimeR m₀) LocalSig.Interp.instruments (fun i ↦ i.isLeft = true)
      (fun r ↦ r.2.2.1) (fun v ↦ realizeT v (gameT M upd pub A)) (fun _ ↦ ρ) j :=
  (viewBy_gameT M upd pub A m₀ ρ j).viewByOn _

end xmss

end Quantum.Xmss.Assembly

end
