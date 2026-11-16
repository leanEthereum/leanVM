module

public import Quantum.Xmss.Assembly.Template
public import Quantum.Xmss.Hybrid.SchemeSeed

@[expose] public section

/-!
# Reparametrizing the table into public data and hidden values

The averaging of `Quantum.Xmss.Hybrid.Disclose` (`avg_le_of_sum_le`, `sum_queryWeight_view_le`)
needs the table as public data and independent uniform hidden values. Here the hidden values are
the honest outputs' digests and the public data is the table with each honest output's digest
replaced, at its output capacity, by an extra uniform pad.

**Over abstract types.** A table is `((h, u), w)`: the rate key `h : Z → X`, a pad `u : S → D` (one
uniform digest per position) and the rest `w`. `Outputs` names the in-table output positions `I`,
the table's values `val w h u` (on `I` the outputs, elsewhere read from the pad: junk positions,
or coordinates such as chain starts that an earlier reparametrization made uniform), and the
output cell `cap w h v s` and rate `rate w h v s` of each output, computed from the values `v` (the
payloads). `DigestFix` is the digest of a cell value (`dig r w`, the digest of the output rate
`r + w`) and its correction (`cor r w d`, the same cell value with digest `d`).

* `fwd`: `((h, u), w) ↦ ((h'', w), v)` with `v = val w h u` and `h''` equal to `h` except at the
  output cells, where the digest is replaced by the pad (`cor r (h c) (u s)`). `back` inverts it,
  computing the cells from the public data and the hidden values.
* `Good`: the output cells are distinct and the paths are local (`Local`: changing `h` off the
  output cells changes no output cell or rate). `back_fwd`: `back (fwd θ) = θ` on `Good`.
  `GoodPV` is the same condition in the coordinates `((h'', w), v)`; with the values ranked
  (`Ranked`: an output's cell depends on lower values only), `fwd` and `back` are inverse
  bijections between `Good` and `GoodPV` (`goodPV_fwd`, `good_back`, `fwd_back`,
  `card_good_eq`), so the bad fraction may be counted where the hidden values are fixed
  (`card_not_good_eq`).
* The coordinates: the hidden coordinate is the table's values (`fwd_snd`); the public data keeps
  `w` (`fwd_fst_snd`) and `h` off the output cells (`fwd_fst_fst_of_ne`); on `Good`, the output
  cells and rates computed from the public data and the hidden values are the table's
  (`cap_fwd`, `rate_fwd`), and the correction gives back `h` there (`cor_fwd`).
* `uavg_le_of_good` (**the averaging corollary**): for a good set `G ⊆ Good`, the average over the
  tables of `f` is at most the average over the public data of the average over the hidden values
  of `g`, plus the fraction of tables outside `G`, if `f ≤ g ∘ fwd` on `G` and `f ≤ 1` elsewhere;
  `uavg_le_of_good_of_sum_le`: with `∑ v, g (p, v) ≤ κ |V|`, at most `κ` plus the bad fraction.
  `uavg_pad`: a quantity that ignores the pad has the same average with or without it.
  `GoodWith`, `GoodPVWith`: good sets given by a path condition preserved off the output cells;
  `card_not_eq_of_maps`: their bad fractions agree in both coordinates.
* `card_mul_filter_capOf_le`: output cells `capOf k k' π (cell q s)` with `cell q` injective on `I`
  (the cells fixed by the coordinates `q` other than `k`, `k'`) collide for at most
  `|I|² (G + 1) / |Z|` of the coordinates, for a `PermGood π G` permutation.

**leanXMSS.** Positions `ValPos`, digests `Digest`, rest `XW` = (public parameter, `π`, `k`, `k'`).

* `xmssFix`: `dig r w = trunc128 (r + w)`, `cor r w d = w + embed128 (d ^^^ trunc128 (r + w))`,
  `Template.roundH`'s correction (`roundH_last`).
* `xO`: the in-table outputs `xI` (`InPos`: chain positions `1` to `3` of the table's keys, tree
  values in range), the slot of each (`outSlot`), its output cell and rate (`outCap`, `outRate`:
  the last round of `Template`'s honest path at `xPub w h`), and the table's values `xVal`
  (`chainV`, `treeV` from the chain starts in the pad, as `HonestTable`). `xO_consistent`,
  `xO_ranked` (`xRank`).
* The good set `XGood`: distinct output cells and `PathsAvoid` (no `h`-cell of an earlier round of
  an in-table path is an output cell), which gives `Local` (`local_of_pathsAvoid`).
* `rounds_fwd`: on `XGood`, the template's `k`, `k'`, `h` program-port values at the public data
  and the hidden values of `fwd` are those at the table's own data (`rounds_congr`), which are the
  table's honest cells (`roundH_table`: the correction vanishes).
* `xVal_wOf`, `pubOf_eq`: for an honest table `L` with its chain starts in the pad, the table's
  values on `xI` are `valueAt L`, and `pubOf L` is `xPub (wOf L) L.keys.1` with `L`'s randomizer
  bases.
* `xGood_bad_frac_le`: the bad fraction is at most the bad permutations, the one-block output-cell
  collisions `|xI₁|² (G + 1) / |Z|` (`card_mul_capColl_le`; chain steps and nodes are one block,
  `outCap_one`, with distinct first blocks, `cellOf_injOn`), and the fraction of public
  coordinates in `PathBad` (a leaf's output cell collides, or `PathsAvoid` fails), which is the
  multi-block path analysis and is not bounded here. `uavg_le_xmss` combines it with the
  averaging corollary.
-/

open scoped ENNReal

namespace Quantum.Xmss.Assembly

open Quantum Quantum.Sponge Quantum.Xmss.Hybrid

/-! ## Over abstract types -/

section generic

/-- **A digest correction** on cell values `X` with digests `D`: `dig r w` is the digest of the
output rate `r + w`, `cor r w d` the cell value agreeing with `w` off the digest, with digest
`d`. -/
structure DigestFix (X D : Type*) where
  /-- The digest of the output rate `r + w`. -/
  dig : X → X → D
  /-- The cell value `w` with its digest replaced by `d`. -/
  cor : X → X → D → X
  dig_cor : ∀ r w d, dig r (cor r w d) = d
  cor_cor : ∀ r w d, cor r (cor r w d) (dig r w) = w

variable {X Z D S W : Type*} [DecidableEq S]

open scoped Classical in
/-- The function `h` with the value `nv s` at each cell `c s`, `s ∈ I`. -/
noncomputable def setAt (I : Finset S) (c : S → Z) (nv : S → X) (h : Z → X) (z : Z) : X :=
  if hz : ∃ s ∈ I, c s = z then nv hz.choose else h z

omit [DecidableEq S] in
theorem setAt_of_mem {I : Finset S} {c : S → Z} (nv : S → X) (h : Z → X)
    (hc : Set.InjOn c I) {s : S} (hs : s ∈ I) : setAt I c nv h (c s) = nv s := by
  have hz : ∃ t ∈ I, c t = c s := ⟨s, hs, rfl⟩
  unfold setAt
  rw [dite_eq_left hz]
  obtain ⟨ht, hcs⟩ := hz.choose_spec
  rw [hc ht hs hcs]

omit [DecidableEq S] in
theorem setAt_of_forall_ne {I : Finset S} {c : S → Z} (nv : S → X) (h : Z → X) {z : Z}
    (hz : ∀ s ∈ I, c s ≠ z) : setAt I c nv h z = h z := by
  unfold setAt
  rw [dite_eq_right]
  rintro ⟨s, hs, e⟩
  exact hz s hs e

/-- **The honest outputs of a table** `((h, u), w)`: the in-table output positions `I`, the table's
values `val w h u`, and each output's cell `cap w h v s` and rate `rate w h v s`, computed from the
values `v`. -/
structure Outputs (X Z D S W : Type*) where
  /-- The in-table output positions. -/
  I : Finset S
  /-- The table's values. -/
  val : W → (Z → X) → (S → D) → S → D
  /-- The cell of `h` at which an output is read, from the values. -/
  cap : W → (Z → X) → (S → D) → S → Z
  /-- The rate an output's cell value is added to, from the values. -/
  rate : W → (Z → X) → (S → D) → S → X

variable (F : DigestFix X D) (O : Outputs X Z D S W)

/-- The table's values: the outputs' digests on `I`, the pad elsewhere. -/
def Outputs.Consistent : Prop :=
  ∀ w h u s, O.val w h u s = if s ∈ O.I then
    F.dig (O.rate w h (O.val w h u) s) (h (O.cap w h (O.val w h u) s)) else u s

/-- **Ranked values**: an output's cell and rate depend on the values of lower rank only. -/
def Outputs.Ranked (rank : S → ℕ) : Prop :=
  ∀ w h (v v' : S → D), ∀ s ∈ O.I, (∀ t, rank t < rank s → v t = v' t) →
    O.cap w h v s = O.cap w h v' s ∧ O.rate w h v s = O.rate w h v' s

/-- `h₂` agrees with `h` off the cells `c s`, `s ∈ I`. -/
def AgreeOff (I : Finset S) (c : S → Z) (h h₂ : Z → X) : Prop :=
  ∀ z, (∀ s ∈ I, c s ≠ z) → h₂ z = h z

/-- **Local paths**: changing `h` off the output cells changes no output's cell or rate. -/
def Outputs.Local (w : W) (h : Z → X) (v : S → D) : Prop :=
  ∀ h₂, AgreeOff O.I (O.cap w h v) h h₂ → ∀ s ∈ O.I,
    O.cap w h₂ v s = O.cap w h v s ∧ O.rate w h₂ v s = O.rate w h v s

/-- **The good set, in the public coordinates** `((h'', w), v)`: distinct output cells and local
paths. -/
def Outputs.GoodPV (y : ((Z → X) × W) × (S → D)) : Prop :=
  Set.InjOn (O.cap y.1.2 y.1.1 y.2) O.I ∧ O.Local y.1.2 y.1.1 y.2

/-- **The good set of tables**: distinct output cells and local paths, at the table's values. -/
def Outputs.Good (θ : ((Z → X) × (S → D)) × W) : Prop :=
  O.GoodPV ((θ.1.1, θ.2), O.val θ.2 θ.1.1 θ.1.2)

/-- **The reparametrization**: the hidden coordinate is the table's values; the public data is `w`
and `h` with the digest at each output cell replaced by the pad. -/
noncomputable def fwd (θ : ((Z → X) × (S → D)) × W) : ((Z → X) × W) × (S → D) :=
  ((setAt O.I (O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2))
      (fun s ↦ F.cor (O.rate θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s)
        (θ.1.1 (O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s)) (θ.1.2 s)) θ.1.1, θ.2),
    O.val θ.2 θ.1.1 θ.1.2)

/-- **The inverse**: the output cells from the public data and the hidden values, the hidden
values written into their digests, the pads read off. -/
noncomputable def back (y : ((Z → X) × W) × (S → D)) : ((Z → X) × (S → D)) × W :=
  ((setAt O.I (O.cap y.1.2 y.1.1 y.2)
      (fun s ↦ F.cor (O.rate y.1.2 y.1.1 y.2 s) (y.1.1 (O.cap y.1.2 y.1.1 y.2 s)) (y.2 s)) y.1.1,
    fun s ↦ if s ∈ O.I then F.dig (O.rate y.1.2 y.1.1 y.2 s) (y.1.1 (O.cap y.1.2 y.1.1 y.2 s))
      else y.2 s), y.1.2)

omit [DecidableEq S] in
theorem fwd_snd (θ : ((Z → X) × (S → D)) × W) : (fwd F O θ).2 = O.val θ.2 θ.1.1 θ.1.2 :=
  rfl

omit [DecidableEq S] in
theorem fwd_fst_snd (θ : ((Z → X) × (S → D)) × W) : (fwd F O θ).1.2 = θ.2 :=
  rfl

omit [DecidableEq S] in
theorem fwd_fst_fst (θ : ((Z → X) × (S → D)) × W) :
    (fwd F O θ).1.1 = setAt O.I (O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2))
      (fun s ↦ F.cor (O.rate θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s)
        (θ.1.1 (O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s)) (θ.1.2 s)) θ.1.1 :=
  rfl

theorem back_snd (y : ((Z → X) × W) × (S → D)) : (back F O y).2 = y.1.2 :=
  rfl

theorem back_fst_fst (y : ((Z → X) × W) × (S → D)) :
    (back F O y).1.1 = setAt O.I (O.cap y.1.2 y.1.1 y.2)
      (fun s ↦ F.cor (O.rate y.1.2 y.1.1 y.2 s) (y.1.1 (O.cap y.1.2 y.1.1 y.2 s)) (y.2 s)) y.1.1 :=
  rfl

theorem back_fst_snd (y : ((Z → X) × W) × (S → D)) (s : S) :
    (back F O y).1.2 s = if s ∈ O.I then
      F.dig (O.rate y.1.2 y.1.1 y.2 s) (y.1.1 (O.cap y.1.2 y.1.1 y.2 s)) else y.2 s :=
  rfl

omit [DecidableEq S] in
/-- The public `h` is the table's off the output cells. -/
theorem fwd_fst_fst_of_ne (θ : ((Z → X) × (S → D)) × W) {z : Z}
    (hz : ∀ s ∈ O.I, O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s ≠ z) :
    (fwd F O θ).1.1 z = θ.1.1 z := by
  rw [fwd_fst_fst]
  exact setAt_of_forall_ne _ _ hz

omit [DecidableEq S] in
/-- At an output cell, the public `h` is the table's with the digest replaced by the pad. -/
theorem fwd_fst_fst_cap (θ : ((Z → X) × (S → D)) × W)
    (hinj : Set.InjOn (O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2)) O.I) {s : S} (hs : s ∈ O.I) :
    (fwd F O θ).1.1 (O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s) =
      F.cor (O.rate θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s)
        (θ.1.1 (O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s)) (θ.1.2 s) := by
  rw [fwd_fst_fst]
  exact setAt_of_mem _ _ hinj hs

theorem back_fst_fst_cap (y : ((Z → X) × W) × (S → D))
    (hinj : Set.InjOn (O.cap y.1.2 y.1.1 y.2) O.I) {s : S} (hs : s ∈ O.I) :
    (back F O y).1.1 (O.cap y.1.2 y.1.1 y.2 s) =
      F.cor (O.rate y.1.2 y.1.1 y.2 s) (y.1.1 (O.cap y.1.2 y.1.1 y.2 s)) (y.2 s) := by
  rw [back_fst_fst]
  exact setAt_of_mem _ _ hinj hs

omit [DecidableEq S] in
theorem AgreeOff.trans {I : Finset S} {c : S → Z} {h₁ h₂ h₃ : Z → X}
    (h₁₂ : AgreeOff I c h₁ h₂) (h₂₃ : AgreeOff I c h₂ h₃) : AgreeOff I c h₁ h₃ :=
  fun z hz ↦ (h₂₃ z hz).trans (h₁₂ z hz)

omit [DecidableEq S] in
theorem AgreeOff.congr {I : Finset S} {c c' : S → Z} {h₁ h₂ : Z → X} (h : AgreeOff I c h₁ h₂)
    (hc : ∀ s ∈ I, c' s = c s) : AgreeOff I c' h₁ h₂ :=
  fun z hz ↦ h z fun s hs ↦ (hc s hs) ▸ hz s hs

omit [DecidableEq S] in
/-- The public `h` agrees with the table's off the output cells. -/
theorem agreeOff_fwd (θ : ((Z → X) × (S → D)) × W) :
    AgreeOff O.I (O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2)) θ.1.1 (fwd F O θ).1.1 :=
  fun _ hz ↦ fwd_fst_fst_of_ne F O θ hz

/-- The table's `h` from the public coordinates agrees with the public `h` off the output cells. -/
theorem agreeOff_back (y : ((Z → X) × W) × (S → D)) :
    AgreeOff O.I (O.cap y.1.2 y.1.1 y.2) y.1.1 (back F O y).1.1 := fun _ hz ↦ by
  rw [back_fst_fst]
  exact setAt_of_forall_ne _ _ hz

variable {F O}

omit [DecidableEq S] in
/-- On `Good`, the output cells computed from the public data and the hidden values are the
table's. -/
theorem cap_fwd {θ : ((Z → X) × (S → D)) × W} (hθ : O.Good θ) {s : S} (hs : s ∈ O.I) :
    O.cap (fwd F O θ).1.2 (fwd F O θ).1.1 (fwd F O θ).2 s =
      O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s :=
  (hθ.2 _ (agreeOff_fwd F O θ) s hs).1

omit [DecidableEq S] in
/-- On `Good`, the output rates computed from the public data and the hidden values are the
table's. -/
theorem rate_fwd {θ : ((Z → X) × (S → D)) × W} (hθ : O.Good θ) {s : S} (hs : s ∈ O.I) :
    O.rate (fwd F O θ).1.2 (fwd F O θ).1.1 (fwd F O θ).2 s =
      O.rate θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s :=
  (hθ.2 _ (agreeOff_fwd F O θ) s hs).2

/-- **The correction gives back the table**: on `Good`, at each output cell, the public value
corrected by the hidden value is the table's value of `h`. -/
theorem cor_fwd (hC : O.Consistent F) {θ : ((Z → X) × (S → D)) × W} (hθ : O.Good θ) {s : S}
    (hs : s ∈ O.I) :
    F.cor (O.rate (fwd F O θ).1.2 (fwd F O θ).1.1 (fwd F O θ).2 s)
        ((fwd F O θ).1.1 (O.cap (fwd F O θ).1.2 (fwd F O θ).1.1 (fwd F O θ).2 s))
        ((fwd F O θ).2 s) =
      θ.1.1 (O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s) := by
  rw [cap_fwd hθ hs, rate_fwd hθ hs, fwd_fst_fst_cap F O θ hθ.1 hs, fwd_snd,
    hC θ.2 θ.1.1 θ.1.2 s, ite_eq_left hs, F.cor_cor]

/-- **The inverse on the good set**: `back (fwd θ) = θ`. -/
theorem back_fwd (hC : O.Consistent F) {θ : ((Z → X) × (S → D)) × W} (hθ : O.Good θ) :
    back F O (fwd F O θ) = θ := by
  have hcap : ∀ s ∈ O.I, O.cap (fwd F O θ).1.2 (fwd F O θ).1.1 (fwd F O θ).2 s =
      O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s := fun s hs ↦ cap_fwd hθ hs
  have hinj : Set.InjOn (O.cap (fwd F O θ).1.2 (fwd F O θ).1.1 (fwd F O θ).2) O.I :=
    fun a ha b hb e ↦ hθ.1 ha hb ((hcap a ha).symm.trans (e.trans (hcap b hb)))
  refine Prod.ext (Prod.ext (funext fun z ↦ ?_) (funext fun s ↦ ?_)) rfl
  · by_cases hz : ∃ s ∈ O.I, O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s = z
    · obtain ⟨s, hs, rfl⟩ := hz
      conv_lhs => rw [← hcap s hs]
      rw [back_fst_fst_cap F O _ hinj hs]
      exact cor_fwd hC hθ hs
    · have hz' : ∀ s ∈ O.I, O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s ≠ z :=
        fun s hs e ↦ hz ⟨s, hs, e⟩
      rw [back_fst_fst, setAt_of_forall_ne _ _ fun s hs ↦ (hcap s hs).symm ▸ hz' s hs]
      exact fwd_fst_fst_of_ne F O θ hz'
  · rw [back_fst_snd]
    split_ifs with hs
    · rw [hcap s hs, rate_fwd hθ hs, fwd_fst_fst_cap F O θ hθ.1 hs, F.dig_cor]
    · rw [fwd_snd, hC, ite_eq_right hs]

theorem injOn_fwd (hC : O.Consistent F) : Set.InjOn (fwd F O) {θ | O.Good θ} :=
  fun a ha b hb e ↦ by rw [← back_fwd hC ha, ← back_fwd hC hb, e]

omit [DecidableEq S] in
/-- `fwd` maps the good set into the good set of the public coordinates. -/
theorem goodPV_fwd {θ : ((Z → X) × (S → D)) × W} (hθ : O.Good θ) : O.GoodPV (fwd F O θ) := by
  have hcap : ∀ s ∈ O.I, O.cap (fwd F O θ).1.2 (fwd F O θ).1.1 (fwd F O θ).2 s =
      O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2) s := fun s hs ↦ cap_fwd hθ hs
  refine ⟨fun a ha b hb e ↦ hθ.1 ha hb ((hcap a ha).symm.trans (e.trans (hcap b hb))),
    fun h₂ h₂' s hs ↦ ?_⟩
  have hag : AgreeOff O.I (O.cap θ.2 θ.1.1 (O.val θ.2 θ.1.1 θ.1.2)) θ.1.1 h₂ :=
    (agreeOff_fwd F O θ).trans (h₂'.congr fun t ht ↦ (hcap t ht).symm)
  obtain ⟨e1, e2⟩ := hθ.2 h₂ hag s hs
  exact ⟨e1.trans (hcap s hs).symm, e2.trans (rate_fwd hθ hs).symm⟩

/-- From the public coordinates, the table's values are the hidden values (by induction on the
rank). -/
theorem val_back (hC : O.Consistent F) {rank : S → ℕ} (hR : O.Ranked rank)
    {y : ((Z → X) × W) × (S → D)} (hy : O.GoodPV y) :
    O.val (back F O y).2 (back F O y).1.1 (back F O y).1.2 = y.2 := by
  have hloc := hy.2 _ (agreeOff_back F O y)
  rw [back_snd]
  funext s
  induction hn : rank s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    rw [hC]
    split_ifs with hs
    · have hlow := hR y.1.2 (back F O y).1.1 (O.val y.1.2 (back F O y).1.1 (back F O y).1.2) y.2
        s hs fun t ht ↦ ih (rank t) (hn ▸ ht) t rfl
      rw [hlow.1, hlow.2, (hloc s hs).1, (hloc s hs).2, back_fst_fst_cap F O y hy.1 hs, F.dig_cor]
    · rw [back_fst_snd, ite_eq_right hs]

/-- `back` maps the good set of the public coordinates into the good set. -/
theorem good_back (hC : O.Consistent F) {rank : S → ℕ} (hR : O.Ranked rank)
    {y : ((Z → X) × W) × (S → D)} (hy : O.GoodPV y) : O.Good (back F O y) := by
  have hv := val_back hC hR hy
  have hag := agreeOff_back F O y
  have hloc := hy.2 _ hag
  unfold Outputs.Good
  rw [hv]
  refine ⟨fun a ha b hb e ↦ hy.1 ha hb ((hloc a ha).1.symm.trans (e.trans (hloc b hb).1)),
    fun h₂ h₂' s hs ↦ ?_⟩
  have hag₂ : AgreeOff O.I (O.cap y.1.2 y.1.1 y.2) y.1.1 h₂ :=
    hag.trans (h₂'.congr fun t ht ↦ ((hloc t ht).1).symm)
  obtain ⟨e1, e2⟩ := hy.2 h₂ hag₂ s hs
  exact ⟨e1.trans (hloc s hs).1.symm, e2.trans (hloc s hs).2.symm⟩

/-- **The inverse on the good set of the public coordinates**: `fwd (back y) = y`. -/
theorem fwd_back (hC : O.Consistent F) {rank : S → ℕ} (hR : O.Ranked rank)
    {y : ((Z → X) × W) × (S → D)} (hy : O.GoodPV y) : fwd F O (back F O y) = y := by
  have hv := val_back hC hR hy
  have hloc := hy.2 _ (agreeOff_back F O y)
  refine Prod.ext (Prod.ext (funext fun z ↦ ?_) rfl) hv
  rw [fwd_fst_fst, hv, back_snd]
  have hinj : Set.InjOn (O.cap y.1.2 (back F O y).1.1 y.2) O.I := fun a ha b hb e ↦
    hy.1 ha hb ((hloc a ha).1.symm.trans (e.trans (hloc b hb).1))
  by_cases hz : ∃ s ∈ O.I, O.cap y.1.2 y.1.1 y.2 s = z
  · obtain ⟨s, hs, rfl⟩ := hz
    rw [← (hloc s hs).1, setAt_of_mem _ _ hinj hs]
    rw [(hloc s hs).1, (hloc s hs).2, back_fst_fst_cap F O y hy.1 hs, back_fst_snd,
      ite_eq_left hs, F.cor_cor]
  · have hz' : ∀ s ∈ O.I, O.cap y.1.2 y.1.1 y.2 s ≠ z := fun s hs e ↦ hz ⟨s, hs, e⟩
    rw [setAt_of_forall_ne _ _ fun s hs ↦ (hloc s hs).1.symm ▸ hz' s hs]
    exact agreeOff_back F O y z hz'

/-! ### Good sets given by a path condition -/

section pathCond

variable (O) in
/-- The good set in the public coordinates for a path condition `Pth`: distinct output cells and
`Pth`. -/
def Outputs.GoodPVWith (Pth : W → (Z → X) → (S → D) → Prop)
    (y : ((Z → X) × W) × (S → D)) : Prop :=
  Set.InjOn (O.cap y.1.2 y.1.1 y.2) O.I ∧ Pth y.1.2 y.1.1 y.2

variable (O) in
/-- The good set of tables for a path condition `Pth`. -/
def Outputs.GoodWith (Pth : W → (Z → X) → (S → D) → Prop)
    (θ : ((Z → X) × (S → D)) × W) : Prop :=
  O.GoodPVWith Pth ((θ.1.1, θ.2), O.val θ.2 θ.1.1 θ.1.2)

variable {Pth : W → (Z → X) → (S → D) → Prop} (hPL : ∀ w h v, Pth w h v → O.Local w h v)
  (hPC : ∀ w h h₂ v, Pth w h v → AgreeOff O.I (O.cap w h v) h h₂ → Pth w h₂ v)
include hPL

omit [DecidableEq S] in
theorem goodPV_of_with {y : ((Z → X) × W) × (S → D)} (hy : O.GoodPVWith Pth y) : O.GoodPV y :=
  ⟨hy.1, hPL _ _ _ hy.2⟩

omit [DecidableEq S] in
theorem good_of_with {θ : ((Z → X) × (S → D)) × W} (hθ : O.GoodWith Pth θ) : O.Good θ :=
  goodPV_of_with hPL hθ

include hPC

omit [DecidableEq S] in
theorem goodPVWith_fwd {θ : ((Z → X) × (S → D)) × W} (hθ : O.GoodWith Pth θ) :
    O.GoodPVWith Pth (fwd F O θ) :=
  ⟨(goodPV_fwd (good_of_with hPL hθ)).1, hPC _ _ _ _ hθ.2 (agreeOff_fwd F O θ)⟩

theorem goodWith_back (hC : O.Consistent F) {rank : S → ℕ} (hR : O.Ranked rank)
    {y : ((Z → X) × W) × (S → D)} (hy : O.GoodPVWith Pth y) : O.GoodWith Pth (back F O y) := by
  have hv := val_back hC hR (goodPV_of_with hPL hy)
  refine ⟨(good_back hC hR (goodPV_of_with hPL hy)).1, ?_⟩
  show Pth y.1.2 (back F O y).1.1 (O.val (back F O y).2 (back F O y).1.1 (back F O y).1.2)
  rw [hv]
  exact hPC _ _ _ _ hy.2 (agreeOff_back F O y)

end pathCond

section count

variable [Fintype X] [Fintype Z] [DecidableEq Z] [Fintype D] [Fintype S] [Fintype W]

open scoped Classical

/-- **The good sets correspond**: the tables of `Good` and the public coordinates of `GoodPV` are
equally many. -/
theorem card_good_eq (hC : O.Consistent F) {rank : S → ℕ} (hR : O.Ranked rank) :
    (Finset.univ.filter fun θ ↦ O.Good θ).card =
      (Finset.univ.filter fun y ↦ O.GoodPV y).card := by
  refine Finset.card_nbij' (fwd F O) (back F O) (fun θ hθ ↦ ?_) (fun y hy ↦ ?_)
    (fun θ hθ ↦ ?_) (fun y hy ↦ ?_)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hθ ⊢
    exact goodPV_fwd hθ
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    exact good_back hC hR hy
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hθ
    exact back_fwd hC hθ
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
    exact fwd_back hC hR hy

theorem card_tab_eq :
    Fintype.card (((Z → X) × (S → D)) × W) = Fintype.card (((Z → X) × W) × (S → D)) := by
  simp only [Fintype.card_prod]
  ring

/-- **The bad fraction in the public coordinates**: as many tables are outside `Good` as public
coordinates are outside `GoodPV`. -/
theorem card_not_good_eq (hC : O.Consistent F) {rank : S → ℕ} (hR : O.Ranked rank) :
    (Finset.univ.filter fun θ ↦ ¬O.Good θ).card =
      (Finset.univ.filter fun y ↦ ¬O.GoodPV y).card := by
  rw [Finset.filter_not, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _), card_good_eq hC hR, Finset.card_univ,
    Finset.card_univ, card_tab_eq]

/-- **The bad fraction of smaller good sets**: for good sets `G ⊆ Good` and `GP ⊆ GoodPV` that
`fwd` and `back` map into each other, as many tables are outside `G` as public coordinates outside
`GP`. -/
theorem card_not_eq_of_maps (hC : O.Consistent F) {rank : S → ℕ} (hR : O.Ranked rank)
    (G : ((Z → X) × (S → D)) × W → Prop) (GP : ((Z → X) × W) × (S → D) → Prop)
    (hG : ∀ θ, G θ → O.Good θ) (hGP : ∀ y, GP y → O.GoodPV y) (hf : ∀ θ, G θ → GP (fwd F O θ))
    (hb : ∀ y, GP y → G (back F O y)) :
    (Finset.univ.filter fun θ ↦ ¬G θ).card = (Finset.univ.filter fun y ↦ ¬GP y).card := by
  have hcard : (Finset.univ.filter fun θ ↦ G θ).card = (Finset.univ.filter fun y ↦ GP y).card := by
    refine Finset.card_nbij' (fwd F O) (back F O) (fun θ hθ ↦ ?_) (fun y hy ↦ ?_)
      (fun θ hθ ↦ ?_) (fun y hy ↦ ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hθ ⊢
      exact hf θ hθ
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
      exact hb y hy
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hθ
      exact back_fwd hC (hG θ hθ)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
      exact fwd_back hC hR (hGP y hy)
  rw [Finset.filter_not, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hcard, Finset.card_univ,
    Finset.card_univ, card_tab_eq]

/-- **The averaging corollary.** For a good set `G ⊆ Good`: if `f ≤ g ∘ fwd` on `G` and `f ≤ 1`
off it, the average of `f` over the tables is at most the average over the public data of the
average over the hidden values of `g`, plus the fraction of tables outside `G`. -/
theorem uavg_le_of_good (hC : O.Consistent F) (G : ((Z → X) × (S → D)) × W → Prop)
    (hG : ∀ θ, G θ → O.Good θ) (f : ((Z → X) × (S → D)) × W → ℝ≥0∞)
    (g : ((Z → X) × W) × (S → D) → ℝ≥0∞) (hfg : ∀ θ, G θ → f θ ≤ g (fwd F O θ))
    (hf : ∀ θ, ¬G θ → f θ ≤ 1) :
    uavg f ≤ uavg (fun p : (Z → X) × W ↦ uavg fun v : S → D ↦ g (p, v)) +
      (Fintype.card (((Z → X) × (S → D)) × W) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun θ ↦ ¬G θ).card := by
  set Gd := Finset.univ.filter fun θ ↦ G θ
  have hsplit : ∑ θ, f θ ≤ ∑ y, g y + (Finset.univ.filter fun θ ↦ ¬G θ).card := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ fun θ ↦ G θ]
    refine add_le_add ?_ ?_
    · calc ∑ θ ∈ Gd, f θ ≤ ∑ θ ∈ Gd, g (fwd F O θ) :=
            Finset.sum_le_sum fun θ hθ ↦ hfg θ (Finset.mem_filter.mp hθ).2
        _ = ∑ y ∈ Gd.image (fwd F O), g y :=
            (Finset.sum_image fun a ha b hb e ↦ injOn_fwd hC (hG a (Finset.mem_filter.mp ha).2)
              (hG b (Finset.mem_filter.mp hb).2) e).symm
        _ ≤ ∑ y, g y := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    · calc ∑ θ ∈ Finset.univ.filter (fun θ ↦ ¬G θ), f θ
          ≤ ∑ _θ ∈ Finset.univ.filter (fun θ ↦ ¬G θ), (1 : ℝ≥0∞) :=
            Finset.sum_le_sum fun θ hθ ↦ hf θ (Finset.mem_filter.mp hθ).2
        _ = _ := by simp
  have hcard : (Fintype.card (((Z → X) × (S → D)) × W) : ℝ≥0∞)⁻¹ =
      (Fintype.card ((Z → X) × W) : ℝ≥0∞)⁻¹ * (Fintype.card (S → D) : ℝ≥0∞)⁻¹ := by
    rw [card_tab_eq, Fintype.card_prod, Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  calc uavg f ≤ (Fintype.card (((Z → X) × (S → D)) × W) : ℝ≥0∞)⁻¹ *
        (∑ y, g y + (Finset.univ.filter fun θ ↦ ¬G θ).card) := by
        unfold uavg
        gcongr
    _ = _ := by
        rw [mul_add, Fintype.sum_prod_type, hcard]
        congr 1
        simp only [uavg, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun v _ ↦ ?_
        ring

/-- **The averaging corollary, with a bound per public datum**: if the hidden values sum `g` to at
most `κ |V|` for every public datum, the average of `f` is at most `κ` plus the bad fraction. -/
theorem uavg_le_of_good_of_sum_le [Nonempty D] (hC : O.Consistent F)
    (G : ((Z → X) × (S → D)) × W → Prop) (hG : ∀ θ, G θ → O.Good θ)
    (f : ((Z → X) × (S → D)) × W → ℝ≥0∞)
    (g : ((Z → X) × W) × (S → D) → ℝ≥0∞) (hfg : ∀ θ, G θ → f θ ≤ g (fwd F O θ))
    (hf : ∀ θ, ¬G θ → f θ ≤ 1) (κ : ℝ≥0∞)
    (hκ : ∀ p, ∑ v, g (p, v) ≤ κ * Fintype.card (S → D)) :
    uavg f ≤ κ + (Fintype.card (((Z → X) × (S → D)) × W) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun θ ↦ ¬G θ).card := by
  refine (uavg_le_of_good hC G hG f g hfg hf).trans (add_le_add ?_ le_rfl)
  have hV : (Fintype.card (S → D) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc uavg (fun p : (Z → X) × W ↦ uavg fun v : S → D ↦ g (p, v))
      ≤ uavg (fun _ : (Z → X) × W ↦ κ) := uavg_mono fun p ↦ by
        unfold uavg
        calc (Fintype.card (S → D) : ℝ≥0∞)⁻¹ * ∑ v, g (p, v)
            ≤ (Fintype.card (S → D) : ℝ≥0∞)⁻¹ * (κ * Fintype.card (S → D)) := by
              gcongr
              exact hκ p
          _ = κ := by
              rw [mul_comm κ, ← mul_assoc, ENNReal.inv_mul_cancel hV (ENNReal.natCast_ne_top _),
                one_mul]
    _ ≤ κ := by
        unfold uavg
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
        exact mul_le_of_le_one_left (by positivity) (ENNReal.inv_mul_le_one _)

end count

omit [DecidableEq S] in
/-- **The pad does not change averages** of quantities that ignore it. -/
theorem uavg_pad {A P : Type*} [Fintype A] [Fintype P] [Nonempty P] (f : A → ℝ≥0∞) :
    uavg (fun t : A × P ↦ f t.1) = uavg f := by
  have hP : (Fintype.card P : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold uavg
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, mul_assoc ((Fintype.card A : ℝ≥0∞)⁻¹),
    ← mul_assoc ((Fintype.card P : ℝ≥0∞)⁻¹), ENNReal.inv_mul_cancel hP (ENNReal.natCast_ne_top _),
    one_mul]

omit [DecidableEq S] in
/-- Moving two inner sums out, over finite sets. -/
theorem sum_comm_four_finset {α β γ δ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β)
    (u : Finset γ) (v : Finset δ) (f : α → β → γ → δ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a b c d =
      ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, f a b c d := by
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a b c d
      = ∑ a ∈ s, ∑ c ∈ u, ∑ d ∈ v, ∑ b ∈ t, f a b c d :=
        Finset.sum_congr rfl fun a _ ↦ by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_comm
    _ = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, f a b c d := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_comm

open scoped Classical in
/-- **Collisions of output cells fixed by the other coordinates.** Output cells
`capOf k k' (πf q) (cell q s)`, with `cell q` injective on `I`, collide for a `PermGood` permutation
on at most `|I|² (G + 1) / |Z|` of the keys `k, k'`, for every `q`. -/
theorem card_mul_sum_not_injOn_capOf_le {X' Z' Q : Type} [Fintype X'] [DecidableEq X']
    [Fintype Z'] [DecidableEq Z'] [AddCommGroup Z'] [Fintype Q] (I : Finset S)
    (πf : Q → Equiv.Perm (X' × Z')) (cell : Q → S → X') (hcell : ∀ q, Set.InjOn (cell q) I)
    (G : ℕ) :
    Fintype.card Z' * ∑ q, ∑ k : X' → Z', ∑ k' : X' → Z',
        (if PermGood (πf q) G ∧ ¬Set.InjOn (fun s ↦ capOf k k' (πf q) (cell q s)) I
          then 1 else 0) ≤
      Fintype.card Q * (Fintype.card (X' → Z') * Fintype.card (X' → Z')) *
        (I.card * I.card * (G + 1)) := by
  have hq : ∀ q, Fintype.card Z' * ∑ k : X' → Z', ∑ k' : X' → Z',
      (if PermGood (πf q) G ∧ ¬Set.InjOn (fun s ↦ capOf k k' (πf q) (cell q s)) I
        then 1 else 0) ≤
      Fintype.card (X' → Z') * Fintype.card (X' → Z') * (I.card * I.card * (G + 1)) := by
    intro q
    by_cases hG : PermGood (πf q) G
    · have hle : ∀ k k' : X' → Z',
          (if PermGood (πf q) G ∧ ¬Set.InjOn (fun s ↦ capOf k k' (πf q) (cell q s)) I
            then 1 else 0) ≤
          ∑ a ∈ I, ∑ b ∈ I, (if a ≠ b ∧ capOf k k' (πf q) (cell q a) =
            capOf k k' (πf q) (cell q b) then 1 else 0) := by
        intro k k'
        split_ifs with h
        · obtain ⟨-, hn⟩ := h
          simp only [Set.InjOn, not_forall] at hn
          obtain ⟨a, ha, b, hb, hab, hne⟩ := hn
          calc 1 = (if a ≠ b ∧ capOf k k' (πf q) (cell q a) = capOf k k' (πf q) (cell q b)
                then 1 else 0) := (ite_eq_left ⟨hne, hab⟩).symm
            _ ≤ ∑ b' ∈ I, (if a ≠ b' ∧ capOf k k' (πf q) (cell q a) =
                capOf k k' (πf q) (cell q b') then 1 else 0) :=
                Finset.single_le_sum (f := fun b' ↦ (if a ≠ b' ∧ capOf k k' (πf q) (cell q a) =
                  capOf k k' (πf q) (cell q b') then 1 else 0)) (fun _ _ ↦ Nat.zero_le _) hb
            _ ≤ _ := Finset.single_le_sum (f := fun a' ↦ ∑ b' ∈ I,
                (if a' ≠ b' ∧ capOf k k' (πf q) (cell q a') =
                  capOf k k' (πf q) (cell q b') then 1 else 0)) (fun _ _ ↦ Nat.zero_le _) ha
        · exact Nat.zero_le _
      have hab : ∀ a ∈ I, ∀ b ∈ I, Fintype.card Z' * ∑ k : X' → Z', ∑ k' : X' → Z',
          (if a ≠ b ∧ capOf k k' (πf q) (cell q a) = capOf k k' (πf q) (cell q b)
            then 1 else 0) ≤ Fintype.card (X' → Z') * Fintype.card (X' → Z') * (G + 1) := by
        intro a ha b hb
        by_cases h : a = b
        · simp [h]
        · have hc := card_mul_sum_capOf_eq_le (πf q) G hG fun e ↦ h (hcell q ha hb e)
          simpa only [ne_eq, h, not_false_eq_true, true_and] using hc
      calc Fintype.card Z' * ∑ k : X' → Z', ∑ k' : X' → Z',
            (if PermGood (πf q) G ∧ ¬Set.InjOn (fun s ↦ capOf k k' (πf q) (cell q s)) I
              then 1 else 0)
          ≤ Fintype.card Z' * ∑ k : X' → Z', ∑ k' : X' → Z', ∑ a ∈ I, ∑ b ∈ I,
              (if a ≠ b ∧ capOf k k' (πf q) (cell q a) = capOf k k' (πf q) (cell q b)
                then 1 else 0) := by
            gcongr with k _ k' _
            exact hle k k'
        _ = ∑ a ∈ I, ∑ b ∈ I, Fintype.card Z' * ∑ k : X' → Z', ∑ k' : X' → Z',
              (if a ≠ b ∧ capOf k k' (πf q) (cell q a) = capOf k k' (πf q) (cell q b)
                then 1 else 0) := by
            rw [sum_comm_four_finset]
            simp only [Finset.mul_sum]
        _ ≤ ∑ _a ∈ I, ∑ _b ∈ I, Fintype.card (X' → Z') * Fintype.card (X' → Z') * (G + 1) :=
            Finset.sum_le_sum fun a ha ↦ Finset.sum_le_sum fun b hb ↦ hab a ha b hb
        _ = _ := by
            simp only [Finset.sum_const, smul_eq_mul]
            ring
    · simp [hG]
  calc Fintype.card Z' * ∑ q, ∑ k : X' → Z', ∑ k' : X' → Z',
        (if PermGood (πf q) G ∧ ¬Set.InjOn (fun s ↦ capOf k k' (πf q) (cell q s)) I
          then 1 else 0)
      = ∑ q, Fintype.card Z' * ∑ k : X' → Z', ∑ k' : X' → Z',
        (if PermGood (πf q) G ∧ ¬Set.InjOn (fun s ↦ capOf k k' (πf q) (cell q s)) I
          then 1 else 0) := Finset.mul_sum _ _ _
    _ ≤ ∑ _q : Q, Fintype.card (X' → Z') * Fintype.card (X' → Z') * (I.card * I.card * (G + 1)) :=
        Finset.sum_le_sum fun q _ ↦ hq q
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

/-- **Collisions of output cells, through a coordinate equivalence**: if the coordinates `Y` are
`((q, k), k')` and the event `P` is a collision of output cells `capOf k k' (πf q) (cell q s)` fixed
by `q` for a `PermGood` permutation, then `P` holds for at most `|I|² (G + 1) / |Z|` of `Y`. -/
theorem card_mul_filter_capOf_le {X' Z' Q Y : Type} [Fintype X'] [DecidableEq X'] [Fintype Z']
    [DecidableEq Z'] [AddCommGroup Z'] [Fintype Q] [Fintype Y] (I : Finset S)
    (e : (Q × (X' → Z')) × (X' → Z') ≃ Y) (πf : Q → Equiv.Perm (X' × Z')) (cell : Q → S → X')
    (hcell : ∀ q, Set.InjOn (cell q) I) (G : ℕ) (P : Y → Prop) [DecidablePred P]
    (hP : ∀ q k k', P (e ((q, k), k')) ↔
      PermGood (πf q) G ∧ ¬Set.InjOn (fun s ↦ capOf k k' (πf q) (cell q s)) I) :
    Fintype.card Z' * (Finset.univ.filter P).card ≤
      Fintype.card Y * (I.card * I.card * (G + 1)) := by
  classical
  have hsum := card_mul_sum_not_injOn_capOf_le I πf cell hcell G
  have hcard : Fintype.card Y = Fintype.card Q * (Fintype.card (X' → Z') *
      Fintype.card (X' → Z')) := by
    rw [← Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod, mul_assoc]
  have hcount : (Finset.univ.filter P).card = ∑ q, ∑ k : X' → Z', ∑ k' : X' → Z',
      (if PermGood (πf q) G ∧ ¬Set.InjOn (fun s ↦ capOf k k' (πf q) (cell q s)) I
        then 1 else 0) := by
    rw [Finset.card_filter, ← Fintype.sum_equiv e _ _ fun _ ↦ rfl, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun k _ ↦
      Finset.sum_congr rfl fun k' _ ↦ if_congr (hP q k k') rfl rfl
  rw [hcount, hcard]
  exact hsum

omit [DecidableEq S] in
/-- Counting the coordinates whose first component, through an equivalence, satisfies `p`. -/
theorem card_filter_comp_fst {Y B C : Type*} [Fintype Y] [Fintype B] [Fintype C] (e : Y ≃ B × C)
    (p : B → Prop) [DecidablePred p] :
    (Finset.univ.filter fun y ↦ p (e y).1).card =
      (Finset.univ.filter p).card * Fintype.card C := by
  rw [Finset.card_filter, Fintype.sum_equiv e _ (fun x ↦ if p x.1 then 1 else 0) fun _ ↦ rfl,
    Fintype.sum_prod_type, Finset.card_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  show (∑ _c : C, if p b then 1 else 0) = _
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- A union bound for a complement covered by three events. -/
theorem card_filter_not_le_three {Y : Type*} [Fintype Y] (GP P₁ P₂ P₃ : Y → Prop)
    [DecidablePred GP] [DecidablePred P₁] [DecidablePred P₂] [DecidablePred P₃]
    (h : ∀ y, ¬GP y → P₁ y ∨ P₂ y ∨ P₃ y) :
    (Finset.univ.filter fun y ↦ ¬GP y).card ≤
      (Finset.univ.filter P₁).card + (Finset.univ.filter P₂).card +
        (Finset.univ.filter P₃).card := by
  classical
  refine (Finset.card_le_card fun y hy ↦ ?_).trans
    ((Finset.card_union_le _ _).trans (add_le_add (Finset.card_union_le _ _) le_rfl))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy ⊢
  rcases h y hy with h1 | h2 | h3
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr h2)
  · exact Or.inr h3

omit [DecidableEq S] in
/-- The fraction of coordinates whose first component, through an equivalence, satisfies `p`. -/
theorem inv_card_mul_card_filter_comp_fst {Y B C : Type*} [Fintype Y] [Fintype B] [Fintype C]
    [Nonempty C] (e : Y ≃ B × C) (p : B → Prop) [DecidablePred p] :
    (Fintype.card Y : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y ↦ p (e y).1).card =
      ((Finset.univ.filter p).card : ℝ≥0∞) / Fintype.card B := by
  have hC : (Fintype.card C : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [card_filter_comp_fst e p, Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul,
    Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _)), div_eq_mul_inv]
  calc (Fintype.card B : ℝ≥0∞)⁻¹ * (Fintype.card C : ℝ≥0∞)⁻¹ *
        (((Finset.univ.filter p).card : ℝ≥0∞) * Fintype.card C)
      = ((Finset.univ.filter p).card : ℝ≥0∞) * (Fintype.card B : ℝ≥0∞)⁻¹ *
          ((Fintype.card C : ℝ≥0∞)⁻¹ * Fintype.card C) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hC (ENNReal.natCast_ne_top _), mul_one]

end generic

/-! ## leanXMSS -/

section xmss

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-! ### The digest correction of `roundH` -/

theorem embed128_zero : embed128 (0#digestBits) = 0 := by
  funext j
  unfold embed128
  split_ifs
  · simp [bitOf]
  · rfl

theorem getLsbD_trunc128 (x : X) {j : ℕ} (hj : j < 128) :
    (trunc128 x).getLsbD j = decide (x ⟨j, by omega⟩ = 1) := by
  change ((out256 x).extractLsb' 0 128).getLsbD j = _
  rw [BitVec.getLsbD_extractLsb', getLsbD_out256 _ _ (by omega)]
  simp [hj]

/-- Adding a digest in the first 128 bits XORs it into the digest. -/
theorem trunc128_add_embed128 (x : X) (d : Digest) :
    trunc128 (x + embed128 d) = trunc128 x ^^^ d := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj' : j < 128 := hj
  rw [BitVec.getLsbD_xor, getLsbD_trunc128 _ hj', getLsbD_trunc128 _ hj']
  have he : embed128 d ⟨j, by omega⟩ = bitOf (d.getLsbD j) := ite_eq_left hj'
  rw [Pi.add_apply, he]
  generalize x ⟨j, by omega⟩ = a
  cases d.getLsbD j <;> revert a <;> decide

theorem add_self_rate (x : X) : x + x = 0 :=
  funext fun j ↦ by
    show x j + x j = 0
    generalize x j = a
    revert a
    decide

theorem xor_xor_cancel_left (a b : Digest) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- **leanXMSS's digest correction**: the digest of the output rate `r + w` is its first 128 bits;
`roundH`'s correction XORs the difference into them. -/
def xmssFix : DigestFix X Digest where
  dig r w := trunc128 (r + w)
  cor r w d := w + embed128 (d ^^^ trunc128 (r + w))
  dig_cor r w d := by
    show trunc128 (r + (w + embed128 (d ^^^ trunc128 (r + w)))) = d
    rw [← add_assoc, trunc128_add_embed128, BitVec.xor_comm d, xor_xor_cancel_left]
  cor_cor r w d := by
    show w + embed128 (d ^^^ trunc128 (r + w)) + embed128 (trunc128 (r + w) ^^^
      trunc128 (r + (w + embed128 (d ^^^ trunc128 (r + w))))) = w
    rw [← add_assoc r, trunc128_add_embed128, xor_xor_cancel_left, add_assoc, add_self_rate,
      add_zero]

/-- At the table's own digest the correction vanishes. -/
theorem xmssFix_cor_dig (r w : X) : xmssFix.cor r w (xmssFix.dig r w) = w := by
  show w + embed128 (trunc128 (r + w) ^^^ trunc128 (r + w)) = w
  rw [BitVec.xor_self, embed128_zero, add_zero]

/-! ### A slot's honest path -/

/-- The state after `π` in the last round of slot `s`'s honest path. -/
def outMid (pub : Pub) (s : Slot) (f : ValPos → Digest) : X × Z :=
  midAt pub (stateAt pub (blocks (slotInput pub s f)) (nBlocks pub s - 1))
    ((blocks (slotInput pub s f)).getD (nBlocks pub s - 1) 0)

/-- **The output cell** of slot `s`: the `h`-cell of the last round. -/
def outCap (pub : Pub) (s : Slot) (f : ValPos → Digest) : Z :=
  (outMid pub s f).2 + pub.keys.2.2 (outMid pub s f).1

/-- **The output rate** of slot `s`: the rate the last `h` value is added to. -/
def outRate (pub : Pub) (s : Slot) (f : ValPos → Digest) : X :=
  (outMid pub s f).1

theorem length_le16 (a : Digest) : (littleEndianBytes 16 a).length = 16 :=
  length_littleEndianBytes 16 a

theorem length_digestsPayload (g : ChainIndex → Digest) :
    (digestsPayload g).length = 16 * chainCount :=
  (length_flatMap_littleEndianBytes (List.ofFn g)).trans
    (congrArg (16 * ·) (List.length_ofFn (f := g)))

theorem length_slotPayload (f f' : ValPos → Digest) (s : Slot) :
    (slotPayload f s).length = (slotPayload f' s).length := by
  cases s with
  | chain l e step i =>
    simp only [slotPayload, Verification.chainPayload, List.length_append, length_le16,
      length_littleEndianBytes]
  | leaf l e => simp only [slotPayload, length_digestsPayload]
  | node l level index => simp only [slotPayload, nodePayload, List.length_append, length_le16]
  | _ => rfl

theorem length_blocks_slotInput (pub : Pub) (s : Slot) (f : ValPos → Digest) :
    (blocks (slotInput pub s f)).length = nBlocks pub s := by
  rw [nBlocks, length_blocks, length_blocks, slotInput, slotInput, length_thInput, length_thInput,
    length_slotPayload f (fun _ ↦ 0)]

theorem nBlocks_pos (pub : Pub) (s : Slot) : 1 ≤ nBlocks pub s := by
  rw [nBlocks, length_blocks]
  omega

theorem stateAt_zero (pub : Pub) (msg : List X) : stateAt pub msg 0 = (0, 0) :=
  rfl

/-- A round of the sponge in the template's terms. -/
theorem stateAt_succ (pub : Pub) (msg : List X) {j : ℕ} (hj : j < msg.length) :
    stateAt pub msg (j + 1) =
      ((midAt pub (stateAt pub msg j) (msg.getD j 0)).1 + pub.keys.1
          ((midAt pub (stateAt pub msg j) (msg.getD j 0)).2 +
            pub.keys.2.2 (midAt pub (stateAt pub msg j) (msg.getD j 0)).1),
        (midAt pub (stateAt pub msg j) (msg.getD j 0)).2 +
          pub.keys.2.2 (midAt pub (stateAt pub msg j) (msg.getD j 0)).1) := by
  unfold stateAt
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some]
  rfl

theorem spongeHash_eq_stateAt (pub : Pub) (msg : List X) :
    spongeHash (spongePerm pub.keys pub.perm) msg = (stateAt pub msg msg.length).1 := by
  rw [stateAt, List.take_length]
  rfl

/-- **A slot's digest is read at its output cell.** -/
theorem trunc128_spongeHash_slotInput (pub : Pub) (s : Slot) (f : ValPos → Digest) :
    trunc128 (spongeHash (spongePerm pub.keys pub.perm) (blocks (slotInput pub s f))) =
      xmssFix.dig (outRate pub s f) (pub.keys.1 (outCap pub s f)) := by
  have h1 := nBlocks_pos pub s
  have hst : stateAt pub (blocks (slotInput pub s f)) (nBlocks pub s) =
      stateAt pub (blocks (slotInput pub s f)) (nBlocks pub s - 1 + 1) := by
    rw [Nat.sub_add_cancel h1]
  rw [spongeHash_eq_stateAt, length_blocks_slotInput, hst,
    stateAt_succ _ _ (by rw [length_blocks_slotInput]; omega)]
  rfl

theorem roundH_fst (pub : Pub) (s : Slot) (f : ValPos → Digest) (j : ℕ) :
    (roundH pub s f j).1 =
      (midAt pub (stateAt pub (blocks (slotInput pub s f)) j)
          ((blocks (slotInput pub s f)).getD j 0)).2 +
        pub.keys.2.2 (midAt pub (stateAt pub (blocks (slotInput pub s f)) j)
          ((blocks (slotInput pub s f)).getD j 0)).1 := by
  dsimp only [roundH]
  split_ifs <;> rfl

theorem roundH_snd_of_ne (pub : Pub) (s : Slot) (f : ValPos → Digest) {j : ℕ}
    (hj : j + 1 ≠ nBlocks pub s) : (roundH pub s f j).2 = pub.keys.1 (roundH pub s f j).1 := by
  dsimp only [roundH]
  rw [ite_eq_right hj]

/-- **The last round of `roundH`** is the output cell with the corrected value. -/
theorem roundH_last (pub : Pub) (s : Slot) (f : ValPos → Digest) :
    roundH pub s f (nBlocks pub s - 1) = (outCap pub s f,
      xmssFix.cor (outRate pub s f) (pub.keys.1 (outCap pub s f)) (f (slotOutPos s))) := by
  dsimp only [roundH]
  rw [ite_eq_left (Nat.sub_add_cancel (nBlocks_pos pub s))]
  rfl

/-! ### The positions, values and output cells of a table -/

/-- **The in-table output positions**: chain positions `1` to `3` of the table's keys, and the tree
values in range (level `0` the leaves). -/
def InPos : ValPos → Prop
  | .chain l e _ j => 1 ≤ j.val ∧ e.val < keyCount l
  | .tree l level index => index.val < 2 ^ (keyBits l - level.val)

instance : DecidablePred InPos := fun p ↦ by
  cases p <;> unfold InPos <;> infer_instance

/-- The in-table output positions, as a finite set (irreducible after `mem_xI`: unfolding it
enumerates every position). -/
def xI : Finset ValPos :=
  Finset.univ.filter InPos

theorem mem_xI {p : ValPos} : p ∈ xI ↔ InPos p := by
  simp only [xI, Finset.mem_filter, Finset.mem_univ, true_and]

attribute [irreducible] xI

theorem chainStep_pred_lt (j : Fin chainLength) : j.val - 1 < chainLength - 1 := by
  have := j.isLt
  simp only [chainLength, winternitzBits] at *
  omega

/-- **The slot whose output a position is**: a chain step, a leaf, or a node. -/
def outSlot : ValPos → Slot
  | .chain l e i j => .chain l e ⟨j.val - 1, chainStep_pred_lt j⟩ i
  | .tree l level index =>
      if level.val = 0 then .leaf l (leafKey index.val) else .node l level.val index.val

/-- The rank of a position: chain positions by their index, tree values above them by level. -/
def xRank : ValPos → ℕ
  | .chain _ _ _ j => j.val
  | .tree _ level _ => chainLength + level.val

/-- The rest of the table: the public parameter, `π`, and the keys `k`, `k'`. -/
abbrev XW : Type :=
  PublicParameter × Equiv.Perm (X × Z) × (X → Z) × (X → Z)

/-- The template's public data of a table (randomizer bases `0`: the paths do not read them). -/
def xPub (w : XW) (h : Z → X) : Pub :=
  ⟨w.1, w.2.1, (h, w.2.2.1, w.2.2.2), fun _ _ _ ↦ 0⟩

/-- The digest of an input under the table's sponge. -/
def xDig (w : XW) (h : Z → X) (input : HashInput) : Digest :=
  trunc128 (spongeHash (spongePerm (xPub w h).keys (xPub w h).perm) (blocks input))

/-- Position `j` of chain `i` of key `e` of layer `l`, from the chain start in the pad `u` (as
`HonestTable.chainValue`). -/
def chainV (w : XW) (h : Z → X) (u : ValPos → Digest) (l : Layer) (e : KeyIndex)
    (i : ChainIndex) : ℕ → Digest
  | 0 => u (.chain l e i ⟨0, by decide⟩)
  | j + 1 => if hj : j < chainLength - 1 then
      xDig w h (thInput w.1 (hashDomainFields (.chain l e ⟨j, hj⟩))
        (Verification.chainPayload i (chainV w h u l e i j)))
    else 0

/-- The tree value of layer `l` at `level`, index `index` (as `HonestTable.treeValue`). -/
def treeV (w : XW) (h : Z → X) (u : ValPos → Digest) (l : Layer) : ℕ → ℕ → Digest
  | 0, index => xDig w h (thInput w.1 (hashDomainFields (.leaf l (leafKey index)))
      (digestsPayload fun i ↦ chainV w h u l (leafKey index) i (chainLength - 1)))
  | level + 1, index => xDig w h (thInput w.1 (hashDomainFields (.node l (level + 1) index))
      (nodePayload (treeV w h u l level (2 * index)) (treeV w h u l level (2 * index + 1))))

/-- The honest value at a position, from the chain starts in the pad. -/
def recVal (w : XW) (h : Z → X) (u : ValPos → Digest) : ValPos → Digest
  | .chain l e i j => chainV w h u l e i j.val
  | .tree l level index => treeV w h u l level.val index.val

/-- **The table's values**: the honest values at the in-table output positions, the pad elsewhere
(chain starts and junk positions). -/
def xVal (w : XW) (h : Z → X) (u : ValPos → Digest) (p : ValPos) : Digest :=
  if InPos p then recVal w h u p else u p

/-- **leanXMSS's honest outputs.** -/
def xO : Outputs X Z Digest ValPos XW where
  I := xI
  val := xVal
  cap w h v p := outCap (xPub w h) (outSlot p) v
  rate w h v p := outRate (xPub w h) (outSlot p) v

theorem xVal_chain (w : XW) (h : Z → X) (u : ValPos → Digest) {l : Layer} {e : KeyIndex}
    (i : ChainIndex) (he : e.val < keyCount l) (j : Fin chainLength) :
    xVal w h u (.chain l e i j) = chainV w h u l e i j.val := by
  unfold xVal
  split_ifs with hm
  · rfl
  · have hj0 : j = ⟨0, by decide⟩ :=
      Fin.ext (Nat.eq_zero_of_not_pos fun hpos ↦ hm ⟨hpos, he⟩)
    subst hj0
    rfl

theorem xVal_tree (w : XW) (h : Z → X) (u : ValPos → Digest) {l : Layer}
    {level : Fin (layerHeight + 1)} {index : Fin (2 ^ 32)}
    (hin : index.val < 2 ^ (keyBits l - level.val)) :
    xVal w h u (.tree l level index) = treeV w h u l level.val index.val := by
  unfold xVal
  split_ifs with hm
  · rfl
  · exact absurd hin hm

theorem lt_lifetime_of_lt {l : Layer} {n : ℕ} (hn : n < 2 ^ keyBits l) : n < lifetime := by
  have := keyCount_le l
  simp only [keyCount, lifetime, layerCount, layerHeight] at *
  omega

theorem leafKey_val_of_lt {l : Layer} {n : ℕ} (hn : n < 2 ^ keyBits l) : (leafKey n).val = n :=
  Nat.mod_eq_of_lt (lt_lifetime_of_lt hn)

theorem slotInput_chain (pub : Pub) (l : Layer) (e : KeyIndex) (step : ChainStep)
    (i : ChainIndex) (f : ValPos → Digest) :
    slotInput pub (.chain l e step i) f = thInput pub.param (hashDomainFields (.chain l e step))
      (Verification.chainPayload i (f (cpos l e i step.val))) :=
  rfl

theorem slotInput_leaf (pub : Pub) (l : Layer) (e : KeyIndex) (f : ValPos → Digest) :
    slotInput pub (.leaf l e) f = thInput pub.param (hashDomainFields (.leaf l e))
      (digestsPayload fun i ↦ f (cpos l e i (chainLength - 1))) :=
  rfl

theorem slotInput_node (pub : Pub) (l : Layer) (level index : ℕ) (f : ValPos → Digest) :
    slotInput pub (.node l level index) f = thInput pub.param
      (hashDomainFields (.node l level index))
      (nodePayload (f (tpos l (level - 1) (2 * index))) (f (tpos l (level - 1) (2 * index + 1)))) :=
  rfl

theorem chainV_succ (w : XW) (h : Z → X) (u : ValPos → Digest) (l : Layer) (e : KeyIndex)
    (i : ChainIndex) {j : ℕ} (hj : j < chainLength - 1) :
    chainV w h u l e i (j + 1) = xDig w h (thInput w.1 (hashDomainFields (.chain l e ⟨j, hj⟩))
      (Verification.chainPayload i (chainV w h u l e i j))) := by
  simp only [chainV, hj, ↓reduceDIte]

/-- **An in-table output's value is its slot's digest** under the table's values. -/
theorem recVal_eq_xDig (w : XW) (h : Z → X) (u : ValPos → Digest) {p : ValPos}
    (hp : InPos p) :
    recVal w h u p = xDig w h (slotInput (xPub w h) (outSlot p) (xVal w h u)) := by
  cases p with
  | chain l e i j =>
    obtain ⟨hj, he⟩ := hp
    obtain ⟨j', hj'⟩ : ∃ j', j.val = j' + 1 := ⟨j.val - 1, by omega⟩
    have hlt : j' < chainLength - 1 := by have := j.isLt; omega
    have e1 : (⟨j.val - 1, chainStep_pred_lt j⟩ : ChainStep) = ⟨j', hlt⟩ :=
      Fin.ext (by simp only; omega)
    have e2 : xVal w h u (cpos l e i (⟨j', hlt⟩ : ChainStep).val) = chainV w h u l e i j' := by
      rw [cpos, xVal_chain w h u i he]
      exact congrArg _ (Nat.mod_eq_of_lt (by omega))
    show chainV w h u l e i j.val =
      xDig w h (slotInput (xPub w h) (.chain l e ⟨j.val - 1, chainStep_pred_lt j⟩ i) (xVal w h u))
    rw [e1, slotInput_chain, e2, hj', chainV_succ w h u l e i hlt]
    rfl
  | tree l level index =>
    have hp' : index.val < 2 ^ (keyBits l - level.val) := hp
    by_cases hl : level.val = 0
    · rw [hl, Nat.sub_zero] at hp'
      have hkey := leafKey_val_of_lt hp'
      have e2 : (fun i ↦ xVal w h u (cpos l (leafKey index.val) i (chainLength - 1))) =
          fun i ↦ chainV w h u l (leafKey index.val) i (chainLength - 1) := funext fun i ↦ by
        rw [cpos, xVal_chain w h u i (by rw [hkey]; exact hp')]
        exact congrArg _ (Nat.mod_eq_of_lt (by decide))
      show treeV w h u l level.val index.val = xDig w h (slotInput (xPub w h)
        (if level.val = 0 then .leaf l (leafKey index.val) else .node l level.val index.val)
        (xVal w h u))
      rw [ite_eq_left hl, slotInput_leaf, e2, hl]
      rfl
    · obtain ⟨lv, hlv⟩ : ∃ lv, level.val = lv + 1 := ⟨level.val - 1, by omega⟩
      rw [hlv] at hp'
      have hle : lv + 1 ≤ keyBits l := by
        have := level.isLt
        have := le_keyBits l
        simp only [layerHeight] at *
        omega
      have hpow : 2 ^ (keyBits l - lv) = 2 * 2 ^ (keyBits l - (lv + 1)) := by
        rw [show keyBits l - lv = keyBits l - (lv + 1) + 1 by omega, pow_succ]
        ring
      have h32 : 2 ^ (keyBits l - lv) ≤ 2 ^ 32 :=
        Nat.pow_le_pow_right (by norm_num) (by have := keyBits_le l; omega)
      have hlv17 : lv < layerHeight + 1 := by have := level.isLt; omega
      have htp : ∀ c, c < 2 ^ (keyBits l - lv) → xVal w h u (tpos l lv c) = treeV w h u l lv c := by
        intro c hc
        have hc32 : c < 2 ^ 32 := lt_of_lt_of_le hc h32
        have hpos : tpos l lv c = .tree l ⟨lv, hlv17⟩ ⟨c, hc32⟩ := by
          unfold tpos
          congr 1
          · exact Fin.ext (Nat.mod_eq_of_lt hlv17)
          · exact Fin.ext (Nat.mod_eq_of_lt hc32)
        rw [hpos, xVal_tree w h u (l := l) (level := ⟨lv, hlv17⟩) (index := ⟨c, hc32⟩) hc]
      show treeV w h u l level.val index.val = xDig w h (slotInput (xPub w h)
        (if level.val = 0 then .leaf l (leafKey index.val) else .node l level.val index.val)
        (xVal w h u))
      rw [ite_eq_right hl, slotInput_node, hlv, Nat.add_sub_cancel, htp _ (by omega),
        htp _ (by omega)]
      rfl

/-- **The table's values are its outputs' digests** (`Consistent`). -/
theorem xO_consistent : xO.Consistent xmssFix := by
  intro w h u p
  show xVal w h u p = if p ∈ xI then
    xmssFix.dig (outRate (xPub w h) (outSlot p) (xVal w h u))
      (h (outCap (xPub w h) (outSlot p) (xVal w h u))) else u p
  by_cases hp : InPos p
  · have hx : xVal w h u p = recVal w h u p := ite_eq_left hp
    rw [ite_eq_left (mem_xI.mpr hp), hx, recVal_eq_xDig w h u hp]
    exact trunc128_spongeHash_slotInput (xPub w h) (outSlot p) (xVal w h u)
  · rw [ite_eq_right fun hm ↦ hp (mem_xI.mp hm)]
    exact ite_eq_right hp

/-- An in-table output's input depends on the values of lower rank only. -/
theorem slotInput_congr (pub : Pub) {p : ValPos} (hp : InPos p) {v v' : ValPos → Digest}
    (hlow : ∀ t, xRank t < xRank p → v t = v' t) :
    slotInput pub (outSlot p) v = slotInput pub (outSlot p) v' := by
  cases p with
  | chain l e i j =>
    obtain ⟨hj, -⟩ := hp
    show slotInput pub (.chain l e ⟨j.val - 1, chainStep_pred_lt j⟩ i) v =
      slotInput pub (.chain l e ⟨j.val - 1, chainStep_pred_lt j⟩ i) v'
    rw [slotInput_chain, slotInput_chain,
      hlow _ (lt_of_le_of_lt (Nat.mod_le _ _) (by show j.val - 1 < j.val; omega))]
  | tree l level index =>
    by_cases hl : level.val = 0
    · rw [show outSlot (.tree l level index) = .leaf l (leafKey index.val) from ite_eq_left hl,
        slotInput_leaf, slotInput_leaf]
      refine congrArg _ (congrArg _ (funext fun i ↦ hlow _ ?_))
      exact lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (Nat.le_add_right _ _)
    · rw [show outSlot (.tree l level index) = .node l level.val index.val from ite_eq_right hl,
        slotInput_node, slotInput_node,
        hlow _ (Nat.add_lt_add_left (lt_of_le_of_lt (Nat.mod_le _ _) (by omega)) _),
        hlow _ (Nat.add_lt_add_left (lt_of_le_of_lt (Nat.mod_le _ _) (by omega)) _)]

/-- **The values are ranked**: an output's cell and rate depend on lower values only. -/
theorem xO_ranked : xO.Ranked xRank := by
  intro w h v v' p hp hlow
  have hin := slotInput_congr (xPub w h) (mem_xI.mp hp) hlow
  refine ⟨?_, ?_⟩
  · show outCap (xPub w h) (outSlot p) v = outCap (xPub w h) (outSlot p) v'
    unfold outCap outMid
    rw [hin]
  · show outRate (xPub w h) (outSlot p) v = outRate (xPub w h) (outSlot p) v'
    unfold outRate outMid
    rw [hin]

/-! ### Local paths -/

theorem xPub_keys (w : XW) (h : Z → X) : (xPub w h).keys = (h, w.2.2.1, w.2.2.2) :=
  rfl

theorem slotInput_xPub (w : XW) (h h₂ : Z → X) : slotInput (xPub w h₂) = slotInput (xPub w h) :=
  rfl

theorem nBlocks_xPub (w : XW) (h h₂ : Z → X) : nBlocks (xPub w h₂) = nBlocks (xPub w h) :=
  rfl

theorem midAt_xPub (w : XW) (h h₂ : Z → X) : midAt (xPub w h₂) = midAt (xPub w h) :=
  rfl

/-- Changing `h` off the `h`-cells of a path's first `j` rounds keeps its first `j` states. -/
theorem stateAt_xPub_congr (w : XW) (h h₂ : Z → X) (s : Slot) (v : ValPos → Digest) :
    ∀ j, j ≤ nBlocks (xPub w h) s →
      (∀ i < j, h₂ (roundH (xPub w h) s v i).1 = h (roundH (xPub w h) s v i).1) →
      stateAt (xPub w h₂) (blocks (slotInput (xPub w h) s v)) j =
        stateAt (xPub w h) (blocks (slotInput (xPub w h) s v)) j
  | 0, _, _ => rfl
  | j + 1, hj, hh => by
    have hlen : j < (blocks (slotInput (xPub w h) s v)).length := by
      rw [length_blocks_slotInput]
      omega
    have hz := hh j (by omega)
    rw [roundH_fst] at hz
    rw [stateAt_succ _ _ hlen, stateAt_succ _ _ hlen,
      stateAt_xPub_congr w h h₂ s v j (by omega) fun i hi ↦ hh i (by omega), midAt_xPub w h h₂]
    simp only [xPub_keys] at hz ⊢
    rw [hz]

/-- Changing `h` off the `h`-cells of a path's rounds before the last keeps its output cell. -/
theorem outMid_xPub_congr {w : XW} {h h₂ : Z → X} {s : Slot} {v : ValPos → Digest}
    (hh : ∀ i, i + 1 < nBlocks (xPub w h) s →
      h₂ (roundH (xPub w h) s v i).1 = h (roundH (xPub w h) s v i).1) :
    outMid (xPub w h₂) s v = outMid (xPub w h) s v := by
  have h1 := nBlocks_pos (xPub w h) s
  unfold outMid
  rw [slotInput_xPub w h h₂, nBlocks_xPub w h h₂, midAt_xPub w h h₂,
    stateAt_xPub_congr w h h₂ s v _ (by omega) fun i hi ↦ hh i (by omega)]

theorem outCap_xPub_congr {w : XW} {h h₂ : Z → X} {s : Slot} {v : ValPos → Digest}
    (hh : ∀ i, i + 1 < nBlocks (xPub w h) s →
      h₂ (roundH (xPub w h) s v i).1 = h (roundH (xPub w h) s v i).1) :
    outCap (xPub w h₂) s v = outCap (xPub w h) s v := by
  unfold outCap
  rw [outMid_xPub_congr hh]
  rfl

theorem outRate_xPub_congr {w : XW} {h h₂ : Z → X} {s : Slot} {v : ValPos → Digest}
    (hh : ∀ i, i + 1 < nBlocks (xPub w h) s →
      h₂ (roundH (xPub w h) s v i).1 = h (roundH (xPub w h) s v i).1) :
    outRate (xPub w h₂) s v = outRate (xPub w h) s v := by
  unfold outRate
  rw [outMid_xPub_congr hh]

theorem roundH_fst_xPub_congr {w : XW} {h h₂ : Z → X} {s : Slot} {v : ValPos → Digest} {j : ℕ}
    (hj : j < nBlocks (xPub w h) s)
    (hh : ∀ i < j, h₂ (roundH (xPub w h) s v i).1 = h (roundH (xPub w h) s v i).1) :
    (roundH (xPub w h₂) s v j).1 = (roundH (xPub w h) s v j).1 := by
  rw [roundH_fst, roundH_fst, slotInput_xPub w h h₂, midAt_xPub w h h₂,
    stateAt_xPub_congr w h h₂ s v j hj.le hh]
  rfl

/-- **The paths avoid the output cells**: no `h`-cell of a round before the last of an in-table
output's path is an output cell. -/
def PathsAvoid (w : XW) (h : Z → X) (v : ValPos → Digest) : Prop :=
  ∀ p ∈ xI, ∀ q ∈ xI, ∀ j, j + 1 < nBlocks (xPub w h) (outSlot p) →
    (roundH (xPub w h) (outSlot p) v j).1 ≠ outCap (xPub w h) (outSlot q) v

theorem agree_of_pathsAvoid {w : XW} {h h₂ : Z → X} {v : ValPos → Digest}
    (hA : PathsAvoid w h v) (hag : AgreeOff xO.I (xO.cap w h v) h h₂) {p : ValPos} (hp : p ∈ xI)
    (i : ℕ) (hi : i + 1 < nBlocks (xPub w h) (outSlot p)) :
    h₂ (roundH (xPub w h) (outSlot p) v i).1 = h (roundH (xPub w h) (outSlot p) v i).1 :=
  hag _ fun q hq e ↦ hA p hp q hq i hi e.symm

/-- **Avoiding paths are local.** -/
theorem local_of_pathsAvoid {w : XW} {h : Z → X} {v : ValPos → Digest} (hA : PathsAvoid w h v) :
    xO.Local w h v := fun _ hag _ hp ↦
  ⟨outCap_xPub_congr (agree_of_pathsAvoid hA hag hp),
    outRate_xPub_congr (agree_of_pathsAvoid hA hag hp)⟩

/-- Avoiding paths stay avoiding when `h` changes off the output cells. -/
theorem pathsAvoid_congr {w : XW} {h h₂ : Z → X} {v : ValPos → Digest} (hA : PathsAvoid w h v)
    (hag : AgreeOff xO.I (xO.cap w h v) h h₂) : PathsAvoid w h₂ v := by
  intro p hp q hq j hj
  have hj' : j + 1 < nBlocks (xPub w h) (outSlot p) := hj
  rw [roundH_fst_xPub_congr (by omega) fun i hi ↦ agree_of_pathsAvoid hA hag hp i (by omega),
    outCap_xPub_congr (agree_of_pathsAvoid hA hag hq)]
  exact hA p hp q hq j hj'

/-- **leanXMSS's good set, in the public coordinates**: distinct output cells, and paths avoiding
them. -/
abbrev XGoodPV : ((Z → X) × XW) × (ValPos → Digest) → Prop :=
  xO.GoodPVWith PathsAvoid

/-- **leanXMSS's good set of tables.** -/
abbrev XGood : ((Z → X) × (ValPos → Digest)) × XW → Prop :=
  xO.GoodWith PathsAvoid

theorem xPL : ∀ w h v, PathsAvoid w h v → xO.Local w h v :=
  fun _ _ _ hA ↦ local_of_pathsAvoid hA

theorem xPC : ∀ w h h₂ v, PathsAvoid w h v → AgreeOff xO.I (xO.cap w h v) h h₂ →
    PathsAvoid w h₂ v :=
  fun _ _ _ _ hA hag ↦ pathsAvoid_congr hA hag

theorem good_of_xGood {θ : ((Z → X) × (ValPos → Digest)) × XW} (hθ : XGood θ) : xO.Good θ :=
  good_of_with xPL hθ

theorem xGoodPV_fwd {θ : ((Z → X) × (ValPos → Digest)) × XW} (hθ : XGood θ) :
    XGoodPV (fwd xmssFix xO θ) :=
  goodPVWith_fwd xPL xPC hθ

theorem xGood_back {y : ((Z → X) × XW) × (ValPos → Digest)} (hy : XGoodPV y) :
    XGood (back xmssFix xO y) :=
  goodWith_back xPL xPC xO_consistent xO_ranked hy

/-! ### The template at the public data programs the table's honest cells -/

theorem slotOutPos_outSlot {p : ValPos} (hp : InPos p) : slotOutPos (outSlot p) = p := by
  cases p with
  | chain l e i j =>
    obtain ⟨hj, -⟩ := hp
    show cpos l e i (j.val - 1 + 1) = .chain l e i j
    unfold cpos
    congr 1
    exact Fin.ext (by rw [Nat.sub_add_cancel hj]; exact Nat.mod_eq_of_lt j.isLt)
  | tree l level index =>
    have hp' : index.val < 2 ^ (keyBits l - level.val) := hp
    by_cases hl : level.val = 0
    · rw [hl, Nat.sub_zero] at hp'
      rw [show outSlot (.tree l level index) = .leaf l (leafKey index.val) from ite_eq_left hl]
      show tpos l 0 (leafKey index.val).val = _
      rw [leafKey_val_of_lt hp']
      unfold tpos
      congr 1
      · exact Fin.ext (by rw [hl]; exact Nat.zero_mod _)
      · exact Fin.ext (Nat.mod_eq_of_lt index.isLt)
    · rw [show outSlot (.tree l level index) = .node l level.val index.val from ite_eq_right hl]
      show tpos l level.val index.val = _
      unfold tpos
      congr 1
      · exact Fin.ext (Nat.mod_eq_of_lt level.isLt)
      · exact Fin.ext (Nat.mod_eq_of_lt index.isLt)

/-- An in-table output's value is the digest at its output cell. -/
theorem xVal_eq_dig (w : XW) (h : Z → X) (u : ValPos → Digest) {p : ValPos} (hp : InPos p) :
    xVal w h u p = xmssFix.dig (outRate (xPub w h) (outSlot p) (xVal w h u))
      (h (outCap (xPub w h) (outSlot p) (xVal w h u))) := by
  rw [show xVal w h u p = recVal w h u p from ite_eq_left hp, recVal_eq_xDig w h u hp]
  exact trunc128_spongeHash_slotInput (xPub w h) (outSlot p) (xVal w h u)

/-- **The table's own template values are its honest cells**: at the table's public data and
values, every `h`-cell is programmed with the table's value of `h` (the correction vanishes). -/
theorem roundH_table (w : XW) (h : Z → X) (u : ValPos → Digest) {p : ValPos} (hp : InPos p)
    {j : ℕ} (hj : j < nBlocks (xPub w h) (outSlot p)) :
    roundH (xPub w h) (outSlot p) (xVal w h u) j =
      ((roundH (xPub w h) (outSlot p) (xVal w h u) j).1,
        h (roundH (xPub w h) (outSlot p) (xVal w h u) j).1) := by
  by_cases hl : j + 1 = nBlocks (xPub w h) (outSlot p)
  · obtain rfl : j = nBlocks (xPub w h) (outSlot p) - 1 := by omega
    rw [roundH_last, slotOutPos_outSlot hp, xVal_eq_dig w h u hp]
    exact Prod.ext rfl (xmssFix_cor_dig _ _)
  · exact Prod.ext rfl (roundH_snd_of_ne _ _ _ hl)

theorem roundK_xPub_congr {w : XW} {h h₂ : Z → X} {s : Slot} {v : ValPos → Digest} {j : ℕ}
    (hj : j ≤ nBlocks (xPub w h) s)
    (hh : ∀ i < j, h₂ (roundH (xPub w h) s v i).1 = h (roundH (xPub w h) s v i).1) :
    roundK (xPub w h₂) s v j = roundK (xPub w h) s v j := by
  dsimp only [roundK]
  rw [slotInput_xPub w h h₂, stateAt_xPub_congr w h h₂ s v j hj hh]
  rfl

theorem roundK'_xPub_congr {w : XW} {h h₂ : Z → X} {s : Slot} {v : ValPos → Digest} {j : ℕ}
    (hj : j ≤ nBlocks (xPub w h) s)
    (hh : ∀ i < j, h₂ (roundH (xPub w h) s v i).1 = h (roundH (xPub w h) s v i).1) :
    roundK' (xPub w h₂) s v j = roundK' (xPub w h) s v j := by
  dsimp only [roundK']
  rw [slotInput_xPub w h h₂, midAt_xPub w h h₂, stateAt_xPub_congr w h h₂ s v j hj hh]
  rfl

/-- The template's values at a public `h₂` agreeing with `h` at the earlier `h`-cells of a path,
and with the correction giving back `h` at its output cell, are those at `h`. -/
theorem rounds_congr {w : XW} {h h₂ : Z → X} {u : ValPos → Digest} {p : ValPos} (hp : InPos p)
    (hh : ∀ i, i + 1 < nBlocks (xPub w h) (outSlot p) →
      h₂ (roundH (xPub w h) (outSlot p) (xVal w h u) i).1 =
        h (roundH (xPub w h) (outSlot p) (xVal w h u) i).1)
    (hc : xmssFix.cor (outRate (xPub w h₂) (outSlot p) (xVal w h u))
        (h₂ (outCap (xPub w h₂) (outSlot p) (xVal w h u))) (xVal w h u p) =
      h (outCap (xPub w h) (outSlot p) (xVal w h u)))
    {j : ℕ} (hj : j < nBlocks (xPub w h) (outSlot p)) :
    roundK (xPub w h₂) (outSlot p) (xVal w h u) j = roundK (xPub w h) (outSlot p) (xVal w h u) j ∧
      roundK' (xPub w h₂) (outSlot p) (xVal w h u) j =
        roundK' (xPub w h) (outSlot p) (xVal w h u) j ∧
      roundH (xPub w h₂) (outSlot p) (xVal w h u) j =
        roundH (xPub w h) (outSlot p) (xVal w h u) j := by
  refine ⟨roundK_xPub_congr hj.le fun i hi ↦ hh i (by omega),
    roundK'_xPub_congr hj.le fun i hi ↦ hh i (by omega), ?_⟩
  by_cases hl : j + 1 = nBlocks (xPub w h) (outSlot p)
  · obtain rfl : j = nBlocks (xPub w h) (outSlot p) - 1 := by omega
    have e1 := roundH_last (xPub w h₂) (outSlot p) (xVal w h u)
    rw [nBlocks_xPub w h h₂] at e1
    rw [e1, roundH_last, outCap_xPub_congr hh, outRate_xPub_congr hh, slotOutPos_outSlot hp,
      xVal_eq_dig w h u hp]
    rw [outCap_xPub_congr hh, outRate_xPub_congr hh, xVal_eq_dig w h u hp] at hc
    exact Prod.ext rfl (hc.trans (xmssFix_cor_dig _ _).symm)
  · have hfst := roundH_fst_xPub_congr (h₂ := h₂) hj fun i hi ↦ hh i (by omega)
    refine Prod.ext hfst ?_
    rw [roundH_snd_of_ne (xPub w h₂) (outSlot p) (xVal w h u) hl,
      roundH_snd_of_ne (xPub w h) (outSlot p) (xVal w h u) hl, hfst]
    exact hh j (by omega)

/-- `cor_fwd` for leanXMSS, in the template's terms. -/
theorem cor_fwd_xmss {h : Z → X} {u : ValPos → Digest} {w : XW} (hθ : XGood ((h, u), w))
    {p : ValPos} (hp : p ∈ xI) :
    xmssFix.cor (outRate (xPub w (fwd xmssFix xO ((h, u), w)).1.1) (outSlot p) (xVal w h u))
        ((fwd xmssFix xO ((h, u), w)).1.1
          (outCap (xPub w (fwd xmssFix xO ((h, u), w)).1.1) (outSlot p) (xVal w h u)))
        (xVal w h u p) =
      h (outCap (xPub w h) (outSlot p) (xVal w h u)) :=
  cor_fwd xO_consistent (good_of_xGood hθ) hp

/-- **The template at the public data programs the table's cells.** On the good set, for every
in-table output and every round of its slot's honest path, the template's `k`, `k'` and `h`
program-port values at the public data `xPub w h''` (`h''` the public `h` of `fwd`; its other
coordinates are `w`, `fwd_fst_snd`, and the hidden values are `xVal w h u`, `fwd_snd`) are those
at the table's own public data, which are the table's honest cells (`roundH_table`). -/
theorem rounds_fwd {h : Z → X} {u : ValPos → Digest} {w : XW} (hθ : XGood ((h, u), w))
    {p : ValPos} (hp : p ∈ xI) {j : ℕ} (hj : j < nBlocks (xPub w h) (outSlot p)) :
    roundK (xPub w (fwd xmssFix xO ((h, u), w)).1.1) (outSlot p) (xVal w h u) j =
        roundK (xPub w h) (outSlot p) (xVal w h u) j ∧
      roundK' (xPub w (fwd xmssFix xO ((h, u), w)).1.1) (outSlot p) (xVal w h u) j =
        roundK' (xPub w h) (outSlot p) (xVal w h u) j ∧
      roundH (xPub w (fwd xmssFix xO ((h, u), w)).1.1) (outSlot p) (xVal w h u) j =
        roundH (xPub w h) (outSlot p) (xVal w h u) j :=
  rounds_congr (mem_xI.mp hp) (agree_of_pathsAvoid hθ.2 (agreeOff_fwd xmssFix xO ((h, u), w)) hp)
    (cor_fwd_xmss hθ hp) hj

/-! ### The honest table's values -/

/-- The rest of an honest table's data. -/
def wOf (L : HonestTable) : XW :=
  (L.param, L.perm, L.keys.2.1, L.keys.2.2)

/-- **The public data of an honest table is `pubOf` up to the randomizer bases**, which the paths
do not read. -/
theorem pubOf_eq (L : HonestTable) :
    pubOf L = { xPub (wOf L) L.keys.1 with rbase := L.randomizerBase } :=
  rfl

theorem xDig_wOf (L : HonestTable) (input : HashInput) :
    xDig (wOf L) L.keys.1 input = L.digest input :=
  L.trunc128_spongeHash input

theorem chainV_wOf (L : HonestTable) (u : ValPos → Digest) {l : Layer} {e : KeyIndex}
    {i : ChainIndex} (hu : u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i) :
    ∀ j, chainV (wOf L) L.keys.1 u l e i j = L.chainValue l e i j
  | 0 => hu
  | j + 1 => by
    by_cases hj : j < chainLength - 1
    · rw [chainV_succ _ _ _ _ _ _ hj, chainV_wOf L u hu j, xDig_wOf,
        L.chainValue_succ l e i ⟨j, hj⟩]
      rfl
    · simp only [chainV, HonestTable.chainValue, hj, ↓reduceDIte]

theorem treeV_wOf (L : HonestTable) (u : ValPos → Digest) (l : Layer)
    (hu : ∀ (e : KeyIndex) i, e.val < keyCount l →
      u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i) :
    ∀ level, level ≤ layerHeight → ∀ index, index < 2 ^ (keyBits l - level) →
      treeV (wOf L) L.keys.1 u l level index = L.treeValue l level index
  | 0, _, index, hin => by
    have hin' : index < 2 ^ keyBits l := by simpa using hin
    have hk : (leafKey index).val < keyCount l := by
      rw [leafKey_val_of_lt hin']
      exact hin'
    have he : (fun i ↦ chainV (wOf L) L.keys.1 u l (leafKey index) i (chainLength - 1)) =
        L.endpoints l (leafKey index) :=
      funext fun i ↦ chainV_wOf L u (hu _ i hk) (chainLength - 1)
    show xDig (wOf L) L.keys.1 _ = _
    rw [he, xDig_wOf]
    rfl
  | level + 1, hlev, index, hin => by
    have hle : level + 1 ≤ keyBits l := le_trans hlev (le_keyBits l)
    have hpow : 2 ^ (keyBits l - level) = 2 * 2 ^ (keyBits l - (level + 1)) := by
      rw [show keyBits l - level = keyBits l - (level + 1) + 1 by omega, pow_succ]
      ring
    show xDig (wOf L) L.keys.1 _ = _
    rw [treeV_wOf L u l hu level (by omega) (2 * index) (by omega),
      treeV_wOf L u l hu level (by omega) (2 * index + 1) (by omega), xDig_wOf,
      L.treeValue_succ]
    rfl

/-- **The hidden coordinate is `valueAt`**: for an honest table with its chain starts in the pad,
the table's values at the in-table output positions are `valueAt L` (so `fwd`'s hidden
coordinate is, `fwd_snd`). -/
theorem xVal_wOf (L : HonestTable) (u : ValPos → Digest)
    (hu : ∀ l (e : KeyIndex) i, e.val < keyCount l →
      u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i) {p : ValPos} (hp : InPos p) :
    xVal (wOf L) L.keys.1 u p = valueAt L p := by
  cases p with
  | chain l e i j =>
    rw [xVal_chain _ _ _ i hp.2, chainV_wOf L u (hu l e i hp.2)]
    rfl
  | tree l level index =>
    rw [xVal_tree _ _ _ hp, treeV_wOf L u l (hu l) level.val (Nat.lt_succ_iff.mp level.isLt)
      index.val hp]
    rfl

/-- The in-table chain starts are read from the pad. -/
theorem xVal_chainStart (w : XW) (h : Z → X) (u : ValPos → Digest) {l : Layer} {e : KeyIndex}
    (i : ChainIndex) (he : e.val < keyCount l) :
    xVal w h u (.chain l e i ⟨0, by decide⟩) = u (.chain l e i ⟨0, by decide⟩) :=
  xVal_chain w h u i he _

/-! ### The bad fraction -/

/-- A leaf position (tree level `0`): its slot's input spans several blocks. -/
def IsLeafPos : ValPos → Prop
  | .tree _ level _ => level.val = 0
  | .chain .. => False

instance : DecidablePred IsLeafPos := fun p ↦ by
  cases p <;> unfold IsLeafPos <;> infer_instance

/-- The in-table outputs of one-block slots: chain steps and nodes. -/
def xI₁ : Finset ValPos :=
  xI.filter fun p ↦ ¬IsLeafPos p

theorem mem_xI₁ {p : ValPos} : p ∈ xI₁ ↔ InPos p ∧ ¬IsLeafPos p := by
  rw [xI₁, Finset.mem_filter, mem_xI]

/-- **Leaf separation**: every in-table leaf's output cell differs from every other in-table
output's. -/
def LeafSep (w : XW) (h : Z → X) (v : ValPos → Digest) : Prop :=
  ∀ p ∈ xI, IsLeafPos p → ∀ q ∈ xI, q ≠ p → xO.cap w h v p ≠ xO.cap w h v q

/-- **The path-collision event**, left to the analysis of the honest paths: a leaf's output cell
collides with another output cell, or an `h`-cell of a path's earlier round is an output cell. -/
def PathBad (y : ((Z → X) × XW) × (ValPos → Digest)) : Prop :=
  ¬LeafSep y.1.2 y.1.1 y.2 ∨ ¬PathsAvoid y.1.2 y.1.1 y.2

theorem injOn_of_leafSep {w : XW} {h : Z → X} {v : ValPos → Digest}
    (h₁ : Set.InjOn (xO.cap w h v) xI₁) (hL : LeafSep w h v) : Set.InjOn (xO.cap w h v) xI := by
  intro a ha b hb e
  have ha' : a ∈ xI := Finset.mem_coe.mp ha
  have hb' : b ∈ xI := Finset.mem_coe.mp hb
  by_contra hne
  by_cases hla : IsLeafPos a
  · exact hL a ha' hla b hb' (Ne.symm hne) e
  · by_cases hlb : IsLeafPos b
    · exact hL b hb' hlb a ha' hne e.symm
    · exact hne (h₁ (Finset.mem_coe.mpr (mem_xI₁.mpr ⟨mem_xI.mp ha', hla⟩))
        (Finset.mem_coe.mpr (mem_xI₁.mpr ⟨mem_xI.mp hb', hlb⟩)) e)

/-- One-block slots: chain steps and nodes. -/
theorem nBlocks_of_one (pub : Pub) {p : ValPos} (hl : ¬IsLeafPos p) :
    nBlocks pub (outSlot p) = 1 := by
  cases p with
  | chain l e i j =>
    rw [nBlocks, length_blocks, slotInput, length_thInput]
    simp only [outSlot, slotPayload, Verification.chainPayload, List.length_append, length_le16,
      length_littleEndianBytes]
  | tree l level index =>
    have hl' : level.val ≠ 0 := hl
    rw [show outSlot (.tree l level index) = .node l level.val index.val from ite_eq_right hl',
      nBlocks, length_blocks, slotInput, length_thInput]
    simp only [slotPayload, nodePayload, List.length_append, length_le16]

/-- **A one-block slot's output cell is `capOf` of its first block.** -/
theorem outCap_one {pub : Pub} {s : Slot} (f : ValPos → Digest) (hn : nBlocks pub s = 1) :
    outCap pub s f = capOf pub.keys.2.1 pub.keys.2.2 pub.perm
      ((blocks (slotInput pub s f)).getD 0 0) := by
  unfold outCap outMid
  rw [hn, Nat.sub_self, stateAt_zero]
  simp only [midAt, capOf, zero_add]

/-- The first block of an output's slot input, from the public parameter and the values. -/
def cellOf (P : PublicParameter) (v : ValPos → Digest) (p : ValPos) : X :=
  (blocks (thInput P (slotFields (outSlot p)) (slotPayload v (outSlot p)))).getD 0 0

/-- A one-block input's single sponge block names the slot its tail names. -/
theorem slotOf_single {input : HashInput} (hlen : (blocks input).length = 1) {P : PublicParameter}
    {s : Slot} (h : slotOf P (absorbTail (Equiv.refl (X × Z)) (blocks input)) = some s) :
    slotOf P [(blocks input).getD 0 0] = some s := by
  obtain ⟨rest, ht, hrl⟩ := absorbTail_blocks (Equiv.refl (X × Z)) input
  rw [length_blocks] at hlen
  have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [ht, hrest] at h
  rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, head?_blocks, Option.getD_some]
  exact h

theorem slotOf_cellOf (P : PublicParameter) (v : ValPos → Digest) {p : ValPos} (hp : InPos p)
    (hl : ¬IsLeafPos p) : slotOf P [cellOf P v p] = some (outSlot p) := by
  have hlen : (blocks (thInput P (slotFields (outSlot p)) (slotPayload v (outSlot p)))).length =
      1 :=
    (length_blocks_slotInput ⟨P, Equiv.refl _, (0, 0, 0), fun _ _ _ ↦ 0⟩ (outSlot p) v).trans
      (nBlocks_of_one _ hl)
  refine slotOf_single hlen ?_
  cases p with
  | chain l e i j => exact slotOf_chain _ P l e _ i _
  | tree l level index =>
    have hl' : level.val ≠ 0 := hl
    rw [show outSlot (.tree l level index) = .node l level.val index.val from ite_eq_right hl']
    exact slotOf_node _ P l level.val index.val
      (lt_of_lt_of_le level.isLt (by simp only [layerHeight]; norm_num)) index.isLt _ _

theorem outSlot_inj {a b : ValPos} (ha : InPos a ∧ ¬IsLeafPos a) (hb : InPos b ∧ ¬IsLeafPos b)
    (e : outSlot a = outSlot b) : a = b := by
  cases a with
  | chain l e₁ i j =>
    cases b with
    | chain l' e₂ i' j' =>
      simp only [outSlot, Slot.chain.injEq, Fin.mk.injEq] at e
      obtain ⟨rfl, rfl, hj, rfl⟩ := e
      have h1 := ha.1.1
      have h2 := hb.1.1
      exact congrArg _ (Fin.ext (by omega))
    | tree l' level index =>
      have hl' : level.val ≠ 0 := hb.2
      rw [show outSlot (.tree l' level index) = .node l' level.val index.val from
        ite_eq_right hl'] at e
      exact Slot.noConfusion e
  | tree l level index =>
    have hl : level.val ≠ 0 := ha.2
    rw [show outSlot (.tree l level index) = .node l level.val index.val from
      ite_eq_right hl] at e
    cases b with
    | chain l' e₂ i' j' => exact Slot.noConfusion e
    | tree l' level' index' =>
      have hl'' : level'.val ≠ 0 := hb.2
      rw [show outSlot (.tree l' level' index') = .node l' level'.val index'.val from
        ite_eq_right hl''] at e
      simp only [Slot.node.injEq] at e
      obtain ⟨rfl, h1, h2⟩ := e
      rw [Fin.ext h1, Fin.ext h2]

/-- **Distinct one-block outputs have distinct first blocks** (their addresses differ). -/
theorem cellOf_injOn (P : PublicParameter) (v : ValPos → Digest) : Set.InjOn (cellOf P v) xI₁ :=
  fun a ha b hb e ↦ by
    have ha' := mem_xI₁.mp (Finset.mem_coe.mp ha)
    have hb' := mem_xI₁.mp (Finset.mem_coe.mp hb)
    have h1 := slotOf_cellOf P v ha'.1 ha'.2
    rw [e, slotOf_cellOf P v hb'.1 hb'.2] at h1
    exact outSlot_inj ha' hb' (Option.some.inj h1).symm

/-- The coordinates other than `k`, `k'`: the public `h`, the public parameter, `π`, the values. -/
abbrev XQ : Type :=
  (Z → X) × PublicParameter × Equiv.Perm (X × Z) × (ValPos → Digest)

/-- The public coordinates as `((q, k), k')`. -/
def pvEquiv : (XQ × (X → Z)) × (X → Z) ≃ ((Z → X) × XW) × (ValPos → Digest) where
  toFun x := ((x.1.1.1, (x.1.1.2.1, x.1.1.2.2.1, x.1.2, x.2)), x.1.1.2.2.2)
  invFun y := (((y.1.1, y.1.2.1, y.1.2.2.1, y.2), y.1.2.2.2.1), y.1.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem cap_pvEquiv (q : XQ) (k k' : X → Z) :
    Set.EqOn (xO.cap (pvEquiv ((q, k), k')).1.2 (pvEquiv ((q, k), k')).1.1
      (pvEquiv ((q, k), k')).2) (fun s ↦ capOf k k' q.2.2.1 (cellOf q.2.1 q.2.2.2 s)) xI₁ :=
  fun _ hs ↦ outCap_one _ (nBlocks_of_one _ (mem_xI₁.mp (Finset.mem_coe.mp hs)).2)

open scoped Classical in
/-- **The output-cell collisions of one-block slots**: for a `PermGood π G` permutation, at most
`|xI₁|² (G + 1) / |Z|` of the public coordinates. -/
theorem card_mul_capColl_le (G : ℕ) :
    Fintype.card Z * (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
      PermGood y.1.2.2.1 G ∧ ¬Set.InjOn (xO.cap y.1.2 y.1.1 y.2) xI₁).card ≤
    Fintype.card (((Z → X) × XW) × (ValPos → Digest)) * (xI₁.card * xI₁.card * (G + 1)) :=
  card_mul_filter_capOf_le xI₁ pvEquiv (fun q : XQ ↦ q.2.2.1) (fun q ↦ cellOf q.2.1 q.2.2.2)
    (fun q ↦ cellOf_injOn q.2.1 q.2.2.2) G _ fun q k k' ↦ and_congr Iff.rfl (not_congr
      ⟨fun h ↦ h.congr (cap_pvEquiv q k k'), fun h ↦ h.congr (cap_pvEquiv q k k').symm⟩)

/-- The coordinates other than `π`. -/
abbrev XR : Type :=
  (Z → X) × PublicParameter × (X → Z) × (X → Z) × (ValPos → Digest)

/-- The public coordinates as `(π, rest)`. -/
def permEquiv : ((Z → X) × XW) × (ValPos → Digest) ≃ Equiv.Perm (X × Z) × XR where
  toFun y := (y.1.2.2.1, (y.1.1, y.1.2.1, y.1.2.2.2.1, y.1.2.2.2.2, y.2))
  invFun x := ((x.2.1, (x.2.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1)), x.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
/-- **The bad fraction of leanXMSS's reparametrization**: the tables outside the good set are at
most the bad permutations, the output-cell collisions of one-block slots
`|xI₁|² (G + 1) / |Z|`, and the path-collision event `PathBad` of the public coordinates. -/
theorem xGood_bad_frac_le (G : ℕ) :
    (Fintype.card (((Z → X) × (ValPos → Digest)) × XW) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun θ ↦ ¬XGood θ).card ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        ((xI₁.card * xI₁.card * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun y ↦ PathBad y).card := by
  set N := Fintype.card (((Z → X) × XW) × (ValPos → Digest))
  set A := (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
    PermGood y.1.2.2.1 G ∧ ¬Set.InjOn (xO.cap y.1.2 y.1.1 y.2) xI₁).card
  set B := (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
    ¬PermGood (permEquiv y).1 G).card
  set C := (Finset.univ.filter fun y ↦ PathBad y).card
  have hN : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hbad : (Finset.univ.filter fun θ ↦ ¬XGood θ).card ≤ A + B + C := by
    rw [card_not_eq_of_maps xO_consistent xO_ranked XGood XGoodPV (fun _ h ↦ good_of_xGood h)
      (fun _ h ↦ goodPV_of_with xPL h) (fun _ h ↦ xGoodPV_fwd h) (fun _ h ↦ xGood_back h)]
    refine card_filter_not_le_three XGoodPV _ _ _ fun y hy ↦ ?_
    by_contra hn
    obtain ⟨hA', hn'⟩ := not_or.mp hn
    obtain ⟨hB', hC'⟩ := not_or.mp hn'
    obtain ⟨hL, hP⟩ := not_or.mp hC'
    have hG : PermGood y.1.2.2.1 G := not_not.mp hB'
    have hI : Set.InjOn (xO.cap y.1.2 y.1.1 y.2) xI₁ := not_not.mp fun h ↦ hA' ⟨hG, h⟩
    exact hy ⟨injOn_of_leafSep hI (not_not.mp hL), not_not.mp hP⟩
  have hA : (A : ℝ≥0∞) ≤ N * (((xI₁.card * xI₁.card * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z) :=
    natCast_le_mul_div_of_mul_le Fintype.card_ne_zero (card_mul_capColl_le G)
  have hB : (N : ℝ≥0∞)⁻¹ * B = ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦
      ¬PermGood π G).card : ℝ≥0∞) / Fintype.card (Equiv.Perm (X × Z)) :=
    inv_card_mul_card_filter_comp_fst permEquiv fun π ↦ ¬PermGood π G
  rw [card_tab_eq]
  calc (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun θ ↦ ¬XGood θ).card
      ≤ (N : ℝ≥0∞)⁻¹ * ((A : ℝ≥0∞) + B + C) := by
        gcongr
        exact_mod_cast hbad
    _ = (N : ℝ≥0∞)⁻¹ * B + (N : ℝ≥0∞)⁻¹ * A + (N : ℝ≥0∞)⁻¹ * C := by ring
    _ ≤ _ := by
        rw [hB]
        gcongr
        calc (N : ℝ≥0∞)⁻¹ * A
            ≤ (N : ℝ≥0∞)⁻¹ * (N * (((xI₁.card * xI₁.card * (G + 1) : ℕ) : ℝ≥0∞) /
              Fintype.card Z)) := by gcongr
          _ = _ := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hN (ENNReal.natCast_ne_top _), one_mul]

open scoped Classical in
/-- **The averaging corollary for leanXMSS**: if `f ≤ g ∘ fwd` on `XGood` and `f ≤ 1` elsewhere,
the average of `f` over the tables is at most the average over the public data of the average over
the hidden values of `g`, plus the bad fraction of `xGood_bad_frac_le`. -/
theorem uavg_le_xmss (G : ℕ) (f : ((Z → X) × (ValPos → Digest)) × XW → ℝ≥0∞)
    (g : ((Z → X) × XW) × (ValPos → Digest) → ℝ≥0∞)
    (hfg : ∀ θ, XGood θ → f θ ≤ g (fwd xmssFix xO θ)) (hf : ∀ θ, ¬XGood θ → f θ ≤ 1) :
    uavg f ≤ uavg (fun p : (Z → X) × XW ↦ uavg fun v : ValPos → Digest ↦ g (p, v)) +
      (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        ((xI₁.card * xI₁.card * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun y ↦ PathBad y).card) :=
  (uavg_le_of_good xO_consistent XGood (fun _ h ↦ good_of_xGood h) f g hfg hf).trans
    (add_le_add le_rfl (xGood_bad_frac_le G))

end xmss

end Quantum.Xmss.Assembly

end
