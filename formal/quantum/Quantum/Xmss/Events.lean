module

public import Quantum.Xmss.Classify
public import Quantum.Sponge.Oracle.Hardwired

@[expose] public section

/-!
# The XMSS event of the hardwired runtime

The register of the hardwired runtime holds the adversary's databases `D`, the hardwired cells `W`
and a finite memory `m : Selections`: for each signed key, the block of its selected
message-digest input (one block) and the selected digest. The event (design 3.3) is

`Bad L N = {(D, W, m) | dbGrade W ≤ N ∧ union W D ∈ xmssBad L (exOf L W) m.toMemory}`,

S7's `xmssBad` with the exempted slots `exOf L W` (the table slots whose honest path `W` holds
with its honest values) and the memory `m.toMemory`. The cap `N` on the hardwired cells corrects
the design: without it the fresh bounds of the `k` and `k'` ports fail, since the bound holds for
every `W` and a large `W` gives the union many tails, so that a fresh `k` cell collides two
capacities (`¬ Good`) for most values.

The database facts hold for any target family that shrinks as cells are hardwired
(`HwTargetBad`, `TgtAnti`); `Bad L N` is the XMSS instance. They are stated for general rate and
capacity types: on the Keccak capacity, the decidable equality behind `Function.update` unfolds
into an enumeration of `Fin 512`, which deep unification must not reach.

* `upClosed_slice_bad`, `empty_not_mem_bad`, `freshBound_slice_bad`: the hypotheses of
  `eventWeight_spongeHardwiredRuntime_le` on the sponge calls, with rate
  `preimageRateBound (N + T) G 2^960` (`2^-128` on `h`, `fiber_div_card_X`).
* `bad_mono_program`: more hardwired cells, fewer targets.
* Program ports (the cell not yet hardwired): a program flips a state into `Bad` only through the
  filled cell. At most `2^960` values of an `h` cell (`card_flip_programH_bad_le`), none when the
  head-tail of the cell is an exempted honest tail (`not_mem_bad_programH_honest`: only `¬ Good`
  could flip, and `h` never changes goodness); the capacity-scale counts of `preimageRateBound`
  for `k`, `k'` (`card_flip_programK_bad_le`, `card_flip_programK'_bad_le`).
* Read ports: the read of the final `h` cell of a message-digest trial of key `(l, e)`, whose cell
  is not recorded (the `1 - P` part of `flipCost`), flips a state into `Bad` with the selection
  recorded for at most `msgCount * 2^960` values, whatever the read leaves in the cell
  (`card_flip_read_le`); `msgCount` counts the `h` cells of the union whose head-tail lies at
  `msg l e`. A trial that selects nothing flips nothing (`not_mem_bad_read_keep`). Reads of `k`
  and `k'` cells change no memory; their flips are the fresh fills of `freshBound_slice_bad`.
-/

namespace Quantum.Sponge

open Quantum

/-! ## Hardwired cells and the union -/

section Size

variable {A Y : Type}

theorem size_or_le [Fintype A] [DecidableEq A] (w d : Database A Y) :
    Database.size (fun a ↦ (w a).or (d a) : Database A Y) ≤ w.size + d.size := by
  unfold Database.size
  refine (Finset.card_le_card fun a ha ↦ ?_).trans (Finset.card_union_le _ _)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at ha ⊢
  cases h : w a <;> simp_all

theorem size_mono [Fintype A] {d d' : Database A Y} (h : ∀ a v, d a = some v → d' a = some v) :
    d.size ≤ d'.size := by
  unfold Database.size
  refine Finset.card_le_card fun a ha ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ha
  rw [h a v hv]
  rfl

theorem eq_some_of_update_none [DecidableEq A] {f : Database A Y} {a b : A} {w : Y}
    (h : Function.update f a none b = some w) : f b = some w := by
  by_cases hb : b = a
  · subst hb
    simp at h
  · rwa [Function.update_of_ne hb] at h

theorem update_some_of_none [DecidableEq A] {f : Database A Y} {a b : A} {v : Option Y} {w : Y}
    (ha : f a = none) (h : f b = some w) : Function.update f a v b = some w := by
  by_cases hb : b = a
  · subst hb
    simp [ha] at h
  · rwa [Function.update_of_ne hb]

theorem size_update_none_le [Fintype A] [DecidableEq A] (d : Database A Y) (a : A) :
    Database.size (Function.update d a none) ≤ d.size :=
  size_mono fun _ _ h ↦ eq_some_of_update_none h

end Size

theorem or_eq_some_of_or_eq_some {Y : Type} {a b b' : Option Y} {w : Y}
    (hb : ∀ v, b = some v → b' = some v) (h : a.or b = some w) : a.or b' = some w := by
  cases a with
  | none => exact hb w h
  | some _ => exact h

variable {X Z : Type}

/-- `W'` holds every hardwired cell of `W` with its value. -/
def HwLe (W W' : Hw X Z) : Prop :=
  (∀ z v, W.1 z = some v → W'.1 z = some v) ∧ (∀ x v, W.2.1 x = some v → W'.2.1 x = some v) ∧
    ∀ x v, W.2.2 x = some v → W'.2.2 x = some v

theorem HwLe.dbGrade_le [Fintype X] [Fintype Z] {W W' : Hw X Z} (h : HwLe W W') :
    dbGrade W ≤ dbGrade W' := by
  have h1 := size_mono h.1
  have h2 := size_mono h.2.1
  have h3 := size_mono h.2.2
  simp only [dbGrade]
  omega

theorem hwLe_programH [DecidableEq Z] {W : Hw X Z} {z : Z} (hW : W.1 z = none) (v : X) :
    HwLe W (Function.update W.1 z (some v), W.2) :=
  ⟨fun _ _ h ↦ update_some_of_none hW h, fun _ _ h ↦ h, fun _ _ h ↦ h⟩

theorem hwLe_programK [DecidableEq X] {W : Hw X Z} {x : X} (hW : W.2.1 x = none) (v : Z) :
    HwLe W (W.1, Function.update W.2.1 x (some v), W.2.2) :=
  ⟨fun _ _ h ↦ h, fun _ _ h ↦ update_some_of_none hW h, fun _ _ h ↦ h⟩

theorem hwLe_programK' [DecidableEq X] {W : Hw X Z} {x : X} (hW : W.2.2 x = none) (v : Z) :
    HwLe W (W.1, W.2.1, Function.update W.2.2 x (some v)) :=
  ⟨fun _ _ h ↦ h, fun _ _ h ↦ h, fun _ _ h ↦ update_some_of_none hW h⟩

/-- A larger database gives a larger union. -/
theorem extendsAll_union (W : Hw X Z) {D D' : DbReg X Z}
    (h1 : ∀ z w, D.1 z = some w → D'.1 z = some w)
    (h2 : ∀ x a, D.2.1 x = some a → D'.2.1 x = some a)
    (h3 : ∀ x a, D.2.2 x = some a → D'.2.2 x = some a) : ExtendsAll (union W D') (union W D) :=
  ⟨⟨fun x _ h ↦ or_eq_some_of_or_eq_some (h2 x) h, fun x _ h ↦ or_eq_some_of_or_eq_some (h3 x) h⟩,
    fun z _ h ↦ or_eq_some_of_or_eq_some (h1 z) h⟩

/-- Emptying an `h` cell. -/
theorem extendsAll_eraseH [DecidableEq Z] (U : Dbs X Z) (z : Z) :
    ExtendsAll U { U with h := Function.update U.h z none } :=
  ⟨⟨fun _ _ h ↦ h, fun _ _ h ↦ h⟩, fun _ _ h ↦ eq_some_of_update_none h⟩

/-- Emptying a `k` cell. -/
theorem extendsAll_eraseK [DecidableEq X] (U : Dbs X Z) (x : X) :
    ExtendsAll U { U with k := Function.update U.k x none } :=
  ⟨⟨fun _ _ h ↦ eq_some_of_update_none h, fun _ _ h ↦ h⟩, fun _ _ h ↦ h⟩

/-- Emptying a `k'` cell. -/
theorem extendsAll_eraseK' [DecidableEq X] (U : Dbs X Z) (x : X) :
    ExtendsAll U { U with k' := Function.update U.k' x none } :=
  ⟨⟨fun _ _ h ↦ h, fun _ _ h ↦ eq_some_of_update_none h⟩, fun _ _ h ↦ h⟩

/-- Changing a database `h` cell that is not hardwired changes the union's cell. -/
theorem union_updateH [DecidableEq Z] (W : Hw X Z) {z : Z} (hW : W.1 z = none)
    (dh : Database Z X)
    (dk dk' : Database X Z) (u : Option X) :
    union W (Function.update dh z u, dk, dk') =
      { union W (dh, dk, dk') with h := Function.update (union W (dh, dk, dk')).h z u } := by
  show Dbs.mk _ _ _ = Dbs.mk _ _ _
  congr 1
  funext z'
  by_cases h : z' = z
  · subst h
    simp [union, hwView, DbReg.toDbs, hW]
  · simp [union, hwView, DbReg.toDbs, Function.update_of_ne h]

/-- Changing a database `h` cell that is hardwired leaves the union. -/
theorem union_updateH_of_hw [DecidableEq Z] (W : Hw X Z) {z : Z} {w : X} (hW : W.1 z = some w)
    (dh : Database Z X) (dk dk' : Database X Z) (u : Option X) :
    union W (Function.update dh z u, dk, dk') = union W (dh, dk, dk') := by
  show Dbs.mk _ _ _ = Dbs.mk _ _ _
  congr 1
  funext z'
  by_cases h : z' = z
  · subst h
    simp [hwView, hW]
  · simp [hwView, Function.update_of_ne h]

/-- Changing a database `k` cell that is not hardwired changes the union's cell. -/
theorem union_updateK [DecidableEq X] (W : Hw X Z) {x : X} (hW : W.2.1 x = none)
    (dh : Database Z X)
    (dk dk' : Database X Z) (u : Option Z) :
    union W (dh, Function.update dk x u, dk') =
      { union W (dh, dk, dk') with k := Function.update (union W (dh, dk, dk')).k x u } := by
  show Dbs.mk _ _ _ = Dbs.mk _ _ _
  congr 1
  funext x'
  by_cases h : x' = x
  · subst h
    simp [union, hwView, DbReg.toDbs, hW]
  · simp [union, hwView, DbReg.toDbs, Function.update_of_ne h]

/-- Changing a database `k` cell that is hardwired leaves the union. -/
theorem union_updateK_of_hw [DecidableEq X] (W : Hw X Z) {x : X} {w : Z}
    (hW : W.2.1 x = some w)
    (dh : Database Z X) (dk dk' : Database X Z) (u : Option Z) :
    union W (dh, Function.update dk x u, dk') = union W (dh, dk, dk') := by
  show Dbs.mk _ _ _ = Dbs.mk _ _ _
  congr 1
  funext x'
  by_cases h : x' = x
  · subst h
    simp [hwView, hW]
  · simp [hwView, Function.update_of_ne h]

/-- Changing a database `k'` cell that is not hardwired changes the union's cell. -/
theorem union_updateK' [DecidableEq X] (W : Hw X Z) {x : X} (hW : W.2.2 x = none)
    (dh : Database Z X)
    (dk dk' : Database X Z) (u : Option Z) :
    union W (dh, dk, Function.update dk' x u) =
      { union W (dh, dk, dk') with k' := Function.update (union W (dh, dk, dk')).k' x u } := by
  show Dbs.mk _ _ _ = Dbs.mk _ _ _
  congr 1
  funext x'
  by_cases h : x' = x
  · subst h
    simp [union, hwView, DbReg.toDbs, hW]
  · simp [union, hwView, DbReg.toDbs, Function.update_of_ne h]

/-- Changing a database `k'` cell that is hardwired leaves the union. -/
theorem union_updateK'_of_hw [DecidableEq X] (W : Hw X Z) {x : X} {w : Z}
    (hW : W.2.2 x = some w)
    (dh : Database Z X) (dk dk' : Database X Z) (u : Option Z) :
    union W (dh, dk, Function.update dk' x u) = union W (dh, dk, dk') := by
  show Dbs.mk _ _ _ = Dbs.mk _ _ _
  congr 1
  funext x'
  by_cases h : x' = x
  · subst h
    simp [hwView, hW]
  · simp [hwView, Function.update_of_ne h]

/-- Programming an `h` cell: the union with the cell emptied, then filled with `v`. -/
theorem union_programH [DecidableEq Z] (W : Hw X Z) (D : DbReg X Z) (z : Z) (v : X) :
    union (Function.update W.1 z (some v), W.2) (Function.update D.1 z none, D.2) =
      { ({ union W D with h := Function.update (union W D).h z none } : Dbs X Z) with
        h := Function.update (Function.update (union W D).h z none) z (some v) } := by
  show Dbs.mk _ _ _ = Dbs.mk _ _ _
  congr 1
  funext z'
  by_cases h : z' = z
  · subst h
    simp [union, hwView, DbReg.toDbs]
  · simp [union, hwView, DbReg.toDbs, Function.update_of_ne h]

/-- Programming a `k` cell: the union with the cell emptied, then filled with `v`. -/
theorem union_programK [DecidableEq X] (W : Hw X Z) (D : DbReg X Z) (x : X) (v : Z) :
    union (W.1, Function.update W.2.1 x (some v), W.2.2)
        (D.1, Function.update D.2.1 x none, D.2.2) =
      { ({ union W D with k := Function.update (union W D).k x none } : Dbs X Z) with
        k := Function.update (Function.update (union W D).k x none) x (some v) } := by
  show Dbs.mk _ _ _ = Dbs.mk _ _ _
  congr 1
  funext x'
  by_cases h : x' = x
  · subst h
    simp [union, hwView, DbReg.toDbs]
  · simp [union, hwView, DbReg.toDbs, Function.update_of_ne h]

/-- Programming a `k'` cell: the union with the cell emptied, then filled with `v`. -/
theorem union_programK' [DecidableEq X] (W : Hw X Z) (D : DbReg X Z) (x : X) (v : Z) :
    union (W.1, W.2.1, Function.update W.2.2 x (some v))
        (D.1, D.2.1, Function.update D.2.2 x none) =
      { ({ union W D with k' := Function.update (union W D).k' x none } : Dbs X Z) with
        k' := Function.update (Function.update (union W D).k' x none) x (some v) } := by
  show Dbs.mk _ _ _ = Dbs.mk _ _ _
  congr 1
  funext x'
  by_cases h : x' = x
  · subst h
    simp [union, hwView, DbReg.toDbs]
  · simp [union, hwView, DbReg.toDbs, Function.update_of_ne h]

theorem size_unionH_le [Fintype X] [Fintype Z] [DecidableEq Z] (W D : DbReg X Z) :
    (union W D).h.size ≤ dbGrade W + dbGrade D :=
  (size_or_le W.1 D.1).trans (by simp only [dbGrade]; omega)

theorem size_unionK_le [Fintype X] [Fintype Z] [DecidableEq X] (W D : DbReg X Z) :
    (union W D).k.size ≤ dbGrade W + dbGrade D :=
  (size_or_le W.2.1 D.2.1).trans (by simp only [dbGrade]; omega)

theorem size_unionK'_le [Fintype X] [Fintype Z] [DecidableEq X] (W D : DbReg X Z) :
    (union W D).k'.size ≤ dbGrade W + dbGrade D :=
  (size_or_le W.2.2 D.2.2).trans (by simp only [dbGrade]; omega)

/-! ## Target events of the hardwired register -/

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z]
  {Y M : Type} {π : Equiv.Perm (X × Z)} {out : X → Y}
  {tgt : Hw X Z → M → List X → Option Y} {N : ℕ}

variable (π out) in
/-- **A target event of the hardwired register**: at most `N` hardwired cells per function, and
the union of the hardwired and the database cells in `TargetBad` for the targets of `(W, m)`. -/
def HwTargetBad (tgt : Hw X Z → M → List X → Option Y) (N : ℕ) : Set (HwReg X Z M) :=
  {x | dbGrade x.2.1 ≤ N ∧ union x.2.1 x.1 ∈ TargetBad π out (tgt x.2.1 x.2.2)}

/-- Targets that shrink as more cells are hardwired. -/
def TgtAnti (tgt : Hw X Z → M → List X → Option Y) : Prop :=
  ∀ W W' m, HwLe W W' → ∀ t y, tgt W' m t = some y → tgt W m t = some y

omit [DecidableEq X] [DecidableEq Z] in
theorem union_not_mem_of_not_mem_hwTargetBad {D : DbReg X Z} {W : Hw X Z} {m : M}
    (hs : (D, W, m) ∉ HwTargetBad π out tgt N) (hN : dbGrade W ≤ N) :
    union W D ∉ TargetBad π out (tgt W m) :=
  fun h ↦ hs ⟨hN, h⟩

omit [DecidableEq X] [DecidableEq Z] in
/-- The start without hardwired cells is outside the event. -/
theorem empty_not_mem_hwTargetBad (m : M) :
    ((Database.empty, Database.empty, Database.empty), (Database.empty, Database.empty,
      Database.empty), m) ∉ HwTargetBad π out tgt N :=
  fun h ↦ not_mem_targetBad_emptyDbs h.2

/-- **Every slice is upward closed**: a filled database cell is shadowed by a hardwired cell or
fills the union's cell. -/
theorem upClosed_slice_hwTargetBad (W : Hw X Z) (m : M) :
    UpClosed (slice (HwTargetBad π out tgt N) W m) where
  h D hD z u hz := ⟨hD.1, TargetBad.mono (extendsAll_union W (D := (D.h, D.k, D.k'))
    (D' := (Function.update D.h z (some u), D.k, D.k')) (fun _ _ h ↦ update_some_of_none hz h)
    (fun _ _ h ↦ h) fun _ _ h ↦ h) hD.2⟩
  k D hD x u hx := ⟨hD.1, TargetBad.mono (extendsAll_union W (D := (D.h, D.k, D.k'))
    (D' := (D.h, Function.update D.k x (some u), D.k')) (fun _ _ h ↦ h)
    (fun _ _ h ↦ update_some_of_none hx h) fun _ _ h ↦ h) hD.2⟩
  k' D hD x u hx := ⟨hD.1, TargetBad.mono (extendsAll_union W (D := (D.h, D.k, D.k'))
    (D' := (D.h, D.k, Function.update D.k' x (some u))) (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) fun _ _ h ↦ update_some_of_none hx h) hD.2⟩

open scoped Classical in
/-- **The fresh bound of every slice** below `T` database entries: the rates of
`preimageRateBound` for the union, which has fewer than `N + T` entries per function. -/
theorem freshBound_slice_hwTargetBad [Fintype M] [DecidableEq M]
    [DecidablePred (· ∈ HwTargetBad π out tgt N)] {G F : ℕ} (hπ : PermGood π G)
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (T : ℕ) (W : Hw X Z) (m : M) :
    FreshBound (slice (HwTargetBad π out tgt N) W m) T
      (preimageRateBound (X := X) (Z := Z) (N + T) G F) := by
  have fb := freshBound_targetBad (tgt := tgt W m) hπ hF (N + T)
  by_cases hN : dbGrade W ≤ N
  swap
  · have hE : ∀ D, D ∉ slice (HwTargetBad π out tgt N) W m := fun D hD ↦ hN hD.1
    refine ⟨fun D _ _ _ _ z _ ↦ ?_, fun D _ _ _ _ x _ ↦ ?_, fun D _ _ _ _ x _ ↦ ?_⟩ <;>
    · rw [Finset.filter_false_of_mem fun u _ ↦ hE _]
      simp
  have hWh : W.1.size ≤ N := by simp only [dbGrade] at hN; omega
  have hWk : W.2.1.size ≤ N := by simp only [dbGrade] at hN; omega
  have hWk' : W.2.2.size ≤ N := by simp only [dbGrade] at hN; omega
  refine ⟨fun D hD hh hk hk' z hz ↦ ?_, fun D hD hh hk hk' x hx ↦ ?_, fun D hD hh hk hk' x hx ↦ ?_⟩
  · have hU : union W (D.h, D.k, D.k') ∉ TargetBad π out (tgt W m) := fun h ↦ hD ⟨hN, h⟩
    rcases hWz : W.1 z with _ | w
    · have hUz : (union W (D.h, D.k, D.k')).h z = none := by
        change (W.1 z).or (D.h z) = none
        rw [hWz, hz]
        rfl
      refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2
        (Finset.card_le_card fun u hu ↦ ?_)) _) (fb.h _ hU ((size_or_le W.1 D.h).trans_lt
          (by omega)) ((size_or_le W.2.1 D.k).trans_lt (by omega))
          ((size_or_le W.2.2 D.k').trans_lt (by omega)) z hUz)
      have h2 : union W (Function.update D.h z (some u), D.k, D.k') ∈
          TargetBad π out (tgt W m) := (Finset.mem_filter.1 hu).2.2
      rw [union_updateH W hWz] at h2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩
    · rw [Finset.filter_false_of_mem fun u _ hu ↦ hU ?_]
      · simp
      have h2 : union W (Function.update D.h z (some u), D.k, D.k') ∈
          TargetBad π out (tgt W m) := hu.2
      rwa [union_updateH_of_hw W hWz] at h2
  · have hU : union W (D.h, D.k, D.k') ∉ TargetBad π out (tgt W m) := fun h ↦ hD ⟨hN, h⟩
    rcases hWx : W.2.1 x with _ | w
    · have hUx : (union W (D.h, D.k, D.k')).k x = none := by
        change (W.2.1 x).or (D.k x) = none
        rw [hWx, hx]
        rfl
      refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2
        (Finset.card_le_card fun u hu ↦ ?_)) _) (fb.k _ hU ((size_or_le W.1 D.h).trans_lt
          (by omega)) ((size_or_le W.2.1 D.k).trans_lt (by omega))
          ((size_or_le W.2.2 D.k').trans_lt (by omega)) x hUx)
      have h2 : union W (D.h, Function.update D.k x (some u), D.k') ∈
          TargetBad π out (tgt W m) := (Finset.mem_filter.1 hu).2.2
      rw [union_updateK W hWx] at h2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩
    · rw [Finset.filter_false_of_mem fun u _ hu ↦ hU ?_]
      · simp
      have h2 : union W (D.h, Function.update D.k x (some u), D.k') ∈
          TargetBad π out (tgt W m) := hu.2
      rwa [union_updateK_of_hw W hWx] at h2
  · have hU : union W (D.h, D.k, D.k') ∉ TargetBad π out (tgt W m) := fun h ↦ hD ⟨hN, h⟩
    rcases hWx : W.2.2 x with _ | w
    · have hUx : (union W (D.h, D.k, D.k')).k' x = none := by
        change (W.2.2 x).or (D.k' x) = none
        rw [hWx, hx]
        rfl
      refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2
        (Finset.card_le_card fun u hu ↦ ?_)) _) (fb.k' _ hU ((size_or_le W.1 D.h).trans_lt
          (by omega)) ((size_or_le W.2.1 D.k).trans_lt (by omega))
          ((size_or_le W.2.2 D.k').trans_lt (by omega)) x hUx)
      have h2 : union W (D.h, D.k, Function.update D.k' x (some u)) ∈
          TargetBad π out (tgt W m) := (Finset.mem_filter.1 hu).2.2
      rw [union_updateK' W hWx] at h2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩
    · rw [Finset.filter_false_of_mem fun u _ hu ↦ hU ?_]
      · simp
      have h2 : union W (D.h, D.k, Function.update D.k' x (some u)) ∈
          TargetBad π out (tgt W m) := hu.2
      rwa [union_updateK'_of_hw W hWx] at h2

omit [Fintype X] [DecidableEq X] [Fintype Z] in
/-- Filling an empty `h` cell `z` of a database outside `TargetBad tgt` with any content gives a
database outside `TargetBad tgt'`, if the new targets (`tgt'` beyond `tgt`) are not reached and
the head-tails of `z` have no target. `h` never changes goodness. -/
theorem not_mem_targetBad_fillH {U : Dbs X Z} {z : Z} (hz : U.h z = none)
    {tgt tgt' : List X → Option Y} {Q : List X → Y → Prop} (hU : U ∉ TargetBad π out tgt)
    (htgt : ∀ t y, tgt' t = some y → tgt t = some y ∨ Q t y)
    (hQ : ∀ t y, Q t y → ¬ Reaches π U out t y)
    (hhead : ∀ t xi, IsHeadTail π U t z xi → tgt' t = none) (u : Option X) :
    ({ U with h := Function.update U.h z u } : Dbs X Z) ∉ TargetBad π out tgt' := by
  obtain ⟨hG, hT⟩ := not_mem_targetBad_iff.1 hU
  have hr : ∀ t y, Reaches π { U with h := Function.update U.h z u } out t y →
      Reaches π U out t y ∨ ∃ xi, IsHeadTail π U t z xi := by
    intro t y h
    cases u with
    | none =>
      rw [show Function.update U.h z none = U.h from hz ▸ Function.update_eq_self z U.h] at h
      exact .inl h
    | some w => exact ((reaches_updateH_iff hz).1 h).imp_right fun ⟨xi, hi, _⟩ ↦ ⟨xi, hi⟩
  rintro (hb | ⟨t, y, ht, hreach⟩)
  · exact hb ((good_update_h_iff _).2 hG)
  rcases hr t y hreach with hreach | ⟨xi, hi⟩
  · rcases htgt t y ht with ht' | hq
    · exact hT t y ht' hreach
    · exact hQ t y hq hreach
  · rw [hhead t xi hi] at ht
    exact absurd ht (by simp)

/-! ## Program ports -/

omit [DecidableEq X] in
open scoped Classical in
/-- **Programming an `h` cell** that is not hardwired: at most `F` values flip a state outside the
event into it (the filled cell's head-tail has one target). -/
theorem card_flip_programH_le [DecidableEq Y] (hanti : TgtAnti tgt) {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) {D : DbReg X Z} {W : Hw X Z}
    {m : M} (hs : (D, W, m) ∉ HwTargetBad π out tgt N) {z : Z} (hW : W.1 z = none) :
    (Finset.univ.filter fun v : X ↦
      ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∈
        HwTargetBad π out tgt N).card ≤ F := by
  by_cases hN : dbGrade W ≤ N
  swap
  · rw [Finset.filter_false_of_mem fun v _ hv ↦ hN ((hwLe_programH hW v).dbGrade_le.trans hv.1)]
    simp
  have hU0 : ({ union W D with h := Function.update (union W D).h z none } : Dbs X Z) ∉
      TargetBad π out (tgt W m) :=
    fun h ↦ hs ⟨hN, TargetBad.mono (extendsAll_eraseH _ z) h⟩
  refine le_trans (Finset.card_le_card fun v hv ↦ ?_)
    (card_targetBad_updateH_le hF hU0 (z := z) (by simp))
  have h2 : union (Function.update W.1 z (some v), W.2) (Function.update D.1 z none, D.2) ∈
      TargetBad π out (tgt (Function.update W.1 z (some v), W.2) m) := (Finset.mem_filter.1 hv).2.2
  rw [union_programH] at h2
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
    targetBad_mono (hanti _ _ _ (hwLe_programH hW v)) h2⟩

omit [DecidableEq X] in
/-- **Programming an `h` cell without flips**: if in a good union no head-tail of the cell has a
target once it is hardwired, the programmed state is outside the event. -/
theorem not_mem_programH (hanti : TgtAnti tgt) {D : DbReg X Z} {W : Hw X Z} {m : M}
    (hs : (D, W, m) ∉ HwTargetBad π out tgt N) {z : Z} (hW : W.1 z = none) (v : X)
    (hhead : Good π (union W D) → ∀ t xi, IsHeadTail π (union W D) t z xi →
      tgt (Function.update W.1 z (some v), W.2) m t = none) :
    ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∉
      HwTargetBad π out tgt N := by
  rintro ⟨hN', h2⟩
  have hN := (hwLe_programH hW v).dbGrade_le.trans hN'
  have hU := union_not_mem_of_not_mem_hwTargetBad hs hN
  have hU0 : ({ union W D with h := Function.update (union W D).h z none } : Dbs X Z) ∉
      TargetBad π out (tgt W m) :=
    fun h ↦ hU (TargetBad.mono (extendsAll_eraseH _ z) h)
  have h2' : union (Function.update W.1 z (some v), W.2) (Function.update D.1 z none, D.2) ∈
      TargetBad π out (tgt (Function.update W.1 z (some v), W.2) m) := h2
  rw [union_programH] at h2'
  exact not_mem_targetBad_fillH (Q := fun _ _ ↦ False) (by simp) hU0
    (fun t y ht ↦ .inl (hanti _ _ _ (hwLe_programH hW v) t y ht)) (fun _ _ h ↦ h.elim)
    (fun t xi hi ↦ hhead (not_mem_targetBad_iff.1 hU).1 t xi
      (hi.mono (extendsAll_eraseH _ z).1)) (some v) h2'

open scoped Classical in
/-- **Programming a `k` cell** that is not hardwired: the capacity-scale count of the `k` fills
of the union with the cell emptied, which has at most `T` entries per function. -/
theorem card_flip_programK_le (hanti : TgtAnti tgt) {G T : ℕ} (hπ : PermGood π G)
    {D : DbReg X Z} {W : Hw X Z} {m : M} (hs : (D, W, m) ∉ HwTargetBad π out tgt N)
    (hT : N + dbGrade D ≤ T) {x : X} (hW : W.2.1 x = none) :
    (Finset.univ.filter fun v : Z ↦
      ((D.1, Function.update D.2.1 x none, D.2.2), (W.1, Function.update W.2.1 x (some v), W.2.2),
        m) ∈ HwTargetBad π out tgt N).card ≤ (T + 1) * ((T + 1) * T + 2 * T) * G := by
  by_cases hN : dbGrade W ≤ N
  swap
  · rw [Finset.filter_false_of_mem fun v _ hv ↦ hN ((hwLe_programK hW v).dbGrade_le.trans hv.1)]
    simp
  have hU0 : ({ union W D with k := Function.update (union W D).k x none } : Dbs X Z) ∉
      TargetBad π out (tgt W m) :=
    fun h ↦ hs ⟨hN, TargetBad.mono (extendsAll_eraseK _ x) h⟩
  refine le_trans (Finset.card_le_card fun v hv ↦ ?_)
    (card_targetBad_updateK_le hπ hU0 ((size_update_none_le _ _).trans
      ((size_unionK_le W D).trans (by omega))) ((size_unionK'_le W D).trans (by omega))
      (x := x) (by simp))
  have h2 : union (W.1, Function.update W.2.1 x (some v), W.2.2)
      (D.1, Function.update D.2.1 x none, D.2.2) ∈
      TargetBad π out (tgt (W.1, Function.update W.2.1 x (some v), W.2.2) m) :=
    (Finset.mem_filter.1 hv).2.2
  rw [union_programK] at h2
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
    targetBad_mono (hanti _ _ _ (hwLe_programK hW v)) h2⟩

open scoped Classical in
/-- **Programming a `k'` cell** that is not hardwired: the capacity-scale count of the `k'` fills
of the union with the cell emptied, which has at most `T` entries per function. -/
theorem card_flip_programK'_le (hanti : TgtAnti tgt) {G T : ℕ} (hπ : PermGood π G)
    {D : DbReg X Z} {W : Hw X Z} {m : M} (hs : (D, W, m) ∉ HwTargetBad π out tgt N)
    (hT : N + dbGrade D ≤ T) {x : X} (hW : W.2.2 x = none) :
    (Finset.univ.filter fun v : Z ↦
      ((D.1, D.2.1, Function.update D.2.2 x none), (W.1, W.2.1, Function.update W.2.2 x (some v)),
        m) ∈ HwTargetBad π out tgt N).card ≤
      (T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T := by
  by_cases hN : dbGrade W ≤ N
  swap
  · rw [Finset.filter_false_of_mem fun v _ hv ↦ hN ((hwLe_programK' hW v).dbGrade_le.trans hv.1)]
    simp
  have hU0 : ({ union W D with k' := Function.update (union W D).k' x none } : Dbs X Z) ∉
      TargetBad π out (tgt W m) :=
    fun h ↦ hs ⟨hN, TargetBad.mono (extendsAll_eraseK' _ x) h⟩
  refine le_trans (Finset.card_le_card fun v hv ↦ ?_)
    (card_targetBad_updateK'_le hπ hU0 ((size_unionH_le W D).trans (by omega))
      ((size_unionK_le W D).trans (by omega))
      ((size_update_none_le _ _).trans ((size_unionK'_le W D).trans (by omega)))
      (x' := x) (by simp))
  have h2 : union (W.1, W.2.1, Function.update W.2.2 x (some v))
      (D.1, D.2.1, Function.update D.2.2 x none) ∈
      TargetBad π out (tgt (W.1, W.2.1, Function.update W.2.2 x (some v)) m) :=
    (Finset.mem_filter.1 hv).2.2
  rw [union_programK'] at h2
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
    targetBad_mono (hanti _ _ _ (hwLe_programK' hW v)) h2⟩

/-! ## Read ports -/

omit [DecidableEq X] in
/-- **A read of an `h` cell** that is neither hardwired nor recorded, with memory `m'` after the
read: whatever the read leaves in the cell, the state is outside the event if the new targets
are not reached and, in a good union, the head-tails of the cell have no target. -/
theorem not_mem_readH {D : DbReg X Z} {W : Hw X Z} {m m' : M}
    (hs : (D, W, m) ∉ HwTargetBad π out tgt N) {z : Z} (hW : W.1 z = none) (hD : D.1 z = none)
    {Q : List X → Y → Prop} (hext : ∀ t y, tgt W m' t = some y → tgt W m t = some y ∨ Q t y)
    (hQ : ∀ t y, Q t y → ¬ Reaches π (union W D) out t y)
    (hhead : Good π (union W D) → ∀ t xi, IsHeadTail π (union W D) t z xi → tgt W m' t = none)
    (u : Option X) : ((Function.update D.1 z u, D.2), W, m') ∉ HwTargetBad π out tgt N := by
  rintro ⟨hN, h2⟩
  have hU := union_not_mem_of_not_mem_hwTargetBad hs hN
  have h2' : union W (Function.update D.1 z u, D.2.1, D.2.2) ∈ TargetBad π out (tgt W m') := h2
  rw [union_updateH W hW] at h2'
  exact not_mem_targetBad_fillH (U := union W (D.1, D.2.1, D.2.2))
    (show (W.1 z).or (D.1 z) = none by rw [hW, hD]; rfl) hU hext hQ
    (hhead (not_mem_targetBad_iff.1 hU).1) u h2'

open scoped Classical in
/-- The `h` cells of `U` whose head-tail satisfies `P`: in a good database, the tails satisfying
`P` that reach an output. -/
noncomputable def tailCount (π : Equiv.Perm (X × Z)) (U : Dbs X Z) (P : List X → Prop) : ℕ :=
  (Finset.univ.filter fun z : Z ↦ ∃ t xi w, P t ∧ IsHeadTail π U t z xi ∧ U.h z = some w).card

omit [Fintype X] [DecidableEq X] [DecidableEq Z] [AddCommGroup X] in
theorem tailCount_le_size (π : Equiv.Perm (X × Z)) (U : Dbs X Z) (P : List X → Prop) :
    tailCount π U P ≤ U.h.size := by
  classical
  unfold tailCount Database.size
  exact Finset.card_le_card fun z hz ↦ by
    obtain ⟨_, _, w, _, _, hw⟩ := (Finset.mem_filter.1 hz).2
    simp [hw]

omit [DecidableEq Z] in
open scoped Classical in
/-- **At most `tailCount * F` values flip a new target**: the values `v` for which a tail
satisfying `P`, other than `t₀`, reaches `out (xi + v)`. Each such output is the output of an `h`
cell, one per cell in a good database, and `F` bounds the fibers of `out`. -/
theorem card_flips_le [DecidableEq Y] {U : Dbs X Z} (hG : Good π U) {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (P : List X → Prop)
    (t₀ : List X) (xi : X) :
    (Finset.univ.filter fun v : X ↦ ∃ t, P t ∧ t ≠ t₀ ∧ Reaches π U out t (out (xi + v))).card ≤
      tailCount π U P * F := by
  let C := Finset.univ.filter fun z : Z ↦ ∃ t xi w, P t ∧ IsHeadTail π U t z xi ∧ U.h z = some w
  let S : Z → Finset X := fun z ↦ Finset.univ.filter fun v : X ↦ ∃ t xi' w,
    IsHeadTail π U t z xi' ∧ U.h z = some w ∧ out (xi + v) = out (xi' + w)
  have hsub : (Finset.univ.filter fun v : X ↦
      ∃ t, P t ∧ t ≠ t₀ ∧ Reaches π U out t (out (xi + v))) ⊆ C.biUnion S := by
    intro v hv
    obtain ⟨t, hP, -, z, xi', w, hi, hw, hy⟩ := (Finset.mem_filter.1 hv).2
    exact Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨Finset.mem_univ _, t, xi', w, hP, hi,
      hw⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, t, xi', w, hi, hw, hy⟩⟩
  have hS : ∀ z ∈ C, (S z).card ≤ F := by
    intro z _
    rcases Finset.eq_empty_or_nonempty (S z) with he | ⟨v0, hv0⟩
    · simp [he]
    obtain ⟨t0, xi0, w0, hi0, hw0, -⟩ := (Finset.mem_filter.1 hv0).2
    refine card_le_of_out_translate hF xi (out (xi0 + w0)) fun v hv ↦ ?_
    obtain ⟨t, xi', w, hi, hw, hy⟩ := (Finset.mem_filter.1 hv).2
    obtain ⟨rfl, rfl⟩ := hG.isHeadTail_unique hi hi0
    obtain rfl := Option.some_injective _ (hw.symm.trans hw0)
    exact hy
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul C S _ hS)

open scoped Classical in
/-- **A read of an `h` cell that may add a target per tail satisfying `P`**: with memory `m' v`
after reading `v`, new targets `out (xi + v)` only on tails satisfying `P` other than `t₀`, and,
in a good union, no target on the head-tails of the cell, at most `tailCount * F` values flip a
state outside the event into it, whatever the read leaves in the cell. -/
theorem card_flip_readH_le [DecidableEq Y] {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) {D : DbReg X Z} {W : Hw X Z}
    {m : M} (hs : (D, W, m) ∉ HwTargetBad π out tgt N) {z : Z} (hW : W.1 z = none)
    (hD : D.1 z = none) (P : List X → Prop) (t₀ : List X) (xi : X) (m' : X → M)
    (hext : ∀ v t y, tgt W (m' v) t = some y →
      tgt W m t = some y ∨ (P t ∧ t ≠ t₀ ∧ y = out (xi + v)))
    (hhead : Good π (union W D) → ∀ v t xi', IsHeadTail π (union W D) t z xi' →
      tgt W (m' v) t = none) :
    (Finset.univ.filter fun v : X ↦ ∃ u : Option X,
      ((Function.update D.1 z u, D.2), W, m' v) ∈ HwTargetBad π out tgt N).card ≤
        tailCount π (union W D) P * F := by
  by_cases hN : dbGrade W ≤ N
  · have hG := (not_mem_targetBad_iff.1 (union_not_mem_of_not_mem_hwTargetBad hs hN)).1
    refine le_trans (Finset.card_le_card fun v hv ↦ ?_) (card_flips_le hG hF P t₀ xi)
    obtain ⟨u, hu⟩ := (Finset.mem_filter.1 hv).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    by_contra hf
    exact not_mem_readH hs hW hD (Q := fun t y ↦ P t ∧ t ≠ t₀ ∧ y = out (xi + v)) (hext v)
      (fun t y ⟨hP, hne, hy⟩ hr ↦ hf ⟨t, hP, hne, hy ▸ hr⟩) (fun hG' ↦ hhead hG' v) u hu
  · rw [Finset.filter_false_of_mem fun v _ ⟨_, hu⟩ ↦ hN hu.1]
    simp

end Quantum.Sponge

namespace Quantum.Xmss

open Quantum Quantum.Sponge HashSig LeanXmss
open scoped ENNReal

/-! ## The finite memory -/

/-- A one-block input with block `x`, if there is one. -/
noncomputable def blockInput (x : X) : HashInput :=
  Classical.epsilon fun c ↦ blocks c = [x]

theorem blocks_blockInput {x : X} {c : HashInput} (h : blocks c = [x]) :
    blocks (blockInput x) = [x] :=
  Classical.epsilon_spec (p := fun c ↦ blocks c = [x]) ⟨c, h⟩

theorem blockInput_eq {x : X} {c : HashInput} (h : blocks c = [x]) : blockInput x = c :=
  blocks_injective ((blocks_blockInput h).trans h.symm)

/-- **The memory of the hardwired register**: for each signed key, the block of its selected
message-digest input and the selected digest. Finite, unlike S7's `Memory`. -/
abbrev Selections := Layer → KeyIndex → Option (X × Digest)

/-- The memory of S7 that a finite memory stands for. -/
noncomputable def Selections.toMemory (m : Selections) : Memory :=
  fun l e ↦ (m l e).map fun s ↦ (blockInput s.1, s.2)

/-- Recording the selection of key `e` of layer `l`: block `x`, digest `y`. -/
def Selections.select (m : Selections) (l : Layer) (e : KeyIndex) (x : X) (y : Digest) :
    Selections :=
  Function.update m l (Function.update (m l) e (some (x, y)))

theorem Selections.toMemory_select_self (m : Selections) (l : Layer) (e : KeyIndex) (x : X)
    (y : Digest) : (m.select l e x y).toMemory l e = some (blockInput x, y) := by
  simp [Selections.toMemory, Selections.select]

theorem Selections.toMemory_select_of_ne (m : Selections) {l l' : Layer} {e e' : KeyIndex} (x : X)
    (y : Digest) (h : ¬(l' = l ∧ e' = e)) :
    (m.select l e x y).toMemory l' e' = m.toMemory l' e' := by
  simp only [Selections.toMemory, Selections.select]
  by_cases hl : l' = l
  · subst hl
    rw [Function.update_self, Function.update_of_ne fun he ↦ h ⟨rfl, he⟩]
  · rw [Function.update_of_ne hl]

/-- A recorded selection is S7's memory entry of its input. -/
theorem Selections.toMemory_of_blocks {m : Selections} {l : Layer} {e : KeyIndex} {x : X}
    {y : Digest} {c : HashInput} (hm : m l e = some (x, y)) (hc : blocks c = [x]) :
    m.toMemory l e = some (c, y) := by
  simp [Selections.toMemory, hm, blockInput_eq hc]

theorem Selections.toMemory_eq_none {m : Selections} {l : Layer} {e : KeyIndex}
    (hm : m l e = none) : m.toMemory l e = none := by
  simp [Selections.toMemory, hm]

/-! ## Exempted slots -/

/-- **The exempted slots**: the table slots whose honest path the hardwired cells hold with its
honest values. -/
def exOf (L : HonestTable) (W : Hw X Z) : Set Slot :=
  {s | InTable s ∧ L.HeldIn W.toDbs s}

theorem heldBy_mono {W W' : Hw X Z} (h : HwLe W W') {e : SpongeRead X Z}
    (he : e.HeldBy W.toDbs) : e.HeldBy W'.toDbs := by
  cases e with
  | h z a => exact h.1 z a he
  | k x a => exact h.2.1 x a he
  | k' x a => exact h.2.2 x a he

theorem exOf_mono (L : HonestTable) {W W' : Hw X Z} (h : HwLe W W') : exOf L W ⊆ exOf L W' :=
  fun _ hs ↦ ⟨hs.1, fun input hi e he ↦ heldBy_mono h (hs.2 input hi e he)⟩

/-- The hardwired cells are cells of the union. -/
theorem heldBy_union {W : Hw X Z} (D : DbReg X Z) {e : SpongeRead X Z} (he : e.HeldBy W.toDbs) :
    e.HeldBy (union W D) := by
  cases e with
  | h z a =>
    change (W.1 z).or (D.1 z) = some a
    rw [show W.1 z = some a from he]
    rfl
  | k x a =>
    change (W.2.1 x).or (D.2.1 x) = some a
    rw [show W.2.1 x = some a from he]
    rfl
  | k' x a =>
    change (W.2.2 x).or (D.2.2 x) = some a
    rw [show W.2.2 x = some a from he]
    rfl

/-- **S7's hypothesis on the exempted slots** (`win_imp_bad`'s `hHeld` for `Ex = exOf L W` and the
union): they are held by the union with their honest values. -/
theorem heldIn_union_of_mem_exOf {L : HonestTable} {W : Hw X Z} (D : DbReg X Z) {s : Slot}
    (hs : s ∈ exOf L W) : L.HeldIn (union W D) s :=
  fun input hi e he ↦ heldBy_union D (hs.2 input hi e he)

/-! ## Targets -/

section Targets

variable {L : HonestTable}

/-- More exempted slots, fewer targets. -/
theorem xmssTgt_mono {Ex Ex' : Set Slot} (h : Ex ⊆ Ex') {M : Memory} {t : List X} {y : Digest}
    (ht : xmssTgt L Ex' M t = some y) : xmssTgt L Ex M t = some y := by
  have key : ∀ s, structTgt L Ex' t s = some y → structTgt L Ex t s = some y := fun s hs ↦ by
    unfold structTgt at hs ⊢
    by_cases hc' : L.honestTail s = some t ∧ s ∈ Ex'
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc')] at hs
      cases hs
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc')] at hs
      rw [ite_eq_right_of_eq_false _ _ (eq_false fun hc ↦ hc' ⟨hc.1, h hc.2⟩)]
      exact hs
  unfold xmssTgt at ht ⊢
  revert ht
  cases slotOf L.param t with
  | none => exact id
  | some s =>
    simp only [Option.bind_some]
    intro ht
    cases s with
    | msg l e => exact ht
    | chain => exact key _ ht
    | leaf => exact key _ ht
    | node => exact key _ ht
    | prf => exact key _ ht
    | rnd => exact key _ ht
    | param => exact key _ ht
    | seed => exact key _ ht

/-- Hardwiring removes targets. -/
theorem xmssBad_mono {Ex Ex' : Set Slot} (h : Ex ⊆ Ex') (M : Memory) :
    xmssBad L Ex' M ⊆ xmssBad L Ex M :=
  targetBad_mono fun _ _ ↦ xmssTgt_mono h

/-- **`bad_mono_program`**: hardwiring more cells (programming hidden honest cells with their table
values) never adds a Struct or Enc target, since it only enlarges the exemption. -/
theorem bad_mono_program {W W' : Hw X Z} (h : HwLe W W') (M : Memory) :
    xmssBad L (exOf L W') M ⊆ xmssBad L (exOf L W) M :=
  xmssBad_mono (exOf_mono L h) M

theorem structural_of_honestTail {s : Slot} {t : List X} (h : L.honestTail s = some t) :
    Structural s := by
  have hin : InTable s := by
    by_contra hn
    simp [HonestTable.honestTail, HonestTable.honestInput, hn] at h
  cases s <;> trivial

/-- An exempted honest tail has no target. -/
theorem xmssTgt_honestTail {Ex : Set Slot} {M : Memory} {s : Slot} {t : List X}
    (h : L.honestTail s = some t) (hs : s ∈ Ex) : xmssTgt L Ex M t = none := by
  rw [xmssTgt, L.slotOf_honestTail h, Option.bind_some,
    slotTgt_of_structural (structural_of_honestTail h), structTgt]
  split_ifs with hc
  · rfl
  · exact absurd ⟨h, hs⟩ hc

/-- A tail at the message slot of an unsigned key has no target. -/
theorem xmssTgt_msg_none {Ex : Set Slot} {M : Memory} {t : List X} {l : Layer} {e : KeyIndex}
    (hs : slotOf L.param t = some (.msg l e)) (hm : M l e = none) : xmssTgt L Ex M t = none := by
  rw [xmssTgt, hs, Option.bind_some]
  show (M l e).bind _ = none
  rw [hm]
  rfl

/-- Recording a selection adds the selected digest as the target of the other tails at its
message slot, and nothing else. -/
theorem xmssTgt_select {Ex : Set Slot} {m : Selections} {l : Layer} {e : KeyIndex} {x : X}
    {y y' : Digest} {t : List X} (h : xmssTgt L Ex (m.select l e x y).toMemory t = some y') :
    xmssTgt L Ex m.toMemory t = some y' ∨
      (slotOf L.param t = some (.msg l e) ∧ t ≠ blocks (blockInput x) ∧ y' = y) := by
  unfold xmssTgt at h ⊢
  revert h
  cases hs : slotOf L.param t with
  | none => exact fun h ↦ absurd h (by simp)
  | some s =>
    simp only [Option.bind_some]
    intro h
    cases s with
    | msg l' e' =>
      by_cases hk : l' = l ∧ e' = e
      · obtain ⟨rfl, rfl⟩ := hk
        right
        change ((m.select l' e' x y).toMemory l' e').bind _ = some y' at h
        rw [Selections.toMemory_select_self, Option.bind_some] at h
        by_cases ht : t = blocks (blockInput x)
        · simp [ht] at h
        · simp only [ht, ↓reduceIte, Option.some.injEq] at h
          exact ⟨rfl, ht, h.symm⟩
      · left
        change ((m.select l e x y).toMemory l' e').bind _ = some y' at h
        rw [Selections.toMemory_select_of_ne m x y hk] at h
        exact h
    | chain => exact .inl h
    | leaf => exact .inl h
    | node => exact .inl h
    | prf => exact .inl h
    | rnd => exact .inl h
    | param => exact .inl h
    | seed => exact .inl h

end Targets

/-! ## The event -/

/-- The targets of the hardwired register's classical data `(W, m)`. -/
noncomputable def xmssTgtHw (L : HonestTable) (W : Hw X Z) (m : Selections) :
    List X → Option Digest :=
  xmssTgt L (exOf L W) m.toMemory

theorem tgtAnti_xmssTgtHw (L : HonestTable) : TgtAnti (xmssTgtHw L) :=
  fun _ _ _ h _ _ ↦ xmssTgt_mono (exOf_mono L h)

/-- **The XMSS event of the hardwired register**: at most `N` hardwired cells per function, and
the union of the hardwired and database cells in S7's `xmssBad`, with the slots of the hardwired
honest paths exempted and the recorded selections. -/
abbrev Bad (L : HonestTable) (N : ℕ) : Set (HwReg X Z Selections) :=
  HwTargetBad L.perm trunc128 (xmssTgtHw L) N

variable {L : HonestTable} {N : ℕ}

theorem mem_bad_iff {D : DbReg X Z} {W : Hw X Z} {m : Selections} :
    (D, W, m) ∈ Bad L N ↔ dbGrade W ≤ N ∧ union W D ∈ xmssBad L (exOf L W) m.toMemory :=
  Iff.rfl

/-- **A win is in the event**: S7's conclusion for the union, with few hardwired cells. -/
theorem mem_bad_of {D : DbReg X Z} {W : Hw X Z} {m : Selections} (hN : dbGrade W ≤ N)
    (h : union W D ∈ xmssBad L (exOf L W) m.toMemory) : (D, W, m) ∈ Bad L N :=
  ⟨hN, h⟩

/-- **The start is outside the event**: no database and no hardwired cell. -/
theorem empty_not_mem_bad (m : Selections) :
    ((Database.empty, Database.empty, Database.empty), (Database.empty, Database.empty,
      Database.empty), m) ∉ Bad L N :=
  empty_not_mem_hwTargetBad m

/-- **Every slice of the event is upward closed.** -/
theorem upClosed_slice_bad (W : Hw X Z) (m : Selections) : UpClosed (slice (Bad L N) W m) :=
  upClosed_slice_hwTargetBad W m

theorem card_X : Fintype.card X = 2 ^ 1088 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The `h`-port rate of `trunc128`: `2^960 / |X| = 2^-128`. -/
theorem fiber_div_card_X : ((2 ^ 960 : ℕ) : ℝ≥0∞) / Fintype.card X = (2 ^ 128)⁻¹ := by
  rw [card_X, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, show (1088 : ℕ) = 960 + 128 from rfl,
    pow_add]
  calc (2 : ℝ≥0∞) ^ 960 / (2 ^ 960 * 2 ^ 128) = 2 ^ 960 * 1 / (2 ^ 960 * 2 ^ 128) := by
        rw [mul_one]
    _ = 1 / 2 ^ 128 := ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ (by simp))
        (ENNReal.pow_ne_top (by simp))
    _ = (2 ^ 128)⁻¹ := one_div _

theorem card_fiber_trunc128_le (d : Digest) :
    (Finset.univ.filter fun x : X ↦ trunc128 x = d).card ≤ 2 ^ 960 :=
  (card_fiber_trunc128 d).le

/-- **The fresh bound of every slice** below `T` database entries: the rates of
`preimageRateBound (N + T) G 2^960`; on `h`, `2^960 / |X| = 2^-128` (`fiber_div_card_X`). -/
theorem freshBound_slice_bad [DecidablePred (· ∈ Bad L N)] {G : ℕ} (hπ : PermGood L.perm G)
    (T : ℕ) (W : Hw X Z) (m : Selections) :
    FreshBound (slice (Bad L N) W m) T (preimageRateBound (X := X) (Z := Z) (N + T) G (2 ^ 960)) :=
  freshBound_slice_hwTargetBad hπ (fun d ↦ by convert card_fiber_trunc128_le d) T W m

/-! ## Program ports -/

open scoped Classical in
/-- **Programming an `h` cell** that is not hardwired: at most `2^960` values flip a state outside
`Bad` into it. -/
theorem card_flip_programH_bad_le {D : DbReg X Z} {W : Hw X Z} {m : Selections}
    (hs : (D, W, m) ∉ Bad L N) {z : Z} (hW : W.1 z = none) :
    (Finset.univ.filter fun v : X ↦
      ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∈
        Bad L N).card ≤ 2 ^ 960 :=
  card_flip_programH_le (tgtAnti_xmssTgtHw L) card_fiber_trunc128_le hs hW

/-- **Programming the final `h` cell of an exempted honest path**: no value flips. In the good
union the head-tail of the cell is the honest tail, exempted once the cell is hardwired. -/
theorem not_mem_bad_programH_honest {D : DbReg X Z} {W : Hw X Z} {m : Selections}
    (hs : (D, W, m) ∉ Bad L N) {z : Z} (hW : W.1 z = none) (v : X) {s : Slot} {t₀ : List X}
    {xi₀ : X} (ht : L.honestTail s = some t₀)
    (hex : s ∈ exOf L (Function.update W.1 z (some v), W.2))
    (hhead : IsHeadTail L.perm (union W D) t₀ z xi₀) :
    ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∉ Bad L N :=
  not_mem_programH (tgtAnti_xmssTgtHw L) hs hW v fun hG _ _ hi ↦ by
    obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hhead
    exact xmssTgt_honestTail ht hex

open scoped Classical in
/-- **Programming a `k` cell** that is not hardwired: the capacity-scale count of
`preimageRateBound`, for at most `T ≥ N + dbGrade D` entries. -/
theorem card_flip_programK_bad_le {G T : ℕ} (hπ : PermGood L.perm G) {D : DbReg X Z}
    {W : Hw X Z} {m : Selections} (hs : (D, W, m) ∉ Bad L N) (hT : N + dbGrade D ≤ T) {x : X}
    (hW : W.2.1 x = none) :
    (Finset.univ.filter fun v : Z ↦
      ((D.1, Function.update D.2.1 x none, D.2.2), (W.1, Function.update W.2.1 x (some v), W.2.2),
        m) ∈ Bad L N).card ≤ (T + 1) * ((T + 1) * T + 2 * T) * G :=
  card_flip_programK_le (tgtAnti_xmssTgtHw L) hπ hs hT hW

open scoped Classical in
/-- **Programming a `k'` cell** that is not hardwired: the capacity-scale count of
`preimageRateBound`, for at most `T ≥ N + dbGrade D` entries. -/
theorem card_flip_programK'_bad_le {G T : ℕ} (hπ : PermGood L.perm G) {D : DbReg X Z}
    {W : Hw X Z} {m : Selections} (hs : (D, W, m) ∉ Bad L N) (hT : N + dbGrade D ≤ T) {x : X}
    (hW : W.2.2 x = none) :
    (Finset.univ.filter fun v : Z ↦
      ((D.1, D.2.1, Function.update D.2.2 x none), (W.1, W.2.1, Function.update W.2.2 x (some v)),
        m) ∈ Bad L N).card ≤ (T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T :=
  card_flip_programK'_le (tgtAnti_xmssTgtHw L) hπ hs hT hW

/-! ## Read ports -/

/-- The `h` cells of `U` whose head-tail lies at the message slot of key `e` of layer `l`: the
tails at that slot that reach an output (one per cell in a good database). -/
noncomputable def msgCount (L : HonestTable) (U : Dbs X Z) (l : Layer) (e : KeyIndex) : ℕ :=
  tailCount L.perm U fun t ↦ slotOf L.param t = some (.msg l e)

theorem msgCount_le_size (L : HonestTable) (U : Dbs X Z) (l : Layer) (e : KeyIndex) :
    msgCount L U l e ≤ U.h.size :=
  tailCount_le_size _ _ _

/-- A selection read: the read of the final `h` cell `z` of the message-digest trial of key
`(l, e)` with block `x` and rate `xi`. The cell is neither hardwired nor recorded, the key has no
selection, and the trial's tail (its one block) is the head-tail of `z` at slot `msg l e`. -/
structure SelectRead (L : HonestTable) (D : DbReg X Z) (W : Hw X Z) (m : Selections) (z : Z)
    (l : Layer) (e : KeyIndex) (x xi : X) : Prop where
  hw : W.1 z = none
  hd : D.1 z = none
  hm : m l e = none
  slot : slotOf L.param (blocks (blockInput x)) = some (.msg l e)
  head : IsHeadTail L.perm (union W D) (blocks (blockInput x)) z xi

/-- Under a selection read, the head-tails of the read cell have no target, before or after the
selection is recorded. -/
theorem selectRead_head_none {D : DbReg X Z} {W : Hw X Z} {m : Selections} {z : Z} {l : Layer}
    {e : KeyIndex} {x xi : X} (hr : SelectRead L D W m z l e x xi) (hG : Good L.perm (union W D))
    {y : Digest} {t : List X} {xi' : X} (hi : IsHeadTail L.perm (union W D) t z xi') :
    xmssTgtHw L W (m.select l e x y) t = none := by
  obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hr.head
  rcases hy : xmssTgtHw L W (m.select l e x y) (blocks (blockInput x)) with _ | y'
  · rfl
  rcases xmssTgt_select hy with h | ⟨-, hne, -⟩
  · rw [xmssTgt_msg_none hr.slot (Selections.toMemory_eq_none hr.hm)] at h
    cases h
  · exact absurd rfl hne

/-- **A selection read whose digest no other tail at the message slot reaches**: whatever the
read leaves in the cell, the state with the selection recorded is outside `Bad`. -/
theorem not_mem_bad_read_select {D : DbReg X Z} {W : Hw X Z} {m : Selections} {z : Z} {l : Layer}
    {e : KeyIndex} {x xi : X} (hs : (D, W, m) ∉ Bad L N) (hr : SelectRead L D W m z l e x xi)
    {v : X} (hv : ∀ t, slotOf L.param t = some (.msg l e) → t ≠ blocks (blockInput x) →
      ¬ Reaches L.perm (union W D) trunc128 t (trunc128 (xi + v))) (u : Option X) :
    ((Function.update D.1 z u, D.2), W, m.select l e x (trunc128 (xi + v))) ∉ Bad L N :=
  not_mem_readH hs hr.hw hr.hd
    (Q := fun t y ↦ slotOf L.param t = some (.msg l e) ∧ t ≠ blocks (blockInput x) ∧
      y = trunc128 (xi + v))
    (fun _ _ ht ↦ xmssTgt_select ht)
    (fun t _ ⟨hslot, hne, hy⟩ hreach ↦ hv t hslot hne (hy ▸ hreach))
    (fun hG _ _ hi ↦ selectRead_head_none hr hG hi) u

/-- **A read that selects nothing flips nothing**: the trial's tail is at the message slot of an
unsigned key, so it has no target. -/
theorem not_mem_bad_read_keep {D : DbReg X Z} {W : Hw X Z} {m : Selections} {z : Z} {l : Layer}
    {e : KeyIndex} {x xi : X} (hs : (D, W, m) ∉ Bad L N) (hr : SelectRead L D W m z l e x xi)
    (u : Option X) : ((Function.update D.1 z u, D.2), W, m) ∉ Bad L N :=
  not_mem_readH hs hr.hw hr.hd (Q := fun _ _ ↦ False) (fun _ _ ht ↦ .inl ht)
    (fun _ _ h ↦ h.elim)
    (fun hG t _ hi ↦ by
      obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hr.head
      exact xmssTgt_msg_none hr.slot (Selections.toMemory_eq_none hr.hm)) u

open scoped Classical in
/-- **`card_flip_read_le`**: a selection read of key `(l, e)` adds its Enc target, which flips a
state outside `Bad` for at most `msgCount * 2^960` values of the read cell, whatever the read
leaves in the cell: the flips are the old outputs of the other tails at `msg l e`. -/
theorem card_flip_read_le {D : DbReg X Z} {W : Hw X Z} {m : Selections} {z : Z} {l : Layer}
    {e : KeyIndex} {x xi : X} (hs : (D, W, m) ∉ Bad L N) (hr : SelectRead L D W m z l e x xi) :
    (Finset.univ.filter fun v : X ↦ ∃ u : Option X,
      ((Function.update D.1 z u, D.2), W, m.select l e x (trunc128 (xi + v))) ∈ Bad L N).card ≤
        msgCount L (union W D) l e * 2 ^ 960 :=
  card_flip_readH_le card_fiber_trunc128_le hs hr.hw hr.hd
    (fun t ↦ slotOf L.param t = some (.msg l e)) (blocks (blockInput x)) xi
    (fun v ↦ m.select l e x (trunc128 (xi + v))) (fun _ _ _ ht ↦ xmssTgt_select ht)
    (fun hG _ _ _ hi ↦ selectRead_head_none hr hG hi)

end Quantum.Xmss

end
