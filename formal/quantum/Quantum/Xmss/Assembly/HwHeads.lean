module

public import Quantum.Xmss.Assembly.EncRefined
public import Quantum.Xmss.Assembly.ProgSafe

@[expose] public section

/-!
# The hardwired `h` cells head honest tails

EncRefined's remaining invariant: along the challenge prefix `prefixR A L`, at every table `L`, every
call is presented only states whose hardwired `h` cells head honest (non-message) head-tails of the
union (`HwHeadsHonest`, `forallQueries_hwHeads_prefixR`). Hence `hwHeadPre = 0`
(`hwHeadPre_eq_zero_all`).

* **Honest heads of the hardwired cells** (`HonAt`, `HonHw`, `hwHeadsHonest_of_honHw`): every
  hardwired `h` cell heads a non-message head-tail of the hardwired `k`, `k'` cells alone; the union
  extends them. A program port inside `tableHw L` never overwrites a hardwired cell with another
  value, so it keeps the earlier heads (`extends_progUpdate`, `honHw_progUpdate`).
* **The `h` port of a round** (`honAt_roundH`): with the slot's `k`, `k'` cells of rounds `0, …, j`
  hardwired, ProgView's `isHeadTail_roundH` gives the head-tail of the first `j + 1` blocks, whose
  slot is the slot or `.seed` (ProgSafe's `slotOf_cons_take`), neither a message slot.
* **The batch order** (`OkH`, `HH`): ProgSafe's `HB` with the port condition "programs a cell of
  `tableHw L`, and an `h` port's cell heads an honest tail of the hardwired cells given the earlier
  ports". Per component: `hh_rounds`, `hh_slotPorts`, `hh_signLayerT`, `hh_signT`,
  `hh_challengeT`, `hh_prefixT`; `forallQueries_of_hh` turns `HH` into the presented invariant along
  the realized prefix, the support staying on `SH` (inside `tableHw L`, the ports `C` hardwired,
  honest heads).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w w₁

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## Honest heads of the hardwired cells -/

section heads

/-- **An honest head at `z`**: a head-tail of `D` ending at `z` at a slot other than a message
slot. -/
def HonAt (L : HonestTable) (D : Dbs X Z) (z : Z) : Prop :=
  ∃ t xi, IsHeadTail L.perm D t z xi ∧ ∀ l e, slotOf L.param t ≠ some (.msg l e)

theorem HonAt.mono {L : HonestTable} {D D' : Dbs X Z} (hE : Extends D D') {z : Z}
    (h : HonAt L D' z) : HonAt L D z :=
  let ⟨t, xi, ht, hs⟩ := h
  ⟨t, xi, ht.mono hE, hs⟩

/-- **The hardwired `h` cells head honest tails of the hardwired `k`, `k'` cells.** -/
def HonHw (L : HonestTable) (W : Hw X Z) : Prop :=
  ∀ z, W.1 z ≠ none → HonAt L W.toDbs z

/-- The union extends the hardwired cells. -/
theorem extends_union (W : Hw X Z) (D : DbReg X Z) : Extends (union W D) W.toDbs :=
  ⟨fun x a h ↦ heldBy_union (e := .k x a) D h, fun x a h ↦ heldBy_union (e := .k' x a) D h⟩

theorem hwHeadsHonest_of_honHw {L : HonestTable} {s : HwReg X Z Mem} (h : HonHw L s.2.1) :
    HwHeadsHonest L s :=
  fun z hz ↦ (h z hz).mono (extends_union s.2.1 s.1)

section gen

variable {X₁ Z₁ : Type} [DecidableEq X₁] [DecidableEq Z₁]

/-- **A program port inside a table never overwrites a hardwired cell with another value**: the
hardwired cells after it extend those before. -/
theorem extends_progUpdate {T W : Hw X₁ Z₁} (hle : Quantum.Sponge.HwLe W T) {c : HwProg X₁ Z₁}
    (hc : ProgOf T c) : Extends (progUpdate c W).toDbs W.toDbs := by
  cases c with
  | programH z a => exact ⟨fun _ _ h ↦ h, fun _ _ h ↦ h⟩
  | programK x a =>
    refine ⟨fun y b h ↦ ?_, fun _ _ h ↦ h⟩
    change W.2.1 y = some b at h
    change Function.update W.2.1 x (some a) y = some b
    by_cases hy : y = x
    · subst hy
      rw [Function.update_self]
      have hc' : T.2.1 y = some a := hc
      rw [← hc', hle.2.1 y b h]
    · rw [Function.update_of_ne hy]
      exact h
  | programK' x a =>
    refine ⟨fun _ _ h ↦ h, fun y b h ↦ ?_⟩
    change W.2.2 y = some b at h
    change Function.update W.2.2 x (some a) y = some b
    by_cases hy : y = x
    · subst hy
      rw [Function.update_self]
      have hc' : T.2.2 y = some a := hc
      rw [← hc', hle.2.2 y b h]
    · rw [Function.update_of_ne hy]
      exact h

/-- Programming an `h` cell keeps the other `h` cells. -/
theorem progUpdate_fst_of_ne {W : Hw X₁ Z₁} {z z' : Z₁} (a : X₁) (h : z' ≠ z) :
    (progUpdate (.programH z a) W).1 z' = W.1 z' := by
  change Function.update W.1 z (some a) z' = W.1 z'
  rw [Function.update_of_ne h]

omit [DecidableEq X₁] [DecidableEq Z₁] in
/-- No hardwired cell inside the empty cells: inside every table. -/
theorem hwLe_of_le_hwEmpty {W T : Hw X₁ Z₁} (h : Quantum.Sponge.HwLe W (hwEmpty X₁ Z₁)) :
    Quantum.Sponge.HwLe W T :=
  ⟨fun z v hv ↦ (Option.some_ne_none v (h.1 z v hv).symm).elim,
    fun x v hv ↦ (Option.some_ne_none v (h.2.1 x v hv).symm).elim,
    fun x v hv ↦ (Option.some_ne_none v (h.2.2 x v hv).symm).elim⟩

omit [DecidableEq X₁] [DecidableEq Z₁] in
theorem fst_eq_none_of_le_hwEmpty {W : Hw X₁ Z₁} (h : Quantum.Sponge.HwLe W (hwEmpty X₁ Z₁))
    (z : Z₁) : W.1 z = none :=
  Option.eq_none_iff_forall_ne_some.2 fun v hv ↦ Option.some_ne_none v (h.1 z v hv).symm

end gen

/-- The condition of a program port at the hardwired cells `W`: an `h` port's cell heads an
honest tail of `W`. -/
def HeadOk (L : HonestTable) : HwProg X Z → Hw X Z → Prop
  | .programH z _, W => HonAt L W.toDbs z
  | _, _ => True

/-- **A program port keeps the honest heads**, inside a table it programs, if an `h` port's cell
heads an honest tail. -/
theorem honHw_progUpdate {L : HonestTable} {T W : Hw X Z} (hle : Quantum.Sponge.HwLe W T)
    {c : HwProg X Z} (hc : ProgOf T c) (hW : HonHw L W) (hh : HeadOk L c W) :
    HonHw L (progUpdate c W) := by
  have hE := extends_progUpdate hle hc
  cases c with
  | programH z a =>
    intro z' hz'
    by_cases h : z' = z
    · subst h
      exact HonAt.mono hE hh
    · rw [progUpdate_fst_of_ne a h] at hz'
      exact (hW z' hz').mono hE
  | programK x a => exact fun z hz ↦ (hW z hz).mono hE
  | programK' x a => exact fun z hz ↦ (hW z hz).mono hE

/-- **The `h` cell of round `j` of a slot heads an honest tail** of hardwired cells inside
`tableHw L` holding the slot's `k`, `k'` cells of rounds `0, …, j` (at values `f` agreeing with the
table on the slot's coordinates). -/
theorem honAt_roundH (L : HonestTable) {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot}
    (he : e.val < keyCount l) (hs : s ∈ layerSlots l e x) {f : ValPos → Digest}
    (hf : ∀ q ∈ slotNeed s, f q = valuePos L q) {j : ℕ} (hj : j < nBlocks (pubOf L) s)
    {W : Hw X Z} (hle : Quantum.Sponge.HwLe W (tableHw L))
    (hK : ∀ i ≤ j, W.2.1 (roundK (pubOf L) s f i).1 ≠ none)
    (hK' : ∀ i ≤ j, W.2.2 (roundK' (pubOf L) s f i).1 ≠ none) :
    HonAt L W.toDbs (roundH (pubOf L) s f j).1 := by
  have hInT : InTable s := inTable_of_layerSlots he hs
  have hinput : L.honestInput s = some (slotInput (pubOf L) s f) := by
    rw [HonestTable.honestInput, ite_eq_left hInT, slotInput, slotPayload_eq L hs hf]
    rfl
  have hlen : (blocks (slotInput (pubOf L) s f)).length = nBlocks (pubOf L) s :=
    blocks_slotInput_length (pubOf L) s f
  have ht : L.honestTail s = some (absorbTail (spongePerm (pubOf L).keys (pubOf L).perm)
      (blocks (slotInput (pubOf L) s f))) := by
    rw [HonestTable.honestTail, hinput]
    rfl
  have hAg : AgreesRounds L.perm L.keys.1 L.keys.2.1 L.keys.2.2 W.toDbs
      ((blocks (slotInput (pubOf L) s f)).take (j + 1)) :=
    agreesRounds_take_succ L.perm L.keys.1 L.keys.2.1 L.keys.2.2 fun i hi ↦
      ⟨heldBy_k_of_le hle (hK i hi), heldBy_k'_of_le hle (hK' i hi)⟩
  refine ⟨_, _, isHeadTail_roundH (pubOf L) s f (D := W.toDbs) (by rw [hlen]; exact hj) hAg, ?_⟩
  obtain ⟨x₀, rest, hft⟩ : ∃ x₀ rest, absorbTail (spongePerm (pubOf L).keys (pubOf L).perm)
      (blocks (slotInput (pubOf L) s f)) = x₀ :: rest := by
    refine List.exists_cons_of_ne_nil fun h0 ↦ ?_
    have h1 := congrArg List.length h0
    rw [length_absorbTail, hlen, List.length_nil] at h1
    omega
  have ht0 : absorbTail (spongePerm (pubOf L).keys (pubOf L).perm)
      ((blocks (slotInput (pubOf L) s f)).take (j + 1)) = x₀ :: rest.take j := by
    rw [absorbTail_take, hft, List.take_succ_cons]
  have hslot := L.slotOf_honestTail ht
  rw [hft] at hslot
  have hsl : slotOf L.param (x₀ :: rest.take j) = some s ∨
      slotOf L.param (x₀ :: rest.take j) = some .seed := by
    rcases eq_or_ne rest [] with rfl | hne
    · rw [List.take_nil]
      exact Or.inl hslot
    · exact slotOf_cons_take hne hslot j
  intro l' e' h
  rw [ht0] at h
  rcases hsl with h1 | h1
  · rw [h1] at h
    obtain rfl := Option.some_inj.mp h
    exact hInT
  · rw [h1] at h
    exact Slot.noConfusion (Option.some_inj.mp h)

end heads

/-! ## Templates whose program ports keep the honest heads in batch order -/

section hh

variable (L : HonestTable) {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- **A program port keeping the honest heads given the hardwired ports `C`**: it programs a cell
of `tableHw L` with its value, and an `h` port's cell heads an honest tail at the hardwired cells
inside `tableHw L` with the cells of `C` hardwired. -/
def OkH (C : Set (HwProg X Z)) (c : HwProg X Z) : Prop :=
  ProgOf (tableHw L) c ∧
    ∀ W : Hw X Z, AllHw C W → Quantum.Sponge.HwLe W (tableHw L) → HeadOk L c W

variable {L} in
theorem OkH.anti {C D : Set (HwProg X Z)} {c : HwProg X Z} (h : OkH L D c) (hD : D ⊆ C) :
    OkH L C c :=
  ⟨h.1, fun W hC hle ↦ h.2 W (fun c' hc' ↦ hC c' (hD hc')) hle⟩

/-- The condition on a port before a call: a program port keeps the honest heads given `C`. -/
def portOkH : (XSpec Selections).Port → Set (HwProg X Z) → Prop
  | .inl (.inr p), C => OkH L C (p.1.realize (valueAt L))
  | _, _ => True

/-- The condition before a command. -/
def cmdOkH {A : QReg} : QuantumComp.Cmd Λ (XSpec Selections) A → Set (HwProg X Z) → Prop
  | .prim _, _ => True
  | .query i _ _, C => portOkH L i C

/-- **A template whose program ports keep the honest heads in batch order**, run from the
hardwired ports `C`, ending with the hardwired ports `C'` (ProgSafe's `HB` with `OkH`). -/
def HH : {A : QReg} → IFreeM (QuantumComp.toIPFunctor Λ (XSpec Selections)) Ω A →
    Set (HwProg X Z) → Set (HwProg X Z) → Prop
  | _, .pure _, C, C' => C' ⊆ C
  | _, .liftBind c next, C, C' => cmdOkH L c C ∧ ∀ b, HH (next b) (cmdNext L c C) C'

theorem cmdOkH_anti {A : QReg} (c : QuantumComp.Cmd Λ (XSpec Selections) A)
    {C D : Set (HwProg X Z)} (hD : D ⊆ C) (h : cmdOkH L c D) : cmdOkH L c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · trivial
  · trivial
  · trivial
  · exact OkH.anti h hD
  · trivial

theorem hh_mono {A : QReg} (y : IFreeM (QuantumComp.toIPFunctor Λ (XSpec Selections)) Ω A)
    {C C' D D' : Set (HwProg X Z)} (hy : HH L y C C') (hD : C ⊆ D) (hD' : D' ⊆ C') :
    HH L y D D' := by
  induction y using IFreeM.inductionOn generalizing C D with
  | pure _ _ => exact hD'.trans (hy.trans hD)
  | liftBind _ c next ih =>
    exact ⟨cmdOkH_anti L c hD hy.1, fun b ↦ ih b (hy.2 b) (cmdNext_mono L c hD)⟩

theorem hh_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor Λ (XSpec Selections)) Ω A) (C C' : Set (HwProg X Z)) :
    HH L (e ▸ y) C C' ↔ HH L y C C' := by
  subst e
  rfl

theorem hh_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor Λ (XSpec Selections)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor Λ (XSpec Selections)) Y u)
    {C D C' : Set (HwProg X Z)} (hx : HH L x C D) (hg : ∀ u a, HH L (g u a) D C') :
    HH L (x.bind g) C C' := by
  induction x using IFreeM.inductionOn generalizing C with
  | pure _ a => exact hh_mono L _ (hg _ a) hx subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem hh₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ Λ (XSpec Selections) A B α)
    (g : α → QuantumComp₂ Λ (XSpec Selections) B B' β)
    {C D C' : Set (HwProg X Z)} (hx : HH L x C D) (hg : ∀ a, HH L (g a) D C') :
    HH L (x.bind g) C C' := by
  refine hh_bind L x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

/-- Substituting trees whose program ports keep the honest heads from nothing hardwired. -/
theorem hh_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor Λ spec)
      (QuantumComp.toIPFunctor Λ (XSpec Selections)))
    (hσ : ∀ A c, HH L (σ A c) ∅ ∅) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor Λ spec) Ω A) : HH L (x.substitute σ) ∅ ∅ := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact hh_bind L _ _ (hσ s c) fun u ans ↦ (hh_cast L ans.2 _ _ _).mpr (ih ans.1)

/-- Runtime 1's programs call no program port. -/
theorem hh_readLift {A : QReg} (y : QuantumComp Λ (hwReadSpec X Z Selections) Ω A)
    (C : Set (HwProg X Z)) : HH L (readLift goodAll y) C C := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind _ c next ih =>
    show HH L (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next)) C C
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

theorem hh_act {A B : QReg} {α : Type} (p : SubInstrument A B α) (C : Set (HwProg X Z)) :
    HH L (QComp.act (spec := XSpec Selections) p) C C :=
  ⟨trivial, fun _ ↦ subset_rfl⟩

theorem hh_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × Selections) → QComp (XSpec Selections) B B' α)
    {C C' : Set (HwProg X Z)} (hk : ∀ r, HH L (k r) C C') :
    HH L (revealThen goodAll T k) C C' :=
  ⟨trivial, fun r ↦ hh₂_bind L _ _ (hh_act L _ _) fun _ ↦ hk r.down⟩

theorem hh_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec Selections) B B' α) {C C' : Set (HwProg X Z)}
    (hok : OkH L C (p.realize (valueAt L))) (hk : HH L k (insert (p.realize (valueAt L)) C) C') :
    HH L (progThen p hp k) C C' :=
  ⟨hok, fun _ ↦ hh₂_bind L _ _ (hh_act L _ _) fun _ ↦ hk⟩

theorem rPortK_mem_slotPorts (pub : Pub) (s : Slot) {j : ℕ} (hj : j < nBlocks pub s) :
    rPortK pub s j ∈ slotPorts pub s :=
  List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_cons_self⟩

theorem rPortK'_mem_slotPorts (pub : Pub) (s : Slot) {j : ℕ} (hj : j < nBlocks pub s) :
    rPortK' pub s j ∈ slotPorts pub s :=
  List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_cons_of_mem _ List.mem_cons_self⟩

/-- **The `h` port of a round keeps the honest heads after the earlier rounds and its `k`, `k'`
ports.** -/
theorem okH_portH {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot}
    (he : e.val < keyCount l) (hs : s ∈ layerSlots l e x) {j : ℕ}
    (hj : j < nBlocks (pubOf L) s) :
    OkH L (insert ((rPortK' (pubOf L) s j).realize (valueAt L))
      (insert ((rPortK (pubOf L) s j).realize (valueAt L)) (doneTo L s j)))
      ((rPortH (pubOf L) s j).realize (valueAt L)) :=
  ⟨progsOf_tableHw L l e x he s hs _ (rPortH_mem_slotPorts (pubOf L) s hj), fun W hC hle ↦
    honAt_roundH L he hs (fun q hq ↦ extendVals_restrictTo (inl_mem_inlSet.mpr hq) (valueAt L))
      hj hle
      (fun i hi ↦ by
        rcases hi.lt_or_eq with hi | rfl
        · exact hC ((rPortK (pubOf L) s i).realize (valueAt L))
            (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, hi, Or.inl rfl⟩))
        · exact hC ((rPortK (pubOf L) s i).realize (valueAt L))
            (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      (fun i hi ↦ by
        rcases hi.lt_or_eq with hi | rfl
        · exact hC ((rPortK' (pubOf L) s i).realize (valueAt L))
            (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, hi, Or.inr (Or.inl rfl)⟩))
        · exact hC ((rPortK' (pubOf L) s i).realize (valueAt L)) (Set.mem_insert _ _))⟩

/-- **The rounds `a, …, a + m - 1` of a slot**, in order, from the earlier rounds hardwired. -/
theorem hh_rounds (B : QReg) {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot}
    (he : e.val < keyCount l) (hs : s ∈ layerSlots l e x) :
    ∀ m a, a + m = nBlocks (pubOf L) s → ∀ C, doneTo L s a ⊆ C →
      HH L (progPorts Selections B ((List.range' a m).flatMap fun j ↦
        [rPortK (pubOf L) s j, rPortK' (pubOf L) s j, rPortH (pubOf L) s j])) C ∅
  | 0, _, _, C, _ => Set.empty_subset C
  | m + 1, a, hm, C, hC => by
    rw [List.range'_succ, List.flatMap_cons]
    refine hh_progThen L (rPortK (pubOf L) s a) trivial _
      ⟨progsOf_tableHw L l e x he s hs _ (rPortK_mem_slotPorts (pubOf L) s (j := a) (by omega)),
        fun _ _ _ ↦ trivial⟩
      (hh_progThen L (rPortK' (pubOf L) s a) trivial _
        ⟨progsOf_tableHw L l e x he s hs _ (rPortK'_mem_slotPorts (pubOf L) s (j := a) (by omega)),
          fun _ _ _ ↦ trivial⟩
        (hh_progThen L (rPortH (pubOf L) s a) trivial _
          ((okH_portH L he hs (j := a) (by omega)).anti ?_)
          (hh_rounds B he hs m (a + 1) (by omega) _ ?_)))
    · exact Set.insert_subset_insert (Set.insert_subset_insert hC)
    · rintro c ⟨i, hi, hc⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (hC ⟨i, hi, hc⟩)))
      · rcases hc with rfl | rfl | rfl
        · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
        · exact Set.mem_insert _ _

/-- **The ports of a slot of an in-table key's layer signature, in `slotPorts` order.** -/
theorem hh_slotPorts (B : QReg) {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot}
    (he : e.val < keyCount l) (hs : s ∈ layerSlots l e x) (C : Set (HwProg X Z)) :
    HH L (progPorts Selections B (slotPorts (pubOf L) s)) C ∅ := by
  rw [slotPorts_eq_flatMap]
  refine hh_rounds L B he hs _ 0 (zero_add _) C ?_
  rintro c ⟨i, hi, -⟩
  exact absurd hi (Nat.not_lt_zero i)

theorem hh_progSlots (B : QReg) (ss : List Slot)
    (h : ∀ s ∈ ss, ∀ C, HH L (progPorts Selections B (slotPorts (pubOf L) s)) C ∅)
    (C : Set (HwProg X Z)) : HH L (progSlots Selections (pubOf L) B ss) C ∅ := by
  induction ss generalizing C with
  | nil => exact Set.empty_subset C
  | cons s ss ih =>
    exact hh₂_bind L _ _ (h s List.mem_cons_self C) fun _ ↦
      ih (fun s' hs' ↦ h s' (List.mem_cons_of_mem _ hs')) ∅

variable (upd : TrialUpd Selections)

/-- **A layer signature of an in-table key**: the randomizer search reads, then the slots it makes
public are programmed slot by slot. -/
theorem hh_signLayerT (B : QReg) (lab : RLabel) (he : lab.key.val < keyCount lab.layer) :
    HH L (signLayerT Selections upd (pubOf L) B lab) ∅ ∅ := by
  refine hh_revealThen L _ _ fun _ ↦ hh₂_bind L _ _ (hh_readLift L _ ∅) fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · exact subset_rfl
  · exact hh_revealThen L _ _ fun _ ↦ hh₂_bind L _ _
      (hh_progSlots L B _ (fun s hs C ↦ hh_slotPorts L B he hs C) ∅) fun _ ↦ subset_rfl

theorem hh_signT (B : QReg) (r : SigningRequest) :
    HH L (signT Selections upd (pubOf L) B r) ∅ ∅ := by
  refine hh₂_bind L _ _ (hh_signLayerT L upd B (botLabel r)
    (keyIndexOnLayer_lt r.leafIndex bottomLayer)) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · exact subset_rfl
  · refine hh₂_bind L _ _ (hh_signLayerT L upd B (topLabel r _)
      (keyIndexOnLayer_lt r.leafIndex topLayer)) fun t ↦ ?_
    rcases t with _ | ⟨top, _⟩ <;> exact subset_rfl

theorem hh_challengeT (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    HH L (challengeT Selections upd (pubOf L) A c) ∅ ∅ := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact hh_readLift L _ ∅
  · exact hh_readLift L _ ∅
  · exact hh_bind L _ _ (hh₂_bind L _ _ (hh_act L _ _) fun _ ↦ hh_signT L upd _ r)
      fun _ _ ↦ subset_rfl

/-- **The challenge prefix's program ports keep the honest heads in batch order.** -/
theorem hh_prefixT (A : Adversary (X × Z)) : HH L (prefixT Selections upd (pubOf L) A) ∅ ∅ :=
  hh_revealThen L _ _ fun _ ↦
    hh₂_bind L _ _ (hh_substitute L _ (hh_challengeT L upd) _) fun _ ↦ subset_rfl

end hh

/-! ## The steps on the hardwired cells -/

section steps

variable {M : Type} [Fintype M] [DecidableEq M]

/-- A step of `runtimeR` at port `i` carries support on the states whose hardwired cells satisfy
`P` to support on those satisfying `P'`. -/
def StepW (m₀ : Finset HPos × M) (i : (recHwSpec X Z HPos M).Port) (P P' : Hw X Z → Prop) :
    Prop :=
  ∀ r σ, QuerySupportedOn (fun m : (recHwSpec X Z HPos M).In i × (runtimeR m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | P s.2.1} σ →
    QuerySupportedOn (fun m : (recHwSpec X Z HPos M).Out i × (runtimeR m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | P' s.2.1} (((runtimeR m₀).step i).branch r σ)

theorem stepW_sponge (m₀ : Finset HPos × M) (i : SpongePort) (P : Hw X Z → Prop) :
    StepW m₀ (.inl (.inl (.inl i))) P P := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m₀ i r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m₀ i q.1 q'.1 q.2 q'.2 hK
    show P q'.2.2.1
    rw [congrArg Prod.fst he]
    exact hq

theorem stepW_read (m₀ : Finset HPos × M)
    (c : {c : HwRead X Z (Finset HPos × M) // ReadMono (memLab X Z HPos M) c})
    (P : Hw X Z → Prop) : StepW m₀ (.inl (.inl (.inr c.1))) P P := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c.1 r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    show P q'.2.2.1
    rw [hwReadKraus_ne_zero_hw c.1 r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK]
    exact hq

theorem stepW_prog (m₀ : Finset HPos × M) (c : HwProg X Z) {P P' : Hw X Z → Prop}
    (h : ∀ W, P W → P' (progUpdate c W)) : StepW m₀ (.inl (.inr c)) P P' := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    show P' q'.2.2.1
    rw [hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK]
    exact h _ hq

theorem stepW_rec (m₀ : Finset HPos × M) (T : Finset HPos) (P : Hw X Z → Prop) :
    StepW m₀ (.inr T) P P := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    show P q'.2.2.1
    rw [recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK]
    exact hq

end steps

/-! ## The presented operators -/

section present

variable (L : HonestTable) {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- **The hardwired cells along the prefix**: inside `tableHw L`, with the ports `C` hardwired,
heading honest tails. -/
def SH (C : Set (HwProg X Z)) (W : Hw X Z) : Prop :=
  Quantum.Sponge.HwLe W (tableHw L) ∧ AllHw C W ∧ HonHw L W

/-- A program port keeping the honest heads moves `SH` at `C` to `SH` at `insert c C`. -/
theorem sH_progUpdate {C : Set (HwProg X Z)} {c : HwProg X Z} (hc : OkH L C c) {W : Hw X Z}
    (hW : SH L C W) : SH L (insert c C) (progUpdate c W) :=
  ⟨hwLe_progUpdate hW.1 hc.1, allHw_progUpdate hW.2.1 c,
    honHw_progUpdate hW.1 hc.1 hW.2.2 (hc.2 W hW.2.1 hW.1)⟩

/-- One call of a realized program, from `SH` at `C` to `SH` at `C'`. -/
theorem forallQueries_queryBind_of_stepW (I : Λ.Interp) {A : QReg}
    (i : (recHwSpec X Z HPos Selections).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z HPos Selections).In i × E)
    (k' : (recHwSpec X Z HPos Selections).Result i → QuantumComp Λ
      (recHwSpec X Z HPos Selections) Ω (QReg.of ((recHwSpec X Z HPos Selections).Out i × E)))
    {C C' : Set (HwProg X Z)} (hstep : StepW m0R i (SH L C) (SH L C'))
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of ((recHwSpec X Z HPos Selections).Out i × E) ×
        (runtimeR m0R).D ↦ m.2) {s : HwReg X Z Mem | SH L C' s.2.1} ρ' →
      (runtimeR m0R).ForallQueries I
        (invSupp (runtimeR m0R) (fun _ ↦ True) (HwHeadsHonest L)) (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m0R).D) (A × (runtimeR m0R).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m0R).D ↦ m.2)
      {s : HwReg X Z Mem | SH L C s.2.1} ρ) :
    (runtimeR m0R).ForallQueries I (invSupp (runtimeR m0R) (fun _ ↦ True) (HwHeadsHonest L))
      (QuantumComp.queryBind i E ℓ k') ρ :=
  ⟨fun _ a ha ↦ relabel_diag_eq_zero_of_supp m0R E ℓ hρ a fun hS ↦
      ha (hwHeadsHonest_of_honHw hS.2.2), fun r ↦
    hk r _ (Hybrid.querySupportedOn_queryStep (runtimeR m0R) (fun s ↦ s) i r (hstep r) E ℓ hρ)⟩

/-- **The realized program of a template whose program ports keep the honest heads in batch order
presents only states whose hardwired `h` cells head honest tails.** -/
theorem forallQueries_of_hh (I : Λ.Interp) {A : QReg} (y : QuantumComp Λ (XSpec Selections) Ω A) :
    ∀ C C', HH L y C C' → ∀ ρ : Matrix (A × (runtimeR m0R).D) (A × (runtimeR m0R).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m0R).D ↦ m.2)
        {s : HwReg X Z Mem | SH L C s.2.1} ρ →
      (runtimeR m0R).ForallQueries I (invSupp (runtimeR m0R) (fun _ ↦ True) (HwHeadsHonest L))
        (realizeT (valueAt L) y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro C C' hy ρ hρ b
    exact ih b C C' (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepW L I (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT (valueAt L) (k r)) (stepW_sponge m0R i _)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepW L I (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT (valueAt L) (k r)) (stepW_read m0R c _)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepW L I
          (.inl (.inr ((LazyProg.programH T₀ c).realize (valueAt L)))) E ℓ
          (fun r ↦ realizeT (valueAt L) (k r)) (stepW_prog m0R _ fun _ ↦ sH_progUpdate L hy.1)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepW L I
          (.inl (.inr ((LazyProg.programK T₀ c).realize (valueAt L)))) E ℓ
          (fun r ↦ realizeT (valueAt L) (k r)) (stepW_prog m0R _ fun _ ↦ sH_progUpdate L hy.1)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepW L I
          (.inl (.inr ((LazyProg.programK' T₀ c).realize (valueAt L)))) E ℓ
          (fun r ↦ realizeT (valueAt L) (k r)) (stepW_prog m0R _ fun _ ↦ sH_progUpdate L hy.1)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepW L I (.inr T) E ℓ
        (fun m ↦ realizeT (valueAt L) (k (restrictTo T (valueAt L), m))) (stepW_rec m0R T _)
        (fun m ↦ ih (restrictTo T (valueAt L), m) _ C'
          (hy.2 (ULift.up (restrictTo T (valueAt L), m)))) ρ hρ

/-- The initial state has no hardwired cell: it is on `SH` with nothing hardwired. -/
theorem querySupportedOn_initR_sH :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2)
      {s : HwReg X Z Mem | SH L ∅ s.2.1} initR := by
  refine (querySupportedOn_initR_hw (hwEmpty X Z)).mono fun s hs ↦ ?_
  exact ⟨hwLe_of_le_hwEmpty hs, fun c hc ↦ absurd hc (Set.notMem_empty c),
    fun z hz ↦ absurd (fst_eq_none_of_le_hwEmpty hs z) hz⟩

/-- **EncRefined's honest-heads invariant**: along the challenge prefix at any table, every call is
presented only states whose hardwired `h` cells head honest (non-message) head-tails. -/
theorem forallQueries_hwHeads_prefixR (A : Adversary (X × Z)) :
    (runtimeR m0R).ForallQueries .instruments
      (invSupp (runtimeR m0R) (fun _ ↦ True) (HwHeadsHonest L)) (prefixR A L) initR :=
  forallQueries_of_hh L .instruments _ ∅ ∅ (hh_prefixT L cwUpd A) initR
    (querySupportedOn_initR_sH L)

end present

/-- **The hardwired trial heads vanish along the prefix**, at every table. -/
theorem hwHeadPre_eq_zero_all {q : ℕ} {A : Adversary (X × Z)}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (L : HonestTable) : hwHeadPre A L = 0 :=
  hwHeadPre_eq_zero hperm hsign L (forallQueries_hwHeads_prefixR L A)

end Quantum.Xmss.Assembly

end
