module

public import Quantum.Xmss.Assembly.MassesR0
public import Quantum.Xmss.Assembly.FullTable

@[expose] public section

/-!
# The template game at the reparametrized public datum

MassesR0's `hgame` (`uavg_totalWeight_portMass_le_xmssR0`): on the good set, the realized template
game at the table's public datum `pubOf L` is the game at the reparametrized public datum
(Reparam's `xPub w h''`, `h''` the public `h` of `fwd`), realized at hidden values that are
Reparam's on the positions and the table's randomizer bases on the labels.

* **Congruence** (`realizeT_gameT_congr`): `gameT M upd pub A` reads `pub.keys` only through the
  program ports of the slots it makes public (`slotPorts`). Realized at `v` and `v'`, the games at
  `pub` and `pub'` are equal when the parameters and the permutations are, `v` and `v'` agree on
  every coordinate the game may reveal (the root, the labels, `layerNeed` of in-range keys), and
  the slot ports agree (`SlotPortsAgree`: the `k`, `k'` and `h` cells and values of every round, at
  the values `v` on the slot's coordinates) for every slot a layer signature by an in-range key
  makes public. Combinators: `realizeT_revealThen_congr`, `realizeT_progThen_eq`,
  `realizeT_readLift_indep` (reads never see the hidden values), `realizeT_bind₂_congr`.
* **The reparametrized datum** (`realizeT_gameT_pubOf`): over Reparam's table `θ` of the table `L`
  with `hsub_core`'s hypotheses (`XGood`, `θ.2 = wOf L`, the chain starts in the pad, `θ`'s `h`
  agreeing with `L`'s at the honest paths' `h`-cells), the slot ports agree
  (`slotPortsAgree_pubOf`, from `cells_transfer`, `rounds_fwd`, `roundH_table` and `roundH_snd`),
  and the positions the game reveals are in the table or chain starts (`layerNeed_good`), where
  Reparam's values are the table's (`xVal_eq_valuePos`).
* **`hgame`** (`hgame_xmssR0`): in the exact shape of `uavg_totalWeight_portMass_le_xmssR0`, with
  the hidden values `e`'s on the positions and the table's on the labels; they agree with `e`'s
  off the non-first labels when `e`'s randomizer bases are the table's there.
-/

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma HashSig.OverPermutation

/-! ## Realizing the combinators -/

section comb

variable {M : Type}

theorem realizeT_bind₂_congr {A B C : QReg} {α β : Type} {v v' : HPos → Digest}
    {x x' : QComp (XSpec M) A B α} {k k' : α → QComp (XSpec M) B C β}
    (hx : realizeT v x = realizeT v' x') (hk : ∀ a, realizeT v (k a) = realizeT v' (k' a)) :
    realizeT v (x.bind k) = realizeT v' (x'.bind k') := by
  rw [realizeT_bind₂, realizeT_bind₂, hx]
  exact congrArg (QuantumComp₂.bind (realizeT v' x')) (funext hk)

theorem realizeT_bind_congr {Ω Ω' : QReg → Type} {A : QReg} {v v' : HPos → Digest}
    {x x' : QuantumComp LocalSig.instruments.{0} (XSpec M) Ω A}
    {g g' : ∀ u, Ω u → QuantumComp LocalSig.instruments.{0} (XSpec M) Ω' u}
    (hx : realizeT v x = realizeT v' x') (hg : ∀ u a, realizeT v (g u a) = realizeT v' (g' u a)) :
    realizeT v (x.bind g) = realizeT v' (x'.bind g') := by
  rw [realizeT_bind, realizeT_bind, hx]
  simp only [hg]

/-- A reveal, realized: the record port of `T`, continuing with the values of `v` on `T`. -/
theorem realizeT_revealThen_eq (v : HPos → Digest) {B C : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B C α) :
    realizeT v (revealThen goodAll T k) =
      QuantumComp.queryBind (L := LocalSig.instruments.{0}) (spec := recHwSpec X Z HPos M) (.inr T)
        B (Equiv.uniqueProd B Unit).symm fun r ↦
          QuantumComp.primBind (L := LocalSig.instruments.{0})
            ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦
              realizeT v (k (restrictTo T v, r)) :=
  rfl

/-- **Reveals at values agreeing on the revealed coordinates** realize alike. -/
theorem realizeT_revealThen_congr {B C : QReg} {α : Type} {v v' : HPos → Digest} (T : Finset HPos)
    (hT : Agree T v v') {k k' : RevealVals XD T × (Finset HPos × M) → QComp (XSpec M) B C α}
    (hk : ∀ r, realizeT v (k r) = realizeT v' (k' r)) :
    realizeT v (revealThen goodAll T k) = realizeT v' (revealThen goodAll T k') := by
  rw [realizeT_revealThen_eq, realizeT_revealThen_eq, ← restrictTo_eq hT]
  simp only [hk]

/-- A realized program port `c` beside `B`, then `K`. -/
noncomputable def progR (B : QReg) {C : QReg} {α : Type} (c : HwProg X Z)
    (K : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos M) (QuantumComp₂.Leaf C α) B) :
    QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos M) (QuantumComp₂.Leaf C α) B :=
  QuantumComp.queryBind (L := LocalSig.instruments.{0}) (spec := recHwSpec X Z HPos M)
    (.inl (.inr c)) B (Equiv.uniqueProd B Unit).symm fun _ ↦
      QuantumComp.primBind (L := LocalSig.instruments.{0})
        ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ K

/-- A program port, realized: the program port it realizes at `v`. -/
theorem realizeT_progThen_eq (v : HPos → Digest) {B C : QReg} {α : Type}
    (p : LazyProg X Z HPos XD) (k : QComp (XSpec M) B C α) :
    realizeT v (progThen p trivial k) = progR B (p.realize v) (realizeT v k) :=
  rfl

/-- **Reads never see the hidden values**: a lifted read program realizes alike at all values. -/
theorem realizeT_readLift_indep (v v' : HPos → Digest) {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (hwReadSpec X Z M) Ω A) :
    realizeT v (readLift goodAll y) = realizeT v' (readLift goodAll y) := by
  show IPFunctor.IFreeM.mapLens (tmplLens v) (IPFunctor.IFreeM.mapLens (readLens goodAll) y) =
    IPFunctor.IFreeM.mapLens (tmplLens v') (IPFunctor.IFreeM.mapLens (readLens goodAll) y)
  rw [← IPFunctor.IFreeM.substitute_toSubstitution (readLens goodAll) y,
    ← IPFunctor.IFreeM.substitute_toSubstitution (tmplLens v),
    ← IPFunctor.IFreeM.substitute_toSubstitution (tmplLens v')]
  refine ((substitute_substitute _ _ y).trans ?_).trans (substitute_substitute _ _ y).symm
  refine congrArg (fun σ ↦ IPFunctor.IFreeM.substitute σ y) (funext fun A ↦ funext fun c ↦ ?_)
  rcases c with o | ⟨i | c, E, ℓ⟩ <;> rfl

theorem realizeT_progPorts_congr {v v' : HPos → Digest} (B : QReg) :
    ∀ {ps ps' : List (LazyProg X Z HPos XD)},
      ps.map (LazyProg.realize v) = ps'.map (LazyProg.realize v') →
        realizeT v (progPorts M B ps) = realizeT v' (progPorts M B ps')
  | [], [], _ => rfl
  | [], _ :: _, h => (List.cons_ne_nil _ _ h.symm).elim
  | _ :: _, [], h => (List.cons_ne_nil _ _ h).elim
  | p :: ps, p' :: ps', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [progPorts, progPorts, realizeT_progThen_eq, realizeT_progThen_eq,
      realizeT_progPorts_congr B h.2, h.1]

theorem realizeT_progSlots_congr {pub pub' : Pub} {v v' : HPos → Digest} (B : QReg) :
    ∀ ss : List Slot,
      (∀ s ∈ ss, (slotPorts pub s).map (LazyProg.realize v) =
        (slotPorts pub' s).map (LazyProg.realize v')) →
        realizeT v (progSlots M pub B ss) = realizeT v' (progSlots M pub' B ss)
  | [], _ => rfl
  | s :: ss, h => by
    rw [progSlots, progSlots]
    exact realizeT_bind₂_congr (realizeT_progPorts_congr B (h s List.mem_cons_self)) fun _ ↦
      realizeT_progSlots_congr B ss fun s' hs' ↦ h s' (List.mem_cons_of_mem _ hs')

end comb

/-! ## The slot ports -/

section slots

/-- **The slot ports of `pub` and `pub'` agree at the values `v`**: the `k`, `k'` and `h` cells
with their values of every round of slot `s`'s honest path, from the values `v` on the slot's
coordinates (as the realized ports read them). -/
def SlotPortsAgree (pub pub' : Pub) (v : HPos → Digest) (s : Slot) : Prop :=
  ∀ j < nBlocks pub s,
    roundK pub s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j =
        roundK pub' s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j ∧
      roundK' pub s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j =
        roundK' pub' s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j ∧
      roundH pub s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j =
        roundH pub' s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j

/-- The realized ports of a slot: the cells and values of its rounds. -/
theorem map_realize_slotPorts (pub : Pub) (s : Slot) (v : HPos → Digest) :
    (slotPorts pub s).map (LazyProg.realize v) =
      (List.range (nBlocks pub s)).flatMap fun j ↦
        [HwProg.programK (roundK pub s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j).1
            (roundK pub s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j).2,
          HwProg.programK' (roundK' pub s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j).1
            (roundK' pub s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j).2,
          HwProg.programH (roundH pub s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j).1
            (roundH pub s (extendVals (restrictTo (inlSet (slotNeed s)) v)) j).2] := by
  simp only [slotPorts, List.map_flatMap, List.map_cons, List.map_nil]
  rfl

theorem map_realize_slotPorts_eq {pub pub' : Pub} {v v' : HPos → Digest}
    (hP : pub.param = pub'.param) {s : Slot} (hag : Agree (inlSet (slotNeed s)) v v')
    (h : SlotPortsAgree pub pub' v s) :
    (slotPorts pub s).map (LazyProg.realize v) = (slotPorts pub' s).map (LazyProg.realize v') := by
  rw [map_realize_slotPorts, map_realize_slotPorts, ← nBlocks_eq_of_param hP,
    ← restrictTo_eq hag]
  refine List.flatMap_congr fun j hj ↦ ?_
  obtain ⟨e1, e2, e3⟩ := h j (List.mem_range.mp hj)
  rw [e1, e2, e3]

/-- An `h`-round reads the values only at the slot's coordinates (its output position among
them). -/
theorem roundH_congr_of_need (pub : Pub) {s : Slot} {f f' : ValPos → Digest}
    (hf : ∀ q ∈ slotNeed s, f q = f' q) (hout : slotOutPos s ∈ slotNeed s) (j : ℕ) :
    roundH pub s f j = roundH pub s f' j := by
  have hin : slotInput pub s f = slotInput pub s f' :=
    slotInput_congr' pub fun q hq ↦ hf q (isInput_mem_slotNeed hq)
  simp only [roundH, hin, hf _ hout]

end slots

/-! ## The congruence -/

section congr

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **A layer signature** at the public data `⟨P, π, t⟩`, `⟨P, π, t'⟩` and the values `v`, `v'`. -/
theorem realizeT_signLayerT_congr {P : PublicParameter} {π : Equiv.Perm (X × Z)}
    {t t' : SpongeKeys X Z} {v v' : HPos → Digest} (hlab : ∀ lab : RLabel, v (.inr lab) = v' (.inr lab))
    (hneed : ∀ (l : Layer) (e : KeyIndex) (x : Encoding), e.val < keyCount l →
      ∀ q ∈ layerNeed l e x, v (.inl q) = v' (.inl q))
    (hslot : ∀ (l : Layer) (e : KeyIndex) (x : Encoding) (s : Slot), e.val < keyCount l →
      s ∈ layerSlots l e x → SlotPortsAgree ⟨P, π, t⟩ ⟨P, π, t'⟩ v s)
    (B : QReg) (lab : RLabel) (he : lab.key.val < keyCount lab.layer) :
    realizeT v (signLayerT M upd ⟨P, π, t⟩ B lab) =
      realizeT v' (signLayerT M upd ⟨P, π, t'⟩ B lab) := by
  rw [signLayerT, signLayerT]
  refine realizeT_revealThen_congr _ (fun s hs ↦ by rw [Finset.mem_singleton.mp hs]; exact hlab lab)
    fun r₀ ↦ ?_
  rw [grindR_keys M upd P π t t']
  refine realizeT_bind₂_congr (realizeT_readLift_indep v v' _) fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · rfl
  · have hag : ∀ T ⊆ layerNeed lab.layer lab.key x, Agree (inlSet T) v v' := fun T hT s hs ↦ by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hs
      exact hneed _ _ _ he q (hT hq)
    refine realizeT_revealThen_congr _ (hag _ subset_rfl) fun r ↦ ?_
    refine realizeT_bind₂_congr (realizeT_progSlots_congr B _ fun s hs ↦ ?_) fun _ ↦ rfl
    refine map_realize_slotPorts_eq (pub := ⟨P, π, t⟩) (pub' := ⟨P, π, t'⟩) rfl
      (hag _ fun q hq ↦ ?_) (hslot _ _ _ s he hs)
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (slotNeed_subset_needUnion hs hq))

theorem realizeT_signT_congr {P : PublicParameter} {π : Equiv.Perm (X × Z)}
    {t t' : SpongeKeys X Z} {v v' : HPos → Digest} (hlab : ∀ lab : RLabel, v (.inr lab) = v' (.inr lab))
    (hneed : ∀ (l : Layer) (e : KeyIndex) (x : Encoding), e.val < keyCount l →
      ∀ q ∈ layerNeed l e x, v (.inl q) = v' (.inl q))
    (hslot : ∀ (l : Layer) (e : KeyIndex) (x : Encoding) (s : Slot), e.val < keyCount l →
      s ∈ layerSlots l e x → SlotPortsAgree ⟨P, π, t⟩ ⟨P, π, t'⟩ v s)
    (B : QReg) (r : SigningRequest) :
    realizeT v (signT M upd ⟨P, π, t⟩ B r) = realizeT v' (signT M upd ⟨P, π, t'⟩ B r) := by
  rw [signT, signT]
  refine realizeT_bind₂_congr (realizeT_signLayerT_congr upd hlab hneed hslot B _
    (keyIndexOnLayer_lt r.leafIndex bottomLayer)) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · rfl
  · exact realizeT_bind₂_congr (realizeT_signLayerT_congr upd hlab hneed hslot B _
      (keyIndexOnLayer_lt r.leafIndex topLayer)) fun b ↦ by rcases b with _ | ⟨top, _⟩ <;> rfl

theorem realizeT_challengeT_congr {P : PublicParameter} {π : Equiv.Perm (X × Z)}
    {t t' : SpongeKeys X Z} {v v' : HPos → Digest} (hlab : ∀ lab : RLabel, v (.inr lab) = v' (.inr lab))
    (hneed : ∀ (l : Layer) (e : KeyIndex) (x : Encoding), e.val < keyCount l →
      ∀ q ∈ layerNeed l e x, v (.inl q) = v' (.inl q))
    (hslot : ∀ (l : Layer) (e : KeyIndex) (x : Encoding) (s : Slot), e.val < keyCount l →
      s ∈ layerSlots l e x → SlotPortsAgree ⟨P, π, t⟩ ⟨P, π, t'⟩ v s)
    (A : QReg) (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z))).A A) :
    realizeT v (challengeT M upd ⟨P, π, t⟩ A c) = realizeT v' (challengeT M upd ⟨P, π, t'⟩ A c) := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact realizeT_readLift_indep v v' _
  · exact realizeT_readLift_indep v v' _
  · refine realizeT_bind_congr ?_ fun _ _ ↦ rfl
    rw [signAt, signAt]
    exact realizeT_bind₂_congr rfl fun _ ↦ realizeT_signT_congr upd hlab hneed hslot _ r

theorem realizeT_challengedT_congr {P : PublicParameter} {π : Equiv.Perm (X × Z)}
    {t t' : SpongeKeys X Z} {v v' : HPos → Digest} (hlab : ∀ lab : RLabel, v (.inr lab) = v' (.inr lab))
    (hneed : ∀ (l : Layer) (e : KeyIndex) (x : Encoding), e.val < keyCount l →
      ∀ q ∈ layerNeed l e x, v (.inl q) = v' (.inl q))
    (hslot : ∀ (l : Layer) (e : KeyIndex) (x : Encoding) (s : Slot), e.val < keyCount l →
      s ∈ layerSlots l e x → SlotPortsAgree ⟨P, π, t⟩ ⟨P, π, t'⟩ v s)
    {A B : QReg} {α : Type} (x : QComp (advSpec (X × Z)) A B α) :
    realizeT v (challengedT M upd ⟨P, π, t⟩ x) = realizeT v' (challengedT M upd ⟨P, π, t'⟩ x) := by
  have h₁ := realizeT_substitute (M := M) (good := goodAll) v (challengeT M upd ⟨P, π, t⟩) x
  have h₂ := realizeT_substitute (M := M) (good := goodAll) v' (challengeT M upd ⟨P, π, t'⟩) x
  refine (h₁.trans ?_).trans h₂.symm
  exact congrArg (fun σ ↦ IPFunctor.IFreeM.substitute σ x)
    (funext fun A ↦ funext fun c ↦ realizeT_challengeT_congr upd hlab hneed hslot A c)

/-- **The game congruence.** Realized at `v` and `v'`, the template games at `pub` and `pub'` are
equal when the parameters and permutations are, the values agree on the coordinates the game may
reveal (the root, the labels' randomizer bases, `layerNeed` of in-range keys), and the slot ports
agree on every slot a layer signature by an in-range key makes public. -/
theorem realizeT_gameT_congr (A : Adversary (X × Z)) {pub pub' : Pub} {v v' : HPos → Digest}
    (hP : pub.param = pub'.param) (hπ : pub.perm = pub'.perm)
    (hroot : v (.inl rootPos) = v' (.inl rootPos))
    (hlab : ∀ lab : RLabel, v (.inr lab) = v' (.inr lab))
    (hneed : ∀ (l : Layer) (e : KeyIndex) (x : Encoding), e.val < keyCount l →
      ∀ q ∈ layerNeed l e x, v (.inl q) = v' (.inl q))
    (hslot : ∀ (l : Layer) (e : KeyIndex) (x : Encoding) (s : Slot), e.val < keyCount l →
      s ∈ layerSlots l e x → SlotPortsAgree pub pub' v s) :
    realizeT v (gameT M upd pub A) = realizeT v' (gameT M upd pub' A) := by
  obtain ⟨P, π, t⟩ := pub
  obtain ⟨P', π', t'⟩ := pub'
  obtain rfl : P = P' := hP
  obtain rfl : π = π' := hπ
  refine realizeT_revealThen_congr _ (fun s hs ↦ by rw [Finset.mem_singleton.mp hs]; exact hroot)
    fun r₀ ↦ ?_
  exact realizeT_bind₂_congr (realizeT_challengedT_congr upd hlab hneed hslot _) fun _ ↦
    realizeT_bind₂_congr (realizeT_readLift_indep v v' _) fun _ ↦ rfl

end congr

/-! ## The reparametrized public datum -/

section reparam

/-- **Reparam's values are the table's** at the in-table positions and the chain starts, for
Reparam's table `((h, u), wOf L)` with `L`'s chain starts in the pad and `h` agreeing with `L`'s on
the honest paths' `h`-cells. -/
theorem xVal_eq_valuePos (L : HonestTable) {h : Z → X} {u : ValPos → Digest}
    (hu : ∀ l e i, u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      h (srcCellH (pubOf L) s (valuePos L) j) = L.keys.1 (srcCellH (pubOf L) s (valuePos L) j))
    (q : ValPos) (hq : InPos q ∨ ∃ l e i, q = .chain l e i ⟨0, by decide⟩) :
    xVal (wOf L) h u q = valuePos L q := by
  have hstart : ∀ (h₀ : Z → X) l e i, xVal (wOf L) h₀ u (.chain l e i ⟨0, by decide⟩) =
      valuePos L (.chain l e i ⟨0, by decide⟩) := fun h₀ l e i ↦ by
    rw [xVal, ite_eq_right fun hp ↦ Nat.not_succ_le_zero 0 hp.1, hu]
    rfl
  have hLk : ∀ q, (InPos q ∨ ∃ l e i, q = .chain l e i ⟨0, by decide⟩) →
      xVal (wOf L) L.keys.1 u q = valuePos L q := fun q hq ↦ by
    rcases hq with hp | ⟨l, e, i, rfl⟩
    · exact xVal_wOf L u (fun l e i _ ↦ hu l e i) hp
    · exact hstart _ l e i
  have hh : ∀ p, InPos p → ∀ i < nBlocks (xPub (wOf L) L.keys.1) (outSlot p),
      h (srcCellH (xPub (wOf L) L.keys.1) (outSlot p) (xVal (wOf L) L.keys.1 u) i) =
        L.keys.1 (srcCellH (xPub (wOf L) L.keys.1) (outSlot p) (xVal (wOf L) L.keys.1 u) i) :=
    fun p hp i hi ↦ by
      have hs := inTable_outSlot hp
      rw [cellH_congr _ (fun q hq ↦ hLk q (inPos_or_start hs hq)) i]
      exact hav _ hs i hi
  rcases hq with hp | ⟨l, e, i, rfl⟩
  · rw [xVal_congr_h hh q hp]
    exact hLk q (Or.inl hp)
  · exact hstart h l e i

/-- **The slot ports agree at the reparametrized datum**: on Reparam's good set, every slot a
layer signature by an in-range key makes public has, at the table's values, the same `k`, `k'` and
`h` cells and values at `pubOf L` and at `xPub (wOf L) h''`. -/
theorem slotPortsAgree_pubOf (L : HonestTable) {h : Z → X} {u : ValPos → Digest}
    (hθ : XGood ((h, u), wOf L))
    (hu : ∀ l e i, u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      h (srcCellH (pubOf L) s (valuePos L) j) = L.keys.1 (srcCellH (pubOf L) s (valuePos L) j))
    {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot} (he : e.val < keyCount l)
    (hs : s ∈ layerSlots l e x) :
    SlotPortsAgree (pubOf L) (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) (valueAt L) s := by
  intro j hj
  have hsIn : InTable s := inTable_of_mem_layerSlots he hs
  have hFv : ∀ q ∈ slotNeed s,
      extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L)) q = valuePos L q :=
    fun q hq ↦ extendVals_restrictTo (inl_mem_inlSet.mpr hq) (valueAt L)
  have hFx : ∀ q ∈ slotNeed s,
      extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L)) q = xVal (wOf L) h u q :=
    fun q hq ↦ (hFv q hq).trans (xVal_eq_valuePos L hu hav q ((mem_slotNeed hq).elim
      (inPos_or_start hsIn) fun hout ↦ Or.inl (hout ▸ inPos_slotOutPos hsIn))).symm
  have hinv : ∀ q, IsInput q s →
      extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L)) q = valuePos L q :=
    fun q hq ↦ hFv q (isInput_mem_slotNeed hq)
  have hinx : ∀ q, IsInput q s →
      extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L)) q = xVal (wOf L) h u q :=
    fun q hq ↦ hFx q (isInput_mem_slotNeed hq)
  obtain ⟨c1, c2, c3⟩ := cells_transfer L hθ hu hav hsIn hj
  refine ⟨?_, ?_, ?_⟩
  · show (srcCellK (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j,
        L.keys.2.1 (srcCellK (pubOf L) s
          (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j)) =
      (srcCellK (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) s
          (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j,
        L.keys.2.1 (srcCellK (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) s
          (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j))
    rw [cellK_congr (pubOf L) hinv, cellK_congr _ hinx, c1]
  · show (srcCellK' (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j,
        L.keys.2.2 (srcCellK' (pubOf L) s
          (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j)) =
      (srcCellK' (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) s
          (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j,
        L.keys.2.2 (srcCellK' (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) s
          (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j))
    rw [cellK'_congr (pubOf L) hinv, cellK'_congr _ hinx, c2]
  · have hj' : j < nBlocks (xPub (wOf L) h) (outSlot (slotOutPos s)) := by
      rw [outSlot_slotOutPos hsIn, nBlocks_xPub_wOf]
      exact hj
    obtain ⟨-, -, e3⟩ := rounds_fwd hθ (mem_xI.mpr (inPos_slotOutPos hsIn)) hj'
    have e4 := roundH_table (wOf L) h u (inPos_slotOutPos hsIn) hj'
    rw [outSlot_slotOutPos hsIn] at e3 e4
    have hc : (roundH (xPub (wOf L) h) s (xVal (wOf L) h u) j).1 =
        srcCellH (pubOf L) s (valuePos L) j := by
      rw [← e3]
      exact c3
    calc roundH (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j
        = (srcCellH (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j,
            L.keys.1 (srcCellH (pubOf L) s
              (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j)) :=
          Prod.ext rfl (roundH_snd L hs j)
      _ = (srcCellH (pubOf L) s (valuePos L) j,
            L.keys.1 (srcCellH (pubOf L) s (valuePos L) j)) := by
          rw [cellH_congr (pubOf L) hinv]
      _ = (srcCellH (pubOf L) s (valuePos L) j, h (srcCellH (pubOf L) s (valuePos L) j)) := by
          rw [hav s hsIn j hj]
      _ = roundH (xPub (wOf L) h) s (xVal (wOf L) h u) j := by
          rw [e4, hc]
      _ = roundH (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) s (xVal (wOf L) h u) j :=
          e3.symm
      _ = roundH (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) s
            (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j :=
          roundH_congr_of_need _ (fun q hq ↦ (hFx q hq).symm) (slotOutPos_mem hs) j

/-- Values agreeing off `B` agree on `univ \ B` (over abstract types: membership in `univ` never
unfolds). -/
theorem agree_univ_sdiff {S β : Type} [Fintype S] [DecidableEq S] {B : Finset S} {w w' : S → β}
    (h : ∀ s, s ∉ B → w s = w' s) : Agree (Finset.univ \ B) w w' :=
  fun s hs ↦ h s (Finset.mem_sdiff.mp hs).2

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **The game at the reparametrized public datum.** Over Reparam's table `θ` of the table `L`
(`hsub_core`'s hypotheses), the realized game at `pubOf L` is the game at `xPub θ.2 h''` (`h''`
the public `h` of `fwd`) realized at any `v` with Reparam's values on the positions and the
table's randomizer bases on the labels. -/
theorem realizeT_gameT_pubOf (A : Adversary (X × Z)) (L : HonestTable) (θ : RTab) (hθ : XGood θ)
    (hw : θ.2 = wOf L) (hu : ∀ l e i, θ.1.2 (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      θ.1.1 (srcCellH (pubOf L) s (valuePos L) j) = L.keys.1 (srcCellH (pubOf L) s (valuePos L) j))
    (v : HPos → Digest) (hinl : ∀ q, v (.inl q) = xVal θ.2 θ.1.1 θ.1.2 q)
    (hinr : ∀ lab, v (.inr lab) = valueAt L (.inr lab)) :
    realizeT (valueAt L) (gameT M upd (pubOf L) A) =
      realizeT v (gameT M upd (xPub θ.2 (fwd xmssFix xO θ).1.1) A) := by
  obtain ⟨⟨h, u⟩, w⟩ := θ
  obtain rfl : w = wOf L := hw
  refine realizeT_gameT_congr upd A rfl rfl ?_ (fun lab ↦ (hinr lab).symm) ?_
    fun l e x s he hs ↦ slotPortsAgree_pubOf L hθ hu hav he hs
  · rw [hinl]
    exact (xVal_eq_valuePos L hu hav _ (Or.inl inPos_rootPos)).symm
  · intro l e x he q hq
    rw [hinl]
    exact (xVal_eq_valuePos L hu hav q (layerNeed_good he hq)).symm

/-- **`hgame` for `uavg_totalWeight_portMass_le_xmssR0`.** For a reparametrization `e` whose
public datum is Reparam's `xPub (θ t).2 h''` of a Reparam table `θ t` of the table (with
`hsub_core`'s hypotheses), whose hidden values on the positions are Reparam's, and whose
randomizer bases off the non-first labels are the table's: on the good set, the game at the table
is the template game at the public datum realized at the hidden values `e`'s on the positions and
the table's on the labels, which agree with `e`'s off the non-first labels. -/
theorem hgame_xmssR0 (A : Adversary (X × Z)) {E P W : Type}
    (e : HonestTable × E → P × ((HPos → Digest) × (RK × W))) (G : HonestTable × E → Prop)
    (pubP : P → Pub) (parP : P → PublicParameter) (permP : P → Equiv.Perm (X × Z))
    (θ : HonestTable × E → RTab) (hθ : ∀ t, G t → XGood (θ t))
    (hw : ∀ t, G t → (θ t).2 = wOf t.1)
    (hu : ∀ t, G t → ∀ l k i, (θ t).1.2 (.chain l k i ⟨0, by decide⟩) = t.1.chainStart l k i)
    (hav : ∀ t, G t → ∀ s, InTable s → ∀ j < nBlocks (pubOf t.1) s,
      (θ t).1.1 (srcCellH (pubOf t.1) s (valuePos t.1) j) =
        t.1.keys.1 (srcCellH (pubOf t.1) s (valuePos t.1) j))
    (hpub : ∀ t, G t → pubP (e t).1 = xPub (θ t).2 (fwd xmssFix xO (θ t)).1.1)
    (hinl : ∀ t, G t → ∀ q, (e t).2.1 (.inl q) = xVal (θ t).2 (θ t).1.1 (θ t).1.2 q)
    (hinr : ∀ t, G t → ∀ lab, (.inr lab : HPos) ∉ r0Bk (permP (e t).1) (parP (e t).1) (e t).2.2.1 →
      (e t).2.1 (.inr lab) = valueAt t.1 (.inr lab)) :
    ∀ t, G t → ∃ v : HPos → Digest,
      Agree (Finset.univ \ r0Bk (permP (e t).1) (parP (e t).1) (e t).2.2.1) v (e t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) = realizeT v (gameT M upd (pubP (e t).1) A) := by
  intro t ht
  refine ⟨Sum.elim (fun q ↦ (e t).2.1 (.inl q)) fun lab ↦ valueAt t.1 (.inr lab),
    agree_univ_sdiff fun s hs ↦ ?_, ?_⟩
  · rcases s with q | lab
    · rfl
    · exact (hinr t ht lab hs).symm
  · rw [hpub t ht]
    exact realizeT_gameT_pubOf upd A t.1 (θ t) (hθ t ht) (hw t ht) (hu t ht) (hav t ht) _
      (hinl t ht) fun _ ↦ rfl

end reparam

end Quantum.Xmss.Assembly

end
