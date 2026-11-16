module

public import Quantum.Sphincs.Assembly.CostRefined
public import Quantum.Xmss.Assembly.HwHeads

@[expose] public section

/-!
# leanSPHINCS: the hardwired `h` cells head honest tails

leanXMSS's `Quantum.Xmss.Assembly.HwHeads` on CostRun's canonical prefix `prefixR pol A p v` at
the template data `(p, v)`, for every digest policy: every call of the prefix is presented only
states whose hardwired `h` cells head head-tails of the union at a slot other than an encoding slot
(`HwHeadsHonest`, `forallQueries_hwHeads_prefixR`). A hardwired trial head (`hwHeadW`: a trial
read whose cell is hardwired, outside `BadR`, the trial's one-block tail heading the cell,
EncPotential's `TrialGood`) then cannot occur, so `hwHeadPre = 0` (`hwHeadPre_eq_zero_all`).

* **Honest heads** (`HonAt`, `HonHw`, `hwHeadsHonest_of_honHw`): every hardwired `h` cell heads a
  non-encoding head-tail of the hardwired `k`, `k'` cells alone; the union extends them. The
  template programs `k`, `k'` cells only with the keys' values (`KeyProg`), so a program keeps the
  earlier heads (`extends_progUpdate_key`, `headsInv_progUpdate`).
* **The `h` port of a round** (`batchOk_heads`): with the `k`, `k'` cells of rounds `0, …, j`
  held, Exempt's `isHeadTail_take_succ_rn` gives the head-tail of the first `j + 1` blocks. Its slot
  is not an encoding slot (`slotOf_take_ne_enc`): a prefix of a tail at a structural or `H_msg`
  slot is read from the same first block, or (one block) as an `H_msg`, `PRF_msg`, key-expansion
  call or that block's slot (`batchOk_heads_slot`, `batchOk_heads_hmsg`).
* **The batch order** (GameTCalls' `HB` with the condition `headsOk`; `hb_heads_prefixT`) and the
  invariant along the realized prefix (`forallQueries_heads_of_hb`, carrying `HeadsInv` beside the
  held ports).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (HashOutput Message Randomizer)
open Quantum.Xmss (X Z blocks length_blocks)
open Quantum.Xmss.Hybrid (LazyProg progUpdate restrictTo ReadMono totalWeight_const_mul_weight)
open Quantum.Xmss.Assembly (recHwSpec runtimeR realizeT extWeight extends_union absorbTail_take
  progUpdate_fst_of_ne invSupp DiagOn traceRight_diag_eq_zero forallQueries_and
  totalWeight_le_of_forallQueries memLab)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default
size. -/
set_option synthInstance.maxSize 2000

/-! ## Honest heads of the hardwired cells -/

section heads

/-- **An honest head at `z`**: a head-tail of `D` ending at `z` at a slot other than an encoding
slot. -/
def HonAt (d : EvData) (D : Dbs X Z) (z : Z) : Prop :=
  ∃ t xi, IsHeadTail d.perm D t z xi ∧ ∀ K : Key, ¬ EncAt d K t

theorem HonAt.mono {d : EvData} {D D' : Dbs X Z} (hE : Extends D D') {z : Z}
    (h : HonAt d D' z) : HonAt d D z :=
  let ⟨t, xi, ht, hs⟩ := h
  ⟨t, xi, ht.mono hE, hs⟩

/-- **The hardwired `h` cells head honest tails of the hardwired `k`, `k'` cells.** -/
def HonHw (d : EvData) (W : Hw X Z) : Prop :=
  ∀ z, W.1 z ≠ none → HonAt d W.toDbs z

/-- **The register states whose hardwired `h` cells head honest tails of the union**: every
hardwired `h` cell is the end of a head-tail of the union at a slot other than an encoding slot. -/
def HwHeadsHonest (d : EvData) (s : HwReg X Z (Mem HPos)) : Prop :=
  ∀ z, s.2.1.1 z ≠ none → HonAt d (union s.2.1 s.1) z

theorem hwHeadsHonest_of_honHw {d : EvData} {s : HwReg X Z (Mem HPos)} (h : HonHw d s.2.1) :
    HwHeadsHonest d s :=
  fun z hz ↦ (h z hz).mono (extends_union s.2.1 s.1)

/-- The condition of a program port at the hardwired cells `W`: an `h` port's cell heads an
honest tail of `W`. -/
def HeadOk (d : EvData) : HwProg X Z → Hw X Z → Prop
  | .programH z _, W => HonAt d W.toDbs z
  | _, _ => True

section gen

variable {X₁ Z₁ : Type} [DecidableEq X₁] [DecidableEq Z₁] (k k' : X₁ → Z₁)

/-- The hardwired `k`, `k'` cells hold the values of `k`, `k'`. -/
def KeyCellsOk (W : Hw X₁ Z₁) : Prop :=
  (∀ x b, W.2.1 x = some b → b = k x) ∧ ∀ x b, W.2.2 x = some b → b = k' x

/-- A program port writes a `k`, `k'` cell with the value of `k`, `k'`. -/
def KeyProg : HwProg X₁ Z₁ → Prop
  | .programK x a => a = k x
  | .programK' x a => a = k' x
  | .programH _ _ => True

variable {k k'}

theorem keyCellsOk_progUpdate {W : Hw X₁ Z₁} (hW : KeyCellsOk k k' W) {c : HwProg X₁ Z₁}
    (hc : KeyProg k k' c) : KeyCellsOk k k' (progUpdate c W) := by
  cases c with
  | programH z a => exact hW
  | programK x a =>
    refine ⟨fun y b h ↦ ?_, hW.2⟩
    change Function.update W.2.1 x (some a) y = some b at h
    by_cases hy : y = x
    · subst hy
      rw [Function.update_self, Option.some_inj] at h
      rw [← h]
      exact hc
    · rw [Function.update_of_ne hy] at h
      exact hW.1 y b h
  | programK' x a =>
    refine ⟨hW.1, fun y b h ↦ ?_⟩
    change Function.update W.2.2 x (some a) y = some b at h
    by_cases hy : y = x
    · subst hy
      rw [Function.update_self, Option.some_inj] at h
      rw [← h]
      exact hc
    · rw [Function.update_of_ne hy] at h
      exact hW.2 y b h

/-- **A program port writing the keys' values never overwrites a hardwired cell with another
value**: the hardwired cells after it extend those before. -/
theorem extends_progUpdate_key {W : Hw X₁ Z₁} (hW : KeyCellsOk k k' W) {c : HwProg X₁ Z₁}
    (hc : KeyProg k k' c) : Extends (progUpdate c W).toDbs W.toDbs := by
  cases c with
  | programH z a => exact ⟨fun _ _ h ↦ h, fun _ _ h ↦ h⟩
  | programK x a =>
    refine ⟨fun y b h ↦ ?_, fun _ _ h ↦ h⟩
    change W.2.1 y = some b at h
    change Function.update W.2.1 x (some a) y = some b
    by_cases hy : y = x
    · subst hy
      rw [Function.update_self, hW.1 y b h]
      exact congrArg some hc
    · rw [Function.update_of_ne hy]
      exact h
  | programK' x a =>
    refine ⟨fun _ _ h ↦ h, fun y b h ↦ ?_⟩
    change W.2.2 y = some b at h
    change Function.update W.2.2 x (some a) y = some b
    by_cases hy : y = x
    · subst hy
      rw [Function.update_self, hW.2 y b h]
      exact congrArg some hc
    · rw [Function.update_of_ne hy]
      exact h

omit [DecidableEq X₁] [DecidableEq Z₁] in
theorem keyCellsOk_hwEmpty : KeyCellsOk k k' (hwEmpty X₁ Z₁) :=
  ⟨fun _ _ h ↦ absurd h (by simp [hwEmpty, Database.empty]),
    fun _ _ h ↦ absurd h (by simp [hwEmpty, Database.empty])⟩

omit [DecidableEq X₁] [DecidableEq Z₁] in
theorem hwEmpty_fst (z : Z₁) : (hwEmpty X₁ Z₁).1 z = none := by
  simp [hwEmpty, Database.empty]

end gen

/-- **The invariant of the hardwired cells**: the keys' values at the `k`, `k'` cells, honest heads
at the `h` cells. -/
def HeadsInv (pub : Pub) (v : (s : HPos) → XD s) (W : Hw X Z) : Prop :=
  KeyCellsOk pub.keys.2.1 pub.keys.2.2 W ∧ HonHw (evData pub v) W

/-- **A program port keeps the invariant** if it writes the keys' values and an `h` port's cell
heads an honest tail. -/
theorem headsInv_progUpdate {pub : Pub} {v : (s : HPos) → XD s} {W : Hw X Z}
    (hW : HeadsInv pub v W) {c : HwProg X Z} (hc : KeyProg pub.keys.2.1 pub.keys.2.2 c)
    (hh : HeadOk (evData pub v) c W) : HeadsInv pub v (progUpdate c W) := by
  refine ⟨keyCellsOk_progUpdate hW.1 hc, ?_⟩
  have hE := extends_progUpdate_key hW.1 hc
  cases c with
  | programH z a =>
    intro z' hz'
    by_cases h : z' = z
    · subst h
      exact HonAt.mono hE hh
    · rw [progUpdate_fst_of_ne a h] at hz'
      exact (hW.2 z' hz').mono hE
  | programK x a => exact fun z hz ↦ (hW.2 z hz).mono hE
  | programK' x a => exact fun z hz ↦ (hW.2 z hz).mono hE

theorem headsInv_hwEmpty (pub : Pub) (v : (s : HPos) → XD s) : HeadsInv pub v (hwEmpty X Z) :=
  ⟨keyCellsOk_hwEmpty, fun z hz ↦ absurd (hwEmpty_fst z) hz⟩

end heads

/-! ## Prefixes of a non-encoding tail -/

section slots

theorem map_hmsg_ne_enc (o : Option DigestCall) (R : Randomizer) (msg : Message) (l : Layer)
    (τ : TreeIndex) (e : TreeLeafIndex) : o.map (Slot.hmsg R msg) ≠ some (.enc l τ e) := by
  rcases o with _ | c <;> intro h <;> cases h

theorem hmsgSlot_ne_enc (pk : PublicKey) (x : X) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) :
    hmsgSlot pk x ≠ some (.enc l τ e) := by
  intro h
  unfold hmsgSlot at h
  split_ifs at h
  exact map_hmsg_ne_enc _ _ _ l τ e h

/-- **A one-block tail is not at an encoding slot** if its block names a non-encoding slot. -/
theorem slotOfOneBlock_ne_enc {pk : PublicKey} {x : X} {s : Slot} (hb : slotOfBlock pk x = some s)
    (hs : ∀ l τ e, s ≠ .enc l τ e) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) :
    slotOfOneBlock pk x ≠ some (.enc l τ e) := by
  unfold slotOfOneBlock
  split_ifs
  · exact hmsgSlot_ne_enc pk x l τ e
  · intro h
    cases h
  · intro h
    cases h
  · rw [hb]
    exact fun h ↦ hs l τ e (Option.some.inj h)

/-- **A nonempty prefix of a tail at a non-encoding slot is not at an encoding slot.** -/
theorem slotOf_take_ne_enc {pk : PublicKey} {t : List X} {s : Slot} (ht : slotOf pk t = some s)
    (hs : ∀ l τ e, s ≠ .enc l τ e) {n : ℕ} (hn : 1 ≤ n) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) : slotOf pk (t.take n) ≠ some (.enc l τ e) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases t with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · simp [slotOf] at ht
  · rw [List.take_succ_cons, List.take_nil, ht]
    exact fun h ↦ hs l τ e (Option.some.inj h)
  · have hb : slotOfBlock pk x = some s := ht
    rcases m with _ | m
    · show slotOfOneBlock pk x ≠ _
      exact slotOfOneBlock_ne_enc hb hs l τ e
    · show slotOfBlock pk x ≠ _
      rw [hb]
      exact fun h ↦ hs l τ e (Option.some.inj h)

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **The prefixes of an absorption whose tail is at a non-encoding slot are at none.** -/
theorem encFree_of_slotOf {msg : List X} {s : Slot}
    (ht : slotOf (evData pub v).pk (absorbTail (spongePerm pub.keys pub.perm) msg) = some s)
    (hs : ∀ l τ e, s ≠ .enc l τ e) :
    ∀ j < msg.length, ∀ K : Key,
      ¬ EncAt (evData pub v) K (absorbTail (spongePerm pub.keys pub.perm) (msg.take (j + 1))) := by
  intro j _ K hK
  unfold EncAt at hK
  rw [absorbTail_take] at hK
  exact slotOf_take_ne_enc ht hs (Nat.succ_pos j) K.1 K.2.1 K.2.2 hK

end slots

/-! ## The condition at the program ports -/

section batch

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **The condition of the honest heads at a program call**: the port writes the keys' values, and
on hardwired cells holding the keys' values an `h` port's cell heads an honest tail. -/
def headsOk (c : HwProg X Z) (r : HwReg X Z (Mem HPos)) : Prop :=
  KeyProg pub.keys.2.1 pub.keys.2.2 c ∧
    (KeyCellsOk pub.keys.2.1 pub.keys.2.2 r.2.1 → HeadOk (evData pub v) c r.2.1)

/-- **The ports of the first `n` rounds of an absorption keep the honest heads** (GameTCalls'
`BatchOk`), if the prefixes of its tail are at no encoding slot: the `h` port of round `j`, with
the `k`, `k'` cells of rounds `0, …, j` held, heads the tail of the first `j + 1` blocks (Exempt's
`isHeadTail_take_succ_rn`). -/
theorem batchOk_heads (msg : List X) (cor : X → X → X) {n : ℕ} (hn : n ≤ msg.length)
    (hne : ∀ j < msg.length, ∀ K : Key,
      ¬ EncAt (evData pub v) K (absorbTail (spongePerm pub.keys pub.perm) (msg.take (j + 1)))) :
    BatchOk pub (headsOk pub v) (fun i ↦ msg.getD i 0) cor n := by
  intro j hj r hr
  refine ⟨⟨rfl, fun _ ↦ trivial⟩, fun hk ↦ ⟨⟨rfl, fun _ ↦ trivial⟩, fun hk' ↦
    ⟨trivial, fun _ ↦ ?_⟩⟩⟩
  show HonAt (evData pub v) r.2.1.toDbs (cellH pub (fun i ↦ msg.getD i 0) (n - 1) cor j).1
  rw [cellH_fst]
  refine ⟨_, _, isHeadTail_take_succ_rn pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
    (D := r.2.1.toDbs) (msg := msg) (j := j) (by omega) fun i hi ↦ ?_, hne j (by omega)⟩
  rcases hi.lt_or_eq with hi | rfl
  · exact ⟨(hr i hi).1, (hr i hi).2.1⟩
  · exact ⟨hk, hk'⟩

/-- **A structural slot's ports keep the honest heads.** -/
theorem batchOk_heads_slot {s : Slot} (hs : InTable s) :
    BatchOk pub (headsOk pub v) (slotBlk pub.seed s (valsOf v)) (cor128 (valsOf v (slotOutPos s)))
      (nBlk pub.seed s) :=
  batchOk_heads pub v (blocks (slotInput pub.seed s (valsOf v))) _
    (length_blocks_slotInput pub.seed s (valsOf v)).ge
    (encFree_of_slotOf pub v ((evData pub v).slotOf_honTail hs) fun l τ e he ↦ by
      rw [he] at hs
      exact hs)

/-- **An `H_msg` call's ports keep the honest heads.** -/
theorem batchOk_heads_hmsg (R : Randomizer) (msg : Message) (i : DigestCall) (y : HashOutput) :
    BatchOk pub (headsOk pub v) (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) (cor256 y) 1 :=
  batchOk_heads pub v (blocks (slotInput pub.seed (.hmsg R msg i) (valsOf v))) _
    (by rw [length_blocks]; omega)
    (encFree_of_slotOf pub v ((evData pub v).slotOf_honTail_hmsg R msg i) fun _ _ _ he ↦ by
      cases he)

/-- **The challenge prefix's program ports keep the honest heads in batch order.** -/
theorem hb_heads_prefixT (pol : DigestPolicy) (A : SAdversary) :
    HB (headsOk pub v) v (prefixT Selections cwUpd pol pub A) ∅ ∅ :=
  hb_revealThen _ v _ _ fun _ ↦ hb₂_bind _ v _ _ (hb_substitute _ v _
    (hb_challengeT (headsOk pub v) v pub (fun _ hs ↦ batchOk_heads_slot pub v hs)
      (fun _ _ _ ↦ batchOk_heads_hmsg pub v _ _ _ _) cwUpd pol) _) fun _ ↦ subset_rfl

end batch

/-! ## The invariant along the realized prefix -/

section present

variable (pub : Pub) (v : (s : HPos) → XD s) {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- The register states holding the ports `C`, on the invariant. -/
def HeldInv (C : Set (HwProg X Z)) (s : HwReg X Z (Mem HPos)) : Prop :=
  AllHeld C s.2.1 ∧ HeadsInv pub v s.2.1

/-- The read ports of `runtimeR`. -/
def ReadPortQ : (recHwSpec X Z HPos Selections).Port → Prop
  | .inl (.inl (.inr _)) => True
  | _ => False

/-- A program step keeping the honest heads moves `HeldInv` at `C` to `HeldInv` at
`heldNext c C`. -/
theorem stepR_heads_prog {C : Set (HwProg X Z)} {c : HwProg X Z} (hc : OkC (headsOk pub v) C c) :
    StepR m0R (.inl (.inr c)) (HeldInv pub v C) (HeldInv pub v (heldNext c C)) :=
  stepR_prog m0R c fun r r' he hr ↦ by
    unfold HeldInv at hr ⊢
    rw [he]
    exact ⟨allHeld_progUpdate hr.1 c, headsInv_progUpdate hr.2 (hc r hr.1).1 ((hc r hr.1).2 hr.2.1)⟩

/-- At a read port, an operator supported on `HeldInv` presents only honest heads. -/
theorem heads_pre_read {C : Set (HwProg X Z)} {A : QReg}
    (c : {c : HwRead X Z (Finset HPos × Selections) // ReadMono (memLab X Z HPos Selections) c})
    (E : QReg) (ℓ : A ≃ (recHwSpec X Z HPos Selections).In (.inl (.inl (.inr c.1))) × E)
    (ρ : Matrix (A × (runtimeR m0R).D) (A × (runtimeR m0R).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m0R).D ↦ m.2) {s | HeldInv pub v C s} ρ) :
    invSupp (runtimeR m0R) ReadPortQ (HwHeadsHonest (evData pub v)) (.inl (.inl (.inr c.1))) E
      ((SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m0R).D)).branch () ρ) :=
  fun _ a ha ↦ relabel_diag_eq_zero_of_supp m0R E ℓ hρ a fun hS ↦
    ha (hwHeadsHonest_of_honHw hS.2.2)

/-- **The realized program of a template whose program ports keep the honest heads in batch order
presents only states whose hardwired `h` cells head honest tails at its read calls**, from states
holding the ports `C` on the invariant. -/
theorem forallQueries_heads_of_hb (I : L.Interp) {A : QReg}
    (y : QuantumComp L (SSpec Selections) Ω A) :
    ∀ C C', HB (headsOk pub v) v y C C' →
      ∀ ρ : Matrix (A × (runtimeR m0R).D) (A × (runtimeR m0R).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m0R).D ↦ m.2) {s | HeldInv pub v C s} ρ →
      (runtimeR m0R).ForallQueries I
        (invSupp (runtimeR m0R) ReadPortQ (HwHeadsHonest (evData pub v))) (realizeT v y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro C C' hy ρ hρ b
    exact ih b C C' (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepR (P := HeldInv pub v C) (P' := HeldInv pub v C)
        m0R I (.inl (.inl (.inl i))) E ℓ (fun r ↦ realizeT v (k r)) (fun _ _ h ↦ (h : False).elim)
        (stepR_sponge m0R i fun _ _ he hr ↦ by
          unfold HeldInv at hr ⊢
          rw [he]
          exact hr)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepR (P := HeldInv pub v C) (P' := HeldInv pub v C)
        m0R I (.inl (.inl (.inr c.1))) E ℓ (fun r ↦ realizeT v (k r))
        (heads_pre_read pub v c E ℓ)
        (stepR_read m0R c fun _ _ he hr ↦ by
          unfold HeldInv at hr ⊢
          rw [he]
          exact hr)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepR (P := HeldInv pub v C) m0R I
          (.inl (.inr ((LazyProg.programH T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun _ _ h ↦ (h : False).elim) (stepR_heads_prog pub v hy.1)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepR (P := HeldInv pub v C) m0R I
          (.inl (.inr ((LazyProg.programK T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun _ _ h ↦ (h : False).elim) (stepR_heads_prog pub v hy.1)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepR (P := HeldInv pub v C) m0R I
          (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun _ _ h ↦ (h : False).elim) (stepR_heads_prog pub v hy.1)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepR (P := HeldInv pub v C) (P' := HeldInv pub v C)
        m0R I (.inr T) E ℓ (fun m ↦ realizeT v (k (restrictTo T v, m)))
        (fun _ _ h ↦ (h : False).elim)
        (stepR_rec m0R T fun _ _ he hr ↦ by
          unfold HeldInv at hr ⊢
          rw [he]
          exact hr)
        (fun m ↦ ih (restrictTo T v, m) _ C' (hy.2 (ULift.up (restrictTo T v, m)))) ρ hρ

/-- The initial state holds nothing and is on the invariant. -/
theorem querySupportedOn_initR_heads :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D ↦ m.2)
      {s | HeldInv pub v ∅ s} initR :=
  querySupportedOn_basis_init m0R () (fun s ↦ s) {s | HeldInv pub v ∅ s}
    ⟨fun c hc ↦ absurd hc (Set.notMem_empty c), headsInv_hwEmpty pub v⟩

/-- **The honest-heads invariant along the prefix**: at every digest policy and template data, every
read call of the challenge prefix is presented only states whose hardwired `h` cells head honest
(non-encoding) head-tails. -/
theorem forallQueries_hwHeads_prefixR (pol : DigestPolicy) (A : SAdversary) :
    (runtimeR m0R).ForallQueries .instruments
      (invSupp (runtimeR m0R) ReadPortQ (HwHeadsHonest (evData pub v)))
      (prefixR pol A pub v) initR :=
  forallQueries_heads_of_hb pub v .instruments _ ∅ ∅ (hb_heads_prefixT pub v pol A) initR
    (querySupportedOn_initR_heads pub v)

end present

/-! ## The hardwired trial heads -/

section hwHead

open scoped Classical in
/-- **The hardwired trial heads of a trial read port**: the states whose read cell is hardwired,
outside `BadR`, with the trial's one-block tail heading the cell (EncPotential's `TrialGood`; `0`
at the other read ports). -/
noncomputable def hwHeadW (p : Pub) (v : (s : HPos) → XD s) (c : HwRead X Z (Mem HPos))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal (∑ q, (if q.2.2.1.1 (trialOf trialUpd c).1 ≠ none ∧
    q.2 ∉ BadR p v progCap ∧ TrialGood Prod.snd (evData p v) (trialOf trialUpd c).1
      (trialOf trialUpd c).2 q.2 then (1 : ℝ) else 0) * (σ q q).re) else 0

/-- **The hardwired trial heads along the prefix.** -/
noncomputable def hwHeadPre (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (hwHeadW p v) fun _ _ ↦ 0))
    (prefixR pol A p v) initR

/-- **No hardwired trial head on states with honest hardwired heads**: outside `BadR` (a good union
at hardwired grade at most `progCap`) the head-tail of the read cell is unique, so it cannot be
both the trial's (at an encoding slot) and an honest one. -/
theorem hwHeadW_eq_zero (p : Pub) (v : (s : HPos) → XD s) (c : HwRead X Z (Mem HPos))
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hH : ∀ a, σ a a ≠ 0 → HwHeadsHonest (evData p v) a.2 ∧ dbGrade a.2.2.1 ≤ progCap) :
    hwHeadW p v c σ = 0 := by
  classical
  by_cases ht : IsTrial trialUpd c
  · simp only [hwHeadW, ht, ↓reduceIte]
    rw [Finset.sum_eq_zero fun a _ ↦ ?_, ENNReal.ofReal_zero]
    by_cases h0 : σ a a = 0
    · rw [h0, Complex.zero_re, mul_zero]
    rw [ite_eq_right, zero_mul]
    rintro ⟨hw, hb, hg⟩
    obtain ⟨hhon, hN⟩ := hH a h0
    obtain ⟨t, xi, hi, hslot⟩ := hhon _ hw
    have hG : Good p.perm (union a.2.2.1 a.2.1) :=
      good_of_not_mem_bad (D := a.2.1) (W := a.2.2.1) (m := a.2.2.2) hb hN
    rcases hg with hg | ⟨-, henc, hi'⟩
    · exact hg hG
    · obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hi'
      exact hslot _ henc
  · simp only [hwHeadW, ht, ↓reduceIte]

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The hardwired trial heads vanish under the honest-heads invariant**: if every read call of
the prefix is presented states whose hardwired `h` cells head honest tails (`HwHeadsHonest`), then
`hwHeadPre = 0`. -/
theorem hwHeadPre_eq_zero (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (h : (runtimeR m0R).ForallQueries .instruments
      (invSupp (runtimeR m0R) ReadPortQ (HwHeadsHonest (evData p v)))
      (prefixR pol A p v) initR) :
    hwHeadPre pol A p v = 0 := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign pol p v
  refine le_antisymm ((totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i σ ↦ PreInv q i σ ∧ (ReadPortQ i → DiagOn (HwHeadsHonest (evData p v)) σ))
    (P := fun i E σ ↦ P i E σ ∧
      invSupp (runtimeR m0R) ReadPortQ (HwHeadsHonest (evData p v)) i E σ)
    (fun i E σ h ↦ ⟨hP i E σ h.1, fun hq a ha ↦
      traceRight_diag_eq_zero fun e ↦ h.2 hq (a, e) ha⟩)
    (w' := fun i σ ↦ 0 * extWeight (hwCost (hwHeadW p v) fun _ _ ↦ 0) i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR pol A p v) initR_posSemidef (forallQueries_and hx h)).trans_eq
    ?_) zero_le
  · rcases i with ((sp | c) | c) | T
    · exact zero_le
    · refine le_of_eq ((hwHeadW_eq_zero p v c fun a ha ↦ ⟨?_, (hI.1.2.1 a a ha).1.2⟩).trans
        (zero_mul _).symm)
      by_contra hn
      exact ha (hI.2 trivial a hn)
    · exact zero_le
    · exact zero_le
  · exact (totalWeight_const_mul_weight (runtimeR m0R) .instruments _
      (extWeight (hwCost (hwHeadW p v) fun _ _ ↦ 0)) (prefixR pol A p v) initR).trans (zero_mul _)

/-- **The hardwired trial heads vanish along the prefix**, at every digest policy and template
data. -/
theorem hwHeadPre_eq_zero_all (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    hwHeadPre pol A p v = 0 :=
  hwHeadPre_eq_zero hperm hsign pol p v (forallQueries_hwHeads_prefixR p v pol A)

end hwHead

end Quantum.Sphincs.Assembly

end
