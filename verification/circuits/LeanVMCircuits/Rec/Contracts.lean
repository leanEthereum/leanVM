module

public import LeanVMCircuits.Rec.Builder
public import LeanVMCircuits.Rec.Rows
public import LeanVMCircuits.Rec.Duplex

@[expose] public section

/-!
What the builder's methods make their outputs.

An assignment gives every wire four `K` limbs. It satisfies a circuit when every pair of wires held equal carries
the same limbs (the bus, `Rec.copy_argument`), every row's slots carry the limbs its table's forms give some row of
columns satisfying the table (its identities; for `HASH` a packed witness of the exported BLAKE2s artifact with the
row's ports), and every public row carries its constant or its statement word. Each method's contract: from a
state keeping the builder's invariant, it keeps it, only adds to the circuit, and in every assignment satisfying any
circuit containing what it built, its output is what the method computes: `a·b + d` in `E`, an inverse, a word's
bits, a digest's words, a BLAKE2s compression.
-/

namespace LeanVMCircuits.Rec.Model

open LeanVMCircuits.Rec

/-! Assignments. -/

abbrev Val := ℕ → Fin 4 → K

/-- A wire's `E` element: its first three limbs. -/
noncomputable def ev (val : Val) (w : ℕ) : E := toE (val w 0) (val w 1) (val w 2)

/-- A constant's limbs. -/
noncomputable def limbsOf (v : Limbs) (i : Fin 4) : K := ofWord (v.getD i 0)

/-- A public row's value: its constant, or its statement word. -/
noncomputable def srcVal (statement : ℕ → Fin 4 → K) : PubSource → Fin 4 → K
  | .const v => limbsOf v
  | .statement i => statement i

/-- A row of a table whose slots carry its wires' limbs, from columns satisfying `holds`. -/
def RowSat (forms : List (List Form)) (holds : (ℕ → K) → Prop) (val : Val) (r : List ℕ) : Prop :=
  ∃ col : ℕ → K, holds col ∧ ∀ s < forms.length, ∀ i : Fin 4, limbs forms s col i = val (r.getD s 0) i

/-- An assignment satisfying a circuit. -/
structure Sat (statement : ℕ → Fin 4 → K) (s : State) (val : Val) : Prop where
  unions : ∀ p ∈ s.unions, val p.1 = val p.2
  emul : ∀ r ∈ s.emul, RowSat Rec.emul (fun _ => True) val r
  exk : ∀ r ∈ s.exk, RowSat Rec.exk (fun _ => True) val r
  hash : ∀ r ∈ s.hash, RowSat Rec.hash HashRow val r
  split : ∀ r ∈ s.split, RowSat Rec.split (fun col => ∀ id ∈ splitIdentities, id.eval col = 0) val r
  cast : ∀ r ∈ s.cast, RowSat Rec.cast (fun _ => True) val r
  pub : ∀ w src, (w, src) ∈ s.pub → val w = srcVal statement src

/-- `s'` holds everything `s` does. -/
structure Ext (s s' : State) : Prop where
  next : s.next ≤ s'.next
  unions : ∀ p ∈ s.unions, p ∈ s'.unions
  emul : ∀ r ∈ s.emul, r ∈ s'.emul
  exk : ∀ r ∈ s.exk, r ∈ s'.exk
  hash : ∀ r ∈ s.hash, r ∈ s'.hash
  split : ∀ r ∈ s.split, r ∈ s'.split
  cast : ∀ r ∈ s.cast, r ∈ s'.cast
  pub : ∀ p ∈ s.pub, p ∈ s'.pub

theorem Ext.refl (s : State) : Ext s s :=
  ⟨le_rfl, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Ext.trans {s₁ s₂ s₃ : State} (h₁ : Ext s₁ s₂) (h₂ : Ext s₂ s₃) : Ext s₁ s₃ :=
  ⟨h₁.next.trans h₂.next, fun p h => h₂.unions p (h₁.unions p h), fun r h => h₂.emul r (h₁.emul r h),
    fun r h => h₂.exk r (h₁.exk r h), fun r h => h₂.hash r (h₁.hash r h), fun r h => h₂.split r (h₁.split r h),
    fun r h => h₂.cast r (h₁.cast r h), fun p h => h₂.pub p (h₁.pub p h)⟩

theorem Sat.mono {st : ℕ → Fin 4 → K} {s s' : State} {val : Val} (h : Sat st s' val) (he : Ext s s') :
    Sat st s val :=
  ⟨fun p hp => h.unions p (he.unions p hp), fun r hr => h.emul r (he.emul r hr), fun r hr => h.exk r (he.exk r hr),
    fun r hr => h.hash r (he.hash r hr), fun r hr => h.split r (he.split r hr), fun r hr => h.cast r (he.cast r hr),
    fun w src hp => h.pub w src (he.pub _ hp)⟩

/-! The builder's invariant. -/

def eOneKey : Kind × Limbs := (.e, [1, 0, 0, 0])

structure Inv (s : State) : Prop where
  emulLt : ∀ r ∈ s.emul, ∀ w ∈ r, w < s.next
  consts : ∀ (kv : Kind × Limbs) w, s.consts[kv]? = some w → (w, PubSource.const kv.2) ∈ s.pub
  eZero : ∀ w, s.units.eZero = some w → (w, PubSource.const [0, 0, 0, 0]) ∈ s.pub
  eOne : ∀ w, s.units.eOne = some w → s.consts[eOneKey]? = some w
  kZero : ∀ w, s.units.kZero = some w → (w, PubSource.const [0, 0, 0, 0]) ∈ s.pub
  kOne : ∀ w, s.units.kOne = some w → (w, PubSource.const [1, 0, 0, 0]) ∈ s.pub
  arithE : ∀ k0 k1 k2 c, s.arith[(0, k0, k1, k2)]? = some c →
    ∃ a b d, [a, b, d, c] ∈ s.emul ∧ emulKey s.units a b d = (k0, k1, k2)
  arithK : ∀ a k d c, s.arith[(1, a, k, d)]? = some c → [a, k, d, c] ∈ s.exk
  /-- Every wire a cached row returns, and every unit, is a wire. -/
  arithLt : ∀ (key : ℕ × ℕ × ℕ × ℕ) c, s.arith[key]? = some c → c < s.next
  constsLt : ∀ (kv : Kind × Limbs) w, s.consts[kv]? = some w → w < s.next
  pubLt : ∀ p ∈ s.pub, p.1 < s.next

theorem inv_empty : Inv ({} : State) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp



/-! Hoare-style contracts of `M` programs. -/

/-- From a state keeping the invariant and `pre`, `m` keeps the invariant, extends the circuit, and relates its
start, output and end by `Q`. -/
def Good {α : Type} (pre : State → Prop) (m : M α) (Q : State → α → State → Prop) : Prop :=
  ∀ s, Inv s → pre s → Inv (m.run s).2 ∧ Ext s (m.run s).2 ∧ Q s (m.run s).1 (m.run s).2

theorem Good.bind {α β : Type} {P : State → Prop} {m : M α} {f : α → M β} {Q₁ : State → α → State → Prop}
    {P₂ : α → State → Prop} {Q₂ : α → State → β → State → Prop} (h₁ : Good P m Q₁)
    (hp : ∀ s a s', Inv s → P s → Q₁ s a s' → Ext s s' → P₂ a s') (h₂ : ∀ a, Good (P₂ a) (f a) (Q₂ a)) :
    Good P (m >>= f) fun s b s'' => ∃ a s', Q₁ s a s' ∧ Ext s s' ∧ Ext s' s'' ∧ Q₂ a s' b s'' := by
  intro s hs hP
  obtain ⟨hi₁, he₁, hq₁⟩ := h₁ s hs hP
  obtain ⟨hi₂, he₂, hq₂⟩ := h₂ _ _ hi₁ (hp _ _ _ hs hP hq₁ he₁)
  exact ⟨hi₂, he₁.trans he₂, _, _, hq₁, he₁, he₂, hq₂⟩

theorem Good.weaken {α : Type} {P P' : State → Prop} {m : M α} {Q Q' : State → α → State → Prop}
    (h : Good P m Q) (hp : ∀ s, P' s → P s) (hq : ∀ s a s', Inv s → P' s → Ext s s' → Q s a s' → Q' s a s') :
    Good P' m Q' := by
  intro s hs hP
  obtain ⟨hi, he, hq'⟩ := h s hs (hp s hP)
  exact ⟨hi, he, hq s _ _ hs hP he hq'⟩

/-! What a satisfying assignment says of each kind of row. -/

theorem RowSat.limb {forms : List (List Form)} {holds : (ℕ → K) → Prop} {val : Val} {r : List ℕ}
    (h : RowSat forms holds val r) : ∃ col, holds col ∧ ∀ s < forms.length, ∀ i : Fin 4,
      limbs forms s col i = val (r.getD s 0) i := h

theorem ev_slot (forms : List (List Form)) (col : ℕ → K) (val : Val) (w s : ℕ)
    (h : ∀ i : Fin 4, limbs forms s col i = val w i) : slotE col (forms.getD s []) = ev val w := by
  rw [slotE_limbs, ev, ← h 0, ← h 1, ← h 2]
  rfl

theorem emul_row_ev {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) {a b d c : ℕ}
    (hr : [a, b, d, c] ∈ s.emul) : ev val c = ev val a * ev val b + ev val d := by
  obtain ⟨col, _, hl⟩ := h.emul _ hr
  have := (emul_spec col).1
  rwa [ev_slot _ col val c 3 (hl 3 (by decide)), ev_slot _ col val a 0 (hl 0 (by decide)),
    ev_slot _ col val b 1 (hl 1 (by decide)), ev_slot _ col val d 2 (hl 2 (by decide))] at this

theorem exk_row_ev {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) {a k d c : ℕ}
    (hr : [a, k, d, c] ∈ s.exk) : ev val c = ev val a * emb (val k 0) + ev val d := by
  obtain ⟨col, _, hl⟩ := h.exk _ hr
  have := (exk_spec col).1
  have hk : ((exk.getD 1 []).getD 0 .zero).eval col = val k 0 := hl 1 (by decide) 0
  rwa [ev_slot _ col val c 3 (hl 3 (by decide)), ev_slot _ col val a 0 (hl 0 (by decide)), hk,
    ev_slot _ col val d 2 (hl 2 (by decide))] at this

theorem pub_ev {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) {w : ℕ} {v : Limbs}
    (hp : (w, PubSource.const v) ∈ s.pub) : val w = limbsOf v := h.pub w _ hp

theorem ev_const (c0 c1 c2 : ℕ) (val : Val) (w : ℕ) (h : val w = limbsOf [c0, c1, c2, 0]) :
    ev val w = toE (ofWord c0) (ofWord c1) (ofWord c2) := by
  simp [ev, h, limbsOf]

theorem ev_zero_const (val : Val) (w : ℕ) (h : val w = limbsOf [0, 0, 0, 0]) : ev val w = 0 := by
  rw [ev_const 0 0 0 val w h, ofWord_zero]
  simp [toE, emb_zero]

theorem ev_one_const (val : Val) (w : ℕ) (h : val w = limbsOf [1, 0, 0, 0]) : ev val w = 1 := by
  rw [ev_const 1 0 0 val w h, ofWord_zero, ofWord_one]
  simp [toE, emb]

/-- The state after a fresh `EMUL` row with key `key`. -/
def emulFresh (s : State) (a b d : ℕ) (key : ℕ × ℕ × ℕ × ℕ) : State :=
  { s with next := s.next + 1, emul := s.emul.push [a, b, d, s.next], arith := s.arith.insert key s.next }

theorem emul_run (a b d : ℕ) (s : State) : (emul a b d).run s =
    match s.arith[(Table.emul.tag, emulKey s.units a b d)]? with
    | some c => (c, s)
    | none => (s.next, emulFresh s a b d (Table.emul.tag, emulKey s.units a b d)) := by
  unfold emul
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.run]
  generalize emulKey s.units a b d = k
  obtain ⟨k0, k1, k2⟩ := k
  cases s.arith[(Table.emul.tag, k0, k1, k2)]? <;> rfl


/-- The state after making a new constant. -/
def constFresh (s : State) (kd : Kind) (v : Limbs) : State :=
  { s with next := s.next + 1, pub := s.pub.push (s.next, .const v), consts := s.consts.insert (kd, v) s.next,
           units := unitAfter s.units kd v s.next }

theorem constant_run (kd : Kind) (v : Limbs) (s : State) : (constant kd v).run s =
    match s.consts[(kd, v)]? with
    | some w => (w, s)
    | none => (s.next, constFresh s kd v) := by
  unfold constant
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.run]
  cases s.consts[(kd, v)]? with
  | some w => rfl
  | none =>
    rfl


theorem unitAfter_eZero (u : Units) (kd : Kind) (v : Limbs) (w : ℕ) :
    (unitAfter u kd v w).eZero = if kd = .e ∧ v = [0, 0, 0, 0] then some w else u.eZero := by
  unfold unitAfter; split <;> simp_all

theorem unitAfter_eOne (u : Units) (kd : Kind) (v : Limbs) (w : ℕ) :
    (unitAfter u kd v w).eOne = if kd = .e ∧ v = [1, 0, 0, 0] then some w else u.eOne := by
  unfold unitAfter; split <;> simp_all

theorem unitAfter_kZero (u : Units) (kd : Kind) (v : Limbs) (w : ℕ) :
    (unitAfter u kd v w).kZero = if kd = .k ∧ v = [0, 0, 0, 0] then some w else u.kZero := by
  unfold unitAfter; split <;> simp_all

theorem unitAfter_kOne (u : Units) (kd : Kind) (v : Limbs) (w : ℕ) :
    (unitAfter u kd v w).kOne = if kd = .k ∧ v = [1, 0, 0, 0] then some w else u.kOne := by
  unfold unitAfter; split <;> simp_all

theorem emulKey_congr (u u' : Units) (h : u.eOne = u'.eOne) (a b d : ℕ) : emulKey u a b d = emulKey u' a b d := by
  simp [emulKey, h]

theorem emulKey_fresh (u u' : Units) (w : ℕ) (hu : u.eOne = none) (hu' : u'.eOne = some w) (a b d : ℕ)
    (ha : a ≠ w) (hb : b ≠ w) : emulKey u' a b d = emulKey u a b d := by
  simp [emulKey, hu, hu', Ne.symm ha, Ne.symm hb]


theorem mem_push_of_mem {α : Type} {a : α} {xs : Array α} (b : α) (h : a ∈ xs) : a ∈ xs.push b :=
  Array.mem_push.mpr (Or.inl h)

theorem constFresh_ext (s : State) (kd : Kind) (v : Limbs) : Ext s (constFresh s kd v) :=
  ⟨Nat.le_succ _, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
    fun _ h => mem_push_of_mem _ h⟩

theorem constFresh_inv (s : State) (kd : Kind) (v : Limbs) (hs : Inv s) (hmiss : s.consts[(kd, v)]? = none) :
    Inv (constFresh s kd v) := by
  have hnew : (s.next, PubSource.const v) ∈ (constFresh s kd v).pub := Array.mem_push.mpr (Or.inr rfl)
  have hold : ∀ p ∈ s.pub, p ∈ (constFresh s kd v).pub := fun _ h => mem_push_of_mem _ h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr w hw
    exact Nat.lt_succ_of_lt (hs.emulLt r hr w hw)
  · intro kv w hw
    simp only [constFresh, Std.HashMap.getElem?_insert] at hw
    split at hw
    · rename_i heq
      cases hw
      have : (kd, v) = kv := by simpa using heq
      subst this
      exact hnew
    · exact hold _ (hs.consts kv w hw)
  · intro w hw
    simp only [constFresh, unitAfter_eZero] at hw
    split at hw
    · rename_i hc; cases hw; obtain ⟨_, rfl⟩ := hc; exact hnew
    · exact hold _ (hs.eZero w hw)
  · intro w hw
    simp only [constFresh, unitAfter_eOne] at hw
    simp only [constFresh, Std.HashMap.getElem?_insert]
    split at hw
    · rename_i hc; cases hw; simp [eOneKey, hc.1, hc.2]
    · have := hs.eOne w hw
      split
      · rename_i heq
        have h2 : (kd, v) = eOneKey := by simpa using heq
        rw [h2, this] at hmiss
        cases hmiss
      · exact this
  · intro w hw
    simp only [constFresh, unitAfter_kZero] at hw
    split at hw
    · rename_i hc; cases hw; obtain ⟨_, rfl⟩ := hc; exact hnew
    · exact hold _ (hs.kZero w hw)
  · intro w hw
    simp only [constFresh, unitAfter_kOne] at hw
    split at hw
    · rename_i hc; cases hw; obtain ⟨_, rfl⟩ := hc; exact hnew
    · exact hold _ (hs.kOne w hw)
  · intro k0 k1 k2 c hc
    obtain ⟨a, b, d, hr, hk⟩ := hs.arithE k0 k1 k2 c hc
    refine ⟨a, b, d, hr, ?_⟩
    rw [← hk]
    simp only [constFresh]
    by_cases h1 : kd = .e ∧ v = [1, 0, 0, 0]
    · have hnone : s.units.eOne = none := by
        cases h : s.units.eOne with
        | none => rfl
        | some w =>
          have := hs.eOne w h
          rw [eOneKey, ← h1.1, ← h1.2, hmiss] at this
          cases this
      apply emulKey_fresh _ _ s.next hnone (by rw [unitAfter_eOne, if_pos h1])
      · exact Nat.ne_of_lt (hs.emulLt _ hr a (by simp))
      · exact Nat.ne_of_lt (hs.emulLt _ hr b (by simp))
    · exact emulKey_congr _ _ (by rw [unitAfter_eOne, if_neg h1]) a b d
  · exact hs.arithK
  · intro key c hc
    exact Nat.lt_succ_of_lt (hs.arithLt key c hc)
  · intro kv w hw
    simp only [constFresh, Std.HashMap.getElem?_insert] at hw
    split at hw
    · cases hw; exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hs.constsLt kv w hw)
  · intro p hp
    rcases Array.mem_push.mp hp with hp | rfl
    · exact Nat.lt_succ_of_lt (hs.pubLt p hp)
    · exact Nat.lt_succ_self _

/-- `constant`: its wire's public row holds the constant. -/
theorem constant_good (kd : Kind) (v : Limbs) :
    Good (fun _ => True) (constant kd v) fun _ w s' => w < s'.next ∧ (w, PubSource.const v) ∈ s'.pub := by
  intro s hs _
  rw [constant_run]
  cases h : s.consts[(kd, v)]? with
  | some w => exact ⟨hs, Ext.refl s, hs.constsLt _ w h, hs.consts _ w h⟩
  | none => exact ⟨constFresh_inv s kd v hs h, constFresh_ext s kd v, Nat.lt_succ_self _,
      Array.mem_push.mpr (Or.inr rfl)⟩


/-! Fresh wires and equalities. -/

theorem wire_good : Good (fun _ => True) wire fun s w s' => w = s.next ∧ s'.next = s.next + 1 := by
  intro s hs _
  refine ⟨⟨fun r hr w hw => Nat.lt_succ_of_lt (hs.emulLt r hr w hw), hs.consts, hs.eZero, hs.eOne, hs.kZero, hs.kOne,
    hs.arithE, hs.arithK, fun k c h => Nat.lt_succ_of_lt (hs.arithLt k c h),
    fun k w h => Nat.lt_succ_of_lt (hs.constsLt k w h), fun p h => Nat.lt_succ_of_lt (hs.pubLt p h)⟩,
    ⟨Nat.le_succ _, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
      fun _ h => h⟩, rfl, rfl⟩

theorem union_good (a b : ℕ) : Good (fun _ => True) (union a b) fun _ _ s' => (a, b) ∈ s'.unions := by
  intro s hs _
  exact ⟨⟨hs.emulLt, hs.consts, hs.eZero, hs.eOne, hs.kZero, hs.kOne, hs.arithE, hs.arithK, hs.arithLt,
    hs.constsLt, hs.pubLt⟩, ⟨le_rfl, fun _ h => mem_push_of_mem _ h, fun _ h => h, fun _ h => h, fun _ h => h,
      fun _ h => h, fun _ h => h, fun _ h => h⟩, Array.mem_push.mpr (Or.inr rfl)⟩

/-! `EMUL`. -/

theorem minmax_cases (x d x' d' : ℕ) (h1 : min x d = min x' d') (h2 : max x d = max x' d') :
    (x = x' ∧ d = d') ∨ (x = d' ∧ d = x') := by omega

theorem emulKey_unit (u : Units) (o a b d : ℕ) (ho : u.eOne = some o) (hab : o = a ∨ o = b) :
    emulKey u a b d = (o, min (if o = a then b else a) d, max (if o = a then b else a) d) := by
  have h : u.eOne = some a ∨ u.eOne = some b := by rcases hab with rfl | rfl <;> simp [ho]
  simp only [emulKey, ho, Option.getD_some, Option.some.injEq, if_pos hab]

theorem emulKey_plain (u : Units) (a b d : ℕ) (h : ¬(u.eOne = some a ∨ u.eOne = some b)) :
    emulKey u a b d = (min a b, max a b, d) := by
  simp only [emulKey, if_neg h]

theorem unit_prod (val : Val) (o a b : ℕ) (ho : ev val o = 1) (hab : o = a ∨ o = b) :
    ev val a * ev val b = ev val (if o = a then b else a) := by
  by_cases ha : o = a
  · rw [if_pos ha, ← ha, ho, one_mul]
  · rw [if_neg ha]
    rcases hab with h | h
    · exact absurd h ha
    · rw [← h, ho, mul_one]

/-- Equal `emul_key`s name equal `a·b + d`, the unit being one. -/
theorem emulKey_sem (u : Units) (val : Val) (hone : ∀ o, u.eOne = some o → ev val o = 1) (a b d a' b' d' : ℕ)
    (h : emulKey u a b d = emulKey u a' b' d') :
    ev val a * ev val b + ev val d = ev val a' * ev val b' + ev val d' := by
  by_cases h₁ : u.eOne = some a ∨ u.eOne = some b <;> by_cases h₂ : u.eOne = some a' ∨ u.eOne = some b'
  · obtain ⟨o, ho⟩ : ∃ o, u.eOne = some o := by rcases h₁ with h | h <;> exact ⟨_, h⟩
    have hab : o = a ∨ o = b := by rcases h₁ with h | h <;> rw [ho] at h <;> simp_all
    have hab' : o = a' ∨ o = b' := by rcases h₂ with h | h <;> rw [ho] at h <;> simp_all
    rw [emulKey_unit u o a b d ho hab, emulKey_unit u o a' b' d' ho hab'] at h
    simp only [Prod.mk.injEq] at h
    rw [unit_prod val o a b (hone o ho) hab, unit_prod val o a' b' (hone o ho) hab']
    rcases minmax_cases _ _ _ _ h.2.1 h.2.2 with ⟨hx, hd⟩ | ⟨hx, hd⟩
    · rw [hx, hd]
    · rw [hx, hd, add_comm]
  · exfalso
    obtain ⟨o, ho⟩ : ∃ o, u.eOne = some o := by rcases h₁ with h | h <;> exact ⟨_, h⟩
    have hab : o = a ∨ o = b := by rcases h₁ with h | h <;> rw [ho] at h <;> simp_all
    rw [emulKey_unit u o a b d ho hab, emulKey_plain u a' b' d' h₂] at h
    simp only [Prod.mk.injEq] at h
    apply h₂
    have : o = a' ∨ o = b' := by omega
    rcases this with hm | hm
    · left; rw [ho, hm]
    · right; rw [ho, hm]
  · exfalso
    obtain ⟨o, ho⟩ : ∃ o, u.eOne = some o := by rcases h₂ with h | h <;> exact ⟨_, h⟩
    have hab : o = a' ∨ o = b' := by rcases h₂ with h | h <;> rw [ho] at h <;> simp_all
    rw [emulKey_unit u o a' b' d' ho hab, emulKey_plain u a b d h₁] at h
    simp only [Prod.mk.injEq] at h
    apply h₁
    have : o = a ∨ o = b := by omega
    rcases this with hm | hm
    · left; rw [ho, hm]
    · right; rw [ho, hm]
  · rw [emulKey_plain u a b d h₁, emulKey_plain u a' b' d' h₂] at h
    simp only [Prod.mk.injEq] at h
    rcases minmax_cases _ _ _ _ h.1 h.2.1 with ⟨hx, hd⟩ | ⟨hx, hd⟩
    · rw [hx, hd, h.2.2]
    · rw [hx, hd, h.2.2, mul_comm]

/-- In a satisfying assignment the unit one is one. -/
theorem Inv.one_ev {s : State} (hs : Inv s) {st : ℕ → Fin 4 → K} {val : Val} (h : Sat st s val) :
    ∀ o, s.units.eOne = some o → ev val o = 1 := fun o ho =>
  ev_one_const val o (h.pub o _ (hs.consts eOneKey o (hs.eOne o ho)))

theorem Inv.zero_ev {s : State} (hs : Inv s) {st : ℕ → Fin 4 → K} {val : Val} (h : Sat st s val) :
    ∀ z, s.units.eZero = some z → ev val z = 0 := fun z hz => ev_zero_const val z (h.pub z _ (hs.eZero z hz))

/-- `emul`: `a·b + d`. -/
theorem emul_good (a b d : ℕ) :
    Good (fun s => a < s.next ∧ b < s.next ∧ d < s.next) (emul a b d) fun _ c s' => c < s'.next ∧
      ∀ st val, Sat st s' val → ev val c = ev val a * ev val b + ev val d := by
  intro s hs ⟨ha, hb, hd⟩
  rw [emul_run]
  cases h : s.arith[(Table.emul.tag, emulKey s.units a b d)]? with
  | some c =>
    refine ⟨hs, Ext.refl s, hs.arithLt _ c h, fun st val hsat => ?_⟩
    generalize hk : emulKey s.units a b d = key at h
    obtain ⟨k0, k1, k2⟩ := key
    obtain ⟨a', b', d', hr, hk'⟩ := hs.arithE k0 k1 k2 c h
    rw [emul_row_ev hsat hr]
    exact emulKey_sem s.units val (hs.one_ev hsat) a' b' d' a b d (hk'.trans hk.symm)
  | none =>
    have hrow : [a, b, d, s.next] ∈ (emulFresh s a b d (Table.emul.tag, emulKey s.units a b d)).emul :=
      Array.mem_push.mpr (Or.inr rfl)
    refine ⟨⟨?_, hs.consts, hs.eZero, hs.eOne, hs.kZero, hs.kOne, ?_, ?_, ?_, ?_, ?_⟩,
      ⟨Nat.le_succ _, fun _ h => h, fun _ h => mem_push_of_mem _ h, fun _ h => h, fun _ h => h, fun _ h => h,
        fun _ h => h, fun _ h => h⟩, Nat.lt_succ_self _, fun st val hsat => emul_row_ev hsat hrow⟩
    · intro r hr w hw
      rcases Array.mem_push.mp hr with hr | rfl
      · exact Nat.lt_succ_of_lt (hs.emulLt r hr w hw)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl <;> simp [emulFresh] <;> omega
    · intro k0 k1 k2 c hc
      simp only [emulFresh, Std.HashMap.getElem?_insert] at hc
      split at hc
      · rename_i heq
        cases hc
        refine ⟨a, b, d, hrow, ?_⟩
        have := (beq_iff_eq.mp heq)
        simp only [Prod.mk.injEq] at this
        exact this.2
      · obtain ⟨a', b', d', hr, hk⟩ := hs.arithE k0 k1 k2 c hc
        exact ⟨a', b', d', mem_push_of_mem _ hr, hk⟩
    · intro a' k d' c hc
      simp only [emulFresh, Std.HashMap.getElem?_insert] at hc
      split at hc
      · rename_i heq
        simp [Table.tag] at heq
      · exact hs.arithK a' k d' c hc
    · intro key c hc
      simp only [emulFresh, Std.HashMap.getElem?_insert] at hc
      split at hc
      · cases hc; exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (hs.arithLt key c hc)
    · intro kv w hw
      exact Nat.lt_succ_of_lt (hs.constsLt kv w hw)
    · intro p hp
      exact Nat.lt_succ_of_lt (hs.pubLt p hp)


/-! Constants and units. -/

theorem Good.get' {α : Type} {P : State → Prop} {f : State → M α} {Q : State → α → State → Prop}
    (h : ∀ s₀, Good (fun s => s = s₀ ∧ P s) (f s₀) Q) : Good P (get >>= f) Q := by
  intro s hs hP
  exact h s s hs ⟨rfl, hP⟩

theorem Good.pure' {α : Type} {P : State → Prop} {a : α} {Q : State → α → State → Prop}
    (h : ∀ s, Inv s → P s → Q s a s) : Good P (pure a) Q := by
  intro s hs hP
  exact ⟨hs, Ext.refl s, h s hs hP⟩

theorem Good.pre {α : Type} {P P' : State → Prop} {m : M α} {Q : State → α → State → Prop} (h : Good P m Q)
    (hp : ∀ s, P' s → P s) : Good P' m Q := fun s hs hP => h s hs (hp s hP)

/-- An `E` constant: its wire is the element. -/
theorem eConst_good (c0 c1 c2 : ℕ) : Good (fun _ => True) (eConst c0 c1 c2) fun _ w s' => w < s'.next ∧
    ∀ st val, Sat st s' val → ev val w = toE (ofWord c0) (ofWord c1) (ofWord c2) :=
  (constant_good _ _).weaken (fun _ h => h) fun _ _ _ _ _ _ h =>
    ⟨h.1, fun _ val hsat => ev_const c0 c1 c2 val _ (hsat.pub _ _ h.2)⟩

theorem kConst_good (v : ℕ) : Good (fun _ => True) (kConst v) fun _ w s' => w < s'.next ∧
    ∀ st val, Sat st s' val → val w = limbsOf [v, 0, 0, 0] :=
  (constant_good _ _).weaken (fun _ h => h) fun _ _ _ _ _ _ h => ⟨h.1, fun _ _ hsat => hsat.pub _ _ h.2⟩

theorem dConst_good (v : Limbs) : Good (fun _ => True) (dConst v) fun _ w s' => w < s'.next ∧
    ∀ st val, Sat st s' val → val w = limbsOf v :=
  (constant_good _ _).weaken (fun _ h => h) fun _ _ _ _ _ _ h => ⟨h.1, fun _ _ hsat => hsat.pub _ _ h.2⟩

theorem zero_good : Good (fun _ => True) zero fun _ z s' => z < s'.next ∧
    ∀ st val, Sat st s' val → ev val z = 0 := by
  apply Good.get'
  intro s₀
  cases h : s₀.units.eZero with
  | some w =>
    apply Good.pure'
    rintro s hs ⟨rfl, -⟩
    exact ⟨hs.pubLt _ (hs.eZero w h), fun _ val hsat => hs.zero_ev hsat w h⟩
  | none =>
    refine (eConst_good 0 0 0).weaken (fun _ _ => trivial) fun _ _ _ _ _ _ h => ⟨h.1, fun st val hsat => ?_⟩
    rw [h.2 st val hsat, ofWord_zero]
    simp [toE, emb_zero]

theorem one_good : Good (fun _ => True) one fun _ o s' => o < s'.next ∧
    ∀ st val, Sat st s' val → ev val o = 1 := by
  apply Good.get'
  intro s₀
  cases h : s₀.units.eOne with
  | some w =>
    apply Good.pure'
    rintro s hs ⟨rfl, -⟩
    exact ⟨hs.constsLt _ _ (hs.eOne w h), fun _ val hsat => hs.one_ev hsat w h⟩
  | none =>
    refine (eConst_good 1 0 0).weaken (fun _ _ => trivial) fun _ _ _ _ _ _ h => ⟨h.1, fun st val hsat => ?_⟩
    rw [h.2 st val hsat, ofWord_zero, ofWord_one]
    simp [toE, emb]

theorem kZero_good : Good (fun _ => True) kZero fun _ z s' => z < s'.next ∧
    ∀ st val, Sat st s' val → val z = limbsOf [0, 0, 0, 0] := by
  apply Good.get'
  intro s₀
  cases h : s₀.units.kZero with
  | some w =>
    apply Good.pure'
    rintro s hs ⟨rfl, -⟩
    exact ⟨hs.pubLt _ (hs.kZero w h), fun _ _ hsat => hsat.pub _ _ (hs.kZero w h)⟩
  | none => exact (kConst_good 0).weaken (fun _ _ => trivial) fun _ _ _ _ _ _ h => h


/-! Arithmetic. -/

/-- The wires `ws` are all wires of `s`. -/
def Wires (ws : List ℕ) (s : State) : Prop := ∀ w ∈ ws, w < s.next

theorem Wires.mono {ws : List ℕ} {s s' : State} (h : Wires ws s) (he : Ext s s') : Wires ws s' :=
  fun w hw => lt_of_lt_of_le (h w hw) he.next

theorem add_good (a d : ℕ) : Good (Wires [a, d]) (add a d) fun _ r s' => r < s'.next ∧
    ∀ st val, Sat st s' val → ev val r = ev val a + ev val d := by
  apply Good.get'
  intro s₀
  dsimp only
  split_ifs with h1 h2
  · apply Good.pure'
    rintro s hs ⟨rfl, hw⟩
    exact ⟨hw a (by simp), fun _ val hsat => by rw [hs.zero_ev hsat d h1, add_zero]⟩
  · apply Good.pure'
    rintro s hs ⟨rfl, hw⟩
    exact ⟨hw d (by simp), fun _ val hsat => by rw [hs.zero_ev hsat a h2, zero_add]⟩
  · refine (Good.bind (one_good.pre (P' := fun s => s = s₀ ∧ Wires [a, d] s) fun _ _ => trivial)
      (P₂ := fun o s => Wires [a, o, d] s) ?_ fun o => (emul_good a o d).pre
      fun s h => ⟨h a (by simp), h o (by simp), h d (by simp)⟩).weaken (fun s h => h) ?_
    · rintro s o s' hs ⟨-, hw⟩ ⟨ho, -⟩ he
      intro w hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl | rfl
      · exact (Wires.mono hw he) w (by simp)
      · exact ho
      · exact (Wires.mono hw he) w (by simp)
    · rintro s c s'' hs - - ⟨o, s', ⟨-, hone⟩, -, he', hc, hsem⟩
      refine ⟨hc, fun st val hsat => ?_⟩
      rw [hsem st val hsat, hone st val (hsat.mono he'), mul_one]


theorem mulAdd_good (a b d : ℕ) : Good (Wires [a, b, d]) (mulAdd a b d) fun _ r s' => r < s'.next ∧
    ∀ st val, Sat st s' val → ev val r = ev val a * ev val b + ev val d := by
  apply Good.get'
  intro s₀
  dsimp only
  split_ifs with h1 h2 h3
  · apply Good.pure'
    rintro s hs ⟨rfl, hw⟩
    refine ⟨hw d (by simp), fun _ val hsat => ?_⟩
    rcases h1 with h | h <;> rw [hs.zero_ev hsat _ h] <;> simp
  · refine (add_good a d).pre (fun s h => ?_) |>.weaken (fun s h => h) ?_
    · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> exact h.2 _ (by simp)
    · rintro s r s' hs ⟨rfl, -⟩ he ⟨hr, hsem⟩
      refine ⟨hr, fun st val hsat => ?_⟩
      rw [hsem st val hsat, hs.one_ev (hsat.mono he) b h2, mul_one]
  · refine (add_good b d).pre (fun s h => ?_) |>.weaken (fun s h => h) ?_
    · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> exact h.2 _ (by simp)
    · rintro s r s' hs ⟨rfl, -⟩ he ⟨hr, hsem⟩
      refine ⟨hr, fun st val hsat => ?_⟩
      rw [hsem st val hsat, hs.one_ev (hsat.mono he) a h3, one_mul]
  · exact (emul_good a b d).pre fun s h => ⟨h.2 a (by simp), h.2 b (by simp), h.2 d (by simp)⟩

theorem mul_good (a b : ℕ) : Good (Wires [a, b]) (mul a b) fun _ r s' => r < s'.next ∧
    ∀ st val, Sat st s' val → ev val r = ev val a * ev val b := by
  refine (Good.bind (zero_good.pre (P' := Wires [a, b]) fun _ _ => trivial)
    (P₂ := fun z s => Wires [a, b, z] s ∧ ∀ st val, Sat st s val → ev val z = 0) ?_
    fun z => (mulAdd_good a b z).pre fun s h => h.1).weaken (fun s h => h) ?_
  · rintro s z s' hs hw ⟨hz, hsem⟩ he
    refine ⟨fun w hw' => ?_, hsem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    · exact (hw.mono he) w (by simp)
    · exact (hw.mono he) w (by simp)
    · exact hz
  · rintro s r s'' hs - - ⟨z, s', ⟨-, hz⟩, -, he', hr, hsem⟩
    refine ⟨hr, fun st val hsat => ?_⟩
    rw [hsem st val hsat, hz st val (hsat.mono he'), add_zero]

theorem square_good (a : ℕ) : Good (Wires [a]) (square a) fun _ r s' => r < s'.next ∧
    ∀ st val, Sat st s' val → ev val r = ev val a * ev val a :=
  (mul_good a a).pre fun s h w hw => h w (by simp at hw; simp [hw])


/-- The state after a fresh `EXK` row. -/
def exkFresh (s : State) (a k d : ℕ) : State :=
  { s with next := s.next + 1, exk := s.exk.push [a, k, d, s.next],
           arith := s.arith.insert (Table.exk.tag, a, k, d) s.next }

theorem emb_limb_zero (val : Val) (k : ℕ) (h : val k = limbsOf [0, 0, 0, 0]) : emb (val k 0) = 0 := by
  rw [h]; simp [limbsOf, ofWord_zero, emb_zero]

theorem emb_limb_one (val : Val) (k : ℕ) (h : val k = limbsOf [1, 0, 0, 0]) : emb (val k 0) = 1 := by
  rw [h]; simp [limbsOf, ofWord_one, emb]

theorem mulKAdd_good (a k d : ℕ) : Good (Wires [a, k, d]) (mulKAdd a k d) fun _ r s' => r < s'.next ∧
    ∀ st val, Sat st s' val → ev val r = ev val a * emb (val k 0) + ev val d := by
  apply Good.get'
  intro s₀
  dsimp only
  split_ifs with h1 h2
  · apply Good.pure'
    rintro s hs ⟨rfl, hw⟩
    refine ⟨hw d (by simp), fun _ val hsat => ?_⟩
    rcases h1 with h | h
    · rw [hs.zero_ev hsat _ h]; simp
    · rw [emb_limb_zero val k (hsat.pub _ _ (hs.kZero k h))]; simp
  · refine (add_good a d).pre (fun s h => ?_) |>.weaken (fun s h => h) ?_
    · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> exact h.2 _ (by simp)
    · rintro s r s' hs ⟨rfl, -⟩ he ⟨hr, hsem⟩
      refine ⟨hr, fun st val hsat => ?_⟩
      rw [hsem st val hsat, emb_limb_one val k ((hsat.mono he).pub _ _ (hs.kOne k h2)), mul_one]
  · apply Good.get'
    intro s₁
    cases h : s₁.arith[(Table.exk.tag, a, k, d)]? with
    | some c =>
      apply Good.pure'
      rintro s hs ⟨rfl, -, -⟩
      exact ⟨hs.arithLt _ c h, fun _ val hsat => exk_row_ev hsat (hs.arithK a k d c h)⟩
    | none =>
      rintro s hs ⟨rfl, -, hw⟩
      have hrow : [a, k, d, s.next] ∈ (exkFresh s a k d).exk := Array.mem_push.mpr (Or.inr rfl)
      change Inv (exkFresh s a k d) ∧ Ext s (exkFresh s a k d) ∧ s.next < (exkFresh s a k d).next ∧ _
      refine ⟨⟨fun r hr w hw' => Nat.lt_succ_of_lt (hs.emulLt r hr w hw'), hs.consts, hs.eZero, hs.eOne, hs.kZero,
        hs.kOne, ?_, ?_, ?_, fun kv w hw' => Nat.lt_succ_of_lt (hs.constsLt kv w hw'),
        fun p hp => Nat.lt_succ_of_lt (hs.pubLt p hp)⟩,
        ⟨Nat.le_succ _, fun _ h => h, fun _ h => h, fun _ h => mem_push_of_mem _ h, fun _ h => h, fun _ h => h,
          fun _ h => h, fun _ h => h⟩, Nat.lt_succ_self _, fun st val hsat => exk_row_ev hsat hrow⟩
      · intro k0 k1 k2 c hc
        simp only [exkFresh, Std.HashMap.getElem?_insert] at hc
        split at hc
        · rename_i heq; simp [Table.tag] at heq
        · exact hs.arithE k0 k1 k2 c hc
      · intro a' k' d' c hc
        simp only [exkFresh, Std.HashMap.getElem?_insert] at hc
        split at hc
        · rename_i heq
          cases hc
          have := beq_iff_eq.mp heq
          simp only [Prod.mk.injEq] at this
          obtain ⟨-, rfl, rfl, rfl⟩ := this
          exact hrow
        · exact mem_push_of_mem _ (hs.arithK a' k' d' c hc)
      · intro key c hc
        simp only [exkFresh, Std.HashMap.getElem?_insert] at hc
        split at hc
        · cases hc; exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (hs.arithLt key c hc)

theorem toE_emb (x : K) : toE x 0 0 = emb x := by simp [toE, emb_zero]

theorem mulConstAdd_good (a c0 c1 c2 d : ℕ) : Good (Wires [a, d]) (mulConstAdd a c0 c1 c2 d)
    fun _ r s' => r < s'.next ∧ ∀ st val, Sat st s' val →
      ev val r = ev val a * toE (ofWord c0) (ofWord c1) (ofWord c2) + ev val d := by
  unfold mulConstAdd
  split_ifs with h
  · refine (Good.bind (kConst_good c0 |>.pre (P' := Wires [a, d]) fun _ _ => trivial)
      (P₂ := fun k s => Wires [a, k, d] s ∧ ∀ st val, Sat st s val → val k = limbsOf [c0, 0, 0, 0]) ?_
      fun k => (mulKAdd_good a k d).pre fun s h => h.1).weaken (fun s h => h) ?_
    · rintro s k s' hs hw ⟨hk, hsem⟩ he
      refine ⟨fun w hw' => ?_, hsem⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl | rfl
      · exact (hw.mono he) w (by simp)
      · exact hk
      · exact (hw.mono he) w (by simp)
    · rintro s r s'' hs - - ⟨k, s', ⟨-, hk⟩, -, he', hr, hsem⟩
      refine ⟨hr, fun st val hsat => ?_⟩
      rw [hsem st val hsat, hk st val (hsat.mono he'), h.1, h.2, ofWord_zero, toE_emb]
      simp [limbsOf]
  · refine (Good.bind (eConst_good c0 c1 c2 |>.pre (P' := Wires [a, d]) fun _ _ => trivial)
      (P₂ := fun c s => Wires [a, c, d] s ∧
        ∀ st val, Sat st s val → ev val c = toE (ofWord c0) (ofWord c1) (ofWord c2)) ?_
      fun c => (mulAdd_good a c d).pre fun s h => h.1).weaken (fun s h => h) ?_
    · rintro s c s' hs hw ⟨hc, hsem⟩ he
      refine ⟨fun w hw' => ?_, hsem⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl | rfl
      · exact (hw.mono he) w (by simp)
      · exact hc
      · exact (hw.mono he) w (by simp)
    · rintro s r s'' hs - - ⟨c, s', ⟨-, hc⟩, -, he', hr, hsem⟩
      refine ⟨hr, fun st val hsat => ?_⟩
      rw [hsem st val hsat, hc st val (hsat.mono he')]


theorem eqConstE_good (a c0 c1 c2 : ℕ) : Good (fun _ => True) (eqConstE a c0 c1 c2) fun _ _ s' =>
    ∀ st val, Sat st s' val → ev val a = toE (ofWord c0) (ofWord c1) (ofWord c2) := by
  refine (Good.bind (eConst_good c0 c1 c2) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
    fun c => union_good a c).weaken (fun s h => h) ?_
  rintro s _ s'' hs - - ⟨c, s', ⟨-, hc⟩, -, he', hu⟩
  intro st val hsat
  have : val a = val c := hsat.unions _ hu
  rw [ev, this, ← ev, hc st val (hsat.mono he')]

theorem eqConstK_good (a v : ℕ) : Good (fun _ => True) (eqConstK a v) fun _ _ s' =>
    ∀ st val, Sat st s' val → val a = limbsOf [v, 0, 0, 0] := by
  refine (Good.bind (kConst_good v) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
    fun c => union_good a c).weaken (fun s h => h) ?_
  rintro s _ s'' hs - - ⟨c, s', ⟨-, hc⟩, -, he', hu⟩
  intro st val hsat
  rw [hsat.unions _ hu, hc st val (hsat.mono he')]

/-- `inv`: a hint `i` with `a·i = 1`. -/
theorem inv_good (a : ℕ) : Good (Wires [a]) (inv a) fun _ i s' => i < s'.next ∧
    ∀ st val, Sat st s' val → ev val a * ev val i = 1 := by
  refine (Good.bind (wire_good.pre (P' := Wires [a]) fun _ _ => trivial) (P₂ := fun i s => Wires [a, i] s) ?_
    fun i => Good.bind ((mul_good a i).pre (P' := Wires [a, i]) fun _ h => h)
      (P₂ := fun p s => Wires [i] s ∧ True) (fun _ _ _ _ h _ he => ⟨fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact (Wires.mono h he) w (by simp), trivial⟩)
      fun p => Good.bind ((eqConstE_good p 1 0 0).pre fun _ _ => trivial) (P₂ := fun _ s => Wires [i] s)
        (fun _ _ _ _ h _ he => Wires.mono h.1 he) fun _ => Good.pure' (Q := fun _ r s' => r = i ∧ r < s'.next)
          fun s _ h => ⟨rfl, h i (by simp)⟩).weaken (fun s h => h) ?_
  · rintro s i s' hs hw ⟨rfl, hn⟩ he
    intro w hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl
    · exact (hw.mono he) w (by simp)
    · rw [hn]; exact Nat.lt_succ_self _
  · rintro s i s4 hs - - ⟨i', s1, -, -, he1, p, s2, ⟨-, hp⟩, -, he2, u, s3, hc, -, he3, rfl, hi⟩
    refine ⟨hi, fun st val hsat => ?_⟩
    rw [← hp st val (hsat.mono he2), hc st val (hsat.mono he3), ofWord_zero, ofWord_one]
    simp [toE, emb]


theorem foldl_add_good (ts : List ℕ) : ∀ acc, Good (Wires (acc :: ts)) (ts.foldlM add acc) fun _ r s' =>
    r < s'.next ∧ ∀ st val, Sat st s' val → ev val r = ev val acc + (ts.map (ev val)).sum := by
  induction ts with
  | nil =>
    intro acc
    exact Good.pure' fun s _ h => ⟨h acc (by simp), fun _ _ _ => by simp⟩
  | cons t ts ih =>
    intro acc
    rw [List.foldlM_cons]
    refine (Good.bind ((add_good acc t).pre (P' := Wires (acc :: t :: ts)) fun s h w hw => h w (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> simp))
      (P₂ := fun r s => Wires (r :: ts) s) ?_ fun r => ih r).weaken (fun s h => h) ?_
    · rintro s r s' hs hw ⟨hr, -⟩ he w hw'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · exact hr
      · exact (hw.mono he) w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw'))
    · rintro s r s'' hs - - ⟨r', s', ⟨-, h1⟩, -, he', hr, h2⟩
      refine ⟨hr, fun st val hsat => ?_⟩
      rw [h2 st val hsat, h1 st val (hsat.mono he'), List.map_cons, List.sum_cons, add_assoc]

/-- `sum`: the terms' sum. -/
theorem sum_good (ts : List ℕ) : Good (Wires ts) (sum ts) fun _ r s' => r < s'.next ∧
    ∀ st val, Sat st s' val → ev val r = (ts.map (ev val)).sum := by
  refine (Good.bind (zero_good.pre (P' := Wires ts) fun _ _ => trivial)
    (P₂ := fun z s => Wires (z :: ts) s ∧ ∀ st val, Sat st s val → ev val z = 0) ?_
    fun z => (foldl_add_good ts z).pre fun s h => h.1).weaken (fun s h => h) ?_
  · rintro s z s' hs hw ⟨hz, hsem⟩ he
    refine ⟨fun w hw' => ?_, hsem⟩
    rcases List.mem_cons.mp hw' with rfl | hw'
    · exact hz
    · exact (hw.mono he) w hw'
  · rintro s r s'' hs - - ⟨z, s', ⟨-, hz⟩, -, he', hr, hsem⟩
    refine ⟨hr, fun st val hsat => ?_⟩
    rw [hsem st val hsat, hz st val (hsat.mono he'), zero_add]


/-! Bits and views. -/

/-- `mapM` of steps each giving a wire satisfying `R`, from states satisfying a stable `P`. -/
theorem mapM_good {β : Type} (P : State → Prop) (hP : ∀ s s', P s → Ext s s' → P s') (f : β → M ℕ)
    (R : β → ℕ → Prop) (hf : ∀ x, Good P (f x) fun _ y s' => R x y ∧ y < s'.next) :
    ∀ l : List β, Good P (l.mapM f) fun _ ys s' =>
      ys.length = l.length ∧ (∀ i (hi : i < l.length) (hy : i < ys.length), R l[i] ys[i]) ∧ Wires ys s' := by
  intro l
  induction l with
  | nil => exact Good.pure' fun _ _ _ => ⟨rfl, fun i hi => absurd hi (by simp), fun _ h => absurd h (by simp)⟩
  | cons x xs ih =>
    rw [List.mapM_cons]
    refine (Good.bind (hf x) (P₂ := fun _ s => P s) (fun _ _ _ _ h _ he => hP _ _ h he) fun y =>
      Good.bind ih (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun ys =>
        Good.pure' (Q := fun _ r s' => r = y :: ys) fun _ _ _ => rfl).weaken (fun s h => h) ?_
    rintro s r s3 hs - - ⟨y, s1, ⟨hR, hy⟩, -, he1, ys, s2, ⟨hlen, hRs, hw⟩, -, he2, rfl⟩
    refine ⟨by simp [hlen], fun i hi hy' => ?_, fun w hw' => ?_⟩
    · cases i with
      | zero => exact hR
      | succ i => exact hRs i (by simpa using hi) (by simpa using hy')
    · rcases List.mem_cons.mp hw' with rfl | hw'
      · exact lt_of_lt_of_le hy he1.next
      · exact lt_of_lt_of_le (hw w hw') he2.next

theorem fresh_good : Good (fun _ => True) wire fun _ y s' => True ∧ y < s'.next :=
  wire_good.weaken (fun _ h => h) fun s y s' _ _ _ ⟨h1, h2⟩ => ⟨trivial, by rw [h2, h1]; exact Nat.lt_succ_self _⟩

theorem row_good (t : Table) (r : List ℕ) (ht : t ≠ .emul) :
    Good (fun _ => True) (row t r) fun _ _ s' => (t = .exk → r ∈ s'.exk) ∧ (t = .hash → r ∈ s'.hash) ∧
      (t = .split → r ∈ s'.split) ∧ (t = .cast → r ∈ s'.cast) := by
  intro s hs _
  have hpush : ∀ {xs : Array (List ℕ)} {y : List ℕ}, y ∈ xs → y ∈ xs.push r := fun h => mem_push_of_mem _ h
  have hnew : ∀ {xs : Array (List ℕ)}, r ∈ xs.push r := Array.mem_push.mpr (Or.inr rfl)
  cases t with
  | emul => exact absurd rfl ht
  | exk | hash | split | cast | pub =>
    refine ⟨⟨hs.emulLt, hs.consts, hs.eZero, hs.eOne, hs.kZero, hs.kOne, hs.arithE, ?_, hs.arithLt, hs.constsLt,
      hs.pubLt⟩, ⟨le_rfl, fun _ h => h, fun _ h => h, ?_, ?_, ?_, ?_, fun _ h => h⟩, ?_⟩ <;>
      first
        | exact fun a k d c h => hpush (hs.arithK a k d c h)
        | exact hs.arithK
        | exact fun _ h => hpush h
        | exact fun _ h => h
        | (simp [row]; exact hnew)
        | simp [row]

/-- `cast_row`: a `CAST` row holding the given wires at their slots and fresh ones elsewhere. -/
theorem castRow_good (given : List (ℕ × ℕ)) : Good (Wires (given.map (·.2))) (castRow given) fun _ ws s' =>
    ws.length = 8 ∧ (∀ i (hw : i < ws.length), ∀ p, given.find? (·.1 = i) = some p → ws[i] = p.2) ∧
      ws ∈ s'.cast ∧ Wires ws s' := by
  have hstep : ∀ i : ℕ, Good (Wires (given.map (·.2)))
      (match given.find? (·.1 = i) with
        | some (_, w) => pure w
        | none => wire) fun _ y s' => (∀ p, given.find? (·.1 = i) = some p → y = p.2) ∧ y < s'.next := by
    intro i
    cases h : given.find? (·.1 = i) with
    | some p =>
      obtain ⟨j, w⟩ := p
      exact Good.pure' fun s _ hw => ⟨fun p hp => by cases hp; rfl,
        hw w (List.mem_map.mpr ⟨(j, w), List.mem_of_find?_eq_some h, rfl⟩)⟩
    | none =>
      exact fresh_good.pre (fun _ _ => trivial) |>.weaken (fun s h => h) fun _ _ _ _ _ _ hy =>
        ⟨fun p hp => (by simp at hp), hy.2⟩
  refine (Good.bind (mapM_good _ (fun _ _ h he => Wires.mono h he) _ _ hstep (List.range 8))
    (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun ws =>
      Good.bind (row_good .cast ws (by decide)) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
        fun _ => Good.pure' (Q := fun _ r s' => r = ws) fun _ _ _ => rfl).weaken (fun s h => h) ?_
  rintro s r s3 hs - - ⟨ws, s1, ⟨hlen, hR, hw⟩, -, he1, u, s2, ⟨-, -, -, hc⟩, -, he2, rfl⟩
  refine ⟨by simpa using hlen, fun i hi p hp => ?_, he2.cast _ (hc rfl), hw.mono he1⟩
  have := hR i (by simpa [hlen] using hi) hi
  simp only [List.getElem_range] at this
  exact this p hp


/-- A `CAST` row's wires: a digest's four words, the element of the first three, the two halves, the four words. -/
theorem cast_sem {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) {ws : List ℕ}
    (hr : ws ∈ s.cast) : ∃ col : ℕ → K, (∀ i : Fin 4, val (ws.getD 0 0) i = col i) ∧
      (∀ i : Fin 4, i.val < 3 → val (ws.getD 1 0) i = col i) ∧
      (val (ws.getD 2 0) 0 = col 0 ∧ val (ws.getD 2 0) 1 = col 1 ∧ val (ws.getD 2 0) 2 = 0) ∧
      (val (ws.getD 3 0) 0 = col 2 ∧ val (ws.getD 3 0) 1 = col 3 ∧ val (ws.getD 3 0) 2 = 0) ∧
      ∀ w : Fin 4, val (ws.getD (4 + w) 0) 0 = col w := by
  obtain ⟨col, -, hl⟩ := h.cast _ hr
  obtain ⟨h0, h1, -, ⟨h20, h21, h22, -⟩, ⟨h30, h31, h32, -⟩, h4⟩ := cast_views col
  simp only [castDigest, castElement, castHalves, castWords] at h0 h1 h20 h21 h22 h30 h31 h32 h4
  have hc : Rec.cast.length = 8 := rfl
  refine ⟨col, fun i => ?_, fun i hi => ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, fun w => ?_⟩
  · rw [← hl 0 (by rw [hc]; omega) i, h0 i]
  · rw [← hl 1 (by rw [hc]; omega) i]; exact h1 ⟨i, hi⟩
  · rw [← hl 2 (by rw [hc]; omega) 0]; exact h20
  · rw [← hl 2 (by rw [hc]; omega) 1]; exact h21
  · rw [← hl 2 (by rw [hc]; omega) 2]; exact h22
  · rw [← hl 3 (by rw [hc]; omega) 0]; exact h30
  · rw [← hl 3 (by rw [hc]; omega) 1]; exact h31
  · rw [← hl 3 (by rw [hc]; omega) 2]; exact h32
  · rw [← hl (4 + w) (by rw [hc]; omega) 0]; exact h4 w


theorem given_getD {given : List (ℕ × ℕ)} {ws : List ℕ} (hlen : ws.length = 8)
    (hR : ∀ i (hw : i < ws.length), ∀ p, given.find? (·.1 = i) = some p → ws[i] = p.2) (j w : ℕ) (hj : j < 8)
    (hf : given.find? (·.1 = j) = some (j, w)) : ws.getD j 0 = w := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact hR j (by omega) _ hf

/-- A view of `CAST` rows: `m` makes one row from the given wires and returns `out` of it. -/
theorem view_good {α : Type} (given : List (ℕ × ℕ)) (out : List ℕ → α) (Q : State → α → State → Prop)
    (hQ : ∀ ws s', ws.length = 8 → ws ∈ s'.cast → Wires ws s' →
      (∀ j w, j < 8 → given.find? (·.1 = j) = some (j, w) → ws.getD j 0 = w) → Q s' (out ws) s') :
    Good (Wires (given.map (·.2))) (do let w ← castRow given; pure (out w)) fun _ r s' => Q s' r s' := by
  refine (Good.bind (castRow_good given) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun ws =>
    Good.pure' (Q := fun _ r s' => r = out ws) fun _ _ _ => rfl).weaken (fun s h => h) ?_
  rintro s r s2 hs - - ⟨ws, s1, ⟨hlen, hR, hc, hw⟩, -, he, rfl⟩
  exact hQ ws s2 hlen (he.cast _ hc) (hw.mono he) fun j w hj hf => given_getD hlen hR j w hj hf


theorem wires_getD {ws : List ℕ} {s : State} (hw : Wires ws s) (hlen : ws.length = 8) (j : ℕ) (hj : j < 8) :
    ws.getD j 0 < s.next := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact hw _ (List.getElem_mem _)

theorem eToK_good (e : ℕ) : Good (Wires [e]) (eToK e) fun _ ks s' => (∀ i < 3, ks.getD i 0 < s'.next) ∧
    ∀ st val, Sat st s' val → ∀ i : Fin 4, i.val < 3 → val (ks.getD i 0) 0 = val e i := by
  unfold eToK
  refine (view_good [(1, e)] (fun w => (w.drop 4).take 3) (fun s' ks _ => (∀ i < 3, ks.getD i 0 < s'.next) ∧
    ∀ st val, Sat st s' val → ∀ i : Fin 4, i.val < 3 → val (ks.getD i 0) 0 = val e i) ?_).pre
    fun _ h => by simpa using h
  intro ws s' hlen hc hw hg
  have hd : ∀ i < 3, ((ws.drop 4).take 3).getD i 0 = ws.getD (4 + i) 0 := by
    intro i hi; simp [List.getD_eq_getElem?_getD, hi, List.getElem?_drop]
  refine ⟨fun i hi => by rw [hd i hi]; exact wires_getD hw hlen _ (by omega), fun st val hsat i hi => ?_⟩
  obtain ⟨col, -, h1, -, -, h4⟩ := cast_sem hsat hc
  rw [hd i hi, h4 i, ← hg 1 e (by omega) (by simp)]
  exact (h1 i hi).symm

theorem kToE_good (k0 k1 k2 : ℕ) : Good (Wires [k0, k1, k2]) (kToE k0 k1 k2) fun _ r s' => r < s'.next ∧
    ∀ st val, Sat st s' val → ev val r = toE (val k0 0) (val k1 0) (val k2 0) := by
  unfold kToE
  refine (view_good [(4, k0), (5, k1), (6, k2)] (fun w => w.getD 1 0) (fun s' r _ => r < s'.next ∧
    ∀ st val, Sat st s' val → ev val r = toE (val k0 0) (val k1 0) (val k2 0)) ?_).pre
    fun _ h => by simpa using h
  intro ws s' hlen hc hw hg
  refine ⟨wires_getD hw hlen 1 (by omega), fun st val hsat => ?_⟩
  obtain ⟨col, -, h1, -, -, h4⟩ := cast_sem hsat hc
  have e0 : val (ws.getD 4 0) 0 = col 0 := h4 0
  have e1 : val (ws.getD 5 0) 0 = col 1 := h4 1
  have e2 : val (ws.getD 6 0) 0 = col 2 := h4 2
  rw [hg 4 k0 (by omega) (by simp)] at e0
  rw [hg 5 k1 (by omega) (by simp)] at e1
  rw [hg 6 k2 (by omega) (by simp)] at e2
  simp only [ev]
  rw [h1 0 (by simp), h1 1 (by simp), h1 2 (by simp), e0, e1, e2]
  rfl

theorem kToE1_good (k : ℕ) : Good (Wires [k]) (kToE1 k) fun _ r s' => r < s'.next ∧
    ∀ st val, Sat st s' val → ev val r = emb (val k 0) := by
  refine (Good.bind (kZero_good.pre (P' := Wires [k]) fun _ _ => trivial)
    (P₂ := fun z s => Wires [k, z, z] s ∧ ∀ st val, Sat st s val → val z = limbsOf [0, 0, 0, 0]) ?_
    fun z => (kToE_good k z z).pre fun s h => h.1).weaken (fun s h => h) ?_
  · rintro s z s' hs hw ⟨hz, hsem⟩ he
    refine ⟨fun w hw' => ?_, hsem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    · exact (hw.mono he) w (by simp)
    · exact hz
    · exact hz
  · rintro s r s'' hs - - ⟨z, s', ⟨-, hz⟩, -, he', hr, hsem⟩
    refine ⟨hr, fun st val hsat => ?_⟩
    rw [hsem st val hsat, hz st val (hsat.mono he')]
    simp [limbsOf, ofWord_zero, toE_emb]

theorem dToK_good (d : ℕ) : Good (Wires [d]) (dToK d) fun _ ks s' => (∀ i < 4, ks.getD i 0 < s'.next) ∧
    ∀ st val, Sat st s' val → ∀ i : Fin 4, val (ks.getD i 0) 0 = val d i := by
  unfold dToK
  refine (view_good [(0, d)] (fun w => w.drop 4) (fun s' ks _ => (∀ i < 4, ks.getD i 0 < s'.next) ∧
    ∀ st val, Sat st s' val → ∀ i : Fin 4, val (ks.getD i 0) 0 = val d i) ?_).pre fun _ h => by simpa using h
  intro ws s' hlen hc hw hg
  have hd : ∀ i, (ws.drop 4).getD i 0 = ws.getD (4 + i) 0 := by
    intro i; simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  refine ⟨fun i hi => by rw [hd i]; exact wires_getD hw hlen _ (by omega), fun st val hsat i => ?_⟩
  obtain ⟨col, h0, -, -, -, h4⟩ := cast_sem hsat hc
  rw [hd i, h4 i, ← hg 0 d (by omega) (by simp), h0 i]

theorem dToEAndK_good (d : ℕ) : Good (Wires [d]) (dToEAndK d) fun _ r s' => r.1 < s'.next ∧ r.2 < s'.next ∧
    ∀ st val, Sat st s' val → (∀ i : Fin 4, i.val < 3 → val r.1 i = val d i) ∧ val r.2 0 = val d 3 := by
  unfold dToEAndK
  refine (view_good [(0, d)] (fun w => (w.getD 1 0, w.getD 7 0)) (fun s' r _ => r.1 < s'.next ∧ r.2 < s'.next ∧
    ∀ st val, Sat st s' val → (∀ i : Fin 4, i.val < 3 → val r.1 i = val d i) ∧ val r.2 0 = val d 3) ?_).pre
    fun _ h => by simpa using h
  intro ws s' hlen hc hw hg
  refine ⟨wires_getD hw hlen 1 (by omega), wires_getD hw hlen 7 (by omega), fun st val hsat => ?_⟩
  obtain ⟨col, h0, h1, -, -, h4⟩ := cast_sem hsat hc
  have hd := hg 0 d (by omega) (by simp)
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [h1 i hi, ← hd, h0 i]
  · rw [show (7 : ℕ) = 4 + ((3 : Fin 4) : ℕ) from rfl, h4 3, ← hd, h0 3]

theorem halvesToD_good (lo hi : ℕ) : Good (Wires [lo, hi]) (halvesToD lo hi) fun _ r s' => r < s'.next ∧
    ∀ st val, Sat st s' val → val r 0 = val lo 0 ∧ val r 1 = val lo 1 ∧ val r 2 = val hi 0 ∧ val r 3 = val hi 1 ∧
      val lo 2 = 0 ∧ val hi 2 = 0 := by
  unfold halvesToD
  refine (view_good [(2, lo), (3, hi)] (fun w => w.getD 0 0) (fun s' r _ => r < s'.next ∧
    ∀ st val, Sat st s' val → val r 0 = val lo 0 ∧ val r 1 = val lo 1 ∧ val r 2 = val hi 0 ∧ val r 3 = val hi 1 ∧
      val lo 2 = 0 ∧ val hi 2 = 0) ?_).pre fun _ h => by simpa using h
  intro ws s' hlen hc hw hg
  refine ⟨wires_getD hw hlen 0 (by omega), fun st val hsat => ?_⟩
  obtain ⟨col, h0, -, ⟨h20, h21, h22⟩, ⟨h30, h31, h32⟩, -⟩ := cast_sem hsat hc
  rw [hg 2 lo (by omega) (by simp)] at h20 h21 h22
  rw [hg 3 hi (by omega) (by simp)] at h30 h31 h32
  exact ⟨by rw [h0 0, h20]; rfl, by rw [h0 1, h21]; rfl, by rw [h0 2, h30]; rfl, by rw [h0 3, h31]; rfl, h22, h32⟩


theorem limbs_split (j : ℕ) (hj : j < 65) (col : ℕ → K) : limbs Rec.split j col 0 = col j := by
  unfold limbs Rec.split
  have : (List.map kSlot (List.range 65)).getD j [] = kSlot j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl
  rw [this]
  rfl

theorem num_congr (c c' : ℕ → ZMod 2) (m : ℕ) (h : ∀ i < m, c i = c' i) : num c m = num c' m := by
  induction m generalizing c c' with
  | zero => rfl
  | succ m ih =>
    simp only [num]
    rw [h 0 (by omega), ih (fun i => c (i + 1)) (fun i => c' (i + 1)) fun i hi => h (i + 1) (by omega)]

/-- A `SPLIT` row's wires: the word's bits, Boolean, spelling it. -/
theorem split_sem {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) {r : List ℕ}
    (hr : r ∈ s.split) : (∀ i < 64, val (r.getD (1 + i) 0) 0 = 0 ∨ val (r.getD (1 + i) 0) 0 = 1) ∧
      toWord (val (r.getD 0 0) 0) = num (fun i => if val (r.getD (1 + i) 0) 0 = 1 then 1 else 0) 64 := by
  obtain ⟨col, hid, hl⟩ := h.split _ hr
  have hc : ∀ j < 65, col j = val (r.getD j 0) 0 := fun j hj => by
    rw [← limbs_split j hj col]; exact hl j (by simpa [Rec.split] using hj) 0
  obtain ⟨hb, hw⟩ := split_spec col hid
  refine ⟨fun i hi => by rw [← hc (1 + i) (by omega)]; exact hb i hi, ?_⟩
  rw [← hc 0 (by omega), hw]
  apply num_congr
  intro i hi
  unfold bitsOf
  rw [hc (1 + i) (by omega)]


theorem splitRow_good (w : ℕ) (bits : List ℕ) : Good (fun _ => True) (splitRow w bits) fun _ _ s' =>
    (w :: bits) ∈ s'.split :=
  (row_good .split (w :: bits) (by decide)).weaken (fun _ h => h) fun _ _ _ _ _ _ h => h.2.2.1 rfl

/-- `split`: 64 Boolean wires spelling the word. -/
theorem split_good (w : ℕ) : Good (fun _ => True) (split w) fun _ bits s' => bits.length = 64 ∧ Wires bits s' ∧
    ∀ st val, Sat st s' val → (∀ i < 64, val (bits.getD i 0) 0 = 0 ∨ val (bits.getD i 0) 0 = 1) ∧
      toWord (val w 0) = num (fun i => if val (bits.getD i 0) 0 = 1 then 1 else 0) 64 := by
  refine (Good.bind (mapM_good _ (fun _ _ h _ => h) _ (fun _ _ => True) (fun _ => fresh_good) (List.range 64))
    (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun bits =>
      Good.bind (splitRow_good w bits) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun _ =>
        Good.pure' (Q := fun _ r _ => r = bits) fun _ _ _ => rfl).weaken (fun s h => h) ?_
  rintro s r s2 hs - - ⟨bits, s1, ⟨hlen, -, hw⟩, -, he1, u, s1', hrow, -, he2, rfl⟩
  refine ⟨by simpa using hlen, hw.mono he1, fun st val hsat => ?_⟩
  obtain ⟨hb, hword⟩ := split_sem (hsat.mono he2) hrow
  simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_comm 1] at hb hword
  exact ⟨hb, hword⟩

/-- `pack`: the word the bits spell, the bits past them zero. -/
theorem pack_good (bits : List ℕ) : Good (Wires bits) (pack bits) fun _ w s' => w < s'.next ∧
    ∀ st val, Sat st s' val → (∀ i < 64, i < bits.length → val (bits.getD i 0) 0 = 0 ∨ val (bits.getD i 0) 0 = 1) ∧
      toWord (val w 0) = num (fun i => if i < bits.length ∧ val (bits.getD i 0) 0 = 1 then 1 else 0) 64 := by
  refine (Good.bind (kZero_good.pre (P' := Wires bits) fun _ _ => trivial)
    (P₂ := fun z s => ∀ st val, Sat st s val → val z = limbsOf [0, 0, 0, 0]) (fun _ _ _ _ _ h _ => h.2)
    fun z => Good.bind (fresh_good.pre fun _ _ => trivial) (P₂ := fun _ _ => True)
      (fun _ _ _ _ _ _ _ => trivial) fun w =>
        Good.bind (splitRow_good w (bits ++ List.replicate (64 - bits.length) z)) (P₂ := fun _ _ => True)
          (fun _ _ _ _ _ _ _ => trivial) fun _ =>
            Good.pure' (Q := fun _ r s' => r = w) fun _ _ _ => rfl).weaken (fun s h => h) ?_
  rintro s r s3 hs - - ⟨z, s1, ⟨-, hz⟩, -, he1, w, s2, ⟨-, hwl⟩, -, he2, u, s2', hrow, -, he3, rfl⟩
  refine ⟨lt_of_lt_of_le hwl he2.next, fun st val hsat => ?_⟩
  obtain ⟨hb, hword⟩ := split_sem (hsat.mono he3) hrow
  have hzv : val z 0 = 0 := by rw [hz st val (hsat.mono he1)]; simp [limbsOf, ofWord_zero]
  have hget : ∀ i < 64, (bits ++ List.replicate (64 - bits.length) z).getD i 0 =
      if i < bits.length then bits.getD i 0 else z := by
    intro i hi
    split_ifs with h
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_of_not_gt h), List.getElem?_replicate]
      rw [if_pos (by omega)]
      rfl
  simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_comm 1] at hb hword
  refine ⟨fun i hi hl => ?_, ?_⟩
  · have := hb i hi; rwa [hget i hi, if_pos hl] at this
  · rw [hword]
    apply num_congr
    intro i hi
    rw [hget i hi]
    by_cases hl : i < bits.length
    · simp [hl]
    · simp [hl, hzv]


/-! Hashing. -/

theorem limbs_hash_word (i : ℕ) (hi : i < 8) (col : ℕ → K) : limbs Rec.hash (8 + i) col 0 = col (hashM + i) := by
  unfold limbs Rec.hash
  have : ([dSlot hashH, [.col hashT, .col hashF, .zero, .zero], (List.range 4).map muxLimb, kSlot hashSel,
      eSlot (hashM + 4), kSlot (hashM + 7), dSlot hashO, eSlot hashO] ++
      (List.range 8).map fun i => kSlot (hashM + i)).getD (8 + i) [] = kSlot (hashM + i) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.getElem?_map]
    simp [List.getElem?_range hi]
  rw [this]
  rfl

/-- A `HASH` row's wires: its columns are the chaining value's, counter's, mux bit's, `x`'s, `ds`'s, output's and
message words' limbs, and its mux slot carries the mux wire. -/
theorem hash_sem {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val)
    {hw tf mux bit x ds o ch : ℕ} {words : List ℕ}
    (hr : ([hw, tf, mux, bit, x, ds, o, ch] ++ words) ∈ s.hash) : ∃ col, HashRow col ∧
      (∀ i : Fin 4, col (hashH + i) = val hw i) ∧ col hashT = val tf 0 ∧ col hashF = val tf 1 ∧
      (∀ i : Fin 4, limbs Rec.hash hashSlotMux col i = val mux i) ∧ col hashSel = val bit 0 ∧
      (∀ i : Fin 4, i.val < 3 → col (hashM + 4 + i) = val x i) ∧ col (hashM + 7) = val ds 0 ∧
      (∀ i : Fin 4, col (hashO + i) = val o i) ∧ ∀ i < 8, col (hashM + i) = val (words.getD i 0) 0 := by
  obtain ⟨col, hrow, hl⟩ := h.hash _ hr
  have hn : Rec.hash.length = 16 := rfl
  have hsl : ∀ j < 16, ∀ i : Fin 4, limbs Rec.hash j col i =
      val (([hw, tf, mux, bit, x, ds, o, ch] ++ words).getD j 0) i := fun j hj i => hl j (by rw [hn]; exact hj) i
  refine ⟨col, hrow, fun i => ?_, ?_, ?_, fun i => hsl 2 (by omega) i, ?_, fun i hi => ?_, ?_, fun i => ?_,
    fun i hi => ?_⟩
  · have := hsl 0 (by omega) i; fin_cases i <;> exact this
  · exact hsl 1 (by omega) 0
  · exact hsl 1 (by omega) 1
  · exact hsl 3 (by omega) 0
  · have := hsl 4 (by omega) i; fin_cases i <;> first | exact this | simp at hi
  · exact hsl 5 (by omega) 0
  · have := hsl 6 (by omega) i; fin_cases i <;> exact this
  · have h8 : limbs Rec.hash (8 + i) col 0 = _ := hsl (8 + i) (by omega) 0
    rw [limbs_hash_word i hi col] at h8
    rw [h8]
    have : ([hw, tf, mux, bit, x, ds, o, ch] ++ words).getD (8 + i) 0 = words.getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp
    rw [this]


theorem columnWord_ofWord (col : ℕ → K) (c : ℕ) (b : BitVec 64) (h : col c = ofWord b.toNat) :
    columnWord col c = b := by
  rw [columnWord, h, toWord_ofWord _ b.isLt]
  simp

theorem hashRow_good (hw tf mux bit x ds : ℕ) (words : List ℕ) :
    Good (fun _ => True) (hashRow hw tf mux bit x ds words) fun _ o s' => o < s'.next ∧
      ∃ ch, ([hw, tf, mux, bit, x, ds, o, ch] ++ words) ∈ s'.hash := by
  refine (Good.bind fresh_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun o =>
    Good.bind fresh_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun ch =>
      Good.bind (row_good .hash ([hw, tf, mux, bit, x, ds, o, ch] ++ words) (by decide)) (P₂ := fun _ _ => True)
        (fun _ _ _ _ _ _ _ => trivial) fun _ => Good.pure' (Q := fun _ r _ => r = o) fun _ _ _ => rfl).weaken
    (fun s h => h) ?_
  rintro s r s4 hs - - ⟨o, s1, ⟨-, ho⟩, -, he1, ch, s2, -, -, he2, u, s3, ⟨-, hrow, -⟩, -, he3, rfl⟩
  exact ⟨lt_of_lt_of_le ho he1.next, ch, he3.hash _ (hrow rfl)⟩

/-- `single_block`'s row: from the parameter IV at counter 64, final, its mux slot `mux`, its bit `bit`, `x` and `ds`
in its message's second half. -/
def SingleSem (val : Val) (mux bit x ds o : ℕ) : Prop :=
  ∃ col, NodeRow col (val mux) ∧ col hashSel = val bit 0 ∧ (∀ i : Fin 4, i.val < 3 → col (hashM + 4 + i) = val x i) ∧
    col (hashM + 7) = val ds 0 ∧ outWords col = words4 (val o)

theorem singleBlock_good (mux bit x ds : ℕ) : Good (fun _ => True) (singleBlock mux bit x ds) fun _ o s' =>
    o < s'.next ∧ ∀ st val, Sat st s' val → SingleSem val mux bit x ds o := by
  refine (Good.bind (dConst_good paramIVLimbs) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun hw =>
    Good.bind (dConst_good [64, final, 0, 0]) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun tf =>
      Good.bind (mapM_good _ (fun _ _ h _ => h) _ (fun _ _ => True) (fun _ => fresh_good) (List.range 8))
        (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun words =>
          hashRow_good hw tf mux bit x ds words).weaken (fun s h => h) ?_
  rintro s o s4 hs - - ⟨hw, s1, ⟨-, hh⟩, -, he1, tf, s2, ⟨-, ht⟩, -, he2, words, s3, ⟨hlen, -, -⟩, -, he3, ho,
    ch, hrow⟩
  refine ⟨ho, fun st val hsat => ?_⟩
  obtain ⟨col, hcol, hH, hT, hF, hM, hS, hX, hD, hO, -⟩ := hash_sem hsat hrow
  have hhv := hh st val (hsat.mono he1)
  have htv := ht st val (hsat.mono he2)
  refine ⟨col, ⟨hcol, fun k => ?_, ?_, ?_, hM⟩, hS, hX, hD, ?_⟩
  · apply columnWord_ofWord
    rw [hH k, hhv]
    simp only [limbsOf, paramIVLimbs]
    fin_cases k <;> rfl
  · apply columnWord_ofWord col hashT 64
    rw [hT, htv]
    rfl
  · have : columnWord col hashF = 0xFFFFFFFF := by
      apply columnWord_ofWord
      rw [hF, htv]
      rfl
    rw [this]
    decide
  · funext k
    simp only [outWords, words4, hO k]


/-- A single block whose bit is held to zero hashes `mux` and then its message's second half. -/
theorem single_zero (val : Val) (mux bit x ds o : ℕ) (h : SingleSem val mux bit x ds o) (hb : val bit 0 = 0)
    (right : Fin 4 → K) (hr : ∀ i : Fin 4, i.val < 3 → val x i = right i) (hd : val ds 0 = right 3) :
    words4 (val o) = Rec.node (words4 (val mux)) (words4 right) := by
  obtain ⟨col, hn, hS, hX, hD, hO⟩ := h
  rw [← hO]
  apply parent_row_digest col (val mux) right ⟨hn, by rw [hS, hb], fun i => ?_⟩
  by_cases hi : i.val < 3
  · rw [hX i hi, hr i hi]
  · have : i = 3 := by ext; omega
    subst this
    rw [show hashM + 4 + ((3 : Fin 4) : ℕ) = hashM + 7 from rfl, hD, hd]

/-- `node`: the parent of `acc` and a sibling, `acc` second when the Boolean `bit` is one. -/
theorem node_good (acc bit : ℕ) : Good (fun _ => True) (node acc bit) fun _ o s' => o < s'.next ∧
    ∀ st val, Sat st s' val → (val bit 0 = 0 ∨ val bit 0 = 1) ∧ ∃ sib : Fin 4 → BitVec 64,
      words4 (val o) = if val bit 0 = 1 then Rec.node sib (words4 (val acc)) else Rec.node (words4 (val acc)) sib := by
  refine (Good.bind fresh_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun x =>
    Good.bind fresh_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun ds =>
      singleBlock_good acc bit x ds).weaken (fun s h => h) ?_
  rintro s o s2 hs - - ⟨x, s1, -, -, -, ds, s1', -, -, -, ho, hsem⟩
  refine ⟨ho, fun st val hsat => ?_⟩
  obtain ⟨col, hn, hS, -, -, hO⟩ := hsem st val hsat
  have hd := node_row_digest col (val acc) hn
  rw [hO] at hd
  rcases node_row col hn.hashRow.identities (val acc) hn.mux with ⟨h0, -⟩ | ⟨h1, -⟩
  · refine ⟨Or.inl (hS ▸ h0), (step col).2, ?_⟩
    have hs : (step col).1 = false := by simp [step, h0]
    rw [hd, hs, ← hS, h0]
    simp
  · refine ⟨Or.inr (hS ▸ h1), (step col).2, ?_⟩
    have hs : (step col).1 = true := by simp [step, h1]
    rw [hd, hs, ← hS, h1]
    simp

/-- `parent`: the node of two wired children. -/
theorem parent_good (l r : ℕ) : Good (Wires [r]) (parent l r) fun _ o s' => o < s'.next ∧
    ∀ st val, Sat st s' val → words4 (val o) = Rec.node (words4 (val l)) (words4 (val r)) := by
  refine (Good.bind (dToEAndK_good r) (P₂ := fun p s => ∀ st val, Sat st s val →
      (∀ i : Fin 4, i.val < 3 → val p.1 i = val r i) ∧ val p.2 0 = val r 3) (fun _ _ _ _ _ h _ => h.2.2) fun p =>
    Good.bind (kZero_good.pre fun _ _ => trivial) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun z =>
      singleBlock_good l z p.1 p.2).weaken (fun s h => h) ?_
  rintro s o s2 hs - - ⟨p, s1, ⟨-, -, hp⟩, -, he1, z, s1', ⟨-, hz⟩, -, he2, ho, hsem⟩
  refine ⟨ho, fun st val hsat => ?_⟩
  obtain ⟨hx, hd⟩ := hp st val (hsat.mono he1)
  have hzv : val z 0 = 0 := by rw [hz st val (hsat.mono he2)]; simp [limbsOf, ofWord_zero]
  exact single_zero val l z p.1 p.2 o (hsem st val hsat) hzv (val r) hx hd

/-- The words `x`'s three limbs and `ds`. -/
noncomputable def xds (val : Val) (x ds : ℕ) (i : Fin 4) : K := if i.val < 3 then val x i else val ds 0

/-- `compress`: one block from the parameter IV of `acc`, `x`'s limbs and `ds`. -/
theorem compress_good (acc x ds : ℕ) : Good (fun _ => True) (compress acc x ds) fun _ o s' => o < s'.next ∧
    ∀ st val, Sat st s' val → words4 (val o) = Rec.node (words4 (val acc)) (words4 (xds val x ds)) := by
  refine (Good.bind kZero_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun z =>
    singleBlock_good acc z x ds).weaken (fun s h => h) ?_
  rintro s o s2 hs - - ⟨z, s1, ⟨-, hz⟩, -, he1, ho, hsem⟩
  refine ⟨ho, fun st val hsat => ?_⟩
  have hzv : val z 0 = 0 := by rw [hz st val (hsat.mono he1)]; simp [limbsOf, ofWord_zero]
  exact single_zero val acc z x ds o (hsem st val hsat) hzv _ (fun i hi => by simp [xds, hi]) (by simp [xds])


/-- A `K` wire's word. -/
noncomputable def w64 (val : Val) (w : ℕ) : BitVec 64 := BitVec.ofNat 64 (toWord (val w 0))

/-- `leaf_block`: RFC 7693's compression of the chaining value `h` and the eight words `m` at counter `t`. -/
theorem leafBlock_good (h : ℕ) (m : List ℕ) (t : ℕ) (last : Bool) (hm : m.length = 8) (ht : t < 2 ^ 64) :
    Good (fun _ => True) (leafBlock h m t last) fun _ o s' => o < s'.next ∧ ∀ st val, Sat st s' val →
      words4 (val o) = digest (Blake2s.Rfc7693.F (cvWords (words4 (val h))) (block (m.map (w64 val)) 0) (BitVec.ofNat 64 t) last) := by
  refine (Good.bind (dConst_good [t, if last then final else 0, 0, 0]) (P₂ := fun _ _ => True)
    (fun _ _ _ _ _ _ _ => trivial) fun tf =>
      Good.bind fresh_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun mux =>
      Good.bind fresh_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun bit =>
      Good.bind fresh_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun x =>
      Good.bind fresh_good (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun ds =>
        hashRow_good h tf mux bit x ds m).weaken (fun s h => h) ?_
  rintro s o s6 hs - - ⟨tf, s1, ⟨-, htf⟩, -, he1, mux, -, -, -, -, bit, -, -, -, -, x, -, -, -, -, ds, -, -, -, -,
    ho, ch, hrow⟩
  refine ⟨ho, fun st val hsat => ?_⟩
  obtain ⟨col, hcol, hH, hT, hF, -, -, -, -, hO, hW⟩ := hash_sem hsat hrow
  have htv := htf st val (hsat.mono he1)
  have hcounter : columnWord col hashT = BitVec.ofNat 64 t := by
    rw [columnWord, hT, htv]
    simp [limbsOf, toWord_ofWord _ ht]
  have hfin : (columnWord col hashF).setWidth 32 = finalWord last := by
    rw [columnWord, hF, htv]
    cases last
    · have : limbsOf [t, if false = true then final else 0, 0, 0] 1 = ofWord 0 := rfl
      rw [this, toWord_ofWord 0 (by norm_num)]
      rfl
    · have : limbsOf [t, if true = true then final else 0, 0, 0] 1 = ofWord final := rfl
      rw [this, toWord_ofWord final (by norm_num [final])]
      rfl
  have hdig := hash_row_digest col hcol (cvWords (words4 (val h)))
    (fun k => by rw [digest_cvWords, columnWord, hH k]; rfl) last hfin
  rw [hcounter, msg_block col (m.map (w64 val)) 0 fun i => ?_] at hdig
  · rw [← hdig]
    funext k
    simp only [outWords, words4, hO k]
  · rw [columnWord, hW i i.isLt, wordAt]
    have hi : i.val < m.length := by omega
    simp [w64, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]


/-- Block `j` of the words padded with `z` is block `j` of the message, `z` being zero. -/
theorem pad_block (val : Val) (words : List ℕ) (z j : ℕ) (hz : val z 0 = 0) :
    block (((List.range 8).map fun i => words.getD (8 * j + i) z).map (w64 val)) 0 =
      block (words.map (w64 val)) j := by
  apply Vector.ext
  intro r hr
  simp only [block, Vector.getElem_ofFn]
  congr 1
  have hzw : w64 val z = 0 := by
    simp only [w64, hz]
    rw [show (0 : K) = ofWord 0 from ofWord_zero.symm, toWord_ofWord 0 (by norm_num)]
    rfl
  simp only [wordAt, List.getD_eq_getElem?_getD, List.getElem?_map, Nat.mul_zero, Nat.zero_add]
  rw [List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  by_cases hl : 8 * j + r / 2 < words.length
  · simp [List.getElem?_eq_getElem hl]
  · rw [List.getElem?_eq_none (by omega : words.length ≤ 8 * j + r / 2)]
    simp [hzw]

theorem chainBlocks_good (words : List ℕ) (z n bytes : ℕ) (hb : bytes < 2 ^ 64)
    (hmid : ∀ j, j + 1 < n → min (64 * (j + 1)) bytes = 64 * (j + 1)) (hlast : min (64 * n) bytes = bytes) :
    ∀ k (H : Val → Vector (BitVec 32) 8) j h, j + k + 1 = n → Good (fun s => ∀ st val, Sat st s val → val z 0 = 0 ∧ words4 (val h) = digest (H val))
      (chainBlocks words z n bytes ((List.range (k + 1)).map (j + ·)) h) fun _ r s' => r < s'.next ∧
        ∀ st val, Sat st s' val → words4 (val r) = digest (blocksFrom (BitVec.ofNat 64 bytes) (H val) j
          (block (words.map (w64 val)) j) ((List.range k).map fun i => block (words.map (w64 val)) (j + 1 + i))) := by
  intro k
  induction k with
  | zero =>
    intro H j h hj
    have hn : j + 1 = n := by omega
    rw [show (List.range (0 + 1)).map (j + ·) = [j] from rfl]
    refine (Good.bind ((leafBlock_good h _ (min (64 * (j + 1)) bytes) (j + 1 = n) (by simp)
      (lt_of_le_of_lt (min_le_right _ _) hb)).pre fun _ _ => trivial) (P₂ := fun _ _ => True)
      (fun _ _ _ _ _ _ _ => trivial) fun r => Good.pure' (Q := fun _ o _ => o = r) fun _ _ _ => rfl).weaken
      (fun s h => h) ?_
    rintro s o s2 hs hpre - ⟨r, s1, ⟨hr, hsem⟩, he, he2, rfl⟩
    refine ⟨lt_of_lt_of_le hr he2.next, fun st val hsat => ?_⟩
    obtain ⟨hz, hh⟩ := hpre st val (hsat.mono (he.trans he2))
    rw [hsem st val (hsat.mono he2), hh, cvWords_digest, pad_block val words z j hz,
      show min (64 * (j + 1)) bytes = bytes by rw [hn]; exact hlast]
    simp [hn, blocksFrom]
  | succ k ih =>
    intro H j h hj
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero, Function.comp_def]
    let H' : Val → Vector (BitVec 32) 8 := fun val =>
      Blake2s.Rfc7693.F (H val) (block (words.map (w64 val)) j) (BitVec.ofNat 64 (64 * (j + 1))) false
    have hrest : (List.range (k + 1)).map (fun i => j + (i + 1)) = (List.range (k + 1)).map (j + 1 + ·) := by
      apply List.map_congr_left; intro i _; omega
    rw [hrest]
    refine (Good.bind ((leafBlock_good h _ (min (64 * (j + 1)) bytes) (j + 1 = n) (by simp)
      (lt_of_le_of_lt (min_le_right _ _) hb)).pre fun _ _ => trivial)
      (P₂ := fun r s => ∀ st val, Sat st s val → val z 0 = 0 ∧ words4 (val r) = digest (H' val))
      ?_ fun r => ih H' (j + 1) r (by omega)).weaken (fun s h => h) ?_
    · rintro s r s1 hs hpre ⟨-, hsem⟩ he st val hsat
      obtain ⟨hz, hh⟩ := hpre st val (hsat.mono he)
      refine ⟨hz, ?_⟩
      rw [hsem st val hsat, hh, cvWords_digest, pad_block val words z j hz, hmid j (by omega)]
      simp [H', show ¬ (j + 1 = n) by omega]
    · rintro s o s2 hs - - ⟨r, s1, -, -, he2, ho, hsem⟩
      refine ⟨ho, fun st val hsat => ?_⟩
      rw [hsem st val hsat, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [blocksFrom, H', Nat.add_zero, Function.comp_def]
      congr 3
      funext i; congr 1; omega


theorem words4_paramIV : words4 (limbsOf paramIVLimbs) = digest paramIV := by
  funext k
  have : limbsOf paramIVLimbs k = ofWord (digest paramIV k).toNat := by
    simp only [limbsOf, paramIVLimbs]; fin_cases k <;> rfl
  rw [words4, this, toWord_ofWord _ (digest paramIV k).isLt]
  simp

/-- `chain`: RFC 7693's BLAKE2s-256 of the words' little-endian bytes. -/
theorem chain_good (words : List ℕ) (hb : 8 * words.length < 2 ^ 64) : Good (fun _ => True) (chain words)
    fun _ r s' => r < s'.next ∧ ∀ st val, Sat st s' val → words4 (val r) = digest (hashWords (words.map (w64 val))) := by
  set n := max 1 ((words.length + 7) / 8) with hn
  have hn1 : 1 ≤ n := le_max_left _ _
  have hmid : ∀ j, j + 1 < n → min (64 * (j + 1)) (8 * words.length) = 64 * (j + 1) := by
    intro j hj; apply min_eq_left
    have : (words.length + 7) / 8 = n := by omega
    omega
  have hlast : min (64 * n) (8 * words.length) = 8 * words.length := by
    apply min_eq_right; omega
  have hrange : List.range n = (List.range (n - 1 + 1)).map (0 + ·) := by
    rw [Nat.sub_add_cancel hn1]; simp
  have hcb := fun z h => (hrange ▸ chainBlocks_good words z n (8 * words.length) hb hmid hlast (n - 1)
    (fun _ => paramIV) 0 h (by omega) :)
  refine (Good.bind kZero_good (P₂ := fun z s => ∀ st val, Sat st s val → val z 0 = 0)
    (fun _ _ _ _ _ h _ st val hsat => by rw [h.2 st val hsat]; simp [limbsOf, ofWord_zero]) fun z =>
      Good.bind ((dConst_good paramIVLimbs).pre (P' := fun s => ∀ st val, Sat st s val → val z 0 = 0)
        fun _ _ => trivial) (P₂ := fun h s => ∀ st val, Sat st s val → val z 0 = 0 ∧ words4 (val h) = digest paramIV)
        ?_ fun h => hcb z h).weaken (fun s h => h) ?_
  · rintro s h s1 hs hz ⟨-, hh⟩ he st val hsat
    refine ⟨hz st val (hsat.mono he), ?_⟩
    rw [hh st val hsat]
    exact words4_paramIV
  · rintro s r s2 hs - - ⟨z, s1, -, -, he, h, s1', -, -, he2, hr, hsem⟩
    refine ⟨hr, fun st val hsat => ?_⟩
    have h1 : nBlocks (words.map (w64 val)).length = n := by rw [List.length_map, hn]; rfl
    rw [hsem st val hsat, hashWords, blake2s256, h1, List.length_map]
    congr 2
    apply List.map_congr_left
    intro i _
    congr 1
    omega


/-! Public statement rows. -/

theorem expose_good (w : ℕ) : Good (Wires [w]) (expose w) fun s i s' => i = s.statement ∧
    ∀ st val, Sat st s' val → val w = st i := by
  intro s hs hw
  have hrow : (w, PubSource.statement s.statement) ∈ (s.pub.push (w, .statement s.statement)) :=
    Array.mem_push.mpr (Or.inr rfl)
  refine ⟨⟨hs.emulLt, fun kv z h => mem_push_of_mem _ (hs.consts kv z h), fun z h => mem_push_of_mem _ (hs.eZero z h), hs.eOne,
    fun z h => mem_push_of_mem _ (hs.kZero z h), fun z h => mem_push_of_mem _ (hs.kOne z h), hs.arithE, hs.arithK,
    hs.arithLt, hs.constsLt, fun p hp => ?_⟩, ⟨le_rfl, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
      fun _ h => h, fun _ h => h, fun _ h => mem_push_of_mem _ h⟩, rfl, fun st val hsat => hsat.pub _ _ hrow⟩
  rcases Array.mem_push.mp hp with hp | rfl
  · exact hs.pubLt p hp
  · exact hw w (by simp)

theorem ret_good {α : Type} {P : State → Prop} {m : M α} {Q : State → α → State → Prop} (h : Good P m Q) :
    Good P (do return [← m]) fun s outs s' => ∃ a, outs = [a] ∧ Q s a s' :=
  (Good.bind h (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun a =>
    Good.pure' (Q := fun s₀ outs s' => outs = [a] ∧ s' = s₀) fun _ _ _ => ⟨rfl, rfl⟩).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨a, _, hq, _, _, hout, hs⟩ => ⟨a, hout, hs ▸ hq⟩


/-! Every call's contract. -/

/-- What a call's outputs are in an assignment satisfying a circuit containing its rows. -/
def Call.Holds (st : ℕ → Fin 4 → K) (val : Val) (outs : List ℕ) : Call → Prop
  | .freeE | .freeK | .freeD => True
  | .eqE a b | .eqK a b | .eqD a b => val a = val b
  | .eqConstE a c0 c1 c2 => ev val a = toE (ofWord c0) (ofWord c1) (ofWord c2)
  | .eqConstK a v => val a = limbsOf [v, 0, 0, 0]
  | .eConst c0 c1 c2 => ev val (outs.getD 0 0) = toE (ofWord c0) (ofWord c1) (ofWord c2)
  | .kConst v => val (outs.getD 0 0) = limbsOf [v, 0, 0, 0]
  | .dConst v => val (outs.getD 0 0) = limbsOf v
  | .zero => ev val (outs.getD 0 0) = 0
  | .one => ev val (outs.getD 0 0) = 1
  | .exposeE w => val w = st (outs.getD 0 0)
  | .mulAdd a b d => ev val (outs.getD 0 0) = ev val a * ev val b + ev val d
  | .mul a b => ev val (outs.getD 0 0) = ev val a * ev val b
  | .add a d => ev val (outs.getD 0 0) = ev val a + ev val d
  | .square a => ev val (outs.getD 0 0) = ev val a * ev val a
  | .mulKAdd a k d => ev val (outs.getD 0 0) = ev val a * emb (val k 0) + ev val d
  | .mulConstAdd a c0 c1 c2 d => ev val (outs.getD 0 0) = ev val a * toE (ofWord c0) (ofWord c1) (ofWord c2) + ev val d
  | .inv a => ev val a * ev val (outs.getD 0 0) = 1
  | .sum terms => ev val (outs.getD 0 0) = (terms.map (ev val)).sum
  | .split w => (∀ i < 64, val (outs.getD i 0) 0 = 0 ∨ val (outs.getD i 0) 0 = 1) ∧
      toWord (val w 0) = num (fun i => if val (outs.getD i 0) 0 = 1 then 1 else 0) 64
  | .pack bits => (∀ i < 64, i < bits.length → val (bits.getD i 0) 0 = 0 ∨ val (bits.getD i 0) 0 = 1) ∧
      toWord (val (outs.getD 0 0) 0) = num (fun i => if i < bits.length ∧ val (bits.getD i 0) 0 = 1 then 1 else 0) 64
  | .eToK e => ∀ i : Fin 4, i.val < 3 → val (outs.getD i 0) 0 = val e i
  | .kToE k0 k1 k2 => ev val (outs.getD 0 0) = toE (val k0 0) (val k1 0) (val k2 0)
  | .kToE1 k => ev val (outs.getD 0 0) = emb (val k 0)
  | .dToK d => ∀ i : Fin 4, val (outs.getD i 0) 0 = val d i
  | .dToEAndK d => (∀ i : Fin 4, i.val < 3 → val (outs.getD 0 0) i = val d i) ∧ val (outs.getD 1 0) 0 = val d 3
  | .halvesToD lo hi => val (outs.getD 0 0) 0 = val lo 0 ∧ val (outs.getD 0 0) 1 = val lo 1 ∧
      val (outs.getD 0 0) 2 = val hi 0 ∧ val (outs.getD 0 0) 3 = val hi 1 ∧ val lo 2 = 0 ∧ val hi 2 = 0
  | .compress acc x ds => words4 (val (outs.getD 0 0)) = Rec.node (words4 (val acc)) (words4 (xds val x ds))
  | .node acc bit => (val bit 0 = 0 ∨ val bit 0 = 1) ∧ ∃ sib : Fin 4 → BitVec 64, words4 (val (outs.getD 0 0)) =
      if val bit 0 = 1 then Rec.node sib (words4 (val acc)) else Rec.node (words4 (val acc)) sib
  | .parent l r => words4 (val (outs.getD 0 0)) = Rec.node (words4 (val l)) (words4 (val r))
  | .leafBlock h m t last => words4 (val (outs.getD 0 0)) =
      digest (Blake2s.Rfc7693.F (cvWords (words4 (val h))) (block (m.map (w64 val)) 0) (BitVec.ofNat 64 t) last)
  | .chain words => words4 (val (outs.getD 0 0)) = digest (hashWords (words.map (w64 val)))

/-- Every call keeps the invariant, only adds to the circuit, and its outputs are what it computes. -/
theorem Call.exec_good (c : Call) (hok : c.ok = true) : Good (Wires c.args) c.exec fun _ outs s' =>
    ∀ st val, Sat st s' val → c.Holds st val outs := by
  cases c with
  | freeE | freeK | freeD =>
    exact (ret_good wire_good).pre (fun _ _ => trivial) |>.weaken (fun _ h => h) fun _ _ _ _ _ _ _ _ _ _ => trivial
  | eqE a b | eqK a b | eqD a b =>
    exact (Good.bind (union_good a b) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun _ =>
      Good.pure' (Q := fun s₀ _ s' => s' = s₀) fun _ _ _ => rfl).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, _, hu, _, _, hs⟩ st val hsat => (hs ▸ hsat).unions _ hu
  | eqConstE a c0 c1 c2 =>
    exact (Good.bind (eqConstE_good a c0 c1 c2) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun _ =>
      Good.pure' (Q := fun s₀ _ s' => s' = s₀) fun _ _ _ => rfl).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, _, hq, _, _, hs⟩ st val hsat => hq st val (hs ▸ hsat)
  | eqConstK a v =>
    exact (Good.bind (eqConstK_good a v) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun _ =>
      Good.pure' (Q := fun s₀ _ s' => s' = s₀) fun _ _ _ => rfl).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, _, hq, _, _, hs⟩ st val hsat => hq st val (hs ▸ hsat)
  | eConst c0 c1 c2 =>
    exact (ret_good (eConst_good c0 c1 c2)).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | kConst v =>
    exact (ret_good (kConst_good v)).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | dConst v =>
    exact (ret_good (dConst_good v)).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | zero =>
    exact (ret_good zero_good).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | one =>
    exact (ret_good one_good).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | exposeE w =>
    exact (ret_good (expose_good w)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | mulAdd a b d =>
    exact (ret_good (mulAdd_good a b d)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | mul a b =>
    exact (ret_good (mul_good a b)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | add a d =>
    exact (ret_good (add_good a d)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | square a =>
    exact (ret_good (square_good a)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | mulKAdd a k d =>
    exact (ret_good (mulKAdd_good a k d)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | mulConstAdd a c0 c1 c2 d =>
    exact (ret_good (mulConstAdd_good a c0 c1 c2 d)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | inv a =>
    exact (ret_good (inv_good a)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | sum terms =>
    exact (ret_good (sum_good terms)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | split w =>
    exact (split_good w).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, _, hq⟩ st val hsat => hq st val hsat
  | pack bits =>
    exact (ret_good (pack_good bits)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | eToK e =>
    exact (eToK_good e).weaken (fun _ h => h) fun _ _ _ _ _ _ ⟨_, hq⟩ st val hsat => hq st val hsat
  | kToE k0 k1 k2 =>
    exact (ret_good (kToE_good k0 k1 k2)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | kToE1 k =>
    exact (ret_good (kToE1_good k)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | dToK d =>
    exact (dToK_good d).weaken (fun _ h => h) fun _ _ _ _ _ _ ⟨_, hq⟩ st val hsat => hq st val hsat
  | dToEAndK d =>
    exact (Good.bind (dToEAndK_good d) (P₂ := fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) fun p =>
      Good.pure' (Q := fun s₀ outs s' => outs = [p.1, p.2] ∧ s' = s₀) fun _ _ _ => ⟨rfl, rfl⟩).weaken
      (fun _ h => h) fun _ _ _ _ _ _ ⟨_, _, ⟨_, _, hq⟩, _, _, hout, hs⟩ st val hsat => by
        subst hout; exact hq st val (hs ▸ hsat)
  | halvesToD lo hi =>
    exact (ret_good (halvesToD_good lo hi)).weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | compress acc x ds =>
    exact (ret_good (compress_good acc x ds)).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | node acc bit =>
    exact (ret_good (node_good acc bit)).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | parent l r =>
    exact (ret_good (parent_good l r)).pre (fun _ h w hw => h w (by simp at hw; simp [Call.args, hw]))
      |>.weaken (fun _ h => h) fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | leafBlock h m t last =>
    simp only [Call.ok, decide_eq_true_eq] at hok
    exact (ret_good (leafBlock_good h m t last hok.1 hok.2)).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat
  | chain words =>
    simp only [Call.ok, decide_eq_true_eq] at hok
    exact (ret_good (chain_good words hok)).pre (fun _ _ => trivial) |>.weaken (fun _ h => h)
      fun _ _ _ _ _ _ ⟨_, hout, _, hq⟩ st val hsat => by subst hout; exact hq st val hsat


/-- Calls in order, with each one's outputs. -/
def runAll : List Call → State → State × List (List ℕ)
  | [], s => (s, [])
  | c :: cs, s => ((runAll cs (c.exec.run s).2).1, (c.exec.run s).1 :: (runAll cs (c.exec.run s).2).2)

/-- Each call names wires already made and has the sizes its Rust method takes: what `checkrec` checks. -/
def Valid : List Call → State → Prop
  | [], _ => True
  | c :: cs, s => Wires c.args s ∧ c.ok = true ∧ Valid cs (c.exec.run s).2

theorem run_eq_exec (c : Call) (s : State) : (c.run.run s).2 = (c.exec.run s).2 := rfl

/-- Replaying valid calls keeps the invariant, and in every assignment satisfying the circuit they build, every
call's outputs are what it computes. -/
theorem replay_sound : ∀ (cs : List Call) (s : State), Inv s → Valid cs s →
    Inv (runAll cs s).1 ∧ Ext s (runAll cs s).1 ∧ ∀ i (hi : i < cs.length) (hj : i < (runAll cs s).2.length) st val,
      Sat st (runAll cs s).1 val → cs[i].Holds st val (runAll cs s).2[i]
  | [], s, hs, _ => ⟨hs, Ext.refl s, fun i hi => absurd hi (by simp)⟩
  | c :: cs, s, hs, ⟨hw, hok, hv⟩ => by
    obtain ⟨hs₁, he₁, hc⟩ := c.exec_good hok s hs hw
    obtain ⟨hs₂, he₂, hrest⟩ := replay_sound cs _ hs₁ hv
    refine ⟨hs₂, he₁.trans he₂, fun i hi hj st val hsat => ?_⟩
    cases i with
    | zero => exact hc st val (hsat.mono he₂)
    | succ i => exact hrest i (by simpa using hi) (by simpa [runAll] using hj) st val hsat

theorem runAll_length : ∀ (cs : List Call) (s : State), (runAll cs s).2.length = cs.length
  | [], _ => rfl
  | _ :: cs, s => by simp [runAll, runAll_length cs]

end LeanVMCircuits.Rec.Model
