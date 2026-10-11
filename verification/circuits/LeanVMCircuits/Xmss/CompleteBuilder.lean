module

public import LeanVMCircuits.Rec.Contracts

@[expose] public section

/-!
What the builder's methods can be made to hold.

`Rec.Contracts` says what every satisfying assignment makes a method's outputs. These contracts say the converse:
an assignment satisfying the circuit before a method runs extends, on the wires the method makes, to one satisfying
the circuit after it, whose outputs are what the method computes, whenever the method's inputs carry values of the
shapes it takes (`K` words with zero upper limbs, `E` elements with a zero top limb, Boolean bits) and the wires it
holds to constants or statement words carry those. `CGood` is such a contract. It is stated pointwise in every
assignment agreeing with the extension on the wires made so far, so contracts compose through `bind` without
transport, and it counts the statement words a method exposes.
-/

namespace LeanVMCircuits.Rec.Model

open LeanVMCircuits.Rec

/-! Assignments agreeing below a wire. -/

/-- `v'` carries `v`'s limbs on every wire below `n`. -/
def Agree (n : ℕ) (v v' : Val) : Prop := ∀ w < n, v' w = v w

theorem Agree.refl (n : ℕ) (v : Val) : Agree n v v := fun _ _ => rfl

theorem Agree.trans {n m : ℕ} {v₁ v₂ v₃ : Val} (h₁ : Agree n v₁ v₂) (h₂ : Agree m v₂ v₃) (h : n ≤ m) :
    Agree n v₁ v₃ := fun w hw => (h₂ w (lt_of_lt_of_le hw h)).trans (h₁ w hw)

theorem Agree.mono {n m : ℕ} {v v' : Val} (h : Agree m v v') (hn : n ≤ m) : Agree n v v' :=
  fun w hw => h w (lt_of_lt_of_le hw hn)

/-- The assignment `v` with wire `w` set to `x`. -/
def setW (v : Val) (w : ℕ) (x : Fin 4 → K) : Val := fun u => if u = w then x else v u

theorem agree_setW (v : Val) (n : ℕ) (x : Fin 4 → K) : Agree n v (setW v n x) :=
  fun _ hw => if_neg (Nat.ne_of_lt hw)

theorem setW_self (v : Val) (n : ℕ) (x : Fin 4 → K) : setW v n x n = x := if_pos rfl

/-- Every slot of a row names a wire below `n`. -/
def RowLt (n : ℕ) (r : List ℕ) : Prop := ∀ j, r.getD j 0 < n

theorem RowLt.mono {n m : ℕ} {r : List ℕ} (h : RowLt n r) (hn : n ≤ m) : RowLt m r :=
  fun j => lt_of_lt_of_le (h j) hn

theorem rowLt_of_wires {r : List ℕ} {n : ℕ} (hw : ∀ w ∈ r, w < n) (hne : r ≠ []) : RowLt n r := by
  intro j
  rw [List.getD_eq_getElem?_getD]
  cases h : r[j]? with
  | some w => exact hw w (List.mem_of_getElem? h)
  | none =>
    obtain ⟨w, hw'⟩ := List.exists_mem_of_ne_nil r hne
    exact lt_of_le_of_lt (Nat.zero_le _) (hw w hw')

/-- Every union and row of the circuit names wires already made. -/
structure Closed (s : State) : Prop where
  unions : ∀ p ∈ s.unions, p.1 < s.next ∧ p.2 < s.next
  emul : ∀ r ∈ s.emul, RowLt s.next r
  exk : ∀ r ∈ s.exk, RowLt s.next r
  hash : ∀ r ∈ s.hash, RowLt s.next r
  split : ∀ r ∈ s.split, RowLt s.next r
  cast : ∀ r ∈ s.cast, RowLt s.next r

theorem closed_empty : Closed ({} : State) :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h,
    fun _ h => by simp at h, fun _ h => by simp at h⟩

/-- A state whose new unions and rows name wires below its `next`. -/
theorem Closed.step {s s' : State} (h : Closed s) (hn : s.next ≤ s'.next)
    (hu : ∀ p ∈ s'.unions, p ∈ s.unions ∨ (p.1 < s'.next ∧ p.2 < s'.next))
    (he : ∀ r ∈ s'.emul, r ∈ s.emul ∨ RowLt s'.next r) (hk : ∀ r ∈ s'.exk, r ∈ s.exk ∨ RowLt s'.next r)
    (hh : ∀ r ∈ s'.hash, r ∈ s.hash ∨ RowLt s'.next r) (hs : ∀ r ∈ s'.split, r ∈ s.split ∨ RowLt s'.next r)
    (hc : ∀ r ∈ s'.cast, r ∈ s.cast ∨ RowLt s'.next r) : Closed s' := by
  refine ⟨fun p hp => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · rcases hu p hp with h' | h'
    · exact ⟨lt_of_lt_of_le (h.unions p h').1 hn, lt_of_lt_of_le (h.unions p h').2 hn⟩
    · exact h'
  · rcases he r hr with h' | h'
    · exact (h.emul r h').mono hn
    · exact h'
  · rcases hk r hr with h' | h'
    · exact (h.exk r h').mono hn
    · exact h'
  · rcases hh r hr with h' | h'
    · exact (h.hash r h').mono hn
    · exact h'
  · rcases hs r hr with h' | h'
    · exact (h.split r h').mono hn
    · exact h'
  · rcases hc r hr with h' | h'
    · exact (h.cast r h').mono hn
    · exact h'

/-- A state with the same unions and rows and more wires. -/
theorem Closed.same {s s' : State} (h : Closed s) (hn : s.next ≤ s'.next) (hu : s'.unions = s.unions)
    (he : s'.emul = s.emul) (hk : s'.exk = s.exk) (hh : s'.hash = s.hash) (hs : s'.split = s.split)
    (hc : s'.cast = s.cast) : Closed s' :=
  h.step hn (fun _ hp => Or.inl (hu ▸ hp)) (fun _ hr => Or.inl (he ▸ hr)) (fun _ hr => Or.inl (hk ▸ hr))
    (fun _ hr => Or.inl (hh ▸ hr)) (fun _ hr => Or.inl (hs ▸ hr)) (fun _ hr => Or.inl (hc ▸ hr))

theorem RowSat.agree {forms : List (List Form)} {holds : (ℕ → K) → Prop} {v v' : Val} {r : List ℕ} {n : ℕ}
    (h : RowSat forms holds v r) (hr : RowLt n r) (ha : Agree n v v') : RowSat forms holds v' r := by
  obtain ⟨col, hc, hl⟩ := h
  exact ⟨col, hc, fun j hj i => by rw [hl j hj i, ha _ (hr j)]⟩

/-- An assignment satisfying a closed circuit satisfies it changed only on wires it does not name. -/
theorem Sat.agree {st : ℕ → Fin 4 → K} {s : State} {v v' : Val} (hs : Inv s) (hc : Closed s) (h : Sat st s v)
    (ha : Agree s.next v v') : Sat st s v' :=
  ⟨fun p hp => by rw [ha _ (hc.unions p hp).1, ha _ (hc.unions p hp).2]; exact h.unions p hp,
    fun r hr => (h.emul r hr).agree (hc.emul r hr) ha, fun r hr => (h.exk r hr).agree (hc.exk r hr) ha,
    fun r hr => (h.hash r hr).agree (hc.hash r hr) ha, fun r hr => (h.split r hr).agree (hc.split r hr) ha,
    fun r hr => (h.cast r hr).agree (hc.cast r hr) ha,
    fun w src hp => by rw [ha w (hs.pubLt _ hp)]; exact h.pub w src hp⟩

/-- An assignment satisfies a circuit grown by unions, rows and public rows it satisfies. -/
theorem Sat.step {st : ℕ → Fin 4 → K} {s s' : State} {v : Val} (h : Sat st s v)
    (hu : ∀ p ∈ s'.unions, p ∈ s.unions ∨ v p.1 = v p.2)
    (he : ∀ r ∈ s'.emul, r ∈ s.emul ∨ RowSat Rec.emul (fun _ => True) v r)
    (hk : ∀ r ∈ s'.exk, r ∈ s.exk ∨ RowSat Rec.exk (fun _ => True) v r)
    (hh : ∀ r ∈ s'.hash, r ∈ s.hash ∨ RowSat Rec.hash HashRow v r)
    (hs : ∀ r ∈ s'.split, r ∈ s.split ∨
      RowSat Rec.split (fun col => ∀ id ∈ splitIdentities, id.eval col = 0) v r)
    (hc : ∀ r ∈ s'.cast, r ∈ s.cast ∨ RowSat Rec.cast (fun _ => True) v r)
    (hp : ∀ w src, (w, src) ∈ s'.pub → (w, src) ∈ s.pub ∨ v w = srcVal st src) : Sat st s' v := by
  refine ⟨fun p hp' => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_,
    fun w src hp' => ?_⟩
  · rcases hu p hp' with h' | h'
    · exact h.unions p h'
    · exact h'
  · rcases he r hr with h' | h'
    · exact h.emul r h'
    · exact h'
  · rcases hk r hr with h' | h'
    · exact h.exk r h'
    · exact h'
  · rcases hh r hr with h' | h'
    · exact h.hash r h'
    · exact h'
  · rcases hs r hr with h' | h'
    · exact h.split r h'
    · exact h'
  · rcases hc r hr with h' | h'
    · exact h.cast r h'
    · exact h'
  · rcases hp w src hp' with h' | h'
    · exact h.pub w src h'
    · exact h'

/-! Completeness contracts. -/

/-- From a state keeping the invariant with closed rows, and an assignment satisfying it all of whose agreeing
assignments meet `P`, `m` keeps the invariant and closure, extends the circuit, exposes `k` statement words, and the
assignment extends on the new wires to one satisfying the new circuit, every assignment agreeing with which on the
wires made meets `Q`. -/
def CGood {α : Type} (st : ℕ → Fin 4 → K) (k : ℕ) (P : State → Val → Prop) (m : M α)
    (Q : State → α → State → Val → Prop) : Prop :=
  ∀ s val, Inv s → Closed s → Sat st s val → (∀ v, Agree s.next val v → P s v) →
    Inv (m.run s).2 ∧ Closed (m.run s).2 ∧ Ext s (m.run s).2 ∧ (m.run s).2.statement = s.statement + k ∧
    ∃ val', Agree s.next val val' ∧ Sat st (m.run s).2 val' ∧
      ∀ v, Agree (m.run s).2.next val' v → Q s (m.run s).1 (m.run s).2 v

theorem run_bind' {α β : Type} (m : M α) (f : α → M β) (s : State) :
    (m >>= f).run s = (f (m.run s).1).run (m.run s).2 := rfl

section

variable {st : ℕ → Fin 4 → K}

theorem CGood.bind {α β : Type} {k₁ k₂ : ℕ} {P : State → Val → Prop} {m : M α} {f : α → M β}
    {Q₁ : State → α → State → Val → Prop} {P₂ : α → State → Val → Prop}
    {Q₂ : α → State → β → State → Val → Prop} (h₁ : CGood st k₁ P m Q₁)
    (hp : ∀ s a s' v, Inv s → P s v → Ext s s' → Q₁ s a s' v → P₂ a s' v)
    (h₂ : ∀ a, CGood st k₂ (P₂ a) (f a) (Q₂ a)) :
    CGood st (k₁ + k₂) P (m >>= f) fun s b s'' v =>
      ∃ a s', Ext s s' ∧ Ext s' s'' ∧ P s v ∧ Q₁ s a s' v ∧ Q₂ a s' b s'' v := by
  intro s val hi hc hsat hP
  rw [run_bind']
  obtain ⟨hi₁, hc₁, he₁, hst₁, val₁, ha₁, hsat₁, hq₁⟩ := h₁ s val hi hc hsat hP
  obtain ⟨hi₂, hc₂, he₂, hst₂, val₂, ha₂, hsat₂, hq₂⟩ := h₂ _ _ val₁ hi₁ hc₁ hsat₁ fun v hv =>
    hp _ _ _ v hi (hP v (ha₁.trans hv he₁.next)) he₁ (hq₁ v hv)
  refine ⟨hi₂, hc₂, he₁.trans he₂, by rw [hst₂, hst₁, Nat.add_assoc], val₂, ha₁.trans ha₂ he₁.next, hsat₂,
    fun v hv => ⟨_, _, he₁, he₂, hP v ((ha₁.trans ha₂ he₁.next).trans hv (he₁.trans he₂).next),
      hq₁ v (ha₂.trans hv he₂.next), hq₂ v hv⟩⟩

theorem CGood.weaken {α : Type} {k : ℕ} {P P' : State → Val → Prop} {m : M α}
    {Q Q' : State → α → State → Val → Prop} (h : CGood st k P m Q) (hp : ∀ s v, P' s v → P s v)
    (hq : ∀ s a s' v, Inv s → P' s v → Ext s s' → Q s a s' v → Q' s a s' v) : CGood st k P' m Q' := by
  intro s val hi hc hsat hP
  obtain ⟨hi', hc', he, hst, val', ha, hsat', hq'⟩ := h s val hi hc hsat fun v hv => hp s v (hP v hv)
  exact ⟨hi', hc', he, hst, val', ha, hsat', fun v hv => hq _ _ _ v hi (hP v (ha.trans hv he.next)) he (hq' v hv)⟩

theorem CGood.pre {α : Type} {k : ℕ} {P P' : State → Val → Prop} {m : M α} {Q : State → α → State → Val → Prop}
    (h : CGood st k P m Q) (hp : ∀ s v, P' s v → P s v) : CGood st k P' m Q :=
  h.weaken hp fun _ _ _ _ _ _ _ hq => hq

theorem CGood.kEq {α : Type} {k k' : ℕ} {P : State → Val → Prop} {m : M α} {Q : State → α → State → Val → Prop}
    (h : CGood st k P m Q) (hk : k = k') : CGood st k' P m Q := hk ▸ h

theorem CGood.pure' {α : Type} {P : State → Val → Prop} {a : α} {Q : State → α → State → Val → Prop}
    (h : ∀ s v, Inv s → P s v → Q s a s v) : CGood st 0 P (pure a) Q :=
  fun s val hi hc hsat hP => ⟨hi, hc, Ext.refl s, rfl, val, Agree.refl _ _, hsat, fun v hv => h s v hi (hP v hv)⟩

theorem CGood.get' {α : Type} {k : ℕ} {P : State → Val → Prop} {f : State → M α}
    {Q : State → α → State → Val → Prop} (h : ∀ s₀, CGood st k (fun s v => s = s₀ ∧ P s v) (f s₀) Q) :
    CGood st k P (get >>= f) Q :=
  fun s val hi hc hsat hP => h s s val hi hc hsat fun v hv => ⟨rfl, hP v hv⟩

/-- A contract from the soundness contract's invariant and extension. -/
theorem CGood.of_good {α : Type} {k : ℕ} {P : State → Val → Prop} {P₀ : State → Prop} {m : M α}
    {Q₀ : State → α → State → Prop} {Q : State → α → State → Val → Prop} (hg : Good P₀ m Q₀)
    (hp : ∀ s v, P s v → P₀ s)
    (h : ∀ s val, Inv s → Closed s → Sat st s val → (∀ v, Agree s.next val v → P s v) → Inv (m.run s).2 →
      Ext s (m.run s).2 → Q₀ s (m.run s).1 (m.run s).2 →
      Closed (m.run s).2 ∧ (m.run s).2.statement = s.statement + k ∧ ∃ val', Agree s.next val val' ∧
        Sat st (m.run s).2 val' ∧ ∀ v, Agree (m.run s).2.next val' v → Q s (m.run s).1 (m.run s).2 v) :
    CGood st k P m Q := by
  intro s val hi hc hsat hP
  obtain ⟨hi', he, hq⟩ := hg s hi (hp s val (hP val (Agree.refl _ _)))
  obtain ⟨hc', hst, rest⟩ := h s val hi hc hsat hP hi' he hq
  exact ⟨hi', hc', he, hst, rest⟩

end

/-! Values: `K` words, `E` elements and digests as limbs. -/

/-- A `K` word's limbs: the element and three zeros. -/
noncomputable def kVal (a : K) : Fin 4 → K := ![a, 0, 0, 0]

theorem toE_surjective (x : E) : ∃ a b c : K, toE a b c = x := by
  set pb := AdjoinRoot.powerBasis' extModulus_monic
  have hdim : pb.dim = 3 := extModulus_natDegree
  have hx := pb.basis.sum_repr x
  rw [PowerBasis.coe_basis] at hx
  let c : ℕ → K := fun i => if h : i < pb.dim then pb.basis.repr x ⟨i, h⟩ else 0
  have hc : ∀ i : Fin pb.dim, pb.basis.repr x i = c i := fun i => by simp [c, i.isLt]
  refine ⟨c 0, c 1, c 2, ?_⟩
  conv_rhs => rw [← hx]
  simp only [hc]
  rw [Fin.sum_univ_eq_sum_range (fun i => c i • pb.gen ^ i), hdim]
  simp [Finset.sum_range_succ, toE, emb, Algebra.smul_def, y, pb]

/-- An `E` element's limbs: its coordinates and a zero top limb. -/
noncomputable def eVal (x : E) : Fin 4 → K :=
  ![Classical.choose (toE_surjective x), Classical.choose (Classical.choose_spec (toE_surjective x)),
    Classical.choose (Classical.choose_spec (Classical.choose_spec (toE_surjective x))), 0]

theorem toE_eVal (x : E) : toE (eVal x 0) (eVal x 1) (eVal x 2) = x :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (toE_surjective x)))

theorem eVal_three (x : E) : eVal x 3 = 0 := rfl

theorem eq_eVal (f : Fin 4 → K) (h3 : f 3 = 0) : f = eVal (toE (f 0) (f 1) (f 2)) := by
  obtain ⟨h0, h1, h2⟩ := toE_injective _ _ _ _ _ _ (toE_eVal (toE (f 0) (f 1) (f 2))).symm
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem eVal_toE (a b c : K) : eVal (toE a b c) = ![a, b, c, 0] := (eq_eVal ![a, b, c, 0] rfl).symm

theorem ev_of_eVal {v : Val} {w : ℕ} {x : E} (h : v w = eVal x) : ev v w = x := by
  rw [ev, h, toE_eVal]

theorem eVal_of_ev {v : Val} {w : ℕ} (h3 : v w 3 = 0) : v w = eVal (ev v w) := eq_eVal _ h3

theorem eVal_injective {x y : E} (h : eVal x = eVal y) : x = y := by
  rw [← toE_eVal x, ← toE_eVal y, h]

theorem eVal_emb (a : K) : eVal (emb a) = kVal a := by
  rw [← toE_emb, eVal_toE]; rfl

theorem limbsOf_k (c : ℕ) : limbsOf [c, 0, 0, 0] = kVal (ofWord c) := by
  funext i; fin_cases i <;> simp [limbsOf, kVal, ofWord_zero]

theorem limbsOf_e (c0 c1 c2 : ℕ) :
    limbsOf [c0, c1, c2, 0] = eVal (toE (ofWord c0) (ofWord c1) (ofWord c2)) := by
  rw [eVal_toE]; funext i; fin_cases i <;> simp [limbsOf, ofWord_zero]

theorem limbsOf_eOne : limbsOf [1, 0, 0, 0] = eVal 1 := by
  rw [limbsOf_e, ofWord_one, ofWord_zero, toE_emb]; simp [emb]

theorem limbsOf_eZero : limbsOf [0, 0, 0, 0] = eVal 0 := by
  rw [limbsOf_e, ofWord_zero, toE_emb, emb_zero]

theorem limbsOf_kZero : limbsOf [0, 0, 0, 0] = kVal 0 := by
  rw [limbsOf_k, ofWord_zero]

theorem ev_agree {n : ℕ} {v v' : Val} (h : Agree n v v') {w : ℕ} (hw : w < n) : ev v' w = ev v w := by
  rw [ev, ev, h w hw]

/-- A digest's four words as limbs. -/
noncomputable def dVal (d : Fin 4 → BitVec 64) : Fin 4 → K := fun k => ofWord (d k).toNat

theorem words4_dVal (d : Fin 4 → BitVec 64) : words4 (dVal d) = d := by
  funext k
  rw [words4, dVal, toWord_ofWord _ (d k).isLt]
  simp

/-! Fresh wires, constants, unions, statement words and rows. -/

section

variable {st : ℕ → Fin 4 → K}

theorem Sat.same {s s' : State} {v : Val} (h : Sat st s v) (hu : s'.unions = s.unions) (he : s'.emul = s.emul)
    (hk : s'.exk = s.exk) (hh : s'.hash = s.hash) (hs : s'.split = s.split) (hc : s'.cast = s.cast)
    (hp : s'.pub = s.pub) : Sat st s' v :=
  h.step (fun _ h' => Or.inl (hu ▸ h')) (fun _ h' => Or.inl (he ▸ h')) (fun _ h' => Or.inl (hk ▸ h'))
    (fun _ h' => Or.inl (hh ▸ h')) (fun _ h' => Or.inl (hs ▸ h')) (fun _ h' => Or.inl (hc ▸ h'))
    fun _ _ h' => Or.inl (hp ▸ h')

/-- The precondition may assume the assignment satisfies the circuit so far. -/
theorem CGood.withSat {α : Type} {k : ℕ} {P : State → Val → Prop} {m : M α} {Q : State → α → State → Val → Prop}
    (h : CGood st k (fun s v => P s v ∧ Sat st s v) m Q) : CGood st k P m Q :=
  fun s val hi hc hsat hP => h s val hi hc hsat fun v hv => ⟨hP v hv, hsat.agree hi hc hv⟩

/-- The contract may depend on the starting state and assignment. -/
theorem CGood.intro {α : Type} {k : ℕ} {P : State → Val → Prop} {m : M α} {Q : State → α → State → Val → Prop}
    (h : ∀ s₀ val₀, CGood st k (fun s v => s = s₀ ∧ Agree s.next val₀ v ∧ P s v) m Q) : CGood st k P m Q :=
  fun s val hi hc hsat hP => h s val s val hi hc hsat fun v hv => ⟨rfl, hv, hP v hv⟩

theorem wire_run (s : State) : wire.run s = (s.next, { s with next := s.next + 1 }) := rfl

/-- `wire`: a fresh wire carrying any value. -/
theorem wire_cgood (x : Fin 4 → K) : CGood st 0 (fun _ _ => True) wire fun s w s' v =>
    w = s.next ∧ s'.next = s.next + 1 ∧ v w = x := by
  refine CGood.of_good wire_good (fun _ _ _ => trivial) fun s val hi hc hsat _ _ _ _ => ?_
  rw [wire_run]
  refine ⟨hc.same (Nat.le_succ _) rfl rfl rfl rfl rfl rfl, rfl, setW val s.next x, agree_setW _ _ _,
    (hsat.agree hi hc (agree_setW _ _ _)).same rfl rfl rfl rfl rfl rfl rfl, fun v hv => ⟨rfl, rfl, ?_⟩⟩
  rw [hv _ (Nat.lt_succ_self _), setW_self]

/-- `constant`: its wire carries the constant, made or cached. -/
theorem constant_cgood (kd : Kind) (lv : Limbs) : CGood st 0 (fun _ _ => True) (constant kd lv)
    fun _ w s' v => w < s'.next ∧ v w = limbsOf lv := by
  refine CGood.of_good (constant_good kd lv) (fun _ _ _ => trivial) fun s val hi hc hsat _ _ _ _ => ?_
  rw [constant_run]
  cases h : s.consts[(kd, lv)]? with
  | some w =>
    refine ⟨hc, rfl, val, Agree.refl _ _, hsat, fun v hv => ⟨hi.constsLt _ w h, ?_⟩⟩
    dsimp only
    rw [hv w (hi.constsLt _ w h)]
    exact hsat.pub w _ (hi.consts _ w h)
  | none =>
    refine ⟨hc.same (Nat.le_succ _) rfl rfl rfl rfl rfl rfl, rfl, setW val s.next (limbsOf lv), agree_setW _ _ _,
      ?_, fun v hv => ⟨Nat.lt_succ_self _, ?_⟩⟩
    · refine (hsat.agree hi hc (agree_setW _ _ _)).step (fun _ h' => Or.inl h') (fun _ h' => Or.inl h')
        (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ h' => Or.inl h')
        fun w src hp => ?_
      rcases Array.mem_push.mp hp with hp | hp
      · exact Or.inl hp
      · cases hp; exact Or.inr (setW_self _ _ _)
    · dsimp only
      rw [hv _ (Nat.lt_succ_self _), setW_self]

theorem kConst_cgood (c : ℕ) : CGood st 0 (fun _ _ => True) (kConst c) fun _ w s' v =>
    w < s'.next ∧ v w = kVal (ofWord c) :=
  (constant_cgood _ _).weaken (fun _ _ h => h) fun _ _ _ _ _ _ _ h => ⟨h.1, h.2.trans (limbsOf_k c)⟩

theorem eConst_cgood (c0 c1 c2 : ℕ) : CGood st 0 (fun _ _ => True) (eConst c0 c1 c2) fun _ w s' v =>
    w < s'.next ∧ v w = eVal (toE (ofWord c0) (ofWord c1) (ofWord c2)) :=
  (constant_cgood _ _).weaken (fun _ _ h => h) fun _ _ _ _ _ _ _ h => ⟨h.1, h.2.trans (limbsOf_e c0 c1 c2)⟩

theorem dConst_cgood (lv : Limbs) : CGood st 0 (fun _ _ => True) (dConst lv) fun _ w s' v =>
    w < s'.next ∧ v w = limbsOf lv :=
  constant_cgood _ _

theorem zero_cgood : CGood st 0 (fun _ _ => True) zero fun _ z s' v => z < s'.next ∧ v z = eVal 0 := by
  apply CGood.get'
  intro s₀
  cases h : s₀.units.eZero with
  | some w =>
    refine CGood.withSat (CGood.pure' ?_)
    rintro s v hs ⟨⟨rfl, -⟩, hsat⟩
    exact ⟨hs.pubLt _ (hs.eZero w h), (hsat.pub w _ (hs.eZero w h)).trans limbsOf_eZero⟩
  | none =>
    exact (eConst_cgood 0 0 0).weaken (fun _ _ _ => trivial) fun _ _ _ _ _ _ _ h =>
      ⟨h.1, by rw [h.2, ofWord_zero, toE_emb, emb_zero]⟩

theorem one_cgood : CGood st 0 (fun _ _ => True) one fun _ o s' v => o < s'.next ∧ v o = eVal 1 := by
  apply CGood.get'
  intro s₀
  cases h : s₀.units.eOne with
  | some w =>
    refine CGood.withSat (CGood.pure' ?_)
    rintro s v hs ⟨⟨rfl, -⟩, hsat⟩
    exact ⟨hs.constsLt _ _ (hs.eOne w h), (hsat.pub w _ (hs.consts _ w (hs.eOne w h))).trans limbsOf_eOne⟩
  | none =>
    exact (eConst_cgood 1 0 0).weaken (fun _ _ _ => trivial) fun _ _ _ _ _ _ _ h =>
      ⟨h.1, by rw [h.2, ← limbsOf_e, limbsOf_eOne]⟩

theorem kZero_cgood : CGood st 0 (fun _ _ => True) kZero fun _ z s' v => z < s'.next ∧ v z = kVal 0 := by
  apply CGood.get'
  intro s₀
  cases h : s₀.units.kZero with
  | some w =>
    refine CGood.withSat (CGood.pure' ?_)
    rintro s v hs ⟨⟨rfl, -⟩, hsat⟩
    exact ⟨hs.pubLt _ (hs.kZero w h), (hsat.pub w _ (hs.kZero w h)).trans limbsOf_kZero⟩
  | none =>
    exact (kConst_cgood 0).weaken (fun _ _ _ => trivial) fun _ _ _ _ _ _ _ h =>
      ⟨h.1, by rw [h.2, ofWord_zero]⟩

theorem union_run (a b : ℕ) (s : State) : (union a b).run s = ((), { s with unions := s.unions.push (a, b) }) := rfl

/-- `union`: wires carrying equal limbs held equal. -/
theorem union_cgood (a b : ℕ) : CGood st 0 (fun s v => a < s.next ∧ b < s.next ∧ v a = v b) (union a b)
    fun _ _ _ _ => True := by
  refine CGood.of_good (union_good a b) (fun _ _ _ => trivial) fun s val hi hc hsat hP _ _ _ => ?_
  obtain ⟨ha, hb, hab⟩ := hP val (Agree.refl _ _)
  rw [union_run]
  refine ⟨hc.step le_rfl (fun p hp => ?_) (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ h' => Or.inl h')
    (fun _ h' => Or.inl h') (fun _ h' => Or.inl h'), rfl, val, Agree.refl _ _,
    hsat.step (fun p hp => ?_) (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ h' => Or.inl h')
      (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ _ h' => Or.inl h'), fun _ _ => trivial⟩
  · rcases Array.mem_push.mp hp with hp | rfl
    · exact Or.inl hp
    · exact Or.inr ⟨ha, hb⟩
  · rcases Array.mem_push.mp hp with hp | rfl
    · exact Or.inl hp
    · exact Or.inr hab

theorem eqConstK_cgood (a c : ℕ) : CGood st 0 (fun s v => a < s.next ∧ v a = kVal (ofWord c)) (eqConstK a c)
    fun _ _ _ _ => True :=
  (CGood.bind ((kConst_cgood c).pre (P' := fun s v => a < s.next ∧ v a = kVal (ofWord c))
    fun _ _ _ => trivial) (P₂ := fun w s v => a < s.next ∧ w < s.next ∧ v a = v w)
    (fun _ _ _ _ _ hp he hq => ⟨lt_of_lt_of_le hp.1 he.next, hq.1, hp.2.trans hq.2.symm⟩)
    fun w => union_cgood a w).weaken (fun _ _ h => h) fun _ _ _ _ _ _ _ _ => trivial

theorem eqConstE_cgood (a c0 c1 c2 : ℕ) :
    CGood st 0 (fun s v => a < s.next ∧ v a = eVal (toE (ofWord c0) (ofWord c1) (ofWord c2))) (eqConstE a c0 c1 c2)
    fun _ _ _ _ => True :=
  (CGood.bind ((eConst_cgood c0 c1 c2).pre
    (P' := fun s v => a < s.next ∧ v a = eVal (toE (ofWord c0) (ofWord c1) (ofWord c2))) fun _ _ _ => trivial) (P₂ := fun w s v => a < s.next ∧ w < s.next ∧ v a = v w)
    (fun _ _ _ _ _ hp he hq => ⟨lt_of_lt_of_le hp.1 he.next, hq.1, hp.2.trans hq.2.symm⟩)
    fun w => union_cgood a w).weaken (fun _ _ h => h) fun _ _ _ _ _ _ _ _ => trivial

theorem expose_run (w : ℕ) (s : State) : (expose w).run s =
    (s.statement, { s with statement := s.statement + 1, pub := s.pub.push (w, .statement s.statement) }) := rfl

/-- `expose`: a wire carrying the next statement word. -/
theorem expose_cgood (w : ℕ) : CGood st 1 (fun s v => w < s.next ∧ v w = st s.statement) (expose w)
    fun s i s' _ => i = s.statement ∧ s'.next = s.next := by
  refine CGood.of_good (expose_good w) (fun s _ h u hu => by simp at hu; subst hu; exact h.1)
    fun s val hi hc hsat hP _ _ _ => ?_
  obtain ⟨-, hw⟩ := hP val (Agree.refl _ _)
  rw [expose_run]
  refine ⟨hc.same le_rfl rfl rfl rfl rfl rfl rfl, rfl, val, Agree.refl _ _,
    hsat.step (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ h' => Or.inl h')
      (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun u src hp => ?_), fun _ _ => ⟨rfl, rfl⟩⟩
  rcases Array.mem_push.mp hp with hp | hp
  · exact Or.inl hp
  · cases hp; exact Or.inr hw

/-- A row of table `t` the assignment satisfies. -/
def TSat (t : Table) (v : Val) (r : List ℕ) : Prop :=
  match t with
  | .emul => RowSat Rec.emul (fun _ => True) v r
  | .exk => RowSat Rec.exk (fun _ => True) v r
  | .hash => RowSat Rec.hash HashRow v r
  | .split => RowSat Rec.split (fun col => ∀ id ∈ splitIdentities, id.eval col = 0) v r
  | .cast => RowSat Rec.cast (fun _ => True) v r
  | .pub => True

/-- `row`: a row the assignment satisfies. -/
theorem row_cgood (t : Table) (r : List ℕ) (ht : t ≠ .emul) :
    CGood st 0 (fun s v => Wires r s ∧ r ≠ [] ∧ TSat t v r) (row t r) fun _ _ s' _ =>
      (t = .exk → r ∈ s'.exk) ∧ (t = .hash → r ∈ s'.hash) ∧ (t = .split → r ∈ s'.split) ∧
        (t = .cast → r ∈ s'.cast) := by
  refine CGood.of_good (row_good t r ht) (fun _ _ _ => trivial) fun s val hi hc hsat hP _ _ hq => ?_
  obtain ⟨hw, hne, hsr⟩ := hP val (Agree.refl _ _)
  have hlt := rowLt_of_wires hw hne
  cases t with
  | emul => exact absurd rfl ht
  | pub => exact ⟨hc, rfl, val, Agree.refl _ _, hsat, fun _ _ => hq⟩
  | exk | hash | split | cast =>
    refine ⟨hc.step le_rfl ?_ ?_ ?_ ?_ ?_ ?_, rfl, val, Agree.refl _ _, hsat.step ?_ ?_ ?_ ?_ ?_ ?_ ?_,
      fun _ _ => hq⟩ <;>
    first
      | exact fun _ h' => Or.inl h'
      | exact fun _ _ h' => Or.inl h'
      | (intro r' hr'; rcases Array.mem_push.mp hr' with h' | rfl; exacts [Or.inl h', Or.inr hlt])
      | (intro r' hr'; rcases Array.mem_push.mp hr' with h' | rfl; exacts [Or.inl h', Or.inr hsr])

end

/-! Arithmetic. -/

section

variable {st : ℕ → Fin 4 → K}

theorem wires_cons {w : ℕ} {ws : List ℕ} {s : State} : Wires (w :: ws) s ↔ w < s.next ∧ Wires ws s :=
  List.forall_mem_cons

theorem wires_nil {s : State} : Wires [] s := fun _ h => absurd h List.not_mem_nil

theorem wires2 {a b : ℕ} {s : State} (ha : a < s.next) (hb : b < s.next) : Wires [a, b] s :=
  wires_cons.2 ⟨ha, wires_cons.2 ⟨hb, wires_nil⟩⟩

theorem wires3 {a b c : ℕ} {s : State} (ha : a < s.next) (hb : b < s.next) (hc : c < s.next) :
    Wires [a, b, c] s :=
  wires_cons.2 ⟨ha, wires_cons.2 ⟨hb, wires_cons.2 ⟨hc, wires_nil⟩⟩⟩

/-- Limb `i` of `x`, zero past four. -/
noncomputable def lim (x : Fin 4 → K) (i : ℕ) : K := if h : i < 4 then x ⟨i, h⟩ else 0

/-- The `EMUL` columns of `a`, `b` and `d`. -/
noncomputable def emulCol (xa xb xd : Fin 4 → K) (j : ℕ) : K :=
  if j < 3 then lim xa j else if j < 6 then lim xb (j - 3) else lim xd (j - 6)

theorem emul_three {s : State} {val : Val} (h : Sat st s val) {a b d c : ℕ} (hr : [a, b, d, c] ∈ s.emul) :
    val c 3 = 0 := by
  obtain ⟨col, -, hl⟩ := h.emul _ hr
  have h3 : limbs Rec.emul 3 col 3 = val c 3 := hl 3 (by decide) 3
  rw [← h3]
  exact (emul_spec col).2

/-- An `EMUL` row is satisfied when its output carries `a·b + d`. -/
theorem emul_rowSat (val : Val) (a b d c : ℕ) (ha : val a 3 = 0) (hb : val b 3 = 0) (hd : val d 3 = 0)
    (hc : val c = eVal (ev val a * ev val b + ev val d)) : RowSat Rec.emul (fun _ => True) val [a, b, d, c] := by
  set col := emulCol (val a) (val b) (val d)
  have hA : slotE col (Rec.emul.getD 0 []) = ev val a := by
    simp [slotE, emul_eq, eSlot, Form.eval, ev, col, emulCol, lim]
  have hB : slotE col (Rec.emul.getD 1 []) = ev val b := by
    simp [slotE, emul_eq, eSlot, Form.eval, ev, col, emulCol, lim]
  have hD : slotE col (Rec.emul.getD 2 []) = ev val d := by
    simp [slotE, emul_eq, eSlot, Form.eval, ev, col, emulCol, lim]
  refine ⟨col, trivial, fun j hj i => ?_⟩
  have hl : Rec.emul.length = 4 := rfl
  rw [hl] at hj
  interval_cases j
  · fin_cases i <;> simp [limbs, emul_eq, eSlot, Form.eval, Form.zero, ofWord_zero, col, emulCol, lim, ha]
  · fin_cases i <;> simp [limbs, emul_eq, eSlot, Form.eval, Form.zero, ofWord_zero, col, emulCol, lim, hb]
  · fin_cases i <;> simp [limbs, emul_eq, eSlot, Form.eval, Form.zero, ofWord_zero, col, emulCol, lim, hd]
  · have hf := eq_eVal (fun i : Fin 4 => limbs Rec.emul 3 col i) (emul_spec col).2
    have ht : toE (limbs Rec.emul 3 col 0) (limbs Rec.emul 3 col 1) (limbs Rec.emul 3 col 2) =
        ev val a * ev val b + ev val d := by
      rw [← slotE_limbs, (emul_spec col).1, hA, hB, hD]
    show limbs Rec.emul 3 col i = val c i
    rw [hc, ← ht]
    exact congrFun hf i

theorem emul_cgood (a b d : ℕ) : CGood st 0 (fun s v => Wires [a, b, d] s ∧ v a 3 = 0 ∧ v b 3 = 0 ∧ v d 3 = 0)
    (emul a b d) fun _ c s' v => c < s'.next ∧ v c = eVal (ev v a * ev v b + ev v d) := by
  refine CGood.of_good (emul_good a b d) (fun s v h => ⟨h.1 a (by simp), h.1 b (by simp), h.1 d (by simp)⟩)
    fun s val hi hc hsat hP _ _ _ => ?_
  obtain ⟨hw, ha3, hb3, hd3⟩ := hP val (Agree.refl _ _)
  have ha := hw a (by simp)
  have hb := hw b (by simp)
  have hd := hw d (by simp)
  rw [emul_run]
  cases h : s.arith[(Table.emul.tag, emulKey s.units a b d)]? with
  | some c =>
    have hcl := hi.arithLt _ c h
    refine ⟨hc, rfl, val, Agree.refl _ _, hsat, fun v hv => ⟨hcl, ?_⟩⟩
    dsimp only
    generalize hk : emulKey s.units a b d = key at h
    obtain ⟨k0, k1, k2⟩ := key
    obtain ⟨a', b', d', hr, hk'⟩ := hi.arithE k0 k1 k2 c h
    have hev : ev val c = ev val a * ev val b + ev val d := by
      rw [emul_row_ev hsat hr]
      exact emulKey_sem s.units val (hi.one_ev hsat) a' b' d' a b d (hk'.trans hk.symm)
    rw [hv c hcl, ev_agree hv ha, ev_agree hv hb, ev_agree hv hd, ← hev]
    exact eVal_of_ev (emul_three hsat hr)
  | none =>
    dsimp only
    set x := eVal (ev val a * ev val b + ev val d)
    have hag := agree_setW val s.next x
    refine ⟨hc.step (Nat.le_succ _) (fun _ h' => Or.inl h') (fun r hr => ?_) (fun _ h' => Or.inl h')
      (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ h' => Or.inl h'), rfl, setW val s.next x, hag,
      (hsat.agree hi hc hag).step (fun _ h' => Or.inl h') (fun r hr => ?_) (fun _ h' => Or.inl h')
        (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ _ h' => Or.inl h'),
      fun v hv => ⟨Nat.lt_succ_self _, ?_⟩⟩
    · rcases Array.mem_push.mp hr with hr | rfl
      · exact Or.inl hr
      · refine Or.inr (rowLt_of_wires (fun w hw' => ?_) (by simp))
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl | rfl | rfl <;> simp only [emulFresh] <;> omega
    · rcases Array.mem_push.mp hr with hr | rfl
      · exact Or.inl hr
      · refine Or.inr (emul_rowSat _ a b d s.next (by rw [hag a ha]; exact ha3) (by rw [hag b hb]; exact hb3)
          (by rw [hag d hd]; exact hd3) ?_)
        rw [setW_self, ev_agree hag ha, ev_agree hag hb, ev_agree hag hd]
    · have hn : s.next < s.next + 1 := Nat.lt_succ_self _
      have hv' : Agree s.next val v := hag.trans hv (Nat.le_succ _)
      rw [hv _ hn, setW_self, ev_agree hv' ha, ev_agree hv' hb, ev_agree hv' hd]

theorem add_cgood (a d : ℕ) : CGood st 0 (fun s v => Wires [a, d] s ∧ v a 3 = 0 ∧ v d 3 = 0) (add a d)
    fun _ r s' v => r < s'.next ∧ v r = eVal (ev v a + ev v d) := by
  apply CGood.withSat
  apply CGood.get'
  intro s₀
  dsimp only
  split_ifs with h1 h2
  · refine CGood.pure' ?_
    rintro s v hs ⟨rfl, ⟨hw, ha3, -⟩, hsat⟩
    refine ⟨hw a (by simp), ?_⟩
    rw [hs.zero_ev hsat d h1, add_zero]
    exact eVal_of_ev ha3
  · refine CGood.pure' ?_
    rintro s v hs ⟨rfl, ⟨hw, -, hd3⟩, hsat⟩
    refine ⟨hw d (by simp), ?_⟩
    rw [hs.zero_ev hsat a h2, zero_add]
    exact eVal_of_ev hd3
  · refine (CGood.bind (one_cgood.pre fun _ _ _ => trivial)
      (P₂ := fun o s v => Wires [a, o, d] s ∧ v a 3 = 0 ∧ v o 3 = 0 ∧ v d 3 = 0 ∧ ev v o = 1) ?_
      fun o => (emul_cgood a o d).pre fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩).weaken (fun _ _ h => h) ?_
    · rintro s o s' v hs ⟨-, ⟨hw, ha3, hd3⟩, -⟩ he ⟨ho, hov⟩
      exact ⟨wires3 (lt_of_lt_of_le (hw a (by simp)) he.next) ho (lt_of_lt_of_le (hw d (by simp)) he.next), ha3,
        by rw [hov]; rfl, hd3, ev_of_eVal hov⟩
    · rintro s r s'' v hs - - ⟨o, s', -, -, -, ⟨-, hov⟩, hr, hrv⟩
      refine ⟨hr, ?_⟩
      rw [hrv, ev_of_eVal hov, mul_one]

theorem mulAdd_cgood (a b d : ℕ) :
    CGood st 0 (fun s v => Wires [a, b, d] s ∧ v a 3 = 0 ∧ v b 3 = 0 ∧ v d 3 = 0) (mulAdd a b d)
      fun _ r s' v => r < s'.next ∧ v r = eVal (ev v a * ev v b + ev v d) := by
  apply CGood.withSat
  apply CGood.get'
  intro s₀
  dsimp only
  split_ifs with h1 h2 h3
  · refine CGood.pure' ?_
    rintro s v hs ⟨rfl, ⟨hw, -, -, hd3⟩, hsat⟩
    refine ⟨hw d (by simp), ?_⟩
    rcases h1 with h | h <;> rw [hs.zero_ev hsat _ h] <;> simp only [zero_mul, mul_zero, zero_add] <;>
      exact eVal_of_ev hd3
  · refine ((add_cgood a d).pre fun s v h => ⟨wires2 (h.2.1.1 a (by simp)) (h.2.1.1 d (by simp)), h.2.1.2.1,
      h.2.1.2.2.2⟩).weaken (fun _ _ h => h) ?_
    rintro s r s' v hs ⟨rfl, -, hsat⟩ he ⟨hr, hrv⟩
    refine ⟨hr, ?_⟩
    rw [hrv, hs.one_ev hsat b h2, mul_one]
  · refine ((add_cgood b d).pre fun s v h => ⟨wires2 (h.2.1.1 b (by simp)) (h.2.1.1 d (by simp)), h.2.1.2.2.1,
      h.2.1.2.2.2⟩).weaken (fun _ _ h => h) ?_
    rintro s r s' v hs ⟨rfl, -, hsat⟩ he ⟨hr, hrv⟩
    refine ⟨hr, ?_⟩
    rw [hrv, hs.one_ev hsat a h3, one_mul]
  · exact (emul_cgood a b d).pre fun _ _ h => h.2.1

/-- The `EXK` columns of `a`, `k` and `d`. -/
noncomputable def exkCol (xa xk xd : Fin 4 → K) (j : ℕ) : K :=
  if j < 3 then lim xa j else if j = 3 then xk 0 else lim xd (j - 4)

theorem exk_three {s : State} {val : Val} (h : Sat st s val) {a k d c : ℕ} (hr : [a, k, d, c] ∈ s.exk) :
    val c 3 = 0 := by
  obtain ⟨col, -, hl⟩ := h.exk _ hr
  have h3 : limbs Rec.exk 3 col 3 = val c 3 := hl 3 (by decide) 3
  rw [← h3]
  exact (exk_spec col).2

theorem exk_rowSat (val : Val) (a k d c : ℕ) (ha : val a 3 = 0) (hk : val k = kVal (val k 0)) (hd : val d 3 = 0)
    (hc : val c = eVal (ev val a * emb (val k 0) + ev val d)) : RowSat Rec.exk (fun _ => True) val [a, k, d, c] := by
  set col := exkCol (val a) (val k) (val d)
  have hA : slotE col (Rec.exk.getD 0 []) = ev val a := by
    simp [slotE, Rec.exk, eSlot, Form.eval, ev, col, exkCol, lim]
  have hK : ((Rec.exk.getD 1 []).getD 0 .zero).eval col = val k 0 := by
    simp [Rec.exk, kSlot, Form.eval, col, exkCol]
  have hD : slotE col (Rec.exk.getD 2 []) = ev val d := by
    simp [slotE, Rec.exk, eSlot, Form.eval, ev, col, exkCol, lim]
  refine ⟨col, trivial, fun j hj i => ?_⟩
  have hl : Rec.exk.length = 4 := rfl
  rw [hl] at hj
  interval_cases j
  · fin_cases i <;> simp [limbs, Rec.exk, eSlot, Form.eval, Form.zero, ofWord_zero, col, exkCol, lim, ha]
  · show limbs Rec.exk 1 col i = val k i
    rw [hk]; fin_cases i <;> simp [limbs, Rec.exk, kSlot, Form.eval, Form.zero, ofWord_zero, col, exkCol, kVal]
  · fin_cases i <;> simp [limbs, Rec.exk, eSlot, Form.eval, Form.zero, ofWord_zero, col, exkCol, lim, hd]
  · have hf := eq_eVal (fun i : Fin 4 => limbs Rec.exk 3 col i) (exk_spec col).2
    have ht : toE (limbs Rec.exk 3 col 0) (limbs Rec.exk 3 col 1) (limbs Rec.exk 3 col 2) =
        ev val a * emb (val k 0) + ev val d := by
      rw [← slotE_limbs, (exk_spec col).1, hA, hK, hD]
    show limbs Rec.exk 3 col i = val c i
    rw [hc, ← ht]
    exact congrFun hf i

theorem mulKAdd_run_zero (a k d : ℕ) (s : State) (h1 : s.units.eZero = some a ∨ s.units.kZero = some k) :
    (mulKAdd a k d).run s = (d, s) := by
  unfold mulKAdd
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.run, if_pos h1] <;> rfl

theorem mulKAdd_run_one (a k d : ℕ) (s : State) (h1 : ¬(s.units.eZero = some a ∨ s.units.kZero = some k))
    (h2 : s.units.kOne = some k) : (mulKAdd a k d).run s = (add a d).run s := by
  unfold mulKAdd
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.run, if_neg h1, if_pos h2] <;> rfl

theorem mulKAdd_run_cached (a k d c : ℕ) (s : State) (h1 : ¬(s.units.eZero = some a ∨ s.units.kZero = some k))
    (h2 : ¬s.units.kOne = some k) (h3 : s.arith[(Table.exk.tag, a, k, d)]? = some c) :
    (mulKAdd a k d).run s = (c, s) := by
  unfold mulKAdd
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.run, if_neg h1, if_neg h2, h3] <;> rfl

theorem mulKAdd_run_fresh (a k d : ℕ) (s : State) (h1 : ¬(s.units.eZero = some a ∨ s.units.kZero = some k))
    (h2 : ¬s.units.kOne = some k) (h3 : s.arith[(Table.exk.tag, a, k, d)]? = none) :
    (mulKAdd a k d).run s = (s.next, exkFresh s a k d) := by
  unfold mulKAdd
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.run, if_neg h1, if_neg h2, h3] <;> rfl

theorem mulKAdd_cgood (a k d : ℕ) :
    CGood st 0 (fun s v => Wires [a, k, d] s ∧ v a 3 = 0 ∧ v k = kVal (v k 0) ∧ v d 3 = 0) (mulKAdd a k d)
      fun _ r s' v => r < s'.next ∧ v r = eVal (ev v a * emb (v k 0) + ev v d) := by
  intro s val hi hc hsat hP
  obtain ⟨hw, ha3, hk3, hd3⟩ := hP val (Agree.refl _ _)
  have ha := hw a (by simp)
  have hk := hw k (by simp)
  have hd := hw d (by simp)
  by_cases h1 : s.units.eZero = some a ∨ s.units.kZero = some k
  · rw [mulKAdd_run_zero a k d s h1]
    refine ⟨hi, hc, Ext.refl s, rfl, val, Agree.refl _ _, hsat, fun v hv => ⟨hd, ?_⟩⟩
    have hsv := hsat.agree hi hc hv
    have hd3' : v d 3 = 0 := by rw [hv d hd]; exact hd3
    rcases h1 with h | h
    · rw [hi.zero_ev hsv a h, zero_mul, zero_add]; exact eVal_of_ev hd3'
    · rw [emb_limb_zero v k (hsv.pub _ _ (hi.kZero k h)), mul_zero, zero_add]; exact eVal_of_ev hd3'
  by_cases h2 : s.units.kOne = some k
  · rw [mulKAdd_run_one a k d s h1 h2]
    obtain ⟨hi', hc', he', hst', val', ha', hsat', hq'⟩ := add_cgood (st := st) a d s val hi hc hsat fun v hv =>
      ⟨wires2 ha hd, by rw [hv a ha]; exact ha3, by rw [hv d hd]; exact hd3⟩
    refine ⟨hi', hc', he', hst', val', ha', hsat', fun v hv => ?_⟩
    obtain ⟨hr, hrv⟩ := hq' v hv
    refine ⟨hr, ?_⟩
    have hsv : Sat st s v := (hsat'.agree hi' hc' hv).mono he'
    rw [hrv, emb_limb_one v k (hsv.pub _ _ (hi.kOne k h2)), mul_one]
  cases h3 : s.arith[(Table.exk.tag, a, k, d)]? with
  | some c =>
    rw [mulKAdd_run_cached a k d c s h1 h2 h3]
    have hcl := hi.arithLt _ c h3
    have hr := hi.arithK a k d c h3
    refine ⟨hi, hc, Ext.refl s, rfl, val, Agree.refl _ _, hsat, fun v hv => ⟨hcl, ?_⟩⟩
    have hsv := hsat.agree hi hc hv
    rw [← exk_row_ev hsv hr]
    exact eVal_of_ev (exk_three hsv hr)
  | none =>
    obtain ⟨hi', he', -⟩ := mulKAdd_good a k d s hi hw
    rw [mulKAdd_run_fresh a k d s h1 h2 h3] at hi' he' ⊢
    set x := eVal (ev val a * emb (val k 0) + ev val d)
    have hag := agree_setW val s.next x
    refine ⟨hi', hc.step (Nat.le_succ _) (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun r hr => ?_)
      (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ h' => Or.inl h'), he', rfl, setW val s.next x, hag,
      (hsat.agree hi hc hag).step (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun r hr => ?_)
        (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ h' => Or.inl h') (fun _ _ h' => Or.inl h'),
      fun v hv => ⟨Nat.lt_succ_self _, ?_⟩⟩
    · rcases Array.mem_push.mp hr with hr | rfl
      · exact Or.inl hr
      · refine Or.inr (rowLt_of_wires (fun w hw' => ?_) (by simp))
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl | rfl | rfl <;> simp only [exkFresh] <;> omega
    · rcases Array.mem_push.mp hr with hr | rfl
      · exact Or.inl hr
      · refine Or.inr (exk_rowSat _ a k d s.next (by rw [hag a ha]; exact ha3) (by rw [hag k hk]; exact hk3)
          (by rw [hag d hd]; exact hd3) ?_)
        rw [setW_self, ev_agree hag ha, hag k hk, ev_agree hag hd]
    · have hv' : Agree s.next val v := hag.trans hv (Nat.le_succ _)
      show v s.next = _
      rw [hv _ (Nat.lt_succ_self _), setW_self, ev_agree hv' ha, hv' k hk, ev_agree hv' hd]

theorem mulConstAdd_cgood (a c0 c1 c2 d : ℕ) :
    CGood st 0 (fun s v => Wires [a, d] s ∧ v a 3 = 0 ∧ v d 3 = 0) (mulConstAdd a c0 c1 c2 d)
      fun _ r s' v => r < s'.next ∧ v r = eVal (ev v a * toE (ofWord c0) (ofWord c1) (ofWord c2) + ev v d) := by
  unfold mulConstAdd
  split_ifs with h
  · refine (CGood.bind (kConst_cgood c0 |>.pre fun _ _ _ => trivial)
      (P₂ := fun k s v => Wires [a, k, d] s ∧ v a 3 = 0 ∧ v k = kVal (ofWord c0) ∧ v d 3 = 0) ?_
      fun k => (mulKAdd_cgood a k d).pre fun _ _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; rfl, h.2.2.2⟩).weaken
      (fun _ _ h => h) ?_
    · rintro s k s' v hs ⟨hw, ha3, hd3⟩ he ⟨hk, hkv⟩
      exact ⟨wires3 (lt_of_lt_of_le (hw a (by simp)) he.next) hk (lt_of_lt_of_le (hw d (by simp)) he.next), ha3,
        hkv, hd3⟩
    · rintro s r s'' v hs - - ⟨k, s', -, -, -, ⟨-, hkv⟩, hr, hrv⟩
      refine ⟨hr, ?_⟩
      rw [hrv, hkv, h.1, h.2, ofWord_zero, toE_emb]
      rfl
  · refine (CGood.bind (eConst_cgood c0 c1 c2 |>.pre fun _ _ _ => trivial)
      (P₂ := fun c s v => Wires [a, c, d] s ∧ v a 3 = 0 ∧ v c = eVal (toE (ofWord c0) (ofWord c1) (ofWord c2)) ∧
        v d 3 = 0) ?_
      fun c => (mulAdd_cgood a c d).pre fun _ _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; rfl, h.2.2.2⟩).weaken
      (fun _ _ h => h) ?_
    · rintro s c s' v hs ⟨hw, ha3, hd3⟩ he ⟨hc, hcv⟩
      exact ⟨wires3 (lt_of_lt_of_le (hw a (by simp)) he.next) hc (lt_of_lt_of_le (hw d (by simp)) he.next), ha3,
        hcv, hd3⟩
    · rintro s r s'' v hs - - ⟨c, s', -, -, -, ⟨-, hcv⟩, hr, hrv⟩
      refine ⟨hr, ?_⟩
      rw [hrv, ev_of_eVal hcv]

end


/-! Lists of wires and `CAST` views. -/

section

variable {st : ℕ → Fin 4 → K}

theorem getD_mem {l : List ℕ} {j : ℕ} (h : j < l.length) : l.getD j 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- `mapM` of steps each giving a wire meeting `R`, from states meeting a stable `P`. -/
theorem mapM_cgood {β : Type} (P : State → Val → Prop) (hP : ∀ s s' v, P s v → Ext s s' → P s' v)
    (f : β → M ℕ) (R : β → ℕ → Val → Prop) (hf : ∀ x, CGood st 0 P (f x) fun _ y s' v => R x y v ∧ y < s'.next) :
    ∀ l : List β, CGood st 0 P (l.mapM f) fun _ ys s' v =>
      ys.length = l.length ∧ (∀ i (hi : i < l.length) (hy : i < ys.length), R l[i] ys[i] v) ∧ Wires ys s' := by
  intro l
  induction l with
  | nil => exact CGood.pure' fun _ _ _ _ => ⟨rfl, fun i hi => absurd hi (by simp), fun _ h => absurd h (by simp)⟩
  | cons x xs ih =>
    rw [List.mapM_cons]
    refine ((CGood.bind (hf x) (P₂ := fun _ s v => P s v) (fun _ _ _ _ _ h he _ => hP _ _ _ h he) fun y =>
      CGood.bind ih (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun ys =>
        CGood.pure' (Q := fun _ r s' _ => r = y :: ys) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_).kEq rfl
    rintro s r s3 v hs - - ⟨y, s1, -, he1, -, ⟨hR, hy⟩, ys, s2, -, he2, -, ⟨hlen, hRs, hw⟩, rfl⟩
    refine ⟨by simp [hlen], fun i hi hy' => ?_, fun w hw' => ?_⟩
    · cases i with
      | zero => exact hR
      | succ i => exact hRs i (by simpa using hi) (by simpa using hy')
    · rcases List.mem_cons.mp hw' with rfl | hw'
      · exact lt_of_lt_of_le hy he1.next
      · exact lt_of_lt_of_le (hw w hw') he2.next

/-- The limbs slot `j` of a `CAST` row takes from columns `col`. -/
noncomputable def castSlot (col : ℕ → K) (j : ℕ) : Fin 4 → K := fun i => limbs Rec.cast j col i

theorem castSlot_digest (col : ℕ → K) : castSlot col 0 = fun i : Fin 4 => col i := by
  funext i; fin_cases i <;> rfl

theorem castSlot_element (col : ℕ → K) : castSlot col 1 = ![col 0, col 1, col 2, 0] := by
  funext i; fin_cases i <;> simp [castSlot, limbs, Rec.cast, eSlot, Form.eval, Form.zero, ofWord_zero]

theorem castSlot_word (col : ℕ → K) (w : Fin 4) : castSlot col (4 + w) = kVal (col w) := by
  funext i
  fin_cases w <;> fin_cases i <;> simp [castSlot, limbs, Rec.cast, kSlot, Form.eval, Form.zero, ofWord_zero, kVal]

/-- `cast_row`: a `CAST` row of columns `col`, the given wires carrying their slots' limbs. -/
theorem castRow_cgood (given : List (ℕ × ℕ)) (col : ℕ → K) :
    CGood st 0 (fun s v => Wires (given.map (·.2)) s ∧
      ∀ j < 8, ∀ p, given.find? (·.1 = j) = some p → v p.2 = castSlot col j) (castRow given)
      fun _ ws s' v => ws.length = 8 ∧ Wires ws s' ∧ ws ∈ s'.cast ∧ ∀ j < 8, v (ws.getD j 0) = castSlot col j := by
  have hstep : ∀ j : ℕ, CGood st 0 (fun s v => Wires (given.map (·.2)) s ∧
      ∀ j < 8, ∀ p, given.find? (·.1 = j) = some p → v p.2 = castSlot col j)
      (match given.find? (·.1 = j) with
        | some (_, w) => pure w
        | none => wire) fun _ y s' v => (j < 8 → v y = castSlot col j) ∧ y < s'.next := by
    intro j
    cases h : given.find? (·.1 = j) with
    | some p =>
      obtain ⟨i, w⟩ := p
      exact CGood.pure' fun s v _ hp => ⟨fun hj => hp.2 j hj _ h,
        hp.1 w (List.mem_map.mpr ⟨(i, w), List.mem_of_find?_eq_some h, rfl⟩)⟩
    | none =>
      exact ((wire_cgood (castSlot col j)).pre fun _ _ _ => trivial).weaken (fun _ _ h => h)
        fun _ _ _ _ _ _ _ hq => ⟨fun _ => hq.2.2, by rw [hq.2.1, hq.1]; exact Nat.lt_succ_self _⟩
  refine ((CGood.bind (mapM_cgood _ (fun _ _ _ h he => ⟨h.1.mono he, h.2⟩) _ _ hstep (List.range 8))
    (P₂ := fun ws s v => Wires ws s ∧ ws ≠ [] ∧ TSat .cast v ws ∧ ws.length = 8 ∧
      ∀ j < 8, v (ws.getD j 0) = castSlot col j) ?_ fun ws =>
      CGood.bind ((row_cgood .cast ws (by decide)).pre fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
        (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun _ =>
        CGood.pure' (Q := fun _ r s' _ => r = ws) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_).kEq rfl
  · rintro s ws s' v hs - he ⟨hlen, hR, hw⟩
    simp only [List.length_range] at hlen
    have hget : ∀ j < 8, v (ws.getD j 0) = castSlot col j := by
      intro j hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      have := hR j (by simpa using hj) (by omega)
      simp only [List.getElem_range] at this
      exact this hj
    refine ⟨hw, by rintro rfl; simp at hlen, ⟨col, trivial, fun j hj i => ?_⟩, hlen, hget⟩
    have hj' : j < 8 := hj
    rw [hget j hj']
    rfl
  · rintro s r s3 v hs - - ⟨ws, s1, -, he1, -, -, u, s2, -, he2, ⟨hw, -, -, hlen, hget⟩, ⟨-, -, -, hc⟩, rfl⟩
    exact ⟨hlen, hw.mono he1, he2.cast _ (hc rfl), hget⟩

theorem eToK_cgood (e : ℕ) : CGood st 0 (fun s v => e < s.next ∧ v e 3 = 0) (eToK e) fun _ ks s' v =>
    ks.length = 3 ∧ Wires ks s' ∧ ∀ i : Fin 4, i.val < 3 → v (ks.getD i 0) = kVal (v e i) := by
  apply CGood.intro
  intro s₀ val₀
  unfold eToK
  refine (CGood.bind ((castRow_cgood [(1, e)] (lim (val₀ e))).pre fun s v h => ⟨?_, ?_⟩)
    (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun ws =>
      CGood.pure' (Q := fun _ r s' _ => r = (ws.drop 4).take 3) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_
  · intro u hu; simp at hu; subst hu; exact h.2.2.1
  · obtain ⟨rfl, hag, he, he3⟩ := h
    intro j hj p hp
    simp only [List.find?_cons, List.find?_nil] at hp
    split at hp
    · rename_i hj1
      cases hp
      simp only [decide_eq_true_eq] at hj1
      subst hj1
      have he3' : val₀ e 3 = 0 := by rw [← hag e he]; exact he3
      rw [castSlot_element, hag e he]
      funext i
      fin_cases i <;> simp [lim, he3']
    · cases hp
  · rintro s r s2 v hs ⟨rfl, hag, he, -⟩ - ⟨ws, s1, -, he1, -, ⟨hlen, hw, -, hget⟩, rfl⟩
    have hd : ∀ i < 3, ((ws.drop 4).take 3).getD i 0 = ws.getD (4 + i) 0 := by
      intro i hi; simp [List.getD_eq_getElem?_getD, hi, List.getElem?_drop]
    refine ⟨by simp [hlen], fun w hw' => ?_, fun i hi => ?_⟩
    · exact (hw.mono he1) w (List.mem_of_mem_drop (List.mem_of_mem_take hw'))
    · rw [hd i hi, hget (4 + i) (by omega), castSlot_word (lim (val₀ e)) i, hag e he]
      simp [lim]

theorem kToE_cgood (k0 k1 k2 : ℕ) :
    CGood st 0 (fun s v => Wires [k0, k1, k2] s ∧ v k0 = kVal (v k0 0) ∧ v k1 = kVal (v k1 0) ∧
      v k2 = kVal (v k2 0)) (kToE k0 k1 k2)
      fun _ r s' v => r < s'.next ∧ v r = ![v k0 0, v k1 0, v k2 0, 0] := by
  apply CGood.intro
  intro s₀ val₀
  unfold kToE
  refine (CGood.bind ((castRow_cgood [(4, k0), (5, k1), (6, k2)]
    (lim ![val₀ k0 0, val₀ k1 0, val₀ k2 0, 0])).pre fun s v h => ⟨?_, ?_⟩)
    (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun ws =>
      CGood.pure' (Q := fun _ r s' _ => r = ws.getD 1 0) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_
  · simpa using h.2.2.1
  · obtain ⟨rfl, hag, hw, h0, h1, h2⟩ := h
    have hk0 := hw k0 (by simp)
    have hk1 := hw k1 (by simp)
    have hk2 := hw k2 (by simp)
    intro j hj p hp
    simp only [List.find?_cons, List.find?_nil] at hp
    split at hp
    · rename_i hj1; cases hp; simp only [decide_eq_true_eq] at hj1; subst hj1
      show v k0 = castSlot _ (4 + ((0 : Fin 4) : ℕ))
      rw [castSlot_word, h0, hag k0 hk0]; rfl
    split at hp
    · rename_i hj1; cases hp; simp only [decide_eq_true_eq] at hj1; subst hj1
      show v k1 = castSlot _ (4 + ((1 : Fin 4) : ℕ))
      rw [castSlot_word, h1, hag k1 hk1]; rfl
    split at hp
    · rename_i hj1; cases hp; simp only [decide_eq_true_eq] at hj1; subst hj1
      show v k2 = castSlot _ (4 + ((2 : Fin 4) : ℕ))
      rw [castSlot_word, h2, hag k2 hk2]; rfl
    · cases hp
  · rintro s r s2 v hs ⟨rfl, hag, hw, -⟩ - ⟨ws, s1, -, he1, -, ⟨hlen, hws, -, hget⟩, rfl⟩
    refine ⟨(hws.mono he1) _ (getD_mem ?_), ?_⟩
    · omega
    · rw [hget 1 (by omega), castSlot_element, hag k0 (hw k0 (by simp)), hag k1 (hw k1 (by simp)),
        hag k2 (hw k2 (by simp))]
      rfl

theorem dToK_cgood (d : ℕ) : CGood st 0 (fun s v => d < s.next) (dToK d) fun _ ks s' v =>
    ks.length = 4 ∧ Wires ks s' ∧ ∀ i : Fin 4, v (ks.getD i 0) = kVal (v d i) := by
  apply CGood.intro
  intro s₀ val₀
  unfold dToK
  refine (CGood.bind ((castRow_cgood [(0, d)] (lim (val₀ d))).pre fun s v h => ⟨?_, ?_⟩)
    (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun ws =>
      CGood.pure' (Q := fun _ r s' _ => r = ws.drop 4) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_
  · intro u hu; simp at hu; subst hu; exact h.2.2
  · obtain ⟨rfl, hag, hd⟩ := h
    intro j hj p hp
    simp only [List.find?_cons, List.find?_nil] at hp
    split at hp
    · rename_i hj1
      cases hp
      simp only [decide_eq_true_eq] at hj1
      subst hj1
      rw [castSlot_digest, hag d hd]
      funext i
      simp [lim]
    · cases hp
  · rintro s r s2 v hs ⟨rfl, hag, hd⟩ - ⟨ws, s1, -, he1, -, ⟨hlen, hw, -, hget⟩, rfl⟩
    refine ⟨by simp [hlen], fun w hw' => (hw.mono he1) w (List.mem_of_mem_drop hw'), fun i => ?_⟩
    have : (ws.drop 4).getD i 0 = ws.getD (4 + i) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [this, hget (4 + i) (by omega), castSlot_word, hag d hd]
    simp [lim]

theorem dToEAndK_cgood (d : ℕ) : CGood st 0 (fun s v => d < s.next) (dToEAndK d) fun _ r s' v =>
    r.1 < s'.next ∧ r.2 < s'.next ∧ v r.1 = ![v d 0, v d 1, v d 2, 0] ∧ v r.2 = kVal (v d 3) := by
  apply CGood.intro
  intro s₀ val₀
  unfold dToEAndK
  refine (CGood.bind ((castRow_cgood [(0, d)] (lim (val₀ d))).pre fun s v h => ⟨?_, ?_⟩)
    (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun ws =>
      CGood.pure' (Q := fun _ r s' _ => r = (ws.getD 1 0, ws.getD 7 0)) fun _ _ _ _ => rfl).weaken
      (fun _ _ h => h) ?_
  · intro u hu; simp at hu; subst hu; exact h.2.2
  · obtain ⟨rfl, hag, hd⟩ := h
    intro j hj p hp
    simp only [List.find?_cons, List.find?_nil] at hp
    split at hp
    · rename_i hj1
      cases hp
      simp only [decide_eq_true_eq] at hj1
      subst hj1
      rw [castSlot_digest, hag d hd]
      funext i
      simp [lim]
    · cases hp
  · rintro s r s2 v hs ⟨rfl, hag, hd⟩ - ⟨ws, s1, -, he1, -, ⟨hlen, hw, -, hget⟩, rfl⟩
    refine ⟨(hw.mono he1) _ (getD_mem (by omega)), (hw.mono he1) _ (getD_mem (by omega)), ?_, ?_⟩
    · rw [hget 1 (by omega), castSlot_element, hag d hd]
      simp [lim]
    · rw [hget 7 (by omega), show (7 : ℕ) = 4 + ((3 : Fin 4) : ℕ) from rfl, castSlot_word, hag d hd]
      simp [lim]

end


/-! `SPLIT` rows. -/

section

variable {st : ℕ → Fin 4 → K}

/-- Bit `i` of the word `n` in `K`. -/
noncomputable def bitK (n i : ℕ) : K := if n.testBit i then 1 else 0

theorem ofWord_toWord (a : K) : ofWord (toWord a) = a :=
  toWord_injective (toWord_ofWord _ (num_lt _ _))

theorem ofWord_lt {n : ℕ} (hn : n < 2 ^ 64) : ofWord n = Rec.ev n := by
  rw [ofWord, Nat.mod_eq_of_lt hn]

/-- A `SPLIT` row's identities hold on a word's columns and its bits'. -/
theorem split_identities (col : ℕ → K) (n : ℕ) (hn : n < 2 ^ 64) (h0 : col 0 = ofWord n)
    (hb : ∀ i < 64, col (1 + i) = bitK n i) : ∀ id ∈ splitIdentities, id.eval col = 0 := by
  have hpow : ∀ i < 64, ofWord (2 ^ i) = root ^ i := by
    intro i hi
    rw [ofWord, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hi), show 2 ^ i = 2 ^ i * 1 by ring,
      ev_two_pow_mul, ev_one, mul_one]
  have hsum : ((List.range 64).map fun i => ofWord (2 ^ i) * col (1 + i)).sum = Rec.ev n := by
    rw [ev_eq_sum 64 n hn, list_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpow i i.isLt, hb i i.isLt, bitK, bitZ]
    split_ifs <;> simp
  intro id hid
  simp only [splitIdentities, List.mem_cons, List.mem_map, List.mem_range] at hid
  rcases hid with rfl | ⟨i, hi, rfl⟩
  · simp only [Identity.eval, splitWord, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero,
      ofWord_one, one_mul, List.map_map]
    refine (add_eq_zero_iff_eq _ _).mpr ?_
    rw [h0, ofWord_lt hn, ← hsum]
    rfl
  · refine (boolean_spec col (1 + i)).mpr ?_
    rw [hb i hi, bitK]
    split_ifs <;> simp

theorem split_slot (col : ℕ → K) (j : ℕ) (hj : j < 65) : (fun i : Fin 4 => limbs Rec.split j col i) = kVal (col j) := by
  have h : Rec.split.getD j [] = kSlot j := by
    simp [Rec.split, List.getD_eq_getElem?_getD, hj]
  funext i
  simp only [limbs, h]
  fin_cases i <;> simp [kSlot, Form.eval, Form.zero, ofWord_zero, kVal]

/-- A `SPLIT` row of the word `w` carrying `ofWord n` and wires carrying `n`'s bits. -/
theorem split_rowSat (v : Val) (w : ℕ) (bits : List ℕ) (n : ℕ) (hn : n < 2 ^ 64) (hw : v w = kVal (ofWord n))
    (hb : ∀ i < 64, v (bits.getD i 0) = kVal (bitK n i)) :
    RowSat Rec.split (fun col => ∀ id ∈ splitIdentities, id.eval col = 0) v (w :: bits) := by
  set col : ℕ → K := fun j => if j = 0 then ofWord n else bitK n (j - 1)
  refine ⟨col, split_identities col n hn rfl fun i _ => ?_, fun j hj i => ?_⟩
  · simp [col]
  · have hj' : j < 65 := by simpa [Rec.split] using hj
    rw [show limbs Rec.split j col i = (fun i : Fin 4 => limbs Rec.split j col i) i from rfl, split_slot col j hj']
    cases j with
    | zero => rw [List.getD_cons_zero, hw]; simp [col]
    | succ j =>
      rw [List.getD_cons_succ, hb j (by omega)]
      simp [col]

theorem splitRow_cgood (w : ℕ) (bits : List ℕ) (n : ℕ) (hn : n < 2 ^ 64) :
    CGood st 0 (fun s v => Wires (w :: bits) s ∧ v w = kVal (ofWord n) ∧
      ∀ i < 64, v (bits.getD i 0) = kVal (bitK n i)) (splitRow w bits)
      fun _ _ s' _ => (w :: bits) ∈ s'.split :=
  ((row_cgood .split (w :: bits) (by decide)).pre fun _ v h => ⟨h.1, by simp, split_rowSat v w bits n hn h.2.1 h.2.2⟩).weaken
    (fun _ _ h => h) fun _ _ _ _ _ _ _ h => h.2.2.1 rfl

/-- `split`: 64 wires carrying the word's bits. -/
theorem split_cgood (w : ℕ) : CGood st 0 (fun s v => w < s.next ∧ v w = kVal (v w 0)) (split w)
    fun _ bits s' v => bits.length = 64 ∧ Wires bits s' ∧ ∀ i < 64, v (bits.getD i 0) = kVal (bitK (toWord (v w 0)) i) := by
  apply CGood.intro
  intro s₀ val₀
  set n := toWord (val₀ w 0)
  have hn : n < 2 ^ 64 := num_lt _ _
  unfold split
  have hmap := (mapM_cgood (st := st)
      (fun s v => s₀.next ≤ s.next ∧ Agree s₀.next val₀ v ∧ w < s₀.next ∧ v w = kVal (v w 0))
      (fun _ _ _ h he => ⟨h.1.trans he.next, h.2⟩) (fun _ => wire) (fun i y v => v y = kVal (bitK n i))
      (fun i => ((wire_cgood (kVal (bitK n i))).pre fun _ _ _ => trivial).weaken (fun _ _ h => h)
        fun _ _ _ _ _ _ _ hq => ⟨hq.2.2, by rw [hq.1, hq.2.1]; exact Nat.lt_succ_self _⟩) (List.range 64)).pre
      (P' := fun s v => s = s₀ ∧ Agree s.next val₀ v ∧ w < s.next ∧ v w = kVal (v w 0))
      (fun _ _ h => by obtain ⟨rfl, h⟩ := h; exact ⟨le_rfl, h⟩)
  refine (CGood.bind hmap
    (P₂ := fun bits s v => bits.length = 64 ∧ Wires (w :: bits) s ∧ v w = kVal (ofWord n) ∧
      ∀ i < 64, v (bits.getD i 0) = kVal (bitK n i)) ?_ fun bits =>
      CGood.bind ((splitRow_cgood w bits n hn).pre fun _ _ h => h.2)
        (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun _ =>
        CGood.pure' (Q := fun _ r _ _ => r = bits) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_
  · rintro s bits s' v hs ⟨rfl, hag, hw, hwk⟩ he ⟨hlen, hR, hws⟩
    simp only [List.length_range] at hlen
    refine ⟨hlen, wires_cons.2 ⟨lt_of_lt_of_le hw he.next, hws⟩, ?_, fun i hi => ?_⟩
    · rw [hwk, hag w hw, ofWord_toWord]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      have := hR i (by simpa using hi) (by omega)
      simpa using this
  · rintro s r s3 v hs ⟨rfl, hag, hw, -⟩ - ⟨bits, s1, -, he1, -, -, u, s2, -, -, ⟨hlen, hws, hwv, hb⟩, -, rfl⟩
    refine ⟨hlen, fun u hu => (hws.mono he1) u (List.mem_cons_of_mem _ hu), fun i hi => ?_⟩
    rw [hb i hi, hag w hw]

/-- `pack`: Boolean wires' word. -/
theorem pack_cgood (bits : List ℕ) : CGood st 0 (fun s v => Wires bits s ∧ bits.length ≤ 64 ∧
    ∀ i < bits.length, v (bits.getD i 0) = kVal 0 ∨ v (bits.getD i 0) = kVal 1) (pack bits)
    fun _ w s' v => w < s'.next ∧ v w = kVal (ofWord (num (fun i =>
      if i < bits.length ∧ v (bits.getD i 0) = kVal 1 then 1 else 0) 64)) := by
  apply CGood.intro
  intro s₀ val₀
  set c : ℕ → ZMod 2 := fun i => if i < bits.length ∧ val₀ (bits.getD i 0) = kVal 1 then 1 else 0
  set n := num c 64
  have hn : n < 2 ^ 64 := num_lt _ _
  have hkv : kVal (0 : K) ≠ kVal 1 := fun h => zero_ne_one (congrFun h 0)
  unfold pack
  refine (CGood.bind (kZero_cgood.pre fun _ _ _ => trivial)
    (P₂ := fun z s v => s₀.next ≤ s.next ∧ Agree s₀.next val₀ v ∧ Wires bits s₀ ∧ bits.length ≤ 64 ∧
      (∀ i < bits.length, val₀ (bits.getD i 0) = kVal 0 ∨ val₀ (bits.getD i 0) = kVal 1) ∧ z < s.next ∧
      v z = kVal 0) ?_ fun z =>
    CGood.bind ((wire_cgood (kVal (ofWord n))).pre fun _ _ _ => trivial)
      (P₂ := fun w s v => s₀.next ≤ s.next ∧ Agree s₀.next val₀ v ∧ Wires bits s₀ ∧ bits.length ≤ 64 ∧
        (∀ i < bits.length, val₀ (bits.getD i 0) = kVal 0 ∨ val₀ (bits.getD i 0) = kVal 1) ∧ z < s.next ∧
        v z = kVal 0 ∧ w < s.next ∧ v w = kVal (ofWord n)) ?_ fun w =>
      CGood.bind ((splitRow_cgood w (bits ++ List.replicate (64 - bits.length) z) n hn).pre ?_)
        (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun _ =>
        CGood.pure' (Q := fun _ r _ _ => r = w) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_
  · rintro s z s' v hs ⟨rfl, hag, hw, hl, hb⟩ he ⟨hz, hzv⟩
    exact ⟨he.next, hag, hw, hl, fun i hi => by rw [← hag _ (hw _ (getD_mem hi))]; exact hb i hi, hz, hzv⟩
  · rintro s w s' v hs ⟨h0, hag, hw, hl, hb, hz, hzv⟩ he ⟨rfl, hn', hwv⟩
    exact ⟨h0.trans he.next, hag, hw, hl, hb, lt_of_lt_of_le hz he.next, hzv, by rw [hn']; exact Nat.lt_succ_self _,
      hwv⟩
  · rintro s v ⟨h0, hag, hw, hl, hb, hz, hzv, hwl, hwv⟩
    refine ⟨wires_cons.2 ⟨hwl, fun u hu => ?_⟩, hwv, fun i hi => ?_⟩
    · rcases List.mem_append.mp hu with hu | hu
      · exact lt_of_lt_of_le (hw u hu) h0
      · rw [List.eq_of_mem_replicate hu]; exact hz
    · have hbit : bitK n i = if c i = 1 then 1 else 0 := by
        rw [bitK, testBit_num c 64 i hi]
        rcases zmod2_cases (c i) with h | h <;> simp [h]
      rw [hbit]
      by_cases hil : i < bits.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hil, ← List.getD_eq_getElem?_getD,
          hag _ (hw _ (getD_mem hil))]
        rcases hb i hil with h | h
        · have hc : ¬c i = 1 := by
            simp only [c]; rw [if_neg (fun h' => hkv (h.symm.trans h'.2))]; exact zero_ne_one
          rw [h, if_neg hc]
        · have hc : c i = 1 := by simp only [c]; rw [if_pos ⟨hil, h⟩]
          rw [h, if_pos hc]
      · have hc : ¬c i = 1 := by simp only [c]; rw [if_neg (fun h' => hil h'.1)]; exact zero_ne_one
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), List.getElem?_replicate,
          if_pos (by omega), Option.getD_some, hzv, if_neg hc]
  · rintro s r s4 v hs ⟨rfl, hag, hw, -, -⟩ - ⟨z, s1, -, -, -, -, w, s2, -, he24, -, ⟨rfl, hn2, hwv⟩, u, s3, -, -, -,
      -, rfl⟩
    refine ⟨lt_of_lt_of_le (by rw [hn2]; exact Nat.lt_succ_self _) he24.next, ?_⟩
    have hc : c = fun i => if i < bits.length ∧ v (bits.getD i 0) = kVal 1 then 1 else 0 := by
      funext i
      by_cases hil : i < bits.length
      · simp only [c, hil, true_and, hag _ (hw _ (getD_mem hil))]
      · simp [c, hil]
    rw [hwv]
    show kVal (ofWord (num c 64)) = _
    rw [hc]

end


/-! `HASH` rows. -/

attribute [local irreducible] Blake2s.program

/-- The artifact's input bits holding the ports `I`. -/
def portBits (I : Blake2s.Compress.Input Bit) (i : ℕ) : Bit :=
  if h : i < 64 then I.t[i]'h else if h' : i < 96 then I.f0[i - 64]'(by omega)
  else if h'' : i < 352 then I.h[i - 96]'(by omega) else if h''' : i < 864 then I.m[i - 352]'(by omega) else 0

theorem ports_agree (I : Blake2s.Compress.Input Bit) (a : ℕ → Bit)
    (h : Flock.AgreeBelow Blake2s.Compress.inputBits (portBits I) a) : Blake2s.Export.ports a = I := by
  have hb : Blake2s.Compress.inputBits = 864 := rfl
  obtain ⟨t, f0, hh, m⟩ := I
  unfold Blake2s.Export.ports
  rw [Blake2s.Compress.Input.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i hi
    rw [Vector.getElem_ofFn, h _ (by omega)]
    unfold portBits
    rw [dif_pos hi]
  · ext i hi
    rw [Vector.getElem_ofFn, h _ (by omega)]
    unfold portBits
    rw [dif_neg (by omega), dif_pos (by omega)]
    simp only [Nat.add_sub_cancel_left]
  · ext i hi
    rw [Vector.getElem_ofFn, h _ (by omega)]
    unfold portBits
    rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
    simp only [Nat.add_sub_cancel_left]
  · ext i hi
    rw [Vector.getElem_ofFn, h _ (by omega)]
    unfold portBits
    rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
    simp only [Nat.add_sub_cancel_left]

theorem literal_toWord {n : ℕ} (y : Vector Bit n) : (Blake2s.literal (Blake2s.toWord y) : Vector Bit n) = y := by
  apply Vector.ext
  intro i hi
  simp only [Blake2s.literal, Vector.getElem_ofFn, Blake2s.getLsbD_toWord, dif_pos hi]
  rcases Blake2s.bit_cases y[i] with h | h <;> simp [h]

/-- A bit vector is the bits of its 64-bit words. -/
theorem resultOf_chunks (x : Vector Bit 256) :
    x = resultOf fun k => Blake2s.toWord (Vector.ofFn fun j : Fin 64 => x[64 * k.val + j.val]'(by omega)) := by
  apply Vector.ext
  intro j hj
  rw [resultOf, Vector.getElem_ofFn]
  dsimp only
  rw [literal_toWord, Vector.getElem_ofFn]
  simp only [Nat.div_add_mod]

/-- The exported artifact has a satisfying witness with any input ports, its result RFC 7693's compression. -/
theorem witness_exists (P : Fin 14 → BitVec 64) (f : Bool) (hf : (P 1).setWidth 32 = finalWord f) :
    ∃ a, Blake2s.Compress.artifact.Holds a ∧ Blake2s.Export.ports a = portsOf P ∧
      Blake2s.Export.result a = resultOf (digest (Blake2s.Rfc7693.F (hWords P) (mWords P) (P 0) f)) := by
  obtain ⟨a, hag, hholds⟩ := Blake2s.Export.completeness (portBits (portsOf P))
  have hports := ports_agree (portsOf P) a hag
  refine ⟨a, hholds, hports, ?_⟩
  have hres := resultOf_chunks (Blake2s.Export.result a)
  have hh := hash_ports_compress a hholds P _ hports hres f hf
  generalize Blake2s.Export.result a = R at hres hh ⊢
  generalize Blake2s.Rfc7693.F (hWords P) (mWords P) (P 0) f = V at hh ⊢
  have hO := fun k => eq_digest (fun k : Fin 4 => Blake2s.toWord (Vector.ofFn fun j : Fin 64 =>
    R[64 * k.val + j.val]'(by omega))) V hh k
  rw [funext hO] at hres
  exact hres

section

variable {st : ℕ → Fin 4 → K}

/-- The limbs slot `j` of a `HASH` row takes from columns `col`. -/
noncomputable def slotV (col : ℕ → K) (j : ℕ) : Fin 4 → K := fun i => limbs Rec.hash j col i

theorem slotV_h (col : ℕ → K) : slotV col 0 = fun i : Fin 4 => col (2 + i) := by
  funext i; fin_cases i <;> rfl

theorem slotV_tf (col : ℕ → K) : slotV col 1 = ![col 0, col 1, 0, 0] := by
  funext i; fin_cases i <;> simp [slotV, limbs, Rec.hash, Form.eval, Form.zero, ofWord_zero, hashT, hashF]

theorem slotV_out (col : ℕ → K) : slotV col 6 = fun i : Fin 4 => col (14 + i) := by
  funext i; fin_cases i <;> rfl

theorem slotV_word (col : ℕ → K) (i : ℕ) (hi : i < 8) : slotV col (8 + i) = kVal (col (6 + i)) := by
  have : Rec.hash.getD (8 + i) [] = kSlot (hashM + i) := by
    rw [Rec.hash, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.getElem?_map]
    simp [List.getElem?_range hi]
  funext l
  simp only [slotV, limbs, this]
  fin_cases l <;> simp [kSlot, Form.eval, Form.zero, ofWord_zero, kVal, hashM]

/-- Wires `l`, from slot `b` on, are wires carrying their slots' limbs. -/
def SlotsOk (col : ℕ → K) (b : ℕ) (l : List ℕ) (s : State) (v : Val) : Prop :=
  ∀ j < l.length, l.getD j 0 < s.next ∧ v (l.getD j 0) = slotV col (b + j)

theorem SlotsOk.mono {col : ℕ → K} {b : ℕ} {l : List ℕ} {s s' : State} {v : Val} (h : SlotsOk col b l s v)
    (he : Ext s s') : SlotsOk col b l s' v :=
  fun j hj => ⟨lt_of_lt_of_le (h j hj).1 he.next, (h j hj).2⟩

theorem SlotsOk.wires {col : ℕ → K} {b : ℕ} {l : List ℕ} {s : State} {v : Val} (h : SlotsOk col b l s v) :
    Wires l s := by
  intro w hw
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  have := (h j hj).1
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this

theorem SlotsOk.snoc {col : ℕ → K} {b : ℕ} {l : List ℕ} {s s' : State} {v : Val} {x : ℕ}
    (h : SlotsOk col b l s v) (he : Ext s s') (hx : x < s'.next) (hv : v x = slotV col (b + l.length)) :
    SlotsOk col b (l ++ [x]) s' v := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hjl : j < l.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
    exact (h.mono he) j hjl
  · have : j = l.length := by omega
    subst this
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]
    exact ⟨hx, hv⟩

theorem slots_wire {col : ℕ → K} {b : ℕ} {l m : List ℕ} {s s' : State} {v : Val} {w : ℕ}
    (h : SlotsOk col b l s v ∧ SlotsOk col 8 m s v ∧ m.length = 8) (he : Ext s s')
    (hq : w = s.next ∧ s'.next = s.next + 1 ∧ v w = slotV col (b + l.length)) :
    SlotsOk col b (l ++ [w]) s' v ∧ SlotsOk col 8 m s' v ∧ m.length = 8 :=
  ⟨h.1.snoc he (by rw [hq.2.1, hq.1]; exact Nat.lt_succ_self _) hq.2.2, h.2.1.mono he, h.2.2⟩

/-- `hash_row`: a `HASH` row of columns `col`, the given wires carrying their slots' limbs. -/
theorem hashRow_cgood (h tf mux bit x ds : ℕ) (words : List ℕ) (col : ℕ → K) (hcol : HashRow col) :
    CGood st 0 (fun s v => SlotsOk col 0 [h, tf, mux, bit, x, ds] s v ∧ SlotsOk col 8 words s v ∧
      words.length = 8) (hashRow h tf mux bit x ds words)
      fun _ o s' v => o < s'.next ∧ v o = slotV col 6 := by
  unfold hashRow
  refine ((CGood.bind ((wire_cgood (slotV col 6)).pre fun _ _ _ => trivial)
    (P₂ := fun o s v => SlotsOk col 0 [h, tf, mux, bit, x, ds, o] s v ∧ SlotsOk col 8 words s v ∧
      words.length = 8) (fun _ _ _ _ _ hp he hq => slots_wire hp he hq) fun o =>
    CGood.bind ((wire_cgood (slotV col 7)).pre fun _ _ _ => trivial)
      (P₂ := fun ch s v => SlotsOk col 0 [h, tf, mux, bit, x, ds, o, ch] s v ∧ SlotsOk col 8 words s v ∧
        words.length = 8) (fun _ _ _ _ _ hp he hq => slots_wire hp he hq) fun ch =>
      CGood.bind ((row_cgood .hash ([h, tf, mux, bit, x, ds, o, ch] ++ words) (by decide)).pre ?_)
        (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun _ =>
        CGood.pure' (Q := fun _ r _ _ => r = o) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_).kEq rfl
  · rintro s v ⟨h8, hw, hlen⟩
    refine ⟨fun u hu => ?_, by simp, col, hcol, fun j hj i => ?_⟩
    · rcases List.mem_append.mp hu with hu | hu
      · exact h8.wires u hu
      · exact hw.wires u hu
    · have hj' : j < 16 := hj
      by_cases hj8 : j < 8
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj8),
          ← List.getD_eq_getElem?_getD, (h8 j (by simpa using hj8)).2]
        simp only [slotV, Nat.zero_add]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
          ← List.getD_eq_getElem?_getD, show j - [h, tf, mux, bit, x, ds, o, ch].length = j - 8 from rfl,
          (hw (j - 8) (by omega)).2, show 8 + (j - 8) = j by omega]
        rfl
  · rintro s r s4 v hs - - ⟨o, s1, -, he14, -, ⟨rfl, hn1, hov⟩, ch, s2, -, -, -, -, u, s3, -, -, -, -, rfl⟩
    exact ⟨lt_of_lt_of_le (by rw [hn1]; exact Nat.lt_succ_self _) he14.next, hov⟩

/-- `leaf_block`'s finalization word. -/
def finW (last : Bool) : ℕ := if last then final else 0

/-- A `HASH` row's input columns: counter, finalization, chaining value `H`, message words `M`. -/
noncomputable def hashIn (H : Fin 4 → K) (M : ℕ → K) (t fw : ℕ) (j : ℕ) : K :=
  if j = 0 then ofWord t else if j = 1 then ofWord fw else if j < 6 then lim H (j - 2)
  else if j < 14 then M (j - 6) else 0

/-- Its input port words. -/
noncomputable def hashPorts (H : Fin 4 → K) (M : ℕ → K) (t fw : ℕ) : Fin 14 → BitVec 64 :=
  fun j => columnWord (hashIn H M t fw) j

/-- A `HASH` row's columns: its inputs, RFC 7693's compression of them as output, mux bit zero. -/
noncomputable def hashCol (H : Fin 4 → K) (M : ℕ → K) (t fw : ℕ) (f : Bool) (j : ℕ) : K :=
  if j < 14 then hashIn H M t fw j
  else if j < 18 then lim (dVal (digest (Blake2s.Rfc7693.F (hWords (hashPorts H M t fw))
    (mWords (hashPorts H M t fw)) (hashPorts H M t fw 0) f))) (j - 14)
  else 0

theorem hashCol_row (H : Fin 4 → K) (M : ℕ → K) (t fw : ℕ) (f : Bool)
    (hf : (hashPorts H M t fw 1).setWidth 32 = finalWord f) : HashRow (hashCol H M t fw f) := by
  obtain ⟨a, hholds, hin, hout⟩ := witness_exists (hashPorts H M t fw) f hf
  refine ⟨⟨a, hholds, ?_, ?_⟩, ?_⟩
  · have hp : hashPorts H M t fw = fun j : Fin 14 => columnWord (hashCol H M t fw f) j :=
      funext fun j => by simp [hashPorts, columnWord, hashCol, j.isLt]
    rw [hin, hp]
  · have hd : digest (Blake2s.Rfc7693.F (hWords (hashPorts H M t fw)) (mWords (hashPorts H M t fw))
        (hashPorts H M t fw 0) f) = fun k : Fin 4 => columnWord (hashCol H M t fw f) (hashO + k) := by
      funext k
      simp only [columnWord, hashCol, hashO, show ¬(14 + k.val < 14) by omega, show 14 + k.val < 18 by omega,
      if_false, if_true, show 14 + k.val - 14 = k.val by omega, lim, dif_pos k.isLt, dVal]
      rw [toWord_ofWord _ (BitVec.isLt _)]
      simp
    rw [hout, hd]
  · intro id hid
    simp only [hashIdentities, List.mem_singleton] at hid
    subst hid
    refine (boolean_spec _ hashSel).mpr (Or.inl ?_)
    simp [hashCol, hashSel]

theorem hashCol_out (H : Fin 4 → K) (M : ℕ → K) (t fw : ℕ) (f : Bool) :
    slotV (hashCol H M t fw f) 6 = dVal (digest (Blake2s.Rfc7693.F (hWords (hashPorts H M t fw))
      (mWords (hashPorts H M t fw)) (hashPorts H M t fw 0) f)) := by
  rw [slotV_out]
  funext k
  simp only [hashCol, show ¬(14 + k.val < 14) by omega, show 14 + k.val < 18 by omega, if_false, if_true,
    show 14 + k.val - 14 = k.val by omega, lim, dif_pos k.isLt]

theorem hashPorts_h (H : Fin 4 → K) (M : ℕ → K) (t fw : ℕ) : hWords (hashPorts H M t fw) = cvWords (words4 H) := by
  apply Vector.ext
  intro r hr
  simp only [hWords, cvWords, Vector.getElem_ofFn, hashPorts, columnWord, words4]
  simp only [hashIn, show ¬(2 + r / 2 = 0) by omega, show ¬(2 + r / 2 = 1) by omega, show 2 + r / 2 < 6 by omega,
    if_false, if_true, show 2 + r / 2 - 2 = r / 2 by omega, lim, dif_pos (show r / 2 < 4 by omega)]

theorem hashPorts_m (H : Fin 4 → K) (M : ℕ → K) (t fw : ℕ) (ws : List (BitVec 64))
    (hm : ∀ i < 8, BitVec.ofNat 64 (toWord (M i)) = wordAt ws i) :
    mWords (hashPorts H M t fw) = block ws 0 := by
  apply Vector.ext
  intro r hr
  simp only [mWords, block, Vector.getElem_ofFn, hashPorts, columnWord, Nat.mul_zero, Nat.zero_add]
  rw [← hm (r / 2) (by omega)]
  simp only [hashIn, show ¬(6 + r / 2 = 0) by omega, show ¬(6 + r / 2 = 1) by omega,
    show ¬(6 + r / 2 < 6) by omega, show 6 + r / 2 < 14 by omega, if_false, if_true,
    show 6 + r / 2 - 6 = r / 2 by omega]

theorem hashPorts_t (H : Fin 4 → K) (M : ℕ → K) (t fw : ℕ) (ht : t < 2 ^ 64) :
    hashPorts H M t fw 0 = BitVec.ofNat 64 t := by
  simp [hashPorts, columnWord, hashIn, toWord_ofWord _ ht]

theorem hashPorts_f (H : Fin 4 → K) (M : ℕ → K) (t : ℕ) (last : Bool) :
    (hashPorts H M t (finW last) 1).setWidth 32 = finalWord last := by
  have h1 : hashPorts H M t (finW last) 1 = BitVec.ofNat 64 (finW last) := by
    simp only [hashPorts, columnWord, hashIn]
    simp only [show ((1 : Fin 14) : ℕ) = 1 from rfl, one_ne_zero, if_false, if_true]
    rw [toWord_ofWord _ (by cases last <;> simp [finW, final])]
  rw [h1]
  cases last <;> decide

/-- `leaf_block`: RFC 7693's compression of the chaining value `h` and the `K` words `m` at counter `t`. -/
theorem leafBlock_cgood (h : ℕ) (m : List ℕ) (t : ℕ) (last : Bool) (hm : m.length = 8) (ht : t < 2 ^ 64) :
    CGood st 0 (fun s v => Wires (h :: m) s ∧ ∀ i < 8, v (m.getD i 0) = kVal (v (m.getD i 0) 0))
      (leafBlock h m t last) fun _ o s' v => o < s'.next ∧ v o = dVal (digest (Blake2s.Rfc7693.F
        (cvWords (words4 (v h))) (block (m.map (w64 v)) 0) (BitVec.ofNat 64 t) last)) := by
  apply CGood.intro
  intro s₀ val₀
  set M : ℕ → K := fun i => val₀ (m.getD i 0) 0
  set col := hashCol (val₀ h) M t (finW last) last
  have hcol : HashRow col := hashCol_row _ _ _ _ _ (hashPorts_f _ _ _ _)
  unfold leafBlock
  refine (CGood.bind ((dConst_cgood [t, if last then final else 0, 0, 0]).pre fun _ _ _ => trivial)
    (P₂ := fun tf s v => SlotsOk col 0 [h, tf] s v ∧ SlotsOk col 8 m s v ∧ m.length = 8) ?_ fun tf =>
    CGood.bind ((wire_cgood (slotV col 2)).pre fun _ _ _ => trivial)
      (P₂ := fun mux s v => SlotsOk col 0 [h, tf, mux] s v ∧ SlotsOk col 8 m s v ∧ m.length = 8)
      (fun _ _ _ _ _ hp he hq => slots_wire hp he hq) fun mux =>
    CGood.bind ((wire_cgood (slotV col 3)).pre fun _ _ _ => trivial)
      (P₂ := fun bit s v => SlotsOk col 0 [h, tf, mux, bit] s v ∧ SlotsOk col 8 m s v ∧ m.length = 8)
      (fun _ _ _ _ _ hp he hq => slots_wire hp he hq) fun bit =>
    CGood.bind ((wire_cgood (slotV col 4)).pre fun _ _ _ => trivial)
      (P₂ := fun x s v => SlotsOk col 0 [h, tf, mux, bit, x] s v ∧ SlotsOk col 8 m s v ∧ m.length = 8)
      (fun _ _ _ _ _ hp he hq => slots_wire hp he hq) fun x =>
    CGood.bind ((wire_cgood (slotV col 5)).pre fun _ _ _ => trivial)
      (P₂ := fun ds s v => SlotsOk col 0 [h, tf, mux, bit, x, ds] s v ∧ SlotsOk col 8 m s v ∧ m.length = 8)
      (fun _ _ _ _ _ hp he hq => slots_wire hp he hq) fun ds =>
    hashRow_cgood h tf mux bit x ds m col hcol).weaken (fun _ _ h => h) ?_
  · rintro s tf s' v hs ⟨rfl, hag, hw, hk⟩ he ⟨htf, htfv⟩
    have hh := hw h (by simp)
    refine ⟨fun j hj => ?_, fun j hj => ?_, hm⟩
    · have hj2 : j < 2 := hj
      interval_cases j
      · refine ⟨lt_of_lt_of_le hh he.next, ?_⟩
        show v h = slotV col 0
        rw [slotV_h, hag h hh]
        funext i
        simp [col, hashCol, hashIn, lim, show (2 + i.val) ≠ 0 by omega, show (2 + i.val) ≠ 1 by omega,
          show 2 + i.val < 6 by omega, show 2 + i.val < 14 by omega]
      · refine ⟨htf, ?_⟩
        show v tf = slotV col 1
        rw [slotV_tf, htfv]
        funext i
        fin_cases i <;> simp [limbsOf, col, hashCol, hashIn, finW, ofWord_zero]
    · have hmj : m.getD j 0 ∈ m := getD_mem (by omega)
      refine ⟨lt_of_lt_of_le (hw _ (List.mem_cons_of_mem _ hmj)) he.next, ?_⟩
      rw [slotV_word col j (by omega), hk j (by omega), hag _ (hw _ (List.mem_cons_of_mem _ hmj))]
      simp [col, hashCol, hashIn, M, show (6 + j) ≠ 0 by omega, show (6 + j) ≠ 1 by omega,
        show ¬(6 + j < 6) by omega, show 6 + j < 14 by omega]
  · rintro s o s6 v hs ⟨rfl, hag, hw, hk⟩ - ⟨tf, s1, -, -, -, -, mux, s2, -, -, -, -, bit, s3, -, -, -, -, x, s4, -,
      -, -, -, ds, s5, -, -, -, -, ho, hov⟩
    refine ⟨ho, ?_⟩
    rw [hov, hashCol_out, hashPorts_h, hashPorts_t _ _ _ _ ht, hashPorts_m _ _ _ _ (m.map (w64 v)) fun i hi => ?_,
      hag h (hw h (by simp))]
    have hmi : m[i]'(by omega) ∈ m := List.getElem_mem _
    simp only [wordAt, w64, M, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show i < m.length by omega), Option.map_some, Option.getD_some]
    rw [hag _ (hw _ (List.mem_cons_of_mem _ hmi))]

end

/-! Statement counts, loops, and `chain`. -/

section

variable {st : ℕ → Fin 4 → K}

/-- The contract's statement count, as a postcondition. -/
theorem CGood.stmt {α : Type} {k : ℕ} {P : State → Val → Prop} {m : M α} {Q : State → α → State → Val → Prop}
    (h : CGood st k P m Q) : CGood st k P m fun s a s' v => Q s a s' v ∧ s'.statement = s.statement + k := by
  intro s val hi hc hsat hP
  obtain ⟨hi', hc', he, hst, val', ha, hsat', hq⟩ := h s val hi hc hsat hP
  exact ⟨hi', hc', he, hst, val', ha, hsat', fun v hv => ⟨hq v hv, hst⟩⟩

/-- A `for` loop whose body keeps an invariant indexed by the iteration, exposing `k` words each time. -/
theorem forIn_cgood {β γ : Type} (k : ℕ) (f : β → γ → M (ForInStep γ)) :
    ∀ (l : List β) (I : ℕ → γ → State → Val → Prop),
      (∀ i (hi : i < l.length) b, CGood st k (I i b) (f l[i] b)
        fun _ r s' v => ∃ b', r = .yield b' ∧ I (i + 1) b' s' v) →
      ∀ b, CGood st (k * l.length) (I 0 b) (forIn l b f) fun _ r s' v => I l.length r s' v
  | [], I, _, b => by
    rw [List.forIn_nil]
    exact (CGood.pure' fun _ _ _ h => h).kEq (by simp)
  | x :: xs, I, hf, b => by
    rw [List.forIn_cons]
    have ih := forIn_cgood k f xs (fun i => I (i + 1)) (fun i hi b => hf (i + 1) (by simp; omega) b)
    refine ((CGood.bind (k₂ := k * xs.length) (hf 0 (by simp) b) (P₂ := fun r s v => ∃ b', r = .yield b' ∧ I 1 b' s v)
      (fun _ _ _ _ _ _ _ h => h)
      (Q₂ := fun _ _ r s'' v => I (xs.length + 1) r s'' v) fun r => ?_).weaken (fun _ _ h => h) ?_).kEq
      (by simp [Nat.mul_succ, Nat.add_comm])
    · cases r with
      | done b' =>
        intro s val _ _ _ hP
        obtain ⟨_, h, _⟩ := hP val (Agree.refl _ _)
        cases h
      | yield b' =>
        exact (ih b').pre fun _ _ h => by obtain ⟨_, h, hI⟩ := h; cases h; exact hI
    · rintro s r s' v - - - ⟨a, s1, -, -, -, -, h⟩
      exact h

/-- A `for` loop of a unit body keeping a stable precondition. -/
theorem forIn_unit_cgood {β : Type} (l : List β) (g : β → M PUnit) (P : State → Val → Prop)
    (hP : ∀ s s' v, P s v → Ext s s' → P s' v)
    (hg : ∀ i (hi : i < l.length), CGood st 0 P (g l[i]) fun _ _ _ _ => True) :
    CGood st 0 P (forIn l PUnit.unit fun x _ => do g x; pure (ForInStep.yield PUnit.unit))
      fun _ _ _ _ => True := by
  refine ((forIn_cgood 0 _ l (fun _ _ => P) (fun i hi b => ?_) PUnit.unit).weaken (fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ => trivial).kEq (by simp)
  refine (CGood.bind (hg i hi) (P₂ := fun _ s v => P s v) (fun _ _ _ _ _ hp he _ => hP _ _ _ hp he) fun _ =>
    CGood.pure' (Q := fun _ r s' v => ∃ b', r = .yield b' ∧ P s' v) fun _ _ _ h => ⟨_, rfl, h⟩).weaken
    (fun _ _ h => h) ?_
  rintro s r s' v - - - ⟨a, s1, -, -, -, -, h⟩
  exact h

theorem pad_mem (words : List ℕ) (z j i : ℕ) (hi : i < 8) :
    ((List.range 8).map fun i => words.getD (8 * j + i) z).getD i 0 ∈ z :: words := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  rw [List.getD_eq_getElem?_getD]
  cases h : words[8 * j + i]? with
  | none => exact List.mem_cons_self
  | some w => exact List.mem_cons_of_mem _ (List.mem_of_getElem? h)

theorem chainBlocks_cgood (words : List ℕ) (z n bytes : ℕ) (hb : bytes < 2 ^ 64)
    (hmid : ∀ j, j + 1 < n → min (64 * (j + 1)) bytes = 64 * (j + 1)) (hlast : min (64 * n) bytes = bytes) :
    ∀ k (H : Val → Vector (BitVec 32) 8) j h, j + k + 1 = n →
      CGood st 0 (fun s v => Wires (h :: z :: words) s ∧ v z = kVal 0 ∧ (∀ w ∈ words, v w = kVal (v w 0)) ∧
        words4 (v h) = digest (H v))
      (chainBlocks words z n bytes ((List.range (k + 1)).map (j + ·)) h) fun _ r s' v => r < s'.next ∧
        v r = dVal (digest (blocksFrom (BitVec.ofNat 64 bytes) (H v) j (block (words.map (w64 v)) j)
          ((List.range k).map fun i => block (words.map (w64 v)) (j + 1 + i)))) := by
  have hpre : ∀ j h (s : State) (v : Val), Wires (h :: z :: words) s → v z = kVal 0 →
      (∀ w ∈ words, v w = kVal (v w 0)) →
      Wires (h :: (List.range 8).map fun i => words.getD (8 * j + i) z) s ∧
        ∀ i < 8, v (((List.range 8).map fun i => words.getD (8 * j + i) z).getD i 0) =
          kVal (v (((List.range 8).map fun i => words.getD (8 * j + i) z).getD i 0) 0) := by
    intro j h s v hw hz hk
    refine ⟨fun u hu => ?_, fun i hi => ?_⟩
    · rcases List.mem_cons.mp hu with rfl | hu
      · exact hw _ List.mem_cons_self
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
        have hi8 : i < 8 := by simpa using hi
        have hm := pad_mem words z j i hi8
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hm
        exact hw _ (List.mem_cons_of_mem _ hm)
    · rcases List.mem_cons.mp (pad_mem words z j i hi) with hm | hm
      · rw [hm, hz]; rfl
      · exact hk _ hm
  have hz0 : ∀ v : Val, v z = kVal 0 → v z 0 = 0 := fun v h => by rw [h]; rfl
  intro k
  induction k with
  | zero =>
    intro H j h hj
    have hn : j + 1 = n := by omega
    rw [show (List.range (0 + 1)).map (j + ·) = [j] from rfl]
    refine (CGood.bind ((leafBlock_cgood h _ (min (64 * (j + 1)) bytes) (j + 1 = n) (by simp)
      (lt_of_le_of_lt (min_le_right _ _) hb)).pre fun s v hp => hpre j h s v hp.1 hp.2.1 hp.2.2.1)
      (P₂ := fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial) fun r =>
        CGood.pure' (Q := fun _ o _ _ => o = r) fun _ _ _ _ => rfl).weaken (fun _ _ h => h) ?_
    rintro s o s2 v hs ⟨-, hz, -, hh⟩ - ⟨r, s1, -, he2, -, ⟨hr, hrv⟩, rfl⟩
    refine ⟨lt_of_lt_of_le hr he2.next, ?_⟩
    rw [hrv, hh, cvWords_digest, pad_block v words z j (hz0 v hz),
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
    refine (CGood.bind ((leafBlock_cgood h _ (min (64 * (j + 1)) bytes) (j + 1 = n) (by simp)
      (lt_of_le_of_lt (min_le_right _ _) hb)).pre fun s v hp => hpre j h s v hp.1 hp.2.1 hp.2.2.1)
      (P₂ := fun r s v => Wires (r :: z :: words) s ∧ v z = kVal 0 ∧ (∀ w ∈ words, v w = kVal (v w 0)) ∧
        words4 (v r) = digest (H' v))
      ?_ fun r => ih H' (j + 1) r (by omega)).weaken (fun _ _ h => h) ?_
    · rintro s r s1 v hs ⟨hw, hz, hk, hh⟩ he ⟨hr, hrv⟩
      refine ⟨wires_cons.2 ⟨hr, (wires_cons.1 hw).2.mono he⟩, hz, hk, ?_⟩
      rw [hrv, words4_dVal, hh, cvWords_digest, pad_block v words z j (hz0 v hz), hmid j (by omega)]
      simp [H', show ¬ (j + 1 = n) by omega]
    · rintro s o s2 v hs - - ⟨r, s1, -, -, -, -, ho, hov⟩
      refine ⟨ho, ?_⟩
      rw [hov, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [blocksFrom, H', Nat.add_zero, Function.comp_def]
      congr 4
      funext i; congr 1; omega

/-- `chain`: RFC 7693's BLAKE2s-256 of `K` words. -/
theorem chain_cgood (words : List ℕ) (hb : 8 * words.length < 2 ^ 64) :
    CGood st 0 (fun s v => Wires words s ∧ ∀ w ∈ words, v w = kVal (v w 0)) (chain words)
      fun _ r s' v => r < s'.next ∧ v r = dVal (digest (hashWords (words.map (w64 v)))) := by
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
  have hcb := fun z h => (hrange ▸ chainBlocks_cgood (st := st) words z n (8 * words.length) hb hmid hlast (n - 1)
    (fun _ => paramIV) 0 h (by omega) :)
  unfold chain
  refine (CGood.bind (kZero_cgood.pre fun _ _ _ => trivial)
    (P₂ := fun z s v => Wires (z :: words) s ∧ v z = kVal 0 ∧ ∀ w ∈ words, v w = kVal (v w 0))
    (fun _ _ _ _ _ hp he hq => ⟨wires_cons.2 ⟨hq.1, hp.1.mono he⟩, hq.2, hp.2⟩) fun z =>
      CGood.bind ((dConst_cgood paramIVLimbs).pre fun _ _ _ => trivial)
        (P₂ := fun h s v => Wires (h :: z :: words) s ∧ v z = kVal 0 ∧ (∀ w ∈ words, v w = kVal (v w 0)) ∧
          words4 (v h) = digest paramIV)
        (fun _ _ _ _ _ hp he hq => ⟨wires_cons.2 ⟨hq.1, hp.1.mono he⟩, hp.2.1, hp.2.2, by rw [hq.2]; exact words4_paramIV⟩)
        fun h => hcb z h).weaken (fun _ _ h => h) ?_
  rintro s r s2 v hs - - ⟨z, s1, -, -, -, -, h, s1', -, -, -, -, hr, hrv⟩
  refine ⟨hr, ?_⟩
  have h1 : nBlocks (words.map (w64 v)).length = n := by rw [List.length_map, hn]; rfl
  rw [hrv, hashWords, blake2s256, h1, List.length_map]
  congr 3
  apply List.map_congr_left
  intro i _
  congr 1
  omega

end

/-! Sequencing, hypotheses and `K` words. -/

theorem kVal_apply_zero (x : K) : kVal x 0 = x := rfl

theorem kVal_isK {v : Val} {w : ℕ} {x : K} (h : v w = kVal x) : v w = kVal (v w 0) := by
  rw [h]; rfl

theorem kVal_inj {a b : K} (h : kVal a = kVal b) : a = b := congrFun h 0

theorem kVal_bitK_eq_one (n i : ℕ) : kVal (bitK n i) = kVal 1 ↔ n.testBit i = true := by
  constructor
  · intro h
    have := kVal_inj h
    by_contra hc
    simp [bitK, hc] at this
  · intro h; simp [bitK, h]

section

variable {st : ℕ → Fin 4 → K}

/-- `bind` with a postcondition of the second step's output only. -/
theorem CGood.seq {α β : Type} {k₁ k₂ : ℕ} {P : State → Val → Prop} {m : M α}
    {f : α → M β} {Q₁ : State → α → State → Val → Prop} {P₂ : α → State → Val → Prop}
    {R : β → State → Val → Prop} (h₁ : CGood st k₁ P m Q₁)
    (hp : ∀ s a s' v, Inv s → P s v → Ext s s' → Q₁ s a s' v → P₂ a s' v)
    (h₂ : ∀ a, CGood st k₂ (P₂ a) (f a) fun _ b s'' v => R b s'' v) :
    CGood st (k₁ + k₂) P (m >>= f) fun _ b s'' v => R b s'' v :=
  (CGood.bind h₁ hp h₂).weaken (fun _ _ h => h) fun _ _ _ _ _ _ _ h => by
    obtain ⟨_, _, _, _, _, _, h⟩ := h; exact h

/-- A hypothesis taken from the precondition. -/
theorem CGood.hyp {α : Type} {k : ℕ} {H : Prop} {P : State → Val → Prop} {m : M α}
    {Q : State → α → State → Val → Prop} (h : H → CGood st k P m Q) :
    CGood st k (fun s v => H ∧ P s v) m Q :=
  fun s val hi hc hsat hP => h (hP val (Agree.refl _ _)).1 s val hi hc hsat fun v hv => (hP v hv).2

end

end LeanVMCircuits.Rec.Model
