module

public import Clean.Air.ProductCheck
public import LeanVMCircuits.Rec.Field

@[expose] public section

/-!
# The bus

The bus of `doc/leanvm/body/05-arithmetization.tex` (§sec:m3) as a Clean channel: tuples of sixteen `K` coordinates,
shorter ones zero-padded, with integer multiplicities. A push has multiplicity `1`, a pull `-1`, and a lookup
producer pushes entry `i` with its multiplicity `m_i`. Over `ℤ` the bus balances exactly when its pushed and
pulled tuples form the same multiset, the balance of §sec:m3, although `K` has characteristic two, where `-1 = 1`
would make a pull indistinguishable from a push.
-/

namespace LeanVMCircuits.Bus

open LeanVMCircuits.Rec

/-- Equality in `K` is decided classically: the bus theorems count tuples, they do not compute. -/
noncomputable instance : DecidableEq K := Classical.decEq K

/-- A bus tuple: sixteen coordinates of `K`. -/
abbrev Tuple := Vector K 16

/-- The domain separator of the VM state, `g^0`. -/
noncomputable def sepST : K := ofWord 1
/-- The domain separator of RAM and the advice, `g^1`. -/
noncomputable def sepMEM : K := ofWord 2
/-- The domain separator of the bytecode, `g^2`. -/
noncomputable def sepBC : K := ofWord 4
/-- The domain separator of the registers, `g^3`. -/
noncomputable def sepREG : K := ofWord 8

theorem ofWord_injective {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : ofWord a = ofWord b) : a = b := by
  have := congrArg toWord h
  rwa [toWord_ofWord a ha, toWord_ofWord b hb] at this

theorem ofWord_eq_iff {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : ofWord a = ofWord b ↔ a = b :=
  ⟨ ofWord_injective ha hb, congrArg ofWord ⟩

theorem mem_sum_map {α β : Type} {l : List β} {f : β → Multiset α} {a : α} :
    a ∈ (l.map f).sum ↔ ∃ x ∈ l, a ∈ f x := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem count_sum_map {α β : Type} [DecidableEq α] (l : List β) (f : β → Multiset α) (a : α) :
    (l.map f).sum.count a = (l.map fun x => (f x).count a).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- The tuple with the given leading coordinates, zero-padded to the bus width. -/
noncomputable def tuple (cs : List K) : Tuple := Vector.ofFn fun s => cs.getD s 0

theorem tuple_get (cs : List K) (s : ℕ) (hs : s < 16) : (tuple cs)[s] = cs.getD s 0 := by
  simp [tuple]

/-- Two coordinate lists of equal length, at most the bus width, give the same tuple only if they are equal. -/
theorem tuple_injective {cs ds : List K} (hlen : cs.length = ds.length) (hle : cs.length ≤ 16)
    (h : tuple cs = tuple ds) : cs = ds := by
  apply List.ext_getElem hlen
  intro s hs hs'
  have := tuple_get cs s (by omega)
  rw [h, tuple_get ds s (by omega), List.getD_eq_getElem _ _ hs', List.getD_eq_getElem _ _ hs] at this
  exact this.symm

/-- The bus channel: arity sixteen, integer multiplicities. Its guarantees are unused: the bus theorems are stated
on the balanced multisets themselves. -/
def channel : RawChannel K ℤ where
  name := "bus"
  arity := 16
  Guarantees _ _ _ := True
  Requirements _ _ _ := True

/-- The interaction carrying `t` with multiplicity `mult`. -/
def interaction (mult : ℤ) (t : Tuple) : Interaction K ℤ where
  channel := channel
  mult := mult
  msg := t.toArray
  same_size := by simp [channel]
  assumeGuarantees := false

/--
Flushes on the bus: tuples pushed once each, tuples pulled once each, and tuples a lookup producer pushes with
a multiplicity (§sec:lookup), counted as that many pushes.
-/
structure Flushes where
  pushes : List Tuple := []
  pulls : List Tuple := []
  produced : List (Tuple × ℕ) := []

namespace Flushes

instance : Append Flushes where
  append f g := ⟨ f.pushes ++ g.pushes, f.pulls ++ g.pulls, f.produced ++ g.produced ⟩

@[simp] theorem append_pushes (f g : Flushes) : (f ++ g).pushes = f.pushes ++ g.pushes := rfl
@[simp] theorem append_pulls (f g : Flushes) : (f ++ g).pulls = f.pulls ++ g.pulls := rfl
@[simp] theorem append_produced (f g : Flushes) : (f ++ g).produced = f.produced ++ g.produced := rfl

/-- The bus interactions of the flushes. -/
def interactions (f : Flushes) : List (Interaction K ℤ) :=
  f.pushes.map (interaction 1) ++ f.pulls.map (interaction (-1)) ++
    f.produced.map fun p => interaction p.2 p.1

/-- The pushed multiset: every push once, every produced tuple as often as its multiplicity. -/
def pushed (f : Flushes) : Multiset Tuple :=
  (f.pushes : Multiset Tuple) + (f.produced.map fun p => Multiset.replicate p.2 p.1).sum

/-- The pulled multiset. -/
def pulled (f : Flushes) : Multiset Tuple := f.pulls

/-- The bus balances: Clean's balance of the interactions, with integer multiplicities. -/
def Balanced (f : Flushes) : Prop := BalancedInteractions f.interactions

@[simp] theorem pushed_append (f g : Flushes) : (f ++ g).pushed = f.pushed + g.pushed := by
  simp only [pushed, append_pushes, append_produced, List.map_append, List.sum_append, ← Multiset.coe_add]
  abel

@[simp] theorem pulled_append (f g : Flushes) : (f ++ g).pulled = f.pulled + g.pulled := by
  simp [pulled]

theorem pushedMessages_cons (i : Interaction K ℤ) (l : List (Interaction K ℤ)) :
    pushedMessages (i :: l) = Multiset.replicate i.mult.toNat i.msg + pushedMessages l := by
  simp [pushedMessages]

theorem pulledMessages_cons (i : Interaction K ℤ) (l : List (Interaction K ℤ)) :
    pulledMessages (i :: l) = Multiset.replicate (-i.mult).toNat i.msg + pulledMessages l := by
  simp [pulledMessages]

theorem pushedMessages_append (l l' : List (Interaction K ℤ)) :
    pushedMessages (l ++ l') = pushedMessages l + pushedMessages l' := by
  simp [pushedMessages]

theorem pulledMessages_append (l l' : List (Interaction K ℤ)) :
    pulledMessages (l ++ l') = pulledMessages l + pulledMessages l' := by
  simp [pulledMessages]

theorem pushedMessages_pushes (l : List Tuple) :
    pushedMessages (l.map (interaction 1)) = (l : Multiset Tuple).map Vector.toArray := by
  induction l with
  | nil => simp [pushedMessages]
  | cons t l ih =>
    rw [List.map_cons, pushedMessages_cons, ih]
    simp [interaction]

theorem pushedMessages_pulls (l : List Tuple) : pushedMessages (l.map (interaction (-1))) = 0 := by
  induction l with
  | nil => simp [pushedMessages]
  | cons t l ih =>
    rw [List.map_cons, pushedMessages_cons, ih]
    simp [interaction]

theorem pushedMessages_produced (l : List (Tuple × ℕ)) :
    pushedMessages (l.map fun p => interaction p.2 p.1) =
      ((l.map fun p => Multiset.replicate p.2 p.1).sum).map Vector.toArray := by
  induction l with
  | nil => simp [pushedMessages]
  | cons p l ih =>
    rw [List.map_cons, pushedMessages_cons, ih]
    simp [interaction, Multiset.map_replicate]

theorem pulledMessages_pushes (l : List Tuple) : pulledMessages (l.map (interaction 1)) = 0 := by
  induction l with
  | nil => simp [pulledMessages]
  | cons t l ih =>
    rw [List.map_cons, pulledMessages_cons, ih]
    simp [interaction]

theorem pulledMessages_pulls (l : List Tuple) :
    pulledMessages (l.map (interaction (-1))) = (l : Multiset Tuple).map Vector.toArray := by
  induction l with
  | nil => simp [pulledMessages]
  | cons t l ih =>
    rw [List.map_cons, pulledMessages_cons, ih]
    simp [interaction]

theorem pulledMessages_produced (l : List (Tuple × ℕ)) :
    pulledMessages (l.map fun p => interaction p.2 p.1) = 0 := by
  induction l with
  | nil => simp [pulledMessages]
  | cons p l ih =>
    rw [List.map_cons, pulledMessages_cons, ih]
    simp [interaction]

theorem pushedMessages_interactions (f : Flushes) :
    pushedMessages f.interactions = f.pushed.map Vector.toArray := by
  rw [interactions, pushedMessages_append, pushedMessages_append, pushedMessages_pushes, pushedMessages_pulls,
    pushedMessages_produced, pushed, Multiset.map_add, add_zero]

theorem pulledMessages_interactions (f : Flushes) :
    pulledMessages f.interactions = f.pulled.map Vector.toArray := by
  rw [interactions, pulledMessages_append, pulledMessages_append, pulledMessages_pushes, pulledMessages_pulls,
    pulledMessages_produced, pulled, zero_add, add_zero]

/-- Over `ℤ`, the bus balances exactly when the pushed and pulled multisets of tuples are equal. -/
theorem balanced_iff (f : Flushes) : f.Balanced ↔ f.pushed = f.pulled := by
  rw [Balanced, balancedInteractions_iff_pushed_eq_pulled, pushedMessages_interactions,
    pulledMessages_interactions]
  exact (Multiset.map_injective fun _ _ h => Vector.toArray_inj.mp h).eq_iff

/-- Every tuple of the flushes lies outside the set `S` (for instance, carries another separator). -/
def Avoids (f : Flushes) (S : Tuple → Prop) : Prop :=
  (∀ t ∈ f.pushes, ¬ S t) ∧ (∀ t ∈ f.pulls, ¬ S t) ∧ (∀ p ∈ f.produced, p.2 ≠ 0 → ¬ S p.1)

theorem mem_pushed {f : Flushes} {t : Tuple} :
    t ∈ f.pushed ↔ t ∈ f.pushes ∨ ∃ p ∈ f.produced, p.2 ≠ 0 ∧ p.1 = t := by
  simp only [pushed, Multiset.mem_add, Multiset.mem_coe, mem_sum_map, Multiset.mem_replicate]
  constructor
  · rintro (h | ⟨ p, p_mem, p_ne, rfl ⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ p, p_mem, p_ne, rfl ⟩
  · rintro (h | ⟨ p, p_mem, p_ne, rfl ⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ p, p_mem, p_ne, rfl ⟩

theorem filter_pushed_of_avoids {f : Flushes} {S : Tuple → Prop} [DecidablePred S] (h : f.Avoids S) :
    f.pushed.filter S = 0 := by
  rw [Multiset.filter_eq_nil]
  intro t t_mem
  rcases mem_pushed.mp t_mem with t_mem | ⟨ p, p_mem, p_ne, rfl ⟩
  · exact h.1 t t_mem
  · exact h.2.2 p p_mem p_ne

theorem filter_pulled_of_avoids {f : Flushes} {S : Tuple → Prop} [DecidablePred S] (h : f.Avoids S) :
    f.pulled.filter S = 0 := by
  rw [Multiset.filter_eq_nil]
  intro t t_mem
  exact h.2.1 t t_mem

/-- Balance survives restriction to any set of tuples. -/
theorem filter_eq_of_balanced {f : Flushes} (balance : f.Balanced) (S : Tuple → Prop) [DecidablePred S] :
    f.pushed.filter S = f.pulled.filter S := by
  rw [(balanced_iff f).mp balance]

end Flushes

end LeanVMCircuits.Bus
