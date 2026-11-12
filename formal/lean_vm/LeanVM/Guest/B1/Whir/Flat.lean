/-
  LeanVM.Guest.B1.Whir.Flat

  A flat body (atoms, calls, conditional calls, then one `ret`) holds exactly when each of its
  statements does: the facts of `open_stacked`'s template, block by block.
-/

module

public import LeanVM.Guest.B1.Whir.DataSpec

/-!
# Flat bodies

`open_stacked`'s body (`osBody`) and its loops have no branch or `match`: every statement is an
atom, a call, a conditional call or a dispatch (a call of one of several functions, chosen by a
selector), and the last is the `ret`. So the body holds
of a valuation exactly when every statement's relation does (`StmtOk`) and the `ret`'s words are
the returns (`holdsList_flat_ret`). `AllOk σ ss` is that conjunction over a block; it splits over
`++` (`allOk_append`), so each block of the template is read on its own.

* `gw_eq`: the template's g-power words are `gen ^ e`;
* `osMat_val`: a materialized pointer is the base times `gen ^ off`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Flat statements -/

/-- A flat statement: an atom, a call, a conditional call or a dispatch. -/
def Stmt.flat : Stmt → Bool
  | .atom _ | .call .. | .callIf .. | .dispatch .. => true
  | _ => false

/-- A flat statement's relation. -/
def StmtOk (C : CallRel) (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .call f args rets => C f (args.map σ) (rets.map σ)
  | .callIf c f args => IsInK (σ c) ∧ (σ c ≠ 0 → C f (args.map σ) [])
  | .dispatch x fs args rets =>
      ∃ (j : ℕ) (h : j < fs.length), σ x = ofK (addressOfIndex j) ∧ C fs[j] (args.map σ) (rets.map σ)
  | _ => True

/-- Every statement of a block holds. -/
def AllOk (C : CallRel) (rd : Reader) (σ : Val) (ss : List Stmt) : Prop := ∀ s ∈ ss, StmtOk C rd σ s

theorem allOk_append {ss ts : List Stmt} :
    AllOk C rd σ (ss ++ ts) ↔ AllOk C rd σ ss ∧ AllOk C rd σ ts := by
  simp only [AllOk, List.mem_append]
  exact ⟨fun h ↦ ⟨fun s hs ↦ h s (Or.inl hs), fun s hs ↦ h s (Or.inr hs)⟩,
    fun h s hs ↦ hs.elim (h.1 s) (h.2 s)⟩

theorem allOk_cons {s : Stmt} {ss : List Stmt} :
    AllOk C rd σ (s :: ss) ↔ StmtOk C rd σ s ∧ AllOk C rd σ ss := by
  simp [AllOk]

theorem allOk_nil : AllOk C rd σ [] := fun _ h ↦ absurd h (by simp)

theorem allOk_flatten {bs : List (List Stmt)} :
    AllOk C rd σ bs.flatten ↔ ∀ b ∈ bs, AllOk C rd σ b := by
  simp only [AllOk, List.mem_flatten]
  exact ⟨fun h b hb s hs ↦ h s ⟨b, hb, hs⟩, fun h s ⟨b, hb, hs⟩ ↦ h b hb s hs⟩

/-- A flat block holds, then `next`, exactly when every statement does and `next`. -/
theorem holdsList_flat : ∀ (ss : List Stmt), ss.all Stmt.flat = true → ∀ (next : Prop)
    (kret : List E → Prop), Stmt.HoldsList C rd σ ss next kret ↔ AllOk C rd σ ss ∧ next
  | [], _, next, kret => by simp [Stmt.HoldsList, allOk_nil]
  | s :: ss, h, next, kret => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := holdsList_flat ss h.2 next kret
    rw [allOk_cons]
    match s, h.1 with
    | .atom a, _ => simp only [Stmt.HoldsList, Stmt.Holds, StmtOk, ih, and_assoc]
    | .call f args rets, _ => simp only [Stmt.HoldsList, Stmt.Holds, StmtOk, ih, and_assoc]
    | .callIf c f args, _ => simp only [Stmt.HoldsList, Stmt.Holds, StmtOk, ih, and_assoc]
    | .dispatch x fs args rets, _ => simp only [Stmt.HoldsList, Stmt.Holds, StmtOk, ih, and_assoc]

/-- **A dispatch at the selector `g^i`** calls its `i`-th function. -/
theorem stmtOk_dispatch {x : V} {fs : List String} {args rets : List V} {i : ℕ}
    (hx : σ x = ofK (Parameters.addressOfIndex i)) (hi : i < 2 ^ 64 - 1)
    (hfl : fs.length < 2 ^ 64 - 1) (h : StmtOk C rd σ (.dispatch x fs args rets)) :
    i < fs.length ∧ C (fs.getD i "") (args.map σ) (rets.map σ) := by
  obtain ⟨j, hj, hjx, hc⟩ := h
  have hji : j = i := gen_pow_inj (by omega) hi
    (by rw [gen_pow_eq_ofK, gen_pow_eq_ofK, ← hjx, hx])
  subst hji
  exact ⟨hj, by rw [List.getD_eq_getElem _ _ hj]; exact hc⟩

/-- **A flat body ending in a `ret`** holds exactly when every statement before it does and the
returns are its words. -/
theorem holdsList_flat_ret (ss : List Stmt) (h : ss.all Stmt.flat = true) (vs : List V)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (ss ++ [.ret vs]) False kret ↔ AllOk C rd σ ss ∧ kret (vs.map σ) := by
  rw [holdsList_append, holdsList_flat ss h]
  simp [Stmt.HoldsList, Stmt.Holds]

/-! ## Atoms -/

theorem holds_const (d : V) (c : E) : (Atom.const d c).Holds rd σ ↔ σ d = c := Iff.rfl
theorem holds_add (d a b : V) : (Atom.add d a b).Holds rd σ ↔ σ d = σ a + σ b := Iff.rfl
theorem holds_mul (d a b : V) : (Atom.mul d a b).Holds rd σ ↔ σ d = σ a * σ b := Iff.rfl
theorem holds_copy (d s : V) : (Atom.copy d s).Holds rd σ ↔ σ d = σ s := Iff.rfl
theorem holds_load (d p : V) (o : ℕ) : (Atom.load d p o).Holds rd σ ↔ LoadHolds rd (σ p) o (σ d) :=
  Iff.rfl
theorem stmtOk_atom (a : Atom) : StmtOk C rd σ (.atom a) ↔ a.Holds rd σ := Iff.rfl
theorem stmtOk_call (f : String) (args rets : List V) :
    StmtOk C rd σ (.call f args rets) ↔ C f (args.map σ) (rets.map σ) := Iff.rfl

/-! ## Words -/

/-- The template's g-power words. -/
theorem gw_eq {e : ℕ} (h : e < u128Bound) : gw e = gen ^ e := by
  rw [gw, gpowK_eq h, gen_pow_eq_ofK, ofK_eq_ofLimbs]

/-- A materialized pointer is the base times `gen ^ off`. -/
theorem osMat_val {base off k : ℕ} (h : off < u128Bound)
    (hok : AllOk C rd σ (osMat base off k).1) :
    σ (.n (osMat base off k).2.1) = σ (.n base) * gen ^ off := by
  by_cases h0 : off = 0
  · subst h0; simp [osMat]
  · simp only [osMat, h0, ↓reduceIte, allOk_cons, StmtOk, Atom.Holds] at hok ⊢
    rw [hok.2.1, hok.1, gw_eq h]

theorem osMat_next (base off k : ℕ) : k ≤ (osMat base off k).2.2 := by
  unfold osMat; split_ifs <;> simp

/-! ## Materializations from earlier ones -/

/-- The materializations hold: each `out` is its base times `g^exp`, and its source times
`g^dist` is too. -/
def MatsOk (σ : Val) (mats : List OsMat) : Prop :=
  ∀ m ∈ mats, m.exp < u128Bound ∧ m.dist < u128Bound ∧
    σ (.n m.out) = σ (.n m.base) * gen ^ m.exp ∧ σ (.n m.src) * gen ^ m.dist = σ (.n m.base) * gen ^ m.exp

theorem matsOk_nil (σ : Val) : MatsOk σ [] := fun _ h ↦ absurd h (by simp)

theorem osMatSrc_ok {σ : Val} {plan : List (ℕ × ℕ × ℕ)} {mats : List OsMat} (hm : MatsOk σ mats)
    {base off : ℕ} (h : off < u128Bound) :
    (osMatSrc plan mats base off).2 < u128Bound ∧ σ (.n (osMatSrc plan mats base off).1) *
      gen ^ (osMatSrc plan mats base off).2 = σ (.n base) * gen ^ off := by
  unfold osMatSrc
  split
  · split
    · rename_i m hf
      have hmem := List.mem_of_find?_eq_some hf
      have he := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at he
      obtain ⟨-, -, ho, -⟩ := hm m hmem
      split_ifs with hlt
      · refine ⟨by omega, ?_⟩
        simp only
        rw [ho, he.1, he.2, mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
      · exact ⟨h, rfl⟩
    · exact ⟨h, rfl⟩
  · exact ⟨h, rfl⟩

/-- **A materialization from earlier ones is the base times `g^off`.** -/
theorem osMatP_val {plan : List (ℕ × ℕ × ℕ)} {mats : List OsMat} {base off k : ℕ}
    (hm : MatsOk σ mats) (h : off < u128Bound)
    (hok : AllOk C rd σ (osMatP plan mats base off k).1) :
    σ (.n (osMatP plan mats base off k).2.1) = σ (.n base) * gen ^ off := by
  by_cases h0 : off = 0
  · subst h0; simp [osMatP]
  · simp only [osMatP, h0, ↓reduceIte, allOk_cons, StmtOk, Atom.Holds] at hok ⊢
    rw [hok.2.1, hok.1]
    split
    · rename_i m hf
      have he := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at he
      obtain ⟨-, hd, -, hs⟩ := hm m (List.mem_of_find?_eq_some hf)
      simp only
      rw [gw_eq hd, hs, he.1, he.2]
    · obtain ⟨hd, hs⟩ := osMatSrc_ok (plan := plan) hm (base := base) h
      rw [gw_eq hd, hs]

/-- The source and distance `osMatP` multiplies: a repeated materialization's, else `osMatSrc`'s. -/
def osMatSD (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off : ℕ) : ℕ × ℕ :=
  match mats.find? (fun m ↦ m.base == base && m.exp == off) with
  | some m => (m.src, m.dist)
  | none => osMatSrc plan mats base off

theorem osMatP_eq {plan : List (ℕ × ℕ × ℕ)} {mats : List OsMat} {base off : ℕ} (k : ℕ)
    (h0 : off ≠ 0) : osMatP plan mats base off k =
      ([.atom (.const (.n k) (gw (osMatSD plan mats base off).2)),
        .atom (.mul (.n (k + 1)) (.n (osMatSD plan mats base off).1) (.n k))], k + 1, k + 2) := by
  unfold osMatP osMatSD
  simp only [h0, ↓reduceIte]
  split <;> rename_i h <;> simp only [h]

/-- The source times `g^dist` is the base times `g^off`. -/
theorem osMatSD_ok {plan : List (ℕ × ℕ × ℕ)} {mats : List OsMat} (hm : MatsOk σ mats)
    {base off : ℕ} (h : off < u128Bound) :
    (osMatSD plan mats base off).2 < u128Bound ∧ σ (.n (osMatSD plan mats base off).1) *
      gen ^ (osMatSD plan mats base off).2 = σ (.n base) * gen ^ off := by
  unfold osMatSD
  split
  · rename_i m hf
    have he := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨-, hd, -, hs⟩ := hm m (List.mem_of_find?_eq_some hf)
    exact ⟨hd, by rw [hs, he.1, he.2]⟩
  · exact osMatSrc_ok hm h

/-- The materializations' values lie below `K`. -/
def MatsBelow (K : ℕ) (mats : List OsMat) : Prop := ∀ m ∈ mats, m.out < K ∧ m.src < K ∧ m.base < K

/-- The source of a materialization lies below `K`. -/
theorem osMatSD_lt {plan : List (ℕ × ℕ × ℕ)} {mats : List OsMat} {base off K : ℕ}
    (hb : MatsBelow K mats) (hbase : base < K) : (osMatSD plan mats base off).1 < K := by
  unfold osMatSD osMatSrc
  split
  · rename_i m hf; exact (hb m (List.mem_of_find?_eq_some hf)).2.1
  · split
    · split
      · rename_i m hf; split_ifs
        · exact (hb m (List.mem_of_find?_eq_some hf)).1
        · exact hbase
      · exact hbase
    · exact hbase

/-- Materializations below `K` keep their facts on a valuation agreeing below `K`. -/
theorem matsOk_agree {σ' : Val} {mats : List OsMat} {K : ℕ} (hm : MatsOk σ mats)
    (hb : MatsBelow K mats) (ha : ∀ i < K, σ' (.n i) = σ (.n i)) : MatsOk σ' mats := by
  intro m hm'
  obtain ⟨e, d, o, s⟩ := hm m hm'
  obtain ⟨b1, b2, b3⟩ := hb m hm'
  exact ⟨e, d, by rw [ha _ b1, ha _ b3]; exact o, by rw [ha _ b2, ha _ b3]; exact s⟩

/-- One more materialization at `k + 1 < K'` from a base below `K ≤ K'` stays below `K'`. -/
theorem matsBelow_after {plan : List (ℕ × ℕ × ℕ)} {mats : List OsMat} {base off k K K' : ℕ}
    (hb : MatsBelow K mats) (hbase : base < K) (hK : K ≤ K') (hk : k + 1 < K') :
    MatsBelow K' (osMatsAfter plan mats base off k) := by
  have hb' : MatsBelow K' mats := fun m hm ↦ by
    obtain ⟨h1, h2, h3⟩ := hb m hm; exact ⟨by omega, by omega, by omega⟩
  unfold osMatsAfter
  split_ifs
  · exact hb'
  · split
    · exact hb'
    · intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hb' m hm
      · simp only [List.mem_singleton] at hm
        subst hm
        refine ⟨hk, ?_, show base < K' by omega⟩
        have := osMatSD_lt (plan := plan) (off := off) hb hbase
        unfold osMatSD at this
        rename_i hf
        rw [hf] at this
        exact lt_of_lt_of_le this hK

theorem osMatP_next (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) :
    k ≤ (osMatP plan mats base off k).2.2 := by
  unfold osMatP; split_ifs <;> simp

theorem osMatP_shape (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) :
    (off = 0 → (osMatP plan mats base off k).2 = (base, k)) ∧
      (off ≠ 0 → (osMatP plan mats base off k).2 = (k + 1, k + 2)) := by
  unfold osMatP; constructor <;> intro h <;> simp [h]

/-- The materializations stay ok after one more, once its statements hold. -/
theorem osMatsAfter_ok {plan : List (ℕ × ℕ × ℕ)} {mats : List OsMat} {base off k : ℕ}
    (hm : MatsOk σ mats) (h : off < u128Bound)
    (hok : AllOk C rd σ (osMatP plan mats base off k).1) :
    MatsOk σ (osMatsAfter plan mats base off k) := by
  have hv := osMatP_val hm h hok
  unfold osMatsAfter
  split_ifs with h0
  · exact hm
  · split
    · exact hm
    · rename_i hf
      intro m hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hm m hmem
      · simp only [List.mem_singleton] at hmem
        subst hmem
        obtain ⟨hd, hs⟩ := osMatSrc_ok (plan := plan) hm (base := base) h
        refine ⟨h, hd, ?_, hs⟩
        have := (osMatP_shape plan mats base off k).2 h0
        rw [this] at hv
        exact hv

end
end LeanVM.Guest.B1.Whir
