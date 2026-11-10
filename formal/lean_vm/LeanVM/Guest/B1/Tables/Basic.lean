/-
  LeanVM.Guest.B1.Tables.Basic

  The proof machinery of the B1 lemmas of the bus, the tables, the selectors and the placement:
  a function's relation unfolded to its body, bodies compared by kernel evaluation and read by
  position, words in `K`, memory runs, valuations built block by block, and `mul_range` loops.
-/

module

public import LeanVM.Guest.B1.Tables.Base

/-!
# B1 of the bus and the tables: machinery

Ported from the BLAKE2s-era `B1/Basic` and `B1/Tables/GkrBase` (branch `mumbai`), local to these
families (prefixed `tb`) until the shared `B1/Common` has them:

* `tb_rel_iff_sem`, `tb_rel_pre`: a function's relation is its body's;
* `tbStmtsEqb`, `tbStmtsEqb_sound`: statements compared by kernel evaluation, words limb by limb;
  `tb_holds_slice`, `tb_holds_atom`, `tb_holds_callIf`: a run of a `ret`-free body's statements
  holds, compared with a template at its position;
* `tb_loadHolds_mul_gen_pow`, `tb_loadHolds_unique`, `tbReadsAt_append`: memory runs;
* `tbSetv`, `tbSetl`, `tb_look`: valuations built block by block;
* `tb_loop_iff`, `tb_guarded_loop_iff`: `mul_range` loops.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Unfolding a function -/

/-- A function's relation is its body's, once it is found by name. -/
theorem tb_rel_iff_sem {P : Core.Program} {rd : Reader} {f : String} {fn : Fn}
    (h : P.find? f = some fn) (args rets : List E) :
    P.Rel rd f args rets ↔
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsList (P.Rel rd) rd σ fn.body False (fun rs => rs = rets) := by
  rw [rel_iff]
  simp only [h, Option.some.injEq, exists_eq_left', Fn.Sem]

/-- A function whose body is `pre ++ [ret vs]`, `pre` without `ret`: its relation is some
valuation of its parameters satisfying `pre` and returning `vs`. -/
theorem tb_rel_pre {rd : Reader} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hnr : Stmt.noRetList pre = true) (args rets : List E) :
    coreProgram.Rel rd f args rets ↔
    ∃ σ : Val, fn.params.map σ = args ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ pre True (fun rs => rs = rets) ∧
      vs.map σ = rets := by
  rw [tb_rel_iff_sem hf, hb]
  refine exists_congr fun σ => and_congr Iff.rfl ?_
  rw [holdsList_append, holdsList_noRet _ hnr]
  rfl

/-! ## Words -/

theorem tb_word_eOfNat (n : ℕ) : word n 0 = eOfNat n := by
  rw [word, eOfNat_eq_ofLimbs]; rfl

theorem tb_word_zero : word 0 0 = 0 := by rw [tb_word_eOfNat, eOfNat_zero]

theorem tb_word_one : word 1 0 = 1 := by rw [tb_word_eOfNat, eOfNat_one]

theorem tb_word_gen : word 2 0 = gen := by rw [tb_word_eOfNat]; rfl

/-- `E(2^a)` is `g^a` below the first reduction. -/
theorem tb_word_two_pow {a : ℕ} (h : a < 64) : word (2 ^ a) 0 = gen ^ a := by
  rw [tb_word_eOfNat, gen_pow_eq_eOfNat h]

theorem tb_isInK_add {a b : E} (ha : IsInK a) (hb : IsInK b) : IsInK (a + b) := by
  obtain ⟨a, rfl⟩ := (isInK_iff _).mp ha
  obtain ⟨b, rfl⟩ := (isInK_iff _).mp hb
  rw [← ofK_add]; exact ofK_isInK _

theorem tb_isInK_mul {a b : E} (ha : IsInK a) (hb : IsInK b) : IsInK (a * b) := by
  obtain ⟨a, rfl⟩ := (isInK_iff _).mp ha
  obtain ⟨b, rfl⟩ := (isInK_iff _).mp hb
  rw [← ofK_mul]; exact ofK_isInK _

theorem tb_gen_pow_isInK (j : ℕ) : IsInK (gen ^ j) := by
  rw [gen_pow_eq_ofK]; exact ofK_isInK _

theorem tb_isInK_mul_ofK {p : E} {c : K} (hc : c ≠ 0) : IsInK (p * ofK c) ↔ IsInK p := by
  rw [eq_ofLimbs p, ofLimbs_mul_ofK, isInK_ofLimbs_iff, isInK_ofLimbs_iff]
  simp [hc]

theorem tb_limb0_mul_ofK {p : E} (hp : IsInK p) (c : K) : (p * ofK c).limb 0 = p.limb 0 * c := by
  rw [eq_ofLimbs p, ofLimbs_mul_ofK, hp.1, hp.2]
  rfl

/-! ## Memory -/

/-- A load through `p·g^j` at offset `k` is the load at offset `j + k`. -/
theorem tb_loadHolds_mul_gen_pow (rd : Reader) (p : E) (j k : ℕ) (w : E) :
    LoadHolds rd (p * gen ^ j) k w ↔ LoadHolds rd p (j + k) w := by
  have hg : Parameters.addressOfIndex j ≠ 0 := pow_ne_zero _ g_ne_zero
  rw [gen_pow_eq_ofK]
  unfold LoadHolds
  rw [tb_isInK_mul_ofK hg]
  constructor
  · rintro ⟨hp, h⟩
    rw [tb_limb0_mul_ofK hp, mul_assoc, Parameters.addressOfIndex, Parameters.addressOfIndex, ←
        pow_add] at h
    exact ⟨hp, h⟩
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    rw [tb_limb0_mul_ofK hp, mul_assoc, Parameters.addressOfIndex, Parameters.addressOfIndex, ←
        pow_add]
    exact h

/-- One address holds one word. -/
theorem tb_loadHolds_unique {rd : Reader} {p : E} {k : ℕ} {w w' : E} (h : LoadHolds rd p k w)
    (h' : LoadHolds rd p k w') : w = w' :=
  Option.some.inj (h.2.symm.trans h'.2)

theorem tbReadsAt_nil (rd : Reader) (p : E) : TbReadsAt rd p [] := fun _ hk => absurd hk (by simp)

/-- Words read at `p·g^a` are words read at `p` from offset `a`. -/
theorem tbReadsAt_gen_pow_mul {rd : Reader} {p : E} {a : ℕ} {xs : List E} :
    TbReadsAt rd (p * gen ^ a) xs ↔ ∀ k (hk : k < xs.length), LoadHolds rd p (a + k) xs[k] := by
  simp only [TbReadsAt, tb_loadHolds_mul_gen_pow]

/-- Two runs of words, one after the other. -/
theorem tbReadsAt_append {rd : Reader} {p : E} {xs ys : List E} :
    TbReadsAt rd p (xs ++ ys) ↔ TbReadsAt rd p xs ∧ TbReadsAt rd (p * gen ^ xs.length) ys := by
  rw [tbReadsAt_gen_pow_mul]
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have := h k (by simp; omega)
      rwa [List.getElem_append_left hk] at this
    · have := h (xs.length + k) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa using this
  · rintro ⟨hx, hy⟩ k hk
    by_cases h : k < xs.length
    · rw [List.getElem_append_left h]; exact hx k h
    · rw [List.getElem_append_right (by omega)]
      have := hy (k - xs.length) (by simp at hk; omega)
      rwa [show xs.length + (k - xs.length) = k by omega] at this

/-- A run of one word. -/
theorem tbReadsAt_singleton {rd : Reader} {p w : E} : TbReadsAt rd p [w] ↔ LoadHolds rd p 0 w := by
  constructor
  · intro h; exact h 0 (by simp)
  · intro h k hk
    obtain rfl : k = 0 := by simpa using hk
    exact h

/-- A run of words, cons. -/
theorem tbReadsAt_cons {rd : Reader} {p w : E} {ws : List E} :
    TbReadsAt rd p (w :: ws) ↔ LoadHolds rd p 0 w ∧ TbReadsAt rd (p * gen) ws := by
  rw [show w :: ws = [w] ++ ws from rfl, tbReadsAt_append, tbReadsAt_singleton]
  simp

/-! ## Comparing statement lists by kernel evaluation -/

/-- Words compared limb by limb. -/
def tbEEqb (a b : E) : Bool :=
  decide (a.limb 0 = b.limb 0) && decide (a.limb 1 = b.limb 1)

theorem tbEEqb_sound {a b : E} (h : tbEEqb a b = true) : a = b := by
  simp only [tbEEqb, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← ofLimbs_limb a, ← ofLimbs_limb b, h.1, h.2]

/-- Atoms compared, words limb by limb. -/
def tbAtomEqb : Atom → Atom → Bool
  | .const d c, .const d' c' => decide (d = d') && tbEEqb c c'
  | .const .., _ => false
  | a, b => decide (a = b)

theorem tbAtomEqb_sound {a b : Atom} (h : tbAtomEqb a b = true) : a = b := by
  cases a <;> cases b <;> simp only [tbAtomEqb, Bool.and_eq_true, decide_eq_true_eq,
    Bool.false_eq_true] at h <;> first | exact h | (rw [h.1, tbEEqb_sound h.2])

mutual
/-- Statements compared structurally. -/
def tbStmtEqb : Stmt → Stmt → Bool
  | .atom a, .atom b => tbAtomEqb a b
  | .ite c z n, .ite c' z' n' => decide (c = c') && tbStmtsEqb z z' && tbStmtsEqb n n'
  | .match_ x as, .match_ x' as' => decide (x = x') && tbArmsEqb as as'
  | .call f a r, .call f' a' r' => decide (f = f') && decide (a = a') && decide (r = r')
  | .callIf c f a, .callIf c' f' a' => decide (c = c') && decide (f = f') && decide (a = a')
  | .dispatch x fs a r, .dispatch x' fs' a' r' =>
      decide (x = x') && decide (fs = fs') && decide (a = a') && decide (r = r')
  | .ret vs, .ret vs' => decide (vs = vs')
  | _, _ => false

/-- Statement lists compared structurally. -/
def tbStmtsEqb : List Stmt → List Stmt → Bool
  | [], [] => true
  | s :: ss, s' :: ss' => tbStmtEqb s s' && tbStmtsEqb ss ss'
  | _, _ => false


/-- Arms compared structurally. -/
def tbArmsEqb : List (List Stmt) → List (List Stmt) → Bool
  | [], [] => true
  | a :: as, a' :: as' => tbStmtsEqb a a' && tbArmsEqb as as'
  | _, _ => false
end

/-- `ls.flatten.drop n` with the lists' lengths `lens` given (`dropFlatL_eq`): the kernel passes a
list by comparing `n` with its length, a number, instead of dropping its elements one by one. -/
def dropFlatL {α : Type} : List ℕ → List (List α) → ℕ → List α
  | len :: lens, l :: ls, n =>
    bif Nat.blt n len then l.drop n ++ ls.flatten else dropFlatL lens ls (n - len)
  | _, _, _ => []

theorem dropFlatL_eq {α : Type} :
    ∀ (ls : List (List α)) (n : ℕ), dropFlatL (ls.map List.length) ls n = ls.flatten.drop n
  | [], _ => by simp [dropFlatL]
  | l :: ls, n => by
    simp only [List.map_cons, dropFlatL, List.flatten_cons, List.drop_append]
    by_cases h : n < l.length
    · simp [Nat.blt_eq.mpr h, Nat.sub_eq_zero_of_le h.le]
    · rw [Nat.not_lt] at h
      simp [Nat.blt_eq, Nat.not_lt.mpr h, dropFlatL_eq ls, List.drop_eq_nil_of_le h]

mutual
theorem tbStmtEqb_sound : ∀ {s t : Stmt}, tbStmtEqb s t = true → s = t
  | .atom a, .atom b, h => by rw [tbAtomEqb_sound h]
  | .ite c z n, .ite c' z' n', h => by
    simp only [tbStmtEqb, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, tbStmtsEqb_sound h.1.2, tbStmtsEqb_sound h.2]
  | .match_ x as, .match_ x' as', h => by
    simp only [tbStmtEqb, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, tbArmsEqb_sound h.2]
  | .call .., .call .., h => by
    simp only [tbStmtEqb, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, h.1.2, h.2]
  | .callIf .., .callIf .., h => by
    simp only [tbStmtEqb, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, h.1.2, h.2]
  | .dispatch .., .dispatch .., h => by
    simp only [tbStmtEqb, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1.1, h.1.1.2, h.1.2, h.2]
  | .ret _, .ret _, h => by
    simp only [tbStmtEqb, decide_eq_true_eq] at h
    rw [h]
  | .atom _, .ite .., h | .atom _, .match_ .., h | .atom _, .call .., h | .atom _, .callIf .., h
  | .atom _, .dispatch .., h | .atom _, .ret _, h | .ite .., .atom _, h | .ite .., .match_ .., h
  | .ite .., .call .., h | .ite .., .callIf .., h | .ite .., .dispatch .., h | .ite .., .ret _, h
  | .match_ .., .atom _, h | .match_ .., .ite .., h | .match_ .., .call .., h
  | .match_ .., .callIf .., h | .match_ .., .dispatch .., h | .match_ .., .ret _, h
  | .call .., .atom _, h | .call .., .ite .., h | .call .., .match_ .., h | .call .., .callIf .., h
  | .call .., .dispatch .., h | .call .., .ret _, h | .callIf .., .atom _, h
  | .callIf .., .ite .., h | .callIf .., .match_ .., h | .callIf .., .call .., h
  | .callIf .., .dispatch .., h | .callIf .., .ret _, h | .dispatch .., .atom _, h
  | .dispatch .., .ite .., h | .dispatch .., .match_ .., h | .dispatch .., .call .., h
  | .dispatch .., .callIf .., h | .dispatch .., .ret _, h | .ret _, .atom _, h
  | .ret _, .ite .., h | .ret _, .match_ .., h | .ret _, .call .., h | .ret _, .callIf .., h
  | .ret _, .dispatch .., h => by simp [tbStmtEqb] at h

theorem tbStmtsEqb_sound : ∀ {s t : List Stmt}, tbStmtsEqb s t = true → s = t
  | [], [], _ => rfl
  | s :: ss, t :: tt, h => by
    simp only [tbStmtsEqb, Bool.and_eq_true] at h
    rw [tbStmtEqb_sound h.1, tbStmtsEqb_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [tbStmtsEqb] at h

theorem tbArmsEqb_sound : ∀ {s t : List (List Stmt)}, tbArmsEqb s t = true → s = t
  | [], [], _ => rfl
  | s :: ss, t :: tt, h => by
    simp only [tbArmsEqb, Bool.and_eq_true] at h
    rw [tbStmtsEqb_sound h.1, tbArmsEqb_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [tbArmsEqb] at h
end

/-! ## Reading a body by position -/

theorem tb_noRetList_append (a b : List Stmt) :
    Stmt.noRetList (a ++ b) = (Stmt.noRetList a && Stmt.noRetList b) := by
  induction a with
  | nil => simp [Stmt.noRetList]
  | cons s a ih => simp [Stmt.noRetList, ih, Bool.and_assoc]

theorem tb_noRetList_flatten_range (n : ℕ) (g : ℕ → List Stmt)
    (hg : ∀ i, Stmt.noRetList (g i) = true) : Stmt.noRetList ((List.range n).map g).flatten = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, tb_noRetList_append, ih,
      List.map_singleton, List.flatten_singleton, hg]; rfl

theorem tb_noRetList_mapAtoms (n : ℕ) (f : ℕ → Atom) :
    Stmt.noRetList ((List.range n).map fun e ↦ Stmt.atom (f e)) = true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, tb_noRetList_append, ih]; rfl

section Slices

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **A run of statements of a body without `ret`** holds: `blk`, equal to the statements at
position `n`. -/
theorem tb_holds_slice {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((pre.drop n).take blk.length) = true) :
    Stmt.HoldsList C rd σ blk True kret := by
  have hsplit : pre = pre.take n ++ (((pre.drop n).take blk.length) ++
      (pre.drop n).drop blk.length) := by simp
  rw [hsplit] at h hnr
  rw [tb_noRetList_append, tb_noRetList_append, Bool.and_eq_true, Bool.and_eq_true] at hnr
  rw [holdsList_append, holdsList_noRet _ hnr.1, holdsList_append,
    holdsList_noRet _ hnr.2.1] at h
  rw [tbStmtsEqb_sound heq]
  exact h.2.1

/-- One atom of a body without `ret` holds. -/
theorem tb_holds_atom {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((pre.drop n).take 1) = true) : a.Holds rd σ := by
  have := tb_holds_slice hnr h n [.atom a] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-- One call of a body without `ret` holds. -/
theorem tb_holds_call {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret) (n : ℕ) (f : String) (args rets : List V)
    (heq : tbStmtsEqb [.call f args rets] ((pre.drop n).take 1) = true) :
    C f (args.map σ) (rets.map σ) := by
  have := tb_holds_slice hnr h n [.call f args rets] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-- One conditional call of a body without `ret` holds. -/
theorem tb_holds_callIf {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret) (n : ℕ) (c : V) (f : String) (args : List V)
    (heq : tbStmtsEqb [.callIf c f args] ((pre.drop n).take 1) = true) :
    IsInK (σ c) ∧ (σ c ≠ 0 → C f (args.map σ) []) := by
  have := tb_holds_slice hnr h n [.callIf c f args] heq
  simp only [Stmt.HoldsList, Stmt.Holds, and_true] at this
  exact this

/-- One fused `match` of calls of a body without `ret` holds. -/
theorem tb_holds_dispatch {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret) (n : ℕ) (x : V) (fs : List String)
    (args rets : List V)
    (heq : tbStmtsEqb [.dispatch x fs args rets] ((pre.drop n).take 1) = true) :
    ∃ (j : ℕ) (h : j < fs.length), σ x = ofK (Parameters.addressOfIndex j) ∧
      C fs[j] (args.map σ) (rets.map σ) := by
  have := tb_holds_slice hnr h n [.dispatch x fs args rets] heq
  simp only [Stmt.HoldsList, Stmt.Holds, and_true] at this
  exact this

end Slices

/-- A block of atoms holds exactly when each of its atoms does. -/
theorem tb_holdsList_atoms {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    ∀ {l : List Stmt}, (∀ s ∈ l, ∃ a, s = .atom a) →
      (Stmt.HoldsList C rd σ l True kret ↔ ∀ a, Stmt.atom a ∈ l → a.Holds rd σ)
  | [], _ => by simp [Stmt.HoldsList]
  | s :: l, h => by
    obtain ⟨a, rfl⟩ := h s (by simp)
    rw [Stmt.HoldsList, Stmt.Holds, tb_holdsList_atoms (fun s hs => h s (by simp [hs]))]
    constructor
    · rintro ⟨ha, hl⟩ b hb
      rcases List.mem_cons.mp hb with e | hb
      · cases e; exact ha
      · exact hl b hb
    · intro hall
      exact ⟨hall a (by simp), fun b hb => hall b (by simp [hb])⟩

section Blocks

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- Two `ret`-free blocks in sequence. -/
theorem tb_holdsList_append_noRet {A B : List Stmt} (ha : Stmt.noRetList A = true) :
    Stmt.HoldsList C rd σ (A ++ B) True kret ↔
      Stmt.HoldsList C rd σ A True kret ∧ Stmt.HoldsList C rd σ B True kret := by
  rw [holdsList_append, holdsList_noRet _ ha]

/-- A block of atoms indexed by `e < n`. -/
theorem tb_holdsList_mapAtoms (n : ℕ) (f : ℕ → Atom) :
    Stmt.HoldsList C rd σ ((List.range n).map fun e ↦ Stmt.atom (f e)) True kret ↔
      ∀ e < n, (f e).Holds rd σ := by
  rw [tb_holdsList_atoms (fun s hs => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hs; exact ⟨_, rfl⟩)]
  constructor
  · intro h e he
    exact h _ (List.mem_map.mpr ⟨e, List.mem_range.mpr he, rfl⟩)
  · intro h a ha
    obtain ⟨e, he, he'⟩ := List.mem_map.mp ha
    cases he'
    exact h e (List.mem_range.mp he)

/-- `ret`-free blocks indexed by `i < n`, in sequence. -/
theorem tb_holdsList_flatten_range (n : ℕ) (g : ℕ → List Stmt)
    (hg : ∀ i, Stmt.noRetList (g i) = true) :
    Stmt.HoldsList C rd σ ((List.range n).map g).flatten True kret ↔
      ∀ i < n, Stmt.HoldsList C rd σ (g i) True kret := by
  rw [holdsList_flatten _ (fun b hb => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb; exact hg i)]
  constructor
  · intro h i hi
    exact h.1 _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · intro h
    refine ⟨fun b hb => ?_, trivial⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact h i (List.mem_range.mp hi)

/-- Blocks without a return, one per index below `n`, hold exactly when each does, then `next`. -/
theorem tb_holdsList_range_flatten (n : ℕ) (blk : ℕ → List Stmt)
    (h : ∀ i, Stmt.noRetList (blk i) = true) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ ((List.range n).map blk).flatten next kret ↔
      (∀ i < n, Stmt.HoldsList C rd σ (blk i) True kret) ∧ next := by
  rw [holdsList_flatten _ (fun b hb => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
    exact h i)]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

/-- A forward branch whose blocks have no `ret` holds, then its continuation. -/
theorem tb_holds_ite_noRet (c : V) (z n : List Stmt)
    (hz : Stmt.noRetList z = true) (hn : Stmt.noRetList n = true) (next : Prop) :
    Stmt.Holds C rd σ (.ite c z n) next kret ↔
      (IsInK (σ c) ∧ (σ c = 0 → Stmt.HoldsList C rd σ z True kret) ∧
        (σ c ≠ 0 → Stmt.HoldsList C rd σ n True kret)) ∧ next := by
  rw [holds_noRet (.ite c z n) (by simp [Stmt.noRet, hz, hn]) next kret]
  rfl

end Blocks

/-! ## Building valuations -/

/-- `σ` with the values `.n (b + k)`, `k < n`, set to `f k`. -/
def tbSetv (σ : Val) (b n : ℕ) (f : ℕ → E) : Val := fun v =>
  if v.path = [] ∧ v.tag = 0 ∧ b ≤ v.idx ∧ v.idx < b + n then f (v.idx - b) else σ v

/-- The valuation of a function's arguments, `.n k ↦ args[k]`. -/
def tbOfArgs (args : List E) : Val := fun v => args.getD v.idx 0

/-- `σ` with the values from `.n b` on set to the words `l`. -/
abbrev tbSetl (σ : Val) (b : ℕ) (l : List E) : Val := tbSetv σ b l.length (fun k => l.getD k 0)

/-- Evaluate a lookup in a valuation built by `tbSetv`/`tbSetl` on `tbOfArgs`, the side
conditions by `omega` from the context. -/
macro "tb_look" : tactic =>
  `(tactic| simp (disch := omega) only [tbSetl, tb_set_n_lt, tb_set_n_ge, tb_set_n_in,
    Nat.add_sub_cancel_left, tb_ofArgs_n, List.getD_cons_succ, List.getD_cons_zero,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.add_zero, Nat.sub_self,
    Nat.zero_add])

/-! ## `mul_range` loops -/

theorem tb_gen_pow_mul_gen (j : ℕ) : gen ^ j * gen = gen ^ (j + 1) := (pow_succ gen j).symm

theorem tb_gen_pow_add_eq_zero_iff {N : E} (j : ℕ) : gen ^ j * gen + N = 0 ↔ N = gen ^ (j + 1) := by
  rw [tb_gen_pow_mul_gen, e_add_eq_zero_iff, eq_comm]

/-- **A `mul_range` loop, soundness**: if `f`'s relation at depth `d + 1` gives its body's meaning
`B x` and the next call, then `f` holding at `g^k` gives `N = g^m` for some `m > k` and `B` at every
`g^j`, `k ≤ j < m`. -/
theorem tb_loop_sound {P : Core.Program} {rd : Reader} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hstep : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] →
      B x ∧ (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) []))
    (k : ℕ) (h : P.Rel rd f (gen ^ k :: ps) []) :
    ∃ m, k < m ∧ N = gen ^ m ∧ ∀ j, k ≤ j → j < m → B (gen ^ j) := by
  obtain ⟨d, hd⟩ := h
  induction d generalizing k with
  | zero => exact hd.elim
  | succ d ih =>
    obtain ⟨hB, hnext⟩ := hstep d _ hd
    by_cases h0 : gen ^ k * gen + N = 0
    · refine ⟨k + 1, by omega, (tb_gen_pow_add_eq_zero_iff k).mp h0, fun j h1 h2 => ?_⟩
      rwa [show j = k by omega]
    · have := hnext h0
      rw [tb_gen_pow_mul_gen] at this
      obtain ⟨m, hm, hN, hall⟩ := ih (k + 1) this
      refine ⟨m, by omega, hN, fun j h1 h2 => ?_⟩
      rcases Nat.lt_or_ge k j with h | h
      · exact hall j (by omega) h2
      · rwa [show j = k by omega]

/-- Two runs of words read at one pointer, of one length, are equal. -/
theorem tbReadsAt_unique {rd : Reader} {p : E} {l1 l2 : List E} (h1 : TbReadsAt rd p l1)
    (h2 : TbReadsAt rd p l2) (hl : l1.length = l2.length) : l1 = l2 :=
  List.ext_getElem hl fun k hk1 hk2 => tb_loadHolds_unique (h1 k hk1) (h2 k hk2)

theorem tb_ite_neg'' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

end
end LeanVM.Guest.B1.Tables
