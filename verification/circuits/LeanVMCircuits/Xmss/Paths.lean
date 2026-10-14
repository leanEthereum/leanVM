module

public import LeanVMCircuits.Rec.Contracts
public import LeanVMCircuits.Xmss.Words

@[expose] public section

/-!
# Hash chains as paths on the dynamic bus

The leanXMSS circuit hashes each signature's chains with 42 `LINK` rows and 99 `STEP` rows (`Xmss.Circuit.chains`),
the leanSPHINCS circuit each layer's with 42 and 103. A step at position `s` of chain `c` pulls its input at the key
of `(c, s)` and pushes its output at the key of `(c, s + 1 mod 8)`; chain `i`'s link pushes the chain element at
`(i, d_i)` and pulls the end at `(i, 7)`.

* `paths_sound`: when the pushes and pulls of the steps and the 42 links balance as multisets, and the steps and the
  digits sum to 294, every chain's end is the walk from its element through positions `d_i .. 6`. Counting per key,
  the number of steps at `(c, s)` is the number at `(c, s - 1 mod 8)` plus the link's push minus its pull, so each
  chain has `k_c + [d_c ≤ s ≤ 6]` steps at `s`; there are `8 Σ k_c + Σ (7 - d_c)` steps in all, so every `k_c` is
  zero, every key is pushed once and pulled once, and the values carry along each chain.
* `paths_complete`: the steps the chains need, chain-major (`cells`), balance.
* `local_sound` and `local_complete` state these over the rows' tuples, the keys `keyK b g p` of the tweak words'
  base `b` and the tag `g` decoding to their position (`posOf`) and tag (`tagOf`).
* `Frame` and `Count`: runs adding no `STEP` or `LINK` row, or a known number; `count_circuit` counts the circuit's
  rows, and `rows_perm` makes the rows the signatures' contracts name all of them, so that the whole bus balances
  exactly when each tag's tuples do (`local_of_balanced`, `balanced_of_local`).
-/

namespace LeanVMCircuits.Xmss

open LeanVMCircuits.Rec (K Tuple ofWord toWord root tweakWord tweakK dynKey dynBit stepPullOf stepPushOf linkPushOf
  linkPullOf)
open LeanVMCircuits.Rec.Model
open Words (Dig)

/-! Runs and the `STEP` and `LINK` rows they add. -/

theorem run_bind_dyn {α β : Type} (m : M α) (f : α → M β) (s : State) :
    (m >>= f).run s = (f (m.run s).1).run (m.run s).2 := rfl

/-- `m` adds no `STEP` or `LINK` row. -/
def Frame {α : Type} (m : M α) : Prop := ∀ s, (m.run s).2.step = s.step ∧ (m.run s).2.link = s.link

theorem Frame.bind {α β : Type} {m : M α} {f : α → M β} (hm : Frame m) (hf : ∀ a, Frame (f a)) :
    Frame (m >>= f) := by
  intro s
  rw [run_bind_dyn]
  exact ⟨(hf _ _).1.trans (hm s).1, (hf _ _).2.trans (hm s).2⟩

theorem Frame.pure' {α : Type} (a : α) : Frame (pure a : M α) := fun _ => ⟨rfl, rfl⟩

theorem Frame.get' : Frame (get : M State) := fun _ => ⟨rfl, rfl⟩

theorem Frame.forIn {β γ : Type} (l : List γ) (b : β) (f : γ → β → M (ForInStep β))
    (hf : ∀ x b, Frame (f x b)) : Frame (forIn l b f) := by
  induction l generalizing b with
  | nil => exact Frame.pure' b
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine Frame.bind (hf x b) fun r => ?_
    cases r with
    | done b => exact Frame.pure' b
    | yield b => exact ih b

theorem Frame.mapM {β γ : Type} (l : List γ) (f : γ → M β) (hf : ∀ x, Frame (f x)) : Frame (l.mapM f) := by
  induction l with
  | nil => exact Frame.pure' _
  | cons x xs ih => rw [List.mapM_cons]; exact Frame.bind (hf x) fun _ => Frame.bind ih fun _ => Frame.pure' _

theorem frame_modify (f : State → State) (h : ∀ s, (f s).step = s.step ∧ (f s).link = s.link) :
    Frame (modify f) := h

theorem frame_row (t : Table) (r : List ℕ) (h1 : t ≠ .step) (h2 : t ≠ .link) : Frame (row t r) := by
  intro s
  cases t <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact ⟨rfl, rfl⟩

theorem frame_wire : Frame wire := fun _ => ⟨rfl, rfl⟩
theorem frame_union (a b : ℕ) : Frame (union a b) := fun _ => ⟨rfl, rfl⟩
theorem frame_pubRow (w : ℕ) (src : PubSource) : Frame (pubRow w src) := fun _ => ⟨rfl, rfl⟩

/-! The `frame` tactic matches atoms only up to reducible unfolding, so that it never unfolds a method (and with it a
constant such as `paramIVLimbs`, whose BLAKE2s digest Lean must not evaluate) to compare it with another. -/

syntax "frame_atom" : tactic
macro_rules | `(tactic| frame_atom) => `(tactic| exact Frame.pure' _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact Frame.get')
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_wire)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_union _ _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_pubRow _ _)
macro_rules | `(tactic| frame_atom) => `(tactic| (refine frame_row _ _ ?_ ?_ <;> decide))
macro_rules | `(tactic| frame_atom) => `(tactic| (refine frame_modify _ ?_ <;> exact fun _ => ⟨rfl, rfl⟩))

syntax "frame_step" : tactic
macro_rules | `(tactic| frame_step) => `(tactic| dsimp only)
macro_rules | `(tactic| frame_step) => `(tactic| split)
macro_rules | `(tactic| frame_step) => `(tactic| with_reducible refine Frame.mapM _ _ fun _ => ?_)
macro_rules | `(tactic| frame_step) => `(tactic| with_reducible refine Frame.forIn _ _ _ fun _ _ => ?_)
macro_rules | `(tactic| frame_step) => `(tactic| with_reducible refine Frame.bind ?_ fun _ => ?_)
macro_rules | `(tactic| frame_step) => `(tactic| with_reducible frame_atom)

/-- Splits a run into binds, loops and branches down to atoms that add no `STEP` or `LINK` row. -/
macro "frame" : tactic => `(tactic| repeat' frame_step)

theorem frame_constant (kd : Kind) (v : Limbs) : Frame (constant kd v) := by unfold constant; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_constant _ _)

theorem frame_kConst (v : ℕ) : Frame (kConst v) := frame_constant _ _
theorem frame_eConst (c0 c1 c2 : ℕ) : Frame (eConst c0 c1 c2) := frame_constant _ _
theorem frame_dConst (v : Limbs) : Frame (dConst v) := frame_constant _ _

macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_kConst _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_eConst _ _ _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_dConst _)

theorem frame_zero : Frame zero := by unfold zero; frame
theorem frame_one : Frame one := by unfold one; frame
theorem frame_kZero : Frame kZero := by unfold kZero; frame
theorem frame_expose (w : ℕ) : Frame (Rec.Model.expose w) := by unfold Rec.Model.expose; frame
theorem frame_eqConstE (a c0 c1 c2 : ℕ) : Frame (eqConstE a c0 c1 c2) := by unfold eqConstE union; frame
theorem frame_eqConstK (a v : ℕ) : Frame (eqConstK a v) := by unfold eqConstK union; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_zero)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_one)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_kZero)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_expose _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_eqConstE _ _ _ _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_eqConstK _ _)

theorem frame_emul (a b d : ℕ) : Frame (emul a b d) := by unfold emul; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_emul _ _ _)

theorem frame_add (a d : ℕ) : Frame (add a d) := by unfold add; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_add _ _)

theorem frame_mulAdd (a b d : ℕ) : Frame (mulAdd a b d) := by unfold mulAdd; frame
theorem frame_mulKAdd (a k d : ℕ) : Frame (mulKAdd a k d) := by unfold mulKAdd; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_mulAdd _ _ _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_mulKAdd _ _ _)

theorem frame_mulConstAdd (a c0 c1 c2 d : ℕ) : Frame (mulConstAdd a c0 c1 c2 d) := by unfold mulConstAdd; frame
theorem frame_split (w : ℕ) : Frame (split w) := by unfold split splitRow; frame
theorem frame_pack (bits : List ℕ) : Frame (pack bits) := by unfold pack splitRow; frame
theorem frame_castRow (given : List (ℕ × ℕ)) : Frame (castRow given) := by unfold castRow; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_mulConstAdd _ _ _ _ _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_split _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_pack _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_castRow _)

theorem frame_eToK (e : ℕ) : Frame (eToK e) := by unfold eToK; frame
theorem frame_kToE (k0 k1 k2 : ℕ) : Frame (kToE k0 k1 k2) := by unfold kToE; frame
theorem frame_dToK (d : ℕ) : Frame (dToK d) := by unfold dToK; frame
theorem frame_dToEAndK (d : ℕ) : Frame (dToEAndK d) := by unfold dToEAndK; frame
theorem frame_leafBlock (h : ℕ) (m : List ℕ) (t : ℕ) (last : Bool) : Frame (leafBlock h m t last) := by
  unfold leafBlock hashRow; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_eToK _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_kToE _ _ _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_dToK _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_dToEAndK _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_leafBlock _ _ _ _)

theorem frame_chainBlocks (words : List ℕ) (z n bytes : ℕ) : ∀ js h, Frame (chainBlocks words z n bytes js h)
  | [], h => Frame.pure' h
  | j :: js, h => by
    rw [chainBlocks]
    exact Frame.bind (frame_leafBlock _ _ _ _) fun h' => frame_chainBlocks words z n bytes js h'

theorem frame_chain (words : List ℕ) : Frame (chain words) := by
  unfold chain
  exact Frame.bind frame_kZero fun _ => Frame.bind (frame_constant _ _) fun _ => frame_chainBlocks _ _ _ _ _ _

macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_chain _)

theorem frame_words (e : ℕ) : Frame (Circuit.words e) := by unfold Circuit.words; frame
theorem frame_statementWords (zeros : ℕ) : Frame (Circuit.statementWords zeros) := by
  unfold Circuit.statementWords; frame
theorem frame_indexWord (bits : List ℕ) (shift : ℕ) : Frame (Circuit.indexWord bits shift) := by
  unfold Circuit.indexWord; frame
theorem frame_tweakHash (ty pos idx : ℕ) (pp payload : List ℕ) : Frame (Circuit.tweakHash ty pos idx pp payload) := by
  unfold Circuit.tweakHash; frame
theorem frame_digitProduct (bits : List ℕ) : Frame (Circuit.digitProduct bits) := by
  unfold Circuit.digitProduct; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_words _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_statementWords _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_indexWord _ _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_tweakHash _ _ _ _ _)
macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_digitProduct _)

theorem frame_level (l idx bit node : ℕ) (pp : List ℕ) : Frame (Circuit.level l idx bit node pp) := by
  unfold Circuit.level; frame

macro_rules | `(tactic| frame_atom) => `(tactic| exact frame_level _ _ _ _ _)

/-- `m` adds `a` `STEP` rows and `b` `LINK` rows. -/
def Count {α : Type} (m : M α) (a b : ℕ) : Prop :=
  ∀ s, (m.run s).2.step.size = s.step.size + a ∧ (m.run s).2.link.size = s.link.size + b

theorem Frame.count {α : Type} {m : M α} (h : Frame m) : Count m 0 0 := fun s => by
  rw [(h s).1, (h s).2]; exact ⟨rfl, rfl⟩

theorem Count.bind {α β : Type} {m : M α} {f : α → M β} {a b c d : ℕ} (hm : Count m a b)
    (hf : ∀ x, Count (f x) c d) : Count (m >>= f) (a + c) (b + d) := by
  intro s
  rw [run_bind_dyn]
  obtain ⟨h1, h2⟩ := hm s
  obtain ⟨h3, h4⟩ := hf (m.run s).1 (m.run s).2
  rw [h3, h4, h1, h2]
  exact ⟨by omega, by omega⟩

theorem Count.congr {α : Type} {m : M α} {a b a' b' : ℕ} (h : Count m a b) (ha : a = a') (hb : b = b') :
    Count m a' b' := ha ▸ hb ▸ h

/-- A frame, then a run adding rows. -/
theorem Count.frame_bind {α β : Type} {m : M α} {f : α → M β} {a b : ℕ} (hm : Frame m)
    (hf : ∀ x, Count (f x) a b) : Count (m >>= f) a b :=
  (hm.count.bind hf).congr (Nat.zero_add _) (Nat.zero_add _)

/-- A run adding rows, then a frame. -/
theorem Count.bind_frame {α β : Type} {m : M α} {f : α → M β} {a b : ℕ} (hm : Count m a b)
    (hf : ∀ x, Frame (f x)) : Count (m >>= f) a b :=
  (hm.bind fun x => (hf x).count).congr (Nat.add_zero _) (Nat.add_zero _)

/-- A loop whose body always continues and adds `a` and `c` rows. -/
theorem Count.forIn {β γ : Type} (l : List γ) (b : β) (f : γ → β → M (ForInStep β)) {a c : ℕ}
    (hf : ∀ x b, Count (f x b) a c) (hy : ∀ x b, ∀ s, ∃ b', ((f x b).run s).1 = .yield b') :
    Count (ForIn.forIn l b f) (a * l.length) (c * l.length) := by
  induction l generalizing b with
  | nil => intro s; exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    intro s
    obtain ⟨b', hb'⟩ := hy x b s
    have hrun : (ForIn.forIn (x :: xs) b f).run s = (ForIn.forIn xs b' f).run ((f x b).run s).2 := by
      rw [List.forIn_cons, run_bind_dyn, hb']
    rw [hrun]
    obtain ⟨h1, h2⟩ := hf x b s
    obtain ⟨h3, h4⟩ := ih b' ((f x b).run s).2
    rw [h3, h4, h1, h2, List.length_cons, Nat.mul_succ, Nat.mul_succ]
    exact ⟨by omega, by omega⟩

theorem yields_pure {β : Type} (b : β) : ∀ s, ∃ b', ((pure (ForInStep.yield b) : M (ForInStep β)).run s).1 =
    .yield b' := fun _ => ⟨b, rfl⟩

theorem yields_bind {α β : Type} (m : M α) (k : α → M (ForInStep β))
    (h : ∀ a, ∀ s, ∃ b, ((k a).run s).1 = .yield b) : ∀ s, ∃ b, ((m >>= k).run s).1 = .yield b := fun s => by
  rw [run_bind_dyn]; exact h _ _

/-- A loop body that always continues, without evaluating it. -/
macro "yields" : tactic => `(tactic| repeat' (first
  | (with_reducible exact yields_pure _)
  | (with_reducible refine yields_bind _ _ fun _ => ?_)
  | dsimp only))

theorem count_row_step (r : List ℕ) : Count (row .step r) 1 0 := fun s => ⟨Array.size_push _, rfl⟩
theorem count_row_link (r : List ℕ) : Count (row .link r) 0 1 := fun s => ⟨rfl, Array.size_push _⟩

theorem frame_leafRow (h : ℕ) (m : List ℕ) (t : ℕ) (last : Bool) : Frame (leafRow h m t last) := by
  unfold leafRow; frame

theorem count_chainStep (idx : ℕ) (pp : ℕ × ℕ) (base tag act : ℕ) : Count (chainStep idx pp base tag act) 1 0 := by
  unfold chainStep
  exact Count.frame_bind frame_wire fun _ => Count.frame_bind frame_wire fun _ => Count.frame_bind frame_wire
    fun _ => Count.frame_bind frame_kZero fun _ => Count.frame_bind (frame_dConst _) fun _ =>
      Count.frame_bind (frame_leafRow _ _ _ _) fun _ => count_row_step _

theorem count_link (w d0 d1 d2 act : ℕ) : Count (link w d0 d1 d2 act) 0 1 := by
  unfold link
  exact Count.frame_bind frame_wire fun _ => Count.frame_bind frame_wire fun _ => Count.frame_bind frame_wire
    fun _ => Count.frame_bind frame_wire fun _ => Count.bind_frame (count_row_link _) fun _ => Frame.pure' _

theorem count_chains (b g steps idx : ℕ) (pp digitBits : List ℕ) :
    Count (Circuit.chains b g steps idx pp digitBits) steps 42 := by
  unfold Circuit.chains
  refine Count.frame_bind frame_wire fun act => Count.frame_bind (frame_eqConstK _ _) fun _ =>
    Count.frame_bind (frame_kConst _) fun base => Count.frame_bind (frame_kConst _) fun tag => ?_
  refine (Count.bind (Count.forIn _ _ _ (a := 0) (c := 1) (fun i b => ?_) fun _ _ => by yields) fun ends =>
    Count.bind_frame (Count.forIn _ _ _ (a := 1) (c := 0) (fun _ _ => ?_) fun _ _ => by yields)
      fun _ => Frame.pure' _).congr (by simp) (by simp)
  · exact Count.frame_bind (frame_kConst _) fun _ => Count.bind_frame (count_link _ _ _ _ _) fun _ => Frame.pure' _
  · exact Count.bind_frame (count_chainStep _ _ _ _ _) fun _ => Frame.pure' _

/-- A signature adds its chains' 99 `STEP` and 42 `LINK` rows. -/
theorem count_signature (j : ℕ) : Count (Circuit.signature j) 99 42 := by
  unfold Circuit.signature
  repeat (first
    | with_reducible exact Count.bind_frame (count_chains _ _ _ _ _ _) fun _ => by frame
    | with_reducible refine Count.frame_bind (by frame) fun _ => ?_
    | dsimp only)

/-- The circuit of `n` signatures has `99 n` `STEP` rows and `42 n` `LINK` rows. -/
theorem count_circuit (n : ℕ) : Count (Circuit.circuit n) (99 * n) (42 * n) := by
  unfold Circuit.circuit
  refine (Count.bind_frame (Count.forIn _ _ _ (a := 99) (c := 42) (fun j _ => ?_) fun _ _ => by yields)
    fun _ => Frame.pure' _).congr (by simp) (by simp)
  exact Count.bind_frame (count_signature j) fun _ => Frame.pure' _

/-! Paths through a balanced multiset of tuples, keyed by chain and position. -/

section Paths

variable {V : Type}

/-- The tuple a step `((c, s), in, out)` pushes: its output at the next position of its chain. -/
def pushOf (x : (ℕ × ℕ) × V × V) : (ℕ × ℕ) × V := ((x.1.1, (x.1.2 + 1) % 8), x.2.2)

/-- The tuple a step pulls: its input at its own position. -/
def pullOf (x : (ℕ × ℕ) × V × V) : (ℕ × ℕ) × V := (x.1, x.2.1)

/-- Chain `i` walked by `H` from `v` at position `d` to position `s`. -/
def walk (H : ℕ → ℕ → V → V) (i d : ℕ) (v : V) (s : ℕ) : V :=
  (List.range' d (s - d)).foldl (fun v s => H i s v) v

theorem walk_self (H : ℕ → ℕ → V → V) (i d : ℕ) (v : V) : walk H i d v d = v := by
  simp [walk]

theorem walk_succ (H : ℕ → ℕ → V → V) (i d : ℕ) (v : V) (s : ℕ) (h : d ≤ s) :
    walk H i d v (s + 1) = H i s (walk H i d v s) := by
  unfold walk
  rw [show s + 1 - d = s - d + 1 by omega, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
    show d + 1 * (s - d) = s by omega]

theorem range_countP (n c : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (List.range n).countP (fun i => decide (i = c ∧ P i)) = if c < n ∧ P c then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, List.countP_singleton]
    by_cases hc : c = n
    · subst hc
      by_cases hp : P c <;> simp [hp]
    · by_cases h1 : c < n
      · simp [Ne.symm hc, h1, show c < n + 1 by omega]
      · simp [Ne.symm hc, h1, show ¬ c < n + 1 by omega]

/-- A list's length is the sum over keys of its entries at each key, when every key is in the set. -/
theorem length_eq_sum_countP {α : Type} (l : List ((ℕ × ℕ) × α)) (S : Finset (ℕ × ℕ)) (h : ∀ x ∈ l, x.1 ∈ S) :
    l.length = ∑ κ ∈ S, l.countP (fun x => decide (x.1 = κ)) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
    simp only [List.countP_cons, decide_eq_true_eq]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (h x List.mem_cons_self)]

theorem sum_lt_42 (m : ℕ) (hm : 42 ≤ m) (g : ℕ → ℕ) :
    ∑ c ∈ Finset.range m, (if c < 42 then g c else 0) = ∑ c ∈ Finset.range 42, g c := by
  induction m, hm using Nat.le_induction with
  | base => exact Finset.sum_congr rfl fun c hc => if_pos (Finset.mem_range.mp hc)
  | succ m hm ih => rw [Finset.sum_range_succ, ih, if_neg (by omega), Nat.add_zero]

theorem sum_cells (d : ℕ) (hd : d < 8) :
    ∑ s ∈ Finset.range 8, (if d ≤ s ∧ s ≤ 6 then 1 else 0) = 7 - d := by
  interval_cases d <;> simp only [Finset.sum_range_succ, Finset.sum_range_zero] <;> decide

/-- A tuple pushed exactly once at its key is the only tuple pulled there. -/
theorem uniq_of_coe {β κ : Type} [DecidableEq κ] {A B : List β} (h : (↑A : Multiset β) = ↑B) (key : β → κ)
    {x y : β} (hx : x ∈ A) (hy : y ∈ B) (hk : key y = key x)
    (h1 : A.countP (fun z => decide (key z = key x)) = 1) : y = x := by
  have hf := congrArg (Multiset.filter (fun z => key z = key x)) h
  simp only [Multiset.filter_coe] at hf
  rw [List.countP_eq_length_filter] at h1
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
  have hxa : x ∈ A.filter (fun z => decide (key z = key x)) := List.mem_filter.mpr ⟨hx, by simp⟩
  have hyb : y ∈ B.filter (fun z => decide (key z = key x)) := List.mem_filter.mpr ⟨hy, by simp [hk]⟩
  rw [ha] at hxa hf
  have hy' : y ∈ (↑[a] : Multiset β) := by rw [hf]; exact Multiset.mem_coe.mpr hyb
  rw [Multiset.mem_coe, List.mem_singleton] at hy'
  rw [List.mem_singleton] at hxa
  rw [hy', hxa]

/-- Balanced paths: when the steps' pushes and the links' pushes are the steps' pulls and the links' pulls, the 99
steps (with the digits) are what the chains need and every chain's end is its walk to position 7. -/
theorem paths_sound (H : ℕ → ℕ → V → V) (steps : List ((ℕ × ℕ) × V × V)) (d : ℕ → ℕ) (tip fin : ℕ → V)
    (hstep : ∀ x ∈ steps, x.1.1 < 64 ∧ x.1.2 < 8 ∧ x.2.2 = H x.1.1 x.1.2 x.2.1) (hd : ∀ i < 42, d i < 8)
    (hlen : steps.length + ∑ i ∈ Finset.range 42, d i = 294)
    (hbal : Multiset.ofList (steps.map pushOf ++ (List.range 42).map fun i => ((i, d i), tip i)) =
      Multiset.ofList (steps.map pullOf ++ (List.range 42).map fun i => ((i, 7), fin i))) :
    ∀ i < 42, fin i = walk H i (d i) (tip i) 7 := by
  set P := steps.map pushOf ++ (List.range 42).map fun i => ((i, d i), tip i) with hP
  set Q := steps.map pullOf ++ (List.range 42).map fun i => ((i, 7), fin i) with hQ
  set N : ℕ → ℕ → ℕ := fun c s => steps.countP (fun x => decide (x.1 = (c, s))) with hNdef
  -- The tuples at each key.
  have hPc : ∀ c s, s < 8 → P.countP (fun y => decide (y.1 = (c, s))) =
      N c ((s + 7) % 8) + if c < 42 ∧ d c = s then 1 else 0 := by
    intro c s hs
    rw [hP, List.countP_append, List.countP_map, List.countP_map, ← range_countP 42 c (fun i => d i = s)]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine List.countP_congr fun x hx => ?_
      obtain ⟨h1, h2, -⟩ := hstep x hx
      obtain ⟨⟨xc, xs⟩, xi, xo⟩ := x
      simp only [Function.comp, pushOf, decide_eq_true_eq, Prod.mk.injEq] at h1 h2 ⊢
      constructor
      · rintro ⟨rfl, h⟩; exact ⟨rfl, by omega⟩
      · rintro ⟨rfl, h⟩; exact ⟨rfl, by omega⟩
    · refine List.countP_congr fun i _ => ?_
      simp only [Function.comp, decide_eq_true_eq, Prod.mk.injEq]
  have hQc : ∀ c s, Q.countP (fun y => decide (y.1 = (c, s))) = N c s + if c < 42 ∧ s = 7 then 1 else 0 := by
    intro c s
    rw [hQ, List.countP_append, List.countP_map, List.countP_map, ← range_countP 42 c (fun _ => s = 7)]
    refine congrArg₂ (· + ·) (List.countP_congr fun x _ => ?_) (List.countP_congr fun i _ => ?_)
    · exact Iff.rfl
    simp only [Function.comp, decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  have hcount : ∀ c s, s < 8 → N c ((s + 7) % 8) + (if c < 42 ∧ d c = s then 1 else 0) =
      N c s + if c < 42 ∧ s = 7 then 1 else 0 := by
    intro c s hs
    have h := congrArg (Multiset.countP (fun y : (ℕ × ℕ) × V => y.1 = (c, s))) hbal
    simp only [Multiset.coe_countP] at h
    rw [← hPc c s hs, ← hQc c s]
    exact h
  -- Each chain's steps at a position.
  have hN : ∀ c s, s < 8 → N c s = N c 7 + if c < 42 ∧ d c ≤ s ∧ s ≤ 6 then 1 else 0 := by
    intro c s hs
    induction s with
    | zero =>
      have h := hcount c 0 (by norm_num)
      rw [show (0 + 7) % 8 = 7 from rfl] at h
      split_ifs at h ⊢ <;> (try simp only [not_and, not_le, and_false] at *) <;> omega
    | succ s ih =>
      by_cases h7 : s + 1 = 7
      · rw [h7]; simp
      have h := hcount c (s + 1) hs
      rw [show (s + 1 + 7) % 8 = s by omega] at h
      have ih := ih (by omega)
      split_ifs at h ih ⊢ <;> (try simp only [not_and, not_le, and_false] at *) <;> omega
  -- No chain has a cycle: all 99 steps are needed ones.
  have hd7 : ∑ c ∈ Finset.range 42, (7 - d c) + ∑ c ∈ Finset.range 42, d c = 294 := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun c hc => show 7 - d c + d c = 7 by
      have := hd c (Finset.mem_range.mp hc); omega]
    simp
  have htotal : steps.length = 8 * ∑ c ∈ Finset.range 64, N c 7 + ∑ c ∈ Finset.range 42, (7 - d c) := by
    have hl := length_eq_sum_countP steps (Finset.range 64 ×ˢ Finset.range 8) fun x hx => by
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]; exact ⟨(hstep x hx).1, (hstep x hx).2.1⟩
    rw [hl, Finset.sum_product, ← sum_lt_42 64 (by norm_num), Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.sum_congr rfl fun s hs => hN c s (Finset.mem_range.mp hs), Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    by_cases h42 : c < 42
    · rw [if_pos h42, ← sum_cells (d c) (hd c h42)]
      simp only [h42, true_and]
    · rw [if_neg h42]
      simp [h42]
  have hz : ∀ c < 64, N c 7 = 0 := by
    have h0 : ∑ c ∈ Finset.range 64, N c 7 = 0 := by omega
    intro c hc
    exact (Finset.sum_eq_zero_iff.mp h0) c (Finset.mem_range.mpr hc)
  have hN' : ∀ c < 64, ∀ s < 8, N c s = if c < 42 ∧ d c ≤ s ∧ s ≤ 6 then 1 else 0 := by
    intro c hc s hs
    rw [hN c s hs, hz c hc, Nat.zero_add]
  -- The values along each chain.
  have hpath : ∀ i < 42, ∀ k, d i + k ≤ 7 → ∀ y ∈ Q, y.1 = (i, d i + k) →
      y.2 = walk H i (d i) (tip i) (d i + k) := by
    intro i hi k
    have hdi := hd i hi
    induction k with
    | zero =>
      intro _ y hy hk
      have hx : ((i, d i), tip i) ∈ P :=
        List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
      have hc1 : P.countP (fun z => decide (z.1 = ((i, d i), tip i).1)) = 1 := by
        rw [hPc i (d i) hdi, hN' i (by omega) _ (Nat.mod_lt _ (by norm_num)), if_neg (by omega),
          if_pos ⟨hi, rfl⟩]
      have := uniq_of_coe hbal Prod.fst hx hy (by rw [hk]; rfl) hc1
      rw [this, Nat.add_zero, walk_self]
    | succ k ih =>
      intro hk y hy hyk
      have hs : d i + k ≤ 6 := by omega
      have hpos : 0 < N i (d i + k) := by
        rw [hN' i (by omega) _ (by omega), if_pos ⟨hi, by omega, hs⟩]; norm_num
      obtain ⟨x, hxs, hxk⟩ := List.countP_pos_iff.mp hpos
      have hxk' : x.1 = (i, d i + k) := by simpa using hxk
      have hin : x.2.1 = walk H i (d i) (tip i) (d i + k) :=
        ih (by omega) (pullOf x) (List.mem_append_left _ (List.mem_map_of_mem hxs)) hxk'
      obtain ⟨-, -, hout⟩ := hstep x hxs
      have hx1 : x.1.1 = i := by rw [hxk']
      have hx2 : x.1.2 = d i + k := by rw [hxk']
      have hpush : pushOf x = ((i, d i + (k + 1)), walk H i (d i) (tip i) (d i + (k + 1))) := by
        rw [← Nat.add_assoc, walk_succ _ _ _ _ _ (by omega), ← hin]
        simp only [pushOf, hout, hx1, hx2, show (d i + k + 1) % 8 = d i + k + 1 by omega]
      have hxP : pushOf x ∈ P := List.mem_append_left _ (List.mem_map_of_mem hxs)
      have hc1 : P.countP (fun z => decide (z.1 = (pushOf x).1)) = 1 := by
        rw [hpush, hPc i (d i + (k + 1)) (by omega), show (d i + (k + 1) + 7) % 8 = d i + k by omega,
          hN' i (by omega) _ (by omega), if_pos ⟨hi, by omega, hs⟩, if_neg (by omega)]
      have := uniq_of_coe hbal Prod.fst hxP hy (by rw [hyk, hpush]) hc1
      rw [this, hpush]
  intro i hi
  have hdi := hd i hi
  have hy : ((i, 7), fin i) ∈ Q := List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  have := hpath i hi (7 - d i) (by omega) _ hy (by simp only [Prod.mk.injEq, true_and]; omega)
  rwa [show d i + (7 - d i) = 7 by omega] at this

/-- The positions the chains need, chain-major: chain `i` from position `d i` to position 6. -/
def cells (d : ℕ → ℕ) : List (ℕ × ℕ) :=
  (List.range 42).flatMap fun i => (List.range' (d i) (7 - d i)).map fun s => (i, s)

/-- The step at a cell, walking the chain from its element. -/
def stepAt (H : ℕ → ℕ → V → V) (d : ℕ → ℕ) (tip : ℕ → V) (κ : ℕ × ℕ) : (ℕ × ℕ) × V × V :=
  (κ, walk H κ.1 (d κ.1) (tip κ.1) κ.2, walk H κ.1 (d κ.1) (tip κ.1) (κ.2 + 1))

theorem sum_range_list (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem cells_length (d : ℕ → ℕ) : (cells d).length = ∑ i ∈ Finset.range 42, (7 - d i) := by
  rw [cells, List.length_flatMap]
  simp only [List.length_map, List.length_range']
  exact sum_range_list _ _

/-- The cells are chain `c`'s positions `d c .. 6`. -/
theorem mem_cells (d : ℕ → ℕ) (κ : ℕ × ℕ) : κ ∈ cells d ↔ κ.1 < 42 ∧ d κ.1 ≤ κ.2 ∧ κ.2 < 7 := by
  obtain ⟨c, s⟩ := κ
  simp only [cells, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_range'_1, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, s', ⟨h1, h2⟩, rfl, rfl⟩
    exact ⟨hi, h1, by omega⟩
  · rintro ⟨hc, h1, h2⟩
    exact ⟨c, hc, s, ⟨h1, by omega⟩, rfl, rfl⟩

theorem cells_getD_mem (d : ℕ → ℕ) (m : ℕ) (hm : m < (cells d).length) : (cells d).getD m (0, 0) ∈ cells d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
  exact List.getElem_mem hm

theorem range'_shift_map {β : Type} (f : ℕ → β) (d n : ℕ) :
    (List.range' d n).map (fun s => f (s + 1)) = (List.range' (d + 1) n).map f := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [List.range'_succ, List.range'_succ, List.map_cons, List.map_cons, ih]

/-- A list built per element and a list of one entry per element, as one multiset per element. -/
theorem coe_flatMap_map {α β : Type} (l : List α) (F : α → List β) (b : α → β) :
    Multiset.ofList (l.flatMap F ++ l.map b) = (Multiset.ofList l).bind fun a => Multiset.ofList (F a) + {b a} := by
  rw [← Multiset.coe_add, ← Multiset.coe_bind, ← Multiset.map_coe, ← Multiset.bind_singleton, ← Multiset.bind_add]

/-- Two lists built per element, as one multiset per element. -/
theorem coe_flatMap_flatMap {α β : Type} (l : List α) (F G : α → List β) :
    Multiset.ofList (l.flatMap F ++ l.flatMap G) = Multiset.ofList (l.flatMap fun a => F a ++ G a) := by
  rw [← Multiset.coe_add, ← Multiset.coe_bind, ← Multiset.coe_bind, ← Multiset.coe_bind, ← Multiset.bind_add]
  simp only [Multiset.coe_add]

/-- The steps the chains need balance: chain by chain, the link's push and the steps' pushes are the steps' pulls and
the link's pull, the walk at positions `d i .. 7`. -/
theorem paths_complete (H : ℕ → ℕ → V → V) (d : ℕ → ℕ) (tip : ℕ → V) (hd : ∀ i < 42, d i < 8) :
    Multiset.ofList ((cells d).map (pushOf ∘ stepAt H d tip) ++ (List.range 42).map fun i => ((i, d i), tip i)) =
      Multiset.ofList ((cells d).map (pullOf ∘ stepAt H d tip) ++
        (List.range 42).map fun i => ((i, 7), walk H i (d i) (tip i) 7)) := by
  rw [cells, List.map_flatMap, List.map_flatMap, coe_flatMap_map, coe_flatMap_map]
  refine Multiset.bind_congr fun i hi => ?_
  have hdi := hd i (List.mem_range.mp (Multiset.mem_coe.mp hi))
  set k : ℕ → (ℕ × ℕ) × V := fun s => ((i, s), walk H i (d i) (tip i) s) with hk
  have hpushL : ((i, d i), tip i) :: List.map ((pushOf ∘ stepAt H d tip) ∘ fun s => (i, s))
      (List.range' (d i) (7 - d i)) = (List.range' (d i) (7 - d i + 1)).map k := by
    rw [List.range'_succ, List.map_cons, ← range'_shift_map k]
    refine List.cons_eq_cons.mpr ⟨by simp only [hk, walk_self], List.map_congr_left fun s hs => ?_⟩
    have hs7 : s < 7 := by rw [List.mem_range'_1] at hs; omega
    simp only [Function.comp, pushOf, stepAt, hk, show (s + 1) % 8 = s + 1 by omega]
  have hpullL : List.map ((pullOf ∘ stepAt H d tip) ∘ fun s => (i, s)) (List.range' (d i) (7 - d i)) ++
      [((i, 7), walk H i (d i) (tip i) 7)] = (List.range' (d i) (7 - d i + 1)).map k := by
    rw [List.range'_concat, List.map_append, show d i + 1 * (7 - d i) = 7 by omega]
    rfl
  rw [List.map_map, List.map_map, Multiset.add_comm, Multiset.singleton_add, Multiset.cons_coe, ← Multiset.coe_singleton,
    Multiset.coe_add, hpushL, hpullL]

end Paths

/-! The keys of a tag's tuples. -/

/-- The key of position `p` of tag `g` over the base word `b`: `X^63 + b + X^32 p + g · X^41`. -/
noncomputable def keyK (b g p : ℕ) : K := dynKey (tweakK (ofWord b) p) (ofWord (g * 2 ^ 41))

/-- That key as a word. -/
def keyNat (b g p : ℕ) : ℕ := tweakWord b p + 2 ^ 41 * (g + 2 ^ 22 * 1)

/-- The position a key names. -/
noncomputable def posOf (k : K) : ℕ := toWord k / 2 ^ 32 % 2 ^ 9

/-- The tag a key names. -/
noncomputable def tagOf (k : K) : ℕ := toWord k / 2 ^ 41 % 2 ^ 22

theorem tweak0_one (p : ℕ) : Circuit.tweak0 1 p = tweakWord (2 ^ 8) p := by
  unfold Circuit.tweak0 tweakWord; ring

theorem ofWord_mul_two_pow_41 (j : ℕ) (hj : j < 2 ^ 22) : ofWord (j * 2 ^ 41) = root ^ 41 * Rec.ev j := by
  rw [ofWord, Nat.mod_eq_of_lt (by omega), Nat.mul_comm, Rec.ev_two_pow_mul]

theorem keyNat_lt (b g p : ℕ) (hb : b < 2 ^ 32) (hp : p < 2 ^ 9) (hg : g < 2 ^ 22) : keyNat b g p < 2 ^ 64 := by
  unfold keyNat tweakWord; omega

theorem keyK_eq (b g p : ℕ) (hb : b < 2 ^ 32) (hp : p < 2 ^ 9) (hg : g < 2 ^ 22) :
    keyK b g p = ofWord (keyNat b g p) := by
  have ht : tweakWord b p < 2 ^ 41 := by unfold tweakWord; omega
  have hR : ofWord (keyNat b g p) = Rec.ev (tweakWord b p) + root ^ 41 * (Rec.ev g + root ^ 22 * 1) := by
    rw [ofWord, Nat.mod_eq_of_lt (keyNat_lt b g p hb hp hg), keyNat, Rec.ev_add_two_pow_mul 41 _ _ ht,
      Rec.ev_add_two_pow_mul 22 _ _ hg, Rec.ev_one]
  have hT : tweakK (ofWord b) p = Rec.ev (tweakWord b p) := by
    rw [← Rec.ofWord_tweakWord b p hb (by omega), ofWord, Nat.mod_eq_of_lt (by omega)]
  rw [hR, keyK, dynKey, hT, ofWord_mul_two_pow_41 g hg, dynBit, Rec.ofWord_two_pow 63 (by norm_num)]
  ring

theorem toWord_keyK (b g p : ℕ) (hb : b < 2 ^ 32) (hp : p < 2 ^ 9) (hg : g < 2 ^ 22) :
    toWord (keyK b g p) = keyNat b g p := by
  rw [keyK_eq b g p hb hp hg, Rec.toWord_ofWord _ (keyNat_lt b g p hb hp hg)]

theorem posOf_keyK (b g p : ℕ) (hb : b < 2 ^ 32) (hp : p < 2 ^ 9) (hg : g < 2 ^ 22) : posOf (keyK b g p) = p := by
  rw [posOf, toWord_keyK b g p hb hp hg, keyNat, tweakWord]; omega

theorem tagOf_keyK (b g p : ℕ) (hb : b < 2 ^ 32) (hp : p < 2 ^ 9) (hg : g < 2 ^ 22) : tagOf (keyK b g p) = g := by
  rw [tagOf, toWord_keyK b g p hb hp hg, keyNat, tweakWord]; omega

theorem toWord_link (b i g : ℕ) (hb : b < 2 ^ 32) (hi : i < 42) (hg : g < 2 ^ 22) :
    toWord (ofWord (tweakWord b (8 * i) + g * 2 ^ 41)) = b + i * 34359738368 + g * 2199023255552 := by
  rw [Rec.toWord_ofWord _ (by unfold tweakWord; omega)]
  unfold tweakWord
  ring

theorem posOf_tweak (b p : ℕ) (hb : b < 2 ^ 32) (hp : p < 2 ^ 9) : posOf (tweakK (ofWord b) p) = p := by
  rw [← Rec.ofWord_tweakWord b p hb (by omega), posOf, Rec.toWord_ofWord _ (by unfold tweakWord; omega)]
  unfold tweakWord
  omega

theorem keyK_def (b g p : ℕ) : keyK b g p = dynKey (tweakK (ofWord b) p) (ofWord (g * 2 ^ 41)) := rfl

/-- Three Boolean digit bits weighted `X^32`, `X^33`, `X^34`: `X^32` times the digit. -/
theorem digit_weights (x0 x1 x2 : K) (h0 : x0 = 0 ∨ x0 = 1) (h1 : x1 = 0 ∨ x1 = 1) (h2 : x2 = 0 ∨ x2 = 1) :
    ofWord (2 ^ 32) * x0 + ofWord (2 ^ 33) * x1 + ofWord (2 ^ 34) * x2 =
      root ^ 32 * Rec.ev ((if x0 = 1 then 1 else 0) + (if x1 = 1 then 2 else 0) + (if x2 = 1 then 4 else 0)) := by
  have e : ∀ a b c : ℕ, a < 2 → b < 2 → Rec.ev (a + 2 * b + 4 * c) = Rec.ev a + root * (Rec.ev b + root * Rec.ev c) :=
    fun a b c ha hb => by
      rw [show a + 2 * b + 4 * c = a + 2 ^ 1 * (b + 2 ^ 1 * c) by ring, Rec.ev_add_two_pow_mul 1 _ _ ha,
        Rec.ev_add_two_pow_mul 1 _ _ hb, pow_one]
  have hb : ∀ x : K, (x = 0 ∨ x = 1) → x = Rec.ev (if x = 1 then 1 else 0) ∧ (if x = 1 then 1 else 0 : ℕ) < 2 := by
    rintro x (rfl | rfl)
    · simp [Rec.ev_zero]
    · simp [Rec.ev_one]
  have h2' : (if x1 = 1 then 2 else 0 : ℕ) = 2 * (if x1 = 1 then 1 else 0) := by split_ifs <;> rfl
  have h4' : (if x2 = 1 then 4 else 0 : ℕ) = 4 * (if x2 = 1 then 1 else 0) := by split_ifs <;> rfl
  rw [h2', h4', e _ _ _ (hb x0 h0).2 (hb x1 h1).2, ← (hb x0 h0).1, ← (hb x1 h1).1, ← (hb x2 h2).1,
    Rec.ofWord_two_pow 32 (by norm_num), Rec.ofWord_two_pow 33 (by norm_num), Rec.ofWord_two_pow 34 (by norm_num)]
  ring

theorem ofWord_link (b i g : ℕ) (hb : b < 2 ^ 32) (hi : i < 42) (hg : g < 2 ^ 22) :
    ofWord (tweakWord b (8 * i) + g * 2 ^ 41) = ofWord b + root ^ 32 * (root ^ 3 * Rec.ev i) + root ^ 41 * Rec.ev g := by
  have ht : tweakWord b (8 * i) < 2 ^ 41 := by unfold tweakWord; omega
  rw [ofWord, Nat.mod_eq_of_lt (by unfold tweakWord; omega), Nat.mul_comm g,
    Rec.ev_add_two_pow_mul 41 _ _ ht, ← Nat.mod_eq_of_lt (show tweakWord b (8 * i) < 2 ^ 64 by omega), ← ofWord,
    Rec.ofWord_tweakWord _ _ hb (by omega), tweakK, show 8 * i = 2 ^ 3 * i by norm_num, Rec.ev_two_pow_mul 3 i]

/-- A link's push key: at the position of its digit. -/
theorem link_push_key (b i g : ℕ) (hb : b < 2 ^ 32) (hi : i < 42) (hg : g < 2 ^ 22) (x0 x1 x2 : K)
    (h0 : x0 = 0 ∨ x0 = 1) (h1 : x1 = 0 ∨ x1 = 1) (h2 : x2 = 0 ∨ x2 = 1) :
    dynKey (ofWord (tweakWord b (8 * i) + g * 2 ^ 41))
        (ofWord (2 ^ 32) * x0 + ofWord (2 ^ 33) * x1 + ofWord (2 ^ 34) * x2) =
      keyK b g (8 * i + ((if x0 = 1 then 1 else 0) + (if x1 = 1 then 2 else 0) + (if x2 = 1 then 4 else 0))) := by
  have hd : (if x0 = 1 then 1 else 0) + (if x1 = 1 then 2 else 0) + (if x2 = 1 then 4 else 0) < 2 ^ 3 := by
    split_ifs <;> norm_num
  rw [digit_weights x0 x1 x2 h0 h1 h2, keyK, dynKey, dynKey, ofWord_link b i g hb hi hg, ofWord_mul_two_pow_41 g hg,
    tweakK, Nat.add_comm (8 * i), show 8 * i = 2 ^ 3 * i by norm_num, Rec.ev_add_two_pow_mul 3 _ _ hd]
  ring

/-- A link's pull key, when active: at position 7. -/
theorem link_pull_key (b i g : ℕ) (hb : b < 2 ^ 32) (hi : i < 42) (hg : g < 2 ^ 22) :
    dynKey (ofWord (tweakWord b (8 * i) + g * 2 ^ 41)) (ofWord (2 ^ 32 + 2 ^ 33 + 2 ^ 34) * 1) =
      keyK b g (8 * i + 7) := by
  have h7 : ofWord (2 ^ 32 + 2 ^ 33 + 2 ^ 34) * 1 = ofWord (2 ^ 32) * 1 + ofWord (2 ^ 33) * 1 + ofWord (2 ^ 34) * 1 := by
    have e : ofWord (2 ^ 32 + 2 ^ 33 + 2 ^ 34) = root ^ 32 * (1 + root * (1 + root * 1)) := by
      rw [ofWord, Nat.mod_eq_of_lt (by norm_num),
        show (2 : ℕ) ^ 32 + 2 ^ 33 + 2 ^ 34 = 2 ^ 32 * (1 + 2 ^ 1 * (1 + 2 ^ 1 * 1)) by norm_num,
        Rec.ev_two_pow_mul, Rec.ev_add_two_pow_mul 1 _ _ (by norm_num), Rec.ev_add_two_pow_mul 1 _ _ (by norm_num),
        Rec.ev_one, pow_one]
    rw [e, Rec.ofWord_two_pow 32 (by norm_num), Rec.ofWord_two_pow 33 (by norm_num),
      Rec.ofWord_two_pow 34 (by norm_num)]
    ring
  have h := link_push_key b i g hb hi hg 1 1 1 (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  simp only [eq_self_iff_true, if_true] at h
  rw [h7, h]

/-! Tag-local balance, read off and built. -/

/-- A tuple's two words as 64-bit words. -/
noncomputable def wd (t : Tuple) : Dig := (BitVec.ofNat 64 (toWord t.2.1), BitVec.ofNat 64 (toWord t.2.2))

/-- A tuple decoded: its key's chain and position, and its words. -/
noncomputable def decT (t : Tuple) : (ℕ × ℕ) × Dig := ((posOf t.1 / 8, posOf t.1 % 8), wd t)

/-- Tag `g`'s tuple over the base `b` of a chain, position and two words. -/
noncomputable def encT (b g : ℕ) (x : (ℕ × ℕ) × Dig) : Tuple :=
  (keyK b g (8 * x.1.1 + x.1.2), ofWord x.2.1.toNat, ofWord x.2.2.toNat)

/-- A chain step's hash over the base `b`, the index word `I` and the parameter `P0, P1`: the first two words of the
hash of the tweak word of position `8c + s`, `I`, `P0`, `P1` and the two words of `v`. -/
def stepHash (b : ℕ) (I P0 P1 : Words.W) (c s : ℕ) (v : Dig) : Dig :=
  (Rec.digest (Rec.hashWords [BitVec.ofNat 64 (tweakWord b (8 * c + s)), I, P0, P1, v.1, v.2]) 0,
    Rec.digest (Rec.hashWords [BitVec.ofNat 64 (tweakWord b (8 * c + s)), I, P0, P1, v.1, v.2]) 1)

/-- leanXMSS's chain steps are `stepHash` over the base `2^8` and the index word of the epoch. -/
theorem walk_stepHash (e : ℕ) (P0 P1 : Words.W) (i d : ℕ) (v : Dig) :
    walk (stepHash (2 ^ 8) (Words.tweak1 e) P0 P1) i d v 7 = Words.chainFrom i e (P0, P1) d v := by
  have h : stepHash (2 ^ 8) (Words.tweak1 e) P0 P1 = fun c s v => Words.chainStep c s e (P0, P1) v := by
    funext c s v
    simp only [stepHash, Words.chainStep, Words.th, Words.tweak0, tweak0_one, List.cons_append, List.nil_append]
  rw [h]
  rfl

/-- The tuples the `STEP` rows `R` and the `LINK` rows `L` push are the tuples they pull. -/
def LocalBal (val : Val) (R L : List (List ℕ)) : Prop :=
  Multiset.ofList (R.map (stepPushRow val) ++ L.map (linkPushRow val)) =
    Multiset.ofList (R.map (stepPullRow val) ++ L.map (linkPullRow val))

/-- A tag's balanced tuples: the steps `R` at positions `pos r` of tag `g` over the base `b`, each hashing its pulled
words into its pushed ones by `H`, and the 42 links, make every chain's end the walk from its element. -/
theorem local_sound (H : ℕ → ℕ → Dig → Dig) (b g : ℕ) (hb : b < 2 ^ 32) (hg : g < 2 ^ 22) (val : Val)
    (R : List (List ℕ)) (pos : List ℕ → ℕ) (Lrow : ℕ → List ℕ) (d : ℕ → ℕ) (hpos : ∀ r ∈ R, pos r < 2 ^ 9)
    (hpull : ∀ r ∈ R, (stepPullRow val r).1 = keyK b g (pos r))
    (hpush : ∀ r ∈ R, (stepPushRow val r).1 = keyK b g (8 * (pos r / 8) + (pos r % 8 + 1) % 8))
    (hhash : ∀ r ∈ R, wd (stepPushRow val r) = H (pos r / 8) (pos r % 8) (wd (stepPullRow val r)))
    (hd : ∀ i < 42, d i < 8) (hlpush : ∀ i < 42, (linkPushRow val (Lrow i)).1 = keyK b g (8 * i + d i))
    (hlpull : ∀ i < 42, (linkPullRow val (Lrow i)).1 = keyK b g (8 * i + 7))
    (hlen : R.length + ∑ i ∈ Finset.range 42, d i = 294) (hbal : LocalBal val R ((List.range 42).map Lrow)) :
    ∀ i < 42, wd (linkPullRow val (Lrow i)) = walk H i (d i) (wd (linkPushRow val (Lrow i))) 7 := by
  have hdec : ∀ (t : Tuple) (q : ℕ), q < 2 ^ 9 → t.1 = keyK b g q → decT t = ((q / 8, q % 8), wd t) := by
    intro t q hq ht
    simp only [decT, ht, posOf_keyK b g q hb hq hg]
  set steps := R.map fun r => ((pos r / 8, pos r % 8), wd (stepPullRow val r), wd (stepPushRow val r)) with hsteps
  have hP : (R.map (stepPushRow val)).map decT = steps.map pushOf := by
    rw [hsteps, List.map_map, List.map_map]
    refine List.map_congr_left fun r hr => ?_
    have hp := hpos r hr
    have hq : 8 * (pos r / 8) + (pos r % 8 + 1) % 8 < 2 ^ 9 := by omega
    simp only [Function.comp, hdec _ _ hq (hpush r hr), pushOf, Prod.mk.injEq, and_true]
    omega
  have hQ : (R.map (stepPullRow val)).map decT = steps.map pullOf := by
    rw [hsteps, List.map_map, List.map_map]
    exact List.map_congr_left fun r hr => by simp only [Function.comp, hdec _ _ (hpos r hr) (hpull r hr), pullOf]
  have hLP : ((List.range 42).map Lrow |>.map (linkPushRow val)).map decT =
      (List.range 42).map fun i => ((i, d i), wd (linkPushRow val (Lrow i))) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    have hdi := hd i hi'
    simp only [Function.comp, hdec _ _ (by omega) (hlpush i hi'), Prod.mk.injEq, and_true]
    omega
  have hLQ : ((List.range 42).map Lrow |>.map (linkPullRow val)).map decT =
      (List.range 42).map fun i => ((i, 7), wd (linkPullRow val (Lrow i))) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    simp only [Function.comp, hdec _ _ (by omega) (hlpull i hi'), Prod.mk.injEq, and_true]
    omega
  have hb := congrArg (Multiset.map decT) hbal
  rw [Multiset.map_coe, Multiset.map_coe, List.map_append, List.map_append, hP, hQ, hLP, hLQ] at hb
  refine paths_sound H steps d (fun i => wd (linkPushRow val (Lrow i))) (fun i => wd (linkPullRow val (Lrow i)))
    (fun x hx => ?_) hd (by rw [hsteps, List.length_map]; exact hlen) hb
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have hp := hpos r hr
  exact ⟨show pos r / 8 < 64 by omega, Nat.mod_lt _ (by norm_num), hhash r hr⟩

theorem map_range_getD {α β : Type} (l : List α) (x : α) (n : ℕ) (hl : l.length = n) (g : α → β) :
    (List.range n).map (fun m => g (l.getD m x)) = l.map g := by
  subst hl
  refine List.ext_getElem (by simp) fun m h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show m < l.length by simpa using h1), Option.getD_some]

/-- A tag's tuples balance when its `n` steps are the cells its chains need, in order, and its links push the
chains' elements and pull their walks' ends. -/
theorem local_complete (H : ℕ → ℕ → Dig → Dig) (b g : ℕ) (val : Val) (d : ℕ → ℕ) (hd : ∀ i < 42, d i < 8)
    (tip : ℕ → Dig) (Srow Lrow : ℕ → List ℕ) (n : ℕ) (hlen : (cells d).length = n)
    (hspull : ∀ m < n, stepPullRow val (Srow m) = encT b g (pullOf (stepAt H d tip ((cells d).getD m (0, 0)))))
    (hspush : ∀ m < n, stepPushRow val (Srow m) = encT b g (pushOf (stepAt H d tip ((cells d).getD m (0, 0)))))
    (hlpush : ∀ i < 42, linkPushRow val (Lrow i) = encT b g ((i, d i), tip i))
    (hlpull : ∀ i < 42, linkPullRow val (Lrow i) = encT b g ((i, 7), walk H i (d i) (tip i) 7)) :
    LocalBal val ((List.range n).map Srow) ((List.range 42).map Lrow) := by
  have hS : ∀ (G : List ℕ → Tuple) (F : (ℕ × ℕ) × Dig × Dig → (ℕ × ℕ) × Dig),
      (∀ m < n, G (Srow m) = encT b g (F (stepAt H d tip ((cells d).getD m (0, 0))))) →
      ((List.range n).map Srow).map G = (cells d).map (encT b g ∘ F ∘ stepAt H d tip) := by
    intro G F h
    rw [List.map_map, ← map_range_getD (cells d) (0, 0) n hlen]
    exact List.map_congr_left fun m hm => h m (List.mem_range.mp hm)
  have hL : ∀ (G : List ℕ → Tuple) (F : ℕ → (ℕ × ℕ) × Dig), (∀ i < 42, G (Lrow i) = encT b g (F i)) →
      ((List.range 42).map Lrow).map G = ((List.range 42).map F).map (encT b g) := by
    intro G F h
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)
  have hbal := congrArg (Multiset.map (encT b g)) (paths_complete H d tip hd)
  rw [Multiset.map_coe, Multiset.map_coe, List.map_append, List.map_append] at hbal
  unfold LocalBal
  rw [hS _ pushOf hspush, hS _ pullOf hspull, hL _ (fun i => ((i, d i), tip i)) hlpush,
    hL _ (fun i => ((i, 7), walk H i (d i) (tip i) 7)) hlpull]
  simp only [List.map_map] at hbal ⊢
  exact hbal

/-! The whole circuit's rows. -/

/-- Rows named in groups of `a`, all distinct and all in a table of `a · n` rows, are the table's rows. -/
theorem rows_perm (arr : Array (List ℕ)) (n a : ℕ) (Rs : ℕ → List (List ℕ)) (hsize : arr.size = a * n)
    (hlen : ∀ j < n, (Rs j).length = a) (hmem : ∀ j < n, ∀ r ∈ Rs j, r ∈ arr)
    (hnd : ((List.range n).flatMap Rs).Nodup) : ((List.range n).flatMap Rs).Perm arr.toList := by
  refine (hnd.subperm fun r hr => ?_).perm_of_length_le ?_
  · obtain ⟨j, hj, hr⟩ := List.mem_flatMap.mp hr
    exact Array.mem_toList_iff.mpr (hmem j (List.mem_range.mp hj) r hr)
  · rw [Array.length_toList, hsize, List.length_flatMap,
      List.map_congr_left fun j hj => hlen j (List.mem_range.mp hj)]
    simp [Nat.mul_comm]

/-- A circuit's pushes and pulls, its rows grouped by signature. -/
theorem pushes_pulls (s : State) (val : Val) (n : ℕ) (Rs Ls : ℕ → List (List ℕ))
    (hR : ((List.range n).flatMap Rs).Perm s.step.toList) (hL : ((List.range n).flatMap Ls).Perm s.link.toList) :
    pushes s val = Multiset.ofList ((List.range n).flatMap fun j =>
        (Rs j).map (stepPushRow val) ++ (Ls j).map (linkPushRow val)) ∧
      pulls s val = Multiset.ofList ((List.range n).flatMap fun j =>
        (Rs j).map (stepPullRow val) ++ (Ls j).map (linkPullRow val)) := by
  constructor
  · rw [pushes, ← coe_flatMap_flatMap, ← List.map_flatMap, ← List.map_flatMap]
    exact Multiset.coe_eq_coe.mpr ((hR.map _).append (hL.map _)).symm
  · rw [pulls, ← coe_flatMap_flatMap, ← List.map_flatMap, ← List.map_flatMap]
    exact Multiset.coe_eq_coe.mpr ((hR.map _).append (hL.map _)).symm

theorem flatMap_single {β : Type} (n j : ℕ) (hj : j < n) (f : ℕ → List β) (h : ∀ j' < n, j' ≠ j → f j' = []) :
    (List.range n).flatMap f = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hjn : j = n
    · subst hjn
      rw [List.flatMap_eq_nil_iff.mpr fun j' hj' => h j' (by simp at hj'; omega) (by simp at hj'; omega),
        List.nil_append]
    · rw [ih (by omega) fun j' hj' hne => h j' (by omega) hne, h n (by omega) (Ne.symm hjn), List.append_nil]

/-- A balanced circuit balances each signature's tuples, when their keys name their signature. -/
theorem local_of_balanced (s : State) (val : Val) (n : ℕ) (Rs Ls : ℕ → List (List ℕ))
    (hR : ((List.range n).flatMap Rs).Perm s.step.toList) (hL : ((List.range n).flatMap Ls).Perm s.link.toList)
    (hb : Balanced s val)
    (htag : ∀ j < n, ∀ t ∈ ((Rs j).map (stepPushRow val) ++ (Ls j).map (linkPushRow val)) ++
      ((Rs j).map (stepPullRow val) ++ (Ls j).map (linkPullRow val)), tagOf t.1 = j) :
    ∀ j < n, LocalBal val (Rs j) (Ls j) := by
  intro j hj
  obtain ⟨hp, hq⟩ := pushes_pulls s val n Rs Ls hR hL
  have h := congrArg (Multiset.filter fun t : Tuple => tagOf t.1 = j) hb
  rw [hp, hq, Multiset.filter_coe, Multiset.filter_coe, List.filter_flatMap, List.filter_flatMap] at h
  have hsel : ∀ (B : ℕ → List Tuple), (∀ j' < n, ∀ t ∈ B j', tagOf t.1 = j') →
      (List.range n).flatMap (fun j' => (B j').filter fun t => decide (tagOf t.1 = j)) = B j := by
    intro B hB
    rw [flatMap_single n j hj _ fun j' hj' hne => List.filter_eq_nil_iff.mpr fun t ht => by
      simp [hB j' hj' t ht, hne]]
    exact List.filter_eq_self.mpr fun t ht => by simp [hB j hj t ht]
  rw [hsel _ fun j' hj' t ht => htag j' hj' t (List.mem_append_left _ ht),
    hsel _ fun j' hj' t ht => htag j' hj' t (List.mem_append_right _ ht)] at h
  exact h

/-- Each signature's tuples balancing balances the circuit. -/
theorem balanced_of_local (s : State) (val : Val) (n : ℕ) (Rs Ls : ℕ → List (List ℕ))
    (hR : ((List.range n).flatMap Rs).Perm s.step.toList) (hL : ((List.range n).flatMap Ls).Perm s.link.toList)
    (hloc : ∀ j < n, LocalBal val (Rs j) (Ls j)) : Balanced s val := by
  obtain ⟨hp, hq⟩ := pushes_pulls s val n Rs Ls hR hL
  rw [Rec.Model.Balanced, hp, hq, ← Multiset.coe_bind, ← Multiset.coe_bind]
  exact Multiset.bind_congr fun j hj => hloc j (List.mem_range.mp (Multiset.mem_coe.mp hj))

/-- Rows grouped by a label, distinct within each group, are distinct. -/
theorem nodup_flatMap_label {β : Type} (n : ℕ) (Rs : ℕ → List β) (lab : β → ℕ) (hnd : ∀ j < n, (Rs j).Nodup)
    (hlab : ∀ j < n, ∀ r ∈ Rs j, lab r = j) : ((List.range n).flatMap Rs).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun j hj => hnd j (List.mem_range.mp hj),
    List.nodup_range.pairwise_of_forall_ne fun a ha b hb hab => ?_⟩
  show List.Disjoint (Rs a) (Rs b)
  intro r hra hrb
  exact hab ((hlab a (List.mem_range.mp ha) r hra).symm.trans (hlab b (List.mem_range.mp hb) r hrb))

end LeanVMCircuits.Xmss
