module

public import LeanVMCircuits.Rec.Contracts
public import LeanVMCircuits.Xmss.Words
public import LeanVMCircuits.Xmss.FieldFacts

@[expose] public section

/-!
# What the leanXMSS circuit's gadgets make their outputs

Contracts in the style of `LeanVMCircuits.Rec.Contracts` for the gadgets of `Xmss.Circuit`: from a state keeping the
builder's invariant, each keeps it, only adds to the circuit, keeps the statement count (`statementWords` adds one),
and in every assignment satisfying a circuit containing its rows its outputs are what the gadget computes over words.

Programs are run forward: `Post s₀ Q r` says the run `r` from a state after `s₀` ends where `Q` relates `s₀` to it,
and `Good.step` and `post_bind` push a contract through one bind. `forIn_post` is the loop rule.
-/

namespace LeanVMCircuits.Xmss

open LeanVMCircuits.Rec (K E toE emb ofWord toWord words4 digest hashWords num root toE_injective)
open LeanVMCircuits.Rec.Model
open Words (W Dig)

/-! Running programs forward. -/

/-- A run's end, judged from `s₀`: it keeps the invariant, extends `s₀`, and `Q` relates `s₀`, the output and it. -/
def Post {α : Type} (s₀ : State) (Q : State → α → State → Prop) (r : α × State) : Prop :=
  Rec.Model.Inv r.2 ∧ Ext s₀ r.2 ∧ Q s₀ r.1 r.2

theorem good_of_post {α : Type} {P : State → Prop} {m : M α} {Q : State → α → State → Prop}
    (h : ∀ s, Rec.Model.Inv s → P s → Post s Q (m.run s)) : Good P m Q := h

theorem run_bind_eq {α β : Type} (m : M α) (f : α → M β) (s : State) :
    (m >>= f).run s = (f (m.run s).1).run (m.run s).2 := rfl

theorem post_bind {α β : Type} {m : M α} {f : α → M β} {s₀ s : State} {Q : State → α → State → Prop}
    {R : State → β → State → Prop} (hm : Post s Q (m.run s))
    (k : ∀ a s', Rec.Model.Inv s' → Ext s s' → Q s a s' → Post s₀ R ((f a).run s')) : Post s₀ R ((m >>= f).run s) :=
  k _ _ hm.1 hm.2.1 hm.2.2

theorem _root_.LeanVMCircuits.Rec.Model.Good.step {α β : Type} {P : State → Prop} {m : M α} {f : α → M β} {Q : State → α → State → Prop}
    {s₀ : State} {R : State → β → State → Prop} (h : Good P m Q) {s : State} (hs : Rec.Model.Inv s) (hP : P s)
    (k : ∀ a s', Rec.Model.Inv s' → Ext s s' → Q s a s' → Post s₀ R ((f a).run s')) : Post s₀ R ((m >>= f).run s) :=
  post_bind (h s hs hP) k

theorem _root_.LeanVMCircuits.Rec.Model.Good.last {α : Type} {P : State → Prop} {m : M α} {Q : State → α → State → Prop}
    {s₀ : State} {R : State → α → State → Prop} (h : Good P m Q) {s : State} (hs : Rec.Model.Inv s) (hP : P s)
    (he : Ext s₀ s) (k : ∀ a s', Ext s s' → Q s a s' → R s₀ a s') : Post s₀ R (m.run s) := by
  obtain ⟨hi, he', hq⟩ := h s hs hP
  exact ⟨hi, he.trans he', k _ _ he' hq⟩

theorem post_pure {α : Type} {s₀ s : State} {a : α} {R : State → α → State → Prop} (hs : Rec.Model.Inv s) (he : Ext s₀ s)
    (h : R s₀ a s) : Post s₀ R ((pure a : M α).run s) := ⟨hs, he, h⟩

/-- Extension along the chain of states a run passed through. -/
syntax "ext_chain" : tactic
macro_rules
  | `(tactic| ext_chain) =>
    `(tactic| first | exact Ext.refl _ | assumption | exact Ext.trans ‹_› (by ext_chain))

theorem lt_mono {a : ℕ} {s s' : State} (h : a < s.next) (he : Ext s s') : a < s'.next :=
  lt_of_lt_of_le h he.next

theorem Wires.nil' {s : State} : Wires [] s := fun _ h => absurd h (by simp)

theorem Wires.cons' {a : ℕ} {l : List ℕ} {s : State} (ha : a < s.next) (hl : Wires l s) : Wires (a :: l) s := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact ha
  · exact hl w hw

/-! The loop rule. -/

theorem forIn_post {β γ : Type} (l : List γ) (f : γ → β → M (ForInStep β)) (I : ℕ → β → State → Prop)
    {s₀ : State} {b₀ : β} (hs : Rec.Model.Inv s₀) (h0 : I 0 b₀ s₀)
    (hstep : ∀ k (hk : k < l.length) b s, Rec.Model.Inv s → Ext s₀ s → I k b s →
      Post s (fun _ r s' => ∃ b', r = .yield b' ∧ I (k + 1) b' s') ((f l[k] b).run s)) :
    Post s₀ (fun _ b s' => I l.length b s') ((forIn l b₀ f).run s₀) := by
  suffices H : ∀ n off b s, n + off = l.length → Rec.Model.Inv s → Ext s₀ s → I off b s →
      Post s₀ (fun _ b s' => I l.length b s') ((forIn (l.drop off) b f).run s) by
    simpa using H l.length 0 b₀ s₀ (by omega) hs (Ext.refl _) h0
  intro n
  induction n with
  | zero =>
    intro off b s hn hs he hI
    obtain rfl : off = l.length := by omega
    rw [List.drop_length, List.forIn_nil]
    exact ⟨hs, he, hI⟩
  | succ n ih =>
    intro off b s hn hs he hI
    rw [List.drop_eq_getElem_cons (by omega), List.forIn_cons]
    obtain ⟨hi1, he1, b', hb', hI'⟩ := hstep off (by omega) b s hs he hI
    rw [run_bind_eq, hb']
    exact ih (off + 1) b' _ (by omega) hi1 (he.trans he1) hI'

theorem forIn_range_post {β : Type} (n : ℕ) (f : ℕ → β → M (ForInStep β)) (I : ℕ → β → State → Prop)
    {s₀ : State} {b₀ : β} (hs : Rec.Model.Inv s₀) (h0 : I 0 b₀ s₀)
    (hstep : ∀ k < n, ∀ b s, Rec.Model.Inv s → Ext s₀ s → I k b s →
      Post s (fun _ r s' => ∃ b', r = .yield b' ∧ I (k + 1) b' s') ((f k b).run s)) :
    Post s₀ (fun _ b s' => I n b s') ((forIn (List.range n) b₀ f).run s₀) := by
  have H := forIn_post (List.range n) f I hs h0 fun k hk b s h1 h2 h3 => by
    have := hstep k (by simpa using hk) b s h1 h2 h3
    rwa [List.getElem_range]
  simpa only [List.length_range] using H

theorem forIn_range'_post {β : Type} (n : ℕ) (f : ℕ → β → M (ForInStep β)) (I : ℕ → β → State → Prop)
    {s₀ : State} {b₀ : β} (hs : Rec.Model.Inv s₀) (h0 : I 0 b₀ s₀)
    (hstep : ∀ k < n, ∀ b s, Rec.Model.Inv s → Ext s₀ s → I k b s →
      Post s (fun _ r s' => ∃ b', r = .yield b' ∧ I (k + 1) b' s') ((f (k + 1) b).run s)) :
    Post s₀ (fun _ b s' => I n b s') ((forIn (List.range' 1 n) b₀ f).run s₀) := by
  have H := forIn_post (List.range' 1 n) f I hs h0 fun k hk b s h1 h2 h3 => by
    have := hstep k (by simpa using hk) b s h1 h2 h3
    rwa [List.getElem_range', Nat.one_mul, Nat.add_comm 1 k]
  simpa only [List.length_range'] using H

/-! The statement count. -/

/-- `m` leaves the statement count alone. -/
def Pres {α : Type} (m : M α) : Prop := ∀ s, (m.run s).2.statement = s.statement

theorem Pres.bind {α β : Type} {m : M α} {f : α → M β} (hm : Pres m) (hf : ∀ a, Pres (f a)) :
    Pres (m >>= f) := by
  intro s
  rw [run_bind_eq, hf, hm]

theorem Pres.pure' {α : Type} (a : α) : Pres (pure a : M α) := fun _ => rfl

theorem Pres.get' : Pres (get : M State) := fun _ => rfl

theorem Pres.forIn {β γ : Type} (l : List γ) (b : β) (f : γ → β → M (ForInStep β)) (hf : ∀ x b, Pres (f x b)) :
    Pres (forIn l b f) := by
  induction l generalizing b with
  | nil => exact Pres.pure' b
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine Pres.bind (hf x b) fun r => ?_
    cases r with
    | done b => exact Pres.pure' b
    | yield b => exact ih b

theorem Pres.mapM {β γ : Type} (l : List γ) (f : γ → M β) (hf : ∀ x, Pres (f x)) : Pres (l.mapM f) := by
  induction l with
  | nil => exact Pres.pure' _
  | cons x xs ih => rw [List.mapM_cons]; exact Pres.bind (hf x) fun _ => Pres.bind ih fun _ => Pres.pure' _

theorem _root_.LeanVMCircuits.Rec.Model.Good.pres {α : Type} {P : State → Prop} {m : M α} {Q : State → α → State → Prop} (h : Good P m Q)
    (hp : Pres m) : Good P m fun s a s' => s'.statement = s.statement ∧ Q s a s' := fun s hs hP =>
  let ⟨hi, he, hq⟩ := h s hs hP
  ⟨hi, he, hp s, hq⟩

syntax "pres_atom" : tactic
macro_rules | `(tactic| pres_atom) => `(tactic| exact Pres.pure' _)
macro_rules | `(tactic| pres_atom) => `(tactic| exact Pres.get')

syntax "pres_step" : tactic
macro_rules | `(tactic| pres_step) => `(tactic| (intro _s; rfl))
macro_rules | `(tactic| pres_step) => `(tactic| dsimp only)
macro_rules | `(tactic| pres_step) => `(tactic| split)
macro_rules | `(tactic| pres_step) => `(tactic| refine Pres.mapM _ _ fun _ => ?_)
macro_rules | `(tactic| pres_step) => `(tactic| refine Pres.bind ?_ fun _ => ?_)
macro_rules | `(tactic| pres_step) => `(tactic| pres_atom)

macro "pres" : tactic => `(tactic| repeat' pres_step)

theorem pres_wire : Pres wire := fun _ => rfl

theorem pres_constant (kd : Kind) (v : Limbs) : Pres (constant kd v) := by
  unfold constant; pres

macro_rules | `(tactic| pres_atom) => `(tactic| exact pres_constant _ _)

theorem pres_kConst (v : ℕ) : Pres (kConst v) := pres_constant _ _
theorem pres_eConst (c0 c1 c2 : ℕ) : Pres (eConst c0 c1 c2) := pres_constant _ _

macro_rules | `(tactic| pres_atom) => `(tactic| exact pres_kConst _)
macro_rules | `(tactic| pres_atom) => `(tactic| exact pres_eConst _ _ _)

theorem pres_zero : Pres zero := by unfold zero; pres
theorem pres_one : Pres one := by unfold one; pres
theorem pres_kZero : Pres kZero := by unfold kZero; pres

macro_rules | `(tactic| pres_atom) => `(tactic| exact pres_zero)
macro_rules | `(tactic| pres_atom) => `(tactic| exact pres_one)
macro_rules | `(tactic| pres_atom) => `(tactic| exact pres_kZero)

theorem pres_emul (a b d : ℕ) : Pres (emul a b d) := by unfold emul; pres

macro_rules | `(tactic| pres_atom) => `(tactic| exact pres_emul _ _ _)

theorem pres_add (a d : ℕ) : Pres (add a d) := by unfold add; pres

macro_rules | `(tactic| pres_atom) => `(tactic| exact pres_add _ _)

theorem pres_mulAdd (a b d : ℕ) : Pres (mulAdd a b d) := by unfold mulAdd; pres
theorem pres_mulKAdd (a k d : ℕ) : Pres (mulKAdd a k d) := by unfold mulKAdd; pres

macro_rules | `(tactic| pres_atom) => `(tactic| exact pres_mulAdd _ _ _)
macro_rules | `(tactic| pres_atom) => `(tactic| exact pres_mulKAdd _ _ _)

theorem pres_mulConstAdd (a c0 c1 c2 d : ℕ) : Pres (mulConstAdd a c0 c1 c2 d) := by unfold mulConstAdd; pres
theorem pres_eqConstE (a c0 c1 c2 : ℕ) : Pres (eqConstE a c0 c1 c2) := by unfold eqConstE; pres
theorem pres_eqConstK (a v : ℕ) : Pres (eqConstK a v) := by unfold eqConstK; pres
theorem pres_row (t : Table) (r : List ℕ) : Pres (row t r) := by intro s; cases t <;> rfl

theorem pres_split (w : ℕ) : Pres (split w) := by
  unfold split splitRow
  exact Pres.bind (Pres.mapM _ _ fun _ => pres_wire) fun _ => Pres.bind (pres_row _ _) fun _ => Pres.pure' _
theorem pres_pack (bits : List ℕ) : Pres (pack bits) := by unfold pack splitRow; pres
theorem pres_castRow (given : List (ℕ × ℕ)) : Pres (castRow given) := by unfold castRow; pres

macro_rules | `(tactic| pres_atom) => `(tactic| exact pres_castRow _)

theorem pres_eToK (e : ℕ) : Pres (eToK e) := by unfold eToK; exact Pres.bind (pres_castRow _) fun _ => Pres.pure' _
theorem pres_kToE (k0 k1 k2 : ℕ) : Pres (kToE k0 k1 k2) := by
  unfold kToE; exact Pres.bind (pres_castRow _) fun _ => Pres.pure' _
theorem pres_dToK (d : ℕ) : Pres (dToK d) := by unfold dToK; exact Pres.bind (pres_castRow _) fun _ => Pres.pure' _
theorem pres_dToEAndK (d : ℕ) : Pres (dToEAndK d) := by
  unfold dToEAndK; exact Pres.bind (pres_castRow _) fun _ => Pres.pure' _

theorem pres_leafBlock (h : ℕ) (m : List ℕ) (t : ℕ) (last : Bool) : Pres (leafBlock h m t last) := by
  unfold leafBlock hashRow; pres

theorem pres_chainBlocks (words : List ℕ) (z n bytes : ℕ) : ∀ js h, Pres (chainBlocks words z n bytes js h)
  | [], h => Pres.pure' h
  | j :: js, h => by
    rw [chainBlocks]
    exact Pres.bind (pres_leafBlock _ _ _ _) fun h' => pres_chainBlocks words z n bytes js h'

theorem pres_chain (words : List ℕ) : Pres (chain words) := by
  unfold chain
  exact Pres.bind pres_kZero fun _ => Pres.bind (pres_constant _ _) fun _ => pres_chainBlocks _ _ _ _ _ _

/-! Words and limbs. -/

theorem toWord_lt (x : K) : toWord x < 2 ^ 64 := Rec.num_lt _ _

theorem ofWord_toWord (x : K) : ofWord (toWord x) = x :=
  Rec.toWord_injective (Rec.toWord_ofWord _ (toWord_lt x))

theorem words4_toNat (v : Fin 4 → K) (k : Fin 4) : (words4 v k).toNat = toWord (v k) := by
  simp only [words4, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (toWord_lt _)

theorem ofWord_words4 (v : Fin 4 → K) (k : Fin 4) : ofWord (words4 v k).toNat = v k := by
  rw [words4_toNat, ofWord_toWord]

theorem w64_toNat (val : Val) (w : ℕ) : (w64 val w).toNat = toWord (val w 0) := words4_toNat (val w) 0

theorem w64_of {val : Val} {a b : ℕ} {k : Fin 4} (h : val a 0 = val b k) : w64 val a = words4 (val b) k := by
  simp only [w64, words4, h]

theorem w64_const {val : Val} {w v : ℕ} (h : val w = limbsOf [v, 0, 0, 0]) : w64 val w = BitVec.ofNat 64 v := by
  have h0 : val w 0 = ofWord v := by rw [h]; rfl
  apply BitVec.eq_of_toNat_eq
  rw [w64_toNat, h0, BitVec.toNat_ofNat]
  have : ofWord v = ofWord (v % 2 ^ 64) := by simp [Rec.ofWord]
  rw [this, Rec.toWord_ofWord _ (Nat.mod_lt _ (by norm_num))]

theorem limb_zero {val : Val} {w : ℕ} (h : val w = limbsOf [0, 0, 0, 0]) (i : Fin 4) : val w i = 0 := by
  rw [h]; fin_cases i <;> exact Rec.ofWord_zero

/-- The two words of a digest wire, or of an `E` wire's first two limbs. -/
noncomputable def dig (val : Val) (w : ℕ) : Dig := (words4 (val w) 0, words4 (val w) 1)

theorem dig_congr {val : Val} {a b : ℕ} (h0 : val a 0 = val b 0) (h1 : val a 1 = val b 1) :
    dig val a = dig val b := by
  simp only [dig, words4, h0, h1]

theorem dig_th {val : Val} {r ty pos e : ℕ} {P : Dig} {pl : List W}
    (h : words4 (val r) = digest (hashWords ([Words.tweak0 ty pos, Words.tweak1 e, P.1, P.2] ++ pl))) :
    dig val r = Words.th ty pos e P pl := by
  simp only [dig, Words.th, h]

theorem fun4 {f : Fin 4 → K} {a b c d : K} (h0 : f 0 = a) (h1 : f 1 = b) (h2 : f 2 = c) (h3 : f 3 = d) :
    f = ![a, b, c, d] := by
  funext i; fin_cases i <;> simp [h0, h1, h2, h3]

/-- Two wires naming one `E` element carry its three limbs. -/
theorem limbs_of_ev {val : Val} {a b : ℕ} (h : ev val a = ev val b) :
    val a 0 = val b 0 ∧ val a 1 = val b 1 ∧ val a 2 = val b 2 :=
  toE_injective _ _ _ _ _ _ h

theorem dig_of_ev {val : Val} {a b : ℕ} (h : ev val a = ev val b) : dig val a = dig val b :=
  dig_congr (limbs_of_ev h).1 (limbs_of_ev h).2.1

theorem emb_one' : emb 1 = 1 := map_one _

theorem add_self_E (a : E) : a + a = 0 := by rw [← two_mul, Rec.two_E, zero_mul]

theorem emb_injective {a b : K} (h : emb a = emb b) : a = b :=
  (toE_injective a 0 0 b 0 0 (by rw [toE_emb, toE_emb]; exact h)).1

theorem ite_one (p : Prop) [Decidable p] : ((if p then 1 else 0 : ZMod 2) = 1) ↔ p := by
  split_ifs with h <;> simp [h]

/-- A word given by its bits. -/
theorem num_eq (c : ℕ → ZMod 2) (n : ℕ) (hn : n < 2 ^ 64) (h : ∀ i < 64, (c i = 1 ↔ n.testBit i = true)) :
    num c 64 = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · rw [Rec.testBit_num _ _ _ hi]
    cases hb : n.testBit i
    · exact decide_eq_false fun hc => by simp [(h i hi).mp hc] at hb
    · exact decide_eq_true ((h i hi).mpr hb)
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (Rec.num_lt c 64) (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- The bits of a split word. -/
theorem testBit_split {x : K} {bits : List ℕ} {val : Val}
    (h : toWord x = num (fun i => if val (bits.getD i 0) 0 = 1 then 1 else 0) 64) (j : ℕ) (hj : j < 64) :
    (toWord x).testBit j = true ↔ val (bits.getD j 0) 0 = 1 := by
  rw [h, Rec.testBit_num _ _ _ hj, decide_eq_true_iff, ite_one]

theorem wires_getD' {l : List ℕ} {s : State} (h : Wires l s) {j : ℕ} (hj : j < l.length) : l.getD j 0 < s.next := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact h _ (List.getElem_mem hj)

theorem Wires.snoc {l : List ℕ} {q : ℕ} {s : State} (h : Wires l s) (hq : q < s.next) : Wires (l ++ [q]) s := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact h w hw
  · rw [List.mem_singleton.mp hw]; exact hq

theorem getD_snoc (l : List ℕ) (q v : ℕ) :
    (l ++ [q]).getD v 0 = if v < l.length then l.getD v 0 else if v = l.length then q else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append]
  by_cases h1 : v < l.length
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : v = l.length
    · subst h2; simp
    · rw [if_neg h2, List.getElem?_eq_none (by simp; omega)]; rfl

/-! The CAST views' top limb. -/

theorem cast_e3 {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) {ws : List ℕ} (hr : ws ∈ s.cast) :
    val (ws.getD 1 0) 3 = 0 := by
  obtain ⟨col, -, hl⟩ := h.cast _ hr
  rw [← hl 1 (by show 1 < 8; omega) 3]
  exact (Rec.cast_views col).2.2.1

theorem list8 {ws : List ℕ} (h : ws.length = 8) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7, ws = [w0, w1, w2, w3, w4, w5, w6, w7] := by
  match ws, h with
  | [w0, w1, w2, w3, w4, w5, w6, w7], _ => exact ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩

theorem eToK_view (e : ℕ) : Good (Wires [e]) (eToK e) fun _ ks s' => ∃ a b c, ks = [a, b, c] ∧ a < s'.next ∧
    b < s'.next ∧ c < s'.next ∧
      ∀ st val, Sat st s' val → val a 0 = val e 0 ∧ val b 0 = val e 1 ∧ val c 0 = val e 2 ∧ val e 3 = 0 := by
  unfold eToK
  refine (view_good [(1, e)] (fun w => (w.drop 4).take 3) (fun s' ks _ => ∃ a b c, ks = [a, b, c] ∧ a < s'.next ∧
    b < s'.next ∧ c < s'.next ∧ ∀ st val, Sat st s' val → val a 0 = val e 0 ∧ val b 0 = val e 1 ∧
      val c 0 = val e 2 ∧ val e 3 = 0) ?_).pre fun _ h => by simpa using h
  intro ws s' hlen hc hw hg
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩ := list8 hlen
  have h1 : w1 = e := hg 1 e (by omega) (by simp)
  subst h1
  refine ⟨w4, w5, w6, rfl, hw w4 (by simp), hw w5 (by simp), hw w6 (by simp), fun st val hsat => ?_⟩
  obtain ⟨col, -, hE, -, -, hW⟩ := cast_sem hsat hc
  have e3 : val w1 3 = 0 := cast_e3 hsat hc
  have a0 : val w4 0 = col 0 := hW 0
  have a1 : val w5 0 = col 1 := hW 1
  have a2 : val w6 0 = col 2 := hW 2
  have b0 : val w1 0 = col 0 := hE 0 (by decide)
  have b1 : val w1 1 = col 1 := hE 1 (by decide)
  have b2 : val w1 2 = col 2 := hE 2 (by decide)
  exact ⟨a0.trans b0.symm, a1.trans b1.symm, a2.trans b2.symm, e3⟩

/-- `eToK`: the element's three limbs as `K` wires, its top limb zero. -/
theorem eToK_good' (e : ℕ) : Good (Wires [e]) (eToK e) fun s ks s' => s'.statement = s.statement ∧
    ∃ a b c, ks = [a, b, c] ∧ a < s'.next ∧ b < s'.next ∧ c < s'.next ∧
      ∀ st val, Sat st s' val → val a 0 = val e 0 ∧ val b 0 = val e 1 ∧ val c 0 = val e 2 ∧ val e 3 = 0 :=
  (eToK_view e).pres (pres_eToK e)

theorem kToE_view (k0 k1 k2 : ℕ) : Good (Wires [k0, k1, k2]) (kToE k0 k1 k2) fun _ r s' => r < s'.next ∧
    ∀ st val, Sat st s' val → val r 0 = val k0 0 ∧ val r 1 = val k1 0 ∧ val r 2 = val k2 0 ∧ val r 3 = 0 := by
  unfold kToE
  refine (view_good [(4, k0), (5, k1), (6, k2)] (fun w => w.getD 1 0) (fun s' r _ => r < s'.next ∧
    ∀ st val, Sat st s' val → val r 0 = val k0 0 ∧ val r 1 = val k1 0 ∧ val r 2 = val k2 0 ∧ val r 3 = 0) ?_).pre
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
  have f0 : val (ws.getD 1 0) 0 = col 0 := h1 0 (by decide)
  have f1 : val (ws.getD 1 0) 1 = col 1 := h1 1 (by decide)
  have f2 : val (ws.getD 1 0) 2 = col 2 := h1 2 (by decide)
  exact ⟨f0.trans e0.symm, f1.trans e1.symm, f2.trans e2.symm, cast_e3 hsat hc⟩

/-- `kToE`: the element of three `K` wires, its top limb zero. -/
theorem kToE_good' (k0 k1 k2 : ℕ) : Good (Wires [k0, k1, k2]) (kToE k0 k1 k2) fun s r s' =>
    s'.statement = s.statement ∧ r < s'.next ∧
      ∀ st val, Sat st s' val → val r 0 = val k0 0 ∧ val r 1 = val k1 0 ∧ val r 2 = val k2 0 ∧ val r 3 = 0 :=
  (kToE_view k0 k1 k2).pres (pres_kToE k0 k1 k2)

theorem fresh_good' : Good (fun _ => True) wire fun s w s' => s'.statement = s.statement ∧ w < s'.next :=
  (fresh_good.pres pres_wire).weaken (fun _ h => h) fun _ _ _ _ _ _ h => ⟨h.1, h.2.2⟩

theorem expose_good' (w : ℕ) : Good (Wires [w]) (expose w) fun s i s' => i = s.statement ∧
    s'.statement = s.statement + 1 ∧ ∀ st val, Sat st s' val → val w = st i := fun s hs hP =>
  let ⟨hi, he, h1, h2⟩ := expose_good w s hs hP
  ⟨hi, he, h1, rfl, h2⟩

/-- Holding a list's wires to zero. -/
theorem zeros_good (l : List ℕ) : Good (fun _ => True)
    (forIn l PUnit.unit fun k _ => do eqConstK k 0; pure (ForInStep.yield PUnit.unit))
    fun s _ s' => s'.statement = s.statement ∧ ∀ st val, Sat st s' val → ∀ k ∈ l, val k = limbsOf [0, 0, 0, 0] := by
  refine good_of_post fun s hs _ => ?_
  have H := forIn_post l (fun k (_ : PUnit) => (do eqConstK k 0; pure (ForInStep.yield PUnit.unit) :
      M (ForInStep PUnit)))
    (fun n _ s' => s'.statement = s.statement ∧ ∀ st val, Sat st s' val →
      ∀ j (hj : j < n) (hl : j < l.length), val l[j] = limbsOf [0, 0, 0, 0])
    (b₀ := PUnit.unit) hs ⟨rfl, fun _ _ _ j hj => absurd hj (Nat.not_lt_zero j)⟩ ?_
  · obtain ⟨hi, he, hst, hv⟩ := H
    refine ⟨hi, he, hst, fun st val hsat k hk => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hk
    exact hv st val hsat j hj hj
  · rintro k hk b s1 hi1 he1 ⟨hst1, hv1⟩
    refine ((eqConstK_good l[k] 0).pres (pres_eqConstK _ _)).step hi1 trivial ?_
    rintro u s2 hi2 he2 ⟨hst2, hz⟩
    refine post_pure hi2 he2 ⟨PUnit.unit, rfl, by omega, fun st val hsat j hj hl => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hv1 st val (hsat.mono he2) j hj hl
    · exact hz st val hsat

/-! The gadgets. -/

/-- `words`: an `E` wire's three limbs as `K` wires. -/
theorem words_good (e : ℕ) : Good (Wires [e]) (Circuit.words e) fun s r s' => s'.statement = s.statement ∧
    r.1 < s'.next ∧ r.2.1 < s'.next ∧ r.2.2 < s'.next ∧ ∀ st val, Sat st s' val →
      val r.1 0 = val e 0 ∧ val r.2.1 0 = val e 1 ∧ val r.2.2 0 = val e 2 ∧ val e 3 = 0 := by
  unfold Circuit.words
  refine good_of_post fun s hs hP => ?_
  refine (eToK_good' e).step hs hP ?_
  rintro ks s1 hi he ⟨hst, a, b, c, rfl, ha, hb, hc, hv⟩
  exact post_pure hi he ⟨hst, ha, hb, hc, hv⟩

/-- `statementWords 1`: an exposed statement word of two words and two zero limbs. -/
theorem statementWords_good1 : Good (fun _ => True) (Circuit.statementWords 1) fun s ks s' =>
    s'.statement = s.statement + 1 ∧ ∃ a b, ks = [a, b] ∧ a < s'.next ∧ b < s'.next ∧
      ∀ st val, Sat st s' val → st s.statement = ![val a 0, val b 0, 0, 0] := by
  unfold Circuit.statementWords
  refine good_of_post fun s hs _ => ?_
  refine fresh_good'.step hs trivial ?_
  rintro w s1 hi1 he1 ⟨hst1, hw1⟩
  refine (expose_good' w).step hi1 (Wires.cons' hw1 Wires.nil') ?_
  rintro i s2 hi2 he2 ⟨rfl, hst2, hx⟩
  refine (eToK_good' w).step hi2 (Wires.cons' (lt_mono hw1 he2) Wires.nil') ?_
  rintro ks s3 hi3 he3 ⟨hst3, a, b, c, rfl, ha, hb, hc, hv⟩
  refine (zeros_good _).step hi3 trivial ?_
  rintro u s4 hi4 he4 ⟨hst4, hz⟩
  refine post_pure hi4 (by ext_chain) ⟨by omega, a, b, rfl, lt_mono ha he4, lt_mono hb he4, fun st val hsat => ?_⟩
  obtain ⟨ha0, hb0, hc0, h3⟩ := hv st val (hsat.mono he4)
  have hc' : val c 0 = 0 := limb_zero (hz st val hsat c (by simp)) 0
  rw [← hst1, ← hx st val (hsat.mono (by ext_chain))]
  exact fun4 ha0.symm hb0.symm (by rw [← hc0]; exact hc') h3

/-- `statementWords 2`: an exposed statement word of one word and three zero limbs. -/
theorem statementWords_good2 : Good (fun _ => True) (Circuit.statementWords 2) fun s ks s' =>
    s'.statement = s.statement + 1 ∧ ∃ a, ks = [a] ∧ a < s'.next ∧
      ∀ st val, Sat st s' val → st s.statement = ![val a 0, 0, 0, 0] := by
  unfold Circuit.statementWords
  refine good_of_post fun s hs _ => ?_
  refine fresh_good'.step hs trivial ?_
  rintro w s1 hi1 he1 ⟨hst1, hw1⟩
  refine (expose_good' w).step hi1 (Wires.cons' hw1 Wires.nil') ?_
  rintro i s2 hi2 he2 ⟨rfl, hst2, hx⟩
  refine (eToK_good' w).step hi2 (Wires.cons' (lt_mono hw1 he2) Wires.nil') ?_
  rintro ks s3 hi3 he3 ⟨hst3, a, b, c, rfl, ha, hb, hc, hv⟩
  refine (zeros_good _).step hi3 trivial ?_
  rintro u s4 hi4 he4 ⟨hst4, hz⟩
  refine post_pure hi4 (by ext_chain) ⟨by omega, a, rfl, lt_mono ha he4, fun st val hsat => ?_⟩
  obtain ⟨ha0, hb0, hc0, h3⟩ := hv st val (hsat.mono he4)
  have hb' : val b 0 = 0 := limb_zero (hz st val hsat b (by simp)) 0
  have hc' : val c 0 = 0 := limb_zero (hz st val hsat c (by simp)) 0
  rw [← hst1, ← hx st val (hsat.mono (by ext_chain))]
  exact fun4 ha0.symm (by rw [← hb0]; exact hb') (by rw [← hc0]; exact hc') h3

/-- `tweakHash`: the digest of the tweak, the parameter and the payload. -/
theorem tweakHash_good (ty pos idx : ℕ) (pp payload : List ℕ) (hlen : 8 * (2 + pp.length + payload.length) < 2 ^ 64) :
    Good (fun _ => True) (Circuit.tweakHash ty pos idx pp payload) fun s r s' => s'.statement = s.statement ∧
      r < s'.next ∧ ∀ st val, Sat st s' val →
        words4 (val r) = digest (hashWords ([Words.tweak0 ty pos, w64 val idx] ++ (pp ++ payload).map (w64 val))) := by
  unfold Circuit.tweakHash
  refine good_of_post fun s hs _ => ?_
  refine ((kConst_good _).pres (pres_kConst _)).step hs trivial ?_
  rintro tw s1 hi1 he1 ⟨hst1, -, htw⟩
  refine ((chain_good _ ?_).pres (pres_chain _)).last hi1 trivial he1 ?_
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  rintro r s2 he2 ⟨hst2, hr, hv⟩
  refine ⟨by omega, hr, fun st val hsat => ?_⟩
  rw [hv st val hsat]
  simp only [List.map_append, List.map_cons, List.cons_append, List.nil_append,
    w64_const (htw st val (hsat.mono he2)), Words.tweak0]

/-- A word's bits `shift .. 31` in its bytes 4 to 7, zero below. -/
theorem index_getD (z : ℕ) (bits : List ℕ) (shift i : ℕ) (hsh : shift ≤ 32) :
    (List.replicate 32 z ++ (bits.take 32).drop shift).getD i 0 =
      if i < 32 then z else if i < 64 - shift then bits.getD (i - 32 + shift) 0 else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_replicate]
  by_cases h1 : i < 32
  · rw [if_pos h1, if_pos h1, List.getElem?_replicate, if_pos h1]; rfl
  · rw [if_neg h1, if_neg h1, List.getElem?_drop, List.getElem?_take]
    by_cases h2 : i < 64 - shift
    · rw [if_pos (by omega), if_pos h2, List.getD_eq_getElem?_getD, show shift + (i - 32) = i - 32 + shift by omega]
    · rw [if_neg (by omega), if_neg h2]; rfl

/-- `indexWord`: the tweak word of the epoch shifted right by `shift`. -/
theorem indexWord_good (bits : List ℕ) (shift : ℕ) (hsh : shift ≤ 32) (hlen : 32 ≤ bits.length) :
    Good (Wires bits) (Circuit.indexWord bits shift) fun s r s' => s'.statement = s.statement ∧ r < s'.next ∧
      ∀ st val, Sat st s' val → ∀ e : ℕ, e < 2 ^ 32 → (∀ i < 32, (val (bits.getD i 0) 0 = 1 ↔ e.testBit i = true)) →
        w64 val r = Words.tweak1 (e / 2 ^ shift) := by
  unfold Circuit.indexWord
  refine good_of_post fun s hs hb => ?_
  refine ((kConst_good 0).pres (pres_kConst 0)).step hs trivial ?_
  rintro z s1 hi1 he1 ⟨hst1, hz, hzv⟩
  refine ((pack_good _).pres (pres_pack _)).last hi1 ?_ he1 ?_
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · rw [List.eq_of_mem_replicate h]; exact hz
    · exact lt_mono (hb w (List.mem_of_mem_take (List.mem_of_mem_drop h))) he1
  rintro r s2 he2 ⟨hst2, hr, hv⟩
  refine ⟨by omega, hr, fun st val hsat e he hbits => ?_⟩
  obtain ⟨-, hnum⟩ := hv st val hsat
  have hz0 : val z 0 = 0 := limb_zero (hzv st val (hsat.mono he2)) 0
  have hL : (List.replicate 32 z ++ (bits.take 32).drop shift).length = 64 - shift := by
    simp only [List.length_append, List.length_replicate, List.length_drop, List.length_take]; omega
  rw [w64, hnum, Words.tweak1]
  apply congrArg (BitVec.ofNat 64)
  apply num_eq
  · have : e / 2 ^ shift % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
    generalize e / 2 ^ shift % 2 ^ 32 = x at this ⊢
    omega
  intro i hi
  rw [ite_one, index_getD z bits shift i hsh, hL]
  simp only [Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Bool.and_eq_true,
    decide_eq_true_eq]
  by_cases h1 : i < 32
  · rw [if_pos h1, hz0]
    constructor
    · intro h; exact absurd h.2 zero_ne_one
    · intro h; omega
  · by_cases h2 : i < 64 - shift
    · rw [if_neg h1, if_pos h2, hbits _ (by omega)]
      constructor
      · intro h; exact ⟨by omega, by omega, h.2⟩
      · intro h; exact ⟨h2, h.2.2⟩
    · rw [if_neg h1, if_neg h2]
      have hf : e.testBit (i - 32 + shift) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) (by omega)))
      constructor
      · intro h; exact absurd h.1 h2
      · intro h; rw [hf] at h; exact absurd h.2.2 (by simp)


/-! The digits' product. -/

/-- The value of three digit bits, low first. -/
noncomputable def dig3 (val : Val) (a0 a1 a2 : ℕ) : ℕ :=
  (if val a0 0 = 1 then 1 else 0) + (if val a1 0 = 1 then 2 else 0) + (if val a2 0 = 1 then 4 else 0)

/-- Digit `i` of a list of digit bits, three per digit. -/
noncomputable def dval (val : Val) (bits : List ℕ) (i : ℕ) : ℕ :=
  dig3 val (bits.getD (3 * i) 0) (bits.getD (3 * i + 1) 0) (bits.getD (3 * i + 2) 0)

/-- The sum of the first `n` digits. -/
noncomputable def dsum (val : Val) (bits : List ℕ) (n : ℕ) : ℕ := ((List.range n).map (dval val bits)).sum

/-- The value of digit `i`'s first `k` bits. -/
noncomputable def pval (val : Val) (bits : List ℕ) (i k : ℕ) : ℕ :=
  ((List.range k).map fun k' => if val (bits.getD (3 * i + k') 0) 0 = 1 then 2 ^ k' else 0).sum

theorem pval_succ (val : Val) (bits : List ℕ) (i k : ℕ) :
    pval val bits i (k + 1) = pval val bits i k + if val (bits.getD (3 * i + k) 0) 0 = 1 then 2 ^ k else 0 := by
  simp [pval, List.range_succ]

theorem pval_zero (val : Val) (bits : List ℕ) (i : ℕ) : pval val bits i 0 = 0 := rfl

theorem pval_three (val : Val) (bits : List ℕ) (i : ℕ) : pval val bits i 3 = dval val bits i := by
  rw [pval_succ, pval_succ, pval_succ, pval_zero]
  simp only [dval, dig3, Nat.add_zero, pow_zero, pow_one, Nat.zero_add]
  norm_num

theorem dval_lt (val : Val) (bits : List ℕ) (i : ℕ) : dval val bits i < 8 := by
  unfold dval dig3; split_ifs <;> omega

theorem dsum_succ (val : Val) (bits : List ℕ) (n : ℕ) : dsum val bits (n + 1) = dsum val bits n + dval val bits n := by
  simp [dsum, List.range_succ]

theorem dsum_le (val : Val) (bits : List ℕ) (n : ℕ) : dsum val bits n ≤ 7 * n := by
  induction n with
  | zero => simp [dsum]
  | succ n ih =>
    have := dval_lt val bits n
    rw [dsum_succ]
    omega

/-- One digit bit's factor: times `x^(2^k)` when the bit is one. -/
theorem digit_mul (q k : ℕ) (hk : k < 3) (x : K) (hx : x = 0 ∨ x = 1) :
    (emb (root ^ q) * toE (ofWord (2 ^ 2 ^ k + 1)) (ofWord 0) (ofWord 0) + 0) * emb x + emb (root ^ q) =
      emb (root ^ (q + if x = 1 then 2 ^ k else 0)) := by
  rw [Rec.ofWord_zero, toE_emb, ofWord_weight k hk, add_zero]
  rcases hx with rfl | rfl
  · simp [Rec.emb_zero]
  · rw [if_pos rfl, emb_one', mul_one, ← Rec.emb_mul, ← Rec.emb_add, pow_add]
    apply congrArg emb
    linear_combination root ^ q * Rec.two_K

/-- `digitProduct`: `x` to the sum of the digits, embedded in `E`. -/
theorem digitProduct_good (bits : List ℕ) (hlen : 126 ≤ bits.length) :
    Good (Wires bits) (Circuit.digitProduct bits) fun s r s' => s'.statement = s.statement ∧ r < s'.next ∧
      ∀ st val, Sat st s' val → (∀ j < 126, val (bits.getD j 0) 0 = 0 ∨ val (bits.getD j 0) 0 = 1) →
        ev val r = emb (root ^ dsum val bits 42) := by
  unfold Circuit.digitProduct
  refine good_of_post fun s hs hb => ?_
  refine (one_good.pres pres_one).step hs trivial ?_
  rintro o s1 hi1 he1 ⟨hst1, ho, hov⟩
  refine (zero_good.pres pres_zero).step hi1 trivial ?_
  rintro z s2 hi2 he2 ⟨hst2, hz, hzv⟩
  refine post_bind (forIn_range_post 42 _ (fun n acc s' => s'.statement = s.statement ∧ acc < s'.next ∧
      ∀ st val, Sat st s' val → (∀ j < 126, val (bits.getD j 0) 0 = 0 ∨ val (bits.getD j 0) 0 = 1) →
        ev val acc = emb (root ^ dsum val bits n)) hi2 ⟨by omega, lt_mono ho he2, fun st val hsat _ => ?_⟩ ?_) ?_
  · rw [hov st val (hsat.mono he2)]; simp [dsum, emb_one']
  · rintro i hi acc s3 hi3 he3 ⟨hst3, hacc, hv3⟩
    refine post_bind (forIn_range_post 3 _ (fun k acc' s' => s'.statement = s.statement ∧ acc' < s'.next ∧
        ∀ st val, Sat st s' val → (∀ j < 126, val (bits.getD j 0) 0 = 0 ∨ val (bits.getD j 0) 0 = 1) →
          ev val acc' = emb (root ^ (dsum val bits i + pval val bits i k))) hi3
        ⟨hst3, hacc, fun st val hsat hB => by rw [pval_zero, Nat.add_zero]; exact hv3 st val hsat hB⟩ ?_) ?_
    · rintro k hk acc' s4 hi4 he4 ⟨hst4, hacc', hv4⟩
      refine ((mulConstAdd_good acc' _ 0 0 z).pres (pres_mulConstAdd _ _ _ _ _)).step hi4
        (Wires.cons' hacc' (Wires.cons' (lt_mono hz (by ext_chain)) Wires.nil')) ?_
      rintro t s5 hi5 he5 ⟨hst5, ht, htv⟩
      refine ((mulKAdd_good t _ acc').pres (pres_mulKAdd _ _ _)).step hi5 (Wires.cons' ht
        (Wires.cons' (lt_mono (wires_getD' hb (by omega)) (by ext_chain)) (Wires.cons' (lt_mono hacc' he5) Wires.nil')))
        ?_
      rintro acc'' s6 hi6 he6 ⟨hst6, hacc'', hv6⟩
      refine post_pure hi6 (by ext_chain) ⟨acc'', rfl, by omega, hacc'', fun st val hsat hB => ?_⟩
      rw [hv6 st val hsat, htv st val (hsat.mono he6), hzv st val (hsat.mono (by ext_chain)),
        hv4 st val (hsat.mono (by ext_chain)) hB, pval_succ, ← Nat.add_assoc]
      exact digit_mul _ _ hk _ (hB _ (by omega))
    · rintro acc' s4 hi4 he4 ⟨hst4, hacc', hv4⟩
      refine post_pure hi4 he4 ⟨acc', rfl, hst4, hacc', fun st val hsat hB => ?_⟩
      rw [hv4 st val hsat hB, pval_three, dsum_succ]
  · rintro acc s3 hi3 he3 ⟨hst3, hacc, hv3⟩
    exact post_pure hi3 (by ext_chain) ⟨hst3, hacc, hv3⟩

/-! The indicators of a digit's values. -/

/-- A digit bit's factor in an indicator: the bit where the index has it, one plus it where not. -/
noncomputable def fac (x : E) (b : Bool) : E := if b then x else x + 1

/-- The indicator of index `v` over the first `m` bits of `as`. -/
noncomputable def indv (val : Val) (as : List ℕ) (m v : ℕ) : E :=
  ∏ k ∈ Finset.range m, fac (emb (val (as.getD k 0) 0)) (v.testBit k)

theorem testBit_top (v m : ℕ) (hv : v < 2 ^ (m + 1)) : v.testBit m = decide (2 ^ m ≤ v) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h1 : v / 2 ^ m < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hv; omega
  have h2 : 1 ≤ v / 2 ^ m ↔ 2 ^ m ≤ v := by
    rw [Nat.le_div_iff_mul_le (by positivity), one_mul]
  generalize v / 2 ^ m = q at h1 h2
  simp only [decide_eq_decide]
  omega

theorem indv_succ (val : Val) (as : List ℕ) (m v : ℕ) (hv : v < 2 ^ (m + 1)) :
    indv val as (m + 1) v = indv val as m (v % 2 ^ m) * fac (emb (val (as.getD m 0) 0)) (decide (2 ^ m ≤ v)) := by
  unfold indv
  rw [Finset.prod_range_succ, testBit_top v m hv]
  refine congrArg (· * fac (emb (val (as.getD m 0) 0)) (decide (2 ^ m ≤ v))) (Finset.prod_congr rfl fun k hk => ?_)
  rw [Nat.testBit_mod_two_pow, decide_eq_true (Finset.mem_range.mp hk), Bool.true_and]

theorem one_add_one_E : (1 : E) + 1 = 0 := add_self_E 1

/-- Over Boolean bits, the indicator of `v` is one exactly at the bits' value. -/
theorem indv_digit (val : Val) (a0 a1 a2 : ℕ) (h0 : val a0 0 = 0 ∨ val a0 0 = 1) (h1 : val a1 0 = 0 ∨ val a1 0 = 1)
    (h2 : val a2 0 = 0 ∨ val a2 0 = 1) (v : ℕ) (hv : v < 8) :
    indv val [a0, a1, a2] 3 v = if v = dig3 val a0 a1 a2 then 1 else 0 := by
  have g0 : [a0, a1, a2].getD 0 0 = a0 := rfl
  have g1 : [a0, a1, a2].getD 1 0 = a1 := rfl
  have g2 : [a0, a1, a2].getD 2 0 = a2 := rfl
  simp only [indv, dig3, Finset.prod_range_succ, Finset.prod_range_zero, fac, one_mul, g0, g1, g2]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    interval_cases v <;> simp (config := { decide := true }) [h0, h1, h2, Rec.emb_zero, emb_one', one_add_one_E]

/-- `indicators`: entry `v` is the product of the bits' factors at `v`. -/
theorem indicators_good (a0 a1 a2 : ℕ) : Good (Wires [a0, a1, a2]) (Circuit.indicators a0 a1 a2) fun s r s' =>
    s'.statement = s.statement ∧ r.length = 8 ∧ Wires r s' ∧ ∀ st val, Sat st s' val →
      ∀ v < 8, ev val (r.getD v 0) = indv val [a0, a1, a2] 3 v := by
  unfold Circuit.indicators
  refine good_of_post fun s hs ha => ?_
  refine (one_good.pres pres_one).step hs trivial ?_
  rintro o s1 hi1 he1 ⟨hst1, ho, hov⟩
  refine (zero_good.pres pres_zero).step hi1 trivial ?_
  rintro z s2 hi2 he2 ⟨hst2, hz, hzv⟩
  refine post_bind (forIn_post [a0, a1, a2] _ (fun m (level : List ℕ) s' => s'.statement = s.statement ∧
      level.length = 2 ^ m ∧ Wires level s' ∧ ∀ st val, Sat st s' val →
        ∀ v < 2 ^ m, ev val (level.getD v 0) = indv val [a0, a1, a2] m v) hi2
      ⟨by omega, rfl, Wires.cons' (lt_mono ho he2) Wires.nil', fun st val hsat v hv => ?_⟩ ?_) ?_
  · obtain rfl : v = 0 := by omega
    rw [show [o].getD 0 0 = o from rfl, hov st val (hsat.mono he2)]
    simp [indv]
  · rintro m hm level s3 hi3 he3 ⟨hst3, hlen, hw3, hv3⟩
    have hpos : 0 < level.length := by rw [hlen]; positivity
    have ham : [a0, a1, a2][m] < s3.next := lt_mono (ha _ (List.getElem_mem hm)) (by ext_chain)
    have hgm : [a0, a1, a2].getD m 0 = [a0, a1, a2][m] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
    refine post_bind (forIn_range_post (2 * level.length) _ (fun j (next : List ℕ) s' => s'.statement = s.statement ∧
        next.length = j ∧ Wires next s' ∧ ∀ st val, Sat st s' val →
          ∀ v < j, ev val (next.getD v 0) = indv val [a0, a1, a2] (m + 1) v) hi3
        ⟨hst3, rfl, Wires.nil', fun _ _ _ v hv => absurd hv (Nat.not_lt_zero v)⟩ ?_) ?_
    · rintro j hj next s4 hi4 he4 ⟨hst4, hlen4, hw4, hv4⟩
      have hp : level.getD (j % level.length) 0 < s4.next := lt_mono (wires_getD' hw3 (Nat.mod_lt _ hpos)) he4
      have hpv : ∀ st val, Sat st s4 val →
          ev val (level.getD (j % level.length) 0) = indv val [a0, a1, a2] m (j % 2 ^ m) := by
        intro st val hsat
        rw [hv3 st val (hsat.mono he4) _ (by rw [← hlen]; exact Nat.mod_lt _ hpos), hlen]
      have hj' : j < 2 ^ (m + 1) := by rw [pow_succ]; rw [hlen] at hj; omega
      try dsimp only
      split
      · rename_i hjl
        refine ((mulKAdd_good _ _ _).pres (pres_mulKAdd _ _ _)).step hi4
          (Wires.cons' hp (Wires.cons' (lt_mono ham he4) (Wires.cons' hp Wires.nil'))) ?_
        rintro q s5 hi5 he5 ⟨hst5, hq, hqv⟩
        refine post_pure hi5 he5 ⟨next ++ [q], rfl, by omega, by simp [hlen4], Wires.snoc (hw4.mono he5) hq,
          fun st val hsat v hv => ?_⟩
        rw [getD_snoc]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
        · rw [if_pos (by omega)]; exact hv4 st val (hsat.mono he5) v hv
        · rw [if_neg (by omega), if_pos hlen4.symm, hqv st val hsat, hpv st val (hsat.mono he5),
            indv_succ _ _ _ _ hj', hgm, decide_eq_false (by rw [← hlen]; omega), fac, if_neg Bool.false_ne_true]
          ring
      · rename_i hjl
        refine ((mulKAdd_good _ _ _).pres (pres_mulKAdd _ _ _)).step hi4
          (Wires.cons' hp (Wires.cons' (lt_mono ham he4) (Wires.cons' (lt_mono hz (by ext_chain)) Wires.nil'))) ?_
        rintro q s5 hi5 he5 ⟨hst5, hq, hqv⟩
        refine post_pure hi5 he5 ⟨next ++ [q], rfl, by omega, by simp [hlen4], Wires.snoc (hw4.mono he5) hq,
          fun st val hsat v hv => ?_⟩
        rw [getD_snoc]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
        · rw [if_pos (by omega)]; exact hv4 st val (hsat.mono he5) v hv
        · rw [if_neg (by omega), if_pos hlen4.symm, hqv st val hsat, hpv st val (hsat.mono he5),
            indv_succ _ _ _ _ hj', hgm, decide_eq_true (by rw [← hlen]; omega),
            hzv st val (hsat.mono (by ext_chain)), fac, if_pos rfl, add_zero]
    · rintro next s4 hi4 he4 ⟨hst4, hlen4, hw4, hv4⟩
      refine post_pure hi4 he4 ⟨next, rfl, hst4, by rw [hlen4, hlen, pow_succ]; ring, hw4,
        fun st val hsat v hv => hv4 st val hsat v (by rw [hlen, ← pow_succ']; exact hv)⟩
  · rintro level s3 hi3 he3 ⟨hst3, hlen, hw3, hv3⟩
    exact post_pure hi3 (by ext_chain) ⟨hst3, by simpa using hlen, hw3,
      fun st val hsat v hv => hv3 st val hsat v (by simpa using hv)⟩

/-! A chain. -/

/-- Chain `i` at position `p`, from `T` at position `x`. -/
def cpart (i e : ℕ) (P : Dig) (x : ℕ) (T : Dig) (p : ℕ) : Dig :=
  (List.range' x (p - x)).foldl (fun v s => Words.chainStep i s e P v) T

theorem cpart_self (i e : ℕ) (P : Dig) (x : ℕ) (T : Dig) : cpart i e P x T x = T := by
  simp [cpart]

theorem cpart_succ (i e : ℕ) (P : Dig) (x : ℕ) (T : Dig) (p : ℕ) (hx : x ≤ p) :
    cpart i e P x T (p + 1) = Words.chainStep i p e P (cpart i e P x T p) := by
  unfold cpart
  rw [show p + 1 - x = p - x + 1 by omega, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
    show x + 1 * (p - x) = p by omega]

/-- The digest of a chain step's hash. -/
theorem step_dig {val : Val} {d idx p0 p1 v0 v1 i s e : ℕ} {V : Dig}
    (hdv : words4 (val d) = digest (hashWords ([Words.tweak0 1 (8 * i + s), w64 val idx] ++
      ([p0, p1] ++ [v0, v1]).map (w64 val))))
    (hidx : w64 val idx = Words.tweak1 e) (h0 : w64 val v0 = V.1) (h1 : w64 val v1 = V.2) :
    dig val d = Words.chainStep i s e (w64 val p0, w64 val p1) V := by
  apply dig_th
  rw [hdv]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, hidx, h0, h1]

/-- The mux of a chain step: the element when the indicator is one, the current value otherwise. -/
theorem mux_ev (c t u : E) (p : Prop) [Decidable p] (hc : c = if p then 1 else 0) :
    c * (t + u) + u = if p then t else u := by
  subst hc
  split_ifs
  · rw [one_mul, add_assoc, add_self_E, add_zero]
  · rw [zero_mul, zero_add]

/-- `chainEnd`: chain `i` from the element `tip` at the digit `x` to position 7. -/
theorem chainEnd_good (i idx tip p0 p1 : ℕ) (ind : List ℕ) :
    Good (fun s => idx < s.next ∧ tip < s.next ∧ p0 < s.next ∧ p1 < s.next ∧ Wires ind s ∧ ind.length = 8)
      (Circuit.chainEnd i idx tip [p0, p1] ind) fun s r s' => s'.statement = s.statement ∧ r.1 < s'.next ∧
        r.2 < s'.next ∧ ∀ st val, Sat st s' val → ∀ x < 8, ∀ e : ℕ,
          (∀ v < 8, ev val (ind.getD v 0) = if v = x then 1 else 0) → w64 val idx = Words.tweak1 e →
            (w64 val r.1, w64 val r.2) = Words.chainFrom i e (w64 val p0, w64 val p1) x (dig val tip) := by
  unfold Circuit.chainEnd
  refine good_of_post fun s hs ⟨hidx, htip, hp0, hp1, hind, hlen⟩ => ?_
  refine (words_good tip).step hs (Wires.cons' htip Wires.nil') ?_
  rintro ⟨t0, t1, t2⟩ s1 hi1 he1 ⟨hst1, ht0, ht1, -, htv⟩
  try dsimp only
  refine (tweakHash_good 1 (8 * i) idx [p0, p1] [t0, t1] (by norm_num)).step hi1 trivial ?_
  rintro d s2 hi2 he2 ⟨hst2, hd, hdv⟩
  refine ((dToEAndK_good d).pres (pres_dToEAndK d)).step hi2 (Wires.cons' hd Wires.nil') ?_
  rintro ⟨o, o'⟩ s3 hi3 he3 ⟨hst3, ho, -, hov⟩
  try dsimp only
  refine post_bind (forIn_range'_post 6 _ (fun k cur s' => s'.statement = s.statement ∧ cur < s'.next ∧
      ∀ st val, Sat st s' val → ∀ x < 8, ∀ e : ℕ, (∀ v < 8, ev val (ind.getD v 0) = if v = x then 1 else 0) →
        w64 val idx = Words.tweak1 e → x ≤ k →
          dig val cur = cpart i e (w64 val p0, w64 val p1) x (dig val tip) (k + 1)) hi3
      ⟨by omega, ho, fun st val hsat x hx e hi he hxk => ?_⟩ ?_) ?_
  · obtain rfl : x = 0 := by omega
    have h0 : ∀ i : Fin 4, i.val < 3 → val o i = val d i := (hov st val hsat).1
    rw [dig_congr (h0 0 (by decide)) (h0 1 (by decide)), cpart_succ _ _ _ _ _ _ le_rfl, cpart_self]
    obtain ⟨a0, a1, -, -⟩ := htv st val (hsat.mono (by ext_chain))
    exact step_dig (s := 0) (V := dig val tip) (hdv st val (hsat.mono he3)) he (w64_of a0) (w64_of a1)
  · rintro k hk cur s4 hi4 he4 ⟨hst4, hcur, hv4⟩
    have hik : ind.getD (k + 1) 0 < s4.next := lt_mono (wires_getD' hind (by omega)) (by ext_chain)
    refine ((add_good tip cur).pres (pres_add _ _)).step hi4
      (Wires.cons' (lt_mono htip (by ext_chain)) (Wires.cons' hcur Wires.nil')) ?_
    rintro diff s5 hi5 he5 ⟨hst5, hdiff, hdiffv⟩
    refine ((mulAdd_good _ diff cur).pres (pres_mulAdd _ _ _)).step hi5
      (Wires.cons' (lt_mono hik he5) (Wires.cons' hdiff (Wires.cons' (lt_mono hcur he5) Wires.nil'))) ?_
    rintro m s6 hi6 he6 ⟨hst6, hm, hmv⟩
    refine (words_good m).step hi6 (Wires.cons' hm Wires.nil') ?_
    rintro ⟨v0, v1, v2⟩ s7 hi7 he7 ⟨hst7, hv0, hv1, -, hvv⟩
    try dsimp only
    refine (tweakHash_good 1 (8 * i + (k + 1)) idx [p0, p1] [v0, v1] (by norm_num)).step hi7 trivial ?_
    rintro d' s8 hi8 he8 ⟨hst8, hd', hdv'⟩
    refine ((dToEAndK_good d').pres (pres_dToEAndK d')).step hi8 (Wires.cons' hd' Wires.nil') ?_
    rintro ⟨o2, o2'⟩ s9 hi9 he9 ⟨hst9, ho2, -, hov2⟩
    try dsimp only
    refine post_pure hi9 (by ext_chain) ⟨o2, rfl, by omega, ho2, fun st val hsat x hx e hi he hxk => ?_⟩
    have h0 : ∀ i : Fin 4, i.val < 3 → val o2 i = val d' i := (hov2 st val hsat).1
    rw [dig_congr (h0 0 (by decide)) (h0 1 (by decide)), cpart_succ _ _ _ _ _ _ hxk]
    obtain ⟨a0, a1, -, -⟩ := hvv st val (hsat.mono (by ext_chain))
    rw [step_dig (V := dig val m) (hdv' st val (hsat.mono he9)) he (w64_of a0) (w64_of a1)]
    apply congrArg (Words.chainStep i (k + 1) e _)
    have hmev : ev val m = if k + 1 = x then ev val tip else ev val cur := by
      rw [hmv st val (hsat.mono (by ext_chain)), hdiffv st val (hsat.mono (by ext_chain))]
      exact mux_ev _ _ _ _ (hi (k + 1) (by omega))
    split_ifs at hmev with hkx
    · rw [dig_of_ev hmev, ← hkx, cpart_self]
    · rw [dig_of_ev hmev]
      exact hv4 st val (hsat.mono (by ext_chain)) x hx e hi he (by omega)
  · rintro cur s4 hi4 he4 ⟨hst4, hcur, hv4⟩
    have hik : ind.getD 7 0 < s4.next := lt_mono (wires_getD' hind (by omega)) (by ext_chain)
    refine ((add_good tip cur).pres (pres_add _ _)).step hi4
      (Wires.cons' (lt_mono htip (by ext_chain)) (Wires.cons' hcur Wires.nil')) ?_
    rintro diff s5 hi5 he5 ⟨hst5, hdiff, hdiffv⟩
    refine ((mulAdd_good _ diff cur).pres (pres_mulAdd _ _ _)).step hi5
      (Wires.cons' (lt_mono hik he5) (Wires.cons' hdiff (Wires.cons' (lt_mono hcur he5) Wires.nil'))) ?_
    rintro m s6 hi6 he6 ⟨hst6, hm, hmv⟩
    refine (words_good m).step hi6 (Wires.cons' hm Wires.nil') ?_
    rintro ⟨n0, n1, n2⟩ s7 hi7 he7 ⟨hst7, hn0, hn1, -, hnv⟩
    try dsimp only
    refine post_pure hi7 (by ext_chain) ⟨by omega, hn0, hn1, fun st val hsat x hx e hi he => ?_⟩
    obtain ⟨a0, a1, -, -⟩ := hnv st val hsat
    have a0' : val n0 0 = val m 0 := a0
    have a1' : val n1 0 = val m 1 := a1
    show (w64 val n0, w64 val n1) = cpart i e (w64 val p0, w64 val p1) x (dig val tip) 7
    rw [w64_of a0', w64_of a1']
    show dig val m = cpart i e (w64 val p0, w64 val p1) x (dig val tip) 7
    have hmev : ev val m = if 7 = x then ev val tip else ev val cur := by
      rw [hmv st val (hsat.mono he7), hdiffv st val (hsat.mono (by ext_chain))]
      exact mux_ev _ _ _ _ (hi 7 (by omega))
    split_ifs at hmev with hkx
    · rw [dig_of_ev hmev, ← hkx, cpart_self]
    · rw [dig_of_ev hmev]
      exact hv4 st val (hsat.mono (by ext_chain)) x hx e hi he (by omega)

/-! A level of the path. -/

/-- `level`: the parent of `node` and a sibling, on the side bit `l` of the epoch names. -/
theorem level_good (l idx bit node p0 p1 : ℕ) :
    Good (fun s => idx < s.next ∧ bit < s.next ∧ node < s.next ∧ p0 < s.next ∧ p1 < s.next)
      (Circuit.level l idx bit node [p0, p1]) fun s r s' => s'.statement = s.statement ∧ r < s'.next ∧
        ∀ st val, Sat st s' val → ∃ sib : Dig, ∀ e : ℕ, w64 val idx = Words.tweak1 (e / 2 ^ (l + 1)) →
          (val bit 0 = 0 ∨ val bit 0 = 1) → (val bit 0 = 1 ↔ e.testBit l = true) →
            dig val r = Words.parent e l (w64 val p0, w64 val p1) (dig val node) sib := by
  unfold Circuit.level
  refine good_of_post fun s hs ⟨hidx, hbit, hnode, hp0, hp1⟩ => ?_
  refine ((dToEAndK_good node).pres (pres_dToEAndK node)).step hs (Wires.cons' hnode Wires.nil') ?_
  rintro ⟨cur, cur'⟩ s1 hi1 he1 ⟨hst1, hcur, -, hcurv⟩
  try dsimp only
  refine fresh_good'.step hi1 trivial ?_
  rintro sib s2 hi2 he2 ⟨hst2, hsib⟩
  refine ((add_good cur sib).pres (pres_add _ _)).step hi2
    (Wires.cons' (lt_mono hcur he2) (Wires.cons' hsib Wires.nil')) ?_
  rintro diff s3 hi3 he3 ⟨hst3, hdiff, hdiffv⟩
  refine ((mulKAdd_good diff bit cur).pres (pres_mulKAdd _ _ _)).step hi3
    (Wires.cons' hdiff (Wires.cons' (lt_mono hbit (by ext_chain))
      (Wires.cons' (lt_mono hcur (by ext_chain)) Wires.nil'))) ?_
  rintro left s4 hi4 he4 ⟨hst4, hleft, hleftv⟩
  refine ((add_good left diff).pres (pres_add _ _)).step hi4
    (Wires.cons' hleft (Wires.cons' (lt_mono hdiff he4) Wires.nil')) ?_
  rintro right s5 hi5 he5 ⟨hst5, hright, hrightv⟩
  refine (words_good left).step hi5 (Wires.cons' (lt_mono hleft he5) Wires.nil') ?_
  rintro ⟨l0, l1, l2⟩ s6 hi6 he6 ⟨hst6, hl0, hl1, -, hlv⟩
  try dsimp only
  refine (words_good right).step hi6 (Wires.cons' (lt_mono hright he6) Wires.nil') ?_
  rintro ⟨r0, r1, r2⟩ s7 hi7 he7 ⟨hst7, hr0, hr1, -, hrv⟩
  try dsimp only
  refine (tweakHash_good 3 (l + 1) idx [p0, p1] [l0, l1, r0, r1] (by norm_num)).last hi7 trivial (by ext_chain) ?_
  rintro r s8 he8 ⟨hst8, hr, hrv8⟩
  refine ⟨by omega, hr, fun st val hsat => ⟨dig val sib, fun e hidxe hb hbe => ?_⟩⟩
  have hsat7 := hsat.mono he8
  have hc : ∀ i : Fin 4, i.val < 3 → val cur i = val node i := (hcurv st val (hsat.mono (by ext_chain))).1
  have hcn : dig val cur = dig val node := dig_congr (hc 0 (by decide)) (hc 1 (by decide))
  obtain ⟨la0, la1, -, -⟩ := hlv st val (hsat.mono (by ext_chain))
  obtain ⟨ra0, ra1, -, -⟩ := hrv st val hsat7
  have hL : ev val left = ev val diff * emb (val bit 0) + ev val cur := hleftv st val (hsat.mono (by ext_chain))
  have hR : ev val right = ev val left + ev val diff := hrightv st val (hsat.mono (by ext_chain))
  have hD : ev val diff = ev val cur + ev val sib := hdiffv st val (hsat.mono (by ext_chain))
  have hw : ∀ (L R : ℕ), w64 val l0 = words4 (val L) 0 → w64 val l1 = words4 (val L) 1 →
      w64 val r0 = words4 (val R) 0 → w64 val r1 = words4 (val R) 1 →
      dig val r = Words.th 3 (l + 1) (e / 2 ^ (l + 1)) (w64 val p0, w64 val p1)
        [(dig val L).1, (dig val L).2, (dig val R).1, (dig val R).2] := by
    intro L R h0 h1 h2 h3
    apply dig_th
    rw [hrv8 st val hsat, hidxe]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, h0, h1, h2, h3, dig]
  rcases hb with hb | hb
  · have hnt : ¬ e.testBit l = true := fun h => by
      have := hbe.mpr h; rw [hb] at this; exact zero_ne_one this
    have hl : ev val left = ev val cur := by rw [hL, hb, Rec.emb_zero, mul_zero, zero_add]
    have hr' : ev val right = ev val sib := by rw [hR, hl, hD, ← add_assoc, add_self_E, zero_add]
    rw [Words.parent, if_neg hnt, ← hcn, ← dig_of_ev hl, ← dig_of_ev hr']
    exact hw left right (w64_of la0) (w64_of la1) (w64_of ra0) (w64_of ra1)
  · have ht : e.testBit l = true := hbe.mp hb
    have hl : ev val left = ev val sib := by
      rw [hL, hb, emb_one', mul_one, hD, add_assoc, add_comm (ev val sib), ← add_assoc, add_self_E, zero_add]
    have hr' : ev val right = ev val cur := by
      rw [hR, hl, hD, add_comm (ev val cur), ← add_assoc, add_self_E, zero_add]
    rw [Words.parent, if_pos ht, ← hcn, ← dig_of_ev hl, ← dig_of_ev hr']
    exact hw left right (w64_of la0) (w64_of la1) (w64_of ra0) (w64_of ra1)

end LeanVMCircuits.Xmss
