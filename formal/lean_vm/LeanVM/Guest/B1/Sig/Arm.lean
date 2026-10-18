/-
  LeanVM.Guest.B1.Sig.Arm

  The walks of one digit group's arm and the arm itself (`walk_group`, G:2334-2342): the chains
  at the arm's digits, the digit sum folded into the product, the digits into the encoding.
-/

module

public import LeanVM.Guest.B1.Sig.Walk

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The tips `t` hold chain `i`'s end at digit `d` from the value `x`. -/
def TipSet (w : Wots) (σ : Val) (i d : Nat) (x : E) (t : V × V) : Prop :=
  σ t.1 = (tipPair w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i d x).1 ∧
    (d ≠ 3 → σ t.2 = (tipPair w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i d x).2)

theorem TipSet.congr {w : Wots} {σ σ' : Val} {i d : Nat} {x : E} {t : V × V} (h : TipSet w σ i d x t)
    (hk : w.pp' σ' = w.pp' σ ∧ w.adr' σ' = w.adr' σ ∧ w.idx' σ' = w.idx' σ ∧ σ' w.md = σ w.md)
    (h1 : σ' t.1 = σ t.1) (h2 : σ' t.2 = σ t.2) : TipSet w σ' i d x t := by
  rw [TipSet, hk.1, hk.2.1, hk.2.2.1, h1, h2]; exact h

/-- The digit of chain `first + r` in arm `k`. -/
def armDigit (k r : Nat) : Nat := k / 4 ^ r % 4

theorem armDigit_lt (k r : Nat) : armDigit k r < 4 := Nat.mod_lt _ (by norm_num)

/-- Where an arm's tips are: the first arm puts them after each walk (`fresh`, every digit
zero), the others read them below their base. -/
def TipsPos (lx : Bool) (tips : Nat → V × V) (k : Nat) (fresh : Bool) (m r b : Nat) : Prop :=
  if fresh then k = 0 ∧ ∀ r', r ≤ r' → r' < r + m →
      tips r' = (.n (b + chainStride lx * (r' - r) + walkSize lx 0),
        .n (b + chainStride lx * (r' - r) + walkSize lx 0 + 1))
  else ∀ r', r ≤ r' → r' < r + m → (∃ j < b, (tips r').1 = .n j) ∧ (∃ j < b, (tips r').2 = .n j)

theorem walkSize_zero_of (lx : Bool) {k r : Nat} (hk : k = 0) :
    walkSize lx (armDigit k r) = walkSize lx 0 := by
  rw [hk, armDigit]; simp

theorem cWalks_snd (w : Wots) (tips : Nat → V × V) (first k : Nat) (fresh : Bool) :
    ∀ (m r b : Nat), b ≤ (cWalks w tips first k fresh m r b).2
  | 0, _, _ => le_rfl
  | m + 1, r, b => by
      simp only [cWalks]
      exact le_trans (by omega) (cWalks_snd w tips first k fresh m (r + 1) _)

theorem cWalks_sound {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {tips : Nat → V × V} {first k : Nat} {fresh : Bool} :
    ∀ (m r b : Nat) {next : Prop} {kret : List E → Prop},
      Stmt.HoldsList C rd σ (cWalks w tips first k fresh m r b).1 next kret →
        (∀ r', r ≤ r' → r' < r + m → ∃ x, TipSet w σ (first + r') (armDigit k r') x (tips r')) ∧ next
  | 0, _, _, _, _, h => ⟨fun r' h1 h2 => absurd h2 (by omega), h⟩
  | m + 1, r, b, next, kret, h => by
      simp only [cWalks] at h
      rw [holdsList_append] at h
      obtain ⟨⟨x, hx1, hx2⟩, h⟩ := cWalk_sound hmd h
      obtain ⟨hr, hn⟩ := cWalks_sound hmd m (r + 1) _ h
      refine ⟨fun r' h1 h2 => ?_, hn⟩
      by_cases e : r' = r
      · subst e; exact ⟨x, hx1, hx2⟩
      · exact hr r' (by omega) (by omega)

theorem cWalks_below {w : Wots} {tips : Nat → V × V} {first k : Nat} {fresh : Bool} {hi : Nat}
    (hw : w.Below hi) :
    ∀ (m r b : Nat), (∀ r', r ≤ r' → r' < r + m →
      (∃ j < hi, (tips r').1 = .n j) ∧ (∃ j < hi, (tips r').2 = .n j)) →
      (cWalks w tips first k fresh m r b).2 ≤ hi →
      NumBelow hi (Stmt.valsList (cWalks w tips first k fresh m r b).1)
  | 0, _, _, _, _ => NumBelow.nil hi
  | m + 1, r, b, ht, hb => by
      simp only [cWalks] at hb ⊢
      rw [valsList_append]
      have h2 := cWalks_snd w tips first k fresh m (r + 1)
        (b + walkSize w.lx (k / 4 ^ r % 4) + if fresh = true then 2 else 0)
      exact (cWalk_below hw (ht r le_rfl (by omega)).1 (ht r le_rfl (by omega)).2
        (le_trans (Nat.le_add_right _ _) (le_trans h2 hb))).append
        (cWalks_below hw m (r + 1) _ (fun r' h1 h2 => ht r' (by omega) (by omega)) hb)

/-- The next base after a walk. -/
def walkNext (lx fresh : Bool) (k r b : Nat) : Nat :=
  b + walkSize lx (armDigit k r) + (if fresh then 2 else 0)

theorem TipsPos.head {lx : Bool} {tips : Nat → V × V} {k : Nat} {fresh : Bool} {m r b : Nat}
    (h : TipsPos lx tips k fresh (m + 1) r b) :
    Out b (b + walkSize lx (armDigit k r)) (tips r).1 ∧ Out b (b + walkSize lx (armDigit k r)) (tips r).2 ∧
      (∃ j < walkNext lx fresh k r b, (tips r).1 = .n j) ∧
      (∃ j < walkNext lx fresh k r b, (tips r).2 = .n j) := by
  unfold TipsPos at h
  unfold walkNext
  cases fresh
  · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨⟨j1, hj1, e1⟩, ⟨j2, hj2, e2⟩⟩ := h r le_rfl (by omega)
    exact ⟨out_of_lt ⟨j1, hj1, e1⟩, out_of_lt ⟨j2, hj2, e2⟩, ⟨j1, by omega, e1⟩, ⟨j2, by omega, e2⟩⟩
  · simp only [↓reduceIte] at h ⊢
    obtain ⟨hk, ht⟩ := h
    rw [ht r le_rfl (by omega), walkSize_zero_of lx hk]
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    exact ⟨out_of_ge ⟨_, le_rfl, rfl⟩, out_of_ge ⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩,
      ⟨_, by omega, rfl⟩⟩

theorem TipsPos.tail {lx : Bool} {tips : Nat → V × V} {k : Nat} {fresh : Bool} {m r b : Nat}
    (h : TipsPos lx tips k fresh (m + 1) r b) : TipsPos lx tips k fresh m (r + 1) (walkNext lx fresh k r b) := by
  unfold TipsPos at h ⊢
  unfold walkNext
  cases fresh
  · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact fun r' h1 h2 => let ⟨⟨j1, hj1, e1⟩, ⟨j2, hj2, e2⟩⟩ := h r' (by omega) (by omega)
      ⟨⟨j1, by omega, e1⟩, ⟨j2, by omega, e2⟩⟩
  · simp only [↓reduceIte] at h ⊢
    obtain ⟨hk, ht⟩ := h
    refine ⟨hk, fun r' h1 h2 => ?_⟩
    rw [ht r' (by omega) (by omega), walkSize_zero_of lx hk]
    have e : chainStride lx * (r' - r) = chainStride lx * (r' - (r + 1)) + chainStride lx := by
      rw [show r' - r = r' - (r + 1) + 1 by omega, Nat.mul_succ]
    rw [e, chainStride]
    simp only [Prod.mk.injEq, V.mk.injEq, true_and]
    omega

theorem TipsPos.later {lx : Bool} {tips : Nat → V × V} {k : Nat} {fresh : Bool} {m r b : Nat}
    (h : TipsPos lx tips k fresh (m + 1) r b) {r' : Nat} (h1 : r < r') (h2 : r' < r + 1 + m) :
    Out b (walkNext lx fresh k r b) (tips r').1 ∧ Out b (walkNext lx fresh k r b) (tips r').2 := by
  unfold TipsPos at h
  unfold walkNext
  cases fresh
  · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact ⟨out_of_lt (h r' (by omega) (by omega)).1, out_of_lt (h r' (by omega) (by omega)).2⟩
  · simp only [↓reduceIte] at h ⊢
    obtain ⟨hk, ht⟩ := h
    rw [ht r' (by omega) (by omega), walkSize_zero_of lx hk]
    have : chainStride lx ≤ chainStride lx * (r' - r) := Nat.le_mul_of_pos_right _ (by omega)
    exact ⟨out_of_ge ⟨_, by simp only [chainStride] at this ⊢; omega, rfl⟩,
      out_of_ge ⟨_, by simp only [chainStride] at this ⊢; omega, rfl⟩⟩

theorem cWalks_eq (w : Wots) (tips : Nat → V × V) (first k : Nat) (fresh : Bool) (m r b : Nat) :
    cWalks w tips first k fresh (m + 1) r b =
      (cWalk w (first + r) (armDigit k r) b (tips r).1 (tips r).2 ++
        (cWalks w tips first k fresh m (r + 1) (walkNext w.lx fresh k r b)).1,
        (cWalks w tips first k fresh m (r + 1) (walkNext w.lx fresh k r b)).2) := rfl

/-- **An arm's walks are complete**: from the values `xs`, the tips preset to the chains' ends. -/
theorem cWalks_complete {w : Wots} {tips : Nat → V × V} {first k : Nat} {fresh : Bool} {xs : Nat → E} :
    ∀ (m r b : Nat) (σ : Val), w.Below b → TipsPos w.lx tips k fresh m r b →
      σ w.md = mdw (stepCount w.lx) true → w.Canon σ →
      (∀ r', r ≤ r' → r' < r + m →
        IsCanonical128 (xs r') ∧ TipSet w σ (first + r') (armDigit k r') (xs r') (tips r')) →
      Completes C rd b (cWalks w tips first k fresh m r b).2 (cWalks w tips first k fresh m r b).1 σ
        (fun σ' => ∀ r', r ≤ r' → r' < r + m → σ' (tips r').1 = σ (tips r').1 ∧ σ' (tips r').2 = σ (tips r').2)
  | 0, _, b, σ, _, _, _, _, _ => ⟨σ, Ext.refl _ _ _, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ hn => hn⟩
  | m + 1, r, b, σ, hw, hp, hmd, hc, hx => by
      rw [cWalks_eq]
      dsimp only
      obtain ⟨ho1, ho2, hb1, hb2⟩ := hp.head
      have hnext : b + walkSize w.lx (armDigit k r) ≤ walkNext w.lx fresh k r b := by
        unfold walkNext; omega
      refine Completes.append (m := walkNext w.lx fresh k r b)
        (P := fun σ' => Ext b (b + walkSize w.lx (armDigit k r)) σ σ') (by omega)
        (cWalks_snd w tips first k fresh m (r + 1) _) ?_ ?_ ?_
      · exact cWalk_below (hw.mono (by omega)) hb1 hb2 hnext
      · obtain ⟨hxc, hxs⟩ := hx r le_rfl (by omega)
        exact (cWalk_complete hw ho1 ho2 hmd hc hxc hxs.1 hxs.2).withExt.mono le_rfl hnext fun _ h => h.2
      · intro σ' he hp'
        have hk := hw.keep he
        refine (cWalks_complete (xs := xs) m (r + 1) _ σ' (hw.mono (by omega))
          hp.tail (by rw [hk.2.2.2, hmd]) (hc.congr hk) fun r' h1 h2 => ?_).withExt.mono le_rfl le_rfl
          fun σ'' h => fun r' h1 h2 => ?_
        · obtain ⟨hxc, hxs⟩ := hx r' (by omega) (by omega)
          obtain ⟨o1, o2⟩ := hp.later (show r < r' by omega) (by omega)
          exact ⟨hxc, hxs.congr hk (he.out o1) (he.out o2)⟩
        · by_cases e : r' = r
          · subst e
            have hb1' : Out (walkNext w.lx fresh k r' b) (cWalks w tips first k fresh m (r' + 1)
                (walkNext w.lx fresh k r' b)).2 (tips r').1 := out_of_lt hb1
            have hb2' : Out (walkNext w.lx fresh k r' b) (cWalks w tips first k fresh m (r' + 1)
                (walkNext w.lx fresh k r' b)).2 (tips r').2 := out_of_lt hb2
            exact ⟨(h.2.out hb1').trans (hp'.out ho1), (h.2.out hb2').trans (hp'.out ho2)⟩
          · obtain ⟨o1, o2⟩ := hp.later (show r < r' by omega) (by omega)
            have := h.1 r' (by omega) (by omega)
            exact ⟨this.1.trans (hp'.out (o1.mono le_rfl hnext)), this.2.trans (hp'.out (o2.mono le_rfl hnext))⟩

/-! ## An arm -/

theorem cWalks_snd_fresh (w : Wots) (tips : Nat → V × V) (first : Nat) :
    ∀ (m r b : Nat), (cWalks w tips first 0 true m r b).2 = b + chainStride w.lx * m
  | 0, _, _ => by simp [cWalks]
  | m + 1, r, b => by
      rw [cWalks_eq]
      dsimp only
      rw [cWalks_snd_fresh w tips first m (r + 1), walkNext, walkSize_zero_of _ rfl, chainStride]
      simp only [↓reduceIte]
      ring

/-- The chains of an arm hold their ends at its digits. -/
def ArmOK (w : Wots) (σ : Val) (tips : Nat → V × V) (first n k : Nat) : Prop :=
  ∀ r < n, ∃ x, TipSet w σ (first + r) (armDigit k r) x (tips r)

theorem lit_zero : lit 0 = 0 := by rw [lit]; simp [word_zero]

/-- The values an arm folds: the product by `g^(digit sum)`, the encoding by `k · 4^first`. -/
def ArmFold (σ : Val) (power : Nat → V) (prodIn encIn prodOut encOut : V) (first n k : Nat)
    (fold : Bool) : Prop :=
  σ prodOut = (if fold then 1 else σ prodIn) * σ (power (digitSum k n)) ∧
    σ encOut = (if fold then 0 else σ encIn) + lit (k * 4 ^ first)

theorem cArm_sound {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {tips : Nat → V × V} {power : Nat → V} {prodIn encIn prodOut encOut : V} {first n k : Nat}
    {fold fresh : Bool} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).1
      next kret) :
    ArmOK w σ tips first n k ∧ ArmFold σ power prodIn encIn prodOut encOut first n k fold ∧ next := by
  unfold cArm at h
  have hw : ∀ {X : Prop} (b0 : Nat),
      Stmt.HoldsList C rd σ (cWalks w tips first k fresh n 0 b0).1 X kret → ArmOK w σ tips first n k ∧ X :=
    fun b0 h => let ⟨h1, h2⟩ := cWalks_sound hmd n 0 b0 h
      ⟨fun r hr => by simpa using h1 r (Nat.zero_le r) (by omega), h2⟩
  have hlit : k = 0 → lit (k * 4 ^ first) = 0 := fun hk => by rw [hk, Nat.zero_mul, lit_zero]
  by_cases hk : k = 0
  · have hl := hlit hk
    subst hk
    simp only [↓reduceIte] at h
    cases fold <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, holdsList_append, cst,
        holdsList_cons_atom, holdsList_nil, Atom.Holds, mulS] at h
    · obtain ⟨ha, h1, h2, hn⟩ := hw _ h
      exact ⟨ha, ⟨h1, by simp only [Bool.false_eq_true, ↓reduceIte]; rw [h2, hl, add_zero]⟩, hn⟩
    · obtain ⟨h0, h⟩ := h
      obtain ⟨ha, h1, h2, hn⟩ := hw _ h
      exact ⟨ha, ⟨by simp [h1], by simp only [↓reduceIte]; rw [h2, h0, hl, word_zero, add_zero]⟩, hn⟩
  · simp only [hk, ↓reduceIte] at h
    cases fold <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, holdsList_append, cst, addS,
        holdsList_cons_atom, holdsList_nil, Atom.Holds, mulS] at h
    · obtain ⟨ha, h1, h2, h3, hn⟩ := hw _ h
      exact ⟨ha, ⟨h1, by simp only [Bool.false_eq_true, ↓reduceIte]; rw [h3, h2]⟩, hn⟩
    · obtain ⟨h0, h⟩ := h
      obtain ⟨ha, h1, h2, h3, hn⟩ := hw _ h
      exact ⟨ha, ⟨by simp [h1], by simp only [↓reduceIte]; rw [h3, h2, h0, word_zero]⟩, hn⟩

/-- The base of an arm's walks. -/
def armStart (fold : Bool) (b : Nat) : Nat := if fold then b + 1 else b

/-- The end of an arm's walks. -/
def armWalksEnd (w : Wots) (tips : Nat → V × V) (first n k : Nat) (fold fresh : Bool) (b : Nat) : Nat :=
  (cWalks w tips first k fresh n 0 (armStart fold b)).2

theorem cArm_snd (w : Wots) (tips : Nat → V × V) (power : Nat → V) (prodIn encIn prodOut encOut : V)
    (first n k : Nat) (fold fresh : Bool) (b : Nat) :
    (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).2 =
      armWalksEnd w tips first n k fold fresh b + (if fresh then 2 else 0) + (if k = 0 then 0 else 1) := by
  unfold cArm armWalksEnd armStart
  by_cases hk : k = 0 <;> simp [hk]

theorem armWalksEnd_ge (w : Wots) (tips : Nat → V × V) (first n k : Nat) (fold fresh : Bool) (b : Nat) :
    armStart fold b ≤ armWalksEnd w tips first n k fold fresh b := cWalks_snd _ _ _ _ _ _ _ _

theorem holdsList_singleton_atom (a : Atom) (next : Prop) (kret : List E → Prop) (σ : Val) :
    Stmt.HoldsList C rd σ [.atom a] next kret ↔ a.Holds rd σ ∧ next := Iff.rfl

/-- The statements after an arm's walks. -/
def armTail (power : Nat → V) (prodIn encIn prodOut encOut : V) (first n k : Nat) (fold : Bool)
    (b1 b : Nat) : List Stmt :=
  let enc0 := if fold then V.n b else encIn
  let prod := if fold then Stmt.atom (.copy prodOut (power (digitSum k n)))
    else mulS prodOut prodIn (power (digitSum k n))
  if k = 0 then [prod, .atom (.copy encOut enc0)]
  else [prod, cst b1 (lit (k * 4 ^ first)), addS encOut enc0 (.n b1)]

theorem cArm_fst (w : Wots) (tips : Nat → V × V) (power : Nat → V) (prodIn encIn prodOut encOut : V)
    (first n k : Nat) (fold fresh : Bool) (b : Nat) :
    (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).1 =
      ((if fold then [cst b (word 0 0 0)] else []) ++ (cWalks w tips first k fresh n 0 (armStart fold b)).1) ++
        armTail power prodIn encIn prodOut encOut first n k fold
          (armWalksEnd w tips first n k fold fresh b + (if fresh then 2 else 0)) b := by
  unfold cArm armTail armWalksEnd armStart
  by_cases hk : k = 0 <;> simp [hk]

theorem armTail_complete {power : Nat → V} {prodIn encIn prodOut encOut : V} {first n k : Nat}
    {fold : Bool} {b1 b : Nat} {σ : Val}
    (hlt : (∃ j < b1, prodIn = .n j) ∧ (∃ j < b1, encIn = .n j) ∧ (∃ j < b1, prodOut = .n j) ∧
      (∃ j < b1, encOut = .n j) ∧ (∃ j < b1, power (digitSum k n) = .n j) ∧ (fold = true → b < b1))
    (hprod : σ prodOut = (if fold then 1 else σ prodIn) * σ (power (digitSum k n)))
    (henc : σ encOut = (if fold then σ (.n b) else σ encIn) + lit (k * 4 ^ first)) :
    Completes C rd b1 (b1 + (if k = 0 then 0 else 1))
      (armTail power prodIn encIn prodOut encOut first n k fold b1 b) σ (fun _ => True) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hlt
  by_cases hk : k = 0
  · subst hk
    refine ⟨σ, Ext.refl _ _ _, trivial, fun next kret hn => ?_⟩
    rw [Nat.zero_mul, lit_zero, add_zero] at henc
    cases fold <;> simp_all [armTail, mulS, Atom.Holds]
  · let σ' := Function.update σ (.n b1) (lit (k * 4 ^ first))
    have he : Ext b1 (b1 + 1) σ σ' := ext_update σ _ le_rfl (by omega)
    have hk' := fun {v : V} (hv : ∃ j < b1, v = .n j) => he.below hv
    refine ⟨σ', by simpa [hk] using he, trivial, fun next kret hn => ?_⟩
    have hb1 : σ' (.n b1) = lit (k * 4 ^ first) := by simp [σ']
    cases fold
    · simp only [armTail, hk, ↓reduceIte, Bool.false_eq_true, mulS, cst, addS, holdsList_cons_atom,
        holdsList_nil, Atom.Holds]
      rw [hk' h1, hk' h2, hk' h3, hk' h4, hk' h5, hb1]
      simp only [Bool.false_eq_true, ↓reduceIte] at hprod henc
      exact ⟨hprod, rfl, henc, hn⟩
    · simp only [armTail, hk, ↓reduceIte, cst, addS, holdsList_cons_atom, holdsList_nil, Atom.Holds]
      rw [hk' h3, hk' h4, hk' h5, hb1, hk' ⟨b, h6 rfl, rfl⟩]
      simp only [↓reduceIte, one_mul] at hprod henc
      exact ⟨hprod, rfl, henc, hn⟩

/-- **An arm is complete**: its tips, product and encoding preset to what the arm computes. -/
theorem cArm_complete {w : Wots} {tips : Nat → V × V} {power : Nat → V}
    {prodIn encIn prodOut encOut : V} {first n k : Nat} {fold fresh : Bool} {b : Nat} {xs : Nat → E}
    {σ : Val} (hw : w.Below b) (hpos : TipsPos w.lx tips k fresh n 0 (if fresh then armStart fold b else b))
    (hout : if fresh then prodOut = .n (armWalksEnd w tips first n k fold fresh b) ∧
        encOut = .n (armWalksEnd w tips first n k fold fresh b + 1)
      else (∃ j < b, prodOut = .n j) ∧ (∃ j < b, encOut = .n j))
    (hin : (∃ j < b, prodIn = .n j) ∧ (∃ j < b, encIn = .n j) ∧ ∃ j < b, power (digitSum k n) = .n j)
    (hmd : σ w.md = mdw (stepCount w.lx) true) (hc : w.Canon σ)
    (hx : ∀ r < n, IsCanonical128 (xs r) ∧ TipSet w σ (first + r) (armDigit k r) (xs r) (tips r))
    (hf : ArmFold σ power prodIn encIn prodOut encOut first n k fold) :
    Completes C rd b (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).2
      (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).1 σ (fun σ' =>
        (∀ r < n, σ' (tips r).1 = σ (tips r).1 ∧ σ' (tips r).2 = σ (tips r).2) ∧
          σ' prodOut = σ prodOut ∧ σ' encOut = σ encOut) := by
  set e := armWalksEnd w tips first n k fold fresh b with he_def
  have hab : b ≤ armStart fold b := by unfold armStart; split <;> omega
  have he0 := armWalksEnd_ge w tips first n k fold fresh b
  rw [← he_def] at he0
  have hsnd := cArm_snd w tips power prodIn encIn prodOut encOut first n k fold fresh b
  rw [← he_def] at hsnd
  rw [hsnd]
  -- the outputs are outside the walks and the first constant
  have hO : Out b e prodOut ∧ Out b e encOut ∧ (∃ j < e + (if fresh then 2 else 0), prodOut = .n j) ∧
      ∃ j < e + (if fresh then 2 else 0), encOut = .n j := by
    cases fresh
    · simp only [Bool.false_eq_true, ↓reduceIte] at hout ⊢
      exact ⟨out_of_lt hout.1, out_of_lt hout.2, let ⟨j, hj, e'⟩ := hout.1; ⟨j, by omega, e'⟩,
        let ⟨j, hj, e'⟩ := hout.2; ⟨j, by omega, e'⟩⟩
    · simp only [↓reduceIte] at hout ⊢
      rw [hout.1, hout.2]
      exact ⟨out_of_ge ⟨e, le_rfl, rfl⟩, out_of_ge ⟨e + 1, by omega, rfl⟩, ⟨e, by omega, rfl⟩,
        ⟨e + 1, by omega, rfl⟩⟩
  have hpos' : TipsPos w.lx tips k fresh n 0 (armStart fold b) := by
    cases fresh
    · simp only [TipsPos, Bool.false_eq_true, ↓reduceIte] at hpos ⊢
      exact fun r h1' h2' => let ⟨⟨j1, h1, e1⟩, ⟨j2, h2, e2⟩⟩ := hpos r h1' h2'
        ⟨⟨j1, by omega, e1⟩, ⟨j2, by omega, e2⟩⟩
    · simpa using hpos
  have hk0 : fresh = true → k = 0 := fun h => by
    simp only [TipsPos, h, ↓reduceIte] at hpos; exact hpos.1
  -- the walks' tips are outside the first constant
  have htb : ∀ r < n, Out b (b + 1) (tips r).1 ∧ Out b (b + 1) (tips r).2 := by
    intro r hr
    cases fresh
    · simp only [TipsPos, Bool.false_eq_true, ↓reduceIte] at hpos
      exact ⟨out_of_lt (hpos r (Nat.zero_le _) (by omega)).1, out_of_lt (hpos r (Nat.zero_le _) (by omega)).2⟩
    · simp only [TipsPos, ↓reduceIte] at hpos
      rw [hpos.2 r (Nat.zero_le r) (by omega)]
      have : 1 ≤ walkSize w.lx 0 := by rw [walkSize_eq _ (by decide)]; omega
      exact ⟨out_of_ge ⟨_, by omega, rfl⟩, out_of_ge ⟨_, by omega, rfl⟩⟩
  have hpre : Completes C rd b (armStart fold b) (if fold then [cst b (word 0 0 0)] else []) σ
      (fun σ' => fold = true → σ' (.n b) = 0) := by
    cases fold
    · exact ⟨σ, Ext.refl _ _ _, fun h => absurd h (by simp), fun _ _ hn => hn⟩
    · refine ⟨Function.update σ (.n b) 0, ext_update σ 0 le_rfl (by simp [armStart]), fun _ => by simp,
        fun next kret hn => ?_⟩
      simp [cst, Atom.Holds, word_zero, hn]
  have hend : (if fresh = true then e = armStart fold b + chainStride w.lx * n else True) := by
    cases fresh
    · trivial
    · simp only [↓reduceIte]
      rw [he_def, armWalksEnd, hk0 rfl, cWalks_snd_fresh]
  have htips : ∀ r', r' < n → (∃ j < e, (tips r').1 = .n j) ∧ (∃ j < e, (tips r').2 = .n j) := by
    intro r' hr'
    cases fresh
    · simp only [TipsPos, Bool.false_eq_true, ↓reduceIte] at hpos
      exact ⟨let ⟨j, hj, e'⟩ := (hpos r' (Nat.zero_le _) (by omega)).1; ⟨j, by omega, e'⟩,
        let ⟨j, hj, e'⟩ := (hpos r' (Nat.zero_le _) (by omega)).2; ⟨j, by omega, e'⟩⟩
    · simp only [TipsPos, ↓reduceIte] at hpos hend
      rw [hpos.2 r' (Nat.zero_le _) (by omega), Nat.sub_zero]
      have : chainStride w.lx * r' + chainStride w.lx ≤ chainStride w.lx * n := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr'
      have hcs : chainStride w.lx = walkSize w.lx 0 + 2 := rfl
      exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩
  have hpe : (cWalks w tips first k fresh n 0 (armStart fold b)).2 = e := rfl
  rw [cArm_fst]
  refine Completes.append (m := e + (if fresh then 2 else 0)) (P := fun σ' => (fold = true → σ' (.n b) = 0) ∧
    Ext b e σ σ' ∧ ∀ r < n, σ' (tips r).1 = σ (tips r).1 ∧ σ' (tips r).2 = σ (tips r).2) (by omega) (by omega)
    ?_ ?_ ?_
  · rw [valsList_append]
    refine NumBelow.append ?_ ?_
    · cases fold
      · exact NumBelow.nil _
      · simp only [↓reduceIte, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
        exact NumBelow.cons ⟨b, by simp only [armStart, ↓reduceIte] at he0; omega, rfl⟩ (NumBelow.nil _)
    · exact (cWalks_below (hw.mono (by omega)) _ _ _
        (fun r' _ h2 => let ⟨⟨j1, h1, e1⟩, ⟨j2, h2', e2⟩⟩ := htips r' (by omega)
          ⟨⟨j1, by omega, e1⟩, ⟨j2, by omega, e2⟩⟩) le_rfl).mono (by omega)
  · have hsb : armStart fold b ≤ b + 1 := by unfold armStart; split <;> omega
    refine Completes.append (m := armStart fold b) (P := fun σ' => fold = true → σ' (.n b) = 0) hab
      (by omega) ?_ hpre ?_
    · cases fold
      · exact NumBelow.nil _
      · simp only [↓reduceIte, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
        exact NumBelow.cons ⟨b, by simp [armStart], rfl⟩ (NumBelow.nil _)
    · intro σ' he' hp
      have hk := hw.keep he'
      have hcw := cWalks_complete (C := C) (rd := rd) (xs := xs) n 0 (armStart fold b) σ' (hw.mono hab)
        hpos' (by rw [hk.2.2.2, hmd]) (hc.congr hk) (fun r' _ h2 =>
          ⟨(hx r' (by omega)).1, (hx r' (by omega)).2.congr hk
            (he'.out ((htb r' (by omega)).1.mono le_rfl hsb))
            (he'.out ((htb r' (by omega)).2.mono le_rfl hsb))⟩)
      rw [hpe] at hcw
      refine hcw.withExt.mono le_rfl (by omega) fun σ'' h => ⟨fun hf => ?_, he'.trans h.2 hab he0,
        fun r hr => ?_⟩
      · rw [h.2.apply (Or.inl (by unfold armStart; simp [hf]))]
        exact hp hf
      · have := h.1 r (Nat.zero_le _) (by omega)
        exact ⟨this.1.trans (he'.out ((htb r hr).1.mono le_rfl hsb)),
          this.2.trans (he'.out ((htb r hr).2.mono le_rfl hsb))⟩
  · intro σ'' _ hp
    obtain ⟨hb0, hext, htips'⟩ := hp
    have hkb : ∀ {v : V}, (∃ j < b, v = .n j) → σ'' v = σ v := fun hv => hext.below hv
    refine (armTail_complete (C := C) (rd := rd) (σ := σ'') ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_).withExt.mono le_rfl
      le_rfl fun σ3 h => ⟨fun r hr => ?_, ?_, ?_⟩
    · exact let ⟨j, hj, e'⟩ := hin.1; ⟨j, by omega, e'⟩
    · exact let ⟨j, hj, e'⟩ := hin.2.1; ⟨j, by omega, e'⟩
    · exact hO.2.2.1
    · exact hO.2.2.2
    · exact let ⟨j, hj, e'⟩ := hin.2.2; ⟨j, by omega, e'⟩
    · intro hf; subst hf; simp only [armStart, ↓reduceIte] at he0; omega
    · rw [hext.out hO.1, hkb hin.1, hkb hin.2.2]; exact hf.1
    · rw [hext.out hO.2.1, hkb hin.2.1, hf.2]
      cases fold
      · rfl
      · simp only [↓reduceIte, forall_const] at hb0 ⊢; rw [hb0]
    · obtain ⟨⟨j1, h1, e1⟩, ⟨j2, h2, e2⟩⟩ := htips r hr
      exact ⟨(h.2.below ⟨j1, by omega, e1⟩).trans (htips' r hr).1,
        (h.2.below ⟨j2, by omega, e2⟩).trans (htips' r hr).2⟩
    · exact (h.2.below hO.2.2.1).trans (hext.out hO.1)
    · exact (h.2.below hO.2.2.2).trans (hext.out hO.2.1)