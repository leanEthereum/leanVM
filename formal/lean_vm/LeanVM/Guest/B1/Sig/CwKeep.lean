/-
  LeanVM.Guest.B1.Sig.CwKeep

  A group's chain starts: where its arm hints them, kept by the arm, and loaded into a valuation.
-/

module

public import LeanVM.Guest.B1.Sig.WotsGroup

/-!
# A group's chain starts

* `Completes.reload`: a block completes from a valuation changed on its own range;
* `fwd_hint_keep`: a block in single-assignment form keeps its hinted values;
* `armStart_mem`: an arm hints each chain's start;
* `grpPos`, `grpPos_spec`, `grpPos_ne`: the starts of arm `k` of a group, in the group's range
  above its base and distinct;
* `sLoad`, `gLoad`: a group's digits and starts loaded.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- **A block completes from a valuation changed on its own range.** -/
theorem Completes.reload {lo hi : Nat} {ss : List Stmt} {σ σr : Val} {Post : Val → Prop}
    (he : Ext lo hi σ σr) (h : Completes C rd lo hi ss σr Post) : Completes C rd lo hi ss σ Post :=
  let ⟨σ', he', hp, hh⟩ := h
  ⟨σ', he.comp he', hp, hh⟩

theorem hint_mem_outs : ∀ {ss : List Stmt} {s : String} {vs : List V},
    Stmt.atom (.hint (.witness s (.stack vs))) ∈ ss → ∀ v ∈ vs, v ∈ outsList ss
  | [], _, _, h, _, _ => absurd h (by simp)
  | .atom a :: ss, s, vs, h, v, hv => by
      simp only [outsList, List.mem_append]
      rcases List.mem_cons.mp h with e | h
      · cases e
        exact Or.inl (by simpa [aOuts] using hv)
      · exact Or.inr (hint_mem_outs h v hv)
  | .ite .. :: ss, _, _, h, v, hv | .match_ .. :: ss, _, _, h, v, hv | .call .. :: ss, _, _, h, v, hv
  | .callIf .. :: ss, _, _, h, v, hv | .dispatch .. :: ss, _, _, h, v, hv | .ret _ :: ss, _, _, h, v, hv => by
      exact hint_mem_outs ((List.mem_cons.mp h).resolve_left (by simp)) v hv

/-- **A block in single-assignment form keeps its hinted values.** -/
theorem fwd_hint_keep : ∀ (ss : List Stmt) (σ : Val), SSA ss → ∀ {s : String} {vs : List V},
    Stmt.atom (.hint (.witness s (.stack vs))) ∈ ss → ∀ v ∈ vs, fwd ss σ v = σ v
  | [], _, _, _, _, h, _, _ => absurd h (by simp)
  | .atom a :: ss, σ, h, s, vs, hm, v, hv => by
      obtain ⟨-, -, hl, hs⟩ := h
      simp only [fwd]
      rcases List.mem_cons.mp hm with e | hm
      · cases e
        exact fwd_of_not_mem ss _ fun ho => hl v ho (by
          simp [Atom.vals, Hint.vals, Dest.vals, hv])
      · rw [fwd_hint_keep ss _ hs hm v hv]
        exact fwdA_of_not_mem σ a fun ho => hl v (hint_mem_outs hm v hv) (outs_sub_vals a v ho)
  | .ite .. :: _, _, h, _, _, _, _, _ | .match_ .. :: _, _, h, _, _, _, _, _
  | .call .. :: _, _, h, _, _, _, _, _ | .callIf .. :: _, _, h, _, _, _, _, _
  | .dispatch .. :: _, _, h, _, _, _, _, _ | .ret _ :: _, _, h, _, _, _, _, _ => h.elim

theorem walkStart_mem (W : WotsT) (i : Nat) (slot : Nat → Nat) (stride d b : Nat) :
    hintW "chain_starts" [walkStartV slot d b] ∈ walkT W i slot stride d b := by
  unfold walkT walkStartV
  split <;> simp

/-- **An arm hints each chain's start.** -/
theorem armStart_mem (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k b : Nat) {t : Nat} (ht : t < n) :
    hintW "chain_starts" [armStart W slots fold k b t] ∈
      (armT W slots first n fold prodIn encIn prodOut encOut k b).1 := by
  have hw := walkStart_mem W (first + t) (slots t) (if k = 0 then W.size + 1 else W.size)
    (k / 4 ^ t % 4) (walkBase (if k = 0 then W.size + 1 else W.size) k 0 t (if fold then b + 1 else b))
  have hm := mem_walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0
    (if fold then b + 1 else b) t ht _ (by simpa using hw)
  unfold armT armStart
  dsimp only
  by_cases hk : k = 0 <;> simp only [hk, ↓reduceIte, List.mem_append] at hm ⊢ <;> exact Or.inl (Or.inr hm)

/-! ## The starts of a group -/

/-- Chain `t`'s start in arm `k` of a group from base `b`. -/
def grpPos (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b k t : Nat) : V :=
  armStart W (slotsT W fold b) fold k (armB W first n fold prodIn encIn b k) t

theorem walkEnd_lt (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b k : Nat) :
    walkBase (if k = 0 then W.size + 1 else W.size) k 0 n
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k) <
      armB W first n fold prodIn encIn b (k + 1) := by
  by_cases hk : k = 0
  · subst hk
    rw [armB_succ]
    simp only [armNext, armT_snd, ↓reduceIte]
    omega
  · rw [armB_next_pos W first n fold prodIn encIn b k hk]
    simp only [hk, ↓reduceIte]
    omega

theorem walkBase_lt_succ (S k a t : Nat) (hd : k / 4 ^ t % 4 ≠ 3) :
    walkBase S k 0 t a < walkBase S k 0 (t + 1) a := by
  rw [walkBase_succ]
  simp only [walkSize, dig, hd, ↓reduceIte]
  omega

/-- **Where arm `k` hints chain `t`'s start**: in the group's range above its base, the tip's slot
at digit `3`, else the walk's base. -/
theorem grpPos_spec (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b k t : Nat)
    (hk : k < 4 ^ n) (ht : t < n) :
    ∃ j, grpPos W first n fold prodIn encIn b k t = .n j ∧ b + 6 ≤ j ∧
      j < armB W first n fold prodIn encIn b (4 ^ n) ∧
      (k / 4 ^ t % 4 = 3 → k ≠ 0 ∧ slotsT W fold b t 2 + 1 ≤ groupStart fold b + chainStride W * n ∧
        j = slotsT W fold b t 2) ∧
      (k / 4 ^ t % 4 ≠ 3 → j = walkBase (if k = 0 then W.size + 1 else W.size) k 0 t
        (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)) := by
  have ha : b + 6 ≤ armB W first n fold prodIn encIn b k := by
    rw [← armB_zero W first n fold prodIn encIn b]
    exact armB_mono W first n fold prodIn encIn b (Nat.zero_le _)
  have hend : armB W first n fold prodIn encIn b (k + 1) ≤ armB W first n fold prodIn encIn b (4 ^ n) :=
    armB_mono W first n fold prodIn encIn b (by omega)
  have h1 : armB W first n fold prodIn encIn b 1 ≤ armB W first n fold prodIn encIn b (4 ^ n) :=
    armB_mono W first n fold prodIn encIn b (by omega)
  rw [armB_one] at h1
  have hsl := slot_bounds W fold b t 2 (by norm_num)
  have hst : chainStride W * (t + 1) ≤ chainStride W * n := Nat.mul_le_mul_left _ ht
  have hgs : b + 6 ≤ groupStart fold b := by rw [groupStart_eq]; split <;> omega
  have hwe := walkEnd_lt W first n fold prodIn encIn b k
  have hwl := walkBase_le (if k = 0 then W.size + 1 else W.size) k
    (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)
    (show t + 1 ≤ n from ht)
  have ha' : armB W first n fold prodIn encIn b k ≤
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k) := by
    split <;> omega
  unfold grpPos armStart walkStartV
  by_cases hd : k / 4 ^ t % 4 = 3
  · have hk0 : k ≠ 0 := by rintro rfl; simp at hd
    simp only [hd, ↓reduceIte]
    exact ⟨_, rfl, by omega, by omega, fun _ => ⟨hk0, by omega, rfl⟩, fun h => absurd rfl h⟩
  · simp only [hd, ↓reduceIte]
    have hlt := walkBase_lt_succ (if k = 0 then W.size + 1 else W.size) k
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k) t hd
    have hb0 := walkBase_le (if k = 0 then W.size + 1 else W.size) k
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)
      (Nat.zero_le t)
    simp only [walkBase] at hb0
    exact ⟨_, rfl, by omega, by omega, fun h => h.elim, fun _ => rfl⟩

/-- **An arm's starts are distinct.** -/
theorem grpPos_ne {W : WotsT} {first n : Nat} {fold : Bool} {prodIn encIn : V} {b k t t' : Nat}
    (hk : k < 4 ^ n) (ht : t < t') (ht' : t' < n) :
    grpPos W first n fold prodIn encIn b k t ≠ grpPos W first n fold prodIn encIn b k t' := by
  obtain ⟨j, e, -, -, h3, h4⟩ := grpPos_spec W first n fold prodIn encIn b k t hk (by omega)
  obtain ⟨j', e', -, -, h3', h4'⟩ := grpPos_spec W first n fold prodIn encIn b k t' hk ht'
  rw [e, e']
  intro hj
  simp only [V.mk.injEq, true_and] at hj
  subst hj
  have ha' : armB W first n fold prodIn encIn b k ≤
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k) := by
    split <;> omega
  by_cases hd : k / 4 ^ t % 4 = 3 <;> by_cases hd' : k / 4 ^ t' % 4 = 3
  · obtain ⟨-, -, e1⟩ := h3 hd
    obtain ⟨-, -, e2⟩ := h3' hd'
    have := (slot_bounds W fold b t 2 (by norm_num)).2
    have := (slot_bounds W fold b t' 2 (by norm_num)).1
    have := chain_le W fold b ht
    omega
  · obtain ⟨hk0, hs, e1⟩ := h3 hd
    have e2 := h4' hd'
    have hb0 := walkBase_le (if k = 0 then W.size + 1 else W.size) k
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)
      (Nat.zero_le t')
    simp only [walkBase] at hb0
    have := armB_pos W first n fold prodIn encIn b hk0
    omega
  · obtain ⟨hk0, hs, e1⟩ := h3' hd'
    have e2 := h4 hd
    have hb0 := walkBase_le (if k = 0 then W.size + 1 else W.size) k
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)
      (Nat.zero_le t)
    simp only [walkBase] at hb0
    have := armB_pos W first n fold prodIn encIn b hk0
    omega
  · have e1 := h4 hd
    have e2 := h4' hd'
    have := walkBase_lt_succ (if k = 0 then W.size + 1 else W.size) k
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k) t hd
    have := walkBase_le (if k = 0 then W.size + 1 else W.size) k
      (if fold then armB W first n fold prodIn encIn b k + 1 else armB W first n fold prodIn encIn b k)
      (show t + 1 ≤ t' from ht)
    omega

/-! ## Loading a group -/

/-- Values `vals t` loaded at `pos t`, `t < m`. -/
def sLoad (pos : Nat → V) (vals : Nat → E) (σ : Val) : Nat → Val
  | 0 => σ
  | m + 1 => Function.update (sLoad pos vals σ m) (pos m) (vals m)

theorem sLoad_other (pos : Nat → V) (vals : Nat → E) (σ : Val) :
    ∀ (m : Nat) {v : V}, (∀ t < m, v ≠ pos t) → sLoad pos vals σ m v = σ v
  | 0, _, _ => rfl
  | m + 1, v, h => by
      simp only [sLoad]
      rw [Function.update_of_ne (h m (by omega)), sLoad_other pos vals σ m fun t ht => h t (by omega)]

theorem sLoad_at (pos : Nat → V) (vals : Nat → E) (σ : Val) :
    ∀ (m : Nat), (∀ t t', t < t' → t' < m → pos t ≠ pos t') → ∀ t < m, sLoad pos vals σ m (pos t) = vals t
  | 0, _, _, ht => absurd ht (by omega)
  | m + 1, hne, t, ht => by
      simp only [sLoad]
      by_cases e : t = m
      · subst e
        exact Function.update_self ..
      · rw [Function.update_of_ne (hne t m (by omega) (by omega)),
          sLoad_at pos vals σ m (fun a b h1 h2 => hne a b h1 (by omega)) t (by omega)]

/-- A group's digits `k` loaded at `d` and its arm's starts `vals`, its arms from `b`. -/
def gLoadD (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (d b k : Nat) (vals : Nat → E)
    (σ : Val) : Val :=
  Function.update (sLoad (grpPos W first n fold prodIn encIn b k) vals σ n) (.n d) (ofK
      (addressOfIndex k))

/-- **A group's load**: its digits at `d`, its starts, changes in its range only. -/
theorem gLoadD_spec (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (d b k : Nat)
    (vals : Nat → E) (σ : Val) (hk : k < 4 ^ n) (hdb : d ≤ b) :
    Ext d (armB W first n fold prodIn encIn b (4 ^ n)) σ (gLoadD W first n fold prodIn encIn d b k vals σ) ∧
      gLoadD W first n fold prodIn encIn d b k vals σ (.n d) = ofK (addressOfIndex k) ∧
      ∀ t < n, gLoadD W first n fold prodIn encIn d b k vals σ (grpPos W first n fold prodIn encIn b k t) =
        vals t := by
  have hne : ∀ t < n, grpPos W first n fold prodIn encIn b k t ≠ .n d := by
    intro t ht e
    obtain ⟨j, ej, hj, -⟩ := grpPos_spec W first n fold prodIn encIn b k t hk ht
    rw [ej] at e
    simp only [V.mk.injEq, true_and] at e
    omega
  have hb5 : b + 6 ≤ armB W first n fold prodIn encIn b (4 ^ n) := by
    rw [← armB_zero W first n fold prodIn encIn b]
    exact armB_mono W first n fold prodIn encIn b (Nat.zero_le _)
  refine ⟨fun v hv => ?_, Function.update_self .., fun t ht => ?_⟩
  · unfold gLoadD
    rw [Function.update_of_ne (hv d le_rfl (by omega))]
    refine sLoad_other _ _ σ n fun t ht e => ?_
    obtain ⟨j, ej, h1, h2, -⟩ := grpPos_spec W first n fold prodIn encIn b k t hk ht
    rw [ej] at e
    exact hv j (by omega) h2 e
  · unfold gLoadD
    rw [Function.update_of_ne (hne t ht)]
    exact sLoad_at _ vals σ n (fun a c h1 h2 => grpPos_ne hk h1 h2) t ht

/-- A group's digits `k` and its arm's starts `vals` loaded. -/
def gLoad (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b k : Nat) (vals : Nat → E)
    (σ : Val) : Val :=
  gLoadD W first n fold prodIn encIn b b k vals σ

/-- **A group's load**: its digits at the base, its starts, changes in its range only. -/
theorem gLoad_spec (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b k : Nat)
    (vals : Nat → E) (σ : Val) (hk : k < 4 ^ n) :
    Ext b (armB W first n fold prodIn encIn b (4 ^ n)) σ (gLoad W first n fold prodIn encIn b k vals σ) ∧
      gLoad W first n fold prodIn encIn b k vals σ (.n b) = ofK (addressOfIndex k) ∧
      ∀ t < n, gLoad W first n fold prodIn encIn b k vals σ (grpPos W first n fold prodIn encIn b k t) =
        vals t :=
  gLoadD_spec W first n fold prodIn encIn b b k vals σ hk le_rfl

end
end LeanVM.Guest.B1.Sig
