/-
  LeanVM.Guest.Backend.Sound.Obl.CheckSound

  The analysis `chk` is sound: it gives the back end's obligations, and the postconditions it
  checks hold of the located call relation.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.Check
public import LeanVM.Guest.Backend.Sound.Spec
public import LeanVM.Guest.CoreLemmas
public import LeanVM.Guest.CoreLoc
public import LeanVM.Parameters.Generator

/-!
# The analysis is sound

* `bnd_sound`: a bound the analysis finds holds, on a memory of at most `2^32` words, of every
  valuation satisfying the hypotheses before the site (`CtxHolds`);
* `oblList_of_chk`: a block the analysis accepts has its obligations (`OblList`), for every call
  relation whose calls meet the callees' postconditions (`SigPost`) and every precondition `U`
  the table's (`SigPre`) implies;
* `holdsList_post`: a block the analysis accepts, holding, returns words meeting the function's
  postcondition;
* `post_relL`: in a program whose every function the analysis accepts, the located call
  relation meets every postcondition, its frames meeting the preconditions.
-/

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## What the table and the hypotheses mean -/

/-- `v = g^e` with `e < n`. -/
def Bnd (v : E) (n : Nat) : Prop := ∃ e < n, v = ofK (addressOfIndex e)

/-- The word at `p · g^c` is `g^e` with `e < n`. -/
def MemB (rd : Reader) (p : E) (c n : Nat) : Prop :=
  ∃ e < n, LoadHolds rd p c (ofK (addressOfIndex e))

/-- **A signature's precondition** on argument words. -/
def SigPre (rd : Reader) (s : Sig) (args : List E) : Prop :=
  (∀ p ∈ s.pre, p.1 < args.length → Bnd (args.getD p.1 0) p.2) ∧
    ∀ m ∈ s.mem, m.1 < args.length → MemB rd (args.getD m.1 0) m.2.1 m.2.2

/-- **A signature's postcondition** on a call's argument and return words. -/
def SigPost (s : Sig) (cells : List E) : Prop :=
  ∀ p ∈ s.post, p.1 < cells.length → Bnd (cells.getD p.1 0) p.2

/-- What a function's postcondition `w` says of its returned words `rs`: its frame cells past the
first two, the parameters' words then `rs`, are bounded as `w.post` says. -/
def SigPostOf (w : Want) (σ : Val) (rs : List E) : Prop :=
  ∀ p ∈ w.post, p.1 < (w.pars.map σ ++ rs).length → Bnd ((w.pars.map σ ++ rs).getD p.1 0) p.2

/-- The powers the table lists are right. -/
def PowsOk (T : Tab) : Prop := ∀ p ∈ T.pows, K.ofBits p.1 = addressOfIndex p.2

/-- What a hypothesis says of a valuation. -/
def Hyp.Holds (T : Tab) (rd : Reader) (σ : Val) : Hyp → Prop
  | .atom a => a.Holds rd σ
  | .arm x j => σ x = ofK (addressOfIndex j)
  | .ret f args rets => SigPost (T.sig f) ((args ++ rets).map σ)
  | .pre x n => Bnd (σ x) n
  | .mem x c n => MemB rd (σ x) c n

/-- Every hypothesis holds. -/
def CtxHolds (T : Tab) (rd : Reader) (σ : Val) (ctx : List Hyp) : Prop :=
  ∀ h ∈ ctx, h.Holds T rd σ

/-! ## Words -/

theorem ofBits_toNat (x : K) : K.ofBits x.toBitVec.toNat = x := by
  simp [K.ofBits]

theorem ofBits_zero : K.ofBits 0 = 0 := by decide

theorem ofK_one' : ofK 1 = 1 := map_one (algebraMap K E)

theorem gp_zero : ofK (addressOfIndex 0) = 1 := by rw [addressOfIndex, pow_zero, ofK_one']

theorem lowBits_spec {c : E} {a : Nat} (h : lowBits c = some a) : c = ofK (K.ofBits a) := by
  unfold lowBits at h
  split at h
  · rename_i h1
    obtain rfl := Option.some.inj h
    have h0 : c.limb 1 = 0 := by rw [← ofBits_toNat (c.limb 1), h1, ofBits_zero]
    rw [ofBits_toNat, ofK_eq_ofLimbs, ← h0, ofLimbs_limb]
  · exact absurd h (by simp)

/-- `g^j` is the word `2^j` below the first reduction (`g` is the polynomial `x`). -/
theorem ofBits_two_pow : ∀ j < 64, K.ofBits (2 ^ j) = addressOfIndex j := by decide +kernel

/-- `1 + g^k` is the word `2^k + 1` for `1 ≤ k < 64`. -/
theorem ofBits_onePlus : ∀ k < 64, 1 ≤ k → K.ofBits (2 ^ k + 1) = 1 + addressOfIndex k := by
  decide +kernel

theorem log2Exact_spec {a j : Nat} (h : log2Exact a = some j) : 2 ^ j = a ∧ j < 64 := by
  simp only [log2Exact] at h
  split at h
  · rename_i hh
    obtain rfl := Option.some.inj h
    exact hh
  · exact absurd h (by simp)

theorem powOf_spec {T : Tab} (hT : PowsOk T) {c : E} {j : Nat} (h : powOf T.pows c = some j) :
    c = ofK (addressOfIndex j) := by
  unfold powOf at h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  rw [lowBits_spec ha]
  cases hl : log2Exact a with
  | some j' =>
    rw [hl] at h
    obtain rfl := Option.some.inj h
    obtain ⟨rfl, hj⟩ := log2Exact_spec hl
    rw [ofBits_two_pow j' hj]
  | none =>
    rw [hl] at h
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hm, hpa⟩ := List.find?_eq_some_iff_append.mp hp |>.imp_left id |> fun h =>
      (⟨List.mem_of_find?_eq_some hp, h.1⟩ : p ∈ T.pows ∧ _)
    rw [beq_iff_eq] at hpa
    rw [← hpa, hT p hm]

theorem oppOf_spec {c : E} {k : Nat} (h : oppOf c = some k) : c = ofK (1 + addressOfIndex k) := by
  unfold oppOf at h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  rw [lowBits_spec ha]
  split at h
  · rename_i k' hk'
    split at h
    · rename_i hh
      obtain rfl := Option.some.inj h
      obtain ⟨-, hk⟩ := log2Exact_spec hk'
      rw [← hh.2, ofBits_onePlus k' hk hh.1]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## Bounds -/

theorem minO_eq_some {a b : Option Nat} {n : Nat} (h : minO a b = some n) :
    a = some n ∨ b = some n := by
  cases a with
  | some a =>
    cases b with
    | some b =>
      simp only [minO, Option.some.injEq] at h ⊢
      omega
    | none => exact .inl h
  | none => exact .inr h

theorem foldl_minO {α : Type} (f : α → Option Nat) (P : Nat → Prop) :
    ∀ (l : List α) (o : Option Nat), (∀ n, o = some n → P n) → (∀ a ∈ l, ∀ n, f a = some n → P n) →
      ∀ n, l.foldl (fun o a => minO o (f a)) o = some n → P n
  | [], _, ho, _, n, h => ho n h
  | a :: l, _, ho, hl, n, h =>
      foldl_minO f P l _ (fun m hm => (minO_eq_some hm).elim (ho m) (hl a List.mem_cons_self m))
        (fun b hb => hl b (List.mem_cons_of_mem _ hb)) n h

section Ctx

variable {T : Tab} {rd : Reader} {σ : Val} {ctx : List Hyp}

theorem gpOf_spec (hT : PowsOk T) (hc : CtxHolds T rd σ ctx) {x : V} {j : Nat}
    (h : gpOf T ctx x = some j) : σ x = ofK (addressOfIndex j) := by
  unfold gpOf at h
  obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
  have hh := hc a ha
  rcases a with ⟨a⟩ | ⟨y, j'⟩ | _ | _ | _
  · rcases a with ⟨d, c⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals try simp only at hp
    all_goals try (simp at hp; done)
    split at hp
    · rename_i hd
      rw [beq_iff_eq] at hd
      subst hd
      exact hh.trans (powOf_spec hT hp)
    · exact absurd hp (by simp)
  · simp only at hp
    split at hp
    · rename_i hy
      rw [beq_iff_eq] at hy
      subst hy
      obtain rfl := Option.some.inj hp
      exact hh
    · exact absurd hp (by simp)
  all_goals simp at hp

theorem oppAt_spec (hc : CtxHolds T rd σ ctx) {x : V} {k : Nat} (h : oppAt ctx x = some k) :
    σ x = ofK (1 + addressOfIndex k) := by
  unfold oppAt at h
  obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
  have hh := hc a ha
  rcases a with ⟨a⟩ | _ | _ | _ | _
  · rcases a with ⟨d, c⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals try simp only at hp
    all_goals try (simp at hp; done)
    split at hp
    · rename_i hd
      rw [beq_iff_eq] at hd
      subst hd
      exact hh.trans (oppOf_spec hp)
    · exact absurd hp (by simp)
  all_goals simp at hp

theorem isBool_spec (hc : CtxHolds T rd σ ctx) {x : V} (h : isBool ctx x = true) :
    σ x = 0 ∨ σ x = 1 := by
  unfold isBool at h
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  have hh := hc a ha
  rcases a with ⟨a⟩ | _ | _ | _ | _
  · rcases a with _ | _ | ⟨d, a, b⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals try simp only at hp
    all_goals try (simp at hp; done)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
    exact IsIdempotentElem.iff_eq_zero_or_one.mp hh.symm
  all_goals simp at hp

theorem bscOf_spec (hc : CtxHolds T rd σ ctx) {u : V} {k : Nat} (h : bscOf ctx u = some k) :
    σ u = 0 ∨ σ u = ofK (1 + addressOfIndex k) := by
  unfold bscOf at h
  obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
  have hh := hc a ha
  rcases a with ⟨a⟩ | _ | _ | _ | _
  · rcases a with _ | _ | ⟨d, a, b⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals try simp only at hp
    all_goals try (simp at hp; done)
    split at hp
    · rename_i hd
      rw [beq_iff_eq] at hd
      subst hd
      have key : ∀ {p q : V}, isBool ctx p = true → oppAt ctx q = some k →
          σ p * σ q = 0 ∨ σ p * σ q = ofK (1 + addressOfIndex k) := by
        intro p q hb ho
        rw [oppAt_spec hc ho]
        rcases isBool_spec hc hb with h0 | h1
        · exact .inl (by rw [h0, zero_mul])
        · exact .inr (by rw [h1, one_mul])
      have hh : σ d = σ a * σ b := hh
      rw [hh]
      cases h1 : isBool ctx a with
      | true =>
        cases h2 : oppAt ctx b with
        | some k' =>
          rw [h1, h2] at hp
          obtain rfl := Option.some.inj hp
          exact key h1 h2
        | none =>
          rw [h1, h2] at hp
          simp only [ite_true, Option.none_or] at hp
          split at hp
          · rename_i hb
            rw [mul_comm]
            exact key hb hp
          · exact absurd hp (by simp)
      | false =>
        rw [h1] at hp
        simp only [Bool.false_eq_true, ite_false, Option.none_or] at hp
        split at hp
        · rename_i hb
          rw [mul_comm]
          exact key hb hp
        · exact absurd hp (by simp)
    · exact absurd hp (by simp)
  all_goals simp at hp

theorem memOf_spec (hc : CtxHolds T rd σ ctx) {x : V} {c n : Nat} (h : memOf ctx x c = some n) :
    MemB rd (σ x) c n := by
  unfold memOf at h
  refine foldl_minO _ (fun n => MemB rd (σ x) c n) ctx none (by simp) ?_ n h
  intro a ha m hm
  have hh := hc a ha
  rcases a with _ | _ | _ | _ | ⟨y, c', n'⟩
  all_goals try simp only at hm
  all_goals try (simp at hm; done)
  split at hm
  · rename_i hy
    simp only [Bool.and_eq_true, beq_iff_eq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    obtain rfl := Option.some.inj hm
    exact hh
  · exact absurd hm (by simp)

theorem getD_map_lt {l : List V} {i : Nat} (h : i < l.length) :
    (l.map σ).getD i 0 = σ (l.getD i default) := by
  simp [List.getD_eq_getElem?_getD, h]

theorem postOf_spec {f : String} {cells : List V} {x : V} {n : Nat}
    (hs : SigPost (T.sig f) (cells.map σ)) (h : postOf T f cells x = some n) : Bnd (σ x) n := by
  unfold postOf at h
  refine foldl_minO _ (fun n => Bnd (σ x) n) _ none (by simp) ?_ n h
  intro p hp m hm
  split at hm
  · rename_i hx
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
    obtain rfl := Option.some.inj hm
    have := hs p hp (by simpa using hx.2)
    rwa [getD_map_lt hx.2, hx.1] at this
  · exact absurd hm (by simp)

/-- A range check against `g^J`, `J < 2^32`, on a memory of at most `2^32` words bounds its
operand by `J + 1`: both operands read memory, so they are `g^i`, `g^i'` with `i, i' < 2^32`,
and `i + i' = J` as `g` has order `2^64 - 1`. -/
theorem rangeCheck_bnd {κ : ℕ} (hκ : κ ≤ 32) {L : MemoryImage κ} {x y t1 t2 k : V} {J : Nat}
    (hJ : J < 2 ^ 32) (h : (Atom.rangeCheck x y t1 t2 k).Holds L.read σ)
    (hk : σ k = ofK (addressOfIndex J)) : Bnd (σ x) (J + 1) := by
  obtain ⟨⟨hx, h1⟩, hm, ⟨hy, h2⟩⟩ := h
  have hκ64 : κ < 64 := by omega
  have h32 : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hκ
  rw [addressOfIndex, pow_zero, mul_one] at h1 h2
  obtain ⟨i, hi, -⟩ := (read_some_iff hκ64 L _ _).mp h1
  obtain ⟨i', hi', -⟩ := (read_some_iff hκ64 L _ _).mp h2
  have ex : σ x = ofK (addressOfIndex i) := by rw [eq_ofK_limb hx, hi]
  have ey : σ y = ofK (addressOfIndex i') := by rw [eq_ofK_limb hy, hi']
  rw [hk, ex, ey, ← ofK_mul, addressOfIndex, addressOfIndex, ← pow_add] at hm
  have hij := gpow_injOn (by simp only [Set.mem_Iio]; omega)
    (by have := i.isLt; have := i'.isLt; simp only [Set.mem_Iio]; omega) (ofK_injective hm)
  exact ⟨i, by omega, ex⟩

variable {κ : ℕ} {L : MemoryImage κ}

/-- **A bound the analysis finds holds.** -/
theorem bnd_sound (hT : PowsOk T) (hκ : κ ≤ 32) (hc : CtxHolds T L.read σ ctx) :
    ∀ (fuel : Nat) {x : V} {n : Nat}, bnd T fuel ctx x = some n → Bnd (σ x) n
  | fuel, x, n, h => by
    rw [bnd] at h
    refine foldl_minO _ (fun n => Bnd (σ x) n) ctx none (by simp) ?_ n h
    intro a ha m hm
    have hh := hc a ha
    rcases a with ⟨a⟩ | ⟨y, j⟩ | ⟨f, as, rs⟩ | ⟨y, n'⟩ | _
    · rcases a with ⟨d, c⟩ | ⟨d, a, b⟩ | ⟨d, a, b⟩ | ⟨d, s⟩ | ⟨d, p, off⟩ | _ | _ |
        ⟨y, yy, t1, t2, k⟩ | _ | _ | _ | _ | _
      all_goals try simp only at hm
      all_goals try (simp at hm; done)
      · -- a constant
        split at hm
        · rename_i hd
          rw [beq_iff_eq] at hd
          subst hd
          obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hm
          exact ⟨j, by omega, hh.trans (powOf_spec hT hj)⟩
        · exact absurd hm (by simp)
      · -- `1 + b·(1 + g^k)`
        split at hm
        · rename_i hd
          rw [beq_iff_eq] at hd
          subst hd
          have hh : σ d = σ a + σ b := hh
          have key : ∀ {p q : V}, gpOf T ctx p = some 0 → ∀ {k : Nat}, bscOf ctx q = some k →
              Bnd (σ p + σ q) (k + 1) := by
            intro p q hp k hq
            rw [gpOf_spec hT hc hp, gp_zero]
            rcases bscOf_spec hc hq with h0 | h1
            · exact ⟨0, by omega, by rw [h0, add_zero, gp_zero]⟩
            · refine ⟨k, by omega, ?_⟩
              rw [h1, ofK_add, ofK_one', ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
          split at hm
          · rename_i ha'
            obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hm
            rw [hh]
            exact key (beq_iff_eq.mp ha') hk
          · split at hm
            · rename_i hb'
              obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hm
              rw [hh, add_comm]
              exact key (beq_iff_eq.mp hb') hk
            · exact absurd hm (by simp)
        · exact absurd hm (by simp)
      · -- a product
        cases fuel with
        | zero => exact absurd hm (by simp)
        | succ f =>
          simp only at hm
          split at hm
          · rename_i hd
            rw [beq_iff_eq] at hd
            subst hd
            split at hm
            · rename_i n₁ n₂ h₁ h₂
              obtain rfl := Option.some.inj hm
              obtain ⟨e₁, he₁, ha⟩ := bnd_sound hT hκ hc f h₁
              obtain ⟨e₂, he₂, hb⟩ := bnd_sound hT hκ hc f h₂
              have hh : σ d = σ a * σ b := hh
              refine ⟨e₁ + e₂, by omega, ?_⟩
              rw [hh, ha, hb, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, pow_add]
            · exact absurd hm (by simp)
          · exact absurd hm (by simp)
      · -- a copy
        cases fuel with
        | zero => exact absurd hm (by simp)
        | succ f =>
          simp only at hm
          have hh : σ d = σ s := hh
          split at hm
          · rename_i hd
            rw [beq_iff_eq] at hd
            subst hd
            rw [hh]
            exact bnd_sound hT hκ hc f hm
          · split at hm
            · rename_i hs
              rw [beq_iff_eq] at hs
              subst hs
              rw [← hh]
              exact bnd_sound hT hκ hc f hm
            · exact absurd hm (by simp)
      · -- a word read where the precondition bounds memory
        split at hm
        · rename_i hd
          rw [beq_iff_eq] at hd
          subst hd
          obtain ⟨e, he, hl⟩ := memOf_spec hc hm
          refine ⟨e, he, ?_⟩
          exact Option.some.inj (hh.2.symm.trans hl.2)
        · exact absurd hm (by simp)
      · -- a range check
        split at hm
        · rename_i hd
          rw [beq_iff_eq] at hd
          subst hd
          split at hm
          · rename_i j hj
            split at hm
            · rename_i hJ
              obtain rfl := Option.some.inj hm
              exact rangeCheck_bnd hκ hJ hh (gpOf_spec hT hc hj)
            · exact absurd hm (by simp)
          · exact absurd hm (by simp)
        · exact absurd hm (by simp)
    · -- an arm
      simp only at hm
      split at hm
      · rename_i hy
        rw [beq_iff_eq] at hy
        subst hy
        obtain rfl := Option.some.inj hm
        exact ⟨j, by omega, hh⟩
      · exact absurd hm (by simp)
    · -- a callee's postcondition
      simp only at hm
      exact postOf_spec hh hm
    · -- the precondition
      simp only at hm
      split at hm
      · rename_i hy
        rw [beq_iff_eq] at hy
        subst hy
        obtain rfl := Option.some.inj hm
        exact hh
      · exact absurd hm (by simp)
    · simp at hm

theorem leO_bnd (hT : PowsOk T) (hκ : κ ≤ 32) (hc : CtxHolds T L.read σ ctx) {x : V} {n : Nat}
    (h : leO (bnd T fuel0 ctx x) n = true) : Bnd (σ x) n := by
  unfold leO at h
  split at h
  · rename_i m hm
    obtain ⟨e, he, hx⟩ := bnd_sound hT hκ hc fuel0 hm
    exact ⟨e, by simp only [Nat.ble_eq] at h; omega, hx⟩
  · exact absurd h (by simp)

theorem leO_mem (hc : CtxHolds T L.read σ ctx) {x : V} {c n : Nat}
    (h : leO (memOf ctx x c) n = true) : MemB L.read (σ x) c n := by
  unfold leO at h
  split at h
  · rename_i m hm
    obtain ⟨e, he, hx⟩ := memOf_spec hc hm
    exact ⟨e, by simp only [Nat.ble_eq] at h; omega, hx⟩
  · exact absurd h (by simp)

/-- **A call the analysis accepts meets its callee's precondition**, and its callee asks nothing
beyond its signature. -/
theorem callOk_sound (hT : PowsOk T) (hκ : κ ≤ 32) (hc : CtxHolds T L.read σ ctx) {f : String}
    {args : List V} (h : callOk T ctx f args = true) :
    f ∉ T.xs ∧ SigPre L.read (T.sig f) (args.map σ) := by
  simp only [callOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hx, hp⟩, hm⟩ := h
  refine ⟨fun hf => absurd (List.contains_iff_mem.mpr hf) (by rw [hx]; decide),
    fun p hp' _ => ?_, fun m hm' _ => ?_⟩
  · obtain ⟨hl, hb⟩ := hp p hp'
    rw [getD_map_lt hl]
    exact leO_bnd hT hκ hc hb
  · obtain ⟨hl, hb⟩ := hm m hm'
    rw [getD_map_lt hl]
    exact leO_mem hc hb

theorem entry_holds {params : List V} {s : Sig} (h : SigPre rd s (params.map σ)) :
    CtxHolds T rd σ (entry params s) := by
  intro a ha
  simp only [entry, List.mem_append, List.mem_filterMap, Option.map_eq_some_iff] at ha
  rcases ha with ⟨p, hp, v, hv, rfl⟩ | ⟨m, hm, v, hv, rfl⟩
  · obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    have := h.1 p hp (by simpa using hl)
    show Bnd _ _
    simpa [List.getD_eq_getElem?_getD, hl] using this
  · obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    have := h.2 m hm (by simpa using hl)
    show MemB _ _ _ _
    simpa [List.getD_eq_getElem?_getD, hl] using this

end Ctx

/-! ## Obligations -/

section Obl

variable {T : Tab} {κ : ℕ} {L : MemoryImage κ} {σ : Val} {C : CallRel}
  {U : String → List E → Prop}

theorem bnd_arm {x : V} {n : Nat} (h : Bnd (σ x) n) :
    ∃ j, j < n ∧ σ x = ofK (addressOfIndex j) := h

mutual
/-- **A statement the analysis accepts has its obligations**, the hypotheses before it holding. -/
theorem obl_of_chk (hT : PowsOk T) (hκ : κ ≤ 32)
    (hU : ∀ f a, f ∉ T.xs → SigPre L.read (T.sig f) a → U f a)
    (hpost : ∀ f a r, C f a r → SigPost (T.sig f) (a ++ r)) (w : Want) :
    ∀ (s : Stmt) (ctx : List Hyp) (N : Prop), CtxHolds T L.read σ ctx → chkS T w ctx s = true →
      (CtxHolds T L.read σ (after ctx s) → N) → Obl C U L.read σ s N
  | .atom a, ctx, _, hc, _, hN => fun ha => hN fun h hh => by
      rcases List.mem_cons.mp hh with rfl | hh
      · exact ha
      · exact hc h hh
  | .ite _ z n, ctx, N, hc, h, hN => by
      simp only [chkS, Bool.and_eq_true] at h
      exact fun _ => ⟨fun _ => oblList_of_chk hT hκ hU hpost w z ctx N hc h.1 (hN hc),
        fun _ => oblList_of_chk hT hκ hU hpost w n ctx N hc h.2 (hN hc)⟩
  | .match_ x arms, ctx, N, hc, h, hN => by
      simp only [chkS, Bool.and_eq_true] at h
      exact ⟨leO_bnd hT hκ hc h.1, oblArms_of_chk hT hκ hU hpost w x arms 0 ctx N hc h.2 (hN hc)⟩
  | .call f args rets, ctx, N, hc, h, hN => by
      simp only [chkS] at h
      obtain ⟨hx, hp⟩ := callOk_sound hT hκ hc h
      refine ⟨hU f _ hx hp, fun hC => hN fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · show SigPost _ _
        rw [List.map_append]
        exact hpost _ _ _ hC
      · exact hc a ha
  | .callIf _ f args, ctx, N, hc, h, hN => by
      simp only [chkS] at h
      obtain ⟨hx, hp⟩ := callOk_sound hT hκ hc h
      exact fun _ => ⟨fun _ => hU f _ hx hp, fun _ => hN hc⟩
  | .dispatch x fs args rets, ctx, N, hc, h, hN => by
      simp only [chkS, Bool.and_eq_true, List.all_eq_true] at h
      refine ⟨leO_bnd hT hκ hc h.1, fun j hj _ => ?_, fun _ => hN hc⟩
      obtain ⟨hx, hp⟩ := callOk_sound hT hκ hc (h.2 fs[j] (List.getElem_mem hj))
      exact hU _ _ hx hp
  | .ret _, _, _, _, _, _ => trivial

/-- **A block the analysis accepts has its obligations.** -/
theorem oblList_of_chk (hT : PowsOk T) (hκ : κ ≤ 32)
    (hU : ∀ f a, f ∉ T.xs → SigPre L.read (T.sig f) a → U f a)
    (hpost : ∀ f a r, C f a r → SigPost (T.sig f) (a ++ r)) (w : Want) :
    ∀ (ss : List Stmt) (ctx : List Hyp) (N : Prop), CtxHolds T L.read σ ctx →
      chkL T w ctx ss = true → N → OblList C U L.read σ ss N
  | [], _, _, _, _, hN => hN
  | s :: ss, ctx, N, hc, h, hN => by
      simp only [chkL, Bool.and_eq_true] at h
      exact obl_of_chk hT hκ hU hpost w s ctx _ hc h.1
        fun hc' => oblList_of_chk hT hκ hU hpost w ss _ N hc' h.2 hN

/-- The arms of a `match` the analysis accepts have their obligations. -/
theorem oblArms_of_chk (hT : PowsOk T) (hκ : κ ≤ 32)
    (hU : ∀ f a, f ∉ T.xs → SigPre L.read (T.sig f) a → U f a)
    (hpost : ∀ f a r, C f a r → SigPost (T.sig f) (a ++ r)) (w : Want) (x : V) :
    ∀ (arms : List (List Stmt)) (j : Nat) (ctx : List Hyp) (N : Prop), CtxHolds T L.read σ ctx →
      chkA T w ctx x j arms = true → N → OblArms C U L.read σ x j arms N
  | [], _, _, _, _, _, _ => trivial
  | a :: as, j, ctx, N, hc, h, hN => by
      simp only [chkA, Bool.and_eq_true] at h
      refine ⟨fun hx => oblList_of_chk hT hκ hU hpost w a _ N ?_ h.1 hN,
        oblArms_of_chk hT hκ hU hpost w x as (j + 1) ctx N hc h.2 hN⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hx
      · exact hc b hb
end

/-- **A function the analysis accepts has its obligations** wherever its precondition holds. -/
theorem fn_obl_of_chk (hT : PowsOk T) (hκ : κ ≤ 32)
    (hU : ∀ f a, f ∉ T.xs → SigPre L.read (T.sig f) a → U f a)
    (hpost : ∀ f a r, C f a r → SigPost (T.sig f) (a ++ r)) {f : Fn} (h : chkFn T f = true)
    (hpre : SigPre L.read (T.sig f.name) (f.params.map σ)) :
    OblList C U L.read σ f.body True :=
  oblList_of_chk hT hκ hU hpost _ f.body _ True (entry_holds hpre) h trivial

end Obl

/-! ## Postconditions -/

section Post

variable {T : Tab} {κ : ℕ} {L : MemoryImage κ} {σ : Val} {C : CallRel}

mutual
/-- **A statement the analysis accepts returns words meeting the postcondition**, the hypotheses
before it holding. -/
theorem holds_post (hT : PowsOk T) (hκ : κ ≤ 32)
    (hpost : ∀ f a r, C f a r → SigPost (T.sig f) (a ++ r)) (w : Want) :
    ∀ (s : Stmt) (ctx : List Hyp) (N N' : Prop) (kret : List E → Prop), CtxHolds T L.read σ ctx →
      chkS T w ctx s = true → (CtxHolds T L.read σ (after ctx s) → N → N') →
      Stmt.Holds C L.read σ s N kret →
        Stmt.Holds C L.read σ s N' (fun rs => kret rs ∧ SigPostOf w σ rs)
  | .atom a, ctx, _, _, _, hc, _, hN, h => ⟨h.1, hN (fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h.1
      · exact hc b hb) h.2⟩
  | .ite _ z n, ctx, N, N', kret, hc, h, hN, hh => by
      simp only [chkS, Bool.and_eq_true] at h
      exact ⟨hh.1, fun h0 => holdsList_post hT hκ hpost w z ctx N N' kret hc h.1 (hN hc) (hh.2.1 h0),
        fun h0 => holdsList_post hT hκ hpost w n ctx N N' kret hc h.2 (hN hc) (hh.2.2 h0)⟩
  | .match_ x arms, ctx, N, N', kret, hc, h, hN, hh => by
      simp only [chkS, Bool.and_eq_true] at h
      exact holdsArms_post hT hκ hpost w x arms 0 ctx N N' kret hc h.2 (hN hc) hh
  | .call f args rets, ctx, _, _, _, hc, _, hN, hh => ⟨hh.1, hN (fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · show SigPost _ _
        rw [List.map_append]
        exact hpost _ _ _ hh.1
      · exact hc b hb) hh.2⟩
  | .callIf .., _, _, _, _, hc, _, hN, hh => ⟨hh.1, hh.2.1, hN hc hh.2.2⟩
  | .dispatch .., _, _, _, _, hc, _, hN, hh => ⟨hh.1, hN hc hh.2⟩
  | .ret vs, ctx, _, _, _, hc, h, _, hh => by
      refine ⟨hh, fun p hp hl => ?_⟩
      simp only [chkS, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hl', hb⟩ := h p hp
      have := leO_bnd hT hκ hc hb
      rwa [← getD_map_lt (σ := σ) hl', List.map_append] at this

/-- A block the analysis accepts returns words meeting the postcondition. -/
theorem holdsList_post (hT : PowsOk T) (hκ : κ ≤ 32)
    (hpost : ∀ f a r, C f a r → SigPost (T.sig f) (a ++ r)) (w : Want) :
    ∀ (ss : List Stmt) (ctx : List Hyp) (N N' : Prop) (kret : List E → Prop),
      CtxHolds T L.read σ ctx → chkL T w ctx ss = true → (N → N') →
      Stmt.HoldsList C L.read σ ss N kret →
        Stmt.HoldsList C L.read σ ss N' (fun rs => kret rs ∧ SigPostOf w σ rs)
  | [], _, _, _, _, _, _, hN, hh => hN hh
  | s :: ss, ctx, N, N', kret, hc, h, hN, hh => by
      simp only [chkL, Bool.and_eq_true] at h
      exact holds_post hT hκ hpost w s ctx _ _ kret hc h.1
        (fun hc' => holdsList_post hT hκ hpost w ss _ N N' kret hc' h.2 hN) hh

/-- The arms of a `match` the analysis accepts return words meeting the postcondition. -/
theorem holdsArms_post (hT : PowsOk T) (hκ : κ ≤ 32)
    (hpost : ∀ f a r, C f a r → SigPost (T.sig f) (a ++ r)) (w : Want) (x : V) :
    ∀ (arms : List (List Stmt)) (j : Nat) (ctx : List Hyp) (N N' : Prop) (kret : List E → Prop),
      CtxHolds T L.read σ ctx → chkA T w ctx x j arms = true → (N → N') →
      Stmt.HoldsArms C L.read σ x j arms N kret →
        Stmt.HoldsArms C L.read σ x j arms N' (fun rs => kret rs ∧ SigPostOf w σ rs)
  | [], _, _, _, _, _, _, _, _, hh => hh
  | a :: as, j, ctx, N, N', kret, hc, h, hN, hh => by
      simp only [chkA, Bool.and_eq_true] at h
      rcases hh with ⟨hx, ha⟩ | ha
      · refine .inl ⟨hx, holdsList_post hT hκ hpost w a _ N N' kret ?_ h.1 hN ha⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hx
        · exact hc b hb
      · exact .inr (holdsArms_post hT hκ hpost w x as (j + 1) ctx N N' kret hc h.2 hN ha)
end

end Post

end
end LeanVM.Guest.Backend.Obl
