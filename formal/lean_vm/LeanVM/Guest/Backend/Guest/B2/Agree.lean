/-
  LeanVM.Guest.Backend.Guest.B2.Agree

  A decidable comparison of a function's values' places with a table of frame cells, and its
  soundness: a body holding under the valuation by places holds under the valuation by the cells.
-/

module

public import LeanVM.Guest.Backend.Sound.Pool
public import LeanVM.Guest.B1.Sig.Frame

/-!
# Places against cells

The certificates read a function's values off frame cells (`Check.valG`: value `v` is the word in
cell `cl[v.idx]`); the back end off places (`valP`: a cell, or a cell times `g^e`). `Agree` holds a
function's places `pl`, its cells `cl` and its residual entries `res`; `fnOk` decides, statement by
statement on every path, that a body holding under `valP` holds under the cells' valuation
(`fnOk_sound`):

* a value placed in the cell the table names has one word under both;
* a constant `v = c` whose cell holds `c` because an earlier constant atom on the path, `u = c`
  with `u` placed in that cell, holds (`known`: the cells the path has so far set, by limbs);
* a hint constrains nothing;
* a residual value (`res`): a constant whose cell holds it, or a pointer placed at `fp[n]·g^e`
  whose cell holds that word, by a fact about the run that the core semantics does not give
  (`ResFact`, a property of the memory at the frame: `B2/Prologue.lean` proves it from the code).

Every other statement must name only values of the first kind (or residual pointers), so a value
whose cells differ appears nowhere else: a dead constant, a hint's destination.
-/

namespace LeanVM.Guest.Backend.B2

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- What the residual table says of a value whose cell the core semantics does not justify. -/
inductive Res where
  /-- A dead constant `word c0 c1`: its cell holds it. -/
  | konst (c0 c1 : Nat)
  /-- A pointer placed at `fp[n]·g^e`: its cell holds that word. -/
  | addr (n e : Nat)
  deriving DecidableEq, Repr

section

variable {κ : ℕ} (L : MemoryImage κ) (fp : K)

/-- **What a residual entry says of the frame cell `c`**: it holds the constant, or the pointer's
word. -/
def ResFact (c : Nat) : Res → Prop
  | .konst c0 c1 => wd L fp c = word c0 c1
  | .addr n e => wd L fp c = wd L fp n * ofK (addressOfIndex e)

end

/-- A function's places, its cell table and its residual values. -/
structure Agree where
  pl : V → Option Loc
  cl : List Nat
  res : List (V × Res)

namespace Agree

variable (A : Agree)

/-- The cell the table gives a value (`0` past it). -/
def cell (v : V) : Nat := A.cl.getD v.idx 0

/-- The value has one word under both valuations: it is placed in its cell, or it is a residual
pointer. -/
def eqv (v : V) : Bool :=
  match A.pl v with
  | some (.cell n) => n == A.cell v
  | some (.shifted n e) => A.res.contains (v, .addr n e)
  | none => false

/-- The cells set so far on the path, after an atom: a constant placed in a cell sets it. -/
def learn (known : List (Nat × Nat × Nat)) : Atom → List (Nat × Nat × Nat)
  | .const u c =>
      match A.pl u with
      | some (.cell n) => (n, limbsOf c) :: known
      | _ => known
  | _ => known

/-- The cells set after a statement, for the statements after it in its block. -/
def after (known : List (Nat × Nat × Nat)) : Stmt → List (Nat × Nat × Nat)
  | .atom a => A.learn known a
  | _ => known

/-- An atom holds under the cells: its values agree, or it is a constant whose cell the path set
or the residual table names, or a hint. -/
def atomOk (known : List (Nat × Nat × Nat)) (a : Atom) : Bool :=
  a.vals.all A.eqv ||
    match a with
    | .const v c => known.contains (A.cell v, limbsOf c) ||
        A.res.contains (v, .konst (limbsOf c).1 (limbsOf c).2)
    | .hint _ => true
    | _ => false

mutual
/-- **The comparison of a statement.** -/
def stmtOk (known : List (Nat × Nat × Nat)) : Stmt → Bool
  | .atom a => A.atomOk known a
  | .ite c z n => A.eqv c && blockOk known z && blockOk known n
  | .match_ x arms => A.eqv x && armsOk known arms
  | .call _ args rets => args.all A.eqv && rets.all A.eqv
  | .callIf c _ args => A.eqv c && args.all A.eqv
  | .dispatch x _ args rets => A.eqv x && args.all A.eqv && rets.all A.eqv
  | .ret vs => vs.all A.eqv

/-- The comparison of a block. -/
def blockOk (known : List (Nat × Nat × Nat)) : List Stmt → Bool
  | [] => true
  | s :: ss => stmtOk known s && blockOk (A.after known s) ss

/-- The comparison of the arms of a `match`. -/
def armsOk (known : List (Nat × Nat × Nat)) : List (List Stmt) → Bool
  | [] => true
  | a :: as => blockOk known a && armsOk known as
end

/-- **The comparison of a function**: its parameters agree and its body compares. -/
def fnOk (f : Fn) : Bool := f.params.all A.eqv && A.blockOk [] f.body

/-! ## Soundness -/

variable {κ : ℕ} (L : MemoryImage κ) (fp : K)

/-- The valuation by the table's cells. -/
noncomputable def valC : Val := fun v => wd L fp (A.cell v)

/-- What a residual entry says at a frame: `ResFact` of the value's cell. -/
def ResHolds (v : V) (r : Res) : Prop := ResFact L fp (A.cell v) r

/-- The cells the path set hold their words. -/
def KnownHolds (known : List (Nat × Nat × Nat)) : Prop :=
  ∀ p ∈ known, wd L fp p.1 = word p.2.1 p.2.2

variable {A L fp} {locs : VMap Loc}

section Sound


theorem eqv_sound (hpl : ∀ v, locs[v]? = A.pl v)
    (hres : ∀ p ∈ A.res, A.ResHolds L fp p.1 p.2) {v : V} (h : A.eqv v = true) :
    valP L fp locs v = A.valC L fp v := by
  unfold eqv at h
  unfold valC valP
  rw [hpl v]
  split at h
  · rename_i n hn
    rw [hn, beq_iff_eq.mp h]
    rfl
  · rename_i n e hn
    have := hres _ (List.contains_iff_mem.mp h)
    simp only [ResHolds, ResFact] at this
    rw [hn, this]
    rfl
  · exact absurd h Bool.false_ne_true

theorem map_eqv (hpl : ∀ v, locs[v]? = A.pl v)
    (hres : ∀ p ∈ A.res, A.ResHolds L fp p.1 p.2) {vs : List V} (h : vs.all A.eqv = true) :
    vs.map (valP L fp locs) = vs.map (A.valC L fp) :=
  List.map_congr_left fun v hv => eqv_sound hpl hres (List.all_eq_true.mp h v hv)

theorem learn_sound (hpl : ∀ v, locs[v]? = A.pl v) {known : List (Nat × Nat × Nat)} (hk : KnownHolds L fp known) {rd : Reader}
    {a : Atom} (ha : a.Holds rd (valP L fp locs)) : KnownHolds L fp (A.learn known a) := by
  cases a with
  | const u c =>
      cases hu : A.pl u with
      | none => simp only [learn, hu]; exact hk
      | some l =>
          cases l with
          | shifted _ _ => simp only [learn, hu]; exact hk
          | cell n =>
              simp only [learn, hu]
              intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · simp only [Atom.Holds, valP, hpl u, hu, locVal] at ha
                rw [ha]
                exact (word_limbsOf c).symm
              · exact hk p hp
  | _ => exact hk

theorem atomOk_sound (hpl : ∀ v, locs[v]? = A.pl v)
    (hres : ∀ p ∈ A.res, A.ResHolds L fp p.1 p.2) {known : List (Nat × Nat × Nat)} (hk : KnownHolds L fp known) {rd : Reader}
    {a : Atom} (hc : A.atomOk known a = true) (ha : a.Holds rd (valP L fp locs)) :
    a.Holds rd (A.valC L fp) := by
  unfold atomOk at hc
  rcases Bool.or_eq_true_iff.mp hc with hc | hc
  · exact (B1.Sig.atom_congr a fun v hv => eqv_sound hpl hres (List.all_eq_true.mp hc v hv)).mp ha
  · cases a with
    | const v c =>
        rcases Bool.or_eq_true_iff.mp hc with hc | hc
        · have := hk _ (List.contains_iff_mem.mp hc)
          simp only [Atom.Holds, valC]
          rw [this, word_limbsOf]
        · have := hres _ (List.contains_iff_mem.mp hc)
          simp only [ResHolds, ResFact] at this
          simp only [Atom.Holds, valC]
          rw [this, word_limbsOf]
    | hint => trivial
    | _ => exact absurd hc (by simp)

mutual
theorem blockOk_sound (hpl : ∀ v, locs[v]? = A.pl v)
    (hres : ∀ p ∈ A.res, A.ResHolds L fp p.1 p.2) {C : CallRel} {rd : Reader} :
    ∀ (known : List (Nat × Nat × Nat)) (ss : List Stmt) (N N' : Prop) (kret : List E → Prop),
      KnownHolds L fp known → A.blockOk known ss = true → (N → N') →
      Stmt.HoldsList C rd (valP L fp locs) ss N kret → Stmt.HoldsList C rd (A.valC L fp) ss N' kret
  | _, [], _, _, _, _, _, hN, h => hN h
  | known, s :: ss, N, N', kret, hk, hc, hN, h => by
      simp only [blockOk, Bool.and_eq_true] at hc
      obtain ⟨hs, hss⟩ := hc
      simp only [Stmt.HoldsList] at h ⊢
      cases s with
      | atom a =>
          simp only [Stmt.Holds] at h ⊢
          exact ⟨atomOk_sound hpl hres hk hs h.1,
            blockOk_sound hpl hres (C := C) (rd := rd) _ ss N N' kret (learn_sound hpl hk h.1) hss hN h.2⟩
      | ite c z n =>
          simp only [stmtOk, Bool.and_eq_true] at hs
          obtain ⟨⟨hcv, hz⟩, hn⟩ := hs
          have hcont := blockOk_sound hpl hres (C := C) (rd := rd) known ss N N' kret hk hss hN
          have e := eqv_sound hpl hres hcv
          simp only [Stmt.Holds] at h ⊢
          rw [← e]
          exact ⟨h.1, fun h0 => blockOk_sound hpl hres (C := C) (rd := rd) known z _ _ kret hk hz hcont (h.2.1 h0),
            fun h0 => blockOk_sound hpl hres (C := C) (rd := rd) known n _ _ kret hk hn hcont (h.2.2 h0)⟩
      | match_ x arms =>
          simp only [stmtOk, Bool.and_eq_true] at hs
          obtain ⟨hxv, ha⟩ := hs
          have hcont := blockOk_sound hpl hres (C := C) (rd := rd) known ss N N' kret hk hss hN
          simp only [Stmt.Holds] at h ⊢
          exact armsOk_sound hpl hres (C := C) (rd := rd) known x arms 0 _ _ kret hk (eqv_sound hpl hres hxv) ha hcont h
      | call f args rets =>
          simp only [stmtOk, Bool.and_eq_true] at hs
          simp only [Stmt.Holds] at h ⊢
          rw [← map_eqv hpl hres hs.1, ← map_eqv hpl hres hs.2]
          exact ⟨h.1, blockOk_sound hpl hres (C := C) (rd := rd) known ss N N' kret hk hss hN h.2⟩
      | callIf c f args =>
          simp only [stmtOk, Bool.and_eq_true] at hs
          simp only [Stmt.Holds] at h ⊢
          rw [← eqv_sound hpl hres hs.1, ← map_eqv hpl hres hs.2]
          exact ⟨h.1, h.2.1, blockOk_sound hpl hres (C := C) (rd := rd) known ss N N' kret hk hss hN h.2.2⟩
      | dispatch x fs args rets =>
          simp only [stmtOk, Bool.and_eq_true] at hs
          obtain ⟨⟨hxv, hav⟩, hrv⟩ := hs
          simp only [Stmt.Holds] at h ⊢
          rw [← eqv_sound hpl hres hxv, ← map_eqv hpl hres hav, ← map_eqv hpl hres hrv]
          exact ⟨h.1, blockOk_sound hpl hres (C := C) (rd := rd) known ss N N' kret hk hss hN h.2⟩
      | ret vs =>
          simp only [stmtOk] at hs
          simp only [Stmt.Holds] at h ⊢
          rw [← map_eqv hpl hres hs]
          exact h

theorem armsOk_sound (hpl : ∀ v, locs[v]? = A.pl v)
    (hres : ∀ p ∈ A.res, A.ResHolds L fp p.1 p.2) {C : CallRel} {rd : Reader} :
    ∀ (known : List (Nat × Nat × Nat)) (x : V) (arms : List (List Stmt)) (j : Nat) (N N' : Prop)
      (kret : List E → Prop), KnownHolds L fp known → valP L fp locs x = A.valC L fp x →
      A.armsOk known arms = true → (N → N') →
      Stmt.HoldsArms C rd (valP L fp locs) x j arms N kret →
        Stmt.HoldsArms C rd (A.valC L fp) x j arms N' kret
  | _, _, [], _, _, _, _, _, _, _, _, h => h.elim
  | known, x, a :: as, j, N, N', kret, hk, hx, hc, hN, h => by
      simp only [armsOk, Bool.and_eq_true] at hc
      simp only [Stmt.HoldsArms] at h ⊢
      rcases h with ⟨hxj, ha⟩ | h
      · exact Or.inl ⟨hx ▸ hxj, blockOk_sound hpl hres (C := C) (rd := rd) known a N N' kret hk hc.1 hN ha⟩
      · exact Or.inr (armsOk_sound hpl hres (C := C) (rd := rd) known x as (j + 1) N N' kret hk hx hc.2 hN h)
end

/-- **The comparison is sound**: a function whose comparison passes, at a frame where its
residual entries hold, has its parameters' words and its body under the cells as under the
places. -/
theorem fnOk_sound (hpl : ∀ v, locs[v]? = A.pl v)
    (hres : ∀ p ∈ A.res, A.ResHolds L fp p.1 p.2) {f : Fn} (hc : A.fnOk f = true) :
    f.params.map (valP L fp locs) = f.params.map (A.valC L fp) ∧
      ∀ (C : CallRel) (rd : Reader) (N : Prop) (kret : List E → Prop),
        Stmt.HoldsList C rd (valP L fp locs) f.body N kret →
          Stmt.HoldsList C rd (A.valC L fp) f.body N kret := by
  simp only [fnOk, Bool.and_eq_true] at hc
  exact ⟨map_eqv hpl hres hc.1, fun C rd N kret h =>
    blockOk_sound hpl hres [] f.body N N kret (fun _ h => absurd h List.not_mem_nil) hc.2 id h⟩

end Sound

end Agree

/-! ## Located relations -/

/-- **One located relation below another**: every frame the first locates a call at the second
does, and there the callee's parameters' words and body carry over from the first valuation to
the second, whatever the call relation. -/
theorem relL_le_of {P : Program} {rd : Reader} {vf vf' : String → K → Val}
    {A A' : String → K → List E → List E → Prop}
    (h : ∀ f fp a r fn, P.find? f = some fn → A f fp a r →
      A' f fp a r ∧ fn.params.map (vf f fp) = fn.params.map (vf' f fp) ∧
        ∀ (C : CallRel) (N : Prop) (kret : List E → Prop),
          Stmt.HoldsList C rd (vf f fp) fn.body N kret →
            Stmt.HoldsList C rd (vf' f fp) fn.body N kret) :
    CallRel.Le (P.RelL rd vf A) (P.RelL rd vf' A') := by
  have hn : ∀ n, CallRel.Le (P.locN rd vf A n) (P.locN rd vf' A' n) := by
    intro n
    induction n with
    | zero => exact fun _ _ _ h => h
    | succ n ih =>
        rintro f a r ⟨fn, fp, hf, hA, hp, hb⟩
        obtain ⟨hA', hpar, ht⟩ := h f fp a r fn hf hA
        exact ⟨fn, fp, hf, hA', hpar ▸ hp,
          holdsList_mono ih fn.body id (fun _ h => h) (ht _ _ _ hb)⟩
  exact fun f a r ⟨n, hl⟩ => ⟨n, hn n f a r hl⟩

end
end LeanVM.Guest.Backend.B2
