/-
  LeanVM.Guest.CoreMode.ResIx

  The residual family `resFam` with the function's top-level atoms indexed by value once
  (`AtomIx`), equal to it (`resFamX_of`), for the kernel.
-/

module

public import LeanVM.Guest.CoreMode.CoreResG

/-!
# Residual families over indexed atoms

`resFam` reads a function's top-level atoms (`Res.topAtoms`) through scans for the atom defining
or reading a value: a range check of `x` (`Res.rcBound`), the constant `k` (`Res.constOf`), the
product or sum `x` (`mulOf`, `bitPow`), a `DEREF` through `x` (`derefAt`). The kernel runs each scan
to the matching atom or the list's end, several for each residual and each step of `expM`. `AtomIx`
keeps the atoms in buckets by the index of the value each scan keys on, each bucket a trie entry
(`bucketT`, built lazily, so the kernel builds it once per check and reads a bucket in the depth of
the trie). A bucket is the atoms of its key in their order (`bkt_eq`), so a scan of it finds
what the scan of all the atoms does (`findSome?_bkt`, `any_bkt`); `resFamX` is `resFam`
over the buckets, and `resFamX_of` says it is the same check. The route's residual checks read it at hint `1`
(`resFamHint`, `ResTab.lean`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## Buckets -/

/-- **Entries by key**, within `d` levels: key `k`'s entries `(k, a)`, in order, at key `k` of the
trie. A level is built when a read reaches it. -/
noncomputable def bucketT {α : Type} (d : ℕ) : List (ℕ × α) → Exec.Trie (List α) :=
  Nat.rec (motive := fun _ ↦ List (ℕ × α) → Exec.Trie (List α)) (fun _ ↦ .nil)
    (fun _ b l ↦ List.casesOn (motive := fun _ ↦ Exec.Trie (List α)) l .nil fun _ _ ↦
      .node (some (l.filterMap fun p ↦ bif Nat.beq p.1 0 then some p.2 else none))
        (b (l.filterMap fun p ↦ bif Nat.beq (Nat.mod p.1 2) 1 then some (Nat.div p.1 2, p.2) else none))
        (b (l.filterMap fun p ↦
          bif !Nat.beq p.1 0 && Nat.beq (Nat.mod p.1 2) 0 then some (Nat.sub (Nat.div p.1 2) 1, p.2) else none))) d

theorem bucketT_get {α : Type} : ∀ (d : ℕ) (l : List (ℕ × α)) (n : ℕ), n + 1 < 2 ^ d →
    ((bucketT d l).get n).getD [] = l.filterMap fun p ↦ if p.1 = n then some p.2 else none
  | 0, _, n, h => by simp at h
  | d + 1, [], _, _ => rfl
  | d + 1, q :: l, n, h => by
    have hb : ∀ a b, Nat.beq a b = decide (a = b) := fun a b ↦ Bool.eq_iff_iff.2 (by simp)
    have e : bucketT (d + 1) (q :: l) =
        .node (some ((q :: l).filterMap fun p ↦ if p.1 = 0 then some p.2 else none))
          (bucketT d ((q :: l).filterMap fun p ↦ if p.1 % 2 = 1 then some (p.1 / 2, p.2) else none))
          (bucketT d ((q :: l).filterMap fun p ↦
            if p.1 ≠ 0 ∧ p.1 % 2 = 0 then some (p.1 / 2 - 1, p.2) else none)) := by
      show Exec.Trie.node _ (bucketT d _) (bucketT d _) = _
      simp only [hb, Bool.cond_decide, ← Bool.decide_and, ← decide_not]
      rfl
    rw [e, Exec.Trie.get_node]
    rw [Nat.pow_succ] at h
    split
    · subst n; rfl
    · split <;> rw [bucketT_get d _ _ (by omega), List.filterMap_filterMap] <;>
        refine congrArg (fun f ↦ List.filterMap f _) (funext fun p ↦ ?_) <;>
        by_cases hq : p.1 = n <;> simp only [hq, ↓reduceIte] <;> split <;> simp <;> omega

/-- The depth of an index's tries. -/
def ixDepth : ℕ := 32

/-- The atoms of `as` by `key`: the trie of `bucketT`. -/
noncomputable def keyT (key : Atom → Option ℕ) (as : List Atom) : Exec.Trie (List Atom) :=
  bucketT ixDepth (as.filterMap fun a ↦ match key a with
    | some k => some (k, a)
    | none => none)

/-- **The atoms of `as` of key `v.idx`**, read from `t`, the atoms' trie by `key`. -/
noncomputable def bkt (key : Atom → Option ℕ) (t : Exec.Trie (List Atom)) (as : List Atom) (v : V) : List Atom :=
  bif Nat.blt (v.idx + 1) (2 ^ ixDepth) then (Check.getF t v.idx).getD [] else as.filter fun a ↦ key a == some v.idx

theorem bkt_eq (key : Atom → Option ℕ) (as : List Atom) (v : V) :
    bkt key (keyT key as) as v = as.filter fun a ↦ key a == some v.idx := by
  unfold bkt
  cases h : Nat.blt (v.idx + 1) (2 ^ ixDepth)
  · rfl
  · rw [Bool.cond_true, Check.getF_eq, keyT, bucketT_get _ _ _ (Nat.blt_eq.mp h), List.filterMap_filterMap]
    induction as with
    | nil => rfl
    | cons a as ih =>
      rw [List.filterMap_cons, List.filter_cons, ih]
      cases key a with
      | none => rfl
      | some k => by_cases hk : k = v.idx <;> simp [hk]

/-! ## Scans of a bucket -/

private theorem findSome?_filter_of {α β : Type} {p : α → Bool} {f : α → Option β}
    (h : ∀ a, (f a).isSome → p a = true) :
    ∀ l : List α, (l.filter p).findSome? f = l.findSome? f
  | [] => rfl
  | a :: l => by
    rw [List.filter_cons, List.findSome?_cons]
    cases hp : p a
    · cases hf : f a with
      | none => exact findSome?_filter_of h l
      | some _ => exact absurd (h a (by rw [hf]; rfl)) (by rw [hp]; decide)
    · simp only [↓reduceIte, List.findSome?_cons, findSome?_filter_of h l]

private theorem any_filter_of {α : Type} {p f : α → Bool} (h : ∀ a, f a = true → p a = true) :
    ∀ l : List α, (l.filter p).any f = l.any f
  | [] => rfl
  | a :: l => by
    rw [List.filter_cons, List.any_cons]
    cases hp : p a
    · cases hf : f a
      · exact any_filter_of h l
      · exact absurd (h a hf) (by rw [hp]; decide)
    · simp only [↓reduceIte, List.any_cons, any_filter_of h l]

/-- A scan that finds only atoms of key `v.idx` finds in `v`'s bucket what it finds in `as`. -/
private theorem findSome?_bkt {β : Type} {key : Atom → Option ℕ} {f : Atom → Option β} (as : List Atom) {v : V}
    (h : ∀ a, (f a).isSome → key a = some v.idx) : (bkt key (keyT key as) as v).findSome? f = as.findSome? f := by
  rw [bkt_eq, findSome?_filter_of (fun a ha ↦ by simp [h a ha])]

/-- `findSome?_bkt` for `List.any`. -/
private theorem any_bkt {key : Atom → Option ℕ} {f : Atom → Bool} (as : List Atom) {v : V}
    (h : ∀ a, f a = true → key a = some v.idx) : (bkt key (keyT key as) as v).any f = as.any f := by
  rw [bkt_eq, any_filter_of (fun a ha ↦ by simp [h a ha])]

/-! ## The index -/

/-- A range check's value. -/
def ixRc : Atom → Option ℕ
  | .rangeCheck x _ _ _ _ => some x.idx
  | _ => none

/-- A constant's value. -/
def ixCst : Atom → Option ℕ
  | .const d _ => some d.idx
  | _ => none

/-- A product's value. -/
def ixMul : Atom → Option ℕ
  | .mul d _ _ => some d.idx
  | _ => none

/-- A sum's value. -/
def ixAdd : Atom → Option ℕ
  | .add d _ _ => some d.idx
  | _ => none

/-- A `DEREF`'s pointer. -/
def ixLd : Atom → Option ℕ
  | .load _ p _ => some p.idx
  | .touch _ p => some p.idx
  | _ => none

/-- **Atoms by value**: the list, and its tries by `ixRc`, `ixCst`, `ixMul`, `ixAdd` and `ixLd`. -/
structure AtomIx where
  as : List Atom
  rc : Exec.Trie (List Atom)
  cst : Exec.Trie (List Atom)
  mul : Exec.Trie (List Atom)
  add : Exec.Trie (List Atom)
  ld : Exec.Trie (List Atom)

namespace AtomIx

/-- The index of the atoms `as`. -/
noncomputable def of (as : List Atom) : AtomIx :=
  ⟨as, keyT ixRc as, keyT ixCst as, keyT ixMul as, keyT ixAdd as, keyT ixLd as⟩

variable (ix : AtomIx)

/-- The range checks of `v`, and maybe more atoms. -/
noncomputable def rcs (v : V) : List Atom := bkt ixRc ix.rc ix.as v
/-- The constants of `v`, and maybe more atoms. -/
noncomputable def csts (v : V) : List Atom := bkt ixCst ix.cst ix.as v
/-- The products of `v`, and maybe more atoms. -/
noncomputable def muls (v : V) : List Atom := bkt ixMul ix.mul ix.as v
/-- The sums of `v`, and maybe more atoms. -/
noncomputable def adds (v : V) : List Atom := bkt ixAdd ix.add ix.as v
/-- The `DEREF`s through `v`, and maybe more atoms. -/
noncomputable def lds (v : V) : List Atom := bkt ixLd ix.ld ix.as v

end AtomIx

/-! ## The families' reads, over the index -/

/-- `Res.constOf`, over the index. -/
noncomputable def constOfI (ix : AtomIx) (k : V) : Option E :=
  (ix.csts k).findSome? fun
    | .const d w => if d = k then some w else none
    | _ => none

/-- `Res.rcBound`, over the index. -/
noncomputable def rcBoundI (ix : AtomIx) (v : V) : Option ℕ :=
  (ix.rcs v).findSome? fun
    | .rangeCheck x _ _ _ k =>
      if x = v then
        match (constOfI ix k).bind Res.powOf with
        | some e => if e + 1 ≤ 2 ^ 33 then some (e + 1) else none
        | none => none
      else none
    | _ => none

/-- `derefAt`, over the index. -/
noncomputable def derefAtI (ix : AtomIx) (p : V) : Bool := (ix.lds p).any fun
  | .load _ p' 0 => decide (p' = p)
  | .touch _ p' => decide (p' = p)
  | _ => false

/-- `mulOf`, over the index. -/
noncomputable def mulOfI (ix : AtomIx) (x : V) : Option (V × V) := (ix.muls x).findSome? fun
  | .mul d a b => if d = x then some (a, b) else none
  | _ => none

/-- `bitPow`, over the index. -/
noncomputable def bitPowI (ix : AtomIx) (x : V) : Option ℕ :=
  (ix.adds x).findSome? fun
    | .add d o y => if d = x ∧ constOfI ix o = some 1 then
        match mulOfI ix y with
        | some (b, w) => if Atom.mul b b b ∈ ix.muls b then (constOfI ix w).bind fun c ↦ Res.powOf (c + 1)
          else none
        | none => none
      else none
    | _ => none

/-- `expM`, over the index. -/
noncomputable def expMI (ix : AtomIx) : ℕ → V → Option ℕ
  | 0, _ => none
  | f + 1, x => if derefAtI ix x then some (2 ^ 28 - 1) else
      match mulOfI ix x with
      | some (a, b) => (expMI ix f a).bind fun ma ↦ (expMI ix f b).map (ma + ·)
      | none => match bitPowI ix x with
        | some m => some m
        | none => (constOfI ix x).bind Res.powOf

/-- `topProd`, over the index. -/
noncomputable def topProdI (ix : AtomIx) : List (ℕ × ℕ) → Option ℕ
  | [] => some 0
  | (x, a) :: bs => (expMI ix expFuel (V.n x)).bind fun M ↦ (topProdI ix bs).map (a * M + ·)

/-- `resFam`'s `rcv`, over the index: `x` range checked against the value `p`. -/
noncomputable def rcvI (ix : AtomIx) (x p : ℕ) : Bool := (ix.rcs (V.n x)).any fun
  | .rangeCheck x' _ _ _ k => decide (x' = V.n x) && decide (k = V.n p)
  | _ => false

/-- The products `k = p·w` among the atoms, `w` the constant `g⁻¹`, over the index. -/
noncomputable def rcnMulI (ix : AtomIx) (k : V) (p : ℕ) : Bool := (ix.muls k).any fun
  | .mul k' p' w => decide (k' = k) && decide (p' = V.n p) &&
      (match constOfI ix w with
      | some w' => invG w'
      | none => false)
  | _ => false

/-- `resFam`'s `rcn`, over the index: `x` range checked against `k = p·w`, `w` the constant `g⁻¹`. -/
noncomputable def rcnI (ix : AtomIx) (x p : ℕ) : Bool := (ix.rcs (V.n x)).any fun
  | .rangeCheck x' _ _ _ k => decide (x' = V.n x) && rcnMulI ix k p
  | _ => false

section Eq

variable (as : List Atom)

theorem constOfI_of (k : V) : constOfI (AtomIx.of as) k = Res.constOf as k :=
  (findSome?_bkt as fun a ↦ by cases a <;> simp_all [ixCst]).trans rfl

theorem rcBoundI_of (v : V) : rcBoundI (AtomIx.of as) v = Res.rcBound as v := by
  simp only [rcBoundI, constOfI_of]
  exact (findSome?_bkt as fun a ↦ by cases a <;> simp_all [ixRc]; split <;> simp_all).trans rfl

theorem derefAtI_of (p : V) : derefAtI (AtomIx.of as) p = derefAt as p :=
  (any_bkt as fun a ↦ by cases a <;> simp_all [ixLd]; split <;> simp_all).trans rfl

theorem mulOfI_of (x : V) : mulOfI (AtomIx.of as) x = mulOf as x :=
  (findSome?_bkt as fun a ↦ by cases a <;> simp_all [ixMul]).trans rfl

theorem muls_of (b : V) : Atom.mul b b b ∈ (AtomIx.of as).muls b ↔ Atom.mul b b b ∈ as := by
  simp [AtomIx.muls, AtomIx.of, bkt_eq, ixMul]

theorem bitPowI_of (x : V) : bitPowI (AtomIx.of as) x = bitPow as x := by
  simp only [bitPowI, constOfI_of, mulOfI_of, muls_of]
  exact (findSome?_bkt as fun a ↦ by cases a <;> simp_all [ixAdd]; split <;> simp_all).trans rfl

theorem expMI_of : ∀ (f : ℕ) (x : V), expMI (AtomIx.of as) f x = expM as f x
  | 0, _ => rfl
  | f + 1, x => by
    simp only [expMI, expM, derefAtI_of, mulOfI_of, bitPowI_of, constOfI_of, expMI_of f]
    rfl

theorem topProdI_of (fn : Fn) :
    ∀ bs : List (ℕ × ℕ), topProdI (AtomIx.of (Res.topAtoms fn.body)) bs = topProd fn bs
  | [] => rfl
  | (x, a) :: bs => by simp only [topProdI, topProd, expMI_of, topProdI_of fn bs]

theorem rcvI_of (x p : ℕ) : rcvI (AtomIx.of as) x p = as.any fun
    | .rangeCheck x' _ _ _ k => decide (x' = V.n x) && decide (k = V.n p)
    | _ => false :=
  any_bkt as fun a ↦ by cases a <;> simp_all [ixRc]

theorem rcnMulI_of (k : V) (p : ℕ) : rcnMulI (AtomIx.of as) k p = as.any fun
    | .mul k' p' w => decide (k' = k) && decide (p' = V.n p) &&
        (match Res.constOf as w with
        | some w' => invG w'
        | none => false)
    | _ => false := by
  simp only [rcnMulI, constOfI_of]
  exact any_bkt as fun a ↦ by cases a <;> simp_all [ixMul]

theorem rcnI_of (x p : ℕ) : rcnI (AtomIx.of as) x p = as.any fun
    | .rangeCheck x' _ _ _ k => decide (x' = V.n x) && as.any fun
        | .mul k' p' w => decide (k' = k) && decide (p' = V.n p) &&
            (match Res.constOf as w with
            | some w' => invG w'
            | none => false)
        | _ => false
    | _ => false := by
  simp only [rcnI, rcnMulI_of]
  exact any_bkt as fun a ↦ by cases a <;> simp_all [ixRc]

end Eq

/-! ## The family -/

/-- **`resFam` over the index `ix`** of the function's top-level atoms; the families it does not
scan for are `resFam`'s own. -/
noncomputable def resFamX (ix : AtomIx) (fn : Fn) (xc : List ℕ) : CRes → Bool
  | .lt (.val x) (.num n) => decide (n < capE) &&
      ((match rcBoundI ix (V.n x) with
        | some N => decide (N ≤ n)
        | none => false) ||
        ((Res.topSels fn.body).any fun p ↦ decide (p.1 = V.n x) && decide (p.2 ≤ n)) ||
        (decide (2 ^ 28 ≤ n) && decide (x < fn.params.length) && xc.contains (2 + x) &&
          expDiff ix.as (V.n x)) ||
        (expMI ix expFuel (V.n x)).any (· < n))
  | .lt (.val x) (.mono c) => match c.bases, c.off with
    | [(p, 1)], 1 => rcvI ix x p
    | _, _ => false
  | .lt (.val x) (.val p) => rcnI ix x p
  | .lt (.mono c) (.num n) => (match c.bases with
    | [(x, 1)] => decide (n < capE) &&
        ((Res.topSels fn.body).any (fun p ↦ decide (p.1 = V.n x) && decide (p.2 + c.off ≤ n)) ||
          match rcBoundI ix (V.n x) with
          | some N => decide (N + c.off ≤ n)
          | none => false)
    | _ => false) || (decide (n < capE) && (topProdI ix c.bases).any (· + c.off < n))
  | .under cs r => resFamX ix fn xc r || negFam fn cs r
  | r => resFam fn xc r

theorem resFamX_of (fn : Fn) (xc : List ℕ) :
    ∀ r, resFamX (AtomIx.of (Res.topAtoms fn.body)) fn xc r = resFam fn xc r
  | .lt (.val x) (.num n) => by simp only [resFamX, resFam, rcBoundI_of, expMI_of]; rfl
  | .lt (.val x) (.mono c) => by simp only [resFamX, resFam, rcvI_of]; rfl
  | .lt (.val x) (.val p) => by simp only [resFamX, resFam, rcnI_of]; rfl
  | .lt (.mono c) (.num n) => by simp only [resFamX, resFam, rcBoundI_of, topProdI_of]; rfl
  | .under cs r => by simp only [resFamX, resFam, resFamX_of fn xc r]
  | .lt (.num _) _ | .lt (.mono _) (.val _) | .lt (.mono _) (.mono _) | .nz _ | .sub _ _
  | .subR _ _ | .subP _ _ => rfl

end

end LeanVM.Guest.CoreMode
