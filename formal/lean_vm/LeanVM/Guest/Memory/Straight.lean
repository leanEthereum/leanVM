/-
  LeanVM.Guest.Memory.Straight

  The path of a straight-line body (atoms, calls, conditional calls, then a return), and of one
  with a fused dispatch between straight runs: its events, `HeapBuf` hints, `frameAddr`s, runs,
  frames and loads, read off the statements.
-/

module

public import LeanVM.Guest.Memory.Regions
public import LeanVM.Guest.Value.Bits

/-!
# Straight-line bodies

A body with no branch, `match` or dispatch walks every statement in turn
(`walk_straight`), so the `HeapBuf` hints, `frameAddr`s and frames of its path are those of its
statements (`straight_parts`), each a `filterMap` over the statements that the kernel evaluates on
a concrete body; only a conditional call's `taken` and a dynamic size's exponent depend on the
valuation. Likewise its loads (`loadAddrs_straight`) and runs (`runs_straight`); a body of atoms
(`walk_atoms`, `allocs_atoms`, ...), and a fused dispatch between straight runs, which walks the
callee its selector picks (`walk_dispatch`, `pick_eq`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- A statement of a straight-line body. -/
def Stmt.straight : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | .callIf .. => true
  | _ => false

/-- The events of a straight-line statement. -/
noncomputable def slEvs (σ : Val) : Stmt → List Ev
  | .atom a => [.atom a]
  | .call f args rets => [.call f args rets]
  | .callIf c f args => [.inK c, if σ c = 0 then .skip f args else .call f args []]
  | _ => []

theorem walk1_straight (σ : Val) : ∀ s : Stmt, Stmt.straight s = true → walk1 σ s = .fall (slEvs σ s)
  | .atom _, _ => rfl
  | .call .., _ => rfl
  | .callIf .., _ => rfl
  | .ite .., h => by simp [Stmt.straight] at h
  | .match_ .., h => by simp [Stmt.straight] at h
  | .dispatch .., h => by simp [Stmt.straight] at h
  | .ret _, h => by simp [Stmt.straight] at h

/-- **A straight-line body walks every statement.** -/
theorem walk_straight (σ : Val) (vs : List V) : ∀ pre : List Stmt, pre.all Stmt.straight = true →
    walk σ (pre ++ [.ret vs]) = .ret (pre.flatMap (slEvs σ)) vs
  | [], _ => by simp [walk, walk1, Out.seq]
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_straight σ vs pre h.2, walk1_straight σ s h.1, Out.seq,
      Out.pre, List.flatMap_cons]

/-- A `HeapBuf` hint: its pointer, and its size or the value whose exponent it is. -/
def Stmt.allocSz : Stmt → Option (V × (ℕ ⊕ V))
  | .atom (.hint (.alloc d n)) => some (d, .inl n)
  | .atom (.hint (.allocDyn d s)) => some (d, .inr s)
  | _ => none

/-- A `frameAddr`: its pointer and its run's first value. -/
def Stmt.addrS : Stmt → Option (V × V)
  | .atom (.frameAddr p (r :: _)) => some (p, r)
  | _ => none

/-- A frame a statement sets up: its condition, callee, arguments, returns. -/
def Stmt.callS : Stmt → Option (Option V × String × List V × List V)
  | .call f args rets => some (none, f, args, rets)
  | .callIf c f args => some (some c, f, args, [])
  | _ => none

/-- The frame of `Stmt.callS` under `σ`. -/
noncomputable def mkCall (σ : Val) : Option V × String × List V × List V → Call
  | (none, f, args, rets) => ⟨f, args, rets, true⟩
  | (some c, f, args, rets) => ⟨f, args, rets, decide (σ c ≠ 0)⟩

theorem slEvs_atom_alloc (σ : Val) (a : Atom) :
    (slEvs σ (.atom a)).filterMap Ev.allocDst? = ((Stmt.allocSz (.atom a)).map Prod.fst).toList ∧
    (slEvs σ (.atom a)).filterMap (Ev.alloc? σ) =
      ((Stmt.allocSz (.atom a)).map fun x => x.2.elim id fun s => logG (σ s)).toList ∧
    (slEvs σ (.atom a)).filterMap Ev.addr? = (Stmt.addrS (.atom a)).toList ∧
    (slEvs σ (.atom a)).filterMap Ev.call? = [] := by
  simp only [slEvs, List.filterMap_cons, List.filterMap_nil]
  cases a with
  | frameAddr p run =>
    cases run <;> simp [Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?, Stmt.allocSz, Stmt.addrS]
  | hint h => cases h <;> simp [Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?, Stmt.allocSz, Stmt.addrS]
  | _ => simp [Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?, Stmt.allocSz, Stmt.addrS]

theorem straight_parts (σ : Val) : ∀ pre : List Stmt, pre.all Stmt.straight = true →
    allocDsts (pre.flatMap (slEvs σ)) = (pre.filterMap Stmt.allocSz).map Prod.fst ∧
    allocs σ (pre.flatMap (slEvs σ)) =
      (pre.filterMap Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) ∧
    addrs (pre.flatMap (slEvs σ)) = pre.filterMap Stmt.addrS ∧
    calls (pre.flatMap (slEvs σ)) = (pre.filterMap Stmt.callS).map (mkCall σ)
  | [], _ => by simp [allocDsts, allocs, addrs, calls]
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨i1, i2, i3, i4⟩ := straight_parts σ pre h.2
    simp only [allocDsts, allocs, addrs, calls, List.flatMap_cons, List.filterMap_append] at i1 i2 i3 i4 ⊢
    rw [i1, i2, i3, i4]
    match s, h.1 with
    | .atom a, _ =>
      obtain ⟨e1, e2, e3, e4⟩ := slEvs_atom_alloc σ a
      rw [e1, e2, e3, e4]
      cases hs : Stmt.allocSz (.atom a) <;> cases ha : Stmt.addrS (.atom a) <;>
        simp [List.filterMap_cons, hs, ha, Stmt.callS]
    | .call f args rets, _ =>
      simp [slEvs, List.filterMap_cons, Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?, Stmt.allocSz,
        Stmt.addrS, Stmt.callS, mkCall]
    | .callIf c f args, _ =>
      by_cases hc : σ c = 0 <;>
        simp [slEvs, hc, List.filterMap_cons, Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?,
          Stmt.allocSz, Stmt.addrS, Stmt.callS, mkCall]

/-! ## Bodies of atoms -/

theorem walk_atoms (σ : Val) (as : List Atom) (vs : List V) :
    walk σ (as.map .atom ++ [.ret vs]) = .ret (as.map Ev.atom) vs := by
  rw [walk_straight σ vs _ (by simp [Stmt.straight])]
  congr 1
  induction as with
  | nil => rfl
  | cons a as ih => simp [slEvs, ih]

/-- An atom's `HeapBuf` hint, if any. -/
def atomAllocB : Atom → Bool
  | .hint (.alloc ..) => true
  | .hint (.allocDyn ..) => true
  | _ => false

/-- An atom's `frameAddr`: its pointer and the first value of its run. -/
def atomAddr? : Atom → Option (V × V)
  | .frameAddr p (r :: _) => some (p, r)
  | _ => none

/-- An atom's run: its first value and its length. -/
def atomRun? : Atom → Option (V × ℕ)
  | .frameAddr _ (r :: rs) => some (r, rs.length + 1)
  | _ => none

/-- An atom's load: its pointer and offset. -/
def atomLoad? : Atom → Option (V × ℕ)
  | .load _ p off => some (p, off)
  | _ => none

theorem allocDsts_atoms {as : List Atom} (h : as.all (fun a => !atomAllocB a) = true) :
    allocDsts (as.map Ev.atom) = [] := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [allocDsts, List.map_cons, List.filterMap_cons] at ih ⊢
    rw [ih h.2]
    cases a with
    | hint hh => cases hh <;> simp_all [Ev.allocDst?, atomAllocB]
    | _ => rfl

theorem allocs_atoms (σ : Val) {as : List Atom} (h : as.all (fun a => !atomAllocB a) = true) :
    allocs σ (as.map Ev.atom) = [] := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [allocs, List.map_cons, List.filterMap_cons] at ih ⊢
    rw [ih h.2]
    cases a with
    | hint hh => cases hh <;> simp_all [Ev.alloc?, atomAllocB]
    | _ => rfl

theorem addrs_atoms (as : List Atom) : addrs (as.map Ev.atom) = as.filterMap atomAddr? := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [addrs, List.map_cons, List.filterMap_cons] at ih ⊢
    rw [ih]
    cases a with
    | frameAddr p run => cases run <;> rfl
    | _ => rfl

theorem runs_atoms (as : List Atom) : runs (as.map Ev.atom) = as.filterMap atomRun? := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [runs, List.map_cons, List.filterMap_cons] at ih ⊢
    rw [ih]
    cases a with
    | frameAddr p run => cases run <;> rfl
    | _ => rfl

theorem calls_atoms (as : List Atom) : calls (as.map Ev.atom) = [] := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [calls, Ev.call?]

theorem loadAddrs_atoms (σ : Val) (as : List Atom) :
    loadAddrs σ (as.map Ev.atom) = (as.filterMap atomLoad?).map fun q => (σ q.1).limb 0 * gpow q.2 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [loadAddrs, List.map_cons, List.filterMap_cons] at ih ⊢
    rw [ih]
    cases a <;> rfl

theorem holds_atoms {rd : Reader} {σ : Val} {as : List Atom} (h : ∀ a ∈ as, a.Holds rd σ) :
    ∀ e ∈ as.map Ev.atom, e.Holds rd σ := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  exact h a ha

/-- The word `g^e`'s first limb. -/
theorem limb0_gen_pow (e : ℕ) : (gen ^ e).limb 0 = gpow e := by
  rw [gen_pow_eq_ofK]; simp

theorem gpow_add' (a b : ℕ) : gpow a * gpow b = gpow (a + b) := by
  simp [Parameters.gpow, pow_add]

/-! ## Straight bodies with calls -/

/-- A statement's load: its pointer and offset. -/
def stmtLoad? : Stmt → Option (V × ℕ)
  | .atom (.load _ p off) => some (p, off)
  | _ => none

theorem loadAddrs_straight (σ : Val) : ∀ pre : List Stmt, pre.all Stmt.straight = true →
    loadAddrs σ (pre.flatMap (slEvs σ)) = (pre.filterMap stmtLoad?).map fun q => (σ q.1).limb 0 * gpow q.2
  | [], _ => rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := loadAddrs_straight σ pre h.2
    simp only [loadAddrs, List.flatMap_cons, List.filterMap_append] at ih ⊢
    rw [ih]
    match s, h.1 with
    | .atom a, _ => cases a <;> rfl
    | .call f args rets, _ => rfl
    | .callIf c f args, _ => by_cases hc : σ c = 0 <;>
      simp [slEvs, hc, Ev.loadAddr?, stmtLoad?, List.filterMap_cons, List.filterMap_nil]

/-- A statement's `frameAddr` run: its first value and its length. -/
def stmtRun? : Stmt → Option (V × ℕ)
  | .atom (.frameAddr _ (r :: rs)) => some (r, rs.length + 1)
  | _ => none

theorem runs_straight (σ : Val) : ∀ pre : List Stmt, pre.all Stmt.straight = true →
    runs (pre.flatMap (slEvs σ)) = pre.filterMap stmtRun?
  | [], _ => rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := runs_straight σ pre h.2
    simp only [runs, List.flatMap_cons, List.filterMap_append] at ih ⊢
    rw [ih]
    match s, h.1 with
    | .atom a, _ =>
      cases a with
      | frameAddr p run => cases run <;> rfl
      | _ => rfl
    | .call f args rets, _ => rfl
    | .callIf c f args, _ => by_cases hc : σ c = 0 <;>
      simp [slEvs, hc, Ev.run?, stmtRun?, List.filterMap_cons, List.filterMap_nil]

/-- An atom of a straight body holds when its path's events are `Ok`. -/
theorem atom_holds_of_ok {C : CallRel} {rd : Reader} {σ : Val} {pre : List Stmt} {a : Atom}
    (ha : Stmt.atom a ∈ pre) (h : ∀ e ∈ pre.flatMap (slEvs σ), e.Ok C rd σ) : a.Holds rd σ :=
  (h (.atom a) (List.mem_flatMap.mpr ⟨_, ha, by simp [slEvs]⟩)).1

/-! ## A fused dispatch between straight runs -/

theorem pick_eq (σ : Val) (x : V) (args rets : List V) : ∀ (fs : List String) (j i : ℕ),
    i < fs.length → j + fs.length ≤ 2 ^ 64 - 1 → σ x = ofK (gpow (j + i)) →
    pick σ x args rets j fs = .fall [.call fs[i]! args rets]
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | f :: fs, j, i, hi, hb, hx => by
    simp only [List.length_cons] at hi hb
    unfold pick
    by_cases hxj : σ x = ofK (gpow j)
    · rw [ite_eq_left hxj]
      obtain rfl : i = 0 := by
        by_contra h0
        exact ofK_gpow_ne (show j < j + i by omega) (by omega) (hxj.symm.trans hx)
      rfl
    · rw [ite_eq_right hxj]
      cases i with
      | zero => exact absurd (by simpa using hx) hxj
      | succ i =>
        rw [pick_eq σ x args rets fs (j + 1) i (by omega) (by omega) (by rw [hx]; congr 2; omega)]
        rfl

/-- **A body: a straight run, a fused dispatch, a straight run, a return**, walks the runs and
the callee the selector picks. -/
theorem walk_dispatch (σ : Val) (pre post : List Stmt) (hpre : pre.all Stmt.straight = true)
    (hpost : post.all Stmt.straight = true) (x : V) (fs : List String) (args rets vs : List V)
    {i : ℕ} (hi : i < fs.length) (hfl : fs.length ≤ 2 ^ 64 - 1) (hx : σ x = ofK (gpow i)) :
    walk σ (pre ++ .dispatch x fs args rets :: (post ++ [.ret vs])) =
      .ret (pre.flatMap (slEvs σ) ++ .call fs[i]! args rets :: post.flatMap (slEvs σ)) vs := by
  induction pre with
  | nil =>
    rw [List.nil_append, walk, walk1, pick_eq σ x args rets fs 0 i hi (by omega) (by rw [Nat.zero_add]; exact hx),
      walk_straight σ vs post hpost]
    rfl
  | cons s pre ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hpre
    rw [List.cons_append, walk, ih hpre.2, walk1_straight σ s hpre.1, Out.seq, Out.pre,
      List.flatMap_cons, List.append_assoc]

theorem logG_gen_pow {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (gen ^ e) = e := by
  rw [gen_pow_eq_ofK, logG_spec he]

/-- A straight run without its `ret` falls through with its statements' events. -/
theorem walk_straight_fall (σ : Val) : ∀ pre : List Stmt, pre.all Stmt.straight = true →
    walk σ pre = .fall (pre.flatMap (slEvs σ))
  | [], _ => rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [walk, walk_straight_fall σ pre h.2, walk1_straight σ s h.1, Out.seq, Out.pre, List.flatMap_cons]

/-- A dispatch between straight runs, without a `ret`, falls through with the chosen call. -/
theorem walk_dispatch_fall (σ : Val) (pre post : List Stmt) (hpre : pre.all Stmt.straight = true)
    (hpost : post.all Stmt.straight = true) (x : V) (fs : List String) (args rets : List V)
    {i : ℕ} (hi : i < fs.length) (hfl : fs.length ≤ 2 ^ 64 - 1) (hx : σ x = ofK (gpow i)) :
    walk σ (pre ++ .dispatch x fs args rets :: post) =
      .fall (pre.flatMap (slEvs σ) ++ .call fs[i]! args rets :: post.flatMap (slEvs σ)) := by
  induction pre with
  | nil =>
    rw [List.nil_append, walk, walk1, pick_eq σ x args rets fs 0 i hi (by omega) (by rw [Nat.zero_add]; exact hx),
      walk_straight_fall σ post hpost]
    rfl
  | cons s pre ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hpre
    rw [List.cons_append, walk, ih hpre.2, walk1_straight σ s hpre.1, Out.seq, Out.pre,
      List.flatMap_cons, List.append_assoc]

end
end LeanVM.Guest.Memory
