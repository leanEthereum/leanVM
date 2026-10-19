/-
  LeanVM.Guest.B1.Da.Atoms

  The path of a body of atoms then a return, for the placed relation: its events, `HeapBuf`
  hints, `frameAddr`s, runs, frames and loads, read off the atoms.
-/

module

public import LeanVM.Guest.Memory.Regions
public import LeanVM.Guest.Memory.GuestWf
public import LeanVM.Guest.B1.Main.Straight
public import LeanVM.Guest.B1.Digest.Common

/-!
# Bodies of atoms

A body `as.map .atom ++ [.ret vs]` walks to the atoms' events (`walk_atoms`). Its `HeapBuf`
hints, `frameAddr`s, runs and loads are `filterMap`s over the atoms (`atomAlloc?`, `atomAddr?`,
`atomRun?`, `atomLoad?`), which the kernel evaluates on a concrete body; it sets up no frame.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem walk_atoms (σ : Val) (as : List Atom) (vs : List V) :
    walk σ (as.map .atom ++ [.ret vs]) = .ret (as.map Ev.atom) vs := by
  rw [Main.walk_straight σ vs _ (by simp [Main.Stmt.straight])]
  congr 1
  induction as with
  | nil => rfl
  | cons a as ih => simp [Main.slEvs, ih]

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

theorem loadAddrs_straight (σ : Val) : ∀ pre : List Stmt, pre.all Main.Stmt.straight = true →
    loadAddrs σ (pre.flatMap (Main.slEvs σ)) = (pre.filterMap stmtLoad?).map fun q => (σ q.1).limb 0 * gpow q.2
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
      simp [Main.slEvs, hc, Ev.loadAddr?, stmtLoad?, List.filterMap_cons, List.filterMap_nil]

/-- A statement's `frameAddr` run: its first value and its length. -/
def stmtRun? : Stmt → Option (V × ℕ)
  | .atom (.frameAddr _ (r :: rs)) => some (r, rs.length + 1)
  | _ => none

theorem runs_straight (σ : Val) : ∀ pre : List Stmt, pre.all Main.Stmt.straight = true →
    runs (pre.flatMap (Main.slEvs σ)) = pre.filterMap stmtRun?
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
      simp [Main.slEvs, hc, Ev.run?, stmtRun?, List.filterMap_cons, List.filterMap_nil]

/-- An atom of a straight body holds when its path's events are `Ok`. -/
theorem atom_holds_of_ok {C : CallRel} {rd : Reader} {σ : Val} {pre : List Stmt} {a : Atom}
    (ha : Stmt.atom a ∈ pre) (h : ∀ e ∈ pre.flatMap (Main.slEvs σ), e.Ok C rd σ) : a.Holds rd σ :=
  (h (.atom a) (List.mem_flatMap.mpr ⟨_, ha, by simp [Main.slEvs]⟩)).1

/-! ## A fused dispatch between straight runs -/

theorem pick_eq (σ : Val) (x : V) (args rets : List V) : ∀ (fs : List String) (j i : ℕ),
    i < fs.length → j + fs.length ≤ 2 ^ 64 - 1 → σ x = ofK (gpow (j + i)) →
    pick σ x args rets j fs = .fall [.call fs[i]! args rets]
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | f :: fs, j, i, hi, hb, hx => by
    simp only [List.length_cons] at hi hb
    unfold pick
    by_cases hxj : σ x = ofK (gpow j)
    · rw [ite_pos' hxj]
      obtain rfl : i = 0 := by
        by_contra h0
        exact ofK_gpow_ne (show j < j + i by omega) (by omega) (hxj.symm.trans hx)
      rfl
    · rw [ite_neg' hxj]
      cases i with
      | zero => exact absurd (by simpa using hx) hxj
      | succ i =>
        rw [pick_eq σ x args rets fs (j + 1) i (by omega) (by omega) (by rw [hx]; congr 2; omega)]
        rfl

/-- **A body: a straight run, a fused dispatch, a straight run, a return**, walks the runs and
the callee the selector picks. -/
theorem walk_dispatch (σ : Val) (pre post : List Stmt) (hpre : pre.all Main.Stmt.straight = true)
    (hpost : post.all Main.Stmt.straight = true) (x : V) (fs : List String) (args rets vs : List V)
    {i : ℕ} (hi : i < fs.length) (hfl : fs.length ≤ 2 ^ 64 - 1) (hx : σ x = ofK (gpow i)) :
    walk σ (pre ++ .dispatch x fs args rets :: (post ++ [.ret vs])) =
      .ret (pre.flatMap (Main.slEvs σ) ++ .call fs[i]! args rets :: post.flatMap (Main.slEvs σ)) vs := by
  induction pre with
  | nil =>
    rw [List.nil_append, walk, walk1, pick_eq σ x args rets fs 0 i hi (by omega) (by rw [Nat.zero_add]; exact hx),
      Main.walk_straight σ vs post hpost]
    rfl
  | cons s pre ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hpre
    rw [List.cons_append, walk, ih hpre.2, Main.walk1_straight σ s hpre.1, Out.seq, Out.pre,
      List.flatMap_cons, List.append_assoc]

end
end LeanVM.Guest.B1.Digest
