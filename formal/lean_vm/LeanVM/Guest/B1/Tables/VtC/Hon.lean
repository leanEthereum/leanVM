/-
  LeanVM.Guest.B1.Tables.VtC.Hon

  `verify_tables`' honest valuation on a memory: its evaluation list evaluated from the arguments,
  loads read from the memory, allocations, hints' and callees' words from an oracle. What it
  gives by position, and the statements that hold by it alone.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.NotStored
public import LeanVM.Guest.B1.Tables.VtC.Glue

/-!
# The honest valuation

`vtσ rd w args`: `vtEvL` evaluated (`Fwd.ev`) on the memory `rd` and the oracle `w` from the
arguments `args`. Each statement of the list satisfies its equations (`Good`, `GoodS`) with the
stores `vtSL` (`vt_good`); the parameters are the arguments (`vt_param`).

By position of `vtPre` (the kernel comparing the statements read): `vt_goodL` (a block's
equations, as one conjunction), `vt_goodIte` (an `ite`'s branches'), `vt_read` (a read gives the
word the memory holds).

**What holds by evaluation alone** (`autoB`): constants, sums, copies, products of older values,
hints. `vt_block`: a block's statements satisfy `VSH` when the others (`rest`, a filter the
kernel computes) do. `vt_loadsBelow`/`vt_bufRead`: every load through a pointer of a buffer whose
words the memory holds stays inside it (one kernel check), a read reads the buffer's word.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- **The honest valuation** of `verify_tables` on the memory `rd`, the oracle `w` and the
arguments `args`. -/
noncomputable def vtσ (rd : Reader) (w : ℕ → E) (args : List E) : Val :=
  B1.Val.ofArgs (ev rd w args vtEvL)

/-- The equations of a block, as one conjunction. -/
def GoodL (rd : Reader) (w : ℕ → E) (σ : Val) : List Stmt → Prop
  | [] => True
  | s :: ss => GoodS rd vtSL w σ (fixNe s) ∧ GoodL rd w σ ss

/-- A statement of the body, not an `ite`, is in the list as `fixNe` reads it. -/
theorem vtEvL_mem {s : Stmt} (hs : s ∈ vtPre) (hni : ∀ c z n, s ≠ .ite c z n) :
    fixNe s ∈ vtEvL :=
  List.mem_map_of_mem (mem_flatIte_of hni hs)

/-- An `ite`'s branches are in the list. -/
theorem vtEvL_mem_ite {c : V} {z n : List Stmt} (hs : Stmt.ite c z n ∈ vtPre) {t : Stmt}
    (ht : t ∈ z ++ n) : fixNe t ∈ vtEvL :=
  List.mem_map_of_mem (mem_flatIte_ite hs t ht)

/-- The statement at a position of the body, by kernel comparison. -/
theorem vt_mem_at (p : ℕ) (s : Stmt) (h : tbStmtsEqb [s] ((vtPre.drop p).take 1) = true) :
    s ∈ vtPre := by
  have e := tbStmtsEqb_sound h
  have : s ∈ (vtPre.drop p).take 1 := by rw [← e]; simp
  exact List.mem_of_mem_drop (List.mem_of_mem_take this)

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vt_good (hl : args.length = 20) : ∀ s ∈ vtEvL, GoodS rd vtSL w (vtσ rd w args) s := by
  have h := (ev_spec rd w vtEvL args (by rw [hl]; exact vt_chk)).2.2
  rw [hl, vt_stores] at h
  exact h

theorem vt_param (hl : args.length = 20) {i : ℕ} (hi : i < 20) :
    vtσ rd w args (.n i) = args.getD i 0 :=
  ev_params rd w (by rw [hl]; exact vt_chk) (by rw [hl]; exact hi)

/-! ## By position -/

theorem vt_mem_slice {n : ℕ} {blk : List Stmt}
    (heq : tbStmtsEqb blk ((vtPre.drop n).take blk.length) = true) {s : Stmt} (hs : s ∈ blk) :
    s ∈ vtPre := by
  rw [tbStmtsEqb_sound heq] at hs
  exact List.mem_of_mem_drop (List.mem_of_mem_take hs)

theorem vt_goodS (hl : args.length = 20) {s : Stmt} (hs : s ∈ vtPre) :
    GoodS rd vtSL w (vtσ rd w args) (fixNe s) := by
  by_cases hi : ∃ c z n, s = .ite c z n
  · obtain ⟨c, z, n, rfl⟩ := hi
    trivial
  · exact vt_good hl _ (vtEvL_mem hs fun c z n h ↦ hi ⟨c, z, n, h⟩)

/-- **A block's equations**, read at position `n`. -/
theorem vt_goodL (hl : args.length = 20) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((vtPre.drop n).take blk.length) = true) :
    GoodL rd w (vtσ rd w args) blk := by
  have h : ∀ s ∈ blk, GoodS rd vtSL w (vtσ rd w args) (fixNe s) :=
    fun s hs ↦ vt_goodS hl (vt_mem_slice heq hs)
  clear heq
  induction blk with
  | nil => trivial
  | cons s ss ih =>
    exact ⟨h s List.mem_cons_self, ih fun t ht ↦ h t (List.mem_cons_of_mem _ ht)⟩

/-- **A read** gives the word at its address (`0` if none). -/
theorem vt_read (hl : args.length = 20) (n : ℕ) {d p : V} {off : ℕ}
    (heq : tbStmtsEqb [.atom (.load d p off)] ((vtPre.drop n).take 1) = true)
    (hS : Atom.load d p off ∉ vtSL) :
    vtσ rd w args d = rdAt rd (vtσ rd w args p) off := by
  have h := vt_goodS (rd := rd) (w := w) hl (vt_mem_slice (blk := [_]) heq List.mem_cons_self)
  simp only [fixNe, GoodS, Good] at h
  exact h.resolve_left hS

/-- A read of a word the memory holds holds, and reads it. -/
theorem vt_readH (hl : args.length = 20) (n : ℕ) {d p : V} {off : ℕ}
    (heq : tbStmtsEqb [.atom (.load d p off)] ((vtPre.drop n).take 1) = true)
    (hS : Atom.load d p off ∉ vtSL) {v : E} (hm : LoadHolds rd (vtσ rd w args p) off v) :
    vtσ rd w args d = v ∧ VSH (coreProgram.Rel rd) rd (vtσ rd w args) (.atom (.load d p off)) := by
  have e : vtσ rd w args d = v := by
    rw [vt_read hl n heq hS, rdAt, hm.2]; rfl
  refine ⟨e, ?_⟩
  show LoadHolds rd _ _ _
  rw [e]; exact hm

/-- A store of the word the memory holds holds. -/
theorem vsh_store {σ : Val} {d p : V} {off : ℕ} {v : E} (hm : LoadHolds rd (σ p) off v)
    (hv : σ d = v) : VSH (coreProgram.Rel rd) rd σ (.atom (.load d p off)) := by
  show LoadHolds rd _ _ _
  rw [hv]; exact hm

/-! ## What holds by evaluation alone -/

theorem vsh_auto (hl : args.length = 20) {s : Stmt} (hs : s ∈ vtPre) (ha : autoB s = true) :
    VSH (coreProgram.Rel rd) rd (vtσ rd w args) s := by
  cases s with
  | atom a =>
    have hg := vt_goodS (rd := rd) (w := w) hl hs
    rw [fixNe_atom] at hg
    simp only [autoB, Bool.or_eq_true] at ha
    rcases ha with ha | ha
    · have e : fixA a = a := by
        cases a with
        | assertNe => simp [pureB] at ha
        | _ => rfl
      rw [e] at hg
      exact holds_of_pure (S := vtSL) (w := w) ha hg
    · cases a with
      | hint _ => exact True.intro
      | _ => simp only [hintB, Bool.false_eq_true] at ha
  | _ => simp only [autoB, Bool.false_eq_true] at ha

/-- **A block's statements hold** when the ones evaluation alone does not settle (`rest`) do. -/
theorem vt_block (hl : args.length = 20) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((vtPre.drop n).take blk.length) = true) (rest : List Stmt)
    (hrest : tbStmtsEqb (blk.filter (fun s ↦ !autoB s)) rest = true)
    (h : ∀ s ∈ rest, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) :
    ∀ s ∈ blk, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s := by
  intro s hs
  cases ha : autoB s
  · exact h s (tbStmtsEqb_sound hrest ▸ List.mem_filter.mpr ⟨hs, by simp [ha]⟩)
  · exact vsh_auto hl (vt_mem_slice heq hs) ha

/-! ## At `vtAt`: what a kernel check evaluates fast -/

theorem vt_memAt (n : ℕ) (s : Stmt) (heq : tbStmtsEqb [s] ((vtAt n).take 1) = true) :
    s ∈ vtPre :=
  vt_mem_slice (blk := [_]) (vtPre_drop n ▸ heq) List.mem_cons_self

/-- The equations of the statement at position `n`, read at `vtAt`. -/
theorem vt_goodAt (hl : args.length = 20) (n : ℕ) (s : Stmt)
    (heq : tbStmtsEqb [s] ((vtAt n).take 1) = true) :
    GoodS rd vtSL w (vtσ rd w args) (fixNe s) :=
  (vt_goodL (rd := rd) (w := w) hl n [s] (vtPre_drop n ▸ heq)).1

theorem vt_copyAt (hl : args.length = 20) (n : ℕ) {d x : V}
    (heq : tbStmtsEqb [.atom (.copy d x)] ((vtAt n).take 1) = true) :
    vtσ rd w args d = vtσ rd w args x :=
  vt_goodAt (rd := rd) (w := w) hl n _ heq

theorem vt_constAt (hl : args.length = 20) (n : ℕ) {d : V} {e : E}
    (heq : tbStmtsEqb [.atom (.const d e)] ((vtAt n).take 1) = true) : vtσ rd w args d = e :=
  vt_goodAt (rd := rd) (w := w) hl n _ heq

theorem vt_allocAt (hl : args.length = 20) (n : ℕ) {d : V} {k : ℕ}
    (heq : tbStmtsEqb [.atom (.hint (.alloc d k))] ((vtAt n).take 1) = true) :
    vtσ rd w args d = w d.idx :=
  vt_goodAt (rd := rd) (w := w) hl n _ heq

theorem vt_allocDynAt (hl : args.length = 20) (n : ℕ) {d s : V}
    (heq : tbStmtsEqb [.atom (.hint (.allocDyn d s))] ((vtAt n).take 1) = true) :
    vtσ rd w args d = w d.idx :=
  vt_goodAt (rd := rd) (w := w) hl n _ heq

theorem vt_mulAt (hl : args.length = 20) (n : ℕ) {d x y : ℕ} (hx : x < d) (hy : y < d)
    (heq : tbStmtsEqb [.atom (.mul (.n d) (.n x) (.n y))] ((vtAt n).take 1) = true) :
    vtσ rd w args (.n d) = vtσ rd w args (.n x) * vtσ rd w args (.n y) := by
  have h := vt_goodAt (rd := rd) (w := w) hl n _ heq
  simp only [GoodS, fixNe, Good] at h
  rw [ite_pos' ⟨hx, hy⟩] at h
  exact h

/-- **A read at `vtAt`** of a word the memory holds holds, and reads it. -/
theorem vt_readAt (hl : args.length = 20) (n : ℕ) {d p : V} {off : ℕ}
    (heq : tbStmtsEqb [.atom (.load d p off)] ((vtAt n).take 1) = true)
    (hS : Atom.load d p off ∉ vtSL) {v : E} (hm : LoadHolds rd (vtσ rd w args p) off v) :
    vtσ rd w args d = v ∧ VSH (coreProgram.Rel rd) rd (vtσ rd w args) (.atom (.load d p off)) :=
  vt_readH hl n (vtPre_drop n ▸ heq) hS hm

/-- **A slice holds** when its statements beyond evaluation (`rest`, the kernel's filter) do. -/
theorem vt_blockR (hl : args.length = 20) (a len : ℕ) (rest : List Stmt)
    (hrest : tbStmtsEqb (((vtAt a).take len).filter (fun s ↦ !autoB s)) rest = true)
    (h : ∀ s ∈ rest, s ∈ vtPre → VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) :
    ∀ s ∈ (vtPre.drop a).take len, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s := by
  rw [← vtPre_drop] at hrest
  intro s hs
  have hm : s ∈ vtPre := List.mem_of_mem_drop (List.mem_of_mem_take hs)
  cases ha : autoB s
  · exact h s (tbStmtsEqb_sound hrest ▸ List.mem_filter.mpr ⟨hs, by simp [ha]⟩) hm
  · exact vsh_auto hl hm ha

/-- Two adjacent slices hold, so does their union. -/
theorem forall_slice_join {P : Stmt → Prop} {a l1 l2 : ℕ}
    (h1 : ∀ s ∈ (vtPre.drop a).take l1, P s) (h2 : ∀ s ∈ (vtPre.drop (a + l1)).take l2, P s) :
    ∀ s ∈ (vtPre.drop a).take (l1 + l2), P s := by
  intro s hs
  rw [List.take_add, List.mem_append] at hs
  rcases hs with hs | hs
  · exact h1 s hs
  · rw [List.drop_drop] at hs
    exact h2 s hs

/-! ## Buffers -/

/-- Every load of `vtEvL` through a pointer `.n p` with `(p, b) ∈ ps` is at an offset below `b`. -/
noncomputable def loadsBelow (ps : List (ℕ × ℕ)) : Bool :=
  vtEvL.all fun s ↦ match s with
    | .atom (.load _ (.n p) off) => ps.all fun q ↦ !(q.1 == p) || decide (off < q.2)
    | _ => true

/-- **A load through a buffer's pointer**, the memory holding at least `b` of its words `W`, with
every load through it below `b` (`loadsBelow`): the memory holds the word at its offset, and a
read reads it. -/
theorem vt_bufLoad (hl : args.length = 20) {ps : List (ℕ × ℕ)} (hok : loadsBelow ps = true)
    {p b : ℕ} (hpb : (p, b) ∈ ps) {W : List E} (hW : TbReadsAt rd (vtσ rd w args (.n p)) W)
    (hb : b ≤ W.length) {d : V} {off : ℕ} (hs : Stmt.atom (.load d (.n p) off) ∈ vtEvL) :
    LoadHolds rd (vtσ rd w args (.n p)) off (W.getD off 0) ∧
      (Atom.load d (.n p) off ∉ vtSL → vtσ rd w args d = W.getD off 0) := by
  have hoff : off < b := by
    have := List.all_eq_true.mp hok _ hs
    simp only at this
    have := List.all_eq_true.mp this _ hpb
    simpa using this
  have hm : LoadHolds rd (vtσ rd w args (.n p)) off (W.getD off 0) := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hW off (by omega)
  refine ⟨hm, fun hS ↦ ?_⟩
  have h := vt_good (rd := rd) (w := w) hl _ hs
  simp only [GoodS, Good] at h
  rw [h.resolve_left hS, rdAt, hm.2]
  rfl

end

end
end LeanVM.Guest.B1.Tables
