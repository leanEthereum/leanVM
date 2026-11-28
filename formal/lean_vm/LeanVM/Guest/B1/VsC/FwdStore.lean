/-
  LeanVM.Guest.B1.VsC.FwdStore

  A straight body that loads input arrays and stores output arrays completes from its meaning.
-/

module

public import LeanVM.Guest.B1.VsC.Fwd

/-!
# Straight bodies with stores

`callCompletes_stores`: a body of atoms then a `ret`, with no assertion or hint, whose loads read
the input arrays `ins` and whose stores (loads into older values) write the output arrays `outs`,
each output word stored once (`storeChecks`, decided by the kernel per function), on arrays at
pairwise distinct addresses (`ArraysApart`). Its meaning gives the output words from the input
words (`hmean`); then on every memory holding the inputs and those outputs it completes.

The proof: on the forward valuation `σ`, the memory `overlay rd S σ` (each store's word at its
address, `rd` elsewhere) satisfies every atom, so the relation holds there; its meaning then says
each stored word is the output word the caller holds, so every store holds on `rd` too.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd

@[expose] public section

/-- A store's address under `σ`. -/
def storeAt (σ : Val) : Atom → Option K
  | .load _ p off => some ((σ p).limb 0 * addressOfIndex off)
  | _ => none

/-- A store's value. -/
def storeVal : Atom → V
  | .load d _ _ => d
  | _ => default

/-- A store's key: its pointer and offset. -/
def storeKey : Atom → V × ℕ
  | .load _ p k => (p, k)
  | _ => (default, 0)

/-- The memory `rd` with each store of `S` written at its address. -/
noncomputable def overlay (rd : Reader) (S : List Atom) (σ : Val) : Reader := fun a =>
  open Classical in
  if h : ∃ s ∈ S, storeAt σ s = some a then some (σ (storeVal (Classical.choose h))) else rd a

theorem overlay_other {rd : Reader} {S : List Atom} {σ : Val} {a : K} (h : ∀ s ∈ S, storeAt σ s ≠ some a) :
    overlay rd S σ a = rd a := by
  unfold overlay
  split
  · next h' => obtain ⟨s, hs, he⟩ := h'; exact absurd he (h s hs)
  · rfl

theorem overlay_store {rd : Reader} {S : List Atom} {σ : Val} {d p : V} {off : ℕ}
    (hu : ∀ s ∈ S, ∀ s' ∈ S, storeAt σ s = storeAt σ s' → storeAt σ s ≠ none → s = s')
    (hm : Atom.load d p off ∈ S) :
    overlay rd S σ ((σ p).limb 0 * addressOfIndex off) = some (σ d) := by
  unfold overlay
  split
  · next h =>
    obtain ⟨hs, he⟩ := Classical.choose_spec h
    have := hu _ hs _ hm (by rw [he]; rfl) (by rw [he]; simp)
    rw [this]
    rfl
  · next h => exact absurd ⟨_, hm, rfl⟩ h

theorem storesOf_mem : ∀ {c : ℕ} {B : List Stmt} {a : Atom}, a ∈ storesOf c B → Stmt.atom a ∈ B
  | _, [], _, h => by simp [storesOf] at h
  | c, s :: ss, a, h => by
    simp only [storesOf, List.mem_append] at h
    rcases h with h | h
    · cases s with
      | atom b =>
        cases b with
        | load d p off =>
          simp only [storeHd] at h
          split at h
          · rw [List.mem_singleton] at h; subst h; exact List.mem_cons_self
          · simp at h
        | _ => simp [storeHd] at h
      | _ => simp [storeHd] at h
    · exact List.mem_cons_of_mem _ (storesOf_mem h)

/-- A load is through an array of `qs` within its length. -/
def inArrays (qs : List (ℕ × ℕ)) (p : V) (k : ℕ) : Bool := qs.any fun q => p == .n q.1 && decide (k < q.2)

/-- An atom of a body with stores `S`: no hint; a store through an output array, any other load
through an input array; any other atom without a side condition. -/
def stOk (ins outs : List (ℕ × ℕ)) (S : List Atom) : Atom → Bool
  | .hint _ => false
  | .load d p k => if Atom.load d p k ∈ S then inArrays outs p k else inArrays ins p k
  | a => !needsSide a

/-- A load. -/
def isLoadB : Atom → Bool
  | .load .. => true
  | _ => false

/-- What the kernel checks of a body with stores on `n` parameters. -/
def storeChecks (n : ℕ) (ins outs : List (ℕ × ℕ)) (B : List Stmt) : Bool :=
  (chk n B).isSome && (retOf B).isSome && (atomsOf B).all (stOk ins outs (storesOf n B)) &&
    ((storesOf n B).map storeKey).Nodup && (storesOf n B).all isLoadB

/-- The arrays lie at pairwise distinct addresses. -/
def ArraysApart (args : List E) (qs : List (ℕ × ℕ)) : Prop :=
  ∀ q ∈ qs, ∀ q' ∈ qs, ∀ a < q.2, ∀ b < q'.2,
    (args.getD q.1 0).limb 0 * addressOfIndex a = (args.getD q'.1 0).limb 0 * addressOfIndex b →
      q.1 = q'.1 ∧ a = b

/-- The memory holds each array's words at its parameter. -/
def HoldsArrays (rd : Reader) (args : List E) (qs : List (ℕ × List E)) : Prop :=
  ∀ q ∈ qs, ReadsAt rd (args.getD q.1 0) q.2

/-- An array's shape: its parameter and length. -/
def shapeOf (qs : List (ℕ × List E)) : List (ℕ × ℕ) := qs.map fun q => (q.1, q.2.length)

theorem inArrays_spec {qs : List (ℕ × List E)} {p : V} {k : ℕ} (h : inArrays (shapeOf qs) p k = true) :
    ∃ q ∈ qs, p = .n q.1 ∧ k < q.2.length := by
  simp only [inArrays, shapeOf, List.any_map, List.any_eq_true, Function.comp, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨q, hq, h1, h2⟩ := h
  exact ⟨q, hq, h1, h2⟩

theorem readsAt_load {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) {k : ℕ} (hk : k < l.length) :
    LoadHolds rd p k (l.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

/-- A non-memory atom's equation does not read the memory. -/
theorem good_reader {rd rd' : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {a : Atom}
    (hl : isLoadB a = false) (hn : needsSide a = false) (hh : noHint a = true) (h : Good rd S w σ a) :
    Good rd' S w σ a := by
  cases a with
  | hint => simp [noHint] at hh
  | load => simp [isLoadB] at hl
  | touch => simp [needsSide] at hn
  | rangeCheck => simp [needsSide] at hn
  | _ => exact h

/-- **A body with stores completes**, from its meaning. -/
theorem callCompletes_stores {k : ℕ} {name : String} {fn : Fn} {args rets : List E}
    (ins outs : List (ℕ × List E)) (hfind : coreProgram.find? name = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hck : storeChecks args.length (shapeOf ins) (shapeOf outs) fn.body = true)
    (hargs : ∀ q ∈ ins ++ outs, q.1 < args.length)
    (hio : ∀ q ∈ ins, ∀ q' ∈ outs, q.1 ≠ q'.1)
    (hapart : ArraysApart args (shapeOf (ins ++ outs)))
    (hmean : ∀ rd', HoldsArrays rd' args ins → ∀ rets', coreProgram.Rel rd' name args rets' →
      HoldsArrays rd' args outs ∧ rets' = rets) :
    CallCompletes k name args rets (fun rd => HoldsArrays rd args ins ∧ HoldsArrays rd args outs)
      PostQuiet := by
  simp only [storeChecks, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨hc, hr⟩, hok⟩, hnd⟩, hSl⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  set S := storesOf args.length fn.body with hSdef
  have hmem : ∀ a, Stmt.atom a ∈ ss → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody]; exact List.mem_append_left _ ha
  have hst : ∀ a, Stmt.atom a ∈ fn.body → stOk (shapeOf ins) (shapeOf outs) S a = true := fun a ha =>
    List.all_eq_true.mp hok a (mem_atomsOf' ha)
  have hq : (atomsOf ss).all atomQuiet = true := List.all_eq_true.mpr fun a ha => by
    have := hst a (hmem a (mem_of_mem_atomsOf ha))
    cases a with
    | hint hh => simp [stOk] at this
    | _ => rfl
  -- the shape of a store and of any other load
  have hS : ∀ a ∈ S, ∃ d q off, a = .load d (.n q.1) off ∧ q ∈ outs ∧ off < q.2.length := by
    intro a ha
    have hl := List.all_eq_true.mp hSl a ha
    have h := hst a (storesOf_mem ha)
    cases a with
    | load d p off =>
      simp only [stOk, ha, ↓reduceIte] at h
      obtain ⟨q, hq, rfl, hk⟩ := inArrays_spec h
      exact ⟨d, q, off, rfl, hq, hk⟩
    | _ => simp [isLoadB] at hl
  have hL : ∀ d p off, Stmt.atom (.load d p off) ∈ fn.body → Atom.load d p off ∉ S →
      ∃ q ∈ ins, p = .n q.1 ∧ off < q.2.length := by
    intro d p off hm hns
    have h := hst _ hm
    simp only [stOk, hns, ↓reduceIte] at h
    exact inArrays_spec h
  refine callCompletes_straightRd (fun rd => fwdVal rd (fun _ => 0) args fn.body) hfind hbody hss hq
    fun rd hl ⟨hin, hout⟩ => ?_
  set σ := fwdVal rd (fun _ => 0) args fn.body with hσ
  have G : ∀ a, Stmt.atom a ∈ fn.body → Good rd S (fun _ => 0) σ a := fwd_good hc
  have hpar : ∀ q ∈ ins ++ outs, σ (.n q.1) = args.getD q.1 0 := fun q hq => fwd_param hc (hargs q hq)
  have hpI : ∀ q ∈ ins, σ (.n q.1) = args.getD q.1 0 := fun q hq => hpar q (List.mem_append_left _ hq)
  have hpO : ∀ q ∈ outs, σ (.n q.1) = args.getD q.1 0 := fun q hq => hpar q (List.mem_append_right _ hq)
  have hshI : ∀ q ∈ ins, (q.1, q.2.length) ∈ shapeOf (ins ++ outs) := fun q hq =>
    List.mem_map.mpr ⟨q, List.mem_append_left _ hq, rfl⟩
  have hshO : ∀ q ∈ outs, (q.1, q.2.length) ∈ shapeOf (ins ++ outs) := fun q hq =>
    List.mem_map.mpr ⟨q, List.mem_append_right _ hq, rfl⟩
  -- distinct stores lie at distinct addresses
  have hu : ∀ s ∈ S, ∀ s' ∈ S, storeAt σ s = storeAt σ s' → storeAt σ s ≠ none → s = s' := by
    intro s hs s' hs' he _
    obtain ⟨d, q, off, rfl, hq, hk⟩ := hS s hs
    obtain ⟨d', q', off', rfl, hq', hk'⟩ := hS s' hs'
    simp only [storeAt, Option.some.injEq, hpO q hq, hpO q' hq'] at he
    obtain ⟨e1, e2⟩ := hapart _ (hshO q hq) _ (hshO q' hq') off hk off' hk' he
    refine List.inj_on_of_nodup_map hnd hs hs' ?_
    have e1' : q.1 = q'.1 := e1
    have e2' : off = off' := e2
    simp only [storeKey, e1', e2']
  set rdS := overlay rd S σ with hrdS
  -- a load not stored reads an input word, the same on both memories
  have hnew : ∀ d p off, Stmt.atom (.load d p off) ∈ fn.body → Atom.load d p off ∉ S →
      LoadHolds rd (σ p) off (σ d) ∧ LoadHolds rdS (σ p) off (σ d) := by
    intro d p off hm hns
    obtain ⟨q, hq, rfl, hk⟩ := hL d p off hm hns
    have hld := readsAt_load (hin q hq) hk
    have hd : σ d = q.2.getD off 0 := by
      rw [← hpI q hq] at hld; exact good_load_eq hld (G _ hm) hns
    rw [hd, hpI q hq]
    refine ⟨hld, hld.1, ?_⟩
    rw [hrdS, overlay_other, hld.2]
    intro s hs he
    obtain ⟨d', q', off', rfl, hq', hk'⟩ := hS s hs
    simp only [storeAt, Option.some.injEq, hpO q' hq'] at he
    obtain ⟨e1, -⟩ := hapart _ (hshO q' hq') _ (hshI q hq) off' hk' off hk he
    exact hio q hq q' hq' (show q'.1 = q.1 from e1).symm
  -- every atom holds on the overlay
  have hAS : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rdS σ := by
    intro a ha
    have hb := atoms_holds (rd := rdS) (S := S) (w := fun _ => 0) (σ := σ) (atoms := [a])
      (fun b hb => by
        rw [List.mem_singleton] at hb; subst hb
        cases hlb : isLoadB b
        · cases hnb : needsSide b
          · have := hst b ha
            refine good_reader hlb hnb ?_ (G b ha)
            cases b with
            | hint => simp [stOk] at this
            | _ => rfl
          · have := hst b ha
            cases b with
            | load => simp [isLoadB] at hlb
            | hint => simp [stOk] at this
            | _ => simp only [stOk, hnb, Bool.not_true, Bool.false_eq_true] at this
        · cases b with
          | load d p off =>
            by_cases hbs : Atom.load d p off ∈ S
            · exact Or.inl hbs
            · right; rw [rdAt, (hnew d p off ha hbs).2.2]; rfl
          | _ => simp [isLoadB] at hlb)
      (fun b hb hn => by
        rw [List.mem_singleton] at hb; subst hb
        have h := hst b ha
        cases b with
        | load d p off =>
          by_cases hbs : Atom.load d p off ∈ S
          · right
            simp only [Side, hbs, ↓reduceIte]
            obtain ⟨d', q, off', he, hq, hk⟩ := hS _ hbs
            obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj he
            refine ⟨?_, overlay_store hu hbs⟩
            rw [hpO q hq]; exact (readsAt_load (hout q hq) hk).1
          · exact Or.inl (hnew d p off ha hbs).2
        | hint => simp [stOk] at h
        | _ => simp only [stOk, hn, Bool.not_true, Bool.false_eq_true] at h)
    exact hb a List.mem_cons_self
  have hp : fn.params.map σ = args := by rw [hparams]; exact fwd_params hc
  have hRel : ∀ rd', (∀ a, Stmt.atom a ∈ fn.body → a.Holds rd' σ) → coreProgram.Rel rd' name args (vs.map σ) :=
    fun rd' hA => (rel_iff_sem hfind _ _).mpr ⟨σ, hp, by
      rw [hbody, holdsList_append]
      exact (holdsList_atoms hss _ _).mpr ⟨fun a ha => hA a (hmem a ha), by simp [Stmt.HoldsList, Stmt.Holds]⟩⟩
  -- the overlay holds the inputs, so its meaning gives each stored word
  have hinS : HoldsArrays rdS args ins := by
    intro q hq i hi
    have hld := hin q hq i hi
    refine ⟨hld.1, ?_⟩
    rw [hrdS, overlay_other, hld.2]
    intro s hs he
    obtain ⟨d', q', off', rfl, hq', hk'⟩ := hS s hs
    simp only [storeAt, Option.some.injEq, hpO q' hq'] at he
    obtain ⟨e1, -⟩ := hapart _ (hshO q' hq') _ (hshI q hq) off' hk' i hi he
    exact hio q hq q' hq' (show q'.1 = q.1 from e1).symm
  obtain ⟨houtS, -⟩ := hmean rdS hinS _ (hRel rdS hAS)
  have hstore : ∀ d p off, Atom.load d p off ∈ S → LoadHolds rd (σ p) off (σ d) := by
    intro d p off hbs
    obtain ⟨d', q, off', he, hq, hk⟩ := hS _ hbs
    obtain ⟨rfl, rfl, rfl⟩ := Atom.load.inj he
    have h1 := readsAt_load (houtS q hq) hk
    have h2 := readsAt_load (hout q hq) hk
    rw [← hpO q hq] at h1 h2
    have := overlay_store (rd := rd) hu hbs
    rw [← hrdS, h1.2] at this
    rw [← Option.some.inj this]
    exact h2
  -- every atom holds on `rd`
  have hA : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ := by
    refine fwd_holds hc fun a ha hn => ?_
    have h := hst a ha
    cases a with
    | load d p off =>
      by_cases hbs : Atom.load d p off ∈ S
      · exact Or.inl (hstore d p off hbs)
      · exact Or.inl (hnew d p off ha hbs).1
    | hint => simp [stOk] at h
    | _ => simp only [stOk, hn, Bool.not_true, Bool.false_eq_true] at h
  obtain ⟨-, hret⟩ := hmean rd hin _ (hRel rd hA)
  refine ⟨hp, hret, fun a ha => ⟨hA a (hmem a ha), ?_⟩⟩
  have := hst a (hmem a ha)
  cases a with
  | hint => simp [stOk] at this
  | _ => trivial

end
end LeanVM.Guest.B1.VsC
