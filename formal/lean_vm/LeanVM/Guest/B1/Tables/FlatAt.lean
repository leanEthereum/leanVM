/-
  LeanVM.Guest.B1.Tables.FlatAt

  Ported from leanVM `3f7dc219`'s `B1/Tables/FlatAt.lean` onto `Memory/Uniform.lean`, the branches'
  atoms allowed any hint but a `HeapBuf`.

  Flat bodies (straight-line statements, branches over plain atoms, dispatches on a power of `g`),
  complete in the uniform placed form.
-/

module

public import LeanVM.Guest.Memory.Uniform

/-!
# Flat bodies, placed

A statement is **flat** (`Stmt.flat`) when it is an atom, a call, a conditional call, a dispatch,
or a branch both of whose arms are plain atoms (no load, no `HeapBuf` hint, no `frameAddr`). A flat body's
path (`flEvs`) is its statements' events in turn, a branch contributing its condition and the
taken arm's atoms, a dispatch its entered callee (`walk_flat`), so its `HeapBuf`s, `frameAddr`s
and loads are its top-level statements' and its frames its calls' and dispatches'
(`flat_parts`). `completeAt_flatD` is `completeAt_straightD` for flat bodies.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- An atom that neither allocates nor places a run. -/
def _root_.LeanVM.Guest.Core.Atom.plain : Atom → Bool
  | .hint (.alloc ..) => false
  | .hint (.allocDyn ..) => false
  | .frameAddr .. => false
  | _ => true

/-- A plain atom statement. -/
def _root_.LeanVM.Guest.Core.Stmt.plainS : Stmt → Bool
  | .atom a => a.plain
  | _ => false

/-- A flat statement. -/
def _root_.LeanVM.Guest.Core.Stmt.flat : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | .callIf .. => true
  | .dispatch .. => true
  | .ite _ z n => z.all Stmt.plainS && n.all Stmt.plainS
  | _ => false

/-- The events of a list of atom statements. -/
def atomsOf (l : List Stmt) : List Ev := l.filterMap fun s => match s with
  | .atom a => some (.atom a)
  | _ => none

/-- The events of a flat statement. -/
noncomputable def flEvs (σ : Val) : Stmt → List Ev
  | .ite c z n => .inK c :: atomsOf (if σ c = 0 then z else n)
  | .dispatch x fs args rets => [.call (fs.getD (logG (σ x)) "") args rets]
  | s => Main.slEvs σ s

/-- A dispatch's selector is a power of `g` naming one of its callees. -/
def DispOk (σ : Val) : Stmt → Prop
  | .dispatch x fs _ _ => ∃ j < fs.length, j < 2 ^ 64 - 1 ∧ σ x = ofK (addressOfIndex j)
  | _ => True

/-- The frame a flat statement sets up. -/
noncomputable def _root_.LeanVM.Guest.Core.Stmt.callSF (σ : Val) : Stmt → Option (Option V × String × List V × List V)
  | .dispatch x fs args rets => some (none, fs.getD (logG (σ x)) "", args, rets)
  | s => Main.Stmt.callS s

theorem walk_plainAtoms (σ : Val) : ∀ l : List Stmt, l.all Stmt.plainS = true → walk σ l = .fall (atomsOf l)
  | [], _ => rfl
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    match s, h.1 with
    | .atom a, _ =>
      rw [walk, walk1, walk_plainAtoms σ l h.2, Out.seq, Out.pre]
      rfl

theorem walk1_flat (σ : Val) : ∀ s : Stmt, s.flat = true → DispOk σ s → walk1 σ s = .fall (flEvs σ s)
  | .atom _, _, _ => rfl
  | .call .., _, _ => rfl
  | .callIf .., _, _ => rfl
  | .ite c z n, h, _ => by
    simp only [Stmt.flat, Bool.and_eq_true] at h
    rw [walk1, flEvs]
    split
    · rw [walk_plainAtoms σ z h.1]; rfl
    · rw [walk_plainAtoms σ n h.2]; rfl
  | .dispatch x fs args rets, _, ⟨j, hj, hj64, hx⟩ => by
    rw [walk1, pick_eq σ x args rets fs 0 j (Nat.zero_le _) (by omega) hj64 hx, flEvs, hx,
      logG_spec hj64, List.getD_eq_getElem _ _ hj]
    simp only [Nat.sub_zero]
  | .match_ .., h, _ => by simp [Stmt.flat] at h
  | .ret _, h, _ => by simp [Stmt.flat] at h

/-- **A flat body walks every statement.** -/
theorem walk_flat (σ : Val) (vs : List V) : ∀ pre : List Stmt, pre.all Stmt.flat = true →
    (∀ s ∈ pre, DispOk σ s) → walk σ (pre ++ [.ret vs]) = .ret (pre.flatMap (flEvs σ)) vs
  | [], _, _ => by simp [walk, walk1, Out.seq]
  | s :: pre, h, hd => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_flat σ vs pre h.2 (fun s' hs' => hd s' (by simp [hs'])),
      walk1_flat σ s h.1 (hd s (by simp)), Out.seq, Out.pre, List.flatMap_cons]

theorem atom_plain_parts (σ : Val) (a : Atom) (h : a.plain = true) :
    Ev.allocDst? (.atom a) = none ∧ Ev.alloc? σ (.atom a) = none ∧ Ev.addr? (.atom a) = none ∧
      Ev.call? (.atom a) = none := by
  cases a with
  | hint hk => cases hk <;> first | exact ⟨rfl, rfl, rfl, rfl⟩ | simp [Atom.plain] at h
  | _ => first | exact ⟨rfl, rfl, rfl, rfl⟩ | simp [Atom.plain] at h

/-- What the events of a list of plain atoms place, call and load: no buffer, no run, no frame,
their loads. -/
theorem atomsOf_parts (σ : Val) : ∀ l : List Stmt, l.all Stmt.plainS = true →
    (atomsOf l).filterMap Ev.allocDst? = [] ∧ (atomsOf l).filterMap (Ev.alloc? σ) = [] ∧
      (atomsOf l).filterMap Ev.addr? = [] ∧ (atomsOf l).filterMap Ev.call? = [] ∧
      (atomsOf l).filterMap (Ev.loadAddr? σ) =
        (l.filterMap Stmt.loadS).map fun q => (σ q.1).limb 0 * addressOfIndex q.2
  | [], _ => by simp [atomsOf]
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨i1, i2, i3, i4, i5⟩ := atomsOf_parts σ l h.2
    match s, h.1 with
    | .atom a, ha =>
      obtain ⟨k1, k2, k3, k4⟩ := atom_plain_parts σ a ha
      simp only [atomsOf, List.filterMap_cons] at i1 i2 i3 i4 i5 ⊢
      simp only [k1, k2, k3, k4]
      refine ⟨i1, i2, i3, i4, ?_⟩
      cases a <;> simp [Ev.loadAddr?, Stmt.loadS, i5]

/-- The loads a flat statement makes under `σ`: an `ite`'s taken branch's, or its own. -/
noncomputable def loadsEv (σ : Val) : Stmt → List (V × ℕ)
  | .ite c z n => (if σ c = 0 then z else n).filterMap Stmt.loadS
  | s => (Stmt.loadS s).toList

/-- No load in a branch. -/
def noLoadIte : Stmt → Bool
  | .ite _ z n => (z ++ n).all fun t ↦ match t with
    | .atom (.load ..) => false
    | _ => true
  | _ => true

theorem flatMap_loadsEv (σ : Val) : ∀ pre : List Stmt, pre.all noLoadIte = true →
    pre.flatMap (loadsEv σ) = pre.filterMap Stmt.loadS
  | [], _ => rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.flatMap_cons, List.filterMap_cons, flatMap_loadsEv σ pre h.2]
    cases s with
    | ite c z n =>
      have hz : (if σ c = 0 then z else n).filterMap Stmt.loadS = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro t ht
        have hall := h.1
        simp only [noLoadIte, List.all_eq_true] at hall
        have := hall t (by split at ht <;> simp [ht])
        cases t with
        | atom a => cases a <;> simp_all [Stmt.loadS]
        | _ => rfl
      simp [loadsEv, hz, Stmt.loadS]
    | atom a => cases a <;> simp [loadsEv, Stmt.loadS]
    | _ => simp [loadsEv, Stmt.loadS]

/-- What one flat statement places, calls and loads. -/
theorem flEvs_parts (σ : Val) (s : Stmt) (hs : s.flat = true) :
    (flEvs σ s).filterMap Ev.allocDst? = ((Main.Stmt.allocSz s).map Prod.fst).toList ∧
    (flEvs σ s).filterMap (Ev.alloc? σ) =
      ((Main.Stmt.allocSz s).map fun x => x.2.elim id fun s => logG (σ s)).toList ∧
    (flEvs σ s).filterMap Ev.addr? = (Main.Stmt.addrS s).toList ∧
    (flEvs σ s).filterMap Ev.call? = ((s.callSF σ).map (Main.mkCall σ)).toList ∧
    (flEvs σ s).filterMap (Ev.loadAddr? σ) = (loadsEv σ s).map fun q => (σ q.1).limb 0 * addressOfIndex q.2 := by
  have hstr : ∀ t : Stmt, Main.Stmt.straight t = true → flEvs σ t = Main.slEvs σ t →
      t.callSF σ = Main.Stmt.callS t →
      (flEvs σ t).filterMap Ev.allocDst? = ((Main.Stmt.allocSz t).map Prod.fst).toList ∧
      (flEvs σ t).filterMap (Ev.alloc? σ) =
        ((Main.Stmt.allocSz t).map fun x => x.2.elim id fun s => logG (σ s)).toList ∧
      (flEvs σ t).filterMap Ev.addr? = (Main.Stmt.addrS t).toList ∧
      (flEvs σ t).filterMap Ev.call? = ((t.callSF σ).map (Main.mkCall σ)).toList ∧
      (flEvs σ t).filterMap (Ev.loadAddr? σ) =
        ((Stmt.loadS t).map fun q => (σ q.1).limb 0 * addressOfIndex q.2).toList := by
    intro t ht he hc
    obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ [t] (by simp [ht])
    have i5 := loadAddrs_straight σ [t] (by simp [ht])
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, allocDsts, allocs, addrs, calls,
      loadAddrs] at i1 i2 i3 i4 i5
    rw [he, hc]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [i1]; cases h : Main.Stmt.allocSz t <;> simp [h]
    · rw [i2]; cases h : Main.Stmt.allocSz t <;> simp [h]
    · rw [i3]; cases h : Main.Stmt.addrS t <;> simp [h]
    · rw [i4]; cases h : Main.Stmt.callS t <;> simp [h]
    · rw [i5]; cases h : Stmt.loadS t <;> simp [h]
  have hstr' : ∀ t : Stmt, Main.Stmt.straight t = true → flEvs σ t = Main.slEvs σ t →
      t.callSF σ = Main.Stmt.callS t → loadsEv σ t = (Stmt.loadS t).toList →
      (flEvs σ t).filterMap Ev.allocDst? = ((Main.Stmt.allocSz t).map Prod.fst).toList ∧
      (flEvs σ t).filterMap (Ev.alloc? σ) =
        ((Main.Stmt.allocSz t).map fun x => x.2.elim id fun s => logG (σ s)).toList ∧
      (flEvs σ t).filterMap Ev.addr? = (Main.Stmt.addrS t).toList ∧
      (flEvs σ t).filterMap Ev.call? = ((t.callSF σ).map (Main.mkCall σ)).toList ∧
      (flEvs σ t).filterMap (Ev.loadAddr? σ) = (loadsEv σ t).map fun q => (σ q.1).limb 0 * addressOfIndex q.2 := by
    intro t ht he hc hl
    obtain ⟨i1, i2, i3, i4, i5⟩ := hstr t ht he hc
    refine ⟨i1, i2, i3, i4, ?_⟩
    rw [i5, hl]; cases Stmt.loadS t <;> rfl
  match s, hs with
  | .atom a, _ => exact hstr' _ rfl rfl rfl (by cases a <;> rfl)
  | .call .., _ => exact hstr' _ rfl rfl rfl rfl
  | .callIf .., _ => exact hstr' _ rfl rfl rfl rfl
  | .ite c z n, h =>
    simp only [Stmt.flat, Bool.and_eq_true] at h
    obtain ⟨i1, i2, i3, i4, i5⟩ := atomsOf_parts σ (if σ c = 0 then z else n)
      (by split; exacts [h.1, h.2])
    simp only [flEvs, List.filterMap_cons, Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?,
      Ev.loadAddr?, i1, i2, i3, i4, i5, loadsEv]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
  | .dispatch x fs args rets, _ =>
    simp only [flEvs, Stmt.callSF, List.filterMap_cons, List.filterMap_nil, Ev.allocDst?, Ev.alloc?,
      Ev.addr?, Ev.call?, Ev.loadAddr?, loadsEv, Stmt.loadS]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **What a flat body places, calls and loads**: its top-level statements'. -/
theorem flat_parts (σ : Val) : ∀ pre : List Stmt, pre.all Stmt.flat = true →
    allocDsts (pre.flatMap (flEvs σ)) = (pre.filterMap Main.Stmt.allocSz).map Prod.fst ∧
    allocs σ (pre.flatMap (flEvs σ)) =
      (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) ∧
    addrs (pre.flatMap (flEvs σ)) = pre.filterMap Main.Stmt.addrS ∧
    calls (pre.flatMap (flEvs σ)) = (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) ∧
    loadAddrs σ (pre.flatMap (flEvs σ)) = (pre.flatMap (loadsEv σ)).map fun q => (σ q.1).limb 0 * addressOfIndex q.2
  | [], _ => by simp [allocDsts, allocs, addrs, calls, loadAddrs]
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre h.2
    obtain ⟨j1, j2, j3, j4, j5⟩ := flEvs_parts σ s h.1
    simp only [allocDsts, allocs, addrs, calls, loadAddrs, List.flatMap_cons, List.filterMap_append]
      at i1 i2 i3 i4 i5 ⊢
    rw [i1, i2, i3, i4, i5, j1, j2, j3, j4, j5]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · cases h : Main.Stmt.allocSz s <;> simp [h]
    · cases h : Main.Stmt.allocSz s <;> simp [h]
    · cases h : Main.Stmt.addrS s <;> simp [h]
    · cases h : s.callSF σ <;> simp [h]
    · simp

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A flat function is complete, placed.** -/
theorem completeAt_flatD {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args k.Out)
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (kids fp) outs ∧
        ∀ q ∈ pre.flatMap (loadsEv σ), ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) :
    CompleteAtD fs cert κ f Lin args (Returns rets) := by
  intro fp
  obtain ⟨N, L, outs, ho, hW, hD, -, hK⟩ := kidsFromIn_of_kidsD (fs := fs) (cert := cert) κ (kids fp)
    (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp) ++ L, rets, [], ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  obtain ⟨σ, hp, hdo, hh, hsz, hbuf, hcm, hld⟩ := hσ fp outs ho rd hlow hB hLin
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets := hsat.2
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp)) i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i hi)
  have hk := hK rd σ (calls (pre.flatMap (flEvs σ))) (fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (memL_lins (hkm fp rd hB hLin))
    (regionsOk_of fun k hk ht i hi => Or.inl ((hkr fp k hk ht i hi).imp_right (hown' i)))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp)
    hk (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [hal] at h
    exact h
  · rw [i5] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩


/-- **`completeAt_flatD` returning its `HeapBuf`s**: the buffers are the function's `Lout`. -/
theorem completeAt_flatOutD {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E) (rets : ℕ → List E)
    (Out : List E → Layout → Prop)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hout : ∀ fp, Out (rets fp) (bufL (fp + fs f) sizes (own fp))) (kids : ℕ → List Kid)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args k.Out)
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun r => r = rets fp) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (kids fp) outs ∧
        ∀ q ∈ pre.flatMap (loadsEv σ), ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) :
    CompleteAtD fs cert κ f Lin args Out := by
  intro fp
  obtain ⟨N, L, outs, ho, hW, hD, -, hK⟩ := kidsFromIn_of_kidsD (fs := fs) (cert := cert) κ (kids fp)
    (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, L, rets fp, bufL (fp + fs f) sizes (own fp), hout fp, ?_,
    disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    fun rd hlow hL => ?_⟩
  · simp only [within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  obtain ⟨σ, hp, hdo, hh, hsz, hbuf, hcm, hld⟩ := hσ fp outs ho rd hlow hB hLin
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets fp := hsat.2
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp)) i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i hi)
  have hk := hK rd σ (calls (pre.flatMap (flEvs σ))) (fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (memL_lins (hkm fp rd hB hLin))
    (regionsOk_of fun k hk ht i hi => Or.inl ((hkr fp k hk ht i hi).imp_right (hown' i)))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL (bufL (fp + fs f) sizes (own fp)))
    (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp)
    hk (fun A hA => ?_) (fun i hi => Or.inl (hown' i hi))
  · rw [hal] at h
    exact h
  · rw [i5] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩

end
end LeanVM.Guest.B1
