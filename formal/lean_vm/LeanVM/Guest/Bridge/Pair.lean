/-
  LeanVM.Guest.Bridge.Pair

  The hint bridge's pairing at a pc: a flow hint the executor runs at a frame of the tree track compiles a hint atom on the frame's path; and what the computed hints' data check gives on a path.
-/

module

public import LeanVM.Guest.Bridge.PairDefs
public import LeanVM.Guest.Bridge.StepRule
public import LeanVM.Guest.B2C.ShareSound

/-!
# The pairing at a pc

`pair_flow`: a frame of the tree track at pc `pc` (`AtPc`) is at an offset of its function's code; each flow hint of the function's advice at `pc` compiles (`compiles`, under the alignment's cell map) a hint atom on the frame's whole path. The alignment at that offset (`alignAt_step`) puts the hints' atoms at the head of the frame's position, which its path walks first.

`pairChk_sound`: on a path of a body passing `pairChk`, each computed hint atom's frame values are at their certificate cells in the frame, and each buffer it names is allocated on the path and written whole by a heap hint on it.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

public section

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => (List.not_mem_nil hb).elim
  | a :: _, b' :: _, .cons hab h, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', hr⟩ := forall₂_mem_right h b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hr⟩

variable {σ : Val}

theorem walk_atoms_pre : ∀ (bs : List Atom) (ps : List Stmt),
    walk σ (bs.map Stmt.atom ++ ps) = (walk σ ps).pre (bs.map Ev.atom)
  | [], ps => by simp only [List.map_nil, List.nil_append, out_pre_nil]
  | b :: bs, ps => by
    rw [List.map_cons, List.cons_append, walk_atom_cons, walk_atoms_pre bs ps, out_pre_pre]
    rfl

/-- **Atoms heading a position are on its path.** -/
theorem atoms_on_path {bs : List Atom} {ps : List Stmt} {es : List Ev} {vs : List V}
    (h : walk σ (bs.map Stmt.atom ++ ps) = .ret es vs) : ∀ a ∈ bs, Ev.atom a ∈ es := by
  rw [walk_atoms_pre] at h
  obtain ⟨es', -, rfl⟩ := pre_eq_ret h
  intro a ha
  exact List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- **The pairing at a pc**: a frame of the tree track at pc `pc` is at an offset `off` of its
function's code, and each flow hint of its advice at `pc` compiles a hint atom on its path. -/
theorem pair_flow {prog : LeanIsaProgram} {P : Core.Program} {A : String → FnAl} (hP : ProgAl prog P A)
    {Is : List Inst} {e : Ent} (hE : EntOk P Is e) {pc : ℕ} (hat : AtPc (entOf A) (alOf A) e pc) :
    ∃ off, pc = (A e.I.t.name).X.entry + off ∧ off < (A e.I.t.name).code.length ∧
      ∀ h ∈ (((A e.I.t.name).d.2.2.lookup pc).getD []), isaFlowHint h = true →
        ∃ hc, Ev.atom (.hint hc) ∈ e.pre ++ e.es ∧ compiles (A e.I.t.name).X.locAt hc h = true := by
  obtain ⟨off, hpc, p, hal, as0, -, hpos⟩ := hat
  obtain ⟨ins, z, tabs, r, as, hins, -, hp, hF2, -⟩ := alignAt_step (hP.ok _ _ hE.find) hal
  refine ⟨off, hpc, (List.getElem?_eq_some_iff.mp hins).1, fun h hh hfl ↦ ?_⟩
  rw [hpc] at hh
  obtain ⟨a, ha, hc, rfl, hcomp⟩ := forall₂_mem_right hF2 h (List.mem_filter.mpr ⟨hh, hfl⟩)
  obtain ⟨vs, -, hw⟩ := hE.path
  rw [hpos, hp, ← List.append_assoc, ← List.map_append] at hw
  exact ⟨hc, List.mem_append_right _ (atoms_on_path hw _ (List.mem_append_right _ (List.mem_filter.mp ha).1)),
    hcomp⟩

/-! ## The data check on a path -/

theorem blockAll_cons (p : Atom → Bool) (s : Stmt) (ss : List Stmt) :
    blockAll p (s :: ss) = (blockAll p [s] && blockAll p ss) := by
  show (_ && _) = ((_ && true) && _)
  rw [Bool.and_true]
  rfl

mutual
theorem stmtAll_sound (p : Atom → Bool) : ∀ (s : Stmt), blockAll p [s] = true → ∀ a ∈ sAtoms s, p a = true
  | .atom a, h, b, hb => by
    simp only [sAtoms, List.mem_singleton] at hb
    subst hb
    have : (p b && true) = true := h
    simpa using this
  | .ite c z n, h, b, hb => by
    have h' : ((blockAll p z && blockAll p n) && true) = true := h
    simp only [Bool.and_true, Bool.and_eq_true] at h'
    simp only [sAtoms, List.mem_append] at hb
    rcases hb with hb | hb
    · exact blockAll_sound p z h'.1 b hb
    · exact blockAll_sound p n h'.2 b hb
  | .match_ x arms, h, b, hb => by
    have h' : (armsAll p arms && true) = true := h
    simp only [Bool.and_true] at h'
    exact armsAll_sound p arms h' b hb
  | .call .., _, b, hb => by simp [sAtoms] at hb
  | .callIf .., _, b, hb => by simp [sAtoms] at hb
  | .dispatch .., _, b, hb => by simp [sAtoms] at hb
  | .ret _, _, b, hb => by simp [sAtoms] at hb

theorem blockAll_sound (p : Atom → Bool) : ∀ (ss : List Stmt), blockAll p ss = true → ∀ a ∈ lAtoms ss, p a = true
  | [], _, b, hb => by simp [lAtoms] at hb
  | s :: ss, h, b, hb => by
    rw [blockAll_cons, Bool.and_eq_true] at h
    simp only [lAtoms, List.mem_append] at hb
    rcases hb with hb | hb
    · exact stmtAll_sound p s h.1 b hb
    · exact blockAll_sound p ss h.2 b hb

theorem armsAll_sound (p : Atom → Bool) : ∀ (arms : List (List Stmt)), armsAll p arms = true →
    ∀ a ∈ aAtoms arms, p a = true
  | [], _, b, hb => by simp [aAtoms] at hb
  | a :: as, h, b, hb => by
    have h' : (blockAll p a && armsAll p as) = true := h
    rw [Bool.and_eq_true] at h'
    simp only [aAtoms, List.mem_append] at hb
    rcases hb with hb | hb
    · exact blockAll_sound p a h'.1 b hb
    · exact armsAll_sound p as h'.2 b hb
end

theorem pick_ne_ret {x : V} {args rets : List V} {es : List Ev} {vs : List V} :
    ∀ (fs : List String) (j : ℕ), pick σ x args rets j fs ≠ .ret es vs
  | [], _ => by simp [pick]
  | f :: fs, j => by
    unfold pick
    split
    · simp
    · exact pick_ne_ret fs (j + 1)

theorem noRet_cons (s : Stmt) (ss : List Stmt) : noRet (s :: ss) = (noRet [s] && noRet ss) := by
  show (_ && _) = ((_ && true) && _)
  rw [Bool.and_true]
  rfl

mutual
/-- **A statement without `ret` does not return.** -/
theorem walk1_noRet : ∀ (s : Stmt), noRet [s] = true → ∀ es vs, walk1 σ s ≠ .ret es vs
  | .atom _, _, _, _ => by simp [walk1]
  | .ite c z n, h, es, vs => by
    have h' : ((noRet z && noRet n) && true) = true := h
    simp only [Bool.and_true, Bool.and_eq_true] at h'
    intro he
    rw [walk1] at he
    obtain ⟨es', he', -⟩ := pre_eq_ret he
    split at he'
    · exact walk_noRet z h'.1 es' vs he'
    · exact walk_noRet n h'.2 es' vs he'
  | .match_ x arms, h, es, vs => by
    have h' : (noRetArms arms && true) = true := h
    simp only [Bool.and_true] at h'
    rw [walk1]
    exact walkArms_noRet x arms 0 h' es vs
  | .call .., _, _, _ => by simp [walk1]
  | .callIf .., _, _, _ => by simp [walk1]
  | .dispatch x fs args rets, _, es, vs => by rw [walk1]; exact pick_ne_ret fs 0
  | .ret _, h, _, _ => absurd (show (false && true) = true from h) (by decide)

theorem walk_noRet : ∀ (ss : List Stmt), noRet ss = true → ∀ es vs, walk σ ss ≠ .ret es vs
  | [], _, _, _ => by simp [walk]
  | s :: ss, h, es, vs => by
    rw [noRet_cons, Bool.and_eq_true] at h
    intro he
    rw [walk] at he
    rcases seq_eq_ret he with ⟨es1, es2, -, h2, -⟩ | h1
    · exact walk_noRet ss h.2 es2 vs h2
    · exact walk1_noRet s h.1 es vs h1

theorem walkArms_noRet (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), noRetArms arms = true →
    ∀ es vs, walkArms σ x j arms ≠ .ret es vs
  | [], _, _, _, _ => by simp [walkArms]
  | a :: as, j, h, es, vs => by
    have h' : (noRet a && noRetArms as) = true := h
    rw [Bool.and_eq_true] at h'
    rw [walkArms]
    split
    · exact walk_noRet a h'.1 es vs
    · exact walkArms_noRet x as (j + 1) h'.2 es vs
end

/-- **The spine is on every path that returns.** -/
theorem spine_on_path : ∀ (ss : List Stmt) {es : List Ev} {vs : List V}, walk σ ss = .ret es vs →
    ∀ a ∈ spine ss, Ev.atom a ∈ es
  | [], _, _, _, a, ha => by simp [spine] at ha
  | .atom b :: ss, es, vs, h, a, ha => by
    rw [walk_atom_cons] at h
    obtain ⟨es', h', rfl⟩ := pre_eq_ret h
    simp only [spine, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (spine_on_path ss h' a ha)
  | .call f args rets :: ss, es, vs, h, a, ha => by
    rw [walk_call_cons] at h
    obtain ⟨es', h', rfl⟩ := pre_eq_ret h
    exact List.mem_append_right _ (spine_on_path ss h' a ha)
  | .callIf c f args :: ss, es, vs, h, a, ha => by
    rw [walk_callIf_cons] at h
    obtain ⟨es', h', rfl⟩ := pre_eq_ret h
    exact List.mem_append_right _ (spine_on_path ss h' a ha)
  | .dispatch x fs args rets :: ss, es, vs, h, a, ha => by
    rw [walk_dispatch_cons] at h
    rcases seq_eq_ret h with ⟨es1, es2, -, h2, rfl⟩ | h1
    · exact List.mem_append_right _ (spine_on_path ss h2 a ha)
    · exact absurd h1 (pick_ne_ret fs 0)
  | .ite c z n :: ss, es, vs, h, a, ha => by
    simp only [spine, Bool.cond_eq_ite, Bool.and_eq_true] at ha
    split at ha
    · rename_i hn
      rw [walk] at h
      rcases seq_eq_ret h with ⟨es1, es2, -, h2, rfl⟩ | h1
      · exact List.mem_append_right _ (spine_on_path ss h2 a ha)
      · exact absurd h1 (walk1_noRet (.ite c z n) (show ((noRet z && noRet n) && true) = true by
          simp [hn.1, hn.2]) es vs)
    · simp at ha
  | .match_ x arms :: ss, es, vs, h, a, ha => by
    simp only [spine, Bool.cond_eq_ite] at ha
    split at ha
    · rename_i hn
      rw [walk] at h
      rcases seq_eq_ret h with ⟨es1, es2, -, h2, rfl⟩ | h1
      · exact List.mem_append_right _ (spine_on_path ss h2 a ha)
      · exact absurd h1 (walk1_noRet (.match_ x arms) (show (noRetArms arms && true) = true by
          simp [hn]) es vs)
    · simp at ha
  | .ret _ :: _, _, _, _, a, ha => by simp [spine] at ha

/-- An allocation atom on a path allocates its pointer. -/
theorem allocDsts_of_mem {es : List Ev} {a : Atom} {p : V} (ha : Ev.atom a ∈ es) (hp : allocOf a = some p) :
    p ∈ allocDsts es := by
  refine List.mem_filterMap.mpr ⟨.atom a, ha, ?_⟩
  cases a with
  | hint h => cases h <;> simp_all [allocOf, Ev.allocDst?]
  | _ => simp [allocOf] at hp

/-- **What the data check gives of a computed hint on a path**: its frame values at their
certificate cells in the frame or at hint-only cells in it, its buffer from offset `0`, of length in `(0, 2^30)`, its pointer at
its certificate cell or a hint-only cell, allocated on the path and written whole by a heap hint on
it. -/
theorem pairChk_sound {extra : List (ℕ × ℕ)} {locs : List ℕ} {n : ℕ} {body : List Stmt}
    (hc : pairChk extra locs n body = true) {es : List Ev} {vs : List V} (hw : walk σ body = .ret es vs)
    {h : Core.Hint} (hh : Ev.atom (.hint h) ∈ es) (hcomp : compHint h = true) :
    (∀ v ∈ hintFrame h, (extra.lookup v.idx = none ∧ v.idx < 2 ^ 30 ∧ 2 ≤ locs.getD v.idx 0 ∧ locs.getD v.idx 0 < n) ∨
      ∃ c, extra.lookup v.idx = some c ∧ 2 ≤ c ∧ c < n) ∧
    ∀ p off len, hintBuf h = some (p, off, len) → off = 0 ∧ 0 < len ∧ len < 2 ^ 30 ∧
      ((extra.lookup p.idx = none ∧ p.idx < 2 ^ 30 ∧ 2 ≤ locs.getD p.idx 0 ∧ locs.getD p.idx 0 < n) ∨
        (extra.lookup p.idx).isSome) ∧
      p ∈ allocDsts es ∧ ∃ a, Ev.atom a ∈ es ∧ atomHeapDest? a = some (p, off, len) := by
  have hcell : ∀ v, cellOk extra locs n v = true →
      extra.lookup v.idx = none ∧ v.idx < 2 ^ 30 ∧ 2 ≤ locs.getD v.idx 0 ∧ locs.getD v.idx 0 < n := fun v hv ↦ by
    simp only [cellOk, Bool.and_eq_true, Option.isNone_iff_eq_none, Nat.ble_eq, Nat.blt_eq] at hv
    exact ⟨hv.1.1.1, hv.1.1.2, hv.1.2, hv.2⟩
  have hok := blockAll_sound _ body hc _ (walk_atoms body (by rw [hw]; exact hh))
  simp only [pairAtomOk, hcomp, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at hok
  have hextra : ∀ v, hintOnlyOk extra n v = true → ∃ c, extra.lookup v.idx = some c ∧ 2 ≤ c ∧ c < n := fun v hv ↦ by
    unfold hintOnlyOk at hv
    split at hv
    · rename_i c hc
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hv
      exact ⟨c, hc, hv⟩
    · cases hv
  refine ⟨fun v hv ↦ (Bool.or_eq_true_iff.mp (hok.1 v hv)).imp (hcell v) (hextra v), fun p off len hb ↦ ?_⟩
  have h2 := hok.2
  rw [hb] at h2
  simp only [bufOk, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Bool.or_eq_true, List.any_eq_true,
    beq_iff_eq] at h2
  obtain ⟨⟨⟨⟨⟨h0, hl1⟩, hl2⟩, hcl⟩, ⟨a1, ha1, hal⟩⟩, ⟨a2, ha2, had⟩⟩ := h2
  exact ⟨h0, hl1, hl2, hcl.imp (hcell p) id,
    allocDsts_of_mem (spine_on_path body hw a1 ha1) hal, a2, spine_on_path body hw a2 ha2, had⟩

end

end LeanVM.Guest.Bridge
