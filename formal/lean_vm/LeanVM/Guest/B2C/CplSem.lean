/-
  LeanVM.Guest.B2C.CplSem

  What the completeness walk's facts rest on: a window's cells are the certificate's, the atoms
  of a block on the path hold on the frame, and the context's fixed cells and header hold.
-/

module

public import LeanVM.Guest.B2C.CplJust
public import LeanVM.Guest.B2C.CplInv

/-!
# The facts of a path

`clocW_get`: a window's packed cells are the certificate's. `walk_noRetC`, `atom_on_pathC`,
`atoms_in`: a block without `ret` falls through or is stuck, and on a path that falls through
every one of its atoms is an event; the last window's statements are such a block and a `ret`.
`val_cell`, `locC_holds`, `fileB_ok`: on a frame holding what the honest memory puts there
(`FrameHolds`), each atom of the path holds on its cells, so every book the walk files holds.
`cxOk`: the context of a window holds.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

/-! ## A window's cells -/

theorem packC_digit : ∀ (l : List ℕ), (∀ c ∈ l, c < 65536) → ∀ k (hk : k < l.length),
    Nat.mod (Nat.div (packC l) (Nat.pow 65536 k)) 65536 = l[k]
  | [], _, k, hk => absurd hk (Nat.not_lt_zero _)
  | c :: cs, h, 0, _ => by
    have hc := h c List.mem_cons_self
    show (c + packC cs * 65536) / 65536 ^ 0 % 65536 = c
    rw [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  | c :: cs, h, k + 1, hk => by
    have hc := h c List.mem_cons_self
    have hk' : k < cs.length := by simpa using hk
    have ih := packC_digit cs (fun x hx ↦ h x (List.mem_cons_of_mem _ hx)) k hk'
    rw [List.getElem_cons_succ]
    show (c + packC cs * 65536) / 65536 ^ (k + 1) % 65536 = cs[k]
    rw [Nat.pow_succ, Nat.mul_comm (65536 ^ k), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hc, Nat.zero_add]
    exact ih

theorem insC_get : ∀ {v c : ℕ} (ps : List (ℕ × ℕ × ℕ)), insC v ps = some c → ∃ j, (v, c, j) ∈ ps
  | _, _, [], h => by simp [insC] at h
  | v, c, p :: ps, h => by
    simp only [insC] at h
    cases hb : Nat.beq p.1 v
    · rw [hb] at h
      obtain ⟨j, hj⟩ := insC_get ps h
      exact ⟨j, List.mem_cons_of_mem _ hj⟩
    · rw [hb] at h
      obtain rfl := Nat.eq_of_beq_eq_true hb
      obtain rfl := Option.some.inj h
      exact ⟨p.2.2, List.mem_cons_self⟩

/-- **A window's packed cells are the certificate's.** -/
theorem clocW_get {C : Cert} {n i : ℕ} (hcont : Cont C n) (hi : i ≤ n)
    (hins : C.insOk (nth C.ins i []) = true) (hn : C.cuts.length = n)
    (hb : (nth C.cells i []).all (fun c ↦ Nat.blt c 65536) = true) {v c : ℕ}
    (h : (clocW C i).get? v = some c) : C.locs.getD v 0 = c := by
  unfold CLoc.get? clocW at h
  simp only at h
  cases hr : (Nat.ble (nth C.los i 0) v && Nat.blt v (Nat.add (nth C.los i 0) (nth C.cells i []).length))
  · rw [hr] at h
    obtain ⟨j, hj⟩ := insC_get _ h
    have := List.all_eq_true.mp hins _ hj
    simp only [Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at this
    obtain ⟨⟨hjn, hlo⟩, hget⟩ := this
    obtain ⟨hm, hget⟩ := List.getElem?_eq_some_iff.mp hget
    rw [show v = nth C.los j 0 + (v - nth C.los j 0) by omega, cont_locs hcont (hn ▸ hjn) hm, hget]
  · rw [hr] at h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hr
    obtain ⟨h1, h2⟩ := hr
    have hm : v - nth C.los i 0 < (nth C.cells i []).length := by
      change v < nth C.los i 0 + _ at h2
      omega
    simp only [Bool.cond_true, Option.some.injEq] at h
    rw [show v = nth C.los i 0 + (v - nth C.los i 0) by omega, cont_locs hcont hi hm]
    rw [show Nat.sub v (nth C.los i 0) = v - nth C.los i 0 from rfl,
      packC_digit _ (fun x hx ↦ Nat.blt_eq.mp (List.all_eq_true.mp hb x hx)) _ hm] at h
    exact h

/-! ## Paths -/

section Walk

variable {σ : Val}

theorem walk_appendC : ∀ (l l' : List Stmt), walk σ (l ++ l') = (walk σ l).seq (walk σ l')
  | [], l' => by
      rw [List.nil_append, walk]
      cases walk σ l' <;> simp [Out.seq, Out.pre]
  | s :: l, l' => by
      rw [List.cons_append, walk, walk, walk_appendC l l']
      cases walk1 σ s <;> cases walk σ l <;> cases walk σ l' <;>
        simp [Out.seq, Out.pre, List.append_assoc]

theorem pre_noRetC {o : Out} {es : List Ev} (h : (∃ es', o = .fall es') ∨ o = .stuck) :
    (∃ es', o.pre es = .fall es') ∨ o.pre es = .stuck := by
  rcases h with ⟨es', rfl⟩ | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr rfl

theorem pick_noRetC {x : V} {a r : List V} : ∀ (gs : List String) (j : ℕ),
    (∃ es, pick σ x a r j gs = .fall es) ∨ pick σ x a r j gs = .stuck
  | [], _ => Or.inr rfl
  | g :: gs, j => by
    unfold pick
    split_ifs
    · exact Or.inl ⟨_, rfl⟩
    · exact pick_noRetC gs (j + 1)

mutual
theorem walk1_noRetC : ∀ (s : Stmt), Stmt.noRet s = true →
    (∃ es, walk1 σ s = .fall es) ∨ walk1 σ s = .stuck
  | .atom _, _ => Or.inl ⟨_, rfl⟩
  | .ite c z n, h => by
      simp only [Stmt.noRet, Bool.and_eq_true] at h
      rw [walk1]
      split_ifs
      · exact pre_noRetC (walk_noRetC z h.1)
      · exact pre_noRetC (walk_noRetC n h.2)
  | .match_ x arms, h => by
      rw [walk1]
      exact walkArms_noRetC x arms 0 h
  | .call .., _ => Or.inl ⟨_, rfl⟩
  | .callIf .., _ => Or.inl ⟨_, rfl⟩
  | .dispatch x gs a r, _ => by rw [walk1]; exact pick_noRetC gs 0
  | .ret _, h => by simp [Stmt.noRet] at h

/-- **A block without `ret` falls through or is stuck.** -/
theorem walk_noRetC : ∀ (ss : List Stmt), Stmt.noRetList ss = true →
    (∃ es, walk σ ss = .fall es) ∨ walk σ ss = .stuck
  | [], _ => Or.inl ⟨[], rfl⟩
  | s :: ss, h => by
      simp only [Stmt.noRetList, Bool.and_eq_true] at h
      rw [walk]
      rcases walk1_noRetC s h.1 with ⟨es, h1⟩ | h1
      · rw [h1]
        exact pre_noRetC (walk_noRetC ss h.2)
      · rw [h1]
        exact Or.inr rfl

theorem walkArms_noRetC (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), Stmt.noRetArms arms = true →
    (∃ es, walkArms σ x j arms = .fall es) ∨ walkArms σ x j arms = .stuck
  | [], _, _ => Or.inr rfl
  | a :: as, j, h => by
      simp only [Stmt.noRetArms, Bool.and_eq_true] at h
      unfold walkArms
      split_ifs
      · exact walk_noRetC a h.1
      · exact walkArms_noRetC x as (j + 1) h.2
end

/-- **A block's atoms are on a path through it.** -/
theorem atom_on_pathC {a : Core.Atom} : ∀ {l : List Stmt} {es : List Ev}, walk σ l = .fall es →
    Stmt.atom a ∈ l → Ev.atom a ∈ es
  | [], _, _, hm => (List.not_mem_nil hm).elim
  | s :: l, es, hw, hm => by
      rw [walk] at hw
      rcases ho : walk1 σ s with es1 | ⟨es1, vs1⟩ | _
      · rw [ho] at hw
        rcases hl : walk σ l with es2 | ⟨es2, vs2⟩ | _
        · rw [hl] at hw
          simp only [Out.seq, Out.pre, Out.fall.injEq] at hw
          subst hw
          rcases List.mem_cons.mp hm with rfl | hm
          · simp only [walk1, Out.fall.injEq] at ho
            subst ho
            exact List.mem_append_left _ List.mem_cons_self
          · exact List.mem_append_right _ (atom_on_pathC hl hm)
        · rw [hl] at hw; simp [Out.seq, Out.pre] at hw
        · rw [hl] at hw; simp [Out.seq, Out.pre] at hw
      · rw [ho] at hw; simp [Out.seq] at hw
      · rw [ho] at hw; simp [Out.seq] at hw

theorem lastOkC_split : ∀ {ss : List Stmt}, lastOkC ss = true →
    ∃ A vs, ss = A ++ [.ret vs] ∧ Stmt.noRetList A = true
  | [], h => by simp [lastOkC] at h
  | [.ret vs], _ => ⟨[], vs, rfl, rfl⟩
  | s :: s' :: ss, h => by
    have h' : Stmt.noRet s = true ∧ lastOkC (s' :: ss) = true := by
      cases s <;> simp_all [lastOkC]
    obtain ⟨A, vs, he, hA⟩ := lastOkC_split h'.2
    refine ⟨s :: A, vs, by rw [he]; rfl, ?_⟩
    simp only [Stmt.noRetList, h'.1, hA, Bool.and_self]
  | [.atom _], h => by simp [lastOkC] at h
  | [.ite ..], h => by simp [lastOkC] at h
  | [.match_ ..], h => by simp [lastOkC] at h
  | [.call ..], h => by simp [lastOkC] at h
  | [.callIf ..], h => by simp [lastOkC] at h
  | [.dispatch ..], h => by simp [lastOkC] at h

/-- On a path through the last window's statements, which return, every atom before the `ret`
is an event. -/
theorem atoms_last {ss : List Stmt} (h : lastOkC ss = true) {o : Out} (hw : walk σ ss = o)
    (hs : o ≠ .stuck) {a : Core.Atom} (ha : Stmt.atom a ∈ ss) : Ev.atom a ∈ o.evs := by
  obtain ⟨A, vs, rfl, hA⟩ := lastOkC_split h
  rw [walk_appendC] at hw
  rcases walk_noRetC A hA with ⟨eA, h1⟩ | h1
  · rw [h1] at hw
    subst hw
    simp only [walk, walk1, Out.seq, Out.pre, Out.evs, List.append_nil]
    rcases List.mem_append.mp ha with ha | ha
    · exact atom_on_pathC h1 ha
    · simp at ha
  · rw [h1] at hw
    exact absurd hw.symm (by simpa [Out.seq] using hs)

end Walk

/-! ## The atoms of a path hold -/

section Frame

variable {κ : ℕ} {L : MemImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
  {kfps : List ℕ} {hdr : E × E} {loc : CLoc}

/-- A window's cells are the certificate's. -/
def LocOk (j : ℕ) (loc : CLoc) : Prop := ∀ (v : V) (c : ℕ), loc.get? v.idx = some c → cellJ j v = c

theorem loc_cell (hl : LocOk j loc) {v : V} (h : 2 ≤ loc.cell v) : cellJ j v = loc.cell v := by
  unfold CLoc.cell at h ⊢
  rcases hg : loc.get? v.idx with _ | c
  · rw [hg] at h; simp at h
  · rw [Option.getD_some]
    exact hl v c hg

theorem inFrame_mem {n : ℕ} : ∀ {l : List ℕ}, inFrame n l = true → ∀ c ∈ l, 2 ≤ c ∧ c < n
  | [], _, _, hc => (List.not_mem_nil hc).elim
  | x :: l, h, c, hc => by
    simp only [inFrame, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨h.1.1, h.1.2⟩
    · exact inFrame_mem h.2 c hc

theorem uses_named {e : Ev} (he : e ∈ es) {v : V} (hv : v ∈ e.uses) :
    v ∈ namedOf (coreOf j).params es vs := by
  unfold namedOf
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hv⟩))

/-- **A value the path names holds its word at its cell.** -/
theorem val_cell (hF : FrameHolds L j fp σ es vs kfps hdr) (hl : LocOk j loc) {v : V}
    (hv : v ∈ namedOf (coreOf j).params es vs) (h2 : 2 ≤ loc.cell v) (h3 : loc.cell v < fsN j) :
    rdc L fp (loc.cell v) = some (σ v) := by
  have e := loc_cell hl h2
  have := hF.val v hv (e ▸ h2) (e ▸ h3)
  rw [e, gpow_addC] at this
  exact this

/-- A range check's temporary holds its word at its cell. -/
theorem tmp_cell (hF : FrameHolds L j fp σ es vs kfps hdr) (hl : LocOk j loc) {e : Ev} (he : e ∈ es)
    {t : V} (ht : t ∈ e.tmps) (h2 : 2 ≤ loc.cell t) (h3 : loc.cell t < fsN j) :
    rdc L fp (loc.cell t) = some (σ t) := by
  have e' := loc_cell hl h2
  have := hF.tmp e he t ht (e' ▸ h2) (e' ▸ h3)
  rw [e', gpow_addC] at this
  exact this

/-- **An atom of the path holds on its cells.** -/
theorem locC_holds (hF : FrameHolds L j fp σ es vs kfps hdr) (hl : LocOk j loc)
    (hev : ∀ e ∈ es, e.Holds L.read σ) {a : Core.Atom} (ha : Ev.atom a ∈ es)
    (hin : inFrame (fsN j) (cellsC (locC loc a)) = true) : LHolds L fp (locC loc a) := by
  have hh := hev _ ha
  have V : ∀ v ∈ Ev.uses (.atom a), loc.cell v ∈ cellsC (locC loc a) →
      rdc L fp (loc.cell v) = some (σ v) := fun v hv hc ↦
    val_cell hF hl (uses_named ha hv) (inFrame_mem hin _ hc).1 (inFrame_mem hin _ hc).2
  cases a with
  | const d x =>
    exact (V d (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC])).trans (by rw [hh])
  | add d x y =>
    refine ⟨σ x, σ y, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V y (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), ?_⟩
    rw [V d (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC])]
    exact congrArg some hh
  | mul d x y =>
    refine ⟨σ x, σ y, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V y (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), ?_⟩
    rw [V d (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC])]
    exact congrArg some hh
  | copy d x =>
    refine ⟨σ x, ?_, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC])⟩
    rw [V d (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC])]
    exact congrArg some hh
  | load d p off =>
    obtain ⟨hK, hr⟩ := hh
    exact ⟨σ p, σ d, V p (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hK,
      V d (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hr⟩
  | assertEq x y =>
    refine ⟨σ x, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), ?_⟩
    rw [V y (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC])]
    exact congrArg some (eq_of_add_eq_zero hh).symm
  | assertNe x i p =>
    obtain ⟨h1, h2⟩ := hh
    refine ⟨σ x, σ i, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V i (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), ?_, h1 ▸ h2⟩
    rw [V p (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), h1]
  | rangeCheck x y t1 t2 k =>
    obtain ⟨⟨hKx, h1⟩, hk, ⟨hKy, h2⟩⟩ := hh
    have T : ∀ t ∈ [t1, t2], loc.cell t ∈ cellsC (locC loc (.rangeCheck x y t1 t2 k)) →
        rdc L fp (loc.cell t) = some (σ t) := fun t ht hc ↦
      tmp_cell hF hl ha (by simpa [Ev.tmps, atomTmps] using ht) (inFrame_mem hin _ hc).1
        (inFrame_mem hin _ hc).2
    refine ⟨σ x, σ y, σ t1, σ t2, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hKx,
      V y (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hKy,
      T t1 (by simp) (by simp [locC, cellsC]), T t2 (by simp) (by simp [locC, cellsC]), h1, h2, ?_⟩
    rw [V k (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hk]
  | assertInK x y =>
    obtain ⟨hx, hy⟩ := hh
    exact ⟨σ x, σ y, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hx,
      V y (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hy⟩
  | blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md =>
    exact ⟨_, _, _, _, _, _, _, _, _,
      V m0 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V m1 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V m2 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V m3 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V cv0 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V cv1 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V o0 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V o1 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V md (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hh⟩
  | frameAddr p run =>
    cases run with
    | nil => trivial
    | cons r rs =>
      have hr := inFrame_mem hin (loc.cell r) (by simp [locC, cellsC])
      have hp : (p, r) ∈ addrs es := List.mem_filterMap.mpr ⟨_, ha, rfl⟩
      refine ⟨loc.cell r, rs.map loc.cell, rfl, ?_⟩
      rw [V p (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hF.addr _ hp,
        loc_cell hl hr.1]
  | hint h => trivial

/-- **Every book the walk files from the path's atoms holds.** -/
theorem fileB_ok (hF : FrameHolds L j fp σ es vs kfps hdr) (hl : LocOk j loc)
    (hev : ∀ e ∈ es, e.Holds L.read σ) :
    ∀ (ss : List Stmt) (B : BookC), BookOk L fp B → (∀ a, Stmt.atom a ∈ ss → Ev.atom a ∈ es) →
      BookOk L fp (fileB loc (fsN j) ss B)
  | [], B, hB, _ => hB
  | .atom a :: ss, B, hB, ha => by
    simp only [fileB, LAtom.seq_eq]
    cases hin : inFrame (fsN j) (cellsC (locC loc a))
    · simp only [Bool.cond_false]
      exact fileB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
    · simp only [Bool.cond_true, Trie.seq_eq]
      exact fileB_ok hF hl hev ss _
        (hB.file (locC_holds hF hl hev (ha a List.mem_cons_self) hin))
        fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
  | .ite .. :: ss, B, hB, ha => fileB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
  | .match_ .. :: ss, B, hB, ha => fileB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
  | .call .. :: ss, B, hB, ha => fileB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
  | .callIf .. :: ss, B, hB, ha => fileB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
  | .dispatch .. :: ss, B, hB, ha => fileB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
  | .ret _ :: ss, B, hB, ha => fileB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)

/-! ## The context -/

theorem statT_get {n o : ℕ} {p : PC} : ∀ (ps : List (ℕ × PC)) (t : Trie PC),
    getF (statT n ps t) o = some p → ((o, p) ∈ ps ∧ 2 ≤ o ∧ o < n) ∨ getF t o = some p
  | [], _, h => Or.inr h
  | q :: ps, t, h => by
    simp only [statT] at h
    cases hb : (Nat.ble 2 q.1 && Nat.blt q.1 n)
    · rw [hb, Bool.cond_false] at h
      rcases statT_get ps t h with ⟨hm, h2⟩ | h'
      · exact Or.inl ⟨List.mem_cons_of_mem _ hm, h2⟩
      · exact Or.inr h'
    · rw [hb, Bool.cond_true, Trie.seq_eq] at h
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hb
      rcases statT_get ps _ h with ⟨hm, h2⟩ | h'
      · exact Or.inl ⟨List.mem_cons_of_mem _ hm, h2⟩
      · rw [getF_eq, setF_eq] at h'
        rcases Trie.get_set h' with ⟨rfl, rfl⟩ | h''
        · exact Or.inl ⟨List.mem_cons_self, hb⟩
        · exact Or.inr (by rwa [getF_eq])

/-- **A window's context holds** on an instance's frame. -/
theorem cxOk (hF : FrameHolds L j fp σ es vs kfps hdr) (hpows : (certOf j).facts.pows.Ok)
    (idx : Trie Exec.Seg) (loc : CLoc) (nv : ℕ) (stop : Option (ℕ × ℕ)) :
    CXOk L fp (cxOf j idx loc (statT (fsN j) (plumbOf j).stat .nil) nv stop) := by
  refine ⟨fun o p h ↦ ?_, fun o ho ↦ ?_, hpows⟩
  · rcases statT_get _ _ h with ⟨hm, h2, h3⟩ | h'
    · have := hF.stat _ hm h2 h3
      rw [gpow_addC] at this
      exact this
    · simp [getF_eq] at h'
  · have hK : (cxOf j idx loc (statT (fsN j) (plumbOf j).stat .nil) nv stop).main = false →
        IsInK hdr.1 ∧ IsInK hdr.2 := fun hm ↦ hF.hdrK (by
      intro h1
      simp [cxOf, h1] at hm)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ho with rfl | rfl
    · refine ⟨hdr.1, ?_, fun hm ↦ (hK hm).1⟩
      have := hF.hdr0
      rw [gpow_addC] at this
      exact this
    · refine ⟨hdr.2, ?_, fun hm ↦ (hK hm).2⟩
      have := hF.hdr1
      rw [gpow_addC] at this
      exact this

end Frame

end
end LeanVM.Guest.B2C
