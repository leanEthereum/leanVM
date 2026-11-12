/-
  LeanVM.Guest.Memory.MemCheck

  The guest's memory-layer facts in one kernel check per function: its temporaries fresh, its
  body well formed, no call of `main` (`memF`), walked by recursors; ranges of functions passing it
  give all three of the whole core IR.
-/

module

public import LeanVM.Guest.Memory.CalleeIdx
public import LeanVM.Guest.Memory.Fresh
public import LeanVM.Guest.Memory.Tree
public import LeanVM.Guest.Memory.SizeTotal
public import LeanVM.Guest.CoreNames

/-!
# One check for the memory layer

`memB p tk nm` walks a block once, by the recursors (which the kernel reduces faster than it builds
`Stmt.usesList`): every value it names passes `p`, every `callIf` its callee's arity `tk`, every
callee `nm`, and every `match` and dispatch has at most `2^64 - 1` arms (`memB_spec`). Function
`j`'s check `memF tt j` runs it with `p` avoiding the function's temporaries (`tmpsR`, by index),
`tk` reading the callee's arity off `tt` through `calleeIdx`, and `nm` excluding `main`; besides,
the temporaries are distinct and no parameter, and a function `tt` gives an arity takes it. A
check of every function (`RangeOk (memF tt)`) gives `Program.Fresh` (`memAll_fresh`),
`Program.Wf` (`memAll_wf`) and no call of `main` (`memAll_callees`). A body too large for one
kernel check is checked by ranges of its statements (`memB_drop`, `memF_of`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-! ## The walk -/

/-- Each value of the list passes `p`, by the recursor. -/
noncomputable def vsAll (p : V → Bool) (l : List V) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun v _ b => p v && b) l

theorem vsAll_eq (p : V → Bool) : ∀ l : List V, vsAll p l = l.all p
  | [] => rfl
  | v :: l => by
      show (p v && vsAll p l) = _
      rw [vsAll_eq p l, List.all_cons]

/-- Each value an atom names passes `p` (`atomUses`), by the recursor. -/
noncomputable def atomAll (p : V → Bool) (a : Atom) : Bool :=
  Atom.rec (motive := fun _ => Bool) (fun d _ => p d) (fun d a b => p d && p a && p b)
    (fun d a b => p d && p a && p b) (fun d s => p d && p s) (fun d q _ => p d && p q)
    (fun a b => p a && p b) (fun x i q => p x && p i && p q) (fun x y _ _ k => p x && p y && p k)
    (fun a b => p a && p b) (fun ins outs _ _ => vsAll p ins && vsAll p outs)
    (fun q run => p q && vsAll p run) (fun h => vsAll p (hintUses h)) (fun _ q => p q) a

theorem atomAll_eq (p : V → Bool) (a : Atom) : atomAll p a = (atomUses a).all p := by
  cases a <;> simp [atomAll, atomUses, vsAll_eq, Bool.and_assoc]

section Walk

variable (p : V → Bool) (tk : String → ℕ → Bool) (nm : String → Bool)

/-- A statement's check (`memB`). -/
noncomputable def memS (s : Stmt) : Bool :=
  Stmt.rec (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (atomAll p) (fun c _ _ bz bn => p c && bz && bn)
    (fun x arms ba => p x && decide (arms.length ≤ 2 ^ 64 - 1) && ba)
    (fun f args rets => nm f && vsAll p args && vsAll p rets)
    (fun c f args => p c && vsAll p args && nm f && tk f args.length)
    (fun x fs args rets => p x && vsAll p args && vsAll p rets &&
      decide (fs.length ≤ 2 ^ 64 - 1) && fs.all nm)
    (fun vs => vsAll p vs)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) s

/-- **A block's check**, in one walk: its values pass `p`, its `callIf`s `tk` on their arities, its
callees `nm`, and its `match`es and dispatches have at most `2^64 - 1` arms. -/
noncomputable def memB (ss : List Stmt) : Bool :=
  Stmt.rec_1 (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (atomAll p) (fun c _ _ bz bn => p c && bz && bn)
    (fun x arms ba => p x && decide (arms.length ≤ 2 ^ 64 - 1) && ba)
    (fun f args rets => nm f && vsAll p args && vsAll p rets)
    (fun c f args => p c && vsAll p args && nm f && tk f args.length)
    (fun x fs args rets => p x && vsAll p args && vsAll p rets &&
      decide (fs.length ≤ 2 ^ 64 - 1) && fs.all nm)
    (fun vs => vsAll p vs)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) ss

/-- Arms' check (`memB`). -/
noncomputable def memA (as : List (List Stmt)) : Bool :=
  Stmt.rec_2 (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (atomAll p) (fun c _ _ bz bn => p c && bz && bn)
    (fun x arms ba => p x && decide (arms.length ≤ 2 ^ 64 - 1) && ba)
    (fun f args rets => nm f && vsAll p args && vsAll p rets)
    (fun c f args => p c && vsAll p args && nm f && tk f args.length)
    (fun x fs args rets => p x && vsAll p args && vsAll p rets &&
      decide (fs.length ≤ 2 ^ 64 - 1) && fs.all nm)
    (fun vs => vsAll p vs)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) as

theorem memB_nil : memB p tk nm [] = true := rfl
theorem memB_cons (s : Stmt) (ss : List Stmt) :
    memB p tk nm (s :: ss) = (memS p tk nm s && memB p tk nm ss) := rfl
theorem memA_nil : memA p tk nm [] = true := rfl
theorem memA_cons (a : List Stmt) (as : List (List Stmt)) :
    memA p tk nm (a :: as) = (memB p tk nm a && memA p tk nm as) := rfl

theorem memB_append : ∀ (l l' : List Stmt), memB p tk nm (l ++ l') = (memB p tk nm l && memB p tk nm l')
  | [], _ => rfl
  | s :: l, l' => by
      rw [List.cons_append, memB_cons, memB_cons, memB_append l l', Bool.and_assoc]

/-- What a block's check gives: its uses pass `p`, its callees `nm`, and it is well formed in any
program whose arities `tk` underestimates. -/
def MemSpec (us : List V) (cs : List String) (wf : Core.Program → Bool) : Prop :=
  (∀ v ∈ us, p v = true) ∧ (∀ g ∈ cs, nm g = true) ∧
    ∀ P : Core.Program, (∀ f n, tk f n = true → P.Takes f n = true) → wf P = true

theorem memSpec_cons {us us' : List V} {cs cs' : List String} {wf wf' : Core.Program → Bool}
    (h : MemSpec p tk nm us cs wf) (h' : MemSpec p tk nm us' cs' wf') :
    MemSpec p tk nm (us ++ us') (cs ++ cs') fun P => wf P && wf' P :=
  ⟨fun v hv => (List.mem_append.mp hv).elim (h.1 v) (h'.1 v),
    fun g hg => (List.mem_append.mp hg).elim (h.2.1 g) (h'.2.1 g),
    fun P hP => Bool.and_eq_true_iff.mpr ⟨h.2.2 P hP, h'.2.2 P hP⟩⟩

theorem vsAll_mem {l : List V} (h : vsAll p l = true) : ∀ v ∈ l, p v = true := by
  rw [vsAll_eq] at h; exact List.all_eq_true.mp h

mutual
theorem memS_spec : ∀ s : Stmt, memS p tk nm s = true →
    MemSpec p tk nm (Stmt.uses s) (Stmt.callees s) fun P => Stmt.wf P s
  | .atom a, h => by
      refine ⟨fun v hv => ?_, fun g hg => by simp [Stmt.callees] at hg, fun P _ => rfl⟩
      have h' : atomAll p a = true := h
      rw [atomAll_eq] at h'
      exact List.all_eq_true.mp h' v hv
  | .ite c z n, h => by
      have h' : (p c && memB p tk nm z && memB p tk nm n) = true := h
      simp only [Bool.and_eq_true] at h'
      have hz := memB_spec z h'.1.2
      have hn := memB_spec n h'.2
      refine ⟨fun v hv => ?_, fun g hg => ?_, fun P hP => ?_⟩
      · simp only [Stmt.uses, List.mem_cons, List.mem_append] at hv
        rcases hv with rfl | hv | hv
        · exact h'.1.1
        · exact hz.1 v hv
        · exact hn.1 v hv
      · simp only [Stmt.callees, List.mem_append] at hg
        exact hg.elim (hz.2.1 g) (hn.2.1 g)
      · show (Stmt.wfList P z && Stmt.wfList P n) = true
        exact Bool.and_eq_true_iff.mpr ⟨hz.2.2 P hP, hn.2.2 P hP⟩
  | .match_ x arms, h => by
      have h' : (p x && decide (arms.length ≤ 2 ^ 64 - 1) && memA p tk nm arms) = true := h
      simp only [Bool.and_eq_true] at h'
      have ha := memA_spec arms h'.2
      refine ⟨fun v hv => ?_, fun g hg => ha.2.1 g (by simpa [Stmt.callees] using hg), fun P hP => ?_⟩
      · simp only [Stmt.uses, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact h'.1.1
        · exact ha.1 v hv
      · show (decide (arms.length ≤ 2 ^ 64 - 1) && Stmt.wfArms P arms) = true
        exact Bool.and_eq_true_iff.mpr ⟨h'.1.2, ha.2.2 P hP⟩
  | .call f args rets, h => by
      have h' : (nm f && vsAll p args && vsAll p rets) = true := h
      simp only [Bool.and_eq_true] at h'
      refine ⟨fun v hv => ?_, fun g hg => ?_, fun P _ => rfl⟩
      · simp only [Stmt.uses, List.mem_append] at hv
        exact hv.elim (vsAll_mem p h'.1.2 v) (vsAll_mem p h'.2 v)
      · simp only [Stmt.callees, List.mem_singleton] at hg
        exact hg ▸ h'.1.1
  | .callIf c f args, h => by
      have h' : (p c && vsAll p args && nm f && tk f args.length) = true := h
      simp only [Bool.and_eq_true] at h'
      refine ⟨fun v hv => ?_, fun g hg => ?_, fun P hP => ?_⟩
      · simp only [Stmt.uses, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact h'.1.1.1
        · exact vsAll_mem p h'.1.1.2 v hv
      · simp only [Stmt.callees, List.mem_singleton] at hg
        exact hg ▸ h'.1.2
      · exact hP _ _ h'.2
  | .dispatch x fs args rets, h => by
      have h' : (p x && vsAll p args && vsAll p rets && decide (fs.length ≤ 2 ^ 64 - 1) &&
          fs.all nm) = true := h
      simp only [Bool.and_eq_true] at h'
      refine ⟨fun v hv => ?_, fun g hg => List.all_eq_true.mp h'.2 g (by simpa [Stmt.callees] using hg),
        fun P _ => h'.1.2⟩
      simp only [Stmt.uses, List.mem_cons, List.mem_append] at hv
      rcases hv with rfl | hv | hv
      · exact h'.1.1.1.1
      · exact vsAll_mem p h'.1.1.1.2 v hv
      · exact vsAll_mem p h'.1.1.2 v hv
  | .ret vs, h => ⟨fun v hv => vsAll_mem p h v (by simpa [Stmt.uses] using hv),
      fun g hg => by simp [Stmt.callees] at hg, fun P _ => rfl⟩

theorem memB_spec : ∀ ss : List Stmt, memB p tk nm ss = true →
    MemSpec p tk nm (Stmt.usesList ss) (Stmt.blockCallees ss) fun P => Stmt.wfList P ss
  | [], _ => ⟨fun v hv => by simp [Stmt.usesList] at hv, fun g hg => by simp [Stmt.blockCallees] at hg,
      fun P _ => rfl⟩
  | s :: ss, h => by
      rw [memB_cons, Bool.and_eq_true] at h
      have := memSpec_cons p tk nm (memS_spec s h.1) (memB_spec ss h.2)
      simpa only [Stmt.usesList, Stmt.blockCallees, Stmt.wfList] using this

theorem memA_spec : ∀ as : List (List Stmt), memA p tk nm as = true →
    MemSpec p tk nm (Stmt.usesArms as) (Stmt.armsCallees as) fun P => Stmt.wfArms P as
  | [], _ => ⟨fun v hv => by simp [Stmt.usesArms] at hv, fun g hg => by simp [Stmt.armsCallees] at hg,
      fun P _ => rfl⟩
  | a :: as, h => by
      rw [memA_cons, Bool.and_eq_true] at h
      have := memSpec_cons p tk nm (memB_spec a h.1) (memA_spec as h.2)
      simpa only [Stmt.usesArms, Stmt.armsCallees, Stmt.wfArms] using this
end

/-- The ranges from `a` and from `a + n` make the range from `a`. -/
theorem memB_drop {l : List Stmt} {a n : ℕ} (h : memB p tk nm ((l.drop a).take n) = true)
    (h' : memB p tk nm (l.drop (a + n)) = true) : memB p tk nm (l.drop a) = true := by
  rw [← List.take_append_drop n (l.drop a), memB_append, List.drop_drop, h, h']; rfl

theorem memB_end {l : List Stmt} {a : ℕ} (ha : l.length ≤ a) : memB p tk nm (l.drop a) = true := by
  rw [List.drop_eq_nil_of_le ha]; rfl

end Walk

/-! ## Temporaries -/

/-- An atom's temporaries' indices (`atomTmps`), by the recursor. -/
noncomputable def atomTmpsR (a : Atom) : List ℕ :=
  Atom.rec (motive := fun _ => List ℕ) (fun _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ => []) (fun _ _ _ => []) (fun _ _ => []) (fun _ _ _ => [])
    (fun _ _ t1 t2 _ => [t1.idx, t2.idx]) (fun _ _ => []) (fun _ _ _ _ => []) (fun _ _ => [])
    (fun _ => []) (fun t _ => [t.idx]) a

/-- A block's temporaries' indices (`Stmt.tmpsList`), by the recursor. -/
noncomputable def tmpsR (ss : List Stmt) : List ℕ :=
  Stmt.rec_1 (motive_1 := fun _ => List ℕ) (motive_2 := fun _ => List ℕ) (motive_3 := fun _ => List ℕ)
    atomTmpsR (fun _ _ _ tz tn => tz ++ tn) (fun _ _ ta => ta) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ _ => []) (fun _ => []) [] (fun _ _ t ts => t ++ ts) [] (fun _ _ t ts => t ++ ts) ss

theorem tmpsR_eq (ss : List Stmt) : tmpsR ss = (Stmt.tmpsList ss).map V.idx :=
  Stmt.rec_1
    (motive_1 := fun s => Stmt.rec (motive_1 := fun _ => List ℕ) (motive_2 := fun _ => List ℕ)
      (motive_3 := fun _ => List ℕ) atomTmpsR (fun _ _ _ tz tn => tz ++ tn) (fun _ _ ta => ta)
      (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ => []) (fun _ => []) [] (fun _ _ t ts => t ++ ts)
      [] (fun _ _ t ts => t ++ ts) s = (Stmt.tmps s).map V.idx)
    (motive_2 := fun ss => tmpsR ss = (Stmt.tmpsList ss).map V.idx)
    (motive_3 := fun as => Stmt.rec_2 (motive_1 := fun _ => List ℕ) (motive_2 := fun _ => List ℕ)
      (motive_3 := fun _ => List ℕ) atomTmpsR (fun _ _ _ tz tn => tz ++ tn) (fun _ _ ta => ta)
      (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ => []) (fun _ => []) [] (fun _ _ t ts => t ++ ts)
      [] (fun _ _ t ts => t ++ ts) as = (Stmt.tmpsArms as).map V.idx)
    (fun a => by cases a <;> rfl)
    (fun _ _ _ hz hn => by
      simp only [Stmt.tmps, List.map_append]; exact congrArg₂ (· ++ ·) hz hn)
    (fun _ _ ha => by simp only [Stmt.tmps]; exact ha)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ => rfl) rfl
    (fun _ _ hs hss => by
      simp only [Stmt.tmpsList, List.map_append]; exact congrArg₂ (· ++ ·) hs hss)
    rfl
    (fun _ _ ha has => by
      simp only [Stmt.tmpsArms, List.map_append]; exact congrArg₂ (· ++ ·) ha has)
    ss

/-- The bit mask of indices. -/
def natMask : List ℕ → ℕ
  | [] => 0
  | x :: xs => natMask xs ||| 1 <<< x

theorem testBit_natMask {x : ℕ} : ∀ {l : List ℕ}, x ∈ l → (natMask l).testBit x = true
  | y :: ys, h => by
      rw [natMask, Nat.testBit_or, Bool.or_eq_true]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (by simp [Nat.testBit_shiftLeft])
      · exact Or.inl (testBit_natMask h)

/-- A value outside the mask `m`. -/
def avoid (m : ℕ) (v : V) : Bool := !m.testBit v.idx

/-- A callee other than `main`. -/
def notMain (g : String) : Bool := decide (g ≠ "main")

/-! ## A function's check -/

/-- Function `j`'s `callIf` to `f` with `n` arguments: `f` is its callee of an index `tt` gives
arity `n`. -/
def takesJ (tt : NTree ℕ) (j : ℕ) (f : String) (n : ℕ) : Bool :=
  match calleeIdx j f with
  | some k => decide (tt.find k = some n)
  | none => false

/-- Function `j` takes the arity `tt` gives it, its parameters distinct. -/
def takesOk (tt : NTree ℕ) (j : ℕ) (fn : Fn) : Bool :=
  match tt.find j with
  | some n => Nat.beq fn.params.length n && nodupBits (fn.params.map V.idx) 0
  | none => true

/-- Function `j`'s check but its body's: its temporaries `ts` distinct, no parameter among them,
and its arity in `tt`. -/
noncomputable def memHead (tt : NTree ℕ) (j : ℕ) (fn : Fn) (ts : List ℕ) : Bool :=
  nodupBits ts 0 && vsAll (avoid (natMask ts)) fn.params && takesOk tt j fn

/-- The check of a body whose temporaries are `ts`. -/
noncomputable def memBody (tt : NTree ℕ) (j : ℕ) (ts : List ℕ) (l : List Stmt) : Bool :=
  memB (avoid (natMask ts)) (takesJ tt j) notMain l

/-- **Function `j`'s memory check**, `tt` the arities of the functions `callIf` names. -/
noncomputable def memF (tt : NTree ℕ) (j : ℕ) (fn : Fn) : Bool :=
  memHead tt j fn (tmpsR fn.body) && memBody tt j (tmpsR fn.body) fn.body

theorem memBody_drop {tt : NTree ℕ} {j : ℕ} {ts : List ℕ} {l : List Stmt} {a n : ℕ}
    (h : memBody tt j ts ((l.drop a).take n) = true) (h' : memBody tt j ts (l.drop (a + n)) = true) :
    memBody tt j ts (l.drop a) = true :=
  memB_drop _ _ _ h h'

theorem memBody_end {tt : NTree ℕ} {j : ℕ} {ts : List ℕ} {l : List Stmt} {a : ℕ} (ha : l.length ≤ a) :
    memBody tt j ts (l.drop a) = true :=
  memB_end _ _ _ ha

/-- A function checked by parts: its temporaries `ts`, its head, its body. -/
theorem memF_of {tt : NTree ℕ} {j : ℕ} {fn : Fn} {ts : List ℕ} (h : tmpsR fn.body = ts)
    (hh : memHead tt j fn ts = true) (hb : memBody tt j ts fn.body = true) : memF tt j fn = true := by
  rw [memF, h, hh, hb]; rfl

/-! ## Soundness -/

theorem fresh_of_memF {tt : NTree ℕ} {j : ℕ} {fn : Fn} (h : memF tt j fn = true) : fn.Fresh := by
  simp only [memF, memHead, memBody, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hnd, hp⟩, -⟩, hb⟩ := h
  have hu := (memB_spec _ _ _ fn.body hb).1
  have ht := tmpsR_eq fn.body
  have hin : ∀ t ∈ Stmt.tmpsList fn.body, (natMask (tmpsR fn.body)).testBit t.idx = true :=
    fun t h => testBit_natMask (ht ▸ List.mem_map_of_mem h)
  refine ⟨List.Nodup.of_map V.idx (ht ▸ (nodup_of_nodupBits hnd).1), fun t htm => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · have := hu t hm
    simp [avoid, hin t htm] at this
  · have := vsAll_mem _ hp t hm
    simp [avoid, hin t htm] at this

section Program

variable {tt : NTree ℕ} (hall : RangeOk (memF tt) 0 coreProgram.length)
include hall

theorem memAll_get {j : ℕ} (hj : j < coreProgram.length) : memF tt j coreProgram[j] = true :=
  RangeOk.all hall hj

/-- **The guest's temporaries are fresh.** -/
theorem memAll_fresh : coreProgram.Fresh := by
  intro fn hfn
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hfn
  exact fresh_of_memF (memAll_get hall hj)

theorem takesJ_sound {j : ℕ} {f : String} {n : ℕ} (h : takesJ tt j f n = true) :
    coreProgram.Takes f n = true := by
  unfold takesJ at h
  rcases hk : calleeIdx j f with _ | k
  · rw [hk] at h; cases h
  rw [hk, decide_eq_true_eq] at h
  have hs := calleeIdx_spec hk
  rcases hg : coreProgram[k]? with _ | fn
  · rw [hg] at hs; cases hs
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  rw [hg, Option.map_some, Option.some.injEq] at hs
  have hm := memAll_get hall hlt
  simp only [memF, memHead, Bool.and_eq_true] at hm
  have ht := hm.1.2
  rw [takesOk, h, Bool.and_eq_true, Nat.beq_eq] at ht
  rw [Program.Takes, ← hs, coreProgram_find_getElem hlt]
  simp only [ht.1, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
  exact List.Nodup.of_map V.idx (nodup_of_nodupBits ht.2).1

/-- **The guest is well formed.** -/
theorem memAll_wf : coreProgram.Wf := by
  intro fn hfn
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hfn
  have hm := memAll_get hall hj
  simp only [memF, memBody, Bool.and_eq_true] at hm
  exact (memB_spec _ _ _ _ hm.2).2.2 coreProgram fun _ _ h => takesJ_sound hall h

/-- **No function calls `main`.** -/
theorem memAll_callees {j : ℕ} (hj : j < coreProgram.length) :
    ∀ g ∈ Stmt.blockCallees coreProgram[j].body, g ≠ "main" := by
  have hm := memAll_get hall hj
  simp only [memF, memBody, Bool.and_eq_true] at hm
  intro g hg
  simpa [notMain] using (memB_spec _ _ _ _ hm.2).2.1 g hg

end Program

end
end LeanVM.Guest.Memory
