/-
  LeanVM.Guest.Backend.Guest.Cpl.Static

  The static facts of one placed function the completeness instance reads: its frame size, its
  parameters' cells, its range checks' temporaries' cells and its frame runs' cells, as a test the
  kernel evaluates function by function, and what a success says.
-/

module

public import LeanVM.Guest.Backend.Piece
public import LeanVM.Guest.Backend.Sound.Compiles
public import LeanVM.Guest.Backend.Complete.Spec
public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.Memory.Fresh
public import LeanVM.Guest.Memory.Alloc

/-!
# A placed function's static facts

`staticOk loops tf pf n` tests the placed function `pf` of the traced function `tf` against the
frame size `n`: `pf`'s frame size is `n`; `tf` is a loop helper by its name (`isLoopName`, which
the back end reads) exactly when it is one by its body (`Fn.loop`, which the allocator reads); a
registered loop helper's self pointer cell `2 + nargs` is in its frame and no temporary's cell; the
parameters' cells are in the frame; parameter `k` is at cell `2 + k`; the values of every `return`
are at the return cells, `2 + nargs + k`; every range check temporary of the body is at a cell of
`[2, n)`, the temporaries at distinct cells; every frame run `frameAddr p (r :: rs)` of the body is
at consecutive cells from `r`'s, ending at most at `n`, at no temporary's cell; two values of the
frame runs at one cell are one value. `staticOk_spec` turns a success into `StaticFacts`.

The kernel shares no evaluation between the copies of a term: the places' trie is evaluated once
before the tests (`withLocs`), and the set of the temporaries' cells once before the runs' test
(`Trie.seq`).
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- `k m`, the trie of `m` evaluated first. -/
def withLocs {α β : Type} (m : VMap α) (k : VMap α → β) : β := m.t.seq fun t => k ⟨t⟩

theorem withLocs_eq {α β : Type} (m : VMap α) (k : VMap α → β) : withLocs m k = k m := by
  cases m
  exact Trie.seq_eq _ _

mutual
/-- The values of the `return`s of a statement. -/
def retS : Stmt → List (List V)
  | .ret vs => [vs]
  | .ite _ z n => retL z ++ retL n
  | .match_ _ arms => retA arms
  | _ => []

/-- The values of the `return`s of a block. -/
def retL : List Stmt → List (List V)
  | [] => []
  | s :: ss => retS s ++ retL ss

/-- The values of the `return`s of arms. -/
def retA : List (List Stmt) → List (List V)
  | [] => []
  | a :: as => retL a ++ retA as
end

/-- The values `vs` are at the consecutive cells from `c`. -/
def consecFrom (locs : VMap Loc) : List V → ℕ → Bool
  | [], _ => true
  | v :: vs, c => Complete.cellP locs v == some c && consecFrom locs vs (c + 1)

/-- The values `vs` are at the consecutive cells from `c`, none of them in the set `tset`. -/
def runFrom (locs : VMap Loc) (tset : NMap Unit) : List V → ℕ → Bool
  | [], _ => true
  | v :: vs, c => Complete.cellP locs v == some c && !tset.contains c && runFrom locs tset vs (c + 1)

/-- Every value of `ts` is at a cell of `[2, n)`. -/
def cellsIn (locs : VMap Loc) (ts : List V) (n : ℕ) : Bool :=
  ts.all fun t => match Complete.cellP locs t with
    | some c => Nat.ble 2 c && Nat.blt c n
    | none => false

/-- The set of the cells of `ts`. -/
def cellSet (locs : VMap Loc) (ts : List V) : NMap Unit :=
  ts.foldl (fun m t => m.insert ((Complete.cellP locs t).getD 0) ()) {}

/-- A frame run is at consecutive cells ending at most at `n`, at no cell of `tset`. -/
def runOk (locs : VMap Loc) (tset : NMap Unit) (n : ℕ) : Atom → Bool
  | .frameAddr _ (r :: rs) => match Complete.cellP locs r with
    | some c => Nat.ble (c + (rs.length + 1)) n && runFrom locs tset (r :: rs) c
    | none => false
  | _ => true

/-- The values of the frame runs among the atoms. -/
def runVals : List Atom → List V
  | [] => []
  | .frameAddr _ rs :: as => rs ++ runVals as
  | _ :: as => runVals as

theorem mem_runVals : ∀ {as : List Atom} {p : V} {rs : List V} {v : V}, Atom.frameAddr p rs ∈ as →
    v ∈ rs → v ∈ runVals as
  | [], _, _, _, h, _ => absurd h List.not_mem_nil
  | a :: as, p, rs, v, h, hv => by
    rcases List.mem_cons.mp h with rfl | h
    · simp [runVals, hv]
    · have := mem_runVals h hv
      cases a <;> simp [runVals, this]

/-- The values `vs` with a cell, at one cell each one value, `seen` the values met by cell. -/
def cellFun (locs : VMap Loc) : List V → NMap V → Bool
  | [], _ => true
  | v :: vs, seen => match Complete.cellP locs v with
    | some c => match seen.get? c with
      | some w => w == v && cellFun locs vs seen
      | none => cellFun locs vs (seen.insert c v)
    | none => cellFun locs vs seen

/-- **The static test of a placed function** against the frame size `n`. -/
def staticOk (loops : Loops) (tf : TracedFn) (pf : Placed) (n : ℕ) : Bool :=
  pf.fn.frameSize == n && isLoopName tf.core.name == tf.core.loop &&
  (!(loops[tf.core.name]?).any (·.registered) || Nat.blt (2 + tf.core.params.length) n) &&
  Nat.ble (2 + tf.core.params.length) n &&
  withLocs pf.locs fun m =>
    consecFrom m tf.core.params 2 &&
      (retL tf.core.body).all (fun vs => consecFrom m vs (2 + tf.core.params.length)) &&
      cellsIn m (Stmt.tmpsList tf.core.body) n &&
      natsDistinct ((Stmt.tmpsList tf.core.body).map fun t => (Complete.cellP m t).getD 0) &&
      cellFun m (runVals (Lift.blockAtoms tf.core.body)) {} &&
      (cellSet m (Stmt.tmpsList tf.core.body)).t.seq fun tt =>
        (!(loops[tf.core.name]?).any (·.registered) ||
          !NMap.contains ⟨tt⟩ (2 + tf.core.params.length)) &&
        (Lift.blockAtoms tf.core.body).all (runOk m ⟨tt⟩ n)

/-- **What the static test says.** -/
structure StaticFacts (loops : Loops) (tf : TracedFn) (pf : Placed) (n : ℕ) : Prop where
  frame : pf.fn.frameSize = n
  loop : isLoopName tf.core.name = tf.core.loop
  self : Complete.registered loops tf.core.name → 2 + tf.core.params.length < n
  selfTmp : Complete.registered loops tf.core.name → ∀ t ∈ Stmt.tmpsList tf.core.body,
    Complete.cellP pf.locs t ≠ some (2 + tf.core.params.length)
  paramsIn : 2 + tf.core.params.length ≤ n
  params : ∀ k (hk : k < tf.core.params.length), Complete.cellP pf.locs tf.core.params[k] = some (2 + k)
  rets : ∀ vs ∈ retL tf.core.body, ∀ k (hk : k < vs.length),
    Complete.cellP pf.locs vs[k] = some (2 + tf.core.params.length + k)
  tmpIn : ∀ t ∈ Stmt.tmpsList tf.core.body, ∃ c, Complete.cellP pf.locs t = some c ∧ 2 ≤ c ∧ c < n
  tmpInj : ∀ t ∈ Stmt.tmpsList tf.core.body, ∀ t' ∈ Stmt.tmpsList tf.core.body,
    Complete.cellP pf.locs t = Complete.cellP pf.locs t' → t = t'
  run : ∀ p r rs, Atom.frameAddr p (r :: rs) ∈ Lift.blockAtoms tf.core.body → ∃ c,
    Complete.cellP pf.locs r = some c ∧ c + (rs.length + 1) ≤ n ∧ ∀ k (hk : k < (r :: rs).length),
      Complete.cellP pf.locs (r :: rs)[k] = some (c + k) ∧
        ∀ t ∈ Stmt.tmpsList tf.core.body, Complete.cellP pf.locs t ≠ some (c + k)
  runsFun : ∀ v ∈ runVals (Lift.blockAtoms tf.core.body), ∀ v' ∈ runVals (Lift.blockAtoms tf.core.body),
    ∀ c, Complete.cellP pf.locs v = some c → Complete.cellP pf.locs v' = some c → v = v'

theorem consecFrom_spec {locs : VMap Loc} : ∀ {vs : List V} {c : ℕ}, consecFrom locs vs c = true →
    ∀ k (hk : k < vs.length), Complete.cellP locs vs[k] = some (c + k)
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | v :: vs, c, h, k, hk => by
    simp only [consecFrom, Bool.and_eq_true, beq_iff_eq] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := consecFrom_spec h.2 k (by simpa using hk)
      simp only [List.getElem_cons_succ]
      rw [this]
      congr 1
      omega

theorem runFrom_spec {locs : VMap Loc} {tset : NMap Unit} : ∀ {vs : List V} {c : ℕ},
    runFrom locs tset vs c = true → ∀ k (hk : k < vs.length),
      Complete.cellP locs vs[k] = some (c + k) ∧ tset.contains (c + k) = false
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | v :: vs, c, h, k, hk => by
    simp only [runFrom, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases k with
    | zero => simpa using ⟨h1, h2⟩
    | succ k =>
      have := runFrom_spec h3 k (by simpa using hk)
      simp only [List.getElem_cons_succ]
      rw [show c + (k + 1) = c + 1 + k by omega]
      exact this

theorem cellSet_go {locs : VMap Loc} : ∀ (ts : List V) (m : NMap Unit) (c : ℕ),
    m.contains c = true → (ts.foldl (fun m t => m.insert ((Complete.cellP locs t).getD 0) ()) m).contains c = true
  | [], _, _, h => h
  | t :: ts, m, c, h => by
    rw [List.foldl_cons]
    refine cellSet_go ts _ c ?_
    simp only [NMap.contains, NMap.get?_insert] at h ⊢
    split <;> simp_all

theorem cellSet_mem {locs : VMap Loc} : ∀ {ts : List V} (m : NMap Unit) {t : V} {c : ℕ},
    t ∈ ts → Complete.cellP locs t = some c →
      (ts.foldl (fun m t => m.insert ((Complete.cellP locs t).getD 0) ()) m).contains c = true
  | [], _, _, _, h, _ => absurd h List.not_mem_nil
  | t' :: ts, m, t, c, h, hc => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · refine cellSet_go ts _ c ?_
      simp [NMap.contains, NMap.get?_insert, hc]
    · exact cellSet_mem _ h hc

theorem cellFun_spec {locs : VMap Loc} : ∀ {vs : List V} {seen : NMap V}, cellFun locs vs seen = true →
    (∀ c w, seen.get? c = some w → Complete.cellP locs w = some c) →
    ∀ v ∈ vs, ∀ c, Complete.cellP locs v = some c →
      (∀ w, seen.get? c = some w → w = v) ∧ ∀ v' ∈ vs, Complete.cellP locs v' = some c → v' = v
  | [], _, _, _, v, hv, _, _ => absurd hv List.not_mem_nil
  | v0 :: vs, seen, h, hinv, v, hv, c, hc => by
    unfold cellFun at h
    cases hc0 : Complete.cellP locs v0 with
    | none =>
      simp only [hc0] at h
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [hc0] at hc; cases hc
      · obtain ⟨h1, h2⟩ := cellFun_spec h hinv v hv c hc
        refine ⟨h1, fun v' hv' hc' => ?_⟩
        rcases List.mem_cons.mp hv' with rfl | hv'
        · rw [hc0] at hc'; cases hc'
        · exact h2 v' hv' hc'
    | some c0 =>
      simp only [hc0] at h
      cases hs : seen.get? c0 with
      | some w =>
        simp only [hs] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hw, h⟩ := h
        have ih := cellFun_spec h hinv
        rcases List.mem_cons.mp hv with rfl | hv
        · have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc)
          subst hcc
          refine ⟨fun w' hw' => ?_, fun v' hv' hc' => ?_⟩
          · rw [hs] at hw'
            exact (Option.some.inj hw').symm.trans hw
          · rcases List.mem_cons.mp hv' with rfl | hv'
            · rfl
            · exact ((ih v' hv' c0 hc').1 w hs).symm.trans hw
        · obtain ⟨h1, h2⟩ := ih v hv c hc
          refine ⟨h1, fun v' hv' hc' => ?_⟩
          rcases List.mem_cons.mp hv' with rfl | hv'
          · have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc')
            subst hcc
            exact hw.symm.trans (h1 w hs)
          · exact h2 v' hv' hc'
      | none =>
        simp only [hs] at h
        have hinv' : ∀ c w, (seen.insert c0 v0).get? c = some w → Complete.cellP locs w = some c := by
          intro c' w hw
          rw [NMap.get?_insert] at hw
          split_ifs at hw with hcc
          · cases hw; rw [hcc]; exact hc0
          · exact hinv c' w hw
        have ih := cellFun_spec h hinv'
        rcases List.mem_cons.mp hv with rfl | hv
        · have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc)
          subst hcc
          refine ⟨fun w' hw' => (by rw [hs] at hw'; cases hw'), fun v' hv' hc' => ?_⟩
          rcases List.mem_cons.mp hv' with rfl | hv'
          · rfl
          · exact ((ih v' hv' c0 hc').1 v (by simp [NMap.get?_insert])).symm
        · obtain ⟨h1, h2⟩ := ih v hv c hc
          refine ⟨fun w' hw' => h1 w' ?_, fun v' hv' hc' => ?_⟩
          · rw [NMap.get?_insert]
            split_ifs with hcc
            · subst hcc; rw [hs] at hw'; cases hw'
            · exact hw'
          · rcases List.mem_cons.mp hv' with rfl | hv'
            · have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc')
              subst hcc
              exact h1 v' (by simp [NMap.get?_insert])
            · exact h2 v' hv' hc'

/-- **What a success of the static test says.** -/
theorem staticOk_spec {loops : Loops} {tf : TracedFn} {pf : Placed} {n : ℕ}
    (h : staticOk loops tf pf n = true) : StaticFacts loops tf pf n := by
  unfold staticOk at h
  rw [withLocs_eq, Trie.seq_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hfs, hlp⟩, hself⟩, hpin⟩, ⟨⟨⟨⟨⟨hpar, hret⟩, hin⟩, hnd⟩, hfun⟩, hselfT, hrun⟩⟩ := h
  have hfs : pf.fn.frameSize = n := beq_iff_eq.mp hfs
  have hlp : isLoopName tf.core.name = tf.core.loop := beq_iff_eq.mp hlp
  have hself : Complete.registered loops tf.core.name → 2 + tf.core.params.length < n := by
    intro hr
    unfold Complete.registered at hr
    rw [hr] at hself
    simpa using hself
  have hselfT : Complete.registered loops tf.core.name → ∀ t ∈ Stmt.tmpsList tf.core.body,
      Complete.cellP pf.locs t ≠ some (2 + tf.core.params.length) := by
    intro hr t ht he
    unfold Complete.registered at hr
    rw [hr] at hselfT
    have h2 : NMap.contains ⟨(cellSet pf.locs (Stmt.tmpsList tf.core.body)).t⟩
        (2 + tf.core.params.length) = false := by simpa using hselfT
    have h3 : true = false := (cellSet_mem (locs := pf.locs) {} ht he).symm.trans h2
    cases h3
  have hrun := List.all_eq_true.mp hrun
  have hin' : ∀ t ∈ Stmt.tmpsList tf.core.body, ∃ c, Complete.cellP pf.locs t = some c ∧ 2 ≤ c ∧ c < n := by
    intro t ht
    have := List.all_eq_true.mp hin t ht
    cases hc : Complete.cellP pf.locs t with
    | none => rw [hc] at this; cases this
    | some c =>
      rw [hc] at this
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
      exact ⟨c, rfl, this⟩
  refine ⟨hfs, hlp, hself, hselfT, Nat.ble_eq.mp hpin,
    fun k hk => by simpa [Nat.add_comm] using consecFrom_spec hpar k hk,
    fun vs hvs k hk => consecFrom_spec (List.all_eq_true.mp hret vs hvs) k hk, hin', ?_, ?_,
    fun v hv v' hv' c hc hc' => ((cellFun_spec hfun (by simp) v hv c hc).2 v' hv' hc').symm⟩
  · intro t ht t' ht' he
    refine List.inj_on_of_nodup_map (natsDistinct_nodup hnd) ht ht' ?_
    show (Complete.cellP pf.locs t).getD 0 = (Complete.cellP pf.locs t').getD 0
    rw [he]
  · intro p r rs hm
    have := hrun _ hm
    simp only [runOk] at this
    cases hc : Complete.cellP pf.locs r with
    | none => rw [hc] at this; cases this
    | some c =>
      rw [hc] at this
      simp only [Bool.and_eq_true, Nat.ble_eq] at this
      refine ⟨c, rfl, this.1, fun k hk => ?_⟩
      obtain ⟨h1, h2⟩ := runFrom_spec this.2 k hk
      refine ⟨h1, fun t ht he => ?_⟩
      have h3 : true = false := (cellSet_mem (locs := pf.locs) {} ht he).symm.trans h2
      cases h3

/-! ## The returned values of a path -/

theorem pre_ret {es : List Ev} {o : Out} {es' : List Ev} {vs : List V} (h : o.pre es = .ret es' vs) :
    ∃ es0, o = .ret es0 vs := by
  cases o with
  | fall _ => cases h
  | ret es0 vs0 => cases h; exact ⟨es0, rfl⟩
  | stuck => cases h

theorem seq_ret {o k : Out} {es : List Ev} {vs : List V} (h : o.seq k = .ret es vs) :
    (∃ e, o = .ret e vs) ∨ ∃ e, k = .ret e vs := by
  cases o with
  | fall e0 =>
    obtain ⟨e1, he⟩ := pre_ret h
    exact Or.inr ⟨e1, he⟩
  | ret e0 vs0 =>
    simp only [Out.seq, Out.ret.injEq] at h
    exact Or.inl ⟨e0, by rw [h.2]⟩
  | stuck => cases h

theorem pick_not_ret {σ : Val} {x : V} {args rets : List V} {es : List Ev} {vs : List V} :
    ∀ (fs : List String) (j : ℕ), pick σ x args rets j fs ≠ .ret es vs
  | [], _, h => by simp [pick] at h
  | f :: fs, j, h => by
    unfold pick at h
    split at h
    · cases h
    · exact pick_not_ret fs (j + 1) h

mutual
theorem walk1_ret {σ : Val} : ∀ (s : Stmt) {es : List Ev} {vs : List V}, walk1 σ s = .ret es vs →
    vs ∈ retS s
  | .atom _, _, _, h => by simp [walk1] at h
  | .ite c z n, es, vs, h => by
    simp only [walk1] at h
    obtain ⟨es0, h0⟩ := pre_ret h
    simp only [retS, List.mem_append]
    split_ifs at h0
    · exact Or.inl (walk_ret z h0)
    · exact Or.inr (walk_ret n h0)
  | .match_ x arms, es, vs, h => by
    simp only [walk1] at h
    exact walkArms_ret x arms 0 h
  | .call .., _, _, h => by simp [walk1] at h
  | .callIf .., _, _, h => by simp [walk1] at h
  | .dispatch x fs args rets, _, _, h => by simp only [walk1] at h; exact absurd h (pick_not_ret fs 0)
  | .ret vs', es, vs, h => by
    simp only [walk1, Out.ret.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [retS]

theorem walk_ret {σ : Val} : ∀ (ss : List Stmt) {es : List Ev} {vs : List V}, walk σ ss = .ret es vs →
    vs ∈ retL ss
  | [], _, _, h => by simp [walk] at h
  | s :: ss, es, vs, h => by
    simp only [walk] at h
    simp only [retL, List.mem_append]
    rcases seq_ret h with ⟨e, he⟩ | ⟨e, he⟩
    · exact Or.inl (walk1_ret s he)
    · exact Or.inr (walk_ret ss he)

theorem walkArms_ret {σ : Val} (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {es : List Ev} {vs : List V},
    walkArms σ x j arms = .ret es vs → vs ∈ retA arms
  | [], _, _, _, h => by simp [walkArms] at h
  | a :: as, j, es, vs, h => by
    unfold walkArms at h
    simp only [retA, List.mem_append]
    split_ifs at h
    · exact Or.inl (walk_ret a h)
    · exact Or.inr (walkArms_ret x as (j + 1) h)
end

end
end LeanVM.Guest.Backend.Cpl
