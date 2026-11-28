/-
  LeanVM.Guest.Complete.MainWinGen

  A body's windows over a list of temporaries read per memory: `WinGen.lean`'s runs, calls and
  branches with touches, a memory-decided range check, and `callIf`.
-/

module

public import LeanVM.Guest.B1.VsC.WinGen
public import LeanVM.Guest.Complete.MainSeg

/-!
# Windows over temporaries

`WinGen.lean` cuts `verify_sub`'s body on `rdOver σ0`, whose temporaries are its range checks'. A body
with touches and guarded calls (`main`) takes the same windows on `over T σ0` (`MainSeg.lean`), `T`
the pairs `(t, x)` of its range checks' and touches' temporaries, each `t` reading the word at
`σ0 x`:

* **Runs.** `segA_runT`: a run passing `tOk T` (no value of `T` named outside its own range check or
  touch, no `frameAddr` or `assertNe`) whose atoms satisfy their equations on `σ0` is a window from
  `RunHypT`: as `RunHyp`, its pure side conditions `PureT` (a range check's operands in `K`, a touch's
  pointer in `K`) and on every memory with `LowDef k`, `Pre` and `O` its words `MemT` (a load's word,
  a range check's or a touch's word defined).
* **Calls.** `segA_callWT`, from the callee's `CallAtA`, as `segA_callW`.
* **Guarded calls.** `.cif c g args` (`callIf`): its guard in `K`; taken (`σ0 c ≠ 0`) from the
  callee's `CallAtA`, skipped a phantom past its tail's frame.
* **Composition.** `WinsHypT`, `SegT`, `segA_winsT`, `seg_iteT`, `seg_bindT`, `winsHypT_append`,
  as `WinGen.lean`'s.
* **The cursor.** Each entered call ends within `2^52` of the callees' cursor when that cursor is
  below `2^57`, and a skipped one's tail frame is below `2^51`: a window of `n` calls from a cursor
  `kc` with `kc + n·2^52 < 2^59` ends its callees within `kc + n·2^52` (`SegT`). This bounds a body's
  end before any memory, so that its words have one.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The kernel checks -/

/-- `v` is no temporary of `T`. -/
def noTB (T : List (V × V)) (v : V) : Bool := (T.lookup v).isNone

/-- **An atom a run window takes**: its values no temporary of `T`, a range check's and a touch's own
temporaries paired in `T` with the value whose word they read, no `frameAddr` or `assertNe`. -/
def tOk (T : List (V × V)) (a : Atom) : Bool :=
  (atomUses a).all (noTB T) &&
    match a with
    | .rangeCheck x y t1 t2 _ => decide (T.lookup t1 = some x) && decide (T.lookup t2 = some y)
    | .touch t p => decide (T.lookup t = some p)
    | .frameAddr .. | .assertNe .. => false
    | _ => true

/-- **A statement a call window takes**: a `call` or a `dispatch` (of at most `64` callees), its
values no temporary. -/
def callOkT (T : List (V × V)) : Stmt → Bool
  | .call _ a r => (a ++ r).all (noTB T)
  | .dispatch x gs a r => (x :: (a ++ r)).all (noTB T) && decide (gs.length ≤ 64)
  | _ => false

/-! ## What a run asks -/

/-- **What an atom asks of the valuation** beyond its equations. -/
def PureT (σ : Val) : Atom → Prop
  | .mul d x y => if x.idx < d.idx ∧ y.idx < d.idx then True else σ y ≠ 0
  | .assertEq x y => σ x + σ y = 0
  | .assertInK x y => IsInK (σ x) ∧ IsInK (σ y)
  | .rangeCheck x y _ _ k => IsInK (σ x) ∧ IsInK (σ y) ∧ (k.idx < y.idx → σ x ≠ 0)
  | .touch _ p => IsInK (σ p)
  | _ => True

/-- **What an atom asks of a memory**: a load's word, a range check's two words and a touch's word
defined. -/
def MemT (rd : Reader) (σ : Val) : Atom → Prop
  | .load d p off => LoadHolds rd (σ p) off (σ d)
  | .rangeCheck x y _ _ _ =>
      (rd ((σ x).limb 0 * addressOfIndex 0)).isSome ∧ (rd ((σ y).limb 0 * addressOfIndex 0)).isSome
  | .touch _ p => (rd ((σ p).limb 0 * addressOfIndex 0)).isSome
  | _ => True

/-- **A run's hypotheses**: as `RunHyp`, with `PureT` and `MemT`. -/
structure RunHypT (k : ℕ) (σ0 : Val) (w : ℕ → E) (a : ℕ) (Own R D : ℕ → Prop) (Pre O : Reader → Prop)
    (as : List Atom) : Prop where
  bufs : (allocDsts (as.map Ev.atom)).map (fun v => w v.idx) =
    (bases a (allocs σ0 (as.map Ev.atom))).map (fun b => ofK (addressOfIndex b))
  loads : ∀ A ∈ loadAddrs σ0 (as.map Ev.atom), ∃ i, A = addressOfIndex i ∧ (Own i ∨ R i ∨ D i)
  hints : ∀ A ∈ heapHintAddrs σ0 (as.map Ev.atom), ∃ i, A = addressOfIndex i ∧ (Own i ∨ R i ∨ D i)
  pure : ∀ x ∈ as, PureT σ0 x
  mem : ∀ rd, LowDef k rd → Pre rd → O rd → ∀ x ∈ as, MemT rd σ0 x

/-! ## One atom, one run -/

theorem tOk_uses {T : List (V × V)} {a : Atom} (h : tOk T a = true) : ∀ v ∈ atomUses a, T.lookup v = none := by
  intro v hv
  simp only [tOk, Bool.and_eq_true, List.all_eq_true] at h
  exact Option.isNone_iff_eq_none.mp (h.1 v hv)

/-- **An atom of a run holds on every memory's valuation** from its equations on `σ0`, its pure
side condition and its memory facts. -/
theorem holdsT_fact {T : List (V × V)} {rd0 rd : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val} {a : Atom}
    (hok : tOk T a = true) (hg : Good rd0 S w σ0 a) (hp : PureT σ0 a) (hm : MemT rd σ0 a) :
    a.Holds rd (over T σ0 rd) := by
  have hu := tOk_uses hok
  have hc : ∀ (b : Atom), atomTmps b = [] → atomUses b = atomUses a →
      (b.Holds rd (over T σ0 rd) ↔ b.Holds rd σ0) := fun b ht hb =>
    atom_holds_congr b fun v hv => by
      rw [ht, List.append_nil, hb] at hv; exact over_eq (hu v hv)
  cases a with
  | rangeCheck x y t1 t2 kk =>
    simp only [tOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hx, hy, h0⟩ := hp
    exact holdsT_rc hok.2.1 hok.2.2 (hu x (by simp [atomUses])) (hu y (by simp [atomUses]))
      (hu kk (by simp [atomUses])) hg hx hy hm.1 hm.2 h0
  | touch t p =>
    simp only [tOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact holdsT_touch hok.2 (hu p (by simp [atomUses])) hp hm
  | frameAddr p run => simp [tOk] at hok
  | assertNe x i p => simp [tOk] at hok
  | const d e => exact (hc (.const d e) rfl rfl).mpr hg
  | add d x y => exact (hc (.add d x y) rfl rfl).mpr hg
  | copy d s => exact (hc (.copy d s) rfl rfl).mpr hg
  | mul d x y => exact (hc (.mul d x y) rfl rfl).mpr (holds_of_good (rd := rd0) (a := .mul d x y) hg hp)
  | load d p off => exact (hc (.load d p off) rfl rfl).mpr hm
  | assertEq x y => exact (hc (.assertEq x y) rfl rfl).mpr hp
  | assertInK x y => exact (hc (.assertInK x y) rfl rfl).mpr hp
  | keccak ins outs i o =>
    exact (hc (.keccak ins outs i o) rfl rfl).mpr (holds_of_good (rd := rd0) (a := .keccak ins outs i o) hg trivial)
  | hint h => trivial

theorem addrs_runT {T : List (V × V)} {as : List Atom} (hok : as.all (tOk T) = true) :
    addrs (as.map Ev.atom) = [] := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    rw [List.map_cons, addrs, List.filterMap_cons]
    have : Ev.addr? (.atom a) = none := by
      cases a with
      | frameAddr p run => simp [tOk] at hok
      | _ => rfl
    rw [this]; exact ih hok.2

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **A run of atoms is a window** from its uniform hypotheses. -/
theorem segA_runT {T : List (V × V)} {k : ℕ} {f : String} {fp : ℕ} {rd0 : Reader} {w : ℕ → E} {σ0 : Val}
    {Own R : ℕ → Prop} {Pre : Reader → Prop} {as : List Atom} {a kc : ℕ} {O : Reader → Prop} {D : ℕ → Prop}
    (hok : as.all (tOk T) = true) (hg : ∀ x ∈ as, ∃ S, Good rd0 S w σ0 x)
    (h : RunHypT k σ0 w a Own R D Pre O as) :
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 (over T σ0) Own R Pre (as.map Stmt.atom)
      (as.map Ev.atom) a (a + (allocs σ0 (as.map Ev.atom)).sum) kc kc O O D D [] := by
  have hokx : ∀ x ∈ as, tOk T x = true := fun x hx => List.all_eq_true.mp hok x hx
  refine segA_atoms fun rd hl hp ho => ?_
  have hag : EvAgree σ0 (over T σ0 rd) (as.map Ev.atom) := fun e he v hv => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact over_eq (tOk_uses (hokx x hx) v hv)
  refine ⟨allocs_congr hag, ?_, by rw [addrs_runT hok]; simp, by rw [loadAddrs_congr hag]; exact h.loads,
    by rw [heapHintAddrs_congr hag]; exact h.hints, fun x hx => ?_⟩
  · rw [allocDsts_congr hag, ← h.bufs]
    refine List.map_congr_left fun v hv => ?_
    obtain ⟨x, hx, hk⟩ := mem_allocDsts hv
    obtain ⟨S, hgx⟩ := hg x hx
    rcases hk with ⟨n, rfl⟩ | ⟨s, rfl⟩ <;> exact hgx
  · obtain ⟨S, hgx⟩ := hg x hx
    exact holdsT_fact (hokx x hx) hgx (h.pure x hx) (h.mem rd hl hp ho x hx)

/-! ## One call -/

theorem callOkT_noT {T : List (V × V)} {s : Stmt} (h : callOkT T s = true) :
    ∀ v ∈ argsOf s ++ retsOf s, T.lookup v = none := by
  intro v hv
  cases s with
  | call g a r =>
    simp only [callOkT, List.all_eq_true] at h
    exact Option.isNone_iff_eq_none.mp (h v hv)
  | dispatch x gs a r =>
    simp only [callOkT, Bool.and_eq_true, List.all_eq_true] at h
    exact Option.isNone_iff_eq_none.mp (h.1 v (List.mem_cons_of_mem _ hv))
  | _ => simp [callOkT] at h

/-- **A call statement enters its callee** on every valuation reading its selector as `σ0` does. -/
theorem walk_entersT {T : List (V × V)} {σ σ0 : Val} {s : Stmt} {g : String} (hok : callOkT T s = true)
    (he : Enters σ0 g s) (hx : ∀ v, T.lookup v = none → σ v = σ0 v) :
    walk σ [s] = .fall [.call g (argsOf s) (retsOf s)] := by
  cases s with
  | call g' a r =>
    have : g' = g := he
    subst this
    exact walk_call _ _ _ _
  | dispatch x gs a r =>
    simp only [callOkT, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
    obtain ⟨j, hj, hxj, hg⟩ := he
    refine walk_dispatch (hx x (Option.isNone_iff_eq_none.mp (hok.1 x List.mem_cons_self))) ?_
    have := LeanVM.Guest.Memory.pick_eq σ0 x a r gs 0 j hj
      (by rw [Nat.zero_add]; exact le_trans hok.2 (by norm_num)) (by rw [Nat.zero_add]; exact hxj)
    rw [this, hg]
  | _ => exact (he : False).elim

/-- **A call is a window** from its callee's `CallAtA` at the aligned base of the callees' cursor. -/
theorem segA_callWT {T : List (V × V)} {k : ℕ} {f : String} {fp : ℕ} {σ0 : Val} {Own R : ℕ → Prop}
    {Pre : Reader → Prop} {s : Stmt} {g : String} {a kc : ℕ} {O : Reader → Prop} {D : ℕ → Prop}
    {Q : Reader → Tree → Prop} {Bc ec : ℕ} {Rc Dc : ℕ → Prop} {Oc : Reader → Prop}
    (hok : callOkT T s = true) (he : Enters σ0 g s) (hR : ∀ i, Rc i → (R i ∨ Own i) ∨ D i)
    (hc : CallAtA fs al cert k g ((argsOf s).map σ0) ((retsOf s).map σ0) Rc Dc Oc (fun rd => Pre rd ∧ O rd) Q Bc
      (allocBase (al g) kc) (allocBase (al g) kc + Bc) ec) :
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 (over T σ0) Own R Pre [s]
      [.call g (argsOf s) (retsOf s)] a a kc ec O (fun rd => O rd ∧ Oc rd) D (fun i => D i ∨ Dc i) [Q] := by
  have hn := callOkT_noT hok
  refine segA_call1 (fun rd _ _ _ _ => walk_entersT hok he fun v hv => over_eq hv)
    (fun rd _ _ _ _ => ⟨?_, ?_⟩) hR hc
  · exact List.map_congr_left fun v hv => (over_eq (hn v (List.mem_append_left _ hv))).symm
  · exact List.map_congr_left fun v hv => (over_eq (hn v (List.mem_append_right _ hv))).symm

end

/-! ## Composition -/

/-- A window: a run of atoms, one call statement, or one guarded call. -/
inductive W1 where
  | run (as : List Atom)
  | call (s : Stmt)
  | cif (c : V) (g : String) (args : List V)

/-- A window's statements. -/
def W1.stmts : W1 → List Stmt
  | .run as => as.map Stmt.atom
  | .call s => [s]
  | .cif c g args => [.callIf c g args]

/-- The statements of a list of windows. -/
def flatW1 (ws : List W1) : List Stmt := ws.flatMap W1.stmts

/-- The atoms of a list of windows' runs. -/
def atomsW1 (ws : List W1) : List Atom := ws.flatMap fun | .run as => as | _ => []

/-- **The windows' kernel check.** -/
def winsOkT (T : List (V × V)) (ws : List W1) : Bool :=
  ws.all fun
    | .run as => as.all (tOk T)
    | .call s => callOkT T s
    | .cif c _ args => (c :: args).all (noTB T)

theorem flatW1_cons (x : W1) (ws : List W1) : flatW1 (x :: ws) = x.stmts ++ flatW1 ws := List.flatMap_cons

theorem mem_atomsW1 {ws : List W1} {x : Atom} (h : x ∈ atomsW1 ws) : Stmt.atom x ∈ flatW1 ws := by
  simp only [atomsW1, List.mem_flatMap] at h
  obtain ⟨wd, hw, hx⟩ := h
  simp only [flatW1, List.mem_flatMap]
  refine ⟨wd, hw, ?_⟩
  cases wd with
  | run as => exact List.mem_map_of_mem hx
  | call s => simp at hx
  | cif c g args => simp at hx

/-- A call's bound on its callees' cursor step, `2^52` (a constant, so that `omega` takes multiples of it
as atoms). -/
def stepB : ℕ := 2 ^ 52

/-- The callees' cursor below which a call's step is bounded, `2^57`. -/
def stepT : ℕ := 2 ^ 57

theorem stepB_eq : stepB = 2 ^ 52 := rfl

theorem stepT_eq : stepT = 2 ^ 57 := rfl

theorem stepB_ge : 2 ^ 51 + 15 ≤ stepB := by unfold stepB; norm_num

section
variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (T : List (V × V)) (f : String)
  (fp : ℕ) (σ0 : Val) (w : ℕ → E) (Own R : ℕ → Prop) (Pre : Reader → Prop)

/-- **Statements as a window from `st`** on `over T σ0`: they walk `σ0` to `es` and are a `SegA` window
to a state `st'` satisfying `K`, its posts `st`'s and the window's, its callees' cursor within
`2^52` per call when it stays below `2^57`. -/
def SegT (ss : List Stmt) (st : St) (K : St → Prop) : Prop :=
  ∃ (es : List Ev) (st' : St) (Qs : List (Reader → Tree → Prop)), walk σ0 ss = .fall es ∧
    st'.Qs = st.Qs ++ Qs ∧
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 (over T σ0) Own R Pre ss es st.a st'.a st.kc st'.kc
      st.O st'.O st.D st'.D Qs ∧
    (st.kc + Qs.length * stepB < stepT → st'.kc ≤ st.kc + Qs.length * stepB) ∧ K st'

/-- **The windows' hypotheses**, in continuation form: each run's `RunHypT`, each call's callee
`CallAtA` at the aligned base of the callees' cursor, each guarded call's guard in `K` and, taken,
its callee's `CallAtA`, skipped, its phantom; `K` on the state after them. An entered call ends within
`2^52` of the cursor below `2^57`; a skipped one's tail frame is below `2^51`. -/
def WinsHypT : List W1 → St → (St → Prop) → Prop
  | [], st, K => K st
  | .run as :: ws, st, K => RunHypT k σ0 w st.a Own R st.D Pre st.O as ∧
      WinsHypT ws ⟨st.a + (allocs σ0 (as.map Ev.atom)).sum, st.kc, st.O, st.D, st.Qs⟩ K
  | .call s :: ws, st, K => ∃ (g : String) (Q : Reader → Tree → Prop) (Bc ec : ℕ) (Rc Dc : ℕ → Prop)
      (Oc : Reader → Prop), Enters σ0 g s ∧ (∀ i, Rc i → (R i ∨ Own i) ∨ st.D i) ∧
      CallAtA fs al cert k g ((argsOf s).map σ0) ((retsOf s).map σ0) Rc Dc Oc (fun rd => Pre rd ∧ st.O rd) Q Bc
        (allocBase (al g) st.kc) (allocBase (al g) st.kc + Bc) ec ∧ (st.kc < stepT → ec ≤ st.kc + stepB) ∧
      WinsHypT ws ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [Q]⟩ K
  | .cif c g args :: ws, st, K => IsInK (σ0 c) ∧
      (σ0 c ≠ 0 → ∃ (Q : Reader → Tree → Prop) (Bc ec : ℕ) (Rc Dc : ℕ → Prop) (Oc : Reader → Prop),
        (∀ i, Rc i → (R i ∨ Own i) ∨ st.D i) ∧
        CallAtA fs al cert k g (args.map σ0) [] Rc Dc Oc (fun rd => Pre rd ∧ st.O rd) Q Bc
          (allocBase (al g) st.kc) (allocBase (al g) st.kc + Bc) ec ∧ (st.kc < stepT → ec ≤ st.kc + stepB) ∧
        WinsHypT ws ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [Q]⟩ K) ∧
      (σ0 c = 0 → (∃ σ', Phantom coreProgram (.phantom g σ') (args.map σ0)) ∧ fs (tailKey g) < 2 ^ 51 ∧
        WinsHypT ws ⟨st.a, allocBase (al g) st.kc + fs (tailKey g), st.O, st.D, st.Qs ++ [fun _ _ => True]⟩ K)

/-- **A branch's hypotheses**: its selector in `K`, its taken arm's windows'. -/
def IteHypT (c : V) (z n : List W1) (st : St) (K : St → Prop) : Prop :=
  IsInK (σ0 c) ∧ (σ0 c = 0 → WinsHypT fs al cert k σ0 w Own R Pre z st K) ∧
    (σ0 c ≠ 0 → WinsHypT fs al cert k σ0 w Own R Pre n st K)

end

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {T : List (V × V)} {f : String} {fp : ℕ} {σ0 : Val} {w : ℕ → E} {Own R : ℕ → Prop}
  {Pre : Reader → Prop} {rd0 : Reader}

/-- **Windows' hypotheses over two lists**, the second's from where the first's end. -/
theorem winsHypT_append : ∀ (ws ws' : List W1) (st : St) (K : St → Prop),
    WinsHypT fs al cert k σ0 w Own R Pre (ws ++ ws') st K ↔
      WinsHypT fs al cert k σ0 w Own R Pre ws st fun s => WinsHypT fs al cert k σ0 w Own R Pre ws' s K
  | [], _, _, _ => Iff.rfl
  | .run as :: ws, ws', st, K => by
    rw [List.cons_append, WinsHypT, WinsHypT, winsHypT_append ws ws']
  | .call s :: ws, ws', st, K => by
    rw [List.cons_append, WinsHypT, WinsHypT]
    simp only [winsHypT_append ws ws']
  | .cif c g args :: ws, ws', st, K => by
    rw [List.cons_append, WinsHypT, WinsHypT]
    simp only [winsHypT_append ws ws']

theorem segT_nil {st : St} {K : St → Prop} (h : K st) : SegT fs al cert k T f fp σ0 Own R Pre [] st K :=
  ⟨[], st, [], rfl, by simp, segA_nil, fun _ => by simp, h⟩

theorem segT_mono {ss : List Stmt} {st : St} {K K' : St → Prop} (h : SegT fs al cert k T f fp σ0 Own R Pre ss st K)
    (hK : ∀ st, K st → K' st) : SegT fs al cert k T f fp σ0 Own R Pre ss st K' := by
  obtain ⟨es, st', Qs, hw, hq, hs, hb, hk⟩ := h
  exact ⟨es, st', Qs, hw, hq, hs, hb, hK st' hk⟩

/-- **Two windows in sequence.** -/
theorem segT_bind {ss ss' : List Stmt} {st : St} {K : St → Prop}
    (h : SegT fs al cert k T f fp σ0 Own R Pre ss st fun st1 => SegT fs al cert k T f fp σ0 Own R Pre ss' st1 K) :
    SegT fs al cert k T f fp σ0 Own R Pre (ss ++ ss') st K := by
  obtain ⟨es, st1, Qs, hw, hq, hs, hb, es', st2, Qs', hw', hq', hs', hb', hK⟩ := h
  refine ⟨es ++ es', st2, Qs ++ Qs', by rw [walk_append, hw, hw']; rfl,
    by rw [hq', hq, List.append_assoc], segA_append hs hs', fun h => ?_, hK⟩
  rw [List.length_append, Nat.add_mul] at h ⊢
  have h1 := hb (by omega)
  have h2 := hb' (by omega)
  omega

/-- **The windows compose.** -/
theorem segA_winsT : ∀ (ws : List W1) (st : St) (K : St → Prop), winsOkT T ws = true →
    (∀ x ∈ atomsW1 ws, ∃ S, Good rd0 S w σ0 x) → WinsHypT fs al cert k σ0 w Own R Pre ws st K →
    SegT fs al cert k T f fp σ0 Own R Pre (flatW1 ws) st K
  | [], st, K, _, _, h => segT_nil h
  | .run as :: ws, st, K, hok, hg, h => by
    rw [WinsHypT] at h
    simp only [winsOkT, List.all_cons, Bool.and_eq_true] at hok
    rw [flatW1_cons]
    refine segT_bind ⟨as.map Ev.atom, ⟨st.a + (allocs σ0 (as.map Ev.atom)).sum, st.kc, st.O, st.D, st.Qs⟩, [],
      walk_atomsF σ0 as, by simp, segA_runT hok.1 (fun x hx => hg x (by simp [atomsW1, hx])) h.1,
      fun _ => by simp, ?_⟩
    exact segA_winsT ws _ K hok.2 (fun x hx => hg x
      (by simp only [atomsW1, List.flatMap_cons] at hx ⊢; exact List.mem_append_right _ hx)) h.2
  | .call s :: ws, st, K, hok, hg, h => by
    rw [WinsHypT] at h
    simp only [winsOkT, List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨g, Q, Bc, ec, Rc, Dc, Oc, he, hR, hc, hb, hrest⟩ := h
    rw [flatW1_cons]
    refine segT_bind ⟨[.call g (argsOf s) (retsOf s)],
      ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [Q]⟩, [Q],
      walk_entersT hok.1 he (fun _ _ => rfl), rfl, segA_callWT hok.1 he hR hc,
      fun h => by
        simp only [List.length_singleton, Nat.one_mul] at h ⊢
        have := hb (by omega)
        omega, ?_⟩
    exact segA_winsT ws _ K hok.2 (fun x hx => hg x
      (by simp only [atomsW1, List.flatMap_cons] at hx ⊢; exact List.mem_append_right _ hx)) hrest
  | .cif c g args :: ws, st, K, hok, hg, h => by
    rw [WinsHypT] at h
    simp only [winsOkT, List.all_cons, Bool.and_eq_true] at hok
    have hn : ∀ v ∈ c :: args, T.lookup v = none := fun v hv => by
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Option.isNone_iff_eq_none.mp hok.1.1
      · exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp hok.1.2 v hv)
    have hsel : ∀ rd, over T σ0 rd c = σ0 c := fun rd => over_eq (hn c List.mem_cons_self)
    have hag : ∀ rd, args.map σ0 = args.map (over T σ0 rd) := fun rd =>
      List.map_congr_left fun v hv => (over_eq (hn v (List.mem_cons_of_mem _ hv))).symm
    have hg' : ∀ x ∈ atomsW1 ws, ∃ S, Good rd0 S w σ0 x := fun x hx => hg x
      (by simp only [atomsW1, List.flatMap_cons] at hx ⊢; exact List.mem_append_right _ hx)
    obtain ⟨hK, hT, hN⟩ := h
    rw [flatW1_cons]
    by_cases h0 : σ0 c = 0
    · obtain ⟨hph, hft, hrest⟩ := hN h0
      have hab := allocBase_le (al g) st.kc
      refine segT_bind ⟨[.inK c, .skip g args],
        ⟨st.a, allocBase (al g) st.kc + fs (tailKey g), st.O, st.D, st.Qs ++ [fun _ _ => True]⟩,
        [fun _ _ => True], by rw [W1.stmts, walk_callIf]; simp [h0], rfl,
        segA_callIfN (fun rd _ _ _ => hsel rd) h0 (fun rd _ _ _ => hag rd) hph, fun _ => by
          have := stepB_ge
          simp only [List.length_singleton, Nat.one_mul]
          omega, ?_⟩
      exact segA_winsT ws _ K hok.2 hg' hrest
    · obtain ⟨Q, Bc, ec, Rc, Dc, Oc, hR, hc, hb, hrest⟩ := hT h0
      refine segT_bind ⟨[.inK c, .call g args []],
        ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [Q]⟩, [Q],
        by rw [W1.stmts, walk_callIf]; simp [h0], rfl,
        segA_callIfT (fun rd _ _ _ _ => hsel rd) h0 hK (fun rd _ _ _ _ => hag rd) hR hc,
        fun h => by
        simp only [List.length_singleton, Nat.one_mul] at h ⊢
        have := hb (by omega)
        omega, ?_⟩
      exact segA_winsT ws _ K hok.2 hg' hrest

/-- **A branch is a window** from its taken arm's windows. -/
theorem seg_iteT {c : V} {z n : List W1} {st : St} {K : St → Prop} (hc : T.lookup c = none)
    (hz : σ0 c = 0 → winsOkT T z = true ∧ ∀ x ∈ atomsW1 z, ∃ S, Good rd0 S w σ0 x)
    (hn : σ0 c ≠ 0 → winsOkT T n = true ∧ ∀ x ∈ atomsW1 n, ∃ S, Good rd0 S w σ0 x)
    (h : IteHypT fs al cert k σ0 w Own R Pre c z n st K) :
    SegT fs al cert k T f fp σ0 Own R Pre [.ite c (flatW1 z) (flatW1 n)] st K := by
  obtain ⟨hK, h0, h1⟩ := h
  have hs : SegT fs al cert k T f fp σ0 Own R Pre (if σ0 c = 0 then flatW1 z else flatW1 n) st K := by
    by_cases h' : σ0 c = 0
    · rw [ite_pos' h']; exact segA_winsT z st K (hz h').1 (hz h').2 (h0 h')
    · rw [ite_neg' h']; exact segA_winsT n st K (hn h').1 (hn h').2 (h1 h')
  obtain ⟨es, st', Qs, hw, hq, hseg, hb, hk⟩ := hs
  refine ⟨.inK c :: es, st', Qs, ?_, hq, segA_ite (fun rd _ _ _ => over_eq hc) hK hseg, hb, hk⟩
  rw [walk, walk1, show walk σ0 [] = .fall [] from rfl]
  by_cases h' : σ0 c = 0
  · rw [ite_pos' h'] at hw ⊢; rw [hw]; simp [Out.seq, Out.pre]
  · rw [ite_neg' h'] at hw ⊢; rw [hw]; simp [Out.seq, Out.pre]

end

end
end LeanVM.Guest.Complete
