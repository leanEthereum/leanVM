/-
  LeanVM.Guest.B1.VsC.WinGen

  A long body's windows, generically: a run of atoms from uniform hypotheses on the honest
  valuation and every memory, a call from its callee's placed statement, their composition.
-/

module

public import LeanVM.Guest.B1.VsC.VsRun
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.B1.VsC.LeafEnd

/-!
# Windows, generically

On the forward valuation `σ0` and its per-memory form `rdOver σ0` (`VsW0.lean`):

* **Runs.** `segA_run`: a run of atoms `as` passing the kernel check `overOk` (no range check's
  temporary named outside its range check, no `frameAddr` or `touch`, a branch `assertNe`'s product
  after its operands) whose atoms satisfy their equations on `σ0` (`Good` of `fixA`) is a window
  from its uniform hypotheses `RunHyp k σ0 w a Own R D Pre O as`: its `HeapBuf` pointers the
  allocator's bases from `a` (`bufs`), its loads and heap hints in `Own`, `R` or `D` (`loads`,
  `hints`), its pure side conditions on `σ0` (`pure`: `PureF`, a divisor nonzero, an assertion, a
  range check's operands `g^m` with `m < 2^k`), and on every memory with `LowDef k`, `Pre` and `O`
  its loads' and stores' words (`mem`: `MemF`).
* **Calls.** `segA_callW`: a `call`, or a `dispatch` whose selector picks the callee on `σ0`
  (`Enters`), passing `callOk`, is a window from the callee's `CallAtA` at the aligned base of the
  callees' cursor.
* **Composition.** `W0` is a window (`run as` or `call s`), `flatW` a list's statements. `WinsHyp
  ws st K` is the windows' hypotheses in continuation form over the state `St` (the `HeapBuf`
  cursor, the callees' cursor, the words held, the data claimed, the callees' posts so far), `K`
  the condition on the state after them. `segA_wins`: `WinsHyp ws st K` gives `Seg (flatW ws) st
  K`: the statements walk `σ0` to some events and are a `SegA` window from `st` to a state
  satisfying `K`. `seg_bind` sequences two `Seg`s, `seg_ite` closes a branch from its taken arm's
  windows (`IteHyp`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The kernel checks -/

/-- `v` is no range check's temporary in `rc`. -/
def noRcB (rc : List (V × V)) (v : V) : Bool := (rc.lookup v).isNone

/-- **An atom a run window takes**: its values no range check's temporary (a range check's own
temporaries the pairs `rc` names), no `frameAddr` or `touch`, a branch `assertNe`'s product after
its operands. -/
def overOk (rc : List (V × V)) (a : Atom) : Bool :=
  (atomUses a).all (noRcB rc) &&
    match a with
    | .rangeCheck x y t1 t2 _ => decide (rc.lookup t1 = some x) && decide (rc.lookup t2 = some y)
    | .assertNe x i p => decide (x.idx < p.idx) && decide (i.idx < p.idx)
    | .frameAddr .. | .touch .. => false
    | _ => true

/-- A call's arguments. -/
def argsOf : Stmt → List V
  | .call _ a _ => a
  | .dispatch _ _ a _ => a
  | _ => []

/-- A call's returns. -/
def retsOf : Stmt → List V
  | .call _ _ r => r
  | .dispatch _ _ _ r => r
  | _ => []

/-- **A statement a call window takes**: a `call` or a `dispatch` (of at most `64` callees), its
values no range check's temporary. -/
def callOk (rc : List (V × V)) : Stmt → Bool
  | .call _ a r => (a ++ r).all (noRcB rc)
  | .dispatch x gs a r => (x :: (a ++ r)).all (noRcB rc) && decide (gs.length ≤ 64)
  | _ => false

/-- The statement enters `g` on `σ0`: a `call` of `g`, or a `dispatch` whose selector is `g^j` with
`g` its callee `j`. -/
def Enters (σ0 : Val) (g : String) : Stmt → Prop
  | .call g' _ _ => g' = g
  | .dispatch x gs _ _ => ∃ j, j < gs.length ∧ σ0 x = ofK (addressOfIndex j) ∧ gs[j]! = g
  | _ => False

/-! ## What a run asks -/

/-- `e = g^m` for some `m < 2^k`: its cell is among a `LowDef k` memory's. -/
def LowW (k : ℕ) (e : E) : Prop := ∃ m, m < 2 ^ k ∧ e = gen ^ m

/-- **What an atom asks of the valuation** beyond its equations: a divisor nonzero, an assertion,
a range check's operands low. -/
def PureF (k : ℕ) (σ : Val) : Atom → Prop
  | .mul d x y => if x.idx < d.idx ∧ y.idx < d.idx then True else σ y ≠ 0
  | .assertEq x y => σ x + σ y = 0
  | .assertInK x y => IsInK (σ x) ∧ IsInK (σ y)
  | .assertNe x i _ => σ x * σ i = 1
  | .rangeCheck x y _ _ _ => LowW k (σ x) ∧ LowW k (σ y)
  | _ => True

/-- **What an atom asks of a memory**: a load's (or store's) word. -/
def MemF (rd : Reader) (σ : Val) : Atom → Prop
  | .load d p off => LoadHolds rd (σ p) off (σ d)
  | _ => True

/-- **A run's hypotheses**, uniform: its `HeapBuf` pointers (the oracle's words) the bases from
`a`, its loads and heap hints in `Own`, `R` or `D`, its pure side conditions on `σ0`, and on every
memory with `LowDef k`, `Pre` and `O` its loads' words. -/
structure RunHyp (k : ℕ) (σ0 : Val) (w : ℕ → E) (a : ℕ) (Own R D : ℕ → Prop) (Pre O : Reader → Prop)
    (as : List Atom) : Prop where
  bufs : (allocDsts (as.map Ev.atom)).map (fun v => w v.idx) =
    (bases a (allocs σ0 (as.map Ev.atom))).map (fun b => ofK (addressOfIndex b))
  loads : ∀ A ∈ loadAddrs σ0 (as.map Ev.atom), ∃ i, A = addressOfIndex i ∧ (Own i ∨ R i ∨ D i)
  hints : ∀ A ∈ heapHintAddrs σ0 (as.map Ev.atom), ∃ i, A = addressOfIndex i ∧ (Own i ∨ R i ∨ D i)
  pure : ∀ x ∈ as, PureF k σ0 x
  mem : ∀ rd, LowDef k rd → Pre rd → O rd → ∀ x ∈ as, MemF rd σ0 x

/-- An atom whose `PureF` asks something of the valuation: a division, an assertion, a range check. -/
def pureAsks : Atom → Bool
  | .mul d x y => !(decide (x.idx < d.idx) && decide (y.idx < d.idx))
  | .assertEq .. => true
  | .assertInK .. => true
  | .assertNe .. => true
  | .rangeCheck .. => true
  | _ => false

/-- An atom whose `MemF` asks something of a memory: a load. -/
def memAsks : Atom → Bool
  | .load .. => true
  | _ => false

theorem pureF_of_asks {k : ℕ} {σ : Val} {a : Atom} (h : pureAsks a = false) : PureF k σ a := by
  cases a <;> simp_all [pureAsks, PureF]

theorem memF_of_asks {rd : Reader} {σ : Val} {a : Atom} (h : memAsks a = false) : MemF rd σ a := by
  cases a <;> simp_all [memAsks, MemF]

/-- **A run's hypotheses from its asking atoms only**: the pure side conditions of its divisions,
assertions and range checks (`pureAsks`), the words of its loads (`memAsks`). -/
theorem RunHyp.of_asks {k : ℕ} {σ0 : Val} {w : ℕ → E} {a : ℕ} {Own R D : ℕ → Prop} {Pre O : Reader → Prop}
    {as : List Atom}
    (bufs : (allocDsts (as.map Ev.atom)).map (fun v => w v.idx) =
      (bases a (allocs σ0 (as.map Ev.atom))).map (fun b => ofK (addressOfIndex b)))
    (loads : ∀ A ∈ loadAddrs σ0 (as.map Ev.atom), ∃ i, A = addressOfIndex i ∧ (Own i ∨ R i ∨ D i))
    (hints : ∀ A ∈ heapHintAddrs σ0 (as.map Ev.atom), ∃ i, A = addressOfIndex i ∧ (Own i ∨ R i ∨ D i))
    (pure : ∀ x ∈ as.filter pureAsks, PureF k σ0 x)
    (mem : ∀ rd, LowDef k rd → Pre rd → O rd → ∀ x ∈ as.filter memAsks, MemF rd σ0 x) :
    RunHyp k σ0 w a Own R D Pre O as := by
  refine ⟨bufs, loads, hints, fun x hx => ?_, fun rd hl hp ho x hx => ?_⟩
  · cases h : pureAsks x
    · exact pureF_of_asks h
    · exact pure x (List.mem_filter.mpr ⟨hx, h⟩)
  · cases h : memAsks x
    · exact memF_of_asks h
    · exact mem rd hl hp ho x (List.mem_filter.mpr ⟨hx, h⟩)

/-! ## One atom, one run -/

theorem overOk_uses {a : Atom} (h : overOk vsRcs a = true) : ∀ v ∈ atomUses a, vsRcs.lookup v = none := by
  intro v hv
  simp only [overOk, Bool.and_eq_true, List.all_eq_true] at h
  exact Option.isNone_iff_eq_none.mp (h.1 v hv)

/-- `fixA` keeps an atom's equations. -/
theorem good_fixA {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {a : Atom} (hok : overOk vsRcs a = true)
    (h : Good rd S w σ a) : Good rd S w σ (fixA a) := by
  cases a with
  | assertNe x i p =>
    simp only [overOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    show if x.idx < p.idx ∧ i.idx < p.idx then σ p = σ x * σ i else σ x = σ p * (σ i)⁻¹
    rw [ite_pos' hok.2]; exact h.2
  | _ => exact h

theorem lowW_isInK {k : ℕ} {e : E} (h : LowW k e) : IsInK e := by
  obtain ⟨m, -, rfl⟩ := h
  rw [Value.gen_pow_eq_ofK]; exact Value.ofK_isInK _

theorem lowW_def {k : ℕ} {rd : Reader} {e : E} (h : LowW k e) (hl : LowDef k rd) :
    (rd (e.limb 0 * addressOfIndex 0)).isSome := by
  obtain ⟨m, hm, rfl⟩ := h
  have e' : (gen ^ m).limb 0 * addressOfIndex 0 = addressOfIndex m := by
    rw [Value.gen_pow_eq_ofK]; simp
  rw [e']; exact hl m hm

theorem lowW_ne {k : ℕ} {e : E} (h : LowW k e) : e ≠ 0 := by
  obtain ⟨m, -, rfl⟩ := h
  exact pow_ne_zero _ Value.gen_ne_zero

/-- **An atom of a run holds on every memory's valuation** from its equations on `σ0`, its pure
side condition and its memory word. -/
theorem holds_fact {k : ℕ} {rd0 rd : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val} {a : Atom}
    (hok : overOk vsRcs a = true) (hg : Good rd0 S w σ0 (fixA a)) (hp : PureF k σ0 a) (hm : MemF rd σ0 a)
    (hl : LowDef k rd) : a.Holds rd (rdOver σ0 rd) := by
  have hu := overOk_uses hok
  have hc : ∀ (b : Atom), atomTmps b = [] → atomUses b = atomUses a →
      (b.Holds rd (rdOver σ0 rd) ↔ b.Holds rd σ0) := fun b ht hb =>
    atom_holds_congr b fun v hv => by
      rw [ht, List.append_nil, hb] at hv; exact rdOver_eq (hu v hv)
  cases a with
  | rangeCheck x y t1 t2 kk =>
    simp only [overOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hx, hy⟩ := hp
    exact holds_rc hok.2.1 hok.2.2 (hu x (by simp [atomUses])) (hu y (by simp [atomUses]))
      (hu kk (by simp [atomUses])) hg (lowW_isInK hx) (lowW_isInK hy) (lowW_def hx hl) (lowW_def hy hl)
      (fun _ => lowW_ne hx)
  | frameAddr p run => simp [overOk] at hok
  | touch t p => simp [overOk] at hok
  | const d e => exact (hc (.const d e) rfl rfl).mpr hg
  | add d x y => exact (hc (.add d x y) rfl rfl).mpr hg
  | copy d s => exact (hc (.copy d s) rfl rfl).mpr hg
  | mul d x y => exact (hc (.mul d x y) rfl rfl).mpr (holds_of_good (rd := rd0) (a := .mul d x y) hg hp)
  | load d p off => exact (hc (.load d p off) rfl rfl).mpr hm
  | assertEq x y => exact (hc (.assertEq x y) rfl rfl).mpr hp
  | assertInK x y => exact (hc (.assertInK x y) rfl rfl).mpr hp
  | assertNe x i p =>
    simp only [overOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    refine (hc (.assertNe x i p) rfl rfl).mpr ?_
    have hg' : σ0 p = σ0 x * σ0 i := by
      have := hg; simp only [fixA, Good] at this; rwa [ite_pos' hok.2] at this
    exact ⟨hg', hg'.trans hp⟩
  | keccak ins outs i o =>
    exact (hc (.keccak ins outs i o) rfl rfl).mpr (holds_of_good (rd := rd0) (a := .keccak ins outs i o) hg trivial)
  | hint h => trivial

theorem addrs_run {as : List Atom} (hok : as.all (overOk vsRcs) = true) : addrs (as.map Ev.atom) = [] := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    rw [List.map_cons, addrs, List.filterMap_cons]
    have : Ev.addr? (.atom a) = none := by
      cases a with
      | frameAddr p run => simp [overOk] at hok
      | _ => rfl
    rw [this]; exact ih hok.2

/-- **A run of atoms is a window** from its uniform hypotheses. -/
theorem segA_run {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {fp : ℕ} {rd0 : Reader} {w : ℕ → E} {σ0 : Val} {Own R : ℕ → Prop} {Pre : Reader → Prop} {as : List Atom}
    {a kc : ℕ} {O : Reader → Prop} {D : ℕ → Prop} (hok : as.all (overOk vsRcs) = true)
    (hg : ∀ x ∈ as, ∃ S, Good rd0 S w σ0 (fixA x)) (h : RunHyp k σ0 w a Own R D Pre O as) :
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 (rdOver σ0) Own R Pre (as.map Stmt.atom) (as.map Ev.atom)
      a (a + (allocs σ0 (as.map Ev.atom)).sum) kc kc O O D D [] := by
  have hokx : ∀ x ∈ as, overOk vsRcs x = true := fun x hx => List.all_eq_true.mp hok x hx
  refine segA_atoms fun rd hl hp ho => ?_
  have hag : EvAgree σ0 (rdOver σ0 rd) (as.map Ev.atom) := fun e he v hv => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact rdOver_eq (overOk_uses (hokx x hx) v hv)
  refine ⟨allocs_congr hag, ?_, by rw [addrs_run hok]; simp, by rw [loadAddrs_congr hag]; exact h.loads,
    by rw [heapHintAddrs_congr hag]; exact h.hints, fun x hx => ?_⟩
  · rw [allocDsts_congr hag, ← h.bufs]
    refine List.map_congr_left fun v hv => ?_
    obtain ⟨x, hx, hk⟩ := mem_allocDsts hv
    obtain ⟨S, hgx⟩ := hg x hx
    rcases hk with ⟨n, rfl⟩ | ⟨s, rfl⟩ <;> exact hgx
  · obtain ⟨S, hgx⟩ := hg x hx
    exact holds_fact (hokx x hx) hgx (h.pure x hx) (h.mem rd hl hp ho x hx) hl

/-! ## One call -/

theorem callOk_noRc {s : Stmt} (h : callOk vsRcs s = true) :
    ∀ v ∈ argsOf s ++ retsOf s, vsRcs.lookup v = none := by
  intro v hv
  cases s with
  | call g a r =>
    simp only [callOk, List.all_eq_true] at h
    exact Option.isNone_iff_eq_none.mp (h v hv)
  | dispatch x gs a r =>
    simp only [callOk, Bool.and_eq_true, List.all_eq_true] at h
    exact Option.isNone_iff_eq_none.mp (h.1 v (List.mem_cons_of_mem _ hv))
  | _ => simp [callOk] at h

/-- **A call statement enters its callee** on every valuation reading its selector as `σ0` does. -/
theorem walk_enters {σ σ0 : Val} {s : Stmt} {g : String} (hok : callOk vsRcs s = true) (he : Enters σ0 g s)
    (hx : ∀ v, vsRcs.lookup v = none → σ v = σ0 v) : walk σ [s] = .fall [.call g (argsOf s) (retsOf s)] := by
  cases s with
  | call g' a r =>
    have : g' = g := he
    subst this
    exact walk_call _ _ _ _
  | dispatch x gs a r =>
    simp only [callOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
    obtain ⟨j, hj, hxj, hg⟩ := he
    refine walk_dispatch (hx x (Option.isNone_iff_eq_none.mp (hok.1 x List.mem_cons_self))) ?_
    have := LeanVM.Guest.Memory.pick_eq σ0 x a r gs 0 j hj
      (by rw [Nat.zero_add]; exact le_trans hok.2 (by norm_num)) (by rw [Nat.zero_add]; exact hxj)
    rw [this, hg]
  | _ => exact (he : False).elim

/-- **A call is a window** from its callee's `CallAtA` at the aligned base of the callees' cursor. -/
theorem segA_callW {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {fp : ℕ} {σ0 : Val} {Own R : ℕ → Prop} {Pre : Reader → Prop} {s : Stmt} {g : String} {a kc : ℕ}
    {O : Reader → Prop} {D : ℕ → Prop} {Q : Reader → Tree → Prop} {Bc ec : ℕ} {Rc Dc : ℕ → Prop}
    {Oc : Reader → Prop} (hok : callOk vsRcs s = true) (he : Enters σ0 g s)
    (hR : ∀ i, Rc i → (R i ∨ Own i) ∨ D i)
    (hc : CallAtA fs al cert k g ((argsOf s).map σ0) ((retsOf s).map σ0) Rc Dc Oc (fun rd => Pre rd ∧ O rd) Q Bc
      (allocBase (al g) kc) (allocBase (al g) kc + Bc) ec) :
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 (rdOver σ0) Own R Pre [s] [.call g (argsOf s) (retsOf s)]
      a a kc ec O (fun rd => O rd ∧ Oc rd) D (fun i => D i ∨ Dc i) [Q] := by
  have hn := callOk_noRc hok
  refine segA_call1 (fun rd _ _ _ _ => walk_enters hok he fun v hv => rdOver_eq hv)
    (fun rd _ _ _ _ => ⟨?_, ?_⟩) hR hc
  · exact List.map_congr_left fun v hv => (rdOver_eq (hn v (List.mem_append_left _ hv))).symm
  · exact List.map_congr_left fun v hv => (rdOver_eq (hn v (List.mem_append_right _ hv))).symm

/-- **A callee's aligned statement at the callees' cursor**: from `CallCompletesA`, at the aligned base
of `kc`, under a precondition the window's implies. -/
theorem callAt_of_completesA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
    {g : String} {args rets : List E} {Rg : ℕ → Prop} {Dg : ℕ → ℕ → ℕ → Prop} {Out Preg P : Reader → Prop}
    {Post : Reader → Tree → Prop} (h : CallCompletesA fs al cert k g args rets Rg Dg Out Preg Post)
    (hP : ∀ rd, P rd → Preg rd) (kc : ℕ) :
    ∃ Bc ec, CallAtA fs al cert k g args rets Rg (Dg (allocBase (al g) kc) (allocBase (al g) kc + Bc)) Out P Post Bc
      (allocBase (al g) kc) (allocBase (al g) kc + Bc) ec := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨e, he⟩ := hB (allocBase (al g) kc) (allocBase (al g) kc + B) le_rfl
  exact ⟨B, e, he.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) hP (fun _ _ _ h => h)⟩

/-! ## Composition -/

/-- A window: a run of atoms, or one call statement. -/
inductive W0 where
  | run (as : List Atom)
  | call (s : Stmt)

/-- A window's statements. -/
def W0.stmts : W0 → List Stmt
  | .run as => as.map Stmt.atom
  | .call s => [s]

/-- The statements of a list of windows. -/
def flatW (ws : List W0) : List Stmt := ws.flatMap W0.stmts

/-- The atoms of a list of windows' runs. -/
def atomsW (ws : List W0) : List Atom := ws.flatMap fun | .run as => as | .call _ => []

/-- **The windows' kernel check.** -/
def winsOk (rc : List (V × V)) (ws : List W0) : Bool :=
  ws.all fun | .run as => as.all (overOk rc) | .call s => callOk rc s

theorem flatW_nil : flatW [] = [] := rfl

theorem flatW_cons (x : W0) (ws : List W0) : flatW (x :: ws) = x.stmts ++ flatW ws := List.flatMap_cons

theorem mem_atomsW {ws : List W0} {x : Atom} (h : x ∈ atomsW ws) : Stmt.atom x ∈ flatW ws := by
  simp only [atomsW, List.mem_flatMap] at h
  obtain ⟨wd, hw, hx⟩ := h
  simp only [flatW, List.mem_flatMap]
  refine ⟨wd, hw, ?_⟩
  cases wd with
  | run as => exact List.mem_map_of_mem hx
  | call s => simp at hx

/-- **The state between windows**: the `HeapBuf` cursor, the callees' cursor, the words held, the
data claimed, the callees' posts so far. -/
structure St where
  a : ℕ
  kc : ℕ
  O : Reader → Prop
  D : ℕ → Prop
  Qs : List (Reader → Tree → Prop)

section
variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (f : String) (fp : ℕ)
  (σ0 : Val) (w : ℕ → E) (Own R : ℕ → Prop) (Pre : Reader → Prop)

/-- **Statements as a window from `st`**: they walk `σ0` to `es` and are a `SegA` window to a state
`st'` satisfying `K`, its posts `st`'s and the window's. -/
def Seg (ss : List Stmt) (st : St) (K : St → Prop) : Prop :=
  ∃ (es : List Ev) (st' : St) (Qs : List (Reader → Tree → Prop)), walk σ0 ss = .fall es ∧
    st'.Qs = st.Qs ++ Qs ∧
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 (rdOver σ0) Own R Pre ss es st.a st'.a st.kc st'.kc
      st.O st'.O st.D st'.D Qs ∧ K st'

/-- **The windows' hypotheses**, in continuation form: each run's `RunHyp`, each call's callee
`CallAtA` at the aligned base of the callees' cursor, `K` on the state after them. -/
def WinsHyp : List W0 → St → (St → Prop) → Prop
  | [], st, K => K st
  | .run as :: ws, st, K => RunHyp k σ0 w st.a Own R st.D Pre st.O as ∧
      WinsHyp ws ⟨st.a + (allocs σ0 (as.map Ev.atom)).sum, st.kc, st.O, st.D, st.Qs⟩ K
  | .call s :: ws, st, K => ∃ (g : String) (Q : Reader → Tree → Prop) (Bc ec : ℕ) (Rc Dc : ℕ → Prop)
      (Oc : Reader → Prop), Enters σ0 g s ∧ (∀ i, Rc i → (R i ∨ Own i) ∨ st.D i) ∧
      CallAtA fs al cert k g ((argsOf s).map σ0) ((retsOf s).map σ0) Rc Dc Oc (fun rd => Pre rd ∧ st.O rd) Q Bc
        (allocBase (al g) st.kc) (allocBase (al g) st.kc + Bc) ec ∧
      WinsHyp ws ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [Q]⟩ K

/-- **A branch's hypotheses**: its selector in `K`, its taken arm's windows'. -/
def IteHyp (c : V) (z n : List W0) (st : St) (K : St → Prop) : Prop :=
  IsInK (σ0 c) ∧ (σ0 c = 0 → WinsHyp fs al cert k σ0 w Own R Pre z st K) ∧
    (σ0 c ≠ 0 → WinsHyp fs al cert k σ0 w Own R Pre n st K)

end

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {f : String} {fp : ℕ}
  {σ0 : Val} {w : ℕ → E} {Own R : ℕ → Prop} {Pre : Reader → Prop} {rd0 : Reader}

/-- **Windows' hypotheses over two lists**, the second's from where the first's end. -/
theorem winsHyp_append : ∀ (ws ws' : List W0) (st : St) (K : St → Prop),
    WinsHyp fs al cert k σ0 w Own R Pre (ws ++ ws') st K ↔
      WinsHyp fs al cert k σ0 w Own R Pre ws st fun s => WinsHyp fs al cert k σ0 w Own R Pre ws' s K
  | [], _, _, _ => Iff.rfl
  | .run as :: ws, ws', st, K => by
    rw [List.cons_append, WinsHyp, WinsHyp, winsHyp_append ws ws']
  | .call s :: ws, ws', st, K => by
    rw [List.cons_append, WinsHyp, WinsHyp]
    simp only [winsHyp_append ws ws']

/-- **A call window's hypotheses from its callee's `CallCompletesA`**: the callee entered on `σ0`, its
region in the window's, its precondition from the window's, the rest from its end. -/
theorem winsHyp_call_of_completesA {s : Stmt} {g : String} {ws : List W0} {st : St} {K : St → Prop}
    {Rg : ℕ → Prop} {Dg : ℕ → ℕ → ℕ → Prop} {Out Preg : Reader → Prop} {Post : Reader → Tree → Prop}
    (he : Enters σ0 g s)
    (h : CallCompletesA fs al cert k g ((argsOf s).map σ0) ((retsOf s).map σ0) Rg Dg Out Preg Post)
    (hR : ∀ i, Rg i → (R i ∨ Own i) ∨ st.D i) (hP : ∀ rd, Pre rd ∧ st.O rd → Preg rd)
    (hrest : ∀ Bc ec, WinsHyp fs al cert k σ0 w Own R Pre ws
      ⟨st.a, ec, fun rd => st.O rd ∧ Out rd,
        fun i => st.D i ∨ Dg (allocBase (al g) st.kc) (allocBase (al g) st.kc + Bc) i, st.Qs ++ [Post]⟩ K) :
    WinsHyp fs al cert k σ0 w Own R Pre (.call s :: ws) st K := by
  obtain ⟨Bc, ec, hc⟩ := callAt_of_completesA h hP st.kc
  rw [WinsHyp]
  exact ⟨g, Post, Bc, ec, Rg, _, Out, he, hR, hc, hrest Bc ec⟩

/-- A leaf callee's end: its frame at the aligned base of the callees' cursor, its end past it. -/
abbrev leafEnd (fs : String → ℕ) (al : String → Bool) (g : String) (kc : ℕ) : ℕ := allocBase (al g) kc + fs g

/-- **A call window's hypotheses from its callee's `CallAtA` at a given end** (`WinsHyp`'s call case), its
precondition from the window's. -/
theorem winsHyp_call_at {s : Stmt} {g : String} {ws : List W0} {st : St} {K : St → Prop}
    {Rg Dg : ℕ → Prop} {Out Preg : Reader → Prop} {Post : Reader → Tree → Prop} {Bc ec : ℕ}
    (he : Enters σ0 g s)
    (h : CallAtA fs al cert k g ((argsOf s).map σ0) ((retsOf s).map σ0) Rg Dg Out Preg Post Bc
      (allocBase (al g) st.kc) (allocBase (al g) st.kc + Bc) ec)
    (hR : ∀ i, Rg i → (R i ∨ Own i) ∨ st.D i) (hP : ∀ rd, Pre rd ∧ st.O rd → Preg rd)
    (hrest : WinsHyp fs al cert k σ0 w Own R Pre ws
      ⟨st.a, ec, fun rd => st.O rd ∧ Out rd, fun i => st.D i ∨ Dg i, st.Qs ++ [Post]⟩ K) :
    WinsHyp fs al cert k σ0 w Own R Pre (.call s :: ws) st K := by
  rw [WinsHyp]
  exact ⟨g, Post, Bc, ec, Rg, Dg, Out, he, hR,
    h.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) hP (fun _ _ _ h => h), hrest⟩

/-- **A leaf's call window's hypotheses**: the callee ends at its cursor, past its frame. -/
theorem winsHyp_call_leaf {s : Stmt} {g : String} {ws : List W0} {st : St} {K : St → Prop}
    {Rg : ℕ → Prop} {Out Preg : Reader → Prop} {Post : Reader → Tree → Prop} (he : Enters σ0 g s)
    (h : LeafAtA fs al cert k g ((argsOf s).map σ0) ((retsOf s).map σ0) Rg Out Preg Post)
    (hR : ∀ i, Rg i → (R i ∨ Own i) ∨ st.D i) (hP : ∀ rd, Pre rd ∧ st.O rd → Preg rd)
    (hrest : WinsHyp fs al cert k σ0 w Own R Pre ws
      ⟨st.a, leafEnd fs al g st.kc, fun rd => st.O rd ∧ Out rd, fun i => st.D i ∨ False, st.Qs ++ [Post]⟩ K) :
    WinsHyp fs al cert k σ0 w Own R Pre (.call s :: ws) st K :=
  winsHyp_call_at he (h _ _ le_rfl) hR hP hrest

theorem seg_nil {st : St} {K : St → Prop} (h : K st) : Seg fs al cert k f fp σ0 Own R Pre [] st K :=
  ⟨[], st, [], rfl, by simp, segA_nil, h⟩

theorem seg_mono {ss : List Stmt} {st : St} {K K' : St → Prop} (h : Seg fs al cert k f fp σ0 Own R Pre ss st K)
    (hK : ∀ st, K st → K' st) : Seg fs al cert k f fp σ0 Own R Pre ss st K' := by
  obtain ⟨es, st', Qs, hw, hq, hs, hk⟩ := h
  exact ⟨es, st', Qs, hw, hq, hs, hK st' hk⟩

/-- **Two windows in sequence.** -/
theorem seg_bind {ss ss' : List Stmt} {st : St} {K : St → Prop}
    (h : Seg fs al cert k f fp σ0 Own R Pre ss st fun st1 => Seg fs al cert k f fp σ0 Own R Pre ss' st1 K) :
    Seg fs al cert k f fp σ0 Own R Pre (ss ++ ss') st K := by
  obtain ⟨es, st1, Qs, hw, hq, hs, es', st2, Qs', hw', hq', hs', hK⟩ := h
  refine ⟨es ++ es', st2, Qs ++ Qs', by rw [walk_append, hw, hw']; rfl,
    by rw [hq', hq, List.append_assoc], segA_append hs hs', hK⟩

/-- **The windows compose.** -/
theorem segA_wins : ∀ (ws : List W0) (st : St) (K : St → Prop), winsOk vsRcs ws = true →
    (∀ x ∈ atomsW ws, ∃ S, Good rd0 S w σ0 (fixA x)) → WinsHyp fs al cert k σ0 w Own R Pre ws st K →
    Seg fs al cert k f fp σ0 Own R Pre (flatW ws) st K
  | [], st, K, _, _, h => seg_nil h
  | .run as :: ws, st, K, hok, hg, h => by
    rw [WinsHyp] at h
    simp only [winsOk, List.all_cons, Bool.and_eq_true] at hok
    rw [flatW_cons]
    refine seg_bind ⟨as.map Ev.atom, ⟨st.a + (allocs σ0 (as.map Ev.atom)).sum, st.kc, st.O, st.D, st.Qs⟩, [],
      walk_atomsF σ0 as, by simp, segA_run hok.1 (fun x hx => hg x (by simp [atomsW, hx])) h.1, ?_⟩
    exact segA_wins ws _ K hok.2 (fun x hx => hg x
      (by simp only [atomsW, List.flatMap_cons] at hx ⊢; exact List.mem_append_right _ hx)) h.2
  | .call s :: ws, st, K, hok, hg, h => by
    rw [WinsHyp] at h
    simp only [winsOk, List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨g, Q, Bc, ec, Rc, Dc, Oc, he, hR, hc, hrest⟩ := h
    rw [flatW_cons]
    refine seg_bind ⟨[.call g (argsOf s) (retsOf s)],
      ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [Q]⟩, [Q],
      walk_enters hok.1 he (fun _ _ => rfl), rfl, segA_callW hok.1 he hR hc, ?_⟩
    exact segA_wins ws _ K hok.2 (fun x hx => hg x
      (by simp only [atomsW, List.flatMap_cons] at hx ⊢; exact List.mem_append_right _ hx)) hrest

/-- **A branch is a window** from its taken arm's windows. -/
theorem seg_ite {c : V} {z n : List W0} {st : St} {K : St → Prop} (hc : vsRcs.lookup c = none)
    (hz : σ0 c = 0 → winsOk vsRcs z = true ∧ ∀ x ∈ atomsW z, ∃ S, Good rd0 S w σ0 (fixA x))
    (hn : σ0 c ≠ 0 → winsOk vsRcs n = true ∧ ∀ x ∈ atomsW n, ∃ S, Good rd0 S w σ0 (fixA x))
    (h : IteHyp fs al cert k σ0 w Own R Pre c z n st K) :
    Seg fs al cert k f fp σ0 Own R Pre [.ite c (flatW z) (flatW n)] st K := by
  obtain ⟨hK, h0, h1⟩ := h
  have hs : Seg fs al cert k f fp σ0 Own R Pre (if σ0 c = 0 then flatW z else flatW n) st K := by
    by_cases h' : σ0 c = 0
    · rw [ite_pos' h']; exact segA_wins z st K (hz h').1 (hz h').2 (h0 h')
    · rw [ite_neg' h']; exact segA_wins n st K (hn h').1 (hn h').2 (h1 h')
  obtain ⟨es, st', Qs, hw, hq, hseg, hk⟩ := hs
  refine ⟨.inK c :: es, st', Qs, ?_, hq, segA_ite (fun rd _ _ _ => rdOver_eq hc) hK hseg, hk⟩
  rw [walk, walk1, show walk σ0 [] = .fall [] from rfl]
  by_cases h' : σ0 c = 0
  · rw [ite_pos' h'] at hw ⊢; rw [hw]; simp [Out.seq, Out.pre]
  · rw [ite_neg' h'] at hw ⊢; rw [hw]; simp [Out.seq, Out.pre]

end


end
end LeanVM.Guest.B1.VsC
