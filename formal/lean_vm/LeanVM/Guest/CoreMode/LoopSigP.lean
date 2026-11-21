/-
  LeanVM.Guest.CoreMode.LoopSigP

  A loop helper's mode signature with pointer runs as a heap signature, and pointer runs read through
  any reader that agrees with a memory.
-/

module

public import LeanVM.Guest.CoreMode.LoopSig
public import LeanVM.Guest.CoreMode.CorePtr
public import LeanVM.Guest.CoreMode.LoopLink

/-!
# A loop helper's signature with pointer runs

`sigOkLP`: a loop helper's heap signature its mode signature's translation (`SigL`), with the loop's pointer runs, its preconditions `preP` and its loop's `postLP`, as
the heap signature's `prePR` and `postPR` (`prT`: the run translated, the offsets kept), each run among
the signature's runs.

A heap pointer run's cells are read through a reader (`PtrSet rd`). Over a frame holding the
parameters, a mode pointer run (`PW`) is its heap pointer run written for a reader consistent with
the memory (`RdW`: where both have a word, the same, `pw_slotT`); conversely for a reader that reads
the memory's written cells (`RdM`, `slot_pwT`), the run's cells written. The reference's reader is
consistent with a memory agreeing with it (`rdW_img`) and reads its written cells within `2 ^ κ` cells
(`rdM_img`); `memRd m rd`, `m`'s words where written and `rd`'s elsewhere, reads `m`'s (`rdM_memRd`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Prover.Exec (St Mem maxCells gpow_inj Mem.get_of_written Agree refMem refRd_img)
open LeanVM.Guest.Mode (IdxVal RW HW PW PtrW MonoVal BaseVal LTF TermAt Names)

@[expose] public section

variable {κ : ℕ}

/-! ## The translation -/

/-- **A mode pointer run as a heap pointer run**: its run translated (`rngT0`), its offsets. -/
def prT (G : Mode.Sig) (np : ℕ) (p : Mode.Rng × List ℕ) : Option (CRun × List ℕ) :=
  (rngT0 G np p.1).map fun q ↦ (q, p.2)

/-- A heap run among runs. -/
def runIn (q : CRun) (l : List CRun) : Bool := l.any fun q' ↦ decide (q' = q)

/-- The frame cells `2 + b`, from `b`, of the arguments `V.n b`: those a call passes on unchanged. -/
def passOf : List V → ℕ → List ℕ
  | [], _ => []
  | v :: vs, b => (match vnum v with
    | some n => bif Nat.beq n b then [2 + b] else []
    | none => []) ++ passOf vs (b + 1)

/-- **The parameters' cells a loop helper's tail call passes on unchanged**: argument `b` the parameter
`V.n b`. -/
def tailPass (body : List Stmt) : List ℕ :=
  match body.reverse with
  | .ret [] :: .callIf _ _ args :: _ => passOf args 0
  | _ => []

theorem passOf_spec : ∀ {args : List V} {b o : ℕ}, o ∈ passOf args b →
    ∃ k, o = 2 + (b + k) ∧ args[k]? = some (V.n (b + k))
  | [], _, _, h => by simp [passOf] at h
  | v :: vs, b, o, h => by
    simp only [passOf, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i n hn
        cases hb : Nat.beq n b <;> simp only [hb, Bool.cond_true, Bool.cond_false] at h
        · cases h
        · rw [Nat.beq_eq] at hb
          subst hb
          rw [List.mem_singleton] at h
          exact ⟨0, by omega, by simp [vnum_eq hn]⟩
      · cases h
    · obtain ⟨k, rfl, hk⟩ := passOf_spec h
      exact ⟨k + 1, by omega, by rw [show b + (k + 1) = b + 1 + k by omega]; simpa using hk⟩

theorem tailPass_spec {body pre : List Stmt} {c : V} {f : String} {args : List V}
    (hb : body = pre ++ [.callIf c f args, .ret []]) {o : ℕ} (h : o ∈ tailPass body) :
    ∃ k, o = 2 + k ∧ args[k]? = some (V.n k) := by
  subst hb
  simp only [tailPass, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at h
  obtain ⟨k, rfl, hk⟩ := passOf_spec h
  exact ⟨k, by omega, by simpa using hk⟩

/-- **A bound whose value exists at each iteration's entry**: a constant, the termination fact's, or the
exponent of an entry run's bound cell (`expCells`, a power of `g` in the reference, `ExpW`) among `ps`
(the cells the tail call passes on unchanged, for the next iteration's preconditions). -/
def idxKX (G : Mode.Sig) (ps : List ℕ) (i : Mode.Idx) : Bool :=
  idxK G i || match i with
    | .ex (.fr o) 0 => (expCells G).contains o && ps.contains o && G.entry.contains o && decide (o < 2 ^ 28)
    | _ => false

/-- A run whose bounds `idxKX`. -/
def rngKX (G : Mode.Sig) (ps : List ℕ) (r : Mode.Rng) : Bool := idxKX G ps r.lo && idxKX G ps r.hi

/-- **A loop helper's heap signature is its mode signature's translation**, pointer runs included:
field by field (`SigL`), its preconditions' pointer runs `preP` the heap signature's `prePR`, its loop's `postLP` its
`postPR`, each pointer run's run among the signature's runs, every bound a constant, the termination
fact's or an entry run's bound cell's (`idxKX`; for the preconditions, one the tail call passes on, `ps`); its runs
over its caller's cells (`.hp 1 d`) over the slots its links `gl` name (`rngTG`, `lgOk`, `dsIn`; a parameter's one the
tail call passes on, in `ps`), the address runs after its preconditions' runs (`addrRs`). -/
def sigOkLP (G : Mode.Sig) (h : HSig) (np : ℕ) (ps : List ℕ) (gl : List (ℕ × ℕ × ℕ)) : Bool :=
  G.ret.isEmpty && G.postP.isEmpty && G.retV.isEmpty && G.postT.isEmpty && G.postC.isEmpty &&
    h.preP.isEmpty && h.postP.isEmpty && h.retM.isEmpty && (h.postV.isEmpty && h.postQ.isEmpty) && h.retEq.isEmpty &&
    (lgOk np gl h.ghosts && dsIn G gl && gl.all (fun l ↦ Nat.ble np l.2.1 || ps.contains (2 + l.2.1))) &&
    (match G.term, h.term with
      | [(lo, hi)], [(.val 0, ei)] => decide (lo = .ex (.fr 2) 0) && parCell G np 2 && decide (idxT G np hi = some ei)
      | _, _ => false) &&
    decide (G.pre.mapM (monoT G np) = some h.pre) &&
    decide ((G.preR.mapM (rngTG G np gl)).map (· ++ addrRs gl) = some h.preR) &&
    decide (G.post.mapM (monoT G np) = some h.post) &&
    decide ((G.postR ++ G.postL).mapM (rngT G np) = some h.postR) &&
    decide (G.preP.mapM (prT G np) = some h.prePR) && decide (G.postLP.mapM (prT G np) = some h.postPR) &&
    G.preR.all (fun r ↦ (rngH gl r).isSome || rngKX G ps r) && (G.postR ++ G.postL).all (rngKX G (expCells G)) && G.preP.all (fun p ↦ rngKX G ps p.1) &&
    G.postLP.all (fun p ↦ rngKX G (expCells G) p.1) && h.prePR.all (fun p ↦ runIn p.1 h.preR) &&
    h.postPR.all (fun p ↦ runIn p.1 h.postR)

/-- **What `sigOkLP` says**, unfolded. -/
structure SigLP (G : Mode.Sig) (h : HSig) (np : ℕ) (ps : List ℕ) (gl : List (ℕ × ℕ × ℕ)) : Prop where
  ret : G.ret = []
  postP : G.postP = []
  retV : G.retV = []
  postT : G.postT = []
  postC : G.postC = []
  hpreP : h.preP = []
  hpostP : h.postP = []
  hretM : h.retM = []
  hpostV : h.postV = []
  hpostQ : h.postQ = []
  hretEq : h.retEq = []
  hghost : lgOk np gl h.ghosts = true
  dsIn : dsIn G gl = true
  pass : ∀ l ∈ gl, np ≤ l.2.1 ∨ 2 + l.2.1 ∈ ps
  term : ∃ hi ei, G.term = [(.ex (.fr 2) 0, hi)] ∧ h.term = [(.val 0, ei)] ∧ parCell G np 2 = true ∧
    idxT G np hi = some ei
  pre : G.pre.mapM (monoT G np) = some h.pre
  preR : (G.preR.mapM (rngTG G np gl)).map (· ++ addrRs gl) = some h.preR
  post : G.post.mapM (monoT G np) = some h.post
  postR : (G.postR ++ G.postL).mapM (rngT G np) = some h.postR
  preP : G.preP.mapM (prT G np) = some h.prePR
  postLP : G.postLP.mapM (prT G np) = some h.postPR
  kpreR : ∀ r ∈ G.preR, (rngH gl r).isSome = true ∨ rngKX G ps r = true
  kpostR : ∀ r ∈ G.postR ++ G.postL, rngKX G (expCells G) r = true
  kpreP : ∀ p ∈ G.preP, rngKX G ps p.1 = true
  kpostLP : ∀ p ∈ G.postLP, rngKX G (expCells G) p.1 = true
  inPre : ∀ p ∈ h.prePR, p.1 ∈ h.preR
  inPost : ∀ p ∈ h.postPR, p.1 ∈ h.postR

theorem runIn_mem {q : CRun} {l : List CRun} (h : runIn q l = true) : q ∈ l := by
  obtain ⟨q', hq', he⟩ := List.any_eq_true.mp h
  rw [← of_decide_eq_true he]
  exact hq'

theorem sigLP_of {G : Mode.Sig} {h : HSig} {np : ℕ} {ps : List ℕ} {gl : List (ℕ × ℕ × ℕ)}
    (hs : sigOkLP G h np ps gl = true) : SigLP G h np ps gl := by
  unfold sigOkLP at hs
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq, List.all_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, ⟨⟨h11, h11'⟩, h11''⟩⟩,
    hterm⟩, hpre⟩, hpreR⟩, hpost⟩, hpostR⟩, hpP⟩, hpLP⟩, hk1⟩, hk2⟩, hk3⟩, hk4⟩, hi1⟩, hi2⟩ := hs
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9.1, h9.2, h10, h11, h11', fun l hl ↦ ?_, ?_, hpre, hpreR, hpost, hpostR,
    hpP, hpLP, fun r hr ↦ Bool.or_eq_true_iff.mp (hk1 r hr), hk2, hk3, hk4, fun p hp ↦ runIn_mem (hi1 p hp),
    fun p hp ↦ runIn_mem (hi2 p hp)⟩
  · have := h11'' l hl
    simp only [Bool.or_eq_true, Nat.ble_eq, List.contains_iff_mem] at this
    exact this
  split at hterm
  · rename_i lo hi ei hG hh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hterm
    obtain ⟨⟨rfl, h2⟩, h3⟩ := hterm
    exact ⟨hi, ei, hG, hh, h2, h3⟩
  · cases hterm

/-- **The entry runs' bound cells among `ps` hold powers of `g`** in frame `s.fp` of the memory. -/
def ExpM (G : Mode.Sig) (ps : List ℕ) (s : St) : Prop :=
  ∀ o ∈ expCells G, o ∈ ps → o ∈ G.entry → o < 2 ^ 28 → ∃ e, e < 2 ^ 62 ∧ s.mem.get (s.fp + o) = some (ofK (g ^ e))

theorem ExpM.mono {G : Mode.Sig} {ps : List ℕ} {s s' : St} (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp)
    (h : ExpM G ps s) : ExpM G ps s' := fun o h1 h2 h3 h4 ↦ by
  obtain ⟨e, he, hg⟩ := h o h1 h2 h3 h4
  exact ⟨e, he, by rw [hfp]; exact hle.get _ _ hg⟩

/-- **A bound `idxKX` has its value** where the termination facts and `ExpM` hold. -/
theorem idxKX_val {G : Mode.Sig} {ps : List ℕ} {s : St} (hT : ∀ p ∈ G.term, LTF s p.1 p.2) (hX : ExpM G ps s)
    {i : Mode.Idx} (h : idxKX G ps i = true) : ∃ x, IdxVal s i x := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact idxK_val hT h
  rcases i with n | ⟨o | ⟨q, d⟩, c⟩
  · simp at h
  · rcases c with _ | c
    · simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      obtain ⟨e, he, hg⟩ := hX o h1 h2 h3 h4
      exact ⟨e, _, e, hg, rfl, he, rfl⟩
    · simp at h
  · simp at h

theorem prT_spec {G : Mode.Sig} {np : ℕ} {p : Mode.Rng × List ℕ} {q : CRun × List ℕ} (h : prT G np p = some q) :
    rngT0 G np p.1 = some q.1 ∧ q.2 = p.2 := by
  unfold prT at h
  obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨hq', rfl⟩

/-! ## Readers and memories -/

theorem lt63_of {x : ℕ} (h : x < maxCells) : x < 2 ^ 63 := by
  unfold maxCells at h; omega

/-- **A reader consistent with a memory**: where both have a word at a cell, the same. -/
def RdW (rd : Reader) (m : Mem) : Prop :=
  ∀ x, x < maxCells → ∀ u v, m.get x = some u → rd (g ^ x) = some v → u = v

/-- **A reader that reads a memory's written cells**: their words. -/
def RdM (rd : Reader) (m : Mem) : Prop :=
  ∀ x, x < maxCells → m.written x = true → rd (g ^ x) = m.get x

theorem RdM.rdW {rd : Reader} {m : Mem} (h : RdM rd m) : RdW rd m := fun x hx u v hu hv ↦ by
  rw [h x hx (Mode.written_of_get hu), hu] at hv
  exact Option.some.inj hv

theorem rdW_img {img : MemoryImage κ} (hκ : κ ≤ 28) {m : Mem} (ha : Agree m (refMem img)) :
    RdW img.read m := fun x hx u v hu hv ↦ by
  have h1 := ha.get _ _ hu
  have h2 := (refRd_img hκ img x v (by unfold maxCells at hx; omega) hv).2
  rw [← h1, h2]

theorem rdM_img {img : MemoryImage κ} (hκ : κ ≤ 28) {m : Mem} (ha : Agree m (refMem img))
    (hu : m.used ≤ 2 ^ κ) : RdM img.read m := fun x _ hw ↦ by
  obtain ⟨p, hp⟩ := Mem.get_of_written hw
  have hlt : x < 2 ^ κ := lt_of_lt_of_le (ha.wf.get_lt hp) hu
  rw [hp, read_refMem hκ hlt, ← ha.get _ _ hp]

open Classical in
/-- **A memory's words where written, the reader's elsewhere.** -/
noncomputable def memRd (m : Mem) (rd : Reader) : Reader := fun y ↦
  if h : ∃ x, x < maxCells ∧ y = g ^ x ∧ m.written x = true then m.get h.choose else rd y

theorem rdM_memRd (m : Mem) (rd : Reader) : RdM (memRd m rd) m := fun x hx hw ↦ by
  have he : ∃ x', x' < maxCells ∧ (g : K) ^ x = g ^ x' ∧ m.written x' = true := ⟨x, hx, rfl, hw⟩
  unfold memRd
  rw [dite_eq_left_of_eq_true (eq_true he)]
  obtain ⟨h1, h2, -⟩ := he.choose_spec
  rw [gpow_inj (lt63_of h1) (lt63_of hx) h2.symm]

/-- At a written cell of `m'` past `m`, written in `m`, `memRd m' rd` reads what `m` holds. -/
theorem memRd_le {m m' : Mem} (hle : m ≤ m') (rd : Reader) {x : ℕ} (hx : x < maxCells) (hw : m.written x = true) :
    memRd m' rd (g ^ x) = m.get x := by
  rw [rdM_memRd m' rd x hx (Mode.written_mono hle hw)]
  obtain ⟨u, hu⟩ := Mem.get_of_written hw
  rw [hu, hle.get _ _ hu]

/-! ## Pointer runs, over a frame holding the parameters -/

/-- **A mode pointer run is its heap pointer run written**, for a reader consistent with the memory. -/
theorem pw_slotT {G : Mode.Sig} {np : ℕ} {s : St} {ws : List E} (hP : ParAt G np s ws) {r : Mode.Rng} {q : CRun}
    (hr : rngT0 G np r = some q) {rd : Reader} (hrd : RdW rd s.mem) {os : List ℕ} (h : PW s r os) :
    ∀ x, (∃ a, q.Set (slotW ws) a ∧ PtrSet rd a os x) → WrK s.mem x := by
  obtain ⟨c, lo, hi, hmS, hmc, hlo, hhi, rfl⟩ := rngT_spec hr
  rintro x ⟨a, ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩, w', hw', o, ho, rfl⟩
  obtain ⟨vq, xlo, xhi, hv, hil, hih, hall⟩ := h
  have e1 := (idxVal_iff hP hlo).mp hil
  have e2 := (idxVal_iff hP hhi).mp hih
  rw [h1, Option.some.injEq] at e1
  rw [h2, Option.some.injEq] at e2
  subst e1 e2
  obtain ⟨x', hx', p, hp, hpw⟩ := hall j h3 h4
  rw [monoVal_slot hmc (slotGet_par hP hmS).eq hv, run_val] at hx'
  rw [hx'.1] at hw'
  obtain rfl := hrd x' hx'.2 p w' hp hw'
  obtain ⟨y, hy, hyw⟩ := hpw o ho
  refine ⟨y, ?_, hy.2, hyw⟩
  rw [← hy.1, limb0_mul_ofK]

/-- **A heap pointer run written is its mode pointer run**, for a reader that reads the memory's
written cells, the run's cells written, both bounds' values existing. -/
theorem slot_pwT {G : Mode.Sig} {np : ℕ} {s : St} {ws : List E} (hP : ParAt G np s ws) {r : Mode.Rng} {q : CRun}
    (hr : rngT0 G np r = some q) {rd : Reader} (hrd : RdM rd s.mem) {os : List ℕ}
    (hlo : ∃ x, IdxVal s r.lo x) (hhi : ∃ x, IdxVal s r.hi x)
    (hcells : ∀ x, q.Set (slotW ws) x → WrK s.mem x)
    (h : ∀ x, (∃ a, q.Set (slotW ws) a ∧ PtrSet rd a os x) → WrK s.mem x) : PW s r os := by
  obtain ⟨c, lo, hi, hmS, hmc, hlo', hhi', rfl⟩ := rngT_spec hr
  obtain ⟨xlo, hxlo⟩ := hlo
  obtain ⟨xhi, hxhi⟩ := hhi
  refine ⟨_, xlo, xhi, monoVal_slot' hmc (slotGet_par hP hmS), hxlo, hxhi, fun j h1 h2 ↦ ?_⟩
  have hset : (⟨⟨c.bases, c.off + r.d⟩, r.S, lo, hi⟩ : CRun).Set (slotW ws)
      (((⟨c.bases, c.off + r.d⟩ : CCell).valW (slotW ws) * ofK (addressOfIndex (r.S * j))).limb 0) :=
    ⟨xlo, xhi, j, (idxVal_iff hP hlo').mp hxlo, (idxVal_iff hP hhi').mp hxhi, h1, h2, rfl⟩
  obtain ⟨x', hx', hw⟩ := names_wrk (hcells _ hset)
  obtain ⟨p, hp⟩ := Mem.get_of_written hw
  rw [run_val]
  refine ⟨x', hx', p, hp, fun o ho ↦ ?_⟩
  have hrd' : rd (((⟨c.bases, c.off + r.d⟩ : CCell).valW (slotW ws) * ofK (addressOfIndex (r.S * j))).limb 0) =
      some p := by
    rw [hx'.1, hrd x' hx'.2 hw, hp]
  obtain ⟨y, hy1, hy2, hyw⟩ := h (p.limb 0 * addressOfIndex o) ⟨_, hset, p, hrd', o, ho, rfl⟩
  refine ⟨y, ⟨?_, hy2⟩, hyw⟩
  rw [limb0_mul_ofK]
  exact hy1

end

end LeanVM.Guest.CoreMode
