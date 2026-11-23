/-
  LeanVM.Guest.CoreMode.LoopSig

  A loop helper's mode signature as a heap signature: bounds over parameters' exponents.
-/

module

public import LeanVM.Guest.CoreMode.CoreSlot

/-!
# A loop helper's signature, translated

A loop helper's mode signature (`Mode.Sig`) speaks of runs whose bounds are exponents of its
parameters' words (`.ex (.fr o) 0`, frame cell `o = 2 + b` holding parameter `b`) or constants, and of
its termination fact (its counter's exponent below its bound's). `idxT` and `rngT` translate those to
the heap check's indices (`CIdx.val b`, `CIdx.num n`) and runs (`CRun`); `SigL` says a heap
signature is a mode signature's translation, field by field (`sigOkLP` checks it, `LoopSigP.lean`).

Over a frame whose parameter cells hold the slots' words (`ParAt`): a mode exponent's value is its
translation's exponent (`idxVal_iff`), a mode run written is its heap run's cells written (`rw_slotT`)
and conversely, both bounds' exponents existing (`slot_rwT`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Prover.Exec (St Mem maxCells)
open LeanVM.Guest.Mode (IdxVal RW HW MonoVal BaseVal LTF TermAt)

@[expose] public section

/-! ## The translation -/

/-- A frame cell holding a parameter's word: `2 + b`, `b` a parameter, an entry cell, small. -/
def parCell (G : Mode.Sig) (np o : ℕ) : Bool :=
  decide (2 ≤ o) && decide (o - 2 < np) && decide (o < 2 ^ 28) && G.entry.contains o

/-- **A mode exponent as a heap index**: a constant below `2^62`, or the exponent of a parameter's
word. -/
def idxT (G : Mode.Sig) (np : ℕ) : Mode.Idx → Option CIdx
  | .num n => bif decide (n < 2 ^ 62) then some (.num n) else none
  | .ex (.fr o) 0 => bif parCell G np o then some (.val (o - 2)) else none
  | _ => none

/-- **A mode run as a heap run, its offset as it is**: its product over parameters' entry cells, its offset folded,
its bounds translated. -/
def rngT0 (G : Mode.Sig) (np : ℕ) (r : Mode.Rng) : Option CRun :=
  bif monoS G np true r.q then
    match monoC r.q, idxT G np r.lo, idxT G np r.hi with
    | some c, some lo, some hi => some ⟨⟨c.bases, c.off + r.d⟩, r.S, lo, hi⟩
    | _, _, _ => none
  else none

/-- Both bounds constants. -/
def numBs (r : Mode.Rng) : Bool :=
  match r.lo, r.hi with
  | .num _, .num _ => true
  | _, _ => false

/-- **A mode run as a heap run**: `rngT0`, or for constant bounds `rngC` (a wrapped offset starting at the run's first
cell). -/
def rngT (G : Mode.Sig) (np : ℕ) (r : Mode.Rng) : Option CRun :=
  bif monoS G np true r.q && numBs r then rngC r else rngT0 G np r

/-- A product over parameters' entry cells, translated. -/
def monoT (G : Mode.Sig) (np : ℕ) (m : Mode.Mono) : Option CCell :=
  bif monoS G np true m then monoC m else none

/-- An exponent either a constant or one of the termination fact's: its value exists wherever the
termination fact holds. -/
def idxK (G : Mode.Sig) : Mode.Idx → Bool
  | .num _ => true
  | i => G.term.any fun p ↦ decide (p.1 = i) || decide (p.2 = i)

/-- A run whose bounds' values exist wherever the termination fact holds. -/
def rngK (G : Mode.Sig) (r : Mode.Rng) : Bool := idxK G r.lo && idxK G r.hi

/-! ## Over a frame holding the parameters -/

/-- Frame `s.fp`'s parameter cells hold the slots' words `ws`. -/
def ParAt (G : Mode.Sig) (np : ℕ) (s : St) (ws : List E) : Prop :=
  ∀ o, parCell G np o = true → s.mem.get (s.fp + o) = some (slotW ws (o - 2))

theorem ParAt.mono {G : Mode.Sig} {np : ℕ} {s s' : St} {ws : List E} (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp)
    (h : ParAt G np s ws) : ParAt G np s' ws := fun o ho ↦ by rw [hfp]; exact hle.get _ _ (h o ho)

theorem parCell_spec {G : Mode.Sig} {np o : ℕ} (h : parCell G np o = true) :
    2 ≤ o ∧ o - 2 < np ∧ o < 2 ^ 28 ∧ o ∈ G.entry := by
  simp only [parCell, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem monoT_spec {G : Mode.Sig} {np : ℕ} {m : Mode.Mono} {c : CCell} (h : monoT G np m = some c) :
    monoS G np true m = true ∧ monoC m = some c := by
  unfold monoT at h
  cases hm : monoS G np true m <;> simp only [hm, Bool.cond_true, Bool.cond_false] at h
  · cases h
  · exact ⟨rfl, h⟩

/-- `ParAt` gives `SlotGet` of a product over parameters' entry cells. -/
theorem slotGet_par {G : Mode.Sig} {np : ℕ} {s : St} {ws : List E} (h : ParAt G np s ws) {m : Mode.Mono}
    (hm : monoS G np true m = true) : SlotGet s ws m.bs := by
  intro b hb
  have hb' := List.all_eq_true.mp hm b hb
  rcases hb1 : b.1 with o | ⟨q, d⟩
  · rw [hb1] at hb'
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hb'
    obtain ⟨⟨⟨h2, hn⟩, h28⟩, hent⟩ := hb'
    exact ⟨o, rfl, h2, h o (by
      simp only [parCell, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]; exact ⟨⟨⟨h2, hn⟩, h28⟩, hent⟩)⟩
  · rw [hb1] at hb'
    cases hb'

theorem idxT_spec {G : Mode.Sig} {np : ℕ} {i : Mode.Idx} {t : CIdx} (h : idxT G np i = some t) :
    (∃ n, i = .num n ∧ t = .num n ∧ n < 2 ^ 62) ∨ (∃ o, i = .ex (.fr o) 0 ∧ t = .val (o - 2) ∧ parCell G np o = true) := by
  rcases i with n | ⟨o | ⟨q, d⟩, c⟩
  · simp only [idxT, Bool.cond_decide] at h
    split_ifs at h with hn
    cases h
    exact Or.inl ⟨n, rfl, rfl, hn⟩
  · rcases c with _ | c
    · simp only [idxT] at h
      cases hp : parCell G np o <;> simp only [hp, Bool.cond_true, Bool.cond_false] at h
      · cases h
      · cases h
        exact Or.inr ⟨o, rfl, rfl, hp⟩
    · simp [idxT] at h
  · simp [idxT] at h

/-- **A mode exponent's value is its translation's exponent**, over a frame holding the parameters. -/
theorem idxVal_iff {G : Mode.Sig} {np : ℕ} {s : St} {ws : List E} (hP : ParAt G np s ws) {i : Mode.Idx} {t : CIdx}
    (h : idxT G np i = some t) {x : ℕ} : IdxVal s i x ↔ rep ((idxC t).valW (slotW ws)) = some x := by
  rcases idxT_spec h with ⟨n, rfl, rfl, hn⟩ | ⟨o, rfl, rfl, ho⟩
  · have hn' : n < capE := by rw [capE_eq]; exact hn
    simp only [IdxVal, idxC, rep_const hn', Option.some.injEq]
    exact eq_comm
  · have hget := hP o ho
    simp only [idxC, valW_baseC, IdxVal, BaseVal]
    constructor
    · rintro ⟨v, e, hv, rfl, he, rfl⟩
      rw [hget, Option.some.injEq] at hv
      rw [hv]
      exact rep_of (by rw [capE_eq]; exact he)
    · intro hr
      obtain ⟨hlt, hw⟩ := rep_spec hr
      refine ⟨_, x, hget, by rw [hw], by rw [capE_eq] at hlt; exact hlt, rfl⟩

theorem rngT_spec {G : Mode.Sig} {np : ℕ} {r : Mode.Rng} {q : CRun} (h : rngT0 G np r = some q) :
    ∃ c lo hi, monoS G np true r.q = true ∧ monoC r.q = some c ∧ idxT G np r.lo = some lo ∧ idxT G np r.hi = some hi ∧
      q = ⟨⟨c.bases, c.off + r.d⟩, r.S, lo, hi⟩ := by
  unfold rngT0 at h
  cases hm : monoS G np true r.q <;> simp only [hm, Bool.cond_true, Bool.cond_false] at h
  · cases h
  split at h
  · rename_i c lo hi hc hlo hhi
    cases h
    exact ⟨c, lo, hi, rfl, hc, hlo, hhi, rfl⟩
  · cases h

theorem rngT_cases {G : Mode.Sig} {np : ℕ} {r : Mode.Rng} {q : CRun} (h : rngT G np r = some q) :
    rngT0 G np r = some q ∨ (monoS G np true r.q = true ∧ rngC r = some q) := by
  unfold rngT at h
  cases hm : (monoS G np true r.q && numBs r) <;> simp only [hm, Bool.cond_true, Bool.cond_false] at h
  · exact Or.inl h
  · exact Or.inr ⟨(Bool.and_eq_true _ _).mp hm |>.1, h⟩

theorem run_val {w : ℕ → E} (c : CCell) (S j d : ℕ) :
    (c.valW w * ofK (g ^ (S * j + d))) = ((⟨c.bases, c.off + d⟩ : CCell).valW w * ofK (addressOfIndex (S * j))) := by
  rw [valW_shiftc]
  simp only [addressOfIndex, pow_add, ofK_mul']
  ring

/-- **A mode run written is its heap run's cells written**, over a frame holding the parameters. -/
theorem rw_slotT {G : Mode.Sig} {np : ℕ} {s : St} {ws : List E} (hP : ParAt G np s ws) {r : Mode.Rng} {q : CRun}
    (hr : rngT G np r = some q) (h : RW s r) : ∀ x, q.Set (slotW ws) x → WrK s.mem x := by
  rcases rngT_cases hr with hr | ⟨hmS, hr⟩
  swap
  · exact rw_slot hr (slotGet_par hP hmS).eq h
  obtain ⟨c, lo, hi, hmS, hmc, hlo, hhi, rfl⟩ := rngT_spec hr
  rintro x ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩
  obtain ⟨vq, xlo, xhi, hv, hil, hih, hall⟩ := h
  have e1 := (idxVal_iff hP hlo).mp hil
  have e2 := (idxVal_iff hP hhi).mp hih
  rw [h1, Option.some.injEq] at e1
  rw [h2, Option.some.injEq] at e2
  subst e1 e2
  obtain ⟨y, hy, hw⟩ := hall j h3 h4
  rw [monoVal_slot hmc (slotGet_par hP hmS).eq hv, run_val] at hy
  exact wrk_names hy hw

/-- **A heap run's cells written is its mode run written**, over a frame holding the parameters, both
bounds' values existing. -/
theorem slot_rwT {G : Mode.Sig} {np : ℕ} {s : St} {ws : List E} (hP : ParAt G np s ws) {r : Mode.Rng} {q : CRun}
    (hr : rngT G np r = some q) (hlo : ∃ x, IdxVal s r.lo x) (hhi : ∃ x, IdxVal s r.hi x)
    (h : ∀ x, q.Set (slotW ws) x → WrK s.mem x) : RW s r := by
  rcases rngT_cases hr with hr | ⟨hmS, hr⟩
  swap
  · exact slot_rw hr (slotGet_par hP hmS) h
  obtain ⟨c, lo, hi, hmS, hmc, hlo', hhi', rfl⟩ := rngT_spec hr
  obtain ⟨xlo, hxlo⟩ := hlo
  obtain ⟨xhi, hxhi⟩ := hhi
  refine ⟨_, xlo, xhi, monoVal_slot' hmc (slotGet_par hP hmS), hxlo, hxhi, fun j h1 h2 ↦ ?_⟩
  have hx := h _ ⟨xlo, xhi, j, (idxVal_iff hP hlo').mp hxlo, (idxVal_iff hP hhi').mp hxhi, h1, h2, rfl⟩
  rw [run_val]
  exact names_wrk hx

/-- A product written is its cell written, over a frame holding the parameters. -/
theorem hw_slotT {G : Mode.Sig} {np : ℕ} {s : St} {ws : List E} (hP : ParAt G np s ws) {m : Mode.Mono} {c : CCell}
    (hm : monoT G np m = some c) (h : HW s m) : WrK s.mem (c.addrW (slotW ws)) :=
  hw_slot (monoT_spec hm).2 (slotGet_par hP (monoT_spec hm).1).eq h

theorem slot_hwT {G : Mode.Sig} {np : ℕ} {s : St} {ws : List E} (hP : ParAt G np s ws) {m : Mode.Mono} {c : CCell}
    (hm : monoT G np m = some c) (h : WrK s.mem (c.addrW (slotW ws))) : HW s m :=
  slot_hw (monoT_spec hm).2 (slotGet_par hP (monoT_spec hm).1) h

/-! ## The signature, field by field -/

theorem mapM_mem {α β : Type} {f : α → Option β} : ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
    (∀ b ∈ l', ∃ a ∈ l, f a = some b) ∧ ∀ a ∈ l, ∃ b ∈ l', f a = some b
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨h1, h2⟩ := mapM_mem hbs
    refine ⟨fun b' hb' ↦ ?_, fun a' ha' ↦ ?_⟩
    · rcases List.mem_cons.mp hb' with rfl | hb'
      · exact ⟨a, List.mem_cons_self, hb⟩
      · obtain ⟨a', ha', h'⟩ := h1 b' hb'
        exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩
    · rcases List.mem_cons.mp ha' with rfl | ha'
      · exact ⟨b, List.mem_cons_self, hb⟩
      · obtain ⟨b', hb', h'⟩ := h2 a' ha'
        exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

/-- **A heap signature, a mode signature's translation**, field by field. -/
structure SigL (G : Mode.Sig) (h : HSig) (np : ℕ) : Prop where
  ret : G.ret = []
  postP : G.postP = []
  postLP : G.postLP = []
  preP : G.preP = []
  retV : G.retV = []
  postT : G.postT = []
  postC : G.postC = []
  hpreP : h.preP = []
  hprePR : h.prePR = []
  hpostP : h.postP = []
  hpostPR : h.postPR = []
  hretM : h.retM = []
  hpostV : h.postV = []
  hpostQ : h.postQ = []
  hretEq : h.retEq = []
  hghost : h.ghosts = 0
  term : ∃ hi ei, G.term = [(.ex (.fr 2) 0, hi)] ∧ h.term = [(.val 0, ei)] ∧ parCell G np 2 = true ∧
    idxT G np hi = some ei
  pre : G.pre.mapM (monoT G np) = some h.pre
  preR : G.preR.mapM (rngT G np) = some h.preR
  post : G.post.mapM (monoT G np) = some h.post
  postR : (G.postR ++ G.postL).mapM (rngT G np) = some h.postR
  kpreR : ∀ r ∈ G.preR, rngK G r = true
  kpostR : ∀ r ∈ G.postR ++ G.postL, rngK G r = true

/-- An exponent of a run checked by `rngK` has its value where the termination facts hold. -/
theorem idxK_val {G : Mode.Sig} {s : St} (hT : ∀ p ∈ G.term, LTF s p.1 p.2) {i : Mode.Idx}
    (h : idxK G i = true) : ∃ x, IdxVal s i x := by
  cases i with
  | num n => exact ⟨n, rfl⟩
  | ex b c =>
    obtain ⟨p, hp, hpi⟩ := List.any_eq_true.mp h
    obtain ⟨xa, xb, ha, hb, -⟩ := hT p hp
    rcases Bool.or_eq_true_iff.mp hpi with h1 | h1
    · rw [decide_eq_true_eq] at h1; rw [← h1]; exact ⟨xa, ha⟩
    · rw [decide_eq_true_eq] at h1; rw [← h1]; exact ⟨xb, hb⟩

end

end LeanVM.Guest.CoreMode
