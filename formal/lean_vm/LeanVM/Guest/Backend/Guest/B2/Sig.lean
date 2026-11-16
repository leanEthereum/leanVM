/-
  LeanVM.Guest.Backend.Guest.B2.Sig

  The guest's precondition `guestU` and a certificate's signature imply each other, from a
  decidable comparison of the two.
-/

module

public import LeanVM.Guest.CheckSound
public import LeanVM.Guest.CheckView
public import LeanVM.Guest.Backend.Sound.Obl.Walk

/-!
# The two preconditions

A certificate's signature asks of a frame (`Check.Pre`): bounds on cells (`pre`), bounds on words
read through cells (`mem`, the cell and the word read), and tagged tuples of cells in relations
(`sem`). The back end's precondition is `guestU` of the argument words: the table's bounds
(`guestTab`), its relations (`guestRel`) and the `ext` functions' (`guestX`). `sigOk cs ts x`
compares a signature `cs` with a table entry `ts` and an `ext` relation `x`, entry by entry in
both directions; with it

* `u_of_cert`: the certificate's precondition gives `guestU` of the frame's argument words;
* `cert_of_u`: `guestU` of them gives the certificate's bounds, reads and relations.

A relation tag the certificates write is decoded as `Check.SemRel` over `globSem` does: `0` the
exponent table, `tagTabs` the window table, a walk tag of kind `0`, `odd = 1` the path windows
(`isWins`), and the `ext` functions' tuples (`semOfSpec`).
-/

namespace LeanVM.Guest.Backend.B2

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend.Obl
open LeanVM.Guest.B1

@[expose] public section

/-! ## The comparison -/

/-- A walk tag of the path windows `walk_path` dispatches on: kind `0`, `odd = 1`. -/
def isWins (t : Nat) : Bool := 2 ≤ t && t < 2 ^ 16 && walkKind t == 0 && walkOdd t == 1

/-- The tagged cells of an `ext` function's relation, as the certificates write them. -/
def semOfSpec : XSpec → List (Nat × List Nat)
  | .gkr => [(tagGkr, [5, 2, 4, 11])]
  | .loop w => [(Check.tagNe, [2, 3]), (walkTag w.base w.odd w.d w.cd, [5, 2, 3])]
  | .main w => [(walkTag (2 + w.base) w.odd w.d w.cd, [8, 9])]
  | .lq n w => [(lqTag n w.odd w.base w.d w.cd, [7])]

/-- An `ext` relation's shape is in the tags' range, and the arguments it reads are below `na`. -/
def specOk (na : Nat) : XSpec → Bool
  | .gkr => 10 ≤ na
  | .loop w => 4 ≤ na && w.base < 2 && w.odd < 2 && w.cd < 64 && w.d < 64 &&
      (w.base == 1 || w.odd == 0)
  | .main w => 8 ≤ na && w.base < 2 && w.odd < 2 && w.cd < 64 && w.d < 64
  | .lq n w => 6 ≤ na && w.base < 2 && w.odd < 2 && w.cd < 64 && w.d < 64 && n < 2 ^ 14

/-- A tagged tuple of the certificate is one of the `ext` relation's. -/
def specCov (ts : Obl.Sig) (x : Option XSpec) (na : Nat) (s : Nat × List Nat) : Bool :=
  match x with
  | some sp => ts.ext && specOk na sp && (semOfSpec sp).contains s
  | none => false

/-- A bound of the certificate is one of the table's, on an argument. -/
def preCov (ts : Obl.Sig) (na : Nat) (p : Nat × Nat) : Bool :=
  ts.pre.any fun q => q.1 + 2 == p.1 && decide (q.1 < na) && decide (q.2 ≤ p.2)

/-- A bounded read of the certificate is a `memRel` relation of the table, on an argument. -/
def memCov (ts : Obl.Sig) (na : Nat) (m : Nat × Nat × Nat) : Bool :=
  decide (m.2.2 < 2 ^ 16) &&
    ts.xpre.any fun q => q.1 + 2 == m.1 && decide (q.1 < na) && q.2 == memRel m.2.1 m.2.2

/-- A tagged tuple of the certificate is a relation of the table on an argument, or the `ext`
relation's. -/
def semCov (ts : Obl.Sig) (x : Option XSpec) (na : Nat) (s : Nat × List Nat) : Bool :=
  (match s.2 with
    | [c] => decide (2 ≤ c) && decide (c - 2 < na) &&
        ((s.1 == 0 && ts.xpre.contains (c - 2, 0)) || (s.1 == tagTabs && ts.xpre.contains (c - 2, 1)) ||
          (isWins s.1 && ts.xpre.contains (c - 2, s.1)))
    | _ => false) || specCov ts x na s

/-- A bound of the table is one of the certificate's. -/
def preBack (cs : Check.Sig) (q : Nat × Nat) : Bool :=
  cs.pre.any fun p => p.1 == q.1 + 2 && decide (p.2 ≤ q.2)

/-- A bound of the table on a word read, if read, is a bounded read of the certificate, or a path
window of a walk relation of the certificate. -/
def memBack (cs : Check.Sig) (q : Nat × Nat × Nat) : Bool :=
  cs.mem.any (fun m => m.1 == q.1 + 2 && m.2.1 == q.2.1 && decide (m.2.2 ≤ q.2.2)) ||
    cs.sem.any fun s => s.2 == [q.1 + 2] && isWins s.1 && decide (walkCd s.1 ≤ walkD s.1) &&
      decide (q.2.1 < (walkD s.1 - walkCd s.1 + 5) / 6) && decide (64 ≤ q.2.2)

/-- A relation of the table is a tagged tuple of the certificate, or a `memRel` its bounded read. -/
def xpreBack (cs : Check.Sig) (q : Nat × Nat) : Bool :=
  (q.2 == 0 && cs.sem.contains (0, [q.1 + 2])) || (q.2 == 1 && cs.sem.contains (tagTabs, [q.1 + 2])) ||
    (isWins q.2 && cs.sem.contains (q.2, [q.1 + 2])) ||
    cs.mem.any fun m => m.1 == q.1 + 2 && decide (m.2.2 < 2 ^ 16) && memRel m.2.1 m.2.2 == q.2

/-- The `ext` relation of the table is the certificate's tuples. -/
def extBack (cs : Check.Sig) (ts : Obl.Sig) (x : Option XSpec) : Bool :=
  !ts.ext || match x with
    | some sp => specOk cs.nargs sp && (semOfSpec sp).all cs.sem.contains
    | none => true

/-- **The comparison of a signature with a table entry and an `ext` relation**, both ways. -/
def sigOk (cs : Check.Sig) (ts : Obl.Sig) (x : Option XSpec) : Bool :=
  cs.pre.all (preCov ts cs.nargs) && cs.mem.all (memCov ts cs.nargs) &&
    cs.sem.all (semCov ts x cs.nargs) && ts.pre.all (preBack cs) && ts.mem.all (memBack cs) &&
    ts.xpre.all (xpreBack cs) && extBack cs ts x

/-! ## Words -/

variable {κ : ℕ} {L : MemoryImage κ} {fp : K}

theorem wd_eq (o : ℕ) : Check.wd L fp o = Backend.wd L fp o := rfl

theorem frameWords_eq (o n : ℕ) : Check.frameWords L fp o n = Backend.frameWords L fp o n := rfl

theorem frameWords_getD {n i : ℕ} (h : i < n) :
    (Backend.frameWords L fp 2 n).getD i 0 = Backend.wd L fp (i + 2) := by
  rw [Backend.frameWords, List.getD_eq_getElem _ _ (by simpa using h)]
  simp [Nat.add_comm]

theorem read_of_wd {o : ℕ} {x : E} (h : Backend.wd L fp o = x) (hx : x ≠ 0) :
    L.read (fp * addressOfIndex o) = some x := by
  unfold Backend.wd at h
  cases hr : L.read (fp * addressOfIndex o) with
  | none => rw [hr] at h; exact absurd h.symm hx
  | some y => rw [hr] at h; exact congrArg some h

theorem ofK_gpow_ne_zero (e : ℕ) : ofK (addressOfIndex e) ≠ 0 := fun h =>
  gpow_ne_zero e ((map_eq_zero_iff (algebraMap K E) (algebraMap K E).injective).mp h)

theorem read_zero (L : MemoryImage κ) : L.read 0 = none := by
  unfold MemoryImage.read addressIndex?
  rw [dite_eq_right]
  · rfl
  · rintro ⟨i, hi⟩
    exact gpow_ne_zero _ hi.symm

/-- A word read through is not `0`. -/
theorem ne_zero_of_load {p v : E} {c : ℕ} (h : LoadHolds L.read p c v) : p ≠ 0 := by
  rintro rfl
  have h2 := h.2
  simp only [show E.limb (0 : E) 0 = 0 from rfl, zero_mul, read_zero] at h2
  exact absurd h2 (by simp)

theorem bnd_of_read {o n : ℕ} (h : ∃ e < n, L.read (fp * addressOfIndex o) = some (ofK (addressOfIndex e))) :
    Obl.Bnd (Backend.wd L fp o) n := by
  obtain ⟨e, he, hr⟩ := h
  exact ⟨e, he, by rw [Backend.wd, hr]; rfl⟩

theorem read_of_bnd {o n : ℕ} (h : Obl.Bnd (Backend.wd L fp o) n) :
    ∃ e < n, L.read (fp * addressOfIndex o) = some (ofK (addressOfIndex e)) := by
  obtain ⟨e, he, hw⟩ := h
  exact ⟨e, he, read_of_wd hw (ofK_gpow_ne_zero e)⟩

/-! ## Relations -/

variable {G : Check.Glob}

theorem semRel_plain (hG : G.sem = globSem) {t : ℕ} (ht : t < 2 ^ 31) (hne : t ≠ Check.tagNe)
    {rd : Reader} {ws : List E} : Check.SemRel G t rd ws ↔ globSem t rd ws := by
  unfold Check.SemRel Check.SemRel0
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hne, hG]

theorem semRel_ne {rd : Reader} {ws : List E} :
    Check.SemRel G Check.tagNe rd ws ↔ ws.getD 0 0 ≠ ws.getD 1 0 := by
  unfold Check.SemRel Check.SemRel0
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

theorem globSem_big {t : ℕ} (h0 : t ≠ 0) (h1 : t ≠ 1) {rd : Reader} {ws : List E} :
    globSem t rd ws ↔ (if t = tagGkr then GkrPar rd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0)
      else if t = tagTabs then B1.WinTabs rd (ws.getD 0 0)
      else if 2 ^ 21 ≤ t then lqSem t rd ws else walkSem t rd ws) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
  rfl

theorem semRel_zero (hG : G.sem = globSem) {rd : Reader} {x : E} :
    Check.SemRel G 0 rd [x] ↔ B1.ExpTables rd x ∧ B1.ExpWinTab rd x := by
  rw [semRel_plain hG (by norm_num) (by decide)]
  rfl

theorem semRel_tabs (hG : G.sem = globSem) {rd : Reader} {x : E} :
    Check.SemRel G tagTabs rd [x] ↔ B1.WinTabs rd x := by
  rw [semRel_plain hG (by unfold tagTabs; norm_num) (by decide), globSem_big (by decide) (by decide),
    ite_eq_right (by decide), ite_eq_left rfl]
  rfl

theorem semRel_wins (hG : G.sem = globSem) {t : ℕ} (ht : isWins t = true) {rd : Reader} {x : E} :
    Check.SemRel G t rd [x] ↔ B1.WinsAt rd (walkD t) (walkCd t) x := by
  simp only [isWins, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht
  obtain ⟨⟨⟨h2, h16⟩, hk⟩, ho⟩ := ht
  rw [semRel_plain hG (by omega) (by unfold Check.tagNe; omega),
    globSem_big (by omega) (by omega), ite_eq_right (by unfold tagGkr; omega),
    ite_eq_right (by unfold tagTabs; omega), ite_eq_right (by omega)]
  unfold walkSem
  rw [hk, ite_eq_left ho]
  rfl

theorem guestRel_wins {t : ℕ} (ht : isWins t = true) {rd : Reader} {x : E} :
    guestRel t rd x ↔ B1.WinsAt rd (walkD t) (walkCd t) x := by
  simp only [isWins, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht
  obtain ⟨⟨⟨h2, h16⟩, -⟩, -⟩ := ht
  unfold guestRel
  constructor
  · exact fun h => h.2.2.1 h2 (by omega)
  · exact fun h => ⟨fun h' => by omega, fun h' => by omega, fun _ _ => h, fun h' => by omega⟩

theorem guestRel_zero {rd : Reader} {x : E} :
    guestRel 0 rd x ↔ B1.ExpTables rd x ∧ B1.ExpWinTab rd x := by
  unfold guestRel
  constructor
  · exact fun h => h.1 rfl
  · exact fun h => ⟨fun _ => h, fun h' => absurd h' (by decide), fun h' => absurd h' (by decide),
      fun h' => absurd h' (by decide)⟩

theorem guestRel_one {rd : Reader} {x : E} : guestRel 1 rd x ↔ B1.WinTabs rd x := by
  unfold guestRel
  constructor
  · exact fun h => h.2.1 rfl
  · exact fun h => ⟨fun h' => absurd h' (by decide), fun _ => h, fun h' => absurd h' (by decide),
      fun h' => absurd h' (by decide)⟩

theorem guestRel_memRel_iff {rd : Reader} {x : E} {c n : ℕ} (hn : n < 2 ^ 16) :
    guestRel (memRel c n) rd x ↔ ∃ e < n, LoadHolds rd x c (ofK (addressOfIndex e)) := by
  obtain ⟨h0, h1, h2⟩ := memRel_decode (c := c) hn
  refine ⟨fun h => ?_, guestRel_memRel hn⟩
  have := h.2.2.2 h0
  rwa [h1, h2] at this

/-! ## The `ext` relations -/

theorem walkSem_loop {w : WalkSpec} (hb : w.base < 2) (ho : w.odd < 2) (hc : w.cd < 64)
    (hbo : w.base = 1 ∨ w.odd = 0) {rd : Reader} {t x N : E} :
    walkSem (walkTag w.base w.odd w.d w.cd) rd [t, x, N] ↔ LoopWalk rd w t x N := by
  obtain ⟨hK, hO, hD, hC⟩ := walkTag_decode (kind := w.base) (by omega) ho hc
  unfold walkSem LoopWalk
  rw [hK, hO, hD, hC]
  rcases (by omega : w.base = 0 ∨ w.base = 1) with h0 | h1
  · have hodd : w.odd = 0 := by omega
    rw [h0, hodd, ite_eq_right (by decide), ite_eq_right (by decide)]
    rfl
  · rw [h1, ite_eq_left rfl]
    rfl

theorem walkSem_main {w : WalkSpec} (hb : w.base < 2) (ho : w.odd < 2) (hc : w.cd < 64)
    {rd : Reader} {t N : E} :
    walkSem (walkTag (2 + w.base) w.odd w.d w.cd) rd [t, N] ↔
      OqMainWins rd w.d w.cd w.odd w.base t N := by
  obtain ⟨hK, hO, hD, hC⟩ := walkTag_decode (kind := 2 + w.base) (by omega) ho hc
  unfold walkSem
  rw [hK, hO, hD, hC]
  rcases (by omega : w.base = 0 ∨ w.base = 1) with h0 | h1
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem walkTag_small {kind odd d cd : ℕ} (hk : kind < 4) (ho : odd < 2) (hc : cd < 64) (hd : d < 64) :
    2 ≤ walkTag kind odd d cd ∧ walkTag kind odd d cd < 2 ^ 16 :=
  ⟨by unfold walkTag; omega, walkTag_lt hk ho hc hd⟩

/-- **An `ext` relation is its tagged tuples of cells**, on the frame's argument words. -/
theorem spec_iff (hG : G.sem = globSem) {sp : XSpec} {na : ℕ} (hs : specOk na sp = true)
    {rd : Reader} :
    (∀ s ∈ semOfSpec sp, Check.SemRel G s.1 rd (s.2.map (Backend.wd L fp))) ↔
      sp.Holds rd (Backend.frameWords L fp 2 na) := by
  cases sp with
  | gkr =>
      simp only [specOk, decide_eq_true_eq] at hs
      simp only [semOfSpec, List.mem_singleton, forall_eq, List.map_cons, List.map_nil,
        XSpec.Holds, frameWords_getD (show 3 < na by omega), frameWords_getD (show 0 < na by omega),
        frameWords_getD (show 2 < na by omega), frameWords_getD (show 9 < na by omega)]
      rw [semRel_plain hG (by unfold tagGkr; norm_num) (by decide),
        globSem_big (by decide) (by decide), ite_eq_left rfl]
      rfl
  | loop w =>
      simp only [specOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hs
      obtain ⟨⟨⟨⟨⟨h4, hb⟩, ho⟩, hc⟩, hd⟩, hbo⟩ := hs
      obtain ⟨h2, h16⟩ := walkTag_small (kind := w.base) (odd := w.odd) (by omega) ho hc hd
      simp only [semOfSpec, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, List.map_cons, List.map_nil, XSpec.Holds,
        frameWords_getD (show 3 < na by omega), frameWords_getD (show 0 < na by omega),
        frameWords_getD (show 1 < na by omega)]
      rw [semRel_ne, semRel_plain hG (by omega) (by unfold Check.tagNe; omega),
        globSem_big (by omega) (by omega), ite_eq_right (by unfold tagGkr; omega),
        ite_eq_right (by unfold tagTabs; omega), ite_eq_right (by omega), walkSem_loop hb ho hc hbo]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      exact and_comm
  | main w =>
      simp only [specOk, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨⟨⟨⟨h8, hb⟩, ho⟩, hc⟩, hd⟩ := hs
      obtain ⟨h2, h16⟩ := walkTag_small (kind := 2 + w.base) (odd := w.odd) (by omega) ho hc hd
      simp only [semOfSpec, List.mem_singleton, forall_eq, List.map_cons, List.map_nil, XSpec.Holds,
        frameWords_getD (show 6 < na by omega), frameWords_getD (show 7 < na by omega)]
      rw [semRel_plain hG (by omega) (by unfold Check.tagNe; omega),
        globSem_big (by omega) (by omega), ite_eq_right (by unfold tagGkr; omega),
        ite_eq_right (by unfold tagTabs; omega), ite_eq_right (by omega), walkSem_main hb ho hc]
  | lq n w =>
      simp only [specOk, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨⟨⟨⟨⟨h6, hb⟩, ho⟩, hc⟩, hd⟩, hn⟩ := hs
      obtain ⟨hW, hN⟩ := lqTag_decode (n := n) hb ho hc hd
      obtain ⟨hK, hO, hD, hC⟩ := walkTag_decode (kind := 2 + w.base) (by omega) ho hc
      have hl : 2 ^ 21 < lqTag n w.odd w.base w.d w.cd := by
        have := walkTag_small (kind := 2 + w.base) (odd := w.odd) (by omega) ho hc hd
        unfold lqTag; omega
      have hlt : lqTag n w.odd w.base w.d w.cd < 2 ^ 31 := by
        have := walkTag_small (kind := 2 + w.base) (odd := w.odd) (by omega) ho hc hd
        unfold lqTag; omega
      simp only [semOfSpec, List.mem_singleton, forall_eq, List.map_cons, List.map_nil, XSpec.Holds]
      rw [semRel_plain hG hlt (by unfold Check.tagNe; omega), globSem_big (by omega) (by omega),
        ite_eq_right (by unfold tagGkr; omega), ite_eq_right (by unfold tagTabs; omega), ite_eq_left (by omega)]
      unfold lqSem
      rw [hW, hN, hK, hO, hD, hC, Nat.add_sub_cancel_left, frameWords_getD (show 5 < na by omega)]
      rfl

/-! ## The two directions -/

theorem frameWords_length {n : ℕ} : (Backend.frameWords L fp 2 n).length = n := by
  simp [Backend.frameWords]

theorem bnd_mono {x : E} {m n : ℕ} (h : Obl.Bnd x m) (hmn : m ≤ n) : Obl.Bnd x n := by
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨e, lt_of_lt_of_le he hmn, rfl⟩

/-- A word read through a frame cell, with its bound: what `Check.MemPre` asks of one entry. -/
theorem memPre_one_iff {o c n : ℕ} :
    (∃ p, L.read (fp * addressOfIndex o) = some p ∧ IsInK p ∧
      ∃ e < n, L.read (p.limb 0 * addressOfIndex c) = some (ofK (addressOfIndex e))) ↔
      ∃ e < n, LoadHolds L.read (Backend.wd L fp o) c (ofK (addressOfIndex e)) := by
  constructor
  · rintro ⟨p, hp, hK, e, he, hr⟩
    refine ⟨e, he, ?_⟩
    rw [Backend.wd, hp]
    exact ⟨hK, hr⟩
  · rintro ⟨e, he, hl⟩
    refine ⟨_, read_of_wd rfl (ne_zero_of_load hl), hl.1, e, he, hl.2⟩

/-- **The certificate's precondition gives `guestU`** of the frame's argument words. -/
theorem u_of_cert (hG : G.sem = globSem) {cs : Check.Sig} {f : String}
    (hok : sigOk cs (guestTab.sig f) (xSpecOf f) = true)
    (hb : Check.BndHolds L fp cs.pre) (hm : Check.MemPre L fp cs.mem)
    (hs : Check.SemHolds G L fp cs.sem) :
    guestU L.read f (Backend.frameWords L fp 2 cs.nargs) := by
  simp only [sigOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hpb⟩, hmb⟩, hxb⟩, heb⟩ := hok
  refine ⟨⟨fun q hq hl => ?_, fun q hq hl => ?_, fun q hq hl => ?_⟩, fun hext s hsp => ?_⟩
  · rw [frameWords_length] at hl
    rw [frameWords_getD hl]
    have := hpb q hq
    simp only [preBack, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨p, hp, h1, h2⟩ := this
    have := hb p hp
    rw [h1] at this
    exact bnd_mono (bnd_of_read this) h2
  · rw [frameWords_length] at hl
    rw [frameWords_getD hl]
    have := hmb q hq
    simp only [memBack, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at this
    rcases this with ⟨m, hmm, ⟨h1, h2⟩, h3⟩ | ⟨s, hss, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩
    · obtain ⟨e, he, hl'⟩ := memPre_one_iff.mp (hm m hmm)
      rw [h1, h2] at hl'
      intro v hv
      exact ⟨e, lt_of_lt_of_le he h3, B1.loadHolds_unique hv hl'⟩
    · have hw := (semRel_wins hG h2).mp (by have := hs s hss; rw [h1] at this; exact this)
      have hd : walkD s.1 = (walkD s.1 - walkCd s.1) + walkCd s.1 := by omega
      rw [hd] at hw
      intro v hv
      exact bnd_mono (winsAt_mem hw h4 v hv) h5
  · rw [frameWords_length] at hl
    rw [frameWords_getD hl]
    have := hxb q hq
    simp only [xpreBack, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem,
      List.any_eq_true, decide_eq_true_eq] at this
    rcases this with ((⟨h0, hc⟩ | ⟨h1, hc⟩) | ⟨hw, hc⟩) | ⟨m, hmm, ⟨h1, h2⟩, h3⟩
    · rw [h0]
      exact guestRel_zero.mpr ((semRel_zero hG).mp (hs _ hc))
    · rw [h1]
      exact guestRel_one.mpr ((semRel_tabs hG).mp (hs _ hc))
    · exact (guestRel_wins hw).mpr ((semRel_wins hG hw).mp (hs _ hc))
    · rw [← h3]
      have := memPre_one_iff.mp (hm m hmm)
      rw [h1] at this
      exact guestRel_memRel h2 this
  · unfold extBack at heb
    rw [hext] at heb
    simp only [Bool.not_true, Bool.false_or] at heb
    rw [hsp] at heb
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at heb
    exact (spec_iff hG heb.1).mp fun t ht => hs t (heb.2 t ht)

/-- **`guestU` of the frame's argument words gives the certificate's precondition**: its bounds,
its reads and its relations. -/
theorem cert_of_u (hG : G.sem = globSem) {cs : Check.Sig} {f : String}
    (hok : sigOk cs (guestTab.sig f) (xSpecOf f) = true)
    (hU : guestU L.read f (Backend.frameWords L fp 2 cs.nargs)) :
    Check.BndHolds L fp cs.pre ∧ Check.MemPre L fp cs.mem ∧ Check.SemHolds G L fp cs.sem := by
  simp only [sigOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hpc, hmc⟩, hsc⟩, -⟩, -⟩, -⟩, -⟩ := hok
  obtain ⟨⟨hpre, -, hxpre⟩, hext⟩ := hU
  refine ⟨fun p hp => ?_, fun m hm => ?_, fun s hs => ?_⟩
  · have := hpc p hp
    simp only [preCov, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨q, hq, ⟨h1, h2⟩, h3⟩ := this
    have hb := hpre q hq (by rw [frameWords_length]; exact h2)
    rw [frameWords_getD h2, h1] at hb
    obtain ⟨e, he, hr⟩ := read_of_bnd hb
    exact ⟨e, lt_of_lt_of_le he h3, hr⟩
  · have := hmc m hm
    simp only [memCov, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨hn, q, hq, ⟨h1, h2⟩, h3⟩ := this
    have hx := hxpre q hq (by rw [frameWords_length]; exact h2)
    rw [frameWords_getD h2, h1, h3] at hx
    exact memPre_one_iff.mpr ((guestRel_memRel_iff hn).mp hx)
  · have := hsc s hs
    unfold semCov at this
    rcases Bool.or_eq_true_iff.mp this with h | h
    · obtain ⟨t, cells⟩ := s
      rcases cells with _ | ⟨c, _ | ⟨c', cs'⟩⟩
      · exact absurd h (by simp)
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
          List.contains_iff_mem] at h
        obtain ⟨⟨h2, hlt⟩, ((⟨rfl, hx⟩ | ⟨rfl, hx⟩) | ⟨hw, hx⟩)⟩ := h
        all_goals
          have hr := hxpre _ hx (by rw [frameWords_length]; exact hlt)
          simp only at hr
          rw [frameWords_getD hlt, show c - 2 + 2 = c by omega] at hr
          simp only [List.map_cons, List.map_nil]
        · exact (semRel_zero hG).mpr (guestRel_zero.mp hr)
        · exact (semRel_tabs hG).mpr (guestRel_one.mp hr)
        · exact (semRel_wins hG hw).mpr ((guestRel_wins hw).mp hr)
      · exact absurd h (by simp)
    · unfold specCov at h
      split at h
      · rename_i sp hsp
        simp only [Bool.and_eq_true, List.contains_iff_mem] at h
        obtain ⟨⟨he, hok⟩, hmem⟩ := h
        exact (spec_iff hG hok).mpr (hext he sp hsp) s hmem
      · exact absurd h (by simp)

end
end LeanVM.Guest.Backend.B2
