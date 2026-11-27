/-
  LeanVM.Guest.CoreMode.LoopLink

  A loop helper's runs over its caller's cells (`.hp 1 d`): each such cell's word a slot (a ghost, or a parameter
  the tail call passes on), the caller's frame address a ghost, and its runs at a frame as the heap runs over them.
-/

module

public import LeanVM.Guest.CoreMode.CoreLink
public import LeanVM.Guest.CoreMode.LoopSig

/-!
# A loop helper's caller's cells

A loop helper's mode signature may ask a run over a word of its caller's frame (`.hp 1 d`): every iteration's
header names the caller's frame `a` (the tail call copies it), whose cell `d` holds the run's base or its upper
bound's power of `g`. The core route links such a cell to a slot (`lgOk`; `loopGl np ds`: cell `ds[j]` to ghost slot
`np + j`; or to a parameter the tail call passes on, `sigOkLP`), and the caller's frame address (`d = 0`) to the last
link's slot (`glFs`). The heap signature's run over the base's slot, its upper bound the exponent of the bound's slot
(`hiH`, `rngH`), is the mode run; an address run (`addrRs`), the one cell `a + d`, says the cell is written, which the
next iteration's mode run needs to read it. The tail call names its own ghosts (`ghostMs`).

At a frame whose header cell is written, agreeing with the reference, the links hold in memory (`LinkM`,
`linkM_of`): a mode run written is its heap run's cells written (`rw_rngH`), and its linked cells are the address
runs' (`addr_wrk`); conversely, with the address runs' cells written and the upper bound's exponent at the slots, a
heap run's cells written is its mode run (`rngH_rw`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (St Fine refMem maxCells Mem gpow_inj Mem.get_of_written Agree refRd_img)
open LeanVM.Guest.Mode (Names written_mono MonoVal BsVal BaseVal IdxVal HW RW names_shift)

@[expose] public section

variable {κ : ℕ}

/-! ## The links -/

/-- **A loop's links** (`CFun.gl`) to ghosts: its caller's cells `ds[j]` to ghost slots `np + j`, then the caller's
frame address (`d = 0`) to ghost slot `np + ds.length`. -/
def loopGl (np : ℕ) (ds : List ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range ds.length).map (fun j ↦ (ds.getD j 0, np + j, 0)) ++ [(0, np + ds.length, 0)]

/-- The caller's cells a loop's links name: all but the last link's. -/
def glDs (gl : List (ℕ × ℕ × ℕ)) : List ℕ := gl.dropLast.map (·.1)

/-- **The slot of the caller's frame address**: the last link's. -/
def glFs (gl : List (ℕ × ℕ × ℕ)) : ℕ := (gl.getLast?.map (·.2.1)).getD 0

/-- **A loop's links and ghost count**: none, or links of caller's cells other than `0` (`glDs`, to its parameters or
its ghost slots), then the caller's frame address (`d = 0`) to a slot past the parameters (`glFs`). -/
def lgOk (np : ℕ) (gl : List (ℕ × ℕ × ℕ)) (ng : ℕ) : Bool :=
  (gl.isEmpty && Nat.beq ng 0) ||
    (decide (gl = gl.dropLast ++ [(0, glFs gl, 0)]) && (glDs gl).all (fun d ↦ !Nat.beq d 0) && Nat.ble np (glFs gl))

/-- **A loop run's upper bound over its caller's cells**: a constant below `2^62`, or the exponent of a linked
caller's cell `d ≠ 0` (cell `d` holding slot `b`'s word times `g^k`, the exponent of `ws[b]·g^k`, as `idxL`). -/
def hiH (gl : List (ℕ × ℕ × ℕ)) : Mode.Idx → Option CIdx
  | .num n => bif decide (n < 2 ^ 62) then some (.num n) else none
  | .ex (.hp q d) c => bif Nat.beq q 1 && !Nat.beq d 0 && Nat.beq c 0 then
      (gl.lookup d).map fun p ↦ bif Nat.beq p.2 0 then .val p.1 else .mono ⟨[(p.1, 1)], p.2⟩ else none
  | .ex (.fr _) _ => none

/-- **A run over one linked caller's cell**: `[[d]·g^k]·g^(S·j + r.d)`, cell `d ≠ 0` linked to slot `b` with no power
of `g`, of a constant lower bound and an upper bound `hiH`, as the heap run over slot `b`. -/
def rngH (gl : List (ℕ × ℕ × ℕ)) (r : Mode.Rng) : Option CRun :=
  match r.q.fp, r.q.bs, r.lo, hiH gl r.hi with
  | 0, [(.hp 1 d, 1)], .num lo, some hi => match gl.lookup d with
    | some (b, 0) => bif !Nat.beq d 0 && decide (lo < 2 ^ 62) then
        some ⟨⟨[(b, 1)], r.q.k + r.d⟩, r.S, .num lo, hi⟩ else none
    | _ => none
  | _, _, _, _ => none

/-- **A loop's mode run as a heap run**: over a linked caller's cell (`rngH`), or over its parameters (`rngT`). -/
def rngTG (G : Mode.Sig) (np : ℕ) (gl : List (ℕ × ℕ × ℕ)) (r : Mode.Rng) : Option CRun :=
  match rngH gl r with
  | some q => some q
  | none => rngT G np r

/-- **The address runs**: for each linked caller's cell `d`, the one cell at the caller's frame address (slot
`glFs gl`) times `g^d`. -/
def addrRs (gl : List (ℕ × ℕ × ℕ)) : List CRun :=
  (glDs gl).map fun d ↦ ⟨⟨[(glFs gl, 1)], d⟩, 1, .num 0, .num 1⟩

/-- **Each linked caller's cell the base or the upper bound of a run of the mode preconditions** (whose word the
entry reads). -/
def dsIn (G : Mode.Sig) (gl : List (ℕ × ℕ × ℕ)) : Bool :=
  (glDs gl).all fun d ↦ G.preR.any fun r ↦ decide (r.q.bs = [(.hp 1 d, 1)]) || decide (r.hi = .ex (.hp 1 d) 0)

theorem lgOk_spec {np : ℕ} {gl : List (ℕ × ℕ × ℕ)} {ng : ℕ} (h : lgOk np gl ng = true) :
    (gl = [] ∧ ng = 0) ∨ (gl = gl.dropLast ++ [(0, glFs gl, 0)] ∧ (∀ d ∈ glDs gl, d ≠ 0) ∧ np ≤ glFs gl) := by
  simp only [lgOk, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff, Nat.beq_eq, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true', Nat.ble_eq] at h
  rcases h with h | ⟨⟨h1, h2⟩, h3⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, fun d hd h0 ↦ ?_, h3⟩
    have := h2 d hd
    rw [h0] at this
    simp at this

/-- **A loop's link of a cell it names**, and its caller's frame address's. -/
theorem lgOk_link {np : ℕ} {gl : List (ℕ × ℕ × ℕ)} {ng : ℕ} (h : lgOk np gl ng = true) {d : ℕ} (hd : d ∈ glDs gl) :
    d ≠ 0 ∧ (∃ b k, (d, b, k) ∈ gl) ∧ (0, glFs gl, 0) ∈ gl := by
  rcases lgOk_spec h with ⟨rfl, -⟩ | ⟨h1, h2, -⟩
  · simp [glDs] at hd
  refine ⟨h2 d hd, ?_, ?_⟩
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hd
    exact ⟨l.2.1, l.2.2, List.dropLast_subset _ hl⟩
  · have : (0, glFs gl, 0) ∈ gl.dropLast ++ [(0, glFs gl, 0)] := List.mem_append_right _ (List.mem_singleton_self _)
    rwa [← h1] at this

/-- **A loop's link of a cell other than `0`** is a link of a cell it names. -/
theorem lgOk_ds {np : ℕ} {gl : List (ℕ × ℕ × ℕ)} {ng : ℕ} (h : lgOk np gl ng = true) {d b k : ℕ}
    (hm : (d, b, k) ∈ gl) (hd : d ≠ 0) : d ∈ glDs gl := by
  rcases lgOk_spec h with ⟨rfl, -⟩ | ⟨h1, -, -⟩
  · cases hm
  · rw [h1] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact List.mem_map.mpr ⟨_, hm, rfl⟩
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      exact absurd hm.1 hd

theorem addrRs_mem {gl : List (ℕ × ℕ × ℕ)} {r : CRun} (h : r ∈ addrRs gl) :
    ∃ d ∈ glDs gl, r = ⟨⟨[(glFs gl, 1)], d⟩, 1, .num 0, .num 1⟩ := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
  exact ⟨d, hd, rfl⟩

theorem addr_set {w : ℕ → E} {c : CCell} {x : K} : (⟨c, 1, .num 0, .num 1⟩ : CRun).Set w x ↔ x = c.addrW w := by
  rw [runSet_const rfl rfl (by norm_num) (by norm_num)]
  constructor
  · rintro ⟨j, h1, h2, rfl⟩
    obtain rfl : j = 0 := by omega
    simp [CCell.addrW, addressOfIndex]
  · rintro rfl
    exact ⟨0, le_rfl, by norm_num, by simp [CCell.addrW, addressOfIndex]⟩

/-! ## In memory -/

/-- **The links in memory**: header cell `1` holds `g^a`; a link `(d, b, k)` with `d ≠ 0` has cell `a + d`, where
written, hold slot `b`'s word times `g^k`; the frame address link (`d = 0`) slot `b`'s word times `g^k` `g^a`. -/
def LinkM (s : St) (gl : List (ℕ × ℕ × ℕ)) (ws : List E) : Prop :=
  ∀ d b k, (d, b, k) ∈ gl → ∃ a, s.mem.get (s.fp + 1) = some (ofK (g ^ a)) ∧ a + d < maxCells ∧
    if d = 0 then slotW ws b * ofK (g ^ k) = ofK (g ^ a) else
      ∀ u, s.mem.get (a + d) = some u → u = slotW ws b * ofK (g ^ k)

/-- **The links in memory**, at a frame agreeing with the reference whose header cell is written. -/
theorem linkM_of {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img))
    (hfp : s.fp < maxCells) (hw1 : s.mem.written (s.fp + 1) = true) {gl : List (ℕ × ℕ × ℕ)} {ws : List E}
    (h : GlF img gl s.fp ws) : LinkM s gl ws := by
  intro d b k hm
  obtain ⟨a, h1, had, hL⟩ := h d b k hm
  obtain ⟨p, hp⟩ := Mem.get_of_written hw1
  have hpa : p = ofK (g ^ a) := rd_getA hκ ha hfp (by norm_num) h1 hp
  refine ⟨a, by rw [hp, hpa], had, ?_⟩
  unfold LinkW at hL
  by_cases hd : d = 0
  · simp only [hd, ↓reduceIte] at hL ⊢
    exact hL
  · simp only [hd, ↓reduceIte] at hL ⊢
    intro u hu
    rw [← hL]
    exact (ha.get _ _ hu).symm

theorem ofK_gpow_inj {a b : ℕ} (ha : a < maxCells) (hb : b < maxCells) (h : (ofK (g ^ a) : E) = ofK (g ^ b)) :
    a = b := by
  have h' : (g : K) ^ a = g ^ b := by
    have := congrArg (fun x : E ↦ x.limb 0) h
    simpa using this
  unfold maxCells at ha hb
  exact gpow_inj (by omega) (by omega) h'

/-- A run over a caller's cell, unfolded. -/
theorem rngH_spec {gl : List (ℕ × ℕ × ℕ)} {r : Mode.Rng} {q : CRun} (h : rngH gl r = some q) :
    ∃ d b lo hi, r.q = ⟨0, r.q.k, [(.hp 1 d, 1)]⟩ ∧ r.lo = .num lo ∧ hiH gl r.hi = some hi ∧
      gl.lookup d = some (b, 0) ∧ d ≠ 0 ∧ lo < 2 ^ 62 ∧ q = ⟨⟨[(b, 1)], r.q.k + r.d⟩, r.S, .num lo, hi⟩ := by
  unfold rngH at h
  split at h
  · rename_i d lo hi hfp hbs hlo hhi
    split at h
    · rename_i b hl
      simp only [Bool.cond_eq_ite, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
      split_ifs at h with hc
      cases h
      obtain ⟨hd, h1⟩ := hc
      refine ⟨d, b, lo, hi, ?_, hlo, hhi, hl, fun h0 ↦ by simp [h0] at hd, h1, rfl⟩
      cases hq : r.q
      rw [hq] at hfp hbs
      simp only at hfp hbs
      subst hfp hbs
      rfl
    · cases h
  · cases h

/-- An upper bound `hiH`, unfolded: a constant, or a linked caller's cell's exponent, its index's word slot `b`'s
times `g^k`. -/
theorem hiH_spec {gl : List (ℕ × ℕ × ℕ)} {i : Mode.Idx} {ci : CIdx} (h : hiH gl i = some ci) :
    (∃ n, i = .num n ∧ ci = .num n ∧ n < 2 ^ 62) ∨
      ∃ d b k, i = .ex (.hp 1 d) 0 ∧ d ≠ 0 ∧ gl.lookup d = some (b, k) ∧
        (∀ w : ℕ → E, (idxC ci).valW w = w b * ofK (g ^ k)) ∧ ci.vals = [b] := by
  match i, h with
  | .num n, h =>
    simp only [hiH, Bool.cond_eq_ite, decide_eq_true_eq] at h
    split_ifs at h with hn
    cases h
    exact Or.inl ⟨n, rfl, rfl, hn⟩
  | .ex (.hp q d) c, h =>
    simp only [hiH, Bool.cond_eq_ite, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at h
    split_ifs at h with hc
    obtain ⟨⟨rfl, hd⟩, rfl⟩ := hc
    obtain ⟨⟨b, k⟩, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    refine Or.inr ⟨d, b, k, rfl, fun h0 ↦ by simp [h0] at hd, hl, fun w ↦ ?_, ?_⟩
    · cases k with
      | zero => simp [idxC, valW_baseC]
      | succ k => simp [idxC, CCell.valW, prodW, addressOfIndex]
    · cases k <;> simp [CIdx.vals, CCell.vals]
  | .ex (.fr _) _, h => simp [hiH] at h

/-- The caller's cell `d` of a link, its word slot `b`'s times `g^k`. -/
theorem link_get {s : St} {gl : List (ℕ × ℕ × ℕ)} {ws : List E} (hL : LinkM s gl ws) {d b k : ℕ} (hm : (d, b, k) ∈ gl)
    (hd : d ≠ 0) {u : E} (hu : Mode.BaseVal s (.hp 1 d) u) : u = slotW ws b * ofK (g ^ k) := by
  obtain ⟨p, x, hp, hx, hu⟩ := hu
  obtain ⟨a, ha1, had, hM⟩ := hL d b k hm
  simp only [hd, ↓reduceIte] at hM
  have hpa : p = ofK (g ^ a) := Option.some.inj (hp.symm.trans ha1)
  subst hpa
  have hxa : x = a + d := names_uniqL hx (names_shift (by simp) had)
  subst hxa
  exact hM u hu

/-- **An upper bound `hiH`'s value is its heap index's exponent**, the links in memory. -/
theorem hiH_rep {s : St} {gl : List (ℕ × ℕ × ℕ)} {ws : List E} (hL : LinkM s gl ws) {i : Mode.Idx} {ci : CIdx}
    (h : hiH gl i = some ci) {x : ℕ} (hx : IdxVal s i x) : rep ((idxC ci).valW (slotW ws)) = some x := by
  rcases hiH_spec h with ⟨n, rfl, rfl, hn⟩ | ⟨d, b, k, rfl, hd, hl, hv, -⟩
  · simp only [IdxVal] at hx
    subst hx
    exact rep_const (by rw [capE_eq]; exact hn)
  · obtain ⟨v, e, hbv, rfl, he, rfl⟩ := hx
    rw [hv, ← link_get hL (lookup_memL hl) hd hbv]
    exact rep_of (by rw [capE_eq]; exact he)

/-- **The caller's cell of an address run written**: header cell `1` names the caller's frame `a`, cell `a + d`
written. -/
theorem addr_cell {s : St} {gl : List (ℕ × ℕ × ℕ)} {ws : List E} (hL : LinkM s gl ws) {d b k bF : ℕ}
    (hd : (d, b, k) ∈ gl) (hF : (0, bF, 0) ∈ gl) (hA : WrK s.mem ((⟨[(bF, 1)], d⟩ : CCell).addrW (slotW ws))) :
    ∃ a, s.mem.get (s.fp + 1) = some (ofK (g ^ a)) ∧ a + d < maxCells ∧ s.mem.written (a + d) = true := by
  obtain ⟨a, ha1, had, -⟩ := hL d b k hd
  obtain ⟨a', ha1', had', hF'⟩ := hL 0 bF 0 hF
  simp only [↓reduceIte, pow_zero, ofK_one, mul_one] at hF'
  have haa : a' = a := ofK_gpow_inj (by omega) (by omega) (Option.some.inj (ha1'.symm.trans ha1))
  subst haa
  obtain ⟨y, hy, hyl, hyw⟩ := hA
  have hy' : y = a' + d := by
    have h1 : (g : K) ^ y = g ^ (a' + d) := by
      rw [← hy]
      simp [CCell.addrW, CCell.valW, prodW, hF', addressOfIndex, pow_add, limb0_mul_ofK]
    unfold maxCells at hyl had
    exact gpow_inj (by omega) (by omega) h1
  subst hy'
  exact ⟨a', ha1, had, hyw⟩

/-- **An upper bound `hiH` with an exponent at the slots has its value**, its caller's cell written, the links in
memory. -/
theorem hiH_idx {s : St} {gl : List (ℕ × ℕ × ℕ)} {ws : List E} (hL : LinkM s gl ws) {i : Mode.Idx} {ci : CIdx}
    (h : hiH gl i = some ci)
    (hw : ∀ d, i = .ex (.hp 1 d) 0 → ∃ a, s.mem.get (s.fp + 1) = some (ofK (g ^ a)) ∧ a + d < maxCells ∧
      s.mem.written (a + d) = true)
    {y : ℕ} (hy : rep ((idxC ci).valW (slotW ws)) = some y) : IdxVal s i y := by
  rcases hiH_spec h with ⟨n, rfl, rfl, hn⟩ | ⟨d, b, k, rfl, hd, hl, hv, -⟩
  · rw [idxC, rep_const (by rw [capE_eq]; exact hn), Option.some.injEq] at hy
    exact hy.symm
  · obtain ⟨a, ha1, had, haw⟩ := hw d rfl
    obtain ⟨u, hu⟩ := Mem.get_of_written haw
    have hbv : Mode.BaseVal s (.hp 1 d) u := ⟨_, a + d, ha1, names_shift (by simp) had, hu⟩
    obtain ⟨hyc, hyv⟩ := rep_spec hy
    rw [capE_eq] at hyc
    refine ⟨u, y, hbv, ?_, hyc, rfl⟩
    rw [link_get hL (lookup_memL hl) hd hbv, ← hv, hyv, addressOfIndex]

/-- A run's cell over slot `b` at offset `k + d`, its slot's word `u`. -/
theorem runW_eq {ws : List E} {b k d S j : ℕ} {u : E} (hu : u = slotW ws b * ofK (g ^ 0)) :
    u * ofK (g ^ k) * ofK (g ^ (S * j + d)) =
      (⟨[(b, 1)], k + d⟩ : CCell).valW (slotW ws) * ofK (addressOfIndex (S * j)) := by
  rw [hu]
  simp only [CCell.valW, prodW, addressOfIndex, pow_zero, ofK_one, mul_one, pow_one, pow_add, ofK_mul]
  ring

/-- **A mode run over a caller's cell written is its heap run's cells written**, the links in memory. -/
theorem rw_rngH {s : St} {gl : List (ℕ × ℕ × ℕ)} {ws : List E} (hL : LinkM s gl ws) {r : Mode.Rng} {q : CRun}
    (hr : rngH gl r = some q) (h : RW s r) : ∀ x, q.Set (slotW ws) x → WrK s.mem x := by
  obtain ⟨d, b, lo, hi, hq, hlo, hhi, hl, hd0, hlo', rfl⟩ := rngH_spec hr
  obtain ⟨vq, xlo, xhi, hv, hil, hih, hall⟩ := h
  rw [hlo] at hil
  simp only [IdxVal] at hil
  subst xlo
  have hrh := hiH_rep hL hhi hih
  rw [hq] at hv
  obtain ⟨p, x, u, hp, hx, hu, rfl⟩ := hp_val hv
  have hu' := link_get hL (lookup_memL hl) hd0 ⟨p, x, hp, hx, hu⟩
  intro y hy
  obtain ⟨ylo, yhi, j, h1, h2, h3, h4, rfl⟩ := runSet_iff.mp hy
  simp only [idxC, rep_const (show lo < capE by rw [capE_eq]; exact hlo'), Option.some.injEq] at h1
  rw [hrh, Option.some.injEq] at h2
  subst h1 h2
  obtain ⟨z, hz, hw⟩ := hall j h3 h4
  have := wrk_names hz hw
  rwa [runW_eq hu'] at this

/-- **The base's cell of a mode run over a caller's cell is written** where the run is, as the address run's cell,
the links in memory. -/
theorem addr_wrk {s : St} {gl : List (ℕ × ℕ × ℕ)} {ws : List E} (hL : LinkM s gl ws) {d b bF k : ℕ}
    (hd : (d, b, k) ∈ gl) (hF : (0, bF, 0) ∈ gl) {v : E} (hv : Mode.BaseVal s (.hp 1 d) v) :
    WrK s.mem ((⟨[(bF, 1)], d⟩ : CCell).addrW (slotW ws)) := by
  obtain ⟨p, x, hp, hx, hu⟩ := hv
  obtain ⟨a, ha1, had, -⟩ := hL d b k hd
  obtain ⟨a', ha1', had', hF'⟩ := hL 0 bF 0 hF
  simp only [↓reduceIte, pow_zero, ofK_one, mul_one] at hF'
  have hpa : p = ofK (g ^ a) := Option.some.inj (hp.symm.trans ha1)
  subst hpa
  have haa : a' = a := ofK_gpow_inj (by omega) (by omega) (Option.some.inj (ha1'.symm.trans ha1))
  subst haa
  have hxa : x = a' + d := names_uniqL hx (names_shift (by simp) had)
  subst hxa
  refine ⟨a' + d, ?_, had, Mode.written_of_get hu⟩
  simp only [CCell.addrW, CCell.valW, prodW, pow_one, mul_one, hF', addressOfIndex, pow_add]
  simp [limb0_mul_ofK]

/-- A product over one caller's cell has a word there. -/
theorem baseVal_of_mono {s : St} {fp' k d : ℕ} {v : E} (hv : MonoVal s ⟨fp', k, [(.hp 1 d, 1)]⟩ v) :
    ∃ u, Mode.BaseVal s (.hp 1 d) u := by
  obtain ⟨w, ⟨u, w', hu, -, -⟩, -⟩ := hv
  exact ⟨u, hu⟩

/-- A bound over a base has a word there. -/
theorem baseVal_of_idx {s : St} {b : Mode.Base} {c x : ℕ} (hx : IdxVal s (.ex b c) x) : ∃ u, Mode.BaseVal s b u := by
  obtain ⟨v, -, hv, -⟩ := hx
  exact ⟨v, hv⟩

/-- **A heap run over a caller's cell written is its mode run**, its base's and upper bound's cells written (the
address runs'), its upper bound with an exponent at the slots, the links in memory. -/
theorem rngH_rw {s : St} {gl : List (ℕ × ℕ × ℕ)} {ws : List E} (hL : LinkM s gl ws) {r : Mode.Rng} {q : CRun}
    (hr : rngH gl r = some q) {bF : ℕ} (hF : (0, bF, 0) ∈ gl)
    (hA : ∀ d, (r.q.bs = [(.hp 1 d, 1)] ∨ r.hi = .ex (.hp 1 d) 0) →
      WrK s.mem ((⟨[(bF, 1)], d⟩ : CCell).addrW (slotW ws)))
    (hE : ∃ y, rep ((idxC q.hi).valW (slotW ws)) = some y)
    (h : ∀ x, q.Set (slotW ws) x → WrK s.mem x) : RW s r := by
  obtain ⟨d, b, lo, hi, hq, hlo, hhi, hl, hd0, hlo', rfl⟩ := rngH_spec hr
  obtain ⟨a', ha1, had, hyw⟩ := addr_cell hL (lookup_memL hl) hF (hA d (Or.inl (by rw [hq])))
  obtain ⟨u, hu⟩ := Mem.get_of_written hyw
  have hbv : Mode.BaseVal s (.hp 1 d) u := ⟨_, a' + d, ha1, names_shift (by simp) had, hu⟩
  have hu' := link_get hL (lookup_memL hl) hd0 hbv
  have hv : MonoVal s r.q (u * ofK (g ^ r.q.k)) := by
    rw [hq]
    refine ⟨u, ⟨u, 1, hbv, rfl, by ring⟩, ?_⟩
    simp only [pow_zero, one_mul]
    ring
  obtain ⟨y, hy⟩ := hE
  have hih : IdxVal s r.hi y := hiH_idx hL hhi (fun d' hd' ↦ by
    rcases hiH_spec hhi with ⟨n, hn, -⟩ | ⟨d'', b'', k'', hd'', -, hl'', -⟩
    · rw [hn] at hd'; cases hd'
    · rw [hd''] at hd'
      cases hd'
      exact addr_cell hL (lookup_memL hl'') hF (hA d' (Or.inr hd''))) hy
  refine ⟨_, lo, y, hv, by rw [hlo]; rfl, hih, fun j h1 h2 ↦ ?_⟩
  have hx := h _ (runSet_iff.mpr ⟨lo, y, j, by simp [idxC, rep_const (show lo < capE by rw [capE_eq]; exact hlo')],
    hy, h1, h2, rfl⟩)
  rw [← runW_eq hu'] at hx
  exact names_wrk hx

end

end LeanVM.Guest.CoreMode
