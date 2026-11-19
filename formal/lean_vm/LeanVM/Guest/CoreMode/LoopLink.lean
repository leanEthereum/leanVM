/-
  LeanVM.Guest.CoreMode.LoopLink

  A loop helper's runs over its caller's cells (`.hp 1 d`): each such cell's word a ghost slot, the caller's
  frame address another, and its runs at a frame as the heap runs over them.
-/

module

public import LeanVM.Guest.CoreMode.CoreLink
public import LeanVM.Guest.CoreMode.LoopSig

/-!
# A loop helper's caller's cells

A loop helper's mode signature may ask a run over a word of its caller's frame (`.hp 1 d`): every iteration's
header names the caller's frame `a` (the tail call copies it), whose cell `d` holds the run's base. The core route
links it (`loopGl np ds`): cell `ds[j]` to ghost slot `np + j` (its word, `LinkW`), and the caller's frame address
(`d = 0`) to ghost slot `np + ds.length`. The heap signature's run over ghost `np + j` (`rngH`) is the mode run;
an address run (`addrRs`), the one cell `a + ds[j]`, says the base's cell is written, which the next iteration's
mode run needs to read its base. The tail call names its own ghosts (`ghostMs`).

At a frame whose header cell is written, agreeing with the reference, the links hold in memory (`LinkM`,
`linkM_of`): a mode run written is its heap run's cells written (`rw_rngH`), and its base's cell is the address
run's (`addr_wrk`); conversely, with the address run's cell written, a heap run's cells written is its mode run
(`rngH_rw`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (St Fine refMem maxCells Mem gpow_inj Mem.get_of_written Agree refRd_img)
open LeanVM.Guest.Mode (Names written_mono MonoVal BsVal BaseVal IdxVal HW RW names_shift)

@[expose] public section

variable {κ : ℕ}

/-! ## The links -/

/-- **A loop's links** (`CFun.gl`): its caller's cells `ds[j]` to ghost slots `np + j`, then the caller's frame
address (`d = 0`) to ghost slot `np + ds.length`. -/
def loopGl (np : ℕ) (ds : List ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range ds.length).map (fun j ↦ (ds.getD j 0, np + j, 0)) ++ [(0, np + ds.length, 0)]

/-- The caller's cells a loop's links name: all but the last link's. -/
def glDs (gl : List (ℕ × ℕ × ℕ)) : List ℕ := gl.dropLast.map (·.1)

/-- **A loop's links and ghost count**: none, or `loopGl np ds` over cells `ds` other than `0`, one ghost per link. -/
def lgOk (np : ℕ) (gl : List (ℕ × ℕ × ℕ)) (ng : ℕ) : Bool :=
  (gl.isEmpty && Nat.beq ng 0) ||
    (decide (gl = loopGl np (glDs gl)) && (glDs gl).all (fun d ↦ !Nat.beq d 0) && Nat.beq ng gl.length)

/-- **A run over one linked caller's cell**, of constant bounds: `[[d]·g^k]·g^(S·j + r.d)`, cell `d ≠ 0` linked to
slot `b` with no power of `g`, as the heap run over slot `b`. -/
def rngH (gl : List (ℕ × ℕ × ℕ)) (r : Mode.Rng) : Option CRun :=
  match r.q.fp, r.q.bs, r.lo, r.hi with
  | 0, [(.hp 1 d, 1)], .num lo, .num hi => match gl.lookup d with
    | some (b, 0) => bif !Nat.beq d 0 && decide (lo < 2 ^ 62) && decide (hi < 2 ^ 62) then
        some ⟨⟨[(b, 1)], r.q.k + r.d⟩, r.S, .num lo, .num hi⟩ else none
    | _ => none
  | _, _, _, _ => none

/-- **A loop's mode run as a heap run**: over a linked caller's cell (`rngH`), or over its parameters (`rngT`). -/
def rngTG (G : Mode.Sig) (np : ℕ) (gl : List (ℕ × ℕ × ℕ)) (r : Mode.Rng) : Option CRun :=
  match rngH gl r with
  | some q => some q
  | none => rngT G np r

/-- **The address runs**: for each linked caller's cell `d`, the one cell at the caller's frame address (ghost slot
`np + ds.length`) times `g^d`. -/
def addrRs (np : ℕ) (gl : List (ℕ × ℕ × ℕ)) : List CRun :=
  (glDs gl).map fun d ↦ ⟨⟨[(np + (glDs gl).length, 1)], d⟩, 1, .num 0, .num 1⟩

/-- **Each linked caller's cell the base of a run of the mode preconditions** (whose word the entry reads). -/
def dsIn (G : Mode.Sig) (gl : List (ℕ × ℕ × ℕ)) : Bool :=
  (glDs gl).all fun d ↦ G.preR.any fun r ↦ decide (r.q.bs = [(.hp 1 d, 1)])

theorem rngTG_nil {G : Mode.Sig} {np : ℕ} (r : Mode.Rng) : rngTG G np [] r = rngT G np r := by
  have : rngH [] r = none := by
    unfold rngH
    split <;> simp
  simp [rngTG, this]

theorem glDs_loopGl (np : ℕ) (ds : List ℕ) : glDs (loopGl np ds) = ds := by
  unfold glDs loopGl
  rw [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, List.map_map]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem lgOk_spec {np : ℕ} {gl : List (ℕ × ℕ × ℕ)} {ng : ℕ} (h : lgOk np gl ng = true) :
    (gl = [] ∧ ng = 0) ∨ (gl = loopGl np (glDs gl) ∧ (∀ d ∈ glDs gl, d ≠ 0) ∧ ng = gl.length) := by
  simp only [lgOk, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff, Nat.beq_eq, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true'] at h
  rcases h with h | ⟨⟨h1, h2⟩, h3⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, fun d hd h0 ↦ ?_, h3⟩
    have := h2 d hd
    rw [h0] at this
    simp at this

/-- The links of `loopGl np ds`: cell `ds[j]` to slot `np + j`, the frame address to slot `np + ds.length`. -/
theorem mem_loopGl {np : ℕ} {ds : List ℕ} {d : ℕ} (hd : d ∈ ds) : ∃ j, (d, np + j, 0) ∈ loopGl np ds := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
  refine ⟨j, List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, ?_⟩)⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem addr_mem_loopGl (np : ℕ) (ds : List ℕ) : (0, np + ds.length, 0) ∈ loopGl np ds :=
  List.mem_append_right _ (List.mem_singleton_self _)

theorem lgOk_ne {np : ℕ} {gl : List (ℕ × ℕ × ℕ)} {ng : ℕ} (h : lgOk np gl ng = true) {d : ℕ} (hd : d ∈ glDs gl) :
    gl = loopGl np (glDs gl) ∧ ∀ d ∈ glDs gl, d ≠ 0 := by
  rcases lgOk_spec h with ⟨rfl, -⟩ | ⟨h1, h2, -⟩
  · simp [glDs] at hd
  · exact ⟨h1, h2⟩

/-- **A loop's word link** of a cell it names: to some slot, with no power of `g`. -/
theorem lgOk_link {np : ℕ} {gl : List (ℕ × ℕ × ℕ)} {ng : ℕ} (h : lgOk np gl ng = true) {d : ℕ} (hd : d ∈ glDs gl) :
    d ≠ 0 ∧ (∃ b, (d, b, 0) ∈ gl) ∧ (0, np + (glDs gl).length, 0) ∈ gl := by
  obtain ⟨h1, h2⟩ := lgOk_ne h hd
  refine ⟨h2 d hd, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := mem_loopGl (np := np) hd
    exact ⟨np + j, h1 ▸ hj⟩
  · rw [h1, glDs_loopGl]
    exact addr_mem_loopGl np _

/-- **A loop's link of a cell other than `0`** is a word link of a cell it names. -/
theorem lgOk_ds {np : ℕ} {gl : List (ℕ × ℕ × ℕ)} {ng : ℕ} (h : lgOk np gl ng = true) {d b k : ℕ}
    (hm : (d, b, k) ∈ gl) (hd : d ≠ 0) : d ∈ glDs gl := by
  rcases lgOk_spec h with ⟨rfl, -⟩ | ⟨h1, -, -⟩
  · cases hm
  · rw [h1] at hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -, -⟩ := he
      have hj' : j < (glDs gl).length := List.mem_range.mp hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
      exact List.getElem_mem _
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      exact absurd hm.1 hd

theorem addrRs_mem {np : ℕ} {gl : List (ℕ × ℕ × ℕ)} {r : CRun} (h : r ∈ addrRs np gl) :
    ∃ d ∈ glDs gl, r = ⟨⟨[(np + (glDs gl).length, 1)], d⟩, 1, .num 0, .num 1⟩ := by
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

theorem ofK_oneL : ofK (1 : K) = 1 := map_one (algebraMap K E)

theorem ofK_gpow_inj {a b : ℕ} (ha : a < maxCells) (hb : b < maxCells) (h : (ofK (g ^ a) : E) = ofK (g ^ b)) :
    a = b := by
  have h' : (g : K) ^ a = g ^ b := by
    have := congrArg (fun x : E ↦ x.limb 0) h
    simpa using this
  unfold maxCells at ha hb
  exact gpow_inj (by omega) (by omega) h'

/-- A run over a caller's cell, unfolded. -/
theorem rngH_spec {gl : List (ℕ × ℕ × ℕ)} {r : Mode.Rng} {q : CRun} (h : rngH gl r = some q) :
    ∃ d b lo hi, r.q = ⟨0, r.q.k, [(.hp 1 d, 1)]⟩ ∧ r.lo = .num lo ∧ r.hi = .num hi ∧ gl.lookup d = some (b, 0) ∧
      d ≠ 0 ∧ lo < 2 ^ 62 ∧ hi < 2 ^ 62 ∧ q = ⟨⟨[(b, 1)], r.q.k + r.d⟩, r.S, .num lo, .num hi⟩ := by
  unfold rngH at h
  split at h
  · rename_i d lo hi hfp hbs hlo hhi
    split at h
    · rename_i b hl
      simp only [Bool.cond_eq_ite, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
      split_ifs at h with hc
      cases h
      obtain ⟨⟨hd, h1⟩, h2⟩ := hc
      refine ⟨d, b, lo, hi, ?_, hlo, hhi, hl, fun h0 ↦ by simp [h0] at hd, h1, h2, rfl⟩
      cases hq : r.q
      rw [hq] at hfp hbs
      simp only at hfp hbs
      subst hfp hbs
      rfl
    · cases h
  · cases h

/-- A run's cell over slot `b` at offset `k + d`, its slot's word `u`. -/
theorem runW_eq {ws : List E} {b k d S j : ℕ} {u : E} (hu : u = slotW ws b * ofK (g ^ 0)) :
    u * ofK (g ^ k) * ofK (g ^ (S * j + d)) =
      (⟨[(b, 1)], k + d⟩ : CCell).valW (slotW ws) * ofK (addressOfIndex (S * j)) := by
  rw [hu]
  simp only [CCell.valW, prodW, addressOfIndex, pow_zero, ofK_oneL, mul_one, pow_one, pow_add, ofK_mul']
  ring

/-- **A mode run over a caller's cell written is its heap run's cells written**, the links in memory. -/
theorem rw_rngH {s : St} {gl : List (ℕ × ℕ × ℕ)} {ws : List E} (hL : LinkM s gl ws) {r : Mode.Rng} {q : CRun}
    (hr : rngH gl r = some q) (h : RW s r) : ∀ x, q.Set (slotW ws) x → WrK s.mem x := by
  obtain ⟨d, b, lo, hi, hq, hlo, hhi, hl, hd0, hlo', hhi', rfl⟩ := rngH_spec hr
  obtain ⟨vq, xlo, xhi, hv, hil, hih, hall⟩ := h
  rw [hlo] at hil
  rw [hhi] at hih
  simp only [IdxVal] at hil hih
  subst xlo xhi
  rw [hq] at hv
  obtain ⟨p, x, u, hp, hx, hu, rfl⟩ := hp_val hv
  obtain ⟨a, ha1, had, hM⟩ := hL d b 0 (lookup_memL hl)
  simp only [hd0, ↓reduceIte] at hM
  have hpa : p = ofK (g ^ a) := Option.some.inj (hp.symm.trans ha1)
  subst hpa
  have hxa : x = a + d := names_uniqL hx (names_shift (by simp) had)
  subst hxa
  have hu' := hM u hu
  intro y hy
  obtain ⟨j, h1, h2, rfl⟩ := (runSet_const (q := ⟨⟨[(b, 1)], r.q.k + r.d⟩, r.S, .num lo, .num hi⟩) rfl rfl
    hlo' hhi').mp hy
  obtain ⟨z, hz, hw⟩ := hall j h1 h2
  have := wrk_names hz hw
  rwa [runW_eq hu'] at this

/-- **The base's cell of a mode run over a caller's cell is written** where the run is, as the address run's cell,
the links in memory. -/
theorem addr_wrk {s : St} {gl : List (ℕ × ℕ × ℕ)} {ws : List E} (hL : LinkM s gl ws) {d b bF k : ℕ}
    (hd : (d, b, 0) ∈ gl) (hF : (0, bF, 0) ∈ gl) {fp' : ℕ} {v : E}
    (hv : MonoVal s ⟨fp', k, [(.hp 1 d, 1)]⟩ v) :
    WrK s.mem ((⟨[(bF, 1)], d⟩ : CCell).addrW (slotW ws)) := by
  obtain ⟨w, ⟨u, w', ⟨p, x, hp, hx, hu⟩, -, -⟩, -⟩ := hv
  obtain ⟨a, ha1, had, -⟩ := hL d b 0 hd
  obtain ⟨a', ha1', had', hF'⟩ := hL 0 bF 0 hF
  simp only [↓reduceIte, pow_zero, ofK_oneL, mul_one] at hF'
  have hpa : p = ofK (g ^ a) := Option.some.inj (hp.symm.trans ha1)
  subst hpa
  have haa : a' = a := ofK_gpow_inj (by omega) (by omega) (Option.some.inj (ha1'.symm.trans ha1))
  subst haa
  have hxa : x = a' + d := names_uniqL hx (names_shift (by simp) had)
  subst hxa
  refine ⟨a' + d, ?_, had, Mode.written_of_get hu⟩
  simp only [CCell.addrW, CCell.valW, prodW, pow_one, mul_one, hF', addressOfIndex, pow_add]
  simp [limb0_mul_ofK]

/-- **A heap run over a caller's cell written is its mode run**, its base's cell written (the address run's), the
links in memory. -/
theorem rngH_rw {s : St} {gl : List (ℕ × ℕ × ℕ)} {ws : List E} (hL : LinkM s gl ws) {r : Mode.Rng} {q : CRun}
    (hr : rngH gl r = some q) {bF : ℕ} (hF : (0, bF, 0) ∈ gl)
    (hA : ∀ d, r.q.bs = [(.hp 1 d, 1)] → WrK s.mem ((⟨[(bF, 1)], d⟩ : CCell).addrW (slotW ws)))
    (h : ∀ x, q.Set (slotW ws) x → WrK s.mem x) : RW s r := by
  obtain ⟨d, b, lo, hi, hq, hlo, hhi, hl, hd0, hlo', hhi', rfl⟩ := rngH_spec hr
  obtain ⟨a, ha1, had, hM⟩ := hL d b 0 (lookup_memL hl)
  simp only [hd0, ↓reduceIte] at hM
  obtain ⟨a', ha1', had', hF'⟩ := hL 0 bF 0 hF
  simp only [↓reduceIte, pow_zero, ofK_oneL, mul_one] at hF'
  have haa : a' = a := ofK_gpow_inj (by omega) (by omega) (Option.some.inj (ha1'.symm.trans ha1))
  subst haa
  obtain ⟨y, hy, hyl, hyw⟩ := hA d (by rw [hq])
  have hy' : y = a' + d := by
    have h1 : (g : K) ^ y = g ^ (a' + d) := by
      rw [← hy]
      simp [CCell.addrW, CCell.valW, prodW, hF', addressOfIndex, pow_add, limb0_mul_ofK]
    unfold maxCells at hyl had
    exact gpow_inj (by omega) (by omega) h1
  subst hy'
  obtain ⟨u, hu⟩ := Mem.get_of_written hyw
  have hu' := hM u hu
  have hv : MonoVal s r.q (u * ofK (g ^ r.q.k)) := by
    rw [hq]
    refine ⟨u, ⟨u, 1, ⟨ofK (g ^ a'), a' + d, ha1, names_shift (by simp) had, hu⟩, rfl, by ring⟩, ?_⟩
    simp only [pow_zero, one_mul]
    ring
  refine ⟨_, lo, hi, hv, by rw [hlo]; rfl, by rw [hhi]; rfl, fun j h1 h2 ↦ ?_⟩
  have hx := h _ ((runSet_const (q := ⟨⟨[(b, 1)], r.q.k + r.d⟩, r.S, .num lo, .num hi⟩) rfl rfl hlo' hhi').mpr
    ⟨j, h1, h2, rfl⟩)
  rw [← runW_eq hu'] at hx
  exact names_wrk hx

end

end LeanVM.Guest.CoreMode
