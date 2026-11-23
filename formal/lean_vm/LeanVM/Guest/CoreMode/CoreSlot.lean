/-
  LeanVM.Guest.CoreMode.CoreSlot

  A mode signature's facts at a frame and the heap signature's at the slots' words: a product over
  frame cells `2 + b` is the cell over slot `b`'s word where those cells hold the slots' words.
-/

module

public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.CoreMode.HeapCSound

/-!
# Mode facts and heap cells over slots

A mode signature names cells by products of frame cells (`Mode.Mono`, bases `.fr o`), a heap
signature by products of slots (`CCell`, slot `b` the word `ws[b]`): parameters, then returned words.
At a frame whose cells `2 + b` hold the slots' words (`SlotEq`: where written; `SlotGet`: written),
`monoC` translates one to the other: `HW` is `WrK` of the cell's address (`hw_slot`, `slot_hw`), a run
of constant bounds `RW` is its heap run written (`rw_slot`, `slot_rw`), its points too (`ptIn_slot`,
`pts_slot`). The words come from the reference (`rd_getA`: a memory agreeing with it).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (St Fine refMem maxCells Mem gpow_inj Mem.get_of_written Agree refRd_img)
open LeanVM.Guest.Mode (Names written_mono MonoVal BsVal BaseVal IdxVal HW RW)

@[expose] public section

variable {κ : ℕ}

/-- The executor's word at a cell of a memory agreeing with the reference is the reference's. -/
theorem rd_getA {img : MemoryImage κ} (hκ : κ ≤ 28) {m : Mem} (ha : Agree m (refMem img)) {fp : ℕ}
    (hfp : fp < maxCells) {o : ℕ} (ho : o < 2 ^ 28) {u v : E} (hr : Rd img fp o = some v)
    (hg : m.get (fp + o) = some u) : u = v := by
  have h1 := ha.get _ _ hg
  unfold maxCells at hfp
  have h2 := (refRd_img hκ img (fp + o) v (by omega) (by rw [pow_add]; exact hr)).2
  rw [← h1, h2]

theorem monoC_spec {m : Mode.Mono} {c : CCell} (h : monoC m = some c) :
    m.fp = 0 ∧ ∃ cb, m.bs.mapM baseOfMono = some cb ∧ c = ⟨cb, m.k⟩ := by
  unfold monoC monoF at h
  split_ifs at h with h0
  obtain ⟨cb, hcb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨h0, cb, hcb, rfl⟩

/-- Frame cells `2 + b` of the bases hold the slots' words where written. -/
def SlotEq (s : St) (ws : List E) (bs : List (Mode.Base × ℕ)) : Prop :=
  ∀ b ∈ bs, ∃ o, b.1 = .fr o ∧ 2 ≤ o ∧ ∀ u, s.mem.get (s.fp + o) = some u → u = slotW ws (o - 2)

/-- Frame cells `2 + b` of the bases hold the slots' words. -/
def SlotGet (s : St) (ws : List E) (bs : List (Mode.Base × ℕ)) : Prop :=
  ∀ b ∈ bs, ∃ o, b.1 = .fr o ∧ 2 ≤ o ∧ s.mem.get (s.fp + o) = some (slotW ws (o - 2))

theorem SlotGet.eq {s : St} {ws : List E} {bs : List (Mode.Base × ℕ)} (h : SlotGet s ws bs) : SlotEq s ws bs :=
  fun b hb ↦ let ⟨o, h1, h2, h3⟩ := h b hb
  ⟨o, h1, h2, fun _ hu ↦ Option.some.inj (hu.symm.trans h3)⟩

theorem bsVal_slot {s : St} {ws : List E} : ∀ (bs : List (Mode.Base × ℕ)) (cb : List (ℕ × ℕ)),
    bs.mapM baseOfMono = some cb → SlotEq s ws bs → ∀ w, BsVal s bs w → w = prodW (slotW ws) cb
  | [], cb, h, _, w, hw => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simpa [BsVal, prodW] using hw
  | (b, e) :: bs, cb, h, hc, w, hw => by
    obtain ⟨o, hb, h2, hget⟩ := hc (b, e) List.mem_cons_self
    simp only at hb
    subst hb
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    simp only [baseOfMono] at hx
    split_ifs at hx
    cases hx
    obtain ⟨u, w', hu, hw', rfl⟩ := hw
    rw [hget u hu, bsVal_slot bs xs hxs (fun b hb ↦ hc b (List.mem_cons_of_mem _ hb)) w' hw']
    rfl

theorem bsVal_slot' {s : St} {ws : List E} : ∀ (bs : List (Mode.Base × ℕ)) (cb : List (ℕ × ℕ)),
    bs.mapM baseOfMono = some cb → SlotGet s ws bs → BsVal s bs (prodW (slotW ws) cb)
  | [], cb, h, _ => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp [BsVal, prodW]
  | (b, e) :: bs, cb, h, hc => by
    obtain ⟨o, hb, h2, hget⟩ := hc (b, e) List.mem_cons_self
    simp only at hb
    subst hb
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    simp only [baseOfMono] at hx
    split_ifs at hx
    cases hx
    exact ⟨_, _, hget, bsVal_slot' bs xs hxs (fun b hb ↦ hc b (List.mem_cons_of_mem _ hb)), rfl⟩

theorem monoVal_slot {s : St} {ws : List E} {m : Mode.Mono} {c : CCell} (hm : monoC m = some c)
    (hc : SlotEq s ws m.bs) {v : E} (h : MonoVal s m v) : v = c.valW (slotW ws) := by
  obtain ⟨h0, cb, hcb, rfl⟩ := monoC_spec hm
  obtain ⟨w, hw, rfl⟩ := h
  rw [bsVal_slot m.bs cb hcb hc w hw, h0]
  simp only [pow_zero, one_mul, CCell.valW]
  ring

theorem monoVal_slot' {s : St} {ws : List E} {m : Mode.Mono} {c : CCell} (hm : monoC m = some c)
    (hc : SlotGet s ws m.bs) : MonoVal s m (c.valW (slotW ws)) := by
  obtain ⟨h0, cb, hcb, rfl⟩ := monoC_spec hm
  refine ⟨_, bsVal_slot' m.bs cb hcb hc, ?_⟩
  rw [h0]
  simp only [pow_zero, one_mul, CCell.valW, addressOfIndex]
  ring

theorem wrk_names {m : Mem} {v : E} {x : ℕ} (hn : Names v x) (hw : m.written x = true) : WrK m (v.limb 0) :=
  ⟨x, hn.1, hn.2, hw⟩

theorem names_wrk {m : Mem} {v : E} (h : WrK m (v.limb 0)) : ∃ x, Names v x ∧ m.written x = true :=
  let ⟨x, h1, h2, h3⟩ := h
  ⟨x, ⟨h1, h2⟩, h3⟩

/-- **A product written is its cell's address written.** -/
theorem hw_slot {s : St} {ws : List E} {m : Mode.Mono} {c : CCell} (hm : monoC m = some c)
    (hc : SlotEq s ws m.bs) (h : HW s m) : WrK s.mem (c.addrW (slotW ws)) := by
  obtain ⟨v, x, hv, hx, hw⟩ := h
  rw [monoVal_slot hm hc hv] at hx
  exact wrk_names hx hw

theorem slot_hw {s : St} {ws : List E} {m : Mode.Mono} {c : CCell} (hm : monoC m = some c)
    (hc : SlotGet s ws m.bs) (h : WrK s.mem (c.addrW (slotW ws))) : HW s m := by
  obtain ⟨x, hx, hw⟩ := names_wrk h
  exact ⟨_, x, monoVal_slot' hm hc, hx, hw⟩

theorem addr_mod (n : ℕ) : addressOfIndex (n % (2 ^ 64 - 1)) = addressOfIndex n := by
  show Parameters.g ^ _ = Parameters.g ^ _
  rw [← orderOf_g, pow_mod_orderOf]

theorem rngC_spec {r : Mode.Rng} {q : CRun} (h : rngC r = some q) :
    ∃ a b c t o, r.lo = .num a ∧ r.hi = .num b ∧ a - t < 2 ^ 62 ∧ b - t < 2 ^ 62 ∧ monoC r.q = some c ∧ t ≤ a ∧
      addressOfIndex o = addressOfIndex (c.off + r.d + r.S * t) ∧
      q = ⟨⟨c.bases, o⟩, r.S, .num (a - t), .num (b - t)⟩ := by
  unfold rngC at h
  split at h
  · rename_i a b hlo hhi
    simp only [Bool.cond_eq_ite, Bool.and_eq_true, decide_eq_true_eq] at h
    split_ifs at h with hab
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    split_ifs with hd
    · exact ⟨a, b, c, 0, c.off + r.d, hlo, hhi, by omega, by omega, hc, Nat.zero_le _, by simp, by simp⟩
    · exact ⟨a, b, c, a, (c.off + r.d + r.S * a) % (2 ^ 64 - 1), hlo, hhi, by omega, by omega, hc, le_rfl,
        addr_mod _, by simp⟩
  · cases h

theorem valW_shiftc {w : ℕ → E} (c : CCell) (d : ℕ) :
    (⟨c.bases, c.off + d⟩ : CCell).valW w = c.valW w * ofK (addressOfIndex d) := by
  simp only [CCell.valW, addressOfIndex, pow_add, ofK_mul]
  ring

theorem runSet_const {w : ℕ → E} {q : CRun} {a b : ℕ} (hlo : q.lo = .num a) (hhi : q.hi = .num b)
    (ha : a < 2 ^ 62) (hb : b < 2 ^ 62) {x : K} :
    q.Set w x ↔ ∃ j, a ≤ j ∧ j < b ∧ x = (q.base.valW w * ofK (addressOfIndex (q.stride * j))).limb 0 := by
  have ha' : a < capE := by rw [capE_eq]; exact ha
  have hb' : b < capE := by rw [capE_eq]; exact hb
  unfold CRun.Set RunSet
  rw [hlo, hhi]
  simp only [idxC, rep_const ha', rep_const hb', Option.some.injEq]
  constructor
  · rintro ⟨ylo, yhi, j, rfl, rfl, h1, h2, h3⟩
    exact ⟨j, h1, h2, h3⟩
  · rintro ⟨j, h1, h2, h3⟩
    exact ⟨a, b, j, rfl, rfl, h1, h2, h3⟩

/-- **A run of constant bounds written is its heap run's cells written.** -/
theorem rw_slot {s : St} {ws : List E} {r : Mode.Rng} {q : CRun} (hr : rngC r = some q)
    (hc : SlotEq s ws r.q.bs) (h : RW s r) : ∀ x, q.Set (slotW ws) x → WrK s.mem x := by
  obtain ⟨a, b, c, t, o, hlo, hhi, ha, hb, hmc, ht, ho, rfl⟩ := rngC_spec hr
  intro x hx
  obtain ⟨j, h1, h2, rfl⟩ := (runSet_const rfl rfl (by omega) (by omega)).mp hx
  obtain ⟨vq, xlo, xhi, hv, hil, hih, hall⟩ := h
  rw [hlo] at hil
  rw [hhi] at hih
  simp only [IdxVal] at hil hih
  subst hil hih
  obtain ⟨y, hy, hw⟩ := hall (j + t) (by omega) (by omega)
  rw [monoVal_slot hmc hc hv] at hy
  have : (c.valW (slotW ws) * ofK (g ^ (r.S * (j + t) + r.d))) =
      ((⟨c.bases, o⟩ : CCell).valW (slotW ws) * ofK (addressOfIndex (r.S * j))) := by
    simp only [CCell.valW, ho]
    simp only [addressOfIndex, pow_add, mul_add, ofK_mul]
    ring
  rw [this] at hy
  exact wrk_names hy hw

theorem slot_rw {s : St} {ws : List E} {r : Mode.Rng} {q : CRun} (hr : rngC r = some q)
    (hc : SlotGet s ws r.q.bs) (h : ∀ x, q.Set (slotW ws) x → WrK s.mem x) : RW s r := by
  obtain ⟨a, b, c, t, o, hlo, hhi, ha, hb, hmc, ht, ho, rfl⟩ := rngC_spec hr
  refine ⟨_, a, b, monoVal_slot' hmc hc, by rw [hlo]; rfl, by rw [hhi]; rfl, fun j h1 h2 ↦ ?_⟩
  have hx := h _ ((runSet_const (q := ⟨⟨c.bases, o⟩, r.S, .num (a - t), .num (b - t)⟩) rfl rfl (by omega)
    (by omega)).mpr ⟨j - t, by omega, by omega, rfl⟩)
  have : (c.valW (slotW ws) * ofK (g ^ (r.S * j + r.d))) =
      ((⟨c.bases, o⟩ : CCell).valW (slotW ws) * ofK (addressOfIndex (r.S * (j - t)))) := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + t := ⟨j - t, by omega⟩
    simp only [Nat.add_sub_cancel, CCell.valW, ho]
    simp only [addressOfIndex, pow_add, mul_add, ofK_mul]
    ring
  rw [this]
  exact names_wrk hx

/-- **A stride-one run made of the mode signature's runs** (`runCov`), each of them written: its cells written. -/
theorem rw_cov {s : St} {ws : List E} {G : Mode.Sig} {np : ℕ} {q : CRun} (h : runCov G np q = true)
    (hc : ∀ r ∈ G.preR, monoS G np false r.q = true → SlotEq s ws r.q.bs) (hw : ∀ r ∈ G.preR, RW s r) :
    ∀ x, q.Set (slotW ws) x → WrK s.mem x := by
  unfold runCov at h
  split at h
  · rename_i m hlo hhi
    simp only [Bool.and_eq_true, Nat.beq_eq, List.any_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq] at h
    obtain ⟨⟨hS1, hm⟩, r0, -, ⟨hpos, hmod⟩, hall⟩ := h
    intro x hx
    obtain ⟨j, -, hj, rfl⟩ := (runSet_const hlo hhi (by norm_num) hm).mp hx
    obtain ⟨r, hr, hmS, hri⟩ := hall (j % r0.S) (Nat.mod_lt _ hpos)
    unfold rngIs at hri
    split at hri
    · rename_i q' hq'
      obtain rfl := of_decide_eq_true hri
      have hdvd : r0.S ∣ m := Nat.dvd_of_mod_eq_zero hmod
      have hk : j / r0.S < m / r0.S := Nat.div_lt_div_of_lt_of_dvd hdvd hj
      refine rw_slot hq' (hc r hr hmS) (hw r hr) _ ((runSet_const rfl rfl (by norm_num)
        (lt_of_le_of_lt (Nat.div_le_self _ _) hm)).mpr ⟨j / r0.S, Nat.zero_le _, hk, ?_⟩)
      have hj' : j = j % r0.S + r0.S * (j / r0.S) := (Nat.mod_add_div j r0.S).symm
      simp only [strand, CCell.valW, hS1, one_mul]
      conv_lhs => rw [hj']
      simp only [addressOfIndex, pow_add, ofK_mul]
      ring_nf
    · cases hri
  · cases h

theorem runPts_spec {r : Mode.Rng} {l : List CCell} (h : runPts ⟨[], 0⟩ r = some l) :
    ∃ a b, r.lo = .num a ∧ r.hi = .num b ∧ ∀ p, p ∈ l ↔ ∃ j, a ≤ j ∧ j < b ∧ p = ⟨[], r.S * j + r.d⟩ := by
  unfold runPts at h
  split at h
  · rename_i a b hlo hhi
    cases h
    refine ⟨a, b, hlo, hhi, fun p ↦ ⟨fun hp ↦ ?_, fun ⟨j, h1, h2, hp⟩ ↦ ?_⟩⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
      exact ⟨a + k, by omega, by simp at hk; omega, by simp⟩
    · exact List.mem_map.mpr ⟨j - a, List.mem_range.mpr (by omega), by rw [hp]; simp [show a + (j - a) = j by omega]⟩
  · cases h

theorem pt_val {w : ℕ → E} (c : CCell) (S j d : ℕ) :
    (⟨c.bases, c.off + (⟨[], S * j + d⟩ : CCell).off⟩ : CCell).valW w = c.valW w * ofK (g ^ (S * j + d)) := by
  simp only [CCell.valW, addressOfIndex, pow_add, ofK_mul]
  ring

/-- **A point of a written run of constant bounds is written.** -/
theorem ptIn_slot {s : St} {ws : List E} {c : CCell} {r : Mode.Rng} (hp : ptIn c r = true)
    (hc : SlotEq s ws r.q.bs) (h : RW s r) : WrK s.mem (c.addrW (slotW ws)) := by
  unfold ptIn at hp
  split at hp
  · rename_i l q hl hq
    obtain ⟨p, hpl, hpe⟩ := List.any_eq_true.mp hp
    obtain ⟨a, b, hlo, hhi, hmem⟩ := runPts_spec hl
    obtain ⟨j, h1, h2, rfl⟩ := (hmem p).mp hpl
    rw [← CCell.beq_eq hpe]
    obtain ⟨vq, xlo, xhi, hv, hil, hih, hall⟩ := h
    rw [hlo] at hil
    rw [hhi] at hih
    simp only [IdxVal] at hil hih
    subst hil hih
    obtain ⟨y, hy, hw⟩ := hall j h1 h2
    rw [monoVal_slot hq hc hv, ← pt_val] at hy
    exact wrk_names hy hw
  · cases hp

/-- **A run of constant bounds whose points are written is written.** -/
theorem pts_slot {s : St} {ws : List E} {r : Mode.Rng} {c : CCell} {l : List CCell} (hmc : monoC r.q = some c)
    (hl : runPts ⟨[], 0⟩ r = some l) (hc : SlotGet s ws r.q.bs)
    (h : ∀ p ∈ l, WrK s.mem ((⟨c.bases, c.off + p.off⟩ : CCell).addrW (slotW ws))) : RW s r := by
  obtain ⟨a, b, hlo, hhi, hmem⟩ := runPts_spec hl
  refine ⟨_, a, b, monoVal_slot' hmc hc, by rw [hlo]; rfl, by rw [hhi]; rfl, fun j h1 h2 ↦ ?_⟩
  have hx := h _ ((hmem _).mpr ⟨j, h1, h2, rfl⟩)
  rw [CCell.addrW, pt_val] at hx
  exact names_wrk hx

/-! ## Where the slots' words come from -/

/-- **At a frame agreeing with the reference**, whose cells `2 + b` hold slot `b`'s word in the
reference for `b < n`, a product over those slots: `SlotEq`. -/
theorem slotEq_of {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img))
    (hfp : s.fp < maxCells) {ws : List E} {n : ℕ} (hws : ∀ b < n, Rd img s.fp (2 + b) = some (slotW ws b))
    {G : Mode.Sig} {ent : Bool} {m : Mode.Mono} (hm : monoS G n ent m = true) : SlotEq s ws m.bs := by
  intro b hb
  have h := List.all_eq_true.mp hm b hb
  rcases hb1 : b.1 with o | ⟨q, d⟩
  · rw [hb1] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h2, hn⟩, h28⟩, -⟩ := h
    refine ⟨o, rfl, h2, fun u hu ↦ rd_getA hκ ha hfp h28 ?_ hu⟩
    have := hws (o - 2) hn
    rwa [show 2 + (o - 2) = o by omega] at this
  · rw [hb1] at h
    cases h

/-- **At a frame agreeing with the reference** whose entry cells are written, a product over the
entry cells of the slots below `n`: `SlotGet`. -/
theorem slotGet_of {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img))
    (hfp : s.fp < maxCells) {ws : List E} {n : ℕ} (hws : ∀ b < n, Rd img s.fp (2 + b) = some (slotW ws b))
    {G : Mode.Sig} (hw : ∀ o ∈ G.entry, s.mem.written (s.fp + o) = true) {m : Mode.Mono}
    (hm : monoS G n true m = true) : SlotGet s ws m.bs := by
  intro b hb
  have h := List.all_eq_true.mp hm b hb
  rcases hb1 : b.1 with o | ⟨q, d⟩
  · rw [hb1] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h
    obtain ⟨⟨⟨h2, hn⟩, h28⟩, hent⟩ := h
    obtain ⟨u, hu⟩ := Mem.get_of_written (hw o hent)
    refine ⟨o, rfl, h2, ?_⟩
    rw [hu, rd_getA hκ ha hfp h28 (by have := hws (o - 2) hn; rwa [show 2 + (o - 2) = o by omega] at this) hu]
  · rw [hb1] at h
    cases h

/-- **At a return**, a product over parameters' entry cells and returned words' return cells, all
written: `SlotGet`. -/
theorem slotGet_ret {img : MemoryImage κ} (hκ : κ ≤ 28) {s : St} (ha : Agree s.mem (refMem img))
    (hfp : s.fp < maxCells) {ws : List E} {np nr : ℕ} (hws : ∀ b < np + nr, Rd img s.fp (2 + b) = some (slotW ws b))
    {G : Mode.Sig} (hw : ∀ o ∈ G.entry, s.mem.written (s.fp + o) = true)
    (hr : ∀ o ∈ G.ret, s.mem.written (s.fp + o) = true) {m : Mode.Mono}
    (hm : monoR G np nr m = true) : SlotGet s ws m.bs := by
  intro b hb
  have h := List.all_eq_true.mp hm b hb
  rcases hb1 : b.1 with o | ⟨q, d⟩
  · rw [hb1] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.contains_iff_mem] at h
    obtain ⟨⟨h2, h28⟩, h⟩ := h
    have hwo : s.mem.written (s.fp + o) = true ∧ o - 2 < np + nr := by
      rcases h with ⟨h1, h3⟩ | ⟨⟨⟨-, h1⟩, h3⟩⟩
      · exact ⟨hw o h3, by omega⟩
      · exact ⟨hr o h3, h1⟩
    obtain ⟨u, hu⟩ := Mem.get_of_written hwo.1
    refine ⟨o, rfl, h2, ?_⟩
    rw [hu, rd_getA hκ ha hfp h28 (by have := hws (o - 2) hwo.2; rwa [show 2 + (o - 2) = o by omega] at this) hu]
  · rw [hb1] at h
    cases h

end

end LeanVM.Guest.CoreMode
