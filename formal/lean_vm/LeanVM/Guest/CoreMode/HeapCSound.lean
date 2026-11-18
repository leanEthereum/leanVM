/-
  LeanVM.Guest.CoreMode.HeapCSound

  The heap check with calls and loops is sound on the path: every event's needs are written
  before it, and the guarantees at return are written.
-/

module

public import LeanVM.Guest.CoreMode.HeapC
public import LeanVM.Guest.CoreMode.HeapSound
public import LeanVM.Guest.Res.LoopTree

/-!
# The heap check with calls and loops is sound

`heapOkC_sound`: for a function passing `heapOkC`, a valuation `σ` whose path returns, its events
holding and each entered call's callee guarantees' runs having their exponents, given its entry
facts (`EntryF`: its preconditions' runs' exponents, its termination facts) and its residuals
(`ResF`): every event's needs are written before it (`ReadsOkC`) and its guarantees at return are
written (`PostOkC`).

The proof follows milestone 1's (`HeapSound.lean`): the pass's state is valid on the path
(`StOk W`: the environment's monomials are the values' words, the scope's cells and runs written in
`W`, the runs' exponents existing), `W` the preconditions and the writes so far; a witness of a cell
or a run gives it written (`ptOk_ok`, `rnOk_ok`, by `ptRun_ok` and `runRun_ok` from the run's
exponents and the facts); a signature at a site is the cells and runs at the slots' words
(`instC_ok`, `MsOk`). A loop's tail (`tailC_ok`) splits on its condition: entered, the next
iteration's guarantees at its words (`EvW`, the same cells when not over the counter, the run from
one further); not entered, the next counter is the end (`Res.loop_path`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq natSeq_eq)
open LeanVM.Guest.Check (getF setF getF_eq setF_eq)

public section

/-! ## Words -/

section Words

variable {w w' : ℕ → E}

theorem prodB_eq (σ : Val) : ∀ l, prodB σ l = prodW (vw σ) l
  | [] => rfl
  | (b, e) :: l => by rw [prodB, prodW, prodB_eq σ l]; rfl

theorem val_eq (σ : Val) (c : CCell) : c.val σ = c.valW (vw σ) := by
  rw [CCell.val, CCell.valW, prodB_eq]

theorem addr_eq (σ : Val) (c : CCell) : c.addr σ = c.addrW (vw σ) := by
  rw [CCell.addr, CCell.addrW, val_eq]

/-- A valuation whose values `V.n k` have the words `w k`. -/
@[expose] def lift (w : ℕ → E) : Val := fun v ↦ w v.idx

theorem vw_lift (w : ℕ → E) : vw (lift w) = w := funext fun _ ↦ rfl

theorem ofK_pow' (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

theorem valW_mul (a b : CCell) : (a.mul b).valW w = a.valW w * b.valW w := by
  have := val_mul (lift w) a b
  rwa [val_eq, val_eq, val_eq, vw_lift] at this

theorem prodW_pow (e : ℕ) : ∀ l : List (ℕ × ℕ), prodW w (l.map fun b ↦ (b.1, b.2 * e)) = prodW w l ^ e
  | [] => by simp [prodW]
  | (b, x) :: l => by
    simp only [List.map_cons, prodW, prodW_pow e l, mul_pow, pow_mul]

theorem valW_pow (c : CCell) (e : ℕ) : (c.pow e).valW w = c.valW w ^ e := by
  rw [CCell.pow, CCell.valW, CCell.valW, prodW_pow, mul_pow, ← ofK_pow', addressOfIndex, addressOfIndex,
    ← pow_mul]

theorem valW_shift (c : CCell) (o : ℕ) : (c.shift o).valW w = c.valW w * ofK (addressOfIndex o) := by
  simp only [CCell.shift, CCell.valW, addressOfIndex, pow_add, ofK_mul', mul_assoc]

theorem valW_baseC (k : ℕ) : (baseC k).valW w = w k := by
  have := val_baseC (lift w) k
  rwa [val_eq, vw_lift] at this

theorem valW_const (n : ℕ) : (⟨[], n⟩ : CCell).valW w = ofK (addressOfIndex n) := by
  simp [CCell.valW, prodW]

theorem valW_nil {c : CCell} (h : c.bases.isEmpty = true) : c.valW w = ofK (addressOfIndex c.off) := by
  obtain ⟨bs, o⟩ := c
  cases bs with
  | nil => exact valW_const o
  | cons _ _ => simp at h

theorem prodW_congr {c : List (ℕ × ℕ)} (h : ∀ b ∈ c, w b.1 = w' b.1) : prodW w c = prodW w' c := by
  induction c with
  | nil => rfl
  | cons b l ih =>
    obtain ⟨b, e⟩ := b
    rw [prodW, prodW, h _ List.mem_cons_self, ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx)]

theorem valW_congr {c : CCell} (h : ∀ b ∈ c.bases, w b.1 = w' b.1) : c.valW w = c.valW w' := by
  rw [CCell.valW, CCell.valW, prodW_congr h]

end Words

/-! ## Exponents -/

section Rep

theorem capE_eq : capE = 2 ^ 62 := by norm_num [capE]

theorem gpow_inj_lt {a b : ℕ} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63)
    (h : ofK (addressOfIndex a) = ofK (addressOfIndex b)) : a = b :=
  gpow_injOn (show a < 2 ^ 64 - 1 by omega) (show b < 2 ^ 64 - 1 by omega) (ofK_injective h)

theorem rep_spec {x : E} {y : ℕ} (h : rep x = some y) : y < capE ∧ x = ofK (addressOfIndex y) := by
  unfold rep at h
  split_ifs at h with hx
  cases h
  exact Classical.choose_spec hx

theorem rep_of {y : ℕ} (hy : y < capE) : rep (ofK (addressOfIndex y)) = some y := by
  have hx : ∃ y', y' < capE ∧ ofK (addressOfIndex y) = ofK (addressOfIndex y') := ⟨y, hy, rfl⟩
  unfold rep
  split_ifs
  obtain ⟨h1, h2⟩ := Classical.choose_spec hx
  have e := capE_eq
  exact congrArg some (gpow_inj_lt (by omega) (by omega) h2).symm

theorem rep_const {w : ℕ → E} {n : ℕ} (h : n < capE) : rep ((⟨[], n⟩ : CCell).valW w) = some n := by
  rw [valW_const, rep_of h]

theorem rep_nil {w : ℕ → E} {c : CCell} (hc : c.bases.isEmpty = true) (h : c.off < capE) :
    rep (c.valW w) = some c.off := by
  rw [valW_nil hc, rep_of h]

/-- The exponent of a word times `g`: one more, while below the bound. -/
theorem rep_succ {x : E} {y : ℕ} (h : rep x = some y) (hy : y + 1 < capE) :
    rep (x * ofK (addressOfIndex 1)) = some (y + 1) := by
  obtain ⟨-, rfl⟩ := rep_spec h
  rw [← ofK_mul', addressOfIndex, addressOfIndex, ← pow_add, ← addressOfIndex, rep_of hy]

end Rep

/-! ## Runs and facts -/

section Runs

variable {w w' : ℕ → E} {W W' : K → Prop}

theorem runSet_congr {b b' lo lo' hi hi' : CCell} {S : ℕ} (hb : b.valW w = b'.valW w')
    (hl : lo.valW w = lo'.valW w') (hh : hi.valW w = hi'.valW w') {x : K} :
    RunSet w b S lo hi x ↔ RunSet w' b' S lo' hi' x := by
  simp only [RunSet, hb, hl, hh]

theorem runF_congr {b b' lo lo' hi hi' : CCell} {S : ℕ} (hb : b.valW w = b'.valW w')
    (hl : lo.valW w = lo'.valW w') (hh : hi.valW w = hi'.valW w') :
    RunF W w b S lo hi ↔ RunF W w' b' S lo' hi' := by
  simp only [RunF, runSet_congr hb hl hh]

theorem RunF.mono {b lo hi : CCell} {S : ℕ} (hw : ∀ x, W x → W' x) (h : RunF W w b S lo hi) :
    RunF W' w b S lo hi :=
  fun x hx ↦ hw x (h x hx)

theorem runSet_of {b lo hi : CCell} {S ylo yhi j : ℕ} (hl : rep (lo.valW w) = some ylo)
    (hh : rep (hi.valW w) = some yhi) (h1 : ylo ≤ j) (h2 : j < yhi) :
    RunSet w b S lo hi ((b.valW w * ofK (addressOfIndex (S * j))).limb 0) :=
  ⟨ylo, yhi, j, hl, hh, h1, h2, rfl⟩

/-- Facts true at `w`. -/
def FOk (w : ℕ → E) (F : List (CCell × CCell)) : Prop := ∀ p ∈ F, LtF w p.1 p.2

theorem hasF_ok {F : List (CCell × CCell)} (hF : FOk w F) {a b : CCell} (h : hasF F a b = true) : LtF w a b := by
  obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hq
  rw [← CCell.beq_eq hq.1, ← CCell.beq_eq hq.2]
  exact hF p hp

theorem hasFC_ok {F : List (CCell × CCell)} (hF : FOk w F) {k : ℕ} {b : CCell} (h : hasFC F k b = true) :
    ∃ yb, rep (b.valW w) = some yb ∧ k < yb := by
  obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hq
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hq
  obtain ⟨ya, yb, ha, hb, hab⟩ := hF p hp
  rw [rep_nil h1 h3, Option.some.injEq] at ha
  rw [CCell.beq_eq h4] at hb
  exact ⟨yb, hb, by omega⟩

/-- **A cell of a run at an index**: `c = base · J^S`, `J` below the upper bound by a fact, past the
lower one. -/
theorem ptIdx_ok {F : List (CCell × CCell)} (hF : FOk w F) {R : PRun}
    (hR : RunF W w R.base R.stride R.lo R.hi) {c J : CCell} (h : ptIdx F R c J = true) : W (c.addrW w) := by
  unfold ptIdx at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨yj, yhi, hyj, hyhi, hab⟩ := hasF_ok hF h2
  have hcap := (rep_spec hyhi).1
  obtain ⟨ylo, hylo, hle⟩ : ∃ ylo, rep (R.lo.valW w) = some ylo ∧ ylo ≤ yj := by
    rcases h3 with (⟨h4, h5⟩ | h4) | h4
    · have h5 := Nat.eq_of_beq_eq_true h5
      have := rep_nil (w := w) h4 (by rw [h5]; norm_num [capE])
      rw [h5] at this
      exact ⟨0, this, Nat.zero_le _⟩
    · exact ⟨yj, by rw [CCell.beq_eq h4]; exact hyj, le_rfl⟩
    · obtain ⟨yl, yj1, hyl, hyj1, hlt⟩ := hasF_ok hF h4
      rw [valW_shift, rep_succ hyj (by omega), Option.some.injEq] at hyj1
      exact ⟨yl, hyl, by omega⟩
  refine hR _ ⟨ylo, yhi, yj, hylo, hyhi, hle, hab, ?_⟩
  rw [CCell.addrW, CCell.beq_eq h1, valW_mul, valW_pow, (rep_spec hyj).2, ← ofK_pow', addressOfIndex,
    addressOfIndex, ← pow_mul, mul_comm yj]

/-- **A cell of a run**: a run written, the facts true, `ptRun` gives the cell written. -/
theorem ptRun_ok {F : List (CCell × CCell)} (hF : FOk w F) {R : PRun}
    (hR : RunF W w R.base R.stride R.lo R.hi) {c : CCell} (h : ptRun F R c = true) : W (c.addrW w) := by
  unfold ptRun at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  rcases Bool.or_eq_true_iff.mp h with h | h
  pick_goal 2
  · exact ptIdx_ok hF hR h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ylo, yhi, hylo, hyhi, hab⟩ := hasF_ok hF h2
    refine hR _ ⟨ylo, yhi, ylo, hylo, hyhi, le_rfl, hab, ?_⟩
    rw [CCell.addrW, CCell.beq_eq h1, valW_mul, valW_pow, (rep_spec hylo).2, ← ofK_pow', addressOfIndex,
      addressOfIndex, ← pow_mul, mul_comm ylo]
  · simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hb, hoff⟩, -⟩, hmod⟩, hlo⟩, hlc⟩, hk⟩, hhi⟩ := h
    have hmod := Nat.eq_of_beq_eq_true hmod
    set k := (c.off - R.base.off) / R.stride with hkdef
    obtain ⟨yhi, hyhi, hlt⟩ : ∃ yhi, rep (R.hi.valW w) = some yhi ∧ k < yhi := by
      rcases hhi with ⟨⟨h1, h2⟩, h3⟩ | h
      · exact ⟨R.hi.off, rep_nil h1 h2, h3⟩
      · exact hasFC_ok hF h
    refine hR _ ⟨R.lo.off, yhi, k, rep_nil hlo hlc, hyhi, hk, hlt, ?_⟩
    have hc : c.off = R.base.off + R.stride * k := by
      rw [hkdef]
      have := Nat.div_add_mod (c.off - R.base.off) R.stride
      omega
    rw [CCell.addrW, CCell.valW, CCell.valW, basesBeq_eq hb, hc, addressOfIndex, addressOfIndex, addressOfIndex,
      pow_add, ofK_mul', mul_assoc]

/-- **A run inside a run**: a run written, the facts true, `runRun` gives the run written. -/
theorem runRun_ok {F : List (CCell × CCell)} (hF : FOk w F) {Q R : PRun}
    (hR : RunF W w R.base R.stride R.lo R.hi) (h : runRun F Q R = true) : RunF W w Q.base Q.stride Q.lo Q.hi := by
  unfold runRun at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hb, hS⟩, hlo⟩, hhi⟩ := h
  have hb := CCell.beq_eq hb
  have hS := Nat.eq_of_beq_eq_true hS
  rintro x ⟨ql, qh, j, hql, hqh, h1, h2, hx⟩
  have lo : ∃ rl, rep (R.lo.valW w) = some rl ∧ rl ≤ ql := by
    unfold loOk at hlo
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hlo
    rcases hlo with (h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨h1, h2⟩
    · exact ⟨ql, by rw [← CCell.beq_eq h]; exact hql, le_rfl⟩
    · rw [rep_nil h1 h4, Option.some.injEq] at hql
      exact ⟨R.lo.off, rep_nil h2 (by omega), by omega⟩
    · obtain ⟨ya, yb, ha, hb', hab⟩ := hasF_ok hF h2
      have := (rep_spec hb').1
      rw [CCell.beq_eq h1, valW_shift, rep_succ ha (by omega), Option.some.injEq] at hql
      exact ⟨ya, ha, by omega⟩
  have hi : ∃ rh, rep (R.hi.valW w) = some rh ∧ qh ≤ rh := by
    unfold hiOk at hhi
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hhi
    rcases hhi with (h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨⟨h1, h2⟩, h3⟩
    · exact ⟨qh, by rw [← CCell.beq_eq h]; exact hqh, le_rfl⟩
    · rw [rep_nil h1 (by omega), Option.some.injEq] at hqh
      exact ⟨R.hi.off, rep_nil h2 h4, by omega⟩
    · obtain ⟨yb, hb', hkb⟩ := hasFC_ok hF h3
      rw [rep_nil h1 h2, Option.some.injEq] at hqh
      exact ⟨yb, hb', by omega⟩
  obtain ⟨rl, hrl, hl⟩ := lo
  obtain ⟨rh, hrh, hh⟩ := hi
  rw [hb, hS] at hx
  exact hR x ⟨rl, rh, j, hrl, hrh, by omega, by omega, hx⟩

end Runs

/-! ## Monomials at a site -/

section Inst

variable {w w' : ℕ → E}

/-- **Slot monomials `ms` naming the slot words `w'`**: each `ms[b]`'s word is `w' b`. -/
def MsOk (w : ℕ → E) (ms : List CCell) (w' : ℕ → E) : Prop := ∀ b m, nth ms b = some m → m.valW w = w' b

theorem instB_ok {ms : List CCell} (h : MsOk w ms w') : ∀ (l : List (ℕ × ℕ)) (acc c' : CCell),
    instB ms l acc = some c' → c'.valW w = acc.valW w * prodW w' l
  | [], acc, c', hc => by
    simp only [instB, Option.some.injEq] at hc
    subst hc
    simp [prodW]
  | (b, e) :: l, acc, c', hc => by
    simp only [instB] at hc
    cases hm : nth ms b with
    | none => rw [hm] at hc; cases hc
    | some m =>
      rw [hm] at hc
      rw [instB_ok h l _ c' hc, valW_mul, valW_pow, h b m hm, prodW]
      ring

theorem instC_ok {ms : List CCell} (h : MsOk w ms w') {c c' : CCell} (hc : instC ms c = some c') :
    c'.valW w = c.valW w' := by
  rw [instB_ok h c.bases ⟨[], c.off⟩ c' hc, valW_const, CCell.valW]
  ring

theorem instI_ok {ms : List CCell} (h : MsOk w ms w') {i : CIdx} {m : CCell} (hi : instI ms i = some m) :
    m.valW w = (idxC i).valW w' := by
  cases i with
  | num n =>
    simp only [instI, Option.some.injEq] at hi
    subst hi
    rw [idxC, valW_const, valW_const]
  | val v => rw [idxC, valW_baseC]; exact h v m hi
  | mono c => rw [idxC]; exact instC_ok h hi

theorem instR_ok {ms : List CCell} (h : MsOk w ms w') {r : CRun} {q : PRun} (hr : instR ms r = some q) :
    q.base.valW w = r.base.valW w' ∧ q.stride = r.stride ∧ q.lo.valW w = (idxC r.lo).valW w' ∧
      q.hi.valW w = (idxC r.hi).valW w' := by
  unfold instR at hr
  cases hb : instC ms r.base with
  | none => simp [hb] at hr
  | some b =>
    cases hl : instI ms r.lo with
    | none => simp [hb, hl] at hr
    | some l =>
      cases hh : instI ms r.hi with
      | none => simp [hb, hl, hh] at hr
      | some hi =>
        simp only [hb, hl, hh, Option.some.injEq] at hr
        subst hr
        exact ⟨instC_ok h hb, rfl, instI_ok h hl, instI_ok h hh⟩

/-- A signature run at a site is written as the pass-level run is. -/
theorem instR_runF {ms : List CCell} (h : MsOk w ms w') {r : CRun} {q : PRun} (hr : instR ms r = some q)
    {W : K → Prop} : RunF W w q.base q.stride q.lo q.hi ↔ r.F W w' := by
  obtain ⟨h1, h2, h3, h4⟩ := instR_ok h hr
  rw [h2]
  exact runF_congr h1 h3 h4

theorem instR_set {ms : List CCell} (h : MsOk w ms w') {r : CRun} {q : PRun} (hr : instR ms r = some q)
    {x : K} : RunSet w q.base q.stride q.lo q.hi x ↔ r.Set w' x := by
  obtain ⟨h1, h2, h3, h4⟩ := instR_ok h hr
  rw [h2]
  exact runSet_congr h1 h3 h4

theorem instAll_ok {ms : List CCell} : ∀ {cs cs' : List CCell}, instAll ms cs = some cs' →
    ∀ c' ∈ cs', ∃ c ∈ cs, instC ms c = some c'
  | [], cs', h, c', hc => by simp only [instAll, Option.some.injEq] at h; subst h; simp at hc
  | c :: cs, cs', h, c', hc => by
    simp only [instAll] at h
    cases h1 : instC ms c with
    | none => simp [h1] at h
    | some c1 =>
      cases h2 : instAll ms cs with
      | none => simp [h1, h2] at h
      | some l =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨c, List.mem_cons_self, h1⟩
        · obtain ⟨d, hd, hd'⟩ := instAll_ok h2 c' hc
          exact ⟨d, List.mem_cons_of_mem _ hd, hd'⟩

theorem instAllR_ok {ms : List CCell} : ∀ {rs : List CRun} {qs : List PRun}, instAllR ms rs = some qs →
    ∀ q ∈ qs, ∃ r ∈ rs, instR ms r = some q
  | [], qs, h, q, hq => by simp only [instAllR, Option.some.injEq] at h; subst h; simp at hq
  | r :: rs, qs, h, q, hq => by
    simp only [instAllR] at h
    cases h1 : instR ms r with
    | none => simp [h1] at h
    | some q1 =>
      cases h2 : instAllR ms rs with
      | none => simp [h1, h2] at h
      | some l =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨r, List.mem_cons_self, h1⟩
        · obtain ⟨d, hd, hd'⟩ := instAllR_ok h2 q hq
          exact ⟨d, List.mem_cons_of_mem _ hd, hd'⟩

theorem nth_append {α : Type} : ∀ (l1 l2 : List α) (b : ℕ),
    nth (l1 ++ l2) b = if b < l1.length then nth l1 b else nth l2 (b - l1.length)
  | [], l2, b => by simp
  | a :: l1, l2, 0 => by simp [nth]
  | a :: l1, l2, b + 1 => by
    simp only [List.cons_append, nth, nth_append l1 l2 b, List.length_cons, Nat.add_lt_add_iff_right,
      Nat.add_sub_add_right]

theorem slotW_append (ws1 ws2 : List E) (b : ℕ) :
    slotW (ws1 ++ ws2) b = if b < ws1.length then slotW ws1 b else slotW ws2 (b - ws1.length) := by
  unfold slotW
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega)]

theorem msOk_append {ms1 ms2 : List CCell} {ws1 ws2 : List E} (h1 : MsOk w ms1 (slotW ws1))
    (h2 : MsOk w ms2 (slotW ws2)) (hl : ms1.length = ws1.length) : MsOk w (ms1 ++ ms2) (slotW (ws1 ++ ws2)) := by
  intro b m hb
  rw [nth_append] at hb
  rw [slotW_append, ← hl]
  split_ifs at hb ⊢
  · exact h1 b m hb
  · exact h2 _ m hb

theorem monos_ok {σ : Val} {env : Trie CCell} (he : EnvOk σ env) : ∀ (vs : List V) (ms : List CCell),
    monos env vs = some ms → MsOk (vw σ) ms (slotW (vs.map σ)) ∧ ms.length = vs.length
  | [], ms, h => by
    simp only [monos, Option.some.injEq] at h
    subst h
    exact ⟨fun b m hm ↦ by simp [nth] at hm, rfl⟩
  | v :: vs, ms, h => by
    simp only [monos] at h
    cases hm : monoOf env v with
    | none => simp [hm] at h
    | some m =>
      cases hms : monos env vs with
      | none => simp [hm, hms] at h
      | some ms' =>
        simp only [hm, hms, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := monos_ok he vs ms' hms
        refine ⟨fun b m' hb ↦ ?_, by simp [h2]⟩
        cases b with
        | zero =>
          simp only [nth, Option.some.injEq] at hb
          subst hb
          rw [← val_eq, ← monoOf_ok he hm]
          rfl
        | succ b =>
          simp only [nth] at hb
          rw [h1 b m' hb]
          rfl

/-- The parameters' words, slot by slot: `V.n b`'s word below their count. -/
theorem slotW_params {σ : Val} {m b : ℕ} (hb : b < m) : slotW ((List.range m).map fun k ↦ σ (V.n k)) b = vw σ b := by
  unfold slotW vw
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hb]

theorem setNth_length {α : Type} : ∀ (l : List α) (n : ℕ) (b : α), (setNth l n b).length = l.length
  | [], _, _ => rfl
  | _ :: l, 0, _ => rfl
  | _ :: l, n + 1, b => by simp [setNth, setNth_length l n b]

theorem nth_setNth {α : Type} : ∀ (l : List α) (n k : ℕ) (b : α),
    nth (setNth l n b) k = if k = n ∧ n < l.length then some b else nth l k
  | [], _, _, _ => by simp [setNth, nth]
  | _ :: l, 0, 0, _ => by simp [setNth, nth]
  | _ :: l, 0, k + 1, _ => by simp [setNth, nth]
  | _ :: l, n + 1, 0, _ => by simp [setNth, nth]
  | _ :: l, n + 1, k + 1, b => by simp [setNth, nth, nth_setNth l n k b]

theorem slotW_setNth : ∀ (l : List E) (n k : ℕ) (b : E),
    slotW (setNth l n b) k = if k = n ∧ n < l.length then b else slotW l k
  | [], _, _, _ => by simp [setNth, slotW]
  | _ :: l, 0, 0, _ => by simp [setNth, slotW]
  | _ :: l, 0, k + 1, _ => by simp [setNth, slotW]
  | _ :: l, n + 1, 0, _ => by simp [setNth, slotW]
  | _ :: l, n + 1, k + 1, b => by
    have := slotW_setNth l n k b
    simp only [slotW] at this ⊢
    rw [setNth, List.getD_cons_succ, List.getD_cons_succ, this]
    simp

theorem msOk_setNth {ms : List CCell} {ws : List E} (h : MsOk w ms (slotW ws)) (hl : ms.length = ws.length)
    {n : ℕ} {m : CCell} {v : E} (hm : m.valW w = v) : MsOk w (setNth ms n m) (slotW (setNth ws n v)) := by
  intro b m' hb
  rw [nth_setNth] at hb
  rw [slotW_setNth, ← hl]
  split_ifs at hb ⊢ with h1
  · cases hb; exact hm
  · exact h b m' hb

end Inst

/-! ## The pass's invariant -/

section Inv

variable {σ : Val} {W W' : K → Prop}

/-- **The run scope is written**: each run's cells are in `W`. -/
def RsOk (W : K → Prop) (σ : Val) (rs : Trie PRun) : Prop :=
  ∀ r R, getF rs r = some R → RunF W (vw σ) R.base R.stride R.lo R.hi

/-- **The sums seen hold**: each value the sum of its operands' monomials' words. -/
def AdOk (σ : Val) (ad : Trie (CCell × CCell)) : Prop :=
  ∀ k p, getF ad k = some p → σ (V.n k) = p.1.valW (vw σ) + p.2.valW (vw σ)

/-- **The state is valid**: its monomials, its written cells and runs, its sums. -/
def StOk (W : K → Prop) (σ : Val) (st : CSt) : Prop :=
  EnvOk σ st.env ∧ ScOk W σ st.sc ∧ RsOk W σ st.rs ∧ AdOk σ st.ad

theorem StOk.mono (hw : ∀ x, W x → W' x) {st : CSt} (h : StOk W σ st) : StOk W' σ st :=
  ⟨h.1, h.2.1.mono hw, fun r R hr ↦ (h.2.2.1 r R hr).mono hw, h.2.2.2⟩

theorem StOk.cnt {st : CSt} (h : StOk W σ st) (s : CSt) : StOk W σ (st.cnt s) := h

theorem StOk.nextC {st : CSt} (h : StOk W σ st) : StOk W σ st.nextC := h

theorem StOk.nextT {st : CSt} (h : StOk W σ st) : StOk W σ st.nextT := h

theorem CSt.seq_eq {β : Type} (st : CSt) (k : CSt → β) : st.seq k = k st := by
  simp only [CSt.seq, Trie.seq_eq, natSeq_eq]

theorem PRun.seq_eq {β : Type} (r : PRun) (k : PRun → β) : r.seq k = k r := by
  simp only [PRun.seq, CCell.seq_eq, natSeq_eq]

theorem push_stOk {st : CSt} (hs : StOk W σ st) (hw : ∀ x, W x → W' x) {c : CCell} (hc : W' (c.addr σ)) :
    StOk W' σ (st.push c) := by
  obtain ⟨he, hsc, hrs, had⟩ := hs
  obtain ⟨h1, h2⟩ := push_ok (W := W') (st := st.toH) (hsc.mono hw) hc
  exact ⟨by rw [CSt.push, CSt.ofH]; exact h1 ▸ he, h2, fun r R hr ↦ (hrs r R hr).mono hw, had⟩

theorem pushL_ok : ∀ {W W' : K → Prop} {cs : List CCell} {st : CSt}, StOk W σ st → (∀ x, W x → W' x) →
    (∀ c ∈ cs, W' (c.addr σ)) → StOk W' σ (pushL cs st)
  | _, _, [], _, hs, hw, _ => hs.mono hw
  | _, _, c :: cs, st, hs, hw, hc => by
    rw [pushL, CCell.seq_eq, CSt.seq_eq]
    exact pushL_ok (push_stOk hs hw (hc c List.mem_cons_self)) (fun _ h ↦ h)
      fun c' h ↦ hc c' (List.mem_cons_of_mem _ h)

theorem pushR_stOk {st : CSt} (hs : StOk W σ st) (hw : ∀ x, W x → W' x) {q : PRun}
    (hq : RunF W' (vw σ) q.base q.stride q.lo q.hi) : StOk W' σ (st.pushR q) := by
  obtain ⟨he, hsc, hrs, had⟩ := hs
  unfold CSt.pushR
  rw [Trie.seq_eq]
  refine ⟨he, hsc.mono hw, fun r R hr ↦ ?_, had⟩
  change getF (setF q Exec.indexDepth st.rs st.nr) r = some R at hr
  rcases getF_setF hr with ⟨-, rfl⟩ | hr
  · exact hq
  · exact (hrs r R hr).mono hw

theorem pushRL_ok : ∀ {W W' : K → Prop} {qs : List PRun} {st : CSt}, StOk W σ st → (∀ x, W x → W' x) →
    (∀ q ∈ qs, RunF W' (vw σ) q.base q.stride q.lo q.hi) → StOk W' σ (pushRL qs st)
  | _, _, [], _, hs, hw, _ => hs.mono hw
  | _, _, q :: qs, st, hs, hw, hq => by
    rw [pushRL, PRun.seq_eq, CSt.seq_eq]
    exact pushRL_ok (pushR_stOk hs hw (hq q List.mem_cons_self)) (fun _ h ↦ h)
      fun q' h ↦ hq q' (List.mem_cons_of_mem _ h)

/-- **What the pass reads, valid**: milestone 1's, the signatures, the parameters, the residuals,
and the facts true at the instance. -/
structure XOk (sigOf : String → HSig) (H : HCert) (f : Fn) (σ : Val) (X : CX) : Prop where
  R : X.R = H.readT
  pre : ∀ k c, getF X.pre k = some c → c ∈ H.sig.pre
  pows : X.pows.Ok
  sigOf : X.sigOf = sigOf
  sig : X.sig = H.sig
  params : X.params = f.params
  res : ∀ i c, getF X.res i = some c → c ∈ H.res
  term : ∀ p ∈ H.sig.term, LtF (vw σ) (idxC p.1) (idxC p.2)
  resF : ResF H σ

theorem idxF_val {env : Trie CCell} (he : EnvOk σ env) (i : CIdx) : (idxF env i).valW (vw σ) = (idxC i).valW (vw σ) := by
  cases i with
  | num n => rfl
  | val k =>
    rw [idxC, valW_baseC, idxF]
    cases hk : getF env k with
    | none => rw [Option.getD_none, valW_baseC]
    | some c => rw [Option.getD_some, ← val_eq, ← he k c hk]; rfl
  | mono c => rfl

theorem ltF_congr {w w' : ℕ → E} {a a' b b' : CCell} (ha : a.valW w = a'.valW w') (hb : b.valW w = b'.valW w') :
    LtF w a b ↔ LtF w' a' b' := by
  simp only [LtF, ha, hb]

theorem facts_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H f σ X)
    {env : Trie CCell} (he : EnvOk σ env) (res : List ℕ) : FOk (vw σ) (facts X env res) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [hX.sig] at hq
    exact (ltF_congr (idxF_val he _) (idxF_val he _)).mpr (hX.term q hq)
  · obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hp
    cases hr : getF X.res i with
    | none => rw [hr] at hi; cases hi
    | some c =>
      rw [hr] at hi
      cases c with
      | lt a b =>
        cases hi
        exact (ltF_congr (idxF_val he _) (idxF_val he _)).mpr (hX.resF a b (hX.res i _ hr))
      | nz => cases hi
      | sub => cases hi

/-- **A cell's witness**: the cell written. -/
theorem ptOk_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H f σ X)
    (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk W σ st) {c : CCell} {w : Wit}
    (h : ptOk X st c w = true) : W (c.addr σ) := by
  cases w with
  | ev n =>
    simp only [ptOk] at h
    cases hn : getF st.sc n with
    | none => rw [hn] at h; cases h
    | some c' => rw [hn] at h; rw [← CCell.beq_eq h]; exact hs.2.1 n c' hn
  | pre k =>
    simp only [ptOk] at h
    cases hk : getF X.pre k with
    | none => rw [hk] at h; cases h
    | some c' => rw [hk] at h; rw [← CCell.beq_eq h]; exact hpre c' (hX.pre k c' hk)
  | run r res =>
    simp only [ptOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      rw [addr_eq]
      exact ptRun_ok (facts_ok hX hs.1 res) (hs.2.2.1 r R hr) h
  | res => simp [ptOk] at h

/-- **A run's witness**: the run written. -/
theorem rnOk_ok {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} (hX : XOk sigOf H f σ X)
    {st : CSt} (hs : StOk W σ st) {Q : PRun} {w : Wit} (h : rnOk X st Q w = true) :
    RunF W (vw σ) Q.base Q.stride Q.lo Q.hi := by
  cases w with
  | run r res =>
    simp only [rnOk] at h
    cases hr : getF st.rs r with
    | none => rw [hr] at h; cases h
    | some R =>
      rw [hr] at h
      exact runRun_ok (facts_ok hX hs.1 res) (hs.2.2.1 r R hr) h
  | ev => simp [rnOk] at h
  | pre => simp [rnOk] at h
  | res => simp [rnOk] at h

variable {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX}

theorem reqP_ok (hX : XOk sigOf H f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk W σ st)
    {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {cs : List CCell} {wl wl' : List Wit}, reqP X st ms cs wl = some wl' → ∀ c ∈ cs, W (c.addrW (slotW ws))
  | [], _, _, _, c, hc => by simp at hc
  | c :: cs, [], _, h, _, _ => by simp [reqP] at h
  | c :: cs, w :: wl, wl', h, c0, hc0 => by
    simp only [reqP] at h
    cases hi : instC ms c with
    | none => rw [hi] at h; cases h
    | some c' =>
      simp only [hi] at h
      cases hp : ptOk X st c' w with
      | false => rw [hp] at h; cases h
      | true =>
        rw [hp, Bool.cond_true] at h
        rcases List.mem_cons.mp hc0 with rfl | hc0
        · have := ptOk_ok hX hpre hs hp
          rwa [addr_eq, CCell.addrW, instC_ok hms hi] at this
        · exact reqP_ok hX hpre hs hms h c0 hc0

theorem reqR_ok (hX : XOk sigOf H f σ X) {st : CSt} (hs : StOk W σ st)
    {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {rs : List CRun} {wl wl' : List Wit}, reqR X st ms rs wl = some wl' → ∀ r ∈ rs, r.F W (slotW ws)
  | [], _, _, _, r, hr => by simp at hr
  | r :: rs, [], _, h, _, _ => by simp [reqR] at h
  | r :: rs, w :: wl, wl', h, r0, hr0 => by
    simp only [reqR] at h
    cases hi : instR ms r with
    | none => rw [hi] at h; cases h
    | some q =>
      simp only [hi] at h
      cases hp : rnOk X st q w with
      | false => rw [hp] at h; cases h
      | true =>
        rw [hp, Bool.cond_true] at h
        rcases List.mem_cons.mp hr0 with rfl | hr0
        · exact (instR_runF hms hi).mp (rnOk_ok hX hs hp)
        · exact reqR_ok hX hs hms h r0 hr0

theorem reqS_ok (hX : XOk sigOf H f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk W σ st)
    {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) {G : HSig} {wl wl' : List Wit}
    (h : reqS X st ms G wl = some wl') : SigOk W G.pre G.preR ws := by
  unfold reqS at h
  cases h1 : reqP X st ms G.pre wl with
  | none => rw [h1] at h; cases h
  | some wl1 =>
    rw [h1] at h
    exact ⟨reqP_ok hX hpre hs hms h1, reqR_ok hX hs hms h⟩

theorem reqArms_ok (hX : XOk sigOf H f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt}
    (hs : StOk W σ st) {ms : List CCell} {ws : List E} (hms : MsOk (vw σ) ms (slotW ws)) :
    ∀ {gs : List String} {wl wl' : List Wit}, reqArms X st ms gs wl = some wl' →
      ∀ g ∈ gs, SigOk W (sigOf g).pre (sigOf g).preR ws
  | [], _, _, _, g, hg => by simp at hg
  | g :: gs, wl, wl', h, g0, hg0 => by
    simp only [reqArms] at h
    cases h1 : reqS X st ms (X.sigOf g) wl with
    | none => rw [h1] at h; cases h
    | some wl1 =>
      rw [h1] at h
      rcases List.mem_cons.mp hg0 with rfl | hg0
      · rw [← hX.sigOf]; exact reqS_ok hX hpre hs hms h1
      · exact reqArms_ok hX hpre hs hms h g0 hg0

end Inv

/-! ## Covered events -/

section Cov

variable {sigOf : String → HSig} {H : HCert} {σ : Val} {rd : Reader}

/-- An address an event of `es` writes. -/
def EW (sigOf : String → HSig) (σ : Val) (es : List Ev) (x : K) : Prop := ∃ e ∈ es, EvW sigOf σ e x

/-- **The needs of `es` are covered**: each event's in `W` or written by the events before it. -/
def CovC (sigOf : String → HSig) (H : HCert) (σ : Val) (W : K → Prop) (es : List Ev) : Prop :=
  ∀ es1 e es2, es = es1 ++ e :: es2 → ReqOk sigOf H σ (fun x ↦ W x ∨ EW sigOf σ es1 x) e

/-- The events hold. -/
def EvsOk (_sigOf : String → HSig) (rd : Reader) (σ : Val) (es : List Ev) : Prop := ∀ e ∈ es, e.Holds rd σ

/-- The own guarantees written in `W` at the parameters' words `ws0` and the returned `vs`. -/
def PostW (_sigOf : String → HSig) (H : HCert) (σ : Val) (ws0 : List E) (W : K → Prop) (vs : List V) : Prop :=
  SigOk W H.sig.post H.sig.postR (ws0 ++ vs.map σ)

theorem SigOk.mono {W W' : K → Prop} (hw : ∀ x, W x → W' x) {cs : List CCell} {rs : List CRun} {ws : List E}
    (h : SigOk W cs rs ws) : SigOk W' cs rs ws :=
  ⟨fun c hc ↦ hw _ (h.1 c hc), fun r hr ↦ (h.2 r hr).mono hw⟩

theorem ReqOk.mono {W W' : K → Prop} (hw : ∀ x, W x → W' x) : ∀ {e : Ev}, ReqOk sigOf H σ W e →
    ReqOk sigOf H σ W' e
  | .atom _, h => fun x hx ↦ hw x (h x hx)
  | .call .., h => SigOk.mono hw h
  | .inK _, _ => trivial
  | .skip .., _ => trivial

theorem CovC.mono {W W' : K → Prop} (hw : ∀ x, W x → W' x) {es : List Ev} (h : CovC sigOf H σ W es) :
    CovC sigOf H σ W' es :=
  fun es1 e es2 he ↦ (h es1 e es2 he).mono fun x hx ↦ hx.imp_left (hw x)

theorem covC_nil (W : K → Prop) : CovC sigOf H σ W [] := fun es1 _ _ he ↦ by simp at he

theorem ew_append_left {es1 es2 : List Ev} {x : K} (h : EW sigOf σ es1 x) : EW sigOf σ (es1 ++ es2) x :=
  let ⟨e, he, hx⟩ := h
  ⟨e, List.mem_append_left _ he, hx⟩

theorem ew_append_right {es1 es2 : List Ev} {x : K} (h : EW sigOf σ es2 x) : EW sigOf σ (es1 ++ es2) x :=
  let ⟨e, he, hx⟩ := h
  ⟨e, List.mem_append_right _ he, hx⟩

theorem ew_append {es1 es2 : List Ev} {x : K} (h : EW sigOf σ (es1 ++ es2) x) :
    EW sigOf σ es1 x ∨ EW sigOf σ es2 x := by
  obtain ⟨e, he, hx⟩ := h
  rcases List.mem_append.mp he with he | he
  · exact Or.inl ⟨e, he, hx⟩
  · exact Or.inr ⟨e, he, hx⟩

theorem covC_append {W : K → Prop} {es1 es2 : List Ev} (h1 : CovC sigOf H σ W es1)
    (h2 : CovC sigOf H σ (fun x ↦ W x ∨ EW sigOf σ es1 x) es2) : CovC sigOf H σ W (es1 ++ es2) := by
  intro p e q he
  rcases List.append_eq_append_iff.mp he with ⟨a', rfl, h⟩ | ⟨c', rfl, h⟩
  · refine (h2 a' e q h).mono fun x hx ↦ ?_
    rcases hx with (hx | hx) | hx
    · exact Or.inl hx
    · exact Or.inr (ew_append_left hx)
    · exact Or.inr (ew_append_right hx)
  · cases c' with
    | nil =>
      simp only [List.nil_append] at h
      refine (h2 [] e q (by rw [← h]; rfl)).mono fun x hx ↦ ?_
      rcases hx with hx | ⟨_, hb, _⟩
      · simpa using hx
      · simp at hb
    | cons e' c'' =>
      rw [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact h1 p e c'' rfl

theorem covC_single {W : K → Prop} {e : Ev} (h : ReqOk sigOf H σ W e) : CovC sigOf H σ W [e] := by
  intro p b q he
  cases p with
  | nil =>
    rw [List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact h.mono fun x hx ↦ Or.inl hx
  | cons _ p => simp at he

theorem evsOk_append {es1 es2 : List Ev} (h : EvsOk sigOf rd σ (es1 ++ es2)) :
    EvsOk sigOf rd σ es1 ∧ EvsOk sigOf rd σ es2 :=
  ⟨fun e he ↦ h e (List.mem_append_left _ he), fun e he ↦ h e (List.mem_append_right _ he)⟩

/-- **What an outcome gives**: its needs covered; returning, the own guarantees written. -/
def OutC (sigOf : String → HSig) (H : HCert) (σ : Val) (rd : Reader) (ws0 : List E) (W : K → Prop) (o : Out) :
    Prop :=
  (∀ es, o = .fall es → EvsOk sigOf rd σ es → CovC sigOf H σ W es) ∧
  (∀ es vs, o = .ret es vs → EvsOk sigOf rd σ es →
    CovC sigOf H σ W es ∧ PostW sigOf H σ ws0 (fun x ↦ W x ∨ EW sigOf σ es x) vs)

/-- **What a block's pass gives on the path**: its outcome's, and, falling through, the state at
its end valid. -/
def BlockC (sigOf : String → HSig) (H : HCert) (σ : Val) (rd : Reader) (ws0 : List E) (W : K → Prop) (o : Out)
    (st' : CSt) : Prop :=
  OutC sigOf H σ rd ws0 W o ∧
    ∀ es, o = .fall es → EvsOk sigOf rd σ es → StOk (fun x ↦ W x ∨ EW sigOf σ es x) σ st'

theorem PostW.mono {ws0 : List E} {W W' : K → Prop} (hw : ∀ x, W x → W' x) {vs : List V}
    (h : PostW sigOf H σ ws0 W vs) : PostW sigOf H σ ws0 W' vs := SigOk.mono hw h

theorem outC_pre {ws0 : List E} {W : K → Prop} {o : Out} (h : OutC sigOf H σ rd ws0 W o) (c : V) :
    OutC sigOf H σ rd ws0 W (o.pre [.inK c]) := by
  have key : ∀ es', CovC sigOf H σ W es' → CovC sigOf H σ W ([Ev.inK c] ++ es') := fun es' hc ↦
    covC_append (covC_single trivial) (hc.mono fun _ ↦ Or.inl)
  have hew : ∀ es' x, (W x ∨ EW sigOf σ es' x) → (W x ∨ EW sigOf σ ([Ev.inK c] ++ es') x) := fun es' x hx ↦
    hx.imp_right ew_append_right
  refine ⟨fun es hw hh ↦ ?_, fun es vs hw hh ↦ ?_⟩
  · cases o with
    | fall es' =>
      simp only [Out.pre, Out.fall.injEq] at hw
      subst hw
      exact key es' (h.1 es' rfl (evsOk_append hh).2)
    | ret => simp [Out.pre] at hw
    | stuck => simp [Out.pre] at hw
  · cases o with
    | ret es' vs' =>
      simp only [Out.pre, Out.ret.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨h1, h2⟩ := h.2 es' vs' rfl (evsOk_append hh).2
      exact ⟨key es' h1, h2.mono (hew es')⟩
    | fall => simp [Out.pre] at hw
    | stuck => simp [Out.pre] at hw

/-- **A statement, then a block.** -/
theorem blockC_seq {ws0 : List E} {W : K → Prop} {o1 : Out} {ss : List Stmt} {st' : CSt}
    {W1 : List Ev → K → Prop} (h1 : OutC sigOf H σ rd ws0 W o1)
    (h2 : ∀ es, o1 = .fall es → EvsOk sigOf rd σ es →
      (∀ x, W1 es x → W x ∨ EW sigOf σ es x) ∧ BlockC sigOf H σ rd ws0 (W1 es) (walk σ ss) st') :
    BlockC sigOf H σ rd ws0 W (o1.seq (walk σ ss)) st' := by
  cases o1 with
  | fall es1 =>
    have hW : ∀ es2 x, EvsOk sigOf rd σ es1 → (W1 es1 x ∨ EW sigOf σ es2 x) →
        (W x ∨ EW sigOf σ (es1 ++ es2) x) := fun es2 x hh hx ↦ by
      rcases hx with hx | hx
      · rcases (h2 es1 rfl hh).1 x hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (ew_append_left hx)
      · exact Or.inr (ew_append_right hx)
    have hcov : ∀ es2, EvsOk sigOf rd σ (es1 ++ es2) → CovC sigOf H σ (W1 es1) es2 →
        CovC sigOf H σ W (es1 ++ es2) := fun es2 hh hc ↦
      covC_append (h1.1 es1 rfl (evsOk_append hh).1)
        (hc.mono fun x hx ↦ (h2 es1 rfl (evsOk_append hh).1).1 x hx)
    refine ⟨⟨fun es hw hh ↦ ?_, fun es vs hw hh ↦ ?_⟩, fun es hw hh ↦ ?_⟩
    · simp only [Out.seq] at hw
      cases hk : walk σ ss with
      | fall es2 =>
        rw [hk] at hw
        simp only [Out.pre, Out.fall.injEq] at hw
        subst hw
        exact hcov es2 hh ((h2 es1 rfl (evsOk_append hh).1).2.1.1 es2 hk (evsOk_append hh).2)
      | ret => rw [hk] at hw; simp [Out.pre] at hw
      | stuck => rw [hk] at hw; simp [Out.pre] at hw
    · simp only [Out.seq] at hw
      cases hk : walk σ ss with
      | ret es2 vs2 =>
        rw [hk] at hw
        simp only [Out.pre, Out.ret.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨hc, hp⟩ := (h2 es1 rfl (evsOk_append hh).1).2.1.2 es2 vs2 hk (evsOk_append hh).2
        exact ⟨hcov es2 hh hc, hp.mono fun x hx ↦ hW es2 x (evsOk_append hh).1 hx⟩
      | fall => rw [hk] at hw; simp [Out.pre] at hw
      | stuck => rw [hk] at hw; simp [Out.pre] at hw
    · simp only [Out.seq] at hw
      cases hk : walk σ ss with
      | fall es2 =>
        rw [hk] at hw
        simp only [Out.pre, Out.fall.injEq] at hw
        subst hw
        exact ((h2 es1 rfl (evsOk_append hh).1).2.2 es2 hk (evsOk_append hh).2).mono
          fun x hx ↦ hW es2 x (evsOk_append hh).1 hx
      | ret => rw [hk] at hw; simp [Out.pre] at hw
      | stuck => rw [hk] at hw; simp [Out.pre] at hw
  | ret es1 vs1 =>
    refine ⟨⟨fun es hw _ ↦ by simp [Out.seq] at hw, fun es vs hw hh ↦ ?_⟩, fun es hw _ ↦ by simp [Out.seq] at hw⟩
    simp only [Out.seq, Out.ret.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact h1.2 es1 vs1 rfl hh
  | stuck =>
    exact ⟨⟨fun es hw _ ↦ by simp [Out.seq] at hw, fun es vs hw _ ↦ by simp [Out.seq] at hw⟩,
      fun es hw _ ↦ by simp [Out.seq] at hw⟩

end Cov

/-! ## Statements -/

section Stmts

variable {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} {σ : Val} {rd : Reader} {W : K → Prop}

theorem atomC_other {st : CSt} {a : Atom} (hl : ∀ d p off, a ≠ .load d p off) (ha : ∀ d x y, a ≠ .add d x y) :
    atomC X st a = (atomH X.toH st.toH a).map st.ofH := by
  cases a <;> first | rfl | exact absurd rfl (hl _ _ _) | exact absurd rfl (ha _ _ _)

theorem addS_fields (st : CSt) (k : ℕ) (a b : CCell) :
    (st.addS k a b).env = st.env ∧ (st.addS k a b).sc = st.sc ∧ (st.addS k a b).rs = st.rs := by
  unfold CSt.addS
  cases getF st.ad k <;> simp [Trie.seq_eq]

theorem addS_adOk {σ : Val} {st : CSt} (had : AdOk σ st.ad) {k : ℕ} {a b : CCell}
    (h : σ (V.n k) = a.valW (vw σ) + b.valW (vw σ)) : AdOk σ (st.addS k a b).ad := by
  unfold CSt.addS
  cases hk : getF st.ad k with
  | some _ => exact had
  | none =>
    simp only [Trie.seq_eq]
    intro k' p hp
    rcases getF_setF hp with ⟨rfl, rfl⟩ | hp
    · exact h
    · exact had k' p hp

/-- **An atom of the path**: its reads in `W`, the state after it valid with its writes. -/
theorem atomC_ok (hX : XOk sigOf H f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt} {a : Atom}
    (h : atomC X st a = some st') (hs : StOk W σ st) (ha : a.Holds rd σ) :
    (∀ x, Reads H σ a x → W x) ∧ StOk (fun x ↦ W x ∨ Writes σ a x) σ st' := by
  by_cases hl : ∃ d p off, a = .load d p off
  · obtain ⟨d, p, off, rfl⟩ := hl
    simp only [atomC] at h
    cases hm : monoOf st.env p with
    | none => rw [hm] at h; cases h
    | some m =>
      simp only [hm, CCell.seq_eq] at h
      have hcell := cellAt_shift σ (monoOf_ok hs.1 hm) off
      cases hw : readWitT X.R d p off with
      | none =>
        simp only [hw, Bool.cond_true, Option.some.injEq] at h
        subst h
        refine ⟨fun x hx ↦ ?_, push_stOk hs (fun _ ↦ Or.inl) (Or.inr (by rw [← hcell]; rfl))⟩
        obtain ⟨hr, -⟩ := hx
        unfold HCert.readWit at hr
        rw [← hX.R, hw] at hr
        cases hr
      | some wt =>
        simp only [hw] at h
        cases hp : ptOk X st (m.shift off) wt with
        | false => rw [hp] at h; cases h
        | true =>
          simp only [hp, Bool.cond_true, Option.some.injEq] at h
          subst h
          refine ⟨fun x hx ↦ ?_, push_stOk hs (fun _ ↦ Or.inl) (Or.inr (by rw [← hcell]; rfl))⟩
          obtain ⟨-, rfl⟩ := hx
          rw [hcell]
          exact ptOk_ok hX hpre hs hp
  by_cases hd : ∃ d x y, a = .add d x y
  · obtain ⟨d, x, y, rfl⟩ := hd
    refine ⟨fun x hx ↦ by simp [Reads] at hx, ?_⟩
    simp only [atomC] at h
    cases hk : vnum d with
    | none => simp only [hk, Option.some.injEq] at h; subst h; exact hs.mono fun _ ↦ Or.inl
    | some k =>
      cases hx : monoOf st.env x with
      | none => simp only [hk, hx, Option.some.injEq] at h; subst h; exact hs.mono fun _ ↦ Or.inl
      | some mx =>
        cases hy : monoOf st.env y with
        | none => simp only [hk, hx, hy, Option.some.injEq] at h; subst h; exact hs.mono fun _ ↦ Or.inl
        | some my =>
          simp only [hk, hx, hy, Option.some.injEq] at h
          subst h
          obtain ⟨e1, e2, e3⟩ := addS_fields st k mx my
          refine ⟨e1 ▸ hs.1, e2 ▸ hs.2.1.mono fun _ ↦ Or.inl,
            e3 ▸ fun r R hr ↦ (hs.2.2.1 r R hr).mono fun _ ↦ Or.inl, addS_adOk hs.2.2.2 ?_⟩
          rw [← vnum_eq hk, show σ d = σ x + σ y from ha, ← val_eq, ← val_eq, ← monoOf_ok hs.1 hx,
              ← monoOf_ok hs.1 hy]
  · simp only [not_exists] at hl hd
    rw [atomC_other hl hd] at h
    cases h1 : atomH X.toH st.toH a with
    | none => rw [h1] at h; cases h
    | some st1 =>
      rw [h1, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨hr, he, hsc⟩ := atomH_ok (X := X.toH) (H := H) (rd := rd) hX.R hX.pre hX.pows hpre h1 hs.1 hs.2.1 ha
      exact ⟨hr, he, hsc, fun r R hr' ↦ (hs.2.2.1 r R hr').mono fun _ ↦ Or.inl, hs.2.2.2⟩

/-- **A call**: its callee's preconditions written; the state after it valid with its writes. -/
theorem callC_ok (hX : XOk sigOf H f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt} {g : String}
    {args rets : List V} (hs : StOk W σ st) (h : callC X st g args rets = some st') :
    SigOk W (sigOf g).pre (sigOf g).preR (args.map σ) ∧
      StOk (fun x ↦ W x ∨ EvW sigOf σ (.call g args rets) x) σ st' := by
  unfold callC at h
  cases ha : monos st.env args with
  | none => simp [ha] at h
  | some ma =>
    cases hr : monos st.env rets with
    | none => simp [ha, hr] at h
    | some mr =>
      cases hc : getF X.C st.nc with
      | none => simp [ha, hr, hc] at h
      | some wl =>
        simp only [ha, hr, hc] at h
        obtain ⟨hma, hla⟩ := monos_ok hs.1 args ma ha
        obtain ⟨hmr, -⟩ := monos_ok hs.1 rets mr hr
        have hm := msOk_append hma hmr (by simpa using hla)
        rw [← List.map_append] at hm
        cases hq : reqS X st ma (X.sigOf g) wl with
        | none => simp [hq] at h
        | some wl' =>
          have hreq := reqS_ok hX hpre hs hma hq
          rw [hX.sigOf] at hreq
          refine ⟨hreq, ?_⟩
          cases wl' with
          | cons _ _ => simp [hq] at h
          | nil =>
            simp only [hq] at h
            cases hp : instAll (ma ++ mr) (X.sigOf g).post with
            | none => simp [hp] at h
            | some ps =>
              cases hrr : instAllR (ma ++ mr) (X.sigOf g).postR with
              | none => simp [hp, hrr] at h
              | some qs =>
                simp only [hp, hrr, Option.some.injEq] at h
                subst h
                rw [hX.sigOf] at hp hrr
                refine pushRL_ok (pushL_ok hs.nextC (fun _ ↦ Or.inl) fun c hc ↦ ?_) (fun _ h ↦ h) fun q hq ↦ ?_
                · obtain ⟨c0, hc0, hi⟩ := instAll_ok hp c hc
                  refine Or.inr (Or.inl ⟨c0, hc0, ?_⟩)
                  rw [addr_eq, CCell.addrW, CCell.addrW, instC_ok hm hi]
                · obtain ⟨r0, hr0, hi⟩ := instAllR_ok hrr q hq
                  exact fun x hx ↦ Or.inr (Or.inr ⟨r0, hr0, (instR_set hm hi).mp hx⟩)

/-- An empty run: its bounds one word. -/
theorem runSet_eq {w : ℕ → E} {b lo hi : CCell} {S : ℕ} (h : lo.valW w = hi.valW w) {x : K} :
    ¬ RunSet w b S lo hi x := by
  rintro ⟨ylo, yhi, j, h1, h2, h3, h4, -⟩
  rw [h, h2, Option.some.injEq] at h1
  omega

/-- **A conditional call** `callIf c g args`: its callee's preconditions written; the state after it valid
with its events' writes (`e`, entered or not). -/
theorem callIfC_ok (hX : XOk sigOf H f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt} {c : V}
    {g : String} {args : List V} (hs : StOk W σ st) (h : callIfC X st c g args = some st') :
    SigOk W (sigOf g).pre (sigOf g).preR (args.map σ) ∧
      StOk (fun x ↦ W x ∨ EW sigOf σ [.inK c, if σ c = 0 then .skip g args else .call g args []] x) σ st' := by
  unfold callIfC at h
  cases ha : monos st.env args with
  | none => simp [ha] at h
  | some ma =>
    cases hc : getF X.C st.nc with
    | none => simp [ha, hc] at h
    | some wl =>
      simp only [ha, hc] at h
      obtain ⟨hma, -⟩ := monos_ok hs.1 args ma ha
      cases hq : reqS X st ma (X.sigOf g) wl with
      | none => simp [hq] at h
      | some wl' =>
        have hreq := reqS_ok hX hpre hs hma hq
        rw [hX.sigOf] at hreq
        refine ⟨hreq, ?_⟩
        cases wl' with
        | cons _ _ => simp [hq] at h
        | nil =>
          simp only [hq] at h
          cases hsum : sumOf st c with
          | none => simp only [hsum, Option.some.injEq] at h; subst h; exact hs.nextC.mono fun _ ↦ Or.inl
          | some p =>
            cases hqs : instAllR ma (X.sigOf g).postR with
            | none => simp only [hsum, hqs, Option.some.injEq] at h; subst h; exact hs.nextC.mono fun _ ↦ Or.inl
            | some qs =>
              simp only [hsum, hqs, Option.some.injEq] at h
              subst h
              refine pushRL_ok hs.nextC (fun _ ↦ Or.inl) fun q hq x hx ↦ ?_
              obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
              -- the guard is the sum of the run's bounds
              have hcs : σ c = q.lo.valW (vw σ) + q.hi.valW (vw σ) := by
                unfold sumOf at hsum
                cases hk : vnum c with
                | none => rw [hk] at hsum; cases hsum
                | some k =>
                  rw [hk] at hsum
                  rw [vnum_eq hk, hs.2.2.2 k p hsum]
                  unfold boundsOf at hq2
                  simp only [Bool.or_eq_true, Bool.and_eq_true] at hq2
                  rcases hq2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · rw [CCell.beq_eq h1, CCell.beq_eq h2]
                  · rw [CCell.beq_eq h1, CCell.beq_eq h2, add_comm]
              by_cases h0 : σ c = 0
              · exact absurd hx (runSet_eq (CoreMode.char2_eq (hcs ▸ h0)))
              · refine Or.inr ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
                rw [ite_eq_right h0]
                obtain ⟨r0, hr0, hi⟩ := instAllR_ok hqs q hq1
                rw [hX.sigOf] at hr0
                simp only [EvW, List.append_nil]
                exact Or.inr ⟨r0, hr0, (instR_set hma hi).mp hx⟩

theorem instArms_mem {sigOf : String → HSig} {ms : List CCell} : ∀ {gs : List String}
    {ps : List (List CCell)} {rs : List (List PRun)}, instArms sigOf ms gs = some (ps, rs) →
    ∀ g ∈ gs, ∃ p ∈ ps, ∃ r ∈ rs, instAll ms (sigOf g).post = some p ∧ instAllR ms (sigOf g).postR = some r
  | [], ps, rs, _, g, hg => by simp at hg
  | g :: gs, ps, rs, h, g0, hg0 => by
    simp only [instArms] at h
    cases h1 : instAll ms (sigOf g).post with
    | none => simp [h1] at h
    | some p =>
      cases h2 : instAllR ms (sigOf g).postR with
      | none => simp [h1, h2] at h
      | some r =>
        cases h3 : instArms sigOf ms gs with
        | none => simp [h1, h2, h3] at h
        | some pr =>
          obtain ⟨ps', rs'⟩ := pr
          simp only [h1, h2, h3, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases List.mem_cons.mp hg0 with rfl | hg0
          · exact ⟨p, List.mem_cons_self, r, List.mem_cons_self, h1, h2⟩
          · obtain ⟨p', hp', r', hr', e1, e2⟩ := instArms_mem h3 g0 hg0
            exact ⟨p', List.mem_cons_of_mem _ hp', r', List.mem_cons_of_mem _ hr', e1, e2⟩

/-- **A dispatch**: every arm's preconditions written; the state after it valid with the taken arm's
writes. -/
theorem dispC_ok (hX : XOk sigOf H f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st st' : CSt}
    {fs : List String} {args rets : List V} (hs : StOk W σ st) (h : dispC X st fs args rets = some st') :
    (∀ g ∈ fs, SigOk W (sigOf g).pre (sigOf g).preR (args.map σ)) ∧
      ∀ g ∈ fs, StOk (fun x ↦ W x ∨ EvW sigOf σ (.call g args rets) x) σ st' := by
  unfold dispC at h
  cases fs with
  | nil => simp at h
  | cons g0 gs =>
  cases ha : monos st.env args with
  | none => simp [ha] at h
  | some ma =>
    cases hr : monos st.env rets with
    | none => simp [ha, hr] at h
    | some mr =>
      cases hc : getF X.C st.nc with
      | none => simp [ha, hr, hc] at h
      | some wl =>
        simp only [ha, hr, hc] at h
        obtain ⟨hma, hla⟩ := monos_ok hs.1 args ma ha
        obtain ⟨hmr, -⟩ := monos_ok hs.1 rets mr hr
        have hm := msOk_append hma hmr (by simpa using hla)
        rw [← List.map_append] at hm
        cases hq : reqArms X st ma (g0 :: gs) wl with
        | none => simp [hq] at h
        | some wl' =>
          refine ⟨reqArms_ok hX hpre hs hma hq, fun g hg ↦ ?_⟩
          cases wl' with
          | cons _ _ => simp [hq] at h
          | nil =>
            simp only [hq] at h
            cases hi : instArms X.sigOf (ma ++ mr) (g0 :: gs) with
            | none => simp [hi] at h
            | some pr =>
              obtain ⟨ps, rs⟩ := pr
              cases ps with
              | nil => simp [hi] at h
              | cons p ps =>
                cases rs with
                | nil => simp [hi] at h
                | cons r rs =>
                  simp only [hi, Option.some.injEq] at h
                  subst h
                  obtain ⟨pg, hpg, rg, hrg, e1, e2⟩ := instArms_mem hi g hg
                  rw [hX.sigOf] at e1 e2
                  refine pushRL_ok (pushL_ok hs.nextC (fun _ ↦ Or.inl) fun c hc ↦ ?_) (fun _ h ↦ h)
                    fun q hq ↦ ?_
                  · obtain ⟨hc1, hc2⟩ := List.mem_filter.mp hc
                    have hcg : c ∈ pg := by
                      rcases List.mem_cons.mp hpg with rfl | hpg
                      · exact hc1
                      · obtain ⟨c', hc', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc2 pg hpg)
                        rwa [← CCell.beq_eq he]
                    obtain ⟨c0, hc0, hi0⟩ := instAll_ok e1 c hcg
                    refine Or.inr (Or.inl ⟨c0, hc0, ?_⟩)
                    rw [addr_eq, CCell.addrW, CCell.addrW, instC_ok hm hi0]
                  · obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
                    have hqg : q ∈ rg := by
                      rcases List.mem_cons.mp hrg with rfl | hrg
                      · exact hq1
                      · obtain ⟨q', hq', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hq2 rg hrg)
                        unfold PRun.beq at he
                        simp only [Bool.and_eq_true] at he
                        obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := he
                        obtain ⟨b, s, l, hh⟩ := q
                        obtain ⟨b', s', l', hh'⟩ := q'
                        simp only at e1 e2 e3 e4
                        rwa [CCell.beq_eq e1, Nat.eq_of_beq_eq_true e2, CCell.beq_eq e3, CCell.beq_eq e4] at hq'
                    obtain ⟨r0, hr0, hi0⟩ := instAllR_ok e2 q hqg
                    exact fun x hx ↦ Or.inr (Or.inr ⟨r0, hr0, (instR_set hm hi0).mp hx⟩)

/-- **A return**: the own guarantees written. -/
theorem retC_ok (hX : XOk sigOf H f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} {vs : List V}
    (hs : StOk W σ st) (h : retC X st vs = true) : PostW sigOf H σ (f.params.map σ) W vs := by
  unfold retC at h
  cases hp : monos st.env X.params with
  | none => simp [hp] at h
  | some mp =>
    cases hv : monos st.env vs with
    | none => simp [hp, hv] at h
    | some mv =>
      cases ht : getF X.T st.nt with
      | none => simp [hp, hv, ht] at h
      | some wl =>
        simp only [hp, hv, ht] at h
        obtain ⟨hmp, hlp⟩ := monos_ok hs.1 _ mp hp
        obtain ⟨hmv, -⟩ := monos_ok hs.1 vs mv hv
        have hm := msOk_append hmp hmv (by simpa using hlp)
        rw [← List.map_append, hX.params] at hm
        cases h1 : reqP X st (mp ++ mv) X.sig.post wl with
        | none => simp [h1] at h
        | some wl' =>
          simp only [h1] at h
          cases h2 : reqR X st (mp ++ mv) X.sig.postR wl' with
          | none => simp [h2] at h
          | some wl'' =>
            rw [hX.sig] at h1 h2
            rw [List.map_append] at hm
            exact ⟨reqP_ok hX hpre hs hm h1, reqR_ok hX hs hm h2⟩

end Stmts

/-! ## Blocks -/

section Pass

variable {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} {σ : Val} {rd : Reader}

theorem pick_cases (x : V) (args rets : List V) : ∀ (fs : List String) (j : ℕ),
    pick σ x args rets j fs = .stuck ∨ ∃ g ∈ fs, pick σ x args rets j fs = .fall [.call g args rets]
  | [], _ => Or.inl rfl
  | g :: fs, j => by
    unfold pick
    split_ifs
    · exact Or.inr ⟨g, List.mem_cons_self, rfl⟩
    · rcases pick_cases x args rets fs (j + 1) with h | ⟨g', hg', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', h⟩

/-- A call, then a block: the call's needs, then the block's pass from the state after it. -/
theorem blockC_call {W : K → Prop} (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ))
    {g : String} {args rets : List V} {ss : List Stmt} {st1 st' : CSt}
    (hreq : SigOk W (sigOf g).pre (sigOf g).preR (args.map σ))
    (hpost : StOk (fun x ↦ W x ∨ EvW sigOf σ (.call g args rets) x) σ st1)
    (hss : ∀ {W' : K → Prop}, (∀ c ∈ H.sig.pre, W' (c.addr σ)) → StOk W' σ st1 →
      BlockC sigOf H σ rd (f.params.map σ) W' (walk σ ss) st') :
    BlockC sigOf H σ rd (f.params.map σ) W ((Out.fall [.call g args rets]).seq (walk σ ss)) st' := by
  refine blockC_seq (W1 := fun _ x ↦ W x ∨ EvW sigOf σ (.call g args rets) x)
    ⟨fun es hw _ ↦ ?_, fun es vs hw _ ↦ by simp at hw⟩ fun es hw _ ↦ ?_
  · simp only [Out.fall.injEq] at hw
    subst hw
    exact covC_single hreq
  · simp only [Out.fall.injEq] at hw
    subst hw
    exact ⟨fun x hx ↦ hx.imp_right fun hx ↦ ⟨_, List.mem_singleton_self _, hx⟩,
      hss (fun c hc ↦ Or.inl (hpre c hc)) hpost⟩

mutual
/-- **The pass over a block, on the path.** -/
theorem chkC_ok (hX : XOk sigOf H f σ X) : ∀ (ss : List Stmt) {st st' : CSt} {W : K → Prop},
    (∀ c ∈ H.sig.pre, W (c.addr σ)) → chkC X ss st = some st' → StOk W σ st →
      BlockC sigOf H σ rd (f.params.map σ) W (walk σ ss) st'
  | [], st, st', W, _, h, hs => by
    simp only [chkC, Option.some.injEq] at h
    subst h
    refine ⟨⟨fun es hw _ ↦ ?_, fun es vs hw _ ↦ by simp [walk] at hw⟩, fun es hw _ ↦ ?_⟩
    · simp only [walk, Out.fall.injEq] at hw
      subst hw
      exact covC_nil W
    · simp only [walk, Out.fall.injEq] at hw
      subst hw
      exact hs.mono fun _ ↦ Or.inl
  | .atom a :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases ha : atomC X st a with
    | none => rw [ha] at h; cases h
    | some st1 =>
      rw [ha] at h
      simp only [CSt.seq_eq] at h
      rw [walk]
      refine blockC_seq (W1 := fun _ x ↦ W x ∨ Writes σ a x)
        ⟨fun es hw hh ↦ ?_, fun es vs hw _ ↦ by simp [walk1] at hw⟩ fun es hw hh ↦ ?_
      · simp only [walk1, Out.fall.injEq] at hw
        subst hw
        exact covC_single (atomC_ok hX hpre ha hs (hh _ List.mem_cons_self)).1
      · simp only [walk1, Out.fall.injEq] at hw
        subst hw
        obtain ⟨-, hs1⟩ := atomC_ok hX hpre ha hs (hh _ List.mem_cons_self)
        exact ⟨fun x hx ↦ hx.imp_right fun hx ↦ ⟨.atom a, List.mem_singleton_self _, hx⟩,
          chkC_ok hX ss (fun c hc ↦ Or.inl (hpre c hc)) h hs1⟩
  | .ite c z n :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : chkC X z st with
    | none => rw [h1] at h; cases h
    | some s1 =>
      simp only [h1] at h
      cases h2 : chkC X n (st.cnt s1) with
      | none => simp [h2] at h
      | some s2 =>
        simp only [h2, CSt.seq_eq] at h
        rw [walk]
        refine blockC_seq (W1 := fun _ ↦ W) ?_ fun es _ _ ↦
          ⟨fun x hx ↦ Or.inl hx, chkC_ok hX ss hpre h (hs.cnt s2)⟩
        simp only [walk1]
        refine outC_pre ?_ c
        by_cases hc : σ c = 0
        · rw [ite_eq_left hc]
          exact (chkC_ok hX z hpre h1 hs).1
        · rw [ite_eq_right hc]
          exact (chkC_ok hX n hpre h2 (hs.cnt s1)).1
  | .match_ x arms :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : chkArmsC X arms st with
    | none => rw [h1] at h; cases h
    | some s =>
      rw [h1] at h
      simp only [CSt.seq_eq] at h
      rw [walk]
      exact blockC_seq (W1 := fun _ ↦ W) (chkArmsC_ok hX arms hpre h1 hs x 0) fun es _ _ ↦
        ⟨fun x hx ↦ Or.inl hx, chkC_ok hX ss hpre h (hs.cnt s)⟩
  | .call g args rets :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : callC X st g args rets with
    | none => rw [h1] at h; cases h
    | some st1 =>
      rw [h1] at h
      simp only [CSt.seq_eq] at h
      rw [walk]
      obtain ⟨hreq, hpost⟩ := callC_ok hX hpre hs h1
      exact blockC_call hpre hreq hpost fun hp hs' ↦ chkC_ok hX ss hp h hs'
  | .callIf c g args :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : callIfC X st c g args with
    | none => rw [h1] at h; cases h
    | some st1 =>
      rw [h1] at h
      simp only [CSt.seq_eq] at h
      obtain ⟨hreq, hs1⟩ := callIfC_ok hX hpre hs h1
      rw [walk]
      refine blockC_seq (W1 := fun es x ↦ W x ∨ EW sigOf σ es x)
        ⟨fun es hw _ ↦ ?_, fun es vs hw _ ↦ by simp [walk1] at hw⟩ fun es hw _ ↦ ?_
      swap
      · simp only [walk1, Out.fall.injEq] at hw
        subst hw
        exact ⟨fun x hx ↦ hx, chkC_ok hX ss (fun c hc ↦ Or.inl (hpre c hc)) h hs1⟩
      simp only [walk1, Out.fall.injEq] at hw
      subst hw
      show CovC sigOf H σ W ([Ev.inK c] ++ [_])
      refine covC_append (covC_single trivial) (covC_single ?_)
      by_cases hc : σ c = 0
      · rw [ite_eq_left hc]; trivial
      · rw [ite_eq_right hc]; exact hreq.mono fun _ ↦ Or.inl
  | .dispatch x fs args rets :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases h1 : dispC X st fs args rets with
    | none => rw [h1] at h; cases h
    | some st1 =>
      rw [h1] at h
      simp only [CSt.seq_eq] at h
      obtain ⟨hreq, hpost⟩ := dispC_ok hX hpre hs h1
      rw [walk]
      simp only [walk1]
      rcases pick_cases x args rets fs 0 with hp | ⟨g, hg, hp⟩
      · rw [hp]
        exact ⟨⟨fun es hw _ ↦ by simp [Out.seq] at hw, fun es vs hw _ ↦ by simp [Out.seq] at hw⟩,
          fun es hw _ ↦ by simp [Out.seq] at hw⟩
      · rw [hp]
        exact blockC_call hpre (hreq g hg) (hpost g hg) fun hp hs' ↦ chkC_ok hX ss hp h hs'
  | .ret vs :: ss, st, st', W, hpre, h, hs => by
    simp only [chkC] at h
    cases hr : retC X st vs with
    | false => rw [hr] at h; cases h
    | true =>
      refine ⟨⟨fun es hw _ ↦ by simp [walk, walk1, Out.seq] at hw, fun es vs' hw _ ↦ ?_⟩,
        fun es hw _ ↦ by simp [walk, walk1, Out.seq] at hw⟩
      simp only [walk, walk1, Out.seq, Out.ret.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨covC_nil W, (retC_ok hX hpre hs hr).mono fun _ ↦ Or.inl⟩

/-- **The pass over the arms, on the path.** -/
theorem chkArmsC_ok (hX : XOk sigOf H f σ X) : ∀ (arms : List (List Stmt)) {st st' : CSt} {W : K → Prop},
    (∀ c ∈ H.sig.pre, W (c.addr σ)) → chkArmsC X arms st = some st' → StOk W σ st →
      ∀ x j, OutC sigOf H σ rd (f.params.map σ) W (walkArms σ x j arms)
  | [], _, _, _, _, _, _, x, j => ⟨fun es hw _ ↦ by simp [walkArms] at hw, fun es vs hw _ ↦ by simp [walkArms] at hw⟩
  | a :: as, st, st', W, hpre, h, hs, x, j => by
    simp only [chkArmsC] at h
    cases h1 : chkC X a st with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1] at h
      rw [walkArms]
      split_ifs
      · exact (chkC_ok hX a hpre h1 hs).1
      · exact chkArmsC_ok hX as hpre h (hs.cnt s1) x (j + 1)
end

end Pass

/-! ## A loop's tail -/

section Tail

variable {sigOf : String → HSig} {H : HCert} {f : Fn} {X : CX} {σ : Val} {rd : Reader} {W : K → Prop}

theorem cond_some {α : Type} {b : Bool} {x : Option α} {y : α} (h : (bif b then x else none) = some y) :
    b = true ∧ x = some y := by
  cases b <;> simp_all

theorem CIdx.beq_eq : ∀ {a b : CIdx}, CIdx.beq a b = true → a = b
  | .num a, .num b, h => by rw [Nat.eq_of_beq_eq_true h]
  | .val a, .val b, h => by rw [Nat.eq_of_beq_eq_true h]
  | .mono a, .mono b, h => by rw [CCell.beq_eq h]
  | .num _, .val _, h => by simp [CIdx.beq] at h
  | .val _, .num _, h => by simp [CIdx.beq] at h
  | .num _, .mono _, h => by simp [CIdx.beq] at h
  | .mono _, .num _, h => by simp [CIdx.beq] at h
  | .val _, .mono _, h => by simp [CIdx.beq] at h
  | .mono _, .val _, h => by simp [CIdx.beq] at h

theorem slotW_cons_ne {a a' : E} {l : List E} {b : ℕ} (hb : b ≠ 0) : slotW (a :: l) b = slotW (a' :: l) b := by
  cases b with
  | zero => exact absurd rfl hb
  | succ b => rfl

theorem valW_cons_noSlot0 {c : CCell} (hc : noSlot0 c = true) (a a' : E) (l : List E) :
    c.valW (slotW (a :: l)) = c.valW (slotW (a' :: l)) := by
  refine valW_congr fun b hb ↦ slotW_cons_ne ?_
  have := List.all_eq_true.mp hc b hb
  simp only [Bool.not_eq_true'] at this
  exact Nat.ne_of_beq_eq_false this

theorem idx_cons_noSlot0 {i : CIdx} (hi : noSlot0I i = true) (a a' : E) (l : List E) :
    (idxC i).valW (slotW (a :: l)) = (idxC i).valW (slotW (a' :: l)) := by
  cases i with
  | num n => rfl
  | val v =>
    rw [idxC, valW_baseC, valW_baseC]
    simp only [noSlot0I, Bool.not_eq_true'] at hi
    exact slotW_cons_ne (Nat.ne_of_beq_eq_false hi)
  | mono c => exact valW_cons_noSlot0 hi a a' l

theorem set_cons_noSlot0 {r : CRun} (hr : noSlot0R r = true) (a a' : E) (l : List E) {x : K} :
    r.Set (slotW (a :: l)) x ↔ r.Set (slotW (a' :: l)) x := by
  simp only [noSlot0R, Bool.and_eq_true] at hr
  exact runSet_congr (valW_cons_noSlot0 hr.1.1 a a' l) (idx_cons_noSlot0 hr.1.2 a a' l)
    (idx_cons_noSlot0 hr.2 a a' l)

theorem endOf_noSlot0 {ei : CIdx} {endc : Option ℕ} (h : endOf ei = some endc) : noSlot0I ei = true := by
  cases ei with
  | num => rfl
  | val v =>
    cases v with
    | zero => simp [endOf] at h
    | succ v => rfl
  | mono => simp [endOf] at h

theorem tailP_ok (hX : XOk sigOf H f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk W σ st)
    {mp mx : List CCell} {ws wx : List E} (hmp : MsOk (vw σ) mp (slotW ws)) (hmx : MsOk (vw σ) mx (slotW wx))
    {ex : Bool} : ∀ {cs : List CCell} {wl wl' : List Wit}, tailP X st mp mx ex cs wl = some wl' →
      ∀ c ∈ cs, W (c.addrW (slotW ws)) ∨ (ex = true ∧ noSlot0 c = true ∧ W (c.addrW (slotW wx)))
  | [], _, _, _, c, hc => by simp at hc
  | c :: cs, [], _, h, _, _ => by simp [tailP] at h
  | c :: cs, w :: wl, wl', h, c0, hc0 => by
    simp only [tailP] at h
    obtain ⟨hb, h⟩ := cond_some h
    rcases List.mem_cons.mp hc0 with rfl | hc0
    · rcases Bool.or_eq_true_iff.mp hb with h1 | h1
      · left
        split at h1
        · rename_i c' hi
          have := ptOk_ok hX hpre hs h1
          rwa [addr_eq, CCell.addrW, instC_ok hmp hi] at this
        · cases h1
      · simp only [Bool.and_eq_true] at h1
        obtain ⟨⟨h1, h2⟩, h3⟩ := h1
        refine Or.inr ⟨h1, h2, ?_⟩
        split at h3
        · rename_i c' hi
          have := ptOk_ok hX hpre hs h3
          rwa [addr_eq, CCell.addrW, instC_ok hmx hi] at this
        · cases h3
    · exact tailP_ok hX hpre hs hmp hmx h c0 hc0

theorem tailR_ok (hX : XOk sigOf H f σ X) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ)) {st : CSt} (hs : StOk W σ st)
    {mp mx : List CCell} {ws wx : List E} (hmp : MsOk (vw σ) mp (slotW ws)) (hmx : MsOk (vw σ) mx (slotW wx))
    {ex : Bool} {ei : CIdx} : ∀ {rs : List CRun} {wl wl' : List Wit}, tailR X st mp mx ex ei rs wl = some wl' →
      ∀ r ∈ rs, r.F W (slotW ws) ∨ (ex = true ∧ noSlot0R r = true ∧ r.F W (slotW wx)) ∨
        (r.lo = .val 0 ∧ r.hi = ei ∧ noSlot0 r.base = true ∧ ∃ b m0, instC mp r.base = some b ∧
          nth mp 0 = some m0 ∧ W ((b.mul (m0.pow r.stride)).addr σ))
  | [], _, _, _, r, hr => by simp at hr
  | r :: rs, [], _, h, _, _ => by simp [tailR] at h
  | r :: rs, w :: wl, wl', h, r0, hr0 => by
    simp only [tailR] at h
    obtain ⟨hb, h⟩ := cond_some h
    rcases List.mem_cons.mp hr0 with rfl | hr0
    · rcases Bool.or_eq_true_iff.mp hb with h1 | h1
      · rcases Bool.or_eq_true_iff.mp h1 with h1 | h1
        · left
          split at h1
          · rename_i q hi
            exact (instR_runF hmp hi).mp (rnOk_ok hX hs h1)
          · cases h1
        · simp only [Bool.and_eq_true] at h1
          obtain ⟨⟨h1, h2⟩, h3⟩ := h1
          refine Or.inr (Or.inl ⟨h1, h2, ?_⟩)
          split at h3
          · rename_i q hi
            exact (instR_runF hmx hi).mp (rnOk_ok hX hs h3)
          · cases h3
      · simp only [Bool.and_eq_true] at h1
        obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := h1
        refine Or.inr (Or.inr ⟨CIdx.beq_eq e1, CIdx.beq_eq e2, e3, ?_⟩)
        split at e4
        · rename_i b m0 hb' hm
          exact ⟨b, m0, hb', hm, ptOk_ok hX hpre hs e4⟩
        · cases e4
    · exact tailR_ok hX hpre hs hmp hmx h r0 hr0

/-- **A loop's tail**: after its body (`W`, the state `st`), its tail call `callIf c self (i' :: ps)` and
its `ret []`, the guarantees written: by the path; or, entered, by the next iteration (a guarantee not
over the counter is its own instance there), not entered, by the path at the exit (the next counter
is the end); or a run `[counter, end)` accumulated: the counter's point by the path, the rest by the
next iteration, none at the exit. -/
theorem tailC_ok (hX : XOk sigOf H f σ X) (hself : sigOf f.name = H.sig) (hpre : ∀ c ∈ H.sig.pre, W (c.addr σ))
    {st : CSt} (hs : StOk W σ st) {ei : CIdx} (hterm : (CIdx.val 0, ei) ∈ H.sig.term) {endc : Option ℕ}
    (hend : endOf ei = some endc) {m : ℕ} (hpar : f.params = (List.range m).map V.n)
    (hover : idxOver m ei = true) {ps : List V} (hps : f.params = V.n 0 :: ps) {c i' : V}
    (hi' : σ i' = σ (V.n 0) * ofK (addressOfIndex 1))
    (hc : σ c = σ (V.n 0) * ofK (addressOfIndex 1) + Res.endVal σ f endc)
    (h : tailC X st (i' :: ps) ei = true) :
    PostW sigOf H σ (f.params.map σ)
      (fun x ↦ W x ∨ EW sigOf σ [.inK c, if σ c = 0 then .skip f.name (i' :: ps) else .call f.name (i' :: ps) []] x)
      [] := by
  set e : Ev := if σ c = 0 then .skip f.name (i' :: ps) else .call f.name (i' :: ps) [] with he
  have hws0' : f.params.map σ = σ (V.n 0) :: ps.map σ := by rw [hps, List.map_cons]
  have hm0 : 0 < m := by
    have := congrArg List.length (hpar.symm.trans hps)
    simp at this
    omega
  have hslot : ∀ b < m, slotW (f.params.map σ) b = vw σ b := fun b hb ↦ by
    rw [hpar, List.map_map]; exact slotW_params hb
  have hei : (idxC ei).valW (slotW (f.params.map σ)) = (idxC ei).valW (vw σ) := by
    cases ei with
    | num n => rfl
    | val v => rw [idxC, valW_baseC, valW_baseC]; exact hslot v (by simpa [idxOver] using hover)
    | mono => simp [endOf] at hend
  have hendv : Res.endVal σ f endc = (idxC ei).valW (vw σ) := by
    cases ei with
    | num n =>
      simp only [endOf, Option.some.injEq] at hend
      subst hend
      rw [idxC, valW_const]
      rfl
    | val v =>
      cases v with
      | zero => simp [endOf] at hend
      | succ v =>
        cases v with
        | succ => simp [endOf] at hend
        | zero =>
          simp only [endOf, Option.some.injEq] at hend
          subst hend
          have hm : 1 < m := by simpa [idxOver] using hover
          obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
          rw [idxC, valW_baseC]
          simp only [Res.endVal, hpar, List.range_succ_eq_map, List.map_cons, List.map_map]
          rfl
    | mono => simp [endOf] at hend
  have hexit : σ c = 0 → σ (V.n 0) * ofK (addressOfIndex 1) = (idxC ei).valW (vw σ) := fun h0 ↦ by
    rw [← hendv]
    exact CoreMode.char2_eq (by rw [← hc, h0])
  have hcall : σ c ≠ 0 → ∀ x, SigSet H.sig.post H.sig.postR ((i' :: ps).map σ) x →
      EW sigOf σ [.inK c, e] x := fun h0 x hx ↦ by
    refine ⟨e, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    rw [he, ite_eq_right h0]
    simp only [EvW]
    rw [hself, List.append_nil]
    exact hx
  unfold tailC at h
  cases hmp : monos st.env X.params with
  | none => simp [hmp] at h
  | some mp =>
    cases ht : getF X.T st.nt with
    | none => simp [hmp, ht] at h
    | some wl =>
      cases hmi : monoOf st.env i' with
      | none => simp [hmp, ht, hmi] at h
      | some mi =>
        simp only [hmp, ht, hmi] at h
        obtain ⟨hmp', hlp⟩ := monos_ok hs.1 _ mp hmp
        rw [hX.params] at hmp' hlp
        have hmx := msOk_setNth (n := 1) hmp' (by simpa using hlp) (show mi.valW (vw σ) = σ i' by
          rw [← val_eq, ← monoOf_ok hs.1 hmi])
        have hwx0 : ei = .val 1 → σ c = 0 → slotW (setNth (f.params.map σ) 1 (σ i')) = slotW (f.params.map σ) :=
          fun he1 h0 ↦ funext fun b ↦ by
            rw [slotW_setNth]
            split_ifs with hb
            · obtain ⟨rfl, -⟩ := hb
              rw [hi', hexit h0, he1, idxC, valW_baseC]
              exact (hslot 1 (by subst he1; simpa [idxOver] using hover)).symm
            · rfl
        cases hp : tailP X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) X.sig.post wl with
        | none => simp [hp] at h
        | some wl' =>
          simp only [hp] at h
          cases hr : tailR X st mp (setNth mp 1 mi) (CIdx.beq ei (.val 1)) ei X.sig.postR wl' with
          | none => simp [hr] at h
          | some wl'' =>
            rw [hX.sig] at hp hr
            have HP := tailP_ok hX hpre hs hmp' hmx hp
            have HR := tailR_ok hX hpre hs hmp' hmx hr
            unfold PostW
            rw [List.map_nil, List.append_nil]
            refine ⟨fun c0 hc0 ↦ ?_, fun r hr0 ↦ ?_⟩
            · rcases HP c0 hc0 with h1 | ⟨hex, hns, h1⟩
              · exact Or.inl h1
              · have hei1 : ei = .val 1 := CIdx.beq_eq hex
                by_cases h0 : σ c = 0
                · exact Or.inl (by rw [← hwx0 hei1 h0]; exact h1)
                · refine Or.inr (hcall h0 _ (Or.inl ⟨c0, hc0, ?_⟩))
                  rw [CCell.addrW, CCell.addrW, hws0', List.map_cons, valW_cons_noSlot0 hns]
            · rcases HR r hr0 with h1 | ⟨hex, hns, h1⟩ | ⟨hlo, hhi, hnb, b, m0, hb, hm0', h1⟩
              · exact h1.mono fun _ ↦ Or.inl
              · have hei1 := CIdx.beq_eq hex
                by_cases h0 : σ c = 0
                · rw [← hwx0 hei1 h0]; exact h1.mono fun _ ↦ Or.inl
                · refine fun x hx ↦ Or.inr (hcall h0 x (Or.inr ⟨r, hr0, ?_⟩))
                  rw [List.map_cons]
                  rw [hws0'] at hx
                  exact (set_cons_noSlot0 hns _ _ _).mp hx
              · have hl0 : (idxC r.lo).valW (slotW (f.params.map σ)) = vw σ 0 := by
                  rw [hlo, idxC, valW_baseC]; exact hslot 0 hm0
                have hh0 : (idxC r.hi).valW (slotW (f.params.map σ)) = (idxC ei).valW (vw σ) := by
                  rw [hhi]; exact hei
                intro x hx
                obtain ⟨ylo, yhi, j, hylo, hyhi, h3, h4, rfl⟩ := hx
                rw [hl0] at hylo
                rw [hh0] at hyhi
                have hcap := (rep_spec hyhi).1
                rcases Nat.eq_or_lt_of_le h3 with rfl | h3
                · left
                  have hb' := instC_ok hmp' hb
                  have hm0'' := hmp' 0 m0 hm0'
                  have hcell : (b.mul (m0.pow r.stride)).addr σ =
                      (r.base.valW (slotW (f.params.map σ)) * ofK (addressOfIndex (r.stride * ylo))).limb 0 := by
                    rw [addr_eq, CCell.addrW, valW_mul, valW_pow, hb', hm0'', hslot 0 hm0, (rep_spec hylo).2,
                      ← ofK_pow']
                    simp only [addressOfIndex, ← pow_mul, mul_comm]
                  rw [← hcell]
                  exact h1
                · by_cases h0 : σ c = 0
                  · exfalso
                    have hx := hexit h0
                    rw [show σ (V.n 0) = vw σ 0 from rfl, (rep_spec hylo).2, ← ofK_mul', addressOfIndex,
                      addressOfIndex, ← pow_add, ← addressOfIndex] at hx
                    rw [← hx, rep_of (by omega), Option.some.injEq] at hyhi
                    omega
                  · refine Or.inr (hcall h0 _ (Or.inr ⟨r, hr0, ylo + 1, yhi, j, ?_, ?_, by omega, h4, ?_⟩))
                    · rw [hlo, idxC, valW_baseC, List.map_cons]
                      show rep (σ i') = some (ylo + 1)
                      rw [hi']
                      exact rep_succ hylo (by omega)
                    · rw [hhi, List.map_cons, idx_cons_noSlot0 (endOf_noSlot0 hend) (σ i') (σ (V.n 0)), ← hws0',
                        hei]
                      exact hyhi
                    · rw [List.map_cons, valW_cons_noSlot0 hnb (σ i') (σ (V.n 0)), ← hws0']

end Tail

/-! ## The function -/

section Main

theorem loopBody_of {fn : Fn} {pre : List Stmt} {a b : Stmt} (h : fn.body = pre ++ [a, b]) : loopBody fn = pre := by
  simp [loopBody, h]

theorem idxOver_val {σ : Val} {f : Fn} {m : ℕ} (hpar : f.params = (List.range m).map V.n) {i : CIdx}
    (h : idxOver m i = true) : (idxC i).valW (slotW (f.params.map σ)) = (idxC i).valW (vw σ) := by
  cases i with
  | num n => rfl
  | val v =>
    rw [idxC, valW_baseC, valW_baseC, hpar, List.map_map]
    exact slotW_params (by simpa [idxOver] using h)
  | mono c =>
    rw [idxC]
    refine valW_congr fun b hb ↦ ?_
    have := List.all_eq_true.mp h b hb
    rw [hpar, List.map_map]
    exact slotW_params (Nat.blt_eq.mp this)

theorem paramEnv_get : ∀ (m k : ℕ) (c : CCell), getF (paramEnv m) k = some c → c = baseC k
  | 0, k, c, h => by simp [paramEnv, getF_nil] at h
  | m + 1, k, c, h => by
    simp only [paramEnv, Trie.seq_eq, id] at h
    rcases getF_setF h with ⟨rfl, rfl⟩ | h
    · rfl
    · exact paramEnv_get m k c h

theorem paramEnv_ok (σ : Val) (m : ℕ) : EnvOk σ (paramEnv m) := fun k c h ↦ by
  rw [paramEnv_get m k c h, val_baseC]

theorem initC_ok {X : CX} {σ : Val} {st0 : CSt} (h : initC X = some st0) :
    StOk (fun x ↦ SigSet X.sig.pre X.sig.preR (X.params.map σ) x) σ st0 := by
  unfold initC at h
  rw [Trie.seq_eq] at h
  cases hm : monos (paramEnv X.params.length) X.params with
  | none => simp [hm] at h
  | some mp =>
    simp only [hm] at h
    cases hr : instAllR mp X.sig.preR with
    | none => simp [hr] at h
    | some rs =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨hmp, -⟩ := monos_ok (paramEnv_ok σ _) _ mp hm
      refine pushRL_ok ⟨paramEnv_ok σ _, fun n c h ↦ by simp [getF_nil] at h, fun r R h ↦ by simp [getF_nil] at h,
        fun k p h ↦ by simp [getF_nil] at h⟩ (fun _ h ↦ h) fun q hq ↦ ?_
      obtain ⟨r, hr0, hi⟩ := instAllR_ok hr q hq
      exact (instR_runF hmp hi).mpr fun x hx ↦ Or.inr ⟨r, hr0, hx⟩

/-- A loop helper's path, its tail's events named: its body's, the tail's guard, then its tail call. -/
theorem walk_tail {σ : Val} {pre : List Stmt} {c i' : V} {g : String} {ps : List V} {es1 : List Ev}
    (h : walk σ pre = .fall es1) :
    walk σ (pre ++ [.callIf c g (i' :: ps), .ret []]) =
      .ret (es1 ++ [.inK c, if σ c = 0 then .skip g (i' :: ps) else .call g (i' :: ps) []]) [] := by
  rw [walk_append, h]
  simp [walk, walk1, Out.seq, Out.pre]

/-- **The heap check with calls and loops is sound**: on a path of a function passing `heapOkC` that
returns, its events holding and each entered call's callee guarantees' runs having their exponents,
given its entry facts and its residuals, every event's needs are written before it and its
guarantees are written at return. A loop helper's own signature is `sigOf`'s for its name. -/
theorem heapOkC_sound {pows : PowTree} (hp : pows.Ok) {sigOf : String → HSig} {f : Fn} {H : HCert}
    (hok : heapOkC pows sigOf f H = true) (hself : sigOf f.name = H.sig) {σ : Val} {rd : Reader}
    {es : List Ev} {vs : List V} (hw : walk σ f.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hE : EntryF H (f.params.map σ)) (hR : ResF H σ) :
    ReadsOkC sigOf H σ (f.params.map σ) es ∧ PostOkC sigOf H σ (f.params.map σ) es vs := by
  unfold heapOkC at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨hpar, hpov⟩, hto⟩, hc⟩ := hok
  simp only [Trie.seq_eq] at hc
  have hpar' : f.params = (List.range f.params.length).map V.n := by
    rw [List.range_eq_range']; exact paramsN_eq _ 0 hpar
  generalize hXdef : (⟨pows, H.readT, trieFrom H.sig.pre 0 .nil, trieFrom H.calls 0 .nil, trieFrom H.rets 0 .nil,
    trieFrom H.res 0 .nil, sigOf, H.sig, f.params⟩ : CX) = X at hc
  have hX : XOk sigOf H f σ X := by
    subst hXdef
    exact { R := rfl
            pre := fun k c h ↦ (getF_trieFrom _ _ _ h).resolve_right (by simp [getF_nil])
            pows := hp
            sigOf := rfl
            sig := rfl
            params := rfl
            res := fun i c h ↦ (getF_trieFrom _ _ _ h).resolve_right (by simp [getF_nil])
            term := fun q hq ↦ by
              have ho := List.all_eq_true.mp hto q hq
              simp only [Bool.and_eq_true] at ho
              exact (ltF_congr (idxOver_val hpar' ho.1) (idxOver_val hpar' ho.2)).mp (hE q hq)
            resF := hR }
  set W0 : K → Prop := fun x ↦ SigSet H.sig.pre H.sig.preR (f.params.map σ) x with hW0
  have hpreW : ∀ c ∈ H.sig.pre, W0 (c.addr σ) := fun c hc ↦ by
    refine Or.inl ⟨c, hc, ?_⟩
    have hv : c.valW (vw σ) = c.valW (slotW (f.params.map σ)) := valW_congr fun b hb ↦ by
      have := List.all_eq_true.mp (List.all_eq_true.mp hpov c hc) b hb
      rw [hpar', List.map_map]
      exact (slotW_params (Nat.blt_eq.mp this)).symm
    rw [addr_eq, CCell.addrW, CCell.addrW, hv]
  have hevs : EvsOk sigOf rd σ es := hh
  have fin : CovC sigOf H σ W0 es → PostW sigOf H σ (f.params.map σ) (fun x ↦ W0 x ∨ EW sigOf σ es x) vs →
      ReadsOkC sigOf H σ (f.params.map σ) es ∧ PostOkC sigOf H σ (f.params.map σ) es vs :=
    fun h1 h2 ↦ ⟨fun es1 e es2 he ↦ h1 es1 e es2 he, h2⟩
  cases hi : initC X with
  | none => simp [hi] at hc
  | some st0 =>
    simp only [hi] at hc
    have hs0 : StOk W0 σ st0 := by
      have := initC_ok (X := X) (σ := σ) hi
      rwa [hX.sig, hX.params] at this
    split at hc
    · obtain ⟨st', hst⟩ := Option.isSome_iff_exists.mp hc
      exact fin ((chkC_ok hX f.body hpreW hst hs0).1.2 es vs hw hevs).1
        ((chkC_ok hX f.body hpreW hst hs0).1.2 es vs hw hevs).2
    · rename_i ei hterm
      unfold loopC at hc
      split at hc
      · rename_i endc c0 g args rest hend hrev
        split at hc
        · rename_i pre hls
          split at hc
          · rename_i st1 hst1
            split at hc
            · rename_i st2 hst2
              obtain ⟨c, i', p0, prest, hps, hbody, -, -⟩ := loopShape_spec hls
              have hlb := loopBody_of hbody
              -- the tail's statement, read off the reversed body
              have htl : Stmt.callIf c0 g args = .callIf c f.name (i' :: prest) := by
                have := congrArg List.reverse hbody
                rw [hrev] at this
                simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
                  List.cons_append, List.cons.injEq] at this
                exact this.2.1
              simp only [Stmt.callIf.injEq] at htl
              obtain ⟨h1, h2, h3⟩ := htl
              subst c0 g args
              -- the parameters
              have hp0 : p0 = V.n 0 ∧ f.params = V.n 0 :: prest := by
                have h1 := hpar'.symm.trans hps
                cases hm : f.params.length with
                | zero => rw [hm] at h1; simp at h1
                | succ k =>
                  rw [hm, List.range_succ_eq_map, List.map_cons] at h1
                  obtain ⟨h2, -⟩ := List.cons.inj h1
                  exact ⟨h2.symm, by rw [hps, ← h2]⟩
              obtain ⟨rfl, hps'⟩ := hp0
              -- the path
              obtain ⟨p0', prest', c', i'', es1, hps2, hw1, hes, hi'', hc''⟩ :=
                Res.loop_path (rd := rd) (by rw [hlb]; exact hls) hw hh
              rw [hlb] at hw1
              have hw2 := walk_tail (c := c) (g := f.name) (i' := i') (ps := prest) hw1
              rw [← hbody, hw] at hw2
              simp only [Out.ret.injEq] at hw2
              obtain ⟨hes2, rfl⟩ := hw2
              rw [hps', List.cons.injEq] at hps2
              obtain ⟨rfl, rfl⟩ := hps2
              rw [hes2] at hes
              simp only [List.append_cancel_left_eq, List.cons.injEq, Ev.inK.injEq, and_true] at hes
              obtain ⟨rfl, hee⟩ := hes
              have hi'eq : i'' = i' := by
                split_ifs at hee <;>
                  simp only [Ev.skip.injEq, Ev.call.injEq, List.cons.injEq, true_and, and_true] at hee <;>
                  exact hee.symm
              subst hi'eq
              subst hes2
              -- the body, then the tail
              have hev := evsOk_append hevs
              have hb1 := chkC_ok (rd := rd) hX pre hpreW hst1 hs0
              have hcov1 := hb1.1.1 es1 hw1 hev.1
              have hs1 := hb1.2 es1 hw1 hev.1
              have hpre1 : ∀ c ∈ H.sig.pre, (fun x ↦ W0 x ∨ EW sigOf σ es1 x) (c.addr σ) :=
                fun c hc ↦ Or.inl (hpreW c hc)
              obtain ⟨hreq, hs2⟩ := callIfC_ok hX hpre1 hs1 hst2
              have hterm' : (CIdx.val 0, ei) ∈ H.sig.term := by rw [hterm]; exact List.mem_singleton_self _
              have hover : idxOver f.params.length ei = true := by
                have := List.all_eq_true.mp hto _ hterm'
                simp only [Bool.and_eq_true] at this
                exact this.2
              have hpost := tailC_ok hX hself (fun c hc ↦ Or.inl (hpre1 c hc)) hs2 hterm' hend hpar' hover hps'
                hi'' hc'' hc
              refine fin (covC_append hcov1 ?_) (hpost.mono fun x hx ↦ ?_)
              · show CovC sigOf H σ _ ([Ev.inK c] ++ [_])
                refine covC_append (covC_single trivial) (covC_single ?_)
                split_ifs
                · trivial
                · exact hreq.mono fun _ ↦ Or.inl
              · rcases hx with ((hx | hx) | hx) | hx
                · exact Or.inl hx
                · exact Or.inr (ew_append_left hx)
                · exact Or.inr (ew_append_right hx)
                · exact Or.inr (ew_append_right hx)
            · cases hc
          · cases hc
        · cases hc
      · cases hc
    · cases hc

end Main

/-! ## Milestone 1's statement -/

/-- A precondition's address at the parameters' words is its address at the values `V.n b`. -/
theorem addr_pre {σ : Val} {f : Fn} {pre : List CCell} (hpar : f.params = (List.range f.params.length).map V.n)
    (hpov : preOver f.params.length pre = true) {c : CCell} (hc : c ∈ pre) :
    c.addrW (slotW (f.params.map σ)) = c.addr σ := by
  have hv : c.valW (vw σ) = c.valW (slotW (f.params.map σ)) := valW_congr fun b hb ↦ by
    have := List.all_eq_true.mp (List.all_eq_true.mp hpov c hc) b hb
    rw [hpar, List.map_map]
    exact (slotW_params (Nat.blt_eq.mp this)).symm
  rw [addr_eq, CCell.addrW, CCell.addrW, hv]

/-- **Milestone 1's statement, a special case**: on a path entering no call, of a function with no
precondition run, `ReadsOkC` is `ReadsWritten`. -/
theorem readsWritten_of_C {sigOf : String → HSig} {H : HCert} {σ : Val} {f : Fn}
    (hpar : f.params = (List.range f.params.length).map V.n) (hpov : preOver f.params.length H.sig.pre = true)
    (hR : H.sig.preR = []) {es : List Ev} (hnc : ∀ g a r, Ev.call g a r ∉ es)
    (h : ReadsOkC sigOf H σ (f.params.map σ) es) : ReadsWritten H σ es := by
  intro es1 a es2 x he hr
  rcases h es1 (.atom a) es2 he x hr with (⟨c, hc, hx⟩ | ⟨r, hr', -⟩) | ⟨e, he1, hx⟩
  · exact Or.inl ⟨c, hc, by rw [← addr_pre hpar hpov hc, hx]⟩
  · rw [hR] at hr'; simp at hr'
  · cases e with
    | atom b => exact Or.inr ⟨b, he1, hx⟩
    | call g a' r => exact absurd (by rw [he]; exact List.mem_append_left _ he1) (hnc g a' r)
    | inK _ => exact hx.elim
    | skip _ _ => exact hx.elim

end

end LeanVM.Guest.CoreMode
