/-
  LeanVM.Guest.B1.VsC.ColSelC

  `column_selector` completes, layout-free, from its template.
-/

module

public import LeanVM.Guest.B1.VsC.Straight0
public import LeanVM.Guest.B1.Stack.ColSel
public import LeanVM.Guest.Memory.LowDef
import LeanVM.Guest.Value.FieldBits

/-!
# `column_selector`, complete

`column_selector__L{n}_L{κ}(offset, sel_eq, sel_g)` (the template `cselBody n κ`, the guest stream's
`ColSel.lean`) on `offset = g^idx`, `idx < 2^(4n)` a multiple of `2^κ`, on a memory defined below
`2^k`, `4 ≤ k` (its range checks read there), holding `selector_tables`' entries at `sel_eq` and the
nibble shares at `sel_g` (`CselPre`): its forward evaluation (`fwdVal`) on the oracle of `idx`'s
nibbles holds every atom, the digits hint is exact, and it returns
`Π_{κ ≤ t < 4n} selBit p p1 idx t`, popping nothing (`csel_complete0`). The template's shape facts
are one kernel decision over every specialization (`cselOk_all`). With no words of its own
(`CallCompletes0`, `csel_complete0`), it transfers to the placed form.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Stack
open LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- What `column_selector` reads: `selector_tables`' entries of the words `p`, `p1` at `se`, and the
nibble shares `g^(u·16^j)` at `sg`. -/
def CselPre (n : ℕ) (p p1 : ℕ → E) (se sg : E) (rd : Reader) : Prop :=
  (∀ j < n, ∀ w < 4, ∀ k < 2 ^ (w + 1),
    LoadHolds rd se (32 * j + selOff w + k * 2 ^ (3 - w)) (selLev p p1 j w k)) ∧
  ∀ j < 9, ∀ u < 16, LoadHolds rd sg (16 * j + u) (gen ^ (u * 16 ^ j))

/-- The template's shape: it returns, pops nothing, its forward evaluation's pattern passes with no
store. -/
def cselOk (n κ : ℕ) : Bool :=
  (retOf (cselBody n κ)).isSome && (atomsOf (cselBody n κ)).all atomQuiet &&
    (chk 3 (cselBody n κ)).isSome && (storesOf 3 (cselBody n κ)).isEmpty

theorem cselOk_all : ∀ n, 4 ≤ n → n ≤ 8 → ∀ κ, κ ≤ 30 → cselOk n κ = true := by
  have h : ((List.range 5).all fun n => (List.range 31).all fun κ => cselOk (n + 4) κ) = true := by
    decide +kernel
  intro n h4 h8 κ hκ
  have := List.all_eq_true.mp (List.all_eq_true.mp h (n - 4) (List.mem_range.mpr (by omega))) κ
    (List.mem_range.mpr (by omega))
  rwa [Nat.sub_add_cancel h4] at this

/-! ## Arithmetic -/

/-- The offset is the sum of its nibbles from `j0` on. -/
theorem nibSum_nibOf (idx j0 : ℕ) : ∀ c, nibSum (fun i => nibOf idx (j0 + i)) j0 c + idx % 16 ^ j0 =
    idx % 16 ^ (j0 + c)
  | 0 => by simp [nibSum]
  | c + 1 => by
    rw [nibSum, Nat.add_right_comm, nibSum_nibOf idx j0 c, ← Nat.add_assoc j0 c 1, Nat.mod_pow_succ,
      nibOf, Nat.shiftRight_eq_div_pow, show 2 ^ (4 * (j0 + c)) = 16 ^ (j0 + c) by rw [pow_mul]; rfl,
      mul_comm]

theorem rdAt_of_load {rd : Reader} {p v : E} {off : ℕ} (h : LoadHolds rd p off v) : rdAt rd p off = v := by
  rw [rdAt, h.2]; rfl

/-- A load through `p` whose word the memory holds is that word, and holds. -/
theorem good_load {rd : Reader} {w : ℕ → E} {σ : Val} {d p : V} {off : ℕ} {v : E}
    (hg : Good rd [] w σ (.load d p off)) (hv : LoadHolds rd (σ p) off v) :
    σ d = v ∧ (Atom.load d p off).Holds rd σ := by
  have := good_load_eq hv hg (by simp)
  exact ⟨this, by show LoadHolds rd (σ p) off (σ d); rw [this]; exact hv⟩

/-- A range check of `g^e`, `e < 16`, against `g^15` holds on a memory defined below `2^k`. -/
theorem good_rc {k : ℕ} (hk : 4 ≤ k) {rd : Reader} (hl : LowDef k rd) {w : ℕ → E} {σ : Val}
    {x : V} {b : ℕ} {e : ℕ} (he : e < 16) (hx : σ x = gen ^ e) (hb : σ (.n b) = csW 15)
    (hg : Good rd [] w σ (.rangeCheck x (.n (b + 1)) (.n (b + 2)) (.n (b + 3)) (.n b))) :
    (Atom.rangeCheck x (.n (b + 1)) (.n (b + 2)) (.n (b + 3)) (.n b)).Holds rd σ := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hlt : (V.n b).idx < (V.n (b + 1)).idx := by show b < b + 1; omega
  simp only [hlt, ↓reduceIte] at h3
  have h16 : 16 ≤ 2 ^ k := le_trans (by decide) (Nat.pow_le_pow_right (by decide) hk)
  have hy : σ (.n (b + 1)) = gen ^ (15 - e) := by
    rw [h3, hb, hx, csW_eq (by decide), show (15 : ℕ) = (15 - e) + e by omega, pow_add,
      mul_inv_cancel_right₀ (gen_pow_ne_zero e), Nat.add_sub_cancel]
  have lx := loadHolds_low hl (i := e) (by omega)
  have ly := loadHolds_low hl (i := 15 - e) (by omega)
  rw [← gen_pow_eq_ofK] at lx ly
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, hx, rdAt_of_load lx]; exact lx
  · rw [hy, hb, hx, csW_eq (by decide), ← pow_add, Nat.add_sub_cancel' (by omega)]
  · rw [h2, hy, rdAt_of_load ly]; exact ly

/-! ## A digit -/

section Digit

variable {k : ℕ} {rd : Reader} {w : ℕ → E} {σ : Val} {j0 κ c : ℕ}

theorem cselB_lt (c i : ℕ) (hi : i ≠ 0) : cselSel c (i - 1) < cselB c i + 6 ∧
    cselReb c (i - 1) < cselB c i + 9 ∧ 3 + i < cselB c i + 4 ∧ cselSel c i = cselB c i + 6 ∧
      cselReb c i = cselB c i + 9 := by
  unfold cselSel cselReb cselB; split_ifs <;> omega

/-- **Digit `0`**: its atoms hold, its selector entry and share are the words read. -/
theorem cselDigit0_holds (hk : 4 ≤ k) (hl : LowDef k rd)
    (hg : ∀ a, Stmt.atom a ∈ cselDigit j0 κ c 0 → Good rd [] w σ a) {e : ℕ} (he : e < 16)
    (h3 : σ (.n 3) = gen ^ e) {v5 v7 : E}
    (hv5 : LoadHolds rd (σ (.n 1)) (e + (32 * j0 + selOff (4 * j0 + 3 - κ))) v5)
    (hv7 : LoadHolds rd (σ (.n 2)) (e + 16 * j0) v7) :
    (∀ a, Stmt.atom a ∈ cselDigit j0 κ c 0 → a.Holds rd σ ∧ a.Exact rd σ) ∧ σ (.n (cselSel c 0)) = v5 ∧
      σ (.n (cselReb c 0)) = v7 := by
  simp only [cselDigit, ↓reduceIte, Nat.add_zero, cselB] at hg ⊢
  have g0 := hg (.const (.n (3 + c)) (csW 15)) List.mem_cons_self
  have g1 := hg (.rangeCheck (.n 3) (.n (3 + c + 1)) (.n (3 + c + 1 + 1)) (.n (3 + c + 1 + 2)) (.n (3 + c)))
    (by simp [csRc])
  have g2 := hg (.mul (.n (3 + c + 4)) (.n 1) (.n 3)) (by simp [osMul])
  have g3 := hg (.load (.n (3 + c + 5)) (.n (3 + c + 4)) (32 * j0 + selOff (4 * j0 + 3 - κ))) (by simp)
  have g4 := hg (.mul (.n (3 + c + 6)) (.n 2) (.n 3)) (by simp [osMul])
  have g5 := hg (.load (.n (3 + c + 7)) (.n (3 + c + 6)) (16 * j0)) (by simp)
  have e0 : σ (.n (3 + c)) = csW 15 := g0
  have m2 := good_mul_eq g2 (by show 1 < 3 + c + 4; omega) (by show 3 < 3 + c + 4; omega)
  have m4 := good_mul_eq g4 (by show 2 < 3 + c + 6; omega) (by show 3 < 3 + c + 6; omega)
  obtain ⟨l3, a3⟩ := good_load g3 (by rw [m2, h3, loadHolds_mul_gen_pow]; exact hv5)
  obtain ⟨l5, a5⟩ := good_load g5 (by rw [m4, h3, loadHolds_mul_gen_pow]; exact hv7)
  refine ⟨fun a ha => ?_, by simpa [cselSel, show 3 + c + 5 = c + 8 by omega] using l3,
    by simpa [cselReb, show 3 + c + 7 = c + 10 by omega] using l5⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Stmt.atom.injEq, osCst, csRc, osMul] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨e0, trivial⟩
  · exact ⟨good_rc hk hl he h3 e0 g1, trivial⟩
  · exact ⟨m2, trivial⟩
  · exact ⟨a3, trivial⟩
  · exact ⟨m4, trivial⟩
  · exact ⟨a5, trivial⟩

/-- **Digit `i ≥ 1`**: its atoms hold, its selector and share multiply the running ones. -/
theorem cselDigitS_holds (hk : 4 ≤ k) (hl : LowDef k rd) {i : ℕ} (hi : i ≠ 0)
    (hg : ∀ a, Stmt.atom a ∈ cselDigit j0 κ c i → Good rd [] w σ a) {e : ℕ} (he : e < 16)
    (h3 : σ (.n (3 + i)) = gen ^ e) {v5 v8 : E}
    (hv5 : LoadHolds rd (σ (.n 1)) (e + (32 * (j0 + i) + 16)) v5)
    (hv8 : LoadHolds rd (σ (.n 2)) (e + 16 * (j0 + i)) v8) :
    (∀ a, Stmt.atom a ∈ cselDigit j0 κ c i → a.Holds rd σ ∧ a.Exact rd σ) ∧
      σ (.n (cselSel c i)) = σ (.n (cselSel c (i - 1))) * v5 ∧
      σ (.n (cselReb c i)) = σ (.n (cselReb c (i - 1))) * v8 := by
  obtain ⟨hs, hr, h3b, hsi, hri⟩ := cselB_lt c i hi
  simp only [cselDigit, hi, ↓reduceIte] at hg ⊢
  set b := cselB c i
  have g0 := hg (.const (.n b) (csW 15)) List.mem_cons_self
  have g1 := hg (.rangeCheck (.n (3 + i)) (.n (b + 1)) (.n (b + 1 + 1)) (.n (b + 1 + 2)) (.n b))
    (by simp [csRc])
  have g2 := hg (.mul (.n (b + 4)) (.n 1) (.n (3 + i))) (by simp [osMul])
  have g3 := hg (.load (.n (b + 5)) (.n (b + 4)) (32 * (j0 + i) + 16)) (by simp)
  have g4 := hg (.mul (.n (b + 6)) (.n (cselSel c (i - 1))) (.n (b + 5))) (by simp [osMul])
  have g5 := hg (.mul (.n (b + 7)) (.n 2) (.n (3 + i))) (by simp [osMul])
  have g6 := hg (.load (.n (b + 8)) (.n (b + 7)) (16 * (j0 + i))) (by simp)
  have g7 := hg (.mul (.n (b + 9)) (.n (cselReb c (i - 1))) (.n (b + 8))) (by simp [osMul])
  have e0 : σ (.n b) = csW 15 := g0
  have m2 := good_mul_eq g2 (by show 1 < b + 4; omega) (by show 3 + i < b + 4; omega)
  have m4 := good_mul_eq g4 (by show cselSel c (i - 1) < b + 6; omega) (by show b + 5 < b + 6; omega)
  have m5 := good_mul_eq g5 (by show 2 < b + 7; omega) (by show 3 + i < b + 7; omega)
  have m7 := good_mul_eq g7 (by show cselReb c (i - 1) < b + 9; omega) (by show b + 8 < b + 9; omega)
  obtain ⟨l3, a3⟩ := good_load g3 (by rw [m2, h3, loadHolds_mul_gen_pow]; exact hv5)
  obtain ⟨l6, a6⟩ := good_load g6 (by rw [m5, h3, loadHolds_mul_gen_pow]; exact hv8)
  refine ⟨fun a ha => ?_, by rw [hsi, m4, l3], by rw [hri, m7, l6]⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Stmt.atom.injEq, osCst, csRc, osMul] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨e0, trivial⟩
  · exact ⟨good_rc hk hl he h3 e0 g1, trivial⟩
  · exact ⟨m2, trivial⟩
  · exact ⟨a3, trivial⟩
  · exact ⟨m4, trivial⟩
  · exact ⟨m5, trivial⟩
  · exact ⟨a6, trivial⟩
  · exact ⟨m7, trivial⟩

end Digit

/-! ## The call -/

/-- The oracle of the digits hint: cell `3 + i` is `g` to `idx`'s nibble `j0 + i`. -/
noncomputable def cselW (idx j0 : ℕ) : ℕ → E := fun m => gen ^ nibOf idx (j0 + (m - 3))

/-- **`column_selector__L{n}_L{κ}`'s forward evaluation** on the oracle of `idx`'s nibbles: it takes
the arguments, returns the selector, and every atom holds and is exact. -/
theorem csel_fwd {k : ℕ} (hk : 4 ≤ k) {f : Fn} {n κ : ℕ} (hn : n ≤ 8)
    (hparams : f.params = [.n 0, .n 1, .n 2])
    (hbody : f.body = cselBody n κ) (hok : cselOk n κ = true) {idx : ℕ} (hidx : idx < 2 ^ (4 * n))
    (hal : 2 ^ κ ∣ idx) (p p1 : ℕ → E) (se sg : E) (rd : Reader) (hl : LowDef k rd)
    (hpre : CselPre n p p1 se sg rd) :
    f.params.map (fwdVal rd (cselW idx (κ / 4)) [gen ^ idx, se, sg] (cselBody n κ)) = [gen ^ idx, se, sg] ∧
      (∀ vs, retOf f.body = some vs → vs.map (fwdVal rd (cselW idx (κ / 4)) [gen ^ idx, se, sg] (cselBody n κ)) =
        [∏ t ∈ Finset.Ico κ (4 * n), selBit p p1 idx t]) ∧
      ∀ a, Stmt.atom a ∈ f.body → a.Holds rd (fwdVal rd (cselW idx (κ / 4)) [gen ^ idx, se, sg] (cselBody n κ)) ∧
        a.Exact rd (fwdVal rd (cselW idx (κ / 4)) [gen ^ idx, se, sg] (cselBody n κ)) := by
  simp only [cselOk, Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨⟨⟨hr, hq⟩, hc⟩, hS⟩ := hok
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨htab, hsh⟩ := hpre
  set j0 := κ / 4 with hj0
  set args : List E := [gen ^ idx, se, sg] with hargs
  set σ := fwdVal rd (cselW idx j0) args (cselBody n κ) with hσ
  have hg : ∀ a, Stmt.atom a ∈ cselBody n κ → Good rd [] (cselW idx j0) σ a := by
    intro a ha; have := fwd_good (rd := rd) (w := cselW idx j0) (args := args) hc' a ha
    rwa [show args.length = 3 from rfl, hS] at this
  have p0 : σ (.n 0) = gen ^ idx := fwd_param (args := args) hc' (i := 0) (by rw [hargs]; simp)
  have p1' : σ (.n 1) = se := fwd_param (args := args) hc' (i := 1) (by rw [hargs]; simp)
  have p2 : σ (.n 2) = sg := fwd_param (args := args) hc' (i := 2) (by rw [hargs]; simp)
  have hpar : f.params.map σ = [gen ^ idx, se, sg] := by
    rw [hparams]; simp only [List.map_cons, List.map_nil, p0, p1', p2]
  by_cases hnk : n ≤ κ / 4
  · -- no nibble: `idx = 0`, the selector is one
    have hi0 : idx = 0 := by
      have h1 : 2 ^ (4 * n) ≤ 2 ^ κ := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.eq_zero_of_dvd_of_lt hal (by omega)
    subst hi0
    have hb : cselBody n κ = [.atom (.hint (.digitsExp (.n 0) (4 * n) 0 4 (4 * (κ / 4)) none (.stack []))),
        osCst 3 (word 1 0), .atom (.assertEq (.n 3) (.n 0)), osCst 4 (word 1 0), .ret [.n 4]] := by
      simp [cselBody, cselBodyA, hnk]
    have c3 : σ (.n 3) = word 1 0 := hg (.const (.n 3) (word 1 0)) (by rw [hb]; simp)
    have c4 : σ (.n 4) = word 1 0 := hg (.const (.n 4) (word 1 0)) (by rw [hb]; simp)
    refine ⟨hpar, fun vs hvs => ?_, fun a ha => ?_⟩
    · rw [hbody, hb] at hvs; simp [retOf] at hvs; subst hvs
      simp [c4, word_one, Finset.Ico_eq_empty_of_le (show 4 * n ≤ κ by omega)]
    · rw [hbody] at ha
      have ha' := ha
      rw [hb] at ha'
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Stmt.atom.injEq, osCst, reduceCtorEq] at ha'
      rcases ha' with rfl | rfl | rfl | rfl
      · refine ⟨trivial, ⟨0, 4 * (κ / 4), by positivity, by rw [p0, gen_pow_eq_ofK], rfl, rfl⟩⟩
      · exact ⟨c3, trivial⟩
      · refine ⟨?_, trivial⟩
        show σ (.n 3) + σ (.n 0) = 0
        rw [e_add_eq_zero_iff, c3, p0, pow_zero, word_one]
      · exact ⟨c4, trivial⟩
  · set c := n - j0 with hc
    have hc1 : 1 ≤ c := by omega
    have hnk' : ¬ n ≤ j0 := hnk
    have hj9 : ∀ i < c, j0 + i < 9 := fun i hi => by omega
    set e : ℕ → ℕ := fun i => nibOf idx (j0 + i) with he_def
    have he : ∀ i, e i < 16 := fun i => Nat.mod_lt _ (by decide)
    have hbA : (cselBodyA n κ).1 = [.atom (.hint (.digitsExp (.n 0) (4 * n) c 4 (4 * j0) none
        (.stack ((List.range c).map fun i => .n (3 + i)))))] ++
        ((List.range c).map (cselDigit j0 κ c)).flatten ++
        [.atom (.assertEq (.n (cselReb c (c - 1))) (.n 0)),
          .atom (.copy (.n (cselB c c)) (.n (cselSel c (c - 1))))] := by
      simp [cselBodyA, hnk', ← hj0, ← hc]
    have hret : (cselBodyA n κ).2 = cselB c c := by simp [cselBodyA, hnk', ← hj0, ← hc]
    have hmemA : ∀ s, s ∈ (cselBodyA n κ).1 → s ∈ cselBody n κ := fun s hs => by
      rw [cselBody]; exact List.mem_append_left _ hs
    have hdig : ∀ i < c, ∀ a, Stmt.atom a ∈ cselDigit j0 κ c i → Stmt.atom a ∈ cselBody n κ :=
      fun i hi a ha => hmemA _ (by
        rw [hbA]; refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr
          ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ha⟩)))
    -- the digits
    have hd : ∀ i < c, σ (.n (3 + i)) = gen ^ e i := by
      intro i hi
      have := hg (.hint (.digitsExp (.n 0) (4 * n) c 4 (4 * j0) none
        (.stack ((List.range c).map fun i => .n (3 + i))))) (hmemA _ (by rw [hbA]; simp)) (.n (3 + i))
        (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
      rw [this]; simp [cselW, e]
    -- digit by digit
    have hD : ∀ i < c, (∀ a, Stmt.atom a ∈ cselDigit j0 κ c i → a.Holds rd σ ∧ a.Exact rd σ) ∧
        σ (.n (cselReb c i)) = gen ^ nibSum e j0 (i + 1) ∧
        σ (.n (cselSel c i)) = ∏ t ∈ Finset.Ico κ (4 * (j0 + i) + 4), selBit p p1 idx t := by
      intro i
      induction i with
      | zero =>
        intro h0
        set lo := κ - 4 * j0 with hlo
        have hlo4 : lo < 4 := by omega
        have hdv : 2 ^ lo ∣ e 0 := by
          show 2 ^ lo ∣ nibOf idx (j0 + 0)
          rw [Nat.add_zero, nibOf, Nat.shiftRight_eq_div_pow]
          obtain ⟨q, hq⟩ := hal
          rw [hq, show κ = 4 * j0 + lo by omega, pow_add, mul_assoc,
            Nat.mul_div_cancel_left _ (by positivity),
            show (16 : ℕ) = 2 ^ lo * 2 ^ (4 - lo) by rw [← pow_add, show lo + (4 - lo) = 4 by omega]; rfl,
            Nat.mul_mod_mul_left]
          exact dvd_mul_right _ _
        obtain ⟨kk, hkk⟩ := hdv
        have hk16 : kk < 2 ^ (3 - lo + 1) := by
          have := he 0; rw [hkk] at this
          rw [show 3 - lo + 1 = 4 - lo by omega]
          have h2 : 2 ^ lo * kk < 2 ^ lo * 2 ^ (4 - lo) := by
            rw [← pow_add, show lo + (4 - lo) = 4 by omega]; exact this
          exact Nat.lt_of_mul_lt_mul_left h2
        have ht := htab j0 (by omega) (3 - lo) (by omega) kk hk16
        rw [show 3 - (3 - lo) = lo by omega, show 32 * j0 + selOff (3 - lo) + kk * 2 ^ lo =
          e 0 + (32 * j0 + selOff (4 * j0 + 3 - κ)) by
            rw [show 4 * j0 + 3 - κ = 3 - lo by omega, hkk]; ring] at ht
        have hs := hsh j0 (hj9 0 h0) (e 0) (he 0)
        rw [Nat.add_comm] at hs
        obtain ⟨hA, hs0, hr0⟩ := cselDigit0_holds hk hl (fun a ha => hg a (hdig 0 h0 a ha)) (he 0)
          (by simpa using hd 0 h0) (by rw [p1']; exact ht) (by rw [p2]; exact hs)
        refine ⟨hA, by rw [hr0]; simp [nibSum], ?_⟩
        rw [hs0, selLev_nib p p1 idx j0 lo kk hlo4 (by rw [mul_comm, ← hkk]; rfl), Nat.add_zero,
          show 4 * j0 + lo = κ by omega]
        simp only [Nat.add_zero]
      | succ i ih =>
        intro hi
        obtain ⟨-, ihr, ihs⟩ := ih (by omega)
        have ht := htab (j0 + (i + 1)) (by omega) 3 (by decide) (e (i + 1)) (by simpa using he (i + 1))
        simp only [selOff, List.getD_cons_succ, List.getD_cons_zero, Nat.sub_self, pow_zero,
          mul_one] at ht
        rw [show 32 * (j0 + (i + 1)) + 16 + e (i + 1) = e (i + 1) + (32 * (j0 + (i + 1)) + 16) by ring] at ht
        have hs := hsh (j0 + (i + 1)) (hj9 _ hi) (e (i + 1)) (he _)
        rw [Nat.add_comm (16 * _)] at hs
        obtain ⟨hA, hs1, hr1⟩ := cselDigitS_holds hk hl (Nat.succ_ne_zero i)
          (fun a ha => hg a (hdig _ hi a ha)) (he _) (hd _ hi) (by rw [p1']; exact ht) (by rw [p2]; exact hs)
        refine ⟨hA, ?_, ?_⟩
        · rw [hr1, Nat.succ_sub_one, ihr, ← pow_add]; rfl
        · rw [hs1, Nat.succ_sub_one, ihs,
            selLev_nib p p1 idx (j0 + (i + 1)) 0 (e (i + 1)) (by decide) (by rw [pow_zero, mul_one]),
            Nat.add_zero, show 4 * (j0 + (i + 1)) = 4 * (j0 + i) + 4 by ring,
            Finset.prod_Ico_consecutive _ (by omega) (by omega)]
    -- the offset rebuilt
    have hsum : nibSum e j0 c = idx := by
      have h1 := nibSum_nibOf idx j0 c
      have h16 : (16 : ℕ) ^ j0 ∣ idx := dvd_trans (by
        rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; exact pow_dvd_pow 2 (by omega)) hal
      rw [Nat.mod_eq_zero_of_dvd h16, Nat.add_zero, show j0 + c = n by omega,
        Nat.mod_eq_of_lt (by rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; exact hidx)] at h1
      exact h1
    have hlast := hD (c - 1) (by omega)
    rw [Nat.sub_add_cancel hc1, hsum, show 4 * (j0 + (c - 1)) + 4 = 4 * n by omega] at hlast
    obtain ⟨-, hreb, hsel⟩ := hlast
    have hcopy : σ (.n (cselB c c)) = σ (.n (cselSel c (c - 1))) :=
      hg (.copy (.n (cselB c c)) (.n (cselSel c (c - 1)))) (hmemA _ (by rw [hbA]; simp))
    refine ⟨hpar, fun vs hvs => ?_, fun a ha => ?_⟩
    · rw [hbody] at hvs
      obtain ⟨ss, hB, -⟩ := retOf_spec hvs
      rw [cselBody] at hB
      have := (List.append_inj' hB rfl).2
      simp only [List.cons.injEq, Stmt.ret.injEq, and_true] at this
      subst this
      simp only [List.map_cons, List.map_nil, hret, hcopy, hsel]
    · have ha' : Stmt.atom a ∈ (cselBodyA n κ).1 := by
        rw [hbody, cselBody] at ha
        rcases List.mem_append.mp ha with h | h
        · exact h
        · simp at h
      rw [hbA] at ha'
      rcases List.mem_append.mp ha' with h | h
      · rcases List.mem_append.mp h with h | h
        · rw [List.mem_singleton, Stmt.atom.injEq] at h
          subst h
          refine ⟨trivial, idx, 4 * j0, hidx, by rw [p0, gen_pow_eq_ofK], rfl, ?_⟩
          show ((List.range c).map fun i => V.n (3 + i)).map σ = _
          rw [List.map_map]
          refine List.map_congr_left fun j hj => ?_
          have hj : j < c := List.mem_range.mp hj
          rw [Function.comp_apply, hd j hj, gen_pow_eq_ofK,
            ite_neg' (show ¬ 128 ≤ 4 * j0 + 4 * j by omega), show 4 * j0 + 4 * j = 4 * (j0 + j) by ring]
          rfl
        · obtain ⟨l, hl, hal'⟩ := List.mem_flatten.mp h
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
          exact (hD i (List.mem_range.mp hi)).1 a hal'
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, Stmt.atom.injEq] at h
        rcases h with rfl | rfl
        · refine ⟨?_, trivial⟩
          show σ _ + σ _ = 0
          rw [e_add_eq_zero_iff, hreb, p0]
        · exact ⟨hcopy, trivial⟩

/-- **`column_selector__L{n}_L{κ}` completes**, from its template: on `g^idx`, `idx < 2^(4n)` a
multiple of `2^κ`, a memory defined below `2^k`, `4 ≤ k`, holding the selector tables of `p`, `p1`
at `se` and the nibble shares at `sg`, it returns `Π_{κ ≤ t < 4n} selBit p p1 idx t`, quiet, with
no words of its own. -/
theorem csel_complete0 {k : ℕ} (hk : 4 ≤ k) {name : String} {f : Fn} {n κ : ℕ} (hn : n ≤ 8)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2])
    (hbody : f.body = cselBody n κ) (hok : cselOk n κ = true) {idx : ℕ} (hidx : idx < 2 ^ (4 * n))
    (hal : 2 ^ κ ∣ idx) (p p1 : ℕ → E) (se sg : E) :
    CallCompletes0 k name [gen ^ idx, se, sg] [∏ t ∈ Finset.Ico κ (4 * n), selBit p p1 idx t]
      (CselPre n p p1 se sg) PostQuiet := by
  have hok' := hok
  simp only [cselOk, Bool.and_eq_true] at hok'
  exact callCompletes0_straight_ex hfind (by rw [hbody, hok'.1.1.1, hok'.1.1.2]; rfl) fun rd hl hpre =>
    ⟨_, csel_fwd hk hn hparams hbody hok hidx hal p p1 se sg rd hl hpre⟩

end
end LeanVM.Guest.B1.VsC
