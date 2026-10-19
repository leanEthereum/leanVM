/-
  LeanVM.Guest.B1.VerifySub.CBlocks

  The templates of `verify_sub`'s body, complete: `fs_next`, `squeeze`, and valuations set on a
  range.
-/

module

public import LeanVM.Guest.B1.VerifySub.CData
public import LeanVM.Guest.B1.Uniform

/-!
# Complete templates

* `upds_n`: an updated valuation, evaluated;
* `setv_ext`: `setv σ b n f` changes `σ` only on `b ..< b + n`;
* `completes_fsNextT`, `completes_squeezeT`: an `fs_next` block and a `squeeze` block complete
  with their honest values (`fsVals`, `sqVals`), from a state of `cv`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem upds_n (σ : Val) (k : ℕ) (e : E) (l : List (ℕ × E)) (j : ℕ) :
    upds σ ((k, e) :: l) (.n j) = if j = k then e else upds σ l (.n j) := by
  split
  · subst j; exact upds_cons_self σ k e l
  · exact upds_cons_ne σ e l (by assumption)

/-- Evaluate an updated valuation at literal value numbers. -/
macro "vs_ev" : tactic =>
  `(tactic| simp only [upds_n, upds_nil, Nat.reduceEqDiff, ↓reduceIte])

/-- A conjunct the evaluation left as `True` or as a reflexive equation. -/
macro "vs_triv" : tactic => `(tactic| first | trivial | rfl)

theorem setv_ext (σ : Val) (b n : ℕ) (f : ℕ → E) : Ext b (b + n) σ (setv σ b n f) := by
  intro v hv
  unfold setv
  split
  · rename_i h
    exact absurd (by cases v; simp_all) (hv v.idx h.2.2.1 h.2.2.2)
  · rfl

/-- A block completes with a valuation set on its range. -/
theorem completes_setv {lo n : ℕ} {ss : List Stmt} {σ : Val} {Post : Val → Prop} (f : ℕ → E)
    (hh : ∀ (next : Prop) (kret : List E → Prop), next →
      Stmt.HoldsList C rd (setv σ lo n f) ss next kret)
    (hp : Post (setv σ lo n f)) : Completes C rd lo (lo + n) ss σ Post :=
  ⟨setv σ lo n f, setv_ext σ lo n f, hp, hh⟩

/-- The value of `V.n k` below the range of `setv`. -/
theorem setv_below {σ : Val} {b n : ℕ} {f : ℕ → E} {v : V} (hv : ∃ k < b, v = .n k) :
    setv σ b n f v = σ v := by
  obtain ⟨k, hk, rfl⟩ := hv; exact set_n_lt hk

/-- A block completing, then an atom over values it leaves. -/
theorem _root_.LeanVM.Guest.B1.Sig.Completes.append_atom {lo hi : ℕ} {xs : List Stmt} {a : Atom} {σ : Val} {P Q : Val → Prop}
    (h : Completes C rd lo hi xs σ P) (ha : ∀ σ', P σ' → a.Holds rd σ' ∧ Q σ') :
    Completes C rd lo hi (xs ++ [.atom a]) σ Q := by
  obtain ⟨σ', he, hp, hh⟩ := h
  refine ⟨σ', he, (ha σ' hp).2, fun next kret hn => ?_⟩
  rw [holdsList_append]
  exact hh _ kret ⟨(ha σ' hp).1, hn⟩

/-- A block completing keeps the values below its range. -/
theorem _root_.LeanVM.Guest.B1.Sig.Completes.keep {lo hi : ℕ} {ss : List Stmt} {σ : Val} {P : Val → Prop} {l : List (ℕ × E)}
    (h : Completes C rd lo hi ss σ P) (hl : Fixes σ l) (hlo : ∀ p ∈ l, p.1 < lo) :
    Completes C rd lo hi ss σ (fun σ' => P σ' ∧ Fixes σ' l) := by
  obtain ⟨σ', he, hp, hh⟩ := h
  exact ⟨σ', he, ⟨hp, hl.of_ext he hlo⟩, hh⟩

theorem _root_.LeanVM.Guest.B1.Sig.Completes.post {lo hi : ℕ} {ss : List Stmt} {σ : Val} {P Q : Val → Prop}
    (h : Completes C rd lo hi ss σ P) (hpq : ∀ σ', Ext lo hi σ σ' → P σ' → Q σ') :
    Completes C rd lo hi ss σ Q := by
  obtain ⟨σ', he, hp, hh⟩ := h
  exact ⟨σ', he, hpq σ' he hp, hh⟩

/-- One fresh value set by a hint. -/
theorem completes_hint {k : ℕ} {h : Hint} {σ : Val} {Post : Val → Prop} (e : E)
    (hp : Post (upds σ [(k, e)])) : Completes C rd k (k + 1) [.atom (.hint h)] σ Post :=
  completes_upds [(k, e)] (by simp) (fun _ _ hn => ⟨trivial, hn⟩) hp

/-! ## `fs_next` -/

/-- The honest values of an `fs_next` block from its first, the word read. -/
def fsNextVals (x : E) (cv : Digest) : ℕ → E
  | 0 => x
  | k + 1 => fsVals x cv 1 k

/-- **`fs_next` completes**: from a state of `cv`, with `x` at the cursor's offset `j`, the block
reads `x` and its state cells become `obsCv cv x`'s. -/
theorem completes_fsNextT {s0 s1 cur : V} {j b : ℕ} {σ : Val} {cv : Digest} {x : E}
    {Post : Val → Prop} (hs0 : ∃ k < b, s0 = .n k) (hs1 : ∃ k < b, s1 = .n k)
    (hcur : ∃ k < b, cur = .n k) (hcv : (σ s0, σ s1) = digestScalars cv)
    (hx : LoadHolds rd (σ cur) j x)
    (hp : ∀ σ', Ext b (b + 15) σ σ' → σ' (.n b) = x →
      (σ' (.n (b + 13)), σ' (.n (b + 14))) = digestScalars (obsCv cv x) → Post σ') :
    Completes C rd b (b + 15) (fsNextT s0 s1 cur j b) σ Post := by
  refine completes_setv (fsNextVals x cv) (fun next kret hn => ?_) (hp _ (setv_ext σ b 15 _)
    (by rw [set_n_in (by omega) (by omega)]; simp [fsNextVals]) ?_)
  · rw [holds_fsNextT]
    refine ⟨⟨?_, cv, by rw [setv_below hs0, setv_below hs1]; exact hcv, fun k h1 h2 => ?_⟩, hn⟩
    · rw [setv_below hcur, set_n_in (by omega) (by omega)]; simpa [fsNextVals] using hx
    · rw [set_n_in (by omega) (by omega), set_n_in (k := b) (by omega) (by omega)]
      simp only [Nat.sub_self, fsNextVals, show b + 1 + k - b = k + 1 by omega]
  · rw [set_n_in (by omega) (by omega), set_n_in (by omega) (by omega),
      show b + 13 - b = 12 + 1 by omega, show b + 14 - b = 13 + 1 by omega]
    simp only [fsNextVals, fsVals, absorbCv_one]

/-! ## `squeeze` -/

/-- **`squeeze` completes**: from a state of `cv`, the new state is `sqCv cv`'s and the challenge
`challengeOf (sqCv cv)`. -/
theorem completes_squeezeT {s0 s1 : V} {b : ℕ} {σ : Val} {cv : Digest} {Post : Val → Prop}
    (hs0 : ∃ k < b, s0 = .n k) (hs1 : ∃ k < b, s1 = .n k)
    (hcv : (σ s0, σ s1) = digestScalars cv)
    (hp : ∀ σ', Ext b (b + 14) σ σ' →
      (σ' (.n (b + 5)), σ' (.n (b + 6))) = digestScalars (sqCv cv) →
      σ' (.n (b + 13)) = challengeOf (sqCv cv) → Post σ') :
    Completes C rd b (b + 14) (squeezeT s0 s1 b) σ Post := by
  refine completes_setv (sqVals cv) (fun next kret hn => ?_) (hp _ (setv_ext σ b 14 _) ?_ ?_)
  · rw [holds_squeezeT]
    refine ⟨⟨cv, by rw [setv_below hs0, setv_below hs1]; exact hcv, fun k hk => ?_⟩, hn⟩
    rw [set_n_in (by omega) (by omega), show b + k - b = k by omega]
  · rw [set_n_in (by omega) (by omega), set_n_in (by omega) (by omega),
      show b + 5 - b = 5 by omega, show b + 6 - b = 6 by omega]
    simp only [sqVals, sqStateVals, absorbCv_sq]
  · rw [set_n_in (by omega) (by omega), show b + 13 - b = 13 by omega]
    rfl

/-! ## Range checks and group 1's callees -/

/-- A range check `log x < K` on `x = g^e`, with the chosen auxiliary words. -/
theorem rc_holds {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {K e : ℕ} (hK1 : 1 ≤ K) (hK : K ≤ 2 ^ κ)
    (he : e < K) {σ : Val} {x y t1 t2 k : V} (hx : σ x = gen ^ e)
    (hy : σ y = (rcAux Lm (gen ^ e) K).1) (ht1 : σ t1 = (rcAux Lm (gen ^ e) K).2.1)
    (ht2 : σ t2 = (rcAux Lm (gen ^ e) K).2.2) (hk : σ k = gen ^ (K - 1)) :
    (Atom.rangeCheck x y t1 t2 k).Holds Lm.read σ := by
  obtain ⟨l1, h2, l3⟩ := rc_complete hκ Lm hK1 hK he
  simp only [Atom.Holds]
  rw [hx, hy, ht1, ht2, hk]
  exact ⟨l1, (gen_pow_eq_ofK (K - 1)).trans h2, l3⟩


/-- A range check `log x < K` on `x = g^e`, on a memory defined below `2^k`. -/
theorem rc_holds_low {k : ℕ} {rd : Reader} (hl : LowDef k rd) {K e : ℕ} (hK : K ≤ 2 ^ k)
    (he : e < K) {σ : Val} {x y t1 t2 kv : V} (hx : σ x = gen ^ e) (hy : σ y = (rcLow rd e K).1)
    (ht1 : σ t1 = (rcLow rd e K).2.1) (ht2 : σ t2 = (rcLow rd e K).2.2) (hk : σ kv = gen ^ (K - 1)) :
    (Atom.rangeCheck x y t1 t2 kv).Holds rd σ := by
  obtain ⟨l1, h2, l3⟩ := rc_complete_low hl hK he
  simp only [Atom.Holds]
  rw [hx, hy, ht1, ht2, hk, gen_pow_eq_ofK e]
  exact ⟨l1, (gen_pow_eq_ofK (K - 1)).trans h2, l3⟩

theorem lowDef_memImage {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) : LowDef κ Lm.read := fun i hi => by
  have := (read_some_iff (by omega) Lm (gpow i) (Lm ⟨i, hi⟩)).mpr ⟨⟨i, hi⟩, rfl, rfl⟩
  rw [this]; rfl

/-- `g_power_of_word(E(N), g_squares)` at six bits, `N < 64`, over its honest bit buffer. -/
theorem gpw6_complete {rd : Reader} {lp sq p : E} (ht : ExpTables rd lp sq) {N : ℕ} (hN : N < 64)
    (hb : ∀ j < 6, LoadHolds rd p j (bitE (N.testBit j))) :
    coreProgram.Rel rd "g_power_of_word__L6" [eOfNat N, sq] [gen ^ N] := by
  have hk : kToNat ((eOfNat N).limb 0) = N := kToNat_eOfNat_limb0 (by omega)
  have hs : ReadsAt rd sq ((List.range 6).map fun j ↦ gen ^ 2 ^ j) := fun j hj => by
    simp only [List.length_map, List.length_range] at hj
    rw [List.getElem_map, List.getElem_range]
    exact (ht j (by unfold sizeBits; omega)).2
  refine g_power_of_word_L6_complete rd p _ _ ⟨eOfNat_isInK N, by rw [hk]; exact hN,
    by rw [hk]; exact hb, _, by simp, hs, ?_⟩
  rw [hk, gpw_pow ht (by unfold sizeBits; omega) (by simp) hs hN]

/-- `log2_ceil_in_the_exponent(g^N, …)`, floor `0`, over its honest buffers. -/
theorem log2L0_complete {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) {lp sq bp ps : E}
    (ht : ExpTables Lm.read lp sq) {N : ℕ} (hN : N < 2 ^ 34) (hl : log2Ceil N < 34)
    (hb : ∀ j < 34, LoadHolds Lm.read bp j (bitE (N.testBit j)))
    (hp : ∀ j ≤ 34, LoadHolds Lm.read ps j (eOfNat (N % 2 ^ j))) :
    coreProgram.Rel Lm.read "log2_ceil_in_the_exponent__L0_L34" [gen ^ N, lp, sq]
      [gen ^ log2Ceil N] :=
  log2_ceil_in_the_exponent_L0_L34_complete hκ hκ6 Lm ht bp ps _
    ⟨N, hN, rfl, by simpa using hl, hb, hp, by simp⟩

/-- `log2_ceil_in_the_exponent(g^N, …)`, floor `15`, over its honest buffers. -/
theorem log2L15_complete {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) {lp sq bp ps : E}
    (ht : ExpTables Lm.read lp sq) {N : ℕ} (hN : N < 2 ^ 34) (hl : max 15 (log2Ceil N) < 34)
    (hb : ∀ j < 34, LoadHolds Lm.read bp j (bitE (N.testBit j)))
    (hp : ∀ j ≤ 34, LoadHolds Lm.read ps j (eOfNat (N % 2 ^ j))) :
    coreProgram.Rel Lm.read "log2_ceil_in_the_exponent__L15_L34" [gen ^ N, lp, sq]
      [gen ^ max 15 (log2Ceil N)] :=
  log2_ceil_in_the_exponent_L15_L34_complete hκ hκ6 Lm ht bp ps _ ⟨N, hN, rfl, hl, hb, hp, rfl⟩

end
end LeanVM.Guest.B1.VerifySub
