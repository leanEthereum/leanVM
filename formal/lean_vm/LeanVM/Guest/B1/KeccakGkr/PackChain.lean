/-
  LeanVM.Guest.B1.KeccakGkr.PackChain

  The pack rounds of a layer as the guest runs them: the eight-round loop's iterations, then the
  remainder loop's, one round each, are `packRunF` on the carried sponge.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PackLoop
public import LeanVM.Guest.B1.KeccakGkr.LayerSpec

/-!
# The pack rounds (`keccak_layer`, G:2699-2761)

`keccak_layer` writes the record `rounds` (the capacity after the squeeze, the cursor past the
product, the product's value at `s`, the scale `1`), runs
`keccak_layer__L1_loop0`/`keccak_layer__L0_loop0` for `xs = g^j`, `j < ⌊y/8⌋` (`Pack8Step`: eight
rounds on the coordinates `8j ..`), then `keccak_layer__L1_loop1`/`keccak_layer__L0_loop1` for `x1 =
g^k`, `k < y % 8`, on `rounds·g^⌊y/8⌋` (`PackRemStep`: one round on the coordinate `8⌊y/8⌋ + k`),
and reads the record `rounds·g^⌊y/8⌋·g^(y % 8)`.

* `PackInv j n`: after `j` records and `n` coordinates, the messages and challenges so far, the
  record `j`, and `packRunF` of the first `n` coordinates; `packInv_extend`: a chain of rounds
  (`EqChain`) from record `j` to record `j + 1` extends it;
* `pack_chain`: the records chain into `packRunF` of the claim's point, the messages read from the
  cursor and the challenges stored at `point`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- **A round of `packRunF` is `eqRound`**. -/
theorem packRunF_eqRound (r g1 g2 v sc : E) (rs : List E) (ms : List (E × E)) (s : Fs) :
    packRunF (r :: rs) ((g1, g2) :: ms) v sc s =
      (((packRunF rs ms (eqRound s g1 g2 r v sc).2.1 (eqRound s g1 g2 r v sc).2.2.1
          (eqRound s g1 g2 r v sc).2.2.2).1.1,
        (packRunF rs ms (eqRound s g1 g2 r v sc).2.1 (eqRound s g1 g2 r v sc).2.2.1
          (eqRound s g1 g2 r v sc).2.2.2).1.2.1,
        (eqRound s g1 g2 r v sc).1 :: (packRunF rs ms (eqRound s g1 g2 r v sc).2.1
          (eqRound s g1 g2 r v sc).2.2.1 (eqRound s g1 g2 r v sc).2.2.2).1.2.2),
        (packRunF rs ms (eqRound s g1 g2 r v sc).2.1 (eqRound s g1 g2 r v sc).2.2.1
          (eqRound s g1 g2 r v sc).2.2.2).2) := by
  have e : (1 + r + (s.absorbAll [g1, g2] dsObserve).squeeze.1) *
      polyEval [v + r * sumE [g1, g2], g1, g2] (s.absorbAll [g1, g2] dsObserve).squeeze.1 =
      (eqRound s g1 g2 r v sc).2.1 := by
    simp only [eqRound, polyEval, sumE, List.foldl, List.foldr]
    ring
  have e' : sc * (1 + r + (s.absorbAll [g1, g2] dsObserve).squeeze.1) =
      (eqRound s g1 g2 r v sc).2.2.1 := by
    simp only [eqRound]
    ring
  simp only [packRunF]
  rw [e, e']
  rfl

/-- `packRunF` past its last round. -/
theorem packRunF_nil (v sc : E) (s : Fs) : packRunF [] [] v sc s = ((v, sc, []), s) := rfl

theorem loadHolds_rec_succ {rec : E} {j off : ℕ} {w : E} :
    LoadHolds rd (rec * gen ^ j) (1 + off) w ↔ LoadHolds rd (rec * gen ^ (j + 1)) off w := by
  rw [loadHolds_mul_gen_pow, loadHolds_mul_gen_pow, show j + (1 + off) = j + 1 + off by omega]

/-- `packRunF` over a prefix of rounds, then the rest. -/
theorem packRunF_append :
    ∀ (A rest : List E) (MA restM : List (E × E)) (v sc : E) (s : Fs), MA.length = A.length →
      packRunF (A ++ rest) (MA ++ restM) v sc s =
        (((packRunF rest restM (packRunF A MA v sc s).1.1 (packRunF A MA v sc s).1.2.1
            (packRunF A MA v sc s).2).1.1,
          (packRunF rest restM (packRunF A MA v sc s).1.1 (packRunF A MA v sc s).1.2.1
            (packRunF A MA v sc s).2).1.2.1,
          (packRunF A MA v sc s).1.2.2 ++ (packRunF rest restM (packRunF A MA v sc s).1.1
            (packRunF A MA v sc s).1.2.1 (packRunF A MA v sc s).2).1.2.2),
          (packRunF rest restM (packRunF A MA v sc s).1.1 (packRunF A MA v sc s).1.2.1
            (packRunF A MA v sc s).2).2)
  | [], rest, [], restM, v, sc, s, _ => by simp [packRunF_nil]
  | r :: A, rest, (g1, g2) :: MA, restM, v, sc, s, h => by
    have h' : MA.length = A.length := by simpa using h
    rw [List.cons_append, List.cons_append, packRunF_eqRound, packRunF_eqRound,
      packRunF_append A rest MA restM _ _ _ h']
    simp only [List.cons_append]
  | [], _, _ :: _, _, _, _, _, h | _ :: _, _, [], _, _, _, _, h => by simp at h

theorem capAt_unique {rec : E} {k : ℕ} {cap cap' : List E} (h : CapAt rd rec k krCap cap)
    (h' : CapAt rd rec k krCap cap') : cap = cap' := by
  apply List.ext_getElem (by rw [h.1, h'.1])
  intro j hj hj'
  exact loadHolds_unique (h.2 j hj) (h'.2 j hj')

theorem roundRec_unique {rec : E} {k : ℕ} {cap cap' : List E} {cur cur' cl cl' sc sc' : E}
    (h : RoundRec rd rec k cap cur cl sc) (h' : RoundRec rd rec k cap' cur' cl' sc') :
    cap = cap' ∧ cur = cur' ∧ cl = cl' ∧ sc = sc' :=
  ⟨capAt_unique h.1 h'.1, loadHolds_unique h.2.1 h'.2.1, loadHolds_unique h.2.2.1 h'.2.2.1,
    loadHolds_unique h.2.2.2 h'.2.2.2⟩

/-- A record written at offset `1` from `rec·g^j` is the record at `rec·g^(j+1)`. -/
theorem roundRec_succ {rec : E} {j : ℕ} {cap : List E} {cur cl sc : E}
    (h : RoundRec rd (rec * gen ^ j) 1 cap cur cl sc) :
    RoundRec rd (rec * gen ^ (j + 1)) 0 cap cur cl sc := by
  obtain ⟨⟨hl, hc⟩, h1, h2, h3⟩ := h
  refine ⟨⟨hl, fun i hi => ?_⟩, ?_, ?_, ?_⟩
  · have := hc i hi
    rw [show 1 + i * krCap = 1 + (0 + i * krCap) by omega, loadHolds_rec_succ] at this
    exact this
  · rw [show 0 + 5 * krCap = 5 * krCap by omega, ← loadHolds_rec_succ]; exact h1
  · rw [show 0 + 6 * krCap = 6 * krCap by omega, ← loadHolds_rec_succ]; exact h2
  · rw [show 0 + 7 * krCap = 7 * krCap by omega, ← loadHolds_rec_succ]; exact h3

theorem gen_pow_ne_one {h : ℕ} (h0 : 0 < h) (hlt : h < ordG) : 1 + gen ^ h ≠ 0 := by
  intro e
  have : gen ^ h = gen ^ 0 := by rw [pow_zero]; exact (e_add_eq_zero_iff.mp e).symm
  have := gen_pow_inj (by unfold ordG at hlt; omega) (by decide) this
  omega

theorem flatMap_pairs_length (msgs : List (E × E)) :
    (msgs.flatMap fun m ↦ [m.1, m.2]).length = 2 * msgs.length := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => simp [List.flatMap_cons, ih]; ring

/-- The invariant after `j` records and `n` coordinates: the messages and challenges so far, the
record `j`, and `packRunF` of the first `n` coordinates. -/
def PackInv (rd : Reader) (rec pt cur hv : E) (capS pts : List E) (j n : ℕ) : Prop :=
  ∃ (msgs : List (E × E)) (chs cap : List E) (cl sc : E), msgs.length = n ∧
    chs.length = n ∧ ReadsAt rd cur (msgs.flatMap fun m ↦ [m.1, m.2]) ∧ ReadsAt rd pt chs ∧
    RoundRec rd (rec * gen ^ j) 0 cap (cur * gen ^ (2 * n)) cl sc ∧
    packRunF (pts.take n) msgs hv 1 ⟨capS, []⟩ = ((cl, sc, chs), ⟨cap, []⟩)

theorem packInv_zero {rec pt cur hv : E} {capS pts : List E} (h0 : RoundRec rd rec 0 capS cur hv 1) :
    PackInv rd rec pt cur hv capS pts 0 0 :=
  ⟨[], [], capS, hv, 1, rfl, rfl, readsAt_nil _ _, readsAt_nil _ _, by simpa using h0, rfl⟩

/-- **A chain of rounds extends the invariant**: from record `j`, the coordinates `n ..` of the
point, the messages at the cursor and the challenges at `point·g^n`, to record `j + 1`. -/
theorem packInv_extend {rec pt cur hv : E} {capS pts : List E} {j n : ℕ}
    (hI : PackInv rd rec pt cur hv capS pts j n) {rs : List E} {ms : List (E × E)}
    {chs' cap0 cap' : List E} {cur0 cl0 sc0 cl' sc' : E}
    (hrec0 : RoundRec rd (rec * gen ^ j) 0 cap0 cur0 cl0 sc0)
    (hrs : ∀ k (hk : k < rs.length), pts[n + k]? = some rs[k]) (hlen : n + rs.length ≤ pts.length)
    (hms : ReadsAt rd cur0 (ms.flatMap fun m ↦ [m.1, m.2]))
    (hch : EqChain rs ms cl0 sc0 cap0 chs' cl' sc' cap') (hchs : ReadsAt rd (pt * gen ^ n) chs')
    (hnext : RoundRec rd (rec * gen ^ j) 1 cap' (cur0 * gen ^ (2 * rs.length)) cl' sc') :
    PackInv rd rec pt cur hv capS pts (j + 1) (n + rs.length) := by
  obtain ⟨msgs, chs, cap, cl, sc, hml, hcl, hrm, hrc, hrec, hrun⟩ := hI
  obtain ⟨rfl, hcur, rfl, rfl⟩ := roundRec_unique hrec0 hrec
  obtain ⟨hmsl, hchl⟩ := packEqChain_length hch
  have htake : pts.take (n + rs.length) = pts.take n ++ rs := by
    apply List.ext_getElem?
    intro k
    rw [List.getElem?_take]
    rcases Nat.lt_or_ge k n with hk | hk
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take]
      simp [hk, show k < n + rs.length by omega]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_take, show min n pts.length = n by omega]
      rcases Nat.lt_or_ge k (n + rs.length) with hk' | hk'
      · simp only [hk', ↓reduceIte]
        have := hrs (k - n) (by omega)
        rw [show n + (k - n) = k by omega] at this
        rw [this, List.getElem?_eq_getElem (by omega)]
      · simp only [show ¬ k < n + rs.length by omega, ↓reduceIte]
        rw [List.getElem?_eq_none (by omega)]
  refine ⟨msgs ++ ms, chs ++ chs', cap', cl', sc', by simp [hml, hmsl], by simp [hcl, hchl], ?_, ?_,
    ?_, ?_⟩
  · rw [List.flatMap_append, readsAt_append, flatMap_pairs_length, hml]
    exact ⟨hrm, hcur ▸ hms⟩
  · rw [readsAt_append, hcl]
    exact ⟨hrc, hchs⟩
  · have := roundRec_succ hnext
    rw [hcur, mul_assoc, ← pow_add, show 2 * n + 2 * rs.length = 2 * (n + rs.length) by ring]
      at this
    exact this
  · rw [htake, packRunF_append _ _ _ _ _ _ _ (by simp [hml]; omega), hrun,
      packRunF_of_chain _ _ _ _ _ _ _ _ _ hch]

/-- The coordinates read at `pp·g^n` are the point's from `n`. -/
theorem coords_of_reads {pp : E} {pts rs : List E} {n : ℕ} (hpp : ReadsAt rd pp pts)
    (hr : ReadsAt rd (pp * gen ^ n) rs) (hlen : n + rs.length ≤ pts.length) :
    ∀ k (hk : k < rs.length), pts[n + k]? = some rs[k] := by
  intro k hk
  have h1 := hr k hk
  rw [loadHolds_mul_gen_pow] at h1
  rw [List.getElem?_eq_getElem (by omega), loadHolds_unique (hpp _ (by omega)) h1]

theorem gen_pow_pow (j m : ℕ) : (gen ^ j) ^ m = gen ^ (m * j) := by rw [← pow_mul, mul_comm]

/-- **An iteration of the eight-round loop extends the invariant.** -/
theorem packInv_succ8 {rec pp pt cur hv : E} {capS pts : List E} {j : ℕ}
    (hI : PackInv rd rec pt cur hv capS pts j (8 * j)) (hS : Pack8Step rd rec pp pt (gen ^ j))
    (hpp : ReadsAt rd pp pts) (hj : 8 * j + 8 ≤ pts.length) :
    PackInv rd rec pt cur hv capS pts (j + 1) (8 * (j + 1)) := by
  obtain ⟨cap, cur0, cl0, sc0, rs, ms, chs, cl', sc', cap', hrec0, hrl, hrr, hms, hch, hchs, hnext⟩ :=
    hS
  rw [gen_pow_pow] at hrr hchs
  have := packInv_extend hI hrec0 (coords_of_reads hpp hrr (by omega)) (by omega) hms hch hchs
    (by rw [hrl]; exact hnext)
  rwa [hrl, show 8 * j + 8 = 8 * (j + 1) by ring] at this

/-- **An iteration of the remainder loop extends the invariant.** -/
theorem packInv_succR {rec pp pt cur hv : E} {capS pts : List E} {s k : ℕ}
    (hI : PackInv rd rec pt cur hv capS pts (s + k) (8 * s + k))
    (hS : PackRemStep rd (rec * gen ^ s) (pp * gen ^ (8 * s)) (pt * gen ^ (8 * s)) (gen ^ k))
    (hpp : ReadsAt rd pp pts) (hk : 8 * s + k + 1 ≤ pts.length) :
    PackInv rd rec pt cur hv capS pts (s + k + 1) (8 * s + k + 1) := by
  obtain ⟨cap, cur0, cl0, sc0, r, g1, g2, hrec0, hr, hms, hS'⟩ := hS
  obtain ⟨hst, hnext⟩ := hS'
  rw [mul_assoc, ← pow_add] at hrec0 hr hst hnext
  have hrr : ReadsAt rd (pp * gen ^ (8 * s + k)) [r] := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    exact hr
  have hch : EqChain [r] [(g1, g2)] cl0 sc0 cap
      [(eqRound ⟨cap, []⟩ g1 g2 r cl0 sc0).1] (eqRound ⟨cap, []⟩ g1 g2 r cl0 sc0).2.1
      (eqRound ⟨cap, []⟩ g1 g2 r cl0 sc0).2.2.1 (eqRound ⟨cap, []⟩ g1 g2 r cl0 sc0).2.2.2.cap :=
    ⟨_, _, _, _, [], rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hchs : ReadsAt rd (pt * gen ^ (8 * s + k)) [(eqRound ⟨cap, []⟩ g1 g2 r cl0 sc0).1] := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    exact hst
  have := packInv_extend hI (by rwa [show s + k = s + k from rfl]) (coords_of_reads hpp hrr (by simp; omega))
    (by simp; omega) (by simpa using hms) hch hchs (by simpa using hnext)
  simpa using this

/-- **The pack rounds**: the loops' records chain into `packRunF` of the claim's point `pts`, the
messages read from the cursor and the challenges stored at `point`; the last record
(`rounds·step_g·rem_g`) holds its result. -/
theorem pack_chain {first : ℕ} (hfirst : first < 2)
    {rec pp pt sg rg cur hv curL vL scL : E} {capS pts capL : List E} {y : ℕ}
    (hsg : sg = gen ^ (y / krStep)) (hrg : rg = gen ^ (y % krStep)) (hy32 : y < 32)
    (hpts : pts.length = y) (hpp : ReadsAt rd pp pts)
    (h0 : RoundRec rd rec 0 capS cur hv 1) {tb : E}
    (hloop : IsInK (1 + sg) ∧
      (1 + sg ≠ 0 → coreProgram.Rel rd (packLoopName first) [1, sg, rec, pp, pt, tb] []))
    (hrem : IsInK (1 + rg) ∧
      (1 + rg ≠ 0 → coreProgram.Rel rd (remLoopName first) [1, rg, rec * sg, pp * sg ^ 8, tb,
        pt * sg ^ 8] []))
    (hlast : RoundRec rd (rec * sg * rg) 0 capL curL vL scL) :
    ∃ (msgs : List (E × E)) (chs : List E), msgs.length = y ∧
      ReadsAt rd cur (msgs.flatMap fun m ↦ [m.1, m.2]) ∧ ReadsAt rd pt chs ∧ chs.length = y ∧
      curL = cur * gen ^ (2 * y) ∧ (packRunF pts msgs hv 1 ⟨capS, []⟩).1 = (vL, scL, chs) ∧
      (packRunF pts msgs hv 1 ⟨capS, []⟩).2 = ⟨capL, []⟩ := by
  have hlt : ∀ m, m < 32 → m < ordG := fun m hm ↦ by unfold ordG; omega
  have hsteps : ∀ j < y / krStep, Pack8Step rd rec pp pt (gen ^ j) := by
    intro j hj
    have hne := gen_pow_ne_one (h := y / krStep) (by omega) (hlt _ (by simp [krStep]; omega))
    obtain ⟨fn, hf, hb, hp⟩ := find_pack8 hfirst
    have hrel := hloop.2 (by rw [hsg]; exact hne)
    exact loop_sound (P := coreProgram) (f := packLoopName first) (ps := [sg, rec, pp, pt, tb])
      (N := sg) (m := y / krStep) (B := Pack8Step rd rec pp pt)
      (fun d x h' => pack8_step hf hb hp d x sg rec pp pt tb h') hsg (hlt _ (by simp [krStep]; omega))
      0 (by rw [pow_zero]; exact hrel) j (Nat.zero_le _) hj
  have hrems : ∀ k < y % krStep, PackRemStep rd (rec * sg) (pp * sg ^ 8) (pt * sg ^ 8) (gen ^ k) := by
    intro k hk
    have hne := gen_pow_ne_one (h := y % krStep) (by omega) (hlt _ (by simp [krStep]; omega))
    obtain ⟨fn, hf, hb, hp⟩ := find_packRem hfirst
    have hrel := hrem.2 (by rw [hrg]; exact hne)
    exact loop_sound (P := coreProgram) (f := remLoopName first)
      (ps := [rg, rec * sg, pp * sg ^ 8, tb, pt * sg ^ 8]) (N := rg) (m := y % krStep)
      (B := PackRemStep rd (rec * sg) (pp * sg ^ 8) (pt * sg ^ 8))
      (fun d x h' => packRem_step hf hb hp d x rg _ _ tb _ h') hrg (hlt _ (by simp [krStep]; omega))
      0 (by rw [pow_zero]; exact hrel) k (Nat.zero_le _) hk
  have hinv8 : ∀ j ≤ y / krStep, PackInv rd rec pt cur hv capS pts j (8 * j) := by
    intro j hj
    induction j with
    | zero => exact packInv_zero h0
    | succ j ih =>
      exact packInv_succ8 (ih (by omega)) (hsteps j (by omega)) hpp (by simp [krStep] at hj; omega)
  have hinvR : ∀ k ≤ y % krStep, PackInv rd rec pt cur hv capS pts (y / krStep + k)
      (8 * (y / krStep) + k) := by
    intro k hk
    induction k with
    | zero => exact hinv8 _ le_rfl
    | succ k ih =>
      have := packInv_succR (s := y / krStep) (k := k) (ih (by omega))
        (by rw [← gen_pow_pow, ← hsg]; exact hrems k (by omega)) hpp
        (by simp [krStep] at hk ⊢; omega)
      simpa [Nat.add_assoc] using this
  obtain ⟨msgs, chs, cap, cl, sc, hml, hcl, hrm, hrc, hrec, hrun⟩ := hinvR _ le_rfl
  have hy : 8 * (y / krStep) + y % krStep = y := by simp only [krStep]; omega
  rw [hy] at hml hcl hrec hrun
  rw [hsg, hrg, mul_assoc, ← pow_add] at hlast
  obtain ⟨rfl, hcur, rfl, rfl⟩ := roundRec_unique hlast hrec
  rw [List.take_of_length_le (by omega)] at hrun
  exact ⟨msgs, chs, hml, hrm, hrc, hcl, hcur, by rw [hrun], by rw [hrun]⟩

end
end LeanVM.Guest.B1.VerifySub
