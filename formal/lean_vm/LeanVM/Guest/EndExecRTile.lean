/-
  LeanVM.Guest.EndExecRTile

  The tile families (`Res.TileDefs`), sound on the reference and at the honest frames.
-/

module

public import LeanVM.Guest.EndExecRF
public import LeanVM.Guest.EndExecRLift
public import LeanVM.Guest.Res.TileDefs
public import LeanVM.Guest.EndExecRExp

/-!
# Tiles

`tile_rres`: where `[n] = g^E`, `E = Σ m_k·a_k` and part `k`'s base holds `g^(a_k)` (`PartsAt`), the run
up to `E` lies in the tile's parts: a point `c < m_0·a_0` is offset `c % m_0` of run `c / m_0` of the
first part, a later one `c - m_0·a_0` of the parts past `x_0^(S·m_0)` (`tile_parts`, by induction);
for `E = 0` the run is empty. `ext_rres`: the point at `[n]`'s exponent is the extra point.
`ord_rres`: `g^(2^64 - 1) = 1`, so offsets compare modulo the order. `liftBack_rres`: a lift's
`[v] = g^k·[u]` read back.

At an honest frame: `cellPow_top` (a touched cell holds `g^e`, `e < 2^32`, `B1.Digest.load_gpow`),
`mulCells_top`, so `mulTile_top`; `TileAt` the sums of `tiles` at the honest frames, given to
`tileList_top`; `ext_top`, `liftBack_top` (`lifts_ok`). `tileFam_top_of`: the families from the
tiles' sums.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (cellJ fsN namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (Wit witOk frEx cellLt inFr tileParts tileRes tileShape cellPow mulCells mulTileB
  tiles tileListB extB ordB ordG liftBack tileFamB)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-- Part `k`'s base holds `g^(as k)`, each exponent below `2^62`. -/
def PartsAt (M : ℕ → E) (fp : ℕ) : List (Base × ℕ) → List ℕ → Prop
  | [], [] => True
  | (x, _) :: ps, a :: as => RBase M fp x (ofK (Parameters.g ^ a)) ∧ a < 2 ^ 62 ∧ PartsAt M fp ps as
  | _, _ => False

/-- The parts' exponents, each times its count of runs. -/
def partsSum : List (Base × ℕ) → List ℕ → ℕ
  | (_, m) :: ps, a :: as => m * a + partsSum ps as
  | _, _ => 0

/-- **A tile's sum at the honest frames** of function `j`: `[n] = g^E`, `E = 0` or the parts' sum. -/
def TileAt (A : String → FnAl) (j : ℕ) (n : Base) (ps : List (Base × ℕ)) : Prop :=
  ∀ (r : Ref) (K : Mode.Cert) (i : ℕ) (e : Bridge.Ent), r.Ok → TopAt A r K i e j → ∃ E < 2 ^ 62,
    RBase (refMem r.img) e.I.fp n (ofK (Parameters.g ^ E)) ∧
    (E = 0 ∨ ∃ as, PartsAt (refMem r.img) e.I.fp ps as ∧ E = partsSum ps as)

end

public section

section

variable {M : ℕ → E} {fp : ℕ}

theorem ofK_one_E : ofK (1 : K) = 1 := map_one (algebraMap K E)

/-- **A base inserted into a product**: its word to the power times the product's. -/
theorem rbs_insert {b : Base} {e : ℕ} {u : E} (hu : RBase M fp b u) :
    ∀ {l : List (Base × ℕ)} {w : E}, RBs M fp l w → RBs M fp (insertBs (b, e) l) (u ^ e * w)
  | [], w, hw => ⟨u, 1, hu, rfl, by rw [show w = 1 from hw]⟩
  | (b', e') :: l, w, ⟨u', w', hu', hw', hw⟩ => by
    unfold insertBs
    dsimp only
    split_ifs with hq hl
    · obtain rfl := Base.beq_eq hq
      exact ⟨u', w', hu', hw', by rw [hw, rbase_uniq hu hu', pow_add]; ring⟩
    · exact ⟨u, w, hu, ⟨u', w', hu', hw', hw⟩, rfl⟩
    · exact ⟨u', u ^ e * w', hu', rbs_insert hu hw', by rw [hw]; ring⟩

theorem rmono_ins {Q : Mono} {x : Base} {e : ℕ} {u vQ : E} (hu : RBase M fp x u) (hQ : RMono M fp Q vQ) :
    RMono M fp ⟨Q.fp, Q.k, insertBs (x, e) Q.bs⟩ (vQ * u ^ e) := by
  obtain ⟨w, hw, rfl⟩ := hQ
  exact ⟨u ^ e * w, rbs_insert hu hw, by ring⟩

theorem ridx_base {x : Base} {a y : ℕ} (hx : RBase M fp x (ofK (Parameters.g ^ a))) (ha : a < 2 ^ 62)
    (hy : RIdx M fp (.ex x 0) y) : y = a := by
  obtain ⟨v, e', hv, hve, he', rfl⟩ := hy
  rw [rbase_uniq hv hx] at hve
  have := ofK_gpow_inj (by omega) (by omega) hve
  omega

/-- **A point below the parts' sum lies in a part.** -/
theorem tile_parts {S d : ℕ} : ∀ {ps : List (Base × ℕ)} {as : List ℕ} {Q : Mono} {vQ : E},
    PartsAt M fp ps as → RMono M fp Q vQ → ∀ c < partsSum ps as,
    ∃ b ∈ tileParts S d Q ps, ∀ vb ylo yhi, RMono M fp b.q vb → RIdx M fp b.lo ylo → RIdx M fp b.hi yhi →
      ∃ j', ylo ≤ j' ∧ j' < yhi ∧
        vQ * ofK (Parameters.g ^ (S * c + d)) = vb * ofK (Parameters.g ^ (b.S * j' + b.d))
  | [], [], _, _, _, _, c, hc => absurd hc (by simp [partsSum])
  | [], _ :: _, _, _, h, _, _, _ => h.elim
  | _ :: _, [], _, _, h, _, _, _ => h.elim
  | (x, m) :: ps, a :: as, Q, vQ, ⟨hx, ha, hps⟩, hQ, c, hc => by
    simp only [partsSum] at hc
    by_cases hca : c < m * a
    · have hm : 0 < m := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hca
      refine ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨c % m, List.mem_range.mpr (Nat.mod_lt _ hm), rfl⟩),
        fun vb ylo yhi hvb hlo hhi ↦ ⟨c / m, ?_, ?_, ?_⟩⟩
      · change ylo = 0 at hlo; rw [hlo]; exact Nat.zero_le _
      · rw [ridx_base hx ha hhi]
        exact (Nat.div_lt_iff_lt_mul hm).mpr (by rw [mul_comm]; exact hca)
      · rw [rmono_uniq hQ hvb]
        have e : S * c + d = S * m * (c / m) + (d + S * (c % m)) := by
          nth_rw 1 [← Nat.div_add_mod c m]; ring
        rw [e]
    · obtain ⟨b, hb, h⟩ := tile_parts (S := S) (d := d) hps (rmono_ins (e := S * m) hx hQ) (c - m * a) (by omega)
      refine ⟨b, List.mem_append_right _ hb, fun vb ylo yhi hvb hlo hhi ↦ ?_⟩
      obtain ⟨j', h1, h2, h3⟩ := h vb ylo yhi hvb hlo hhi
      refine ⟨j', h1, h2, ?_⟩
      rw [← h3]
      have e : S * c + d = a * (S * m) + (S * (c - m * a) + d) := by
        have : c = m * a + (c - m * a) := by omega
        nth_rw 1 [this]; ring
      simp only [ofK_gpow]
      rw [e, pow_add, pow_mul]
      ring

/-- **A run cut into its tile's parts**: `[n] = g^E`, `E = 0` or the parts' sum. -/
theorem tile_rres {Q : Mono} {n : Base} {S d E : ℕ} {ps : List (Base × ℕ)}
    (hn : RBase M fp n (ofK (Parameters.g ^ E))) (hE : E < 2 ^ 62)
    (h : E = 0 ∨ ∃ as, PartsAt M fp ps as ∧ E = partsSum ps as) : RRes M fp (tileRes Q n S d ps) := by
  refine ⟨0, E, rfl, ⟨_, E, hn, rfl, hE, rfl⟩, fun vq hvq c _ hc ↦ ?_⟩
  rcases h with rfl | ⟨as, hps, rfl⟩
  · exact absurd hc (Nat.not_lt_zero _)
  · exact tile_parts hps hvq c hc

/-- **A run one point past another**: `[n] = g^E`. -/
theorem ext_rres {Q : Mono} {n : Base} {S d E : ℕ} (hn : RBase M fp n (ofK (Parameters.g ^ E)))
    (hE : E < 2 ^ 62) : RRes M fp (.sub ⟨Q, .num 0, .ex n 1, S, d⟩ [⟨Q, .num 0, .ex n 0, S, d⟩,
      ⟨⟨Q.fp, Q.k + d, insertBs (n, S) Q.bs⟩, .num 0, .num 1, 1, 0⟩]) := by
  refine ⟨0, E + 1, rfl, ⟨_, E, hn, rfl, hE, rfl⟩, fun vq hvq c _ hc ↦ ?_⟩
  by_cases hcE : c < E
  · refine ⟨_, List.mem_cons_self, fun vb ylo yhi hvb hlo hhi ↦ ⟨c, ?_, ?_, ?_⟩⟩
    · change ylo = 0 at hlo; omega
    · rw [ridx_base hn hE hhi]; exact hcE
    · rw [rmono_uniq hvq hvb]
  · obtain rfl : c = E := by omega
    refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun vb ylo yhi hvb hlo hhi ↦ ⟨0, ?_, ?_, ?_⟩⟩
    · change ylo = 0 at hlo; omega
    · change yhi = 1 at hhi; omega
    · obtain ⟨w, hw, rfl⟩ := hvq
      obtain ⟨w', hw', rfl⟩ := hvb
      obtain ⟨u, wl, hu, hwl, rfl⟩ := rbs_insert_inv hw'
      rw [rbase_uniq hu hn, rbs_uniq hwl hw]
      simp only [ofK_gpow, mul_zero, add_zero, pow_zero, ofK_one_E, mul_one]
      rw [pow_add, pow_add, ← pow_mul]
      ring

theorem gen_pow_mod (n : ℕ) : gen ^ (n % ordG) = gen ^ n := by
  rw [← ofK_gpow, ← ofK_gpow]
  congr 1
  have h := pow_mod_orderOf (x := Parameters.g) (n := n)
  rwa [orderOf_g] at h

/-- **Offsets modulo the order.** -/
theorem ord_rres {x : Mode.Res} (h : ordB x = true) : RRes M fp x := by
  match x, h with
  | .sub ⟨aq, alo, ahi, aS, ad⟩ [⟨bq, blo, bhi, bS, bd⟩], h =>
    cases alo <;> cases ahi <;> cases blo <;> cases bhi <;> simp only [ordB, Bool.false_eq_true] at h
    rename_i lo hi blo bhi
    simp only [decide_eq_true_eq] at h
    obtain ⟨rfl, rfl, rfl, h1, h2, h3⟩ := h
    refine ⟨lo, hi, rfl, rfl, fun vq hvq c hc1 hc2 ↦ ⟨_, List.mem_singleton_self _,
      fun vb ylo yhi hvb hlo hhi ↦ ⟨(lo + ad) % ordG + (c - lo) - bd, ?_, ?_, ?_⟩⟩⟩
    · change ylo = blo at hlo; omega
    · change yhi = bhi at hhi; omega
    · rw [rmono_uniq hvq hvb]
      simp only [one_mul, ofK_gpow]
      congr 1
      rw [show (lo + ad) % ordG + (c - lo) - bd + bd = (lo + ad) % ordG + (c - lo) by omega,
        ← gen_pow_mod (c + ad), ← gen_pow_mod ((lo + ad) % ordG + (c - lo))]
      congr 1
      rw [Nat.mod_eq_of_lt (by omega : (lo + ad) % ordG + (c - lo) < ordG),
        show c + ad = (lo + ad) + (c - lo) by omega, Nat.add_mod, Nat.mod_eq_of_lt (b := ordG) (a := c - lo)
          (by have := Nat.mod_lt (lo + ad) (show 0 < ordG by norm_num); omega)]
      exact Nat.mod_eq_of_lt (by omega)
  | .sub _ [], h => simp [ordB] at h
  | .sub _ (_ :: _ :: _), h => simp [ordB] at h
  | .lt _ _, h => simp [ordB] at h
  | .nz _, h => simp [ordB] at h
  | .name _, h => simp [ordB] at h

/-- **A lift read back**: `[u] = g^a`, `[v] = g^(a + k)`. -/
theorem liftBack_rres {u v k a : ℕ} (hu : M (fp + u) = ofK (Parameters.g ^ a))
    (hv : M (fp + v) = ofK (Parameters.g ^ (a + k))) (hlt : a + k < 2 ^ 62) {x : Mode.Res}
    (hx : liftBack u v k x = true) : RRes M fp x := by
  match x, hx with
  | .sub ⟨⟨afp, ak, abs⟩, alo, ahi, aS, ad⟩ [⟨⟨bfp, bk, bbs⟩, blo, bhi, bS, bd⟩], hx =>
    simp only [liftBack, decide_eq_true_eq] at hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hx
    refine ⟨k, a + k, rfl, ⟨_, a + k, hv, rfl, hlt, rfl⟩, fun vq hvq c hc1 hc2 ↦ ⟨_, List.mem_singleton_self _,
      fun vb ylo yhi hvb hlo hhi ↦ ⟨c - k, ?_, ?_, ?_⟩⟩⟩
    · change ylo = 0 at hlo; omega
    · rw [ridx_ex_fr hu (by omega) yhi hhi]; omega
    · obtain ⟨w, hw, rfl⟩ := hvq
      obtain ⟨w', hw', rfl⟩ := hvb
      rw [rbs_uniq hw hw']
      simp only [one_mul, add_zero, ofK_gpow]
      have e : gen ^ c = gen ^ k * gen ^ (c - k) := by rw [← pow_add]; congr 1; omega
      rw [e, pow_add]
      ring
  | .sub _ [], hx => simp [liftBack] at hx
  | .sub _ (_ :: _ :: _), hx => simp [liftBack] at hx
  | .lt _ _, hx => simp [liftBack] at hx
  | .nz _, hx => simp [liftBack] at hx
  | .name _, hx => simp [liftBack] at hx

end

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

/-- **A cell holding a power of `g`** at an honest frame. -/
theorem cellPow_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {o : ℕ}
    (h : cellPow j w o = true) : ∃ x < 2 ^ 33, refMem r.img (e.I.fp + o) = ofK (Parameters.g ^ x) := by
  simp only [cellPow, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨hin, h⟩
  · exact cellLt_top t hr hW h
  · obtain ⟨vs, hw, hF, hev, hwa, -⟩ := t.wit hr hW
    obtain ⟨a, ha, hb⟩ := List.any_eq_true.mp h
    cases a with
    | touch d p =>
      simp only [beq_iff_eq] at hb
      simp only [inFr, Bool.and_eq_true, decide_eq_true_eq] at hin
      have hon := hwa _ ha
      have hl : LoadHolds r.img.read (e.σ p) 0 (e.σ d) := hev _ hon
      obtain ⟨x, hx, hσ⟩ := B1.Digest.load_gpow (ref_memOk hr) hl
      have hc := t.cell hr hF (x := p) (namedOf_atom hon (by simp [atomUses])) (by rw [hb]; exact hin.1)
        (by rw [hb]; exact hin.2)
      rw [hb] at hc
      exact ⟨x, by omega, by rw [hc, hσ, Value.gen_pow_eq_ofK]⟩
    | _ => simp at hb

/-- **A top-level product at an honest frame**: `[p] = [x]·[y]`. -/
theorem mulCells_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {p x y : ℕ}
    (hx : 2 ≤ x ∧ x < fsN j) (hy : 2 ≤ y ∧ y < fsN j) (h : mulCells j w p x y = true) :
    refMem r.img (e.I.fp + p) = refMem r.img (e.I.fp + x) * refMem r.img (e.I.fp + y) := by
  obtain ⟨vs, hw, hF, hev, hwa, -⟩ := t.wit hr hW
  obtain ⟨a, ha, hb⟩ := List.any_eq_true.mp h
  cases a with
  | mul P X Y =>
    have hon := hwa _ ha
    have hm : e.σ P = e.σ X * e.σ Y := hev _ hon
    simp only [inFr, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
    obtain ⟨⟨hP, rfl⟩, hb⟩ := hb
    have cell : ∀ v ∈ atomUses (.mul P X Y), 2 ≤ cellJ j v → cellJ j v < fsN j →
        refMem r.img (e.I.fp + cellJ j v) = e.σ v := fun v hv h2 hlt ↦
      t.cell hr hF (namedOf_atom hon hv) h2 hlt
    rw [cell P (by simp [atomUses]) hP.1 hP.2, hm]
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [cell X (by simp [atomUses]) hx.1 hx.2, cell Y (by simp [atomUses]) hy.1 hy.2]
    · rw [cell X (by simp [atomUses]) hy.1 hy.2, cell Y (by simp [atomUses]) hx.1 hx.2, mul_comm]
  | _ => simp at hb

theorem cellPow_bounds {o : ℕ} (h : cellPow j w o = true) : 2 ≤ o ∧ o < fsN j := by
  simp only [cellPow, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨h, -⟩
  · exact cellLt_bounds h
  · simp only [inFr, Bool.and_eq_true, decide_eq_true_eq] at h; exact h

theorem tileShape_eq {n : Base} {ps : List (Base × ℕ)} {a : Rng} {bs : List Rng}
    (h : tileShape n ps (.sub a bs) = true) : Mode.Res.sub a bs = tileRes a.q n a.S a.d ps := by
  simpa [tileShape] using h

/-- **A run up to a product's exponent cut at a factor's, at an honest frame.** -/
theorem mulTile_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {x : Mode.Res}
    (hx : mulTileB j w x = true) : RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a [b, c], hx =>
    simp only [mulTileB] at hx
    cases hp : frEx a.hi with
    | none => rw [hp] at hx; cases hx
    | some p =>
    cases hu : frEx b.hi with
    | none => rw [hp, hu] at hx; cases hx
    | some u =>
    cases hv : frEx c.hi with
    | none => rw [hp, hu, hv] at hx; cases hx
    | some v =>
      rw [hp, hu, hv] at hx
      simp only [Bool.and_eq_true] at hx
      obtain ⟨⟨⟨hsh, hm⟩, hpu⟩, hpv⟩ := hx
      obtain ⟨xu, hxu, hwu⟩ := cellPow_top t hr hW hpu
      obtain ⟨xv, hxv, hwv⟩ := cellPow_top t hr hW hpv
      have hwp := mulCells_top t hr hW (cellPow_bounds hpu) (cellPow_bounds hpv) hm
      rw [hwu, hwv, ← ofK_mul, ← pow_add] at hwp
      rw [tileShape_eq hsh]
      refine tile_rres (E := xu + xv) hwp (by omega) (Or.inr ⟨[xu, xv], ⟨hwu, by omega, hwv, by omega, trivial⟩,
        by simp [partsSum]⟩)
  | .sub _ [], hx => simp [mulTileB] at hx
  | .sub _ [_], hx => simp [mulTileB] at hx
  | .sub _ (_ :: _ :: _ :: _), hx => simp [mulTileB] at hx
  | .lt _ _, hx => simp [mulTileB] at hx
  | .nz _, hx => simp [mulTileB] at hx
  | .name _, hx => simp [mulTileB] at hx

/-- **A tile of `tiles` at an honest frame**, given the tiles' sums. -/
theorem tileList_top (htl : ∀ p ∈ tiles, TileAt A p.1 p.2.1 p.2.2) (t : TopAt A r K i e j) (hr : r.Ok)
    {x : Mode.Res} (hx : tileListB j x = true) : RRes (refMem r.img) e.I.fp x := by
  obtain ⟨p, hp, hpx⟩ := List.any_eq_true.mp hx
  simp only [Bool.and_eq_true, beq_iff_eq] at hpx
  obtain ⟨rfl, hsh⟩ := hpx
  obtain ⟨E, hE, hn, h⟩ := htl p hp r K i e hr t
  match x, hsh with
  | .sub a bs, hsh =>
    rw [tileShape_eq hsh]
    exact tile_rres hn hE h

/-- **A run one point past another, at an honest frame.** -/
theorem ext_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {x : Mode.Res}
    (hx : extB j w x = true) : RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a [b, c], hx =>
    simp only [extB] at hx
    split at hx
    · rename_i o hah
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
      obtain ⟨hpo, hal, rfl, rfl⟩ := hx
      obtain ⟨E, hE, hw⟩ := cellPow_top t hr hW hpo
      obtain ⟨q, lo, hi, S, d⟩ := a
      simp only at hah hal
      subst hah hal
      exact ext_rres (Q := q) (S := S) (d := d) hw (by omega)
    · cases hx
  | .sub _ [], hx => simp [extB] at hx
  | .sub _ [_], hx => simp [extB] at hx
  | .sub _ (_ :: _ :: _ :: _), hx => simp [extB] at hx
  | .lt _ _, hx => simp [extB] at hx
  | .nz _, hx => simp [extB] at hx
  | .name _, hx => simp [extB] at hx

/-- **A lift read back at an honest frame.** -/
theorem liftBack_top (t : TopAt A r K i e j) (hr : r.Ok) {x : Mode.Res} (hx : Res.liftBackB j x = true) :
    RRes (refMem r.img) e.I.fp x := by
  obtain ⟨p, hp, hpx⟩ := List.any_eq_true.mp hx
  simp only [Bool.and_eq_true, beq_iff_eq] at hpx
  obtain ⟨rfl, hsh⟩ := hpx
  obtain ⟨a, hu, hv, hlt⟩ := lifts_ok p hp r K i e hr t
  exact liftBack_rres hu hv hlt hsh

/-- An index of a selector's base has a value at an honest frame. -/
theorem idxPow_ridx (t : TopAt A r K i e j) (hr : r.Ok) {w : Res.Wit} (hW : Res.witOk j w = true)
    {I : Mode.Idx} (h : Res.idxPow j w I = true)
    (hin : RIdxIn (refMem r.img) e.I.fp I) : ∃ y, RIdx (refMem r.img) e.I.fp I y := by
  match I, h, hin with
  | .num n, _, _ => exact ⟨n, rfl⟩
  | .ex B c, h, hin =>
    simp only [Res.idxPow, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨xa, -, ⟨v, a, hv, hva, ha, -⟩, -, -⟩ := ltSel_top t hr h ⟨hin, trivial⟩
      exact ⟨a + c, v, a, hv, hva, ha, rfl⟩
    · cases B with
      | fr o =>
        obtain ⟨-, a, ha, hv⟩ := pw_top t hr hW h
        exact ⟨a + c, _, a, rfl, hv, by omega, rfl⟩
      | hp _ _ => simp at h

theorem ridx_succ {M : ℕ → E} {fp : ℕ} : ∀ {I : Mode.Idx} {y : ℕ}, RIdx M fp I y → RIdx M fp (Res.idxSucc I) (y + 1)
  | .num _, _, h => by change _ = _ + 1; rw [h]
  | .ex _ _, _, ⟨v, a, hv, hva, ha, h⟩ => ⟨v, a, hv, hva, ha, by rw [h]; rfl⟩

theorem ridxIn_succ {M : ℕ → E} {fp : ℕ} : ∀ {I : Mode.Idx}, RIdxIn M fp (Res.idxSucc I) → RIdxIn M fp I
  | .num _, _ => trivial
  | .ex _ _, h => h

/-- **The same cells named one index up** at an honest frame. -/
theorem ordShift_top (t : TopAt A r K i e j) (hr : r.Ok) {w : Res.Wit} (hW : Res.witOk j w = true) {x : Mode.Res}
    (hx : Res.ordShiftB j w x = true)
    (hin : RIn (refMem r.img) e.I.fp x) : RRes (refMem r.img) e.I.fp x := by
  match x, hx, hin with
  | .sub ⟨aq, alo, ahi, aS, ad⟩ [⟨bq, blo, bhi, bS, bd⟩], hx, hin =>
    have hg : Parameters.g ^ ordG = 1 := by
      have := pow_orderOf_eq_one Parameters.g
      rwa [orderOf_g] at this
    simp only [Res.ordShiftB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨hl, hh⟩ := hin
    rcases hx with ⟨⟨⟨rfl, rfl, rfl, rfl, hd⟩, hplo⟩, hphi⟩ | ⟨⟨⟨rfl, rfl, rfl, rfl, hd⟩, hplo⟩, hphi⟩
    · obtain ⟨yl, hyl⟩ := idxPow_ridx t hr hW hplo (ridxIn_succ hl)
      obtain ⟨yh, hyh⟩ := idxPow_ridx t hr hW hphi (ridxIn_succ hh)
      refine ⟨yl + 1, yh + 1, ridx_succ hyl, ridx_succ hyh, fun vq hvq c hc1 hc2 ↦ ⟨_, List.mem_singleton_self _,
        fun vb ylo yhi hvb hlo hhi ↦ ⟨c - 1, ?_, ?_, ?_⟩⟩⟩
      · rw [ridx_uniq hlo hyl]; omega
      · rw [ridx_uniq hhi hyh]; omega
      · rw [rmono_uniq hvq hvb]
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        have h1 : aS * (c' + 1) + ad = aS * (c' + 1 - 1) + bd + ordG := by
          rw [Nat.add_sub_cancel, mul_add, mul_one]; omega
        rw [h1, pow_add _ (aS * (c' + 1 - 1) + bd) ordG, hg, mul_one]
    · obtain ⟨yl, hyl⟩ := idxPow_ridx t hr hW hplo hl
      obtain ⟨yh, hyh⟩ := idxPow_ridx t hr hW hphi hh
      refine ⟨yl, yh, hyl, hyh, fun vq hvq c hc1 hc2 ↦ ⟨_, List.mem_singleton_self _,
        fun vb ylo yhi hvb hlo hhi ↦ ⟨c + 1, ?_, ?_, ?_⟩⟩⟩
      · rw [ridx_uniq hlo (ridx_succ hyl)]; omega
      · rw [ridx_uniq hhi (ridx_succ hyh)]; omega
      · rw [rmono_uniq hvq hvb]
        have h1 : aS * (c + 1) + bd = aS * c + ad + ordG := by rw [mul_add, mul_one]; omega
        rw [h1, pow_add _ (aS * c + ad) ordG, hg, mul_one]
  | .sub _ [], hx, _ => simp [Res.ordShiftB] at hx
  | .sub _ (_ :: _ :: _), hx, _ => simp [Res.ordShiftB] at hx
  | .lt _ _, hx, _ => simp [Res.ordShiftB] at hx
  | .nz _, hx, _ => simp [Res.ordShiftB] at hx
  | .name _, hx, _ => simp [Res.ordShiftB] at hx

/-- **The tile families at an honest frame**, given the tiles' sums. -/
theorem tileFam_top_of (htl : ∀ p ∈ tiles, TileAt A p.1 p.2.1 p.2.2) (t : TopAt A r K i e j) (hr : r.Ok)
    (hW : witOk j w = true) {x : Mode.Res} (hx : tileFamB j w x = true) : RRes (refMem r.img) e.I.fp x := by
  simp only [tileFamB, Bool.or_eq_true] at hx
  rcases hx with ((hx | hx) | hx) | hx
  · exact mulTile_top t hr hW hx
  · exact tileList_top htl t hr hx
  · exact ext_top t hr hW hx
  · exact ord_rres hx

end

end

end LeanVM.Guest.EndExec
