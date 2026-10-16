module

public import LeanVMCircuits.Rec.Verdict
public import LeanVMCircuits.Rec.UnionSound

@[expose] public section

/-!
The union's coverage check on the shipped circuit (`rec::tree::union`).

- `prod_closed`: a product is `∏ (1 + on · (X + 1 + ∑_k w_k t_k))` over its pool's slots, each slot's `on` its
  selection bit times its validity and its tuple `t` the label of its run's last header `(1, label[0..6])` (zero
  before any) and the slot's member words. At the point's weights that is `UnionSound.slotsAt`.
- `onClaims_agree`: two assignments agreeing on the pool's digests, begin and selection bits, whose compressions do not
  collide, have the same claims on.
- `union_cover`: if, in one assignment holding every constraint but the tests, the selected child claims and the
  declared claims are different multisets, then the points of `S^5` at which some assignment with the same digests,
  begin and selection bits, whose compressions do not collide with the first's, holds every constraint but the tests
  and the coverage test, are at most a `4N/|S|` fraction, `N` bounding both pools' slots. The point is squeezed after
  the digests and the begin and selection bits are absorbed (`Bind.tests_determined`).
- `union_sound`: the union's theorem on an accepted circuit. With what the union's transcript absorbs fixed, the
  point uniform on `S^5`, and the prover answering each point with an assignment that absorbs the same words, holds
  every constraint but the tests, and does not collide with the first, the coverage test holds at a matching point
  for at most a `4N/|S|` fraction of the outcomes when the two multisets differ.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model PoolParse UnionSound ProdCert

/-! A product in closed form. -/

/-- `∑_{k < 16} w_k t_k`. -/
noncomputable def wfp (W t : ℕ → E) : E := ∑ k ∈ Finset.range 16, W k * t k

namespace ProdCert

variable (os : Array (List ℕ)) (pc : PoolCert) (val : Val)

/-- Item `i`'s block word `j`, as `E`. -/
noncomputable def Mv (i j : ℕ) : E := emb (val (m os pc i j) 0)

/-- Item `i` as a header: `(1, m_0, ..., m_5)`. -/
noncomputable def hdrT (i k : ℕ) : E := if k = 0 then 1 else if k < 7 then Mv os pc val i (k - 1) else 0

/-- The label tuple after item `i`: a header's own, else its run's so far, zero at a run's start. -/
noncomputable def labT : ℕ → ℕ → E
  | 0 => if Model.ev val (o os (pc.p 0 + 9)) = 0 then hdrT os pc val 0 else fun _ => 0
  | i + 1 => if Model.ev val (o os (pc.p (i + 1) + 9)) = 0 then hdrT os pc val (i + 1)
    else if pc.sigma os val (i + 1) then fun _ => 0 else labT i

/-- The label tuple before item `i`. -/
noncomputable def LTin (i : ℕ) : ℕ → E := if pc.sigma os val i then fun _ => 0 else labT os pc val (i - 1)

/-- Slot `sl` of item `i`'s tuple: its label tuple and member words. -/
noncomputable def slotT (i sl k : ℕ) : E :=
  if k < 7 then labT os pc val i k else if k < 11 then Mv os pc val i (4 * sl + (k - 7)) else 0

/-- Whether slot `sl` of item `i` is on: valid, and selected. -/
noncomputable def onBit (i sl : ℕ) : E :=
  Model.ev val (valid os pc i sl) * if pc.selecting then emb (val (selW os pc i sl) 0) else 1

/-- The first `k` items' slots, tuples indexed by `ℕ`. -/
noncomputable def slotsN (k : ℕ) : List (E × (ℕ → E)) :=
  (List.range k).flatMap fun i => [(onBit os pc val i 0, slotT os pc val i 0), (onBit os pc val i 1, slotT os pc val i 1)]

/-- The pool's slots: each slot's bit and tuple. -/
noncomputable def slots : List (E × Tuple) := (slotsN os pc val pc.n).map fun p => (p.1, fun t => p.2 t)

end ProdCert

section Closed

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {pc : PoolCert} {qc : ProdCert}
  {st : ℕ → Fin 4 → K} {val : Val}

theorem labT_high (i k : ℕ) (hk : 7 ≤ k) : labT os pc val i k = 0 := by
  induction i with
  | zero => simp only [labT]; split <;> simp [hdrT, show k ≠ 0 by omega, show ¬ k < 7 by omega]
  | succ i ih =>
    simp only [labT]
    split
    · simp [hdrT, show k ≠ 0 by omega, show ¬ k < 7 by omega]
    · split
      · rfl
      · exact ih

theorem labT_eq (i : ℕ) : labT os pc val i =
    if Model.ev val (o os (pc.p i + 9)) = 0 then hdrT os pc val i else LTin os pc val i := by
  cases i with
  | zero => simp [labT, LTin, PoolCert.sigma_zero]
  | succ i => simp [labT, LTin]

theorem wfp_zero (W : ℕ → E) : wfp W (fun _ => 0) = 0 := by simp [wfp]

theorem wfp_hdr (W : ℕ → E) (i : ℕ) : wfp W (hdrT os pc val i) =
    W 6 * Mv os pc val i 5 + (W 5 * Mv os pc val i 4 + (W 4 * Mv os pc val i 3 + (W 3 * Mv os pc val i 2 +
      (W 2 * Mv os pc val i 1 + (W 1 * Mv os pc val i 0 + W 0))))) := by
  simp only [wfp, Finset.sum_range_succ, Finset.sum_range_zero, hdrT]
  norm_num
  ring

theorem wfp_slot (W : ℕ → E) (i sl : ℕ) : wfp W (slotT os pc val i sl) =
    W 10 * Mv os pc val i (4 * sl + 3) + (W 9 * Mv os pc val i (4 * sl + 2) + (W 8 * Mv os pc val i (4 * sl + 1) +
      (W 7 * Mv os pc val i (4 * sl) + wfp W (labT os pc val i)))) := by
  simp only [wfp, Finset.sum_range_succ, Finset.sum_range_zero, slotT]
  norm_num
  rw [labT_high i 7 (by norm_num), labT_high i 8 (by norm_num), labT_high i 9 (by norm_num), labT_high i 10 (by norm_num),
    labT_high i 11 (by norm_num), labT_high i 12 (by norm_num), labT_high i 13 (by norm_num), labT_high i 14 (by norm_num),
    labT_high i 15 (by norm_num)]
  ring

/-- A slot's factor at `X + 1 = x1` and weights `W`. -/
noncomputable def factor (x1 : E) (W : ℕ → E) (p : E × (ℕ → E)) : E := 1 + p.1 * (x1 + wfp W p.2)

theorem bit_cases {x : K} (h : IsBit x) : emb x = 0 ∨ emb x = 1 := by
  rcases h with rfl | rfl
  · exact Or.inl emb_zero
  · exact Or.inr emb_one'

/-- One item of a product, in closed form. -/
theorem closed_step (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) (hqok : qc.ok os pc cs rl = true)
    (W : ℕ → E) (hW : ∀ k < 11, Model.ev val (qc.w k) = W k) {i : ℕ} (hi : i < pc.n)
    (ih : 0 < i → Model.ev val (labOut os pc qc (i - 1)) = wfp W (labT os pc val (i - 1)) ∧
      Model.ev val (acc os pc qc (i - 1) 1) =
        ((slotsN os pc val i).map (factor (Model.ev val qc.x1) W)).prod) :
    Model.ev val (labOut os pc qc i) = wfp W (labT os pc val i) ∧
      Model.ev val (acc os pc qc i 1) = ((slotsN os pc val (i + 1)).map (factor (Model.ev val qc.x1) W)).prod := by
  simp only [ProdCert.ok, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hqok
  obtain ⟨hhq, hitq⟩ := hqok
  obtain ⟨⟨⟨hrst, hhead⟩, hs0⟩, hs1⟩ := hitq i hi
  have Hq := holds_all hF hhq
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, Call.Holds,
    getD_o] at Hq
  have hz : Model.ev val (qc.zero os) = 0 := Hq.1
  have ho : Model.ev val (qc.one os) = 1 := Hq.2
  obtain ⟨-, -, hhdr, -, hitem, -, hbitsOk⟩ := PoolCert.ok_parts hok
  obtain ⟨phz, pho, -⟩ := PoolCert.header_sem hF hhdr
  have k := kind_sem hF phz pho (PoolCert.item_parts (hitem i hi)).1
  dsimp only at k
  have hbits := (PoolCert.pool_sem hF hok).bits i hi
  simp only [PoolCert.vals] at hbits
  obtain ⟨b0, b1, bp⟩ := hbits
  -- The label before the item.
  have hlab : Model.ev val (lab os pc qc i) = wfp W (LTin os pc val i) := by
    rcases PoolCert.startOf_cases (pc := pc) (os := os) i with ⟨rfl, hst⟩ | ⟨h0, hm, hr, hst⟩ | ⟨h0, -, hst⟩
    · simp only [lab, hst, LTin, PoolCert.sigma_zero, if_true, hz, wfp_zero]
    · simp only [resetCalls, hst] at hrst
      have H := holds_all hF hrst
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, Call.Holds,
        getD_o] at H
      have hbeta : IsBit (val (pc.beta os (i / chunk)) 0) := by
        have hj : i / chunk < pc.chunks := by simp only [PoolCert.n, chunk] at hi; simp only [chunk]; omega
        have hbg : pc.begins (i / chunk) = true := by
          simp only [PoolCert.begins, Bool.and_eq_true, decide_eq_true_eq]; simp only [chunk] at hm ⊢; omega
        simp only [PoolCert.bitsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
          Bool.not_eq_true'] at hbitsOk
        rcases hbitsOk.2 _ hj with h | h
        · rw [hbg] at h; exact absurd h (by decide)
        · exact PoolCert.packed_bit hF h
      simp only [lab, hst, LTin, PoolCert.sigma]
      rw [H, (ih (by omega)).1]
      rcases hbeta with h | h
      · simp [h, emb_zero]
      · simp only [h, emb_one', mul_one, decide_true, if_true, wfp_zero]
        exact add_self_E _
    · simp only [lab, hst, LTin, PoolCert.sigma, Bool.false_eq_true, if_false]
      exact (ih (by omega)).1
  -- The label after it.
  have H := holds_all hF hhead
  simp only [headCalls, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    Call.Holds, getD_o] at H
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := H
  have hhdrv : Model.ev val (o os (qc.q i + d os pc i + 5)) = wfp W (hdrT os pc val i) := by
    rw [wfp_hdr, h5, h4, h3, h2, h1, h0, hW 0 (by norm_num), hW 1 (by norm_num), hW 2 (by norm_num),
      hW 3 (by norm_num), hW 4 (by norm_num), hW 5 (by norm_num), hW 6 (by norm_num)]
    rfl
  have hlo : Model.ev val (labOut os pc qc i) = wfp W (labT os pc val i) := by
    rw [show labOut os pc qc i = o os (qc.q i + d os pc i + 7) from rfl, h7, h6, hlab, hhdrv, labT_eq, k.2.2.2.2.1]
    have hnh : IsBit (val (o os (pc.p i)) 0 + val (o os (pc.p i + 1)) 0 +
        val (o os (pc.p i)) 0 * val (o os (pc.p i + 1)) 0) := by
      rcases b0 with h | h <;> rcases b1 with h' | h' <;> simp [h, h', IsBit, two_K']
    rcases bit_cases hnh with h | h
    · rw [h, if_pos rfl, zero_mul, zero_add]
    · rw [h, if_neg one_ne_zero, one_mul]
      linear_combination wfp W (hdrT os pc val i) * two_E
  -- The slots.
  have hslot : ∀ sl, callsOk cs rl (qc.slotCalls os pc i sl) = true →
      Model.ev val (acc os pc qc i sl) = Model.ev val (accIn os pc qc i sl) *
        factor (Model.ev val qc.x1) W (onBit os pc val i sl, slotT os pc val i sl) := by
    intro sl hsc
    have H := holds_all hF hsc
    set b := base os pc qc i sl
    have hfp : ∀ (f0 : Model.ev val (o os b) = Model.ev val (qc.w 7) * emb (val (m os pc i (4 * sl)) 0) +
          Model.ev val (labOut os pc qc i))
        (f1 : Model.ev val (o os (b + 1)) = Model.ev val (qc.w 8) * emb (val (m os pc i (4 * sl + 1)) 0) +
          Model.ev val (o os b))
        (f2 : Model.ev val (o os (b + 2)) = Model.ev val (qc.w 9) * emb (val (m os pc i (4 * sl + 2)) 0) +
          Model.ev val (o os (b + 1)))
        (f3 : Model.ev val (o os (b + 3)) = Model.ev val (qc.w 10) * emb (val (m os pc i (4 * sl + 3)) 0) +
          Model.ev val (o os (b + 2))),
        Model.ev val (o os (b + 3)) = wfp W (slotT os pc val i sl) := by
      intro f0 f1 f2 f3
      rw [wfp_slot, f3, f2, f1, f0, hlo, hW 7 (by norm_num), hW 8 (by norm_num), hW 9 (by norm_num),
        hW 10 (by norm_num)]
      rfl
    cases hsel : pc.selecting with
    | true =>
      simp only [slotCalls, hsel, if_true, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, and_true, Call.Holds, getD_o] at H
      obtain ⟨⟨f0, f1, f2, f3, t⟩, hd, fc, ac⟩ := H
      rw [show acc os pc qc i sl = o os (b + 7) by simp [acc, len, hsel, b], ac, fc, hd, t, hfp f0 f1 f2 f3, ho]
      simp only [factor, onBit, hsel, if_true]
      ring
    | false =>
      simp only [slotCalls, hsel, Bool.false_eq_true, if_false, List.forall_mem_append, List.forall_mem_cons,
        List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, Call.Holds, getD_o] at H
      obtain ⟨⟨f0, f1, f2, f3, t⟩, fc, ac⟩ := H
      rw [show acc os pc qc i sl = o os (b + 6) by simp [acc, len, hsel, b], ac, fc, t, hfp f0 f1 f2 f3, ho]
      simp only [factor, onBit, hsel, Bool.false_eq_true, if_false]
      ring
  refine ⟨hlo, ?_⟩
  rw [hslot 1 hs1, show accIn os pc qc i 1 = acc os pc qc i 0 by simp [accIn], hslot 0 hs0]
  have hin : Model.ev val (accIn os pc qc i 0) = ((slotsN os pc val i).map (factor (Model.ev val qc.x1) W)).prod := by
    simp only [accIn, Nat.zero_ne_one, if_false]
    split
    · subst_vars; simp [slotsN, ho]
    · exact (ih (by omega)).2
  rw [hin, show slotsN os pc val (i + 1) = slotsN os pc val i ++
      [(onBit os pc val i 0, slotT os pc val i 0), (onBit os pc val i 1, slotT os pc val i 1)] by
    simp [slotsN, List.range_succ, List.flatMap_append], List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

/-- A product in closed form: `∏ (1 + on · (X + 1 + ∑_k w_k t_k))` over its pool's slots. -/
theorem prod_closed (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) (hqok : qc.ok os pc cs rl = true)
    (W : ℕ → E) (hW : ∀ k < 11, Model.ev val (qc.w k) = W k) :
    Model.ev val (out os pc qc) = ((slotsN os pc val pc.n).map (factor (Model.ev val qc.x1) W)).prod := by
  have key : ∀ i < pc.n, Model.ev val (labOut os pc qc i) = wfp W (labT os pc val i) ∧
      Model.ev val (acc os pc qc i 1) = ((slotsN os pc val (i + 1)).map (factor (Model.ev val qc.x1) W)).prod := by
    intro i
    induction i with
    | zero => intro hi; exact closed_step hF hok hqok W hW hi (fun h => absurd h (lt_irrefl 0))
    | succ i ih => intro hi; exact closed_step hF hok hqok W hW hi fun _ => ih (by omega)
  have hn : 0 < pc.n := by
    obtain ⟨h0, -⟩ := PoolCert.ok_parts hok
    simp only [PoolCert.n, chunk]; omega
  have := (key (pc.n - 1) (by omega)).2
  rw [show pc.n - 1 + 1 = pc.n by omega] at this
  exact this

/-- At the weights `eq(A, k)` a product is `UnionSound.slotsAt` of its pool's slots. -/
theorem prod_slotsAt (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) (hqok : qc.ok os pc cs rl = true)
    (a : Fin 4 → E) (hW : ∀ k : Fin 16, Model.ev val (qc.w k) = eqAt a k) :
    Model.ev val (out os pc qc) = slotsAt (slots os pc val) (Model.ev val qc.x1) a := by
  set W : ℕ → E := fun k => if h : k < 16 then eqAt a ⟨k, h⟩ else 0
  have hs : ∀ g : ℕ → E, wfp W g = fpAt a fun t => g t := by
    intro g
    rw [wfp, ← Fin.sum_univ_eq_sum_range (fun k => W k * g k) 16, fpAt]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [W, dif_pos k.isLt, Fin.eta]
  rw [prod_closed hF hok hqok W (fun k hk => by rw [hW ⟨k, by omega⟩]; simp [W, show k < 16 by omega]), slotsAt,
    slots, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro p _
  rw [factor, hs]
  rfl

/-- Each slot's bit is a bit. -/
theorem slots_bits (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) :
    ∀ p ∈ slots os pc val, p.1 = 0 ∨ p.1 = 1 := by
  obtain ⟨-, -, hhdr, -, hitem, -, hbitsOk⟩ := PoolCert.ok_parts hok
  obtain ⟨phz, pho, -⟩ := PoolCert.header_sem hF hhdr
  simp only [PoolCert.bitsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at hbitsOk
  intro p hp
  simp only [slots, slotsN, List.mem_map, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  obtain ⟨q, ⟨i, hi, hq⟩, rfl⟩ := hp
  have k := kind_sem hF phz pho (PoolCert.item_parts (hitem i hi)).1
  dsimp only at k
  have hbits := (PoolCert.pool_sem hF hok).bits i hi
  simp only [PoolCert.vals] at hbits
  obtain ⟨b0, b1, bp⟩ := hbits
  have hv : ∀ sl, Model.ev val (valid os pc i sl) = 0 ∨ Model.ev val (valid os pc i sl) = 1 := by
    intro sl
    unfold valid
    split
    · rw [k.2.2.1]; apply bit_cases
      rcases b0 with h | h <;> rcases b1 with h' | h' <;> simp [h, h', IsBit, two_K']
    · rw [k.2.2.2.2.2.1]; apply bit_cases
      rcases b0 with h | h <;> rcases b1 with h' | h' <;> rcases bp with h'' | h'' <;> simp [h, h', h'', IsBit, two_K']
  have hs : ∀ sl, (if pc.selecting then emb (val (selW os pc i sl) 0) else 1) = 0 ∨
      (if pc.selecting then emb (val (selW os pc i sl) 0) else 1) = 1 := by
    intro sl
    cases hsel : pc.selecting with
    | false => right; rfl
    | true =>
      simp only [if_true]
      obtain ⟨-, hsb⟩ := hbitsOk.1 i hi
      rcases hsb with h | ⟨h0, h1⟩
      · rw [hsel] at h; exact absurd h (by decide)
      · apply bit_cases
        unfold selW; split
        · exact PoolCert.packed_bit hF h0
        · exact PoolCert.packed_bit hF h1
  have hon : ∀ sl, onBit os pc val i sl = 0 ∨ onBit os pc val i sl = 1 := by
    intro sl
    unfold onBit
    rcases hv sl with h | h <;> rcases hs sl with h' | h' <;> simp [h, h']
  rcases hq with rfl | rfl
  · exact hon 0
  · exact hon 1

end Closed

/-! Two assignments' claims. -/

section Agree

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {pc : PoolCert}
  {st st' : ℕ → Fin 4 → K} {val val' : Val}

theorem onClaims_append (l l' : List (E × Tuple)) : onClaims (l ++ l') = onClaims l + onClaims l' := by
  classical
  simp [onClaims, List.filter_append]

theorem onClaims_pair {a b a' b' : E × Tuple} (ha : a = a' ∨ (a.1 = 0 ∧ a'.1 = 0))
    (hb : b = b' ∨ (b.1 = 0 ∧ b'.1 = 0)) : onClaims [a, b] = onClaims [a', b'] := by
  classical
  have h01 : (0 : E) ≠ 1 := zero_ne_one
  rcases ha with rfl | ⟨ha, ha'⟩ <;> rcases hb with rfl | ⟨hb, hb'⟩
  · rfl
  · simp [onClaims, List.filter_cons, hb, hb', h01]
  · simp [onClaims, List.filter_cons, ha, ha', h01]
  · simp [onClaims, ha, ha', hb, hb', h01]

/-- Two assignments agreeing on a pool's digests, begin and selection bits, whose compressions do not collide, have
the same claims on. -/
theorem slots_agree {s : State} (hF : Facts cs rl os st val) (hF' : Facts cs rl os st' val') (hR : RowsIn cs os s)
    (hok : pc.ok os cs rl = true) (hcr : HashCR s val val')
    (hd : ∀ r < pc.runs, val (pc.digests.getD r 0) = val' (pc.digests.getD r 0))
    (hb : ∀ j < pc.chunks, pc.begins j = true → val (pc.beta os j) = val' (pc.beta os j))
    (hs : pc.selecting = true → ∀ i < pc.n,
      val (o os (pc.blk os i + 16)) = val' (o os (pc.blk os i + 16)) ∧
        val (o os (pc.blk os i + 17)) = val' (o os (pc.blk os i + 17))) :
    onClaims (slots os pc val) = onClaims (slots os pc val') := by
  obtain ⟨-, -, hhdr, -, hitem, -, -⟩ := PoolCert.ok_parts hok
  obtain ⟨phz, pho, -⟩ := PoolCert.header_sem hF hhdr
  obtain ⟨phz', pho', -⟩ := PoolCert.header_sem hF' hhdr
  have hpu := PoolCert.pool_unique hF hF' hR hok hcr hd hb
  have hsig := PoolCert.sigma_agree (val := val) (val' := val') hb
  -- Each item: its kind forms agree, and but for padding its words.
  have item : ∀ i < pc.n,
      Model.ev val (o os (pc.p i + 9)) = Model.ev val' (o os (pc.p i + 9)) ∧
      (∀ sl, Model.ev val (valid os pc i sl) = Model.ev val' (valid os pc i sl)) ∧
      (val (o os (pc.p i)) 0 * val (o os (pc.p i + 1)) 0 = 0 → ∀ j < 8, Mv os pc val i j = Mv os pc val' i j) ∧
      (val (o os (pc.p i)) 0 * val (o os (pc.p i + 1)) 0 ≠ 0 →
        Model.ev val (o os (pc.p i + 9)) ≠ 0 ∧ ∀ sl, Model.ev val (valid os pc i sl) = 0) := by
    intro i hi
    have k := kind_sem hF phz pho (PoolCert.item_parts (hitem i hi)).1
    have k' := kind_sem hF' phz' pho' (PoolCert.item_parts (hitem i hi)).1
    dsimp only at k k'
    obtain ⟨e0, e1, ep, hins⟩ := hpu i hi
    simp only [PoolCert.vals] at e0 e1 ep hins
    have hbits := (PoolCert.pool_sem hF hok).bits i hi
    simp only [PoolCert.vals] at hbits
    refine ⟨by rw [k.2.2.2.2.1, k'.2.2.2.2.1, e0, e1], fun sl => ?_, fun hpad j hj => ?_, fun hpad => ?_⟩
    · unfold valid; split
      · rw [k.2.2.1, k'.2.2.1, e0, e1]
      · rw [k.2.2.2.2.2.1, k'.2.2.2.2.2.1, e0, e1, ep]
    · have := hins hpad (6 + j) (by omega)
      simp only [show 6 + j ≠ 0 by omega, show 6 + j ≠ 1 by omega, show ¬ 6 + j < 6 by omega, if_false,
        show 6 + j - 6 = j by omega, blockWords_getD _ j hj] at this
      simp only [Mv, m, this]
    · have hp1 := (pad_bit hbits.1 hbits.2.1).resolve_left hpad
      obtain ⟨a0, a1⟩ := pad_one hbits.1 hbits.2.1 hp1
      refine ⟨by rw [k.2.2.2.2.1, a0, a1, two_K', zero_add, mul_one, emb_one']; exact one_ne_zero, fun sl => ?_⟩
      unfold valid; split
      · rw [k.2.2.1, a0, a1, one_mul, two_K', emb_zero]
      · rw [k.2.2.2.2.2.1, a0, a1, one_mul, two_K', zero_mul, emb_zero]
  -- The label tuples agree.
  have hlab : ∀ i < pc.n, labT os pc val i = labT os pc val' i := by
    intro i
    induction i with
    | zero =>
      intro hi
      obtain ⟨hnh, -, hm, hpd⟩ := item 0 hi
      rw [labT_eq, labT_eq, hnh, LTin, LTin, hsig 0 hi]
      split
      · rename_i h0
        have hpad : val (o os (pc.p 0)) 0 * val (o os (pc.p 0 + 1)) 0 = 0 := by
          by_contra hc; exact (hpd hc).1 (hnh ▸ h0)
        funext t; simp only [hdrT]; split; rfl; split; rw [hm hpad _ (by omega)]; rfl
      · -- The first item starts a run: its label before it is zero in both, not `labT` of an item before it.
        simp only [PoolCert.sigma_zero, if_true]
    | succ i ih =>
      intro hi
      obtain ⟨hnh, -, hm, hpd⟩ := item (i + 1) hi
      rw [labT_eq, labT_eq, hnh, LTin, LTin, hsig (i + 1) hi, Nat.add_sub_cancel, ih (by omega)]
      split
      · rename_i h0
        have hpad : val (o os (pc.p (i + 1))) 0 * val (o os (pc.p (i + 1) + 1)) 0 = 0 := by
          by_contra hc; exact (hpd hc).1 (hnh ▸ h0)
        funext t; simp only [hdrT]; split; rfl; split; rw [hm hpad _ (by omega)]; rfl
      · rfl
  -- Slot by slot.
  have hslot : ∀ i < pc.n, ∀ sl < 2, (onBit os pc val i sl, fun t : Fin 16 => slotT os pc val i sl t) =
      (onBit os pc val' i sl, fun t : Fin 16 => slotT os pc val' i sl t) ∨
      (onBit os pc val i sl = 0 ∧ onBit os pc val' i sl = 0) := by
    intro i hi sl hsl
    obtain ⟨-, hv, hm, hpd⟩ := item i hi
    have hsel : (if pc.selecting then emb (val (selW os pc i sl) 0) else 1) =
        (if pc.selecting then emb (val' (selW os pc i sl) 0) else 1) := by
      cases hse : pc.selecting with
      | false => simp only [Bool.false_eq_true, if_false]
      | true =>
        obtain ⟨a, b⟩ := hs hse i hi
        simp only [if_true]; unfold selW; split
        · rw [a]
        · rw [b]
    by_cases hpad : val (o os (pc.p i)) 0 * val (o os (pc.p i + 1)) 0 = 0
    · left
      simp only [onBit, hv sl, hsel, Prod.mk.injEq, true_and]
      funext t
      simp only [slotT, hlab i hi]
      split; rfl; split; rw [hm hpad _ (by omega)]; rfl
    · right
      have h0 := (hpd hpad).2 sl
      exact ⟨by simp [onBit, h0], by simp [onBit, ← hv sl, h0]⟩
  have key : ∀ k ≤ pc.n, onClaims ((slotsN os pc val k).map fun p => (p.1, fun t : Fin 16 => p.2 t)) =
      onClaims ((slotsN os pc val' k).map fun p => (p.1, fun t : Fin 16 => p.2 t)) := by
    intro k
    induction k with
    | zero => intro _; simp only [slotsN, List.range_zero, List.flatMap_nil]
    | succ k ih =>
      intro hk
      have split : ∀ v, slotsN os pc v (k + 1) = slotsN os pc v k ++
          [(onBit os pc v k 0, slotT os pc v k 0), (onBit os pc v k 1, slotT os pc v k 1)] := fun v => by
        simp [slotsN, List.range_succ, List.flatMap_append]
      rw [split, split, List.map_append, List.map_append, onClaims_append, onClaims_append, ih (by omega)]
      congr 1
      exact onClaims_pair (hslot k (by omega) 0 (by norm_num)) (hslot k (by omega) 1 (by norm_num))
  exact key _ le_rfl

end Agree

/-! The coverage check. -/

/-- Two assignments agree on a pool's digests, begin and selection bits: what the union's transcript absorbs of it. -/
def PoolCert.Agree (os : Array (List ℕ)) (pc : PoolCert) (val val' : Val) : Prop :=
  (∀ r < pc.runs, val (pc.digests.getD r 0) = val' (pc.digests.getD r 0)) ∧
  (∀ j < pc.chunks, pc.begins j = true → val (pc.beta os j) = val' (pc.beta os j)) ∧
  (pc.selecting = true → ∀ i < pc.n, val (o os (pc.blk os i + 16)) = val' (o os (pc.blk os i + 16)) ∧
    val (o os (pc.blk os i + 17)) = val' (o os (pc.blk os i + 17)))

theorem PoolCert.agree_of_committed {os : Array (List ℕ)} {pc : PoolCert} {val val' : Val}
    (h : ∀ w ∈ pc.committed os, val w = val' w) : pc.Agree os val val' := by
  simp only [PoolCert.committed, List.mem_append, List.mem_map, List.mem_filter, List.mem_range] at h
  refine ⟨fun r hr => h _ (Or.inl (Or.inl (getD_mem_of_lt hr))), fun j hj hb => h _ (Or.inl (Or.inr ⟨j, ⟨hj, hb⟩, rfl⟩)),
    fun hse i hi => ⟨?_, ?_⟩⟩
  · exact h _ (Or.inr (by simp [hse]; exact ⟨i, hi, Or.inl rfl⟩))
  · exact h _ (Or.inr (by simp [hse]; exact ⟨i, hi, Or.inr rfl⟩))

theorem length_slotsN (os : Array (List ℕ)) (pc : PoolCert) (val : Val) :
    ∀ k, (slotsN os pc val k).length = 2 * k
  | 0 => by simp [slotsN]
  | k + 1 => by
    rw [show slotsN os pc val (k + 1) = slotsN os pc val k ++
        [(onBit os pc val k 0, slotT os pc val k 0), (onBit os pc val k 1, slotT os pc val k 1)] by
      simp [slotsN, List.range_succ, List.flatMap_append], List.length_append, length_slotsN os pc val k]
    simp only [List.length_cons, List.length_nil]
    ring

theorem length_slots (os : Array (List ℕ)) (pc : PoolCert) (val : Val) : (slots os pc val).length = 2 * pc.n := by
  simp [slots, length_slotsN]

/-- An accepted certificate's facts in an assignment holding every constraint but the tests. -/
theorem facts_of_holds {c : Cert} {s : State} (h : c.unionsOk s = true) {st : ℕ → Fin 4 → K} {val : Val}
    (hv : Holds st s c.test val) : Facts c.calls c.relax c.outs st val ∧ RowsIn c.calls c.outs s ∧
      (∀ i < c.prods.size, (c.poolOf i).ok c.outs c.calls c.relax = true ∧
        (c.prods.getD i default).ok c.outs (c.poolOf i) c.calls c.relax = true ∧
        (c.points.getD i default).ok c.outs c.calls c.relax (c.prods.getD i default) = true) := by
  unfold Cert.unionsOk at h
  unfold Cert.outs
  split at h
  · simp at h
  · rename_i t os hr
    rw [hr]
    simp only [Cert.unionsAt, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.all_eq_true,
      List.mem_range] at h
    obtain ⟨⟨⟨hsame, -⟩, hall⟩, hpts⟩ := h
    obtain ⟨-, -, -, hfacts⟩ := replayR_sound c.calls c.relax 0 {} #[] t os inv_empty rfl (Nat.zero_le _)
      (fun j hj => absurd hj (Nat.not_lt_zero j)) hr
    have hsat : Sat st t val := sat_of_sameSat hsame hv
    have hhash : t.hash = s.hash := by
      simp only [sameSat, Bool.and_eq_true, beq_iff_eq] at hsame
      exact hsame.1.1.1.2.symm
    refine ⟨fun j hj hrl _ => (hfacts j hj hj).1 st val hsat hrl, fun j hj => rows_of_hash (hfacts j hj hj).2 hhash,
      fun i hi => ?_⟩
    have hq : c.prods.getD i default ∈ c.prods := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
      exact Array.getElem_mem hi
    exact ⟨(hall _ hq).1, (hall _ hq).2, hpts i hi⟩

theorem PointCert.ok_parts {os : Array (List ℕ)} {pt : PointCert} {cs : Array Call} {rl : Array Bool}
    {qc : ProdCert} (h : pt.ok os cs rl qc = true) :
    callsOk cs rl (pt.calls os) = true ∧ qc.x1 = pt.x1 os ∧ qc.weights = (List.range 16).map (pt.weight os) := by
  simp only [PointCert.ok, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A product's `X + 1` and weights at a point `f` its point takes. -/
theorem cover_point {c : Cert} {s : State} (h : c.unionsOk s = true) {st₀ st : ℕ → Fin 4 → K} {val₀ val : Val}
    (hv₀ : Holds st₀ s c.test val₀) (hv : Holds st s c.test val) {f : Fin 5 → E}
    {i l : ℕ} (hl : l < c.prods.size) (hptl : c.points.getD l default = c.points.getD i default)
    (hx : Model.ev val (c.points.getD i default).x = f 0)
    (ha : ∀ k : Fin 4, Model.ev val ((c.points.getD i default).aj k) = f k.succ) :
    Model.ev val (c.prods.getD l default).x1 = f 0 + 1 ∧
      ∀ k : Fin 16, Model.ev val ((c.prods.getD l default).w k) = eqAt (Fin.tail f) k := by
  obtain ⟨-, -, hcerts⟩ := facts_of_holds h hv₀
  obtain ⟨hF, -, -⟩ := facts_of_holds h hv
  obtain ⟨hcalls, hx1, hw⟩ := PointCert.ok_parts (hcerts l hl).2.2
  rw [hptl] at hcalls hx1 hw
  obtain ⟨hpx, hpw⟩ := point_sem hF hcalls
  refine ⟨by rw [hx1, hpx, hx], fun k => ?_⟩
  rw [ProdCert.w, hw, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range k.isLt,
    Option.map_some, Option.getD_some, hpw k]
  congr 1
  funext t
  exact ha t

/-- At a point `f` that product `i`'s point takes, a product `l` reading the same point, in an assignment agreeing with
`val₀` on its pool's digests, begin and selection bits, is the product of its pool's claims on in `val₀`. -/
theorem cover_side {c : Cert} {s : State} (h : c.unionsOk s = true) {st₀ st : ℕ → Fin 4 → K} {val₀ val : Val}
    (hv₀ : Holds st₀ s c.test val₀) (hv : Holds st s c.test val) (hcr : HashCR s val₀ val) {f : Fin 5 → E}
    {i l : ℕ} (hl : l < c.prods.size) (hptl : c.points.getD l default = c.points.getD i default)
    (hx : Model.ev val (c.points.getD i default).x = f 0)
    (ha : ∀ k : Fin 4, Model.ev val ((c.points.getD i default).aj k) = f k.succ)
    (hag : (c.poolOf l).Agree c.outs val₀ val) :
    Model.ev val (out c.outs (c.poolOf l) (c.prods.getD l default)) =
      prodAt (onClaims (slots c.outs (c.poolOf l) val₀)) (f 0) (Fin.tail f) := by
  obtain ⟨hF₀, hR, hcerts⟩ := facts_of_holds h hv₀
  obtain ⟨hF, -, -⟩ := facts_of_holds h hv
  obtain ⟨hd, hb, hs⟩ := hag
  obtain ⟨hpo, hqo, -⟩ := hcerts l hl
  obtain ⟨hx1, hW⟩ := cover_point h hv₀ hv hl hptl hx ha
  rw [prod_slotsAt hF hpo hqo _ hW, hx1, slots_eq _ (slots_bits hF hpo) (f 0) (Fin.tail f),
    slots_agree hF₀ hF hR hpo hcr hd hb hs]

open Classical Finset in
/-- The coverage check's soundness on the circuit. Products `i` and `j` read one point, squeezed after their pools'
digests, begin and selection bits. If in an assignment `val₀` holding every constraint but the tests the claims on
in the two pools are different multisets, then the points `(X, A)` of `S^5` at which some assignment with the same
digests, begin and selection bits, whose compressions do not collide with `val₀`'s, holds every constraint but the
tests and the coverage test `product_i = product_j`, are at most a `4N/|S|` fraction, `N = 2 · max(n_i, n_j)` the
slots of the larger pool. -/
theorem union_cover (c : Cert) (s : State) (h : c.unionsOk s = true) {i j : ℕ} (hi : i < c.prods.size)
    (hj : j < c.prods.size) (hpt : c.points.getD i default = c.points.getD j default)
    {st₀ : ℕ → Fin 4 → K} {val₀ : Val} (hv₀ : Holds st₀ s c.test val₀)
    (hne : onClaims (slots c.outs (c.poolOf i) val₀) ≠ onClaims (slots c.outs (c.poolOf j) val₀)) (S : Finset E) :
    (#{f ∈ Fintype.piFinset fun _ : Fin 5 => S | ∃ (st : ℕ → Fin 4 → K) (val : Val), Holds st s c.test val ∧
        HashCR s val₀ val ∧ (c.poolOf i).Agree c.outs val₀ val ∧ (c.poolOf j).Agree c.outs val₀ val ∧
        Model.ev val (c.points.getD i default).x = f 0 ∧
        (∀ k : Fin 4, Model.ev val ((c.points.getD i default).aj k) = f k.succ) ∧
        Model.ev val (out c.outs (c.poolOf i) (c.prods.getD i default)) =
          Model.ev val (out c.outs (c.poolOf j) (c.prods.getD j default))} : ℚ≥0) / (#S ^ 5 : ℚ≥0) ≤
      4 * (2 * max (c.poolOf i).n (c.poolOf j).n : ℕ) / #S := by
  classical
  set P := onClaims (slots c.outs (c.poolOf i) val₀)
  set Q := onClaims (slots c.outs (c.poolOf j) val₀)
  set N := 2 * max (c.poolOf i).n (c.poolOf j).n
  have hP : Multiset.card P ≤ N := (card_onClaims _).trans (by rw [length_slots]; omega)
  have hQ : Multiset.card Q ≤ N := (card_onClaims _).trans (by rw [length_slots]; omega)
  -- At a point where some such assignment passes the test, the two multisets' products agree. The sets are the
  -- statements' own, so no two decidability instances need comparing.
  refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card ?_)) (by positivity))
    (coverage_sound P Q N hP hQ hne S)
  intro f hf
  rw [mem_filter] at hf ⊢
  obtain ⟨hfS, st, val, hv, hcr, hai, haj, hx, ha, htest⟩ := hf
  refine ⟨hfS, ?_⟩
  rw [← cover_side h hv₀ hv hcr hi rfl hx ha hai, ← cover_side h hv₀ hv hcr hj hpt.symm hx ha haj, htest]

/-! The union's soundness on an accepted circuit. -/

/-- A point's challenges `(X, A)`. -/
noncomputable def PointCert.at (pt : PointCert) (val : Val) : Fin 5 → E :=
  Fin.cons (Model.ev val pt.x) fun k : Fin 4 => Model.ev val (pt.aj k)

theorem Cert.marks_getD (c : Cert) (s : State) {k : ℕ} (hk : k < (c.marks s).length) :
    (c.marks s).getD k default = (c.transcripts.getD k default, c.times s (c.transcripts.getD k default)) := by
  have hk' : k < c.transcripts.length := by simpa [Cert.marks] using hk
  simp [Cert.marks, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

open Classical Finset in
/-- With the challenge `pt` uniform on `S^5` over the outcomes `Ω`, the outcomes of `A`, each drawing a challenge of
`F ⊆ S^5`, are at most a `#F/|S|^5` fraction. -/
theorem uniform_count {Ω : Type} [Fintype Ω] (S : Finset E) (pt : Ω → Fin 5 → E)
    (hS : ∀ ω, pt ω ∈ Fintype.piFinset fun _ : Fin 5 => S)
    (hpt : ∀ f ∈ Fintype.piFinset (fun _ : Fin 5 => S), #S ^ 5 * #{ω | pt ω = f} = Fintype.card Ω)
    (A : Finset Ω) (F : Finset (Fin 5 → E)) (hF : F ⊆ Fintype.piFinset fun _ : Fin 5 => S)
    (hA : ∀ ω ∈ A, pt ω ∈ F) : (#A : ℚ≥0) / Fintype.card Ω ≤ #F / (#S ^ 5 : ℚ≥0) := by
  have hsub : A ⊆ F.biUnion fun f => {ω | pt ω = f} := by
    intro ω hω
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    exact ⟨pt ω, hA ω hω, rfl⟩
  have hcard := (card_le_card hsub).trans card_biUnion_le
  have hsum : #S ^ 5 * ∑ f ∈ F, #({ω | pt ω = f} : Finset Ω) = #F * Fintype.card Ω := by
    rw [mul_sum, sum_congr rfl fun f hf => hpt f (hF hf), sum_const, smul_eq_mul]
  rcases (Fintype.card Ω).eq_zero_or_pos with h0 | h0
  · rw [h0]; simp
  have hS0 : 0 < #S := by
    obtain ⟨ω⟩ : Nonempty Ω := Fintype.card_pos_iff.mp h0
    have := hS ω
    rw [Fintype.mem_piFinset] at this
    exact card_pos.mpr ⟨_, this 0⟩
  rw [div_le_div_iff₀ (by exact_mod_cast h0) (by positivity)]
  have key : #A * #S ^ 5 ≤ #F * Fintype.card Ω := by
    rw [mul_comm, ← hsum]
    exact Nat.mul_le_mul_left _ hcard
  exact_mod_cast key

open Classical Finset in
/-- The union's soundness. Take an accepted circuit and one of its unions (`cv`): the coverage test of the products
over the children's selected claims and the declared claims, and the transcript drawing their point `(X, A)`. Fix
what the transcript absorbs by an assignment `val₀` holding every constraint but the tests, in which the selected
child claims and the declared claims are different multisets. The point is the transcript's challenge, uniform on
`S^5` (`pt`, over the outcomes `Ω`). For each outcome the prover answers with an assignment holding every constraint
but the tests, whose transcript absorbs the same words and whose compressions and output windows do not collide with
`val₀`'s. Then the outcomes at which its point is the challenge and the coverage test holds are at most a `4N/|S|`
fraction, `N` the slots of the larger pool. -/
theorem union_sound (c : Cert) (s : State) (h : c.accepts s = true) {cv : Cover} (hcv : cv ∈ c.covers)
    {st₀ : ℕ → Fin 4 → K} {val₀ : Val} (hv₀ : Holds st₀ s c.test val₀)
    (hne : onClaims (slots c.outs (c.poolOf cv.sel) val₀) ≠ onClaims (slots c.outs (c.poolOf cv.decl) val₀))
    (S : Finset E) {Ω : Type} [Fintype Ω] (pt : Ω → Fin 5 → E) (hS : ∀ ω, pt ω ∈ Fintype.piFinset fun _ : Fin 5 => S)
    (hpt : ∀ f ∈ Fintype.piFinset (fun _ : Fin 5 => S), #S ^ 5 * #{ω | pt ω = f} = Fintype.card Ω)
    (st : Ω → ℕ → Fin 4 → K) (val : Ω → Val) (hv : ∀ ω, Holds (st ω) s c.test (val ω))
    (hcr : ∀ ω, HashCR s val₀ (val ω)) (hwin : ∀ ω, WindowCR s val₀ (val ω))
    (hseed : ∀ ω, ∀ n ∈ seedsOf s (c.transcripts.getD cv.transcript default), nu val₀ n = nu (val ω) n) :
    (#{ω | (c.points.getD cv.sel default).at (val ω) = pt ω ∧
        ∀ a b, s.unions[cv.test]? = some (a, b) → val ω a = val ω b} : ℚ≥0) / Fintype.card Ω ≤
      4 * (2 * max (c.poolOf cv.sel).n (c.poolOf cv.decl).n : ℕ) / #S := by
  classical
  obtain ⟨hr, -, hun, -, -, hcov⟩ := Cert.accepts_parts h
  simp only [Cert.coversOk, Bool.and_eq_true, Array.all_eq_true', List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hcov
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsel, hdecl⟩, htr⟩, -⟩, hpts⟩, hu⟩, hm⟩, -⟩, -⟩, -⟩ := hcov.2 cv hcv
  rw [Cert.marks_getD c s htr] at hm
  -- What both pools commit to is in the transcript's closure, so the answers agree with `val₀` on it.
  have hagree : ∀ ω, ∀ w ∈ (c.poolOf cv.sel).committed c.outs ++ (c.poolOf cv.decl).committed c.outs,
      val₀ w = val ω w := by
    intro ω w hw
    have hvalid := fun i hi => rules_valid (L := fun _ => True) hr (hv₀.toP _) ((hv ω).toP _) ((hcr ω).toP _ _)
      ((hwin ω).toP _ _) (unionsValid c s hun hv₀ (hv ω) (hcr ω)) i hi fun _ _ => trivial
    exact eq_of_limbs4 fun n hn => by
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hm n (List.mem_flatMap.mpr ⟨w, hw, hn⟩))
      exact closure_agree hvalid (hseed ω) ((Cert.times_sound c s _ hk).mono seedsBefore_seedsOf)
  refine le_trans (uniform_count S pt hS hpt _ _ (filter_subset _ _) fun ω hω => ?_)
    (union_cover c s hun hsel hdecl hpts hv₀ hne S)
  rw [mem_filter] at hω ⊢
  obtain ⟨-, hat, htest⟩ := hω
  have heq := htest _ _ hu
  refine ⟨hS ω, st ω, val ω, hv ω, hcr ω,
    PoolCert.agree_of_committed fun w hw => hagree ω w (List.mem_append_left _ hw),
    PoolCert.agree_of_committed fun w hw => hagree ω w (List.mem_append_right _ hw), ?_, fun k => ?_, ?_⟩
  · rw [← hat]; simp [PointCert.at]
  · rw [← hat]; simp [PointCert.at]
  · unfold Model.ev; rw [heq]

end LeanVMCircuits.Rec.Bind
