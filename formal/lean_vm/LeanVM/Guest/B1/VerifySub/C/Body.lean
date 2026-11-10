/-
  LeanVM.Guest.B1.VerifySub.C.Body

  `verify_sub`'s statements hold on its honest valuation, from the memory's words and the
  oracle's values (`VsSecData`).
-/

module

public import LeanVM.Guest.B1.VerifySub.C.ValsB

/-!
# The body, honestly

`VsSecData rd w args`: what the honest valuation `vsσ rd w args` needs of the memory `rd` and the
oracle `w` (the allocations and the callees' returns): the stream's first eleven words, the
buffers the body reads or stores into holding their words (`table_rows`, `dims_g`,
`kappa_base`, the exponent table's squares at the push blocks, `fp_w`, the ring map's
challenges, `c_table`, the pooled claims, the deferred claim's cells), and the callees' powers
of `g` (the rate, the memory's log, the bus depth, the stack's log).

`vsSideA`: the atoms of the body whose side condition is not automatic, by the kernel (reads,
stores, range checks, two quotients); `vs_sideHolds` proves each from the data, `vs_dispIdx` the
three dispatches' indices, and `vsCPre_complete`: every statement of `verify_sub` but its `ret`
holds under the trivial call relation.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The atoms needing a side condition -/

/-- The values the stream's words at offsets `0 .. 10` are read into. -/
def vsWv11 (k : ℕ) : ℕ := [27, 30, 33, 36, 52, 55, 58, 61, 268, 271, 283].getD k 0

/-! Pieces of the atoms needing a side condition. -/

def vsSPw : List Atom := (List.range 11).map fun k ↦ .load (.n (vsWv11 k)) (.n 25) k
def vsSProws : List Atom := (List.range 6).map fun i ↦ .load (.n (vsX (i + 1))) (.n 26) i
def vsSPquot : List Atom := [.mul (.n 64) (.n 66) (.n 65), .mul (.n 72) (.n 79) (.n 78)]
def vsSPrng : List Atom :=
  [.rangeCheck (.n 66) (.n 68) (.n 69) (.n 70) (.n 67),
    .rangeCheck (.n 72) (.n 74) (.n 75) (.n 76) (.n 73),
    .rangeCheck (.n 79) (.n 80) (.n 81) (.n 82) (.n 77),
    .rangeCheck (.n 278) (.n 280) (.n 281) (.n 282) (.n 279),
    .rangeCheck (.n 322) (.n 324) (.n 325) (.n 326) (.n 323),
    .rangeCheck (.n 1922) (.n 1924) (.n 1925) (.n 1926) (.n 1923)]
def vsSPdims : List Atom :=
  .load (.n 72) (.n 71) 0 :: .load (.n 583) (.n 71) 6 ::
    (List.range 6).map fun t ↦ .load (.n (86 + t)) (.n 71) (1 + t)
def vsSPkb : List Atom := (List.range 8).map fun i ↦ .load (.n (84 + i)) (.n 83) i
def vsSPpush : List Atom :=
  (List.range 54).map fun b ↦ .load (.n (vsPushD b)) (.n (vsPushP b)) (Tables.blockKappaAdj b)
def vsSPfpw : List Atom :=
  (List.range 16).map fun i ↦ .load (.n (if i = 0 then 313 else 335 + 14 * i)) (.n 335) i
def vsSPmaps : List Atom :=
  .load (.n 602) (.n 595) 0 :: (List.range 16).map fun i ↦ .load (.n (vsCh i)) (.n 847) i
def vsSPctab : List Atom :=
  (List.range 8).flatMap fun b ↦ (List.range 8).map fun p ↦
    .load (.n (vsCtabD b p)) (.n 848) (8 * p + b)
def vsSPlam : List Atom :=
  .load (.n 1915) (.n 310) 0 :: (List.range 134).map fun i ↦
    .load (.n (1376 + 4 * i)) (.n (vsClaimAt (vsKept i)).1) (vsClaimAt (vsKept i)).2
def vsSPz : List Atom := (List.range 19).map fun k ↦ .load (.n (1936 + k)) (.n 254) k
def vsSPzo : List Atom := (List.range 19).map fun k ↦ .load (.n (1936 + k)) (.n 5) k
def vsSPal : List Atom := (List.range 4).map fun k ↦ .load (.n (1955 + k)) (.n 570) k
def vsSPalo : List Atom := (List.range 4).map fun k ↦ .load (.n (1955 + k)) (.n 5) (19 + k)
def vsSPlast : List Atom := [.load (.n 580) (.n 5) 23]

/-- The atoms of the body needing a side condition, piece by piece. -/
def vsSidePieces : List Atom :=
  [vsSPw, vsSProws, vsSPquot, vsSPrng, vsSPdims, vsSPkb, vsSPpush, vsSPfpw, vsSPmaps, vsSPctab,
    vsSPlam, vsSPz, vsSPzo, vsSPal, vsSPalo, vsSPlast].flatten

/-- A statement is no atom needing a side condition, or one of `vsSidePieces`. -/
def vsSideOk : Stmt → Bool
  | .atom a => !needsSide a || vsSidePieces.contains a
  | _ => true

theorem vs_sideCls : vsCPre.all vsSideOk = true := by decide +kernel

theorem vs_side_mem {a : Atom} (hs : Stmt.atom a ∈ vsCPre) (hn : needsSide a = true) :
    a ∈ vsSidePieces := by
  have h := List.all_eq_true.mp vs_sideCls _ hs
  simp only [vsSideOk, hn, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h
  exact h

/-! ## What the sections take -/

/-- **What the honest valuation needs** of the memory and the oracle. -/
structure VsSecData (rd : Reader) (w : ℕ → E) (args : List E) : Type where
  hl : args.length = 6
  /-- The memory is defined below `2^κ`. -/
  κ : ℕ
  hκ : 16 ≤ κ
  hlow : LowDef κ rd
  /-- The stream's first eleven words: the eight sizes, the root's two, the nonce. -/
  ws : List E
  hwl : 11 ≤ ws.length
  hws : ∀ k < 11, LoadHolds rd (w 25) k (ws.getD k 0)
  hrows : ∀ i < 6, LoadHolds rd (w 26) i (ws.getD (i + 1) 0)
  /-- The rate and the memory's log, as `g_power_of_word` returns them. -/
  rate : ℕ
  logMem : ℕ
  hr1 : 1 ≤ rate
  hr4 : rate ≤ 4
  hm16 : 16 ≤ logMem
  hm32 : logMem ≤ 32
  h64 : w 64 = gen ^ rate
  h72 : w 72 = gen ^ logMem
  /-- `dims_g` and `kappa_base`. -/
  hsW : List E
  hsWl : hsW.length = 6
  hdims : ReadsAt rd (w 71) (w 72 :: hsW)
  hkb : ReadsAt rd (w 83) (1 :: w 72 :: hsW)
  /-- The push blocks' squares. -/
  hpush : ∀ b < 54, ∃ v, LoadHolds rd
    (args.getD 4 0 * (1 :: w 72 :: hsW).getD (Tables.blockKappaSrc.getD b 0) 0)
    (Tables.blockKappaAdj b) v
  /-- The bus depth and the stack's log, as `log2_ceil_in_the_exponent` returns them. -/
  d : ℕ
  m : ℕ
  hd16 : 16 ≤ d
  hd33 : d ≤ 33
  hm22 : 22 ≤ m
  hm28 : m ≤ 28
  h253 : w 253 = gen ^ d
  h276 : w 276 = gen ^ m
  /-- `ood_value`, `fp_w`, `col_eval_words`, `claim_pool`. -/
  hood : ∃ v, LoadHolds rd (w 310) 0 v
  hfpw : ReadsAt rd (w 335) (w 313 :: ((vsFpwFs w).squeezeN 15).1)
  hcol : ∀ k < 153, ∃ v, LoadHolds rd (w 582) k v
  hpool : ∀ k ∈ [0, 1, 2, 3, 157, 158], ∃ v, LoadHolds rd (w 6) k v
  /-- The ring map's nonce, challenges and `c_table`. -/
  nonce : E
  hnonce : LoadHolds rd (w 595) 0 nonce
  hmaps : ReadsAt rd (w 847) (vsRchs (vsKCap w) nonce)
  hct : ReadsAt rd (w 848) (ringCoefficients ((vsRchs (vsKCap w) nonce).take 8)
    ((vsRchs (vsKCap w) nonce).drop 8))
  /-- `zeta`, `bc_point` and the deferred claim's cells. -/
  zs : List E
  hzl : 19 ≤ zs.length
  hz : ReadsAt rd (w 254) zs
  al : List E
  hall : al.length = 4
  hal : ReadsAt rd (w 570) al
  hout : ReadsAt rd (args.getD 5 0) (zs.take 19 ++ al ++ [w 580])

/-! ## Helpers -/

theorem rdg {rd : Reader} {p : E} {xs : List E} {k : ℕ} (h : ReadsAt rd p xs) (hk : k < xs.length) :
    LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

theorem rdAt_of_load {rd : Reader} {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) :
    rdAt rd p k = v := by
  unfold rdAt; rw [h.2]; rfl

theorem vsSPw_notS : ∀ k < 11, Atom.load (.n (vsWv11 k)) (.n 25) k ∉ vsSL := by decide +kernel

theorem vsSPdims_notS : ∀ t < 6, Atom.load (.n (86 + t)) (.n 71) (1 + t) ∉ vsSL := by
  decide +kernel

theorem vsSPpush_notS : ∀ b < 54,
    Atom.load (.n (vsPushD b)) (.n (vsPushP b)) (Tables.blockKappaAdj b) ∉ vsSL := by
  decide +kernel

theorem ld_new {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d p : V} {off : ℕ} {v : E}
    (hg : GoodS rd S w σ (.atom (.load d p off))) (hS : Atom.load d p off ∉ S)
    (hv : LoadHolds rd (σ p) off v) : (Atom.load d p off).Holds rd σ := by
  show LoadHolds _ _ _ _
  rw [good_read hg hS hv]; exact hv

theorem ld_store {rd : Reader} {σ : Val} {d p : V} {off : ℕ} {v : E} (hd : σ d = v)
    (hv : LoadHolds rd (σ p) off v) : (Atom.load d p off).Holds rd σ := by
  show LoadHolds _ _ _ _
  rw [hd]; exact hv

theorem gen_defined' {κ : ℕ} {rd : Reader} (hlow : LowDef κ rd) {a : ℕ} (ha : a < 2 ^ κ) :
    (rd ((gen ^ a).limb 0 * Parameters.addressOfIndex 0)).isSome := by
  rw [gen_pow_eq_ofK, show Parameters.addressOfIndex 0 = 1 from pow_zero _, mul_one]
  rw [show (ofK (Parameters.addressOfIndex a)).limb 0 = Parameters.addressOfIndex a by simp]
  exact hlow a ha

/-- A range check of `g^a` against `g^c`, `a ≤ c < 2^κ`, on an evaluated valuation. -/
theorem rc_holds {κ : ℕ} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} (hlow : LowDef κ rd)
    {x y t1 t2 k : V} (hk : k.idx < y.idx) {a c : ℕ} (hac : a ≤ c) (hc : c < 2 ^ κ)
    (hx : σ x = gen ^ a) (hkv : σ k = gen ^ c) (hg : Good rd S w σ (.rangeCheck x y t1 t2 k)) :
    (Atom.rangeCheck x y t1 t2 k).Holds rd σ := by
  have hy : σ y = gen ^ (c - a) := by
    simp only [Good] at hg
    rw [ite_pos' hk] at hg
    rw [hg.2.2, hkv, hx, ← pow_sub₀ _ gen_ne_zero hac]
  refine holds_of_good hg ?_
  simp only [Side]
  rw [ite_pos' hk, hx, hy]
  exact ⟨gen_pow_isInK a, gen_defined' hlow (by omega), gen_pow_isInK _,
    gen_defined' hlow (by omega), pow_ne_zero _ gen_ne_zero⟩

theorem quot_holds {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d x y : V}
    (hd : ¬ (x.idx < d.idx ∧ y.idx < d.idx)) (hy : σ y ≠ 0) (hg : Good rd S w σ (.mul d x y)) :
    (Atom.mul d x y).Holds rd σ := by
  refine holds_of_good hg ?_
  simp only [Side]
  rw [ite_neg' hd]
  exact hy

/-- `(range n).flatMap F` at `8 p + b`, blocks of eight. -/
theorem getD_flatMap8 {F : ℕ → List E} (hF : ∀ q, (F q).length = 8) :
    ∀ n p b, p < n → b < 8 → ((List.range n).flatMap F).getD (8 * p + b) 0 = (F p).getD b 0
  | 0, _, _, h, _ => absurd h (by omega)
  | n + 1, p, b, hp, hb => by
    have hl : ((List.range n).flatMap F).length = 8 * n := by
      simp [List.length_flatMap, hF, mul_comm]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
      exact getD_flatMap8 hF n p b hp hb
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl,
        show 8 * p + b - 8 * p = b by omega, ← List.getD_eq_getElem?_getD]

/-! ## The pieces hold -/

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

local notation "ς" => vsσ rd w args

theorem vs_param4 (hl : args.length = 6) : ς (.n 4) = args.getD 4 0 := vsC_param hl (by omega)
theorem vs_param5 (hl : args.length = 6) : ς (.n 5) = args.getD 5 0 := vsC_param hl (by omega)

/-- `kb` in the frame: `1`, `g^logMem`, `dims_g[1 .. 6]`. -/
theorem vs_kbV (D : VsSecData rd w args) :
    ∀ i < 8, ς (.n (84 + i)) = (1 :: w 72 :: D.hsW).getD i 0 := by
  obtain ⟨h65, -, -, h72, -, -, -, -, h84, h85, h86⟩ :=
    vs_sizesV (rd := rd) (w := w) D.hl D.hr1 D.hm16 D.h64 D.h72
  intro i hi
  rcases i with _ | _ | t
  · exact h84
  · rw [h85, D.h72]; rfl
  · rw [show 84 + (t + 2) = 86 + t by omega, h86 t (by omega)]
    have := rdg D.hdims (k := 1 + t) (by simp [D.hsWl]; omega)
    rw [rdAt_of_load this]
    simp only [List.getD_cons_succ, show 1 + t = t + 1 by omega]

theorem vsSPw_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPw, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  intro a ha hs
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
  rw [List.mem_range] at hk
  exact ld_new (vs_goodS D.hl hs) (vsSPw_notS k hk)
    (by rw [vs_w D.hl (by decide)]; exact D.hws k hk)

theorem vsSProws_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSProws, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  intro a ha _
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  rw [List.mem_range] at hi
  have W := vs_word (rd := rd) (w := w) D.hl (k := i + 1) (by omega) (D.hws (i + 1) (by omega))
  rw [vsWv_lt (i + 1) (by omega)] at W
  exact ld_store W.1 (by rw [vs_w D.hl (by decide)]; exact D.hrows i hi)

theorem vsSPquot_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPquot, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  obtain ⟨h65, -, -, -, -, h78, -⟩ := vs_sizesV (rd := rd) (w := w) D.hl D.hr1 D.hm16 D.h64 D.h72
  intro a ha hs
  have hg := vs_goodS (rd := rd) (w := w) D.hl hs
  simp only [vsSPquot, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact quot_holds (S := vsSL) (w := w) (by simp) (by rw [h65]; exact gen_ne_zero) hg
  · exact quot_holds (S := vsSL) (w := w) (by simp) (by rw [h78]; exact pow_ne_zero _ gen_ne_zero) hg

theorem vsSPrng_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPrng, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  obtain ⟨-, h66, h67, h72, h73, -, h79, h77, -⟩ :=
    vs_sizesV (rd := rd) (w := w) D.hl D.hr1 D.hm16 D.h64 D.h72
  obtain ⟨h278, h279⟩ := vs_placeV (rd := rd) (w := w) D.hl D.hm22 D.h276
  obtain ⟨h322, h323, -⟩ := vs_busGrind (rd := rd) (w := w) D.hl D.hd16 D.h253
  obtain ⟨h1922, h1923, -⟩ := vs_tailV (rd := rd) (w := w) D.hl D.hr1 D.hm22 D.h64 D.h276
  have hκ : (40 : ℕ) < 2 ^ D.κ :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) D.hκ)
  have hr := D.hr4
  have hm := D.hm32
  have hm28 := D.hm28
  have hd := D.hd33
  intro a ha hs
  have hg := vs_goodS (rd := rd) (w := w) D.hl hs
  simp only [vsSPrng, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rc_holds (S := vsSL) (w := w) D.hlow (by simp) (by omega) (by omega) h66 h67 hg
  · exact rc_holds (S := vsSL) (w := w) D.hlow (by simp) D.hm32 (by omega) h72 h73 hg
  · exact rc_holds (S := vsSL) (w := w) D.hlow (by simp) (by omega) (by omega) h79 h77 hg
  · exact rc_holds (S := vsSL) (w := w) D.hlow (by simp) (by omega) (by omega) h278 h279 hg
  · exact rc_holds (S := vsSL) (w := w) D.hlow (by simp) (by omega) (by omega) h322 h323 hg
  · exact rc_holds (S := vsSL) (w := w) D.hlow (by simp) (by omega) (by omega) h1922 h1923 hg

theorem vsSPdims_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPdims, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  intro a ha hs
  have hg := vs_goodS (rd := rd) (w := w) D.hl hs
  have e71 : ς (.n 71) = w 71 := vs_w D.hl (by decide)
  simp only [vsSPdims, List.mem_cons, List.mem_map, List.mem_range] at ha
  rcases ha with rfl | rfl | ⟨t, ht, rfl⟩
  · refine ld_store (vs_w D.hl (by decide)) ?_
    rw [e71]; exact rdg D.hdims (k := 0) (by simp)
  · refine ld_new hg (by decide +kernel) (v := (w 72 :: D.hsW).getD 6 0) ?_
    rw [e71]; exact rdg D.hdims (k := 6) (by simp [D.hsWl])
  · refine ld_new hg (vsSPdims_notS t ht) (v := (w 72 :: D.hsW).getD (1 + t) 0) ?_
    rw [e71]; exact rdg D.hdims (k := 1 + t) (by simp [D.hsWl]; omega)

theorem vsSPkb_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPkb, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  intro a ha _
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  rw [List.mem_range] at hi
  refine ld_store (vs_kbV D i hi) ?_
  rw [vs_w D.hl (by decide)]
  exact rdg D.hkb (by simp [D.hsWl]; omega)

theorem vsSPpush_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPpush, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  intro a ha hs
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
  rw [List.mem_range] at hb
  obtain ⟨v, hv⟩ := D.hpush b hb
  have hsrc : Tables.blockKappaSrc.getD b 0 < 8 := blockKappaSrc_lt b (by show b < 153; omega)
  refine ld_new (vs_goodS D.hl hs) (vsSPpush_notS b hb) (v := v) ?_
  rw [vs_pushP D.hl hb, vs_kbV D _ hsrc, vs_param4 D.hl]; exact hv

theorem vsSPfpw_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPfpw, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  intro a ha _
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  rw [List.mem_range] at hi
  have hlen : (w 313 :: ((vsFpwFs w).squeezeN 15).1).length = 16 := by
    simp [vs_squeezeN_length]
  have hr := rdg D.hfpw (k := i) (by omega)
  rw [← vs_w (rd := rd) (w := w) (args := args) D.hl (a := 335) (by decide)] at hr
  refine ld_store ?_ hr
  rcases i with _ | i
  · exact vs_w D.hl (by decide)
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, List.getD_cons_succ]
    rw [show 335 + 14 * (i + 1) = 349 + 14 * i by omega]
    exact (vs_fpw (rd := rd) (w := w) D.hl).1 i (by omega)

theorem vsRchs_length (cap : List E) (n : E) : (vsRchs cap n).length = 16 := by
  simp [vsRchs, vs_squeezeN_length]

theorem vsSPmaps_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPmaps, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  obtain ⟨-, -, -, hch, -⟩ := vs_maps (rd := rd) (w := w) (args := args) D.hl D.hnonce
  intro a ha hs
  simp only [vsSPmaps, List.mem_cons, List.mem_map, List.mem_range] at ha
  rcases ha with rfl | ⟨i, hi, rfl⟩
  · exact ld_new (vs_goodS D.hl hs) (by decide +kernel)
      (by rw [vs_w D.hl (by decide)]; exact D.hnonce)
  · refine ld_store (hch i hi) ?_
    rw [vs_w D.hl (by decide)]
    exact rdg D.hmaps (by rw [vsRchs_length]; exact hi)

theorem vsSPctab_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPctab, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  obtain ⟨-, -, -, hch, -⟩ := vs_maps (rd := rd) (w := w) (args := args) D.hl D.hnonce
  intro a ha _
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.1 ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  rw [List.mem_range] at hb hp
  have hR : (vsRchs (vsKCap w) D.nonce).length = 16 := vsRchs_length _ _
  have hct := D.hct
  generalize vsRchs (vsKCap w) D.nonce = R at hch hct hR
  have ht8 : (R.take 8).length = 8 := by simp [hR]
  refine ld_store (vs_ctabV D.hl hb p hp) ?_
  rw [hch p (by omega), hch (8 + b) (by omega), vs_w D.hl (a := 848) (by decide)]
  have hr := rdg hct (k := 8 * p + b)
    (by rw [ringCoefficients_eq ht8]; simp [List.length_flatMap, hR]; omega)
  rw [ringCoefficients_eq ht8, getD_flatMap8 (fun q ↦ by simp [hR]) 8 p b hp hb] at hr
  have e1 : (R.take 8).getD p 0 = R.getD p 0 := by
    simp [List.getD_eq_getElem?_getD, hp]
  have e3 : (R.drop 8).getD b 0 = R.getD (8 + b) 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hb8 : b < (R.drop 8).length := by simp [hR]; omega
  rw [List.getD_eq_getElem _ _ (by simpa using hb8), List.getElem_map,
    ← List.getD_eq_getElem _ 0 hb8, e1, e3, zero_add] at hr
  exact hr

theorem vsSPlam_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPlam, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  intro a ha hs
  simp only [vsSPlam, List.mem_cons, List.mem_map, List.mem_range] at ha
  rcases ha with rfl | ⟨i, hi, rfl⟩
  · obtain ⟨v, hv⟩ := D.hood
    exact ld_new (vs_goodS D.hl hs) (by decide +kernel) (v := v)
      (by rw [vs_w D.hl (by decide)]; exact hv)
  · have hk : vsKept i < 159 := by simp only [vsKept]; split <;> omega
    have hex : ∃ v, LoadHolds rd (ς (.n (vsClaimAt (vsKept i)).1)) (vsClaimAt (vsKept i)).2 v := by
      unfold vsClaimAt
      split_ifs with h
      · obtain ⟨v, hv⟩ := D.hcol (vsKept i - 4) (by omega)
        exact ⟨v, by rw [vs_w D.hl (a := 582) (by decide)]; exact hv⟩
      · obtain ⟨v, hv⟩ := D.hpool (vsKept i) (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
        exact ⟨v, by rw [vs_w D.hl (a := 6) (by decide)]; exact hv⟩
    obtain ⟨v, hv⟩ := hex
    exact ld_new (vs_goodS D.hl hs) (vsLamT_notS i hi) hv

theorem vsSPz_notS : ∀ k < 19, Atom.load (.n (1936 + k)) (.n 254) k ∉ vsSL := by decide +kernel

theorem vsSPal_notS : ∀ k < 4, Atom.load (.n (1955 + k)) (.n 570) k ∉ vsSL := by decide +kernel

theorem vsSPz_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPz, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  intro a ha hs
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
  rw [List.mem_range] at hk
  exact ld_new (vs_goodS D.hl hs) (vsSPz_notS k hk)
    (by rw [vs_w D.hl (by decide)]; exact rdg D.hz (by have := D.hzl; omega))

theorem vsSPal_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPal, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  intro a ha hs
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
  rw [List.mem_range] at hk
  exact ld_new (vs_goodS D.hl hs) (vsSPal_notS k hk)
    (by rw [vs_w D.hl (by decide)]; exact rdg D.hal (by have := D.hall; omega))

theorem vs_zv (D : VsSecData rd w args) {k : ℕ} (hk : k < 19) :
    ς (.n (1936 + k)) = D.zs.getD k 0 := by
  have hm : Stmt.atom (.load (.n (1936 + k)) (.n 254) k) ∈ vsTailP := by
    rw [vsTailP]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, List.mem_cons_self⟩)))
  exact good_read (vsTailP_good D.hl _ hm) (vsSPz_notS k hk)
    (by rw [vs_w D.hl (by decide)]; exact rdg D.hz (by have := D.hzl; omega))

theorem vs_alv (D : VsSecData rd w args) {k : ℕ} (hk : k < 4) :
    ς (.n (1955 + k)) = D.al.getD k 0 := by
  have hm : Stmt.atom (.load (.n (1955 + k)) (.n 570) k) ∈ vsTailP := by
    rw [vsTailP]
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, List.mem_cons_self⟩))
  exact good_read (vsTailP_good D.hl _ hm) (vsSPal_notS k hk)
    (by rw [vs_w D.hl (by decide)]; exact rdg D.hal (by have := D.hall; omega))

theorem vs_outLen (D : VsSecData rd w args) : (D.zs.take 19 ++ D.al ++ [w 580]).length = 24 := by
  have := D.hzl; have := D.hall
  simp; omega

theorem vsSPout_holds (D : VsSecData rd w args) :
    ∀ a ∈ vsSPzo ++ vsSPalo ++ vsSPlast, Stmt.atom a ∈ vsCPre → a.Holds rd ς := by
  have hzl := D.hzl
  have hall := D.hall
  have h5 := vs_param5 (rd := rd) (w := w) D.hl
  intro a ha _
  simp only [vsSPzo, vsSPalo, vsSPlast, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | rfl
  · refine ld_store (vs_zv D hk) ?_
    have hr := rdg D.hout (k := k) (by rw [vs_outLen]; omega)
    rw [h5]
    have e : (D.zs.take 19).getD k 0 = D.zs.getD k 0 := by
      simp [List.getD_eq_getElem?_getD, hk]
    rwa [List.append_assoc, List.getD_append _ _ _ _ (by rw [List.length_take]; omega), e] at hr
  · refine ld_store (vs_alv D hk) ?_
    have hr := rdg D.hout (k := 19 + k) (by rw [vs_outLen]; omega)
    rw [h5]
    rwa [List.getD_append _ _ _ _ (by rw [List.length_append, List.length_take]; omega),
      List.getD_append_right _ _ _ _ (by rw [List.length_take]; omega),
      show 19 + k - (D.zs.take 19).length = k by rw [List.length_take]; omega] at hr
  · refine ld_store (vs_w D.hl (a := 580) (by decide)) ?_
    have hr := rdg D.hout (k := 23) (by rw [vs_outLen]; omega)
    rw [h5]
    rwa [List.getD_append_right _ _ _ _ (by rw [List.length_append, List.length_take]; omega),
      show 23 - (D.zs.take 19 ++ D.al).length = 0 by
        rw [List.length_append, List.length_take]; omega] at hr

/-- **Every atom needing a side condition holds.** -/
theorem vs_sideHolds (D : VsSecData rd w args) :
    ∀ a, Stmt.atom a ∈ vsCPre → needsSide a = true → a.Holds rd ς := by
  intro a hs hn
  obtain ⟨l, hl, ha⟩ := List.mem_flatten.1 (vs_side_mem hs hn)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact vsSPw_holds D a ha hs
  · exact vsSProws_holds D a ha hs
  · exact vsSPquot_holds D a ha hs
  · exact vsSPrng_holds D a ha hs
  · exact vsSPdims_holds D a ha hs
  · exact vsSPkb_holds D a ha hs
  · exact vsSPpush_holds D a ha hs
  · exact vsSPfpw_holds D a ha hs
  · exact vsSPmaps_holds D a ha hs
  · exact vsSPctab_holds D a ha hs
  · exact vsSPlam_holds D a ha hs
  · exact vsSPz_holds D a ha hs
  · exact vsSPout_holds D a (List.mem_append_left _ (List.mem_append_left _ ha)) hs
  · exact vsSPal_holds D a ha hs
  · exact vsSPout_holds D a (List.mem_append_left _ (List.mem_append_right _ ha)) hs
  · exact vsSPout_holds D a (List.mem_append_right _ ha) hs

/-! ## The dispatches -/

/-- A dispatch's selector and its number of callees. -/
def dispOf : Stmt → Option (V × ℕ)
  | .dispatch x fs _ _ => some (x, fs.length)
  | _ => none

theorem vs_disps : vsCPre.filterMap dispOf = [(.n 278, 7), (.n 322, 18), (.n 1922, 28)] := by
  decide +kernel

/-- **The dispatches' indices**: `g^(m - 22)`, `g^(d - 16)` and the candidate. -/
theorem vs_dispIdx (D : VsSecData rd w args) : ∀ x fs as rs, Stmt.dispatch x fs as rs ∈ vsCPre →
    ∃ j < fs.length, j < 2 ^ 64 - 1 ∧ ς x = ofK (addressOfIndex j) := by
  obtain ⟨h278, -⟩ := vs_placeV (rd := rd) (w := w) D.hl D.hm22 D.h276
  obtain ⟨h322, -⟩ := vs_busGrind (rd := rd) (w := w) D.hl D.hd16 D.h253
  obtain ⟨h1922, -⟩ := vs_tailV (rd := rd) (w := w) D.hl D.hr1 D.hm22 D.h64 D.h276
  have := D.hm28; have := D.hd33; have := D.hr4
  intro x fs as rs h
  have hm : (x, fs.length) ∈ vsCPre.filterMap dispOf := List.mem_filterMap.2 ⟨_, h, rfl⟩
  rw [vs_disps] at hm
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩
  · exact ⟨D.m - 22, by omega, by omega, by rw [h278, gen_pow_eq_ofK]⟩
  · exact ⟨D.d - 16, by omega, by omega, by rw [h322, gen_pow_eq_ofK]⟩
  · exact ⟨D.m - 22 + 7 * (D.rate - 1), by omega, by omega, by rw [h1922, gen_pow_eq_ofK]⟩

/-- **The dispatches' selectors** name one of their callees (`completeAt_flatDepR`'s `DispOk`). -/
theorem vs_dispOk (D : VsSecData rd w args) : ∀ s ∈ vsCPre, DispOk ς s := by
  intro s hs
  cases s with
  | dispatch x fs as rs => exact vs_dispIdx D x fs as rs hs
  | _ => trivial

/-- **`verify_sub`'s statements but its `ret` hold on its honest valuation**, under the trivial
call relation. -/
theorem vsCPre_complete (D : VsSecData rd w args) {next : Prop} {kret : List E → Prop}
    (hn : next) : Stmt.HoldsList (fun _ _ _ ↦ True) rd ς vsCPre next kret :=
  vsCPre_holds_of D.hl (vs_sideHolds D) (fun x fs as rs h ↦
    let ⟨j, hj, _, hx⟩ := vs_dispIdx D x fs as rs h; ⟨j, hj, hx⟩) hn

end

end
end LeanVM.Guest.B1.VerifySub
