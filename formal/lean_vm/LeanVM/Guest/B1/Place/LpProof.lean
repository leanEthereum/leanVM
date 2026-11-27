/-
  LeanVM.Guest.B1.Place.LpProof

  `level_positions` placed at every frame pointer (`lp_placed`).
-/

module

public import LeanVM.Guest.B1.Place.Lp
public import LeanVM.Guest.B1.Bits.QueryWindowsAtAll
public import LeanVM.Guest.Memory.PopsNil
public import LeanVM.Guest.B1.Whir.Commit
public import LeanVM.Guest.B1.Whir.DataSpec
public import LeanVM.Guest.B1.Whir.HelperAll
import LeanVM.Guest.StmtsAppend

/-!
# `level_positions`, placed

`lp_placed`: at every frame pointer, the specialization's walk is straight-line (its squeeze run
allocated, the capacity stored in row `1`, the decoders' group, the last row loaded and
returned); on every memory holding its squeeze run (`lpSqzW`: row `j ≥ 1` the capacity after
`j - 1` squeezes), the decoders' runs and the caller's words, it relates its arguments to the last
capacity in `lpN` words, the group placed by `os_sq_groupE`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-! ## Square and multiply, honestly -/

/-- The values of the square-and-multiply chain on `X` from `X^a`. -/
def lqPowVals (X : E) : List Bool → ℕ → List E
  | [], _ => []
  | true :: ds, a => [X ^ (2 * a), X ^ (2 * a + 1)] ++ lqPowVals X ds (2 * a + 1)
  | false :: ds, a => [X ^ (2 * a)] ++ lqPowVals X ds (2 * a)

theorem lqPowVals_length (X : E) : ∀ (ds : List Bool) (a : ℕ),
    (lqPowVals X ds a).length = ds.length + (ds.filter id).length
  | [], _ => rfl
  | true :: ds, a => by simp [lqPowVals, lqPowVals_length X ds]; omega
  | false :: ds, a => by simp [lqPowVals, lqPowVals_length X ds]; omega

/-- **The square-and-multiply chain, honestly.** -/
theorem lq_powSteps_complete {C : CallRel} {rd : Reader} {σ : Val} (x : ℕ) :
    ∀ (ds : List Bool) (acc k a : ℕ), σ (.n acc) = σ (.n x) ^ a →
    (∀ j < (lqPowVals (σ (.n x)) ds a).length,
      σ (.n (k + j)) = (lqPowVals (σ (.n x)) ds a).getD j 0) →
    AllOk C rd σ (osPowSteps x ds acc k).1 ∧
      σ (.n (osPowSteps x ds acc k).2) = σ (.n x) ^ digitsVal ds a
  | [], _, _, _, ha, _ => ⟨allOk_nil, ha⟩
  | true :: ds, acc, k, a, ha, hv => by
    have v0 := hv 0 (by simp [lqPowVals])
    have v1 := hv 1 (by simp [lqPowVals])
    simp only [lqPowVals, List.cons_append, List.nil_append, List.getD_cons_zero,
      List.getD_cons_succ, Nat.add_zero] at v0 v1
    have := lq_powSteps_complete (C := C) (rd := rd) x ds (k + 1) (k + 2) (2 * a + 1) v1
      (fun j hj ↦ by
        have := hv (j + 2) (by simp [lqPowVals]; omega)
        simp only [lqPowVals, List.cons_append, List.nil_append, List.getD_cons_succ] at this
        rw [show k + 2 + j = k + (j + 2) by ring, this])
    simp only [osPowSteps, ↓reduceIte, allOk_cons, Whir.StmtOk, osMul, Atom.Holds]
    refine ⟨⟨by rw [v0, ha, ← pow_add]; ring_nf, by rw [v1, v0]; ring, this.1⟩, ?_⟩
    rw [this.2]; rfl
  | false :: ds, acc, k, a, ha, hv => by
    have v0 := hv 0 (by simp [lqPowVals])
    simp only [lqPowVals, List.cons_append, List.nil_append, List.getD_cons_zero,
      Nat.add_zero] at v0
    have := lq_powSteps_complete (C := C) (rd := rd) x ds k (k + 1) (2 * a) v0 (fun j hj ↦ by
      have := hv (j + 1) (by simp [lqPowVals]; omega)
      simp only [lqPowVals, List.cons_append, List.nil_append, List.getD_cons_succ] at this
      rw [show k + 1 + j = k + (j + 1) by ring, this])
    simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, allOk_cons, Whir.StmtOk, osMul, Atom.Holds]
    refine ⟨⟨by rw [v0, ha, ← pow_add]; ring_nf, this.1⟩, ?_⟩
    rw [this.2]; simp [digitsVal]

/-! ## The squeeze run -/

/-- Row `j` of the squeeze run: the capacity after `j - 1` squeezes of `cap` (row `0` unused). -/
def lpRow (cap : List E) (j : ℕ) : List E :=
  if j = 0 then [0, 0, 0, 0, 0] else ((⟨cap, []⟩ : Fs).squeezeN (j - 1)).2.cap

/-- The squeeze run's words. -/
def lpSqzW (S : ℕ) (cap : List E) : List E :=
  (List.range ((S + 1) * 5)).map fun k ↦ (lpRow cap (k / 5)).getD (k % 5) 0

theorem lpSqzW_length (S : ℕ) (cap : List E) : (lpSqzW S cap).length = (S + 1) * 5 := by
  simp [lpSqzW]

theorem lpSqzW_get {S : ℕ} {cap : List E} {j i : ℕ} (hi : i < 5)
    (h : 5 * j + i < (lpSqzW S cap).length) :
    (lpSqzW S cap)[5 * j + i] = (lpRow cap j).getD i 0 := by
  simp only [lpSqzW, List.getElem_map, List.getElem_range]
  rw [show (5 * j + i) / 5 = j by omega, show (5 * j + i) % 5 = i by omega]

theorem lp_squeezeN_succ (s : Fs) : ∀ n, (s.squeezeN (n + 1)).2 = (s.squeezeN n).2.squeeze.2 := by
  intro n
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [squeezeN_succ', ih s.squeeze.2]; rfl

theorem lp_squeezeN_cap_len (s : Fs) (h : s.cap.length = 5) : ∀ n, (s.squeezeN n).2.cap.length = 5
  | 0 => h
  | n + 1 => by rw [lp_squeezeN_succ]; rfl

theorem lpRow_length {cap : List E} (hcl : cap.length = 5) (j : ℕ) : (lpRow cap j).length = 5 := by
  unfold lpRow
  split
  · rfl
  · exact lp_squeezeN_cap_len _ hcl _

theorem lp_fs_eta {s : Fs} (h : s.pend = []) : (⟨s.cap, []⟩ : Fs) = s := by
  cases s; simp_all

/-- Row `j ≥ 1`'s squeeze is the next row and its word squeeze `j`'s. -/
theorem lpRow_squeeze {cap : List E} {j : ℕ} (hj : 1 ≤ j) :
    (⟨lpRow cap j, []⟩ : Fs).squeeze.2.cap = lpRow cap (j + 1) ∧
      ∀ w0, (⟨lpRow cap j, []⟩ : Fs).squeeze.1 = sqSample w0 cap j := by
  have he : (⟨lpRow cap j, []⟩ : Fs) = ((⟨cap, []⟩ : Fs).squeezeN (j - 1)).2 := by
    have hj0 : j ≠ 0 := by omega
    simp only [lpRow, hj0, ↓reduceIte]
    exact lp_fs_eta (squeezeN_pend rfl _)
  refine ⟨?_, fun w0 ↦ ?_⟩
  · rw [he]
    simp only [lpRow, Nat.add_one_ne_zero, ↓reduceIte]
    rw [show j + 1 - 1 = (j - 1) + 1 by omega, lp_squeezeN_succ]
  · rw [he]
    have hj0 : j ≠ 0 := by omega
    simp only [sqSample, hj0, ↓reduceIte]

/-! ## The body -/

/-- The body before its `ret`. -/
def lpPreB (d cd : ℕ) (loop : String) : List Stmt :=
  [osCst 10 (gw 1), osMul 11 9 10, osMul 12 11 11, osMul 13 12 12, osMul 14 13 11,
    .atom (.hint (.allocDyn (.n 15) (.n 14)))] ⧺
    ((List.range 5).map fun i ↦ osLd (1 + i) 15 (5 + i)) ⧺
    [.call (dqwName d cd) [.n 0, .n 6, .n 7, .n 8] []] ⧺
    osLoopCallR loop 1 9 [15, 6, 7, 8] 16 ⧺
    [osMul 19 9 9, osMul 20 19 19, osMul 21 20 9, osMul 22 15 21] ⧺
    ((List.range 5).map fun i ↦ osLd (23 + i) 22 i) ⧺
    ((List.range 5).map fun i ↦ osCp (28 + i) (23 + i))

theorem lpBody_pre (d cd : ℕ) (loop : String) :
    lpBody d cd loop = lpPreB d cd loop ⧺ [.ret ((List.range 5).map fun i ↦ .n (28 + i))] :=
  rfl

theorem lpPreB_straight (d cd : ℕ) (loop : String) :
    (lpPreB d cd loop).all Main.Stmt.straight = true := rfl

theorem lpPreB_flat (d cd : ℕ) (loop : String) : (lpPreB d cd loop).all Stmt.flat = true := rfl

theorem lpPreB_allocs (d cd : ℕ) (loop : String) :
    (lpPreB d cd loop).filterMap Main.Stmt.allocSz = [(.n 15, .inr (.n 14))] := rfl

theorem lpPreB_addrs (d cd : ℕ) (loop : String) :
    (lpPreB d cd loop).filterMap Main.Stmt.addrS = [] := rfl

theorem lpPreB_calls (d cd : ℕ) (loop : String) :
    (lpPreB d cd loop).filterMap Main.Stmt.callS =
      [(none, dqwName d cd, [.n 0, .n 6, .n 7, .n 8], []),
        (some (.n 17), loop, [.n 18, .n 9, .n 15, .n 6, .n 7, .n 8], [])] := rfl

theorem lpPreB_hints (d cd : ℕ) (loop : String) :
    (lpPreB d cd loop).filterMap hintS = [.allocDyn (.n 15) (.n 14)] := rfl

theorem lpPreB_loads (d cd : ℕ) (loop : String) :
    (lpPreB d cd loop).filterMap Stmt.loadS =
      ((List.range 5).map fun i ↦ ((.n 15 : V), 5 + i)) ++
        ((List.range 5).map fun i ↦ ((.n 22 : V), i)) := rfl

theorem lp_addr (b e t : ℕ) : (ofK (addressOfIndex b) * gen ^ e).limb 0 * addressOfIndex t =
    addressOfIndex (b + e + t) := by
  rw [gen_pow_eq_ofK, limb0_mul_ofK, limb_ofK]
  simp only [Fin.val_zero, ↓reduceIte, Parameters.addressOfIndex, ← pow_add]

theorem lp_logG_gw {e : ℕ} (he : e < 2 ^ 64 - 1) : logG (gw e) = e := by
  rw [Whir.gw_eq (by unfold u128Bound; omega), logG_gen_pow he]

/-- **`level_positions`' loop ends with its tail call**: it is a loop helper. -/
theorem lpLoop_isLoop {d cd : ℕ} {loop : String} {fn : Fn} (hf : coreProgram.find? loop = some fn)
    (hb : fn.body = lpLoopBody d cd loop) : coreProgram.loop loop = true := by
  have hn : fn.name = loop := by simpa using List.find?_some hf
  rw [Program.loop_of_find? hf, Fn.loop, hb, hn]
  simp [lpLoopBody, sqLoopBody, osLoopTail, List.reverse_append]

/-- **`level_positions` ends with its returns**: it is no loop helper. -/
theorem lp_notLoop {d cd : ℕ} {name loop : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = lpBody d cd loop) : coreProgram.loop name = false := by
  rw [Program.loop_of_find? hf, Fn.loop, hb]
  simp [lpBody, List.reverse_append]

/-! ## Placed -/

/-- **`level_positions` at one specialization, placed at `fp`, exact**: by a tree popping nothing whose every node is
exact on the memory. -/
theorem lp_placedE (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {name loop : String}
    {S d cd : ℕ} (hlp : FnIs name (osParams 10) (lpBody d cd loop))
    (hl : FnIs loop (osParams 6) (lpLoopBody d cd loop)) (hS : 0 < S) (hSo : S < ordG) (hSB : S ≤ 64)
    (hpw : digitsVal (osPowDigits (128 / d)) 1 = 128 / d)
    (hdec : QwDecodeAtDE fs cert κ d cd (dqwName d cd))
    {w0 : E} {cap : List E} {ep ew : ℕ} {tabs : E} {Lin : Layout} (hcl : cap.length = 5) (fp : ℕ)
    (hreg : ∀ k < S * (128 / d), RegionL Lin (ep + k) ∧ RegionL Lin (ew + k))
    (hregt : ∀ t < 128, ∃ i, tabs.limb 0 * addressOfIndex t = addressOfIndex i ∧ RegionL Lin i)
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      LpMem cert S d cd (lpDecPos fs name loop S d cd fp) w0 cap (ofK (addressOfIndex ep))
        (ofK (addressOfIndex ew)) tabs rd) :
    ∃ Lown : Layout,
      Within (lpRuns fs cert name loop S d cd w0 cap fp ++ Lown) fp (lpN fs name loop S d cd) ∧
      DisjL (lpRuns fs cert name loop S d cd w0 cap fp ++ Lown) ∧
      ∀ rd, LowDef κ rd → MemL rd (lpRuns fs cert name loop S d cd w0 cap fp ++ Lown ++ Lin) →
        RelAtInPE coreProgram fs cert rd (ExactAt coreProgram rd) (RegionL Lin)
          (RegionL (lpRuns fs cert name loop S d cd w0 cap fp)) fp (lpN fs name loop S d cd) name
          (w0 :: cap ++ [ofK (addressOfIndex ep), ofK (addressOfIndex ew), tabs, gen ^ S])
          ((⟨cap, []⟩ : Fs).squeezeN (S - 1)).2.cap [] := by
  obtain ⟨fnL, hfL, hpL, hbL⟩ := hl
  obtain ⟨fn, hf, hps, hb⟩ := hlp
  have hll : coreProgram.loop loop = true := lpLoop_isLoop hfL hbL
  have hnl : coreProgram.loop name = false := lp_notLoop hf hb
  set lv : OsLv := lpLvP d cd with hlv
  have hpo : lv.posOff = 0 := rfl
  have hit : SqIterC lv := by
    have := sqIterC'_holds lv hpw (by rw [hpo]; unfold u128Bound; norm_num); exact this
  have hdec' : QwDecodeAtDE fs cert κ lv.depth lv.capDepth (sqDecName lv) := hdec
  set P := 128 / d with hP
  set b := lpKidsAt fs name S fp with hbdef
  set sqzE := fp + fs name with hsqzE
  set sqz : E := ofK (addressOfIndex sqzE) with hsqz
  set W := lpSqzW S cap with hW
  set w : ℕ → E := sqSample w0 cap with hw
  set qpos : E := ofK (addressOfIndex ep) with hqpos
  set qbp : E := ofK (addressOfIndex ew) with hqbp
  set Lk : Layout := (sqzE, W) :: Lin with hLk
  have hO : ordG = 2 ^ 64 - 1 := rfl
  have hU : u128Bound = 2 ^ 128 := rfl
  have hsq5 : S * 5 < u128Bound := by omega
  have hsq64 : (S + 1) * 5 < 2 ^ 64 - 1 := by omega
  have hsp : sqPer lv = P := rfl
  have hdn : sqDecName (lpLv d cd) = dqwName d cd := rfl
  have hdp : (default : OsLv).posOff = 0 := rfl
  have hlvP : lpLvP d cd = lpLv d cd := rfl
  have hrowM : ∀ rd, MemL rd Lk → ∀ j ≤ S, ∀ i < 5,
      LoadHolds rd (sqz * (gen ^ j) ^ 5) i ((lpRow cap j).getD i 0) := by
    intro rd hm j hj i hi
    have h := hm _ List.mem_cons_self (5 * j + i) (by rw [lpSqzW_length]; omega)
    rw [lpSqzW_get hi] at h
    rw [← pow_mul, loadHolds_mul_gen_pow, show j * 5 + i = 5 * j + i by ring]
    exact h
  -- the group
  have hgroup := os_sq_groupE fs cert κ hfL hpL hbL hll hit hdec' (n := S) (by omega) hSo
    (w := w) (cap := lpRow cap) (fun j ↦ lpRow_length hcl j)
    (fun j hj ↦ (lpRow_squeeze hj).2 w0) (sqz := sqz) (tabs := tabs) (eqp := ep) (eq := ew)
    (Lk := Lk)
    (fun rd hl hm ↦ by
      have hM := hmem rd hl (fun q hq ↦ hm q (List.mem_cons_of_mem _ hq))
      refine ⟨hM.1, fun j hj1 hj ↦ ⟨fun i hi ↦ hrowM rd hm j (by omega) i hi, fun i hi ↦ ?_⟩,
        fun j hj i hi ↦ ?_⟩
      · rw [(lpRow_squeeze hj1).1]
        have := hrowM rd hm (j + 1) (by omega) i hi
        rw [← pow_mul, loadHolds_mul_gen_pow] at this ⊢
        rw [show j * 5 + (5 + i) = (j + 1) * 5 + i by ring]
        exact this
      · have := (hM.2 j hj i hi).1
        rw [hpo, pow_zero, mul_one, ← pow_mul, loadHolds_mul_gen_pow]
        exact this)
    (fun j hj1 hj t ht ↦ ⟨sqzE + j * 5 + t, by rw [← pow_mul, lp_addr],
      ⟨(sqzE, W), List.mem_cons_self, by omega, by rw [hW, lpSqzW_length]; omega⟩⟩)
    (fun j hj t ht ↦ by
      have ht' : t < P := ht
      have hk : j * P + t < S * P := by
        have := Nat.mul_le_mul_right P (show j + 1 ≤ S by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; omega
      obtain ⟨q, hq, h1, h2⟩ := (hreg _ hk).1
      exact ⟨q, List.mem_cons_of_mem _ hq, by rw [hpo, hsp]; omega, by rw [hpo, hsp]; omega⟩)
    (fun t ht ↦ by
      obtain ⟨i, hi, q, hq, h1, h2⟩ := hregt t ht
      exact ⟨i, hi, q, List.mem_cons_of_mem _ hq, h1, h2⟩)
  -- the honest values
  obtain ⟨a0, a1, a2, a3, a4, rfl⟩ : ∃ a0 a1 a2 a3 a4, cap = [a0, a1, a2, a3, a4] := by
    match cap, hcl with
    | [a0, a1, a2, a3, a4], _ => exact ⟨a0, a1, a2, a3, a4, rfl⟩
  set cap := [a0, a1, a2, a3, a4] with hcap
  set last := ((⟨cap, []⟩ : Fs).squeezeN (S - 1)).2.cap with hlast
  have hll5 : last.length = 5 := lp_squeezeN_cap_len _ hcl _
  obtain ⟨l0, l1, l2, l3, l4, hl5⟩ : ∃ l0 l1 l2 l3 l4, last = [l0, l1, l2, l3, l4] := by
    match last, hll5 with
    | [l0, l1, l2, l3, l4], _ => exact ⟨l0, l1, l2, l3, l4, rfl⟩
  have hrow1 : lpRow cap 1 = cap := rfl
  have hrowS : lpRow cap S = last := by
    have hS0 : S ≠ 0 := by omega
    simp only [lpRow, hS0, ↓reduceIte, hlast]
  set vals : List E := [w0, a0, a1, a2, a3, a4, qpos, qbp, tabs, gen ^ S] ++
    [gw 1, gen ^ S * gw 1, gen ^ S * gw 1 * (gen ^ S * gw 1),
      gen ^ S * gw 1 * (gen ^ S * gw 1) * (gen ^ S * gw 1 * (gen ^ S * gw 1)),
      gen ^ S * gw 1 * (gen ^ S * gw 1) * (gen ^ S * gw 1 * (gen ^ S * gw 1)) * (gen ^ S * gw 1),
      sqz, gw 1, gw 1 + gen ^ S, gw 1,
      gen ^ S * gen ^ S, gen ^ S * gen ^ S * (gen ^ S * gen ^ S),
      gen ^ S * gen ^ S * (gen ^ S * gen ^ S) * gen ^ S,
      sqz * (gen ^ S * gen ^ S * (gen ^ S * gen ^ S) * gen ^ S)] ++
    last ++ last with hvals
  set σ : Val := fun v ↦ if v.path = [] ∧ v.tag = 0 then vals.getD v.idx 0 else 0 with hσ
  have hv : ∀ i, σ (.n i) = vals.getD i 0 := fun i ↦ by simp [hσ]
  have hg1 : gw 1 = gen := by rw [Whir.gw_eq (by unfold u128Bound; norm_num), pow_one]
  have hG5 : gen ^ S * gen ^ S * (gen ^ S * gen ^ S) * gen ^ S = gen ^ (S * 5) := by ring
  -- the walk
  have hst := lpPreB_straight d cd loop
  have hwalk : walk σ fn.body = .ret ((lpPreB d cd loop).flatMap (Main.slEvs σ))
      ((List.range 5).map fun i ↦ .n (28 + i)) := by
    rw [hb, lpBody_pre]; exact Main.walk_straight σ _ _ hst
  set es := (lpPreB d cd loop).flatMap (Main.slEvs σ) with hes_def
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ _ hst
  have h14 : σ (.n 14) = gen ^ ((S + 1) * 5) := by
    simp [hv, hvals, hg1]; ring
  have h15 : σ (.n 15) = sqz := by simp [hv, hvals]
  have h17 : σ (.n 17) = gen + gen ^ S := by simp [hv, hvals, hg1]
  have h22 : σ (.n 22) = sqz * gen ^ (S * 5) := by simp [hv, hvals, hG5]
  have hal : allocs σ es = [(S + 1) * 5] := by
    rw [i2, lpPreB_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, h14, logG_gen_pow hsq64]
  have hcalls : calls es = [⟨dqwName d cd, [.n 0, .n 6, .n 7, .n 8], [], true⟩,
      ⟨loop, [.n 18, .n 9, .n 15, .n 6, .n 7, .n 8], [], decide (gen + gen ^ S ≠ 0)⟩] := by
    rw [i4, lpPreB_calls]
    simp [Main.mkCall, h17]
  have hown : ∀ k < (S + 1) * 5, ownData cert fp (fp + fs name) name (allocs σ es) es
      (sqzE + k) := fun k hk => by
    rw [hal]
    exact Or.inl ⟨((S + 1) * 5, fp + fs name), by simp [bases], by omega, by simp only; omega⟩
  -- the group's calls
  obtain ⟨LownG, hWG, hDG, hKG⟩ := hgroup σ ⟨dqwName d cd, [.n 0, .n 6, .n 7, .n 8], [], true⟩
    ⟨loop, [.n 18, .n 9, .n 15, .n 6, .n 7, .n 8], [], decide (gen + gen ^ S ≠ 0)⟩ rfl rfl
    (by simp [hv, hvals, hqpos, hqbp, lpLv, hw, sqSample, hdp]) rfl rfl rfl
    (by simp [hv, hvals, hg1, hqpos, hqbp]) rfl b
  set runs := sqGroupRuns fs cert lv loop S b w with hruns
  have hrunsE : lpRuns fs cert name loop S d cd w0 cap fp = runs := rfl
  rw [hrunsE]
  refine ⟨(sqzE, W) :: LownG, ?_, ?_, fun rd hlow hL => ?_⟩
  · intro q hq
    simp only [List.mem_append, List.mem_cons] at hq
    rcases hq with hq | rfl | hq
    · have := hWG q (List.mem_append_left _ hq)
      unfold lpN; simp only [hbdef, lpKidsAt, hdn, hlvP] at this ⊢; omega
    · simp only [hW, lpSqzW_length, lpN]; omega
    · have := hWG q (List.mem_append_right _ hq)
      unfold lpN; simp only [hbdef, lpKidsAt, hdn, hlvP] at this ⊢; omega
  · have hc : DisjL ((sqzE, W) :: (runs ++ LownG)) := by
      unfold DisjL
      refine List.pairwise_cons.mpr ⟨fun q hq => Or.inl ?_, hDG⟩
      have := hWG q hq
      simp only [hW, lpSqzW_length, hbdef, lpKidsAt] at this ⊢; omega
    exact List.Pairwise.perm hc List.perm_middle.symm fun h => Or.symm h
  have hLin : MemL rd Lin := fun q hq => hL q (List.mem_append_right _ hq)
  have hE : ReadsAt rd sqz W :=
    hL _ (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
  have hLk : MemL rd Lk := fun q hq => by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hE
    · exact hLin q hq
  have hM := hmem rd hlow hLin
  have hrowM' := hrowM rd hLk
  have h1row : ∀ i < 5, LoadHolds rd sqz (5 + i) (cap.getD i 0) := fun i hi ↦ by
    have := hrowM' 1 (by omega) i hi
    rw [pow_one, loadHolds_mul_gen_pow] at this
    exact this
  have hSrow : ∀ i < 5, LoadHolds rd (sqz * gen ^ (S * 5)) i (last.getD i 0) := fun i hi ↦ by
    have := hrowM' S le_rfl i hi
    rw [hrowS, ← pow_mul] at this
    exact this
  have hholds : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ fn.body False (fun r ↦ r = last) := by
    rw [hb, lpBody_pre, holdsList_flat_ret _ (lpPreB_flat d cd loop)]
    refine ⟨?_, ?_⟩
    · simp only [lpPreB, osLoopCallR, allOk_cons, allOk_nil, and_true, StmtOk,
        Atom.Holds, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, implies_true, osLd, osCst, osMul, osCp, osAdd, hv]
      simp [hvals, hl5, hG5, hg1]
      rw [hl5] at hSrow
      exact ⟨h1row 0 (by omega), h1row 1 (by omega), h1row 2 (by omega), h1row 3 (by omega),
        h1row 4 (by omega), isInK_add (by rw [← pow_one gen]; exact gen_pow_isInK 1) (gen_pow_isInK S),
        hSrow 0 (by omega), hSrow 1 (by omega), hSrow 2 (by omega), hSrow 3 (by omega),
        hSrow 4 (by omega)⟩
    · simp [hv, hvals, hl5, List.range_succ]
  have hes : ∀ e ∈ es, e.Holds rd σ := by
    have := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf))
      hholds
    rw [hwalk] at this
    exact fun e he => (this.1 e he).1
  -- the window pointers
  have hWp : MemL rd (sqW fs cert lv loop S ew b) := by
    intro q hq
    simp only [sqW, List.mem_singleton] at hq
    subst hq
    intro k hk
    simp only [sqWinPtrs, List.length_map, List.length_range] at hk
    have hP0 : 0 < P := by
      rcases Nat.eq_zero_or_pos P with h | h
      · rw [hsp, h, Nat.mul_zero] at hk; omega
      · exact h
    have hj : k / P < S := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; rw [hsp] at hk; exact hk)
    have hi : k % P < P := Nat.mod_lt _ hP0
    have := (hM.2 (k / P) hj (k % P) hi).2
    rw [Nat.div_add_mod'] at this
    simp only [sqWinPtrs, List.getElem_map, List.getElem_range, hpo, Nat.add_zero]
    exact this
  -- the group's kids
  have hK := hKG rd (fun i ↦ RegionL Lin i ∨ ownData cert fp (fp + fs name) name (allocs σ es) es i)
    (fun _ ↦ False) hlow
    (fun q hq ↦ hL q (by
      rcases List.mem_append.mp hq with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ h))))
    (Main.memL_append.mpr ⟨hLk, hWp⟩)
    (fun i hi ↦ Or.inl (by
      obtain ⟨q, hq, h1, h2⟩ := hi
      have hq' : q ∈ ((sqzE, W) :: Lin) ++ sqW fs cert lv loop S ew b := hq
      rcases List.mem_append.mp hq' with hq | hq
      · rcases List.mem_cons.mp hq with rfl | hq
        · right
          have := hown (i - sqzE) (by simp only [hW, lpSqzW_length] at h2; omega)
          rwa [show sqzE + (i - sqzE) = i by omega] at this
        · exact Or.inl ⟨q, hq, h1, h2⟩
      · simp only [sqW, List.mem_singleton] at hq
        subst hq
        simp only [sqWinPtrs, List.length_map, List.length_range, hpo, Nat.add_zero] at h1 h2
        left
        have := (hreg (i - ew) (by rw [hsp] at h2; omega)).2
        rwa [show ew + (i - ew) = i by omega] at this))
  have hnw := walk_noWit (σ := σ) fn.body (by rw [hb]; rfl)
  rw [hwalk] at hnw
  have hrel := relAtInPE_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (Q := ExactAt coreProgram rd) (pss := [[], []]) (ps := [])
    (R := RegionL Lin) (D := RegionL runs) (Dk := RegionL runs)
    (N := fs (sqDecName lv) + sqTot fs lv loop (S - 1) 0) (fp := fp)
    (args := w0 :: cap ++ [qpos, qbp, tabs, gen ^ S]) (rets := last)
    coreProgram_wf hf (Or.inl hnl)
    (by rw [hps]; simp [osParams, List.range_succ, hv, hvals, hcap]) hwalk
    (by simp [hv, hvals, hl5, List.range_succ]) hes
    (by rw [hal, i1, lpPreB_allocs]; simp [bases, h15, hsqz, hsqzE])
    (fun q hq => by rw [i3, lpPreB_addrs] at hq; simp at hq)
    (by
      have hb' : fp + fs name + (allocs σ es).sum = b := by
        rw [hal]; simp [hbdef, lpKidsAt]
      rw [hcalls, hb']
      exact hK)
    (fun A hA => by
      rw [loadAddrs_straight σ _ hst, lpPreB_loads] at hA
      simp only [List.map_append, List.map_map, List.mem_append, List.mem_map, List.mem_range,
        Function.comp] at hA
      rcases hA with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · refine ⟨sqzE + (5 + i), ?_, Or.inl (hown _ (by omega))⟩
        rw [h15, hsqz, Main.addr_ofK]
      · refine ⟨sqzE + S * 5 + i, ?_, Or.inl ?_⟩
        · rw [h22, hsqz, lp_addr]
        · rw [Nat.add_assoc]; exact hown _ (by omega))
    (fun i hi => Or.inr hi) (splice_nil_of _ _ hnw (by simp))
    (exactAt_of_walk hf hwalk fun e he => evs_exact_of_hints (σ := σ) (pre := lpPreB d cd loop)
      (fun x hx => by rw [lpPreB_hints] at hx; simp only [List.mem_singleton] at hx; subst hx; rfl) e he rd)
  rw [hal] at hrel
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hrel
  exact hrel

/-- **`level_positions` at one specialization, placed at `fp`** (`lp_placedE`). -/
theorem lp_placed (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {name loop : String}
    {S d cd : ℕ} (hlp : FnIs name (osParams 10) (lpBody d cd loop))
    (hl : FnIs loop (osParams 6) (lpLoopBody d cd loop)) (hS : 0 < S) (hSo : S < ordG) (hSB : S ≤ 64)
    (hpw : digitsVal (osPowDigits (128 / d)) 1 = 128 / d)
    (hdec : QwDecodeAtDE fs cert κ d cd (dqwName d cd))
    {w0 : E} {cap : List E} {ep ew : ℕ} {tabs : E} {Lin : Layout} (hcl : cap.length = 5) (fp : ℕ)
    (hreg : ∀ k < S * (128 / d), RegionL Lin (ep + k) ∧ RegionL Lin (ew + k))
    (hregt : ∀ t < 128, ∃ i, tabs.limb 0 * addressOfIndex t = addressOfIndex i ∧ RegionL Lin i)
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      LpMem cert S d cd (lpDecPos fs name loop S d cd fp) w0 cap (ofK (addressOfIndex ep))
        (ofK (addressOfIndex ew)) tabs rd) :
    ∃ Lown : Layout,
      Within (lpRuns fs cert name loop S d cd w0 cap fp ++ Lown) fp (lpN fs name loop S d cd) ∧
      DisjL (lpRuns fs cert name loop S d cd w0 cap fp ++ Lown) ∧
      ∀ rd, LowDef κ rd → MemL rd (lpRuns fs cert name loop S d cd w0 cap fp ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin)
          (RegionL (lpRuns fs cert name loop S d cd w0 cap fp)) fp (lpN fs name loop S d cd) name
          (w0 :: cap ++ [ofK (addressOfIndex ep), ofK (addressOfIndex ew), tabs, gen ^ S])
          ((⟨cap, []⟩ : Fs).squeezeN (S - 1)).2.cap := by
  obtain ⟨Lown, hW, hD, hR⟩ := lp_placedE fs cert κ hlp hl hS hSo hSB hpw hdec hcl fp hreg hregt hmem
  exact ⟨Lown, hW, hD, fun rd hl hm => RelAtInT.relAtIn (hR rd hl hm)⟩

/-! ## Every specialization -/

set_option maxRecDepth 100000 in
/-- The constants of `lpTable`'s entries the proof uses. -/
theorem lpTable_facts : ∀ e ∈ lpTable,
    digitsVal (osPowDigits (128 / e.2.2.1)) 1 = 128 / e.2.2.1 ∧
    (dqwName e.2.2.1 e.2.2.2, e.2.2.1, e.2.2.2) ∈ queryWindowsShapes := by
  decide +kernel

end
end LeanVM.Guest.B1
