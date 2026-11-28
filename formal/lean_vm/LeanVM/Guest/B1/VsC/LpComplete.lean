/-
  LeanVM.Guest.B1.VsC.LpComplete

  `level_positions` completes placed (`LpA`), every specialization.
-/

module

public import LeanVM.Guest.B1.VsC.LpTable
public import LeanVM.Guest.B1.VsC.QwCertB2C

/-!
# `level_positions`, placed

`level_positions__L{d}_L{cd}` at `S` squeezes on `[w0, fsv, positions, win_ptrs, tabs, g^S]`
allocates its squeeze run `sqz` (`5(S + 1)` words at its cursor `c`, its own words `lpSqz`: row
`k` the capacity after `k - 1` squeezes), decodes `w0` (`QwA`), runs its loop when `S ≠ 1`
(`lpL_complete`), and returns row `S`.

* `lpPreX`, `lpBody_eqX`: its body, written out.
* `lpA_complete'`: one specialization, by `callAtA_node` on the explicit valuation.
* `lpA_complete`: every `lpTable` entry, given its decode's `QwA`; `lpA_b2c` at the compiled frames.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## Blocks of a run -/

theorem blk_div {k P i : ℕ} (hi : i < P) : (k * P + i) / P = k := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < P), Nat.div_eq_of_lt hi, Nat.zero_add]

theorem blk_mod {k P i : ℕ} (hi : i < P) : (k * P + i) % P = i := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

/-- Block `k` of a run of `S` blocks of `P` words, word `m` of the run `g (m / P) (m % P)`. -/
theorem readsAt_blk {rd : Reader} {a P S k : ℕ} {g : ℕ → ℕ → E} (hk : k < S)
    (h : ReadsAt rd (ptrAt a) ((List.range (S * P)).map fun m => g (m / P) (m % P))) :
    ReadsAt rd (ptrAt (a + k * P)) ((List.range P).map fun i => g k i) := by
  intro m hm
  simp only [List.length_map, List.length_range] at hm
  have hlt : k * P + m < ((List.range (S * P)).map fun m => g (m / P) (m % P)).length := by
    simp only [List.length_map, List.length_range]; nlinarith
  have := h (k * P + m) hlt
  simp only [List.getElem_map, List.getElem_range, blk_div hm, blk_mod hm] at this ⊢
  rw [loadHolds_ptrAt_add]; exact this

/-! ## `level_positions`' body -/

/-- `level_positions`' body before its return, written out. -/
def lpPreX (d cd : ℕ) (loop : String) : List Stmt :=
  [osCst 10 (gw 1), osMul 11 9 10, osMul 12 11 11, osMul 13 12 12, osMul 14 13 11,
    .atom (.hint (.allocDyn (.n 15) (.n 14))),
    osLd 1 15 5, osLd 2 15 6, osLd 3 15 7, osLd 4 15 8, osLd 5 15 9,
    .call (dqwName d cd) [.n 0, .n 6, .n 7, .n 8] [],
    osCst 16 (gw 1), osAdd 17 16 9, osCst 18 (gw 1),
    .callIf (.n 17) loop [.n 18, .n 9, .n 15, .n 6, .n 7, .n 8],
    osMul 19 9 9, osMul 20 19 19, osMul 21 20 9, osMul 22 15 21,
    osLd 23 22 0, osLd 24 22 1, osLd 25 22 2, osLd 26 22 3, osLd 27 22 4,
    osCp 28 23, osCp 29 24, osCp 30 25, osCp 31 26, osCp 32 27]

theorem lpBody_eqX (d cd : ℕ) (loop : String) :
    lpBody d cd loop = lpPreX d cd loop ++ [.ret [.n 28, .n 29, .n 30, .n 31, .n 32]] := by
  rw [lpBody_split]; rfl

theorem lpPreX_straight (d cd : ℕ) (loop : String) : (lpPreX d cd loop).all Stmt.straight = true := rfl

theorem lpPreX_quiet (d cd : ℕ) (loop : String) :
    (lpPreX d cd loop).all (fun s => match s with | .atom a => atomQuiet a | _ => true) = true := rfl

theorem lpPreX_triv (d cd : ℕ) (loop : String) :
    (lpPreX d cd loop).all (fun s => match s with | .atom a => trivExact a | _ => true) = true := rfl

/-! ## `level_positions`, placed -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

variable (fs al cert) in
/-- What `level_positions` reads: `LpA`'s. -/
def LpPosPre (d cd S ipos iptr it : ℕ) (loop : String) (w0 : E) (fsv : List E) (c : ℕ) (rd : Reader) : Prop :=
  WinTabs rd (ptrAt it) ∧
    ReadsAt rd (ptrAt ipos) ((List.range (S * (128 / d))).map fun k =>
      eOfNat (qwPosOf d (sqSample w0 fsv (k / (128 / d))) (k % (128 / d)))) ∧
    ReadsAt rd (ptrAt iptr) ((List.range (S * (128 / d))).map fun k =>
      ptrAt (lpDqFrame fs al (dqwName d cd) loop S c (k / (128 / d)) + cert (dqwName d cd) (.n 5) +
        k % (128 / d) * qwN d cd))

variable (fs al cert) in
/-- What `level_positions`' windows hold: `LpA`'s. -/
def LpPosOut (d cd S : ℕ) (loop : String) (w0 : E) (fsv : List E) (c : ℕ) (rd : Reader) : Prop :=
  ∀ j < S, ReadsAt rd (ptrAt (lpDqFrame fs al (dqwName d cd) loop S c j + cert (dqwName d cd) (.n 5)))
    (qwRunList d cd (sqSample w0 fsv j))

variable (fs al cert) in
/-- The windows `level_positions` claims: `LpA`'s. -/
def LpPosD (d cd S : ℕ) (loop : String) (c i : ℕ) : Prop :=
  ∃ j < S, lpDqFrame fs al (dqwName d cd) loop S c j + cert (dqwName d cd) (.n 5) ≤ i ∧
    i < lpDqFrame fs al (dqwName d cd) loop S c j + cert (dqwName d cd) (.n 5) + 128 / d * qwN d cd

theorem lpDqFrame_zero (dq loop : String) (S c : ℕ) :
    lpDqFrame fs al dq loop S c 0 = allocBase (al dq) (c + 5 * (S + 1)) := by simp [lpDqFrame]

theorem lpDqFrame_lpF (dq loop : String) {S c k cL : ℕ}
    (hcL : cL = allocBase (al loop) (lpDqStep fs al dq (c + 5 * (S + 1))) + lpB fs loop S 1) (hk : k ≠ 0) :
    lpDqFrame fs al dq loop S c k = lpF fs al dq cL 1 k := by
  simp [lpDqFrame, lpF, hk, hcL]

theorem gw_one : gw 1 = gen ^ 1 := gw_gen 1 (by norm_num)

/-- `level_positions`' end, from its pieces. -/
theorem lp_end_le {c S A B T x e : ℕ} (hS : 1 ≤ S)
    (hx : x ≤ c + 5 * (S + 1) + 15 + A + 15 + (S - 1) * B + T) (he : e ≤ x + (S - 1) * (15 + A)) :
    e ≤ c + (S + 1) * (A + B + T + 64) := by
  have h1 : (S + 1) * B = (S - 1) * B + 2 * B := by rw [← Nat.add_mul]; congr 1; omega
  have h2 : (S + 1) * A = (S - 1) * A + 2 * A := by rw [← Nat.add_mul]; congr 1; omega
  have h3 : (S - 1) * (15 + A) = (S - 1) * 15 + (S - 1) * A := Nat.mul_add _ _ _
  have h5 : T ≤ (S + 1) * T := Nat.le_mul_of_pos_left T (by omega)
  have hX : (S + 1) * (A + B + T + 64) = (S + 1) * A + (S + 1) * B + (S + 1) * T + (S + 1) * 64 := by ring
  omega

/-- **`level_positions` completes placed, its end bounded.** -/
theorem lpAE_complete' {kd : ℕ} {name loop : String} {d cd : ℕ} {fo fl : Fn}
    (hfo : coreProgram.find? name = some fo) (hpo : fo.params = osParams 10) (hbo : fo.body = lpBody d cd loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = osParams 6) (hbl : fl.body = lpLoopBody d cd loop)
    (hlc : lpLChecks d cd loop = true) (hqw : QwA fs al cert kd (dqwName d cd) d cd) :
    LpAE fs al cert kd name loop (dqwName d cd) d cd := by
  intro S w0 fsv ipos iptr it R hS1 hS hfsv hkd hRp hRq hRt fp c hfc
  show ∃ e, e ≤ c + (S + 1) * (fs (dqwName d cd) + fs loop + fs (tailKey loop) + 64) ∧ CallAtA fs al cert kd name _ _ R (LpPosD fs al cert d cd S loop c) (LpPosOut fs al cert d cd S loop w0 fsv c)
    (LpPosPre fs al cert d cd S ipos iptr it loop w0 fsv c) PostQuiet (fs name) fp c e
  obtain ⟨f0, f1, f2, f3, f4, rfl⟩ : ∃ f0 f1 f2 f3 f4, fsv = [f0, f1, f2, f3, f4] := by
    match fsv, hfsv with
    | [a, b, c', e', f], _ => exact ⟨a, b, c', e', f, rfl⟩
  set fsv := [f0, f1, f2, f3, f4] with hfsvd
  obtain ⟨r0, r1, r2, r3, r4, hrS⟩ : ∃ r0 r1 r2 r3 r4, lpRow fsv S = [r0, r1, r2, r3, r4] := by
    have hl := lpRow_length (fsv := fsv) rfl S
    match lpRow fsv S, hl with
    | [a, b, c', e', f], _ => exact ⟨a, b, c', e', f, rfl⟩
  have h128 : 128 ≤ 2 ^ winTabBits := by decide
  have hlo : coreProgram.loop name = false := by
    rw [Program.loop_of_find? hfo, Fn.loop, hbo, lpBody_eqX]; rfl
  let σ : Val := fun v => [w0, f0, f1, f2, f3, f4, ptrAt ipos, ptrAt iptr, ptrAt it, gen ^ S, gen ^ 1,
    gen ^ (S + 1), gen ^ (2 * (S + 1)), gen ^ (4 * (S + 1)), gen ^ (5 * (S + 1)), ptrAt c, gen ^ 1,
    gen ^ 1 + gen ^ S, gen ^ 1, gen ^ (2 * S), gen ^ (4 * S), gen ^ (5 * S), ptrAt (c + 5 * S),
    r0, r1, r2, r3, r4, r0, r1, r2, r3, r4].getD v.idx 0
  have hstr := lpPreX_straight d cd loop
  set es := (lpPreX d cd loop).flatMap (slEvs σ) with hes
  have hw : walk σ fo.body = .ret es [.n 28, .n 29, .n 30, .n 31, .n 32] := by
    rw [hbo, lpBody_eqX]; exact walk_straight σ _ _ hstr
  have hal : allocs σ es = [5 * (S + 1)] := by
    rw [hes, (straight_parts σ _ hstr).2.1]
    show [logG (gen ^ (5 * (S + 1)))] = _
    rw [gen_pow_eq_ofK, logG_spec (by omega)]
  have hsum : (allocs σ es).sum = 5 * (S + 1) := by rw [hal]; simp
  have hcalls : calls es = [⟨dqwName d cd, [.n 0, .n 6, .n 7, .n 8], [], true⟩,
      ⟨loop, [.n 18, .n 9, .n 15, .n 6, .n 7, .n 8], [], decide (σ (.n 17) ≠ 0)⟩] := by
    rw [hes, (straight_parts σ _ hstr).2.2.2]; rfl
  -- the squeeze run
  let Wo : Words := [(c, lpSqz fsv S)]
  have hWo : ∀ rd, HoldsWords rd Wo → ReadsAt rd (ptrAt c) (lpSqz fsv S) := fun rd h => h _ List.mem_cons_self
  have hown : ∀ i, c ≤ i → i < c + 5 * (S + 1) → ownData cert fp c name (allocs σ es) es i := by
    intro i h1 h2
    rw [hal]
    exact ownData_buf (s := 5 * (S + 1)) (b := c) (by simp [bases]) h1 h2
  let Rc : ℕ → Prop := fun i => R i ∨ (c ≤ i ∧ i < c + 5 * (S + 1))
  have hRc : ∀ i, Rc i → R i ∨ ownData cert fp c name (allocs σ es) es i := by
    rintro i (hi | ⟨h1, h2⟩)
    · exact Or.inl hi
    · exact Or.inr (hown i h1 h2)
  have hblkP : ∀ k < S, ∀ rd, LpPosPre fs al cert d cd S ipos iptr it loop w0 fsv c rd →
      ReadsAt rd (ptrAt (ipos + k * (128 / d)))
        ((List.range (128 / d)).map fun i => eOfNat (qwPosOf d (sqSample w0 fsv k) i)) ∧
      ReadsAt rd (ptrAt (iptr + k * (128 / d)))
        ((List.range (128 / d)).map fun i =>
          ptrAt (lpDqFrame fs al (dqwName d cd) loop S c k + cert (dqwName d cd) (.n 5) + i * qwN d cd)) :=
    fun k hk rd h =>
      ⟨readsAt_blk (g := fun a b => eOfNat (qwPosOf d (sqSample w0 fsv a) b)) hk h.2.1,
        readsAt_blk (g := fun a b => ptrAt (lpDqFrame fs al (dqwName d cd) loop S c a + cert (dqwName d cd) (.n 5) +
          b * qwN d cd)) hk h.2.2⟩
  -- the first decode
  set F0 := allocBase (al (dqwName d cd)) (c + 5 * (S + 1)) with hF0
  have hdq : CallAtA fs al cert kd (dqwName d cd) [w0, ptrAt ipos, ptrAt iptr, ptrAt it] [] Rc
      (fun i => F0 + cert (dqwName d cd) (.n 5) ≤ i ∧ i < F0 + cert (dqwName d cd) (.n 5) + 128 / d * qwN d cd)
      (fun rd => ReadsAt rd (ptrAt (F0 + cert (dqwName d cd) (.n 5))) (qwRunList d cd w0))
      (fun rd => LpPosPre fs al cert d cd S ipos iptr it loop w0 fsv c rd ∧ HoldsWords rd Wo)
      PostQuiet (fs (dqwName d cd)) F0 (F0 + fs (dqwName d cd)) (lpDqStep fs al (dqwName d cd) (c + 5 * (S + 1))) := by
    refine (hqw w0 ipos iptr it Rc hkd (fun j hj => Or.inl (hRp j (by nlinarith)))
      (fun j hj => Or.inl (hRq j (by nlinarith))) (fun n hn => Or.inl (hRt n (by omega))) F0
      (F0 + fs (dqwName d cd))).mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd h => ?_) (fun _ _ _ h => h)
    obtain ⟨hps, hpt⟩ := hblkP 0 (by omega) rd h.1
    simp only [Nat.zero_mul, Nat.add_zero, lpDqFrame_zero] at hps hpt
    exact ⟨h.1.1, by simpa [sqSample] using hps, hpt⟩
  -- the events
  have hev : ∀ rd, LpPosPre fs al cert d cd S ipos iptr it loop w0 fsv c rd → HoldsWords rd Wo → ∀ ev ∈ es, ev.Holds rd σ := by
    intro rd _ hW
    have hsq := hWo rd hW
    have hrow1 : ∀ i < 5, LoadHolds rd (ptrAt c) (5 + i) (fsv.getD i 0) := fun i hi => by
      have := lpSqz_load (k := 1) hsq (by omega) hi
      rwa [loadHolds_ptrAt_add, show 5 * 1 + i = 5 + i by ring] at this
    have hrowS : ∀ i < 5, LoadHolds rd (ptrAt (c + 5 * S)) i ([r0, r1, r2, r3, r4].getD i 0) := fun i hi => by
      have := lpSqz_load (k := S) hsq le_rfl hi
      rwa [hrS] at this
    refine holds_slEvs _ (fun a ha => ?_) (fun c' f args h => ?_)
    · simp only [lpPreX, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq, reduceCtorEq,
        false_or] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show gen ^ 1 = gw 1; exact gw_one.symm
      · show gen ^ (S + 1) = gen ^ S * gen ^ 1; exact pow_add _ _ _
      · show gen ^ (2 * (S + 1)) = gen ^ (S + 1) * gen ^ (S + 1); rw [two_mul, pow_add]
      · show gen ^ (4 * (S + 1)) = gen ^ (2 * (S + 1)) * gen ^ (2 * (S + 1))
        rw [← pow_add, show 2 * (S + 1) + 2 * (S + 1) = 4 * (S + 1) by ring]
      · show gen ^ (5 * (S + 1)) = gen ^ (4 * (S + 1)) * gen ^ (S + 1)
        rw [← pow_add, show 4 * (S + 1) + (S + 1) = 5 * (S + 1) by ring]
      · trivial
      · exact hrow1 0 (by decide)
      · exact hrow1 1 (by decide)
      · exact hrow1 2 (by decide)
      · exact hrow1 3 (by decide)
      · exact hrow1 4 (by decide)
      · show gen ^ 1 = gw 1; exact gw_one.symm
      · rfl
      · show gen ^ 1 = gw 1; exact gw_one.symm
      · show gen ^ (2 * S) = gen ^ S * gen ^ S; rw [two_mul, pow_add]
      · show gen ^ (4 * S) = gen ^ (2 * S) * gen ^ (2 * S)
        rw [← pow_add, show 2 * S + 2 * S = 4 * S by ring]
      · show gen ^ (5 * S) = gen ^ (4 * S) * gen ^ S
        rw [← pow_add, show 4 * S + S = 5 * S by ring]
      · show ptrAt (c + 5 * S) = ptrAt c * gen ^ (5 * S); exact (ptrAt_mul_gen c (5 * S)).symm
      · exact hrowS 0 (by decide)
      · exact hrowS 1 (by decide)
      · exact hrowS 2 (by decide)
      · exact hrowS 3 (by decide)
      · exact hrowS 4 (by decide)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · simp only [lpPreX, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
        Stmt.callIf.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      exact isInK_add (gen_pow_isInK 1) (gen_pow_isInK S)
  -- the loads
  have hlA : loadAddrs σ es = [(σ (.n 15)).limb 0 * addressOfIndex 5, (σ (.n 15)).limb 0 * addressOfIndex 6,
      (σ (.n 15)).limb 0 * addressOfIndex 7, (σ (.n 15)).limb 0 * addressOfIndex 8,
      (σ (.n 15)).limb 0 * addressOfIndex 9, (σ (.n 22)).limb 0 * addressOfIndex 0,
      (σ (.n 22)).limb 0 * addressOfIndex 1, (σ (.n 22)).limb 0 * addressOfIndex 2,
      (σ (.n 22)).limb 0 * addressOfIndex 3, (σ (.n 22)).limb 0 * addressOfIndex 4] := by
    rw [loadAddrs, hes, filterMap_slEvs (Ev.loadAddr? σ) σ (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)]
    rfl
  have hhA : heapHintAddrs σ es = [] := by
    rw [heapHintAddrs, hes, flatMap_slEvs (Ev.hintAddrs σ) σ (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)]
    rfl
  have hloads : ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp c name (allocs σ es) es i ∨ R i ∨ LpPosD fs al cert d cd S loop c i) := by
    intro A hA
    rw [hlA] at hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    have s15 : σ (.n 15) = ptrAt c := rfl
    have s22 : σ (.n 22) = ptrAt (c + 5 * S) := rfl
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [s15, s22, ptrAt, Main.addr_ofK] <;>
      exact ⟨_, rfl, Or.inl (hown _ (by omega) (by omega))⟩
  -- the callees
  set ec := lpDqStep fs al (dqwName d cd) (c + 5 * (S + 1)) with hec
  set fL := allocBase (al loop) ec with hfL
  set cL := fL + lpB fs loop S 1 with hcL
  have hd17 : decide (σ (.n 17) ≠ 0) = decide (S ≠ 1) := by
    refine decide_eq_decide.mpr ⟨fun h hS' => h ?_, fun h h0 => h ?_⟩
    · show gen ^ 1 + gen ^ S = 0
      rw [hS']; exact CharTwo.add_self_eq_zero _
    · have := gen_pow_inj (by omega) (by omega) (CharTwo.add_eq_zero.mp (show gen ^ 1 + gen ^ S = 0 from h0))
      omega
  have hOut0 : ∀ rd, ReadsAt rd (ptrAt (F0 + cert (dqwName d cd) (.n 5))) (qwRunList d cd w0) →
      ReadsAt rd (ptrAt (lpDqFrame fs al (dqwName d cd) loop S c 0 + cert (dqwName d cd) (.n 5)))
        (qwRunList d cd (sqSample w0 fsv 0)) := fun rd h => by
    rw [lpDqFrame_zero]; simpa [sqSample] using h
  have hecB : ec ≤ c + 5 * (S + 1) + 15 + fs (dqwName d cd) := by
    rw [hec]; unfold lpDqStep; have := allocBase_le (al (dqwName d cd)) (c + 5 * (S + 1)); omega
  have hfLB : fL ≤ ec + 15 := by rw [hfL]; exact allocBase_le _ _
  have hkids : ∃ e, e ≤ c + (S + 1) * (fs (dqwName d cd) + fs loop + fs (tailKey loop) + 64) ∧
      KidsAtF fs al cert kd σ (fun i => R i ∨ ownData cert fp c name (allocs σ es) es i)
      (LpPosPre fs al cert d cd S ipos iptr it loop w0 fsv c) (fun rd => HoldsWords rd Wo) (fun _ => False)
      ((calls es).map fun _ => PostQuiet) (calls es) (c + (allocs σ es).sum) e
      (fun rd => HoldsWords rd Wo ∧ LpPosOut fs al cert d cd S loop w0 fsv c rd) (LpPosD fs al cert d cd S loop c) := by
    rw [hcalls, hsum]
    simp only [List.map_cons, List.map_nil]
    by_cases hS1' : S = 1
    · -- no loop
      have hd : decide (σ (.n 17) ≠ 0) = false := by rw [hd17]; simp [hS1']
      refine ⟨fL + fs (tailKey loop), lp_end_le (x := fL + fs (tailKey loop)) hS1 (by omega) (by omega), ?_⟩
      rw [KidsAtF]
      simp only [↓reduceIte]
      refine ⟨fs (dqwName d cd), ec, Rc, _, _, fun i hi => Or.inl (hRc i hi), hdq, ?_⟩
      rw [KidsAtF]
      simp only [hd, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨fun v => ([V.n 18, .n 9, .n 15, .n 6, .n 7, .n 8].map σ).getD v.idx 0, fl, hfl, ?_⟩, ?_⟩
      · rw [hpl]; exact params_range_map _
      · rw [KidsAtF]
        refine ⟨rfl, fun rd h => ⟨h.1, fun j hj => ?_⟩, fun i hi => ?_⟩
        · obtain rfl : j = 0 := by omega
          exact hOut0 rd h.2
        · obtain ⟨j, hj, hi1, hi2⟩ := hi
          obtain rfl : j = 0 := by omega
          rw [lpDqFrame_zero] at hi1 hi2
          exact Or.inr ⟨hi1, hi2⟩
    · -- the loop
      have hd : decide (σ (.n 17) ≠ 0) = true := by rw [hd17]; simpa using hS1'
      have hReg : LpLReg S (128 / d) c ipos iptr it Rc :=
        ⟨fun n hn => Or.inr ⟨by omega, by omega⟩, fun k hk => Or.inl (hRp k hk), fun k hk => Or.inl (hRq k hk),
          fun n hn => Or.inl (hRt n (by omega))⟩
      have hL := lpL_complete hfl hpl hbl hlc hqw hkd hS (fsv := fsv) rfl w0 hReg (S - 2) 1 (by omega) le_rfl fL cL
        le_rfl
      have hiter := iter_le_add (g := lpDqStep fs al (dqwName d cd)) (d := 15 + fs (dqwName d cd))
        (fun x => by have := allocBase_le (al (dqwName d cd)) x; unfold lpDqStep; omega) (S - 1) cL
      have hcLe : cL = fL + ((S - 1) * fs loop + fs (tailKey loop)) := by rw [hcL, lpB]
      refine ⟨(lpDqStep fs al (dqwName d cd))^[S - 1] cL, lp_end_le (x := cL) hS1 (by omega) hiter, ?_⟩
      rw [KidsAtF]
      simp only [↓reduceIte]
      refine ⟨fs (dqwName d cd), ec, Rc, _, _, fun i hi => Or.inl (hRc i hi), hdq, ?_⟩
      rw [KidsAtF]
      simp only [hd, ↓reduceIte]
      refine ⟨lpB fs loop S 1, (lpDqStep fs al (dqwName d cd))^[S - 1] cL, Rc, LpLD fs al cert d cd S cL 1,
        LpLOut fs al cert d cd S w0 fsv cL 1, fun i hi => Or.inl (hRc i hi), ?_, ?_⟩
      · refine hL.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd h => ?_) (fun _ _ _ h => h)
        refine ⟨h.1.1, hWo rd h.2.1, fun k hk1 hk2 => ?_⟩
        rw [← lpDqFrame_lpF (dqwName d cd) loop hcL (by omega)]
        exact hblkP k hk2 rd h.1
      · rw [KidsAtF]
        refine ⟨rfl, fun rd h => ⟨h.1.1, fun j hj => ?_⟩, fun i hi => ?_⟩
        · rcases Nat.eq_zero_or_pos j with rfl | hj0
          · exact hOut0 rd h.1.2
          · have := h.2 j hj0 hj
            rwa [← lpDqFrame_lpF (dqwName d cd) loop hcL (by omega)] at this
        · obtain ⟨j, hj, hi1, hi2⟩ := hi
          rcases Nat.eq_zero_or_pos j with rfl | hj0
          · rw [lpDqFrame_zero] at hi1 hi2
            exact Or.inl (Or.inr ⟨hi1, hi2⟩)
          · rw [lpDqFrame_lpF (dqwName d cd) loop hcL (by omega)] at hi1 hi2
            exact Or.inr ⟨j, hj0, hj, hi1, hi2⟩
  obtain ⟨e, hbe, hk⟩ := hkids
  refine ⟨e, hbe, callAtA_node hlo hfc ⟨σ, fo, es, [.n 28, .n 29, .n 30, .n 31, .n 32],
    Wo, (calls es).map fun _ => PostQuiet, fun rd => HoldsWords rd Wo ∧ LpPosOut fs al cert d cd S loop w0 fsv c rd,
    LpPosD fs al cert d cd S loop c, hfo, by rw [hpo]; rfl, hw, ?_, ?_, ?_, hloads, ?_, fun i h => Or.inr h, hk,
    fun rd h => h.2, fun rd _ hp hO => hev rd hp hO.1, ?_⟩⟩
  · -- the returns
    show [r0, r1, r2, r3, r4] = ((⟨fsv, []⟩ : Fs).squeezeN (S - 1)).2.cap
    rw [← hrS]; rfl
  · -- placed
    rw [hal]
    refine ⟨?_, fun q' hq' => ?_⟩
    · rw [hes, (straight_parts σ _ hstr).1]; rfl
    · have h0 : (lpPreX d cd loop).filterMap Stmt.addrS = [] := rfl
      rw [hes, (straight_parts σ _ hstr).2.2.1, h0] at hq'
      exact absurd hq' List.not_mem_nil
  · -- own words
    rw [hsum]
    refine ⟨fun q' hq' => Or.inr ?_, List.pairwise_singleton _ _⟩
    simp only [Wo, List.mem_cons, List.not_mem_nil, or_false] at hq'
    subst hq'
    exact ⟨le_rfl, by simp [lpSqz_length]⟩
  · -- heap hints
    intro A hA
    rw [hhA] at hA
    exact absurd hA List.not_mem_nil
  · -- the post
    intro rd ts _ _ _ hv hq'
    refine postQuiet_node hfo hw (fun a ha => ?_) (fun ev hev' => ?_) hv hq' _
    · have := List.all_eq_true.mp (lpPreX_quiet d cd loop) _ (mem_atom_slEvs ha)
      simpa using this
    · cases ev with
      | atom a =>
        refine exact_of_trivExact ?_
        have := List.all_eq_true.mp (lpPreX_triv d cd loop) _ (mem_atom_slEvs hev')
        simpa using this
      | _ => trivial

/-! ## Every specialization -/

/-- **`level_positions` completes placed.** -/
theorem lpA_complete' {kd : ℕ} {name loop : String} {d cd : ℕ} {fo fl : Fn}
    (hfo : coreProgram.find? name = some fo) (hpo : fo.params = osParams 10) (hbo : fo.body = lpBody d cd loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = osParams 6) (hbl : fl.body = lpLoopBody d cd loop)
    (hlc : lpLChecks d cd loop = true) (hqw : QwA fs al cert kd (dqwName d cd) d cd) :
    LpA fs al cert kd name loop (dqwName d cd) d cd :=
  (lpAE_complete' hfo hpo hbo hfl hpl hbl hlc hqw).toA

/-- **Every `level_positions` completes placed, its end bounded**, given its decode's `QwA`. -/
theorem lpAE_complete (kd : ℕ) : ∀ e ∈ lpTable, QwA fs al cert kd (dqwName e.2.2.1 e.2.2.2) e.2.2.1 e.2.2.2 →
    LpAE fs al cert kd e.1 e.2.1 (dqwName e.2.2.1 e.2.2.2) e.2.2.1 e.2.2.2 := by
  intro e he hqw
  obtain ⟨⟨fo, hfo, hpo, hbo⟩, ⟨fl, hfl, hpl, hbl⟩⟩ := lpTable_ok e he
  have hck := lp_checks e he
  simp only [lpEntryOk, Bool.and_eq_true, decide_eq_true_eq] at hck
  exact lpAE_complete' hfo hpo hbo hfl hpl hbl hck.1 hqw

/-- **Every `level_positions` completes placed at the compiled frames, its end bounded.** -/
theorem lpAE_b2c (al : String → Bool) (kd : ℕ) : ∀ e ∈ lpTable,
    LpAE B2C.fs al B2C.cert kd e.1 e.2.1 (dqwName e.2.2.1 e.2.2.2) e.2.2.1 e.2.2.2 := by
  intro e he
  have hck := lp_checks e he
  simp only [lpEntryOk, Bool.and_eq_true, decide_eq_true_eq] at hck
  have hq : QwA B2C.fs al B2C.cert kd (dqwName e.2.2.1 e.2.2.2) e.2.2.1 e.2.2.2 :=
    qwA_b2c al kd (dqwName e.2.2.1 e.2.2.2, e.2.2.1, e.2.2.2) hck.2
  exact lpAE_complete (fs := B2C.fs) (cert := B2C.cert) kd e he hq

/-- **Every `level_positions` completes placed**, given its decode's `QwA`. -/
theorem lpA_complete (kd : ℕ) : ∀ e ∈ lpTable, QwA fs al cert kd (dqwName e.2.2.1 e.2.2.2) e.2.2.1 e.2.2.2 →
    LpA fs al cert kd e.1 e.2.1 (dqwName e.2.2.1 e.2.2.2) e.2.2.1 e.2.2.2 := by
  intro e he hqw
  obtain ⟨⟨fo, hfo, hpo, hbo⟩, ⟨fl, hfl, hpl, hbl⟩⟩ := lpTable_ok e he
  have hck := lp_checks e he
  simp only [lpEntryOk, Bool.and_eq_true, decide_eq_true_eq] at hck
  exact lpA_complete' hfo hpo hbo hfl hpl hbl hck.1 hqw

/-- **Every `level_positions` completes placed at the compiled frames.** -/
theorem lpA_b2c (al : String → Bool) (kd : ℕ) : ∀ e ∈ lpTable,
    LpA B2C.fs al B2C.cert kd e.1 e.2.1 (dqwName e.2.2.1 e.2.2.2) e.2.2.1 e.2.2.2 := by
  intro e he
  have hck := lp_checks e he
  simp only [lpEntryOk, Bool.and_eq_true, decide_eq_true_eq] at hck
  have hq : QwA B2C.fs al B2C.cert kd (dqwName e.2.2.1 e.2.2.2) e.2.2.1 e.2.2.2 :=
    qwA_b2c al kd (dqwName e.2.2.1 e.2.2.2, e.2.2.1, e.2.2.2) hck.2
  exact lpA_complete (fs := B2C.fs) (cert := B2C.cert) kd e he hq

end
end LeanVM.Guest.B1.VsC
