/-
  LeanVM.Guest.B1.Place.LrProof

  `level_residual` is complete placed at every specialization of `lrTable`.
-/

module

public import LeanVM.Guest.B1.Place.Lr
public import LeanVM.Guest.B1.Place.LrLoops
public import LeanVM.Guest.B1.Place.LpProof
public import LeanVM.Guest.B1.Place.LrPure
public import LeanVM.Guest.Memory.Retemp
public import LeanVM.Guest.Memory.Restrict
public import LeanVM.Guest.B1.Whir.DataSpec
public import LeanVM.Guest.B1.Whir.HelperAll
import LeanVM.Guest.StmtsAppend

/-!
# `level_residual`, placed

`level_residual` at `fp` allocates one buffer at `fp + fs name` (`lrSizes`, `lrW`): its batches'
chains (`rcC`, from `0`), then the rest's (`rsC`, from `2·(q / resBatch)`); its loops, which place
nothing, are placed after it by trees of one size on every memory holding its words
(`lr_relAtIn_pure_uniform`, `lr_guarded_uniform`).

* `lr_relAtIn`: the body at `fp`, its loops' trees given.
* `lr_key`: the body at `fp`, its buffer's words honest, on every memory holding the buffer and the
  caller's words.
* `lrAtD_of`, `level_residual_completeAt`: `LrAtD` at every entry of `lrTable`, from its facts
  (`LrFacts`: its sizes decided, `lrTable_sizes`; its loops pure at every row, `Place/LrPure`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## Small facts -/

/-- The valuation holding the words `args` at the values `0 ..`. -/
def lrVal (args : List E) : Val := fun v ↦ args.getD v.idx 0

theorem lrVal_n (args : List E) (i : ℕ) : lrVal args (.n i) = args.getD i 0 := rfl

/-- The size of `level_residual`'s buffer at `q` queries: the batches' chains, then the rest's. -/
def lrSizes (q : ℕ) : List ℕ := [2 * (q / resBatch + q % resBatch + 1)]

/-- What a straight statement's events need: an atom holds, a conditional call's condition is in
`K`. -/
def LrSlOk (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .callIf c _ _ => IsInK (σ c)
  | _ => True

theorem lr_slEvs_holds {rd : Reader} {σ : Val} {pre : List Stmt} (h : ∀ s ∈ pre, LrSlOk rd σ s) :
    ∀ e ∈ pre.flatMap (Main.slEvs σ), e.Holds rd σ := by
  intro e he
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  have hs' := h s hs
  match s, hs', he with
  | .atom a, hs', he =>
    simp only [Main.slEvs, List.mem_singleton] at he
    subst he; exact hs'
  | .call .., _, he =>
    simp only [Main.slEvs, List.mem_singleton] at he
    subst he; trivial
  | .callIf c f args, hs', he =>
    simp only [Main.slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hs'
    · split <;> trivial

theorem lr_slOk_of_allOk {C : CallRel} {rd : Reader} {σ : Val} {pre : List Stmt}
    (h : Whir.AllOk C rd σ pre) : ∀ s ∈ pre, LrSlOk rd σ s := by
  intro s hs
  have hs' := h s hs
  match s, hs' with
  | .atom _, hs' => exact hs'
  | .callIf .., hs' => exact hs'.1
  | .call .., _ => trivial
  | .ite .., _ => trivial
  | .match_ .., _ => trivial
  | .dispatch .., _ => trivial
  | .ret _, _ => trivial

theorem lr_one_lt (n : ℕ) : 1 < 2 * (n + 1) := by omega

theorem lr_zero_lt (n : ℕ) : 0 < 2 * (n + 1) := by omega

theorem isInK_one_add_gen_pow (n : ℕ) : IsInK (1 + gen ^ n) :=
  isInK_add (by rw [← pow_zero gen]; exact gen_pow_isInK 0) (gen_pow_isInK n)

/-- **A loop's call as a callee**: entered when its guard is not zero. -/
theorem kidsFromIn_loopCall {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader} {σ : Val}
    {R Dacc Rk : ℕ → Prop} {b m n' : ℕ} {f : String} {args : List V} {cv : V} {cs : List Call}
    (hRk : ∀ i, Rk i → R i)
    (h : if σ cv ≠ 0 then RelAtIn coreProgram fs cert rd Rk (fun _ ↦ False) b m f (args.map σ) []
      else m = fs (tailKey f))
    (hrest : ∀ Dacc', KidsFromIn coreProgram fs cert rd σ R Dacc' cs (b + m) n' (fun _ ↦ False)) :
    KidsFromIn coreProgram fs cert rd σ R Dacc (⟨f, args, [], decide (σ cv ≠ 0)⟩ :: cs) b (m + n')
      (fun _ ↦ False) := by
  refine ⟨m, n', Rk, fun _ ↦ False, rfl, fun i hi ↦ Or.inl (hRk i hi), ?_, hrest _⟩
  simp only [decide_eq_true_eq, List.map_nil]
  exact h

theorem lr_kidsFromIn_nil {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader} {σ : Val}
    {R Dacc : ℕ → Prop} {b : ℕ} :
    KidsFromIn coreProgram fs cert rd σ R Dacc [] b 0 (fun _ ↦ False) :=
  ⟨rfl, fun _ h ↦ h.elim⟩

theorem lr_notLoop {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    {pre : List Stmt} {vs : List V} (hv : vs ≠ []) (hb : fn.body = pre ⧺ [.ret vs]) :
    coreProgram.loop name = false := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hv
  rw [Program.loop_of_find? hf, Fn.loop, hb]
  simp [List.reverse_append]

/-! ## The body, placed -/

theorem lr_addr_mul (b e : ℕ) : ofK (addressOfIndex b) * gen ^ e = ofK (addressOfIndex (b + e)) :=
  ofK_addr_mul_gen_pow b e

set_option maxHeartbeats 1600000 in
/-- **`level_residual` placed** at `fp`: its chains `W` at `fp + fs name` (the batches' from `0`,
the rest's from `2·(q / resBatch)`), its loops' trees of `m1` and `m2` words after them. -/
theorem lr_relAtIn {name loop1 loop2 : String} {q : ℕ}
    (hlr : FnIs name (osParams 6) (lrBody loop1 loop2)) (hq : q < ordG)
    (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader}
    {R Rk1 Rk2 : ℕ → Prop} {fp m1 m2 : ℕ} {P BD HS M : E} {W : List E}
    (hW : ReadsAt rd (ofK (addressOfIndex (fp + fs name))) W)
    (hWl : W.length = 2 * (q / resBatch + q % resBatch + 1)) (hz0 : W.getD 0 0 = 0)
    (hz1 : W.getD 1 0 = 0)
    (hL1 : if 1 + gen ^ (q / resBatch) ≠ 0 then
      RelAtIn coreProgram fs cert rd Rk1 (fun _ ↦ False) (fp + fs name + W.length) m1 loop1
        [1, gen ^ (q / resBatch), P, ofK (addressOfIndex (fp + fs name)), BD, HS, M] []
      else m1 = fs (tailKey loop1))
    (hL2 : if 1 + gen ^ (q % resBatch) ≠ 0 then
      RelAtIn coreProgram fs cert rd Rk2 (fun _ ↦ False) (fp + fs name + W.length + m1) m2 loop2
        [1, gen ^ (q % resBatch), ofK (addressOfIndex (fp + fs name + 2 * (q / resBatch))),
          P * gen ^ (resBatch * (q / resBatch)), BD, HS, M] []
      else m2 = fs (tailKey loop2))
    (hRk1 : ∀ i, Rk1 i → R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + W.length))
    (hRk2 : ∀ i, Rk2 i → R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + W.length)) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp (fs name + W.length + (m1 + m2)) name
      [P, BD, HS, M, gen ^ (q / resBatch), gen ^ (q % resBatch)]
      [W.getD (2 * (q / resBatch) + 2 * (q % resBatch)) 0,
        W.getD (2 * (q / resBatch) + 2 * (q % resBatch) + 1) 0] := by
  obtain ⟨fn, hf, hps, hb⟩ := hlr
  set B := q / resBatch with hB
  set r := q % resBatch with hr
  have hBle : B ≤ q := Nat.div_le_self _ _
  have hrle : r ≤ q := Nat.mod_le _ _
  have hO : ordG = 2 ^ 64 - 1 := rfl
  have hU : u128Bound = 2 ^ 128 := rfl
  have hrb8 : resBatch = 8 := rfl
  have hg0 : gw 0 = 1 := by rw [Whir.gw_eq (by rw [hU]; omega), pow_zero]
  have hg1 : gw 1 = gen := by rw [Whir.gw_eq (by rw [hU]; omega), pow_one]
  set b := fp + fs name with hbd
  set CH : E := ofK (addressOfIndex b) with hCH
  set R0 := W.getD (2 * B + 2 * r) 0 with hR0
  set R1 := W.getD (2 * B + 2 * r + 1) 0 with hR1
  set A : List E := [P, BD, HS, M, gen ^ B, gen ^ r, gen ^ B * gen ^ r, gw 1,
    gen ^ B * gen ^ r * gw 1, gen ^ B * gen ^ r * gw 1 * (gen ^ B * gen ^ r * gw 1), CH, word 0 0,
    word 0 0, gw 0, gw 0 + gen ^ B, gw 0, gen ^ B * gen ^ B, CH * (gen ^ B * gen ^ B)] with hA
  set PV := lqPowVals (gen ^ B) (osPowDigits resBatch) 1 with hPV
  set T : List E := [P * (gen ^ B) ^ resBatch, gw 0, gw 0 + gen ^ r, gw 0, gen ^ r * gen ^ r,
    CH * (gen ^ B * gen ^ B) * (gen ^ r * gen ^ r), R0, R1] with hT
  set vals := A ++ (PV ++ T) with hvals
  set σ := lrVal vals with hσ
  have hAl : A.length = 18 := rfl
  have hpl : PV.length = osPowLen resBatch := by rw [hPV, lqPowVals_length, osPowLen]
  have hvA : ∀ i < 18, σ (.n i) = A.getD i 0 := fun i hi ↦ by
    rw [hσ, lrVal_n, hvals, List.getD_append _ _ _ _ (by rw [hAl]; exact hi)]
  have hvP : ∀ j < osPowLen resBatch, σ (.n (18 + j)) = PV.getD j 0 := fun j hj ↦ by
    rw [hσ, lrVal_n, hvals, List.getD_append_right _ _ _ _ (by rw [hAl]; omega), hAl,
      show 18 + j - 18 = j by omega, List.getD_append _ _ _ _ (by rw [hpl]; exact hj)]
  have hvT : ∀ j < 8, σ (.n (18 + osPowLen resBatch + j)) = T.getD j 0 := fun j hj ↦ by
    rw [hσ, lrVal_n, hvals, List.getD_append_right _ _ _ _ (by rw [hAl]; omega), hAl,
      show 18 + osPowLen resBatch + j - 18 = osPowLen resBatch + j by omega,
      List.getD_append_right _ _ _ _ (by rw [hpl]; omega), hpl,
      show osPowLen resBatch + j - osPowLen resBatch = j by omega]
  have a0 : σ (.n 0) = P := hvA 0 (by omega)
  have a1 : σ (.n 1) = BD := hvA 1 (by omega)
  have a2 : σ (.n 2) = HS := hvA 2 (by omega)
  have a3 : σ (.n 3) = M := hvA 3 (by omega)
  have a4 : σ (.n 4) = gen ^ B := hvA 4 (by omega)
  have a5 : σ (.n 5) = gen ^ r := hvA 5 (by omega)
  have a9 : σ (.n 9) = gen ^ B * gen ^ r * gw 1 * (gen ^ B * gen ^ r * gw 1) := hvA 9 (by omega)
  have a10 : σ (.n 10) = CH := hvA 10 (by omega)
  have a14 : σ (.n 14) = gw 0 + gen ^ B := hvA 14 (by omega)
  have a15 : σ (.n 15) = gw 0 := hvA 15 (by omega)
  have a17 : σ (.n 17) = CH * (gen ^ B * gen ^ B) := hvA 17 (by omega)
  have t0 : σ (.n (18 + osPowLen resBatch)) = P * (gen ^ B) ^ resBatch := hvT 0 (by omega)
  have t2 : σ (.n (18 + osPowLen resBatch + 2)) = gw 0 + gen ^ r := hvT 2 (by omega)
  have t3 : σ (.n (18 + osPowLen resBatch + 3)) = gw 0 := hvT 3 (by omega)
  have t5 : σ (.n (18 + osPowLen resBatch + 5)) = CH * (gen ^ B * gen ^ B) * (gen ^ r * gen ^ r) :=
    hvT 5 (by omega)
  have t6 : σ (.n (18 + osPowLen resBatch + 6)) = R0 := hvT 6 (by omega)
  have t7 : σ (.n (18 + osPowLen resBatch + 7)) = R1 := hvT 7 (by omega)
  have hpow := lq_powSteps_complete (C := fun _ _ _ ↦ True) (rd := rd) (σ := σ) 4
    (osPowDigits resBatch) 4 18 1 (by rw [pow_one]) (fun j hj ↦ by
      rw [a4] at hj ⊢; exact hvP j (by rw [← hpl]; exact hj))
  rw [a4, batch_digits] at hpow
  -- the chains' cells
  have hld : ∀ e < W.length, LoadHolds rd CH e (W.getD e 0) := fun e he ↦ by
    rw [List.getD_eq_getElem _ _ he]; exact hW e he
  have hl0 : LoadHolds rd CH 0 (word 0 0) := by
    have := hld 0 (by rw [hWl]; exact lr_zero_lt _); rwa [hz0, ← word_zero] at this
  have hl1 : LoadHolds rd CH 1 (word 0 0) := by
    have := hld 1 (by rw [hWl]; exact lr_one_lt _); rwa [hz1, ← word_zero] at this
  have hE5 : CH * (gen ^ B * gen ^ B) * (gen ^ r * gen ^ r) = CH * gen ^ (2 * B + 2 * r) := by ring
  have hlR0 : LoadHolds rd (CH * (gen ^ B * gen ^ B) * (gen ^ r * gen ^ r)) 0 R0 := by
    rw [hE5, loadHolds_mul_gen_pow]; exact hld _ (by rw [hWl]; omega)
  have hlR1 : LoadHolds rd (CH * (gen ^ B * gen ^ B) * (gen ^ r * gen ^ r)) 1 R1 := by
    rw [hE5, loadHolds_mul_gen_pow]; exact hld _ (by rw [hWl]; omega)
  have hok : Whir.AllOk (fun _ _ _ ↦ True) rd σ (lrBodyA loop1 loop2) := by
    simp only [lrBodyA, allOk_append]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, hpow.1⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [osCst, osLd, osMul, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      simp only [hvA 4 (by omega), hvA 5 (by omega), hvA 6 (by omega), hvA 7 (by omega),
        hvA 8 (by omega), hvA 9 (by omega), hvA 10 (by omega), hvA 11 (by omega),
        hvA 12 (by omega), hA]
      simp [hl0, hl1]
    · simp only [osLoopCallR, osCst, osAdd, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      simp only [hvA 4 (by omega), hvA 13 (by omega), hvA 14 (by omega), hvA 15 (by omega), hA]
      simp [hg0, isInK_one_add_gen_pow]
    · simp only [osMul, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      simp only [hvA 4 (by omega), hvA 10 (by omega), hvA 16 (by omega), hvA 17 (by omega), hA]
      simp
    · simp only [osMul, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      rw [t0, a0, hpow.2]
    · simp only [osLoopCallR, osCst, osAdd, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      rw [hvT 1 (by omega), t2, t3, a5]
      simp [hT, hg0, isInK_one_add_gen_pow]
    · simp only [osMul, osLd, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      rw [hvT 4 (by omega), t5, t6, t7, a5, a17]
      simp only [hT]
      exact ⟨by simp, by simp, hlR0, hlR1⟩
  have hstr : (lrBodyA loop1 loop2).all Main.Stmt.straight = true := by
    simp [lrBodyA, osLoopCallR, Main.Stmt.straight, os_powSteps_straight]
  have hb' : fn.body = lrBodyA loop1 loop2 ⧺
      [.ret [.n (18 + osPowLen resBatch + 6), .n (18 + osPowLen resBatch + 7)]] := by
    rw [hb, lrBody_split]
  have hw := Main.walk_straight σ [.n (18 + osPowLen resBatch + 6), .n (18 + osPowLen resBatch + 7)]
    (lrBodyA loop1 loop2) hstr
  rw [← hb'] at hw
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ (lrBodyA loop1 loop2) hstr
  have hal : (lrBodyA loop1 loop2).filterMap Main.Stmt.allocSz = [(.n 10, .inr (.n 9))] := by
    simp only [lrBodyA, List.filterMap_append, fm_pow_nil Main.Stmt.allocSz (fun _ _ _ ↦ rfl)]
    rfl
  set es := (lrBodyA loop1 loop2).flatMap (Main.slEvs σ) with hes
  have hsz : W.length < 2 ^ 64 - 1 := by
    have h8 : resBatch * B ≤ q := Nat.mul_div_le q resBatch
    have hr8 : r < resBatch := Nat.mod_lt q (by rw [hrb8]; omega)
    rw [hrb8] at h8 hr8
    rw [hWl]; omega
  have hallocs : allocs σ es = [W.length] := by
    rw [i2, hal]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, a9, hg1]
    rw [show gen ^ B * gen ^ r * gen * (gen ^ B * gen ^ r * gen) = gen ^ W.length by
      rw [hWl]; ring, logG_gen_pow hsz]
  have hcalls : calls es = [⟨loop1, [.n 15, .n 4, .n 0, .n 10, .n 1, .n 2, .n 3], [],
      decide (σ (.n 14) ≠ 0)⟩, ⟨loop2, [.n (18 + osPowLen resBatch + 3), .n 5, .n 17,
        .n (18 + osPowLen resBatch), .n 1, .n 2, .n 3], [],
      decide (σ (.n (18 + osPowLen resBatch + 2)) ≠ 0)⟩] := by
    rw [i4]
    simp only [lrBodyA, List.filterMap_append, fm_pow_nil Main.Stmt.callS (fun _ _ _ ↦ rfl)]
    rfl
  have hown : ∀ i, b ≤ i → i < b + W.length →
      ownData cert fp (fp + fs name) name (allocs σ es) es i :=
    fun i h1 h2 ↦ Or.inl ⟨(W.length, b), by rw [hallocs]; simp [bases, b], h1, h2⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    coreProgram_wf (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp)
    (N := m1 + (m2 + 0)) (args := [P, BD, HS, M, gen ^ B, gen ^ r]) (rets := [R0, R1])
    hf (Or.inl (lr_notLoop hf (by simp) hb')) (by
      rw [hps]; simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
        List.nil_append, List.cons_append]
      rw [a0, a1, a2, a3, a4, a5]) hw
    (by simp only [List.map_cons, List.map_nil]; rw [t6, t7])
    (lr_slEvs_holds (lr_slOk_of_allOk hok))
    (by rw [i1, hal, hallocs]; simp [bases, a10, hCH, b])
    (fun q' hq' ↦ by
      have ha : (lrBodyA loop1 loop2).filterMap Main.Stmt.addrS = [] := by
        simp only [lrBodyA, List.filterMap_append, fm_pow_nil Main.Stmt.addrS (fun _ _ _ ↦ rfl)]
        rfl
      rw [i3, ha] at hq'
      simp at hq')
    ?_ (fun A' hA' ↦ ?_) (fun _ h ↦ h.elim)
  · rw [hallocs] at h
    simpa [Nat.add_assoc] using h
  · rw [hcalls, hallocs, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hargs1 : ([.n 15, .n 4, .n 0, .n 10, .n 1, .n 2, .n 3] : List V).map σ =
        [1, gen ^ B, P, CH, BD, HS, M] := by
      simp only [List.map_cons, List.map_nil]
      rw [a15, a4, a0, a10, a1, a2, a3, hg0]
    have hargs2 : ([.n (18 + osPowLen resBatch + 3), .n 5, .n 17, .n (18 + osPowLen resBatch), .n 1,
        .n 2, .n 3] : List V).map σ =
        [1, gen ^ r, ofK (addressOfIndex (b + 2 * B)), P * gen ^ (resBatch * B), BD, HS, M] := by
      simp only [List.map_cons, List.map_nil]
      rw [t3, a5, a17, t0, a1, a2, a3, hg0, hCH, ← pow_add, lr_addr_mul, ← two_mul, ← pow_mul,
        Nat.mul_comm B resBatch]
    have hreg : ∀ Rk : ℕ → Prop, (∀ i, Rk i → R i ∨ (b ≤ i ∧ i < b + W.length)) →
        ∀ i, Rk i → R i ∨ ownData cert fp (fp + fs name) name [W.length] es i := by
      intro Rk hRk i hi
      rcases hRk i hi with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [← hallocs]; exact hown i h.1 h.2)
    refine kidsFromIn_loopCall (Rk := Rk1) (hreg Rk1 hRk1) (by rw [hargs1, a14, hg0]; exact hL1)
      fun _ ↦ kidsFromIn_loopCall (Rk := Rk2) (hreg Rk2 hRk2) (by rw [hargs2, t2, hg0]; exact hL2)
        fun _ ↦ lr_kidsFromIn_nil
  · rw [B1.loadAddrs_straight σ _ hstr] at hA'
    have hl : (lrBodyA loop1 loop2).filterMap B1.Stmt.loadS =
        [(.n 10, 0), (.n 10, 1), (.n (18 + osPowLen resBatch + 5), 0),
          (.n (18 + osPowLen resBatch + 5), 1)] := by
      simp only [lrBodyA, List.filterMap_append, fm_pow_nil B1.Stmt.loadS (fun _ _ _ ↦ rfl)]
      rfl
    rw [hl] at hA'
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA'
    have hw1 : ∀ t < W.length, ∃ j, (ofK (addressOfIndex b) * gen ^ 0).limb 0 * addressOfIndex t =
        addressOfIndex j ∧ (ownData cert fp (fp + fs name) name (allocs σ es) es j ∨ R j ∨ False) :=
      fun t ht ↦ ⟨b + 0 + t, lp_addr _ _ _, Or.inl (hown _ (by omega) (by omega))⟩
    have hw2 : ∀ t < 2, ∃ j, (ofK (addressOfIndex b) * gen ^ (2 * B + 2 * r)).limb 0 *
        addressOfIndex t = addressOfIndex j ∧
        (ownData cert fp (fp + fs name) name (allocs σ es) es j ∨ R j ∨ False) :=
      fun t ht ↦ ⟨b + (2 * B + 2 * r) + t, lp_addr _ _ _,
        Or.inl (hown _ (by omega) (by rw [hWl]; omega))⟩
    rcases hA' with rfl | rfl | rfl | rfl
    · rw [a10, hCH, ← mul_one (ofK _), ← pow_zero gen]; exact hw1 0 (by rw [hWl]; exact lr_zero_lt _)
    · rw [a10, hCH, ← mul_one (ofK _), ← pow_zero gen]; exact hw1 1 (by rw [hWl]; exact lr_one_lt _)
    · rw [t5, hE5, hCH]; exact hw2 0 (by omega)
    · rw [t5, hE5, hCH]; exact hw2 1 (by omega)

/-! ## Pure loops, one size on every memory -/

/-- **A pure callee on the words `Lk`, one size**: its relation on every memory defined below
`2^κ` holding `Lk`, kept on `Lk`, places it on all of them by trees of one size. -/
theorem lr_relAtIn_pure_uniform {S : List String} (hS : coreProgram.PureIn S) {g : String}
    (hg : g ∈ S) (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {Lk : Layout}
    {args rets : List E}
    (h : ∀ rd, LowDef κ rd → MemL rd Lk →
      coreProgram.Rel (Main.restrict rd (RegionL Lk)) g args rets) :
    ∃ n, ∀ fp rd, LowDef κ rd → MemL rd Lk →
      RelAtIn coreProgram fs cert rd (RegionL Lk) (fun _ ↦ False) fp n g args rets := by
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lk
  swap
  · exact ⟨0, fun fp rd hl hL ↦ absurd ⟨rd, hl, hL⟩ hex⟩
  obtain ⟨rd1, hl1, h1⟩ := hex
  have hsupp := Main.restrict_supp' rd1 (RegionL Lk)
  obtain ⟨n, hn⟩ := relAtIn_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg
    (Main.relIn_of_rel_supp coreProgram_wf hsupp (h rd1 hl1 h1))
  refine ⟨n, fun fp rd _ hL ↦ hn fp rd (fun i hi ↦ ?_) (fun A hA ↦ ?_)⟩
  · rw [Main.memL_agree hL h1 i hi, Main.restrict_of ⟨i, rfl, hi⟩]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi⟩ := hsupp _ _ hv
    rw [Main.memL_agree hL h1 i hi, ← Main.restrict_of (rd := rd1) (S := RegionL Lk) ⟨i, rfl, hi⟩, hv]
    rfl

/-- **A guarded pure call on the words `Lk`**, one size on every memory defined below `2^κ`
holding them. -/
theorem lr_guarded_uniform {S : List String} (hS : coreProgram.PureIn S) {g : String} (hg : g ∈ S)
    (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {Lk : Layout} {args : List E}
    {G : Prop} [Decidable G]
    (h : G → ∀ rd, LowDef κ rd → MemL rd Lk →
      coreProgram.Rel (Main.restrict rd (RegionL Lk)) g args []) :
    ∃ m, ∀ fp' rd, LowDef κ rd → MemL rd Lk → if G then
      RelAtIn coreProgram fs cert rd (RegionL Lk) (fun _ ↦ False) fp' m g args []
      else m = fs (tailKey g) := by
  by_cases hG : G
  · obtain ⟨n, hn⟩ := lr_relAtIn_pure_uniform hS hg fs cert (h hG)
    exact ⟨n, fun fp' rd hl hL ↦ by simp only [hG, ↓reduceIte]; exact hn fp' rd hl hL⟩
  · exact ⟨fs (tailKey g), fun _ _ _ _ ↦ by simp only [hG, ↓reduceIte]⟩

theorem lr_pureIn {loop : String} {body : List Stmt} (hl : FnIs loop (osParams 7) body)
    (hp : Stmt.pureList [loop] body = true) : coreProgram.PureIn [loop] := by
  intro g hg fn hf
  obtain ⟨fl, hfl, -, hbl⟩ := hl
  rw [List.mem_singleton] at hg
  subst hg
  rw [hfl] at hf; cases hf; rw [hbl]; exact hp

/-! ## The decided facts -/

/-- An entry's static facts: its row's (`ResStatic`, but the query count's), its loops placing
nothing, and its words few. -/
def LrFacts (cols nhs hbits : ℕ) (l1 l2 : String) : Prop :=
  1 ≤ cols ∧ 1 ≤ nhs ∧ hbits ≤ 3 ∧ hbits ≤ cols + 1 ∧
    Stmt.pureList [l1] (lrLoop1Body cols nhs hbits l1) = true ∧
    Stmt.pureList [l2] (lrLoop2Body cols nhs hbits l2) = true ∧ cols + nhs ≤ 2 ^ 20

/-- An entry's sizes: `LrFacts` but the loops' purity, which holds at every row. -/
def LrSizes (cols nhs hbits : ℕ) : Prop :=
  1 ≤ cols ∧ 1 ≤ nhs ∧ hbits ≤ 3 ∧ hbits ≤ cols + 1 ∧ cols + nhs ≤ 2 ^ 20

instance (cols nhs hbits : ℕ) : Decidable (LrSizes cols nhs hbits) := by
  unfold LrSizes; infer_instance

set_option maxRecDepth 100000 in
/-- Every entry of `lrTable` has its sizes, by the kernel. -/
theorem lrTable_sizes : ∀ e ∈ lrTable, LrSizes e.2.1 e.2.2.1 e.2.2.2.1 := by
  decide +kernel

/-- **Every entry of `lrTable` has its facts.** -/
theorem lrTable_facts : ∀ e ∈ lrTable,
    LrFacts e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2 := by
  intro e he
  obtain ⟨h1, h2, h3, h4, h5⟩ := lrTable_sizes e he
  exact ⟨h1, h2, h3, h4, lrLoop1_pure .., lrLoop2_pure .., h5⟩

/-! ## The statement -/

/-- `level_residual`'s chains' buffer: the batches' chains (`rcC`), then the rest's after their
first pair (`rsC`, from the batches' last pair). -/
def lrW (q cols nhs hbits : ℕ) (D : ℕ → E) (hsv : List E) (p : ℕ → E) (M : E) : List E :=
  (List.range (2 * (q / resBatch + q % resBatch + 1))).map fun e ↦
    if e < 2 * (q / resBatch + 1) then (rcC (lrRow q cols nhs hbits) D hsv p M).getD e 0
    else (rsC (lrRow q cols nhs hbits) D hsv p M (q / resBatch) (q % resBatch)).getD
      (e - 2 * (q / resBatch)) 0

theorem lrW_length (q cols nhs hbits : ℕ) (D : ℕ → E) (hsv : List E) (p : ℕ → E) (M : E) :
    (lrW q cols nhs hbits D hsv p M).length = 2 * (q / resBatch + q % resBatch + 1) := by
  simp [lrW]

theorem lrW_getD {q cols nhs hbits : ℕ} {D : ℕ → E} {hsv : List E} {p : ℕ → E} {M : E} {e : ℕ}
    (he : e < 2 * (q / resBatch + q % resBatch + 1)) :
    (lrW q cols nhs hbits D hsv p M).getD e 0 =
      if e < 2 * (q / resBatch + 1) then (rcC (lrRow q cols nhs hbits) D hsv p M).getD e 0
      else (rsC (lrRow q cols nhs hbits) D hsv p M (q / resBatch) (q % resBatch)).getD
        (e - 2 * (q / resBatch)) 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [lrW_length]; exact he)]
  simp [lrW]

/-- The buffer's pairs from `2·(q / resBatch)` on are the rest's chains. -/
theorem lrW_rs {q cols nhs hbits : ℕ} {D : ℕ → E} {hsv : List E} {p : ℕ → E} {M : E} {j : ℕ}
    (hj : j ≤ q % resBatch) :
    (lrW q cols nhs hbits D hsv p M).getD (2 * (q / resBatch) + 2 * j) 0 =
        (rsAt (lrRow q cols nhs hbits) D hsv p M (q / resBatch) j).1 ∧
      (lrW q cols nhs hbits D hsv p M).getD (2 * (q / resBatch) + 2 * j + 1) 0 =
        (rsAt (lrRow q cols nhs hbits) D hsv p M (q / resBatch) j).2 := by
  rw [lrW_getD (by omega), lrW_getD (by omega)]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [Nat.mul_zero, Nat.add_zero, show 2 * (q / resBatch) < 2 * (q / resBatch + 1) by omega,
      show 2 * (q / resBatch) + 1 < 2 * (q / resBatch + 1) by omega, ↓reduceIte]
    obtain ⟨g0, g1⟩ := rcC_get (lrRow q cols nhs hbits) D hsv p M (j := q / resBatch)
      (show q / resBatch ≤ q / resBatch from le_rfl)
    rw [g0, g1]
    exact ⟨rfl, rfl⟩
  · simp only [show ¬ 2 * (q / resBatch) + 2 * j < 2 * (q / resBatch + 1) by omega,
      show ¬ 2 * (q / resBatch) + 2 * j + 1 < 2 * (q / resBatch + 1) by omega, ↓reduceIte,
      show 2 * (q / resBatch) + 2 * j - 2 * (q / resBatch) = 2 * j by omega,
      show 2 * (q / resBatch) + 2 * j + 1 - 2 * (q / resBatch) = 2 * j + 1 by omega]
    exact rsC_get _ _ _ _ _ _ _ hj

/-- **What the rest's loop reads**: the buffer from `2·(q / resBatch)` on is `rsC`. -/
theorem lrW_rsC {q cols nhs hbits : ℕ} {D : ℕ → E} {hsv : List E} {p : ℕ → E} {M : E} {i : ℕ}
    (hi : i < 2 * (q % resBatch + 1)) :
    (lrW q cols nhs hbits D hsv p M).getD (2 * (q / resBatch) + i) 0 =
      (rsC (lrRow q cols nhs hbits) D hsv p M (q / resBatch) (q % resBatch)).getD i 0 := by
  have hi2 : i / 2 ≤ q % resBatch := by omega
  obtain ⟨w0, w1⟩ := lrW_rs (q := q) (cols := cols) (nhs := nhs) (hbits := hbits) (D := D) (hsv := hsv)
    (p := p) (M := M) hi2
  obtain ⟨r0, r1⟩ := rsC_get (lrRow q cols nhs hbits) D hsv p M (q / resBatch) (q % resBatch) hi2
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [show i = 2 * (i / 2) by omega, w0, r0]
  · rw [show i = 2 * (i / 2) + 1 by omega, ← Nat.add_assoc, w1, r1]

/-- **What the batches' loop reads**: the buffer's first `2·(q / resBatch + 1)` words are `rcC`. -/
theorem lrW_rcC {q cols nhs hbits : ℕ} {D : ℕ → E} {hsv : List E} {p : ℕ → E} {M : E} {i : ℕ}
    (hi : i < 2 * (q / resBatch + 1)) :
    (lrW q cols nhs hbits D hsv p M).getD i 0 = (rcC (lrRow q cols nhs hbits) D hsv p M).getD i 0 := by
  rw [lrW_getD (by omega)]
  simp [hi]

/-- `level_residual`'s buffer at `fp`. -/
def lrLb (fs : String → ℕ) (name : String) (q cols nhs hbits : ℕ) (D : ℕ → E) (hsv : List E)
    (p : ℕ → E) (M : E) (fp : ℕ) : Layout :=
  [(fp + fs name, lrW q cols nhs hbits D hsv p M)]

set_option maxHeartbeats 1600000 in
/-- **`level_residual` at `fp`, its buffer's words honest**: by its frame, its buffer and its
loops' trees of `m` words, on every memory holding the buffer and the caller's words. -/
theorem lr_key {name loop1 loop2 : String} {q cols nhs hbits : ℕ}
    (hlr : FnIs name (osParams 6) (lrBody loop1 loop2))
    (hl1 : FnIs loop1 (osParams 7) (lrLoop1Body cols nhs hbits loop1))
    (hl2 : FnIs loop2 (osParams 7) (lrLoop2Body cols nhs hbits loop2))
    (hF : LrFacts cols nhs hbits loop1 loop2) (hqb : resBatch ≤ q) (hq : q < ordG)
    (fs : String → ℕ) (cert : String → V → ℕ)
    (κ : ℕ) {Lin : Layout} {P BD HS M : E} {D p : ℕ → E} {hsv : List E} (hlen : hsv.length = nhs)
    (hreg : RegPtrs [(0, q), (1, cols), (2, nhs)]
      [P, BD, HS, M, gen ^ (q / resBatch), gen ^ (q % resBatch)] (RegionL Lin))
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      (∀ i < q, LoadHolds rd P i (p i)) ∧ (∀ s < cols, LoadHolds rd BD s (D s)) ∧
        ∀ c < nhs, LoadHolds rd HS c (hsv.getD c 0)) (fp : ℕ) :
    ∃ m, ∀ rd, LowDef κ rd → MemL rd (lrLb fs name q cols nhs hbits D hsv p M fp ++ Lin) →
      RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ ↦ False) fp
        (fs name + (lrSizes q).sum + m) name
        [P, BD, HS, M, gen ^ (q / resBatch), gen ^ (q % resBatch)]
        [(lrRet q cols nhs hbits D hsv p M).1, (lrRet q cols nhs hbits D hsv p M).2] := by
  obtain ⟨hc1, hn1, hb3, hbn, hp1, hp2, -⟩ := hF
  classical
  have hqd : resBatch * (q / resBatch) + (q % resBatch) = q := Nat.div_add_mod q resBatch
  have hO : ordG = 2 ^ 64 - 1 := rfl
  have hq8le : q / resBatch ≤ q := Nat.div_le_self _ _
  have hq8 : 0 < q / resBatch := Nat.div_pos hqb (by norm_num [resBatch])
  have h2B : 8 * (q / resBatch) ≤ q := Nat.mul_div_le q resBatch
  have hst : ResStatic (lrRow q cols nhs hbits) hsv := ⟨hc1, hn1, hb3, hbn, hlen,
    by show q / resBatch < u128Bound; simp only [u128Bound]; omega,
    by show 2 * (q / resBatch + 1) < 2 ^ 64 - 1; omega⟩
  set W := lrW q cols nhs hbits D hsv p M with hWd
  have hWl : W.length = 2 * (q / resBatch + q % resBatch + 1) := lrW_length ..
  have hsum : (lrSizes q).sum = W.length := by rw [hWl]; simp [lrSizes]
  set b := fp + fs name with hbd
  set Lb : Layout := [(b, W)] with hLb
  have hRb : ∀ i, RegionL Lb i → b ≤ i ∧ i < b + W.length := by
    rintro i ⟨e, he, h1, h2⟩
    simp only [hLb, List.mem_singleton] at he
    subst he; exact ⟨h1, h2⟩
  have hCHm : ∀ rd, MemL rd Lb → ReadsAt rd (ofK (addressOfIndex b)) W := fun rd h ↦
    h (b, W) List.mem_cons_self
  have hrcR : ∀ rd, MemL rd Lb →
      ReadsAt rd (ofK (addressOfIndex b)) (rcC (lrRow q cols nhs hbits) D hsv p M) := by
    intro rd h k hk
    have hk' : k < 2 * (q / resBatch + 1) := by rw [rcC_length] at hk; exact hk
    have := hCHm rd h k (by rw [hWl]; omega)
    rw [List.getElem_eq_getD 0, lrW_rcC hk', ← List.getElem_eq_getD 0] at this
    exact this
  have hrsR : ∀ rd, MemL rd Lb → ReadsAt rd (ofK (addressOfIndex (b + 2 * (q / resBatch))))
      (rsC (lrRow q cols nhs hbits) D hsv p M (q / resBatch) (q % resBatch)) := by
    intro rd h k hk
    have hk' : k < 2 * (q % resBatch + 1) := by rw [rsC_length] at hk; exact hk
    have := hCHm rd h (2 * (q / resBatch) + k) (by rw [hWl]; omega)
    rw [List.getElem_eq_getD 0, lrW_rsC hk', ← List.getElem_eq_getD 0,
      ← loadHolds_mul_gen_pow, lr_addr_mul] at this
    exact this
  obtain ⟨Lk, hLk⟩ : ∃ L, L = Lb ++ Lin := ⟨_, rfl⟩
  have hregK : ∀ i, RegionL Lk i → RegionL Lin i ∨ (b ≤ i ∧ i < b + W.length) := by
    rintro i ⟨e, he, h1, h2⟩
    rw [hLk] at he
    rcases List.mem_append.mp he with he | he
    · exact Or.inr (hRb i ⟨e, he, h1, h2⟩)
    · exact Or.inl ⟨e, he, h1, h2⟩
  have hLinK : ∀ i, RegionL Lin i → RegionL Lk i :=
    fun i ⟨e, he, h⟩ ↦ ⟨e, by rw [hLk]; exact List.mem_append_right _ he, h⟩
  have hLbK : ∀ i, RegionL Lb i → RegionL Lk i :=
    fun i ⟨e, he, h⟩ ↦ ⟨e, by rw [hLk]; exact List.mem_append_left _ he, h⟩
  -- the loops' words, on the restricted memory
  have hres : ∀ rd, LowDef κ rd → MemL rd Lk →
      (∀ i < q, LoadHolds (Main.restrict rd (RegionL Lk)) P i (p i)) ∧
      (∀ s < cols, LoadHolds (Main.restrict rd (RegionL Lk)) BD s (D s)) ∧
      (∀ c < nhs, LoadHolds (Main.restrict rd (RegionL Lk)) HS c (hsv.getD c 0)) ∧
      MemL (Main.restrict rd (RegionL Lk)) Lb := by
    intro rd hl hL
    rw [hLk] at hL
    obtain ⟨hLb', hLin'⟩ := Main.memL_append.mp hL
    obtain ⟨hP, hD, hH⟩ := hmem rd hl hLin'
    refine ⟨fun i hi ↦ Main.loadHolds_restrict (hP i hi) ?_,
      fun s hs ↦ Main.loadHolds_restrict (hD s hs) ?_,
      fun c hc ↦ Main.loadHolds_restrict (hH c hc) ?_, Main.memL_restrict hLb' hLbK⟩
    · obtain ⟨j, hj, hR⟩ := hreg (0, q) (by simp) i hi
      exact ⟨j, hj, hLinK j hR⟩
    · obtain ⟨j, hj, hR⟩ := hreg (1, cols) (by simp) s hs
      exact ⟨j, hj, hLinK j hR⟩
    · obtain ⟨j, hj, hR⟩ := hreg (2, nhs) (by simp) c hc
      exact ⟨j, hj, hLinK j hR⟩
  obtain ⟨m1, hm1⟩ := lr_guarded_uniform (lr_pureIn hl1 hp1) (List.mem_singleton_self _) fs cert
    (κ := κ) (Lk := Lk) (G := 1 + gen ^ (q / resBatch) ≠ 0)
    (args := [1, gen ^ (q / resBatch), P, ofK (addressOfIndex b), BD, HS, M])
    (fun hg rd hl hL ↦ by
      obtain ⟨hP, hD, hH, hB⟩ := hres rd hl hL
      exact lrLoop1_complete hl1 hst hq8 hP hD hH (hrcR _ hB) hg)
  obtain ⟨m2, hm2⟩ := lr_guarded_uniform (lr_pureIn hl2 hp2) (List.mem_singleton_self _) fs cert
    (κ := κ) (Lk := Lk) (G := 1 + gen ^ (q % resBatch) ≠ 0)
    (args := [1, gen ^ (q % resBatch), ofK (addressOfIndex (b + 2 * (q / resBatch))),
      P * gen ^ (resBatch * (q / resBatch)), BD, HS, M])
    (fun hg rd hl hL ↦ by
      obtain ⟨hP, hD, hH, hB⟩ := hres rd hl hL
      have hr0 : 0 < q % resBatch := by
        rcases Nat.eq_zero_or_pos (q % resBatch) with h0 | h0
        · exact absurd (by rw [h0, pow_zero, e_add_self]) hg
        · exact h0
      refine lrLoop2_complete hl2 hst (nb := q / resBatch) (Pos := p) hr0
        (fun k hk ↦ ?_) hD hH (hrsR _ hB) hg
      rw [loadHolds_mul_gen_pow]
      exact hP _ (by omega))
  -- the chains' ends
  have hret : lrRet q cols nhs hbits D hsv p M =
      (W.getD (2 * (q / resBatch) + 2 * (q % resBatch)) 0,
        W.getD (2 * (q / resBatch) + 2 * (q % resBatch) + 1) 0) := by
    obtain ⟨g0, g1⟩ := lrW_rs (q := q) (cols := cols) (nhs := nhs) (hbits := hbits) (D := D)
      (hsv := hsv) (p := p) (M := M) (j := q % resBatch) le_rfl
    rw [hWd, g0, g1]
    show _ = rsAt (lrRow q cols nhs hbits) D hsv p M (q / resBatch) (q % resBatch)
    unfold rsAt lrRet
    rw [hqd]
    rfl
  have hz : W.getD 0 0 = 0 ∧ W.getD 1 0 = 0 := by
    obtain ⟨g0, g1⟩ := rcC_get (lrRow q cols nhs hbits) D hsv p M (j := 0) (Nat.zero_le _)
    rw [hWd, lrW_rcC (by omega), lrW_rcC (by omega), show 1 = 2 * 0 + 1 from rfl, g0, g1]
    exact ⟨rfl, rfl⟩
  refine ⟨m1 + m2, fun rd hl hL ↦ ?_⟩
  have hL' : MemL rd Lk := by rw [hLk]; exact hL
  have hB := (Main.memL_append.mp hL).1
  rw [hret, hsum]
  exact lr_relAtIn hlr hq fs cert (hCHm rd hB) hWl hz.1 hz.2 (hm1 _ rd hl hL') (hm2 _ rd hl hL')
    hregK hregK

/-- **`level_residual` at an entry is `LrAtD`.** -/
theorem lrAtD_of {name loop1 loop2 : String} {cols nhs hbits : ℕ}
    (hlr : FnIs name (osParams 6) (lrBody loop1 loop2))
    (hl1 : FnIs loop1 (osParams 7) (lrLoop1Body cols nhs hbits loop1))
    (hl2 : FnIs loop2 (osParams 7) (lrLoop2Body cols nhs hbits loop2))
    (hF : LrFacts cols nhs hbits loop1 loop2) (fs : String → ℕ) (cert : String → V → ℕ)
    (κ : ℕ) : LrAtD fs cert κ name cols nhs hbits := by
  intro q hqb hq Lin P BD HS M D p hsv hlen hreg hmem fp
  obtain ⟨m, hm⟩ := lr_key hlr hl1 hl2 hF hqb hq fs cert κ hlen hreg hmem fp
  have hl : (lrSizes q).sum = (lrW q cols nhs hbits D hsv p M).length := by
    rw [lrW_length]; simp [lrSizes]
  refine ⟨fs name + (lrSizes q).sum + m, lrLb fs name q cols nhs hbits D hsv p M fp, _, [],
    ⟨rfl, rfl⟩, ?_, by simp [lrLb, DisjL],
    fun rd hl hL ↦ relAtIn_dmono (hm rd hl (by simpa using hL)) (fun i hi ↦ ?_)⟩
  · intro e he
    simp only [lrLb, List.nil_append, List.mem_singleton] at he
    subst he
    simp only
    omega
  · obtain ⟨e, he, _⟩ := hi; simp at he

/-- **`level_residual` is complete placed at every specialization.** -/
theorem level_residual_completeAt : level_residual_completeAt_Spec := by
  intro fs cert κ _ _ _ e he
  obtain ⟨hlr, hl1, hl2⟩ := lrTable_ok e he
  exact lrAtD_of hlr hl1 hl2 (lrTable_facts e he) fs cert κ

end
end LeanVM.Guest.B1
