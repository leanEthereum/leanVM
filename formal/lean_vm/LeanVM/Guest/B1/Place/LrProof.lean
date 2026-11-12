/-
  LeanVM.Guest.B1.Place.LrProof

  `level_residual` is complete placed at every specialization of `lrTable`.
-/

module

public import LeanVM.Guest.B1.Place.Lr
public import LeanVM.Guest.B1.Place.LrLoops
public import LeanVM.Guest.B1.Place.LpProof
public import LeanVM.Guest.Memory.Retemp
public import LeanVM.Guest.Memory.Restrict

/-!
# `level_residual`, placed

`level_residual` at `fp` allocates its batches' chains (`2(q/8 + 1)` words, `rcC`) at
`fp + fs name` and, when `8 ∤ q`, the rest's chains (`2(q % 8 + 1)` words, `rsC`) right after
them; its loops, which place nothing, are placed after its buffers by trees of one size on every
memory holding its words (`relAtIn_pure_uniform`, `guarded_uniform`).

* `lr_relAtIn0`, `lr_relAtIn1`: the body at `fp`, `8 ∣ q` and `8 ∤ q`, its loops' trees given.
* `lr_loop1_rel`, `lr_loop2_rel`: the loops' relations on the honest buffers (`Place/LrLoops`).
* `lrAtD_of`, `level_residual_completeAt`: `LrAtD` at every entry of `lrTable`, from its decided
  facts (`LrFacts`).
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

/-- The sizes of `level_residual`'s buffers at `q` queries. -/
def lrSizes (q : ℕ) : List ℕ :=
  if q % resBatch = 0 then [2 * (q / resBatch + 1)]
  else [2 * (q / resBatch + 1), 2 * (q % resBatch + 1)]

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
      else m = fs f)
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
    {pre : List Stmt} {vs : List V} (hv : vs ≠ []) (hb : fn.body = pre ++ [.ret vs]) :
    coreProgram.loop name = false := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hv
  rw [Program.loop_of_find? hf, Fn.loop, hb]
  simp [List.reverse_append]

/-! ## The body, placed -/

set_option maxHeartbeats 1600000 in
/-- **`level_residual`, `8 ∣ q`, placed** at `fp`: its chains `CH` at `fp + fs name`, its loop's
tree of `m1` words after them. -/
theorem lr_relAtIn0 {name loop1 loop2 : String} {q : ℕ}
    (hlr : FnIs name (osParams 4) (lrBody q loop1 loop2)) (hq : 2 * q + 2 < 2 ^ 64 - 1)
    (h0 : q % resBatch = 0) (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader}
    {R Rk1 : ℕ → Prop} {fp m1 : ℕ} {P BD HS M : E} {CH : List E}
    (hCH : ReadsAt rd (ofK (addressOfIndex (fp + fs name))) CH)
    (hCl : CH.length = 2 * (q / resBatch + 1)) (hz0 : CH.getD 0 0 = 0) (hz1 : CH.getD 1 0 = 0)
    (hL1 : if 1 + gen ^ (q / resBatch) ≠ 0 then
      RelAtIn coreProgram fs cert rd Rk1 (fun _ ↦ False) (fp + fs name + (lrSizes q).sum) m1 loop1
        [1, gen ^ (q / resBatch), P, ofK (addressOfIndex (fp + fs name)), BD, HS, M] []
      else m1 = fs loop1)
    (hRk1 : ∀ i, Rk1 i → R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (lrSizes q).sum)) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp (fs name + (lrSizes q).sum + m1) name
      [P, BD, HS, M] [CH.getD (2 * (q / resBatch)) 0, CH.getD (2 * (q / resBatch) + 1) 0] := by
  obtain ⟨fn, hf, hps, hb⟩ := hlr
  set q8 := q / resBatch with hq8
  have hq8le : q8 ≤ q := Nat.div_le_self _ _
  have h8 : q8 < u128Bound := by simp only [u128Bound]; omega
  have h0u : 0 < u128Bound := by simp only [u128Bound]; omega
  have h81 : 2 * (q8 + 1) < u128Bound := by simp only [u128Bound]; omega
  have hS : lrSizes q = [2 * (q8 + 1)] := by simp [lrSizes, h0, hq8]
  set pre : List Stmt := osHeap (2 * (q8 + 1)) 4 ++
      [osCst 6 (word 0 0), osLd 6 5 0, osCst 7 (word 0 0), osLd 7 5 1] ++
      osLoopCall loop1 0 q8 [0, 5, 1, 2, 3] 8 ++ [osLd 13 5 (2 * q8), osLd 14 5 (2 * q8 + 1)] ++
      [osCp 15 13, osCp 16 14] with hpre
  have hb' : fn.body = pre ++ [.ret [.n 15, .n 16]] := by
    rw [hb, lrBody]
    simp only [h0, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append, hq8, hpre]
  have hstr : pre.all Main.Stmt.straight = true := by
    simp [hpre, osHeap, osLoopCall, Main.Stmt.straight]
  set b := fp + fs name with hbd
  set A0 := CH.getD (2 * q8) 0
  set A1 := CH.getD (2 * q8 + 1) 0
  set vals := [P, BD, HS, M, gw (2 * (q8 + 1)), ofK (addressOfIndex b), word 0 0, word 0 0, gw 0, gw q8,
    gw 0 + gw q8, gw 0, gw q8, A0, A1, A0, A1] with hvals
  set σ := lrVal vals with hσ
  have hld : ∀ e < CH.length, LoadHolds rd (ofK (addressOfIndex b)) e (CH.getD e 0) := fun e he ↦ by
    rw [List.getD_eq_getElem _ _ he]; exact hCH e he
  have hok : Whir.AllOk (fun _ _ _ ↦ True) rd σ pre := by
    simp only [hpre, osHeap, osLoopCall, osCst, osLd, osCp, osAdd, List.cons_append,
      List.nil_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds,
      List.map_cons, List.map_nil, lrVal_n, hσ]
    simp only [hvals, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, true_and, and_true, implies_true]
    rw [Whir.gw_eq h8, Whir.gw_eq h0u, pow_zero]
    refine ⟨?_, ?_, isInK_one_add_gen_pow q8, ?_, ?_⟩
    · have := hld 0 (by rw [hCl]; exact lr_zero_lt _); rwa [hz0, ← word_zero] at this
    · have := hld 1 (by rw [hCl]; exact lr_one_lt _); rwa [hz1, ← word_zero] at this
    · exact hld _ (by omega)
    · exact hld _ (by omega)
  have hw := Main.walk_straight σ [.n 15, .n 16] pre hstr
  rw [← hb'] at hw
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ pre hstr
  have hal : pre.filterMap Main.Stmt.allocSz = [(.n 5, .inr (.n 4))] := rfl
  have e4 : σ (.n 4) = gw (2 * (q8 + 1)) := rfl
  have e5 : σ (.n 5) = ofK (addressOfIndex b) := rfl
  have e10 : σ (.n 10) = 1 + gen ^ q8 := by
    show gw 0 + gw q8 = _; rw [Whir.gw_eq h8, Whir.gw_eq h0u, pow_zero]
  set es := pre.flatMap (Main.slEvs σ) with hes
  have hallocs : allocs σ es = [2 * (q8 + 1)] := by
    rw [i2, hal]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, e4]
    rw [Whir.gw_eq h81, gen_pow_eq_ofK, logG_spec (by omega)]
  have hcalls : calls es = [⟨loop1, [.n 11, .n 12, .n 0, .n 5, .n 1, .n 2, .n 3], [],
      decide (σ (.n 10) ≠ 0)⟩] := by
    rw [i4, show pre.filterMap Main.Stmt.callS =
      [(some (.n 10), loop1, [.n 11, .n 12, .n 0, .n 5, .n 1, .n 2, .n 3], [])] from rfl]
    rfl
  have hown : ∀ i, b ≤ i → i < b + 2 * (q8 + 1) →
      ownData cert fp (fp + fs name) name (allocs σ es) es i :=
    fun i h1 h2 ↦ Or.inl ⟨(2 * (q8 + 1), b), by rw [hallocs]; simp [bases, b], h1, h2⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    coreProgram_wf (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp) (N := m1 + 0)
    (args := [P, BD, HS, M]) (rets := [A0, A1])
    hf (Or.inl (lr_notLoop hf (by simp) hb')) (by rw [hps]; rfl) hw
    (by simp [hσ, lrVal_n, hvals]) (lr_slEvs_holds (lr_slOk_of_allOk hok))
    (by rw [i1, hal, hallocs]; simp [bases, e5, b])
    (fun q' hq' ↦ by
      rw [i3, show pre.filterMap Main.Stmt.addrS = [] from rfl] at hq'
      simp at hq')
    ?_ (fun A hA ↦ ?_) (fun _ h ↦ h.elim)
  · rw [hallocs] at h
    simpa [hS] using h
  · have hsum : (allocs σ es).sum = (lrSizes q).sum := by rw [hallocs, hS]
    rw [hcalls, hsum]
    have hargs : ([.n 11, .n 12, .n 0, .n 5, .n 1, .n 2, .n 3] : List V).map σ =
        [1, gen ^ q8, P, ofK (addressOfIndex b), BD, HS, M] := by
      simp only [List.map_cons, List.map_nil, hσ, lrVal_n, hvals, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [Whir.gw_eq h8, Whir.gw_eq h0u, pow_zero]
    refine kidsFromIn_loopCall (Rk := Rk1) (fun i hi ↦ ?_) ?_ fun _ ↦ lr_kidsFromIn_nil
    · rcases hRk1 i hi with h | h
      · exact Or.inl h
      · rw [hS] at h; exact Or.inr (hown i h.1 (by simpa using h.2))
    · rw [hargs, e10]; exact hL1
  · rw [B1.loadAddrs_straight σ pre hstr] at hA
    have hl : pre.filterMap B1.Stmt.loadS =
        [(.n 5, 0), (.n 5, 1), (.n 5, 2 * q8), (.n 5, 2 * q8 + 1)] := rfl
    rw [hl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have hw' : ∀ t < 2 * (q8 + 1), ∃ j, (σ (.n 5)).limb 0 * addressOfIndex t = addressOfIndex j ∧
        (ownData cert fp (fp + fs name) name (allocs σ es) es j ∨ R j ∨ False) :=
      fun t ht ↦ ⟨b + t, by rw [e5, Main.addr_ofK], Or.inl (hown _ (by omega) (by omega))⟩
    rcases hA with rfl | rfl | rfl | rfl
    · exact hw' 0 (lr_zero_lt _)
    · exact hw' 1 (lr_one_lt _)
    · exact hw' _ (by omega)
    · exact hw' _ (by omega)

set_option maxHeartbeats 1600000 in
/-- **`level_residual`, `8 ∤ q`, placed** at `fp`: its chains `CH` at `fp + fs name`, the rest's
`RS` right after them, its loops' trees of `m1` and `m2` words after those. -/
theorem lr_relAtIn1 {name loop1 loop2 : String} {q : ℕ}
    (hlr : FnIs name (osParams 4) (lrBody q loop1 loop2)) (hq : 2 * q + 2 < 2 ^ 64 - 1)
    (h0 : q % resBatch ≠ 0) (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader}
    {R Rk1 Rk2 : ℕ → Prop} {fp m1 m2 : ℕ} {P BD HS M : E} {CH RS : List E}
    (hCH : ReadsAt rd (ofK (addressOfIndex (fp + fs name))) CH)
    (hCl : CH.length = 2 * (q / resBatch + 1)) (hz0 : CH.getD 0 0 = 0) (hz1 : CH.getD 1 0 = 0)
    (hRS : ReadsAt rd (ofK (addressOfIndex (fp + fs name + 2 * (q / resBatch + 1)))) RS)
    (hRl : RS.length = 2 * (q % resBatch + 1))
    (hr0 : RS.getD 0 0 = CH.getD (2 * (q / resBatch)) 0)
    (hr1 : RS.getD 1 0 = CH.getD (2 * (q / resBatch) + 1) 0)
    (hL1 : if 1 + gen ^ (q / resBatch) ≠ 0 then
      RelAtIn coreProgram fs cert rd Rk1 (fun _ ↦ False) (fp + fs name + (lrSizes q).sum) m1 loop1
        [1, gen ^ (q / resBatch), P, ofK (addressOfIndex (fp + fs name)), BD, HS, M] []
      else m1 = fs loop1)
    (hL2 : if 1 + gen ^ (q % resBatch) ≠ 0 then
      RelAtIn coreProgram fs cert rd Rk2 (fun _ ↦ False) (fp + fs name + (lrSizes q).sum + m1) m2
        loop2 [1, gen ^ (q % resBatch),
          ofK (addressOfIndex (fp + fs name + 2 * (q / resBatch + 1))),
          P * gen ^ (resBatch * (q / resBatch)), BD, HS, M] []
      else m2 = fs loop2)
    (hRk1 : ∀ i, Rk1 i → R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (lrSizes q).sum))
    (hRk2 : ∀ i, Rk2 i → R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (lrSizes q).sum)) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp (fs name + (lrSizes q).sum + (m1 + m2))
      name [P, BD, HS, M] [RS.getD (2 * (q % resBatch)) 0, RS.getD (2 * (q % resBatch) + 1) 0] := by
  obtain ⟨fn, hf, hps, hb⟩ := hlr
  set q8 := q / resBatch with hq8
  set r := q % resBatch with hr
  have hqd : resBatch * q8 + r = q := Nat.div_add_mod q resBatch
  have hq8le : q8 ≤ q := Nat.div_le_self _ _
  have hrle : r ≤ q := Nat.mod_le _ _
  have h8 : q8 < u128Bound := by simp only [u128Bound]; omega
  have h0u : 0 < u128Bound := by simp only [u128Bound]; omega
  have h81 : 2 * (q8 + 1) < u128Bound := by simp only [u128Bound]; omega
  have hr8 : r < u128Bound := by simp only [u128Bound]; omega
  have hrb1 : 2 * (r + 1) < u128Bound := by simp only [u128Bound]; omega
  have hb8 : resBatch * q8 < u128Bound := by simp only [u128Bound]; omega
  have h0' : ¬ q % resBatch = 0 := h0
  have hS : lrSizes q = [2 * (q8 + 1), 2 * (r + 1)] := by simp only [lrSizes, h0', ↓reduceIte, hq8, hr]
  set pre : List Stmt := osHeap (2 * (q8 + 1)) 4 ++
      [osCst 6 (word 0 0), osLd 6 5 0, osCst 7 (word 0 0), osLd 7 5 1] ++
      osLoopCall loop1 0 q8 [0, 5, 1, 2, 3] 8 ++ [osLd 13 5 (2 * q8), osLd 14 5 (2 * q8 + 1)] ++
      (osHeap (2 * (r + 1)) 15 ++
        [osLd 13 16 0, osLd 14 16 1, osCst 17 (gw (resBatch * q8)), osMul 18 0 17] ++
        osLoopCall loop2 0 r [16, 18, 1, 2, 3] 19 ++
        [osLd 24 16 (2 * r), osLd 25 16 (2 * r + 1), osCp 26 24, osCp 27 25]) with hpre
  have hb' : fn.body = pre ++ [.ret [.n 26, .n 27]] := by
    rw [hb, lrBody]
    simp only [h0', ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append, hq8, hr, hpre]
  have hstr : pre.all Main.Stmt.straight = true := by
    simp [hpre, osHeap, osLoopCall, Main.Stmt.straight]
  set b := fp + fs name with hbd
  set b' := fp + fs name + 2 * (q8 + 1) with hbd'
  set A0 := CH.getD (2 * q8) 0
  set A1 := CH.getD (2 * q8 + 1) 0
  set RB0 := RS.getD (2 * r) 0
  set RB1 := RS.getD (2 * r + 1) 0
  set vals := [P, BD, HS, M, gw (2 * (q8 + 1)), ofK (addressOfIndex b), word 0 0, word 0 0, gw 0,
    gw q8, gw 0 + gw q8, gw 0, gw q8, A0, A1, gw (2 * (r + 1)), ofK (addressOfIndex b'),
    gw (resBatch * q8), P * gw (resBatch * q8), gw 0, gw r, gw 0 + gw r, gw 0, gw r, RB0, RB1, RB0,
    RB1] with hvals
  set σ := lrVal vals with hσ
  have hld : ∀ e < CH.length, LoadHolds rd (ofK (addressOfIndex b)) e (CH.getD e 0) := fun e he ↦ by
    rw [List.getD_eq_getElem _ _ he]; exact hCH e he
  have hldR : ∀ e < RS.length, LoadHolds rd (ofK (addressOfIndex b')) e (RS.getD e 0) := fun e he ↦ by
    rw [List.getD_eq_getElem _ _ he]; exact hRS e he
  have hok : Whir.AllOk (fun _ _ _ ↦ True) rd σ pre := by
    simp only [hpre, osHeap, osLoopCall, osCst, osLd, osCp, osAdd, osMul, List.cons_append,
      List.nil_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds,
      List.map_cons, List.map_nil, lrVal_n, hσ]
    simp only [hvals, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, true_and, and_true, implies_true]
    rw [Whir.gw_eq h8, Whir.gw_eq h0u, Whir.gw_eq hr8, pow_zero]
    refine ⟨?_, ?_, isInK_one_add_gen_pow q8, ?_, ?_, ?_, ?_, isInK_one_add_gen_pow r, ?_, ?_⟩
    · have := hld 0 (by rw [hCl]; exact lr_zero_lt _); rwa [hz0, ← word_zero] at this
    · have := hld 1 (by rw [hCl]; exact lr_one_lt _); rwa [hz1, ← word_zero] at this
    · exact hld _ (by omega)
    · exact hld _ (by omega)
    · have := hldR 0 (by rw [hRl]; exact lr_zero_lt _); rwa [hr0] at this
    · have := hldR 1 (by rw [hRl]; exact lr_one_lt _); rwa [hr1] at this
    · exact hldR _ (by omega)
    · exact hldR _ (by omega)
  have hw := Main.walk_straight σ [.n 26, .n 27] pre hstr
  rw [← hb'] at hw
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ pre hstr
  have hal : pre.filterMap Main.Stmt.allocSz = [(.n 5, .inr (.n 4)), (.n 16, .inr (.n 15))] := rfl
  have e4 : σ (.n 4) = gw (2 * (q8 + 1)) := rfl
  have e5 : σ (.n 5) = ofK (addressOfIndex b) := rfl
  have e15 : σ (.n 15) = gw (2 * (r + 1)) := rfl
  have e16 : σ (.n 16) = ofK (addressOfIndex b') := rfl
  have e10 : σ (.n 10) = 1 + gen ^ q8 := by
    show gw 0 + gw q8 = _; rw [Whir.gw_eq h8, Whir.gw_eq h0u, pow_zero]
  have e21 : σ (.n 21) = 1 + gen ^ r := by
    show gw 0 + gw r = _; rw [Whir.gw_eq hr8, Whir.gw_eq h0u, pow_zero]
  set es := pre.flatMap (Main.slEvs σ) with hes
  have hallocs : allocs σ es = [2 * (q8 + 1), 2 * (r + 1)] := by
    rw [i2, hal]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, e4, e15]
    rw [Whir.gw_eq h81, Whir.gw_eq hrb1, gen_pow_eq_ofK, gen_pow_eq_ofK, logG_spec (by omega),
      logG_spec (by omega)]
  have hcalls : calls es = [⟨loop1, [.n 11, .n 12, .n 0, .n 5, .n 1, .n 2, .n 3], [],
      decide (σ (.n 10) ≠ 0)⟩, ⟨loop2, [.n 22, .n 23, .n 16, .n 18, .n 1, .n 2, .n 3], [],
      decide (σ (.n 21) ≠ 0)⟩] := by
    rw [i4, show pre.filterMap Main.Stmt.callS =
      [(some (.n 10), loop1, [.n 11, .n 12, .n 0, .n 5, .n 1, .n 2, .n 3], []),
        (some (.n 21), loop2, [.n 22, .n 23, .n 16, .n 18, .n 1, .n 2, .n 3], [])] from rfl]
    rfl
  have hown : ∀ i, b ≤ i → i < b + (2 * (q8 + 1) + 2 * (r + 1)) →
      ownData cert fp (fp + fs name) name (allocs σ es) es i := by
    intro i h1 h2
    rw [hallocs]
    by_cases hi : i < b + 2 * (q8 + 1)
    · exact Or.inl ⟨(2 * (q8 + 1), b), by simp [bases, b], h1, hi⟩
    · exact Or.inl ⟨(2 * (r + 1), b'), by simp [bases, b'], by omega, by omega⟩
  have hsum : (lrSizes q).sum = 2 * (q8 + 1) + 2 * (r + 1) := by rw [hS]; simp
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    coreProgram_wf (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp)
    (N := m1 + (m2 + 0)) (args := [P, BD, HS, M]) (rets := [RB0, RB1])
    hf (Or.inl (lr_notLoop hf (by simp) hb')) (by rw [hps]; rfl) hw
    (by simp [hσ, lrVal_n, hvals]) (lr_slEvs_holds (lr_slOk_of_allOk hok))
    (by rw [i1, hal, hallocs]; simp [bases, e5, e16, b, b'])
    (fun q' hq' ↦ by
      rw [i3, show pre.filterMap Main.Stmt.addrS = [] from rfl] at hq'
      simp at hq')
    ?_ (fun A hA ↦ ?_) (fun _ h ↦ h.elim)
  · rw [hallocs] at h
    simpa [hS, Nat.add_assoc] using h
  · have hsum' : (allocs σ es).sum = (lrSizes q).sum := by rw [hallocs, hS]
    rw [hcalls, hsum']
    have hargs1 : ([.n 11, .n 12, .n 0, .n 5, .n 1, .n 2, .n 3] : List V).map σ =
        [1, gen ^ q8, P, ofK (addressOfIndex b), BD, HS, M] := by
      simp only [List.map_cons, List.map_nil, hσ, lrVal_n, hvals, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [Whir.gw_eq h8, Whir.gw_eq h0u, pow_zero]
    have hargs2 : ([.n 22, .n 23, .n 16, .n 18, .n 1, .n 2, .n 3] : List V).map σ =
        [1, gen ^ r, ofK (addressOfIndex b'), P * gen ^ (resBatch * q8), BD, HS, M] := by
      simp only [List.map_cons, List.map_nil, hσ, lrVal_n, hvals, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [Whir.gw_eq hr8, Whir.gw_eq h0u, Whir.gw_eq hb8, pow_zero]
    have hreg : ∀ Rk : ℕ → Prop, (∀ i, Rk i → R i ∨ (b ≤ i ∧ i < b + (lrSizes q).sum)) →
        ∀ i, Rk i → R i ∨ ownData cert fp (fp + fs name) name (allocs σ es) es i := by
      intro Rk hRk i hi
      rcases hRk i hi with h | h
      · exact Or.inl h
      · rw [hsum] at h; exact Or.inr (hown i h.1 h.2)
    refine kidsFromIn_loopCall (Rk := Rk1) (hreg Rk1 hRk1) (by rw [hargs1, e10]; exact hL1)
      fun _ ↦ kidsFromIn_loopCall (Rk := Rk2) (hreg Rk2 hRk2) (by rw [hargs2, e21]; exact hL2)
        fun _ ↦ lr_kidsFromIn_nil
  · rw [B1.loadAddrs_straight σ pre hstr] at hA
    have hl : pre.filterMap B1.Stmt.loadS = [(.n 5, 0), (.n 5, 1), (.n 5, 2 * q8),
        (.n 5, 2 * q8 + 1), (.n 16, 0), (.n 16, 1), (.n 16, 2 * r), (.n 16, 2 * r + 1)] := rfl
    rw [hl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have hw1 : ∀ t < 2 * (q8 + 1), ∃ j, (σ (.n 5)).limb 0 * addressOfIndex t = addressOfIndex j ∧
        (ownData cert fp (fp + fs name) name (allocs σ es) es j ∨ R j ∨ False) :=
      fun t ht ↦ ⟨b + t, by rw [e5, Main.addr_ofK], Or.inl (hown _ (by omega) (by omega))⟩
    have hw2 : ∀ t < 2 * (r + 1), ∃ j, (σ (.n 16)).limb 0 * addressOfIndex t = addressOfIndex j ∧
        (ownData cert fp (fp + fs name) name (allocs σ es) es j ∨ R j ∨ False) :=
      fun t ht ↦ ⟨b' + t, by rw [e16, Main.addr_ofK], Or.inl (hown _ (by omega) (by omega))⟩
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw1 0 (lr_zero_lt _)
    · exact hw1 1 (lr_one_lt _)
    · exact hw1 _ (by omega)
    · exact hw1 _ (by omega)
    · exact hw2 0 (lr_zero_lt _)
    · exact hw2 1 (lr_one_lt _)
    · exact hw2 _ (by omega)
    · exact hw2 _ (by omega)

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
      RelAtIn coreProgram fs cert rd (RegionL Lk) (fun _ ↦ False) fp' m g args [] else m = fs g := by
  by_cases hG : G
  · obtain ⟨n, hn⟩ := lr_relAtIn_pure_uniform hS hg fs cert (h hG)
    exact ⟨n, fun fp' rd hl hL ↦ by simp only [hG, ↓reduceIte]; exact hn fp' rd hl hL⟩
  · exact ⟨fs g, fun _ _ _ _ ↦ by simp only [hG, ↓reduceIte]⟩

theorem lr_pureIn {loop : String} {body : List Stmt} (hl : FnIs loop (osParams 7) body)
    (hp : Stmt.pureList [loop] body = true) : coreProgram.PureIn [loop] := by
  intro g hg fn hf
  obtain ⟨fl, hfl, -, hbl⟩ := hl
  rw [List.mem_singleton] at hg
  subst hg
  rw [hfl] at hf; cases hf; rw [hbl]; exact hp

/-! ## The decided facts -/

/-- An entry's static facts: its row's (`ResStatic`), its sizes in range, a batch, its loops
placing nothing, and its words few. -/
def LrFacts (q cols nhs hbits : ℕ) (l1 l2 : String) : Prop :=
  1 ≤ cols ∧ 1 ≤ nhs ∧ hbits ≤ 3 ∧ hbits ≤ cols + 1 ∧ 0 < q / resBatch ∧
    2 * q + 2 < 2 ^ 64 - 1 ∧ Stmt.pureList [l1] (lrLoop1Body cols nhs hbits l1) = true ∧
    (q % resBatch ≠ 0 → Stmt.pureList [l2] (lrLoop2Body cols nhs hbits l2) = true) ∧
    q + cols + nhs ≤ 2 ^ 20

instance (q cols nhs hbits : ℕ) (l1 l2 : String) : Decidable (LrFacts q cols nhs hbits l1 l2) := by
  unfold LrFacts; infer_instance

set_option maxRecDepth 100000 in
/-- **Every entry of `lrTable` has its facts**, by the kernel. -/
theorem lrTable_facts : ∀ e ∈ lrTable,
    LrFacts e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2 := by
  decide +kernel

/-! ## The statement -/

/-- `level_residual`'s chains' buffers' words: the batches', and the rest's when `8 ∤ q`. -/
def lrWords (q cols nhs hbits : ℕ) (D : ℕ → E) (hsv : List E) (p : ℕ → E) (M : E) :
    List (List E) :=
  if q % resBatch = 0 then [rcC (lrRow q cols nhs hbits) D hsv p M]
  else [rcC (lrRow q cols nhs hbits) D hsv p M,
    rsC (lrRow q cols nhs hbits) D hsv p M (q / resBatch) (q % resBatch)]

/-- `level_residual`'s buffers at `fp`. -/
def lrLb (fs : String → ℕ) (name : String) (q cols nhs hbits : ℕ) (D : ℕ → E) (hsv : List E)
    (p : ℕ → E) (M : E) (fp : ℕ) : Layout :=
  bufL (fp + fs name) (lrSizes q) (lrWords q cols nhs hbits D hsv p M)

theorem lrWords_fit (q cols nhs hbits : ℕ) (D : ℕ → E) (hsv : List E) (p : ℕ → E) (M : E) :
    List.Forall₂ (fun c s ↦ c.length ≤ s) (lrWords q cols nhs hbits D hsv p M) (lrSizes q) := by
  by_cases h0 : q % resBatch = 0
  · simp only [lrWords, lrSizes, h0, ↓reduceIte]
    exact .cons (le_of_eq (by rw [rcC_length]; rfl)) .nil
  · simp only [lrWords, lrSizes, h0, ↓reduceIte]
    exact .cons (le_of_eq (by rw [rcC_length]; rfl)) (.cons (le_of_eq (by rw [rsC_length])) .nil)

set_option maxHeartbeats 1600000 in
/-- **`level_residual` at `fp`, its buffers' words honest**: by its frame, its buffers and its
loops' trees of `m` words, on every memory holding the buffers and the caller's words. -/
theorem lr_key {name loop1 loop2 : String} {q cols nhs hbits : ℕ}
    (hlr : FnIs name (osParams 4) (lrBody q loop1 loop2))
    (hl1 : FnIs loop1 (osParams 7) (lrLoop1Body cols nhs hbits loop1))
    (hl2 : q % resBatch ≠ 0 → FnIs loop2 (osParams 7) (lrLoop2Body cols nhs hbits loop2))
    (hF : LrFacts q cols nhs hbits loop1 loop2) (fs : String → ℕ) (cert : String → V → ℕ)
    (κ : ℕ) {Lin : Layout} {P BD HS M : E} {D p : ℕ → E} {hsv : List E} (hlen : hsv.length = nhs)
    (hreg : RegPtrs [(0, q), (1, cols), (2, nhs)] [P, BD, HS, M] (RegionL Lin))
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      (∀ i < q, LoadHolds rd P i (p i)) ∧ (∀ s < cols, LoadHolds rd BD s (D s)) ∧
        ∀ c < nhs, LoadHolds rd HS c (hsv.getD c 0)) (fp : ℕ) :
    ∃ m, ∀ rd, LowDef κ rd → MemL rd (lrLb fs name q cols nhs hbits D hsv p M fp ++ Lin) →
      RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ ↦ False) fp
        (fs name + (lrSizes q).sum + m) name [P, BD, HS, M]
        [(lrRet q cols nhs hbits D hsv p M).1, (lrRet q cols nhs hbits D hsv p M).2] := by
  obtain ⟨hc1, hn1, hb3, hbn, hq8, hq64, hp1, hp2, -⟩ := hF
  classical
  have hqd : resBatch * (q / resBatch) + (q % resBatch) = q := Nat.div_add_mod q resBatch
  have hq : 2 * q + 2 < 2 ^ 64 - 1 := hq64
  have hq8le : q / resBatch ≤ q := Nat.div_le_self _ _
  have hst : ResStatic (lrRow q cols nhs hbits) hsv := ⟨hc1, hn1, hb3, hbn, hlen,
    by show q / resBatch < u128Bound; simp only [u128Bound]; omega,
    by show 2 * (q / resBatch + 1) < 2 ^ 64 - 1; omega⟩
  obtain ⟨CHw, hCHw⟩ : ∃ w, w = rcC (lrRow q cols nhs hbits) D hsv p M := ⟨_, rfl⟩
  obtain ⟨RSw, hRSw⟩ : ∃ w, w = rsC (lrRow q cols nhs hbits) D hsv p M (q / resBatch) (q % resBatch) :=
    ⟨_, rfl⟩
  obtain ⟨words, hwords⟩ : ∃ w : List (List E), w = if (q % resBatch) = 0 then [CHw] else [CHw, RSw] :=
    ⟨_, rfl⟩
  have hwf : List.Forall₂ (fun c s ↦ c.length ≤ s) words (lrSizes q) := by
    by_cases h0 : (q % resBatch) = 0
    · simp only [hwords, lrSizes, h0, ↓reduceIte]
      exact .cons (le_of_eq (by rw [hCHw, rcC_length]; rfl)) .nil
    · simp only [hwords, lrSizes, h0, ↓reduceIte]
      exact .cons (le_of_eq (by rw [hCHw, rcC_length]; rfl))
        (.cons (le_of_eq (by rw [hRSw, rsC_length])) .nil)
  obtain ⟨Lb, hLb⟩ : ∃ L, L = bufL (fp + fs name) (lrSizes q) words := ⟨_, rfl⟩
  have hWb : Within Lb (fp + fs name) (lrSizes q).sum := by rw [hLb]; exact bufL_within _ _ _ hwf
  have hDb : DisjL Lb := by rw [hLb]; exact bufL_disj _ _ _ hwf
  have hRb : ∀ i, RegionL Lb i → fp + fs name ≤ i ∧ i < fp + fs name + (lrSizes q).sum := by
    rintro i ⟨e, he, h1, h2⟩
    have := hWb e he; omega
  have hLbE : Lb = if (q % resBatch) = 0 then [(fp + fs name, CHw)] else
      [(fp + fs name, CHw), (fp + fs name + 2 * ((q / resBatch) + 1), RSw)] := by
    by_cases h0 : (q % resBatch) = 0
    · simp [hLb, hwords, lrSizes, h0, bufL, bases]
    · simp [hLb, hwords, lrSizes, h0, bufL, bases]
  have hCHm : ∀ rd, MemL rd Lb → ReadsAt rd (ofK (addressOfIndex (fp + fs name))) CHw := fun rd h ↦
    h (fp + fs name, CHw) (by rw [hLbE]; split <;> simp)
  have hRSm : (q % resBatch) ≠ 0 → ∀ rd, MemL rd Lb →
      ReadsAt rd (ofK (addressOfIndex (fp + fs name + 2 * ((q / resBatch) + 1)))) RSw := fun h0 rd h ↦
    h (fp + fs name + 2 * ((q / resBatch) + 1), RSw) (by rw [hLbE]; simp [h0])
  obtain ⟨Lk, hLk⟩ : ∃ L, L = Lb ++ Lin := ⟨_, rfl⟩
  have hregK : ∀ i, RegionL Lk i → RegionL Lin i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (lrSizes q).sum) := by
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
    (args := [1, gen ^ (q / resBatch), P, ofK (addressOfIndex (fp + fs name)), BD, HS, M])
    (fun hg rd hl hL ↦ by
      obtain ⟨hP, hD, hH, hB⟩ := hres rd hl hL
      exact lrLoop1_complete hl1 hst hq8 hP hD hH (by rw [← hCHw]; exact hCHm _ hB) hg)
  obtain ⟨m2, hm2a, hm2b⟩ : ∃ m2, ((q % resBatch) = 0 → m2 = 0) ∧ ∀ rd, LowDef κ rd → MemL rd Lk →
      ((q % resBatch) ≠ 0 → if 1 + gen ^ (q % resBatch) ≠ 0 then
        RelAtIn coreProgram fs cert rd (RegionL Lk) (fun _ ↦ False) (fp + fs name + (lrSizes q).sum + m1) m2
          loop2 [1, gen ^ (q % resBatch), ofK (addressOfIndex (fp + fs name + 2 * ((q / resBatch) + 1))),
            P * gen ^ (resBatch * (q / resBatch)), BD, HS, M] []
        else m2 = fs loop2) := by
    by_cases h0 : (q % resBatch) = 0
    · exact ⟨0, fun _ ↦ rfl, fun _ _ _ h ↦ absurd h0 h⟩
    · obtain ⟨m2, hm2⟩ := lr_guarded_uniform (lr_pureIn (hl2 h0) (hp2 h0))
        (List.mem_singleton_self _) fs cert (κ := κ) (Lk := Lk) (G := 1 + gen ^ (q % resBatch) ≠ 0)
        (args := [1, gen ^ (q % resBatch), ofK (addressOfIndex (fp + fs name + 2 * ((q / resBatch) + 1))),
          P * gen ^ (resBatch * (q / resBatch)), BD, HS, M])
        (fun hg rd hl hL ↦ by
          obtain ⟨hP, hD, hH, hB⟩ := hres rd hl hL
          refine lrLoop2_complete (hl2 h0) hst (nb := q / resBatch) (Pos := p) (Nat.pos_of_ne_zero h0)
            (fun k hk ↦ ?_) hD hH (by rw [← hRSw]; exact hRSm h0 _ hB) hg
          rw [loadHolds_mul_gen_pow]
          exact hP _ (by omega))
      exact ⟨m2, fun h ↦ absurd h h0, fun rd hl hL _ ↦ hm2 _ rd hl hL⟩
  -- the chains' ends
  have hret : lrRet q cols nhs hbits D hsv p M =
      if (q % resBatch) = 0 then (CHw.getD (2 * (q / resBatch)) 0, CHw.getD (2 * (q / resBatch) + 1) 0)
      else (RSw.getD (2 * (q % resBatch)) 0, RSw.getD (2 * (q % resBatch) + 1) 0) := by
    by_cases h0 : (q % resBatch) = 0
    · obtain ⟨g0, g1⟩ := rcC_get (lrRow q cols nhs hbits) D hsv p M (j := (q / resBatch)) (by show (q / resBatch) ≤ q / resBatch; omega)
      simp only [h0, ↓reduceIte]
      rw [hCHw, g0, g1]
      show _ = rcAt (lrRow q cols nhs hbits) D hsv p M (q / resBatch)
      unfold rcAt lrRet
      rw [show resBatch * (q / resBatch) = q by omega]
      rfl
    · obtain ⟨g0, g1⟩ := rsC_get (lrRow q cols nhs hbits) D hsv p M (q / resBatch) (q % resBatch) (j := (q % resBatch)) le_rfl
      simp only [h0, ↓reduceIte]
      rw [hRSw, g0, g1]
      show _ = rsAt (lrRow q cols nhs hbits) D hsv p M (q / resBatch) (q % resBatch)
      unfold rsAt lrRet
      rw [hqd]
      rfl
  have key : ∀ rd, LowDef κ rd → MemL rd Lk →
      RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ ↦ False) fp (fs name + (lrSizes q).sum + (m1 + m2))
        name [P, BD, HS, M]
        [(lrRet q cols nhs hbits D hsv p M).1, (lrRet q cols nhs hbits D hsv p M).2] := by
    intro rd hl hL
    have hB := (Main.memL_append.mp (hLk ▸ hL)).1
    have hz : CHw.getD 0 0 = 0 ∧ CHw.getD 1 0 = 0 := by
      obtain ⟨g0, g1⟩ := rcC_get (lrRow q cols nhs hbits) D hsv p M (j := 0) (Nat.zero_le _)
      rw [hCHw, g0, g1]
      exact ⟨rfl, rfl⟩
    rw [hret]
    by_cases h0 : (q % resBatch) = 0
    · simp only [h0, ↓reduceIte]
      rw [hm2a h0, Nat.add_zero]
      exact lr_relAtIn0 hlr hq h0 fs cert (hCHm rd hB) (by rw [hCHw, rcC_length]; rfl) hz.1 hz.2
        (hm1 _ rd hl hL) hregK
    · simp only [h0, ↓reduceIte]
      obtain ⟨g0, g1⟩ := rsC_get (lrRow q cols nhs hbits) D hsv p M (q / resBatch) (q % resBatch) (j := 0) (Nat.zero_le _)
      obtain ⟨c0, c1⟩ := rcC_get (lrRow q cols nhs hbits) D hsv p M (j := (q / resBatch)) (by show (q / resBatch) ≤ q / resBatch; omega)
      exact lr_relAtIn1 hlr hq h0 fs cert (hCHm rd hB) (by rw [hCHw, rcC_length]; rfl) hz.1 hz.2
        (hRSm h0 rd hB) (by rw [hRSw, rsC_length]) (by rw [hRSw, hCHw, g0, c0]; rfl)
        (by rw [hRSw, hCHw, g1, c1]; rfl) (hm1 _ rd hl hL) (hm2b rd hl hL h0) hregK hregK
  refine ⟨m1 + m2, fun rd hl hL ↦ key rd hl ?_⟩
  rw [hLk, hLb, hwords, hCHw, hRSw]
  exact hL

/-- **`level_residual` at an entry is `LrAtD`.** -/
theorem lrAtD_of {name loop1 loop2 : String} {q cols nhs hbits : ℕ}
    (hlr : FnIs name (osParams 4) (lrBody q loop1 loop2))
    (hl1 : FnIs loop1 (osParams 7) (lrLoop1Body cols nhs hbits loop1))
    (hl2 : q % resBatch ≠ 0 → FnIs loop2 (osParams 7) (lrLoop2Body cols nhs hbits loop2))
    (hF : LrFacts q cols nhs hbits loop1 loop2) (fs : String → ℕ) (cert : String → V → ℕ)
    (κ : ℕ) : LrAtD fs cert κ name q cols nhs hbits := by
  intro Lin P BD HS M D p hsv hlen hreg hmem fp
  obtain ⟨m, hm⟩ := lr_key hlr hl1 hl2 hF fs cert κ hlen hreg hmem fp
  have hW : Within (lrLb fs name q cols nhs hbits D hsv p M fp) (fp + fs name) (lrSizes q).sum :=
    bufL_within _ _ _ (lrWords_fit _ _ _ _ _ _ _ _)
  refine ⟨fs name + (lrSizes q).sum + m, lrLb fs name q cols nhs hbits D hsv p M fp, _, [],
    ⟨rfl, rfl⟩, ?_, by rw [List.nil_append]; exact bufL_disj _ _ _ (lrWords_fit q cols nhs hbits D hsv p M),
    fun rd hl hL ↦ relAtIn_dmono (hm rd hl (by simpa using hL)) (fun i hi ↦ ?_)⟩
  · simpa using hW.mono (b' := fp) (n' := fs name + (lrSizes q).sum + m) (Nat.le_add_right _ _)
      (by omega)
  · obtain ⟨e, he, _⟩ := hi; simp at he

/-- **`level_residual` is complete placed at every specialization.** -/
theorem level_residual_completeAt : level_residual_completeAt_Spec := by
  intro fs cert κ _ _ _ e he
  obtain ⟨hlr, hl1, hl2⟩ := lrTable_ok e he
  exact lrAtD_of hlr hl1 hl2 (lrTable_facts e he) fs cert κ

end
end LeanVM.Guest.B1
