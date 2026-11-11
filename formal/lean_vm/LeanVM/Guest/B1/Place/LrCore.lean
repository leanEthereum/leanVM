/-
  LeanVM.Guest.B1.Place.LrCore

  `level_residual`'s body placed at a frame pointer: its chain buffers after its frame, its loops
  after them.
-/

module

public import LeanVM.Guest.B1.Place.LrPure

/-!
# `level_residual`'s body, placed

`lr_relAtIn0` (`8 ∣ q`) and `lr_relAtIn1` (`8 ∤ q`): `level_residual` at `fp`, its batches'
chain (`lrAcc` at multiples of eight) at `fp + fs name` and, when `8 ∤ q`, the rest's chain right
after it, holds by its frame, its buffers and its loops' trees, given placed after the buffers,
each loading from the caller's region or the buffers.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The sizes of `level_residual`'s buffers at `q` queries. -/
def lrSizes (q : ℕ) : List ℕ :=
  if q % resBatch = 0 then [q / resBatch + 1] else [q / resBatch + 1, q % resBatch + 1]

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

/-- What a flat block's events need, from its statements' relations. -/
theorem slOk_of_allOk {C : CallRel} {rd : Reader} {σ : Val} {pre : List Stmt}
    (h : AllOk C rd σ pre) : ∀ s ∈ pre, LrSlOk rd σ s := by
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

theorem kidsFromIn_nil' {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader} {σ : Val}
    {R Dacc : ℕ → Prop} {b : ℕ} :
    KidsFromIn coreProgram fs cert rd σ R Dacc [] b 0 (fun _ ↦ False) :=
  ⟨rfl, fun _ h ↦ h.elim⟩

theorem lr_notLoop {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    {pre : List Stmt} {v : V} (hb : fn.body = pre ++ [.ret [v]]) : coreProgram.loop name = false := by
  rw [Program.loop_of_find? hf, Fn.loop, hb]
  simp [List.reverse_append]

/-! ## `8 ∣ q` -/

/-- **`level_residual` at `q` queries, `8 ∣ q`, placed**: its batches' chain at `fp + fs name`, its
loop's tree of `m1` words after it. -/
theorem lr_relAtIn0 {name loop1 loop2 : String} {q cols : ℕ}
    (hlr : FnIs name (osParams 3) (lrBody q loop1 loop2)) (hq : q + 2 < 2 ^ 64 - 1)
    (h0 : q % resBatch = 0) (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader}
    {R Rk1 : ℕ → Prop} {fp m1 : ℕ} {P BD M : E} {D p : ℕ → E}
    (hCH : ∀ j ≤ q / resBatch, LoadHolds rd (ofK (addressOfIndex (fp + fs name))) j
      (lrAcc D cols M p (resBatch * j)))
    (hL1 : if 1 + gen ^ (q / resBatch) ≠ 0 then
      RelAtIn coreProgram fs cert rd Rk1 (fun _ ↦ False) (fp + fs name + (lrSizes q).sum) m1 loop1
        [1, gen ^ (q / resBatch), ofK (addressOfIndex (fp + fs name)), P, BD, M] []
      else m1 = fs loop1)
    (hRk1 : ∀ i, Rk1 i → R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (lrSizes q).sum)) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp (fs name + (lrSizes q).sum + m1) name
      [P, BD, M] [lrAcc D cols M p q] := by
  obtain ⟨fn, hf, hps, hb⟩ := hlr
  set q8 := q / resBatch with hq8
  have hqd : resBatch * q8 = q := by
    have := Nat.div_add_mod q resBatch; rw [← hq8, h0] at this; omega
  have hq8le : q8 ≤ q := Nat.div_le_self _ _
  have h8 : q8 < u128Bound := by simp only [u128Bound]; omega
  have h81 : q8 + 1 < u128Bound := by simp only [u128Bound]; omega
  have hS : lrSizes q = [q8 + 1] := by simp [lrSizes, h0, hq8]
  set pre : List Stmt := osHeap (q8 + 1) 3 ++
      [.atom (.const (.n 5) (word 0 0 0)), .atom (.load (.n 5) (.n 4) 0)] ++
      osLoopCall loop1 q8 [4, 0, 1, 2] 6 ++ [.atom (.load (.n 11) (.n 4) q8)] ++
      [.atom (.copy (.n 12) (.n 11))] with hpre
  have hb' : fn.body = pre ++ [.ret [.n 12]] := by
    rw [hb, lrBody]
    simp only [h0, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append, hq8, hpre]
  have hstr : pre.all Main.Stmt.straight = true := by
    simp [hpre, osHeap, osLoopCall, Main.Stmt.straight]
  set A8 := lrAcc D cols M p (resBatch * q8)
  set vals := [P, BD, M, gw (q8 + 1), ofK (addressOfIndex (fp + fs name)), word 0 0 0, word 1 0 0, gw q8, word 1 0 0 + gw q8,
    word 1 0 0, gw q8, A8, A8] with hvals
  set σ := argVal vals with hσ
  have hz : LoadHolds rd (ofK (addressOfIndex (fp + fs name))) 0 (word 0 0 0) := by
    have := hCH 0 (Nat.zero_le _)
    rw [word_zero]; simpa [lrAcc, resFoldC] using this
  have hB := hCH q8 le_rfl
  have hok : AllOk (fun _ _ _ ↦ True) rd σ pre := by
    simp only [hpre, osHeap, osLoopCall, List.cons_append, List.nil_append,
      allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil, argVal_n,
      hσ]
    simp only [hvals, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, true_and, and_true, implies_true]
    rw [Whir.gw_eq h8]
    exact ⟨hz, isInK_one_add_gen_pow q8, hB⟩
  have hw := Main.walk_straight σ [.n 12] pre hstr
  rw [← hb'] at hw
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ pre hstr
  have hal : pre.filterMap Main.Stmt.allocSz = [(.n 4, .inr (.n 3))] := by
    rfl
  have e3 : σ (.n 3) = gw (q8 + 1) := by rw [hσ, argVal_n]; rfl
  have e4 : σ (.n 4) = ofK (addressOfIndex (fp + fs name)) := by rw [hσ, argVal_n]; rfl
  have e8 : σ (.n 8) = 1 + gen ^ q8 := by rw [hσ, argVal_n]; simp [hvals, word_one, Whir.gw_eq h8]
  set es := pre.flatMap (Main.slEvs σ) with hes
  have hallocs : allocs σ es = [q8 + 1] := by
    rw [i2, hal]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, e3]
    rw [Whir.gw_eq h81, gen_pow_eq_ofK, logG_spec (by omega)]
  have hcalls : calls es = [⟨loop1, [.n 9, .n 10, .n 4, .n 0, .n 1, .n 2], [],
      decide (σ (.n 8) ≠ 0)⟩] := by
    rw [i4, show pre.filterMap Main.Stmt.callS =
      [(some (.n 8), loop1, [.n 9, .n 10, .n 4, .n 0, .n 1, .n 2], [])] from rfl]
    rfl
  have hown : ∀ i, fp + fs name ≤ i → i < (fp + fs name) + (q8 + 1) → ownData cert fp (fp + fs name) name (allocs σ es) es i :=
    fun i h1 h2 ↦ Or.inl ⟨(q8 + 1, fp + fs name), by rw [hallocs]; simp [bases], h1, h2⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    coreProgram_wf (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp) (N := m1 + 0)
    (args := [P, BD, M]) (rets := [lrAcc D cols M p q])
    hf (Or.inl (lr_notLoop hf hb')) (by rw [hps]; rfl) hw
    (by simp [hσ, argVal_n, hvals, A8, hqd]) (lr_slEvs_holds (slOk_of_allOk hok))
    (by rw [i1, hal, hallocs]; simp [bases, e4])
    (fun q' hq' ↦ by
      rw [i3, show pre.filterMap Main.Stmt.addrS = [] from rfl] at hq'
      simp at hq')
    ?_ (fun A hA ↦ ?_) (fun _ h ↦ h.elim)
  · rw [hallocs] at h
    simpa [hS] using h
  · have hsum : (allocs σ es).sum = (lrSizes q).sum := by rw [hallocs, hS]
    rw [hcalls, hsum]
    have hargs : ([.n 9, .n 10, .n 4, .n 0, .n 1, .n 2] : List V).map σ =
        [1, gen ^ q8, ofK (addressOfIndex (fp + fs name)), P, BD, M] := by
      simp [hσ, argVal_n, hvals, word_one, Whir.gw_eq h8]
    refine kidsFromIn_loopCall (Rk := Rk1) (fun i hi ↦ ?_) ?_ fun _ ↦ kidsFromIn_nil'
    · rcases hRk1 i hi with h | h
      · exact Or.inl h
      · rw [hS] at h; exact Or.inr (hown i h.1 (by simpa using h.2))
    · rw [hargs, e8]; exact hL1
  · rw [B1.loadAddrs_straight σ pre hstr] at hA
    have hl : pre.filterMap B1.Stmt.loadS = [(.n 4, 0), (.n 4, q8)] := by
      rfl
    rw [hl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl
    · have a1 : fp + fs name ≤ fp + fs name + 0 := Nat.le_add_right _ _
      have a2 : fp + fs name + 0 < fp + fs name + (q8 + 1) := Nat.add_lt_add_left (Nat.succ_pos q8) _
      exact ⟨fp + fs name + 0, by rw [e4, Main.addr_ofK], Or.inl (hown _ a1 a2)⟩
    · have a1 : fp + fs name ≤ fp + fs name + q8 := Nat.le_add_right _ _
      have a2 : fp + fs name + q8 < fp + fs name + (q8 + 1) := Nat.lt_succ_self _
      exact ⟨fp + fs name + q8, by rw [e4, Main.addr_ofK], Or.inl (hown _ a1 a2)⟩

/-! ## `8 ∤ q` -/

theorem lr_win (b x y z : ℕ) (h : z ≤ x) : b ≤ b + z ∧ b + z < b + (x + 1 + (y + 1)) := by
  omega

theorem lr_win' (b x y z : ℕ) (h : z ≤ y) :
    b ≤ b + (x + 1) + z ∧ b + (x + 1) + z < b + (x + 1 + (y + 1)) := by
  omega

/-- **`level_residual` at `q` queries, `8 ∤ q`, placed**: its batches' chain at `fp + fs name`, the
rest's chain right after it, its loops' trees of `m1` and `m2` words after them. -/
theorem lr_relAtIn1 {name loop1 loop2 : String} {q cols : ℕ}
    (hlr : FnIs name (osParams 3) (lrBody q loop1 loop2)) (hq : q + 2 < 2 ^ 64 - 1)
    (h0 : q % resBatch ≠ 0) (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader}
    {R Rk1 Rk2 : ℕ → Prop} {fp m1 m2 : ℕ} {P BD M : E} {D p : ℕ → E}
    (hCH : ∀ j ≤ q / resBatch, LoadHolds rd (ofK (addressOfIndex (fp + fs name))) j
      (lrAcc D cols M p (resBatch * j)))
    (hRS : ∀ j ≤ q % resBatch,
      LoadHolds rd (ofK (addressOfIndex (fp + fs name + (q / resBatch + 1)))) j
        (lrAcc D cols M p (resBatch * (q / resBatch) + j)))
    (hL1 : if 1 + gen ^ (q / resBatch) ≠ 0 then
      RelAtIn coreProgram fs cert rd Rk1 (fun _ ↦ False) (fp + fs name + (lrSizes q).sum) m1 loop1
        [1, gen ^ (q / resBatch), ofK (addressOfIndex (fp + fs name)), P, BD, M] []
      else m1 = fs loop1)
    (hL2 : if 1 + gen ^ (q % resBatch) ≠ 0 then
      RelAtIn coreProgram fs cert rd Rk2 (fun _ ↦ False) (fp + fs name + (lrSizes q).sum + m1) m2
        loop2 [1, gen ^ (q % resBatch), ofK (addressOfIndex (fp + fs name + (q / resBatch + 1))),
          P * gen ^ (resBatch * (q / resBatch)), BD, M] []
      else m2 = fs loop2)
    (hRk1 : ∀ i, Rk1 i → R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (lrSizes q).sum))
    (hRk2 : ∀ i, Rk2 i → R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (lrSizes q).sum)) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp (fs name + (lrSizes q).sum + (m1 + m2))
      name [P, BD, M] [lrAcc D cols M p q] := by
  obtain ⟨fn, hf, hps, hb⟩ := hlr
  have hS : lrSizes q = [q / resBatch + 1, q % resBatch + 1] := by simp [lrSizes, h0]
  have hb' : fn.body = (osHeap (q / resBatch + 1) 3 ++
      [.atom (.const (.n 5) (word 0 0 0)), .atom (.load (.n 5) (.n 4) 0)] ++
      osLoopCall loop1 (q / resBatch) [4, 0, 1, 2] 6 ++ [.atom (.load (.n 11) (.n 4) (q / resBatch))] ++
      (osHeap (q % resBatch + 1) 12 ++
        [.atom (.load (.n 11) (.n 13) 0), .atom (.const (.n 14) (gw (resBatch * (q / resBatch)))),
          .atom (.mul (.n 15) (.n 0) (.n 14))] ++
        osLoopCall loop2 (q % resBatch) [13, 15, 1, 2] 16 ++
        [.atom (.load (.n 21) (.n 13) (q % resBatch)), .atom (.copy (.n 22) (.n 21))])) ++
      [.ret [.n 22]] := by
    rw [hb, lrBody]
    simp only [h0, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]
  set q8 := q / resBatch with hq8
  set r := q % resBatch with hr
  have hqd : resBatch * q8 + r = q := Nat.div_add_mod q resBatch
  have hq8le : q8 ≤ q := Nat.div_le_self _ _
  have hrle : r ≤ q := Nat.mod_le _ _
  have h8 : q8 < u128Bound := by simp only [u128Bound]; omega
  have h81 : q8 + 1 < u128Bound := by simp only [u128Bound]; omega
  have hr8 : r < u128Bound := by simp only [u128Bound]; omega
  have hr1 : r + 1 < u128Bound := by simp only [u128Bound]; omega
  have hb8 : resBatch * q8 < u128Bound := by simp only [u128Bound]; omega
  set pre : List Stmt := osHeap (q8 + 1) 3 ++
      [.atom (.const (.n 5) (word 0 0 0)), .atom (.load (.n 5) (.n 4) 0)] ++
      osLoopCall loop1 q8 [4, 0, 1, 2] 6 ++ [.atom (.load (.n 11) (.n 4) q8)] ++
      (osHeap (r + 1) 12 ++
        [.atom (.load (.n 11) (.n 13) 0), .atom (.const (.n 14) (gw (resBatch * q8))),
          .atom (.mul (.n 15) (.n 0) (.n 14))] ++
        osLoopCall loop2 r [13, 15, 1, 2] 16 ++
        [.atom (.load (.n 21) (.n 13) r), .atom (.copy (.n 22) (.n 21))]) with hpre
  have hstr : pre.all Main.Stmt.straight = true := by
    simp [hpre, osHeap, osLoopCall, Main.Stmt.straight]
  set b := fp + fs name
  set A8 := lrAcc D cols M p (resBatch * q8)
  set Aq := lrAcc D cols M p q
  set vals := [P, BD, M, gw (q8 + 1), ofK (addressOfIndex b), word 0 0 0, word 1 0 0, gw q8,
    word 1 0 0 + gw q8, word 1 0 0, gw q8, A8, gw (r + 1), ofK (addressOfIndex (b + (q8 + 1))),
    gw (resBatch * q8), P * gw (resBatch * q8), word 1 0 0, gw r, word 1 0 0 + gw r, word 1 0 0,
    gw r, Aq, Aq] with hvals
  set σ := argVal vals with hσ
  have hz : LoadHolds rd (ofK (addressOfIndex b)) 0 (word 0 0 0) := by
    have := hCH 0 (Nat.zero_le _)
    rw [word_zero]; simpa [lrAcc, resFoldC] using this
  have hB := hCH q8 le_rfl
  have hR0 := hRS 0 (by omega)
  have hRr := hRS r le_rfl
  rw [Nat.add_zero] at hR0
  rw [hqd] at hRr
  have hok : AllOk (fun _ _ _ ↦ True) rd σ pre := by
    simp only [hpre, osHeap, osLoopCall, List.cons_append, List.nil_append,
      allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil, argVal_n,
      hσ]
    simp only [hvals, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, true_and, and_true, implies_true]
    rw [Whir.gw_eq h8, Whir.gw_eq hr8]
    exact ⟨hz, isInK_one_add_gen_pow q8, hB, hR0, isInK_one_add_gen_pow r, hRr⟩
  have hw := Main.walk_straight σ [.n 22] pre hstr
  rw [← hb'] at hw
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ pre hstr
  have hal : pre.filterMap Main.Stmt.allocSz = [(.n 4, .inr (.n 3)), (.n 13, .inr (.n 12))] := rfl
  have e3 : σ (.n 3) = gw (q8 + 1) := by rw [hσ, argVal_n]; rfl
  have e4 : σ (.n 4) = ofK (addressOfIndex b) := by rw [hσ, argVal_n]; rfl
  have e12 : σ (.n 12) = gw (r + 1) := by rw [hσ, argVal_n]; rfl
  have e13 : σ (.n 13) = ofK (addressOfIndex (b + (q8 + 1))) := by rw [hσ, argVal_n]; rfl
  have e8 : σ (.n 8) = 1 + gen ^ q8 := by rw [hσ, argVal_n]; simp [hvals, word_one, Whir.gw_eq h8]
  have e18 : σ (.n 18) = 1 + gen ^ r := by rw [hσ, argVal_n]; simp [hvals, word_one, Whir.gw_eq hr8]
  set es := pre.flatMap (Main.slEvs σ) with hes
  have hallocs : allocs σ es = [q8 + 1, r + 1] := by
    rw [i2, hal]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, e3, e12]
    rw [Whir.gw_eq h81, Whir.gw_eq hr1, gen_pow_eq_ofK, gen_pow_eq_ofK, logG_spec (by omega),
      logG_spec (by omega)]
  have hcalls : calls es = [⟨loop1, [.n 9, .n 10, .n 4, .n 0, .n 1, .n 2], [], decide (σ (.n 8) ≠ 0)⟩,
      ⟨loop2, [.n 19, .n 20, .n 13, .n 15, .n 1, .n 2], [], decide (σ (.n 18) ≠ 0)⟩] := by
    rw [i4, show pre.filterMap Main.Stmt.callS =
      [(some (.n 8), loop1, [.n 9, .n 10, .n 4, .n 0, .n 1, .n 2], []),
        (some (.n 18), loop2, [.n 19, .n 20, .n 13, .n 15, .n 1, .n 2], [])] from rfl]
    rfl
  have hown : ∀ i, b ≤ i → i < b + (q8 + 1 + (r + 1)) →
      ownData cert fp (fp + fs name) name (allocs σ es) es i := by
    intro i h1 h2
    rw [hallocs]
    by_cases hi : i < b + (q8 + 1)
    · exact Or.inl ⟨(q8 + 1, b), by simp [bases, b], h1, hi⟩
    · exact Or.inl ⟨(r + 1, b + (q8 + 1)), by simp [bases, b],
        Nat.le_of_not_lt hi, by rw [Nat.add_assoc]; exact h2⟩
  have hsum : (lrSizes q).sum = q8 + 1 + (r + 1) := by rw [hS]; simp
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    coreProgram_wf (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp)
    (N := m1 + (m2 + 0)) (args := [P, BD, M]) (rets := [Aq])
    hf (Or.inl (lr_notLoop hf hb')) (by rw [hps]; rfl) hw
    (by simp [hσ, argVal_n, hvals]) (lr_slEvs_holds (slOk_of_allOk hok))
    (by rw [i1, hal, hallocs]; simp [bases, e4, e13, b])
    (fun q' hq' ↦ by
      rw [i3, show pre.filterMap Main.Stmt.addrS = [] from rfl] at hq'
      simp at hq')
    ?_ (fun A hA ↦ ?_) (fun _ h ↦ h.elim)
  · rw [hallocs] at h
    simpa [hS, Nat.add_assoc] using h
  · have hsum' : (allocs σ es).sum = (lrSizes q).sum := by rw [hallocs, hS]
    rw [hcalls, hsum']
    have hargs1 : ([.n 9, .n 10, .n 4, .n 0, .n 1, .n 2] : List V).map σ =
        [1, gen ^ q8, ofK (addressOfIndex b), P, BD, M] := by
      simp [hσ, argVal_n, hvals, word_one, Whir.gw_eq h8]
    have hargs2 : ([.n 19, .n 20, .n 13, .n 15, .n 1, .n 2] : List V).map σ =
        [1, gen ^ r, ofK (addressOfIndex (b + (q8 + 1))), P * gen ^ (resBatch * q8), BD, M] := by
      simp [hσ, argVal_n, hvals, word_one, Whir.gw_eq hr8, Whir.gw_eq hb8]
    have hreg : ∀ Rk : ℕ → Prop, (∀ i, Rk i → R i ∨ (b ≤ i ∧ i < b + (lrSizes q).sum)) →
        ∀ i, Rk i → R i ∨ ownData cert fp (fp + fs name) name (allocs σ es) es i := by
      intro Rk hRk i hi
      rcases hRk i hi with h | h
      · exact Or.inl h
      · rw [hsum] at h; exact Or.inr (hown i h.1 h.2)
    refine kidsFromIn_loopCall (Rk := Rk1) (hreg Rk1 hRk1) (by rw [hargs1, e8]; exact hL1)
      fun _ ↦ kidsFromIn_loopCall (Rk := Rk2) (hreg Rk2 hRk2) (by rw [hargs2, e18]; exact hL2)
        fun _ ↦ kidsFromIn_nil'
  · rw [B1.loadAddrs_straight σ pre hstr] at hA
    have hl : pre.filterMap B1.Stmt.loadS = [(.n 4, 0), (.n 4, q8), (.n 13, 0), (.n 13, r)] := rfl
    rw [hl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have hw' : ∀ i, b ≤ i → i < b + (q8 + 1 + (r + 1)) → ∃ j, addressOfIndex i = addressOfIndex j ∧
        (ownData cert fp (fp + fs name) name (allocs σ es) es j ∨ R j ∨ False) :=
      fun i h1 h2 ↦ ⟨i, rfl, Or.inl (hown i h1 h2)⟩
    rcases hA with rfl | rfl | rfl | rfl
    · rw [e4, Main.addr_ofK]
      exact hw' _ (lr_win b q8 r 0 (Nat.zero_le _)).1 (lr_win b q8 r 0 (Nat.zero_le _)).2
    · rw [e4, Main.addr_ofK]
      exact hw' _ (lr_win b q8 r q8 le_rfl).1 (lr_win b q8 r q8 le_rfl).2
    · rw [e13, Main.addr_ofK]
      exact hw' _ (lr_win' b q8 r 0 (Nat.zero_le _)).1 (lr_win' b q8 r 0 (Nat.zero_le _)).2
    · rw [e13, Main.addr_ofK]
      exact hw' _ (lr_win' b q8 r r le_rfl).1 (lr_win' b q8 r r le_rfl).2

end
end LeanVM.Guest.B1
