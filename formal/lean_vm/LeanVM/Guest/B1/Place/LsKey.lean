/-
  LeanVM.Guest.B1.Place.LsKey

  `level_residual_slow` placed at every entry of `lrsTable`, its sum's buffers honest.
-/

module

public import LeanVM.Guest.B1.Place.LsLoops
public import LeanVM.Guest.B1.Place.LrProof

/-!
# `level_residual_slow`, placed

`level_residual_slow` at `fp` allocates nothing: at a zero flag it returns it (`lrs_relAtIn0`),
else it calls its sum at `fp + fs name` (`lrs_relAtIn1`). The sum allocates its two buffers of
`Q + 1` words (`acc`, `lrsAcc`, then `pw`, `λ^(2 + j)`) after its frame and calls its loop, which
places nothing, after them (`lsum_relAtIn`); the loop and its `residual_query_slow` are placed by
trees of one size on every memory holding their words (`lr_relAtIn_pure_uniform`).

* `lsKey`: at a flag `z ∈ {0, 1}`, the helper by its frame, its sum's buffers (`lsLb`) and the
  loop's tree, on every memory holding the buffers and the caller's words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## The sum, placed -/

/-- **`level_residual_sum`, placed** at `fp`: its buffers `AC`, `PW` at `fp + fs sum`, its loop's
tree of `m` words after them. -/
theorem lsum_relAtIn {sum loop : String} {Q : ℕ} (hs : FnIs sum (osParams 4) (lsumBody Q loop))
    (hQ : 1 ≤ Q) (hQb : Q < 2 ^ 30) (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader}
    {R Rk : ℕ → Prop} {fp m : ℕ} {P F T lam : E} {AC PW : List E}
    (hAC : ReadsAt rd (ofK (addressOfIndex (fp + fs sum))) AC) (hACl : AC.length = Q + 1)
    (hz : AC.getD 0 0 = 0)
    (hPW : ReadsAt rd (ofK (addressOfIndex (fp + fs sum + (Q + 1)))) PW) (hPWl : PW.length = Q + 1)
    (hp0 : PW.getD 0 0 = lam * lam)
    (hL : RelAtIn coreProgram fs cert rd Rk (fun _ ↦ False) (fp + fs sum + 2 * (Q + 1)) m loop
      [1, gen ^ Q, ofK (addressOfIndex (fp + fs sum)), ofK (addressOfIndex (fp + fs sum + (Q + 1))),
        P, F, T, lam] [])
    (hRk : ∀ i, Rk i → R i ∨ (fp + fs sum ≤ i ∧ i < fp + fs sum + 2 * (Q + 1))) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp (fs sum + 2 * (Q + 1) + m) sum
      [P, F, T, lam] [AC.getD Q 0] := by
  obtain ⟨fn, hf, hps, hb⟩ := hs
  have hQu : Q < u128Bound := by simp only [u128Bound]; omega
  have hQ1u : Q + 1 < u128Bound := by simp only [u128Bound]; omega
  set pre : List Stmt :=
    [.atom (.const (.n 4) (gw (Q + 1))), .atom (.hint (.allocDyn (.n 5) (.n 4))),
      .atom (.const (.n 6) (gw (Q + 1))), .atom (.hint (.allocDyn (.n 7) (.n 6))),
      .atom (.const (.n 8) (word 0 0)), .atom (.load (.n 8) (.n 5) 0),
      .atom (.mul (.n 9) (.n 3) (.n 3)), .atom (.load (.n 9) (.n 7) 0),
      .atom (.const (.n 10) (word 1 0)), .atom (.const (.n 11) (gw Q)),
      .atom (.add (.n 12) (.n 10) (.n 11)), .atom (.const (.n 13) (word 1 0)),
      .atom (.const (.n 14) (gw Q)),
      .callIf (.n 12) loop [.n 13, .n 14, .n 5, .n 7, .n 0, .n 1, .n 2, .n 3],
      .atom (.load (.n 15) (.n 5) Q)] with hpre
  have hb' : fn.body = pre ++ [.ret [.n 15]] := by rw [hb]; rfl
  have hstr : pre.all Main.Stmt.straight = true := by simp [hpre, Main.Stmt.straight]
  set b := fp + fs sum with hbd
  set b' := fp + fs sum + (Q + 1) with hbd'
  set vals := [P, F, T, lam, gw (Q + 1), ofK (addressOfIndex b), gw (Q + 1), ofK (addressOfIndex b'),
    word 0 0, lam * lam, word 1 0, gw Q, word 1 0 + gw Q, word 1 0, gw Q, AC.getD Q 0] with hvals
  set σ := lrVal vals with hσ
  have hld : ∀ e < AC.length, LoadHolds rd (ofK (addressOfIndex b)) e (AC.getD e 0) := fun e he ↦ by
    rw [List.getD_eq_getElem _ _ he]; exact hAC e he
  have hldP : ∀ e < PW.length, LoadHolds rd (ofK (addressOfIndex b')) e (PW.getD e 0) := fun e he ↦ by
    rw [List.getD_eq_getElem _ _ he]; exact hPW e he
  have e12 : σ (.n 12) = 1 + gen ^ Q := by
    show word 1 0 + gw Q = _; rw [Whir.gw_eq hQu, word_one]
  have hne : σ (.n 12) ≠ 0 := by rw [e12]; exact one_add_gen_pow_ne hQ hQb
  have hok : Whir.AllOk (fun _ _ _ ↦ True) rd σ pre := by
    simp only [hpre, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, lrVal_n, hσ]
    simp only [hvals, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, true_and, and_true, implies_true]
    rw [Whir.gw_eq hQu, word_one]
    refine ⟨?_, ?_, isInK_one_add_gen_pow Q, ?_⟩
    · have := hld 0 (by omega); rwa [hz, ← word_zero] at this
    · have := hldP 0 (by omega); rwa [hp0] at this
    · exact hld _ (by omega)
  have hw := Main.walk_straight σ [.n 15] pre hstr
  rw [← hb'] at hw
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ pre hstr
  have hal : pre.filterMap Main.Stmt.allocSz = [(.n 5, .inr (.n 4)), (.n 7, .inr (.n 6))] := rfl
  have e4 : σ (.n 4) = gw (Q + 1) := rfl
  have e6 : σ (.n 6) = gw (Q + 1) := rfl
  have e5 : σ (.n 5) = ofK (addressOfIndex b) := rfl
  have e7 : σ (.n 7) = ofK (addressOfIndex b') := rfl
  set es := pre.flatMap (Main.slEvs σ) with hes
  have hallocs : allocs σ es = [Q + 1, Q + 1] := by
    rw [i2, hal]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, e4, e6]
    rw [Whir.gw_eq hQ1u, gen_pow_eq_ofK, logG_spec (by omega)]
  have hsum : (allocs σ es).sum = 2 * (Q + 1) := by
    rw [hallocs]; simp only [List.sum_cons, List.sum_nil]; omega
  have hcalls : calls es = [⟨loop, [.n 13, .n 14, .n 5, .n 7, .n 0, .n 1, .n 2, .n 3], [],
      decide (σ (.n 12) ≠ 0)⟩] := by
    rw [i4, show pre.filterMap Main.Stmt.callS =
      [(some (.n 12), loop, [.n 13, .n 14, .n 5, .n 7, .n 0, .n 1, .n 2, .n 3], [])] from rfl]
    rfl
  have hown : ∀ i, b ≤ i → i < b + 2 * (Q + 1) →
      ownData cert fp (fp + fs sum) sum (allocs σ es) es i := by
    intro i h1 h2
    rw [hallocs]
    by_cases hi : i < b + (Q + 1)
    · exact Or.inl ⟨(Q + 1, b), by simp [bases, b], h1, hi⟩
    · exact Or.inl ⟨(Q + 1, b'), by simp [bases, b'], by omega, by omega⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    coreProgram_wf (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp) (N := m + 0)
    (args := [P, F, T, lam]) (rets := [AC.getD Q 0])
    hf (Or.inl (lr_notLoop hf (by simp) hb')) (by rw [hps]; rfl) hw
    (by simp [hσ, lrVal_n, hvals]) (lr_slEvs_holds (lr_slOk_of_allOk hok))
    (by rw [i1, hal, hallocs]; simp [bases, e5, e7, b, b'])
    (fun q' hq' ↦ by
      rw [i3, show pre.filterMap Main.Stmt.addrS = [] from rfl] at hq'
      simp at hq')
    ?_ (fun A hA ↦ ?_) (fun _ h ↦ h.elim)
  · rwa [hsum, Nat.add_zero] at h
  · rw [hcalls, hsum]
    have hargs : ([.n 13, .n 14, .n 5, .n 7, .n 0, .n 1, .n 2, .n 3] : List V).map σ =
        [1, gen ^ Q, ofK (addressOfIndex b), ofK (addressOfIndex b'), P, F, T, lam] := by
      simp only [List.map_cons, List.map_nil, hσ, lrVal_n, hvals, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [Whir.gw_eq hQu, word_one]
    refine kidsFromIn_loopCall (Rk := Rk) (fun i hi ↦ ?_) ?_ fun _ ↦ lr_kidsFromIn_nil
    · rcases hRk i hi with h | h
      · exact Or.inl h
      · exact Or.inr (hown i h.1 h.2)
    · rw [ite_eq_left hne, hargs]; exact hL
  · rw [B1.loadAddrs_straight σ pre hstr] at hA
    have hl : pre.filterMap B1.Stmt.loadS = [(.n 5, 0), (.n 7, 0), (.n 5, Q)] := rfl
    rw [hl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl
    · exact ⟨b + 0, by rw [e5, Main.addr_ofK], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨b' + 0, by rw [e7, Main.addr_ofK], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨b + Q, by rw [e5, Main.addr_ofK], Or.inl (hown _ (by omega) (by omega))⟩

/-! ## The helper, placed -/

/-- `level_residual_slow`'s body before its `ret`. -/
theorem lrsBody_split (sum : String) :
    lrsBody sum = [.ite (.n 4) [.atom (.copy (.n 5) (.n 4))] [.call sum [.n 0, .n 1, .n 2, .n 3] [.n 5]],
      .atom (.copy (.n 6) (.n 5))] ++ [.ret [.n 6]] := rfl

/-- **`level_residual_slow` at a zero flag, placed** at `fp`: its frame alone. -/
theorem lrs_relAtIn0 {name sum : String} (hl : FnIs name (osParams 5) (lrsBody sum))
    (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader} {R : ℕ → Prop} {fp : ℕ} {P F T lam : E} :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp (fs name) name [P, F, T, lam, 0] [0] := by
  obtain ⟨fn, hf, hps, hb⟩ := hl
  set σ := lrVal [P, F, T, lam, 0, 0, 0] with hσ
  have h4 : σ (.n 4) = 0 := rfl
  set es : List Ev := [.inK (.n 4), .atom (.copy (.n 5) (.n 4)), .atom (.copy (.n 6) (.n 5))] with hes
  have hw : walk σ fn.body = .ret es [.n 6] := by
    rw [hb]
    simp [lrsBody, walk, walk1, Out.seq, Out.pre, h4, hes]
  have hal : allocs σ es = [] := rfl
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    coreProgram_wf (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp) (N := 0)
    (args := [P, F, T, lam, 0]) (rets := [0])
    hf (Or.inl (lr_notLoop hf (by simp) (hb.trans (lrsBody_split sum)))) (by rw [hps]; rfl) hw rfl
    (fun e he ↦ ?_) (by rw [hal]; rfl) (fun q hq ↦ by simp [hes, addrs, Ev.addr?] at hq)
    (by rw [show calls es = [] from rfl]; exact lr_kidsFromIn_nil)
    (fun A hA ↦ by simp [hes, loadAddrs, Ev.loadAddr?] at hA) (fun _ h ↦ h.elim)
  · rwa [hal, List.sum_nil, Nat.add_zero, Nat.add_zero] at h
  · simp only [hes, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · show IsInK (σ (.n 4)); rw [h4, ← ofK_zero]; exact ofK_isInK 0
    · rfl
    · rfl

/-- **`level_residual_slow` at the flag `1`, placed** at `fp`: its frame, then its sum's tree of `m`
words at `fp + fs name`. -/
theorem lrs_relAtIn1 {name sum : String} (hl : FnIs name (osParams 5) (lrsBody sum))
    (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader} {R Rk : ℕ → Prop} {fp m : ℕ}
    {P F T lam r : E}
    (hS : RelAtIn coreProgram fs cert rd Rk (fun _ ↦ False) (fp + fs name) m sum [P, F, T, lam] [r])
    (hRk : ∀ i, Rk i → R i) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp (fs name + m) name [P, F, T, lam, 1] [r] := by
  obtain ⟨fn, hf, hps, hb⟩ := hl
  set σ := lrVal [P, F, T, lam, 1, r, r] with hσ
  have h4 : σ (.n 4) = 1 := rfl
  set es : List Ev := [.inK (.n 4), .call sum [.n 0, .n 1, .n 2, .n 3] [.n 5],
    .atom (.copy (.n 6) (.n 5))] with hes
  have hw : walk σ fn.body = .ret es [.n 6] := by
    rw [hb]
    simp [lrsBody, walk, walk1, Out.seq, Out.pre, h4, hes]
  have hal : allocs σ es = [] := rfl
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    coreProgram_wf (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp) (N := m + 0)
    (args := [P, F, T, lam, 1]) (rets := [r])
    hf (Or.inl (lr_notLoop hf (by simp) (hb.trans (lrsBody_split sum)))) (by rw [hps]; rfl) hw rfl
    (fun e he ↦ ?_) (by rw [hal]; rfl) (fun q hq ↦ by simp [hes, addrs, Ev.addr?] at hq) ?_
    (fun A hA ↦ by simp [hes, loadAddrs, Ev.loadAddr?] at hA) (fun _ h ↦ h.elim)
  · rwa [hal, List.sum_nil, Nat.add_zero, Nat.add_zero] at h
  · simp only [hes, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · show IsInK (σ (.n 4)); rw [h4, ← pow_zero gen]; exact gen_pow_isInK 0
    · trivial
    · rfl
  · rw [show calls es = [⟨sum, [.n 0, .n 1, .n 2, .n 3], [.n 5], true⟩] from rfl, hal]
    refine ⟨m, 0, Rk, fun _ ↦ False, rfl, fun i hi ↦ Or.inl (Or.inl (hRk i hi)), ?_, ?_⟩
    · simp only [↓reduceIte, List.sum_nil, Nat.add_zero]
      exact hS
    · exact lr_kidsFromIn_nil

/-! ## The key -/

/-- The sum's accumulator words: `acc[j]`, `j ≤ Q`. -/
def lsAccW (Q n vo : ℕ) (p cs : ℕ → E) (lam : E) : List E :=
  (List.range (Q + 1)).map (lrsAcc n vo p cs lam)

/-- The sum's powers: `pw[j] = λ^(2 + j)`, `j ≤ Q`. -/
def lsPwW (Q : ℕ) (lam : E) : List E := (List.range (Q + 1)).map fun j ↦ lam ^ 2 * lam ^ j

/-- The sum's buffers, at the flag `z`: none at `0`, else both after the helper's and the sum's
frames. -/
def lsLb (fs : String → ℕ) (name sum : String) (Q n vo : ℕ) (p cs : ℕ → E) (lam z : E) (fp : ℕ) :
    Layout :=
  if z = 0 then [] else
    [(fp + fs name + fs sum, lsAccW Q n vo p cs lam),
      (fp + fs name + fs sum + (Q + 1), lsPwW Q lam)]

/-- The words of `level_residual_slow`'s tree beyond the loop's: its frame, and at a nonzero flag
its sum's frame and buffers. -/
def lsN (fs : String → ℕ) (name sum : String) (Q : ℕ) (z : E) : ℕ :=
  if z = 0 then fs name else fs name + (fs sum + 2 * (Q + 1))

theorem lsAccW_get {Q n vo : ℕ} {p cs : ℕ → E} {lam : E} {j : ℕ} (hj : j ≤ Q) :
    (lsAccW Q n vo p cs lam).getD j 0 = lrsAcc n vo p cs lam j := by
  rw [List.getD_eq_getElem _ _ (by simp [lsAccW]; omega)]
  simp [lsAccW]

theorem lsPwW_get {Q : ℕ} {lam : E} {j : ℕ} (hj : j ≤ Q) :
    (lsPwW Q lam).getD j 0 = lam ^ 2 * lam ^ j := by
  rw [List.getD_eq_getElem _ _ (by simp [lsPwW]; omega)]
  simp [lsPwW]

theorem lsLb_within (fs : String → ℕ) (name sum : String) (Q n vo : ℕ) (p cs : ℕ → E) (lam z : E)
    (fp : ℕ) : Within (lsLb fs name sum Q n vo p cs lam z fp) fp (lsN fs name sum Q z) := by
  unfold lsLb lsN
  split
  · intro q hq; simp at hq
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp [lsAccW, lsPwW] <;> omega

theorem lsLb_disj (fs : String → ℕ) (name sum : String) (Q n vo : ℕ) (p cs : ℕ → E) (lam z : E)
    (fp : ℕ) : DisjL (lsLb fs name sum Q n vo p cs lam z fp) := by
  unfold lsLb
  split
  · exact .nil
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons (fun _ h ↦ absurd h List.not_mem_nil) .nil)
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    left; simp [lsAccW]

/-- Every entry of `lrsTable` reads few challenges, by the kernel. -/
theorem lrsTable_small : ∀ e ∈ lrsTable, e.2.2.1 + e.2.2.2.1 ≤ 2 ^ 20 := by decide +kernel

theorem ls_pureIn {loop rq : String} {pre yr vo : ℕ}
    (hl : FnIs loop (osParams 8) (lrsLoopBody rq loop)) (hr : FnIs rq (osParams 3) (rqsBody pre yr vo)) :
    coreProgram.PureIn [loop, rq] := by
  intro g hg fn hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · obtain ⟨fl, hfl, -, hbl⟩ := hl
    rw [hfl] at hf; cases hf; rw [hbl]; exact lrsLoop_pure _ _
  · obtain ⟨fr, hfr, -, hbr⟩ := hr
    rw [hfr] at hf; cases hf; rw [hbr]; exact rqs_pure _ pre yr vo

/-- **`level_residual_slow` at `fp`, its sum's buffers honest**: by its frame, its sum's frame and
buffers and its loop's tree of `m` words, on every memory holding the buffers and the caller's
words. -/
theorem lsKey {e : String × ℕ × ℕ × ℕ × ℕ × String × String × String} (he : e ∈ lrsTable)
    (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {Lin : Layout} {P F T lam z : E}
    {p cs : ℕ → E} (hz : z = 0 ∨ z = 1)
    (hreg : RegPtrs [(0, e.2.1), (1, e.2.2.1), (2, e.2.2.2.1)] [P, F, T, lam, z] (RegionL Lin))
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      (∀ k < e.2.1, LoadHolds rd P k (p k)) ∧ (∀ t < e.2.2.1, LoadHolds rd F t (cs t)) ∧
        ∀ j < e.2.2.2.1, LoadHolds rd T j (cs (e.2.2.1 + j))) (fp : ℕ) :
    ∃ m, ∀ rd, LowDef κ rd →
      MemL rd (lsLb fs e.1 e.2.2.2.2.2.1 e.2.1 (e.2.2.1 + e.2.2.2.1) e.2.2.2.2.1 p cs lam z fp ++ Lin) →
      RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ ↦ False) fp
        (lsN fs e.1 e.2.2.2.2.2.1 e.2.1 z + m) e.1 [P, F, T, lam, z]
        [slowVal e.2.1 (e.2.2.1 + e.2.2.2.1) e.2.2.2.2.1 p cs lam z] := by
  obtain ⟨⟨fo, hfo, hpo, hbo⟩, hsum, hloop⟩ := lrsTable_ok e he
  obtain ⟨hQ, hQb, hrqT⟩ := lrsTable_shapes e he
  obtain ⟨name, Q, pre, yr, vo, sum, loop, rq⟩ := e
  simp only at hfo hpo hbo hsum hloop hrqT hQ hQb hreg hmem ⊢
  have hlrs : FnIs name (osParams 5) (lrsBody sum) := ⟨fo, hfo, hpo, hbo⟩
  rcases hz with rfl | rfl
  · refine ⟨0, fun rd _ _ ↦ ?_⟩
    simp only [lsN, slowVal, ↓reduceIte, Nat.add_zero]
    exact lrs_relAtIn0 hlrs fs cert
  have h10 : (1 : E) ≠ 0 := one_ne_zero
  obtain ⟨fr, hfr, hpr, hbr⟩ := rqsTable_ok _ hrqT
  have hrqF : FnIs rq (osParams 3) (rqsBody pre yr vo) := ⟨fr, hfr, hpr, hbr⟩
  set n := pre + yr with hn
  set b := fp + fs name + fs sum with hbd
  set AC := lsAccW Q n vo p cs lam with hAC
  set PW := lsPwW Q lam with hPW
  set Lb : Layout := [(b, AC), (b + (Q + 1), PW)] with hLb
  have hLbE : lsLb fs name sum Q n vo p cs lam 1 fp = Lb := by simp [lsLb, h10, hLb, hbd, hAC, hPW]
  have hACl : AC.length = Q + 1 := by simp [hAC, lsAccW]
  have hPWl : PW.length = Q + 1 := by simp [hPW, lsPwW]
  obtain ⟨Lk, hLk⟩ : ∃ L, L = Lb ++ Lin := ⟨_, rfl⟩
  have hLinK : ∀ i, RegionL Lin i → RegionL Lk i :=
    fun i ⟨q, hq, h⟩ ↦ ⟨q, by rw [hLk]; exact List.mem_append_right _ hq, h⟩
  have hLbK : ∀ i, RegionL Lb i → RegionL Lk i :=
    fun i ⟨q, hq, h⟩ ↦ ⟨q, by rw [hLk]; exact List.mem_append_left _ hq, h⟩
  have hregK : ∀ i, RegionL Lk i → RegionL Lin i ∨ (b ≤ i ∧ i < b + 2 * (Q + 1)) := by
    rintro i ⟨q, hq, h1, h2⟩
    rw [hLk] at hq
    rcases List.mem_append.mp hq with hq | hq
    · right
      simp only [hLb, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · simp only [hACl] at h2; omega
      · simp only [hPWl] at h2; omega
    · exact Or.inl ⟨q, hq, h1, h2⟩
  -- the loop's relation on the restricted memory
  have hres : ∀ rd, LowDef κ rd → MemL rd Lk →
      coreProgram.Rel (Main.restrict rd (RegionL Lk)) loop
        [1, gen ^ Q, ofK (addressOfIndex b), ofK (addressOfIndex (b + (Q + 1))), P, F, T, lam] [] := by
    intro rd hl hL
    set rd' := Main.restrict rd (RegionL Lk) with hrd'
    rw [hLk] at hL
    obtain ⟨hLb', hLin'⟩ := Main.memL_append.mp hL
    obtain ⟨hP, hF, hT⟩ := hmem rd hl hLin'
    have hP' : ∀ k < Q, LoadHolds rd' P k (p k) := fun k hk ↦ Main.loadHolds_restrict (hP k hk) (by
      obtain ⟨j, hj, hr⟩ := hreg (0, Q) (by simp) k hk; exact ⟨j, hj, hLinK j hr⟩)
    have hF' : ∀ t < pre, LoadHolds rd' F t (cs t) := fun t ht ↦ Main.loadHolds_restrict (hF t ht) (by
      obtain ⟨j, hj, hr⟩ := hreg (1, pre) (by simp) t ht; exact ⟨j, hj, hLinK j hr⟩)
    have hT' : ∀ j < yr, LoadHolds rd' T j (cs (pre + j)) := fun t ht ↦ Main.loadHolds_restrict (hT t ht)
      (by obtain ⟨j, hj, hr⟩ := hreg (2, yr) (by simp) t ht; exact ⟨j, hj, hLinK j hr⟩)
    have hB := Main.memL_restrict hLb' hLbK
    have hACm : ReadsAt rd' (ofK (addressOfIndex b)) AC := hB (b, AC) (by simp [hLb])
    have hPWm : ReadsAt rd' (ofK (addressOfIndex (b + (Q + 1)))) PW := hB (b + (Q + 1), PW) (by simp [hLb])
    refine lsLoop_rel he (pos := p) (cs := cs) (fun k hk ↦ ?_) (fun k hk ↦ ?_) hP' hF' hT'
    · have := Whir.readsAt_getD' hACm (j := k) (by rw [hACl]; exact Nat.lt_succ_of_le hk)
      rwa [hAC, lsAccW_get hk] at this
    · have := Whir.readsAt_getD' hPWm (j := k) (by rw [hPWl]; exact Nat.lt_succ_of_le hk)
      rwa [hPW, lsPwW_get hk] at this
  obtain ⟨m, hm⟩ := lr_relAtIn_pure_uniform (ls_pureIn hloop hrqF) (List.mem_cons_self) fs cert hres
  refine ⟨m, fun rd hl hL ↦ ?_⟩
  rw [hLbE] at hL
  have hB := (Main.memL_append.mp hL).1
  have hACm : ReadsAt rd (ofK (addressOfIndex b)) AC := hB (b, AC) (by simp [hLb])
  have hPWm : ReadsAt rd (ofK (addressOfIndex (b + (Q + 1)))) PW := hB (b + (Q + 1), PW) (by simp [hLb])
  have hS := lsum_relAtIn hsum hQ hQb fs cert (rd := rd) (R := RegionL Lin) (Rk := RegionL Lk)
    (fp := fp + fs name) (m := m) (P := P) (F := F) (T := T) (lam := lam) hACm hACl
    (by rw [hAC, lsAccW_get (Nat.zero_le _)]; simp [lrsAcc])
    hPWm hPWl (by rw [hPW, lsPwW_get (Nat.zero_le _)]; ring)
    (hm _ rd hl (by rw [hLk]; exact hL)) hregK
  have hret : AC.getD Q 0 = slowVal Q n vo p cs lam 1 := by
    rw [hAC, lsAccW_get le_rfl, slowVal, ite_eq_right h10]
    rfl
  rw [hret] at hS
  have h := lrs_relAtIn1 hlrs fs cert hS (fun i hi ↦ hi)
  rw [lsN, ite_eq_right h10, show fs name + (fs sum + 2 * (Q + 1)) + m = fs name + (fs sum + 2 * (Q + 1) + m)
    by omega]
  exact h

end
end LeanVM.Guest.B1
