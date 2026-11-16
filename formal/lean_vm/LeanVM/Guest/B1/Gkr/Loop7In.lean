/-
  LeanVM.Guest.B1.Gkr.Loop7In

  `verify_bus_gkr_loop0` loads from any region holding, at each iteration, its layer slot, its row,
  its round records and the words at the records' cursors.
-/

module

public import LeanVM.Guest.B1.Gkr.Layer
public import LeanVM.Guest.B1.Gkr.RoundsIn
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr_loop0`, loading from a region

`verify_bus_gkr_loop0`'s body is straight but for a branch on `odd_g` between two blocks of
straight statements, ending in `gkr_rounds__L2` (an even depth) or `gkr_rounds__L1`: it walks its
statements in turn and the block taken (`ly_walk`).

* `Ly7In`: what iteration `j` reads, in `R`: the slot of `L = 2j + 2 - sh` (`30` words, through
  the next slot's stores) and its position; its row of the point triangle (`L + 43` words); the
  records from `rounds·pos` (`j + 5174` words), record `y ≤ j`'s cursor `cj·g^(8y)`, the last
  one's `cj·g^(4L)`, and the `4L + 12` words from `cj`.
* `loop7_relIn`: with those at every `j < m` in `R`, iteration `j < m` of `verify_bus_gkr_loop0`
  loads from `R`, by the depth of its derivation; its rounds by `loop29_relIn` and
  `gkr_rounds_relIn`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## The walk -/

/-- A block of straight statements walks each, falling through. -/
theorem walk_straight_fall (σ : Val) {z : List Stmt} (h : z.all Main.Stmt.straight = true) :
    walk σ z = .fall (z.flatMap (Main.slEvs σ)) := by
  have e := walk_pre_straight σ [] z h
  rw [List.append_nil] at e
  rw [e, walk, Out.pre, List.append_nil]

/-- A branch between blocks of straight statements: its condition, then the block taken. -/
theorem walk1_ite_straight (σ : Val) (c : V) {z n : List Stmt}
    (hz : z.all Main.Stmt.straight = true) (hn : n.all Main.Stmt.straight = true) :
    walk1 σ (.ite c z n) = .fall (.inK c :: (if σ c = 0 then z else n).flatMap (Main.slEvs σ)) := by
  rw [walk1]
  by_cases hc : σ c = 0
  · simp only [hc, ↓reduceIte, walk_straight_fall σ hz, Out.pre, List.singleton_append]
  · simp only [hc, ↓reduceIte, walk_straight_fall σ hn, Out.pre, List.singleton_append]

/-- `verify_bus_gkr_loop0`'s statements before the branch on `odd_g`. -/
noncomputable def lyA : List Stmt := lyBody.take 53

/-- `verify_bus_gkr_loop0`'s statements after the branch, before its `ret`. -/
noncomputable def lyB : List Stmt := lyPre.drop 54

theorem lyBody_split : lyBody = lyA ++ (.ite (.n 67) ly72 ly71 :: (lyB ++ [.ret []])) :=
  tbStmtsEqb_sound (by decide +kernel)

theorem lyA_straight : lyA.all Main.Stmt.straight = true := by decide +kernel
theorem lyB_straight : lyB.all Main.Stmt.straight = true := by decide +kernel
theorem ly72_straight : ly72.all Main.Stmt.straight = true := by decide +kernel
theorem ly71_straight : ly71.all Main.Stmt.straight = true := by decide +kernel

theorem lyA_calls : lyA.filterMap Main.Stmt.callS =
    [(some (.n 62), name% «verify_bus_gkr_loop0_loop0», [.n 63, .n 0, .n 56, .n 55, .n 4],
        [])] := by decide +kernel

theorem lyB_calls : lyB.filterMap Main.Stmt.callS =
    [(some (.n 234), name% «verify_bus_gkr_loop0», [.n 236, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6,
        .n 7, .n 8, .n 9, .n 10],
      [])] := by
  decide +kernel

theorem lyA_loads : lyA.all (loadsViaB [(17, 10), (56, 5173), (64, 4311)]) = true := by
  decide +kernel

theorem lyB_loads : lyB.all (loadsViaB [(17, 30), (55, 42), (74, 5173), (80, 12)]) = true := by
  decide +kernel

/-- **`verify_bus_gkr_loop0`'s walk**: its statements in turn, the block taken. -/
theorem ly_walk (σ : Val) :
    walk σ lyBody = .ret (lyA.flatMap (Main.slEvs σ) ++
      (.inK (.n 67) :: (if σ (.n 67) = 0 then ly72 else ly71).flatMap (Main.slEvs σ)) ++
        lyB.flatMap (Main.slEvs σ)) [] := by
  rw [lyBody_split, walk_pre_straight σ _ lyA lyA_straight, walk,
    walk1_ite_straight σ _ ly72_straight ly71_straight, Main.walk_straight σ [] lyB lyB_straight]
  simp only [Out.seq, Out.pre, List.append_assoc]

theorem tb_lName_gkr_rounds : lName "gkr_rounds" 1 = "gkr_rounds__L1" ∧
    lName "gkr_rounds" 2 = "gkr_rounds__L2" :=
  ⟨rfl, rfl⟩

/-! ## The iterations -/

/-- **What iteration `j` reads, in `R`**: the slot of `L = 2j + 2 - sh` through the next slot's
stores and its position; the point row; the round records from `rounds·pos`, record `y ≤ j`'s
cursor `cj·g^(8y)`, the last one's `cj·g^(4L)`, and the words from `cj` the rounds and the
children read. -/
def Ly7In (rd : Reader) (R : ℕ → Prop) (layers pts rounds : E) (sh j : ℕ) : Prop :=
  ∃ pos cj : E,
    PtrIn R (layers * gen ^ (10 * (2 * j + 2 - sh))) 30 ∧
    LoadHolds rd layers (10 * (2 * j + 2 - sh) + 9) pos ∧
    PtrIn R (pts * gen ^ (40 * (j + 1))) (2 * j + 2 - sh + 43) ∧
    PtrIn R (rounds * pos) (j + 5174) ∧ PtrIn R cj (4 * (2 * j + 2 - sh) + 12) ∧
    (∀ y ≤ j, LoadHolds rd (rounds * pos * gen ^ y) 4310 (cj * gen ^ (8 * y))) ∧
    LoadHolds rd (rounds * pos * gen ^ (j + 1)) 4310 (cj * gen ^ (4 * (2 * j + 2 - sh)))

/-- **`verify_bus_gkr_loop0` loads from `R`**, every iteration `j < m`, its slots, rows, records and
cursors in `R` (`Ly7In`). -/
theorem loop7_relIn {rd : Reader} {R : ℕ → Prop} {layers tabs pts rounds u stream gmu : E}
    {sh m : ℕ} (hsh2 : sh < 2) (hit : ∀ j < m, Ly7In rd R layers pts rounds sh j) :
    ∀ d j, j < m →
      coreProgram.relN rd d name% «verify_bus_gkr_loop0» [gen ^ j, gen ^ m, gen ^ (2 - sh), layers,
          tabs, pts, rounds, u, gen ^ sh, stream, gmu] [] →
      coreProgram.RelIn rd R name% «verify_bus_gkr_loop0» [gen ^ j, gen ^ m, gen ^ (2 - sh),
          layers, tabs, pts, rounds, u, gen ^ sh, stream, gmu] [] := by
  intro d
  induction d with
  | zero => intro j _ h; exact h.elim
  | succ d ih =>
    intro j hj h
    obtain ⟨fn, hf, hsem⟩ := h
    obtain ⟨fn', hf', hpm, hb⟩ := lyFound
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    obtain ⟨pos, cj, hRL, hpos, hRrow, hRrec, hRcur, hcur, hcurL⟩ := hit j hj
    set L := 2 * j + 2 - sh with hL
    refine relIn_of_sem hf hsem fun σ hpar' hhl es vs hw ↦ ?_
    rw [hpm] at hpar'
    have hpar'' : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
        σ (.n 8), σ (.n 9), σ (.n 10)] = [gen ^ j, gen ^ m, gen ^ (2 - sh), layers, tabs, pts,
        rounds, u, gen ^ sh, stream, gmu] := hpar'
    simp only [List.cons.injEq, and_true] at hpar''
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ := hpar''
    rw [hb, lyBody_eq, holdsList_append, holdsList_noRet _ lyPre_noRet] at hhl
    have hP := hhl.1
    have hnr := lyPre_noRet
    have a := fun n a heq ↦ tb_holds_atom hnr hP n a heq
    have m11 := a 0 (.mul (.n 11) (.n 0) (.n 0)) (by decide +kernel)
    have m12 := a 1 (.mul (.n 12) (.n 11) (.n 2)) (by decide +kernel)
    have m13 := a 2 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel)
    have m14 := a 3 (.mul (.n 14) (.n 13) (.n 13)) (by decide +kernel)
    have m15 := a 4 (.mul (.n 15) (.n 14) (.n 12)) (by decide +kernel)
    have m16 := a 5 (.mul (.n 16) (.n 15) (.n 15)) (by decide +kernel)
    have m17 := a 6 (.mul (.n 17) (.n 3) (.n 16)) (by decide +kernel)
    have l46 := a 23 (.load (.n 46) (.n 17) 9) (by decide +kernel)
    have c47 := a 24 (.const (.n 47) (word 2 0)) (by decide +kernel)
    have m48 := a 25 (.mul (.n 48) (.n 0) (.n 47)) (by decide +kernel)
    have m49 := a 26 (.mul (.n 49) (.n 48) (.n 48)) (by decide +kernel)
    have m50 := a 27 (.mul (.n 50) (.n 49) (.n 49)) (by decide +kernel)
    have m51 := a 28 (.mul (.n 51) (.n 50) (.n 48)) (by decide +kernel)
    have m52 := a 29 (.mul (.n 52) (.n 51) (.n 51)) (by decide +kernel)
    have m53 := a 30 (.mul (.n 53) (.n 52) (.n 52)) (by decide +kernel)
    have m54 := a 31 (.mul (.n 54) (.n 53) (.n 53)) (by decide +kernel)
    have m55 := a 32 (.mul (.n 55) (.n 5) (.n 54)) (by decide +kernel)
    have m56 := a 33 (.mul (.n 56) (.n 6) (.n 46)) (by decide +kernel)
    have c61 := a 45 (.const (.n 61) (word 1 0)) (by decide +kernel)
    have a62 := a 46 (.add (.n 62) (.n 61) (.n 0)) (by decide +kernel)
    have c63 := a 47 (.const (.n 63) (word 1 0)) (by decide +kernel)
    have m64 := a 49 (.mul (.n 64) (.n 56) (.n 0)) (by decide +kernel)
    have l65 := a 50 (.load (.n 65) (.n 64) 4310) (by decide +kernel)
    have c66 := a 51 (.const (.n 66) (word 1 0)) (by decide +kernel)
    have a67 := a 52 (.add (.n 67) (.n 8) (.n 66)) (by decide +kernel)
    have m72 := a 54 (.mul (.n 72) (.n 56) (.n 0)) (by decide +kernel)
    have c73 := a 55 (.const (.n 73) (word 2 0)) (by decide +kernel)
    have m74 := a 56 (.mul (.n 74) (.n 72) (.n 73)) (by decide +kernel)
    have l80 := a 62 (.load (.n 80) (.n 74) 4310) (by decide +kernel)
    have c232 := a 179 (.const (.n 232) (word 2 0)) (by decide +kernel)
    have m233 := a 180 (.mul (.n 233) (.n 0) (.n 232)) (by decide +kernel)
    have a234 := a 181 (.add (.n 234) (.n 233) (.n 1)) (by decide +kernel)
    have c235 := a 182 (.const (.n 235) (word 2 0)) (by decide +kernel)
    have m236 := a 183 (.mul (.n 236) (.n 0) (.n 235)) (by decide +kernel)
    simp only [Atom.Holds] at m11 m12 m13 m14 m15 m16 m17 l46 c47 m48 m49 m50 m51 m52 m53 m54
    simp only [Atom.Holds] at m55 m56 c61 a62 c63 m64 l65 c66 a67 m72 c73 m74 l80
    simp only [Atom.Holds] at c232 m233 a234 c235 m236
    rw [tb_word_one] at c61 c63 c66
    rw [tb_word_gen] at c47 c73 c232 c235
    have e11 : σ (.n 11) = gen ^ (2 * j) := by rw [m11, p0, ← pow_add]; ring_nf
    have e12 : σ (.n 12) = gen ^ L := by
      rw [m12, e11, p2, ← pow_add, show 2 * j + (2 - sh) = L by omega]
    have e17 : σ (.n 17) = layers * gen ^ (10 * L) := by
      rw [m17, m16, m15, m14, m13, e12, p3, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      ring_nf
    have e46 : σ (.n 46) = pos := by
      rw [e17, tb_loadHolds_mul_gen_pow] at l46; exact tb_loadHolds_unique l46 hpos
    have e55 : σ (.n 55) = pts * gen ^ (40 * (j + 1)) := by
      rw [m55, m54, m53, m52, m51, m50, m49, m48, c47, p0, p5, ← pow_succ]
      ring
    have e56 : σ (.n 56) = rounds * pos := by rw [m56, p6, e46]
    have e64 : σ (.n 64) = rounds * pos * gen ^ j := by rw [m64, e56, p0]
    have e74 : σ (.n 74) = rounds * pos * gen ^ (j + 1) := by
      rw [m74, m72, e56, p0, c73, pow_succ, mul_assoc]
    rw [e64] at l65
    rw [e74] at l80
    have e65 := tb_loadHolds_unique l65 (hcur j le_rfl)
    have e80 := tb_loadHolds_unique l80 hcurL
    rw [hb, ly_walk σ] at hw
    injection hw with hes _
    subst hes
    refine ⟨fun A hA ↦ ?_, fun c hc ht ↦ ?_⟩
    · -- the loads
      have hbr : loadAddrs σ (.inK (.n 67) :: (if σ (.n 67) = 0 then ly72 else ly71).flatMap
          (Main.slEvs σ)) = [] := by
        show loadAddrs σ ((if σ (.n 67) = 0 then ly72 else ly71).flatMap (Main.slEvs σ)) = []
        split
        · rw [B1.loadAddrs_straight σ ly72 ly72_straight, show ly72.filterMap Stmt.loadS = [] by
            decide +kernel]; rfl
        · rw [B1.loadAddrs_straight σ ly71 ly71_straight, show ly71.filterMap Stmt.loadS = [] by
            decide +kernel]; rfl
      rw [loadAddrs_append, loadAddrs_append, hbr, B1.loadAddrs_straight σ lyA lyA_straight,
        B1.loadAddrs_straight σ lyB lyB_straight] at hA
      simp only [List.append_nil, List.mem_append, List.mem_map] at hA
      rcases hA with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · refine loads_via lyA_loads (fun pb hpb ↦ ?_) q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
        rcases hpb with rfl | rfl | rfl
        · rw [e17]; exact ptrIn_mono hRL (by omega)
        · rw [e56]; exact ptrIn_mono hRrec (by omega)
        · rw [e64]; exact ptrIn_mul (ptrIn_mono hRrec (by omega))
      · refine loads_via lyB_loads (fun pb hpb ↦ ?_) q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
        rcases hpb with rfl | rfl | rfl | rfl
        · rw [e17]; exact hRL
        · rw [e55]; exact ptrIn_mono hRrow (by omega)
        · rw [e74]; exact ptrIn_mul (ptrIn_mono hRrec (by omega))
        · rw [e80]; exact ptrIn_mul (ptrIn_mono hRcur (by omega))
    · -- the calls
      have hbr : calls (.inK (.n 67) :: (if σ (.n 67) = 0 then ly72 else ly71).flatMap
          (Main.slEvs σ)) = if σ (.n 67) = 0 then (ly72.filterMap Main.Stmt.callS).map
            (Main.mkCall σ) else (ly71.filterMap Main.Stmt.callS).map (Main.mkCall σ) := by
        show calls ((if σ (.n 67) = 0 then ly72 else ly71).flatMap (Main.slEvs σ)) = _
        split
        · exact (Main.straight_parts σ ly72 ly72_straight).2.2.2
        · exact (Main.straight_parts σ ly71 ly71_straight).2.2.2
      rw [calls_append, calls_append, hbr, (Main.straight_parts σ lyA lyA_straight).2.2.2,
        (Main.straight_parts σ lyB lyB_straight).2.2.2, lyA_calls, lyB_calls] at hc
      simp only [List.mem_append] at hc
      have hi := tb_holds_slice hnr hP 53 [.ite (.n 67) ly72 ly71] (by decide +kernel)
      simp only [Stmt.HoldsList] at hi
      rw [tb_holds_ite_noRet _ _ _ (by decide +kernel) (by decide +kernel)] at hi
      obtain ⟨⟨-, heven, hodd⟩, -⟩ := hi
      rcases hc with (hc | hc) | hc
      · -- `verify_bus_gkr_loop0_loop0`
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
        have hci := tb_holds_callIf hnr hP 48 (.n 62) name% «verify_bus_gkr_loop0_loop0»
          [.n 63, .n 0, .n 56, .n 55, .n 4] (by decide +kernel)
        have hrel := hci.2 ht
        have hK : 0 < j := by
          rcases Nat.eq_zero_or_pos j with h0 | h0
          · exfalso; apply ht
            rw [a62, c61, p0, h0, pow_zero, e_add_self]
          · exact h0
        simp only [List.map_cons, List.map_nil, c63, p0, e56, e55, p4] at hrel ⊢
        rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at hrel ⊢
        exact loop29_relIn (ptrIn_mono hRrec (by omega)) (ptrIn_mono hRrow (by omega))
          (fun k' hk' c hc ↦ by
            rw [tb_loadHolds_unique hc (hcur k' (by omega))]
            exact ptrIn_mul (ptrIn_mono hRcur (by omega))) d 0 hK hrel
      · -- `gkr_rounds__L2` or `gkr_rounds__L1`
        have hcurIn : PtrIn R (σ (.n 65)) (4 * (2 - sh)) := by
          rw [e65]; exact ptrIn_mul (ptrIn_mono hRcur (by omega))
        have hrec : PtrIn R (σ (.n 64)) 5174 := by
          rw [e64]; exact ptrIn_mul (ptrIn_mono hRrec (by omega))
        have hrow : ∀ v, σ v = σ (.n 55) * σ (.n 11) → PtrIn R (σ v) (43 + (2 - sh)) := by
          intro v hv
          rw [hv, e55, e11]; exact ptrIn_mul (ptrIn_mono hRrow (by omega))
        split at hc
        · rename_i h67
          have hsh0 : sh = 0 := by
            by_contra h1
            rw [a67, c66, p8, show sh = 1 by omega, pow_one] at h67
            have := gen_pow_inj (a := 1) (b := 0) (by omega) (by omega)
              ((pow_one gen).trans ((e_add_eq_zero_iff.mp h67).trans (pow_zero gen).symm))
            omega
          rw [show ly72.filterMap Main.Stmt.callS =
            [(none, "gkr_rounds__L2", [.n 64, .n 68, .n 65, .n 4, .n 9], [.n 69])] by
              decide +kernel] at hc
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
          subst hc
          simp only [ly72, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
            and_true] at heven
          obtain ⟨m68, hrel⟩ := heven h67
          simp only [Main.mkCall, List.map_cons, List.map_nil]
          rw [← tb_lName_gkr_rounds.2] at hrel ⊢
          subst hsh0
          exact gkr_rounds_relIn (by simp [grCounts]) hrec (hrow _ m68) hcurIn ⟨d, hrel⟩
        · rename_i h67
          have hsh1 : sh = 1 := by
            by_contra h0
            apply h67
            rw [a67, c66, p8, show sh = 0 by omega, pow_zero, e_add_self]
          rw [show ly71.filterMap Main.Stmt.callS =
            [(none, "gkr_rounds__L1", [.n 64, .n 70, .n 65, .n 4, .n 9], [.n 71])] by
              decide +kernel] at hc
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
          subst hc
          simp only [ly71, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
            and_true] at hodd
          obtain ⟨m70, hrel⟩ := hodd h67
          simp only [Main.mkCall, List.map_cons, List.map_nil]
          rw [← tb_lName_gkr_rounds.1] at hrel ⊢
          subst hsh1
          exact gkr_rounds_relIn (by simp [grCounts]) hrec (hrow _ m70) hcurIn ⟨d, hrel⟩
      · -- the next iteration
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
        have hci := tb_holds_callIf hnr hP 184 (.n 234) name% «verify_bus_gkr_loop0»
          [.n 236, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10] (by decide +kernel)
        have hrel := hci.2 ht
        have e236 : σ (.n 236) = gen ^ (j + 1) := by rw [m236, c235, p0, pow_succ]
        have e234 : σ (.n 234) = gen ^ (j + 1) + gen ^ m := by
          rw [a234, m233, c232, p0, p1, pow_succ]
        have hj1 : j + 1 < m := by
          rcases Nat.lt_or_ge (j + 1) m with h' | h'
          · exact h'
          · exfalso
            apply ht
            rw [e234, show j + 1 = m by omega, e_add_eq_zero_iff]
        simp only [List.map_cons, List.map_nil, e236, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
          at hrel ⊢
        exact ih (j + 1) hj1 hrel

end
end LeanVM.Guest.B1.Tables
