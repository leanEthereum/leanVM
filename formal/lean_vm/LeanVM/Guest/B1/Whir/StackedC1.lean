/-
  LeanVM.Guest.B1.Whir.StackedC1

  The completeness of `open_stacked`'s first blocks: the materialized pointers, `fs_next`, the
  fold rounds.
-/

module

public import LeanVM.Guest.B1.Whir.StackedInv
public import LeanVM.Guest.B1.Whir.StackedBlocks
public import LeanVM.Guest.B1.Whir.QueriesComplete

/-!
# `open_stacked`'s blocks, honestly: pointers, reads, folds (TRIAGE #36)

`OsAt σ st cv cur p`: the guest's state `st` against the chain state `cv` with `p` words of the
stream at `cur` read: the Fiat-Shamir cells are `cv`'s and the cursor points `p` words on. Every
block lemma takes the block's honest values at its value range (`*Vals`, a list from the block's
first value) and gives its relation and the state after it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The guest's state against the chain state `cv` and `p` words read from `cur`. -/
structure OsAt (σ : Val) (st : OsSt) (cv : Digest) (cur : E) (p : ℕ) : Prop where
  fs : (σ (.n st.f0), σ (.n st.f1)) = digestScalars cv
  cursor : σ (.n st.cb) * gen ^ st.co = cur * gen ^ p

/-! ## Pointers -/

/-- The values of `osMat base off k` from `k`, at the base `bv`. -/
def osMatVals (bv : E) (off : ℕ) : List E := if off = 0 then [] else [osGw off, bv * osGw off]

theorem osMat_next' (base off k : ℕ) : (osMat base off k).2.2 = k + (osMatVals 0 off).length := by
  unfold osMat osMatVals; split <;> simp

theorem os_length_matVals' (bv : E) (off : ℕ) : (osMatVals bv off).length = (osMatVals 0 off).length := by
  unfold osMatVals; split <;> simp

theorem osMat_complete {base off k : ℕ} (hoff : off < 2 ^ 128) {kret : List E → Prop}
    (hv : ∀ j < (osMatVals (σ (.n base)) off).length, σ (.n (k + j)) = (osMatVals (σ (.n base)) off).getD j 0) :
    Stmt.HoldsList C rd σ (osMat base off k).1 True kret ∧
      σ (.n (osMat base off k).2.1) = σ (.n base) * gen ^ off := by
  unfold osMat
  by_cases h0 : off = 0
  · simp [h0, Stmt.HoldsList]
  · have e0 := hv 0 (by simp [osMatVals, h0])
    have e1 := hv 1 (by simp [osMatVals, h0])
    simp only [osMatVals, h0, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1
    simp only [h0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨⟨e0, by rw [e1, e0]⟩, by rw [e1, os_gw_eq hoff]⟩

/-! ## `fs_next` -/

/-- The values of `osFsNext` from its first: the word `x`, then `fs_compress`'s. -/
def osFsNextVals (x : E) (cv : Digest) : List E := x :: (List.range 14).map (fsVals x cv 1)

theorem os_cursor_load {σ : Val} {st : OsSt} {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ st cv cur p)
    {j : ℕ} {w : E} (h : LoadHolds rd cur (p + j) w) :
    LoadHolds rd (σ (.n st.cb)) (st.co + j) w := by
  rw [← loadHolds_mul_gen_pow, hat.cursor, loadHolds_mul_gen_pow]
  exact h

/-- **`fs_next`** at its honest values: the word at the cursor read and absorbed. -/
theorem osFsNext_complete {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} (hat : OsAt σ s cv cur p)
    {x : E} (hx : LoadHolds rd cur p x) {kret : List E → Prop}
    (hv : ∀ j < 15, σ (.n (s.k + j)) = (osFsNextVals x cv).getD j 0) :
    Stmt.HoldsList C rd σ (osFsNext s).1 True kret ∧ OsAt σ (osFsNext s).2 (obsCv cv x) cur (p + 1) := by
  have e0 : σ (.n s.k) = x := by simpa [osFsNextVals] using hv 0 (by omega)
  have e : ∀ j < 14, σ (.n (s.k + 1 + j)) = fsVals x cv 1 j := fun j hj => by
    rw [show s.k + 1 + j = s.k + (j + 1) by ring, hv _ (by omega)]
    simp [osFsNextVals, List.getD_eq_getElem?_getD, hj]
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · show Stmt.HoldsList C rd σ (fsNextT (.n s.f0) (.n s.f1) (.n s.cb) s.co s.k) True kret
    rw [holds_fsNextT]
    refine ⟨⟨?_, cv, hat.fs, fun j h1 h2 => ?_⟩, trivial⟩
    · have hl := os_cursor_load (j := 0) hat (by rw [Nat.add_zero]; exact hx)
      rw [Nat.add_zero] at hl
      rw [e0]; exact hl
    · rw [e j h2, e0]
  · show (σ (.n (s.k + 13)), σ (.n (s.k + 14))) = _
    rw [show s.k + 13 = s.k + 1 + 12 by ring, show s.k + 14 = s.k + 1 + 13 by ring, e 12 (by omega),
      e 13 (by omega)]
    simp only [fsVals, absorbCv_one]
  · show σ (.n s.cb) * gen ^ (s.co + 1) = cur * gen ^ (p + 1)
    rw [pow_succ, pow_succ, ← mul_assoc, ← mul_assoc, hat.cursor]

/-! ## The fold rounds -/

/-- The values of one fold round from its first, the cursor at `bv·g^co`, `p` words read: the
pointer, `opening_fold`'s returns, the copies, the next quadratic's middle coefficient. -/
def osFoldVals (xs : List E) (cv : Digest) (p : ℕ) (q : List E) (bv : E) (co : ℕ) : List E :=
  let ch := challengeOf (sqCv cv)
  let t := polyEval q ch
  let d0 := xs.getD p 0
  let d2 := xs.getD (p + 1) 0
  let cv' := obsAll (sqCv cv) [d0, d2]
  osMatVals bv co ++ [(digestScalars cv').1, (digestScalars cv').2, bv * osGw co * gen ^ 2, t, d0, d2, ch,
    (digestScalars cv').1, (digestScalars cv').2, t + d2]

/-- `opening_fold`'s returns at a round. -/
def osFoldRets (xs : List E) (cv : Digest) (p : ℕ) (q : List E) (curv : E) : List E :=
  let ch := challengeOf (sqCv cv)
  let t := polyEval q ch
  let d0 := xs.getD p 0
  let d2 := xs.getD (p + 1) 0
  let cv' := obsAll (sqCv cv) [d0, d2]
  [(digestScalars cv').1, (digestScalars cv').2, curv * gen ^ 2, t, d0, d2, ch]

theorem os_range7 (r : ℕ) : ((List.range 7).map fun j => V.n (r + j)) =
    [.n r, .n (r + 1), .n (r + 2), .n (r + 3), .n (r + 4), .n (r + 5), .n (r + 6)] := by
  simp [List.range_succ]

/-- **One fold round** at its honest values, its call holding. -/
theorem osFold_complete {s : OsSt} {cv : Digest} {cur : E} {p : ℕ} {xs : List E} (hat : OsAt σ s cv cur p)
    (hco : s.co < 2 ^ 128) {fch fo : ℕ} {kret : List E → Prop}
    (hv : ∀ j < (osFoldVals xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co).length,
      σ (.n (s.k + j)) = (osFoldVals xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co).getD j 0)
    (hcall : C "opening_fold" [σ (.n s.f0), σ (.n s.f1), σ (.n s.cb) * gen ^ s.co, σ (.n s.c), σ (.n s.b),
      σ (.n s.a)] (osFoldRets xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb) * gen ^ s.co)))
    (hst : LoadHolds rd (σ (.n fch)) fo (challengeOf (sqCv cv))) :
    Stmt.HoldsList C rd σ (osFold s fch fo).1 True kret ∧
      OsAt σ (osFold s fch fo).2 (obsAll (sqCv cv) [xs.getD p 0, xs.getD (p + 1) 0]) cur (p + 2) ∧
      (osFold s fch fo).2.co = 0 ∧
      σ (.n (osFold s fch fo).2.t) = polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCv cv)) ∧
      [σ (.n (osFold s fch fo).2.c), σ (.n (osFold s fch fo).2.b), σ (.n (osFold s fch fo).2.a)] =
        [xs.getD p 0, polyEval [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (challengeOf (sqCv cv)) +
          xs.getD (p + 1) 0, xs.getD (p + 1) 0] ∧
      (osFold s fch fo).2.k = s.k + (osFoldVals xs cv p [σ (.n s.c), σ (.n s.b), σ (.n s.a)] (σ (.n s.cb)) s.co).length := by
  set q := [σ (.n s.c), σ (.n s.b), σ (.n s.a)]
  set M := osMatVals (σ (.n s.cb)) s.co with hM
  set ch := challengeOf (sqCv cv)
  set t := polyEval q ch
  set d0 := xs.getD p 0
  set d2 := xs.getD (p + 1) 0
  set cv' := obsAll (sqCv cv) [d0, d2]
  set T : List E := [(digestScalars cv').1, (digestScalars cv').2, σ (.n s.cb) * osGw s.co * gen ^ 2, t, d0, d2, ch,
    (digestScalars cv').1, (digestScalars cv').2, t + d2] with hT
  have hvals : osFoldVals xs cv p q (σ (.n s.cb)) s.co = M ++ T := rfl
  rw [hvals] at hv
  have hlen : (M ++ T).length = M.length + 10 := by simp [hT]
  have hr : (osMat s.cb s.co s.k).2.2 = s.k + M.length := by
    rw [osMat_next', hM, os_length_matVals' (σ (.n s.cb))]
  have hm := osMat_complete (C := C) (rd := rd) (σ := σ) (base := s.cb) (k := s.k) (kret := kret) hco fun j hj => by
    rw [hv j (by rw [hlen, hM]; omega), oq_getD_app_lt hj]
  have gT : ∀ j < 10, σ (.n ((osMat s.cb s.co s.k).2.2 + j)) = T.getD j 0 := fun j hj => by
    rw [hr, show s.k + M.length + j = s.k + (M.length + j) by ring, hv _ (by rw [hlen]; omega),
      oq_getD_app_ge (by omega), Nat.add_sub_cancel_left]
  have hgw : σ (.n s.cb) * osGw s.co = σ (.n s.cb) * gen ^ s.co := by rw [os_gw_eq hco]
  generalize hR : (osMat s.cb s.co s.k).2.2 = r at gT hr
  have g := fun j (hj : j < 10) => gT j hj
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega)
  have g3 := g 3 (by omega); have g4 := g 4 (by omega); have g5 := g 5 (by omega)
  have g6 := g 6 (by omega); have g7 := g 7 (by omega); have g8 := g 8 (by omega)
  have g9 := g 9 (by omega)
  simp only [hT, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  unfold osFold
  dsimp only
  rw [hR]
  refine ⟨?_, ⟨?_, ?_⟩, rfl, g3, ?_, by rw [hvals, hlen, hr]; ring⟩
  · rw [holdsList_append]
    refine (holdsList_noRet _ (osMat_noRet _ _ _) _ _).mpr ⟨hm.1, ?_⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, os_range7, List.map_cons, List.map_nil, and_true]
    refine ⟨?_, by rw [g7, g0], by rw [g8, g1], by rw [g6]; exact hst, by rw [g9, g3, g5]⟩
    rw [hm.2, g0, g1, g2, g3, g4, g5, g6, hgw]
    exact hcall
  · show (σ (.n (r + 7)), σ (.n (r + 8))) = _
    rw [g7, g8]
  · show σ (.n (r + 2)) * gen ^ 0 = cur * gen ^ (p + 2)
    rw [g2, pow_zero, mul_one, hgw, hat.cursor, mul_assoc, ← pow_add]
  · show [σ (.n (r + 4)), σ (.n (r + 9)), σ (.n (r + 5))] = _
    rw [g4, g9, g5]

end
end LeanVM.Guest.B1
