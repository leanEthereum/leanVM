/-
  LeanVM.Guest.B1.VsC.SlowC

  The slow residual completes, layout-free: `residual_query_slow`, the loop of
  `level_residual_sum`, `level_residual_sum` and `level_residual_slow`.
-/

module

public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.B1.VsC.Quiet
public import LeanVM.Guest.B1.VsC.Mono
public import LeanVM.Guest.B1.Whir.SlowSound
public import LeanVM.Guest.Complete.Compose
public import LeanVM.Guest.Memory.Straight
import LeanVM.Guest.B1.Common.Vc

/-!
# The slow residual, complete

On a level whose challenges' product is zero, `open_stacked` sums the queries' unfactored weights
(`level_residual_slow`). Each specialization is its template (`Whir/SlowT.lean`, checked by the
guest stream's `lrsTable_ok`, `rqsTable_ok`), so the proofs here are over the templates.

* `rqs_complete`: `residual_query_slow` on `[x, fold_cs, tail_cs]`, the challenges at `fold_cs` and
  `tail_cs` (`CsAt`), returns the product of its factors (`rqsW`), by `callCompletes0_pure`, with no
  words of its own (`CallCompletes0`).
* `lp_loop`: the loop of `level_residual_sum` from iteration `j`, on a memory holding the sum's
  buffers' honest words (`accL`, `pwL`), the positions and the challenges, with no words of its own.
* `lsum_complete`: `level_residual_sum` returns `lrsAcc … Q`, its two buffers its own words.
* `lrs_complete`: `level_residual_slow` returns `slowVal`, at every flag in `K`.

Each pops nothing and is exact (`PostQuiet`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Generic facts -/

/-- A word `j + k` of a run, read at `p·g^j`. -/
theorem readsAt_at {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) {j k : ℕ} {w : E}
    (hk : j + k < l.length) (hw : l[j + k] = w) : LoadHolds rd (p * gen ^ j) k w := by
  rw [loadHolds_mul_gen_pow]
  have := h (j + k) hk
  rwa [hw] at this

/-- The run `f 0, …, f (n - 1)` at `p`. -/
theorem readsAt_map_range {rd : Reader} {p : E} {n : ℕ} {f : ℕ → E}
    (h : ∀ k < n, LoadHolds rd p k (f k)) : ReadsAt rd p ((List.range n).map f) := by
  intro k hk
  simp only [List.length_map, List.length_range] at hk
  simpa using h k hk

/-- A hint that allocates or is a witness is exact; so is every other atom. -/
def trivExact : Atom → Bool
  | .hint (.allocDyn ..) => true
  | .hint (.alloc ..) => true
  | .hint (.witness ..) => true
  | .hint _ => false
  | _ => true

theorem exact_of_trivExact {rd : Reader} {σ : Val} {a : Atom} (h : trivExact a = true) :
    a.Exact rd σ := by
  cases a with
  | hint hh => cases hh <;> simp_all [trivExact, Atom.Exact, Hint.Exact]
  | _ => trivial

theorem flatMap_atoms (σ : Val) : ∀ l : List Atom, (l.map Stmt.atom).flatMap (slEvs σ) = l.map Ev.atom
  | [] => rfl
  | a :: l => by rw [List.map_cons, List.flatMap_cons, flatMap_atoms σ l]; rfl

theorem wordsIn_single (b : ℕ) (l : List E) : WordsIn [(b, l)] b l.length :=
  ⟨by simp, List.pairwise_singleton _ _⟩

theorem one_isInK : IsInK (1 : E) := by
  have := gen_pow_isInK 0
  rwa [pow_zero] at this

/-! ## `residual_query_slow` -/

/-- A query's unfactored weight at `x`. -/
abbrev rqsW (n vo : ℕ) (cs : ℕ → E) (x : E) : E := ∏ t ∈ Finset.range n, rqsFac vo n cs x t

/-- The `pre` fold challenges at `fc`, the `yr` tail challenges at `tc`. -/
def CsAt (pre yr : ℕ) (fc tc : E) (cs : ℕ → E) (rd : Reader) : Prop :=
  (∀ t < pre, LoadHolds rd fc t (cs t)) ∧ ∀ j < yr, LoadHolds rd tc j (cs (pre + j))

/-- What `residual_query_slow__L{pre}_L{yr}_L{vo}`'s completeness gives, with no words of its own. -/
def RqsComplete (kd : ℕ) (name : String) (pre yr vo : ℕ) : Prop :=
  ∀ (x fc tc : E) (cs : ℕ → E), CallCompletes0 kd name [x, fc, tc] [rqsW (pre + yr) vo cs x]
    (CsAt pre yr fc tc cs) PostQuiet

/-- What the kernel checks of every `residual_query_slow`: a pure body reading its challenges. -/
theorem rqsTable_pure : ∀ e ∈ rqsTable,
    pureChecks 3 [(1, e.2.1), (2, e.2.2.1)] (rqsBody e.2.1 e.2.2.1 e.2.2.2) = true := by
  decide +kernel

/-- **Every `residual_query_slow` completes**, returning the query's weight. -/
theorem rqs_complete (kd : ℕ) : ∀ e ∈ rqsTable, RqsComplete kd e.1 e.2.1 e.2.2.1 e.2.2.2 := by
  intro e he x fc tc cs
  obtain ⟨fn, hfn, hp, hb⟩ := rqsTable_ok e he
  obtain ⟨hpre, hinv⟩ := rqsTable_shapes e he
  refine callCompletes0_pure [(1, e.2.1), (2, e.2.2.1)] hfn (by rw [hp]; rfl)
    (by rw [hb]; exact rqsTable_pure e he) (by simp) (fun rd _ hP q hq => ?_) (fun rd _ hP r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨(List.range e.2.1).map cs, by simp, readsAt_map_range hP.1⟩
    · exact ⟨(List.range e.2.2.1).map fun j => cs (e.2.1 + j), by simp, readsAt_map_range hP.2⟩
  · obtain ⟨d, hd⟩ := hr
    cases d with
    | zero => exact hd.elim
    | succ d =>
      rw [LeanVM.Guest.B1.relN_succ_iff_fnSem hfn] at hd
      exact rqs_sound hpre hinv (hp.trans osParams_three) hb hd hP.1 hP.2

/-! ## The loop of `level_residual_sum` -/

/-- `acc`'s honest words: `acc[j] = λ²·Σ_{k<j} λ^k·w_k`. -/
def accL (Q n vo : ℕ) (pos cs : ℕ → E) (lam : E) : List E :=
  (List.range (Q + 1)).map (lrsAcc n vo pos cs lam)

/-- `pw`'s honest words: `pw[j] = λ²·λ^j`. -/
def pwL (Q : ℕ) (lam : E) : List E := (List.range (Q + 1)).map fun j => lam ^ 2 * lam ^ j

/-- The `Q` positions. -/
def posL (Q : ℕ) (pos : ℕ → E) : List E := (List.range Q).map pos

/-- What the loop reads: the buffers' honest words, the positions and the challenges. -/
def LpPre (Q pre yr vo : ℕ) (acc pw posp fc tc lam : E) (pos cs : ℕ → E) (rd : Reader) : Prop :=
  ReadsAt rd acc (accL Q (pre + yr) vo pos cs lam) ∧ ReadsAt rd pw (pwL Q lam) ∧
    ReadsAt rd posp (posL Q pos) ∧ CsAt pre yr fc tc cs rd

/-- The loop's atoms before its call. -/
def lpA1 : List Atom :=
  [.mul (.n 8) (.n 2) (.n 0), .load (.n 9) (.n 8) 0,
    .mul (.n 10) (.n 3) (.n 0), .load (.n 11) (.n 10) 0,
    .mul (.n 12) (.n 4) (.n 0), .load (.n 13) (.n 12) 0]

/-- The loop's atoms after its call. -/
def lpA2 : List Atom :=
  [.mul (.n 15) (.n 11) (.n 14), .add (.n 16) (.n 9) (.n 15),
    .mul (.n 17) (.n 2) (.n 0), .load (.n 16) (.n 17) 1,
    .mul (.n 18) (.n 3) (.n 0), .load (.n 19) (.n 18) 0,
    .mul (.n 20) (.n 19) (.n 7),
    .mul (.n 21) (.n 3) (.n 0), .load (.n 20) (.n 21) 1,
    .const (.n 22) (word 2 0), .mul (.n 23) (.n 0) (.n 22),
    .add (.n 24) (.n 23) (.n 1),
    .const (.n 25) (word 2 0), .mul (.n 26) (.n 0) (.n 25)]

/-- The loop's arguments to itself. -/
def lpSelfArgs : List V := [.n 26, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]

/-- The loop's body before its `ret`. -/
def lpPre (rq self : String) : List Stmt :=
  lpA1.map .atom ++ [.call rq [.n 13, .n 5, .n 6] [.n 14]] ++ lpA2.map .atom ++
    [.callIf (.n 24) self lpSelfArgs]

theorem lpBody_eq (rq self : String) : lrsLoopBody rq self = lpPre rq self ++ [.ret []] := rfl

theorem lpPre_straight (rq self : String) : (lpPre rq self).all Stmt.straight = true := rfl

theorem lp_evs (σ : Val) (rq self : String) : (lpPre rq self).flatMap (slEvs σ) =
    lpA1.map .atom ++ [.call rq [.n 13, .n 5, .n 6] [.n 14]] ++ lpA2.map .atom ++
      [.inK (.n 24), if σ (.n 24) = 0 then .skip self lpSelfArgs else .call self lpSelfArgs []] := rfl

theorem lp_calls (σ : Val) (rq self : String) : calls ((lpPre rq self).flatMap (slEvs σ)) =
    [⟨rq, [.n 13, .n 5, .n 6], [.n 14], true⟩, ⟨self, lpSelfArgs, [], decide (σ (.n 24) ≠ 0)⟩] := by
  rw [(straight_parts σ _ (lpPre_straight rq self)).2.2.2]
  rfl

/-- The loop's arguments at iteration `j`. -/
def lpArgs (j Q : ℕ) (acc pw posp fc tc lam : E) : List E := [gen ^ j, gen ^ Q, acc, pw, posp, fc, tc, lam]

/-- Iteration `j`'s words: `a = acc[j]`, `p = pw[j]`, `x` the position, `w` its weight. -/
def lpVals (j Q : ℕ) (acc pw posp fc tc lam a p x w : E) : List E :=
  [gen ^ j, gen ^ Q, acc, pw, posp, fc, tc, lam,
    acc * gen ^ j, a, pw * gen ^ j, p, posp * gen ^ j, x, w,
    p * w, a + p * w, acc * gen ^ j, pw * gen ^ j, p, p * lam, pw * gen ^ j,
    gen, gen ^ (j + 1), gen ^ (j + 1) + gen ^ Q, gen, gen ^ (j + 1)]

theorem lrsAcc_succ (n vo : ℕ) (pos cs : ℕ → E) (lam : E) (j : ℕ) :
    lrsAcc n vo pos cs lam (j + 1) =
      lrsAcc n vo pos cs lam j + lam ^ 2 * lam ^ j * rqsW n vo cs (pos j) := by
  simp only [lrsAcc, Finset.sum_range_succ, mul_add]
  ring

theorem gen_add_ne' {a b : ℕ} (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1) :
    gen ^ a + gen ^ b = 0 ↔ a = b := by
  refine ⟨fun h => gen_pow_inj ha hb (CharTwo.add_eq_zero.mp h), fun h => ?_⟩
  rw [h]; exact CharTwo.add_self_eq_zero _

/-- **One iteration of the loop completes**, the next one completing when `j + 1 < Q`. -/
theorem lp_step {kd : ℕ} {rq self : String} {f : Fn} (hfind : coreProgram.find? self = some f)
    (hparams : f.params = osParams 8) (hbody : f.body = lrsLoopBody rq self) {Q pre yr vo : ℕ}
    (hrq : RqsComplete kd rq pre yr vo) (hQ : Q < 2 ^ 30)
    (acc pw posp fc tc lam : E) (pos cs : ℕ → E) {j : ℕ} (hj : j < Q)
    (hnext : j + 1 < Q → CallCompletes0 kd self (lpArgs (j + 1) Q acc pw posp fc tc lam) []
      (LpPre Q pre yr vo acc pw posp fc tc lam pos cs) PostQuiet) :
    CallCompletes0 kd self (lpArgs j Q acc pw posp fc tc lam) []
      (LpPre Q pre yr vo acc pw posp fc tc lam pos cs) PostQuiet := by
  set n := pre + yr
  set a := lrsAcc n vo pos cs lam j
  set p := lam ^ 2 * lam ^ j
  set x := pos j
  set w := rqsW n vo cs x
  set σ : Val := fun v => (lpVals j Q acc pw posp fc tc lam a p x w).getD v.idx 0 with hσ
  have v : ∀ i, σ (.n i) = (lpVals j Q acc pw posp fc tc lam a p x w).getD i 0 := fun _ => rfl
  have hw : walk σ f.body = .ret ((lpPre rq self).flatMap (slEvs σ)) [] := by
    rw [hbody, lpBody_eq]; exact walk_straight σ [] _ (lpPre_straight rq self)
  have h24 : σ (.n 24) = 0 ↔ j + 1 = Q := by
    rw [v]; exact gen_add_ne' (by omega) (by omega)
  have hA1 : ∀ rd, LpPre Q pre yr vo acc pw posp fc tc lam pos cs rd → ∀ b ∈ lpA1, b.Holds rd σ := by
    intro rd hP
    obtain ⟨ha, hp, hx, -⟩ := hP
    simp only [lpA1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const,
      and_true, Atom.Holds]
    refine ⟨rfl, ?_, rfl, ?_, rfl, ?_⟩
    · show LoadHolds rd (acc * gen ^ j) 0 a
      exact readsAt_at ha (by simp [accL]; omega) (by simp [accL]; rfl)
    · show LoadHolds rd (pw * gen ^ j) 0 p
      exact readsAt_at hp (by simp [pwL]; omega) (by simp [pwL, p])
    · show LoadHolds rd (posp * gen ^ j) 0 x
      exact readsAt_at hx (by simp [posL]; omega) (by simp [posL, x])
  have hA2 : ∀ rd, LpPre Q pre yr vo acc pw posp fc tc lam pos cs rd → ∀ b ∈ lpA2, b.Holds rd σ := by
    intro rd hP
    obtain ⟨ha, hp, -, -⟩ := hP
    simp only [lpA2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const,
      and_true, Atom.Holds]
    refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, rfl, rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · show LoadHolds rd (acc * gen ^ j) 1 (a + p * w)
      refine readsAt_at ha (by simp [accL]; omega) ?_
      simp only [accL, List.getElem_map, List.getElem_range]
      rw [lrsAcc_succ]
    · show LoadHolds rd (pw * gen ^ j) 0 p
      exact readsAt_at hp (by simp [pwL]; omega) (by simp [pwL, p])
    · show LoadHolds rd (pw * gen ^ j) 1 (p * lam)
      refine readsAt_at hp (by simp [pwL]; omega) ?_
      simp only [pwL, List.getElem_map, List.getElem_range, p]
      ring
    · exact word_gen.symm
    · exact pow_succ gen j
    · exact word_gen.symm
    · exact pow_succ gen j
  set es := (lpPre rq self).flatMap (slEvs σ) with hes
  have hev : ∀ rd, LpPre Q pre yr vo acc pw posp fc tc lam pos cs rd → ∀ e ∈ es, e.Holds rd σ := by
    intro rd hP e he
    rw [hes, lp_evs] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ((⟨b, hb, rfl⟩ | rfl) | ⟨b, hb, rfl⟩) | rfl | rfl
    · exact hA1 rd hP b hb
    · trivial
    · exact hA2 rd hP b hb
    · show IsInK (σ (.n 24))
      rw [v]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
    · split <;> trivial
  have hquiet : ∀ c, Ev.atom c ∈ es → atomQuiet c = true := by
    intro c hc
    rw [hes, lp_evs] at hc
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((⟨b, hb, hbc⟩ | hc) | ⟨b, hb, hbc⟩) | hc | hc
    · cases hbc; simp only [lpA1, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · cases hc
    · cases hbc; simp only [lpA2, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · cases hc
    · split at hc <;> cases hc
  have hexact : ∀ rd, ∀ e ∈ es, e.Exact rd σ := by
    intro rd e he
    rw [hes, lp_evs] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ((⟨b, hb, rfl⟩ | rfl) | ⟨b, hb, rfl⟩) | rfl | rfl
    · simp only [lpA1, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
    · trivial
    · simp only [lpA2, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
    · trivial
    · split <;> trivial
  refine callCompletes0_node fun rd hl hP => ?_
  obtain ⟨t1, hn1, hv1, hb1, hq1⟩ := hrq x fc tc cs rd hl hP.2.2.2
  obtain ⟨t2, hk2, hb2, hq2⟩ : ∃ t2, Tree.KidsValid coreProgram rd σ
      [⟨self, lpSelfArgs, [], decide (σ (.n 24) ≠ 0)⟩] [t2] ∧ Tree.BufsOk coreProgram t2 ∧
      PostQuiet rd t2 := by
    by_cases hl1 : j + 1 = Q
    · have hd : decide (σ (.n 24) ≠ 0) = false := by simp [h24.mpr hl1]
      have hph : (osParams 8).map (fun v => (lpVals (j + 1) Q acc pw posp fc tc lam 0 0 0 0).getD v.idx 0) =
          lpSelfArgs.map σ := by
        simp only [osParams, lpSelfArgs, List.range_succ, List.range_zero, List.nil_append,
          List.map_cons, List.map_nil, v, lpVals, List.getD_cons_succ, List.getD_cons_zero, List.cons_append]
      refine ⟨.phantom self (fun v => (lpVals (j + 1) Q acc pw posp fc tc lam 0 0 0 0).getD v.idx 0),
        kidsValid_cons_skip (c := ⟨self, lpSelfArgs, [], decide (σ (.n 24) ≠ 0)⟩) (cs := []) (fn := f) hd hfind
          (by rw [hparams]; exact hph) kidsValid_nil,
        by rw [Tree.BufsOk]; trivial, by rw [PostQuiet, Tree.pops]; exact ⟨rfl, Tree.every_phantom⟩⟩
    · have hd : decide (σ (.n 24) ≠ 0) = true := by simp [h24, hl1]
      obtain ⟨t2, hn2, hv2, hb2, hq2⟩ := hnext (by omega) rd hl hP
      exact ⟨t2, kidsValid_cons_taken hd hn2 hv2 kidsValid_nil, hb2, hq2⟩
  have hK : Tree.KidsValid coreProgram rd σ (calls es) [t1, t2] := by
    rw [hes, lp_calls]
    exact kidsValid_cons_taken rfl hn1 hv1 hk2
  refine ⟨σ, f, es, [], [t1, t2], hfind, by rw [hparams]; rfl, hw, rfl, hev rd hP, hK,
    by rw [Tree.BufsOkKids, Tree.BufsOkKids, Tree.BufsOkKids]; exact ⟨hb1, hb2, trivial⟩, ?_⟩
  refine postQuiet_node hfind hw hquiet (hexact rd) hK ?_ _
  rw [hes, lp_calls, List.map_cons, List.map_cons, List.map_nil, kidsPost_cons, kidsPost_cons]
  exact ⟨fun _ => hq1, fun _ => hq2, by simp [KidsPost]⟩

/-- **The loop completes from iteration `j`**, every `j < Q`. -/
theorem lp_loop {kd : ℕ} {rq self : String} {f : Fn} (hfind : coreProgram.find? self = some f)
    (hparams : f.params = osParams 8) (hbody : f.body = lrsLoopBody rq self) {Q pre yr vo : ℕ}
    (hrq : RqsComplete kd rq pre yr vo) (hQ : Q < 2 ^ 30)
    (acc pw posp fc tc lam : E) (pos cs : ℕ → E) :
    ∀ m j, Q = j + m + 1 → CallCompletes0 kd self (lpArgs j Q acc pw posp fc tc lam) []
      (LpPre Q pre yr vo acc pw posp fc tc lam pos cs) PostQuiet := by
  intro m
  induction m with
  | zero =>
    intro j hj
    exact lp_step hfind hparams hbody hrq hQ acc pw posp fc tc lam pos cs (by omega)
      (fun h => absurd h (by omega))
  | succ m ih =>
    intro j hj
    exact lp_step hfind hparams hbody hrq hQ acc pw posp fc tc lam pos cs (by omega)
      (fun _ => ih (j + 1) (by omega))

/-! ## `level_residual_sum` -/

/-- What `level_residual_sum__L{Q}_L{pre}_L{yr}_L{vo}`'s completeness gives: on the positions and
the challenges, it returns `λ²·Σ_{k<Q} λ^k·w_k`. -/
def LsumComplete (kd : ℕ) (name : String) (Q pre yr vo : ℕ) : Prop :=
  ∀ (posp fc tc lam : E) (pos cs : ℕ → E),
    CallCompletes kd name [posp, fc, tc, lam] [lrsAcc (pre + yr) vo pos cs lam Q]
      (fun rd => ReadsAt rd posp (posL Q pos) ∧ CsAt pre yr fc tc cs rd) PostQuiet

/-- `level_residual_sum`'s atoms before its call. -/
def lsA1 (Q : ℕ) : List Atom :=
  [.const (.n 4) (gw (Q + 1)), .hint (.allocDyn (.n 5) (.n 4)),
    .const (.n 6) (gw (Q + 1)), .hint (.allocDyn (.n 7) (.n 6)),
    .const (.n 8) (word 0 0), .load (.n 8) (.n 5) 0,
    .mul (.n 9) (.n 3) (.n 3), .load (.n 9) (.n 7) 0,
    .const (.n 10) (word 1 0), .const (.n 11) (gw Q),
    .add (.n 12) (.n 10) (.n 11), .const (.n 13) (word 1 0),
    .const (.n 14) (gw Q)]

/-- `level_residual_sum`'s loop arguments. -/
def lsLoopArgs : List V := [.n 13, .n 14, .n 5, .n 7, .n 0, .n 1, .n 2, .n 3]

/-- `level_residual_sum`'s body before its `ret`. -/
def lsPre (Q : ℕ) (loop : String) : List Stmt :=
  (lsA1 Q).map .atom ++ [.callIf (.n 12) loop lsLoopArgs, .atom (.load (.n 15) (.n 5) Q)]

theorem lsBody_eq (Q : ℕ) (loop : String) : lsumBody Q loop = lsPre Q loop ++ [.ret [.n 15]] := rfl

theorem lsPre_straight (Q : ℕ) (loop : String) : (lsPre Q loop).all Stmt.straight = true := rfl

theorem ls_evs (σ : Val) (Q : ℕ) (loop : String) : (lsPre Q loop).flatMap (slEvs σ) =
    (lsA1 Q).map .atom ++ [.inK (.n 12), if σ (.n 12) = 0 then .skip loop lsLoopArgs else
      .call loop lsLoopArgs [], .atom (.load (.n 15) (.n 5) Q)] := by
  rw [lsPre, List.flatMap_append, flatMap_atoms]; rfl

theorem ls_calls (σ : Val) (Q : ℕ) (loop : String) : calls ((lsPre Q loop).flatMap (slEvs σ)) =
    [⟨loop, lsLoopArgs, [], decide (σ (.n 12) ≠ 0)⟩] := by
  rw [(straight_parts σ _ (lsPre_straight Q loop)).2.2.2]
  rfl

/-- `level_residual_sum`'s valuation, `A`, `P` its buffers, `r` its return. -/
def lsσ (Q : ℕ) (posp fc tc lam A P r : E) : Val := fun v =>
  [posp, fc, tc, lam, gw (Q + 1), A, gw (Q + 1), P, word 0 0, lam * lam,
    word 1 0, gw Q, word 1 0 + gw Q, word 1 0, gw Q, r].getD v.idx 0

/-- **`level_residual_sum` completes**, its buffers `acc` and `pw` its own words. -/
theorem lsum_complete' {kd Q : ℕ} {name rq loop : String} {fo fl : Fn}
    (hfo : coreProgram.find? name = some fo) (hpo : fo.params = osParams 4)
    (hbo : fo.body = lsumBody Q loop) (hfl : coreProgram.find? loop = some fl)
    (hpl : fl.params = osParams 8) (hbl : fl.body = lrsLoopBody rq loop) {pre yr vo : ℕ}
    (hrq : RqsComplete kd rq pre yr vo) (hQ1 : 1 ≤ Q) (hQ : Q < 2 ^ 30) :
    LsumComplete kd name Q pre yr vo := by
  intro posp fc tc lam pos cs
  have hgQ : gw Q = gen ^ Q := gw_eq (by unfold u128Bound; omega)
  refine callCompletes_node fun b => ?_
  obtain ⟨A, hA⟩ : ∃ A : E, A = ofK (addressOfIndex b) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : E, P = ofK (addressOfIndex (b + (accL Q (pre + yr) vo pos cs lam).length)) :=
    ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : E, r = lrsAcc (pre + yr) vo pos cs lam Q := ⟨_, rfl⟩
  let σ : Val := lsσ Q posp fc tc lam A P r
  have hw : walk σ fo.body = .ret ((lsPre Q loop).flatMap (slEvs σ)) [.n 15] := by
    rw [hbo, lsBody_eq]; exact walk_straight σ _ _ (lsPre_straight Q loop)
  have h12 : σ (.n 12) ≠ 0 := by
    show word 1 0 + gw Q ≠ 0
    rw [word_one, hgQ]; exact one_add_gen_pow_ne hQ1 hQ
  let Wo : Words := [(b, accL Q (pre + yr) vo pos cs lam)] ++
    [(b + (accL Q (pre + yr) vo pos cs lam).length, pwL Q lam)]
  have hWo : WordsIn Wo b ((accL Q (pre + yr) vo pos cs lam).length + (pwL Q lam).length) :=
    (wordsIn_single _ _).append (wordsIn_single _ _)
  have hRd : ∀ rd, HoldsWords rd Wo → ReadsAt rd A (accL Q (pre + yr) vo pos cs lam) ∧
      ReadsAt rd P (pwL Q lam) := fun rd h => by
    rw [holdsWords_append] at h
    obtain ⟨h1, h2⟩ := h
    have e1 := h1 (b, accL Q (pre + yr) vo pos cs lam) List.mem_cons_self
    have e2 := h2 (b + (accL Q (pre + yr) vo pos cs lam).length, pwL Q lam) List.mem_cons_self
    rw [← hA] at e1
    rw [← hP] at e2
    exact ⟨e1, e2⟩
  refine ⟨_, Wo, σ, fo, (lsPre Q loop).flatMap (slEvs σ), [.n 15],
    (calls ((lsPre Q loop).flatMap (slEvs σ))).map fun _ => PostQuiet,
    hWo, hfo, by rw [hpo]; rfl, hw, by show [r] = _; rw [hr], fun rd _ hW hP e he => ?_, ?_, ?_⟩
  · obtain ⟨ha, hp⟩ := hRd rd hW
    rw [ls_evs] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
    · simp only [lsA1, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        try first | exact rfl | trivial
      · show LoadHolds rd A 0 (word 0 0)
        have := ha 0 (by simp [accL])
        simpa [accL, lrsAcc, word_zero] using this
      · show LoadHolds rd P 0 (lam * lam)
        have := hp 0 (by simp [pwL])
        simpa [pwL, pow_two] using this
    · show IsInK (word 1 0 + gw Q)
      rw [word_one, hgQ]; exact isInK_add one_isInK (gen_pow_isInK _)
    · split <;> trivial
    · show LoadHolds rd A Q r
      have := ha Q (by simp [accL])
      simpa [accL, hr] using this
  · rw [ls_calls]
    refine ⟨?_, trivial⟩
    have : decide (σ (.n 12) ≠ 0) = true := by simp [h12]
    simp only [this, ↓reduceIte, List.map_cons, List.map_nil, List.headD_cons]
    have e : [σ (.n 13), σ (.n 14), σ (.n 5), σ (.n 7), σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3)] =
        lpArgs 0 Q A P posp fc tc lam := by
      show [word 1 0, gw Q, A, P, posp, fc, tc, lam] = _
      rw [word_one, hgQ, lpArgs, pow_zero]
    simp only [lsLoopArgs, List.map_cons, List.map_nil, e]
    refine (lp_loop hfl hpl hbl hrq hQ A P posp fc tc lam pos cs (Q - 1) 0 (by omega)).toCallCompletes.mono'
      fun rd h => ?_
    obtain ⟨ha, hp⟩ := hRd rd h.1
    exact ⟨ha, hp, h.2.1, h.2.2⟩
  · intro rd ts _ _ _ hv hq
    refine postQuiet_node hfo hw (fun c hc => ?_) (fun e he => ?_) hv hq _
    · rw [ls_evs] at hc
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ⟨c', hc', hcc⟩ | hc | hc | hc
      · cases hcc; simp only [lsA1, List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · cases hc
      · split at hc <;> cases hc
      · cases hc; rfl
    · rw [ls_evs] at he
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with ⟨c', hc', rfl⟩ | rfl | rfl | rfl
      · simp only [lsA1, List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
      · trivial
      · split <;> trivial
      · trivial

/-! ## `level_residual_slow` -/

/-- What `level_residual_slow__L{Q}_L{pre}_L{yr}_L{vo}`'s completeness gives: at a flag `z` in
`K`, on the positions and the challenges, it returns `slowVal`. -/
def LrsComplete (kd : ℕ) (name : String) (Q pre yr vo : ℕ) : Prop :=
  ∀ (posp fc tc lam z : E) (pos cs : ℕ → E), IsInK z →
    CallCompletes kd name [posp, fc, tc, lam, z] [slowVal Q (pre + yr) vo pos cs lam z]
      (fun rd => ReadsAt rd posp (posL Q pos) ∧ CsAt pre yr fc tc cs rd) PostQuiet

theorem lrs_complete' {kd : ℕ} {name sum : String} {fo : Fn}
    (hfo : coreProgram.find? name = some fo) (hpo : fo.params = osParams 5)
    (hbo : fo.body = lrsBody sum) {Q pre yr vo : ℕ} (hsum : LsumComplete kd sum Q pre yr vo) :
    LrsComplete kd name Q pre yr vo := by
  intro posp fc tc lam z pos cs hz
  set r := slowVal Q (pre + yr) vo pos cs lam z
  set σ : Val := fun v => [posp, fc, tc, lam, z, r, r].getD v.idx 0 with hσ
  by_cases h0 : z = 0
  · have hr : r = 0 := by simp [r, slowVal, h0]
    have hw : walk σ fo.body = .ret [.inK (.n 4), .atom (.copy (.n 5) (.n 4)), .atom (.copy (.n 6) (.n 5))]
        [.n 6] := by
      have : σ (.n 4) = 0 := h0
      simp [hbo, lrsBody, walk, walk1, Out.seq, Out.pre, this]
    refine callCompletes_node fun b => ⟨0, [], σ, fo, _, _, [], wordsIn_nil b, hfo, by rw [hpo]; rfl, hw, rfl,
      fun rd _ _ _ e he => ?_, trivial, fun rd ts _ _ _ hv _ => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hz
      · show r = z; rw [hr, h0]
      · show r = r; rfl
    · have hc0 : calls [Ev.inK (.n 4), .atom (.copy (.n 5) (.n 4)), .atom (.copy (.n 6) (.n 5))] = [] := rfl
      refine postQuiet_node hfo hw (fun c hc => ?_) (fun e he => ?_) hv
        (by rw [hc0]; cases ts <;> simp [KidsPost]) _
      · simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or] at hc
        rcases hc with h | h <;> cases h <;> rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;> trivial
  · have hr : r = lrsAcc (pre + yr) vo pos cs lam Q := by
      simp only [r, slowVal, h0, ↓reduceIte, lrsAcc]
      rfl
    have hw : walk σ fo.body = .ret [.inK (.n 4), .call sum [.n 0, .n 1, .n 2, .n 3] [.n 5],
        .atom (.copy (.n 6) (.n 5))] [.n 6] := by
      have : σ (.n 4) ≠ 0 := h0
      simp [hbo, lrsBody, walk, walk1, Out.seq, Out.pre, this]
    refine callCompletes_node fun b => ⟨0, [], σ, fo, _, _, [PostQuiet], wordsIn_nil b, hfo,
      by rw [hpo]; rfl, hw, rfl, fun rd _ _ _ e he => ?_, ?_, fun rd ts _ _ _ hv hq => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hz
      · trivial
      · show r = r; rfl
    · simp only [calls, List.filterMap_cons, Ev.call?, List.filterMap_nil, KidsCompl, ↓reduceIte,
        List.map_cons, List.map_nil, List.headD_cons, and_true]
      have e : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3)] = [posp, fc, tc, lam] := rfl
      have e5 : σ (.n 5) = lrsAcc (pre + yr) vo pos cs lam Q := hr
      rw [e, e5]
      exact (hsum posp fc tc lam pos cs).mono' fun rd h => h.2
    · refine postQuiet_node hfo hw (fun c hc => ?_) (fun e he => ?_) hv ?_ _
      · simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or] at hc
        cases hc; rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;> trivial
      · have hc1 : calls [Ev.inK (.n 4), .call sum [.n 0, .n 1, .n 2, .n 3] [.n 5],
            .atom (.copy (.n 6) (.n 5))] = [⟨sum, [.n 0, .n 1, .n 2, .n 3], [.n 5], true⟩] := rfl
        rw [hc1] at hq ⊢
        exact hq

/-! ## Every specialization -/

/-- **Every `level_residual_slow` and its sum complete.** -/
theorem lrs_complete (kd : ℕ) : ∀ e ∈ lrsTable,
    LrsComplete kd e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 ∧
      LsumComplete kd e.2.2.2.2.2.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 := by
  intro e he
  obtain ⟨⟨fo, hfo, hpo, hbo⟩, ⟨fs, hfs, hps, hbs⟩, ⟨fl, hfl, hpl, hbl⟩⟩ := lrsTable_ok e he
  obtain ⟨hQ1, hQ, hrq⟩ := lrsTable_shapes e he
  have hsum := lsum_complete' hfs hps hbs hfl hpl hbl (rqs_complete kd _ hrq) hQ1 hQ
  exact ⟨lrs_complete' hfo hpo hbo hsum, hsum⟩

end
end LeanVM.Guest.B1.VsC
