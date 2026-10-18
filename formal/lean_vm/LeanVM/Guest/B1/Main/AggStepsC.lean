/-
  LeanVM.Guest.B1.Main.AggStepsC

  One iteration of each batching loop of `aggregate_claims` backward: the honest words in memory
  give the iteration, at every depth.
-/

module

public import LeanVM.Guest.B1.Main.AggSteps

/-!
# The batching loops, backward

`loop_complete`: a `mul_range` loop holds from `g^0` to `N = g^m` once each iteration holds,
given the next one, at every depth. At `x = g^c`, `loop95_back` to `loop98_back` build the
iteration's valuation from the row's words: `setl` and `setv` for its straight-line values and
the squeezes', `setb` for repeated blocks (the bytecode weight's coordinates `l97V`, an absorb
chain's `fs_next` blocks `chainV`, `obsChain_complete`), looked up by `b1_lookb`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- **A `mul_range` loop, backward**: its helper holds from `g^0` to `N = g^m`, `0 < m`, once
the iteration at each `g^j`, `j < m`, holds at every depth given the next one. -/
theorem loop_complete {f : String} {ps : List E} {N : E} {m : ℕ} {B : ℕ → Prop}
    (hm0 : 0 < m) (hN : N = gen ^ m) (hB : ∀ j < m, B j)
    (hstep : ∀ d j, B j → IsInK (gen ^ j * gen + N) →
      (gen ^ j * gen + N ≠ 0 → coreProgram.relN rd d f (gen ^ j * gen :: ps) []) →
      coreProgram.relN rd (d + 1) f (gen ^ j :: ps) []) :
    coreProgram.Rel rd f (1 :: ps) [] := by
  have hK : ∀ j, IsInK (gen ^ j * gen + N) := fun j => by
    rw [hN]
    exact isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
  have key : ∀ t j, j + t + 1 = m → coreProgram.relN rd (t + 1) f (gen ^ j :: ps) [] := by
    intro t
    induction t with
    | zero =>
      intro j hj
      refine hstep 0 j (hB j (by omega)) (hK j) fun hne => absurd ?_ hne
      rw [gen_pow_add_eq_zero_iff, hN]; congr 1; omega
    | succ t ih =>
      intro j hj
      refine hstep (t + 1) j (hB j (by omega)) (hK j) fun _ => ?_
      rw [gen_pow_mul_gen]
      exact ih (j + 1) (by omega)
  refine ⟨m, ?_⟩
  have := key (m - 1) 0 (by omega)
  rwa [pow_zero, show m - 1 + 1 = m by omega] at this

theorem loadHolds_of_mul {p q v : E} {j k : ℕ} (hq : q = p * gen ^ j)
    (h : LoadHolds rd p (j + k) v) : LoadHolds rd q k v := by
  rw [hq, loadHolds_mul_gen_pow]; exact h

theorem loadHolds_of_mul0 {p q v : E} {j : ℕ} (hq : q = p * gen ^ j)
    (h : LoadHolds rd p j v) : LoadHolds rd q 0 v :=
  loadHolds_of_mul hq (by rwa [Nat.add_zero])

theorem sqVals_five (cv : Digest) : sqVals cv 5 = (digestScalars (sqCv cv)).1 := rfl

theorem sqVals_six (cv : Digest) : sqVals cv 6 = (digestScalars (sqCv cv)).2 := rfl

theorem sqVals_ch (cv : Digest) : sqVals cv 13 = challengeOf (sqCv cv) := rfl

/-! ## Valuations by blocks -/

/-- `σ` with the values `.n (b + w·k + o)`, `k < n`, `o < w`, set to `g k o`. -/
def setb (σ : Val) (b n w : ℕ) (g : ℕ → ℕ → E) : Val := setv σ b (n * w) fun i => g (i / w) (i % w)

theorem setb_lt {σ : Val} {b n w k : ℕ} {g : ℕ → ℕ → E} (h : k < b) :
    setb σ b n w g (.n k) = σ (.n k) := set_n_lt h

theorem setb_ge {σ : Val} {b n w k : ℕ} {g : ℕ → ℕ → E} (h : b + n * w ≤ k) :
    setb σ b n w g (.n k) = σ (.n k) := set_n_ge h

theorem setb_in {σ : Val} {b n w : ℕ} {g : ℕ → ℕ → E} {k o : ℕ} (ho : o < w) (hk : k < n) :
    setb σ b n w g (.n (b + w * k + o)) = g k o := by
  have h1 : w * k + o < n * w := by
    have := Nat.mul_le_mul_left w (show k + 1 ≤ n by omega)
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm w n] at this; omega
  rw [setb, set_n_in (by omega) (by omega), show b + w * k + o - b = w * k + o by omega,
    Nat.mul_add_div (by omega), Nat.mul_add_mod, Nat.div_eq_of_lt ho, Nat.mod_eq_of_lt ho,
    Nat.add_zero]

theorem setb_in0 {σ : Val} {b n w : ℕ} {g : ℕ → ℕ → E} {k : ℕ} (hw : 0 < w) (hk : k < n) :
    setb σ b n w g (.n (b + w * k)) = g k 0 := by
  have := setb_in (σ := σ) (b := b) (g := g) (o := 0) hw hk
  rwa [Nat.add_zero] at this

theorem setb_lit {σ : Val} {b n w : ℕ} {g : ℕ → ℕ → E} {i : ℕ} (h1 : b ≤ i) (h2 : i < b + n * w) :
    setb σ b n w g (.n i) = g ((i - b) / w) ((i - b) % w) := set_n_in h1 h2

/-- Lookups in a valuation built by `setl`, `setv` and `setb`, the blocks by `setb_in`. -/
macro "b1_lookb" : tactic =>
  `(tactic| simp (disch := omega) only [setl, set_n_lt, set_n_ge, set_n_in, setb_lt, setb_ge, setb_in,
    setb_in0, Nat.add_sub_cancel_left, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.add_zero, Nat.sub_self,
    Nat.zero_add])

/-! ## `__loop97` -/

/-- Value `o` of `__loop97`'s coordinate block `k`, coordinate `k + 1`. -/
def l97V (r f g : List E) (k : ℕ) : ℕ → E
  | 0 => r.getD (k + 1) 0
  | 1 => 1
  | 2 => f.getD (k + 1) 0
  | 3 => 1 + f.getD (k + 1) 0
  | 4 => 1 + f.getD (k + 1) 0 + r.getD (k + 1) 0
  | 5 => eqEval (f.take (k + 2)) (r.take (k + 2))
  | 6 => 1
  | 7 => g.getD (k + 1) 0
  | 8 => 1 + g.getD (k + 1) 0
  | 9 => 1 + g.getD (k + 1) 0 + r.getD (k + 1) 0
  | _ => eqEval (g.take (k + 2)) (r.take (k + 2))

theorem eqEval_take_succ' (as bs : List E) (j : ℕ) (ha : j < as.length) (hb : j < bs.length) :
    eqEval (as.take (j + 1)) (bs.take (j + 1)) =
      eqEval (as.take j) (bs.take j) * (1 + as.getD j 0 + bs.getD j 0) := by
  rw [eqEval_take_succ as bs j ha hb, List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]

theorem eqEval_take_one (as bs : List E) (ha : 0 < as.length) (hb : 0 < bs.length) :
    eqEval (as.take 1) (bs.take 1) = 1 + as.getD 0 0 + bs.getD 0 0 := by
  rw [eqEval_take_succ' as bs 0 ha hb]; simp [eqEval]

theorem readsAt_getD' {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ} (hk : k < xs.length) :
    LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

/-- **`__loop97` at `x = g^c`, backward**: the row's words give the iteration. -/
theorem loop97_back {N frow crow bcp wsum lam : E} (d c : ℕ) (fp cp : E) (r f g : List E)
    (w lf lc : E) (hrl : r.length = 22) (hfl : f.length = 22) (hgl : g.length = 22)
    (hf : LoadHolds rd frow c fp) (hc : LoadHolds rd crow c cp) (hR : ReadsAt rd bcp r)
    (hF : ReadsAt rd fp f) (hG : ReadsAt rd cp g) (hw : LoadHolds rd wsum c w)
    (hlf : LoadHolds rd lam (2 * c) lf) (hlc : LoadHolds rd lam (2 * c + 1) lc)
    (hn : LoadHolds rd wsum (c + 1) (w + lf * eqEval f r + lc * eqEval g r))
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 →
      coreProgram.relN rd d "__loop97" [gen ^ c * gen, N, frow, crow, bcp, wsum, lam] []) :
    coreProgram.relN rd (d + 1) "__loop97" [gen ^ c, N, frow, crow, bcp, wsum, lam] [] := by
  set x := gen ^ c with hx
  have e2 : lam * (x * x) = lam * gen ^ (2 * c) := by rw [hx]; ring
  have ef : frow * x = frow * gen ^ c := rfl
  have ec : crow * x = crow * gen ^ c := rfl
  have ew : wsum * x = wsum * gen ^ c := rfl
  have eF : eqEval (f.take 22) (r.take 22) = eqEval f r := by
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  have eG : eqEval (g.take 22) (r.take 22) = eqEval g r := by
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  rw [relN_succ_iff find_loop97]
  refine ⟨setl (setb (setl (Val.ofArgs [x, N, frow, crow, bcp, wsum, lam]) 7
      [frow * x, fp, crow * x, cp, r.getD 0 0, 1, f.getD 0 0, 1 + f.getD 0 0,
        1 + f.getD 0 0 + r.getD 0 0, 1, g.getD 0 0, 1 + g.getD 0 0, 1 + g.getD 0 0 + r.getD 0 0])
      20 21 11 (l97V r f g)) 251
    [x * x, wsum * x, w, lam * (x * x), lf, lf * eqEval f r, w + lf * eqEval f r, lam * (x * x), lc,
      lc * eqEval g r, w + lf * eqEval f r + lc * eqEval g r, wsum * x, gen, x * gen, x * gen + N,
      gen, x * gen],
    by simp only [show Fn.params Data.core569 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] from rfl,
      List.map_cons, List.map_nil]; b1_lookb, ?_⟩
  rw [core569_body, l97Body, holdsList_append, holdsList_append,
    holdsList_range_flatten 21 (fun k => l97Coord (k + 1)) (fun _ => rfl)]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen,
    word_one]
  b1_lookb
  rw [setb_lit (by omega) (by omega), setb_lit (by omega) (by omega)]
  simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, l97V, Nat.reduceAdd, eF, eG, ef, ec, ew,
    e2, loadHolds_mul_gen_pow, Nat.add_zero, true_and, and_true]
  refine ⟨hf, hc, readsAt_getD' hR (by omega), readsAt_getD' hF (by omega),
    readsAt_getD' hG (by omega), fun k hk => ?_, hw, hlf, hlc, hn, hK, hnext⟩
  simp only [l97Coord, Nat.add_sub_cancel, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one,
    Nat.add_eq_right]
  rcases k with _ | k
  · simp only [↓reduceIte]
    b1_lookb
    simp only [l97V, Nat.reduceAdd, true_and, and_true]
    refine ⟨readsAt_getD' hR (by omega), readsAt_getD' hF (by omega), ?_,
      readsAt_getD' hG (by omega), ?_⟩ <;>
      (rw [eqEval_take_succ' _ _ 1 (by omega) (by omega), eqEval_take_one _ _ (by omega) (by omega)])
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, show 20 + 11 * (k + 1) - 6 = 20 + 11 * k + 5 by omega,
      show 20 + 11 * (k + 1) - 1 = 20 + 11 * k + 10 by omega]
    b1_lookb
    simp only [l97V, true_and, and_true]
    refine ⟨readsAt_getD' hR (by omega), readsAt_getD' hF (by omega), ?_,
      readsAt_getD' hG (by omega), ?_⟩ <;>
      (rw [show k + 1 + 2 = k + 2 + 1 by omega, eqEval_take_succ' _ _ (k + 2) (by omega) (by omega)])

/-! ## `__loop95` -/

/-- **An absorb chain, backward**: the words at the cursor, and the chain's values the honest
ones, from the state of `cv`. -/
theorem obsChain_complete {C : CallRel} {σ : Val} (s0 s1 cur : V) (B n : ℕ) (kret : List E → Prop)
    {cv : Digest} (xs : List E) (hl : xs.length = n) (hcv : (σ s0, σ s1) = digestScalars cv)
    (hx : ∀ k < n, σ (.n (B + 15 * k)) = xs.getD k 0)
    (hv : ∀ k < n, ∀ j, 2 ≤ j → j < 14 →
      σ (.n (B + 15 * k + 1 + j)) = fsVals (xs.getD k 0) (obsAll cv (xs.take k)) 1 j)
    (hr : ReadsAt rd (σ cur) xs) :
    Stmt.HoldsList C rd σ (obsChainT s0 s1 cur B n) True kret := by
  have key : ∀ m ≤ n, (σ (chainS0 s0 B m), σ (chainS1 s1 B m)) =
      digestScalars (obsAll cv (xs.take m)) := by
    intro m hm
    induction m with
    | zero => simpa [chainS0, chainS1, obsAll] using hcv
    | succ m ih =>
      rw [obsAll_take_succ _ _ _ (by omega), chainS0, chainS1,
        show B + 15 * m + 13 = B + 15 * m + 1 + 12 by omega,
        show B + 15 * m + 14 = B + 15 * m + 1 + 13 by omega, hv m (by omega) 12 (by omega) (by omega),
        hv m (by omega) 13 (by omega) (by omega)]
      rfl
  rw [obsChainT, holdsList_range_flatten _ _ (fun _ => rfl)]
  refine ⟨fun k hk => ?_, trivial⟩
  rw [holds_fsNextT]
  refine ⟨⟨by rw [hx k hk]; exact readsAt_getD' hr (by omega),
    ⟨obsAll cv (xs.take k), key k (by omega), fun j hj1 hj2 => ?_⟩⟩, trivial⟩
  rw [hv k hk j hj1 hj2, hx k hk]

/-- Value `o` of block `k` of an absorb chain over `xs` from the state of `cv`. -/
def chainV (xs : List E) (cv : Digest) (k o : ℕ) : E :=
  if o = 0 then xs.getD k 0 else fsVals (xs.getD k 0) (obsAll cv (xs.take k)) 1 (o - 1)

/-- **`__loop95` at `x = g^c`, backward**: the row's words give the iteration. -/
theorem loop95_back {N absorb cpi cfresh frow ccar crow : E} (d c : ℕ) (cv : Digest) (p0 p1 : E)
    (fs cs : List E) (hfl : fs.length = 106) (hcl : cs.length = 53)
    (h0 : LoadHolds rd absorb (2 * c) (digestScalars cv).1)
    (h1 : LoadHolds rd absorb (2 * c + 1) (digestScalars cv).2)
    (q0 : LoadHolds rd cpi (2 * c) p0) (q1 : LoadHolds rd cpi (2 * c + 1) p1)
    (hfr : ReadsAt rd (cfresh * gen ^ (106 * c)) fs) (hcr : ReadsAt rd (ccar * gen ^ (53 * c)) cs)
    (wf : LoadHolds rd frow c (cfresh * gen ^ (106 * c)))
    (wc : LoadHolds rd crow c (ccar * gen ^ (53 * c)))
    (o0 : LoadHolds rd absorb (2 * c + 2) (digestScalars (obsAll cv (p0 :: p1 :: (fs ++ cs)))).1)
    (o1 : LoadHolds rd absorb (2 * c + 3) (digestScalars (obsAll cv (p0 :: p1 :: (fs ++ cs)))).2)
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 → coreProgram.relN rd d "__loop95"
      [gen ^ c * gen, N, absorb, cpi, cfresh, frow, ccar, crow] []) :
    coreProgram.relN rd (d + 1) "__loop95" [gen ^ c, N, absorb, cpi, cfresh, frow, ccar, crow] [] := by
  let cv1 := obsCv cv p0
  let cv2 := obsCv cv1 p1
  let cv3 := obsAll cv2 fs
  have hall : obsAll cv (p0 :: p1 :: (fs ++ cs)) = obsAll cv3 cs := by
    simp [cv3, cv2, cv1, obsAll, List.foldl_append]
  rw [hall] at o0 o1
  rw [relN_succ_iff find_loop95]
  refine ⟨setl (setb (setl (setb (setl (setv (setl (setv (setl
      (Val.ofArgs [gen ^ c, N, absorb, cpi, cfresh, frow, ccar, crow]) 8
      [gen ^ (2 * c), absorb * gen ^ (2 * c), (digestScalars cv).1, (digestScalars cv).2,
        gen ^ (2 * c), cpi * gen ^ (2 * c), p0]) 15 14 (fsVals p0 cv 1)) 29
      [cpi * gen ^ (2 * c), p1]) 31 14 (fsVals p1 cv1 1)) 45
      [gen ^ (2 * c), gen ^ (3 * c), gen ^ (6 * c), gen ^ (12 * c), gen ^ (13 * c), gen ^ (26 * c),
        gen ^ (52 * c), gen ^ (53 * c), gen ^ (106 * c), cfresh * gen ^ (106 * c), frow * gen ^ c])
      56 106 15 (chainV fs cv2)) 1646
      [gen ^ (2 * c), gen ^ (3 * c), gen ^ (6 * c), gen ^ (12 * c), gen ^ (13 * c), gen ^ (26 * c),
        gen ^ (52 * c), gen ^ (53 * c), ccar * gen ^ (53 * c), crow * gen ^ c])
      1656 53 15 (chainV cs cv3)) 2451
    [gen, gen ^ c * gen, gen ^ c * gen + N, gen, gen ^ c * gen],
    by simp only [show Fn.params Data.core566 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]
      from rfl, List.map_cons, List.map_nil]; b1_lookb, ?_⟩
  rw [core566_body, l95Body]
  simp only [holdsList_append, holds_fsNextT]
  rw [holdsList_noRet (obsChainT (.n 43) (.n 44) (.n 54) 56 106) (noRetList_obsChainT ..),
    holdsList_noRet (obsChainT (.n 1644) (.n 1645) (.n 1654) 1656 53) (noRetList_obsChainT ..)]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen]
  b1_lookb
  rw [setb_lit (i := 2449) (by omega) (by omega), setb_lit (i := 2450) (by omega) (by omega)]
  have e52 : obsAll cv3 cs = obsCv (obsAll cv3 (cs.take 52)) (cs.getD 52 0) := by
    rw [← obsAll_take_succ _ _ _ (by omega), List.take_of_length_le (by omega)]
  simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, chainV, OfNat.ofNat_ne_zero, ↓reduceIte,
    loadHolds_mul_gen_pow, Nat.add_zero, true_and, and_true]
  rw [e52] at o0 o1
  refine ⟨by ring, h0, h1, by ring, ⟨q0, cv, rfl, fun k h1 h2 => by b1_lookb⟩,
    ⟨q1, cv1, rfl, fun k h1 h2 => by b1_lookb⟩, by ring, by ring, by ring, by ring, by ring, by ring,
    by ring, by ring, by ring, wf, ?_, by ring, by ring, by ring, by ring, by ring, by ring, by ring,
    by ring, wc, ?_, o0, o1, hK, hnext⟩
  · refine obsChain_complete _ _ _ _ _ _ fs hfl (cv := cv2) (by b1_lookb; rfl) (fun k hk => ?_)
      (fun k hk j hj1 hj2 => ?_) (by b1_lookb; exact hfr)
    · b1_lookb; simp [chainV]
    · b1_lookb
      rw [Nat.add_assoc (56 + 15 * k) 1 j, setb_in (by omega) (by omega)]
      simp [chainV]
  · have e105 : obsAll cv2 fs = obsCv (obsAll cv2 (fs.take 105)) (fs.getD 105 0) := by
      rw [← obsAll_take_succ _ _ _ (by omega), List.take_of_length_le (by omega)]
    refine obsChain_complete _ _ _ _ _ _ cs hcl (cv := cv3) ?_ (fun k hk => ?_)
      (fun k hk j hj1 hj2 => ?_) (by b1_lookb; exact hcr)
    · b1_lookb
      rw [setb_lit (i := 1644) (by omega) (by omega), setb_lit (i := 1645) (by omega) (by omega)]
      simp only [Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, chainV, OfNat.ofNat_ne_zero,
        ↓reduceIte]
      show _ = digestScalars (obsAll cv2 fs)
      rw [e105]; rfl
    · b1_lookb; simp [chainV]
    · b1_lookb
      rw [Nat.add_assoc (1656 + 15 * k) 1 j, setb_in (by omega) (by omega)]
      simp [chainV]

/-- **`__loop96` at `x = g^c`, backward**: the row's words give the iteration. -/
theorem loop96_back {N bcc lam frow crow : E} (d c : ℕ) (cv : Digest) (fp cp acc fv cv' : E)
    (h0 : LoadHolds rd bcc (3 * c) (digestScalars cv).1)
    (h1 : LoadHolds rd bcc (3 * c + 1) (digestScalars cv).2)
    (l0 : LoadHolds rd lam (2 * c) (challengeOf (sqCv cv)))
    (l1 : LoadHolds rd lam (2 * c + 1) (challengeOf (sqCv (sqCv cv))))
    (s0 : LoadHolds rd bcc (3 * c + 3) (digestScalars (sqCv (sqCv cv))).1)
    (s1 : LoadHolds rd bcc (3 * c + 4) (digestScalars (sqCv (sqCv cv))).2)
    (hf : LoadHolds rd frow c fp) (hc : LoadHolds rd crow c cp)
    (ha : LoadHolds rd bcc (3 * c + 2) acc) (hfv : LoadHolds rd fp 22 fv)
    (hcv : LoadHolds rd cp 22 cv')
    (hn : LoadHolds rd bcc (3 * c + 5)
      (acc + challengeOf (sqCv cv) * fv + challengeOf (sqCv (sqCv cv)) * cv'))
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 →
      coreProgram.relN rd d "__loop96" [gen ^ c * gen, N, bcc, lam, frow, crow] []) :
    coreProgram.relN rd (d + 1) "__loop96" [gen ^ c, N, bcc, lam, frow, crow] [] := by
  set x := gen ^ c with hx
  have e3 : bcc * (x * x * x) = bcc * gen ^ (3 * c) := by rw [hx]; ring
  have e2 : lam * (x * x) = lam * gen ^ (2 * c) := by rw [hx]; ring
  have ef : frow * x = frow * gen ^ c := rfl
  have ec : crow * x = crow * gen ^ c := rfl
  rw [relN_succ_iff find_loop96]
  refine ⟨setl (setv (setv (setl (Val.ofArgs [x, N, bcc, lam, frow, crow]) 6
      [x * x, x * x * x, bcc * (x * x * x), (digestScalars cv).1, (digestScalars cv).2]) 11 14
      (sqVals cv)) 25 14 (sqVals (sqCv cv))) 39
    [x * x, lam * (x * x), lam * (x * x), frow * x, fp, crow * x, cp, acc, fv,
      challengeOf (sqCv cv) * fv, acc + challengeOf (sqCv cv) * fv, cv',
      challengeOf (sqCv (sqCv cv)) * cv',
      acc + challengeOf (sqCv cv) * fv + challengeOf (sqCv (sqCv cv)) * cv', gen, x * gen,
      x * gen + N, gen, x * gen], by simp only [show Fn.params Data.core567 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]
      from rfl, List.map_cons, List.map_nil]; b1_look, ?_⟩
  rw [core567_body, l96Body]
  simp only [holdsList_append, holds_squeezeT]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [sqVals_five, sqVals_six, sqVals_ch, e3, e2, ef, ec, loadHolds_mul_gen_pow, Nat.add_zero,
    true_and, and_true]
  exact ⟨h0, h1, ⟨cv, rfl, fun k hk => by b1_look⟩, ⟨sqCv cv, rfl, fun k hk => by b1_look⟩, l0, l1, hf,
    hc, s0, s1, ha, hfv, hcv, hn, hK, hnext⟩

/-- **`__loop98` at `x = g^c`, backward**: the row's words give the iteration. -/
theorem loop98_back {N mcc lam frow crow : E} (d c : ℕ) (cv : Digest) (fp cp acc fv ca cb : E)
    (h0 : LoadHolds rd mcc (3 * c) (digestScalars cv).1)
    (h1 : LoadHolds rd mcc (3 * c + 1) (digestScalars cv).2)
    (l0 : LoadHolds rd lam (3 * c) (challengeOf (sqCv cv)))
    (l1 : LoadHolds rd lam (3 * c + 1) (challengeOf (sqCv (sqCv cv))))
    (l2 : LoadHolds rd lam (3 * c + 2) (challengeOf (sqCv (sqCv (sqCv cv)))))
    (s0 : LoadHolds rd mcc (3 * c + 3) (digestScalars (sqCv (sqCv (sqCv cv)))).1)
    (s1 : LoadHolds rd mcc (3 * c + 4) (digestScalars (sqCv (sqCv (sqCv cv)))).2)
    (hf : LoadHolds rd frow c fp) (hc : LoadHolds rd crow c cp)
    (ha : LoadHolds rd mcc (3 * c + 2) acc) (hfv : LoadHolds rd fp 105 fv)
    (hca : LoadHolds rd cp 51 ca) (hcb : LoadHolds rd cp 52 cb)
    (hn : LoadHolds rd mcc (3 * c + 5) (acc + challengeOf (sqCv cv) * fv +
      challengeOf (sqCv (sqCv cv)) * ca + challengeOf (sqCv (sqCv (sqCv cv))) * cb))
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 →
      coreProgram.relN rd d "__loop98" [gen ^ c * gen, N, mcc, lam, frow, crow] []) :
    coreProgram.relN rd (d + 1) "__loop98" [gen ^ c, N, mcc, lam, frow, crow] [] := by
  set x := gen ^ c with hx
  have e3 : mcc * (x * x * x) = mcc * gen ^ (3 * c) := by rw [hx]; ring
  have e3' : lam * (x * x * x) = lam * gen ^ (3 * c) := by rw [hx]; ring
  have ef : frow * x = frow * gen ^ c := rfl
  have ec : crow * x = crow * gen ^ c := rfl
  rw [relN_succ_iff find_loop98]
  refine ⟨setl (setv (setv (setv (setl (Val.ofArgs [x, N, mcc, lam, frow, crow]) 6
      [x * x, x * x * x, mcc * (x * x * x), (digestScalars cv).1, (digestScalars cv).2]) 11 14
      (sqVals cv)) 25 14 (sqVals (sqCv cv))) 39 14 (sqVals (sqCv (sqCv cv)))) 53
    [x * x, x * x * x, lam * (x * x * x), lam * (x * x * x), lam * (x * x * x), frow * x, fp,
      crow * x, cp, acc, fv, challengeOf (sqCv cv) * fv, acc + challengeOf (sqCv cv) * fv, ca,
      challengeOf (sqCv (sqCv cv)) * ca,
      acc + challengeOf (sqCv cv) * fv + challengeOf (sqCv (sqCv cv)) * ca, cb,
      challengeOf (sqCv (sqCv (sqCv cv))) * cb,
      acc + challengeOf (sqCv cv) * fv + challengeOf (sqCv (sqCv cv)) * ca +
        challengeOf (sqCv (sqCv (sqCv cv))) * cb, gen, x * gen, x * gen + N, gen, x * gen],
    by simp only [show Fn.params Data.core570 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
      List.map_cons, List.map_nil]; b1_look, ?_⟩
  rw [core570_body, l98Body]
  simp only [holdsList_append, holds_squeezeT]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [sqVals_five, sqVals_six, sqVals_ch, e3, e3', ef, ec, loadHolds_mul_gen_pow,
    Nat.add_zero, true_and, and_true]
  exact ⟨h0, h1, ⟨cv, rfl, fun k hk => by b1_look⟩, ⟨sqCv cv, rfl, fun k hk => by b1_look⟩,
    ⟨sqCv (sqCv cv), rfl, fun k hk => by b1_look⟩, l0, l1, l2, hf, hc, s0, s1, ha, hfv, hca, hcb, hn,
    hK, hnext⟩

end
end LeanVM.Guest.B1.Main
