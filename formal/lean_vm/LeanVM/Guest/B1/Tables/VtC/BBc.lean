/-
  LeanVM.Guest.B1.Tables.VtC.BBc

  `verify_tables`' bytecode share on the honest valuation: the share and the slot sumcheck's
  first round read, its challenge squeezed, the three `opening_tail_round` calls, the slot point
  stored in `bc_point`, the value read, and the closing check.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BGlue
public import LeanVM.Guest.B1.Tables.Vt.BcShare

/-!
# The bytecode share, honestly (G:2422-2469)

The honest share from the sponge `F0` after the four framework words and the ten words `w` the
stream holds after them (`S`, the first round's `c0`, `c2`, the three tail rounds' two words each,
the value): `vtBcF` absorbs the first three, `vtBcR0` is the first challenge, `vtBcCl1` the first
round's claim at it, `vtBcR1 .. vtBcR3` the tail rounds (`bcRound`: the capacity after, the claim,
the challenge), `vtBcPoint` the four challenges. `vtBc_run`: when the last claim is the slot
weights' fold at the point times the value, `bytecodeShare` runs on `w` from `F0`.

`vtB_fresh`: on a memory holding the four framework words and `w` at the cursor, the honest
valuation reads them, and its first challenge and the capacity after it are `F0`'s.
`vtB_bc`: with `bc_point` holding `vtBcPoint`, the oracle returning the tail rounds' words and the
last claim accepted, the share's stores, calls, value read and closing check hold.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (multilinearEval_eq_dot)

@[expose] public section

/-! ## The honest share -/

/-- A plain round of `sumcheck _ 3` on the capacity `cap` at the claim, its words `a`, `b`: the
capacity after, the next claim and the challenge. -/
def bcRound (cap : List E) (claim a b : E) : List E × E × E :=
  (((⟨cap, []⟩ : Fs).absorbAll [a, b] dsObserve).squeeze.2.cap,
    a + ((⟨cap, []⟩ : Fs).absorbAll [a, b] dsObserve).squeeze.1 *
      (claim + (1 + ((⟨cap, []⟩ : Fs).absorbAll [a, b] dsObserve).squeeze.1) * b),
    ((⟨cap, []⟩ : Fs).absorbAll [a, b] dsObserve).squeeze.1)

/-- The sponge after the share and the first round's two words. -/
def vtBcF (F0 : Fs) (w : List E) : Fs := F0.absorbAll (w.take 3) dsObserve

/-- The first challenge. -/
def vtBcR0 (F0 : Fs) (w : List E) : E := (vtBcF F0 w).squeeze.1

/-- The first round's claim at it. -/
def vtBcCl1 (F0 : Fs) (w : List E) : E :=
  w.getD 1 0 + vtBcR0 F0 w * (w.getD 0 0 + (1 + vtBcR0 F0 w) * w.getD 2 0)

/-- The first tail round. -/
def vtBcR1 (F0 : Fs) (w : List E) : List E × E × E :=
  bcRound (vtBcF F0 w).squeeze.2.cap (vtBcCl1 F0 w) (w.getD 3 0) (w.getD 4 0)

/-- The second tail round. -/
def vtBcR2 (F0 : Fs) (w : List E) : List E × E × E :=
  bcRound (vtBcR1 F0 w).1 (vtBcR1 F0 w).2.1 (w.getD 5 0) (w.getD 6 0)

/-- The third tail round. -/
def vtBcR3 (F0 : Fs) (w : List E) : List E × E × E :=
  bcRound (vtBcR2 F0 w).1 (vtBcR2 F0 w).2.1 (w.getD 7 0) (w.getD 8 0)

/-- The slot point: the four challenges. -/
def vtBcPoint (F0 : Fs) (w : List E) : List E :=
  [vtBcR0 F0 w, (vtBcR1 F0 w).2.2, (vtBcR2 F0 w).2.2, (vtBcR3 F0 w).2.2]

/-- A ten-word list is its ten entries. -/
theorem vt_list10 (w : List E) (hw : w.length = 10) :
    w = [w.getD 0 0, w.getD 1 0, w.getD 2 0, w.getD 3 0, w.getD 4 0, w.getD 5 0, w.getD 6 0,
      w.getD 7 0, w.getD 8 0, w.getD 9 0] := by
  match w, hw with
  | [_, _, _, _, _, _, _, _, _, _], _ => rfl

/-- **The bytecode share runs** on `w` from `F0` when its last claim is accepted. -/
theorem vtBc_run (F0 : Fs) (w : List E) (hwl : w.length = 10) (weights low : List E)
    (hacc : (vtBcR3 F0 w).2.1 = dot (eqKernel (vtBcPoint F0 w)) weights * w.getD 9 0) :
    RunsTo (bytecodeShare weights low) F0 w (w.getD 0 0, low ++ vtBcPoint F0 w, w.getD 9 0)
      ((⟨(vtBcR3 F0 w).1, []⟩ : Fs).absorb (w.getD 9 0) dsObserve) := by
  have sq : ∀ s : Fs, s.squeeze.2 = ⟨s.squeeze.2.cap, []⟩ := fun s ↦ rfl
  have hR4 := runsTo_sumcheck_nil (⟨(vtBcR3 F0 w).1, []⟩ : Fs) (vtBcR3 F0 w).2.1 3
  have hR3 := vt_tail_cons (vtBcR2 F0 w).1 (w.getD 7 0) (w.getD 8 0) (vtBcR2 F0 w).2.1
    (rest := []) (ys := []) (pt := []) (fin := (vtBcR3 F0 w).2.1)
    (s2 := ⟨(vtBcR3 F0 w).1, []⟩) (by rw [sq]; exact hR4)
  have hR2 := vt_tail_cons (vtBcR1 F0 w).1 (w.getD 5 0) (w.getD 6 0) (vtBcR1 F0 w).2.1
    (by rw [sq]; exact hR3)
  have hR1 := vt_tail_cons (vtBcF F0 w).squeeze.2.cap (w.getD 3 0) (w.getD 4 0) (vtBcCl1 F0 w)
    (by rw [sq]; exact hR2)
  have hF : ((F0.absorb (w.getD 0 0) dsObserve).absorb (w.getD 1 0) dsObserve).absorbAll
      [w.getD 2 0] dsObserve = vtBcF F0 w := by
    rw [vtBcF, vt_list10 w hwl]
    simp [Fs.absorbAll]
  have hR0 := runsTo_sumcheck_cons
    (runsTo_roundPolyNone (F0.absorb (w.getD 0 0) dsObserve) (w.getD 0 0) (w.getD 1 0)
      [w.getD 2 0] 3 rfl (by decide))
    (by rw [hF, sq, ← tail_eval]; exact hR1)
  rw [hF] at hR0
  have hR0' : RunsTo (sumcheck (w.getD 0 0) 3 (List.replicate busBits none))
      (F0.absorb (w.getD 0 0) dsObserve)
      ([w.getD 1 0, w.getD 2 0] ++ ([w.getD 3 0, w.getD 4 0] ++ ([w.getD 5 0, w.getD 6 0] ++
        ([w.getD 7 0, w.getD 8 0] ++ []))))
      (vtBcPoint F0 w, (vtBcR3 F0 w).2.1) ⟨(vtBcR3 F0 w).1, []⟩ := by
    refine RunsTo.of_eq hR0 rfl rfl ?_ rfl
    simp only [vtBcPoint, vtBcR0, vtBcR1, vtBcR2, vtBcR3, bcRound]
  have hS := runsTo_readE F0 (w.getD 0 0)
  have hv := runsTo_readE (⟨(vtBcR3 F0 w).1, []⟩ : Fs) (w.getD 9 0)
  have hq := tb_runsTo_require hacc ((⟨(vtBcR3 F0 w).1, []⟩ : Fs).absorb (w.getD 9 0) dsObserve)
  have hw : w = [w.getD 0 0] ++ (([w.getD 1 0, w.getD 2 0] ++ ([w.getD 3 0, w.getD 4 0] ++
      ([w.getD 5 0, w.getD 6 0] ++ ([w.getD 7 0, w.getD 8 0] ++ [])))) ++ ([w.getD 9 0] ++ ([] ++ []))) := by
    simpa using vt_list10 w hwl
  refine RunsTo.of_eq ?_ rfl hw.symm rfl rfl
  unfold bytecodeShare
  refine hS.bind ?_
  refine hR0'.bind ?_
  refine hv.bind ?_
  refine hq.bind ?_
  exact runsTo_ret _ _

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}

local notation "σv" => vtσ rd wo args

/-- An atom that holds by evaluation alone, read at `vtAt`. -/
theorem vtB_pureAt (hl : args.length = 20) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((vtAt n).take 1) = true) (hp : pureB a = true := by decide) :
    a.Holds rd σv := by
  have hg := vt_goodAt (rd := rd) (w := wo) hl n _ heq
  rw [fixNe_atom] at hg
  cases a with
  | assertNe x i p => simp [pureB] at hp
  | _ => exact holds_of_pure (S := vtSL) (w := wo) hp hg

/-- The sponge after the four framework words, from the carried capacity. -/
def vtF0 (args xs : List E) : Fs :=
  (⟨[args.getD 0 0, args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0], []⟩ : Fs).absorbAll
    xs dsObserve

/-- A stream read's word and its two cells, from the cursor's words. -/
theorem vtB_next (hl : args.length = 20) {pos off b : ℕ} {x : E}
    (hcheck : tbStmtsEqb (fsNextT (.n 5) off b) ((vtAt pos).take 3) = true)
    (hS : Atom.load (.n b) (.n 5) off ∉ vtSL) (hx : LoadHolds rd (args.getD 5 0) off x) :
    σv (.n b) = x ∧ FsPackOk σv (.n b) (b + 1) dsObserve := by
  have hc : tbStmtsEqb (fsNextT (.n 5) off b)
      ((vtPre.drop pos).take (fsNextT (.n 5) off b).length) = true := by
    rw [vtPre_drop]; exact hcheck
  obtain ⟨-, e, hv⟩ := vtc_fsNext (wo := wo) hl hc hS (by rw [vt_param hl (by norm_num)]; exact hx)
  refine ⟨e, ?_, ?_⟩
  · have h0 := hv 0 (by norm_num)
    simp only [Nat.add_zero] at h0
    rw [h0, e]; rfl
  · exact hv 1 (by norm_num)

set_option maxRecDepth 10000 in
/-- **The share's first words and its first challenge**, honestly: the four framework words and
the share's three at the cursor are read; the first challenge (`1867`) and the capacity after it
(`1862 .. 1866`) are `F0`'s. -/
theorem vtB_fresh (hl : args.length = 20) {xs w : List E} (hxl : xs.length = 4)
    (hwl : w.length = 10) (hcur : TbReadsAt rd (args.getD 5 0) (xs ++ w)) :
    [σv (.n 812), σv (.n 816), σv (.n 1302), σv (.n 1316)] = xs ∧
      σv (.n 1840) = w.getD 0 0 ∧ σv (.n 1844) = w.getD 1 0 ∧ σv (.n 1848) = w.getD 2 0 ∧
      σv (.n 1867) = vtBcR0 (vtF0 args xs) w ∧
      [σv (.n 1862), σv (.n 1863), σv (.n 1864), σv (.n 1865), σv (.n 1866)] =
        (vtBcF (vtF0 args xs) w).squeeze.2.cap ∧
      σv (.n 1843) = σv (.n 1840) ∧ σv (.n 1847) = σv (.n 1844) ∧ σv (.n 1851) = σv (.n 1848) := by
  have hlen : (xs ++ w).length = 14 := by simp [hxl, hwl]
  have hc : ∀ k (hk : k < 14), LoadHolds rd (args.getD 5 0) k ((xs ++ w).getD k 0) := fun k hk ↦ by
    rw [List.getD_eq_getElem (xs ++ w) 0 (by rw [hlen]; exact hk)]
    exact hcur k (by rw [hlen]; exact hk)
  obtain ⟨l0, p0⟩ := vtB_next (wo := wo) hl (pos := 799) (b := 812) (by decide +kernel) (by decide +kernel) (hc 0 (by norm_num))
  obtain ⟨l1, p1⟩ := vtB_next (wo := wo) hl (pos := 804) (b := 816) (by decide +kernel) (by decide +kernel) (hc 1 (by norm_num))
  obtain ⟨l2, p2⟩ := vtB_next (wo := wo) hl (pos := 1342) (b := 1302) (by decide +kernel) (by decide +kernel) (hc 2 (by norm_num))
  obtain ⟨l3, p3⟩ := vtB_next (wo := wo) hl (pos := 1357) (b := 1316) (by decide +kernel) (by decide +kernel) (hc 3 (by norm_num))
  obtain ⟨l4, p4⟩ := vtB_next (wo := wo) hl (pos := 1915) (b := 1840) (by decide +kernel) (by decide +kernel) (hc 4 (by norm_num))
  obtain ⟨l5, p5⟩ := vtB_next (wo := wo) hl (pos := 1919) (b := 1844) (by decide +kernel) (by decide +kernel) (hc 5 (by norm_num))
  obtain ⟨l6, p6⟩ := vtB_next (wo := wo) hl (pos := 1923) (b := 1848) (by decide +kernel) (by decide +kernel) (hc 6 (by norm_num))
  have c20 := vtB_pureAt (rd := rd) (wo := wo) hl 0 (.copy (.n 20) (.n 0)) (by decide +kernel)
  have c21 := vtB_pureAt (rd := rd) (wo := wo) hl 1 (.copy (.n 21) (.n 1)) (by decide +kernel)
  have c22 := vtB_pureAt (rd := rd) (wo := wo) hl 2 (.copy (.n 22) (.n 2)) (by decide +kernel)
  have c23 := vtB_pureAt (rd := rd) (wo := wo) hl 3 (.copy (.n 23) (.n 3)) (by decide +kernel)
  have c24 := vtB_pureAt (rd := rd) (wo := wo) hl 4 (.copy (.n 24) (.n 4)) (by decide +kernel)
  have k1 : (Atom.keccak [.n 813, .n 814, .n 817, .n 818, .n 1303, .n 1304, .n 1317, .n 1318, .n 20,
      .n 21, .n 22, .n 23, .n 24] (vtOuts 1827) false false).Holds rd σv :=
    vtB_keccakAt (wo := wo) hl 1914 (by decide +kernel)
  have z6 := vtB_pureAt (rd := rd) (wo := wo) hl 1927 (.const (.n 1852) (word 0 0)) (by decide +kernel)
  have z7 := vtB_pureAt (rd := rd) (wo := wo) hl 1928 (.const (.n 1853) (word 0 0)) (by decide +kernel)
  have k2 : (Atom.keccak [.n 1841, .n 1842, .n 1845, .n 1846, .n 1849, .n 1850, .n 1852, .n 1853,
      .n 1835, .n 1836, .n 1837, .n 1838, .n 1839] (vtOuts 1854) false false).Holds rd σv :=
    vtB_keccakAt (wo := wo) hl 1929 (by decide +kernel)
  have hch := vtB_pureAt (rd := rd) (wo := wo) hl 1930 (.copy (.n 1867) (.n 1854)) (by decide +kernel)
  have d43 := vtB_pureAt (rd := rd) (wo := wo) hl 1918 (.copy (.n 1843) (.n 1840)) (by decide +kernel)
  have d47 := vtB_pureAt (rd := rd) (wo := wo) hl 1922 (.copy (.n 1847) (.n 1844)) (by decide +kernel)
  have d51 := vtB_pureAt (rd := rd) (wo := wo) hl 1926 (.copy (.n 1851) (.n 1848)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at c20 c21 c22 c23 c24 z6 z7 d43 d47 d51 hch
  have p : ∀ i < 20, σv (.n i) = args.getD i 0 := fun i hi ↦ vt_param hl hi
  generalize vtσ rd wo args = σ at *
  obtain ⟨hP1, hC1⟩ := vt_keccak k1
  obtain ⟨hP2, hC2⟩ := vt_keccak k2
  have e0 := fsPackT_cells p0
  have e1 := fsPackT_cells p1
  have e2 := fsPackT_cells p2
  have e3 := fsPackT_cells p3
  have e4 := fsPackT_cells p4
  have e5 := fsPackT_cells p5
  have e6 := fsPackT_cells p6
  have hxs : xs = [σ (.n 812), σ (.n 816), σ (.n 1302), σ (.n 1316)] := by
    rw [l0, l1, l2, l3]
    match xs, hxl with
    | [a, b, c, d], _ => rfl
  have hw3 : w.take 3 = [σ (.n 1840), σ (.n 1844), σ (.n 1848)] := by
    rw [l4, l5, l6, vt_list10 w hwl]
    simp [hxl]
  have hargs : [args.getD 0 0, args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0] =
      [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] := by
    rw [p 0 (by norm_num), p 1 (by norm_num), p 2 (by norm_num), p 3 (by norm_num),
      p 4 (by norm_num)]
  -- the four framework words, and their permutation
  set S4 : Fs := ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)],
    [(σ (.n 812), dsObserve), (σ (.n 816), dsObserve), (σ (.n 1302), dsObserve),
      (σ (.n 1316), dsObserve)]⟩ with hS4d
  have hS4 : vtF0 args xs = S4 := by
    rw [vtF0, hargs, hxs, absorbAll_short _ _ _ (by simp)]; rfl
  have hin1 : ([.n 813, .n 814, .n 817, .n 818, .n 1303, .n 1304, .n 1317, .n 1318, .n 20,
      .n 21, .n 22, .n 23, .n 24] : List V).map σ = rateOf S4.pend ++ S4.cap := by
    rw [rateOf_eq_cells _ (by simp [hS4d])]
    simp only [hS4d, List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      ← e0, ← e1, ← e2, ← e3, c20, c21, c22, c23, c24]
    rfl
  rw [hin1] at hC1
  have hcap : capOf S4.perm = [σ (.n 1835), σ (.n 1836), σ (.n 1837), σ (.n 1838),
      σ (.n 1839)] := by
    rw [Fs.perm, ← hC1]; rfl
  -- the share and the round's coefficients, after the permutation
  set S7 : Fs := ⟨capOf S4.perm, [(σ (.n 1840), dsObserve), (σ (.n 1844), dsObserve),
    (σ (.n 1848), dsObserve)]⟩ with hS7d
  have hS7 : vtBcF (vtF0 args xs) w = S7 := by
    have h1 : S4.absorb (σ (.n 1840)) dsObserve =
        ⟨capOf S4.perm, [(σ (.n 1840), dsObserve)]⟩ := by
      simp [Fs.absorb, hS4d, rateScalars]
    rw [vtBcF, hS4, hw3]
    show (S4.absorb (σ (.n 1840)) dsObserve).absorbAll [σ (.n 1844), σ (.n 1848)] dsObserve = S7
    rw [h1, absorbAll_short _ _ _ (by simp)]
    rfl
  have hin2 : ([.n 1841, .n 1842, .n 1845, .n 1846, .n 1849, .n 1850, .n 1852, .n 1853, .n 1835,
      .n 1836, .n 1837, .n 1838, .n 1839] : List V).map σ = rateOf S7.pend ++ S7.cap := by
    rw [rateOf_eq_cells _ (by simp [hS7d])]
    simp only [hS7d, hcap, List.map_cons, List.map_nil, pendCells, List.flatMap_cons,
      List.flatMap_nil, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
      List.append_nil, ← e4, ← e5, ← e6, z6, z7]
    rfl
  rw [hin2] at hP2 hC2
  refine ⟨hxs.symm, ?_, ?_, ?_, ?_, ?_, d43, d47, d51⟩
  · rw [l4, List.getD_append_right _ _ _ _ (by omega)]; simp [hxl]
  · rw [l5, List.getD_append_right _ _ _ _ (by omega)]; simp [hxl]
  · rw [l6, List.getD_append_right _ _ _ _ (by omega)]; simp [hxl]
  · rw [vtBcR0, hS7]
    simp only [Fs.squeeze, Fs.perm]
    exact challengeT_value (show ChallengeOk σ (.n 1854) 1867 from hch) (hP2 0 (by omega))
  · rw [hS7]
    simp only [Fs.squeeze, Fs.perm]
    have e : ∀ k, 1854 + 8 + k = 1862 + k := fun k => by omega
    simp only [e] at hC2
    rw [← hC2]
    rfl

/-- A call's returns are the oracle's. -/
theorem vtB_callRets (hl : args.length = 20) (n : ℕ) {f : String} {as rs : List V}
    (heq : tbStmtsEqb [.call f as rs] ((vtAt n).take 1) = true) :
    rs.map σv = rs.map fun v ↦ wo v.idx := by
  have g := vt_goodAt (rd := rd) (w := wo) hl n _ heq
  exact List.map_congr_left fun v hv ↦ g v hv

theorem vt_range8 (wo : ℕ → E) (b : ℕ) : (List.range 8).map (fun i ↦ wo (b + i)) =
    [wo b, wo (b + 1), wo (b + 2), wo (b + 3), wo (b + 4), wo (b + 5), wo (b + 6), wo (b + 7)] := by
  simp [List.range_succ]

set_option maxRecDepth 10000 in
/-- **The bytecode share, honestly**: with the cursor holding the four framework words and the
share's ten, `fp_w` the sixteen slot weights, `bc_point` the honest slot point, the oracle
returning the three tail rounds' words, and the last claim accepted, the share's stores into
`bc_point`, its three `opening_tail_round` calls, its read of the value and its closing check
hold; the share, the value, the last round's capacity and the cursor after it are the honest
ones. -/
theorem vtB_bc (hl : args.length = 20) {xs w weights : List E} (hxl : xs.length = 4)
    (hwl : w.length = 10) (hcur : TbReadsAt rd (args.getD 5 0) (xs ++ w))
    (hW16 : weights.length = 16) (hW : TbReadsAt rd (args.getD 13 0) weights)
    (hpt : TbReadsAt rd (args.getD 19 0) (vtBcPoint (vtF0 args xs) w))
    (hw1 : (List.range 8).map (fun i ↦ wo (1876 + i)) = (vtBcR1 (vtF0 args xs) w).1 ++
      [args.getD 5 0 * gen ^ 7 * gen ^ 2, (vtBcR1 (vtF0 args xs) w).2.1,
        (vtBcR1 (vtF0 args xs) w).2.2])
    (hw2 : (List.range 8).map (fun i ↦ wo (1884 + i)) = (vtBcR2 (vtF0 args xs) w).1 ++
      [args.getD 5 0 * gen ^ 7 * gen ^ 2 * gen ^ 2, (vtBcR2 (vtF0 args xs) w).2.1,
        (vtBcR2 (vtF0 args xs) w).2.2])
    (hw3 : (List.range 8).map (fun i ↦ wo (1892 + i)) = (vtBcR3 (vtF0 args xs) w).1 ++
      [args.getD 5 0 * gen ^ 7 * gen ^ 2 * gen ^ 2 * gen ^ 2, (vtBcR3 (vtF0 args xs) w).2.1,
        (vtBcR3 (vtF0 args xs) w).2.2])
    (hacc : (vtBcR3 (vtF0 args xs) w).2.1 =
      dot (eqKernel (vtBcPoint (vtF0 args xs) w)) weights * w.getD 9 0) :
    VSH (coreProgram.Rel rd) rd σv (.atom (.load (.n 1867) (.n 19) 0)) ∧
    VSH (coreProgram.Rel rd) rd σv (.call "opening_tail_round" [.n 1862, .n 1863, .n 1864, .n 1865,
      .n 1866, .n 1875, .n 1873, .n 18] [.n 1876, .n 1877, .n 1878, .n 1879, .n 1880, .n 1881,
      .n 1882, .n 1883]) ∧
    VSH (coreProgram.Rel rd) rd σv (.atom (.load (.n 1883) (.n 19) 1)) ∧
    VSH (coreProgram.Rel rd) rd σv (.call "opening_tail_round" [.n 1876, .n 1877, .n 1878, .n 1879,
      .n 1880, .n 1881, .n 1882, .n 18] [.n 1884, .n 1885, .n 1886, .n 1887, .n 1888, .n 1889,
      .n 1890, .n 1891]) ∧
    VSH (coreProgram.Rel rd) rd σv (.atom (.load (.n 1891) (.n 19) 2)) ∧
    VSH (coreProgram.Rel rd) rd σv (.call "opening_tail_round" [.n 1884, .n 1885, .n 1886, .n 1887,
      .n 1888, .n 1889, .n 1890, .n 18] [.n 1892, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897,
      .n 1898, .n 1899]) ∧
    VSH (coreProgram.Rel rd) rd σv (.atom (.load (.n 1899) (.n 19) 3)) ∧
    VSH (coreProgram.Rel rd) rd σv (.atom (.load (.n 1905) (.n 1897) 0)) ∧
    VSH (coreProgram.Rel rd) rd σv (.atom (.assertEq (.n 1898) (.n 1973))) ∧
    σv (.n 1840) = w.getD 0 0 ∧ σv (.n 1905) = w.getD 9 0 ∧
    [σv (.n 1892), σv (.n 1893), σv (.n 1894), σv (.n 1895), σv (.n 1896)] =
      (vtBcR3 (vtF0 args xs) w).1 ∧
    σv (.n 1897) = args.getD 5 0 * gen ^ 13 := by
  obtain ⟨-, e40, e44, e48, e67, ecap, d43, d47, d51⟩ := vtB_fresh (wo := wo) hl hxl hwl hcur
  have p : ∀ i < 20, σv (.n i) = args.getD i 0 := fun i hi ↦ vt_param hl hi
  have hlen : (xs ++ w).length = 14 := by simp [hxl, hwl]
  have hc : ∀ k (hk : k < 10), LoadHolds rd (args.getD 5 0) (4 + k) (w.getD k 0) := fun k hk ↦ by
    have := hcur (4 + k) (by rw [hlen]; omega)
    rw [List.getElem_append_right (by omega)] at this
    simp only [hxl, Nat.add_sub_cancel_left] at this
    rwa [List.getD_eq_getElem w 0 (by omega)]
  have hw13 : ∀ i < 16, LoadHolds rd (σv (.n 13)) i (weights.getD i 0) := fun i hi ↦ by
    rw [p 13 (by norm_num), List.getD_eq_getElem weights 0 (by omega)]; exact hW i (by omega)
  have hpt19 : ∀ i < 4, LoadHolds rd (σv (.n 19)) i ((vtBcPoint (vtF0 args xs) w).getD i 0) :=
    fun i hi ↦ by
      have h4 : (vtBcPoint (vtF0 args xs) w).length = 4 := rfl
      rw [p 19 (by norm_num), List.getD_eq_getElem (vtBcPoint (vtF0 args xs) w) 0 (by omega)]
      exact hpt i (by omega)
  -- the calls' returns
  have r1 := vtB_callRets (rd := rd) (wo := wo) hl 1940 (f := "opening_tail_round")
    (as := [.n 1862, .n 1863, .n 1864, .n 1865, .n 1866, .n 1875, .n 1873, .n 18])
    (rs := [.n 1876, .n 1877, .n 1878, .n 1879, .n 1880, .n 1881, .n 1882, .n 1883])
    (by decide +kernel)
  have r2 := vtB_callRets (rd := rd) (wo := wo) hl 1942 (f := "opening_tail_round")
    (as := [.n 1876, .n 1877, .n 1878, .n 1879, .n 1880, .n 1881, .n 1882, .n 18])
    (rs := [.n 1884, .n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890, .n 1891])
    (by decide +kernel)
  have r3 := vtB_callRets (rd := rd) (wo := wo) hl 1944 (f := "opening_tail_round")
    (as := [.n 1884, .n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890, .n 18])
    (rs := [.n 1892, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897, .n 1898, .n 1899])
    (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at r1 r2 r3
  rw [vt_range8] at hw1 hw2 hw3
  obtain ⟨q1, u1, v1, s1⟩ := vt_split8 (C := (vtBcR1 (vtF0 args xs) w).1) rfl (r1.trans hw1)
  obtain ⟨q2, u2, v2, s2⟩ := vt_split8 (C := (vtBcR2 (vtF0 args xs) w).1) rfl (r2.trans hw2)
  obtain ⟨q3, u3, v3, s3⟩ := vt_split8 (C := (vtBcR3 (vtF0 args xs) w).1) rfl (r3.trans hw3)
  -- the value
  have hm : LoadHolds rd (σv (.n 1897)) 0 (w.getD 9 0) := by
    rw [u3, loadHolds_mul_gen_pow, loadHolds_mul_gen_pow, loadHolds_mul_gen_pow,
      loadHolds_mul_gen_pow]
    exact hc 9 (by norm_num)
  obtain ⟨e1905, l1951⟩ := vt_readAt (rd := rd) (w := wo) hl 1951 (d := .n 1905) (p := .n 1897)
    (off := 0) (by decide +kernel) (by decide +kernel) hm
  -- the round's arithmetic and the fold of `fp_w`
  have a1932 := vtB_pureAt (rd := rd) (wo := wo) hl 1932 (.const (.n 1868) (word 1 0)) (by decide +kernel)
  have a1933 := vtB_pureAt (rd := rd) (wo := wo) hl 1933 (.add (.n 1869) (.n 1868) (.n 1867)) (by decide +kernel)
  have a1934 := vtB_pureAt (rd := rd) (wo := wo) hl 1934 (.mul (.n 1870) (.n 1869) (.n 1851)) (by decide +kernel)
  have a1935 := vtB_pureAt (rd := rd) (wo := wo) hl 1935 (.add (.n 1871) (.n 1843) (.n 1870)) (by decide +kernel)
  have a1936 := vtB_pureAt (rd := rd) (wo := wo) hl 1936 (.mul (.n 1872) (.n 1867) (.n 1871)) (by decide +kernel)
  have a1937 := vtB_pureAt (rd := rd) (wo := wo) hl 1937 (.add (.n 1873) (.n 1847) (.n 1872)) (by decide +kernel)
  have a1938 := vtB_pureAt (rd := rd) (wo := wo) hl 1938 (.const (.n 1874) (word 128 0)) (by decide +kernel)
  have a1939 := vtB_pureAt (rd := rd) (wo := wo) hl 1939 (.mul (.n 1875) (.n 5) (.n 1874)) (by decide +kernel)
  have c0 := vtB_pureAt (rd := rd) (wo := wo) hl 1946 (.copy (.n 1900) (.n 1892)) (by decide +kernel)
  have c1 := vtB_pureAt (rd := rd) (wo := wo) hl 1947 (.copy (.n 1901) (.n 1893)) (by decide +kernel)
  have c2 := vtB_pureAt (rd := rd) (wo := wo) hl 1948 (.copy (.n 1902) (.n 1894)) (by decide +kernel)
  have c3 := vtB_pureAt (rd := rd) (wo := wo) hl 1949 (.copy (.n 1903) (.n 1895)) (by decide +kernel)
  have c4 := vtB_pureAt (rd := rd) (wo := wo) hl 1950 (.copy (.n 1904) (.n 1896)) (by decide +kernel)
  have cv := vtB_pureAt (rd := rd) (wo := wo) hl 1952 (.copy (.n 1906) (.n 1905)) (by decide +kernel)
  have a1957 := vtB_pureAt (rd := rd) (wo := wo) hl 1957 (.add (.n 1911) (.n 1909) (.n 1910)) (by decide +kernel)
  have a1958 := vtB_pureAt (rd := rd) (wo := wo) hl 1958 (.mul (.n 1912) (.n 1908) (.n 1911)) (by decide +kernel)
  have a1959 := vtB_pureAt (rd := rd) (wo := wo) hl 1959 (.add (.n 1913) (.n 1909) (.n 1912)) (by decide +kernel)
  have a1962 := vtB_pureAt (rd := rd) (wo := wo) hl 1962 (.add (.n 1916) (.n 1914) (.n 1915)) (by decide +kernel)
  have a1963 := vtB_pureAt (rd := rd) (wo := wo) hl 1963 (.mul (.n 1917) (.n 1908) (.n 1916)) (by decide +kernel)
  have a1964 := vtB_pureAt (rd := rd) (wo := wo) hl 1964 (.add (.n 1918) (.n 1914) (.n 1917)) (by decide +kernel)
  have a1967 := vtB_pureAt (rd := rd) (wo := wo) hl 1967 (.add (.n 1921) (.n 1919) (.n 1920)) (by decide +kernel)
  have a1968 := vtB_pureAt (rd := rd) (wo := wo) hl 1968 (.mul (.n 1922) (.n 1908) (.n 1921)) (by decide +kernel)
  have a1969 := vtB_pureAt (rd := rd) (wo := wo) hl 1969 (.add (.n 1923) (.n 1919) (.n 1922)) (by decide +kernel)
  have a1972 := vtB_pureAt (rd := rd) (wo := wo) hl 1972 (.add (.n 1926) (.n 1924) (.n 1925)) (by decide +kernel)
  have a1973 := vtB_pureAt (rd := rd) (wo := wo) hl 1973 (.mul (.n 1927) (.n 1908) (.n 1926)) (by decide +kernel)
  have a1974 := vtB_pureAt (rd := rd) (wo := wo) hl 1974 (.add (.n 1928) (.n 1924) (.n 1927)) (by decide +kernel)
  have a1977 := vtB_pureAt (rd := rd) (wo := wo) hl 1977 (.add (.n 1931) (.n 1929) (.n 1930)) (by decide +kernel)
  have a1978 := vtB_pureAt (rd := rd) (wo := wo) hl 1978 (.mul (.n 1932) (.n 1908) (.n 1931)) (by decide +kernel)
  have a1979 := vtB_pureAt (rd := rd) (wo := wo) hl 1979 (.add (.n 1933) (.n 1929) (.n 1932)) (by decide +kernel)
  have a1982 := vtB_pureAt (rd := rd) (wo := wo) hl 1982 (.add (.n 1936) (.n 1934) (.n 1935)) (by decide +kernel)
  have a1983 := vtB_pureAt (rd := rd) (wo := wo) hl 1983 (.mul (.n 1937) (.n 1908) (.n 1936)) (by decide +kernel)
  have a1984 := vtB_pureAt (rd := rd) (wo := wo) hl 1984 (.add (.n 1938) (.n 1934) (.n 1937)) (by decide +kernel)
  have a1987 := vtB_pureAt (rd := rd) (wo := wo) hl 1987 (.add (.n 1941) (.n 1939) (.n 1940)) (by decide +kernel)
  have a1988 := vtB_pureAt (rd := rd) (wo := wo) hl 1988 (.mul (.n 1942) (.n 1908) (.n 1941)) (by decide +kernel)
  have a1989 := vtB_pureAt (rd := rd) (wo := wo) hl 1989 (.add (.n 1943) (.n 1939) (.n 1942)) (by decide +kernel)
  have a1992 := vtB_pureAt (rd := rd) (wo := wo) hl 1992 (.add (.n 1946) (.n 1944) (.n 1945)) (by decide +kernel)
  have a1993 := vtB_pureAt (rd := rd) (wo := wo) hl 1993 (.mul (.n 1947) (.n 1908) (.n 1946)) (by decide +kernel)
  have a1994 := vtB_pureAt (rd := rd) (wo := wo) hl 1994 (.add (.n 1948) (.n 1944) (.n 1947)) (by decide +kernel)
  have a1996 := vtB_pureAt (rd := rd) (wo := wo) hl 1996 (.add (.n 1950) (.n 1913) (.n 1918)) (by decide +kernel)
  have a1997 := vtB_pureAt (rd := rd) (wo := wo) hl 1997 (.mul (.n 1951) (.n 1949) (.n 1950)) (by decide +kernel)
  have a1998 := vtB_pureAt (rd := rd) (wo := wo) hl 1998 (.add (.n 1952) (.n 1913) (.n 1951)) (by decide +kernel)
  have a1999 := vtB_pureAt (rd := rd) (wo := wo) hl 1999 (.add (.n 1953) (.n 1923) (.n 1928)) (by decide +kernel)
  have a2000 := vtB_pureAt (rd := rd) (wo := wo) hl 2000 (.mul (.n 1954) (.n 1949) (.n 1953)) (by decide +kernel)
  have a2001 := vtB_pureAt (rd := rd) (wo := wo) hl 2001 (.add (.n 1955) (.n 1923) (.n 1954)) (by decide +kernel)
  have a2002 := vtB_pureAt (rd := rd) (wo := wo) hl 2002 (.add (.n 1956) (.n 1933) (.n 1938)) (by decide +kernel)
  have a2003 := vtB_pureAt (rd := rd) (wo := wo) hl 2003 (.mul (.n 1957) (.n 1949) (.n 1956)) (by decide +kernel)
  have a2004 := vtB_pureAt (rd := rd) (wo := wo) hl 2004 (.add (.n 1958) (.n 1933) (.n 1957)) (by decide +kernel)
  have a2005 := vtB_pureAt (rd := rd) (wo := wo) hl 2005 (.add (.n 1959) (.n 1943) (.n 1948)) (by decide +kernel)
  have a2006 := vtB_pureAt (rd := rd) (wo := wo) hl 2006 (.mul (.n 1960) (.n 1949) (.n 1959)) (by decide +kernel)
  have a2007 := vtB_pureAt (rd := rd) (wo := wo) hl 2007 (.add (.n 1961) (.n 1943) (.n 1960)) (by decide +kernel)
  have a2009 := vtB_pureAt (rd := rd) (wo := wo) hl 2009 (.add (.n 1963) (.n 1952) (.n 1955)) (by decide +kernel)
  have a2010 := vtB_pureAt (rd := rd) (wo := wo) hl 2010 (.mul (.n 1964) (.n 1962) (.n 1963)) (by decide +kernel)
  have a2011 := vtB_pureAt (rd := rd) (wo := wo) hl 2011 (.add (.n 1965) (.n 1952) (.n 1964)) (by decide +kernel)
  have a2012 := vtB_pureAt (rd := rd) (wo := wo) hl 2012 (.add (.n 1966) (.n 1958) (.n 1961)) (by decide +kernel)
  have a2013 := vtB_pureAt (rd := rd) (wo := wo) hl 2013 (.mul (.n 1967) (.n 1962) (.n 1966)) (by decide +kernel)
  have a2014 := vtB_pureAt (rd := rd) (wo := wo) hl 2014 (.add (.n 1968) (.n 1958) (.n 1967)) (by decide +kernel)
  have a2016 := vtB_pureAt (rd := rd) (wo := wo) hl 2016 (.add (.n 1970) (.n 1965) (.n 1968)) (by decide +kernel)
  have a2017 := vtB_pureAt (rd := rd) (wo := wo) hl 2017 (.mul (.n 1971) (.n 1969) (.n 1970)) (by decide +kernel)
  have a2018 := vtB_pureAt (rd := rd) (wo := wo) hl 2018 (.add (.n 1972) (.n 1965) (.n 1971)) (by decide +kernel)
  have a2019 := vtB_pureAt (rd := rd) (wo := wo) hl 2019 (.mul (.n 1973) (.n 1972) (.n 1905)) (by decide +kernel)
  have w0 := (vt_readAt (rd := rd) (w := wo) hl 1955 (d := (.n 1909)) (by decide +kernel) (by decide +kernel) (hw13 0 (by norm_num))).1
  have w1 := (vt_readAt (rd := rd) (w := wo) hl 1956 (d := (.n 1910)) (by decide +kernel) (by decide +kernel) (hw13 1 (by norm_num))).1
  have w2 := (vt_readAt (rd := rd) (w := wo) hl 1960 (d := (.n 1914)) (by decide +kernel) (by decide +kernel) (hw13 2 (by norm_num))).1
  have w3 := (vt_readAt (rd := rd) (w := wo) hl 1961 (d := (.n 1915)) (by decide +kernel) (by decide +kernel) (hw13 3 (by norm_num))).1
  have w4 := (vt_readAt (rd := rd) (w := wo) hl 1965 (d := (.n 1919)) (by decide +kernel) (by decide +kernel) (hw13 4 (by norm_num))).1
  have w5 := (vt_readAt (rd := rd) (w := wo) hl 1966 (d := (.n 1920)) (by decide +kernel) (by decide +kernel) (hw13 5 (by norm_num))).1
  have w6 := (vt_readAt (rd := rd) (w := wo) hl 1970 (d := (.n 1924)) (by decide +kernel) (by decide +kernel) (hw13 6 (by norm_num))).1
  have w7 := (vt_readAt (rd := rd) (w := wo) hl 1971 (d := (.n 1925)) (by decide +kernel) (by decide +kernel) (hw13 7 (by norm_num))).1
  have w8 := (vt_readAt (rd := rd) (w := wo) hl 1975 (d := (.n 1929)) (by decide +kernel) (by decide +kernel) (hw13 8 (by norm_num))).1
  have w9 := (vt_readAt (rd := rd) (w := wo) hl 1976 (d := (.n 1930)) (by decide +kernel) (by decide +kernel) (hw13 9 (by norm_num))).1
  have w10 := (vt_readAt (rd := rd) (w := wo) hl 1980 (d := (.n 1934)) (by decide +kernel) (by decide +kernel) (hw13 10 (by norm_num))).1
  have w11 := (vt_readAt (rd := rd) (w := wo) hl 1981 (d := (.n 1935)) (by decide +kernel) (by decide +kernel) (hw13 11 (by norm_num))).1
  have w12 := (vt_readAt (rd := rd) (w := wo) hl 1985 (d := (.n 1939)) (by decide +kernel) (by decide +kernel) (hw13 12 (by norm_num))).1
  have w13 := (vt_readAt (rd := rd) (w := wo) hl 1986 (d := (.n 1940)) (by decide +kernel) (by decide +kernel) (hw13 13 (by norm_num))).1
  have w14 := (vt_readAt (rd := rd) (w := wo) hl 1990 (d := (.n 1944)) (by decide +kernel) (by decide +kernel) (hw13 14 (by norm_num))).1
  have w15 := (vt_readAt (rd := rd) (w := wo) hl 1991 (d := (.n 1945)) (by decide +kernel) (by decide +kernel) (hw13 15 (by norm_num))).1
  have l0 := (vt_readAt (rd := rd) (w := wo) hl 1954 (d := (.n 1908)) (by decide +kernel) (by decide +kernel) (hpt19 0 (by norm_num))).1
  have l1 := (vt_readAt (rd := rd) (w := wo) hl 1995 (d := (.n 1949)) (by decide +kernel) (by decide +kernel) (hpt19 1 (by norm_num))).1
  have l2 := (vt_readAt (rd := rd) (w := wo) hl 2008 (d := (.n 1962)) (by decide +kernel) (by decide +kernel) (hpt19 2 (by norm_num))).1
  have l3 := (vt_readAt (rd := rd) (w := wo) hl 2015 (d := (.n 1969)) (by decide +kernel) (by decide +kernel) (hpt19 3 (by norm_num))).1
  simp only [Atom.Holds] at a1932 a1933 a1934 a1935 a1936 a1937 a1938 a1939 c0 c1 c2 c3
  simp only [Atom.Holds] at c4 cv a1957 a1958 a1959 a1962 a1963 a1964 a1967 a1968 a1969 a1972
  simp only [Atom.Holds] at a1973 a1974 a1977 a1978 a1979 a1982 a1983 a1984 a1987 a1988 a1989 a1992
  simp only [Atom.Holds] at a1993 a1994 a1996 a1997 a1998 a1999 a2000 a2001 a2002 a2003 a2004 a2005
  simp only [Atom.Holds] at a2006 a2007 a2009 a2010 a2011 a2012 a2013 a2014 a2016 a2017 a2018 a2019
  simp only [vtBcPoint, List.getD_cons_zero, List.getD_cons_succ] at l0 l1 l2 l3
  have p5 := p 5 (by norm_num)
  generalize vtσ rd wo args = σ at *
  have h1875 : σ (.n 1875) = args.getD 5 0 * gen ^ 7 := by
    rw [a1939, a1938, p5, show (128 : ℕ) = 2 ^ 7 by norm_num, tb_word_two_pow (by norm_num)]
  have h1873 : σ (.n 1873) = vtBcCl1 (vtF0 args xs) w := by
    rw [a1937, a1936, a1935, a1934, a1933, a1932, tb_word_one, d43, d47, d51, e40, e44, e48, e67,
      vtBcCl1]
  have e1972 : σ (.n 1972) = multilinearEval ((List.range 16).map fun i ↦ weights.getD i 0)
      (vtBcPoint (vtF0 args xs) w) := by
    rw [a2018, a2017, a2016, a2011, a2010, a2009, a2014, a2013, a2012, a1998, a1997, a1996,
      a2001, a2000, a1999, a2004, a2003, a2002, a2007, a2006, a2005, a1959, a1958, a1957,
      a1964, a1963, a1962, a1969, a1968, a1967, a1974, a1973, a1972, a1979, a1978, a1977,
      a1984, a1983, a1982, a1989, a1988, a1987, a1994, a1993, a1992, l0, l1, l2, l3,
      w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]
    simp only [vtBcPoint, multilinearEval, List.range_succ, List.range_zero,
      List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.foldl_cons,
      List.foldl_nil, foldPairs, List.headD_cons]
    ring
  have h1973 : σ (.n 1973) = dot (eqKernel (vtBcPoint (vtF0 args xs) w)) weights * w.getD 9 0 := by
    rw [a2019, e1972, e1905, ← vt_list16 weights hW16,
      multilinearEval_eq_dot weights _ hW16 (by simp [vtBcPoint])]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, l1951, ?_, e40, e1905, q3, ?_⟩
  · show LoadHolds rd (σ (.n 19)) 0 (σ (.n 1867))
    rw [e67]; exact hpt19 0 (by norm_num)
  · show coreProgram.Rel rd "opening_tail_round" [σ (.n 1862), σ (.n 1863), σ (.n 1864),
      σ (.n 1865), σ (.n 1866), σ (.n 1875), σ (.n 1873), σ (.n 18)] [σ (.n 1876), σ (.n 1877),
      σ (.n 1878), σ (.n 1879), σ (.n 1880), σ (.n 1881), σ (.n 1882), σ (.n 1883)]
    rw [opening_tail_round_holds]
    refine ⟨w.getD 3 0, w.getD 4 0, fun k hk ↦ ?_, ?_⟩
    · simp only [List.length_cons, List.length_nil] at hk
      rw [h1875, loadHolds_mul_gen_pow]
      interval_cases k
      · exact hc 3 (by norm_num)
      · exact hc 4 (by norm_num)
    · rw [r1.trans hw1, ecap, h1875, h1873]
      rfl
  · show LoadHolds rd (σ (.n 19)) 1 (σ (.n 1883))
    rw [s1]; exact hpt19 1 (by norm_num)
  · show coreProgram.Rel rd "opening_tail_round" [σ (.n 1876), σ (.n 1877), σ (.n 1878),
      σ (.n 1879), σ (.n 1880), σ (.n 1881), σ (.n 1882), σ (.n 18)] [σ (.n 1884), σ (.n 1885),
      σ (.n 1886), σ (.n 1887), σ (.n 1888), σ (.n 1889), σ (.n 1890), σ (.n 1891)]
    rw [opening_tail_round_holds]
    refine ⟨w.getD 5 0, w.getD 6 0, fun k hk ↦ ?_, ?_⟩
    · simp only [List.length_cons, List.length_nil] at hk
      rw [u1, loadHolds_mul_gen_pow, loadHolds_mul_gen_pow]
      interval_cases k
      · exact hc 5 (by norm_num)
      · exact hc 6 (by norm_num)
    · rw [r2.trans hw2, q1, u1, v1]
      rfl
  · show LoadHolds rd (σ (.n 19)) 2 (σ (.n 1891))
    rw [s2]; exact hpt19 2 (by norm_num)
  · show coreProgram.Rel rd "opening_tail_round" [σ (.n 1884), σ (.n 1885), σ (.n 1886),
      σ (.n 1887), σ (.n 1888), σ (.n 1889), σ (.n 1890), σ (.n 18)] [σ (.n 1892), σ (.n 1893),
      σ (.n 1894), σ (.n 1895), σ (.n 1896), σ (.n 1897), σ (.n 1898), σ (.n 1899)]
    rw [opening_tail_round_holds]
    refine ⟨w.getD 7 0, w.getD 8 0, fun k hk ↦ ?_, ?_⟩
    · simp only [List.length_cons, List.length_nil] at hk
      rw [u2, loadHolds_mul_gen_pow, loadHolds_mul_gen_pow, loadHolds_mul_gen_pow]
      interval_cases k
      · exact hc 7 (by norm_num)
      · exact hc 8 (by norm_num)
    · rw [r3.trans hw3, q2, u2, v2]
      rfl
  · show LoadHolds rd (σ (.n 19)) 3 (σ (.n 1899))
    rw [s3]; exact hpt19 3 (by norm_num)
  · show σ (.n 1898) + σ (.n 1973) = 0
    rw [e_add_eq_zero_iff, v3, h1973, hacc]
  · rw [u3]; ring

end

end
end LeanVM.Guest.B1.Tables
