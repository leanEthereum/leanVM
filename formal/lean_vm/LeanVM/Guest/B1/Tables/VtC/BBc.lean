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
# The bytecode share, honestly (G:2472-2519)

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

theorem bcRound_cap_length {cap : List E} {claim a b : E} : (bcRound cap claim a b).1.length = 5 :=
  rfl

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

end

end
end LeanVM.Guest.B1.Tables
