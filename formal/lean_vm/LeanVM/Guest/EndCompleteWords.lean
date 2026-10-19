/-
  LeanVM.Guest.EndCompleteWords

  `main`'s bound as a `Linear` in the node's work: generic in the frame function and the callees'
  bounds (`eaLin`, `ea_bound`), at the words (`eaWords`, `ea_words`).
-/

module

public import LeanVM.Guest.B1.Main.MainBudget
public import LeanVM.Guest.B1.Main.CalleesProved
public import LeanVM.Guest.B1.Main.HonestWords
public import LeanVM.Guest.B1.Da.DvAffine

/-!
# `main`'s bound within a linear budget

`mainBound fr Bd W` is `main`'s frame, buffers and callees' bounds at the frame function `fr` and
the callees' bounds `Bd`. `eaLin fr Bd A`: a constant, plus per unit of work what a declared claim,
a coverage slot, a raw signature or matrix, a child and a child's claim add, given the claim lists',
the child claim lists' and the DA lists' bounds affine (`EaAffC`, `EaAffOk`). `ea_bound`: at the
honest words of a node within the limits, `mainBound fr Bd` is at most it. At the words
(`fr := fs`, `Bd := calleeBd fs H`): `eaWords`, `ea_words`, the claim lists' bound affine once
`__loop86`'s is (`a86`, `b86`). At an instruction weight (`fr := ω`, `Bd` the callees' weight
bounds), the same `ea_bound` gives the instruction budget.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.End (Limits Linear work coverage bytecode)

@[expose] public section

/-- The largest of a list. -/
def eaMax (l : List ℕ) : ℕ := l.foldr max 0

theorem ea_le_max : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ eaMax l
  | [], _, h => absurd h (by simp)
  | y :: l, x, h => by
    unfold eaMax
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ea_le_max h) (le_max_right _ _)

/-! ## Generic in the frame function and the callees' bounds -/

/-- The affine constants of the callees' bounds that grow: a claim list's slope and constant, a
child claim list's, the DA lists' largest, and the direct DA claim's check per matrix and per row. -/
structure EaAffC where
  aCl : ℕ
  bCl : ℕ
  aCcl : ℕ
  bCcl : ℕ
  dlMax : ℕ
  dvA : ℕ
  dvB : ℕ

/-- The callees' bounds within those constants. -/
structure EaAffOk (Bd : CalleeBounds) (A : EaAffC) : Prop where
  cl : ∀ n, Bd.cl n ≤ A.aCl * n + A.bCl
  ccl : ∀ n, Bd.ccl n ≤ A.aCcl * n + A.bCcl
  dl : ∀ n ≤ 16, Bd.daList n ≤ A.dlMax
  dv : ∀ r, Bd.daVerify r ≤ A.dvA + A.dvB * r
  dvW : ∀ θ r, Bd.daVerifyW θ r ≤ Digest.dvWA θ + Digest.dvWB θ * r

variable (fr : String → ℕ) (Bd : CalleeBounds) (A : EaAffC)

/-- The batching's slope and constant. -/
def eaAggA : ℕ := 18 + fr "__loop95" + fr "__loop96" + fr "__loop97" + fr "__loop98" + fr "__loop99"
def eaAggB : ℕ := fr "aggregate_claims" + 413 + fr "__loop95" + fr "__loop96" + fr "__loop97" +
  fr "__loop98" + fr "__loop99" + fr "batch_sumcheck__L22" + fr "batch_sumcheck__L28"

theorem ea_agg (n : ℕ) : aggBound fr n = eaAggA fr * n + eaAggB fr := by
  simp only [aggBound, aggSizes, eaAggA, eaAggB, List.sum_cons, List.sum_nil]; ring

/-- A child's bound, affinely in its claims: constant and slope. -/
def eaChK : ℕ := 2 + 2 * A.bCcl + fr "__loop100" + A.dlMax + Bd.sd + Bd.vs
def eaChA : ℕ := 4 + A.aCcl + fr "__loop100" + Bd.cover

theorem ea_childBd {Bd : CalleeBounds} {A : EaAffC} (hA : EaAffOk Bd A) (r : ChildWords)
    (hda : r.da.length ≤ 16) :
    childBd fr Bd r ≤ eaChK fr Bd A + eaChA fr Bd A * (r.nx + r.ns + r.da.length) := by
  have c1 := hA.ccl r.nx
  have c2 := hA.ccl r.ns
  have d := hA.dl r.da.length hda
  have e1 : A.aCcl * r.nx ≤ eaChA fr Bd A * r.nx := Nat.mul_le_mul_right _ (by unfold eaChA; omega)
  have e2 : A.aCcl * r.ns ≤ eaChA fr Bd A * r.ns := Nat.mul_le_mul_right _ (by unfold eaChA; omega)
  have e3 : r.da.length * (fr "__loop100" + Bd.cover) + 4 * r.da.length ≤ eaChA fr Bd A * r.da.length := by
    have : (fr "__loop100" + Bd.cover) + 4 ≤ eaChA fr Bd A := by unfold eaChA; omega
    nlinarith
  have e4 : eaChA fr Bd A * (r.nx + r.ns + r.da.length) =
      eaChA fr Bd A * r.nx + eaChA fr Bd A * r.ns + eaChA fr Bd A * r.da.length := by ring
  simp only [childBd, eaChK]
  omega

theorem ea_loopSum (c K K' : ℕ) (bs : ℕ → ℕ) : ∀ (L : List Child) (j : ℕ),
    (∀ i (hi : i < L.length), bs (j + i) ≤ K + K' * cnw L[i]) →
    loopSum c bs j L.length ≤ L.length * (c + K) + c + K' * (L.map cnw).sum
  | [], _, _ => by simp [loopSum]
  | x :: L, j, h => by
    have ih := ea_loopSum c K K' bs L (j + 1) fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show j + (i + 1) = j + 1 + i by ring] at this
      simpa using this
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    simp only [List.length_cons, loopSum, List.map_cons, List.sum_cons]
    nlinarith

/-- **`main`'s bound, linearly in the work.** -/
def eaLin : Linear where
  base := fr "main" + 56 + fr "exponent_tables" + 68 + fr "__loop0" + A.dlMax + 2 * A.bCl +
    fr "__loop1" + fr "__loop2" + fr "__loop3" + fr "__loop4" + fr "__loop5" + eaAggB fr + Bd.sd
  declared := A.aCl
  coverage := 5 + fr "__loop0" + fr "__loop1" + fr "__loop2"
  rawXmss := fr "__loop3" + Bd.xmss
  rawSphincs := fr "__loop4" + Bd.sphincs
  rawDa := A.dvA + Bd.cover
  rawDaRows := A.dvB
  children := 162 + fr "__loop5" + eaChK fr Bd A + eaAggA fr
  childClaims := eaChA fr Bd A

theorem ea_eval (u : LeanVM.Guest.End.Work) : (eaLin fr Bd A).eval u =
    (eaLin fr Bd A).base + A.aCl * u.declared +
      (5 + fr "__loop0" + fr "__loop1" + fr "__loop2") * u.coverage + (fr "__loop3" + Bd.xmss) * u.rawXmss +
      (fr "__loop4" + Bd.sphincs) * u.rawSphincs + (A.dvA + Bd.cover) * u.rawDa + A.dvB * u.rawDaRows +
      (162 + fr "__loop5" + eaChK fr Bd A + eaAggA fr) * u.children + eaChA fr Bd A * u.childClaims := rfl

set_option maxHeartbeats 1000000 in
/-- **`main`'s bound at the honest words is within `eaLin`**, for a node within the limits. -/
theorem ea_bound {Bd : CalleeBounds} {A : EaAffC} (hA : EaAffOk Bd A) {seed : Digest} {s : NodeStatement}
    {w : NodeWitness} (hlim : Limits s w) :
    mainBound fr Bd (honestWords seed s w) ≤ (eaLin fr Bd A).eval (work s w) := by
  rw [ea_eval]
  set W := honestWords seed s w with hW
  have hcov : (work s w).coverage = W.total := by
    show coverage s w = _
    rw [coverage_eq]; rfl
  have hdecl : (work s w).declared = W.dx + W.ds + W.da := rfl
  have hrx : (work s w).rawXmss = W.rx := rfl
  have hrs : (work s w).rawSphincs = W.rs := rfl
  have hrd : (work s w).rawDa = W.rd := rfl
  have hrr : (work s w).rawDaRows = W.drows := rfl
  have hnc : (work s w).children = W.nc := rfl
  have hcc : (work s w).childClaims = (w.children.map cnw).sum := rfl
  have hrd1 : W.rd ≤ 1 := hlim.directDa
  have hda16 : W.da ≤ 16 := hlim.daRoots.1
  have htot : W.total = W.dx + W.ux + (W.ds + W.us) + (W.da + W.ud) := rfl
  have hsz : W.sizes.sum = 5 * W.total + 162 * W.nc + 56 := by
    simp only [MainWords.sizes, List.sum_cons, List.sum_nil, htot]; ring
  have c1 := hA.cl W.dx
  have c2 := hA.cl W.ds
  have d1 := hA.dl W.da hda16
  have m0 : (W.da + W.ud) * fr "__loop0" ≤ fr "__loop0" * W.total := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have m1 : W.ux * fr "__loop1" ≤ fr "__loop1" * W.total := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have m2 : W.us * fr "__loop2" ≤ fr "__loop2" * W.total := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have m3 : (5 + fr "__loop0" + fr "__loop1" + fr "__loop2") * W.total =
      5 * W.total + fr "__loop0" * W.total + fr "__loop1" * W.total + fr "__loop2" * W.total := by ring
  have m4 : A.aCl * (W.dx + W.ds + W.da) ≥ A.aCl * W.dx + A.aCl * W.ds := by
    rw [Nat.mul_add, Nat.mul_add]; omega
  have m5 : W.rx * (fr "__loop3" + Bd.xmss) = (fr "__loop3" + Bd.xmss) * W.rx := Nat.mul_comm _ _
  have m6 : W.rs * (fr "__loop4" + Bd.sphincs) = (fr "__loop4" + Bd.sphincs) * W.rs := Nat.mul_comm _ _
  have hbs8 : (mainBs8 fr Bd W).sum = (W.da + W.ud) * fr "__loop0" + fr "__loop0" +
      Bd.daList W.da + Bd.cl W.dx + Bd.cl W.ds +
      (W.ux * fr "__loop1" + fr "__loop1") + (W.us * fr "__loop2" + fr "__loop2") +
      (W.rx * (fr "__loop3" + Bd.xmss) + fr "__loop3") +
      (W.rs * (fr "__loop4" + Bd.sphincs) + fr "__loop4") := by
    simp only [mainBs8, List.sum_cons, List.sum_nil]; ring
  have hda : (if W.rd = 1 then Bd.daVerify W.drows + Bd.cover else 0) ≤
      (A.dvA + Bd.cover) * W.rd + A.dvB * W.drows := by
    split_ifs with h
    · rw [h, Nat.mul_one]; have := hA.dv W.drows; omega
    · exact Nat.zero_le _
  have hch : loopSum (fr "__loop5") (fun c => childBd fr Bd (W.child c)) 0 W.nc ≤
      W.nc * (fr "__loop5" + eaChK fr Bd A) + fr "__loop5" + eaChA fr Bd A * (w.children.map cnw).sum := by
    refine ea_loopSum (fr "__loop5") (eaChK fr Bd A) (eaChA fr Bd A) _ w.children 0 fun i hi => ?_
    have hc : W.child (0 + i) = childWordsOf seed w.children[i] (hbase s w i) := by
      simp only [hW, honestWords, Nat.zero_add, hi, ↓reduceDIte]
    show childBd fr Bd (W.child (0 + i)) ≤ _
    rw [hc]
    exact ea_childBd fr hA _ (hlim.daRoots.2 _ (List.getElem_mem _))
  have hagg : (if W.nc = 0 then 0 else aggBound fr W.nc) ≤ eaAggA fr * W.nc + eaAggB fr := by
    split_ifs
    · exact Nat.zero_le _
    · rw [ea_agg]
  have hn5 : W.nc * (fr "__loop5" + eaChK fr Bd A) = fr "__loop5" * W.nc + eaChK fr Bd A * W.nc := by ring
  have hn6 : (162 + fr "__loop5" + eaChK fr Bd A + eaAggA fr) * W.nc =
      162 * W.nc + fr "__loop5" * W.nc + eaChK fr Bd A * W.nc + eaAggA fr * W.nc := by ring
  simp only [mainBound, mainKidsBound, hsz, hbs8, eaLin, hcov, hdecl, hrx, hrs, hrd, hrr, hnc, hcc]
  omega

/-! ## At the words -/

variable (fs : String → ℕ) {cert : String → V → ℕ} {bc : List K} (H : CalleesHyps fs cert bc)

/-- The claim tails' largest bound, the child claim tails' largest frame, the DA lists' largest. -/
def eaCtMax : ℕ := eaMax ((List.range 32).map H.Bct)
def eaCctMax : ℕ := eaMax (Digest.cctNames.map fs)
def eaDlMax : ℕ := eaMax ((List.range 17).map fun n => H.Bdl (gen ^ n))

/-- `c` per block of 32 is at most `⌈c / 32⌉` per item. -/
theorem ea_div32 (c n : ℕ) : c * ((n - 1) / 32) ≤ (c + 31) / 32 * n := by
  have h1 : 32 * ((n - 1) / 32) ≤ n := by omega
  have h2 : c ≤ (c + 31) / 32 * 32 := by omega
  calc c * ((n - 1) / 32) ≤ (c + 31) / 32 * 32 * ((n - 1) / 32) := Nat.mul_le_mul_right _ h2
    _ = (c + 31) / 32 * (32 * ((n - 1) / 32)) := by ring
    _ ≤ (c + 31) / 32 * n := Nat.mul_le_mul_left _ h1

/-- A claim list's bound, affinely: slope (a block of 32 claims per `__loop86` iteration) and
constant. -/
def eaClA (a86 : ℕ) : ℕ := (4 + a86 + 31) / 32
def eaClB (b86 : ℕ) : ℕ := fs "claim_list_digest" + 4 + b86 + fs "__loop86" + eaCtMax fs H + H.Bsl6
/-- A child claim list's. -/
def eaCclA : ℕ := (4 + fs "__loop87" + (fs "child_claims_window" + H.Bsl) + 31) / 32
def eaCclB : ℕ := fs "child_claim_list_digest" + 4 + fs "__loop87" + eaCctMax fs + H.Bsl6

theorem ea_cl {a86 b86 : ℕ} (h86 : ∀ q, H.B86 (gen ^ q) ≤ a86 * q + b86) (n : ℕ) :
    (calleeBd fs H).cl n ≤ eaClA a86 * n + eaClB fs H b86 := by
  simp only [calleeBd, Digest.cldBound, eaClB]
  have h1 := h86 ((n - 1) / 32)
  have h2 : (4 + a86) * ((n - 1) / 32) ≤ eaClA a86 * n := ea_div32 _ _
  have h3 : H.Bct ((n - 1) % 32) ≤ eaCtMax fs H :=
    ea_le_max (List.mem_map.mpr ⟨_, List.mem_range.mpr (Nat.mod_lt (n - 1) (show 0 < 32 by norm_num)), rfl⟩)
  have h4 : max (H.B86 (gen ^ ((n - 1) / 32))) (fs "__loop86") ≤ a86 * ((n - 1) / 32) + b86 + fs "__loop86" :=
    max_le (by omega) (by omega)
  have h5 : (4 + a86) * ((n - 1) / 32) = 4 * ((n - 1) / 32) + a86 * ((n - 1) / 32) := by ring
  omega

theorem ea_ccl (n : ℕ) : (calleeBd fs H).ccl n ≤ eaCclA fs H * n + eaCclB fs H := by
  simp only [calleeBd, Digest.ccldBound, Digest.l87Bound, eaCclB, Nat.sub_zero]
  have h2 : (4 + fs "__loop87" + (fs "child_claims_window" + H.Bsl)) * ((n - 1) / 32) ≤ eaCclA fs H * n :=
    ea_div32 _ _
  have h3 : fs (Digest.cctNames.getD ((n - 1) % 32) "") ≤ eaCctMax fs := by
    refine ea_le_max (List.mem_map.mpr ⟨_, ?_, rfl⟩)
    rw [List.getD_eq_getElem _ _ (by
      have : Digest.cctNames.length = 32 := by decide
      rw [this]; exact Nat.mod_lt _ (by norm_num))]
    exact List.getElem_mem _
  have h5 : (4 + fs "__loop87" + (fs "child_claims_window" + H.Bsl)) * ((n - 1) / 32) =
      4 * ((n - 1) / 32) + (n - 1) / 32 * (fs "__loop87" + (fs "child_claims_window" + H.Bsl)) := by ring
  omega

theorem ea_dl {n : ℕ} (hn : n ≤ 16) : (calleeBd fs H).daList n ≤ eaDlMax fs H :=
  ea_le_max (List.mem_map.mpr ⟨n, List.mem_range.mpr (show n < 17 by omega), rfl⟩)

/-- The words' affine constants. -/
def eaWordsC (a86 b86 : ℕ) : EaAffC :=
  ⟨eaClA a86, eaClB fs H b86, eaCclA fs H, eaCclB fs H, eaDlMax fs H, Digest.dvWA fs, Digest.dvWB fs⟩

theorem ea_wordsOk {a86 b86 : ℕ} (h86 : ∀ q, H.B86 (gen ^ q) ≤ a86 * q + b86) :
    EaAffOk (calleeBd fs H) (eaWordsC fs H a86 b86) :=
  ⟨ea_cl fs H h86, ea_ccl fs H, fun _ hn => ea_dl fs H hn, fun r => Digest.dv_tot_affine fs r,
    fun θ r => Digest.dv_tot_affine θ r⟩

/-- **The words budget.** -/
def eaWords (a86 b86 : ℕ) : Linear := eaLin fs (calleeBd fs H) (eaWordsC fs H a86 b86)

/-- **`main`'s bound at the honest words is within the words budget**, for a node within the
limits, once `__loop86`'s bound is affine. -/
theorem ea_words {a86 b86 : ℕ} (h86 : ∀ q, H.B86 (gen ^ q) ≤ a86 * q + b86) {seed : Digest}
    {s : NodeStatement} {w : NodeWitness} (hlim : Limits s w) :
    mainBound fs (calleeBd fs H) (honestWords seed s w) ≤ (eaWords fs H a86 b86).eval (work s w) :=
  ea_bound fs (ea_wordsOk fs H h86) hlim

end
end LeanVM.Guest.B1.Main
