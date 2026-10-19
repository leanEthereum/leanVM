/-
  LeanVM.Guest.EndCompleteWords

  The words budget: a `Linear` in the node's work dominating `main`'s bound `mainBound` at the
  honest words, for the callees' bounds `calleeBd`.
-/

module

public import LeanVM.Guest.B1.Main.MainBudget
public import LeanVM.Guest.B1.Main.CalleesProved
public import LeanVM.Guest.B1.Main.HonestWords

/-!
# `main`'s words within a linear budget

`eaWords fs H a86 b86`: a constant, plus per unit of work the words its callees and buffers take
per declared claim, coverage slot, raw signature or matrix, child and child's claim.
`ea_words`: at the honest words of a node within the limits, `mainBound fs (calleeBd fs H)` is
at most it. The claim lists' bound is affine once `__loop86`'s is (`a86`, `b86`); the child lists'
and the batching's are affine as they stand; the DA lists' is a constant (at most `16` roots).
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

variable (fs : String → ℕ) {cert : String → V → ℕ} {bc : List K} (H : CalleesHyps fs cert bc)

/-- The claim tails' largest bound, the child claim tails' largest frame, the DA lists' largest. -/
def eaCtMax : ℕ := eaMax ((List.range 32).map H.Bct)
def eaCctMax : ℕ := eaMax (Digest.cctNames.map fs)
def eaDlMax : ℕ := eaMax ((List.range 17).map fun n => H.Bdl (gen ^ n))

/-- A claim list's bound, affinely: slope and constant. -/
def eaClA (a86 : ℕ) : ℕ := 4 + a86
def eaClB (b86 : ℕ) : ℕ := fs "claim_list_digest" + 4 + b86 + fs "__loop86" + eaCtMax fs H + H.Bsl6
/-- A child claim list's. -/
def eaCclA : ℕ := 4 + fs "__loop87" + (fs "child_claims_window" + H.Bsl)
def eaCclB : ℕ := fs "child_claim_list_digest" + 4 + fs "__loop87" + eaCctMax fs + H.Bsl6
/-- The batching's. -/
def eaAggA : ℕ := 18 + fs "__loop95" + fs "__loop96" + fs "__loop97" + fs "__loop98" + fs "__loop99"
def eaAggB : ℕ := fs "aggregate_claims" + 413 + fs "__loop95" + fs "__loop96" + fs "__loop97" +
  fs "__loop98" + fs "__loop99" + fs "batch_sumcheck__L22" + fs "batch_sumcheck__L28"

theorem ea_agg (n : ℕ) : aggBound fs n = eaAggA fs * n + eaAggB fs := by
  simp only [aggBound, aggSizes, eaAggA, eaAggB, List.sum_cons, List.sum_nil]; ring

theorem ea_cl {a86 b86 : ℕ} (h86 : ∀ q, H.B86 (gen ^ q) ≤ a86 * q + b86) (n : ℕ) :
    (calleeBd fs H).cl n ≤ eaClA a86 * n + eaClB fs H b86 := by
  simp only [calleeBd, Digest.cldBound, eaClA, eaClB]
  have hq : (n - 1) / 32 ≤ n := le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
  have h1 := h86 ((n - 1) / 32)
  have h2 : a86 * ((n - 1) / 32) ≤ a86 * n := Nat.mul_le_mul_left _ hq
  have h3 : H.Bct ((n - 1) % 32) ≤ eaCtMax fs H :=
    ea_le_max (List.mem_map.mpr ⟨_, List.mem_range.mpr (Nat.mod_lt (n - 1) (show 0 < 32 by norm_num)), rfl⟩)
  have h4 : max (H.B86 (gen ^ ((n - 1) / 32))) (fs "__loop86") ≤ a86 * n + b86 + fs "__loop86" :=
    max_le (by omega) (by omega)
  have h5 : (4 + a86) * n = 4 * n + a86 * n := by ring
  omega

theorem ea_ccl (n : ℕ) : (calleeBd fs H).ccl n ≤ eaCclA fs H * n + eaCclB fs H := by
  simp only [calleeBd, Digest.ccldBound, Digest.l87Bound, eaCclA, eaCclB, Nat.sub_zero]
  have hq : (n - 1) / 32 ≤ n := le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
  have h2 : (n - 1) / 32 * (fs "__loop87" + (fs "child_claims_window" + H.Bsl)) ≤
      n * (fs "__loop87" + (fs "child_claims_window" + H.Bsl)) := Nat.mul_le_mul_right _ hq
  have h3 : fs (Digest.cctNames.getD ((n - 1) % 32) "") ≤ eaCctMax fs := by
    refine ea_le_max (List.mem_map.mpr ⟨_, ?_, rfl⟩)
    rw [List.getD_eq_getElem _ _ (by
      have : Digest.cctNames.length = 32 := by decide
      rw [this]; exact Nat.mod_lt _ (by norm_num))]
    exact List.getElem_mem _
  have h5 : (4 + fs "__loop87" + (fs "child_claims_window" + H.Bsl)) * n =
      4 * n + n * (fs "__loop87" + (fs "child_claims_window" + H.Bsl)) := by ring
  omega

theorem ea_dl {n : ℕ} (hn : n ≤ 16) : (calleeBd fs H).daList n ≤ eaDlMax fs H :=
  ea_le_max (List.mem_map.mpr ⟨n, List.mem_range.mpr (show n < 17 by omega), rfl⟩)

/-- A child's bound, affinely in its claims: constant and slope. -/
def eaChK : ℕ := 2 + 2 * eaCclB fs H + fs "__loop100" + eaDlMax fs H + H.Bsd + (calleeBd fs H).vs
def eaChA : ℕ := 4 + eaCclA fs H + fs "__loop100" + fs "cover_da_root"

theorem ea_childBd (r : ChildWords) (hda : r.da.length ≤ 16) :
    childBd fs (calleeBd fs H) r ≤ eaChK fs H + eaChA fs H * (r.nx + r.ns + r.da.length) := by
  have c1 := ea_ccl fs H r.nx
  have c2 := ea_ccl fs H r.ns
  have d := ea_dl fs H hda
  have e1 : eaCclA fs H * r.nx ≤ eaChA fs H * r.nx := Nat.mul_le_mul_right _ (by unfold eaChA; omega)
  have e2 : eaCclA fs H * r.ns ≤ eaChA fs H * r.ns := Nat.mul_le_mul_right _ (by unfold eaChA; omega)
  have e3 : r.da.length * (fs "__loop100" + fs "cover_da_root") + 4 * r.da.length ≤
      eaChA fs H * r.da.length := by
    have : (fs "__loop100" + fs "cover_da_root") + 4 ≤ eaChA fs H := by unfold eaChA; omega
    nlinarith
  have e4 : eaChA fs H * (r.nx + r.ns + r.da.length) =
      eaChA fs H * r.nx + eaChA fs H * r.ns + eaChA fs H * r.da.length := by ring
  simp only [childBd, eaChK]
  have hcov : (calleeBd fs H).cover = fs "cover_da_root" := rfl
  have hsd : (calleeBd fs H).sd = H.Bsd := rfl
  rw [hcov, hsd]
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

/-- **The words budget.** -/
def eaWords (a86 b86 : ℕ) : Linear where
  base := fs "main" + 56 + fs "exponent_tables" + 68 + fs "__loop0" + eaDlMax fs H + 2 * eaClB fs H b86 +
    fs "__loop1" + fs "__loop2" + fs "__loop3" + fs "__loop4" + fs "__loop5" + eaAggB fs + H.Bsd
  declared := eaClA a86
  coverage := 5 + fs "__loop0" + fs "__loop1" + fs "__loop2"
  rawXmss := fs "__loop3" + H.Bx
  rawSphincs := fs "__loop4" + H.Bsp
  rawDa := dvMax fs + fs "cover_da_root"
  children := 162 + fs "__loop5" + eaChK fs H + eaAggA fs
  childClaims := eaChA fs H

theorem ea_eval (a86 b86 : ℕ) (u : LeanVM.Guest.End.Work) : (eaWords fs H a86 b86).eval u =
    (eaWords fs H a86 b86).base + eaClA a86 * u.declared +
      (5 + fs "__loop0" + fs "__loop1" + fs "__loop2") * u.coverage + (fs "__loop3" + H.Bx) * u.rawXmss +
      (fs "__loop4" + H.Bsp) * u.rawSphincs + (dvMax fs + fs "cover_da_root") * u.rawDa +
      (162 + fs "__loop5" + eaChK fs H + eaAggA fs) * u.children + eaChA fs H * u.childClaims := rfl

set_option maxHeartbeats 1000000 in
/-- **`main`'s bound at the honest words is within the words budget**, for a node within the
limits, once `__loop86`'s bound is affine. -/
theorem ea_words {a86 b86 : ℕ} (h86 : ∀ q, H.B86 (gen ^ q) ≤ a86 * q + b86) {seed : Digest}
    {s : NodeStatement} {w : NodeWitness} (hlim : Limits s w) :
    mainBound fs (calleeBd fs H) (honestWords seed s w) ≤ (eaWords fs H a86 b86).eval (work s w) := by
  rw [ea_eval]
  set W := honestWords seed s w with hW
  have hcov : (work s w).coverage = W.total := by
    show coverage s w = _
    rw [coverage_eq]; rfl
  have hdecl : (work s w).declared = W.dx + W.ds + W.da := rfl
  have hrx : (work s w).rawXmss = W.rx := rfl
  have hrs : (work s w).rawSphincs = W.rs := rfl
  have hrd : (work s w).rawDa = W.rd := rfl
  have hnc : (work s w).children = W.nc := rfl
  have hcc : (work s w).childClaims = (w.children.map cnw).sum := rfl
  have hrd1 : W.rd ≤ 1 := hlim.directDa
  have hda16 : W.da ≤ 16 := hlim.daRoots.1
  have htot : W.total = W.dx + W.ux + (W.ds + W.us) + (W.da + W.ud) := rfl
  -- the buffers
  have hsz : W.sizes.sum = 5 * W.total + 162 * W.nc + 56 := by
    simp only [MainWords.sizes, List.sum_cons, List.sum_nil, htot]; ring
  -- the eight calls
  have c1 := ea_cl fs H h86 W.dx
  have c2 := ea_cl fs H h86 W.ds
  have d1 := ea_dl fs H hda16
  have m0 : (W.da + W.ud) * fs "__loop0" ≤ fs "__loop0" * W.total := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have m1 : W.ux * fs "__loop1" ≤ fs "__loop1" * W.total := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have m2 : W.us * fs "__loop2" ≤ fs "__loop2" * W.total := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have m3 : (5 + fs "__loop0" + fs "__loop1" + fs "__loop2") * W.total =
      5 * W.total + fs "__loop0" * W.total + fs "__loop1" * W.total + fs "__loop2" * W.total := by ring
  have m4 : eaClA a86 * (W.dx + W.ds + W.da) ≥ eaClA a86 * W.dx + eaClA a86 * W.ds := by
    rw [Nat.mul_add, Nat.mul_add]; omega
  have m5 : W.rx * (fs "__loop3" + (calleeBd fs H).xmss) = (fs "__loop3" + H.Bx) * W.rx := Nat.mul_comm _ _
  have m6 : W.rs * (fs "__loop4" + (calleeBd fs H).sphincs) = (fs "__loop4" + H.Bsp) * W.rs := Nat.mul_comm _ _
  have hbs8 : (mainBs8 fs (calleeBd fs H) W).sum = (W.da + W.ud) * fs "__loop0" + fs "__loop0" +
      (calleeBd fs H).daList W.da + (calleeBd fs H).cl W.dx + (calleeBd fs H).cl W.ds +
      (W.ux * fs "__loop1" + fs "__loop1") + (W.us * fs "__loop2" + fs "__loop2") +
      (W.rx * (fs "__loop3" + (calleeBd fs H).xmss) + fs "__loop3") +
      (W.rs * (fs "__loop4" + (calleeBd fs H).sphincs) + fs "__loop4") := by
    simp only [mainBs8, List.sum_cons, List.sum_nil]; ring
  -- the direct DA claim
  have hda : (if W.rd = 1 then (calleeBd fs H).daVerify + (calleeBd fs H).cover else 0) ≤
      (dvMax fs + fs "cover_da_root") * W.rd := by
    have hdv : (calleeBd fs H).daVerify = dvMax fs := by simp only [calleeBd]
    have hcv : (calleeBd fs H).cover = fs "cover_da_root" := rfl
    rw [hdv, hcv]
    split_ifs with h
    · rw [h, Nat.mul_one]
    · exact Nat.zero_le _
  -- the children
  have hch : loopSum (fs "__loop5") (fun c => childBd fs (calleeBd fs H) (W.child c)) 0 W.nc ≤
      W.nc * (fs "__loop5" + eaChK fs H) + fs "__loop5" + eaChA fs H * (w.children.map cnw).sum := by
    refine ea_loopSum (fs "__loop5") (eaChK fs H) (eaChA fs H) _ w.children 0 fun i hi => ?_
    have hc : W.child (0 + i) = childWordsOf seed w.children[i] (hbase s w i) := by
      simp only [hW, honestWords, Nat.zero_add, hi, ↓reduceDIte]
    show childBd fs (calleeBd fs H) (W.child (0 + i)) ≤ _
    rw [hc]
    exact ea_childBd fs H _ (hlim.daRoots.2 _ (List.getElem_mem _))
  have hagg : (if W.nc = 0 then 0 else aggBound fs W.nc) ≤ eaAggA fs * W.nc + eaAggB fs := by
    split_ifs
    · exact Nat.zero_le _
    · rw [ea_agg]
  have hn5 : W.nc * (fs "__loop5" + eaChK fs H) = fs "__loop5" * W.nc + eaChK fs H * W.nc := by ring
  have hn6 : (162 + fs "__loop5" + eaChK fs H + eaAggA fs) * W.nc =
      162 * W.nc + fs "__loop5" * W.nc + eaChK fs H * W.nc + eaAggA fs * W.nc := by ring
  have hsd : (calleeBd fs H).sd = H.Bsd := rfl
  simp only [mainBound, mainKidsBound, hsz, hbs8, eaWords, hcov, hdecl, hrx, hrs, hrd, hnc, hcc, hsd]
  omega

end
end LeanVM.Guest.B1.Main
