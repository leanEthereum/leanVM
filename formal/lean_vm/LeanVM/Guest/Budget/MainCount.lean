/-
  LeanVM.Guest.Budget.MainCount

  `main`'s weight at one opcode's instruction counts on the tree of its bounded completeness: its
  frame's, its statically bounded callees' constants, and its other callees' by their trees' shapes.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Budget.Main
public import LeanVM.Guest.Budget.Static
public import LeanVM.Guest.B1.Main.MainHonestB
public import LeanVM.Guest.B1.Main.MainGoalsClT
public import LeanVM.Guest.B1.Da.DvAt

/-!
# `main`'s instruction counts

`MainCounts ω fs`: per callee of `main`, a bound on every valid tree's weight at `ω` (an opcode's
instructions per frame, `B2C.ωArm`):
* `exponent_tables`, `statement_digest`: constants (`WeightLe`);
* the loops `__loop0` .. `__loop3`: per iteration (`LoopW`), run from `1` to `g^n` at `main`'s
  counts;
* `aggregate_claims`: affine in its children's count;
* `claim_list_digest`: affine in its claims' count on a tree of its honest shape (`clHonest n`);
* `da_verify`: affine in its rows and its padded rows `2^L` on a tree of its honest shape
  (`Da.dvNH r L`);
* the claim lists, `da_verify` and `__loop4`, the children's loop, in `main`: bounds `Kx`, `Ks`,
  `Kd`, `K5` on every valid tree of their predicates (`Final` gives the first three from the
  above, `L5Count` the last per child, at the child's announced shape).
`main_weight_count`: on `main`'s node with `main`'s calls, honest values and callee predicates,
the weight is at most `mainCount`.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (MainIn MVals MainBounds mCalls mTs mEvs MainPreds MainBs mOrc)

@[expose] public section

/-- **The weights of `main`'s callees at `ω`.** -/
structure MainCounts (ω fs : String → ℕ) : Type where
  kExp : ℕ
  exp : WeightLe coreProgram ω "exponent_tables" fun _ => kExp
  kSd : ℕ
  sd : WeightLe coreProgram ω "statement_digest" fun _ => kSd
  kL1 : ℕ
  l1 : LoopW ω (name% main_loop0) kL1
  kL2 : ℕ
  l2 : LoopW ω (name% main_loop1) kL2
  kL3 : ℕ
  l3 : LoopW ω (name% main_loop2) kL3
  kL4 : ℕ
  l4 : LoopW ω (name% main_loop3) kL4
  aggC : ℕ
  aggD : ℕ
  agg : ∀ (rd : Reader) (t : Tree) (args rets : List E) (n : ℕ), t.name = "aggregate_claims" →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram → args.getD 0 0 = ofK
        (addressOfIndex n) →
    0 < n → n < 2 ^ 64 - 1 → t.weight ω ≤ aggC + aggD * n
  clA : ℕ
  clS : ℕ
  cl : ∀ (rd : Reader) (t : Tree) (args rets : List E) (n : ℕ), t.name = "claim_list_digest" →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram → B1.Main.clHonest n t →
    n / 17 < 2 ^ 64 - 1 → t.weight ω ≤ clA + clS * n
  dvA : ℕ
  dvR : ℕ
  dvP : ℕ
  dv : ∀ (rd : Reader) (t : Tree) (args rets : List E) (r L : ℕ), t.name = "da_verify" →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram → B1.Da.dvNH r L t → 1 ≤ r →
    r ≤ LeanDa.maxRows → 2 ^ L = LeanDa.paddedRowCount r → t.weight ω ≤ dvA + dvR * r + dvP * 2 ^ L

variable {ω fs : String → ℕ}

/-- **`main`'s weight bound** at the counts `m`, the claim lists' weights `Kx`, `Ks`,
`da_verify`'s `Kd` and the children's loop's `K5`. -/
def mainCount (H : MainCounts ω fs) (m : MainIn) (Kx Ks Kd K5 : ℕ) : ℕ :=
  ω "main" + (H.kExp + Kx + Ks + m.nxd * H.kL1 +
    m.nsd * H.kL2 + m.nrx * H.kL3 + m.nrs * H.kL4 + (if m.nd = 1 then Kd else 0) +
    (if m.nc = 0 then 0 else K5 + (H.aggC + H.aggD * m.nc)) + H.kSd)

/-- A call's bound, by its callee. -/
def mainCallW (H : MainCounts ω fs) (m : MainIn) (Kx Ks Kd K5 : ℕ) (c : Call) : ℕ :=
  if c.f = "exponent_tables" then H.kExp
  else if c.f = "claim_list_digest" then (if c.args = [.n 31, .n 0] then Kx else Ks)
  else if c.f = (name% main_loop0) then m.nxd * H.kL1
  else if c.f = (name% main_loop1) then m.nsd * H.kL2
  else if c.f = (name% main_loop2) then m.nrx * H.kL3
  else if c.f = (name% main_loop3) then m.nrs * H.kL4
  else if c.f = "da_verify" then Kd
  else if c.f = (name% main_loop4) then (if m.nc = 0 then 0 else K5)
  else if c.f = "aggregate_claims" then H.aggC + H.aggD * m.nc
  else if c.f = "statement_digest" then H.kSd
  else 0

theorem callsW_le_sum (W : Call → ℕ) : ∀ cs : List Call, callsW W cs ≤ (cs.map W).sum
  | [] => le_rfl
  | c :: cs => by
    have := callsW_le_sum W cs
    unfold callsW at this ⊢
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    split <;> omega

/-- `main`'s calls' bounds sum to `mainCount` past its frame. -/
theorem mainCalls_sum (H : MainCounts ω fs) (σ : Val) (m : MainIn) (Kx Ks Kd K5 : ℕ) :
    ω "main" + ((mCalls σ m).map (mainCallW H m Kx Ks Kd K5)).sum ≤ mainCount H m Kx Ks Kd K5 := by
  unfold mCalls mainCount
  by_cases hd : m.nd = 1 <;> by_cases hc : m.nc = 0 <;>
    simp [hd, hc, mainCallW] <;> omega

/-! ## The callees, by kind -/

variable {rd : Reader} {σ : Val} {m : MainIn}

theorem orc_cnt (hMV : MVals rd σ m) (j : ℕ) (hj : j < 8) :
    σ (.n j) = gen ^ m.cnt.getD j 0 := by
  rw [hMV.orc j (by simp; omega)]
  simp [mOrc, hj]

/-- A loop of `main` from `1` to `g^n`, entered. -/
theorem loop_case {f : String} {K : ℕ} (hL : LoopW ω f K) {args : List V} {t : Tree} {rets : List E}
    {n : ℕ} (hn : t.name = f) (hv : t.Valid coreProgram rd (args.map σ) rets)
    (hb : t.BufsOk coreProgram) (h0 : σ (args.getD 0 (.n 0)) = 1)
    (h1 : σ (args.getD 1 (.n 0)) = gen ^ n) (hn0 : n ≠ 0) (hn64 : n < 2 ^ 64 - 1)
    (hlen : 2 ≤ args.length) : t.weight ω ≤ n * K := by
  refine hL.at hn hv hb ?_ ?_ hn0 hn64
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at h0
    simpa using h0
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at h1
    simpa using h1

set_option maxRecDepth 10000 in
/-- **`main`'s weight at `ω`** on its tree: its frame's and `mainCount`'s callees' bounds, the
claim lists within `Kx`, `Ks`, `da_verify` within `Kd` (a direct blob held) and the children's
loop within `K5` on their predicates' trees. -/
theorem main_weight_count (H : MainCounts ω fs) {bufs : List ℕ} {ks : List Tree} {p : MainPreds}
    {b : MainBs} (Kx Ks Kd K5 : ℕ)
    (hclx : ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = "claim_list_digest" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram → p.Px t → t.weight ω ≤ Kx)
    (hcls : ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = "claim_list_digest" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram → p.Ps t → t.weight ω ≤ Ks)
    (hdv : m.nd = 1 → ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = "da_verify" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram → p.Pd t → t.weight ω ≤ Kd)
    (h5 : ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = (name% main_loop4) →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram → p.T5 t → t.weight ω ≤ K5)
    (hv : (Memory.Tree.node "main" σ bufs ks).Valid coreProgram rd [] [])
    (hb : (Memory.Tree.node "main" σ bufs ks).BufsOk coreProgram)
    (hc : calls (mEvs σ) = mCalls σ m) (hMV : MVals rd σ m) (hB : MainBounds (2 ^ 23) m)
    (hT : KidsT (mCalls σ m) ((fun _ => True) :: mTs m (p.withTotal fs b)) ks) :
    (Memory.Tree.node "main" σ bufs ks).weight ω ≤ mainCount H m Kx Ks Kd K5 := by
  have hl : (mCalls σ m).length ≤ ((fun _ => True) :: mTs m (p.withTotal fs b)).length := by
    unfold mCalls mTs
    by_cases hd : m.nd = 1 <;> by_cases hc0 : m.nc = 0 <;> simp [hd, hc0]
  have h := main_weight_le ω (mainCallW H m Kx Ks Kd K5) _ hv hb hc hl hT ?_
  · exact le_trans h (le_trans (Nat.add_le_add_left (callsW_le_sum _ _) _)
      (mainCalls_sum H σ m Kx Ks Kd K5))
  intro c T hmem ht t rets hn hv' hb' hT'
  have hx := orc_cnt hMV
  unfold mCalls mTs at hmem
  by_cases hd : m.nd = 1 <;> by_cases hc0 : m.nc = 0 <;>
    simp only [hd, hc0, ↓reduceIte, List.cons_append, List.nil_append, List.zip_cons_cons,
      List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
      MainPreds.withTotal] at hmem <;>
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [mainCallW, ↓reduceIte, String.reduceEq, hc0] at hn ⊢ <;>
    first
    | exact H.exp rd t _ rets hn hv' hb'
    | exact H.sd rd t _ rets hn hv' hb'
    | exact hclx rd t _ rets hn hv' hb' hT'.1
    | exact hcls rd t _ rets hn hv' hb' hT'.1
    | exact hdv hd rd t _ rets hn hv' hb' hT'.1
    | exact h5 rd t _ rets hn hv' hb' hT'.1
    | exact absurd hc0 (ne_zero_of_guard (by simpa [hMV.g434] using ht))
    | exact loop_case (n := m.nxd) H.l1 hn hv' hb' (by simpa using hMV.g62)
        (by simpa [MainIn.cnt] using hx 1 (by norm_num))
        (ne_zero_of_guard (by simpa [hMV.g61] using ht)) (by have := hB.xd; omega) (by simp)
    | exact loop_case (n := m.nsd) H.l2 hn hv' hb' (by simpa using hMV.g65)
        (by simpa [MainIn.cnt] using hx 4 (by norm_num))
        (ne_zero_of_guard (by simpa [hMV.g64] using ht)) (by have := hB.sd; omega) (by simp)
    | exact loop_case (n := m.nrx) H.l3 hn hv' hb' (by simpa using hMV.g378)
        (by simpa [MainIn.cnt] using hx 2 (by norm_num))
        (ne_zero_of_guard (by simpa [hMV.g377] using ht)) (by have := hB.rx; omega) (by simp)
    | exact loop_case (n := m.nrs) H.l4 hn hv' hb' (by simpa using hMV.g381)
        (by simpa [MainIn.cnt] using hx 5 (by norm_num))
        (ne_zero_of_guard (by simpa [hMV.g380] using ht)) (by have := hB.rs; omega) (by simp)
    | exact H.agg rd t _ rets m.nc hn hv' hb'
        (by simpa [MainIn.cnt, Value.gen_pow_eq_ofK] using hx 6 (by norm_num))
        (Nat.pos_of_ne_zero hc0) (by have := hB.nc; omega)

end
end LeanVM.Guest.Budget
