/-
  LeanVM.Guest.B1.Lag64

  B1 for the inline `lag64`: the 64 Lagrange numerators at `z` over a window of the skip nodes.
-/

module

public import LeanVM.Guest.B1.QueryBits

/-!
# `lag64` (TRIAGE #21)

`lag64(z, out, node_base)` (G:780-797) is inline: a prefix chain `pre[i] = Π_{j<i} (z + n_j)`,
a suffix chain `suf[i] = Π_{i≤j<64} (z + n_j)`, and `out[i] = pre[i]·suf[i+1]`, the nodes
`n_j = PHI8_NODES[node_base + j]`, `φ_8(node_base + j)` (`phi`, V:741). Its expansion is `lag64T`,
the compiler folding the zero node `φ_8(0)`; `holds_lag64T` reads it, `lag64_values` gives each
numerator as the product over the other nodes, `lag64_of_agree` is its completeness, and
`core12_lag64_hi`, `core12_lag64_lo`, `core572_lag64` place it in `verify_flock` and `__loop99`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The nodes -/

/-- `PHI8_NODES` as the data writes it (`aggregation.rs:2517`). -/
def phi8Words : List ℕ :=
  [0, 1, 233317187178767958, 233317187178767959, 5847396588373319944, 5847396588373319945,
    5916261553440163678, 5916261553440163679, 909273441170553857, 909273441170553856,
    1126616643693337175, 1126616643693337174, 6753221685647269129, 6753221685647269128,
    6810757554037128031, 6810757554037128030, 13425015913296524956, 13425015913296524957,
    13363258058013790410, 13363258058013790411, 16963121286284040084, 16963121286284040085,
    16741555821419917762, 16741555821419917763, 13173415632012282525, 13173415632012282524,
    13109335328444067019, 13109335328444067018, 16714968798032636821, 16714968798032636820,
    16486437098630516163, 16486437098630516162, 13413663147086793287, 13413663147086793286,
    13337989939188722705, 13337989939188722704, 16933754119322725199, 16933754119322725198,
    16734302103207496985, 16734302103207496984, 13166419680609547846, 13166419680609547847,
    13079698300183580688, 13079698300183580689, 16689958445912364878, 16689958445912364879,
    16474814470949679384, 16474814470949679385, 29795976497216731, 29795976497216730,
    240155289994828429, 240155289994828428, 5859178164118920659, 5859178164118920658,
    5941114056868903813, 5941114056868903812, 934417933708345562, 934417933708345563,
    1138091936817112716, 1138091936817112717, 6760351777467556306, 6760351777467556307,
    6840247247740520324, 6840247247740520325, 5077413140227349505, 5077413140227349504,
    4992927275758287447, 4992927275758287446, 1680045447218232585, 1680045447218232584,
    1471640032698489695, 1471640032698489694, 5397840376063860736, 5397840376063860737,
    5319898533665736278, 5319898533665736279, 2003779738599850248, 2003779738599850249,
    1797556034875041630, 1797556034875041631, 18174738647891815069, 18174738647891815068,
    18376177690117868747, 18376177690117868746, 12474835414352726933, 12474835414352726932,
    12547991768974339523, 12547991768974339522, 17341048660226299548, 17341048660226299549,
    17553676061639045322, 17553676061639045323, 11637837820279650196, 11637837820279650197,
    11726545947089916354, 11726545947089916355, 18181172200248022598, 18181172200248022599,
    18405252315020079120, 18405252315020079121, 12499283362976839502, 12499283362976839503,
    12559051997470757144, 12559051997470757145, 17351837927878388295, 17351837927878388294,
    17578380677594729489, 17578380677594729488, 11666641484232641359, 11666641484232641358,
    11733236166605761817, 11733236166605761816, 5052831051185709274, 5052831051185709275,
    4982014381818922636, 4982014381818922637, 1673477754444464594, 1673477754444464595,
    1442712742353364868, 1442712742353364869, 5368607902574976219, 5368607902574976218,
    5313623929546259085, 5313623929546259084, 1992561661411900883, 1992561661411900882,
    1773267034315692933, 1773267034315692932]

theorem ofBits_phi8Words : ∀ j < 128, K.ofBits (phi8Words.getD j 0) = Flock.phi8 j := by decide +kernel

theorem word_phi8Words {j : ℕ} (hj : j < 128) : word (phi8Words.getD j 0) 0 0 = phi j := by
  rw [word_eOfNat, eOfNat, phi, ofBits_phi8Words j hj]

/-! ## The template -/

/-- One factor `z + node` of a product chain from `prev`, from value `c` (a zero node folded). -/
def lgStep (z : V) (node : ℕ) (prev : V) (c : ℕ) : List Stmt × ℕ :=
  if node = 0 then ([.atom (.mul (.n c) prev z)], c + 1) else
    ([.atom (.const (.n c) (word node 0 0)), .atom (.add (.n (c + 1)) z (.n c)),
      .atom (.mul (.n (c + 2)) prev (.n (c + 1)))], c + 3)

/-- The chain over the nodes `node i ..`, `n` of them, from `prev`: the statements, the cells of
the products, the next value. -/
def lgRun (z : V) (node : ℕ → ℕ) : ℕ → ℕ → V → ℕ → List Stmt × List V × ℕ
  | _, 0, _, c => ([], [], c)
  | i, n + 1, prev, c =>
    let s := lgStep z (node i) prev c
    let r := lgRun z node (i + 1) n (.n (s.2 - 1)) s.2
    (s.1 ++ r.1, .n (s.2 - 1) :: r.2.1, r.2.2)

/-- The prefix chain, from `pre[0]` at `k`. -/
def lgPreRun (z : V) (node : ℕ → ℕ) (k : ℕ) : List Stmt × List V × ℕ :=
  lgRun z node 0 64 (.n k) (k + 1)

/-- The suffix chain, the nodes reversed, from `suf[64]` after the prefix chain. -/
def lgSufRun (z : V) (node : ℕ → ℕ) (k : ℕ) : List Stmt × List V × ℕ :=
  lgRun z (fun i => node (63 - i)) 0 64 (.n (lgPreRun z node k).2.2) ((lgPreRun z node k).2.2 + 1)

/-- `pre[i]`, `i ≤ 64`. -/
def lgPre (z : V) (node : ℕ → ℕ) (k i : ℕ) : V :=
  if i = 0 then .n k else (lgPreRun z node k).2.1.getD (i - 1) (.n 0)

/-- `suf[i]`, `i ≤ 64`. -/
def lgSuf (z : V) (node : ℕ → ℕ) (k i : ℕ) : V :=
  if i = 64 then .n (lgPreRun z node k).2.2 else (lgSufRun z node k).2.1.getD (63 - i) (.n 0)

/-- The first numerator's value. -/
def lgOut (z : V) (node : ℕ → ℕ) (k : ℕ) : ℕ := (lgSufRun z node k).2.2

/-- The expansion of `lag64(z, out, node_base)` from value `k`, `node j` the word of node `j`. -/
def lag64T (z : V) (node : ℕ → ℕ) (k : ℕ) : List Stmt :=
  [.atom (.const (.n k) (word 1 0 0))] ++ (lgPreRun z node k).1 ++
    [.atom (.const (.n (lgPreRun z node k).2.2) (word 1 0 0))] ++ (lgSufRun z node k).1 ++
    ((List.range 64).map fun i =>
      [.atom (.mul (.n (lgOut z node k + i)) (lgPre z node k i) (lgSuf z node k (i + 1)))]).flatten

/-- The nodes from `b`. -/
def phi8From (b : ℕ) (j : ℕ) : ℕ := phi8Words.getD (b + j) 0

theorem segment_eq {l t : List Stmt} {a : ℕ} (h : (l.drop a).take t.length = t) :
    l = l.take a ++ t ++ l.drop (a + t.length) := by
  conv_lhs => rw [← List.take_append_drop a l, ← List.take_append_drop t.length (l.drop a)]
  rw [h, List.drop_drop, List.append_assoc]

set_option maxRecDepth 100000 in
/-- `lag64(zerocheck_z, lagrange_nums, 64)` in `verify_flock` (G:1871). -/
theorem core12_lag64_hi :
    Fn.body Data.core12 = (Fn.body Data.core12).take 954 ++ lag64T (.n 1014) (phi8From 64) 1015 ++
      (Fn.body Data.core12).drop (954 + (lag64T (.n 1014) (phi8From 64) 1015).length) :=
  segment_eq (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
/-- `lag64(zerocheck_z, claim_nums, 0)` in `verify_flock` (G:1923). -/
theorem core12_lag64_lo :
    Fn.body Data.core12 = (Fn.body Data.core12).take 2192 ++ lag64T (.n 1014) (phi8From 0) 2273 ++
      (Fn.body Data.core12).drop (2192 + (lag64T (.n 1014) (phi8From 0) 2273).length) :=
  segment_eq (stmtsEqb_sound (by decide +kernel))

set_option maxRecDepth 100000 in
/-- `lag64(fresh[GEN ** FRESH_Z_SKIP], row_nums, 0)` in `aggregate_claims`' loop `__loop99`
(G:3452). -/
theorem core572_lag64 :
    Fn.body Data.core572 = (Fn.body Data.core572).take 3 ++ lag64T (.n 11) (phi8From 0) 12 ++
      (Fn.body Data.core572).drop (3 + (lag64T (.n 11) (phi8From 0) 12).length) :=
  segment_eq (stmtsEqb_sound (by decide +kernel))

/-! ## Soundness -/

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- What one factor asks. -/
def LgStepOk (σ : Val) (z : V) (node : ℕ) (prev : V) (c : ℕ) : Prop :=
  if node = 0 then σ (.n c) = σ prev * σ z else
    σ (.n c) = word node 0 0 ∧ σ (.n (c + 1)) = σ z + σ (.n c) ∧
      σ (.n (c + 2)) = σ prev * σ (.n (c + 1))

theorem holds_lgStep (z : V) (node : ℕ) (prev : V) (c : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (lgStep z node prev c).1 next kret ↔ LgStepOk σ z node prev c ∧ next := by
  unfold lgStep LgStepOk
  by_cases h : node = 0 <;> simp [h, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_assoc]

theorem lgStep_value {z : V} {node : ℕ} {prev : V} {c : ℕ} (h : LgStepOk σ z node prev c) :
    σ (.n ((lgStep z node prev c).2 - 1)) = σ prev * (σ z + word node 0 0) := by
  unfold LgStepOk at h
  unfold lgStep
  by_cases hn : node = 0
  · rw [ite_pos' hn] at h ⊢
    rw [Nat.add_sub_cancel, h, hn, word_zero, add_zero]
  · rw [ite_neg' hn] at h ⊢
    obtain ⟨h0, h1, h2⟩ := h
    rw [show c + 3 - 1 = c + 2 by omega, h2, h1, h0]

/-- What a chain asks. -/
def LgRunOk (σ : Val) (z : V) (node : ℕ → ℕ) : ℕ → ℕ → V → ℕ → Prop
  | _, 0, _, _ => True
  | i, n + 1, prev, c => LgStepOk σ z (node i) prev c ∧
      LgRunOk σ z node (i + 1) n (.n ((lgStep z (node i) prev c).2 - 1)) (lgStep z (node i) prev c).2

theorem holds_lgRun (z : V) (node : ℕ → ℕ) (next : Prop) (kret : List E → Prop) :
    ∀ n i prev c, Stmt.HoldsList C rd σ (lgRun z node i n prev c).1 next kret ↔
      LgRunOk σ z node i n prev c ∧ next
  | 0, _, _, _ => by simp [lgRun, LgRunOk, Stmt.HoldsList]
  | n + 1, i, prev, c => by
    simp only [lgRun, LgRunOk]
    rw [holdsList_append, holds_lgStep, holds_lgRun z node next kret n, and_assoc]

/-- The factor at node `j`. -/
def lgFac (σ : Val) (z : V) (node : ℕ → ℕ) (j : ℕ) : E := σ z + word (node j) 0 0

theorem lgRun_values (z : V) (node : ℕ → ℕ) : ∀ n i prev c, LgRunOk σ z node i n prev c →
    ∀ t < n, σ ((lgRun z node i n prev c).2.1.getD t (.n 0)) =
      σ prev * ∏ j ∈ Finset.range (t + 1), lgFac σ z node (i + j)
  | 0, _, _, _, _, t, ht => absurd ht (by omega)
  | n + 1, i, prev, c, ⟨hs, hr⟩, t, ht => by
    simp only [lgRun]
    cases t with
    | zero =>
      rw [List.getD_cons_zero, lgStep_value hs, Finset.prod_range_one, Nat.add_zero, lgFac]
    | succ t =>
      rw [List.getD_cons_succ, lgRun_values z node n (i + 1) _ _ hr t (by omega), lgStep_value hs,
        Finset.prod_range_succ' (n := t + 1), Nat.add_zero, mul_assoc]
      simp only [show ∀ j, i + 1 + j = i + (j + 1) from fun j => by omega]
      rw [lgFac, mul_comm (σ z + word (node i) 0 0)]
      rfl

/-- What `lag64` asks. -/
def Lag64Ok (σ : Val) (z : V) (node : ℕ → ℕ) (k : ℕ) : Prop :=
  σ (.n k) = word 1 0 0 ∧ LgRunOk σ z node 0 64 (.n k) (k + 1) ∧
    σ (.n (lgPreRun z node k).2.2) = word 1 0 0 ∧
    LgRunOk σ z (fun i => node (63 - i)) 0 64 (.n (lgPreRun z node k).2.2)
      ((lgPreRun z node k).2.2 + 1) ∧
    ∀ i < 64, σ (.n (lgOut z node k + i)) = σ (lgPre z node k i) * σ (lgSuf z node k (i + 1))

theorem holds_lag64T (z : V) (node : ℕ → ℕ) (k : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (lag64T z node k) next kret ↔ Lag64Ok σ z node k ∧ next := by
  unfold lag64T Lag64Ok
  rw [holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_range_flatten 64 _ (fun _ => rfl)]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one, lgPreRun, lgSufRun]
  rw [holds_lgRun, holds_lgRun]
  simp only [and_true, and_assoc]

/-- The product over the nodes but `i`, split at `i`. -/
theorem prod_erase_split (f : ℕ → E) {i : ℕ} (hi : i < 64) :
    ∏ j ∈ (Finset.range 64).erase i, f j =
      (∏ j ∈ Finset.range i, f j) * ∏ j ∈ Finset.range (63 - i), f (63 - j) := by
  have hset : (Finset.range 64).erase i = Finset.range i ∪ Finset.Ico (i + 1) 64 := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  rw [hset, Finset.prod_union (Finset.disjoint_left.mpr fun j h1 h2 => by
    simp only [Finset.mem_range] at h1
    simp only [Finset.mem_Ico] at h2
    omega), Finset.prod_Ico_eq_prod_range, show 64 - (i + 1) = 63 - i by omega,
    ← Finset.prod_range_reflect (fun j => f (i + 1 + j))]
  exact congrArg _ (Finset.prod_congr rfl fun j hj => by
    have := Finset.mem_range.mp hj
    rw [show i + 1 + (63 - i - 1 - j) = 63 - j by omega])

theorem lgPre_value {z : V} {node : ℕ → ℕ} {k i : ℕ} (h0 : σ (.n k) = word 1 0 0)
    (hp : LgRunOk σ z node 0 64 (.n k) (k + 1)) (hi : i < 64) :
    σ (lgPre z node k i) = ∏ j ∈ Finset.range i, lgFac σ z node j := by
  unfold lgPre
  by_cases hi0 : i = 0
  · rw [ite_pos' hi0, h0, hi0, word_one, Finset.prod_range_zero]
  · rw [ite_neg' hi0, lgPreRun, lgRun_values z node 64 0 _ _ hp (i - 1) (by omega), h0, word_one,
      one_mul, show i - 1 + 1 = i by omega]
    simp only [Nat.zero_add]

theorem lgSuf_value {z : V} {node : ℕ → ℕ} {k i : ℕ} (h1 : σ (.n (lgPreRun z node k).2.2) = word 1 0 0)
    (hs : LgRunOk σ z (fun i => node (63 - i)) 0 64 (.n (lgPreRun z node k).2.2)
      ((lgPreRun z node k).2.2 + 1)) (hi : i < 64) :
    σ (lgSuf z node k (i + 1)) = ∏ j ∈ Finset.range (63 - i), lgFac σ z node (63 - j) := by
  unfold lgSuf
  by_cases hi63 : i + 1 = 64
  · rw [ite_pos' hi63, h1, word_one, show 63 - i = 0 by omega, Finset.prod_range_zero]
  · rw [ite_neg' hi63, lgSufRun, lgRun_values _ _ 64 0 _ _ hs (63 - (i + 1)) (by omega), h1,
      word_one, one_mul, show 63 - (i + 1) + 1 = 63 - i by omega]
    simp only [Nat.zero_add, lgFac]

/-- **The numerators** (G:780-797): `out[i]` is the product of `z + n_j` over the nodes `j ≠ i`. -/
theorem lag64_values {z : V} {node : ℕ → ℕ} {k : ℕ} (h : Lag64Ok σ z node k) :
    ∀ i < 64, σ (.n (lgOut z node k + i)) = ∏ j ∈ (Finset.range 64).erase i, lgFac σ z node j := by
  obtain ⟨h0, hp, h1, hs, ho⟩ := h
  intro i hi
  rw [ho i hi, prod_erase_split _ hi, lgPre_value h0 hp hi, lgSuf_value h1 hs hi]

/-- At the skip nodes from `b`: the numerators over `phi (b + j)`. -/
theorem lag64_phi {z : V} {b k : ℕ} (hb : b + 64 ≤ 128) (h : Lag64Ok σ z (phi8From b) k) :
    ∀ i < 64, σ (.n (lgOut z (phi8From b) k + i)) =
      ∏ j ∈ (Finset.range 64).erase i, (σ z + phi (b + j)) := by
  intro i hi
  rw [lag64_values h i hi]
  exact Finset.prod_congr rfl fun j hj => by
    have := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    rw [lgFac, phi8From, word_phi8Words (by omega)]

/-! ## Completeness -/

theorem agree_congr {a b : ℕ} {l : List E} (h : a = b) (hag : Agree σ a l) : Agree σ b l := h ▸ hag

/-- The honest words of one factor, `x` the point and `P` the product so far. -/
def lgStepV (x : E) (node : ℕ) (P : E) : List E :=
  if node = 0 then [P * x] else [word node 0 0, x + word node 0 0, P * (x + word node 0 0)]

/-- The honest words of a chain. -/
def lgRunV (x : E) (node : ℕ → ℕ) : ℕ → ℕ → E → List E
  | _, 0, _ => []
  | i, n + 1, P => lgStepV x (node i) P ++ lgRunV x node (i + 1) n (P * (x + word (node i) 0 0))

theorem lgStep_of_agree {z prev : V} {x P : E} {node c : ℕ} (hz : σ z = x) (hp : σ prev = P)
    (hag : Agree σ c (lgStepV x node P)) :
    LgStepOk σ z node prev c ∧ (lgStep z node prev c).2 = c + (lgStepV x node P).length := by
  unfold LgStepOk lgStep
  unfold lgStepV at hag ⊢
  by_cases hn : node = 0
  · simp only [ite_pos' hn] at hag ⊢
    have a0 := hag 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at a0
    exact ⟨by rw [a0, hz, hp], rfl⟩
  · simp only [ite_neg' hn] at hag ⊢
    have a0 := hag 0 (by simp)
    have a1 := hag 1 (by simp)
    have a2 := hag 2 (by simp)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at a0 a1 a2
    exact ⟨⟨a0, by rw [a1, hz, a0], by rw [a2, hp, a1]⟩, rfl⟩

theorem lgRun_of_agree {z : V} {x : E} (node : ℕ → ℕ) (hz : σ z = x) :
    ∀ n i prev c P, σ prev = P → Agree σ c (lgRunV x node i n P) →
      LgRunOk σ z node i n prev c ∧ (lgRun z node i n prev c).2.2 = c + (lgRunV x node i n P).length
  | 0, _, _, _, _, _, _ => ⟨trivial, rfl⟩
  | n + 1, i, prev, c, P, hp, hag => by
    simp only [lgRunV] at hag
    rw [agree_append] at hag
    obtain ⟨s1, s2⟩ := lgStep_of_agree hz hp hag.1
    have hv := lgStep_value s1
    rw [hp, hz] at hv
    rw [← s2] at hag
    obtain ⟨r1, r2⟩ := lgRun_of_agree node hz n (i + 1) _ _ _ hv hag.2
    refine ⟨⟨s1, r1⟩, ?_⟩
    simp only [lgRun, lgRunV, List.length_append]
    rw [r2, s2, Nat.add_assoc]

/-- The honest words of `lag64` at the point `x`. -/
def lag64V (x : E) (node : ℕ → ℕ) : List E :=
  [word 1 0 0] ++ lgRunV x node 0 64 (word 1 0 0) ++ [word 1 0 0] ++
    lgRunV x (fun i => node (63 - i)) 0 64 (word 1 0 0) ++
    (List.range 64).map fun i => (∏ j ∈ Finset.range i, (x + word (node j) 0 0)) *
      ∏ j ∈ Finset.range (63 - i), (x + word (node (63 - j)) 0 0)

/-- **Completeness**: the honest words from `k` meet `lag64`. -/
theorem lag64_of_agree {z : V} {x : E} {node : ℕ → ℕ} {k : ℕ} (hz : σ z = x)
    (hag : Agree σ k (lag64V x node)) : Lag64Ok σ z node k := by
  unfold lag64V at hag
  rw [agree_append, agree_append, agree_append, agree_append] at hag
  obtain ⟨⟨⟨⟨g0, g1⟩, g2⟩, g3⟩, g4⟩ := hag
  have h0 : σ (.n k) = word 1 0 0 := by simpa using g0 0 (by simp)
  obtain ⟨p1, p2⟩ := lgRun_of_agree node hz 64 0 (.n k) (k + 1) _ h0 g1
  have h1 : σ (.n (lgPreRun z node k).2.2) = word 1 0 0 := by
    have := g2 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at this
    rw [lgPreRun, p2]
    convert this using 3
    simp
    omega
  have g3' : Agree σ ((lgPreRun z node k).2.2 + 1) (lgRunV x (fun i => node (63 - i)) 0 64 (word 1 0 0)) :=
    agree_congr (by rw [lgPreRun, p2]; simp; omega) g3
  obtain ⟨s1, s2⟩ := lgRun_of_agree (fun i => node (63 - i)) hz 64 0 _ _ _ h1 g3'
  have g4' := agree_congr (show _ = lgOut z node k by
    rw [lgOut, lgSufRun, s2, lgPreRun, p2]; simp; omega) g4
  refine ⟨h0, p1, h1, s1, fun i hi => ?_⟩
  rw [lgPre_value h0 p1 hi, lgSuf_value h1 s1 hi, g4' i (by simp; omega),
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  simp only [lgFac, hz]

end
end LeanVM.Guest.B1
