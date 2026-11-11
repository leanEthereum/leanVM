/-
  LeanVM.Guest.Budget.L5Count

  The children loop's instructions, per opcode, iteration by iteration: each child's claim lists'
  digests and statement digest by their static counts, `verify_sub` within a bound `V c` per
  child.
-/

module

public import LeanVM.Guest.Budget.VsCount
public import LeanVM.Guest.Budget.Chain
public import LeanVM.Guest.Budget.Static
public import LeanVM.Guest.B1.Main.MainHonestBudget
public import LeanVM.Guest.Budget.Instrs
public import LeanVM.Guest.Count.VsMax
public import LeanVM.Guest.AcceptableChild

/-!
# The children loop's instructions

`ccW op n`: `child_claim_list_digest`'s instructions of `op` on `n` claims: its frame's weight,
`list_split`'s and `child_claim_list_any`'s (`anyW`: its frame's, `n / 136` iterations of
`__loop17`, `n % 136 / 17` of `__loop18` and the last group's `child_claim_list_last__L{n % 17}`;
`ccl_weight_le`, on a tree of honest shape `ccHonest n`, `any_weight_le` under it).
`l5B op X S V c`: iteration `c` of `__loop4`: its frame's weight, the two claim lists' digests
(`X c`, `S c` claims), `statement_digest`, and `verify_sub` within `V c`. `l5_weight_le`: the iterations from `c`
(`L5From`) weigh at most the sum of their `l5B`. `l5B_le`: `l5B` is at most a constant `l5C op`,
`ccS op` per claim, and `V c` (`ccW_le`: `n / 136` iterations within `⌈K / 136⌉` per claim).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.Count
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.B1.Main (ccHonest L5From l5CallList l5Ts l5Ts4 l5Evs l5Pre l5Tail l5Body
  l5Body_split l5Pre_straight l5_body find_l5)

@[expose] public section

/-- **`child_claim_list_any`'s instructions of `op` on `n = 136a + 17b + c` claims**: its frame's
weight, `a` iterations of `__loop17`, `b` of `__loop18`, and `child_claim_list_last__L{c}`. -/
def anyW (op : Opcode) (n : ℕ) : ℕ :=
  (omT op).getD 3 0 + n / 136 * kcL17 op + n % 136 / 17 * kcL18 op + (kcCclT op).getD (n % 17) 0

/-- **`child_claim_list_digest`'s instructions of `op` on `n` claims**: its frame's weight,
`list_split`'s and `child_claim_list_any`'s (`anyW`). -/
def ccW (op : Opcode) (n : ℕ) : ℕ :=
  (omT op).getD 1 0 + (if n = 0 then 0 else kcLs op + anyW op n)

theorem cclNames_eq {k : ℕ} (hk : k < 17) :
    B1.Digest.cclNames[k]! = "child_claim_list_last__L" ++ B1.Whir.natStr k := by
  interval_cases k <;> decide +kernel

theorem ccl_ne {k : ℕ} (hk : k < 17) :
    B1.Digest.cclNames[k]! ≠ "__loop17" ∧ B1.Digest.cclNames[k]! ≠ "__loop18" := by
  interval_cases k <;> decide

/-- **`child_claim_list_any`'s instructions** on a tree of honest shape (`anyHonest n`). -/
theorem any_weight_le (op : Opcode) {n : ℕ} (hn : n / 136 < 2 ^ 64 - 1) {rd : Reader} {t : Tree}
    {args rets : List E} (h : B1.Digest.anyHonest n t) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) : t.weight (B2C.ωArm B2C.xmssArmC op) ≤ anyW op n := by
  let W : Call → ℕ := fun c =>
    if c.f = "__loop17" then n / 136 * kcL17 op
    else if c.f = "__loop18" then n % 136 / 17 * kcL18 op else (kcCclT op).getD (n % 17) 0
  obtain ⟨σ, -, hle⟩ := NodeHonest.weight_le (B2C.ωArm B2C.xmssArmC op) (fun _ => W) h hv hb
    (by
      intro σ hQ c T hmem ht t' rets' hn' hv' hb' _
      obtain ⟨h4, h5, -, -, h33, h51⟩ := hQ
      simp only [B1.Digest.anyCalls, B1.Digest.anyTs, List.zip_cons_cons,
        List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [W, ↓reduceIte]
        have hq : n / 136 ≠ 0 := by simpa using ht
        have := l17_loop op rd t' _ rets' 0 (n / 136) hn' hv' hb'
          (by simp only [List.map_cons, List.getD_cons_zero]; rw [h33, one_eq_ofK])
          (by simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
              rw [h4, Value.gen_pow_eq_ofK]) (by omega) hn
        simpa using this
      · simp only [W, String.reduceEq, ↓reduceIte]
        have hq : n % 136 / 17 ≠ 0 := by simpa using ht
        have := l18_loop op rd t' _ rets' 0 (n % 136 / 17) hn' hv' hb'
          (by simp only [List.map_cons, List.getD_cons_zero]; rw [h51, one_eq_ofK])
          (by simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
              rw [h5, Value.gen_pow_eq_ofK]) (by omega) (by omega)
        simpa using this
      · have hk : n % 17 < 17 := Nat.mod_lt _ (by norm_num)
        obtain ⟨e1, e2⟩ := ccl_ne hk
        simp only [W, e1, e2, ↓reduceIte]
        rw [cclNames_eq hk] at hn'
        exact ccl_weightLe op hk rd t' _ rets' hn' hv' hb')
  have hom := om_eq op (i := 3) (by norm_num)
  simp only [omNames, List.getD_cons_succ, List.getD_cons_zero] at hom
  rw [hom] at hle
  have hc : callsW W (B1.Digest.anyCalls n σ) ≤
      n / 136 * kcL17 op + n % 136 / 17 * kcL18 op + (kcCclT op).getD (n % 17) 0 := by
    obtain ⟨e1, e2⟩ := ccl_ne (Nat.mod_lt n (show 0 < 17 by norm_num))
    simp only [callsW, B1.Digest.anyCalls, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, W, String.reduceEq, e1, e2, ↓reduceIte]
    clear hle
    generalize n / 136 * kcL17 op = P
    generalize n % 136 / 17 * kcL18 op = Q
    split <;> split <;> omega
  unfold anyW
  omega

/-- **`child_claim_list_digest`'s instructions** on a tree of honest shape (`ccHonest n`: the
`child_claim_list_any` walk). -/
theorem ccl_weight_le (op : Opcode) {n : ℕ} (hn : n / 17 < 2 ^ 64 - 1) {rd : Reader} {t : Tree}
    {args rets : List E} (h : ccHonest n t) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) : t.weight (B2C.ωArm B2C.xmssArmC op) ≤ ccW op n := by
  let W : Call → ℕ := fun c => if c.f = "list_split" then kcLs op else anyW op n
  obtain ⟨σ, -, hle⟩ := NodeHonest.weight_le (B2C.ωArm B2C.xmssArmC op) (fun _ => W) h hv hb
    (by
      intro σ _ c T hmem _ t' rets' hn' hv' hb' hT'
      by_cases h0 : n = 0
      · simp [B1.Digest.ccCalls, h0] at hmem
      simp only [B1.Digest.ccCalls, h0, ↓reduceIte, B1.Digest.ccTs, List.zip_cons_cons,
        List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [W, ↓reduceIte]
        exact ls_weightLe op rd t' _ rets' hn' hv' hb'
      · simp only [W, String.reduceEq, ↓reduceIte]
        exact any_weight_le op (by omega) hT' hv' hb')
  have hom := om_eq op (i := 1) (by norm_num)
  simp only [omNames, List.getD_cons_succ, List.getD_cons_zero] at hom
  rw [hom] at hle
  unfold ccW
  by_cases h0 : n = 0
  · have hc : callsW W (B1.Digest.ccCalls n σ) = 0 := by simp [callsW, B1.Digest.ccCalls, h0]
    simp only [h0, ↓reduceIte]
    omega
  · have hc : callsW W (B1.Digest.ccCalls n σ) = kcLs op + anyW op n := by
      simp only [callsW, B1.Digest.ccCalls, h0, ↓reduceIte, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, W, String.reduceEq]
      omega
    simp only [h0, ↓reduceIte]
    omega

/-- **Iteration `c` of `__loop4`**: its frame, the claim lists' digests on `X c` and `S c` claims,
the statement's digest, and `verify_sub` within `V c`. -/
def l5B (op : Opcode) (X S V : ℕ → ℕ) (c : ℕ) : ℕ :=
  (omT op).getD 2 0 + ccW op (X c) + ccW op (S c) + kcSd op + V c

theorem l5_walk {σ : Val} {fn : Fn} {es : List Ev} {vs : List V}
    (hf : coreProgram.find? "__loop4" = some fn) (hw : walk σ fn.body = .ret es vs) :
    es = l5Evs σ := by
  rw [find_l5, Option.some.injEq] at hf
  subst hf
  have hw' := walk_straight σ [] (l5Pre ++ [l5Tail]) l5Pre_straight
  rw [← l5Body_split, l5Body, ← l5_body] at hw'
  rw [hw'] at hw
  injection hw with h1
  exact h1.symm

set_option maxRecDepth 10000 in
/-- **The children loop's instructions**: the iterations from child `c` weigh at most the sum of
their `l5B`. -/
theorem l5_weight_le (op : Opcode) {ex es X S : ℕ → ℕ} {Pvs : ℕ → Tree → Prop} (V : ℕ → ℕ)
    (N : ℕ) (hX : ∀ c, X c / 17 < 2 ^ 64 - 1) (hS : ∀ c, S c / 17 < 2 ^ 64 - 1)
    (hV : ∀ c, c < N → ∀ (rd : Reader) (t : Tree) (args rets : List E), Pvs c t →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
        t.weight (B2C.ωArm B2C.xmssArmC op) ≤ V c) :
    ∀ m c (rd : Reader) (t : Tree) (args rets : List E), c + m ≤ N →
      L5From ex es (fun c => ccHonest (X c)) (fun c => ccHonest (S c)) Pvs m c t →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
        t.weight (B2C.ωArm B2C.xmssArmC op) ≤ iterSum (l5B op X S V) c m
  | 0, _, _, _, _, _, _, h, _, _ => h.elim
  | m + 1, c, rd, t, args, rets, hN, h, hv, hb => by
    obtain ⟨σ, bufs, ks, rfl, -, -, hcalls, hKT⟩ := h
    have hv' := hv
    obtain ⟨fn, hf, -, es', vs', hw, -, hes, hk⟩ := hv'
    have he := l5_walk hf hw
    subst he
    rw [hcalls] at hk
    have hk' := kids_weight_leL (B2C.ωArm B2C.xmssArmC op) (l5CallList σ)
      (l5Ts (ccHonest (X c)) (ccHonest (S c)) (Pvs c)
        (L5From ex es (fun c => ccHonest (X c)) (fun c => ccHonest (S c)) Pvs m (c + 1)))
      [ccW op (X c), ccW op (S c), kcSd op, V c, iterSum (l5B op X S V) (c + 1) m] ks hk hb.2 hKT
      (by simp [l5CallList, l5Ts, l5Ts4]) (by simp [l5CallList])
      (fun i hi _ _ ht t' rets' hn hv'' hb'' hT' => by
        have hi5 : i < 5 := by simpa [l5CallList] using hi
        interval_cases i <;>
          simp only [l5CallList, l5Ts, l5Ts4, List.cons_append, List.nil_append,
            List.getElem_cons_zero, List.getElem_cons_succ] at ht hn hv'' hT' ⊢
        · exact ccl_weight_le op (hX c) hT' hv'' hb''
        · exact ccl_weight_le op (hS c) hT' hv'' hb''
        · exact kcSd_weightLe op rd t' _ rets' hn hv'' hb''
        · exact hV c (by omega) rd t' _ rets' hT' hv'' hb''
        · exact l5_weight_le op V N hX hS hV m (c + 1) rd t' _ rets' (by omega) hT' hv'' hb'')
    have hom := om_eq op (i := 2) (by norm_num)
    simp only [omNames, List.getD_cons_succ, List.getD_cons_zero] at hom
    rw [Tree.weight, iterSum_succ, hom]
    simp only [List.sum_cons, List.sum_nil] at hk'
    have hl5 : l5B op X S V c = (omT op).getD 2 0 + ccW op (X c) + ccW op (S c) + kcSd op + V c :=
      rfl
    omega

/-- The per-claim slope of `ccW`: `⌈K / 136⌉` of `__loop17`'s `K` per iteration. -/
def ccS (op : Opcode) : ℕ := (kcL17 op + 135) / 136

/-- The constant of `ccW`: the two frames, `list_split`, at most `7` iterations of `__loop18`
(`n % 136 / 17 ≤ 7`) and the largest last group. -/
def ccA (op : Opcode) : ℕ :=
  (omT op).getD 1 0 + kcLs op + (omT op).getD 3 0 + 7 * kcL18 op + (kcCclT op).foldl max 0

theorem ccW_le (op : Opcode) (n : ℕ) : ccW op n ≤ ccA op + n * ccS op := by
  unfold ccW ccA ccS anyW
  split
  · omega
  · have hk : (kcCclT op).getD (n % 17) 0 ≤ (kcCclT op).foldl max 0 := by
      cases op <;> (have : n % 17 < 17 := Nat.mod_lt _ (by norm_num); interval_cases (n % 17) <;> decide)
    have hq : n / 136 * kcL17 op ≤ n * ((kcL17 op + 135) / 136) := by
      have h1 : kcL17 op ≤ 136 * ((kcL17 op + 135) / 136) := by omega
      have h2 : 136 * (n / 136) ≤ n := Nat.mul_div_le n 136
      calc n / 136 * kcL17 op ≤ n / 136 * (136 * ((kcL17 op + 135) / 136)) :=
            Nat.mul_le_mul_left _ h1
        _ = 136 * (n / 136) * ((kcL17 op + 135) / 136) := by ring
        _ ≤ n * ((kcL17 op + 135) / 136) := Nat.mul_le_mul_right _ h2
    have hb : n % 136 / 17 * kcL18 op ≤ 7 * kcL18 op :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- **An iteration's constant**: all but the claims' slope and `verify_sub`. -/
def l5C (op : Opcode) : ℕ := (omT op).getD 2 0 + 2 * ccA op + kcSd op

theorem l5B_le (op : Opcode) (X S V : ℕ → ℕ) (c : ℕ) :
    l5B op X S V c ≤ l5C op + ccS op * (X c + S c) + V c := by
  have h1 := ccW_le op (X c); have h2 := ccW_le op (S c)
  unfold l5B l5C
  have : ccS op * (X c + S c) = X c * ccS op + S c * ccS op := by ring
  omega

/-- **The children loop's instructions, linearly**: `m` iterations from `c` within `m` constants,
the slope on their claims and their `verify_sub`'s. -/
theorem iterSum_l5B_le (op : Opcode) (X S V : ℕ → ℕ) : ∀ c m,
    iterSum (l5B op X S V) c m ≤
      m * l5C op + ccS op * iterSum (fun i => X i + S i) c m + iterSum V c m
  | _, 0 => by simp [iterSum]
  | c, m + 1 => by
    rw [iterSum_succ, iterSum_succ, iterSum_succ]
    have := iterSum_l5B_le op X S V (c + 1) m
    have := l5B_le op X S V c
    have e : (m + 1) * l5C op = l5C op + m * l5C op := by ring
    have e2 : ccS op * (X c + S c + iterSum (fun i => X i + S i) (c + 1) m) =
      ccS op * (X c + S c) + ccS op * iterSum (fun i => X i + S i) (c + 1) m := by ring
    omega

/-! ## The honest children's loop -/

/-- **`verify_sub`'s instructions of `op` on a child of announced stack log `μ` and rate `r`**:
`vsCountT op` at its arm `μ - 20`, whatever the rate. -/
def vsCnt (op : Opcode) (μ _r : ℕ) : ℕ := (vsCountT op).getD (μ - 20) 0

/-- **`verify_sub`'s instructions of `op` on B1-d's tree at the deployed bounds** (`vsTs` at
`Count.vsWords` and `vkBound`): at most `vsCnt op μ r`. -/
theorem vs_weight_le_deployed (op : Opcode) {μ r : ℕ} (hμ1 : 20 ≤ μ) (hμ2 : μ ≤ 30)
    {rd : Reader} {t : Tree} {args rets : List E}
    (h : FlatShape coreProgram "verify_sub"
      (B1.VerifySub.vsTs B2C.fs Count.vsWords B1.VerifySub.vkBound μ r) t)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    t.weight (B2C.ωArm B2C.xmssArmC op) ≤ vsCnt op μ r :=
  vs_weight_le_vsTs op hμ1 hμ2 (vbgMax_eq.trans_le (by norm_num)) (vkBound_eq.trans_le (by norm_num)) h
    hv hb

theorem iterSum_le {A B : ℕ → ℕ} (h : ∀ i, A i ≤ B i) : ∀ c m, iterSum A c m ≤ iterSum B c m
  | _, 0 => by simp [iterSum]
  | c, m + 1 => by
    rw [iterSum_succ, iterSum_succ]
    have := iterSum_le h (c + 1) m
    have := h c
    omega

theorem iterSum_getD : ∀ (l : List ℕ) (c : ℕ) (f : ℕ → ℕ),
    (∀ i (hi : i < l.length), f (c + i) = l[i]) → iterSum f c l.length = l.sum
  | [], _, _, _ => by simp [iterSum]
  | a :: l, c, f, h => by
    rw [List.length_cons, iterSum_succ, List.sum_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0, iterSum_getD l (c + 1) f fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show c + (i + 1) = c + 1 + i by omega] at this
      simpa using this]

theorem hEx_lt {s : NodeStatement} {w : NodeWitness}
    (hl : DeployedLimits s w) (c : ℕ) : B1.Main.hEx w c < 2 ^ 20 := by
  unfold B1.Main.hEx
  by_cases hc : c < w.children.length
  · rw [B1.Main.getD_map_lt _ _ _ hc]
    exact (hl.childClaimListsBelow2Pow20 _ (List.getElem_mem hc)).1
  · rw [List.getD_eq_default _ _ (by simpa using hc)]
    norm_num

theorem hEs_lt {s : NodeStatement} {w : NodeWitness}
    (hl : DeployedLimits s w) (c : ℕ) : B1.Main.hEs w c < 2 ^ 20 := by
  unfold B1.Main.hEs
  by_cases hc : c < w.children.length
  · rw [B1.Main.getD_map_lt _ _ _ hc]
    exact (hl.childClaimListsBelow2Pow20 _ (List.getElem_mem hc)).2
  · rw [List.getD_eq_default _ _ (by simpa using hc)]
    norm_num

/-- **The honest children's loop's instructions of `op`**: on the tree `main`'s completeness gives
it (`mainPredsH`'s `T5`), each child's `verify_sub` within `vsCnt op` at its announced stack log
and rate, at most `l5C op` per child, `ccS op` per child's claim and `vsCnt op μ r` per child of
announced shape `(μ, r)`. -/
theorem l5_honest_weight_le (op : Opcode) {s : NodeStatement} {w : NodeWitness}
    {Pd : Tree → Prop} {Pvs : ℕ → Tree → Prop} (hl : DeployedLimits s w)
    (hPv : ∀ c (hc : c < w.children.length) (rd : Reader) (t : Tree) (args rets : List E),
      Pvs c t → t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
        t.weight (B2C.ωArm B2C.xmssArmC op) ≤
          vsCnt op (childShape End.bytecode w.children[c]).1 (childShape End.bytecode w.children[c]).2)
    {rd : Reader} {t : Tree} {args rets : List E} (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (hT : (B1.Main.mainPredsH s w Pd Pvs).T5 t) :
    t.weight (B2C.ωArm B2C.xmssArmC op) ≤ l5Lin (l5C op) (ccS op) (vsCnt op) (End.work s w) := by
  let L : List ℕ := w.children.map fun ch =>
    vsCnt op (childShape End.bytecode ch).1 (childShape End.bytecode ch).2
  let V : ℕ → ℕ := fun c => L.getD c 0
  have hV : ∀ c, c < w.children.length → ∀ (rd : Reader) (t : Tree) (args rets : List E),
      Pvs c t → t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
        t.weight (B2C.ωArm B2C.xmssArmC op) ≤ V c := by
    intro c hc rd t args rets hP hv hb
    have := hPv c hc rd t args rets hP hv hb
    simp only [V, L]
    rw [B1.Main.getD_map_lt _ _ _ hc]
    exact this
  have h1 := l5_weight_le op (X := fun c => (B1.Main.hKid s w c).ex)
    (S := fun c => (B1.Main.hKid s w c).es) V w.children.length
    (fun c => by have := hEx_lt hl c; show B1.Main.hEx w c / 17 < _; omega)
    (fun c => by have := hEs_lt hl c; show B1.Main.hEs w c / 17 < _; omega)
    hV w.children.length 0 rd t args rets (by omega) hT hv hb
  have h2 := iterSum_l5B_le op (fun c => (B1.Main.hKid s w c).ex) (fun c => (B1.Main.hKid s w c).es)
    V 0 w.children.length
  have hVs : iterSum V 0 w.children.length = ((End.work s w).childShapes.map fun p =>
      vsCnt op p.1 p.2).sum := by
    have := iterSum_getD L 0 V (fun i _ => by simp only [V, Nat.zero_add]; rw [List.getD_eq_getElem])
    simp only [L, List.length_map] at this
    rw [this]
    simp only [End.work, List.map_map]
    rfl
  let C : List ℕ := w.children.map fun ch => ch.statement.claims.xmss.length +
    ch.statement.claims.sphincs.length
  have hXS : iterSum (fun i => (B1.Main.hKid s w i).ex + (B1.Main.hKid s w i).es) 0
      w.children.length ≤ (End.work s w).childClaims := by
    have hle := iterSum_le (A := fun i => (B1.Main.hKid s w i).ex + (B1.Main.hKid s w i).es)
      (B := fun i => C.getD i 0) (fun i => by
        have := B1.Main.kid_counts w i
        show B1.Main.hEx w i + B1.Main.hEs w i ≤ _
        simp only [C]
        omega) 0 w.children.length
    have := iterSum_getD C 0 (fun i => C.getD i 0) (fun i _ => by
      simp only [Nat.zero_add]; rw [List.getD_eq_getElem])
    simp only [C, List.length_map] at this
    rw [this] at hle
    exact hle
  have e : (End.work s w).children = w.children.length := rfl
  unfold l5Lin
  rw [e, ← hVs]
  have := Nat.mul_le_mul_left (ccS op) hXS
  rw [Nat.mul_comm (l5C op)]
  omega

end
end LeanVM.Guest.Budget
