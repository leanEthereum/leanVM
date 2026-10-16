module

public import LeanVMCircuits.Rec.GkrChain
public import LeanVMCircuits.Rec.Bind

@[expose] public section

/-!
The bus's draw `(β, A)` and its fingerprint weights, from the dumps' calls.

`bus::verify_balance` draws `A`'s four coordinates from the child's transcript, builds `eq_table(A)` (`Arith::eq_table`: from a `one`, each coordinate `A_j` doubles the table, the entries with bit `j` set a `mul(old, A_j)`, emitted first, those with it clear a `times_one_plus(old, A_j) = mul_add(old, A_j, old)`), then draws `β`. `DrawCert` names where: the `one` call, `A`'s wires and the five challenges `β, A_0, .., A_3` (`ChalCert`s on one transcript). `DrawCert.ok` checks the table's calls, the side's fingerprint weights the table's first five entries, its `β` and `A` the challenges' wires, and the challenges drawn from the transcript (`ChalCert.ok`, `chalsOk`).

`DrawCert.sem`: where the calls hold and the transcript's squeezes answer the oracle, the side's `β` is the oracle's draw's first coordinate and its weights `w_i` are `eqAt A i` at the draw's other four (`readR` of the challenges' words, `DrawCert.own`), the premise `ChildCerts.roots` takes. `DrawCert.owns`: those words are the transcript's challenge seeds, no two the same (`OwnAt`, `OwnInj`), what `AirLink.busRun_frac` takes of the draw.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Finset AirLink

/-- Where a dump's calls draw a bus's `(β, A)`: the transcript `tr`, the `one` call `start` the eq table starts from, `A`'s four wires `a`, and the challenges `β, A_0, .., A_3` in that order. -/
structure DrawCert where
  tr : ℕ
  start : ℕ
  a : List ℕ
  chals : List ChalCert
  deriving Inhabited, Repr

namespace DrawCert

variable (os : Array (List ℕ)) (dc : DrawCert)

/-- `A_j`'s wire. -/
def aj (j : ℕ) : ℕ := dc.a.getD j 0

/-- Round `j`'s first call: round `j` makes `2^j` `mul`s, then `2^j` `mul_add`s. -/
def round (j : ℕ) : ℕ := dc.start + 1 + 2 * (2 ^ j - 1)

/-- The table's entry `k` before round `j`: the `one`'s output, then after round `j` an entry with bit `j` clear its `mul_add`'s, set its `mul`'s. -/
def tbl : ℕ → ℕ → ℕ
  | 0, _ => o os dc.start
  | j + 1, k => if k < 2 ^ j then o os (dc.round j + 2 ^ j + k) else o os (dc.round j + (k - 2 ^ j))

/-- `Arith::eq_table(A)`'s calls: the `one`, then per coordinate the table times `A_j`, then the table times `1 + A_j` as `mul_add(old, A_j, old)`. -/
def calls : List (ℕ × Call) :=
  (dc.start, .one) :: (List.range 4).flatMap fun j =>
    ((List.range (2 ^ j)).map fun k => (dc.round j + k, .mul (dc.tbl os j k) (dc.aj j))) ++
      (List.range (2 ^ j)).map fun k => (dc.round j + 2 ^ j + k, .mulAdd (dc.tbl os j k) (dc.aj j) (dc.tbl os j k))

/-- Challenge `i` of `(β, A)`. -/
def chal (i : Fin 5) : ChalCert := dc.chals.getD i default

/-- The draw's words: challenge `i`'s three. -/
def own : Fin 5 → Fin 3 → ℕ := chalWords os dc.chal

/-- The draw against a side's certificate: the eq table's calls are in the replay, the side's five fingerprint weights are its first five entries, `β` and `A`'s wires are the challenges', each challenge is drawn after its transcript's first `time` blocks (`ChalCert.ok`) and the five from the oracle's words (`chalsOk`). -/
def ok (s : State) (cs : Array Call) (rl : Array Bool) (ts : List Transcript) (sc : SideCert) : Bool :=
  callsOk cs rl (dc.calls os) && dc.a.length == 4 && sc.w == (List.range 5).map (dc.tbl os 4) &&
    dc.chals.map (·.chal) == sc.beta :: dc.a && dc.chals.all (·.ok s os cs (ts.getD dc.tr default).blocks) &&
    chalsOk s os (ts.getD dc.tr default) false dc.chals

end DrawCert

/-- The draw a side's weights `w` and `β` read, on transcript `tr`: the eq table's `one` the call 23 before the first weight's maker (its round-3 `mul_add` of entry 0), `A_j` the right operand of round `j`'s first `mul`, and each challenge's squeezed words (`chalOf`) at its time (`chalTime`). -/
def drawOf (rp : Replay) (ts : List Transcript) (tr : ℕ) (w : List ℕ) (beta : ℕ) : Option DrawCert := do
  let idx := outIndex rp
  let start := rp.maker.getD (w.headD 0) 0 - 23
  let dc0 : DrawCert := { tr, start, a := [], chals := [] }
  let a ← (List.range 4).mapM fun j => match rp.calls.getD (dc0.round j) .zero with
    | .mul _ x => some x
    | _ => none
  let chals ← (beta :: a).mapM fun x => do
    let cc ← chalOf rp idx x
    let time ← chalTime rp rp.state (ts.getD tr default) cc
    return { cc with time }
  return { dc0 with a, chals }

section Sem

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
  {dc : DrawCert}

theorem DrawCert.ok_parts {s : State} {ts : List Transcript} {sc : SideCert} (h : dc.ok os s cs rl ts sc = true) :
    callsOk cs rl (dc.calls os) = true ∧ dc.a.length = 4 ∧ sc.w = (List.range 5).map (dc.tbl os 4) ∧
      dc.chals.map (·.chal) = sc.beta :: dc.a ∧ (∀ c ∈ dc.chals, c.ok s os cs (ts.getD dc.tr default).blocks = true) ∧
      chalsOk s os (ts.getD dc.tr default) false dc.chals = true := by
  simp only [DrawCert.ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- Round `j` of `eq_table` doubles the table: entry `k` is entry `k mod 2^j` times `A_j` or `1 + A_j` by bit `j`. -/
theorem DrawCert.round_sem (hF : Facts cs rl os st val) (hok : callsOk cs rl (dc.calls os) = true) {j : ℕ}
    (hj : j < 4) :
    ∀ k < 2 ^ (j + 1), Model.ev val (dc.tbl os (j + 1) k) =
      Model.ev val (dc.tbl os j (k % 2 ^ j)) *
        (if k.testBit j then Model.ev val (dc.aj j) else 1 + Model.ev val (dc.aj j)) := by
  have hmem : ∀ x, x ∈ ((List.range (2 ^ j)).map fun k => (dc.round j + k, Call.mul (dc.tbl os j k) (dc.aj j))) ++
      (List.range (2 ^ j)).map (fun k => (dc.round j + 2 ^ j + k,
        Call.mulAdd (dc.tbl os j k) (dc.aj j) (dc.tbl os j k))) → x ∈ dc.calls os := fun x hx =>
    List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, hx⟩)
  intro k hk
  by_cases hlo : k < 2 ^ j
  · have h := holds_of_mem hF hok (hmem _ (List.mem_append_right _
      (List.mem_map.mpr ⟨k, List.mem_range.mpr hlo, rfl⟩)))
    simp only [Call.Holds, getD_o] at h
    rw [DrawCert.tbl, if_pos hlo, h, Nat.mod_eq_of_lt hlo]
    simp only [Nat.testBit_lt_two_pow hlo, Bool.false_eq_true, if_false]
    ring
  · have hk' : k - 2 ^ j < 2 ^ j := by rw [pow_succ] at hk; omega
    have h := holds_of_mem hF hok (hmem _ (List.mem_append_left _
      (List.mem_map.mpr ⟨k - 2 ^ j, List.mem_range.mpr hk', rfl⟩)))
    simp only [Call.Holds, getD_o] at h
    have hmod : k % 2 ^ j = k - 2 ^ j := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hk']
    have hbit : k.testBit j = true := by
      have := Nat.testBit_two_pow_add_eq (k - 2 ^ j) j
      rwa [show 2 ^ j + (k - 2 ^ j) = k by omega, Nat.testBit_lt_two_pow hk', Bool.not_false] at this
    rw [DrawCert.tbl, if_neg hlo, h, hmod, hbit]
    simp

/-- After `j` rounds entry `k` is `∏_{i < j} (A_i if bit i of k else 1 + A_i)`. -/
theorem DrawCert.tbl_sem (hF : Facts cs rl os st val) (hok : callsOk cs rl (dc.calls os) = true) :
    ∀ j ≤ 4, ∀ k < 2 ^ j, Model.ev val (dc.tbl os j k) = prodBits (fun i => Model.ev val (dc.aj i)) k j := by
  have ho := holds_of_mem hF hok (List.mem_cons_self (a := (dc.start, Call.one)))
  simp only [Call.Holds, getD_o] at ho
  intro j
  induction j with
  | zero => intro _ k _; simp [DrawCert.tbl, ho, prodBits]
  | succ j ih =>
    intro hj k hk
    rw [DrawCert.round_sem hF hok (by omega) k hk, ih (by omega) _ (Nat.mod_lt _ (by positivity)), prodBits,
      prodBits, Finset.prod_range_succ]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp [Nat.testBit_mod_two_pow, hi]

/-- The challenges as a family over `Fin 5`. -/
theorem DrawCert.ofFn_chal {dc : DrawCert} (h : dc.chals.length = 5) : List.ofFn dc.chal = dc.chals := by
  refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
  simp only [List.getElem_ofFn, DrawCert.chal, List.getD_eq_getElem _ _ h2]

theorem DrawCert.chals_length {s : State} {ts : List Transcript} {sc : SideCert} (h : dc.ok os s cs rl ts sc = true) :
    dc.chals.length = 5 := by
  obtain ⟨-, ha, -, hc, -⟩ := DrawCert.ok_parts h
  have := congrArg List.length hc
  simp only [List.length_map, List.length_cons, ha] at this
  exact this

theorem DrawCert.mem_chal {dc : DrawCert} (hlen : dc.chals.length = 5) (i : Fin 5) : dc.chal i ∈ dc.chals := by
  simp only [DrawCert.chal, List.getD_eq_getElem _ _ (by rw [hlen]; exact i.isLt)]
  exact List.getElem_mem _

/-- The draw's words are its transcript's challenge seeds one step after each challenge's time, no two the same: `AirLink.busRun_frac`'s `OwnAt` and `OwnInj` of the draw `readR (dc.own os)`. -/
theorem DrawCert.owns {s : State} {ts : List Transcript} {sc : SideCert} (h : dc.ok os s cs rl ts sc = true) :
    OwnAt s (ts.getD dc.tr default) (dc.own os) (fun i => (dc.chal i).time) ∧ OwnInj (dc.own os) := by
  obtain ⟨-, -, -, -, hok, hch⟩ := DrawCert.ok_parts h
  have hlen := DrawCert.chals_length h
  rw [← DrawCert.ofFn_chal hlen] at hch
  obtain ⟨h1, h2, -⟩ := chalsOk_sem hch fun i => ChalCert.ok_words (hok _ (DrawCert.mem_chal hlen i))
  exact ⟨h1, h2⟩

/-- Where the calls hold and the draw's transcript's squeezes answer the oracle `ρ`, the side's `β` is the draw's first coordinate and its fingerprint weights are `eqAt A i` at the draw's other four. -/
theorem DrawCert.sem {s : State} {ts : List Transcript} {sc : SideCert} {ρ : ℕ → K} (hF : Facts cs rl os st val)
    (h : dc.ok os s cs rl ts sc = true) (hans : ∀ p ∈ chalSeeds s (ts.getD dc.tr default), nu val p.2 = ρ p.2) :
    readR (dc.own os) ρ 0 = Model.ev val sc.beta ∧
      ∀ j (hj : j < 5), sc.wV val j = UnionSound.eqAt (Fin.tail (readR (dc.own os) ρ)) ⟨j, by omega⟩ := by
  obtain ⟨hcalls, ha, hw, hc, hok, hch⟩ := DrawCert.ok_parts h
  have hlen := DrawCert.chals_length h
  have hmem := DrawCert.mem_chal hlen
  rw [← DrawCert.ofFn_chal hlen] at hch
  have hr : ∀ i : Fin 5, Model.ev val (dc.chal i).chal = readR (dc.own os) ρ i := fun i =>
    chal_readR hch (fun i => hok _ (hmem i)) hF hans i
  -- The challenges' wires: `β`, then `A`'s.
  have hwire : ∀ i : Fin 5, (dc.chal i).chal = (sc.beta :: dc.a).getD i 0 := fun i => by
    have e := congrArg (fun l => l.getD i 0) hc
    rw [← e, List.getD_eq_getElem _ _ (by simp [hlen]), List.getElem_map, DrawCert.chal,
      List.getD_eq_getElem _ _ (by rw [hlen]; exact i.isLt)]
  refine ⟨by rw [← hr 0, hwire 0]; rfl, fun j hj => ?_⟩
  have hA : (fun i : Fin 4 => Model.ev val (dc.aj i)) = Fin.tail (readR (dc.own os) ρ) := funext fun i => by
    rw [Fin.tail, ← hr i.succ, hwire i.succ]
    rfl
  have hwj : sc.w.getD j 0 = dc.tbl os 4 j := by
    rw [hw, List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map, List.getElem_range]
  rw [SideCert.wV, hwj, DrawCert.tbl_sem hF hcalls 4 le_rfl j (by omega), ← hA, prodBits, UnionSound.eqAt,
    ← Fin.prod_univ_eq_prod_range (fun i => if j.testBit i then Model.ev val (dc.aj i) else 1 + Model.ev val (dc.aj i)) 4]

end Sem

end LeanVMCircuits.Rec.Bind
