/-
  LeanVM.Guest.B1.Digest.Steps

  Memory runs, sponge states held in memory, `mul_range` loops read forward, and `KECCAK` chains
  between states held in memory.
-/

module

public import LeanVM.Guest.B1.Digest.Range

/-!
# Steps: memory, loops, chains between states

* `memAt rd p k`, `memRun rd p n`: the word at `p · g^k`, the `n` words from `p`; a run that
  `ReadsAt` describes is the memory's (`readsAt_memRun`).
* `StateAt rd p off S`: the thirteen cells of the sponge state `S` (even layout) at
  `p · g^off`, … (`claim_list_digest`'s heap chain).
* `splitLoop`, `holds_loopBody`: a `mul_range` helper's body, atoms then the conditional call;
  `loop_sound`: a guarded loop read forward, through `Program.Rel` only.
* `stLoadsOk`; `chain_whole_mem`, `chain_final_mem`: a chain from a state read from memory, over
  cells read from memory, to a state written to memory (`final=0`) or a digest.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

open scoped VDec

@[expose] public section

/-! ## Memory runs -/

/-- The word at `p · g^k`, or `0`. -/
noncomputable def memAt (rd : Reader) (p : E) (k : ℕ) : E :=
  (rd (p.limb 0 * Parameters.addressOfIndex k)).getD 0

/-- The `n` words from `p`. -/
noncomputable def memRun (rd : Reader) (p : E) (n : ℕ) : List E := (List.range n).map (memAt rd p)

theorem memAt_of_load {rd : Reader} {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) :
    memAt rd p k = v := by
  unfold memAt; rw [h.2]; rfl

theorem readsAt_memRun {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) :
    xs = memRun rd p xs.length :=
  List.ext_getElem (by simp [memRun]) fun k h1 _ => by simp [memRun, memAt_of_load (h k h1)]

@[simp] theorem length_memRun (rd : Reader) (p : E) (n : ℕ) : (memRun rd p n).length = n := by
  simp [memRun]

/-- A run read in two parts. -/
theorem readsAt_append {rd : Reader} {p : E} {xs ys : List E} :
    ReadsAt rd p (xs ++ ys) ↔ ReadsAt rd p xs ∧ ReadsAt rd (p * gen ^ xs.length) ys := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have := h k (by rw [List.length_append]; omega)
      rwa [List.getElem_append_left hk] at this
    · have := h (xs.length + k) (by rw [List.length_append]; omega)
      rw [List.getElem_append_right (by omega)] at this
      simp only [Nat.add_sub_cancel_left] at this
      exact (loadHolds_mul_gen_pow rd p _ k _).mpr this
  · rintro ⟨h1, h2⟩ k hk
    rw [List.length_append] at hk
    by_cases hkx : k < xs.length
    · rw [List.getElem_append_left hkx]; exact h1 k hkx
    · rw [List.getElem_append_right (by omega)]
      have := (loadHolds_mul_gen_pow rd p _ _ _).mp (h2 (k - xs.length) (by omega))
      rwa [show xs.length + (k - xs.length) = k by omega] at this

/-! ## Sponge states in memory -/

/-- The thirteen cells of the state `S` (even layout) at `p · g^off`, …, `p · g^(off + 12)`. -/
def StateAt (rd : Reader) (p : E) (off : ℕ) (S : KeccakState) : Prop :=
  ∀ c : Fin 13, LoadHolds rd p (off + c) (cellsOfState S false c)

/-- The thirteen values `vs` are loaded through `p` at offsets `off`, …, `off + 12`. -/
def stLoadsOk (atoms : List Atom) (p : V) (vs : List V) (off : ℕ) : Bool :=
  vs.length == 13 && (List.range 13).all fun c => atoms.any (isLoadAt (vs.getD c default) p (off + c))

theorem stLoads_sound {rd : Reader} {σ : Val} {atoms : List Atom} {p : V} {vs : List V} {off : ℕ}
    (h : stLoadsOk atoms p vs off = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) (c : Fin 13) :
    LoadHolds rd (σ p) (off + c) (σ (vs.getD c default)) := by
  simp only [stLoadsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact load_sound (h.2 c c.isLt) hat

/-! ## Loop bodies -/

/-- A `mul_range` helper's body: atoms, the conditional call, `ret []`. -/
def splitLoop : List Stmt → Option (List Atom × V × String × List V)
  | [.callIf c f args, .ret []] => some ([], c, f, args)
  | .atom a :: rest => (splitLoop rest).map fun p => (a :: p.1, p.2)
  | _ => none

theorem splitLoop_eq : ∀ {body : List Stmt} {as : List Atom} {c : V} {f : String} {args : List V},
    splitLoop body = some (as, c, f, args) →
      body = as.map Stmt.atom ++ [Stmt.callIf c f args, Stmt.ret []]
  | [], _, _, _, _, h => by simp [splitLoop] at h
  | [.callIf c' f' a', .ret []], as, c, f, args, h => by
    simp only [splitLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl
  | .atom a :: rest, as, c, f, args, h => by
    simp only [splitLoop, Option.map_eq_some_iff, Prod.exists] at h
    obtain ⟨as', c', f', a', h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h2
    rw [splitLoop_eq h1]
    rfl
  | [.callIf _ _ _], _, _, _, _, h | .callIf _ _ _ :: .ret (_ :: _) :: _, _, _, _, _, h
  | .callIf _ _ _ :: .ret [] :: _ :: _, _, _, _, _, h
  | .callIf _ _ _ :: .atom _ :: _, _, _, _, _, h | .callIf _ _ _ :: .ite .. :: _, _, _, _, _, h
  | .callIf _ _ _ :: .match_ .. :: _, _, _, _, _, h | .callIf _ _ _ :: .call .. :: _, _, _, _, _, h
  | .callIf _ _ _ :: .callIf .. :: _, _, _, _, _, h
  | .callIf _ _ _ :: .dispatch .. :: _, _, _, _, _, h
  | .ret _ :: _, _, _, _, _, h | .ite .. :: _, _, _, _, _, h | .match_ .. :: _, _, _, _, _, h
  | .call .. :: _, _, _, _, _, h | .dispatch .. :: _, _, _, _, _, h => by
    simp [splitLoop] at h

theorem holds_loopBody {C : CallRel} {rd : Reader} {σ : Val} (as : List Atom) (c : V) (f : String)
    (args : List V) :
    Stmt.HoldsList C rd σ (as.map Stmt.atom ++ [Stmt.callIf c f args, Stmt.ret []]) False
        (fun rs => rs = []) ↔
      (∀ a ∈ as, a.Holds rd σ) ∧ IsInK (σ c) ∧ (σ c ≠ 0 → C f (args.map σ) []) := by
  induction as with
  | nil => simp [Stmt.HoldsList, Stmt.Holds]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, Stmt.HoldsList, Stmt.Holds, List.forall_mem_cons,
      ih, and_assoc]

theorem one_add_gen_pow_ne_zero {m : ℕ} (h0 : 0 < m) (hm : m < ordG) : 1 + gen ^ m ≠ 0 := by
  intro h
  have h1 : gen ^ m = gen ^ 0 := by rw [pow_zero]; exact (e_add_eq_zero_iff.mp h).symm
  have := gen_pow_inj hm (by norm_num) h1
  omega

/-- **A guarded loop, forward** (`for x in mul_range(1, N)`, `N = g^m`): if every run of the
helper at `x` gives the body `B x` and, while `x·g ≠ N`, a run at `x·g`, then the guard and its
call give `B` at every `g^j`, `j < m`. -/
theorem loop_sound {rd : Reader} {f : String} {ps : List E} {N : E} {m : ℕ} {B : E → Prop}
    (hm : m < ordG) (hN : N = gen ^ m)
    (hstep : ∀ x, coreProgram.Rel rd f (x :: ps) [] →
      B x ∧ (x * gen + N ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []))
    (h : 1 + N ≠ 0 → coreProgram.Rel rd f (1 :: ps) []) : ∀ j < m, B (gen ^ j) := by
  have key : ∀ t k, k + t = m → coreProgram.Rel rd f (gen ^ k :: ps) [] →
      ∀ j, k ≤ j → j < m → B (gen ^ j) := by
    intro t
    induction t with
    | zero => intro k hk _ j h1 h2; omega
    | succ t ih =>
      intro k hk hrun j h1 h2
      obtain ⟨hB, hnext⟩ := hstep _ hrun
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hB
      · have hne : gen ^ k * gen + N ≠ 0 := by
          intro he
          rw [gen_pow_add_eq_zero_iff, hN] at he
          have := gen_pow_inj hm (by unfold ordG at hm; omega) he
          omega
        have := hnext hne
        rw [gen_pow_mul_gen] at this
        exact ih (k + 1) (by omega) this j hlt h2
  intro j hj
  have h1 := h (by rw [hN]; exact one_add_gen_pow_ne_zero (by omega) hm)
  rw [← pow_zero gen] at h1
  exact key m 0 (by omega) h1 j (Nat.zero_le j) hj

/-! ## Products, by evaluation -/

/-- The operands of the first `MUL` into `x`. -/
def mulOf (atoms : List Atom) (x : V) : Option (V × V) :=
  atoms.findSome? fun a => match a with
    | .mul d p q => if d = x then some (p, q) else none
    | _ => none

theorem mulOf_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x p q : V}
    (h : mulOf atoms x = some (p, q)) (hat : ∀ a ∈ atoms, a.Holds rd σ) : σ x = σ p * σ q := by
  obtain ⟨a, ha, hs⟩ := List.exists_of_findSome?_eq_some h
  have := hat a ha
  cases a <;> simp only [reduceCtorEq] at hs
  split at hs
  · rename_i hd
    obtain ⟨rfl, rfl⟩ := Option.some.inj hs
    subst hd
    exact this
  · exact absurd hs (by simp)

/-- The factors of `x` through the `MUL`s of the list, at most `fuel` deep. -/
def monoOf (atoms : List Atom) : ℕ → V → List V
  | 0, v => [v]
  | fuel + 1, v => match mulOf atoms v with
    | some (p, q) => monoOf atoms fuel p ++ monoOf atoms fuel q
    | none => [v]

theorem mono_sound {rd : Reader} {σ : Val} {atoms : List Atom} (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∀ (fuel : ℕ) (v : V), σ v = ((monoOf atoms fuel v).map σ).prod
  | 0, v => by simp [monoOf]
  | fuel + 1, v => by
    unfold monoOf
    split
    · rename_i p q h
      rw [mulOf_sound h hat, List.map_append, List.prod_append, ← mono_sound hat fuel p,
        ← mono_sound hat fuel q]
    · simp

/-- `x`'s factors are `base` and `e` times `y`. -/
def monoIs (atoms : List Atom) (x base y : V) (e : ℕ) : Bool :=
  (monoOf atoms 40 x).isPerm (base :: List.replicate e y)

theorem monoIs_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x base y : V} {e : ℕ}
    (h : monoIs atoms x base y e = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    σ x = σ base * σ y ^ e := by
  rw [mono_sound hat 40 x, (List.isPerm_iff.mp h).map σ |>.prod_eq]
  simp

/-- `x = p · g`, through a `MUL` by the constant `g`. -/
def genMulOk (atoms : List Atom) (x p : V) : Bool :=
  match mulOf atoms x with
  | some (a, b) => decide (a = p) && atoms.any (isConstAt b 2 0)
  | none => false

theorem genMul_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x p : V}
    (h : genMulOk atoms x p = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) : σ x = σ p * gen := by
  unfold genMulOk at h
  split at h
  · rename_i a b hab
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hc⟩ := h
    rw [mulOf_sound hab hat, const_sound hc hat, word_gen]
  · exact absurd h (by simp)

/-! ## Loop helpers -/

/-- **The shape of a `mul_range` helper `f`** (`__loopN`): parameters `.n 0` (the counter `x`),
`.n 1` (the end `N`), …; its body atoms, then `callIf (x·g + N) f [x·g, the other parameters]`. -/
def loopShape (fn : Fn) (f : String) : Bool :=
  decide (2 ≤ fn.params.length) && decide (fn.params = (List.range fn.params.length).map V.n) &&
  match splitLoop fn.body with
  | some (atoms, c, g, args) =>
    g == f && decide (args.length = fn.params.length) && decide (args.tail = fn.params.tail) &&
      genMulOk atoms (args.headD default) (V.n 0) &&
      (match addOf atoms c with
       | some (p, q) => genMulOk atoms p (V.n 0) && decide (q = V.n 1)
       | none => false)
  | none => false

/-- The atoms of a loop helper's body. -/
def loopAtoms (fn : Fn) : List Atom := ((splitLoop fn.body).map (·.1)).getD []

/-- **A run of a loop helper**: some valuation of its body's atoms with the counter `x` and the
other parameters `ps`, and, while `x·g ≠ N`, the run at `x·g`. -/
theorem loop_step {rd : Reader} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShape fn f = true) {x : E} {ps : List E} (h : coreProgram.Rel rd f (x :: ps) []) :
    ∃ σ : Val, σ (V.n 0) = x ∧ fn.params.tail.map σ = ps ∧ (∀ a ∈ loopAtoms fn, a.Holds rd σ) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []) := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem hf _ _).mp h
  simp only [loopShape, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h2, hpar⟩, hok⟩ := hok
  unfold loopAtoms
  split at hok
  · rename_i atoms c g args hsl
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨rfl, hlen⟩, htail⟩, hg⟩, hc⟩ := hok
    rw [splitLoop_eq hsl, holds_loopBody] at hb
    obtain ⟨hat, -, hcall⟩ := hb
    have hx0 : σ (V.n 0) = x := by
      have := congrArg List.head? hp
      rw [hpar] at this
      obtain ⟨k, hk⟩ : ∃ k, fn.params.length = k + 2 := ⟨fn.params.length - 2, by omega⟩
      rw [hk, List.range_succ_eq_map] at this
      simpa using this
    have hps : fn.params.tail.map σ = ps := by
      have := congrArg List.tail hp
      rwa [← List.map_tail] at this
    have hN : ps.headD 0 = σ (V.n 1) := by
      rw [← hps, hpar]
      obtain ⟨k, hk⟩ : ∃ k, fn.params.length = k + 2 := ⟨fn.params.length - 2, by omega⟩
      rw [hk, List.range_succ_eq_map, List.range_succ_eq_map]
      simp
    refine ⟨σ, hx0, hps, by simpa [hsl] using hat, fun hne => ?_⟩
    split at hc
    · rename_i p q hpq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hp', rfl⟩ := hc
      have hcv : σ c = x * gen + ps.headD 0 := by
        rw [addOf_sound hpq hat, genMul_sound hp' hat, hx0, hN]
      have := hcall (by rw [hcv]; exact hne)
      have hargs : args.map σ = x * gen :: ps := by
        obtain ⟨a0, rest, rfl⟩ : ∃ a0 rest, args = a0 :: rest := by
          cases args with
          | nil => simp at hlen; omega
          | cons a0 rest => exact ⟨a0, rest, rfl⟩
        simp only [List.headD_cons] at hg
        simp only [List.tail_cons] at htail
        rw [List.map_cons, genMul_sound hg hat, hx0, htail, hps]
      rwa [hargs] at this
    · exact absurd hc (by simp)
  · exact absurd hok (by simp)

/-! ## Flat blocks: atoms and calls -/

/-- A statement without control flow of its own: an atom or a call. -/
def Stmt.flat : Stmt → Bool
  | .atom _ | .call .. | .callIf .. | .dispatch .. => true
  | _ => false

theorem holds_flat_iff {C : CallRel} {rd : Reader} {σ : Val} {s : Stmt} (h : Stmt.flat s = true)
    (next : Prop) (kret : List E → Prop) :
    Stmt.Holds C rd σ s next kret ↔ Stmt.Holds C rd σ s True kret ∧ next := by
  cases s <;> simp_all [Stmt.flat, Stmt.Holds, and_assoc]

/-- **A flat block holds**: each statement does, then the continuation. -/
theorem holdsList_flat {C : CallRel} {rd : Reader} {σ : Val} :
    ∀ (ss : List Stmt), ss.all Stmt.flat = true → ∀ (next : Prop) (kret : List E → Prop),
      Stmt.HoldsList C rd σ ss next kret → (∀ s ∈ ss, Stmt.Holds C rd σ s True kret) ∧ next
  | [], _, _, _, h => ⟨by simp, h⟩
  | s :: ss, hf, next, kret, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    simp only [Stmt.HoldsList] at h
    rw [holds_flat_iff hf.1] at h
    obtain ⟨h0, hrest⟩ := h
    obtain ⟨h1, h2⟩ := holdsList_flat (C := C) (rd := rd) (σ := σ) ss hf.2 next kret hrest
    exact ⟨fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · exact h0
      · exact h1 t ht, h2⟩

/-- The atoms of a block. -/
def atomsIn (ss : List Stmt) : List Atom := ss.filterMap fun s => match s with
  | .atom a => some a
  | _ => none

theorem atoms_of_flat {C : CallRel} {rd : Reader} {σ : Val} {ss : List Stmt} {kret : List E → Prop}
    (h : ∀ s ∈ ss, Stmt.Holds C rd σ s True kret) : ∀ a ∈ atomsIn ss, a.Holds rd σ := by
  intro a ha
  obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp ha
  cases s <;> simp only [reduceCtorEq, Option.some.injEq] at hsa
  subst hsa
  exact (h _ hs).1

theorem call_of_flat {C : CallRel} {rd : Reader} {σ : Val} {ss : List Stmt} {kret : List E → Prop}
    (h : ∀ s ∈ ss, Stmt.Holds C rd σ s True kret) {f : String} {args rets : List V}
    (hm : ss.any (stmtEqb · (.call f args rets)) = true) : C f (args.map σ) (rets.map σ) := by
  obtain ⟨s, hs, he⟩ := List.any_eq_true.mp hm
  rw [stmtEqb_sound he] at hs
  exact (h _ hs).1

theorem callIf_of_flat {C : CallRel} {rd : Reader} {σ : Val} {ss : List Stmt} {kret : List E → Prop}
    (h : ∀ s ∈ ss, Stmt.Holds C rd σ s True kret) {c : V} {f : String} {args : List V}
    (hm : ss.any (stmtEqb · (.callIf c f args)) = true) :
    IsInK (σ c) ∧ (σ c ≠ 0 → C f (args.map σ) []) := by
  obtain ⟨s, hs, he⟩ := List.any_eq_true.mp hm
  rw [stmtEqb_sound he] at hs
  exact ⟨(h _ hs).1, (h _ hs).2.1⟩

theorem dispatch_of_flat {C : CallRel} {rd : Reader} {σ : Val} {ss : List Stmt}
    {kret : List E → Prop} (h : ∀ s ∈ ss, Stmt.Holds C rd σ s True kret) {x : V}
    {fs : List String} {args rets : List V}
    (hm : ss.any (stmtEqb · (.dispatch x fs args rets)) = true) :
    ∃ (j : ℕ) (hj : j < fs.length), σ x = ofK (Parameters.addressOfIndex j) ∧
      C fs[j] (args.map σ) (rets.map σ) := by
  obtain ⟨s, hs, he⟩ := List.any_eq_true.mp hm
  rw [stmtEqb_sound he] at hs
  exact (h _ hs).1

/-! ## Chains between states in memory -/

theorem initCell_of_loads {rd : Reader} {σ : Val} {atoms : List Atom} {s : ChainSpec} {st : List V}
    {sp : V} (hinit : s.init = some st) (hst : stLoadsOk atoms sp st 0 = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) {S : KeccakState} (hS : StateAt rd (σ sp) 0 S) (c : Fin 13) :
    s.initCell σ c = cellsOfState S false c := by
  rw [ChainSpec.initCell, hinit]
  have h1 := stLoads_sound hst hat c
  have h2 := hS c
  exact loadHolds_unique h1 h2

/-- **A `final=0` chain from a state in memory to a state in memory**, over cells read from
memory. -/
theorem chain_whole_mem {rd : Reader} {σ : Val} {atoms : List Atom} {s : ChainSpec} {st : List V}
    {sp mp op : V} {oo : ℕ} (hc : s.check atoms = true) (hfin : s.final = false)
    (hinit : s.init = some st) (hst : stLoadsOk atoms sp st 0 = true)
    (hmsg : loadsOk atoms mp s.msg = true)
    (hout : stLoadsOk atoms op ((List.range 13).map (s.outV (s.nb - 1))) oo = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) {n : ℕ} {pre : List UInt8} (hpre : pre.length = rate * n)
    (hS : StateAt rd (σ sp) 0 (absorbChunks n zeroState pre)) :
    ReadsAt rd (σ mp) (s.vals σ) ∧
      StateAt rd (σ op) oo (absorbChunks (n + s.nb) zeroState (pre ++ cellsBytes (s.vals σ))) ∧
      (pre ++ cellsBytes (s.vals σ)).length = rate * (n + s.nb) := by
  obtain ⟨hw, hl⟩ := chain_whole hc hfin hat hpre (initCell_of_loads hinit hst hat hS)
  refine ⟨loads_sound hmsg hat, fun c => ?_, hl⟩
  have := stLoads_sound hout hat c
  rw [← hw c]
  simpa [List.getD_eq_getElem?_getD, c.isLt] using this

/-- **A padded chain from a state in memory**, over cells read from memory, returning the digest. -/
theorem chain_final_mem {rd : Reader} {σ : Val} {atoms : List Atom} {s : ChainSpec} {st : List V}
    {sp mp : V} {r0 r1 : V} (hc : s.check atoms = true) (hfin : s.final = true)
    (hinit : s.init = some st) (hst : stLoadsOk atoms sp st 0 = true)
    (hmsg : loadsOk atoms mp s.msg = true) (hr : retOk atoms s r0 r1 = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) {n : ℕ} {pre : List UInt8} (hpre : pre.length = rate * n)
    (hS : StateAt rd (σ sp) 0 (absorbChunks n zeroState pre)) :
    ReadsAt rd (σ mp) (s.vals σ) ∧
      [σ r0, σ r1] = digestCells (keccak256 (pre ++ cellsBytes ((s.vals σ).take (s.len / 16)))) := by
  have hd := chain_final hc hfin hat hpre (initCell_of_loads hinit hst hat hS)
  simp only [retOk, Bool.and_eq_true] at hr
  refine ⟨loads_sound hmsg hat, ?_⟩
  rw [copy_sound hr.1 hat, copy_sound hr.2 hat, digestCells, ← hd]

end
end LeanVM.Guest.B1.Digest
