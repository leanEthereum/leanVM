/-
  LeanVM.Protocol.EndToEnd.Front.WalkFaithful

  The deployed verifier's forward walk of the BLAKE2s circuit computes the left and right products
  of the R1CS of `blake2sFlockSpec`: `WalkFaithful blake2sFlockSpec`.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.FlockTerminal
public import LeanVM.Protocol.EndToEnd.Front.WalkFaithfulWords
public import LeanVM.Protocol.FlockSpec

/-!
# The forward walk is faithful

`walkFaithful_blake2sFlockSpec : WalkFaithful blake2sFlockSpec`: for every column-weight vector
`w` of the block's size, the deployed verifier's forward walk `blake2sRowValues w` (the
transcription in `Verifier.lean` of `blake2s_row_values`,
`python-verifier/verifier.py:1179-1288` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`)
returns, row by row, the left and right products `(A w, B w)` of the R1CS of `blake2sFlockSpec`,
that is of `blake2sCircuit.toBlockR1CS E`. With `terminalFaithful` this discharges the one
hypothesis of the lincheck terminal (`terminalFaithful_blake2sFlockSpec`).

The walk and the circuit agree on every row, with no deployment mismatch: the same 14720 product
gates at `1280 … 15999` with the same two forms each, the input rows `(w_j, 1)` at `0 … 255` and
`640 … 1279`, the output rows `(out bit, 1)` at `256 … 511`, the constant row `(1, 1)` at `512`,
and zero rows elsewhere.

The proof follows the walk as the builder runs (`WalkFaithfulWords.lean`):

* `blake2sWalk_eq`: the walk with its round body named (`walkRound`, `walkGate`), by `rfl`.
* `sim_walkGate`, `sim_walkRound`, `sim_rounds`, `sim_compressW`: the walk's ten rounds write the
  rows of the gates `compressW` records, and leave the value words of its working vector
  (`stateVal`).
* `run_walk`: the whole walk writes, in order, the input rows, the compression's gates, the output
  rows and the constant row (`writeRows`).
* `writeRows_getD`: with distinct positions, the row written at `k` is that of the one gate at
  `k`; `walk_rows` reads `rowOf k` off it, position by position.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.ProductCircuit
open LeanVM.Protocol.Blake2sCircuit

@[expose] public section

namespace WalkSim

/-! ## The walk, structured -/

/-- One mixing step of the walk (`verifier.py:1263-1283`), its gate positions from
`1280 + 184 (8 round + gate)`. -/
def walkGate (cw : Array E) (roundIndex : ℕ) (x : (ℕ × ℕ × ℕ × ℕ) × ℕ)
    (state : Array (Array E)) : RowM (ForInStep (Array (Array E))) :=
  match x with
  | ((laneA, laneB, laneC, laneD), gateIndex) =>
    let gate := roundIndex * 8 + gateIndex
    let gateBase := 1280 + 184 * gate
    let a := state.getD laneA #[]
    let b := state.getD laneB #[]
    let c := state.getD laneC #[]
    let d := state.getD laneD #[]
    let mx := slotsW cw (640 + 32 * blake2sSigma roundIndex (2 * gateIndex))
    let my := slotsW cw (640 + 32 * blake2sSigma roundIndex (2 * gateIndex + 1))
    do
    let a1 ← add3W cw a b mx gateBase
    let d1 := rotateRightW (xorW d a1) 16
    let c1 ← Verifier.addW cw c d1 (gateBase + 61)
    let b1 := rotateRightW (xorW b c1) 12
    let a2 ← add3W cw a1 b1 my (gateBase + 92)
    let d2 := rotateRightW (xorW d1 a2) 8
    let c2 ← Verifier.addW cw c1 d2 (gateBase + 153)
    let b2 := rotateRightW (xorW b1 c2) 7
    pure (ForInStep.yield ((((state.set! laneA a2).set! laneB b2).set! laneC c2).set! laneD d2))

/-- One round of the walk: the eight mixing steps. -/
def walkRound (cw : Array E) (roundIndex : ℕ) (state : Array (Array E)) :
    RowM (ForInStep (Array (Array E))) := do
  let state ← forIn blake2sGLanes.zipIdx state (walkGate cw roundIndex)
  pure (ForInStep.yield state)

/-- `blake2sWalk` with its round loop's body named: definitionally the same program. -/
theorem blake2sWalk_eq (cw : Array E) : blake2sWalk cw = (do
    let constant := weightAt cw blake2sConstantColumn
    for (base, length) in [(0, 256), (640, 512), (1152, 128)] do
      for row in List.range length do
        setRow (base + row) (weightAt cw (base + row)) constant
    let mut state : Array (Array E) := Array.replicate 16 (Array.replicate 32 0)
    for word in List.range 8 do
      state := state.set! word (slotsW cw (32 * word))
    for word in List.range 4 do
      state := state.set! (8 + word) (literalW cw (blake2sIv word))
    for (word, base) in [(0, 1152), (1, 1184), (2, 1216), (3, 1248)] do
      state := state.set! (12 + word)
        (xorW (literalW cw (blake2sIv (4 + word))) (slotsW cw base))
    state ← forIn (List.range 10) state (walkRound cw)
    for word in List.range 8 do
      let out :=
        xorW (xorW (state.getD word #[]) (state.getD (word + 8) #[])) (slotsW cw (32 * word))
      linearRows cw out (256 + 32 * word)
    setRow blake2sConstantColumn constant constant) := rfl

/-! ## Simulation combinators -/

section Combinators

variable {k₀ : ℕ}

theorem sim_at {α β : Type} {cw : Array E} {n n' k : ℕ} {mb : Builder k₀ α} {mw : RowM β}
    {R : α → β → Prop} (h : Sim cw n k mb mw R) (e : n = n') : Sim cw n' k mb mw R := e ▸ h

theorem sim_forIn_cons {α γ β δ : Type} {cw : Array E} {n k₁ k₂ : ℕ} {mb : Builder k₀ α}
    {h : α → Builder k₀ γ} {f : δ → β → RowM (ForInStep β)} {a : δ} {l : List δ} {b : β}
    {g : α → β} {Q : γ → β → Prop}
    (h1 : Sim cw n k₁ mb (f a b) (fun x r ↦ r = ForInStep.yield (g x)))
    (h2 : ∀ x, Sim cw (n + k₁) k₂ (h x) (forIn l (g x) f) Q) :
    Sim cw n (k₁ + k₂) (mb >>= h) (forIn (a :: l) b f) Q := by
  rw [List.forIn_cons]
  refine sim_bind h1 fun x r hr ↦ ?_
  subst hr
  exact h2 x

theorem sim_forIn_last {α β δ : Type} {cw : Array E} {n k : ℕ} {mb : Builder k₀ α}
    {f : δ → β → RowM (ForInStep β)} {a : δ} {b : β} {g : α → β}
    (h1 : Sim cw n k mb (f a b) (fun x r ↦ r = ForInStep.yield (g x))) :
    Sim cw n k mb (forIn [a] b f) (fun x st ↦ st = g x) := by
  intro hle σ hσ s
  obtain ⟨new, h1', h2', h3', h4'⟩ := h1 hle σ hσ s
  have e : (f a b).run s = (ForInStep.yield (g (mb.run σ).1), ((f a b).run s).2) :=
    Prod.ext h4' rfl
  refine ⟨new, h1', h2', ?_, ?_⟩
  · rw [run_forIn_cons, e]; exact h3'
  · rw [run_forIn_cons, e]; rfl

theorem sim_map_walk {α β γ : Type} {cw : Array E} {n k : ℕ} {mb : Builder k₀ α} {mw : RowM β}
    {R : α → β → Prop} {Q : α → γ → Prop} {g : β → γ} (h : Sim cw n k mb mw R)
    (hQ : ∀ a b, R a b → Q a (g b)) : Sim cw n k mb (mw >>= fun b ↦ pure (g b)) Q := by
  intro hle σ hσ s
  obtain ⟨new, h1, h2, h3, h4⟩ := h hle σ hσ s
  exact ⟨new, h1, h2, h3, hQ _ _ h4⟩

theorem sim_map_builder {α β γ : Type} {cw : Array E} {n k : ℕ} {mb : Builder k₀ α} {mw : RowM β}
    {R : α → β → Prop} {Q : γ → β → Prop} {g : α → γ} (h : Sim cw n k mb mw R)
    (hQ : ∀ a b, R a b → Q (g a) b) : Sim cw n k (mb >>= fun a ↦ pure (g a)) mw Q := by
  intro hle σ hσ s
  obtain ⟨new, h1, h2, h3, h4⟩ := h hle σ hσ s
  exact ⟨new, h1, h2, h3, hQ _ _ h4⟩

end Combinators

theorem two_pow_m : 2 ^ m = 16384 := rfl

/-! ## The working vector -/

/-- The walk's working vector: the value words of the builder's sixteen words. -/
def stateVal (cw : Array E) (v : Vector (Word m) 16) : Array (Array E) :=
  Array.ofFn fun j : Fin 16 ↦ wordVal cw v[j]

theorem getD_stateVal (cw : Array E) (v : Vector (Word m) 16) (j : Fin 16) :
    (stateVal cw v).getD j #[] = wordVal cw v[j] := by
  simp [stateVal, Array.getD_eq_getD_getElem?]

theorem set_stateVal (cw : Array E) (v : Vector (Word m) 16) (j : Fin 16) (x : Word m) :
    (stateVal cw v).set! j (wordVal cw x) = stateVal cw (v.set j x) := by
  apply Array.ext
  · simp [stateVal]
  · intro i h1 h2
    simp only [stateVal, Array.size_ofFn] at h2
    simp only [stateVal, Array.set!]
    rw [Array.getElem_setIfInBounds (by simp only [Array.size_ofFn]; omega)]
    simp only [Array.getElem_ofFn, Fin.getElem_fin, Vector.getElem_set]
    split_ifs <;> rfl

/-! ## One mixing step -/

/-- **One mixing step**: the walk's step writes the builder's `184` gates of `gW` from
`1280 + 184 (8 r + g)` and leaves the value words of the builder's working vector. -/
theorem sim_walkGate (cw : Array E) (r gi : ℕ) (v : Vector (Word m) 16) (a b c d : Fin 16)
    (mx my : Word m) (hmx : slotsW cw (640 + 32 * blake2sSigma r (2 * gi)) = wordVal cw mx)
    (hmy : slotsW cw (640 + 32 * blake2sSigma r (2 * gi + 1)) = wordVal cw my) :
    Sim cw (1280 + 184 * (r * 8 + gi)) 184 (gW v a b c d mx my)
      (walkGate cw r ((a.val, b.val, c.val, d.val), gi) (stateVal cw v))
      (fun v' res ↦ res = ForInStep.yield (stateVal cw v')) := by
  unfold walkGate gW
  dsimp only
  rw [getD_stateVal, getD_stateVal, getD_stateVal, getD_stateVal, hmx, hmy]
  refine sim_cast (k := 61 + (31 + (61 + (31 + 0)))) ?_ rfl
  refine sim_bind (sim_add3W cw _ _ _ _) fun a1 a1' h ↦ ?_
  subst h
  rw [xorW_wordVal, rotateRightW_wordVal]
  refine sim_bind (sim_addW cw _ _ _) fun c1 c1' h ↦ ?_
  subst h
  rw [xorW_wordVal, rotateRightW_wordVal]
  refine sim_bind (sim_at (sim_add3W cw _ _ _ _) (by omega)) fun a2 a2' h ↦ ?_
  subst h
  rw [xorW_wordVal, rotateRightW_wordVal]
  refine sim_bind (sim_at (sim_addW cw _ _ _) (by omega)) fun c2 c2' h ↦ ?_
  subst h
  rw [xorW_wordVal, rotateRightW_wordVal]
  refine sim_pure ?_
  rw [set_stateVal, set_stateVal, set_stateVal, set_stateVal]


/-! ## Rounds -/

/-- The builder's message words. -/
def msgV : Vector (Word m) 16 := Vector.ofFn fun w ↦ msgW w

theorem slotsW_msg (cw : Array E) (r : ℕ) (s : Vector (Fin 16) 16)
    (hs : ∀ p (hp : p < 16), blake2sSigma r p = (s[p]).val) (p : ℕ) (hp : p < 16) :
    slotsW cw (640 + 32 * blake2sSigma r p) = wordVal cw msgV[s[p]] := by
  rw [hs p hp, msgV, Fin.getElem_fin, Vector.getElem_ofFn, msgW]
  exact slotsW_wordVal cw (by rw [two_pow_m]; have := (s[p]).isLt; omega)

theorem zipIdx_lanes : blake2sGLanes.zipIdx =
    [((0, 4, 8, 12), 0), ((1, 5, 9, 13), 1), ((2, 6, 10, 14), 2), ((3, 7, 11, 15), 3),
      ((0, 5, 10, 15), 4), ((1, 6, 11, 12), 5), ((2, 7, 8, 13), 6), ((3, 4, 9, 14), 7)] := rfl

/-- **One round**: the walk's round writes the builder's `1472` gates of `roundW` from
`1280 + 1472 r`. -/
theorem sim_walkRound (cw : Array E) (r : ℕ) (s : Vector (Fin 16) 16)
    (hs : ∀ p (hp : p < 16), blake2sSigma r p = (s[p]).val) (v : Vector (Word m) 16) :
    Sim cw (1280 + 1472 * r) 1472 (roundW v msgV s) (walkRound cw r (stateVal cw v))
      (fun v' res ↦ res = ForInStep.yield (stateVal cw v')) := by
  have hm := slotsW_msg cw r s hs
  unfold walkRound roundW
  rw [zipIdx_lanes]
  refine sim_map_walk (R := fun v' st ↦ st = stateVal cw v') ?_
    fun _ _ h ↦ congrArg ForInStep.yield h
  refine sim_cast (k := 184 + (184 + (184 + (184 + (184 + (184 + (184 + 184))))))) ?_ (by norm_num)
  refine sim_forIn_cons (sim_at (sim_walkGate cw r 0 v 0 4 8 12 _ _ (hm (2 * 0) (by decide))
    (hm (2 * 0 + 1) (by decide))) (by omega)) fun v ↦ ?_
  refine sim_forIn_cons (sim_at (sim_walkGate cw r 1 v 1 5 9 13 _ _ (hm (2 * 1) (by decide))
    (hm (2 * 1 + 1) (by decide))) (by omega)) fun v ↦ ?_
  refine sim_forIn_cons (sim_at (sim_walkGate cw r 2 v 2 6 10 14 _ _ (hm (2 * 2) (by decide))
    (hm (2 * 2 + 1) (by decide))) (by omega)) fun v ↦ ?_
  refine sim_forIn_cons (sim_at (sim_walkGate cw r 3 v 3 7 11 15 _ _ (hm (2 * 3) (by decide))
    (hm (2 * 3 + 1) (by decide))) (by omega)) fun v ↦ ?_
  refine sim_forIn_cons (sim_at (sim_walkGate cw r 4 v 0 5 10 15 _ _ (hm (2 * 4) (by decide))
    (hm (2 * 4 + 1) (by decide))) (by omega)) fun v ↦ ?_
  refine sim_forIn_cons (sim_at (sim_walkGate cw r 5 v 1 6 11 12 _ _ (hm (2 * 5) (by decide))
    (hm (2 * 5 + 1) (by decide))) (by omega)) fun v ↦ ?_
  refine sim_forIn_cons (sim_at (sim_walkGate cw r 6 v 2 7 8 13 _ _ (hm (2 * 6) (by decide))
    (hm (2 * 6 + 1) (by decide))) (by omega)) fun v ↦ ?_
  exact sim_forIn_last (sim_at (sim_walkGate cw r 7 v 3 4 9 14 _ _ (hm (2 * 7) (by decide))
    (hm (2 * 7 + 1) (by decide))) (by omega))


theorem blake2sSigma_toList (r : ℕ) (hr : r < sigma.toList.length) (p : ℕ) (hp : p < 16) :
    blake2sSigma r p = ((sigma.toList[r])[p]).val := by
  simp [blake2sSigma, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, hp]

/-- **The rounds**: from round `r`, the walk's remaining rounds write the builder's gates. -/
theorem sim_rounds (cw : Array E) : ∀ k r (v : Vector (Word m) 16), r + k = 10 →
    Sim cw (1280 + 1472 * r) (1472 * k)
      ((sigma.toList.drop r).foldlM (fun v s ↦ roundW v msgV s) v)
      (forIn (List.range' r k) (stateVal cw v) (walkRound cw))
      (fun v' st ↦ st = stateVal cw v') := by
  intro k
  induction k with
  | zero =>
    intro r v h
    have hnil : sigma.toList.drop r = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [hnil, List.foldlM_nil, List.range'_zero, List.forIn_nil]
    exact sim_pure rfl
  | succ k ih =>
    intro r v h
    have hr : r < sigma.toList.length := by simp; omega
    rw [List.drop_eq_getElem_cons hr, List.foldlM_cons, List.range'_succ]
    refine sim_cast (k := 1472 + 1472 * k) ?_ (by ring)
    exact sim_forIn_cons (sim_walkRound cw r _ (blake2sSigma_toList r hr) v)
      fun v' ↦ sim_at (ih (r + 1) v' (by omega)) (by ring)

/-- The output words of the builder's working vector. -/
def outsOf (v : Vector (Word m) 16) : Vector (Word m) 8 :=
  Vector.ofFn fun w : Fin 8 ↦ ProductCircuit.xorW (ProductCircuit.xorW v[w] v[w.val + 8]) (cvW w)

/-- **The compression's gates**: the walk's ten rounds write the gates `compressW` records from
`1280`, and leave the working vector whose output words `compressW` returns. -/
theorem sim_compressW (cw : Array E) :
    Sim cw 1280 14720 compressW (forIn (List.range 10) (stateVal cw initW) (walkRound cw))
      (fun outs st ↦ ∃ v, st = stateVal cw v ∧ outs = outsOf v) := by
  unfold compressW
  dsimp only
  rw [← Vector.foldlM_toList]
  refine sim_map_builder (R := fun v' st ↦ st = stateVal cw v') ?_ fun v st h ↦ ⟨v, h, rfl⟩
  have := sim_rounds cw 10 0 initW rfl
  rw [List.drop_zero, ← List.range_eq_range'] at this
  exact this


/-! ## The whole walk -/

/-- A loop whose body always yields runs as a fold of its steps. -/
theorem run_pure_rowM {α : Type} (a : α) (s : Array E × Array E) :
    (pure a : RowM α).run s = (a, s) := rfl

theorem run_forIn_unit {α : Type} (l : List α) (f : α → PUnit → RowM (ForInStep PUnit))
    (s : Array E × Array E)
    (hf : ∀ a s, ((f a PUnit.unit).run s).1 = ForInStep.yield PUnit.unit) :
    (forIn l PUnit.unit f).run s =
      (PUnit.unit, l.foldl (fun s a ↦ ((f a PUnit.unit).run s).2) s) := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    have e : (f a PUnit.unit).run s = (ForInStep.yield PUnit.unit, ((f a PUnit.unit).run s).2) :=
      Prod.ext (hf a s) rfl
    rw [run_forIn_cons, e]
    exact ih _

/-- The input positions the walk writes, in its order. -/
def inPositions : List ℕ :=
  (List.range 256).map (0 + ·) ++ (List.range 512).map (640 + ·) ++ (List.range 128).map (1152 + ·)

/-- The row of an input position: `(z_j, 1)`. -/
def inRow (j : ℕ) : Pos m × Gate m := (pos j, ⟨Form.var (pos j), Form.var Flock.constPos⟩)

/-- The row of the constant: `(1, 1)`. -/
def constRow : Pos m × Gate m :=
  (Flock.constPos, ⟨Form.var Flock.constPos, Form.var Flock.constPos⟩)

/-- A fold over `List.range n` is a fold over `List.finRange n`. -/
theorem foldl_range_eq_finRange {β : Type} (n : ℕ) (f : β → ℕ → β) (b : β) :
    (List.range n).foldl f b = (List.finRange n).foldl (fun b i ↦ f b i.val) b := by
  rw [← List.map_coe_finRange_eq_range, List.foldl_map]

/-- The input rows: the walk's first loops write `(cw[j], cw[512])` at every input position. -/
theorem inputs_fold (cw : Array E) (s0 : Array E × Array E)
    {g : ℕ × ℕ → Array E × Array E → Array E × Array E}
    (hg : ∀ b n s, g (b, n) s = (List.range n).foldl (fun s row ↦
      (s.1.set! (b + row) (weightAt cw (b + row)),
        s.2.set! (b + row) (weightAt cw blake2sConstantColumn))) s) :
    List.foldl (fun s a ↦ g a s) s0 [(0, 256), (640, 512), (1152, 128)] =
      writeRows cw s0 (inPositions.map inRow) := by
  have key : ∀ b n s, b + n ≤ 2 ^ m →
      g (b, n) s = writeRows cw s (((List.range n).map (b + ·)).map inRow) := by
    intro b n s hbn
    rw [hg, writeRows, List.foldl_map, List.foldl_map]
    refine List.foldl_ext _ _ _ fun s row hrow ↦ ?_
    rw [List.mem_range] at hrow
    rw [inRow, writeRow_pos cw s (by omega), formVal_var, formVal_var, pos_val (by omega)]
    rfl
  simp only [List.foldl_cons, List.foldl_nil, inPositions, List.map_append, writeRows_append]
  rw [key _ _ _ (by rw [two_pow_m]; norm_num), key _ _ _ (by rw [two_pow_m]; norm_num),
    key _ _ _ (by rw [two_pow_m]; norm_num)]

/-- The initial working vector: the walk's three pure loops build the value words of `initW`. -/
theorem init_fold (cw : Array E) {f₁ f₂ : Array (Array E) → ℕ → Array (Array E)}
    {f₃ : Array (Array E) → ℕ × ℕ → Array (Array E)}
    (h₁ : ∀ st word, f₁ st word = st.set! word (slotsW cw (32 * word)))
    (h₂ : ∀ st word, f₂ st word = st.set! (8 + word) (literalW cw (blake2sIv word)))
    (h₃ : ∀ st x, f₃ st x =
      st.set! (12 + x.1) (Verifier.xorW (literalW cw (blake2sIv (4 + x.1))) (slotsW cw x.2))) :
    List.foldl f₃ (List.foldl f₂ (List.foldl f₁ (Array.replicate 16 (Array.replicate 32 0))
      (List.range 8)) (List.range 4)) [(0, 1152), (1, 1184), (2, 1216), (3, 1248)] =
      stateVal cw initW := by
  obtain rfl : f₁ = _ := funext₂ h₁
  obtain rfl : f₂ = _ := funext₂ h₂
  obtain rfl : f₃ = _ := funext₂ h₃
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  have hs : ∀ k (hk : k < 8), slotsW cw (32 * k) = wordVal cw initW[k] := fun k hk ↦ by
    rw [slotsW_wordVal cw (by rw [two_pow_m]; omega)]
    simp [initW, cvW, hk]
  have hiv : ∀ k (hk : k < 8), blake2sIv k = iv[k].toNat := fun k hk ↦ by
    simp [blake2sIv, hk]
  have hl : ∀ k (hk : k < 4), literalW cw (blake2sIv k) = wordVal cw initW[8 + k] := fun k hk ↦ by
    rw [hiv k (by omega), literalW_wordVal cw (cpos := Flock.constPos) rfl]
    simp [initW, show 8 + k < 12 by omega]
  have hx : ∀ k (hk : k < 4), Verifier.xorW (literalW cw (blake2sIv (4 + k)))
      (slotsW cw (1152 + 32 * k)) = wordVal cw initW[12 + k] := fun k hk ↦ by
    rw [hiv _ (by omega), literalW_wordVal cw (cpos := Flock.constPos) rfl,
      slotsW_wordVal cw (by rw [two_pow_m]; omega), xorW_wordVal]
    simp [initW, show 4 + k = 12 + k - 8 by omega, show ¬ 12 + k < 8 by omega, counterLo]
  rw [hs 0 (by decide), hs 1 (by decide), hs 2 (by decide), hs 3 (by decide), hs 4 (by decide),
    hs 5 (by decide), hs 6 (by decide), hs 7 (by decide), hl 0 (by decide), hl 1 (by decide),
    hl 2 (by decide), hl 3 (by decide), show (1152 : ℕ) = 1152 + 32 * 0 from rfl,
    show (1184 : ℕ) = 1152 + 32 * 1 from rfl, show (1216 : ℕ) = 1152 + 32 * 2 from rfl,
    show (1248 : ℕ) = 1152 + 32 * 3 from rfl, hx 0 (by decide), hx 1 (by decide),
    hx 2 (by decide), hx 3 (by decide)]
  apply Array.ext
  · simp [stateVal]
  · intro i h1 h2
    simp only [stateVal, Array.size_ofFn] at h2
    simp only [stateVal, Array.getElem_ofFn, Array.set!]
    interval_cases i <;> simp

theorem getD_stateVal' (cw : Array E) (v : Vector (Word m) 16) (j : ℕ) (hj : j < 16) :
    (stateVal cw v).getD j #[] = wordVal cw v[j] := getD_stateVal cw v ⟨j, hj⟩

theorem run_linearRows (cw vals : Array E) (base : ℕ) (s : Array E × Array E) :
    ((linearRows cw vals base).run s).2 = (List.range 32).foldl (fun s bit ↦
      (s.1.set! (base + bit) (vals.getD bit 0),
        s.2.set! (base + bit) (weightAt cw blake2sConstantColumn))) s := by
  unfold linearRows
  rw [run_bind_rowM, run_forIn_unit _ _ _ (fun _ _ ↦ rfl)]
  rfl

/-- The output rows: the walk's last loop writes `(out bit, cw[512])` at every output
position. -/
theorem outputs_fold (cw : Array E) (v : Vector (Word m) 16) (s : Array E × Array E)
    {g : ℕ → Array E × Array E → Array E × Array E}
    (hg : ∀ word s, g word s = ((linearRows cw (Verifier.xorW (Verifier.xorW
      ((stateVal cw v).getD word #[]) ((stateVal cw v).getD (word + 8) #[]))
      (slotsW cw (32 * word))) (256 + 32 * word)).run s).2) :
    List.foldl (fun s a ↦ g a s) s (List.range 8) = writeRows cw s (outRows (outsOf v)) := by
  rw [foldl_range_eq_finRange, outRows, writeRows, List.foldl_flatMap]
  refine List.foldl_ext _ _ _ fun s w _ ↦ ?_
  have hw := w.isLt
  rw [hg, getD_stateVal' cw v _ (by omega), getD_stateVal' cw v _ (by omega),
    slotsW_wordVal cw (by rw [two_pow_m]; omega), xorW_wordVal, xorW_wordVal, run_linearRows,
    foldl_range_eq_finRange, List.foldl_map]
  refine List.foldl_ext _ _ _ fun s i _ ↦ ?_
  have hi := i.isLt
  rw [writeRow_pos cw s (by rw [two_pow_m]; omega), getD_wordVal cw _ hi, formVal_var]
  simp [outsOf, cvW]
  rfl

theorem run_walk (cw : Array E) (s0 : Array E × Array E) :
    ((blake2sWalk cw).run s0).2 = writeRows cw s0 (inPositions.map inRow ++
      (compressW.run ⟨gateBase, #[]⟩).2.gates.toList ++
      outRows (compressW.run ⟨gateBase, #[]⟩).1 ++ [constRow]) := by
  rw [blake2sWalk_eq, run_bind_rowM, run_forIn_unit _ _ _ ?y, inputs_fold cw _ ?hg]
  case y =>
    intro a s
    rcases a with ⟨b, n⟩
    rfl
  case hg =>
    intro b n s
    dsimp only
    rw [run_bind_rowM, run_forIn_unit _ _ _ (fun _ _ ↦ rfl)]
    rfl
  dsimp only
  rw [run_bind_rowM]
  simp only [List.forIn_pure_yield_eq_foldl, pure_bind]
  rw [run_pure_rowM]
  dsimp only
  rw [init_fold cw (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)]
  obtain ⟨new, h1, -, h3, v, hv, houts⟩ := sim_compressW cw (by rw [two_pow_m]; norm_num)
    ⟨gateBase, #[]⟩ rfl (writeRows cw s0 (inPositions.map inRow))
  rw [run_bind_rowM, hv, h3, h1, houts, run_bind_rowM, run_forIn_unit _ _ _ ?y2,
    outputs_fold cw v _ ?hg2]
  case y2 => intro a s; rfl
  case hg2 => intro word s; rw [run_bind_rowM]; rfl
  rw [run_setRow]
  simp only [writeRows_append, Array.toList_append, List.nil_append]
  rw [writeRows_cons, writeRows_nil, writeRow]
  simp only [constRow, formVal_var]
  rfl

/-! ## Reading the rows back -/

theorem size_writeRows (cw : Array E) (s : Array E × Array E) (L : List (Pos m × Gate m)) :
    (writeRows cw s L).1.size = s.1.size ∧ (writeRows cw s L).2.size = s.2.size := by
  induction L generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons g L ih =>
    rw [writeRows_cons, (ih _).1, (ih _).2]
    simp [writeRow]

theorem getD_set! (a : Array E) (i j : ℕ) (v : E) (hj : j < a.size) :
    (a.set! i v).getD j 0 = if i = j then v else a.getD j 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds]
  split_ifs <;> simp_all

/-- With distinct positions, the walk's row at `k` is the value of the one gate written there, if
any. -/
theorem writeRows_getD (cw : Array E) (L : List (Pos m × Gate m)) (hnd : (L.map Prod.fst).Nodup)
    (s : Array E × Array E) (k : Pos m) (h1 : k.val < s.1.size) (h2 : k.val < s.2.size) :
    (writeRows cw s L).1.getD k 0 =
        (match L.lookup k with | some g => formVal cw g.a | none => s.1.getD k 0) ∧
      (writeRows cw s L).2.getD k 0 =
        (match L.lookup k with | some g => formVal cw g.b | none => s.2.getD k 0) := by
  induction L generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons pg L ih =>
    obtain ⟨p, g⟩ := pg
    rw [List.map_cons, List.nodup_cons] at hnd
    have hs1 : k.val < (writeRow cw s (p, g)).1.size := by simpa [writeRow] using h1
    have hs2 : k.val < (writeRow cw s (p, g)).2.size := by simpa [writeRow] using h2
    obtain ⟨ih1, ih2⟩ := ih hnd.2 _ hs1 hs2
    rw [writeRows_cons, List.lookup_cons]
    cases hl : L.lookup k with
    | some g' =>
      have hkp : (k == p) = false := by
        obtain ⟨l₁, l₂, hL, -⟩ := List.lookup_eq_some_iff.mp hl
        rw [beq_eq_false_iff_ne]
        rintro rfl
        exact hnd.1 (by rw [hL]; simp)
      rw [hl] at ih1 ih2
      simp only [hkp]
      exact ⟨ih1, ih2⟩
    | none =>
      rw [hl] at ih1 ih2
      rw [ih1, ih2]
      simp only [writeRow, getD_set! _ _ _ _ h1, getD_set! _ _ _ _ h2]
      by_cases hkp : k = p
      · subst hkp; simp
      · have : (k == p) = false := beq_eq_false_iff_ne.mpr hkp
        simp [this, show ¬ (p : ℕ) = k from fun h ↦ hkp (Fin.ext h).symm]

/-- The positions of an input-row list. -/
theorem lookup_inRows (l : List ℕ) (hl : ∀ j ∈ l, j < 2 ^ m) (k : Pos m) :
    (l.map inRow).lookup k =
      if (k : ℕ) ∈ l then some ⟨Form.var k, Form.var Flock.constPos⟩ else none := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, inRow, List.lookup_cons, ih fun i hi ↦ hl i (List.mem_cons_of_mem _ hi)]
    have hj := hl j List.mem_cons_self
    by_cases hkj : (k : ℕ) = j
    · have hk : k = pos j := Fin.ext (by rw [pos_val hj, hkj])
      subst hk
      simp [hkj]
    · have : (k == pos j) = false := beq_eq_false_iff_ne.mpr fun h ↦ hkj (by rw [h, pos_val hj])
      simp [this, hkj]

theorem keys_inRows : (inPositions.map inRow).map (fun g ↦ (g.1 : ℕ)) = inPositions := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id inPositions]
  refine List.map_congr_left fun j hj ↦ ?_
  have : j < 2 ^ m := by
    rw [two_pow_m]; simp only [inPositions, List.mem_append, List.mem_map, List.mem_range] at hj
    omega
  simp [inRow, pos_val this]

theorem flatMap_range' (b c n : ℕ) :
    (List.range n).flatMap (fun w ↦ List.range' (b + c * w) c) = List.range' b (c * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, List.range'_append_1,
      Nat.mul_succ]

theorem keys_outRows (outs : Vector (Word m) 8) :
    (outRows outs).map (fun g ↦ (g.1 : ℕ)) = List.range' 256 256 := by
  rw [outRows, List.map_flatMap]
  have inner : ∀ w ∈ List.finRange 8, List.map (fun g : Pos m × Gate m ↦ (g.1 : ℕ))
      ((List.finRange 32).map fun i ↦ ((pos (256 + 32 * w.val + i.val) : Pos m),
        (⟨outs[w][i], Form.var Flock.constPos⟩ : Gate m))) =
      List.range' (256 + 32 * w.val) 32 := by
    intro w _
    rw [List.range'_eq_map_range, ← List.map_coe_finRange_eq_range, List.map_map, List.map_map]
    refine List.map_congr_left fun i _ ↦ ?_
    have := w.isLt
    have := i.isLt
    simp [pos_val (show 256 + 32 * w.val + i.val < 2 ^ m by rw [two_pow_m]; omega)]
  rw [List.flatMap_congr inner,
    ← List.flatMap_map Fin.val (fun w ↦ List.range' (256 + 32 * w) 32),
    List.map_coe_finRange_eq_range, flatMap_range']


/-- The row of a position, read off a circuit's gate list, constant and inputs. -/
theorem rowOf_of_gates (c : ProductCircuit m) {L : List (Pos m × Gate m)} {cp : Pos m}
    {inp : Form m} (hL : c.gates.toList = L) (hcp : c.cpos = cp) (hinp : c.inputs = inp)
    (k : Pos m) :
    c.rowOf k = match L.lookup k with
      | some g => g
      | none =>
        if k = cp then ⟨Form.var cp, Form.var cp⟩
        else if inp.getLsbD k then ⟨Form.var k, Form.var cp⟩
        else ⟨0, 0⟩ := by
  subst hL hcp hinp
  unfold rowOf
  cases c.gates.toList.lookup k <;> rfl

theorem mem_keys_of_lookup {L : List (Pos m × Gate m)} {k : Pos m} {g : Gate m}
    (h : L.lookup k = some g) : (k : ℕ) ∈ L.map (fun g ↦ (g.1 : ℕ)) := by
  obtain ⟨l₁, l₂, hL, -⟩ := List.lookup_eq_some_iff.mp h
  rw [hL]
  simp

/-- **The walk's rows, position by position**: the walk's left and right values at position `k`
are the values of the left and right forms of `rowOf k` of the circuit. -/
theorem walk_rows (w : List E) (k : Pos m) :
    (blake2sRowValues w).1.getD k 0 = formVal w.toArray (blake2sCircuit.rowOf k).a ∧
      (blake2sRowValues w).2.getD k 0 = formVal w.toArray (blake2sCircuit.rowOf k).b := by
  obtain ⟨new, h1, h2, -, -⟩ := sim_compressW w.toArray (by rw [two_pow_m]; norm_num)
    ⟨gateBase, #[]⟩ rfl (#[], #[])
  have hG : (compressW.run ⟨gateBase, #[]⟩).2.gates.toList = new := by rw [h1]; simp
  have hgates : blake2sCircuit.gates.toList = new ++ outRows (compressW.run ⟨gateBase, #[]⟩).1 := by
    rw [blake2sCircuit_gates, Array.toList_append, hG]
  have hrow : blake2sRowValues w = ((blake2sWalk w.toArray).run
      (Array.replicate (2 ^ blake2sR1csLogSize) 0, Array.replicate (2 ^ blake2sR1csLogSize) 0)).2 :=
    rfl
  rw [hrow, run_walk, hG]
  generalize (compressW.run ⟨gateBase, #[]⟩).1 = outs at hgates ⊢
  have hk : (k : ℕ) < 16384 := k.isLt
  have hpos : inPositions = List.range' 0 256 ++ List.range' 640 512 ++ List.range' 1152 128 := by
    simp only [inPositions, List.range'_eq_map_range]
  have hmemIn' : ∀ j, j ∈ inPositions ↔ j < 256 ∨ 640 ≤ j ∧ j < 1280 := by
    intro j
    simp only [hpos, List.mem_append, List.mem_range'_1]
    omega
  have hmemIn := hmemIn' k
  have hinB : ∀ j ∈ inPositions, j < 2 ^ m := by
    intro j hj
    rw [two_pow_m]
    rw [hmemIn'] at hj
    omega
  have hnd : ((inPositions.map inRow ++ new ++ outRows outs ++ [constRow]).map Prod.fst).Nodup := by
    apply List.Nodup.of_map Fin.val
    rw [List.map_map, show (Fin.val ∘ Prod.fst : Pos m × Gate m → ℕ) = fun g ↦ (g.1 : ℕ) from rfl]
    simp only [List.map_append, keys_inRows, h2, keys_outRows]
    have hnin : inPositions.Nodup := by
      rw [hpos]
      simp only [List.nodup_append, List.mem_append, List.mem_range'_1]
      refine ⟨⟨List.nodup_range' _, List.nodup_range' _, ?_⟩, List.nodup_range' _, ?_⟩ <;>
        intros <;> omega
    have hc : ((constRow : Pos m × Gate m).1 : ℕ) = 512 := rfl
    simp only [List.nodup_append, hnin, List.mem_append, List.mem_range'_1,
      hmemIn', List.map_cons, List.map_nil, List.mem_singleton, List.nodup_cons, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_self, true_and, hc]
    refine ⟨⟨⟨List.nodup_range' _, ?_⟩, List.nodup_range' _, ?_⟩, ?_⟩ <;> intros <;> omega
  obtain ⟨e1, e2⟩ := writeRows_getD w.toArray _ hnd
    (Array.replicate (2 ^ blake2sR1csLogSize) 0, Array.replicate (2 ^ blake2sR1csLogSize) 0) k
    (by rw [Array.size_replicate]; exact hk) (by rw [Array.size_replicate]; exact hk)
  rw [e1, e2]
  have hzero : (Array.replicate (2 ^ blake2sR1csLogSize) (0 : E)).getD k 0 = 0 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  have hz1 : ((Array.replicate (2 ^ blake2sR1csLogSize) (0 : E),
      Array.replicate (2 ^ blake2sR1csLogSize) (0 : E)).1.getD k 0) = 0 := hzero
  simp only [hz1]
  rw [rowOf_of_gates blake2sCircuit hgates blake2sCircuit_cpos blake2sCircuit_inputs,
    getLsbD_inputs]
  simp only [List.lookup_append, Option.or_assoc, lookup_inRows _ hinB k]
  cases hN : new.lookup k with
  | some g =>
    have hm := mem_keys_of_lookup hN
    rw [h2, List.mem_range'_1] at hm
    have hnot : (k : ℕ) ∉ inPositions := by rw [hmemIn]; omega
    simp [hnot]
  | none =>
    cases hO : (outRows outs).lookup k with
    | some g =>
      have hm := mem_keys_of_lookup hO
      rw [keys_outRows, List.mem_range'_1] at hm
      have hnot : (k : ℕ) ∉ inPositions := by rw [hmemIn]; omega
      simp [hnot]
    | none =>
      simp only [Option.none_or, List.lookup_cons, List.lookup_nil, constRow]
      by_cases hkc : k = Flock.constPos
      · subst hkc
        have hnot : ((Flock.constPos : Pos m) : ℕ) ∉ inPositions := by
          rw [hmemIn']
          decide
        simp [hnot, formVal_var]
      · by_cases hki : (k : ℕ) ∈ inPositions
        · have hd := hmemIn.mp hki
          simp [hki, hkc, hd, formVal_var]
        · have hd : ¬ ((k : ℕ) < 256 ∨ 640 ≤ (k : ℕ) ∧ (k : ℕ) < 1280) := fun h ↦ hki (hmemIn.mpr h)
          have hb : (k == Flock.constPos) = false := beq_eq_false_iff_ne.mpr hkc
          have h0 : formVal w.toArray (BitVec.ofNat (2 ^ m) 0) = 0 := formVal_zero _
          simp [hki, hkc, hd, hb, h0]


theorem size_rowValues (w : List E) :
    (blake2sRowValues w).1.size = 2 ^ m ∧ (blake2sRowValues w).2.size = 2 ^ m := by
  have hrow : blake2sRowValues w = ((blake2sWalk w.toArray).run
      (Array.replicate (2 ^ blake2sR1csLogSize) 0, Array.replicate (2 ^ blake2sR1csLogSize) 0)).2 :=
    rfl
  rw [hrow, run_walk, (size_writeRows _ _ _).1, (size_writeRows _ _ _).2]
  exact ⟨Array.size_replicate, Array.size_replicate⟩

/-- The value of a form is its pairing with the column weights read off the list. -/
theorem formVal_toArray (w : List E) (L : Form m) :
    formVal w.toArray L = ∑ j : Pos m, if L.getLsbD j then (toVec (2 ^ m) w)[j] else 0 := by
  unfold formVal
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [weightAt, toVec, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem spec_A (k j : Pos m) :
    Blake2sFlock.blake2sFlockSpec.r1cs.A k j = (blake2sCircuit.rowOf k).a.getLsbD j := rfl

theorem spec_B (k j : Pos m) :
    Blake2sFlock.blake2sFlockSpec.r1cs.B k j = (blake2sCircuit.rowOf k).b.getLsbD j := rfl

end WalkSim

open WalkSim in
/-- **The deployed walk is faithful**: for every column-weight vector of the block's size, the
verifier's forward walk `blake2s_row_values` (`Verifier.blake2sRowValues`) returns exactly the left
and right products `(A w, B w)` of the R1CS of `blake2sFlockSpec`, the R1CS of `blake2sCircuit`. -/
theorem walkFaithful_blake2sFlockSpec : WalkFaithful Blake2sFlock.blake2sFlockSpec := by
  intro w _
  have hsize := size_rowValues w
  have hrows := walk_rows w
  generalize blake2sRowValues w = R at hsize hrows ⊢
  constructor
  · apply List.ext_getElem
    · rw [Array.length_toList, hsize.1, List.length_ofFn]
    · intro i h1 h2
      rw [List.length_ofFn] at h2
      rw [List.getElem_ofFn, Array.getElem_toList, BlockR1CS.rows_fst]
      have hi : i < R.1.size := by rw [hsize.1]; exact h2
      have e : R.1[i] = R.1.getD i 0 := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
      rw [e, (hrows ⟨i, h2⟩).1, formVal_toArray]
      simp only [spec_A]
      rfl
  · apply List.ext_getElem
    · rw [Array.length_toList, hsize.2, List.length_ofFn]
    · intro i h1 h2
      rw [List.length_ofFn] at h2
      rw [List.getElem_ofFn, Array.getElem_toList, BlockR1CS.rows_snd]
      have hi : i < R.2.size := by rw [hsize.2]; exact h2
      have e : R.2[i] = R.2.getD i 0 := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
      rw [e, (hrows ⟨i, h2⟩).2, formVal_toArray]
      simp only [spec_B]
      rfl

/-- **The lincheck's terminal is faithful** for the deployed BLAKE2s R1CS. -/
theorem terminalFaithful_blake2sFlockSpec (prog : LeanVM.Semantics.Program)
    (s : LeanVM.Protocol.LeanIsa.Sizes) :
    TerminalFaithful Blake2sFlock.blake2sFlockSpec prog s :=
  terminalFaithful _ prog s walkFaithful_blake2sFlockSpec

end
end LeanVM.Protocol.EndToEnd.Front
