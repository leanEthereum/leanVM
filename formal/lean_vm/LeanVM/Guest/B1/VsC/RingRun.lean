/-
  LeanVM.Guest.B1.VsC.RingRun

  A run window that allocates, by parts; the ring switch's three buffers as templates, and their words.
-/

module

public import LeanVM.Guest.B1.VsC.RunBufs

/-!
# The ring switch's run, generically

`RunHyp` of a run cut into parts: `runHyp_append0` (a first part allocating nothing), `runHyp_alloc_cons` (a
`HeapBuf(n)` at the cursor, the rest from the cursor past it), `RunHyp.of_noAlloc` (a part with no allocation and no
heap hint, from its loads, its asking atoms and its loads' words).

`verify_sub`'s ring switch fills three buffers by straight code, written here as templates the kernel matches against
the body:

* `vsMcS`: the sixteen map challenges, `f` then `g` (`vsMcV`), stored into `.n 3039`; their words `mcW σ`.
* `vsRc`: `ring_coefficients(f, g)` into `.n 3040`, block `c` (`rcBlock`) the products `f_r · g_c^(2^(8r))`, each
  `g_c` squared eight times a step; `rcBlock_vals` gives each product's value, `ringCoefficients_getD` the native
  coefficient at `8r + c`, so the stores (`rcStores`) write `ringCoefficients f g`.
* `vsRs`: the merged slices into `.n 3553`, word `i` the Keccak slice `i` plus `rho` times the link's word `80 + i`
  of the packed message (`rsW`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Runs by parts -/

/-- No heap hint. -/
def noHeapB (a : Atom) : Bool := (atomHeapDest? a).isNone

theorem hints_nil {σ : Val} {as : List Atom} (h : as.all noHeapB = true) : heapHintAddrs σ (as.map Ev.atom) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro A hA
  simp only [heapHintAddrs, List.mem_flatMap, List.mem_map] at hA
  obtain ⟨_, ⟨x, hm, rfl⟩, hA⟩ := hA
  obtain ⟨p, off, len, hd, -⟩ := mem_hintAddrs hA
  have := List.all_eq_true.mp h x hm
  simp [noHeapB, hd] at this

section
variable {k : ℕ} {σ0 : Val} {w : ℕ → E} {a : ℕ} {Own R D : ℕ → Prop} {Pre O : Reader → Prop}

/-- **A part with no allocation and no heap hint**: its loads in the region, its asks. -/
theorem RunHyp.of_noAlloc {as : List Atom} (h0 : as.all noAllocB = true) (h1 : as.all noHeapB = true)
    (loads : ∀ d p off, Atom.load d p off ∈ as →
      ∃ i, (σ0 p).limb 0 * addressOfIndex off = addressOfIndex i ∧ (Own i ∨ R i ∨ D i))
    (pure : ∀ x ∈ as.filter pureAsks, PureF k σ0 x)
    (mem : ∀ rd, LowDef k rd → Pre rd → O rd → ∀ x ∈ as.filter memAsks, MemF rd σ0 x) :
    RunHyp k σ0 w a Own R D Pre O as :=
  RunHyp.of_asks (by rw [(noAlloc_fields (σ := σ0) h0).1, (noAlloc_fields (σ := σ0) h0).2]; rfl)
    (fun A hA => by obtain ⟨d, p, off, hm, rfl⟩ := mem_loadAddrs hA; exact loads d p off hm)
    (fun A hA => by rw [hints_nil h1] at hA; simp at hA) pure mem

/-- **Two parts, the first allocating nothing.** -/
theorem runHyp_append0 {xs ys : List Atom} (h0 : xs.all noAllocB = true) (hx : RunHyp k σ0 w a Own R D Pre O xs)
    (hy : RunHyp k σ0 w a Own R D Pre O ys) : RunHyp k σ0 w a Own R D Pre O (xs ++ ys) := by
  obtain ⟨e1, e2⟩ := noAlloc_fields (σ := σ0) h0
  have h2 := hy.bufs
  refine ⟨?_, fun A hA => ?_, fun A hA => ?_, fun x hm => ?_, fun rd hl hp ho x hm => ?_⟩
  · have f1 : allocDsts ((xs ++ ys).map Ev.atom) = allocDsts (ys.map Ev.atom) := by
      simp only [allocDsts, List.map_append, List.filterMap_append] at e1 ⊢; rw [e1, List.nil_append]
    have f2 : allocs σ0 ((xs ++ ys).map Ev.atom) = allocs σ0 (ys.map Ev.atom) := by
      simp only [allocs, List.map_append, List.filterMap_append] at e2 ⊢; rw [e2, List.nil_append]
    rw [f1, f2]; exact h2
  · simp only [loadAddrs, List.map_append, List.filterMap_append, List.mem_append] at hA
    exact hA.elim (hx.loads A) (hy.loads A)
  · simp only [heapHintAddrs, List.map_append, List.flatMap_append, List.mem_append] at hA
    exact hA.elim (hx.hints A) (hy.hints A)
  · exact (List.mem_append.mp hm).elim (hx.pure x) (hy.pure x)
  · exact (List.mem_append.mp hm).elim (hx.mem rd hl hp ho x) (hy.mem rd hl hp ho x)

/-- **A `HeapBuf(n)` at the cursor**, then the rest from the cursor past it. -/
theorem runHyp_alloc_cons {d : V} {n b : ℕ} {ys : List Atom} (hw : w d.idx = ofK (addressOfIndex a))
    (hb : b = a + n) (hy : RunHyp k σ0 w b Own R D Pre O ys) :
    RunHyp k σ0 w a Own R D Pre O (.hint (.alloc d n) :: ys) := by
  subst hb
  have h2 := hy.bufs
  refine ⟨?_, fun A hA => ?_, fun A hA => ?_, fun x hm => ?_, fun rd hl hp ho x hm => ?_⟩
  · show w d.idx :: (allocDsts (ys.map Ev.atom)).map (fun v => w v.idx) =
      ofK (addressOfIndex a) :: (bases (a + n) (allocs σ0 (ys.map Ev.atom))).map (fun b => ofK (addressOfIndex b))
    rw [hw, h2]
  · exact hy.loads A hA
  · exact hy.hints A hA
  · rcases List.mem_cons.mp hm with rfl | hm
    · trivial
    · exact hy.pure x hm
  · rcases List.mem_cons.mp hm with rfl | hm
    · trivial
    · exact hy.mem rd hl hp ho x hm

end

theorem allocs_append0 {σ : Val} {xs ys : List Atom} (h0 : xs.all noAllocB = true) :
    allocs σ ((xs ++ ys).map Ev.atom) = allocs σ (ys.map Ev.atom) := by
  have e2 := (noAlloc_fields (σ := σ) h0).2
  simp only [allocs, List.map_append, List.filterMap_append] at e2 ⊢
  rw [e2, List.nil_append]

theorem allocs_alloc_cons {σ : Val} {d : V} {n : ℕ} {ys : List Atom} :
    allocs σ ((Atom.hint (.alloc d n) :: ys).map Ev.atom) = n :: allocs σ (ys.map Ev.atom) := rfl

/-! ## `ring_coefficients` -/

/-- A step of `ring_coefficients`' fold. -/
def rcStep (acc : List E × List E) (fP : E) : List E × List E :=
  (acc.1 ++ acc.2.map (fP * ·), acc.2.map (frobenius8 · 1))

theorem sq_pow (x : E) {n m : ℕ} (h : m = n + 1) : (x ^ 2 ^ n) ^ 2 = x ^ 2 ^ m := by
  subst h; rw [← pow_mul, ← pow_succ]

/-- The fold of `ring_coefficients` from step `n`. -/
theorem rc_foldl : ∀ (f acc g : List E) (n : ℕ),
    (f.foldl rcStep (acc, g.map (· ^ 2 ^ (8 * n)))).1 =
      acc ++ (f.zipIdx n).flatMap (fun p => g.map (fun x => p.1 * x ^ 2 ^ (8 * p.2)))
  | [], acc, g, n => by simp
  | fP :: f, acc, g, n => by
    have e : (g.map (· ^ 2 ^ (8 * n))).map (frobenius8 · 1) = g.map (· ^ 2 ^ (8 * (n + 1))) := by
      rw [List.map_map]
      refine List.map_congr_left fun x _ => ?_
      show (x ^ 2 ^ (8 * n)) ^ 2 ^ (8 * 1) = x ^ 2 ^ (8 * (n + 1))
      rw [← pow_mul, ← pow_add, show 8 * n + 8 * 1 = 8 * (n + 1) by ring]
    rw [List.foldl_cons, show rcStep (acc, g.map (· ^ 2 ^ (8 * n))) fP =
      (acc ++ (g.map (· ^ 2 ^ (8 * n))).map (fP * ·), (g.map (· ^ 2 ^ (8 * n))).map (frobenius8 · 1)) from rfl,
      e, rc_foldl f _ g (n + 1), List.zipIdx_cons, List.flatMap_cons, List.map_map, List.append_assoc]
    rfl

/-- `ring_coefficients(f, g)` as a sum over `f`'s indices. -/
theorem ringCoefficients_eq (f g : List E) :
    ringCoefficients f g = (f.zipIdx).flatMap (fun p => g.map (fun x => p.1 * x ^ 2 ^ (8 * p.2))) := by
  have h := rc_foldl f [] g 0
  rw [show (g.map (· ^ 2 ^ (8 * 0))) = g by simp, List.nil_append] at h
  exact h

/-- An index of a flattening of lists of eight. -/
theorem flatMap_get8 {α β : Type} (F : α → List β) (hF : ∀ x, (F x).length = 8) :
    ∀ (l : List α) (r c : ℕ), c < 8 → (l.flatMap F)[8 * r + c]? = l[r]?.bind fun x => (F x)[c]?
  | [], r, c, _ => by simp
  | x :: l, 0, c, hc => by
    have h1 : 8 * 0 + c < (F x).length := by rw [hF]; omega
    rw [List.flatMap_cons, List.getElem?_append_left h1]
    simp
  | x :: l, r + 1, c, hc => by
    have h2 : (F x).length ≤ 8 * (r + 1) + c := by rw [hF]; omega
    rw [List.flatMap_cons, List.getElem?_append_right h2, hF,
      show 8 * (r + 1) + c - 8 = 8 * r + c by omega, flatMap_get8 F hF l r c hc]
    simp

theorem getElem?_getD {l : List E} {i : ℕ} (h : i < l.length) : l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- **The coefficient `8r + c`**: `f_r · g_c^(2^(8r))`. -/
theorem ringCoefficients_getD {f g : List E} (hg : g.length = 8) {r c : ℕ} (hr : r < f.length) (hc : c < 8) :
    (ringCoefficients f g)[8 * r + c]? = some (f.getD r 0 * g.getD c 0 ^ 2 ^ (8 * r)) := by
  rw [ringCoefficients_eq, flatMap_get8 (fun p : E × ℕ => g.map (fun x => p.1 * x ^ 2 ^ (8 * p.2)))
    (fun _ => by rw [List.length_map, hg]) _ r c hc, List.getElem?_zipIdx, getElem?_getD hr]
  show (List.map (fun x => f.getD r 0 * x ^ 2 ^ (8 * (0 + r))) g)[c]? = _
  rw [List.getElem?_map, getElem?_getD (show c < g.length by omega), Nat.zero_add]
  rfl

/-! ## The templates -/

/-- The map challenges' values, `f` then `g`. -/
def vsMcV : List ℕ := [2997, 2998, 2999, 3000, 3001, 3002, 3003, 3017, 3018, 3019, 3020, 3021, 3022, 3023, 3024, 3038]

theorem vsMcV_le : ∀ j < 16, vsMcV.getD j 0 ≤ 3038 := by decide

/-- The map challenges stored into `.n 3039`. -/
def vsMcS : List Atom := (List.range 16).map fun j => .load (.n (vsMcV.getD j 0)) (.n 3039) j

/-- The map challenges' words. -/
def mcW (σ : Val) : List E := vsMcV.map fun i => σ (.n i)

/-- The operand of the `j`-th squaring of round `r` of block `v`: `g_c` first, then the previous square. -/
def rcSq (v gc r j : ℕ) : ℕ := if j = 0 then (if r = 0 then gc else v + 9 * r - 1) else v + 9 * r + j

theorem rcSq_succ (v gc r j : ℕ) : rcSq v gc r (j + 1) = v + 9 * r + (j + 1) := by
  simp only [rcSq, Nat.add_one_ne_zero, ↓reduceIte]

theorem rcSq_zero_succ (v gc r : ℕ) : rcSq v gc (r + 1) 0 = v + 9 * (r + 1) - 1 := by
  simp only [rcSq, Nat.add_one_ne_zero, ↓reduceIte]

/-- Block `c` of `ring_coefficients` from value `v`: `f_0·g_c` stored at `c`, then per round `r + 1` eight squarings
of `g_c` and `f_(r+1)` times the last, stored at `8(r + 1) + c`. -/
def rcBlock (v gc c : ℕ) : List Atom :=
  [.mul (.n v) (.n (vsMcV.getD 0 0)) (.n gc), .load (.n v) (.n 3040) c] ++
    (List.range 7).flatMap fun r =>
      (List.range 8).map (fun j => .mul (.n (v + 1 + 9 * r + j)) (.n (rcSq v gc r j)) (.n (rcSq v gc r j))) ++
        [.mul (.n (v + 9 + 9 * r)) (.n (vsMcV.getD (r + 1) 0)) (.n (v + 8 + 9 * r)),
          .load (.n (v + 9 + 9 * r)) (.n 3040) (8 * (r + 1) + c)]

/-- `ring_coefficients` into `.n 3040`. -/
def vsRc : List Atom := (List.range 8).flatMap fun c => rcBlock (3041 + 64 * c) (vsMcV.getD (8 + c) 0) c

/-- `vsRc`'s stores. -/
def rcStores : List Atom :=
  (List.range 8).flatMap fun c => (List.range 8).map fun r => .load (.n (3041 + 64 * c + 9 * r)) (.n 3040) (8 * r + c)

/-- The merged slices into `.n 3553`. -/
def vsRs : List Atom :=
  (List.range 64).flatMap fun i =>
    [.load (.n (3554 + 4 * i)) (.n 21) i, .load (.n (3554 + 4 * i + 1)) (.n 1076) (80 + i),
      .mul (.n (3554 + 4 * i + 2)) (.n 3026) (.n (3554 + 4 * i + 1)),
      .add (.n (3554 + 4 * i + 3)) (.n (3554 + 4 * i)) (.n (3554 + 4 * i + 2)),
      .load (.n (3554 + 4 * i + 3)) (.n 3553) i]

/-- `vsRs`'s stores. -/
def rsStores : List Atom := (List.range 64).map fun i => .load (.n (3554 + 4 * i + 3)) (.n 3553) i

/-- The merged slices' words: slice `i` plus `r` times the message's word `80 + i`. -/
def rsW (sl m : List E) (r : E) : List E := (List.range 64).map fun i => sl.getD i 0 + r * m.getD (80 + i) 0

theorem rsW_length (sl m : List E) (r : E) : (rsW sl m r).length = 64 := by simp [rsW]

theorem rsW_get? (sl m : List E) (r : E) {i : ℕ} (hi : i < 64) :
    (rsW sl m r)[i]? = some (sl.getD i 0 + r * m.getD (80 + i) 0) := by
  simp [rsW, hi]

/-! ## The values -/

section
variable {rd0 : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

theorem mem_rcBlock_first {v gc c : ℕ} : Atom.mul (.n v) (.n (vsMcV.getD 0 0)) (.n gc) ∈ rcBlock v gc c :=
  List.mem_append.mpr (Or.inl List.mem_cons_self)

theorem mem_rcBlock_sq {v gc c r j : ℕ} (hr : r < 7) (hj : j < 8) :
    Atom.mul (.n (v + 1 + 9 * r + j)) (.n (rcSq v gc r j)) (.n (rcSq v gc r j)) ∈ rcBlock v gc c :=
  List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
    List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))⟩))

theorem mem_rcBlock_prod {v gc c r : ℕ} (hr : r < 7) :
    Atom.mul (.n (v + 9 + 9 * r)) (.n (vsMcV.getD (r + 1) 0)) (.n (v + 8 + 9 * r)) ∈ rcBlock v gc c :=
  List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
    List.mem_append.mpr (Or.inr List.mem_cons_self)⟩))

/-- **A block's products**: `σ (v + 9r) = f_r · g_c^(2^(8r))`. -/
theorem rcBlock_vals {v gc c : ℕ} (hg : ∀ x ∈ rcBlock v gc c, Good rd0 S w σ x) (hgc : gc < v)
    (hf : ∀ r < 8, vsMcV.getD r 0 < v) :
    ∀ r < 8, σ (.n (v + 9 * r)) = σ (.n (vsMcV.getD r 0)) * σ (.n gc) ^ 2 ^ (8 * r) := by
  have step : ∀ r < 7, ∀ j < 8, σ (.n (v + 1 + 9 * r + j)) = σ (.n (rcSq v gc r j)) ^ 2 := fun r hr j hj => by
    rw [sq]
    refine good_mulF (hg _ (mem_rcBlock_sq hr hj)) ?_ ?_ <;> (unfold rcSq; split_ifs <;> omega)
  have sqv : ∀ r < 7, ∀ j < 8, σ (.n (v + 1 + 9 * r + j)) = σ (.n gc) ^ 2 ^ (8 * r + j + 1) := by
    intro r
    induction r with
    | zero =>
      intro hr j hj
      induction j with
      | zero => rw [step 0 hr 0 hj]; simp [rcSq]
      | succ j ih =>
        rw [step 0 hr (j + 1) hj, show rcSq v gc 0 (j + 1) = v + 1 + 9 * 0 + j by rw [rcSq_succ]; omega,
          ih (by omega)]
        exact sq_pow _ (by omega)
    | succ r ihr =>
      intro hr j hj
      induction j with
      | zero =>
        rw [step (r + 1) hr 0 hj, show rcSq v gc (r + 1) 0 = v + 1 + 9 * r + 7 by rw [rcSq_zero_succ]; omega,
          ihr (by omega) 7 (by omega)]
        exact sq_pow _ (by omega)
      | succ j ih =>
        rw [step (r + 1) hr (j + 1) hj,
          show rcSq v gc (r + 1) (j + 1) = v + 1 + 9 * (r + 1) + j by rw [rcSq_succ]; omega,
          ih (by omega)]
        exact sq_pow _ (by omega)
  intro r hr
  cases r with
  | zero =>
    have h := good_mulF (hg _ mem_rcBlock_first) (hf 0 (by norm_num)) hgc
    simpa using h
  | succ r =>
    have h := good_mulF (hg _ (mem_rcBlock_prod (r := r) (by omega))) (by have := hf (r + 1) hr; omega) (by omega)
    rw [show v + 9 * (r + 1) = v + 9 + 9 * r by ring, h, show v + 8 + 9 * r = v + 1 + 9 * r + 7 by omega,
      sqv r (by omega) 7 (by omega)]
    exact congrArg (fun t => σ (.n (vsMcV.getD (r + 1) 0)) * σ (.n gc) ^ 2 ^ t) (by omega)

theorem mcW_take (σ : Val) : ∀ r < 8, ((mcW σ).take 8).getD r 0 = σ (.n (vsMcV.getD r 0)) := by
  intro r hr; interval_cases r <;> rfl

theorem mcW_drop (σ : Val) : ∀ c < 8, ((mcW σ).drop 8).getD c 0 = σ (.n (vsMcV.getD (8 + c) 0)) := by
  intro c hc; interval_cases c <;> rfl

theorem mcW_get? (σ : Val) : ∀ j < 16, (mcW σ)[j]? = some (σ (.n (vsMcV.getD j 0))) := by
  intro j hj; interval_cases j <;> rfl

/-- The ring coefficients of the map challenges. -/
def mcRc (σ : Val) : List E := ringCoefficients ((mcW σ).take 8) ((mcW σ).drop 8)

theorem mcW_length (σ : Val) : (mcW σ).length = 16 := rfl

/-- **`vsRc`'s stores write `ring_coefficients(f, g)`.** -/
theorem rcStores_mem {b : ℕ} (hg : ∀ x ∈ vsRc, Good rd0 S w σ x) (h40 : σ (.n 3040) = ptrAt b)
    (r40 : ReadsAt rd0 (ptrAt b) (mcRc σ)) : ∀ x ∈ rcStores, MemF rd0 σ x := by
  intro x hx
  simp only [rcStores, List.mem_flatMap, List.mem_range, List.mem_map] at hx
  obtain ⟨c, hc, r, hr, rfl⟩ := hx
  have hv := rcBlock_vals (v := 3041 + 64 * c) (gc := vsMcV.getD (8 + c) 0) (c := c)
    (fun x hx => hg x (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, hx⟩))
    (by have := vsMcV_le (8 + c) (by omega); omega) (fun r hr => by have := vsMcV_le r (by omega); omega) r hr
  show LoadHolds rd0 (σ (.n 3040)) (8 * r + c) (σ (.n (3041 + 64 * c + 9 * r)))
  rw [h40, hv]
  refine loadHolds_of_get? r40 ?_
  rw [mcRc, ringCoefficients_getD (by rw [List.length_drop, mcW_length]) (by rw [List.length_take, mcW_length]; omega) hc, mcW_take σ r hr,
    mcW_drop σ c hc]

/-- **`vsMcS`'s stores write the map challenges.** -/
theorem mcStores_mem {b : ℕ} (h39 : σ (.n 3039) = ptrAt b) (r39 : ReadsAt rd0 (ptrAt b) (mcW σ)) :
    ∀ x ∈ vsMcS, MemF rd0 σ x := by
  intro x hx
  simp only [vsMcS, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  show LoadHolds rd0 (σ (.n 3039)) j (σ (.n (vsMcV.getD j 0)))
  rw [h39]
  exact loadHolds_of_get? r39 (mcW_get? σ j hj)

/-- `vsRs`'s fresh loads are no stores. -/
def rsFreshB (S : List Atom) : Bool :=
  (List.range 64).all fun i =>
    !S.contains (.load (.n (3554 + 4 * i)) (.n 21) i) && !S.contains (.load (.n (3554 + 4 * i + 1)) (.n 1076) (80 + i))

/-- **`vsRs`'s stores write the merged slices.** -/
theorem rsStores_mem {b b21 bm : ℕ} {sl m : List E} (hg : ∀ x ∈ vsRs, Good rd0 S w σ x) (hS : rsFreshB S = true)
    (h21 : σ (.n 21) = ptrAt b21) (hl21 : 64 ≤ sl.length) (r21 : ReadsAt rd0 (ptrAt b21) sl)
    (hm : σ (.n 1076) = ptrAt bm) (hlm : 144 ≤ m.length) (rm : ReadsAt rd0 (ptrAt bm) m)
    (h53 : σ (.n 3553) = ptrAt b) (r53 : ReadsAt rd0 (ptrAt b) (rsW sl m (σ (.n 3026)))) :
    ∀ x ∈ rsStores, MemF rd0 σ x := by
  intro x hx
  simp only [rsStores, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have mem : ∀ y ∈ [Atom.load (.n (3554 + 4 * i)) (.n 21) i, .load (.n (3554 + 4 * i + 1)) (.n 1076) (80 + i),
      .mul (.n (3554 + 4 * i + 2)) (.n 3026) (.n (3554 + 4 * i + 1)),
      .add (.n (3554 + 4 * i + 3)) (.n (3554 + 4 * i)) (.n (3554 + 4 * i + 2)),
      .load (.n (3554 + 4 * i + 3)) (.n 3553) i], Good rd0 S w σ y := fun y hy =>
    hg y (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hy⟩)
  have hf := List.all_eq_true.mp hS i (List.mem_range.mpr hi)
  have hf1 : Atom.load (.n (3554 + 4 * i)) (.n 21) i ∉ S := fun h => by
    rw [List.contains_iff_mem.mpr h] at hf; simp at hf
  have hf2 : Atom.load (.n (3554 + 4 * i + 1)) (.n 1076) (80 + i) ∉ S := fun h => by
    rw [List.contains_iff_mem.mpr h] at hf; simp at hf
  have e0 : σ (.n (3554 + 4 * i)) = sl.getD i 0 :=
    good_load_get? hf1 (mem (.load (.n (3554 + 4 * i)) (.n 21) i) (by simp)) h21 r21 (getElem?_getD (by omega))
  have e1 : σ (.n (3554 + 4 * i + 1)) = m.getD (80 + i) 0 :=
    good_load_get? hf2 (mem (.load (.n (3554 + 4 * i + 1)) (.n 1076) (80 + i)) (by simp)) hm rm
      (getElem?_getD (by omega))
  have e2 : σ (.n (3554 + 4 * i + 2)) = σ (.n 3026) * σ (.n (3554 + 4 * i + 1)) :=
    good_mulF (mem (.mul (.n (3554 + 4 * i + 2)) (.n 3026) (.n (3554 + 4 * i + 1))) (by simp)) (by omega) (by omega)
  have e3 : σ (.n (3554 + 4 * i + 3)) = σ (.n (3554 + 4 * i)) + σ (.n (3554 + 4 * i + 2)) :=
    mem (.add (.n (3554 + 4 * i + 3)) (.n (3554 + 4 * i)) (.n (3554 + 4 * i + 2))) (by simp)
  show LoadHolds rd0 (σ (.n 3553)) i (σ (.n (3554 + 4 * i + 3)))
  rw [h53, e3, e2, e0, e1]
  exact loadHolds_of_get? r53 (rsW_get? sl m _ hi)

end

end
end LeanVM.Guest.B1.VsC
