/-
  LeanVM.Guest.B1.Da.RowsIn

  A column's row loop (`__loop484`, `__loop486`) and gap loop (`__loop485`, `__loop487`) loading
  from a region, by trees of known words (`RelInT`).
-/

module

public import LeanVM.Guest.B1.Da.CellIn
public import LeanVM.Guest.B1.Da.Column

/-!
# The row and gap loops, by region

At row `g^j` of a column `g^b`, the row loop reads `rowbase[g^j]` (word `q + j`, holding the row
sum's chain `g^(a + 129j)`), the chain's cells `a + 129j + b` and the next, stores the cell's
digest at the column tree's leaf `nd + 2j` and the next, and, in the prefix columns, reads
`prefix_bases[g^j]` (word `p + j`, holding `g^(pd + 128j)`) and stores the digest there at
`pd + 128j + 2b` and the next; its `da_verify_cell` reads the weights at `l`. `RowR` collects
these words; the gap loop stores the zero cell's digest at `nd + 2(r + d)` and the next.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem rowBody_split (store : Bool) : rowBody store = (rowBody store).dropLast ++ [.ret []] := by
  cases store <;> rfl

theorem rowPre_straight (store : Bool) : (rowBody store).dropLast.all Main.Stmt.straight = true := by
  cases store <;> rfl

theorem gapBody_split (store : Bool) : gapBody store = (gapBody store).dropLast ++ [.ret []] := by
  cases store <;> rfl

theorem gapPre_straight (store : Bool) : (gapBody store).dropLast.all Main.Stmt.straight = true := by
  cases store <;> rfl

/-- The words a row loop's iterations read and write, and its cells' weights. -/
def RowR (store : Bool) (r l q b nd p a pd : ℕ) (i : ℕ) : Prop :=
  (∃ j < r, i = q + j ∨ i = a + 129 * j + b ∨ i = a + 129 * j + b + 1 ∨ i = nd + 2 * j ∨ i = nd + 2 * j + 1 ∨
    (store = true ∧ (i = p + j ∨ i = pd + 128 * j + 2 * b ∨ i = pd + 128 * j + 2 * b + 1))) ∨
    (l ≤ i ∧ i < l + 256)

theorem load_rd {rd : Reader} {x : E} {off : ℕ} {w : E} (h : LoadHolds rd x off w) :
    rd (x.limb 0 * gpow off) = some w := h.2

theorem addr_gen (e off : ℕ) : (gen ^ e).limb 0 * gpow off = gpow (e + off) := by
  rw [limb0_gen_pow, gpow_add']

theorem gen_succ_ne {j r : ℕ} (hr : r < 2 ^ 33) (hj : j < r) (hjr : j + 1 ≠ r) :
    gen ^ j * gen + gen ^ r ≠ 0 := by
  rw [← pow_succ]
  intro h
  exact hjr (gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp h))

/-- **An iteration of the row loop.** -/
theorem row_inst {rd : Reader} (store : Bool) {σ : Val} {fn : Fn} {es : List Ev} {vs : List V}
    {j r l q b nd p a pd : ℕ} (hf : coreProgram.find? (rowName store) = some fn)
    (hp : fn.params.map σ = [gen ^ j, gen ^ r, gen ^ l, gen ^ q, gen ^ b, gen ^ nd, gen ^ p])
    (hw : walk σ fn.body = .ret es vs) (hok : ∀ e ∈ es, e.Ok (coreProgram.Rel rd) rd σ)
    (hj : j < r) (hr : r < 2 ^ 33) (hrb : rd (gpow (q + j)) = some (gen ^ (a + 129 * j)))
    (hpb : store = true → rd (gpow (p + j)) = some (gen ^ (pd + 128 * j))) :
    (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ RowR store r l q b nd p a pd i) ∧
      calls es = [⟨"da_verify_cell", [.n 2], [.n 7, .n 8, .n 9], true⟩,
        ⟨rowName store, if store then [.n 25, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]
          else [.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], [], decide (j + 1 ≠ r)⟩] ∧
      [Core.V.n 2].map σ = [gen ^ l] ∧
      (if store then [Core.V.n 25, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]
        else [.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]).map σ =
        [gen ^ (j + 1), gen ^ r, gen ^ l, gen ^ q, gen ^ b, gen ^ nd, gen ^ p] ∧
      allocs σ es = [] := by
  rw [find_row, Option.some.injEq] at hf
  subst hf
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hp
  rw [rowBody_split, Main.walk_straight σ _ _ (rowPre_straight store)] at hw
  obtain ⟨rfl, -⟩ : (rowBody store).dropLast.flatMap (Main.slEvs σ) = es ∧ _ := by
    injection hw; exact ⟨by assumption, by assumption⟩
  obtain ⟨-, hal, -, hcl⟩ := Main.straight_parts σ _ (rowPre_straight store)
  have hA : ∀ {x : Atom}, Stmt.atom x ∈ (rowBody store).dropLast → x.Holds rd σ :=
    fun hx => atom_holds_of_ok hx hok
  have hsucc : ∀ {x y : V}, σ x = gen ^ j → σ y = word 2 0 0 → σ x * σ y = gen ^ (j + 1) := fun hx hy => by
    rw [hx, hy, word_gen, pow_succ]
  have hdec : ∀ {c : V}, σ c = gen ^ (j + 1) + gen ^ r → decide (σ c ≠ 0) = decide (j + 1 ≠ r) := fun hc => by
    rw [hc]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, e_add_eq_zero_iff]), fun h he => h ?_⟩
    exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)
  have e11 : ∀ {x : V}, σ x = gen ^ (q + j) → LoadHolds rd (σ x) 0 (σ (.n 11)) →
      σ (.n 11) = gen ^ (a + 129 * j) := fun hx hl => by
    have := load_rd hl
    rw [hx, addr_gen, Nat.add_zero] at this
    exact Option.some.inj (this.symm.trans hrb)
  cases store
  · have m10 : σ (.n 10) = σ (.n 3) * σ (.n 0) := hA (x := .mul (.n 10) (.n 3) (.n 0)) (by simp [rowBody])
    have l11 : LoadHolds rd (σ (.n 10)) 0 (σ (.n 11)) := hA (x := .load (.n 11) (.n 10) 0) (by simp [rowBody])
    have m12 : σ (.n 12) = σ (.n 11) * σ (.n 4) := hA (x := .mul (.n 12) (.n 11) (.n 4)) (by simp [rowBody])
    have m15 : σ (.n 15) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 15) (.n 0) (.n 0)) (by simp [rowBody])
    have m16 : σ (.n 16) = σ (.n 5) * σ (.n 15) := hA (x := .mul (.n 16) (.n 5) (.n 15)) (by simp [rowBody])
    have c17 : σ (.n 17) = word 2 0 0 := hA (x := .const (.n 17) (word 2 0 0)) (by simp [rowBody])
    have m18 : σ (.n 18) = σ (.n 0) * σ (.n 17) := hA (x := .mul (.n 18) (.n 0) (.n 17)) (by simp [rowBody])
    have a19 : σ (.n 19) = σ (.n 18) + σ (.n 1) := hA (x := .add (.n 19) (.n 18) (.n 1)) (by simp [rowBody])
    have c20 : σ (.n 20) = word 2 0 0 := hA (x := .const (.n 20) (word 2 0 0)) (by simp [rowBody])
    have m21 : σ (.n 21) = σ (.n 0) * σ (.n 20) := hA (x := .mul (.n 21) (.n 0) (.n 20)) (by simp [rowBody])
    have g10 : σ (.n 10) = gen ^ (q + j) := by rw [m10, h3, h0, ← pow_add]
    have g11 := e11 g10 l11
    have g12 : σ (.n 12) = gen ^ (a + 129 * j + b) := by rw [m12, g11, h4, ← pow_add]
    have g16 : σ (.n 16) = gen ^ (nd + 2 * j) := by rw [m16, m15, h5, h0, ← pow_add, ← pow_add, two_mul]
    refine ⟨fun A hA => ?_, ?_, by rw [List.map_cons, List.map_nil, h2], ?_, by rw [hal]; rfl⟩
    · rw [loadAddrs_straight σ _ (rowPre_straight false),
        show (rowBody false).dropLast.filterMap stmtLoad? =
          [(.n 10, 0), (.n 12, 0), (.n 12, 1), (.n 16, 0), (.n 16, 1)] from rfl] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl | rfl
      · exact ⟨q + j, by rw [g10, addr_gen, Nat.add_zero], Or.inl ⟨j, hj, Or.inl rfl⟩⟩
      · exact ⟨a + 129 * j + b, by rw [g12, addr_gen, Nat.add_zero], Or.inl ⟨j, hj, Or.inr (Or.inl rfl)⟩⟩
      · exact ⟨a + 129 * j + b + 1, by rw [g12, addr_gen], Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inl rfl))⟩⟩
      · exact ⟨nd + 2 * j, by rw [g16, addr_gen, Nat.add_zero], Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩⟩
      · exact ⟨nd + 2 * j + 1, by rw [g16, addr_gen],
          Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩⟩
    · rw [hcl, show (rowBody false).dropLast.filterMap Main.Stmt.callS =
        [(none, "da_verify_cell", [.n 2], [.n 7, .n 8, .n 9]),
         (some (.n 19), "__loop486", [.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], [])] from rfl]
      simp only [List.map_cons, List.map_nil, Main.mkCall, Bool.false_eq_true, ↓reduceIte]
      rw [hdec (by rw [a19, m18, hsucc h0 c17, h1])]
      rfl
    · simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil]
      rw [m21, hsucc h0 c20, h1, h2, h3, h4, h5, h6]
  · have m10 : σ (.n 10) = σ (.n 3) * σ (.n 0) := hA (x := .mul (.n 10) (.n 3) (.n 0)) (by simp [rowBody])
    have l11 : LoadHolds rd (σ (.n 10)) 0 (σ (.n 11)) := hA (x := .load (.n 11) (.n 10) 0) (by simp [rowBody])
    have m12 : σ (.n 12) = σ (.n 11) * σ (.n 4) := hA (x := .mul (.n 12) (.n 11) (.n 4)) (by simp [rowBody])
    have m15 : σ (.n 15) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 15) (.n 0) (.n 0)) (by simp [rowBody])
    have m16 : σ (.n 16) = σ (.n 5) * σ (.n 15) := hA (x := .mul (.n 16) (.n 5) (.n 15)) (by simp [rowBody])
    have m17 : σ (.n 17) = σ (.n 6) * σ (.n 0) := hA (x := .mul (.n 17) (.n 6) (.n 0)) (by simp [rowBody])
    have l18 : LoadHolds rd (σ (.n 17)) 0 (σ (.n 18)) := hA (x := .load (.n 18) (.n 17) 0) (by simp [rowBody])
    have m19 : σ (.n 19) = σ (.n 4) * σ (.n 4) := hA (x := .mul (.n 19) (.n 4) (.n 4)) (by simp [rowBody])
    have m20 : σ (.n 20) = σ (.n 18) * σ (.n 19) := hA (x := .mul (.n 20) (.n 18) (.n 19)) (by simp [rowBody])
    have c21 : σ (.n 21) = word 2 0 0 := hA (x := .const (.n 21) (word 2 0 0)) (by simp [rowBody])
    have m22 : σ (.n 22) = σ (.n 0) * σ (.n 21) := hA (x := .mul (.n 22) (.n 0) (.n 21)) (by simp [rowBody])
    have a23 : σ (.n 23) = σ (.n 22) + σ (.n 1) := hA (x := .add (.n 23) (.n 22) (.n 1)) (by simp [rowBody])
    have c24 : σ (.n 24) = word 2 0 0 := hA (x := .const (.n 24) (word 2 0 0)) (by simp [rowBody])
    have m25 : σ (.n 25) = σ (.n 0) * σ (.n 24) := hA (x := .mul (.n 25) (.n 0) (.n 24)) (by simp [rowBody])
    have g10 : σ (.n 10) = gen ^ (q + j) := by rw [m10, h3, h0, ← pow_add]
    have g11 := e11 g10 l11
    have g12 : σ (.n 12) = gen ^ (a + 129 * j + b) := by rw [m12, g11, h4, ← pow_add]
    have g16 : σ (.n 16) = gen ^ (nd + 2 * j) := by rw [m16, m15, h5, h0, ← pow_add, ← pow_add, two_mul]
    have g17 : σ (.n 17) = gen ^ (p + j) := by rw [m17, h6, h0, ← pow_add]
    have g18 : σ (.n 18) = gen ^ (pd + 128 * j) := by
      have := load_rd l18
      rw [g17, addr_gen, Nat.add_zero] at this
      exact Option.some.inj (this.symm.trans (hpb rfl))
    have g20 : σ (.n 20) = gen ^ (pd + 128 * j + 2 * b) := by
      rw [m20, m19, g18, h4, ← pow_add, ← pow_add, two_mul]
    refine ⟨fun A hA => ?_, ?_, by rw [List.map_cons, List.map_nil, h2], ?_, by rw [hal]; rfl⟩
    · rw [loadAddrs_straight σ _ (rowPre_straight true),
        show (rowBody true).dropLast.filterMap stmtLoad? =
          [(.n 10, 0), (.n 12, 0), (.n 12, 1), (.n 16, 0), (.n 16, 1), (.n 17, 0), (.n 20, 0), (.n 20, 1)]
          from rfl] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨q + j, by rw [g10, addr_gen, Nat.add_zero], Or.inl ⟨j, hj, Or.inl rfl⟩⟩
      · exact ⟨a + 129 * j + b, by rw [g12, addr_gen, Nat.add_zero], Or.inl ⟨j, hj, Or.inr (Or.inl rfl)⟩⟩
      · exact ⟨a + 129 * j + b + 1, by rw [g12, addr_gen], Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inl rfl))⟩⟩
      · exact ⟨nd + 2 * j, by rw [g16, addr_gen, Nat.add_zero], Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩⟩
      · exact ⟨nd + 2 * j + 1, by rw [g16, addr_gen],
          Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩⟩
      · exact ⟨p + j, by rw [g17, addr_gen, Nat.add_zero],
          Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))))⟩⟩
      · exact ⟨pd + 128 * j + 2 * b, by rw [g20, addr_gen, Nat.add_zero],
          Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl rfl)⟩))))⟩⟩
      · exact ⟨pd + 128 * j + 2 * b + 1, by rw [g20, addr_gen],
          Or.inl ⟨j, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr rfl)⟩))))⟩⟩
    · rw [hcl, show (rowBody true).dropLast.filterMap Main.Stmt.callS =
        [(none, "da_verify_cell", [.n 2], [.n 7, .n 8, .n 9]),
         (some (.n 23), "__loop484", [.n 25, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], [])] from rfl]
      simp only [List.map_cons, List.map_nil, Main.mkCall, ↓reduceIte]
      rw [hdec (by rw [a23, m22, hsucc h0 c21, h1])]
      rfl
    · simp only [↓reduceIte, List.map_cons, List.map_nil]
      rw [m25, hsucc h0 c24, h1, h2, h3, h4, h5, h6]

/-- The words of the row loop from row `j`: an iteration's frame and its cell's, then the skipped
tail's frame. -/
def rowTot (fs : String → ℕ) (store : Bool) (r j : ℕ) : ℕ :=
  (r - j) * (fs (rowName store) + fs "da_verify_cell") + fs (rowName store)

theorem rowName_ne (store : Bool) : rowName store ≠ "da_verify_cell" := by cases store <;> decide

/-- **The row loop by region**: from row `g^j`, `j < r`, on a memory holding the rows' chains at
`rowbase` and, in the prefix columns, the rows' prefix bases, a tree of `rowTot` words whose loads
are in `RowR`. -/
theorem rowLoop_relInT (fs : String → ℕ) (store : Bool) {rd : Reader} {r l q b nd p a pd : ℕ} {R : ℕ → Prop}
    (hr : r < 2 ^ 33) (hrb : ∀ j < r, rd (gpow (q + j)) = some (gen ^ (a + 129 * j)))
    (hpb : store = true → ∀ j < r, rd (gpow (p + j)) = some (gen ^ (pd + 128 * j)))
    (hR : ∀ i, RowR store r l q b nd p a pd i → R i) {j : ℕ} (hj : j < r)
    (h : coreProgram.Rel rd (rowName store) [gen ^ j, gen ^ r, gen ^ l, gen ^ q, gen ^ b, gen ^ nd, gen ^ p] []) :
    RelInTW fs rd R (rowTot fs store r j) (rowName store)
      [gen ^ j, gen ^ r, gen ^ l, gen ^ q, gen ^ b, gen ^ nd, gen ^ p] [] fun θ => rowTot θ store r j := by
  have key := relInTW_of_inv fs (R := R)
    (fun f args => (f = rowName store ∧ ∃ j < r, args = [gen ^ j, gen ^ r, gen ^ l, gen ^ q, gen ^ b, gen ^ nd, gen ^ p]) ∨
      (f = "da_verify_cell" ∧ args = [gen ^ l]))
    (fun θ f args => if f = "da_verify_cell" then θ "da_verify_cell" else rowTot θ store r (logG (args.headD 0)))
    (fun f args σ fn es vs hI hf hp hw hok => ?_) (Or.inl ⟨rfl, j, hj, rfl⟩) h
  · simpa [rowName_ne store, logG_gen_pow (show j < 2 ^ 64 - 1 by omega)] using key
  rcases hI with ⟨rfl, j, hj, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hl, hc, h2, hnext, ha⟩ := row_inst store hf hp hw hok hj hr (hrb j hj) (fun hs => hpb hs j hj)
    refine ⟨fun A hA => ?_, fun c hc' ht => ?_, ?_⟩
    · obtain ⟨i, hi, hRi⟩ := hl A hA
      exact ⟨i, hi, hR i hRi⟩
    · rw [hc] at hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl
      · exact Or.inr ⟨rfl, h2⟩
      · simp only [decide_eq_true_eq] at ht
        exact Or.inl ⟨rfl, j + 1, by omega, hnext⟩
    · intro θ
      rw [hc, ha, callsTot]
      simp only [List.map_cons, List.map_nil, ↓reduceIte, List.sum_cons, List.sum_nil,
        rowName_ne store, hnext, List.headD_cons, Nat.add_zero, List.sum_nil]
      rw [logG_gen_pow (show j < 2 ^ 64 - 1 by omega)]
      by_cases hj1 : j + 1 = r
      · simp only [hj1, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, rowTot]
        rw [show r - j = 1 by omega]
        ring
      · simp only [ne_eq, hj1, not_false_eq_true, decide_true, ↓reduceIte, rowTot]
        rw [logG_gen_pow (show j + 1 < 2 ^ 64 - 1 by omega), show r - j = (r - (j + 1)) + 1 by omega]
        ring
  · obtain ⟨hl, hc, ha⟩ := vc_inst hf hp hw
    refine ⟨fun A hA => ?_, fun c hc' => by rw [hc] at hc'; simp at hc', fun θ => by rw [hc, ha]; simp [callsTot]⟩
    obtain ⟨i, hi, h1, h2⟩ := hl A hA
    exact ⟨i, hi, hR i (Or.inr ⟨h1, h2⟩)⟩

/-- The words the gap loop stores: the zero cell's digest at the padding leaves. -/
def GapR (r G nd : ℕ) (i : ℕ) : Prop := ∃ d < G, i = nd + 2 * (r + d) ∨ i = nd + 2 * (r + d) + 1

/-- The words of the gap loop from padding row `d`. -/
def gapTot (fs : String → ℕ) (store : Bool) (G d : ℕ) : ℕ := (G - d) * fs (gapName store) + fs (gapName store)

/-- **The gap loop by region.** -/
theorem gapLoop_relInT (fs : String → ℕ) (store : Bool) {rd : Reader} {r G nd : ℕ} {R : ℕ → Prop}
    (hG : G < 2 ^ 33) (hR : ∀ i, GapR r G nd i → R i) {d : ℕ} (hd : d < G)
    (h : coreProgram.Rel rd (gapName store) [gen ^ d, gen ^ G, gen ^ nd, gen ^ r] []) :
    RelInTW fs rd R (gapTot fs store G d) (gapName store) [gen ^ d, gen ^ G, gen ^ nd, gen ^ r] []
      fun θ => gapTot θ store G d := by
  have key := relInTW_of_inv fs (R := R)
    (fun f args => f = gapName store ∧ ∃ d < G, args = [gen ^ d, gen ^ G, gen ^ nd, gen ^ r])
    (fun θ _ args => gapTot θ store G (logG (args.headD 0)))
    (fun f args σ fn es vs hI hf hp hw hok => ?_) ⟨rfl, d, hd, rfl⟩ h
  · simpa [logG_gen_pow (show d < 2 ^ 64 - 1 by omega)] using key
  obtain ⟨rfl, d, hd, rfl⟩ := hI
  rw [find_gap, Option.some.injEq] at hf
  subst hf
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3⟩ := hp
  rw [gapBody_split, Main.walk_straight σ _ _ (gapPre_straight store)] at hw
  obtain ⟨rfl, -⟩ : (gapBody store).dropLast.flatMap (Main.slEvs σ) = es ∧ _ := by
    injection hw; exact ⟨by assumption, by assumption⟩
  obtain ⟨-, hal, -, hcl⟩ := Main.straight_parts σ _ (gapPre_straight store)
  have hA : ∀ {x : Atom}, Stmt.atom x ∈ (gapBody store).dropLast → x.Holds rd σ :=
    fun hx => atom_holds_of_ok hx hok
  have m4 : σ (.n 4) = σ (.n 3) * σ (.n 3) := hA (x := .mul (.n 4) (.n 3) (.n 3)) (by simp [gapBody])
  have m5 : σ (.n 5) = σ (.n 2) * σ (.n 4) := hA (x := .mul (.n 5) (.n 2) (.n 4)) (by simp [gapBody])
  have m6 : σ (.n 6) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 6) (.n 0) (.n 0)) (by simp [gapBody])
  have m7 : σ (.n 7) = σ (.n 5) * σ (.n 6) := hA (x := .mul (.n 7) (.n 5) (.n 6)) (by simp [gapBody])
  have c10 : σ (.n 10) = word 2 0 0 := hA (x := .const (.n 10) (word 2 0 0)) (by simp [gapBody])
  have m11 : σ (.n 11) = σ (.n 0) * σ (.n 10) := hA (x := .mul (.n 11) (.n 0) (.n 10)) (by simp [gapBody])
  have a12 : σ (.n 12) = σ (.n 11) + σ (.n 1) := hA (x := .add (.n 12) (.n 11) (.n 1)) (by simp [gapBody])
  have c13 : σ (.n 13) = word 2 0 0 := hA (x := .const (.n 13) (word 2 0 0)) (by simp [gapBody])
  have m14 : σ (.n 14) = σ (.n 0) * σ (.n 13) := hA (x := .mul (.n 14) (.n 0) (.n 13)) (by simp [gapBody])
  have g7 : σ (.n 7) = gen ^ (nd + 2 * (r + d)) := by
    rw [m7, m6, m5, m4, h0, h2, h3]; ring
  have g11 : σ (.n 11) = gen ^ (d + 1) := by rw [m11, c10, h0, word_gen, pow_succ]
  have g14 : σ (.n 14) = gen ^ (d + 1) := by rw [m14, c13, h0, word_gen, pow_succ]
  have hc : calls ((gapBody store).dropLast.flatMap (Main.slEvs σ)) =
      [⟨gapName store, [.n 14, .n 1, .n 2, .n 3], [], decide (d + 1 ≠ G)⟩] := by
    rw [hcl, show (gapBody store).dropLast.filterMap Main.Stmt.callS =
      [(some (.n 12), gapName store, [.n 14, .n 1, .n 2, .n 3], [])] by cases store <;> rfl]
    have hdec : decide (gen ^ (d + 1) + gen ^ G ≠ 0) = decide (d + 1 ≠ G) := by
      refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, e_add_eq_zero_iff]), fun h he => h ?_⟩
      exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)
    simp only [List.map_cons, List.map_nil, Main.mkCall, a12, g11, h1, hdec]
  refine ⟨fun A hA => ?_, fun c hc' ht => ?_, ?_⟩
  · rw [loadAddrs_straight σ _ (gapPre_straight store),
      show (gapBody store).dropLast.filterMap stmtLoad? = [(.n 7, 0), (.n 7, 1)] by cases store <;> rfl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl
    · exact ⟨nd + 2 * (r + d), by rw [g7, addr_gen, Nat.add_zero], hR _ ⟨d, hd, Or.inl rfl⟩⟩
    · exact ⟨nd + 2 * (r + d) + 1, by rw [g7, addr_gen], hR _ ⟨d, hd, Or.inr rfl⟩⟩
  · rw [hc] at hc'
    obtain rfl := List.mem_singleton.mp hc'
    simp only [decide_eq_true_eq] at ht
    refine ⟨rfl, d + 1, by omega, ?_⟩
    simp only [List.map_cons, List.map_nil, g14, h1, h2, h3]
  · intro θ
    rw [hc, hal, show (gapBody store).dropLast.filterMap Main.Stmt.allocSz = [] by cases store <;> rfl, callsTot]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.headD_cons, Nat.add_zero, g14]
    rw [logG_gen_pow (show d < 2 ^ 64 - 1 by omega)]
    by_cases hd1 : d + 1 = G
    · simp only [hd1, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, gapTot]
      rw [show G - d = 1 by omega]
      ring
    · simp only [ne_eq, hd1, not_false_eq_true, decide_true, ↓reduceIte, gapTot]
      rw [logG_gen_pow (show d + 1 < 2 ^ 64 - 1 by omega), show G - d = (G - (d + 1)) + 1 by omega]
      ring

end
end LeanVM.Guest.B1.Digest
