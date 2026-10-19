/-
  LeanVM.Guest.B1.Da.SetupIn

  `da_verify`'s self-calling loops (`__loop88`, `__loop89`, `__loop92`, `__loop93`, `__loop94`)
  loading from a region, by trees of known words within weights (`RelInTW`).
-/

module

public import LeanVM.Guest.B1.Da.LoopIn
public import LeanVM.Guest.B1.Da.RowHash
public import LeanVM.Guest.B1.Da.RowShape

/-!
# `da_verify`'s loops by region

Row `g^j` of `__loop88` stores `prefix_bases[g^j]` (word `P + j`); of `__loop89`, `rowbase[g^j]`
(`B + j`) and the chain's first cell (`A + 129j`); of `__loop92`, it reads `rowbase[g^j]` and
the chain's last cell (`A + 129j + 128`); of `__loop93`, `prefix_bases[g^j]`, the row's 128 prefix
cells (`D + 128j + k`) and its leaf (`T + 2j`, `T + 2j + 1`); padding row `g^d` of `__loop94`
stores its leaf (`T + 2(r + d)`, `T + 2(r + d) + 1`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem tail_iff {σ : Val} {c a w : V} {j n : ℕ} (hj : j < n) (hn : n < 2 ^ 33)
    (hc : σ c = σ a + σ w) (ha : σ a = gen ^ (j + 1)) (hw : σ w = gen ^ n) : σ c ≠ 0 ↔ j + 1 < n := by
  rw [hc, ha, hw, ne_eq, e_add_eq_zero_iff]
  exact ⟨fun h => by by_contra h'; exact h (by rw [show j + 1 = n by omega]),
    fun h he => by have := gen_pow_inj' (by omega) (by omega) he; omega⟩

theorem gen_mul_w2 {σ : Val} {x y : V} {j : ℕ} (hx : σ x = gen ^ j) (hy : σ y = word 2 0 0) :
    σ x * σ y = gen ^ (j + 1) := by rw [hx, hy, word_gen, pow_succ]

/-! ## `__loop88` -/

def R88 (r P : ℕ) (i : ℕ) : Prop := ∃ j < r, i = P + j

theorem l88_relInT (fs : String → ℕ) {rd : Reader} {r P D : ℕ} {R : ℕ → Prop} (hr : r < 2 ^ 33)
    (hR : ∀ i, R88 r P i → R i) {j : ℕ} (hj : j < r)
    (h : coreProgram.Rel rd "__loop88" [gen ^ j, gen ^ r, gen ^ P, gen ^ D] []) :
    RelInTW fs rd R ((r - j) * fs "__loop88" + fs "__loop88") "__loop88" [gen ^ j, gen ^ r, gen ^ P, gen ^ D] []
      fun θ => (r - j) * θ "__loop88" + θ "__loop88" := by
  refine loop_relInT fs (pre := l88Body.dropLast) (c := .n 15) (targs := [.n 17, .n 1, .n 2, .n 3])
    (ps := [gen ^ r, gen ^ P, gen ^ D]) find_l88 rfl rfl rfl rfl hr (fun j hj σ hp hok => ?_) hj h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3⟩ := hp
  have hA : ∀ {x : Atom}, Stmt.atom x ∈ l88Body.dropLast → x.Holds rd σ := fun hx => atom_holds_of_ok hx hok
  have m12 : σ (.n 12) = σ (.n 2) * σ (.n 0) := hA (x := .mul (.n 12) (.n 2) (.n 0)) (by simp [l88Body])
  have c13 : σ (.n 13) = word 2 0 0 := hA (x := .const (.n 13) (word 2 0 0)) (by simp [l88Body])
  have m14 : σ (.n 14) = σ (.n 0) * σ (.n 13) := hA (x := .mul (.n 14) (.n 0) (.n 13)) (by simp [l88Body])
  have a15 : σ (.n 15) = σ (.n 14) + σ (.n 1) := hA (x := .add (.n 15) (.n 14) (.n 1)) (by simp [l88Body])
  have c16 : σ (.n 16) = word 2 0 0 := hA (x := .const (.n 16) (word 2 0 0)) (by simp [l88Body])
  have m17 : σ (.n 17) = σ (.n 0) * σ (.n 16) := hA (x := .mul (.n 17) (.n 0) (.n 16)) (by simp [l88Body])
  refine ⟨fun A hA' => ?_, tail_iff hj hr a15 (by rw [m14, gen_mul_w2 h0 c13]) h1, ?_⟩
  · rw [loadAddrs_straight σ _ rfl, show l88Body.dropLast.filterMap stmtLoad? = [(.n 12, 0)] from rfl] at hA'
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hA'
    subst hA'
    exact ⟨P + j, by rw [m12, h2, h0, ← pow_add, addr_gen, Nat.add_zero], hR _ ⟨j, hj, rfl⟩⟩
  · simp only [List.map_cons, List.map_nil, m17, gen_mul_w2 h0 c16, h1, h2, h3]

/-! ## `__loop89` -/

def R89 (r A B : ℕ) (i : ℕ) : Prop := ∃ j < r, i = B + j ∨ i = A + 129 * j

theorem l89_relInT (fs : String → ℕ) {rd : Reader} {r A B : ℕ} {R : ℕ → Prop} (hr : r < 2 ^ 33)
    (hR : ∀ i, R89 r A B i → R i) {j : ℕ} (hj : j < r)
    (h : coreProgram.Rel rd "__loop89" [gen ^ j, gen ^ r, gen ^ A, gen ^ B] []) :
    RelInTW fs rd R ((r - j) * fs "__loop89" + fs "__loop89") "__loop89" [gen ^ j, gen ^ r, gen ^ A, gen ^ B] []
      fun θ => (r - j) * θ "__loop89" + θ "__loop89" := by
  refine loop_relInT fs (pre := l89Body.dropLast) (c := .n 17) (targs := [.n 19, .n 1, .n 2, .n 3])
    (ps := [gen ^ r, gen ^ A, gen ^ B]) find_l89 rfl rfl rfl rfl hr (fun j hj σ hp hok => ?_) hj h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3⟩ := hp
  have hA : ∀ {x : Atom}, Stmt.atom x ∈ l89Body.dropLast → x.Holds rd σ := fun hx => atom_holds_of_ok hx hok
  have m4 : σ (.n 4) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 4) (.n 0) (.n 0)) (by simp [l89Body])
  have m5 : σ (.n 5) = σ (.n 4) * σ (.n 4) := hA (x := .mul (.n 5) (.n 4) (.n 4)) (by simp [l89Body])
  have m6 : σ (.n 6) = σ (.n 5) * σ (.n 5) := hA (x := .mul (.n 6) (.n 5) (.n 5)) (by simp [l89Body])
  have m7 : σ (.n 7) = σ (.n 6) * σ (.n 6) := hA (x := .mul (.n 7) (.n 6) (.n 6)) (by simp [l89Body])
  have m8 : σ (.n 8) = σ (.n 7) * σ (.n 7) := hA (x := .mul (.n 8) (.n 7) (.n 7)) (by simp [l89Body])
  have m9 : σ (.n 9) = σ (.n 8) * σ (.n 8) := hA (x := .mul (.n 9) (.n 8) (.n 8)) (by simp [l89Body])
  have m10 : σ (.n 10) = σ (.n 9) * σ (.n 9) := hA (x := .mul (.n 10) (.n 9) (.n 9)) (by simp [l89Body])
  have m11 : σ (.n 11) = σ (.n 10) * σ (.n 0) := hA (x := .mul (.n 11) (.n 10) (.n 0)) (by simp [l89Body])
  have m12 : σ (.n 12) = σ (.n 2) * σ (.n 11) := hA (x := .mul (.n 12) (.n 2) (.n 11)) (by simp [l89Body])
  have m13 : σ (.n 13) = σ (.n 3) * σ (.n 0) := hA (x := .mul (.n 13) (.n 3) (.n 0)) (by simp [l89Body])
  have c15 : σ (.n 15) = word 2 0 0 := hA (x := .const (.n 15) (word 2 0 0)) (by simp [l89Body])
  have m16 : σ (.n 16) = σ (.n 0) * σ (.n 15) := hA (x := .mul (.n 16) (.n 0) (.n 15)) (by simp [l89Body])
  have a17 : σ (.n 17) = σ (.n 16) + σ (.n 1) := hA (x := .add (.n 17) (.n 16) (.n 1)) (by simp [l89Body])
  have c18 : σ (.n 18) = word 2 0 0 := hA (x := .const (.n 18) (word 2 0 0)) (by simp [l89Body])
  have m19 : σ (.n 19) = σ (.n 0) * σ (.n 18) := hA (x := .mul (.n 19) (.n 0) (.n 18)) (by simp [l89Body])
  have g12 : σ (.n 12) = gen ^ (A + 129 * j) := by
    rw [m12, m11, m10, m9, m8, m7, m6, m5, m4, h2, h0]; ring
  refine ⟨fun A' hA' => ?_, tail_iff hj hr a17 (by rw [m16, gen_mul_w2 h0 c15]) h1, ?_⟩
  · rw [loadAddrs_straight σ _ rfl,
      show l89Body.dropLast.filterMap stmtLoad? = [(.n 13, 0), (.n 12, 0)] from rfl] at hA'
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA'
    rcases hA' with rfl | rfl
    · exact ⟨B + j, by rw [m13, h3, h0, ← pow_add, addr_gen, Nat.add_zero], hR _ ⟨j, hj, Or.inl rfl⟩⟩
    · exact ⟨A + 129 * j, by rw [g12, addr_gen, Nat.add_zero], hR _ ⟨j, hj, Or.inr rfl⟩⟩
  · simp only [List.map_cons, List.map_nil, m19, gen_mul_w2 h0 c18, h1, h2, h3]

/-! ## `__loop92` -/

def R92 (r A B : ℕ) (i : ℕ) : Prop := ∃ j < r, i = B + j ∨ i = A + 129 * j + 128

theorem l92_relInT (fs : String → ℕ) {rd : Reader} {r A B : ℕ} {R : ℕ → Prop} (hr : r < 2 ^ 33)
    (hrb : ∀ j < r, rd (gpow (B + j)) = some (gen ^ (A + 129 * j)))
    (hR : ∀ i, R92 r A B i → R i) {j : ℕ} (hj : j < r)
    (h : coreProgram.Rel rd "__loop92" [gen ^ j, gen ^ r, gen ^ B] []) :
    RelInTW fs rd R ((r - j) * fs "__loop92" + fs "__loop92") "__loop92" [gen ^ j, gen ^ r, gen ^ B] []
      fun θ => (r - j) * θ "__loop92" + θ "__loop92" := by
  refine loop_relInT fs (pre := l92Body.dropLast) (c := .n 9) (targs := [.n 11, .n 1, .n 2])
    (ps := [gen ^ r, gen ^ B]) find_l92 rfl rfl rfl rfl hr (fun j hj σ hp hok => ?_) hj h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2⟩ := hp
  have hA : ∀ {x : Atom}, Stmt.atom x ∈ l92Body.dropLast → x.Holds rd σ := fun hx => atom_holds_of_ok hx hok
  have m3 : σ (.n 3) = σ (.n 2) * σ (.n 0) := hA (x := .mul (.n 3) (.n 2) (.n 0)) (by simp [l92Body])
  have l4 : LoadHolds rd (σ (.n 3)) 0 (σ (.n 4)) := hA (x := .load (.n 4) (.n 3) 0) (by simp [l92Body])
  have c7 : σ (.n 7) = word 2 0 0 := hA (x := .const (.n 7) (word 2 0 0)) (by simp [l92Body])
  have m8 : σ (.n 8) = σ (.n 0) * σ (.n 7) := hA (x := .mul (.n 8) (.n 0) (.n 7)) (by simp [l92Body])
  have a9 : σ (.n 9) = σ (.n 8) + σ (.n 1) := hA (x := .add (.n 9) (.n 8) (.n 1)) (by simp [l92Body])
  have c10 : σ (.n 10) = word 2 0 0 := hA (x := .const (.n 10) (word 2 0 0)) (by simp [l92Body])
  have m11 : σ (.n 11) = σ (.n 0) * σ (.n 10) := hA (x := .mul (.n 11) (.n 0) (.n 10)) (by simp [l92Body])
  have g3 : σ (.n 3) = gen ^ (B + j) := by rw [m3, h2, h0, ← pow_add]
  have g4 : σ (.n 4) = gen ^ (A + 129 * j) := by
    have := load_rd l4
    rw [g3, addr_gen, Nat.add_zero] at this
    exact Option.some.inj (this.symm.trans (hrb j hj))
  refine ⟨fun A' hA' => ?_, tail_iff hj hr a9 (by rw [m8, gen_mul_w2 h0 c7]) h1, ?_⟩
  · rw [loadAddrs_straight σ _ rfl,
      show l92Body.dropLast.filterMap stmtLoad? = [(.n 3, 0), (.n 4, 128)] from rfl] at hA'
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA'
    rcases hA' with rfl | rfl
    · exact ⟨B + j, by rw [g3, addr_gen, Nat.add_zero], hR _ ⟨j, hj, Or.inl rfl⟩⟩
    · exact ⟨A + 129 * j + 128, by rw [g4, addr_gen], hR _ ⟨j, hj, Or.inr rfl⟩⟩
  · simp only [List.map_cons, List.map_nil, m11, gen_mul_w2 h0 c10, h1, h2]

/-! ## `__loop94` -/

def R94 (G T r : ℕ) (i : ℕ) : Prop := ∃ d < G, i = T + 2 * (r + d) ∨ i = T + 2 * (r + d) + 1

theorem l94_relInT (fs : String → ℕ) {rd : Reader} {G T r : ℕ} {R : ℕ → Prop} (hG : G < 2 ^ 33)
    (hR : ∀ i, R94 G T r i → R i) {d : ℕ} (hd : d < G)
    (h : coreProgram.Rel rd "__loop94" [gen ^ d, gen ^ G, gen ^ T, gen ^ r] []) :
    RelInTW fs rd R ((G - d) * fs "__loop94" + fs "__loop94") "__loop94" [gen ^ d, gen ^ G, gen ^ T, gen ^ r] []
      fun θ => (G - d) * θ "__loop94" + θ "__loop94" := by
  refine loop_relInT fs (pre := l94Body.dropLast) (c := .n 12) (targs := [.n 14, .n 1, .n 2, .n 3])
    (ps := [gen ^ G, gen ^ T, gen ^ r]) find_l94 rfl rfl rfl rfl hG (fun d hd σ hp hok => ?_) hd h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3⟩ := hp
  have hA : ∀ {x : Atom}, Stmt.atom x ∈ l94Body.dropLast → x.Holds rd σ := fun hx => atom_holds_of_ok hx hok
  have m4 : σ (.n 4) = σ (.n 3) * σ (.n 3) := hA (x := .mul (.n 4) (.n 3) (.n 3)) (by simp [l94Body])
  have m5 : σ (.n 5) = σ (.n 2) * σ (.n 4) := hA (x := .mul (.n 5) (.n 2) (.n 4)) (by simp [l94Body])
  have m6 : σ (.n 6) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 6) (.n 0) (.n 0)) (by simp [l94Body])
  have m7 : σ (.n 7) = σ (.n 5) * σ (.n 6) := hA (x := .mul (.n 7) (.n 5) (.n 6)) (by simp [l94Body])
  have c10 : σ (.n 10) = word 2 0 0 := hA (x := .const (.n 10) (word 2 0 0)) (by simp [l94Body])
  have m11 : σ (.n 11) = σ (.n 0) * σ (.n 10) := hA (x := .mul (.n 11) (.n 0) (.n 10)) (by simp [l94Body])
  have a12 : σ (.n 12) = σ (.n 11) + σ (.n 1) := hA (x := .add (.n 12) (.n 11) (.n 1)) (by simp [l94Body])
  have c13 : σ (.n 13) = word 2 0 0 := hA (x := .const (.n 13) (word 2 0 0)) (by simp [l94Body])
  have m14 : σ (.n 14) = σ (.n 0) * σ (.n 13) := hA (x := .mul (.n 14) (.n 0) (.n 13)) (by simp [l94Body])
  have g7 : σ (.n 7) = gen ^ (T + 2 * (r + d)) := by rw [m7, m6, m5, m4, h0, h2, h3]; ring
  refine ⟨fun A' hA' => ?_, tail_iff hd hG a12 (by rw [m11, gen_mul_w2 h0 c10]) h1, ?_⟩
  · rw [loadAddrs_straight σ _ rfl,
      show l94Body.dropLast.filterMap stmtLoad? = [(.n 7, 0), (.n 7, 1)] from rfl] at hA'
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA'
    rcases hA' with rfl | rfl
    · exact ⟨_, by rw [g7, addr_gen, Nat.add_zero], hR _ ⟨d, hd, Or.inl rfl⟩⟩
    · exact ⟨_, by rw [g7, addr_gen], hR _ ⟨d, hd, Or.inr rfl⟩⟩
  · simp only [List.map_cons, List.map_nil, m14, gen_mul_w2 h0 c13, h1, h2, h3]

/-! ## `__loop93` -/

def R93 (r P D T : ℕ) (i : ℕ) : Prop :=
  ∃ j < r, i = P + j ∨ (D + 128 * j ≤ i ∧ i < D + 128 * j + 128) ∨ i = T + 2 * j ∨ i = T + 2 * j + 1

/-- `__loop93`'s statements before its return. -/
def rhPre : List Stmt := rhAtoms.map .atom ++ [.callIf (.n 236) "__loop93" [.n 238, .n 1, .n 2, .n 3]]

theorem rh_loads : rhPre.filterMap stmtLoad? =
    [(.n 4, 0)] ++ (List.range 128).map (fun k => (.n 5, k)) ++ [(.n 233, 0), (.n 233, 1)] := by
  decide +kernel

theorem l93_relInT (fs : String → ℕ) {rd : Reader} {r P D T : ℕ} {R : ℕ → Prop} (hr : r < 2 ^ 33)
    (hpb : ∀ j < r, rd (gpow (P + j)) = some (gen ^ (D + 128 * j)))
    (hR : ∀ i, R93 r P D T i → R i) {j : ℕ} (hj : j < r)
    (h : coreProgram.Rel rd "__loop93" [gen ^ j, gen ^ r, gen ^ P, gen ^ T] []) :
    RelInTW fs rd R ((r - j) * fs "__loop93" + fs "__loop93") "__loop93" [gen ^ j, gen ^ r, gen ^ P, gen ^ T] []
      fun θ => (r - j) * θ "__loop93" + θ "__loop93" := by
  have hs : rhPre.all Main.Stmt.straight = true := by simp [rhPre, Main.Stmt.straight]
  refine loop_relInT fs (pre := rhPre) (c := .n 236) (targs := [.n 238, .n 1, .n 2, .n 3])
    (ps := [gen ^ r, gen ^ P, gen ^ T]) find_l93 (by simp [rhBody, rhPre]) hs
    (by rw [rhPre, List.filterMap_append, show (rhAtoms.map Stmt.atom).filterMap Main.Stmt.callS = [] by
      rw [List.filterMap_map]; simp [Function.comp_def, Main.Stmt.callS]]; rfl)
    (by rw [rhPre, List.filterMap_append, show (rhAtoms.map Stmt.atom).filterMap Main.Stmt.allocSz = [] by
      decide +kernel]; rfl) hr (fun j hj σ hp hok => ?_) hj h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3⟩ := hp
  have hA : ∀ {x : Atom}, x ∈ rhAtoms → x.Holds rd σ := fun hx =>
    atom_holds_of_ok (List.mem_append_left _ (List.mem_map.mpr ⟨_, hx, rfl⟩)) hok
  have m4 : σ (.n 4) = σ (.n 2) * σ (.n 0) := hA (x := .mul (.n 4) (.n 2) (.n 0)) (by simp [rhAtoms])
  have l5 : LoadHolds rd (σ (.n 4)) 0 (σ (.n 5)) := hA (x := .load (.n 5) (.n 4) 0) (by simp [rhAtoms])
  have m232 : σ (.n 232) = σ (.n 0) * σ (.n 0) := hA (x := .mul (.n 232) (.n 0) (.n 0)) (by simp [rhAtoms])
  have m233 : σ (.n 233) = σ (.n 3) * σ (.n 232) := hA (x := .mul (.n 233) (.n 3) (.n 232)) (by simp [rhAtoms])
  have c234 : σ (.n 234) = word 2 0 0 := hA (x := .const (.n 234) (word 2 0 0)) (by simp [rhAtoms])
  have m235 : σ (.n 235) = σ (.n 0) * σ (.n 234) := hA (x := .mul (.n 235) (.n 0) (.n 234)) (by simp [rhAtoms])
  have a236 : σ (.n 236) = σ (.n 235) + σ (.n 1) := hA (x := .add (.n 236) (.n 235) (.n 1)) (by simp [rhAtoms])
  have c237 : σ (.n 237) = word 2 0 0 := hA (x := .const (.n 237) (word 2 0 0)) (by simp [rhAtoms])
  have m238 : σ (.n 238) = σ (.n 0) * σ (.n 237) := hA (x := .mul (.n 238) (.n 0) (.n 237)) (by simp [rhAtoms])
  have g4 : σ (.n 4) = gen ^ (P + j) := by rw [m4, h2, h0, ← pow_add]
  have g5 : σ (.n 5) = gen ^ (D + 128 * j) := by
    have := load_rd l5
    rw [g4, addr_gen, Nat.add_zero] at this
    exact Option.some.inj (this.symm.trans (hpb j hj))
  have g233 : σ (.n 233) = gen ^ (T + 2 * j) := by rw [m233, m232, h3, h0]; ring
  refine ⟨fun A' hA' => ?_, tail_iff hj hr a236 (by rw [m235, gen_mul_w2 h0 c234]) h1, ?_⟩
  · rw [loadAddrs_straight σ _ hs, rh_loads] at hA'
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map, List.mem_range, Function.comp_apply] at hA'
    rcases hA' with (rfl | ⟨k, hk, rfl⟩) | rfl | rfl
    · exact ⟨P + j, by rw [g4, addr_gen, Nat.add_zero], hR _ ⟨j, hj, Or.inl rfl⟩⟩
    · exact ⟨D + 128 * j + k, by rw [g5, addr_gen], hR _ ⟨j, hj, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩⟩
    · exact ⟨T + 2 * j, by rw [g233, addr_gen, Nat.add_zero], hR _ ⟨j, hj, Or.inr (Or.inr (Or.inl rfl))⟩⟩
    · exact ⟨T + 2 * j + 1, by rw [g233, addr_gen], hR _ ⟨j, hj, Or.inr (Or.inr (Or.inr rfl))⟩⟩
  · simp only [List.map_cons, List.map_nil, m238, gen_mul_w2 h0 c237, h1, h2, h3]

/-! ## `da_row_shape` -/

/-- `da_row_shape`'s atoms. -/
def drsAtoms : List Atom :=
  [.const (.n 3) (word 1 0 0), .add (.n 4) (.n 0) (.n 3), .hint (.inverse (.n 4) (.n 5)),
    .assertNe (.n 4) (.n 5) (.n 6), .const (.n 7) (word 281474976776218 0 0),
    .rangeCheck (.n 0) (.n 8) (.n 9) (.n 10) (.n 7), .const (.n 11) (word 1024 0 0),
    .rangeCheck (.n 1) (.n 12) (.n 13) (.n 14) (.n 11), .mul (.n 15) (.n 2) (.n 1),
    .load (.n 16) (.n 15) 0, .mul (.n 16) (.n 17) (.n 0), .const (.n 18) (word 281474976776218 0 0),
    .rangeCheck (.n 17) (.n 19) (.n 20) (.n 21) (.n 18), .const (.n 22) (word 140737488388109 0 0),
    .mul (.n 23) (.n 0) (.n 0), .const (.n 24) (word 2 0 0), .mul (.n 25) (.n 16) (.n 24),
    .mul (.n 23) (.n 26) (.n 25), .rangeCheck (.n 26) (.n 27) (.n 28) (.n 29) (.n 22),
    .copy (.n 30) (.n 16), .copy (.n 31) (.n 17)]

theorem drsBody_eq : drsBody = drsAtoms.map .atom ++ [.ret [.n 30, .n 31]] := rfl

/-- **`da_row_shape(n_blob, g^lp, gsq)` loads `g_squares[lp]`** only. -/
theorem drs_relInT (fs : String → ℕ) {rd : Reader} {R : ℕ → Prop} {nb gsq : E} {lp : ℕ}
    (hR : ∃ i, (gsq * gen ^ lp).limb 0 * gpow 0 = gpow i ∧ R i)
    {rets : List E} (h : coreProgram.Rel rd "da_row_shape" [nb, gen ^ lp, gsq] rets) :
    RelInTW fs rd R (fs "da_row_shape") "da_row_shape" [nb, gen ^ lp, gsq] rets fun θ => θ "da_row_shape" := by
  refine relInTW_of_inv fs (fun f args => f = "da_row_shape" ∧ args = [nb, gen ^ lp, gsq]) (fun θ f _ => θ f)
    (fun f args σ fn es vs hI hf hp hw hok => ?_) ⟨rfl, rfl⟩ h
  obtain ⟨rfl, rfl⟩ := hI
  rw [find_da_row_shape, Option.some.injEq] at hf
  subst hf
  rw [drsBody_eq, walk_atoms] at hw
  obtain ⟨rfl, -⟩ : drsAtoms.map Ev.atom = es ∧ _ := by injection hw; exact ⟨by assumption, by assumption⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨-, h1, h2⟩ := hp
  have m15 : σ (.n 15) = σ (.n 2) * σ (.n 1) :=
    (hok _ (List.mem_map.mpr ⟨.mul (.n 15) (.n 2) (.n 1), by simp [drsAtoms], rfl⟩)).1
  refine ⟨fun A hA => ?_, fun c hc => by rw [calls_atoms] at hc; simp at hc, ?_⟩
  · rw [loadAddrs_atoms, show drsAtoms.filterMap atomLoad? = [(.n 15, 0)] by decide +kernel] at hA
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hA
    subst hA
    obtain ⟨i, hi, hRi⟩ := hR
    exact ⟨i, by rw [m15, h2, h1, hi], hRi⟩
  · intro θ
    rw [calls_atoms, allocs_atoms σ (by decide +kernel)]
    simp [callsTot]

end
end LeanVM.Guest.B1.Digest
