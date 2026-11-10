/-
  LeanVM.Guest.B1.Da.Offsets

  `da_column_offsets`' template, its loops' and its meaning (G:4467-4485).
-/

module

public import LeanVM.Guest.B1.Da.Help

/-!
# `da_column_offsets` (G:4467-4485)

`da_column_offsets(zs)` (`core32`): a heap run `offsets` (`.n 1`, `1024` words) whose first eight
words are zero; then for each bit `b < 7` of the cell index a run `steps` (`.n (offB b)`, eight
words), `steps[j] = zs[j] · Ŵ_j(e_(8 + b))` (`DA_VHAT_COLUMN[8b + j]`, here `offC b j`, read off
`wK`), and the loop `__loop{22 + b}` (`core{379 + b}`) over `h < 2^b`, which writes
`offsets[8 (h + 2^b) + j] = offsets[8 h + j] + steps[j]`. The body is the template `offP`
(`offOk`), each loop's block `offLoopA b` (`offLoopOk`), both checked by kernel evaluation in
`OffsetsChk`. Since `Ŵ_j` is additive over the bits of its point (`wK_two_pow_add`), induction on
`h` gives `offsets[8h + j] = zs[j] · Ŵ_j(256 h)` (`da_column_offsets_val`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## `wK` is additive over disjoint bits -/

theorem wK_zero (j : ℕ) : wK j 0 = 0 := by
  unfold wK
  refine List.sum_eq_zero fun v hv ↦ ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hv
  simp

/-- **`Ŵ_j` is additive**: a top bit `2^n` above `x` adds its value. -/
theorem wK_two_pow_add (j : ℕ) {n x : ℕ} (hx : x < 2 ^ n) :
    wK j (2 ^ n + x) = wK j x + wK j (2 ^ n) := by
  unfold wK
  rw [← List.sum_map_add]
  refine congrArg _ (List.map_congr_left fun c _ ↦ ?_)
  rw [show 2 ^ n + x = 2 ^ n * 1 + x by ring, Nat.testBit_two_pow_mul_add 1 hx, Nat.testBit_two_pow]
  by_cases hc : c < n
  · simp [hc, show n ≠ c by omega]
  · rw [testBit_lt_eq_false hx (by omega)]
    by_cases hcn : c = n
    · subst hcn; simp
    · simp [hc, Ne.symm hcn, show c - n ≠ 0 by omega, Nat.testBit_one_eq_true_iff_self_eq_zero]

/-! ## The template -/

/-- The run `steps` of bit `b`. -/
def offB (b : ℕ) : ℕ := 10 + 30 * b

/-- `DA_VHAT_COLUMN[8b + j]`: `Ŵ_j(e_(8 + b))` as a word. -/
def offC (b j : ℕ) : ℕ := (wK j (2 ^ (8 + b))).toBitVec.toNat

/-- `g^(2^b)` as a word, `b < 7`. -/
def offN (b : ℕ) : ℕ := [2, 4, 16, 256, 65536, 4294967296, 27].getD b 0

/-- The name of bit `b`'s loop. -/
def offLoopName (b : ℕ) : String :=
  ["__loop26", "__loop27", "__loop28", "__loop29", "__loop30", "__loop31", "__loop32"].getD b ""

/-- The zero at `offsets[j]`. -/
def offZeroA (j : ℕ) : List Atom := [.const (.n (2 + j)) (word 0 0), .load (.n (2 + j)) (.n 1) j]

/-- `steps[j]` of bit `b`. -/
def offStepA (b j : ℕ) : List Atom :=
  let v := offB b + 1 + 3 * j
  [.load (.n v) (.n 0) j, .const (.n (v + 1)) (word (offC b j) 0), .mul (.n (v + 2)) (.n v) (.n (v + 1)),
    .load (.n (v + 2)) (.n (offB b)) j]

/-- Bit `b`'s statements: its run `steps`, its loop's guard and call. -/
def offBlockS (b : ℕ) : List Stmt :=
  (.atom (.hint (.alloc (.n (offB b)) 8)) :: ((List.range 8).flatMap (offStepA b)).map .atom) ++
    [.atom (.const (.n (offB b + 25)) (word 1 0)), .atom (.const (.n (offB b + 26)) (word (offN b) 0)),
      .atom (.add (.n (offB b + 27)) (.n (offB b + 25)) (.n (offB b + 26))),
      .atom (.const (.n (offB b + 28)) (word 1 0)), .atom (.const (.n (offB b + 29)) (word (offN b) 0)),
      .callIf (.n (offB b + 27)) (offLoopName b) [.n (offB b + 28), .n (offB b + 29), .n 1, .n (offB b)]]

/-- **`da_column_offsets`' block** (its body but the final `ret`). -/
def offP : List Stmt :=
  (.atom (.hint (.alloc (.n 1) 1024)) :: ((List.range 8).flatMap offZeroA).map .atom) ++
    (List.range 7).flatMap offBlockS ++ [.atom (.copy (.n 220) (.n 1))]

/-- **`da_column_offsets`' body, checked.** -/
def offOk (fn : Fn) : Bool :=
  decide (fn.params = [.n 0]) && stmtsEqb fn.body (offP ++ [.ret [.n 220]]) && offP.all Stmt.flat &&
    (List.range 7).all fun b ↦ decide (K.ofBits (offN b) = addressOfIndex (2 ^ b))

/-- Bit `b`'s loop block: `offsets·x^8`, then `dst[j] = src[j] + steps[j]` at `8·2^b` further. -/
def offLoopA (b : ℕ) : List Atom :=
  [.mul (.n 4) (.n 0) (.n 0), .mul (.n 5) (.n 4) (.n 4), .mul (.n 6) (.n 5) (.n 5),
    .mul (.n 7) (.n 2) (.n 6)] ++
  (List.range 8).flatMap (fun j ↦ [.load (.n (8 + 3 * j)) (.n 7) j, .load (.n (9 + 3 * j)) (.n 3) j,
    .add (.n (10 + 3 * j)) (.n (8 + 3 * j)) (.n (9 + 3 * j)),
    .load (.n (10 + 3 * j)) (.n 7) (8 * 2 ^ b + j)]) ++
  [.const (.n 32) (word 2 0), .mul (.n 33) (.n 0) (.n 32), .add (.n 34) (.n 33) (.n 1),
    .const (.n 35) (word 2 0), .mul (.n 36) (.n 0) (.n 35)]

/-- **Bit `b`'s loop, checked.** -/
def offLoopOk (fn : Fn) (b : ℕ) : Bool :=
  loopShapeF fn (offLoopName b) && decide (fn.params.length = 4) &&
    atomsEqb (atomsIn (loopPre fn)) (offLoopA b)

/-! ## The loops -/

theorem atom_mem_holds {C : CallRel} {P : List Stmt} {kret : List E → Prop}
    (hall : ∀ s ∈ P, Stmt.Holds C rd σ s True kret) {a : Atom} (h : Stmt.atom a ∈ P) :
    a.Holds rd σ := (hall _ h).1

/-- **A run of bit `b`'s loop at `x`**: `offsets[8·2^b + j]` through `offsets·x^8` is its word
`j`'s plus `steps[j]`. -/
theorem off_loop_step {b : ℕ} (hb : b < 7) (hok : offLoopOk (coreProgram.getD (436 + b) default) b = true)
    (hidx : coreProgram.indexOf? (offLoopName b) = some (436 + b)) {x : E} {ps : List E}
    (h : coreProgram.Rel rd (offLoopName b) (x :: ps) []) :
    (∀ N off st, ps = [N, off, st] → ∀ j < 8, ∃ a s, LoadHolds rd (off * x ^ 8) j a ∧
      LoadHolds rd st j s ∧ LoadHolds rd (off * x ^ 8) (8 * 2 ^ b + j) (a + s)) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd (offLoopName b) (x * gen :: ps) []) := by
  simp only [offLoopOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hshape, hlen⟩, hat0⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ :=
    loop_stepF (find_of_idx hidx (by rw [coreProgram_length]; omega)) hshape h
  refine ⟨fun N off st hN j hj ↦ ?_, hnext⟩
  have hat := atoms_of_flat hall
  rw [atomsEqb_sound hat0] at hat
  have hpar : (coreProgram.getD (436 + b) default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3⟩ := hps
  have hm : ∀ a ∈ [Atom.mul (.n 4) (.n 0) (.n 0), .mul (.n 5) (.n 4) (.n 4), .mul (.n 6) (.n 5) (.n 5),
      .mul (.n 7) (.n 2) (.n 6)], a.Holds rd σ := fun a ha ↦
    hat a (List.mem_append_left _ (List.mem_append_left _ ha))
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Atom.Holds] at hm
  obtain ⟨m4, m5, m6, m7⟩ := hm
  have h7 : σ (.n 7) = off * x ^ 8 := by
    rw [m7, m6, m5, m4, h2, hx]; ring
  have hj' : ∀ a ∈ [Atom.load (.n (8 + 3 * j)) (.n 7) j, .load (.n (9 + 3 * j)) (.n 3) j,
      .add (.n (10 + 3 * j)) (.n (8 + 3 * j)) (.n (9 + 3 * j)),
      .load (.n (10 + 3 * j)) (.n 7) (8 * 2 ^ b + j)], a.Holds rd σ := fun a ha ↦
    hat a (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ha⟩)))
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    Atom.Holds] at hj'
  obtain ⟨l1, l2, ad, l3⟩ := hj'
  rw [h7] at l1 l3
  rw [h3] at l2
  rw [ad] at l3
  exact ⟨_, _, l1, l2, l3⟩

/-! ## The body -/

theorem mem_offP_zero {j : ℕ} (hj : j < 8) {a : Atom} (ha : a ∈ offZeroA j) : Stmt.atom a ∈ offP :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨a, List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ha⟩, rfl⟩)))

theorem mem_offP_block {b : ℕ} (hb : b < 7) {s : Stmt} (hs : s ∈ offBlockS b) : s ∈ offP :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, List.mem_range.mpr hb, hs⟩))

theorem mem_offBlock_step {b j : ℕ} (hj : j < 8) {a : Atom} (ha : a ∈ offStepA b j) :
    Stmt.atom a ∈ offBlockS b :=
  List.mem_append_left _ (List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨a, List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ha⟩, rfl⟩))

theorem offC_word (b j : ℕ) : word (offC b j) 0 = ofK (wK j (2 ^ (8 + b))) := by
  rw [word_eOfNat, eOfNat, offC]
  congr 1
  simp [K.ofBits]

/-- **`da_column_offsets`' body gives its meaning**, from its loops'. -/
theorem da_column_offsets_val {fn : Fn} (hok : offOk fn = true)
    (hloop : ∀ b < 7, offLoopOk (coreProgram.getD (436 + b) default) b = true)
    (hidx : ∀ b < 7, coreProgram.indexOf? (offLoopName b) = some (436 + b))
    {args rets : List E} (hpar : fn.params.map σ = args)
    (hb : Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs ↦ rs = rets)) :
    MeaningDaColumnOffsets rd args rets := by
  unfold offOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨hparams, hbody⟩, hflat⟩, hN⟩ := hok
  rw [stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hall, hret⟩ := holdsList_flat offP (List.all_eq_true.mpr hflat) _ _ hb
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar hret
  have hcp : σ (.n 220) = σ (.n 1) := atom_mem_holds hall (List.mem_append_right _ (List.mem_singleton_self _))
  simp only [MeaningDaColumnOffsets]
  rw [hcp]
  -- the zeros
  have hz : ∀ j < 8, LoadHolds rd (σ (.n 1)) j 0 := by
    intro j hj
    have c := atom_mem_holds hall (mem_offP_zero hj (a := .const (.n (2 + j)) (word 0 0)) (by simp [offZeroA]))
    have l := atom_mem_holds hall (mem_offP_zero hj (a := .load (.n (2 + j)) (.n 1) j) (by simp [offZeroA]))
    simp only [Atom.Holds] at c l
    rwa [c, word_zero] at l
  -- each bit's steps
  have hs : ∀ b < 7, ∀ j < 8, LoadHolds rd (σ (.n 0)) j (σ (.n (offB b + 1 + 3 * j))) ∧
      LoadHolds rd (σ (.n (offB b))) j (σ (.n (offB b + 1 + 3 * j)) * ofK (wK j (2 ^ (8 + b)))) := by
    intro b hb j hj
    have e := fun a (ha : a ∈ offStepA b j) ↦ atom_mem_holds hall (mem_offP_block hb (mem_offBlock_step hj ha))
    have l1 := e (.load (.n (offB b + 1 + 3 * j)) (.n 0) j) (by simp [offStepA])
    have c := e (.const (.n (offB b + 1 + 3 * j + 1)) (word (offC b j) 0)) (by simp [offStepA])
    have m := e (.mul (.n (offB b + 1 + 3 * j + 2)) (.n (offB b + 1 + 3 * j))
      (.n (offB b + 1 + 3 * j + 1))) (by simp [offStepA])
    have l2 := e (.load (.n (offB b + 1 + 3 * j + 2)) (.n (offB b)) j) (by simp [offStepA])
    simp only [Atom.Holds] at l1 c m l2
    rw [m, c, offC_word] at l2
    exact ⟨l1, l2⟩
  -- the powers
  refine ⟨fun j ↦ σ (.n (offB 0 + 1 + 3 * j)), fun j hj ↦ (hs 0 (by norm_num) j hj).1, ?_⟩
  have hstep : ∀ b < 7, ∀ j < 8, LoadHolds rd (σ (.n (offB b))) j
      (σ (.n (offB 0 + 1 + 3 * j)) * ofK (wK j (2 ^ (8 + b)))) := by
    intro b hb j hj
    have e := loadHolds_unique (hs b hb j hj).1 (hs 0 (by norm_num) j hj).1
    rw [← e]
    exact (hs b hb j hj).2
  -- each bit's loop
  have hloops : ∀ b < 7, ∀ h < 2 ^ b, ∀ j < 8, ∃ a s, LoadHolds rd (σ (.n 1)) (8 * h + j) a ∧
      LoadHolds rd (σ (.n (offB b))) j s ∧ LoadHolds rd (σ (.n 1)) (8 * h + 8 * 2 ^ b + j) (a + s) := by
    intro b hb
    have hNb : word (offN b) 0 = gen ^ 2 ^ b := by
      rw [word_eOfNat, eOfNat, hN b hb, gen_pow_eq_ofK]
    have hblk := fun s (hs : s ∈ offBlockS b) ↦ hall s (mem_offP_block hb hs)
    have c25 := (hblk (.atom (.const (.n (offB b + 25)) (word 1 0))) (by simp [offBlockS])).1
    have c26 := (hblk (.atom (.const (.n (offB b + 26)) (word (offN b) 0))) (by simp [offBlockS])).1
    have a27 := (hblk (.atom (.add (.n (offB b + 27)) (.n (offB b + 25)) (.n (offB b + 26))))
      (by simp [offBlockS])).1
    have c28 := (hblk (.atom (.const (.n (offB b + 28)) (word 1 0))) (by simp [offBlockS])).1
    have c29 := (hblk (.atom (.const (.n (offB b + 29)) (word (offN b) 0))) (by simp [offBlockS])).1
    have ci := (hblk (.callIf (.n (offB b + 27)) (offLoopName b)
      [.n (offB b + 28), .n (offB b + 29), .n 1, .n (offB b)]) (by simp [offBlockS])).2.1
    simp only [Atom.Holds] at c25 c26 a27 c28 c29
    simp only [List.map_cons, List.map_nil] at ci
    rw [c28, c29, word_one, hNb] at ci
    rw [a27, c25, c26, word_one, hNb] at ci
    have hm : 2 ^ b < ordG := by
      have : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
      unfold ordG; omega
    have L := loop_sound (f := offLoopName b) (ps := [gen ^ 2 ^ b, σ (.n 1), σ (.n (offB b))])
      (B := fun x ↦ ∀ j < 8, ∃ a s, LoadHolds rd (σ (.n 1) * x ^ 8) j a ∧
        LoadHolds rd (σ (.n (offB b))) j s ∧
        LoadHolds rd (σ (.n 1) * x ^ 8) (8 * 2 ^ b + j) (a + s)) hm rfl
      (fun x hx ↦ by
        obtain ⟨k1, k2⟩ := off_loop_step hb (hloop b hb) (hidx b hb) hx
        exact ⟨k1 _ _ _ rfl, k2⟩) ci
    intro h hh j hj
    obtain ⟨a, s, l1, l2, l3⟩ := L h hh j hj
    rw [← pow_mul, mul_comm h 8, loadHolds_mul_gen_pow] at l1 l3
    exact ⟨a, s, l1, l2, by rw [show 8 * h + 8 * 2 ^ b + j = 8 * h + (8 * 2 ^ b + j) by ring]; exact l3⟩
  -- the doubling
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro hh j hj
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · simpa [wK_zero, ofK_zero] using hz j hj
    · set b := Nat.log 2 h with hbdef
      have hb2 : 2 ^ b ≤ h := Nat.pow_log_le_self 2 (by omega)
      have hlt : h < 2 ^ (b + 1) := Nat.lt_pow_succ_log_self (by norm_num) h
      have hb7 : b < 7 := by
        by_contra hc
        have : 2 ^ 7 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      set h' := h - 2 ^ b
      have hh' : h' < 2 ^ b := by rw [pow_succ] at hlt; omega
      obtain ⟨a, s, l1, l2, l3⟩ := hloops b hb7 h' hh' j hj
      have ea := loadHolds_unique l1 (ih h' (by omega) (by omega) j hj)
      have es := loadHolds_unique l2 (hstep b hb7 j hj)
      rw [ea, es, show 8 * h' + 8 * 2 ^ b + j = 8 * h + j by omega] at l3
      have hw : wK j (256 * h) = wK j (256 * h') + wK j (2 ^ (8 + b)) := by
        rw [show 256 * h = 2 ^ (8 + b) + 256 * h' by rw [pow_add]; omega]
        exact wK_two_pow_add j (by rw [pow_add]; omega)
      rw [hw, ofK_add, mul_add]
      exact l3

end
end LeanVM.Guest.B1.Da
