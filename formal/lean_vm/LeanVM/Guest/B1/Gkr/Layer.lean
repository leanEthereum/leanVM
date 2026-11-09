/-
  LeanVM.Guest.B1.Gkr.Layer

  A layer of `verify_bus_gkr`'s walk, its loop `__loop6`: one step of two levels of the
  specification's GKR walk, between two layer slots.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop29

/-!
# A layer of two levels (`__loop6`, G:1838-1927)

The template of `__loop6`'s body, from the layer slot at `layers·x_layer^17`: the combiner's
permutation over the slot's capacity and waiting cells, the first round record, the rounds
(`__loop36`, then `gkr_rounds__L{2r}` at the layer index's `r = j % 4`, then `gkr_rounds__L1` at
an odd depth),
the twelve children read, their check, the two new coordinates squeezed, and the next slot
`34` words on.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The first value of child `i`'s read. -/
def lyEv (i : ℕ) : ℕ := if i < 4 then 85 + 11 * i else if i < 8 then 142 + 11 * (i - 4) else 199 + 11 * (i - 8)

/-- Child `i`'s read: `fs_next` at the tail cursor, its word copied. -/
def lyEvT (i : ℕ) : List Stmt :=
  fsNextT (.n 83) i (lyEv i) ++ [.atom (.copy (.n (lyEv i + 10)) (.n (lyEv i)))]

/-- The rate cells of children `4m .. 4m + 3`. -/
def lyRate (m : ℕ) : List V :=
  (List.range 4).flatMap fun i ↦ [.n (lyEv (4 * m + i) + 7), .n (lyEv (4 * m + i) + 9)]

/-- A run of `13` values from `b`. -/
def lyOuts (b : ℕ) : List V := (List.range 13).map fun k ↦ .n (b + k)

/-- The capacity cells among a permutation's outputs from `b`. -/
def lyCap (b : ℕ) : List V := (List.range 5).map fun k ↦ .n (b + 8 + k)

/-- The side `t`'s new value: `lo + c1·(lo + hi)`, its values from `b`. -/
def lyVal (t b off : ℕ) : List Stmt :=
  let e := fun i ↦ lyEv (4 * t + i) + 10
  [.atom (.add (.n b) (.n (e 0)) (.n (e 1))), .atom (.mul (.n (b + 1)) (.n 278) (.n b)),
    .atom (.add (.n (b + 2)) (.n (e 0)) (.n (b + 1))),
    .atom (.add (.n (b + 3)) (.n (e 2)) (.n (e 3))), .atom (.mul (.n (b + 4)) (.n 278) (.n (b + 3))),
    .atom (.add (.n (b + 5)) (.n (e 2)) (.n (b + 4))),
    .atom (.add (.n (b + 6)) (.n (b + 2)) (.n (b + 5))), .atom (.mul (.n (b + 7)) (.n 298) (.n (b + 6))),
    .atom (.add (.n (b + 8)) (.n (b + 2)) (.n (b + 7))), .atom (.load (.n (b + 8)) (.n 16) off)]

/-- `__loop6`'s body. -/
def lyBody : List Stmt :=
  List.flatten [
    [.atom (.mul (.n 7) (.n 0) (.n 0)), .atom (.mul (.n 8) (.n 2) (.n 3)),
      .atom (.load (.n 9) (.n 8) 0), .atom (.mul (.n 10) (.n 7) (.n 9)),
      .atom (.mul (.n 11) (.n 10) (.n 10)), .atom (.mul (.n 12) (.n 11) (.n 11)),
      .atom (.mul (.n 13) (.n 12) (.n 12)), .atom (.mul (.n 14) (.n 13) (.n 13)),
      .atom (.mul (.n 15) (.n 14) (.n 10)), .atom (.mul (.n 16) (.n 4) (.n 15))],
    (List.range 5).map (fun k ↦ .atom (.load (.n (17 + k)) (.n 16) k)),
    (List.range 4).map (fun k ↦ .atom (.load (.n (22 + k)) (.n 16) (13 + k))),
    [.atom (.const (.n 26) (word 1 0 0)), .atom (.const (.n 27) (word 0 0 0)),
      .atom (.const (.n 28) (word 0 0 0)), .atom (.const (.n 29) (word 0 0 0)),
      .atom (.const (.n 30) (word 0 0 0)),
      keccakA ([.n 22, .n 23, .n 24, .n 25, .n 27, .n 28, .n 29, .n 30] ++
        (List.range 5).map fun k ↦ .n (17 + k)) (lyOuts 31)],
    challengeT (.n 31) (.n 32) 44,
    [.atom (.load (.n 51) (.n 16) 9), .atom (.load (.n 52) (.n 16) 10),
      .atom (.mul (.n 53) (.n 5) (.n 52))],
    (List.range 5).map (fun k ↦ .atom (.load (.n (39 + k)) (.n 53) (862 * k))),
    [.atom (.load (.n 54) (.n 16) 5), .atom (.load (.n 54) (.n 53) 4310),
      .atom (.load (.n 55) (.n 16) 6), .atom (.load (.n 56) (.n 16) 7),
      .atom (.load (.n 57) (.n 16) 8), .atom (.mul (.n 58) (.n 50) (.n 57)),
      .atom (.add (.n 59) (.n 56) (.n 58)), .atom (.mul (.n 60) (.n 50) (.n 59)),
      .atom (.add (.n 61) (.n 55) (.n 60)), .atom (.load (.n 61) (.n 53) 5172),
      .atom (.load (.n 62) (.n 16) 11), .atom (.load (.n 63) (.n 16) 12),
      .atom (.const (.n 64) (word 1 0 0)), .atom (.add (.n 65) (.n 64) (.n 62)),
      .atom (.const (.n 66) (word 1 0 0)),
      .callIf (.n 65) "__loop36" [.n 66, .n 62, .n 53, .n 51],
      .atom (.mul (.n 67) (.n 62) (.n 62)), .atom (.mul (.n 68) (.n 67) (.n 67)),
      .atom (.mul (.n 69) (.n 68) (.n 68)), .atom (.mul (.n 70) (.n 53) (.n 69)),
      .atom (.mul (.n 71) (.n 51) (.n 69)),
      .dispatch (.n 63) ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"]
        [.n 70, .n 71] [.n 72],
      .atom (.add (.n 73) (.n 10) (.n 7)),
      .ite (.n 73) [] [.atom (.mul (.n 74) (.n 53) (.n 7)), .atom (.mul (.n 75) (.n 51) (.n 7)),
        .call "gkr_rounds__L1" [.n 74, .n 75] [.n 76]],
      .atom (.mul (.n 77) (.n 53) (.n 10))],
    (List.range 5).map (fun k ↦ .atom (.load (.n (78 + k)) (.n 77) (862 * k))),
    [.atom (.load (.n 83) (.n 77) 4310), .atom (.load (.n 84) (.n 77) 5172)],
    ((List.range 4).map lyEvT).flatten,
    [keccakA (lyRate 0 ++ (List.range 5).map fun k ↦ .n (78 + k)) (lyOuts 129)],
    ((List.range 4).map fun i ↦ lyEvT (4 + i)).flatten,
    [keccakA (lyRate 1 ++ lyCap 129) (lyOuts 186)],
    ((List.range 4).map fun i ↦ lyEvT (8 + i)).flatten,
    [.atom (.mul (.n 243) (.n 209) (.n 220)), .atom (.mul (.n 244) (.n 243) (.n 231)),
      .atom (.mul (.n 245) (.n 244) (.n 242)), .atom (.const (.n 246) (word 0 0 0)),
      .atom (.mul (.n 247) (.n 50) (.n 246)), .atom (.add (.n 248) (.n 245) (.n 247)),
      .atom (.mul (.n 249) (.n 152) (.n 163)), .atom (.mul (.n 250) (.n 249) (.n 174)),
      .atom (.mul (.n 251) (.n 250) (.n 185)), .atom (.mul (.n 252) (.n 50) (.n 248)),
      .atom (.add (.n 253) (.n 251) (.n 252)), .atom (.mul (.n 254) (.n 95) (.n 106)),
      .atom (.mul (.n 255) (.n 254) (.n 117)), .atom (.mul (.n 256) (.n 255) (.n 128)),
      .atom (.mul (.n 257) (.n 50) (.n 253)), .atom (.add (.n 258) (.n 256) (.n 257)),
      .atom (.assertEq (.n 84) (.n 258)),
      keccakA (lyRate 2 ++ lyCap 186) (lyOuts 259)],
    challengeT (.n 259) (.n 260) 272,
    [keccakA ([.n 27, .n 27, .n 27, .n 27, .n 27, .n 28, .n 29, .n 30] ++ lyCap 259) (lyOuts 279)],
    challengeT (.n 279) (.n 280) 292,
    [.atom (.load (.n 278) (.n 51) 40), .atom (.load (.n 298) (.n 51) 41)],
    (List.range 5).map (fun k ↦ .atom (.load (.n (287 + k)) (.n 16) (34 + k))),
    ((List.range 4).map fun k ↦ [.atom (.const (.n (299 + k)) (word 0 0 0)),
      .atom (.load (.n (299 + k)) (.n 16) (47 + k))]).flatten,
    [.atom (.const (.n 303) (word 4096 0 0)), .atom (.mul (.n 304) (.n 83) (.n 303)),
      .atom (.load (.n 304) (.n 16) 39)],
    lyVal 0 305 40,
    lyVal 1 314 41,
    lyVal 2 323 42,
    [.atom (.const (.n 332) (word 1099511627776 0 0)), .atom (.mul (.n 333) (.n 51) (.n 332)),
      .atom (.load (.n 333) (.n 16) 43), .atom (.mul (.n 334) (.n 52) (.n 10)),
      .atom (.const (.n 335) (word 2 0 0)), .atom (.mul (.n 336) (.n 334) (.n 335)),
      .atom (.load (.n 336) (.n 16) 44), .atom (.mul (.n 337) (.n 6) (.n 63)),
      .atom (.load (.n 338) (.n 337) 4), .atom (.mul (.n 339) (.n 62) (.n 338)),
      .atom (.load (.n 339) (.n 16) 45), .atom (.mul (.n 340) (.n 6) (.n 63)),
      .atom (.load (.n 341) (.n 340) 0), .atom (.load (.n 341) (.n 16) 46),
      .atom (.const (.n 342) (word 2 0 0)), .atom (.mul (.n 343) (.n 0) (.n 342)),
      .atom (.add (.n 344) (.n 343) (.n 1)), .atom (.const (.n 345) (word 2 0 0)),
      .atom (.mul (.n 346) (.n 0) (.n 345)),
      .callIf (.n 344) "__loop6" [.n 346, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], .ret []]]

noncomputable def lyCheck : Bool :=
  match coreProgram.find? "__loop6" with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]) && tbStmtsEqb fn.body lyBody
  | none => false

theorem lyCheck_eq : lyCheck = true := by decide +kernel

theorem lyFound : ∃ fn : Fn, coreProgram.find? "__loop6" = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧ fn.body = lyBody := by
  have h := lyCheck_eq
  unfold lyCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- `__loop6`'s statements before its `ret`. -/
def lyPre : List Stmt := lyBody.take 298

theorem lyBody_eq : lyBody = lyPre ++ [.ret []] := tbStmtsEqb_sound (by decide +kernel)

theorem lyPre_noRet : Stmt.noRetList lyPre = true := by decide +kernel

/-! ## The layer slot -/

/-- **The slot of point length `L`** in `layers` (`LAYER_SLOTS = 17`): the carried capacity and the
waiting cells of the sponge `s` (at most two scalars; the cells there, once canonical as the next
permutation asks, are their rate cells), the cursor, the three trees' values, a row holding the
point (of length `L`), the round position, `half` and `parity`. -/
def GkSlot (rd : Reader) (layers : E) (L : ℕ) (s : Fs) (cur : E) (st : GkrState)
    (row pos half parity : E) : Prop :=
  s.cap.length = 5 ∧
    (∀ j < 5, LoadHolds rd layers (17 * L + j) (s.cap.getD j 0)) ∧ s.pend.length ≤ 2 ∧
    (∀ c : ℕ → E, (∀ j < 4, LoadHolds rd layers (17 * L + 13 + j) (c j)) →
      (∀ j < 4, IsCanonical128 (c j)) → ∀ j < 4, c j = (rateOf s.pend).getD j 0) ∧
    LoadHolds rd layers (17 * L + 5) cur ∧ st.values.length = 3 ∧
    (∀ t < 3, LoadHolds rd layers (17 * L + 6 + t) (st.values.getD t 0)) ∧
    LoadHolds rd layers (17 * L + 9) row ∧ st.point.length = L ∧ TbReadsAt rd row st.point ∧
    LoadHolds rd layers (17 * L + 10) pos ∧ LoadHolds rd layers (17 * L + 11) half ∧
    LoadHolds rd layers (17 * L + 12) parity

/-- The table `k_mod_next` (G:1802-1805): at `g^r`, `r < 4`, the next layer index's `g^((r + 1) % 4)`,
and at `g^(4 + r)` its carry into `half`, `g^((r + 1) / 4)`. -/
def KModNext (rd : Reader) (kmn : E) : Prop :=
  ∀ r < 4, LoadHolds rd kmn (4 + r) (gen ^ ((r + 1) / 4)) ∧ LoadHolds rd kmn r (gen ^ ((r + 1) % 4))

/-- **A layer of two levels** at `x = g^j`, the depth's parity `sh` (`depth_shift[g_bus_mu]`):
from the slot of `L = 2j + sh`, its `half = g^(j/4)` and `parity = g^(j % 4)`, the stream runs
`gkrStep 2` to the slot of `L + 2`, the row `40` words on, given the table `k_mod_next`. -/
def LyB (rd : Reader) (dsb gmu layers kmn x : E) : Prop :=
  KModNext rd kmn →
  ∀ j sh : ℕ, x = gen ^ j → LoadHolds rd (dsb * gmu) 0 (gen ^ sh) → j < 2 ^ 30 → sh < 2 →
    ∀ (s : Fs) (cur : E) (st : GkrState) (row pos : E),
      GkSlot rd layers (2 * j + sh) s cur st row pos (gen ^ (j / 4)) (gen ^ (j % 4)) →
      ∃ (xs : List E) (st' : GkrState) (s' : Fs) (pos' : E),
        RunsTo (gkrStep 2 st) s xs st' s' ∧ TbReadsAt rd cur xs ∧ s'.pend = [] ∧
        GkSlot rd layers (2 * j + sh + 2) s' (cur * gen ^ xs.length) st' (row * gen ^ 40) pos'
          (gen ^ ((j + 1) / 4)) (gen ^ ((j + 1) % 4))

/-! ## The layer's head -/

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- A list of length `n` is its `n` entries. -/
theorem tb_eq_map_getD {l : List E} {n : ℕ} (h : l.length = n) :
    l = (List.range n).map (l.getD · 0) := by
  subst h
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- The rate cells of at most two waiting scalars: past the fourth, zeros. -/
theorem rateOf_getD_four {pend : List (E × ℕ)} (h : pend.length ≤ 2) {j : ℕ} (hj : 4 ≤ j)
    (hj8 : j < 8) : (rateOf pend).getD j 0 = 0 := by
  have hl : (pendCells pend).length = 2 * pend.length := by
    simp [pendCells, List.length_flatMap]; omega
  rw [rateOf_eq_cells _ (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), hl, List.getElem?_replicate]
  split <;> rfl

/-- The capacity of a permutation's state is canonical. -/
theorem tb_capOf_canonical (S : KeccakState) : AllCanonical (capOf S) := by
  intro x hx
  simp only [capOf, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact cellsOfState_canonical _ _ _

/-- **The layer's head**: the combiner is the slot's sponge's challenge, and the first round
record carries the sponge after it, the cursor and the combined claim. -/
theorem ly_head (h : Stmt.HoldsList C rd σ lyPre True kret) {j sh : ℕ} (hx : σ (.n 0) = gen ^ j)
    (hsh : LoadHolds rd (σ (.n 2) * σ (.n 3)) 0 (gen ^ sh)) {s : Fs} {cur : E} {st : GkrState}
    {row pos half parity : E}
    (hslot : GkSlot rd (σ (.n 4)) (2 * j + sh) s cur st row pos half parity) :
    σ (.n 7) = gen ^ (2 * j) ∧ σ (.n 10) = gen ^ (2 * j + sh) ∧
      σ (.n 16) = σ (.n 4) * gen ^ (17 * (2 * j + sh)) ∧
      σ (.n 50) = s.squeeze.1 ∧ σ (.n 51) = row ∧ σ (.n 52) = pos ∧
      σ (.n 53) = σ (.n 5) * pos ∧ σ (.n 62) = half ∧ σ (.n 63) = parity ∧
      TbCapAt rd (σ (.n 53)) 0 gkCap s.squeeze.2.cap ∧ AllCanonical s.squeeze.2.cap ∧
      LoadHolds rd (σ (.n 53)) (5 * gkCap) cur ∧
      LoadHolds rd (σ (.n 53)) (6 * gkCap) (polyEval st.values s.squeeze.1) := by
  have hnr := lyPre_noRet
  obtain ⟨hcl, hcap, hpl, hrate, hcur, hvl, hval, hrow, -, -, hpos, hhalf, hpar⟩ := hslot
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have m6 := a 0 (.mul (.n 7) (.n 0) (.n 0)) (by decide +kernel)
  have m7 := a 1 (.mul (.n 8) (.n 2) (.n 3)) (by decide +kernel)
  have l8 := a 2 (.load (.n 9) (.n 8) 0) (by decide +kernel)
  have m9 := a 3 (.mul (.n 10) (.n 7) (.n 9)) (by decide +kernel)
  have m10 := a 4 (.mul (.n 11) (.n 10) (.n 10)) (by decide +kernel)
  have m11 := a 5 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel)
  have m12 := a 6 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel)
  have m13 := a 7 (.mul (.n 14) (.n 13) (.n 13)) (by decide +kernel)
  have m14 := a 8 (.mul (.n 15) (.n 14) (.n 10)) (by decide +kernel)
  have m15 := a 9 (.mul (.n 16) (.n 4) (.n 15)) (by decide +kernel)
  simp only [Atom.Holds] at m6 m7 l8 m9 m10 m11 m12 m13 m14 m15
  rw [← m7] at hsh
  have e8 := tb_loadHolds_unique l8 hsh
  have e6 : σ (.n 7) = gen ^ (2 * j) := by rw [m6, hx, ← pow_add]; ring_nf
  have e9 : σ (.n 10) = gen ^ (2 * j + sh) := by rw [m9, e6, e8, pow_add]
  have e15 : σ (.n 16) = σ (.n 4) * gen ^ (17 * (2 * j + sh)) := by
    rw [m15, m14, m13, m12, m11, m10, e9, ← pow_add, ← pow_add, ← pow_add, ← pow_add]; ring_nf
  set L := 2 * j + sh
  have ld : ∀ k w, LoadHolds rd (σ (.n 16)) k w ↔ LoadHolds rd (σ (.n 4)) (17 * L + k) w := by
    intro k w; rw [e15, tb_loadHolds_mul_gen_pow]
  -- the slot's capacity and waiting cells
  have hcapL := tb_holds_slice hnr h 10 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (17 + k)) (.n 16) k)) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcapL
  have hpendL := tb_holds_slice hnr h 15 ((List.range 4).map fun k ↦
    Stmt.atom (.load (.n (22 + k)) (.n 16) (13 + k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hpendL
  simp only [Atom.Holds] at hcapL hpendL
  have ecap : ∀ k < 5, σ (.n (17 + k)) = s.cap.getD k 0 := fun k hk =>
    tb_loadHolds_unique ((ld k _).mp (hcapL k hk)) (hcap k hk)
  have c26 := a 20 (.const (.n 27) (word 0 0 0)) (by decide +kernel)
  have c27 := a 21 (.const (.n 28) (word 0 0 0)) (by decide +kernel)
  have c28 := a 22 (.const (.n 29) (word 0 0 0)) (by decide +kernel)
  have c29 := a 23 (.const (.n 30) (word 0 0 0)) (by decide +kernel)
  have k1 := a 24 (.keccak ([.n 22, .n 23, .n 24, .n 25, .n 27, .n 28, .n 29, .n 30] ++
      (List.range 5).map fun k ↦ .n (17 + k)) (lyOuts 31) false false) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at c26 c27 c28 c29
  obtain ⟨-, -, hcanI, hout⟩ := keccakA_perm k1
  have epend : ∀ k < 4, σ (.n (22 + k)) = (rateOf s.pend).getD k 0 := by
    refine hrate (fun k ↦ σ (.n (22 + k))) (fun k hk => ?_) (fun k hk => hcanI _ ?_)
    · rw [Nat.add_assoc]; exact (ld (13 + k) _).mp (hpendL k hk)
    · simp only [List.map_append, List.mem_append, List.map_cons, List.mem_cons, List.map_nil]
      left
      interval_cases k <;> simp
  have hrl : (rateOf s.pend).length = 8 := by simp [rateOf]
  have hins : (([.n 22, .n 23, .n 24, .n 25, .n 27, .n 28, .n 29, .n 30] ++
      (List.range 5).map fun k ↦ V.n (17 + k)) : List V).map σ = rateOf s.pend ++ s.cap := by
    rw [tb_eq_map_getD hrl, tb_eq_map_getD hcl]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.cons.injEq, and_true]
    refine ⟨epend 0 (by omega), epend 1 (by omega), epend 2 (by omega), epend 3 (by omega),
      ?_, ?_, ?_, ?_, ecap 0 (by omega), ecap 1 (by omega), ecap 2 (by omega), ecap 3 (by omega),
      ecap 4 (by omega)⟩
    · rw [c26, rateOf_getD_four hpl (by omega) (by omega)]
    · rw [c27, rateOf_getD_four hpl (by omega) (by omega)]
    · rw [c28, rateOf_getD_four hpl (by omega) (by omega)]
    · rw [c29, rateOf_getD_four hpl (by omega) (by omega)]
  rw [hins] at hout
  have hP : ∀ k (hk : k < 13), σ (.n (31 + k)) = cellsOfState s.perm false ⟨k, hk⟩ := by
    intro k hk
    have := outs_eq hout ⟨k, hk⟩ (by simpa [lyOuts] using hk)
    simpa [lyOuts, Fs.perm] using this
  have hch := tb_holds_slice hnr h 25 (challengeT (.n 31) (.n 32) 44) (by decide +kernel)
  rw [holds_challengeT] at hch
  have e49 := challengeT_value hch.1 (hP 0 (by omega)) (hP 1 (by omega))
  -- the slot's row, position, half and parity
  have l50 := a 33 (.load (.n 51) (.n 16) 9) (by decide +kernel)
  have l51 := a 34 (.load (.n 52) (.n 16) 10) (by decide +kernel)
  have m52 := a 35 (.mul (.n 53) (.n 5) (.n 52)) (by decide +kernel)
  have l61 := a 51 (.load (.n 62) (.n 16) 11) (by decide +kernel)
  have l62 := a 52 (.load (.n 63) (.n 16) 12) (by decide +kernel)
  simp only [Atom.Holds] at l50 l51 m52 l61 l62
  have e50 := tb_loadHolds_unique ((ld _ _).mp l50) hrow
  have e51 := tb_loadHolds_unique ((ld _ _).mp l51) hpos
  have e61 := tb_loadHolds_unique ((ld _ _).mp l61) hhalf
  have e62 := tb_loadHolds_unique ((ld _ _).mp l62) hpar
  rw [e51] at m52
  -- the first record
  have hst := tb_holds_slice hnr h 36 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (39 + k)) (.n 53) (862 * k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hst
  simp only [Atom.Holds] at hst
  have l53 := a 41 (.load (.n 54) (.n 16) 5) (by decide +kernel)
  have l53' := a 42 (.load (.n 54) (.n 53) 4310) (by decide +kernel)
  have l54 := a 43 (.load (.n 55) (.n 16) 6) (by decide +kernel)
  have l55 := a 44 (.load (.n 56) (.n 16) 7) (by decide +kernel)
  have l56 := a 45 (.load (.n 57) (.n 16) 8) (by decide +kernel)
  have m57 := a 46 (.mul (.n 58) (.n 50) (.n 57)) (by decide +kernel)
  have a58 := a 47 (.add (.n 59) (.n 56) (.n 58)) (by decide +kernel)
  have m59 := a 48 (.mul (.n 60) (.n 50) (.n 59)) (by decide +kernel)
  have a60 := a 49 (.add (.n 61) (.n 55) (.n 60)) (by decide +kernel)
  have l60 := a 50 (.load (.n 61) (.n 53) 5172) (by decide +kernel)
  simp only [Atom.Holds] at l53 l53' l54 l55 l56 m57 a58 m59 a60 l60
  have e53 := tb_loadHolds_unique ((ld _ _).mp l53) hcur
  have e54 := tb_loadHolds_unique ((ld _ _).mp l54) (hval 0 (by omega))
  have e55 := tb_loadHolds_unique ((ld _ _).mp l55) (hval 1 (by omega))
  have e56 := tb_loadHolds_unique ((ld _ _).mp l56) (hval 2 (by omega))
  refine ⟨e6, e9, e15, e49, e50, e51, m52, e61, e62, ⟨by simp [Fs.squeeze, capOf], ?_⟩,
    tb_capOf_canonical _, by rw [← e53]; exact l53', ?_⟩
  · intro k hk
    have hk5 : k < 5 := by simpa [Fs.squeeze, capOf] using hk
    have := hst k hk5
    rw [show 0 + k * gkCap = 862 * k by unfold gkCap; ring]
    interval_cases k
    · rw [hP 8 (by omega)] at this; exact this
    · rw [hP 9 (by omega)] at this; exact this
    · rw [hP 10 (by omega)] at this; exact this
    · rw [hP 11 (by omega)] at this; exact this
    · rw [hP 12 (by omega)] at this; exact this
  · obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
      match st.values, hvl with
      | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
    have hv : polyEval st.values s.squeeze.1 = σ (.n 61) := by
      rw [a60, m59, a58, m57, e54, e55, e56, e49, hv3]
      simp only [polyEval, List.foldr, List.getD_cons_zero, List.getD_cons_succ, Fs.squeeze]
      ring
    rw [hv]; exact l60

end Sem

end
end LeanVM.Guest.B1.Tables
