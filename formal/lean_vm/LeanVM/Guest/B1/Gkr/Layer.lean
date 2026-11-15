/-
  LeanVM.Guest.B1.Gkr.Layer

  A layer of `verify_bus_gkr`'s walk past the root-most, its loop `verify_bus_gkr_loop0`: one step
  of two levels of the specification's GKR walk, between two layer slots.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop29
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData

/-!
# A layer of two levels (`verify_bus_gkr_loop0`)

`verify_bus_gkr_loop0`'s body is the core IR's (`(fn% «verify_bus_gkr_loop0»).body`); its arguments
are `[x, bound, start_g, layers, tabs, rounds, claim, odd_g, g_bus_mu, k_mod_next]`. From the layer
slot at `layers·x_layer^13`, `x_layer = x²·start_g`: the combiner's permutation over the slot's
capacity, nothing waiting (a grind of `0` bits), the first round record, the rounds
(`verify_bus_gkr_loop0_loop0`, then `gkr_rounds__L{2r}` at `r = k % 4`, then `gkr_rounds__L1` at an
odd depth), the twelve children read, their check, the two new coordinates squeezed, and the next
slot `26` words on.

At `x = g^j` and `start_g = g^(2 - sh)`, `sh` the depth's parity, the slot is that of point length
`L = 2j + 2 - sh = 2k + sh`, `k = j + 1 - sh` its radix-four index, whose `half = g^(k / 4)` and
`parity = g^(k % 4)` count its `L` rounds: eight per `verify_bus_gkr_loop0_loop0` iteration, two per
`parity` step, and one at an odd depth.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_bus_gkr_loop0`'s parameters. -/
def lyParams : List V := (List.range 10).map V.n

/-- `verify_bus_gkr_loop0`'s body, the core IR's. -/
noncomputable def lyBody : List Stmt := (fn% «verify_bus_gkr_loop0»).body

noncomputable def lyCheck : Bool :=
  match coreProgram.find? name% «verify_bus_gkr_loop0» with
  | some fn => decide (fn.params = lyParams) && tbStmtsEqb fn.body lyBody
  | none => false

theorem lyCheck_eq : lyCheck = true := by decide +kernel

theorem lyFound : ∃ fn : Fn, coreProgram.find? name% «verify_bus_gkr_loop0» = some fn ∧
    fn.params = lyParams ∧ fn.body = lyBody := by
  have h := lyCheck_eq
  unfold lyCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- `verify_bus_gkr_loop0`'s statements before its `ret`. -/
noncomputable def lyPre : List Stmt := lyBody.take 192

theorem lyBody_eq : lyBody = lyPre ++ [.ret []] := tbStmtsEqb_sound (by decide +kernel)

theorem lyPre_noRet : Stmt.noRetList lyPre = true := by decide +kernel

/-! ## The layer slot -/

/-- **The slot of point length `L`** in `layers` (`LAYER_SLOTS = 13`): the carried capacity of the
sponge `s`, nothing waiting, the cursor, the three trees' values, a row holding the point (of
length `L`), the round position, `half` and `parity`. -/
def GkSlot (rd : Reader) (layers : E) (L : ℕ) (s : Fs) (cur : E) (st : GkrState)
    (row pos half parity : E) : Prop :=
  s.cap.length = 5 ∧ (∀ j < 5, LoadHolds rd layers (13 * L + j) (s.cap.getD j 0)) ∧ s.pend = [] ∧
    LoadHolds rd layers (13 * L + 5) cur ∧ st.values.length = 3 ∧
    (∀ t < 3, LoadHolds rd layers (13 * L + 6 + t) (st.values.getD t 0)) ∧
    LoadHolds rd layers (13 * L + 9) row ∧ st.point.length = L ∧ TbReadsAt rd row st.point ∧
    LoadHolds rd layers (13 * L + 10) pos ∧ LoadHolds rd layers (13 * L + 11) half ∧
    LoadHolds rd layers (13 * L + 12) parity

/-- The table `k_mod_next`: at `g^r`, `r < 4`, the next layer index's
`g^((r + 1) % 4)`, and at `g^(4 + r)` its carry into `half`, `g^((r + 1) / 4)`. -/
def KModNext (rd : Reader) (kmn : E) : Prop :=
  ∀ r < 4, LoadHolds rd kmn (4 + r) (gen ^ ((r + 1) / 4)) ∧ LoadHolds rd kmn r (gen ^ ((r + 1) % 4))

/-- **A layer of two levels** at `x = g^j`, the depth's parity `sh` (`start_g = g^(2 - sh)`,
`odd_g = g^sh`): from the slot of `L = 2j + 2 - sh`, its `half` and `parity` those of
`k = j + 1 - sh`, the stream runs `gkrStep 2` to the slot of `L + 2`, the row `40` words on,
given the table `k_mod_next`. -/
def LyB (rd : Reader) (sg og layers kmn x : E) : Prop :=
  KModNext rd kmn →
  ∀ j sh : ℕ, x = gen ^ j → sg = gen ^ (2 - sh) → og = gen ^ sh → j < 2 ^ 30 → sh < 2 →
    ∀ (s : Fs) (cur : E) (st : GkrState) (row pos : E),
      GkSlot rd layers (2 * j + 2 - sh) s cur st row pos (gen ^ ((j + 1 - sh) / 4))
        (gen ^ ((j + 1 - sh) % 4)) →
      ∃ (xs : List E) (st' : GkrState) (s' : Fs) (pos' : E),
        RunsTo (gkrStep 2 false st) s xs st' s' ∧ TbReadsAt rd cur xs ∧
        GkSlot rd layers (2 * j + 2 - sh + 2) s' (cur * gen ^ xs.length) st' (row * gen ^ 40) pos'
          (gen ^ ((j + 2 - sh) / 4)) (gen ^ ((j + 2 - sh) % 4))

/-! ## The layer's head -/

/-- A list of length `n` is its `n` entries. -/
theorem tb_eq_map_getD {l : List E} {n : ℕ} (h : l.length = n) :
    l = (List.range n).map (l.getD · 0) := by
  subst h
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- The rate cells of nothing waiting are zeros. -/
theorem tb_rateOf_nil_getD (k : ℕ) : (rateOf []).getD k 0 = 0 := by
  rw [rateOf_eq_cells [] (by simp)]
  simp only [pendCells, List.flatMap_nil, List.nil_append, List.length_nil,
    List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- A run of `13` values from `b`. -/
def lyOuts (b : ℕ) : List V := (List.range 13).map fun k ↦ .n (b + k)

/-- The capacity cells among a permutation's outputs from `b`. -/
def lyCap (b : ℕ) : List V := (List.range 5).map fun k ↦ .n (b + 8 + k)

/-- A permutation's thirteen outputs from `b`, and its capacity cells. -/
theorem ly_keccak {rd : Reader} {σ : Val} {ins : List V} {b : ℕ}
    (hk : (Atom.keccak ins (lyOuts b) false false).Holds rd σ) :
    (∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = capOf (permOf (ins.map σ)) := by
  obtain ⟨-, -, hout⟩ := keccakA_perm hk
  have hP : ∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩ := by
    intro k hk
    have := outs_eq hout ⟨k, hk⟩ (by simpa [lyOuts] using hk)
    simpa [lyOuts] using this
  refine ⟨hP, ?_⟩
  simp only [lyCap, capOf, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rw [hP (8 + 0) (by omega), hP (8 + 1) (by omega), hP (8 + 2) (by omega), hP (8 + 3) (by omega),
    hP (8 + 4) (by omega)]
  rfl

/-- The empty rate and a capacity as a permutation's inputs. -/
theorem ly_zero_rate {σ : Val} {z1 z2 z3 z4 : ℕ} (h1 : σ (.n z1) = 0) (h2 : σ (.n z2) = 0)
    (h3 : σ (.n z3) = 0) (h4 : σ (.n z4) = 0) (cap : List V) :
    (([.n z1, .n z1, .n z1, .n z1, .n z1, .n z2, .n z3, .n z4] ++ cap : List V).map σ) =
      rateOf [] ++ cap.map σ := by
  rw [List.map_append, tb_eq_map_getD (show (rateOf []).length = 8 by simp [rateOf])]
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, tb_rateOf_nil_getD, h1, h2, h3, h4]

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **The layer's head**: at `x = g^j` with `start_g = g^(2 - sh)`, the slot is at
`layers·g^(13 L)`, `L = 2j + 2 - sh`; the combiner is the slot's sponge's challenge, and the first
round record carries the sponge after it, the cursor and the combined claim. -/
theorem ly_head (h : Stmt.HoldsList C rd σ lyPre True kret) {j sh : ℕ} (hx : σ (.n 0) = gen ^ j)
    (hsg : σ (.n 2) = gen ^ (2 - sh)) (hsh : sh < 2) {s : Fs} {cur : E} {st : GkrState}
    {row pos half parity : E}
    (hslot : GkSlot rd (σ (.n 3)) (2 * j + 2 - sh) s cur st row pos half parity) :
    σ (.n 10) = gen ^ (2 * j) ∧ σ (.n 11) = gen ^ (2 * j + 2 - sh) ∧
      σ (.n 17) = σ (.n 3) * gen ^ (13 * (2 * j + 2 - sh)) ∧
      σ (.n 42) = s.squeeze.1 ∧ σ (.n 46) = row ∧ σ (.n 47) = pos ∧
      σ (.n 48) = σ (.n 5) * pos ∧ σ (.n 53) = half ∧ σ (.n 54) = parity ∧
      TbCapAt rd (σ (.n 48)) 0 gkCap s.squeeze.2.cap ∧
      LoadHolds rd (σ (.n 48)) (5 * gkCap) cur ∧
      LoadHolds rd (σ (.n 48)) (6 * gkCap) (polyEval st.values s.squeeze.1) := by
  have hnr := lyPre_noRet
  obtain ⟨hcl, hcap, hpe, hcur, hvl, hval, hrow, -, -, hpos, hhalf, hpar⟩ := hslot
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have m10 := a 0 (.mul (.n 10) (.n 0) (.n 0)) (by decide +kernel)
  have m11 := a 1 (.mul (.n 11) (.n 10) (.n 2)) (by decide +kernel)
  have m12 := a 2 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel)
  have m13 := a 3 (.mul (.n 13) (.n 12) (.n 11)) (by decide +kernel)
  have m14 := a 4 (.mul (.n 14) (.n 13) (.n 13)) (by decide +kernel)
  have m15 := a 5 (.mul (.n 15) (.n 14) (.n 14)) (by decide +kernel)
  have m16 := a 6 (.mul (.n 16) (.n 15) (.n 11)) (by decide +kernel)
  have m17 := a 7 (.mul (.n 17) (.n 3) (.n 16)) (by decide +kernel)
  simp only [Atom.Holds] at m10 m11 m12 m13 m14 m15 m16 m17
  set L := 2 * j + 2 - sh with hL
  have e10 : σ (.n 10) = gen ^ (2 * j) := by rw [m10, hx, ← pow_add]; ring_nf
  have e11 : σ (.n 11) = gen ^ L := by
    rw [m11, e10, hsg, ← pow_add, show 2 * j + (2 - sh) = L by omega]
  have e17 : σ (.n 17) = σ (.n 3) * gen ^ (13 * L) := by
    rw [m17, m16, m15, m14, m13, m12, e11, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    ring_nf
  have ld : ∀ k w, LoadHolds rd (σ (.n 17)) k w ↔ LoadHolds rd (σ (.n 3)) (13 * L + k) w := by
    intro k w; rw [e17, tb_loadHolds_mul_gen_pow]
  -- the slot's capacity, the combiner's permutation
  have hcapL := tb_holds_slice hnr h 8 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (18 + k)) (.n 17) k)) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcapL
  simp only [Atom.Holds] at hcapL
  have ecap : ∀ k < 5, σ (.n (18 + k)) = s.cap.getD k 0 := fun k hk =>
    tb_loadHolds_unique ((ld k _).mp (hcapL k hk)) (hcap k hk)
  have c25 := a 15 (.const (.n 25) (word 0 0)) (by decide +kernel)
  have c26 := a 16 (.const (.n 26) (word 0 0)) (by decide +kernel)
  have c27 := a 17 (.const (.n 27) (word 0 0)) (by decide +kernel)
  have c28 := a 18 (.const (.n 28) (word 0 0)) (by decide +kernel)
  have k1 := a 19 (.keccak ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++
      (List.range 5).map fun k ↦ .n (18 + k)) (lyOuts 29) false false) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at c25 c26 c27 c28
  obtain ⟨hP, -⟩ := ly_keccak k1
  have hcapE : ((List.range 5).map fun k ↦ V.n (18 + k)).map σ = s.cap := by
    rw [tb_eq_map_getD hcl, List.map_map]
    exact List.map_congr_left fun k hk => ecap k (List.mem_range.mp hk)
  have hins : (([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++
      (List.range 5).map fun k ↦ V.n (18 + k)) : List V).map σ = rateOf s.pend ++ s.cap := by
    rw [ly_zero_rate c25 c26 c27 c28, hpe, hcapE]
  rw [hins] at hP
  have c42 := a 20 (.copy (.n 42) (.n 29)) (by decide +kernel)
  simp only [Atom.Holds] at c42
  have e42 : σ (.n 42) = s.squeeze.1 := by
    rw [c42, hP 0 (by omega)]
    exact (Keccak.challengeOf_cells _).symm
  -- the slot's values, row, position, half and parity
  have l43 := a 21 (.load (.n 43) (.n 17) 6) (by decide +kernel)
  have l44 := a 22 (.load (.n 44) (.n 17) 7) (by decide +kernel)
  have l45 := a 23 (.load (.n 45) (.n 17) 8) (by decide +kernel)
  have l46 := a 24 (.load (.n 46) (.n 17) 9) (by decide +kernel)
  have l47 := a 25 (.load (.n 47) (.n 17) 10) (by decide +kernel)
  have m48 := a 26 (.mul (.n 48) (.n 5) (.n 47)) (by decide +kernel)
  have l23 := a 13 (.load (.n 23) (.n 17) 5) (by decide +kernel)
  have l23' := a 32 (.load (.n 23) (.n 48) 4310) (by decide +kernel)
  have m49 := a 33 (.mul (.n 49) (.n 42) (.n 45)) (by decide +kernel)
  have a50 := a 34 (.add (.n 50) (.n 44) (.n 49)) (by decide +kernel)
  have m51 := a 35 (.mul (.n 51) (.n 42) (.n 50)) (by decide +kernel)
  have a52 := a 36 (.add (.n 52) (.n 43) (.n 51)) (by decide +kernel)
  have l52 := a 37 (.load (.n 52) (.n 48) 5172) (by decide +kernel)
  have l53 := a 38 (.load (.n 53) (.n 17) 11) (by decide +kernel)
  have l54 := a 39 (.load (.n 54) (.n 17) 12) (by decide +kernel)
  simp only [Atom.Holds] at l43 l44 l45 l46 l47 m48 l23 l23' m49 a50 m51 a52 l52 l53 l54
  have e43 := tb_loadHolds_unique ((ld _ _).mp l43) (hval 0 (by omega))
  have e44 := tb_loadHolds_unique ((ld _ _).mp l44) (hval 1 (by omega))
  have e45 := tb_loadHolds_unique ((ld _ _).mp l45) (hval 2 (by omega))
  have e46 := tb_loadHolds_unique ((ld _ _).mp l46) hrow
  have e47 := tb_loadHolds_unique ((ld _ _).mp l47) hpos
  have e53 := tb_loadHolds_unique ((ld _ _).mp l53) hhalf
  have e54 := tb_loadHolds_unique ((ld _ _).mp l54) hpar
  have e23 := tb_loadHolds_unique ((ld _ _).mp l23) hcur
  rw [e47] at m48
  -- the first record
  have hst := tb_holds_slice hnr h 27 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (37 + k)) (.n 48) (862 * k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hst
  simp only [Atom.Holds] at hst
  refine ⟨e10, e11, e17, e42, e46, e47, m48, e53, e54, ⟨by simp [Fs.squeeze, capOf], ?_⟩,
    by rw [← e23]; exact l23', ?_⟩
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
    have hv : polyEval st.values s.squeeze.1 = σ (.n 52) := by
      rw [a52, m51, a50, m49, e43, e44, e45, e42, hv3]
      simp only [polyEval, List.foldr, List.getD_cons_zero, List.getD_cons_succ]
      ring
    rw [hv]; exact l52

end Sem

end
end LeanVM.Guest.B1.Tables
