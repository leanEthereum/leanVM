/-
  LeanVM.Guest.B1.Digest.MonoAt0

  `child_claim_list_mono`'s path and honest valuation, and its chain buffer's honest words.
-/

module

public import LeanVM.Guest.B1.Digest.MonoCLasts

/-!
# The gap walk, the parts

* The path: `child_claim_list_mono`'s body is flat (G:4440-4472): a straight run `monoP1` (the
  chain buffer's `HeapBuf`, the zero state, the region and the table at `chain · g^13`,
  `chain · g^14`, `child_claim_list_mono_loop0` over the big frames, `child_claim_list_mono_loop1`
  over the groups), the dispatch on the rest, two copies, the `ret` (`monoFlat_split`).
* `monoCOk`: the body evaluated in order (`Fwd.ev`), its stores the first record's fifteen words,
  no other side condition. `monoBody_core`: on a memory holding the first record at the chain
  buffer, the evaluated valuation holds every atom (`MonoVals`).
* `monoCells`: the chain buffer's honest words, each record the state after its frames and the
  walk's pointers there; `monoRec_of_reads` reads a record back.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The path -/

/-- The dispatch on the rest. -/
def monoDispS : Stmt := .dispatch (.n 6) mlNames [.n 49, .n 1, .n 2, .n 3] [.n 50, .n 51]

/-- `child_claim_list_mono_loop0`'s call: the big frames. -/
def mono31S : Stmt := .callIf (.n 31) name% «child_claim_list_mono_loop0» [.n 32, .n 4, .n 16, .n 2]

/-- `child_claim_list_mono_loop1`'s call: the groups. -/
def mono41S : Stmt := .callIf (.n 41) name% «child_claim_list_mono_loop1» [.n 42, .n 5, .n 39, .n 2]

/-- The body before its dispatch. -/
noncomputable def monoP1 : List Stmt := monoFlat.take 60

/-- The body after its dispatch. -/
noncomputable def monoPost : List Stmt := monoFlat.drop 61

set_option maxRecDepth 100000 in
theorem monoFlat_split : monoFlat = monoP1 ++ monoDispS :: monoPost :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem monoPost_eq : monoPost = [.atom (.copy (.n 52) (.n 50)), .atom (.copy (.n 53) (.n 51))] :=
  stmtsEqb_sound (by decide +kernel)

theorem monoPost_straight : monoPost.all Main.Stmt.straight = true := by rw [monoPost_eq]; rfl

set_option maxRecDepth 100000 in
theorem monoP1_straight : monoP1.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoP1_allocs : monoP1.filterMap Main.Stmt.allocSz = [(.n 16, .inr (.n 15))] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem monoP1_addrs : monoP1.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem monoP1_calls : monoP1.filterMap Main.Stmt.callS =
    [(some (.n 31), name% «child_claim_list_mono_loop0», [.n 32, .n 4, .n 16, .n 2], []),
      (some (.n 41), name% «child_claim_list_mono_loop1», [.n 42, .n 5, .n 39, .n 2], [])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem monoP1_loads : monoP1.filterMap B1.Stmt.loadS =
    (List.range 15).map fun c => (.n 16, c) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem monoP1_kinds : monoP1.all (fun s => isAtomS s || stmtEqb s mono31S || stmtEqb s mono41S) =
    true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mono_loop : coreProgram.loop "child_claim_list_mono" = false := by
  rw [Program.loop_of_find? find_child_claim_list_mono]; decide +kernel

theorem mono_param (σ : Val) : (Fn.params fn% «child_claim_list_mono»).map σ =
    [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] := rfl

theorem mono_body : Fn.body fn% «child_claim_list_mono» =
    monoP1 ++ monoDispS :: (monoPost ++ [.ret [.n 52, .n 53]]) := by
  rw [child_claim_list_mono_shape, monoFlat_split]; simp

theorem mlNames_get {r : ℕ} (hr : r < 17) : mlNames[r]! = mlNames.getD r "" := by
  have h : r < mlNames.length := by simp [mlNames]; omega
  rw [getElem!_pos mlNames r h, List.getD_eq_getElem _ _ h]

/-! ## The evaluated body -/

/-- **`child_claim_list_mono`'s body, evaluated**: in order, its stores the first record's words
at the chain buffer `.n 16` (the zero state, the region, the table), no other side condition;
the buffer's size `(g^a g^b g)^15`. -/
noncomputable def monoCOk : Bool :=
  let SE := storesOf 7 monoFlat
  (chk 7 monoFlat).isSome &&
  SE.all (fun a => (List.range 13).any (fun c => atomEqb a (.load (.n (17 + c)) (.n 16) c)) ||
    atomEqb a (.load (.n 1) (.n 16) 13) || atomEqb a (.load (.n 0) (.n 16) 14)) &&
  (atomsIn monoFlat).all (fun a => !needsSide a || decide (a ∈ SE)) &&
  (atomsIn monoFlat).any (isConstAt (.n 8) 2 0) &&
  (monoOf (atomsIn monoFlat) 40 (.n 15)).isPerm
    (List.replicate 15 (.n 4) ++ List.replicate 15 (.n 5) ++ List.replicate 15 (.n 8)) &&
  (atomsIn monoFlat).any (fun a => atomEqb a (.hint (.allocDyn (.n 16) (.n 15))))

set_option maxRecDepth 100000 in
theorem monoc_ok : monoCOk = true := by decide +kernel

/-- The oracle of `child_claim_list_mono`'s valuation: the chain buffer, the digest. -/
noncomputable def monow (chain : E) (D : Digest) (i : ℕ) : E :=
  if i = 16 then chain else if i = 50 then (digestHalves D).1 else if i = 51 then (digestHalves D).2
  else 0

/-- `child_claim_list_mono`'s valuation. -/
noncomputable def monoσ (rd : Reader) (args : List E) (chain : E) (D : Digest) : Val :=
  B1.Val.ofArgs (ev rd (monow chain D) args monoFlat)

/-- **What `child_claim_list_mono`'s valuation is** (`n = 136a + 17b + c`). -/
structure MonoVals (rd : Reader) (σ : Val) (args : List E) (a b : ℕ) (chain : E) (D : Digest) :
    Prop where
  atoms : ∀ x ∈ atomsIn monoFlat, x.Holds rd σ
  par : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] = args
  v15 : σ (.n 15) = gen ^ (15 * (a + b + 1))
  v16 : σ (.n 16) = chain
  v31 : σ (.n 31) = 1 + gen ^ a
  v32 : σ (.n 32) = 1
  v39 : σ (.n 39) = chain * gen ^ (15 * a)
  v41 : σ (.n 41) = 1 + gen ^ b
  v42 : σ (.n 42) = 1
  v49 : σ (.n 49) = chain * gen ^ (15 * (a + b))
  v50 : σ (.n 50) = (digestHalves D).1
  v51 : σ (.n 51) = (digestHalves D).2
  v52 : σ (.n 52) = (digestHalves D).1
  v53 : σ (.n 53) = (digestHalves D).2

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **`child_claim_list_mono`'s valuation**: on a memory holding the first record at the chain
buffer. -/
theorem monoBody_core {entries region base limit chain : E} {a b c : ℕ} (D : Digest)
    (hR : MonoRecAt rd chain 0 [] region entries 0) :
    MonoVals rd (monoσ rd [entries, region, base, limit, gen ^ a, gen ^ b, gen ^ c] chain D)
      [entries, region, base, limit, gen ^ a, gen ^ b, gen ^ c] a b chain D := by
  obtain ⟨hz0, h13, h14⟩ := hR
  have hk := monoc_ok
  simp only [monoCOk, Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨hchk1, hst⟩, hside⟩, hc8⟩, hm15⟩, hal16⟩ := hk
  have hb := monoBody_ok
  simp only [monoBodyOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hdis⟩, h32⟩, h31⟩, h30⟩, h42⟩, h41⟩, h40⟩, -⟩,
    -⟩, -⟩, hm39⟩, hm49⟩, hc52⟩, hc53⟩ := hb
  set w := monow chain D with hw
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp hchk1
  let args : List E := [entries, region, base, limit, gen ^ a, gen ^ b, gen ^ c]
  set σ := monoσ rd args chain D with hσ
  obtain ⟨-, -, hgs⟩ := ev_spec rd w monoFlat args hchk
  rw [show args.length = 7 from rfl] at hgs
  set SE := storesOf 7 monoFlat with hSE
  have hg : ∀ x ∈ atomsIn monoFlat, Good rd SE w σ x := fun x hx => hgs _ (cl_atom_mem hx)
  have par : ∀ i (hi : i < 7), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = entries := par 0 (by omega)
  have e1 : σ (.n 1) = region := par 1 (by omega)
  have e4 : σ (.n 4) = gen ^ a := par 4 (by omega)
  have e5 : σ (.n 5) = gen ^ b := par 5 (by omega)
  have v16 : σ (.n 16) = chain := by
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hal16
    rw [atomEqb_sound he] at hx
    have : σ (.n 16) = w 16 := hg _ hx
    rw [this, hw]; simp [monow]
  have hF := pure_holds hg
  have v17 : ∀ c < 13, σ (.n (17 + c)) = 0 := by
    intro c hc'
    have := (monoBody_ok)
    simp only [monoBodyOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at this
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp (this.1.1.1.1.1.1.2 c hc').2
    have hgx := hg x hx
    cases x <;> simp only [isConstAt, Bool.false_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hp
    obtain ⟨rfl, he⟩ := hp
    have hgx' : σ (.n (17 + c)) = _ := hgx
    rw [hgx', eEqb_sound he, word_zero]
  have hat : ∀ x ∈ atomsIn monoFlat, x.Holds rd σ := by
    refine atoms_holds_stores hg (fun x hx hnS hns => ?_) (fun _ x hx hxS => ?_)
    · have := List.all_eq_true.mp hside x hx
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
      rcases this with h | h
      · rw [hns] at h; exact absurd h (by simp)
      · exact absurd h hnS
    · have := List.all_eq_true.mp hst x hxS
      simp only [Bool.or_eq_true] at this
      rcases this with (h | h) | h
      · obtain ⟨c, hc', he⟩ := List.any_eq_true.mp h
        rw [atomEqb_sound he]
        have hc13 := List.mem_range.mp hc'
        show LoadHolds rd (σ (.n 16)) c (σ (.n (17 + c)))
        rw [v16, v17 c hc13]
        have := hz0 ⟨c, hc13⟩
        rwa [Nat.zero_add, absorbChunks, cellsOfState_zero] at this
      · rw [atomEqb_sound h]
        show LoadHolds rd (σ (.n 16)) 13 (σ (.n 1))
        rw [v16, e1]
        simpa using h13
      · rw [atomEqb_sound h]
        show LoadHolds rd (σ (.n 16)) 14 (σ (.n 0))
        rw [v16, e0]
        simpa using h14
  have gd : ∀ v ∈ [V.n 50, V.n 51], σ v = w v.idx := by
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp hdis
    rw [stmtEqb_sound he] at hs
    exact hgs _ hs
  have v50 : σ (.n 50) = (digestHalves D).1 := by
    rw [gd _ (by simp), hw]; simp [monow]
  have v51 : σ (.n 51) = (digestHalves D).2 := by
    rw [gd _ (by simp), hw]; simp [monow]
  have v8 : σ (.n 8) = gen := by rw [const_sound hc8 hat, word_gen]
  have v15 : σ (.n 15) = gen ^ (15 * (a + b + 1)) := by
    rw [mono_sound hat 40, (List.isPerm_iff.mp hm15).map σ |>.prod_eq]
    simp only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate, e4, e5,
      v8]
    ring
  refine ⟨hat, ?_, v15, v16, ?_, ?_, ?_, ?_, ?_, ?_, v50, v51, ?_, ?_⟩
  · rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega),
      par 5 (by omega), par 6 (by omega)]
    rfl
  · rw [add_sound h31 hat, const_sound h30 hat, word_one, e4]
  · rw [const_sound h32 hat, word_one]
  · rw [monoIs_sound hm39 hat, v16, e4, gen_pow_pow]
  · rw [add_sound h41 hat, const_sound h40 hat, word_one, e5]
  · rw [const_sound h42 hat, word_one]
  · rw [mono2Is_sound hm49 hat, v16, e4, e5, gen_pow_pow, gen_pow_pow, mul_assoc, ← pow_add,
      Nat.mul_add]
  · rw [copy_sound hc52 hat, v50]
  · rw [copy_sound hc53 hat, v51]

/-! ## The chain buffer -/

/-- A record's fifteen words: the state, the coverage pointer `region · g^O`, the table pointer
`entries · g^(4O)`. -/
def recCells (S : KeccakState) (region entries : E) (O : ℕ) : List E :=
  stCells S ++ [region * gen ^ O, entries * gen ^ (4 * O)]

theorem length_recCells (S : KeccakState) (region entries : E) (O : ℕ) :
    (recCells S region entries O).length = 15 := by simp [recCells, stCells]

/-- **The chain buffer's honest words**: after each of the first `a + b + 1` frames (`a` big
frames, then `b` groups), the state after their claims' cells and the walk's pointers past them. -/
def monoCells (region entries : E) (o : ℕ → ℕ) (cells : List E) (a b : ℕ) : List E :=
  (List.range (a + b + 1)).flatMap fun t =>
    recCells (absorbChunks (8 * clU a t) zeroState (cellsBytes (cells.take (68 * clU a t))))
      region entries (mStart o (17 * clU a t))

theorem length_monoCells (region entries : E) (o : ℕ → ℕ) (cells : List E) (a b : ℕ) :
    (monoCells region entries o cells a b).length = 15 * (a + b + 1) := by
  simp only [monoCells, List.length_flatMap, length_recCells, List.map_const', List.length_range,
    List.sum_replicate, smul_eq_mul]
  ring

theorem recCells_st (S : KeccakState) (region entries : E) (O : ℕ) (c : Fin 13) :
    (recCells S region entries O).getD c 0 = cellsOfState S false c := by
  have hc := c.isLt
  rw [recCells, List.getD_eq_getElem _ _ (by simp [stCells]; omega),
    List.getElem_append_left (by simp [stCells])]
  simp only [stCells, List.getElem_ofFn]

theorem recCells_13 (S : KeccakState) (region entries : E) (O : ℕ) :
    (recCells S region entries O).getD 13 0 = region * gen ^ O := by
  simp [recCells, stCells, List.getD_eq_getElem?_getD]

theorem recCells_14 (S : KeccakState) (region entries : E) (O : ℕ) :
    (recCells S region entries O).getD 14 0 = entries * gen ^ (4 * O) := by
  simp [recCells, stCells, List.getD_eq_getElem?_getD]

/-- **A record of the chain buffer, read back.** -/
theorem monoRec_of_reads {chain region entries : E} {o : ℕ → ℕ} {cells : List E} {a b : ℕ}
    (h : ReadsAt rd chain (monoCells region entries o cells a b)) {t : ℕ} (ht : t ≤ a + b) :
    MonoRecAt rd (chain * gen ^ (15 * t)) (8 * clU a t)
      (cellsBytes (cells.take (68 * clU a t))) region entries (mStart o (17 * clU a t)) := by
  have hr := fun c (hc : c < 15) => Main.readsAt_range_flatMap (w := 15)
    (fun q _ => length_recCells _ _ _ _) h t (by omega) c hc
  refine ⟨fun c => ?_, ?_, ?_⟩
  · have := hr c (by omega)
    rw [recCells_st] at this
    rw [loadHolds_mul_gen_pow, Nat.zero_add]
    exact this
  · have := hr 13 (by omega)
    rw [recCells_13] at this
    rw [loadHolds_mul_gen_pow]
    exact this
  · have := hr 14 (by omega)
    rw [recCells_14] at this
    rw [loadHolds_mul_gen_pow]
    exact this

end
end LeanVM.Guest.B1.Digest
