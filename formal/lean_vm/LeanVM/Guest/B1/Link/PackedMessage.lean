/-
  LeanVM.Guest.B1.Link.PackedMessage

  B1 for `packed_message__L144`: the link's packed message and the challenge after it.
-/

module

public import LeanVM.Guest.B1.Link.SqueezePacked
import LeanVM.Guest.CoreRef
import LeanVM.Guest.Value.KeccakEval

/-!
# `packed_message`

`packed_message(fs0..fs4, msg, n)` (G), at `n = 144`, absorbs the `n` words at `msg` eight a
permutation (`observePacked`), then permutes the capacity alone for the next challenge, returning
it and the capacity. `pkAbsorb b xs cap`: the capacity after `b` permutations of eight words of `xs`
each over `cap`. `runsTo_readPacked`: a packed read of `8 b` words from the carried capacity is
those permutations. `MeaningPM`: the words at `msg`, and the returns are `Fs.squeeze` after them.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The packed read on the carried sponge -/

/-- `b` permutations, eight words of `xs` each over the capacity: the capacity after them. -/
def pkAbsorb : ℕ → List E → List E → List E
  | 0, _, cap => cap
  | b + 1, xs, cap => pkAbsorb b (xs.drop 8) (capOf (permOf (xs.take 8 ++ cap)))

theorem pkAbsorb_succ' : ∀ (b : ℕ) (xs cap : List E), pkAbsorb (b + 1) xs cap =
    capOf (permOf ((xs.drop (8 * b)).take 8 ++ pkAbsorb b xs cap))
  | 0, xs, cap => by simp [pkAbsorb]
  | b + 1, xs, cap => by
    rw [pkAbsorb, pkAbsorb_succ' b, pkAbsorb, List.drop_drop, show 8 + 8 * b = 8 * (b + 1) by ring]

theorem getD_flatMap_pair (l : List E) (f g : E → UInt64) (i : ℕ) (hi : i < 2 * l.length) :
    (l.flatMap fun x ↦ [f x, g x]).getD i 0 =
      if i % 2 = 0 then f (l.getD (i / 2) 0) else g (l.getD (i / 2) 0) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    match i with
    | 0 => simp
    | 1 => simp
    | i + 2 =>
      simp only [List.flatMap_cons, List.cons_append, List.getD_cons_succ, List.nil_append]
      rw [ih i (by simp at hi; omega), show (i + 2) / 2 = i / 2 + 1 by omega, List.getD_cons_succ,
        show (i + 2) % 2 = i % 2 by omega]

open LeanVM.Guest.Value.Keccak (lane_stateOfCells laneCell laneLimb laneCellIdx laneLimbIdx
  limb_cellsOfState lane_ofLane) in
/-- **A packed permutation's input is the cells of eight words and the capacity.** -/
theorem packedInput_cells (S : KeccakState) {chunk : List E} (hc : chunk.length = 8) :
    stateOfCells (cells13 (chunk ++ capOf S)) false = packedInput S chunk := by
  apply Vector.ext
  intro i hi
  have e := KeccakEval.lane_fin (stateOfCells (cells13 (chunk ++ capOf S)) false) ⟨i, hi⟩
  simp only [Fin.getElem_fin] at e
  rw [← e, lane_stateOfCells _ false ⟨i, hi⟩, packedInput, Vector.getElem_ofFn]
  by_cases h : i < 16
  · simp only [h, ↓reduceIte, laneCell, laneLimb, laneCellIdx, laneLimbIdx,
      show ¬ (false = true ∨ 17 ≤ i) by simp; omega, cells13]
    rw [getD_flatMap_pair _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    rcases Nat.mod_two_eq_zero_or_one i with h2 | h2
    · simp [h2]
    · simp [h2]
  · have hc8 : 8 ≤ (laneCell false ⟨i, hi⟩).val := by
      simp only [laneCell, laneCellIdx, Bool.false_eq_true, false_or]; split <;> omega
    have hcell : cells13 (chunk ++ capOf S) (laneCell false ⟨i, hi⟩) =
        cellsOfState S false (laneCell false ⟨i, hi⟩) := by
      generalize hl : laneCell false ⟨i, hi⟩ = c at hc8 ⊢
      simp only [cells13]
      rw [List.getD_append_right _ _ _ _ (by omega), hc]
      fin_cases c <;> simp_all [capOf]
    rw [hcell, limb_cellsOfState, lane_ofLane]
    simp [h]

theorem apc_step (f : ℕ) (S : KeccakState) (x : E) (xs : List E) :
    absorbPackedChunks (m := Id) keccakF1600 (f + 1) S (x :: xs) =
      absorbPackedChunks (m := Id) keccakF1600 f (keccakF1600 (packedInput S ((x :: xs).take 8)))
        ((x :: xs).drop 8) := rfl

theorem apc_carried : ∀ (b : ℕ) (xs : List E) (S : KeccakState) (f : ℕ), xs.length = 8 * b → b ≤ f →
    capOf (absorbPackedChunks (m := Id) keccakF1600 f S xs) = pkAbsorb b xs (capOf S)
  | 0, xs, S, f, hl, _ => by
    obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    cases f <;> rfl
  | b + 1, x :: xs, S, f + 1, hl, hf => by
    rw [apc_step, apc_carried b _ _ f (by simp at hl ⊢; omega) (by omega), pkAbsorb, permOf,
      packedInput_cells S (by simp at hl ⊢; omega)]
  | b + 1, [], _, _, hl, _ => by simp at hl

/-- **A packed read of `8 b` words from the carried capacity.** -/
theorem runsTo_readPacked (cap xs : List E) {b : ℕ} (hl : xs.length = 8 * b) :
    RunsTo (VerifierProgram.readScalarsPacked (8 * b)) ⟨cap, []⟩ xs xs ⟨pkAbsorb b xs cap, []⟩ := by
  intro sp hs rest os roots
  obtain ⟨st, pd, gr⟩ := sp
  obtain ⟨h1, h2, h3⟩ := hs
  simp only at h1 h2 h3
  subst h2 h3
  refine ⟨⟨absorbPackedChunks (m := Id) keccakF1600 xs.length st xs, [], none⟩, ⟨?_, rfl, rfl⟩, ?_⟩
  · rw [apc_carried b xs st _ hl (by omega), h1]
  · simp only [runId, VerifierProgram.readScalarsPacked, Compile.runWithHash]
    simp only [Option.isNone_none, true_and, List.length_append, ← hl, Nat.le_add_right, ↓reduceIte,
      List.take_left', List.drop_left']
    rfl

/-! ## The template -/

/-- Permutation `j`: its eight words loaded, then the `KECCAK` over them and the capacity. -/
def pmBlk (j : ℕ) : List Stmt :=
  (List.range 8).map (fun i ↦ .atom (.load (.n (11 + 21 * j + i)) (.n 5) (8 * j + i))) ++
    [.atom (.keccak ((List.range 8).map (fun i ↦ V.n (11 + 21 * j + i)) ++
      (List.range 5).map fun i ↦ V.n (6 + 21 * j + i)) ((List.range 13).map fun i ↦ .n (19 + 21 * j + i))
      false false)]

/-- The first `b` permutations. -/
def pmBlocks (b : ℕ) : List Stmt := ((List.range b).map pmBlk).flatten

/-- `packed_message__L{8 b}`'s atoms. -/
def pmA (b : ℕ) : List Stmt :=
  (List.range 5).map (fun i ↦ .atom (.copy (.n (6 + i)) (.n i))) ++ pmBlocks b ++
    [.atom (.const (.n (11 + 21 * b)) (word 1 0)), .atom (.const (.n (12 + 21 * b)) (word 0 0)),
      .atom (.const (.n (13 + 21 * b)) (word 0 0)), .atom (.const (.n (14 + 21 * b)) (word 0 0)),
      .atom (.const (.n (15 + 21 * b)) (word 0 0)),
      .atom (.keccak ([.n (12 + 21 * b), .n (12 + 21 * b), .n (12 + 21 * b), .n (12 + 21 * b),
        .n (12 + 21 * b), .n (13 + 21 * b), .n (14 + 21 * b), .n (15 + 21 * b)] ++
        (List.range 5).map fun i ↦ V.n (6 + 21 * b + i)) ((List.range 13).map fun i ↦ .n (16 + 21 * b + i))
        false false),
      .atom (.copy (.n (29 + 21 * b)) (.n (16 + 21 * b)))] ++
    (List.range 5).map fun i ↦ .atom (.copy (.n (30 + 21 * b + i)) (.n (24 + 21 * b + i)))

/-- `packed_message__L{8 b}`'s body. -/
def pmBody (b : ℕ) : List Stmt := pmA b ++ [.ret ((List.range 6).map fun i ↦ .n (29 + 21 * b + i))]

theorem pmA_atoms (b : ℕ) : AllAtoms (pmA b) := by
  unfold pmA pmBlocks
  refine allAtoms_append (allAtoms_append (allAtoms_append ?_ (allAtoms_map_flatten fun j _ ↦
    allAtoms_append ?_ ?_)) ?_) ?_
  all_goals intro s hs
  all_goals simp only [List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hs
  all_goals first
    | (rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
    | (obtain ⟨_, _, rfl⟩ := hs; exact ⟨_, rfl⟩)

/-! ## The meaning -/

/-- The words `packed_message`'s loads read, from the values they load into. -/
def pmXs (σ : Val) (N : ℕ) : List E := (List.range (8 * N)).map fun i ↦ σ (.n (11 + 21 * (i / 8) + i % 8))

theorem pmXs_chunk (σ : Val) {j N : ℕ} (hj : j < N) :
    ((pmXs σ N).drop (8 * j)).take 8 = (List.range 8).map fun i ↦ σ (.n (11 + 21 * j + i)) := by
  apply List.ext_getElem
  · simp [pmXs]; omega
  · intro i h1 h2
    simp only [pmXs, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h2
    rw [show (8 * j + i) / 8 = j by omega, show (8 * j + i) % 8 = i by omega]

theorem pmBlocks_sound {rd : Reader} {σ : Val} {b N : ℕ} (hbN : b ≤ N)
    (hA : ∀ a, Stmt.atom a ∈ pmBlocks b → a.Holds rd σ) :
    (∀ j < b, ∀ i < 8, LoadHolds rd (σ (.n 5)) (8 * j + i) (σ (.n (11 + 21 * j + i)))) ∧
      (List.range 5).map (fun i ↦ σ (.n (6 + 21 * b + i))) =
        pkAbsorb b (pmXs σ N) ((List.range 5).map fun i ↦ σ (.n (6 + i))) := by
  induction b with
  | zero => exact ⟨fun j hj ↦ absurd hj (by omega), by simp [pkAbsorb]⟩
  | succ b ih =>
    have hsplit : pmBlocks (b + 1) = pmBlocks b ++ pmBlk b := by
      simp [pmBlocks, List.range_succ]
    rw [hsplit] at hA
    obtain ⟨ihl, ihc⟩ := ih (by omega) fun a ha ↦ hA a (List.mem_append_left _ ha)
    have hB : ∀ a, Stmt.atom a ∈ pmBlk b → a.Holds rd σ := fun a ha ↦ hA a (List.mem_append_right _ ha)
    have hk := hB _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hp := (keccakA_perm hk (by simp)).2.2
    have hins : ((List.range 8).map (fun i ↦ V.n (11 + 21 * b + i)) ++
        (List.range 5).map fun i ↦ V.n (6 + 21 * b + i)).map σ =
        ((pmXs σ N).drop (8 * b)).take 8 ++ pkAbsorb b (pmXs σ N) ((List.range 5).map fun i ↦ σ (.n (6 + i))) := by
      rw [pmXs_chunk σ (by omega), ← ihc]
      simp [List.map_map, Function.comp_def]
    rw [hins] at hp
    have ho := outs_cells_of (F := 19 + 21 * b) (by simpa using hp)
    refine ⟨fun j hj i hi ↦ ?_, ?_⟩
    · rcases Nat.lt_or_ge j b with h | h
      · exact ihl j h i hi
      · obtain rfl : j = b := by omega
        have := hB _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
        simpa [Atom.Holds] using this
    · rw [pkAbsorb_succ', capOf_outs ho]
      simp only [List.map_map]
      refine List.map_congr_left fun i _ ↦ ?_
      simp only [Function.comp]
      congr 2
      ring

/-- **`packed_message__L{8 b}(fs0..fs4, msg)`**: the `8 b` words at `msg`; it returns the challenge
and the capacity of `Fs.squeeze` after their packed permutations. -/
def MeaningPM (b : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, msg], rets => ∃ xs : List E, xs.length = 8 * b ∧ ReadsAt rd msg xs ∧
      rets = (Fs.squeeze ⟨pkAbsorb b xs [f0, f1, f2, f3, f4], []⟩).1 ::
        (Fs.squeeze ⟨pkAbsorb b xs [f0, f1, f2, f3, f4], []⟩).2.cap
  | _, _ => False

theorem pm_sound {b : ℕ} {rd : Reader} {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]) (hbody : f.body = pmBody b)
    (args rets : List E) : coreProgram.Rel rd name args rets → MeaningPM b rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams]
  rintro ⟨σ, rfl, h⟩
  rw [pmBody, holdsList_append] at h
  obtain ⟨hA, hret⟩ := (holdsList_atoms (pmA_atoms b) _ _).mp h
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_map] at hret
  have mem : ∀ a, Stmt.atom a ∈ pmA b → a.Holds rd σ := hA
  have hcp : ∀ i < 5, σ (.n (6 + i)) = σ (.n i) := fun i hi ↦ by
    have := mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))))
    simpa [Atom.Holds] using this
  have htail : ∀ a, Stmt.atom a ∈ [Stmt.atom (.const (.n (11 + 21 * b)) (word 1 0)),
      .atom (.const (.n (12 + 21 * b)) (word 0 0)),
      .atom (.const (.n (13 + 21 * b)) (word 0 0)), .atom (.const (.n (14 + 21 * b)) (word 0 0)),
      .atom (.const (.n (15 + 21 * b)) (word 0 0)),
      .atom (.keccak ([.n (12 + 21 * b), .n (12 + 21 * b), .n (12 + 21 * b), .n (12 + 21 * b),
        .n (12 + 21 * b), .n (13 + 21 * b), .n (14 + 21 * b), .n (15 + 21 * b)] ++
        (List.range 5).map fun i ↦ V.n (6 + 21 * b + i)) ((List.range 13).map fun i ↦ .n (16 + 21 * b + i))
        false false),
      .atom (.copy (.n (29 + 21 * b)) (.n (16 + 21 * b)))] → a.Holds rd σ := fun a ha ↦
    mem a (List.mem_append_left _ (List.mem_append_right _ ha))
  have z1 := htail (.const (.n (12 + 21 * b)) (word 0 0)) (by simp)
  have z2 := htail (.const (.n (13 + 21 * b)) (word 0 0)) (by simp)
  have z3 := htail (.const (.n (14 + 21 * b)) (word 0 0)) (by simp)
  have z4 := htail (.const (.n (15 + 21 * b)) (word 0 0)) (by simp)
  have hk := htail (.keccak ([.n (12 + 21 * b), .n (12 + 21 * b), .n (12 + 21 * b), .n (12 + 21 * b),
        .n (12 + 21 * b), .n (13 + 21 * b), .n (14 + 21 * b), .n (15 + 21 * b)] ++
        (List.range 5).map fun i ↦ V.n (6 + 21 * b + i)) ((List.range 13).map fun i ↦ .n (16 + 21 * b + i))
        false false) (by simp)
  have hc0 := htail (.copy (.n (29 + 21 * b)) (.n (16 + 21 * b))) (by simp)
  have hcs : ∀ i < 5, σ (.n (30 + 21 * b + i)) = σ (.n (24 + 21 * b + i)) := fun i hi ↦ by
    have := mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    simpa [Atom.Holds] using this
  simp only [Atom.Holds, word_zero] at z1 z2 z3 z4 hc0
  obtain ⟨hl, hc⟩ := pmBlocks_sound (N := b) le_rfl fun a ha ↦
    mem a (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha)))
  have hcap0 : (List.range 5).map (fun i ↦ σ (.n (6 + i))) = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] := by
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append]
    rw [hcp 0 (by norm_num), hcp 1 (by norm_num), hcp 2 (by norm_num), hcp 3 (by norm_num), hcp 4 (by norm_num)]
  rw [hcap0] at hc
  have hf := keccakA_fs (s := ⟨pkAbsorb b (pmXs σ b) [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩)
    hk (by simp) (by
      simp only [List.map_append, List.map_cons, List.map_nil, z1, z2, z3, z4]
      rw [List.map_map, show (List.range 5).map (σ ∘ fun i ↦ V.n (6 + 21 * b + i)) = _ from hc]
      rfl)
  have ho := outs_cells_of (F := 16 + 21 * b) (by simpa using hf)
  refine ⟨pmXs σ b, by simp [pmXs], fun k hk ↦ ?_, ?_⟩
  · simp only [pmXs, List.length_map, List.length_range] at hk
    have := hl (k / 8) (by omega) (k % 8) (by omega)
    rw [show 8 * (k / 8) + k % 8 = k by omega] at this
    simpa [pmXs] using this
  · rw [← hret]
    simp only [Fs.squeeze, Keccak.challengeOf_cells, capOf_outs ho]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    match i, h1 with
    | 0, _ => simpa [Function.comp] using hc0.trans (ho 0 (by norm_num))
    | k + 1, hk =>
      simp only [List.getElem_map, List.getElem_range, List.getElem_cons_succ, Function.comp]
      rw [show 29 + 21 * b + (k + 1) = 30 + 21 * b + k by ring, hcs k (by omega)]
      congr 2
      omega

set_option maxRecDepth 100000 in
theorem pm144_body : Fn.body (fn% «packed_message__L144») = pmBody 18 :=
  stmtsEqb_sound (by decide +kernel)

/-- **`packed_message__L144`'s core IR implies its meaning.** -/
theorem packed_message_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "packed_message__L144" args rets → MeaningPM 18 rd args rets :=
  pm_sound (coreProgram_find?_at (j := idx% «packed_message__L144») rfl) rfl pm144_body args rets

end
end LeanVM.Guest.B1.Link
