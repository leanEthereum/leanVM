/-
  LeanVM.Guest.Backend.Sound.Compiles

  A program compiled from its pieces: `lowerProgram` succeeds, and the assembled functions and
  size are the given ones, from one piece per function and checks on numbers.
-/

module

public import LeanVM.Guest.Backend.Sound.Piece

/-!
# A program compiled from its pieces

`compiles_of_pieces`: if the pieces of every function of `p` hold (`pieceAt`, function `j` placed
from the jump tables the functions before it leave, `tablesAt`, at the pc past them), the program's
checks hold (`progChecks`), the slots are written once each and inside the tables (`slotsOk`,
numbers only), `__jump_tables` is the given compiled function chunk by chunk (`jtChunkOk`) and the
padded size is `2 ^ k`, then `lowerProgram p` succeeds with the jump table slots `slotsOfOuts p os`,
and the assembled program's functions are `cfJt :: cfs`, of size `2 ^ k`. The loop and signature
tables and the layout are taken as equations (`hloops`, `hsigs`, `hl`), so that a check of the
pieces reads them as values computed once.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

@[expose] public section

/-! ## The pieces as a chain -/

theorem chain_of_forall {loops : Loops} {sigs : SMap (ℕ × ℕ)} {l : Layout} :
    ∀ (tfs : List TracedFn) (os : List FnOut) (frs : List ℕ) (cfs : List CompiledFunction)
      (t : Tables) (pc : ℕ), os.length = tfs.length → frs.length = tfs.length →
      cfs.length = tfs.length →
      (∀ j < tfs.length, pieceOk loops sigs l ((os.take j).foldl Tables.after t) (tfs.getD j default)
        (os.getD j default) (pc + ((os.take j).map (·.size)).sum) (frs.getD j 0)
        (cfs.getD j noFunction) = true) →
      Chain loops sigs l t pc tfs os frs cfs
  | [], [], [], [], _, _, _, _, _, _ => trivial
  | tf :: tfs, o :: os, fr :: frs, cf :: cfs, t, pc, hos, hfrs, hcfs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hos hfrs hcfs
      refine ⟨?_, chain_of_forall tfs os frs cfs _ _ hos hfrs hcfs fun j hj => ?_⟩
      · simpa using h 0 (by simp)
      · have := h (j + 1) (by simp; omega)
        simpa [List.take_succ_cons, List.foldl_cons, Nat.add_assoc] using this
  | [], _ :: _, _, _, _, _, h, _, _, _ => by simp at h
  | [], [], _ :: _, _, _, _, _, h, _, _ => by simp at h
  | [], [], [], _ :: _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, _, h, _, _ => by simp at h
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, h, _ => by simp at h

theorem chainOut_length {l : Layout} : ∀ (placed : List Placed) (tfs : List TracedFn)
    (os : List FnOut) (frs : List ℕ) (cfs : List CompiledFunction) (pc : ℕ),
    ChainOut l pc placed tfs os frs cfs → placed.length = tfs.length
  | [], [], [], [], [], _, _ => rfl
  | _ :: pfs, _ :: tfs, _ :: os, _ :: frs, _ :: cfs, _, ⟨_, hr⟩ => by
      simp [chainOut_length pfs tfs os frs cfs _ hr]
  | [], _ :: _, _, _, _, _, h => nomatch h
  | [], [], _ :: _, _, _, _, h => nomatch h
  | [], [], [], _ :: _, _, _, h => nomatch h
  | [], [], [], [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, _, _, _, h => nomatch h
  | _ :: _, _ :: _, [], _, _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, h => nomatch h

theorem chainOut_names {l : Layout} : ∀ (placed : List Placed) (tfs : List TracedFn)
    (os : List FnOut) (frs : List ℕ) (cfs : List CompiledFunction) (pc : ℕ),
    ChainOut l pc placed tfs os frs cfs →
      placed.map (fun pf => (emitFn pf.fn).1.name) = tfs.map (·.core.name)
  | [], [], [], [], [], _, _ => rfl
  | _ :: pfs, _ :: tfs, _ :: os, _ :: frs, _ :: cfs, _, ⟨⟨_, h2, _⟩, hr⟩ => by
      simp only [List.map_cons, h2, chainOut_names pfs tfs os frs cfs _ hr]
  | [], _ :: _, _, _, _, _, h => nomatch h
  | [], [], _ :: _, _, _, _, h => nomatch h
  | [], [], [], _ :: _, _, _, h => nomatch h
  | [], [], [], [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, _, _, _, h => nomatch h
  | _ :: _, _ :: _, [], _, _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, h => nomatch h

/-- What the layout reads of the functions resolved with the frame sizes `frs`. -/
theorem chainOut_infoAt {l : Layout} : ∀ (placed : List Placed) (tfs : List TracedFn)
    (os : List FnOut) (frs : List ℕ) (cfs : List CompiledFunction) (pc : ℕ),
    ChainOut l pc placed tfs os frs cfs →
      (List.zipWith (fun pf fr => { (emitFn pf.fn).1 with frameSize := fr }) placed frs).map infoOf =
        ((tfs.zip frs).zip os).map fun x => (x.1.1.core.name, x.2.size, x.1.2)
  | [], [], [], [], [], _, _ => rfl
  | _ :: pfs, _ :: tfs, _ :: os, _ :: frs, _ :: cfs, _, ⟨⟨_, h2, _, h4, _⟩, hr⟩ => by
      simp only [List.zipWith_cons_cons, List.map_cons, List.zip_cons_cons, infoOf] at *
      rw [chainOut_infoAt pfs tfs os frs cfs _ hr, h2, h4]
  | [], _ :: _, _, _, _, _, h => nomatch h
  | [], [], _ :: _, _, _, _, h => nomatch h
  | [], [], [], _ :: _, _, _, h => nomatch h
  | [], [], [], [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, _, _, _, h => nomatch h
  | _ :: _, _ :: _, [], _, _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, h => nomatch h

theorem chainOut_sizes {l : Layout} : ∀ (placed : List Placed) (tfs : List TracedFn)
    (os : List FnOut) (frs : List ℕ) (cfs : List CompiledFunction) (pc : ℕ),
    ChainOut l pc placed tfs os frs cfs →
      totalSize (List.zipWith (fun pf fr => { (emitFn pf.fn).1 with frameSize := fr }) placed frs) =
        (os.map (·.size)).sum
  | [], [], [], [], [], _, _ => rfl
  | _ :: pfs, _ :: tfs, _ :: os, _ :: frs, _ :: cfs, _, ⟨⟨_, _, _, h4, _⟩, hr⟩ => by
      simp only [List.zipWith_cons_cons, totalSize_cons, List.map_cons, List.sum_cons]
      rw [chainOut_sizes pfs tfs os frs cfs _ hr, h4]
  | [], _ :: _, _, _, _, _, h => nomatch h
  | [], [], _ :: _, _, _, _, h => nomatch h
  | [], [], [], _ :: _, _, _, h => nomatch h
  | [], [], [], [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, _, _, _, h => nomatch h
  | _ :: _, _ :: _, [], _, _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => nomatch h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, h => nomatch h

/-! ## The jump tables' slots, by numbers -/

theorem natsDistinct_go : ∀ (l : List ℕ) (seen : NMap Unit), natsDistinct.go l seen = true →
    l.Nodup ∧ ∀ n ∈ l, seen.get? n = none
  | [], _, _ => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | n :: ns, seen, h => by
      simp only [natsDistinct.go, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨hn, hrest⟩ := h
      obtain ⟨hnd, hfresh⟩ := natsDistinct_go ns _ hrest
      have hn' : seen.get? n = none := by simpa [NMap.contains] using hn
      refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩, fun m hm => ?_⟩
      · have := hfresh n hm
        rw [NMap.get?_insert, ite_eq_left rfl] at this
        cases this
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact hn'
        · have := hfresh m hm
          rw [NMap.get?_insert] at this
          split at this
          · cases this
          · exact this

theorem natsDistinct_nodup {l : List ℕ} (h : natsDistinct l = true) : l.Nodup :=
  (natsDistinct_go l {} h).1

/-- Inserting the pairs of `l` in turn: a key `l` does not name keeps its value. -/
theorem foldl_insert_not_mem {α : Type} : ∀ (l : List (ℕ × α)) (m : NMap α) (i : ℕ),
    i ∉ l.map (·.1) → (l.foldl (fun m x => m.insert x.1 x.2) m).get? i = m.get? i
  | [], _, _, _ => rfl
  | x :: l, m, i, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [List.foldl_cons, foldl_insert_not_mem l _ i h.2, NMap.get?_insert]
      simp [h.1]

/-- Inserting the pairs of `l`, of distinct keys, in turn: each key has its value. -/
theorem foldl_insert_mem {α : Type} : ∀ (l : List (ℕ × α)) (m : NMap α) (i : ℕ) (a : α),
    (l.map (·.1)).Nodup → (i, a) ∈ l → (l.foldl (fun m x => m.insert x.1 x.2) m).get? i = some a
  | [], _, _, _, _, h => nomatch h
  | x :: l, m, i, a, hnd, h => by
      rw [List.map_cons, List.nodup_cons] at hnd
      rw [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | h
      · rw [foldl_insert_not_mem l _ _ hnd.1, NMap.get?_insert]
        simp
      · exact foldl_insert_mem l _ i a hnd.2 h

theorem entries_eq (t : Tables) : t.entries = (entriesL t.shared).toArray := rfl

theorem entriesL_keys (shared : List (List String × ℕ)) :
    (entriesL shared).map (·.1) =
      shared.reverse.flatMap fun x => (List.range x.1.length).map (x.2 + ·) := by
  simp only [entriesL, List.map_flatMap, List.map_map]
  congr 1
  funext x
  obtain ⟨cs, first⟩ := x
  simp only
  rw [List.range_eq_range']
  have : ((fun y : ℕ × String => y.1) ∘ fun (x : String × ℕ) => (first + x.2, x.1)) =
      (first + ·) ∘ Prod.snd := rfl
  rw [this, ← List.map_map, List.zipIdx_map_snd]

theorem tableSlots_eq (len : ℕ) (fills : List Fill) (entries : List (ℕ × String)) :
    tableSlots len fills.toArray entries.toArray = slotsFrom (tableMapL fills entries) len := by
  simp only [tableSlots, slotsFrom, tableMapL, List.foldl_toArray']

theorem tableSlots_get {len : ℕ} {fills : List Fill} {entries : List (ℕ × String)}
    (hnd : (fills.map (·.1) ++ entries.map (·.1)).Nodup)
    (hlt : ∀ k ∈ fills.map (·.1) ++ entries.map (·.1), k < len) :
    (∀ x ∈ fills, (tableSlots len fills.toArray entries.toArray)[x.1]? = some x.2) ∧
      ∀ x ∈ entries, (tableSlots len fills.toArray entries.toArray)[x.1]? = some (.entry x.2) := by
  let l : List (ℕ × KVal) := fills ++ entries.map fun x => (x.1, KVal.entry x.2)
  have hkeys : l.map (·.1) = fills.map (·.1) ++ entries.map (·.1) := by simp [l]
  have hm : ((entries.toArray.foldl (fun m (x : ℕ × String) => m.insert x.1 (KVal.entry x.2))
      (fills.toArray.foldl (fun m (x : Fill) => m.insert x.1 x.2) ({} : NMap KVal)))) =
      l.foldl (fun m x => m.insert x.1 x.2) {} := by
    simp only [List.foldl_toArray', l, List.foldl_append, List.foldl_map]
  have hget : ∀ i a, (i, a) ∈ l → (tableSlots len fills.toArray entries.toArray)[i]? = some a := by
    intro i a hia
    have hi : i < len := hlt i (hkeys ▸ List.mem_map_of_mem (f := (·.1)) hia)
    simp only [tableSlots]
    rw [show (fun (m : NMap KVal) (x : Fill) => match x with | (i, k) => m.insert i k) =
        fun m x => m.insert x.1 x.2 from rfl,
      show (fun (m : NMap KVal) (x : ℕ × String) => match x with | (i, c) => m.insert i (KVal.entry c)) =
        fun m x => m.insert x.1 (KVal.entry x.2) from rfl, hm]
    rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some]
    rw [foldl_insert_mem l {} i a (hkeys ▸ hnd) hia]
    rfl
  refine ⟨fun x hx => hget x.1 x.2 (List.mem_append_left _ hx), fun x hx => ?_⟩
  exact hget x.1 _ (List.mem_append_right _ (List.mem_map_of_mem (f := fun x => (x.1, KVal.entry x.2)) hx))

theorem slotsHold_of_keys {len : ℕ} {fills : List Fill} {t : Tables}
    (hnd : (fills.map (·.1) ++ (entriesL t.shared).map (·.1)).Nodup)
    (hlt : ∀ k ∈ fills.map (·.1) ++ (entriesL t.shared).map (·.1), k < len) :
    slotsHold (tableSlots len fills.toArray t.entries) fills t.shared = true := by
  obtain ⟨hf, he⟩ := tableSlots_get hnd hlt
  rw [entries_eq]
  simp only [slotsHold, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨hf, fun p hp x hx => ?_⟩
  apply he (p.2 + x.2, x.1)
  simp only [entriesL, List.mem_flatMap, List.mem_reverse, List.mem_map]
  exact ⟨p, hp, x, hx, rfl⟩

theorem fillsOfOuts_keys : ∀ (p : List TracedFn) (os : List FnOut), os.length = p.length →
    (fillsOfOuts p os).map (·.1) = os.flatMap fun o => o.fills.map (·.1)
  | [], [], _ => rfl
  | tf :: p, o :: os, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have := fillsOfOuts_keys p os h
      simp only [fillsOfOuts, List.zip_cons_cons, List.flatMap_cons, List.map_append] at this ⊢
      rw [this, fillsOfOut, List.map_map]
      rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ## `__jump_tables`, chunk by chunk -/

theorem chunked_go_range : ∀ (fuel : ℕ) (code : List OffsetInstruction),
    (code.length + chunkSize - 1) / chunkSize ≤ fuel →
      chunked.go fuel code = (List.range ((code.length + chunkSize - 1) / chunkSize)).map
        fun c => (code.drop (c * chunkSize)).take chunkSize
  | 0, code, h => by
      have : (code.length + chunkSize - 1) / chunkSize = 0 := Nat.le_zero.mp h
      rw [this]
      rfl
  | fuel + 1, [], _ => rfl
  | fuel + 1, a :: code, h => by
      have hcs : chunkSize = 2048 := rfl
      have hm : ((a :: code).length + chunkSize - 1) / chunkSize =
          (((a :: code).drop chunkSize).length + chunkSize - 1) / chunkSize + 1 := by
        rw [List.length_drop, hcs]
        simp only [List.length_cons]
        omega
      have hfuel : (((a :: code).drop chunkSize).length + chunkSize - 1) / chunkSize ≤ fuel := by
        omega
      rw [chunked.go]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      rw [chunked_go_range fuel _ hfuel, hm, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Nat.zero_mul, List.drop_zero]
      refine congrArg _ (List.map_congr_left fun c _ => ?_)
      simp only [Function.comp, List.drop_drop, Nat.succ_mul, Nat.add_comm chunkSize]

theorem chunked_eq (code : List OffsetInstruction) :
    chunked code = (List.range ((code.length + chunkSize - 1) / chunkSize)).map
      fun c => (code.drop (c * chunkSize)).take chunkSize := by
  unfold chunked
  exact chunked_go_range _ _ (by rw [show chunkSize = 2048 from rfl]; omega)

theorem drop_zipIdx {α : Type} : ∀ (l : List α) (n k : ℕ),
    (l.zipIdx n).drop k = (l.drop k).zipIdx (n + k)
  | [], _, _ => by simp
  | _ :: _, _, 0 => rfl
  | a :: l, n, k + 1 => by
      simp only [List.zipIdx_cons, List.drop_succ_cons]
      rw [drop_zipIdx l (n + 1) k, Nat.add_right_comm, Nat.add_assoc]

theorem take_zipIdx {α : Type} : ∀ (l : List α) (n k : ℕ),
    (l.zipIdx n).take k = (l.take k).zipIdx n
  | [], _, _ => by simp
  | _ :: _, _, 0 => rfl
  | a :: l, n, k + 1 => by
      simp only [List.zipIdx_cons, List.take_succ_cons]
      rw [take_zipIdx l (n + 1) k]

theorem resolvedFn_jtOf (l : Layout) (base : ℕ) (slots : Array KVal) :
    resolvedFn l 0 (jtOf base slots) = slots.toList.zipIdx.map fun x =>
      resolveOp l 0 (base + slots.size) (.set (base + x.2) x.1) := by
  simp only [resolvedFn, jtOf, Array.toList_map, Array.toList_zipIdx, List.map_map]
  rfl

theorem jtChunk_eq (l : Layout) (base : ℕ) (slots : Array KVal) (c : ℕ) :
    jtChunk l base slots c =
      ((resolvedFn l 0 (jtOf base slots)).drop (c * chunkSize)).take chunkSize := by
  rw [resolvedFn_jtOf, ← List.map_drop, ← List.map_take, drop_zipIdx, Nat.zero_add, jtChunk,
    take_zipIdx]

/-- Whether a compiled function is `__jump_tables` of `slots` at pc `0` but for its code. -/
def jtHead (slots : Array KVal) (cf : CompiledFunction) : Bool :=
  cf.name == "__jump_tables" && cf.entryPc == 0 && cf.instructionCount == slots.size &&
    cf.chunks.length == (slots.size + chunkSize - 1) / chunkSize

/-- **`__jump_tables`, chunk by chunk**: its compiled function, when each chunk is. -/
theorem jt_of_chunks {l : Layout} {base : ℕ} {slots : Array KVal} {cf : CompiledFunction}
    (hhead : jtHead slots cf = true)
    (hchunks : ∀ c < cf.chunks.length, jtChunkOk l base slots cf c = true) :
    cf = ⟨"__jump_tables", 0, slots.size, chunked (resolvedFn l 0 (jtOf base slots))⟩ := by
  simp only [jtHead, Bool.and_eq_true, beq_iff_eq] at hhead
  obtain ⟨⟨⟨hn, he⟩, hc⟩, hl⟩ := hhead
  obtain ⟨n, e, c, ch⟩ := cf
  simp only at hn he hc hl hchunks ⊢
  subst hn he hc
  simp only [CompiledFunction.mk.injEq, true_and]
  have hlen : (resolvedFn l 0 (jtOf base slots)).length = slots.size := by
    simp [resolvedFn, jtOf]
  rw [chunked_eq, hlen]
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    have := hchunks i h1
    simp only [jtChunkOk, decide_eq_true_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      Option.getD_some, jtChunk_eq] at this
    simp [this]

/-! ## The composition -/

/-- **A program compiled from its pieces.** -/
theorem compiles_of_pieces {p : List TracedFn} {os : List FnOut} {cfJt : CompiledFunction}
    {cfs : List CompiledFunction} {loops : Loops} {sigs : SMap (ℕ × ℕ)} {l : Layout} {k : ℕ}
    (hloops : loopTable p = loops) (hsigs : sigTable p = sigs)
    (hl : layoutInfo (infoOfOuts p os) (baseOf os) = l) (hchecks : progChecks p loops = true)
    (hos : os.length = p.length) (hcfs : cfs.length = p.length)
    (hpieces : ∀ j < p.length, pieceAt loops sigs l p os cfs j = true)
    (hslots : slotsOk os = true) (hne : (tablesEnd os).len ≠ 0)
    (hjt : cfJt = ⟨"__jump_tables", 0, (slotsOfOuts p os).size,
      chunked (resolvedFn l 0 (jtOf (baseOf os) (slotsOfOuts p os)))⟩)
    (hsize : nextPow2 ((tablesEnd os).len + (os.map (·.size)).sum + 1) = 2 ^ k) (hk : k ≤ 128) :
    ∃ fns, lowerProgram p = .ok (fns, slotsOfOuts p os) ∧
      (assemble fns (slotsOfOuts p os)).toFunctions = cfJt :: cfs ∧
      (assemble fns (slotsOfOuts p os)).size = 2 ^ k := by
  set n := (tablesEnd os).len with hn
  set slots := slotsOfOuts p os with hslotsDef
  have hfrs : (framesOf n os).length = p.length := by
    cases os <;> simp [framesOf] at hos ⊢ <;> omega
  have hchain : Chain loops sigs l {} n p os (framesOf n os) cfs :=
    chain_of_forall p os _ cfs {} n hos hfrs hcfs fun j hj => hpieces j hj
  obtain ⟨placed, hplace, hout⟩ := placeFns_of_chain _ _ _ _ _ _ hchain
  simp only [progChecks, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hchecks
  obtain ⟨⟨⟨hmain, hjtn⟩, hdist⟩, hloopm⟩ := hchecks
  have hpp : placeProgram p = .ok (placed, tablesEnd os) := by
    unfold placeProgram
    simp only [hmain, hjtn, hdist, hloopm, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, hloops, hsigs]
    exact hplace
  have hfills : fillsOf placed = fillsOfOuts p os := fillsOf_of_chainOut _ _ _ _ _ _ hout
  simp only [slotsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hslots
  obtain ⟨hnd, hlt⟩ := hslots
  have hkeys : (fillsOfOuts p os).map (·.1) ++ (entriesL (tablesEnd os).shared).map (·.1) =
      slotKeys os := by
    rw [fillsOfOuts_keys p os hos, entriesL_keys]
    rfl
  have hhold : slotsHold slots (fillsOf placed) (tablesEnd os).shared = true := by
    have := slotsHold_of_keys (t := tablesEnd os) (len := (tablesEnd os).len)
      (hkeys ▸ natsDistinct_nodup hnd) (hkeys ▸ hlt)
    rw [entries_eq, tableSlots_eq] at this
    rw [hfills]
    exact this
  have hlow : lowerProgram p = .ok (placed.map fun pf => (emitFn pf.fn).1, slots) := by
    unfold lowerProgram
    rw [hpp]
    have hs : tableSlots (tablesEnd os).len (fillsOf placed).toArray (tablesEnd os).entries = slots := by
      rw [hfills, entries_eq, tableSlots_eq]
      rfl
    simp only [hs, hhold, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, hlow, ?_⟩
  -- the program's first function is `main`
  have hlenp := chainOut_length _ _ _ _ _ _ hout
  obtain ⟨pf0, pfs, rfl⟩ : ∃ pf0 pfs, placed = pf0 :: pfs := by
    cases placed with
    | nil =>
        cases p with
        | nil => simp at hmain
        | cons _ _ => simp at hlenp
    | cons pf0 pfs => exact ⟨pf0, pfs, rfl⟩
  obtain ⟨tf0, p', rfl⟩ : ∃ tf0 p', p = tf0 :: p' := by
    cases p with
    | nil => simp at hlenp
    | cons tf0 p' => exact ⟨tf0, p', rfl⟩
  obtain ⟨o0, os', rfl⟩ : ∃ o0 os', os = o0 :: os' := by
    cases os with
    | nil => simp at hos
    | cons o0 os' => exact ⟨o0, os', rfl⟩
  obtain ⟨cf0, cfs', rfl⟩ : ∃ cf0 cfs', cfs = cf0 :: cfs' := by
    cases cfs with
    | nil => simp at hcfs
    | cons cf0 cfs' => exact ⟨cf0, cfs', rfl⟩
  have hsz : slots.size = n := by simp [hslotsDef, slotsOfOuts, slotsFrom, hn]
  have hsne : slots.isEmpty = false := by
    rw [Array.isEmpty_eq_false_iff, ← Array.size_pos_iff, hsz]
    omega
  obtain ⟨⟨_, _, h3, _⟩, hrest⟩ := hout
  have hwt : withTables (List.map (fun pf => (emitFn pf.fn).1) (pf0 :: pfs)) slots =
      (jtOf (baseOf (o0 :: os')) slots ::
        List.zipWith (fun pf fr => { (emitFn pf.fn).1 with frameSize := fr }) (pf0 :: pfs)
          (framesOf n (o0 :: os')), baseOf (o0 :: os')) := by
    simp only [List.map_cons, withTables, hsne, Bool.false_eq_true, ↓reduceIte, framesOf,
      List.zipWith_cons_cons, baseOf, List.head?_cons, Option.map_some, Option.getD_some, h3, jtOf]
    rw [chainOut_frames pfs p' os' _ cfs' _ hrest rfl, hsz]
  have hout' : ChainOut l n (pf0 :: pfs) (tf0 :: p') (o0 :: os') (framesOf n (o0 :: os'))
      (cf0 :: cfs') := ⟨⟨by assumption, by assumption, h3, by assumption⟩, hrest⟩
  have hfr := chainOut_frames pfs p' os' _ cfs' _ hrest rfl
  have hnames : ((withTables (List.map (fun pf => (emitFn pf.fn).1) (pf0 :: pfs)) slots).1.map
      (·.name)) = "__jump_tables" :: (tf0 :: p').map (·.core.name) := by
    rw [hwt]
    obtain ⟨h1, h2⟩ := List.cons_eq_cons.mp (chainOut_names _ _ _ _ _ _ hout')
    simp only [List.map_cons, jtOf, framesOf, List.zipWith_cons_cons, List.cons.injEq, true_and]
    refine ⟨h1, ?_⟩
    rw [← h2, hfr, List.map_map]
    rfl
  have hnd' : ((withTables (List.map (fun pf => (emitFn pf.fn).1) (pf0 :: pfs)) slots).1.map
      (·.name)).Nodup := by
    rw [hnames, List.nodup_cons]
    exact ⟨by simpa using hjtn, namesDistinct_nodup hdist⟩
  have hjsz : (jtOf (baseOf (o0 :: os')) slots).code.size = n := by simp [jtOf, hsz]
  have htot : totalSize (withTables (List.map (fun pf => (emitFn pf.fn).1) (pf0 :: pfs)) slots).1 =
      n + ((o0 :: os').map (·.size)).sum := by
    rw [hwt, totalSize_cons, chainOut_sizes _ _ _ _ _ _ hout', hjsz]
  have hsize' : (assemble (List.map (fun pf => (emitFn pf.fn).1) (pf0 :: pfs)) slots).size = 2 ^ k := by
    rw [assemble_def, assembleAt_size, layout_size, htot, hsize]
  refine ⟨?_, hsize'⟩
  rw [assemble_toFunctions _ _ hnd' (by rw [hsize']; exact Nat.pow_le_pow_right (by norm_num) hk)]
  have hinfo : (jtOf (baseOf (o0 :: os')) slots :: List.zipWith
      (fun pf fr => { (emitFn pf.fn).1 with frameSize := fr }) (pf0 :: pfs)
        (framesOf n (o0 :: os'))).map infoOf = infoOfOuts (tf0 :: p') (o0 :: os') := by
    rw [List.map_cons, chainOut_infoAt _ _ _ _ _ _ hout', infoOfOuts]
    simp only [infoOf, jtOf, hsz, ← hn, Array.size_map, Array.size_zipIdx]
  rw [hwt]
  simp only
  rw [hinfo, hl]
  simp only [fnsFrom, Nat.zero_add, hjsz]
  rw [fnsFrom_of_chainOut _ _ _ _ _ _ hout', hjt, hsz]
  rfl

/-! ## Ranges of pieces -/

section Ranges

variable {loops : Loops} {sigs : SMap (ℕ × ℕ)} {l : Layout} {p : List TracedFn} {os : List FnOut}
  {cfs : List CompiledFunction} {extra : VMap Loc → Bool}

theorem piecesIn_spec {a b : ℕ} (h : piecesIn loops sigs l p os cfs a b = true) :
    ∀ j, a ≤ j → j < b → pieceAt loops sigs l p os cfs j = true := by
  intro j h1 h2
  simp only [piecesIn, List.all_eq_true, List.mem_range'_1] at h
  exact h j ⟨h1, by omega⟩

theorem piecesIn_glue {a b c : ℕ} (h1 : piecesIn loops sigs l p os cfs a b = true)
    (h2 : piecesIn loops sigs l p os cfs b c = true) (hab : a ≤ b) (hbc : b ≤ c) :
    piecesIn loops sigs l p os cfs a c = true := by
  simp only [piecesIn, List.all_eq_true, List.mem_range'_1] at h1 h2 ⊢
  intro j hj
  by_cases hjb : j < b
  · exact h1 j ⟨hj.1, by omega⟩
  · exact h2 j ⟨by omega, by omega⟩

theorem piecesIn_single {j : ℕ} (h : pieceAt loops sigs l p os cfs j = true) :
    piecesIn loops sigs l p os cfs j (j + 1) = true := by
  simp [piecesIn, h]

theorem pieceOk_of_with {t : Tables} {tf : TracedFn} {o : FnOut} {pc0 frame : ℕ}
    {cf : CompiledFunction} (h : pieceOkWith extra loops sigs l t tf o pc0 frame cf = true) :
    pieceOk loops sigs l t tf o pc0 frame cf = true := by
  unfold pieceOk pieceOkWith at *
  split at h
  · cases h
  · simp only [Bool.and_eq_true] at h ⊢
    simp [h.1]

theorem piecesInWith_spec {a b : ℕ} (h : piecesInWith extra loops sigs l p os cfs a b = true) :
    ∀ j, a ≤ j → j < b → pieceAtWith extra loops sigs l p os cfs j = true := by
  intro j h1 h2
  simp only [piecesInWith, List.all_eq_true, List.mem_range'_1] at h
  exact h j ⟨h1, by omega⟩

theorem piecesInWith_glue {a b c : ℕ} (h1 : piecesInWith extra loops sigs l p os cfs a b = true)
    (h2 : piecesInWith extra loops sigs l p os cfs b c = true) (hab : a ≤ b) (hbc : b ≤ c) :
    piecesInWith extra loops sigs l p os cfs a c = true := by
  simp only [piecesInWith, List.all_eq_true, List.mem_range'_1] at h1 h2 ⊢
  intro j hj
  by_cases hjb : j < b
  · exact h1 j ⟨hj.1, by omega⟩
  · exact h2 j ⟨by omega, by omega⟩

theorem piecesInWith_single {j : ℕ} (h : pieceAtWith extra loops sigs l p os cfs j = true) :
    piecesInWith extra loops sigs l p os cfs j (j + 1) = true := by
  simp [piecesInWith, h]

/-- A piece with a test on the placed locations is a piece. -/
theorem pieceAt_of_with {j : ℕ} (h : pieceAtWith extra loops sigs l p os cfs j = true) :
    pieceAt loops sigs l p os cfs j = true :=
  pieceOk_of_with h

/-- **A piece with a test passes the test on the placed locations** of its function. -/
theorem extra_of_with {j : ℕ} (h : pieceAtWith extra loops sigs l p os cfs j = true) :
    extra (placedLocsAt loops sigs p os j) = true := by
  obtain ⟨pf, hpf, -, -, -, -, -, -, -, -, hx⟩ := pieceOkWith_spec h
  rw [placedLocsAt, hpf]
  exact hx

end Ranges

/-! ## The placed functions -/

theorem placeFns_cons_inv {loops : Loops} {sigs : SMap (ℕ × ℕ)} {tf : TracedFn}
    {tfs : List TracedFn} {t t' : Tables} {placed : List Placed}
    (h : placeFns loops sigs (tf :: tfs) t = .ok (placed, t')) :
    ∃ pf t1 pfs, placeFn loops sigs t tf = .ok (pf, t1) ∧ placeFns loops sigs tfs t1 = .ok (pfs, t') ∧
      placed = pf :: pfs := by
  rw [placeFns] at h
  rcases h1 : placeFn loops sigs t tf with e | ⟨pf, t1⟩
  · simp only [h1] at h
    cases h
  · simp only [h1] at h
    rcases h2 : placeFns loops sigs tfs t1 with e | ⟨pfs, t2⟩
    · simp only [h2] at h
      cases h
    · simp only [h2, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨pf, t1, pfs, rfl, h2, rfl⟩

/-- `placeFns` succeeds through every function: function `j` is placed from the jump tables the
ones before it leave. -/
theorem placeFns_getElem {loops : Loops} {sigs : SMap (ℕ × ℕ)} :
    ∀ (tfs : List TracedFn) (os : List FnOut) (t : Tables) (placed : List Placed) (t' : Tables),
      os.length = tfs.length → placeFns loops sigs tfs t = .ok (placed, t') →
      (∀ j < tfs.length, ∃ pf, placeFn loops sigs ((os.take j).foldl Tables.after t)
        (tfs.getD j default) = .ok (pf, (os.take (j + 1)).foldl Tables.after t)) →
      ∀ j < tfs.length, ∃ pf, placed[j]? = some pf ∧
        placeFn loops sigs ((os.take j).foldl Tables.after t) (tfs.getD j default) =
          .ok (pf, (os.take (j + 1)).foldl Tables.after t)
  | [], _, _, _, _, _, _, _, j, hj => by simp at hj
  | _ :: _, [], _, _, _, hos, _, _, _, _ => by simp at hos
  | tf :: tfs, o :: os, t, placed, t', hos, h, hall, j, hj => by
      obtain ⟨pf, t1, pfs, hpf, hrest, rfl⟩ := placeFns_cons_inv h
      obtain ⟨pf0, h0⟩ := hall 0 (by simp)
      simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil,
        List.getD_cons_zero, Nat.zero_add] at h0
      rw [hpf] at h0
      simp only [Except.ok.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      cases j with
      | zero =>
          refine ⟨pf, rfl, ?_⟩
          simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil,
            List.getD_cons_zero, Nat.zero_add]
          exact hpf
      | succ j =>
          obtain ⟨q, hq1, hq2⟩ := placeFns_getElem tfs os (t.after o) pfs t' (by simpa using hos)
            hrest (fun i hi => by
              obtain ⟨x, hx⟩ := hall (i + 1) (by simp; omega)
              exact ⟨x, by simpa [List.take_succ_cons] using hx⟩) j (by simp at hj; omega)
          exact ⟨q, by simpa using hq1, by simpa [List.take_succ_cons] using hq2⟩

/-- In a list of distinct keys, the element at `j` is the one found by its key. -/
theorem find?_of_getElem? {α : Type} (key : α → String) :
    ∀ (xs : List α) (j : ℕ) (x : α), (xs.map key).Nodup → xs[j]? = some x →
      xs.find? (fun y => key y == key x) = some x
  | [], _, _, _, h => by simp at h
  | y :: ys, 0, x, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp
  | y :: ys, j + 1, x, hnd, h => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      simp only [List.getElem?_cons_succ] at h
      have hx : x ∈ ys := List.mem_of_getElem? h
      have hne : key y ≠ key x := fun he => hnd.1 (he ▸ List.mem_map_of_mem hx)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact find?_of_getElem? key ys j x hnd.2 h

/-- **The places of function `j`'s values** in a program compiled from its pieces are the ones its
placement from the jump tables before it gives. -/
theorem placed_locs_of_pieces {p : List TracedFn} {os : List FnOut} {cfs : List CompiledFunction}
    {loops : Loops} {sigs : SMap (ℕ × ℕ)} {l : Layout}
    (hloops : loopTable p = loops) (hsigs : sigTable p = sigs) (hchecks : progChecks p loops = true)
    (hos : os.length = p.length) (hcfs : cfs.length = p.length)
    (hpieces : ∀ j < p.length, pieceAt loops sigs l p os cfs j = true) {j : ℕ} (hj : j < p.length) :
    (match ((match placeProgram p with
      | .ok r => r.1
      | .error _ => []) : List Placed).find? (·.fn.name == (p.getD j default).core.name) with
      | some pf => pf.locs
      | none => {}) = placedLocsAt loops sigs p os j := by
  set n := (tablesEnd os).len
  have hfrs : (framesOf n os).length = p.length := by
    cases os <;> simp [framesOf] at hos ⊢ <;> omega
  have hchain : Chain loops sigs l {} n p os (framesOf n os) cfs :=
    chain_of_forall p os _ cfs {} n hos hfrs hcfs fun j hj => hpieces j hj
  obtain ⟨placed, hplace, hout⟩ := placeFns_of_chain _ _ _ _ _ _ hchain
  simp only [progChecks, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hchecks
  obtain ⟨⟨⟨hmain, hjtn⟩, hdist⟩, hloopm⟩ := hchecks
  have hpp : placeProgram p = .ok (placed, tablesEnd os) := by
    unfold placeProgram
    simp only [hmain, hjtn, hdist, hloopm, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, hloops, hsigs]
    exact hplace
  have hall : ∀ j < p.length, ∃ pf, placeFn loops sigs ((os.take j).foldl Tables.after {})
      (p.getD j default) = .ok (pf, (os.take (j + 1)).foldl Tables.after {}) := by
    intro i hi
    obtain ⟨pf, hpf, -⟩ := pieceOk_spec (hpieces i hi)
    refine ⟨pf, ?_⟩
    rw [tablesAt] at hpf
    rw [hpf]
    have hi' : i < os.length := hos ▸ hi
    rw [List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some, List.foldl_append]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  obtain ⟨pf, hget, hpf⟩ := placeFns_getElem p os {} placed _ hos hplace hall j hj
  have hnames : placed.map (·.fn.name) = p.map (·.core.name) := by
    rw [← chainOut_names _ _ _ _ _ _ hout]
    rfl
  have hname : pf.fn.name = (p.getD j default).core.name := by
    obtain ⟨st', -, rfl, -⟩ := placeFn_ok hpf
    rfl
  rw [hpp]
  simp only
  rw [← hname, find?_of_getElem? (·.fn.name) placed j pf (hnames ▸ namesDistinct_nodup hdist) hget]
  rw [placedLocsAt, tablesAt, hpf]

end
end LeanVM.Guest.Backend
