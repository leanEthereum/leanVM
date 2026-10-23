/-
  LeanVM.Arithmetization.Completeness.Bus

  What a row sends on each of the six channels, and the counts the reads of a sequence of rows
  get.
-/

module

public import LeanVM.Arithmetization.Completeness.Rows
public import LeanVM.Arithmetization.Completeness.Balance
public import LeanVM.Arithmetization.Completeness.Skeletons

@[expose] public section

/-!
# Rows with their counts

A row of the witness is a skeleton (`Completeness.Skeletons`: a state and the instruction fetched
there) together with the numbers of its reads: `PRow`. The `j`-th memory read of a row has count
`g^(exps j)` and its bytecode read `g^bc`. `mkRows` writes the rows of a list of skeletons,
threading two counters through it: how many times each memory cell and each bytecode slot has been
read so far, so the numbers a cell's reads get are `0, 1, 2, …` in the order of the list
(`Completeness.Balance`).

`nextOf` is the state a skeleton steps to, `SkelOk` says a skeleton is the instruction fetched at
its counter and executes, and for a row of such a skeleton `PRow.sends` is what it sends
(`Completeness.Rows`). Its memory pulls and pushes are the messages `memMsg a e` of the cells it
reads, with the number `e` and `e + 1`, so that the pulls and pushes of all the rows are the
sequences the chain lemma takes (`mkRows_memPulls`, `mkRows_memPushes`); the same for the
bytecode (`mkRows_bcPulls`, `mkRows_bcPushes`).

## Wrong readings excluded

* The number of a read counts the reads of its own cell, not of the table: a cell read by two
  tables is numbered across both, which is why the rows of all six tables are numbered as one
  sequence.
* The pushed count is `g · count`, which is `g^(e + 1)` for the pulled `g^e` (`pow_succ'`), never
  `g^e + 1`.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-! ## The channels of a row's sends -/

/-- Mapping the singletons of a list and then a function is mapping the composition. -/
theorem map_flatMap_singleton {α β γ : Type} (f : α → β) (h : β → γ) (l : List α) :
    (l.flatMap fun a ↦ [f a]).map h = l.map fun a ↦ h (f a) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- A list of singletons is a map. -/
theorem flatMap_singleton_eq_map {α β : Type} (f : α → β) (l : List α) :
    (l.flatMap fun a ↦ [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- A row sends one state pull, `(pc, fp)`. -/
theorem sendsOf_statePull (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) :
    ((sendsOf pc fp next rbc e reads).filter (·.1 = StatePull.name)).map (·.2) =
      [#[pc, fp]] := by
  simp [sendsOf, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    List.filter_flatMap]

/-- A row sends one state push, the successor. -/
theorem sendsOf_statePush (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) :
    ((sendsOf pc fp next rbc e reads).filter (·.1 = StatePush.name)).map (·.2) =
      [#[next.pc, next.fp]] := by
  simp [sendsOf, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    List.filter_flatMap]

/-- A row sends one bytecode pull, the entry with the count `rbc`. -/
theorem sendsOf_bcPull (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) :
    ((sendsOf pc fp next rbc e reads).filter (·.1 = BytecodePull.name)).map (·.2) =
      [bcMsgOf pc rbc e] := by
  simp [sendsOf, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    List.filter_flatMap]

/-- A row sends one bytecode push, the entry with the count `g · rbc`. -/
theorem sendsOf_bcPush (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) :
    ((sendsOf pc fp next rbc e reads).filter (·.1 = BytecodePush.name)).map (·.2) =
      [bcMsgOf pc (g * rbc) e] := by
  simp [sendsOf, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    List.filter_flatMap]

/-- A row sends a memory pull per read. -/
theorem sendsOf_memPull (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) :
    ((sendsOf pc fp next rbc e reads).filter (·.1 = MemPull.name)).map (·.2) =
      reads.map fun x ↦ memMsgOf x.1 x.2.1 x.2.2 := by
  simp only [sendsOf, List.filter_append, List.map_append, List.filter_flatMap]
  simp [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    map_flatMap_singleton]

/-- A row sends a memory push per read, with the count `g · count`. -/
theorem sendsOf_memPush (pc fp : K) (next : Regs K) (rbc : K) (e : Vector K 8)
    (reads : List (K × K × Vector K 3)) :
    ((sendsOf pc fp next rbc e reads).filter (·.1 = MemPush.name)).map (·.2) =
      reads.map fun x ↦ memMsgOf x.1 (g * x.2.1) x.2.2 := by
  simp only [sendsOf, List.filter_append, List.map_append, List.filter_flatMap]
  simp [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    map_flatMap_singleton]

/-! ## Rows with counts -/

/-- A row of the witness: a skeleton, the numbers of its memory reads in the circuit's order, and
the number of its bytecode read. -/
structure PRow where
  /-- The state the row is stepped from and the instruction fetched there. -/
  sk : Skel
  /-- The number of each memory read: the count of the `j`-th read is `g^(exps j)`. -/
  exps : List ℕ
  /-- The number of the bytecode read: its count is `g^bc`. -/
  bc : ℕ

/-- The count of the `j`-th memory read of a row. -/
noncomputable def PRow.cnt (r : PRow) (j : ℕ) : K := g ^ r.exps.getD j 0

/-- The state a skeleton steps to over the image `img`: the successor `execute` computes, the
state itself if the instruction fails. -/
noncomputable def nextOf {κ : ℕ} (img : MemImage κ) (sk : Skel) : Regs K :=
  (execute img sk.regs sk.ins).getD sk.regs

/-- A skeleton is sound for the program and the image: the program fetches its instruction at its
counter, and the instruction executes from its state. -/
def SkelOk {κ : ℕ} (prog : Program) (img : MemImage κ) (sk : Skel) : Prop :=
  prog.fetch sk.pc = some sk.ins ∧ ∃ next, execute img sk.regs sk.ins = some next

/-- The raw row of a row of the witness, in the table of its instruction's opcode. -/
noncomputable def PRow.raw {κ : ℕ} (img : MemImage κ) (r : PRow) : Array K :=
  rowOf img r.sk.pc r.sk.fp r.cnt (g ^ r.bc) r.sk.ins

/-- What a row of the witness sends. -/
noncomputable def PRow.sends {κ : ℕ} (img : MemImage κ) (r : PRow) : List (String × Array K) :=
  sendsOf r.sk.pc r.sk.fp (nextOf img r.sk) (g ^ r.bc) (entry r.sk.ins)
    (readsOf img r.sk.fp r.cnt r.sk.ins)

/-- The row circuit of a row of an executing skeleton sends what `PRow.sends` says. -/
theorem PRow.rowSends_raw {κ : ℕ} {img : MemImage κ} {r : PRow}
    (h : ∃ next, execute img r.sk.regs r.sk.ins = some next) (data : ProverData K) :
    rowSends (opComponent r.sk.ins.opcode) (Environment.fromArray (r.raw img) data) =
      r.sends img := by
  obtain ⟨next, hn⟩ := h
  have := rowOf_sends hn r.cnt (g ^ r.bc) data
  rw [PRow.raw, this, PRow.sends]
  simp [nextOf, hn]

/-- The rows of a list of skeletons, threading the counters of the memory cells and of the
bytecode slots read so far through it. -/
noncomputable def mkRows {κ : ℕ} (img : MemImage κ) :
    (K → ℕ) → (K → ℕ) → List Skel → List PRow
  | _, _, [] => []
  | sm, sb, sk :: rest =>
      ⟨sk, readExps sm (readAddrs img sk.fp sk.ins), sb sk.pc⟩ ::
        mkRows img (readBump sm (readAddrs img sk.fp sk.ins)) (readBump sb [sk.pc]) rest

/-- The skeletons of the rows are the skeletons. -/
theorem mkRows_sk {κ : ℕ} (img : MemImage κ) (sm sb : K → ℕ) (S : List Skel) :
    (mkRows img sm sb S).map (·.sk) = S := by
  induction S generalizing sm sb with
  | nil => rfl
  | cons sk S ih => simp [mkRows, ih]

/-- A row has a number for each memory read. -/
theorem mkRows_exps_length {κ : ℕ} (img : MemImage κ) (sm sb : K → ℕ) (S : List Skel) :
    ∀ r ∈ mkRows img sm sb S,
      r.exps.length = (readAddrs img r.sk.fp r.sk.ins).length := by
  induction S generalizing sm sb with
  | nil => simp [mkRows]
  | cons sk S ih =>
    intro r hr
    simp only [mkRows, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact readExps_length _ _
    · exact ih _ _ r hr

/-! ## The messages of the memory and bytecode pairs -/

/-- The message of the memory cell `a` with the number `e`: `(a, g^e, v)` for the word the image
holds at `a`. -/
noncomputable def memMsg {κ : ℕ} (img : MemImage κ) (a : K) (e : ℕ) : Array K :=
  memMsgOf a (g ^ e) (img.limbsAt a)

/-- The entry the program holds at the counter `pc`, `0` where it holds none. -/
noncomputable def entryAt (prog : Program) (pc : K) : Vector K 8 :=
  match prog.fetch pc with
  | some ins => entry ins
  | none => 0

/-- The message of the bytecode slot at `pc` with the number `e`. -/
noncomputable def bcMsg (prog : Program) (pc : K) (e : ℕ) : Array K :=
  bcMsgOf pc (g ^ e) (entryAt prog pc)

/-- A row's memory pulls are the messages of the cells it reads, numbered as its row says. -/
theorem PRow.memPulls_eq {κ : ℕ} (img : MemImage κ) (r : PRow)
    (h : r.exps.length = (readAddrs img r.sk.fp r.sk.ins).length) :
    ((r.sends img).filter (·.1 = MemPull.name)).map (·.2) =
      List.zipWith (fun a e ↦ memMsg img a e) (readAddrs img r.sk.fp r.sk.ins) r.exps := by
  rw [PRow.sends, sendsOf_memPull, readsOf]
  have := mapIdx_eq_zipWith (fun a e ↦ ((a, g ^ e, img.limbsAt a) : K × K × Vector K 3)) r.exps
    (readAddrs img r.sk.fp r.sk.ins) h
  simp only [PRow.cnt] at *
  rw [this, List.map_zipWith]
  rfl

/-- A row's memory pushes are the messages of the cells it reads, numbered one higher. -/
theorem PRow.memPushes_eq {κ : ℕ} (img : MemImage κ) (r : PRow)
    (h : r.exps.length = (readAddrs img r.sk.fp r.sk.ins).length) :
    ((r.sends img).filter (·.1 = MemPush.name)).map (·.2) =
      List.zipWith (fun a e ↦ memMsg img a (e + 1)) (readAddrs img r.sk.fp r.sk.ins) r.exps := by
  rw [PRow.sends, sendsOf_memPush, readsOf]
  have := mapIdx_eq_zipWith (fun a e ↦ ((a, g ^ e, img.limbsAt a) : K × K × Vector K 3)) r.exps
    (readAddrs img r.sk.fp r.sk.ins) h
  simp only [PRow.cnt] at *
  rw [this, List.map_zipWith]
  congr 1
  funext a e
  simp only [memMsg, pow_succ']

/-- The memory pulls of the rows of a list of skeletons are the messages of its reads, numbered by
the chain: the reads of the list, in order, with the numbers from the counters `sm`. -/
theorem mkRows_memPulls {κ : ℕ} (img : MemImage κ) (sm sb : K → ℕ) (S : List Skel) :
    (mkRows img sm sb S).flatMap (fun r ↦ ((r.sends img).filter (·.1 = MemPull.name)).map (·.2)) =
      List.zipWith (fun a e ↦ memMsg img a e) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)
        (readExps sm (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) := by
  induction S generalizing sm sb with
  | nil => simp [mkRows, readExps]
  | cons sk S ih =>
    simp only [mkRows, List.flatMap_cons]
    rw [ih, readExps_append, List.zipWith_append (by rw [readExps_length])]
    congr 1
    exact PRow.memPulls_eq img ⟨sk, readExps sm (readAddrs img sk.fp sk.ins), sb sk.pc⟩
      (readExps_length _ _)

/-- The memory pushes of the rows of a list of skeletons, likewise. -/
theorem mkRows_memPushes {κ : ℕ} (img : MemImage κ) (sm sb : K → ℕ) (S : List Skel) :
    (mkRows img sm sb S).flatMap (fun r ↦ ((r.sends img).filter (·.1 = MemPush.name)).map (·.2)) =
      List.zipWith (fun a e ↦ memMsg img a (e + 1))
        (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)
        (readExps sm (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)) := by
  induction S generalizing sm sb with
  | nil => simp [mkRows, readExps]
  | cons sk S ih =>
    simp only [mkRows, List.flatMap_cons]
    rw [ih, readExps_append, List.zipWith_append (by rw [readExps_length])]
    congr 1
    exact PRow.memPushes_eq img ⟨sk, readExps sm (readAddrs img sk.fp sk.ins), sb sk.pc⟩
      (readExps_length _ _)

/-- A row of a skeleton the program fetches pulls the bytecode entry at its counter with its
number. -/
theorem PRow.bcPulls_eq {κ : ℕ} {prog : Program} (img : MemImage κ) (r : PRow)
    (h : prog.fetch r.sk.pc = some r.sk.ins) :
    ((r.sends img).filter (·.1 = BytecodePull.name)).map (·.2) = [bcMsg prog r.sk.pc r.bc] := by
  rw [PRow.sends, sendsOf_bcPull, bcMsg, entryAt, h]

/-- … and pushes it with the next. -/
theorem PRow.bcPushes_eq {κ : ℕ} {prog : Program} (img : MemImage κ) (r : PRow)
    (h : prog.fetch r.sk.pc = some r.sk.ins) :
    ((r.sends img).filter (·.1 = BytecodePush.name)).map (·.2) =
      [bcMsg prog r.sk.pc (r.bc + 1)] := by
  rw [PRow.sends, sendsOf_bcPush, bcMsg, entryAt, h, pow_succ']

/-- The bytecode pulls of the rows of a list of fetched skeletons are the messages of their
counters, numbered by the chain over the counters. -/
theorem mkRows_bcPulls {κ : ℕ} {prog : Program} (img : MemImage κ) (sm sb : K → ℕ)
    (S : List Skel) (hS : ∀ sk ∈ S, prog.fetch sk.pc = some sk.ins) :
    (mkRows img sm sb S).flatMap
        (fun r ↦ ((r.sends img).filter (·.1 = BytecodePull.name)).map (·.2)) =
      List.zipWith (fun pc e ↦ bcMsg prog pc e) (S.map (·.pc)) (readExps sb (S.map (·.pc))) := by
  induction S generalizing sm sb with
  | nil => simp [mkRows, readExps]
  | cons sk S ih =>
    simp only [mkRows, List.flatMap_cons, List.map_cons, readExps, List.zipWith_cons_cons]
    rw [PRow.bcPulls_eq img _ (hS sk List.mem_cons_self)]
    simp only [List.singleton_append]
    congr 1
    exact ih _ _ fun sk' h ↦ hS sk' (List.mem_cons_of_mem _ h)

/-- The bytecode pushes of the rows of a list of fetched skeletons, likewise. -/
theorem mkRows_bcPushes {κ : ℕ} {prog : Program} (img : MemImage κ) (sm sb : K → ℕ)
    (S : List Skel) (hS : ∀ sk ∈ S, prog.fetch sk.pc = some sk.ins) :
    (mkRows img sm sb S).flatMap
        (fun r ↦ ((r.sends img).filter (·.1 = BytecodePush.name)).map (·.2)) =
      List.zipWith (fun pc e ↦ bcMsg prog pc (e + 1)) (S.map (·.pc))
        (readExps sb (S.map (·.pc))) := by
  induction S generalizing sm sb with
  | nil => simp [mkRows, readExps]
  | cons sk S ih =>
    simp only [mkRows, List.flatMap_cons, List.map_cons, readExps, List.zipWith_cons_cons]
    rw [PRow.bcPushes_eq img _ (hS sk List.mem_cons_self)]
    simp only [List.singleton_append]
    congr 1
    exact ih _ _ fun sk' h ↦ hS sk' (List.mem_cons_of_mem _ h)

/-- The state pulls of the rows are the states of the skeletons. -/
theorem mkRows_statePulls {κ : ℕ} (img : MemImage κ) (sm sb : K → ℕ) (S : List Skel) :
    (mkRows img sm sb S).flatMap
        (fun r ↦ ((r.sends img).filter (·.1 = StatePull.name)).map (·.2)) =
      S.map fun sk ↦ #[sk.pc, sk.fp] := by
  have h : ∀ r : PRow, ((r.sends img).filter (·.1 = StatePull.name)).map (·.2) =
      [#[r.sk.pc, r.sk.fp]] := fun r ↦ sendsOf_statePull _ _ _ _ _ _
  simp only [h]
  rw [flatMap_singleton_eq_map]
  calc (mkRows img sm sb S).map (fun r ↦ #[r.sk.pc, r.sk.fp])
      = ((mkRows img sm sb S).map (·.sk)).map (fun sk ↦ #[sk.pc, sk.fp]) := by
        rw [List.map_map]; rfl
    _ = S.map (fun sk ↦ #[sk.pc, sk.fp]) := by rw [mkRows_sk]

/-- The state pushes of the rows are the successors of the skeletons. -/
theorem mkRows_statePushes {κ : ℕ} (img : MemImage κ) (sm sb : K → ℕ) (S : List Skel) :
    (mkRows img sm sb S).flatMap
        (fun r ↦ ((r.sends img).filter (·.1 = StatePush.name)).map (·.2)) =
      S.map fun sk ↦ #[(nextOf img sk).pc, (nextOf img sk).fp] := by
  have h : ∀ r : PRow, ((r.sends img).filter (·.1 = StatePush.name)).map (·.2) =
      [#[(nextOf img r.sk).pc, (nextOf img r.sk).fp]] := fun r ↦ sendsOf_statePush _ _ _ _ _ _
  simp only [h]
  rw [flatMap_singleton_eq_map]
  calc (mkRows img sm sb S).map (fun r ↦ #[(nextOf img r.sk).pc, (nextOf img r.sk).fp])
      = ((mkRows img sm sb S).map (·.sk)).map
          (fun sk ↦ #[(nextOf img sk).pc, (nextOf img sk).fp]) := by
        rw [List.map_map]; rfl
    _ = S.map (fun sk ↦ #[(nextOf img sk).pc, (nextOf img sk).fp]) := by rw [mkRows_sk]

end LeanVM.Arithmetization
