module

public import LeanVM.Prover.ExecuteCompleteOp

/-!
# The executor's `KECCAK` is complete

`keccak_complete`: with its thirteen input cells written, the executor's `KECCAK` reads the
reference's input, writes the reference's outputs, which the reference's relation fixes, and moves
to the next instruction. The permutation's value is generalized away at once, never evaluated.
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

theorem exMapM_eq {ε α β : Type} {f : α → Except ε β} {h : α → β} :
    ∀ l : List α, (∀ x ∈ l, f x = .ok (h x)) → l.mapM f = .ok (l.map h)
  | [], _ => rfl
  | x :: l, H => by
    rw [List.mapM_cons, H x (List.mem_cons_self ..), ok_bind,
      exMapM_eq l fun y hy ↦ H y (List.mem_cons_of_mem _ hy), ok_bind]
    rfl

theorem Agree.putOuts {M : ℕ → E} (O : Fin 13 → E) :
    ∀ (l : List (ℕ × ℕ)) (m : Mem), Agree m M →
      (∀ x ∈ l, x.1 < maxCells ∧ M x.1 = O ⟨x.2 % 13, Nat.mod_lt _ (by decide)⟩) →
      ∃ m', l.foldlM (fun m (c, k) ↦ m.put c (O ⟨k % 13, Nat.mod_lt _ (by decide)⟩)) m = .ok m' ∧
        Agree m' M ∧ m ≤ m'
  | [], m, h, _ => ⟨m, rfl, h, Mem.le_refl m⟩
  | (c, k) :: l, m, h, hl => by
    obtain ⟨hc, hv⟩ := hl _ (List.mem_cons_self ..)
    obtain ⟨m1, e1, h1, le1, -⟩ := h.put hv hc
    obtain ⟨m2, e2, h2, le2⟩ := Agree.putOuts O l m1 h1 fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)
    exact ⟨m2, by rw [List.foldlM_cons, bind_ok]; exact ⟨m1, e1, e2⟩, h2, Mem.le_trans le1 le2⟩

theorem cellCount_le (o : KeccakOutputCells) : o.cellCount ≤ 13 := by
  cases o <;> decide

theorem keccak_complete {C : Ctx} {M : ℕ → E} {s : St} {rd : K → Option E} {r' : Registers K}
    {om : Fin 4 → K} {otail ob8 ocap : K} {outCells : KeccakOutputCells} {L : List ℕ} {out : ℕ}
    {inOdd outOdd : Bool} (hs : Fine M s) (hrd : RefRd rd M)
    (hL : List.Forall₂ (fun c k ↦ g ^ k = keccakInputCellOffset om otail ob8 ocap c)
      (List.finRange 13) L)
    (hsm : OpSmall (.keccak L.toArray out inOdd outOdd outCells.cellCount))
    (hpc : s.pc < C.ops.size) (hsz : C.ops.size ≤ 2 ^ 30) (hnext : NextOk C r')
    (hex : executeWith rd ⟨g ^ s.pc, g ^ s.fp⟩ (.keccak om otail ob8 ocap (g ^ out) inOdd outOdd
      outCells) = some r')
    (hmo : OpModed M s (.keccak L.toArray out inOdd outOdd outCells.cellCount)) :
    ∃ s', runOp C s (.keccak L.toArray out inOdd outOdd outCells.cellCount) = .ok s' ∧
      OpDone C M s s' r' := by
  simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hex
  obtain ⟨inp, hinp, f, hf, u, hu, hr⟩ := hex
  simp [guard] at hu hr
  rw [readCells_eq_some_iff] at hinp
  obtain ⟨hf1, -⟩ := (readFirstCells_eq_some_iff _ _ _ _ _).mp hf
  unfold KeccakCellsRelation at hu
  generalize hO : cellsOfState (keccakF1600 (stateOfCells inp inOdd)) outOdd = O at hu
  obtain ⟨hsmI, hout⟩ := hsm
  have hsmI' : ∀ i ∈ L, i < 2 ^ 28 := fun i hi ↦ hsmI i (by simpa using hi)
  have hmo' : ∀ i ∈ L, s.mem.written (s.fp + i) = true := fun i hi ↦ hmo i (by simpa using hi)
  have hlL : L.length = 13 := by rw [← hL.length_eq, List.length_finRange]
  have hin : ∀ (j : ℕ) (hj : j < 13), s.fp + L[j]'(by rw [hlL]; exact hj) < maxCells ∧
      M (s.fp + L[j]'(by rw [hlL]; exact hj)) = inp ⟨j, hj⟩ := by
    intro j hj
    have h1 := forall₂_getElem hL (i := j) (by simpa using hj) (by rw [hlL]; exact hj)
    simp only [List.getElem_finRange, Fin.cast_mk] at h1
    have h2 := hinp ⟨j, hj⟩
    rw [← h1] at h2
    exact hrd.at hs.fp (hsmI' _ (List.getElem_mem _)) h2
  have hcu : ∀ i ∈ L, s.fp + i < maxCells := fun i hi ↦ by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
    exact (hin j (by rw [← hlL]; exact hj)).1
  have hcount := cellCount_le outCells
  have hou : ∀ k, k < outCells.cellCount → s.fp + (out + k) < maxCells ∧
      M (s.fp + (out + k)) = O ⟨k % 13, Nat.mod_lt _ (by decide)⟩ := fun k hk ↦ by
    have h1 := hf1 ⟨k, by omega⟩ hk
    rw [← pow_add, ← pow_add, Nat.add_comm k out] at h1
    obtain ⟨h2, h3⟩ := hrd _ _ (by have := hs.fp; unfold maxCells at this; omega) h1
    have hk13 : (⟨k % 13, Nat.mod_lt _ (by decide)⟩ : Fin 13) = ⟨k, by omega⟩ :=
      Fin.ext (Nat.mod_eq_of_lt (by omega))
    refine ⟨h2, ?_⟩
    rw [hk13, h3, hu ⟨k, by omega⟩ hk]
  have hcells : L.toArray.toList.mapM (cellAt s.fp) = .ok (L.map (s.fp + ·)) := by
    rw [List.toList_toArray]
    exact exMapM_eq L fun i hi ↦ cellAt_eq (hcu i hi)
  have hinput : (L.map (s.fp + ·)).mapM s.mem.read = .ok ((L.map (s.fp + ·)).map M) := by
    refine exMapM_eq _ fun c hc ↦ ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    exact hs.agree.read (hmo' i hi)
  have houts : (List.range outCells.cellCount).mapM (fun k ↦ cellAt s.fp (out + k)) =
      .ok ((List.range outCells.cellCount).map fun k ↦ s.fp + (out + k)) :=
    exMapM_eq _ fun k hk ↦ cellAt_eq (hou k (List.mem_range.mp hk)).1
  have hcell : (fun c : Fin 13 ↦ ((L.map (s.fp + ·)).map M).getD c.val 0) = inp := by
    funext c
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlL]), Option.getD_some]
    simp only [List.getElem_map]
    exact (hin c.val c.isLt).2
  obtain ⟨m1, e1, h1, le1⟩ := hs.agree.putOuts O
    ((List.range outCells.cellCount).map fun k ↦ s.fp + (out + k)).zipIdx s.mem fun x hx ↦ by
      have hx' := List.mem_zipIdx_iff_getElem?.mp hx
      obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hx'
      simp only [List.length_map, List.length_range] at hlt
      simp only [List.getElem_map, List.getElem_range] at he
      rw [← he]
      exact hou x.2 hlt
  have hall : ∀ c ∈ L.map (s.fp + ·) ++ (List.range outCells.cellCount).map
      (fun k ↦ s.fp + (out + k)), c < maxCells := fun c hc ↦ by
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; exact hcu i hi
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc; exact (hou k (List.mem_range.mp hk)).1
  have h2 := h1.foldl_ensure _ m1 hall
  obtain ⟨le2, -⟩ := Mem.foldl_ensure (L.map (s.fp + ·) ++ (List.range outCells.cellCount).map
    (fun k ↦ s.fp + (out + k))) m1 h1.wf
  refine ⟨{ s with
    mem := (L.map (s.fp + ·) ++ (List.range outCells.cellCount).map
      (fun k ↦ s.fp + (out + k))).foldl Mem.ensure m1, pc := s.pc + 1 }, ?_,
    next_done ⟨h2, hs.dl, hs.small, hs.fp⟩ (Mem.le_trans le1 le2) rfl rfl rfl hr.symm hnext hpc hsz⟩
  simp only [runOp]
  rw [hcells, ok_bind, hinput, ok_bind, houts, ok_bind, hcell, hO,
    St.withMem_eq (by rw [e1, ok_bind]; rfl), ok_bind]
  rfl

end

end LeanVM.Prover.Exec
