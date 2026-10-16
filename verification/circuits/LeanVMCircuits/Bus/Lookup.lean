module

public import LeanVMCircuits.Bus.Fingerprint

@[expose] public section

/-!
# Lookup correctness

Theorem `thm:omc` and Corollary `cor:addrrange` of `doc/leanvm/body/06-bus-interactions.tex`: when the reads of a
lookup array and its producer are the only flushes carrying the array's separator, balance makes every read an
entry of the array and reads entry `i` exactly `m_i` times. The bytecode is the instance `bytecode`.
-/

namespace LeanVMCircuits.Bus

open LeanVMCircuits.Rec

/-- A lookup array (§sec:lookup): `size` entries of `n` components, at pairwise distinct addresses, under a separator. -/
structure LookupArray (n : ℕ) where
  sep : K
  size : ℕ
  addr : Fin size → K
  addr_injective : Function.Injective addr
  entry : Fin size → Vector K n

namespace LookupArray

variable {n : ℕ} (lut : LookupArray n)

/-- The tuple `⟨sep, a, v⟩` of a read of `v` at `a`. -/
noncomputable def readTuple (a : K) (v : Vector K n) : Tuple := tuple (lut.sep :: a :: v.toList)

/-- Entry `i` as a tuple, `e_i`. -/
noncomputable def entryTuple (i : Fin lut.size) : Tuple := lut.readTuple (lut.addr i) (lut.entry i)

/-- The array's flushes: a pull per read, and its producer pushing entry `i` with multiplicity `mult i`. -/
noncomputable def flushes (mult : Fin lut.size → ℕ) (reads : List (K × Vector K n)) : Flushes where
  pulls := reads.map fun r => lut.readTuple r.1 r.2
  produced := (List.finRange lut.size).map fun i => (lut.entryTuple i, mult i)

theorem readTuple_sep (a : K) (v : Vector K n) : (lut.readTuple a v)[0] = lut.sep := by
  simp [readTuple, tuple_get]

theorem readTuple_injective (hn : n + 2 ≤ 16) {a a' : K} {v v' : Vector K n}
    (h : lut.readTuple a v = lut.readTuple a' v') : a = a' ∧ v = v' := by
  have := tuple_injective (by simp) (by simp; omega) h
  simp only [List.cons.injEq, true_and] at this
  exact ⟨ this.1, Vector.toList_inj.mp this.2 ⟩

theorem entryTuple_injective (hn : n + 2 ≤ 16) : Function.Injective lut.entryTuple := by
  intro i j h
  exact lut.addr_injective (lut.readTuple_injective hn h).1

/--
Theorem `thm:omc`. Let the reads and the producer be the only flushes carrying the array's separator, the rest of
the bus being `rest`. If the bus balances, with the producer pushing entry `i` with multiplicity `mult i`, then every
read is an entry, `(a_j, v_j) = (addr i, entry i)`, and entry `i` is read exactly `mult i` times.
-/
theorem lookup_correct (hn : n + 2 ≤ 16) (mult : Fin lut.size → ℕ) (reads : List (K × Vector K n))
    (rest : Flushes) (avoids : rest.Avoids fun t => t[0] = lut.sep)
    (balance : (rest ++ lut.flushes mult reads).Balanced) :
    (∀ r ∈ reads, ∃ i, r = (lut.addr i, lut.entry i)) ∧
      ∀ i, Multiset.count (lut.addr i, lut.entry i) (reads : Multiset (K × Vector K n)) = mult i := by
  have sep_eq := Flushes.filter_eq_of_balanced balance fun t => t[0] = lut.sep
  simp only [Flushes.pushed_append, Flushes.pulled_append, Multiset.filter_add,
    Flushes.filter_pushed_of_avoids avoids, Flushes.filter_pulled_of_avoids avoids, zero_add] at sep_eq
  have all_sep : ∀ t ∈ (lut.flushes mult reads).pushed + (lut.flushes mult reads).pulled, t[0] = lut.sep := by
    intro t t_mem
    rcases Multiset.mem_add.mp t_mem with t_mem | t_mem
    · rcases Flushes.mem_pushed.mp t_mem with t_mem | ⟨ p, p_mem, -, rfl ⟩
      · simp [flushes] at t_mem
      · simp only [flushes, List.mem_map, List.mem_finRange, true_and] at p_mem
        obtain ⟨ i, rfl ⟩ := p_mem
        exact lut.readTuple_sep _ _
    · simp only [flushes, Flushes.pulled, Multiset.mem_coe, List.mem_map] at t_mem
      obtain ⟨ r, -, rfl ⟩ := t_mem
      exact lut.readTuple_sep _ _
  rw [Multiset.filter_eq_self.mpr fun t ht => all_sep t (Multiset.mem_add.mpr (Or.inl ht)),
    Multiset.filter_eq_self.mpr fun t ht => all_sep t (Multiset.mem_add.mpr (Or.inr ht))] at sep_eq
  -- the reads' tuples are the entries, each as often as its multiplicity
  have key : ((reads.map fun r => lut.readTuple r.1 r.2 : List Tuple) : Multiset Tuple) =
      ((List.finRange lut.size).map fun i => Multiset.replicate (mult i) (lut.entryTuple i)).sum := by
    simpa [flushes, Flushes.pushed, Flushes.pulled, List.map_map, Function.comp_def] using sep_eq.symm
  have read_injective : Function.Injective fun r : K × Vector K n => lut.readTuple r.1 r.2 := by
    intro r r' h
    have := lut.readTuple_injective hn h
    exact Prod.ext this.1 this.2
  constructor
  · intro r r_mem
    have mem : lut.readTuple r.1 r.2 ∈ ((List.finRange lut.size).map fun i =>
        Multiset.replicate (mult i) (lut.entryTuple i)).sum := by
      rw [← key]
      exact Multiset.mem_coe.mpr (List.mem_map_of_mem r_mem)
    obtain ⟨ i, -, i_mem ⟩ := mem_sum_map.mp mem
    have := lut.readTuple_injective hn (Multiset.eq_of_mem_replicate i_mem)
    exact ⟨ i, Prod.ext this.1 this.2 ⟩
  · intro i
    have := congrArg (Multiset.count (lut.entryTuple i)) key
    rw [← Multiset.map_coe, count_sum_map] at this
    have count_reads : Multiset.count (lut.entryTuple i)
        (Multiset.map (fun r : K × Vector K n => lut.readTuple r.1 r.2) (reads : Multiset (K × Vector K n))) =
          Multiset.count (lut.addr i, lut.entry i) (reads : Multiset (K × Vector K n)) :=
      Multiset.count_map_eq_count' _ _ read_injective (lut.addr i, lut.entry i)
    rw [count_reads] at this
    rw [this]
    simp only [Multiset.count_replicate, (lut.entryTuple_injective hn).eq_iff]
    rw [← Fin.sum_univ_def, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]

/-- Corollary `cor:addrrange`: every read address is an entry address. -/
theorem read_addr_in_range (hn : n + 2 ≤ 16) (mult : Fin lut.size → ℕ) (reads : List (K × Vector K n))
    (rest : Flushes) (avoids : rest.Avoids fun t => t[0] = lut.sep)
    (balance : (rest ++ lut.flushes mult reads).Balanced) :
    ∀ r ∈ reads, ∃ i, r.1 = lut.addr i := by
  intro r r_mem
  obtain ⟨ i, rfl ⟩ := (lut.lookup_correct hn mult reads rest avoids balance).1 r r_mem
  exact ⟨ i, rfl ⟩

/-- The array's producer (§sec:lookup): entry `i` with the bit columns `bits i` of its multiplicity. -/
noncomputable def producer (bits : Fin lut.size → ℕ → K) (nbit : ℕ)
    (boolean : ∀ i, ∀ k < nbit, bits i k = 0 ∨ bits i k = 1) : Producer where
  entries := (List.finRange lut.size).map fun i => (lut.entryTuple i, bits i)
  nbit := nbit
  boolean := by
    intro p hp k hk
    obtain ⟨ i, -, rfl ⟩ := List.mem_map.mp hp
    exact boolean i k hk

/--
Theorem `thm:omc` from the product check itself: if the pushed tuples' factors times the producer's bit leaves equal
the pulled tuples' factors, the reads being pulls, as polynomials in the formal challenges, then every read is an
entry, and entry `i` is read exactly `m_i = ∑_k b_{i,k} 2^k` times.
-/
theorem lookup_correct_of_product_check (hn : n + 2 ≤ 16) (bits : Fin lut.size → ℕ → K) (nbit : ℕ)
    (boolean : ∀ i, ∀ k < nbit, bits i k = 0 ∨ bits i k = 1) (reads : List (K × Vector K n))
    (rest : Flushes) (avoids : rest.Avoids fun t => t[0] = lut.sep)
    (check : product rest.pushed * (lut.producer bits nbit boolean).leaves =
      product (rest.pulled + ((reads.map fun r => lut.readTuple r.1 r.2 : List Tuple) : Multiset Tuple))) :
    (∀ r ∈ reads, ∃ i, r = (lut.addr i, lut.entry i)) ∧
      ∀ i, Multiset.count (lut.addr i, lut.entry i) (reads : Multiset (K × Vector K n)) =
        bitsValue (bits i) nbit := by
  let readFlushes : Flushes := { pulls := reads.map fun r => lut.readTuple r.1 r.2 }
  have balance := balanced_of_product_check (rest ++ readFlushes) (lut.producer bits nbit boolean) (by
    simpa [readFlushes, Flushes.pushed, Flushes.pulled] using check)
  apply lut.lookup_correct hn _ reads rest avoids
  rw [Flushes.balanced_iff] at balance ⊢
  have pushed_eq : (lut.producer bits nbit boolean).flushes.pushed =
      (lut.flushes (fun i => bitsValue (bits i) nbit) reads).pushed := by
    simp [Producer.flushes, producer, flushes, Flushes.pushed, List.map_map, Function.comp_def]
  have pulled_eq : (readFlushes ++ (lut.producer bits nbit boolean).flushes).pulled =
      (lut.flushes (fun i => bitsValue (bits i) nbit) reads).pulled := by
    simp [Producer.flushes, flushes, Flushes.pulled, readFlushes]
  simp only [Flushes.pushed_append, Flushes.pulled_append] at balance pulled_eq ⊢
  rw [← pushed_eq, ← pulled_eq, ← add_assoc]
  convert balance using 2
  simp [readFlushes, Flushes.pushed]

end LookupArray

/--
The bytecode (§sec:bytecode) as a lookup array: `2^kbc` entries of ten decoded fields, entry `i` at the byte
address `tbase + 4 i` read as a word of `K`, under the separator `g^2`.
-/
noncomputable def bytecode (tbase kbc : ℕ) (fits : tbase + 4 * 2 ^ kbc ≤ 2 ^ 64)
    (decoded : Fin (2 ^ kbc) → Vector K 10) : LookupArray 10 where
  sep := sepBC
  size := 2 ^ kbc
  addr i := ofWord (tbase + 4 * i)
  addr_injective := by
    intro i j h
    have hi := i.isLt
    have hj := j.isLt
    have := ofWord_injective (by omega) (by omega) h
    ext
    omega
  entry := decoded

/--
Lookup correctness for the bytecode: if every row's read of its instruction and the bytecode's producer are the only
flushes under the bytecode separator, balance makes every read the decoded entry at an instruction address
`tbase + 4 i`, read exactly `mult i` times.
-/
theorem bytecode_reads_correct (tbase kbc : ℕ) (fits : tbase + 4 * 2 ^ kbc ≤ 2 ^ 64)
    (decoded : Fin (2 ^ kbc) → Vector K 10) (mult : Fin (2 ^ kbc) → ℕ) (reads : List (K × Vector K 10))
    (rest : Flushes) (avoids : rest.Avoids fun t => t[0] = sepBC)
    (balance : (rest ++ (bytecode tbase kbc fits decoded).flushes mult reads).Balanced) :
    (∀ r ∈ reads, ∃ i : Fin (2 ^ kbc), r = (ofWord (tbase + 4 * i), decoded i)) ∧
      ∀ i : Fin (2 ^ kbc), Multiset.count (ofWord (tbase + 4 * i), decoded i) (reads : Multiset (K × Vector K 10)) =
        mult i :=
  (bytecode tbase kbc fits decoded).lookup_correct (by norm_num) mult reads rest avoids balance

end LeanVMCircuits.Bus
