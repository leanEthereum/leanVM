/-
  LeanVM.Arithmetization.Soundness.MemChannel

  Soundness of the memory channel: in a satisfying witness every pulled memory tuple is a correct
  read of the image the prover data names.
-/

module

public import LeanVM.Arithmetization.Soundness.BytecodeChannel
public import LeanVM.Arithmetization.Soundness.Lookup

@[expose] public section

/-!
# Soundness of the memory channel

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `b41c196b`. Specification
Lemma 6.3, Theorem 6.4 and Corollary 6.5 (`doc/leanvm/body/06-bus-interactions.tex`, §6.2 to
§6.3) for the memory pair, as `mem_channel_sound`: the guarantee of the memory pull
(`MemPull.Guarantees`, `Arithmetization.Channels`) for every memory pull of a witness of the
constraint statement `SatisfiedBy` of multiplicity `1`: every memory pull but the cancelled
gated pulls of `KECCAK` output cells (leanVM main `40f877dc`, `memory_coords_if`). It
serves `constraintSoundness`.

**The argument.** A memory message `(addr, count, v)` is read as the triple of its address, count
and limbs (`memMsgOf`, injective). The witness pulls the reads of the six tables, their gated
reads, and the memory block's finalizes, and pushes the reads bumped by `g`, the gated reads at
the gated counter, and the block's seeds `(g^i, 1, m_i)`, one per word of the image
(`Soundness.Bus`); `SatisfiedBy.mem_balanced` makes the two lists permutations of each other.
Every gate is `0` or `1` (`opRecs_bits`): a row's bytecode coordinates are the program's entry
(`opRecs_bc_sound`), whose output flags decode. So a gated read at flag `1` pulls `(a, c, v)` and
pushes `(a, g·c, v)`, a read; at flag `0` it pulls and pushes the one tuple `(a, c, v)`, which
`perm_cancel_mid` drops from both sides (`mem_triples_perm`). The counts of the reads are nonzero
(`CountsNonzero`, which covers every memory pull of the six tables), there are fewer than
`2^64 - 1` reads (`opReads_length_lt`, from `Caps`: at most twenty-six reads per row, `2^32` rows
per table, six tables), and each finalize has a seed's key. So `lookup_sound` makes every read's
key, its address and limbs, a seed's: `(g^i, m_i)`, which is a correct read of word `i`
(`MemoryImage.read_gpow`, as `κ ≤ 32`). A pull of multiplicity `1` is a read a row makes or a
finalize (`mem_pull_of_mult`), hence a correct read (`mem_channel_sound`).

## Wrong readings excluded

* The finalize counts are not checked by the verifier (§6.2 "Nothing checks the finalize counts")
  and are not used: a finalize pull is a correct read by its key alone.
* The guarantee is about the limbs, not the word: two limb triples naming the same word of `E`
  would be different keys, and the seed's limbs are the image's (`limbsOf`).
* A cancelled gated pull is not claimed to be a read: its values are the row's output lanes,
  which no memory cell need hold, and its guarantee is not assumed (multiplicity `0`).
* The gates are not assumed bits: a gate other than `0` and `1` would push a counter that is
  neither `g·count` nor `count`, and is excluded by the bytecode channel alone, never by the
  memory pair.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component EnsembleWitness)

variable {prog : LeanIsaProgram} {κ : ℕ} {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog κ)}

/-! ## Memory messages as triples -/

/-- A memory message as its triple. -/
def memMsgOfTriple (x : K × K × Vector K 2) : Array K := memMsgOf x.1 x.2.1 x.2.2

/-- The triple of a memory message, `0` for a missing coordinate. -/
def tripleOfMemMsg (a : Array K) : K × K × Vector K 2 :=
  (a.getD 0 0, a.getD 1 0, #v[a.getD 2 0, a.getD 3 0])

/-- A vector of two is its entries. -/
theorem vec2_eta (v : Vector K 2) : #v[v[0], v[1]] = v := by
  refine Vector.ext fun i hi ↦ ?_
  interval_cases i <;> rfl

/-- Reading a memory message back gives its triple. -/
theorem tripleOfMemMsg_memMsgOfTriple (x : K × K × Vector K 2) :
    tripleOfMemMsg (memMsgOfTriple x) = x := by
  obtain ⟨a, c, v⟩ := x
  simp only [tripleOfMemMsg, memMsgOfTriple, memMsgOf]
  simp [vec2_eta]

/-- Memory messages are injective in their triple. -/
theorem memMsgOfTriple_injective : Function.Injective memMsgOfTriple := fun x y h ↦ by
  rw [← tripleOfMemMsg_memMsgOfTriple x, h, tripleOfMemMsg_memMsgOfTriple]

/-- A typed memory message flattens to the message of its triple. -/
theorem toElements_memMsg (m : MemMsg K) :
    (toElements m).toArray = memMsgOfTriple (m.addr, m.count, m.v) :=
  memMsg_toArray m

/-- Reading a memory message back gives its coordinates. -/
theorem tripleOfMemMsg_memMsgOf (a c : K) (v : Vector K 2) :
    tripleOfMemMsg (memMsgOf a c v) = (a, c, v) :=
  tripleOfMemMsg_memMsgOfTriple (a, c, v)

/-! ## The memory pair -/

/-- The reads the rows of the six tables make: each row's reads and gated reads at flag `1`. -/
def opReads (w : EnsembleWitness (leanIsaEnsemble prog κ)) (f : Air.Flat.Table K × Array K → RowRec) :
    List (K × K × Vector K 2) :=
  (opPairs w).flatMap fun p ↦ (f p).real

/-- The cancelled pairs of the rows of the six tables: their gated reads at flag `0`. -/
def opSkips (w : EnsembleWitness (leanIsaEnsemble prog κ)) (f : Air.Flat.Table K × Array K → RowRec) :
    List (K × K × Vector K 2) :=
  (opPairs w).flatMap fun p ↦ (f p).skips

/-- A read pushed back: its count multiplied by `g`. -/
def bumpRead (x : K × K × Vector K 2) : K × K × Vector K 2 := (x.1, g * x.2.1, x.2.2)

/-- The gated reads at a flag other than `1` are those at flag `0`, when every gate is a bit. -/
theorem filter_not_one {l : List (K × K × K × Vector K 2)} (hb : ∀ y ∈ l, y.1 = 0 ∨ y.1 = 1) :
    l.filter (fun y ↦ !decide (y.1 = 1)) = l.filter fun y ↦ y.1 = 0 := by
  refine List.filter_congr fun y hy ↦ ?_
  rcases hb y hy with h | h <;> simp [h]

/-- **A row's memory pulls**, when its gates are bits: up to order, the reads it makes and its
cancelled pairs. -/
theorem chanOf_rowRec_memPull_perm (x : RowRec) (hb : ∀ y ∈ x.gated, y.1 = 0 ∨ y.1 = 1) :
    (chanOf MemPull.name x.sends).Perm ((x.real ++ x.skips).map memMsgOfTriple) := by
  rw [RowRec.sends, chanOf, List.filter_append, List.map_append, sendsOf_memPull,
    gatedSends_memPull, RowRec.real, RowRec.skips, List.append_assoc, List.map_append]
  refine List.Perm.append (by rfl) ?_
  have hp := (List.filter_append_perm (fun y ↦ decide (y.1 = 1)) x.gated).map
    (fun y : K × K × K × Vector K 2 ↦ memMsgOf y.2.1 y.2.2.1 y.2.2.2)
  rw [filter_not_one hb] at hp
  simpa [List.map_map, Function.comp_def, memMsgOfTriple] using hp.symm

/-- **A row's memory pushes**, when its gates are bits: up to order, the reads it makes bumped by
`g`, and its cancelled pairs as they are. -/
theorem chanOf_rowRec_memPush_perm (x : RowRec) (hb : ∀ y ∈ x.gated, y.1 = 0 ∨ y.1 = 1) :
    (chanOf MemPush.name x.sends).Perm ((x.real.map bumpRead ++ x.skips).map memMsgOfTriple) := by
  rw [RowRec.sends, chanOf, List.filter_append, List.map_append, sendsOf_memPush,
    gatedSends_memPush, RowRec.real, RowRec.skips]
  simp only [List.map_append, List.append_assoc]
  refine List.Perm.append (by simp [List.map_map, Function.comp_def, memMsgOfTriple, bumpRead])
    ?_
  rw [← List.map_append]
  have hp := (List.filter_append_perm (fun y ↦ decide (y.1 = 1)) x.gated).map
    (fun y : K × K × K × Vector K 2 ↦ memMsgOf y.2.1 (gatedCount y.1 y.2.2.1) y.2.2.2)
  rw [filter_not_one hb] at hp
  have h1 : ∀ y ∈ x.gated.filter (fun y ↦ decide (y.1 = 1)),
      memMsgOf y.2.1 (gatedCount y.1 y.2.2.1) y.2.2.2 = memMsgOfTriple (bumpRead y.2) := by
    intro y hy
    rw [show y.1 = 1 by simpa using (List.mem_filter.mp hy).2, gatedCount_one]
    rfl
  have h0 : ∀ y ∈ x.gated.filter (fun y ↦ decide (y.1 = 0)),
      memMsgOf y.2.1 (gatedCount y.1 y.2.2.1) y.2.2.2 = memMsgOfTriple y.2 := by
    intro y hy
    rw [show y.1 = 0 by simpa using (List.mem_filter.mp hy).2, gatedCount_zero]
    rfl
  rw [List.map_append, List.map_congr_left h1, List.map_congr_left h0] at hp
  simpa [List.map_map, Function.comp_def] using hp.symm

/-- A list cancels from the middle of both sides of a permutation. -/
theorem perm_cancel_mid {α : Type} {a b c x y : List α} (h : ((a ++ c) ++ x).Perm ((b ++ c) ++ y)) :
    (a ++ x).Perm (b ++ y) := by
  have hc : ∀ u v : List α, ((u ++ c) ++ v).Perm ((u ++ v) ++ c) := fun u v ↦ by
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  exact (List.perm_append_right_iff c).mp ((hc a x).symm.trans (h.trans (hc b y)))

/-- **The memory pair of a satisfying witness, as triples**, when every row's gates are bits: the
reads the rows make, bumped, and the seeds are a permutation of those reads and the finalizes; the
cancelled pairs, pushed and pulled alike, drop out. -/
theorem mem_triples_perm (h : SatisfiedByB prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    {mfin : Fin (2 ^ (imageOf w.data).1) → K} {bfin : Fin (2 ^ prog.logSize) → K}
    (hall : allSends w = verifierSends prog ++ (opPairs w).flatMap (fun p ↦ (f p).sends) ++
      memSeedSends (imageOf w.data).2 mfin ++ bcSeedSends prog bfin)
    (hbits : ∀ p ∈ opPairs w, ∀ y ∈ (f p).gated, y.1 = 0 ∨ y.1 = 1) :
    ((opReads w f).map bumpRead ++ (List.finRange (2 ^ (imageOf w.data).1)).map fun i : Fin _ ↦
        (addressOfIndex i, 1, limbsOf (imageOf w.data).2 i)).Perm
      (opReads w f ++ (List.finRange (2 ^ (imageOf w.data).1)).map fun i : Fin _ ↦
        (addressOfIndex i, mfin i, limbsOf (imageOf w.data).2 i)) := by
  have hb := h.mem_balanced
  unfold BalancedPair at hb
  rw [messagesOn_eq_chanOf, messagesOn_eq_chanOf, chanOf_allSends _ hall,
    chanOf_allSends _ hall] at hb
  simp only [Channel.toRaw_name] at hb
  rw [chanOf_verifier_eq_nil (by simp [MemPush, StatePull]) (by simp [MemPush, StatePush]),
    chanOf_verifier_eq_nil (by simp [MemPull, StatePull]) (by simp [MemPull, StatePush]),
    chanOf_bcSeed_eq_nil _ (by simp [MemPush, BytecodePull]) (by simp [MemPush, BytecodePush]),
    chanOf_bcSeed_eq_nil _ (by simp [MemPull, BytecodePull]) (by simp [MemPull, BytecodePush]),
    chanOf_memSeed_push, chanOf_memSeed_pull] at hb
  simp only [List.nil_append, List.append_nil] at hb
  have hP : ((opPairs w).flatMap fun p ↦ chanOf MemPush.name (f p).sends).Perm
      (((opReads w f).map bumpRead ++ opSkips w f).map memMsgOfTriple) := by
    refine (List.Perm.flatMap_left _ fun p hp ↦ chanOf_rowRec_memPush_perm (f p) (hbits p hp)).trans
      ?_
    simp only [opReads, opSkips, List.map_append, List.map_flatMap]
    exact flatMap_append_perm _ _ _
  have hQ : ((opPairs w).flatMap fun p ↦ chanOf MemPull.name (f p).sends).Perm
      ((opReads w f ++ opSkips w f).map memMsgOfTriple) := by
    refine (List.Perm.flatMap_left _ fun p hp ↦ chanOf_rowRec_memPull_perm (f p) (hbits p hp)).trans
      ?_
    simp only [opReads, opSkips, List.map_append, List.map_flatMap]
    exact flatMap_append_perm _ _ _
  have h2 := (((hP.symm.append_right _).trans hb).trans (hQ.append_right _)).map tripleOfMemMsg
  simp only [List.map_append, List.map_map, Function.comp_def, tripleOfMemMsg_memMsgOfTriple,
    tripleOfMemMsg_memMsgOf, List.map_id'] at h2
  exact perm_cancel_mid h2

/-- Every row's gates are bits: its bytecode coordinates are the program's entry (the bytecode
channel), an instruction's. -/
theorem opRecs_bits (h : SatisfiedByB prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) : ∀ p ∈ opPairs w, ∀ y ∈ (f p).gated, y.1 = 0 ∨ y.1 = 1 := by
  intro p hp
  obtain ⟨k, -, he⟩ := opRecs_bc_sound h hf hp
  exact (hf p hp).2.2.2.1 ⟨_, he⟩

/-- Every read the rows make, and every finalize, has a seed's address and limbs. -/
theorem mem_reads_seeded (h : SatisfiedByB prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) {mfin : Fin (2 ^ (imageOf w.data).1) → K} {bfin : Fin (2 ^ prog.logSize) → K}
    (hall : allSends w = verifierSends prog ++ (opPairs w).flatMap (fun p ↦ (f p).sends) ++
      memSeedSends (imageOf w.data).2 mfin ++ bcSeedSends prog bfin) :
    ∀ x ∈ opReads w f ++ (List.finRange (2 ^ (imageOf w.data).1)).map fun i : Fin _ ↦
      (addressOfIndex i, mfin i, limbsOf (imageOf w.data).2 i),
      ∃ i : Fin (2 ^ (imageOf w.data).1), x.1 = addressOfIndex i ∧ x.2.2 = limbsOf (imageOf
          w.data).2 i := by
  have hperm := mem_triples_perm h hall (opRecs_bits h hf)
  let key : K × K × Vector K 2 → K × Vector K 2 := fun x ↦ (x.1, x.2.2)
  have hseeded := lookup_sound key (·.2.1) bumpRead (opReads w f) _ _ (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) hperm
    (fun x hx ↦ by
      obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
      exact (opRecs_counts_nonzero h hf hp).1 x hx)
    (opReads_length_lt h hf)
    (fun x hx ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map.mpr ⟨_, List.mem_map_of_mem (List.mem_finRange i), rfl⟩)
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨y, hy, hyx⟩ := List.mem_map.mp (hseeded x hx)
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
    exact ⟨i, (congrArg Prod.fst hyx).symm, (congrArg Prod.snd hyx).symm⟩
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact ⟨i, rfl, rfl⟩

/-- A memory pull of multiplicity `1` of a satisfying witness is a read a row makes or a
finalize: the memory block pulls the finalizes; a row of the six tables pulls at `1` only the
reads it makes (`OpRow`); the verifier and the bytecode block pull no memory. -/
theorem mem_pull_of_mult (h : SatisfiedByB prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) {mfin : Fin (2 ^ (imageOf w.data).1) → K}
    (hmb : tableSends (tableAt w 6) = memSeedSends (imageOf w.data).2 mfin) :
    ∀ i ∈ w.interactions, i.channel.name = MemPull.name → i.mult = 1 →
      i.msg ∈ (opReads w f ++ (List.finRange (2 ^ (imageOf w.data).1)).map fun i : Fin _ ↦
        (addressOfIndex i, mfin i, limbsOf (imageOf w.data).2 i)).map memMsgOfTriple := by
  intro i hi hn hm
  unfold EnsembleWitness.interactions at hi
  rcases List.mem_append.mp hi with hv | hi
  · -- The verifier pulls no memory: it sends on the state pair only.
    have hsend : (i.channel.name, i.msg) ∈ verifierSends prog := by
      rw [verifierSends, ← verifier_sends prog (Environment.fromInput w.publicInput w.data)]
      exact List.mem_map_of_mem (f := fun i : Interaction K ↦ (i.channel.name, i.msg)) hv
    have : i.msg ∈ chanOf MemPull.name (verifierSends prog) :=
      List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hsend, by simp [hn]⟩, rfl⟩
    rw [chanOf_verifier_eq_nil (by simp [MemPull, StatePull]) (by simp [MemPull, StatePush])] at this
    exact absurd this List.not_mem_nil
  obtain ⟨t, ht, hit⟩ := List.mem_flatMap.mp hi
  unfold Air.Flat.Table.interactions at hit
  obtain ⟨row, hrow, hir⟩ := List.mem_flatMap.mp hit
  rw [Component.interactionsValues_eq] at hir
  have hsend : (i.channel.name, i.msg) ∈ rowSends t.component (t.environment row) :=
    List.mem_map_of_mem (f := fun i : Interaction K ↦ (i.channel.name, i.msg)) hir
  have hchan : i.msg ∈ chanOf MemPull.name (tableSends t) := by
    rw [tableSends, chanOf_flatMap']
    exact List.mem_flatMap.mpr ⟨row, hrow, List.mem_map.mpr
      ⟨_, List.mem_filter.mpr ⟨hsend, by simp [hn]⟩, rfl⟩⟩
  · obtain ⟨j, rfl⟩ := mem_tables_iff.mp ht
    by_cases hj : (j : ℕ) < 6
    · -- A row of the six tables: a read it makes.
      have hp : (tableAt w j, row) ∈ opPairs w := by
        unfold opPairs
        refine List.mem_flatMap.mpr ⟨tableAt w j, ?_, List.mem_map_of_mem hrow⟩
        have hlen : w.tables.length = 8 := w.same_length.symm
        rw [List.mem_iff_getElem]
        exact ⟨j, by rw [List.length_take, hlen]; omega, by simp [tableAt]⟩
      have := (hf _ hp).2.2.1 i hir hn hm
      refine List.mem_map.mpr ?_
      obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp this
      exact ⟨y, List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, hp, hy⟩), hyeq⟩
    · obtain rfl | rfl : j = 6 ∨ j = 7 := by
        revert hj; fin_cases j <;> decide
      · -- The memory block: a finalize.
        rw [hmb, chanOf_memSeed_pull] at hchan
        obtain ⟨k, hk, hkeq⟩ := List.mem_map.mp hchan
        exact List.mem_map.mpr ⟨_, List.mem_append_right _ (List.mem_map_of_mem hk), hkeq⟩
      · -- The bytecode block pulls no memory.
        obtain ⟨bf, hbc⟩ := bcBlock_sends_eq h
        rw [hbc, chanOf_bcSeed_eq_nil _ (by simp [MemPull, BytecodePull])
          (by simp [MemPull, BytecodePush])] at hchan
        exact absurd hchan (List.not_mem_nil)

/-- **Soundness of the memory channel** (specification Lemma 6.3, Theorem 6.4, Corollary 6.5):
with nonzero counts and fewer than `2^64 - 1` reads, balance of the memory pair makes every memory
pull of multiplicity `1`, the one whose guarantee a soundness proof assumes, a correct read of
the image the data names. A gated pull of a `KECCAK` output cell its bytecode does not request has
multiplicity `0` and its push is its own tuple: the pair cancels, and nothing is claimed of it.
The read bound is derived from `Caps`. -/
theorem mem_channel_sound (h : SatisfiedByB prog input w) :
    ∀ i ∈ w.interactions, i.channel.name = MemPull.name → i.mult = 1 →
      ∀ m : MemMsg K, i.msg = (toElements m).toArray → MemPull.Guarantees m w.data := by
  intro i hi hname hmult m hm
  obtain ⟨f, hf⟩ := exists_opRecs w
  obtain ⟨mfin, hmb⟩ := memBlock_sends_eq h
  obtain ⟨bfin, hbc⟩ := bcBlock_sends_eq h
  have hall := allSends_eq_of h hf hmb hbc
  have hmsg := mem_pull_of_mult h hf hmb i hi hname hmult
  obtain ⟨x, hx, hxm⟩ := List.mem_map.mp hmsg
  obtain ⟨j, h1, h2⟩ := mem_reads_seeded h hf hall x hx
  rw [hm, toElements_memMsg] at hxm
  obtain rfl := memMsgOfTriple_injective hxm
  have hκ : (imageOf w.data).1 < 64 := lt_of_le_of_lt h.caps.le_maxLogMem (by decide)
  show (imageOf w.data).2.read m.addr = some (E.ofLimbs m.v[0] m.v[1])
  rw [show m.addr = addressOfIndex j from h1, show m.v = limbsOf (imageOf w.data).2 j from h2,
    MemoryImage.read_gpow hκ]
  simp only [limbsOf]
  exact congrArg some (ofLimbs_limb _).symm

end LeanVM.Arithmetization
