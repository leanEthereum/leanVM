/-
  LeanVM.Arithmetization.Soundness.MemChannel

  Soundness of the memory channel: in a satisfying witness every pulled memory tuple is a correct
  read of the image the prover data names.
-/

module

public import LeanVM.Arithmetization.Soundness.Bus
public import LeanVM.Arithmetization.Soundness.Lookup

@[expose] public section

/-!
# Soundness of the memory channel

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `42fe4b26`. Specification
Lemma 6.3, Theorem 6.4 and Corollary 6.5 (`doc/leanvm/body/06-bus-interactions.tex`, §6.2 to
§6.3) for the memory pair, as `mem_channel_sound`: the guarantee of the memory pull
(`MemPull.Guarantees`, `Arithmetization.Channels`) for every memory pull of a witness of the
constraint statement `SatisfiedBy`. It serves `constraintSoundness`.

**The argument.** A memory message `(addr, count, v)` is read as the triple of its address, count
and limbs (`memMsgOf`, injective). The witness pulls the reads of the six tables and the memory
block's finalizes, and pushes the reads bumped by `g` and the block's seeds `(g^i, 1, m_i)`, one
per word of the image (`Soundness.Bus`); `SatisfiedBy.mem_balanced` makes the two lists
permutations of each other. The counts of the reads are nonzero (`CountsNonzero`), there are
fewer than `2^64 - 1` reads (`opReads_length_lt`, from `Caps`: at most nine reads per row, `2^32`
rows per table, six tables), and each finalize has a seed's key. So `lookup_sound` makes every
read's key, its address and limbs, a seed's: `(g^i, m_i)`, which is a correct read of word `i`
(`MemImage.read_gpow`, as `κ ≤ 32`).

## Wrong readings excluded

* The finalize counts are not checked by the verifier (§6.2 "Nothing checks the finalize counts")
  and are not used: a finalize pull is a correct read by its key alone.
* The guarantee is about the limbs, not the word: two limb triples naming the same word of `E`
  would be different keys, and the seed's limbs are the image's (`limbsOf`).
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics
open Air.Flat (Component EnsembleWitness)

variable {prog : Program} {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)}

/-! ## Memory messages as triples -/

/-- A memory message as its triple. -/
def memMsgOfTriple (x : K × K × Vector K 3) : Array K := memMsgOf x.1 x.2.1 x.2.2

/-- The triple of a memory message, `0` for a missing coordinate. -/
def tripleOfMemMsg (a : Array K) : K × K × Vector K 3 :=
  (a.getD 0 0, a.getD 1 0, #v[a.getD 2 0, a.getD 3 0, a.getD 4 0])

/-- A vector of three is its entries. -/
theorem vec3_eta (v : Vector K 3) : #v[v[0], v[1], v[2]] = v := by
  refine Vector.ext fun i hi ↦ ?_
  interval_cases i <;> rfl

/-- Reading a memory message back gives its triple. -/
theorem tripleOfMemMsg_memMsgOfTriple (x : K × K × Vector K 3) :
    tripleOfMemMsg (memMsgOfTriple x) = x := by
  obtain ⟨a, c, v⟩ := x
  simp only [tripleOfMemMsg, memMsgOfTriple, memMsgOf]
  simp [vec3_eta]

/-- Memory messages are injective in their triple. -/
theorem memMsgOfTriple_injective : Function.Injective memMsgOfTriple := fun x y h ↦ by
  rw [← tripleOfMemMsg_memMsgOfTriple x, h, tripleOfMemMsg_memMsgOfTriple]

/-- A typed memory message flattens to the message of its triple. -/
theorem toElements_memMsg (m : MemMsg K) :
    (toElements m).toArray = memMsgOfTriple (m.addr, m.count, m.v) :=
  memMsg_toArray m

/-! ## The memory pair -/

/-- The memory reads of the six tables. -/
def opReads (w : EnsembleWitness (leanIsaEnsemble prog)) (f : Air.Flat.Table K × Array K → RowRec) :
    List (K × K × Vector K 3) :=
  (opPairs w).flatMap fun p ↦ (f p).reads

/-- A read pushed back: its count multiplied by `g`. -/
def bumpRead (x : K × K × Vector K 3) : K × K × Vector K 3 := (x.1, g * x.2.1, x.2.2)

/-- The memory messages a row of the six tables pulls. -/
theorem chanOf_rowRec_memPull (x : RowRec) :
    chanOf MemPull.name x.sends = x.reads.map memMsgOfTriple :=
  sendsOf_memPull _ _ _ _ _ _

/-- The memory messages a row of the six tables pushes. -/
theorem chanOf_rowRec_memPush (x : RowRec) :
    chanOf MemPush.name x.sends = (x.reads.map bumpRead).map memMsgOfTriple := by
  rw [List.map_map]
  exact sendsOf_memPush _ _ _ _ _ _

/-- **The memory pair of a satisfying witness, as triples**: the bumped reads and the seeds are a
permutation of the reads and the finalizes. -/
theorem mem_triples_perm (h : SatisfiedBy prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    {mfin : Fin (2 ^ (imageOf w.data).1) → K} {bfin : Fin (2 ^ prog.logSize) → K}
    (hall : allSends w = verifierSends prog ++ (opPairs w).flatMap (fun p ↦ (f p).sends) ++
      memSeedSends (imageOf w.data).2 mfin ++ bcSeedSends prog bfin) :
    ((opReads w f).map bumpRead ++ (List.finRange (2 ^ (imageOf w.data).1)).map fun i : Fin _ ↦
        (gpow i, 1, limbsOf (imageOf w.data).2 i)).Perm
      (opReads w f ++ (List.finRange (2 ^ (imageOf w.data).1)).map fun i : Fin _ ↦
        (gpow i, mfin i, limbsOf (imageOf w.data).2 i)) := by
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
  simp only [chanOf_rowRec_memPull, chanOf_rowRec_memPush, List.nil_append, List.append_nil]
    at hb
  have := hb.map tripleOfMemMsg
  simp only [List.map_append, List.map_map] at this
  convert this using 2
  · rw [opReads, List.map_flatMap, List.map_flatMap]
    refine List.flatMap_congr fun p _ ↦ ?_
    rw [List.map_map]
    exact List.map_congr_left fun x _ ↦ by simp [tripleOfMemMsg_memMsgOfTriple]
  · exact List.map_congr_left fun i _ ↦ (tripleOfMemMsg_memMsgOfTriple _).symm
  · rw [opReads, List.map_flatMap]
    refine List.flatMap_congr fun p _ ↦ ?_
    rw [List.map_map]
    exact (List.map_congr_left fun x _ ↦ tripleOfMemMsg_memMsgOfTriple x).trans (List.map_id _)
      |>.symm
  · exact List.map_congr_left fun i _ ↦ (tripleOfMemMsg_memMsgOfTriple _).symm

/-- Every memory message a satisfying witness pulls has a seed's address and limbs. -/
theorem mem_pulls_seeded (h : SatisfiedBy prog input w) :
    ∀ msg ∈ messagesOn w MemPull.toRaw, ∃ x : K × K × Vector K 3, msg = memMsgOfTriple x ∧
      ∃ i : Fin (2 ^ (imageOf w.data).1), x.1 = gpow i ∧ x.2.2 = limbsOf (imageOf w.data).2 i := by
  obtain ⟨f, hf⟩ := exists_opRecs w
  obtain ⟨mfin, bfin, hall⟩ := allSends_eq h hf
  have hperm := mem_triples_perm h hall
  let key : K × K × Vector K 3 → K × Vector K 3 := fun x ↦ (x.1, x.2.2)
  have hseeded := lookup_sound key (·.2.1) bumpRead (opReads w f) _ _ (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) hperm
    (fun x hx ↦ by
      obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
      exact (opRecs_counts_nonzero h hf hp).1 x hx)
    (opReads_length_lt h hf)
    (fun x hx ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map.mpr ⟨_, List.mem_map_of_mem (List.mem_finRange i), rfl⟩)
  have hkey : ∀ x ∈ opReads w f ++ (List.finRange (2 ^ (imageOf w.data).1)).map fun i : Fin _ ↦
      (gpow i, mfin i, limbsOf (imageOf w.data).2 i),
      ∃ i : Fin (2 ^ (imageOf w.data).1), x.1 = gpow i ∧ x.2.2 = limbsOf (imageOf w.data).2 i := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, hyx⟩ := List.mem_map.mp (hseeded x hx)
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
      exact ⟨i, (congrArg Prod.fst hyx).symm, (congrArg Prod.snd hyx).symm⟩
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨i, rfl, rfl⟩
  intro msg hmsg
  have hpull : messagesOn w MemPull.toRaw =
      (opReads w f ++ (List.finRange (2 ^ (imageOf w.data).1)).map fun i : Fin _ ↦
        (gpow i, mfin i, limbsOf (imageOf w.data).2 i)).map memMsgOfTriple := by
    rw [messagesOn_eq_chanOf, chanOf_allSends _ hall]
    simp only [Channel.toRaw_name]
    rw [chanOf_verifier_eq_nil (by simp [MemPull, StatePull]) (by simp [MemPull, StatePush]),
      chanOf_bcSeed_eq_nil _ (by simp [MemPull, BytecodePull]) (by simp [MemPull, BytecodePush]),
      chanOf_memSeed_pull]
    simp only [chanOf_rowRec_memPull, List.nil_append, List.append_nil, List.map_append,
      opReads, List.map_flatMap, List.map_map]
    rfl
  rw [hpull] at hmsg
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmsg
  exact ⟨x, rfl, hkey x hx⟩

/-- **Soundness of the memory channel** (specification Lemma 6.3, Theorem 6.4, Corollary 6.5):
with nonzero counts and fewer than `2^64 - 1` reads, balance of the memory pair makes every pulled
memory tuple a correct read of the image the data names. The read bound is derived from `Caps`. -/
theorem mem_channel_sound (h : SatisfiedBy prog input w) :
    ∀ i ∈ w.interactions, i.channel.name = MemPull.name →
      ∀ m : MemMsg K, i.msg = (toElements m).toArray → MemPull.Guarantees m w.data := by
  intro i hi hname m hm
  obtain ⟨x, hx, j, h1, h2⟩ := mem_pulls_seeded h i.msg (mem_messagesOn hi hname)
  rw [hm, toElements_memMsg] at hx
  obtain rfl := memMsgOfTriple_injective hx
  have hκ : (imageOf w.data).1 < 64 := lt_of_le_of_lt h.caps.le_maxLogMem (by decide)
  show (imageOf w.data).2.read m.addr = some (E.ofLimbs m.v[0] m.v[1] m.v[2])
  rw [show m.addr = gpow j from h1, show m.v = limbsOf (imageOf w.data).2 j from h2,
    MemImage.read_gpow hκ]
  simp only [limbsOf]
  exact congrArg some (ofLimbs_limb _).symm

end LeanVM.Arithmetization
