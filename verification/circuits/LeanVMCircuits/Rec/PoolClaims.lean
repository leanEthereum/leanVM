module

public import LeanVMCircuits.Rec.UnionCover

@[expose] public section

/-!
A pool's claims are the claims of the sets its digests name (`rec::tree::multiset`).

A claim set is written as blocks (`ClaimSet.blocks`): per group a header holding its label, then its members two to a
block, then an end; its digest is the chain of their compressions from the parameter IV, the counter word of each
block its kind bits and the start bit on the first (`ClaimSet.digest`, with `blakeF` the BLAKE2s compression a
`block` call's row computes). `ChainCR` says no pool row's compression collides with one of the chain's.

- `run_reads`: a run of a pool whose expected digest is a chain's last output reads the chain's blocks, item for
  item, unless a row collides with the chain.
- `reads_sum`: if every run's expected digest is the digest of a set, the pool's items read, slot for slot, the sum
  of those sets' claims (`readC_blocks`: a set's blocks read its claims).
- `Bind.pool_claims`: on a pool's rows, the claims on are at most the sum of the sets its runs name, and exactly that
  sum when the pool does not select. `Bind.decl_claims`: a pool of one digest that does not select has the claims on
  of the set it names. `Bind.sel_claims`: a pool whose run one-hot ends at its last digest (`PoolCert.endOk`) has
  claims on among the sum of the sets its digests name.
- `Bind.union_sound_sets`: `Bind.union_sound` with the multisets read as the sets the digests name: if the declared
  set's claims are not among the children's, the coverage test holds at a matching point for at most a `4N/|S|`
  fraction of the outcomes.
-/

namespace LeanVMCircuits.Rec.PoolClaims

open LeanVMCircuits.Rec PoolParse UnionSound

/-! Chains of blocks. -/

/-- A block of a written form: its kind bits (`MEMBER`, `END`, `PAIR`) and its eight words. -/
structure Block where
  b0 : Bool
  b1 : Bool
  p : Bool
  w : ℕ → K

noncomputable instance : Inhabited Block := ⟨⟨false, false, false, fun _ => 0⟩⟩

/-- Block `j`'s row inputs from the chaining value `h`: the counter limb (start and kind bits), the finalization limb
(unread here: the compression's flag), the chaining value's four limbs, the block's eight words. -/
noncomputable def rowIn (j : ℕ) (b : Block) (h : ℕ → K) (c : ℕ) : K :=
  if c = 0 then code (decide (j = 0)) (bitK b.b0) (bitK b.b1) (bitK b.p)
  else if c = 1 then 0 else if c < 6 then h (c - 2) else b.w (c - 6)

/-- The chain of a compression `F` (row inputs and finalization flag to four output limbs) over blocks from `iv`:
the output after block `j`. -/
noncomputable def chainOut (F : (ℕ → K) → Bool → ℕ → K) (iv : ℕ → K) (bs : List Block) : ℕ → ℕ → K
  | 0 => F (rowIn 0 (bs.getD 0 default) iv) (decide (bs.length = 1))
  | j + 1 => F (rowIn (j + 1) (bs.getD (j + 1) default) (chainOut F iv bs j)) (decide (j + 2 = bs.length))

/-- Block `j`'s row inputs in the chain. -/
noncomputable def chainIn (F : (ℕ → K) → Bool → ℕ → K) (iv : ℕ → K) (bs : List Block) (j : ℕ) : ℕ → K :=
  rowIn j (bs.getD j default) (if j = 0 then iv else chainOut F iv bs (j - 1))

/-- Row inputs `cin` and outputs `cout` chaining the blocks `bs`. -/
structure Chain (bs : List Block) (cin cout : ℕ → ℕ → K) : Prop where
  counter : ∀ j < bs.length, cin j 0 =
    code (decide (j = 0)) (bitK (bs.getD j default).b0) (bitK (bs.getD j default).b1) (bitK (bs.getD j default).p)
  chain : ∀ j < bs.length, 0 < j → ∀ k < 4, cin j (2 + k) = cout (j - 1) k
  words : ∀ j < bs.length, ∀ c < 8, cin j (6 + c) = (bs.getD j default).w c

theorem chain_of (F : (ℕ → K) → Bool → ℕ → K) (iv : ℕ → K) (bs : List Block) :
    Chain bs (chainIn F iv bs) (chainOut F iv bs) where
  counter j _ := by simp [chainIn, rowIn]
  chain j _ hj k hk := by
    simp [chainIn, rowIn, show j ≠ 0 by omega, show 2 + k ≠ 1 by omega,
      show 2 + k < 6 by omega]
  words j _ c _ := by simp [chainIn, rowIn, show 6 + c ≠ 1 by omega]

/-- No row of a pool's `n` items collides with one of the chain's `L` compressions: a row whose output is the chain's
output after block `j` has block `j`'s inputs (but the finalization limb, which the compression's flag stands for). -/
def ChainCR (n : ℕ) (v : Vals) (L : ℕ) (cin cout : ℕ → ℕ → K) : Prop :=
  ∀ i < n, ∀ j < L, (∀ k < 4, v.outs i k = cout j k) → ∀ c < 14, c ≠ 1 → v.ins i c = cin j c

section Run

variable {n : ℕ} {σ : ℕ → Bool} {X : ℕ → E × E} {v : Vals}

theorem bitK_isBit (b : Bool) : IsBit (bitK b) := by cases b <;> simp [bitK, IsBit]

/-- An item with a block's inputs has its kind bits and starts a run exactly when the block is the first. -/
theorem kinds_of_counter (hS : Sem n σ X v) {i : ℕ} (hi : i < n) {j : ℕ} {b : Block}
    (h : v.ins i 0 = code (decide (j = 0)) (bitK b.b0) (bitK b.b1) (bitK b.p)) :
    σ i = decide (j = 0) ∧ v.b0 i = bitK b.b0 ∧ v.b1 i = bitK b.b1 ∧ v.p i = bitK b.p := by
  rw [hS.counter i hi] at h
  obtain ⟨b0, b1, bp⟩ := hS.bits i hi
  exact code_inj b0 b1 bp (bitK_isBit _) (bitK_isBit _) (bitK_isBit _) h

theorem seg_ge {σ : ℕ → Bool} {a : ℕ} (hσa : σ a = true) : ∀ i, a ≤ i → a ≤ seg σ i := by
  intro i
  induction i with
  | zero => intro h; simp [seg]; omega
  | succ i ih =>
    intro h
    rcases Nat.lt_or_ge a (i + 1) with hl | hl
    · unfold seg; split
      · exact h
      · exact ih (by omega)
    · obtain rfl : a = i + 1 := le_antisymm h hl
      rw [seg_true hσa]

theorem seg_sigma {σ : ℕ → Bool} (hσ0 : σ 0 = true) : ∀ i, σ (seg σ i) = true
  | 0 => hσ0
  | i + 1 => by
    unfold seg
    split
    · assumption
    · exact seg_sigma hσ0 i

/-- A run whose expected digest is the last output of a chain of blocks reads them item for item, unless a row
collides with the chain: the run's items `a + j` have block `j`'s inputs (but the finalization limb), and none after
its first starts a run. -/
theorem run_reads (hS : Sem n σ X v) (hσ0 : σ 0 = true) (steady : ∀ i < n, 0 < i → σ i = false → X i = X (i - 1))
    {bs : List Block} {cin cout : ℕ → ℕ → K} (hC : Chain bs cin cout) (hne : bs ≠ [])
    (hcr : ChainCR n v bs.length cin cout) {a : ℕ} (ha : a < n) (hσa : σ a = true)
    (hX : X a = halves (cout (bs.length - 1))) :
    a + bs.length ≤ n ∧ ∀ j < bs.length, (∀ i, a < i → i ≤ a + j → σ i = false) ∧
      ∀ c < 14, c ≠ 1 → v.ins (a + j) c = cin j c := by
  set L := bs.length with hL
  have hL0 : 0 < L := List.length_pos_of_ne_nil hne
  obtain ⟨e, he, hseg, h1, hp, hae⟩ := end_exists hS hσ0 a ha
  rw [seg_true hσa] at hseg
  have hae : a ≤ e := hae.resolve_right fun h => by rw [hS.startPad a ha hσa] at h; exact zero_ne_one h
  have hout : ∀ k < 4, v.outs e k = cout (L - 1) k := by
    apply halves_inj
    rw [hS.ends e he (end_one h1 hp), X_seg steady e he, hseg, hX]
  -- Back from the end, block by block.
  have back : ∀ t, t ≤ L - 1 → t ≤ e ∧ a ≤ e - t ∧ seg σ (e - t) = a ∧ (∀ c < 14, c ≠ 1 → v.ins (e - t) c = cin (L - 1 - t) c) ∧
      ∀ i, e - t < i → i ≤ e → σ i = false := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨Nat.zero_le _, by simpa using hae, by simpa using hseg, by simpa using hcr e he (L - 1) (by omega) hout,
        fun i h1 h2 => by omega⟩
    | succ t ih =>
      intro ht
      obtain ⟨-, hat, hst, hin, hσs⟩ := ih (by omega)
      have hj : L - 1 - t < L := by omega
      obtain ⟨hσ, -⟩ := kinds_of_counter hS (by omega) ((hin 0 (by norm_num) (by norm_num)).trans (hC.counter _ hj))
      have hσf : σ (e - t) = false := by rw [hσ]; simp; omega
      have hpos : a < e - t := by
        rcases Nat.lt_or_ge a (e - t) with h | h
        · exact h
        · obtain rfl : a = e - t := le_antisymm hat h
          rw [hσa] at hσf; exact absurd hσf (by decide)
      have hk : ∀ k < 4, v.outs (e - (t + 1)) k = cout (L - 1 - (t + 1)) k := by
        intro k hk
        have h2 := hin (2 + k) (by omega) (by omega)
        rw [hS.chain (e - t) (by omega) (by omega) hσf k hk, hC.chain _ hj (by omega) k hk] at h2
        rw [show e - (t + 1) = e - t - 1 by omega, show L - 1 - (t + 1) = L - 1 - t - 1 by omega]
        exact h2
      have hseg' : seg σ (e - (t + 1)) = a := by
        have : e - t = (e - (t + 1)) + 1 := by omega
        rw [this] at hσf hst
        rwa [seg_false hσf] at hst
      refine ⟨by omega, by have := seg_le σ (e - (t + 1)); omega, hseg', hcr _ (by omega) _ (by omega) hk, fun i h1 h2 => ?_⟩
      rcases Nat.lt_or_ge (e - t) i with h | h
      · exact hσs i h h2
      · obtain rfl : i = e - t := le_antisymm h (by omega)
        exact hσf
  obtain ⟨hLe, hat, hst, hin, hσs⟩ := back (L - 1) le_rfl
  obtain ⟨hσ, -⟩ := kinds_of_counter hS (by omega) ((hin 0 (by norm_num) (by norm_num)).trans
    (hC.counter _ (by omega)))
  have hσt : σ (e - (L - 1)) = true := by rw [hσ]; simp
  rw [seg_true hσt] at hst
  have hea : e = a + (L - 1) := by omega
  refine ⟨by omega, fun j hj => ⟨fun i h1 h2 => hσs i (by omega) (by omega), fun c hc hc1 => ?_⟩⟩
  obtain ⟨-, -, -, hin', -⟩ := back (L - 1 - j) (by omega)
  have := hin' c hc hc1
  rwa [show e - (L - 1 - j) = a + j by omega, show L - 1 - (L - 1 - j) = j by omega] at this

/-- An item of a run after it has read its blocks, through the pool's next start, is padding. -/
theorem pad_after (hS : Sem n σ X v) {a L : ℕ} (hL : 0 < L) (hlast : v.b1 (a + L - 1) = 1) :
    ∀ d i, i = a + L + d → i < n → seg σ i = a → v.pad i = 1 := by
  intro d
  induction d with
  | zero =>
    intro i hi hin hseg
    have hσ : σ i = false := by
      cases h : σ i with
      | false => rfl
      | true => rw [seg_true h] at hseg; omega
    rw [hS.padAfter i hin (by omega) hσ, show i - 1 = a + L - 1 by omega, hlast]
  | succ d ih =>
    intro i hi hin hseg
    have hσ : σ i = false := by
      cases h : σ i with
      | false => rfl
      | true => rw [seg_true h] at hseg; omega
    have hseg' : seg σ (i - 1) = a := by
      have : i = (i - 1) + 1 := by omega
      rw [this] at hσ hseg
      rwa [seg_false hσ] at hseg
    have hp := ih (i - 1) (by omega) (by omega) hseg'
    rw [hS.padAfter i hin (by omega) hσ]
    exact (pad_one (hS.bits _ (by omega)).1 (hS.bits _ (by omega)).2.1 hp).2

end Run

/-! Claim sets, their written form, and what blocks read. -/

/-- A group of claims: a label and its members, each word a `K` value (`ofWord` of the Rust word). -/
structure Group where
  label : Fin 6 → K
  members : List (Fin 4 → K)

/-- A claim set: its groups, in the order they are written. -/
abbrev ClaimSet := List Group

/-- `multiset::code::TAG`, `u64::from_le_bytes(*b"claimset")`: the end block's first word. -/
def tag : ℕ := 0x7465736d69616c63

/-- Four words, then zeros. -/
noncomputable def w4 (a : Fin 4 → K) (j : ℕ) : K := if h : j < 4 then a ⟨j, h⟩ else 0

/-- Members two to a block, the second zeros if none. -/
noncomputable def memberBlocks : List (Fin 4 → K) → List Block
  | [] => []
  | [a] => [⟨true, false, false, w4 a⟩]
  | a :: b :: r => ⟨true, false, true, fun j => if j < 4 then w4 a j else w4 b (j - 4)⟩ :: memberBlocks r

/-- A group's header's words: its label, then zeros. -/
noncomputable def Group.hdrW (g : Group) (j : ℕ) : K := if h : j < 6 then g.label ⟨j, h⟩ else 0

/-- A group's blocks: its header, then its members. -/
noncomputable def Group.blocks (g : Group) : List Block := ⟨false, false, false, g.hdrW⟩ :: memberBlocks g.members

/-- The end block. -/
noncomputable def endBlock : Block := ⟨false, true, false, fun j => if j = 0 then ofWord tag else 0⟩

/-- A set's written form (`ClaimSet::items`). -/
noncomputable def ClaimSet.blocks (C : ClaimSet) : List Block := C.flatMap Group.blocks ++ [endBlock]

/-- A claim's tuple: `(1, label[0..6], member[0..4])`, zeros after. -/
noncomputable def claimTup (l : Fin 6 → K) (m : Fin 4 → K) : Tuple := fun t =>
  if (t : ℕ) = 0 then 1 else if h : (t : ℕ) < 7 then emb (l ⟨t - 1, by omega⟩)
  else if h' : (t : ℕ) < 11 then emb (m ⟨t - 7, by omega⟩) else 0

/-- A set's claims, as tuples. -/
noncomputable def ClaimSet.tuples (C : ClaimSet) : Multiset Tuple :=
  ((C.flatMap fun g => g.members.map (claimTup g.label) : List Tuple) : Multiset Tuple)

/-- A header's label tuple `(1, w[0..6])`. -/
noncomputable def hdrTup (w : ℕ → K) (k : ℕ) : E := if k = 0 then 1 else if k < 7 then emb (w (k - 1)) else 0

/-- Slot `sl`'s tuple: the label tuple `ℓ`, then the slot's four words. -/
noncomputable def slotTup (ℓ : ℕ → E) (w : ℕ → K) (sl : ℕ) : Tuple := fun t =>
  if (t : ℕ) < 7 then ℓ t else if (t : ℕ) < 11 then emb (w (4 * sl + (t - 7))) else 0

/-- A header: neither kind bit. -/
def Block.isHdr (b : Block) : Bool := !b.b0 && !b.b1

/-- A block of members. -/
def Block.isMem (b : Block) : Bool := b.b0 && !b.b1

/-- The label tuple after a block, `ℓ` before it. -/
noncomputable def Block.lab (b : Block) (ℓ : ℕ → E) : ℕ → E := if b.isHdr then hdrTup b.w else ℓ

/-- The claims a block reads, `ℓ` the label tuple before it: a block of members reads its first slot, and its second
when it is a pair. -/
noncomputable def Block.reads (b : Block) (ℓ : ℕ → E) : Multiset Tuple :=
  if b.isMem then {slotTup (b.lab ℓ) b.w 0} + (if b.p then {slotTup (b.lab ℓ) b.w 1} else 0) else 0

/-- The label tuple after blocks. -/
noncomputable def readL : (ℕ → E) → List Block → ℕ → E
  | ℓ, [] => ℓ
  | ℓ, b :: bs => readL (b.lab ℓ) bs

/-- The claims blocks read. -/
noncomputable def readC : (ℕ → E) → List Block → Multiset Tuple
  | _, [] => 0
  | ℓ, b :: bs => b.reads ℓ + readC (b.lab ℓ) bs

theorem readC_append (ℓ : ℕ → E) (bs bs' : List Block) :
    readC ℓ (bs ++ bs') = readC ℓ bs + readC (readL ℓ bs) bs' := by
  induction bs generalizing ℓ with
  | nil => simp [readC, readL]
  | cons b bs ih => simp [readC, readL, ih, add_assoc]

theorem readL_append (ℓ : ℕ → E) (bs bs' : List Block) : readL ℓ (bs ++ bs') = readL (readL ℓ bs) bs' := by
  induction bs generalizing ℓ with
  | nil => rfl
  | cons b bs ih => simp [readL, ih]

theorem slot_single (l : Fin 6 → K) (lw : ℕ → K) (hl : ∀ j (h : j < 6), lw j = l ⟨j, h⟩) (a : Fin 4 → K) :
    slotTup (hdrTup lw) (w4 a) 0 = claimTup l a := by
  funext t
  fin_cases t <;> simp [slotTup, hdrTup, claimTup, w4, hl]

theorem slot_pair (l : Fin 6 → K) (lw : ℕ → K) (hl : ∀ j (h : j < 6), lw j = l ⟨j, h⟩) (a b : Fin 4 → K) :
    slotTup (hdrTup lw) (fun j => if j < 4 then w4 a j else w4 b (j - 4)) 0 = claimTup l a ∧
      slotTup (hdrTup lw) (fun j => if j < 4 then w4 a j else w4 b (j - 4)) 1 = claimTup l b := by
  constructor <;> funext t <;> fin_cases t <;> simp [slotTup, hdrTup, claimTup, w4, hl]

theorem readC_members (l : Fin 6 → K) (lw : ℕ → K) (hl : ∀ j (h : j < 6), lw j = l ⟨j, h⟩) :
    ∀ ms : List (Fin 4 → K), readC (hdrTup lw) (memberBlocks ms) = ((ms.map (claimTup l) : List Tuple) : Multiset Tuple) ∧
      readL (hdrTup lw) (memberBlocks ms) = hdrTup lw
  | [] => by simp [memberBlocks, readC, readL]
  | [a] => by
    simp [memberBlocks, readC, readL, Block.reads, Block.isMem, Block.lab, Block.isHdr, slot_single l lw hl]
  | a :: b :: r => by
    obtain ⟨ih1, ih2⟩ := readC_members l lw hl r
    obtain ⟨p0, p1⟩ := slot_pair l lw hl a b
    simp only [memberBlocks, readC, readL, Block.reads, Block.isMem, Block.lab, Block.isHdr, Bool.not_true,
      Bool.false_and, Bool.false_eq_true, if_false, Bool.not_false, Bool.and_self, if_true, ih1, ih2, p0, p1,
      List.map_cons]
    simp [← Multiset.cons_coe]

/-- A set's blocks read its claims. -/
theorem readC_blocks (C : ClaimSet) (ℓ : ℕ → E) : readC ℓ C.blocks = C.tuples := by
  induction C generalizing ℓ with
  | nil => simp [ClaimSet.blocks, ClaimSet.tuples, endBlock, readC, Block.reads, Block.isMem]
  | cons g C ih =>
    have hl : ∀ j (h : j < 6), g.hdrW j = g.label ⟨j, h⟩ := fun j h => by simp [Group.hdrW, h]
    obtain ⟨h1, h2⟩ := readC_members g.label g.hdrW hl g.members
    have := ih (hdrTup g.hdrW)
    simp only [ClaimSet.blocks, List.flatMap_cons, List.append_assoc] at this ⊢
    rw [readC_append, Group.blocks, readC, readL]
    simp only [Block.reads, Block.isMem, Block.lab, Block.isHdr, Bool.false_and, Bool.false_eq_true, if_false,
      Bool.not_false, Bool.and_self, if_true, zero_add]
    rw [h2, this, h1]
    simp [ClaimSet.tuples]

theorem blocks_ne (C : ClaimSet) : C.blocks ≠ [] := by simp [ClaimSet.blocks]

theorem blocks_last (C : ClaimSet) : (C.blocks.getD (C.blocks.length - 1) default).b1 = true := by
  simp [ClaimSet.blocks, List.getD_eq_getElem?_getD, endBlock]

/-! A pool's items, read run by run. -/

theorem take_sat {α : Type} {l : List α} {k k' : ℕ} (h : l.length ≤ k) (h' : l.length ≤ k') : l.take k = l.take k' := by
  rw [List.take_of_length_le h, List.take_of_length_le h']

/-- A pool's items read the blocks of its runs: if each run (from its start `a`, `σ a`) reads the blocks `bs a`, item
for item, from the zero label, and the items after it through the next start read nothing and keep the label, then
the pool's items read the sum of what the runs' blocks read. -/
theorem reads_sum {n : ℕ} {σ : ℕ → Bool} (hσ0 : σ 0 = true) (bs : ℕ → List Block) (lab : ℕ → ℕ → E)
    (rd : ℕ → Multiset Tuple)
    (hfit : ∀ a < n, σ a = true → a + (bs a).length ≤ n ∧ ∀ i, a < i → i < a + (bs a).length → σ i = false)
    (hstep : ∀ i < n, if i - seg σ i < (bs (seg σ i)).length then
        rd i = ((bs (seg σ i)).getD (i - seg σ i) default).reads (if σ i then fun _ => 0 else lab (i - 1)) ∧
        lab i = ((bs (seg σ i)).getD (i - seg σ i) default).lab (if σ i then fun _ => 0 else lab (i - 1))
      else rd i = 0 ∧ lab i = if σ i then fun _ => 0 else lab (i - 1)) :
    ∑ i ∈ Finset.range n, rd i = ∑ a ∈ (Finset.range n).filter (σ · = true), readC (fun _ => 0) (bs a) := by
  classical
  -- Run by run, up to item `k`.
  have inv : ∀ k ≤ n, ∑ i ∈ Finset.range k, rd i =
      ∑ a ∈ (Finset.range k).filter (σ · = true), readC (fun _ => 0) ((bs a).take (k - a)) ∧
      (0 < k → lab (k - 1) = readL (fun _ => 0) ((bs (seg σ (k - 1))).take (k - seg σ (k - 1)))) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨ihs, ihl⟩ := ih (by omega)
      have hst := hstep k (by omega)
      -- Every run started before `k` but `k`'s own has read all its blocks by `k`.
      have hdone : ∀ a < k, σ a = true → a ≠ seg σ k → (bs a).length ≤ k - a := by
        intro a ha hσa hne
        have h1 : a ≤ seg σ k := seg_ge hσa k ha.le
        have h2 : a < seg σ k := lt_of_le_of_ne h1 hne
        have hs := seg_sigma hσ0 k
        have hlt : ¬ (seg σ k < a + (bs a).length) := fun h => by
          have := (hfit a (by omega) hσa).2 (seg σ k) h2 h
          rw [hs] at this
          exact absurd this (by decide)
        have := seg_le σ k
        omega
      cases hσ : σ k with
      | true =>
        have hsk : seg σ k = k := seg_true hσ
        rw [hsk] at hst
        simp only [Nat.sub_self, hσ, if_true] at hst
        have hf : (Finset.range (k + 1)).filter (σ · = true) = insert k ((Finset.range k).filter (σ · = true)) := by
          rw [Finset.range_add_one, Finset.filter_insert, if_pos hσ]
        have hnot : k ∉ (Finset.range k).filter (σ · = true) := by simp
        rw [Finset.sum_range_succ, ihs, hf, Finset.sum_insert hnot]
        refine ⟨?_, fun _ => ?_⟩
        · have e2 : ∑ a ∈ (Finset.range k).filter (σ · = true), readC (fun _ => 0) ((bs a).take (k - a)) =
              ∑ a ∈ (Finset.range k).filter (σ · = true), readC (fun _ => 0) ((bs a).take (k + 1 - a)) := by
            refine Finset.sum_congr rfl fun a ha => ?_
            rw [Finset.mem_filter, Finset.mem_range] at ha
            have := hdone a ha.1 ha.2 (by omega)
            rw [take_sat (by omega : (bs a).length ≤ k - a) (by omega : (bs a).length ≤ k + 1 - a)]
          have e1 : rd k = readC (fun _ => 0) ((bs k).take (k + 1 - k)) := by
            rw [show k + 1 - k = 1 by omega]
            split at hst
            · obtain ⟨hr, -⟩ := hst
              obtain ⟨b, l, hb⟩ := List.exists_cons_of_length_pos ‹0 < (bs k).length›
              rw [hr, hb]
              simp [readC]
            · rw [hst.1, List.eq_nil_of_length_eq_zero (by omega : (bs k).length = 0)]
              simp [readC]
          rw [e1, e2, add_comm]
        · simp only [Nat.add_sub_cancel, hsk, show k + 1 - k = 1 by omega]
          split at hst
          · obtain ⟨-, hl⟩ := hst
            obtain ⟨b, l, hb⟩ := List.exists_cons_of_length_pos ‹0 < (bs k).length›
            rw [hl, hb]
            simp [readL]
          · rw [hst.2, List.eq_nil_of_length_eq_zero (by omega : (bs k).length = 0)]
            simp [readL]
      | false =>
        have hk0 : 0 < k := by
          rcases Nat.eq_zero_or_pos k with rfl | h
          · rw [hσ0] at hσ; exact absurd hσ (by decide)
          · exact h
        have hsk : seg σ k = seg σ (k - 1) := by
          have : k = (k - 1) + 1 := by omega
          conv_lhs => rw [this]
          rw [seg_false (by rw [← this]; exact hσ)]
        set s := seg σ k with hs
        have hlab := ihl hk0
        rw [← hsk] at hlab
        simp only [hσ, Bool.false_eq_true, if_false] at hst
        have hf : (Finset.range (k + 1)).filter (σ · = true) = (Finset.range k).filter (σ · = true) := by
          rw [Finset.range_add_one, Finset.filter_insert, if_neg (by simp [hσ])]
        have hsmem : s ∈ (Finset.range k).filter (σ · = true) := by
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨by have := seg_le σ (k - 1); omega, seg_sigma hσ0 k⟩
        rw [Finset.sum_range_succ, ihs, hf]
        -- The sum moves on at `s`'s term only.
        have hpt : ∀ a ∈ (Finset.range k).filter (σ · = true),
            readC (fun _ => 0) ((bs a).take (k + 1 - a)) =
              readC (fun _ => 0) ((bs a).take (k - a)) + if a = s then rd k else 0 := by
          intro a ha
          rw [Finset.mem_filter, Finset.mem_range] at ha
          by_cases has : a = s
          · rw [has, if_pos rfl]
            split at hst
            · obtain ⟨hr, -⟩ := hst
              rw [show k + 1 - s = (k - s) + 1 by have := seg_le σ k; omega, List.take_add_one,
                List.getElem?_eq_getElem ‹_›, Option.toList_some, readC_append, hr, hlab]
              simp [readC, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ‹_›]
            · rw [hst.1, add_zero, take_sat (k := k + 1 - s) (k' := k - s) (by omega) (by omega)]
          · rw [if_neg has, add_zero, take_sat (by have := hdone a ha.1 ha.2 has; omega)
              (hdone a ha.1 ha.2 has)]
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq' _ _ (fun _ => rd k), if_pos hsmem]
        refine ⟨rfl, fun _ => ?_⟩
        simp only [Nat.add_sub_cancel, ← hs]
        split at hst
        · obtain ⟨-, hl⟩ := hst
          rw [show k + 1 - s = (k - s) + 1 by have := seg_le σ k; omega, List.take_add_one,
            List.getElem?_eq_getElem ‹_›, Option.toList_some, readL_append, hl, hlab]
          simp [readL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ‹_›]
        · rw [hst.2, hlab, take_sat (k := k - s) (k' := k + 1 - s) (by omega) (by omega)]
  rw [(inv n le_rfl).1]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_filter, Finset.mem_range] at ha
  rw [List.take_of_length_le (by have := (hfit a ha.1 ha.2).1; omega)]

/-! Digests. -/

/-- The parameter IV's four limbs. -/
noncomputable def iv (k : ℕ) : K := ofWord (Model.paramIVLimbs.getD k 0)

/-- A set's digest under a compression `F`: the chain of its blocks from the parameter IV, as four limbs. -/
noncomputable def ClaimSet.digest (F : (ℕ → K) → Bool → ℕ → K) (C : ClaimSet) : ℕ → K :=
  chainOut F iv C.blocks (C.blocks.length - 1)

/-- BLAKE2s's compression on row inputs, as a `block` call's row computes it (`Model.hashBlock_good`): RFC 7693's `F`
of the chaining value (limbs 2 to 5), the eight words (limbs 6 to 13) and the counter word (limb 0), for the
finalization flag, its output's four words as limbs. `ClaimSet.digest blakeF` is `ClaimSet::digest`. -/
noncomputable def blakeF (ins : ℕ → K) (f : Bool) (k : ℕ) : K :=
  if h : k < 4 then
    ofWord (digest (Blake2s.Rfc7693.F (cvWords fun j => BitVec.ofNat 64 (toWord (ins (2 + j))))
      (block ((List.range 8).map fun j => BitVec.ofNat 64 (toWord (ins (6 + j)))) 0)
      (BitVec.ofNat 64 (toWord (ins 0))) f) ⟨k, h⟩).toNat
  else 0

/-- A run names a set: its expected digest is the set's, and no row of the pool collides with the set's chain. -/
def Names (F : (ℕ → K) → Bool → ℕ → K) (n : ℕ) (v : Vals) (X : E × E) (C : ClaimSet) : Prop :=
  X = halves (ClaimSet.digest F C) ∧ ChainCR n v C.blocks.length (chainIn F iv C.blocks) (chainOut F iv C.blocks)

end LeanVMCircuits.Rec.PoolClaims

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model PoolClaims PoolParse UnionSound ProdCert

section Claims

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {pc : PoolCert} {st : ℕ → Fin 4 → K} {val : Val}

theorem emb_mem (a b : Bool) : emb (bitK a + bitK a * bitK b) = if (a && !b) = true then 1 else 0 := by
  cases a <;> cases b <;> simp [bitK, two_K', emb_one', emb_zero]

theorem emb_pair (a b p : Bool) :
    emb ((bitK a + bitK a * bitK b) * bitK p) = if (a && !b && p) = true then 1 else 0 := by
  cases a <;> cases b <;> cases p <;> simp [bitK, two_K', emb_one', emb_zero]

theorem emb_hdr (a b : Bool) : emb (bitK a + bitK b + bitK a * bitK b) = 0 ↔ (!a && !b) = true := by
  cases a <;> cases b <;> simp [bitK, two_K', emb_one', emb_zero]

theorem onClaims_two (a b : E) (t0 t1 : Tuple) :
    onClaims [(a, t0), (b, t1)] = (if a = 1 then {t0} else 0) + (if b = 1 then {t1} else 0) := by
  classical
  by_cases ha : a = 1 <;> by_cases hb : b = 1 <;>
    simp [onClaims, ha, hb, ← Multiset.cons_coe]

/-- Item `i`'s two slots with their bits. -/
noncomputable def itemOn (os : Array (List ℕ)) (pc : PoolCert) (val : Val) (i : ℕ) : List (E × Tuple) :=
  [(onBit os pc val i 0, fun t => slotT os pc val i 0 t), (onBit os pc val i 1, fun t => slotT os pc val i 1 t)]

/-- The claims item `i`'s valid slots hold, selected or not. -/
noncomputable def itemV (os : Array (List ℕ)) (pc : PoolCert) (val : Val) (i : ℕ) : Multiset Tuple :=
  onClaims [(Model.ev val (valid os pc i 0), fun t => slotT os pc val i 0 t),
    (Model.ev val (valid os pc i 1), fun t => slotT os pc val i 1 t)]

theorem onClaims_slotsN (os : Array (List ℕ)) (pc : PoolCert) (val : Val) : ∀ k,
    onClaims ((slotsN os pc val k).map fun p => (p.1, fun t => p.2 t)) =
      ∑ i ∈ Finset.range k, onClaims (itemOn os pc val i)
  | 0 => by simp [slotsN, onClaims]
  | k + 1 => by
    have ih := onClaims_slotsN os pc val k
    simp only [slotsN] at ih ⊢
    rw [List.range_succ, List.flatMap_append, List.map_append, onClaims_append, ih, Finset.sum_range_succ]
    simp [itemOn]

theorem Mv_ins (i j : ℕ) (hj : j < 8) : Mv os pc val i j = emb ((pc.vals os val).ins i (6 + j)) := by
  have hb := blockWords_getD (os := os) (pc.blk os i) j hj
  simp only [Mv, m, PoolCert.vals, show 6 + j ≠ 0 by omega, show 6 + j ≠ 1 by omega, show ¬ 6 + j < 6 by omega,
    if_false, Nat.add_sub_cancel_left, hb]

/-- A slot's bit is its validity times its selection bit, a bit when selecting. -/
theorem sel_bit (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) {i : ℕ} (hi : i < pc.n) (sl : ℕ) :
    (if pc.selecting then emb (val (selW os pc i sl) 0) else 1) = 0 ∨
      (if pc.selecting then emb (val (selW os pc i sl) 0) else 1) = 1 := by
  obtain ⟨-, -, -, -, -, -, hbitsOk⟩ := PoolCert.ok_parts hok
  simp only [PoolCert.bitsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at hbitsOk
  cases hsel : pc.selecting with
  | false => right; rfl
  | true =>
    simp only [if_true]
    obtain ⟨-, hsb⟩ := hbitsOk.1 i hi
    rcases hsb with h | ⟨h0, h1⟩
    · rw [hsel] at h; exact absurd h (by decide)
    · apply bit_cases
      unfold selW; split
      · exact PoolCert.packed_bit hF h0
      · exact PoolCert.packed_bit hF h1

/-- An item's slots on are among its valid slots, and are them when the pool does not select. -/
theorem itemOn_le (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) {i : ℕ} (hi : i < pc.n) :
    onClaims (itemOn os pc val i) ≤ itemV os pc val i ∧
      (pc.selecting = false → onClaims (itemOn os pc val i) = itemV os pc val i) := by
  have key : ∀ (x s : E) (t : Tuple), (s = 0 ∨ s = 1) →
      (if x * s = 1 then ({t} : Multiset Tuple) else 0) ≤ if x = 1 then {t} else 0 := by
    intro x s t hs
    rcases hs with rfl | rfl
    · simp
    · simp
  simp only [itemOn, itemV, onBit, onClaims_two]
  refine ⟨add_le_add (key _ _ _ (sel_bit hF hok hi 0)) (key _ _ _ (sel_bit hF hok hi 1)), fun hs => ?_⟩
  simp [hs]

/-- An item with a block's kind bits and words reads what the block reads from the label before it, and leaves the
label the block leaves. -/
theorem item_reads (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) {i : ℕ} (hi : i < pc.n) {b : Block}
    (hb0 : (pc.vals os val).b0 i = bitK b.b0) (hb1 : (pc.vals os val).b1 i = bitK b.b1)
    (hp : (pc.vals os val).p i = bitK b.p) (hw : ∀ c < 8, (pc.vals os val).ins i (6 + c) = b.w c) :
    itemV os pc val i = b.reads (LTin os pc val i) ∧ labT os pc val i = b.lab (LTin os pc val i) := by
  obtain ⟨-, -, hhdr, -, hitem, -, -⟩ := PoolCert.ok_parts hok
  obtain ⟨phz, pho, -⟩ := PoolCert.header_sem hF hhdr
  have k := kind_sem hF phz pho (PoolCert.item_parts (hitem i hi)).1
  dsimp only at k
  have e0 : val (o os (pc.p i)) 0 = bitK b.b0 := hb0
  have e1 : val (o os (pc.p i + 1)) 0 = bitK b.b1 := hb1
  have e2 : val (o os (pc.p i + 2)) 0 = bitK b.p := hp
  rw [e0, e1, e2] at k
  have hM : ∀ j < 8, Mv os pc val i j = emb (b.w j) := fun j hj => by rw [Mv_ins i j hj, hw j hj]
  have hlab : labT os pc val i = b.lab (LTin os pc val i) := by
    rw [labT_eq, k.2.2.2.2.1]
    by_cases hh : (!b.b0 && !b.b1) = true
    · rw [if_pos ((emb_hdr _ _).mpr hh)]
      simp only [Block.lab, Block.isHdr, hh, if_true]
      funext t
      simp only [hdrT, hdrTup]
      split_ifs with h0 h7
      · rfl
      · exact hM _ (by omega)
      · rfl
    · rw [if_neg (mt (emb_hdr _ _).mp hh)]
      simp only [Block.lab, Block.isHdr, hh, Bool.false_eq_true, if_false]
  have hslot : ∀ sl < 2, (fun t : Fin 16 => slotT os pc val i sl t) = slotTup (b.lab (LTin os pc val i)) b.w sl := by
    intro sl hsl
    funext t
    simp only [slotT, slotTup, hlab]
    split_ifs with h7 h11
    · rfl
    · exact hM _ (by omega)
    · rfl
  refine ⟨?_, hlab⟩
  simp only [itemV, valid, if_true, show (1 : ℕ) ≠ 0 by norm_num, if_false]
  rw [k.2.2.1, k.2.2.2.2.2.1, emb_mem, emb_pair, hslot 0 (by norm_num), hslot 1 (by norm_num), onClaims_two]
  rcases b with ⟨b0, b1, bp, w⟩
  cases b0 <;> cases b1 <;> cases bp <;> simp [Block.reads, Block.isMem]

/-- A padding item reads nothing and keeps the label. -/
theorem item_pad (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) {i : ℕ} (hi : i < pc.n)
    (hpad : (pc.vals os val).pad i = 1) :
    itemV os pc val i = 0 ∧ labT os pc val i = LTin os pc val i := by
  obtain ⟨-, -, hhdr, -, hitem, -, -⟩ := PoolCert.ok_parts hok
  obtain ⟨phz, pho, -⟩ := PoolCert.header_sem hF hhdr
  have k := kind_sem hF phz pho (PoolCert.item_parts (hitem i hi)).1
  dsimp only at k
  have hb := (PoolCert.pool_sem hF hok).bits i hi
  obtain ⟨a0, a1⟩ := pad_one hb.1 hb.2.1 hpad
  have e0 : val (o os (pc.p i)) 0 = bitK true := by
    show (pc.vals os val).b0 i = _
    rw [a0]; simp [bitK]
  have e1 : val (o os (pc.p i + 1)) 0 = bitK true := by
    show (pc.vals os val).b1 i = _
    rw [a1]; simp [bitK]
  rw [e0, e1] at k
  refine ⟨?_, ?_⟩
  · simp only [itemV, valid, if_true, show (1 : ℕ) ≠ 0 by norm_num, if_false]
    rw [k.2.2.1, k.2.2.2.2.2.1, onClaims_two]
    simp [bitK, two_K', emb_zero]
  · rw [labT_eq, k.2.2.2.2.1, if_neg (mt (emb_hdr _ _).mp (by decide))]

/-- A pool's claims on are at most the sum of the sets its runs name, and that sum when it does not select. Each run
`a` (an item starting one) names the set `C a`: its expected digest is `ClaimSet.digest F (C a)`, and no row of the
pool collides with the set's chain. -/
theorem pool_claims (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) (F : (ℕ → K) → Bool → ℕ → K)
    (C : ℕ → ClaimSet)
    (hC : ∀ a < pc.n, pc.sigma os val a = true → Names F pc.n (pc.vals os val) (pc.X os val a) (C a)) :
    onClaims (slots os pc val) ≤ ∑ a ∈ (Finset.range pc.n).filter (pc.sigma os val · = true), (C a).tuples ∧
      (pc.selecting = false →
        onClaims (slots os pc val) = ∑ a ∈ (Finset.range pc.n).filter (pc.sigma os val · = true), (C a).tuples) := by
  classical
  have hS := PoolCert.pool_sem hF hok
  have hσ0 : pc.sigma os val 0 = true := PoolCert.sigma_zero
  have hsteady := PoolCert.steady hF hok
  have hrun := fun a (ha : a < pc.n) (hσa : pc.sigma os val a = true) =>
    run_reads hS hσ0 hsteady (chain_of F iv (C a).blocks) (blocks_ne _) (hC a ha hσa).2 ha hσa (hC a ha hσa).1
  have hlen : ∀ a, 0 < (C a).blocks.length := fun a => List.length_pos_of_ne_nil (blocks_ne _)
  -- Each item reads its run's block, or is padding.
  have hsum := reads_sum hσ0 (fun a => (C a).blocks) (labT os pc val) (itemV os pc val)
    (fun a ha hσa => ⟨(hrun a ha hσa).1, fun i h1 h2 =>
      ((hrun a ha hσa).2 ((C a).blocks.length - 1) (by have := hlen a; omega)).1 i h1 (by omega)⟩)
    (fun i hi => by
      set s := seg (pc.sigma os val) i with hs
      have hσs : pc.sigma os val s = true := seg_sigma hσ0 i
      have hsi : s ≤ i := seg_le _ i
      obtain ⟨hfit, hmatch⟩ := hrun s (by omega) hσs
      have hC' := chain_of F iv (C s).blocks
      split
      · rename_i hj
        obtain ⟨-, hin⟩ := hmatch (i - s) hj
        rw [show s + (i - s) = i by omega] at hin
        obtain ⟨-, b0, b1, bp⟩ := kinds_of_counter hS hi ((hin 0 (by norm_num) (by norm_num)).trans (hC'.counter _ hj))
        exact item_reads hF hok hi b0 b1 bp fun c hc =>
          (hin (6 + c) (by omega) (by omega)).trans (hC'.words _ hj c hc)
      · rename_i hj
        have hL := hlen s
        obtain ⟨-, hin⟩ := hmatch ((C s).blocks.length - 1) (by omega)
        obtain ⟨-, -, hb1, -⟩ := kinds_of_counter hS (by omega)
          ((hin 0 (by norm_num) (by norm_num)).trans (hC'.counter _ (by omega)))
        rw [blocks_last] at hb1
        have hlast : (pc.vals os val).b1 (s + (C s).blocks.length - 1) = 1 := by
          rw [(show s + (C s).blocks.length - 1 = s + ((C s).blocks.length - 1) by omega), hb1]
          simp [bitK]
        have hpad := pad_after hS hL hlast (i - (s + (C s).blocks.length)) i (by omega) hi hs.symm
        exact item_pad hF hok hi hpad)
  simp only [readC_blocks] at hsum
  have hle := fun i (hi : i ∈ Finset.range pc.n) => itemOn_le hF hok (Finset.mem_range.mp hi)
  rw [slots, onClaims_slotsN, ← hsum]
  exact ⟨Finset.sum_le_sum fun i hi => (hle i hi).1, fun hs => Finset.sum_congr rfl fun i hi => (hle i hi).2 hs⟩

/-- A pool of one digest that does not select has the claims on of the set its digest names, unless a row collides
with the set's chain. -/
theorem decl_claims (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) (hsel : pc.selecting = false)
    (hr : pc.runs = 1) (F : (ℕ → K) → Bool → ℕ → K) (D : ClaimSet)
    (hd : ∀ k : Fin 4, val (pc.digests.getD 0 0) k = ClaimSet.digest F D k)
    (hcr : ChainCR pc.n (pc.vals os val) D.blocks.length (chainIn F iv D.blocks) (chainOut F iv D.blocks)) :
    onClaims (slots os pc val) = D.tuples := by
  classical
  have hσ : ∀ a, pc.sigma os val a = decide (a = 0) := by
    intro a
    simp only [PoolCert.sigma, PoolCert.startOf, hr, lt_irrefl, and_false, if_false]
    by_cases h : a = 0 <;> simp [h]
  obtain ⟨hch0, -, hhdr, -⟩ := PoolCert.ok_parts hok
  obtain ⟨-, -, -, -, -, -, hh⟩ := PoolCert.header_sem hF hhdr
  obtain ⟨hlo, hhi⟩ := hh 0 (by omega)
  have hn : 0 < pc.n := by simp only [PoolCert.n, chunk]; omega
  have hX : pc.X os val 0 = halves (ClaimSet.digest F D) := by
    simp only [PoolCert.X, PoolCert.eLo, PoolCert.eHi, hr, lt_irrefl, if_false, Nat.zero_div, halves]
    rw [hlo, hhi, hd 0, hd 1, hd 2, hd 3]
    rfl
  have h := (pool_claims hF hok F (fun _ => D) fun a ha hσa => by
    rw [hσ, decide_eq_true_eq] at hσa
    subst hσa
    exact ⟨hX, hcr⟩).2 hsel
  have hf : (Finset.range pc.n).filter (pc.sigma os val · = true) = {0} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, hσ, decide_eq_true_eq, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hn, h⟩⟩
  rw [h, hf, Finset.sum_singleton]

/-! The run one-hot. -/

/-- The run chunk `j` is in: how many of chunks `1..j` have their begin bit set. -/
noncomputable def runAt (os : Array (List ℕ)) (pc : PoolCert) (val : Val) : ℕ → ℕ
  | 0 => 0
  | j + 1 => runAt os pc val j + if pc.begins (j + 1) = true ∧ val (pc.beta os (j + 1)) 0 = 1 then 1 else 0

theorem runAt_mono {j : ℕ} : ∀ {j'}, j ≤ j' → runAt os pc val j ≤ runAt os pc val j'
  | 0, h => by obtain rfl : j = 0 := by omega
               exact le_rfl
  | j' + 1, h => by
    rcases Nat.lt_or_ge j (j' + 1) with hl | hl
    · exact (runAt_mono (j' := j') (by omega)).trans (by simp only [runAt]; omega)
    · obtain rfl : j = j' + 1 := by omega
      exact le_rfl

theorem runAt_one (hr : pc.runs ≤ 1) : ∀ j, runAt os pc val j = 0
  | 0 => rfl
  | j + 1 => by simp [runAt, runAt_one hr j, PoolCert.begins]; omega

/-- A begin bit is a bit. -/
theorem beta_bit (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) {j : ℕ} (hj : j < pc.chunks)
    (hb : pc.begins j = true) : IsBit (val (pc.beta os j) 0) := by
  obtain ⟨-, -, -, -, -, -, hbits⟩ := PoolCert.ok_parts hok
  simp only [PoolCert.bitsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at hbits
  rcases hbits.2 _ hj with h | h
  · rw [hb] at h; exact absurd h (by decide)
  · exact PoolCert.packed_bit hF h

/-- The run one-hot of chunk `j` is at `runAt j`. -/
theorem cur_runAt (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) :
    ∀ j < pc.chunks, ∀ r < pc.runs, Model.ev val (pc.cur os j r) = if r = runAt os pc val j then 1 else 0 := by
  obtain ⟨-, -, hhdr, hch, -, -, -⟩ := PoolCert.ok_parts hok
  obtain ⟨hz, ho, -⟩ := PoolCert.header_sem hF hhdr
  intro j
  induction j with
  | zero =>
    intro _ r _
    by_cases h : r = 0 <;> simp [PoolCert.cur, PoolCert.begins, runAt, h, hz, ho]
  | succ j ih =>
    intro hj r hr
    by_cases hb : pc.begins (j + 1) = true
    · rw [(PoolCert.chunk_sem hF hz (hch _ hj)).1 hb r hr, Nat.add_sub_cancel]
      rcases beta_bit hF hok hj hb with h | h
      · rw [h, emb_zero, mul_zero, zero_add, ih (by omega) r hr]
        simp [runAt, h]
      · rw [h, emb_one', mul_one, add_assoc, add_self_E, add_zero]
        rcases r with _ | r
        · simp [hz, runAt, h, hb]
        · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
          rw [ih (by omega) r (by omega)]
          simp [runAt, hb, h]
    · have hr1 : pc.runs ≤ 1 := by simp [PoolCert.begins] at hb; omega
      have hr0 : r = 0 := by omega
      subst hr0
      simp [PoolCert.cur, hb, ho, runAt_one hr1]

theorem dotE_single (q : ℕ) (h : ℕ → E) :
    ∀ k, PoolCert.dotE (fun r => if r = q then 1 else 0) h k = if q < k then h q else 0
  | 0 => by simp [PoolCert.dotE]
  | k + 1 => by
    rw [PoolCert.dotE, dotE_single q h k]
    by_cases hq : k = q
    · subst hq; simp
    · by_cases hl : q < k
      · simp [hq, hl, show q < k + 1 by omega]
      · simp [hq, hl, show ¬ q < k + 1 by omega]

/-- An item's expected digest is the digest of its chunk's run. -/
theorem X_runAt (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) {a : ℕ} (ha : a < pc.n)
    (hr : runAt os pc val (a / chunk) < pc.runs) :
    pc.X os val a = (toE (val (pc.digests.getD (runAt os pc val (a / chunk)) 0) 0)
      (val (pc.digests.getD (runAt os pc val (a / chunk)) 0) 1) 0,
      toE (val (pc.digests.getD (runAt os pc val (a / chunk)) 0) 2)
      (val (pc.digests.getD (runAt os pc val (a / chunk)) 0) 3) 0) := by
  obtain ⟨-, hr0, hhdr, hch, -, -, -⟩ := PoolCert.ok_parts hok
  obtain ⟨hz, -, -, -, -, -, hh⟩ := PoolCert.header_sem hF hhdr
  have hj : a / chunk < pc.chunks := by simp only [PoolCert.n, chunk] at ha; simp only [chunk]; omega
  obtain ⟨hlo, hhi⟩ := hh _ hr
  by_cases h1 : 1 < pc.runs
  · obtain ⟨l, h⟩ := (PoolCert.chunk_sem hF hz (hch _ hj)).2 h1
    have hc := cur_runAt hF hok _ hj
    simp only [PoolCert.X]
    rw [l, h, PoolCert.dotE_congr (c' := fun r => if r = runAt os pc val (a / chunk) then 1 else 0)
      (h' := fun r => Model.ev val (pc.halfLo os r)) _ fun r hr' => ⟨hc r hr', rfl⟩,
      PoolCert.dotE_congr (c' := fun r => if r = runAt os pc val (a / chunk) then 1 else 0)
      (h' := fun r => Model.ev val (pc.halfHi os r)) _ fun r hr' => ⟨hc r hr', rfl⟩,
      dotE_single, dotE_single, if_pos hr, if_pos hr, hlo, hhi]
  · have hz' : runAt os pc val (a / chunk) = 0 := runAt_one (by omega) _
    rw [hz'] at hlo hhi ⊢
    simp only [PoolCert.X, PoolCert.eLo, PoolCert.eHi, h1, if_false]
    rw [hlo, hhi]

/-- Of two items starting runs, the later is in a later run. -/
theorem runAt_lt {a a' : ℕ} (haa : a < a') (hσ' : pc.sigma os val a' = true) :
    runAt os pc val (a / chunk) < runAt os pc val (a' / chunk) := by
  rcases PoolCert.startOf_cases (pc := pc) (os := os) a' with ⟨h0, -⟩ | ⟨h0, hm, hr, hs⟩ | ⟨-, -, hs⟩
  · omega
  · simp only [PoolCert.sigma, hs, decide_eq_true_eq] at hσ'
    have hq : 0 < a' / chunk := by simp only [chunk] at hm ⊢; omega
    have hle : a / chunk ≤ a' / chunk - 1 := by simp only [chunk] at hm ⊢; omega
    have hb : pc.begins (a' / chunk) = true := by
      simp only [PoolCert.begins, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hq, hr⟩
    have hstep : runAt os pc val (a' / chunk) = runAt os pc val (a' / chunk - 1) + 1 := by
      obtain ⟨q, hq'⟩ : ∃ q, a' / chunk = q + 1 := ⟨a' / chunk - 1, by omega⟩
      rw [hq', runAt, Nat.add_sub_cancel, if_pos (by rw [← hq']; exact ⟨hb, hσ'⟩)]
    rw [hstep]
    exact Nat.lt_succ_of_le (runAt_mono hle)
  · simp [PoolCert.sigma, hs] at hσ'

/-- The children's pool: if its run one-hot closes at its last digest, its claims on are among the sum of the sets its
digests name, unless a row collides with one of the sets' chains. -/
theorem sel_claims (hF : Facts cs rl os st val) (hok : pc.ok os cs rl = true) (hend : pc.endOk os cs rl = true)
    (F : (ℕ → K) → Bool → ℕ → K) (Cs : ℕ → ClaimSet)
    (hd : ∀ r < pc.runs, ∀ k : Fin 4, val (pc.digests.getD r 0) k = ClaimSet.digest F (Cs r) k)
    (hcr : ∀ r < pc.runs, ChainCR pc.n (pc.vals os val) (Cs r).blocks.length (chainIn F iv (Cs r).blocks)
      (chainOut F iv (Cs r).blocks)) :
    onClaims (slots os pc val) ≤ ∑ r ∈ Finset.range pc.runs, (Cs r).tuples := by
  classical
  obtain ⟨hch0, hr0, -⟩ := PoolCert.ok_parts hok
  -- The one-hot closes at the last digest, so every chunk's run is a digest's.
  have hlast : runAt os pc val (pc.chunks - 1) = pc.runs - 1 := by
    have hm : (pc.endAt + 1 + (pc.runs - 1), Call.eqConstE (pc.cur os (pc.chunks - 1) (pc.runs - 1)) 1 0 0) ∈
        pc.endCalls os := by
      simp only [PoolCert.endCalls, List.mem_map, List.mem_range]
      exact ⟨pc.runs - 1, by omega, by simp [show pc.runs - 1 + 1 = pc.runs by omega]⟩
    have H : Model.ev val (pc.cur os (pc.chunks - 1) (pc.runs - 1)) = toE (ofWord 1) (ofWord 0) (ofWord 0) :=
      holds_of_mem hF hend hm
    rw [cur_runAt hF hok _ (by omega) _ (by omega), ofWord_one', ofWord_zero', toE_emb, emb_one'] at H
    by_contra hne
    rw [if_neg (Ne.symm hne)] at H
    exact zero_ne_one H
  have hlt : ∀ a < pc.n, runAt os pc val (a / chunk) < pc.runs := by
    intro a ha
    have : a / chunk ≤ pc.chunks - 1 := by simp only [PoolCert.n, chunk] at ha; simp only [chunk]; omega
    have := runAt_mono (os := os) (pc := pc) (val := val) this
    omega
  have hpc := (pool_claims hF hok F (fun a => Cs (runAt os pc val (a / chunk))) fun a ha _ => ⟨by
    rw [X_runAt hF hok ha (hlt a ha), halves, hd _ (hlt a ha) 0, hd _ (hlt a ha) 1, hd _ (hlt a ha) 2,
      hd _ (hlt a ha) 3]
    rfl, hcr _ (hlt a ha)⟩).1
  refine hpc.trans ?_
  rw [← Finset.sum_image (f := fun r => (Cs r).tuples) (g := fun a => runAt os pc val (a / chunk)) fun x hx y hy hxy => ?_]
  · refine Finset.sum_le_sum_of_subset fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_range.mpr (hlt a (Finset.mem_range.mp (Finset.mem_filter.mp ha).1))
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    rcases lt_trichotomy x y with h | h | h
    · exact absurd hxy (runAt_lt h hy.2).ne
    · exact h
    · exact absurd hxy (runAt_lt h hx.2).ne'

/-- In `val₀`, a union's children's digests name the sets `Cs r` and its declared digest names `D` under the
compression `F` (`blakeF` for BLAKE2s), and no row of either pool collides with those sets' chains. -/
structure SetsNamed (c : Cert) (cv : Cover) (val₀ : Val) (F : (ℕ → K) → Bool → ℕ → K) (Cs : ℕ → ClaimSet)
    (D : ClaimSet) : Prop where
  sel : ∀ r < (c.poolOf cv.sel).runs, ∀ k : Fin 4,
    val₀ ((c.poolOf cv.sel).digests.getD r 0) k = ClaimSet.digest F (Cs r) k
  decl : ∀ k : Fin 4, val₀ ((c.poolOf cv.decl).digests.getD 0 0) k = ClaimSet.digest F D k
  crSel : ∀ r < (c.poolOf cv.sel).runs, ChainCR (c.poolOf cv.sel).n ((c.poolOf cv.sel).vals c.outs val₀)
    (Cs r).blocks.length (chainIn F iv (Cs r).blocks) (chainOut F iv (Cs r).blocks)
  crDecl : ChainCR (c.poolOf cv.decl).n ((c.poolOf cv.decl).vals c.outs val₀) D.blocks.length
    (chainIn F iv D.blocks) (chainOut F iv D.blocks)

/-- On an accepted circuit, if the sets a union's digests name in `val₀` are such that the declared set's claims are
not among the children's, the two pools' claims on differ. -/
theorem sets_differ (c : Cert) (s : State) (h : c.accepts s = true) {cv : Cover} (hcv : cv ∈ c.covers)
    {st₀ : ℕ → Fin 4 → K} {val₀ : Val} (hv₀ : Holds st₀ s c.test val₀) {F : (ℕ → K) → Bool → ℕ → K}
    {Cs : ℕ → ClaimSet} {D : ClaimSet} (hN : SetsNamed c cv val₀ F Cs D)
    (hne : ¬ D.tuples ≤ ∑ r ∈ Finset.range (c.poolOf cv.sel).runs, (Cs r).tuples) :
    onClaims (slots c.outs (c.poolOf cv.sel) val₀) ≠ onClaims (slots c.outs (c.poolOf cv.decl) val₀) := by
  obtain ⟨-, -, hun, -, -, hcov⟩ := Cert.accepts_parts h
  simp only [Cert.coversOk, Bool.and_eq_true, Array.all_eq_true', List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq, Bool.not_eq_true'] at hcov
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsel, hdecl⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hds⟩, hdr⟩, hend⟩ := hcov.2 cv hcv
  obtain ⟨hF, -, hpools⟩ := facts_of_holds hun hv₀
  have hS' := sel_claims hF (hpools _ hsel).1 hend F Cs hN.sel hN.crSel
  have hD' := decl_claims hF (hpools _ hdecl).1 hds hdr F D hN.decl hN.crDecl
  intro heq
  apply hne
  rw [← hD', ← heq]
  exact hS'

open Classical Finset in
/-- `Bind.union_sound` with the two multisets read as the sets the digests name. Take an accepted circuit, one of its
unions, and an assignment `val₀` holding every constraint but the tests in which the union's digests name sets
(`SetsNamed`) and the declared set's claims are not among the children's. Then, with the point uniform on `S^5` and
the prover answering as in `Bind.union_sound`, the coverage test holds at a matching point for at most a `4N/|S|`
fraction of the outcomes. -/
theorem union_sound_sets (c : Cert) (s : State) (h : c.accepts s = true) {cv : Cover} (hcv : cv ∈ c.covers)
    {st₀ : ℕ → Fin 4 → K} {val₀ : Val} (hv₀ : Holds st₀ s c.test val₀)
    {F : (ℕ → K) → Bool → ℕ → K} {Cs : ℕ → ClaimSet} {D : ClaimSet} (hN : SetsNamed c cv val₀ F Cs D)
    (hne : ¬ D.tuples ≤ ∑ r ∈ Finset.range (c.poolOf cv.sel).runs, (Cs r).tuples)
    (S : Finset E) {Ω : Type} [Fintype Ω] (pt : Ω → Fin 5 → E) (hS : ∀ ω, pt ω ∈ Fintype.piFinset fun _ : Fin 5 => S)
    (hpt : ∀ f ∈ Fintype.piFinset (fun _ : Fin 5 => S), #S ^ 5 * #{ω | pt ω = f} = Fintype.card Ω)
    (st : Ω → ℕ → Fin 4 → K) (val : Ω → Val) (hv : ∀ ω, Holds (st ω) s c.test (val ω))
    (hcr : ∀ ω, HashCR s val₀ (val ω)) (hwin : ∀ ω, WindowCR s val₀ (val ω))
    (hseed : ∀ ω, ∀ n ∈ seedsOf s (c.transcripts.getD cv.transcript default), nu val₀ n = nu (val ω) n) :
    (#{ω | (c.points.getD cv.sel default).at (val ω) = pt ω ∧
        ∀ a b, s.unions[cv.test]? = some (a, b) → val ω a = val ω b} : ℚ≥0) / Fintype.card Ω ≤
      4 * (2 * max (c.poolOf cv.sel).n (c.poolOf cv.decl).n : ℕ) / #S :=
  union_sound c s h hcv hv₀ (sets_differ c s h hcv hv₀ hN hne) S pt hS hpt st val hv hcr hwin hseed

end Claims

end LeanVMCircuits.Rec.Bind
