/-
  LeanVM.Guest.End

  The end theorems of the guest's verification, from the pieces still being proved: soundness
  (a valid execution of the guest gives `NodeSpec`), completeness (`NodeRel` within the deployed
  limits gives a valid execution that fits the verifier), and their composition with the
  protocol's two theorems.
-/

module

public import LeanVM.Protocol.LeanVM
public import LeanVM.Protocol.EndToEnd.Front.PubPhase
public import LeanVM.Protocol.EndToEnd.Complete.Public
public import LeanVM.Guest.Bytecode
public import LeanVM.Guest.CoreData
public import LeanVM.Guest.Logic
public import LeanVM.Guest.Memory
public import LeanVM.Guest.Hints
public import LeanVM.Guest.B1.Whir.CapAgrees

/-!
# The end theorems

**The run's start** (proved here). A run of `guest` starts at `(g^0, 1)` in `__jump_tables`, the
`4478` `SET`s of the jump table's slots in `main`'s frame, and falls through into `main` at pc
`mainEntry = 4478`, with `fp = 1`. `safe_jumpTables`: a halting run from `(g^0, 1)` has every slot
written (`JumpTables`: each `SET` of `Memory.tableCells` holds at `fp = 1`) and halts from
`(g^mainEntry, 1)`; `reach_jumpTables` is the converse for completeness. Memory is read through
`MemImage.read` throughout, the `Reader` of the core IR being `L.read`.

**Soundness** (`SoundPieces`, `guest_sound_of`). B2 is a family of contracts (`Contracts`: an
index, entries, pre- and postconditions on the frame over the memory), as checker K's
`Check.Pre`, `Check.Post` over its `Glob`:

* `step`: every function's contract for runs shorter than `n + 1`, given all of them for runs
  shorter than `n` (`checkFn_run` with `main = false`, then `funSpec_induction`);
* `main`: from `main`'s entry at `fp = 1`, the jump table written and every contract for runs
  shorter than the steps left, `coreProgram.Rel L.read "main" [] []` (`checkFn_run` with
  `main = true`, whose `ret` is the halting jump);
* `mainB1`: group 7's soundness of `main`: on a memory of `2^κ` words, `16 ≤ κ ≤ 32`, whose words
  `g^0` and `g^1` are a digest's two cells, `main`'s relation gives a seed and a statement of
  that digest held by a witness (`main_sound`, its callees' soundness and `aggregate_claims`'
  discharged).

The public input reaches `main` through memory, not through its arguments: `main` takes none,
and reads `m[0]`, `m[1]`, which `ValidExecution` fixes to `publicDigest input`'s halves
(`digestScalars_publicDigest`).

**Completeness** (`CompletePieces`, `guest_complete_of`). The memory is the honest memory of a
call tree (`Memory.honest`) at the certificates' frame sizes `fs`, headers `H` and cells `C`, the
tree placed at the certificates' cells `cert` (`Memory.HonestAt`: its `HeapBuf` pointers the bump
allocator's, its `frameAddr`s in its frames):

* `honest`: for `NodeRel` within the deployed limits (`Limits`), a tree of `main`, valid on some
  memory, satisfying `Memory.Honest` with the public input as `main`'s header, of cost at most
  `budget s w` (group 7's completeness of `main` at the bump allocator's `HeapBuf` pointers,
  agent T's `Program.Rel.tree` and the discharge of `Honest`);
* `table`: `main`'s cells hold its jump table (`Memory.tableCells`);
* `b2`: on the honest memory, `main` runs from its entry at `fp = 1` to the halting registers
  (checker K's completeness, `exec_complete` and the certificates, by `returns_induction`);
* `size`: that run's committed size is at most the tree's cost (K, counting the instructions of
  each instance).

`Limits` transcribes the six findings of `TRIAGE.md`; they do not bound the run's size, so the
size is a seventh limit, `budget s w ≤ 2^28`. An eighth is on the children's proofs: their
openings agree in the guest's write-once Merkle caps (`CapsAgree`). The deployed budget is linear in the node's work
(`Budget`: the words a run allocates and the instructions of each opcode it executes, each a
constant plus a coefficient per declared claim, coverage slot, raw signature or blob, child and
child's claim, `work s w`), at `Trace.committedSize`'s formula (`Budget.size`), so the final
statement is `GuestComplete (b.size ∘ work)` for the budget `b` the certificates count.
`CompletePiecesWithin` splits the size at a call tree's instruction counts `cnt T op` (`count`:
the run's against the tree's; `honest`: the tree's words and counts against the budget), and
`guest_complete_within` gives `GuestCompleteWithin b`.

**Composition** (`aggregate_sound_of`, `aggregate_complete_of`). With
`knowledgeSoundness_holds`, an adversary in the random-oracle experiment whose statement is the
guest makes the verifier accept a public input that is no `NodeSpec` statement's digest with
probability at most `soundnessError Q`. With `LeanVM.completeness`, the honest prover's proof of
the guest's honest execution is rejected with probability at most `completenessError fuel`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.EndToEnd
open scoped ENNReal

@[expose] public section

/-- The guest's bytecode, as the verifier and `NodeSpec` read it. -/
abbrev bytecode : List K := bytecodeWords guest

theorem bytecode_length : bytecode.length = 2 ^ 22 := by
  simp [bytecode, bytecodeWords, guest_logSize]

/-- The public input a digest is: its two halves in words `0` and `1`
(`Front.publicInputOfDigest`). -/
abbrev publicInputOf (d : Digest) : PublicInput := Front.publicInputOfDigest d

theorem publicDigest_publicInputOf (d : Digest) : publicDigest (publicInputOf d) = d := by
  ext i hi
  interval_cases i <;>
    simp [publicDigest, Front.publicInputOfDigest, lowWord_ofWords, highWord_ofWords]

/-! ## The jump table -/

/-- `main`'s entry pc, after `__jump_tables`. -/
def mainEntry : ℕ := Data.f0.len

theorem f1_main : Data.f1.name = "main" ∧ Data.f1.entry = mainEntry := ⟨rfl, rfl⟩

/-- **The jump table is written**: every slot of `Memory.tableCells` holds its word. -/
def JumpTables {κ : ℕ} (L : MemImage κ) : Prop := ∀ q ∈ Memory.tableCells, L.read (gpow q.1) = some q.2

/-- The slot a `SET` writes. -/
def setCell? : OInstr → Option (ℕ × E)
  | .set o k0 k1 k2 => some (o, OInstr.imm k0 k1 k2)
  | _ => none

theorem tableCells_eq : Memory.tableCells = Data.f0.code.filterMap setCell? := by
  unfold Memory.tableCells
  congr 1

set_option maxRecDepth 100000 in
theorem f0_all_set : Data.f0.code.all (fun ins ↦ (setCell? ins).isSome) = true := by
  decide +kernel

theorem f0_mem : Data.f0 ∈ Data.functions := List.mem_cons_self

theorem f0_entry : Data.f0.entry = 0 := rfl

/-- Instruction `i` of `__jump_tables` is a `SET` of a slot of the table. -/
theorem f0_instr {i : ℕ} (hi : i < Data.f0.len) :
    ∃ o k0 k1 k2, Data.f0.instrAt i = .set o k0 k1 k2 ∧ (o, OInstr.imm k0 k1 k2) ∈ Memory.tableCells := by
  have hc := CompiledFn.getElem?_code (CompiledFn.wellChunked_of_mem f0_mem) hi
  have hmem : Data.f0.instrAt i ∈ Data.f0.code := List.mem_of_getElem? hc
  have hs := List.all_eq_true.mp f0_all_set _ hmem
  rcases h : Data.f0.instrAt i with _ | _ | ⟨o, k0, k1, k2⟩ | _ | _ | _ <;> rw [h] at hs hmem <;>
    simp only [setCell?, Option.isSome_none, Bool.false_eq_true] at hs
  exact ⟨o, k0, k1, k2, rfl, tableCells_eq ▸ List.mem_filterMap.mpr ⟨_, hmem, rfl⟩⟩

theorem f0_fetch {i : ℕ} (hi : i < Data.f0.len) :
    guest.fetch (gpow i) = some (Data.f0.instrAt i).toInstr := by
  have := guest_fetch f0_mem hi
  rwa [f0_entry, Nat.zero_add] at this

theorem f0_pc_lt {i : ℕ} (hi : i < Data.f0.len) : i < 2 ^ guest.logSize - 1 := by
  have := guest_pc_lt f0_mem hi
  rwa [f0_entry, Nat.zero_add] at this

theorem gpow_mul_one (o : ℕ) : (1 : K) * gpow o = gpow o := one_mul _

/-- **The run's start, soundly**: a halting run from `(g^0, 1)` writes the jump table and halts
from `main`'s entry at `fp = 1`. -/
theorem safe_jumpTables {κ : ℕ} {L : MemImage κ} {k : ℕ} (h : Safe guest L k ⟨gpow 0, 1⟩) :
    JumpTables L ∧ ∃ k', Safe guest L k' ⟨gpow mainEntry, 1⟩ := by
  have hwalk : ∀ i ≤ Data.f0.len, (∀ j < i, Holds L j 1 (Data.f0.instrAt j)) ∧
      ∃ k', Safe guest L k' ⟨gpow i, 1⟩ := by
    intro i
    induction i with
    | zero => exact fun _ ↦ ⟨fun _ hj ↦ absurd hj (Nat.not_lt_zero _), k, h⟩
    | succ i ih =>
      intro hi
      obtain ⟨hh, k', hk'⟩ := ih (by omega)
      obtain ⟨o, k0, k1, k2, hins, -⟩ := f0_instr (show i < Data.f0.len by omega)
      have hf := f0_fetch (show i < Data.f0.len by omega)
      rw [hins] at hf
      obtain ⟨k'', -, hH, hs⟩ := hk'.fallThrough hf (f0_pc_lt (by omega)) rfl
      refine ⟨fun j hj ↦ ?_, k'', hs⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hh j hj
      · rw [hins]; exact hH
  obtain ⟨hh, hrun⟩ := hwalk _ le_rfl
  refine ⟨fun q hq ↦ ?_, hrun⟩
  obtain ⟨ins, hmem, hq⟩ := List.mem_filterMap.mp (tableCells_eq ▸ hq)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  have hlen : i < Data.f0.len := CompiledFn.length_code (CompiledFn.wellChunked_of_mem f0_mem) ▸ hi
  have hc := CompiledFn.getElem?_code (CompiledFn.wellChunked_of_mem f0_mem) hlen
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hc
  obtain ⟨o, k0, k1, k2, hins, -⟩ := f0_instr hlen
  have hH := hh i hlen
  rw [hc, hins] at hq
  rw [hins] at hH
  simp only [setCell?, Option.some.injEq] at hq
  subst hq
  rw [← gpow_mul_one]
  exact hH

/-- **The run's start, completely**: on a memory holding the jump table, `__jump_tables` runs
from `(g^0, 1)` to `main`'s entry at `fp = 1`. -/
theorem reach_jumpTables {κ : ℕ} {L : MemImage κ} (h : JumpTables L) :
    Reach guest L ⟨gpow 0, 1⟩ ⟨gpow mainEntry, 1⟩ := by
  have hwalk : ∀ i ≤ Data.f0.len, Reach guest L ⟨gpow 0, 1⟩ ⟨gpow i, 1⟩ := by
    intro i
    induction i with
    | zero => exact fun _ ↦ Reach.refl _
    | succ i ih =>
      intro hi
      obtain ⟨o, k0, k1, k2, hins, hq⟩ := f0_instr (show i < Data.f0.len by omega)
      have hf := f0_fetch (show i < Data.f0.len by omega)
      rw [hins] at hf
      have hH : Holds L i 1 (.set o k0 k1 k2) := by
        show L.read (1 * gpow o) = some (OInstr.imm k0 k1 k2)
        rw [gpow_mul_one]
        exact h _ hq
      exact (ih (by omega)).trans (reach_fallThrough hf (f0_pc_lt (by omega)) rfl hH)
  exact hwalk _ le_rfl

/-! ## Soundness -/

/-- **B2's contracts**: a family of compiled functions, their entry pcs, and a pre- and a
postcondition on the frame pointer over each memory (checker K: `ι = ℕ`, `entry j =
(G.sig j).entry`, `pre j κ L = Check.Pre G L j`, `post j κ L = Check.Post coreProgram G L j`). -/
structure Contracts where
  /-- The functions. -/
  ι : Type
  /-- Their entry pcs. -/
  entry : ι → ℕ
  /-- Their preconditions. -/
  pre : ι → (κ : ℕ) → MemImage κ → K → Prop
  /-- Their postconditions. -/
  post : ι → (κ : ℕ) → MemImage κ → K → Prop

/-- Every contract of `B`, for runs shorter than `n`. -/
def Contracts.Lt (B : Contracts) {κ : ℕ} (L : MemImage κ) (n : ℕ) : Prop :=
  ∀ j, FunSpecLt guest L n (B.entry j) (B.pre j κ L) (B.post j κ L)

/-- **What soundness rests on**, for the contracts `B`. -/
structure SoundPieces (B : Contracts) : Prop where
  /-- B2 (checker K, `checkFn_run` at `main = false`): each contract for runs shorter than
  `n + 1`, given all of them for runs shorter than `n`. -/
  step : ∀ {κ : ℕ} (L : MemImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ n, B.Lt L n →
    ∀ i, FunSpecLt guest L (n + 1) (B.entry i) (B.pre i κ L) (B.post i κ L)
  /-- B2 (checker K, `checkFn_run` at `main = true`): a halting run from `main`'s entry at
  `fp = 1`, the jump table written and every contract holding for runs shorter than it, gives
  `main`'s relation on the memory. -/
  main : ∀ {κ : ℕ} (L : MemImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → JumpTables L → ∀ k,
    B.Lt L k → Safe guest L k ⟨gpow mainEntry, 1⟩ → coreProgram.Rel L.read "main" [] []
  /-- B1 (group 7, `main_sound`): on a memory whose words `g^0`, `g^1` are the cells of `D`,
  `main`'s relation gives a seed and a statement of digest `D` that a witness holds. -/
  mainB1 : ∀ {κ : ℕ} (L : MemImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ D : Digest,
    L.read 1 = some (digestScalars D).1 → L.read g = some (digestScalars D).2 →
    coreProgram.Rel L.read "main" [] [] →
      ∃ seed s w, statementDigest seed s = D ∧ NodeRel bytecode seed s w

variable {B : Contracts}

/-- **B2 for the whole guest**: a halting run from `(g^0, 1)` gives `main`'s relation. -/
theorem mainRel_of (h : SoundPieces B) {κ : ℕ} {L : MemImage κ} (h16 : minLogMem ≤ κ)
    (h32 : κ ≤ maxLogMem) {k : ℕ} (hs : Safe guest L k ⟨gpow 0, 1⟩) :
    coreProgram.Rel L.read "main" [] [] := by
  obtain ⟨hjt, k', hk'⟩ := safe_jumpTables hs
  have hall : ∀ j, FunSpec guest L (B.entry j) (B.pre j κ L) (B.post j κ L) :=
    funSpec_induction (P := fun j ↦ B.pre j κ L) (Q := fun j ↦ B.post j κ L) (h.step L h16 h32)
  exact h.main L h16 h32 hjt k' (fun j ↦ (hall j).lt k') hk'

/-- **Soundness at any public input**: a valid execution of the guest on `input` gives a
statement of digest `publicDigest input` that a witness holds. -/
theorem guest_sound_input (h : SoundPieces B) (input : PublicInput) (t : Trace guest)
    (hv : ValidExecution guest input t) :
    ∃ seed s, statementDigest seed s = publicDigest input ∧ s.defer.Shaped bytecode ∧
      NodeSpec bytecode seed s := by
  have hs := safe_of_validExecution hv
  obtain ⟨⟨h16, h32, h0, h1⟩, -⟩ := hv
  have hrel := mainRel_of h h16 h32 hs
  have hd := Complete.digestScalars_publicDigest input
  obtain ⟨seed, s, w, hD, hw⟩ := h.mainB1 t.image h16 h32 (publicDigest input)
    (by rw [hd, ← pow_zero g]; exact h0) (by rw [hd, ← pow_one g]; exact h1) hrel
  exact ⟨seed, s, hD, hw.1, w, hw⟩

/-- **Soundness**, the statement: a valid execution of the guest on the digest of `s` under
`seed` gives a statement of the same digest, of the guest's shape, that a witness holds. -/
def GuestSound : Prop :=
  ∀ seed s (t : Trace guest), ValidExecution guest (publicInputOf (statementDigest seed s)) t →
    ∃ seed' s', statementDigest seed' s' = statementDigest seed s ∧ s'.defer.Shaped bytecode ∧
      NodeSpec bytecode seed' s'

/-- **Soundness, from its pieces.** -/
theorem guest_sound_of (h : SoundPieces B) : GuestSound := fun seed s t hv ↦ by
  have := guest_sound_input h _ t hv
  rwa [publicDigest_publicInputOf] at this

/-! ## Completeness -/

open Hints in
/-- The coverage table's slots: each region's declared claims and its duplicates, as
`honestPushes` plans them. -/
def coverage (s : NodeStatement) (w : NodeWitness) : ℕ :=
  let ch := w.children
  s.claims.xmss.length + (plan s.claims.xmss ((direct s.claims.xmss w.xmss).map (·.1))
      (ch.map (·.statement.claims.xmss))).dups.length +
    s.claims.sphincs.length + (plan s.claims.sphincs ((direct s.claims.sphincs w.sphincs).map (·.1))
      (ch.map (·.statement.claims.sphincs))).dups.length +
    s.claims.da.length + (plan s.claims.da ((direct s.claims.da w.da).map (·.1))
      (ch.map (·.statement.claims.da))).dups.length

open Hints in
/-- **The deployed limits** (`TRIAGE.md`'s findings), where `NodeRel` admits witnesses the guest
cannot run. -/
structure Limits (s : NodeStatement) (w : NodeWitness) : Prop where
  /-- 1. A child's stack log is in `[22, 28]` (G:2246). -/
  stackLog : ∀ c ∈ w.children, ∀ layout r, Verifier.announced bytecode c.proof.stream = some (layout, r) →
    22 ≤ layout.stackLog ∧ layout.stackLog ≤ 28
  /-- 2. A child's proof stream is at most `8192` scalars (G:2095). -/
  stream : ∀ c ∈ w.children, c.proof.stream.length ≤ streamCap
  /-- 3. At most one DA claim is held directly (G:3154). -/
  directDa : (direct s.claims.da w.da).length ≤ 1
  /-- 4. A claim declared `n` times is held `n` times, by signatures or by distinct entries of
  the children's lists (G:2815, 2835, 2876, 3291). -/
  xmssHeld : ∀ x, s.claims.xmss.count x ≤ ((direct s.claims.xmss w.xmss).map (·.1)).count x +
    (w.children.map fun c ↦ c.statement.claims.xmss.count x).sum
  sphincsHeld : ∀ x, s.claims.sphincs.count x ≤ ((direct s.claims.sphincs w.sphincs).map (·.1)).count x +
    (w.children.map fun c ↦ c.statement.claims.sphincs.count x).sum
  daHeld : ∀ x, s.claims.da.count x ≤ ((direct s.claims.da w.da).map (·.1)).count x +
    (w.children.map fun c ↦ c.statement.claims.da.count x).sum
  /-- 5. At most `16` children (G:3145-3169). -/
  children : w.children.length ≤ 16
  /-- 5. At most `16` DA roots per statement and per child. -/
  daRoots : s.claims.da.length ≤ 16 ∧ ∀ c ∈ w.children, c.statement.claims.da.length ≤ 16
  /-- 5. Every signature list below `2^16` (G:3275). -/
  lists : ∀ c ∈ w.children, c.statement.claims.xmss.length < 2 ^ 16 ∧
    c.statement.claims.sphincs.length < 2 ^ 16
  /-- 5. The coverage table below `2^16`. -/
  coverage : coverage s w < 2 ^ 16
  /-- 6. At least one declared claim (G:3207). -/
  nonempty : 0 < s.claims.xmss.length + s.claims.sphincs.length + s.claims.da.length

/-- **A child's openings agree in the guest's Merkle caps**: the guest writes each committed
tree's cap once, so two openings of one query step meeting at a node must give it one digest,
where the specification checks each opening alone against the root (`B1.CapAgrees`). It holds at
every query step of each child's deferring verifier, under the node's seed; one tree's openings,
the honest prover's, agree (`B1.capAgrees_of_tree`). -/
def CapsAgree (seed : Digest) (w : NodeWitness) : Prop :=
  ∀ c ∈ w.children, ∀ b ∈ B1.queriesOf
      (Verifier.deferredProgram c.fresh bytecode (statementDigest seed c.statement))
      ⟨blake2sBytes (digestBytes seed ++ digestBytes (statementDigest seed c.statement)),
        c.proof.stream, c.proof.openings, []⟩,
    B1.BatchAgrees b.1 b.2

/-! ## The seventh limit -/

/-- **A node's work**: what the size of its run grows with. -/
structure Work where
  /-- The declared claims, of the three lists. -/
  declared : ℕ
  /-- The coverage table's slots. -/
  coverage : ℕ
  /-- The raw leanXMSS signatures. -/
  rawXmss : ℕ
  /-- The raw leanSPHINCS signatures. -/
  rawSphincs : ℕ
  /-- The blob matrices held directly. -/
  rawDa : ℕ
  /-- Their rows: the blobs held directly. -/
  rawDaRows : ℕ
  /-- The children. -/
  children : ℕ
  /-- The children's declared claims, of the three lists. -/
  childClaims : ℕ

/-- The work of the node `s` with the witness `w`. -/
def work (s : NodeStatement) (w : NodeWitness) : Work where
  declared := s.claims.xmss.length + s.claims.sphincs.length + s.claims.da.length
  coverage := coverage s w
  rawXmss := (Hints.direct s.claims.xmss w.xmss).length
  rawSphincs := (Hints.direct s.claims.sphincs w.sphincs).length
  rawDa := (Hints.direct s.claims.da w.da).length
  rawDaRows := ((Hints.direct s.claims.da w.da).map fun p ↦ p.2.rows.length).sum
  children := w.children.length
  childClaims := (w.children.map fun c ↦ c.statement.claims.xmss.length +
    c.statement.claims.sphincs.length + c.statement.claims.da.length).sum

/-- A bound linear in the work: a constant and a coefficient per unit. -/
structure Linear where
  base : ℕ
  declared : ℕ
  coverage : ℕ
  rawXmss : ℕ
  rawSphincs : ℕ
  rawDa : ℕ
  rawDaRows : ℕ
  children : ℕ
  childClaims : ℕ

/-- The bound at the work `u`. -/
def Linear.eval (l : Linear) (u : Work) : ℕ :=
  l.base + l.declared * u.declared + l.coverage * u.coverage + l.rawXmss * u.rawXmss +
    l.rawSphincs * u.rawSphincs + l.rawDa * u.rawDa + l.rawDaRows * u.rawDaRows + l.children * u.children +
    l.childClaims * u.childClaims

/-- **A size budget**: bounds on the words a run allocates and on the instructions of each opcode
it executes. -/
structure Budget where
  /-- The words allocated. -/
  words : Linear
  /-- The instructions of each opcode executed. -/
  instrs : Opcode → Linear

/-- `Trace.committedSize`'s formula for a run of the guest allocating `words` words, on
`2^logMem words` of memory, and executing `instrs op` instructions of each opcode `op`. -/
def sizeOf (words : ℕ) (instrs : Opcode → ℕ) : ℕ :=
  let height (op : Opcode) : ℕ := 2 ^ Nat.clog 2 (instrs op)
  4 * 2 ^ Memory.logMem words + 2 ^ guest.logSize +
    15 * height .xor + 15 * height .mulNative + 8 * height .setConstant + 15 * height .deref +
    14 * height .jump + 19 * height .blake2s + 2 ^ 8 * height .blake2s

/-- The committed size of a run within the budget at the work `u`. -/
def Budget.size (b : Budget) (u : Work) : ℕ := sizeOf (b.words.eval u) fun op ↦ (b.instrs op).eval u

theorem logMem_mono {m n : ℕ} (h : m ≤ n) : Memory.logMem m ≤ Memory.logMem n :=
  max_le_max le_rfl (Nat.clog_mono_right 2 h)

theorem sizeOf_mono {w w' : ℕ} {i i' : Opcode → ℕ} (hw : w ≤ w') (hi : ∀ op, i op ≤ i' op) :
    sizeOf w i ≤ sizeOf w' i' := by
  have hh : ∀ op, 2 ^ Nat.clog 2 (i op) ≤ 2 ^ Nat.clog 2 (i' op) := fun op ↦
    Nat.pow_le_pow_right (by norm_num) (Nat.clog_mono_right 2 (hi op))
  have hm : 2 ^ Memory.logMem w ≤ 2 ^ Memory.logMem w' :=
    Nat.pow_le_pow_right (by norm_num) (logMem_mono hw)
  dsimp only [sizeOf]
  have := hh .xor; have := hh .mulNative; have := hh .setConstant; have := hh .deref
  have := hh .jump; have := hh .blake2s
  omega

/-- **A budget's words within its size**: the memory alone commits `4` words per word. -/
theorem words_le_of_size {b : Budget} {u : Work} (h : b.size u ≤ 2 ^ 28) : b.words.eval u ≤ 2 ^ 26 := by
  have hm := Memory.le_two_pow_logMem (b.words.eval u)
  have : 4 * 2 ^ Memory.logMem (b.words.eval u) ≤ b.size u := by
    unfold Budget.size; dsimp only [sizeOf]; simp only [Nat.add_assoc]; exact Nat.le_add_right _ _
  omega

/-- The committed size of a run on `2^logMem n` words is `sizeOf n` at its counts. -/
theorem committedSize_eq {n : ℕ} (L : MemImage (Memory.logMem n)) (steps : ℕ) :
    (⟨_, L, steps⟩ : Trace guest).committedSize = sizeOf n (⟨_, L, steps⟩ : Trace guest).count :=
  rfl

/-- `main`'s header: the public input's two words. -/
abbrev hdrOf (d : Digest) : E × E := ((publicInputOf d).word0, (publicInputOf d).word1)

/-- **What completeness rests on**, for the certificates' frame sizes `fs`, headers `H`, cells `C`
and value cells `cert`, a cost of a call tree and a budget of a node. -/
structure CompletePieces (fs : String → ℕ) (H : Memory.Inst → ℕ → E × E)
    (C : Memory.Inst → List (ℕ × E)) (cert : String → V → ℕ) (cost : Memory.Tree → ℕ)
    (budget : NodeStatement → NodeWitness → ℕ) : Prop where
  /-- B1 (group 7: `main`'s completeness at the bump allocator's `HeapBuf` pointers), agent T
  (`Program.Rel.tree`, and the discharge of `Honest`): a call tree of `main`, honest with the
  statement's digest as `main`'s header, of cost within the node's budget. -/
  honest : ∀ seed s w, NodeRel bytecode seed s w → Limits s w → CapsAgree seed w →
    budget s w ≤ 2 ^ 28 →
    ∃ (rd : Reader) (T : Memory.Tree), T.name = "main" ∧
      Memory.HonestAt coreProgram fs H C (hdrOf (statementDigest seed s)) T cert rd [] [] ∧
      cost T ≤ budget s w
  /-- Agent T: `main`'s cells hold its jump table. -/
  table : ∀ (I : Memory.Inst) σ bufs kids, I.t = .node "main" σ bufs kids → Memory.tableCells ⊆ C I
  /-- B2 (checker K: `exec_complete`, the certificates, `returns_induction`): on the honest
  memory, `main` runs from its entry at `fp = 1` to the halting registers. -/
  b2 : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    Memory.HonestAt coreProgram fs H C hdr T cert rd [] [] →
      Reach guest (Memory.honest coreProgram fs H C hdr T) ⟨gpow mainEntry, 1⟩ (Regs.final guest)
  /-- B2 (checker K, counting): a halting run on the honest memory commits at most the tree's
  cost. -/
  size : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    Memory.HonestAt coreProgram fs H C hdr T cert rd [] [] → ∀ n,
      run guest (Memory.honest coreProgram fs H C hdr T) n Regs.initial = some (Regs.final guest) →
        (⟨_, Memory.honest coreProgram fs H C hdr T, n⟩ : Trace guest).committedSize ≤ cost T

/-- **Completeness**, the statement: a witness of `NodeRel` within the deployed limits, its
children's openings agreeing in the caps and the node within the budget, gives a valid execution of the guest on the statement's digest within the
verifier's committed size. -/
def GuestComplete (budget : NodeStatement → NodeWitness → ℕ) : Prop :=
  ∀ seed s w, NodeRel bytecode seed s w → Limits s w → CapsAgree seed w → budget s w ≤ 2 ^ 28 →
    ∃ t : Trace guest, ValidExecution guest (publicInputOf (statementDigest seed s)) t ∧
      t.committedSize ≤ 2 ^ 28

/-- **Completeness within a linear budget**, the final statement's form. -/
abbrev GuestCompleteWithin (b : Budget) : Prop := GuestComplete fun s w ↦ b.size (work s w)

/-- **What completeness within the budget `b` rests on**: `CompletePieces` with the size split
at the instruction counts `cnt T op` of a call tree, the run's against the tree's and the tree's
against the budget. -/
structure CompletePiecesWithin (fs : String → ℕ) (H : Memory.Inst → ℕ → E × E)
    (C : Memory.Inst → List (ℕ × E)) (cert : String → V → ℕ) (cnt : Memory.Tree → Opcode → ℕ)
    (b : Budget) : Prop where
  /-- B1 (group 7), agent T: as `CompletePieces.honest`, the tree within the budget's words and
  instruction counts. -/
  honest : ∀ seed s w, NodeRel bytecode seed s w → Limits s w → CapsAgree seed w →
    b.size (work s w) ≤ 2 ^ 28 →
    ∃ (rd : Reader) (T : Memory.Tree), T.name = "main" ∧
      Memory.HonestAt coreProgram fs H C (hdrOf (statementDigest seed s)) T cert rd [] [] ∧
      T.total fs ≤ b.words.eval (work s w) ∧ ∀ op, cnt T op ≤ (b.instrs op).eval (work s w)
  /-- Agent T: `main`'s cells hold its jump table. -/
  table : ∀ (I : Memory.Inst) σ bufs kids, I.t = .node "main" σ bufs kids → Memory.tableCells ⊆ C I
  /-- B2 (checker K): as `CompletePieces.b2`. -/
  b2 : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    Memory.HonestAt coreProgram fs H C hdr T cert rd [] [] →
      Reach guest (Memory.honest coreProgram fs H C hdr T) ⟨gpow mainEntry, 1⟩ (Regs.final guest)
  /-- B2 (checker K, counting): a halting run on the honest memory executes at most the tree's
  instructions of each opcode. -/
  count : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    Memory.HonestAt coreProgram fs H C hdr T cert rd [] [] → ∀ n,
      run guest (Memory.honest coreProgram fs H C hdr T) n Regs.initial = some (Regs.final guest) →
        ∀ op, (⟨_, Memory.honest coreProgram fs H C hdr T, n⟩ : Trace guest).count op ≤ cnt T op

theorem CompletePiecesWithin.pieces {fs : String → ℕ} {H : Memory.Inst → ℕ → E × E}
    {C : Memory.Inst → List (ℕ × E)} {cert : String → V → ℕ} {cnt : Memory.Tree → Opcode → ℕ}
    {b : Budget} (h : CompletePiecesWithin fs H C cert cnt b) :
    CompletePieces fs H C cert (fun T ↦ sizeOf (T.total fs) (cnt T)) fun s w ↦ b.size (work s w) where
  honest seed s w hrel hlim hcap hb := by
    obtain ⟨rd, T, hname, hH, hw, hc⟩ := h.honest seed s w hrel hlim hcap hb
    exact ⟨rd, T, hname, hH, sizeOf_mono hw hc⟩
  table := h.table
  b2 := h.b2
  size hdr rd T hname hH n hrun := by
    rw [committedSize_eq]
    exact sizeOf_mono le_rfl (h.count hdr rd T hname hH n hrun)

/-- The honest memory holds the jump table. -/
theorem jumpTables_honest {fs : String → ℕ} {H : Memory.Inst → ℕ → E × E}
    {C : Memory.Inst → List (ℕ × E)} {hdr : E × E} {T : Memory.Tree} {rd : Reader}
    (hH : Memory.Honest coreProgram fs H C hdr T rd [] []) (hname : T.name = "main")
    (htable : ∀ (I : Memory.Inst) σ bufs kids, I.t = .node "main" σ bufs kids → Memory.tableCells ⊆ C I) :
    JumpTables (Memory.honest coreProgram fs H C hdr T) := by
  intro q hq
  obtain ⟨I, hI, hIt, hfp, -⟩ := Memory.root_inst (fs := fs) (H := H) (hdr := hdr) (T := T)
  have hC : (q.1, q.2) ∈ C I := by
    have hv := hH.valid
    cases T with
    | node f σ bufs kids =>
      simp only [Memory.Tree.name] at hname
      exact htable I σ bufs kids (by rw [hIt, hname]) hq
    | phantom => exact (hv : False).elim
  have := hH.read_C hI hC
  rwa [hfp, gpow, pow_zero, one_mul] at this

/-- **Completeness, from its pieces.** -/
theorem guest_complete_of {fs : String → ℕ} {H : Memory.Inst → ℕ → E × E}
    {C : Memory.Inst → List (ℕ × E)} {cert : String → V → ℕ} {cost : Memory.Tree → ℕ}
    {budget : NodeStatement → NodeWitness → ℕ} (h : CompletePieces fs H C cert cost budget) :
    GuestComplete budget := fun seed s w hrel hlim hcap hbudget ↦ by
  obtain ⟨rd, T, hname, hH, hcost⟩ := h.honest seed s w hrel hlim hcap hbudget
  have hb := hH.toHonest.publicBoundary (prog := guest)
  have hreach := (reach_jumpTables (jumpTables_honest hH.toHonest hname h.table)).trans (h.b2 _ rd T hname hH)
  obtain ⟨n, hv⟩ := validExecution_of_reach hb hreach
  exact ⟨_, hv, (h.size _ rd T hname hH n hv.2).trans (hcost.trans hbudget)⟩

/-- **Completeness within the budget `b`, from its pieces.** -/
theorem guest_complete_within {fs : String → ℕ} {H : Memory.Inst → ℕ → E × E}
    {C : Memory.Inst → List (ℕ × E)} {cert : String → V → ℕ} {cnt : Memory.Tree → Opcode → ℕ}
    {b : Budget} (h : CompletePiecesWithin fs H C cert cnt b) : GuestCompleteWithin b :=
  guest_complete_of h.pieces

/-! ## Composition with the protocol -/

/-- **The guest's soundness in the random-oracle experiment**: for an adversary of at most `Q`
queries, the verifier accepts a statement whose program is the guest and whose public input is
the digest of no statement of the guest's shape that a witness holds with probability at most
`soundnessError Q` (`knowledgeSoundness_holds` and `guest_sound_input`). For an aggregate's
adversary, whose statement is `(guest, publicInputOf (statementDigest (fiatShamirIv bytecode)
s))`, the program's conjunct holds of every outcome and the public input's digest is
`statementDigest (fiatShamirIv bytecode) s` (`publicDigest_publicInputOf`). -/
theorem aggregate_sound_of (h : SoundPieces B) {A : Adversary} {Q : ℕ}
    (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment A}[z.1.2 = true ∧ z.1.1.1.1 = guest ∧
      ¬ ∃ seed s, statementDigest seed s = publicDigest z.1.1.1.2 ∧ s.defer.Shaped bytecode ∧
        NodeSpec bytecode seed s] ≤ soundnessError Q := by
  obtain ⟨extract, hks⟩ := knowledgeSoundness_holds
  refine le_trans (prEvent_mono _ _ _ ?_) (hks A Q hA)
  rintro ⟨⟨⟨⟨prog, input⟩, π⟩, b⟩, c⟩ ⟨hb, hprog, hno⟩
  dsimp only at hb hprog hno
  subst hprog
  refine ⟨hb, guest_sentinelSafe, ?_⟩
  rintro ⟨t, -, hv⟩
  exact hno (guest_sound_input h input t hv)

/-- **The guest's completeness in the random-oracle experiment**: within the limits and the
budget, there is an execution of the guest on the statement's digest whose honest proof, at an
inverse rate `2^ρ`, `1 ≤ ρ ≤ 4`, and a fuel of at most `2^64` nonces, the verifier rejects with
probability at most `completenessError fuel` (`LeanVM.completeness`). -/
theorem aggregate_complete_of {fs : String → ℕ} {H : Memory.Inst → ℕ → E × E}
    {C : Memory.Inst → List (ℕ × E)} {cert : String → V → ℕ} {cost : Memory.Tree → ℕ}
    {budget : NodeStatement → NodeWitness → ℕ} (h : CompletePieces fs H C cert cost budget)
    {seed : Digest} {s : NodeStatement} {w : NodeWitness} (hrel : NodeRel bytecode seed s w)
    (hlim : Limits s w) (hcap : CapsAgree seed w) (hbudget : budget s w ≤ 2 ^ 28) :
    ∃ t : Trace guest, ValidExecution guest (publicInputOf (statementDigest seed s)) t ∧
      ∀ ρ fuel, 1 ≤ ρ ∧ ρ ≤ 4 → fuel ≤ 2 ^ 64 →
        Pr{let z ← experiment (honestProver guest (publicInputOf (statementDigest seed s)) t ρ fuel)}[
          z.1.2 = false] ≤ completenessError fuel := by
  obtain ⟨t, hv, hsize⟩ := guest_complete_of h seed s w hrel hlim hcap hbudget
  exact ⟨t, hv, fun _ _ hρ hfuel ↦ completeness hv hsize hρ hfuel⟩

end
end LeanVM.Guest.End
