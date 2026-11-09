import LeanVM.Arithmetization.Boundary

/-!
# Tests: the boundary blocks

A classic test for kernel evaluation: the fixtures decide `E` arithmetic in the kernel. One
prover data serves the three blocks, a four-word image (`κ = 2`) read through `imageOf` at
literal indices as in the channel and table tests, beside a two-slot program `bProg` (`logSize =
1`), a `Program` value: the program is public and no table of the data.

The three components are pinned to the Rust blocks (`layout.rs:429-472`) as data: each is a
push at count `1` and a pull at the finalize count, on its channel pair, the pull Clean's
direction `.pull` at multiplicity `1`; the verifier of a program is a `Verifier.Program`, whose
operations are its two interactions and nothing else (no witness), whose constraints hold for
every public input, and which pulls the program's sentinel as a constant, `g^1` for the
fixture's two-slot program. The two blocks are preallocated components: the memory block's
`2^κ` rows with the index column fixed to `g^i` (`memMode_fixedAt`), the bytecode block's
`2^N` rows with the counter and the entry fixed to the program's (`bytecodeMode_fixedAt`), each
named so that Clean derives the prover data from its rows (`"mem"`, `"bytecode"`).
`PublicIO` flattens to the four lanes.

For the two seed blocks: the honest row of a word is bound (`MemSpec`), the honest row of a
slot decodes (`BytecodeDecodes`, the block's `Spec`) and is the program's (`BytecodeBindings
bProg`, the per-row reading of `BytecodeRowsAreTheProgram`, unstated by the block), and the row
`memRowOf`/`bytecodeRowOf` builds from the image or the program alone is the honest row and
satisfies the constraints `main` emits (`mem_word_complete`, `bytecode_entry_complete`), with
any finalize count, `0` included, since nothing checks the finalize counts (specification
§6.2). Rejections use actual rows and the blocks' own theorems: a changed limb, the address `0`
and an address past the image fail `MemSpec` and hence the constraints in
every environment over the data (read back through `soundness`); a nonzero spare slot
fails `BytecodeDecodes` the same way, over any data; a
changed opcode and a counter past the program are accepted by the block's circuit, whose `Spec`
names no program, and rejected by `BytecodeBindings bProg`, which the block's fixed columns
enforce (`bytecodeMode_fixedAt`, tested last).
-/

namespace LeanVMTests.Arithmetization.Boundary

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization

/-! ## The fixture: four words, two slots -/

/-- The image: four words, `κ = 2`. -/
def memWords : Array (Vector K 3) := #[#v[1, K.ofBits 2, K.ofBits 3], #v[K.ofBits 4, K.ofBits 5, K.ofBits 6], #v[K.ofBits 7, K.ofBits 8, K.ofBits 9], #v[0, 0, 0]]

/-- The program: an `XOR` and a `JUMP`, `logSize = 1`, a `Program` value (public, not data). -/
def bProg : LeanIsaProgram := ⟨1,
    by decide, ![.xor (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4), .jump 1 1 1]⟩

/-- The prover data, its one table matched on arity so that the kernel never compares names
(as in the channel and table tests). -/
def bData : ProverData K := fun _ n ↦
  match n with
  | 3 => memWords
  | _ => #[]

theorem bData_logSize : (imageOf bData).1 = 2 := by
  show min (Nat.log 2 (memRows bData).size) maxLogMem = 2
  rw [show (memRows bData).size = 4 from rfl, show (4 : ℕ) = 2 ^ 2 by decide,
    Nat.log_pow (by norm_num)]
  decide

theorem bData_wellShaped : WellShapedData bData where
  memRows_size := by rw [bData_logSize]; rfl

/-- The word at `g^k` of the fixture's image, as limbs. -/
theorem read_at (k : ℕ) (v : Vector K 3) (hk : k < 4 := by decide)
    (hv : memWords[k]'(by rw [show memWords.size = 4 from rfl]; exact hk) = v :=
      by decide +kernel) :
    (imageOf bData).2.read (addressOfIndex k) = some (E.ofLimbs v[0] v[1] v[2]) := by
  have hk' : k < 2 ^ (imageOf bData).1 := by rw [bData_logSize]; omega
  rw [show addressOfIndex k = addressOfIndex ((⟨k, hk'⟩ : Fin (2 ^ (imageOf bData).1)) : ℕ)
      from rfl,
    MemoryImage.read_gpow (by rw [bData_logSize]; decide), imageOf_apply bData_wellShaped _ hv]

/-- The instruction at `g^i` of the fixture's program. -/
theorem fetch_at (i : ℕ) (ins : LeanIsaInstruction) (hi : i < 2 ^ bProg.logSize := by decide)
    (hd : bProg.instructions ⟨i, hi⟩ = ins :=
        by rfl) : bProg.fetch (addressOfIndex i) = some ins := by
  rw [show addressOfIndex i = addressOfIndex ((⟨i, hi⟩ : Fin (2 ^ bProg.logSize)) : ℕ) from rfl,
    LeanIsaProgram.fetch_gpow, hd]

/-! ## The three blocks are their flushes (`layout.rs:429-472`) -/

/-- The memory block: the seed push at count `1`, the finalize pull at `cntFin`, on the memory
pair; the row's limbs come first (`⟨m, idx, cntFin⟩`), as the committed columns do. -/
example (r : Var MemRow K) : (memTable.main r).operations 0 =
    [.interact ⟨MemPush.toRaw, .push, 1, toElements (⟨r.idx, 1, r.m⟩ : MemMsg (Expression K))⟩,
     .interact ⟨MemPull.toRaw, .pull, 1, toElements (⟨r.idx, r.cntFin, r.m⟩ : MemMsg (Expression K))⟩] :=
  rfl

/-- The bytecode block, likewise, on the bytecode pair. -/
example (r : Var BytecodeRow K) : (bytecodeTable.main r).operations 0 =
    [.interact ⟨BytecodePush.toRaw, .push, 1,
       toElements (⟨r.idx, 1, r.opcode, r.op⟩ : BytecodeMsg (Expression K))⟩,
     .interact ⟨BytecodePull.toRaw, .pull, 1,
       toElements (⟨r.idx, r.cntFin, r.opcode, r.op⟩ : BytecodeMsg (Expression K))⟩] :=
  rfl

/-- The verifier of `prog`: push `(1, 1)`, pull `(prog.pcFinal, 1)`, both constants, on the state
pair (specification §6.1; `layout.rs:431-435`). -/
example (prog : LeanIsaProgram) (pi : Var PublicIO K) :
    ((leanIsaVerifier prog).main pi).operations.interactions =
    [⟨StatePush.toRaw, .push, 1, toElements (⟨1, 1⟩ : Registers (Expression K))⟩,
     ⟨StatePull.toRaw, .pull, 1,
       toElements (⟨Expression.const prog.pcFinal, 1⟩ : Registers (Expression K))⟩] :=
  rfl

/-- The seed count is the word `1 = g^0`. -/
example (env : Environment K) : Expression.eval env (1 : Expression K) = addressOfIndex 0 := by
  simp only [circuit_norm]; rfl

/-- The verifier has no local witness: its circuit operations, the two interactions, allocate
no cell. -/
example (prog : LeanIsaProgram) (pi : Var PublicIO K) :
    Operations.localLength ((leanIsaVerifier prog).main pi).circuitOperations = 0 := by
  simp only [circuit_norm, leanIsaVerifier]

/-- The verifier's constraints hold for every program and public input over every data. -/
example (prog : LeanIsaProgram) (pi : PublicIO K) (data : ProverData K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((leanIsaVerifier prog).main (const pi)).circuitOperations := by
  simp only [circuit_norm, leanIsaVerifier, StatePull, -BitVec.reduceNeg]

/-- The two boundary states are the run's: `(1, 1)`, and `(g^(N_prog - 1), 1)`, which is
`(g^1, 1)` for the fixture's two-slot program. -/
example (env : Environment K) : eval env (⟨1, 1⟩ : Registers (Expression K)) = Registers.initial :=
  verifier_push_eval env

example (env : Environment K) :
    eval env (⟨Expression.const bProg.pcFinal, 1⟩ : Registers (Expression K)) = ⟨addressOfIndex 1,
        1⟩ := by
  rw [verifier_pull_eval]
  rfl

/-! ## The public input -/

-- The four lanes, and nothing else: the sentinel counter is the verifier's constant.
#guard (toElements (⟨#v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4]⟩ : PublicIO K)).toList = [1, K.ofBits 2, K.ofBits 3, K.ofBits 4]
#guard (toElements (PublicIO.ofInput ⟨![K.ofBits 7, K.ofBits 8, K.ofBits 9, K.ofBits 10]⟩)).toList = [K.ofBits 7, K.ofBits 8, K.ofBits 9, K.ofBits 10]

-- Four coordinates.
example : size PublicIO = 4 := rfl

/-! ## The memory block -/

/-- The honest seed row of word `1`: `(g^1, g^3, (4, 5, 6))`, read three times. -/
def memRow1 : MemRow K := ⟨#v[K.ofBits 4, K.ofBits 5, K.ofBits 6], addressOfIndex 1,
    addressOfIndex 3⟩

/-- The honest row is bound to the image. -/
theorem memRow1_spec : MemSpec memRow1 bData := ⟨read_at 1 #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]⟩

/-- Nothing checks the finalize count (specification §6.2): the same row with count `0` is
bound too. -/
example : MemSpec { memRow1 with cntFin := 0 } bData := ⟨read_at 1 #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]⟩

/-- The row `memRowOf` builds from the image is the honest row. -/
example : memRowOf (imageOf bData).2 ⟨1,
    by rw [bData_logSize]; decide⟩ (addressOfIndex 3) = memRow1 := by
  rw [memRowOf, imageOf_apply bData_wellShaped _ (v := #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]) (by decide +kernel)]
  simp only [limb_ofLimbs]
  rfl

/-- Every word of the image has a satisfying seed row from the image alone
(`mem_word_complete`), with any count: word `1` at `g^3`, word `3` at `0`. -/
example : ConstraintsHold.Completeness (rowEnv bData)
    ((memTable.main (const (memRowOf (imageOf bData).2 ⟨1, by rw [bData_logSize]; decide⟩
      (addressOfIndex 3)))).operations 0) :=
  mem_word_complete _ _

example : ConstraintsHold.Completeness (rowEnv bData)
    ((memTable.main (const (memRowOf (imageOf bData).2 ⟨3, by rw [bData_logSize]; decide⟩
      0))).operations 0) :=
  mem_word_complete _ _

/-- A changed limb: the row is no word of the image, so it is not bound … -/
def memRow1' : MemRow K := { memRow1 with m := #v[K.ofBits 4, K.ofBits 5, K.ofBits 7] }

theorem memRow1'_not_spec : ¬ MemSpec memRow1' bData := by
  rintro ⟨h⟩
  rw [show memRow1'.idx = addressOfIndex 1 from rfl, read_at 1 #v[K.ofBits 4, K.ofBits 5, K.ofBits
      6]] at h
  exact absurd (Option.some.inj h) (by decide +kernel)

/-- … and the constraints `main` emits on it fail in every environment over the data: its pull
is no read of the image (`soundness`, read back). -/
example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, bData⟩ ((memTable.main (const memRow1')).operations 0) :=
  fun h ↦ memRow1'_not_spec
    (memTable.soundness 0 ⟨get, bData⟩ (const memRow1') memRow1' ProvableType.eval_const
      trivial h).1

/-- The address `0` is no address: a row there is bound to nothing. -/
example (cntFin : K) (m : Vector K 3) : ¬ MemSpec ⟨m, 0, cntFin⟩ bData := by
  rintro ⟨h⟩
  rw [MemoryImage.read_zero] at h
  cases h

/-- An address past the image, `g^4` at `κ = 2`, is no address either. -/
example (cntFin : K) (m : Vector K 3) : ¬ MemSpec ⟨m, addressOfIndex 4, cntFin⟩ bData := by
  rintro ⟨h⟩
  rw [MemoryImage.read, gLog?_gpow_eq_none (by rw [bData_logSize]; decide) (by decide),
    Option.map_none] at h
  cases h

/-! ## The bytecode block -/

/-- The honest seed row of slot `0`: the `XOR` entry, executed twice. -/
def bcRow0 : BytecodeRow K :=
  ⟨addressOfIndex 0, addressOfIndex 2, Opcode.xor.busCode, #v[addressOfIndex 2, addressOfIndex 3,
      addressOfIndex 4, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- The honest row decodes: the block's `Spec`, over no data. -/
theorem bcRow0_decodes : BytecodeDecodes bcRow0 :=
  ⟨.xor (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4), by decide +kernel⟩

/-- … and is the program's: its entry is the instruction fetched at its counter, the per-row
reading of `BytecodeRowsAreTheProgram`, which the block does not state. -/
theorem bcRow0_bindings : BytecodeBindings bProg bcRow0 :=
  ⟨_, fetch_at 0 (.xor (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4)), by decide +kernel⟩

/-- The two slot indices of the fixture's program. -/
theorem slot0_lt : 0 < 2 ^ bProg.logSize := by decide
theorem slot1_lt : 1 < 2 ^ bProg.logSize := by decide

/-- The row `bytecodeRowOf` builds from the program is the honest row, and slot `1` gives the
`JUMP` entry with its nine spare slots zero: the block's rows are a function of the program,
the finalize count aside. -/
example : bytecodeRowOf bProg ⟨0, slot0_lt⟩ (addressOfIndex 2) = bcRow0 := rfl

example : bytecodeRowOf bProg ⟨1, slot1_lt⟩ 1 =
    ⟨addressOfIndex 1, 1, Opcode.jump.busCode, #v[1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ :=
  rfl

/-- Every slot of the program has a satisfying seed row from the program alone
(`bytecode_entry_complete`), with any count, over any data. -/
example : ConstraintsHold.Completeness (rowEnv bData)
    ((bytecodeTable.main (const (bytecodeRowOf bProg ⟨0, slot0_lt⟩ (addressOfIndex
        2)))).operations 0) :=
  bytecode_entry_complete bProg _ _

example (data : ProverData K) : ConstraintsHold.Completeness (rowEnv data)
    ((bytecodeTable.main (const (bytecodeRowOf bProg ⟨1, slot1_lt⟩ 0))).operations 0) :=
  bytecode_entry_complete bProg _ _

/-- A changed opcode: the row still decodes, so the block accepts it, its `Spec` naming no
program (leanVM's block carries the program as public columns it does not check) … -/
def bcRow0' : BytecodeRow K := { bcRow0 with opcode := Opcode.mulNative.busCode }

example : BytecodeDecodes bcRow0' :=
  ⟨.mulNative (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4), by decide +kernel⟩

/-- … and it is not the program's: `BytecodeBindings bProg` rejects it, as the block's fixed entry
columns do (below), never its circuit. -/
theorem bcRow0'_not_bound : ¬ BytecodeBindings bProg bcRow0' := by
  rintro ⟨ins, hfetch, hdec⟩
  rw [show bcRow0'.idx = addressOfIndex 0 from rfl, fetch_at 0 (.xor (addressOfIndex 2)
      (addressOfIndex 3) (addressOfIndex 4))] at hfetch
  obtain rfl := Option.some.inj hfetch
  exact absurd hdec (by decide +kernel)

/-- A nonzero spare slot is no instruction: the row decodes to
nothing, fails the block's `Spec` … -/
def bcRow0'' : BytecodeRow K := { bcRow0 with op := #v[addressOfIndex 2, addressOfIndex 3, addressOfIndex 4, 0, 0, 0, 0, 0, 0, 0, 0,
  1] }

theorem bcRow0''_not_decodes : ¬ BytecodeDecodes bcRow0'' := by
  rintro ⟨ins, hdec⟩
  rw [show decode (#v[bcRow0''.opcode] ++ bcRow0''.op) = none by decide +kernel] at hdec
  cases hdec

/-- … and so the constraints `main` emits on it fail in every environment over any data
(`soundness`, read back). -/
example (get : ℕ → K) (data : ProverData K) :
    ¬ ConstraintsHold.Soundness ⟨get, data⟩
      ((bytecodeTable.main (const bcRow0'')).operations 0) :=
  fun h ↦ bcRow0''_not_decodes
    (bytecodeTable.soundness 0 ⟨get, data⟩ (const bcRow0'') bcRow0'' ProvableType.eval_const
      trivial h).1

/-- A counter past the program, `g^2` at `logSize = 1`, fetches nothing: the row is no slot of
the program, whatever its entry, though the block accepts a decodable one. -/
example (cntFin opcode : K) (op : Vector K 12) :
    ¬ BytecodeBindings bProg ⟨addressOfIndex 2, cntFin, opcode, op⟩ := by
  rintro ⟨ins, hfetch, -⟩
  rw [LeanIsaProgram.fetch, gLog?_gpow_eq_none (by decide) (by decide), Option.map_none] at hfetch
  cases hfetch

/-! ## The blocks as preallocated components -/

/-- The blocks are named for the prover data Clean derives from their rows: the memory block's
rows are the `"mem"` table that `imageOf` reads. -/
example : (memComponent 2).circuit.name = memDataName := rfl
example : (bytecodeComponent bProg).circuit.name = "bytecode" := rfl

/-- The memory block of `κ = 2` has four rows, the bytecode block of the two-slot program two. -/
example : (memMode 2).height = 4 := rfl
example : (bytecodeMode bProg).height = 2 := rfl

/-- Row `1` of the memory block is fixed to the address `g^1`: the honest row agrees with it, the
same row at `g^2` does not. -/
example : (memMode 2).FixedAt 1 memRow1 := (memMode_fixedAt (by decide) _).mpr rfl

example : ¬ (memMode 2).FixedAt 1 { memRow1 with idx := addressOfIndex 2 } := fun h ↦
  absurd ((memMode_fixedAt (by decide) _).mp h) (by decide +kernel)

/-- Row `0` of the bytecode block is fixed to the program's slot `0`: the honest row agrees with
it, the row with a changed opcode does not, which is where the block now rejects it. -/
example : (bytecodeMode bProg).FixedAt 0 bcRow0 :=
  (bytecodeMode_fixedAt bProg (by decide) _).mpr rfl

example : ¬ (bytecodeMode bProg).FixedAt 0 bcRow0' := fun h ↦
  absurd (congrArg BytecodeRow.opcode ((bytecodeMode_fixedAt bProg (by decide) _).mp h))
    (by decide +kernel)

end LeanVMTests.Arithmetization.Boundary
