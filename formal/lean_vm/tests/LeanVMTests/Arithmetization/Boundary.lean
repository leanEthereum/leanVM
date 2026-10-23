import LeanVM.Arithmetization.Boundary

/-!
# Tests: the boundary blocks

A classic test for kernel evaluation: the fixtures decide `E` arithmetic in the kernel. One
prover data serves the three blocks, a four-word image (`κ = 2`) read through `imageOf` at
literal indices as in the channel and table tests, beside a two-slot program `bProg` (`logSize =
1`), a `Program` value: the program is public and no table of the data.

The three components are pinned to the Rust blocks (`layout.rs:351-394`) as data: each is a
push at count `1` and a pull at the finalize count, on its channel pair, with the pull's
multiplicity `-1` and its guarantee assumed; the verifier of a program has no local witness (the
`verifier_length_zero` field of `leanIsaEnsemble`), is complete for every public input, and
pulls the program's sentinel as a constant, `g^1` for the fixture's two-slot program.
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
changed opcode and a counter past the program are accepted by the block, whose `Spec` names no
program, and rejected by `BytecodeBindings bProg`, where `BytecodeRowsAreTheProgram` rejects
the witness.
-/

namespace LeanVMTests.Arithmetization.Boundary

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization

/-! ## The fixture: four words, two slots -/

/-- The image: four words, `κ = 2`. -/
def memWords : Array (Vector K 3) := #[#v[1, K.ofBits 2, K.ofBits 3], #v[K.ofBits 4, K.ofBits 5, K.ofBits 6], #v[K.ofBits 7, K.ofBits 8, K.ofBits 9], #v[0, 0, 0]]

/-- The program: an `XOR` and a `JUMP`, `logSize = 1`, a `Program` value (public, not data). -/
def bProg : Program := ⟨1, by decide, ![.xor (gpow 2) (gpow 3) (gpow 4), .jump 1 1 1]⟩

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
    (imageOf bData).2.read (gpow k) = some (E.ofLimbs v[0] v[1] v[2]) := by
  have hk' : k < 2 ^ (imageOf bData).1 := by rw [bData_logSize]; omega
  rw [show gpow k = gpow ((⟨k, hk'⟩ : Fin (2 ^ (imageOf bData).1)) : ℕ) from rfl,
    MemImage.read_gpow (by rw [bData_logSize]; decide), imageOf_apply bData_wellShaped _ hv]

/-- The instruction at `g^i` of the fixture's program. -/
theorem fetch_at (i : ℕ) (ins : Instr) (hi : i < 2 ^ bProg.logSize := by decide)
    (hd : bProg.code ⟨i, hi⟩ = ins := by rfl) : bProg.fetch (gpow i) = some ins := by
  rw [show gpow i = gpow ((⟨i, hi⟩ : Fin (2 ^ bProg.logSize)) : ℕ) from rfl,
    Program.fetch_gpow, hd]

/-! ## The three blocks are their flushes (`layout.rs:351-394`) -/

/-- The memory block: the seed push at count `1`, the finalize pull at `cntFin`, on the memory
pair. -/
example (r : Var MemRow K) : (memTable.main r).operations 0 =
    [.interact ⟨MemPush.toRaw, 1, toElements (⟨r.idx, 1, r.m⟩ : MemMsg (Expression K)), false⟩,
     .interact ⟨MemPull.toRaw, -1, toElements (⟨r.idx, r.cntFin, r.m⟩ : MemMsg (Expression K)),
       true⟩] :=
  rfl

/-- The bytecode block, likewise, on the bytecode pair. -/
example (r : Var BytecodeRow K) : (bytecodeTable.main r).operations 0 =
    [.interact ⟨BytecodePush.toRaw, 1,
       toElements (⟨r.idx, 1, r.opcode, r.op⟩ : BytecodeMsg (Expression K)), false⟩,
     .interact ⟨BytecodePull.toRaw, -1,
       toElements (⟨r.idx, r.cntFin, r.opcode, r.op⟩ : BytecodeMsg (Expression K)), true⟩] :=
  rfl

/-- The verifier of `prog`: push `(1, 1)`, pull `(prog.finalPc, 1)`, both constants, on the state
pair (specification §6.1; `layout.rs:353-357`). -/
example (prog : Program) (pi : Var PublicIO K) : ((leanIsaVerifier prog).main pi).operations 0 =
    [.interact ⟨StatePush.toRaw, 1, toElements (⟨1, 1⟩ : Regs (Expression K)), false⟩,
     .interact ⟨StatePull.toRaw, -1,
       toElements (⟨Expression.const prog.finalPc, 1⟩ : Regs (Expression K)), true⟩] :=
  rfl

/-- The seed count is the word `1 = g^0`. -/
example (env : Environment K) : Expression.eval env (1 : Expression K) = gpow 0 := by
  simp only [circuit_norm]; rfl

/-- The verifier has no local witness: the `verifier_length_zero` field of `leanIsaEnsemble`. -/
example (prog : Program) (pi : Var PublicIO K) : (leanIsaVerifier prog).localLength pi = 0 := by
  simp only [circuit_norm, leanIsaVerifier]

/-- The verifier is complete for every program and public input over every data. -/
example (prog : Program) (pi : PublicIO K) (data : ProverData K) :
    ConstraintsHold.Completeness (rowEnv data)
      (((leanIsaVerifier prog).main (const pi)).operations 0) :=
  ((leanIsaVerifier prog).completeness 0 (rowEnv data) (const pi)
    (by simp only [circuit_norm, leanIsaVerifier, -BitVec.reduceNeg]) pi
    ProvableType.eval_const_prover trivial).1

/-- The two boundary states are the run's: `(1, 1)`, and `(g^(N_prog - 1), 1)`, which is
`(g^1, 1)` for the fixture's two-slot program. -/
example (env : Environment K) : eval env (⟨1, 1⟩ : Regs (Expression K)) = Regs.initial :=
  verifier_push_eval env

example (env : Environment K) :
    eval env (⟨Expression.const bProg.finalPc, 1⟩ : Regs (Expression K)) = ⟨gpow 1, 1⟩ := by
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
def memRow1 : MemRow K := ⟨gpow 1, gpow 3, #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]⟩

/-- The honest row is bound to the image. -/
theorem memRow1_spec : MemSpec memRow1 bData := ⟨read_at 1 #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]⟩

/-- Nothing checks the finalize count (specification §6.2): the same row with count `0` is
bound too. -/
example : MemSpec { memRow1 with cntFin := 0 } bData := ⟨read_at 1 #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]⟩

/-- The row `memRowOf` builds from the image is the honest row. -/
example : memRowOf (imageOf bData).2 ⟨1, by rw [bData_logSize]; decide⟩ (gpow 3) = memRow1 := by
  rw [memRowOf, imageOf_apply bData_wellShaped _ (v := #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]) (by decide +kernel)]
  simp only [limb_ofLimbs]
  rfl

/-- Every word of the image has a satisfying seed row from the image alone
(`mem_word_complete`), with any count: word `1` at `g^3`, word `3` at `0`. -/
example : ConstraintsHold.Completeness (rowEnv bData)
    ((memTable.main (const (memRowOf (imageOf bData).2 ⟨1, by rw [bData_logSize]; decide⟩
      (gpow 3)))).operations 0) :=
  mem_word_complete _ _

example : ConstraintsHold.Completeness (rowEnv bData)
    ((memTable.main (const (memRowOf (imageOf bData).2 ⟨3, by rw [bData_logSize]; decide⟩
      0))).operations 0) :=
  mem_word_complete _ _

/-- A changed limb: the row is no word of the image, so it is not bound … -/
def memRow1' : MemRow K := { memRow1 with m := #v[K.ofBits 4, K.ofBits 5, K.ofBits 7] }

theorem memRow1'_not_spec : ¬ MemSpec memRow1' bData := by
  rintro ⟨h⟩
  rw [show memRow1'.idx = gpow 1 from rfl, read_at 1 #v[K.ofBits 4, K.ofBits 5, K.ofBits 6]] at h
  exact absurd (Option.some.inj h) (by decide +kernel)

/-- … and the constraints `main` emits on it fail in every environment over the data: its pull
is no read of the image (`soundness`, read back). -/
example (get : ℕ → K) :
    ¬ ConstraintsHold.Soundness ⟨get, bData⟩ ((memTable.main (const memRow1')).operations 0) :=
  fun h ↦ memRow1'_not_spec
    (memTable.soundness 0 ⟨get, bData⟩ (const memRow1') memRow1' ProvableType.eval_const
      trivial h).1

/-- The address `0` is no address: a row there is bound to nothing. -/
example (cntFin : K) (m : Vector K 3) : ¬ MemSpec ⟨0, cntFin, m⟩ bData := by
  rintro ⟨h⟩
  rw [MemImage.read_zero] at h
  cases h

/-- An address past the image, `g^4` at `κ = 2`, is no address either. -/
example (cntFin : K) (m : Vector K 3) : ¬ MemSpec ⟨gpow 4, cntFin, m⟩ bData := by
  rintro ⟨h⟩
  rw [MemImage.read, gLog?_gpow_eq_none (by rw [bData_logSize]; decide) (by decide),
    Option.map_none] at h
  cases h

/-! ## The bytecode block -/

/-- The honest seed row of slot `0`: the `XOR` entry, executed twice. -/
def bcRow0 : BytecodeRow K :=
  ⟨gpow 0, gpow 2, Opcode.xor.code, #v[gpow 2, gpow 3, gpow 4, 0, 0, 0, 0]⟩

/-- The honest row decodes: the block's `Spec`, over no data. -/
theorem bcRow0_decodes : BytecodeDecodes bcRow0 :=
  ⟨.xor (gpow 2) (gpow 3) (gpow 4), by decide +kernel⟩

/-- … and is the program's: its entry is the instruction fetched at its counter, the per-row
reading of `BytecodeRowsAreTheProgram`, which the block does not state. -/
theorem bcRow0_bindings : BytecodeBindings bProg bcRow0 :=
  ⟨_, fetch_at 0 (.xor (gpow 2) (gpow 3) (gpow 4)), by decide +kernel⟩

/-- The two slot indices of the fixture's program. -/
theorem slot0_lt : 0 < 2 ^ bProg.logSize := by decide
theorem slot1_lt : 1 < 2 ^ bProg.logSize := by decide

/-- The row `bytecodeRowOf` builds from the program is the honest row, and slot `1` gives the
`JUMP` entry with its four spare slots zero: the block's rows are a function of the program,
the finalize count aside. -/
example : bytecodeRowOf bProg ⟨0, slot0_lt⟩ (gpow 2) = bcRow0 := rfl

example : bytecodeRowOf bProg ⟨1, slot1_lt⟩ 1 =
    ⟨gpow 1, 1, Opcode.jump.code, #v[1, 1, 1, 0, 0, 0, 0]⟩ :=
  rfl

/-- Every slot of the program has a satisfying seed row from the program alone
(`bytecode_entry_complete`), with any count, over any data. -/
example : ConstraintsHold.Completeness (rowEnv bData)
    ((bytecodeTable.main (const (bytecodeRowOf bProg ⟨0, slot0_lt⟩ (gpow 2)))).operations 0) :=
  bytecode_entry_complete bProg _ _

example (data : ProverData K) : ConstraintsHold.Completeness (rowEnv data)
    ((bytecodeTable.main (const (bytecodeRowOf bProg ⟨1, slot1_lt⟩ 0))).operations 0) :=
  bytecode_entry_complete bProg _ _

/-- A changed opcode: the row still decodes, so the block accepts it, its `Spec` naming no
program (leanVM's block carries the program as public columns it does not check) … -/
def bcRow0' : BytecodeRow K := { bcRow0 with opcode := Opcode.mulNative.code }

example : BytecodeDecodes bcRow0' :=
  ⟨.mulNative (gpow 2) (gpow 3) (gpow 4), by decide +kernel⟩

/-- … and it is not the program's: `BytecodeBindings bProg` rejects it, which is where
`BytecodeRowsAreTheProgram` rejects the witness, never the block. -/
theorem bcRow0'_not_bound : ¬ BytecodeBindings bProg bcRow0' := by
  rintro ⟨ins, hfetch, hdec⟩
  rw [show bcRow0'.idx = gpow 0 from rfl, fetch_at 0 (.xor (gpow 2) (gpow 3) (gpow 4))] at hfetch
  obtain rfl := Option.some.inj hfetch
  exact absurd hdec (by decide +kernel)

/-- A nonzero spare slot is no instruction: the row decodes to
nothing, fails the block's `Spec` … -/
def bcRow0'' : BytecodeRow K := { bcRow0 with op := #v[gpow 2, gpow 3, gpow 4, 0, 0, 0, 1] }

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
example (cntFin opcode : K) (op : Vector K 7) :
    ¬ BytecodeBindings bProg ⟨gpow 2, cntFin, opcode, op⟩ := by
  rintro ⟨ins, hfetch, -⟩
  rw [Program.fetch, gLog?_gpow_eq_none (by decide) (by decide), Option.map_none] at hfetch
  cases hfetch

end LeanVMTests.Arithmetization.Boundary
