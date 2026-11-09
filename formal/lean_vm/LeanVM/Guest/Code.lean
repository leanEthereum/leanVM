/-
  LeanVM.Guest.Code

  Compiled bytecode in offset form: instructions over `ℕ` frame offsets, compiled functions in
  chunks, their assembly into a `Program`, and the fetch lemma of an assembled program.
-/

module

public import LeanVM.Semantics.Lemmas
public import Statement.LeanIsa

/-!
# Offset-form bytecode

The compiler's `Op` (`crates/leanvm_core/src/cpu/isa.rs`) names a frame cell by its offset `o`,
whose bytecode slot is `g^o` (`crates/leanvm_core/src/cpu/layout.rs:292-362`), and holds a `SET`
immediate as three `u64` limbs. `OffsetInstruction` is that form, and
`OffsetInstruction.toLeanIsaInstruction` its meaning in
`Statement.LeanIsa`: the kernel never evaluates a power of `g`, which costs one multiplication per
unit of the exponent, because every offset stays a `ℕ` until `toLeanIsaInstruction` wraps it in
`gpow`.

A compiled function (`CompiledFn`) is its name, entry pc, length and code, the code in chunks of
`chunkSize` instructions so that no literal is too large to elaborate. `assemble` lays a list of
functions out as a `Program`, padding with `SET fp[0] = 0` as the compiler does
(`crates/lean_compiler/src/lib.rs`). When the functions are laid out one after another from pc
`0` (`consecutive`, decided once per program), `assemble_fetch` gives the instruction at every pc
of every function, by a proof that evaluates nothing but the one instruction asked for.

A `KECCAK`'s thirteen read cells are at the offsets `keccakIns` (`m0..m3`, the runs from `tail` and
`cap`, `b8`) and its one, two or thirteen written cells at `keccakOuts` (`out + k`, `k` below the
instruction's `outCells.cellCount`); `keccakInOffset_gpow` and
`keccakOutOffset_gpow` turn the instruction's addresses into these offsets.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## Instructions -/

/-- The frame offset of read cell `c < 13` of `OffsetInstruction.keccak m0 m1 m2 m3 tail b8 cap _`:
`m0, …, m3`, then `tail + k` (`k < 4`), `b8`, then `cap + k` (`k < 4`) (`keccakInputCellOffset` in offset
form, `keccakInOffset_gpow`). -/
def keccakInOff (m0 m1 m2 m3 tail b8 cap c : ℕ) : ℕ :=
  if c = 0 then m0 else if c = 1 then m1 else if c = 2 then m2 else if c = 3 then m3
  else if c < 8 then tail + (c - 4) else if c = 8 then b8 else cap + (c - 9)

/-- The frame offsets of the thirteen cells a `KECCAK` reads, in order. -/
def keccakIns (m0 m1 m2 m3 tail b8 cap : ℕ) : List ℕ :=
  (List.range 13).map (keccakInOff m0 m1 m2 m3 tail b8 cap)

/-- The frame offsets of the `n` cells a `KECCAK` writes, `out + k` (`k < n`, `n` its
`outCells.cellCount`). -/
def keccakOuts (out n : ℕ) : List ℕ := (List.range n).map (out + ·)

/-- Whether an instruction is a `JUMP`, the one that may not fall through. -/
def OffsetInstruction.isJump : OffsetInstruction → Bool
  | .jump .. => true
  | _ => false

/-! ## Compiled functions -/

/-- The code as one list. -/
def CompiledFunction.code (f : CompiledFunction) : List OffsetInstruction := f.chunks.flatten

/-- The chunks hold `n` instructions, `C` in each but the last. -/
def chunked (C : ℕ) : List (List OffsetInstruction) → ℕ → Bool
  | [], n => n == 0
  | c :: cs, n =>
      if n ≤ C then cs.isEmpty && c.length == n else c.length == C && chunked C cs (n - C)

/-- The chunks hold exactly the function's `len` instructions. -/
def CompiledFunction.WellChunked (f : CompiledFunction) : Prop := chunked chunkSize f.chunks
    f.instructionCount = true

/-! ## Assembly -/

/-- The functions are laid out one after another from pc `s`, ending at pc `e`. -/
def consecutive : ℕ → List CompiledFunction → ℕ → Bool
  | s, [], e => s == e
  | s, f :: fs, e => f.entryPc == s && consecutive (s + f.instructionCount) fs e

/-- `assemble` with its instructions computed once, into an array: the same program
(`assembleArray_eq`), for compiled code that reads every slot (`bytecodeWords` reads each sixteen
times), where `assemble` would look each slot up again. -/
def assembleArray (fns : List CompiledFunction) (logSize : ℕ) (h : logSize ≤ maxLogBytecode) :
    LeanIsaProgram :=
  let code : Array LeanIsaInstruction := Array.ofFn fun i : Fin (2 ^ logSize) ↦ (instructionAtPc fns
      i).toLeanIsaInstruction
  ⟨logSize, h, fun i ↦ code[i.val]'(by simp [code])⟩

theorem assembleArray_eq (fns : List CompiledFunction) (logSize : ℕ) (h : logSize ≤
    maxLogBytecode) :
    assembleArray fns logSize h = assemble fns logSize h := by
  simp [assembleArray, assemble]

/-! ## Lemmas -/

/-- `KECCAK`'s read offsets in offset form: read cell `c` of the instruction `toLeanIsaInstruction` gives is at
the frame offset `keccakInOff … c`. -/
theorem keccakInOffset_gpow (m0 m1 m2 m3 tail b8 cap : ℕ) (c : Fin 13) :
    keccakInputCellOffset ![addressOfIndex m0, addressOfIndex m1, addressOfIndex m2, addressOfIndex
        m3] (addressOfIndex tail) (addressOfIndex b8) (addressOfIndex cap) c =
      addressOfIndex (keccakInOff m0 m1 m2 m3 tail b8 cap c.val) := by
  fin_cases c <;> simp [keccakInputCellOffset, keccakInOff, addressOfIndex, ← pow_add, ← pow_succ',
      Nat.add_comm]

/-- `KECCAK`'s write offsets in offset form: written cell `k` is at `out + k`. -/
theorem keccakOutOffset_gpow (out k : ℕ) : g ^ k * addressOfIndex out = addressOfIndex (out +
    k) := by
  simp [addressOfIndex, ← pow_add, Nat.add_comm]

theorem keccakIns_eq (m0 m1 m2 m3 tail b8 cap : ℕ) :
    keccakIns m0 m1 m2 m3 tail b8 cap =
      [m0, m1, m2, m3, tail, tail + 1, tail + 2, tail + 3, b8, cap, cap + 1, cap + 2, cap + 3] := by
  simp [keccakIns, keccakInOff, List.range_succ]

theorem keccakIns_getD (m0 m1 m2 m3 tail b8 cap : ℕ) {c : ℕ} (hc : c < 13) :
    (keccakIns m0 m1 m2 m3 tail b8 cap).getD c 0 = keccakInOff m0 m1 m2 m3 tail b8 cap c := by
  simp [keccakIns, hc]

theorem keccakOuts_getD (out n : ℕ) {k : ℕ} (hk : k < n) : (keccakOuts out n).getD k 0 = out + k := by
  simp [keccakOuts, hk]

theorem keccakOuts_length (out n : ℕ) : (keccakOuts out n).length = n := by
  simp [keccakOuts]

/-- Instruction `i` of code in chunks of `chunkLength`, the padding past the end:
`CompiledFunction.instructionAt` at any chunk length. -/
def chunkedInstructionAt (chunkLength : ℕ) (chunks : List (List OffsetInstruction)) (i : ℕ) :
    OffsetInstruction :=
  listElementOrDefault (listElementOrDefault chunks (i / chunkLength) []) (i % chunkLength) .padding

theorem nth_eq_getElem? {α : Type} {l : List α} {n : ℕ} (d : α) (h : n < l.length) :
    l[n]? = some (listElementOrDefault l n d) := by
  induction l generalizing n with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih (Nat.lt_of_succ_lt_succ h)

/-- Well-chunked code has the stated length, and `chunkAt` reads it. -/
theorem chunked_spec {C : ℕ} (hC : 0 < C) {cs : List (List OffsetInstruction)} {n : ℕ}
    (h : chunked C cs n = true) :
    cs.flatten.length = n ∧ ∀ i < n, cs.flatten[i]? = some (chunkedInstructionAt C cs i) := by
  induction cs generalizing n with
  | nil =>
    have : n = 0 := by simpa [chunked] using h
    subst this
    exact ⟨rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  | cons c cs ih =>
    unfold chunked at h
    split_ifs at h with hn
    · simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
      obtain ⟨rfl, hc⟩ := h
      refine ⟨by simp [hc], fun i hi ↦ ?_⟩
      have hiC : i < C := Nat.lt_of_lt_of_le hi hn
      rw [chunkedInstructionAt, Nat.div_eq_of_lt hiC, Nat.mod_eq_of_lt hiC]
      simpa [listElementOrDefault] using nth_eq_getElem? (l := c) OffsetInstruction.padding
          (by omega)
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hc, hcs⟩ := h
      obtain ⟨hlen, hget⟩ := ih hcs
      refine ⟨by simp [hlen, hc]; omega, fun i hi ↦ ?_⟩
      rw [List.flatten_cons, chunkedInstructionAt]
      by_cases hiC : i < C
      · rw [Nat.div_eq_of_lt hiC, Nat.mod_eq_of_lt hiC, List.getElem?_append_left (by omega)]
        exact nth_eq_getElem? _ (by omega)
      · rw [List.getElem?_append_right (by omega), hc, Nat.div_eq_sub_div hC (by omega),
          Nat.mod_eq_sub_mod (by omega)]
        exact hget (i - C) (by omega)

/-- The code of a well-chunked function has `len` instructions. -/
theorem CompiledFunction.length_code {f : CompiledFunction} (h : f.WellChunked) : f.code.length =
    f.instructionCount :=
  (chunked_spec (by decide) h).1

/-- In a well-chunked function, `instructionAt` reads the code. -/
theorem CompiledFunction.getElem?_code {f : CompiledFunction} (h : f.WellChunked) {i : ℕ} (hi : i <
    f.instructionCount) :
    f.code[i]? = some (f.instructionAt i) :=
  (chunked_spec (by decide) h).2 i hi

theorem consecutive_le {s e : ℕ} {fns : List CompiledFunction} (h : consecutive s fns e = true) :
    s ≤ e := by
  induction fns generalizing s with
  | nil => simp [consecutive] at h; omega
  | cons f fs ih =>
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at h
    have := ih h.2
    omega

/-- In a consecutive layout, pc `entry + i` of a function is its instruction `i`. -/
theorem lookup_of_mem {s e : ℕ} {fns : List CompiledFunction} (h : consecutive s fns e = true)
    {f : CompiledFunction} (hf : f ∈ fns) {i : ℕ} (hi : i < f.instructionCount) :
    instructionAtPc fns (f.entryPc + i) = f.instructionAt i ∧ s ≤ f.entryPc ∧ f.entryPc + i <
        e := by
  induction fns generalizing s with
  | nil => exact absurd hf List.not_mem_nil
  | cons f' fs ih =>
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hentry, hfs⟩ := h
    have hle := consecutive_le hfs
    rcases List.mem_cons.mp hf with rfl | hf
    · refine ⟨?_, by omega, by omega⟩
      rw [instructionAtPc, ite_eq_left (by omega), Nat.add_sub_cancel_left]
    · obtain ⟨hl, hs, he⟩ := ih hfs hf
      refine ⟨?_, by omega, he⟩
      rw [instructionAtPc, ite_eq_right (by omega), hl]

/-- In a consecutive layout ending at `e`, every pc from `e` on is padding. -/
theorem lookup_of_le {s e pc : ℕ} {fns : List CompiledFunction} (h : consecutive s fns e = true)
    (hpc : e ≤ pc) : instructionAtPc fns pc = .padding := by
  induction fns generalizing s with
  | nil => rfl
  | cons f fs ih =>
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at h
    have := consecutive_le h.2
    rw [instructionAtPc, ite_eq_right (by omega), ih h.2]

section

variable {fns : List CompiledFunction} {logSize e : ℕ} {hl : logSize ≤ maxLogBytecode}

/-- **The fetch lemma**: in a consecutive layout from pc `0` that fits the program, the
instruction at pc `entry + i` of a function `f` is `f.instructionAt i`. -/
theorem assemble_fetch (h : consecutive 0 fns e = true) (he : e ≤ 2 ^ logSize)
    {f : CompiledFunction} (hf : f ∈ fns) {i : ℕ} (hi : i < f.instructionCount) :
    (assemble fns logSize hl).fetch (addressOfIndex (f.entryPc + i)) = some (f.instructionAt
        i).toLeanIsaInstruction := by
  obtain ⟨hlookup, -, hlt⟩ := lookup_of_mem h hf hi
  rw [LeanIsaProgram.fetch_gpow (assemble fns logSize hl) ⟨f.entryPc + i, (by omega : f.entryPc + i < 2 ^ logSize)⟩]
  exact congrArg (fun ins ↦ some (OffsetInstruction.toLeanIsaInstruction ins)) hlookup

/-- `assemble_fetch` at a pc and an instruction given as literals: each side condition is one
small evaluation (`decide +kernel`). -/
theorem assemble_fetch_of (h : consecutive 0 fns e = true) (he : e ≤ 2 ^ logSize)
    {f : CompiledFunction} (hf : f ∈ fns) {i pc : ℕ} {ins : OffsetInstruction} (hi : i <
        f.instructionCount)
    (hpc : f.entryPc + i = pc) (hins : f.instructionAt i = ins) :
    (assemble fns logSize hl).fetch (addressOfIndex pc) = some ins.toLeanIsaInstruction := by
  rw [← hpc, ← hins]
  exact assemble_fetch h he hf hi

/-- Past the functions, the program holds the padding. -/
theorem assemble_fetch_pad (h : consecutive 0 fns e = true) {pc : ℕ} (hpc : e ≤ pc)
    (hpc' : pc < 2 ^ logSize) :
    (assemble fns logSize hl).fetch (addressOfIndex pc) = some
        OffsetInstruction.padding.toLeanIsaInstruction := by
  rw [LeanIsaProgram.fetch_gpow (assemble fns logSize hl) ⟨pc, hpc'⟩]
  exact congrArg (fun ins ↦ some (OffsetInstruction.toLeanIsaInstruction ins)) (lookup_of_le h hpc)

end

end
end LeanVM.Guest
