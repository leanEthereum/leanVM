/-
  LeanVM.Guest.Code

  Compiled bytecode in offset form: instructions over `ℕ` frame offsets, compiled functions in
  chunks, their assembly into a `Program`, and the fetch lemma of an assembled program.
-/

module

public import LeanVM.Semantics.Lemmas

/-!
# Offset-form bytecode

The compiler's `Op` (`crates/leanvm_core/src/cpu/isa.rs`) names a frame cell by its offset `o`,
whose bytecode slot is `g^o` (`crates/leanvm_core/src/cpu/layout.rs:221-300`), and holds a `SET`
immediate as three `u64` limbs. `OInstr` is that form, and `OInstr.toInstr` its meaning in
`LeanVM.Spec.Isa`: the kernel never evaluates a power of `g`, which costs one multiplication per
unit of the exponent, because every offset stays a `ℕ` until `toInstr` wraps it in `gpow`.

A compiled function (`CompiledFn`) is its name, entry pc, length and code, the code in chunks of
`chunkSize` instructions so that no literal is too large to elaborate. `assemble` lays a list of
functions out as a `Program`, padding with `SET fp[0] = 0` as the compiler does
(`crates/lean_compiler/src/lib.rs`). When the functions are laid out one after another from pc
`0` (`consecutive`, decided once per program), `assemble_fetch` gives the instruction at every pc
of every function, by a proof that evaluates nothing but the one instruction asked for.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## Instructions -/

/-- An instruction with frame offsets as `ℕ` and a `SET` immediate as three limbs. -/
inductive OInstr
  /-- `fp[c] = fp[a] + fp[b]`. -/
  | xor (a b c : ℕ)
  /-- `fp[c] = fp[a] · fp[b]`. -/
  | mul (a b c : ℕ)
  /-- `fp[o] = k0 + k1·y + k2·y²`, each limb a 64-bit word. -/
  | set (o k0 k1 k2 : ℕ)
  /-- `*(fp[o1]·g^o2)` is the source `mode` selects, `fp[o3]` for `.cell`. -/
  | deref (o1 o2 o3 : ℕ) (mode : DerefMode)
  /-- If `fp[oc] ≠ 0`, `(pc, fp) := (fp[od], fp[of])`. -/
  | jump (oc od of : ℕ)
  /-- `fp[out], fp[out+1]` is the compression of `fp[m0..m3]` under `fp[cv], fp[cv+1]`, with
  metadata `fp[md]`. -/
  | blake2s (m0 m1 m2 m3 cv out md : ℕ)
  deriving DecidableEq, Repr

/-- The padding instruction, `SET fp[0] = 0`. -/
def OInstr.pad : OInstr := .set 0 0 0 0

/-- The word of a `SET` immediate's limbs. -/
def OInstr.imm (k0 k1 k2 : ℕ) : E := E.ofLimbs (K.ofBits k0) (K.ofBits k1) (K.ofBits k2)

/-- The instruction of `LeanVM.Spec.Isa` an offset-form instruction denotes. -/
def OInstr.toInstr : OInstr → Instr
  | .xor a b c => .xor (gpow a) (gpow b) (gpow c)
  | .mul a b c => .mulNative (gpow a) (gpow b) (gpow c)
  | .set o k0 k1 k2 => .setConstant (gpow o) (OInstr.imm k0 k1 k2)
  | .deref o1 o2 o3 mode => .deref (gpow o1) (gpow o2) (gpow o3) mode
  | .jump oc od of => .jump (gpow oc) (gpow od) (gpow of)
  | .blake2s m0 m1 m2 m3 cv out md =>
      .blake2s ![gpow m0, gpow m1, gpow m2, gpow m3] (gpow cv) (gpow out) (gpow md)

/-- Whether an instruction is a `JUMP`, the one that may not fall through. -/
def OInstr.isJump : OInstr → Bool
  | .jump .. => true
  | _ => false

/-! ## Compiled functions -/

/-- The instructions per chunk of a compiled function's code. -/
def chunkSize : ℕ := 2048

/-- Element `n` of a list, `d` past its end; structural, for the kernel. -/
def nth {α : Type} : List α → ℕ → α → α
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: as, n + 1, d => nth as n d

/-- A compiled function: its name, entry pc, number of instructions, and code in chunks. -/
structure CompiledFn where
  /-- The compiler's name, `f__L…` for a specialization. -/
  name : String
  /-- The pc of its first instruction. -/
  entry : ℕ
  /-- The number of instructions. -/
  len : ℕ
  /-- The code, `chunkSize` instructions per chunk but the last. -/
  chunks : List (List OInstr)

/-- Instruction `i` of code in chunks of `C`, the padding past the end. -/
def chunkAt (C : ℕ) (cs : List (List OInstr)) (i : ℕ) : OInstr := nth (nth cs (i / C) []) (i % C) .pad

/-- The instruction at offset `i`, the padding past the end. -/
def CompiledFn.instrAt (f : CompiledFn) (i : ℕ) : OInstr := chunkAt chunkSize f.chunks i

/-- The code as one list. -/
def CompiledFn.code (f : CompiledFn) : List OInstr := f.chunks.flatten

/-- The chunks hold `n` instructions, `C` in each but the last. -/
def chunked (C : ℕ) : List (List OInstr) → ℕ → Bool
  | [], n => n == 0
  | c :: cs, n =>
      if n ≤ C then cs.isEmpty && c.length == n else c.length == C && chunked C cs (n - C)

/-- The chunks hold exactly the function's `len` instructions. -/
def CompiledFn.WellChunked (f : CompiledFn) : Prop := chunked chunkSize f.chunks f.len = true

/-! ## Assembly -/

/-- The instruction at pc `pc` of the functions `fns`, the padding outside them. -/
def lookup : List CompiledFn → ℕ → OInstr
  | [], _ => .pad
  | f :: fs, pc => if pc < f.entry + f.len then f.instrAt (pc - f.entry) else lookup fs pc

/-- The functions are laid out one after another from pc `s`, ending at pc `e`. -/
def consecutive : ℕ → List CompiledFn → ℕ → Bool
  | s, [], e => s == e
  | s, f :: fs, e => f.entry == s && consecutive (s + f.len) fs e

/-- The program of `2^logSize` slots holding the functions `fns`, padded. -/
def assemble (fns : List CompiledFn) (logSize : ℕ) (h : logSize ≤ maxLogBytecode) : Program :=
  ⟨logSize, h, fun i ↦ (lookup fns i).toInstr⟩

/-! ## Lemmas -/

theorem nth_eq_getElem? {α : Type} {l : List α} {n : ℕ} (d : α) (h : n < l.length) :
    l[n]? = some (nth l n d) := by
  induction l generalizing n with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih (Nat.lt_of_succ_lt_succ h)

/-- Well-chunked code has the stated length, and `chunkAt` reads it. -/
theorem chunked_spec {C : ℕ} (hC : 0 < C) {cs : List (List OInstr)} {n : ℕ}
    (h : chunked C cs n = true) :
    cs.flatten.length = n ∧ ∀ i < n, cs.flatten[i]? = some (chunkAt C cs i) := by
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
      rw [chunkAt, Nat.div_eq_of_lt hiC, Nat.mod_eq_of_lt hiC]
      simpa [nth] using nth_eq_getElem? (l := c) OInstr.pad (by omega)
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hc, hcs⟩ := h
      obtain ⟨hlen, hget⟩ := ih hcs
      refine ⟨by simp [hlen, hc]; omega, fun i hi ↦ ?_⟩
      rw [List.flatten_cons, chunkAt]
      by_cases hiC : i < C
      · rw [Nat.div_eq_of_lt hiC, Nat.mod_eq_of_lt hiC, List.getElem?_append_left (by omega)]
        exact nth_eq_getElem? _ (by omega)
      · rw [List.getElem?_append_right (by omega), hc, Nat.div_eq_sub_div hC (by omega),
          Nat.mod_eq_sub_mod (by omega)]
        exact hget (i - C) (by omega)

/-- The code of a well-chunked function has `len` instructions. -/
theorem CompiledFn.length_code {f : CompiledFn} (h : f.WellChunked) : f.code.length = f.len :=
  (chunked_spec (by decide) h).1

/-- In a well-chunked function, `instrAt` reads the code. -/
theorem CompiledFn.getElem?_code {f : CompiledFn} (h : f.WellChunked) {i : ℕ} (hi : i < f.len) :
    f.code[i]? = some (f.instrAt i) :=
  (chunked_spec (by decide) h).2 i hi

theorem consecutive_le {s e : ℕ} {fns : List CompiledFn} (h : consecutive s fns e = true) :
    s ≤ e := by
  induction fns generalizing s with
  | nil => simp [consecutive] at h; omega
  | cons f fs ih =>
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at h
    have := ih h.2
    omega

/-- In a consecutive layout, pc `entry + i` of a function is its instruction `i`. -/
theorem lookup_of_mem {s e : ℕ} {fns : List CompiledFn} (h : consecutive s fns e = true)
    {f : CompiledFn} (hf : f ∈ fns) {i : ℕ} (hi : i < f.len) :
    lookup fns (f.entry + i) = f.instrAt i ∧ s ≤ f.entry ∧ f.entry + i < e := by
  induction fns generalizing s with
  | nil => exact absurd hf List.not_mem_nil
  | cons f' fs ih =>
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hentry, hfs⟩ := h
    have hle := consecutive_le hfs
    rcases List.mem_cons.mp hf with rfl | hf
    · refine ⟨?_, by omega, by omega⟩
      rw [lookup, ite_eq_left (by omega), Nat.add_sub_cancel_left]
    · obtain ⟨hl, hs, he⟩ := ih hfs hf
      refine ⟨?_, by omega, he⟩
      rw [lookup, ite_eq_right (by omega), hl]

/-- In a consecutive layout ending at `e`, every pc from `e` on is padding. -/
theorem lookup_of_le {s e pc : ℕ} {fns : List CompiledFn} (h : consecutive s fns e = true)
    (hpc : e ≤ pc) : lookup fns pc = .pad := by
  induction fns generalizing s with
  | nil => rfl
  | cons f fs ih =>
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at h
    have := consecutive_le h.2
    rw [lookup, ite_eq_right (by omega), ih h.2]

section

variable {fns : List CompiledFn} {logSize e : ℕ} {hl : logSize ≤ maxLogBytecode}

/-- **The fetch lemma**: in a consecutive layout from pc `0` that fits the program, the
instruction at pc `entry + i` of a function `f` is `f.instrAt i`. -/
theorem assemble_fetch (h : consecutive 0 fns e = true) (he : e ≤ 2 ^ logSize)
    {f : CompiledFn} (hf : f ∈ fns) {i : ℕ} (hi : i < f.len) :
    (assemble fns logSize hl).fetch (gpow (f.entry + i)) = some (f.instrAt i).toInstr := by
  obtain ⟨hlookup, -, hlt⟩ := lookup_of_mem h hf hi
  rw [Program.fetch_gpow (assemble fns logSize hl) ⟨f.entry + i, (by omega : f.entry + i < 2 ^ logSize)⟩]
  exact congrArg (fun ins ↦ some (OInstr.toInstr ins)) hlookup

/-- `assemble_fetch` at a pc and an instruction given as literals: each side condition is one
small evaluation (`decide +kernel`). -/
theorem assemble_fetch_of (h : consecutive 0 fns e = true) (he : e ≤ 2 ^ logSize)
    {f : CompiledFn} (hf : f ∈ fns) {i pc : ℕ} {ins : OInstr} (hi : i < f.len)
    (hpc : f.entry + i = pc) (hins : f.instrAt i = ins) :
    (assemble fns logSize hl).fetch (gpow pc) = some ins.toInstr := by
  rw [← hpc, ← hins]
  exact assemble_fetch h he hf hi

/-- Past the functions, the program holds the padding. -/
theorem assemble_fetch_pad (h : consecutive 0 fns e = true) {pc : ℕ} (hpc : e ≤ pc)
    (hpc' : pc < 2 ^ logSize) :
    (assemble fns logSize hl).fetch (gpow pc) = some OInstr.pad.toInstr := by
  rw [Program.fetch_gpow (assemble fns logSize hl) ⟨pc, hpc'⟩]
  exact congrArg (fun ins ↦ some (OInstr.toInstr ins)) (lookup_of_le h hpc)

/-- A program whose functions end before its last slot is sentinel safe: that slot is padding. -/
theorem assemble_sentinelSafe (h : consecutive 0 fns e = true) (he : e < 2 ^ logSize) :
    SentinelSafe (assemble fns logSize hl) := by
  show (OInstr.toInstr (lookup fns (2 ^ logSize - 1))).opcode ≠ .jump
  rw [lookup_of_le h (by omega)]
  decide

end

end
end LeanVM.Guest
