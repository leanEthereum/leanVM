module

public import LeanVMCircuits.Blake2s.Schedule

@[expose] public section

/-!
The BLAKE2s compression of the VM's `blake2s` instruction as one Clean circuit, and its soundness against RFC 7693.

Its inputs are the instruction class's ports, as bits: the 64-bit counter `t`, the 32-bit finalization word `f0`, the
chaining value's eight 32-bit words `h` and the message's sixteen `m`, each word low bit first. Its output is the new
chaining value's eight words. The circuit computes the compression with `f0` XORed into the working vector's word 14,
which is RFC 7693's F for the two finalization words `0` and `0xFFFFFFFF`.
-/

namespace LeanVMCircuits.Blake2s.Compress

open LeanVMCircuits Rfc7693

attribute [local irreducible] program

structure Input (F : Type) where
  t : Vector F 64
  f0 : Vector F 32
  h : Vector F 256
  m : Vector F 512
  deriving ProvableStruct

/-- Word `i` of a vector of words. -/
def chunk {α : Type} {k : ℕ} (v : Vector α (32 * k)) (i : ℕ) (hi : i < k) : Vector α 32 :=
  Vector.ofFn fun j => v[32 * i + j.val]'(by omega)

def low {α : Type} (t : Vector α 64) : Vector α 32 := Vector.ofFn fun j => t[j.val]

def high {α : Type} (t : Vector α 64) : Vector α 32 := Vector.ofFn fun j => t[32 + j.val]

/-- The program's first 32 registers: `h`, `m`, then the working vector's words 8 to 15 before the rounds. -/
def register (input : Var Input Bit) (r : Fin 32) : Reg :=
  if h : r.val < 8 then chunk input.h r.val h
  else if h : r.val < 24 then chunk (k := 16) input.m (r.val - 8) (by omega)
  else match r.val - 24 with
    | 4 => xorBits (literal IV[4]) (low input.t)
    | 5 => xorBits (literal IV[5]) (high input.t)
    | 6 => xorBits (literal IV[6]) input.f0
    | 7 => literal IV[7]
    | i => literal IV[i % 8]

def registers (input : Var Input Bit) : List Reg := List.ofFn (register input)

/-- Output bit `32 i + j`: `h_i ^ v_i ^ v_{i+8}`, through the program's final lanes. -/
def output (input : Var Input Bit) (final : List Reg) : Vector (Expression Bit) 256 :=
  Vector.ofFn fun k =>
    let i : Fin 8 := ⟨k.val / 32, by omega⟩
    let j : Fin 32 := ⟨k.val % 32, by omega⟩
    (chunk input.h i.val i.isLt)[j] + (get final program.lanes[i.val])[j] + (get final program.lanes[i.val + 8])[j]

def main (input : Var Input Bit) : Circuit Bit (Var (fields 256) Bit) := do
  let final ← run program.ops (registers input)
  return output input final

instance elaborated : ElaboratedCircuit Bit Input (fields 256) main where
  localLength _ := (program.ops.map Op.length).sum
  localLength_eq input offset := by
    have := run_localLength program.ops (registers input) offset
    simp only [main, circuit_norm] at this ⊢
    simpa using this
  subcircuitsConsistent input offset := by
    have := run_consistent program.ops (registers input) offset
    simp only [main, circuit_norm] at this ⊢
    simpa using this
  channelsLawful := by
    intro input offset
    have := run_channelsLawful program.ops (registers input) offset
    simp only [main, circuit_norm] at this ⊢
    simpa using this

def words {k : ℕ} (v : Vector Bit (32 * k)) : Vector Word k := Vector.ofFn fun i => toWord (chunk v i.val i.isLt)

def Spec (input : Input Bit) (out : fields 256 Bit) : Prop :=
  ∀ f : Bool, toWord input.f0 = (if f then BitVec.allOnes 32 else 0) →
    words (k := 8) out = F (words input.h) (words input.m) (toWord input.t) f

/-- F's working vector before its rounds. -/
def initialV (h : Vector Word 8) (t : BitVec 64) (f : Bool) : Vector Word 16 :=
  let v := h ++ IV
  let v := v.set 12 (v[12] ^^^ t.setWidth 32)
  let v := v.set 13 (v[13] ^^^ (t >>> 32).setWidth 32)
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes 32) else v

theorem F_eq (h : Vector Word 8) (m : Vector Word 16) (t : BitVec 64) (f : Bool) :
    F h m t f = Vector.ofFn fun i : Fin 8 =>
      h[i] ^^^ (rounds (initialV h t f) m)[i] ^^^ (rounds (initialV h t f) m)[i.val + 8] := by
  cases f <;> rfl

theorem map_chunk {α β : Type} {k : ℕ} (f : α → β) (v : Vector α (32 * k)) (i : ℕ) (hi : i < k) :
    (chunk v i hi).map f = chunk (v.map f) i hi := by
  ext j hj; simp [chunk]

theorem map_low {α β : Type} (f : α → β) (t : Vector α 64) : (low t).map f = low (t.map f) := by
  ext j hj; simp [low]

theorem map_high {α β : Type} (f : α → β) (t : Vector α 64) : (high t).map f = high (t.map f) := by
  ext j hj; simp [high]

theorem toWord_low (t : Vector Bit 64) : toWord (low t) = (toWord t).setWidth 32 := by
  apply toWord_ext
  intro i hi
  simp [low, -BitVec.getLsbD_eq_getElem, getLsbD_toWord, hi, show i < 64 by omega]

theorem toWord_high (t : Vector Bit 64) : toWord (high t) = ((toWord t) >>> 32).setWidth 32 := by
  apply toWord_ext
  intro i hi
  simp [high, BitVec.getLsbD_ushiftRight, -BitVec.getLsbD_eq_getElem, getLsbD_toWord, hi,
    show 32 + i < 64 by omega]

theorem values_registers (env : Environment Bit) (input : Var Input Bit) (r : ℕ) (hr : r < 32) :
    (values env (registers input)).getD r 0 = toWord ((register input ⟨r, hr⟩).map (Expression.eval env)) := by
  rw [values, List.getD_eq_getElem?_getD, List.getElem?_map, registers, List.getElem?_ofFn]
  simp [hr]

theorem registers_holds (env : Environment Bit) (input : Var Input Bit) (f : Bool)
    (hf : toWord (input.f0.map (Expression.eval env)) = (if f then BitVec.allOnes 32 else 0)) :
    Holds (values env (registers input)) Blake2s.initial
      (initialV (words (input.h.map (Expression.eval env))) (toWord (input.t.map (Expression.eval env))) f)
      (words (input.m.map (Expression.eval env))) := by
  refine ⟨by simp [values, registers, Blake2s.initial], by simp [Blake2s.initial], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [Blake2s.initial]
  · intro i
    cases f <;> fin_cases i
    all_goals
      simp only [Blake2s.initial]
      rw [values_registers env input _ (by decide)]
      simp [register, initialV, words, map_chunk, map_low, map_high, map_xorBits, toWord_xor, eval_literal,
        toWord_literal, toWord_low, toWord_high, hf]
    all_goals first
      | (rw [Vector.getElem_append_left (by decide)]; simp)
      | (rw [Vector.getElem_append_right (by decide)]; rfl)
      | (rw [Vector.getElem_append_right (by decide)]; simp)
  · intro j
    rw [values_registers env input (8 + j.val) (by omega), register, dif_neg (show ¬ (8 + j.val < 8) by omega), dif_pos (show 8 + j.val < 24 by omega),
      map_chunk]
    simp [words]

theorem output_words (env : Environment Bit) (input : Var Input Bit) (final : List Reg) (i : ℕ) (hi : i < 8) :
    toWord (chunk ((output input final).map (Expression.eval env)) i hi) =
      toWord ((chunk input.h i hi).map (Expression.eval env)) ^^^
        toWord ((get final program.lanes[i]).map (Expression.eval env)) ^^^
        toWord ((get final program.lanes[i + 8]).map (Expression.eval env)) := by
  rw [← toWord_xor, ← toWord_xor]
  congr 1
  ext j hj
  have hdiv : (32 * i + j) / 32 = i := by omega
  have hmod : (32 * i + j) % 32 = j := by omega
  simp [output, chunk, xorBits, Expression.eval, hdiv, Nat.mod_eq_of_lt hj]

theorem soundness : Soundness Bit main (fun _ => True) Spec := by
  circuit_proof_start
  refine ⟨?_, run_requirements _ _ _ env⟩
  intro f hf
  obtain ⟨h_t, h_f0, h_h, h_m⟩ := h_input
  set input_var : Var Input Bit := { t := input_var_t, f0 := input_var_f0, h := input_var_h, m := input_var_m }
  have hrun := run_soundness program.ops (fun op h => program_valid op h) (registers input_var) i₀ env h_holds
  have hinit := registers_holds env input_var f (by simpa only [input_var, h_f0] using hf)
  simp only [input_var, h_t, h_h, h_m] at hinit
  have hiv : (initialV (words input_h) (toWord input_t) f)[8] = IV[0] ∧
      (initialV (words input_h) (toWord input_t) f)[9] = IV[1] ∧
      (initialV (words input_h) (toWord input_t) f)[10] = IV[2] ∧
      (initialV (words input_h) (toWord input_t) f)[11] = IV[3] := by
    cases f <;> simp [initialV] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Vector.getElem_append_right] <;> simp
  have hp := program_correct _ _ _ hinit hiv
  rw [← hrun] at hp
  obtain ⟨_, _, _, hlane, _⟩ := hp
  rw [F_eq]
  apply Vector.ext
  intro i hi
  have h1 := hlane ⟨i, by omega⟩
  have h2 := hlane ⟨i + 8, by omega⟩
  simp only [Fin.getElem_fin, Circuit.output] at h1 h2
  rw [words, Vector.getElem_ofFn]
  simp only
  rw [output_words env input_var _ i hi, ← values_getD, ← values_getD, h1, h2, map_chunk]
  simp [input_var, h_h, words]

theorem completeness : Completeness Bit main (fun _ => True) := by
  circuit_proof_start
  exact run_completeness _ _ _ _

def circuit : FormalCircuit Bit Input (fields 256) where
  main
  Spec
  soundness
  completeness
  exposedChannels_eq input offset := by
    have := run_exposedChannelsLawful program.ops (registers input) offset
    simp only [main, circuit_norm] at this ⊢
  requirementsChannelsLawful input offset := by
    have := run_requirementsChannelsLawful program.ops (registers input) offset
    simp only [main, circuit_norm] at this ⊢
    simpa using this

end LeanVMCircuits.Blake2s.Compress
