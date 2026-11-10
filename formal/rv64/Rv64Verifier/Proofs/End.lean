import Rv64Verifier.EndStatement
import Rv64Verifier.Sym.Read
import Rv64Verifier.Proofs.Rodata

/-!
# From `main`'s contract to the end statement

`_start` sets `gp` and `sp`, calls `main`, and on its return issues `HALT` with `main`'s verdict
in `a0`. So if `main` returns `1` only on an input that decodes to an accepted proof
(`MainPost`), the image is sound (`sound_of_main`): a run that halts with `1` is that run, the
machine being deterministic, and every other way `main` can end (a dead end) never halts with
`1`.
-/

namespace Rv64Verifier.Proofs.End
open RiscvZkvm.Rv64 Rv64Verifier.Sym LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- The image. -/
def image : LoadImage := ⟨Image.entry, Image.code, Image.dataWords⟩

def mainEntry : Word := 0x800002cc
def returnPoint : Word := 0x8000001c
def haltPoint : Word := 0x80000020
def stackTop : Word := 0xbffffff0
def globalPointer : Word := 0xa0001738

/-! ## Runs that stop -/

theorem stop_unique_aux {code : Code} : ∀ (n m : Nat) (s u t : MachineState),
    Steps code n s u → step code u = none → Steps code m s t → step code t = none → t = u
  | 0, 0, _, _, _, hu, _, ht, _ => by cases hu; cases ht; rfl
  | 0, _ + 1, _, _, _, hu, hstop, ht, _ => by
    cases hu; obtain ⟨_, hs, _⟩ := ht; rw [hstop] at hs; cases hs
  | _ + 1, 0, _, _, _, hu, _, ht, htstop => by
    cases ht; obtain ⟨_, hs, _⟩ := hu; rw [htstop] at hs; cases hs
  | n + 1, m + 1, _, u, t, hu, hstop, ht, htstop => by
    obtain ⟨s₁, hs₁, hu⟩ := hu
    obtain ⟨s₂, hs₂, ht⟩ := ht
    rw [hs₁] at hs₂
    cases hs₂
    exact stop_unique_aux n m s₁ u t hu hstop ht htstop

/-- Two runs from the same state that both end where the machine stops are the same run. -/
theorem stop_unique {code : Code} {n : Nat} {s u t : MachineState} (hu : Steps code n s u)
    (hstop : step code u = none) (ht : Reaches code s t) (htstop : step code t = none) : t = u :=
  let ⟨m, ht⟩ := ht
  stop_unique_aux n m s u t hu hstop ht htstop

theorem Halting.step_none {code : Code} {t : MachineState} (h : Halting code t) :
    step code t = none := by
  obtain ⟨hf, ht0⟩ := h
  have hx5 : ({ t with code := code.baseMap } : MachineState).getReg .x5 = 0 := ht0
  simp only [step, hf]
  simp only [RiscvZkvm.Rv64.step, Code.baseMap, hf]
  simp [hx5]

/-! ## `_start` -/

def cfg : Config := { noAlias := true }

/-- `la gp`, `li sp`, `call main`. -/
def startExpect : Expect where
  steps := 7
  pc := .c mainEntry
  regs := [(.x1, .c returnPoint), (.x2, .c stackTop), (.x3, .c globalPointer), (.x10, .reg .x10)]
  mem := []
  writes := []
  obl := []

theorem start_spec : BlockSpec Image.code Image.entry 7 (fun _ ↦ True) startExpect.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 7) (x := startExpect)
    (words := (Image.code.words.drop 0).take 7) (by decide +kernel)
    (CodeAt.slice Image.code 0 7 Image.entry (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ _ ↦ trivial) (fun _ _ _ h ↦ h)

/-- `li t0, 0`, then the `HALT` call. -/
def haltExpect : Expect where
  steps := 1
  pc := .c haltPoint
  regs := [(.x5, .c 0), (.x10, .reg .x10)]
  mem := []
  writes := []
  obl := []

theorem halt_spec : BlockSpec Image.code returnPoint 1 (fun _ ↦ True) haltExpect.Holds :=
  BlockSpec.of_expect (cfg := cfg) (fuel := 1) (x := haltExpect)
    (words := (Image.code.words.drop 7).take 1) (by decide +kernel)
    (CodeAt.slice Image.code 7 1 returnPoint (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ _ ↦ trivial) (fun _ _ _ h ↦ h)

theorem halt_fetch : Image.code.fetch haltPoint = some (.base .ECALL) := by rfl

/-! ## `main`'s contract, and soundness -/

/-- What `main` starts from: `_start`'s registers, the image's data, and the input. -/
def MainPre (words : List Word) (s : MachineState) : Prop :=
  s.getReg .x2 = stackTop ∧ s.getReg .x3 = globalPointer ∧
  s.getReg .x10 = BitVec.ofNat 64 words.length ∧
  (∀ p ∈ Image.dataWords, s.getMem p.1 = p.2) ∧
  (∀ i (h : i < words.length), s.getMem (inputBase + BitVec.ofNat 64 (8 * i)) = words[i])

/-- `main` starts with `.rodata` in place. -/
theorem MainPre.rodataOk {words : List Word} {s : MachineState} (h : MainPre words s) :
    RodataOk s :=
  fun p hp ↦ h.2.2.2.1 p (List.mem_of_mem_filter hp)

/-- `main` returns `1` only on an accepted proof. -/
def MainPost (words : List Word) (_ t : MachineState) : Prop :=
  t.getReg .x10 = 1 → ∃ bytecode publicInput proof,
    decodeInput words = some (bytecode, publicInput, proof) ∧ verify bytecode publicInput proof = true

/-- **Soundness, from `main`'s contract.** -/
theorem sound_of_main (hmain : ∀ words, FunSpec Image.code mainEntry (MainPre words) (MainPost words)) :
    Sound image := by
  intro words s n hload hhalts
  obtain ⟨hpc, hdata, hinput, ha0, -⟩ := hload
  obtain ⟨u, hu, hhalt, hu1⟩ := hhalts
  have hustop := Halting.step_none hhalt
  -- `_start` up to the call
  obtain ⟨s₁, hs₁, hx⟩ := start_spec.reaches hpc trivial
  have hfr : ∀ a, s₁.getMem a = s.getMem a := fun a ↦ hx.frame a (by simp [startExpect])
  have hreg : ∀ r v, (r, v) ∈ startExpect.regs → s₁.getReg r = v.eval s :=
    fun r v h ↦ hx.2.1 (r, v) h
  have hpre : MainPre words s₁ := by
    refine ⟨hreg .x2 (.c stackTop) (by simp [startExpect]),
      hreg .x3 (.c globalPointer) (by simp [startExpect]), ?_, ?_, ?_⟩
    · rw [hreg .x10 (.reg .x10) (by simp [startExpect])]; exact ha0
    · intro p hp; rw [hfr]; exact hdata p hp
    · intro i h; rw [hfr]; exact hinput i h
  have hmainpc : s₁.pc = mainEntry := hx.pc
  obtain ⟨t, hst, hout⟩ := hmain words s₁ hmainpc hpre
  rcases hout with ⟨htpc, -, hpost⟩ | hdead
  · -- `main` returned to `_start`
    have hret : t.pc = returnPoint := by
      rw [htpc, returnAddress, hreg .x1 (.c returnPoint) (by simp [startExpect])]
      show returnPoint &&& ~~~1#64 = returnPoint
      decide +kernel
    obtain ⟨t₂, ht₂, hy⟩ := halt_spec.reaches hret trivial
    have hfetch : Image.code.fetch t₂.pc = some (.base .ECALL) := by rw [hy.pc]; exact halt_fetch
    have hx5 : t₂.getReg .x5 = 0 := hy.2.1 (.x5, .c 0) (by simp [haltExpect])
    have ha0' : t₂.getReg .x10 = t.getReg .x10 := hy.2.1 (.x10, .reg .x10) (by simp [haltExpect])
    have hsame : t₂ = u :=
      stop_unique hu hustop (hs₁.trans (hst.trans ht₂)) (Halting.step_none ⟨hfetch, hx5⟩)
    apply hpost
    rw [← ha0', hsame, hu1]
  · have hsame : t = u := stop_unique hu hustop (hs₁.trans hst) hdead.1
    subst hsame
    exact absurd hu1 (hdead.2 hhalt)

end Rv64Verifier.Proofs.End
