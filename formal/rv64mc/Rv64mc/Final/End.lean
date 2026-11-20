/-
  Rv64mc.Final.End

  The end theorem for the concrete image (`image`, read from `out/gen.elf` by `Rv64mc/Gen/Image.lean`, the ELF whose
  sha256 is `image.sha256`): `rv64_sound`, `AllDecode image ∧ Sound image` from `main`'s contract alone. Every other
  hypothesis of `sound_of_main` is discharged here by the kernel's evaluation of a check on the image
  (`kernel_eq`), and the link step's (`Rv64mc/Gen/Link/`): machine-checked's functions are the image's
  (`wordsIn_of_check`), `_start` is function 0 and its template's link holds (`Gen.Start.tmpl_eq`, `Gen.Start.wf`),
  and the environment (`env`) fits the image. `loaded_nonempty`: `Loaded image words` is satisfiable for every input
  that fits, so `Sound image` is not vacuous by its loader. Until `MainSpec` is proved, it is the one hypothesis.
-/

import Rv64mc.Final.Sound
import Rv64mc.Final.Image
import Rv64mc.Gen.Image
import Rv64mc.Gen.Link.Start
import Rv64mc.Gen.Link.VerifierRv64.Bump.AsGlobalAlloc.Alloc

namespace Rv64mc

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter MachineChecked.RiscV.Lift Tools.ToLean

/-! ## The environment of the image -/

/-- `NEXT`, where the allocator's template reads it. -/
def nextAddr : Word := Gen.VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr

/-- The heap's end (`HEAP_END`, `guest/src/main.rs`). -/
def heapEnd : Word := 0x78000000

/-- The lowest stack address: the word after `NEXT`, the image's last data word. -/
def stackLimit : Word := nextAddr + 8

/-- The stack `main` may use, from `stackTop` down to `stackLimit`. -/
def need : Nat := stackTop.toNat - stackLimit.toNat

/-- The static data: every data word of the image but `NEXT`. -/
def StaticData (m : MachineState) : Prop := ∀ p ∈ image.data, p.1 ≠ nextAddr → m.getMem p.1 = p.2

kernel_eq static_region :
  (image.data.all fun p => p.1 == nextAddr || (heapEnd.toNat ≤ p.1.toNat && p.1.toNat < nextAddr.toNat)) = true

kernel_eq layout_check :
  (heapEnd.toNat ≤ nextAddr.toNat && nextAddr.toNat + 8 < 2 ^ 64 && stackLimit.toNat + 0 ≤ stackTop.toNat &&
    stackLimit.toNat = nextAddr.toNat + 8 && heapStart.toNat ≤ heapEnd.toNat) = true

theorem layout_facts : heapEnd.toNat ≤ nextAddr.toNat ∧ stackLimit.toNat ≤ stackTop.toNat ∧
    stackLimit.toNat = nextAddr.toNat + 8 ∧ heapStart.toNat ≤ heapEnd.toNat := by
  have := layout_check
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  omega

theorem staticData_frame (m m' : MachineState)
    (h : ∀ a : Word, heapEnd.toNat ≤ a.toNat → a.toNat < nextAddr.toNat → m'.getMem a = m.getMem a)
    (hs : StaticData m) : StaticData m' := by
  intro p hp hne
  have := List.all_eq_true.1 static_region p hp
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with he | ⟨h1, h2⟩
  · exact absurd he hne
  · rw [h p.1 h1 h2, hs p hp hne]

/-- **The image's environment**: the static data in `[heapEnd, NEXT)`, `NEXT`, the stack above it. -/
noncomputable def env : Env where
  Static := StaticData
  staticLo := heapEnd
  staticHi := nextAddr
  static_frame := staticData_frame
  data := image.data.filter fun p => p.1 != nextAddr
  static_data := fun _ hs q hq => by
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at hq
    exact hs q hq.1 hq.2
  nextAddr := nextAddr
  heapEnd := heapEnd
  stackLimit := stackLimit
  layout := by have := layout_facts; omega

/-! ## The image's checks -/

kernel_eq all_decode_check : (image.code.all fun w => Runnable (decode w)) = true

kernel_eq wf_check : image.wfCheck = true

kernel_eq words_in_check : wordsInCheck image Gen.words = true

kernel_eq next_check : image.data.contains (nextAddr, heapStart) = true

kernel_eq entry_check : (Gen.Start.link.base == image.entry) = true

theorem fns_eq : Gen.fns = fnsOf Gen.words := rfl

/-! ## The end theorem -/

/-- **Every input that fits can be loaded.** -/
theorem loaded_nonempty (words : List Word) (h : words.length ≤ inputCapacity) : ∃ s, Loaded image words s :=
  loaded_exists (Image.wf_of_check wf_check) words h

/-- **The image is sound, and every code word is an instruction the machine runs**, if `main` keeps its
    contract. -/
theorem rv64_sound (hmain : MainSpec env (liftProg Gen.fns) Gen.Start.link.main.idx need) :
    AllDecode image ∧ Sound image := by
  refine ⟨allDecode_of_all all_decode_check, ?_⟩
  have hw := wordsIn_of_check words_in_check
  obtain ⟨fn, hg⟩ : ∃ fn, Gen.fns[0]? = some fn := by
    have := Gen.Start.tmpl_eq
    simp only [liftProg, List.getElem?_map, Option.map_eq_some_iff] at this
    obtain ⟨fn, h, -⟩ := this
    exact ⟨fn, h⟩
  have hl := layout_facts
  exact sound_of_main (fns := Gen.fns) (env := env) (need := need) (by rw [fns_eq]; exact progOk_of_wordsIn hw)
    (by rw [fns_eq]; exact fnsIn_of_wordsIn hw) hg Gen.Start.tmpl_eq (by simpa using entry_check) Gen.Start.wf
    (fun _ h p hp _ => h p hp) (by simpa [env] using next_check) hl.2.2.2
    (by simp only [env, need]; omega) hmain

end Rv64mc

/-- info: 'Rv64mc.rv64_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.rv64_sound

/-- info: 'Rv64mc.loaded_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.loaded_nonempty
