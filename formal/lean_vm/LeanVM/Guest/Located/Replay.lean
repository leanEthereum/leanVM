/-
  LeanVM.Guest.Located.Replay

  The frame map of a valid execution, by replaying its run: a call's valuation is that of the
  first frame at which the run entered the callee on the call's words.
-/

module

public import LeanVM.Guest.EndLoc
public import LeanVM.Guest.Located.Interface
public import LeanVM.Guest.PlaceCode
public import LeanVM.Guest.Compiled.Places
public import LeanVM.Guest.Compiled.DecoderTables
public import LeanVM.Cost.Decoder.GuestTablesCheck
public import LeanVM.Protocol.Extraction.Run

/-!
# The replayed frame map

The back end locates every call of `main`'s body at a frame the run from `(g^0, 1)` entered the
callee at, its precondition holding there and its argument and return words the call's
(`World.Entered`). The frame map `replayFrameV L` finds such a frame by replaying the run: it
steps the machine from `(g^0, 1)` (`statesIn`, reading the memory and the bytecode through the
indices of their addresses, `Extraction.powIndex`), and gives a call `f args rets` the valuation
by places (`placeWith`, the back end's places of `f`'s values, `Cost.Decoder.guestPlaces`) of the
first state that is the entry of a function named `f`, whose self test passes at the state's
frame (`selfTest`, decided) and whose frame's argument and return words are `args` and `rets`
(`enteredTest`). It chooses nothing: every test is decided by evaluation. The functions' entries,
argument and return counts and registered flags are the decoder's literal tables
(`Cost.Decoder.guestEntries`, `guestArgCounts`, `guestRetCounts`, `guestRegistered`).

* `statesIn`: the run's states; `mem_statesIn`, `run_of_mem_statesIn`: they are the states the run
  reaches, within the fuel. `steps_lt_replayFuel`: a halting run from `(g^0, 1)` takes fewer
  than `2^128` steps (it never repeats a state, `Protocol.Halting.run_injective`), so the replay
  with `replayFuel = 2^128` sees every state of a valid execution.
* `selfTest_iff`: the decided test is the back end's precondition `World.Pre` but for the jump
  table, which the run writes first, and what callers are asked for (`guestU`), which reads only
  the argument words, so it carries over between frames of one call.
* **`unfoldsV_replay`**: on a valid execution, the located relation `RLg` unfolds along the
  replayed frame map: the frame the replay finds is one the run entered, so the callee's contract
  (`End.globSpec`) gives its body there, under the valuation by places (`PlacesAgree`: the
  table's row is the back end's valuation on the function's values).
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.B1 LeanVM.Extraction LeanVM.Protocol.Halting LeanVM.Cost.Decoder

@[expose] public section

/-! ## The memory, read through an index -/

/-- The word at address `a`, its index looked up in `idx`. -/
def readIn (idx : Std.HashMap UInt64 ℕ) {κ : ℕ} (L : MemoryImage κ) (a : K) : Option E :=
  (gLogIn idx κ a).map L

/-- Through the index of the `2^κ` addresses, `κ < 64`, the read is the memory's. -/
theorem readIn_powIndex {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    readIn (powIndex κ) L = L.read :=
  funext fun a ↦ by rw [readIn, gLogIn_powIndex hκ]; rfl

/-- The word in cell `o` of the frame `fp`, read with `rd`, `0` if none (`LeanVM.Compiler.wd`). -/
def wordWith (rd : Reader) (fp : K) (o : ℕ) : E := (rd (fp * addressOfIndex o)).getD 0

/-- The `n` words of the frame `fp` from cell `o`, read with `rd` (`LeanVM.Compiler.frameWords`). -/
def wordsWith (rd : Reader) (fp : K) (o n : ℕ) : List E := (List.range n).map fun i ↦ wordWith rd fp (o + i)

/-! ## The run, replayed -/

section Replay

variable {memIdx codeIdx : Std.HashMap UInt64 ℕ} {prog : Semantics.LeanIsaProgram} {κ : ℕ} {L : MemoryImage κ}

/-- **The states of the run from `r`**, stepped through the indices: `r`, then, unless `r` is the
final state, the states from its step, for `fuel` steps at most. -/
def statesIn (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : Semantics.LeanIsaProgram) {κ : ℕ} (L : MemoryImage κ) :
    ℕ → Registers K → List (Registers K)
  | 0, r => [r]
  | n + 1, r => r :: if r = Registers.final prog then [] else
      match stepIn memIdx codeIdx prog L r with
      | some r' => statesIn memIdx codeIdx prog L n r'
      | none => []

/-- A state the run reaches within the fuel is replayed. -/
theorem mem_statesIn (hS : ∀ r, stepIn memIdx codeIdx prog L r = step prog L r) :
    ∀ {n fuel : ℕ} {r s : Registers K}, run prog L n r = some s → n ≤ fuel →
      s ∈ statesIn memIdx codeIdx prog L fuel r
  | 0, fuel, r, s, h, _ => by
    obtain rfl : r = s := Option.some.inj h
    cases fuel <;> simp [statesIn]
  | n + 1, 0, _, _, _, hn => absurd hn (by omega)
  | n + 1, fuel + 1, r, s, h, hn => by
    have hne := ne_final_of_run_succ h
    rw [run_succ_of_ne_final hne] at h
    obtain ⟨r', hr', h'⟩ := Option.bind_eq_some_iff.mp h
    rw [statesIn, ite_eq_right hne, hS, hr']
    exact List.mem_cons_of_mem _ (mem_statesIn hS h' (by omega))

/-- A replayed state is one the run reaches. -/
theorem run_of_mem_statesIn (hS : ∀ r, stepIn memIdx codeIdx prog L r = step prog L r) :
    ∀ {fuel : ℕ} {r s : Registers K}, s ∈ statesIn memIdx codeIdx prog L fuel r →
      ∃ n, run prog L n r = some s
  | 0, r, s, h => ⟨0, by simp [statesIn] at h; rw [h]; rfl⟩
  | fuel + 1, r, s, h => by
    rw [statesIn] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, rfl⟩
    · by_cases hf : r = Registers.final prog
      · rw [ite_eq_left hf] at h; simp at h
      · rw [ite_eq_right hf, hS] at h
        rcases hr : step prog L r with _ | r'
        · rw [hr] at h; simp at h
        · rw [hr] at h
          obtain ⟨n, hn⟩ := run_of_mem_statesIn hS h
          exact ⟨n + 1, by rw [run_succ_of_ne_final hf, hr]; exact hn⟩

/-- A run halting after `T` steps reaches its states in at most `T`. -/
theorem run_le_of_halts {T n : ℕ} {r s : Registers K}
    (hT : run prog L T r = some (Registers.final prog)) (hn : run prog L n r = some s) : n ≤ T := by
  by_contra hlt
  obtain ⟨d, rfl⟩ : ∃ d, n = T + (d + 1) := ⟨n - T - 1, by omega⟩
  rw [run_add, hT] at hn
  simp [run_succ_of_eq rfl] at hn

/-- From a state the halting run reaches after `n` steps, it halts after `T - n` more. -/
theorem safe_of_halts {T n : ℕ} {r s : Registers K}
    (hT : run prog L T r = some (Registers.final prog)) (hn : run prog L n r = some s) :
    Safe prog L (T - n) s := by
  have hle := run_le_of_halts hT hn
  have h := hT
  rw [show T = n + (T - n) by omega, run_add, hn] at h
  exact h

/-- **The fuel of the replay**: `2^128`, more than the machine's states `(pc, fp)`. -/
def replayFuel : ℕ := 2 ^ 128

/-- The code of a state below `2^128`: its two registers' lanes. -/
def regsCode (r : Registers K) : ℕ := r.pc.lane.toNat * 2 ^ 64 + r.fp.lane.toNat

theorem regsCode_lt (r : Registers K) : regsCode r < replayFuel := by
  have h1 : r.pc.lane.toNat < 18446744073709551616 := UInt64.toNat_lt_size _
  have h2 : r.fp.lane.toNat < 18446744073709551616 := UInt64.toNat_lt_size _
  unfold regsCode replayFuel
  rw [show (2 : ℕ) ^ 128 = 18446744073709551616 * 18446744073709551616 by norm_num,
    show (2 : ℕ) ^ 64 = 18446744073709551616 by norm_num]
  omega

theorem regsCode_injective : Function.Injective regsCode := by
  intro r r' h
  have h1 : r.fp.lane.toNat < 18446744073709551616 := UInt64.toNat_lt_size _
  have h2 : r'.fp.lane.toNat < 18446744073709551616 := UInt64.toNat_lt_size _
  unfold regsCode at h
  rw [show (2 : ℕ) ^ 64 = 18446744073709551616 by norm_num] at h
  have hp : r.pc.lane.toNat = r'.pc.lane.toNat := by omega
  have hf : r.fp.lane.toNat = r'.fp.lane.toNat := by omega
  exact regs_ext (K.lane_injective (UInt64.toNat_inj.mp hp)) (K.lane_injective (UInt64.toNat_inj.mp hf))

/-- **A halting run from `(g^0, 1)` takes fewer than `2^128` steps**: it never repeats a state
(`run_injective`), and there are at most `2^128` states. -/
theorem steps_lt_replayFuel {T : ℕ} (hv : run prog L T Registers.initial = some (Registers.final prog)) :
    T < replayFuel := by
  have hsome : ∀ i ≤ T, ∃ r, run prog L i Registers.initial = some r := by
    intro i hi
    rcases hi.lt_or_eq with hi | rfl
    · obtain ⟨r, hr, -⟩ := run_intermediate hv hi
      exact ⟨r, hr⟩
    · exact ⟨_, hv⟩
  let code : Fin (T + 1) → Fin replayFuel := fun i ↦
    ⟨((run prog L i Registers.initial).map regsCode).getD 0, by
      obtain ⟨r, hr⟩ := hsome i (by omega)
      rw [hr]
      exact regsCode_lt r⟩
  have hinj : Function.Injective code := by
    intro i j hij
    obtain ⟨r, hr⟩ := hsome i (by omega)
    obtain ⟨r', hr'⟩ := hsome j (by omega)
    have hc : regsCode r = regsCode r' := by
      have := congrArg Fin.val hij
      simp only [code, hr, hr', Option.map_some, Option.getD_some] at this
      exact this
    obtain rfl := regsCode_injective hc
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact run_injective hv hlt (by omega) hr hr'
    · exact run_injective hv hlt (by omega) hr' hr
  have := Fintype.card_le_of_injective code hinj
  simp only [Fintype.card_fin] at this
  omega

end Replay

/-! ## The precondition, decided -/

/-- **Function `j`'s self test at frame `fp`**: `j` is a callee (`2 ≤ j < nFns`), and if it is a
registered loop helper (`guestRegistered`), its frame holds its own pointer in the cell past its
arguments. The back end's precondition `World.Pre` but for the jump table, which the run writes
first, and what its callers are asked for (`guestU`), which reads only the argument words. -/
def selfTest (rd : Reader) (j : ℕ) (fp : K) : Bool :=
  decide (2 ≤ j) && decide (j < nFns) &&
    if guestRegistered.getD j 0 = 1 then decide (wordWith rd fp (2 + guestArgCounts.getD j 0) = ofK fp)
    else true

section Tests

variable {κ : ℕ} {L : MemoryImage κ} {fp : K}

/-- **The decided test is the back end's self pointer**, for a function `1 ≤ j < nFns`. -/
theorem selfTest_iff {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    selfTest L.read j fp = true ↔ 2 ≤ j ∧ ((guestW L).registered (coreOf j).name →
      LeanVM.Compiler.wd L fp (2 + (coreOf j).params.length) = ofK fp) := by
  have hg : guestRegistered.getD j 0 = 1 ↔
      (LeanVM.Compiler.isLoopName (coreOf j).name && (infoOf j).2.2.1) = true := by
    rw [← guestRegistered_eq j h1 h2, beq_iff_eq]
  have hr := LeanVM.Guest.Compiled.registered_tfOf (L := L) LeanVM.Guest.Compiled.guest_compiles h1 h2
  rw [← hg] at hr
  unfold selfTest
  rw [guestArgCounts_coreOf h2]
  by_cases hx : guestRegistered.getD j 0 = 1
  · have hreg : (guestW L).registered (coreOf j).name := hr.mpr hx
    rw [ite_eq_left hx]
    simp only [Bool.and_eq_true, decide_eq_true_eq, h2, and_true]
    exact ⟨fun ⟨a, b⟩ => ⟨a, fun _ => b⟩, fun ⟨a, b⟩ => ⟨a, b hreg⟩⟩
  · have hreg : ¬ (guestW L).registered (coreOf j).name := fun h => hx (hr.mp h)
    rw [ite_eq_right hx]
    simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, h2, and_true]
    exact ⟨fun a => ⟨a, fun h => absurd h hreg⟩, fun ⟨a, _⟩ => a⟩

end Tests

/-! ## The replayed frame map -/

/-- **Function `j` was entered at the state `r` on the words `args`, `rets`**, decided: `r` is at
`j`'s entry, `j` is named `f`, its self test passes at `r`'s frame, and the frame's argument and
return words are `args` and `rets`. -/
noncomputable def enteredTest (rd : Reader) (f : String) (args rets : List E) (r : Registers K)
    (j : ℕ) : Bool :=
  decide (r.pc = addressOfIndex (guestEntries.getD j 0)) && decide ((coreOf j).name = f) &&
    selfTest rd j r.fp &&
    decide (wordsWith rd r.fp 2 (guestArgCounts.getD j 0) = args) &&
    decide (wordsWith rd r.fp (2 + guestArgCounts.getD j 0) (guestRetCounts.getD j 0) = rets)

/-- **The first frame of `states` at which a function named `f` was entered on `args`, `rets`**. -/
noncomputable def firstEntered (states : List (Registers K)) (rd : Reader) (f : String)
    (args rets : List E) : Option K :=
  states.findSome? fun r ↦ if (List.range nFns).any (enteredTest rd f args rets r) then some r.fp else none

/-- The frame map of the states `states`, read with `rd`: a call's valuation is that by the
callee's places (`guestPlaces`) of the first frame of `states` its callee was entered at on the
call's words. -/
noncomputable def frameVWith (states : List (Registers K)) (rd : Reader) : FrameMap :=
  fun f args rets ↦ match firstEntered states rd f args rets with
    | some fp => fun v ↦ placeWith rd fp ((guestPlaces.getD (nameIndex f) #[]).getD v.idx 0)
    | none => fun _ ↦ 0

/-- **The replayed frame map of the memory `L`**: the run from `(g^0, 1)` replayed through the
indices of the addresses, a call's valuation that of the first frame the run entered its callee
at on the call's words. -/
noncomputable def replayFrameV {κ : ℕ} (L : MemoryImage κ) : FrameMap :=
  frameVWith (statesIn (powIndex κ) (powIndex guestProgram.logSize) guestProgram L replayFuel ⟨addressOfIndex 0, 1⟩)
    (readIn (powIndex κ) L)

/-- **The places of the guest's values, decoded from the table**: on every value of function `j`'s
parameters and body, its code in function `j`'s row of `guestPlaces` (by the value's index), read
by `placeWith`, is the guest world's valuation by places. -/
def PlacesAgree : Prop :=
  ∀ j, 1 ≤ j → j < nFns → ∀ {κ : ℕ} (L : MemoryImage κ) (fp : K),
    ∀ v ∈ (coreOf j).params ++ Stmt.valsList (coreOf j).body,
      placeWith L.read fp ((guestPlaces.getD j #[]).getD v.idx 0) = (guestW L).vf (coreOf j).name fp v

/-- **The located relation unfolds along the replayed frame map**, on a valid execution: the frame
the replay finds for a call is one the run entered the callee at, its self test passing and its
words the call's, so the callee's contract gives its body there. -/
theorem unfoldsV_replay (hpa : PlacesAgree) {input : PublicInput} {t : Execution guestProgram}
    (hv : ValidExecution guestProgram input t) :
    UnfoldsV t.memory.read (RLg t.memory) (replayFrameV t.memory) := by
  obtain ⟨κ, L, T⟩ := t
  have h16 : minLogMem ≤ κ := hv.1.1
  have h32 : κ ≤ maxLogMem := hv.1.2.1
  have hκ : κ < 64 := by unfold maxLogMem at h32; omega
  have hS : ∀ r, stepIn (powIndex κ) (powIndex guestProgram.logSize) guestProgram L r = step guestProgram L r :=
    stepIn_powIndex hκ L
  have hT : run guestProgram L T ⟨addressOfIndex 0, 1⟩ = some (Registers.final guestProgram) :=
    safe_of_validExecution hv
  have hTi : run guestProgram L T Registers.initial = some (Registers.final guestProgram) := hv.2
  have hfuel : T ≤ replayFuel := (steps_lt_replayFuel hTi).le
  have hV : replayFrameV L = frameVWith (statesIn (powIndex κ) (powIndex guestProgram.logSize) guestProgram L
      replayFuel ⟨addressOfIndex 0, 1⟩) L.read := by
    rw [replayFrameV, readIn_powIndex hκ]
  set states := statesIn (powIndex κ) (powIndex guestProgram.logSize) guestProgram L replayFuel ⟨addressOfIndex 0, 1⟩
  show UnfoldsV L.read (RLg L) (replayFrameV L)
  rw [hV]
  intro f args rets h
  rw [RLg_eq] at h
  obtain ⟨-, fp, -, ⟨-, hpre, ⟨n, hn⟩, tf, htf, hname, hw1, hw2⟩, -, -⟩ :=
    (relL_iff coreProgram f args rets).mp h
  obtain ⟨j, hj1, hj2, rfl⟩ := mem_guestTraced htf
  obtain rfl : (coreOf j).name = f := hname
  have hj2' : 2 ≤ j := by
    by_contra hlt
    obtain rfl : j = 1 := by omega
    exact hpre.1 core0_main.1
  have hent : (guestW L).ent (coreOf j).name = guestEntries.getD j 0 := by
    rw [guestEntries_fnOf hj2]
    exact ent_eq LeanVM.Guest.Compiled.guest_compiles hj1 hj2
  have hprog : (guestW L).prog = guestProgram := LeanVM.Guest.Compiled.guestWorld_prog LeanVM.Guest.Compiled.guest_compiles
  rw [hent, hprog] at hn
  have hargs : guestArgCounts.getD j 0 = (coreOf j).params.length := guestArgCounts_coreOf hj2
  have hrets : guestRetCounts.getD j 0 = (infoOf j).2.1 := guestRetCounts_eq j hj1 hj2
  obtain ⟨tf', htf', hnm, hreg, hU⟩ := hpre.2.2
  obtain rfl := tf_eq L LeanVM.Guest.Compiled.guest_compiles htf' hj1 hj2 hnm
  -- the run entered `j` at `fp`: a candidate
  have hmem : (⟨addressOfIndex (guestEntries.getD j 0), fp⟩ : Registers K) ∈ states :=
    mem_statesIn hS hn ((run_le_of_halts hT hn).trans hfuel)
  have htest : enteredTest L.read (coreOf j).name args rets
      ⟨addressOfIndex (guestEntries.getD j 0), fp⟩ j = true := by
    have hs : selfTest L.read j fp = true := (selfTest_iff hj1 hj2).mpr ⟨hj2', hreg⟩
    simp only [enteredTest, Bool.and_eq_true, decide_eq_true_eq, and_true, true_and, hs]
    exact ⟨by rw [hargs]; exact hw1.symm, by rw [hargs, hrets]; exact hw2.symm⟩
  -- the replay finds a frame
  obtain ⟨fp', hfirst⟩ : ∃ fp', firstEntered states L.read (coreOf j).name args rets = some fp' := by
    unfold firstEntered
    rcases hs : states.findSome? (fun r ↦ if (List.range nFns).any
        (enteredTest L.read (coreOf j).name args rets r) then some r.fp else none) with _ | fp'
    · have := List.findSome?_eq_none_iff.mp hs _ hmem
      rw [ite_eq_left (List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj2, htest⟩)] at this
      cases this
    · exact ⟨fp', rfl⟩
  obtain ⟨r, hr, hsome⟩ := List.exists_of_findSome?_eq_some hfirst
  split at hsome
  · rename_i hany
    obtain rfl := Option.some.inj hsome
    obtain ⟨j', hj', htest'⟩ := List.any_eq_true.mp hany
    have hj'2 : j' < nFns := List.mem_range.mp hj'
    simp only [enteredTest, Bool.and_eq_true, decide_eq_true_eq] at htest'
    obtain ⟨⟨⟨⟨hpc, hname'⟩, hself'⟩, hw1'⟩, hw2'⟩ := htest'
    have hj'1 : 2 ≤ j' := by
      simp only [selfTest, Bool.and_eq_true, decide_eq_true_eq] at hself'
      exact hself'.1.1
    obtain rfl : j = j' := coreOf_name_inj hj1 hj2 (by omega) hj'2 hname'.symm
    rw [hargs] at hw1'
    rw [hargs, hrets] at hw2'
    have hself := ((selfTest_iff hj1 hj2).mp hself').2
    have hpre' : (guestW L).Pre (coreOf j).name r.fp := by
      refine ⟨hpre.1, hpre.2.1, tfOf j, getElem_mem_guestTraced hj1 hj2, rfl, hself, ?_⟩
      have hw : LeanVM.Compiler.frameWords L r.fp 2 (coreOf j).params.length =
          LeanVM.Compiler.frameWords L fp 2 (coreOf j).params.length := hw1'.trans hw1
      show (guestW L).U (coreOf j).name (LeanVM.Compiler.frameWords L r.fp 2 (coreOf j).params.length)
      rw [hw]
      exact hU
    obtain ⟨n', hrun⟩ := run_of_mem_statesIn hS hr
    have hreg' : r = ⟨addressOfIndex ((guestW L).ent (coreOf j).name), r.fp⟩ := by
      rw [hent]; exact regs_ext hpc rfl
    rw [hreg'] at hrun
    have hsr : SafeReached guestProgram L (T - n')
        ⟨addressOfIndex ((guestW L).ent (coreOf j).name), r.fp⟩ :=
      ⟨safe_of_halts hT hrun, ⟨n', hrun⟩⟩
    obtain ⟨-, -, -, -, ⟨tf'', htf'', hnm', hbody, -⟩, -⟩ :=
      End.globSpec h16 h32 (coreOf j).name r.fp (T - n') hpre' hsr
    obtain rfl := tf_eq L LeanVM.Guest.Compiled.guest_compiles htf'' hj1 hj2 hnm'
    have hrow : frameVWith states L.read (coreOf j).name args rets =
        fun v ↦ placeWith L.read r.fp ((guestPlaces.getD j #[]).getD v.idx 0) := by
      simp only [frameVWith, hfirst, nameIndex_coreOf hj1 hj2]
    have hagree := hpa j hj1 hj2 L r.fp
    refine ⟨coreOf j, coreOf_find hj1 hj2, ?_, ?_⟩
    · rw [hrow, ← hw1', List.map_congr_left fun v hv => hagree v (List.mem_append_left _ hv)]
      exact hbody.1
    · rw [hrow, ← hw2', B1.Sig.holdsList_congr _ fun v hv => hagree v (List.mem_append_right _ hv)]
      exact hbody.2
  · cases hsome

end
end LeanVM.Guest.Located
