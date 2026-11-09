/-
  LeanVM.Guest.Located.Replay

  The frame map of a valid execution, by replaying its run: a call's valuation is that of the
  first frame at which the run entered the callee on the call's words.
-/

module

public import LeanVM.Guest.EndLoc
public import LeanVM.Guest.SoundFacts
public import LeanVM.Guest.Located.Interface
public import LeanVM.Protocol.Extraction.Run

/-!
# The replayed frame map

B2 locates every call of `main`'s body at a frame the run from `(g^0, 1)` entered the callee at,
its precondition holding there and its argument and return cells holding the call's words
(`Check.EnteredAt`). The frame map `replayFrameV L` finds such a frame by replaying the run: it
steps the machine from `(g^0, 1)` (`statesIn`, reading the memory and the bytecode through the
indices of their addresses, `Extraction.powIndex`), and gives a call `f args rets` the valuation
of the first state that is the entry of a function named `f`, whose precondition holds at the
state's frame (`preTest`, decided) and whose frame's argument and return cells hold `args` and
`rets` (`enteredTest`). It chooses nothing: every test is decided by evaluation.

* `statesIn`: the run's states; `mem_statesIn`, `run_of_mem_statesIn`: they are the states the run
  reaches, within the fuel. `steps_lt_replayFuel`: a halting run from `(g^0, 1)` takes fewer
  than `2^128` steps (it never repeats a state, `Protocol.Halting.run_injective`), so the replay
  with `replayFuel = 2^128` sees every state of a valid execution.
* `preTest_iff`: the decided precondition is `Check.Pre`, the jump table and the semantic tuples
  given (those read only the argument words, `End.sigSem_args`, so they carry over between frames
  of one call, `semHolds_of_args`).
* **`unfoldsV_replay`**: on a valid execution, the located relation `RLg` unfolds along the
  replayed frame map: the frame the replay finds is one the run entered, so the callee's contract
  (`End.globSpec`) gives its body there.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.Exec LeanVM.Guest.B1 LeanVM.Extraction LeanVM.Protocol.Halting

@[expose] public section

/-! ## The memory, read through an index -/

/-- The word at address `a`, its index looked up in `idx`. -/
def readIn (idx : Std.HashMap UInt64 ℕ) {κ : ℕ} (L : MemoryImage κ) (a : K) : Option E :=
  (gLogIn idx κ a).map L

/-- Through the index of the `2^κ` addresses, `κ < 64`, the read is the memory's. -/
theorem readIn_powIndex {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    readIn (powIndex κ) L = L.read :=
  funext fun a ↦ by rw [readIn, gLogIn_powIndex hκ]; rfl

/-- The word in cell `o` of the frame `fp`, read with `rd`, `0` if none (`Check.wd`). -/
def wordWith (rd : Reader) (fp : K) (o : ℕ) : E := (rd (fp * addressOfIndex o)).getD 0

/-- The `n` words of the frame `fp` from cell `o`, read with `rd` (`Check.frameWords`). -/
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

/-- The entry environment holds of the frame, decided: every key the environment lists. -/
noncomputable def envTest (rd : Reader) (fp : K) (env : List (ℕ × Sym)) : Bool :=
  env.all fun p ↦ match (envOf env).get p.1 with
    | some v => decide (rd (fp * addressOfIndex p.1) = some (v.val fp))
    | none => true

/-- The bounds hold, decided. -/
def bndTest (rd : Reader) (fp : K) (bnd : List (ℕ × ℕ)) : Bool :=
  bnd.all fun p ↦ (List.range p.2).any fun e ↦ decide (rd (fp * addressOfIndex p.1) = some (ofK
      (addressOfIndex e)))

/-- The memory bounds hold, decided. -/
def memTest (rd : Reader) (fp : K) (mem : List (ℕ × ℕ × ℕ)) : Bool :=
  mem.all fun m ↦ match rd (fp * addressOfIndex m.1) with
    | some p => decide (IsInK p) &&
        (List.range m.2.2).any fun e ↦ decide (rd (p.limb 0 * addressOfIndex m.2.1) = some (ofK
            (addressOfIndex e)))
    | none => false

/-- **Function `j`'s precondition at frame `fp`, decided**, but for the jump table, which the run
writes first, and the semantic tuples (`Check.Pre`): those are on argument cells (`sigSem_args`),
and the replay matches the call's argument words, so they carry over from the frame B2 locates
(`semHolds_of_args`). -/
noncomputable def preTest (rd : Reader) (j : ℕ) (fp : K) : Bool :=
  glob.good j && envTest rd fp (glob.sig j).env && bndTest rd fp (glob.sig j).pre &&
    memTest rd fp (glob.sig j).mem

theorem envOf_get_mem {env : List (ℕ × Sym)} {n : ℕ} {v : Sym} (h : (envOf env).get n = some v) :
    n ∈ env.map Prod.fst := by
  unfold envOf at h
  suffices ∀ (l : List (ℕ × Sym)) (t : Trie Sym),
      (l.foldl (fun t p ↦ t.set p.2 envDepth p.1) t).get n = some v →
        n ∈ l.map Prod.fst ∨ t.get n = some v by
    rcases this env .nil h with h | h
    · exact h
    · simp at h
  intro l
  induction l with
  | nil => exact fun _ h ↦ Or.inr h
  | cons p l ih =>
    intro t h
    rcases ih _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases Trie.get_set h with ⟨rfl, -⟩ | h
      · exact Or.inl List.mem_cons_self
      · exact Or.inr h

section Tests

variable {κ : ℕ} {L : MemoryImage κ} {fp : K}

theorem envTest_iff {env : List (ℕ × Sym)} : envTest L.read fp env = true ↔ EnvHolds L fp (envOf env) := by
  unfold envTest
  rw [List.all_eq_true]
  constructor
  · intro h n v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (envOf_get_mem hv)
    have := h p hp
    rw [hv] at this
    exact of_decide_eq_true this
  · intro h p _
    split
    · rename_i v hv
      exact decide_eq_true (h _ _ hv)
    · rfl

theorem bndTest_iff {bnd : List (ℕ × ℕ)} : bndTest L.read fp bnd = true ↔ BndHolds L fp bnd := by
  simp [bndTest, BndHolds, List.all_eq_true, List.any_eq_true, List.mem_range]

theorem memTest_iff {mem : List (ℕ × ℕ × ℕ)} : memTest L.read fp mem = true ↔ MemPre L fp mem := by
  unfold memTest MemPre
  simp only [List.all_eq_true]
  refine forall_congr' fun m ↦ forall_congr' fun _ ↦ ?_
  split
  · rename_i p hp
    simp [hp, List.any_eq_true, List.mem_range]
  · rename_i hp
    simp [hp]

/-- **The decided precondition is `Check.Pre`**, the jump table and the semantic tuples holding. -/
theorem preTest_iff (hjt : JTHolds glob L) {j : ℕ} (hsem : SemHolds glob L fp (glob.sig j).sem) :
    preTest L.read j fp = true ↔ Pre glob L j fp := by
  unfold preTest Pre
  simp only [Bool.and_eq_true, envTest_iff, bndTest_iff, memTest_iff]
  exact ⟨fun ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ ↦ ⟨h1, hjt, h2, h3, h4, hsem⟩,
    fun ⟨h1, _, h2, h3, h4, _⟩ ↦ ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩

theorem frameWords_getD {n o : ℕ} (h1 : 2 ≤ o) (h2 : o < 2 + n) :
    (frameWords L fp 2 n).getD (o - 2) 0 = wd L fp o := by
  rw [List.getD_eq_getElem _ _ (by simp [frameWords]; omega)]
  simp only [frameWords, List.getElem_map, List.getElem_range]
  congr 1
  omega

/-- **Semantic tuples on argument cells carry over** between frames holding the same argument
words: a tuple's relation reads only the memory and the tuple's words. -/
theorem semHolds_of_args {fp' : K} {n : ℕ} {sems : List (ℕ × List ℕ)}
    (hcells : ∀ s ∈ sems, ∀ o ∈ s.2, 2 ≤ o ∧ o < 2 + n)
    (hargs : frameWords L fp 2 n = frameWords L fp' 2 n) (h : SemHolds glob L fp sems) :
    SemHolds glob L fp' sems := by
  intro s hs
  have hw : s.2.map (wd L fp') = s.2.map (wd L fp) := List.map_congr_left fun o ho ↦ by
    obtain ⟨h1, h2⟩ := hcells s hs o ho
    rw [← frameWords_getD h1 h2, ← frameWords_getD h1 h2, hargs]
  rw [hw]
  exact h s hs

end Tests

/-! ## The replayed frame map -/

/-- **Function `j` was entered at the state `r` on the words `args`, `rets`**, decided: `r` is at
`j`'s entry, `j` is named `f`, its precondition holds at `r`'s frame (but the jump table), and the
frame's argument and return cells hold `args` and `rets`. -/
noncomputable def enteredTest (rd : Reader) (f : String) (args rets : List E) (r : Registers K)
    (j : ℕ) : Bool :=
  decide (r.pc = addressOfIndex (glob.sig j).entry) && decide ((glob.sig j).name = f) && preTest rd
      j r.fp &&
    decide (wordsWith rd r.fp 2 (glob.sig j).nargs = args) &&
    decide (wordsWith rd r.fp (2 + (glob.sig j).nargs) (glob.sig j).nret = rets)

/-- **The first frame of `states` at which a function named `f` was entered on `args`, `rets`**. -/
noncomputable def firstEntered (states : List (Registers K)) (rd : Reader) (f : String)
    (args rets : List E) : Option K :=
  states.findSome? fun r ↦ if (List.range nFns).any (enteredTest rd f args rets r) then some r.fp else none

/-- The frame map of the states `states`, read with `rd`: a call's valuation is that of the first
frame of `states` its callee was entered at on the call's words. -/
noncomputable def frameVWith (states : List (Registers K)) (rd : Reader) : FrameMap :=
  fun f args rets ↦ match firstEntered states rd f args rets with
    | some fp => fun v ↦ wordWith rd fp ((certByName f).locs.getD v.idx 0)
    | none => fun _ ↦ 0

/-- **The replayed frame map of the memory `L`**: the run from `(g^0, 1)` replayed through the
indices of the addresses, a call's valuation that of the first frame the run entered its callee
at on the call's words. -/
noncomputable def replayFrameV {κ : ℕ} (L : MemoryImage κ) : FrameMap :=
  frameVWith (statesIn (powIndex κ) (powIndex guestProgram.logSize) guestProgram L replayFuel ⟨addressOfIndex 0, 1⟩)
    (readIn (powIndex κ) L)

/-- **The located relation unfolds along the replayed frame map**, on a valid execution: the frame
the replay finds for a call is one the run entered the callee at, its precondition holding and its
cells holding the call's words, so the callee's contract gives its body there. -/
theorem unfoldsV_replay (hb2 : End.B2SoundL) {input : PublicInput} {t : Execution guestProgram}
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
  have hjt : JTHolds glob L := End.jtHolds_of (End.safe_jumpTables hT).1
  have hfuel : T ≤ replayFuel := (steps_lt_replayFuel hTi).le
  have hV : replayFrameV L = frameVWith (statesIn (powIndex κ) (powIndex guestProgram.logSize) guestProgram L
      replayFuel ⟨addressOfIndex 0, 1⟩) L.read := by
    rw [replayFrameV, readIn_powIndex hκ]
  set states := statesIn (powIndex κ) (powIndex guestProgram.logSize) guestProgram L replayFuel ⟨addressOfIndex 0, 1⟩
  show UnfoldsV L.read (RLg L) (replayFrameV L)
  rw [hV]
  intro f args rets h
  obtain ⟨fn, fp, hfind, ⟨-, j, hname, hpre, ⟨n, hn⟩, hw1, hw2⟩, -, -⟩ :=
    (relL_iff coreProgram f args rets).mp h
  -- the run entered `j` at `fp`: a candidate
  have hmem : (⟨addressOfIndex (glob.sig j).entry, fp⟩ : Registers K) ∈ states :=
    mem_statesIn hS hn ((run_le_of_halts hT hn).trans hfuel)
  have hj : j < nFns := by
    have := hpre.1
    simp only [glob, good, Bool.and_eq_true, Nat.blt_eq] at this
    exact this.2
  have htest : enteredTest L.read f args rets ⟨addressOfIndex (glob.sig j).entry, fp⟩ j = true := by
    simp only [enteredTest, Bool.and_eq_true]
    exact ⟨⟨⟨⟨by simp, decide_eq_true hname⟩, (preTest_iff hjt hpre.2.2.2.2.2).mpr hpre⟩,
      decide_eq_true hw1⟩, decide_eq_true hw2⟩
  -- the replay finds a frame
  obtain ⟨fp', hfirst⟩ : ∃ fp', firstEntered states L.read f args rets = some fp' := by
    unfold firstEntered
    rcases hs : states.findSome? (fun r ↦ if (List.range nFns).any (enteredTest L.read f args rets r)
        then some r.fp else none) with _ | fp'
    · have := List.findSome?_eq_none_iff.mp hs _ hmem
      rw [ite_eq_left (List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, htest⟩)] at this
      cases this
    · exact ⟨fp', rfl⟩
  obtain ⟨r, hr, hsome⟩ := List.exists_of_findSome?_eq_some hfirst
  split at hsome
  · rename_i hany
    obtain rfl := Option.some.inj hsome
    obtain ⟨j', -, htest'⟩ := List.any_eq_true.mp hany
    simp only [enteredTest, Bool.and_eq_true] at htest'
    obtain ⟨⟨⟨⟨hpc, hname'⟩, hpre'⟩, hw1'⟩, hw2'⟩ := htest'
    have hpc : r.pc = addressOfIndex (glob.sig j').entry := of_decide_eq_true hpc
    have hname' : (glob.sig j').name = f := of_decide_eq_true hname'
    have hw1' : frameWords L r.fp 2 (glob.sig j').nargs = args := of_decide_eq_true hw1'
    have hw2' : frameWords L r.fp (2 + (glob.sig j').nargs) (glob.sig j').nret = rets :=
      of_decide_eq_true hw2'
    have hgood : glob.good j' = true := by
      simp only [preTest, Bool.and_eq_true] at hpre'
      exact hpre'.1.1.1
    have hj' : 2 ≤ j' ∧ j' < nFns := by simpa [glob, good] using hgood
    have hj2 : 2 ≤ j := by
      have := hpre.1
      simp only [glob, good, Bool.and_eq_true, Nat.ble_eq] at this
      exact this.1
    obtain rfl : j' = j := End.sig_name_inj (by omega) hj'.2 (by omega) hj (hname'.trans hname.symm)
    have hpre'' := (preTest_iff hjt (semHolds_of_args (End.sigSem_args hj) (hw1.trans hw1'.symm)
      hpre.2.2.2.2.2)).mp hpre'
    obtain ⟨n', hn'⟩ := run_of_mem_statesIn hS hr
    have hreg : r = ⟨addressOfIndex (glob.sig j').entry, r.fp⟩ := regs_ext hpc rfl
    rw [hreg] at hn'
    obtain ⟨-, -, -, -, ⟨⟨fn', hfind', hp', hb'⟩, -, -⟩, -⟩ :=
      End.globSpec hb2 h16 h32 j' r.fp (T - n') hpre'' ⟨safe_of_halts hT hn', ⟨n', hn'⟩⟩
    rw [hname'] at hfind' hp' hb'
    rw [hw1'] at hp'
    rw [hw2'] at hb'
    refine ⟨fn', hfind', ?_, ?_⟩
    · simp only [frameVWith, hfirst]
      exact hp'
    · simp only [frameVWith, hfirst]
      exact hb'
  · cases hsome

end
end LeanVM.Guest.Located
