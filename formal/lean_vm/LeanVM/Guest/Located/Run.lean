/-
  LeanVM.Guest.Located.Run

  The run of a memory replayed through the address indices and tables, and a discrete logarithm's
  readers: the parts of the replayed frame map that name no certificate.
-/

module

public import LeanVM.Guest.Logic
public import LeanVM.Guest.B1.Main.Facts
public import LeanVM.Protocol.Extraction.Run
public import LeanVM.Protocol.Extraction.Fast.Address

/-!
# The run, replayed

* `statesIn`, `statesTable`: the states of the run from a state, stepped through the address
  indices (`Extraction.powIndex`) or their sorted tables (`Extraction.Fast.powTable`), equal on at
  most `2^63` words (`statesTable_eq`); `mem_statesIn`, `run_of_mem_statesIn`: they are the states
  the run reaches, within the fuel; `steps_lt_replayFuel`: a halting run from `(g^0, 1)` takes
  fewer than `2^128` steps (it never repeats a state), so the replay with `replayFuel = 2^128` sees
  every state of a valid execution.
* `readIn`, `readTable`: the memory read through the index or the table (`readIn_powIndex`,
  `readTable_powTable`).
* **A discrete logarithm.** `DiscreteLogSpec dl`: `dl x = some n` exactly when `x = g^n`,
  `n < 2^64 − 1` (the order of `g`). Given one, `∃ e < n, g^e = x` is `dl x < n`
  (`exists_lt_gpow_iff`, `isPowBelow_iff`), and `gLogWith dl` is `B1.Main.gLog` (`gLogWith_eq`).
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.B1 LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol.Halting

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

/-! ## The memory and the run, through the address tables -/

section Tables

/-- The word at address `a`, its index found by binary search in the address table `t`
(`Extraction.Fast.gLogTable`, the extractor's). -/
def readTable (t : Array (ℕ × ℕ)) {κ : ℕ} (L : MemoryImage κ) (a : K) : Option E :=
  (gLogTable t κ a).map L

/-- Through the table of the `2^κ` addresses, `κ < 64`, the read is the memory's. -/
theorem readTable_powTable {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    readTable (powTable κ) L = L.read := by
  funext a
  rw [readTable, gLogTable_eq hκ]
  exact congrFun (readIn_powIndex hκ L) a

/-- **The states of the run from `r`, through the address tables** (`statesIn`): each step the
extractor's `stepTable` (its compiled `stepVec` on the memory's vector). -/
def statesTable (memT codeT : Array (ℕ × ℕ)) (prog : Semantics.LeanIsaProgram) {κ : ℕ}
    (L : MemoryImage κ) : ℕ → Registers K → List (Registers K)
  | 0, r => [r]
  | n + 1, r => r :: if r = Registers.final prog then [] else
      match stepTable memT codeT prog L r with
      | some r' => statesTable memT codeT prog L n r'
      | none => []

/-- Through the tables, on at most `2^63` words, the replay is `statesIn`'s. -/
theorem statesTable_eq {prog : Semantics.LeanIsaProgram} {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    ∀ fuel r, statesTable (powTable κ) (powTable prog.logSize) prog L fuel r =
      statesIn (powIndex κ) (powIndex prog.logSize) prog L fuel r
  | 0, r => rfl
  | fuel + 1, r => by
    rw [statesTable, statesIn, stepTable_eq hκ]
    congr 1
    split
    · rfl
    · cases stepIn (powIndex κ) (powIndex prog.logSize) prog L r with
      | none => rfl
      | some r' => exact statesTable_eq hκ L fuel r'

end Tables

/-! ## Discrete logarithms -/

/-- **A discrete logarithm of `K*`**: `dl x = some n` exactly when `x = g^n` with `n` below the
order `2^64 − 1` of `g`. -/
def DiscreteLogSpec (dl : K → Option ℕ) : Prop :=
  ∀ x n, dl x = some n ↔ addressOfIndex n = x ∧ n < 2 ^ 64 - 1

theorem gpow_mod_order (e : ℕ) : addressOfIndex (e % (2 ^ 64 - 1)) = addressOfIndex e := by
  show Parameters.g ^ _ = Parameters.g ^ _
  rw [← orderOf_g, pow_mod_orderOf]

section Log

variable {dl : K → Option ℕ}

/-- With a discrete logarithm, `x` is a power `g^e` with `e < n` exactly when its logarithm is
below `n`. -/
theorem exists_lt_gpow_iff (hdl : DiscreteLogSpec dl) (x : K) (n : ℕ) :
    (∃ e < n, addressOfIndex e = x) ↔ ∃ m, dl x = some m ∧ m < n := by
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e % (2 ^ 64 - 1), (hdl _ _).mpr ⟨gpow_mod_order e, Nat.mod_lt _ (by norm_num)⟩,
      lt_of_le_of_lt (Nat.mod_le _ _) he⟩
  · rintro ⟨m, hm, hmn⟩
    exact ⟨m, hmn, ((hdl _ _).mp hm).1⟩

/-- `w` is the word `g^e` of some `e < n`, by the logarithm. -/
def isPowBelow (dl : K → Option ℕ) (w : E) (n : ℕ) : Bool :=
  decide (IsInK w) && match dl (w.limb 0) with
    | some m => decide (m < n)
    | none => false

theorem isPowBelow_iff (hdl : DiscreteLogSpec dl) (w : E) (n : ℕ) :
    isPowBelow dl w n = true ↔ ∃ e < n, w = ofK (addressOfIndex e) := by
  unfold isPowBelow
  rw [Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨hK, h⟩
    rcases hm : dl (w.limb 0) with _ | m
    · rw [hm] at h; cases h
    · rw [hm, decide_eq_true_iff] at h
      refine ⟨m, h, ?_⟩
      rw [eq_ofK_limb hK, ((hdl _ _).mp hm).1]
  · rintro ⟨e, he, rfl⟩
    refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
    obtain ⟨m, hm, hmn⟩ := (exists_lt_gpow_iff hdl (addressOfIndex e) n).mp ⟨e, he, rfl⟩
    have h0 : (ofK (addressOfIndex e)).limb 0 = addressOfIndex e := by simp [limb_ofK]
    rw [h0, hm]
    exact decide_eq_true hmn

theorem any_range_pow_iff (hdl : DiscreteLogSpec dl) (o : Option E) (n : ℕ) :
    ((List.range n).any fun e ↦ decide (o = some (ofK (addressOfIndex e)))) =
      match o with
      | some w => isPowBelow dl w n
      | none => false := by
  rcases o with _ | w
  · simp
  · apply Bool.eq_iff_iff.mpr
    rw [isPowBelow_iff hdl, List.any_eq_true]
    simp only [List.mem_range, decide_eq_true_eq, Option.some.injEq]

/-- B1's exponent of a power of `g` below `2^34` (`B1.Main.gLog`), by the logarithm. -/
def gLogWith (dl : K → Option ℕ) (x : E) : ℕ :=
  match dl (x.limb 0) with
  | some n => if n < 2 ^ 34 then n else 0
  | none => 0

/-- **By the logarithm, the exponent is `B1.Main.gLog`.** -/
theorem gLogWith_eq (hdl : DiscreteLogSpec dl) : gLogWith dl = B1.Main.gLog := by
  funext x
  unfold B1.Main.gLog gLogWith
  rw [B1.Main.indexSearch_eq (by norm_num)]
  rcases hm : dl (x.limb 0) with _ | n
  · have : addressIndex? 34 (x.limb 0) = none := by
      refine gLog?_eq_none_iff.mpr fun i hi ↦ ?_
      have := (hdl _ i).mpr ⟨hi.symm, by have := i.isLt; omega⟩
      rw [hm] at this
      cases this
    rw [this]
    rfl
  · obtain ⟨hn, hlt⟩ := (hdl _ _).mp hm
    show (if n < 2 ^ 34 then n else 0) = _
    by_cases h34 : n < 2 ^ 34
    · rw [ite_eq_left h34, (gLog?_spec (κ := 34) (by norm_num) (i := ⟨n, h34⟩)).mpr hn.symm]
      rfl
    · rw [ite_eq_right h34]
      have : addressIndex? 34 (x.limb 0) = none := by
        refine gLog?_eq_none_iff.mpr fun i hi ↦ h34 ?_
        have hi' : (i : ℕ) < 2 ^ 64 - 1 := by have := i.isLt; omega
        have := gpow_injOn hlt hi' (hn.trans hi)
        rw [this]
        exact i.isLt
      rw [this]
      rfl

end Log

end
end LeanVM.Guest.Located
