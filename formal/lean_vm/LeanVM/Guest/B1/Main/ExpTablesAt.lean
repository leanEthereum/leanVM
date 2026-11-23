/-
  LeanVM.Guest.B1.Main.ExpTablesAt

  `exponent_tables` placed at a frame pointer: its one table after its frame, returned.
-/

module

public import LeanVM.Guest.B1.Bits.Tables
public import LeanVM.Guest.B1.Da.AtBase
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«exponent_tables»
import LeanVM.Guest.LitRef

/-!
# `exponent_tables`, placed

`exponent_tables` allocates one `HeapBuf(236 + 2^11)` from `b = fp + fs "exponent_tables"` and
writes the table and its bit windows there (`expTabAllWords`). `et_at`: on a memory holding them,
it holds at `fp` by its frame and its buffer, returning `g^b` and claiming the buffer.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds limb0_gen_pow_mul)

@[expose] public section

/-- `exponent_tables`' atoms: the table's words, then the returned pointer. -/
def etAs : List Atom :=
  [.hint (.alloc (.n (val% «exponent_tables» "g_squares")) lit% B1.expTabN)] ++ (List.range lit% B1.expTabN).flatMap (fun t =>
    [.const (.n (t + (val% «exponent_tables» "s2.u0.s0#0"))) (word (etWord t) 0), .load (.n (t + (val% «exponent_tables» "s2.u0.s0#0"))) (.n (val% «exponent_tables» "g_squares")) (etOff t)]) ++
  [.copy (.n (val% «exponent_tables» "s8#0")) (.n (val% «exponent_tables» "g_squares"))]

theorem etBlks_eq : ∀ l : List ℕ, (l.map etBlk).flatten = (l.flatMap fun t =>
    [Atom.const (.n (t + 1)) (word (etWord t) 0), .load (.n (t + 1)) (.n (val% «exponent_tables» "g_squares")) (etOff t)]).map Stmt.atom
  | [] => rfl
  | t :: l => by
    simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, etBlks_eq l, etBlk,
      List.cons_append, List.nil_append]

theorem et_split : Fn.body fn% «exponent_tables» = etAs.map Stmt.atom ++ [.ret [.n (val% «exponent_tables» "s8#0")]] := by
  rw [exponent_tables_body, etBody, etBlks_eq, etAs]
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append]

theorem et_straight : (etAs.map Stmt.atom).all Main.Stmt.straight = true := by
  simp [Main.Stmt.straight]

theorem length_expTableWords : expTableWords.length = 236 := by
  simp [expTableWords, length_etWordsN]

/-- The table's first `34` words are the squares `g^(2^j)`. -/
theorem expTableWords_sq {j : ℕ} (hj : j < 34) :
    expTableWords[j]'(by rw [length_expTableWords]; omega) = gen ^ 2 ^ j := by
  rw [← List.getD_eq_getElem _ 0, expTableWords_getD j (by omega), etListK_sq j hj, ofK_pow,
    ← gen_eq_ofK]

/-- The whole table's first `34` words are the squares `g^(2^j)`. -/
theorem expTabAllWords_sq {j : ℕ} (hj : j < 34) :
    expTabAllWords[j]'(by rw [length_expTabAllWords]; omega) = gen ^ 2 ^ j := by
  rw [← List.getD_eq_getElem _ 0, expTabAllWords_getD, ite_pos' (by omega), expTabWord,
    ite_pos' (by omega), List.getD_eq_getElem _ _ (by rw [length_expTableWords]; omega),
    expTableWords_sq hj]

/-- The table's first word at `fp`. -/
abbrev etB (fs : String → ℕ) (fp : ℕ) : ℕ := fp + fs "exponent_tables"

theorem expTables_of_reads {rd : Reader} {b : ℕ} (h : ReadsAt rd (gen ^ b) expTabAllWords) :
    ExpTables rd (gen ^ b) ∧ ExpWinTab rd (gen ^ b) :=
  (expTabAll_iff rd _).2 fun o ho => by
    have := h o (by rw [length_expTabAllWords]; exact ho)
    have e : expTabAllWords[o]'(by rw [length_expTabAllWords]; exact ho) = expTabWord o := by
      rw [← List.getD_eq_getElem _ 0, expTabAllWords_getD, ite_pos' ho]
    rwa [e] at this

set_option maxRecDepth 20000 in
/-- **`exponent_tables` at `fp`**, on a memory holding its table. -/
theorem et_at (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader} {fp : ℕ} {R : ℕ → Prop}
    (hm : ExpTables rd (gen ^ etB fs fp) ∧ ExpWinTab rd (gen ^ etB fs fp)) :
    RelAtIn coreProgram fs cert rd R (fun i => etB fs fp ≤ i ∧ i < etB fs fp + lit% B1.expTabN) fp
      (fs "exponent_tables" + lit% B1.expTabN) "exponent_tables" [] [gen ^ etB fs fp] := by
  have hrel := (exponent_tables_holds rd [] [gen ^ etB fs fp]).mpr hm
  obtain ⟨σ, hp, hh⟩ := (rel_iff_sem find_exponent_tables _ _).mp hrel
  rw [et_split, Digest.holdsList_atoms_ret] at hh
  obtain ⟨hat, hr⟩ := hh
  have h0 : σ (.n (val% «exponent_tables» "g_squares")) = gen ^ etB fs fp := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hr
    rw [← (hat (.copy (.n (val% «exponent_tables» "s8#0")) (.n (val% «exponent_tables» "g_squares"))) (by simp [etAs]) : σ (.n (val% «exponent_tables» "s8#0")) = σ (.n (val% «exponent_tables» "g_squares"))), hr]
  have hw := Main.walk_straight σ [.n (val% «exponent_tables» "s8#0")] (etAs.map Stmt.atom) et_straight
  rw [← et_split] at hw
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ et_straight
  have hsz : (etAs.map Stmt.atom).filterMap Main.Stmt.allocSz = [(.n (val% «exponent_tables» "g_squares"), .inl lit% B1.expTabN)] := by
    decide +kernel
  have hal : allocs σ ((etAs.map Stmt.atom).flatMap (Main.slEvs σ)) = [lit% B1.expTabN] := by
    rw [hpa, hsz]; rfl
  have hown : ∀ i, etB fs fp ≤ i → i < etB fs fp + lit% B1.expTabN →
      ownData cert fp (fp + fs "exponent_tables") "exponent_tables" [lit% B1.expTabN]
        ((etAs.map Stmt.atom).flatMap (Main.slEvs σ)) i :=
    fun i h1 h2 => Or.inl ⟨(lit% B1.expTabN, etB fs fp), by simp [bases], h1, h2⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := R) (D := fun i => etB fs fp ≤ i ∧ i < etB fs fp + lit% B1.expTabN) (Dk := fun _ => False) (N := 0)
    (fp := fp) (args := []) (rets := [gen ^ etB fs fp])
    coreProgram_wf find_exponent_tables (Or.inl (by
      rw [Program.loop_of_find? find_exponent_tables]; decide +kernel)) hp hw hr
    (slEvs_holds fun s hs => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
      exact hat a ha)
    (by
      rw [hal, hpd, hsz]
      simp only [List.map_cons, List.map_nil, bases, h0, gen_pow_eq_ofK])
    (fun q hq => by
      rw [hpad, show (etAs.map Stmt.atom).filterMap Main.Stmt.addrS = [] by decide +kernel] at hq
      simp at hq)
    (by
      rw [hpc, show (etAs.map Stmt.atom).filterMap Main.Stmt.callS = [] by decide +kernel]
      exact ⟨rfl, fun _ h => h⟩)
    (fun A hA => by
      rw [B1.loadAddrs_straight σ _ et_straight, show (etAs.map Stmt.atom).filterMap B1.Stmt.loadS =
        (List.range lit% B1.expTabN).map (fun t => (V.n (val% «exponent_tables» "g_squares"), etOff t)) by decide +kernel] at hA
      simp only [List.map_map, List.mem_map, List.mem_range, Function.comp] at hA
      obtain ⟨t, ht, rfl⟩ := hA
      have := etOff_lt ht
      refine ⟨etB fs fp + etOff t, by rw [h0, limb0_gen_pow_mul], Or.inl ?_⟩
      rw [hal]; exact hown _ (by omega) (by omega))
    (fun i hi => Or.inl (by rw [hal]; exact hown i hi.1 hi.2))
  rw [hal] at h
  simpa using h

end
end LeanVM.Guest.B1.Main
