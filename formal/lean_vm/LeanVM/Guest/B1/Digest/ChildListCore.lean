/-
  LeanVM.Guest.B1.Digest.ChildListCore

  `child_claim_list_last__L{k}`'s honest valuation, with where its loads read: for its placed
  completeness.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCLast

/-!
# The last child claims' honest valuation

`cclAtoms k`: `child_claim_list_last__L{k}`'s atoms, its body those and a return
(`ccl_split`), placing nothing and not a loop helper. `ccl_core`: from the state after whole
blocks `pre` at `sp = g^sP` and `k` honest records, the body's evaluated valuation (`Fwd.ev`, the
slots from `slotW`) holds its atoms and returns the digest, and every load reads the state's
`13` words, a record's mark at `region · g^(os j)`, or a record's four cells at
`entries · g^(4 os j)`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Da (limb0_gen_pow_mul)

@[expose] public section

variable {rd : Reader}

/-- `child_claim_list_last__L{k}`'s atoms. -/
noncomputable def cclAtoms (k : ℕ) : List Atom :=
  ((splitBody (coreProgram.getD (367 + k) default).body).map (·.1)).getD []

set_option maxRecDepth 100000 in
theorem ccl_shape_all : ∀ k < 17, ((cclAtoms k).all (fun a => !Memory.atomAllocB a &&
    (Memory.atomAddr? a).isNone) && ((coreProgram.getD (367 + k) default).loop == false)) = true := by
  decide +kernel

theorem ccl_name {k : ℕ} (hk : k < 17) :
    coreProgram.find? (cclNames.getD k "") = some (coreProgram.getD (367 + k) default) :=
  find_of_idx (ccl_idx k hk) (by rw [coreProgram_length]; omega)

theorem ccl_loop {k : ℕ} (hk : k < 17) : coreProgram.loop (cclNames.getD k "") = false := by
  rw [Program.loop_of_find? (ccl_name hk)]
  have := ccl_shape_all k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

theorem ccl_na {k : ℕ} (hk : k < 17) : (cclAtoms k).all (fun a => !Memory.atomAllocB a) = true := by
  have := ccl_shape_all k hk
  simp only [Bool.and_eq_true, List.all_eq_true] at this
  exact List.all_eq_true.mpr fun a ha => (this.1 a ha).1

theorem ccl_addr {k : ℕ} (hk : k < 17) : (cclAtoms k).filterMap Memory.atomAddr? = [] := by
  have := ccl_shape_all k hk
  simp only [Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at this
  exact List.filterMap_eq_nil_iff.mpr fun a ha => (this.1 a ha).2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The last child claims' honest valuation** (`[state, entries, region, marks, last]`), with
where its loads read. -/
theorem ccl_core {k : ℕ} (hk : k < 17) {sp entries region marks last : E} {sP eP rg L : ℕ}
    (hsp : sp = gen ^ sP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    {n : ℕ} {pre : List UInt8} (hpre : pre.length = rate * n)
    (hS : StateAt rd sp 0 (absorbChunks n zeroState pre)) {os : ℕ → ℕ} {cells : List E}
    (hl : cells.length = 4 * k)
    (hrec : RecMem rd region (gen ^ L) entries marks k os cells)
    (hlast : last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hdef : BoundMem rd L) :
    ∃ (vs : List V) (σ : Val),
      (coreProgram.getD (367 + k) default).body = (cclAtoms k).map Stmt.atom ++ [.ret vs] ∧
      (coreProgram.getD (367 + k) default).params.map σ = [sp, entries, region, marks, last] ∧
      (∀ a ∈ cclAtoms k, a.Holds rd σ) ∧
      vs.map σ = digestCells (keccak256 (pre ++ cellsBytes cells)) ∧
      ∀ q ∈ (cclAtoms k).filterMap Memory.atomLoad?,
        (∃ o < 13, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (sP + o)) ∨
        (∃ j < k, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (rg + os j)) ∨
        (∃ j < k, ∃ c < 4,
          (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (eP + 4 * os j + c)) := by
  have hok := ccl_all k hk
  have hcok := ccc_all hk
  set fn := coreProgram.getD (367 + k) default
  simp only [cclOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hok⟩ := hok
  simp only [cccOk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨c', hchk⟩, hcok⟩ := hcok
  split at hok
  · rename_i atoms r0 r1 hsb
    rw [hsb] at hcok
    have hatoms : cclAtoms k = atoms := by
      show ((splitBody fn.body).map (·.1)).getD [] = atoms
      rw [hsb]; rfl
    rw [hatoms]
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok hcok
    obtain ⟨⟨⟨hck, hret⟩, -⟩, hst⟩ := hok
    obtain ⟨⟨hedge, hrecs⟩, -⟩ := hcok
    obtain ⟨hSt, hst0, -, htl⟩ := edge_parts hedge
    set S := storesOf 5 fn.body with hSdef
    let args : List E := [sp, entries, region, marks, last]
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (slotW 5 os) args fn.body) := ⟨_, rfl⟩
    have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
    obtain ⟨-, -, hgs⟩ := ev_spec rd (slotW 5 os) fn.body args hchk
    rw [show args.length = 5 from rfl, ← hσ] at hgs
    have hbody := splitBody_eq hsb
    have hg : ∀ a ∈ atoms, Good rd S (slotW 5 os) σ a := fun a ha =>
      hgs (.atom a) (by rw [hbody]; exact List.mem_append_left _ (List.mem_map_of_mem ha))
    have par : ∀ i (hi : i < 5), σ (.n i) = args.getD i 0 := fun i hi => by
      rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
    have e0 : σ (.n 0) = sp := par 0 (by omega)
    have e1 : σ (.n 1) = entries := par 1 (by omega)
    have e2 : σ (.n 2) = region := par 2 (by omega)
    have e3 : σ (.n 3) = marks := par 3 (by omega)
    have e4 : σ (.n 4) = last := par 4 (by omega)
    have hrec' : RecMem rd (σ cclP.region) (gen ^ L) (σ cclP.entries) (σ cclP.marks) k os cells := by
      show RecMem rd (σ (.n 2)) (gen ^ L) (σ (.n 1)) (σ (.n 3)) k os cells
      rw [e2, e1, e3]; exact hrec
    have hlast' : σ cclP.last * gen = gen ^ L := by show σ (.n 4) * gen = _; rw [e4]; exact hlast
    obtain ⟨hwit, -, vc, hside⟩ := recsW_holds hrecs hg hSt hrec' hlast' hL33 hdef
    have hpv : ∀ {p : V}, p.idx = 0 → σ p = sp := fun hp => by rw [hidx, hp, e0]
    have hnSl : ∀ {d p : V} {off : ℕ}, p.idx = 0 → off < 13 → Atom.load d p off ∉ S :=
      fun hp ho => notS_of_ptr hSt (by rw [hp]; exact hst0) ho
    have vst : ∀ c : Fin 13, σ ((cclSt k).getD c default) =
        cellsOfState (absorbChunks n zeroState pre) false c := by
      intro c
      simp only [stLoadsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hst
      rw [load_val (hst.2 c c.isLt) hg (hnSl rfl (by have := c.isLt; omega)), e0,
        rdAt_of_load (hS c)]
    have hat : ∀ a ∈ atoms, a.Holds rd σ := by
      refine blockW_holds (c := 5) (ss := fn.body) (p0 := 0) (stp := 0) (outs := [])
        hg hedge hside ?_
        (fun a _ h => (isStSt_nil h).elim) (fun _ a _ h => (isStSt_nil h).elim)
      intro a ha h haS
      cases a <;> simp only [isStLd, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      rename_i d p off
      have hv := hS ⟨off, h.2⟩
      rw [Nat.zero_add, ← hpv h.1] at hv
      exact load_holds_of haS (hg _ ha) hv
    have hd := chain_final hck rfl hat hpre
      (initCell_of_loads rfl hst hat (by rw [e0]; exact hS))
    have hv : ((cclSpec k atoms).vals σ).take ((cclSpec k atoms).len / 16) = cells := by
      have : (cclSpec k atoms).vals σ = cells := ccMsg_vals hl vc
      rw [this, List.take_of_length_le (by simp only [cclSpec]; omega)]
    rw [hv] at hd
    simp only [retOk, Bool.and_eq_true] at hret
    refine ⟨[r0, r1], σ, hbody, ?_, hat, ?_, fun q hq => ?_⟩
    · rw [hpar]
      simp only [List.map_cons, List.map_nil, e0, e1, e2, e3, e4]
    · rw [List.map_cons, List.map_cons, List.map_nil, copy_sound hret.1 hat, copy_sound hret.2 hat,
        digestCells, ← hd]
    · obtain ⟨a, ha, haq⟩ := List.mem_filterMap.mp hq
      cases a with
      | load d p off =>
        simp only [Memory.atomLoad?, Option.some.injEq] at haq
        subst haq
        rcases mem_parts (p0 := 0) (K := k) ha with h | ⟨i, hi, h⟩ | h
        · simp at h
        · have hFi : ∀ b ∈ (ccOwn atoms 0 i).filter pureB, b.Holds rd σ :=
            fun b hb => hat b (mem_ccOwn (List.mem_filter.mp hb).1)
          rcases sideW_addr hFi (hwit i hi) (show σ (.n 2) = _ by rw [e2, hrg])
              (show σ (.n 1) = _ by rw [e1, hen])
              ((recW_parts (hrecs i hi)).2.2.2 _ h rfl) with h' | ⟨c, hc4, h'⟩
          · exact Or.inr (Or.inl ⟨i, hi, h'⟩)
          · exact Or.inr (Or.inr ⟨i, hi, c, hc4, h'⟩)
        · rcases htl _ h with h' | h' | h'
          · exact absurd h' (by simp [needsSide])
          · simp only [isStLd, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
            refine Or.inl ⟨off, h'.2, ?_⟩
            show (σ p).limb 0 * addressOfIndex off = _
            rw [hpv h'.1, hsp, limb0_gen_pow_mul]
          · exact (isStSt_nil h').elim
      | _ => simp [Memory.atomLoad?] at haq
  · exact absurd hok (by simp)

end
end LeanVM.Guest.B1.Digest
