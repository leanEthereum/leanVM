import Rv64Verifier.Sym.Exec
import Rv64Verifier.Sym.Steps

/-!
# Soundness of the symbolic executor

Ported from sig.golf's `SigGolfCandidate.Rv`.

Main theorem (`symRun_sound`): if `symRun cfg words pc fuel = some r`, `words` sit at `pc` in
`code` (`CodeAt`), and the concrete state `s` has `s.pc = pc` and satisfies the side conditions
`r.obligs s`, then for some code map `c`

  `Steps code r.steps s (r.toState s c)`

where `r.toState s c` is the explicit final state: registers `(r.st.regs.get x).eval s`, memory
`memEval s r.st.mem` (every address not written is unchanged, `memEval_frame`), pc
`r.pc.eval s`, code map `c`, every other field as in `s`. The code map is existential because a
base instruction's step replaces it by `code.baseMap` and a word operation's keeps it.
-/

namespace Rv64Verifier.Sym
open RiscvZkvm.Rv64

/-! ## Register file -/

@[simp] theorem RegFile.get_x0 (rf : RegFile) : rf.get .x0 = .c 0 := rfl
@[simp] theorem RegFile.set_x0 (rf : RegFile) (e : E) : rf.set .x0 e = rf := rfl

theorem RegFile.get_set_self (rf : RegFile) {r : Reg} (e : E) (h : r ≠ .x0) :
    (rf.set r e).get r = e := by
  cases r <;> first | exact absurd rfl h | rfl

set_option maxHeartbeats 4000000 in
theorem RegFile.get_set_ne (rf : RegFile) {r r' : Reg} (e : E) (h : r' ≠ r) :
    (rf.set r e).get r' = rf.get r' := by
  cases r <;> cases r' <;> first | exact absurd rfl h | rfl

theorem RegFile.init_get_eval (s : MachineState) (r : Reg) :
    (RegFile.init.get r).eval s = s.getReg r := by
  cases r <;> rfl

/-! ## `toState` -/

theorem MachineState.ext' {a b : MachineState} (hr : a.regs = b.regs) (hm : a.mem = b.mem)
    (hc : a.code = b.code) (hp : a.pc = b.pc) (h1 : a.committed = b.committed)
    (h2 : a.publicValues = b.publicValues) (h3 : a.privateInput = b.privateInput)
    (h4 : a.inputBufBase = b.inputBufBase) : a = b := by
  cases a; cases b; simp_all

variable {c : Word → Option Instr}

@[simp] theorem SymState.toState_getReg (σ : SymState) (s : MachineState) (pc : Word) (r : Reg) :
    (σ.toState s c pc).getReg r = (σ.regs.get r).eval s := by
  cases r <;> rfl

@[simp] theorem SymState.toState_getMem (σ : SymState) (s : MachineState) (pc a : Word) :
    (σ.toState s c pc).getMem a = memEval s σ.mem a := rfl

@[simp] theorem SymState.toState_pc (σ : SymState) (s : MachineState) (pc : Word) :
    (σ.toState s c pc).pc = pc := rfl

@[simp] theorem SymState.toState_code (σ : SymState) (s : MachineState) (pc : Word) :
    (σ.toState s c pc).code = c := rfl

theorem SymState.toState_setPC (σ : SymState) (s : MachineState) (pc pc' : Word) :
    (σ.toState s c pc).setPC pc' = σ.toState s c pc' := rfl

theorem SymState.toState_congr {σ σ' : SymState} {s : MachineState} (hr : σ.regs = σ'.regs)
    (hm : memEval s σ.mem = memEval s σ'.mem) (pc : Word) :
    σ.toState s c pc = σ'.toState s c pc := by
  unfold SymState.toState; rw [hr, hm]

theorem SymState.init_toState (s : MachineState) : SymState.init.toState s s.code s.pc = s := by
  apply MachineState.ext' <;> try rfl
  funext r
  cases r <;> rfl

theorem setReg_of_ne (t : MachineState) {r : Reg} (v : Word) (h : r ≠ .x0) :
    t.setReg r v = { t with regs := fun r' => if r' = r then v else t.regs r' } := by
  cases r <;> first | exact absurd rfl h | (simp only [MachineState.setReg, beq_iff_eq])

theorem SymState.toState_setReg (σ : SymState) (s : MachineState) (pc : Word) (rd : Reg) (e : E) :
    (σ.toState s c pc).setReg rd (e.eval s) =
      ({ σ with regs := σ.regs.set rd e }).toState s c pc := by
  by_cases hrd : rd = .x0
  · subst hrd; rfl
  · rw [setReg_of_ne _ _ hrd]
    apply MachineState.ext' <;> try rfl
    funext r'
    simp only [SymState.toState]
    by_cases h : r' = rd
    · subst h; simp [hrd, RegFile.get_set_self _ _ hrd]
    · simp [h, RegFile.get_set_ne _ _ h]

theorem SymState.toState_setMem (σ : SymState) (s : MachineState) (pc : Word) (k : Addr) (e : E) :
    (σ.toState s c pc).setMem (k.eval s) (e.eval s) =
      ({ σ with mem := (k, e) :: σ.mem }).toState s c pc := by
  apply MachineState.ext' <;> try rfl
  funext a
  simp [MachineState.setMem, SymState.toState, memEval]

/-! ## Memory -/

theorem memEval_nil (s : MachineState) (a : Word) : memEval s [] a = s.getMem a := rfl

theorem memEval_cons (s : MachineState) (k : Addr) (v : E) (ws : SymMem) (a : Word) :
    memEval s ((k, v) :: ws) a = if a = k.eval s then v.eval s else memEval s ws a := rfl

/-- Frame property: an address different from every written key reads the initial memory. -/
theorem memEval_frame (s : MachineState) (ws : SymMem) (a : Word)
    (h : ∀ p ∈ ws, a ≠ p.1.eval s) : memEval s ws a = s.getMem a := by
  induction ws with
  | nil => rfl
  | cons p ws ih =>
    obtain ⟨k, v⟩ := p
    rw [memEval_cons, ite_eq_right (h _ (List.mem_cons_self ..))]
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem isSame_eval {k k' : Addr} (h : isSame k k' = true) (s : MachineState) :
    k.eval s = k'.eval s := by
  unfold isSame at h
  split at h
  · rename_i hs; exact Addr.alias_same hs s
  · cases h

theorem memEval_writeMem (s : MachineState) (k : Addr) (v : E) (ws : SymMem) :
    memEval s (writeMem k v ws) = memEval s ((k, v) :: ws) := by
  funext a
  simp only [writeMem, memEval_cons]
  split
  · rfl
  · rename_i hne
    induction ws with
    | nil => rfl
    | cons p ws ih =>
      obtain ⟨k', v'⟩ := p
      simp only [List.filter_cons]
      split
      · rw [memEval_cons, memEval_cons, ih]
      · rename_i hs
        have hs' : isSame k k' = true := by simpa using hs
        rw [memEval_cons, ite_eq_right, ih]
        rw [← isSame_eval hs' s]; exact hne

theorem readMem_sound {cfg : Config} {k : Addr} {ws : SymMem} {e : E} {os : List Oblig}
    (h : readMem cfg k ws = some (e, os)) (s : MachineState) (hos : ∀ o ∈ os, o.holds s) :
    memEval s ws (k.eval s) = e.eval s := by
  induction ws generalizing e os with
  | nil =>
    simp only [readMem, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [memEval_nil, E.eval, Addr.toE_eval]
  | cons p ws ih =>
    obtain ⟨k', v⟩ := p
    simp only [readMem] at h
    rw [memEval_cons]
    split at h
    · rename_i hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [ite_eq_left (Addr.alias_same hs s)]
    · rename_i hd
      rw [ite_eq_right (Addr.alias_diff hd s)]
      exact ih h hos
    · split at h
      · split at h
        · cases h
        · rename_i e' os' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hne := hos _ (List.mem_cons_self ..)
          simp only [Oblig.holds] at hne
          rw [ite_eq_right hne]
          exact ih hr (fun o ho => hos o (List.mem_cons_of_mem _ ho))
      · cases h

/-! ## Side conditions -/

theorem SymState.addObl_regs (σ : SymState) (o : Oblig) : (σ.addObl o).regs = σ.regs := by
  unfold SymState.addObl; split <;> rfl

theorem SymState.addObl_mem (σ : SymState) (o : Oblig) : (σ.addObl o).mem = σ.mem := by
  unfold SymState.addObl; split <;> rfl

theorem SymState.addObl_sub (σ : SymState) (o : Oblig) : σ.obl ⊆ (σ.addObl o).obl := by
  unfold SymState.addObl; split
  · exact List.Subset.refl _
  · exact List.subset_cons_self ..

theorem SymState.addObl_mem_obl (σ : SymState) (o : Oblig) : o ∈ (σ.addObl o).obl := by
  unfold SymState.addObl; split
  · rename_i h
    obtain ⟨o', ho', hb⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp h).2
    rw [Oblig.beq_eq hb]; exact ho'
  · exact List.mem_cons_self ..

theorem SymState.addObls_regs (σ : SymState) (os : List Oblig) : (σ.addObls os).regs = σ.regs := by
  induction os generalizing σ with
  | nil => rfl
  | cons o os ih => simp only [SymState.addObls, List.foldl_cons] at ih ⊢; rw [ih, addObl_regs]

theorem SymState.addObls_mem (σ : SymState) (os : List Oblig) : (σ.addObls os).mem = σ.mem := by
  induction os generalizing σ with
  | nil => rfl
  | cons o os ih => simp only [SymState.addObls, List.foldl_cons] at ih ⊢; rw [ih, addObl_mem]

theorem SymState.addObls_sub (σ : SymState) (os : List Oblig) : σ.obl ⊆ (σ.addObls os).obl := by
  induction os generalizing σ with
  | nil => exact List.Subset.refl _
  | cons o os ih =>
    simp only [SymState.addObls, List.foldl_cons] at ih ⊢
    exact List.Subset.trans (addObl_sub σ o) (ih _)

theorem SymState.addObls_mem_obl (σ : SymState) (os : List Oblig) :
    ∀ o ∈ os, o ∈ (σ.addObls os).obl := by
  induction os generalizing σ with
  | nil => intro o h; cases h
  | cons o os ih =>
    intro o' h
    simp only [SymState.addObls, List.foldl_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact addObls_sub _ os (addObl_mem_obl σ o')
    · exact ih _ o' h

/-! ## Address arithmetic -/

theorem byteOffset_eq (x : Word) : byteOffset x = x.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and, show (7#64).toNat = 7 from rfl]
  simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 3

theorem alignToDword_toNat (x : Word) : (alignToDword x).toNat = x.toNat - x.toNat % 8 := by
  unfold alignToDword
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 7 from rfl]
  have hhi_mod : (x.toNat &&& (2 ^ 64 - 1 - 7)) % 8 = 0 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_mod_two_pow,
      show (2 ^ 64 - 1 - 7 : Nat) % 2 ^ 3 = 0 from by decide]
    simp
  have hhi_div : (x.toNat &&& (2 ^ 64 - 1 - 7)) / 8 = x.toNat / 8 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_div_two_pow,
      show (2 ^ 64 - 1 - 7 : Nat) / 2 ^ 3 = 2 ^ 61 - 1 from by decide]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by have := x.isLt; omega)
  have heucl := Nat.div_add_mod (x.toNat &&& (2 ^ 64 - 1 - 7)) 8
  have heucl2 := Nat.div_add_mod x.toNat 8
  omega

theorem aligned_add (b k : Word) (hb : b.toNat % 8 = 0) :
    alignToDword (b + k) = b + alignToDword k ∧ byteOffset (b + k) = byteOffset k := by
  have hbl := b.isLt
  have hkl := k.isLt
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, BitVec.toNat_add, BitVec.toNat_add, alignToDword_toNat]
    omega
  · rw [byteOffset_eq, byteOffset_eq, BitVec.toNat_add]
    omega

theorem checkValid_sound {σ σ₁ : SymState} {a : Addr} {w : Nat} (h : checkValid σ a w = some σ₁)
    (s : MachineState) (hobl : ∀ o ∈ σ₁.obl, o.holds s) :
    validAccess w (a.eval s) = true ∧ σ₁.regs = σ.regs ∧ σ₁.mem = σ.mem ∧ σ.obl ⊆ σ₁.obl := by
  unfold checkValid at h
  split at h
  · rename_i hb
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h; subst h
      refine ⟨?_, rfl, rfl, List.Subset.refl _⟩
      simp only [Addr.eval, hb]; exact hv
    · cases h
  · rename_i b hb
    simp only [Option.some.injEq] at h; subst h
    refine ⟨?_, SymState.addObl_regs _ _, SymState.addObl_mem _ _, SymState.addObl_sub _ _⟩
    exact hobl _ (SymState.addObl_mem_obl _ _)

theorem subKey_sound {σ σ₂ : SymState} {a key : Addr} {bo : Nat} (h : subKey σ a = (σ₂, key, bo))
    (s : MachineState) (hobl : ∀ o ∈ σ₂.obl, o.holds s) :
    key.eval s = alignToDword (a.eval s) ∧ bo = byteOffset (a.eval s) ∧
      σ₂.regs = σ.regs ∧ σ₂.mem = σ.mem ∧ σ.obl ⊆ σ₂.obl := by
  unfold subKey at h
  split at h
  · rename_i hb
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [Addr.eval, hb]
  · rename_i b hb
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hal : (b.eval s).toNat % 8 = 0 := hobl _ (SymState.addObl_mem_obl _ _)
    have := aligned_add (b.eval s) a.off hal
    refine ⟨?_, ?_, SymState.addObl_regs _ _, SymState.addObl_mem _ _, SymState.addObl_sub _ _⟩
    · simp [Addr.eval, hb, this.1]
    · simp [Addr.eval, hb, this.2]

theorem anyKey_sound (s : MachineState) (a : Addr) :
    (anyKey a).1.eval s = alignToDword (a.eval s) ∧
      ((anyKey a).2.eval s).toNat = byteOffset (a.eval s) := by
  simp only [anyKey, norm_eval, mkBin_eval, Addr.toE_eval]
  exact ⟨rfl, rfl⟩

/-! ## One micro-op -/

theorem Src.sym_eval (σ : SymState) (s : MachineState) (pc : Word) (a : Src) :
    (a.sym σ.regs pc).eval s = a.eval (σ.toState s c pc) := by
  cases a <;> simp [Src.sym, Src.eval, E.eval]

theorem LoadKind.isD_iff (k : LoadKind) : k.isD = true ↔ k = .d := by cases k <;> simp [LoadKind.isD]
theorem StoreKind.isD_iff (k : StoreKind) : k.isD = true ↔ k = .d := by
  cases k <;> simp [StoreKind.isD]

/-- The next pc after a micro-op. -/
def nextPc (s : MachineState) (pc : Word) : Option E → Word
  | none => pc + 4
  | some t => t.eval s

set_option maxHeartbeats 1000000 in
theorem symMicro_sound {cfg : Config} {pc : Word} {σ σ' : SymState} {m : Micro} {ctl : Option E}
    (h : symMicro cfg pc σ m = some (σ', ctl)) (s : MachineState)
    (hobl : ∀ o ∈ σ'.obl, o.holds s) :
    σ.obl ⊆ σ'.obl ∧ m.exec (σ.toState s c pc) = some (σ'.toState s c (nextPc s pc ctl)) := by
  cases m with
  | alu rd op a b =>
    simp only [symMicro, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.Subset.refl _, ?_⟩
    simp only [Micro.exec, SymState.toState_pc, ← Src.sym_eval, ← mkBin_eval,
      SymState.toState_setReg, SymState.toState_setPC, nextPc]
  | load k rd rs off =>
    simp only [symMicro] at h
    split at h
    · cases h
    · rename_i σ₁ hcv
      have haddr : (norm (mkAdd (σ.regs.get rs) (.c off))).eval s =
          (σ.toState s c pc).getReg rs + off := by
        rw [norm_eval, mkAdd_eval]; simp [E.eval]
      split at h
      · -- doubleword
        rename_i hk
        have hk' : k = .d := (LoadKind.isD_iff k).mp hk
        subst hk'
        split at h
        · cases h
        · rename_i v os hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hsub2 := SymState.addObls_sub σ₁ os
          have hobl1 : ∀ o ∈ σ₁.obl, o.holds s := fun o ho => hobl o (hsub2 ho)
          obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl1
          have hos : ∀ o ∈ os, o.holds s := fun o ho =>
            hobl o (SymState.addObls_mem_obl σ₁ os o ho)
          have hread := readMem_sound hr s hos
          refine ⟨List.Subset.trans hs1 hsub2, ?_⟩
          rw [haddr, hm1] at hread
          rw [haddr] at hv
          simp only [Micro.exec, hv, ite_true, LoadKind.read, SymState.toState_getMem,
            SymState.toState_pc]
          rw [hread, SymState.toState_setReg, SymState.toState_setPC]
          congr 1
          apply SymState.toState_congr
          · simp [SymState.addObls_regs, hr1]
          · simp [SymState.addObls_mem, hm1]
      · -- sub-doubleword
        rename_i hk
        have hk' : k ≠ .d := fun h' => hk ((LoadKind.isD_iff k).mpr h')
        split at h
        · -- at any address
          split at h
          · cases h
          · rename_i w os hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hsub2 := SymState.addObls_sub σ₁ os
            have hobl1 : ∀ o ∈ σ₁.obl, o.holds s := fun o ho => hobl o (hsub2 ho)
            obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl1
            have hos : ∀ o ∈ os, o.holds s := fun o ho =>
              hobl o (SymState.addObls_mem_obl σ₁ os o ho)
            have hread := readMem_sound hr s hos
            obtain ⟨hkey, hpos⟩ := anyKey_sound s (norm (mkAdd (σ.regs.get rs) (E.c off)))
            refine ⟨List.Subset.trans hs1 hsub2, ?_⟩
            rw [haddr] at hv hkey hpos
            rw [hkey, hm1] at hread
            simp only [Micro.exec, hv, ite_true, SymState.toState_pc]
            rw [LoadKind.read_sub _ _ _ hk', SymState.toState_getMem, hread, ← hpos,
              show k.fromWord (w.eval s) ((anyKey (norm (mkAdd (σ.regs.get rs) (E.c off)))).2.eval
                s).toNat = (mkBin (.ldx k) w (anyKey (norm (mkAdd (σ.regs.get rs) (E.c off)))).2).eval
                s by rw [mkBin_eval]; rfl,
              SymState.toState_setReg, SymState.toState_setPC]
            congr 1
            apply SymState.toState_congr
            · simp [SymState.addObls_regs, hr1]
            · simp [SymState.addObls_mem, hm1]
        generalize hsk : subKey σ₁ (norm (mkAdd (σ.regs.get rs) (E.c off))) = p at h
        obtain ⟨σ₂, key, bo⟩ := p
        simp only at h
        split at h
        · cases h
        · rename_i w os hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hsub3 := SymState.addObls_sub σ₂ os
          have hobl2 : ∀ o ∈ σ₂.obl, o.holds s := fun o ho => hobl o (hsub3 ho)
          obtain ⟨hkey, hbo, hr2, hm2, hs2⟩ := subKey_sound hsk s hobl2
          have hobl1 : ∀ o ∈ σ₁.obl, o.holds s := fun o ho => hobl2 o (hs2 ho)
          obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl1
          have hos : ∀ o ∈ os, o.holds s := fun o ho =>
            hobl o (SymState.addObls_mem_obl σ₂ os o ho)
          have hread := readMem_sound hr s hos
          refine ⟨List.Subset.trans hs1 (List.Subset.trans hs2 hsub3), ?_⟩
          rw [haddr] at hv hkey hbo
          rw [hkey, hm2, hm1] at hread
          simp only [Micro.exec, hv, ite_true, SymState.toState_pc]
          rw [LoadKind.read_sub _ _ _ hk', SymState.toState_getMem, hread, ← hbo,
            show k.fromWord (w.eval s) bo = (mkUn (.ld k bo) w).eval s by rw [mkUn_eval]; rfl,
            SymState.toState_setReg, SymState.toState_setPC]
          congr 1
          apply SymState.toState_congr
          · simp [SymState.addObls_regs, hr1, hr2]
          · simp [SymState.addObls_mem, hm1, hm2]
  | store k rs1 rs2 off =>
    simp only [symMicro] at h
    split at h
    · cases h
    · rename_i σ₁ hcv
      have haddr : (norm (mkAdd (σ.regs.get rs1) (.c off))).eval s =
          (σ.toState s c pc).getReg rs1 + off := by
        rw [norm_eval, mkAdd_eval]; simp [E.eval]
      split at h
      · rename_i hk
        have hk' : k = .d := (StoreKind.isD_iff k).mp hk
        subst hk'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl
        refine ⟨hs1, ?_⟩
        rw [haddr] at hv
        simp only [Micro.exec, hv, ite_true, StoreKind.write, SymState.toState_pc]
        rw [← haddr, show (σ.toState s c pc).getReg rs2 = (σ.regs.get rs2).eval s by simp,
          SymState.toState_setMem, SymState.toState_setPC]
        congr 1
        apply SymState.toState_congr
        · simp [hr1]
        · simp [memEval_writeMem, hm1]
      · rename_i hk
        have hk' : k ≠ .d := fun h' => hk ((StoreKind.isD_iff k).mpr h')
        split at h
        · -- at any address
          split at h
          · cases h
          · rename_i old os hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hsub2 := SymState.addObls_sub σ₁ os
            have hobl1 : ∀ o ∈ σ₁.obl, o.holds s := fun o ho => hobl o (hsub2 ho)
            obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl1
            have hos : ∀ o ∈ os, o.holds s := fun o ho =>
              hobl o (SymState.addObls_mem_obl σ₁ os o ho)
            have hread := readMem_sound hr s hos
            obtain ⟨hkey, hpos⟩ := anyKey_sound s (norm (mkAdd (σ.regs.get rs1) (E.c off)))
            refine ⟨List.Subset.trans hs1 hsub2, ?_⟩
            rw [haddr] at hv hkey hpos
            rw [hkey, hm1] at hread
            simp only [Micro.exec, hv, ite_true, SymState.toState_pc]
            rw [StoreKind.write_sub _ _ _ _ hk', SymState.toState_getMem, hread, ← hpos, ← hkey,
              show k.merge (old.eval s) ((anyKey (norm (mkAdd (σ.regs.get rs1) (E.c off)))).2.eval
                s).toNat ((σ.toState s c pc).getReg rs2) = (E.stx k old (anyKey (norm (mkAdd
                (σ.regs.get rs1) (E.c off)))).2 (σ.regs.get rs2)).eval s by simp [E.eval],
              SymState.toState_setMem, SymState.toState_setPC]
            congr 1
            apply SymState.toState_congr
            · simp [SymState.addObls_regs, hr1]
            · simp [memEval_writeMem, SymState.addObls_mem, hm1]
        generalize hsk : subKey σ₁ (norm (mkAdd (σ.regs.get rs1) (E.c off))) = p at h
        obtain ⟨σ₂, key, bo⟩ := p
        simp only at h
        split at h
        · cases h
        · rename_i old os hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hsub3 := SymState.addObls_sub σ₂ os
          have hobl2 : ∀ o ∈ σ₂.obl, o.holds s := fun o ho => hobl o (hsub3 ho)
          obtain ⟨hkey, hbo, hr2, hm2, hs2⟩ := subKey_sound hsk s hobl2
          have hobl1 : ∀ o ∈ σ₁.obl, o.holds s := fun o ho => hobl2 o (hs2 ho)
          obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl1
          have hos : ∀ o ∈ os, o.holds s := fun o ho =>
            hobl o (SymState.addObls_mem_obl σ₂ os o ho)
          have hread := readMem_sound hr s hos
          refine ⟨List.Subset.trans hs1 (List.Subset.trans hs2 hsub3), ?_⟩
          rw [haddr] at hv hkey hbo
          rw [hkey, hm2, hm1] at hread
          simp only [Micro.exec, hv, ite_true, SymState.toState_pc]
          rw [StoreKind.write_sub _ _ _ _ hk', SymState.toState_getMem, hread, ← hbo, ← hkey,
            show k.merge (old.eval s) bo ((σ.toState s c pc).getReg rs2) =
              (mkBin (.st k bo) old (σ.regs.get rs2)).eval s by rw [mkBin_eval]; simp; rfl,
            SymState.toState_setMem, SymState.toState_setPC]
          congr 1
          apply SymState.toState_congr
          · simp [SymState.addObls_regs, hr1, hr2]
          · simp [memEval_writeMem, SymState.addObls_mem, hm1, hm2]
  | branch op r1 r2 off =>
    simp only [symMicro, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.Subset.refl _, ?_⟩
    simp only [Micro.exec, nextPc, mkIte_eval, SymState.toState_getReg, SymState.toState_pc,
      SymState.toState_setPC, E.eval]
  | jal rd off =>
    simp only [symMicro, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.Subset.refl _, ?_⟩
    simp only [Micro.exec, nextPc, SymState.toState_pc, E.eval]
    rw [show pc + 4 = (E.c (pc + 4)).eval s from rfl, SymState.toState_setReg,
      SymState.toState_setPC]
    rfl
  | jalr rd rs off =>
    simp only [symMicro, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.Subset.refl _, ?_⟩
    simp only [Micro.exec, nextPc, SymState.toState_pc, mkBin_eval, mkAdd_eval, E.eval,
      SymState.toState_getReg, BinOp.eval]
    rw [show pc + 4 = (E.c (pc + 4)).eval s from rfl, SymState.toState_setReg,
      SymState.toState_setPC]
    rfl

/-! ## Code placement -/

theorem getElem?_of_prefix_drop {l : List (BitVec 32)} {i : Nat} {w : BitVec 32}
    {ws : List (BitVec 32)} (h4 : w :: ws <+: List.drop i l) : l[i]? = some w := by
  obtain ⟨t, ht⟩ := h4
  have := congrArg (·[0]?) ht
  simp only [List.getElem?_drop, List.cons_append, List.getElem?_cons_zero, Nat.add_zero] at this
  exact this.symm

theorem CodeAt.fetch {code : Code} {pc : Word} {w : BitVec 32} {ws : List (BitVec 32)}
    (h : CodeAt code pc (w :: ws)) : code.fetch pc = decodeInstruction w := by
  obtain ⟨h1, h2, _, h4⟩ := h
  have hget : code.words[(pc.toNat - code.base.toNat) / 4]? = some w := getElem?_of_prefix_drop h4
  unfold Code.fetch
  rw [ite_eq_left ⟨h1, h2⟩, hget]
  rfl

theorem CodeAt.tail {code : Code} {pc : Word} {w : BitVec 32} {ws : List (BitVec 32)}
    (h : CodeAt code pc (w :: ws)) : CodeAt code (pc + 4) ws := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [List.length_cons] at h3
  have hpc : (pc + 4).toNat = pc.toNat + 4 := by
    rw [BitVec.toNat_add, show (4 : Word).toNat = 4 from rfl]; omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hpc, show (pc.toNat + 4 - code.base.toNat) / 4 = (pc.toNat - code.base.toNat) / 4 + 1 by omega,
    ← List.drop_drop]
  obtain ⟨t, ht⟩ := h4
  rw [← ht]
  exact ⟨t, by simp⟩

/-- Placement from a decomposition `code.words = pre ++ words ++ post`. -/
theorem CodeAt.of_append {code : Code} {pre words post : List (BitVec 32)}
    (h : code.words = pre ++ words ++ post) (pc : Word)
    (hpc : pc.toNat = code.base.toNat + 4 * pre.length) (h4 : pc.toNat % 4 = 0)
    (hrange : pc.toNat + 4 * words.length < 2 ^ 64) : CodeAt code pc words := by
  refine ⟨by omega, h4, hrange, ?_⟩
  rw [hpc, show (code.base.toNat + 4 * pre.length - code.base.toNat) / 4 = pre.length by omega, h,
    List.append_assoc, List.drop_left]
  exact List.prefix_append _ _

/-- Placement of the `n` words from index `i`, the usual way to name a function of an image. -/
theorem CodeAt.slice (code : Code) (i n : Nat) (pc : Word)
    (hpc : pc.toNat = code.base.toNat + 4 * i) (h4 : pc.toNat % 4 = 0)
    (hrange : pc.toNat + 4 * n < 2 ^ 64) : CodeAt code pc ((code.words.drop i).take n) := by
  refine ⟨by omega, h4, by simp; omega, ?_⟩
  rw [hpc, show (code.base.toNat + 4 * i - code.base.toNat) / 4 = i by omega]
  exact List.take_prefix _ _

/-! ## The block theorem -/

theorem isEcall_eq {i : Instruction} (h : isEcall i = true) : i = .base .ECALL := by
  unfold isEcall at h; split at h <;> first | rfl | cases h

theorem symRunAux_sound (cfg : Config) (code : Code) (s : MachineState) :
    ∀ (words : List (BitVec 32)) (pc : Word) (fuel : Nat) (σ : SymState) (r : Result)
      (c : Word → Option Instr),
      symRunAux cfg words pc fuel σ = some r → CodeAt code pc words →
      (∀ o ∈ r.st.obl, o.holds s) →
      (∃ c', Steps code r.steps (σ.toState s c pc) (r.toState s c')) ∧ σ.obl ⊆ r.st.obl ∧
        (r.stop = .ecall → code.fetch (r.pc.eval s) = some (.base .ECALL)) := by
  intro words
  induction words with
  | nil =>
    intro pc fuel σ r c h _ _
    cases fuel <;> simp only [symRunAux, Option.some.injEq] at h <;> subst h <;>
      exact ⟨⟨c, rfl⟩, List.Subset.refl _, by simp⟩
  | cons w ws ih =>
    intro pc fuel σ r c h hcode hobl
    cases fuel with
    | zero =>
      simp only [symRunAux, Option.some.injEq] at h; subst h
      exact ⟨⟨c, rfl⟩, List.Subset.refl _, by simp⟩
    | succ f =>
      simp only [symRunAux] at h
      split at h
      · cases h
      · rename_i i hdec
        have hf : code.fetch (σ.toState s c pc).pc = some i := hcode.fetch.trans hdec
        split at h
        · rename_i he
          simp only [Option.some.injEq] at h; subst h
          refine ⟨⟨c, rfl⟩, List.Subset.refl _, fun _ => ?_⟩
          rw [← isEcall_eq he]
          exact hf
        · split at h
          · cases h
          · rename_i m hcl
            split at h
            · cases h
            · rename_i σ' hm
              split at h
              · cases h
              · rename_i r' hr'
                simp only [Option.some.injEq] at h; subst h
                obtain ⟨⟨c', hsteps⟩, hsub, hec⟩ :=
                  ih (pc + 4) f σ' r' (codeAfter code (σ.toState s c pc) i) hr' hcode.tail hobl
                obtain ⟨hsub', hexec⟩ := symMicro_sound (c := c) hm s (fun o ho => hobl o (hsub ho))
                refine ⟨⟨c', Steps.cons ?_ hsteps⟩, List.Subset.trans hsub' hsub, hec⟩
                rw [classify_sound hf hcl, hexec]
                rfl
            · rename_i σ' t hm
              simp only [Option.some.injEq] at h; subst h
              obtain ⟨hsub', hexec⟩ := symMicro_sound (c := c) hm s hobl
              refine ⟨⟨codeAfter code (σ.toState s c pc) i, Steps.cons ?_ (Steps.refl _ _)⟩,
                hsub', ?_⟩
              · rw [classify_sound hf hcl, hexec]
                rfl
              · intro hst; cases m <;> cases hst

/-- **Soundness of the symbolic executor.** -/
theorem symRun_sound {cfg : Config} {code : Code} {words : List (BitVec 32)} {pc : Word}
    {fuel : Nat} {r : Result} (hrun : symRun cfg words pc fuel = some r)
    (hcode : CodeAt code pc words) (s : MachineState) (hpc : s.pc = pc) (hobl : r.obligs s) :
    ∃ c, Steps code r.steps s (r.toState s c) := by
  have := (symRunAux_sound cfg code s words pc fuel _ r s.code hrun hcode
    ((Oblig.all_iff s _).mp hobl)).1
  rwa [← hpc, SymState.init_toState] at this

/-- When the block stopped at an `ECALL`, its final pc fetches that `ECALL`. -/
theorem symRun_ecall {cfg : Config} {code : Code} {words : List (BitVec 32)} {pc : Word}
    {fuel : Nat} {r : Result} (hrun : symRun cfg words pc fuel = some r)
    (hcode : CodeAt code pc words) (s : MachineState) (hobl : r.obligs s)
    (hstop : r.stop = .ecall) : code.fetch (r.pc.eval s) = some (.base .ECALL) :=
  (symRunAux_sound cfg code s words pc fuel _ r s.code hrun hcode
    ((Oblig.all_iff s _).mp hobl)).2.2 hstop

/-! ## Reading final states -/

@[simp] theorem Result.toState_getReg (r : Result) (s : MachineState) (x : Reg) :
    (r.toState s c).getReg x = (r.st.regs.get x).eval s := by
  simp [Result.toState]

@[simp] theorem Result.toState_getMem (r : Result) (s : MachineState) (a : Word) :
    (r.toState s c).getMem a = memEval s r.st.mem a := rfl

@[simp] theorem Result.toState_pc (r : Result) (s : MachineState) :
    (r.toState s c).pc = r.pc.eval s := rfl

@[simp] theorem Result.toState_code (r : Result) (s : MachineState) :
    (r.toState s c).code = c := rfl

/-- Reflective read of the final memory: resolve a symbolic address against the block's writes. -/
theorem Result.toState_getMem_of_read (r : Result) (s : MachineState) {cfg : Config} {k : Addr}
    {e : E} {os : List Oblig} (h : readMem cfg k r.st.mem = some (e, os))
    (hos : Oblig.all s os) : (r.toState s c).getMem (k.eval s) = e.eval s :=
  readMem_sound h s ((Oblig.all_iff s _).mp hos)

/-- Frame: untouched memory is unchanged. -/
theorem Result.toState_getMem_frame (r : Result) (s : MachineState) (a : Word)
    (h : ∀ p ∈ r.st.mem, a ≠ p.1.eval s) : (r.toState s c).getMem a = s.getMem a :=
  memEval_frame s _ a h

end Rv64Verifier.Sym
