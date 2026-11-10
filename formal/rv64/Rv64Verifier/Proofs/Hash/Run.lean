import Rv64Verifier.Proofs.Common
import Rv64Verifier.Sym.Code

/-!
# Checking blocks by reflection

What the Keccak proofs add to `Sym`:

* `Region`: `n` doublewords at a register plus a constant. `oblOk` decides the side conditions
  a block's run raises about addresses in regions (a valid aligned doubleword of a region, two
  addresses in apart regions), so `oblig_all` proves a block's side conditions from one
  `decide` and the regions' validity and apartness.
* `memOk`, `regOk`: a block's written doubleword or final register agrees, modulo the
  associativity and commutativity of `^^^`, `&&&`, `|||` (`E.acEq`), with a given expression.
  The Keccak proofs give the expressions of the specification, built by functions, so the kernel
  compares them with the block's, and nobody elaborates either.
* `meetsR` and `run_spec`: `Result.meets` with side conditions checked by `oblOk`, from any
  starting symbolic state (`run_spec`), so that a block can start from registers known to be
  constants (a loop index the executor must see).
-/

namespace Rv64Verifier.Hash
open RiscvZkvm.Rv64 Rv64Verifier.Sym

/-! ## Regions -/

/-- `n` doublewords from `reg + lo`. -/
structure Region where
  reg : Reg
  lo : Word
  n : Nat

def Region.start (s : MachineState) (R : Region) : Word := s.getReg R.reg + R.lo

/-- The byte index in `R` of an address `R.reg + off`. -/
def Region.idx (R : Region) (a : Addr) : Option Nat :=
  match a.base with
  | some (.reg r) =>
    if Reg.beqN r R.reg && decide ((a.off - R.lo).toNat < 8 * R.n) then
      some (a.off - R.lo).toNat
    else none
  | _ => none

theorem Region.idx_eval {R : Region} {a : Addr} {i : Nat} (h : R.idx a = some i)
    (s : MachineState) : a.eval s = R.start s + BitVec.ofNat 64 i ∧ i < 8 * R.n := by
  rcases a with ⟨_ | b, off⟩
  · simp [Region.idx] at h
  · cases b with
    | reg r =>
      simp only [Region.idx, Bool.and_eq_true, decide_eq_true_eq] at h
      split at h
      · rename_i hc
        obtain ⟨hr, hlt⟩ := hc
        cases h
        have hr' := Reg.beqN_eq hr
        subst hr'
        refine ⟨?_, hlt⟩
        simp only [Addr.eval, E.eval, Region.start, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rw [BitVec.add_assoc, BitVec.add_comm R.lo, BitVec.sub_add_cancel]
      · cases h
    | _ => simp [Region.idx] at h

/-- The regions are valid memory. -/
def RegionsOk (s : MachineState) (rs : List Region) : Prop :=
  ∀ R ∈ rs, ValidMemRange (R.start s) R.n

/-- The regions are pairwise apart. -/
def RegionsApart (s : MachineState) (rs : List Region) : Prop :=
  rs.Pairwise fun R R' ↦ Rv64Verifier.Apart (R.start s) (8 * R.n) (R'.start s) (8 * R'.n)

def Region.has (a : Addr) (R : Region) : Bool := (R.idx a).isSome

/-- `a` and `b` lie in two different regions. -/
def neOk : List Region → Addr → Addr → Bool
  | [], _, _ => false
  | R :: rs, a, b =>
    (R.has a && rs.any (Region.has b)) || (R.has b && rs.any (Region.has a)) || neOk rs a b

def validOk (rs : List Region) (a : Addr) (w : Nat) : Bool :=
  rs.any fun R ↦ match R.idx a with
    | some i => w == 8 && i % 8 == 0
    | none => false

/-- `n` bytes from `reg + lo`, each a valid address (`BRegionsOk`). -/
structure BRegion where
  reg : Reg
  lo : Word
  n : Nat

def BRegion.start (s : MachineState) (B : BRegion) : Word := s.getReg B.reg + B.lo

def BRegion.idx (B : BRegion) (a : Addr) : Option Nat :=
  match a.base with
  | some (.reg r) =>
    if Reg.beqN r B.reg && decide ((a.off - B.lo).toNat < B.n) then some (a.off - B.lo).toNat
    else none
  | _ => none

theorem BRegion.idx_eval {B : BRegion} {a : Addr} {i : Nat} (h : B.idx a = some i)
    (s : MachineState) : a.eval s = B.start s + BitVec.ofNat 64 i ∧ i < B.n := by
  rcases a with ⟨_ | b, off⟩
  · simp [BRegion.idx] at h
  · cases b with
    | reg r =>
      simp only [BRegion.idx, Bool.and_eq_true, decide_eq_true_eq] at h
      split at h
      · rename_i hc
        obtain ⟨hr, hlt⟩ := hc
        cases h
        have hr' := Reg.beqN_eq hr
        subst hr'
        refine ⟨?_, hlt⟩
        simp only [Addr.eval, E.eval, BRegion.start, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rw [BitVec.add_assoc, BitVec.add_comm B.lo, BitVec.sub_add_cancel]
      · cases h
    | _ => simp [BRegion.idx] at h

/-- Every byte of the byte regions is a valid address. -/
def BRegionsOk (s : MachineState) (bs : List BRegion) : Prop :=
  ∀ B ∈ bs, ∀ i < B.n, isValidMemAddr (B.start s + BitVec.ofNat 64 i) = true

def validB (bs : List BRegion) (a : Addr) (w : Nat) : Bool :=
  w == 1 && bs.any fun B ↦ (B.idx a).isSome

theorem validB_sound {s : MachineState} {bs : List BRegion} (hok : BRegionsOk s bs) {a : Addr}
    {w : Nat} (h : validB bs a w = true) : validAccess w (a.eval s) = true := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, h⟩ := h
  obtain ⟨B, hB, hi⟩ := List.any_eq_true.mp h
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hi
  obtain ⟨ha, hlt⟩ := BRegion.idx_eval hi s
  rw [ha]
  exact hok B hB i hlt

/-- A side condition the regions discharge. -/
def oblOk (rs : List Region) (bs : List BRegion) : Oblig → Bool
  | .valid a w => validOk rs a w || validB bs a w
  | .ne a b => neOk rs a b
  | .align8 _ => false
  | .apart .. => false

theorem region_bounds {s : MachineState} {R : Region} (h : ValidMemRange (R.start s) R.n)
    (hn : 0 < R.n) : 0x20 ≤ (R.start s).toNat ∧ (R.start s).toNat % 8 = 0 ∧
      (R.start s).toNat + 8 * R.n ≤ 0xc0000008 :=
  ValidMemRange.bounds h hn

theorem validOk_sound {s : MachineState} {rs : List Region} (hok : RegionsOk s rs) {a : Addr}
    {w : Nat} (h : validOk rs a w = true) : validAccess w (a.eval s) = true := by
  obtain ⟨R, hR, hm⟩ := List.any_eq_true.mp h
  split at hm
  · rename_i i hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨rfl, hm⟩ := hm
    obtain ⟨ha, hlt⟩ := Region.idx_eval hi s
    rw [ha, show i = 8 * (i / 8) by omega]
    exact hok R hR _ (by omega)
  · cases hm

theorem ne_of_regions {s : MachineState} {R R' : Region} (hR : ValidMemRange (R.start s) R.n)
    (hR' : ValidMemRange (R'.start s) R'.n)
    (hap : Apart (R.start s) (8 * R.n) (R'.start s) (8 * R'.n)) {a b : Addr} {i j : Nat}
    (hi : R.idx a = some i) (hj : R'.idx b = some j) : a.eval s ≠ b.eval s := by
  obtain ⟨ha, hilt⟩ := Region.idx_eval hi s
  obtain ⟨hb, hjlt⟩ := Region.idx_eval hj s
  have h1 := region_bounds hR (by omega)
  have h2 := region_bounds hR' (by omega)
  rw [ha, hb]
  addr_omega [hap, h1, h2, hilt, hjlt]

theorem neOk_sound {s : MachineState} :
    ∀ {rs : List Region}, RegionsOk s rs → RegionsApart s rs → ∀ {a b : Addr},
      neOk rs a b = true → a.eval s ≠ b.eval s
  | [], _, _, _, _, h => by cases h
  | R :: rs, hok, hap, a, b, h => by
    simp only [neOk, Bool.or_eq_true, Bool.and_eq_true] at h
    have hap' := List.pairwise_cons.mp hap
    have hRok : ValidMemRange (R.start s) R.n := hok R (List.mem_cons_self ..)
    rcases h with (⟨ha, hb⟩ | ⟨hb, ha⟩) | h
    · obtain ⟨R', hR', hb⟩ := List.any_eq_true.mp hb
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp ha
      obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hb
      exact ne_of_regions hRok (hok R' (List.mem_cons_of_mem _ hR')) (hap'.1 R' hR') hi hj
    · obtain ⟨R', hR', ha⟩ := List.any_eq_true.mp ha
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp ha
      obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hb
      exact fun he ↦ ne_of_regions hRok (hok R' (List.mem_cons_of_mem _ hR')) (hap'.1 R' hR')
        hj hi he.symm
    · exact neOk_sound (fun R' h' ↦ hok R' (List.mem_cons_of_mem _ h')) hap'.2 h

theorem oblOk_sound {s : MachineState} {rs : List Region} {bs : List BRegion}
    (hok : RegionsOk s rs) (hap : RegionsApart s rs) (hbok : BRegionsOk s bs) {o : Oblig}
    (h : oblOk rs bs o = true) : o.holds s := by
  cases o with
  | valid a w =>
    simp only [oblOk, Bool.or_eq_true] at h
    rcases h with h | h
    · exact validOk_sound hok h
    · exact validB_sound hbok h
  | ne a b => exact neOk_sound hok hap h
  | align8 _ => cases h
  | apart _ _ => cases h

/-- The check of a side condition: the regions discharge it, or it is listed. -/
def oblCheck (rs : List Region) (bs : List BRegion) (extra : List Oblig) (o : Oblig) : Bool :=
  oblOk rs bs o || extra.any (Oblig.beq o)

theorem oblCheck_sound {s : MachineState} {rs : List Region} {bs : List BRegion}
    (hok : RegionsOk s rs) (hap : RegionsApart s rs) (hbok : BRegionsOk s bs)
    {extra : List Oblig} (hx : Oblig.all s extra) {o : Oblig}
    (h : oblCheck rs bs extra o = true) : o.holds s := by
  simp only [oblCheck, Bool.or_eq_true] at h
  rcases h with h | h
  · exact oblOk_sound hok hap hbok h
  · exact Oblig.holds_of_any hx h

/-- **Side conditions from regions**: every condition of `l` the regions discharge or `extra`
lists. -/
theorem oblig_all {s : MachineState} {rs : List Region} {bs : List BRegion} (hok : RegionsOk s rs)
    (hap : RegionsApart s rs) (hbok : BRegionsOk s bs) {extra : List Oblig}
    (hx : Oblig.all s extra) {l : List Oblig} (hl : l.all (oblCheck rs bs extra) = true) :
    Oblig.all s l :=
  (Oblig.all_iff s l).mpr fun o ho ↦ oblCheck_sound hok hap hbok hx (List.all_eq_true.mp hl o ho)

/-! ## Reading a block's result modulo AC -/

/-- `x` writes `e` (modulo AC) at `k`. -/
def memOk (x : Expect) (k : Addr) (e : E) : Bool :=
  x.mem.any fun p ↦ Addr.beq p.1 k && E.acEq p.2 e

/-- `x` leaves `e` (modulo AC) in `r`. -/
def regOk (x : Expect) (r : Reg) (e : E) : Bool :=
  (x.regs.find? fun p ↦ Reg.beqN p.1 r).isSome && E.acEq (x.reg r) e

theorem _root_.Rv64Verifier.Sym.Expect.Holds.mem_of_ok {x : Expect} {s t : MachineState} (h : x.Holds s t) {k : Addr}
    {e : E} (hk : memOk x k e = true) : t.getMem (k.eval s) = e.eval s := by
  obtain ⟨p, hp, hm⟩ := List.any_eq_true.mp hk
  simp only [Bool.and_eq_true] at hm
  rw [← Addr.beq_eq hm.1, ← E.acEq_eval s hm.2]
  exact h.2.2.1 p hp

theorem _root_.Rv64Verifier.Sym.Expect.Holds.reg_of_ok {x : Expect} {s t : MachineState} (h : x.Holds s t) {r : Reg}
    {e : E} (hk : regOk x r e = true) : t.getReg r = e.eval s := by
  simp only [regOk, Bool.and_eq_true] at hk
  rw [h.reg r hk.1, E.acEq_eval s hk.2]


/-- `a`, a register or a load at a register plus a constant, is `e` (modulo AC) after `x`. -/
def atomOk (x : Expect) (a e : E) : Bool :=
  match a with
  | .reg r => regOk x r e
  | .ld (.bin .add (.reg r) (.c off)) => regOk x r (.reg r) && memOk x ⟨some (.reg r), off⟩ e
  | _ => false

theorem _root_.Rv64Verifier.Sym.Expect.Holds.eval_of_atomOk {x : Expect} {s t : MachineState} (h : x.Holds s t) {a e : E}
    (ha : atomOk x a e = true) : a.eval t = e.eval s := by
  unfold atomOk at ha
  split at ha
  · exact h.reg_of_ok ha
  · rename_i r off
    simp only [Bool.and_eq_true] at ha
    have hr := h.reg_of_ok ha.1
    have hm := h.mem_of_ok ha.2
    simp only [E.eval, BinOp.eval, Addr.eval] at hr hm ⊢
    rw [hr, hm]
  · cases ha

/-- Every write of `x` lies in one of the regions. -/
def writesIn (x : Expect) (rs : List Region) : Bool :=
  x.writes.all fun k ↦ rs.any (Region.has k)

/-- A block whose writes lie in valid regions leaves memory outside them unchanged. -/
theorem _root_.Rv64Verifier.Sym.Expect.Holds.frame_regions {x : Expect} {s t : MachineState} (h : x.Holds s t)
    {rs : List Region} (hok : RegionsOk s rs) (hw : writesIn x rs = true) (a : Word)
    (ha : ∀ R ∈ rs, ¬ Within a (R.start s) (8 * R.n)) : t.getMem a = s.getMem a := by
  apply h.frame a
  intro k hk heq
  obtain ⟨R, hR, hk'⟩ := List.any_eq_true.mp (List.all_eq_true.mp hw k hk)
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hk'
  obtain ⟨he, hlt⟩ := Region.idx_eval hi s
  have hb := region_bounds (hok R hR) (by omega)
  have hnot := ha R hR
  rw [heq, he] at hnot
  exact hnot (by addr_omega [hb, hlt])

/-! ## Runs with side conditions checked by regions -/

/-- `Result.meets` with each side condition discharged by `oblCheck`. -/
def meetsR (cfg : Config) (rs : List Region) (bs : List BRegion) (r : Result) (x : Expect) : Bool :=
  r.steps == x.steps && E.acEq r.pc x.pc &&
    x.regs.all (fun p ↦ E.acEq (r.st.regs.get p.1) p.2) &&
    x.mem.all (fun p ↦ match readMem cfg p.1 r.st.mem with
      | some (e, os) => E.acEq e p.2 && os.all (oblCheck rs bs x.obl)
      | none => false) &&
    r.st.mem.all (fun w ↦ x.writes.any (Addr.beq w.1)) &&
    r.st.obl.all (oblCheck rs bs x.obl)

theorem meetsR_holds {cfg : Config} {rs : List Region} {bs : List BRegion} {r : Result}
    {x : Expect} (h : meetsR cfg rs bs r x = true) {s : MachineState} (hok : RegionsOk s rs)
    (hap : RegionsApart s rs) (hbok : BRegionsOk s bs) (hobl : Oblig.all s x.obl)
    (c : Word → Option Instr) :
    r.steps = x.steps ∧ r.obligs s ∧ x.Holds s (r.toState s c) := by
  simp only [meetsR, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hsteps, hpc⟩, hregs⟩, hmem⟩, hwrites⟩, hobls⟩ := h
  refine ⟨hsteps, (Oblig.all_iff s _).mpr fun o ho ↦ oblCheck_sound hok hap hbok hobl (hobls o ho),
    ?_, ?_, ?_, ?_⟩
  · exact E.acEq_eval s hpc
  · intro p hp
    rw [Result.toState_getReg]
    exact E.acEq_eval s (hregs p hp)
  · intro p hp
    have hp' := hmem p hp
    split at hp'
    · rename_i e os hr
      simp only [Bool.and_eq_true, List.all_eq_true] at hp'
      rw [Result.toState_getMem, readMem_sound hr s fun o ho ↦
        oblCheck_sound hok hap hbok hobl (hp'.2 o ho)]
      exact E.acEq_eval s hp'.1
    · cases hp'
  · intro a ha
    apply Result.toState_getMem_frame
    intro w hw
    obtain ⟨k, hk, hb⟩ := List.any_eq_true.mp (hwrites w hw)
    rw [Addr.beq_eq hb]
    exact ha k hk

/-- **A run from a symbolic state**: the machine at `u`, which the symbolic state `σ` describes
relative to `s`, runs `x.steps` steps to a state meeting `x`. -/
theorem run_spec {cfg : Config} {w code : Code} {pc : Word} {fuel : Nat} {σ : SymState}
    {rs : List Region} {bs : List BRegion} {x : Expect}
    (hrun : (symRunCodeAux cfg w pc fuel σ).any (meetsR cfg rs bs · x) = true)
    (hsub : CodeSub w code) {s u : MachineState} (hu : σ.toState s u.code pc = u)
    (hok : RegionsOk s rs) (hap : RegionsApart s rs) (hbok : BRegionsOk s bs)
    (hobl : Oblig.all s x.obl) :
    ∃ t, Steps code x.steps u t ∧ x.Holds s t := by
  cases hr : symRunCodeAux cfg w pc fuel σ with
  | none => rw [hr] at hrun; cases hrun
  | some r =>
    rw [hr] at hrun
    have hm : meetsR cfg rs bs r x = true := hrun
    obtain ⟨hsteps, hobls, -⟩ := meetsR_holds hm hok hap hbok hobl s.code
    obtain ⟨⟨c, h⟩, -, -⟩ :=
      symRunCodeAux_sound cfg hsub s fuel pc σ r u.code hr ((Oblig.all_iff s _).mp hobls)
    obtain ⟨-, -, hx⟩ := meetsR_holds hm hok hap hbok hobl c
    rw [hu] at h
    exact ⟨_, hsteps ▸ h, hx⟩

/-- The symbolic state that is the identity but for some registers known to be constants. -/
def withConsts (cs : List (Reg × Word)) : SymState :=
  { SymState.init with regs := cs.foldl (fun rf p ↦ rf.set p.1 (.c p.2)) SymState.init.regs }

theorem withConsts_get (cs : List (Reg × Word)) (rf : RegFile) (s : MachineState)
    (hrf : ∀ r, (rf.get r).eval s = s.getReg r) (hcs : ∀ p ∈ cs, s.getReg p.1 = p.2) (r : Reg) :
    ((cs.foldl (fun rf p ↦ rf.set p.1 (.c p.2)) rf).get r).eval s = s.getReg r := by
  induction cs generalizing rf with
  | nil => exact hrf r
  | cons p cs ih =>
    rw [List.foldl_cons]
    refine ih _ (fun r' ↦ ?_) (fun q hq ↦ hcs q (List.mem_cons_of_mem _ hq))
    show ((rf.set p.1 (.c p.2)).get r').eval s = s.getReg r'
    by_cases h0 : p.1 = .x0
    · have : rf.set p.1 (.c p.2) = rf := by rw [h0]; rfl
      rw [this]; exact hrf r'
    · by_cases hr : r' = p.1
      · subst hr
        rw [RegFile.get_set_self _ _ h0]
        exact (hcs p (List.mem_cons_self ..)).symm
      · rw [RegFile.get_set_ne _ _ hr]; exact hrf r'

theorem withConsts_toState (cs : List (Reg × Word)) {s : MachineState}
    (hcs : ∀ p ∈ cs, s.getReg p.1 = p.2) : (withConsts cs).toState s s.code s.pc = s := by
  apply MachineState.ext' <;> try rfl
  funext r
  simp only [SymState.toState, withConsts]
  split
  · rename_i h; subst h; rfl
  · rename_i h
    rw [show SymState.init.regs = RegFile.init from rfl,
      withConsts_get cs _ s (RegFile.init_get_eval s) hcs r]
    cases r <;> first | exact absurd rfl h | rfl

end Rv64Verifier.Hash
