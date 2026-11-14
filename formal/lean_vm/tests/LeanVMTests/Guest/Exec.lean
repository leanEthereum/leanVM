import LeanVM.Guest.Exec
import LeanVM.Guest.Check

/-!
# The symbolic executor and the checker's bounds on guest functions

`exec` evaluated by the kernel on compiled functions of the guest:

* `claim_list_last__L0`, straight code with a `KECCAK`: its one segment, and its contract by
  `exec_sound`, the run returning in fewer steps, gives `KeccakCellsRelation` of the
  thirteen cells it reads (`m0..m3`, the runs from `tail` and `cap`, `b8`) and the two it writes,
  the digest;
* the selectors bounded by booleanity (`Check.selBound`): `r_g` of `shared_selector_tables`
  (`(1 + b₀(1 + g))(1 + b₁(1 + g²))`, below `g^4`) and `rem_g` of `verify_keccak`
  (`(1 + b₀(1 + g))(1 + b₁(1 + g²))(1 + b₂(1 + g⁴))`, below `g^8`), from the atoms of the
  functions' paths.
-/

namespace LeanVMTests.Guest.Exec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

def F0 : Facts := {}

/-! ## A `KECCAK`: `claim_list_last__L0` -/

/-- Its `KECCAK`: the thirteen cells `fp[26], fp[9], fp[10], fp[11]`, `fp[12..15]`, `fp[28]`,
`fp[17..20]`, in the even layout, to the two cells `fp[6..7]`, in the even layout. -/
def hashIns : OffsetInstruction := .keccak 26 9 10 11 12 28 17 6 false false .two

theorem hash_name : Data.f349.name = "claim_list_last__L0" ∧ Data.f349.entryPc = 234105 := by
  decide +kernel

theorem hash_shape : (exec F0 Data.f349).segs.map (fun s ↦ (s.start, s.env.sub Sym.beq .nil,
    (branchExits s.items).isEmpty, (s.items.filterMap Item.atom?).contains (.instr 234126 hashIns),
      s.exit.kind)) = [(0, true, true, true, .ret)] := by
  decide +kernel

/-- **`claim_list_last__L0`'s contract**: a halting run entering it, on the run from `(g^0, 1)`,
returns, in fewer steps, with its `KECCAK` holding: the cells it reads hold a state whose
Keccak-f[1600]'s first two cells the cells it writes hold. -/
theorem hash_spec {κ : ℕ} {L : MemoryImage κ} (hκ : κ ≤ 32) :
    FunSpecReached guestProgram L 234105 (fun _ ↦ True) (fun fp ↦ ∃ input output : Fin 13 → E,
      (∀ c : Fin 13, L.read (fp * addressOfIndex (keccakInOff 26 9 10 11 12 28 17 c.val)) = some
          (input c)) ∧
      (∀ c : Fin 13, c.val < KeccakOutputCells.two.cellCount →
        L.read (fp * addressOfIndex (6 + c.val)) = some (output c)) ∧
      KeccakCellsRelation input false output false .two) := by
  intro fp k _ h
  obtain ⟨s, hs, he⟩ := List.mem_map.mp (hash_shape ▸ List.mem_singleton_self _)
  simp only [Prod.mk.injEq] at he
  obtain ⟨h0, henv, hb, hmem, hkind⟩ := he
  have hctx : Ctx F0 κ fp := ⟨trivial, fun h ↦ absurd h (by decide), hκ⟩
  have hentry : Data.f349.entryPc + s.start = 234105 := by rw [h0]; rfl
  have hrun := exec_sound hctx (guest_fetches (mem_functions (j := 349) rfl)) hs
    (EnvHolds.nil.sub henv) (hentry ▸ h)
  obtain ⟨hall, k', -, hlt, -, -, r, hr, hsafe⟩ :=
    RunK.straight (List.isEmpty_iff.mp hb) hrun
  rw [hkind] at hr
  exact ⟨k', hlt, r, hr, hall _ (List.elem_iff.mp hmem), hsafe⟩

/-! ## Selectors bounded by booleanity -/

open LeanVM.Guest.Check in
/-- The atoms of every path of a function, filed in one book. -/
noncomputable def bookOf (f : CompiledFunction) : Book :=
  ((exec F0 f).segs.flatMap fun s ↦ s.items.filterMap Item.atom?).foldl addFact .nil

theorem names : Data.f11.name = "shared_selector_tables" ∧ Data.f13.name = "verify_keccak" := by
  decide +kernel

open LeanVM.Guest.Check in
/-- `r_g = (1 + b₀(1 + g))(1 + b₁(1 + g²))` in `fp[21]`, the selector of the dispatch on
`log(r_g)` over four arms: `g^e` with `e < 4`. -/
theorem r_g_bound : selBound (bookOf Data.f11) selFuel 21 = some 4 := by decide +kernel

open LeanVM.Guest.Check in
set_option maxRecDepth 100000 in
/-- `rem_g = (1 + b₀(1 + g))(1 + b₁(1 + g²))(1 + b₂(1 + g⁴))` in `fp[60]`, the remainder of a
layer's rounds that `verify_keccak` passes to `keccak_layer`: `g^e` with `e < 8`. -/
theorem rem_g_bound : selBound (bookOf Data.f13) selFuel 60 = some 8 := by decide +kernel

open LeanVM.Guest.Check in
set_option maxRecDepth 100000 in
/-- Its first factor `1 + b₀(1 + g)` in `fp[53]`: `g^e` with `e < 2`. -/
theorem rem_g_factor_bound : selBound (bookOf Data.f13) selFuel 53 = some 2 := by decide +kernel

open LeanVM.Guest.Check in
set_option maxRecDepth 100000 in
/-- A selector bound is only claimed of such a selector: `fp[52] = b₀·(1 + g)` is none. -/
theorem rem_g_scaled_none : selBound (bookOf Data.f13) selFuel 52 = none := by decide +kernel

end LeanVMTests.Guest.Exec
