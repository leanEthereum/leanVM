/-
  LeanVM.Guest.Memory.GuestCnt

  The guest's instruction counts by opcode with its hand functions (`Memory/GuestCntH/`,
  `Memory/GuestCntZ/`, written by `scripts/count/cycles.py`), checked by the kernel at the frame
  weights `B2C.ωArm B2C.xmssArmC op` (`cntOm_eq`): the check with hand functions at each opcode, the
  zero-challenge sum counted (`ch_checkedH`) or its functions absent (`cz_checkedH`), and `main`'s
  weight within its inner bound plus the node's constants (`ch_mainWeight_le`, `cz_mainWeight_le`).
-/

module

public import LeanVM.Guest.Memory.GuestCntH.All
public import LeanVM.Guest.Memory.GuestCntZ.All
public import LeanVM.Guest.Memory.HandNodeV
public import LeanVM.Guest.Budget.Arms

/-!
# The guest's instruction counts with hand functions, certified

Every function of the guest's core IR is checked counting each opcode's instructions, a vector
certificate per function (`Memory/FamilyHandV.lean`), at its frame's weights: its `pathMax`, and for
`main_loop2` (leanXMSS's check, inline) the largest of its separately counted arms
(`B2C.xmssArmC`). The table `Data.cntOmJ` is checked against the plumbing's `pmax` by the kernel
(`cntOm_walk`), so its coordinates are `B2C.ωArm B2C.xmssArmC op` (`cntOm_eq`). The hand functions
are `hand.py`'s method not counting words: a count's quotient, `list_split`'s blocks, the Keccak
table's size, `verify_sub`'s shape, `main`'s meta counts; `da_verify` and the children's loop are the
node's (`Memory/HandNodeV.lean`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-! ## The frame weights -/

/-- The weights `ωArm xmssArmC`, an opcode's. -/
noncomputable abbrev ωC (op : Opcode) : String → ℕ := B2C.ωArm B2C.xmssArmC op

theorem cntArm_eq : Data.cntArmJ + 1 = Data.armFn ∧ Data.cntArms = Data.armMax := by decide +kernel

/-- Function `j`'s weights in the table are its plumbing's `pmax` and, for `main_loop2`, its arms. -/
def cntOmOk (j : ℕ) (pl : B2C.Plumb) : Bool :=
  Vec.le (Data.cntOmJ j) (Vec.add pl.pmax (if j = Data.cntArmJ then Data.cntArms else [])) &&
    Vec.le (Vec.add pl.pmax (if j = Data.cntArmJ then Data.cntArms else [])) (Data.cntOmJ j)

set_option maxRecDepth 100000 in
theorem cntOm_walk : walkOk cntOmOk 0 (Data.plumbs.drop 1) = true := by decide +kernel

theorem cnt_plumbs_length : Data.plumbs.length = coreProgram.length + 1 := by
  rw [coreProgram_length]; decide +kernel

theorem cnt_name_arm {j : ℕ} (hj : j < coreProgram.length) :
    coreProgram[j].name = name% «main_loop2» ↔ j = Data.cntArmJ := by
  have hx : (coreProgram[Data.cntArmJ]?).map Fn.name = some (name% «main_loop2») := by decide +kernel
  constructor
  · intro h
    have := coreIdx_getElem hj
    rw [h, coreIdx_of_name hx] at this
    exact this.symm
  · rintro rfl
    rw [List.getElem?_eq_getElem hj] at hx
    simpa using hx

theorem cnt_idxOf {j : ℕ} (hj : j < coreProgram.length) :
    B2C.idxOf coreProgram[j].name = some (j + 1) := by
  unfold B2C.idxOf
  rw [coreProgram_indexOf?_getElem hj]
  rfl

theorem cnt_nth {α : Type} : ∀ (l : List α) (n : ℕ) (d : α), listElementOrDefault l n d = l[n]?.getD d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: as, n + 1, d => cnt_nth as n d

/-- **The table's weights are `B2C.ωArm B2C.xmssArmC`**, every function's. -/
theorem cntOm_eq {j : ℕ} (hj : j < coreProgram.length) (op : Opcode) :
    ωC op coreProgram[j].name = omP Data.cntOmJ (B2C.opIdx op) j := by
  have hl : j + 1 < Data.plumbs.length := by rw [cnt_plumbs_length]; omega
  have hp : (Data.plumbs.drop 1)[j]? = some (B2C.plumbOf (j + 1)) := by
    rw [List.getElem?_drop, B2C.plumbOf, cnt_nth, Nat.add_comm 1 j, List.getElem?_eq_getElem hl]
    rfl
  have hw := walkOk_get cntOm_walk hp
  rw [Nat.zero_add] at hw
  simp only [cntOmOk, Bool.and_eq_true] at hw
  unfold omP
  rw [Nat.le_antisymm (Vec.getD_le hw.1 _) (Vec.getD_le hw.2 _), Vec.getD_add]
  unfold ωC B2C.ωArm B2C.pathMax
  rw [cnt_idxOf hj]
  dsimp only
  by_cases hx : j = Data.cntArmJ
  · subst hx
    simp only [(cnt_name_arm hj).mpr rfl, ↓reduceIte, B2C.xmssArmC, cntArm_eq.2]
  · have hn : ¬ coreProgram[j].name = name% «main_loop2» := fun h => hx ((cnt_name_arm hj).mp h)
    simp [hn, hx]

/-! ## The families -/

/-- **The guest's check with hand functions counting `op`'s instructions, the zero-challenge sum
counted**, by the kernel. -/
theorem ch_checkedH (op : Opcode) :
    CheckedH coreProgram false (fun g => certP Data.chcertJ (B2C.opIdx op) (coreIdx g)) (ωC op)
      (fun g => handP Data.chhandJ (B2C.opIdx op) (coreIdx g))
      (fun g => Data.chabsJ (coreIdx g) = true ∨ (lhP Data.chloopJ (B2C.opIdx op) (coreIdx g)).isSome = true) :=
  checkedH_of_chkHJ (rangeOk_proj _ ch_all) fun _ hj => cntOm_eq hj op

/-- **The guest's check with hand functions counting `op`'s instructions, the zero-challenge sum
absent**, by the kernel. -/
theorem cz_checkedH (op : Opcode) :
    CheckedH coreProgram false (fun g => certP Data.czcertJ (B2C.opIdx op) (coreIdx g)) (ωC op)
      (fun g => handP Data.czhandJ (B2C.opIdx op) (coreIdx g))
      (fun g => Data.czabsJ (coreIdx g) = true ∨ (lhP Data.czloopJ (B2C.opIdx op) (coreIdx g)).isSome = true) :=
  checkedH_of_chkHJ (rangeOk_proj _ cz_all) fun _ hj => cntOm_eq hj op

/-- **The facts about `main`, `da_verify` and the loop, the zero-challenge sum counted**, by the kernel. -/
theorem ch_nodeIdx : NodeIdxV Data.chcertJ Data.chhandJ Data.chloopJ Data.chabsJ Data.chidxMain Data.chidxDa
    Data.chidxLoop where
  hm := by rw [coreProgram_length]; decide
  hl := by rw [coreProgram_length]; decide
  nm := Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)
  nd := Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)
  nl := Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)
  callers := callers_ofV (by rw [coreProgram_length]; decide +kernel)
  loopd := by decide +kernel
  certd := rfl
  certl := rfl
  handd := by decide +kernel
  handm := by decide +kernel
  lhl := by decide +kernel
  absm := by decide +kernel
  lhm := rfl
  absl := by decide +kernel
  topm := by decide +kernel
  sitesd := by decide +kernel
  sitesl := by decide +kernel

/-- **The facts about `main`, `da_verify` and the loop, the zero-challenge sum absent**, by the kernel. -/
theorem cz_nodeIdx : NodeIdxV Data.czcertJ Data.czhandJ Data.czloopJ Data.czabsJ Data.czidxMain Data.czidxDa
    Data.czidxLoop where
  hm := by rw [coreProgram_length]; decide
  hl := by rw [coreProgram_length]; decide
  nm := Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)
  nd := Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)
  nl := Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)
  callers := callers_ofV (by rw [coreProgram_length]; decide +kernel)
  loopd := by decide +kernel
  certd := rfl
  certl := rfl
  handd := by decide +kernel
  handm := by decide +kernel
  lhl := by decide +kernel
  absm := by decide +kernel
  lhm := rfl
  absl := by decide +kernel
  topm := by decide +kernel
  sitesd := by decide +kernel
  sitesl := by decide +kernel

/-- The certificates counting `op`'s instructions at the node's constants `C₁` (`da_verify`), `C₂` (the
loop), the sum counted. -/
noncomputable def chCertAt (op : Opcode) (C₁ C₂ : ℕ) (g : String) : Cert :=
  certAt (certP Data.chcertJ (B2C.opIdx op)) Data.chidxDa Data.chidxLoop C₁ C₂ (coreIdx g)
/-- The hands with `main`'s raised by `C₁ + C₂`, the sum counted. -/
noncomputable def chHandAt (op : Opcode) (C₁ C₂ : ℕ) (g : String) : Option Hand :=
  handAt (handP Data.chhandJ (B2C.opIdx op)) Data.chidxMain (C₁ + C₂) (coreIdx g)
/-- Left out of the check: the loop hand, the sum counted. -/
noncomputable def chOut (op : Opcode) (g : String) : Prop :=
  Data.chabsJ (coreIdx g) = true ∨ (lhP Data.chloopJ (B2C.opIdx op) (coreIdx g)).isSome = true

/-- The certificates counting `op`'s instructions at the node's constants, the sum absent. -/
noncomputable def czCertAt (op : Opcode) (C₁ C₂ : ℕ) (g : String) : Cert :=
  certAt (certP Data.czcertJ (B2C.opIdx op)) Data.czidxDa Data.czidxLoop C₁ C₂ (coreIdx g)
/-- The hands with `main`'s raised by `C₁ + C₂`, the sum absent. -/
noncomputable def czHandAt (op : Opcode) (C₁ C₂ : ℕ) (g : String) : Option Hand :=
  handAt (handP Data.czhandJ (B2C.opIdx op)) Data.czidxMain (C₁ + C₂) (coreIdx g)
/-- Left out of the check: the zero-challenge sum's functions and the loop hand. -/
noncomputable def czOut (op : Opcode) (g : String) : Prop :=
  Data.czabsJ (coreIdx g) = true ∨ (lhP Data.czloopJ (B2C.opIdx op) (coreIdx g)).isSome = true

variable {rd : Reader} {σ : Val} {bufs : List ℕ} {kids : List Tree} {args rets : List E}

/-- **`main`'s tree's instructions of `op` within its inner bound plus the node's constants**, the
zero-challenge sum counted: every node of its callees but the children's loop with its hand fact at the
constants, and the loop's run within `C₂`. -/
theorem ch_mainWeight_le (op : Opcode) (C₁ C₂ : ℕ)
    (hv : (Tree.node "main" σ bufs kids).Valid coreProgram rd args rets)
    (hb : (Tree.node "main" σ bufs kids).BufsOk coreProgram)
    (hkids : ∀ k ∈ kids, k.name = "__loop4_main" ∨
      k.Every (HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op)))
    (hloop : ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params
        (Data.chloopHand.proj (B2C.opIdx op)) (ωC op "__loop4_main")
        (fun k => k.Every (HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op))) k S ∧
        S ≤ C₂)
    (hpre : ArgsPre Data.chmainHand.pre (args ++ Data.chmainHand.vps.map σ)) :
    (Tree.node "main" σ bufs kids).weight (ωC op) ≤
      (Data.chmainHand.b.proj (B2C.opIdx op)).eval (args ++ Data.chmainHand.vps.map σ) + (C₁ + C₂) :=
  mainWeight_le ch_all (B2C.opIdx op) (fun _ hj => cntOm_eq hj op) ch_nodeIdx C₁ C₂ (h := Data.chmainHand)
    rfl (hl := Data.chloopHand) (endc := none) rfl hv hb hkids hloop hpre

/-- **`main`'s tree's instructions of `op` within its inner bound plus the node's constants**, the
zero-challenge sum absent (no `level_residual_sum__*` node, `czOut` in every hand fact). -/
theorem cz_mainWeight_le (op : Opcode) (C₁ C₂ : ℕ)
    (hv : (Tree.node "main" σ bufs kids).Valid coreProgram rd args rets)
    (hb : (Tree.node "main" σ bufs kids).BufsOk coreProgram)
    (hkids : ∀ k ∈ kids, k.name = "__loop4_main" ∨
      k.Every (HandFact coreProgram (czCertAt op C₁ C₂) (czHandAt op C₁ C₂) (czOut op)))
    (hloop : ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[Data.czidxLoop]'cz_nodeIdx.hl).params
        (Data.czloopHand.proj (B2C.opIdx op)) (ωC op "__loop4_main")
        (fun k => k.Every (HandFact coreProgram (czCertAt op C₁ C₂) (czHandAt op C₁ C₂) (czOut op))) k S ∧
        S ≤ C₂)
    (hpre : ArgsPre Data.czmainHand.pre (args ++ Data.czmainHand.vps.map σ)) :
    (Tree.node "main" σ bufs kids).weight (ωC op) ≤
      (Data.czmainHand.b.proj (B2C.opIdx op)).eval (args ++ Data.czmainHand.vps.map σ) + (C₁ + C₂) :=
  mainWeight_le cz_all (B2C.opIdx op) (fun _ hj => cntOm_eq hj op) cz_nodeIdx C₁ C₂ (h := Data.czmainHand)
    rfl (hl := Data.czloopHand) (endc := none) rfl hv hb hkids hloop hpre

/-- The children's loop's last frame weighs its table entry. -/
theorem ωC_loop (op : Opcode) : ωC op "__loop4_main" = omP Data.cntOmJ (B2C.opIdx op) Data.czidxLoop := by
  have h := cntOm_eq cz_nodeIdx.hl op
  have hn : (coreProgram[Data.czidxLoop]'cz_nodeIdx.hl).name = "__loop4_main" := by
    have := cz_nodeIdx.nl; rw [List.getElem?_eq_getElem cz_nodeIdx.hl] at this; exact Option.some.inj this
  rwa [hn] at h

end
end LeanVM.Guest.Memory
