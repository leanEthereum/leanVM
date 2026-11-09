/-
  LeanVM.Guest.Exec

  The symbolic executor of compiled functions (`ExecCore.lean`): what its segments mean, and its
  soundness, completeness and linking.
-/

module

public import LeanVM.Guest.ExecCore
public import LeanVM.Guest.Bytecode
public import LeanVM.Guest.Logic

namespace LeanVM.Guest.Exec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

@[expose] public section

/-! ## Semantics -/

section Semantics

variable {κ : ℕ} (L : MemoryImage κ) (fp : K)

/-- The environment holds of the frame: every known cell holds its value. -/
def EnvHolds (env : Trie Sym) : Prop :=
  ∀ n v, env.get n = some v → L.read (fp * addressOfIndex n) = some (v.val fp)

/-- The stores hold: `L[fp[q]·g^off] = v`, `fp[q]` a word of `K`. -/
def MemHolds (mem : List (ℕ × ℕ × Sym)) : Prop :=
  ∀ q off v, (q, off, v) ∈ mem → ∃ p, L.read (fp * addressOfIndex q) = some p ∧ IsInK p ∧
    L.read (p.limb 0 * addressOfIndex off) = some (v.val fp)

/-- What is known along a path holds. -/
def St.Holds (st : St) : Prop :=
  EnvHolds L fp st.env ∧ MemHolds L fp st.mem ∧ ∀ x ∈ st.prev, Guest.Holds L x.1 fp x.2

/-- `a` is the register value `t` names. -/
def Tgt.Is (a : K) : Tgt → Prop
  | .gp e => a = addressOfIndex e
  | .fpg e => a = fp * addressOfIndex e
  | .cell o => ∃ v, L.read (fp * addressOfIndex o) = some v ∧ IsInK v ∧ a = v.limb 0

/-- **What an atom means**, of the memory and the frame. -/
def Atom.Holds : Atom → Prop
  | .instr pc ins => Guest.Holds L pc fp ins
  | .jump oc od of => ∃ c d f, L.read (fp * addressOfIndex oc) = some c ∧ L.read (fp * addressOfIndex od) = some d ∧
      L.read (fp * addressOfIndex of) = some f ∧ IsInK c ∧ IsInK d ∧ IsInK f
  | .copy dst src => ∃ v, L.read (fp * addressOfIndex src) = some v ∧ L.read (fp * addressOfIndex dst) = some v
  | .eq a b => ∃ v, L.read (fp * addressOfIndex a) = some v ∧ L.read (fp * addressOfIndex b) = some v
  | .nz x => ∃ v, L.read (fp * addressOfIndex x) = some v ∧ v ≠ 0
  | .ne a b => ∃ u v, L.read (fp * addressOfIndex a) = some u ∧ L.read (fp * addressOfIndex b) = some v ∧ u ≠ v
  | .bool x => ∃ v, L.read (fp * addressOfIndex x) = some v ∧ (v = 0 ∨ v = 1)
  | .range x y k => ∃ e e', e + e' + 1 = k ∧ L.read (fp * addressOfIndex x) = some (ofK (addressOfIndex e)) ∧
      L.read (fp * addressOfIndex y) = some (ofK (addressOfIndex e'))
  | .powPair x y z => ∃ e e', e < 2 ^ κ ∧ e' < 2 ^ κ ∧
      L.read (fp * addressOfIndex x) = some (ofK (addressOfIndex e)) ∧ L.read (fp * addressOfIndex
          y) = some (ofK (addressOfIndex e')) ∧
      L.read (fp * addressOfIndex z) = some (ofK (addressOfIndex (e + e')))

/-- The registers `r` an exit of a function at `entry` leaves to. -/
def Kind.Regs (entry : ℕ) (r : Semantics.Registers K) : Kind → Prop
  | .next t => r = ⟨addressOfIndex (entry + t), fp⟩
  | .ret => retRegs L fp = some r
  | .call pc q _ => ∃ p a, L.read (fp * addressOfIndex q) = some p ∧ IsInK p ∧ pc.Is L fp a ∧
      r = ⟨a, p.limb 0⟩
  | .jump pc f => ∃ a b, pc.Is L fp a ∧ f.Is L fp b ∧ r = ⟨a, b⟩

/-- What else holds at an exit: a callee's frame holds the return registers. -/
def Kind.Extra : Kind → Prop
  | .call _ q r => ∃ p, L.read (fp * addressOfIndex q) = some p ∧ retRegs L (p.limb 0) = some ⟨addressOfIndex r, fp⟩
  | _ => True

/-- **Completeness along a path**: the atoms of `its` hold until the path leaves by a branch
whose exit goes to `r`, or reaches its end with `Q`. -/
def Follows (entry : ℕ) (r : Registers K) (Q : Prop) : List Item → Prop
  | [] => Q
  | .ins a :: its => a.Holds L fp ∧ Follows entry r Q its
  | .fact _ :: its => Follows entry r Q its
  | .branch oc od of x :: its => (Atom.jump oc od of).Holds L fp ∧
      ((L.read (fp * addressOfIndex oc) = some 0 ∧ Follows entry r Q its) ∨
        ((∃ v, L.read (fp * addressOfIndex oc) = some v ∧ v ≠ 0) ∧ x.kind.Regs L fp entry r))

variable (prog : LeanIsaProgram)

/-- An exit is reached with `k` steps left, fewer than the `k₀` the path started with: its
environment and extra facts hold, and the run goes on from its registers. -/
def Exit.Reached (entry k₀ : ℕ) (x : Exit) (k : ℕ) : Prop :=
  k < k₀ ∧ EnvHolds L fp x.env ∧ x.kind.Extra L fp ∧
    ∃ r, x.kind.Regs L fp entry r ∧ SafeReached prog L k r

/-- **Soundness along a path**: from `k` steps left, every atom of `its` holds on the path the run
takes, each executed instruction a step, and the run leaves by a branch's exit, or reaches the
end with `Q` of the steps left. -/
def RunK (entry k₀ : ℕ) (Q : ℕ → Prop) : List Item → ℕ → Prop
  | [], k => Q k
  | .ins a :: its, k => a.Holds L fp ∧ ∃ k', k = k' + 1 ∧ RunK entry k₀ Q its k'
  | .fact a :: its, k => a.Holds L fp ∧ RunK entry k₀ Q its k
  | .branch oc od of x :: its, k => (Atom.jump oc od of).Holds L fp ∧ ∃ k', k = k' + 1 ∧
      ((L.read (fp * addressOfIndex oc) = some 0 ∧ RunK entry k₀ Q its k') ∨
        ((∃ v, L.read (fp * addressOfIndex oc) = some v ∧ v ≠ 0) ∧ x.Reached L fp prog entry k₀ k'))

end Semantics

/-- What the soundness of the executor assumes of a frame: the powers are powers, the frame of
`main` is `1`, and the memory has at most `2^32` words. -/
structure Ctx (F : Facts) (κ : ℕ) (fp : K) : Prop where
  pows : F.pows.Ok
  fpOne : F.fpOne = true → fp = 1
  le : κ ≤ 32

/-- The code from pc `pc` is fetched there, before the last slot. -/
def Fetches (prog : LeanIsaProgram) (pc : ℕ) (code : List OffsetInstruction) : Prop :=
  ∀ j ins, code[j]? = some ins →
    prog.fetch (addressOfIndex (pc + j)) = some ins.toLeanIsaInstruction ∧ pc + j < 2 ^
        prog.logSize - 1

/-! ## Lemmas on values -/

section Values

theorem PowTree.find_ok {t : PowTree} (ht : t.Ok) {k e : ℕ} (h : t.find k = some e) :
    K.ofBits k = addressOfIndex e := by
  induction t with
  | leaf => exact absurd h (by simp [PowTree.find])
  | node k' e' l r ihl ihr =>
    have hf : (PowTree.node k' e' l r).find k =
        (bif k == k' then some e' else bif Nat.blt k k' then l.find k else r.find k) := rfl
    rw [hf] at h
    simp only [Bool.cond_eq_ite, beq_iff_eq] at h
    split_ifs at h with h1 h2
    · subst h1
      obtain rfl := Option.some.inj h
      exact ht.1
    · exact ihl ht.2.1 h
    · exact ihr ht.2.2 h

theorem ofK_zero : ofK 0 = 0 := map_zero (algebraMap K E)

theorem ofK_one : ofK 1 = 1 := map_one (algebraMap K E)

theorem imm_zero : OffsetInstruction.immediateWord 0 0 0 = 0 := by
  rw [OffsetInstruction.immediateWord]
  exact (ofLimbs_eq_zero_iff _).mpr rfl

theorem imm_of_ofBits {k : ℕ} {a : K} (h : K.ofBits k = a) : OffsetInstruction.immediateWord k 0 0 =
    ofK a := by
  rw [OffsetInstruction.immediateWord, h, ofK_eq_ofLimbs]
  rfl

theorem gpow_zero' : addressOfIndex 0 = 1 := pow_zero g

theorem symOf_val {F : Facts} (hp : F.pows.Ok) {k0 k1 k2 : ℕ} {v : Sym}
    (h : F.symOf k0 k1 k2 = some v) (fp : K) : OffsetInstruction.immediateWord k0 k1 k2 = v.val
        fp := by
  simp only [Facts.symOf, Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq] at h
  split_ifs at h with h12 h0 h1
  · obtain ⟨rfl, rfl⟩ := h12
    subst h0
    obtain rfl := Option.some.inj h
    exact imm_zero
  · obtain ⟨rfl, rfl⟩ := h12
    subst h1
    obtain rfl := Option.some.inj h
    rw [Sym.val, gpow_zero']
    exact imm_of_ofBits rfl
  · obtain ⟨rfl, rfl⟩ := h12
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact imm_of_ofBits (PowTree.find_ok hp he)

theorem expo_val {s : Option Sym} {e : ℕ} (h : Sym.expo s = some e) (fp : K) :
    ∃ v, s = some v ∧ v.val fp = ofK (addressOfIndex e) := by
  rcases s with _ | (_ | e' | _) <;> simp [Sym.expo] at h
  exact ⟨_, rfl, by rw [h]; rfl⟩

theorem isOne_val {s : Option Sym} (h : isOne s = true) (fp : K) :
    ∃ v, s = some v ∧ v.val fp = 1 := by
  rcases s with _ | (_ | (_ | e) | _) <;> simp [isOne] at h
  exact ⟨_, rfl, by rw [Sym.val, gpow_zero', ofK_one]⟩

theorem isZero_eq {s : Option Sym} (h : isZero s = true) : s = some .zero := by
  rcases s with _ | (_ | _ | _) <;> simp_all [isZero]

theorem isNonzero_val {s : Option Sym} (h : isNonzero s = true) (fp : K) :
    ∃ v, s = some v ∧ v.val fp ≠ 0 := by
  rcases s with _ | (_ | e | _) <;> simp [isNonzero] at h
  refine ⟨_, rfl, fun h0 ↦ gpow_ne_zero e (ofK_injective ?_)⟩
  rw [ofK_zero]
  exact h0

theorem inK_eq {p : E} (h : IsInK p) : p = ofK (p.limb 0) := by
  rw [ofK_eq_ofLimbs, ofLimbs_of_isInK h]

theorem memFind_mem {m : List (ℕ × ℕ × Sym)} {q off : ℕ} {v : Sym} (h : memFind m q off = some v) :
    (q, off, v) ∈ m := by
  induction m with
  | nil => simp [memFind] at h
  | cons x m ih =>
    obtain ⟨q', off', v'⟩ := x
    simp only [memFind, Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq] at h
    split_ifs at h with hx
    · obtain ⟨rfl, rfl⟩ := hx
      obtain rfl := Option.some.inj h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- Characteristic two: equal sums are equal words. -/
theorem eq_of_add_eq_zero {a b : E} (h : a + b = 0) : a = b := by
  have := congrArg (· + b) h
  simpa [add_assoc, CharTwo.add_self_eq_zero] using this

end Values

section Env

variable {κ : ℕ} {L : MemoryImage κ} {fp : K}

theorem EnvHolds.set {env : Trie Sym} (h : EnvHolds L fp env) {o : ℕ} {v : Sym} {d : ℕ}
    (hv : L.read (fp * addressOfIndex o) = some (v.val fp)) : EnvHolds L fp (env.set v d o) := by
  intro n w hw
  rcases Trie.get_set hw with ⟨rfl, rfl⟩ | hw
  · exact hv
  · exact h n w hw

theorem EnvHolds.learn {env : Trie Sym} (h : EnvHolds L fp env) {o : ℕ} {v : Sym}
    (hv : L.read (fp * addressOfIndex o) = some (v.val fp)) : EnvHolds L fp (Exec.learn env o
        v) := by
  unfold Exec.learn
  split
  · exact h
  · exact h.set hv

theorem EnvHolds.nil : EnvHolds L fp .nil := fun _ _ h ↦ by simp at h

theorem EnvHolds.sub {a b : Trie Sym} (hs : a.sub Sym.beq b = true) (h : EnvHolds L fp b) :
    EnvHolds L fp a :=
  fun n v hv ↦ h n v (Trie.get_of_sub (fun _ _ ↦ Sym.beq_eq) hs hv)

theorem MemHolds.cons {m : List (ℕ × ℕ × Sym)} (h : MemHolds L fp m) {q off : ℕ} {v : Sym}
    (hv : ∃ p, L.read (fp * addressOfIndex q) = some p ∧ IsInK p ∧
      L.read (p.limb 0 * addressOfIndex off) = some (v.val fp)) : MemHolds L fp ((q, off, v) ::
          m) := by
  intro q' off' v' hm
  rcases List.mem_cons.mp hm with he | hm
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact hv
  · exact h q' off' v' hm

theorem MemHolds.take {m : List (ℕ × ℕ × Sym)} (h : MemHolds L fp m) (n : ℕ) :
    MemHolds L fp (m.take n) :=
  fun q off v hm ↦ h q off v (List.mem_of_mem_take hm)

theorem tgtOf_is {env : Trie Sym} (he : EnvHolds L fp env) {o : ℕ} {d : E}
    (hd : L.read (fp * addressOfIndex o) = some d) (hdK : IsInK d) :
    (tgtOf (env.get o) o).Is L fp (d.limb 0) := by
  unfold tgtOf
  split
  · rename_i e h
    have := (he o _ h).symm.trans hd
    obtain rfl := Option.some.inj this
    simp [Tgt.Is, Sym.val]
  · rename_i e h
    have := (he o _ h).symm.trans hd
    obtain rfl := Option.some.inj this
    simp [Tgt.Is, Sym.val]
  · exact ⟨d, hd, hdK, rfl⟩

theorem Tgt.is_unique {t : Tgt} {a b : K} (ha : t.Is L fp a) (hb : t.Is L fp b) : a = b := by
  cases t with
  | gp e => exact ha.trans hb.symm
  | fpg e => exact ha.trans hb.symm
  | cell o =>
    obtain ⟨v, hv, -, rfl⟩ := ha
    obtain ⟨w, hw, -, rfl⟩ := hb
    rw [Option.some.inj (hv.symm.trans hw)]

theorem self_is {F : Facts} (hfp : F.fpOne = true → fp = 1) {t : Tgt} (hs : F.self t = true)
    {a : K} (ha : t.Is L fp a) : a = fp := by
  unfold Facts.self at hs
  split at hs
  · simpa [Tgt.Is, gpow_zero'] using ha
  · simp only [Tgt.Is] at ha
    rw [ha, gpow_zero', hfp hs]
  · exact absurd hs (by simp)

theorem Kind.regs_unique {entry : ℕ} {k : Kind} {r r' : Semantics.Registers K} (h : k.Regs L fp entry r)
    (h' : k.Regs L fp entry r') : r = r' := by
  cases k with
  | next t => exact h.trans h'.symm
  | ret => exact Option.some.inj (h.symm.trans h')
  | call pc q _ =>
    obtain ⟨p, a, hp, -, ha, rfl⟩ := h
    obtain ⟨p', a', hp', -, ha', rfl⟩ := h'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    rw [Tgt.is_unique ha ha']
  | jump pc f =>
    obtain ⟨a, b, ha, hb, rfl⟩ := h
    obtain ⟨a', b', ha', hb', rfl⟩ := h'
    rw [Tgt.is_unique ha ha', Tgt.is_unique hb hb']

end Env


/-! ## One instruction: soundness and completeness -/

section Step

variable {κ : ℕ} {L : MemoryImage κ} {fp : K} {F : Facts}

theorem read_addr (hκ : κ ≤ 32) {a : K} {v : E} (h : L.read a = some v) :
    ∃ i < 2 ^ κ, a = addressOfIndex i := by
  obtain ⟨i, hi, -⟩ := (MemoryImage.read_eq_some_iff (by omega) L).mp h
  exact ⟨i, i.isLt, hi⟩

/-- A word of `K` dereferenced at offset `0` is an address. -/
theorem deref0_addr (hκ : κ ≤ 32) {p v : E} (hpK : IsInK p)
    (h : L.read (p.limb 0 * addressOfIndex 0) = some v) : ∃ i < 2 ^ κ, p = ofK (addressOfIndex
        i) := by
  rw [gpow_zero', mul_one] at h
  obtain ⟨i, hi, he⟩ := read_addr hκ h
  exact ⟨i, hi, by rw [inK_eq hpK, he]⟩

theorem ofK_gpow_mul (a b : ℕ) : ofK (addressOfIndex a) * ofK (addressOfIndex b) = ofK
    (addressOfIndex (a + b)) := by
  rw [← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, pow_add]

theorem mulFacts_holds {a b c pc : ℕ} {env : Trie Sym} (he : EnvHolds L fp env)
    (hh : Guest.Holds L pc fp (.mul a b c)) :
    ∀ x ∈ mulFacts a b c (env.get a) (env.get b), x.Holds L fp := by
  obtain ⟨vA, vB, hA, hB, hC⟩ := hh
  intro x hx
  simp only [mulFacts, List.mem_append] at hx
  rcases hx with hx | hx
  · split_ifs at hx with hab
    · obtain ⟨rfl, rfl⟩ := hab
      simp only [List.mem_singleton] at hx
      subst hx
      obtain rfl := Option.some.inj (hA.symm.trans hB)
      have hsq := Option.some.inj (hA.symm.trans hC)
      refine ⟨_, hA, ?_⟩
      by_cases h0 : vA = 0
      · exact Or.inl h0
      · exact Or.inr (mul_left_cancel₀ h0 ((mul_one vA).trans hsq)).symm
    · simp at hx
  · split_ifs at hx with h1 h2
    · simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨w, hw, hw1⟩ := isOne_val h1 fp
      have := (he b w hw).symm.trans hB
      rw [hw1] at this
      obtain rfl := Option.some.inj this
      exact ⟨vA, hA, by rw [hC, mul_one]⟩
    · simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨w, hw, hw1⟩ := isOne_val h2 fp
      have := (he a w hw).symm.trans hA
      rw [hw1] at this
      obtain rfl := Option.some.inj this
      exact ⟨vB, hB, by rw [hC, one_mul]⟩
    · simp at hx

theorem mulEnv_holds {a b c pc : ℕ} {env : Trie Sym} (he : EnvHolds L fp env)
    (hh : Guest.Holds L pc fp (.mul a b c)) : EnvHolds L fp (mulEnv F env a b c) := by
  obtain ⟨vA, vB, hA, hB, hC⟩ := hh
  unfold mulEnv
  cases F.scaled.contains a
  · exact he
  · simp only [Bool.cond_true]
    split
    · rename_i e hea
      split
      · rename_i e' heb
        apply he.learn
        obtain ⟨w, hw, hwv⟩ := expo_val heb fp
        obtain rfl := Option.some.inj ((he a _ hea).symm.trans hA)
        obtain rfl := Option.some.inj ((he b w hw).symm.trans hB)
        rw [hC, hwv, Sym.val, Sym.val, ← ofK_mul, mul_assoc, addressOfIndex, addressOfIndex,
            addressOfIndex, pow_add]
      · exact he
    · exact he

theorem neFacts_holds {o pc : ℕ} {prev : List (ℕ × OffsetInstruction)}
    (hprev : ∀ x ∈ prev, Guest.Holds L x.1 fp x.2) (hh : Guest.Holds L pc fp (.set o 1 0 0)) :
    ∀ x ∈ neFacts o prev, x.Holds L fp := by
  have h1 : L.read (fp * addressOfIndex o) = some 1 := by
    rw [show (1 : E) = OffsetInstruction.immediateWord 1 0 0 from (imm_of_ofBits rfl).trans ofK_one
        |>.symm]
    exact hh
  unfold neFacts
  split
  next _ x y p' rest =>
    split_ifs with hp
    · subst hp
      obtain ⟨vX, vY, hX, hY, hP⟩ := hprev _ List.mem_cons_self
      have hxy : vX * vY = 1 := Option.some.inj (hP.symm.trans h1)
      have hx0 : vX ≠ 0 := fun h0 ↦ by simp [h0] at hxy
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨vX, hX, hx0⟩
      · split at hz
        next _ a b x' =>
          split_ifs at hz with hx'
          · simp only [List.mem_singleton] at hz
            subst hz hx'
            obtain ⟨vA, vB, hA, hB, hX'⟩ := hprev _ (List.mem_cons_of_mem _ List.mem_cons_self)
            obtain rfl := Option.some.inj (hX.symm.trans hX')
            refine ⟨vA, vB, hA, hB, fun hab ↦ hx0 ?_⟩
            rw [hab, CharTwo.add_self_eq_zero]
          · simp at hz
        next => simp at hz
    · intro z hz
      simp at hz
  next =>
    intro z hz
    simp at hz

theorem rangeFact_holds (hκ : κ ≤ 32) {y t pc : ℕ} {env : Trie Sym} {prev : List (ℕ ×
    OffsetInstruction)}
    (he : EnvHolds L fp env) (hprev : ∀ x ∈ prev, Guest.Holds L x.1 fp x.2)
    (hh : Guest.Holds L pc fp (.deref y 0 t .cell)) : ∀ a ∈ rangeFact env y prev, a.Holds L fp := by
  unfold rangeFact
  split
  next _ x y' z _ x' _ =>
    split_ifs with hxy
    · obtain ⟨rfl, rfl⟩ := hxy
      obtain ⟨vX, vY, hX, hY, hZ⟩ := hprev _ List.mem_cons_self
      obtain ⟨p, v3, hp, hpK, -, hp0⟩ := hprev _ (List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨q, w3, hq, hqK, -, hq0⟩ := hh
      obtain ⟨i, hi, rfl⟩ := deref0_addr hκ hpK hp0
      obtain ⟨j, hj, rfl⟩ := deref0_addr hκ hqK hq0
      obtain rfl := Option.some.inj (hX.symm.trans hp)
      obtain rfl := Option.some.inj (hY.symm.trans hq)
      rw [ofK_gpow_mul] at hZ
      split
      · rename_i k hk
        split_ifs with hk63
        · intro a ha
          simp only [List.mem_singleton] at ha
          subst ha
          obtain ⟨w, hw, hwv⟩ := expo_val hk fp
          have := (he z w hw).symm.trans hZ
          rw [hwv] at this
          have hij := gpow_injOn (show k ∈ Set.Iio (2 ^ 64 - 1) by simp only [Set.mem_Iio]; omega)
            (show i + j ∈ Set.Iio (2 ^ 64 - 1) by
              have : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hκ
              simp only [Set.mem_Iio]; omega)
            (ofK_injective (Option.some.inj this))
          exact ⟨i, j, by omega, hp, hq⟩
        · intro a ha
          simp only [List.mem_singleton] at ha
          subst ha
          exact ⟨i, j, hi, hj, hp, hq, hZ⟩
      · intro a ha
        simp only [List.mem_singleton] at ha
        subst ha
        exact ⟨i, j, hi, hj, hp, hq, hZ⟩
    · intro a ha
      simp at ha
  next =>
    intro a ha
    simp at ha

theorem derefMem_holds {pc o1 o2 o3 : ℕ} {mode : DerefMode} {st : St} (hst : St.Holds L fp st)
    (hh : Guest.Holds L pc fp (.deref o1 o2 o3 mode)) :
    EnvHolds L fp (derefMem pc st o1 o2 o3 mode).1 ∧
      MemHolds L fp (derefMem pc st o1 o2 o3 mode).2 := by
  obtain ⟨p, v3, hp, hpK, h3, hs⟩ := hh
  cases mode with
  | fp =>
    refine ⟨hst.1, (hst.2.1.cons ⟨p, hp, hpK, ?_⟩).take 4⟩
    rw [hs, derefSource_fp, Sym.val, gpow_zero', mul_one]
  | pc =>
    refine ⟨hst.1, (hst.2.1.cons ⟨p, hp, hpK, ?_⟩).take 4⟩
    rw [hs, derefSource_pc]
    rfl
  | cell =>
    simp only [derefMem]
    split
    · rename_i v hv
      obtain ⟨p', hp', -, hs'⟩ := hst.2.1 _ _ _ (memFind_mem hv)
      obtain rfl := Option.some.inj (hp.symm.trans hp')
      have : v3 = v.val fp := Option.some.inj (hs.symm.trans hs')
      exact ⟨hst.1.learn (this ▸ h3), hst.2.1⟩
    · cases o2 == 0
      · exact ⟨hst.1, hst.2.1⟩
      · simp only [Bool.cond_true]
        split
        · rename_i v hv
          have : v3 = v.val fp := Option.some.inj (h3.symm.trans (hst.1 _ _ hv))
          exact ⟨hst.1, (hst.2.1.cons ⟨p, hp, hpK, this ▸ hs⟩).take 4⟩
        · exact ⟨hst.1, hst.2.1⟩

/-- **A non-`JUMP` teaches only what holds.** -/
theorem nonJump_holds (hκ : κ ≤ 32) (hp : F.pows.Ok) {pc : ℕ} {st : St} {ins : OffsetInstruction}
    (hst : St.Holds L fp st) (hh : Guest.Holds L pc fp ins) :
    (∀ a ∈ (nonJump F pc st ins).1, a.Holds L fp) ∧ EnvHolds L fp (nonJump F pc st ins).2.1 ∧
      MemHolds L fp (nonJump F pc st ins).2.2 := by
  cases ins with
  | xor a b c =>
    refine ⟨?_, hst.1, hst.2.1⟩
    simp only [nonJump]
    split_ifs with hz
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨vA, vB, hA, hB, hC⟩ := hh
      have := (hst.1 c _ (isZero_eq hz)).symm.trans hC
      exact ⟨vA, hA, by rw [hB, eq_of_add_eq_zero (Option.some.inj this).symm]⟩
    · intro x hx
      simp at hx
  | mul a b c => exact ⟨mulFacts_holds hst.1 hh, mulEnv_holds hst.1 hh, hst.2.1⟩
  | set o k0 k1 k2 =>
    refine ⟨?_, ?_, hst.2.1⟩
    · simp only [nonJump]
      split_ifs with hk
      · obtain ⟨rfl, rfl, rfl⟩ := hk
        exact neFacts_holds hst.2.2 hh
      · intro x hx
        simp at hx
    · simp only [nonJump]
      split
      · rename_i v hv
        exact hst.1.set (by rw [← symOf_val hp hv fp]; exact hh)
      · exact hst.1
  | deref o1 o2 o3 mode =>
    refine ⟨?_, derefMem_holds hst hh⟩
    simp only [nonJump]
    split_ifs with hm
    · obtain ⟨rfl, rfl⟩ := hm
      exact rangeFact_holds hκ hst.1 hst.2.2 hh
    · intro x hx
      simp at hx
  | keccak => exact ⟨fun x hx ↦ by simp [nonJump] at hx, hst.1, hst.2.1⟩
  | jump => exact absurd hh id

theorem St.Holds.push {st : St} (hst : St.Holds L fp st) {env : Trie Sym}
    {mem : List (ℕ × ℕ × Sym)} (he : EnvHolds L fp env) (hm : MemHolds L fp mem) {pc : ℕ}
    {ins : OffsetInstruction} (hh : Guest.Holds L pc fp ins) : St.Holds L fp (st.push env mem pc
        ins) := by
  refine ⟨he, hm, fun x hx ↦ ?_⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hh
  · exact hst.2.2 x (List.mem_of_mem_take hx)

theorem tgtOf_cell {s : Option Sym} {o q : ℕ} (h : tgtOf s o = .cell q) : q = o := by
  unfold tgtOf at h
  split at h <;> simp_all

/-- **Where a `JUMP` goes is what its exit says.** -/
theorem jumpKind_holds (hfp : F.fpOne = true → fp = 1) {entry len i od of : ℕ} {st : St}
    (hst : St.Holds L fp st) {d f : E} (hd : L.read (fp * addressOfIndex od) = some d) (hdK :
        IsInK d)
    (hf : L.read (fp * addressOfIndex of) = some f) (hfK : IsInK f) :
    (jumpKind F entry len i st od of).1.Regs L fp entry ⟨d.limb 0, f.limb 0⟩ ∧
      (jumpKind F entry len i st od of).1.Extra L fp := by
  unfold jumpKind
  split_ifs with h01
  · obtain ⟨rfl, rfl⟩ := h01
    exact ⟨retRegs_eq_some_iff.mpr ⟨d, f, hd, hf, rfl⟩, trivial⟩
  · rw [Tgt.seq_eq, Tgt.seq_eq]
    have hpt := tgtOf_is hst.1 hd hdK
    have hft := tgtOf_is hst.1 hf hfK
    generalize tgtOf (st.env.get od) od = pt at hpt
    generalize hg : tgtOf (st.env.get of) of = ft at hft
    split_ifs with hself
    · have hb := self_is hfp hself hft
      split
      · rename_i e
        split_ifs with hl
        · refine ⟨?_, trivial⟩
          simp only [Kind.Regs, Tgt.Is] at hpt ⊢
          rw [hpt, hb, show entry + (e - entry) = e by omega]
        · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩
      · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩
      · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩
    · split
      · rename_i q
        obtain rfl := tgtOf_cell hg
        split
        · rename_i r v0 h0 h1
          obtain ⟨w, hw, hwv⟩ := expo_val h0 fp
          obtain ⟨p, hp, hpK, hp0⟩ := hst.2.1 _ _ _ (memFind_mem hw)
          obtain ⟨p', hp', -, hp1⟩ := hst.2.1 _ _ _ (memFind_mem h1)
          obtain rfl := Option.some.inj (hp.symm.trans hp')
          obtain rfl := Option.some.inj (hp.symm.trans hf)
          refine ⟨⟨_, _, hp, hpK, hpt, rfl⟩, p, hp, ?_⟩
          rw [hwv] at hp0
          rw [Sym.val, gpow_zero', mul_one] at hp1
          exact retRegs_eq_some_iff.mpr ⟨_, _, hp0, hp1, by simp⟩
        · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩
      · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩

theorem jumpExit_eq (F : Facts) (entry len i : ℕ) (st : St) (od of : ℕ) :
    jumpExit F entry len i st od of =
      ⟨(jumpKind F entry len i st od of).1, st.env, (jumpKind F entry len i st od of).2⟩ := rfl

end Step


/-! ## One instruction against the run -/

section StepRun

variable {κ : ℕ} {L : MemoryImage κ} {fp : K} {F : Facts} {prog : LeanIsaProgram}

/-- What an instruction's result says of the run from it, with `k` steps left: on to the next
offset with one step fewer, or out by an exit. -/
def Res.Sound (L : MemoryImage κ) (fp : K) (prog : LeanIsaProgram) (entry k₀ i k : ℕ) : Res → Prop
  | .go its st => RunK L fp prog entry k₀
      (fun k' ↦ k' + 1 = k ∧ St.Holds L fp st ∧ SafeReached prog L k' ⟨addressOfIndex (entry + i + 1), fp⟩) its k
  | .stop its x => RunK L fp prog entry k₀ (x.Reached L fp prog entry k₀) its k

/-- What an instruction's result gives a run to `r`: from its atoms, the run reaches `r` by an
exit, or the next offset with `Q`. -/
def Res.Comp (L : MemoryImage κ) (fp : K) (prog : LeanIsaProgram) (entry i : ℕ) (r : Semantics.Registers K) :
    Res → Prop
  | .go its st => ∀ Q : Prop, Follows L fp entry r Q its →
      Reach prog L ⟨addressOfIndex (entry + i), fp⟩ r ∨
        (Q ∧ St.Holds L fp st ∧ Reach prog L ⟨addressOfIndex (entry + i), fp⟩ ⟨addressOfIndex (entry
            + i + 1), fp⟩)
  | .stop its x => Follows L fp entry r (x.kind.Regs L fp entry r) its →
      Reach prog L ⟨addressOfIndex (entry + i), fp⟩ r

theorem stepI_of_nonJump {entry len i : ℕ} {st : St} {ins : OffsetInstruction} (hj : ins.isJump =
    false) :
    stepI F entry len i st ins =
      .go (.ins (.instr (entry + i) ins) :: (nonJump F (entry + i) st ins).1.map .fact)
        (st.push (nonJump F (entry + i) st ins).2.1 (nonJump F (entry + i) st ins).2.2 (entry + i)
          ins) := by
  cases ins with
  | jump => simp [OffsetInstruction.isJump] at hj
  | _ => rfl

theorem runK_facts {entry k₀ k : ℕ} {Q : ℕ → Prop} {fs : List Atom}
    (h : ∀ a ∈ fs, a.Holds L fp) (hq : Q k) : RunK L fp prog entry k₀ Q (fs.map .fact) k := by
  induction fs with
  | nil => exact hq
  | cons a fs ih =>
    exact ⟨h a List.mem_cons_self, ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)⟩

theorem follows_facts {entry : ℕ} {r : Semantics.Registers K} {Q : Prop} {fs : List Atom} :
    Follows L fp entry r Q (fs.map .fact) ↔ Q := by
  induction fs with
  | nil => rfl
  | cons a fs ih => exact ih

theorem jump_atom {oc od of : ℕ} {c d f : E} (hc : L.read (fp * addressOfIndex oc) = some c)
    (hd : L.read (fp * addressOfIndex od) = some d) (hf : L.read (fp * addressOfIndex of) = some f)
        (hcK : IsInK c)
    (hdK : IsInK d) (hfK : IsInK f) : (Atom.jump oc od of).Holds L fp :=
  ⟨c, d, f, hc, hd, hf, hcK, hdK, hfK⟩

/-- **One instruction is sound.** -/
theorem stepI_sound (hctx : Ctx F κ fp) {entry len i k k₀ : ℕ} {st : St} {ins : OffsetInstruction}
    (hf : prog.fetch (addressOfIndex (entry + i)) = some ins.toLeanIsaInstruction)
    (hpc : entry + i < 2 ^ prog.logSize - 1) (hst : St.Holds L fp st) (hk : k ≤ k₀)
    (h : SafeReached prog L k ⟨addressOfIndex (entry + i), fp⟩) :
    (stepI F entry len i st ins).Sound L fp prog entry k₀ i k := by
  cases hj : ins.isJump with
  | false =>
    rw [stepI_of_nonJump hj]
    obtain ⟨k', rfl, hh, hs⟩ := h.fallThrough hf hpc hj
    obtain ⟨hfs, he, hm⟩ := nonJump_holds hctx.le hctx.pows hst hh
    exact ⟨hh, k', rfl, runK_facts hfs ⟨rfl, hst.push he hm hh, hs⟩⟩
  | true =>
    cases ins with
    | jump oc od of =>
      obtain ⟨k', r, rfl, ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, rfl⟩, hs⟩ := h.jump hf hpc
      have hatom := jump_atom hc hd hf' hcK hdK hfK
      obtain ⟨hreg, hext⟩ := jumpKind_holds (entry := entry) (len := len) (i := i) hctx.fpOne hst hd
        hdK hf' hfK
      have hreach : ∀ x, x = jumpExit F entry len i st od of → c ≠ 0 →
          x.Reached L fp prog entry k₀ k' := by
        rintro x rfl hc0
        rw [ite_eq_right hc0] at hs
        exact ⟨by omega, hst.1, hext, _, hreg, hs⟩
      simp only [stepI, optSeq_eq]
      split_ifs with hz hnz
      · have h0 := (hst.1 oc _ (isZero_eq hz)).symm.trans hc
        obtain rfl : c = 0 := (Option.some.inj h0).symm
        rw [ite_eq_left rfl] at hs
        exact ⟨hatom, k', rfl, rfl, hst, by simpa [Nat.add_assoc] using hs⟩
      · obtain ⟨w, hw, hw0⟩ := isNonzero_val hnz fp
        have hcw : c = w.val fp := Option.some.inj (hc.symm.trans (hst.1 oc w hw))
        exact ⟨hatom, k', rfl, hreach _ rfl (hcw ▸ hw0)⟩
      · refine ⟨hatom, k', rfl, ?_⟩
        by_cases hc0 : c = 0
        · subst hc0
          rw [ite_eq_left rfl] at hs
          exact Or.inl ⟨hc, rfl, hst, by simpa [Nat.add_assoc] using hs⟩
        · exact Or.inr ⟨⟨c, hc, hc0⟩, hreach _ rfl hc0⟩
    | _ => simp [OffsetInstruction.isJump] at hj

/-- **One instruction is complete.** -/
theorem stepI_complete (hctx : Ctx F κ fp) {entry len i : ℕ} {st : St} {ins : OffsetInstruction}
    (hf : prog.fetch (addressOfIndex (entry + i)) = some ins.toLeanIsaInstruction)
    (hpc : entry + i < 2 ^ prog.logSize - 1) (hst : St.Holds L fp st) (r : Semantics.Registers K) :
    (stepI F entry len i st ins).Comp L fp prog entry i r := by
  cases hj : ins.isJump with
  | false =>
    rw [stepI_of_nonJump hj]
    rintro Q ⟨hh, hq⟩
    rw [follows_facts] at hq
    obtain ⟨-, he, hm⟩ := nonJump_holds hctx.le hctx.pows hst hh
    exact Or.inr ⟨hq, hst.push he hm hh, reach_fallThrough hf hpc hj hh⟩
  | true =>
    cases ins with
    | jump oc od of =>
      have hgo : ∀ {c d f : E}, L.read (fp * addressOfIndex oc) = some c → L.read (fp *
          addressOfIndex od) = some d →
          L.read (fp * addressOfIndex of) = some f → IsInK c → IsInK d → IsInK f → c ≠ 0 →
          (jumpExit F entry len i st od of).kind.Regs L fp entry r →
          Reach prog L ⟨addressOfIndex (entry + i), fp⟩ r := by
        intro c d f hc hd hf' hcK hdK hfK hc0 hr
        obtain ⟨hreg, -⟩ := jumpKind_holds (entry := entry) (len := len) (i := i) hctx.fpOne hst
          hd hdK hf' hfK
        rw [jumpExit_eq] at hr
        obtain rfl := Kind.regs_unique hr hreg
        exact reach_jump hf hpc ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, by rw [ite_eq_right hc0]⟩
      have hnext : ∀ {d f : E}, L.read (fp * addressOfIndex oc) = some 0 → L.read (fp *
          addressOfIndex od) = some d →
          L.read (fp * addressOfIndex of) = some f → IsInK d → IsInK f →
          Reach prog L ⟨addressOfIndex (entry + i), fp⟩ ⟨addressOfIndex (entry + i + 1), fp⟩ := by
        intro d f hc hd hf' hdK hfK
        exact reach_jump hf hpc ⟨0, d, f, hc, hd, hf', (isInK_iff _).mpr ⟨0, ofK_zero.symm⟩, hdK,
          hfK, by rw [ite_eq_left rfl]⟩
      simp only [stepI, optSeq_eq]
      split_ifs with hz hnz
      · rintro Q ⟨⟨c, d, f, hc, hd, hf', -, hdK, hfK⟩, hq⟩
        have h0 := (hst.1 oc _ (isZero_eq hz)).symm.trans hc
        obtain rfl : c = 0 := (Option.some.inj h0).symm
        exact Or.inr ⟨hq, hst, hnext hc hd hf' hdK hfK⟩
      · rintro ⟨⟨c, d, f, hc, hd, hf', hcK, hdK, hfK⟩, hr⟩
        obtain ⟨w, hw, hw0⟩ := isNonzero_val hnz fp
        have hcw : c = w.val fp := Option.some.inj (hc.symm.trans (hst.1 oc w hw))
        exact hgo hc hd hf' hcK hdK hfK (hcw ▸ hw0) hr
      · rintro Q ⟨⟨c, d, f, hc, hd, hf', hcK, hdK, hfK⟩, ⟨h0, hq⟩ | ⟨⟨v, hv, hv0⟩, hr⟩⟩
        · obtain rfl : c = 0 := Option.some.inj (hc.symm.trans h0)
          exact Or.inr ⟨hq, hst, hnext hc hd hf' hdK hfK⟩
        · obtain rfl := Option.some.inj (hv.symm.trans hc)
          exact Or.inl (hgo hc hd hf' hcK hdK hfK hv0 hr)
    | _ => simp [OffsetInstruction.isJump] at hj

end StepRun


/-! ## Paths: composition -/

section Paths

variable {κ : ℕ} {L : MemoryImage κ} {fp : K} {prog : LeanIsaProgram}

theorem RunK.mono {entry k₀ : ℕ} {Q Q' : ℕ → Prop} (hQ : ∀ k, Q k → Q' k) :
    ∀ {its : List Item} {k : ℕ}, RunK L fp prog entry k₀ Q its k →
      RunK L fp prog entry k₀ Q' its k
  | [], _, h => hQ _ h
  | .ins _ :: _, _, ⟨ha, k', hk, h⟩ => ⟨ha, k', hk, RunK.mono hQ h⟩
  | .fact _ :: _, _, ⟨ha, h⟩ => ⟨ha, RunK.mono hQ h⟩
  | .branch _ _ _ _ :: _, _, ⟨ha, k', hk, h⟩ =>
    ⟨ha, k', hk, h.imp (fun h ↦ ⟨h.1, RunK.mono hQ h.2⟩) id⟩

theorem RunK.append {entry k₀ : ℕ} {Q : ℕ → Prop} :
    ∀ {l₁ l₂ : List Item} {k : ℕ},
      RunK L fp prog entry k₀ (fun k' ↦ RunK L fp prog entry k₀ Q l₂ k') l₁ k →
        RunK L fp prog entry k₀ Q (l₁ ++ l₂) k
  | [], _, _, h => h
  | .ins _ :: _, _, _, ⟨ha, k', hk, h⟩ => ⟨ha, k', hk, RunK.append h⟩
  | .fact _ :: _, _, _, ⟨ha, h⟩ => ⟨ha, RunK.append h⟩
  | .branch _ _ _ _ :: _, _, _, ⟨ha, k', hk, h⟩ =>
    ⟨ha, k', hk, h.imp (fun h ↦ ⟨h.1, RunK.append h.2⟩) id⟩

theorem Follows.append {entry : ℕ} {r : Semantics.Registers K} {Q : Prop} :
    ∀ {l₁ l₂ : List Item}, Follows L fp entry r Q (l₁ ++ l₂) →
      Follows L fp entry r (Follows L fp entry r Q l₂) l₁
  | [], _, h => h
  | .ins _ :: l₁, _, ⟨ha, h⟩ => ⟨ha, Follows.append (l₁ := l₁) h⟩
  | .fact _ :: l₁, _, h => Follows.append (l₁ := l₁) h
  | .branch _ _ _ _ :: l₁, _, ⟨ha, h⟩ =>
    ⟨ha, h.imp (fun h ↦ ⟨h.1, Follows.append (l₁ := l₁) h.2⟩) id⟩

theorem branchExits_append : ∀ (l₁ l₂ : List Item),
    branchExits (l₁ ++ l₂) = branchExits l₁ ++ branchExits l₂
  | [], _ => rfl
  | .ins _ :: l₁, l₂ => branchExits_append l₁ l₂
  | .fact _ :: l₁, l₂ => branchExits_append l₁ l₂
  | .branch _ _ _ x :: l₁, l₂ => congrArg (x :: ·) (branchExits_append l₁ l₂)

theorem mem_branchExits_reverse {x : Exit} : ∀ {l : List Item},
    x ∈ branchExits l.reverse → x ∈ branchExits l
  | [], h => h
  | a :: l, h => by
    rw [List.reverse_cons, branchExits_append, List.mem_append] at h
    rcases h with h | h
    · cases a <;> simp only [branchExits] <;> first | exact List.mem_cons_of_mem _ (mem_branchExits_reverse h) | exact mem_branchExits_reverse h
    · cases a <;> simp_all [branchExits]

theorem branchExits_reverseAux : ∀ (l acc : List Item),
    branchExits (l.reverseAux acc) = (branchExits l).reverseAux (branchExits acc)
  | [], _ => rfl
  | .ins a :: l, acc => branchExits_reverseAux l (.ins a :: acc)
  | .fact a :: l, acc => branchExits_reverseAux l (.fact a :: acc)
  | .branch oc od of x :: l, acc => branchExits_reverseAux l (.branch oc od of x :: acc)

end Paths

/-! ## The pass: soundness and completeness -/

section Pass

variable {κ : ℕ} {L : MemoryImage κ} {fp : K} {F : Facts} {prog : LeanIsaProgram} {entry len : ℕ}

/-- **A good segment**: from its start, with its environment, it is sound (`RunK`) and complete
(`Follows`), and `exits` lists its exits. -/
def SegGood (L : MemoryImage κ) (fp : K) (prog : LeanIsaProgram) (entry : ℕ) (s : Seg) : Prop :=
  (∀ k₀, EnvHolds L fp s.env → SafeReached prog L k₀ ⟨addressOfIndex (entry + s.start), fp⟩ →
    RunK L fp prog entry k₀ (s.exit.Reached L fp prog entry k₀) s.items k₀) ∧
  (EnvHolds L fp s.env → ∀ r, Follows L fp entry r (s.exit.kind.Regs L fp entry r) s.items →
    Reach prog L ⟨addressOfIndex (entry + s.start), fp⟩ r) ∧
  (∀ x, x = s.exit ∨ x ∈ branchExits s.items → x ∈ s.exits)

/-- A good segment being walked, at offset `i`. -/
def CurGood (L : MemoryImage κ) (fp : K) (prog : LeanIsaProgram) (entry : ℕ) (c : Cur) (i : ℕ) :
    Prop :=
  c.start ≤ i ∧ branchExits c.acc = c.xs ∧
  (∀ k₀, EnvHolds L fp c.env → SafeReached prog L k₀ ⟨addressOfIndex (entry + c.start), fp⟩ →
    RunK L fp prog entry k₀ (fun k ↦ k + i = k₀ + c.start ∧ St.Holds L fp c.st ∧
      SafeReached prog L k ⟨addressOfIndex (entry + i), fp⟩) c.acc.reverse k₀) ∧
  (EnvHolds L fp c.env → ∀ r Q, Follows L fp entry r Q c.acc.reverse →
    Reach prog L ⟨addressOfIndex (entry + c.start), fp⟩ r ∨
      (Q ∧ St.Holds L fp c.st ∧ Reach prog L ⟨addressOfIndex (entry + c.start), fp⟩ ⟨addressOfIndex
          (entry + i), fp⟩))

theorem stHolds_init {env : Trie Sym} (he : EnvHolds L fp env) : St.Holds L fp (St.init env) :=
  ⟨he, fun _ _ _ h ↦ by simp [St.init] at h, fun _ h ↦ by simp [St.init] at h⟩

theorem curGood_init (i : ℕ) (env : Trie Sym) : CurGood L fp prog entry (Cur.init i env) i := by
  refine ⟨le_rfl, rfl, fun k₀ he hs ↦ ?_, fun he r Q hq ↦ Or.inr ⟨hq, stHolds_init he, Reach.refl _⟩⟩
  exact ⟨by simp [Cur.init], stHolds_init he, hs⟩

theorem items_close (c : Cur) (its : List Item) :
    ((its.reverseAux c.acc).reverse) = c.acc.reverse ++ its := by
  rw [List.reverseAux_eq, List.reverse_append, List.reverse_reverse]

theorem segGood_close {c : Cur} {i : ℕ} (hc : CurGood L fp prog entry c i) (hlt : c.start < i)
    (succ : List ℕ) : SegGood L fp prog entry (c.close [] ⟨.next i, c.st.env, succ⟩) := by
  obtain ⟨-, hxs, hsound, hcomp⟩ := hc
  refine ⟨fun k₀ he hs ↦ ?_, fun he r hf ↦ ?_, fun x hx ↦ ?_⟩
  · simp only [Cur.close, items_close, List.append_nil]
    refine RunK.mono (fun k ⟨hk, hst, hs'⟩ ↦ ⟨by omega, hst.1, trivial, _, rfl, hs'⟩)
      (hsound k₀ he hs)
  · simp only [Cur.close, items_close, List.append_nil] at hf
    rcases hcomp he r _ hf with h | ⟨rfl, -, h⟩
    · exact h
    · exact h
  · simp only [Cur.close] at hx ⊢
    rcases hx with rfl | hx
    · exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      have := mem_branchExits_reverse hx
      rwa [branchExits_reverseAux, hxs] at this

theorem curGood_go (hctx : Ctx F κ fp) {c : Cur} {i : ℕ} {ins : OffsetInstruction}
    (hc : CurGood L fp prog entry c i) (hf : prog.fetch (addressOfIndex (entry + i)) = some
        ins.toLeanIsaInstruction)
    (hpc : entry + i < 2 ^ prog.logSize - 1) {its : List Item} {st : St}
    (hs : stepI F entry len i c.st ins = .go its st) :
    CurGood L fp prog entry
      ⟨c.start, c.env, its.reverseAux c.acc, (branchExits its).reverseAux c.xs, st⟩ (i + 1) := by
  obtain ⟨hle, hxs, hsound, hcomp⟩ := hc
  refine ⟨show c.start ≤ i + 1 by omega, by simp only; rw [branchExits_reverseAux, hxs],
    fun k₀ he h0 ↦ ?_, fun he r Q hq ↦ ?_⟩
  · simp only
    rw [List.reverseAux_eq, List.reverse_append, List.reverse_reverse]
    refine RunK.append (RunK.mono (fun k ⟨hk, hst, hs'⟩ ↦ ?_) (hsound k₀ he h0))
    have := stepI_sound (len := len) (k₀ := k₀) hctx hf hpc hst (by omega) hs'
    rw [hs] at this
    refine RunK.mono (fun k' ⟨hk', hst', hs''⟩ ↦ ⟨by omega, hst', ?_⟩) this
    simpa [Nat.add_assoc] using hs''
  · simp only at hq
    rw [List.reverseAux_eq, List.reverse_append, List.reverse_reverse] at hq
    rcases hcomp he r _ (Follows.append hq) with h | ⟨hq', hst, h⟩
    · exact Or.inl h
    · have := stepI_complete (len := len) hctx hf hpc hst r
      rw [hs] at this
      rcases this Q hq' with h' | ⟨hQ, hst', h'⟩
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨hQ, hst', by simpa [Nat.add_assoc] using h.trans h'⟩

theorem segGood_stop (hctx : Ctx F κ fp) {c : Cur} {i : ℕ} {ins : OffsetInstruction}
    (hc : CurGood L fp prog entry c i) (hf : prog.fetch (addressOfIndex (entry + i)) = some
        ins.toLeanIsaInstruction)
    (hpc : entry + i < 2 ^ prog.logSize - 1) {its : List Item} {x : Exit}
    (hs : stepI F entry len i c.st ins = .stop its x) : SegGood L fp prog entry (c.close its x) := by
  obtain ⟨hle, hxs, hsound, hcomp⟩ := hc
  refine ⟨fun k₀ he h0 ↦ ?_, fun he r hq ↦ ?_, fun y hy ↦ ?_⟩
  · simp only [Cur.close, items_close]
    refine RunK.append (RunK.mono (fun k ⟨hk, hst, hs'⟩ ↦ ?_) (hsound k₀ he h0))
    have := stepI_sound (len := len) (k₀ := k₀) hctx hf hpc hst (by omega) hs'
    rw [hs] at this
    exact this
  · simp only [Cur.close, items_close] at hq
    rcases hcomp he r _ (Follows.append hq) with h | ⟨hq', hst, h⟩
    · exact h
    · have := stepI_complete (len := len) hctx hf hpc hst r
      rw [hs] at this
      exact h.trans (this hq')
  · simp only [Cur.close] at hy ⊢
    rcases hy with rfl | hy
    · exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      have := mem_branchExits_reverse hy
      rwa [branchExits_reverseAux, hxs] at this

theorem atJoin_good {i : ℕ} {cur : Option Cur} {pend : Pend} {out : List Seg}
    (hcur : ∀ c, cur = some c → CurGood L fp prog entry c i)
    (hout : ∀ s ∈ out, SegGood L fp prog entry s) :
    (∀ c, (atJoin i cur pend out).1 = some c → CurGood L fp prog entry c i) ∧
      ∀ s ∈ (atJoin i cur pend out).2.2, SegGood L fp prog entry s := by
  unfold atJoin
  split
  · rename_i t a ps
    split_ifs with ht
    · cases cur with
      | some c =>
        simp only [Trie.seq_eq]
        split_ifs with hlt
        · refine ⟨fun c' hc' ↦ ?_, fun s hs ↦ ?_⟩
          · obtain rfl := Option.some.inj hc'
            exact curGood_init i _
          · rcases List.mem_cons.mp hs with rfl | hs
            · exact segGood_close (hcur c rfl) hlt [i]
            · exact hout s hs
        · refine ⟨fun c' hc' ↦ ?_, hout⟩
          obtain rfl := Option.some.inj hc'
          exact curGood_init i _
      | none =>
        simp only [Trie.seq_eq]
        refine ⟨fun c' hc' ↦ ?_, hout⟩
        obtain rfl := Option.some.inj hc'
        exact curGood_init i _
    · exact ⟨hcur, hout⟩
  · exact ⟨hcur, hout⟩

theorem Fetches.tail {pc : ℕ} {ins : OffsetInstruction} {rest : List OffsetInstruction}
    (h : Fetches prog pc (ins :: rest)) : Fetches prog (pc + 1) rest := by
  intro j ins' hj
  have := h (j + 1) ins' (by simpa using hj)
  simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem Fetches.head {pc : ℕ} {ins : OffsetInstruction} {rest : List OffsetInstruction}
    (h : Fetches prog pc (ins :: rest)) :
    prog.fetch (addressOfIndex pc) = some ins.toLeanIsaInstruction ∧ pc < 2 ^ prog.logSize - 1 := by
  simpa using h 0 ins rfl

/-- **The walk produces good segments.** -/
theorem pass_good (hctx : Ctx F κ fp) : ∀ (code : List OffsetInstruction) (i : ℕ) (cur : Option Cur)
    (pend : Pend) (out : List Seg) (dead : ℕ), Fetches prog (entry + i) code →
    (∀ c, cur = some c → CurGood L fp prog entry c i) →
    (∀ s ∈ out, SegGood L fp prog entry s) →
    ∀ s ∈ (pass F entry len code i cur pend out dead).segs, SegGood L fp prog entry s
  | [], i, cur, pend, out, dead, _, hcur, hout => by
    show ∀ s ∈ (passEnd len i cur out dead).segs, _
    unfold passEnd
    cases cur with
    | none => exact hout
    | some c =>
      simp only
      by_cases hlt : c.start < i
      · rw [ite_eq_left hlt]
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact segGood_close (hcur c rfl) hlt _
        · exact hout s hs
      · rw [ite_eq_right hlt]
        exact hout
  | ins :: rest, i, cur, pend, out, dead, hf, hcur, hout => by
    show ∀ s ∈ (passStep F entry len ins (pass F entry len rest) i cur pend out dead).segs, _
    obtain ⟨hcur', hout'⟩ := atJoin_good (pend := pend) hcur hout
    have hrest : Fetches prog (entry + (i + 1)) rest := by
      simpa [Nat.add_assoc] using hf.tail
    obtain ⟨hfi, hpc⟩ := hf.head
    unfold passStep
    rcases hj : atJoin i cur pend out with ⟨cur', pend', out'⟩
    rw [hj] at hcur' hout'
    cases cur' with
    | none =>
      simp only [natSeq_eq]
      exact pass_good hctx rest (i + 1) none pend' out' (dead + 1) hrest (fun _ h ↦ by cases h)
        hout'
    | some c =>
      have hc := hcur' c rfl
      simp only
      rcases hs : stepI F entry len i c.st ins with ⟨its, st⟩ | ⟨its, x⟩
      · simp only [St.seq_eq, headSeq_eq, natSeq_eq]
        exact pass_good hctx rest (i + 1) _ _ out' dead hrest
          (fun c' h ↦ Option.some.inj h ▸ curGood_go hctx hc hfi hpc hs) hout'
      · simp only [headSeq_eq, natSeq_eq]
        refine pass_good hctx rest (i + 1) none _ _ dead hrest (fun _ h ↦ by cases h) ?_
        intro s hs'
        rcases List.mem_cons.mp hs' with rfl | hs'
        · exact segGood_stop hctx hc hfi hpc hs
        · exact hout' s hs'

end Pass


/-! ## The executor: soundness, completeness, linking -/

section Main

variable {κ : ℕ} {L : MemoryImage κ} {fp : K} {F : Facts} {prog : LeanIsaProgram} {f :
    CompiledFunction}

/-- Every segment of `exec F f` is good. -/
theorem exec_good (hctx : Ctx F κ fp) (hf : Fetches prog f.entryPc f.code) :
    ∀ s ∈ (exec F f).segs, SegGood L fp prog f.entryPc s :=
  pass_good hctx f.code 0 _ [] [] 0 (by simpa using hf)
    (fun _ h ↦ Option.some.inj h ▸ curGood_init 0 _) (fun _ h ↦ by cases h)

/-- **Soundness**: a halting run entering a segment of `exec F f` at its start, in a frame its
environment holds of, satisfies every atom of the path it takes, one step per instruction, and
leaves by that path's exit (`Exit.Reached`: with fewer steps left, its environment holding,
at the registers its kind names). -/
theorem exec_sound (hctx : Ctx F κ fp) (hf : Fetches prog f.entryPc f.code) {s : Seg}
    (hs : s ∈ (exec F f).segs) {k : ℕ} (he : EnvHolds L fp s.env)
    (h : SafeReached prog L k ⟨addressOfIndex (f.entryPc + s.start), fp⟩) :
    RunK L fp prog f.entryPc k (s.exit.Reached L fp prog f.entryPc k) s.items k :=
  (exec_good hctx hf s hs).1 k he h

theorem index_get {segs : List Seg} {t : ℕ} {s : Seg} (h : (index segs).get t = some s) :
    s ∈ segs := by
  have key : ∀ (l : List Seg) (acc : Trie Seg),
      (l.foldl (fun t s ↦ t.set s indexDepth s.start) acc).get t = some s →
        s ∈ l ∨ acc.get t = some s := by
    intro l
    induction l with
    | nil => exact fun _ h ↦ Or.inr h
    | cons a l ih =>
      intro acc h
      rcases ih _ h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases Trie.get_set h with ⟨-, rfl⟩ | h
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h
  rcases key segs .nil h with h | h
  · exact h
  · simp at h

/-- **Linking**: when the result is linked, every successor of an exit starts a segment whose
entry environment holds wherever the exit's does. -/
theorem Result.linked_spec {R : Result} (hl : R.linked = true) {s : Seg} (hs : s ∈ R.segs)
    {x : Exit} (hx : x ∈ s.exits) {t : ℕ} (ht : t ∈ x.succ) :
    ∃ s' ∈ R.segs, s'.start = t ∧
      ∀ {κ : ℕ} (L : MemoryImage κ) (fp : K), EnvHolds L fp x.env → EnvHolds L fp s'.env := by
  obtain ⟨segs, dead⟩ := R
  simp only [Result.linked, listSeq_eq, Trie.seq_eq, linkedWith, List.all_eq_true] at hl
  have h := hl s hs x hx t ht
  split at h
  · rename_i s' hs'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨s', index_get hs', h.1, fun L fp he ↦ he.sub h.2⟩
  · exact absurd h (by simp)

/-- The code of a guest function is fetched at its pcs. -/
theorem guest_fetches {f : CompiledFunction} (hf : f ∈ Data.functions) : Fetches guestProgram f.entryPc f.code := by
  intro j ins hj
  have hw := CompiledFunction.wellChunked_of_mem hf
  obtain ⟨hjl, -⟩ := List.getElem?_eq_some_iff.mp hj
  rw [CompiledFunction.length_code hw] at hjl
  rw [CompiledFunction.getElem?_code hw hjl] at hj
  obtain rfl := Option.some.inj hj
  exact ⟨guest_fetch hf hjl, guest_pc_lt hf hjl⟩

end Main


/-! ## Straight segments -/

section Straight

variable {κ : ℕ} {L : MemoryImage κ} {fp : K} {prog : LeanIsaProgram}

/-- The atom of an item, if it has one of its own. -/
def Item.atom? : Item → Option Atom
  | .ins a => some a
  | .fact a => some a
  | .branch .. => none

/-- **A path without branches**: every atom holds, and the end is reached. -/
theorem RunK.straight {entry k₀ : ℕ} {Q : ℕ → Prop} :
    ∀ {its : List Item} {k : ℕ}, branchExits its = [] → RunK L fp prog entry k₀ Q its k →
      (∀ a ∈ its.filterMap Item.atom?, a.Holds L fp) ∧ ∃ k' ≤ k, Q k'
  | [], k, _, h => ⟨fun _ h ↦ by simp at h, k, le_rfl, h⟩
  | .ins a :: its, _, hb, ⟨ha, k', rfl, h⟩ => by
    obtain ⟨hs, k'', hk, hq⟩ := RunK.straight (its := its) hb h
    refine ⟨fun b hb' ↦ ?_, k'', by omega, hq⟩
    simp only [List.filterMap_cons, Item.atom?, List.mem_cons] at hb'
    rcases hb' with rfl | hb'
    · exact ha
    · exact hs b hb'
  | .fact a :: its, k, hb, ⟨ha, h⟩ => by
    obtain ⟨hs, k'', hk, hq⟩ := RunK.straight (its := its) hb h
    refine ⟨fun b hb' ↦ ?_, k'', hk, hq⟩
    simp only [List.filterMap_cons, Item.atom?, List.mem_cons] at hb'
    rcases hb' with rfl | hb'
    · exact ha
    · exact hs b hb'
  | .branch _ _ _ _ :: _, _, hb, _ => by simp [branchExits] at hb

end Straight


/-! ## Windows -/

section Windows

variable {κ : ℕ} {L : MemoryImage κ} {fp : K} {F : Facts} {prog : LeanIsaProgram} {f :
    CompiledFunction}

theorem Fetches.window {pc : ℕ} {code : List OffsetInstruction} (h : Fetches prog pc code) (a
    n : ℕ) :
    Fetches prog (pc + a) ((code.drop a).take n) := by
  intro j ins hj
  rw [List.getElem?_take] at hj
  split_ifs at hj
  rw [List.getElem?_drop] at hj
  simpa [Nat.add_assoc] using h (a + j) ins hj

/-- Every segment of a window is good. -/
theorem execWin_good (hctx : Ctx F κ fp) (hf : Fetches prog f.entryPc f.code) (a : ℕ)
    (env : List (ℕ × Sym)) (b : ℕ) : ∀ s ∈ (execWin F f a env b).segs, SegGood L fp prog f.entryPc s :=
  pass_good hctx _ a _ [] [] 0 (hf.window a (b - a))
    (fun _ h ↦ Option.some.inj h ▸ curGood_init a _) (fun _ h ↦ by cases h)

/-- Every segment of a window entered at several offsets is good. -/
theorem execWinS_good (hctx : Ctx F κ fp) (hf : Fetches prog f.entryPc f.code) (a : ℕ)
    (env : List (ℕ × Sym)) (seeds : List ℕ) (b : ℕ) :
    ∀ s ∈ (execWinS F f a env seeds b).segs, SegGood L fp prog f.entryPc s :=
  pass_good hctx _ a _ _ [] 0 (hf.window a (b - a))
    (fun _ h ↦ Option.some.inj h ▸ curGood_init a _) (fun _ h ↦ by cases h)

/-- **Linking across windows**: every successor of an exit of a window starts one of its
segments, or one of the windows `ext`, with an environment holding where the exit's does. -/
theorem Result.linkedExt_spec {ext : List (ℕ × List (ℕ × Sym))} {R : Result}
    (hl : R.linkedExt ext = true) {s : Seg} (hs : s ∈ R.segs) {x : Exit} (hx : x ∈ s.exits) {t : ℕ}
    (ht : t ∈ x.succ) :
    (∃ s' ∈ R.segs, s'.start = t ∧
      ∀ {κ : ℕ} (L : MemoryImage κ) (fp : K), EnvHolds L fp x.env → EnvHolds L fp s'.env) ∨
    ∃ e, (t, e) ∈ ext ∧
      ∀ {κ : ℕ} (L : MemoryImage κ) (fp : K), EnvHolds L fp x.env → EnvHolds L fp (envOf e) := by
  obtain ⟨segs, dead⟩ := R
  simp only [Result.linkedExt, listSeq_eq, Trie.seq_eq, linkedExtWith, List.all_eq_true] at hl
  have h := hl s hs x hx t ht
  split at h
  · rename_i s' hs'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact Or.inl ⟨s', index_get hs', h.1, fun L fp he ↦ he.sub h.2⟩
  · split at h
    · rename_i e he
      have hu := List.find?_some he
      have hmem := List.mem_of_find?_eq_some he
      obtain ⟨⟨u', e0⟩, hm0, rfl⟩ := List.mem_map.mp hmem
      simp only [beq_iff_eq] at hu
      subst hu
      exact Or.inr ⟨e0, hm0, fun L fp hx' ↦ hx'.sub h⟩
    · exact absurd h (by simp)

end Windows

end
end LeanVM.Guest.Exec
