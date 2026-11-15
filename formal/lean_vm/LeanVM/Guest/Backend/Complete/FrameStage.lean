/-
  LeanVM.Guest.Backend.Complete.FrameStage

  A `match` on the path as one stage: the head of a chain whose arms jump to the join.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameMatch
public import LeanVM.Guest.Backend.Complete.FrameEdge
public import LeanVM.Guest.Backend.Complete.FramePool

/-!
# A `match` whose arms jump to the join

`match_pre`: a `match` statement's edge flush and the reset of the chaining flags, the invariant's
facts after them handed on. `head1`: from there, a `match` whose arms do not dispatch into the next
one (`placeMatch … none false`): its cells (selector, frame pointer, `1`, the join, the first
table, the entry, whose words are those of the final placement read ahead: `joinW`, `entryW`), its
arms (the picked one on the path, `placeArms_pick`), its `emit` and the chain node; the outcome is
`BlockOut` of `[.match_ x arms]`. `stmtW_match`: `StmtW` of a `match` the statements after which
do not start with a `match` (a chained `match` then fails to place).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The scope walk of a `match` -/

section Scope

theorem scopeMatch_inv {rc : ℕ} {x : V} {arms : List (List Stmt)} {s s' : SSt}
    (h : scopeStmt rc (.match_ x arms) s = .ok s') : ∃ s₀ s₁, flushEdge rc s = .ok s₀ ∧
      s₀.live.contains x = true ∧ scopeArms rc arms s₀ s₀.retDone = .ok s₁ ∧
      expectS isEmit "a match" s₁ = .ok s' := by
  simp only [scopeStmt] at h
  split at h
  · cases h
  next s₀ h₀ =>
  split at h
  · cases h
  next hn =>
  split at h
  · cases h
  next s₁ h₁ =>
  refine ⟨s₀, s₁, h₀, ?_, h₁, h⟩
  unfold needScope at hn
  split at hn
  · rename_i hi
    simpa [inScope] using hi
  · cases hn

end Scope

/-! ## A stage's pieces -/

section Pieces

variable {ctx : Backend.Ctx} {I : Inst} {C : (ℕ → E) → Prop} {st : St}

theorem matchCells_lz {x : V} {rest : List Stmt} {chained : Bool} :
    LzAt ctx st (matchCells x rest chained) := by
  unfold matchCells
  lz_straight

theorem matchCells_placed {x : V} {rest : List Stmt} {chained : Bool} :
    wpP (matchCells x rest chained) ctx st fun _ _ => st.locs[x]? ≠ none := by
  unfold matchCells
  exact wp_bind.mpr (wp_mono (cellOf_placed x) fun _ _ h _ _ _ => h)

/-- **The cells an unchained `match` jumps with**, the cells the constraint left free kept. -/
theorem matchCells_fatB (hI : I.Ok) (hmain : ctx.isMain = true → I.fp = 0) {x : V}
    {rest : List Stmt} {ok : V → Prop} (hv : VW I C st ok) (hx : ok x) (h2 : 2 ≤ st.next) :
    FAt ctx I C st (matchCells x rest false) fun r C' st' => r.2.1 = none ∧
      2 ≤ r.1 ∧ r.1 < st'.next ∧ (∀ Ψ, C' Ψ → Ψ r.1 = I.σ x) ∧
      2 ≤ r.2.2.1 ∧ r.2.2.1 < st'.next ∧ (∀ Ψ, C' Ψ → Ψ r.2.2.1 = I.fpw) ∧
      2 ≤ r.2.2.2 ∧ r.2.2.2 < st'.next ∧ (∀ Ψ, C' Ψ → Ψ r.2.2.2 = 1) ∧
      st'.locs = st.locs ∧ st'.rest = st.rest ∧ KeepB C C' st.next := by
  unfold matchCells
  simp only [Bool.false_eq_true, ite_false]
  refine FAt.bind (cellOf_fat x hI hv hx)
    fun lx st₁ C₁ _ hn₁ _ ⟨hx2, hxlt, hlo₁, hr₁, hxw, hkb₁⟩ => ?_
  refine FAt.bind (FAt.pure (R := fun a C' st' => a = (none : Option (Cell × ℕ)) ∧ C' = C₁ ∧
    st' = st₁) ⟨rfl, rfl, rfl⟩) fun ns st₂ C₂ _ _ _ ⟨hns, hC₂, hst₂⟩ => ?_
  subst hC₂ hst₂
  refine FAt.bind (selfFp_fat hI hmain (le_trans h2 hn₁))
    fun sfp st₃ C₃ hs₃ hn₃ _ ⟨hf2, hflt, hlo₃, hr₃, hfw, hkb₃⟩ => ?_
  refine FAt.bind (constCell_fatB (1, 0) (hI.kconst 1 0) (le_trans h2 (le_trans hn₁ hn₃)))
    fun one st₄ C₄ hs₄ hn₄ _ ⟨ho2, holt, hlo₄, hr₄, how, hkb₄⟩ => ?_
  refine FAt.pure ⟨hns, hx2, lt_of_lt_of_le hxlt (le_trans hn₃ hn₄),
    fun Ψ hΨ => hxw Ψ (hs₃ Ψ (hs₄ Ψ hΨ)), hf2, lt_of_lt_of_le hflt hn₄,
    fun Ψ hΨ => hfw Ψ (hs₄ Ψ hΨ), ho2, holt, fun Ψ hΨ => (how Ψ hΨ).trans word_one,
    by rw [hlo₄, hlo₃, hlo₁], by rw [hr₄, hr₃, hr₁],
    (hkb₁.trans hkb₃ hn₁).trans hkb₄ (le_trans hn₁ hn₃)⟩

/-- **The cells of a `match` whose arms dispatch into the next one** (`x'`, whose cell holds its
value), the cells the constraint left free kept. -/
theorem matchCells_fatC (hI : I.Ok) (hmain : ctx.isMain = true → I.fp = 0) {x x' : V}
    {arms' : List (List Stmt)} {rest' : List Stmt} {ok : V → Prop} (hv : VW I C st ok) (hx : ok x)
    (hx' : ok x') (h2 : 2 ≤ st.next) :
    FAt ctx I C st (matchCells x (.match_ x' arms' :: rest') true) fun r C' st' =>
      (∃ lx', r.2.1 = some (lx', arms'.length) ∧ 2 ≤ lx' ∧ lx' < st'.next ∧
        ∀ Ψ, C' Ψ → Ψ lx' = I.σ x') ∧
      2 ≤ r.1 ∧ r.1 < st'.next ∧ (∀ Ψ, C' Ψ → Ψ r.1 = I.σ x) ∧
      2 ≤ r.2.2.1 ∧ r.2.2.1 < st'.next ∧ (∀ Ψ, C' Ψ → Ψ r.2.2.1 = I.fpw) ∧
      2 ≤ r.2.2.2 ∧ r.2.2.2 < st'.next ∧ (∀ Ψ, C' Ψ → Ψ r.2.2.2 = 1) ∧
      st'.locs = st.locs ∧ st'.rest = st.rest ∧ KeepB C C' st.next := by
  unfold matchCells
  simp only [ite_true]
  refine FAt.bind (cellOf_fat x hI hv hx)
    fun lx st₁ C₁ hs₁ hn₁ _ ⟨hx2, hxlt, hlo₁, hr₁, hxw, hkb₁⟩ => ?_
  simp only [pure_bind]
  refine FAt.bind (cellOf_fat x' hI (hv.step hs₁ hn₁ hlo₁) hx')
    fun lx' st₂ C₂ hs₂ hn₂ _ ⟨hy2, hylt, hlo₂, hr₂, hyw, hkb₂⟩ => ?_
  refine FAt.bind (selfFp_fat hI hmain (le_trans h2 (le_trans hn₁ hn₂)))
    fun sfp st₃ C₃ hs₃ hn₃ _ ⟨hf2, hflt, hlo₃, hr₃, hfw, hkb₃⟩ => ?_
  refine FAt.bind (constCell_fatB (1, 0) (hI.kconst 1 0)
      (le_trans h2 (le_trans hn₁ (le_trans hn₂ hn₃))))
    fun one st₄ C₄ hs₄ hn₄ _ ⟨ho2, holt, hlo₄, hr₄, how, hkb₄⟩ => ?_
  refine FAt.pure ⟨⟨lx', rfl, hy2, lt_of_lt_of_le hylt (le_trans hn₃ hn₄),
      fun Ψ hΨ => hyw Ψ (hs₃ Ψ (hs₄ Ψ hΨ))⟩, hx2,
    lt_of_lt_of_le hxlt (le_trans hn₂ (le_trans hn₃ hn₄)),
    fun Ψ hΨ => hxw Ψ (hs₂ Ψ (hs₃ Ψ (hs₄ Ψ hΨ))), hf2, lt_of_lt_of_le hflt hn₄,
    fun Ψ hΨ => hfw Ψ (hs₄ Ψ hΨ), ho2, holt, fun Ψ hΨ => (how Ψ hΨ).trans word_one,
    by rw [hlo₄, hlo₃, hlo₂, hlo₁], by rw [hr₄, hr₃, hr₂, hr₁],
    ((hkb₁.trans hkb₂ hn₁).trans hkb₃ (le_trans hn₁ hn₂)).trans hkb₄
      (le_trans hn₁ (le_trans hn₂ hn₃))⟩

/-- A chained `match` followed by no `match` fails to place, whatever follows. -/
theorem chained_fail {x : V} {n : ℕ} {rest : List Stmt} {e : Option (ℕ × Cell)}
    {armsAt : Cell → ArmExit → P (List (List PStmt))} {Q : Unit → St → Prop} {g : Unit → P Unit}
    (hnc : ∀ x' arms' rest', rest ≠ .match_ x' arms' :: rest') :
    wpP (placeMatch x n rest e true armsAt >>= g) ctx st Q := by
  unfold placeMatch matchCells
  simp only [ite_true, bind_assoc]
  refine wp_bind.mpr fun _ _ _ => ?_
  cases rest with
  | nil => exact wp_bind.mpr wp_failP
  | cons s r =>
    cases s <;> first
      | exact absurd rfl (hnc _ _ _)
      | exact wp_bind.mpr wp_failP

/-- **The next stage's selector is known to the stage before it**: in scope there, or made by
the events its edge flush passes (then not yet placed). -/
theorem nextSel_live {rc : ℕ} {x : V} {s₀ s₁ sc' s₀' : SSt} {arms : List (List Stmt)}
    (hsa : scopeArms rc arms s₀ s₀.retDone = .ok s₁) (hem : expectS isEmit "a match" s₁ = .ok sc')
    (h₀' : flushEdge rc sc' = .ok s₀') (hx : s₀'.live.contains x = true) :
    s₀.live.contains x = true ∨ x ∈ allocsOf (flushSeg sc'.rest) := by
  obtain ⟨-, hfl⟩ := flushEdge_ok h₀'
  obtain ⟨-, hlive, -⟩ := flushS_seg _ _ _ _ _ (show flushS rc sc'.rest sc'.live sc'.retDone = .ok s₀'
    from hfl)
  obtain ⟨_, _, _, hl, _⟩ := expectS_ok hem
  rcases hlive x hx with h | h
  · left
    rw [hl, scopeArms_live rc arms _ _ _ hsa] at h
    exact h
  · exact Or.inr h

theorem armsOps_in : ∀ (bs : List (List PStmt)) (q j : ℕ) (hj : j < bs.length),
    OpsIn I q (armsOps bs q) →
    OpsIn I (q + armsSize (bs.take j)) (blockOps bs[j] (q + armsSize (bs.take j)))
  | [], _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | b :: bs, q, 0, _, h => by simpa [armsOps, armsSize] using h.left
  | b :: bs, q, j + 1, hj, h => by
    have h' := h.right
    rw [blockOps_length] at h'
    have := armsOps_in bs (q + blockSize b) j (by simpa using hj) h'
    simpa [armsSize, List.take_succ_cons, Nat.add_assoc] using this

theorem armsFills_blk (f : String) (first : ℕ) {y : Fill} :
    ∀ (bs : List (List PStmt)) (j₀ q i : ℕ) (hi : i < bs.length),
    y ∈ blockFills f bs[i] (q + armsSize (bs.take i)) → y ∈ armsFills f first bs j₀ q
  | [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | b :: bs, j₀, q, 0, _, h => by
    simp only [armsFills, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl (by simpa [armsSize] using h))
  | b :: bs, j₀, q, i + 1, hi, h => by
    simp only [armsFills, List.mem_cons, List.mem_append]
    refine Or.inr (Or.inr (armsFills_blk f first bs (j₀ + 1) (q + blockSize b) i
      (by simpa using hi) ?_))
    simpa [armsSize, List.take_succ_cons, Nat.add_assoc] using h

end Pieces

/-! ## The head of a chain whose arms jump to the join -/

section Head

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Backend.Ctx} {I : Inst}

theorem fills_arm {h : List LHint} {join lx entry one sfp first pos j : ℕ}
    {bs : List (List PStmt)} (hF : FillsIn Γ Ag pos [PStmt.chain h join lx entry one sfp [first] [bs]])
    (hj : j < bs.length) : FillsIn Γ Ag (pos + 3 + armsSize (bs.take j)) bs[j] :=
  fun f k i hm => hF f k i (by
    have := armsFills_blk f first bs 0 (pos + 3) j hj hm
    simpa [blockFills, stmtFills, stagesFills] using this)

/-- The values a `match`'s path reads: its selector and the picked arm's. -/
theorem pathVals_match {σ : Val} {x : V} {arms : List (List Stmt)} {j : ℕ} (hj : j < arms.length)
    {o : Out} (hsel : armSels σ x 0 arms = pathSels σ arms[j]) :
    ∀ v ∈ pathVals σ [.match_ x arms] o, v ∈ x :: pathVals σ arms[j] o := by
  intro v hv
  have hs : pathSels σ [Stmt.match_ x arms] = sels1 σ (.match_ x arms) := by
    simp only [pathSels]
    split <;> simp
  simp only [pathVals, hs, sels1, hsel] at hv ⊢
  simp only [List.mem_append, List.mem_cons] at hv ⊢
  tauto

/-- **The facts after a `match`'s edge flush** and the reset of the chaining flags, handed to the
placement of the `match` (`placeMatch`), with whether its arms dispatch into the next one. -/
theorem match_pre (hI : I.Ok) {x : V} {arms : List (List Stmt)} {rest : List Stmt}
    {C : (ℕ → E) → Prop} {st : St} {sc s₀ : SSt} {R : Unit → ((ℕ → E) → Prop) → St → Prop}
    {g : Unit → P Unit}
    (hinv : WInv ctx I C st sc) (h₀ : flushEdge ctx.retCells sc = .ok s₀)
    (hf : ∀ (b : Bool) (st₂ : St) (C₂ : (ℕ → E) → Prop), st.next ≤ st₂.next →
      COk I C₂ st₂.next st₂.scope st₂.locs → EmitsW I C₂ st st₂ → PK st st₂ →
      st₂.rest = s₀.rest → st₂.rest.length ≤ ctx.fuel →
      VW I C₂ st₂ (fun v => s₀.live.contains v = true) →
      (s₀.retDone = false → RetBlind ctx C₂) →
      (∀ v, st₂.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest)) →
      st₂.chainIn = none → st₂.lazy = none →
      FBAt ctx I C₂ st₂ (placeMatch x arms.length rest none b
        (fun base exit => placeArms arms 0 arms.length base exit) >>= g) R) :
    FBAt ctx I C st (placeStmt (.match_ x arms) rest >>= g) R := by
  obtain ⟨hlf, hfl₀⟩ := flushEdge_ok h₀
  have hfl : flushS ctx.retCells st.rest sc.live sc.retDone = .ok s₀ := by
    rw [← hinv.rest]; exact hfl₀
  obtain ⟨hseg, hlive, huseS⟩ := flushS_seg _ _ _ _ _ hfl
  have hsegA : ∀ v ∈ allocsOf (flushSeg st.rest), st.locs[v]? = none := fun v hv =>
    (hinv.fresh v (by rw [hseg, allocsOf_append]; exact List.mem_append_left _ hv)).1
  have hvw : VW I C st fun v => sc.live.contains v = true ∨ st.locs[v]? = none :=
    fun v l hv hl => hv.elim (fun h => hinv.vw v l h hl) fun h => by rw [h] at hl; cases hl
  have hokOf : ∀ v, s₀.live.contains v = true →
      sc.live.contains v = true ∨ st.locs[v]? = none := fun v hv =>
    (hlive v hv).elim Or.inl fun h => Or.inr (hsegA v h)
  rw [placeStmt]
  simp only [bind_assoc]
  refine FBAt.fat_bind (FAt.and_wp (flushSeg_lock ctx I C st [] sc.live sc.retDone s₀
      (fun v => sc.live.contains v = true ∨ st.locs[v]? = none) hI hfl hinv.fuel
      (fun k _ _ _ hk => by simp at hk)
      (fun v _ _ hv _ => (huseS v hv).elim Or.inl fun h => Or.inr (hsegA v h))
      hinv.abi hinv.two hvw (fun hr k hk Ψ w hC => hinv.ret hr Ψ k w hk hC))
    (wp_and flush_pk (wp_and (flushLazy [] st (hinv.rest ▸ hlf)) flush_keep)))
    fun _ st₁ C₁ _ hn₁ _ _ hE₁ ⟨⟨hr₁, hFR₁, hrb₁, hloc₁⟩, hpk₁, hz₁, hk₁⟩ => ?_
  have hvw₁ : VW I C₁ st₁ fun v => s₀.live.contains v = true :=
    hFR₁.2.anti fun v hv => Or.inl (hokOf v hv)
  have hch₁ : st₁.chainIn = none := (show st₁.chainIn = st.chainIn from hk₁).trans hinv.chain
  have hf₁ : st₁.rest.length ≤ ctx.fuel := by
    have h1 := hinv.fuel
    have h2 := congrArg List.length hseg
    rw [List.length_append] at h2
    rw [hr₁]
    omega
  refine FBAt.get_bind ?_
  rw [hch₁]
  refine FBAt.fat_bind (FAt.ofSame (R := fun _ C' st' => C' = C₁ ∧
      st' = { st₁ with chainIn := none, chain := false })
    (wp_set.mpr ⟨rfl, rfl, rfl, LocsLe.refl _, rfl, rfl⟩))
    fun _ st₂ C₂ _ hn₂ hl₂ hc₂ hE₂ ⟨hC₂, hst₂⟩ => ?_
  subst hC₂ hst₂
  exact hf st₁.chain _ _ hn₁ hc₂ (hE₁.step hE₂ (Stronger.refl _) hn₂ hl₂)
    (hpk₁.trans (pk_same rfl rfl rfl)) hr₁ hf₁ hvw₁ hrb₁ hloc₁ rfl (by rw [hz₁]; exact hinv.lazy)

theorem FBAt.fat_bind2 {α β γ : Type} {C : (ℕ → E) → Prop} {st : St} {m : P α} {f : α → P β}
    {g : β → P γ} {R₁ : α → ((ℕ → E) → Prop) → St → Prop} {R₂ : γ → ((ℕ → E) → Prop) → St → Prop}
    (hm : FAt ctx I C st m R₁)
    (hf : ∀ a st₁ C₁, Stronger C₁ C → st.next ≤ st₁.next → LocsLe st.locs st₁.locs →
      COk I C₁ st₁.next st₁.scope st₁.locs → EmitsW I C₁ st st₁ → R₁ a C₁ st₁ →
      FBAt ctx I C₁ st₁ (f a >>= g) R₂) :
    FBAt ctx I C st ((m >>= f) >>= g) R₂ := by
  rw [bind_assoc]
  exact FBAt.fat_bind hm hf

theorem wp_eq {α : Type} {m : P α} {st : St} :
    wpP m ctx st fun a st' => m ctx st = .ok (a, st') := fun _ _ h => h

/-- **A stage's arms**, the picked one on the path when the instructions so far are final (the
invariant at their start then), all of them off it otherwise. -/
theorem arms_fb (we : E) {arms : List (List Stmt)} {jp : ℕ} {exit : ArmExit}
    {C : (ℕ → E) → Prop} {st : St} {s s' : SSt} {q i₀ : ℕ} {o : Out}
    (hj : jp < arms.length) (hin : InBlockW Γ Ag cl ctx I arms[jp])
    (hsc : scopeArms ctx.retCells arms s s.retDone = .ok s')
    (hr : st.rest = s.rest) (hf : st.rest.length ≤ ctx.fuel)
    (hinv : OutOps I st → WInv ctx I C st s)
    (hw : walk I.σ arms[jp] = o) (hns : o ≠ .stuck) (hes : ∀ e ∈ outEs o, e ∈ I.es)
    (hcl : ∀ k < (calls (outEs o)).length, cl[i₀ + k]? = (calls (outEs o))[k]?)
    (hfa : ∀ v ∈ pathVals I.σ arms[jp] o, ∀ run,
      Atom.frameAddr v run ∉ armsAtoms (arms.drop (jp + 1))) :
    FBAt ctx I C st (placeArms arms 0 arms.length st.next exit) fun bs C' st' =>
      COk I C' st'.next st'.scope st'.locs ∧ bs.length = arms.length ∧ st'.rest = s'.rest ∧
      st'.scope = st.scope ∧ st'.out = st.out ∧ (st.chainIn = none → st'.chainIn = none) ∧
      OffNew st st' (armsAtoms arms) ∧ (∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st.rest) ∧
      (∀ x ∈ st.tables.shared, x ∈ st'.tables.shared) ∧
      (OutOps I st → ∃ blk leave, bs[jp]? = some (blk ++ leave) ∧
        LeaveOK exit jp arms.length leave C' we st.next st'.next ∧
        (∀ es, o = .fall es → Fits I st' →
          OpsIn I (q + armsSize (bs.take jp)) (blockOps blk (q + armsSize (bs.take jp))) →
          TabsW Γ Ag st' → FillsIn Γ Ag (q + armsSize (bs.take jp)) blk → WInv ctx I C' st' s') ∧
        (Fits I st' →
          OpsIn I (q + armsSize (bs.take jp)) (blockOps blk (q + armsSize (bs.take jp))) →
          TabsW Γ Ag st' → FillsIn Γ Ag (q + armsSize (bs.take jp)) blk →
          BlkW Γ I ctx Ag cl C' blk arms[jp] [] o i₀ (q + armsSize (bs.take jp)) ∧
            RW I C' st' (pathVals I.σ arms[jp] o))) ∧
      (¬ OutOps I st → C' = C) := by
  intro hc a st' he
  obtain ⟨hb, hr₃, hs₃, ho₃, hc₃, hn₃, hl₃, -, -, hz, hsub, ht⟩ :=
    placeArms_off (n := arms.length) (base := st.next) (exit := exit) arms 0 st s s.retDone s'
      hsc hr hf a st' he
  have hcok : ∀ C', Stronger C' C → (∃ Ψ, C' Ψ) → Blind C' st'.next →
      COk I C' st'.next st'.scope st'.locs := fun C' hs h0 hbl =>
    ⟨h0, hbl, fun Ψ hΨ => by rw [hs₃]; exact (hc.pools Ψ (hs Ψ hΨ)).grow hl₃,
      by rw [hs₃]; exact hc.cells.mono hn₃⟩
  by_cases hO : OutOps I st
  · have hfl : ∀ v run, s.live.contains v = true → Atom.frameAddr v run ∉ armsAtoms arms :=
      fun v run hv hm => by
        have := scopeArms_fa _ arms s _ s' hsc v run hm
        rw [hv] at this
        cases this
    obtain ⟨C', hst', hsat', hb', hn', hl', -, -, -, -, -, -, blk, leave, hbs, hlv, hW, hB⟩ :=
      placeArms_pick (n := arms.length) (base := st.next) (exit := exit) we arms jp 0 st s
        s.retDone s' q i₀ o C hj hin hsc (hinv hO) hfl hw hns hes hcl hfa a st' he
    rw [Nat.zero_add] at hlv
    exact ⟨C', hsat', hb', hst', hn', hl', hcok C' hst' hsat' hb', hb, hr₃, hs₃, ho₃, hc₃, hz,
      hsub, ht, fun _ => ⟨blk, leave, hbs, hlv, hW, hB⟩, fun h => absurd hO h⟩
  · exact ⟨C, hc.sat, hc.blind.mono hn₃, Stronger.refl _, hn₃, hl₃,
      hcok C (Stronger.refl _) hc.sat (hc.blind.mono hn₃), hb, hr₃, hs₃, ho₃, hc₃, hz, hsub, ht,
      fun h => absurd h hO, fun _ => rfl⟩

/-- A one-stage chain's instructions: the join's `SET`, the `SLOT`, the `JUMP`, the arms, all in
the final placement. -/
theorem opsIn_chain1 {h : List LHint} {join lx entry one sfp first pos : ℕ}
    {bs : List (List PStmt)}
    (hO : OpsIn I pos (stmtOps (.chain h join lx entry one sfp [first] [bs]) pos)) :
    I.ops[pos]? = some (.set join (.local (pos + 3 + armsSize bs))) ∧
      LOp.slot lx first entry ∈ I.ops ∧ LOp.jump one entry sfp ∈ I.ops ∧
      OpsIn I (pos + 3) (armsOps bs (pos + 3)) ∧ pos + 3 + armsSize bs ≤ I.ops.length := by
  simp only [stmtOps, stagesOps, stagesSize, List.append_nil, Nat.add_zero, List.headD_cons]
    at hO
  have hR := hO.right
  simp only [List.length_cons, List.length_nil] at hR
  have hlen := hO (2 + armsSize bs) (by simp [armsOps_length]; omega)
  refine ⟨by simpa using hO 0 (by simp), hO.mem _ (by simp), hO.mem _ (by simp), by simpa using hR,
    ?_⟩
  have := (List.getElem?_eq_some_iff.mp hlen).1
  omega

theorem winv_out {C : (ℕ → E) → Prop} {st : St} {s : SSt} (h : WInv ctx I C st s)
    (out : Rev PStmt) : WInv ctx I C { st with out := out } s :=
  ⟨h.cok, h.rest, h.vw, h.two, h.abi, h.fuel, h.ret, h.nodup, h.fresh, h.chain, h.pnt, h.lazy⟩

set_option maxHeartbeats 4000000 in
/-- **The head of a chain whose arms jump to the join** (an unchained `match`), from the state
after its edge flush: its cells, the picked arm on the path, the others off it, the `emit` and
the chain node; a statement's outcome (`BlockOut`). -/
theorem head_join (hok : OpOK Γ I Ag cl) (hI : I.Ok) (hmain : ctx.isMain = true → I.fp = 0)
    (hAg : AgOwn I Ag) (hkw : ∀ k, I.kw k = kwOf Γ k)
    (hlocB : ∀ q, q ≤ I.ops.length → kwOf Γ (.local q) = Γ.tgt q)
    {x : V} {arms : List (List Stmt)} {rest tl : List Stmt} (hu : x ∉ I.tmps)
    (hin : ∀ j (hj : j < arms.length), InBlockW Γ Ag cl ctx I arms[j])
    (hafa : ∀ j (hj : j < arms.length), ∀ v ∈ pathVals I.σ arms[j] (walk I.σ arms[j]), ∀ run,
      Atom.frameAddr v run ∉ armsAtoms (arms.drop (j + 1)))
    {C C₂ : (ℕ → E) → Prop} {st st₂ : St} {sc s₀ s₁ sc' : SSt} {i₀ p₀ : ℕ} {o : Out}
    (hinv : WInv ctx I C st sc) (h₀ : flushEdge ctx.retCells sc = .ok s₀)
    (hx : s₀.live.contains x = true) (hsa : scopeArms ctx.retCells arms s₀ s₀.retDone = .ok s₁)
    (hem : expectS isEmit "a match" s₁ = .ok sc')
    (hw : walk1 I.σ (.match_ x arms) = o) (hns : o ≠ .stuck) (hes : ∀ e ∈ outEs o, e ∈ I.es)
    (hcl : ∀ k < (calls (outEs o)).length, cl[i₀ + k]? = (calls (outEs o))[k]?)
    (hn₂ : st.next ≤ st₂.next) (hE₂ : EmitsW I C₂ st st₂) (hpk₂ : PK st st₂)
    (hr₂ : st₂.rest = s₀.rest) (hf₂ : st₂.rest.length ≤ ctx.fuel)
    (hvw₂ : VW I C₂ st₂ (fun v => s₀.live.contains v = true))
    (hrb₂ : s₀.retDone = false → RetBlind ctx C₂)
    (hloc₂ : ∀ v, st₂.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest))
    (hch₂ : st₂.chainIn = none) (hz₂ : st₂.lazy = none) :
    FBAt ctx I C₂ st₂ (placeMatch x arms.length rest none false
      (fun base exit => placeArms arms 0 arms.length base exit) >>= fun _ => endStmt)
      fun _ C' st' => BlockOut Γ Ag cl ctx I st sc' [.match_ x arms] (rest ++ tl) o i₀ p₀ C' st' := by
  have hns' : walkArms I.σ x 0 arms ≠ .stuck := fun h => hns (by rw [← hw, walk1, h])
  obtain ⟨j, hj, hxj, hne, hwj, hsel⟩ := walkArms_pick arms 0 hns'
  simp only [Nat.zero_add] at hxj hne
  have hwo : walk I.σ arms[j] = o := by rw [← hwj, ← hw, walk1]
  unfold placeMatch
  rw [bind_assoc]
  refine FBAt.fat_bind (FAt.and_wp (matchCells_fatB hI hmain hvw₂ hx (le_trans hinv.two hn₂))
    (wp_and matchCells_pk (wp_and matchCells_lz (wp_and matchCells_keep matchCells_placed))))
    fun r st₃ C₃ hs₃ hn₃ hl₃ _ hE₃ ⟨⟨hnone, hx2, hxlt, hxw, hf2, hflt, hfw, ho2, holt, how,
      hlo₃, hr₃, hkb₃⟩, hpk₃, hz₃, hk₃, hpl₃⟩ => ?_
  obtain ⟨lx, ns, sfp, one⟩ := r
  simp only at hnone hx2 hxlt hxw hf2 hflt hfw ho2 holt how
  subst hnone
  dsimp only
  simp only [bind_assoc, pure_bind]
  have hxS : ∀ σ', I.Same σ' → σ' x = I.σ x := fun σ' h => h x hu
  refine FBAt.fat_bind (fresh_fat (fun _ => joinW I (p₀ + blockSize st₃.out.toList))
    (wblind_const _ _)) fun join st₄ C₄ _ _ _ _ hE₄ ⟨hjn, hst₄, hC₄⟩ => ?_
  subst hjn hst₄ hC₄
  refine FBAt.fat_bind takeHints_fat fun hints st₅ C₅ _ _ _ _ hE₅ ⟨hC₅, hst₅⟩ => ?_
  subst hC₅ hst₅
  refine FBAt.fat_bind (FAt.ofSame (R := fun a C' st' => a = st₃.tables.len ∧ C' = _ ∧
      st' = { st₃ with next := st₃.next + 1, tables.len := st₃.tables.len + arms.length, pending := #[] })
    (wp_modifyGet.mpr ⟨rfl, rfl, rfl, LocsLe.refl _, rfl, rfl, rfl⟩))
    fun first st₆ C₆ _ _ _ _ hE₆ ⟨hfst, hC₆, hst₆⟩ => ?_
  subst hfst hC₆ hst₆
  refine FBAt.fat_bind (fresh_fat (fun _ => entryW Γ ctx arms (.join st₃.next one sfp) j
      (p₀ + blockSize st₃.out.toList)
      { st₃ with next := st₃.next + 2, tables.len := st₃.tables.len + arms.length, pending := #[] })
    (wblind_const _ _)) fun entry S C₇ _ _ _ hc₇ hE₇ ⟨hen, hS, hC₇⟩ => ?_
  subst hen
  set n := st₃.next with hn
  set pos := p₀ + blockSize st₃.out.toList with hpos
  have hSn : S.next = n + 2 := by rw [hS]
  have hSl : S.locs = st₂.locs := by rw [hS]; exact hlo₃
  have hSr : S.rest = s₀.rest := by rw [hS]; exact hr₃.trans hr₂
  have hSo : S.out = st₃.out := by rw [hS]
  have hSc : S.chainIn = none := by rw [hS]; exact (show st₃.chainIn = st₂.chainIn from hk₃).trans hch₂
  have hSz : S.lazy = none := by rw [hS]; exact hz₃.1.trans hz₂
  have hSt : S.tables.shared = st₃.tables.shared := by rw [hS]
  have hC7 : ∀ Ψ, C₇ Ψ → C₃ Ψ ∧ Ψ n = joinW I pos ∧ Ψ (n + 1) = entryW Γ ctx arms
      (.join n one sfp) j pos
      { st₃ with next := st₃.next + 2, tables.len := st₃.tables.len + arms.length, pending := #[] } := by
    subst hC₇; exact fun Ψ h => ⟨h.1.1, h.1.2, h.2⟩
  have hkb₇ : KeepB C₂ C₇ st₂.next := by
    subst hC₇
    intro c hc hb
    have hcn : c < n := lt_of_lt_of_le hc hn₃
    exact blindAt_assign (blindAt_assign (hkb₃ c hc hb) (Nat.ne_of_lt hcn))
      (Nat.ne_of_lt (Nat.lt_succ_of_lt hcn))
  have hs₇ : Stronger C₇ C₂ := fun Ψ h => hs₃ Ψ (hC7 Ψ h).1
  have hn₂S : st₂.next ≤ S.next := by rw [hSn]; exact le_trans hn₃ (Nat.le_add_right _ _)
  have hpkS : PK st S := hpk₂.trans (hpk₃.trans (pk_same (by rw [hS]) (by rw [hS]) (by rw [hS])))
  have hinvS : OutOps I S → WInv ctx I C₇ S s₀ := fun hO =>
    winv_edge hinv h₀ hc₇ (le_trans hn₂ hn₂S) hSr (hvw₂.step hs₇ hn₂S hSl)
      (fun hr => RetBlind.keep (hrb₂ hr) (le_trans hinv.abi hn₂) hkb₇)
      (fun v hv => hloc₂ v (by rwa [hSl] at hv)) hSc
      ⟨fun k o' hk => (hpkS.2.1 k o' hk).nt hI hinv.pnt hO,
        fun c' l hc' p hp => (hpkS.2.2 c' l hc' p hp).nt hI hinv.pnt hO⟩ hSz
  have hfS : S.rest.length ≤ ctx.fuel := by rw [hSr, ← hr₂]; exact hf₂
  refine FBAt.get_bind ?_
  refine FBAt.bind (FBAt.and_wp (arms_fb (q := pos + 3) (i₀ := i₀) (exit := .join n one sfp) 0 hj
    (hin j hj) hsa (hSr) hfS hinvS hwo hns hes hcl (hwo ▸ hafa j hj)) wp_eq)
    (fun _ _ _ h => h.1.1) ?_
  rintro bs st₈ C₈ hs₈ hn₈ hl₈ ⟨⟨-, hlen, hr₈, -, ho₈, hch₈, -, hsub₈, ht₈, hpick, -⟩, heq⟩
  obtain ⟨ev, hev, heS, -, -⟩ := expectS_ok hem
  refine FBAt.mono (stageEnd_fbat (hr₈.trans hev) heS) ?_
  rintro _ C' st' - - - ⟨rfl, hst'⟩
  have hjb : j < bs.length := hlen ▸ hj
  have hout' : st'.out.toList =
      st₈.out.toList ++ [PStmt.chain hints n lx (n + 1) one sfp [st₃.tables.len] [bs]] := by
    rw [hst']; simp
  have hn' : st'.next = st₈.next := by rw [hst']
  have hl' : st'.locs = st₈.locs := by rw [hst']
  have ht' : st'.tables = st₈.tables := by rw [hst']
  have hr' : st'.rest = sc'.rest := by rw [hst']
  have hc' : st'.chainIn = st₈.chainIn := by rw [hst']
  have ho₈' : st₈.out.toList = st₃.out.toList := by rw [ho₈, hSo]
  have hfin : FinAt Γ I Ag p₀ st' →
      OutOps I S ∧ Fits I st₈ ∧ TabsW Γ Ag st₈ ∧
      OpsIn I pos (stmtOps (PStmt.chain hints n lx (n + 1) one sfp [st₃.tables.len] [bs]) pos) ∧
      FillsIn Γ Ag pos [PStmt.chain hints n lx (n + 1) one sfp [st₃.tables.len] [bs]] := by
    intro hF
    obtain ⟨h1, h2, h3, h4⟩ := fin_ite (stb := st₈) hF hout' (by rw [hn']) (by rw [hl']; exact LocsLe.refl _)
      fun _ h => by rw [ht']; exact h
    rw [ho₈'] at h3 h4
    refine ⟨fun hh o' hm => hF.2.1.outOps hh o' ?_, h1, h2, h3, h4⟩
    rw [hout', ho₈']
    rw [hSo] at hm
    exact List.mem_append_left _ hm
  refine ⟨fun es hes' hF => ?_, hc'.trans (hch₈ hSc), fun hF => ?_⟩
  · obtain ⟨hO, hFt, hT, hOp, hFl⟩ := hfin hF
    obtain ⟨blk, leave, hbs, -, hW, -⟩ := hpick hO
    have hbj : bs[j] = blk ++ leave := Option.some.inj ((List.getElem?_eq_getElem hjb).symm.trans hbs)
    obtain ⟨-, -, -, hAo, -⟩ := opsIn_chain1 hOp
    have hA := armsOps_in bs (pos + 3) j hjb hAo
    have hFa := fills_arm hFl hjb
    rw [hbj, bops_append] at hA
    rw [hbj] at hFa
    rw [hst']
    exact (winv_emit (hW es hes' hFt hA.left hT hFa.left) hem _).2
  · obtain ⟨hO, hFt, hT, hOp, hFl⟩ := hfin hF
    obtain ⟨blk, leave, hbs, hlv, -, hB⟩ := hpick hO
    have hbj : bs[j] = blk ++ leave :=
      Option.some.inj ((List.getElem?_eq_getElem hjb).symm.trans hbs)
    obtain ⟨hset, hslo, hjmp, hAo, hle⟩ := opsIn_chain1 hOp
    have hA := armsOps_in bs (pos + 3) j hjb hAo
    have hFa := fills_arm hFl hjb
    rw [hbj, bops_append] at hA
    rw [hbj] at hFa
    obtain ⟨hBw, hRw⟩ := hB hFt hA.left hT hFa.left
    have hbj' : bs[j] = blk ++
        (if j + 1 != bs.length then [PStmt.op [] (.jump one n sfp)] else []) := by
      rw [hbj, hlen]
      simp only [LeaveOK] at hlv
      rw [hlv]
    have hC8 := fun Ψ (h : C' Ψ) => hC7 Ψ (hs₈ Ψ h)
    have hSe : S = { st₃ with next := st₃.next + 2, tables.len := st₃.tables.len + arms.length, pending := #[] } := by
      rw [hS]
    have hn8 : n + 2 ≤ st₈.next := hSn ▸ hn₈
    obtain ⟨ops, hops, hopsW⟩ := hE₂.step hE₃ hs₃ hn₃ hl₃
    have hF₃ : Fits I st₃ := hFt.back (le_trans (Nat.le_add_right _ _) hn8)
      (fun v l h => hl₈ v l (by rw [hSl, ← hlo₃]; exact h))
    have hO₃ : OutOps I st₃ := fun h o' hm => hO h o' (by rw [hSo]; exact hm)
    refine ⟨ops ++ [PStmt.chain hints n lx (n + 1) one sfp [st₃.tables.len] [bs]],
      by rw [hout', ho₈', hops, List.append_assoc], ?_, ?_⟩
    · refine blkW_ops_X hok (fun s hs => ?_) ?_
      · obtain ⟨h, o', rfl, hw'⟩ := hopsW hF₃ hO₃ s hs
        exact ⟨h, o', rfl, fun Ψ hΨ => hw' Ψ (hC8 Ψ hΨ).1⟩
      · have hp : p₀ + blockSize st.out.toList + blockSize ops = pos := by
          rw [hpos, Nat.add_assoc, ← bsize_append, ← hops]
        rw [hp]
        refine blkW_chain1 hjb hj hbj' hxj hne hxS hBw fun _ Ψ hΨ σ' _ kh _ => ?_
        have hr : Rds (Ag σ' Ψ kh) I.fp I.size (fwd I.hdr ⟨patchT I Ψ σ', kh⟩) :=
          fun κ L hL m hm => hAg σ' Ψ kh κ L hL m hm
        obtain ⟨hc3, hjw, hew⟩ := hC8 Ψ hΨ
        have hsz : n + 2 ≤ I.size := le_trans hn8 hFt.1
        have h2n : 2 ≤ n := le_trans hx2 (Nat.le_of_lt hxlt)
        have htj : ¬ I.tc n :=
          not_tc_of hI (List.mem_of_getElem? hset) (by simp [opCells]) fun _ h => nomatch h
        have hte : ¬ I.tc (n + 1) := not_tc_of hI hslo (by simp [opCells]) fun _ h => nomatch h
        have htx : ¬ I.tc lx := not_tc_of hI hslo (by simp [opCells]) fun _ h => nomatch h
        have hto : ¬ I.tc one := not_tc_of hI hjmp (by simp [opCells]) fun _ h => nomatch h
        have hts : ¬ I.tc sfp := not_tc_of hI hjmp (by simp [opCells]) fun _ h => nomatch h
        rw [← hSe] at hew
        have hfj : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ n = kwOf Γ (.local (pos + 3 + armsSize bs)) :=
          (fwd_patchT h2n htj).trans (hjw.trans ((joinW_eq hset).trans (hkw _)))
        have hn1 : n + 1 < I.size := lt_of_lt_of_le (Nat.lt_succ_self _) hsz
        have hn0 : n < I.size := lt_trans (Nat.lt_succ_self _) hn1
        exact head_words hr hn0 (lt_trans hxlt hn0) hn1 (lt_trans holt hn0) (lt_trans hflt hn0) hfj
          (hfj.trans (hlocB _ hle)) ((fwd_patchT hx2 htx).trans ((hxw Ψ hc3).trans hxj))
          ((fwd_patchT (le_trans h2n (Nat.le_succ n)) hte).trans (hew.trans (entryW_eq heq)))
          (fun κ L hL => slot_chain1 hFl hjb σ' Ψ kh κ L hL)
          ((fwd_patchT ho2 hto).trans (how Ψ hc3)) ((fwd_patchT hf2 hts).trans (hfw Ψ hc3))
    · have hsubr : ∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st₈.rest := fun v hv => by
        rw [hr₈, hev]
        rw [hr'] at hv
        simp only [allocsOf, List.flatMap_cons, List.mem_append]
        exact Or.inr hv
      have hrw : RW I C' st' (pathVals I.σ arms[j] o) :=
        hRw.grow (Stronger.refl _) (by rw [hn']) (by rw [hl']; exact LocsLe.refl _)
          (fun v _ h => Or.inl (by rwa [hl'] at h)) hsubr
      have hxrw : RW I C' st' [x] := by
        intro v hv
        rw [List.mem_singleton] at hv
        rw [hv]
        obtain ⟨l₀, hl₀⟩ := Option.ne_none_iff_exists'.mp hpl₃
        refine ⟨fun h => ?_, fun _ l hl => ?_⟩
        · have := ((hinvS hO).fresh x (hsub₈ x (hsubr x h))).2
          rw [hx] at this
          cases this
        · have h8 : st₈.locs[x]? = some l₀ := hl₈ x l₀ (by rw [hSl]; exact hl₀)
          rw [hl', h8] at hl
          cases hl
          obtain ⟨b1, b2, b3⟩ := hvw₂ x l₀ hx hl₀
          exact ⟨b1, by rw [hn']; exact lt_of_lt_of_le b2 (le_trans hn₂S hn₈),
            fun Ψ hΨ => b3 Ψ (hs₇ Ψ (hs₈ Ψ hΨ))⟩
      exact (hxrw.append hrw).anti fun v hv => by simpa using pathVals_match hj hsel v hv

/-- **A statement, then the rest of its block**, the statement's outcome given for its own run
(`BlockW.cons` with the statement's lemma at one state). -/
theorem cons_at (hmono : PlaceMono ctx) (hnew : PlaceNew ctx) {s : Stmt} {rest tl : List Stmt}
    (hfa : FaAfter I.σ s rest) (h₂ : BlockW Γ Ag cl ctx I (placeBlock rest) rest tl)
    {C : (ℕ → E) → Prop} {st₀ st : St} {sc₁ sc'' : SSt} {i₀ p₀ : ℕ} {o : Out} {m : P Unit}
    (hsc : scopeBlock ctx.retCells rest sc₁ = .ok sc'') (hw : walk I.σ (s :: rest) = o)
    (hns : o ≠ .stuck) (hes : ∀ e ∈ outEs o, e ∈ I.es)
    (hcl : ∀ j < (calls (outEs o)).length, cl[i₀ + j]? = (calls (outEs o))[j]?)
    (h₁ : ∀ o₁, walk1 I.σ s = o₁ → o₁ ≠ .stuck → (∀ e ∈ outEs o₁, e ∈ I.es) →
      (∀ j < (calls (outEs o₁)).length, cl[i₀ + j]? = (calls (outEs o₁))[j]?) →
      FBAt ctx I C st (m >>= fun _ => endStmt) fun _ C' st' =>
        BlockOut Γ Ag cl ctx I st₀ sc₁ [s] (rest ++ tl) o₁ i₀ p₀ C' st') :
    FBAt ctx I C st ((m >>= fun _ => endStmt) >>= fun _ => placeBlock rest) fun _ C' st' =>
      BlockOut Γ Ag cl ctx I st₀ sc'' (s :: rest) tl o i₀ p₀ C' st' := by
  rw [walk] at hw
  cases ho₁ : walk1 I.σ s with
  | stuck =>
    rw [ho₁] at hw
    exact absurd hw.symm (by simpa [Out.seq] using hns)
  | ret es₁ vs =>
    rw [ho₁] at hw
    simp only [Out.seq] at hw
    subst hw
    refine FBAt.mono (FBAt.bind_dead (Q := fun st₁ _ st₂ => (st₁.chainIn = none →
        st₂.chainIn = none ∧ ∃ blk, st₂.out.toList = st₁.out.toList ++ blk) ∧
        ((st₁.lazy = none → ∀ v, st₂.locs[v]? ≠ none → st₁.locs[v]? ≠ none ∨
          v ∈ allocsOf st₁.rest ∨ ∃ run, Atom.frameAddr v run ∈ atomsIn rest) ∧
          (∀ v ∈ allocsOf st₂.rest, v ∈ allocsOf st₁.rest) ∧
          ∀ x ∈ st₁.tables.shared, x ∈ st₂.tables.shared))
      (FBAt.and_wp (h₁ _ ho₁ (by simp) hes hcl) (end_lazy _ st)) fun _ st₁ a s h =>
        let ⟨h1, h2, h3⟩ := hmono rest st₁ a s h
        ⟨h1, h2, h3, hnew rest st₁ a s h⟩) ?_
    rintro _ C' st₂ - - - ⟨_, st₁, ⟨⟨-, hc₁, hw₁⟩, hlz⟩, ⟨hq, hnw, hrr, htb⟩, hn₂, hl₂⟩
    obtain ⟨hc₂, blk₂, ho₂⟩ := hq hc₁
    refine ⟨(fun _ h => nomatch h), hc₂, fun hfin => ?_⟩
    obtain ⟨blk₁, ho₁', hb₁, hrw⟩ := hw₁ (hfin.back hn₂ hl₂ ho₂ htb)
    have hvs := placeNew_vs hfa (hnw hlz)
    rw [ho₁] at hvs
    refine ⟨blk₁ ++ blk₂, by rw [ho₂, ho₁', List.append_assoc], BlkW.append_ret hb₁, ?_⟩
    rw [pathVals_ret ho₁]
    exact hrw.grow (Stronger.refl _) hn₂ hl₂ hvs hrr
  | fall es₁ =>
    rw [ho₁] at hw
    simp only [Out.seq] at hw
    have hns₂ : walk I.σ rest ≠ .stuck := fun h => hns (by rw [← hw, h]; rfl)
    have hes' : outEs o = es₁ ++ outEs (walk I.σ rest) := by rw [← hw, outEs_pre hns₂]
    have hc' : calls (outEs o) = calls es₁ ++ calls (outEs (walk I.σ rest)) := by
      rw [hes', calls_append']
    refine FBAt.bind_if (FinAt Γ I Ag p₀)
      (Q := fun st₁ _ st₂ => (st₁.chainIn = none →
        st₂.chainIn = none ∧ ∃ blk, st₂.out.toList = st₁.out.toList ++ blk) ∧
        ∀ x ∈ st₁.tables.shared, x ∈ st₂.tables.shared)
      (h₁ _ ho₁ (by simp)
      (fun e he => hes e (by rw [hes']; exact List.mem_append_left _ he))
      (fun j hj => by
        rw [hcl j (by rw [hc', List.length_append]; simp only [outEs] at hj; omega), hc']
        simp only [outEs] at hj ⊢
        exact List.getElem?_append_left hj))
      (fun _ st₁ a s h =>
        let ⟨h1, h2, h3⟩ := hmono rest st₁ a s h
        ⟨h1, h2, h3, (hnew rest st₁ a s h).2.2⟩)
      (fun _ _ _ hr hF => (hr.1 es₁ rfl hF).cok)
      (fun _ st₁ C₁ hs₁ _ _ ⟨hw₁, _, hb₁⟩ hF => ?_)
      (fun _ C₁ st₁ _ st₂ ⟨_, hc₁, _⟩ hF hn₂ hl₂ ⟨hq, htb⟩ => by
        obtain ⟨hc₂, blk, ho⟩ := hq hc₁
        exact ⟨fun _ _ hF₂ => absurd (hF₂.back hn₂ hl₂ ho htb) hF, hc₂,
          fun hF₂ => absurd (hF₂.back hn₂ hl₂ ho htb) hF⟩)
    have hW₁ := hw₁ es₁ rfl hF
    refine FBAt.mono (FBAt.and_wp (h₂ C₁ st₁ sc₁ sc'' (i₀ + (calls es₁).length) p₀ _ hsc rfl hns₂
      (fun e he => hes e (by rw [hes']; exact List.mem_append_right _ he))
      (fun j hj => by
        rw [Nat.add_assoc, hcl _ (by rw [hc', List.length_append]; omega), hc',
          List.getElem?_append_right (by omega)]
        simp) hW₁) (hnew rest st₁)) ?_
    rintro _ C₂ st₂ hs₂ hn₂ hl₂ ⟨⟨hw₂, hc₂, hb₂⟩, hnw, hrr, htb⟩
    refine ⟨fun es he hF₂ => ?_, hc₂, fun hfin => ?_⟩
    · obtain ⟨es₂, h⟩ : ∃ es₂, walk I.σ rest = .fall es₂ := by
        cases h : walk I.σ rest with
        | fall es₂ => exact ⟨es₂, rfl⟩
        | ret es₂ vs => rw [← hw, h] at he; nomatch he
        | stuck => exact absurd h hns₂
      exact hw₂ es₂ h hF₂
    · obtain ⟨blk₂, ho₂, hb₂', hrw₂⟩ := hb₂ hfin
      obtain ⟨blk₁, ho₁', hb₁', hrw₁⟩ := hb₁ (hfin.back hn₂ hl₂ ho₂ htb)
      refine ⟨blk₁ ++ blk₂, by rw [ho₂, ho₁', List.append_assoc], ?_, ?_⟩
      · rw [← hw]
        rw [ho₁', bsize_append, ← Nat.add_assoc] at hb₂'
        exact BlkW.append_fall (hb₁'.mono hs₂) hb₂'
      · rw [← hw]
        have hvs := placeNew_vs hfa (hnw hW₁.lazy)
        rw [ho₁] at hvs
        exact ((hrw₁.grow hs₂ hn₂ hl₂ hvs hrr).append hrw₂).anti (pathVals_fall ho₁ hns₂)

/-- **A `match` whose arms dispatch into the next** (the head of a chain of two or more stages),
from the state after its edge flush, with the rest of its block: the open statement `matchW_of`
takes. -/
def ChainHeadW (Good : List Stmt → Prop) : Prop :=
  ∀ x arms rest tl, Good (.match_ x arms :: rest) →
    BlockIH Γ Ag cl ctx I Good (.match_ x arms :: rest) →
  ∀ (C C₂ : (ℕ → E) → Prop) (st st₂ : St) (sc s₀ s₁ sc' sc'' : SSt) (i₀ p₀ : ℕ) (o : Out),
    WInv ctx I C st sc → flushEdge ctx.retCells sc = .ok s₀ → s₀.live.contains x = true →
    scopeArms ctx.retCells arms s₀ s₀.retDone = .ok s₁ → expectS isEmit "a match" s₁ = .ok sc' →
    scopeBlock ctx.retCells rest sc' = .ok sc'' →
    walk I.σ (.match_ x arms :: rest) = o → o ≠ .stuck → (∀ e ∈ outEs o, e ∈ I.es) →
    (∀ k < (calls (outEs o)).length, cl[i₀ + k]? = (calls (outEs o))[k]?) →
    st.next ≤ st₂.next → COk I C₂ st₂.next st₂.scope st₂.locs → EmitsW I C₂ st st₂ →
    PK st st₂ → st₂.rest = s₀.rest → st₂.rest.length ≤ ctx.fuel →
    VW I C₂ st₂ (fun v => s₀.live.contains v = true) →
    (s₀.retDone = false → RetBlind ctx C₂) →
    (∀ v, st₂.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest)) →
    st₂.chainIn = none → st₂.lazy = none →
    FBAt ctx I C₂ st₂ (placeMatch x arms.length rest none true
        (fun base exit => placeArms arms 0 arms.length base exit) >>= fun _ =>
          endStmt >>= fun _ => placeBlock rest)
      fun _ C' st' => BlockOut Γ Ag cl ctx I st sc'' (.match_ x arms :: rest) tl o i₀ p₀ C' st'

theorem sizeOf_arm_lt {x : V} {arms : List (List Stmt)} {rest a : List Stmt} (h : a ∈ arms) :
    sizeOf a < sizeOf (Stmt.match_ x arms :: rest) := by
  have := List.sizeOf_lt_of_mem h
  simp only [List.cons.sizeOf_spec, Stmt.match_.sizeOf_spec]
  omega

/-- **A `match` on the path** (`MatchW`): an unchained one by `head_join` and the block lemma of
the rest (`cons_at`), a chained one by `ChainHeadW`. -/
theorem matchW_of {Good : List Stmt → Prop} (hmono : PlaceMono ctx) (hnew : PlaceNew ctx)
    (hok : OpOK Γ I Ag cl) (hI : I.Ok) (hmain : ctx.isMain = true → I.fp = 0)
    (hAg : AgOwn I Ag) (hkw : ∀ k, I.kw k = kwOf Γ k)
    (hlocB : ∀ q, q ≤ I.ops.length → kwOf Γ (.local q) = Γ.tgt q)
    (hsub : ∀ x arms rest, Good (.match_ x arms :: rest) → (∀ a ∈ arms, Good a) ∧ Good rest)
    (hfa : ∀ s rest, Good (s :: rest) → FaAfter I.σ s rest)
    (hu : ∀ x arms rest, Good (.match_ x arms :: rest) → x ∉ I.tmps)
    (hafa : ∀ x arms rest, Good (.match_ x arms :: rest) → ∀ j (hj : j < arms.length),
      ∀ v ∈ pathVals I.σ arms[j] (walk I.σ arms[j]), ∀ run,
        Atom.frameAddr v run ∉ armsAtoms (arms.drop (j + 1)))
    (hin : InBlockOf Γ Ag cl ctx I) (hch : ChainHeadW (Γ := Γ) (Ag := Ag) (cl := cl) (ctx := ctx) (I := I) Good) :
    MatchW Γ Ag cl ctx I Good := by
  intro x arms rest tl hg ih C st sc sc'' i₀ p₀ o hsc hw hns hes hcl hinv
  rw [scopeBlock] at hsc
  split at hsc
  · cases hsc
  next sc' hsc₁ =>
  obtain ⟨s₀, s₁, h₀, hx, hsa, hem⟩ := scopeMatch_inv hsc₁
  obtain ⟨harms, hrest⟩ := hsub x arms rest hg
  have hin' : ∀ j (hj : j < arms.length), InBlockW Γ Ag cl ctx I arms[j] := fun j hj =>
    hin _ fun tl' => ih _ (harms _ (List.getElem_mem hj)) (sizeOf_arm_lt (List.getElem_mem hj)) tl'
  rw [placeBlock]
  refine match_pre hI hinv h₀ fun b st₂ C₂ hn₂ hc₂ hE₂ hpk₂ hr₂ hf₂ hvw₂ hrb₂ hloc₂ hch₂ hz₂ => ?_
  cases b
  · have := cons_at (m := placeMatch x arms.length rest none false
        (fun base exit => placeArms arms 0 arms.length base exit)) (st₀ := st) (p₀ := p₀) hmono hnew (hfa _ _ hg)
      (ih rest hrest (by simp) tl) hsc hw hns hes hcl fun o₁ ho₁ hns₁ hes₁ hcl₁ =>
        head_join hok hI hmain hAg hkw hlocB (hu x arms rest hg) hin' (hafa x arms rest hg) hinv h₀
          hx hsa hem ho₁ hns₁ hes₁ hcl₁ hn₂ hE₂ hpk₂ hr₂ hf₂ hvw₂ hrb₂ hloc₂ hch₂ hz₂
    rwa [bind_assoc] at this
  · exact hch x arms rest tl hg ih C C₂ st st₂ sc s₀ s₁ sc' sc'' i₀ p₀ o hinv h₀ hx hsa hem hsc hw
      hns hes hcl hn₂ hc₂ hE₂ hpk₂ hr₂ hf₂ hvw₂ hrb₂ hloc₂ hch₂ hz₂

/-! ## Chains: the statement for a block entered by an open chain -/

/-- **The words of the stages a block adds to an open chain**, then the block after the chain:
`stagesN` from the absolute position `q`, the first stage entered at its arm `T`, the block `blk`
placed after the chain node, for the core statements `ss` (the stages' `match`es, then the rest)
followed by `tl`, with path `o` and calls from `i₀`. -/
def StagesW (C : (ℕ → E) → Prop) (stagesN : List (List (List PStmt))) (blk : List PStmt)
    (ss tl : List Stmt) (o : Out) (i₀ q T : ℕ) : Prop :=
  ∃ hs : List (E × E), hs.length = (calls (outEs o)).length ∧ HsOk I ctx (calls (outEs o)) hs ∧
  (PremW I ctx → KLast I o i₀ → ∀ Ψ, C Ψ → ∀ σ', I.Same σ' → ∀ (kh : ℕ → E × E)
    (ks : List (ℕ × ℕ)) (next : List Stmt → List (ℕ × ℕ) → Prop)
    (kj : List (ℕ × ℕ) → E → E → Prop) (kret khalt : Prop),
    (∀ o' ∈ stagesOps stagesN q ++ blockOps blk (q + stagesSize stagesN), o' ∈ I.ops) →
    KsAt cl I.kf kh i₀ (calls (outEs o)) hs ks →
    OutK o tl next (if ctx.isMain then khalt else kret) ks →
    wStages Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl stagesN (ss.take stagesN.length) q
      (fun ks' => wLc Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl blk
        (ss.drop stagesN.length ++ tl) (q + stagesSize stagesN) ks' next kj kret khalt)
      kret khalt ks (Γ.tgt T) (ofK (addressOfIndex I.fp)))

/-- **What placing a block entered by an open chain gives**: the chain node (at index
`O.length` of the output, its stages so far `stages` and their tables `firsts`) extended by the
stages `stagesN` the block's leading `match`es make (the first in the table `first`), the block
`blk` after it; no `match` chaining out; once the final placement extends the final state, the
invariant if the path falls through, the first new stage's picked arm `j` (the first with
`σ x = g^j`) and its absolute position `T`, which the slot `first + j` holds, the stages' and the
rest's words (`StagesW`) and the words of the values the path read. -/
def OpenOut (O : List PStmt) (h : List LHint) (join lx entry one sfp : ℕ) (firsts : List ℕ)
    (stages : List (List (List PStmt))) (first : ℕ) (x : V) (s' : SSt) (ss tl : List Stmt) (o : Out)
    (i₀ p₀ : ℕ) (C' : (ℕ → E) → Prop) (st' : St) : Prop :=
  st'.chainIn = none ∧
  (∀ es, o = .fall es → FinAt Γ I Ag p₀ st' → WInv ctx I C' st' s') ∧
  (FinAt Γ I Ag p₀ st' → ∃ (firstsN : List ℕ) (stagesN : List (List (List PStmt)))
      (blk : List PStmt) (j T : ℕ),
    st'.out.toList = O ++ [.chain h join lx entry one sfp (firsts ++ firstsN) (stages ++ stagesN)] ++
      blk ∧
    firstsN.head? = some first ∧ firstsN.length = stagesN.length ∧ stagesN ≠ [] ∧
    stagesN.length ≤ ss.length ∧
    I.σ x = ofK (addressOfIndex j) ∧ (∀ i < j, I.σ x ≠ ofK (addressOfIndex i)) ∧
    T = p₀ + blockSize O + 3 + stagesSize stages + armsSize ((stagesN.headD []).take j) ∧
    (∀ σ' Ψ kh κ (L : MemoryImage κ), Ag σ' Ψ kh κ L →
      L.read (addressOfIndex (Γ.l.tablesBase + (first + j))) = some (Γ.tgt T)) ∧
    StagesW (Γ := Γ) (Ag := Ag) (cl := cl) (ctx := ctx) (I := I) C' stagesN blk ss tl o i₀
      (p₀ + blockSize O + 3 + stagesSize stages) T ∧
    RW I C' st' (pathVals I.σ ss o))

/-- **A block entered by an open chain** (its first statement a `match` the `match` before it
dispatches into: `chainIn = some (first, join)`, the output ending in the chain node so far),
given the block lemma for the smaller good blocks: `OpenOut`. With the head stage whose arms
dispatch into the next (`placeMatch … none true`), it gives `ChainHeadW`. -/
def OpenW (Good : List Stmt → Prop) : Prop :=
  ∀ x arms rest tl, Good (.match_ x arms :: rest) →
    BlockIH Γ Ag cl ctx I Good (.match_ x arms :: rest) →
  ∀ (C : (ℕ → E) → Prop) (st : St) (sc sc'' : SSt) (i₀ p₀ : ℕ) (o : Out) (O : List PStmt)
    (h : List LHint) (join lx entry one sfp : ℕ) (firsts : List ℕ)
    (stages : List (List (List PStmt))) (first : ℕ),
    scopeBlock ctx.retCells (.match_ x arms :: rest) sc = .ok sc'' →
    walk I.σ (.match_ x arms :: rest) = o → o ≠ .stuck → (∀ e ∈ outEs o, e ∈ I.es) →
    (∀ k < (calls (outEs o)).length, cl[i₀ + k]? = (calls (outEs o))[k]?) →
    WInv ctx I C { st with chainIn := none } sc → st.chainIn = some (first, join) →
    st.out.toList = O ++ [.chain h join lx entry one sfp firsts stages] →
    firsts.length = stages.length →
    FBAt ctx I C st (placeBlock (.match_ x arms :: rest)) fun _ C' st' =>
      OpenOut (Γ := Γ) (Ag := Ag) (cl := cl) (ctx := ctx) (I := I) O h join lx entry one sfp firsts
        stages first x sc'' (.match_ x arms :: rest) tl o i₀ p₀ C' st'

end Head

end

end LeanVM.Guest.Backend.Complete
