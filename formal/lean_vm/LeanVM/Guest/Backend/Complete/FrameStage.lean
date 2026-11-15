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

/-- A chained `match` followed by no `match` fails to place. -/
theorem chained_fail {x : V} {n : ℕ} {rest : List Stmt} {e : Option (ℕ × Cell)}
    {armsAt : Cell → ArmExit → P (List (List PStmt))} {Q : Unit → St → Prop}
    (hnc : ∀ x' arms' rest', rest ≠ .match_ x' arms' :: rest') :
    wpP (placeMatch x n rest e true armsAt >>= fun _ => endStmt) ctx st Q := by
  unfold placeMatch matchCells
  simp only [ite_true, bind_assoc]
  refine wp_bind.mpr fun _ _ _ => ?_
  cases rest with
  | nil => exact wp_bind.mpr wp_failP
  | cons s r =>
    cases s <;> first
      | exact absurd rfl (hnc _ _ _)
      | exact wp_bind.mpr wp_failP

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
    (hinv : WInv ctx I C st sc) (h₀ : flushEdge ctx.retCells sc = .ok s₀)
    (hf : ∀ (b : Bool) (st₂ : St) (C₂ : (ℕ → E) → Prop), st.next ≤ st₂.next →
      COk I C₂ st₂.next st₂.scope st₂.locs → EmitsW I C₂ st st₂ → PK st st₂ →
      st₂.rest = s₀.rest → st₂.rest.length ≤ ctx.fuel →
      VW I C₂ st₂ (fun v => s₀.live.contains v = true) →
      (s₀.retDone = false → RetBlind ctx C₂) →
      (∀ v, st₂.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest)) →
      st₂.chainIn = none → st₂.lazy = none →
      FBAt ctx I C₂ st₂ (placeMatch x arms.length rest none b
        (fun base exit => placeArms arms 0 arms.length base exit) >>= fun _ => endStmt) R) :
    FBAt ctx I C st (placeStmt (.match_ x arms) rest >>= fun _ => endStmt) R := by
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

end Head

end

end LeanVM.Guest.Backend.Complete
