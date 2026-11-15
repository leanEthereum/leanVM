/-
  LeanVM.Guest.Backend.Complete.FrameChain

  The head of a chain of `match`es whose arms dispatch into the next (`ChainHeadW`), and the
  chains of a body at the walk's instance (`ChainBody`).
-/

module

public import LeanVM.Guest.Backend.Complete.FrameFa
public import LeanVM.Guest.Backend.Complete.FrameOpen

/-!
# The head of a chain

`chainHeadW_of`: a `match` whose arms dispatch into the next one (`placeMatch … none true`), from
the state after its edge flush: its cells, the picked arm on the path (its way out reading the
next stage's table, whose word is the final placement's target of the next stage's picked arm,
read off the final state), the `emit` and the chain node, then the rest of the block entered by
the open chain (`OpenW` on the path, `OpenOffW` for the final chain node's shape).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## Pieces -/

section Pieces

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Backend.Ctx} {I : Inst}

/-- The first arm a selector's word names is unique. -/
theorem pick_unique {σ : Val} {x : V} {j j' : ℕ} (h : σ x = ofK (addressOfIndex j))
    (hm : ∀ i < j, σ x ≠ ofK (addressOfIndex i)) (h' : σ x = ofK (addressOfIndex j'))
    (hm' : ∀ i < j', σ x ≠ ofK (addressOfIndex i)) : j = j' := by
  rcases lt_trichotomy j j' with hl | hl | hl
  · exact absurd h (hm' j hl)
  · exact hl
  · exact absurd h' (hm j' hl)

/-- A chain's instructions: the join's `SET`, the `SLOT`, the `JUMP`, the stages, all in the
final placement. -/
theorem opsIn_chain {h : List LHint} {join lx entry one sfp pos : ℕ} {firsts : List ℕ}
    {stages : List (List (List PStmt))}
    (hO : OpsIn I pos (stmtOps (.chain h join lx entry one sfp firsts stages) pos)) :
    I.ops[pos]? = some (.set join (.local (pos + 3 + stagesSize stages))) ∧
      LOp.slot lx (firsts.headD 0) entry ∈ I.ops ∧ LOp.jump one entry sfp ∈ I.ops ∧
      OpsIn I (pos + 3) (stagesOps stages (pos + 3)) ∧
      pos + 3 + stagesSize stages ≤ I.ops.length := by
  simp only [stmtOps] at hO
  have hR := hO.right
  simp only [List.length_cons, List.length_nil] at hR
  have hlen := hO (2 + stagesSize stages) (by simp [stagesOps_length]; omega)
  refine ⟨by simpa using hO 0 (by simp), hO.mem _ (by simp), hO.mem _ (by simp),
    by simpa using hR, ?_⟩
  have := (List.getElem?_eq_some_iff.mp hlen).1
  omega

/-- The slots a chain's first stage fills are among the chain's. -/
theorem fills_stage1 {h : List LHint} {join lx entry one sfp first pos : ℕ} {firsts : List ℕ}
    {bs : List (List PStmt)} {stages : List (List (List PStmt))}
    (hF : FillsIn Γ Ag pos [PStmt.chain h join lx entry one sfp (first :: firsts) (bs :: stages)])
    {f : String} {k i : ℕ} (hm : (k, KVal.at f i) ∈ armsFills f first bs 0 (pos + 3)) :
    ∀ σ' Ψ kh κ (L : MemoryImage κ), Ag σ' Ψ kh κ L →
      L.read (addressOfIndex (Γ.l.tablesBase + k)) = some (Γ.tgt i) :=
  hF f k i (by
    simp only [blockFills, stmtFills, stagesFills, List.headD_cons, List.append_nil]
    exact List.mem_append_left _ hm)

/-- A state the final placement extends, its output a chain node between two blocks: the node's
instructions and slots. -/
theorem fin_mid {p₀ : ℕ} {st : St} {O B : List PStmt} {X : PStmt} (hF : FinAt Γ I Ag p₀ st)
    (ho : st.out.toList = O ++ [X] ++ B) :
    OpsIn I (p₀ + blockSize O) (stmtOps X (p₀ + blockSize O)) ∧
      FillsIn Γ Ag (p₀ + blockSize O) [X] := by
  have h1 := hF.2.1
  unfold OpsAt at h1
  rw [ho, bops_append, bops_append] at h1
  have h2 := h1.left.right
  rw [blockOps_length] at h2
  have h3 : FillsIn Γ Ag p₀ (O ++ [X] ++ B) := by rw [← ho]; exact hF.2.2.2
  exact ⟨by simpa [blockOps] using h2, FillsIn.drop h3.left⟩

/-- Straight-line instructions with their words, then a block with its own. -/
theorem blkW_ops_B (hok : OpOK Γ I Ag cl) {C : (ℕ → E) → Prop} {ops B : List PStmt}
    {bx : Backend.Ctx} {ss tl : List Stmt} {o : Out} {i₀ pos : ℕ} (hB0 : B ≠ [])
    (hW : ∀ s ∈ ops, ∃ h o, s = PStmt.op h o ∧ ∀ Ψ, C Ψ → OpW I Ψ o)
    (hX : BlkW Γ I bx Ag cl C B ss tl o i₀ (pos + blockSize ops)) :
    BlkW Γ I bx Ag cl C (ops ++ B) ss tl o i₀ pos := by
  obtain ⟨hs, hl, hh, h⟩ := hX
  refine ⟨hs, hl, hh, fun hp hK Ψ hΨ σ' hσ kh cs ks next kj kret khalt hbo hcs hks hk => ?_⟩
  rw [wLc_append _ _ _ _ _ _ _ ops B hB0]
  exact wLc_ops hok hΨ hσ kh ops hW pos
    (fun o' ho => hbo o' (by rw [bops_append]; exact List.mem_append_left _ ho)) cs ks _ _ kret
    khalt (h hp hK Ψ hΨ σ' hσ kh cs ks next kj kret khalt
      (fun o' ho => hbo o' (by rw [bops_append]; exact List.mem_append_right _ ho)) hcs hks hk)

/-- **A chain's words from its stages' words** (`StagesW` from its start `pos + 3`): its head's
words, the join's `SET`, the first table read and the jump into the first stage's picked arm. -/
theorem blkW_chainS {C : (ℕ → E) → Prop} {h : List LHint} {join lx entry one sfp : ℕ}
    {firsts : List ℕ} {stages : List (List (List PStmt))} {blk : List PStmt} {x : V}
    {arms : List (List Stmt)} {rest tl : List Stmt} {o : Out} {i₀ pos T : ℕ}
    (hlen : stages.length ≤ (Stmt.match_ x arms :: rest).length)
    (hS : StagesW (Γ := Γ) (Ag := Ag) (cl := cl) (ctx := ctx) (I := I) C stages blk
      (.match_ x arms :: rest) tl o i₀ (pos + 3) T)
    (hhead : PremW I ctx → ∀ Ψ, C Ψ → ∀ σ', I.Same σ' → ∀ kh : ℕ → E × E,
      (∀ o' ∈ blockOps [PStmt.chain h join lx entry one sfp firsts stages] pos, o' ∈ I.ops) →
      HW Γ I.fp (Ag σ' Ψ kh) (Γ.pc0 + pos) (.set join (.local (pos + 3 + stagesSize stages))) ∧
      HW Γ I.fp (Ag σ' Ψ kh) (Γ.pc0 + pos + 1) (.slot lx (firsts.headD 0) entry) ∧
      JumpTo Γ I.fp I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) one entry sfp T) :
    BlkW Γ I ctx Ag cl C ([PStmt.chain h join lx entry one sfp firsts stages] ++ blk)
      (.match_ x arms :: rest) tl o i₀ pos := by
  obtain ⟨hs, hl, hh, hW⟩ := hS
  refine ⟨hs, hl, hh, fun hP hK Ψ hΨ σ' hσ kh cs ks next kj kret khalt hops hcs hks hk => ?_⟩
  have hpX : pos + blockSize [PStmt.chain h join lx entry one sfp firsts stages] =
      pos + 3 + stagesSize stages := by simp [blockSize, stmtSize]; omega
  have hops₀ : ∀ o' ∈ blockOps [PStmt.chain h join lx entry one sfp firsts stages] pos,
      o' ∈ I.ops := fun o' ho => hops o' (by rw [bops_append]; exact List.mem_append_left _ ho)
  have hopsS : ∀ o' ∈ stagesOps stages (pos + 3) ++ blockOps blk (pos + 3 + stagesSize stages),
      o' ∈ I.ops := fun o' ho => hops o' (by
    rw [bops_append, hpX]
    rcases List.mem_append.mp ho with h' | h'
    · refine List.mem_append_left _ ?_
      simp only [blockOps, stmtOps, List.append_nil, List.mem_append]
      exact Or.inr h'
    · exact List.mem_append_right _ h')
  obtain ⟨hset, hslot, hhd⟩ := hhead hP Ψ hΨ σ' hσ kh hops₀
  have hcs' : ctrlSplit cs = some (.match_ x arms, rest ++ tl) := by rw [hcs]; rfl
  have := hW hP hK Ψ hΨ σ' hσ kh ks next kj kret khalt hopsS hks hk
  rw [List.singleton_append]
  simp only [wLc]
  refine wS_chain hcs' hset hslot hhd ?_
  rw [← List.cons_append, List.take_append_of_le_length hlen,
    List.drop_append_of_le_length hlen]
  have hpX' : pos + stmtSize (PStmt.chain h join lx entry one sfp firsts stages) =
      pos + 3 + stagesSize stages := by simp [stmtSize]; omega
  rw [hpX']
  exact this

/-- `blkW_chainS` for a path that returns in the chain: the stages' words for the core statements
up to the end of the trace (`tl` in them), nothing after. -/
theorem blkW_chainS_ret {C : (ℕ → E) → Prop} {h : List LHint} {join lx entry one sfp : ℕ}
    {firsts : List ℕ} {stages : List (List (List PStmt))} {blk : List PStmt} {x : V}
    {arms : List (List Stmt)} {rest tl : List Stmt} {es : List Ev} {vs : List V} {i₀ pos T : ℕ}
    (hS : StagesW (Γ := Γ) (Ag := Ag) (cl := cl) (ctx := ctx) (I := I) C stages blk
      (.match_ x arms :: (rest ++ tl)) [] (.ret es vs) i₀ (pos + 3) T)
    (hhead : PremW I ctx → ∀ Ψ, C Ψ → ∀ σ', I.Same σ' → ∀ kh : ℕ → E × E,
      (∀ o' ∈ blockOps [PStmt.chain h join lx entry one sfp firsts stages] pos, o' ∈ I.ops) →
      HW Γ I.fp (Ag σ' Ψ kh) (Γ.pc0 + pos) (.set join (.local (pos + 3 + stagesSize stages))) ∧
      HW Γ I.fp (Ag σ' Ψ kh) (Γ.pc0 + pos + 1) (.slot lx (firsts.headD 0) entry) ∧
      JumpTo Γ I.fp I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) one entry sfp T) :
    BlkW Γ I ctx Ag cl C ([PStmt.chain h join lx entry one sfp firsts stages] ++ blk)
      (.match_ x arms :: rest) tl (.ret es vs) i₀ pos := by
  obtain ⟨hs, hl, hh, hW⟩ := hS
  refine ⟨hs, hl, hh, fun hP hK Ψ hΨ σ' hσ kh cs ks next kj kret khalt hops hcs hks hk => ?_⟩
  have hpX : pos + blockSize [PStmt.chain h join lx entry one sfp firsts stages] =
      pos + 3 + stagesSize stages := by simp [blockSize, stmtSize]; omega
  have hops₀ : ∀ o' ∈ blockOps [PStmt.chain h join lx entry one sfp firsts stages] pos,
      o' ∈ I.ops := fun o' ho => hops o' (by rw [bops_append]; exact List.mem_append_left _ ho)
  have hopsS : ∀ o' ∈ stagesOps stages (pos + 3) ++ blockOps blk (pos + 3 + stagesSize stages),
      o' ∈ I.ops := fun o' ho => hops o' (by
    rw [bops_append, hpX]
    rcases List.mem_append.mp ho with h' | h'
    · refine List.mem_append_left _ ?_
      simp only [blockOps, stmtOps, List.append_nil, List.mem_append]
      exact Or.inr h'
    · exact List.mem_append_right _ h')
  obtain ⟨hset, hslot, hhd⟩ := hhead hP Ψ hΨ σ' hσ kh hops₀
  have hcs' : ctrlSplit cs = some (.match_ x arms, rest ++ tl) := by rw [hcs]; rfl
  have := hW hP hK Ψ hΨ σ' hσ kh ks next kj kret khalt hopsS hks hk
  rw [List.singleton_append]
  simp only [wLc]
  refine wS_chain hcs' hset hslot hhd ?_
  have hpX' : pos + stmtSize (PStmt.chain h join lx entry one sfp firsts stages) =
      pos + 3 + stagesSize stages := by simp [stmtSize]; omega
  rw [hpX']
  simpa using this

/-- The target of the picked arm `j` of the second stage of the chain node at index `k` of a
state's output, the node's first instruction at `pos`. -/
def weOf (Γ : Site κ₀) (st : St) (k pos j : ℕ) : E :=
  match st.out.toList[k]? with
  | some (.chain _ _ _ _ _ _ _ stg) =>
      Γ.tgt (pos + 3 + stagesSize (stg.take 1) + armsSize (((stg.drop 1).headD []).take j))
  | _ => 0

theorem weOf_eq {st : St} {O B : List PStmt} {h : List LHint} {join lx entry one sfp : ℕ}
    {firsts : List ℕ} {bs : List (List PStmt)} {stagesN : List (List (List PStmt))}
    (ho : st.out.toList = O ++ [PStmt.chain h join lx entry one sfp firsts (bs :: stagesN)] ++ B)
    (pos j : ℕ) :
    weOf Γ st O.length pos j = Γ.tgt (pos + 3 + armsSize bs + armsSize ((stagesN.headD []).take j)) := by
  simp [weOf, ho, stagesSize]

/-- An action's spec proved knowing its final state. -/
theorem FBAt.at_end {α : Type} {C : (ℕ → E) → Prop} {st : St} {m : P α}
    {R : α → ((ℕ → E) → Prop) → St → Prop}
    (h : ∀ a Sf, m ctx st = .ok (a, Sf) →
      FBAt ctx I C st m fun a' C' st' => st' = Sf → R a' C' st') :
    FBAt ctx I C st m R := fun hc a Sf he => by
  obtain ⟨C', h1, h2, h3, h4, h5, h6⟩ := h a Sf he hc a Sf he
  exact ⟨C', h1, h2, h3, h4, h5, h6 rfl⟩

end Pieces

/-! ## The head of a chain -/

section Head

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Backend.Ctx} {I : Inst}

set_option maxHeartbeats 4000000 in
/-- **The head of a chain whose arms dispatch into the next `match`**, from the state after its
edge flush, with the rest of its block (`ChainHeadW` for a block whose second statement is a
`match`). -/
theorem chainHead_match (hnew : PlaceNew ctx) (hok : OpOK Γ I Ag cl) (hI : I.Ok)
    (hmain : ctx.isMain = true → I.fp = 0) (hAg : AgOwn I Ag) (hkw : ∀ k, I.kw k = kwOf Γ k)
    {Good : List Stmt → Prop}
    (hopen : OpenW (Γ := Γ) (Ag := Ag) (cl := cl) (ctx := ctx) (I := I) Good)
    (hoff : OpenOffW (ctx := ctx))
    {x x' : V} {arms arms' : List (List Stmt)} {rest' tl : List Stmt} (hu : x ∉ I.tmps)
    (hg' : Good (.match_ x' arms' :: rest'))
    (ih' : BlockIH Γ Ag cl ctx I Good (.match_ x' arms' :: rest'))
    (hfa : FaAfter I.σ (.match_ x arms) (.match_ x' arms' :: rest'))
    (hin : ∀ j (hj : j < arms.length), InBlockW Γ Ag cl ctx I arms[j])
    (hafa : ∀ j (hj : j < arms.length), ∀ v ∈ pathVals I.σ arms[j] (walk I.σ arms[j]), ∀ run,
      Atom.frameAddr v run ∉ armsAtoms (arms.drop (j + 1)))
    {C C₂ : (ℕ → E) → Prop} {st st₂ : St} {sc s₀ s₁ sc' sc'' : SSt} {i₀ p₀ : ℕ} {o : Out}
    (hinv : WInv ctx I C st sc) (h₀ : flushEdge ctx.retCells sc = .ok s₀)
    (hx : s₀.live.contains x = true) (hsa : scopeArms ctx.retCells arms s₀ s₀.retDone = .ok s₁)
    (hem : expectS isEmit "a match" s₁ = .ok sc')
    (hsc : scopeBlock ctx.retCells (.match_ x' arms' :: rest') sc' = .ok sc'')
    (hw : walk I.σ (.match_ x arms :: .match_ x' arms' :: rest') = o) (hns : o ≠ .stuck)
    (hes : ∀ e ∈ outEs o, e ∈ I.es)
    (hcl : ∀ k < (calls (outEs o)).length, cl[i₀ + k]? = (calls (outEs o))[k]?)
    (hn₂ : st.next ≤ st₂.next) (hE₂ : EmitsW I C₂ st st₂) (hpk₂ : PK st st₂)
    (hr₂ : st₂.rest = s₀.rest) (hf₂ : st₂.rest.length ≤ ctx.fuel)
    (hvw₂ : VW I C₂ st₂ (fun v => s₀.live.contains v = true))
    (hrb₂ : s₀.retDone = false → RetBlind ctx C₂)
    (hloc₂ : ∀ v, st₂.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest))
    (hch₂ : st₂.chainIn = none) (hz₂ : st₂.lazy = none) :
    FBAt ctx I C₂ st₂ (placeMatch x arms.length (.match_ x' arms' :: rest') none true
      (fun base exit => placeArms arms 0 arms.length base exit) >>= fun _ =>
        endStmt >>= fun _ => placeBlock (.match_ x' arms' :: rest'))
      fun _ C' st' => BlockOut Γ Ag cl ctx I st sc''
        (.match_ x arms :: .match_ x' arms' :: rest') tl o i₀ p₀ C' st' := by
  -- the walk
  rw [walk] at hw
  obtain ⟨o₁, ho₁⟩ : ∃ o₁, walk1 I.σ (.match_ x arms) = o₁ := ⟨_, rfl⟩
  rw [ho₁] at hw
  have hns₁ : o₁ ≠ .stuck := fun h => hns (by rw [← hw, h]; rfl)
  have hns' : walkArms I.σ x 0 arms ≠ .stuck := fun h => hns₁ (by rw [← ho₁, walk1, h])
  obtain ⟨j, hj, hxj, hne, hwj, hsel⟩ := walkArms_pick arms 0 hns'
  simp only [Nat.zero_add] at hxj hne
  have hwo : walk I.σ arms[j] = o₁ := by rw [← hwj, ← ho₁, walk1]
  obtain ⟨es', hes'⟩ : ∃ es', outEs o = outEs o₁ ++ es' := by
    cases o₁ with
    | fall es₁ =>
      have hst : walk I.σ (.match_ x' arms' :: rest') ≠ .stuck := fun h =>
        hns (by rw [← hw, h]; rfl)
      exact ⟨_, by rw [← hw]; simp only [Out.seq]; rw [outEs_pre hst]; rfl⟩
    | ret es₁ vs => exact ⟨[], by rw [← hw]; simp [Out.seq, outEs]⟩
    | stuck => exact absurd rfl hns₁
  have hes₁ : ∀ e ∈ outEs o₁, e ∈ I.es := fun e he =>
    hes e (by rw [hes']; exact List.mem_append_left _ he)
  have hcl₁ : ∀ k < (calls (outEs o₁)).length, cl[i₀ + k]? = (calls (outEs o₁))[k]? :=
    fun k hk => by
      rw [hcl k (by rw [hes', calls_append', List.length_append]; omega), hes', calls_append',
        List.getElem?_append_left hk]
  obtain ⟨j₂, hj₂⟩ : ∃ j₂, ∀ es₁, o₁ = .fall es₁ → I.σ x' = ofK (addressOfIndex j₂) ∧
      ∀ i < j₂, I.σ x' ≠ ofK (addressOfIndex i) := by
    cases o₁ with
    | fall es₁ =>
      have hst : walkArms I.σ x' 0 arms' ≠ .stuck := fun h => hns (by
        rw [← hw]; simp [Out.seq, walk, walk1, h, Out.pre])
      obtain ⟨j₂, -, hx2, hne2, -, -⟩ := walkArms_pick arms' 0 hst
      exact ⟨j₂, fun _ _ => ⟨by simpa using hx2, fun i hi => by simpa using hne2 i hi⟩⟩
    | ret es₁ vs => exact ⟨0, fun _ h => nomatch h⟩
    | stuck => exact absurd rfl hns₁
  -- the next stage's selector
  have hsc0 := hsc
  rw [scopeBlock] at hsc0
  split at hsc0
  · cases hsc0
  next sc₁' hsc₁ =>
  obtain ⟨s₀', s₁', h₀', hx'', -, -⟩ := scopeMatch_inv hsc₁
  have hx' := nextSel_ok hinv h₀ hloc₂ hsa hem h₀' hx''
  have hvwx : VW I C₂ st₂ fun v => s₀.live.contains v = true ∨ st₂.locs[v]? = none :=
    fun v l hv hl => hv.elim (fun h => hvw₂ v l h hl) fun h => by rw [h] at hl; cases hl
  refine FBAt.at_end fun _ Sf _ => ?_
  unfold placeMatch
  rw [bind_assoc]
  refine FBAt.fat_bind (FAt.and_wp
    (matchCells_fatC hI hmain hvwx (Or.inl hx) hx' (le_trans hinv.two hn₂))
    (wp_and matchCells_pk (wp_and matchCells_lz (wp_and matchCells_keep matchCells_placed))))
    fun r st₃ C₃ hs₃ hn₃ hl₃ _ hE₃ ⟨⟨⟨lx', hns3, hy2, hylt, hyw⟩, hx2, hxlt, hxw, hf2, hflt, hfw,
      ho2, holt, how, hlo₃, hr₃, hkb₃⟩, hpk₃, hz₃, hk₃, hpl₃⟩ => ?_
  obtain ⟨lx, ns, sfp, one⟩ := r
  simp only at hns3 hx2 hxlt hxw hf2 hflt hfw ho2 holt how
  subst hns3
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
  refine FBAt.fat_bind (fresh_fat (fun _ => entryW Γ ctx arms
      (.next lx' (st₃.tables.len + arms.length) one sfp) j (p₀ + blockSize st₃.out.toList)
      { st₃ with next := st₃.next + 2, tables.len := st₃.tables.len + arms.length + arms'.length, pending := #[] })
    (wblind_const _ _)) fun entry S₇ C₇ _ _ _ _ hE₇ ⟨hen, hS₇, hC₇⟩ => ?_
  subst hen
  refine FBAt.fat_bind (FAt.ofSame (R := fun a C' st' => a = S₇.tables.len ∧ C₇ = C' ∧
      st' = { S₇ with tables.len := S₇.tables.len + arms'.length })
    (wp_modifyGet.mpr ⟨rfl, rfl, rfl, LocsLe.refl _, rfl, rfl, rfl⟩))
    fun nf S C₈' _ _ _ hcS hE₈ ⟨hnf, hC₈', hS⟩ => ?_
  subst hC₈'
  have hnf' : nf = st₃.tables.len + arms.length := by rw [hnf, hS₇]
  subst hnf'
  set n := st₃.next with hn
  set pos := p₀ + blockSize st₃.out.toList with hpos
  have hSe : S = { st₃ with next := st₃.next + 2, tables.len := st₃.tables.len + arms.length + arms'.length, pending := #[] } := by
    rw [hS, hS₇]
  have hSn : S.next = n + 2 := by rw [hSe]
  have hSl : S.locs = st₂.locs := by rw [hSe]; exact hlo₃
  have hSr : S.rest = s₀.rest := by rw [hSe]; exact hr₃.trans hr₂
  have hSo : S.out = st₃.out := by rw [hSe]
  have hSc : S.chainIn = none := by
    rw [hSe]; exact (show st₃.chainIn = st₂.chainIn from hk₃).trans hch₂
  have hSz : S.lazy = none := by rw [hSe]; exact hz₃.1.trans hz₂
  have hSt : S.tables.shared = st₃.tables.shared := by rw [hSe]
  have hC7 : ∀ Ψ, C₇ Ψ → C₃ Ψ ∧ Ψ n = joinW I pos ∧ Ψ (n + 1) = entryW Γ ctx arms
      (.next lx' (st₃.tables.len + arms.length) one sfp) j pos
      { st₃ with next := st₃.next + 2, tables.len := st₃.tables.len + arms.length + arms'.length, pending := #[] } := by
    subst hC₇; exact fun Ψ h => ⟨h.1.1, h.1.2, h.2⟩
  have hkb₇ : KeepB C₂ C₇ st₂.next := by
    subst hC₇
    intro c hc hb
    have hcn : c < n := lt_of_lt_of_le hc hn₃
    exact blindAt_assign (blindAt_assign (hkb₃ c hc hb) (Nat.ne_of_lt hcn))
      (Nat.ne_of_lt (Nat.lt_succ_of_lt hcn))
  have hs₇ : Stronger C₇ C₂ := fun Ψ h => hs₃ Ψ (hC7 Ψ h).1
  have hn₂S : st₂.next ≤ S.next := by rw [hSn]; exact le_trans hn₃ (Nat.le_add_right _ _)
  have hpkS : PK st S :=
    hpk₂.trans (hpk₃.trans (pk_same (by rw [hSe]) (by rw [hSe]) (by rw [hSe])))
  have hinvS : OutOps I S → WInv ctx I C₇ S s₀ := fun hO =>
    winv_edge hinv h₀ hcS (le_trans hn₂ hn₂S) hSr (hvw₂.step hs₇ hn₂S hSl)
      (fun hr => RetBlind.keep (hrb₂ hr) (le_trans hinv.abi hn₂) hkb₇)
      (fun v hv => hloc₂ v (by rwa [hSl] at hv)) hSc
      ⟨fun k o' hk => (hpkS.2.1 k o' hk).nt hI hinv.pnt hO,
        fun c' l hc' p hp => (hpkS.2.2 c' l hc' p hp).nt hI hinv.pnt hO⟩ hSz
  have hfS : S.rest.length ≤ ctx.fuel := by rw [hSr, ← hr₂]; exact hf₂
  refine FBAt.get_bind ?_
  refine FBAt.bind (FBAt.and_wp (arms_fb (q := pos + 3) (i₀ := i₀)
    (exit := .next lx' (st₃.tables.len + arms.length) one sfp)
    (weOf Γ Sf st₃.out.toList.length pos j₂) hj
    (hin j hj) hsa hSr hfS hinvS hwo hns₁ hes₁ hcl₁ (hwo ▸ hafa j hj)) wp_eq)
    (fun _ _ _ h => h.1.1) ?_
  rintro bs st₈ C₈ hs₈ hn₈ hl₈ ⟨⟨-, hlen, hr₈, -, ho₈, hch₈, -, hsub₈, ht₈, hpick, -⟩, heq⟩
  obtain ⟨ev, hev, heS, -, -⟩ := expectS_ok hem
  refine stageEndNext_fbat (hr₈.trans hev) ?_
  have hjb : j < bs.length := hlen ▸ hj
  have hO8 : st₈.out.toList = st₃.out.toList := by rw [ho₈, hSo]
  have hC8 : ∀ Ψ, C₈ Ψ → C₃ Ψ ∧ Ψ n = joinW I pos ∧ Ψ (n + 1) = entryW Γ ctx arms
      (.next lx' (st₃.tables.len + arms.length) one sfp) j pos
      { st₃ with next := st₃.next + 2, tables.len := st₃.tables.len + arms.length + arms'.length, pending := #[] } :=
    fun Ψ h => hC7 Ψ (hs₈ Ψ h)
  have hn8 : n + 2 ≤ st₈.next := hSn ▸ hn₈
  -- the facts the final node gives the stages before it
  have hQof : ∀ (st' : St) (firstsN : List ℕ) (stagesN : List (List (List PStmt)))
      (blk : List PStmt), FinAt Γ I Ag p₀ st' → st₈.next ≤ st'.next → LocsLe st₈.locs st'.locs →
      (∀ y ∈ st₈.tables.shared, y ∈ st'.tables.shared) →
      st'.out.toList = st₃.out.toList ++ [PStmt.chain hints n lx (n + 1) one sfp
        (st₃.tables.len :: firstsN) (bs :: stagesN)] ++ blk →
      (OutOps I S ∧ Fits I st₈ ∧ TabsW Γ Ag st₈ ∧ OpsIn I (pos + 3) (armsOps bs (pos + 3)) ∧
        ∀ f k i, (k, KVal.at f i) ∈ armsFills f st₃.tables.len bs 0 (pos + 3) →
          ∀ σ' Ψ kh κ (L : MemoryImage κ), Ag σ' Ψ kh κ L →
            L.read (addressOfIndex (Γ.l.tablesBase + k)) = some (Γ.tgt i)) ∧
      OpsIn I pos (stmtOps (PStmt.chain hints n lx (n + 1) one sfp
        (st₃.tables.len :: firstsN) (bs :: stagesN)) pos) ∧
      FillsIn Γ Ag pos [PStmt.chain hints n lx (n + 1) one sfp
        (st₃.tables.len :: firstsN) (bs :: stagesN)] := by
    intro st' firstsN stagesN blk hF hn hl ht hout
    obtain ⟨hOp, hFl⟩ := fin_mid hF hout
    obtain ⟨-, -, -, hSo', -⟩ := opsIn_chain hOp
    refine ⟨⟨fun h' o' hm => hF.2.1.outOps h' o' (by
        rw [hout]; rw [hSo] at hm; exact List.mem_append_left _ (List.mem_append_left _ hm)),
      hF.1.back hn hl, fun fs f hm => hF.2.2.1 fs f (ht _ hm), ?_,
      fun f k i hm => fills_stage1 hFl hm⟩, hOp, hFl⟩
    simp only [stagesOps] at hSo'
    exact hSo'.left
  -- the picked arm, under those facts
  have harm : OutOps I S → Fits I st₈ → TabsW Γ Ag st₈ → OpsIn I (pos + 3) (armsOps bs (pos + 3)) →
      (∀ f k i, (k, KVal.at f i) ∈ armsFills f st₃.tables.len bs 0 (pos + 3) →
        ∀ σ' Ψ kh κ (L : MemoryImage κ), Ag σ' Ψ kh κ L →
          L.read (addressOfIndex (Γ.l.tablesBase + k)) = some (Γ.tgt i)) →
      ∃ blk e, bs[j] = blk ++ [PStmt.op [] (.slot lx' (st₃.tables.len + arms.length) e),
          .op [] (.jump one e sfp)] ∧ S.next ≤ e ∧ e < st₈.next ∧
        (∀ Ψ, C₈ Ψ → Ψ e = weOf Γ Sf st₃.out.toList.length pos j₂) ∧
        (∀ es, o₁ = .fall es → WInv ctx I C₈ st₈ s₁) ∧
        BlkW Γ I ctx Ag cl C₈ blk arms[j] [] o₁ i₀ (pos + 3 + armsSize (bs.take j)) ∧
        RW I C₈ st₈ (pathVals I.σ arms[j] o₁) := by
    intro hO hFt hT hAo hFl
    obtain ⟨blk, leave, hbs, hlv, hW, hB⟩ := hpick hO
    obtain ⟨e, he1, he2, hleave, hew⟩ := hlv
    have hbj : bs[j] = blk ++ leave :=
      Option.some.inj ((List.getElem?_eq_getElem hjb).symm.trans hbs)
    have hA := armsOps_in bs (pos + 3) j hjb hAo
    have hFa : FillsIn Γ Ag (pos + 3 + armsSize (bs.take j)) bs[j] := fun f k i hm =>
      hFl f k i (armsFills_blk f _ bs 0 (pos + 3) j hjb hm)
    rw [hbj, bops_append] at hA
    rw [hbj] at hFa
    obtain ⟨hBw, hRw⟩ := hB hFt hA.left hT hFa.left
    exact ⟨blk, e, hleave ▸ hbj, he1, he2, hew, fun es h => hW es h hFt hA.left hT hFa.left,
      hBw, hRw⟩
  -- the chain's head words
  have hheadOf : ∀ (firstsN : List ℕ) (stagesN : List (List (List PStmt))),
      OpsIn I pos (stmtOps (PStmt.chain hints n lx (n + 1) one sfp
        (st₃.tables.len :: firstsN) (bs :: stagesN)) pos) →
      FillsIn Γ Ag pos [PStmt.chain hints n lx (n + 1) one sfp
        (st₃.tables.len :: firstsN) (bs :: stagesN)] → Fits I st₈ →
      ∀ Ψ, C₈ Ψ → ∀ σ' (kh : ℕ → E × E),
      HW Γ I.fp (Ag σ' Ψ kh) (Γ.pc0 + pos)
          (.set n (.local (pos + 3 + stagesSize (bs :: stagesN)))) ∧
        HW Γ I.fp (Ag σ' Ψ kh) (Γ.pc0 + pos + 1)
          (.slot lx ((st₃.tables.len :: firstsN).headD 0) (n + 1)) ∧
        JumpTo Γ I.fp I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) one (n + 1) sfp
          (pos + 3 + armsSize (bs.take j)) := by
    intro firstsN stagesN hOp hFl hFt Ψ hΨ σ' kh
    obtain ⟨hset, hslo, hjmp, -, hle⟩ := opsIn_chain hOp
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
    have hfj : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ n =
        kwOf Γ (.local (pos + 3 + stagesSize (bs :: stagesN))) :=
      (fwd_patchT h2n htj).trans (hjw.trans ((joinW_eq hset).trans (hkw _)))
    have hn1 : n + 1 < I.size := lt_of_lt_of_le (Nat.lt_succ_self _) hsz
    have hn0 : n < I.size := lt_trans (Nat.lt_succ_self _) hn1
    have hfe : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ (n + 1) = Γ.tgt (pos + 3 + armsSize (bs.take j)) :=
      (fwd_patchT (le_trans h2n (Nat.le_succ n)) hte).trans (hew.trans (entryW_eq heq))
    have hfx : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ lx = ofK (addressOfIndex j) :=
      (fwd_patchT hx2 htx).trans ((hxw Ψ hc3).trans hxj)
    have hsl1 : ∀ (κ : ℕ) (L : MemoryImage κ), Ag σ' Ψ kh κ L →
        L.read (addressOfIndex (Γ.l.tablesBase + (st₃.tables.len + j))) =
          some (fwd I.hdr ⟨patchT I Ψ σ', kh⟩ (n + 1)) := fun κ L hL => by
      rw [hfe]
      have := armsFills_mem "" st₃.tables.len bs 0 (pos + 3) j hjb
      simp only [Nat.zero_add] at this
      exact fills_stage1 hFl this σ' Ψ kh κ L hL
    exact ⟨set_hw hr hn0 hfj, slot_hw hr (lt_trans hxlt hn0) hn1 hfx hsl1,
      jumpTo_of hr (lt_trans holt hn0) hn1 (lt_trans hflt hn0)
        ((fwd_patchT ho2 hto).trans (how Ψ hc3)) hfe ((fwd_patchT hf2 hts).trans (hfw Ψ hc3))⟩
  obtain ⟨ops, hops, hopsW⟩ := hE₂.step hE₃ hs₃ hn₃ hl₃
  have hp : p₀ + blockSize st.out.toList + blockSize ops = pos := by
    rw [hpos, Nat.add_assoc, ← bsize_append, ← hops]
  -- the rest of the block, entered by the open chain
  have key : ∀ St' : St, St'.rest = sc'.rest →
      St'.out.toList = st₈.out.toList ++
        [PStmt.chain hints n lx (n + 1) one sfp [st₃.tables.len] [bs]] →
      St'.chainIn = some (st₃.tables.len + arms.length, n) → St'.lazy = none →
      St'.next = st₈.next → St'.locs = st₈.locs → St'.tables = st₈.tables →
      (∀ es, o₁ = .fall es →
        (OutOps I S ∧ Fits I st₈ ∧ TabsW Γ Ag st₈ ∧ OpsIn I (pos + 3) (armsOps bs (pos + 3)) ∧
        ∀ f k i, (k, KVal.at f i) ∈ armsFills f st₃.tables.len bs 0 (pos + 3) →
          ∀ σ' Ψ kh κ (L : MemoryImage κ), Ag σ' Ψ kh κ L →
            L.read (addressOfIndex (Γ.l.tablesBase + k)) = some (Γ.tgt i)) →
        WInv ctx I C₈ { St' with chainIn := none } sc') →
      FBAt ctx I C₈ St' (placeBlock (.match_ x' arms' :: rest')) fun _ C' st' =>
        st' = Sf → BlockOut Γ Ag cl ctx I st sc''
          (.match_ x arms :: .match_ x' arms' :: rest') tl o i₀ p₀ C' st' := by
    intro St' hRr hRo hRc hRz hRn hRl hRt hRinv
    have hoffS := hoff x' arms' rest' St' st₈.out.toList hints n lx (n + 1) one sfp
      (st₃.tables.len + arms.length) [st₃.tables.len] [bs] n hRc hRo
    have hnewS := hnew (.match_ x' arms' :: rest') St'
    have hsubr : ∀ v ∈ allocsOf St'.rest, v ∈ allocsOf st₈.rest := fun v hv => by
      rw [hr₈, hev]
      rw [hRr] at hv
      simp only [allocsOf, List.flatMap_cons, List.mem_append]
      exact Or.inr hv
    -- the values the stage read, at the open state
    have hrwS : OutOps I S → RW I C₈ st₈ (pathVals I.σ arms[j] o₁) →
        RW I C₈ St' (pathVals I.σ [.match_ x arms] o₁) := by
      intro hO hRw
      have hrw : RW I C₈ St' (pathVals I.σ arms[j] o₁) :=
        hRw.grow (Stronger.refl _) (by rw [hRn]) (by rw [hRl]; exact LocsLe.refl _)
          (fun v _ h => Or.inl (by rwa [hRl] at h)) hsubr
      have hxrw : RW I C₈ St' [x] := by
        intro v hv
        rw [List.mem_singleton] at hv
        rw [hv]
        obtain ⟨l₀, hl₀⟩ := Option.ne_none_iff_exists'.mp hpl₃
        refine ⟨fun h => ?_, fun _ l hl => ?_⟩
        · have := ((hinvS hO).fresh x (hsub₈ x (hsubr x h))).2
          rw [hx] at this
          cases this
        · have h8 : st₈.locs[x]? = some l₀ := hl₈ x l₀ (by rw [hSl]; exact hl₀)
          rw [hRl, h8] at hl
          cases hl
          obtain ⟨b1, b2, b3⟩ := hvw₂ x l₀ hx hl₀
          exact ⟨b1, by rw [hRn]; exact lt_of_lt_of_le b2 (le_trans hn₂S hn₈),
            fun Ψ hΨ => b3 Ψ (hs₇ Ψ (hs₈ Ψ hΨ))⟩
      exact (hxrw.append hrw).anti fun v hv => by simpa using pathVals_match hj hsel v hv
    have hF3 : Fits I st₈ → Fits I st₃ := fun hFt => hFt.back (le_trans (Nat.le_add_right _ _) hn8)
      (fun v l h => hl₈ v l (by rw [hSl, ← hlo₃]; exact h))
    have hW3 : ∀ (C' : (ℕ → E) → Prop), Stronger C' C₈ → OutOps I S → Fits I st₈ →
        ∀ s ∈ ops, ∃ h o, s = PStmt.op h o ∧ ∀ Ψ, C' Ψ → OpW I Ψ o := fun C' hs' hO hFt s hs => by
      obtain ⟨h, o', rfl, hw'⟩ := hopsW (hF3 hFt) (fun h o' hm => hO h o' (by rw [hSo]; exact hm)) s hs
      exact ⟨h, o', rfl, fun Ψ hΨ => hw' Ψ (hC8 Ψ (hs' Ψ hΨ)).1⟩
    cases o₁ with
    | stuck => exact absurd rfl hns₁
    | fall es₁ =>
      have hw' : o = (walk I.σ (.match_ x' arms' :: rest')).pre es₁ := by rw [← hw]; rfl
      have hns₂ : walk I.σ (.match_ x' arms' :: rest') ≠ .stuck := fun h =>
        hns (by rw [hw', h]; rfl)
      have hc' : calls (outEs o) =
          calls es₁ ++ calls (outEs (walk I.σ (.match_ x' arms' :: rest'))) := by
        rw [hw', outEs_pre hns₂, calls_append']
      have hes₂ : ∀ e ∈ outEs (walk I.σ (.match_ x' arms' :: rest')), e ∈ I.es := fun e he =>
        hes e (by rw [hw', outEs_pre hns₂]; exact List.mem_append_right _ he)
      have hcl₂ : ∀ k < (calls (outEs (walk I.σ (.match_ x' arms' :: rest')))).length,
          cl[i₀ + (calls es₁).length + k]? =
            (calls (outEs (walk I.σ (.match_ x' arms' :: rest'))))[k]? := fun k hk => by
        rw [Nat.add_assoc, hcl _ (by rw [hc', List.length_append]; omega), hc',
          List.getElem?_append_right (by omega)]
        simp
      obtain ⟨hj2, hne2⟩ := hj₂ es₁ rfl
      have hop := hopen x' arms' rest' tl hg' ih' C₈ St' sc' sc'' (i₀ + (calls es₁).length) p₀
        (walk I.σ (.match_ x' arms' :: rest')) st₈.out.toList hints n lx (n + 1) one sfp
        [st₃.tables.len] [bs] (st₃.tables.len + arms.length) _ hsc rfl hns₂ hes₂ hcl₂
        (hRinv es₁ rfl) hRc
        ⟨le_trans hx2 (Nat.le_of_lt hxlt),
          by rw [hRn]; exact lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_succ_self n)) hn8,
          fun Ψ hΨ => by rw [hO8]; exact (hC8 Ψ hΨ).2.1⟩ hRo rfl
      refine FBAt.mono (FBAt.and_wp (FBAt.and_wp hop hoffS) hnewS) ?_
      rintro _ C' st' hs' hn' hl' ⟨⟨hOO, -, hRn', hRl', hRt', firstsN, stagesN, blk, hout, -⟩,
        hnw, hrr, -⟩ rfl
      simp only [List.singleton_append] at hout
      rw [hO8] at hout
      rw [hRn] at hRn'
      rw [hRl] at hRl'
      rw [hRt] at hRt'
      refine ⟨fun es h hF => ?_, hOO.1, fun hF => ?_⟩
      · obtain ⟨hQ, -, -⟩ := hQof st' firstsN stagesN blk hF hRn' hRl' hRt' hout
        rw [hw'] at h
        cases h₂ : walk I.σ (.match_ x' arms' :: rest') with
        | fall es₂ => exact hOO.2.1 es₂ h₂ hF hQ
        | ret es₂ vs => rw [h₂] at h; cases h
        | stuck => exact absurd h₂ hns₂
      obtain ⟨hQ, -, -⟩ := hQof st' firstsN stagesN blk hF hRn' hRl' hRt' hout
      obtain ⟨hO, hFt, hT, hAo, hFl'⟩ := hQ
      obtain ⟨blkA, e, hbj, he1, he2, hew, -, hBw, hRw⟩ := harm hO hFt hT hAo hFl'
      obtain ⟨firstsN', stagesN', blk', j', T, hout', -, -, -, hlenS, hxj', hne', hT', hslotT,
        hSW, hRW⟩ := hOO.2.2 hF ⟨hO, hFt, hT, hAo, hFl'⟩
      simp only [List.singleton_append] at hout'
      rw [hO8] at hout'
      obtain ⟨-, hOp, hFl⟩ := hQof st' firstsN' stagesN' blk' hF hRn' hRl' hRt' hout'
      have hjj : j' = j₂ := pick_unique hxj' hne' hj2 hne2
      subst hjj
      have hwe : weOf Γ st' st₃.out.toList.length pos j' = Γ.tgt T := by
        rw [weOf_eq hout' pos j', hT', hO8]
        congr 1
      have hq : p₀ + blockSize st₈.out.toList + 3 + stagesSize [bs] = pos + 3 + armsSize bs := by
        rw [hO8]; simp only [stagesSize]; omega
      rw [hq] at hSW
      have hsl : ∀ Ψ, C' Ψ → ∀ σ' (kh : ℕ → E × E),
          HW Γ I.fp (Ag σ' Ψ kh) (Γ.pc0 + (pos + 3 + armsSize (bs.take j) + blockSize blkA))
            (.slot lx' (st₃.tables.len + arms.length) e) ∧
          JumpTo Γ I.fp I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) one e sfp T := by
        intro Ψ hΨ σ' kh
        obtain ⟨-, -, hjmp, hSo', -⟩ := opsIn_chain hOp
        simp only [stagesOps] at hSo'
        have hA := armsOps_in bs (pos + 3) j hjb hSo'.left
        rw [hbj, bops_append] at hA
        have hslo' := hA.right.mem (LOp.slot lx' (st₃.tables.len + arms.length) e)
          (by simp [blockOps, stmtOps])
        have hr : Rds (Ag σ' Ψ kh) I.fp I.size (fwd I.hdr ⟨patchT I Ψ σ', kh⟩) :=
          fun κ L hL m hm => hAg σ' Ψ kh κ L hL m hm
        have hΨ8 := hs' Ψ hΨ
        obtain ⟨hc3, -, -⟩ := hC8 Ψ hΨ8
        have hsz : st₈.next ≤ I.size := hFt.1
        rw [hSn] at he1
        have he2' : 2 ≤ e := le_trans (Nat.le_add_left 2 n) he1
        have hte : ¬ I.tc e := not_tc_of hI hslo' (by simp [opCells]) fun _ h => nomatch h
        have hty : ¬ I.tc lx' := not_tc_of hI hslo' (by simp [opCells]) fun _ h => nomatch h
        have hto : ¬ I.tc one := not_tc_of hI hjmp (by simp [opCells]) fun _ h => nomatch h
        have hts : ¬ I.tc sfp := not_tc_of hI hjmp (by simp [opCells]) fun _ h => nomatch h
        have hfe : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ e = Γ.tgt T :=
          (fwd_patchT he2' hte).trans ((hew Ψ hΨ8).trans hwe)
        have hfy : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ lx' = ofK (addressOfIndex j') :=
          (fwd_patchT hy2 hty).trans ((hyw Ψ hc3).trans hj2)
        have hn3 : n ≤ I.size := le_trans (Nat.le_add_right n 2) (le_trans hn8 hsz)
        refine ⟨slot_hw hr (lt_of_lt_of_le hylt hn3) (lt_of_lt_of_le he2 hsz) hfy
          (fun κ L hL => by rw [hfe]; exact hslotT σ' Ψ kh κ L hL), ?_⟩
        exact jumpTo_of hr (lt_of_lt_of_le holt hn3) (lt_of_lt_of_le he2 hsz)
          (lt_of_lt_of_le hflt hn3) ((fwd_patchT ho2 hto).trans (how Ψ hc3)) hfe
          ((fwd_patchT hf2 hts).trans (hfw Ψ hc3))
      have hSt := stagesW_next (q := pos + 3) (C := C')
        (o₂ := walk I.σ (.match_ x' arms' :: rest')) hjb hj hbj hxj hne hxS hw.symm
        (hBw.mono hs') (fun es h => by cases h; exact hSW)
        (fun _ _ _ Ψ hΨ σ' _ kh => hsl Ψ hΨ σ' kh)
      have hhd := hheadOf firstsN' stagesN' hOp hFl hFt
      have hl2 : (bs :: stagesN').length ≤
          (Stmt.match_ x arms :: Stmt.match_ x' arms' :: rest').length := Nat.succ_le_succ hlenS
      have hX : BlkW Γ I ctx Ag cl C' ([PStmt.chain hints n lx (n + 1) one sfp
          (st₃.tables.len :: firstsN') (bs :: stagesN')] ++ blk')
          (.match_ x arms :: .match_ x' arms' :: rest') tl o i₀ pos := blkW_chainS hl2 hSt
        (fun _ Ψ hΨ σ' _ kh _ => hhd Ψ (hs' Ψ hΨ) σ' kh)
      refine ⟨ops ++ ([PStmt.chain hints n lx (n + 1) one sfp (st₃.tables.len :: firstsN')
        (bs :: stagesN')] ++ blk'), by rw [hout', hops]; simp, ?_, ?_⟩
      · exact blkW_ops_B hok (by simp) (hW3 C' hs' hO hFt) (by rw [hp]; exact hX)
      · have hvs := placeNew_vs hfa (hnw hRz)
        rw [ho₁] at hvs
        have h1 := (hrwS hO hRw).grow hs' hn' hl' hvs hrr
        rw [hw']
        exact (h1.append hRW).anti (pathVals_fall ho₁ hns₂)
    | ret es₁ vs =>
      have hoe : o = .ret es₁ vs := by rw [← hw]; rfl
      have hoffD : wpP (placeBlock (.match_ x' arms' :: rest')) ctx St' fun _ st' =>
          St'.next ≤ st'.next ∧ LocsLe St'.locs st'.locs ∧ (st'.chainIn = none ∧
          (∀ y ∈ St'.tables.shared, y ∈ st'.tables.shared) ∧
          ∃ (firstsN : List ℕ) (stagesN : List (List (List PStmt))) (blk : List PStmt),
            st'.out.toList = st₈.out.toList ++ [PStmt.chain hints n lx (n + 1) one sfp
              ([st₃.tables.len] ++ firstsN) ([bs] ++ stagesN)] ++ blk ∧
            firstsN.head? = some (st₃.tables.len + arms.length)) :=
        wp_mono hoffS fun _ _ h => ⟨h.2.1, h.2.2.1, h.1, h.2.2.2.1, h.2.2.2.2⟩
      refine FBAt.mono (FBAt.and_wp (FBAt.dead hoffD) hnewS) ?_
      rintro _ C' st' hs' hn' hl' ⟨⟨rfl, hch', hRt', firstsN, stagesN, blk, hout⟩, hnw, hrr, -⟩ rfl
      obtain ⟨hout, -⟩ := hout
      simp only [List.singleton_append] at hout
      rw [hO8] at hout
      rw [hRn] at hn'
      rw [hRl] at hl'
      rw [hRt] at hRt'
      refine ⟨fun es h _ => by rw [hoe] at h; exact Out.noConfusion h, hch', fun hF => ?_⟩
      obtain ⟨⟨hO, hFt, hT, hAo, hFl'⟩, hOp, hFl⟩ :=
        hQof st' firstsN stagesN blk hF hn' hl' hRt' hout
      obtain ⟨blkA, e, hbj, -, -, -, -, hBw, hRw⟩ := harm hO hFt hT hAo hFl'
      have hSt := stagesW_next (q := pos + 3) (C := C')
        (rest := (.match_ x' arms' :: rest') ++ tl) (tl := []) (stagesN := stagesN) (blk := blk)
        (o := .ret es₁ vs) (o₂ := .stuck) (T' := 0) hjb hj hbj hxj hne hxS rfl hBw
        (fun _ h => Out.noConfusion h) (fun _ h => Out.noConfusion h)
      have hhd := hheadOf firstsN stagesN hOp hFl hFt
      have hX : BlkW Γ I ctx Ag cl C' ([PStmt.chain hints n lx (n + 1) one sfp
          (st₃.tables.len :: firstsN) (bs :: stagesN)] ++ blk)
          (.match_ x arms :: .match_ x' arms' :: rest') tl (.ret es₁ vs) i₀ pos :=
        blkW_chainS_ret hSt
        (fun _ Ψ hΨ σ' _ kh _ => hhd Ψ hΨ σ' kh)
      refine ⟨ops ++ ([PStmt.chain hints n lx (n + 1) one sfp (st₃.tables.len :: firstsN)
        (bs :: stagesN)] ++ blk), by rw [hout, hops]; simp, ?_, ?_⟩
      · rw [hoe]
        exact blkW_ops_B hok (by simp) (hW3 C' (Stronger.refl _) hO hFt) (by rw [hp]; exact hX)
      · have hvs := placeNew_vs hfa (hnw hRz)
        rw [ho₁] at hvs
        rw [hoe, pathVals_ret ho₁]
        exact (hrwS hO hRw).grow hs' (by rw [hRn]; exact hn') (by rw [hRl]; exact hl') hvs hrr
  refine key _ rfl (by simp) rfl rfl rfl rfl rfl fun es h hQ => ?_
  obtain ⟨hO, hFt, hT, hAo, hFl⟩ := hQ
  obtain ⟨-, -, -, -, -, -, hWi, -, -⟩ := harm hO hFt hT hAo hFl
  exact winv_reset (winv_emit (hWi es h) hem _).2 _

/-- **`ChainHeadW`**: a `match` whose arms dispatch into the next one is followed by a `match`
(else it fails to place, `chained_fail`); then `chainHead_match`. -/
theorem chainHeadW_of {Good : List Stmt → Prop} (hnew : PlaceNew ctx) (hok : OpOK Γ I Ag cl)
    (hI : I.Ok) (hmain : ctx.isMain = true → I.fp = 0) (hAg : AgOwn I Ag)
    (hkw : ∀ k, I.kw k = kwOf Γ k)
    (hsub : ∀ x arms rest, Good (.match_ x arms :: rest) → (∀ a ∈ arms, Good a) ∧ Good rest)
    (hfa : ∀ s rest, Good (s :: rest) → FaAfter I.σ s rest)
    (hu : ∀ x arms rest, Good (.match_ x arms :: rest) → x ∉ I.tmps)
    (hafa : ∀ x arms rest, Good (.match_ x arms :: rest) → ∀ j (hj : j < arms.length),
      ∀ v ∈ pathVals I.σ arms[j] (walk I.σ arms[j]), ∀ run,
        Atom.frameAddr v run ∉ armsAtoms (arms.drop (j + 1)))
    (hin : InBlockOf Γ Ag cl ctx I)
    (hopen : OpenW (Γ := Γ) (Ag := Ag) (cl := cl) (ctx := ctx) (I := I) Good)
    (hoff : OpenOffW (ctx := ctx)) :
    ChainHeadW (Γ := Γ) (Ag := Ag) (cl := cl) (ctx := ctx) (I := I) Good := by
  intro x arms rest tl hg ih C C₂ st st₂ sc s₀ s₁ sc' sc'' i₀ p₀ o hinv h₀ hx hsa hem hsc hw hns
    hes hcl hn₂ _ hE₂ hpk₂ hr₂ hf₂ hvw₂ hrb₂ hloc₂ hch₂ hz₂
  obtain ⟨harms, hrest⟩ := hsub x arms rest hg
  have hin' : ∀ j (hj : j < arms.length), InBlockW Γ Ag cl ctx I arms[j] := fun j hj =>
    hin _ fun tl' => ih _ (harms _ (List.getElem_mem hj)) (sizeOf_arm_lt (List.getElem_mem hj)) tl'
  cases rest with
  | nil => exact fun _ => chained_fail fun _ _ _ h => nomatch h
  | cons s rest' =>
    cases s with
    | match_ x' arms' =>
      have ih' : BlockIH Γ Ag cl ctx I Good (.match_ x' arms' :: rest') := fun ss' hg' hs tl' =>
        ih ss' hg' (lt_trans hs (by simp only [List.cons.sizeOf_spec]; omega)) tl'
      exact chainHead_match hnew hok hI hmain hAg hkw hopen hoff (hu x arms _ hg) hrest ih'
        (hfa _ _ hg) hin' (hafa x arms _ hg) hinv h₀ hx hsa hem hsc hw hns hes hcl hn₂ hE₂ hpk₂
        hr₂ hf₂ hvw₂ hrb₂ hloc₂ hch₂ hz₂
    | atom a => exact fun _ => chained_fail fun _ _ _ h => nomatch h
    | ite c z nz => exact fun _ => chained_fail fun _ _ _ h => nomatch h
    | _ => exact fun _ => chained_fail fun _ _ _ h => nomatch h

end Head

/-! ## The chains of a body -/

/-- **A body's blocks entered by an open chain** (owed: `openW_of`, CplFramePrims4). -/
def OpenBody : Prop := AtBody fun W tf pf fp hdr σ es kfps =>
  OpenW (Γ := World.cplSite W tf.core.name)
    (Ag := agK W tf pf fp hdr es kfps (instK W tf pf fp hdr σ es kfps)) (cl := calls es)
    (ctx := ctxOf (loopTable W.p) (sigTable W.p) tf) (I := instK W tf pf fp hdr σ es kfps)
    (InBody tf.core.body)

/-- **A body's chains of `match`es**, from its blocks entered by an open chain. -/
theorem chainBody_of (hopen : OpenBody) : ChainBody := by
  intro κ₀ W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd
  have hI := instK_ok (kfps := kfps) hW htf hpa hta hrd
  have hok := opOK_K (kfps := kfps) hW htf hpa hsc hta hw hrd
  have hfresh := hta.fresh
  exact chainHeadW_of placeNew_ok hok hI (fun h => hfp (by simpa [ctxOf] using h)) agOwn_K
    (fun _ => rfl) (fun x arms rest hg => ⟨fun a ha => .arm hg ha, .tail hg⟩)
    (faBody W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd)
    (fun x arms rest hin ht => (hfresh.2 x ht).1 (inBody_uses hin x (by simp [Stmt.uses])))
    (aFaBody W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd)
    (inBlockOf hok hI) (hopen W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd)
    (openOffW placeMono)

/-- **The frame side's statement**, from the blocks entered by an open chain. -/
theorem frameWords_of_open (hopen : OpenBody) : FrameWordsStmt :=
  frameWords_of_fa_chain faBody aFaBody (chainBody_of hopen)

/-- info: 'LeanVM.Guest.Backend.Complete.frameWords_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frameWords_of_open


end

end LeanVM.Guest.Backend.Complete
