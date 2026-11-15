/-
  LeanVM.Guest.Backend.Complete.FrameIte

  A branch statement on the path, from its inner blocks.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameEdge
public import LeanVM.Guest.Backend.Complete.FrameMatch
public import LeanVM.Guest.Backend.Complete.FramePool

/-!
# A branch on the path

`stmtW_ite : IteStmt`: the branch's edge flush (`winv_edge`), the condition's cell, the frame
pointer, the pooled `1`, the cell of the `else` target (whose word is the `SET` the final
placement has at the branch's position, `setW`), then the block the condition picks on the path
(`InBlockW`) and the other off it (`InBlockOff`, `winv_past`), the `emit`, the statement. Its words
(`blkW_iteZ`, `blkW_iteN`): the `SET` of the target, the `JUMP` on the condition, the picked
block's words at its position.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The scope walk of a branch -/

section Scope

theorem scopeIte_inv {rc : ℕ} {c : V} {z nz : List Stmt} {s s' : SSt}
    (h : scopeStmt rc (.ite c z nz) s = .ok s') : ∃ s₀ s₁, flushEdge rc s = .ok s₀ ∧
      s₀.live.contains c = true ∧ scopeInner rc (fun s' => scopeBlock rc z s') s₀ = .ok s₁ ∧
      scopeIteTail nz.isEmpty (scopeInner rc (fun s' => scopeBlock rc nz s')) s₀.retDone s₁ =
        .ok s' := by
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
  · next hc => simpa [inScope] using hc
  · cases hn

theorem scopeIteTail_inv {e : Bool} {nz : SSt → Except String SSt} {b : Bool} {s₁ s' : SSt}
    (h : scopeIteTail e nz b s₁ = .ok s') :
    (∃ r s₂, s₁.rest = .enter :: r ∧ nz { s₁ with retDone := b } = .ok s₂ ∧
      expectS isEmit "a branch" { s₂ with retDone := s₁.retDone || s₂.retDone } = .ok s') ∨
    ((∀ r, s₁.rest ≠ .enter :: r) ∧ e = true ∧ expectS isEmit "a branch" s₁ = .ok s') := by
  unfold scopeIteTail at h
  split at h
  · next r hr =>
    split at h
    · cases h
    · next s₂ h₂ => exact Or.inl ⟨r, s₂, hr, h₂, h⟩
  · next hne =>
    split at h
    · cases h
    · next he => exact Or.inr ⟨fun r hr => hne r hr, by simpa using he, h⟩

theorem flushS_retDone (rc : ℕ) : ∀ (rs : List Event) (live : VMap Unit) (r : Bool) (s₁ : SSt),
    flushS rc rs live r = .ok s₁ → r = true → s₁.retDone = true
  | [], _, _, s₁, h, hr => by
    simp only [flushS, Except.ok.injEq] at h
    subst h
    exact hr
  | e :: es, live, r, s₁, h, hr => by
    have ih : ∀ l r', flushS rc es l r' = .ok s₁ → r' = true → s₁.retDone = true :=
      fun l r' h' hr' => flushS_retDone rc es l r' s₁ h' hr'
    cases e <;> simp only [flushS] at h <;> (try split at h) <;>
      first
        | (cases h; done)
        | (cases h; exact hr)
        | exact ih _ _ h hr

mutual
/-- **A path's return area stays made** through a block of the scope walk. -/
theorem scopeBlock_retDone (rc : ℕ) : ∀ (ss : List Stmt) (s s' : SSt),
    scopeBlock rc ss s = .ok s' → s.retDone = true → s'.retDone = true
  | [], s, s', h, hr => by
    simp only [scopeBlock] at h
    cases h
    exact hr
  | st :: rest, s, s', h, hr => by
    simp only [scopeBlock] at h
    split at h
    · cases h
    · next s₁ h₁ => exact scopeBlock_retDone rc rest s₁ s' h (scopeStmt_retDone rc st s s₁ h₁ hr)

theorem scopeStmt_retDone (rc : ℕ) : ∀ (st : Stmt) (s s' : SSt),
    scopeStmt rc st s = .ok s' → s.retDone = true → s'.retDone = true
  | .ite c z nz, s, s', h, hr => by
    obtain ⟨s₀, s₁, h₀, -, h₁, ht⟩ := scopeIte_inv h
    have r₀ : s₀.retDone = true := flushS_retDone rc _ _ _ _ (flushEdge_ok h₀).2 hr
    obtain ⟨t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄, rfl⟩ := scopeInner_inv h₁
    obtain ⟨_, _, _, _, d₁⟩ := expectS_ok e₁
    obtain ⟨_, _, _, _, d₄⟩ := expectS_ok e₄
    have r₂ : t₂.retDone = true := scopeBlock_retDone rc z t₁ t₂ e₂ (by rw [d₁]; exact r₀)
    have r₃ : t₃.retDone = true := flushS_retDone rc _ _ _ _ (flushEdge_ok e₃).2 r₂
    have r₁ : ({ t₄ with live := s₀.live } : SSt).retDone = true := by
      show t₄.retDone = true
      rw [d₄]
      exact r₃
    rcases scopeIteTail_inv ht with ⟨r, s₂, -, -, he⟩ | ⟨-, -, he⟩
    · obtain ⟨_, _, _, _, hd⟩ := expectS_ok he
      rw [hd]
      simp only [Bool.or_eq_true]
      exact Or.inl (show t₄.retDone = true by rw [d₄]; exact r₃)
    · obtain ⟨_, _, _, _, hd⟩ := expectS_ok he
      rw [hd]
      exact r₁
  | .match_ x arms, s, s', h, hr => by
    simp only [scopeStmt] at h
    split at h
    · cases h
    next s₀ h₀ =>
    split at h
    · cases h
    split at h
    · cases h
    next s₁ h₁ =>
    obtain ⟨_, _, _, _, hd⟩ := expectS_ok h
    rw [hd]
    exact scopeArms_retDone rc arms s₀ s₀.retDone s₁ h₁
      (flushS_retDone rc _ _ _ _ (flushEdge_ok h₀).2 hr)
  | .atom a, s, s', h, hr => by
    obtain ⟨s₁, hfl, -, -, hd₁, -⟩ := scopeFlat_inv h
    rw [hd₁]
    exact flushS_retDone rc _ _ _ _ hfl hr
  | .call f args rets, s, s', h, hr => by
    obtain ⟨s₁, hfl, -, -, hd₁, -⟩ := scopeFlat_inv h
    rw [hd₁]
    exact flushS_retDone rc _ _ _ _ hfl hr
  | .callIf c f args, s, s', h, hr => by
    obtain ⟨s₁, hfl, -, -, hd₁, -⟩ := scopeFlat_inv h
    rw [hd₁]
    exact flushS_retDone rc _ _ _ _ hfl hr
  | .dispatch x fs args rets, s, s', h, hr => by
    obtain ⟨s₁, hfl, -, -, hd₁, -⟩ := scopeFlat_inv h
    rw [hd₁]
    exact flushS_retDone rc _ _ _ _ hfl hr
  | .ret vs, s, s', h, hr => by
    obtain ⟨s₁, hfl, -, -, hd₁, -⟩ := scopeFlat_inv h
    rw [hd₁]
    exact flushS_retDone rc _ _ _ _ hfl hr
end

theorem scopeInner_retDone {rc : ℕ} {b : List Stmt} {s s' : SSt}
    (h : scopeInner rc (fun s' => scopeBlock rc b s') s = .ok s') (hr : s.retDone = true) :
    s'.retDone = true := by
  obtain ⟨t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄, rfl⟩ := scopeInner_inv h
  obtain ⟨_, _, _, _, d₁⟩ := expectS_ok e₁
  obtain ⟨_, _, _, _, d₄⟩ := expectS_ok e₄
  show t₄.retDone = true
  rw [d₄]
  exact flushS_retDone rc _ _ _ _ (flushEdge_ok e₃).2
    (scopeBlock_retDone rc b t₁ t₂ e₂ (by rw [d₁]; exact hr))

/-- No frame address of an inner block is of a value in scope at its start. -/
theorem inner_live_fa {rc : ℕ} {b : List Stmt} {s s' : SSt}
    (h : scopeInner rc (fun s' => scopeBlock rc b s') s = .ok s') :
    ∀ v run, s.live.contains v = true → Atom.frameAddr v run ∉ atomsIn b := by
  intro v run hv hm
  obtain ⟨t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄, rfl⟩ := scopeInner_inv h
  obtain ⟨_, _, _, hl, _⟩ := expectS_ok e₁
  have := scopeBlock_fa rc b t₁ t₂ e₂ v run hm
  rw [hl, hv] at this
  cases this

/-- The value of a frame address of an inner block is made by the trace at its start. -/
theorem inner_made {rc : ℕ} {b : List Stmt} {s s' : SSt}
    (h : scopeInner rc (fun s' => scopeBlock rc b s') s = .ok s') :
    ∀ v run, Atom.frameAddr v run ∈ atomsIn b → v ∈ allocsOf s.rest := by
  intro v run hm
  obtain ⟨t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄, rfl⟩ := scopeInner_inv h
  obtain ⟨pre, hpre, hp⟩ := made_trans (Cons.suf (rc := rc) (expectS_cons noAlloc_enter e₁))
    (scopeBlock_made rc b t₁ t₂ e₂ v run hm)
    (Cons.suf ((flushAt_cons (flushEdge_ok e₃).2).trans
      (expectS_cons (s' := t₄) noAlloc_leave e₄)))
  rw [hpre, allocsOf_append]
  exact List.mem_append_left _ hp

end Scope

/-! ## The words of a branch -/

section Words

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Backend.Ctx} {I : Inst}

/-- Instructions at a position of the final placement end within it. -/
theorem OpsIn.len {p : ℕ} {ops : List LOp} (h : OpsIn I p ops) (hne : ops ≠ []) :
    p + ops.length ≤ I.ops.length := by
  have hl : ops.length - 1 < ops.length := by
    cases ops with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have h2 := (List.getElem?_eq_some_iff.mp (h _ hl)).1
  omega

/-- The word of the `SET` the final placement has at the absolute position `pos`. -/
def setW (I : Inst) (pos : ℕ) : E :=
  match I.ops[pos]? with
  | some (.set _ k) => I.kw k
  | _ => 0

theorem setW_of {pos o : ℕ} {k : KVal} (h : I.ops[pos]? = some (.set o k)) :
    setW I pos = I.kw k := by
  unfold setW
  rw [h]

/-- A branch's instructions: the `SET` of the `else` target, the `JUMP`, the `zero` block, and
with an `else` block its exit's `SET` and `JUMP` and the block. -/
theorem opsIn_ite {pos : ℕ} {h : List LHint} {lc bdest sfp edest one : ℕ} {zb nb : List PStmt}
    {e : Bool} (hO : OpsIn I pos (stmtOps (.ite h lc bdest sfp zb e edest one nb) pos)) :
    I.ops[pos]? = some (.set bdest (.local (elseAt pos zb e))) ∧ LOp.jump lc bdest sfp ∈ I.ops ∧
    OpsIn I (pos + 2) (blockOps zb (pos + 2)) ∧
    (e = true → I.ops[pos + 2 + blockSize zb]? =
        some (.set edest (.local (elseAt pos zb e + blockSize nb))) ∧
      LOp.jump one edest sfp ∈ I.ops ∧ OpsIn I (elseAt pos zb e) (blockOps nb (elseAt pos zb e))) := by
  simp only [stmtOps] at hO
  have hL := hO.left
  have h0 := hO 0 (by simp)
  refine ⟨by simpa using h0, hO.mem _ (by simp), ?_, fun he => ?_⟩
  · have := hL.right
    simpa using this
  · subst he
    have hR := hO.right
    simp only [↓reduceIte, List.length_append, blockOps_length, List.length_cons,
      List.length_nil] at hR
    have e1 : pos + (0 + 1 + 1 + blockSize zb) = pos + 2 + blockSize zb := by omega
    rw [e1] at hR
    have hR0 := hR 0 (by simp)
    have hRr := hR.right
    have e2 : pos + 2 + blockSize zb + [LOp.set edest (.local (elseAt pos zb true + blockSize nb)),
        LOp.jump one edest sfp].length = elseAt pos zb true := by simp [elseAt]
    rw [e2] at hRr
    exact ⟨by simpa using hR0, hR.mem _ (by simp), hRr⟩

theorem fillsIn_ite {pos : ℕ} {h : List LHint} {lc bdest sfp edest one : ℕ} {zb nb : List PStmt}
    {e : Bool} (hF : FillsIn Γ Ag pos [.ite h lc bdest sfp zb e edest one nb]) :
    FillsIn Γ Ag (pos + 2) zb ∧ (e = true → FillsIn Γ Ag (elseAt pos zb e) nb) :=
  ⟨fun f k i hm => hF f k i (by simp [blockFills, stmtFills, hm]),
    fun he f k i hm => hF f k i (by subst he; simp [blockFills, stmtFills, hm])⟩

/-- A branch's events make no call but the picked block's. -/
theorem calls_inK {ob : Out} {c : V} (hns : ob ≠ .stuck) :
    calls (outEs (ob.pre [.inK c])) = calls (outEs ob) := by
  rw [outEs_pre hns, calls_append']
  simp [calls, Ev.call?]

/-- What follows the picked block of a branch is what follows the branch. -/
theorem outK_ite {ob : Out} {c : V} {tl : List Stmt} {next : List Stmt → List (ℕ × ℕ) → Prop}
    {K : Prop} {ks : List (ℕ × ℕ)} {Q : List (ℕ × ℕ) → Prop} (hns : ob ≠ .stuck)
    (h : OutK (ob.pre [.inK c]) tl next K ks) (hQ : ∀ ks', next tl ks' → Q ks') :
    OutK ob [] (fun _ ks' => Q ks') K ks := by
  cases ob with
  | fall es =>
    intro cs' _
    have h' : next tl (ks.drop (calls ([Ev.inK c] ++ es)).length) := h tl rfl
    have hc : calls ([Ev.inK c] ++ es) = calls es := rfl
    rw [hc] at h'
    exact hQ _ h'
  | ret es vs => exact h
  | stuck => exact absurd rfl hns

/-- The values a branch's path reads: its condition and the picked block's. -/
theorem pathVals_ite {σ : Val} {c : V} {z nz : List Stmt} {ob : Out} (hns : ob ≠ .stuck) :
    ∀ v ∈ pathVals σ [.ite c z nz] (ob.pre [.inK c]),
      v ∈ [c] ++ pathVals σ (if σ c = 0 then z else nz) ob := by
  intro v hv
  have hsel : pathSels σ [Stmt.ite c z nz] = sels1 σ (.ite c z nz) := by
    simp only [pathSels]
    split <;> simp
  have hr : retVals (ob.pre [.inK c]) = retVals ob := by
    cases ob <;> simp [Out.pre, retVals]
  simp only [pathVals, outEs_pre hns, hsel, hr, sels1] at hv ⊢
  by_cases h : σ c = 0 <;> simp_all [Ev.uses]

/-- The frame words of a branch's condition, `else` target and frame pointer cells. -/
theorem ite_fwd (hI : I.Ok) (hkw : ∀ k, I.kw k = kwOf Γ k) {C : (ℕ → E) → Prop}
    {Ψ : ℕ → E} (hΨ : C Ψ) (σ' : Val) (kh : ℕ → E × E) {c : V} {lc bdest sfp pos q : ℕ}
    (hjmp : LOp.jump lc bdest sfp ∈ I.ops) (hset : I.ops[pos]? = some (.set bdest (.local q)))
    (hlc : 2 ≤ lc ∧ lc < I.size ∧ ∀ Ψ, C Ψ → Ψ lc = I.σ c)
    (hbd : 2 ≤ bdest ∧ bdest < I.size ∧ ∀ Ψ, C Ψ → Ψ bdest = setW I pos)
    (hsf : 2 ≤ sfp ∧ sfp < I.size ∧ ∀ Ψ, C Ψ → Ψ sfp = I.fpw) :
    fwd I.hdr ⟨patchT I Ψ σ', kh⟩ lc = I.σ c ∧
      fwd I.hdr ⟨patchT I Ψ σ', kh⟩ bdest = kwOf Γ (.local q) ∧
      fwd I.hdr ⟨patchT I Ψ σ', kh⟩ sfp = ofK (addressOfIndex I.fp) :=
  ⟨(fwd_patchT hlc.1 (not_tc_of hI hjmp (by simp [opCells]) fun _ h => nomatch h)).trans
      (hlc.2.2 Ψ hΨ),
    (fwd_patchT hbd.1 (not_tc_of hI hjmp (by simp [opCells]) fun _ h => nomatch h)).trans
      ((hbd.2.2 Ψ hΨ).trans ((setW_of hset).trans (hkw _))),
    (fwd_patchT hsf.1 (not_tc_of hI hjmp (by simp [opCells]) fun _ h => nomatch h)).trans
      (hsf.2.2 Ψ hΨ)⟩

/-- **The words of a branch whose condition is `0`**: the `SET` of the `else` target, the `JUMP`
falling through into the `zero` block's words, then (with an `else` block) the exit's `SET` and
`JUMP` past the `else` block. -/
theorem blkW_iteZ (hI : I.Ok) (hAg : AgOwn I Ag) (hkw : ∀ k, I.kw k = kwOf Γ k)
    (hlocB : ∀ q, q ≤ I.ops.length → kwOf Γ (.local q) = Γ.tgt q)
    {C : (ℕ → E) → Prop} {c : V} {z nz rest tl : List Stmt} {i₀ pos : ℕ}
    {h : List LHint} {lc bdest sfp edest one : ℕ} {zb nb : List PStmt} {e : Bool}
    (hσ0 : I.σ c = 0) (hu : c ∉ I.tmps) (hcK : IsInK (I.σ c)) (hns : walk I.σ z ≠ .stuck)
    (hbz : BlkW Γ I ctx Ag cl C zb z [] (walk I.σ z) i₀ (pos + 2))
    (hO : OpsIn I pos (stmtOps (.ite h lc bdest sfp zb e edest one nb) pos))
    (hlc : 2 ≤ lc ∧ lc < I.size ∧ ∀ Ψ, C Ψ → Ψ lc = I.σ c)
    (hbd : 2 ≤ bdest ∧ bdest < I.size ∧ ∀ Ψ, C Ψ → Ψ bdest = setW I pos)
    (hsf : 2 ≤ sfp ∧ sfp < I.size ∧ ∀ Ψ, C Ψ → Ψ sfp = I.fpw)
    (hel : e = true → (2 ≤ edest ∧ edest < I.size ∧
      ∀ Ψ, C Ψ → Ψ edest = setW I (pos + 2 + blockSize zb)) ∧
      (2 ≤ one ∧ one < I.size ∧ ∀ Ψ, C Ψ → Ψ one = 1)) :
    BlkW Γ I ctx Ag cl C [.ite h lc bdest sfp zb e edest one nb] [.ite c z nz] (rest ++ tl)
      ((walk I.σ z).pre [.inK c]) i₀ pos := by
  obtain ⟨hset, hjmp, -, hOe⟩ := opsIn_ite hO
  obtain ⟨hs, hl, hh, hW⟩ := hbz
  have hcalls := calls_inK (c := c) hns
  refine ⟨hs, by rw [hcalls]; exact hl, by rw [hcalls]; exact hh,
    fun hp Ψ hΨ σ' hσ kh cs ks next kj kret khalt hbo hcs hks hk => ?_⟩
  have hcs' : ctrlSplit cs = some (.ite c z nz, rest ++ tl) := by rw [hcs]; rfl
  have hr : Rds (Ag σ' Ψ kh) I.fp I.size (fwd I.hdr ⟨patchT I Ψ σ', kh⟩) :=
    fun κ L hL n hn => hAg σ' Ψ kh κ L hL n hn
  obtain ⟨hfc, hfb, hfs⟩ := ite_fwd hI hkw hΨ σ' kh hjmp hset hlc hbd hsf
  have hlen : pos + stmtSize (.ite h lc bdest sfp zb e edest one nb) ≤ I.ops.length := by
    have := hO.len (by simp [stmtOps])
    rwa [stmtOps_length] at this
  have hloc₀ := hlocB (elseAt pos zb e) (by
    unfold elseAt
    unfold stmtSize at hlen
    cases e <;> simp at hlen ⊢ <;> omega)
  simp only [wLc, wS, hcs']
  refine ⟨set_hw hr hbd.2.1 hfb, jw_of hr hlc.2.1 hbd.2.1 hsf.2.1
    (by rw [hfc]; exact hcK) (by rw [hfb, hloc₀]; exact isInK_ofK _)
    (by rw [hfs]; exact isInK_ofK _) (fun _ => ⟨by rw [hσ c hu, hσ0], ?_⟩)
    (fun h0 => absurd (hfc.trans hσ0) h0)⟩
  rw [wL_eq_wLc]
  refine hW hp Ψ hΨ σ' hσ kh z ks _ _ kret khalt (fun o' ho => hbo o' ?_)
    (by rw [List.append_nil]) (by rw [hcalls] at hks; exact hks) (outK_ite hns hk fun ks' hn => ?_)
  · simp [blockOps, stmtOps, ho]
  · cases e with
    | false => simpa using hn
    | true =>
      obtain ⟨hset', hjmp', -⟩ := hOe rfl
      obtain ⟨⟨he2, helt, hew⟩, ⟨ho2, holt, how⟩⟩ := hel rfl
      have hfe : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ edest =
          kwOf Γ (.local (elseAt pos zb true + blockSize nb)) :=
        (fwd_patchT he2 (not_tc_of hI hjmp' (by simp [opCells]) fun _ h => nomatch h)).trans
          ((hew Ψ hΨ).trans ((setW_of hset').trans (hkw _)))
      have hfo : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ one = 1 :=
        (fwd_patchT ho2 (not_tc_of hI hjmp' (by simp [opCells]) fun _ h => nomatch h)).trans
          (how Ψ hΨ)
      have hloc' := hlocB (elseAt pos zb true + blockSize nb) (by
        unfold elseAt
        unfold stmtSize at hlen
        simp at hlen ⊢
        omega)
      simp only [↓reduceIte]
      exact ⟨set_hw hr helt hfe, jw_of hr holt helt hsf.2.1
        (by rw [hfo]; exact (isInK_iff 1).mpr ⟨1, ofK_one.symm⟩)
        (by rw [hfe, hloc']; exact isInK_ofK _) (by rw [hfs]; exact isInK_ofK _)
        (fun h0 => absurd (hfo.symm.trans h0) one_ne_zero)
        fun _ => ⟨by rw [hfe, hloc'], hfs, hn⟩⟩

/-- **The words of a branch whose condition is not `0`**: the `SET` of the `else` target, the
`JUMP` to it, the `else` block's words there (or the join, without one). -/
theorem blkW_iteN (hI : I.Ok) (hAg : AgOwn I Ag) (hkw : ∀ k, I.kw k = kwOf Γ k)
    (hlocB : ∀ q, q ≤ I.ops.length → kwOf Γ (.local q) = Γ.tgt q)
    {C : (ℕ → E) → Prop} {c : V} {z nz rest tl : List Stmt} {i₀ pos : ℕ}
    {h : List LHint} {lc bdest sfp edest one : ℕ} {zb nb : List PStmt} {e : Bool}
    (hσ0 : I.σ c ≠ 0) (hu : c ∉ I.tmps) (hcK : IsInK (I.σ c)) (hns : walk I.σ nz ≠ .stuck)
    (hbn : e = true → BlkW Γ I ctx Ag cl C nb nz [] (walk I.σ nz) i₀ (elseAt pos zb e))
    (hne : e = false → nz = [])
    (hO : OpsIn I pos (stmtOps (.ite h lc bdest sfp zb e edest one nb) pos))
    (hlc : 2 ≤ lc ∧ lc < I.size ∧ ∀ Ψ, C Ψ → Ψ lc = I.σ c)
    (hbd : 2 ≤ bdest ∧ bdest < I.size ∧ ∀ Ψ, C Ψ → Ψ bdest = setW I pos)
    (hsf : 2 ≤ sfp ∧ sfp < I.size ∧ ∀ Ψ, C Ψ → Ψ sfp = I.fpw) :
    BlkW Γ I ctx Ag cl C [.ite h lc bdest sfp zb e edest one nb] [.ite c z nz] (rest ++ tl)
      ((walk I.σ nz).pre [.inK c]) i₀ pos := by
  obtain ⟨hset, hjmp, -, -⟩ := opsIn_ite hO
  have hcalls := calls_inK (c := c) hns
  have hlen : pos + stmtSize (.ite h lc bdest sfp zb e edest one nb) ≤ I.ops.length := by
    have := hO.len (by simp [stmtOps])
    rwa [stmtOps_length] at this
  have hloc₀ := hlocB (elseAt pos zb e) (by
    unfold elseAt
    unfold stmtSize at hlen
    cases e <;> simp at hlen ⊢ <;> omega)
  cases e with
  | true =>
    obtain ⟨hs, hl, hh, hW⟩ := hbn rfl
    refine ⟨hs, by rw [hcalls]; exact hl, by rw [hcalls]; exact hh,
      fun hp Ψ hΨ σ' hσ kh cs ks next kj kret khalt hbo hcs hks hk => ?_⟩
    have hcs' : ctrlSplit cs = some (.ite c z nz, rest ++ tl) := by rw [hcs]; rfl
    have hr : Rds (Ag σ' Ψ kh) I.fp I.size (fwd I.hdr ⟨patchT I Ψ σ', kh⟩) :=
      fun κ L hL n hn => hAg σ' Ψ kh κ L hL n hn
    obtain ⟨hfc, hfb, hfs⟩ := ite_fwd hI hkw hΨ σ' kh hjmp hset hlc hbd hsf
    simp only [wLc, wS, hcs']
    refine ⟨set_hw hr hbd.2.1 hfb, jw_of hr hlc.2.1 hbd.2.1 hsf.2.1
      (by rw [hfc]; exact hcK) (by rw [hfb, hloc₀]; exact isInK_ofK _)
      (by rw [hfs]; exact isInK_ofK _) (fun h0 => absurd (hfc.symm.trans h0) hσ0)
      fun _ => ⟨by rw [hσ c hu]; exact hσ0, by rw [hfb, hloc₀], hfs, ?_⟩⟩
    simp only [↓reduceIte]
    rw [wL_eq_wLc]
    exact hW hp Ψ hΨ σ' hσ kh nz ks _ _ kret khalt
      (fun o' ho => hbo o' (by simp [blockOps, stmtOps, ho])) (by rw [List.append_nil])
      (by rw [hcalls] at hks; exact hks) (outK_ite hns hk fun ks' hn => hn)
  | false =>
    obtain rfl := hne rfl
    refine ⟨[], by rw [hcalls]; rfl, HsOk.nil _ _ _,
      fun hp Ψ hΨ σ' hσ kh cs ks next kj kret khalt hbo hcs hks hk => ?_⟩
    have hcs' : ctrlSplit cs = some (.ite c z [], rest ++ tl) := by rw [hcs]; rfl
    have hr : Rds (Ag σ' Ψ kh) I.fp I.size (fwd I.hdr ⟨patchT I Ψ σ', kh⟩) :=
      fun κ L hL n hn => hAg σ' Ψ kh κ L hL n hn
    obtain ⟨hfc, hfb, hfs⟩ := ite_fwd hI hkw hΨ σ' kh hjmp hset hlc hbd hsf
    simp only [wLc, wS, hcs']
    refine ⟨set_hw hr hbd.2.1 hfb, jw_of hr hlc.2.1 hbd.2.1 hsf.2.1
      (by rw [hfc]; exact hcK) (by rw [hfb, hloc₀]; exact isInK_ofK _)
      (by rw [hfs]; exact isInK_ofK _) (fun h0 => absurd (hfc.symm.trans h0) hσ0)
      fun _ => ⟨by rw [hσ c hu]; exact hσ0, by rw [hfb, hloc₀], hfs, ?_⟩⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hk (rest ++ tl) rfl

end Words

/-! ## The branch statement -/

section Main

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Backend.Ctx} {I : Inst}

/-- **A branch's outcome** from the state after its cells (`st₆`, the invariant there once its
statements are final) to the state after it: the words of the instructions before the branch
and the branch's own, the condition's word read and the picked block's. -/
theorem iteOut (hok : OpOK Γ I Ag cl) {C₆ C' : (ℕ → E) → Prop} {st st₆ st' : St}
    {sc' s₀ : SSt} {c : V} {z nz b rest tl : List Stmt} {o ob : Out} {i₀ p₀ : ℕ} {X : PStmt}
    (hpv : ∀ v ∈ pathVals I.σ [.ite c z nz] o, v ∈ [c] ++ pathVals I.σ b ob)
    (hE : EmitsW I C₆ st st₆) (hs : Stronger C' C₆) (hn : st₆.next ≤ st'.next)
    (hl : LocsLe st₆.locs st'.locs) (ho : st'.out.toList = st₆.out.toList ++ [X])
    (hch : st'.chainIn = none) (hall : ∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st₆.rest)
    (hinv₆ : OutOps I st₆ → WInv ctx I C₆ st₆ s₀) (hc₀ : s₀.live.contains c = true)
    (hpc : st₆.locs[c]? ≠ none)
    (hWI : ∀ es, o = .fall es → FinAt Γ I Ag p₀ st' → WInv ctx I C' st' sc')
    (hBW : FinAt Γ I Ag p₀ st' → OutOps I st₆ →
      BlkW Γ I ctx Ag cl C' [X] [.ite c z nz] (rest ++ tl) o i₀ (p₀ + blockSize st₆.out.toList) ∧
      RW I C' st' (pathVals I.σ b ob)) :
    BlockOut Γ Ag cl ctx I st sc' [.ite c z nz] (rest ++ tl) o i₀ p₀ C' st' := by
  refine ⟨hWI, hch, fun hF => ?_⟩
  obtain ⟨ops, hops, hopsW⟩ := hE
  have hO₆ : OutOps I st₆ := fun h o' hm =>
    hF.2.1.outOps h o' (by rw [ho]; exact List.mem_append_left _ hm)
  have hF₆ : Fits I st₆ := hF.1.back hn hl
  have hinv₆' := hinv₆ hO₆
  obtain ⟨hbw, hrw⟩ := hBW hF hO₆
  refine ⟨ops ++ [X], by rw [ho, hops, List.append_assoc], ?_, ?_⟩
  · refine blkW_ops_X hok (fun s hs' => ?_) ?_
    · obtain ⟨h, o', rfl, hw⟩ := hopsW hF₆ hO₆ s hs'
      exact ⟨h, o', rfl, fun Ψ hΨ => hw Ψ (hs Ψ hΨ)⟩
    · have hpos : p₀ + blockSize st.out.toList + blockSize ops = p₀ + blockSize st₆.out.toList := by
        rw [Nat.add_assoc, ← bsize_append, ← hops]
      rw [hpos]
      exact hbw
  · have hcrw : RW I C' st' [c] := by
      intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      refine ⟨fun h => absurd (hinv₆'.fresh v (hall v h)).2 (by rw [hc₀]; simp),
        fun _ l hl' => ?_⟩
      obtain ⟨l₀, hl₀⟩ := Option.ne_none_iff_exists'.mp hpc
      have := hl v l₀ hl₀
      rw [hl'] at this
      cases this
      obtain ⟨b1, b2, b3⟩ := hinv₆'.vw v _ hc₀ hl₀
      exact ⟨b1, lt_of_lt_of_le b2 hn, fun Ψ hΨ => b3 Ψ (hs Ψ hΨ)⟩
    exact (hcrw.append hrw).anti hpv

local macro "comega" : tactic => `(tactic| ((try simp only [Cell] at *); omega))

set_option maxHeartbeats 4000000 in
/-- **A branch on the path** from its inner blocks. -/
theorem stmtW_ite (hok : OpOK Γ I Ag cl) (hI : I.Ok) (hmain : ctx.isMain = true → I.fp = 0)
    (hRd : ∀ rd, I.Rd rd → ∀ e ∈ I.es, evNT rd I.σ e) (hAg : AgOwn I Ag)
    (hkw : ∀ k, I.kw k = kwOf Γ k)
    (hlocB : ∀ q, q ≤ I.ops.length → kwOf Γ (.local q) = Γ.tgt q)
    {c : V} {z nz rest tl : List Stmt} (hu : c ∉ I.tmps)
    (hz : InBlockW Γ Ag cl ctx I z) (hnz : InBlockW Γ Ag cl ctx I nz) :
    StmtW Γ Ag cl ctx I (.ite c z nz) rest tl := by
  intro C st sc sc' i₀ p₀ o hsc _ hw hns hes hcl _ hinv
  obtain ⟨s₀, s₁, h₀, hc₀, h₁, ht⟩ := scopeIte_inv hsc
  obtain ⟨hlf, hfl₀⟩ := flushEdge_ok h₀
  have hwo : o = (if I.σ c = 0 then walk I.σ z else walk I.σ nz).pre [.inK c] := by
    rw [← hw]; rfl
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
    fun _ st₁ C₁ hs₁ hn₁ hl₁ _ hE₁ ⟨⟨hr₁, hFR₁, hrb₁, hloc₁⟩, hpk₁, hz₁, hk₁⟩ => ?_
  have hvw₁ : VW I C₁ st₁ fun v => s₀.live.contains v = true :=
    hFR₁.2.anti fun v hv => Or.inl (hokOf v hv)
  refine FBAt.fat_bind (FAt.and_wp (cellOf_fat c hI hvw₁ hc₀) (wp_and (cellOf_placed c)
      (wp_and cellOf_pk (wp_and cellOf_lz cellOf_keep))))
    fun lc st₂ C₂ hs₂ hn₂ hl₂ _ hE₂ ⟨⟨hlc2, hlclt, hlo₂, hr₂, hlcw, hkb₂⟩, hpl₂, hpk₂, hz₂, hk₂⟩ =>
      ?_
  have h2₂ : 2 ≤ st₂.next := le_trans hinv.two (le_trans hn₁ hn₂)
  refine FBAt.fat_bind (FAt.and_wp (selfFp_fat hI hmain h2₂)
      (wp_and selfFp_pk (wp_and selfFp_lz selfFp_keep)))
    fun sfp st₃ C₃ hs₃ hn₃ hl₃ _ hE₃ ⟨⟨hsf2, hsflt, hlo₃, hr₃, hsfw, hkb₃⟩, hpk₃, hz₃, hk₃⟩ => ?_
  unfold oneCell
  refine FBAt.fat_bind (FAt.and_wp (constCell_fatB (1, 0) (hI.kconst 1 0) (le_trans h2₂ hn₃))
      (wp_and constCell_pk (wp_and constCell_lz constCell_keep)))
    fun one st₄ C₄ hs₄ hn₄ hl₄ _ hE₄ ⟨⟨ho2, holt, hlo₄, hr₄, how, hkb₄⟩, hpk₄, hz₄, hk₄⟩ => ?_
  refine FBAt.fat_bind (FAt.and_wp (fresh_fat (fun _ => setW I (p₀ + blockSize st₄.out.toList))
      (wblind_const _ _)) (wp_and fresh_pk (wp_and fresh_lz fresh_keep)))
    fun bdest st₅ C₅ hs₅ hn₅ hl₅ _ hE₅ ⟨⟨hbd, hst₅, hC₅⟩, hpk₅, hz₅, hk₅⟩ => ?_
  refine FBAt.fat_bind (FAt.and_wp takeHints_fat
      (wp_and takeHints_pk (wp_and takeHints_lz takeHints_keep)))
    fun hints st₆ C₆ hs₆ hn₆ hl₆ hc₆ hE₆ ⟨⟨hC₆, hst₆⟩, hpk₆, hz₆, hk₆⟩ => ?_
  have hn6 : st₆.next = st₄.next + 1 := by rw [hst₆, hst₅]
  have hlo6 : st₆.locs = st₁.locs := by rw [hst₆, hst₅]; exact hlo₄.trans (hlo₃.trans hlo₂)
  have hr6 : st₆.rest = s₀.rest := by
    rw [hst₆, hst₅]; exact hr₄.trans (hr₃.trans (hr₂.trans hr₁))
  have hout6 : st₆.out = st₄.out := by rw [hst₆, hst₅]
  have hz6 : st₆.lazy = none := by
    rw [hz₆.1, hz₅.1, hz₄.1, hz₃.1, hz₂.1, hz₁]; exact hinv.lazy
  have hch6 : st₆.chainIn = none := by
    rw [hk₆, hk₅, hk₄, hk₃, hk₂, hk₁]; exact hinv.chain
  have hpk6 : PK st st₆ := hpk₁.trans (hpk₂.trans (hpk₃.trans (hpk₄.trans (hpk₅.trans hpk₆))))
  have hC6 : ∀ Ψ, C₆ Ψ → C₄ Ψ ∧ Ψ st₄.next = setW I (p₀ + blockSize st₆.out.toList) := by
    intro Ψ h
    rw [hC₆, hC₅] at h
    rw [hout6]
    exact h
  have hs16 : Stronger C₆ C₁ := fun Ψ h => hs₂ Ψ (hs₃ Ψ (hs₄ Ψ (hC6 Ψ h).1))
  have hn16 : st₁.next ≤ st₆.next := by
    have := hn₂; have := hn₃; have := hn₄; rw [hn6]; simp only [Cell] at *; comega
  have hE6 : EmitsW I C₆ st st₆ :=
    ((((hE₁.step hE₂ hs₂ hn₂ hl₂).step hE₃ hs₃ hn₃ hl₃).step hE₄ hs₄ hn₄ hl₄).step hE₅ hs₅ hn₅
      hl₅).step hE₆ hs₆ hn₆ hl₆
  have hkb6 : KeepB C₁ C₆ st₁.next :=
    ((hkb₂.trans hkb₃ hn₂).trans hkb₄ (le_trans hn₂ hn₃)).trans
      (fun c' hc' hb => by
        intro Ψ w h
        rw [hC₆, hC₅] at h ⊢
        exact blindAt_assign hb (Nat.ne_of_lt hc') Ψ w h)
      (le_trans hn₂ (le_trans hn₃ hn₄))
  have hpnt6 : OutOps I st₆ → PoolNT I st₆.scope := fun hO =>
    ⟨fun k o' hk => (hpk6.2.1 k o' hk).nt hI hinv.pnt hO,
      fun c' l hc' p hp => (hpk6.2.2 c' l hc' p hp).nt hI hinv.pnt hO⟩
  have hinv6 : OutOps I st₆ → WInv ctx I C₆ st₆ s₀ := fun hO =>
    winv_edge hinv h₀ hc₆ (le_trans hn₁ hn16) hr6 (hvw₁.step hs16 hn16 hlo6)
      (fun hr => RetBlind.keep (hrb₁ hr) (le_trans hinv.abi hn₁) hkb6)
      (fun v hv => hloc₁ v (by rw [← hlo6]; exact hv)) hch6 (hpnt6 hO) hz6
  have hf6 : st₆.rest.length ≤ ctx.fuel := by
    have h1 := hinv.fuel
    have h2 := congrArg List.length hseg
    rw [List.length_append] at h2
    rw [hr6]
    comega
  have hpc6 : st₆.locs[c]? ≠ none := by rw [hlo6]; exact hpl₂
  have hlc6 : 2 ≤ lc ∧ lc < st₆.next ∧ ∀ Ψ, C₆ Ψ → Ψ lc = I.σ c :=
    ⟨hlc2, by have := hn₃; have := hn₄; rw [hn6]; simp only [Cell] at *; comega,
      fun Ψ h => hlcw Ψ (hs₃ Ψ (hs₄ Ψ (hC6 Ψ h).1))⟩
  have hsf6 : 2 ≤ sfp ∧ sfp < st₆.next ∧ ∀ Ψ, C₆ Ψ → Ψ sfp = I.fpw :=
    ⟨hsf2, by have := hn₄; rw [hn6]; simp only [Cell] at *; comega,
      fun Ψ h => hsfw Ψ (hs₄ Ψ (hC6 Ψ h).1)⟩
  have hone6 : 2 ≤ one ∧ one < st₆.next ∧ ∀ Ψ, C₆ Ψ → Ψ one = 1 :=
    ⟨ho2, by rw [hn6]; simp only [Cell] at *; comega,
      fun Ψ h => (how Ψ (hC6 Ψ h).1).trans word_one⟩
  have hbd6 : 2 ≤ bdest ∧ bdest < st₆.next ∧
      ∀ Ψ, C₆ Ψ → Ψ bdest = setW I (p₀ + blockSize st₆.out.toList) :=
    ⟨by rw [hbd]; exact le_trans h2₂ (le_trans hn₃ hn₄), by rw [hbd, hn6]; exact Nat.lt_succ_self _,
      fun Ψ h => by rw [hbd]; exact (hC6 Ψ h).2⟩
  clear hC6 hst₅ hst₆ hC₅ hC₆
  obtain ⟨hlv₁, pre₁, hpre₁⟩ := scopeInner_live_rest h₁
  have hf₁ : s₁.rest.length ≤ ctx.fuel := by
    have := congrArg List.length hpre₁
    rw [List.length_append] at this
    rw [hr6] at hf6
    comega
  have hcK : IsInK (I.σ c) := by
    have hnsb : (if I.σ c = 0 then walk I.σ z else walk I.σ nz) ≠ .stuck := fun h =>
      hns (by rw [hwo, h]; rfl)
    obtain ⟨rd, hrd⟩ := hI.rd
    have := hRd rd hrd (.inK c) (hes _ (by
      rw [hwo, outEs_pre hnsb]; exact List.mem_append_left _ (List.mem_singleton_self _)))
    simpa [evNT, Ev.Holds] using this
  by_cases hσ0 : I.σ c = 0
  · -- the `zero` block on the path, the `else` block off it
    have hif : (if I.σ c = 0 then walk I.σ z else walk I.σ nz) = walk I.σ z := by simp [hσ0]
    rw [hif] at hwo
    have hnsz : walk I.σ z ≠ .stuck := fun h => hns (by rw [hwo, h]; rfl)
    have hpv := pathVals_ite (σ := I.σ) (c := c) (z := z) (nz := nz) hnsz
    simp only [hσ0, ↓reduceIte] at hpv
    rw [← hwo] at hpv
    have hesz : ∀ e ∈ outEs (walk I.σ z), e ∈ I.es := fun e he =>
      hes e (by rw [hwo, outEs_pre hnsz]; exact List.mem_append_right _ he)
    have hclz : ∀ j < (calls (outEs (walk I.σ z))).length,
        cl[i₀ + j]? = (calls (outEs (walk I.σ z)))[j]? := by
      rw [← calls_inK (c := c) hnsz, ← hwo]; exact hcl
    refine FBAt.bind (inBlock_fb hz (i₀ := i₀) (p₁ := p₀ + blockSize st₆.out.toList + 2) h₁ rfl
      hnsz hesz hclz hr6 hf6 hinv6) (fun _ _ _ h => h.1)
      fun zb st₇ C₇ hs₇ _ _ ⟨_, hoff₇, hW₇, _⟩ => ?_
    obtain ⟨hr₇, hsc₇, hout₇, hch₇, hn₇, hl₇, hnew₇, hall₇, htb₇⟩ := hoff₇
    obtain ⟨hz₇, -, -⟩ := hnew₇ hz6
    have hn67 : st₆.next ≤ st₇.next := hn₇
    refine FBAt.peek_bind ?_
    rcases scopeIteTail_inv ht with ⟨r, s₂, hrE, h₂, he⟩ | ⟨hne, hnzE, he⟩
    · rw [hr₇, hrE]
      simp only [List.head?_cons, bind_assoc]
      refine FBAt.fat_bind (fresh_fat
        (fun _ => setW I (p₀ + blockSize st₆.out.toList + 2 + blockSize zb)) (wblind_const _ _))
        fun edest st₈ C₈ hs₈ _ _ _ _ ⟨hed, hst₈, hC₈⟩ => ?_
      have hr₈ : st₈.rest = s₁.rest := by rw [hst₈]; exact hr₇
      have hf₈ : st₈.rest.length ≤ ctx.fuel := by rw [hr₈]; exact hf₁
      refine FBAt.bind (FBAt.offPath (wp_mono (inBlockOff_ok nz st₈ _ s₂ h₂ hr₈ hf₈)
        fun _ st' h => ⟨h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h⟩))
        (fun _ _ _ h => by rw [h.1]; exact h.2.1)
        fun nb st₉ C₉ _ _ _ ⟨hC₉, _, hoff₉⟩ => ?_
      obtain ⟨hr₉, hsc₉, hout₉, hch₉, hn₉, hl₉, hnew₉, hall₉, htb₉⟩ := hoff₉
      refine FBAt.bind (FBAt.offPath (Q := fun _ st' => st' = { st₉ with rest := st₉.rest.tail })
        (wp_mono expect_rest fun _ st' h => by subst h; exact ⟨rfl, le_rfl, LocsLe.refl _, rfl⟩))
        (fun _ _ _ h => by rw [h.1]; exact h.2.1) fun _ st₁₀ C₁₀ _ _ _ ⟨hC₁₀, _, hst₁₀⟩ => ?_
      refine push_end' fun _ => ?_
      subst C₁₀ C₉ hst₁₀
      have hz₈ : st₈.lazy = none := by rw [hst₈]; exact hz₇
      obtain ⟨hz₉, hnw₉, -⟩ := hnew₉ hz₈
      have hs86 : Stronger C₈ C₆ := fun Ψ h => hs₇ Ψ (by rw [hC₈] at h; exact h.1)
      have hn79 : st₇.next + 1 ≤ st₉.next := by rw [hst₈] at hn₉; exact hn₉
      have hl79 : LocsLe st₇.locs st₉.locs := by rw [hst₈] at hl₉; exact hl₉
      have hout9 : st₉.out = st₆.out := by rw [hout₉, hst₈]; exact hout₇
      have ho_end : (st₉.out.push (PStmt.ite hints lc bdest sfp zb true edest one nb)).toList =
          st₆.out.toList ++ [PStmt.ite hints lc bdest sfp zb true edest one nb] := by
        simp [hout9]
      have hch9 : st₉.chainIn = none := hch₉ (by rw [hst₈]; exact hch₇ hch6)
      have hall9 : ∀ v ∈ allocsOf st₉.rest.tail, v ∈ allocsOf st₆.rest := fun v hv =>
        hall₇ v (by rw [← hr₈.trans hr₇.symm]; exact hall₉ v (allocsOf_tail hv))
      refine iteOut hok hpv hE6 hs86 (by show st₆.next ≤ st₉.next; comega)
        (fun v x h => hl79 v x (hl₇ v x h)) ho_end hch9 hall9 hinv6 hc₀ hpc6
        (fun es hfa hF => ?_) (fun hF hO6 => ?_)
      · -- the invariant after the branch
        obtain ⟨es', hes'⟩ : ∃ es', walk I.σ z = .fall es' := by
          cases h : walk I.σ z with
          | fall es' => exact ⟨es', rfl⟩
          | ret _ _ => rw [hwo, h] at hfa; cases hfa
          | stuck => exact absurd h hnsz
        obtain ⟨hFt₇, hT₇, hOX, hFX⟩ := fin_ite (stb := st₇) hF ho_end (by show _ ≤ st₉.next; comega)
          hl79 (fun x hx => by rw [hst₈] at htb₉; exact htb₉ x hx)
        have hO6 : OutOps I st₆ := fun h o' hm =>
          hF.2.1.outOps h o' (by rw [ho_end]; exact List.mem_append_left _ hm)
        obtain ⟨-, -, hOz, -⟩ := opsIn_ite hOX
        obtain ⟨hFz, -⟩ := fillsIn_ite hFX
        obtain ⟨-, -, -, hWz, -⟩ := hW₇ hO6
        have W8 : WInv ctx I C₈ st₈ s₁ := by
          rw [hst₈, hC₈]
          exact (hWz es' hes' hFt₇ hOz hT₇ hFz).assign _
        have W9 := winv_past W8 (scopeInner_live_rest h₂).1 (scopeInner_live_rest h₂).2
          (fun v run hv => inner_live_fa h₂ v run hv) hr₉ hsc₉ hch₉ hn₉ hl₉ hnew₉
        obtain ⟨_, _, _, hlv', hrd'⟩ := expectS_ok he
        exact WInv.past W9 (by obtain ⟨ev, hev, hna⟩ := emit_past he; exact ⟨ev, hev, hna⟩) hlv'
          (fun h => by rw [hrd'] at h; exact (Bool.or_eq_false_iff.mp h).1) rfl rfl rfl
          (by obtain ⟨ev, hev, -⟩ := emit_past he; show st₉.rest.tail = _; rw [hr₉]; exact
            congrArg List.tail hev) rfl rfl
      · -- the words
        obtain ⟨hFt₇, hT₇, hOX, hFX⟩ := fin_ite (stb := st₇) hF ho_end (by show _ ≤ st₉.next; comega)
          hl79 (fun x hx => by rw [hst₈] at htb₉; exact htb₉ x hx)
        obtain ⟨-, -, hOz, -⟩ := opsIn_ite hOX
        obtain ⟨hFz, -⟩ := fillsIn_ite hFX
        obtain ⟨-, -, -, -, hBz⟩ := hW₇ hO6
        obtain ⟨hbz, hrz⟩ := hBz hFt₇ hOz hT₇ hFz
        have hsz : st₉.next ≤ I.size := hF.1.1
        have hs87 : Stronger C₈ C₇ := fun Ψ h => by rw [hC₈] at h; exact h.1
        have hX := blkW_iteZ (rest := rest) (tl := tl) (nz := nz) hI hAg hkw hlocB hσ0 hu hcK hnsz
          (hbz.mono hs87) hOX
          ⟨hlc6.1, by comega, fun Ψ h => hlc6.2.2 Ψ (hs86 Ψ h)⟩
          ⟨hbd6.1, by comega, fun Ψ h => hbd6.2.2 Ψ (hs86 Ψ h)⟩
          ⟨hsf6.1, by comega, fun Ψ h => hsf6.2.2 Ψ (hs86 Ψ h)⟩
          fun _ => ⟨⟨by rw [hed]; comega, by rw [hed]; comega, fun Ψ h => by
            rw [hC₈] at h; rw [hed]; exact h.2⟩,
            ⟨hone6.1, by comega, fun Ψ h => hone6.2.2 Ψ (hs86 Ψ h)⟩⟩
        rw [← hwo] at hX
        refine ⟨hX, ?_⟩
        refine hrz.grow hs87 (by comega) hl79 (fun v _ hp => ?_) (fun v hv => ?_)
        · rcases hnw₉ v hp with h | h | ⟨run, h⟩
          · exact Or.inl (by rw [hst₈] at h; exact h)
          · exact Or.inr (by rw [hst₈] at h; exact h)
          · exact Or.inr (by rw [hr₇]; exact inner_made h₂ v run h)
        · have := hall₉ v (allocsOf_tail hv)
          rw [hst₈] at this
          exact this
    · -- no `else` block
      have hnh : ∀ r, st₇.rest ≠ .enter :: r := by rw [hr₇]; exact hne
      have hnz0 : nz = [] := List.isEmpty_iff.mp hnzE
      split
      · next hh =>
        exfalso
        cases h : st₇.rest with
        | nil => rw [h] at hh; cases hh
        | cons ev r =>
          rw [h] at hh
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          exact hnh r h
      simp only [hnzE, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
      refine FBAt.bind (FBAt.offPath (Q := fun _ st' => st' = { st₇ with rest := st₇.rest.tail })
        (wp_mono expect_rest fun _ st' h => by subst h; exact ⟨rfl, le_rfl, LocsLe.refl _, rfl⟩))
        (fun _ _ _ h => by rw [h.1]; exact h.2.1) fun _ st₁₀ C₁₀ _ _ _ ⟨hC₁₀, _, hst₁₀⟩ => ?_
      refine push_end' fun _ => ?_
      subst C₁₀ hst₁₀
      have ho_end : (st₇.out.push (PStmt.ite hints lc bdest sfp zb false 0 0 [])).toList =
          st₆.out.toList ++ [PStmt.ite hints lc bdest sfp zb false 0 0 []] := by
        simp [hout₇]
      obtain ⟨_, hev, -⟩ := emit_past he
      refine iteOut hok hpv hE6 hs₇ hn67 hl₇ ho_end (hch₇ hch6)
        (fun v hv => hall₇ v (allocsOf_tail hv)) hinv6 hc₀ hpc6 (fun es hfa hF => ?_)
        (fun hF hO6 => ?_)
      · obtain ⟨es', hes'⟩ : ∃ es', walk I.σ z = .fall es' := by
          cases h : walk I.σ z with
          | fall es' => exact ⟨es', rfl⟩
          | ret _ _ => rw [hwo, h] at hfa; cases hfa
          | stuck => exact absurd h hnsz
        obtain ⟨hFt₇, hT₇, hOX, hFX⟩ := fin_ite (stb := st₇) hF ho_end le_rfl (LocsLe.refl _)
          fun _ hx => hx
        have hO6 : OutOps I st₆ := fun h o' hm =>
          hF.2.1.outOps h o' (by rw [ho_end]; exact List.mem_append_left _ hm)
        obtain ⟨-, -, hOz, -⟩ := opsIn_ite hOX
        obtain ⟨hFz, -⟩ := fillsIn_ite hFX
        obtain ⟨-, -, -, hWz, -⟩ := hW₇ hO6
        obtain ⟨_, _, _, hlv', hrd'⟩ := expectS_ok he
        exact WInv.past (hWz es' hes' hFt₇ hOz hT₇ hFz) (emit_past he) hlv'
          (fun h => by rw [← hrd']; exact h) rfl rfl rfl
          (by show st₇.rest.tail = _; rw [hr₇, hev]; rfl) rfl rfl
      · obtain ⟨hFt₇, hT₇, hOX, hFX⟩ := fin_ite (stb := st₇) hF ho_end le_rfl (LocsLe.refl _)
          fun _ hx => hx
        obtain ⟨-, -, hOz, -⟩ := opsIn_ite hOX
        obtain ⟨hFz, -⟩ := fillsIn_ite hFX
        obtain ⟨-, -, -, -, hBz⟩ := hW₇ hO6
        obtain ⟨hbz, hrz⟩ := hBz hFt₇ hOz hT₇ hFz
        have hsz : st₇.next ≤ I.size := hF.1.1
        have hX := blkW_iteZ (rest := rest) (tl := tl) (nz := nz) (edest := 0) (one := 0)
          (nb := []) hI hAg hkw hlocB hσ0 hu hcK hnsz hbz hOX
          ⟨hlc6.1, by comega, fun Ψ h => hlc6.2.2 Ψ (hs₇ Ψ h)⟩
          ⟨hbd6.1, by comega, fun Ψ h => hbd6.2.2 Ψ (hs₇ Ψ h)⟩
          ⟨hsf6.1, by comega, fun Ψ h => hsf6.2.2 Ψ (hs₇ Ψ h)⟩
          fun h => absurd h Bool.false_ne_true
        rw [← hwo] at hX
        exact ⟨hX, hrz.grow (Stronger.refl _) le_rfl (LocsLe.refl _) (fun _ _ h => Or.inl h)
          fun v hv => allocsOf_tail hv⟩
  · -- the `zero` block off the path, the `else` block (if any) on it
    have hif : (if I.σ c = 0 then walk I.σ z else walk I.σ nz) = walk I.σ nz := by simp [hσ0]
    rw [hif] at hwo
    have hnsn : walk I.σ nz ≠ .stuck := fun h => hns (by rw [hwo, h]; rfl)
    have hpv := pathVals_ite (σ := I.σ) (c := c) (z := z) (nz := nz) hnsn
    simp only [hσ0, ↓reduceIte] at hpv
    rw [← hwo] at hpv
    have hesn : ∀ e ∈ outEs (walk I.σ nz), e ∈ I.es := fun e he =>
      hes e (by rw [hwo, outEs_pre hnsn]; exact List.mem_append_right _ he)
    have hcln : ∀ j < (calls (outEs (walk I.σ nz))).length,
        cl[i₀ + j]? = (calls (outEs (walk I.σ nz)))[j]? := by
      rw [← calls_inK (c := c) hnsn, ← hwo]; exact hcl
    refine FBAt.bind (FBAt.offPath (wp_mono (inBlockOff_ok z st₆ s₀ s₁ h₁ hr6 hf6)
      fun _ st' h => ⟨h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h⟩))
      (fun _ _ _ h => by rw [h.1]; exact h.2.1) fun zb st₇ C₇ _ _ _ ⟨hC₇, _, hoff₇⟩ => ?_
    subst C₇
    obtain ⟨hr₇, hsc₇, hout₇, hch₇, hn₇, hl₇, hnew₇, hall₇, htb₇⟩ := hoff₇
    have hinv7 : OutOps I st₆ → WInv ctx I C₆ st₇ { s₁ with retDone := s₀.retDone } := fun hO =>
      winv_past (hinv6 hO) hlv₁ ⟨pre₁, hpre₁⟩ (fun v run hv => inner_live_fa h₁ v run hv) hr₇
        hsc₇ hch₇ hn₇ hl₇ hnew₇
    have hn67 : st₆.next ≤ st₇.next := hn₇
    refine FBAt.peek_bind ?_
    rcases scopeIteTail_inv ht with ⟨r, s₂, hrE, h₂, he⟩ | ⟨hne, hnzE, he⟩
    · rw [hr₇, hrE]
      simp only [List.head?_cons, bind_assoc]
      refine FBAt.fat_bind (fresh_fat
        (fun _ => setW I (p₀ + blockSize st₆.out.toList + 2 + blockSize zb)) (wblind_const _ _))
        fun edest st₈ C₈ hs₈ _ _ _ _ ⟨hed, hst₈, hC₈⟩ => ?_
      have hr₈ : st₈.rest = s₁.rest := by rw [hst₈]; exact hr₇
      have hf₈ : st₈.rest.length ≤ ctx.fuel := by rw [hr₈]; exact hf₁
      have hout8 : st₈.out = st₆.out := by rw [hst₈]; exact hout₇
      have hinv8 : OutOps I st₈ → WInv ctx I C₈ st₈ { s₁ with retDone := s₀.retDone } :=
        fun hO => by
          rw [hst₈, hC₈]
          exact (hinv7 fun h o' hm => hO h o' (by rw [hout8]; exact hm)).assign _
      refine FBAt.bind (inBlock_fb hnz (i₀ := i₀)
        (p₁ := elseAt (p₀ + blockSize st₆.out.toList) zb true) h₂ rfl hnsn hesn hcln hr₈ hf₈
        hinv8) (fun _ _ _ h => h.1) fun nb st₉ C₉ hs₉ _ _ ⟨_, hoff₉, hW₉, _⟩ => ?_
      obtain ⟨hr₉, hsc₉, hout₉, hch₉, hn₉, hl₉, hnew₉, hall₉, htb₉⟩ := hoff₉
      refine FBAt.bind (FBAt.offPath (Q := fun _ st' => st' = { st₉ with rest := st₉.rest.tail })
        (wp_mono expect_rest fun _ st' h => by subst h; exact ⟨rfl, le_rfl, LocsLe.refl _, rfl⟩))
        (fun _ _ _ h => by rw [h.1]; exact h.2.1) fun _ st₁₀ C₁₀ _ _ _ ⟨hC₁₀, _, hst₁₀⟩ => ?_
      refine push_end' fun _ => ?_
      subst C₁₀ hst₁₀
      have hs96 : Stronger C₉ C₆ := fun Ψ h => by
        have := hs₉ Ψ h
        rw [hC₈] at this
        exact this.1
      have hn79 : st₇.next + 1 ≤ st₉.next := by rw [hst₈] at hn₉; exact hn₉
      have hl79 : LocsLe st₇.locs st₉.locs := by rw [hst₈] at hl₉; exact hl₉
      have hout9 : st₉.out = st₆.out := by rw [hout₉]; exact hout8
      have ho_end : (st₉.out.push (PStmt.ite hints lc bdest sfp zb true edest one nb)).toList =
          st₆.out.toList ++ [PStmt.ite hints lc bdest sfp zb true edest one nb] := by
        simp [hout9]
      have hch9 : st₉.chainIn = none := hch₉ (by rw [hst₈]; exact hch₇ hch6)
      have hall9 : ∀ v ∈ allocsOf st₉.rest.tail, v ∈ allocsOf st₆.rest := fun v hv =>
        hall₇ v (by rw [← hr₈.trans hr₇.symm]; exact hall₉ v (allocsOf_tail hv))
      obtain ⟨_, hev, -⟩ := emit_past he
      refine iteOut hok hpv hE6 hs96 (by comega)
        (fun v x h => hl79 v x (hl₇ v x h)) ho_end hch9 hall9 hinv6 hc₀ hpc6
        (fun es hfa hF => ?_) (fun hF hO6 => ?_)
      · obtain ⟨es', hes'⟩ : ∃ es', walk I.σ nz = .fall es' := by
          cases h : walk I.σ nz with
          | fall es' => exact ⟨es', rfl⟩
          | ret _ _ => rw [hwo, h] at hfa; cases hfa
          | stuck => exact absurd h hnsn
        obtain ⟨hFt₉, hT₉, hOX, hFX⟩ := fin_ite (stb := st₉) hF ho_end le_rfl (LocsLe.refl _)
          fun _ hx => hx
        have hO6 : OutOps I st₆ := fun h o' hm =>
          hF.2.1.outOps h o' (by rw [ho_end]; exact List.mem_append_left _ hm)
        have hO8 : OutOps I st₈ := fun h o' hm => hO6 h o' (by rw [← hout8]; exact hm)
        obtain ⟨-, -, -, hOe⟩ := opsIn_ite hOX
        obtain ⟨-, hFn⟩ := fillsIn_ite hFX
        obtain ⟨-, -, -, hWn, -⟩ := hW₉ hO8
        obtain ⟨_, _, _, hlv', hrd'⟩ := expectS_ok he
        exact WInv.past (hWn es' hes' hFt₉ (hOe rfl).2.2 hT₉ (hFn rfl))
          (by obtain ⟨ev, hev', hna⟩ := emit_past he; exact ⟨ev, hev', hna⟩) hlv'
          (fun h => by rw [hrd'] at h; exact (Bool.or_eq_false_iff.mp h).2) rfl rfl rfl
          (by show st₉.rest.tail = _; rw [hr₉, hev]; rfl) rfl rfl
      · obtain ⟨hFt₉, hT₉, hOX, hFX⟩ := fin_ite (stb := st₉) hF ho_end le_rfl (LocsLe.refl _)
          fun _ hx => hx
        have hO8 : OutOps I st₈ := fun h o' hm => hO6 h o' (by rw [← hout8]; exact hm)
        obtain ⟨-, -, -, hOe⟩ := opsIn_ite hOX
        obtain ⟨-, hFn⟩ := fillsIn_ite hFX
        obtain ⟨-, -, -, -, hBn⟩ := hW₉ hO8
        obtain ⟨hbn, hrn⟩ := hBn hFt₉ (hOe rfl).2.2 hT₉ (hFn rfl)
        have hsz : st₉.next ≤ I.size := hF.1.1
        have hX := blkW_iteN (rest := rest) (tl := tl) (z := z) hI hAg hkw hlocB hσ0 hu hcK hnsn
          (fun _ => hbn) (fun h => nomatch h) hOX
          ⟨hlc6.1, by comega, fun Ψ h => hlc6.2.2 Ψ (hs96 Ψ h)⟩
          ⟨hbd6.1, by comega, fun Ψ h => hbd6.2.2 Ψ (hs96 Ψ h)⟩
          ⟨hsf6.1, by comega, fun Ψ h => hsf6.2.2 Ψ (hs96 Ψ h)⟩
        rw [← hwo] at hX
        exact ⟨hX, hrn.grow (Stronger.refl _) le_rfl (LocsLe.refl _) (fun _ _ h => Or.inl h)
          fun v hv => allocsOf_tail hv⟩
    · -- no `else` block
      have hnh : ∀ r, st₇.rest ≠ .enter :: r := by rw [hr₇]; exact hne
      have hnz0 : nz = [] := List.isEmpty_iff.mp hnzE
      split
      · next hh =>
        exfalso
        cases h : st₇.rest with
        | nil => rw [h] at hh; cases hh
        | cons ev r =>
          rw [h] at hh
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          exact hnh r h
      simp only [hnzE, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
      refine FBAt.bind (FBAt.offPath (Q := fun _ st' => st' = { st₇ with rest := st₇.rest.tail })
        (wp_mono expect_rest fun _ st' h => by subst h; exact ⟨rfl, le_rfl, LocsLe.refl _, rfl⟩))
        (fun _ _ _ h => by rw [h.1]; exact h.2.1) fun _ st₁₀ C₁₀ _ _ _ ⟨hC₁₀, _, hst₁₀⟩ => ?_
      refine push_end' fun _ => ?_
      subst C₁₀ hst₁₀
      have ho_end : (st₇.out.push (PStmt.ite hints lc bdest sfp zb false 0 0 [])).toList =
          st₆.out.toList ++ [PStmt.ite hints lc bdest sfp zb false 0 0 []] := by
        simp [hout₇]
      obtain ⟨_, hev, -⟩ := emit_past he
      refine iteOut hok hpv hE6 (Stronger.refl _) hn67 hl₇ ho_end (hch₇ hch6)
        (fun v hv => hall₇ v (allocsOf_tail hv)) hinv6 hc₀ hpc6 (fun es hfa hF => ?_)
        (fun hF hO6 => ?_)
      · have hO6 : OutOps I st₆ := fun h o' hm =>
          hF.2.1.outOps h o' (by rw [ho_end]; exact List.mem_append_left _ hm)
        obtain ⟨_, _, _, hlv', hrd'⟩ := expectS_ok he
        exact WInv.past (hinv7 hO6) (by obtain ⟨ev, hev', hna⟩ := emit_past he; exact ⟨ev, hev', hna⟩) hlv'
          (fun h => by
            rw [hrd'] at h
            cases h0 : s₀.retDone with
            | false => rfl
            | true => rw [scopeInner_retDone h₁ h0] at h; cases h) rfl rfl rfl
          (by show st₇.rest.tail = _; rw [hr₇, hev]; rfl) rfl rfl
      · have hsz : st₇.next ≤ I.size := hF.1.1
        obtain ⟨-, -, hOX, -⟩ := fin_ite (stb := st₇) hF ho_end le_rfl (LocsLe.refl _)
          fun _ hx => hx
        have hX := blkW_iteN (ctx := ctx) (cl := cl) (i₀ := i₀)
          (rest := rest) (tl := tl) (z := z) (nz := nz) (edest := 0) (one := 0)
          (nb := []) hI hAg hkw hlocB hσ0 hu hcK hnsn (fun h => absurd h Bool.false_ne_true)
          (fun _ => hnz0) hOX
          ⟨hlc6.1, by comega, fun Ψ h => hlc6.2.2 Ψ h⟩
          ⟨hbd6.1, by comega, fun Ψ h => hbd6.2.2 Ψ h⟩
          ⟨hsf6.1, by comega, fun Ψ h => hsf6.2.2 Ψ h⟩
        rw [← hwo] at hX
        refine ⟨hX, fun v hv => ?_⟩
        subst hnz0
        simp [pathVals, walk, outEs, retVals, pathSels] at hv

/-- **The branch statement** (`IteStmt`, for `bodyW`). -/
theorem iteStmt (hok : OpOK Γ I Ag cl) (hI : I.Ok) (hmain : ctx.isMain = true → I.fp = 0)
    (hRd : ∀ rd, I.Rd rd → ∀ e ∈ I.es, evNT rd I.σ e) (hAg : AgOwn I Ag)
    (hkw : ∀ k, I.kw k = kwOf Γ k)
    (hlocB : ∀ q, q ≤ I.ops.length → kwOf Γ (.local q) = Γ.tgt q) :
    IteStmt Γ Ag cl ctx I :=
  fun _ _ _ _ _ hu hz hnz => stmtW_ite hok hI hmain hRd hAg hkw hlocB hu hz hnz

end Main

end

end LeanVM.Guest.Backend.Complete
