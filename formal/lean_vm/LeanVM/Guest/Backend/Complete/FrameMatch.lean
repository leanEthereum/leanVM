/-
  LeanVM.Guest.Backend.Complete.FrameMatch

  A `match` on the path, with the chain of `match`es it starts.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameSelf
public import LeanVM.Guest.Backend.Complete.ScopedRet
public import LeanVM.Guest.Backend.Complete.FrameInner

/-!
# A `match` on the path

The words of a chain's stages (`wStages`, `wArms`) from the arm each stage's selector picks: that
arm's words at its position, the arms before it passed over (`wArms_pick`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The arm a selector picks -/

/-- **The arm `walkArms` runs**: the first arm `j` whose index the selector's word is. -/
theorem walkArms_pick {σ : Val} {x : V} : ∀ (arms : List (List Stmt)) (j₀ : ℕ),
    walkArms σ x j₀ arms ≠ .stuck → ∃ j, ∃ hj : j < arms.length,
      σ x = ofK (addressOfIndex (j₀ + j)) ∧ (∀ i < j, σ x ≠ ofK (addressOfIndex (j₀ + i))) ∧
      walkArms σ x j₀ arms = walk σ arms[j] ∧ armSels σ x j₀ arms = pathSels σ arms[j]
  | [], _, h => absurd (by simp [walkArms]) h
  | a :: as, j₀, h => by
    by_cases hx : σ x = ofK (addressOfIndex j₀)
    · exact ⟨0, by simp, by simpa using hx, fun _ h => absurd h (Nat.not_lt_zero _),
        by simp [walkArms, hx], by simp [armSels, hx]⟩
    · have h' : walkArms σ x (j₀ + 1) as ≠ .stuck := by simpa [walkArms, hx] using h
      obtain ⟨j, hj, h1, h2, h3, h4⟩ := walkArms_pick as (j₀ + 1) h'
      refine ⟨j + 1, by simp; omega, by rw [h1]; congr 2; omega, fun i hi => ?_,
        by simpa [walkArms, hx] using h3, by simpa [armSels, hx] using h4⟩
      cases i with
      | zero => simpa using hx
      | succ i =>
        have := h2 i (by omega)
        rwa [show j₀ + 1 + i = j₀ + (i + 1) by omega] at this

section Words

variable {κ₀ : ℕ} {Γ : Site κ₀} {fp : ℕ} {σ : Val} {hdr : E × E} {FS : FrameSpec}
  {Ag : (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}

/-- **Into the arm a stage's selector picks**: the jump lands on arm `j`'s first instruction, the
frame pointer kept, and the arm's words hold, its fall through jumping on past it. -/
theorem wArms_pick {xv : V} {kj : List (ℕ × ℕ) → E → E → Prop} {kret khalt : Prop}
    {ks : List (ℕ × ℕ)} {d f : E} : ∀ (pas : List (List PStmt)) (arms : List (List Stmt))
    (j₀ pos j : ℕ) (hj : j < pas.length) (ha : j < arms.length),
    σ xv = ofK (addressOfIndex (j₀ + j)) → (∀ i < j, σ xv ≠ ofK (addressOfIndex (j₀ + i))) →
    d = Γ.tgt (pos + armsSize (pas.take j)) → f = ofK (addressOfIndex fp) →
    wL Γ fp σ hdr FS Ag cl pas[j] arms[j] (pos + armsSize (pas.take j)) ks
      (fun ks' => kj ks' (Γ.tgt (pos + armsSize (pas.take j) + blockSize pas[j]))
        (ofK (addressOfIndex fp))) kj kret khalt →
    wArms Γ fp σ hdr FS Ag cl xv pas arms j₀ pos kj kret khalt ks d f
  | [], _, _, _, _, hj, _, _, _, _, _, _ => absurd hj (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, _, ha, _, _, _, _, _ => absurd ha (Nat.not_lt_zero _)
  | pa :: pas, a :: as, j₀, pos, 0, _, _, hx, _, hd, hf, hw => by
    simp only [Nat.add_zero] at hx
    simp only [List.take_zero, armsSize, Nat.add_zero] at hd hw
    rw [wArms]
    simp only [hx, ite_true]
    exact ⟨hd, hf, hw⟩
  | pa :: pas, a :: as, j₀, pos, j + 1, hj, ha, hx, hne, hd, hf, hw => by
    rw [wArms]
    have h0 : σ xv ≠ ofK (addressOfIndex j₀) := by simpa using hne 0 (Nat.succ_pos _)
    simp only [h0, ite_false]
    have e : pos + armsSize ((pa :: pas).take (j + 1)) =
        pos + blockSize pa + armsSize (pas.take j) := by
      simp only [List.take_succ_cons, armsSize]; omega
    refine wArms_pick pas as (j₀ + 1) (pos + blockSize pa) j (by simpa using hj)
      (by simpa using ha) (by rw [hx]; congr 2; omega) (fun i hi => ?_) (by rw [hd, e])
      hf (by rw [e] at hw; simpa using hw)
    have := hne (i + 1) (by omega)
    rwa [show j₀ + (i + 1) = j₀ + 1 + i by omega] at this

variable (Γ fp hdr FS Ag) in
/-- A `JUMP` to the instruction `t` of the function, the frame kept, whatever it falls into. -/
def JumpTo (oc od of t : ℕ) : Prop :=
  ∀ (fall : Prop) (taken : E → E → Prop), taken (Γ.tgt t) (ofK (addressOfIndex fp)) →
    JW fp hdr FS Ag oc od of fall taken

/-- **The words of a one-stage chain** (a `match` whose arms jump to the join): the join's `SET`,
the table read at the selector and the jump into the picked arm `j`, whose words (`wL`) end by
going on at the join with the statements after the `match`. -/
theorem wS_chain1 {h : List LHint} {join lx entry one sfp first : ℕ}
    {blocks : List (List PStmt)} {cs rest : List Stmt} {xv : V} {arms : List (List Stmt)}
    {pos : ℕ} {ks : List (ℕ × ℕ)} {next : List Stmt → List (ℕ × ℕ) → Prop}
    {kj : List (ℕ × ℕ) → E → E → Prop} {kret khalt : Prop}
    (hcs : ctrlSplit cs = some (.match_ xv arms, rest))
    (hset : HW Γ fp Ag (Γ.pc0 + pos) (.set join (.local (pos + 3 + armsSize blocks))))
    (hslot : HW Γ fp Ag (Γ.pc0 + pos + 1) (.slot lx first entry))
    (j : ℕ) (hj : j < blocks.length) (ha : j < arms.length)
    (hx : σ xv = ofK (addressOfIndex j)) (hne : ∀ i < j, σ xv ≠ ofK (addressOfIndex i))
    (hhead : JumpTo Γ fp hdr FS Ag one entry sfp (pos + 3 + armsSize (blocks.take j)))
    (harm : wL Γ fp σ hdr FS Ag cl blocks[j] arms[j] (pos + 3 + armsSize (blocks.take j)) ks
      (fun ks' => Γ.tgt (pos + 3 + armsSize (blocks.take j) + blockSize blocks[j]) =
          Γ.tgt (pos + 3 + armsSize blocks) ∧ next rest ks')
      (fun ks' d f => d = Γ.tgt (pos + 3 + armsSize blocks) ∧ f = ofK (addressOfIndex fp) ∧
        next rest ks') kret khalt) :
    wS Γ fp σ hdr FS Ag cl (.chain h join lx entry one sfp [first] [blocks]) cs pos ks next kj
      kret khalt := by
  simp only [wS, hcs, stagesSize, Nat.add_zero, List.headD_cons]
  refine ⟨hset, hslot, hhead _ _ ?_⟩
  simp only [List.length_singleton, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, wStages]
  refine wArms_pick blocks arms 0 (pos + 3) j hj ha (by simpa using hx)
    (fun i hi => by simpa using hne i hi) rfl rfl ?_
  simp only [true_and]
  exact harm

/-- **The words of the picked arm of a last stage**: its block's words given how its path ends,
then the jump to the join (an arm but the last) or the fall into it (the last arm). -/
theorem wL_arm_join {o : Out} {blk : List PStmt} {a : List Stmt} {p T j n join one sfp : ℕ}
    {ks : List (ℕ × ℕ)} {N : List (ℕ × ℕ) → Prop} {K kret khalt : Prop}
    (hblk : ∀ (next : List Stmt → List (ℕ × ℕ) → Prop) (kj : List (ℕ × ℕ) → E → E → Prop),
      OutK o [] next K ks → wLc Γ fp σ hdr FS Ag cl blk a p ks next kj kret khalt)
    (hout : OutK o [] (fun _ ks' => N ks') K ks)
    (hlast : j + 1 = n → p + blockSize blk = T)
    (hjump : j + 1 ≠ n → JumpTo Γ fp hdr FS Ag one join sfp T) :
    wL Γ fp σ hdr FS Ag cl (blk ++ (if j + 1 != n then [PStmt.op [] (.jump one join sfp)] else []))
      a p ks (fun ks' => Γ.tgt (p + blockSize (blk ++
        (if j + 1 != n then [PStmt.op [] (.jump one join sfp)] else []))) = Γ.tgt T ∧ N ks')
      (fun ks' d f => d = Γ.tgt T ∧ f = ofK (addressOfIndex fp) ∧ N ks') kret khalt := by
  rw [wL_eq_wLc]
  by_cases hl : j + 1 = n
  · have e : (j + 1 != n) = false := by simp [hl]
    simp only [e, Bool.false_eq_true, ite_false, List.append_nil]
    refine hblk _ _ ?_
    cases o with
    | fall es => exact fun cs' hc => ⟨by rw [hlast hl], hout cs' hc⟩
    | ret es vs => exact hout
    | stuck => exact hout.elim
  · have e : (j + 1 != n) = true := by simp [hl]
    simp only [e, ite_true]
    rw [wLc_append Γ fp σ hdr FS Ag cl _ _ (List.cons_ne_nil _ _)]
    refine hblk _ _ ?_
    cases o with
    | fall es =>
      intro cs' hc
      simp only [wLc, wS, List.isEmpty_nil, ite_true]
      exact hjump hl _ _ ⟨rfl, rfl, hout cs' hc⟩
    | ret es vs => exact hout
    | stuck => exact hout.elim

/-- **The words of the picked arm of a stage that dispatches into the next**: its block's words
given how its path ends, then the read of the next stage's table and the jump to the arm `T` it
names, where the next stage's words `kj` hold. -/
theorem wL_arm_next {o : Out} {blk : List PStmt} {a : List Stmt} {p T lx nf e one sfp : ℕ}
    {ks : List (ℕ × ℕ)} {Nf : List (ℕ × ℕ) → Prop} {kj : List (ℕ × ℕ) → E → E → Prop}
    {K kret khalt : Prop}
    (hblk : ∀ (next : List Stmt → List (ℕ × ℕ) → Prop) (kj : List (ℕ × ℕ) → E → E → Prop),
      OutK o [] next K ks → wLc Γ fp σ hdr FS Ag cl blk a p ks next kj kret khalt)
    (hout : OutK o [] (fun _ ks' => kj ks' (Γ.tgt T) (ofK (addressOfIndex fp))) K ks)
    (hslot : HW Γ fp Ag (Γ.pc0 + (p + blockSize blk)) (.slot lx nf e))
    (hjump : JumpTo Γ fp hdr FS Ag one e sfp T) :
    wL Γ fp σ hdr FS Ag cl (blk ++ [PStmt.op [] (.slot lx nf e), .op [] (.jump one e sfp)])
      a p ks Nf kj kret khalt := by
  rw [wL_eq_wLc, wLc_append Γ fp σ hdr FS Ag cl _ _ (List.cons_ne_nil _ _)]
  refine hblk _ _ ?_
  cases o with
  | fall es =>
    intro cs' hc
    simp only [wLc, wS, List.isEmpty_nil, ite_true]
    exact ⟨hslot, hjump _ _ (hout cs' hc)⟩
  | ret es vs => exact hout
  | stuck => exact hout.elim

/-- **The words of a chain** from its head (the join's `SET`, the first table read, the jump into
the arm `T` the first selector names) and its stages' words from there. -/
theorem wS_chain {h : List LHint} {join lx entry one sfp : ℕ} {firsts : List ℕ}
    {stages : List (List (List PStmt))} {cs rest : List Stmt} {s : Stmt} {pos T : ℕ}
    {ks : List (ℕ × ℕ)} {next : List Stmt → List (ℕ × ℕ) → Prop}
    {kj : List (ℕ × ℕ) → E → E → Prop} {kret khalt : Prop}
    (hcs : ctrlSplit cs = some (s, rest))
    (hset : HW Γ fp Ag (Γ.pc0 + pos) (.set join (.local (pos + 3 + stagesSize stages))))
    (hslot : HW Γ fp Ag (Γ.pc0 + pos + 1) (.slot lx (firsts.headD 0) entry))
    (hhead : JumpTo Γ fp hdr FS Ag one entry sfp T)
    (hst : wStages Γ fp σ hdr FS Ag cl stages ((s :: rest).take stages.length) (pos + 3)
      (next ((s :: rest).drop stages.length)) kret khalt ks (Γ.tgt T) (ofK (addressOfIndex fp))) :
    wS Γ fp σ hdr FS Ag cl (.chain h join lx entry one sfp firsts stages) cs pos ks next kj
      kret khalt := by
  simp only [wS, hcs]
  exact ⟨hset, hslot, hhead _ _ hst⟩

end Words

/-! ## Arms off the path -/

/-- What off-path placements (`InBlockOff`'s clause) do to the places: with no value waiting to
be placed before, none after, new places only of values the passed events make or of frame
addresses among the atoms `A`, and the values the later trace makes left unplaced. -/
def OffNew (st st' : St) (A : List Atom) : Prop :=
  st.lazy = none → st'.lazy = none ∧
    (∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf st.rest ∨
      ∃ run, Atom.frameAddr v run ∈ A) ∧
    ((allocsOf st.rest).Nodup → ∀ v ∈ allocsOf st'.rest, st.locs[v]? = none → st'.locs[v]? = none)

section Inv

variable {ctx : Backend.Ctx} {I : Inst} {C : (ℕ → E) → Prop}

/-- The scope walk of an inner block gives the values in scope back and passes a prefix of the
trace. -/
theorem scopeInner_live_rest {rc : ℕ} {z : List Stmt} {s s₁ : SSt}
    (hsc : scopeInner rc (fun s' => scopeBlock rc z s') s = .ok s₁) :
    s₁.live = s.live ∧ ∃ pre, s.rest = pre ++ s₁.rest := by
  obtain ⟨_, _, _, s₄, -, -, -, -, rfl⟩ := scopeInner_inv hsc
  obtain ⟨pre, hpre, -⟩ := scopeInner_cons (scopeBlock_cons rc z) hsc
  exact ⟨rfl, pre, hpre⟩

/-- **The invariant past placements off the path** (arms not taken): the constraint kept, in
lockstep with the scope walk past them (which gives the values in scope back and passes a prefix
of the trace), the return area as before, given that no value in scope is the target of a frame
address among the atoms `A` they place. -/
theorem winv_past {A : List Atom} {st st' : St} {s s₁ : SSt} (hinv : WInv ctx I C st s)
    (hlv : s₁.live = s.live) (hpre : ∃ pre, s.rest = pre ++ s₁.rest)
    (hfl : ∀ v run, s.live.contains v = true → Atom.frameAddr v run ∉ A)
    (hr : st'.rest = s₁.rest) (hs : st'.scope = st.scope)
    (hch : st.chainIn = none → st'.chainIn = none)
    (hn : st.next ≤ st'.next) (hl : LocsLe st.locs st'.locs) (hnew : OffNew st st' A) :
    WInv ctx I C st' { s₁ with retDone := s.retDone } := by
  obtain ⟨pre, hpre⟩ := hpre
  have hrest : st.rest = pre ++ st'.rest := by rw [← hinv.rest, hpre, hr]
  have hall : allocsOf st.rest = allocsOf pre ++ allocsOf st'.rest := by
    rw [hrest, allocsOf_append]
  obtain ⟨hlz, hnw, hfr⟩ := hnew hinv.lazy
  refine ⟨⟨hinv.cok.sat, hinv.cok.blind.mono hn, fun Ψ hΨ => by
      rw [hs]; exact (hinv.cok.pools Ψ hΨ).grow hl, by rw [hs]; exact hinv.cok.cells.mono hn⟩,
    hr.symm, fun v l hv hvl => ?_, le_trans hinv.two hn, le_trans hinv.abi hn, ?_,
    fun hd => hinv.ret hd, ?_, fun v hv => ⟨hfr hinv.nodup v hv
        (hinv.fresh v (by rw [hall]; exact List.mem_append_right _ hv)).1,
      show s₁.live.contains v = false from hlv ▸
        (hinv.fresh v (by rw [hall]; exact List.mem_append_right _ hv)).2⟩,
    hch hinv.chain, by rw [hs]; exact hinv.pnt, hlz⟩
  · have hv' : s.live.contains v = true := by rw [← hlv]; exact hv
    cases h0 : st.locs[v]? with
    | none =>
      rcases hnw v (by rw [hvl]; simp) with h | h | ⟨run, h⟩
      · exact absurd h0 h
      · rw [(hinv.fresh v h).2] at hv'
        cases hv'
      · exact absurd h (hfl v run hv')
    | some l' =>
      have e : l' = l := by
        have := hl v l' h0
        rw [hvl] at this
        exact (Option.some.inj this).symm
      subst e
      obtain ⟨h1, h2, h3⟩ := hinv.vw v l' hv' h0
      exact ⟨h1, lt_of_lt_of_le h2 hn, h3⟩
  · have := hinv.fuel
    rw [hrest, List.length_append] at this
    omega
  · have := hinv.nodup
    rw [hall] at this
    exact this.of_append_right

/-- **The invariant at a rewound next free cell**: the constraint blind from `base` on, the pools
and the values in scope below it. -/
theorem WInv.rewind {st : St} {s : SSt} {base : ℕ} (hinv : WInv ctx I C st s)
    (hb : Blind C base) (hg : ScopeGood base st.scope)
    (hlt : ∀ v l, s.live.contains v = true → st.locs[v]? = some l → locBase l < base)
    (h2 : 2 ≤ base) (habi : 2 + ctx.argCells + ctx.retCells ≤ base) :
    WInv ctx I C { st with next := base } s :=
  ⟨⟨hinv.cok.sat, hb, hinv.cok.pools, hg⟩, hinv.rest, fun v l hv hl =>
    ⟨(hinv.vw v l hv hl).1, hlt v l hv hl, (hinv.vw v l hv hl).2.2⟩, h2, habi, hinv.fuel,
    hinv.ret, hinv.nodup, hinv.fresh, hinv.chain, hinv.pnt, hinv.lazy⟩

end Inv

/-! ## The arms of a stage -/

/-- How an arm of a `match` leaves (`placeArms`): through the next stage's table, or to the join
(the last arm falling through into it). -/
def armLeave (exit : ArmExit) (j n : ℕ) : P (List PStmt) :=
  match exit with
  | .next x first one sfp => do
      let e ← fresh
      pure [PStmt.op [] (.slot x first e), .op [] (.jump one e sfp)]
  | .join join one sfp => pure (if j + 1 != n then [PStmt.op [] (.jump one join sfp)] else [])

theorem placeArms_cons (arm : List Stmt) (more : List (List Stmt)) (j n base : ℕ)
    (exit : ArmExit) : placeArms (arm :: more) j n base exit = (do
      modify fun s => { s with next := base }
      let blk ← inBlock (placeBlock arm)
      let leave ← armLeave exit j n
      let top := (← get).next
      let blocks ← placeArms more (j + 1) n base exit
      modify fun s => { s with next := max s.next top }
      pure ((blk ++ leave) :: blocks)) := by
  rw [placeArms]
  cases exit <;> simp only [armLeave, bind_assoc, pure_bind]

/-- An arm's way out moves the next free cell only. -/
theorem armLeave_wp {ctx : Backend.Ctx} {st : St} (exit : ArmExit) (j n : ℕ) :
    wpP (armLeave exit j n) ctx st fun _ st' => ∃ k, st' = { st with next := st.next + k } := by
  cases exit with
  | next x first one sfp =>
    exact wp_bind.mpr (wp_modifyGet.mpr (wp_pure.mpr ⟨1, rfl⟩))
  | join join one sfp => exact wp_pure.mpr ⟨0, rfl⟩

theorem OffNew.trans {st st₁ st₂ : St} {A B : List Atom} (h₁ : OffNew st st₁ A)
    (h₂ : OffNew st₁ st₂ B) (hsub₁ : ∀ v ∈ allocsOf st₁.rest, v ∈ allocsOf st.rest)
    (hsub₂ : ∀ v ∈ allocsOf st₂.rest, v ∈ allocsOf st₁.rest)
    (hnd : (allocsOf st.rest).Nodup → (allocsOf st₁.rest).Nodup) : OffNew st st₂ (A ++ B) := by
  intro hz
  obtain ⟨z₁, n₁, f₁⟩ := h₁ hz
  obtain ⟨z₂, n₂, f₂⟩ := h₂ z₁
  refine ⟨z₂, fun v hv => ?_, fun hnd₀ v hv h0 => f₂ (hnd hnd₀) v hv (f₁ hnd₀ v (hsub₂ v hv) h0)⟩
  rcases n₂ v hv with h | h | ⟨run, h⟩
  · rcases n₁ v h with h' | h' | ⟨run, h'⟩
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr ⟨run, List.mem_append_left _ h'⟩)
  · exact Or.inr (Or.inl (hsub₁ v h))
  · exact Or.inr (Or.inr ⟨run, List.mem_append_right _ h⟩)

section Arms

variable {ctx : Backend.Ctx} {exit : ArmExit} {n base : ℕ}

/-- **Arms off the path** from the next free cell `base` on: each gives the scope, the statements
and the chaining back, in lockstep with the scope walk, the next free cell ending past `base`, the
places grown by the passed events' values and the arms' frame addresses only. -/
theorem placeArms_off : ∀ (arms : List (List Stmt)) (j : ℕ) (st : St) (s : SSt) (acc : Bool)
    (s' : SSt), scopeArms ctx.retCells arms s acc = .ok s' →
    st.rest = s.rest → st.rest.length ≤ ctx.fuel →
    wpP (placeArms arms j n base exit) ctx st fun bs st' => bs.length = arms.length ∧
      st'.rest = s'.rest ∧ st'.scope = st.scope ∧ st'.out = st.out ∧
      (st.chainIn = none → st'.chainIn = none) ∧ base ≤ st'.next ∧ LocsLe st.locs st'.locs ∧
      s'.live = s.live ∧ (∃ pre, s.rest = pre ++ s'.rest) ∧ OffNew st st' (armsAtoms arms) ∧
      (∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st.rest) ∧
      (∀ x ∈ st.tables.shared, x ∈ st'.tables.shared)
  | [], j, st, s, acc, s', hsc, hr, _ => by
    simp only [scopeArms] at hsc
    cases hsc
    rw [placeArms]
    refine wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ?_))
    exact ⟨rfl, hr, rfl, rfl, fun h => h, le_rfl, LocsLe.refl _, rfl, ⟨[], rfl⟩,
      fun h => ⟨h, fun v hv => Or.inl hv, fun _ _ _ h => h⟩, fun _ h => h, fun _ h => h⟩
  | arm :: more, j, st, s, acc, s', hsc, hr, hf => by
    simp only [scopeArms] at hsc
    split at hsc
    · cases hsc
    next s₁ h₁ =>
    obtain ⟨hlv₁, pre₁, hpre₁⟩ := scopeInner_live_rest h₁
    rw [placeArms_cons]
    refine wp_bind.mpr (wp_modify.mpr ?_)
    refine wp_bind.mpr fun blk st₁ he₁ => ?_
    obtain ⟨hr₁, hs₁, ho₁, hc₁, hn₁, hl₁, hz₁, hsub₁, ht₁⟩ :=
      inBlockOff_ok arm { st with next := base } s s₁ h₁ hr hf blk st₁ he₁
    refine wp_bind.mpr fun leave st₂ he₂ => ?_
    obtain ⟨k, rfl⟩ := armLeave_wp exit j n leave st₂ he₂
    refine wp_bind.mpr (wp_get.mpr ?_)
    refine wp_bind.mpr fun bs st₃ he₃ => ?_
    have hrest : st.rest = pre₁ ++ st₁.rest := by rw [hr, hpre₁, hr₁]
    have hlen₁ : st₁.rest.length ≤ ctx.fuel := by
      have := congrArg List.length hrest
      rw [List.length_append] at this
      omega
    obtain ⟨hb₃, hr₃, hs₃, ho₃, hc₃, hn₃, hl₃, hlv₃, ⟨pre₃, hpre₃⟩, hz₃, hsub₃, ht₃⟩ :=
      placeArms_off more (j + 1) { st₁ with next := st₁.next + k } { s₁ with retDone := s.retDone }
        _ s' hsc hr₁ hlen₁ bs st₃ he₃
    refine wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ?_))
    refine ⟨by simp [hb₃], hr₃, by rw [hs₃]; exact hs₁, by rw [ho₃]; exact ho₁,
      fun h => hc₃ (hc₁ h), le_trans hn₃ (Nat.le_max_left _ _),
      fun v x h => hl₃ v x (hl₁ v x h), by rw [hlv₃]; exact hlv₁,
      ⟨pre₁ ++ pre₃, by rw [hpre₁, List.append_assoc]; exact congrArg (pre₁ ++ ·) hpre₃⟩,
      ?_, fun v hv => hsub₁ v (hsub₃ v hv), fun x hx => ht₃ x (ht₁ x hx)⟩
    have := OffNew.trans (st₁ := { st₁ with next := st₁.next + k }) (st₂ := st₃) hz₁ hz₃ hsub₁
      hsub₃ fun hnd => by rw [hrest, allocsOf_append] at hnd; exact hnd.of_append_right
    exact this

end Arms

/-! ## The arm a stage's selector picks, on the path -/

/-- How a placed arm leaves: through the next stage's table, its fresh cell (from `lo` on, below
`hi`) holding `we` under the constraint, or to the join. -/
def LeaveOK (exit : ArmExit) (j n : ℕ) (leave : List PStmt) (C : (ℕ → E) → Prop) (we : E)
    (lo hi : ℕ) : Prop :=
  match exit with
  | .next x first one sfp => ∃ e, lo ≤ e ∧ e < hi ∧
      leave = [PStmt.op [] (.slot x first e), .op [] (.jump one e sfp)] ∧ ∀ Ψ, C Ψ → Ψ e = we
  | .join join one sfp => leave = (if j + 1 != n then [PStmt.op [] (.jump one join sfp)] else [])

theorem LeaveOK.mono {exit : ArmExit} {j n : ℕ} {leave : List PStmt} {C C' : (ℕ → E) → Prop}
    {we : E} {lo hi hi' : ℕ} (h : LeaveOK exit j n leave C we lo hi) (hs : Stronger C' C)
    (hh : hi ≤ hi') : LeaveOK exit j n leave C' we lo hi' := by
  cases exit with
  | next x first one sfp =>
    obtain ⟨e, h1, h2, h3, h4⟩ := h
    exact ⟨e, h1, lt_of_lt_of_le h2 hh, h3, fun Ψ hΨ => h4 Ψ (hs Ψ hΨ)⟩
  | join join one sfp => exact h

theorem TabsW.back {κ₀ : ℕ} {Γ : Site κ₀}
    {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {st st' : St}
    (h : TabsW Γ Ag st') (ht : ∀ x ∈ st.tables.shared, x ∈ st'.tables.shared) : TabsW Γ Ag st :=
  fun fs first hm => h fs first (ht _ hm)

theorem scopeArms_retDone (rc : ℕ) : ∀ (arms : List (List Stmt)) (s : SSt) (acc : Bool)
    (s' : SSt), scopeArms rc arms s acc = .ok s' → acc = true → s'.retDone = true
  | [], s, acc, s', h, ha => by
    simp only [scopeArms] at h
    cases h
    exact ha
  | arm :: more, s, acc, s', h, ha => by
    simp only [scopeArms] at h
    split at h
    · cases h
    · exact scopeArms_retDone rc more _ _ s' h (by simp [ha])

section Inv2

variable {ctx : Backend.Ctx} {I : Inst} {C : (ℕ → E) → Prop}

/-- The invariant past a fresh cell holding the word `we`. -/
theorem WInv.assign {st : St} {s : SSt} (hinv : WInv ctx I C st s) (we : E) :
    WInv ctx I (fun Ψ => C Ψ ∧ Ψ st.next = we) { st with next := st.next + 1 } s :=
  ⟨hinv.cok.assign (wblind_const we _), hinv.rest,
    fun v l hv hl => let ⟨h1, h2, h3⟩ := hinv.vw v l hv hl
      ⟨h1, Nat.lt_succ_of_lt h2, fun Ψ hΨ => h3 Ψ hΨ.1⟩,
    Nat.le_succ_of_le hinv.two, Nat.le_succ_of_le hinv.abi, hinv.fuel,
    fun hr Ψ k w hk hΨ => ⟨hinv.ret hr Ψ k w hk hΨ.1, by
      rw [Function.update_of_ne (by have := hinv.abi; omega)]
      exact hΨ.2⟩,
    hinv.nodup, hinv.fresh, hinv.chain, hinv.pnt, hinv.lazy⟩

/-- The invariant with the next free cell moved up. -/
theorem WInv.raise {st : St} {s : SSt} {m : ℕ} (hinv : WInv ctx I C st s) (hm : st.next ≤ m) :
    WInv ctx I C { st with next := m } s :=
  ⟨⟨hinv.cok.sat, hinv.cok.blind.mono hm, hinv.cok.pools, hinv.cok.cells.mono hm⟩, hinv.rest,
    fun v l hv hl => ⟨(hinv.vw v l hv hl).1, lt_of_lt_of_le (hinv.vw v l hv hl).2.1 hm,
      (hinv.vw v l hv hl).2.2⟩,
    le_trans hinv.two hm, le_trans hinv.abi hm, hinv.fuel, hinv.ret, hinv.nodup, hinv.fresh,
    hinv.chain, hinv.pnt, hinv.lazy⟩

/-- The invariant with another return-area flag, made later or no earlier. -/
theorem WInv.setRet {st : St} {s : SSt} (hinv : WInv ctx I C st s) {b : Bool}
    (hb : b = false → s.retDone = false) : WInv ctx I C st { s with retDone := b } :=
  ⟨hinv.cok, hinv.rest, hinv.vw, hinv.two, hinv.abi, hinv.fuel, fun h => hinv.ret (hb h),
    hinv.nodup, hinv.fresh, hinv.chain, hinv.pnt, hinv.lazy⟩

/-- Off-path placements keep the places of the values in scope. -/
theorem live_locs_keep {A : List Atom} {st st' : St} {s : SSt} (hinv : WInv ctx I C st s)
    (hfl : ∀ v run, s.live.contains v = true → Atom.frameAddr v run ∉ A)
    (hl : LocsLe st.locs st'.locs)
    (hnew : OffNew st st' A) :
    ∀ v l, s.live.contains v = true → st'.locs[v]? = some l → st.locs[v]? = some l := by
  intro v l hv hvl
  cases h0 : st.locs[v]? with
  | none =>
    rcases (hnew hinv.lazy).2.1 v (by rw [hvl]; simp) with h | h | ⟨run, h⟩
    · exact absurd h0 h
    · rw [(hinv.fresh v h).2] at hv
      cases hv
    · exact absurd h (hfl v run hv)
  | some l' =>
    have := hl v l' h0
    rw [hvl] at this
    exact this.symm

end Inv2

section Pick

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Backend.Ctx} {I : Inst} {exit : ArmExit} {n base : ℕ}

/-- **The arms of a stage, the picked one on the path**: from the state whose rewound next free
cell `base` has the invariant, the arms before arm `jp` are off the path (the constraint kept, the
next free cell rewound for each), arm `jp` runs as `InBlockW` has it at the absolute position
`q` plus the arms before it, its way out holds `we` in its fresh cell, and the arms after it are
dead. -/
theorem placeArms_pick (we : E) : ∀ (arms : List (List Stmt)) (jp j : ℕ) (st : St) (s : SSt)
    (acc : Bool) (s' : SSt) (q i₀ : ℕ) (o : Out) (C : (ℕ → E) → Prop) (hj : jp < arms.length),
    InBlockW Γ Ag cl ctx I arms[jp] →
    scopeArms ctx.retCells arms s acc = .ok s' → WInv ctx I C { st with next := base } s →
    (∀ v run, s.live.contains v = true → Atom.frameAddr v run ∉ armsAtoms arms) →
    walk I.σ arms[jp] = o → o ≠ .stuck → (∀ e ∈ outEs o, e ∈ I.es) →
    (∀ k < (calls (outEs o)).length, cl[i₀ + k]? = (calls (outEs o))[k]?) →
    (∀ v ∈ pathVals I.σ arms[jp] o, ∀ run,
      Atom.frameAddr v run ∉ armsAtoms (arms.drop (jp + 1))) →
    wpP (placeArms arms j n base exit) ctx st fun bs st' => ∃ C', Stronger C' C ∧
      (∃ Ψ, C' Ψ) ∧ Blind C' st'.next ∧ base ≤ st'.next ∧ LocsLe st.locs st'.locs ∧
      bs.length = arms.length ∧ st'.out = st.out ∧ st'.scope = st.scope ∧ st'.chainIn = none ∧
      st'.rest = s'.rest ∧ (∀ x ∈ st.tables.shared, x ∈ st'.tables.shared) ∧
      ∃ blk leave, bs[jp]? = some (blk ++ leave) ∧
        LeaveOK exit (j + jp) n leave C' we base st'.next ∧
        (∀ es, o = .fall es → Fits I st' →
          OpsIn I (q + armsSize (bs.take jp)) (blockOps blk (q + armsSize (bs.take jp))) →
          TabsW Γ Ag st' → FillsIn Γ Ag (q + armsSize (bs.take jp)) blk → WInv ctx I C' st' s') ∧
        (Fits I st' →
          OpsIn I (q + armsSize (bs.take jp)) (blockOps blk (q + armsSize (bs.take jp))) →
          TabsW Γ Ag st' → FillsIn Γ Ag (q + armsSize (bs.take jp)) blk →
          BlkW Γ I ctx Ag cl C' blk arms[jp] [] o i₀ (q + armsSize (bs.take jp)) ∧
            RW I C' st' (pathVals I.σ arms[jp] o))
  | [], _, _, _, _, _, _, _, _, _, _, hj, _, _, _, _, _, _, _, _, _ =>
    absurd hj (Nat.not_lt_zero _)
  | arm :: more, 0, j, st, s, acc, s', q, i₀, o, C, _, hin, hsc, hW, hfl, hw, hns, hes,
      hcl, hfa => by
    simp only [scopeArms] at hsc
    split at hsc
    · cases hsc
    next s₁ h₁ =>
    obtain ⟨hlv₁, pre₁, hpre₁⟩ := scopeInner_live_rest h₁
    rw [placeArms_cons]
    refine wp_bind.mpr (wp_modify.mpr ?_)
    refine wp_bind.mpr fun blk st₁ he₁ => ?_
    obtain ⟨hr₁, hs₁, ho₁, hc₁, hn₁, hl₁, hz₁, hsub₁, ht₁⟩ :=
      inBlockOff_ok arm { st with next := base } s s₁ h₁ hW.rest.symm hW.fuel blk st₁ he₁
    obtain ⟨C₁, hsat₁, hb₁, hst₁, -, -, hout₁, hsc₁, hch₁, hW₁, hB₁⟩ :=
      hin C { st with next := base } s s₁ i₀ q o h₁ hw hns hes hcl hW hW.cok blk st₁ he₁
    refine wp_bind.mpr fun leave st₂ he₂ => ?_
    -- the way out: a fresh cell holding `we` through the next stage's table, or nothing
    obtain ⟨C₂, k, rfl, hst₂, hsat₂, hb₂, hlv₂, hW₂⟩ : ∃ C₂ k, st₂ = { st₁ with next := st₁.next + k } ∧
        Stronger C₂ C₁ ∧ (∃ Ψ, C₂ Ψ) ∧ Blind C₂ (st₁.next + k) ∧
        LeaveOK exit (j + 0) n leave C₂ we base (st₁.next + k) ∧
        (WInv ctx I C₁ st₁ s₁ → WInv ctx I C₂ { st₁ with next := st₁.next + k } s₁) := by
      cases exit with
      | next x first one sfp =>
        have := (wp_bind.mpr (wp_modifyGet.mpr (wp_pure.mpr ⟨rfl, rfl⟩)) :
          wpP (armLeave (.next x first one sfp) j n) ctx st₁ fun lv st' =>
            lv = [PStmt.op [] (.slot x first st₁.next), .op [] (.jump one st₁.next sfp)] ∧
            st' = { st₁ with next := st₁.next + 1 }) leave st₂ he₂
        obtain ⟨rfl, rfl⟩ := this
        exact ⟨fun Ψ => C₁ Ψ ∧ Ψ st₁.next = we, 1, rfl, fun _ h => h.1,
          assign_sat hb₁ (wblind_const we _) le_rfl hsat₁,
          assign_blind hb₁ (wblind_const we _) le_rfl,
          ⟨st₁.next, le_trans (by simp) hn₁, Nat.lt_succ_self _, rfl, fun _ h => h.2⟩,
          fun h => h.assign we⟩
      | join join one sfp =>
        have := (wp_pure.mpr ⟨rfl, rfl⟩ :
          wpP (armLeave (.join join one sfp) j n) ctx st₁ fun lv st' =>
            lv = (if j + 1 != n then [PStmt.op [] (.jump one join sfp)] else []) ∧ st' = st₁)
          leave st₂ he₂
        obtain ⟨rfl, rfl⟩ := this
        exact ⟨C₁, 0, rfl, Stronger.refl _, hsat₁, hb₁, by simp [LeaveOK], fun h => h⟩
    refine wp_bind.mpr (wp_get.mpr ?_)
    refine wp_bind.mpr fun bs st₃ he₃ => ?_
    have hrs : s.rest = st.rest := hW.rest
    have hlen₁ : st₁.rest.length ≤ ctx.fuel := by
      have hf0 : st.rest.length ≤ ctx.fuel := hW.fuel
      have h' := congrArg List.length hpre₁
      rw [List.length_append, hrs, ← hr₁] at h'
      omega
    obtain ⟨hb₃, hr₃, hs₃, ho₃, hc₃, hn₃, hl₃, hlv₃, ⟨pre₃, hpre₃⟩, hz₃, hsub₃, ht₃⟩ :=
      placeArms_off more (j + 1) { st₁ with next := st₁.next + k } { s₁ with retDone := s.retDone }
        _ s' hsc hr₁ hlen₁ bs st₃ he₃
    refine wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ?_))
    have hnm : st₁.next + k ≤ max st₃.next (st₁.next + k) := Nat.le_max_right _ _
    have hl₁₃ : LocsLe st₁.locs st₃.locs := hl₃
    have hfl' : ∀ v run, s₁.live.contains v = true → Atom.frameAddr v run ∉ armsAtoms more :=
      fun v run hv h => hfl v run (by rw [← hlv₁]; exact hv)
        (by simp only [armsAtoms]; exact List.mem_append_right _ h)
    have hnew₃ := hz₃ (hz₁ (by simpa using hW.lazy)).1
    refine ⟨C₂, hst₁.trans hst₂, hsat₂, hb₂.mono hnm, le_trans (le_trans hn₁ (Nat.le_add_right _ _))
      hnm, fun v x h => hl₃ v x (hl₁ v x h), by simp [hb₃], by rw [ho₃]; exact ho₁,
      by rw [hs₃]; exact hs₁, hc₃ hch₁, hr₃, fun x hx => ht₃ x (ht₁ x hx),
      blk, leave, rfl, hlv₂.mono (Stronger.refl _) hnm, fun es hes' hF hO hT hFl => ?_,
      fun hF hO hT hFl => ?_⟩
    · have hF₁ : Fits I st₁ := hF.back (le_trans (Nat.le_add_right _ _) hnm) hl₁₃
      have hW₂' := hW₂ (hW₁ es hes' hF₁ (by simpa [armsSize] using hO) (hT.back ht₃)
        (by simpa [armsSize] using hFl))
      have := winv_past (A := armsAtoms more)
        (st' := { st₃ with next := max st₃.next (st₁.next + k) }) hW₂' (by rw [hlv₃]) ⟨pre₃, hpre₃⟩
        hfl' hr₃ hs₃ hc₃ hnm hl₃ hz₃
      refine (this.setRet fun hb => ?_ : WInv ctx I C₂ _ { s' with retDone := s'.retDone })
      cases h1 : s₁.retDone
      · rfl
      · rw [scopeArms_retDone _ more _ _ s' hsc (by simp [h1])] at hb
        cases hb
    · have hF₁ : Fits I st₁ := hF.back (le_trans (Nat.le_add_right _ _) hnm) hl₁₃
      obtain ⟨hB, hR⟩ := hB₁ hF₁ (by simpa [armsSize] using hO) (hT.back ht₃)
        (by simpa [armsSize] using hFl)
      refine ⟨by simpa [armsSize] using hB.mono hst₂,
        hR.grow (st' := { st₃ with next := max st₃.next (st₁.next + k) }) hst₂
          (le_trans (Nat.le_add_right _ _) hnm) hl₁₃ (fun v hv hvl => ?_) (fun v hv => hsub₃ v hv)⟩
      rcases hnew₃.2.1 v hvl with h | h | ⟨run, h⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hfa v (by simpa using hv) run)
  | arm :: more, jp + 1, j, st, s, acc, s', q, i₀, o, C, hj, hin, hsc, hW, hfl, hw, hns,
      hes, hcl, hfa => by
    simp only [scopeArms] at hsc
    split at hsc
    · cases hsc
    next s₁ h₁ =>
    obtain ⟨hlv₁, pre₁, hpre₁⟩ := scopeInner_live_rest h₁
    rw [placeArms_cons]
    refine wp_bind.mpr (wp_modify.mpr ?_)
    refine wp_bind.mpr fun blk st₁ he₁ => ?_
    obtain ⟨hr₁, hs₁, ho₁, hc₁, hn₁, hl₁, hz₁, hsub₁, ht₁⟩ :=
      inBlockOff_ok arm { st with next := base } s s₁ h₁ hW.rest.symm hW.fuel blk st₁ he₁
    refine wp_bind.mpr fun leave st₂ he₂ => ?_
    obtain ⟨k, rfl⟩ := armLeave_wp exit j n leave st₂ he₂
    refine wp_bind.mpr (wp_get.mpr ?_)
    refine wp_bind.mpr fun bs st₃ he₃ => ?_
    have hfl₀ : ∀ v run, s.live.contains v = true → Atom.frameAddr v run ∉ atomsIn arm :=
      fun v run hv h => hfl v run hv (by simp only [armsAtoms]; exact List.mem_append_left _ h)
    have hW₂ := winv_past (A := atomsIn arm) (st' := { st₁ with next := st₁.next + k }) hW hlv₁
      ⟨pre₁, hpre₁⟩ hfl₀ hr₁ hs₁ hc₁ (le_trans hn₁ (Nat.le_add_right _ _)) hl₁ hz₁
    have hkeep := live_locs_keep (A := atomsIn arm) (st' := { st₁ with next := st₁.next + k }) hW
      hfl₀ hl₁ hz₁
    have hWb : WInv ctx I C { { st₁ with next := st₁.next + k } with next := base }
        { s₁ with retDone := s.retDone } :=
      hW₂.rewind hW.cok.blind (by rw [hs₁]; exact hW.cok.cells)
        (fun v l hv hl => (hW.vw v l (by rw [← hlv₁]; exact hv) (hkeep v l
          (by rw [← hlv₁]; exact hv) hl)).2.1) hW.two hW.abi
    obtain ⟨C', hst', hsat', hb', hn', hl', hb₃, ho₃, hs₃, hc₃, hr₃, ht₃, blk', leave', hbs,
        hlv', hW', hB'⟩ :=
      placeArms_pick we more jp (j + 1) { st₁ with next := st₁.next + k }
        { s₁ with retDone := s.retDone } _ s' (q + blockSize (blk ++ leave)) i₀ o C
        (by simpa using hj) (by simpa using hin)
        hsc hWb (fun v run hv h => hfl v run (by rw [← hlv₁]; exact hv)
          (by simp only [armsAtoms]; exact List.mem_append_right _ h)) (by simpa using hw) hns
        hes hcl (by simpa using hfa) bs st₃ he₃
    refine wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ?_))
    have hnm : st₃.next ≤ max st₃.next (st₁.next + k) := Nat.le_max_left _ _
    have hpos : q + armsSize (((blk ++ leave) :: bs).take (jp + 1)) =
        q + blockSize (blk ++ leave) + armsSize (bs.take jp) := by
      simp only [List.take_succ_cons, armsSize]
      omega
    have hlvk : LeaveOK exit (j + (jp + 1)) n leave' C' we base (max st₃.next (st₁.next + k)) := by
      rw [show j + (jp + 1) = j + 1 + jp by omega]
      exact hlv'.mono (Stronger.refl _) hnm
    refine ⟨C', hst', hsat', hb'.mono hnm, le_trans hn' hnm,
      fun v x h => hl' v x (hl₁ v x h), by simp [hb₃], by rw [ho₃]; exact ho₁,
      by rw [hs₃]; exact hs₁, hc₃, hr₃, fun x hx => ht₃ x (ht₁ x hx), blk', leave',
      by simpa using hbs, hlvk, fun es hes' hF hO hT hFl => ?_, fun hF hO hT hFl => ?_⟩
    · rw [hpos] at hO hFl
      exact (hW' es hes' (hF.back hnm (LocsLe.refl _)) hO hT hFl).raise hnm
    · rw [hpos] at hO hFl ⊢
      obtain ⟨hB, hR⟩ := hB' (hF.back hnm (LocsLe.refl _)) hO hT hFl
      exact ⟨(by simpa using hB), hR.grow (Stronger.refl _) hnm (LocsLe.refl _)
        (fun v _ h => Or.inl h) (fun v hv => hv)⟩

end Pick

/-! ## A stage's cells -/

section Cells

variable {ctx : Backend.Ctx} {I : Inst} {C : (ℕ → E) → Prop} {st : St}

/-- **The cells an unchained `match` jumps with**: its selector's (holding its value), the frame
pointer's and the pooled `1`. -/
theorem matchCells_fat (hI : I.Ok) (hmain : ctx.isMain = true → I.fp = 0)
    (hk1 : I.kw (.const 1 0) = Guest.word 1 0) {x : V} {rest : List Stmt} {ok : V → Prop}
    (hv : VW I C st ok) (hx : ok x) (h2 : 2 ≤ st.next) :
    FAt ctx I C st (matchCells x rest false) fun r C' st' => r.2.1 = none ∧
      2 ≤ r.1 ∧ r.1 < st'.next ∧ (∀ Ψ, C' Ψ → Ψ r.1 = I.σ x) ∧
      2 ≤ r.2.2.1 ∧ r.2.2.1 < st'.next ∧ (∀ Ψ, C' Ψ → Ψ r.2.2.1 = I.fpw) ∧
      2 ≤ r.2.2.2 ∧ r.2.2.2 < st'.next ∧ (∀ Ψ, C' Ψ → Ψ r.2.2.2 = Guest.word 1 0) ∧
      st'.locs = st.locs ∧ st'.rest = st.rest := by
  unfold matchCells
  simp only [Bool.false_eq_true, ite_false]
  refine FAt.bind (cellOf_fat x hI hv hx) fun lx st₁ C₁ _ hn₁ _ ⟨hx2, hxlt, hlo₁, hr₁, hxw, _⟩ => ?_
  refine FAt.bind (FAt.pure (R := fun a C' st' => a = (none : Option (Cell × ℕ)) ∧ C' = C₁ ∧
    st' = st₁) ⟨rfl, rfl, rfl⟩) fun ns st₂ C₂ _ _ _ ⟨hns, hC₂, hst₂⟩ => ?_
  subst hC₂ hst₂
  refine FAt.bind (selfFp_fat hI hmain (le_trans h2 hn₁))
    fun sfp st₃ C₃ hs₃ hn₃ _ ⟨hf2, hflt, hlo₃, hr₃, hfw, _⟩ => ?_
  refine FAt.bind (constCell_fat (1, 0) hk1 (le_trans h2 (le_trans hn₁ hn₃)))
    fun one st₄ C₄ hs₄ hn₄ _ ⟨ho2, holt, hlo₄, hr₄, how⟩ => ?_
  refine FAt.pure ⟨hns, hx2, lt_of_lt_of_le hxlt (le_trans hn₃ hn₄),
    fun Ψ hΨ => hxw Ψ (hs₃ Ψ (hs₄ Ψ hΨ)), hf2, lt_of_lt_of_le hflt hn₄,
    fun Ψ hΨ => hfw Ψ (hs₄ Ψ hΨ), ho2, holt, how, by rw [hlo₄, hlo₃, hlo₁],
    by rw [hr₄, hr₃, hr₁]⟩

/-- **The words a chain's head gives its fresh cells**, fixed when the cells are made though they
name positions placed later: the join's is what the final instructions `SET` at the chain's
position `pos`, the entry's the target of the arm `j` the selector picks, read off the arms'
placement from the state `st'` they start in (placement is a function of its state). -/
def joinW (I : Inst) (pos : ℕ) : E :=
  match I.ops[pos]? with
  | some (.set _ k) => I.kw k
  | _ => 0

def entryW {κ₀ : ℕ} (Γ : Site κ₀) (ctx : Backend.Ctx) (arms : List (List Stmt)) (exit : ArmExit)
    (j pos : ℕ) (st' : St) : E :=
  match placeArms arms 0 arms.length st'.next exit ctx st' with
  | .ok (bs, _) => Γ.tgt (pos + 3 + armsSize (bs.take j))
  | .error _ => 0

theorem joinW_eq {I : Inst} {pos join : ℕ} {k : KVal} (h : I.ops[pos]? = some (.set join k)) :
    joinW I pos = I.kw k := by
  simp [joinW, h]

theorem entryW_eq {κ₀ : ℕ} {Γ : Site κ₀} {arms : List (List Stmt)} {exit : ArmExit}
    {j pos : ℕ} {st' st'' : St} {bs : List (List PStmt)}
    (h : placeArms arms 0 arms.length st'.next exit ctx st' = .ok (bs, st'')) :
    entryW Γ ctx arms exit j pos st' = Γ.tgt (pos + 3 + armsSize (bs.take j)) := by
  simp [entryW, h]

/-- **A chain's head cells**: the join and the entry, fresh with the words `wj` and `we`, the hints
taken, the first stage's table. -/
theorem headCells_fat (wj we : E) (n : ℕ) :
    FAt ctx I C st (do
      let join ← fresh
      let hints ← takeHints
      let first ← allocTable n
      let entry ← fresh
      pure (join, first, some (hints, entry))) fun r C' st' =>
      r.1 = st.next ∧ r.2.1 = st.tables.len ∧ (r.2.2.map Prod.snd) = some (st.next + 1) ∧
      st' = { st with next := st.next + 2, tables.len := st.tables.len + n, pending := #[] } ∧
      C' = fun Ψ => (C Ψ ∧ Ψ st.next = wj) ∧ Ψ (st.next + 1) = we := by
  refine FAt.bind (fresh_fat (fun _ => wj) (wblind_const wj _))
    fun join st₁ C₁ _ _ _ ⟨hj, hst₁, hC₁⟩ => ?_
  subst hj hst₁ hC₁
  refine FAt.bind takeHints_fat fun hints st₂ C₂ _ _ _ ⟨hC₂, hst₂⟩ => ?_
  subst hC₂ hst₂
  refine FAt.bind (FAt.ofSame (R := fun a C' st' => a = st.tables.len ∧ C' = _ ∧
      st' = { st with next := st.next + 1, tables.len := st.tables.len + n, pending := #[] })
    (wp_modifyGet.mpr ⟨rfl, rfl, rfl, LocsLe.refl _, rfl, rfl, rfl⟩))
    fun first st₃ C₃ _ _ _ ⟨hf, hC₃, hst₃⟩ => ?_
  subst hf hC₃ hst₃
  refine FAt.bind (fresh_fat (fun _ => we) (wblind_const we _))
    fun entry st₄ C₄ _ _ _ ⟨he, hst₄, hC₄⟩ => ?_
  subst he hst₄ hC₄
  exact FAt.pure ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The invariant past a statement's `emit` and its push**: the trace one event on, the
statement pushed, nothing waiting to be placed. -/
theorem winv_emit {s s' : SSt} {what : String} (hinv : WInv ctx I C st s)
    (h : expectS isEmit what s = .ok s') (X : PStmt) :
    st.rest = .emit :: s'.rest ∧ WInv ctx I C
      { st with rest := s'.rest, out := st.out.push X, lazy := none, used := [],
                shift := none } s' := by
  obtain ⟨ev, hr, he, hl, hd⟩ := expectS_ok h
  have hev : ev = .emit := by cases ev <;> simp_all [isEmit]
  subst hev
  have hst : st.rest = .emit :: s'.rest := by rw [← hinv.rest, hr]
  have hall : allocsOf st.rest = allocsOf s'.rest := by
    rw [hst, allocsOf_other (e := Event.emit) (fun _ _ h => nomatch h)]
  refine ⟨hst, ⟨hinv.cok, rfl, by rw [hl]; exact hinv.vw, hinv.two, hinv.abi, ?_,
    by rw [hd]; exact hinv.ret, by rw [← hall]; exact hinv.nodup, fun v hv => ?_, hinv.chain,
    hinv.pnt, rfl⟩⟩
  · have := hinv.fuel
    rw [hst] at this
    simp only [List.length_cons] at this
    show s'.rest.length ≤ ctx.fuel
    omega
  · rw [hl]
    exact hinv.fresh v (by rw [hall]; exact hv)

/-- **A stage's end**: its `emit`, the chain node pushed, the statement's end. -/
theorem stageEnd_fbat {X : PStmt} {ev : Event} {es : List Event} {what : String}
    (hr : st.rest = ev :: es) (he : isEmit ev = true) :
    FBAt ctx I C st (expect isEmit what >>= fun _ => push X >>= fun _ => endStmt)
      fun _ C' st' => C' = C ∧
        st' = { st with rest := es, out := st.out.push X, lazy := none, used := [],
                        shift := none } := by
  refine FBAt.bind (FBAt.ofFAt (expect_fat hr he)) (fun _ _ _ h => h.1) ?_
  rintro _ st₁ C₁ - - - ⟨-, rfl, rfl⟩
  exact push_end' fun _ => ⟨rfl, rfl⟩

end Cells

end
end LeanVM.Guest.Backend.Complete
