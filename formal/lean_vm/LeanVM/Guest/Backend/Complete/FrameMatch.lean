/-
  LeanVM.Guest.Backend.Complete.FrameMatch

  A `match` on the path, with the chain of `match`es it starts.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameSelf
public import LeanVM.Guest.Backend.Complete.ScopedRet

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

end Words

/-! ## Arms off the path -/

/-- **An inner block off the path** (`CplFrameSide5`'s `InBlockOff`, with the values the rest of
the trace makes left unplaced): its placement passes the events the scope walk passes, gives the
scope, the statements and the chaining back, moves the next free cell up, grows the places by
values the passed events make or its frame addresses only, and the shared tables. -/
def ArmOff (ctx : Backend.Ctx) (z : List Stmt) : Prop :=
  ∀ (st : St) (sc sc' : SSt),
    scopeInner ctx.retCells (fun s' => scopeBlock ctx.retCells z s') sc = .ok sc' →
    st.rest = sc.rest → st.rest.length ≤ ctx.fuel →
    wpP (inBlock (placeBlock z)) ctx st fun _ st' => st'.rest = sc'.rest ∧
      st'.scope = st.scope ∧ st'.out = st.out ∧ st'.chainIn = st.chainIn ∧ st.next ≤ st'.next ∧
      LocsLe st.locs st'.locs ∧ (st.lazy = none → st'.lazy = none ∧ ∀ v, st'.locs[v]? ≠ none →
        st.locs[v]? ≠ none ∨ v ∈ allocsOf st.rest ∨ ∃ run, Atom.frameAddr v run ∈ atomsIn z) ∧
      (∀ x ∈ st.tables.shared, x ∈ st'.tables.shared) ∧
      ((∀ v ∈ allocsOf st.rest, st.locs[v]? = none) → ∀ v ∈ allocsOf st'.rest, st'.locs[v]? = none)

section Inv

variable {ctx : Backend.Ctx} {I : Inst} {C : (ℕ → E) → Prop}

/-- **The invariant past an arm off the path**: the constraint kept, in lockstep with the scope
walk past the arm (whose values in scope and return area are the ones before it), given that no
value in scope is the target of a frame address of the arm. -/
theorem winv_off {z : List Stmt} {st st' : St} {s s₁ : SSt} (hinv : WInv ctx I C st s)
    (hsc : scopeInner ctx.retCells (fun s' => scopeBlock ctx.retCells z s') s = .ok s₁)
    (hfl : ∀ v run, s.live.contains v = true → Atom.frameAddr v run ∉ atomsIn z)
    (hr : st'.rest = s₁.rest) (hs : st'.scope = st.scope) (hch : st'.chainIn = st.chainIn)
    (hn : st.next ≤ st'.next) (hl : LocsLe st.locs st'.locs)
    (hnew : st.lazy = none → st'.lazy = none ∧ ∀ v, st'.locs[v]? ≠ none →
      st.locs[v]? ≠ none ∨ v ∈ allocsOf st.rest ∨ ∃ run, Atom.frameAddr v run ∈ atomsIn z)
    (hfr : (∀ v ∈ allocsOf st.rest, st.locs[v]? = none) →
      ∀ v ∈ allocsOf st'.rest, st'.locs[v]? = none) :
    WInv ctx I C st' { s₁ with retDone := s.retDone } := by
  obtain ⟨_, _, _, s₄, -, -, -, -, rfl⟩ := scopeInner_inv hsc
  obtain ⟨pre, hpre, -⟩ := scopeInner_cons (scopeBlock_cons ctx.retCells z) hsc
  have hrest : st.rest = pre ++ st'.rest := by rw [← hinv.rest, hpre, hr]
  have hall : allocsOf st.rest = allocsOf pre ++ allocsOf st'.rest := by
    rw [hrest, allocsOf_append]
  obtain ⟨hlz, hnw⟩ := hnew hinv.lazy
  refine ⟨⟨hinv.cok.sat, hinv.cok.blind.mono hn, fun Ψ hΨ => by
      rw [hs]; exact (hinv.cok.pools Ψ hΨ).grow hl, by rw [hs]; exact hinv.cok.cells.mono hn⟩,
    hr.symm, fun v l hv hvl => ?_, le_trans hinv.two hn, le_trans hinv.abi hn, ?_,
    fun hd => hinv.ret hd, ?_, fun v hv => ⟨hfr (fun v hv => (hinv.fresh v hv).1) v hv,
      (hinv.fresh v (by rw [hall]; exact List.mem_append_right _ hv)).2⟩,
    by rw [hch]; exact hinv.chain, by rw [hs]; exact hinv.pnt, hlz⟩
  · have hv' : s.live.contains v = true := hv
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

end
end LeanVM.Guest.Backend.Complete
