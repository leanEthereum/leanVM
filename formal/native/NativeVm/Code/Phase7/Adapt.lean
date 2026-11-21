module

public import NativeVm.Code.Phase7.Chunk
public import NativeVm.Code.Phase7.Steps

/-!
# Composing phase 7's pieces

A chain of pieces carries a memory fact `X` (`Dep` on area words). A pure piece (`pure_then`) and a
transcript piece stated from a ghost memory `m0` with the words it writes (`m0_then`) keep the part
`X'` of `X` that reads none of them, and add what they establish. `area_fits`, `area_disj`: the
working area's runs as `Fits` and `Disj`. `foldRounds_roots`, `levelAt_roots`: what the steps do
to the roots.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Env Fits Disj wd_toNat)

variable {p : Par} {X X' : (UInt64 → Option UInt64) → Prop} {D : Nat → Prop}

/-- The kept part of a fact through a piece writing only `Wc`. -/
theorem keepX (hX : Dep p.env X' D) (hD : ∀ j, D j → mineLo ≤ j ∧ j < dataEnd)
    {Wc : Nat → Prop} (hDW : ∀ j, D j → ¬ Wc j) {m0 m : UInt64 → Option UInt64}
    (ho : Only p.env Wc m0 m) (hx : X' m0) : X' m :=
  hX m0 m (fun j hj ↦ ho j (hD j hj).1 (hD j hj).2 (hDW j hj)) hx

/-- **A pure piece**, then the rest. -/
theorem pure_then {β : Type} {c : Stmt} {cs : List Stmt} {m : VM β} {Q : β → TState → QState → Prop}
    {I : TState → Prop} {R : QState → Prop} {Wc : Nat → Prop}
    (hX : Dep p.env X' D) (hD : ∀ j, D j → mineLo ≤ j ∧ j < dataEnd)
    (hDW : ∀ j, D j → ¬ Wc j) (hXX : ∀ m, X m → X' m)
    (hc : ∀ t s, Base p t s → X s.mem → I t →
      WP c s (fun s' ↦ R s' ∧ FrM p.env s s' ∧ Only p.env Wc s.mem s'.mem) (fun _ ↦ False))
    (h : Refines (fun t s ↦ Base p t s ∧ (X' s.mem ∧ R s) ∧ I t) (blk cs) m Q (Err p)) :
    Refines (fun t s ↦ Base p t s ∧ X s.mem ∧ I t) (blk (c :: cs)) m Q (Err p) :=
  Refines.pre_blk (fun t s ⟨hb, hx, hi⟩ ↦ WP.mono (hc t s hb hx hi)
    (fun _ ⟨hr, hf, ho⟩ ↦ ⟨hb.frM hf, ⟨keepX hX hD hDW ho (hXX _ hx), hr⟩, hi⟩)
    fun _ h ↦ h) h

/-- **A transcript piece** from a ghost memory, then the rest. -/
theorem m0_then {α β : Type} {c : Stmt} {cs : List Stmt} {mc : VM α} {m₂ : α → VM β}
    {Q : β → TState → QState → Prop} {I : TState → Prop} {Post : α → TState → QState → Prop}
    {Wc : Nat → Prop}
    (hX : Dep p.env X' D) (hD : ∀ j, D j → mineLo ≤ j ∧ j < dataEnd)
    (hDW : ∀ j, D j → ¬ Wc j) (hXX : ∀ m, X m → X' m)
    (hc : ∀ m0, Refines (fun t s ↦ Base p t s ∧ s.mem = m0 ∧ X s.mem ∧ I t) c mc
      (fun x t s ↦ Base p t s ∧ Post x t s ∧ Only p.env Wc m0 s.mem) (Err p))
    (h : ∀ x, Refines (fun t s ↦ Base p t s ∧ X' s.mem ∧ Post x t s) (blk cs) (m₂ x) Q (Err p)) :
    Refines (fun t s ↦ Base p t s ∧ X s.mem ∧ I t) (blk (c :: cs)) (mc >>= m₂) Q (Err p) := by
  intro t s ⟨hb, hx, hi⟩
  refine Refines.blk_cons (P := fun t' s' ↦ Base p t' s' ∧ s'.mem = s.mem ∧ X s'.mem ∧ I t')
    ((hc s.mem).mono (fun _ _ h ↦ h)
      (fun x t' s' (h : Base p t' s' ∧ Post x t' s' ∧ Only p.env Wc s.mem s'.mem) ↦
        (⟨h.1, keepX hX hD hDW h.2.2 (hXX _ hx), h.2.1⟩ :
          Base p t' s' ∧ X' s'.mem ∧ Post x t' s')) (fun _ h ↦ h)) h t s ⟨hb, rfl, hx, hi⟩

/-- A fact of neither state, pulled into the context. -/
theorem Refines.pull {α : Type} {P : TState → QState → Prop} {R : Prop} {c : Stmt} {m : VM α}
    {Q : α → TState → QState → Prop} {E : QState → Prop} (h : R → Refines P c m Q E) :
    Refines (fun t s ↦ P t s ∧ R) c m Q E := fun t s ⟨hp, hr⟩ ↦ h hr t s hp

theorem sum_take_succ (L : List Whir.Level) {k : Nat} (hk : k < L.length) :
    ((L.take (k + 1)).map (·.fold)).sum = ((L.take k).map (·.fold)).sum + L[k].fold := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append,
    List.sum_append, List.map_singleton, List.sum_singleton]

/-! ## The working area's runs -/

theorem area_fits {p : Par} {s : QState} (hin : Inputs p.env p.inp s.mem) {o n : Nat}
    (ho : o < dataEnd) (h : o + n ≤ dataEnd) : Fits (wd p.env.work o) n := by
  have := workWords_ge p.inp.bytecode.size
  rw [dataEnd_val] at ho h
  exact NativeVm.Transcript.Fits.sub hin.fitWork (by omega) (by omega)

theorem area_disj {p : Par} {s : QState} (hin : Inputs p.env p.inp s.mem) {o n o' n' : Nat}
    (ho : o < dataEnd) (ho' : o' < dataEnd) (hd : o + n ≤ o' ∨ o' + n' ≤ o) :
    Disj (wd p.env.work o) n (wd p.env.work o') n' := by
  have := workWords_ge p.inp.bytecode.size
  rw [dataEnd_val] at ho ho'
  unfold Disj
  rw [wd_toNat hin.fitWork (by omega), wd_toNat hin.fitWork (by omega)]
  omega

/-! ## The roots -/

theorem foldRound_roots (s : WhirStateW) : KeepsRoots (foldRound s) := by
  unfold foldRound
  refine KeepsRoots.readScalar.bind fun _ ↦ KeepsRoots.readScalar.bind fun _ ↦
    KeepsRoots.readScalar.bind fun _ ↦ KeepsRoots.readScalar.bind fun _ ↦
    (KeepsRoots.grind _).bind fun _ ↦ KeepsRoots.sampleChallenge.bind fun _ ↦
    KeepsRoots.sampleChallenge.bind fun _ ↦ KeepsRoots.pure _

theorem foldRounds_roots (n : Nat) (s : WhirStateW) : KeepsRoots (foldRounds n s) :=
  KeepsRoots.foldlM (fun _ _ ↦ (foldRound_roots _).bind fun x ↦ by
    obtain ⟨_, _⟩ := x; exact KeepsRoots.pure _) _ _

end NativeVm.Code.P7
