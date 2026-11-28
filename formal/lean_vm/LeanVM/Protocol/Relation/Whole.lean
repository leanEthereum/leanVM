/-
  LeanVM.Protocol.Relation.Whole

  The leanVM verifier program's doom certificate: from no doom, every group within `2^-125`
  after its grind, an accepting run good.
-/

module

public import LeanVM.Protocol.Relation.Body
public import LeanVM.Protocol.Compile.SpecRules.Cert
public import LeanVM.Protocol.Whir.Params.RingSound

/-!
# The certificate of the leanVM verifier

`leanVmProgramG` is the verifier program returning its verdict, the announced sizes and the
stacked opening's trace; dropping them it is `leanVmVerifierProgram` (`leanVmProgramG_eq`). An
accepting run is **good** (`GoodRun`) when the trace the ghost returns there is good from the bad
stacks (`OpeningIface.TraceGood`, `StackBad`): its descent ends on a candidate of the stack's word
that satisfies the relation. **`leanVmCert`**: the certificate the random-oracle theorem takes,
accepting from doom only good runs, every escape within `2^-125` after its grind
(`leanVmCert_bound`). It rests on the phases' interfaces and on ring switching's facts
(`RingFactsOf`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Params
open LeanVM.Protocol.Whir.Sound (WhirTrace)
open scoped ENNReal

@[expose] public section

/-! ## Accepting at the root -/

section AtRoot

variable {α : Type} {p : VerifierProgram α} {Post : α → List Ev → Prop} {εmax L T : ℝ≥0∞}

open Classical in
/-- **A specification of a whole program run from the empty history** also gives, where it
returns in doom, that the history is a run of the program to that value. -/
noncomputable def Spec.atRoot (S : Spec p (fun _ ↦ False) Post εmax L T) :
    Spec p (fun _ ↦ False) (fun a h ↦ Post a h ∧ p.after h = some (.ret a)) εmax L T where
  D h₀ l := S.D h₀ l ∧ h₀ = []
  V h₀ l := if h₀ = [] then S.V h₀ l else 1
  le_one h₀ l := by split_ifs; exacts [S.le_one h₀ l, le_rfl]
  start_D _ h := h.elim
  start_V _ h := h.elim
  read x hl ha hD := ⟨S.read x hl ha hD.1, hD.2⟩
  readPacked xs hl ha hn hD := ⟨S.readPacked xs hl ha hn hD.1, hD.2⟩
  grind hl ha hD := ⟨S.grind hl ha hD.1, hD.2⟩
  commit word hl ha hw hD := ⟨S.commit word hl ha hw hD.1, hD.2⟩
  sample {h₀ l k} hl ha := by
    by_cases h0 : h₀ = []
    · simp only [h0, ↓reduceIte]; exact S.sample (h0 ▸ hl) ha
    · simp only [h0, ↓reduceIte]; exact avg_le_one _ fun _ ↦ le_rfl
  samplePacked {h₀ l n k} hl ha := by
    by_cases h0 : h₀ = []
    · simp only [h0, ↓reduceIte]; exact S.samplePacked (h0 ▸ hl) ha
    · simp only [h0, ↓reduceIte]; exact (avgPk_const _ _).le
  query {h₀ l i ps k rows} hl ha hans := by
    by_cases h0 : h₀ = []
    · simp only [h0, ↓reduceIte]; exact S.query (h0 ▸ hl) ha (by simpa [h0] using hans)
    · simp [h0]
  moveEnd {h₀ l q} hl ha hm hD := by
    by_cases h0 : h₀ = []
    · simp only [h0, ↓reduceIte]
      exact S.moveEnd (h0 ▸ hl) ha hm fun hd ↦ hD ⟨h0 ▸ hd, h0⟩
    · simp [h0]
  retEnd {h₀ l a} hl ha hD := by
    by_cases h0 : h₀ = []
    · simp only [h0, ↓reduceIte]
      exact S.retEnd (h0 ▸ hl) ha fun hd ↦ hD ⟨h0 ▸ hd, h0⟩
    · simp [h0]
  retDoom {h₀ l a} hl ha hD := by
    simp only [hD.2, ↓reduceIte]
    exact S.retDoom (hD.2 ▸ hl) ha (hD.2 ▸ hD.1)
  post {h₀ l a} hl ha hD := by
    obtain ⟨hd, rfl⟩ := hD
    exact ⟨S.post hl ha hd, by simpa using ha⟩
  bound {h₀ l} hl hne hm hD := by
    simp only [hD.2, ↓reduceIte]
    exact S.bound (hD.2 ▸ hl) hne hm (hD.2 ▸ hD.1)

end AtRoot

/-! ## The verifier, returning its data -/

/-- The leanVM verifier program, returning its verdict, the announced sizes and the stacked
opening's trace. -/
def leanVmProgramG (bytecode : List K) (input : PublicInput) :
    VerifierProgram (Bool × ((Layout × ℕ) × WhirTrace)) :=
  (readAnnouncedSizes bytecode).bind fun a ↦
    (veBodyG a.1 a.2 input).bind fun tr ↦ VerifierProgram.ret (true, (a, tr))

theorem leanVmProgramG_eq (bytecode : List K) (input : PublicInput) :
    (leanVmProgramG bytecode input).bind (fun r ↦ VerifierProgram.ret r.1) =
      leanVmVerifierProgram bytecode (publicInputDigest input) := by
  simp only [leanVmProgramG, leanVmVerifierProgram, verifyExecution_eq, VerifierProgram.bind_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind, VerifierProgram.pure_eq]

/-- **Ring switching's facts** for every announced layout and every front result of its shape. -/
def RingFactsOf (input : PublicInput) (bytecode : List K) : Prop :=
  ∀ (layout : Layout) (ρ : ℕ), Announced bytecode layout ρ → ∀ qk,
    layout.placements.getD qkeccak none = some qk → ∀ r, FrontShape layout input r →
      RingFacts layout.stackLog (ringsOf qk r)

/-- **Ring switching's facts hold** (`ringFacts_of_shape`). -/
theorem ringFactsOf_holds (input : PublicInput) (bytecode : List K) : RingFactsOf input bytecode :=
  fun _ _ hA _ hqk _ hr ↦
    ringFacts_of_shape (announced_built hA).1.choose_spec.choose_spec hr.1 hr.2.2 hqk

variable (O : OpeningIface) (LI : LinkIface)

/-- The data an accepting run returns is good. -/
def GoodAt (input : PublicInput) (d : (Layout × ℕ) × WhirTrace) (cs : List (ℕ × ℕ × Word)) :
    Prop :=
  O.TraceGood d.1.1.stackLog d.1.2 (StackBad LI input d.1.1) d.2 cs

/-- **A good run**: wherever the verifier accepts after the history, the data its ghost returns
there is good. -/
def GoodRun (bytecode : List K) (input : PublicInput) (h : List Ev) : Prop :=
  ∀ d, (leanVmProgramG bytecode input).after h = some (.ret (true, d)) →
    GoodAt O LI input d (commits h)

theorem bind_D_of_none {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {Pre : List Ev → Prop} {Post : α → List Ev → Prop} {Q : β → List Ev → Prop}
    {εmax L T Lf : ℝ≥0∞} (S : Spec p Pre Post εmax L Lf) (F : ∀ a, Spec (f a) (Post a) Q εmax Lf T)
    {h₀ l : List Ev} (hp : p.retSplit l = none) (hD : S.D h₀ l) : (S.bind F).D h₀ l := by
  rw [Spec.bind_D]
  exact (Spec.bindD_none hp).mpr hD

theorem bind_D_of_some {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {Pre : List Ev → Prop} {Post : α → List Ev → Prop} {Q : β → List Ev → Prop}
    {εmax L T Lf : ℝ≥0∞} (S : Spec p Pre Post εmax L Lf) (F : ∀ a, Spec (f a) (Post a) Q εmax Lf T)
    {h₀ l l₁ l₂ : List Ev} {a : α} (hp : p.retSplit l = some (a, l₁, l₂)) (hne : l₂ ≠ [])
    (hD : (F a).D (h₀ ++ l₁) l₂) : (S.bind F).D h₀ l := by
  rw [Spec.bind_D]
  exact (Spec.bindD_after hp hne).mpr hD

/-- The placements the body needs, of an announced layout. -/
def Placed (layout : Layout) : Prop :=
  ∃ qk p0 p1 : Placement, layout.placements.getD qkeccak none = some qk ∧
    layout.placements.getD memory0 none = some p0 ∧ layout.placements.getD memory1 none = some p1

open Classical in
/-- `verify_execution`'s body at the announced data, returning the data. -/
noncomputable def bodyDataSpec (KI : KeccakIface) (input : PublicInput) {bytecode : List K}
    (hRF : RingFactsOf input bytecode) (a : Layout × ℕ) :
    Spec ((veBodyG a.1 a.2 input).bind fun tr ↦ VerifierProgram.ret (true, (a, tr)))
      (fun _ ↦ False) (fun r h ↦ GoodAt O LI input r.2 (commits h)) εmsg 0 0 :=
  if hA : Announced bytecode a.1 a.2 then
    if hp : Placed a.1 then
      (bodySpec O LI KI input (announced_built hA).1.choose_spec.choose_spec hA
        hp.choose_spec.choose_spec.choose_spec.1 hp.choose_spec.choose_spec.choose_spec.2.1
        hp.choose_spec.choose_spec.choose_spec.2.2
        (hRF a.1 a.2 hA _ hp.choose_spec.choose_spec.choose_spec.1)).bind fun tr ↦
        Spec.ret (Post := fun (r : Bool × ((Layout × ℕ) × WhirTrace)) h ↦
          GoodAt O LI input r.2 (commits h)) (εmax := εmsg) (T := 0) (true, (a, tr))
    else Spec.dead
  else Spec.dead

theorem readOod_bind_ne_ret {β : Type} (μ : ℕ) (f : StackClaim → VerifierProgram β) (b : β) :
    (readOod μ).bind f ≠ .ret b := by
  intro h
  obtain ⟨c, hc, -⟩ := bind_eq_ret_iff h
  simp [readOod, VerifierProgram.grindProofOfWork, Whir.oodGrindingBits, VerifierProgram.bind] at hc

/-- Right after the root, the body has not returned. -/
theorem veBodyG_after_commit {layout : Layout} {ρ : ℕ} {input : PublicInput} {e : Ev}
    (hce : (commitStack layout.stackLog ρ).after [e] = some (.ret ())) {β : Type}
    (g : WhirTrace → VerifierProgram β) :
    ((veBodyG layout ρ input).bind g).retSplit [e] = none := by
  rcases h : ((veBodyG layout ρ input).bind g).retSplit [e] with _ | ⟨b, l₁, l₂⟩
  · rfl
  · obtain ⟨h1, h2⟩ := VerifierProgram.retSplit_eq_some_iff.mp h
    rw [veBodyG_eq] at h2
    simp only [VerifierProgram.bind_assoc] at h2
    exfalso
    rcases l₁ with _ | ⟨e', l₁⟩
    · simp only [VerifierProgram.after, Option.some.injEq] at h2
      obtain ⟨u, hcs, -⟩ := bind_eq_ret_iff h2
      obtain ⟨_, _, _, -, hm⟩ := commitStack_after_ret (logN := layout.stackLog)
        (logInvRate := ρ) (m := []) (by rw [hcs]; rfl)
      simp at hm
    · have hl : l₁ = [] ∧ e' = e := by
        cases l₁ <;> simp_all
      obtain ⟨rfl, rfl⟩ := hl
      rw [show [e'] = [e'] ++ [] from rfl, VerifierProgram.after_bind_append _ hce] at h2
      simp only [VerifierProgram.after, Option.some.injEq] at h2
      exact readOod_bind_ne_ret _ _ _ h2

theorem congr_D_eq {α : Type} {p p' : VerifierProgram α} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {εmax L T : ℝ≥0∞} (h : p = p') (S : Spec p Pre Post εmax L T)
    (h₀ l : List Ev) : (S.congr h).D h₀ l ↔ S.D h₀ l := by
  cases h; rfl

/-- **Right after the root, the body's doom is level 0's shape**, at the announced data. -/
theorem bodyDataSpec_D_commit (KI : KeccakIface) (input : PublicInput) {bytecode : List K}
    (hRF : RingFactsOf input bytecode) {a : Layout × ℕ} (hA : Announced bytecode a.1 a.2)
    (hp : Placed a.1) {h₀ : List Ev} {e : Ev}
    (hce : (commitStack a.1.stackLog a.2).after [e] = some (.ret ()))
    (hpost : O.ShapeOK₀ a.1.stackLog a.2 (commits (h₀ ++ [e]))) :
    (bodyDataSpec O LI KI input hRF a).D h₀ [e] := by
  unfold bodyDataSpec
  simp only [hA, hp, ↓reduceDIte]
  refine bind_D_of_none _ _ (by
    have := veBodyG_after_commit (input := input) hce VerifierProgram.ret
    rwa [VerifierProgram.bind_ret] at this) ?_
  unfold bodySpec
  rw [congr_D_eq]
  exact bodySpecRaw_D_commit O LI KI input _ hA _ _ _ _ hce hpost

/-- The verifier program's specification on its ghost form. -/
@[irreducible] noncomputable def leanVmSpecG (KI : KeccakIface) (bytecode : List K) (input : PublicInput)
    (hRF : RingFactsOf input bytecode) :
    Spec ((leanVmProgramG bytecode input).bind fun r ↦ VerifierProgram.ret r.1) (fun _ ↦ False)
      (fun b h ↦ b = false ∨ GoodRun O LI bytecode input h) εmsg 0 0 :=
  (Spec.atRoot ((Spec.dead (p := readAnnouncedSizes bytecode)
      (Post := fun _ _ ↦ False) (εmax := εmsg) (L := 0) (T := 0)).bind
    (bodyDataSpec O LI KI input hRF)) |>.bind fun (r : Bool × ((Layout × ℕ) × WhirTrace)) ↦
    (Spec.ret (Post := fun b h ↦ b = false ∨ GoodRun O LI bytecode input h) (T := 0) r.1).mono
      (fun h hp ↦ Or.inr fun d hd ↦ by
        unfold leanVmProgramG at hd
        have h2 := hp.2
        rw [h2] at hd
        obtain rfl := (VerifierProgram.ret.inj (Option.some.inj hd))
        exact hp.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)

/-- **The specification of the leanVM verifier program**: from no doom, every group at most
`2^-125` after its grind, lead `0`, and an accepting return in doom a good run. -/
@[irreducible] noncomputable def leanVmSpec (KI : KeccakIface) (bytecode : List K) (input : PublicInput)
    (hRF : RingFactsOf input bytecode) :
    Spec (leanVmVerifierProgram bytecode (publicInputDigest input)) (fun _ ↦ False)
      (fun b h ↦ b = false ∨ GoodRun O LI bytecode input h) εmsg 0 0 :=
  (leanVmSpecG O LI KI bytecode input hRF).congr (leanVmProgramG_eq bytecode input)

/-- **The doom certificate of the leanVM verifier**, accepting from doom only good runs. -/
noncomputable def leanVmCert (KI : KeccakIface) (bytecode : List K) (input : PublicInput)
    (hRF : RingFactsOf input bytecode) :
    CertG (leanVmVerifierProgram bytecode (publicInputDigest input))
      (GoodRun O LI bytecode input) :=
  (leanVmSpec O LI KI bytecode input hRF).toCertG

theorem Spec.congr_D' {α : Type} {p p' : VerifierProgram α} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {εmax L T : ℝ≥0∞} (h : p = p') (S : Spec p Pre Post εmax L T) :
    (S.congr h).D = S.D := by
  cases h; rfl

theorem retSplit_nil_of_ne {β : Type} {p : VerifierProgram β} (hp : ∀ a, p ≠ .ret a) :
    p.retSplit [] = none := by
  rcases h : p.retSplit [] with _ | ⟨a, l₁, l₂⟩
  · rfl
  · obtain ⟨h1, h2⟩ := VerifierProgram.retSplit_eq_some_iff.mp h
    obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp h1.symm
    simp only [VerifierProgram.after, Option.some.injEq] at h2
    exact absurd h2 (hp a)

theorem readAnnouncedSizes_retSplit_nil' (bytecode : List K) :
    (readAnnouncedSizes bytecode).retSplit [] = none :=
  retSplit_nil_of_ne fun _ h ↦ by cases h

theorem readAnnouncedSizes_retSplit_nil (bytecode : List K) {β : Type}
    (f : Layout × ℕ → VerifierProgram β) :
    ((readAnnouncedSizes bytecode).bind f).retSplit [] = none :=
  retSplit_nil_of_ne fun _ h ↦ by cases h

section DNil

variable {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
  {Pre : List Ev → Prop} {Post : α → List Ev → Prop} {Q : β → List Ev → Prop} {εmax L T Lf : ℝ≥0∞}

theorem bind_D_nil (S : Spec p Pre Post εmax L Lf) (F : ∀ a, Spec (f a) (Post a) Q εmax Lf T)
    (hp : p.retSplit [] = none) (hD : (S.bind F).D [] []) : S.D [] [] := by
  rw [Spec.bind_D] at hD
  exact (Spec.bindD_none hp).mp hD

theorem atRoot_D {S : Spec p (fun _ ↦ False) Post εmax L T} {h₀ l : List Ev}
    (hD : (Spec.atRoot S).D h₀ l) : S.D h₀ l := hD.1

theorem dead_D {h₀ l : List Ev} (hD : (Spec.dead : Spec p (fun _ ↦ False) Post εmax L T).D h₀ l) :
    False := hD

end DNil

theorem congr_D_nil {α : Type} {p p' : VerifierProgram α} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {εmax L T : ℝ≥0∞} (h : p = p') (S : Spec p Pre Post εmax L T)
    (hS : ¬ S.D [] []) : ¬ (S.congr h).D [] [] := by
  cases h; exact hS

theorem leanVmProgramG_retSplit_nil (bytecode : List K) (input : PublicInput) :
    (leanVmProgramG bytecode input).retSplit [] = none :=
  readAnnouncedSizes_retSplit_nil bytecode _


theorem leanVmSpecG_D_nil (KI : KeccakIface) (bytecode : List K) (input : PublicInput)
    (hRF : RingFactsOf input bytecode) : ¬ (leanVmSpecG O LI KI bytecode input hRF).D [] [] := by
  intro hD
  unfold leanVmSpecG at hD
  have h1 := bind_D_nil (p := leanVmProgramG bytecode input) (f := fun r ↦ VerifierProgram.ret r.1)
    _ _ (leanVmProgramG_retSplit_nil bytecode input) hD
  have h2 := atRoot_D h1
  exact dead_D (bind_D_nil (p := readAnnouncedSizes bytecode)
    (f := fun a ↦ (veBodyG a.1 a.2 input).bind fun tr ↦ VerifierProgram.ret (true, (a, tr)))
    _ _ (readAnnouncedSizes_retSplit_nil' bytecode) h2)

/-- Doom never holds at the empty history: the announced sizes are not at stake. -/
theorem leanVmSpec_D_nil (KI : KeccakIface) (bytecode : List K) (input : PublicInput)
    (hRF : RingFactsOf input bytecode) : ¬ (leanVmSpec O LI KI bytecode input hRF).D [] [] := by
  unfold leanVmSpec
  exact congr_D_nil _ _ (leanVmSpecG_D_nil O LI KI bytecode input hRF)

/-- **The certificate's bound**: every escape bound, discounted by the proof of work before its
group, is at most `2^-125`. -/
theorem leanVmCert_bound (KI : KeccakIface) (bytecode : List K) (input : PublicInput)
    (hRF : RingFactsOf input bytecode) (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ grindBits h * (leanVmCert O LI KI bytecode input hRF).ε h ≤ εmsg :=
  Spec.toCertG_bound _ (fun hD ↦ absurd hD (leanVmSpec_D_nil O LI KI bytecode input hRF)) h

/-! ## Doom right after the stack's root -/

section Prefix

variable {α β : Type}

/-- A program returns along at most one prefix of a history. -/
theorem ret_prefix_unique {p : VerifierProgram α} {l l' hist : List Ev} {a a' : α}
    (h1 : l <+: hist) (h2 : l' <+: hist) (ha : p.after l = some (.ret a))
    (ha' : p.after l' = some (.ret a')) : l = l' := by
  have key : ∀ {m m' : List Ev} {b b' : α}, m <+: m' → p.after m = some (.ret b) →
      p.after m' = some (.ret b') → m = m' := by
    intro m m' b b' hp hb hb'
    obtain ⟨t, rfl⟩ := hp
    rw [VerifierProgram.after_append, hb, Option.bind_some] at hb'
    rcases t with _ | ⟨e, t⟩
    · simp
    · cases e <;> simp [VerifierProgram.after] at hb'
  rcases List.prefix_or_prefix_of_prefix h1 h2 with hp | hp
  · exact key hp ha ha'
  · exact (key hp ha' ha).symm

/-- Where the first part returns along a prefix and the rest does not return along the rest, the
sequence does not return along the whole. -/
theorem retSplit_bind_none {p : VerifierProgram α} {f : α → VerifierProgram β} {l₁ l₂ : List Ev}
    {a : α} (h1 : p.after l₁ = some (.ret a)) (h2 : (f a).retSplit l₂ = none) :
    (p.bind f).retSplit (l₁ ++ l₂) = none := by
  rcases h : (p.bind f).retSplit (l₁ ++ l₂) with _ | ⟨b, m₁, m₂⟩
  · rfl
  · exfalso
    obtain ⟨hm, hr⟩ := VerifierProgram.retSplit_eq_some_iff.mp h
    obtain ⟨a', k₁, k₂, rfl, hk₁, hk₂⟩ := after_bind_ret hr
    have hk : k₁ = l₁ := ret_prefix_unique (hist := l₁ ++ l₂) ⟨k₂ ++ m₂, by simp [hm]⟩
      ⟨l₂, rfl⟩ hk₁ h1
    subst hk
    rw [hk₁, Option.some.injEq, VerifierProgram.ret.injEq] at h1
    subst h1
    have hl₂ : l₂ = k₂ ++ m₂ := by simpa [List.append_assoc] using hm
    rw [hl₂, VerifierProgram.retSplit_of_after _ _ _ hk₂] at h2
    cases h2

end Prefix

/-- **Right after the stack's root, the certificate's doom is level 0's shape**: along a history
where the announced sizes returned and the root was committed. -/
theorem leanVmSpec_D_commit (KI : KeccakIface) (bytecode : List K) (input : PublicInput)
    (hRF : RingFactsOf input bytecode) {l₁ : List Ev} {a : Layout × ℕ}
    (hl₁ : (readAnnouncedSizes bytecode).after l₁ = some (.ret a)) (hp : Placed a.1) {e : Ev}
    (hce : (commitStack a.1.stackLog a.2).after [e] = some (.ret ()))
    (hpost : O.ShapeOK₀ a.1.stackLog a.2 (commits (l₁ ++ [e]))) :
    (leanVmSpec O LI KI bytecode input hRF).D [] (l₁ ++ [e]) := by
  unfold leanVmSpec
  rw [congr_D_eq]
  unfold leanVmSpecG
  refine bind_D_of_none _ _ (retSplit_bind_none hl₁ (veBodyG_after_commit hce _)) ?_
  refine ⟨?_, rfl⟩
  refine bind_D_of_some _ _ (VerifierProgram.retSplit_of_after _ l₁ [e] hl₁)
    (List.cons_ne_nil _ _) ?_
  rw [List.nil_append]
  exact bodyDataSpec_D_commit O LI KI input hRF (returns_of_after hl₁) hp hce hpost

/-- The certificate's doom is the specification's from the empty history. -/
theorem leanVmCert_D (KI : KeccakIface) (bytecode : List K) (input : PublicInput)
    (hRF : RingFactsOf input bytecode) (h : List Ev) :
    (leanVmCert O LI KI bytecode input hRF).D h ↔ (leanVmSpec O LI KI bytecode input hRF).D [] h :=
  Iff.rfl

end

end LeanVM.Protocol.Relation
