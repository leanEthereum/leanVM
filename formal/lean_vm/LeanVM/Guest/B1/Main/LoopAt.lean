/-
  LeanVM.Guest.B1.Main.LoopAt

  The uniform placed completeness by bounded trees (`CompleteAtB`) of a loop helper from its
  iterations, and of a straight-line iteration from its valuation and its callees' `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Uniform
public import LeanVM.Guest.B1.Main.Straight
public import LeanVM.Guest.B1.Tables.VtCSize

/-!
# Loops, placed

A loop helper's iteration `j` is placed at `fp`, its tail call (iteration `j + 1`, or the frame
of the call not taken) right after its frame, its own buffers and callees after the tail's
subtree. `completeAt_loop` composes the iterations from the last one down: each iteration,
given its tail's size `mt`, one size and one layout of its own words serving every memory that
holds them and the caller's words `Lin`, is complete at every `fp`, by a tree within the frames
and the iterations' bounds (`loopSum`).

`loopStep_straight`: an iteration of a straight-line body with no `HeapBuf` and no `frameAddr`,
whose callees before the tail are `CompleteAtB` (`Kid`s reading within `Lin`) and whose loads read
`Lin`, given its valuation on every memory, within its callees' bounds (`kidsBound`).
`kidInf`: the least bound a callee is complete by. `leafLoop_total`: a `mul_range` loop helper with
no callee and no `HeapBuf` is its frames.

`CellL`, `regionL_of_mem`: the words of a layout and where they lie.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtB Returns Kid CallsMatch OutsOk RegionsOk outRegion
  kidsFromIn_of_kidsB kidsBound relAtIn_dmono within_append
  vtc_loop_total vtc_atom)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## Layout words -/

theorem regionL_of_mem {L : Layout} {b k : ℕ} {xs : List E} (hq : (b, xs) ∈ L)
    (hk : k < xs.length) : RegionL L (b + k) :=
  ⟨(b, xs), hq, by simp, by simp only; omega⟩

theorem regionL_mono {L L' : Layout} (h : ∀ q ∈ L, q ∈ L') {i : ℕ} (hi : RegionL L i) :
    RegionL L' i :=
  let ⟨q, hq, h1, h2⟩ := hi; ⟨q, h q hq, h1, h2⟩

theorem memL_mono {rd : Reader} {L L' : Layout} (h : ∀ q ∈ L, q ∈ L') (hL : MemL rd L') :
    MemL rd L := fun q hq => hL q (h q hq)

theorem regionL_append_or {L L' : Layout} {i : ℕ} (h : RegionL (L ++ L') i) :
    RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

/-- **`L` lies within `L'`**: every memory holding `L'` holds `L`, and `L`'s words are `L'`'s. -/
def SubL (L L' : Layout) : Prop := (∀ rd, MemL rd L' → MemL rd L) ∧ ∀ i, RegionL L i → RegionL L' i

theorem SubL.of_mem {L L' : Layout} (h : ∀ q ∈ L, q ∈ L') : SubL L L' :=
  ⟨fun _ hL => memL_mono h hL, fun _ hi => regionL_mono h hi⟩

theorem SubL.append {L1 L2 L' : Layout} (h1 : SubL L1 L') (h2 : SubL L2 L') : SubL (L1 ++ L2) L' :=
  ⟨fun rd hL => memL_append.mpr ⟨h1.1 rd hL, h2.1 rd hL⟩, fun i hi =>
    (regionL_append_or hi).elim (h1.2 i) (h2.2 i)⟩

theorem SubL.trans {L1 L2 L3 : Layout} (h1 : SubL L1 L2) (h2 : SubL L2 L3) : SubL L1 L3 :=
  ⟨fun rd hL => h1.1 rd (h2.1 rd hL), fun i hi => h2.2 i (h1.2 i hi)⟩

/-- A run of an entry's words is within it. -/
theorem SubL.run {L : Layout} {b o : ℕ} {xs ys : List E} (hq : (b, ys) ∈ L)
    (hlen : o + xs.length ≤ ys.length) (h : ∀ k (hk : k < xs.length), xs[k] = ys[o + k]'(by omega)) :
    SubL [(b + o, xs)] L := by
  refine ⟨fun rd hL q hq' => ?_, fun i hi => ?_⟩
  · rw [List.mem_singleton] at hq'; subst hq'
    intro k hk
    have hk' : k < xs.length := hk
    have := hL _ hq (o + k) (by simp only; omega)
    rw [← h k hk'] at this
    refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
    rw [addr_ofK, Nat.add_assoc]
    have h2 := this.2
    rwa [addr_ofK] at h2
  · obtain ⟨q, hq', h1, h2⟩ := hi
    rw [List.mem_singleton] at hq'; subst hq'
    exact ⟨(b, ys), hq, by simp only at h1 ⊢; omega, by simp only at h2 ⊢; omega⟩

/-! ## Bounds -/

/-- **A loop's bound** from iteration `j` with `d` iterations left: each iteration's frame and
bound `bs`, and the frame of the call not taken. -/
def loopSum (c : ℕ) (bs : ℕ → ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => c
  | d + 1 => c + bs j + loopSum c bs (j + 1) d

theorem loopSum_const (c b : ℕ) : ∀ j d : ℕ, loopSum c (fun _ => b) j d = d * (c + b) + c
  | _, 0 => by simp [loopSum]
  | j, d + 1 => by rw [loopSum, loopSum_const c b (j + 1) d]; ring

/-- **The least bound** a callee is complete by. -/
noncomputable def kidInf (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (k : Kid) : ℕ :=
  sInf {B | CompleteAtB fs cert κ k.f k.Lin k.args k.Out B}

theorem kidInf_le {κ : ℕ} {k : Kid} {B : ℕ} (h : CompleteAtB fs cert κ k.f k.Lin k.args k.Out B) :
    kidInf fs cert κ k ≤ B :=
  Nat.sInf_le h

theorem kidInf_le' {κ : ℕ} {f : String} {tk : Bool} {args : List E} {Lin : Layout}
    {Out : List E → Layout → Prop} {B : ℕ} (h : CompleteAtB fs cert κ f Lin args Out B) :
    kidInf fs cert κ ⟨f, tk, args, Lin, Out⟩ ≤ B :=
  Nat.sInf_le h

theorem completeAtB_kidInf {κ : ℕ} {k : Kid} {B : ℕ}
    (h : CompleteAtB fs cert κ k.f k.Lin k.args k.Out B) :
    CompleteAtB fs cert κ k.f k.Lin k.args k.Out (kidInf fs cert κ k) :=
  Nat.sInf_mem (s := {B | CompleteAtB fs cert κ k.f k.Lin k.args k.Out B}) ⟨B, h⟩

/-- **Callees within bounds**: each entered one complete by a tree within its bound, each one not
entered its frame within it. -/
def KidsB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (ks : List Kid) (bs : List ℕ) : Prop :=
  List.Forall₂ (fun k b => (k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args k.Out b) ∧
    (k.taken = false → fs k.f ≤ b)) ks bs

theorem KidsB.complete {κ : ℕ} {ks : List Kid} {bs : List ℕ} (h : KidsB fs cert κ ks bs) :
    ∀ k ∈ ks, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args k.Out (kidInf fs cert κ k) := by
  induction h with
  | nil => intro k hk; simp at hk
  | cons hkb _ ih =>
    intro k hk ht
    rcases List.mem_cons.mp hk with rfl | hk
    · exact completeAtB_kidInf (hkb.1 ht)
    · exact ih k hk ht

theorem KidsB.bound {κ : ℕ} {ks : List Kid} {bs : List ℕ} (h : KidsB fs cert κ ks bs) :
    kidsBound fs (kidInf fs cert κ) ks ≤ bs.sum := by
  induction h with
  | nil => simp [kidsBound]
  | @cons k b ks bs hkb _ ih =>
    simp only [kidsBound, List.map_cons, List.sum_cons] at ih ⊢
    cases ht : k.taken
    · simp only [Bool.false_eq_true, ↓reduceIte]; have := hkb.2 ht; omega
    · simp only [↓reduceIte]; have := kidInf_le (hkb.1 ht); omega

theorem KidsB.append {κ : ℕ} {ks ks' : List Kid} {bs bs' : List ℕ} (h : KidsB fs cert κ ks bs)
    (h' : KidsB fs cert κ ks' bs') : KidsB fs cert κ (ks ++ ks') (bs ++ bs') :=
  List.rel_append h h'

theorem mem_of_getElem? {l : List Core.Stmt} {s : Core.Stmt} (i : ℕ) (h : l[i]? = some s) : s ∈ l :=
  List.mem_of_getElem? h

/-- **A `mul_range` loop helper with no callee and no `HeapBuf`**: its valid trees over `m`
iterations are within its `m + 1` frames. -/
theorem leafLoop_total {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre : List Stmt} {ps : List V} {a b c d e : V}
    (hb : fn.body = pre ++ [.callIf c f (e :: .n 1 :: ps), .ret []])
    (hp : fn.params = .n 0 :: .n 1 :: ps)
    (hst : pre.all Stmt.straight = true) (hna : pre.filterMap Stmt.allocSz = [])
    (hcs : pre.filterMap Stmt.callS = [])
    (ha : Core.Stmt.atom (.const a (word 2 0 0)) ∈ pre) (hb1 : Core.Stmt.atom (.mul b (.n 0) a) ∈ pre)
    (hc : Core.Stmt.atom (.add c b (.n 1)) ∈ pre) (hd : Core.Stmt.atom (.const d (word 2 0 0)) ∈ pre)
    (he : Core.Stmt.atom (.mul e (.n 0) d) ∈ pre)
    {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = f) (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * fs f + fs f := by
  have key := vtc_loop_total (fs := fs) hf hb hst hna rd m rest 0 ?_ m 0 t rets (by omega) hm hn
    (by rwa [pow_zero]) hbo
  · simpa using key
  intro σ j _ hpσ hes
  rw [hp] at hpσ
  simp only [List.map_cons, List.cons.injEq] at hpσ
  obtain ⟨h0, h1, hr⟩ := hpσ
  have xa := vtc_atom hes ha
  have xb := vtc_atom hes hb1
  have xc := vtc_atom hes hc
  have xd := vtc_atom hes hd
  have xe := vtc_atom hes he
  simp only [Atom.Holds, word_gen] at xa xb xc xd xe
  refine ⟨by rw [xc, xb, xa, h0, h1], by simp [xe, xd, h0, h1, hr], fun kids hk _ => ?_⟩
  rw [hcs] at hk
  match kids, hk with
  | [], _ => simp [Tree.totalKids]

/-! ## The iterations -/

/-- **A loop helper is complete from its iterations**: iteration `j < m`, its tail of size `mt`
right after its frame (a `RelAtIn` when `j + 1 < m`, the frame of the call not taken otherwise),
is complete at every `fp` with one size, at most `bs j`, and one layout of its own words from
`fp + fs f + mt`. -/
theorem completeAt_loop {f : String} (κ : ℕ) (Lin : Layout) (A : ℕ → List E) (m : ℕ)
    (bs : ℕ → ℕ)
    (step : ∀ j < m, ∀ fp mt : ℕ, ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧
      n ≤ bs j ∧ ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) →
        (j + 1 < m → RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          (A (j + 1)) []) →
        (j + 1 = m → mt = fs f) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f
          (A j) []) :
    ∀ j < m, CompleteAtB fs cert κ f Lin (A j) (Returns []) (loopSum (fs f) bs j (m - j)) := by
  have key : ∀ t j, j + t + 1 = m →
      CompleteAtB fs cert κ f Lin (A j) (Returns []) (loopSum (fs f) bs j (t + 1)) := by
    intro t
    induction t with
    | zero =>
      intro j hj fp
      obtain ⟨n, L, hW, hD, hn, hS⟩ := step j (by omega) fp (fs f)
      refine ⟨fs f + fs f + n, L, [], [], ⟨rfl, rfl⟩, ?_, by simpa using hD,
        by simp only [loopSum]; omega, fun rd hl hL => ?_⟩
      · simpa using hW.mono (by omega) (by omega)
      · refine relAtIn_dmono (hS rd hl (by simpa using hL) (fun h => by omega) (fun _ => rfl))
          fun i hi => ?_
        obtain ⟨q, hq, _⟩ := hi; simp at hq
    | succ t ih =>
      intro j hj fp
      obtain ⟨nt, Lt, rt, Lo, ⟨rfl, rfl⟩, hWt, hDt, hnt, hSt⟩ := ih (j + 1) (by omega) (fp + fs f)
      obtain ⟨n, L, hW, hD, hn, hS⟩ := step j (by omega) fp nt
      simp only [List.nil_append] at hWt hDt
      refine ⟨fs f + nt + n, Lt ++ L, [], [], ⟨rfl, rfl⟩, ?_, by simpa using disj_append hDt hD hWt hW le_rfl,
        by rw [loopSum]; omega, fun rd hl hL => ?_⟩
      · simp only [List.nil_append]
        rw [within_append]
        exact ⟨hWt.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
      · simp only [List.nil_append, List.append_assoc] at hL
        obtain ⟨hL1, hL2⟩ := memL_append.mp hL
        refine relAtIn_dmono (hS rd hl hL2 (fun _ => ?_) (fun h => by omega)) fun i hi => ?_
        · refine relAtIn_dmono (hSt rd hl (by simpa using memL_append.mpr ⟨hL1, (memL_append.mp hL2).2⟩))
            fun i hi => ?_
          exact hi.elim
        · obtain ⟨q, hq, _⟩ := hi; simp at hq
  intro j hj
  have := key (m - 1 - j) j (by omega)
  rwa [show m - 1 - j + 1 = m - j by omega] at this

/-! ## A straight-line iteration -/

theorem regionsOk_of_sub {R : ℕ → Prop} : ∀ (Dacc : ℕ → Prop) (ks : List Kid)
    (outs : List (List E × Layout)), (∀ k ∈ ks, ∀ i, RegionL k.Lin i → R i) →
    RegionsOk R Dacc ks outs
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | Dacc, k :: ks, o :: os, h => ⟨fun _ i hi => Or.inl (h k (by simp) i hi),
      regionsOk_of_sub _ ks os fun k' hk' => h k' (by simp [hk'])⟩

/-- **A straight-line loop iteration, placed**: the body `pre ++ [ret []]` places nothing, its
callees before the tail are the `Kid`s `ks` (each `CompleteAtB` by `bd`, reading within `Lin`),
and on every memory holding their words and `Lin`, for their results, a valuation satisfies the
body with the frames matching the kids and loads reading `Lin`. -/
theorem loopStep_straight {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) {pre : List Stmt} (hb : fn.body = pre ++ [.ret []])
    (hs : pre.all Stmt.straight = true) (hal : pre.filterMap Stmt.allocSz = [])
    (had : pre.filterMap Stmt.addrS = []) (κ : ℕ) (Lin : Layout) (args : List E)
    (fronts : List (Option V × String × List V × List V)) (tc : V) (targs : List V)
    (hcs : pre.filterMap Stmt.callS = fronts ++ [(some tc, f, targs, [])])
    (ks : List Kid) (bd : Kid → ℕ)
    (hks : ∀ k ∈ ks, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args k.Out (bd k))
    (hsub : ∀ k ∈ ks, ∀ q ∈ k.Lin, q ∈ Lin)
    (targs' : List E) (more : Bool) (fp mt : ℕ)
    (hσ : ∀ rd, LowDef κ rd → MemL rd Lin → ∀ outs, OutsOk ks outs → ∃ σ : Val,
      fn.params.map σ = args ∧
      Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = []) ∧
      CallsMatch σ (fronts.map (mkCall σ)) ks outs ∧ decide (σ tc ≠ 0) = more ∧
      targs.map σ = targs' ∧
      ∀ q ∈ pre.filterMap LeanVM.Guest.B1.Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧ RegionL Lin i) :
    ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧ n ≤ kidsBound fs bd ks ∧
      ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) →
        (more = true → RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          targs' []) →
        (more = false → mt = fs f) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f args [] := by
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromIn_of_kidsB (fs := fs) (cert := cert) κ bd ks hks
    (fp + fs f + mt + 0)
  refine ⟨N, L, by simpa using hW, hD, hNb, fun rd hlow hL htail hnot => ?_⟩
  obtain ⟨hL1, hL2⟩ := memL_append.mp hL
  obtain ⟨σ, hp, hH, hcm, htk, hta, hld⟩ := hσ rd hlow hL2 outs ho
  have hwf : Stmt.wfList coreProgram fn.body = true :=
    coreProgram_wf fn (List.mem_of_find?_eq_some hf)
  have hw := walk_straight σ [] pre hs
  rw [← hb] at hw
  have hsat := walk_sat fn.body hwf hH
  rw [hw] at hsat
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ pre hs
  rw [hal] at e1 e2
  rw [had] at e3
  rw [hcs, List.map_append] at e4
  have hld' := LeanVM.Guest.B1.loadAddrs_straight σ pre hs
  have hc : (mkCall σ (some tc, f, targs, [])).taken = more := htk
  have hsumz : (allocs σ (pre.flatMap (Main.slEvs σ))).sum = 0 := by rw [e2]; rfl
  have := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := fun _ => False) (Dk := fun i => False ∨ outRegion ks outs i) (Rt := RegionL Lin)
    (Dt := fun _ => False) (fp := fp) (m := mt) (N := N) (σ := σ) (rd := rd) coreProgram_wf hf hl hp hw rfl
    (fun e he => (hsat.1 e he).1) e4 ?_ (by rw [e1, e2]; rfl) (by rw [e3]; simp) ?_
    (fun i hi => Or.inl hi) ?_ (fun i hi => hi.elim)
  · rwa [hsumz, Nat.add_zero] at this
  · cases more with
    | true =>
      simp only [hc, ↓reduceIte]
      simp only [mkCall, List.map_nil]
      rw [hta]
      exact htail rfl
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact hnot rfl
  · rw [hsumz]
    have hK' := hK rd σ _ (fun i => RegionL Lin i ∨ ownData cert fp (fp + fs f + mt) f
      (allocs σ (pre.flatMap (Main.slEvs σ))) (pre.flatMap (Main.slEvs σ)) i) (fun _ => False) hcm hlow
      hL1 (memL_mono (fun q hq => by
        obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hq
        exact hsub k hk q hq) hL2)
      (regionsOk_of_sub _ _ _ fun k hk i hi => Or.inl (regionL_mono (hsub k hk) hi))
    exact hK'
  · intro A hA
    rw [hld', List.mem_map] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    obtain ⟨i, hi, hr⟩ := hld q hq
    exact ⟨i, hi, Or.inr (Or.inl hr)⟩

/-- **A straight-line loop iteration with its own buffers, placed**: as `loopStep_straight`, the
body's `HeapBuf`s of sizes `sizes` from `fp + fs f + mt`, holding `bufs`, and its callees reading
within `Lin` and those buffers. -/
theorem loopStep_bufs {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) {pre : List Stmt} (hb : fn.body = pre ++ [.ret []])
    (hs : pre.all Stmt.straight = true) (AL : List (V × (ℕ ⊕ V))) (hal : pre.filterMap Stmt.allocSz = AL)
    (had : pre.filterMap Stmt.addrS = []) (κ : ℕ) (Lin : Layout) (args : List E)
    (fronts : List (Option V × String × List V × List V)) (tc : V) (targs : List V)
    (hcs : pre.filterMap Stmt.callS = fronts ++ [(some tc, f, targs, [])])
    (sizes : List ℕ) (bufs : List (List E)) (hbl : List.Forall₂ (fun c s => c.length ≤ s) bufs sizes)
    (fp mt : ℕ) (ks : List Kid) (bd : Kid → ℕ)
    (hks : ∀ k ∈ ks, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args k.Out (bd k))
    (hsub : ∀ k ∈ ks, SubL k.Lin (bufL (fp + fs f + mt) sizes bufs ++ Lin))
    (targs' : List E) (more : Bool)
    (hσ : ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f + mt) sizes bufs ++ Lin) → ∀ outs, OutsOk ks outs →
      ∃ σ : Val, fn.params.map σ = args ∧
      Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = []) ∧
      AL.map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
      (AL.map Prod.fst).map σ = (bases (fp + fs f + mt) sizes).map (fun b => ofK (gpow b)) ∧
      CallsMatch σ (fronts.map (mkCall σ)) ks outs ∧ decide (σ tc ≠ 0) = more ∧
      targs.map σ = targs' ∧
      ∀ q ∈ pre.filterMap LeanVM.Guest.B1.Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
        (RegionL Lin i ∨ RegionL (bufL (fp + fs f + mt) sizes bufs) i)) :
    ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧
      n ≤ sizes.sum + kidsBound fs bd ks ∧
      ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) →
        (more = true → RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          targs' []) →
        (more = false → mt = fs f) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f args [] := by
  set Lb := bufL (fp + fs f + mt) sizes bufs with hLb
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromIn_of_kidsB (fs := fs) (cert := cert) κ bd ks hks
    (fp + fs f + mt + sizes.sum)
  refine ⟨sizes.sum + N, Lb ++ L, ?_,
    disj_append (bufL_disj _ _ _ hbl) hD (LeanVM.Guest.B1.bufL_within _ _ _ hbl) hW le_rfl,
    by omega, fun rd hlow hL htail hnot => ?_⟩
  · rw [within_append]
    exact ⟨(LeanVM.Guest.B1.bufL_within _ _ _ hbl).mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
  rw [List.append_assoc] at hL
  obtain ⟨hLb, hL'⟩ := memL_append.mp hL
  obtain ⟨hL1, hL2⟩ := memL_append.mp hL'
  obtain ⟨σ, hp, hH, hsz, hdst, hcm, htk, hta, hld⟩ := hσ rd hlow (memL_append.mpr ⟨hLb, hL2⟩) outs ho
  have hwf : Stmt.wfList coreProgram fn.body = true :=
    coreProgram_wf fn (List.mem_of_find?_eq_some hf)
  have hw := walk_straight σ [] pre hs
  rw [← hb] at hw
  have hsat := walk_sat fn.body hwf hH
  rw [hw] at hsat
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ pre hs
  rw [hal] at e1 e2
  have hsz' := e2.trans hsz
  rw [had] at e3
  rw [hcs, List.map_append] at e4
  have hld' := LeanVM.Guest.B1.loadAddrs_straight σ pre hs
  have hc : (mkCall σ (some tc, f, targs, [])).taken = more := htk
  have hown : ∀ i, RegionL Lb i → ownData cert fp (fp + fs f + mt) f (allocs σ (pre.flatMap (slEvs σ)))
      (pre.flatMap (slEvs σ)) i := fun i hi => by
    rw [hsz']
    exact Or.inl (LeanVM.Guest.B1.bufL_region _ _ _ hbl i hi)
  have := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := fun _ => False) (Dk := fun i => False ∨ outRegion ks outs i) (Rt := RegionL Lin)
    (Dt := fun _ => False) (fp := fp) (m := mt) (N := N) (σ := σ) (rd := rd) coreProgram_wf hf hl hp hw rfl
    (fun e he => (hsat.1 e he).1) e4 ?_ (by rw [e1, hsz']; exact hdst) (by rw [e3]; simp) ?_
    (fun i hi => Or.inl hi) ?_ (fun i hi => hi.elim)
  · rwa [hsz', Nat.add_assoc] at this
  · cases more with
    | true =>
      simp only [hc, ↓reduceIte]
      simp only [mkCall, List.map_nil]
      rw [hta]
      exact htail rfl
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact hnot rfl
  · have hsum : (allocs σ (pre.flatMap (slEvs σ))).sum = sizes.sum := by rw [hsz']
    rw [hsum]
    exact hK rd σ _ _ (fun _ => False) hcm hlow hL1
      (LeanVM.Guest.B1.memL_lins fun k hk => (hsub k hk).1 rd (memL_append.mpr ⟨hLb, hL2⟩))
      (regionsOk_of_sub _ _ _ fun k hk i hi =>
        (regionL_append_or ((hsub k hk).2 i hi)).elim (fun h => Or.inr (hown i h)) Or.inl)
  · intro A hA
    rw [hld', List.mem_map] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    obtain ⟨i, hi, hr⟩ := hld q hq
    exact ⟨i, hi, hr.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inl (hown i h)⟩

end
end LeanVM.Guest.B1.Main
