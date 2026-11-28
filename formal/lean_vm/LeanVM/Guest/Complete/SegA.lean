module

public import LeanVM.Guest.Complete.ComposeRd
public import LeanVM.Guest.Memory.SelArm
public import LeanVM.Guest.Memory.Restrict

/-!
# A node's body, placed, segment by segment

`callAtA_nodeRd` takes a node's whole path at once. A long body (`verify_sub`'s `4222`
statements) is proved in windows: `SegA … ss es a a' kc kc' O O' D D' Qs` says the statements `ss`
fall through along the events `es` on each memory's valuation `σ rd`, their `HeapBuf`s placed from
the cursor `a` to `a'`, their callees from `kc` to `kc'` (`KidsAtF`, from the words held `O` and
the data claimed `D` to `O'`, `D'`), agreeing with `σ0` on the calls, loading in the node's own data
`Own`, the region `R` or the data claimed `D'`, every event holding. `segA_append` joins two
windows; `callAtA_segRd` closes a body `ss ++ [.ret vs]` into `CallAtA`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem bases_append : ∀ (b : ℕ) (l l' : List ℕ), bases b (l ++ l') = bases b l ++ bases (b + l.sum) l'
  | b, [], l' => by simp [bases]
  | b, s :: l, l' => by
    rw [List.cons_append, bases, bases, bases_append (b + s) l l', List.sum_cons, Nat.add_assoc]; rfl

theorem heapHintAddrs_append (σ : Val) (a b : List Ev) :
    heapHintAddrs σ (a ++ b) = heapHintAddrs σ a ++ heapHintAddrs σ b := List.flatMap_append

/-- **`KidsAtF` from more words held and more data claimed.** -/
theorem kidsAtF_mono {k : ℕ} {σ : Val} {R : ℕ → Prop} {Pre : Reader → Prop} :
    ∀ (cs : List Call) (O O' : Reader → Prop) (Dacc Dacc' : ℕ → Prop) (Qs : List (Reader → Tree → Prop))
      (cur e : ℕ) (Oend : Reader → Prop) (Dend : ℕ → Prop),
    KidsAtF fs al cert k σ R Pre O Dacc Qs cs cur e Oend Dend → (∀ rd, O' rd → O rd) →
      (∀ i, Dacc i → Dacc' i) → KidsAtF fs al cert k σ R Pre O' Dacc' Qs cs cur e Oend Dend
  | [], O, O', Dacc, Dacc', Qs, cur, e, Oend, Dend, h, hO, hD => by
    rw [KidsAtF] at h ⊢
    exact ⟨h.1, fun rd ho => h.2.1 rd (hO rd ho), fun i hi => hD i (h.2.2 i hi)⟩
  | c :: cs, O, O', Dacc, Dacc', Qs, cur, e, Oend, Dend, h, hO, hD => by
    rw [KidsAtF] at h ⊢
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at h ⊢
      obtain ⟨Bc, ec, Rc, Dc, Oc, hR, hc, hrest⟩ := h
      refine ⟨Bc, ec, Rc, Dc, Oc, fun i hi => (hR i hi).imp_right (hD i), ?_, ?_⟩
      · exact hc.mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
          (fun rd hp => ⟨hp.1, hO rd hp.2⟩) (fun _ _ _ h => h)
      · exact kidsAtF_mono cs _ _ _ _ _ _ _ _ _ hrest (fun rd ho => ⟨hO rd ho.1, ho.2⟩)
          (fun i hi => hi.imp_left (hD i))
    · have ht' : c.taken = false := by simpa using ht
      simp only [ht', Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ⟨h.1, kidsAtF_mono cs _ _ _ _ _ _ _ _ _ h.2 hO hD⟩

/-- **`KidsAtF` over two runs of calls**, the second from what the first ends with. -/
theorem kidsAtF_append {k : ℕ} {σ : Val} {R : ℕ → Prop} {Pre : Reader → Prop} :
    ∀ (cs cs' : List Call) (O O1 O2 : Reader → Prop) (D D1 D2 : ℕ → Prop)
      (Qs Qs' : List (Reader → Tree → Prop)) (cur mid e : ℕ), Qs.length = cs.length →
    KidsAtF fs al cert k σ R Pre O D Qs cs cur mid O1 D1 →
    KidsAtF fs al cert k σ R Pre O1 D1 Qs' cs' mid e O2 D2 →
    KidsAtF fs al cert k σ R Pre O D (Qs ++ Qs') (cs ++ cs') cur e O2 D2
  | [], cs', O, O1, O2, D, D1, D2, Qs, Qs', cur, mid, e, hl, h1, h2 => by
    rw [KidsAtF] at h1
    obtain ⟨rfl, hO, hD⟩ := h1
    have : Qs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this
    exact kidsAtF_mono cs' _ _ _ _ _ _ _ _ _ h2 hO hD
  | c :: cs, cs', O, O1, O2, D, D1, D2, Qs, Qs', cur, mid, e, hl, h1, h2 => by
    obtain ⟨Q, Qs, rfl⟩ : ∃ Q Qt, Qs = Q :: Qt := by
      cases Qs with
      | nil => simp at hl
      | cons Q Qt => exact ⟨Q, Qt, rfl⟩
    have hl' : Qs.length = cs.length := by simpa using hl
    rw [KidsAtF] at h1
    rw [List.cons_append, List.cons_append, KidsAtF]
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte, List.headD_cons, List.tail_cons] at h1 ⊢
      obtain ⟨Bc, ec, Rc, Dc, Oc, hR, hc, hrest⟩ := h1
      exact ⟨Bc, ec, Rc, Dc, Oc, hR, hc, kidsAtF_append cs cs' _ _ _ _ _ _ _ _ _ _ _ hl' hrest h2⟩
    · have ht' : c.taken = false := by simpa using ht
      simp only [ht', Bool.false_eq_true, ↓reduceIte, List.tail_cons] at h1 ⊢
      exact ⟨h1.1, kidsAtF_append cs cs' _ _ _ _ _ _ _ _ _ _ _ hl' h1.2 h2⟩

/-- **A window of a node's body, placed, on a valuation per memory**: the statements `ss` of `f`
(frame `fp`) fall through along `es` on every memory's `σ rd`; their `HeapBuf`s from `a` to `a'`,
their callees from `kc` to `kc'` taking the words held from `O` to `O'` and the data claimed from
`D` to `D'`; on every memory, the allocations, `HeapBuf` pointers and `frameAddr`s placed, the calls'
words `σ0`'s, the loads and heap hints in `Own`, `R` or `D'`, every event holding. -/
def SegA (k : ℕ) (f : String) (fp : ℕ) (σ0 : Val) (σ : Reader → Val) (Own R : ℕ → Prop)
    (Pre : Reader → Prop) (ss : List Stmt) (es : List Ev) (a a' kc kc' : ℕ) (O O' : Reader → Prop)
    (D D' : ℕ → Prop) (Qs : List (Reader → Tree → Prop)) : Prop :=
  a' = a + (allocs σ0 es).sum ∧ Qs.length = (calls es).length ∧ (∀ rd, O' rd → O rd) ∧
    (∀ i, D i → D' i) ∧
    KidsAtF fs al cert k σ0 (fun i => R i ∨ Own i) Pre O D Qs (calls es) kc kc' O' D' ∧
    ∀ rd, LowDef k rd → Pre rd → O' rd →
      walk (σ rd) ss = .fall es ∧ allocs (σ rd) es = allocs σ0 es ∧
      (allocDsts es).map (σ rd) = (bases a (allocs σ0 es)).map (fun b => ofK (addressOfIndex b)) ∧
      (∀ q ∈ addrs es, σ rd q.1 = ofK (addressOfIndex (fp + cert f q.2))) ∧
      VsC.CallsAgree σ0 (σ rd) (calls es) ∧
      (∀ A ∈ loadAddrs (σ rd) es, ∃ i, A = addressOfIndex i ∧ (Own i ∨ R i ∨ D' i)) ∧
      (∀ A ∈ heapHintAddrs (σ rd) es, ∃ i, A = addressOfIndex i ∧ (Own i ∨ R i ∨ D' i)) ∧
      ∀ ev ∈ es, ev.Holds rd (σ rd)

/-- **Two windows, one after the other.** -/
theorem segA_append {k : ℕ} {f : String} {fp : ℕ} {σ0 : Val} {σ : Reader → Val} {Own R : ℕ → Prop}
    {Pre : Reader → Prop} {ss ss' : List Stmt} {es es' : List Ev} {a a1 a2 k0 k1 k2 : ℕ}
    {O O1 O2 : Reader → Prop} {D D1 D2 : ℕ → Prop} {Qs Qs' : List (Reader → Tree → Prop)}
    (h1 : SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 σ Own R Pre ss es a a1 k0 k1 O O1 D D1 Qs)
    (h2 : SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 σ Own R Pre ss' es' a1 a2 k1 k2 O1 O2 D1 D2 Qs') :
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 σ Own R Pre (ss ++ ss') (es ++ es') a a2 k0 k2 O O2
      D D2 (Qs ++ Qs') := by
  obtain ⟨ha1, hl1, hO1, hD1, hk1, hr1⟩ := h1
  obtain ⟨ha2, hl2, hO2, hD2, hk2, hr2⟩ := h2
  refine ⟨by rw [allocs_append, List.sum_append]; omega, by rw [calls_append]; simp [hl1, hl2],
    fun rd h => hO1 rd (hO2 rd h), fun i h => hD2 i (hD1 i h), ?_, fun rd hl hp ho => ?_⟩
  · rw [calls_append]; exact kidsAtF_append _ _ _ _ _ _ _ _ _ _ _ _ _ hl1 hk1 hk2
  obtain ⟨w1, al1, ad1, ar1, ag1, lo1, hh1, ev1⟩ := hr1 rd hl hp (hO2 rd ho)
  obtain ⟨w2, al2, ad2, ar2, ag2, lo2, hh2, ev2⟩ := hr2 rd hl hp ho
  have hreg : ∀ A, (∃ i, A = addressOfIndex i ∧ (Own i ∨ R i ∨ D1 i)) →
      ∃ i, A = addressOfIndex i ∧ (Own i ∨ R i ∨ D2 i) := fun A ⟨i, hi, h⟩ =>
    ⟨i, hi, h.imp_right (Or.imp_right (hD2 i))⟩
  refine ⟨by rw [walk_append, w1, w2]; rfl, by rw [allocs_append, allocs_append, al1, al2], ?_,
    fun q hq => ?_, fun c hc => ?_, fun A hA => ?_, fun A hA => ?_, fun ev hev => ?_⟩
  · rw [allocDsts_append, List.map_append, ad1, ad2, allocs_append, bases_append, List.map_append, ha1]
  · rw [addrs_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ar1 q hq
    · exact ar2 q hq
  · rw [calls_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ag1 c hc
    · exact ag2 c hc
  · rw [loadAddrs_append] at hA
    rcases List.mem_append.mp hA with hA | hA
    · exact hreg A (lo1 A hA)
    · exact lo2 A hA
  · rw [heapHintAddrs_append] at hA
    rcases List.mem_append.mp hA with hA | hA
    · exact hreg A (hh1 A hA)
    · exact hh2 A hA
  · rcases List.mem_append.mp hev with hev | hev
    · exact ev1 ev hev
    · exact ev2 ev hev

/-- **The empty window.** -/
theorem segA_nil {k : ℕ} {f : String} {fp : ℕ} {σ0 : Val} {σ : Reader → Val} {Own R : ℕ → Prop}
    {Pre : Reader → Prop} {a kc : ℕ} {O : Reader → Prop} {D : ℕ → Prop} :
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 σ Own R Pre [] [] a a kc kc O O D D [] := by
  refine ⟨by simp [allocs], by simp [calls], fun _ h => h, fun _ h => h, ?_, fun rd _ _ _ => ?_⟩
  · simp only [calls, List.filterMap_nil]; rw [KidsAtF]; exact ⟨rfl, fun _ h => h, fun _ h => h⟩
  · refine ⟨by rw [walk], by simp [allocs], by simp [allocDsts, allocs, bases], by simp [addrs],
      by simp [VsC.CallsAgree, calls], by simp [loadAddrs], by simp [heapHintAddrs], by simp⟩

/-- **A node closes from one window**: its body `ss ++ [.ret vs]`, `ss` a window from the cursor
`c` past the frame, its callees from the end of its `HeapBuf`s, holding its own words `Wo`. -/
theorem callAtA_segRd {k : ℕ} {f : String} {fn : Fn} {args rets : List E} {R D : ℕ → Prop}
    {Out Pre : Reader → Prop} {Post : Reader → Tree → Prop} {fp c e : ℕ} {ss : List Stmt} {vs : List V}
    (hlp : coreProgram.loop f = false) (hfc : fp + fs f ≤ c) (hf : coreProgram.find? f = some fn)
    (hbody : fn.body = ss ++ [.ret vs]) (σ0 : Val) (σ : Reader → Val) (es : List Ev) (Wo : Words)
    (Qs : List (Reader → Tree → Prop)) (Oend : Reader → Prop) (Dend : ℕ → Prop)
    (hWo : WordsInA Wo (fp + 2) (fp + fs f) c (c + (allocs σ0 es).sum))
    (hD : ∀ i, D i → ownData cert fp c f (allocs σ0 es) es i ∨ Dend i)
    (hseg : SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 σ (ownData cert fp c f (allocs σ0 es) es) R Pre
      ss es c (c + (allocs σ0 es).sum) (c + (allocs σ0 es).sum) e (fun rd => HoldsWords rd Wo) Oend
      (fun _ => False) Dend Qs)
    (hout : ∀ rd, Oend rd → Out rd)
    (hpar : ∀ rd, LowDef k rd → Pre rd → Oend rd → fn.params.map (σ rd) = args ∧ vs.map (σ rd) = rets)
    (hpost : ∀ rd, LowDef k rd → Pre rd → Oend rd → ∀ ts, Tree.KidsValid coreProgram rd (σ rd) (calls es) ts →
      KidsPost rd Qs (calls es) ts → Post rd (.node f (σ rd) (allocs σ0 es) ts)) :
    CallAtA fs al cert k f args rets R D Out Pre Post (fs f) fp c e := by
  obtain ⟨-, -, -, -, hk, hr⟩ := hseg
  refine callAtA_nodeRd hlp hfc ⟨σ0, fn, es, vs, Wo, Qs, Oend, Dend, hf, hWo, hD,
    hk, hout, fun rd hl hp ho => ?_⟩
  obtain ⟨hw, hal, had, har, hag, hlo, hhi, hev⟩ := hr rd hl hp ho
  obtain ⟨hpa, hre⟩ := hpar rd hl hp ho
  refine ⟨σ rd, hpa, ?_, hre, hal, ⟨had, har⟩, hag, hlo, hhi, hev,
    fun ts hv hq => hpost rd hl hp ho ts hv hq⟩
  rw [hbody, walk_append, hw]
  simp [walk, walk1, Memory.Out.seq, Memory.Out.pre]

end
end LeanVM.Guest.Complete
