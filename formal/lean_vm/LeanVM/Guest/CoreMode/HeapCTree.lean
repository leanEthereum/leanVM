/-
  LeanVM.Guest.CoreMode.HeapCTree

  The heap check over an honest call tree: every instance's path is sound, and each callee's
  subtree writes its guarantees.
-/

module

public import LeanVM.Guest.CoreMode.HeapCSound
public import LeanVM.Guest.Memory.Retemp

/-!
# The heap check over a call tree

`heapOkC_sound` is about one instance, a call event writing its callee's guarantees by its signature.
On a valid tree (`Tree.Valid`) whose every function passes `heapOkC` against the certificates'
signatures (`CertsOk`), with every instance's entry facts and residuals (`TreeFacts`), the
signatures are kept: `tree_post`, each instance's guarantees at its words are its preconditions or
written by an atom of its subtree (`treeWr`); `tree_inst`, each instance's path is sound
(`ReadsOkC`, `PostOkC`). By induction over the tree: an entered call's
guarantees are its callee's subtree's writes or its callee's preconditions, which the caller's path
wrote before the call (`written_tree`, by induction on the events before).

**Ghosts.** An instance's ghost words are those its caller's certificate names for its call (`gargsW`, at
the caller's valuation with its own ghost words), the root's none: `TreeFacts P cert t gw` asks each
instance's facts at its valuation with its ghost words (`setG σ gw`), and the theorems are about that
valuation. A function names no ghost value (`noGhost`, in `heapOkC`), so its path and its events' words
are the same at both (`node_sound`). Without ghost words named, `treeFacts_of_treeAll`.

**Words at cells.** An instance's values `DB + k` hold the words at its certificate's cells `ders[k]` in the
memory (`setD`, `instV`), so `DerOk` holds there (`derOk_setD`); `TreeFacts` asks, at each call on the path, the
cells its ghost words read in memory (`DerDef`), which the caller's path wrote before the call (`DerW`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (PowTree)

public section

/-! ## Trees -/

mutual
/-- **The addresses a subtree writes**: an atom of an instance's path, or a frame run's cell of the path
(`FAW`), or a callee's subtree's. -/
@[expose] def treeWr (P : Program) : Tree → K → Prop
  | .node f σ _ kids, x => (∃ fn es vs, P.find? f = some fn ∧ walk σ fn.body = .ret es vs ∧
      ((∃ a, Ev.atom a ∈ es ∧ Writes σ a x) ∨ ∃ fas, FAW σ fas es x)) ∨ kidsWr P kids x
  | .phantom .., _ => False

/-- The addresses the callees' subtrees write. -/
@[expose] def kidsWr (P : Program) : List Tree → K → Prop
  | [], _ => False
  | k :: ks, x => treeWr P k x ∨ kidsWr P ks x
end

mutual
/-- `Q` at every instance of a tree. -/
@[expose] def treeAll (Q : String → Val → Prop) : Tree → Prop
  | .node f σ _ kids => Q f σ ∧ kidsAll Q kids
  | .phantom .. => True

/-- `Q` at every instance of the callees' trees. -/
@[expose] def kidsAll (Q : String → Val → Prop) : List Tree → Prop
  | [] => True
  | k :: ks => treeAll Q k ∧ kidsAll Q ks
end

/-- **An instance's facts**: its entry facts, residuals and own parameter words, under its function's certificate. -/
def FactsAt (P : Program) (cert : String → HCert) (rd : Reader) (f : String) (σ : Val) : Prop :=
  ∀ fn, P.find? f = some fn → EntryF (cert f) (fn.params.map σ) ∧ ResF (cert f) σ ∧ GwOk (cert f).sig rd σ

/-- **A valuation with ghost words**: the values `V.n (GB + j)`, `j` below their count, hold `gw[j]`. -/
def setG (σ : Val) (gw : List E) : Val := fun v ↦
  if v.path = [] ∧ v.tag = 0 ∧ GB ≤ v.idx then (gw[v.idx - GB]?).getD (σ v) else σ v

/-- **A valuation with the words at cells**: the values `V.n (DB + k)` below `GB` hold the word at the cell
`H.ders[k]` (at `σ`), where there is one. -/
def setD (rd : Reader) (H : HCert) (σ : Val) : Val := fun v ↦
  if v.path = [] ∧ v.tag = 0 ∧ DB ≤ v.idx ∧ v.idx < GB then
    (match H.ders[v.idx - DB]? with
    | some c => (rd (c.addrW (vw σ))).getD (σ v)
    | none => σ v)
  else σ v

/-- **An instance's valuation**: `σ` with its ghost words `gw` (`setG`), then its words at cells (`setD`). -/
def instV (rd : Reader) (H : HCert) (σ : Val) (gw : List E) : Val := setD rd H (setG σ gw)

mutual
/-- **Every instance's facts, at its ghost words**: an instance of `f` at `σ` with ghost words `gw` has
its facts at its valuation `instV rd (cert f) σ gw`, the cells its calls' ghost words read in memory
(`DerDef`), and each callee its own facts, at the ghost words its caller's certificate names for the call
(`gargsW`, at the caller's valuation). -/
def TreeFacts (P : Program) (cert : String → HCert) (rd : Reader) : Tree → List E → Prop
  | .node f σ _ kids, gw => FactsAt P cert rd f (instV rd (cert f) σ gw) ∧
      ∀ fn es vs, P.find? f = some fn → walk σ fn.body = .ret es vs →
        (∀ g a r, Ev.call g a r ∈ es → DerDef (cert f) rd (instV rd (cert f) σ gw) g a) ∧
        KidsFacts P cert rd (cert f) (instV rd (cert f) σ gw) (calls es) kids
  | .phantom .., _ => True

/-- The callees' facts, each at the ghost words of its call. -/
def KidsFacts (P : Program) (cert : String → HCert) (rd : Reader) (H : HCert) (σ : Val) : List Call → List Tree → Prop
  | c :: cs, k :: ks => TreeFacts P cert rd k (gargsW H σ c.f c.args) ∧ KidsFacts P cert rd H σ cs ks
  | _, _ => True
end

/-- **Every function's certificate passes**, against the certificates' signatures. -/
def CertsOk (pows : PowTree) (P : Program) (cert : String → HCert) : Prop :=
  ∀ f fn, P.find? f = some fn → heapOkC pows (fun g ↦ (cert g).sig) fn (cert f) = true

/-- **What a subtree keeps of its signature**, called with the ghost words `gw` (as many as it has
ghosts): each guarantee at its words is its precondition at its arguments and `gw`, or written by its
subtree; its returned words are its `retM` monomials; the final memory holds its words at return
(`postV`). -/
def PostT (P : Program) (cert : String → HCert) (rd : Reader) (t : Tree) (args gw rets : List E) : Prop :=
  (gw.length = (cert t.name).sig.ghosts → ∀ x, PostSet rd (cert t.name).sig (args ++ rets) x →
    PreSet rd (cert t.name).sig (args ++ gw) x ∨ treeWr P t x) ∧
  RetMOk (cert t.name).sig args rets ∧ RetVOk rd (cert t.name).sig (args ++ rets) ∧
    RetEqOk (cert t.name).sig (args ++ rets)

theorem kidsWr_of_mem {P : Program} {x : K} : ∀ {ks : List Tree} {k : Tree}, k ∈ ks → treeWr P k x → kidsWr P ks x
  | [], _, hk, _ => by simp at hk
  | k' :: ks, k, hk, h => by
    rcases List.mem_cons.mp hk with rfl | hk
    · exact Or.inl h
    · exact Or.inr (kidsWr_of_mem hk h)

/-! ## Ghost words -/

section Ghost

variable {σ : Val} {gw : List E}

theorem setG_eq {v : V} (h : v.idx < GB) : setG σ gw v = σ v := by
  unfold setG
  split_ifs with h'
  · omega
  · rfl

theorem setG_nil : setG σ [] = σ := funext fun v ↦ by
  unfold setG
  split_ifs <;> simp

theorem ownG_setG {G : HSig} (h : gw.length = G.ghosts) : ownG G (setG σ gw) = gw := by
  refine List.ext_getElem (by simp [ownG, h]) fun j h1 h2 ↦ ?_
  simp only [ownG, List.getElem_map, List.getElem_range, vw, setG, V.n]
  simp [h2]

/-- The values a function names are no ghost's or word at a cell. -/
theorem noGhost_idx {f : Fn} (h : noGhost f = true) {v : V}
    (hv : v ∈ Stmt.usesList f.body ++ Stmt.tmpsList f.body ++ f.params) : v.idx < DB :=
  Nat.blt_eq.mp (List.all_eq_true.mp h v hv)

theorem setD_eq {rd : Reader} {H : HCert} {v : V} (h : v.idx < DB ∨ GB ≤ v.idx) : setD rd H σ v = σ v := by
  unfold setD
  split_ifs with h'
  · omega
  · rfl

theorem setD_nil {rd : Reader} {H : HCert} (h : H.ders = []) : setD rd H σ = σ := funext fun v ↦ by
  unfold setD
  split_ifs
  · simp [h]
  · rfl

theorem instV_eq {rd : Reader} {H : HCert} {v : V} (h : v.idx < DB) : instV rd H σ gw v = σ v := by
  rw [instV, setD_eq (Or.inl h), setG_eq (by unfold DB GB at *; omega)]

theorem instV_nil {rd : Reader} {H : HCert} (h : H.ders = []) : instV rd H σ [] = σ := by
  rw [instV, setD_nil h, setG_nil]

/-- A cell over no word at a cell names the same word with them. -/
theorem valW_setD {rd : Reader} {H : HCert} {c : CCell} (hc : c.bases.all (fun b ↦ Nat.blt b.1 DB || Nat.ble GB b.1)) :
    c.valW (vw (setD rd H σ)) = c.valW (vw σ) := by
  refine valW_congr fun b hb ↦ ?_
  have := List.all_eq_true.mp hc b hb
  simp only [Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at this
  exact setD_eq this

theorem ownG_setD {rd : Reader} {H : HCert} {G : HSig} : ownG G (setD rd H σ) = ownG G σ := by
  simp only [ownG, vw]
  exact List.map_congr_left fun j _ ↦ setD_eq (Or.inr (by simp))

/-- **The words at cells, set from the memory, are the memory's** (`DerOk`). -/
theorem derOk_setD {rd : Reader} {H : HCert} (hd : dersOk H.ders = true) : DerOk H rd (setD rd H σ) := by
  unfold dersOk at hd
  simp only [Bool.and_eq_true] at hd
  intro k c hk w hw
  have hl := Nat.blt_eq.mp hd.1
  have hkl : k < H.ders.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [CCell.addrW, valW_setD (List.all_eq_true.mp hd.2 c (List.mem_of_getElem? hk)), ← CCell.addrW] at hw
  show setD rd H σ (V.n (DB + k)) = w
  unfold setD
  split_ifs with h0
  · simp only [Nat.add_sub_cancel_left, hk, hw, Option.getD_some]
  · exact absurd ⟨rfl, rfl, Nat.le_add_right _ _, by show DB + k < GB; unfold GB DB at *; omega⟩ h0

/-- A heap hint's pointer is a value it names. -/
theorem hintHeap_uses {h : Hint} {p : V} {off len : ℕ} (hh : hintHeap h = some (p, off, len)) : p ∈ hintUses h := by
  cases h <;> simp only [hintHeap] at hh <;> (try split at hh) <;> simp_all [hintUses, destUses]

/-- An atom's writes depend only on the values it names. -/
theorem writes_congr {σ σ' : Val} {a : Atom} (h : ∀ v ∈ atomUses a, σ' v = σ v) (x : K) :
    Writes σ' a x ↔ Writes σ a x := by
  cases a with
  | load d p off => simp only [Writes, cellAt, h p (by simp [atomUses])]
  | hint hn =>
    simp only [Writes]
    constructor
    · rintro ⟨p, off, len, hh, k, hk, rfl⟩
      exact ⟨p, off, len, hh, k, hk, by rw [cellAt, cellAt, h p (by simpa [atomUses] using hintHeap_uses hh)]⟩
    · rintro ⟨p, off, len, hh, k, hk, rfl⟩
      exact ⟨p, off, len, hh, k, hk, by rw [cellAt, cellAt, h p (by simpa [atomUses] using hintHeap_uses hh)]⟩
  | _ => simp [Writes]

/-- An event's check depends only on the values it names. -/
theorem holds_congr {rd : Reader} {σ σ' : Val} {e : Ev} (h : ∀ v ∈ e.uses ++ e.tmps, σ' v = σ v) :
    e.Holds rd σ' ↔ e.Holds rd σ := by
  cases e with
  | atom a => exact Memory.atom_holds_congr a h
  | inK c => simp only [Ev.Holds, h c (by simp [Ev.uses])]
  | call _ _ _ => exact Iff.rfl
  | skip _ _ => exact Iff.rfl

end Ghost

/-! ## Written before, over the tree -/

section Written

variable {sigOf : String → HSig} {H : HCert} {rd : Reader} {σ : Val} {ws0 : List E} {es : List Ev}

/-- **What a path writes, over the tree**: an address written after some of its events is a
precondition's or written by `T`, given that `T` holds each atom's writes and each entered call's
guarantees but its callee's preconditions (at its arguments and the ghost words its call names), the
path's needs being written before each event. -/
theorem written_tree (hreads : ReadsOkC sigOf H rd σ ws0 es) (hdd : ∀ g a r, Ev.call g a r ∈ es → DerDef H rd σ g a)
    {T : K → Prop} (hatom : ∀ a x, Ev.atom a ∈ es → Writes σ a x → T x)
    (hkid : ∀ g a r, Ev.call g a r ∈ es → ∀ x, PostSet rd (sigOf g) ((a ++ r).map σ) x →
      PreSet rd (sigOf g) (a.map σ ++ gargsW H σ g a) x ∨ T x) :
    ∀ (n : ℕ) (es1 es2 : List Ev), es1.length ≤ n → es = es1 ++ es2 → ∀ x,
      WrittenC sigOf H rd σ ws0 es1 x → PreSet rd H.sig (ws0 ++ ownG H.sig σ) x ∨ T x := by
  intro n
  induction n with
  | zero =>
    intro es1 es2 hl _ x hx
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)] at hx
    rcases hx with hx | ⟨e, he, -⟩
    · exact Or.inl hx
    · simp at he
  | succ n ih =>
    intro es1 es2 hl hes x hx
    rcases hx with hx | ⟨e, he, hx⟩
    · exact Or.inl hx
    obtain ⟨A, B, rfl⟩ := List.append_of_mem he
    have hmem : e ∈ es := by rw [hes]; simp
    cases e with
    | atom a => exact Or.inr (hatom a x hmem hx)
    | call g a r =>
      rcases hkid g a r hmem x hx with hx | hx
      · have hreq := (hreads A (.call g a r) (B ++ es2) (by rw [hes]; simp)).2 (hdd g a r hmem)
        have hA : WrittenC sigOf H rd σ ws0 A x := by
          rcases hx with (⟨c, hc, rfl⟩ | ⟨r', hr', hx⟩) | hx
          · exact hreq.2.1.1 c hc
          · exact hreq.2.1.2 r' hr' x hx
          · exact hreq.2.2 x hx
        exact ih A (Ev.call g a r :: B ++ es2) (by simp at hl; omega) (by rw [hes]; simp) x hA
      · exact Or.inr hx
    | inK _ => exact hx.elim
    | skip _ _ => exact hx.elim

end Written

/-! ## The tree -/

section Tree

variable {pows : PowTree} {P : Program} {cert : String → HCert} {rd : Reader}

/-- An entered call's callee, of the tree's callees. -/
theorem kid_of_call {σ : Val} : ∀ {ks : List Tree} {cs : List Call}, Tree.KidsValid P rd σ cs ks →
    ∀ c ∈ cs, c.taken = true → ∃ k ∈ ks, k.name = c.f ∧ k.Valid P rd (c.args.map σ) (c.rets.map σ)
  | [], [], _, c, hc, _ => by simp at hc
  | k :: ks, c :: cs, ⟨hn, hk, hks⟩, c', hc', ht => by
    rcases List.mem_cons.mp hc' with rfl | hc'
    · rw [ite_eq_left ht] at hk
      exact ⟨k, List.mem_cons_self, hn, hk⟩
    · obtain ⟨k', hk', h1, h2⟩ := kid_of_call hks c' hc' ht
      exact ⟨k', List.mem_cons_of_mem _ hk', h1, h2⟩
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

theorem kidsAll_mem {Q : String → Val → Prop} : ∀ {ks : List Tree} {k : Tree}, kidsAll Q ks → k ∈ ks → treeAll Q k
  | [], _, _, hk => by simp at hk
  | k' :: ks, k, h, hk => by
    rcases List.mem_cons.mp hk with rfl | hk
    · exact h.1
    · exact kidsAll_mem h.2 hk

/-- The words at cells of a certificate that passes are checked (`dersOk`). -/
theorem heapOkC_ders {f : Fn} {H : HCert} {sigOf : String → HSig} (h : heapOkC pows sigOf f H = true) :
    dersOk H.ders = true := by
  unfold heapOkC at h
  simp only [Bool.and_eq_true, Exec.Trie.seq_eq] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i st0 hi
    cases hd : dersOk H.ders with
    | true => rfl
    | false => simp [initC, hd] at hi
  · cases h

/-- **An instance, its callees keeping their signatures**: its path at the valuation with its ghost
words is sound (`heapOkC_sound`), and its returned words are its `retM` monomials. The path is the same
at both valuations, its events naming no ghost. -/
theorem node_sound (hp : pows.Ok) (hC : CertsOk pows P cert) {f : String} {σ : Val} {gw : List E}
    {kids : List Tree} {fn : Fn} {es : List Ev} {vs : List V} (hf : P.find? f = some fn)
    (hw : walk σ fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ) (hfa : FactsAt P cert rd f (instV rd (cert f) σ gw))
    (hkids : ∀ c ∈ calls es, c.taken = true → ∃ k ∈ kids, k.name = c.f ∧
      k.Valid P rd (c.args.map σ) (c.rets.map σ) ∧
      PostT P cert rd k (c.args.map σ) (gargsW (cert f) (instV rd (cert f) σ gw) c.f c.args) (c.rets.map σ)) :
    (∀ e ∈ es, ∀ v ∈ e.uses, instV rd (cert f) σ gw v = σ v) ∧ fn.params.map (instV rd (cert f) σ gw) = fn.params.map σ ∧
      vs.map (instV rd (cert f) σ gw) = vs.map σ ∧
      ReadsOkC (fun g ↦ (cert g).sig) (cert f) rd (instV rd (cert f) σ gw) (fn.params.map σ) es ∧
      PostOkC (fun g ↦ (cert g).sig) (cert f) rd (instV rd (cert f) σ gw) (fn.params.map σ) es vs ∧
      RetMOk (cert f).sig (fn.params.map σ) (vs.map σ) ∧ RetVOk rd (cert f).sig (fn.params.map σ ++ vs.map σ) ∧
      RetEqOk (cert f).sig (fn.params.map σ ++ vs.map σ) := by
  have hok := hC f fn hf
  have hng : noGhost fn = true := by
    unfold heapOkC at hok
    simp only [Bool.and_eq_true] at hok
    exact hok.1.1.2
  have hag : ∀ v ∈ Stmt.usesList fn.body ++ Stmt.tmpsList fn.body ++ fn.params, instV rd (cert f) σ gw v = σ v :=
    fun v hv ↦ instV_eq (noGhost_idx hng hv)
  have hw' : walk (instV rd (cert f) σ gw) fn.body = .ret es vs := by
    rw [walk_congr fn.body fun v hv ↦ hag v (by simp [hv]), hw]
  have hwi := walk_within (σ := σ) fn.body
  rw [hw] at hwi
  obtain ⟨hu, ht, hvs⟩ := hwi
  have hev : ∀ e ∈ es, ∀ v ∈ e.uses ++ e.tmps, instV rd (cert f) σ gw v = σ v := fun e he v hv ↦ by
    rcases List.mem_append.mp hv with hv | hv
    · exact hag v (by simp [hu e he v hv])
    · exact hag v (by simp [ht.subset (List.mem_flatMap.mpr ⟨e, he, hv⟩)])
  have hpar : fn.params.map (instV rd (cert f) σ gw) = fn.params.map σ := List.map_congr_left fun v hv ↦ hag v (by simp [hv])
  have hvs' : vs.map (instV rd (cert f) σ gw) = vs.map σ := List.map_congr_left fun v hv ↦ hag v (by simp [hvs v hv])
  have hM : ∀ e ∈ es, EvM (fun g ↦ (cert g).sig) rd (instV rd (cert f) σ gw) e := fun e he ↦ by
    cases e with
    | call g a r =>
      obtain ⟨k, -, hn, -, hkp⟩ := hkids _ (mem_calls_of_call he) rfl
      have hn' : k.name = g := hn
      unfold PostT at hkp
      rw [hn'] at hkp
      have hu' : ∀ v ∈ a ++ r, instV rd (cert f) σ gw v = σ v := fun v hv ↦ hev _ he v (by simp [Ev.uses] at hv ⊢; tauto)
      show RetMOk _ (a.map _) (r.map _) ∧ RetVOk _ _ ((a ++ r).map _) ∧ RetEqOk _ ((a ++ r).map _)
      rw [List.map_congr_left fun v hv ↦ hu' v (List.mem_append_left _ hv),
        List.map_congr_left fun v hv ↦ hu' v (List.mem_append_right _ hv), List.map_congr_left hu',
        List.map_append]
      exact hkp.2
    | atom _ => trivial
    | inK _ => trivial
    | skip _ _ => trivial
  obtain ⟨hE, hR, hG⟩ := hfa fn hf
  obtain ⟨hreads, hpost, hrm, hrv, hre⟩ := heapOkC_sound hp hok (by rw [fn_name_of_find hf]) hw'
    (fun e he ↦ (holds_congr (hev e he)).mpr (hh e he)) hM hE hR (derOk_setD (heapOkC_ders hok)) hG
  rw [hpar] at hreads hpost hrm hrv hre
  rw [hvs'] at hrm hrv hre
  exact ⟨fun e he v hv ↦ hev e he v (List.mem_append_left _ hv), hpar, hvs', hreads, hpost, hrm, hrv, hre⟩

mutual
/-- **Each subtree keeps its signature**: called with as many ghost words as it has ghosts, each
guarantee at its words is its precondition (at its arguments and those ghost words) or written by an
atom of its subtree; its returned words are its `retM` monomials. -/
theorem tree_post (hp : pows.Ok) (hC : CertsOk pows P cert) : ∀ (t : Tree) {args rets gw : List E},
    t.Valid P rd args rets → TreeFacts P cert rd t gw → PostT P cert rd t args gw rets
  | .node f σ bufs kids, args, rets, gw, hv, ht => by
    obtain ⟨fn, hf, hpar, es, vs, hw, hret, hh, hk⟩ := hv
    have hkids := kids_post hp hC kids σ (instV rd (cert f) σ gw) (cert f) (calls es) hk (ht.2 fn es vs hf hw).2
    obtain ⟨hag, hpar', hvs', hreads, hpost, hrm, hrv, hre⟩ := node_sound hp hC hf hw hh ht.1 hkids
    show (gw.length = (cert f).sig.ghosts → ∀ x, PostSet rd (cert f).sig (args ++ rets) x →
      PreSet rd (cert f).sig (args ++ gw) x ∨ treeWr P (.node f σ bufs kids) x) ∧ RetMOk (cert f).sig args rets ∧
      RetVOk rd (cert f).sig (args ++ rets) ∧ RetEqOk (cert f).sig (args ++ rets)
    rw [← hpar, ← hret]
    unfold PostOkC at hpost
    rw [hvs'] at hpost
    refine ⟨fun hlen x hx ↦ ?_, hrm, hrv, hre⟩
    have hW' : WrittenC (fun g ↦ (cert g).sig) (cert f) rd (instV rd (cert f) σ gw) (fn.params.map σ) es x ∨
        FAW (instV rd (cert f) σ gw) (cert f).fas es x := by
      rcases hx with (⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | hx | hx
      · exact hpost.1.1 c hc
      · exact hpost.1.2 r hr x hx
      · exact hpost.2.1 x hx
      · exact hpost.2.2.1 x hx
    rcases hW' with hW | ⟨p, run, i, v, hfa, hv, hd, rfl⟩ | ⟨kp, i, run, hm, hfa, hne, hle, rfl⟩
    rotate_left
    · refine Or.inr (Or.inl ⟨fn, es, vs, hf, hw, Or.inr ⟨(cert f).fas, Or.inl ⟨p, run, i, v, hfa, hv, hd, ?_⟩⟩⟩)
      rw [cellAt, cellAt, hag _ hfa p (by simp [Ev.uses, atomUses])]
    · refine Or.inr (Or.inl ⟨fn, es, vs, hf, hw, Or.inr ⟨(cert f).fas, Or.inr ⟨kp, i, run, hm, hfa, hne, hle, ?_⟩⟩⟩)
      rw [cellAt, cellAt, hag _ hfa (V.n kp) (by simp [Ev.uses, atomUses])]
    have := written_tree hreads (ht.2 fn es vs hf hw).1 (T := treeWr P (.node f σ bufs kids))
      (fun a x ha hx ↦ Or.inl ⟨fn, es, vs, hf, hw, Or.inl ⟨a, ha, (writes_congr (fun v hv ↦ hag _ ha v hv) x).mp hx⟩⟩)
      (fun g a r hg x hx ↦ ?_) es.length es [] le_rfl (by simp) x hW
    · rwa [instV, ownG_setD, ownG_setG hlen] at this
    obtain ⟨k, hk', hn, -, hkp⟩ := hkids _ (mem_calls_of_call hg) rfl
    obtain ⟨A, B, hes⟩ := List.append_of_mem hg
    have hlen' := ((hreads A _ B hes).2 ((ht.2 fn es vs hf hw).1 g a r hg)).1
    have hu' : ∀ v ∈ a ++ r, instV rd (cert f) σ gw v = σ v := fun v hv ↦ hag _ hg v (by simpa [Ev.uses] using hv)
    have ha' : a.map (instV rd (cert f) σ gw) = a.map σ := List.map_congr_left fun v hv ↦ hu' v (List.mem_append_left _ hv)
    have hr' : r.map (instV rd (cert f) σ gw) = r.map σ := List.map_congr_left fun v hv ↦ hu' v (List.mem_append_right _ hv)
    have hn' : k.name = g := hn
    unfold PostT at hkp
    rw [hn'] at hkp
    have := hkp.1 (by rw [gargsW, List.length_map]; exact hlen') x (by rw [List.map_append, ha', hr'] at hx; exact hx)
    rw [ha']
    exact this.imp_right fun h ↦ Or.inr (kidsWr_of_mem hk' h)
  | .phantom .., _, _, _, hv, _ => hv.elim

/-- **The callees keep their signatures**: each entered call's callee, at the ghost words its call
names. -/
theorem kids_post (hp : pows.Ok) (hC : CertsOk pows P cert) : ∀ (ks : List Tree) (σ σ' : Val) (H : HCert)
    (cs : List Call), Tree.KidsValid P rd σ cs ks → KidsFacts P cert rd H σ' cs ks → ∀ c ∈ cs, c.taken = true →
      ∃ k ∈ ks, k.name = c.f ∧ k.Valid P rd (c.args.map σ) (c.rets.map σ) ∧
        PostT P cert rd k (c.args.map σ) (gargsW H σ' c.f c.args) (c.rets.map σ)
  | [], _, _, _, [], _, _, c, hc, _ => by simp at hc
  | k :: ks, σ, σ', H, c :: cs, ⟨hn, hk, hks⟩, ⟨ha, has⟩, c', hc', ht => by
    rcases List.mem_cons.mp hc' with rfl | hc'
    · rw [ite_eq_left ht] at hk
      exact ⟨k, List.mem_cons_self, hn, hk, tree_post hp hC k hk ha⟩
    · obtain ⟨k', hk', h1, h2, h3⟩ := kids_post hp hC ks σ σ' H cs hks has c' hc' ht
      exact ⟨k', List.mem_cons_of_mem _ hk', h1, h2, h3⟩
  | [], _, _, _, _ :: _, h, _, _, _, _ => h.elim
  | _ :: _, _, _, _, [], h, _, _, _, _ => h.elim
end

/-- **Every instance's path is sound**: on a valid tree whose functions pass `heapOkC` against the
certificates' signatures, every instance having its facts at its ghost words, the root's path at the
valuation with its ghost words reads only what is written before and writes its guarantees
(`heapOkC_sound`; the callees' facts give their returned words' monomials, `tree_post`). The path and
its events' words are the same at both valuations (`node_sound`). -/
theorem tree_inst (hp : pows.Ok) (hC : CertsOk pows P cert) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} {args rets gw : List E} (hv : (Memory.Tree.node f σ bufs kids).Valid P rd args rets)
    (ht : TreeFacts P cert rd (.node f σ bufs kids) gw) :
    ∃ fn es vs, P.find? f = some fn ∧ walk σ fn.body = .ret es vs ∧
      (∀ e ∈ es, ∀ v ∈ e.uses, instV rd (cert f) σ gw v = σ v) ∧
      ReadsOkC (fun g ↦ (cert g).sig) (cert f) rd (instV rd (cert f) σ gw) (fn.params.map σ) es ∧
      PostOkC (fun g ↦ (cert g).sig) (cert f) rd (instV rd (cert f) σ gw) (fn.params.map σ) es vs := by
  obtain ⟨fn, hf, -, es, vs, hw, -, hh, hk⟩ := hv
  obtain ⟨hag, -, -, h1, h2, -, -, -⟩ := node_sound hp hC hf hw hh ht.1
    (kids_post hp hC kids σ (instV rd (cert f) σ gw) (cert f) (calls es) hk (ht.2 fn es vs hf hw).2)
  exact ⟨fn, es, vs, hf, hw, hag, h1, h2⟩

/-! ## Without ghosts -/

mutual
/-- **Without ghost words or words at cells named**, every instance's facts at its own valuation are its facts
at its ghost words (none). -/
theorem treeFacts_of_treeAll (hg : ∀ f, (cert f).gargs = []) (hd : ∀ f, (cert f).ders = []) : ∀ (t : Tree),
    treeAll (FactsAt P cert rd) t → TreeFacts P cert rd t []
  | .node f σ _ kids, ht => by
    refine ⟨by rw [instV_nil (hd f)]; exact ht.1, fun fn es vs _ _ ↦ ⟨fun g a r _ k hk ↦ ?_, ?_⟩⟩
    · rw [callDers_nil (hg f)] at hk; cases hk
    rw [instV_nil (hd f)]
    exact kidsFacts_of_kidsAll hg hd (cert f) σ (calls es) kids ht.2 (hg f)
  | .phantom .., _ => trivial

theorem kidsFacts_of_kidsAll (hg : ∀ f, (cert f).gargs = []) (hd : ∀ f, (cert f).ders = []) (H : HCert) (σ : Val) :
    ∀ (cs : List Call) (ks : List Tree), kidsAll (FactsAt P cert rd) ks → H.gargs = [] → KidsFacts P cert rd H σ cs ks
  | c :: cs, k :: ks, ⟨hk, hks⟩, hH => by
    refine ⟨?_, kidsFacts_of_kidsAll hg hd H σ cs ks hks hH⟩
    have : gargsW H σ c.f c.args = [] := by simp [gargsW, gargsOf, hH]
    rw [this]
    exact treeFacts_of_treeAll hg hd k hk
  | [], ks, _, _ => by cases ks <;> simp [KidsFacts]
  | _ :: _, [], _, _ => by simp [KidsFacts]
end

end Tree

end

end LeanVM.Guest.CoreMode
