/-
  LeanVM.Guest.B1.Tables.VtC.SLoads

  Where `verify_tables`' loads of statements `0 ..< 765` read: in `dims_g`, `table_rows`, the
  exponent table, the four group buffers and `idxc_tab`, some through computed pointers.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SAll
public import LeanVM.Guest.B1.Tables.VtC.InBuf

/-!
# The loads of statements `0 ..< 765`

A load through a computed pointer (`p = base · x`, `x = g^a` with `a` bounded) lands in `base`'s
buffer when `a + off` is below its length. `ptrRun` tracks, statement by statement, what the
holding statements say of the variables: `PF.pw e` (`σ v = g^a`, `a ≤ e`: a constant
`word (2^k)`, a product of two such, a word read from a buffer whose words are such) and
`PF.pt b e` (`σ v = σ b · g^a`, `a ≤ e`), and checks every load against the buffers
(`ptrRun_sound`). `vtS_loads`: statements `0 ..< 765`, whose loads read `dims_g` (`7`),
`table_rows` (`6`), the exponent table (`236`, at `σ12 · g^κ` and `σ12 · g^gi`), the group buffers
(`24` each, also at `σ(33+i) · g^gi`) and `idxc_tab` (`34`), from `dims_g`'s words (`g^` at most
`32`) and the group order's (`g^` at most `23`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The pointer check -/

/-- A variable's index, when it is a plain `.n i`. -/
def vIdx (v : V) : Option ℕ := if v.path = [] ∧ v.tag = 0 then some v.idx else none

theorem vIdx_eq {v : V} {i : ℕ} (h : vIdx v = some i) : v = .n i := by
  unfold vIdx at h
  split_ifs at h with hc
  obtain ⟨p, t, j⟩ := v
  simp only [Option.some.injEq] at h
  simp only at hc
  rw [hc.1, hc.2, h]

/-- What the statements say of a variable. -/
inductive PF where
  /-- `σ v = g^a`, `a ≤ e`. -/
  | pw (e : ℕ)
  /-- `σ v = σ b · g^a`, `a ≤ e`. -/
  | pt (b e : ℕ)

/-- The fact holds. -/
def PF.Holds (σ : Val) (v : ℕ) : PF → Prop
  | .pw e => ∃ a ≤ e, σ (.n v) = gen ^ a
  | .pt b e => ∃ a ≤ e, σ (.n v) = σ (.n b) * gen ^ a

/-- The first entry of a key. -/
def assocGet {α : Type} (l : List (ℕ × α)) (k : ℕ) : Option α :=
  (l.find? (fun q ↦ q.1 == k)).map (·.2)

theorem assocGet_mem {α : Type} {l : List (ℕ × α)} {k : ℕ} {a : α} (h : assocGet l k = some a) :
    (k, a) ∈ l := by
  unfold assocGet at h
  cases hq : l.find? (fun q ↦ q.1 == k) with
  | none => rw [hq] at h; simp at h
  | some q =>
    rw [hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have h1 := List.find?_some hq
    have h2 := List.mem_of_find?_eq_some hq
    simp only [beq_iff_eq] at h1
    rw [← h1, ← h]
    exact h2

/-- The fact a product gives. -/
def pfMul (F : List (ℕ × PF)) (x y : ℕ) : Option PF :=
  match assocGet F x, assocGet F y with
  | some (.pw e1), some (.pw e2) => some (.pw (e1 + e2))
  | _, some (.pw e) => some (.pt x e)
  | some (.pw e), _ => some (.pt y e)
  | _, _ => none

/-- The fact a constant gives: `word (2^k)` for `k ∈ ks`. -/
def constFact (ks : List ℕ) (c : E) : Option PF :=
  (ks.find? (fun k ↦ decide (k < 64) && tbEEqb c (word (2 ^ k) 0))).map PF.pw

/-- The fact a load gives: a word of a buffer whose words at `offs` are `g^` at most `c`. -/
def loadFact (pws : List (ℕ × ℕ × List ℕ)) (p off : ℕ) : Option PF :=
  match assocGet pws p with
  | some (c, offs) => if offs.contains off then some (.pw c) else none
  | none => none

/-- A load lands in a buffer. -/
def loadOk (bs : List (ℕ × ℕ)) (F : List (ℕ × PF)) (p off : ℕ) : Bool :=
  match assocGet bs p with
  | some l => decide (off < l)
  | none => match assocGet F p with
    | some (.pt b e) => match assocGet bs b with
      | some l => decide (e + off < l)
      | none => false
    | _ => false

/-- Record a fact of `d`. -/
def ptrAdd (d : V) (f : Option PF) (F : List (ℕ × PF)) : List (ℕ × PF) :=
  match vIdx d, f with
  | some i, some f => (i, f) :: F
  | _, _ => F

/-- **The pointer check**: every load lands in a buffer of `bs` (variable, length). -/
def ptrRun (bs : List (ℕ × ℕ)) (pws : List (ℕ × ℕ × List ℕ)) (ks : List ℕ) :
    List (ℕ × PF) → List Stmt → Bool
  | _, [] => true
  | F, .atom (.load d p off) :: r =>
    match vIdx p with
    | some i => loadOk bs F i off && ptrRun bs pws ks (ptrAdd d (loadFact pws i off) F) r
    | none => false
  | F, .atom (.const d c) :: r => ptrRun bs pws ks (ptrAdd d (constFact ks c) F) r
  | F, .atom (.mul d x y) :: r =>
    match vIdx x, vIdx y with
    | some i, some j => ptrRun bs pws ks (ptrAdd d (pfMul F i j) F) r
    | _, _ => ptrRun bs pws ks F r
  | F, _ :: r => ptrRun bs pws ks F r

section
variable {C : CallRel} {rd : Reader} {σ : Val}

theorem assocGet_holds {F : List (ℕ × PF)} (hF : ∀ q ∈ F, q.2.Holds σ q.1) {v : ℕ} {f : PF}
    (h : assocGet F v = some f) : f.Holds σ v := hF _ (assocGet_mem h)

theorem pfMul_sound {F : List (ℕ × PF)} (hF : ∀ q ∈ F, q.2.Holds σ q.1) {d x y : ℕ} {f : PF}
    (hm : σ (.n d) = σ (.n x) * σ (.n y)) (h : pfMul F x y = some f) : f.Holds σ d := by
  unfold pfMul at h
  split at h
  · rename_i e1 e2 h1 h2
    obtain ⟨a1, ha1, e1'⟩ := assocGet_holds hF h1
    obtain ⟨a2, ha2, e2'⟩ := assocGet_holds hF h2
    cases h
    exact ⟨a1 + a2, by omega, by rw [hm, e1', e2', pow_add]⟩
  · rename_i e h2 _
    obtain ⟨a, ha, e'⟩ := assocGet_holds hF h2
    cases h
    exact ⟨a, ha, by rw [hm, e']⟩
  · rename_i e h1 _
    obtain ⟨a, ha, e'⟩ := assocGet_holds hF h1
    cases h
    exact ⟨a, ha, by rw [hm, e', mul_comm]⟩
  · cases h

theorem constFact_sound {ks : List ℕ} {c : E} {d : ℕ} {f : PF} (hc : σ (.n d) = c)
    (h : constFact ks c = some f) : f.Holds σ d := by
  unfold constFact at h
  cases hk : ks.find? (fun k ↦ decide (k < 64) && tbEEqb c (word (2 ^ k) 0)) with
  | none => rw [hk] at h; simp at h
  | some k =>
    rw [hk] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have h1 := List.find?_some hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    subst h
    exact ⟨k, le_rfl, by rw [hc, tbEEqb_sound h1.2, tb_word_two_pow h1.1]⟩

theorem ptrAdd_holds {F : List (ℕ × PF)} (hF : ∀ q ∈ F, q.2.Holds σ q.1) {d : V} {fo : Option PF}
    (h : ∀ i f, vIdx d = some i → fo = some f → f.Holds σ i) :
    ∀ q ∈ ptrAdd d fo F, q.2.Holds σ q.1 := by
  unfold ptrAdd
  cases hd : vIdx d with
  | none => exact hF
  | some i =>
    cases hfo : fo with
    | none => exact hF
    | some f =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h i f hd hfo
      · exact hF q hq

theorem loadOk_sound {bufs : List (E × ℕ)} {bs : List (ℕ × ℕ)}
    (hb : ∀ q ∈ bs, (σ (.n q.1), q.2) ∈ bufs) {F : List (ℕ × PF)}
    (hF : ∀ q ∈ F, q.2.Holds σ q.1) {p off : ℕ} (h : loadOk bs F p off = true) :
    InBuf σ bufs (.n p) off := by
  unfold loadOk at h
  split at h
  · rename_i l hl
    exact vt_inBuf_direct (hb _ (assocGet_mem hl)) (by simpa using h)
  · split at h
    · rename_i b e hp
      split at h
      · rename_i l hl
        obtain ⟨a, ha, e'⟩ := assocGet_holds hF hp
        exact ⟨_, hb _ (assocGet_mem hl), a, e', by simp at h; omega⟩
      · cases h
    · cases h

theorem loadsInBuf_cons {bufs : List (E × ℕ)} {s : Stmt} {r : List Stmt}
    (h1 : ∀ d p off, s = .atom (.load d p off) → InBuf σ bufs p off)
    (h2 : LoadsInBuf σ bufs r) : LoadsInBuf σ bufs (s :: r) := by
  intro d p off hm
  rcases List.mem_cons.mp hm with e | hm
  · exact h1 d p off e.symm
  · exact h2 d p off hm

/-- **The pointer check is sound**: on holding statements, from holding facts, every load lands
in a buffer. -/
theorem ptrRun_sound {bufs : List (E × ℕ)} {bs : List (ℕ × ℕ)} {pws : List (ℕ × ℕ × List ℕ)}
    {ks : List ℕ} (hb : ∀ q ∈ bs, (σ (.n q.1), q.2) ∈ bufs)
    (hpw : ∀ q ∈ pws, ∀ j ∈ q.2.2, ∀ v, LoadHolds rd (σ (.n q.1)) j v → ∃ a ≤ q.2.1, v = gen ^ a) :
    ∀ (blk : List Stmt) (F : List (ℕ × PF)), (∀ q ∈ F, q.2.Holds σ q.1) →
      (∀ s ∈ blk, VSH C rd σ s) → ptrRun bs pws ks F blk = true → LoadsInBuf σ bufs blk
  | [], _, _, _, _ => fun _ _ _ hm ↦ absurd hm List.not_mem_nil
  | s :: r, F, hF, hV, hr => by
    have hV' : ∀ s ∈ r, VSH C rd σ s := fun s hs ↦ hV s (List.mem_cons_of_mem _ hs)
    have hs := hV s List.mem_cons_self
    have skip : ∀ F', (∀ q ∈ F', q.2.Holds σ q.1) → ptrRun bs pws ks F' r = true →
        (∀ d p off, s ≠ .atom (.load d p off)) → LoadsInBuf σ bufs (s :: r) := fun F' hF' h hn ↦
      loadsInBuf_cons (fun d p off e ↦ absurd e (hn d p off))
        (ptrRun_sound hb hpw r F' hF' hV' h)
    cases s with
    | atom a =>
      cases a with
      | load d p off =>
        simp only [ptrRun] at hr
        split at hr
        · rename_i i hi
          rw [Bool.and_eq_true] at hr
          obtain ⟨h1, h2⟩ := hr
          have hp := vIdx_eq hi
          subst hp
          refine loadsInBuf_cons (fun d' p' off' e ↦ ?_) (ptrRun_sound hb hpw r _ ?_ hV' h2)
          · simp only [Stmt.atom.injEq, Atom.load.injEq] at e
            obtain ⟨-, rfl, rfl⟩ := e
            exact loadOk_sound hb hF h1
          · refine ptrAdd_holds hF fun j f hj hf ↦ ?_
            have hd := vIdx_eq hj
            subst hd
            unfold loadFact at hf
            split at hf
            · rename_i c offs hq
              split_ifs at hf with ho
              cases hf
              have hl : LoadHolds rd (σ (.n i)) off (σ (.n j)) := hs
              exact hpw _ (assocGet_mem hq) off (by simpa using ho) _ hl
            · cases hf
        · cases hr
      | const d c =>
        simp only [ptrRun] at hr
        refine skip _ (ptrAdd_holds hF fun j f hj hf ↦ ?_) hr (by simp)
        have hd := vIdx_eq hj
        subst hd
        exact constFact_sound hs hf
      | mul d x y =>
        simp only [ptrRun] at hr
        split at hr
        · rename_i i j hi hj
          have hx := vIdx_eq hi
          have hy := vIdx_eq hj
          subst hx hy
          refine skip _ (ptrAdd_holds hF fun k f hk hf ↦ ?_) hr (by simp)
          have hd := vIdx_eq hk
          subst hd
          exact pfMul_sound hF hs hf
        · exact skip F hF hr (by simp)
      | _ => exact skip F hF (by simpa [ptrRun] using hr) (by simp)
    | _ => exact skip F hF (by simpa [ptrRun] using hr) (by simp)

end


/-! ## Statements `0 ..< 765` -/

/-- The buffers statements `0 ..< 765` load from: `dims_g`, `table_rows`, the exponent table, the
group buffers, `idxc_tab`. -/
def vtBufsSIdx : List (ℕ × ℕ) :=
  [(10, 7), (11, 6), (12, 236), (33, 24), (34, 24), (35, 24), (36, 24), (664, 34)]

/-- The buffers the pointers' exponents come from: `dims_g` (`g^` at most `32`), the group order
at the push and the pull side's slots (`g^` at most `23`). -/
def vtPwsS : List (ℕ × ℕ × List ℕ) :=
  [(10, 32, List.range 7), (36, 23, List.range 9 ++ (List.range 6).map (18 + ·))]

theorem vtS_ptr_check : ptrRun vtBufsSIdx vtPwsS [0, 19] [] ((vtPre.drop 0).take 765) = true := by
  simp only [vtPre_drop]; decide +kernel

theorem pw_of_reads {rd : Reader} {p : E} {ws : List E} (h : TbReadsAt rd p ws) {c : ℕ} {j : ℕ}
    (hj : j < ws.length) (hw : ∃ a ≤ c, ws.getD j 0 = gen ^ a) {v : E} (hl : LoadHolds rd p j v) :
    ∃ a ≤ c, v = gen ^ a := by
  obtain ⟨a, ha, e⟩ := hw
  refine ⟨a, ha, ?_⟩
  rw [← tb_loadHolds_unique (h j hj) hl, ← e, List.getD_eq_getElem _ _ hj]

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **Where statements `0 ..< 765` load**: in `dims_g`, `table_rows`, the exponent table, the
group buffers and `idxc_tab`, on `dims_g`'s and the group order's honest words. -/
theorem vtS_loads {bufs : List (E × ℕ)}
    (hV : ∀ s ∈ (vtPre.drop 0).take 765, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s)
    (hb : ∀ q ∈ vtBufsSIdx, (vtσ rd w args (.n q.1), q.2) ∈ bufs) {lm : ℕ} (hlm : lm ≤ 32)
    {τ : ℕ → ℕ} (hτ : ∀ t < 6, τ t < 29)
    (hdims : TbReadsAt rd (vtσ rd w args (.n 10)) (gen ^ lm :: (vtTauList τ).map (gen ^ ·)))
    (hord : TbReadsAt rd (vtσ rd w args (.n 36)) (vtGOrdW lm τ)) :
    LoadsInBuf (vtσ rd w args) bufs ((vtPre.drop 0).take 765) := by
  refine ptrRun_sound hb (fun q hq j hj v hl ↦ ?_) _ [] (by simp) hV vtS_ptr_check
  simp only [vtPwsS, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> dsimp only at hj hl ⊢
  · simp only [List.mem_range] at hj
    refine pw_of_reads hdims (by simp [vtTauList]; omega) ?_ hl
    rcases j with _ | j
    · exact ⟨lm, hlm, rfl⟩
    · refine ⟨τ j, by have := hτ j (by omega); omega, ?_⟩
      simp [vtTauList, List.getD_eq_getElem?_getD, show j < 6 by omega]
  · simp only [List.mem_append, List.mem_range, List.mem_map] at hj
    refine pw_of_reads hord (by simp [vtGOrdW]; omega) ?_ hl
    rcases hj with hj | ⟨i, hi, rfl⟩
    · refine ⟨vtPi lm τ 0 j, ?_, ?_⟩
      · have := vtPi_lt (lm := lm) (τ := τ) (s := 0) (r := j) (by simp [vtGm]; omega)
        simp [vtGm] at this; omega
      · simp [vtGOrdW, List.getD_eq_getElem?_getD, show j < 24 by omega, hj]
    · refine ⟨18 + vtPi lm τ 2 i, ?_, ?_⟩
      · have := vtPi_lt (lm := lm) (τ := τ) (s := 2) (r := i) (by simp [vtGm]; omega)
        simp [vtGm] at this; omega
      · simp [vtGOrdW, List.getD_eq_getElem?_getD, show 18 + i < 24 by omega,
          show ¬ 18 + i < 9 by omega]

end

end
end LeanVM.Guest.B1.Tables
