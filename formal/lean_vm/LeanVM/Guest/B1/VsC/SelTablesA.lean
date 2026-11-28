/-
  LeanVM.Guest.B1.VsC.SelTablesA

  `selector_tables` completes placed, its eq tables its own `HeapBuf`.
-/

module

public import LeanVM.Guest.B1.VsC.LeafA
public import LeanVM.Guest.B1.Stack.SelTables
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.Memory.Restrict
public import Mathlib.Tactic.IntervalCases

/-!
# `selector_tables`, placed

`selector_tables__L{n}(point, point1)`, `4 ≤ n ≤ 8` (the guest stream's template `stBody n`,
`SelTables.lean`), placed at frame `fp` and cursor `c`: its `allocDyn` buffer of `32 n` words is at
`c`, its own words the run `selWords n p p1` there (nibble `j`'s level `w` entry `k` at
`32 j + selOff w + k·2^(3-w)`, `0` at the two offsets of each stride no level uses), and on every
memory holding the words `p` at `point` and `p1` at `point1` it returns `g^c`, popping nothing,
every node exact (`selector_tables_placed`). Its forward evaluation (`callAtA_fwd`) on the oracle
`g^c` holds every atom: the loads by the caller's words, each level's entries `selLev` by the
template (`stPre_vals`), so each store writes its own word. The template's shape facts are one
kernel decision over the five specializations (`stOkA_all`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier LeanVM.Guest.Value LeanVM.Guest

@[expose] public section

/-! ## The own words -/

/-- Offset `o` of nibble `j`'s stride of `selector_tables`' buffer. -/
def selEntry (p p1 : ℕ → E) (j o : ℕ) : E :=
  if 16 ≤ o then selLev p p1 j 3 (o - 16)
  else if o % 2 = 1 then selLev p p1 j 2 (o / 2)
  else if o % 4 = 2 then selLev p p1 j 1 (o / 4)
  else if o % 8 = 4 then selLev p p1 j 0 (o / 8)
  else 0

/-- `selector_tables`' buffer: `n` strides of `32` words. -/
def selWords (n : ℕ) (p p1 : ℕ → E) : List E :=
  (List.range (32 * n)).map fun i => selEntry p p1 (i / 32) (i % 32)

theorem selEntry_lev (p p1 : ℕ → E) (j : ℕ) {w k : ℕ} (hw : w < 4) (hk : k < 2 ^ (w + 1)) :
    selOff w + k * 2 ^ (3 - w) < 32 ∧ selEntry p p1 j (selOff w + k * 2 ^ (3 - w)) = selLev p p1 j w k := by
  interval_cases w <;> simp only [selOff, List.getD_cons_zero, List.getD_cons_succ] at hk ⊢ <;>
    norm_num at hk ⊢ <;> refine ⟨by omega, ?_⟩ <;> unfold selEntry <;>
    split_ifs <;> first | (exfalso; omega) | (congr 1; omega)

/-- **The run holds the entries.** -/
theorem selWords_load {rd : Reader} {c n : ℕ} {p p1 : ℕ → E}
    (h : ReadsAt rd (ofK (addressOfIndex c)) (selWords n p p1)) :
    ∀ j < n, ∀ w < 4, ∀ k < 2 ^ (w + 1),
      LoadHolds rd (ofK (addressOfIndex c)) (32 * j + selOff w + k * 2 ^ (3 - w)) (selLev p p1 j w k) := by
  intro j hj w hw k hk
  obtain ⟨hlt, he⟩ := selEntry_lev p p1 j hw hk
  have hi : 32 * j + selOff w + k * 2 ^ (3 - w) < (selWords n p p1).length := by
    simp only [selWords, List.length_map, List.length_range]; omega
  have := h _ hi
  simp only [selWords, List.getElem_map, List.getElem_range] at this
  rwa [show (32 * j + selOff w + k * 2 ^ (3 - w)) / 32 = j by omega,
    show (32 * j + selOff w + k * 2 ^ (3 - w)) % 32 = selOff w + k * 2 ^ (3 - w) by omega, he] at this

/-! ## The template -/

/-- Nibble `j`'s statements before its stores. -/
def stPre (j s : ℕ) : List Stmt :=
  [.atom (.load (.n s) (.n 1) (4 * j + 3)), .atom (.load (.n (s + 1)) (.n 0) (4 * j + 3))] ++
    stLev j s 1 ++ stLev j s 2 ++ stLev j s 3

theorem stNib_eq (j s : ℕ) : stNib j s = stPre j s ++ stStores j s := by
  simp only [stNib, stPre, List.append_assoc]

/-- The statements after the buffer's allocation. -/
def stTail (n : ℕ) : List Stmt :=
  ((List.range n).map fun j ↦ stNib j (4 + 36 * j)).flatten ++
    [.atom (.copy (.n (4 + 36 * n)) (.n 3)), .ret [.n (4 + 36 * n)]]

theorem stBody_eq (n : ℕ) :
    stBody n = .atom (.const (.n 2) (gw (32 * n))) :: .atom (.hint (.allocDyn (.n 3) (.n 2))) :: stTail n := by
  simp only [stBody, stBodyA, stTail, osCst, List.cons_append, List.nil_append, List.append_assoc]

/-- A statement before nibble `j`'s stores: a load through `point` or `point1`, or a product. -/
def preAtomB : Stmt → Bool
  | .atom (.load _ (.n 0) _) | .atom (.load _ (.n 1) _) | .atom (.mul ..) => true
  | _ => false

theorem stPre_all (j s : ℕ) : (stPre j s).all preAtomB = true := by
  simp [stPre, stLev, List.all_flatten, List.all_map, preAtomB, osMul]

theorem mem_stStores {j s : ℕ} {st : Stmt} (h : st ∈ stStores j s) : ∃ w < 4, ∃ k < 2 ^ (w + 1),
    st = .atom (.load (.n (stV s w k)) (.n 3) (32 * j + selOff w + k * 2 ^ (3 - w))) := by
  simp only [stStores, List.mem_flatten, List.mem_map, List.mem_range] at h
  obtain ⟨l, ⟨w, hw, hl⟩, hst⟩ := h
  subst hl
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hst
  exact ⟨w, hw, k, List.mem_range.mp hk, he.symm⟩

theorem mem_stTail {n : ℕ} {st : Stmt} (h : st ∈ stTail n) :
    (∃ j < n, st ∈ stPre j (4 + 36 * j) ∨ st ∈ stStores j (4 + 36 * j)) ∨
      st = .atom (.copy (.n (4 + 36 * n)) (.n 3)) ∨ st = .ret [.n (4 + 36 * n)] := by
  simp only [stTail, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range, List.mem_cons,
    List.mem_nil_iff, or_false] at h
  rcases h with ⟨_, ⟨j, hj, rfl⟩, h⟩ | h
  · rw [stNib_eq, List.mem_append] at h
    exact Or.inl ⟨j, hj, h⟩
  · exact Or.inr h

theorem stNib_mem {n j : ℕ} (hj : j < n) {st : Stmt} (h : st ∈ stNib j (4 + 36 * j)) : st ∈ stTail n := by
  simp only [stTail, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
  exact Or.inl ⟨_, ⟨j, hj, rfl⟩, h⟩

/-- **Nibble `j`'s levels hold `selLev`**, from the atoms before its stores. -/
theorem stPre_vals {C : CallRel} {rd : Reader} {σ : Val} {p p1 : ℕ → E} {j s : ℕ}
    (hp : ∀ i ≤ 4 * j + 3, LoadHolds rd (σ (.n 0)) i (p i))
    (hp1 : ∀ i ≤ 4 * j + 3, LoadHolds rd (σ (.n 1)) i (p1 i)) (h : AllOk C rd σ (stPre j s)) :
    ∀ w < 4, ∀ k < 2 ^ (w + 1), σ (.n (stV s w k)) = selLev p p1 j w k := by
  simp only [stPre, allOk_append, allOk_cons, allOk_nil, and_true] at h
  obtain ⟨⟨⟨⟨l0, l1⟩, h1⟩, h2⟩, h3⟩ := h
  simp only [StmtOk, Atom.Holds] at l0 l1
  have hlev : ∀ w, 1 ≤ w → w < 4 → AllOk C rd σ (stLev j s w) := fun w h1w hw ↦ by
    interval_cases w
    exacts [h1, h2, h3]
  intro w
  induction w with
  | zero =>
    intro _ k hk
    rcases k with _ | _ | k
    · simp only [stV, ↓reduceIte, Nat.add_zero, selLev]
      exact loadHolds_unique l0 (hp1 _ le_rfl)
    · simp only [stV, ↓reduceIte, selLev]
      exact loadHolds_unique l1 (hp _ le_rfl)
    · simp at hk
  | succ w ih =>
    intro hw k hk
    obtain ⟨lb0, lb1, hprod⟩ := stLev_ok (hlev (w + 1) (by omega) hw)
    have hr : σ (.n (stBase s (w + 1))) = p (4 * j + 2 - w) := by
      rw [show 4 * j + 2 - w = 4 * j + 3 - (w + 1) by omega]
      exact loadHolds_unique lb0 (hp _ (by omega))
    have hr1 : σ (.n (stBase s (w + 1) + 1)) = p1 (4 * j + 2 - w) := by
      rw [show 4 * j + 2 - w = 4 * j + 3 - (w + 1) by omega]
      exact loadHolds_unique lb1 (hp1 _ (by omega))
    obtain ⟨i, rfl | rfl⟩ : ∃ i, k = 2 * i ∨ k = 2 * i + 1 := ⟨k / 2, by omega⟩
    · have hi : i < 2 ^ (w + 1) := by rw [pow_succ] at hk; omega
      rw [(hprod i hi).1, Nat.add_sub_cancel, ih (by omega) i hi, hr1, selLev,
        show 2 * i / 2 = i by omega, show 2 * i % 2 = 0 by omega]
      simp
    · have hi : i < 2 ^ (w + 1) := by rw [pow_succ] at hk; omega
      rw [(hprod i hi).2, Nat.add_sub_cancel, ih (by omega) i hi, hr, selLev,
        show (2 * i + 1) / 2 = i by omega, show (2 * i + 1) % 2 = 1 by omega]
      simp

/-! ## The kernel's checks -/

/-- A load through `point` or `point1` below `4 n`, a store through the buffer below `32 n`, any other
atom without a side condition. -/
def stAtomOk (S : List Atom) (n : ℕ) : Atom → Bool
  | a@(.load _ p k) => if a ∈ S then inArrays [(3, 32 * n)] p k else inArrays [(0, 4 * n), (1, 4 * n)] p k
  | a => !needsSide a

/-- No computed hint but a `HeapBuf`'s. -/
def allocHintsOnly : Atom → Bool
  | .hint (.alloc ..) | .hint (.allocDyn ..) => true
  | .hint _ => false
  | _ => true

/-- What the kernel checks of `selector_tables__L{n}`'s template. -/
def stOkA (n : ℕ) : Bool :=
  leafChecks 2 (stBody n) && (atomsOf (stBody n)).all (stAtomOk (storesOf 2 (stBody n)) n) &&
    (atomsOf (stBody n)).all allocHintsOnly && (atomsOf (stTail n)).all (fun a => !atomAllocB a) &&
    retOf (stBody n) == some [.n (4 + 36 * n)]

theorem stOkA_all : ∀ n, 4 ≤ n → n ≤ 8 → stOkA n = true := by
  have h : ((List.range 5).all fun n => stOkA (n + 4)) = true := by decide +kernel
  intro n h4 h8
  have := List.all_eq_true.mp h (n - 4) (List.mem_range.mpr (by omega))
  rwa [Nat.sub_add_cancel h4] at this

/-! ## Placed -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **`selector_tables__L{n}` completes placed**, from its template. -/
theorem st_placed {k : ℕ} {name : String} {fn : Fn} {n : ℕ} (h4 : 4 ≤ n) (h8 : n ≤ 8)
    (hfind : coreProgram.find? name = some fn) (hparams : fn.params = [.n 0, .n 1])
    (hbody : fn.body = stBody n) (hok : stOkA n = true) {pt pt1 : E} {p p1 : ℕ → E} {R : ℕ → Prop}
    (hR : ∀ i < 4 * n, (∃ m, pt.limb 0 * addressOfIndex i = addressOfIndex m ∧ R m) ∧
      ∃ m, pt1.limb 0 * addressOfIndex i = addressOfIndex m ∧ R m) (fp c : ℕ) :
    CallAtA fs al cert k name [pt, pt1] [ofK (addressOfIndex c)] R (fun i => c ≤ i ∧ i < c + 32 * n)
      (fun rd => ∀ j < n, ∀ w < 4, ∀ k < 2 ^ (w + 1),
        LoadHolds rd (ofK (addressOfIndex c)) (32 * j + selOff w + k * 2 ^ (3 - w)) (selLev p p1 j w k))
      (fun rd => (∀ i < 4 * n, LoadHolds rd pt i (p i)) ∧ ∀ i < 4 * n, LoadHolds rd pt1 i (p1 i))
      PostQuiet (fs name) fp c (c + 32 * n) := by
  simp only [stOkA, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨hck, hst⟩, hhint⟩, hna⟩, hret⟩ := hok
  have hlp : coreProgram.loop name = false := by
    rw [Program.loop_of_find? hfind, Fn.loop, hbody, stBody]; simp
  have hsum : c + [32 * n].sum = c + 32 * n := by simp
  rw [← hsum]
  have hck' : leafChecks [pt, pt1].length fn.body = true := by rw [hbody]; exact hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp (by
    simp only [leafChecks, Bool.and_eq_true] at hck'; exact hck'.1.1)
  refine callAtA_fwd (fun _ => ofK (addressOfIndex c)) [32 * n] [(c, selWords n p p1)] hfind hlp
    (by rw [hparams]; rfl) hck' ⟨fun q hq => ?_, List.pairwise_singleton _ _⟩
    (fun rd hw => selWords_load (hw _ List.mem_cons_self)) (fun i hi => by simpa using hi)
    fun rd hl hw ⟨hp, hp1⟩ σ hσ => ?_
  · rw [List.mem_singleton] at hq; subst hq
    right; simp [selWords]
  have hW : ∀ j < n, ∀ w < 4, ∀ k < 2 ^ (w + 1), LoadHolds rd (ofK (addressOfIndex c))
      (32 * j + selOff w + k * 2 ^ (3 - w)) (selLev p p1 j w k) := selWords_load (hw _ List.mem_cons_self)
  set S := storesOf [pt, pt1].length fn.body with hS
  have hG : ∀ a, Stmt.atom a ∈ fn.body → Good rd S (fun _ => ofK (addressOfIndex c)) σ a :=
    fun a ha => hσ ▸ fwd_good hc a ha
  have hmemB : ∀ st, st ∈ stTail n → st ∈ fn.body := fun st h => by
    rw [hbody, stBody_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  have hσ0 : σ (.n 0) = pt := by rw [hσ]; exact fwd_param hc (by simp)
  have hσ1 : σ (.n 1) = pt1 := by rw [hσ]; exact fwd_param hc (by simp)
  have hσ2 : σ (.n 2) = gw (32 * n) := hG (.const (.n 2) (gw (32 * n))) (by rw [hbody, stBody_eq]; exact List.mem_cons_self)
  have hσ3 : σ (.n 3) = ofK (addressOfIndex c) :=
    hG (.hint (.allocDyn (.n 3) (.n 2))) (by rw [hbody, stBody_eq]; simp)
  have hok' : ∀ a, Stmt.atom a ∈ fn.body → stAtomOk S n a = true := fun a ha => by
    have := List.all_eq_true.mp hst a (mem_atomsOf' (hbody ▸ ha)); rwa [hS, hbody]
  -- the loads' pointers and offsets
  have hload : ∀ d q off, Stmt.atom (.load d q off) ∈ fn.body →
      (Atom.load d q off ∈ S ∧ q = .n 3 ∧ off < 32 * n) ∨
        (Atom.load d q off ∉ S ∧ (q = .n 0 ∨ q = .n 1) ∧ off < 4 * n) := fun d q off ha => by
    have h := hok' _ ha
    simp only [stAtomOk] at h
    by_cases hm : Atom.load d q off ∈ S
    · simp only [hm, ↓reduceIte, inArrays, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq] at h
      exact Or.inl ⟨hm, h⟩
    · simp only [hm, ↓reduceIte, inArrays, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      right; refine ⟨hm, ?_⟩; rcases h with h | h
      · exact ⟨Or.inl h.1, h.2⟩
      · exact ⟨Or.inr h.1, h.2⟩
  -- the stores' words
  have hstore : (∀ a, Stmt.atom a ∈ fn.body → a ∉ S → a.Holds rd σ) → ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ := by
    intro hns a ha
    by_cases haS : a ∉ S
    · exact hns a ha haS
    have hmS : a ∈ S := not_not.mp haS
    rw [hbody, stBody_eq] at ha
    rcases List.mem_cons.mp ha with h | h
    · rw [Stmt.atom.injEq] at h; subst h
      obtain ⟨_, _, _, he⟩ := storesOf_isLoad hmS; cases he
    rcases List.mem_cons.mp h with h | h
    · rw [Stmt.atom.injEq] at h; subst h
      obtain ⟨_, _, _, he⟩ := storesOf_isLoad hmS; cases he
    rcases mem_stTail h with ⟨j, hj, hpre | hsto⟩ | h | h
    · exfalso
      have hb := List.all_eq_true.mp (stPre_all j (4 + 36 * j)) _ hpre
      obtain ⟨d, q, off, rfl⟩ := storesOf_isLoad hmS
      have hm := hmemB _ (stNib_mem hj (by rw [stNib_eq]; exact List.mem_append_left _ hpre))
      rcases hload d q off hm with ⟨-, rfl, -⟩ | ⟨hn, -⟩
      · simp [preAtomB] at hb
      · exact hn hmS
    · obtain ⟨w, hw, k', hk', he⟩ := mem_stStores hsto
      rw [Stmt.atom.injEq] at he; subst he
      -- the nibble's levels
      have hpre : AllOk (fun _ _ _ => True) rd σ (stPre j (4 + 36 * j)) := by
        intro st hst'
        have hb := List.all_eq_true.mp (stPre_all j (4 + 36 * j)) _ hst'
        have hm := hmemB _ (stNib_mem hj (by rw [stNib_eq]; exact List.mem_append_left _ hst'))
        match st, hb, hm with
        | .atom (.load d (.n 0) off), _, hm =>
          exact hns _ hm fun hmS' => by rcases hload _ _ _ hm with ⟨-, h, -⟩ | ⟨h, -⟩ <;> simp_all
        | .atom (.load d (.n 1) off), _, hm =>
          exact hns _ hm fun hmS' => by rcases hload _ _ _ hm with ⟨-, h, -⟩ | ⟨h, -⟩ <;> simp_all
        | .atom (.mul d x y), _, hm =>
          exact hns _ hm fun hmS' => by obtain ⟨_, _, _, he⟩ := storesOf_isLoad hmS'; cases he
      have hv := stPre_vals (p := p) (p1 := p1) (fun i hi => by rw [hσ0]; exact hp i (by omega))
        (fun i hi => by rw [hσ1]; exact hp1 i (by omega)) hpre w hw k' hk'
      show LoadHolds rd (σ (.n 3)) _ (σ _)
      rw [hσ3, hv]; exact hW j hj w hw k' hk'
    · rw [Stmt.atom.injEq] at h; subst h
      obtain ⟨_, _, _, he⟩ := storesOf_isLoad hmS; cases he
    · cases h
  have hatoms : atomsOf fn.body = .const (.n 2) (gw (32 * n)) :: .hint (.allocDyn (.n 3) (.n 2)) ::
      atomsOf (stTail n) := by rw [hbody, stBody_eq]; rfl
  have hal : allocs σ ((atomsOf fn.body).map Ev.atom) = [32 * n] := by
    rw [hatoms, List.map_cons, List.map_cons, show ∀ (x y : Ev) (l : List Ev), x :: y :: l = [x, y] ++ l
      from fun _ _ _ => rfl, allocs_append, allocs_atoms σ hna]
    simp only [allocs, List.filterMap_cons, List.filterMap_nil, Ev.alloc?, hσ2, List.append_nil]
    rw [gw_eq (by unfold u128Bound; omega), gen_pow_eq_ofK, logG_spec (by omega)]
  refine ⟨fun a ha haS hn => ?_, fun hns a ha => hstore hns a (storesOf_mem ha),
    fun a ha => ?_, fun vs hvs => ?_, hal, ?_, fun A hA => ?_⟩
  · -- the side condition of a load through `point` or `point1`
    cases a with
    | load d q off =>
      rcases hload d q off ha with ⟨h, -⟩ | ⟨-, hq, hoff⟩
      · exact absurd h haS
      simp only [Side, haS, ↓reduceIte]
      rcases hq with rfl | rfl
      · rw [hσ0]; exact ⟨(hp off hoff).1, by rw [(hp off hoff).2]; rfl⟩
      · rw [hσ1]; exact ⟨(hp1 off hoff).1, by rw [(hp1 off hoff).2]; rfl⟩
    | _ =>
      have := hok' _ ha
      simp only [stAtomOk, hn, Bool.not_true, Bool.false_eq_true] at this
  · have := List.all_eq_true.mp hhint a (mem_atomsOf' (hbody ▸ ha))
    cases a with
    | hint hh => cases hh <;> simp_all [allocHintsOnly, Atom.Exact, Hint.Exact]
    | _ => trivial
  · rw [hbody, hret, Option.some.injEq] at hvs
    subst hvs
    have hcp : σ (.n (4 + 36 * n)) = σ (.n 3) :=
      hG (.copy (.n (4 + 36 * n)) (.n 3)) (hmemB _ (by simp [stTail]))
    simp [hcp, hσ3]
  · rw [hatoms, List.map_cons, List.map_cons, show ∀ (x y : Ev) (l : List Ev), x :: y :: l = [x, y] ++ l
      from fun _ _ _ => rfl, allocDsts_append, allocDsts_atoms hna]
    simp only [bases, List.map_cons, List.map_nil, List.append_nil, allocDsts, List.map_eq_singleton_iff]
    exact ⟨.n 3, rfl, hσ3⟩
  · obtain ⟨d, q, off, hm, rfl⟩ := mem_loadAddrs hA
    have hm' : Stmt.atom (.load d q off) ∈ fn.body := mem_of_mem_atomsOf hm
    rcases hload d q off hm' with ⟨-, rfl, hoff⟩ | ⟨-, hq, hoff⟩
    · refine ⟨c + off, by rw [hσ3]; simp [addressOfIndex, pow_add], Or.inl ⟨by omega, by simp; omega⟩⟩
    · rcases hq with rfl | rfl
      · obtain ⟨m, hm, hR'⟩ := (hR off hoff).1
        exact ⟨m, by rw [hσ0, hm], Or.inr hR'⟩
      · obtain ⟨m, hm, hR'⟩ := (hR off hoff).2
        exact ⟨m, by rw [hσ1, hm], Or.inr hR'⟩

set_option maxRecDepth 100000 in
/-- **`selector_tables` completes placed**, every specialization `__L{n}`, `4 ≤ n ≤ 8`: its buffer of
`32 n` words at the cursor `c`, its entries there, returning `g^c`. -/
theorem selector_tables_placed {k : ℕ} (n : ℕ) (h4 : 4 ≤ n) (h8 : n ≤ 8) {pt pt1 : E} {p p1 : ℕ → E}
    {R : ℕ → Prop}
    (hR : ∀ i < 4 * n, (∃ m, pt.limb 0 * addressOfIndex i = addressOfIndex m ∧ R m) ∧
      ∃ m, pt1.limb 0 * addressOfIndex i = addressOfIndex m ∧ R m) (fp c : ℕ) :
    CallAtA fs al cert k ("selector_tables__L" ++ natStr n) [pt, pt1] [ofK (addressOfIndex c)] R
      (fun i => c ≤ i ∧ i < c + 32 * n)
      (fun rd => ∀ j < n, ∀ w < 4, ∀ k < 2 ^ (w + 1),
        LoadHolds rd (ofK (addressOfIndex c)) (32 * j + selOff w + k * 2 ^ (3 - w)) (selLev p p1 j w k))
      (fun rd => (∀ i < 4 * n, LoadHolds rd pt i (p i)) ∧ ∀ i < 4 * n, LoadHolds rd pt1 i (p1 i))
      PostQuiet (fs ("selector_tables__L" ++ natStr n)) fp c (c + 32 * n) := by
  interval_cases n
  · exact st_placed (by decide) (by decide)
      (coreProgram_find?_at (j := idx% «selector_tables__L4») rfl) rfl selector_tables_L4_body
      (stOkA_all 4 (by decide) (by decide)) hR fp c
  · exact st_placed (by decide) (by decide)
      (coreProgram_find?_at (j := idx% «selector_tables__L5») rfl) rfl selector_tables_L5_body
      (stOkA_all 5 (by decide) (by decide)) hR fp c
  · exact st_placed (by decide) (by decide)
      (coreProgram_find?_at (j := idx% «selector_tables__L6») rfl) rfl selector_tables_L6_body
      (stOkA_all 6 (by decide) (by decide)) hR fp c
  · exact st_placed (by decide) (by decide)
      (coreProgram_find?_at (j := idx% «selector_tables__L7») rfl) rfl selector_tables_L7_body
      (stOkA_all 7 (by decide) (by decide)) hR fp c
  · exact st_placed (by decide) (by decide)
      (coreProgram_find?_at (j := idx% «selector_tables__L8») rfl) rfl selector_tables_L8_body
      (stOkA_all 8 (by decide) (by decide)) hR fp c

end
end LeanVM.Guest.B1.VsC
