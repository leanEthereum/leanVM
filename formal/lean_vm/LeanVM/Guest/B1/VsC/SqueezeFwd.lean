/-
  LeanVM.Guest.B1.VsC.SqueezeFwd

  Permutations of the capacity alone, forward; `squeeze_packed_last` completes with no words of its
  own, placed.
-/

module

public import LeanVM.Guest.B1.VsC.LeafA
public import LeanVM.Guest.B1.Link.SqueezePacked
public import LeanVM.Guest.Complete.PureA
import LeanVM.Guest.CoreRef

/-!
# `squeeze_cells`, forward

`spPerms_fwd`: on a valuation whose `KECCAK` atoms hold (their equations, which no memory changes)
and whose zero run is zero, `squeeze_cells`' outputs are `pkSqueeze`'s: each permutation's eight
rate cells and the last capacity. So its stores write known words, and no overlay of the memory is
needed: `squeeze_packed_last` completes on every memory holding the capacity and those words
(`spl_complete0`), at addresses that may coincide.

`loadsR_hintsR_of_loadOkR`: `loadsR_hintsR_of_loadOk` with each array's cells in a region given
per cell (a pointer argument need not be a `ptrAt`). `splA`: `squeeze_packed_last__L{k}` placed by
the transfer `callAtA_of_callCompletes0`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Guest.Value

@[expose] public section

/-! ## Permutations forward -/

/-- Permutation `j`'s `KECCAK` atom. -/
def spKec (o : ℕ) (cap : List ℕ) (z j : ℕ) : Atom :=
  .keccak ([.n z, .n z, .n z, .n z, .n z, .n (z + 1), .n (z + 2), .n (z + 3)] ++ (spCap o cap j).map V.n)
    ((List.range 13).map fun i ↦ .n (o + 13 * j + i)) false false

/-- **`squeeze_cells` forward**: its outputs are `pkSqueeze n`'s, from its `KECCAK` atoms alone. -/
theorem spPerms_fwd {rd : Reader} {σ : Val} {o : ℕ} {cap : List ℕ} {z : ℕ}
    (hz : ∀ i < 4, σ (.n (z + i)) = 0) : ∀ n, (∀ j < n, (spKec o cap z j).Holds rd σ) →
    (spCap o cap n).map (σ ∘ .n) = (pkSqueeze n (cap.map (σ ∘ .n))).2 ∧
      ∀ j < n, ∀ i < 8, σ (.n (o + 13 * j + i)) = (pkSqueeze n (cap.map (σ ∘ .n))).1.getD (8 * j + i) 0 := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨by simp [spCap, pkSqueeze], fun j hj => absurd hj (by omega)⟩
  | succ n ih =>
    intro hK
    obtain ⟨ihk, ihc⟩ := ih fun j hj => hK j (by omega)
    have hk := hK n (by omega)
    have hc := keccakA_fs (s := ⟨(spCap o cap n).map (σ ∘ .n), []⟩) hk (by simp) (by
      simp only [List.map_append, List.map_cons, List.map_nil, List.map_map]
      have z0 := hz 0 (by norm_num)
      rw [Nat.add_zero] at z0
      rw [z0, hz 1 (by norm_num), hz 2 (by norm_num), hz 3 (by norm_num)]
      simp [pendCells])
    have ho := outs_cells_of hc
    set S := pkSqueeze n (cap.map (σ ∘ .n))
    have hperm : Fs.perm ⟨(spCap o cap n).map (σ ∘ .n), []⟩ = pkPerm S.2 := by
      rw [ihk, Fs.perm, rateOf_eq_cells [] (by simp)]
      rfl
    rw [hperm] at ho
    refine ⟨?_, fun j hj i hi => ?_⟩
    · rw [pkSqueeze_succ', capOf_outs ho]
      simp only [spCap, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, List.map_map]
      rfl
    · rw [pkSqueeze_succ']
      rcases Nat.lt_or_ge j n with h | h
      · rw [List.getD_append _ _ _ _ (by rw [pkSqueeze_length]; omega)]
        exact ihc j h i hi
      · obtain rfl : j = n := by omega
        rw [List.getD_append_right _ _ _ _ (by rw [pkSqueeze_length]; omega), pkSqueeze_length,
          show 8 * j + i - 8 * j = i by omega, ho i (by omega)]
        simp [S, List.getD_eq_getElem?_getD, hi, cellAt, show i < 13 by omega]

theorem mem_spPermsT {o : ℕ} {cap : List ℕ} {z cells off n : ℕ} {a : Atom}
    (h : Stmt.atom a ∈ spPermsT o cap z cells off n) :
    ∃ j < n, a = spKec o cap z j ∨ ∃ i < 8, a = .load (.n (o + 13 * j + i)) (.n cells) (off + 8 * j + i) := by
  obtain ⟨l, hl, ha⟩ := List.mem_flatten.mp h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
  refine ⟨j, List.mem_range.mp hj, ?_⟩
  rcases List.mem_cons.mp ha with h | h
  · exact Or.inl (Stmt.atom.inj h)
  · obtain ⟨i, hi, he⟩ := List.mem_map.mp h
    exact Or.inr ⟨i, List.mem_range.mp hi, (Stmt.atom.inj he).symm⟩

theorem spKec_mem {o : ℕ} {cap : List ℕ} {z cells off n j : ℕ} (hj : j < n) :
    Stmt.atom (spKec o cap z j) ∈ spPermsT o cap z cells off n :=
  List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, List.mem_cons_self⟩

/-- An atom with no side condition holds by its equation. -/
theorem holds_of_good' {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {a : Atom}
    (hg : Good rd S w σ a) (hn : needsSide a = false) : a.Holds rd σ :=
  atoms_holds (atoms := [a]) (fun b hb => by rw [List.mem_singleton.mp hb]; exact hg)
    (fun b hb h => by rw [List.mem_singleton.mp hb] at h; simp [hn] at h) a List.mem_cons_self

/-- A load not stored holds on a memory defining its word. -/
theorem holds_load_of_good {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d p : V} {off : ℕ}
    (hg : Good rd S w σ (.load d p off)) (hS : Atom.load d p off ∉ S) {x : E}
    (hx : LoadHolds rd (σ p) off x) : (Atom.load d p off).Holds rd σ := by
  have := good_load_eq hx hg hS
  rw [Atom.Holds, this]; exact hx

/-! ## `squeeze_packed_last` -/

/-- **`squeeze_packed_last__L{k}` completes with no words of its own**: on the capacity at `rec`,
the cells of `k` permutations at `cells` and the capacity after them at `en`, it returns `0`. -/
def SqueezePackedLastComplete0 (kd k : ℕ) (name : String) : Prop :=
  ∀ (rec en cells : E) (cap : List E), cap.length = 5 →
    CallCompletes0 kd name [rec, en, cells] [0]
      (fun rd ↦ ReadsAt rd rec cap ∧ ReadsAt rd cells (pkSqueeze k cap).1 ∧ ReadsAt rd en (pkSqueeze k cap).2)
      PostQuiet

/-- The record's reads of `squeeze_packed_last`. -/
def splReads : List Atom :=
  [.load (.n 3) (.n 0) 0, .load (.n 4) (.n 0) 1, .load (.n 5) (.n 0) 2, .load (.n 6) (.n 0) 3, .load (.n 7) (.n 0) 4]

/-- What the kernel checks of `squeeze_packed_last__L{k}`'s body: its forward shape, the record's
reads not stores, every other atom free of side conditions but loads. -/
def splChecks (k : ℕ) : Bool :=
  (chk 3 (spLastBody k)).isSome && (retOf (spLastBody k)).isSome && splReads.all (fun a => !decide (a ∈ storesOf 3 (spLastBody k))) &&
    (atomsOf (spLastBody k)).all (fun a => isLoadB a || (!needsSide a && atomQuiet a && noHint a))

theorem readsAt_getD {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) {i : ℕ} (hi : i < l.length) :
    LoadHolds rd p i (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ hi]; exact h i hi

theorem spl_complete0 {kd k : ℕ} {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2]) (hbody : f.body = spLastBody k) (hck : splChecks k = true) :
    SqueezePackedLastComplete0 kd k name := by
  intro rec en cells cap hcap
  simp only [splChecks, Bool.and_eq_true, List.all_eq_true] at hck
  obtain ⟨⟨⟨hc, hr0⟩, hrd⟩, hat⟩ := hck
  obtain ⟨c', hc1⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr0
  rw [← hbody] at hc1 hrd hat hr
  have hc2 : chk [rec, en, cells].length f.body = some c' := hc1
  obtain ⟨ss, hb, hss⟩ := retOf_spec hr
  have hq : (atomsOf ss).all atomQuiet = true := List.all_eq_true.mpr fun a ha => by
    have := hat a (by rw [hb, atomsOf_append_ret]; exact ha)
    cases a with
    | hint hh => simp [isLoadB, noHint] at this
    | _ => rfl
  refine callCompletes0_straightRd (fun rd => fwdVal rd (fun _ => 0) [rec, en, cells] f.body) hfind hb hss hq
    fun rd _ ⟨hrec, hcl, hen⟩ => ?_
  set σ := fwdVal rd (fun _ => 0) [rec, en, cells] f.body with hσ
  set S := storesOf [rec, en, cells].length f.body
  have G : ∀ a, Stmt.atom a ∈ f.body → Good rd S (fun _ => 0) σ a := fwd_good hc2
  have p0 : σ (.n 0) = rec := fwd_param hc2 (by norm_num)
  have p1 : σ (.n 1) = en := fwd_param hc2 (by norm_num)
  have p2 : σ (.n 2) = cells := fwd_param hc2 (by norm_num)
  have hpar : f.params.map σ = [rec, en, cells] := by rw [hparams]; exact fwd_params hc2
  have hlast : (ss ++ [Stmt.ret vs]).getLast? = (spLastBody k).getLast? := by rw [← hb, hbody]
  have hmem : ∀ a, Stmt.atom a ∈ ss → Stmt.atom a ∈ f.body := fun a ha => by
    rw [hb]; exact List.mem_append_left _ ha
  -- the record read
  have hrec' : ∀ i < 5, Stmt.atom (.load (.n (3 + i)) (.n 0) i) ∈ f.body →
      σ (.n (3 + i)) = cap.getD i 0 ∧ (Atom.load (.n (3 + i)) (.n 0) i).Holds rd σ := by
    intro i hi hm
    have hS : Atom.load (.n (3 + i)) (.n 0) i ∉ S := fun h => by
      have hm' : Atom.load (.n (3 + i)) (.n 0) i ∈ splReads := by interval_cases i <;> simp [splReads]
      have := hrd _ hm'
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
      exact this h
    have hx : LoadHolds rd (σ (.n 0)) i (cap.getD i 0) := by rw [p0]; exact readsAt_getD hrec (by omega)
    exact ⟨good_load_eq hx (G _ hm) hS, holds_load_of_good (G _ hm) hS hx⟩
  have hne : ∀ a, Stmt.atom a ∈ f.body → isLoadB a = false → a.Holds rd σ := fun a ha hl => by
    have := hat a (mem_atomsOf' ha)
    simp only [hl, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact holds_of_good' (G a ha) this.1.1
  have hexact : ∀ a, Stmt.atom a ∈ f.body → a.Exact rd σ := fun a ha => by
    have := hat a (mem_atomsOf' ha)
    cases a with
    | hint hh => simp [isLoadB, noHint] at this
    | _ => trivial
  have hcp : ∀ i < 8 * k, LoadHolds rd cells i ((pkSqueeze k cap).1.getD i 0) := fun i hi =>
    readsAt_getD hcl (by rw [pkSqueeze_length]; exact hi)
  have hep : ∀ i < 5, LoadHolds rd en i ((pkSqueeze k cap).2.getD i 0) := fun i hi =>
    readsAt_getD hen (by rw [pkSqueeze_cap_length k cap hcap]; exact hi)
  by_cases hk0 : k = 0
  · subst hk0
    have hb0 : f.body = spLastBody 0 := hbody
    have hm : ∀ a, Stmt.atom a ∈ f.body → a = .load (.n 3) (.n 0) 0 ∨ a = .load (.n 3) (.n 1) 0 ∨
        a = .load (.n 4) (.n 0) 1 ∨ a = .load (.n 4) (.n 1) 1 ∨ a = .load (.n 5) (.n 0) 2 ∨
        a = .load (.n 5) (.n 1) 2 ∨ a = .load (.n 6) (.n 0) 3 ∨ a = .load (.n 6) (.n 1) 3 ∨
        a = .load (.n 7) (.n 0) 4 ∨ a = .load (.n 7) (.n 1) 4 ∨ a = .const (.n 8) (word 0 0) := fun a ha => by
      rw [hb0] at ha
      simpa [spLastBody] using ha
    have hm' : ∀ a, (a = .load (.n 3) (.n 0) 0 ∨ a = .load (.n 3) (.n 1) 0 ∨
        a = .load (.n 4) (.n 0) 1 ∨ a = .load (.n 4) (.n 1) 1 ∨ a = .load (.n 5) (.n 0) 2 ∨
        a = .load (.n 5) (.n 1) 2 ∨ a = .load (.n 6) (.n 0) 3 ∨ a = .load (.n 6) (.n 1) 3 ∨
        a = .load (.n 7) (.n 0) 4 ∨ a = .load (.n 7) (.n 1) 4 ∨ a = .const (.n 8) (word 0 0)) →
        Stmt.atom a ∈ f.body := fun a ha => by
      rw [hb0]; rcases ha with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [spLastBody]
    have r := fun i (hi : i < 5) => hrec' i hi (hm' _ (by interval_cases i <;> simp))
    have hv8 : σ (.n 8) = 0 := by rw [← word_zero]; exact G (.const (.n 8) (word 0 0)) (hm' _ (by simp))
    have hst : ∀ i < 5, (Atom.load (.n (3 + i)) (.n 1) i).Holds rd σ := fun i hi => by
      show LoadHolds rd (σ (.n 1)) i (σ (.n (3 + i)))
      rw [p1, (r i hi).1]; simpa [pkSqueeze] using hep i hi
    have hvs : vs = [.n 8] := by simpa [spLastBody] using hlast
    refine ⟨hpar, by rw [hvs]; simp [hv8], fun a ha => ⟨?_, hexact a (hmem a ha)⟩⟩
    rcases hm a (hmem a ha) with h | h | h | h | h | h | h | h | h | h | h <;> subst h
    exacts [(r 0 (by norm_num)).2, hst 0 (by norm_num), (r 1 (by norm_num)).2, hst 1 (by norm_num),
      (r 2 (by norm_num)).2, hst 2 (by norm_num), (r 3 (by norm_num)).2, hst 3 (by norm_num),
      (r 4 (by norm_num)).2, hst 4 (by norm_num), hne _ (hmem _ ha) rfl]
  · -- `k ≥ 1` permutations
    have hbk : f.body = spLastBody k := hbody
    have hpre : ∀ a, Stmt.atom a ∈ ([.atom (.load (.n 3) (.n 0) 0), .atom (.load (.n 4) (.n 0) 1),
        .atom (.load (.n 5) (.n 0) 2), .atom (.load (.n 6) (.n 0) 3), .atom (.load (.n 7) (.n 0) 4),
        .atom (.const (.n 8) (word 1 0)), .atom (.const (.n 9) (word 0 0)), .atom (.const (.n 10) (word 0 0)),
        .atom (.const (.n 11) (word 0 0)), .atom (.const (.n 12) (word 0 0))] : List Stmt) → Stmt.atom a ∈ f.body :=
      fun a ha => by rw [hbk, spLastBody, ite_eq_right hk0]; simp only [List.append_assoc]; exact List.mem_append_left _ ha
    have hperm : ∀ a, Stmt.atom a ∈ spPermsT 13 [3, 4, 5, 6, 7] 9 2 0 k → Stmt.atom a ∈ f.body := fun a ha => by
      rw [hbk, spLastBody, ite_eq_right hk0]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha))
    have hstoreM : ∀ j < 5, Stmt.atom (.load (.n (13 + 13 * (k - 1) + 8 + j)) (.n 1) j) ∈ f.body := fun j hj => by
      rw [hbk, spLastBody, ite_eq_right hk0]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    have hlastM : Stmt.atom (.const (.n (13 + 13 * k)) (word 0 0)) ∈ f.body := by
      rw [hbk, spLastBody, ite_eq_right hk0]; simp
    have r := fun i (hi : i < 5) => hrec' i hi (hpre _ (by interval_cases i <;> simp))
    have hz : ∀ i < 4, σ (.n (9 + i)) = 0 := fun i hi => by
      have := G (.const (.n (9 + i)) (word 0 0)) (hpre _ (by interval_cases i <;> simp))
      rw [this, word_zero]
    have hcapv : [3, 4, 5, 6, 7].map (σ ∘ .n) = cap := by
      have e0 := (r 0 (by norm_num)).1; have e1 := (r 1 (by norm_num)).1; have e2 := (r 2 (by norm_num)).1
      have e3 := (r 3 (by norm_num)).1; have e4 := (r 4 (by norm_num)).1
      obtain ⟨c0, c1, c2, c3, c4, rfl⟩ : ∃ c0 c1 c2 c3 c4, cap = [c0, c1, c2, c3, c4] := by
        match cap, hcap with | [c0, c1, c2, c3, c4], _ => exact ⟨c0, c1, c2, c3, c4, rfl⟩
      simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3 e4
      simp [e0, e1, e2, e3, e4]
    obtain ⟨hfc, hfo⟩ := spPerms_fwd (rd := rd) (o := 13) (cap := [3, 4, 5, 6, 7]) hz k
      fun j hj => holds_of_good' (G _ (hperm _ (spKec_mem hj))) rfl
    rw [hcapv] at hfc hfo
    have hv : σ (.n (13 + 13 * k)) = 0 := by rw [← word_zero]; exact G _ hlastM
    have hvs : vs = [.n (13 + 13 * k)] := by
      have e : ss ++ [Stmt.ret vs] = ([.atom (.load (.n 3) (.n 0) 0), .atom (.load (.n 4) (.n 0) 1),
          .atom (.load (.n 5) (.n 0) 2), .atom (.load (.n 6) (.n 0) 3), .atom (.load (.n 7) (.n 0) 4),
          .atom (.const (.n 8) (word 1 0)), .atom (.const (.n 9) (word 0 0)), .atom (.const (.n 10) (word 0 0)),
          .atom (.const (.n 11) (word 0 0)), .atom (.const (.n 12) (word 0 0))] ++ spPermsT 13 [3, 4, 5, 6, 7] 9 2 0 k ++
          ((List.range 5).map fun j ↦ .atom (.load (.n (13 + 13 * (k - 1) + 8 + j)) (.n 1) j)) ++
          [.atom (.const (.n (13 + 13 * k)) (word 0 0))]) ++ [Stmt.ret [.n (13 + 13 * k)]] := by
        rw [← hb, hbk, spLastBody, ite_eq_right hk0]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have := (List.append_inj' e rfl).2
      simpa using this
    refine ⟨hpar, by rw [hvs]; simp [hv], fun a ha => ⟨?_, hexact a (hmem a ha)⟩⟩
    have ha' := hmem a ha
    rw [hbk, spLastBody, ite_eq_right hk0] at ha'
    simp only [List.mem_append] at ha'
    rcases ha' with (((ha' | ha') | ha') | ha')
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha'
      rcases ha' with rfl | rfl | rfl | rfl | rfl | h | h | h | h | h
      exacts [(r 0 (by norm_num)).2, (r 1 (by norm_num)).2, (r 2 (by norm_num)).2, (r 3 (by norm_num)).2,
        (r 4 (by norm_num)).2, hne _ (hmem _ (h ▸ ha)) (by rw [h]; rfl), hne _ (hmem _ (h ▸ ha)) (by rw [h]; rfl),
        hne _ (hmem _ (h ▸ ha)) (by rw [h]; rfl), hne _ (hmem _ (h ▸ ha)) (by rw [h]; rfl),
        hne _ (hmem _ (h ▸ ha)) (by rw [h]; rfl)]
    · obtain ⟨j, hj, rfl | ⟨i, hi, rfl⟩⟩ := mem_spPermsT ha'
      · exact holds_of_good' (G _ (hperm _ (spKec_mem hj))) rfl
      · show LoadHolds rd (σ (.n 2)) (0 + 8 * j + i) (σ (.n (13 + 13 * j + i)))
        rw [p2, hfo j hj i hi, Nat.zero_add]
        exact hcp _ (by omega)
    · obtain ⟨j, hj, he⟩ := List.mem_map.mp ha'
      obtain rfl := Stmt.atom.inj he.symm
      have hj' := List.mem_range.mp hj
      show LoadHolds rd (σ (.n 1)) j (σ (.n (13 + 13 * (k - 1) + 8 + j)))
      have e := congrArg (fun l => l.getD j 0) hfc
      simp only [spCap, hk0, ↓reduceIte, List.map_map, Function.comp_def] at e
      rw [List.getD_eq_getElem _ _ (by simp; omega)] at e
      simp only [List.getElem_map, List.getElem_range] at e
      rw [p1, e]; exact hep j hj'
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha'
      rcases ha' with rfl | h
      · exact hne _ (hmem _ ha) rfl
      · cases h

/-! ## Straight leaves with no words of their own, placed -/

/-- A load through an array of `ps` within its length; any other atom hints nothing to the heap. -/
def loadInB (ps : List (ℕ × ℕ)) : Atom → Bool
  | .load _ p k => ps.any fun q => p == .n q.1 && decide (k < q.2)
  | a => (atomHeapDest? a).isNone

/-- **A straight leaf reading its arguments' arrays loads from them**, each array's cells in the
region `R` cell by cell, and hints nothing to the heap. -/
theorem loadsR_hintsR_of_loadIn {f : String} {fn : Fn} {ps : List (ℕ × ℕ)} {args rets : List E}
    {rd : Reader} {t : Tree} (R R' : ℕ → Prop) (hfind : coreProgram.find? f = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hL : (atomsOf fn.body).all (loadInB ps) = true) (hr : (retOf fn.body).isSome = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length)
    (hptr : ∀ q ∈ ps, ∀ off < q.2, ∃ i, (args.getD q.1 0).limb 0 * addressOfIndex off = addressOfIndex i ∧ R i)
    (hn : t.name = f) (hv : t.Valid coreProgram rd args rets) :
    t.LoadsR coreProgram R ∧ t.HintsR coreProgram R' := by
  obtain ⟨vs0, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
    obtain ⟨fn', hfn, hpar, es, vs, hw, _, _, hk⟩ := hv
    simp only [Tree.name] at hn
    subst hn
    rw [hfind] at hfn
    cases hfn
    have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
    have hw' : walk σ fn.body = .ret ((atomsOf ss).map Ev.atom) vs0 := by rw [hb']; exact walk_atoms _ _ _
    rw [hw'] at hw
    cases hw
    have hev : (Memory.Tree.node g σ bufs kids).events coreProgram = (atomsOf ss).map Ev.atom := by
      simp only [Tree.events, Tree.name, Tree.val, hfind, hw']
    rw [calls_atoms] at hk
    have hkids : kids = [] := by
      cases kids with
      | nil => rfl
      | cons _ _ => simp [Tree.KidsValid] at hk
    subst hkids
    have hok : ∀ a ∈ atomsOf ss, loadInB ps a = true := fun a ha =>
      List.all_eq_true.mp hL a (mem_atomsOf' (by rw [hbody]; exact List.mem_append_left _ (mem_of_mem_atomsOf ha)))
    have hσ : ∀ j < args.length, σ (.n j) = args.getD j 0 := by
      intro j hj
      have hj' : (((List.range args.length).map V.n).map σ)[j]? = args[j]? := by rw [← hparams, hpar]
      simp [hj] at hj'
      simpa [List.getD_eq_getElem?_getD, hj] using hj'
    refine ⟨?_, ?_⟩
    · rw [Tree.LoadsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.LoadsRKids]; trivial⟩
      simp only [loadAddrs, List.filterMap_map, List.mem_filterMap, Function.comp] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have hk := hok a ha
      cases a with
      | load d p off =>
        simp only [Ev.loadAddr?, Option.some.injEq] at hA
        simp only [loadInB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
        obtain ⟨q, hqm, rfl, hoff⟩ := hk
        obtain ⟨i, hi, hR⟩ := hptr q hqm off hoff
        exact ⟨i, by rw [← hA, hσ _ (hargs q hqm)]; exact hi, hR⟩
      | _ => simp [Ev.loadAddr?] at hA
    · rw [Tree.HintsR, hev, heapHintAddrs_atoms]
      · exact ⟨fun A hA => by simp at hA, by rw [Tree.HintsRKids]; trivial⟩
      · refine List.all_eq_true.mpr fun a ha => ?_
        have hk := hok a ha
        cases a with
        | load => rfl
        | _ => exact hk

/-- **A straight leaf with no words of its own completes placed**: `CallCompletes0` transferred, at
its frame, ending at its cursor. -/
theorem callAtA_leaf0 {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {S : List String}
    (hS : coreProgram.PureIn S) {k : ℕ} {f : String} (hf : f ∈ S) (hlp : coreProgram.loop f = false) {fn : Fn}
    {ps : List (ℕ × ℕ)} {args rets : List E} {R : ℕ → Prop} {Pre : Reader → Prop} {Post : Reader → Tree → Prop}
    (hfind : coreProgram.find? f = some fn) (hparams : fn.params = (List.range args.length).map V.n)
    (hL : (atomsOf fn.body).all (loadInB ps) = true) (hr : (retOf fn.body).isSome = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length)
    (hptr : ∀ q ∈ ps, ∀ off < q.2, ∃ i, (args.getD q.1 0).limb 0 * addressOfIndex off = addressOfIndex i ∧ R i)
    (h : CallCompletes0 k f args rets Pre Post) (fp c : ℕ) :
    CallAtA fs al cert k f args rets R (fun _ => False) (fun _ => True) Pre Post (fs f) fp c c := by
  obtain ⟨vs0, hr'⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr'
  have hnc : ∀ fn' σ es vs, coreProgram.find? f = some fn' → walk σ fn'.body = .ret es vs → calls es = [] := by
    intro fn' σ es vs hfn hw
    rw [hfind] at hfn
    cases hfn
    have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
    rw [hb', walk_atoms] at hw
    cases hw
    exact calls_atoms _
  refine callAtA_of_callCompletes0 hS hf le_rfl h fun rd t _ _ hn hv hb _ => ?_
  obtain ⟨h1, h2⟩ := block_endA_leaf (fs := fs) (al := al) hS hf hlp hnc hn hv hb c
  exact ⟨h1, h2, loadsR_hintsR_of_loadIn R R hfind hparams hL hr hargs hptr hn hv |>.1,
    loadsR_hintsR_of_loadIn R R hfind hparams hL hr hargs hptr hn hv |>.2⟩

/-! ## The specializations -/

/-- `squeeze_packed_last`'s names. -/
def splNames : List String :=
  ["squeeze_packed_last__L0", "squeeze_packed_last__L1", "squeeze_packed_last__L2", "squeeze_packed_last__L3"]

theorem spl_pureIn : coreProgram.PureIn splNames := by
  intro g hg fn hf
  simp only [splNames, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · rw [coreProgram_find?_at (j := idx% «squeeze_packed_last__L0») rfl] at hf
    obtain rfl := Option.some.inj hf; decide +kernel
  · rw [coreProgram_find?_at (j := idx% «squeeze_packed_last__L1») rfl] at hf
    obtain rfl := Option.some.inj hf; decide +kernel
  · rw [coreProgram_find?_at (j := idx% «squeeze_packed_last__L2») rfl] at hf
    obtain rfl := Option.some.inj hf; decide +kernel
  · rw [coreProgram_find?_at (j := idx% «squeeze_packed_last__L3») rfl] at hf
    obtain rfl := Option.some.inj hf; decide +kernel

set_option maxRecDepth 100000 in
theorem spl_complete0_all (kd : ℕ) : ∀ r < 4, SqueezePackedLastComplete0 kd r (splNames.getD r "") := by
  intro r hr
  interval_cases r
  · exact spl_complete0 (coreProgram_find?_at (j := idx% «squeeze_packed_last__L0») rfl) rfl spl0_body
      (by decide +kernel)
  · exact spl_complete0 (coreProgram_find?_at (j := idx% «squeeze_packed_last__L1») rfl) rfl spl1_body
      (by decide +kernel)
  · exact spl_complete0 (coreProgram_find?_at (j := idx% «squeeze_packed_last__L2») rfl) rfl spl2_body
      (by decide +kernel)
  · exact spl_complete0 (coreProgram_find?_at (j := idx% «squeeze_packed_last__L3») rfl) rfl spl3_body
      (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **`squeeze_packed_last__L{r}` completes placed**, its arrays' cells in `R`. -/
theorem splA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} (kd : ℕ) {r : ℕ} (hr : r < 4)
    {rec en cells : E} {cap : List E} (hcap : cap.length = 5) {R : ℕ → Prop}
    (hptr : ∀ q ∈ [(0, 5), (1, 5), (2, 8 * r)], ∀ off < q.2,
      ∃ i, ([rec, en, cells].getD q.1 0).limb 0 * addressOfIndex off = addressOfIndex i ∧ R i) (fp c : ℕ) :
    CallAtA fs al cert kd (splNames.getD r "") [rec, en, cells] [0] R (fun _ => False) (fun _ => True)
      (fun rd ↦ ReadsAt rd rec cap ∧ ReadsAt rd cells (pkSqueeze r cap).1 ∧ ReadsAt rd en (pkSqueeze r cap).2)
      PostQuiet (fs (splNames.getD r "")) fp c c := by
  have hm : splNames.getD r "" ∈ splNames := by interval_cases r <;> simp [splNames]
  have h := spl_complete0_all kd r hr rec en cells cap hcap
  interval_cases r
  · exact callAtA_leaf0 spl_pureIn hm (by decide +kernel)
      (coreProgram_find?_at (j := idx% «squeeze_packed_last__L0») rfl) rfl (by decide +kernel) (by decide +kernel)
      (by simp) hptr h fp c
  · exact callAtA_leaf0 spl_pureIn hm (by decide +kernel)
      (coreProgram_find?_at (j := idx% «squeeze_packed_last__L1») rfl) rfl (by decide +kernel) (by decide +kernel)
      (by simp) hptr h fp c
  · exact callAtA_leaf0 spl_pureIn hm (by decide +kernel)
      (coreProgram_find?_at (j := idx% «squeeze_packed_last__L2») rfl) rfl (by decide +kernel) (by decide +kernel)
      (by simp) hptr h fp c
  · exact callAtA_leaf0 spl_pureIn hm (by decide +kernel)
      (coreProgram_find?_at (j := idx% «squeeze_packed_last__L3») rfl) rfl (by decide +kernel) (by decide +kernel)
      (by simp) hptr h fp c

end
end LeanVM.Guest.B1.VsC
