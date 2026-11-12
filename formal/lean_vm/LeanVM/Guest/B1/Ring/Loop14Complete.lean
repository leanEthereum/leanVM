/-
  LeanVM.Guest.B1.Ring.Loop14Complete

  `__loop13`, completely: on the honest chain, every iteration's block holds on its evaluated
  valuation, so the loop runs from `g^j` to its end `g^8`.
-/

module

public import LeanVM.Guest.B1.Ring.Target
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.Memory.Uniform

/-!
# `__loop13`, completely

The honest memory of `ring_switch_target(slices, map_challenges)`: the 64 slices `s` at `sl`,
the sixteen challenges at `mc` (`g_0 .. g_7` the last eight, `gs`), and its chain at `cb`, entry
`8j + p` (`j ≤ 8`, `p < 8`) holding chain `p` after the first `8j` images `Ψ(s_t)`: Horner in
`w_p` from `0` (`rtHz`, `chainWords`).

`l13_block`: at `x`, the evaluated valuation `l13σ` of the loop's body (`Fwd.ev`) satisfies every
atom of the body: its loads read the challenges, the slices and row `j` of the chain, and its
eight stores write row `j + 1`, which the honest chain holds (`Ψ` of the loaded slices by the
soundness lemma `holds_psRowAt`, the Horner steps by `hz_steps`). `l13_relIn`: the loop holds from
`g^j`, `j ≤ 7`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd LeanVM.Guest.Memory

@[expose] public section

/-! ## The honest chain -/

/-- The images `Ψ(s_t)` of the slices at the challenges `gs`. -/
def rtImgs (s gs : List E) : List E := s.map (ringPsi · gs)

/-- Chain `p` after the first `n` images: Horner in `w_p` from `0`. -/
def rtHz (s gs : List E) (p n : ℕ) : E :=
  ((rtImgs s gs).take n).foldl (hstep (ofK (ringWK.getD p 0))) 0

/-- **The honest chain**: entry `8j + p` is chain `p` after `8j` images. -/
def chainWords (s gs : List E) : List E :=
  (List.range 72).map fun k ↦ rtHz s gs (k % 8) (8 * (k / 8))

theorem chainWords_length (s gs : List E) : (chainWords s gs).length = 72 := by
  simp [chainWords]

theorem chainWords_get (s gs : List E) {k : ℕ} (hk : k < (chainWords s gs).length) :
    (chainWords s gs)[k] = rtHz s gs (k % 8) (8 * (k / 8)) := by
  simp [chainWords]

/-- The chain read through `p`, at row `j` and entry `p'`. -/
theorem chain_load {rd : Reader} {s gs : List E} {cb : E} (h : ReadsAt rd cb (chainWords s gs))
    {j p : ℕ} (hj : j ≤ 8) (hp : p < 8) : LoadHolds rd cb (8 * j + p) (rtHz s gs p (8 * j)) := by
  have := h (8 * j + p) (by rw [chainWords_length]; omega)
  rwa [chainWords_get, show (8 * j + p) % 8 = p by omega, show (8 * j + p) / 8 = j by omega] at this

/-- One row more: eight Horner steps by the chunk's images. -/
theorem rtHz_succ (s gs : List E) (p j : ℕ) :
    rtHz s gs p (8 * j + 8) = ((((s.drop (8 * j)).take 8).map (ringPsi · gs)).foldl
      (hstep (ofK (ringWK.getD p 0))) (rtHz s gs p (8 * j))) := by
  rw [rtHz, rtHz, List.take_add, List.foldl_append]
  refine congrArg (List.foldl _ _) ?_
  rw [rtImgs, List.map_take, List.map_drop]

/-! ## Helpers -/

theorem rt_rdAt_of_load {rd : Reader} {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) :
    rdAt rd p k = v := by
  rw [rdAt, h.2]; rfl

theorem rt_side_of_load {rd : Reader} {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) :
    IsInK p ∧ (rd (p.limb 0 * Parameters.addressOfIndex k)).isSome := ⟨h.1, by rw [h.2]; rfl⟩

/-- A block of atoms that hold holds. -/
theorem holdsList_of_atoms {C : CallRel} {rd : Reader} {σ : Val} :
    ∀ (ss : List Stmt), (∀ s ∈ ss, ∃ a, s = .atom a ∧ a.Holds rd σ) →
      ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ ss next kret
  | [], _, _, _, hn => hn
  | s :: ss, h, _, _, hn => by
    obtain ⟨a, rfl, ha⟩ := h s List.mem_cons_self
    exact ⟨ha, holdsList_of_atoms ss (fun t ht ↦ h t (List.mem_cons_of_mem _ ht)) hn⟩

/-- The atoms of a block. -/
def rtAtoms (ss : List Stmt) : List Atom := ss.filterMap fun s => match s with
  | .atom a => some a
  | _ => none

theorem rt_mem_atoms {ss : List Stmt} {a : Atom} (h : a ∈ rtAtoms ss) : Stmt.atom a ∈ ss := by
  obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp h
  cases s <;> simp only [reduceCtorEq, Option.some.injEq] at hsa
  subst hsa
  exact hs

theorem rt_atoms_mem {ss : List Stmt} {a : Atom} (h : Stmt.atom a ∈ ss) : a ∈ rtAtoms ss :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem rt_addr_mul (b c k : ℕ) : (ofK (Parameters.addressOfIndex b) * gen ^ c).limb 0 *
    Parameters.addressOfIndex k = Parameters.addressOfIndex (b + c + k) := by
  have e : ofK (Parameters.addressOfIndex b) * gen ^ c = ofK (Parameters.addressOfIndex (b + c)) := by
    rw [gen_pow_eq_ofK, ← ofK_mul, Parameters.addressOfIndex, Parameters.addressOfIndex,
      Parameters.addressOfIndex, pow_add]
  rw [e, Main.addr_ofK]

/-- Two lists read at one pointer, of one length, are one. -/
theorem rt_readsAt_unique {rd : Reader} {p : E} {xs ys : List E} (hl : xs.length = ys.length)
    (h1 : ReadsAt rd p xs) (h2 : ReadsAt rd p ys) : xs = ys :=
  List.ext_getElem hl fun k hk hk' => loadHolds_unique (h1 k hk) (h2 k hk')

/-! ## The body's parts -/

/-- The challenges' loads. -/
def l13G : List Stmt := ((List.range 8).map fun b ↦ [.atom (.load (.n (4 + b)) (.n 1) (8 + b))]).flatten
/-- The slices' pointer. -/
def l13M1 : List Stmt :=
  [.atom (.mul (.n 12) (.n 0) (.n 0)), .atom (.mul (.n 13) (.n 12) (.n 12)),
    .atom (.mul (.n 14) (.n 13) (.n 13)), .atom (.mul (.n 15) (.n 2) (.n 14))]
/-- The rows of `Ψ`. -/
def l13P : List Stmt := ((List.range 8).map psRow).flatten
/-- The chain's pointer. -/
def l13M2 : List Stmt :=
  [.atom (.mul (.n 200) (.n 0) (.n 0)), .atom (.mul (.n 201) (.n 200) (.n 200)),
    .atom (.mul (.n 202) (.n 201) (.n 201)), .atom (.mul (.n 203) (.n 3) (.n 202))]
/-- The chains. -/
def l13H : List Stmt := ((List.range 8).map hzRow).flatten
/-- The guard's values. -/
def l13T : List Stmt :=
  [.atom (.const (.n 404) (word 2 0)), .atom (.mul (.n 405) (.n 0) (.n 404)),
    .atom (.const (.n 406) (word 256 0)), .atom (.add (.n 407) (.n 405) (.n 406)),
    .atom (.const (.n 408) (word 2 0)), .atom (.mul (.n 409) (.n 0) (.n 408))]

/-- `__loop13`'s atoms. -/
def l13A : List Stmt := l13G ++ l13M1 ++ l13P ++ l13M2 ++ l13H ++ l13T

theorem loop13T_split : loop13T = l13A ++
    [.callIf (.n 407) "__loop13" [.n 409, .n 1, .n 2, .n 3], .ret []] := by
  simp only [loop13T, l13A, l13G, l13M1, l13P, l13M2, l13H, l13T, List.append_assoc,
    List.cons_append, List.nil_append]

theorem l13A_mem {s : Stmt}
    (h : s ∈ l13G ∨ s ∈ l13M1 ∨ s ∈ l13P ∨ s ∈ l13M2 ∨ s ∈ l13H ∨ s ∈ l13T) : s ∈ l13A := by
  simp only [l13A, List.mem_append]
  tauto

theorem mem_l13P {r : ℕ} (hr : r < 8) {s : Stmt} (hs : s ∈ psRow r) : s ∈ l13A :=
  l13A_mem (Or.inr (Or.inr (Or.inl (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩, hs⟩))))

/-- Chain `p`'s statements but its store. -/
def hzPre (p : ℕ) : List Stmt :=
  [.atom (.load (.n (hzBase p)) (.n 203) p)] ++ ((List.range 8).map (hzStep (hzBase p) p)).flatten

theorem mem_l13H {p : ℕ} (hp : p < 8) {s : Stmt} (hs : s ∈ hzPre p) : s ∈ l13A := by
  refine l13A_mem (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_flatten.mpr
    ⟨_, List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩, ?_⟩))))))
  rw [hzRow, hzRowAt]
  exact List.mem_append_left _ hs

/-- The stores: chain `p`'s value into row entry `8 + p`. -/
def l13S : List Atom := (List.range 8).map fun p => Atom.load (.n (hzBase p + 24)) (.n 203) (8 + p)

/-- An atom not among the stores. -/
def nsAtom : Stmt → Bool
  | .atom a => decide (a ∉ l13S)
  | _ => false

theorem l13P_ns : (List.range 8).all (fun r => (psRow r).all nsAtom) = true := by decide +kernel

theorem l13H_ns : (List.range 8).all (fun p => (hzPre p).all nsAtom) = true := by decide +kernel

theorem l13_allAtoms : l13A.all (fun s => match s with | .atom _ => true | _ => false) = true := by
  decide +kernel

theorem l13_chk : chk 4 loop13T = some 410 := by decide +kernel

theorem l13_stores : storesOf 4 loop13T = l13S := by decide +kernel

/-- The loads `__loop13` needs a word for: the challenges (`1`), the slices (`15`), the chain's
row (`203`). -/
def l13LoadOk : Atom → Bool
  | .load _ (.n 1) off => decide (8 ≤ off ∧ off < 16)
  | .load _ (.n 15) off => decide (off < 8)
  | .load _ (.n 203) off => decide (off < 8)
  | _ => false

theorem l13_needs : (rtAtoms l13A).all (fun a => decide (a ∈ l13S) || !needsSide a ||
    l13LoadOk a) = true := by decide +kernel

/-- Chain `p` over a chunk, but its store. -/
theorem holds_hzPre {C : CallRel} {rd : Reader} {σ : Val} {p : ℕ} (hp : p < 8)
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (hzPre p) True kret) :
    LoadHolds rd (σ (.n 203)) p (σ (.n (hzBase p))) ∧
      σ (.n (hzBase p + 24)) = (psVals σ).foldl (hstep (ofK (ringWK.getD p 0))) (σ (.n (hzBase p))) := by
  rw [hzPre, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l0, h⟩ := h
  obtain ⟨hs, -⟩ := (holdsList_range_flatten 8 (hzStep (hzBase p) p) (hzStep_noRet _ p) _ _).mp h
  have hs' : ∀ r < 8, σ (.n (hzBase p + 1 + 3 * r)) = word (ringWNat.getD p 0) 0 ∧
      σ (.n (hzBase p + 2 + 3 * r)) = σ (.n (hzBase p + 3 * r)) * σ (.n (hzBase p + 1 + 3 * r)) ∧
      σ (.n (hzBase p + 3 + 3 * r)) = σ (.n (hzBase p + 2 + 3 * r)) + σ (.n (psBase r + 22)) := by
    intro r hr
    have := hs r hr
    simp only [hzStep, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at this
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  refine ⟨l0, ?_⟩
  have := hz_steps hp hs' 8 le_rfl
  rw [show hzBase p + 3 * 8 = hzBase p + 24 by ring] at this
  rw [this]
  rfl

/-! ## The block -/

/-- The evaluated valuation of `__loop13`'s body. -/
noncomputable def l13σ (rd : Reader) (x mc sl cb : E) : Val :=
  B1.Val.ofArgs (ev rd (fun _ => 0) [x, mc, sl, cb] loop13T)

/-- **`__loop13`'s block holds** on its evaluated valuation, at `x` over the honest row: the
challenges `gs`, the chunk `vs`, row `x^8`'s entries `acc p` and the next row's. -/
theorem l13_block {rd : Reader} {x mc sl cb : E} {gs vs : List E} {acc : ℕ → E}
    (hgl : gs.length = 8) (hvl : vs.length = 8)
    (hg : ∀ b < 8, LoadHolds rd mc (8 + b) (gs.getD b 0)) (hvs : ReadsAt rd (sl * x ^ 8) vs)
    (hr0 : ∀ p < 8, LoadHolds rd (cb * x ^ 8) p (acc p))
    (hr1 : ∀ p < 8, LoadHolds rd (cb * x ^ 8) (8 + p)
      ((vs.map (ringPsi · gs)).foldl (hstep (ofK (ringWK.getD p 0))) (acc p))) :
    (∀ a ∈ rtAtoms l13A, a.Holds rd (l13σ rd x mc sl cb)) ∧
      l13σ rd x mc sl cb (.n 0) = x ∧ l13σ rd x mc sl cb (.n 1) = mc ∧
      l13σ rd x mc sl cb (.n 2) = sl ∧ l13σ rd x mc sl cb (.n 3) = cb ∧
      l13σ rd x mc sl cb (.n 407) = x * gen + gen ^ 8 ∧
      l13σ rd x mc sl cb (.n 409) = x * gen ∧ l13σ rd x mc sl cb (.n 15) = sl * x ^ 8 ∧
      l13σ rd x mc sl cb (.n 203) = cb * x ^ 8 := by
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = l13σ rd x mc sl cb := ⟨_, rfl⟩
  rw [← hσdef]
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) loop13T [x, mc, sl, cb] l13_chk
  rw [show [x, mc, sl, cb].length = 4 from rfl, l13_stores, ← l13σ, ← hσdef] at hgs
  have mA : ∀ a, Stmt.atom a ∈ l13A → a ∈ rtAtoms l13A := fun a h ↦ rt_atoms_mem h
  have gA : ∀ a ∈ rtAtoms l13A, Good rd l13S (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (by rw [loop13T_split]; exact List.mem_append_left _ (rt_mem_atoms ha))
  have hpar : ∀ i (hi : i < 4), σ (.n i) = [x, mc, sl, cb].getD i 0 := fun i hi => by
    rw [hσdef]; exact ev_params rd _ (l := [x, mc, sl, cb]) l13_chk (by simpa using hi)
  have e0 := hpar 0 (by omega)
  have e1 := hpar 1 (by omega)
  have e2 := hpar 2 (by omega)
  have e3 := hpar 3 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3
  have mulE : ∀ d u v : ℕ, u < d → v < d → Stmt.atom (.mul (.n d) (.n u) (.n v)) ∈ l13A →
      σ (.n d) = σ (.n u) * σ (.n v) := by
    intro d u v hu hv hm
    have := gA _ (mA _ hm)
    simp only [Good] at this
    rwa [ite_pos' ⟨hu, hv⟩] at this
  have constE : ∀ d : ℕ, ∀ c : E, Stmt.atom (.const (.n d) c) ∈ l13A → σ (.n d) = c :=
    fun d c h ↦ gA _ (mA _ h)
  have addE : ∀ d u v : ℕ, Stmt.atom (.add (.n d) (.n u) (.n v)) ∈ l13A →
      σ (.n d) = σ (.n u) + σ (.n v) := fun d u v h ↦ gA _ (mA _ h)
  have m1 : ∀ s ∈ l13M1, s ∈ l13A := fun s h ↦ l13A_mem (Or.inr (Or.inl h))
  have m2 : ∀ s ∈ l13M2, s ∈ l13A := fun s h ↦ l13A_mem (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have mT : ∀ s ∈ l13T, s ∈ l13A := fun s h ↦
    l13A_mem (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  have e12 := mulE 12 0 0 (by omega) (by omega) (m1 _ (by simp [l13M1]))
  have e13 := mulE 13 12 12 (by omega) (by omega) (m1 _ (by simp [l13M1]))
  have e14 := mulE 14 13 13 (by omega) (by omega) (m1 _ (by simp [l13M1]))
  have e15 := mulE 15 2 14 (by omega) (by omega) (m1 _ (by simp [l13M1]))
  have e200 := mulE 200 0 0 (by omega) (by omega) (m2 _ (by simp [l13M2]))
  have e201 := mulE 201 200 200 (by omega) (by omega) (m2 _ (by simp [l13M2]))
  have e202 := mulE 202 201 201 (by omega) (by omega) (m2 _ (by simp [l13M2]))
  have e203 := mulE 203 3 202 (by omega) (by omega) (m2 _ (by simp [l13M2]))
  have hσ15 : σ (.n 15) = sl * x ^ 8 := by rw [e15, e14, e13, e12, e2, e0]; ring
  have hσ203 : σ (.n 203) = cb * x ^ 8 := by rw [e203, e202, e201, e200, e3, e0]; ring
  -- the loads' side conditions
  have hside : ∀ a ∈ rtAtoms l13A, a ∉ l13S → needsSide a = true → a.Holds rd σ ∨ Side rd l13S σ a := by
    intro a ha haS hns
    right
    have hok := List.all_eq_true.mp l13_needs a ha
    simp only [hns, Bool.not_true, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hok
    rcases hok with h | h
    · exact absurd h haS
    · match a, h with
      | .load d (.n 1) off, h =>
        simp only [l13LoadOk, decide_eq_true_eq] at h
        simp only [Side, ite_neg' haS, e1]
        have := hg (off - 8) (by omega)
        rw [show 8 + (off - 8) = off by omega] at this
        exact rt_side_of_load this
      | .load d (.n 15) off, h =>
        simp only [l13LoadOk, decide_eq_true_eq] at h
        simp only [Side, ite_neg' haS, hσ15]
        exact rt_side_of_load (hvs off (by omega))
      | .load d (.n 203) off, h =>
        simp only [l13LoadOk, decide_eq_true_eq] at h
        simp only [Side, ite_neg' haS, hσ203]
        exact rt_side_of_load (hr0 off h)
  -- the non-store atoms
  have hnon : ∀ a ∈ rtAtoms l13A, a ∉ l13S → a.Holds rd σ := by
    have := atoms_holds (S := l13S) (w := fun _ => 0) (atoms := (rtAtoms l13A).filter
      fun a => decide (a ∉ l13S)) (fun a ha => gA a (List.mem_filter.mp ha).1)
      (fun a ha hns => hside a (List.mem_filter.mp ha).1 (by simpa using (List.mem_filter.mp ha).2) hns)
    exact fun a ha haS => this a (List.mem_filter.mpr ⟨ha, by simpa using haS⟩)
  have hblk : ∀ ss : List Stmt, (∀ s ∈ ss, s ∈ l13A) → ss.all nsAtom = true →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ ss True (fun _ => True) := by
    intro ss hsub hns
    refine holdsList_of_atoms ss (fun s hs => ?_) trivial
    have := List.all_eq_true.mp hns s hs
    cases s with
    | atom a => exact ⟨a, rfl, hnon a (mA a (hsub _ hs)) (by simpa [nsAtom] using this)⟩
    | _ => simp [nsAtom] at this
  -- the challenges
  have notS : ∀ d p off, p ≠ (.n 203 : V) → Atom.load d p off ∉ l13S := by
    intro d p off hp hm
    obtain ⟨k, -, hk⟩ := List.mem_map.mp hm
    simp only [Atom.load.injEq] at hk
    exact hp hk.2.1.symm
  have hgv : gVals σ = gs := by
    apply List.ext_getElem (by simp [gVals, hgl])
    intro b h1 h2
    simp only [gVals, List.length_map, List.length_range] at h1
    simp only [gVals, List.getElem_map, List.getElem_range]
    have hm : Stmt.atom (.load (.n (4 + b)) (.n 1) (8 + b)) ∈ l13A :=
      l13A_mem (Or.inl (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨b, List.mem_range.mpr h1, rfl⟩,
        List.mem_singleton_self _⟩))
    have l := hnon _ (mA _ hm) (notS _ _ _ (by decide))
    simp only [Atom.Holds] at l
    rw [e1] at l
    have := hg b h1
    rw [List.getD_eq_getElem _ _ h2] at this
    exact loadHolds_unique l this
  -- the rows of `Ψ`
  have hrow : ∀ r < 8, σ (.n (psBase r)) = vs.getD r 0 ∧
      σ (.n (psBase r + 22)) = ringPsi (vs.getD r 0) gs := by
    intro r hr
    obtain ⟨l, e⟩ := holds_psRowAt (hblk (psRow r) (fun s hs => mem_l13P hr hs)
      (List.all_eq_true.mp l13P_ns r (List.mem_range.mpr hr)))
    rw [hσ15] at l
    have hv := loadHolds_unique l (hvs r (by omega))
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact ⟨hv, by rw [e, hv, hgv]⟩
  have hpsv : psVals σ = vs.map (ringPsi · gs) := by
    apply List.ext_getElem (by simp [psVals, hvl])
    intro r h1 h2
    simp only [psVals, List.length_map, List.length_range] at h1
    simp only [psVals, List.getElem_map, List.getElem_range]
    rw [(hrow r h1).2, List.getD_eq_getElem _ _ (by omega)]
  -- the chains
  have hz : ∀ p < 8, σ (.n (hzBase p + 24)) =
      (vs.map (ringPsi · gs)).foldl (hstep (ofK (ringWK.getD p 0))) (acc p) := by
    intro p hp
    obtain ⟨l, e⟩ := holds_hzPre hp (hblk (hzPre p) (fun s hs => mem_l13H hp hs)
      (List.all_eq_true.mp l13H_ns p (List.mem_range.mpr hp)))
    rw [hσ203] at l
    rw [e, hpsv, loadHolds_unique l (hr0 p hp)]
  -- the tail's values
  have e404 := constE 404 (word 2 0) (mT _ (by simp [l13T]))
  have e405 := mulE 405 0 404 (by omega) (by omega) (mT _ (by simp [l13T]))
  have e406 := constE 406 (word 256 0) (mT _ (by simp [l13T]))
  have e407 := addE 407 405 406 (mT _ (by simp [l13T]))
  have e408 := constE 408 (word 2 0) (mT _ (by simp [l13T]))
  have e409 := mulE 409 0 408 (by omega) (by omega) (mT _ (by simp [l13T]))
  refine ⟨fun a ha => ?_, e0, e1, e2, e3, ?_, ?_, hσ15, hσ203⟩
  · by_cases haS : a ∈ l13S
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp haS
      have hp8 := List.mem_range.mp hp
      show LoadHolds rd (σ (.n 203)) (8 + p) (σ (.n (hzBase p + 24)))
      rw [hσ203, hz p hp8]
      exact hr1 p hp8
    · exact hnon a ha haS
  · rw [e407, e405, e404, e406, e0, word_gen, ← word_two_pow (by decide : 8 < 64)]; rfl
  · rw [e409, e408, e0, word_gen]

/-! ## The loop, loading the slices, the challenges and the chain -/

/-- The loads of `__loop13`'s block: the challenges (`1`), the slices (`15`), the chain's row and
the next (`203`). -/
def l13LoadIn : Atom → Bool
  | .load _ (.n 1) off => decide (off < 16)
  | .load _ (.n 15) off => decide (off < 8)
  | .load _ (.n 203) off => decide (off < 16)
  | .load .. => false
  | _ => true

theorem l13LoadIn_load {d p : V} {off : ℕ} (h : l13LoadIn (.load d p off) = true) :
    (p = .n 1 ∧ off < 16) ∨ (p = .n 15 ∧ off < 8) ∨ (p = .n 203 ∧ off < 16) := by
  unfold l13LoadIn at h
  split at h <;> simp_all

theorem l13_loadIn : (rtAtoms l13A).all l13LoadIn = true := by decide +kernel

/-- `__loop13`'s statements before its `ret`. -/
def l13Pre : List Stmt := l13A ++ [Stmt.callIf (.n 407) "__loop13" [.n 409, .n 1, .n 2, .n 3]]

theorem l13_body_pre : Data.core272.body = l13Pre ++ [.ret []] := by
  rw [loop13_body, loop13T_split, l13Pre, List.append_assoc]
  rfl

theorem l13_straight : l13Pre.all Main.Stmt.straight = true := by decide +kernel

theorem l13_callS : l13Pre.filterMap Main.Stmt.callS =
    [(some (.n 407), "__loop13", [.n 409, .n 1, .n 2, .n 3], [])] := by decide +kernel

/-- **One iteration of `__loop13`, loading its regions**: at `g^j`, `j < 8`, over the honest
chain, the next iteration's relation (while `j < 7`) gives this one's. -/
theorem l13_iter {rd : Reader} {bs bm bc : ℕ} {s chs : List E} (hs : s.length = 64)
    (hc : chs.length = 16) (hsl : ReadsAt rd (ofK (Parameters.addressOfIndex bs)) s)
    (hmc : ReadsAt rd (ofK (Parameters.addressOfIndex bm)) chs)
    (hch : ReadsAt rd (ofK (Parameters.addressOfIndex bc)) (chainWords s (chs.drop 8)))
    {R : ℕ → Prop}
    (hR : ∀ i, (bs ≤ i ∧ i < bs + 64) ∨ (bm ≤ i ∧ i < bm + 16) ∨ (bc ≤ i ∧ i < bc + 72) → R i)
    {j : ℕ} (hj : j < 8)
    (hnext : j < 7 → coreProgram.RelIn rd R "__loop13" [gen ^ (j + 1),
      ofK (Parameters.addressOfIndex bm), ofK (Parameters.addressOfIndex bs),
      ofK (Parameters.addressOfIndex bc)] []) :
    coreProgram.RelIn rd R "__loop13" [gen ^ j, ofK (Parameters.addressOfIndex bm),
      ofK (Parameters.addressOfIndex bs), ofK (Parameters.addressOfIndex bc)] [] := by
  have hgl : (chs.drop 8).length = 8 := by simp [hc]
  have hg : ∀ b < 8, LoadHolds rd (ofK (Parameters.addressOfIndex bm)) (8 + b)
      ((chs.drop 8).getD b 0) := by
    intro b hb
    rw [List.getD_eq_getElem _ _ (by omega), List.getElem_drop]
    exact hmc (8 + b) (by omega)
  have hvl : ((s.drop (8 * j)).take 8).length = 8 := by simp [hs]; omega
  have hvs : ReadsAt rd (ofK (Parameters.addressOfIndex bs) * (gen ^ j) ^ 8)
      ((s.drop (8 * j)).take 8) := by
    intro k hk
    rw [← pow_mul, show j * 8 = 8 * j by ring, loadHolds_mul_gen_pow]
    simp only [List.getElem_take, List.getElem_drop]
    exact hsl _ (by rw [hs]; rw [hvl] at hk; omega)
  have hr0 : ∀ p < 8, LoadHolds rd (ofK (Parameters.addressOfIndex bc) * (gen ^ j) ^ 8) p
      (rtHz s (chs.drop 8) p (8 * j)) := by
    intro p hp
    rw [← pow_mul, show j * 8 = 8 * j by ring, loadHolds_mul_gen_pow]
    exact chain_load hch (by omega) hp
  have hr1 : ∀ p < 8, LoadHolds rd (ofK (Parameters.addressOfIndex bc) * (gen ^ j) ^ 8) (8 + p)
      ((((s.drop (8 * j)).take 8).map (ringPsi · (chs.drop 8))).foldl
        (hstep (ofK (ringWK.getD p 0))) (rtHz s (chs.drop 8) p (8 * j))) := by
    intro p hp
    rw [← pow_mul, show j * 8 = 8 * j by ring, loadHolds_mul_gen_pow, ← rtHz_succ,
      show 8 * j + (8 + p) = 8 * (j + 1) + p by ring, show 8 * j + 8 = 8 * (j + 1) by ring]
    exact chain_load hch (by omega) hp
  obtain ⟨hat, e0, e1, e2, e3, e407, e409, e15, e203⟩ := l13_block hgl hvl hg hvs hr0 hr1
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = l13σ rd (gen ^ j) (ofK (Parameters.addressOfIndex bm))
      (ofK (Parameters.addressOfIndex bs)) (ofK (Parameters.addressOfIndex bc)) := ⟨_, rfl⟩
  rw [← hσdef] at hat e0 e1 e2 e3 e407 e409 e15 e203
  have hw := Main.walk_straight σ [] l13Pre l13_straight
  rw [← l13_body_pre] at hw
  have hev : ∀ e ∈ l13Pre.flatMap (Main.slEvs σ), (∃ a ∈ rtAtoms l13A, e = .atom a) ∨
      e = .inK (.n 407) ∨ e = .skip "__loop13" [.n 409, .n 1, .n 2, .n 3] ∨
      e = .call "__loop13" [.n 409, .n 1, .n 2, .n 3] [] := by
    intro e he
    obtain ⟨st, hst, he⟩ := List.mem_flatMap.mp he
    rw [l13Pre, List.mem_append] at hst
    rcases hst with hst | hst
    · have := List.all_eq_true.mp l13_allAtoms st hst
      cases st <;> simp only [Bool.false_eq_true] at this
      rename_i a
      simp only [Main.slEvs, List.mem_singleton] at he
      exact Or.inl ⟨a, rt_atoms_mem hst, he⟩
    · simp only [List.mem_singleton] at hst
      subst hst
      simp only [Main.slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | he
      · exact Or.inr (Or.inl rfl)
      · split at he <;> subst he <;> simp
  refine relIn_of_walk coreProgram_wf find_loop13 ?_ hw rfl ?_ ?_ ?_
  · show [Core.V.n 0, .n 1, .n 2, .n 3].map σ = _
    simp only [List.map_cons, List.map_nil, e0, e1, e2, e3]
  · intro e he
    rcases hev e he with ⟨a, ha, rfl⟩ | rfl | rfl | rfl
    · exact hat a ha
    · show IsInK (σ (.n 407))
      rw [e407]
      exact isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1))
        (gen_pow_isInK 8)
    · trivial
    · trivial
  · intro A hA
    obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
    rcases hev e he with ⟨a, ha, rfl⟩ | rfl | rfl | rfl
    · have hok := List.all_eq_true.mp l13_loadIn a ha
      cases a with
      | load d p off =>
        simp only [Ev.loadAddr?, Option.some.injEq] at hea
        subst hea
        rcases l13LoadIn_load hok with ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩
        · rw [e1, Main.addr_ofK]
          exact ⟨_, rfl, hR _ (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩
        · rw [e15, ← pow_mul, rt_addr_mul]
          exact ⟨_, rfl, hR _ (Or.inl ⟨by omega, by omega⟩)⟩
        · rw [e203, ← pow_mul, rt_addr_mul]
          exact ⟨_, rfl, hR _ (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩
      | _ => simp [Ev.loadAddr?] at hea
    · simp [Ev.loadAddr?] at hea
    · simp [Ev.loadAddr?] at hea
    · simp [Ev.loadAddr?] at hea
  · intro c hc htaken
    rw [(Main.straight_parts σ l13Pre l13_straight).2.2.2, l13_callS] at hc
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
    subst hc
    simp only [Main.mkCall, decide_eq_true_eq] at htaken ⊢
    have hj7 : j < 7 := by
      by_contra hj7
      have : j = 7 := by omega
      subst this
      exact htaken (by rw [e407, gen_pow_mul_gen]; exact e_add_self _)
    simp only [List.map_cons, List.map_nil, e409, e1, e2, e3, gen_pow_mul_gen]
    exact hnext hj7

/-- **`__loop13`, completely, loading its regions**: over the honest chain, from `g^j`, `j ≤ 7`. -/
theorem l13_relIn {rd : Reader} {bs bm bc : ℕ} {s chs : List E} (hs : s.length = 64)
    (hc : chs.length = 16) (hsl : ReadsAt rd (ofK (Parameters.addressOfIndex bs)) s)
    (hmc : ReadsAt rd (ofK (Parameters.addressOfIndex bm)) chs)
    (hch : ReadsAt rd (ofK (Parameters.addressOfIndex bc)) (chainWords s (chs.drop 8)))
    {R : ℕ → Prop}
    (hR : ∀ i, (bs ≤ i ∧ i < bs + 64) ∨ (bm ≤ i ∧ i < bm + 16) ∨ (bc ≤ i ∧ i < bc + 72) → R i) :
    ∀ t j, j + t = 7 → coreProgram.RelIn rd R "__loop13"
      [gen ^ j, ofK (Parameters.addressOfIndex bm), ofK (Parameters.addressOfIndex bs),
        ofK (Parameters.addressOfIndex bc)] [] := by
  intro t
  induction t with
  | zero => exact fun j hj ↦ l13_iter hs hc hsl hmc hch hR (by omega) fun h ↦ absurd h (by omega)
  | succ t ih => exact fun j hj ↦ l13_iter hs hc hsl hmc hch hR (by omega) fun _ ↦ ih (j + 1) (by omega)

end
end LeanVM.Guest.B1.VerifySub
