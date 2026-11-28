/-
  LeanVM.Guest.B1.VsC.TerminalA

  `link_terminal__L{w}` completes placed, its eq tables its own `HeapBuf`.
-/

module

public import LeanVM.Guest.B1.VsC.EqTreeC
public import LeanVM.Guest.B1.VsC.LinkCalleesA
public import LeanVM.Guest.B1.VsC.CalleesB
public import LeanVM.Guest.B1.VsC.LeafA
public import LeanVM.Guest.B1.Link.Terminal
public import LeanVM.Guest.B1.Whir.Flat
public import LeanVM.Guest.Memory.Retemp
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.Memory.Restrict
public import Mathlib.Data.Nat.Log
import LeanVM.Guest.CoreRef

/-!
# `link_terminal`, placed

`link_terminal__L{w}` (`ltBody`, `19 ≤ w ≤ 24`) placed at frame `fp`, its cursor `c` right after:
its `allocDyn` buffer of `ltSize = step·d` words at `c`, its own words `ltWords` there (chunk `i`'s
level `t` of `eqKernel` of its part of the index point at `step·i + 2^t - 2`), by `callAtA_fwd` on
the forward evaluation with the buffer at `c`.

* The stores are `eqtree`'s (`ltStores`, by the kernel), each holding by `eqtreeAt_complete` once
  the atoms that are not stores do; the template's reads (`ltReads`) are not stores.
* The claim `.n 7` occurs only in the final `assertEq`. On `fwdVal` with `.n 7` set to the
  checked value (`ltSet`) every atom holds, so the soundness stream's `lt_check` gives the summand
  plus `rest`, which the hypothesis on `claim` makes the claim: the assert's converse.

What the kernel checks per specialization (`ltOk`): the forward shape, every atom's side condition
(loads through the arguments' arrays or the buffer, the one `assertEq`), the claim's one use, the
stores, the reads apart from them, the one allocation, the return, the buffer's size word.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Guest.Value

@[expose] public section

/-! ## The own words -/

/-- The buffer's size: one stride per chunk. -/
def ltSize (c : Chunks) : ℕ := ltStep c * c.d

/-- The buffer's word at `o`: chunk `o / step`'s level `t` entry `j`, `o % step = 2^t - 2 + j`. -/
def ltEntry (c : Chunks) (rs : List E) (o : ℕ) : E :=
  (eqKernel ((c.part rs (o / ltStep c)).take (Nat.log 2 (o % ltStep c + 2)))).getD
    (o % ltStep c + 2 - 2 ^ Nat.log 2 (o % ltStep c + 2)) 0

/-- `link_terminal`'s own words: its buffer. -/
def ltWords (c : Chunks) (rs : List E) : List E := (List.range (ltSize c)).map (ltEntry c rs)

theorem ltEntry_at {c : Chunks} (rs : List E) {i t j : ℕ} (hle : cW c i ≤ cW c 0) (ht1 : 1 ≤ t)
    (ht : t ≤ cW c i) (hj : j < 2 ^ t) :
    ltStep c * i + (2 ^ t - 2 + j) < ltStep c * (i + 1) ∧
      ltEntry c rs (ltStep c * i + (2 ^ t - 2 + j)) = (eqKernel ((c.part rs i).take t)).getD j 0 := by
  have h2 : 2 ≤ 2 ^ t := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht1
  have hlt : 2 ^ t + j < 2 ^ (t + 1) := by rw [pow_succ]; omega
  have hst : 2 ^ (t + 1) ≤ ltStep c := by
    unfold ltStep; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < ltStep c := by omega
  have hr : 2 ^ t - 2 + j < ltStep c := by omega
  refine ⟨by rw [Nat.mul_succ]; omega, ?_⟩
  unfold ltEntry
  rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hr, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hr,
    show 2 ^ t - 2 + j + 2 = 2 ^ t + j by omega,
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) hlt, show 2 ^ t + j - 2 ^ t = j by omega]
  simp only [Nat.add_zero]

/-- **The buffer holds the levels.** -/
theorem ltWords_load {rd : Reader} {c : Chunks} {rs : List E} {b : ℕ}
    (hle : ∀ i < c.d, cW c i ≤ cW c 0) (h : ReadsAt rd (ofK (addressOfIndex b)) (ltWords c rs)) :
    ∀ i < c.d, ∀ t, 1 ≤ t → t ≤ cW c i → ∀ j < 2 ^ t,
      LoadHolds rd (ofK (addressOfIndex b)) (ltStep c * i + (2 ^ t - 2 + j)) ((eqKernel ((c.part rs i).take t)).getD j 0) := by
  intro i hi t ht1 ht j hj
  obtain ⟨hlt, he⟩ := ltEntry_at rs (hle i hi) ht1 ht hj
  have hk : ltStep c * i + (2 ^ t - 2 + j) < (ltWords c rs).length := by
    simp only [ltWords, ltSize, List.length_map, List.length_range]
    calc _ < ltStep c * (i + 1) := hlt
      _ ≤ ltStep c * c.d := Nat.mul_le_mul_left _ hi
  have := h _ hk
  simp only [ltWords, List.getElem_map, List.getElem_range] at this
  rwa [he] at this

/-! ## The template's parts -/

/-- `link_terminal`'s stores: each chunk's `eqtree`'s. -/
def ltStores (c : Chunks) : List Atom :=
  ((List.range c.d).map fun i ↦ eqStoresAt (.n 9) (ltStep c * i) (ltEqS c i) (cW c i)).flatten

/-- `link_terminal`'s `eqtree` reads. -/
def ltReads (c : Chunks) : List Atom :=
  ((List.range c.d).map fun i ↦ eqReadsAt (.n 0) (.n 9) (cI c i) (ltStep c * i) (ltEqS c i) (cW c i)).flatten

/-- The statements after the buffer's allocation. -/
def ltTail (c : Chunks) : List Stmt :=
  ((List.range c.d).map fun i ↦ eqtreeAt (.n 0) (.n 9) (cI c i) (ltStep c * i) (ltEqS c i) (cW c i)).flatten ++
  ((List.range c.d).map (ltD c)).flatten ++
  [.atom (.mul (.n (ltLow0 c)) (.n 2) (.n (ltVal c 0)))] ++
  ((List.range 12).map fun s ↦ ltShBlk c (s + 1)).flatten ++
  ((List.range (c.d - 1)).map fun i ↦ .atom (.mul (.n (ltL c + i + 1)) (.n (ltL c + i)) (.n (ltVal c (i + 1))))) ++
  ((List.range c.d).map (ltCertBlk c)).flatten ++
  [.atom (.add (.n (ltF c)) (.n (ltL c + c.d - 1)) (.n (ltCert c (c.d - 1)))),
    .atom (.add (.n (ltF c + 1)) (.n (ltF c)) (.n 6)), .atom (.assertEq (.n (ltF c + 1)) (.n 7)),
    .atom (.const (.n (ltF c + 2)) (word 0 0)), .ret [.n (ltF c + 2)]]

theorem ltBody_eq (c : Chunks) (cw : ℕ) :
    ltBody c cw = .atom (.const (.n 8) (word cw 0)) :: .atom (.hint (.allocDyn (.n 9) (.n 8))) :: ltTail c := by
  simp only [ltBody, ltAtoms, ltTail, List.cons_append, List.nil_append, List.append_assoc]

/-- An atom of `link_terminal`'s body: a load through `r` (`.n 0`), `sent[80 ..]` (`.n 1`),
`shifts` (`.n 3`), `nu` (`.n 5`) or the buffer (`.n 9`) within their lengths, the one `assertEq`,
the buffer's `allocDyn`, or an atom with no side condition and no hint. -/
def ltAtomOkB (c : Chunks) : Atom → Bool
  | .load _ p k => (p == .n 0 && decide (k < c.width)) || (p == .n 1 && decide (80 ≤ k) && decide (k < 144)) ||
      (p == .n 3 && decide (k < 12)) || (p == .n 5 && decide (k < c.d)) || (p == .n 9 && decide (k < ltSize c))
  | .assertEq x y => x == .n (ltF c + 1) && y == .n 7
  | .hint (.allocDyn ..) => true
  | .hint _ => false
  | a => !needsSide a

/-- The claim `.n 7` is named by the final `assertEq` alone. -/
def ltNo7B (c : Chunks) (a : Atom) : Bool :=
  a == .assertEq (.n (ltF c + 1)) (.n 7) || !((atomUses a ++ atomTmps a).contains (.n 7))

/-- **What the kernel checks of `link_terminal__L{w}`**, at the chunking `c` and size word `cw`. -/
def ltOk (c : Chunks) (cw : ℕ) : Bool :=
  leafChecks 8 (ltBody c cw) && (atomsOf (ltBody c cw)).all (fun a => ltAtomOkB c a && ltNo7B c a) &&
    decide (storesOf 8 (ltBody c cw) = ltStores c) && (ltReads c).all (fun a => !decide (a ∈ ltStores c)) &&
    (atomsOf (ltTail c)).all (fun a => !atomAllocB a) && retOf (ltBody c cw) == some [.n (ltF c + 2)] &&
    decide (Pow.gpowN (ltSize c) = cw) && decide (ltSize c < 2 ^ 20) &&
    (List.range c.d).all (fun i => decide (cW c i ≤ cW c 0)) && decide (ltF c ≠ 6)

theorem mem_ltStores {c : Chunks} {a : Atom} (h : a ∈ ltStores c) :
    ∃ i < c.d, a ∈ eqStoresAt (.n 9) (ltStep c * i) (ltEqS c i) (cW c i) := by
  obtain ⟨l, hl, ha⟩ := List.mem_flatten.mp h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
  exact ⟨i, List.mem_range.mp hi, ha⟩

theorem mem_ltReads {c : Chunks} {i : ℕ} (hi : i < c.d) {a : Atom}
    (h : a ∈ eqReadsAt (.n 0) (.n 9) (cI c i) (ltStep c * i) (ltEqS c i) (cW c i)) : a ∈ ltReads c :=
  List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, h⟩

theorem part_getD {c : Chunks} (hc : ChunkOk c) {rs : List E} (hrs : rs.length = c.width) {i t : ℕ}
    (hi : i < c.d) (ht : t < cW c i) :
    cI c i + t < rs.length ∧ (c.part rs i).getD t 0 = rs.getD (cI c i + t) 0 := by
  have hk : cI c i + t < rs.length := by have := hc.idx i hi; omega
  refine ⟨hk, ?_⟩
  have ht' : t < c.widths[i]?.getD 0 := by simpa [cW, List.getD_eq_getElem?_getD] using ht
  simp only [Chunks.part, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, ht', ↓reduceIte]
  rfl

theorem part_length {c : Chunks} (hc : ChunkOk c) {rs : List E} (hrs : rs.length = c.width) {i : ℕ}
    (hi : i < c.d) : (c.part rs i).length = cW c i := by
  simp only [Chunks.part, List.length_take, List.length_drop, cW] at *
  have := hc.idx i hi; simp only [cW, cI] at this; omega

theorem word_gpowN {N cw : ℕ} (hN : N < 2 ^ 20) (h : Pow.gpowN N = cw) : word cw 0 = gen ^ N := by
  rw [← Whir.gw_eq (by unfold u128Bound; omega), Whir.gw, show Nat.blt N (2 ^ 20) = true from Nat.blt_eq.mpr hN,
    Bool.cond_true, h]
  rfl

/-! ## Placed -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- The valuation with the claim `.n 7` set to `x`. -/
def ltSet (σ : Val) (x : E) : Val := fun v => if v = .n 7 then x else σ v

set_option maxHeartbeats 1000000 in
/-- **`link_terminal__L{w}` completes placed**, from its template's kernel checks. -/
theorem lt_placed {k w cw : ℕ} {name : String} {fn : Fn} {c : Chunks} (hcw : Chunks.new w = some c)
    (hc : ChunkOk c) (hfind : coreProgram.find? name = some fn) (hlp : coreProgram.loop name = false)
    (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]) (hbody : fn.body = ltBody c cw)
    (hok : ltOk c cw = true) (hd : c.d ≤ 64) :
    LinkTerminalCompleteAE fs al cert k w name (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) := by
  intro c' hc' r sent coef shifts certW nu rest claim rs sl shs nus fp hrs hsll hshl hnul hclaim hpb
  obtain rfl : c = c' := Option.some.inj (hcw.symm.trans hc')
  simp only [ltOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, hat⟩, hS⟩, hrdS⟩, hna⟩, hret⟩, hgp⟩, hN⟩, hle⟩, hF⟩ := hok
  set c0 := fp + fs name with hc0
  set args : List E := [r, sent, coef, shifts, certW, nu, rest, claim] with hargs
  have hck' : leafChecks args.length fn.body = true := by rw [hbody]; exact hck
  obtain ⟨c'', hchk⟩ := Option.isSome_iff_exists.mp (by
    simp only [leafChecks, Bool.and_eq_true] at hck'; exact hck'.1.1)
  have hsum : c0 + [ltSize c].sum = c0 + ltSize c := by simp
  have hle' : ∀ i < c.d, cW c i ≤ cW c 0 := fun i hi => hle i (List.mem_range.mpr hi)
  have hub : FsSmall fs → c0 + [ltSize c].sum ≤ c0 + 2 ^ 21 := fun _ => by
    have h32 : ltSize c = 32 * c.d := by simp [ltSize, ltStep, hc.w0]
    rw [hsum, h32]
    have := hd
    omega
  refine ⟨c0 + [ltSize c].sum, hub, callAtA_fwd (fun _ => ofK (addressOfIndex c0)) [ltSize c] [(c0, ltWords c rs)]
    hfind hlp (by rw [hparams]; rfl) hck' ⟨fun q hq => ?_, List.pairwise_singleton _ _⟩ (fun _ _ => trivial)
    (fun _ h => h.elim) fun rd _ hw ⟨hr, hsl, hsh, hnu⟩ σ hσ => ?_⟩
  · rw [List.mem_singleton] at hq; subst hq
    right; simp [ltWords]
  have hW := ltWords_load hle' (hw _ List.mem_cons_self)
  have hWr : ReadsAt rd (ofK (addressOfIndex c0)) (ltWords c rs) := hw _ List.mem_cons_self
  set S := storesOf args.length fn.body with hSdef
  have hSe : S = ltStores c := by rw [hSdef, hbody]; exact hS
  have hG : ∀ a, Stmt.atom a ∈ fn.body → Good rd S (fun _ => ofK (addressOfIndex c0)) σ a :=
    fun a ha => hσ ▸ fwd_good hchk a ha
  have hp : ∀ i (hi : i < 8), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact fwd_param hchk (by simpa [hargs] using hi)
  have hmem : ∀ a, Stmt.atom a ∈ ltAtoms c cw → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody, ltBody]; exact List.mem_append_left _ ha
  have hσ8 : σ (.n 8) = word cw 0 := hG (.const (.n 8) (word cw 0)) (by rw [hbody, ltBody_eq]; simp)
  have hσ9 : σ (.n 9) = ofK (addressOfIndex c0) :=
    hG (.hint (.allocDyn (.n 9) (.n 8))) (by rw [hbody, ltBody_eq]; simp)
  have hok' : ∀ a, Stmt.atom a ∈ fn.body → ltAtomOkB c a = true ∧ ltNo7B c a = true := fun a ha => by
    have := hat a (mem_atomsOf' (hbody ▸ ha)); simpa only [Bool.and_eq_true] using this
  have hσ0 : σ (.n 0) = r := hp 0 (by norm_num)
  have hσ1 : σ (.n 1) = sent := hp 1 (by norm_num)
  have hσ3 : σ (.n 3) = shifts := hp 3 (by norm_num)
  have hσ5 : σ (.n 5) = nu := hp 5 (by norm_num)
  -- every load reads a defined word, and where
  have hload : ∀ d p off, Stmt.atom (.load d p off) ∈ fn.body →
      (p = .n 0 ∧ off < rs.length) ∨ (p = .n 1 ∧ 80 ≤ off ∧ off < 144) ∨ (p = .n 3 ∧ off < 12) ∨
        (p = .n 5 ∧ off < nus.length) ∨ (p = .n 9 ∧ off < ltSize c) := fun d p off ha => by
    have h := (hok' _ ha).1
    simp only [ltAtomOkB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rw [hrs, hnul]
    rcases h with (((h | h) | h) | h) | h
    exacts [Or.inl h, Or.inr (Or.inl ⟨h.1.1, h.1.2, h.2⟩), Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inl h))), Or.inr (Or.inr (Or.inr (Or.inr h)))]
  have hdef : ∀ d p off, Stmt.atom (.load d p off) ∈ fn.body → ∃ x, LoadHolds rd (σ p) off x := by
    intro d p off ha
    rcases hload d p off ha with ⟨rfl, h⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact ⟨_, hσ0 ▸ hr off h⟩
    · have := hsl (off - 80) (by omega)
      rw [show 80 + (off - 80) = off by omega] at this
      exact ⟨_, hσ1 ▸ this⟩
    · exact ⟨_, hσ3 ▸ hsh off (by omega)⟩
    · exact ⟨_, hσ5 ▸ hnu off h⟩
    · exact ⟨_, hσ9 ▸ hWr off (by simpa [ltWords] using h)⟩
  have hside : ∀ d p off, Stmt.atom (.load d p off) ∈ fn.body →
      IsInK (σ p) ∧ (rd ((σ p).limb 0 * addressOfIndex off)).isSome := fun d p off ha => by
    obtain ⟨x, hx1, hx2⟩ := hdef d p off ha
    exact ⟨hx1, by rw [hx2]; rfl⟩
  -- the atoms other than the assert, the stores apart
  have hns : ∀ a, Stmt.atom a ∈ fn.body → a ∉ S → a ≠ .assertEq (.n (ltF c + 1)) (.n 7) → a.Holds rd σ := by
    intro a ha hS' hne
    refine atoms_holds (atoms := [a]) (fun b hb => by rw [List.mem_singleton.mp hb]; exact hG a ha)
      (fun b hb hn => ?_) a List.mem_cons_self
    rw [List.mem_singleton.mp hb] at hn ⊢
    right
    cases a with
    | load d p off =>
      simp only [Side, hS', ↓reduceIte]
      exact hside d p off ha
    | assertEq x y =>
      have h := (hok' _ ha).1
      simp only [ltAtomOkB, Bool.and_eq_true, beq_iff_eq] at h
      exact absurd (by rw [h.1, h.2]) hne
    | hint h =>
      cases h <;> simp [needsSide] at hn
    | _ =>
      have h := (hok' _ ha).1
      simp only [ltAtomOkB, hn, Bool.not_true, Bool.false_eq_true] at h
  -- the stores, from the atoms that are not
  have hstore : (∀ a, Stmt.atom a ∈ fn.body → a ∉ S → a ≠ .assertEq (.n (ltF c + 1)) (.n 7) → a.Holds rd σ) →
      ∀ a ∈ S, a.Holds rd σ := by
    intro hns' a haS
    obtain ⟨i, hi, hai⟩ := mem_ltStores (hSe ▸ haS)
    have hpl := part_length hc hrs hi
    refine eqtreeAt_complete (hc.wpos i hi) (S := S) (fun a ha => storesOf_isLoad ha)
      (fun a ha haS' => ?_) (fun a ha haS' => hns' a (hmem a (mem_ltAtoms_eqtree hi ha)) haS' ?_) hpl
      (fun t ht => ?_) (fun t ht1 ht j hj => ?_) a (eqStoresAt_mem hai)
    · have := hrdS a (mem_ltReads hi ha)
      rw [hSe] at haS'
      exact absurd (decide_eq_true haS') (by simpa using this)
    · rintro rfl
      rcases mem_eqtreeAt ha with h | h | h | h | h | ⟨t, -, -, (h | h | h | ⟨j, -, (h | h | h | h | h)⟩)⟩ <;>
        cases h
    · obtain ⟨hk, he⟩ := part_getD hc hrs hi ht
      rw [he, hσ0, List.getD_eq_getElem _ _ hk]; exact hr _ hk
    · rw [hσ9]; exact hW i hi t ht1 (hpl ▸ ht) j hj
  have hA0 : ∀ a, Stmt.atom a ∈ fn.body → a ≠ .assertEq (.n (ltF c + 1)) (.n 7) → a.Holds rd σ := by
    intro a ha hne
    by_cases haS : a ∈ S
    · exact hstore hns a haS
    · exact hns a ha haS hne
  -- the claim checked: the soundness stream's `lt_check` with the claim set
  have hcheck : σ (.n (ltF c + 1)) = claim := by
    set σ' := ltSet σ (σ (.n (ltF c + 1))) with hσ'
    have h7 : ∀ v, v ≠ .n 7 → σ' v = σ v := fun v hv => by simp [hσ', ltSet, hv]
    have hA' : ∀ a, Stmt.atom a ∈ ltAtoms c cw → a.Holds rd σ' := by
      intro a ha
      by_cases hne : a = .assertEq (.n (ltF c + 1)) (.n 7)
      · subst hne
        show σ' (.n (ltF c + 1)) + σ' (.n 7) = 0
        rw [h7 _ (by simpa using hF)]
        simp only [hσ', ltSet, ↓reduceIte]
        exact add_self_E _
      · have h : V.n 7 ∉ atomUses a ++ atomTmps a := by
          simpa [ltNo7B, hne] using (hok' _ (hmem a ha)).2
        refine (atom_holds_congr a fun v hv => h7 v fun e => ?_).mpr (hA0 a (hmem a ha) hne)
        subst e; exact h hv
    have hL := lt_check hA' hc rs sl shs nus hrs hsll hshl hnul
      (by rw [h7 (.n 0) (by decide), hσ0]; exact hr)
      (by rw [h7 (.n 1) (by decide), hσ1]; exact hsl)
      (by rw [h7 (.n 3) (by decide), hσ3]; exact hsh)
      (by rw [h7 (.n 5) (by decide), hσ5]; exact hnu)
    have e7 : σ' (.n 7) = σ (.n (ltF c + 1)) := by simp only [hσ', ltSet, ↓reduceIte]
    rw [h7 (.n 2) (by decide), h7 (.n 4) (by decide), h7 (.n 6) (by decide), e7, hp 2 (by norm_num),
      hp 4 (by norm_num), hp 6 (by norm_num)] at hL
    rw [hclaim]
    exact hL.symm
  have hall : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ := by
    intro a ha
    by_cases hne : a = .assertEq (.n (ltF c + 1)) (.n 7)
    · subst hne
      show σ (.n (ltF c + 1)) + σ (.n 7) = 0
      rw [hcheck, hp 7 (by norm_num)]; exact add_self_E _
    · exact hA0 a ha hne
  have hatoms : atomsOf fn.body = .const (.n 8) (word cw 0) :: .hint (.allocDyn (.n 9) (.n 8)) ::
      atomsOf (ltTail c) := by rw [hbody, ltBody_eq]; rfl
  refine ⟨fun a ha haS hn => ?_, fun _ a ha => hall a (storesOf_mem ha), fun a ha => ?_, fun vs hvs => ?_, ?_, ?_,
    fun A hA => ?_⟩
  · -- the side conditions
    cases a with
    | load d p off =>
      simp only [Side, haS, ↓reduceIte]
      exact hside d p off ha
    | assertEq x y =>
      have h := (hok' _ ha).1
      simp only [ltAtomOkB, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      show σ (.n (ltF c + 1)) + σ (.n 7) = 0
      rw [hcheck, hp 7 (by norm_num)]
      exact add_self_E _
    | hint h =>
      cases h <;> simp [needsSide] at hn
    | _ =>
      have h := (hok' _ ha).1
      simp only [ltAtomOkB, hn, Bool.not_true, Bool.false_eq_true] at h
  · have h := (hok' _ ha).1
    cases a with
    | hint hh => cases hh <;> simp_all [ltAtomOkB, Atom.Exact, Hint.Exact]
    | _ => trivial
  · rw [hbody, hret, Option.some.injEq] at hvs
    subst hvs
    have h0 : σ (.n (ltF c + 2)) = word 0 0 := hG (.const (.n (ltF c + 2)) (word 0 0)) (hmem _ (mem_ltAtoms_fin (by simp)))
    simp [h0, word_zero]
  · rw [hatoms, List.map_cons, List.map_cons, show ∀ (x y : Ev) (l : List Ev), x :: y :: l = [x, y] ++ l
      from fun _ _ _ => rfl, allocs_append, allocs_atoms σ (List.all_eq_true.mpr hna)]
    simp only [allocs, List.filterMap_cons, List.filterMap_nil, Ev.alloc?, hσ8, List.append_nil]
    rw [word_gpowN hN hgp, gen_pow_eq_ofK, logG_spec (by omega)]
  · rw [hatoms, List.map_cons, List.map_cons, show ∀ (x y : Ev) (l : List Ev), x :: y :: l = [x, y] ++ l
      from fun _ _ _ => rfl, allocDsts_append, allocDsts_atoms (List.all_eq_true.mpr hna)]
    simp only [bases, List.map_cons, List.map_nil, List.append_nil, allocDsts, List.map_eq_singleton_iff]
    exact ⟨.n 9, rfl, hσ9⟩
  · obtain ⟨d, q, off, hm, rfl⟩ := mem_loadAddrs hA
    have hm' : Stmt.atom (.load d q off) ∈ fn.body := mem_of_mem_atomsOf hm
    rcases hload d q off hm' with ⟨rfl, h⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · obtain ⟨i, -, hi⟩ := hpb (r, rs.length) (by simp [ltArrays]) off h
      exact ⟨i, by rw [hσ0, hi], Or.inr ⟨_, by simp [ltArrays], off, h, hi⟩⟩
    · obtain ⟨i, -, hi⟩ := hpb (sent * gen ^ 80, 64) (by simp [ltArrays]) (off - 80) (by omega)
      have e : (sent * gen ^ 80).limb 0 * addressOfIndex (off - 80) = sent.limb 0 * addressOfIndex off := by
        rw [gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add,
          show 80 + (off - 80) = off by omega]
      exact ⟨i, by rw [hσ1, ← e, hi], Or.inr ⟨_, by simp [ltArrays], off - 80, by omega, hi⟩⟩
    · obtain ⟨i, -, hi⟩ := hpb (shifts, 12) (by simp [ltArrays]) off h
      exact ⟨i, by rw [hσ3, hi], Or.inr ⟨_, by simp [ltArrays], off, h, hi⟩⟩
    · obtain ⟨i, -, hi⟩ := hpb (nu, nus.length) (by simp [ltArrays]) off h
      exact ⟨i, by rw [hσ5, hi], Or.inr ⟨_, by simp [ltArrays], off, h, hi⟩⟩
    · exact ⟨c0 + off, by rw [hσ9]; exact Main.addr_ofK _ _, Or.inl ⟨by omega, by simp; omega⟩⟩

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem lt_L19_ok : ltOk ((Chunks.new 19).getD default) 7607 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem link_terminal_L19_completeA (k : ℕ) :
    LinkTerminalCompleteAE fs al cert k 19 "link_terminal__L19" (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) :=
  lt_placed (by decide +kernel) chunkOk_19 (coreProgram_find?_at (j := idx% «link_terminal__L19») rfl)
    (by decide +kernel) rfl link_terminal_L19_body lt_L19_ok
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lt_L20_ok : ltOk ((Chunks.new 20).getD default) 7607 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem link_terminal_L20_completeA (k : ℕ) :
    LinkTerminalCompleteAE fs al cert k 20 "link_terminal__L20" (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) :=
  lt_placed (by decide +kernel) chunkOk_20 (coreProgram_find?_at (j := idx% «link_terminal__L20») rfl)
    (by decide +kernel) rfl link_terminal_L20_body lt_L20_ok
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lt_L21_ok : ltOk ((Chunks.new 21).getD default) 32671816220672 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem link_terminal_L21_completeA (k : ℕ) :
    LinkTerminalCompleteAE fs al cert k 21 "link_terminal__L21" (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) :=
  lt_placed (by decide +kernel) chunkOk_21 (coreProgram_find?_at (j := idx% «link_terminal__L21») rfl)
    (by decide +kernel) rfl link_terminal_L21_body lt_L21_ok
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lt_L22_ok : ltOk ((Chunks.new 22).getD default) 32671816220672 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem link_terminal_L22_completeA (k : ℕ) :
    LinkTerminalCompleteAE fs al cert k 22 "link_terminal__L22" (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) :=
  lt_placed (by decide +kernel) chunkOk_22 (coreProgram_find?_at (j := idx% «link_terminal__L22») rfl)
    (by decide +kernel) rfl link_terminal_L22_body lt_L22_ok
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lt_L23_ok : ltOk ((Chunks.new 23).getD default) 69649 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem link_terminal_L23_completeA (k : ℕ) :
    LinkTerminalCompleteAE fs al cert k 23 "link_terminal__L23" (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) :=
  lt_placed (by decide +kernel) chunkOk_23 (coreProgram_find?_at (j := idx% «link_terminal__L23») rfl)
    (by decide +kernel) rfl link_terminal_L23_body lt_L23_ok
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem lt_L24_ok : ltOk ((Chunks.new 24).getD default) 299140177199104 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem link_terminal_L24_completeA (k : ℕ) :
    LinkTerminalCompleteAE fs al cert k 24 "link_terminal__L24" (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) :=
  lt_placed (by decide +kernel) chunkOk_24 (coreProgram_find?_at (j := idx% «link_terminal__L24») rfl)
    (by decide +kernel) rfl link_terminal_L24_body lt_L24_ok
    (by decide +kernel)

/-- **Every `link_terminal__L{w}` completes placed**, `19 ≤ w ≤ 24`, its end within `2^21` of its cursor
when every frame is below `2^16`. -/
theorem link_terminal_completeA (k : ℕ) :
    ∀ w, 19 ≤ w → w ≤ 24 → LinkTerminalCompleteAE fs al cert k w (ltNames.getD (w - 19) "")
      (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) := by
  intro w h1 h2
  interval_cases w
  exacts [link_terminal_L19_completeA k, link_terminal_L20_completeA k, link_terminal_L21_completeA k,
    link_terminal_L22_completeA k, link_terminal_L23_completeA k, link_terminal_L24_completeA k]

end
end LeanVM.Guest.B1.VsC
