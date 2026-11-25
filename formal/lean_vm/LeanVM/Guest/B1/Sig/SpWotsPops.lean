/-
  LeanVM.Guest.B1.Sig.SpWotsPops

  The witness-stream entries `sp_wots` (`lean_ethereum.py:4072-4102`) pops on its completing valuation: each digit group's word (`"digits"`), then the starts of the chains its arm walks (`"chain_starts"`).
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsCompleteStmt
public import LeanVM.Guest.B1.Sig.BlockPops
public import LeanVM.Guest.B1.Sig.PopsKit
import LeanVM.Guest.B1.Sig.SpWotsLinksAll
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«sp_wots»
import LeanVM.Guest.StmtsAppend

/-!
# `sp_wots`'s pops

* `stackHints`, `fallPops_stackHints`: a block of atoms pops what its witness hints write into frame cells, read off the block;
* the body's pieces (`spP`, `SpWotsLinks`), checked by the kernel: group `p`'s digit word hinted at `spSel p`, then its `match` on it, arm `k` hinting its chains' starts where the decoder reads them; the last piece hints nothing and returns;
* `sp_wots_complete_cells_pops`, `sp_wots_complete_pops`: `sp_wots` completes on a valuation whose path pops `spWotsPops digest values`: the honest valuation of its reference function (`spWotsRef_honest`) carried to the body (`sp_wots_bwd`) holds each group's word and its arm's starts where those pieces hint them.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory LeanVM.Guest.Ref LeanVM.Guest.Fast

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## Blocks of atoms -/

/-- What an atom's witness hint writes into frame cells: its stream and cells; `none` for a witness
hint into memory. -/
def atomStackHints : Atom → Option (List (String × List V))
  | .hint (.witness s (.stack vs)) => some [(s, vs)]
  | .hint (.witness _ (.heap ..)) => none
  | _ => some []

/-- What a block of atoms' witness hints write into frame cells, in order; `none` at a statement
that is no atom or a witness hint into memory. -/
def stackHints : List Stmt → Option (List (String × List V))
  | [] => some []
  | s :: ss => match s with
    | .atom a => (atomStackHints a).bind fun x => (stackHints ss).map (x ++ ·)
    | _ => none

theorem atomStackHints_pops (σ : Val) {a : Atom} {hs : List (String × List V)}
    (h : atomStackHints a = some hs) : a.pops rd σ = hs.map fun x => (x.1, x.2.map σ) := by
  rcases a with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | (⟨s, _ | _⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _) | _ <;>
    cases h <;> rfl

/-- **A block of atoms pops what its witness hints write into frame cells.** -/
theorem fallPops_stackHints (σ : Val) : ∀ {ss : List Stmt} {hs : List (String × List V)},
    stackHints ss = some hs → FallPops rd σ ss (hs.map fun x => (x.1, x.2.map σ))
  | [], _, h => by cases h; exact FallPops.nil
  | .atom a :: ss, _, h => by
      simp only [stackHints, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      rw [List.map_append, ← atomStackHints_pops σ hx]
      exact (fallPops_stackHints σ hy).cons_atom
  | .ite .. :: _, _, h | .match_ .. :: _, _, h | .call .. :: _, _, h | .callIf .. :: _, _, h
  | .dispatch .. :: _, _, h | .ret _ :: _, _, h => by simp [stackHints] at h

/-! ## The body's pieces -/

/-- The starts arm `k` of group `p` hints, where the decoder reads them. -/
private def spStartHints (p k : Nat) : List (String × List V) :=
  (List.range (spN p)).map fun r => ("chain_starts", [V.n (spSel.getD p 0 + offAt (spTabOf p) r k)])

/-- Piece `p < 22`: atoms hinting group `p`'s digit word at `spSel p`, then the `match` on it, of
`4 ^ spN p` arms, arm `k` atoms hinting `spStartHints p k`. -/
private def spGroupShape (p : Nat) (ss : List Stmt) : Bool :=
  match ss.getLast? with
  | some (.match_ x arms) => x == V.n (spSel.getD p 0) && arms.length == 4 ^ spN p &&
      stackHints ss.dropLast == some [("digits", [V.n (spSel.getD p 0)])] &&
      (List.range arms.length).all fun k => stackHints (arms.getD k []) == some (spStartHints p k)
  | _ => false

/-- The last piece: atoms hinting nothing, then the return. -/
private def spLastShape (ss : List Stmt) : Bool :=
  match ss.getLast? with
  | some (.ret _) => stackHints ss.dropLast == some []
  | _ => false

private theorem sp_shapes :
    (((List.range 22).all fun p => spGroupShape p (spP p)) && spLastShape (spP 22)) = true := by
  decide +kernel

/-! ## The pops -/

/-- Group `q`'s entries: its digit word, then its chains' starts. -/
def spGroupPops (d : Nat → Nat) (vals : Nat → E) (q : Nat) : List Pop :=
  ("digits", [ofK (addressOfIndex (spK d q))]) :: (List.range (spN q)).map fun t => startPop (vals (3 * q + t))

/-- The body's entries: its 22 groups'. -/
def spPopsT (d : Nat → Nat) (vals : Nat → E) : List Pop := (List.range 22).flatMap (spGroupPops d vals)

/-- **Group `p`'s piece pops its entries** on a valuation holding its digit word and its arm's starts
where it hints them. -/
private theorem spGroup_pops {d : Nat → Nat} {vals : Nat → E} {σ : Val} {p : Nat} (hp : p < 22)
    (hx : σ (.n (spSel.getD p 0)) = ofK (addressOfIndex (spK d p)))
    (hs : ∀ r < spN p, σ (.n (spSel.getD p 0 + offAt (spTabOf p) r (spK d p))) = vals (3 * p + r)) :
    FallPops rd σ (spP p) (spGroupPops d vals p) := by
  have h : spGroupShape p (spP p) = true := by
    have := sp_shapes
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at this
    exact this.1 p hp
  unfold spGroupShape at h
  split at h
  · rename_i x arms hl
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨rfl, hn⟩, hpre⟩, harms⟩ := h
    have hk : spK d p < arms.length := hn ▸ spK_lt d p
    have ha := fallPops_stackHints (rd := rd) σ (harms _ hk)
    rw [List.getD_eq_getElem _ _ hk] at ha
    have h64 : spK d p < 2 ^ 64 - 1 := by
      have : 4 ^ spN p ≤ 64 := by unfold spN; split <;> norm_num
      have := spK_lt d p
      omega
    rw [← List.dropLast_append_getLast? _ hl]
    refine FallPops.congr_pops ((fallPops_stackHints σ hpre).append (FallPops.match_ hk h64 hx ha)) ?_
    simp only [spGroupPops, spStartHints, List.map_cons, List.map_nil, List.map_map, hx,
      List.singleton_append, Function.comp_def]
    exact congrArg _ (List.map_congr_left fun r hr => by rw [hs r (List.mem_range.mp hr)])
  · cases h

private theorem fallPops_range {σ : Val} (P : Nat → List Stmt) (f : Nat → List Pop) :
    ∀ n, (∀ i < n, FallPops rd σ (P i) (f i)) →
      FallPops rd σ ((List.range n).map P).flatten ((List.range n).flatMap f)
  | 0, _ => FallPops.nil
  | n + 1, h => by
      rw [List.range_succ, List.map_append, List.flatten_append, List.flatMap_append]
      simpa using (fallPops_range P f n fun i hi => h i (by omega)).append (h n (by omega))

/-- **The body returns popping its groups' entries** on a valuation holding each group's digit word
and its arm's starts where it hints them. -/
private theorem sp_body_pops {d : Nat → Nat} {vals : Nat → E} {σ : Val}
    (hx : ∀ p < 22, σ (.n (spSel.getD p 0)) = ofK (addressOfIndex (spK d p)))
    (hs : ∀ p < 22, ∀ r < spN p,
      σ (.n (spSel.getD p 0 + offAt (spTabOf p) r (spK d p))) = vals (3 * p + r)) :
    ∃ es vs, walk σ (Fn.«sp_wots».core).body = .ret es vs ∧ calls es = [] ∧
      evPops rd σ es = spPopsT d vals := by
  have h : spLastShape (spP 22) = true := ((Bool.and_eq_true _ _).mp sp_shapes).2
  unfold spLastShape at h
  split at h
  · rename_i vs hl
    have hcut : cutAt spCuts Fn.«sp_wots».core.body = (List.range 23).map spP :=
      List.ext_getElem (by simp [length_cutAt, spCuts]) fun i h1 _ => by
        rw [List.getElem_map, List.getElem_range, spP, List.getD_eq_getElem _ _ h1]
    have hb : Fn.«sp_wots».core.body =
        (((List.range 22).map spP).flatten ++ (spP 22).dropLast) ⧺ [.ret vs] := by
      rw [List.append_assoc, List.dropLast_append_getLast? _ hl,
        ← flatten_cutAt spCuts Fn.«sp_wots».core.body, hcut,
        show List.range 23 = List.range 22 ++ [22] from List.range_succ, List.map_append,
        List.flatten_append]
      simp
    obtain ⟨es, hw, hc, hp⟩ := retPops_of_fallPops (vs := vs)
      ((fallPops_range spP _ 22 fun p hp => spGroup_pops (rd := rd) hp (hx p hp) (hs p hp)).append
        (fallPops_stackHints σ (beq_iff_eq.mp h)))
    exact ⟨es, vs, (congrArg (walk σ) hb).trans hw, hc, by simpa [spPopsT] using hp⟩
  · cases h

/-! ## Complete, popping -/

/-- **`sp_wots` is complete, popping its groups' entries**: `sp_wots_complete_cells`, and on the completing valuation its path returns setting up no call and popping `spPopsT d vals`. -/
theorem sp_wots_complete_cells_pops {pp a0 a1 : E} {d : Nat → Nat} (hd : ∀ i, d i < 4)
    (hsum : ∑ i ∈ Finset.range 64, d i = 128) {vals : Nat → E} (hm : MemOK rd 64) :
    ∃ σ : Val, σ (.n (val% «sp_wots» "pp")) = pp ∧ σ (.n (val% «sp_wots» "a0")) = a0 ∧ σ (.n (val% «sp_wots» "a1")) = a1 ∧ σ (.n (val% «sp_wots» "encoding")) = eOfNat128 (spX d 64) ∧
      Stmt.HoldsList C rd σ (Fn.«sp_wots».core).body False (fun rs => rs = [spLeafCell pp a0 a1 d vals]) ∧
      ∃ es vs, walk σ (Fn.«sp_wots».core).body = .ret es vs ∧ calls es = [] ∧ evPops rd σ es = spPopsT d vals := by
  obtain ⟨ρ, hp, hsat, hr, hg, hst⟩ := spWotsRef_honest (rd := rd) (pp := pp) (a0 := a0) (a1 := a1)
    vals hsum fun p hp => spK_ok hd hm hp
  obtain ⟨σ, hpar, hpos, hb⟩ := sp_wots_bwd (C := C) hsat
  have hpar' : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3)] = [pp, a0, a1, eOfNat128 (spX d 64)] :=
    hpar.trans hp
  simp only [List.cons.injEq, and_true] at hpar'
  refine ⟨σ, hpar'.1, hpar'.2.1, hpar'.2.2.1, hpar'.2.2.2, hr ▸ hb, sp_body_pops (fun q hq => ?_)
    fun q hq t ht => ?_⟩
  · exact (hpos _ (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, List.mem_cons_self ..⟩)).trans
      (hg q hq)
  · have h3 : t < 3 := by unfold spN at ht; split at ht <;> omega
    rw [hpos _ (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, List.mem_cons_of_mem _
      (List.mem_flatMap.mpr ⟨_, List.mem_range.mpr (spK_lt d q), List.mem_map.mpr ⟨t,
        List.mem_range.mpr ht, rfl⟩⟩)⟩), ← hst _ (by unfold spN at ht; split at ht <;> omega),
      show (3 * q + t) / 3 = q by omega]

/-! ## Against the statement -/

/-- **`sp_wots`'s entries** for a digest and chain values: each group's word of the digest's `base_2b` digits, then its chains' values. -/
def spWotsPops (digest : HashSig.Digest) (values : Sphincs.ChainIndex → HashSig.Digest) : List Pop :=
  spPopsT (spDigitsOf digest) (spValsOf values)

/-- **`sp_wots` is complete, popping its entries**: `sp_wots_complete_Spec`, and on the completing valuation its path returns setting up no call and popping `spWotsPops digest values`. -/
theorem sp_wots_complete_pops (C : CallRel) (rd : Reader) (publicSeed : HashSig.PublicParameter)
    (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) (leaf : Sphincs.TreeLeafIndex) (digest : HashSig.Digest)
    (values : Sphincs.ChainIndex → HashSig.Digest) (hm : MemOK rd 64)
    (hT : Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits digest)) :
    ∃ σ : Val, σ (.n (val% «sp_wots» "pp")) = cellOf128 publicSeed ∧
      (σ (.n (val% «sp_wots» "a0")), σ (.n (val% «sp_wots» "a1"))) = keyAdrsCells layer.val tree.val leaf.val ∧
      σ (.n (val% «sp_wots» "encoding")) = cellOf128 digest ∧
      Stmt.HoldsList C rd σ (Fn.«sp_wots».core).body False
        (fun rs => rs = [cellOf128 (wotsLeafOf publicSeed layer tree leaf digest values)]) ∧
      ∃ es vs, walk σ (Fn.«sp_wots».core).body = .ret es vs ∧ calls es = [] ∧
        evPops rd σ es = spWotsPops digest values := by
  have hpk : keyAdrsCells layer.val tree.val leaf.val =
      (adrsCell0 layer.val tree.val, adrsCell1 0 leaf.val 0 0) := rfl
  obtain ⟨σ, h0, h1, h2, h3, hh, hp⟩ := sp_wots_complete_cells_pops (C := C) (rd := rd)
    (pp := cellOf128 publicSeed) (a0 := adrsCell0 layer.val tree.val) (a1 := adrsCell1 0 leaf.val 0 0)
    (vals := spValsOf values) (spDigitsOf_lt digest) (spDigitsOf_sum hT) hm
  refine ⟨σ, h0, by rw [hpk, h1, h2], by rw [h3, spX_digest]; exact (cellOf128_eq_eOfNat128' digest).symm,
    by rw [← spLeafCell_digest]; exact hh, hp⟩

end
end LeanVM.Guest.B1.Sig
