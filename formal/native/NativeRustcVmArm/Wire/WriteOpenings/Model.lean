module

public import NativeRustcVmArm.Wire.WriteOpenings.Basic
public import NativeRustcVm.Wire.ReaderFacts

/-!
# `write_openings`' memory words in the model's terms

Given the postcondition's lists (`Hyp`: the queries, the positions, the leaves, the siblings in
the entry's memory), what the function reads is the model's: the first position of query `j`
(`pos_qw`), the leaf's words (`lfw_eq`), the level's digest (`digest_eq`). Hence the openings
written are the phase of `openingAt` (`phaseAt_of`), and nothing is `Bad` (`Hyp.not_bad`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVm.Transcript (PhaseAt OpeningAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile NativeVm.Model

@[expose] public section

/-- **The postcondition's hypotheses** on the entry's memory. -/
structure Hyp (R : Run) (qs ps : List Nat) (leaves : List (List K))
    (sibs : List (List (Nat × Digest))) : Prop where
  qlen : qs.length = R.nq
  qin : ∀ q ∈ qs, q < 2 ^ 32 ∧ q ∈ ps
  qws : WordsAt R.d0 R.qa (qs.map Nat.toUInt64)
  plen : ps.length = R.np
  plt : ∀ p ∈ ps, p < 2 ^ 64
  pws : WordsAt R.d0 R.pa (ps.map Nat.toUInt64)
  llen : leaves.length = ps.length
  lwid : ∀ x ∈ leaves, x.length = R.lw
  lvs : LeavesAt R.d0 R.lv leaves
  slen : sibs.length = R.h
  sws : SibsAt R.d0 R.sb R.cnt sibs

end

public section

/-! ## Lists -/

theorem lookup_eq_findIdx {α β : Type} [BEq α] (l : List (α × β)) (k : α) :
    l.lookup k = (l.findIdx? fun p ↦ k == p.1).bind fun i ↦ (l[i]?).map Prod.snd := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    rw [List.lookup_cons, List.findIdx?_cons]
    by_cases h : (k == a) = true
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, ih, Option.bind_map]
      rfl

theorem lookup_zip {α β : Type} [BEq α] (ks : List α) (vs : List β) (h : vs.length = ks.length)
    (k : α) : (ks.zip vs).lookup k = (ks.findIdx? fun a ↦ k == a).bind fun i ↦ vs[i]? := by
  induction ks generalizing vs with
  | nil => rfl
  | cons a ks ih =>
    cases vs with
    | nil => simp at h
    | cons v vs =>
      simp only [List.zip_cons_cons, List.lookup_cons, List.findIdx?_cons]
      by_cases hk : (k == a) = true
      · simp [hk]
      · simp only [hk, Bool.false_eq_true, ↓reduceIte, ih vs (by simpa using h), Option.bind_map]
        rfl

theorem toUInt64_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (a.toUInt64 == b.toUInt64) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne]
    intro he
    apply h
    have := congrArg UInt64.toNat he
    rwa [toNat_toUInt64_of_lt ha, toNat_toUInt64_of_lt hb] at this

theorem findIdx?_congr_mem {α : Type} {p p' : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = p' a) → l.findIdx? p = l.findIdx? p'
  | [], _ => rfl
  | a :: l, h => by
    rw [List.findIdx?_cons, List.findIdx?_cons, h a List.mem_cons_self,
      findIdx?_congr_mem fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]

end

namespace Hyp

variable {R : Run} {qs ps : List Nat} {leaves : List (List K)} {sibs : List (List (Nat × Digest))}

public section

theorem qw_eq (H : Hyp R qs ps leaves sibs) {j : Nat} (hj : j < R.nq) :
    R.qw j = (qs[j]'(by rw [H.qlen]; exact hj)).toUInt64 := by
  have := H.qws.getElem (i := j) (by simp [H.qlen]; exact hj)
  rw [List.getElem_map] at this
  exact NativeRustcVm.wordOf_of_wordAt this

theorem pw_eq (H : Hyp R qs ps leaves sibs) {i : Nat} (hi : i < R.np) :
    R.pw i = (ps[i]'(by rw [H.plen]; exact hi)).toUInt64 := by
  have := H.pws.getElem (i := i) (by simp [H.plen]; exact hi)
  rw [List.getElem_map] at this
  exact NativeRustcVm.wordOf_of_wordAt this

theorem pws_eq (H : Hyp R qs ps leaves sibs) :
    (List.range R.np).map R.pw = ps.map Nat.toUInt64 := by
  apply List.ext_getElem (by simp [H.plen])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact H.pw_eq (by simpa using h1)

/-- The first position of a word below `2 ^ 64`. -/
theorem pos_eq (H : Hyp R qs ps leaves sibs) {q : Nat} (hq : q < 2 ^ 64) :
    R.pos q.toUInt64 = ps.findIdx? fun a ↦ q == a := by
  unfold Run.pos
  rw [H.pws_eq, List.findIdx?_map]
  refine findIdx?_congr_mem fun a ha ↦ ?_
  simp only [Function.comp_apply]
  rw [toUInt64_beq (H.plt a ha) hq, Bool.beq_comm]

theorem qs_lt (H : Hyp R qs ps leaves sibs) {j : Nat} (hj : j < qs.length) : qs[j] < 2 ^ 32 :=
  (H.qin _ (List.getElem_mem hj)).1

/-- Query `j`'s first position: some `i`, where the leaves hold its leaf. -/
theorem pos_qw (H : Hyp R qs ps leaves sibs) {j : Nat} (hj : j < R.nq) :
    ∃ i, ∃ hi : i < R.np, R.pos (R.qw j) = some i ∧
      (ps.zip leaves).lookup (qs[j]'(by rw [H.qlen]; exact hj)) = some (leaves[i]'(by
        rw [H.llen, H.plen]; exact hi)) := by
  have hjl : j < qs.length := by rw [H.qlen]; exact hj
  have hq := H.qs_lt hjl
  rw [H.qw_eq hj, H.pos_eq (by omega)]
  have hin := (H.qin _ (List.getElem_mem hjl)).2
  cases hf : ps.findIdx? (fun a ↦ qs[j] == a) with
  | none =>
    rw [List.findIdx?_eq_none_iff] at hf
    have := hf _ hin
    simp at this
  | some i =>
    have hi := (List.findIdx?_eq_some_iff_getElem.mp hf).1
    refine ⟨i, by rw [← H.plen]; exact hi, rfl, ?_⟩
    rw [lookup_zip ps leaves H.llen, hf, Option.bind_some,
      List.getElem?_eq_getElem (by rw [H.llen]; exact hi)]

/-- Word `t` of leaf `i`. -/
theorem lfw_eq (H : Hyp R qs ps leaves sibs) {i : Nat} (hi : i < R.np) :
    (List.range R.lw).map (R.lfw i) =
      (leaves[i]'(by rw [H.llen, H.plen]; exact hi)).map K.lane := by
  have hil : i < leaves.length := by rw [H.llen, H.plen]; exact hi
  have hw := H.lwid _ (List.getElem_mem hil)
  apply List.ext_getElem (by simp [hw])
  intro t h1 h2
  simp only [List.length_map, List.length_range] at h1
  have := (H.lvs i hil).getElem (i := t) (by simp [hw, h1])
  rw [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add, List.getElem_map] at this
  simp only [List.getElem_map, List.getElem_range]
  exact NativeRustcVm.wordOf_of_wordAt this

theorem cw_eq (H : Hyp R qs ps leaves sibs) {l : Nat} (hl : l < R.h) :
    (R.cw l).toNat = (sibs[l]'(by rw [H.slen]; exact hl)).length ∧
      (sibs[l]'(by rw [H.slen]; exact hl)).length ≤ 256 := by
  have hll : l < sibs.length := by rw [H.slen]; exact hl
  obtain ⟨hle, hw, -⟩ := H.sws l hll
  refine ⟨?_, hle⟩
  unfold Run.cw
  rw [NativeRustcVm.wordOf_of_wordAt hw, toNat_toUInt64_of_lt (by omega)]

/-- **Nothing bad**: every query has a position, every level at most `256` siblings. -/
theorem not_bad (H : Hyp R qs ps leaves sibs) : ¬R.Bad := by
  rintro (⟨j, hj, hn⟩ | ⟨l, hl, hc⟩)
  · obtain ⟨i, -, hi, -⟩ := H.pos_qw hj
    rw [hi] at hn
    cases hn
  · have := H.cw_eq hl
    omega

theorem skey_eq {q : Nat} (hq : q < 2 ^ 64) (l : Nat) : skey q.toUInt64 l = (q >>> l).toUInt64 := by
  apply UInt64.toNat_inj.mp
  unfold skey
  rw [UInt64.toNat_ofBitVec, BitVec.toNat_ushiftRight, UInt64.toNat_toBitVec,
    toNat_toUInt64_of_lt hq, toNat_toUInt64_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) hq)]

theorem default_digest : (default : Digest).toList = [0, 0, 0, 0] := rfl

/-- **Level `l`'s digest** for query `q`: the model's lookup, zeros where none. -/
theorem digest_eq (H : Hyp R qs ps leaves sibs) {l : Nat} (hl : l < R.h) {q : Nat}
    (hq : q < 2 ^ 64) :
    R.digest l q.toUInt64 =
      ((((sibs.getD l []).lookup (q >>> l)).getD default) : Digest).toList := by
  have hll : l < sibs.length := by rw [H.slen]; exact hl
  obtain ⟨hc, hle⟩ := H.cw_eq hl
  obtain ⟨-, -, hns⟩ := H.sws l hll
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hll, Option.getD_some]
  set ns := sibs[l]
  have hkey : ∀ n (hn : n < ns.length), wordOf R.d0 (R.na l n) = ns[n].1.toUInt64 := by
    intro n hn
    have := (hns n hn).2.1
    rw [NativeRustcVm.Transcript.off, NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add,
      show nodesBytes = 10240 from rfl] at this
    exact NativeRustcVm.wordOf_of_wordAt this
  have hks : R.keys l = ns.map fun p ↦ p.1.toUInt64 := by
    apply List.ext_getElem (by simp [Run.keys, hc])
    intro n h1 h2
    simp only [Run.keys, List.getElem_map, List.getElem_range]
    exact hkey n (by simpa [Run.keys, hc] using h1)
  have hsh : q >>> l < 2 ^ 64 := lt_of_le_of_lt (Nat.shiftRight_le _ _) hq
  have hk64 : ∀ p ∈ ns, p.1 < 2 ^ 64 := fun p hp ↦ by
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hp
    exact (hns n hn).1
  have hf : (R.keys l).findIdx? (· == skey q.toUInt64 l) = ns.findIdx? fun p ↦ q >>> l == p.1 := by
    rw [hks, List.findIdx?_map, skey_eq hq]
    refine findIdx?_congr_mem fun p hp ↦ ?_
    simp only [Function.comp_apply]
    rw [toUInt64_beq (hk64 p hp) hsh, Bool.beq_comm]
  unfold Run.digest
  rw [hf, lookup_eq_findIdx]
  cases hfi : ns.findIdx? fun p ↦ q >>> l == p.1 with
  | none => rfl
  | some n =>
    have hn := (List.findIdx?_eq_some_iff_getElem.mp hfi).1
    simp only [Option.bind_some, List.getElem?_eq_getElem hn, Option.map_some, Option.getD_some]
    have hd := (hns n hn).2.2
    apply List.ext_getElem (by simp)
    intro u h1 h2
    simp only [List.length_map, List.length_range] at h1
    have := hd.getElem (i := u) (by simpa using h1)
    rw [NativeRustcVm.Transcript.off, NativeRustcVm.Transcript.off, NativeRustcVm.Transcript.off,
      NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add,
      show nodesBytes = 10240 from rfl] at this
    simp only [List.getElem_map, List.getElem_range]
    rw [Run.na, NativeRustcVm.addr_add_add]
    rw [NativeRustcVm.addr_add_add, ← Nat.add_assoc] at this
    exact NativeRustcVm.wordOf_of_wordAt this

/-- **The phase written**: the head and every opening, as the model's phase. -/
theorem phaseAt_of (G : Geo R) (H : Hyp R qs ps leaves sibs) {d : Mem 64} (hd : R.Done d R.nq) :
    PhaseAt d R.out (phaseW ⟨R.h, R.lw, qs.map (openingAt ps leaves sibs R.h)⟩) := by
  obtain ⟨⟨h0, h8, h16⟩, hop⟩ := hd
  have hsz : (phaseW ⟨R.h, R.lw, qs.map (openingAt ps leaves sibs R.h)⟩).size = R.nq := by
    simp [phaseW, H.qlen]
  refine ⟨R.h, R.lw, G.h32, G.lw64, by rw [hsz]; exact G.nq256, ?_, h8, h16, fun j hj ↦ ?_⟩
  · rw [hsz]; simpa using h0
  rw [hsz] at hj
  have hjl : j < qs.length := by rw [H.qlen]; exact hj
  obtain ⟨i, hi, hpos, hlk⟩ := H.pos_qw hj
  obtain ⟨i', hpos', hq, hleaf, hpath⟩ := hop j hj
  rw [hpos] at hpos'
  cases hpos'
  have hq32 := H.qs_lt hjl
  have hil : i < leaves.length := by rw [H.llen, H.plen]; exact hi
  have hw := H.lwid _ (List.getElem_mem hil)
  simp only [phaseW, List.getElem_toArray, List.getElem_map, openingW, openingAt, hlk,
    Option.getD_some]
  have e : NativeRustcVm.Transcript.off R.out (8 * (3 + j * NativeVm.openingWords)) =
      R.oa (ob j) := by
    simp only [NativeRustcVm.Transcript.off, NativeVm.openingWords, wireMaxLeafWords,
      wireMaxHeight, ob]
    congr 2
    omega
  rw [e]
  refine ⟨by simp [hw], by simp, ?_, ?_, ?_, ?_⟩
  · rw [toNat_toUInt64_of_lt (by omega)]; exact hq32
  · rw [← H.qw_eq hj]; exact hq
  · rw [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add, List.toList_toArray,
      ← H.lfw_eq hi]
    exact hleaf
  · rw [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add,
      show ob j + 8 * (1 + wireMaxLeafWords) = ob j + 520 from rfl, List.toList_toArray,
      List.flatMap_map]
    unfold Run.PathPart at hpath
    rw [H.qw_eq hj] at hpath
    convert hpath using 1
    refine List.flatMap_congr fun l hl ↦ ?_
    rw [List.mem_range] at hl
    exact (H.digest_eq hl (by omega)).symm

end

end Hyp

end NativeRustcVmArm.Wire.WriteOpenings
