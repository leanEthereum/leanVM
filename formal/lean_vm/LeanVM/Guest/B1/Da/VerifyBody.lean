/-
  LeanVM.Guest.B1.Da.VerifyBody

  `da_verify`'s body (G:2888-2956): its template, and what its relation says of memory
  (`DaFacts`), each loop and call in Spec terms.
-/

module

public import LeanVM.Guest.B1.Da.RowHash
public import LeanVM.Guest.B1.Da.RowShape
import LeanVM.Guest.B1.Sig.Decide

/-!
# `da_verify`'s body

`da_verify(g_squares)` hints the row count `r` and `g^⌈log₂ r⌉`, checks them (`da_row_shape`),
lays out `prefix_bases` (`__loop88`), the vector hash's states at `hashes` (from the IV), the
`385` counter words as a frame run at `counters`, the row sums' chains (`__loop89`), runs the
`128` columns (`__loop90`, `__loop91`), checks every row sum's end (`__loop92`), hashes the
column tree (`da_levels__L128_L7`), the rows' digests (`__loop93`) and the padding rows
(`__loop94`) into the row tree (`da_levels` at the dispatched depth), and returns the hash of
the two roots and the vector hash's final state. `DaFacts` lists these on memory, the hinted
pointers quantified; `da_verify_facts` derives it.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## The template -/

/-- Up to the vector hash's IV. -/
def dvA : List Stmt :=
  [.atom (.hint (.witness "da_shape" (.stack [.n 1, .n 2]))),
   .call "da_row_shape" [.n 1, .n 2, .n 0] [.n 3, .n 4],
   .atom (.mul (.n 5) (.n 3) (.n 3)), .atom (.mul (.n 6) (.n 5) (.n 5)), .atom (.mul (.n 7) (.n 6) (.n 6)),
   .atom (.mul (.n 8) (.n 7) (.n 7)), .atom (.mul (.n 9) (.n 8) (.n 8)), .atom (.mul (.n 10) (.n 9) (.n 9)),
   .atom (.mul (.n 11) (.n 10) (.n 10)), .atom (.hint (.allocDyn (.n 12) (.n 11))),
   .atom (.hint (.allocDyn (.n 13) (.n 1))), .atom (.const (.n 14) (word 1 0 0)),
   .atom (.add (.n 15) (.n 14) (.n 1)), .atom (.const (.n 16) (word 1 0 0)),
   .callIf (.n 15) "__loop88" [.n 16, .n 1, .n 13, .n 12],
   .atom (.hint (.alloc (.n 17) 258)),
   .atom (.const (.n 18) (word 13503953895743350343 11912009169889063794 0)), .atom (.load (.n 18) (.n 17) 0),
   .atom (.const (.n 19) (word 11170449402626986623 6620516960021240235 0)), .atom (.load (.n 19) (.n 17) 1)]

/-- The counter words. -/
def dvK : List Atom := (List.range 385).map fun w => .const (.n (20 + w)) (word (w * 2048) 0 0)

/-- From the counters' address on. -/
def dvB : List Stmt :=
  [.atom (.frameAddr (.n 405) ((List.range 385).map fun w => .n (20 + w))),
   .atom (.mul (.n 406) (.n 1) (.n 1)), .atom (.mul (.n 407) (.n 406) (.n 406)),
   .atom (.mul (.n 408) (.n 407) (.n 407)), .atom (.mul (.n 409) (.n 408) (.n 408)),
   .atom (.mul (.n 410) (.n 409) (.n 409)), .atom (.mul (.n 411) (.n 410) (.n 410)),
   .atom (.mul (.n 412) (.n 411) (.n 411)), .atom (.mul (.n 413) (.n 412) (.n 1)),
   .atom (.hint (.allocDyn (.n 414) (.n 413))), .atom (.hint (.allocDyn (.n 415) (.n 1))),
   .atom (.const (.n 416) (word 1 0 0)), .atom (.add (.n 417) (.n 416) (.n 1)),
   .atom (.const (.n 418) (word 1 0 0)), .callIf (.n 417) "__loop89" [.n 418, .n 1, .n 414, .n 415],
   .atom (.hint (.alloc (.n 419) 512)), .atom (.const (.n 420) (word 1 0 0)),
   .call "__loop90" [.n 420, .n 1, .n 3, .n 4, .n 2, .n 13, .n 419, .n 415, .n 17, .n 405] [],
   .atom (.const (.n 421) (word 27 0 0)),
   .call "__loop91" [.n 421, .n 1, .n 3, .n 4, .n 2, .n 13, .n 419, .n 415, .n 17, .n 405] [],
   .atom (.const (.n 422) (word 1 0 0)), .atom (.add (.n 423) (.n 422) (.n 1)),
   .atom (.const (.n 424) (word 1 0 0)), .callIf (.n 423) "__loop92" [.n 424, .n 1, .n 415],
   .call "da_levels__L128_L7" [.n 419] [.n 425, .n 426],
   .atom (.mul (.n 427) (.n 3) (.n 3)), .atom (.mul (.n 428) (.n 427) (.n 427)),
   .atom (.hint (.allocDyn (.n 429) (.n 428))),
   .atom (.const (.n 430) (word 1 0 0)), .atom (.add (.n 431) (.n 430) (.n 1)),
   .atom (.const (.n 432) (word 1 0 0)), .callIf (.n 431) "__loop93" [.n 432, .n 1, .n 13, .n 429],
   .atom (.const (.n 433) (word 1 0 0)), .atom (.add (.n 434) (.n 433) (.n 4)),
   .atom (.const (.n 435) (word 1 0 0)), .callIf (.n 434) "__loop94" [.n 435, .n 4, .n 429, .n 1],
   .dispatch (.n 2) dlNames [.n 429] [.n 436, .n 437],
   .atom (.const (.n 438) (word 13503953895743350343 11912009169889063794 0)),
   .atom (.const (.n 439) (word 11170449402626986623 6620516960021240235 0)),
   .atom (.const (.n 440) (word 64 4294967295 0)),
   .atom (.blake2s (.n 436) (.n 437) (.n 425) (.n 426) (.n 438) (.n 439) (.n 441) (.n 442) (.n 440)),
   .atom (.copy (.n 443) (.n 441)), .atom (.copy (.n 444) (.n 442)),
   .atom (.load (.n 445) (.n 17) 256), .atom (.load (.n 446) (.n 17) 257),
   .ret [.n 443, .n 444, .n 445, .n 446]]

/-- `da_verify`'s body. -/
def dvBody : List Stmt := dvA ++ dvK.map .atom ++ dvB

open scoped LeanVM.Guest.B1.Sig.Dec in
theorem dv_eq : Data.core23.body = dvBody := by decide +kernel

theorem find_dv : coreProgram.find? "da_verify" = some ⟨"da_verify", [.n 0], dvBody⟩ := by
  rw [Program.find?_of_indexOf? (j := 23) (by decide +kernel) rfl, ← dv_eq]
  rfl

/-! ## What the body says -/

/-- **What `da_verify`'s relation says of memory**: `r` rows, `1 ≤ r ≤ 1024`, and, the hinted
pointers quantified, every loop's and call's meaning, with the vector hash's IV at `hashes` and
the counter words at `counters`. -/
def DaFacts (rd : Reader) (r0 r1 v0 v1 : E) : Prop :=
  ∃ (r : ℕ) (pb pd hs ctr acc rb ct rt rc0 rc1 rr0 rr1 : E),
    1 ≤ r ∧ r ≤ LeanDa.maxRows ∧
    (∀ i < r, L88Step rd pb pd (gen ^ i)) ∧
    LoadHolds rd hs 0 (digestScalars paramIv).1 ∧ LoadHolds rd hs 1 (digestScalars paramIv).2 ∧
    IsInK ctr ∧ (∀ k < 385, ∀ w, rd (ctr.limb 0 * Parameters.gpow k) = some w → w = word (k * 2048) 0 0) ∧
    (∀ i < r, L89Step rd acc rb (gen ^ i)) ∧
    (∀ b < 128, Meaning_da_verify_column (decide (b < 64)) rd
      [gen ^ b, gen ^ r, gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r, pb, ct, rb,
        hs, ctr] []) ∧
    (∀ i < r, L92Step rd rb (gen ^ i)) ∧
    Meaning_da_levels 7 rd [ct] [rc0, rc1] ∧
    (∀ i < r, L93Step rd pb rt (gen ^ i)) ∧
    (∀ d < LeanDa.nPad r - r, L94Step rd rt (gen ^ r) (gen ^ d)) ∧
    Meaning_da_levels (LeanDa.logPad r) rd [rt] [rr0, rr1] ∧
    CompressCells ![rr0, rr1, rc0, rc1] (digestScalars paramIv).1 (digestScalars paramIv).2 r0 r1
      (metadataCell 64 true) ∧
    LoadHolds rd hs 256 v0 ∧ LoadHolds rd hs 257 v1

theorem holdsList_atoms' {C : CallRel} {rd : Reader} {σ : Val} (as : List Atom) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (as.map .atom) next kret ↔ (∀ a ∈ as, a.Holds rd σ) ∧ next := by
  have := holdsList_atoms (C := C) (rd := rd) (σ := σ) as [] next kret
  rw [List.append_nil] at this
  rw [this]; rfl

/-- A loop over `g^0 .. g^(n-1)` from its `loop_iff` form: every iteration below `n`. -/
theorem loop_all {W : E} {n : ℕ} {B : ℕ → Prop} (hn : n < 2 ^ 33) (hW : W = gen ^ n)
    (h : ∃ m, 0 < m ∧ W = gen ^ m ∧ (∀ j, 0 < j → j < m → gen ^ j ≠ W) ∧ ∀ j, 0 ≤ j → j < m → B j) :
    ∀ j < n, B j := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · intro j hj; omega
  obtain ⟨m, -, hN, hfirst, hall⟩ := h
  subst hW
  have := loop_end_exact hn hpos hN hfirst
  subst this
  exact fun j hj => hall j (Nat.zero_le _) hj

/-- A `mul_range(1, g^n)` loop helper called at `1 + g^n ≠ 0`. -/
theorem callIf_loop {P : Prop} {n : ℕ} (hn : 0 < n) (hn' : n < 2 ^ 33) (h : 1 + gen ^ n ≠ 0 → P) : P :=
  h (one_add_ne_zero.mpr fun he => by
    have := (gen_pow_eq_one_iff (by omega)).mp he; omega)

theorem logPad_le {r : ℕ} (hr : r ≤ LeanDa.maxRows) : LeanDa.logPad r ≤ 10 :=
  Nat.clog_le_of_le_pow (by unfold LeanDa.maxRows at hr; norm_num; omega)

theorem nPad_le {r : ℕ} (hr : r ≤ LeanDa.maxRows) : LeanDa.nPad r ≤ 1024 := by
  unfold LeanDa.nPad
  calc 2 ^ LeanDa.logPad r ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (logPad_le hr)
    _ = 1024 := by norm_num

theorem da_verify_facts {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    {r0 r1 v0 v1 : E} (h : coreProgram.Rel rd "da_verify" [gsq] [r0, r1, v0, v1]) :
    DaFacts rd r0 r1 v0 v1 := by
  rw [rel_of_find find_dv] at h
  obtain ⟨σ, hp, hb⟩ := h
  rw [dvBody, holdsList_append, holdsList_append, holdsList_atoms'] at hb
  simp only [dvA, dvB, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    word_one, word_g64] at hb hp
  obtain ⟨hshape, m5, m6, m7, m8, m9, m10, m11, c14, a15, c16, hk15, h88, c18, l18, c19, l19, hK, ⟨hk405, hfr⟩,
    m406, m407, m408, m409, m410, m411, m412, m413, c416, a417, c418, hk417, h89, c420, h90, c421, h91, c422,
    a423, c424, hk423, h92, hlv7, m427, m428, c430, a431, c432, hk431, h93, c433, a434, c435, hk434, h94,
    hdl, c438, c439, c440, hfin, c443, c444, l445, l446, hret⟩ := hb
  simp only [List.cons.injEq, and_true] at hp hret
  subst hp
  obtain ⟨_, _, _, np, gap, he, hr, r, hr1, hr2, hnb, hglp, hnp, hgap⟩ := (da_row_shape_iff hm hT _ _ _).mp hshape
  simp only [List.cons.injEq, and_true] at he hr
  obtain ⟨e1, e2, -⟩ := he
  obtain ⟨e3, e4⟩ := hr
  rw [← e1] at hnb
  rw [← e2] at hglp
  rw [← e3] at hnp
  rw [← e4] at hgap
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hlp := logPad_le hr2
  have hN := nPad_le hr2
  -- the counter words
  have hK' : ∀ k < 385, σ (.n (20 + k)) = word (k * 2048) 0 0 := by
    intro k hk
    exact hK _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hret
  rw [hnb, hglp, hnp, hgap] at h90 h91
  rw [c420] at h90
  rw [c421, ← word_g64] at h91
  have h88' := callIf_loop hr1 hr33 (by rwa [a15, c14, hnb] at h88)
  have h89' := callIf_loop hr1 hr33 (by rwa [a417, c416, hnb] at h89)
  have h92' := callIf_loop hr1 hr33 (by rwa [a423, c422, hnb] at h92)
  have h93' := callIf_loop hr1 hr33 (by rwa [a431, c430, hnb] at h93)
  rw [c16, ← pow_zero gen] at h88'
  rw [c418, ← pow_zero gen] at h89'
  rw [c424, ← pow_zero gen] at h92'
  rw [c432, ← pow_zero gen] at h93'
  obtain ⟨k, hk, hk2, hlvk⟩ := dl_dispatch.mp hdl
  rw [hglp] at hk2
  have hkl : k = LeanDa.logPad r := gen_pow_inj' (by omega) (by omega) hk2.symm
  subst hkl
  rw [c438, c439, c440, iv0_word, iv1_word, md64_word] at hfin
  refine ⟨r, σ (.n 13), σ (.n 12), σ (.n 17), σ (.n 405), σ (.n 414), σ (.n 415), σ (.n 419), σ (.n 429),
    σ (.n 425), σ (.n 426), σ (.n 436), σ (.n 437), hr1, hr2,
    loop_all (B := fun j => L88Step rd (σ (.n 13)) (σ (.n 12)) (gen ^ j)) hr33 rfl
      ((l88_iff rd _ _ _ 0).mp h88'),
    by rw [← iv0_word, ← c18]; exact l18, by rw [← iv1_word, ← c19]; exact l19, hk405,
    fun k hk w hw => ?_,
    loop_all (B := fun j => L89Step rd (σ (.n 414)) (σ (.n 415)) (gen ^ j)) hr33 rfl
      ((l89_iff rd _ _ _ 0).mp h89'),
    fun b hb => ?_,
    loop_all (B := fun j => L92Step rd (σ (.n 415)) (gen ^ j)) hr33 rfl ((l92_iff rd _ _ 0).mp h92'),
    (da_levels_iff 7 (by norm_num) _ _).mp hlv7,
    loop_all (B := fun j => L93Step rd (σ (.n 13)) (σ (.n 429)) (gen ^ j)) hr33 rfl
      ((l93_iff rd _ _ _ 0).mp h93'),
    fun d hd => ?_, hlvk, by rw [c443, c444]; exact hfin, l445, l446⟩
  · have := hfr k (by simpa using hk) w hw
    simp only [List.getElem_map, List.getElem_range] at this
    rw [this, hK' k hk]
  · by_cases h64 : b < 64
    · rw [decide_eq_true h64]
      exact colLoop_prefix rfl h90 b h64
    · rw [decide_eq_false h64]
      exact colLoop_rest rfl h91 b (by omega) hb
  · have hpos : 0 < LeanDa.nPad r - r := by omega
    have h94' := callIf_loop hpos (by omega) (by rwa [a434, c433, hgap] at h94)
    rw [c435, hnb, ← pow_zero gen] at h94'
    exact loop_all (B := fun j => L94Step rd (σ (.n 429)) (gen ^ r) (gen ^ j)) (by omega) rfl
      ((l94_iff rd _ _ _ 0).mp h94') d hd

/-! ## The converse -/

/-- `x` squared `n` times. -/
def sqIter (x : E) : ℕ → E
  | 0 => x
  | n + 1 => sqIter x n * sqIter x n

/-- The honest values of `da_verify`. -/
def dvVals (gsq nb glp np gap pd pb hs ctr acc rb ct rt rc0 rc1 rr0 rr1 r0 r1 v0 v1 : E) (k : ℕ) : E :=
  if k < 20 then [gsq, nb, glp, np, gap, sqIter np 1, sqIter np 2, sqIter np 3, sqIter np 4, sqIter np 5,
    sqIter np 6, sqIter np 7, pd, pb, 1, 1 + nb, 1, hs, word 13503953895743350343 11912009169889063794 0,
    word 11170449402626986623 6620516960021240235 0].getD k 0
  else if k < 405 then word ((k - 20) * 2048) 0 0
  else [ctr, sqIter nb 1, sqIter nb 2, sqIter nb 3, sqIter nb 4, sqIter nb 5, sqIter nb 6, sqIter nb 7,
    sqIter nb 7 * nb, acc, rb, 1, 1 + nb, 1, ct, 1, gen ^ 64, 1, 1 + nb, 1, rc0, rc1, np * np,
    np * np * (np * np), rt, 1, 1 + nb, 1, 1, 1 + gap, 1, rr0, rr1,
    word 13503953895743350343 11912009169889063794 0, word 11170449402626986623 6620516960021240235 0,
    word 64 4294967295 0, r0, r1, r0, r1, v0, v1].getD (k - 405) 0

theorem dvVals_K (gsq nb glp np gap pd pb hs ctr acc rb ct rt rc0 rc1 rr0 rr1 r0 r1 v0 v1 : E) {w : ℕ}
    (hw : w < 385) : dvVals gsq nb glp np gap pd pb hs ctr acc rb ct rt rc0 rc1 rr0 rr1 r0 r1 v0 v1 (20 + w) =
      word (w * 2048) 0 0 := by
  unfold dvVals
  rw [ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel_left]

/-- A `mul_range(1, g^n)` loop's `loop_iff` form from its iterations. -/
theorem loop_of_all {n : ℕ} {B : ℕ → Prop} (hn : 0 < n) (hn' : n < 2 ^ 33) (h : ∀ j < n, B j) :
    ∃ m, 0 < m ∧ gen ^ n = gen ^ m ∧ (∀ j, 0 < j → j < m → gen ^ j ≠ gen ^ n) ∧ ∀ j, 0 ≤ j → j < m → B j :=
  ⟨n, hn, rfl, fun j h1 h2 he => by have := gen_pow_inj' (by omega) hn' he; omega, fun j _ hj => h j hj⟩

theorem one_rel {rd : Reader} {f : String} {ps : List E} (h : coreProgram.Rel rd f (gen ^ 0 :: ps) []) :
    coreProgram.Rel rd f (1 :: ps) [] := by rwa [pow_zero] at h

/-- **`da_verify`'s body holds** under its honest values, the pointers given. -/
theorem dv_holds {rd : Reader} (hl : Low16 rd) {gsq : E} (hT : SquaresAt rd gsq)
    {r0 r1 v0 v1 : E} {r : ℕ} {pb pd hs ctr acc rb ct rt rc0 rc1 rr0 rr1 : E}
    (hr1 : 1 ≤ r) (hr2 : r ≤ LeanDa.maxRows)
    (h88 : ∀ i < r, L88Step rd pb pd (gen ^ i))
    (hiv0 : LoadHolds rd hs 0 (digestScalars paramIv).1) (hiv1 : LoadHolds rd hs 1 (digestScalars paramIv).2)
    (hkc : IsInK ctr) (hctr : ∀ k < 385, ∀ w, rd (ctr.limb 0 * Parameters.gpow k) = some w → w = word (k * 2048) 0 0)
    (h89 : ∀ i < r, L89Step rd acc rb (gen ^ i))
    (hcol : ∀ b < 128, Meaning_da_verify_column (decide (b < 64)) rd
      [gen ^ b, gen ^ r, gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r, pb, ct, rb,
        hs, ctr] [])
    (h92 : ∀ i < r, L92Step rd rb (gen ^ i))
    (hlv7 : Meaning_da_levels 7 rd [ct] [rc0, rc1])
    (h93 : ∀ i < r, L93Step rd pb rt (gen ^ i))
    (h94 : ∀ d < LeanDa.nPad r - r, L94Step rd rt (gen ^ r) (gen ^ d))
    (hlvr : Meaning_da_levels (LeanDa.logPad r) rd [rt] [rr0, rr1])
    (hfin : CompressCells ![rr0, rr1, rc0, rc1] (digestScalars paramIv).1 (digestScalars paramIv).2 r0 r1
      (metadataCell 64 true))
    (hv0 : LoadHolds rd hs 256 v0) (hv1 : LoadHolds rd hs 257 v1) :
    Stmt.HoldsList (coreProgram.Rel rd) rd (fun v => dvVals gsq (gen ^ r) (gen ^ LeanDa.logPad r)
      (gen ^ LeanDa.nPad r) (gen ^ (LeanDa.nPad r - r)) pd pb hs ctr acc rb ct rt rc0 rc1 rr0 rr1 r0 r1 v0 v1 v.idx)
      dvBody False (fun rs => rs = [r0, r1, v0, v1]) := by
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hlp := logPad_le hr2
  have hN := nPad_le hr2
  have hrN : r ≤ LeanDa.nPad r := ((logPad_iff (lp := LeanDa.logPad r) hr1).mp rfl).1
  rw [dvBody, holdsList_append, holdsList_append, holdsList_atoms']
  simp only [dvA, dvB, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    word_one, word_g64]
  have hk1 : IsInK (1 + gen ^ r) := isInK_one_add.mpr (isInK_gen_pow r)
  have hcolRel : ∀ b < 128, coreProgram.Rel rd (colName (decide (b < 64))) [gen ^ b, gen ^ r,
      gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r, pb, ct, rb, hs, ctr] [] :=
    fun b hb => (da_verify_column_iff _ rd _ _).mpr (hcol b hb)
  refine ⟨da_row_shape_complete hl hT _ _ _ ⟨_, _, _, _, _, rfl, rfl, r, hr1, hr2, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hk1,
    fun _ => one_rel ((l88_iff rd _ _ _ 0).mpr (loop_of_all hr1 hr33 h88)),
    rfl, by rw [← iv0_word] at hiv0; exact hiv0, rfl, by rw [← iv1_word] at hiv1; exact hiv1, fun a ha => ?_, ⟨hkc, fun k hk w hw => ?_⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hk1,
    fun _ => one_rel ((l89_iff rd _ _ _ 0).mpr (loop_of_all hr1 hr33 h89)),
    rfl, one_rel ((colLoop_iff true rd _ rfl 0).mpr ⟨64, by norm_num, by rw [colLoopEnd_eq, ite_pos' rfl],
      fun j h1 h2 he => ?_, fun b _ hb => ?_⟩),
    rfl, ?_, rfl, rfl, rfl, hk1,
    fun _ => one_rel ((l92_iff rd _ _ 0).mpr (loop_of_all hr1 hr33 h92)),
    (da_levels_iff 7 (by norm_num) _ _).mpr hlv7, rfl, rfl, rfl, rfl, rfl, hk1,
    fun _ => one_rel ((l93_iff rd _ _ _ 0).mpr (loop_of_all hr1 hr33 h93)),
    rfl, rfl, rfl, isInK_one_add.mpr (isInK_gen_pow _), fun hne => ?_,
    dl_dispatch.mpr ⟨_, by omega, rfl, hlvr⟩, rfl, rfl, rfl, ?_, rfl, rfl, hv0, hv1, rfl⟩
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    exact dvVals_K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (List.mem_range.mp hw)
  · simp only [List.length_map, List.length_range] at hk
    simp only [List.getElem_map, List.getElem_range]
    rw [hctr k hk w hw]
    exact (dvVals_K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk).symm
  · rw [colLoopEnd_eq, ite_pos' rfl] at he
    have := gen_pow_inj' (by omega) (by norm_num) he
    omega
  · have := hcolRel b (by omega)
    rwa [decide_eq_true hb] at this
  · refine (colLoop_iff false rd [gen ^ r, gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r,
      pb, ct, rb, hs, ctr] rfl 64).mpr ⟨128, by norm_num, by rw [colLoopEnd_eq, ite_neg' (by decide)],
      fun j h1 h2 he => ?_, fun b hb hb' => ?_⟩
    · rw [colLoopEnd_eq, ite_neg' (by decide)] at he
      have := gen_pow_inj' (by omega) (by norm_num) he
      omega
    · have := hcolRel b hb'
      rwa [decide_eq_false (by omega)] at this
  · have hpos : 0 < LeanDa.nPad r - r := by
      by_contra h0
      apply hne
      rw [show LeanDa.nPad r - r = 0 by omega, pow_zero]
      exact e_add_eq_zero_iff.mpr rfl
    exact one_rel ((l94_iff rd _ _ _ 0).mpr (loop_of_all hpos (by omega) h94))
  · rw [← iv0_word, ← iv1_word, ← md64_word] at hfin
    exact hfin

/-- **The converse of `da_verify_facts`**: the facts give `da_verify`'s relation. -/
theorem da_verify_of_facts {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    {r0 r1 v0 v1 : E} (h : DaFacts rd r0 r1 v0 v1) : coreProgram.Rel rd "da_verify" [gsq] [r0, r1, v0, v1] := by
  obtain ⟨r, pb, pd, hs, ctr, acc, rb, ct, rt, rc0, rc1, rr0, rr1, hr1, hr2, h88, hiv0, hiv1, hkc, hctr, h89,
    hcol, h92, hlv7, h93, h94, hlvr, hfin, hv0, hv1⟩ := h
  rw [rel_of_find find_dv]
  exact ⟨_, rfl, dv_holds hm.low16 hT hr1 hr2 h88 hiv0 hiv1 hkc hctr h89 hcol h92 hlv7 h93 h94 hlvr hfin hv0 hv1⟩

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1
export Digest (da_verify_of_facts)
end LeanVM.Guest.B1
