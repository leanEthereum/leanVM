/-
  LeanVM.Guest.B1.VsC.RsRowsAllA

  `rs_eq_rows_all` completes placed, storing its rows into its caller's array past the words it reads.
-/

module

public import LeanVM.Guest.B1.VsC.SelTablesA
public import LeanVM.Guest.B1.Eq.RsRowsAll

/-!
# `rs_eq_rows_all`, placed

`rs_eq_rows_all__L{n}(row, zs, ps)`, `1 ≤ n ≤ 8` (the guest stream's template `rraBody n`,
`Eq/RsRowsAll.lean`), has no words of its own: it reads the `64` words `c` at `row` and the `n`
words `zs`, `ps`, and stores row `i + 1`'s `ringRow` at `row·g^(64 (i + 1) + k)`, in its caller's
array past what it reads. On every memory holding all of these (`rs_eq_rows_all_placed`) its forward
evaluation (`callAtA_fwd`) holds every atom: each stored word is the template's product
(`rraAcc_eq'`, from the coordinates' equations alone), which the caller holds there; no apartness of
the read and written words is needed. The template's shape facts, its stores among them
(`rraStores`), are one kernel decision (`rraOkA_all`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `rs_eq_rows_all__L{n}`'s stores: row `k`'s product after coordinate `i` at `64 (i + 1) + k`. -/
def rraStores (n : ℕ) : List Atom :=
  ((List.range 64).map fun k => (List.range n).map fun i =>
    Atom.load (.n (rrS n k + 2 + rrStride k * i)) (.n 0) (64 * (i + 1) + k)).flatten

/-- What the kernel checks of `rs_eq_rows_all__L{n}`'s template. -/
def rraOkA (n : ℕ) : Bool :=
  leafChecks 3 (rraBody n) &&
    (atomsOf (rraBody n)).all (loadOkB [(0, 64 * (n + 1)), (1, n), (2, n)]) &&
    (atomsOf (rraBody n)).all (fun a => !atomAllocB a) &&
    storesOf 3 (rraBody n) == rraStores n && retOf (rraBody n) == some [.n (rrT n)]

theorem rraOkA_all : ∀ n, 1 ≤ n → n ≤ 8 → rraOkA n = true := by
  have h : ((List.range 8).all fun n => rraOkA (n + 1)) = true := by decide +kernel
  intro n h1 h8
  have := List.all_eq_true.mp h (n - 1) (List.mem_range.mpr (by omega))
  rwa [Nat.sub_add_cancel h1] at this

/-! ## The template from the coordinates' equations -/

theorem rraZ_pow' {σ : Val} {n : ℕ} (h : ∀ k < 64, ∀ i < n, RrCoordOk σ n k i) :
    ∀ k < 64, ∀ i < n, σ (.n (rrZ n k i)) = σ (.n (3 + 2 * i)) ^ 2 ^ k
  | 0, _, i, _ => by simp [rrZ]
  | k + 1, hk, i, hi => by
    rw [rrZ, (h k (by omega) i hi).2.2 (by omega), rraZ_pow' h k (by omega) i hi, ← pow_add,
      ← two_mul, ← pow_succ']

theorem rraAcc_eq' {σ : Val} {n : ℕ} (h : ∀ k < 64, ∀ i < n, RrCoordOk σ n k i) (k : ℕ) (hk : k < 64) :
    ∀ i ≤ n, σ (.n (rrAcc n k i)) = ringRow (σ (.n (rrS n k)))
      (((List.range n).map fun i ↦ σ (.n (3 + 2 * i))).take i)
      (((List.range n).map fun i ↦ σ (.n (4 + 2 * i))).take i) k
  | 0, _ => by rw [ringRow_nil]; rfl
  | i + 1, hi => by
    obtain ⟨e1, e2, -⟩ := h k hk i (by omega)
    rw [ringRow_take_succ _ _ _ _ _ (by simp; omega) (by simp; omega), ← rraAcc_eq' h k hk i (by omega)]
    simp only [List.getElem_map, List.getElem_range]
    rw [show rrAcc n k (i + 1) = rrS n k + 2 + rrStride k * i from rfl, e2, e1,
      rraZ_pow' h k hk i (by omega)]

theorem mem_rraBody_coord {n k i : ℕ} (hk : k < 64) (hi : i < n) {st : Stmt} (h : st ∈ rrCoord n k i) :
    st ∈ rraBody n := by
  simp only [rraBody, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨_, ⟨k, hk, rfl⟩, List.mem_append.mpr (Or.inr (List.mem_flatten.mpr
    ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, List.mem_append.mpr (Or.inl h)⟩))⟩)

theorem mem_rraBody_row {n k : ℕ} (hk : k < 64) : Stmt.atom (.load (.n (rrS n k)) (.n 0) k) ∈ rraBody n := by
  simp only [rraBody, rraRow, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨_, ⟨k, hk, rfl⟩, List.mem_append.mpr (Or.inl (by simp))⟩)

theorem mem_rraBody_head {n i : ℕ} (hi : i < n) :
    Stmt.atom (.load (.n (3 + 2 * i)) (.n 1) i) ∈ rraBody n ∧ Stmt.atom (.load (.n (4 + 2 * i)) (.n 2) i) ∈ rraBody n := by
  simp only [rraBody, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
  exact ⟨Or.inl (Or.inl ⟨_, ⟨i, hi, rfl⟩, by simp [rraHeadBlk]⟩),
    Or.inl (Or.inl ⟨_, ⟨i, hi, rfl⟩, by simp [rraHeadBlk]⟩)⟩

theorem mem_rraStores {n : ℕ} {a : Atom} (h : a ∈ rraStores n) : ∃ k < 64, ∃ i < n,
    a = .load (.n (rrS n k + 2 + rrStride k * i)) (.n 0) (64 * (i + 1) + k) := by
  simp only [rraStores, List.mem_flatten, List.mem_map, List.mem_range] at h
  obtain ⟨_, ⟨k, hk, rfl⟩, h'⟩ := h
  obtain ⟨i, hi, he⟩ := List.mem_map.mp h'
  exact ⟨k, hk, i, List.mem_range.mp hi, he.symm⟩

/-! ## Placed -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **`rs_eq_rows_all__L{n}` completes placed**, from its template. -/
theorem rra_placed {k : ℕ} {name : String} {fn : Fn} {n : ℕ} (h1 : 1 ≤ n)
    (hfind : coreProgram.find? name = some fn) (hparams : fn.params = [.n 0, .n 1, .n 2])
    (hbody : fn.body = rraBody n) (hok : rraOkA n = true) {row z p : E} {zs ps c : List E}
    (hzs : zs.length = n) (hps : ps.length = n) (hc : c.length = 64) {R : ℕ → Prop}
    (hR : (∀ t < 64 * (n + 1), ∃ m, row.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) ∧
      (∀ t < n, ∃ m, z.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) ∧
      ∀ t < n, ∃ m, p.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) (fp c0 : ℕ) :
    CallAtA fs al cert k name [row, z, p] [0] R (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd z zs ∧ ReadsAt rd p ps ∧ ReadsAt rd row c ∧
        ∀ i < n, ∀ k < 64, LoadHolds rd row (64 * (i + 1) + k)
          (ringRow (c.getD k 0) (zs.take (i + 1)) (ps.take (i + 1)) k))
      PostQuiet (fs name) fp c0 c0 := by
  simp only [rraOkA, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨hck, hst⟩, hna⟩, hSeq⟩, hret⟩ := hok
  have hlp : coreProgram.loop name = false := by
    rw [Program.loop_of_find? hfind, Fn.loop, hbody, rraBody]; simp
  have hck' : leafChecks [row, z, p].length fn.body = true := by rw [hbody]; exact hck
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (by
    simp only [leafChecks, Bool.and_eq_true] at hck'; exact hck'.1.1)
  have e := callAtA_fwd (fs := fs) (al := al) (cert := cert) (k := k) (R := R) (D := fun _ => False)
    (Out := fun _ => True) (fp := fp) (c := c0) (rets := [0]) (fun _ => 0) [] [] hfind hlp (by rw [hparams]; rfl) hck'
    ⟨by simp, List.Pairwise.nil⟩ (fun _ _ => trivial) (fun _ h => h.elim)
    (Pre := fun rd => ReadsAt rd z zs ∧ ReadsAt rd p ps ∧ ReadsAt rd row c ∧
        ∀ i < n, ∀ k < 64, LoadHolds rd row (64 * (i + 1) + k)
          (ringRow (c.getD k 0) (zs.take (i + 1)) (ps.take (i + 1)) k))
    fun rd _ _ ⟨hz, hp, hrow, hout⟩ σ hσ => ?_
  · simpa using e
  set S := storesOf [row, z, p].length fn.body with hS
  have hSr : S = rraStores n := by rw [hS, hbody]; exact hSeq
  have hG : ∀ a, Stmt.atom a ∈ fn.body → Good rd S (fun _ => 0) σ a := fun a ha => hσ ▸ fwd_good hc' a ha
  have hσ0 : σ (.n 0) = row := by rw [hσ]; exact fwd_param hc' (by simp)
  have hσ1 : σ (.n 1) = z := by rw [hσ]; exact fwd_param hc' (by simp)
  have hσ2 : σ (.n 2) = p := by rw [hσ]; exact fwd_param hc' (by simp)
  have hok' : ∀ a, Stmt.atom a ∈ fn.body → loadOkB [(0, 64 * (n + 1)), (1, n), (2, n)] a = true :=
    fun a ha => List.all_eq_true.mp hst a (mem_atomsOf' (hbody ▸ ha))
  have hload : ∀ d q off, Stmt.atom (.load d q off) ∈ fn.body →
      (q = .n 0 ∧ off < 64 * (n + 1)) ∨ (q = .n 1 ∧ off < n) ∨ (q = .n 2 ∧ off < n) := fun d q off ha => by
    have h := hok' _ ha
    simpa only [loadOkB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] using h
  have hdef : ∀ off < 64 * (n + 1), ∃ v, LoadHolds rd row off v := fun off ho => by
    by_cases h64 : off < 64
    · exact ⟨_, hrow off (by omega)⟩
    · have := hout (off / 64 - 1) (by omega) (off % 64) (Nat.mod_lt _ (by decide))
      rw [show 64 * (off / 64 - 1 + 1) + off % 64 = off by omega] at this
      exact ⟨_, this⟩
  have hnS : ∀ a, (∀ d q off, a ≠ .load d q off) → a ∉ S := fun a h hm => by
    obtain ⟨d, q, off, he⟩ := storesOf_isLoad hm; exact h d q off he
  refine ⟨fun a ha haS hn => ?_, fun hns a ha => ?_, fun a ha => ?_, fun vs hvs => ?_, ?_, ?_, fun A hA => ?_⟩
  · cases a with
    | load d q off =>
      simp only [Side, haS, ↓reduceIte]
      rcases hload d q off ha with ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩
      · obtain ⟨v, hv⟩ := hdef off ho; rw [hσ0]; exact ⟨hv.1, by rw [hv.2]; rfl⟩
      · rw [hσ1]; exact ⟨(hz off (by omega)).1, by rw [(hz off (by omega)).2]; rfl⟩
      · rw [hσ2]; exact ⟨(hp off (by omega)).1, by rw [(hp off (by omega)).2]; rfl⟩
    | hint => have := hok' _ ha; simp [loadOkB] at this
    | _ =>
      have := hok' _ ha
      simp only [loadOkB, hn, Bool.not_true, Bool.false_eq_true] at this
  · -- a store: row `k`'s product after coordinate `i`
    rw [hSr] at ha
    obtain ⟨k', hk', i, hi, rfl⟩ := mem_rraStores ha
    have hcoord : ∀ k < 64, ∀ i < n, RrCoordOk σ n k i := fun k hk i hi => by
      have hm : ∀ a, Stmt.atom a ∈ rrCoord n k i → a.Holds rd σ := fun a h' => by
        refine hns a (hbody ▸ mem_rraBody_coord hk hi h') (hnS a fun d q off he => ?_)
        subst he
        unfold rrCoord at h'
        split at h' <;> simp at h'
      unfold RrCoordOk
      refine ⟨hm (.add (.n (rrS n k + 1 + rrStride k * i)) (.n (rrZ n k i)) (.n (4 + 2 * i)))
          (by unfold rrCoord; split <;> simp),
        hm (.mul (.n (rrS n k + 2 + rrStride k * i)) (.n (rrAcc n k i)) (.n (rrS n k + 1 + rrStride k * i)))
          (by unfold rrCoord; split <;> simp), fun h63 => ?_⟩
      exact hm (.mul (.n (rrS n k + 3 + 3 * i)) (.n (rrZ n k i)) (.n (rrZ n k i))) (by unfold rrCoord; simp [h63])
    have hrowv : ∀ k < 64, σ (.n (rrS n k)) = c.getD k 0 := fun k hk => by
      have hm := hbody ▸ mem_rraBody_row (n := n) hk
      have hn : Atom.load (.n (rrS n k)) (.n 0) k ∉ S := by
        rw [hSr]; intro h'
        obtain ⟨k', -, i', -, he⟩ := mem_rraStores h'
        simp only [Atom.load.injEq] at he; omega
      have hl := hrow k (by omega); rw [← hσ0] at hl
      rw [good_load_eq hl (hG _ hm) hn, List.getD_eq_getElem _ _ (by omega)]
    have hzv : ((List.range n).map fun i ↦ σ (.n (3 + 2 * i))) = zs := by
      refine List.ext_getElem (by simp [hzs]) fun i h1 h2 => ?_
      simp only [List.getElem_map, List.getElem_range]
      have hm := hbody ▸ (mem_rraBody_head (n := n) (by simpa using h1)).1
      have hn : Atom.load (.n (3 + 2 * i)) (.n 1) i ∉ S := by
        rw [hSr]; intro h'
        obtain ⟨_, -, _, -, he⟩ := mem_rraStores h'
        simp only [Atom.load.injEq] at he; exact absurd he.2.1 (by decide)
      have hl := hz i h2; rw [← hσ1] at hl
      exact good_load_eq hl (hG _ hm) hn
    have hpv : ((List.range n).map fun i ↦ σ (.n (4 + 2 * i))) = ps := by
      refine List.ext_getElem (by simp [hps]) fun i h1 h2 => ?_
      simp only [List.getElem_map, List.getElem_range]
      have hm := hbody ▸ (mem_rraBody_head (n := n) (by simpa using h1)).2
      have hn : Atom.load (.n (4 + 2 * i)) (.n 2) i ∉ S := by
        rw [hSr]; intro h'
        obtain ⟨_, -, _, -, he⟩ := mem_rraStores h'
        simp only [Atom.load.injEq] at he; exact absurd he.2.1 (by decide)
      have hl := hp i h2; rw [← hσ2] at hl
      exact good_load_eq hl (hG _ hm) hn
    have hv := rraAcc_eq' hcoord k' hk' (i + 1) (by omega)
    rw [show rrAcc n k' (i + 1) = rrS n k' + 2 + rrStride k' * i from rfl, hrowv k' hk', hzv, hpv] at hv
    show LoadHolds rd (σ (.n 0)) _ (σ _)
    rw [hσ0, hv]; exact hout i hi k' hk'
  · have := hok' a ha
    cases a with
    | hint hh => simp [loadOkB] at this
    | _ => trivial
  · rw [hbody, hret, Option.some.injEq] at hvs
    subst hvs
    have hT : σ (.n (rrT n)) = word 0 0 := hG (.const (.n (rrT n)) (word 0 0)) (by rw [hbody, rraBody]; simp)
    simp [hT, word_zero]
  · rw [hbody]; exact allocs_atoms _ hna
  · rw [hbody, allocDsts_atoms hna]; rfl
  · obtain ⟨d, q, off, hm, rfl⟩ := mem_loadAddrs hA
    have hm' : Stmt.atom (.load d q off) ∈ fn.body := mem_of_mem_atomsOf hm
    rcases hload d q off hm' with ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, ho⟩
    · obtain ⟨m, he, hRm⟩ := hR.1 off ho; exact ⟨m, by rw [hσ0, he], Or.inr hRm⟩
    · obtain ⟨m, he, hRm⟩ := hR.2.1 off ho; exact ⟨m, by rw [hσ1, he], Or.inr hRm⟩
    · obtain ⟨m, he, hRm⟩ := hR.2.2 off ho; exact ⟨m, by rw [hσ2, he], Or.inr hRm⟩

set_option maxRecDepth 100000 in
/-- **`rs_eq_rows_all` completes placed**, every specialization `__L{n}`, `1 ≤ n ≤ 8`. -/
theorem rs_eq_rows_all_placed {k : ℕ} (n : ℕ) (h1 : 1 ≤ n) (h8 : n ≤ 8) {row z p : E} {zs ps c : List E}
    (hzs : zs.length = n) (hps : ps.length = n) (hc : c.length = 64) {R : ℕ → Prop}
    (hR : (∀ t < 64 * (n + 1), ∃ m, row.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) ∧
      (∀ t < n, ∃ m, z.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) ∧
      ∀ t < n, ∃ m, p.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) (fp c0 : ℕ) :
    CallAtA fs al cert k (rsEqRowsAllNames.getD n "") [row, z, p] [0] R (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd z zs ∧ ReadsAt rd p ps ∧ ReadsAt rd row c ∧
        ∀ i < n, ∀ k < 64, LoadHolds rd row (64 * (i + 1) + k)
          (ringRow (c.getD k 0) (zs.take (i + 1)) (ps.take (i + 1)) k))
      PostQuiet (fs (rsEqRowsAllNames.getD n "")) fp c0 c0 := by
  interval_cases n
  · exact rra_placed (by decide) (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L1») rfl) rfl
      rs_eq_rows_all_L1_body (rraOkA_all 1 (by decide) (by decide)) hzs hps hc hR fp c0
  · exact rra_placed (by decide) (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L2») rfl) rfl
      rs_eq_rows_all_L2_body (rraOkA_all 2 (by decide) (by decide)) hzs hps hc hR fp c0
  · exact rra_placed (by decide) (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L3») rfl) rfl
      rs_eq_rows_all_L3_body (rraOkA_all 3 (by decide) (by decide)) hzs hps hc hR fp c0
  · exact rra_placed (by decide) (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L4») rfl) rfl
      rs_eq_rows_all_L4_body (rraOkA_all 4 (by decide) (by decide)) hzs hps hc hR fp c0
  · exact rra_placed (by decide) (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L5») rfl) rfl
      rs_eq_rows_all_L5_body (rraOkA_all 5 (by decide) (by decide)) hzs hps hc hR fp c0
  · exact rra_placed (by decide) (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L6») rfl) rfl
      rs_eq_rows_all_L6_body (rraOkA_all 6 (by decide) (by decide)) hzs hps hc hR fp c0
  · exact rra_placed (by decide) (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L7») rfl) rfl
      rs_eq_rows_all_L7_body (rraOkA_all 7 (by decide) (by decide)) hzs hps hc hR fp c0
  · exact rra_placed (by decide) (coreProgram_find?_at (j := idx% «rs_eq_rows_all__L8») rfl) rfl
      rs_eq_rows_all_L8_body (rraOkA_all 8 (by decide) (by decide)) hzs hps hc hR fp c0


theorem rs_eq_rows_all_L0_body :
    Fn.body fn% «rs_eq_rows_all__L0» = [.atom (.const (.n 3) (word 0 0)), .ret [.n 3]] :=
  stmtsEqb_sound (by decide +kernel)

/-- **`rs_eq_rows_all__L0` completes placed**: it returns `0`, touching nothing. -/
theorem rs_eq_rows_all_L0_placed {k : ℕ} {row z p : E} {R : ℕ → Prop} {Pre : Reader → Prop} (fp c0 : ℕ) :
    CallAtA fs al cert k "rs_eq_rows_all__L0" [row, z, p] [0] R (fun _ => False) (fun _ => True) Pre
      PostQuiet (fs "rs_eq_rows_all__L0") fp c0 c0 := by
  have hfind : coreProgram.find? "rs_eq_rows_all__L0" = some fn% «rs_eq_rows_all__L0» :=
    coreProgram_find?_at (j := idx% «rs_eq_rows_all__L0») rfl
  have hlp : coreProgram.loop "rs_eq_rows_all__L0" = false := by
    rw [Program.loop_of_find? hfind, Fn.loop, rs_eq_rows_all_L0_body]; simp
  have hpar : Fn.params fn% «rs_eq_rows_all__L0» = [.n 0, .n 1, .n 2] := rfl
  have e := callAtA_straight (fs := fs) (al := al) (cert := cert) (k := k) (R := R) (D := fun _ => False)
    (Out := fun _ => True) (Pre := Pre) (fp := fp) (c := c0) (args := [row, z, p]) (rets := [0])
    (fun _ v => [row, z, p, 0].getD v.idx 0) [] [] hfind hlp (by rw [rs_eq_rows_all_L0_body]; rfl)
    ⟨by simp, List.Pairwise.nil⟩ (fun _ _ => trivial) (fun _ h => h.elim) fun rd _ _ _ => ?_
  · simpa using e
  rw [rs_eq_rows_all_L0_body, hpar]
  refine ⟨rfl, fun vs hvs => ?_, fun a ha => ?_, rfl, rfl, fun A hA => ?_⟩
  · simp only [retOf, Option.some.injEq] at hvs
    subst hvs; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq, reduceCtorEq] at ha
    subst ha
    exact ⟨show (0 : E) = word 0 0 by rw [word_zero], trivial⟩
  · simp [loadAddrs, atomsOf, Ev.loadAddr?] at hA

/-- **`rs_eq_rows_all__L{n}` completes placed**, every `n ≤ 8`. -/
theorem rs_eq_rows_all_placed' {k : ℕ} (n : ℕ) (h8 : n ≤ 8) {row z p : E} {zs ps c : List E}
    (hzs : zs.length = n) (hps : ps.length = n) (hc : c.length = 64) {R : ℕ → Prop}
    (hR : (∀ t < 64 * (n + 1), ∃ m, row.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) ∧
      (∀ t < n, ∃ m, z.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) ∧
      ∀ t < n, ∃ m, p.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) (fp c0 : ℕ) :
    CallAtA fs al cert k (rsEqRowsAllNames.getD n "") [row, z, p] [0] R (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd z zs ∧ ReadsAt rd p ps ∧ ReadsAt rd row c ∧
        ∀ i < n, ∀ k < 64, LoadHolds rd row (64 * (i + 1) + k)
          (ringRow (c.getD k 0) (zs.take (i + 1)) (ps.take (i + 1)) k))
      PostQuiet (fs (rsEqRowsAllNames.getD n "")) fp c0 c0 := by
  rcases Nat.eq_zero_or_pos n with rfl | h1
  · exact rs_eq_rows_all_L0_placed fp c0
  · exact rs_eq_rows_all_placed n h1 h8 hzs hps hc hR fp c0

end
end LeanVM.Guest.B1.VsC
