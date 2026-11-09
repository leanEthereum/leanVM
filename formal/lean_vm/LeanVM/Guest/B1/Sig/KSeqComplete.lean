/-
  LeanVM.Guest.B1.Sig.KSeqComplete

  Sequential blocks of constants, sums, copies, `KECCAK`s and hints, each defining the next fresh
  values from values below them, complete on canonical cells.
-/

module

public import LeanVM.Guest.B1.Sig.CompleteKit

/-!
# Sequential blocks with `KECCAK`s and hints

`KSeq lo X b ss b'`: each atom of `ss` defines the next fresh values from `b` (a canonical constant, a
sum or a copy of one value, a `KECCAK`'s thirteen, a hint's run) from the block's own values from
`lo` or external ones of `X` below `lo`, ending at `b'`. `kseq_completes`: from a valuation whose
external values of `X` and hinted values are canonical, the block holds of an extension on
`lo ..< b'` keeping the hints, all its values canonical.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- A value a block from `lo` reads at `b`: one of its own, from `lo`, or an external one of `X` below
`lo`. -/
def KRd (lo : Nat) (X : V → Prop) (b : Nat) (v : V) : Prop :=
  (∃ k, lo ≤ k ∧ k < b ∧ v = .n k) ∨ (X v ∧ NBv lo v)

/-- An atom defining the values from `b` up to `m`, from values the block reads. -/
def KSeqA (lo : Nat) (X : V → Prop) (b : Nat) : Atom → Nat → Prop
  | .const d c, m => d = .n b ∧ IsCanonical128 c ∧ m = b + 1
  | .add d x y, m => d = .n b ∧ KRd lo X b x ∧ KRd lo X b y ∧ m = b + 1
  | .copy d x, m => d = .n b ∧ KRd lo X b x ∧ m = b + 1
  | .keccak ins outs _ _, m => ∃ n, (n = 1 ∨ n = 2 ∨ n = 13) ∧ outs = runV b n ∧ ins.length = 13 ∧
      (∀ v ∈ ins, KRd lo X b v) ∧ m = b + n
  | .hint (.witness _ (.stack vs)), m => vs = runV b (m - b) ∧ b ≤ m
  | _, _ => False

/-- A block of such atoms from `b` to `b'`. -/
def KSeq (lo : Nat) (X : V → Prop) : Nat → List Stmt → Nat → Prop
  | b, [], b' => b' = b
  | b, .atom a :: ss, b' => ∃ m, KSeqA lo X b a m ∧ KSeq lo X m ss b'
  | _, _ :: _, _ => False

/-- The hinted values of a block are canonical. -/
def HintsCan (σ : Val) (ss : List Stmt) : Prop :=
  ∀ s vs, Stmt.atom (.hint (.witness s (.stack vs))) ∈ ss → ∀ v ∈ vs, IsCanonical128 (σ v)

/-- The hinted values of a block are kept. -/
def HintsKept (σ σ' : Val) (ss : List Stmt) : Prop :=
  ∀ s vs, Stmt.atom (.hint (.witness s (.stack vs))) ∈ ss → ∀ v ∈ vs, σ' v = σ v

variable {lo : Nat} {X : V → Prop}

theorem KRd.mono {b b' : Nat} {v : V} (h : KRd lo X b v) (hle : b ≤ b') : KRd lo X b' v := by
  rcases h with ⟨k, h1, h2, e⟩ | h
  · exact Or.inl ⟨k, h1, by omega, e⟩
  · exact Or.inr h

theorem KRd.nb {b : Nat} {v : V} (h : KRd lo X b v) (hlo : lo ≤ b) : NBv b v := by
  rcases h with ⟨k, -, h2, e⟩ | ⟨-, k, hk, e⟩
  · exact ⟨k, h2, e⟩
  · exact ⟨k, by omega, e⟩

theorem KSeqA.le {b m : Nat} {a : Atom} (h : KSeqA lo X b a m) : b ≤ m := by
  cases a with
  | const d c => obtain ⟨-, -, rfl⟩ := h; omega
  | add d x y => obtain ⟨-, -, -, rfl⟩ := h; omega
  | copy d x => obtain ⟨-, -, rfl⟩ := h; omega
  | keccak ins outs i o => obtain ⟨_, -, -, -, -, rfl⟩ := h; omega
  | hint hh =>
      match hh, h with
      | .witness _ (.stack _), ⟨_, hbm⟩ => exact hbm
  | _ => exact h.elim

theorem KSeq.le : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, KSeq lo X b ss b' → b ≤ b'
  | _, [], _, h => by simp only [KSeq] at h; omega
  | _, .atom _ :: _, _, ⟨_, h1, h2⟩ => le_trans h1.le (KSeq.le h2)
  | _, .ite .. :: _, _, h | _, .match_ .. :: _, _, h | _, .call .. :: _, _, h
  | _, .callIf .. :: _, _, h | _, .dispatch .. :: _, _, h | _, .ret _ :: _, _, h => h.elim

theorem KSeq.append : ∀ {b m b' : Nat} {xs ys : List Stmt}, KSeq lo X b xs m → KSeq lo X m ys b' →
    KSeq lo X b (xs ++ ys) b'
  | _, _, _, [], _, h1, h2 => by simp only [KSeq] at h1; subst h1; exact h2
  | _, _, _, .atom _ :: _, _, ⟨m', h1, h2⟩, h3 => ⟨m', h1, KSeq.append h2 h3⟩
  | _, _, _, .ite .. :: _, _, h, _ | _, _, _, .match_ .. :: _, _, h, _
  | _, _, _, .call .. :: _, _, h, _ | _, _, _, .callIf .. :: _, _, h, _
  | _, _, _, .dispatch .. :: _, _, h, _ | _, _, _, .ret _ :: _, _, h, _ => h.elim

theorem KSeq.atoms : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, KSeq lo X b ss b' → atomsOnly ss = true
  | _, [], _, _ => rfl
  | _, .atom _ :: ss, _, ⟨_, _, h⟩ => (KSeq.atoms h : atomsOnly ss = true)
  | _, .ite .. :: _, _, h | _, .match_ .. :: _, _, h | _, .call .. :: _, _, h
  | _, .callIf .. :: _, _, h | _, .dispatch .. :: _, _, h | _, .ret _ :: _, _, h => h.elim

theorem runV_mem_nb {o n m : Nat} (h : o + n ≤ m) {v : V} (hv : v ∈ runV o n) : NBv m v := by
  simp only [runV, List.mem_map, List.mem_range] at hv
  obtain ⟨k, hk, rfl⟩ := hv
  exact ⟨o + k, by omega, rfl⟩

theorem KSeqA.vals {b m : Nat} {a : Atom} (hlo : lo ≤ b) (h : KSeqA lo X b a m) : NumBelow m a.vals := by
  have hle := h.le
  intro v hv
  cases a with
  | const d c =>
      obtain ⟨rfl, -, rfl⟩ := h
      simp only [Atom.vals, List.mem_singleton] at hv
      subst hv; exact ⟨b, by omega, rfl⟩
  | add d x y =>
      obtain ⟨rfl, hx, hy, rfl⟩ := h
      simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨b, by omega, rfl⟩
      · exact (hx.nb hlo).mono' (by omega)
      · exact (hy.nb hlo).mono' (by omega)
  | copy d x =>
      obtain ⟨rfl, hx, rfl⟩ := h
      simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨b, by omega, rfl⟩
      · exact (hx.nb hlo).mono' (by omega)
  | keccak ins outs i o =>
      obtain ⟨_, -, rfl, -, hin, rfl⟩ := h
      simp only [Atom.vals, List.mem_append] at hv
      rcases hv with hv | hv
      · exact ((hin v hv).nb hlo).mono' (by omega)
      · exact runV_mem_nb (by omega) hv
  | hint hh =>
      match hh, h with
      | .witness _ (.stack vs), ⟨e, _⟩ =>
          subst e
          simp only [Atom.vals, Hint.vals, Dest.vals] at hv
          exact runV_mem_nb (by omega) hv
  | _ => exact h.elim

theorem KSeq.numBelow : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, lo ≤ b → KSeq lo X b ss b' →
    NumBelow b' (Stmt.valsList ss)
  | _, [], _, _, _ => NumBelow.nil _
  | _, .atom _ :: _, _, hlo, ⟨_, h1, h2⟩ => by
      rw [valsList_cons]
      exact ((h1.vals hlo).mono (KSeq.le h2)).append (KSeq.numBelow (le_trans hlo h1.le) h2)
  | _, .ite .. :: _, _, _, h | _, .match_ .. :: _, _, _, h | _, .call .. :: _, _, _, h
  | _, .callIf .. :: _, _, _, h | _, .dispatch .. :: _, _, _, h | _, .ret _ :: _, _, _, h => h.elim

/-- A block's hints lie in its range. -/
theorem KSeq.hint_range : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, KSeq lo X b ss b' →
    ∀ s vs, Stmt.atom (.hint (.witness s (.stack vs))) ∈ ss → ∀ v ∈ vs, ∃ k, b ≤ k ∧ k < b' ∧ v = .n k
  | _, [], _, _, _, _, h, _, _ => absurd h (by simp)
  | b, .atom a :: ss, b', ⟨m, h1, h2⟩, s, vs, hm, v, hv => by
      have hle := KSeq.le h2
      rcases List.mem_cons.mp hm with e | hm
      · cases e
        obtain ⟨e, hbm⟩ := h1
        subst e
        simp only [runV, List.mem_map, List.mem_range] at hv
        obtain ⟨k, hk, rfl⟩ := hv
        exact ⟨b + k, by omega, by omega, rfl⟩
      · obtain ⟨k, h1', h2', e⟩ := KSeq.hint_range h2 s vs hm v hv
        exact ⟨k, le_trans h1.le h1', h2', e⟩
  | _, .ite .. :: _, _, h, _, _, _, _, _ | _, .match_ .. :: _, _, h, _, _, _, _, _
  | _, .call .. :: _, _, h, _, _, _, _, _ | _, .callIf .. :: _, _, h, _, _, _, _, _
  | _, .dispatch .. :: _, _, h, _, _, _, _, _ | _, .ret _ :: _, _, h, _, _, _, _, _ => h.elim

theorem KRd.canon {b : Nat} {v : V} {σ : Val} (h : KRd lo X b v) (hX : ∀ v, X v → NBv lo v → IsCanonical128 (σ v))
    (hin : ∀ j, lo ≤ j → j < b → IsCanonical128 (σ (.n j))) : IsCanonical128 (σ v) := by
  rcases h with ⟨k, h1, h2, rfl⟩ | ⟨hx, hn⟩
  · exact hin k h1 h2
  · exact hX v hx hn

/-- **One atom of a sequential block completes**, its values canonical, a hint keeping its own. -/
theorem kseqA_complete {b m : Nat} {a : Atom} (hlo : lo ≤ b) (h : KSeqA lo X b a m) (σ : Val)
    (hX : ∀ v, X v → NBv lo v → IsCanonical128 (σ v)) (hin : ∀ j, lo ≤ j → j < b → IsCanonical128 (σ (.n j)))
    (hh : ∀ s vs, a = .hint (.witness s (.stack vs)) → ∀ v ∈ vs, IsCanonical128 (σ v)) :
    ∃ σ', Ext b m σ σ' ∧ a.Holds rd σ' ∧ (∀ j, b ≤ j → j < m → IsCanonical128 (σ' (.n j))) ∧
      ∀ s vs, a = .hint (.witness s (.stack vs)) → ∀ v ∈ vs, σ' v = σ v := by
  have hat : ∀ {σ' : Val} {Post : Val → Prop}, Completes (fun _ _ _ => True) rd b m [.atom a] σ Post →
      ∃ σ', Ext b m σ σ' ∧ Post σ' ∧ a.Holds rd σ' := fun ⟨σ', he, hp, hh'⟩ =>
    ⟨σ', he, hp, (hh' True (fun _ => True) trivial).1⟩
  cases a with
  | const d c =>
      obtain ⟨rfl, hcan, rfl⟩ := h
      obtain ⟨σ', he, hp, ha⟩ := hat (σ' := σ) (cst_complete (C := fun _ _ _ => True) (rd := rd) σ b c)
      refine ⟨σ', he, ha, fun j h1 h2 => ?_, fun s vs e => by cases e⟩
      rw [show j = b by omega, hp]; exact hcan
  | add d x y =>
      obtain ⟨rfl, hx, hy, rfl⟩ := h
      obtain ⟨σ', he, hp, ha⟩ := hat (σ' := σ)
        (addS_complete (C := fun _ _ _ => True) (rd := rd) σ b (hx.nb hlo) (hy.nb hlo))
      refine ⟨σ', he, ha, fun j h1 h2 => ?_, fun s vs e => by cases e⟩
      rw [show j = b by omega, hp]
      exact canon_add (hx.canon hX hin) (hy.canon hX hin)
  | copy d x =>
      obtain ⟨rfl, hx, rfl⟩ := h
      obtain ⟨σ', he, hp, ha⟩ := hat (σ' := σ)
        (copyS_complete (C := fun _ _ _ => True) (rd := rd) σ b (hx.nb hlo))
      refine ⟨σ', he, ha, fun j h1 h2 => ?_, fun s vs e => by cases e⟩
      rw [show j = b by omega, hp]
      exact hx.canon hX hin
  | keccak ins outs i o =>
      obtain ⟨n, hn, rfl, hl, hin', rfl⟩ := h
      have hcan : ∀ cc : Fin 13, IsCanonical128 (cells13 (ins.map σ) cc) := by
        intro cc
        simp only [cells13]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem (by rw [hl]; exact cc.isLt)]
        simp only [Option.map_some, Option.getD_some]
        exact (hin' _ (List.getElem_mem _)).canon hX hin
      obtain ⟨σ', he, hp, ha⟩ := hat (σ' := σ) (kecS_complete (C := fun _ _ _ => True) (rd := rd) σ b hn hl
        (fun v hv => (hin' v hv).nb hlo) hcan i o)
      refine ⟨σ', he, ha, fun j h1 h2 => ?_, fun s vs e => by cases e⟩
      rw [show j = b + (j - b) by omega, hp (j - b) (by omega)]
      exact canon_kOut _ _ _ _
  | hint hh' =>
      match hh', h with
      | .witness s0 (.stack vs0), ⟨e, hbm⟩ =>
          refine ⟨σ, Ext.refl _ _ _, trivial, fun j h1 h2 => ?_, fun s vs _ v _ => rfl⟩
          have := hh s0 vs0 rfl (.n j) (by
            rw [e]; simp only [runV, List.mem_map, List.mem_range]; exact ⟨j - b, by omega, by
              congr 1; omega⟩)
          exact this
      | .bits .., hf => exact hf.elim
      | .bitsExp .., hf => exact hf.elim
      | .limbs .., hf => exact hf.elim
      | .log2Ceil .., hf => exact hf.elim
      | .witness _ (.heap ..), hf => exact hf.elim
  | _ => exact h.elim

/-- **A sequential block completes** on canonical cells, keeping its hints. -/
theorem kseq_complete : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, lo ≤ b → KSeq lo X b ss b' → ∀ σ : Val,
    (∀ v, X v → NBv lo v → IsCanonical128 (σ v)) → (∀ j, lo ≤ j → j < b → IsCanonical128 (σ (.n j))) →
    HintsCan σ ss →
    ∃ σ', Ext b b' σ σ' ∧ AtomsHold rd σ' ss ∧ (∀ j, lo ≤ j → j < b' → IsCanonical128 (σ' (.n j))) ∧
      HintsKept σ σ' ss
  | _, [], _, _, h, σ, _, hin, _ => by
      simp only [KSeq] at h; subst h
      exact ⟨σ, Ext.refl _ _ _, fun _ ha => absurd ha (by simp), hin, fun _ _ h => absurd h (by simp)⟩
  | b, .atom a :: ss, b', hlo, ⟨m, h1, h2⟩, σ, hX, hin, hh => by
      have hbm := h1.le
      have hmb := KSeq.le h2
      obtain ⟨σ1, he1, ha1, hc1, hk1⟩ := kseqA_complete (rd := rd) hlo h1 σ hX hin
        (fun s vs e v hv => hh s vs (by rw [e]; exact List.mem_cons_self ..) v hv)
      have hag1 : AgreeBelow b σ σ1 := he1.agree
      have hX1 : ∀ v, X v → NBv lo v → IsCanonical128 (σ1 v) := by
        rintro v hv ⟨k, hk, rfl⟩
        rw [← hag1 k (by omega)]
        exact hX _ hv ⟨k, hk, rfl⟩
      obtain ⟨σ2, he2, ha2, hc2, hk2⟩ := kseq_complete (le_trans hlo hbm) h2 σ1 hX1
        (fun j hj1 hj2 => by
          by_cases hjb : j < b
          · rw [← hag1 j hjb]; exact hin j hj1 hjb
          · exact hc1 j (by omega) hj2)
        (fun s vs hm v hv => by
          obtain ⟨k, hk1, hk2, rfl⟩ := KSeq.hint_range h2 s vs hm v hv
          rw [he1.apply (Or.inr hk1)]
          exact hh s vs (List.mem_cons_of_mem _ hm) _ hv)
      have hag2 : AgreeBelow m σ1 σ2 := he2.agree
      refine ⟨σ2, he1.trans he2 hbm hmb, fun x hx => ?_, hc2, fun s vs hm v hv => ?_⟩
      · rcases List.mem_cons.mp hx with e | hx
        · cases e
          exact (atom_congr a fun v hv => by
            obtain ⟨k, hk, rfl⟩ := h1.vals hlo v hv
            exact hag2 k hk).mp ha1
        · exact ha2 x hx
      · rcases List.mem_cons.mp hm with e | hm
        · obtain ⟨k, hj1, hj2, rfl⟩ : ∃ k, b ≤ k ∧ k < m ∧ v = .n k := by
            cases e
            obtain ⟨e', -⟩ := h1
            rw [e'] at hv
            simp only [runV, List.mem_map, List.mem_range] at hv
            obtain ⟨k, hk, rfl⟩ := hv
            exact ⟨b + k, by omega, by omega, rfl⟩
          rw [← hag2 k hj2]
          exact hk1 s vs (Stmt.atom.inj e).symm _ hv
        · obtain ⟨k, hj1, hj2, rfl⟩ := KSeq.hint_range h2 s vs hm v hv
          rw [hk2 s vs hm _ hv, he1.apply (Or.inr hj1)]
  | _, .ite .. :: _, _, _, h, _, _, _, _ | _, .match_ .. :: _, _, _, h, _, _, _, _
  | _, .call .. :: _, _, _, h, _, _, _, _ | _, .callIf .. :: _, _, _, h, _, _, _, _
  | _, .dispatch .. :: _, _, _, h, _, _, _, _ | _, .ret _ :: _, _, _, h, _, _, _, _ => h.elim

/-- **A sequential block completes**, as `Completes`. -/
theorem kseq_completes {b' : Nat} {ss : List Stmt} (h : KSeq lo X lo ss b') (σ : Val)
    (hX : ∀ v, X v → NBv lo v → IsCanonical128 (σ v)) (hh : HintsCan σ ss) :
    Completes C rd lo b' ss σ (fun σ' => AtomsHold rd σ' ss ∧
      (∀ j, lo ≤ j → j < b' → IsCanonical128 (σ' (.n j))) ∧ HintsKept σ σ' ss) := by
  obtain ⟨σ', he, ha, hc', hk⟩ := kseq_complete (rd := rd) le_rfl h σ hX (fun j h1 h2 => by omega) hh
  exact completes_atoms h.atoms he ⟨ha, hc', hk⟩ ha

theorem krd_in' {b k : Nat} (h1 : lo ≤ k) (h2 : k < b) : KRd lo X b (.n k) := Or.inl ⟨k, h1, h2, rfl⟩

theorem KSeqA.vals_rd {b m : Nat} {a : Atom} (h : KSeqA lo X b a m) : ∀ v ∈ a.vals, KRd lo X m v ∨
    ∃ k, b ≤ k ∧ k < m ∧ v = .n k := by
  have hle := h.le
  intro v hv
  cases a with
  | const d c =>
      obtain ⟨rfl, -, rfl⟩ := h
      simp only [Atom.vals, List.mem_singleton] at hv
      subst hv; exact Or.inr ⟨b, le_rfl, by omega, rfl⟩
  | add d x y =>
      obtain ⟨rfl, hx, hy, rfl⟩ := h
      simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact Or.inr ⟨b, le_rfl, by omega, rfl⟩
      · exact Or.inl (hx.mono (by omega))
      · exact Or.inl (hy.mono (by omega))
  | copy d x =>
      obtain ⟨rfl, hx, rfl⟩ := h
      simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact Or.inr ⟨b, le_rfl, by omega, rfl⟩
      · exact Or.inl (hx.mono (by omega))
  | keccak ins outs i o =>
      obtain ⟨_, -, rfl, -, hin, rfl⟩ := h
      simp only [Atom.vals, List.mem_append] at hv
      rcases hv with hv | hv
      · exact Or.inl ((hin v hv).mono (by omega))
      · simp only [runV, List.mem_map, List.mem_range] at hv
        obtain ⟨k, hk, rfl⟩ := hv
        exact Or.inr ⟨b + k, by omega, by omega, rfl⟩
  | hint hh =>
      match hh, h with
      | .witness _ (.stack vs), ⟨e, _⟩ =>
          subst e
          simp only [Atom.vals, Hint.vals, Dest.vals, runV, List.mem_map, List.mem_range] at hv
          obtain ⟨k, hk, rfl⟩ := hv
          exact Or.inr ⟨b + k, by omega, by omega, rfl⟩
  | _ => exact h.elim

/-- **A block's values** are its own, from `lo`, or external ones of `X` below `lo`. -/
theorem KSeq.vals_rd : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, lo ≤ b → KSeq lo X b ss b' →
    ∀ v ∈ Stmt.valsList ss, KRd lo X b' v
  | _, [], _, _, _, v, hv => absurd hv (by simp)
  | _, .atom _ :: _, _, hlo, ⟨_, h1, h2⟩, v, hv => by
      rw [valsList_cons] at hv
      have hle := KSeq.le h2
      rcases List.mem_append.mp hv with hv | hv
      · rcases h1.vals_rd v (by simpa [Stmt.vals] using hv) with h | ⟨k, hk1, hk2, rfl⟩
        · exact h.mono hle
        · exact krd_in' (by omega) (by omega)
      · exact KSeq.vals_rd (le_trans hlo h1.le) h2 v hv
  | _, .ite .. :: _, _, _, h, _, _ | _, .match_ .. :: _, _, _, h, _, _ | _, .call .. :: _, _, _, h, _, _
  | _, .callIf .. :: _, _, _, h, _, _ | _, .dispatch .. :: _, _, _, h, _, _
  | _, .ret _ :: _, _, _, h, _, _ => h.elim

end
end LeanVM.Guest.B1.Sig
