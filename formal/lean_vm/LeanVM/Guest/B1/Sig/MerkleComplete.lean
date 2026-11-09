/-
  LeanVM.Guest.B1.Sig.MerkleComplete

  A Merkle path completes: the children hinted in the order of the node's bit, each parent hashed.
-/

module

public import LeanVM.Guest.B1.Sig.CodewordComplete
public import LeanVM.Guest.B1.Sig.KMsgComplete

/-!
# The Merkle path, complete

* `check_complete`: an atom holding already completes on an empty range;
* `merkle_level_complete`: one level, its children hinted in order;
* `merkleT_complete`: the path from `cur`, its node at each level the forward fold `mFold`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- **A holding atom completes**, changing nothing. -/
theorem check_complete {a : Atom} {σ : Val} (h : a.Holds rd σ) (lo : Nat) :
    Completes C rd lo lo [.atom a] σ (fun σ' => σ' = σ) :=
  completes_atoms rfl (Ext.refl _ _ _) rfl (fun x hx => by
    simp only [List.mem_singleton, Stmt.atom.injEq] at hx
    subst hx; exact h)

/-- The address of a level: its constant plus the parent's index. -/
def mA (σ : Val) (nodeOf : Nat → Option V) (addrOf : Nat → Nat) (l : Nat) : E :=
  word (addrOf l) 0 0 + match nodeOf l with
    | none => 0
    | some nd => σ nd

/-- A level's children in the order of its bit, from the node and the sibling. -/
def mPair (bit : Bool) (node sib : E) : E × E := if bit then (sib, node) else (node, sib)

theorem mA_congr {σ σ' : Val} {nodeOf : Nat → Option V} {addrOf : Nat → Nat} {l b : Nat}
    (hnd : ∀ nd, nodeOf l = some nd → NBv b nd) (hσ : AgreeBelow b σ σ') :
    mA σ' nodeOf addrOf l = mA σ nodeOf addrOf l := by
  unfold mA
  cases h : nodeOf l with
  | none => rfl
  | some nd => simp only; rw [hσ.apply (hnd nd h)]

theorem canon_mA {σ : Val} {nodeOf : Nat → Option V} {addrOf : Nat → Nat} {l : Nat}
    (h : ∀ nd, nodeOf l = some nd → IsCanonical128 (σ nd)) : IsCanonical128 (mA σ nodeOf addrOf l) := by
  unfold mA
  cases hn : nodeOf l with
  | none => simpa using canon_word (addrOf l) 0
  | some nd => exact canon_add (canon_word _ _) (h nd hn)

theorem k64_vals_eq (pad : Nat) (m0 m1 m2 m3 : V) (c o : Nat) :
    k64 pad m0 m1 m2 m3 c o = [cst c (word (2 ^ 63) 0 0)] ++ [kecS [m0, m1, m2, m3, .n pad, .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)]
      (runV o 1) false false] := rfl

/-- **A 64-byte `keccak` completes** on canonical inputs, its output the inputs' `hcell`. -/
theorem k64_complete {pad : Nat} {m0 m1 m2 m3 : V} {c : Nat} (σ : Val) (hp : PadOK σ pad)
    (hpc : pad + 5 ≤ c) (hm : ∀ v ∈ [m0, m1, m2, m3], NBv c v ∧ IsCanonical128 (σ v)) :
    Completes C rd c (c + 2) (k64 pad m0 m1 m2 m3 c (c + 1)) σ
      (fun σ' => σ' (.n (c + 1)) = (hcell [σ m0, σ m1, σ m2, σ m3]).1 ∧
        IsCanonical128 (σ' (.n (c + 1)))) := by
  rw [k64_vals_eq]
  refine Completes.append (m := c + 1) (by omega) (by omega)
    (by simp [cst, Stmt.vals, Atom.vals]; exact .cons ⟨c, by omega, rfl⟩ (.nil _))
    (cst_complete σ c _) (fun σ1 he1 hp1 => ?_)
  have hag : AgreeBelow c σ σ1 := he1.agree
  have hin : ∀ v ∈ [m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n (pad + 4)], NBv (c + 1) v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ((hm _ (by simp)).1).mono' (by omega)
    · exact ((hm _ (by simp)).1).mono' (by omega)
    · exact ((hm _ (by simp)).1).mono' (by omega)
    · exact ((hm _ (by simp)).1).mono' (by omega)
    all_goals exact ⟨_, by omega, rfl⟩
  have hp1' : PadOK σ1 pad := hp.congr hpc hag
  obtain ⟨q0, q1, q2, q3, q4⟩ := hp1'
  have hcan : ∀ cc : Fin 13, IsCanonical128 (cells13 ([m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2),
      .n (pad + 3), .n c, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)].map σ1) cc) := by
    have h4 : ∀ v ∈ [m0, m1, m2, m3], IsCanonical128 (σ1 v) := fun v hv => by
      rw [hag.apply (hm v hv).1]; exact (hm v hv).2
    intro cc
    fin_cases cc <;> simp [cells13, q0, q1, q2, q3, q4, hp1] <;>
      first | exact h4 _ (by simp) | exact canon_word _ _
  obtain ⟨σ2, he2, hp2, hh2⟩ := kecS_complete (C := C) (rd := rd) σ1 (c + 1) (.inl rfl) rfl hin hcan false false
  refine ⟨σ2, he2.mono (by omega) (by omega), ⟨?_, ?_⟩, hh2⟩
  · have hk : AtomsHold rd σ2 [kecS [m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c,
        .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)] (runV (c + 1) 1) false false] :=
      atomsHold_of_holdsList rfl (hh2 True (fun _ => True) trivial)
    have hag2 : AgreeBelow (c + 1) σ1 σ2 := he2.agree
    have hp2' : PadOK σ2 pad := hp.congr hpc (fun j hj => (hag j hj).trans (hag2 j (by omega)))
    have := k64_sound (rd := rd) (m0 := m0) (m1 := m1) (m2 := m2) (m3 := m3) (c := c) (o := c + 1) hp2' (h := ?_)
    · rw [this]
      congr 2
      simp only [List.cons.injEq]
      refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;>
        exact ((hag2.apply ((hm _ (by simp)).1.mono' (by omega))).trans (hag.apply (hm _ (by simp)).1))
    · rw [k64_vals_eq]
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · simp only [cst, List.mem_singleton, Stmt.atom.injEq] at ha
        subst ha
        show σ2 (.n c) = _
        rw [hag2.apply ⟨c, by omega, rfl⟩]
        exact hp1
      · exact hk a ha
  · rw [hp2 0 (by norm_num)]
    exact canon_kOut _ _ _ _

/-- **One level of a Merkle path completes**, its children hinted in the order of its bit. -/
theorem merkle_level_complete {pad : Nat} {pp bit cur : V} {b c w : Nat} {nodeL : List Stmt} (σ : Val)
    (hp : PadOK σ pad) (hpb : pad + 5 ≤ b) (hpp : NBv b pp) (hbit : NBv b bit) (hcur : NBv b cur)
    (hseq : SeqOK (b + 4) ([cst (b + 4) (word w 0 0)] ++ nodeL) c) (hcb : b + 5 ≤ c)
    {Aval : E} (hA : ∀ σ', AgreeBelow b σ σ' → AtomsHold rd σ' ([cst (b + 4) (word w 0 0)] ++ nodeL) →
      σ' (.n (c - 1)) = Aval) (hAc : IsCanonical128 Aval) {bt : Bool}
    (hbv : σ bit = if bt then 1 else 0) {sib : E} (hsc : IsCanonical128 sib)
    (hcc : IsCanonical128 (σ cur)) (hppc : IsCanonical128 (σ pp))
    (hh : σ (.n b) = (mPair bt (σ cur) sib).1 ∧ σ (.n (b + 1)) = (mPair bt (σ cur) sib).2) :
    Completes C rd b (c + 2)
      ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
          addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) bit (.n (b + 3)), cst (b + 4) (word w 0 0)] ++
        nodeL ++ k64 pad pp (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1)) σ
      (fun σ' => σ' (.n (c + 1)) = (hcell [σ pp, Aval, (mPair bt (σ cur) sib).1,
        (mPair bt (σ cur) sib).2]).1 ∧ IsCanonical128 (σ' (.n (c + 1))) ∧ σ' (.n b) = σ (.n b) ∧
        σ' (.n (b + 1)) = σ (.n (b + 1))) := by
  have hle := hseq.le
  have hsplit : [hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
      addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) bit (.n (b + 3)), cst (b + 4) (word w 0 0)] ++
      nodeL ++ k64 pad pp (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1) =
      [hintW "siblings" [.n b, .n (b + 1)]] ++ ([addS (.n (b + 2)) cur (.n b),
        addS (.n (b + 3)) (.n b) (.n (b + 1))] ++ ([mulS (.n (b + 2)) bit (.n (b + 3))] ++
        (([cst (b + 4) (word w 0 0)] ++ nodeL) ++ k64 pad pp (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1)))) := by
    simp
  rw [hsplit]
  have hs2 : SeqOK (b + 2) [addS (.n (b + 2)) cur (.n b), addS (.n (b + 3)) (.n b) (.n (b + 1))] (b + 4) :=
    ⟨⟨rfl, hcur.mono' (by omega), ⟨b, by omega, rfl⟩⟩, ⟨rfl, ⟨b, by omega, rfl⟩, ⟨b + 1, by omega, rfl⟩⟩, rfl⟩
  refine Completes.append (m := b + 2) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.nil _)))
    (hintKeep_complete σ _ _ _ _) (fun σ1 he1 hp1 => ?_)
  rw [hp1]
  refine Completes.append (m := b + 4) (by omega) (by omega) hs2.numBelow (seq_completes hs2 σ)
    (fun σ2 he2 hp2 => ?_)
  have hag2 : AgreeBelow (b + 2) σ σ2 := he2.agree
  have e2 : σ2 (.n (b + 2)) = σ2 cur + σ2 (.n b) := hp2.atom (a := .add _ _ _) (by simp [addS])
  have e3 : σ2 (.n (b + 3)) = σ2 (.n b) + σ2 (.n (b + 1)) := hp2.atom (a := .add _ _ _) (by simp [addS])
  have hb2 : σ2 (.n b) = σ (.n b) := hag2.apply ⟨b, by omega, rfl⟩
  have hb12 : σ2 (.n (b + 1)) = σ (.n (b + 1)) := hag2.apply ⟨b + 1, by omega, rfl⟩
  have hc2 : σ2 cur = σ cur := hag2.apply (hcur.mono' (by omega))
  have hbit2 : σ2 bit = σ bit := hag2.apply (hbit.mono' (by omega))
  have hmul : (Atom.mul (.n (b + 2)) bit (.n (b + 3))).Holds rd σ2 := by
    show σ2 (.n (b + 2)) = σ2 bit * σ2 (.n (b + 3))
    rw [e2, e3, hb2, hb12, hc2, hbit2, hbv, hh.1, hh.2]
    cases bt
    · simp [mPair, e_add_self]
    · simp [mPair, add_comm]
  refine Completes.append (m := b + 4) le_rfl (by omega)
    (by simp only [mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
        exact .cons ⟨b + 2, by omega, rfl⟩ (.cons (hbit.mono' (show b ≤ b + 4 by omega))
          (.cons ⟨b + 3, by omega, rfl⟩ (.nil _))))
    (check_complete hmul (b + 4)) (fun σ3 he3 hp3 => ?_)
  rw [hp3]
  refine Completes.append (m := c) (by omega) (by omega) hseq.numBelow (seq_completes hseq σ2)
    (fun σ4 he4 hp4 => ?_)
  have hag4 : AgreeBelow (b + 4) σ2 σ4 := he4.agree
  have hag24 : AgreeBelow b σ σ4 := fun j hj => (hag2 j (by omega)).trans (hag4 j (by omega))
  have hadr : σ4 (.n (c - 1)) = Aval := hA σ4 hag24 hp4
  have hpad4 : PadOK σ4 pad := hp.congr hpb hag24
  have h4b : σ4 (.n b) = σ (.n b) := (hag4.apply ⟨b, by omega, rfl⟩).trans hb2
  have h4b1 : σ4 (.n (b + 1)) = σ (.n (b + 1)) := (hag4.apply ⟨b + 1, by omega, rfl⟩).trans hb12
  have h4pp : σ4 pp = σ pp := hag24.apply hpp
  have hpc : IsCanonical128 (mPair bt (σ cur) sib).1 ∧ IsCanonical128 (mPair bt (σ cur) sib).2 := by
    cases bt <;> simp [mPair, hsc, hcc]
  obtain ⟨σ5, he5, ⟨hout, hcan⟩, hh5⟩ := k64_complete (C := C) (rd := rd) (pad := pad)
    (m0 := pp) (m1 := .n (c - 1)) (m2 := .n b) (m3 := .n (b + 1)) (c := c) σ4 hpad4 (by omega) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl)
      · exact ⟨hpp.mono' (by omega), by rw [h4pp]; exact hppc⟩
      · exact ⟨⟨c - 1, by omega, rfl⟩, by rw [hadr]; exact hAc⟩
      · exact ⟨⟨b, by omega, rfl⟩, by rw [h4b, hh.1]; exact hpc.1⟩
      · exact ⟨⟨b + 1, by omega, rfl⟩, by rw [h4b1, hh.2]; exact hpc.2⟩)
  refine ⟨σ5, he5, ⟨?_, hcan, ?_, ?_⟩, hh5⟩
  · have := hout
    rw [this, h4pp, hadr, h4b, h4b1, hh.1, hh.2]
  · rw [he5.apply (Or.inl (by omega)), h4b]
  · rw [he5.apply (Or.inl (by omega)), h4b1]

theorem merkleT_snd_ge (pad : Nat) (pp : V) (bitOf : Nat → V) (nodeOf : Nat → Option V)
    (addrOf : Nat → Nat) : ∀ (m l : Nat) (cur : V) (b : Nat), b ≤ (merkleT pad pp bitOf nodeOf addrOf m l cur b).2.1
  | 0, _, _, _ => le_rfl
  | m + 1, l, cur, b => by
      simp only [merkleT]
      split <;>
        exact le_trans (Nat.le_trans (Nat.le_add_right b _) (Nat.le_add_right _ 2))
          (merkleT_snd_ge pad pp bitOf nodeOf addrOf m (l + 1) _ _)

theorem level_numBelow {pad : Nat} {pp bit cur : V} {b c w : Nat} {nodeL : List Stmt}
    (hpb : pad + 5 ≤ b) (hpp : NBv b pp) (hbit : NBv b bit) (hcur : NBv b cur)
    (hseq : SeqOK (b + 4) ([cst (b + 4) (word w 0 0)] ++ nodeL) c) (hcb : b + 5 ≤ c) :
    NumBelow (c + 2) (Stmt.valsList ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
      addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) bit (.n (b + 3)), cst (b + 4) (word w 0 0)] ++
      nodeL ++ k64 pad pp (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1))) := by
  have hn := hseq.numBelow
  rw [valsList_append] at hn
  intro x hx
  simp only [valsList_append, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · simp only [hintW, addS, mulS, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, Hint.vals,
      Dest.vals, List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact ⟨_, by omega, rfl⟩ | exact hcur.mono' (by omega) | exact hbit.mono' (by omega)
  · obtain ⟨j, hj, rfl⟩ := hn x (List.mem_append_right _ hx)
    exact ⟨j, by omega, rfl⟩
  · simp only [k64, cst, kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hx
    all_goals first | exact ⟨_, by omega, rfl⟩ | exact hpp.mono' (by omega) |
      exact runV_nb (o := c + 1) (n := 1) (by omega) _ hx

/-- **A Merkle path completes**, each level's children loaded in the order of its bit: its node at
each level the forward fold of the siblings, each level's sibling kept. -/
theorem merkleT_complete {pad : Nat} {pp : V} {bitOf : Nat → V} {nodeOf : Nat → Option V}
    {addrOf : Nat → Nat} {bits : Nat → Bool} {sibs : Nat → E} :
    ∀ (m l : Nat) (cur : V) (b : Nat) (σ : Val), PadOK σ pad → pad + 5 ≤ b → NBv b pp → NBv b cur →
      (∀ j < m, NBv b (bitOf (l + j)) ∧ σ (bitOf (l + j)) = if bits (l + j) then 1 else 0) →
      (∀ l' nd, nodeOf l' = some nd → NBv b nd ∧ IsCanonical128 (σ nd)) →
      IsCanonical128 (σ pp) → IsCanonical128 (σ cur) → (∀ j < m, IsCanonical128 (sibs (l + j))) →
      Completes C rd b (merkleT pad pp bitOf nodeOf addrOf m l cur b).2.1
        (merkleT pad pp bitOf nodeOf addrOf m l cur b).1 σ
        (fun σ' => σ' (merkleT pad pp bitOf nodeOf addrOf m l cur b).2.2 =
          mFold (σ pp) (mA σ nodeOf addrOf) bits sibs m l (σ cur) ∧
          IsCanonical128 (σ' (merkleT pad pp bitOf nodeOf addrOf m l cur b).2.2) ∧
          ∀ j < m, mSib σ' bitOf (l + j) (mBase nodeOf l j b) = sibs (l + j))
  | 0, _, cur, b, σ, _, _, _, _, _, _, _, hcc, _ =>
      ⟨σ, Ext.refl _ _ _, ⟨rfl, hcc, fun j hj => absurd hj (by omega)⟩, fun _ _ hn => hn⟩
  | m + 1, l, cur, b, σ, hp, hpb, hpp, hcur, hbits, hnodes, hppc, hcc, hsibs => by
      have h0 := hbits 0 (by omega)
      simp only [Nat.add_zero] at h0
      -- the level's children, loaded
      have hextr : Ext b (b + 2) σ (Function.update (Function.update σ (.n b)
          (mPair (bits l) (σ cur) (sibs l)).1) (.n (b + 1)) (mPair (bits l) (σ cur) (sibs l)).2) :=
        fun v hv => by
          rw [Function.update_of_ne (hv (b + 1) (by omega) (by omega)),
            Function.update_of_ne (hv b le_rfl (by omega))]
      set σr := Function.update (Function.update σ (.n b) (mPair (bits l) (σ cur) (sibs l)).1) (.n (b + 1))
        (mPair (bits l) (σ cur) (sibs l)).2 with hσr
      have hr0 : σr (.n b) = (mPair (bits l) (σ cur) (sibs l)).1 := by
        rw [hσr, Function.update_of_ne (by simp), Function.update_self]
      have hr1 : σr (.n (b + 1)) = (mPair (bits l) (σ cur) (sibs l)).2 := by
        rw [hσr, Function.update_self]
      have hagr : AgreeBelow b σ σr := hextr.agree
      have hppr : σr pp = σ pp := hagr.apply hpp
      have hcurr : σr cur = σ cur := hagr.apply hcur
      -- the level, then the rest
      have hall : ∀ (c : Nat) (nodeL : List Stmt), b + 5 ≤ c → mNext nodeOf l b = c + 2 →
          SeqOK (b + 4) ([cst (b + 4) (word (addrOf l) 0 0)] ++ nodeL) c →
          (∀ σ', AgreeBelow b σr σ' → AtomsHold rd σ' ([cst (b + 4) (word (addrOf l) 0 0)] ++ nodeL) →
            σ' (.n (c - 1)) = mA σ nodeOf addrOf l) →
          merkleT pad pp bitOf nodeOf addrOf (m + 1) l cur b =
            ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
              addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) (bitOf l) (.n (b + 3)),
              cst (b + 4) (word (addrOf l) 0 0)] ++ nodeL ++ k64 pad pp (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1) ++
              (merkleT pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 2)).1,
              (merkleT pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 2)).2.1,
              (merkleT pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 2)).2.2) →
          Completes C rd b (merkleT pad pp bitOf nodeOf addrOf (m + 1) l cur b).2.1
            (merkleT pad pp bitOf nodeOf addrOf (m + 1) l cur b).1 σ
            (fun σ' => σ' (merkleT pad pp bitOf nodeOf addrOf (m + 1) l cur b).2.2 =
              mFold (σ pp) (mA σ nodeOf addrOf) bits sibs (m + 1) l (σ cur) ∧
              IsCanonical128 (σ' (merkleT pad pp bitOf nodeOf addrOf (m + 1) l cur b).2.2) ∧
              ∀ j < m + 1, mSib σ' bitOf (l + j) (mBase nodeOf l j b) = sibs (l + j)) := by
        intro c nodeL hc hnx hseq hA heq
        rw [heq]
        have hge := merkleT_snd_ge pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 2)
        refine Completes.reload (hextr.mono le_rfl (show b + 2 ≤
          (merkleT pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 2)).2.1 by omega)) ?_
        refine Completes.append (m := c + 2) (by omega) hge
          (level_numBelow hpb hpp h0.1 hcur hseq hc)
          (merkle_level_complete (C := C) (rd := rd) σr (hp.congr hpb hagr) hpb hpp h0.1 hcur hseq hc hA
            (canon_mA (fun nd h => (hnodes l nd h).2)) (by rw [hagr.apply h0.1]; exact h0.2)
            (hsibs 0 (by omega)) (by rw [hcurr]; exact hcc) (by rw [hppr]; exact hppc)
            ⟨by rw [hr0, hcurr, Nat.add_zero], by rw [hr1, hcurr, Nat.add_zero]⟩)
          (fun σ1 he1 hp1 => ?_)
        obtain ⟨hv1, hc1, hk0, hk1⟩ := hp1
        have hag : AgreeBelow b σ σ1 := fun j hj => (hagr j hj).trans (he1.agree j hj)
        have hpp1 : σ1 pp = σ pp := hag.apply hpp
        have hA1 : mA σ1 nodeOf addrOf = mA σ nodeOf addrOf :=
          funext fun l' => mA_congr (fun nd h => (hnodes l' nd h).1) hag
        have hstep : mFold (σ pp) (mA σ nodeOf addrOf) bits sibs (m + 1) l (σ cur) =
            mFold (σ1 pp) (mA σ1 nodeOf addrOf) bits sibs m (l + 1) (σ1 (.n (c + 1))) := by
          rw [hpp1, hA1, hv1, hppr, hcurr, mFold]
          simp only [mPair]
          cases bits l <;> rfl
        have hb1 : ∀ j < m, NBv (c + 2) (bitOf (l + 1 + j)) ∧
            σ1 (bitOf (l + 1 + j)) = if bits (l + 1 + j) then 1 else 0 := by
          intro j hj
          obtain ⟨b1, b2⟩ := hbits (j + 1) (by omega)
          rw [show l + 1 + j = l + (j + 1) by omega]
          exact ⟨b1.mono' (by omega), by rw [hag.apply b1]; exact b2⟩
        have hn1 : ∀ l' nd, nodeOf l' = some nd → NBv (c + 2) nd ∧ IsCanonical128 (σ1 nd) := by
          intro l' nd h
          obtain ⟨n1, n2⟩ := hnodes l' nd h
          exact ⟨n1.mono' (by omega), by rw [hag.apply n1]; exact n2⟩
        obtain ⟨σ', he', ⟨e1, e2, e3⟩, hh'⟩ := merkleT_complete m (l + 1) (.n (c + 1)) (c + 2) σ1
          (hp.congr hpb hag) (by omega) (hpp.mono' (by omega)) ⟨c + 1, by omega, rfl⟩ hb1 hn1
          (by rw [hpp1]; exact hppc) hc1
          (fun j hj => by simpa [show l + 1 + j = l + (j + 1) by omega] using hsibs (j + 1) (by omega))
        refine ⟨σ', he', ⟨by rw [e1, hstep], e2, fun j hj => ?_⟩, hh'⟩
        rcases j with _ | j
        · simp only [Nat.add_zero, mBase]
          have hbk : σ' (.n b) = (mPair (bits l) (σ cur) (sibs l)).1 := by
            rw [he'.apply (Or.inl (by omega)), hk0, hr0]
          have hbk1 : σ' (.n (b + 1)) = (mPair (bits l) (σ cur) (sibs l)).2 := by
            rw [he'.apply (Or.inl (by omega)), hk1, hr1]
          have hbit' : σ' (bitOf l) = if bits l then 1 else 0 := by
            rw [he'.agree.apply (h0.1.mono' (by omega)), hag.apply h0.1]
            exact h0.2
          unfold mSib
          rw [hbit', hbk, hbk1]
          cases bits l <;> simp [mPair]
        · have hb : mBase nodeOf l (j + 1) b = mBase nodeOf (l + 1) j (c + 2) := by
            simp only [mBase, hnx]
          rw [hb, show l + (j + 1) = l + 1 + j by omega]
          exact e3 j (by omega)
      cases hn : nodeOf l with
      | none =>
          refine hall (b + 5) [] (by omega) (by simp [mNext, hn]) ⟨rfl, rfl⟩ (fun σ' _ hat => ?_)
            (by simp [merkleT, hn])
          have := hat.atom (a := .const (.n (b + 4)) (word (addrOf l) 0 0)) (by simp [cst])
          simp only [mA, hn, add_zero]
          exact this
      | some nd =>
          have hnd := hnodes l nd hn
          refine hall (b + 6) [addS (.n (b + 5)) (.n (b + 4)) nd] (by omega) (by simp [mNext, hn])
            ⟨rfl, ⟨rfl, ⟨b + 4, by omega, rfl⟩, hnd.1.mono' (by omega)⟩, rfl⟩ (fun σ' hag hat => ?_)
            (by simp [merkleT, hn])
          have e1 := hat.atom (a := .const (.n (b + 4)) (word (addrOf l) 0 0)) (by simp [cst])
          have e2 := hat.atom (a := .add (.n (b + 5)) (.n (b + 4)) nd) (by simp [addS])
          simp only [Atom.Holds] at e1 e2
          simp only [mA, hn]
          show σ' (.n (b + 5)) = _
          rw [e2, e1, hag.apply hnd.1, hagr.apply hnd.1]

end
end LeanVM.Guest.B1.Sig
