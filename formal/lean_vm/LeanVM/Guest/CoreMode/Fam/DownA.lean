/-
  LeanVM.Guest.CoreMode.Fam.DownA

  `Fam/Down.lean`'s induction down a valid tree, over the instances the aligned allocator places
  (`Tree.instsA`).
-/

module

public import LeanVM.Guest.CoreMode.Fam.Down
public import LeanVM.Guest.Memory.AllocA

/-!
# Facts carried down a valid tree, aligned

`insts_downA`: `insts_down` over `Tree.instsA`: a property of the root's instance that passes from
each node to each of its callees (`KidStep`) holds of every instance the aligned allocator places.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

section

variable {P : Core.Program} {rd : Reader} {fs : String → ℕ} {lp al : String → Bool} {H : Inst → ℕ → E × E}

/-- A kid's instances are among its siblings', aligned. -/
theorem insts_sub_instsKidsA (I : Inst) : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (j i : ℕ) {k : Tree}
    {p : ℕ × ℕ}, ks[i]? = some k → ps[i]? = some p → ∀ J ∈ k.instsA fs lp al H p (H I (j + i)),
      J ∈ Tree.instsKidsA fs lp al H I j ps ks
  | [], _, _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, h, _, _ => by simp at h
  | k' :: ks, p' :: ps, j, 0, k, p, h, h', J, hJ => by
    obtain rfl := Option.some.inj h
    obtain rfl := Option.some.inj h'
    rw [instsKidsA_cons]
    exact List.mem_append_left _ (by simpa using hJ)
  | k' :: ks, p' :: ps, j, i + 1, k, p, h, h', J, hJ => by
    rw [instsKidsA_cons]
    exact List.mem_append_right _ (insts_sub_instsKidsA I ks ps (j + 1) i (by simpa using h)
      (by simpa using h') J (by rw [show j + 1 + i = j + (i + 1) by omega]; exact hJ))

mutual
/-- **Down a valid tree, aligned**: `Q` of the root's instance and of each callee of an instance
having it gives `Q` of every instance. -/
theorem insts_downA {S : List Inst} {Q : Inst → Prop} (hs : KidStep P rd H S Q) :
    ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E) {args rets : List E}, t.Valid P rd args rets →
      (∀ J ∈ t.instsA fs lp al H p hdr, J ∈ S) → (∀ J rest, t.instsA fs lp al H p hdr = J :: rest → Q J) →
      ∀ J ∈ t.instsA fs lp al H p hdr, Q J
  | .node f σ bufs kids, p, hdr, args, rets, hv, hS, h0, J, hJ => by
    rw [instsA_node] at hS h0 hJ
    set ps := kidPosA fs lp al p f bufs kids with hps
    set I : Inst := ⟨.node f σ bufs kids, p.1, p.2, hdr, ps.map Prod.fst, bases p.2 bufs⟩ with hI
    have hQI : Q I := h0 _ _ rfl
    rcases List.mem_cons.mp hJ with rfl | hJ
    · exact hQI
    have hv' := hv
    obtain ⟨fn, hf, -, es, vs, hw, -, hh, hk⟩ := hv'
    refine instsKidsA_down hs I σ kids (calls es) 0 ps hk (fun J' hJ' ↦ hS J' (List.mem_cons_of_mem _ hJ'))
      (fun i k q c hk' hq hc J0 rest hJ0 ↦ ?_) J hJ
    obtain ⟨J1, rest1, he, ht, hfp, -, hh0⟩ := head_instsA (fs := fs) (lp := lp) (al := al) (H := H) k q (H I (0 + i))
    rw [he] at hJ0
    obtain ⟨rfl, -⟩ := List.cons.inj hJ0
    have hmem : J1 ∈ S := hS J1 (List.mem_cons_of_mem _
      (insts_sub_instsKidsA I kids ps 0 i hk' hq J1 (by rw [he]; exact List.mem_cons_self)))
    obtain ⟨hnm, hval, hph⟩ := kidsValid_at hk hc hk'
    refine hs I (hS I List.mem_cons_self) f σ bufs kids rfl fn hf es vs hw hh i c J1 hc hmem
      (by rw [ht]; exact hk') (by simp only [hI, List.getElem?_map, hq, hfp]; rfl)
      (by rw [hh0, Nat.zero_add]) (by rw [ht]; exact hnm) (fun ht' ↦ by rw [ht]; exact hval ht')
      (fun ht' ↦ by rw [ht]; exact hph ht') hQI
  | .phantom .., _, _, _, _, hv, _, _, _, _ => hv.elim

/-- `insts_downA` for the callees of `I` from its `j`-th. -/
theorem instsKidsA_down {S : List Inst} {Q : Inst → Prop} (hs : KidStep P rd H S Q) (I : Inst) (σ : Val) :
    ∀ (ks : List Tree) (cs : List Call) (j : ℕ) (ps : List (ℕ × ℕ)), Tree.KidsValid P rd σ cs ks →
      (∀ J ∈ Tree.instsKidsA fs lp al H I j ps ks, J ∈ S) →
      (∀ (i : ℕ) (k : Tree) (q : ℕ × ℕ) (c : Call), ks[i]? = some k → ps[i]? = some q → cs[i]? = some c →
        ∀ J rest, k.instsA fs lp al H q (H I (j + i)) = J :: rest → Q J) →
      ∀ J ∈ Tree.instsKidsA fs lp al H I j ps ks, Q J
  | [], _, _, _, _, _, _, J, hJ => by rw [instsKidsA_nil] at hJ; exact absurd hJ List.not_mem_nil
  | _ :: _, _, _, [], _, _, _, J, hJ => by rw [instsKidsA_nil_left] at hJ; exact absurd hJ List.not_mem_nil
  | _ :: _, [], _, _ :: _, hk, _, _, _, _ => hk.elim
  | k :: ks, c :: cs, j, q :: ps, hk, hS, h0, J, hJ => by
    rw [instsKidsA_cons] at hS hJ
    rcases List.mem_append.mp hJ with hJ | hJ
    · have hk0 := kidsValid_at (P := P) (rd := rd) hk (i := 0) rfl rfl
      have hh0 : ∀ J rest, k.instsA fs lp al H q (H I j) = J :: rest → Q J := fun J rest h ↦
        h0 0 k q c rfl rfl rfl J rest (by rw [Nat.add_zero]; exact h)
      cases ht : c.taken
      · obtain ⟨f', σ', rfl⟩ := hk0.2.2 ht
        rw [instsA_phantom, List.mem_singleton] at hJ
        subst hJ
        exact hh0 _ _ instsA_phantom
      · exact insts_downA hs k q (H I j) (hk0.2.1 ht) (fun J' h ↦ hS J' (List.mem_append_left _ h)) hh0 J hJ
    · exact instsKidsA_down hs I σ ks cs (j + 1) ps hk.2.2 (fun J' h ↦ hS J' (List.mem_append_right _ h))
        (fun i k' q' c' h1 h2 h3 J' rest h ↦ h0 (i + 1) k' q' c' (by simpa using h1) (by simpa using h2)
          (by simpa using h3) J' rest (by rw [show j + (i + 1) = j + 1 + i by omega]; exact h)) J hJ
end

end

end

end LeanVM.Guest.Res
