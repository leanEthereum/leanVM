/-
  LeanVM.Guest.B1.Opening.QueriesPlaced4

  Where an honest query reads, and the walk of a body with one branch.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced3

/-!
# Where a query reads; a body with one branch

`OqQReg`: what a query reads from the caller's region: its challenges, its final coefficients
(final level), its windows (the path's and the cap's two), its flag and its cap leaf.
`oqQLoad_in`: at its honest values each load of a query (`OqQLoad`) reads that region.

`walk_ite_flatM`: a body of flat statements around one branch walks the branch taken;
`ite_parts`: its buffers, frame addresses, calls and loads are those of the flat statements
before, in and after the branch taken (the condition's event has none).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- What a query reads from the caller's region: its challenges, its final coefficients (final
level), its windows (the path's and the cap's two), its flag and its cap leaf. -/
structure OqQReg (R : ℕ → Prop) (s : Oq) (cap flags coefs hs bp : E) (q : ℕ) : Prop where
  co : ∀ off < 2 * s.folds, OqIn R (coefs.limb 0 * Parameters.addressOfIndex off)
  h : s.final = 1 → ∀ off < s.nHs, OqIn R (hs.limb 0 * Parameters.addressOfIndex off)
  b : ∀ off < oqNpw s + 2, OqIn R (bp.limb 0 * Parameters.addressOfIndex off)
  f : OqIn R ((flags * gen ^ (q / 2 ^ (s.pd + 1))).limb 0 * Parameters.addressOfIndex 0)
  c : ∀ e < 2, OqIn R ((cap * gen ^ (4 * (q / 2 ^ (s.pd + 1)) +
    (if q.testBit s.pd then 2 else 0))).limb 0 * Parameters.addressOfIndex e)

theorem OqQReg.mono {R R' : ℕ → Prop} {s : Oq} {cap flags coefs hs bp : E} {q : ℕ}
    (h : OqQReg R s cap flags coefs hs bp q) (hR : ∀ i, R i → R' i) :
    OqQReg R' s cap flags coefs hs bp q :=
  ⟨fun o ho ↦ let ⟨i, h1, h2⟩ := h.co o ho; ⟨i, h1, hR i h2⟩,
    fun hf o ho ↦ let ⟨i, h1, h2⟩ := h.h hf o ho; ⟨i, h1, hR i h2⟩,
    fun o ho ↦ let ⟨i, h1, h2⟩ := h.b o ho; ⟨i, h1, hR i h2⟩,
    let ⟨i, h1, h2⟩ := h.f; ⟨i, h1, hR i h2⟩,
    fun e he ↦ let ⟨i, h1, h2⟩ := h.c e he; ⟨i, h1, hR i h2⟩⟩

/-- **A query's load reads the caller's region**, at its honest values. -/
theorem oqQLoad_in {R : ℕ → Prop} {d : QD} {σ : Val} (hv : d.Hv σ) {coefs hs bp : V}
    (hreg : OqQReg R d.s d.capv d.flagsv (σ coefs) (σ hs) (σ bp) d.q) {p : V} {off : ℕ}
    (hl : OqQLoad d.s coefs hs bp d.ch p off) : OqIn R ((σ p).limb 0 * Parameters.addressOfIndex off) := by
  rcases hl with ⟨rfl, ho⟩ | ⟨hf, rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨rfl, rfl⟩ | ⟨rfl, ho⟩
  · exact hreg.co off ho
  · exact hreg.h hf off ho
  · exact hreg.b off ho
  · rw [d.ptr_flag hv]; exact hreg.f
  · rw [d.ptr_cap hv]; exact hreg.c off ho

/-- `KidsFromIn` grows with the data earlier kids claimed. -/
theorem kidsFromIn_dacc {P : Program} {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader} {σ : Val}
    {R : ℕ → Prop} : ∀ (cs : List Call) {Dacc Dacc' : ℕ → Prop} {b n : ℕ} {Dend : ℕ → Prop},
    (∀ i, Dacc i → Dacc' i) → KidsFromIn P fs cert rd σ R Dacc cs b n Dend →
      KidsFromIn P fs cert rd σ R Dacc' cs b n Dend
  | [], _, _, _, _, _, h, ⟨hn, hd⟩ => ⟨hn, fun i hi ↦ h i (hd i hi)⟩
  | _ :: cs, _, _, _, _, _, h, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ =>
    ⟨m, n', Rk, Dk, hn, fun i hi ↦ (hR i hi).imp_right (h i), hc,
      kidsFromIn_dacc cs (fun i hi ↦ hi.imp (h i) id) hk⟩

/-! ## One branch -/

theorem walk_flatM_fall (σ : Val) : ∀ pre : List Stmt, pre.all Stmt.flatM = true →
    (∀ s ∈ pre, MatchOk σ s) → walk σ pre = .fall (pre.flatMap (fmEvs σ))
  | [], _, _ => rfl
  | s :: pre, h, hd => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [walk, walk_flatM_fall σ pre h.2 (fun s' hs' => hd s' (by simp [hs'])),
      walk1_flatM σ s h.1 (hd s (by simp)), Out.seq, Out.pre, List.flatMap_cons]

/-- **A body of flat statements around one branch** walks the branch taken. -/
theorem walk_ite_flatM (σ : Val) (c : V) (z n post : List Stmt) (vs : List V)
    (hb : (if σ c = 0 then z else n).all Stmt.flatM = true)
    (hbm : ∀ s ∈ (if σ c = 0 then z else n), MatchOk σ s)
    (hp : post.all Stmt.flatM = true) (hpm : ∀ s ∈ post, MatchOk σ s) :
    ∀ pre : List Stmt, pre.all Stmt.flatM = true → (∀ s ∈ pre, MatchOk σ s) →
    walk σ (pre ++ .ite c z n :: (post ++ [.ret vs])) =
      .ret (pre.flatMap (fmEvs σ) ++ .inK c :: ((if σ c = 0 then z else n).flatMap (fmEvs σ) ++
        post.flatMap (fmEvs σ))) vs
  | [], _, _ => by
    rw [List.nil_append, walk, walk1,
      show (if σ c = 0 then walk σ z else walk σ n) = walk σ (if σ c = 0 then z else n) by
        split <;> rfl,
      walk_flatM_fall σ _ hb hbm, walk_flatM σ vs post hp hpm]
    simp [Out.seq, Out.pre]
  | s :: pre, h, hd => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_ite_flatM σ c z n post vs hb hbm hp hpm pre h.2
      (fun s' hs' => hd s' (by simp [hs'])), walk1_flatM σ s h.1 (hd s (by simp)), Out.seq, Out.pre,
      List.flatMap_cons, List.append_assoc]

/-- **A one-branch body's parts** are those of its flat statements before, in and after the branch
taken. -/
theorem ite_parts (σ : Val) (c : V) (pre br post : List Stmt) :
    let es := pre.flatMap (fmEvs σ) ++ .inK c :: (br.flatMap (fmEvs σ) ++ post.flatMap (fmEvs σ))
    let fl := (pre ++ br ++ post).flatMap (fmEvs σ)
    allocDsts es = allocDsts fl ∧ allocs σ es = allocs σ fl ∧ addrs es = addrs fl ∧
      calls es = calls fl ∧ loadAddrs σ es = loadAddrs σ fl := by
  simp only [allocDsts, allocs, addrs, calls, loadAddrs, List.flatMap_append, List.filterMap_append,
    List.filterMap_cons, Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?, Ev.loadAddr?, List.append_assoc]
  trivial

end
end LeanVM.Guest.B1
