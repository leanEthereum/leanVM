module

public import LeanVM.Guest.Complete.DaPad
public import LeanVM.Guest.Complete.StraightA
public import LeanVM.Guest.Complete.LeafA
public import LeanVM.Guest.Complete.PureA
import LeanVM.Guest.Data.ValNames.«da_padding»
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_pad»
import LeanVM.Guest.Data.ValNames.«da_pad_loop0»

/-!
# `da_pad` and `da_padding`, placed

`da_pad(roots, g^r, g^d)` and its loop place nothing (`plainS`): each iteration's frame is the
loop's block from `da_pad`'s cursor, the `d` iterations then the skipped tail's frame
(`padBlock`), and they write the padding root into the slots `r ..< r + d` of `roots` (`padR`).
`padL_callAtA` places iteration `j` at any frame, by `callAtA_straightL` and induction;
`da_pad_callAtA` places `da_pad` at any frame and cursor `c`, ending at the loop's block from
`allocBase (al L) c`. `da_padding` is a straight leaf placing nothing, loading nothing
(`da_padding_callCompletesA`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Prover.Exec (allocBase)
open LeanVM.Guest.B1.VsC LeanVM.Guest.B1.Digest

@[expose] public section

/-- The padding roots' slots, `r ..< r + d`, two cells each, of the roots at index `q`. -/
def padR (q r d : ℕ) (i : ℕ) : Prop := q + 2 * r ≤ i ∧ i < q + 2 * (r + d)

/-- The block of the padding loop's last `m` iterations and its skipped tail. -/
def padBlock (fs : String → ℕ) (m : ℕ) : ℕ := m * fs name% «da_pad_loop0» + fs (tailKey name% «da_pad_loop0»)

theorem padL_loop : coreProgram.loop name% «da_pad_loop0» = true := by decide +kernel
theorem pad_not_loop : coreProgram.loop "da_pad" = false := by decide +kernel

theorem ptrAt_mul_gen_pow (q m : ℕ) : ptrAt q * gen ^ m = ptrAt (q + m) := by
  rw [gen_pow_eq_ofK, ptrAt, ptrAt, ← gpow_add']; exact (map_mul (algebraMap K E) _ _).symm

theorem pops_one_nil {rd : Reader} {σ : Val} {c : Call} {t : Tree}
    (hv : Tree.KidsValid coreProgram rd σ [c] [t]) (hq : KidsPost rd [PopsNil] [c] [t]) :
    t.pops coreProgram rd = [] := by
  rw [Tree.KidsValid] at hv
  rw [kidsPost_cons] at hq
  by_cases ht : c.taken = true
  · exact hq.1 ht
  · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hv
    obtain ⟨-, ⟨⟨f, σ', rfl⟩, -⟩, -⟩ := hv
    rw [Tree.pops]

theorem kidsValid_one {rd : Reader} {σ : Val} {c : Call} {ts : List Tree}
    (hv : Tree.KidsValid coreProgram rd σ [c] ts) : ∃ t, ts = [t] := by
  match ts, hv with
  | [t], _ => exact ⟨t, rfl⟩
  | [], hv => simp [Tree.KidsValid] at hv
  | _ :: _ :: _, hv => simp [Tree.KidsValid] at hv

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxRecDepth 100000 in
theorem padL_step_A (k : ℕ) {q r d : ℕ} (hd : d < 2 ^ 34) {j : ℕ} (hj : j < d) {fp c : ℕ}
    (hfc : fp + padBlock fs (d - j) ≤ c)
    (htail : j + 1 < d → ∀ fp' c', fp' + padBlock fs (d - (j + 1)) ≤ c' →
      CallAtA fs al cert k name% «da_pad_loop0» [gen ^ (j + 1), gen ^ d, ptrAt q, gen ^ r] [] (padR q r d)
        (fun _ => False) (fun _ => True) (PadPre r d (ptrAt q)) PopsNil (padBlock fs (d - (j + 1))) fp' c' c') :
    CallAtA fs al cert k name% «da_pad_loop0» [gen ^ j, gen ^ d, ptrAt q, gen ^ r] [] (padR q r d)
      (fun _ => False) (fun _ => True) (PadPre r d (ptrAt q)) PopsNil (padBlock fs (d - j)) fp c c := by
  set σ := padLσ j d (ptrAt q) (gen ^ r) with hσ
  have hblk : padBlock fs (d - j) = fs name% «da_pad_loop0» + padBlock fs (d - (j + 1)) := by
    obtain ⟨m, hm⟩ : ∃ m, d - j = m + 1 := ⟨d - j - 1, by omega⟩
    rw [padBlock, padBlock, hm, show d - (j + 1) = m by omega, Nat.add_mul, one_mul]; ring
  rw [hblk] at hfc ⊢
  have e12 : σ (.n 12) = gen ^ j * word 2 0 + gen ^ d := rfl
  have hargs : [V.n 14, .n 1, .n 2, .n 3].map σ = [gen ^ (j + 1), gen ^ d, ptrAt q, gen ^ r] := by
    show [gen ^ j * word 2 0, gen ^ d, ptrAt q, gen ^ r] = _; rw [gen_mul_two]
  have hslot : σ (.n 7) = ptrAt (q + 2 * (r + j)) := by
    rw [← ptrAt_mul_gen_pow]; exact pad_slot r j (ptrAt q)
  have hc := daPadBlob_cells
  simp only [Prod.ext_iff] at hc
  have hcalls : (padLPre.filterMap Stmt.callS).map (mkCall σ) =
      [⟨name% «da_pad_loop0», [.n 14, .n 1, .n 2, .n 3], [], decide (σ (.n 12) ≠ 0)⟩] := rfl
  refine callAtA_straightL find_padL padL_body rfl (by decide +kernel) padL_loop hfc σ rfl rfl ?_ [PopsNil]
    (fun rd => HoldsWords rd []) (fun _ => False) ?_ (fun _ _ => trivial) ?_ ?_
  · intro x hx
    simp only [padLPre, List.filterMap_cons, stmtLoad?, List.filterMap_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨q + 2 * (r + j) + 0, by rw [hslot]; exact Main.addr_ofK _ _, by unfold padR; omega⟩
    · exact ⟨q + 2 * (r + j) + 1, by rw [hslot]; exact Main.addr_ofK _ _, by unfold padR; omega⟩
  · rw [hcalls, KidsAtL]
    by_cases hlt : j + 1 < d
    · have htk : decide (σ (.n 12) ≠ 0) = true := by
        rw [e12, loopGuard_taken hd (by omega)]; exact decide_eq_true (by omega)
      simp only [htk, ↓reduceIte]
      refine ⟨padR q r d, fun _ => False, fun _ => True, fun i hi => Or.inl hi, ?_, fun _ h _ => h,
        fun _ h => h.elim⟩
      rw [hargs]
      exact (htail hlt (fp + fs name% «da_pad_loop0») c (by omega)).mono (fun _ h => h) (fun _ h => h)
        (fun _ _ => trivial) (fun _ h => h.1) (fun _ _ _ h => h)
    · have htk : decide (σ (.n 12) ≠ 0) = false := by
        rw [e12, loopGuard_taken hd (by omega)]; exact decide_eq_false (by omega)
      simp only [htk, Bool.false_eq_true, ↓reduceIte]
      have hph : (fn% «da_pad_loop0»).params.map (padLσ (j + 1) d (ptrAt q) (gen ^ r)) =
          [V.n 14, .n 1, .n 2, .n 3].map σ := by rw [padL_params, hargs]; rfl
      refine ⟨⟨padLσ (j + 1) d (ptrAt q) (gen ^ r), fn% «da_pad_loop0», find_padL, hph⟩, ?_, ?_, ?_, ?_⟩
      · rw [show d - (j + 1) = 0 by omega, padBlock]; simp
      · trivial
      · exact fun _ h => h
      · exact fun _ h => h.elim
  · intro rd _ hp _ s hs
    have hR := hp j hj
    simp only [padLPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · show LoadHolds rd (σ (.n 7)) 0 (word 8002054802297438051 4108169256045952147)
      rw [show σ (.n 7) = ptrAt q * gen ^ (2 * (r + j)) from pad_slot r j (ptrAt q), hc.1]
      exact hR 0 (by simp [padCells])
    · exact rfl
    · show LoadHolds rd (σ (.n 7)) 1 (word 12830724869163462953 1721925254677230945)
      rw [show σ (.n 7) = ptrAt q * gen ^ (2 * (r + j)) from pad_slot r j (ptrAt q), hc.2]
      exact hR 1 (by simp [padCells])
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · show IsInK (gen ^ j * word 2 0 + gen ^ d); rw [gen_mul_two]; exact gen_pow_add_isInK _ _
  · intro rd ts _ _ _ hv hq
    rw [hcalls] at hv hq
    obtain ⟨t1, rfl⟩ := kidsValid_one hv
    show _ = _
    rw [pops_straight_none find_padL padL_body rfl rfl (by rw [hcalls]; exact hv), Tree.popsKids, Tree.popsKids,
      pops_one_nil hv hq]
    rfl

/-- **The padding loop completes placed** from iteration `j`, at any frame past its block. -/
theorem padL_callAtA (k : ℕ) {q r d : ℕ} (hd : d < 2 ^ 34) :
    ∀ j < d, ∀ fp c, fp + padBlock fs (d - j) ≤ c →
      CallAtA fs al cert k name% «da_pad_loop0» [gen ^ j, gen ^ d, ptrAt q, gen ^ r] [] (padR q r d)
        (fun _ => False) (fun _ => True) (PadPre r d (ptrAt q)) PopsNil (padBlock fs (d - j)) fp c c := by
  have key : ∀ t j, j + 1 + t = d → ∀ fp c, fp + padBlock fs (d - j) ≤ c →
      CallAtA fs al cert k name% «da_pad_loop0» [gen ^ j, gen ^ d, ptrAt q, gen ^ r] [] (padR q r d)
        (fun _ => False) (fun _ => True) (PadPre r d (ptrAt q)) PopsNil (padBlock fs (d - j)) fp c c := by
    intro t
    induction t with
    | zero => intro j hj fp c hfc; exact padL_step_A k hd (by omega) hfc fun h' => absurd h' (by omega)
    | succ t ih => intro j hj fp c hfc; exact padL_step_A k hd (by omega) hfc fun _ => ih (j + 1) (by omega)
  intro j hj
  exact key (d - j - 1) j (by omega)

set_option maxRecDepth 100000 in
/-- **`da_pad` completes placed** at any frame and cursor `c`, writing the padding roots' slots of
the roots at index `q`: its loop entered fresh from `c`, ending after the loop's block. -/
theorem da_pad_callAtA (k : ℕ) {q r d : ℕ} (hd : d < 2 ^ 34) {fp c : ℕ} (hfc : fp + fs "da_pad" ≤ c) :
    CallAtA fs al cert k "da_pad" [ptrAt q, gen ^ r, gen ^ d] [] (padR q r d) (fun _ => False) (fun _ => True)
      (PadPre r d (ptrAt q)) PopsNil (fs "da_pad") fp c
      (allocBase (al name% «da_pad_loop0») c + padBlock fs d) := by
  set σ : Val := fun v => [ptrAt q, gen ^ r, gen ^ d, word 1 0, word 1 0 + gen ^ d, word 1 0].getD v.idx 0 with hσ
  have hargs : [V.n 5, .n 2, .n 0, .n 1].map σ = [gen ^ 0, gen ^ d, ptrAt q, gen ^ r] := by
    show [word 1 0, gen ^ d, ptrAt q, gen ^ r] = _; rw [word_one, pow_zero]
  have hcalls : (padPre.filterMap Stmt.callS).map (mkCall σ) =
      [⟨name% «da_pad_loop0», [.n 5, .n 2, .n 0, .n 1], [], decide (σ (.n 4) ≠ 0)⟩] := rfl
  refine callAtA_straight find_pad pad_body rfl (by decide +kernel) pad_not_loop hfc σ rfl rfl ?_ [PopsNil]
    (fun rd => HoldsWords rd []) (fun _ => False) ?_ (fun _ _ => trivial) ?_ ?_
  · intro x hx; simp [padPre, stmtLoad?] at hx
  · rw [hcalls, KidsAtF]
    by_cases h0 : d = 0
    · have htk : decide (σ (.n 4) ≠ 0) = false := by
        show decide (word 1 0 + gen ^ d ≠ 0) = false; rw [one_add_gen_pow_ne hd]; exact decide_eq_false (by omega)
      simp only [htk, Bool.false_eq_true, ↓reduceIte]
      have hph : (fn% «da_pad_loop0»).params.map (padLσ 0 d (ptrAt q) (gen ^ r)) =
          [V.n 5, .n 2, .n 0, .n 1].map σ := by rw [padL_params, hargs]; rfl
      refine ⟨⟨padLσ 0 d (ptrAt q) (gen ^ r), fn% «da_pad_loop0», find_padL, hph⟩, ?_⟩
      · rw [KidsAtF]
        exact ⟨by rw [padBlock, h0]; simp, fun _ h => h, fun _ h => h.elim⟩
    · have htk : decide (σ (.n 4) ≠ 0) = true := by
        show decide (word 1 0 + gen ^ d ≠ 0) = true; rw [one_add_gen_pow_ne hd]; exact decide_eq_true h0
      simp only [htk, ↓reduceIte]
      refine ⟨padBlock fs d, allocBase (al name% «da_pad_loop0») c + padBlock fs d, padR q r d, fun _ => False,
        fun _ => True, fun i hi => Or.inl hi, ?_, ?_⟩
      · rw [hargs]
        have h := padL_callAtA (fs := fs) (al := al) (cert := cert) k (q := q) (r := r) hd 0 (by omega)
          (allocBase (al name% «da_pad_loop0») c) (allocBase (al name% «da_pad_loop0») c + padBlock fs d)
          (by simp)
        simp only [Nat.sub_zero] at h
        exact h.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h.1) (fun _ _ _ h => h)
      · rw [KidsAtF]
        exact ⟨rfl, fun _ h => h.1, fun _ h => h.elim⟩
  · intro rd _ _ _ s hs
    simp only [padPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · show IsInK (word 1 0 + gen ^ d); rw [word_one, ← pow_zero gen]; exact gen_pow_add_isInK _ _
  · intro rd ts _ _ _ hv hq
    rw [hcalls] at hv hq
    obtain ⟨t1, rfl⟩ := kidsValid_one hv
    show _ = _
    rw [pops_straight_none find_pad pad_body rfl rfl (by rw [hcalls]; exact hv), Tree.popsKids, Tree.popsKids,
      pops_one_nil hv hq]
    rfl

/-- **A straight leaf placing nothing and loading nothing** loads and hints only in any region. -/
theorem loadsR_hintsR_of_leafPlain {f : String} {fn : Fn} {args rets : List E} {rd : Reader} {t : Tree}
    (R : ℕ → Prop) (hfind : coreProgram.find? f = some fn)
    (hP : (atomsOf fn.body).all (fun a => plainS (.atom a) && (atomLoad? a).isNone) = true)
    (hr : (retOf fn.body).isSome = true) (hn : t.name = f) (hv : t.Valid coreProgram rd args rets) :
    t.LoadsR coreProgram R ∧ t.HintsR coreProgram R := by
  obtain ⟨vs0, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
    obtain ⟨fn', hfn, _, es, vs, hw, _, _, hk⟩ := hv
    simp only [Tree.name] at hn
    subst hn
    rw [hfind] at hfn
    cases hfn
    have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
    have hw' : walk σ fn.body = .ret ((atomsOf ss).map Ev.atom) vs0 := by rw [hb']; exact walk_atoms _ _ _
    rw [hw'] at hw
    cases hw
    have hev : (Memory.Tree.node g σ bufs kids).events coreProgram = (atomsOf ss).map Ev.atom := by
      simp only [Tree.events, Tree.name, Tree.val, hfind, hw']
    rw [calls_atoms] at hk
    have hkids : kids = [] := by
      cases kids with
      | nil => rfl
      | cons _ _ => simp [Tree.KidsValid] at hk
    subst hkids
    have hok : ∀ a ∈ atomsOf ss, (plainS (.atom a) && (atomLoad? a).isNone) = true := fun a ha =>
      List.all_eq_true.mp hP a (mem_atomsOf' (by rw [hbody]; exact List.mem_append_left _ (mem_of_mem_atomsOf ha)))
    refine ⟨?_, ?_⟩
    · rw [Tree.LoadsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.LoadsRKids]; trivial⟩
      rw [loadAddrs_atoms] at hA
      obtain ⟨q, hq, -⟩ := List.mem_map.mp hA
      obtain ⟨a, ha, hqa⟩ := List.mem_filterMap.mp hq
      have := hok a ha
      simp [hqa] at this
    · rw [Tree.HintsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.HintsRKids]; trivial⟩
      simp only [heapHintAddrs, List.flatMap_map, List.mem_flatMap] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have := hok a ha
      cases a with
      | hint h => cases h <;> simp_all [plainS, Ev.hintAddrs, hintDest?, Option.isNone_iff_eq_none]
      | _ => simp [Ev.hintAddrs] at hA

set_option maxRecDepth 100000 in
theorem find_da_padding : coreProgram.find? "da_padding" = some fn% «da_padding» :=
  coreProgram_find?_at (j := idx% «da_padding») rfl

theorem da_padding_pureIn : coreProgram.PureIn ["da_padding"] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [find_da_padding] at hf
  obtain rfl := Option.some.inj hf
  decide +kernel

theorem da_padding_not_loop : coreProgram.loop "da_padding" = false := by decide +kernel

/-- **`da_padding` completes placed** at every position, on `r` rows within the cap: block its frame,
ending at its cursor, loading nothing, popping nothing, every node exact. -/
theorem da_padding_callAtA (hwf : coreProgram.Wf) {k : ℕ} (hk : 16 ≤ k) {r : ℕ} (h1 : 1 ≤ r)
    (h2 : r ≤ LeanDa.maxRows) (R : ℕ → Prop) (fp c : ℕ) :
    CallAtA fs al cert k "da_padding" [gen ^ r] [gen ^ (LeanDa.maxRows - r)] R
      (fun _ => False) (fun _ => True) (fun _ => True) FreePost (fs "da_padding") fp c c := by
  refine callAtA_of_callCompletes0_leaf da_padding_pureIn List.mem_cons_self da_padding_not_loop ?_
    (callCompletes0_free hwf da_padding_free.1 da_padding_free.2 fun rd hl _ =>
      da_padding_complete rd (hl.mono hk) r h1 h2) ?_ fp c
  · intro fn σ es vs hf hw
    rw [find_da_padding] at hf
    obtain rfl := Option.some.inj hf
    obtain ⟨vs0, hr⟩ := Option.isSome_iff_exists.mp (by decide +kernel : (retOf (fn% «da_padding»).body).isSome = true)
    obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
    have hb' : (fn% «da_padding»).body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by
      rw [hbody, ← eq_map_atomsOf hss]
    rw [hb', walk_atoms] at hw
    cases hw
    exact calls_atoms _
  · intro rd t _ _ hn hv _ _
    exact loadsR_hintsR_of_leafPlain _ find_da_padding (by decide +kernel) (by decide +kernel) hn hv

theorem da_padding_callCompletesA (hwf : coreProgram.Wf) {k : ℕ} (hk : 16 ≤ k) {r : ℕ} (h1 : 1 ≤ r)
    (h2 : r ≤ LeanDa.maxRows) (R : ℕ → Prop) :
    CallCompletesA fs al cert k "da_padding" [gen ^ r] [gen ^ (LeanDa.maxRows - r)] R
      (fun _ _ _ => False) (fun _ => True) (fun _ => True) FreePost :=
  ⟨fs "da_padding", fun fp c _ => ⟨c, da_padding_callAtA hwf hk h1 h2 R fp c⟩⟩

end
end LeanVM.Guest.Complete
