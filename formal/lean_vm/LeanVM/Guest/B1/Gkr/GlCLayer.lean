/-
  LeanVM.Guest.B1.Gkr.GlCLayer

  `gkr_layer__L{p}_L{o}` is complete: from the slot of `L = 2j + 2 - o` (`j = 4m + p`), one step
  of two levels, its words, its round records and the next slot, the layer holds.
-/

module

public import LeanVM.Guest.B1.Gkr.GlCLayerK
public import LeanVM.Guest.B1.Gkr.GlCSt
public import LeanVM.Guest.B1.Gkr.RecsC
public import LeanVM.Guest.B1.Gkr.SpecInv
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L0_L0»

/-!
# A radix-four layer, completely

`glc_layer`: from the slot of `L = 2j + 2 - o` (`GkSlot`, its point in row `j + 1`), a step of two
levels (`GkStepD.Ok`) with its words at the cursor, the round records `rounds·pos·g^y`, `y ≤ m`,
after `2p + 8y` rounds (`RecAt`), at an odd depth the row's zero cell after the point, and the
slot of `L + 2` (position `pos·g^(m + 1)`), `gkr_layer__L{p}_L{o}` holds at `x_m = g^m`,
`x_j = g^j`, `start_g = g^(2 - o)`. Its body is evaluated forward (`ev`) and holds piece by piece
(`glc_pre`, `glc_rounds`, `glc_hstore`, `glc_lcall`, `glc_tsetup`, `glc_rounds`, `glc_pad`); its
tail, renamed by `glRho p o`, holds at `σ ∘ glRho p o` in the canonical numbering
(`glct_kids`, `glct_check`, `glct_y`, `glct_next`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Fwd

@[expose] public section

theorem glKids_load {off : ℕ} {d q : V} {o' : ℕ} (h : Stmt.atom (.load d q o') ∈ glKids off) :
    ∃ i < 12, d = .n (chB (val% «gkr_layer__L0_L0» "x@9") i) ∧ q = .n (val% «gkr_layer__L0_L0» "tcur") ∧ o' = off + i := by
  have hc : ∀ i, Stmt.atom (.load d q o') ∈ chT (.n (val% «gkr_layer__L0_L0» "tcur")) off (val% «gkr_layer__L0_L0» "x@9") i →
      d = .n (chB (val% «gkr_layer__L0_L0» "x@9") i) ∧ q = .n (val% «gkr_layer__L0_L0» "tcur") ∧ o' = off + i := fun i hi ↦ by
    simp only [chT, fsNextT, fsPackT, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, Stmt.atom.injEq, reduceCtorEq] at hi
    simp only [Atom.load.injEq] at hi
    exact ⟨hi.1, hi.2.1, hi.2.2⟩
  unfold glKids at h
  simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq, reduceCtorEq] at h
  rcases h with ((⟨_, ⟨i, hi, rfl⟩, hs⟩ | ⟨_, ⟨i, hi, rfl⟩, hs⟩) | ⟨_, ⟨i, hi, rfl⟩, hs⟩)
  · exact ⟨i, by omega, hc i hs⟩
  · exact ⟨4 + i, by omega, hc _ hs⟩
  · exact ⟨8 + i, by omega, hc _ hs⟩

theorem glc_take_range {α : Type} (f : ℕ → α) {a L : ℕ} (h : a ≤ L) :
    ((List.range L).map f).take a = (List.range a).map f := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem glcRho_lo (p o k : ℕ) (hk : k < 58) : glRho p o (.n k) = .n k := by
  simp [glRho, hk]

theorem glcRho_mid (p o k : ℕ) (h1 : 58 ≤ k) (h2 : k < 121) : glRho p o (.n k) = .n (k + glD p) := by
  simp [glRho, show ¬ k < 58 by omega, h2]

theorem glcRho_hi (p o k : ℕ) (h1 : 121 ≤ k) (h2 : k < 160) :
    glRho p o (.n k) = .n (k + glD p - 39 * o) := by
  simp [glRho, show ¬ k < 58 by omega, show ¬ k < 121 by omega, h2]


theorem glc_squeezeN_two (s : Fs) : s.squeezeN 2 =
    ([challengeOf s.perm, challengeOf (permOf (rateOf [] ++ capOf s.perm))],
      ⟨capOf (permOf (rateOf [] ++ capOf s.perm)), []⟩) := rfl

theorem glcRoundKeys_mem {B cur pt n q : ℕ} (hq : q < n) :
    (B + 39 * q, cur, 4 * q) ∈ glcRoundKeys B cur pt n ∧
      (B + 39 * q + 3, cur, 4 * q + 1) ∈ glcRoundKeys B cur pt n ∧
      (B + 39 * q + 6, cur, 4 * q + 2) ∈ glcRoundKeys B cur pt n ∧
      (B + 39 * q + 9, cur, 4 * q + 3) ∈ glcRoundKeys B cur pt n ∧
      (B + 39 * q + 25, pt, q) ∈ glcRoundKeys B cur pt n := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [glcRoundKeys, List.mem_flatMap, List.mem_range] <;>
    exact ⟨q, hq, by simp⟩

theorem glc_chw {τ : Val} {ch0 ch1 ch2 : List E} (h0 : ch0.length = 4) (h1 : ch1.length = 4)
    (h2 : ch2.length = 4) (hv : ∀ i < 12, τ (.n (chB (val% «gkr_layer__L0_L0» "x@9") i)) = (ch0 ++ (ch1 ++ ch2)).getD i 0) :
    chWords τ (val% «gkr_layer__L0_L0» "x@9") 0 = ch0 ∧ chWords τ (val% «gkr_layer__L0_L0» "x@9") 1 = ch1 ∧ chWords τ (val% «gkr_layer__L0_L0» "x@9") 2 = ch2 := by
  rw [list4_eq h0, list4_eq h1, list4_eq h2] at hv ⊢
  refine ⟨?_, ?_, ?_⟩ <;> rw [chWords_eq] <;>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, show 4 * 2 = 8 by rfl] <;>
    rw [hv _ (by norm_num), hv _ (by norm_num), hv _ (by norm_num), hv _ (by norm_num)] <;> rfl

theorem glRounds_head (p : ℕ) : glHeadRounds p =
    glRounds 58 (2 * p) (.n (valf% «gkr_layer» "s4#0")) (.n (valf% «gkr_layer» "point_row")) (.n (valf% «gkr_layer» "point_row")) 42 (.n (valf% «gkr_layer» "claim@2")) (glCap (valf% «gkr_layer» "nxt[8]@1")) := rfl

theorem glBodyA_noRet (p o : ℕ) (nm : String) :
    Stmt.noRetList glPre = true ∧ Stmt.noRetList (glHeadRounds p) = true ∧
      Stmt.noRetList (glHeadStore p) = true ∧ Stmt.noRetList (glLoopCall p nm) = true ∧
      Stmt.noRetList (glTailSetup p) = true ∧ Stmt.noRetList (glTailRounds p o) = true ∧
      Stmt.noRetList (glPad p o) = true := by
  refine ⟨by decide, glcRounds_noRet _ _ _ _ _ _ _ _, ?_, ?_, ?_, glcRounds_noRet _ _ _ _ _ _ _ _, ?_⟩
  · unfold glHeadStore; split <;> rfl
  · unfold glLoopCall; split <;> rfl
  · unfold glTailSetup; split <;> rfl
  · unfold glPad; split <;> rfl

theorem glTail_noRet (o : ℕ) :
    Stmt.noRetList (glKids (4 * (2 - o))) = true ∧ Stmt.noRetList glCheck = true ∧
      Stmt.noRetList glY = true ∧ Stmt.noRetList (glNext (4 * (2 - o) + 12)) = true := by
  refine ⟨?_, by decide, by decide, rfl⟩
  have := glKids_atoms (4 * (2 - o))
  generalize glKids (4 * (2 - o)) = l at this ⊢
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨a, rfl⟩ := this x List.mem_cons_self
    exact ih fun s hs ↦ this s (List.mem_cons_of_mem _ hs)

section Layer

variable {rd : Reader}

/-- The rounds' words and factors as functions. -/
def glcCf (cs : List (List E)) (q : ℕ) : List E :=
  [(cs.getD q []).getD 0 0, (cs.getD q []).getD 1 0, (cs.getD q []).getD 2 0, (cs.getD q []).getD 3 0]

theorem glcCf_eq {cs : List (List E)} (h4 : ∀ c ∈ cs, c.length = 4) :
    cs = (List.range cs.length).map (glcCf cs) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, glcCf, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, Option.getD_some]
  exact list4_eq (h4 _ (List.getElem_mem h1))

theorem glcEf_eq (es : List E) : es = (List.range es.length).map (fun q ↦ es.getD q 0) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- **A radix-four layer, completely.** -/
theorem glc_layer {p o m : ℕ} (hp : p < 4) (ho : o < 2) (hm : m < 2 ^ 26)
    {layers rounds pts gmu tabs stream : E} {s : Fs} {cur : E} {st : GkrState} {pos : E}
    {D : GkStepD}
    (hS : GkSlot rd layers (2 * (4 * m + p) + 2 - o) s cur st
      (pts * gen ^ (40 * (4 * m + p + 1))) pos)
    (hD : D.Ok s st 2) (hx : TbReadsAt rd cur D.xs)
    (hR : ∀ y ≤ m, RecAt rd (rounds * pos * gen ^ (7 * y)) cur D.cs st.point
      (polyEval st.values s.squeeze.1) s.squeeze.2 (2 * p + 8 * y))
    (hpad : o = 1 → LoadHolds rd (pts * gen ^ (40 * (4 * m + p + 1))) (2 * (4 * m + p) + 43) 0)
    (hS' : GkSlot rd layers (2 * (4 * m + p) + 2 - o + 2) (D.s' s st 2) (cur * gen ^ D.xs.length)
      (D.st' s st 2) (pts * gen ^ (40 * (4 * m + p + 2))) (pos * gen ^ (7 * (m + 1)))) :
    coreProgram.Rel rd (glName p o) [layers, rounds, pts, gen ^ m, gen ^ (4 * m + p), gen ^ (2 - o),
      gmu, tabs, stream] [] := by
  set j := 4 * m + p with hj
  set L := 2 * j + 2 - o with hL
  set row := pts * gen ^ (40 * (j + 1)) with hrow
  set a := 2 * p + 8 * m with ha
  have haL : a + (2 - o) = L := by omega
  obtain ⟨fn, hf, hpar, hb⟩ := glIs_sound (glIs_layers p hp o ho)
  set args : List E := [layers, rounds, pts, gen ^ m, gen ^ j, gen ^ (2 - o), gmu, tabs, stream]
    with hargs
  obtain ⟨hchk, -⟩ := glc_layer_check p hp o ho
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hchk
  have hc9 : chk args.length (glcL p o) = some c' := hc'
  set σ : Val := B1.Val.ofArgs (ev rd (fun _ => 0) args (glcL p o)) with hσ
  set S := storesOf 9 (glcL p o) with hSd
  have hG : ∀ s ∈ glcL p o, GoodS rd S (fun _ => 0) σ s := (ev_spec rd _ (glcL p o) args hc9).2.2
  have par : ∀ i < (valf% «gkr_layer» "x_layer~0"), σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd _ hc9 (by simpa [hargs] using hi)
  have e0 : σ (.n (valf% «gkr_layer» "layers")) = layers := par 0 (by omega)
  have e1 : σ (.n (valf% «gkr_layer» "rounds")) = rounds := par 1 (by omega)
  have e2 : σ (.n (valf% «gkr_layer» "gkr_pts")) = pts := par 2 (by omega)
  have e3 : σ (.n (valf% «gkr_layer» "x_m")) = gen ^ m := par 3 (by omega)
  have e4 : σ (.n (valf% «gkr_layer» "x_j")) = gen ^ j := par 4 (by omega)
  have e5 : σ (.n (valf% «gkr_layer» "start_g")) = gen ^ (2 - o) := par 5 (by omega)
  have hfr := glc_fresh hp ho
  -- the pieces' equations
  have mem : ∀ {X : List Stmt}, (∀ s ∈ X, s ∈ glcL p o) → ∀ s ∈ X, GoodS rd S (fun _ => 0) σ s :=
    fun hX s hs ↦ hG s (hX s hs)
  have mPre : ∀ s ∈ glPre, s ∈ glcL p o := fun s hs ↦ by
    simp only [glcL, glBody, List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inl hs))))))
  have mHR : ∀ s ∈ glHeadRounds p, s ∈ glcL p o := fun s hs ↦ by
    simp only [glcL, glBody, List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inr hs))))))
  have mHS : ∀ s ∈ glHeadStore p, s ∈ glcL p o := fun s hs ↦ by
    simp only [glcL, glBody, List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inr hs)))))
  have mLC : ∀ s ∈ glLoopCall p (glLoopName p o), s ∈ glcL p o := fun s hs ↦ by
    simp only [glcL, glBody, List.mem_append]; exact .inl (.inl (.inl (.inl (.inr hs))))
  have mTS : ∀ s ∈ glTailSetup p, s ∈ glcL p o := fun s hs ↦ by
    simp only [glcL, glBody, List.mem_append]; exact .inl (.inl (.inl (.inr hs)))
  have mTR : ∀ s ∈ glTailRounds p o, s ∈ glcL p o := fun s hs ↦ by
    simp only [glcL, glBody, List.mem_append]; exact .inl (.inl (.inr hs))
  have mPD : ∀ s ∈ glPad p o, s ∈ glcL p o := fun s hs ↦ by
    simp only [glcL, glBody, List.mem_append]; exact .inl (.inr hs)
  have mT : ∀ s ∈ glTail o, s.rename (glRho p o) ∈ glcL p o := fun s hs ↦ by
    simp only [glcL, glBody, List.mem_append]; exact .inr (mem_renameList_of hs)
  have fk : ∀ k ∈ glcFresh p o, some k ∉ S.map loadKey := hfr
  -- the step's data
  have hS0 := hS
  obtain ⟨hcl, -, hpe, -, hvl, -, hpl, hpt, -⟩ := hS
  obtain ⟨hl, h4, hl0, hl1, hl2, hcheck⟩ := hD
  have hcsL : D.cs.length = L := hl.trans hpl
  set Cf := glcCf D.cs with hCf
  set ef : ℕ → E := fun q ↦ st.point.getD q 0 with hef
  have h4' : ∀ q, (Cf q).length = 4 := fun _ ↦ rfl
  have hcs : D.cs = (List.range L).map Cf := by rw [← hcsL]; exact glcCf_eq h4
  have hes : st.point = (List.range L).map ef := by rw [← hpl]; exact glcEf_eq _
  set claim0 := polyEval st.values s.squeeze.1 with hclaim0
  set cap0 := s.squeeze.2.cap with hcap0
  have hs0 : s.squeeze.2 = ⟨cap0, []⟩ := rfl
  set St := gkSt Cf ef claim0 ⟨cap0, []⟩ with hSt
  have hrun : D.run s st = gkrRun ((List.range L).map Cf) ((List.range L).map ef) claim0
      ⟨cap0, []⟩ := by rw [GkStepD.run, hcs, hes, hs0]
  have hrun1 : (D.run s st).1 = (List.range L).map fun q ↦ challengeOf (gkP Cf ef claim0 ⟨cap0, []⟩ q) := by
    rw [hrun, gkrRun_range1]
  have hrun2 : (D.run s st).2 = St L := by rw [hrun, gkrRun_range2]
  -- the records
  have REC : ∀ y ≤ m, GlRecK rd (rounds * pos * gen ^ (7 * y)) cur Cf ef claim0 ⟨cap0, []⟩ (2 * p + 8 * y) := by
    intro y hy
    obtain ⟨r1, r2, r3⟩ := hR y hy
    have ht : ∀ {α : Type} (f : ℕ → α), ((List.range L).map f).take (2 * p + 8 * y) =
        (List.range (2 * p + 8 * y)).map f := fun f ↦ glc_take_range f (by omega)
    rw [hcs, hes, ht, ht, hs0, gkrRun_range2] at r1 r3
    exact ⟨r1, r2, r3⟩
  -- the words, the factors, the challenges
  have hxs := tbReadsAt_append.mp hx
  have hw : ∀ q < L, ∀ i < 4, LoadHolds rd cur (4 * q + i) ((Cf q).getD i 0) := by
    intro q hq i hi
    have hflat := hxs.1
    rw [hcs] at hflat
    have hk : 4 * q + i < ((List.range L).map Cf).flatten.length := by
      rw [flatten4_length Cf h4']; omega
    have := hflat _ hk
    rwa [show ((List.range L).map Cf).flatten[4 * q + i] =
        ((List.range L).map Cf).flatten.getD (4 * q + i) 0 by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk],
      flatten4_get Cf h4' L q i hq hi] at this
  have he : ∀ q < L, LoadHolds rd row q (ef q) := by
    intro q hq
    have := hpt q (by omega)
    rwa [← List.getD_eq_getElem _ 0] at this
  obtain ⟨-, hcap', -, hcur', -, hval', -, hpt', hpos'⟩ := hS'
  have hpt2 := tbReadsAt_append.mp hpt'
  have hysl : (D.ys s st 2).length = 2 := rfl
  have hch : ∀ q < L, LoadHolds rd (row * gen ^ 42) q (challengeOf (gkP Cf ef claim0 ⟨cap0, []⟩ q)) := by
    intro q hq
    have h := hpt2.2 q (by rw [hrun1]; simp; omega)
    rw [hysl, show pts * gen ^ (40 * (j + 2)) * gen ^ 2 = row * gen ^ 42 by rw [hrow]; ring] at h
    simpa [hrun1] using h

  -- the prefix
  have fPre : ∀ k ∈ glPreKeys, some k ∉ S.map loadKey := fun k hk ↦ fk k (by
    simp only [glcFresh, List.mem_append]; exact .inl (.inl (.inl (.inl hk))))
  have fHR : ∀ k ∈ glcRoundKeys 58 21 52 (2 * p), some k ∉ S.map loadKey := fun k hk ↦ fk k (by
    simp only [glcFresh, List.mem_append]; exact .inl (.inl (.inl (.inr hk))))
  have fTS : ∀ k ∈ glTailKeys p, some k ∉ S.map loadKey := fun k hk ↦ fk k (by
    simp only [glcFresh, List.mem_append]; exact .inl (.inl (.inr hk)))
  have fTR : ∀ k ∈ glcRoundKeys (82 + glD p) (80 + glD p) (71 + glD p) (2 - o),
      some k ∉ S.map loadKey := fun k hk ↦ fk k (by
    simp only [glcFresh, List.mem_append]; exact .inl (.inr hk))
  have fK : ∀ k ∈ glcKidKeys p o, some k ∉ S.map loadKey := fun k hk ↦ fk k (by
    simp only [glcFresh, List.mem_append]; exact .inr hk)
  obtain ⟨R1, e15, e21, e40, hcap35, e44, e53, e54, e58, z23, z24, z25, z26⟩ :=
    glc_pre (C := coreProgram.Rel rd) (kret := fun rs => rs = []) (mem mPre) fPre ho e0 e1 e2 e4 e5
      hS0
  -- the head rounds
  have HR := glc_rounds (C := coreProgram.Rel rd) (kret := fun rs => rs = []) (rd := rd) (S := S)
    (w := fun _ => 0) (σ := σ) (B := 58) (cur := 21) (pt := 52) (npt := 52) (noff := 42)
    (claimV := .n (valf% «gkr_layer» "claim@2")) (cap := glCap (val% «gkr_layer__L0_L0» "nxt[8]@1")) (by simp [glCap]) (Cf := Cf) (ef := ef) h4' (2 * p)
    (fun s hs ↦ mem mHR s (by rw [glRounds_head]; exact hs))
    (fun q hq ↦ by
      obtain ⟨k0, k1, k2, k3, k4⟩ := glcRoundKeys_mem (B := 58) (cur := 21) (pt := 52) hq
      exact ⟨fHR _ k0, fHR _ k1, fHR _ k2, fHR _ k3, fHR _ k4⟩)
    (fun q hq i hi ↦ by rw [e21]; exact hw q (by omega) i hi)
    (fun q hq ↦ by rw [e53]; exact he q (by omega))
    (fun q hq ↦ by
      rw [e53, e58, hcap35, ← tb_loadHolds_mul_gen_pow]; exact hch q (by omega))
  rw [e58, hcap35] at HR
  obtain ⟨R2, hHR⟩ := HR
  -- the head record
  have R3 := glc_hstore (C := coreProgram.Rel rd) (kret := fun rs => rs = []) hp (mem mHS) e21 e54
    (cap := (St (2 * p)).2.cap) (claim := (St (2 * p)).1)
    (by
      by_cases h0 : p = 0
      · simp only [h0, ↓reduceIte, Nat.mul_zero]; exact hcap35
      · simp only [h0, ↓reduceIte]
        rw [show 39 + 78 * p = 58 + 39 * (2 * p) - 19 by omega]
        exact (hHR (2 * p) (by omega) le_rfl).2)
    (by
      by_cases h0 : p = 0
      · simp only [h0, ↓reduceIte, Nat.mul_zero]; exact e58
      · simp only [h0, ↓reduceIte]
        rw [show 57 + 78 * p = 58 + 39 * (2 * p) - 1 by omega]
        exact (hHR (2 * p) (by omega) le_rfl).1)
    (by have := (REC 0 (by omega)).1; simpa using this)
    (by have := (REC 0 (by omega)).2.1; simpa [show 4 * (2 * p) = 8 * p by ring] using this)
    (by have := (REC 0 (by omega)).2.2; simpa using this)
  -- the loop
  have R4 := glc_lcall (kret := fun rs => rs = []) hp (mem mLC) e3 e53
    (fun hm0 ↦ glc_complete (rd := rd) hp ho (head := σ (.n (valf% «gkr_layer» "head"))) (qrow := row * gen ^ (2 * p))
      (tabs := σ (.n (valf% «gkr_layer» "tabs"))) rfl hm0 (by omega) (fun y hy ↦ by
        have r0 := REC y (by omega)
        have r1 := REC (y + 1) (by omega)
        rw [← e54] at r0 r1
        rw [show 2 * p + 8 * (y + 1) = 2 * p + 8 * y + 8 by ring, show 7 * (y + 1) = 7 * y + 7 * 1 by ring,
          pow_add, ← mul_assoc] at r1
        refine glc_tb (a := 2 * p + 8 * y) (n := 8) (t := 1) h4' r0.1 r0.2.1 r0.2.2
          (by simpa using r1.1) (by simpa using r1.2.1) (by simpa using r1.2.2)
          (fun q hq i hi ↦ ?_) (fun q hq ↦ ?_) (fun q hq ↦ ?_)
        · rw [tb_loadHolds_mul_gen_pow, show 4 * (2 * p + 8 * y) + (4 * q + i) =
            4 * (2 * p + 8 * y + q) + i by ring]
          exact hw _ (by omega) i hi
        · rw [show row * gen ^ (2 * p) * gen ^ (8 * y) = row * gen ^ (2 * p + 8 * y) by ring,
            tb_loadHolds_mul_gen_pow]
          exact he _ (by omega)
        · rw [show row * gen ^ (2 * p) * gen ^ (8 * y) * gen ^ 42 =
            row * gen ^ 42 * gen ^ (2 * p + 8 * y) by ring, tb_loadHolds_mul_gen_pow]
          exact hch _ (by omega)))
  -- the last record and the tail's rows
  obtain ⟨R5, e68, e71, ecap72, e77, e78⟩ := glc_tsetup (C := coreProgram.Rel rd)
    (kret := fun rs => rs = []) hp (mem mTS) fTS e54 e3 e53 (REC m le_rfl)
  rw [← ha] at ecap72 e77 e78
  have hSa : (⟨(St a).2.cap, []⟩ : Fs) = (St a).2 := (gkSt_empty Cf ef claim0 cap0 a).symm
  have hshift : ∀ q, gkSt (fun i ↦ Cf (a + i)) (fun i ↦ ef (a + i)) (St a).1 ⟨(St a).2.cap, []⟩ q =
      St (a + q) := fun q ↦ by rw [hSa]; exact (gkSt_addN Cf ef claim0 ⟨cap0, []⟩ a q).symm
  have TR := glc_rounds (C := coreProgram.Rel rd) (kret := fun rs => rs = []) (rd := rd) (S := S)
    (w := fun _ => 0) (σ := σ) (B := 82 + glD p) (cur := 80 + glD p) (pt := 71 + glD p)
    (npt := 74 + glD p) (noff := 0) (claimV := .n (81 + glD p)) (cap := glCap (75 + glD p))
    (by simp [glCap]) (Cf := fun i ↦ Cf (a + i)) (ef := fun i ↦ ef (a + i)) (fun _ ↦ h4' _) (2 - o)
    (mem mTR)
    (fun q hq ↦ by
      obtain ⟨k0, k1, k2, k3, k4⟩ := glcRoundKeys_mem (B := 82 + glD p) (cur := 80 + glD p)
        (pt := 71 + glD p) hq
      exact ⟨fTR _ k0, fTR _ k1, fTR _ k2, fTR _ k3, fTR _ k4⟩)
    (fun q hq i hi ↦ by
      rw [e77, tb_loadHolds_mul_gen_pow, show 4 * a + (4 * q + i) = 4 * (a + q) + i by ring]
      exact hw _ (by omega) i hi)
    (fun q hq ↦ by
      rw [e68, mul_assoc, ← pow_add, ← ha, tb_loadHolds_mul_gen_pow]
      exact he _ (by omega))
    (fun q hq ↦ by
      rw [e71, e78, ecap72, hSa, hSt, ← gkP_addN, show row * gen ^ (2 * p) * gen ^ 42 * gen ^ (8 * m) =
        row * gen ^ 42 * gen ^ a by rw [ha]; ring, tb_loadHolds_mul_gen_pow, Nat.zero_add]
      exact hch _ (by omega))
  rw [e78, ecap72] at TR
  obtain ⟨R6, hTR⟩ := TR
  have hTRL := hTR (2 - o) (by omega) le_rfl
  rw [hshift, haL] at hTRL
  -- the pad
  have R7 := glc_pad (C := coreProgram.Rel rd) (kret := fun rs => rs = []) (mem mPD) (fun h1 ↦ by
    rw [e71, show row * gen ^ (2 * p) * gen ^ 42 * gen ^ (8 * m) = row * gen ^ (42 + 2 * j) by
      rw [hj]; ring, tb_loadHolds_mul_gen_pow,
      show 42 + 2 * j + 1 = 2 * (4 * m + p) + 43 by omega]
    exact hpad h1)
  -- the tail, canonically numbered
  set τ : Val := σ ∘ glRho p o with hτ
  have tlo : ∀ k, k < 58 → τ (.n k) = σ (.n k) := fun k hk ↦ by
    simp only [hτ, Function.comp_apply, glcRho_lo p o k hk]
  have t77 : τ (.n (val% «gkr_layer__L0_L0» "tcur")) = cur * gen ^ (4 * a) := by
    simp only [hτ, Function.comp_apply, glcRho_mid p o 80 (by omega) (by omega), Nat.add_comm 80]
    rw [Nat.add_comm]; exact e77
  have t158 : τ (.n (val% «gkr_layer__L0_L0» "nclaim@2")) = (St L).1 := by
    simp only [hτ, Function.comp_apply, glcRho_hi p o 159 (by omega) (by omega)]
    rw [← hTRL.1, show 159 + glD p - 39 * o = 82 + glD p + 39 * (2 - o) - 1 by omega]
  have tcap : (glCap (val% «gkr_layer__L0_L0» "nxt[8]@3")).map τ = (St L).2.cap := by
    rw [← hTRL.2]
    simp only [glCap, List.map_map]
    refine List.map_congr_left fun k hk ↦ ?_
    have hk5 := List.mem_range.mp hk
    simp only [hτ, Function.comp_apply, glcRho_hi p o (141 + k) (by omega) (by omega)]
    rw [show 141 + k + glD p - 39 * o = 82 + glD p + 39 * (2 - o) - 19 + k by omega]
  have hT : ∀ a', Stmt.atom a' ∈ glTail o → (∀ d q off, a' = .load d q off →
      some ((glRho p o d).idx, (glRho p o q).idx, off) ∉ S.map loadKey) →
      Good rd [] (fun _ => 0) τ a' := fun a' ha' hld ↦
    good_rho ho (List.all_eq_true.mp (glTail_ok o ho) _ ha') (hG _ (mT _ ha')) hld
  have mK : ∀ s ∈ glKids (4 * (2 - o)), s ∈ glTail o := fun s hs ↦ by
    simp only [glTail, List.mem_append]; exact .inl (.inl (.inl (.inl hs)))
  have mC : ∀ s ∈ glCheck, s ∈ glTail o := fun s hs ↦ by
    simp only [glTail, List.mem_append]; exact .inl (.inl (.inl (.inr hs)))
  have mY : ∀ s ∈ glY, s ∈ glTail o := fun s hs ↦ by
    simp only [glTail, List.mem_append]; exact .inl (.inl (.inr hs))
  have mN : ∀ s ∈ glNext (4 * (2 - o) + 12), s ∈ glTail o := fun s hs ↦ by
    simp only [glTail, List.mem_append]; exact .inl (.inr hs)
  -- the children
  have hGk : ∀ s ∈ glKids (4 * (2 - o)), GoodS rd [] (fun _ => 0) τ s := fun s hs ↦ by
    obtain ⟨a', rfl⟩ := glKids_atoms _ s hs
    refine hT a' (mK _ hs) fun d q off h ↦ ?_
    subst h
    obtain ⟨i, hi, rfl, rfl, rfl⟩ := glKids_load hs
    refine fK _ ?_
    have h1 : (glRho p o (.n (chB (val% «gkr_layer__L0_L0» "x@9") i))).idx = chB (val% «gkr_layer__L0_L0» "x@9") i + glD p - 38 * o := by
      have hidx : (V.n (chB (val% «gkr_layer__L0_L0» "x@9") i)).idx = chB (val% «gkr_layer__L0_L0» "x@9") i := rfl
      rw [glRho_idx, hidx]
      have : 160 ≤ chB (val% «gkr_layer__L0_L0» "x@9") i := by simp only [chB]; omega
      split_ifs <;> omega
    rw [h1, glcRho_mid p o 80 (by omega) (by omega)]
    simp only [glcKidKeys, List.mem_map, List.mem_range]
    exact ⟨i, hi, by simp [Nat.add_comm]⟩
  have hflen : D.cs.flatten.length = 4 * L := by rw [flatten_length_four h4, hcsL]
  obtain ⟨RK, EV, B1⟩ := glct_kids (C := coreProgram.Rel rd) (kret := fun rs => rs = [])
    (off := 4 * (2 - o)) hGk tcap (ch := D.ch0 ++ (D.ch1 ++ D.ch2)) (by simp [hl0, hl1, hl2])
    (by
      have := hxs.2
      rw [hflen] at this
      rw [t77, mul_assoc, ← pow_add, show 4 * a + 4 * (2 - o) = 4 * L by omega]
      exact this)
  obtain ⟨hc0, hc1, hc2⟩ := glc_chw (τ := τ) hl0 hl1 hl2 fun i hi ↦ (EV i hi).1
  -- the check
  have RC := glct_check (C := coreProgram.Rel rd) (kret := fun rs => rs = []) (τ := τ) (rd := rd)
    (w := fun _ => 0)
    (fun s hs ↦ by
      obtain ⟨a', rfl⟩ := glCheck_atoms s hs
      exact hT a' (mC _ hs) fun d q off h ↦ by subst h; simp [glCheck] at hs)
    (fun i hi ↦ (EV i hi).2.1)
    (by rw [t158, hc0, hc1, hc2, tlo 27 (by omega), e40, ← hrun2]; exact hcheck)
  -- the new coordinates
  have hp0' : (D.run s st).2.2 = ⟨(D.run s st).2.2.cap, []⟩ := by
    rw [hrun2, hSt]; exact gkSt_empty _ _ _ _ _
  have hsb : D.sb s st = ⟨capOf (Fs.perm ⟨capOf (Fs.perm ⟨(St L).2.cap,
      D.ch0.map (·, dsObserve)⟩), D.ch1.map (·, dsObserve)⟩), D.ch2.map (·, dsObserve)⟩ := by
    show ((((D.run s st).2.2.absorbAll D.ch0 dsObserve).absorbAll D.ch1 dsObserve).absorbAll D.ch2
      dsObserve) = _
    rw [hp0', absorbAll_short ⟨(D.run s st).2.2.cap, []⟩ D.ch0 dsObserve (by simp [hl0]),
      List.nil_append,
      tb_absorbAll_full ⟨(D.run s st).2.2.cap, D.ch0.map (·, dsObserve)⟩ (by simp [hl0]) D.ch1 hl1,
      tb_absorbAll_full _ (by simp [hl1]) D.ch2 hl2, hrun2]
  set P3 := Fs.perm ⟨capOf (Fs.perm ⟨capOf (Fs.perm ⟨(St L).2.cap, D.ch0.map (·, dsObserve)⟩),
    D.ch1.map (·, dsObserve)⟩), D.ch2.map (·, dsObserve)⟩ with hP3
  have hys : D.ys s st 2 = [challengeOf P3, challengeOf (permOf (rateOf [] ++ capOf P3))] := by
    show ((D.sb s st).squeezeN 2).1 = _; rw [hsb, glc_squeezeN_two]
  have hs' : D.s' s st 2 = ⟨capOf (permOf (rateOf [] ++ capOf P3)), []⟩ := by
    show ((D.sb s st).squeezeN 2).2 = _; rw [hsb, glc_squeezeN_two]
  have hrow' : pts * gen ^ (40 * (j + 2)) = τ (.n (valf% «gkr_layer» "point_row")) * gen ^ 40 := by
    rw [tlo 52 (by omega), e53, mul_assoc, ← pow_add]; ring_nf
  have y0 := hpt2.1 0 (by rw [hysl]; omega)
  have y1 := hpt2.1 1 (by rw [hysl]; omega)
  simp only [hys, List.getElem_cons_zero, List.getElem_cons_succ] at y0 y1
  rw [hrow', tb_loadHolds_mul_gen_pow] at y0 y1
  obtain ⟨RY, e262, e276, ecap⟩ := glct_y (C := coreProgram.Rel rd) (kret := fun rs => rs = [])
    (τ := τ) (rd := rd) (w := fun _ => 0) (fun s hs hn ↦ by
      obtain ⟨a', rfl⟩ := glY_atoms s hs
      exact hT a' (mY _ hs) fun d q off h ↦ absurd (congrArg Stmt.atom h) (hn d q off))
    (fun i hi ↦ (EV (8 + i) (by omega)).2.2) (cap := capOf (Fs.perm ⟨capOf (Fs.perm ⟨(St L).2.cap,
      D.ch0.map (·, dsObserve)⟩), D.ch1.map (·, dsObserve)⟩)) (by rw [B1, hc0, hc1])
    (by rw [tlo 23 (by omega)]; exact z23) (by rw [tlo 24 (by omega)]; exact z24)
    (by rw [tlo 25 (by omega)]; exact z25) (by rw [tlo 26 (by omega)]; exact z26)
    (by rw [hc2]; exact y0) (by rw [hc2]; exact y1)
  rw [hc2, ← hP3] at e262 e276 ecap
  -- the next slot
  have t15 : τ (.n (valf% «gkr_layer» "layer")) = layers * gen ^ (10 * L) := by rw [tlo 15 (by omega), e15]
  have ldn : ∀ k v, LoadHolds rd layers (10 * (L + 2) + k) v → LoadHolds rd (τ (.n (valf% «gkr_layer» "layer"))) (20 + k) v :=
    fun k v h ↦ by rw [t15, tb_loadHolds_mul_gen_pow, show 10 * L + (20 + k) = 10 * (L + 2) + k by ring]; exact h
  have hxl : D.xs.length = 4 * L + 12 := by
    simp [GkStepD.xs, hflen, hl0, hl1, hl2]
  have RN := glct_next (C := coreProgram.Rel rd) (kret := fun rs => rs = []) (τ := τ)
    (cw := 4 * (2 - o) + 12) (by omega)
    (fun a' ha' hn ↦ hT a' (mN _ ha') fun d q off h ↦ absurd h (hn d q off))
    (fun i hi ↦ (EV i hi).2.1)
    (fun k hk ↦ by
      have := hcap' k hk
      rw [hs'] at this
      refine ldn k _ ?_
      have hk' : τ (.n ((val% «gkr_layer__L0_L0» "nxt[8]@7") + k)) = (capOf (permOf (rateOf [] ++ capOf P3))).getD k 0 := by
        rw [← ecap]; simp [List.getD_eq_getElem?_getD, hk]
      rw [hk']; exact this)
    (by
      have := ldn 5 _ hcur'
      rw [hxl] at this
      rw [t77, mul_assoc, ← pow_add, show 4 * a + (4 * (2 - o) + 12) = 4 * L + 12 by omega]
      exact this)
    (fun t ht ↦ by
      have := ldn (6 + t) _ (by rw [← Nat.add_assoc]; exact hval' t ht)
      rw [show 20 + (6 + t) = 26 + t by ring] at this
      have hv : (D.st' s st 2).values.getD t 0 =
          multilinearEval (chWords τ (val% «gkr_layer__L0_L0» "x@9") t) [τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")), τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7"))] := by
        show ([D.ch0, D.ch1, D.ch2].map (multilinearEval · (D.ys s st 2))).getD t 0 = _
        rw [hys, e262, e276]
        interval_cases t
        · rw [hc0]; rfl
        · rw [hc1]; rfl
        · rw [hc2]; rfl
      rwa [hv] at this)
    (by
      have := ldn 9 _ hpos'
      rw [tlo 43 (by omega), tlo 3 (by omega), e44, e3, ← pow_succ, ← pow_mul, mul_comm (m + 1) 7]
      exact this)
  -- the relation
  obtain ⟨nPre, nHR, nHS, nLC, nTS, nTR, nPD⟩ := glBodyA_noRet p o (glLoopName p o)
  obtain ⟨nK, nC, nY, nN⟩ := glTail_noRet o
  refine (tb_rel_iff_sem hf _ _).mpr ⟨σ, ?_, ?_⟩
  · rw [hpar]
    simp only [glParams, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.map_append]
    rw [e0, e1, e2, e3, e4, e5, par 6 (by omega), par 7 (by omega), par 8 (by omega)]
    rfl
  · rw [hb, glBody]
    rw [holdsList_append, holdsList_noRet _ (by simp only [tb_noRetList_append, nPre, nHR, nHS, nLC,
      nTS, nTR, nPD, Bool.and_self])]
    refine ⟨?_, ?_⟩
    · rw [tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nPre, nHR, nHS, nLC, nTS,
        nTR, Bool.and_self]), tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nPre,
        nHR, nHS, nLC, nTS, Bool.and_self]), tb_holdsList_append_noRet (by simp only
        [tb_noRetList_append, nPre, nHR, nHS, nLC, Bool.and_self]), tb_holdsList_append_noRet (by
        simp only [tb_noRetList_append, nPre, nHR, nHS, Bool.and_self]), tb_holdsList_append_noRet
        (by simp only [tb_noRetList_append, nPre, nHR, Bool.and_self]), tb_holdsList_append_noRet nPre]
      exact ⟨⟨⟨⟨⟨⟨R1, R2⟩, R3⟩, R4⟩, R5⟩, R6⟩, R7⟩
    · rw [Stmt.holdsList_rename, glTail, holdsList_append,
        holdsList_noRet _ (by simp only [tb_noRetList_append, nK, nC, nY, nN, Bool.and_self]),
        tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nK, nC, nY, Bool.and_self]),
        tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nK, nC, Bool.and_self]),
        tb_holdsList_append_noRet nK]
      exact ⟨⟨⟨⟨RK, RC⟩, RY⟩, RN⟩, rfl⟩

end Layer

end
end LeanVM.Guest.B1.Tables
