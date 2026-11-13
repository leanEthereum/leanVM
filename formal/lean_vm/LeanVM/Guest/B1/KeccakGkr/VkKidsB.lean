/-
  LeanVM.Guest.B1.KeccakGkr.VkKidsB

  `verify_keccak`'s callees, complete where it places them, within their bounds (`KidsGB`), as
  `completeAt_flatGB` takes them.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCI
public import LeanVM.Guest.B1.KeccakGkr.FlatGB
public import LeanVM.Guest.B1.KeccakGkr.LayerCPlacedB
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_keccak`'s callees within their bounds

`kids_completeB` is `kids_complete` with each call within its bound in `D.kidsB` (in order):

* the copy loops `verify_keccak_loop0`, `verify_keccak_loop1`, `verify_keccak_loop2` (`τ - 4` words
  each): `(τ - 4) * KC` and the loop's frame, from their runs' words (`TotalLeOn … LoopPre`, at most
  `KC` per iteration and their one phantom frame);
* the twelve layers: `layerWords fs (firstOf s) (D.layer s).y KP KR` (`layer_completeAtFB`);
* the committed outputs' and the inputs' opening's rounds (`plainName 0`): `KO`; the inputs'
  rounds (`plainName 1`): `KI` (`TotalLe`).

Every call is entered, so the callees' words (`kidsGBound`) are at most `(D.kidsB …).sum`
(`kids_boundB`), which is `3 * ((τ - 4) * KC)` and the copy loops' frames, `2 * KO + KI` and
`Σ_{s < 12} layerWords …` (`kidsB_sum`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public noncomputable section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## Bounded callees, entry by entry -/

/-- `KidsGB` from the calls and their bounds, pairwise. -/
theorem kidsGB_of_zip {κ : ℕ} : ∀ {ks : List KidG} {Bs : List ℕ}, ks.length = Bs.length →
    (∀ kb ∈ ks.zip Bs, kb.1.taken = true → ∀ ps, CompleteAtFB fs cert κ kb.1.f
      (fun p ↦ kb.1.Lin (ps ++ [p])) (kb.1.args ps) (fun p ↦ kb.1.Out (ps ++ [p])) kb.2) →
    KidsGB fs cert κ ks Bs
  | [], _, _, _ => trivial
  | _ :: _, [], hl, _ => by simp at hl
  | k :: ks, B :: Bs, hl, h =>
    ⟨fun ht ps ↦ h (k, B) (by simp) ht ps,
      kidsGB_of_zip (by simpa using hl) fun kb hkb ↦ h kb (List.mem_cons_of_mem _ hkb)⟩

/-- Every call entered, the callees' words are at most the bounds' sum. -/
theorem kidsGBound_le_sum : ∀ (ks : List KidG) (Bs : List ℕ), (∀ k ∈ ks, k.taken = true) →
    kidsGBound fs ks Bs ≤ Bs.sum
  | [], _, _ => Nat.zero_le _
  | k :: ks, [], h => by
    have := kidsGBound_le_sum ks [] fun k' hk' ↦ h k' (List.mem_cons_of_mem _ hk')
    simp only [kidsGBound, h k List.mem_cons_self, ↓reduceIte, List.headD_nil, List.tail_nil,
      List.sum_nil] at this ⊢
    omega
  | k :: ks, B :: Bs, h => by
    have := kidsGBound_le_sum ks Bs fun k' hk' ↦ h k' (List.mem_cons_of_mem _ hk')
    simp only [kidsGBound, h k List.mem_cons_self, ↓reduceIte, List.headD_cons, List.tail_cons,
      List.sum_cons]
    omega

/-- **A copy loop, complete within `m * KC` and its frame**: `loop_complete` with its run's words,
per iteration and its one phantom frame. -/
theorem loop_completeB {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = copyLoopT name) (hpar : fn.params = [.n 0, .n 1, .n 2, .n 3])
    (hS : name ∈ vkKidS) {KC : ℕ}
    (hT : TotalLeOn coreProgram fs name LoopPre fun a ↦ logG (a.getD 1 0) * KC + fs name)
    (κ : ℕ) {L : Main.Layout} {m : ℕ} (hm1 : 0 < m) (hm2 : m < ordG)
    {db sb dj sj : ℕ} {dw sw : List E} (hd : (db, dw) ∈ L) (hs : (sb, sw) ∈ L)
    (hdl : dj + m ≤ dw.length) (hsl : sj + m ≤ sw.length)
    (heq : ∀ j < m, dw.getD (dj + j) 0 = sw.getD (sj + j) 0) {dst src : E}
    (hdst : dst = ptr db * gen ^ dj) (hsrc : src = ptr sb * gen ^ sj) :
    CompleteAtB fs cert κ name L [1, gen ^ m, dst, src] (Returns []) (m * KC + fs name) := by
  refine CompleteAtDTB.toCompleteAtB (completeAtDTB_of_relIn vkKidS_pure hS
    (fun rd t rets' hn hv hb' ↦ ?_) fun rd _ hmem ↦ ?_)
  · have h1 := hT rd t _ rets' hn (loopPre_gen hm1 (by unfold ordG at hm2; omega) _) hv hb'
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h1
    rwa [gen_pow_eq_ofK, logG_spec (by unfold ordG at hm2; omega)] at h1
  have hD := memL_entry hmem hd
  have hS' := memL_entry hmem hs
  subst hdst hsrc
  refine (copyLoop_relIn hf hb hpar (m := m) (fun j hj ↦ ⟨dw.getD (dj + j) 0, ?_, ?_⟩)
    (fun j hj ↦ ⟨?_, ?_⟩)).2 (gen_pow_ne_one hm1 hm2)
  · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, heq j hj, add_zero]
    exact ClaimLay.getD_load hS' (by omega)
  · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, add_zero]
    exact ClaimLay.getD_load hD (by omega)
  · rw [mul_assoc, ← pow_add]; exact inR_entry hs (by omega)
  · rw [mul_assoc, ← pow_add]; exact inR_entry hd (by omega)

/-- **The openings' rounds, complete within `K`.** -/
theorem plain_completeB {k0 : ℕ} (hk : k0 < 2) {K : ℕ}
    (hT : TotalLe coreProgram fs (plainName k0) fun _ ↦ K) (κ : ℕ) {L : Main.Layout}
    {args rets : List E} (hpc : PlainCellsOk k0 args)
    (hm : ∀ rd, MemL rd L → MeaningPlainRounds (plainCount k0) k0 rd args rets)
    (hcur : ∀ k < 2 * plainCount k0, InR (RegionL L) (args.getD 7 0) k)
    (hpt : ∀ k < plainCount k0, InR (RegionL L) (args.getD 9 0) k) :
    CompleteAtB fs cert κ (plainName k0) L args (Returns rets) K :=
  CompleteAtDTB.toCompleteAtB (completeAtDTB_of_relIn vkKidS_pure
    (by interval_cases k0 <;> simp [vkKidS, plainName])
    (fun rd t rets' hn hv hb ↦ hT rd t args rets' hn hv hb)
    fun rd _ hmem ↦ keccak_plain_rounds_relIn hk hpc (hm rd hmem) hcur hpt)

namespace VkData

/-- **The calls' bounds**, in order: `verify_keccak_loop0`, the twelve layers, the committed
outputs'
rounds, `verify_keccak_loop1`, the inputs' rounds, their opening's rounds, `verify_keccak_loop2`. -/
def kidsB (D : VkData) (fs : String → ℕ) (KC KP KR KO KI : ℕ) : List ℕ :=
  [(D.τ - 4) * KC + fs name% «verify_keccak_loop0»] ++
  (List.range 12).map (fun s ↦ layerWords fs (firstOf s) (D.layer s).y KP KR) ++
  [KO, (D.τ - 4) * KC + fs name% «verify_keccak_loop1», KI, KO,
      (D.τ - 4) * KC + fs name% «verify_keccak_loop2»]

variable {D : VkData}

/-- The bounds' sum. -/
theorem kidsB_sum (D : VkData) (fs : String → ℕ) (KC KP KR KO KI : ℕ) :
    (D.kidsB fs KC KP KR KO KI).sum = 3 * ((D.τ - 4) * KC) +
      (fs name% «verify_keccak_loop0» + fs name% «verify_keccak_loop1» + fs
          name% «verify_keccak_loop2») + 2 * KO + KI +
      ((List.range 12).map (fun s ↦ layerWords fs (firstOf s) (D.layer s).y KP KR)).sum := by
  simp only [kidsB, List.sum_append, List.sum_cons, List.sum_nil]
  omega

/-- **Every call is entered: the callees' words are at most the bounds' sum.** -/
theorem kids_boundB (B curE chiE olE zvE slE tbE KC KP KR KO KI : ℕ) :
    kidsGBound fs (D.kids fs B curE chiE olE zvE slE tbE) (D.kidsB fs KC KP KR KO KI) ≤
      (D.kidsB fs KC KP KR KO KI).sum := by
  refine kidsGBound_le_sum _ _ fun k hk ↦ ?_
  simp only [kids, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hk
  rcases hk with ((rfl | ⟨s, -, rfl⟩) | rfl | rfl | rfl | rfl | rfl) <;> rfl

/-- **The calls, complete where `verify_keccak` places them, within `D.kidsB`**: the copy loops
at most `KC` words per iteration, the layers' eight-round loops `KP` and remainder loops `KR` (each
loop's run and its one phantom frame), the openings' rounds `KO` (`plainName 0`) and `KI`
(`plainName 1`). -/
theorem kids_completeB (h : D.Ok) {κ : ℕ} (hκ : 11 ≤ κ) (B curE chiE olE zvE slE tbE : ℕ)
    {KC KP KR KO KI : ℕ}
    (hC : ∀ name ∈ [name% «verify_keccak_loop0», name% «verify_keccak_loop1»,
        name% «verify_keccak_loop2»],
      TotalLeOn coreProgram fs name LoopPre fun a ↦ logG (a.getD 1 0) * KC + fs name)
    (hP : ∀ first < 2, TotalLeOn coreProgram fs (packLoopName first) LoopPre
      fun a ↦ logG (a.getD 1 0) * KP + fs (packLoopName first))
    (hR : ∀ first < 2, TotalLeOn coreProgram fs (remLoopName first) LoopPre
      fun a ↦ logG (a.getD 1 0) * KR + fs (remLoopName first))
    (hO : TotalLe coreProgram fs (plainName 0) fun _ ↦ KO)
    (hI : TotalLe coreProgram fs (plainName 1) fun _ ↦ KI) :
    KidsGB fs cert κ (D.kids fs B curE chiE olE zvE slE tbE) (D.kidsB fs KC KP KR KO KI) := by
  have hτ1 := h.1
  have hτ2 := h.2.1
  have hchis := h.2.2.1
  have hord : D.τ - 4 < ordG := by unfold ordG; omega
  have hlin : ∀ {b ws}, (b, ws) ∈ [(curE, D.xs), (chiE, D.chis), (olE, D.outs), (zvE, D.op),
      (zvE + qkeccakVarsCap, D.point), (slE, D.slices), (tbE, winTabWords)] →
      (b, ws) ∈ D.lin curE chiE olE zvE slE tbE :=
    fun h ↦ h
  refine kidsGB_of_zip (by simp [kids, kidsB]) fun kb hkb _ ps ↦ ?_
  rw [kids, kidsB, List.zip_append (by simp), List.zip_append (by simp), List.zip_map'] at hkb
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_append, List.mem_cons,
    List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hkb
  rcases hkb with ((rfl | ⟨s, hs, rfl⟩) | rfl | rfl | rfl | rfl | rfl)
  · -- `verify_keccak_loop0`
    exact (loop_completeB find_copyLoop11 copyLoop_body11 rfl (by simp [vkKidS])
      (hC _ (by simp)) κ
      (L := [(chiE, D.chis), (B, D.c0.point)]) (dw := D.c0.point) (sw := D.chis)
      (m := D.τ - 4) (by omega) hord (db := B) (dj := 0) (sb := chiE) (sj := 4)
      (by simp) (by simp) (by rw [c0_point_length h]; omega) (by omega)
      (fun j hj ↦ by rw [zero_add, c0_point_getD h hj]) (by simp) rfl).toFB
  · -- the layers
    have hy := D.layer_y h (k := s) (by omega)
    have hcl := D.layer_cap h hs
    obtain ⟨hpl, hgr, hpm, hlm, hproj, hfin⟩ := D.layer_facts h hs
    have hf2 : firstOf s < 2 := by unfold firstOf; split <;> omega
    have H := layer_completeAtFB (fs := fs) (cert := cert) (first := firstOf s)
      hf2 hκ (D.layer s)
      (D.CL B (D.lsOf fs ps) s) (curE + D.lcur s) (B + D.o201 + 22 * (s + 1)) tbE
      (p0 := (D.cells s).1) (p1 := (D.cells s).2) (hP _ hf2) (hR _ hf2) hcl (fun hf1 ↦ by
        obtain rfl : s = 0 := by unfold firstOf at hf1; split at hf1 <;> omega
        rfl) (by rw [hy]; omega) (by rw [hy]; omega) hpl hpm hlm hproj hgr hfin
      (D.CL_ok h B _ (by omega))
    have hb : (D.CL B (D.lsOf fs ps) s).bclaim = B + D.o201 + 22 * s := by cases s <;> rfl
    rw [hb] at H
    simp only [layKid, List.dropLast_concat, List.getLast?_concat, Option.getD_some]
    exact H
  · -- the committed outputs' rounds
    obtain ⟨a, b, c, d, e, hc⟩ := five_of_length' (L_ok h).2
    refine (plain_completeB (k0 := 0) (by norm_num) hO κ (L := D.lin curE chiE olE zvE slE tbE)
      (fun h0 ↦ absurd h0 (by decide)) (fun rd hm ↦ oMeaning h hm) (fun j hj ↦ ?_)
      (fun j hj ↦ ?_)).toFB
    · have e : (D.oArgs curE zvE tbE).getD 7 0 = ptr curE * gen ^ D.lcur 12 := by
        rw [oArgs, hc, ← cL_eq]; rfl
      rw [e]
      exact inR_entry (ws := D.xs) (hlin (by simp))
        (by rw [xs_length h]; simp [plainCount] at hj; omega)
    · have e : (D.oArgs curE zvE tbE).getD 9 0 = ptr zvE * gen ^ D.τ := by rw [oArgs, hc]; rfl
      rw [e]
      exact inR_entry (ws := D.op) (hlin (by simp))
        (by rw [op_length h]; simp [plainCount] at hj; omega)
  · -- `verify_keccak_loop1`
    refine (loop_completeB find_copyLoop12 copyLoop_body12 rfl (by simp [vkKidS])
      (hC _ (by simp)) κ
      (L := [(zvE, D.op), (B, D.c0.point)]) (dw := D.op) (sw := D.c0.point) (m := D.τ - 4)
      (by omega) hord (db := zvE) (dj := 4) (sb := B) (sj := 0)
      (by simp) (by simp) (by rw [op_length h]; omega) (by rw [c0_point_length h]; omega)
      (fun j hj ↦ ?_) rfl (by simp)).toFB
    rw [zero_add, c0_point_getD h hj, op_eq, List.take_append_drop,
      List.getD_append _ _ _ _ (by rw [inst_length h]; omega), inst_getD h (by omega)]
  · -- the inputs' rounds
    obtain ⟨a, b, c, d, e, hc⟩ := five_of_length' (O_ok h).2
    refine (plain_completeB (k0 := 1) (by norm_num) hI κ (L := D.lin curE chiE olE zvE slE tbE)
      (fun _ ↦ ⟨D.word, by rw [iArgs, hc]; rfl⟩) (fun rd hm ↦ iMeaning h hm) (fun j hj ↦ ?_)
      (fun j hj ↦ ?_)).toFB
    · have e : (D.iArgs curE zvE tbE).getD 7 0 = ptr curE * gen ^ (D.lcur 12 + 13) := by
        rw [iArgs, hc]
        show D.cL curE * gen ^ (2 * 6) * gen = _
        rw [cL, ptr_mul_gen, ptr_mul_gen1, ptr_mul_gen]
        congr 1
      rw [e]
      exact inR_entry (ws := D.xs) (hlin (by simp))
        (by rw [xs_length h]; simp [plainCount] at hj; omega)
    · have e : (D.iArgs curE zvE tbE).getD 9 0 = ptr (zvE + qkeccakVarsCap) * gen ^ 0 := by
        rw [iArgs, hc]
        show ptr zvE * gen ^ 39 = _
        rw [ptr_mul_gen, ptr_mul_gen]
      rw [e]
      exact inR_entry (ws := D.point) (hlin (by simp))
        (by rw [point_length h]; simp [plainCount] at hj; omega)
  · -- the inputs' opening's rounds
    obtain ⟨a, b, c, d, e, hc⟩ := five_of_length' (I_ok h).2
    refine (plain_completeB (k0 := 0) (by norm_num) hO κ (L := D.lin curE chiE olE zvE slE tbE)
      (fun h0 ↦ absurd h0 (by decide)) (fun rd hm ↦ sMeaning h hm) (fun j hj ↦ ?_)
      (fun j hj ↦ ?_)).toFB
    · have e : (D.sArgs curE zvE tbE).getD 7 0 = ptr curE * gen ^ (D.lcur 12 + 21) := by
        rw [sArgs, hc]
        show D.cL curE * gen ^ (2 * 6) * gen * gen ^ (2 * 4) = _
        rw [cL, ptr_mul_gen, ptr_mul_gen1, ptr_mul_gen, ptr_mul_gen]
        congr 1
      rw [e]
      exact inR_entry (ws := D.xs) (hlin (by simp))
        (by rw [xs_length h]; simp [plainCount] at hj; omega)
    · have e : (D.sArgs curE zvE tbE).getD 9 0 = ptr (zvE + qkeccakVarsCap) * gen ^ D.τ := by
        rw [sArgs, hc]
        show ptr zvE * gen ^ 39 * gen ^ D.τ = _
        rw [ptr_mul_gen]
      rw [e]
      exact inR_entry (ws := D.point) (hlin (by simp))
        (by rw [point_length h]; simp [plainCount] at hj; omega)
  · -- `verify_keccak_loop2`
    have hL : (fun p ↦ [(zvE + qkeccakVarsCap, D.point),
        (D.lsOf fs (ps ++ [p]).dropLast 11, (D.layer 11).chs (firstOf 11))]) =
        fun _ ↦ [(zvE + qkeccakVarsCap, D.point),
          (D.lsOf fs ps 11, (D.layer 11).chs (firstOf 11))] :=
      funext fun p ↦ by rw [List.dropLast_concat]
    simp only
    rw [hL]
    refine (loop_completeB find_copyLoop13 copyLoop_body13 rfl (by simp [vkKidS])
      (hC _ (by simp)) κ
      (L := [(zvE + qkeccakVarsCap, D.point), (D.lsOf fs ps 11, (D.layer 11).chs (firstOf 11))])
      (dw := D.point) (sw := (D.layer 11).chs (firstOf 11)) (m := D.τ - 4) (by omega) hord
      (db := zvE + qkeccakVarsCap) (dj := 4)
      (sb := D.lsOf fs ps 11) (sj := 0) (by simp) (by simp)
      (by rw [point_length h]; omega) (by rw [← L1_point h, L_point h]; omega)
      (fun j hj ↦ ?_) (by rw [ptr_mul_gen, ptr_mul_gen]) (by simp)).toFB
    rw [zero_add, ← L1_point h, point,
      List.getD_append _ _ _ _ (by simp [I1_length h, L_point h]; omega),
      List.getD_append_right _ _ _ _ (by rw [I1_length h]; omega), I1_length h,
      List.getD_eq_getElem?_getD, List.getElem?_take]
    simp [show 4 + j - 4 = j by omega, hj, List.getD_eq_getElem?_getD]

end VkData

end
end LeanVM.Guest.B1.VerifySub
