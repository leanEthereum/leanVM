/-
  LeanVM.Guest.CoreMode.Fn.link_rounds.SoundA

  `link_rounds`' own routing facts, sound at the honest instances of b2c's aligned tree: its loops are cursor-run
  loops (`StLoopOkA`); its returned cursor is `cursor·count_g^W` (`OwnOkA`, its family `retEq`).
-/

module

public import LeanVM.Guest.CoreMode.Fn.link_rounds.LrChain
public import LeanVM.Guest.CoreMode.Fn.link_rounds.Fam
public import LeanVM.Guest.CoreMode.Fn.link_rounds_last.SoundA

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol.Verifier (gen)

public section

/-- **A last arm's record cursor**: `link_rounds_last__L{nt}_L{bits}_L{k}` on the records `rp`, `out` stores at `out`'s
cell `5` the cursor read at `rp`'s, `k` rounds of `W` words on. -/
theorem lrLast_cur {rd : Reader} {nt bits k : ℕ} (hW : EndExec.lrW nt bits < 64) {name : String} {f : Fn}
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2, .n 3])
    (hbody : f.body = lrLastBody nt bits k) {args rets : List E} (h : coreProgram.Rel rd name args rets) {c : E}
    (h5 : LoadHolds rd (args.getD 0 0) 5 c) :
    LoadHolds rd (args.getD 1 0) 5 (c * gen ^ (k * EndExec.lrW nt bits)) := by
  rw [rel_iff_sem hfind, hbody, hparams] at h
  obtain ⟨σ, rfl, h⟩ := h
  simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ] at h5 ⊢
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [lrLastBody, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, l5, s5, -⟩ := h
    rw [loadHolds_unique l5 h5] at s5
    simpa using s5
  · have hk0 : k ≠ 0 := by omega
    simp only [lrLastBody, hk0, ↓reduceIte] at h
    generalize hrs : lrRounds nt bits 2 3 k 11 [4, 5, 6, 7, 8] 9 10 none = rs at h
    have hatR : AllAtoms rs.1 := by rw [← hrs]; exact lrRounds_atoms _ _ _ _ _ _ _ _ _ _
    simp only [holdsList_append] at h
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
    obtain ⟨-, -, -, -, -, l5, -, h⟩ := h
    obtain ⟨hR, h⟩ := (holdsList_atoms hatR _ _).mp h
    have hatS : AllAtoms ((List.range 5).map fun j ↦ Stmt.atom (.load (.n (rs.2.1.getD j 0)) (.n 1) j)) := by
      intro s hs
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hs
      exact ⟨_, rfl⟩
    obtain ⟨-, s5, -⟩ := (holdsList_atoms hatS _ _).mp h
    have hR' : ∀ a, Stmt.atom a ∈ (lrRounds nt bits 2 3 k 11 [4, 5, 6, 7, 8] 9 10 none).1 → a.Holds rd σ := by
      rw [hrs]; exact hR
    have hcur := lrRounds_cur (pts := 2) (tabs := 3) hW k 11 [4, 5, 6, 7, 8] 9 10 none hR'
    rw [hrs] at hcur
    rw [hcur, loadHolds_unique l5 h5] at s5
    exact s5

end

end LeanVM.Guest.B1.Link

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Protocol.Verifier (gen)

public section

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

set_option maxHeartbeats 1000000 in
/-- **`link_rounds`' returned cursor** at an honest instance: its value `73`, read at its last record's cell `5`, is
`cursor·count_g^W` (its split count `count = 4h + r`, its loop's records, its dispatch's arm `r`). -/
theorem lr_retCur {nt bits : ℕ} {main loop : String} {lasts : List String}
    (hmem : (nt, bits, main, loop, lasts) ∈ lrlSpecs) (hR : RefH (layB al) (D r) r) {I : Inst}
    (hI : I ∈ instsR al D r) {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node main σ bufs kids) :
    σ (.n 73) = σ (.n 5) * σ (.n 8) ^ lrW nt bits := by
  have hS := lrlSpec_all hmem
  obtain ⟨hW, ⟨fL, hfL, -, -, hparL, hbodyL⟩, ⟨fM, jm, lasts', hfM, -, -, -, -, -, -, -, -, -⟩, -⟩ :=
    lrSpec_all hS.spec
  have hbodyM : fM.body = B1.Link.lrMainBody loop lasts := by
    have := hS.body
    rw [hfM, Option.map_some] at this
    exact Option.some.inj this
  obtain ⟨args, rets, hvI⟩ := inst_validA hR hI ht
  obtain ⟨-, hbI⟩ := Res.holds_of_valid Res.fs_pos hvI hfM
  rw [hbodyM] at hbI
  simp only [B1.Link.lrMainBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    true_and] at hbI
  obtain ⟨b0, c16, c17, m18, a19, b1, c20, c21, m22, a23, m24, b2, c25, c26, m27, a28, b3, c29, c30,
    m31, a32, m33, b4, c34, c35, m36, a37, m38, b5, c39, c40, m41, a42, m43, m44, m45, m46, hassert,
    c47, m48, m49, m50, m51, m52, s0, s1, s2, s3, s4, s5, s6, c54, a55, c56, hK55, hcall, m57, m58, m59,
    m60, m61, c62, m63, -, -, -, ⟨j, hj, hj24, hlast⟩, -, -, -, -, -, r73, -⟩ := hbI
  have w3 : word 3 0 = gen ^ 1 + 1 := B1.Link.word_two_pow_xor_one (a := 1) (by norm_num)
  have w5 : word 5 0 = gen ^ 2 + 1 := B1.Link.word_two_pow_xor_one (a := 2) (by norm_num)
  have w17 : word 17 0 = gen ^ 4 + 1 := B1.Link.word_two_pow_xor_one (a := 4) (by norm_num)
  have w257 : word 257 0 = gen ^ 8 + 1 := B1.Link.word_two_pow_xor_one (a := 8) (by norm_num)
  have hrg : σ (.n 24) = gen ^ (B1.Link.bv (σ (.n 10)) + 2 * B1.Link.bv (σ (.n 11))) := by
    rw [m24, a19, a23, m18, m22, c16, c17, c20, c21, w3, w5, B1.word_one, B1.Link.bit_factor b0,
      B1.Link.bit_factor b1, ← pow_add]
    simp only [B1.Link.bv, one_mul]
  have hqg : σ (.n 43) = gen ^ (B1.Link.bv (σ (.n 12)) + 2 * B1.Link.bv (σ (.n 13)) +
      4 * B1.Link.bv (σ (.n 14)) + 8 * B1.Link.bv (σ (.n 15))) := by
    rw [m43, m38, m33, a28, a32, a37, a42, m27, m31, m36, m41, c25, c26, c29, c30, c34, c35, c39, c40, w3, w5,
      w17, w257, B1.word_one, B1.Link.bit_factor b2, B1.Link.bit_factor b3, B1.Link.bit_factor b4,
      B1.Link.bit_factor b5, ← pow_add, ← pow_add, ← pow_add]
    simp only [B1.Link.bv, one_mul]
  set rv := B1.Link.bv (σ (.n 10)) + 2 * B1.Link.bv (σ (.n 11)) with hrv
  set qv := B1.Link.bv (σ (.n 12)) + 2 * B1.Link.bv (σ (.n 13)) + 4 * B1.Link.bv (σ (.n 14)) +
    8 * B1.Link.bv (σ (.n 15)) with hqv
  have hrv4 : rv < 4 := by
    have := B1.Link.bv_le (σ (.n 10)); have := B1.Link.bv_le (σ (.n 11)); omega
  have hqv16 : qv < 16 := by
    have := B1.Link.bv_le (σ (.n 12)); have := B1.Link.bv_le (σ (.n 13)); have := B1.Link.bv_le (σ (.n 14))
    have := B1.Link.bv_le (σ (.n 15)); omega
  have hcg : σ (.n 8) = gen ^ (4 * qv + rv) := by
    have : σ (.n 8) = σ (.n 46) := by linear_combination hassert.symm + σ (.n 8) * B1.Link.two_eq_zero_E
    rw [this, m46, m45, m44, hqg, hrg]
    ring
  have hlen := hS.len
  have hjr : j = rv := by
    rw [hrg, ← gen_pow_eq_ofK] at hj24
    exact (gen_pow_inj (by omega) (by omega) hj24).symm
  -- the record the arm reads: the loop's last, or the first
  have hrec : LoadHolds r.img.read (σ (.n 53) * gen ^ (7 * qv)) 5 (σ (.n 5) * gen ^ (4 * lrW nt bits * qv)) := by
    rcases Nat.eq_zero_or_pos qv with h0 | hq1
    · rw [h0]; simpa using s5
    · have hq0 : σ (.n 55) ≠ 0 := by
        rw [a55, c54, B1.word_one, hqg]
        intro h0
        have : gen ^ qv = 1 := by linear_combination h0 - B1.Link.two_eq_zero_E
        rw [Value.gen_pow_eq_one_iff (by omega)] at this
        omega
      have hrel := (hcall hq0).rel
      rw [c56, B1.word_one, hqg, ← pow_zero gen] at hrel
      exact B1.Link.lrLoop_cur hW hfL hparL hbodyL hq1 (by unfold B1.ordG; omega) _ _ _ _ hrel s5
  have h61 : σ (.n 61) = σ (.n 53) * gen ^ (7 * qv) := by
    rw [m61, m60, m59, m58, m57, hqg]
    ring
  -- the arm's record stored
  obtain ⟨fl, hfl, hparl, hbodyl, -⟩ := hS.lastF j hj
  have hout := B1.Link.lrLast_cur hW hfl hparl hbodyl hlast.rel
    (c := σ (.n 5) * gen ^ (4 * lrW nt bits * qv)) (by simpa [h61] using hrec)
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hout
  have h63 : σ (.n 63) = σ (.n 61) * gen ^ 7 := by
    rw [m63, c62, show (128 : ℕ) = 2 ^ 7 from rfl, B1.word_two_pow (by norm_num)]
  rw [h63, B1.loadHolds_mul_gen_pow, show 7 + 5 = 12 from rfl] at hout
  rw [B1.loadHolds_unique r73 hout, hcg, hjr, ← pow_mul, mul_assoc, ← pow_add]
  congr 2
  ring

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.link_rounds

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec

public section

/-- **Its loops' cursors** (`lr_stOk`). -/
theorem stLoops_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ stLoops, StLoopOkA al D c := by
  intro c hc
  simp only [stLoops, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lr_stOk (nt := 1) (bits := 0) (main := name% «link_rounds__L1_L0») (by decide) rfl rfl
  · exact lr_stOk (nt := 6) (bits := 0) (main := name% «link_rounds__L6_L0») (by decide) rfl rfl
  · exact lr_stOk (nt := 7) (bits := 0) (main := name% «link_rounds__L7_L0») (by decide) rfl rfl
  · exact lr_stOk (nt := 8) (bits := 1) (main := name% «link_rounds__L8_L1») (by decide) rfl rfl
  · exact lr_stOk (nt := 9) (bits := 1) (main := name% «link_rounds__L9_L1») (by decide) rfl rfl
  · exact lr_stOk (nt := 10) (bits := 1) (main := name% «link_rounds__L10_L1») (by decide) rfl rfl

/-- **Its family** (`lr_retCur`), aligned. -/
theorem fams_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ fams, OwnOkA al D c := by
  intro c hc r hR hr I hI σ bufs kids ht fn hf x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  simp only [decide_eq_true_eq] at hx
  subst hx
  obtain ⟨nt, bits, loop, lasts, hmem, hW⟩ := retSpecs_lrl hp
  have he := lr_retCur hmem hR hI ht
  show CCell.valW _ _ = CCell.valW _ _
  simp only [CCell.valW, prodW, vw, pow_one, mul_one, he, hW]

end

end LeanVM.Guest.CoreMode.Own.link_rounds
