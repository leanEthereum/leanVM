/-
  LeanVM.Guest.B1.Whir.Squeezes

  A level's query positions and batching challenge: the template's squeeze block, with its loop,
  squeezes the Spec's `sampleQueries` and `sampleE`.
-/

module

public import LeanVM.Guest.B1.Whir.SqLoop
public import LeanVM.Guest.B1.Whir.Positions

/-!
# The squeezes of a level (G:1559-1593)

After the proof of work the sponge has nothing waiting. The level stores its capacity in the
squeeze run's row `0`, runs the squeeze loop (`lv.squeezes` squeezes, each decoding `192/depth`
positions), loads the last capacity and squeezes the batching challenge `lam`
(`osSqueezes_sound`). In the Spec that is `sampleQueries` (V:1682; `sampleQueriesAux_run`) and
`sampleE`.

`PadOk σ pad`: the sponge's zero run, once allocated, holds zeros.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The zero run, once allocated, holds zeros after its first cell. -/
def PadOk (σ : Val) : Option ℕ → Prop
  | none => True
  | some p => σ (.n (p + 1)) = 0 ∧ σ (.n (p + 2)) = 0 ∧ σ (.n (p + 3)) = 0 ∧ σ (.n (p + 4)) = 0

theorem osPad_ok {pad : Option ℕ} {k : ℕ} (hp : PadOk σ pad) {C : CallRel}
    (h : AllOk C rd σ (osPad pad k).1) : PadOk σ (some (osPad pad k).2.1) := by
  cases pad with
  | some p => exact hp
  | none =>
    simp only [osPad, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h
    obtain ⟨-, h1, h2, h3, h4⟩ := h
    simp only [PadOk, osPad]
    rw [h1, h2, h3, h4, word_zero]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem osPad_next (pad : Option ℕ) (k : ℕ) : k ≤ (osPad pad k).2.2 := by
  cases pad <;> simp [osPad]

/-- A squeeze with nothing waiting (`osSqueeze0`) on the capacity values `cap`, the zero run at
`p` holding zeros: its outputs are the cells of the sponge's permutation, its challenge the
sponge's. -/
theorem osSqueeze0_val {C : CallRel} {p : ℕ} {cap : List ℕ} (hcl : cap.length = 5) {j : ℕ}
    (hp : PadOk σ (some p)) (h : AllOk C rd σ (osSqueeze0 p cap j)) :
    (∀ c : Fin 13, σ (.n (j + c.val)) =
      cellsOfState (⟨cap.map fun i ↦ σ (.n i), []⟩ : Fs).perm false c) ∧
    σ (.n (j + 19)) = challengeOf (⟨cap.map fun i ↦ σ (.n i), []⟩ : Fs).perm := by
  match cap, hcl with
  | [a0, a1, a2, a3, a4], _ =>
  simp only [osSqueeze0, allOk_cons, allOk_challengeT] at h
  obtain ⟨hK, hch⟩ := h
  obtain ⟨-, -, -, hout⟩ := keccakA_perm (rd := rd) hK
  obtain ⟨z1, z2, z3, z4⟩ := hp
  have hS : permOf (List.map σ (List.map V.n ([p + 1, p + 1, p + 1, p + 1, p + 1, p + 2, p + 3,
      p + 4] ++ [a0, a1, a2, a3, a4]))) =
      (⟨[a0, a1, a2, a3, a4].map fun i ↦ σ (.n i), []⟩ : Fs).perm := by
    rw [perm_eq_cells _ (by simp)]
    simp [pendCells, z1, z2, z3, z4]
  rw [hS] at hout
  have e : ∀ c : Fin 13, σ (.n (j + c.val)) =
      cellsOfState (⟨[a0, a1, a2, a3, a4].map fun i ↦ σ (.n i), []⟩ : Fs).perm false c :=
    fun c ↦ by simpa [osRun] using outs_eq hout c (by simp [osRun])
  refine ⟨e, ?_⟩
  have := challengeT_value hch (e 0) (e 1)
  simpa using this

theorem squeezeN_cap_length : ∀ (n : ℕ) (s : Fs), s.cap.length = 5 →
    (s.squeezeN n).2.cap.length = 5
  | 0, _, h => h
  | n + 1, s, _ => by rw [squeezeN_snoc]; simp [Fs.squeeze, capOf]

/-- A sponge with nothing waiting is its capacity. -/
theorem fs_of_pend_nil {s : Fs} (h : s.pend = []) : s = ⟨s.cap, []⟩ := by
  cases s; simp_all

/-- **A level's squeezes** (G:1556-1583): from the capacity it carries with nothing waiting
(`F0`), the loop's `n` squeezes decode the positions and their windows (reading the window table
at `win_tabs`), the next squeeze is the batching
challenge `lam` (at the returned `k - 1`), its capacity the sponge's. -/
theorem osSqueezes_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt}
    (hok : AllOk (coreProgram.Rel rd) rd σ (osSqueezes c lvl lv st).1)
    (hloop : FnIs (c.sqLoop lvl) (osParams 6) (sqLoopBody lv (c.sqLoop lvl)))
    (hpw : digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth)
    (hpo : lv.posOff < u128Bound)
    (hdec : ∀ args rets, WinTabs rd (args.getD 3 0) →
      coreProgram.Rel rd ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
        args rets → MeaningDecodeQueryWindows lv.depth lv.capDepth rd args rets)
    (hwt : WinTabs rd (σ (.n osWin)))
    (hn0 : 0 < lv.squeezes) (hn : lv.squeezes < ordG) (hn5 : lv.squeezes * 5 < u128Bound)
    (hfs : st.fs.length = 5) (hpad : PadOk σ st.pad) :
    (∀ jj < lv.squeezes, MeaningDecodeQueryWindows lv.depth lv.capDepth rd
      [((⟨st.fsv σ, []⟩ : Fs).squeezeN jj).2.squeeze.1,
        σ (.n osQpos) * gen ^ (lv.posOff + jj * (192 / lv.depth)),
        σ (.n osQbp) * gen ^ (lv.posOff + jj * (192 / lv.depth)), σ (.n osWin)] []) ∧
    σ (.n ((osSqueezes c lvl lv st).2.k - 1)) =
      ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 ∧
    (osSqueezes c lvl lv st).2.fsv σ =
      ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.2.cap ∧
    PadOk σ (osSqueezes c lvl lv st).2.pad ∧ (osSqueezes c lvl lv st).2.fs.length = 5 ∧
    (osSqueezes c lvl lv st).2.mats = st.mats := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fold_args st hfs
  obtain ⟨fn, hfind, hps, hbody⟩ := hloop
  set k := st.k
  set p := (osPad st.pad (k + 14)).2.1
  set j := (osPad st.pad (k + 14)).2.2
  have hsk : (osSqueezes c lvl lv st).2.k = j + 20 := rfl
  have hsfs : (osSqueezes c lvl lv st).2.fs = [j + 8, j + 9, j + 10, j + 11, j + 12] := rfl
  have hspad : (osSqueezes c lvl lv st).2.pad = some p := rfl
  have hstm : (osSqueezes c lvl lv st).1 = osHeap ((c.maxSq + 1) * 5) k ++
      (st.fs.zipIdx.map fun (f, i) ↦ .atom (.load (.n f) (.n (k + 1)) i)) ++
      osLoopCall (c.sqLoop lvl) lv.squeezes [k + 1, osQpos, osQbp, osWin] (k + 2) ++
      [.atom (.const (.n (k + 7)) (gw (lv.squeezes * 5))),
        .atom (.mul (.n (k + 8)) (.n (k + 1)) (.n (k + 7)))] ++
      ((List.range 5).map fun i ↦ .atom (.load (.n (k + 9 + i)) (.n (k + 8)) i)) ++
      (osPad st.pad (k + 14)).1 ++ osSqueeze0 p [k + 9, k + 10, k + 11, k + 12, k + 13] j := rfl
  rw [hstm] at hok
  rw [hsk, hsfs, hspad]
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨⟨-, hS⟩, hL⟩, hM⟩, hLd⟩, hPd⟩, hQ⟩ := hok
  simp only [osLoopCall, hf, List.zipIdx_cons, List.zipIdx_nil, allOk_cons, allOk_nil,
    and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, Nat.add_zero, Nat.zero_add, Nat.add_assoc,
    Nat.reduceAdd] at hS hL hM hLd
  obtain ⟨s0, s1, s2, s3, s4⟩ := hS
  obtain ⟨c2, c3, a4, c5, c6, -, hcall⟩ := hL
  obtain ⟨c7, m8⟩ := hM
  obtain ⟨l9, l10, l11, l12, l13⟩ := hLd
  have hpad' := osPad_ok hpad hPd
  have hsq := osSqueeze0_val (cap := [k + 9, k + 10, k + 11, k + 12, k + 13]) rfl hpad' hQ
  -- the loop
  have hgn : gw lv.squeezes = gen ^ lv.squeezes := gw_eq (by
    have : ordG < u128Bound := by unfold ordG u128Bound; norm_num
    omega)
  have hit := sqLoop_sound hfind lv hps hbody hpw hpo hdec hn0 hn (σ (.n (k + 1))) (σ (.n osQpos))
    (σ (.n osQbp)) (σ (.n osWin)) hwt (by
      rw [a4, c2, c3, c5, c6, hgn, word_one] at hcall
      exact hcall)
  have hfsv : st.fsv σ = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
    simp [OsSt.fsv, hf]
  obtain ⟨P, D⟩ := sqChain (st.fsv σ) (by simp [OsSt.fsv, hfs]) (fun i hi ↦ by
      rw [hfsv]
      rcases i with _ | _ | _ | _ | _ | i
      · exact s0
      · exact s1
      · exact s2
      · exact s3
      · exact s4
      · omega) hit
  -- the last capacity
  have hrow : σ (.n (k + 8)) = σ (.n (k + 1)) * gen ^ (5 * lv.squeezes) := by
    rw [m8, c7, gw_eq hn5, Nat.mul_comm]
  have hlast : [σ (.n (k + 9)), σ (.n (k + 10)), σ (.n (k + 11)), σ (.n (k + 12)), σ (.n (k + 13))] =
      ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.cap := by
    refine five_eq (o := 5 * lv.squeezes) rfl ?_ (fun i hi ↦ ?_) (P lv.squeezes le_rfl)
    · exact squeezeN_cap_length _ _ (by simp [OsSt.fsv, hfs])
    · rw [← loadHolds_mul_gen_pow, ← hrow]
      rcases i with _ | _ | _ | _ | _ | i
      · exact l9
      · exact l10
      · exact l11
      · exact l12
      · exact l13
      · omega
  have hF : (⟨[σ (.n (k + 9)), σ (.n (k + 10)), σ (.n (k + 11)), σ (.n (k + 12)),
      σ (.n (k + 13))], []⟩ : Fs) = ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2 := by
    rw [hlast, ← fs_of_pend_nil (squeezeN_pend rfl _)]
  simp only [List.map_cons, List.map_nil, hF] at hsq
  obtain ⟨hcells, hlam⟩ := hsq
  refine ⟨D, by rw [show j + 20 - 1 = j + 19 by omega, hlam]; rfl, ?_, hpad', rfl, rfl⟩
  have h8 : σ (.n (j + 8)) = _ := hcells 8
  have h9 : σ (.n (j + 9)) = _ := hcells 9
  have h10 : σ (.n (j + 10)) = _ := hcells 10
  have h11 : σ (.n (j + 11)) = _ := hcells 11
  have h12 : σ (.n (j + 12)) = _ := hcells 12
  rw [OsSt.fsv, hsfs]
  simp only [List.map_cons, List.map_nil, Fs.squeeze, capOf, h8, h9, h10, h11, h12]

end
end LeanVM.Guest.B1.Whir
