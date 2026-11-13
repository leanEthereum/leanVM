/-
  LeanVM.Guest.B1.Ring.CompleteB

  `ring_switch_target` and `ring_switch_weight` complete, placed, within a bound (`CompleteAtB`):
  their frame, their chain and their loop's or `rs_eq_run`'s words.
-/

module

public import LeanVM.Guest.B1.Ring.WeightComplete
public import LeanVM.Guest.B1.Tables.FlatAtT
public import LeanVM.Guest.Memory.SizeTotal
public import LeanVM.Guest.Data.NameStrings

/-!
# The ring switch, placed, within a bound

`rst_completeAtB`, `rsw_completeAtB`: `rst_completeAt`, `rsw_completeAt` with the size bounded
before the memory (B1-c's `completeAt_flatDTB`, forgetting the tree's shape). Their only callee is
a pure loop (`ring_switch_target_loop0`) or a pure function (`rs_eq_run`) whose words are a hypothesis
(`TotalLeOn`, fs-generic): `ring_switch_target_loop0` called from `1` (its end the constant `g^8`), `rs_eq_run` on
`count` coordinates (its last argument `g^count`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`ring_switch_target` is complete, placed, within `fs "ring_switch_target" + 72 + B14`**: its
frame, its chain (`72` words) and `ring_switch_target_loop0`'s words, at most `B14` when called from `1`
(`hl14`). -/
theorem rst_completeAtB (κ : ℕ) {bs bm : ℕ} {s chs : List E} (hs : s.length = 64)
    (hc : chs.length = 16) {B14 : ℕ}
    (hl14 : TotalLeOn coreProgram fs name% «ring_switch_target_loop0» (fun a => a.getD 0 0 = 1) fun _ => B14) :
    CompleteAtB fs cert κ "ring_switch_target" [(bs, s), (bm, chs)]
      [ofK (Parameters.addressOfIndex bs), ofK (Parameters.addressOfIndex bm)]
      (Returns [ringTarget s (chs.take ringMapWidth) (chs.drop ringMapWidth)])
      (fs "ring_switch_target" + 72 + B14) := by
  have e : fs "ring_switch_target" + 72 + B14 = fs "ring_switch_target" + [72].sum + B14 := by simp
  rw [e]
  refine B1.CompleteAtDTB.toCompleteAtB (completeAt_flatDTB (fs := fs) (cert := cert) find_rst
    rst_not_loop κ _ _ _ rst_body' rst_flat rst_addrs [72] (fun _ ↦ [chainWords s (chs.drop 8)])
    (fun _ ↦ by simp [chainWords_length])
    (fun fp ↦ [⟨name% «ring_switch_target_loop0», true, [1, ofK (Parameters.addressOfIndex bm),
      ofK (Parameters.addressOfIndex bs), ofK (Parameters.addressOfIndex (fp + fs "ring_switch_target"))],
      l13Lin bs bm (fp + fs "ring_switch_target") s chs, Returns []⟩])
    (fun _ => True) [fun _ => True] [B14] B14 ?_ (fun _ => by simp [kidsBoundL]) (fun _ => le_rfl)
    ?_ ?_ ?_)
  · -- the loop, placed, within `B14`
    intro fp
    refine ⟨fun _ => ?_, trivial⟩
    exact completeAtDTB_of_relIn l13_pure (List.mem_singleton_self _)
      (fun rd t rets' hn hv hb => hl14 rd t _ rets' hn rfl hv hb)
      fun rd _ hL ↦ l13_relIn_lin hs hc hL
  · -- the loop's words: the caller's and the chain
    intro fp k hk _ i hi
    rw [List.mem_singleton] at hk
    subst hk
    obtain ⟨q, hq, hi⟩ := hi
    simp only [l13Lin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Or.inl ⟨_, by simp, hi⟩
    · exact Or.inl ⟨_, by simp, hi⟩
    · exact Or.inr ⟨_, by simp [bufL, bases], hi⟩
  · intro fp rd hB hLin k hk
    rw [List.mem_singleton] at hk
    subst hk
    intro q hq
    simp only [l13Lin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hLin (bs, s) (by simp)
    · exact hLin (bm, chs) (by simp)
    · exact hB (fp + fs "ring_switch_target", chainWords s (chs.drop 8)) (by simp [bufL, bases])
  · -- the honest valuation
    intro fp outs ho rd _ hB hLin
    rcases outs with _ | ⟨o, _ | ⟨o', os⟩⟩
    · exact absurd ho (by simp [OutsOk])
    swap
    · exact absurd ho.2 (by simp [OutsOk])
    obtain ⟨ho', -⟩ := ho
    obtain ⟨ho1, -⟩ := ho' rfl
    obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := rst_hσ hs hc fp rd hB hLin o ho1
    exact ⟨σ, h1, h2, h3, h4, h5, h6, h7, trivial⟩


/-- **`ring_switch_weight` is complete, placed, within
`fs "ring_switch_weight" + 64 · (count + 1) + Brs`**: its frame, its chain (`allocDyn`, at most
`64 · (count + 1)` words) and `rs_eq_run`'s words, at most `Brs` on `count` coordinates (`hrs`). -/
theorem rsw_completeAtB (κ : ℕ) {bz bp bc count : ℕ} {zs ps cs : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) (hc : cs.length = 64) {Brs : ℕ}
    (hrs : TotalLeOn coreProgram fs "rs_eq_run" (fun a => a.getD 3 0 = gen ^ count) fun _ => Brs) :
    CompleteAtB fs cert κ "ring_switch_weight" [(bz, zs), (bp, ps), (bc, cs)]
      [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
      (Returns [ringWeight zs (ps.map (1 + ·)) cs])
      (fs "ring_switch_weight" + 64 * (count + 1) + Brs) := by
  have e : fs "ring_switch_weight" + 64 * (count + 1) + Brs =
      fs "ring_switch_weight" + [64 * (count + 1)].sum + Brs := by simp
  rw [e]
  refine B1.CompleteAtDTB.toCompleteAtB (completeAt_flatDTB (fs := fs) (cert := cert) find_rsw
    rsw_not_loop κ _ _ _ rsw_body' rsw_flat rsw_addrs [64 * (count + 1)] (fun _ ↦ [rswChain zs ps count])
    (fun _ ↦ by simpa using rswChain_le zs ps count)
    (fun fp ↦ [⟨"rs_eq_run", true, [ofK (addressOfIndex (fp + fs "ring_switch_weight")), ofK
        (addressOfIndex bz),
      ofK (addressOfIndex bp), gen ^ count], rsLin (fp + fs "ring_switch_weight") bz bp count zs ps,
      Returns [ofK (addressOfIndex (fp + fs "ring_switch_weight")) * gen ^ (64 * rswH count)]⟩])
    (fun _ => True) [fun _ => True] [Brs] Brs ?_ (fun _ => by simp [kidsBoundL]) (fun _ => le_rfl)
    ?_ ?_ ?_)
  · intro fp
    refine ⟨fun _ => ?_, trivial⟩
    exact (completeAt_of_rel_pureBat rs_pure (by simp [rsPureNames]) (fun rd hL ↦ rs_rel hcount hz hp hL) κ
      fun rd t hn hv hb => hrs rd t _ _ hn rfl hv hb).toDTB
  · intro fp k hk _ i hi
    rw [List.mem_singleton] at hk
    subst hk
    obtain ⟨q, hq, hi⟩ := hi
    simp only [rsLin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Or.inr ⟨_, by simp [bufL, bases], hi⟩
    · exact Or.inl ⟨_, by simp, hi⟩
    · exact Or.inl ⟨_, by simp, hi⟩
  · intro fp rd hB hLin k hk
    rw [List.mem_singleton] at hk
    subst hk
    intro q hq
    simp only [rsLin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hB (fp + fs "ring_switch_weight", rswChain zs ps count) (by simp [bufL, bases])
    · exact hLin (bz, zs) (by simp)
    · exact hLin (bp, ps) (by simp)
  · intro fp outs ho rd _ hB hLin
    have hzs : ReadsAt rd (ofK (addressOfIndex bz)) zs := hLin (bz, zs) (by simp)
    have hps : ReadsAt rd (ofK (addressOfIndex bp)) ps := hLin (bp, ps) (by simp)
    have hcs : ReadsAt rd (ofK (addressOfIndex bc)) cs := hLin (bc, cs) (by simp)
    have hch : ReadsAt rd (ofK (addressOfIndex (fp + fs "ring_switch_weight"))) (rswChain zs ps
        count) :=
      hB (fp + fs "ring_switch_weight", rswChain zs ps count) (by simp [bufL, bases])
    rcases outs with _ | ⟨o, _ | ⟨o', os⟩⟩
    · exact absurd ho (by simp [OutsOk])
    swap
    · exact absurd ho.2 (by simp [OutsOk])
    obtain ⟨ho', -⟩ := ho
    obtain ⟨ho1, -⟩ := ho' rfl
    obtain ⟨σ, hσdef⟩ : ∃ σ, σ = rswσ rd [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
        (addressOfIndex bc), gen ^ count]
        (fp + fs "ring_switch_weight") (rswH count) := ⟨_, rfl⟩
    obtain ⟨hat, h11, e12, e77, e333⟩ := rsw_block hcount hz hp hc hzs hps hcs hch
    rw [← hσdef] at hat h11 e12 e77 e333
    have hpar : ∀ i (hi : i < 4), σ (.n i) =
        [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^
            count].getD i 0 := by
      intro i hi
      rw [hσdef]
      exact ev_params rd _ (l := [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK
          (addressOfIndex bc), gen ^ count]) rsw_chk
        (by simpa using hi)
    have e0 := hpar 0 (by omega)
    have e1 := hpar 1 (by omega)
    have e2 := hpar 2 (by omega)
    have e3 := hpar 3 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3
    refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · show [Core.V.n 0, .n 1, .n 2, .n 3].map σ = _
      simp only [List.map_cons, List.map_nil, e0, e1, e2, e3]
    · intro s hs
      have := List.all_eq_true.mp rsw_noDisp s hs
      cases s <;> simp_all [DispOk]
    · rw [rsw_body']
      refine Fwd.holdsList_straight _ _ _ _ (fun s hs ↦ ?_) (by simp [e333])
      have hnd := List.all_eq_true.mp rsw_kinds s hs
      cases s with
      | atom a => exact hat a (rsw_atom_mem hs)
      | call f args rets =>
        have : Stmt.call f args rets = .call "rs_eq_run" [.n 12, .n 0, .n 1, .n 3] [.n 77] := by
          have h := rsw_callSF σ
          have hm : (Option.none, f, args, rets) ∈ rswPre.filterMap (Stmt.callSF σ) :=
            List.mem_filterMap.mpr ⟨_, hs, rfl⟩
          rw [h, List.mem_singleton] at hm
          simp only [Prod.mk.injEq] at hm
          obtain ⟨-, rfl, rfl, rfl⟩ := hm
          rfl
        rw [this]
        show coreProgram.Rel rd "rs_eq_run" [σ (.n 12), σ (.n 0), σ (.n 1), σ (.n 3)] [σ (.n 77)]
        rw [e12, e0, e1, e3, e77]
        exact rs_rel hcount hz hp (fun q hq ↦ by
          simp only [rsLin, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact hch
          · exact hzs
          · exact hps)
      | _ => simp [atomOrCall] at hnd
    · rw [rsw_allocs]
      simp only [List.map_cons, List.map_nil, Sum.elim_inr, h11, List.cons.injEq, and_true]
      exact logG_spec (by omega)
    · rw [rsw_allocs]
      simp [bases, e12]
    · unfold flatCalls
      rw [rsw_callSF]
      refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n 12), σ (.n 0), σ (.n 1), σ (.n 3)] = _
        rw [e12, e0, e1, e3]
      · show [σ (.n 77)] = o.1
        rw [ho1, e77]
    · intro q hq
      obtain ⟨hoff, hp'⟩ := rsw_loads_ok (rt_filterMap_of_loadsEv (by decide +kernel) hq)
      rcases hp' with h | h | h <;> rw [h]
      · rw [e2, Main.addr_ofK]
        exact ⟨_, rfl, Or.inl ⟨(bc, cs), by simp, by simp [hc]; omega⟩⟩
      · rw [e77, rt_addr_mul]
        exact ⟨_, rfl, Or.inr ⟨(fp + fs "ring_switch_weight", rswChain zs ps count),
          by simp [bufL, bases], by simp only [rswChain_length]; omega⟩⟩
      · rw [e12, Main.addr_ofK]
        exact ⟨_, rfl, Or.inr ⟨(fp + fs "ring_switch_weight", rswChain zs ps count),
          by simp [bufL, bases], by simp only [rswChain_length]; omega⟩⟩


end
end LeanVM.Guest.B1.VerifySub
