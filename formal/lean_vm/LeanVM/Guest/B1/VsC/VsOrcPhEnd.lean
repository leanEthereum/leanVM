/-
  LeanVM.Guest.B1.VsC.VsOrcPhEnd

  `vsKEndW` at the end of the honest phases: the posts from `Ph12` on against the honest pops' last ten entries.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPhOpen
public import LeanVM.Guest.B1.VsC.VsOrcBnd

/-!
# The end of the honest phases

The honest pops `vsPs` end in `replicate 8 [] ++ [mk, []]` past the `qs6 + 7` posts `Ph11` leaves (`vsPs_split`), so
the phases from `Ph12` on, adding eight quiet posts, `open_stacked`'s and `check_stack_terminal`'s quiet one, extend
`Bnd`'s prefix to the whole list (`forall₂_end`). **`VsCtx.kEndW`**: `vsKEndW` at the end state from `Bnd` and `Carry11`
at `Ph12`'s, `open_stacked`'s post giving `mk`'s pops, the overlay fact `VsFresh`, and the own words `h6 h9 h14 h240`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vs471_rc : vsRcs.lookup (.n 471) = none := by decide +kernel

/-- The honest pops' count before `Ph12`: the front's eleven (ten), then twelve. -/
noncomputable def qsOf (σ : Val) : ℕ := if σ (.n 471) = 0 then 16 else 15

/-- **The honest pops' last ten entries.** -/
theorem vsPs_split (σ : Val) (ch stk mk : List Pop) :
    vsPs σ ch stk mk = (vsPs σ ch stk mk).take (qsOf σ + 7) ++ (List.replicate 8 [] ++ [mk, []]) := by
  unfold vsPs qsOf
  split_ifs <;> rfl

/-- **The posts from `Ph12` on complete `Bnd`'s prefix.** -/
theorem forall₂_end {rd : Reader} {σ : Val} {ch stk mk : List Pop} {Qs : List (Reader → Tree → Prop)}
    {Qo : Reader → Tree → Prop}
    (h : List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t) Qs ((vsPs σ ch stk mk).take Qs.length))
    (hl : Qs.length = qsOf σ + 7) (ho : ∀ t, Qo rd t → PopsPost mk rd t) :
    List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t)
      (Qs ++ List.replicate 5 PostQuiet ++ [PostQuiet] ++ [PostQuiet, PostQuiet] ++ [Qo, PostQuiet])
      (vsPs σ ch stk mk) := by
  rw [vsPs_split σ ch stk mk, ← hl]
  have e : Qs ++ List.replicate 5 PostQuiet ++ [PostQuiet] ++ [PostQuiet, PostQuiet] ++ [Qo, PostQuiet] =
      Qs ++ [PostQuiet, PostQuiet, PostQuiet, PostQuiet, PostQuiet, PostQuiet, PostQuiet, PostQuiet, Qo, PostQuiet] := by
    simp only [List.append_assoc]; rfl
  rw [e]
  refine List.rel_append h ?_
  have q : ∀ t, PostQuiet rd t → PopsPost [] rd t := fun _ h => popsPost_quiet h
  exact .cons q (.cons q (.cons q (.cons q (.cons q (.cons q (.cons q (.cons q (.cons ho (.cons q .nil)))))))))

namespace VsCtx

variable {x : VsCtx}

theorem qsOf_rdOver (rd : Reader) : qsOf (rdOver x.σ0 rd) = x.qs6 := by
  simp only [qsOf, qs6, rdOver_eq vs471_rc]

/-- **`vsKEndW` at the end of the honest phases**: from `Bnd` and `Carry11` at `Ph12`'s state `st`, the end state's
posts those of `Ph12` on, its memories with `st.O`, `open_stacked`'s post giving `mk`'s pops, the overlay fact and the
own words. -/
theorem kEndW (hx : x.Hon) {st : St} (hb : x.Bnd st) (hc : x.Carry11 st) {layout : Layout} {rate : ℕ}
    (hann : announcedLayoutAndRate guestBytecode x.c.proof.stream = some (layout, rate))
    (hf : VsFresh x.rd1 x.rd0 x.w x.args) {a kc : ℕ} {O : Reader → Prop} {D : ℕ → Prop}
    {Qo : Reader → Tree → Prop} (hO : ∀ rd, O rd → st.O rd)
    (ho : ∀ rd, LowDef 17 rd → x.Pre rd → O rd → ∀ t, Qo rd t →
      PopsPost (Prover.merkleHints true (Prover.childQueries guestBytecode x.seed x.c) x.c.proof.openings) rd t)
    (h6 : ∀ rd, LowDef 17 rd → x.Pre rd → O rd →
      (Dest.heap (.n 6) 0 6).words rd (rdOver x.σ0 rd) = layout.tableLogHeights.map Prover.count)
    (h9 : ∀ rd, LowDef 17 rd → x.Pre rd → O rd → (Dest.heap (.n 9) 0 4).words rd (rdOver x.σ0 rd) = vsLinkShape layout)
    (h14 : ∀ rd, LowDef 17 rd → x.Pre rd → O rd →
      (Dest.heap (.n 14) 0 36).words rd (rdOver x.σ0 rd) = x.c.freshClaim.values)
    (h240 : ∀ rd, LowDef 17 rd → x.Pre rd → O rd → (Hint.bitsExp (.n 240) 24 (.heap (.n 8) 0 24)).Exact rd x.σ0) :
    vsKEndW 17 guestBytecode x.seed x.c x.qt x.qo x.σ0
      ⟨a, kc, O, D, st.Qs ++ List.replicate 5 PostQuiet ++ [PostQuiet] ++ [PostQuiet, PostQuiet] ++ [Qo, PostQuiet]⟩ := by
  have ha : x.args.length = 6 := rfl
  refine vsKEndW_honest (rd0 := x.rd0) (rd1 := x.rd1) (cur := x.cur) (ret := x.ret) (args := x.args) ha hx.hret hf hann
    (fun rd hl hp ho' => ?_) h6 h9 h14 h240
  have hq := hb.hQ rd hl hp (hO rd ho')
  simp only [vsPsH, hann] at hq
  exact forall₂_end hq (hc.1.trans (congrArg (· + 7) (qsOf_rdOver rd).symm)) (ho rd hl hp ho')

end VsCtx

end
end LeanVM.Guest.B1.VsC
