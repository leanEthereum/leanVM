module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Check

/-! # The output buffer header write in block 66 -/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.KeccakGkr.SeqZ NativeVm.Model
open NativeRustcVmX64.Ring
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVm.KeccakGkr (off)

public section

@[expose] def headerW (S : SState) : Bool := S.mem.all fun w ↦
  (w.r == 0 && decide (w.off + w.n ≤ 3344)) || (w.r == 4 && w.off == 0 && w.n == 8)

variable [Labels] {m0 : MachineData} {a : DecArea} {inst : Array EW}

omit [Labels] in
theorem headerW_ok {S : SState} (h : headerW S = true) :
    S.mem.all (writeOk 3344 (3368 :: (rsOf m0).map Prod.snd) wrAll) = true := by
  apply List.all_eq_true.mpr
  intro w hw
  have he := List.all_eq_true.mp h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
  rcases he with ⟨hr, hb⟩ | ⟨⟨hr, ho⟩, hn⟩
  · simp [writeOk, hr, hb]
  · simp [writeOk, hr, ho, hn, rsOf, wrAll]

theorem chg_header (c : Ctx a inst m0) {m m' : MachineData} {vals : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState}
    (hm : Match (envZ m0 m 3344 3368 (rsOf m0) vals ret) S m')
    (hwf : (envZ m0 m 3344 3368 (rsOf m0) vals ret).WF) (hw : headerW S = true) :
    Chg m0 m.dmem m'.dmem (wsL S) [(4, 0, 8)] := by
  intro q hq
  refine hm.get?_mem0 hwf fun hW ↦ hq ?_
  obtain ⟨w, hwm, b, sz, hb, h1, h2⟩ := hW
  have he := List.all_eq_true.mp hw w hwm
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
  rcases he with ⟨hr, hn⟩ | ⟨⟨hr, ho⟩, hn⟩
  · rw [hr] at hb
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    refine .inr (.inl ⟨(w.off, w.n), List.mem_map.mpr ⟨w, hwm, rfl⟩, ?_⟩)
    have he := off_fb c (o := w.off) (by omega)
    have hf := fb_toNat c
    have hs := c.sp
    have ht := c.top
    rw [vk_eq] at hs
    rw [NativeRustcX64.Sym.inRange_iff (by rw [he]; omega), he]
    change (fb m0).toNat + w.off ≤ q.toNat at h1
    change q.toNat < (fb m0).toNat + w.off + w.n at h2
    constructor <;> omega
  · rw [hr] at hb
    change some (keccakOutArg m0, 1608) = some (b, sz) at hb
    have hb' : keccakOutArg m0 = b := congrArg Prod.fst (Option.some.inj hb)
    rw [← hb'] at h1 h2
    refine chgR_reg List.mem_cons_self ?_
    simp only [off0, ob]
    rw [NativeRustcX64.Sym.inRange_iff (by have := c.oW; omega)]
    simp only [ho, hn, Nat.add_zero] at h1 h2
    exact ⟨h1, h2⟩

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
