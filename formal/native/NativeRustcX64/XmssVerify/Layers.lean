module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Memset.Names
public import NativeRustcX64.Code.Common.Update.Names
public import NativeRustcX64.Code.Xmss.WotsLeaf.Names

public import NativeRustcX64.XmssVerify.TopRun
public import NativeRustcX64.XmssVerify.Tree1Run
public import NativeRustcX64.XmssVerify.Epilogue

/-!
# `xmss_verify`: the two layers composed (x86-64)

`layers`: from `Parsed` at block 5, the bottom layer's leaf and path (`bottom`, `loop0`), the top
layer's (`top`, `loop1`) and the comparison with the key's root (`final`), or the failure where a
layer's one-time leaf is `None` (`fail`); RAX is `xmssVerify`'s result (`xmssVerify_eq`).
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym NativeRustc NativeRustc.Xmss

set_option Elab.async false

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

/-- **The layers**: from block 5 with the parsed signature, the return with `xmssVerify`'s result
in RAX. -/
public theorem layers {k : Nat} (hp : Placed code k)
    (hset : Spec (label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost)
    (hcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hupd : Spec (label NativeRustcX64.Common.Update.entryLabel) UpdatePre UpdatePost)
    (hfin : Spec (label NativeRustcX64.Common.Finalize.entryLabel) FinalizePre FinalizePost)
    (hwots : Spec (label NativeRustcX64.Xmss.WotsLeaf.entryLabel) WotsLeafPre WotsLeafPost) (P : Pre w m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.XmssVerify.b5Offset)) (h : Parsed w m₀ st.data) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m₀ ∧
      rspOf st'.data = rspOf m₀ + 8#64 ∧ reg st'.data .rax = (if xmssVerify w then 1 else 0) ∧
      SameOutside m₀.dmem st'.data.dmem
        (InRange (stackBelow m₀ xmssVerifyStack) xmssVerifyStack) ∧
      Saved m₀ st'.data) st :=
  bottom hp hwots hcpy P hpc h (fun _ hpc' F => fail hp P hpc' F)
    fun _ _ _ hl0 hpc₁ T0 =>
      Eventually.bind (loop0 hp hset hupd hcpy hfin P (wotsLeaf_length hl0).2 hpc₁ T0)
        fun _ ⟨hpc₂, T0'⟩ =>
          top hp hwots P hl0 hpc₂ T0' (fun _ hpc' F => fail hp P hpc' F)
            fun _ _ _ hl1 hpc₃ T1 =>
              Eventually.bind (loop1 hp hset hupd hcpy hfin P (wotsLeaf_length hl1).2 hpc₃ T1)
                fun _ ⟨hpc₄, T1'⟩ =>
                  Eventually.mono (final hp P hpc₄ T1') fun _ ⟨h1, h2, h3, h4, h5⟩ =>
                    ⟨h1, h2, by
                      rw [h3, xmssVerify_eq]
                      simp only [layerRoot0 hl0, layerRoot1 hl1], h4, h5⟩

end NativeRustcX64.Xmss.XmssVerify
