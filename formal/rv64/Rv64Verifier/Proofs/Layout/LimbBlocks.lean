import Rv64Verifier.Proofs.Layout.LimbTail
import Rv64Verifier.Proofs.Layout.CellLanes

/-!
# `flushes_keccak`'s `limb` closure: the summing blocks, split

`0x80004f34`, `0x80004f88` and `0x80004fdc` copy a summand's buffer and length through `s2` to
`sp' + 128` and then read them back from `sp' + 128`; their generated blocks read the old words
(`s2` is `sp' + 128`), so each is split after its two stores.
-/

namespace Rv64Verifier.Layout.Limb
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Runtime
open Rv64Verifier.Runtime.Memcpy (keepE)
open Rv64Verifier.Layout.CellLanes (cfgN spec_ofN)

/-- `addi a1, sp, o; ld a2, 0(a1); ld a1, 8(a1); sd a2, 0(s2); sd a1, 8(s2)`. -/
def copyE (o T : Word) : Expect where
  steps := 5
  pc := .c T
  regs := [(.x11, .ld (.bin .add (.reg .x2) (.c (o + 8)))), (.x12, .ld (.bin .add (.reg .x2) (.c o)))] ++
    keepE [.x11, .x12]
  mem := [(⟨some (.reg .x18), 8⟩, .ld (.bin .add (.reg .x2) (.c (o + 8)))),
    (⟨some (.reg .x18), 0⟩, .ld (.bin .add (.reg .x2) (.c o)))]
  writes := [⟨some (.reg .x18), 8⟩, ⟨some (.reg .x18), 0⟩]
  obl := [.valid ⟨some (.reg .x18), 8⟩ 8, .valid ⟨some (.reg .x18), 0⟩ 8,
    .valid ⟨some (.reg .x2), o + 8⟩ 8, .valid ⟨some (.reg .x2), o⟩ 8]

/-- `0x80004f34`: as `copyE 80`, and `a3 = 8`. -/
def copy0E : Expect where
  steps := 6
  pc := .c 0x80004f4c
  regs := [(.x10, .ld (.bin .add (.reg .x2) (.c 88))), (.x11, .ld (.bin .add (.reg .x2) (.c 80))),
    (.x13, .c 8)] ++ keepE [.x10, .x11, .x13]
  mem := [(⟨some (.reg .x18), 8⟩, .ld (.bin .add (.reg .x2) (.c 88))),
    (⟨some (.reg .x18), 0⟩, .ld (.bin .add (.reg .x2) (.c 80)))]
  writes := [⟨some (.reg .x18), 8⟩, ⟨some (.reg .x18), 0⟩]
  obl := [.valid ⟨some (.reg .x18), 8⟩ 8, .valid ⟨some (.reg .x18), 0⟩ 8,
    .valid ⟨some (.reg .x2), 88⟩ 8, .valid ⟨some (.reg .x2), 80⟩ 8]

/-- The sum `(a3, a4, a0)` and `r` stored at `sp + 96`, then `add_scaled(sp + 96, the copied
summand, ONE)`, returning to `T`. -/
def storeE (r : Reg) (T : Word) : Expect where
  steps := 11
  pc := .c 0x800119cc
  regs := [(.x1, .c T), (.x10, .bin .add (.reg .x2) (.c 96)),
    (.x11, .ld (.bin .add (.reg .x2) (.c 128))), (.x12, .ld (.bin .add (.reg .x2) (.c 136))),
    (.x13, .c 0xa00000b0)] ++ keepE [.x1, .x10, .x11, .x12, .x13]
  mem := [(⟨some (.reg .x2), 120⟩, .reg r), (⟨some (.reg .x2), 112⟩, .reg .x10),
    (⟨some (.reg .x2), 104⟩, .reg .x14), (⟨some (.reg .x2), 96⟩, .reg .x13)]
  writes := [⟨some (.reg .x2), 120⟩, ⟨some (.reg .x2), 112⟩, ⟨some (.reg .x2), 104⟩,
    ⟨some (.reg .x2), 96⟩]
  obl := [.valid ⟨some (.reg .x2), 120⟩ 8, .valid ⟨some (.reg .x2), 112⟩ 8,
    .valid ⟨some (.reg .x2), 104⟩ 8, .valid ⟨some (.reg .x2), 96⟩ 8,
    .valid ⟨some (.reg .x2), 136⟩ 8, .valid ⟨some (.reg .x2), 128⟩ 8]

/-- `0x80004f4c`: as `storeE`, the sum empty (`(0, a3, 0)`). -/
def store0E : Expect where
  steps := 11
  pc := .c 0x800119cc
  regs := [(.x1, .c 0x80004f78), (.x10, .bin .add (.reg .x2) (.c 96)),
    (.x11, .ld (.bin .add (.reg .x2) (.c 128))), (.x12, .ld (.bin .add (.reg .x2) (.c 136))),
    (.x13, .c 0xa00000b0)] ++ keepE [.x1, .x10, .x11, .x12, .x13]
  mem := [(⟨some (.reg .x2), 120⟩, .reg .x21), (⟨some (.reg .x2), 112⟩, .c 0),
    (⟨some (.reg .x2), 104⟩, .reg .x13), (⟨some (.reg .x2), 96⟩, .c 0)]
  writes := [⟨some (.reg .x2), 120⟩, ⟨some (.reg .x2), 112⟩, ⟨some (.reg .x2), 104⟩,
    ⟨some (.reg .x2), 96⟩]
  obl := [.valid ⟨some (.reg .x2), 120⟩ 8, .valid ⟨some (.reg .x2), 112⟩ 8,
    .valid ⟨some (.reg .x2), 104⟩ 8, .valid ⟨some (.reg .x2), 96⟩ 8,
    .valid ⟨some (.reg .x2), 136⟩ 8, .valid ⟨some (.reg .x2), 128⟩ 8]

theorem copy0_spec : BlockSpec Image.code 0x80004f34 6 (fun s ↦ Oblig.all s copy0E.obl) copy0E.Holds :=
  spec_ofN 5069 6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem store0_spec :
    BlockSpec Image.code 0x80004f4c 11 (fun s ↦ Oblig.all s store0E.obl) store0E.Holds :=
  spec_ofN 5075 11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem copy1_spec :
    BlockSpec Image.code 0x80004f88 5 (fun s ↦ Oblig.all s (copyE 56 0x80004f9c).obl)
      (copyE 56 0x80004f9c).Holds :=
  spec_ofN 5090 5 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem store1_spec :
    BlockSpec Image.code 0x80004f9c 11 (fun s ↦ Oblig.all s (storeE .x20 0x80004fc8).obl)
      (storeE .x20 0x80004fc8).Holds :=
  spec_ofN 5095 11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem copy2_spec :
    BlockSpec Image.code 0x80004fdc 5 (fun s ↦ Oblig.all s (copyE 32 0x80004ff0).obl)
      (copyE 32 0x80004ff0).Holds :=
  spec_ofN 5111 5 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem store2_spec :
    BlockSpec Image.code 0x80004ff0 11 (fun s ↦ Oblig.all s (storeE .x9 0x8000501c).obl)
      (storeE .x9 0x8000501c).Holds :=
  spec_ofN 5116 11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Rv64Verifier.Layout.Limb
