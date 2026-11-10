import Rv64Verifier.Proofs.Pcs.VsoClimbBytes
import Rv64Verifier.Image
import Rv64Verifier.Proofs.Transcript.Openings

/-!
# The climb's copy of a sibling, at any alignment

A sibling's 32 bytes need not be 8-aligned (`Vec<[u8; 32]>`), so the climb's block at
`0x8000abfc`, which reads them a byte at a time, is checked here by the symbolic executor with
sub-doubleword loads at any address (`cfgA`): `abfcA_bytes` is the copy. A frame keeps a
digest's bytes when it misses the doublewords holding them (`DFrame.bytesU`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Contracts Rv64Verifier.Transcript Rv64Verifier.Runtime

def cfgA : Config := { noAlias := true, anyAlign := true }

def abfcA : Expect :=
  { steps := 95,
      pc := Rv64Verifier.Sym.E.c 0x000000008000ad78#64,
      regs := [(RiscvZkvm.Rv64.Reg.x1, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x1)),
               (RiscvZkvm.Rv64.Reg.x2, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
               (RiscvZkvm.Rv64.Reg.x3, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x3)),
               (RiscvZkvm.Rv64.Reg.x4, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x4)),
               (RiscvZkvm.Rv64.Reg.x5, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x5)),
               (RiscvZkvm.Rv64.Reg.x6, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x6)),
               (RiscvZkvm.Rv64.Reg.x7, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x7)),
               (RiscvZkvm.Rv64.Reg.x8, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x8)),
               (RiscvZkvm.Rv64.Reg.x9, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x9)),
               (RiscvZkvm.Rv64.Reg.x10,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                  (Rv64Verifier.Sym.E.c 0x00000000000002b0#64)),
               (RiscvZkvm.Rv64.Reg.x11,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.add)
                  (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2))
                  (Rv64Verifier.Sym.E.c 0x0000000000000370#64)),
               (RiscvZkvm.Rv64.Reg.x12, Rv64Verifier.Sym.E.c 0x0000000000000020#64),
               (RiscvZkvm.Rv64.Reg.x13,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                  (Rv64Verifier.Sym.E.ld
                    (Rv64Verifier.Sym.E.bin
                      (Rv64Verifier.Sym.BinOp.and)
                      (Rv64Verifier.Sym.E.bin
                        (Rv64Verifier.Sym.BinOp.add)
                        (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                        (Rv64Verifier.Sym.E.c 0x0000000000000004#64))
                      (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.and)
                    (Rv64Verifier.Sym.E.bin
                      (Rv64Verifier.Sym.BinOp.add)
                      (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                      (Rv64Verifier.Sym.E.c 0x0000000000000004#64))
                    (Rv64Verifier.Sym.E.c 0x0000000000000007#64))),
               (RiscvZkvm.Rv64.Reg.x14,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.or)
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.sll)
                    (Rv64Verifier.Sym.E.bin
                      (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                      (Rv64Verifier.Sym.E.ld
                        (Rv64Verifier.Sym.E.bin
                          (Rv64Verifier.Sym.BinOp.and)
                          (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.add)
                            (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                            (Rv64Verifier.Sym.E.c 0x0000000000000007#64))
                          (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                      (Rv64Verifier.Sym.E.bin
                        (Rv64Verifier.Sym.BinOp.and)
                        (Rv64Verifier.Sym.E.bin
                          (Rv64Verifier.Sym.BinOp.add)
                          (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                          (Rv64Verifier.Sym.E.c 0x0000000000000007#64))
                        (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                    (Rv64Verifier.Sym.E.c 0x0000000000000018#64))
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.sll)
                    (Rv64Verifier.Sym.E.bin
                      (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                      (Rv64Verifier.Sym.E.ld
                        (Rv64Verifier.Sym.E.bin
                          (Rv64Verifier.Sym.BinOp.and)
                          (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.add)
                            (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                            (Rv64Verifier.Sym.E.c 0x0000000000000006#64))
                          (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                      (Rv64Verifier.Sym.E.bin
                        (Rv64Verifier.Sym.BinOp.and)
                        (Rv64Verifier.Sym.E.bin
                          (Rv64Verifier.Sym.BinOp.add)
                          (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                          (Rv64Verifier.Sym.E.c 0x0000000000000006#64))
                        (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                    (Rv64Verifier.Sym.E.c 0x0000000000000010#64))),
               (RiscvZkvm.Rv64.Reg.x15,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.sll)
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                    (Rv64Verifier.Sym.E.ld
                      (Rv64Verifier.Sym.E.bin
                        (Rv64Verifier.Sym.BinOp.and)
                        (Rv64Verifier.Sym.E.bin
                          (Rv64Verifier.Sym.BinOp.add)
                          (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                          (Rv64Verifier.Sym.E.c 0x0000000000000007#64))
                        (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                    (Rv64Verifier.Sym.E.bin
                      (Rv64Verifier.Sym.BinOp.and)
                      (Rv64Verifier.Sym.E.bin
                        (Rv64Verifier.Sym.BinOp.add)
                        (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                        (Rv64Verifier.Sym.E.c 0x0000000000000007#64))
                      (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                  (Rv64Verifier.Sym.E.c 0x0000000000000018#64)),
               (RiscvZkvm.Rv64.Reg.x16,
                Rv64Verifier.Sym.E.bin
                  (Rv64Verifier.Sym.BinOp.sll)
                  (Rv64Verifier.Sym.E.bin
                    (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                    (Rv64Verifier.Sym.E.ld
                      (Rv64Verifier.Sym.E.bin
                        (Rv64Verifier.Sym.BinOp.and)
                        (Rv64Verifier.Sym.E.bin
                          (Rv64Verifier.Sym.BinOp.add)
                          (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                          (Rv64Verifier.Sym.E.c 0x000000000000000f#64))
                        (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                    (Rv64Verifier.Sym.E.bin
                      (Rv64Verifier.Sym.BinOp.and)
                      (Rv64Verifier.Sym.E.bin
                        (Rv64Verifier.Sym.BinOp.add)
                        (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                        (Rv64Verifier.Sym.E.c 0x000000000000000f#64))
                      (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                  (Rv64Verifier.Sym.E.c 0x0000000000000018#64)),
               (RiscvZkvm.Rv64.Reg.x17, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x17)),
               (RiscvZkvm.Rv64.Reg.x18, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
               (RiscvZkvm.Rv64.Reg.x19, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x19)),
               (RiscvZkvm.Rv64.Reg.x20, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x20)),
               (RiscvZkvm.Rv64.Reg.x21, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x21)),
               (RiscvZkvm.Rv64.Reg.x22, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x22)),
               (RiscvZkvm.Rv64.Reg.x23, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x23)),
               (RiscvZkvm.Rv64.Reg.x24, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x24)),
               (RiscvZkvm.Rv64.Reg.x25, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x25)),
               (RiscvZkvm.Rv64.Reg.x26, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x26)),
               (RiscvZkvm.Rv64.Reg.x27, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x27)),
               (RiscvZkvm.Rv64.Reg.x28, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x28)),
               (RiscvZkvm.Rv64.Reg.x29, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x29)),
               (RiscvZkvm.Rv64.Reg.x30, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x30)),
               (RiscvZkvm.Rv64.Reg.x31, Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x31))],
      mem := [({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                 off := 0x0000000000000290#64 },
               Rv64Verifier.Sym.E.bin
                 (Rv64Verifier.Sym.BinOp.or)
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.sll)
                   (Rv64Verifier.Sym.E.bin
                     (Rv64Verifier.Sym.BinOp.or)
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.or)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.sll)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                           (Rv64Verifier.Sym.E.ld
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.and)
                               (Rv64Verifier.Sym.E.bin
                                 (Rv64Verifier.Sym.BinOp.add)
                                 (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                                 (Rv64Verifier.Sym.E.c 0x0000000000000007#64))
                               (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000007#64))
                             (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                         (Rv64Verifier.Sym.E.c 0x0000000000000018#64))
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.sll)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                           (Rv64Verifier.Sym.E.ld
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.and)
                               (Rv64Verifier.Sym.E.bin
                                 (Rv64Verifier.Sym.BinOp.add)
                                 (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                                 (Rv64Verifier.Sym.E.c 0x0000000000000006#64))
                               (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000006#64))
                             (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                         (Rv64Verifier.Sym.E.c 0x0000000000000010#64)))
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.or)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.sll)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                           (Rv64Verifier.Sym.E.ld
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.and)
                               (Rv64Verifier.Sym.E.bin
                                 (Rv64Verifier.Sym.BinOp.add)
                                 (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                                 (Rv64Verifier.Sym.E.c 0x0000000000000005#64))
                               (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000005#64))
                             (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                         (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000004#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000004#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))))
                   (Rv64Verifier.Sym.E.c 0x0000000000000020#64))
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.or)
                   (Rv64Verifier.Sym.E.bin
                     (Rv64Verifier.Sym.BinOp.or)
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.sll)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000003#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000003#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                       (Rv64Verifier.Sym.E.c 0x0000000000000018#64))
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.sll)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000002#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000002#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                       (Rv64Verifier.Sym.E.c 0x0000000000000010#64)))
                   (Rv64Verifier.Sym.E.bin
                     (Rv64Verifier.Sym.BinOp.or)
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.sll)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000001#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000001#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                       (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                       (Rv64Verifier.Sym.E.ld
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                           (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.and)
                         (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                         (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))))),
              ({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                 off := 0x0000000000000298#64 },
               Rv64Verifier.Sym.E.bin
                 (Rv64Verifier.Sym.BinOp.or)
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.sll)
                   (Rv64Verifier.Sym.E.bin
                     (Rv64Verifier.Sym.BinOp.or)
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.or)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.sll)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                           (Rv64Verifier.Sym.E.ld
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.and)
                               (Rv64Verifier.Sym.E.bin
                                 (Rv64Verifier.Sym.BinOp.add)
                                 (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                                 (Rv64Verifier.Sym.E.c 0x000000000000000f#64))
                               (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x000000000000000f#64))
                             (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                         (Rv64Verifier.Sym.E.c 0x0000000000000018#64))
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.sll)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                           (Rv64Verifier.Sym.E.ld
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.and)
                               (Rv64Verifier.Sym.E.bin
                                 (Rv64Verifier.Sym.BinOp.add)
                                 (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                                 (Rv64Verifier.Sym.E.c 0x000000000000000e#64))
                               (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x000000000000000e#64))
                             (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                         (Rv64Verifier.Sym.E.c 0x0000000000000010#64)))
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.or)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.sll)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                           (Rv64Verifier.Sym.E.ld
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.and)
                               (Rv64Verifier.Sym.E.bin
                                 (Rv64Verifier.Sym.BinOp.add)
                                 (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                                 (Rv64Verifier.Sym.E.c 0x000000000000000d#64))
                               (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x000000000000000d#64))
                             (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                         (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x000000000000000c#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x000000000000000c#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))))
                   (Rv64Verifier.Sym.E.c 0x0000000000000020#64))
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.or)
                   (Rv64Verifier.Sym.E.bin
                     (Rv64Verifier.Sym.BinOp.or)
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.sll)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x000000000000000b#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x000000000000000b#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                       (Rv64Verifier.Sym.E.c 0x0000000000000018#64))
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.sll)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x000000000000000a#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x000000000000000a#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                       (Rv64Verifier.Sym.E.c 0x0000000000000010#64)))
                   (Rv64Verifier.Sym.E.bin
                     (Rv64Verifier.Sym.BinOp.or)
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.sll)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000009#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000009#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                       (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                       (Rv64Verifier.Sym.E.ld
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                           (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.and)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.add)
                           (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                           (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                         (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))))),
              ({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                 off := 0x00000000000002a0#64 },
               Rv64Verifier.Sym.E.bin
                 (Rv64Verifier.Sym.BinOp.or)
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.sll)
                   (Rv64Verifier.Sym.E.bin
                     (Rv64Verifier.Sym.BinOp.or)
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.or)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.sll)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                           (Rv64Verifier.Sym.E.ld
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.and)
                               (Rv64Verifier.Sym.E.bin
                                 (Rv64Verifier.Sym.BinOp.add)
                                 (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                                 (Rv64Verifier.Sym.E.c 0x0000000000000017#64))
                               (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000017#64))
                             (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                         (Rv64Verifier.Sym.E.c 0x0000000000000018#64))
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.sll)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                           (Rv64Verifier.Sym.E.ld
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.and)
                               (Rv64Verifier.Sym.E.bin
                                 (Rv64Verifier.Sym.BinOp.add)
                                 (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                                 (Rv64Verifier.Sym.E.c 0x0000000000000016#64))
                               (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000016#64))
                             (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                         (Rv64Verifier.Sym.E.c 0x0000000000000010#64)))
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.or)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.sll)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                           (Rv64Verifier.Sym.E.ld
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.and)
                               (Rv64Verifier.Sym.E.bin
                                 (Rv64Verifier.Sym.BinOp.add)
                                 (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                                 (Rv64Verifier.Sym.E.c 0x0000000000000015#64))
                               (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000015#64))
                             (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                         (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000014#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000014#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))))
                   (Rv64Verifier.Sym.E.c 0x0000000000000020#64))
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.or)
                   (Rv64Verifier.Sym.E.bin
                     (Rv64Verifier.Sym.BinOp.or)
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.sll)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000013#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000013#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                       (Rv64Verifier.Sym.E.c 0x0000000000000018#64))
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.sll)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000012#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000012#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                       (Rv64Verifier.Sym.E.c 0x0000000000000010#64)))
                   (Rv64Verifier.Sym.E.bin
                     (Rv64Verifier.Sym.BinOp.or)
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.sll)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000011#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000011#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                       (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                       (Rv64Verifier.Sym.E.ld
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000010#64))
                           (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.and)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.add)
                           (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                           (Rv64Verifier.Sym.E.c 0x0000000000000010#64))
                         (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))))),
              ({ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                 off := 0x00000000000002a8#64 },
               Rv64Verifier.Sym.E.bin
                 (Rv64Verifier.Sym.BinOp.or)
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.sll)
                   (Rv64Verifier.Sym.E.bin
                     (Rv64Verifier.Sym.BinOp.or)
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.or)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.sll)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                           (Rv64Verifier.Sym.E.ld
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.and)
                               (Rv64Verifier.Sym.E.bin
                                 (Rv64Verifier.Sym.BinOp.add)
                                 (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                                 (Rv64Verifier.Sym.E.c 0x000000000000001f#64))
                               (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x000000000000001f#64))
                             (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                         (Rv64Verifier.Sym.E.c 0x0000000000000018#64))
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.sll)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                           (Rv64Verifier.Sym.E.ld
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.and)
                               (Rv64Verifier.Sym.E.bin
                                 (Rv64Verifier.Sym.BinOp.add)
                                 (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                                 (Rv64Verifier.Sym.E.c 0x000000000000001e#64))
                               (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x000000000000001e#64))
                             (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                         (Rv64Verifier.Sym.E.c 0x0000000000000010#64)))
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.or)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.sll)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                           (Rv64Verifier.Sym.E.ld
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.and)
                               (Rv64Verifier.Sym.E.bin
                                 (Rv64Verifier.Sym.BinOp.add)
                                 (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                                 (Rv64Verifier.Sym.E.c 0x000000000000001d#64))
                               (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x000000000000001d#64))
                             (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                         (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x000000000000001c#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x000000000000001c#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))))
                   (Rv64Verifier.Sym.E.c 0x0000000000000020#64))
                 (Rv64Verifier.Sym.E.bin
                   (Rv64Verifier.Sym.BinOp.or)
                   (Rv64Verifier.Sym.E.bin
                     (Rv64Verifier.Sym.BinOp.or)
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.sll)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x000000000000001b#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x000000000000001b#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                       (Rv64Verifier.Sym.E.c 0x0000000000000018#64))
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.sll)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x000000000000001a#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x000000000000001a#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                       (Rv64Verifier.Sym.E.c 0x0000000000000010#64)))
                   (Rv64Verifier.Sym.E.bin
                     (Rv64Verifier.Sym.BinOp.or)
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.sll)
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                         (Rv64Verifier.Sym.E.ld
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.and)
                             (Rv64Verifier.Sym.E.bin
                               (Rv64Verifier.Sym.BinOp.add)
                               (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                               (Rv64Verifier.Sym.E.c 0x0000000000000019#64))
                             (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000019#64))
                           (Rv64Verifier.Sym.E.c 0x0000000000000007#64)))
                       (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                     (Rv64Verifier.Sym.E.bin
                       (Rv64Verifier.Sym.BinOp.ldx (Rv64Verifier.Sym.LoadKind.bu))
                       (Rv64Verifier.Sym.E.ld
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.and)
                           (Rv64Verifier.Sym.E.bin
                             (Rv64Verifier.Sym.BinOp.add)
                             (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                             (Rv64Verifier.Sym.E.c 0x0000000000000018#64))
                           (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)))
                       (Rv64Verifier.Sym.E.bin
                         (Rv64Verifier.Sym.BinOp.and)
                         (Rv64Verifier.Sym.E.bin
                           (Rv64Verifier.Sym.BinOp.add)
                           (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                           (Rv64Verifier.Sym.E.c 0x0000000000000018#64))
                         (Rv64Verifier.Sym.E.c 0x0000000000000007#64))))))],
      writes := [{ base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                   off := 0x0000000000000290#64 },
                 { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                   off := 0x0000000000000298#64 },
                 { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                   off := 0x00000000000002a0#64 },
                 { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                   off := 0x00000000000002a8#64 }],
      obl := [Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000290#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000007#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000007#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000007#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000298#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000007#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000006#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000006#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000006#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000298#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000006#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000004#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000004#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000004#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000298#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000004#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000005#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000005#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000005#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000298#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000005#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000298#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000000#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000003#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000003#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000003#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000298#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000003#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000002#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000002#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000002#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000298#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000002#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000001#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000001#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000001#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000298#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000001#64 }
                1,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x0000000000000298#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x000000000000000f#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x000000000000000f#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x000000000000000f#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x000000000000000e#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x000000000000000e#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x000000000000000e#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x000000000000000d#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x000000000000000d#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x000000000000000d#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x000000000000000c#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x000000000000000c#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x000000000000000c#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x000000000000000b#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x000000000000000b#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x000000000000000b#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x000000000000000a#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x000000000000000a#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x000000000000000a#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000008#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000008#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000009#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000009#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000009#64 }
                1,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a0#64 }
                8,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000017#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000017#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000016#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000016#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000015#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000015#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000014#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000014#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000013#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000013#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000012#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000012#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000010#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000010#64 }
                1,
              Rv64Verifier.Sym.Oblig.ne
                { base := some (Rv64Verifier.Sym.E.bin
                            (Rv64Verifier.Sym.BinOp.and)
                            (Rv64Verifier.Sym.E.bin
                              (Rv64Verifier.Sym.BinOp.add)
                              (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18))
                              (Rv64Verifier.Sym.E.c 0x0000000000000011#64))
                            (Rv64Verifier.Sym.E.c 0xfffffffffffffff8#64)),
                  off := 0x0000000000000000#64 }
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 },
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000011#64 }
                1,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x2)),
                  off := 0x00000000000002a8#64 }
                8,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x000000000000001f#64 }
                1,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x000000000000001e#64 }
                1,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x000000000000001d#64 }
                1,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x000000000000001c#64 }
                1,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x000000000000001b#64 }
                1,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x000000000000001a#64 }
                1,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000018#64 }
                1,
              Rv64Verifier.Sym.Oblig.valid
                { base := some (Rv64Verifier.Sym.E.reg (RiscvZkvm.Rv64.Reg.x18)),
                  off := 0x0000000000000019#64 }
                1] }

theorem abfcA_spec : BlockSpec Image.code 0x000000008000abfc#64 95
    (fun s ↦ Oblig.all s abfcA.obl) abfcA.Holds :=
  BlockSpec.of_expect (cfg := cfgA) (fuel := 95) (x := abfcA)
    (words := (Image.code.words.drop 11007).take 95) (by decide +kernel)
    (CodeAt.slice Image.code 11007 95 0x000000008000abfc#64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)) (fun _ h ↦ h) (fun _ _ _ h ↦ h)

theorem abfcA_x10 {s t : MachineState} (h : abfcA.Holds s t) :
    t.getReg .x10 = s.getReg .x2 + 688 :=
  h.reg_eq .x10 rfl (by rv_eval [])

theorem abfcA_x11 {s t : MachineState} (h : abfcA.Holds s t) :
    t.getReg .x11 = s.getReg .x2 + 880 :=
  h.reg_eq .x11 rfl (by rv_eval [])

theorem abfcA_x12 {s t : MachineState} (h : abfcA.Holds s t) :
    t.getReg .x12 = 32 :=
  h.reg_eq .x12 rfl (by rv_eval [])

theorem abfcA_keeps {s t : MachineState} (h : abfcA.Holds s t) :
    ∀ r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg), t.getReg r = s.getReg r :=
  h.keeps rfl

theorem abfcA_pc {s t : MachineState} (h : abfcA.Holds s t) : t.pc = 0x8000ad78 :=
  h.pc_eq rfl

theorem abfcA_frame {s t : MachineState} (h : abfcA.Holds s t) (hb : (s.getReg .x2).toNat + 688 ≤ 2 ^ 64) :
    MemFrame s t (s.getReg .x2 + 656) 32 :=
  h.memFrame (by rv_eval []; and_intros <;> addr_omega [hb])

/-! ## Bytes at any alignment -/

theorem toNat_f8 (a : Word) : (a &&& (18446744073709551608 : Word)).toNat = a.toNat - a.toNat % 8 := by
  rw [show (18446744073709551608 : Word) = ~~~7#64 by decide]
  exact Sym.alignToDword_toNat a

/-- A doubleword key apart from `b`'s eight bytes. -/
theorem f8_ne {a b : Word} (h : b.toNat + 8 ≤ a.toNat - a.toNat % 8 ∨ a.toNat < b.toNat) :
    a &&& (18446744073709551608 : Word) ≠ b := by
  intro e
  have := congrArg BitVec.toNat e
  rw [toNat_f8] at this
  omega

theorem validAccess_one {a : Word}
    (h : (0x20 ≤ a.toNat ∧ a.toNat < 0x78000000) ∨ (0xa0000000 ≤ a.toNat ∧ a.toNat < 0xc0000000)) :
    Sym.validAccess 1 a = true := by
  simp only [Sym.validAccess, isValidByteAccess, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

/-- The bytes inside the doublewords holding them are mapped. -/
theorem mapped_of_wide {p : Word} {n : ℕ} (hn : n ≠ 0) (h : Region (alignToDword p) (sibSpan p n)) :
    Mapped p (32 * n) := by
  have hal := Sym.alignToDword_toNat p
  simp only [Region, Mapped, sibSpan] at h ⊢
  omega

/-- What misses the doublewords holding bytes misses the bytes. -/
theorem apart_of_wide {p b : Word} {n m : ℕ} (h : Apart (alignToDword p) (sibSpan p n) b m) :
    Apart p (32 * n) b m := by
  have hal := Sym.alignToDword_toNat p
  simp only [Apart, sibSpan] at h ⊢
  omega

/-- 32 bytes that a frame missing the doublewords holding them keeps. -/
theorem DFrame.bytesU {u v : MachineState} {X : Word → Prop} (hX : DFrame u v X) {a : Word}
    (hw : (alignToDword a).toNat + Transcript.sibSpan a 1 ≤ 2 ^ 64)
    (hm : ∀ y, Within y (alignToDword a) (Transcript.sibSpan a 1) → ¬ X y) :
    Contracts.bytesAt v a 32 = Contracts.bytesAt u a 32 := by
  simp only [Contracts.bytesAt]
  refine List.map_congr_left fun i hi ↦ ?_
  simp only [List.mem_range] at hi
  refine Transcript.getByte_congr (hX _ fun j hj hx ↦ hm _ ?_ hx)
  have hal := Sym.alignToDword_toNat (a + BitVec.ofNat 64 i)
  have hal0 := Sym.alignToDword_toNat a
  addr_omega [hw, hi, hj, hal, hal0]

/-- A digest read as bytes that a frame missing the doublewords holding them keeps. -/
theorem DFrame.digestU {u v : MachineState} {X : Word → Prop} (hX : DFrame u v X) {a : Word}
    (hw : (alignToDword a).toNat + Transcript.sibSpan a 1 ≤ 2 ^ 64)
    (hm : ∀ y, Within y (alignToDword a) (Transcript.sibSpan a 1) → ¬ X y) :
    digestBytesAt v a = digestBytesAt u a := by
  unfold digestBytesAt
  congr 1
  funext l
  congr 1
  unfold Contracts.bytesAt
  refine List.map_congr_left fun m hm' ↦ ?_
  simp only [List.mem_range] at hm'
  refine Transcript.getByte_congr (hX _ fun k hk hx ↦ hm _ ?_ hx)
  have hal := Sym.alignToDword_toNat (a + BitVec.ofNat 64 (8 * l.val) + BitVec.ofNat 64 m)
  have hal0 := Sym.alignToDword_toNat a
  have hl := l.isLt
  addr_omega [hw, hk, hl, hm', hal, hal0]

/-! ## The copy -/

/-- A doubleword from eight bytes, as the climb's blocks assemble it. -/
def ofBytes8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : Word :=
  (BitVec.zeroExtend 64 b7 <<< ((24#64).toNat % 64) ||| BitVec.zeroExtend 64 b6 <<< ((16#64).toNat % 64) |||
      (BitVec.zeroExtend 64 b5 <<< ((8#64).toNat % 64) ||| BitVec.zeroExtend 64 b4)) <<< ((32#64).toNat % 64) |||
    (BitVec.zeroExtend 64 b3 <<< ((24#64).toNat % 64) ||| BitVec.zeroExtend 64 b2 <<< ((16#64).toNat % 64) |||
      (BitVec.zeroExtend 64 b1 <<< ((8#64).toNat % 64) ||| BitVec.zeroExtend 64 b0))

theorem ofBytes8_byte (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) {j : ℕ} (hj : j < 8) :
    extractByte (ofBytes8 b0 b1 b2 b3 b4 b5 b6 b7) j = [b0, b1, b2, b3, b4, b5, b6, b7].getD j 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofBytes8, Runtime.getLsbD_extractByte, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.zeroExtend_eq_setWidth]
  interval_cases j <;> interval_cases i <;> simp

/-- A byte, as a load at any address reads it. -/
theorem getByte_ldx (s : MachineState) (a : Word) :
    s.getByte a = extractByte (s.getMem (a &&& 0xfffffffffffffff8#64)) (a &&& 7#64).toNat := by
  rw [MachineState.getByte, alignToDword, byteOffset, show (~~~7#64 : Word) = 0xfffffffffffffff8#64 by
    decide]

/-- 32 bytes from an aligned `a`, each the byte of `s` at the same place from `b`. -/
theorem bytesAt_of_extract {s t : MachineState} {a b : Word} (ha : a.toNat % 8 = 0)
    (h : ∀ m < 4, ∀ j < 8, extractByte (t.getMem (a + BitVec.ofNat 64 (8 * m))) j =
      s.getByte (b + BitVec.ofNat 64 (8 * m + j))) :
    Contracts.bytesAt t a 32 = Contracts.bytesAt s b 32 := by
  have hal (m : ℕ) : (a + BitVec.ofNat 64 (8 * m)).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [Contracts.bytesAt]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  have e : a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [e, getByte_aligned t (hal _) (Nat.mod_lt _ (by omega)), h (i / 8) (by omega) (i % 8)
    (Nat.mod_lt _ (by omega)), show 8 * (i / 8) + i % 8 = i by omega]

/-- The block's obligations: the 32 bytes from `x18` mapped and apart from the stack slots it
writes. -/
theorem abfcA_obl {s : MachineState} (h18 : Mapped (s.getReg .x18) 32)
    (hap : (s.getReg .x18).toNat + 32 ≤ (s.getReg .x2).toNat + 656 ∨
      (s.getReg .x2).toNat + 688 ≤ (s.getReg .x18).toNat - (s.getReg .x18).toNat % 8)
    (hv : Sym.validAccess 8 (s.getReg .x2 + 656) = true ∧ Sym.validAccess 8 (s.getReg .x2 + 664) = true ∧
      Sym.validAccess 8 (s.getReg .x2 + 672) = true ∧ Sym.validAccess 8 (s.getReg .x2 + 680) = true)
    (hw : (s.getReg .x2).toNat + 688 ≤ 2 ^ 64) : Oblig.all s abfcA.obl := by
  simp only [Mapped] at h18
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  rv_eval []
  and_intros
  all_goals first
    | with_reducible exact hv1
    | with_reducible exact hv2
    | with_reducible exact hv3
    | with_reducible exact hv4
    | exact f8_ne (by addr_omega [h18, hap, hw])
    | exact validAccess_one (by addr_omega [h18])

/-- **The copy**: the 32 bytes from `x18` to `S + 656`, at any alignment of `x18`. -/
theorem abfcA_bytes {s t : MachineState} (h : abfcA.Holds s t) (h8 : (s.getReg .x2).toNat % 8 = 0)
    (hw : (s.getReg .x2).toNat + 688 ≤ 2 ^ 64) :
    Contracts.bytesAt t (s.getReg .x2 + 656) 32 = Contracts.bytesAt s (s.getReg .x18) 32 := by
  refine bytesAt_of_extract (by addr_omega [h8, hw]) fun m hm j hj ↦ ?_
  simp only [getByte_ldx]
  interval_cases m
  · have e := h.mem_eq (a := s.getReg .x2 + 656) 0 (by decide) (by rv_eval []) rfl
    simp only [reduceMem, List.getElem_cons_zero, Sym.E.eval, Sym.BinOp.eval,
      Sym.LoadKind.fromWord] at e
    rw [show s.getReg .x2 + 656 + BitVec.ofNat 64 (8 * 0) = s.getReg .x2 + 656 by
      rw [BitVec.add_assoc]; rfl, e]
    refine (ofBytes8_byte _ _ _ _ _ _ _ _ hj).trans ?_
    interval_cases j <;> first
      | rfl
      | simp only [List.getD_cons_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero]
  · have e := h.mem_eq (a := s.getReg .x2 + 664) 1 (by decide) (by rv_eval []) rfl
    simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval, Sym.BinOp.eval,
      Sym.LoadKind.fromWord] at e
    rw [show s.getReg .x2 + 656 + BitVec.ofNat 64 (8 * 1) = s.getReg .x2 + 664 by
      rw [BitVec.add_assoc]; rfl, e]
    refine (ofBytes8_byte _ _ _ _ _ _ _ _ hj).trans ?_
    interval_cases j <;> rfl
  · have e := h.mem_eq (a := s.getReg .x2 + 672) 2 (by decide) (by rv_eval []) rfl
    simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval, Sym.BinOp.eval,
      Sym.LoadKind.fromWord] at e
    rw [show s.getReg .x2 + 656 + BitVec.ofNat 64 (8 * 2) = s.getReg .x2 + 672 by
      rw [BitVec.add_assoc]; rfl, e]
    refine (ofBytes8_byte _ _ _ _ _ _ _ _ hj).trans ?_
    interval_cases j <;> rfl
  · have e := h.mem_eq (a := s.getReg .x2 + 680) 3 (by decide) (by rv_eval []) rfl
    simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval, Sym.BinOp.eval,
      Sym.LoadKind.fromWord] at e
    rw [show s.getReg .x2 + 656 + BitVec.ofNat 64 (8 * 3) = s.getReg .x2 + 680 by
      rw [BitVec.add_assoc]; rfl, e]
    refine (ofBytes8_byte _ _ _ _ _ _ _ _ hj).trans ?_
    interval_cases j <;> rfl

end Rv64Verifier.Proofs.Pcs.Vso
