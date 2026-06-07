use backend::PackedValue;

use backend::*;

pub(super) enum LayerStorage<'a, EF: ExtensionField<PF<EF>>> {
    Initial {
        nums: ArenaCow<'a, PFPacking<EF>>,
        dens: ArenaCow<'a, EFPacking<EF>>,
        chunk_log: usize,
    },
    PackedBr {
        nums: ArenaCow<'a, EFPacking<EF>>,
        dens: ArenaCow<'a, EFPacking<EF>>,
        chunk_log: usize,
    },
    Natural {
        nums: ArenaCow<'a, EF>,
        dens: ArenaCow<'a, EF>,
    },
}

impl<'a, EF: ExtensionField<PF<EF>>> LayerStorage<'a, EF> {
    pub(super) fn convert_to_natural(&self) -> Self {
        match self {
            Self::Initial { nums, dens, chunk_log } => {
                let n_nat_base: ArenaVec<EF> = unpack_base_and_unreverse_active::<EF>(nums.as_ref(), *chunk_log);
                let d_nat = unpack_and_unreverse_active::<EF>(dens.as_ref(), *chunk_log);
                Self::Natural {
                    nums: ArenaCow::Owned(n_nat_base),
                    dens: ArenaCow::Owned(d_nat),
                }
            }
            Self::PackedBr { nums, dens, chunk_log } => {
                let n_nat = unpack_and_unreverse_active::<EF>(nums.as_ref(), *chunk_log);
                let d_nat = unpack_and_unreverse_active::<EF>(dens.as_ref(), *chunk_log);
                Self::Natural {
                    nums: ArenaCow::Owned(n_nat),
                    dens: ArenaCow::Owned(d_nat),
                }
            }
            Self::Natural { nums, dens } => Self::Natural {
                nums: ArenaCow::Owned(ArenaVec::from_slice(nums.as_ref())),
                dens: ArenaCow::Owned(ArenaVec::from_slice(dens.as_ref())),
            },
        }
    }

    pub(super) fn sum_quotients_2_by_2(&self) -> Self {
        match self {
            Self::Initial { nums, dens, chunk_log } => {
                let (new_nums, new_dens) =
                    sum_quotients_2_by_2_packed_br::<EF, _>(nums.as_ref(), dens.as_ref(), *chunk_log);
                Self::PackedBr {
                    nums: ArenaCow::Owned(new_nums),
                    dens: ArenaCow::Owned(new_dens),
                    chunk_log: *chunk_log - 1,
                }
            }
            Self::PackedBr { nums, dens, chunk_log } => {
                let (new_nums, new_dens) =
                    sum_quotients_2_by_2_packed_br::<EF, _>(nums.as_ref(), dens.as_ref(), *chunk_log);
                Self::PackedBr {
                    nums: ArenaCow::Owned(new_nums),
                    dens: ArenaCow::Owned(new_dens),
                    chunk_log: *chunk_log - 1,
                }
            }
            Self::Natural { nums, dens } => {
                let (nn, nd) = sum_quotients_2_by_2(nums.as_ref(), dens.as_ref());
                Self::Natural {
                    nums: ArenaCow::Owned(nn),
                    dens: ArenaCow::Owned(nd),
                }
            }
        }
    }

    pub(super) fn chunk_log(&self) -> usize {
        match self {
            Self::Initial { chunk_log, .. } => *chunk_log,
            Self::PackedBr { chunk_log, .. } => *chunk_log,
            Self::Natural { .. } => 0,
        }
    }

    pub fn materialise_in_full(self) -> (ArenaVec<EF>, ArenaVec<EF>) {
        let natural = match self {
            Self::Natural { .. } => self,
            other => other.convert_to_natural(),
        };
        let Self::Natural { nums, dens } = natural else {
            unreachable!()
        };
        let mut n = nums.into_owned();
        let mut d = dens.into_owned();
        let full = n.len().next_power_of_two();
        n.resize(full, EF::ZERO);
        d.resize(full, EF::ONE);
        (n, d)
    }
}

pub(super) fn bit_reverse_chunks<T: Copy + Send + Sync>(v: &[T], chunk_log: usize) -> ArenaVec<T> {
    let n = v.len();
    let chunk_size = 1usize << chunk_log;
    debug_assert!(n.is_multiple_of(chunk_size));
    let mut out: ArenaVec<T> = unsafe { ArenaVec::uninitialized(n) };
    if chunk_log == 0 {
        out.copy_from_slice(v);
        return out;
    }
    let shift = usize::BITS as usize - chunk_log;
    parallel::par_chunks_mut(&mut out, chunk_size, |c, dst| {
        let src = &v[c * chunk_size..][..chunk_size];
        for (p, slot) in dst.iter_mut().enumerate() {
            *slot = src[p.reverse_bits() >> shift];
        }
    });
    out
}

fn sum_quotients_2_by_2<EF: ExtensionField<PF<EF>>>(nums: &[EF], dens: &[EF]) -> (ArenaVec<EF>, ArenaVec<EF>) {
    assert_eq!(nums.len(), dens.len());
    let active_len = nums.len();
    let new_active = active_len.div_ceil(2);
    let full_pairs = active_len / 2;

    let mut new_nums: ArenaVec<EF> = unsafe { ArenaVec::uninitialized(new_active) };
    let mut new_dens: ArenaVec<EF> = unsafe { ArenaVec::uninitialized(new_active) };

    parallel::par_for_each_mut2(
        &mut new_nums[..full_pairs],
        &mut new_dens[..full_pairs],
        |i, num, den| {
            let n0 = nums[2 * i];
            let n1 = nums[2 * i + 1];
            let d0 = dens[2 * i];
            let d1 = dens[2 * i + 1];
            *num = d1 * n0 + d0 * n1;
            *den = d0 * d1;
        },
    );

    // Boundary (at most one pair: a/b + 0/1 = a/b).
    if full_pairs < new_active {
        new_nums[full_pairs] = nums[2 * full_pairs];
        new_dens[full_pairs] = dens[2 * full_pairs];
    }

    (new_nums, new_dens)
}

fn sum_quotients_2_by_2_packed_br<EF: ExtensionField<PF<EF>>, N>(
    nums: &[N],
    dens: &[EFPacking<EF>],
    chunk_log: usize,
) -> (ArenaVec<EFPacking<EF>>, ArenaVec<EFPacking<EF>>)
where
    N: Copy + Send + Sync,
    EFPacking<EF>: Algebra<N>,
{
    let w = packing_log_width::<EF>();
    debug_assert!(chunk_log > w);
    debug_assert_eq!(nums.len(), dens.len());

    let bit = chunk_log - 1 - w;
    let stride = 1usize << bit;
    let lo_mask = stride - 1;

    let mut new_nums: ArenaVec<EFPacking<EF>> = unsafe { ArenaVec::uninitialized(nums.len() >> 1) };
    let mut new_dens: ArenaVec<EFPacking<EF>> = unsafe { ArenaVec::uninitialized(nums.len() >> 1) };

    parallel::par_for_each_mut2(&mut new_nums, &mut new_dens, |new_j, num_out, den_out| {
        let i_hi = new_j >> bit;
        let i_lo = new_j & lo_mask;
        let i0 = (i_hi << (bit + 1)) | i_lo;
        let i1 = i0 | stride;
        *num_out = dens[i1] * nums[i0] + dens[i0] * nums[i1];
        *den_out = dens[i0] * dens[i1];
    });

    (new_nums, new_dens)
}

pub(super) fn unpack_and_unreverse_active<EF: ExtensionField<PF<EF>>>(
    v: &[EFPacking<EF>],
    chunk_log: usize,
) -> ArenaVec<EF> {
    bit_reverse_chunks(&unpack_extension::<EF, ArenaVec<_>>(v), chunk_log)
}

fn unpack_base_and_unreverse_active<EF: ExtensionField<PF<EF>>>(v: &[PFPacking<EF>], chunk_log: usize) -> ArenaVec<EF> {
    let active_unpacked: ArenaVec<EF> = PFPacking::<EF>::unpack_slice(v).iter().map(|x| EF::from(*x)).collect();
    bit_reverse_chunks(&active_unpacked, chunk_log)
}
