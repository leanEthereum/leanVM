//! Conditional degree accounting; the proof obligations are recorded in `doc/leanvm/security.md`.

use crate::{class_flock, cpu, leaf, pcs, tables};
use ::pcs::whir_config::{SecurityTerms, WhirSecurityConfig};
use pcs::MAX_MU;
use primitives::field::F64;

/// Algebraic accounting for one actual public layout, without allocating its witness.
#[derive(Clone, Debug)]
pub struct Ledger {
    /// Conservative bus fingerprint and GKR degree sum.
    pub bus_degree: u128,
    /// Shared table batching, random-point detection and cubic sumcheck degree sum.
    pub table_degree: usize,
    /// Conservative zerocheck, lincheck and constant-pin degree sum per class.
    pub class_degrees: [usize; tables::N_TABLES],
    /// Upper bound on the shared power-batch degree for this layout.
    pub opening_batch_degree: usize,
    /// Negative log of the union bound for outer algebraic checks over the L0 list.
    ///
    /// Conditional on the auxiliary and class reductions' proof obligations.
    pub outer_algebraic_bits: f64,
    /// PCS terms in commitment order, including the initial batch degree bound.
    pub pcs: Vec<SecurityTerms>,
}

impl Ledger {
    /// Account for announced table heights in the protocol's class order.
    ///
    /// The report derives its layout and claim-count bound without trusting caller-supplied wiring.
    pub fn for_program(program: &cpu::Program, table_log_rows: &[usize], log_inv_rate: usize) -> Result<Self, String> {
        let taus: [usize; tables::N_TABLES] = table_log_rows.try_into().map_err(|_| "wrong number of table heights")?;
        for (t, &tau) in taus.iter().enumerate() {
            let floor = class_flock::n_blocks_log(tables::CLASSES[t], 1);
            if !(floor..=cpu::MAX_LOG_ROWS).contains(&tau) {
                return Err("table height is outside the verifier's bounds".into());
            }
        }
        let layout = cpu::layout(program.rv(), taus, F64::ONE);
        Self::for_layout(&layout, log_inv_rate)
    }

    fn for_layout(layout: &cpu::Layout, log_inv_rate: usize) -> Result<Self, String> {
        if !(pcs::MIN_MU..=MAX_MU).contains(&layout.shape.mu) {
            return Err("unsupported committed shape".into());
        }
        for (t, &tau) in layout.taus.iter().enumerate() {
            let floor = class_flock::n_blocks_log(tables::CLASSES[t], 1);
            if !(floor..=cpu::MAX_LOG_ROWS).contains(&tau) {
                return Err("table height is outside the verifier's bounds".into());
            }
        }
        let mut bus_mu = 0;
        for blocks in [&layout.push, &layout.pull, &layout.count] {
            let mut leaves = 0u128;
            for block in blocks {
                if block.kappa >= 64 {
                    return Err("bus block dimension exceeds the counter budget".into());
                }
                leaves = leaves
                    .checked_add(1u128 << block.kappa)
                    .ok_or("bus leaf count overflows")?;
            }
            let dimension = if leaves <= 1 {
                0
            } else {
                (u128::BITS - (leaves - 1).leading_zeros()) as usize
            };
            bus_mu = bus_mu.max(dimension);
        }
        if bus_mu >= 64 {
            return Err("bus exceeds the unground algebraic budget".into());
        }
        let bus_degree = leaf::soundness_degree_bound(bus_mu);
        let table_degree = cpu::xi_form_base() + 2 + 4 * layout.taus.iter().copied().max().unwrap_or(0);
        // The conservative Flock annex bound includes the random outer equality test and constant pin.
        let class_degrees = std::array::from_fn(|t| 5 * tables::CLASSES[t].k_log + 4 * layout.taus[t] + 93);
        // A framework column can appear once per suffix length; table columns add one claim each.
        let opening_claims_bound = cpu::schema().n * (bus_mu + 2) + 5 + tables::N_TABLES;
        let opening_batch_degree = opening_claims_bound - 1;
        let config =
            WhirSecurityConfig::derive_config_with_log_inv_rate(layout.shape.mu + ::pcs::LOG_PACKING, log_inv_rate)?;
        let pcs = config.security_terms(opening_batch_degree);
        // L0 is list binding; a fixed-witness degree bound must pay for every candidate witness.
        let outer_degree = bus_degree
            + table_degree as u128
            + class_degrees.iter().map(|&d| d as u128).sum::<u128>()
            + opening_batch_degree as u128;
        let outer_algebraic_bits = 192.0 - (outer_degree as f64).log2() - pcs[0].log2_list_size;
        Ok(Self {
            bus_degree,
            table_degree,
            class_degrees,
            opening_batch_degree,
            outer_algebraic_bits,
            pcs,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_layouts_pay_the_l0_list_and_every_class() {
        let program = cpu::Program::from_elf(include_bytes!("../../../programs/fibonacci/fibonacci.elf")).unwrap();
        let taus = std::array::from_fn(|t| class_flock::n_blocks_log(tables::CLASSES[t], 1));
        let layout = cpu::layout(program.rv(), taus, F64::ONE);
        let mut last_mu = 0;
        for extra in 0..=MAX_MU {
            let grown = cpu::layout(program.rv(), taus.map(|tau| tau + extra), F64::ONE);
            if grown.shape.mu > MAX_MU {
                assert!(Ledger::for_layout(&grown, pcs::TEST_LOG_INV_RATE).is_err());
                break;
            }
            last_mu = grown.shape.mu;
            for rate in pcs::MIN_LOG_INV_RATE..=pcs::MAX_LOG_INV_RATE {
                let report = Ledger::for_program(&program, &taus.map(|tau| tau + extra), rate).unwrap();
                assert!(report.opening_batch_degree < ::pcs::ring_switch::RING_SWITCH_SOUNDNESS_DEGREE);
                assert!(report.class_degrees.iter().all(|&d| d > 127));
                let raw = 192.0 - (report.bus_degree as f64).log2();
                assert!(report.outer_algebraic_bits < raw - report.pcs[0].log2_list_size);
                assert!(report.outer_algebraic_bits >= 128.0);
                assert!(report.pcs.iter().all(|t| t.algebraic_bits >= 128.0));
            }
        }
        assert_eq!(last_mu, MAX_MU);
        assert!(Ledger::for_program(&program, &taus, 0).is_err());
        assert!(Ledger::for_program(&program, &[], pcs::TEST_LOG_INV_RATE).is_err());
        assert!(Ledger::for_program(&program, &[usize::MAX; tables::N_TABLES], pcs::TEST_LOG_INV_RATE).is_err());
        let mut malformed = layout;
        malformed.push[0].kappa = usize::MAX;
        assert!(Ledger::for_layout(&malformed, pcs::TEST_LOG_INV_RATE).is_err());
    }
}
