use backend::*;

use crate::ExtraDataForBuses;

/// h9-A (iter 5): data-only bus fingerprint for deferred-claim buses
/// (Multiplicity::One memory lookups whose address columns are virtual). Emits ONE
/// encoded constraint — no multiplicity assert (the One-multiplicity numerator is
/// already reconstructed verifier-side for committed One-buses). The constant
/// `domainsep` is lifted directly into the fingerprint (vs. eval_bus_virtual's
/// column-borne domainsep).
pub(crate) fn eval_bus_data_only<AB: AirBuilder, EF: ExtensionField<PF<EF>>>(
    builder: &mut AB,
    extra_data: &ExtraDataForBuses<EF>,
    domainsep: usize,
    data: &[AB::IF],
) {
    let logup_alphas_eq_poly = extra_data.transmute_bus_data::<AB::EF>();
    assert!(data.len() < logup_alphas_eq_poly.len());
    let encoded = logup_alphas_eq_poly
        .iter()
        .zip(data)
        .map(|(c, d)| *c * *d)
        .sum::<AB::EF>()
        + *logup_alphas_eq_poly.last().unwrap() * AB::F::from_usize(domainsep);
    builder.assert_zero_ef(encoded);
}

pub(crate) fn eval_bus_virtual<AB: AirBuilder, EF: ExtensionField<PF<EF>>>(
    builder: &mut AB,
    extra_data: &ExtraDataForBuses<EF>,
    multiplicity: AB::IF,
    domainsep: AB::IF,
    data: &[AB::IF],
) {
    let logup_alphas_eq_poly = extra_data.transmute_bus_data::<AB::EF>();

    assert!(data.len() < logup_alphas_eq_poly.len());

    builder.assert_zero(multiplicity);

    // fingerprinted bus data
    let encoded = logup_alphas_eq_poly
        .iter()
        .zip(data)
        .map(|(c, d)| *c * *d)
        .sum::<AB::EF>()
        + *logup_alphas_eq_poly.last().unwrap() * domainsep;
    builder.assert_zero_ef(encoded);
}
