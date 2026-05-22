use backend::*;

use crate::ExtraDataForBuses;

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
