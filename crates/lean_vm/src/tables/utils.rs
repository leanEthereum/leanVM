use backend::*;

use crate::ExtraDataForBuses;

pub(crate) fn eval_bus_virtual<AB: AirBuilder, EF: ExtensionField<PF<EF>>>(
    extra_data: &ExtraDataForBuses<EF>,
    multiplicity: AB::IF,
    domainsep: AB::IF,
    data: &[AB::IF],
) -> AB::EF {
    let (logup_alphas_eq_poly, bus_beta) = extra_data.transmute_bus_data::<AB::EF>();

    assert!(data.len() < logup_alphas_eq_poly.len());
    (logup_alphas_eq_poly
        .iter()
        .zip(data)
        .map(|(c, d)| *c * *d)
        .sum::<AB::EF>()
        + *logup_alphas_eq_poly.last().unwrap() * domainsep)
        * *bus_beta
        + multiplicity
}
