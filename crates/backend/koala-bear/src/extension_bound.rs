use field::{ExtensionField, Field, PrimeCharacteristicRing};

use crate::KoalaBear;

pub trait KoalaBearExtension:
    Field + ExtensionField<KoalaBear> + PrimeCharacteristicRing<PrimeSubfield = KoalaBear>
{
}

impl<T: Field + ExtensionField<KoalaBear> + PrimeCharacteristicRing<PrimeSubfield = KoalaBear>> KoalaBearExtension
    for T
{
}
