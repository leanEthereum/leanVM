// jemalloc configured for proving.
#[cfg(unix)]
#[global_allocator]
static ALLOCATOR: allocator::Jemalloc = allocator::Jemalloc;

use lean_pq::{sphincs, vrf, xmss, Message};
use pyo3::create_exception;
use pyo3::exceptions::{PyException, PyValueError};
use pyo3::prelude::*;
use pyo3::pybacked::PyBackedBytes;
use pyo3::types::{PyBytes, PyInt, PyType};
use pyo3::wrap_pyfunction;

create_exception!(py_lean_pq, LeanPqError, PyException);

fn api_error(error: lean_pq::Error) -> PyErr {
    match error {
        lean_pq::Error::InvalidLength { .. }
        | lean_pq::Error::InvalidXmssCache
        | lean_pq::Error::InvalidVrfCache => PyValueError::new_err(error.to_string()),
        _ => LeanPqError::new_err(error.to_string()),
    }
}

fn fixed<const N: usize>(bytes: &[u8], name: &str) -> PyResult<[u8; N]> {
    bytes.try_into().map_err(|_| {
        PyValueError::new_err(format!(
            "{name} must be exactly {N} bytes, got {}",
            bytes.len()
        ))
    })
}

fn message(bytes: &[u8]) -> PyResult<Message> {
    fixed(bytes, "message")
}

fn xmss_public_key(bytes: &[u8]) -> PyResult<xmss::PublicKey> {
    xmss::PublicKey::from_bytes(bytes).map_err(api_error)
}

fn xmss_signature(bytes: &[u8]) -> PyResult<xmss::Signature> {
    xmss::Signature::from_bytes(bytes).map_err(api_error)
}

fn sphincs_public_key(bytes: &[u8]) -> PyResult<sphincs::PublicKey> {
    sphincs::PublicKey::from_bytes(bytes).map_err(api_error)
}

fn sphincs_signature(bytes: &[u8]) -> PyResult<sphincs::Signature> {
    sphincs::Signature::from_bytes(bytes).map_err(api_error)
}

type SignedMessage = (PyBackedBytes, PyBackedBytes, PyBackedBytes);
type Claim = (PyBackedBytes, PyBackedBytes);

#[pyclass(name = "XmssSecretKey", frozen, module = "py_lean_pq")]
struct PyXmssSecretKey {
    inner: xmss::SecretKey,
}

#[pymethods]
impl PyXmssSecretKey {
    #[classmethod]
    fn generate(_cls: &Bound<'_, PyType>, py: Python<'_>) -> Self {
        Self {
            inner: py.detach(xmss::SecretKey::generate),
        }
    }

    #[classmethod]
    fn from_seed(_cls: &Bound<'_, PyType>, py: Python<'_>, seed: &[u8]) -> PyResult<Self> {
        let seed = fixed(seed, "seed")?;
        Ok(Self {
            inner: py.detach(move || xmss::SecretKey::from_seed(seed)),
        })
    }

    #[classmethod]
    fn from_bytes(_cls: &Bound<'_, PyType>, py: Python<'_>, data: &[u8]) -> PyResult<Self> {
        Ok(Self {
            inner: py
                .detach(|| xmss::SecretKey::from_bytes(data))
                .map_err(api_error)?,
        })
    }

    #[classmethod]
    fn from_cache_bytes(
        _cls: &Bound<'_, PyType>,
        py: Python<'_>,
        seed: &[u8],
        public_key: &[u8],
        cache: &[u8],
    ) -> PyResult<Self> {
        let seed = fixed(seed, "seed")?;
        let public_key = xmss_public_key(public_key)?;
        Ok(Self {
            inner: py
                .detach(move || xmss::SecretKey::from_cache_bytes(seed, &public_key, cache))
                .map_err(api_error)?,
        })
    }

    fn to_bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.to_bytes())
    }

    fn cache_to_bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.cache_to_bytes())
    }

    #[getter]
    fn public_key<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.public_key().to_bytes())
    }

    fn prepare(&self, py: Python<'_>, leaf_index: xmss::LeafIndex) {
        py.detach(|| self.inner.prepare(leaf_index));
    }

    fn sign<'py>(
        &self,
        py: Python<'py>,
        message: &[u8],
        leaf_index: xmss::LeafIndex,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let message = self::message(message)?;
        let signature = py.detach(|| self.inner.sign(&message, leaf_index));
        Ok(PyBytes::new(py, &signature.to_bytes()))
    }
}

#[pyclass(name = "SphincsSecretKey", frozen, module = "py_lean_pq")]
struct PySphincsSecretKey {
    inner: sphincs::SecretKey,
}

#[pymethods]
impl PySphincsSecretKey {
    #[classmethod]
    fn generate(_cls: &Bound<'_, PyType>, py: Python<'_>) -> Self {
        Self {
            inner: py.detach(sphincs::SecretKey::generate),
        }
    }

    #[classmethod]
    fn from_seed(_cls: &Bound<'_, PyType>, py: Python<'_>, seed: &[u8]) -> PyResult<Self> {
        let seed = fixed(seed, "seed")?;
        Ok(Self {
            inner: py.detach(move || sphincs::SecretKey::from_seed(seed)),
        })
    }

    #[classmethod]
    fn from_bytes(_cls: &Bound<'_, PyType>, py: Python<'_>, data: &[u8]) -> PyResult<Self> {
        Ok(Self {
            inner: py
                .detach(|| sphincs::SecretKey::from_bytes(data))
                .map_err(api_error)?,
        })
    }

    fn to_bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.to_bytes())
    }

    #[getter]
    fn public_key<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.public_key().to_bytes())
    }

    fn sign<'py>(&self, py: Python<'py>, message: &[u8]) -> PyResult<Bound<'py, PyBytes>> {
        let message = self::message(message)?;
        let signature = py.detach(|| self.inner.sign(&message));
        Ok(PyBytes::new(py, &signature.to_bytes()))
    }
}

#[pyclass(name = "VrfKey", frozen, module = "py_lean_pq")]
struct PyVrfKey {
    inner: vrf::Key,
}

#[pymethods]
impl PyVrfKey {
    #[classmethod]
    fn from_seed(
        _cls: &Bound<'_, PyType>,
        py: Python<'_>,
        seed: &[u8],
        start: vrf::Slot,
        end: vrf::Slot,
    ) -> PyResult<Self> {
        let seed = fixed(seed, "seed")?;
        Ok(Self {
            inner: py
                .detach(move || vrf::Key::new(seed, start..end))
                .map_err(api_error)?,
        })
    }

    #[classmethod]
    fn from_cache_bytes(
        _cls: &Bound<'_, PyType>,
        py: Python<'_>,
        seed: &[u8],
        root: &[u8],
        cache: &[u8],
    ) -> PyResult<Self> {
        let seed = fixed(seed, "seed")?;
        let root = fixed(root, "root")?;
        Ok(Self {
            inner: py
                .detach(move || vrf::Key::from_cache_bytes(seed, &root, cache))
                .map_err(api_error)?,
        })
    }

    fn cache_to_bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.cache_to_bytes())
    }

    fn root<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.root())
    }

    fn proof<'py>(&self, py: Python<'py>, slot: vrf::Slot) -> PyResult<Bound<'py, PyBytes>> {
        let proof = py.detach(|| self.inner.proof(slot)).map_err(api_error)?;
        Ok(PyBytes::new(py, proof.as_flattened()))
    }
}

#[pyclass(name = "Aggregate", frozen, module = "py_lean_pq")]
struct PyAggregate {
    inner: lean_pq::Aggregate,
}

fn claims<'py, const N: usize>(
    py: Python<'py>,
    claims: impl IntoIterator<Item = ([u8; N], Message)>,
) -> Vec<(Bound<'py, PyBytes>, Bound<'py, PyBytes>)> {
    claims
        .into_iter()
        .map(|(key, message)| (PyBytes::new(py, &key), PyBytes::new(py, &message)))
        .collect()
}

#[pymethods]
impl PyAggregate {
    #[classmethod]
    #[pyo3(
        signature = (data, xmss_claims = Vec::new(), sphincs_claims = Vec::new()),
        text_signature = "(data, xmss_claims=(), sphincs_claims=())"
    )]
    fn from_bytes(
        _cls: &Bound<'_, PyType>,
        py: Python<'_>,
        data: &[u8],
        xmss_claims: Vec<Claim>,
        sphincs_claims: Vec<Claim>,
    ) -> PyResult<Self> {
        let (xmss_claims, sphincs_claims) = claim_lists(&xmss_claims, &sphincs_claims)?;
        Ok(Self {
            inner: py
                .detach(|| lean_pq::Aggregate::from_bytes(data, &xmss_claims, &sphincs_claims))
                .map_err(api_error)?,
        })
    }

    fn to_bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.to_bytes())
    }

    #[getter]
    fn xmss_claims<'py>(&self, py: Python<'py>) -> Vec<(Bound<'py, PyBytes>, Bound<'py, PyBytes>)> {
        claims(
            py,
            self.inner
                .xmss_claims()
                .into_iter()
                .map(|(key, message)| (key.to_bytes(), message)),
        )
    }

    #[getter]
    fn sphincs_claims<'py>(
        &self,
        py: Python<'py>,
    ) -> Vec<(Bound<'py, PyBytes>, Bound<'py, PyBytes>)> {
        claims(
            py,
            self.inner
                .sphincs_claims()
                .into_iter()
                .map(|(key, message)| (key.to_bytes(), message)),
        )
    }
}

#[pyfunction]
#[pyo3(signature = (threads = None), text_signature = "(threads=0)")]
fn setup(py: Python<'_>, threads: Option<&Bound<'_, PyInt>>) -> PyResult<()> {
    let threads = match threads {
        None => 0,
        Some(threads) => threads.extract::<usize>().map_err(|_| {
            PyValueError::new_err(format!(
                "threads must be from 0 to the machine's parallelism, got {threads}"
            ))
        })?,
    };
    py.detach(|| lean_pq::setup(threads)).map_err(api_error)
}

#[pyfunction]
fn xmss_verify(
    py: Python<'_>,
    public_key: &[u8],
    message: &[u8],
    signature: &[u8],
) -> PyResult<()> {
    let public_key = xmss_public_key(public_key)?;
    let message = self::message(message)?;
    let signature = xmss_signature(signature)?;
    py.detach(|| public_key.verify(&message, &signature))
        .map_err(api_error)
}

#[pyfunction]
fn sphincs_verify(
    py: Python<'_>,
    public_key: &[u8],
    message: &[u8],
    signature: &[u8],
) -> PyResult<()> {
    let public_key = sphincs_public_key(public_key)?;
    let message = self::message(message)?;
    let signature = sphincs_signature(signature)?;
    py.detach(|| public_key.verify(&message, &signature))
        .map_err(api_error)
}

#[pyfunction]
fn vrf_verify(py: Python<'_>, root: &[u8], slot: u64, proof: &[u8]) -> PyResult<()> {
    let root = fixed(root, "root")?;
    let proof: [u8; vrf::PROOF_LEN] = fixed(proof, "proof")?;
    let (nodes, _) = proof.as_chunks::<32>();
    let proof: vrf::Proof = nodes.try_into().expect("a proof is 32 nodes");
    py.detach(|| vrf::verify(&root, slot, &proof))
        .map_err(api_error)
}

/// Claim lists, as `Aggregate::from_bytes` and `aggregate_only` take them.
type Claims = (
    Vec<(xmss::PublicKey, Message)>,
    Vec<(sphincs::PublicKey, Message)>,
);

fn claim_lists(xmss_claims: &[Claim], sphincs_claims: &[Claim]) -> PyResult<Claims> {
    let xmss_claims = xmss_claims
        .iter()
        .map(|(public_key, message)| Ok((xmss_public_key(public_key)?, self::message(message)?)))
        .collect::<PyResult<Vec<_>>>()?;
    let sphincs_claims = sphincs_claims
        .iter()
        .map(|(public_key, message)| Ok((sphincs_public_key(public_key)?, self::message(message)?)))
        .collect::<PyResult<Vec<_>>>()?;
    Ok((xmss_claims, sphincs_claims))
}

#[pyfunction]
#[pyo3(
    signature = (children = Vec::new(), xmss = Vec::new(), sphincs = Vec::new(), xmss_claims = None, sphincs_claims = None),
    text_signature = "(children=(), xmss=(), sphincs=(), xmss_claims=None, sphincs_claims=None)"
)]
fn aggregate(
    py: Python<'_>,
    children: Vec<Bound<'_, PyAggregate>>,
    xmss: Vec<SignedMessage>,
    sphincs: Vec<SignedMessage>,
    xmss_claims: Option<Vec<Claim>>,
    sphincs_claims: Option<Vec<Claim>>,
) -> PyResult<PyAggregate> {
    let children = children
        .iter()
        .map(|child| &child.get().inner)
        .collect::<Vec<_>>();
    let xmss = xmss
        .iter()
        .map(|(public_key, message, signature)| {
            Ok((
                xmss_public_key(public_key)?,
                self::message(message)?,
                xmss_signature(signature)?,
            ))
        })
        .collect::<PyResult<Vec<_>>>()?;
    let sphincs = sphincs
        .iter()
        .map(|(public_key, message, signature)| {
            Ok((
                sphincs_public_key(public_key)?,
                self::message(message)?,
                sphincs_signature(signature)?,
            ))
        })
        .collect::<PyResult<Vec<_>>>()?;
    // Either list asks for exactly those claims; the other, omitted, means none.
    let only = if xmss_claims.is_none() && sphincs_claims.is_none() {
        None
    } else {
        Some(claim_lists(
            &xmss_claims.unwrap_or_default(),
            &sphincs_claims.unwrap_or_default(),
        )?)
    };
    py.detach(|| match &only {
        None => lean_pq::aggregate(&children, &xmss, &sphincs),
        Some((xmss_claims, sphincs_claims)) => {
            lean_pq::aggregate_only(&children, &xmss, &sphincs, xmss_claims, sphincs_claims)
        }
    })
    .map(|inner| PyAggregate { inner })
    .map_err(api_error)
}

#[pymodule]
fn py_lean_pq(py: Python<'_>, module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add("__version__", env!("CARGO_PKG_VERSION"))?;
    module.add("LeanPqError", py.get_type::<LeanPqError>())?;
    module.add_class::<PyXmssSecretKey>()?;
    module.add_class::<PySphincsSecretKey>()?;
    module.add_class::<PyVrfKey>()?;
    module.add_class::<PyAggregate>()?;
    module.add_function(wrap_pyfunction!(setup, module)?)?;
    module.add_function(wrap_pyfunction!(xmss_verify, module)?)?;
    module.add_function(wrap_pyfunction!(sphincs_verify, module)?)?;
    module.add_function(wrap_pyfunction!(vrf_verify, module)?)?;
    module.add_function(wrap_pyfunction!(aggregate, module)?)?;
    Ok(())
}
