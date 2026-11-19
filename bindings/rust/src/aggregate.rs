//! Recursive aggregation of leanXMSS and leanSPHINCS signatures into one leanVM proof, proven and
//! verified by a leanVM sidecar (`bins/leanvm-sidecar`), a separate process reached over a Unix
//! socket.
//!
//! It is the argument-based multi-signature of Drake, Khovratovich, Kudinov and Wagner.
//!
//! - Paper: "Hash-Based Multi-Signatures for Post-Quantum Ethereum", IACR Communications in Cryptology 2(1), 2025.
//! - Construction 4: an aggregate is a succinct argument of knowledge of every signature.
//! - Theorem 2: it is as unforgeable as the signatures, given adaptive knowledge soundness.
//!
//! An encoded aggregate is the proof alone: the claims travel separately, and a receiver checks
//! the proof against the claims it expects.

use std::fmt;
use std::path::{Path, PathBuf};
#[cfg(unix)]
use std::process::Child;
#[cfg(unix)]
use std::sync::{Mutex, PoisonError};
#[cfg(unix)]
use std::time::Duration;

use claims::AggregateClaims;

use crate::{sphincs, xmss, Error, Message};

/// The most children one aggregation recurses over.
pub const MAX_CHILDREN: usize = 16;

/// Exponent of the proof's Reed-Solomon code rate, `rho = 2^-2 = 1/4`: a larger one gives a smaller
/// proof but slower proving.
#[cfg(unix)]
const LOG_INV_RATE: usize = 2;

/// How long [`Sidecar::start`] waits for a sidecar to warm up and listen.
#[cfg(unix)]
const STARTUP_TIMEOUT: Duration = Duration::from_secs(600);

/// A connection to a leanVM sidecar, which proves and verifies aggregates.
///
/// - Calls on one connection run one at a time; the sidecar proves one request at a time anyway.
/// - After the sidecar stops or the connection breaks, the next call connects again.
/// - Connect again in a forked child rather than sharing the parent's connection.
/// - Unix only: on other platforms [`Sidecar::connect`] and [`Sidecar::start`] fail.
#[derive(Debug)]
pub struct Sidecar {
    #[cfg_attr(not(unix), allow(dead_code))]
    socket: PathBuf,
    #[cfg(unix)]
    client: Mutex<Option<sidecar::Client>>,
    /// The sidecar [`Sidecar::start`] launched, stopped on drop.
    #[cfg(unix)]
    process: Option<Owned>,
}

/// A sidecar process this value launched, and the process that launched it: a forked child
/// inherits the value but must not stop the parent's sidecar. The child also exits when `_stdin`
/// closes, which the launching process's exit does however it exits.
#[cfg(unix)]
#[derive(Debug)]
struct Owned {
    child: Child,
    _stdin: Option<std::process::ChildStdin>,
    owner: u32,
}

#[cfg(unix)]
impl Drop for Sidecar {
    fn drop(&mut self) {
        if let Some(owned) = &mut self.process {
            if owned.owner == std::process::id() {
                let _ = owned.child.kill();
                let _ = owned.child.wait();
            }
        }
    }
}

impl Sidecar {
    /// Connects to the sidecar listening on `socket`.
    ///
    /// # Errors
    ///
    /// - Fails when nothing listens on `socket`, or when it is not a compatible leanVM sidecar.
    /// - Fails on platforms without Unix sockets.
    pub fn connect(socket: impl AsRef<Path>) -> Result<Self, Error> {
        let socket = socket.as_ref().to_path_buf();
        #[cfg(unix)]
        {
            let client = sidecar::Client::connect(&socket).map_err(sidecar_error)?;
            Ok(Self {
                socket,
                client: Mutex::new(Some(client)),
                process: None,
            })
        }
        #[cfg(not(unix))]
        {
            let _ = socket;
            Err(Error::SidecarUnsupported)
        }
    }

    /// Launches the `leanvm-sidecar` executable at `binary` on `socket`, waits until it has warmed
    /// up and listens, and connects to it. Dropping the value stops the sidecar.
    ///
    /// - The socket's directory is created, readable by this user only, if it does not exist.
    /// - The sidecar's log goes to the socket's path with `.log` appended.
    /// - The sidecar also stops when this process exits without dropping the value.
    ///
    /// # Errors
    ///
    /// - Fails when a sidecar already listens on `socket`: connect to it instead.
    /// - Fails when `binary` cannot run, or when the sidecar exits or does not listen within ten
    ///   minutes; the error quotes the end of its log.
    /// - Fails on platforms without Unix sockets.
    pub fn start(binary: impl AsRef<Path>, socket: impl AsRef<Path>) -> Result<Self, Error> {
        #[cfg(unix)]
        {
            Self::launch(binary.as_ref(), socket.as_ref())
        }
        #[cfg(not(unix))]
        {
            let _ = (binary, socket);
            Err(Error::SidecarUnsupported)
        }
    }

    #[cfg(unix)]
    fn launch(binary: &Path, socket: &Path) -> Result<Self, Error> {
        use std::os::unix::fs::DirBuilderExt;
        use std::process::{Command, Stdio};
        use std::time::Instant;

        let failure = |reason: String| Error::Sidecar { reason };
        if sidecar::Client::connect(socket).is_ok() {
            return Err(failure(format!(
                "a sidecar already listens on {}: connect to it instead",
                socket.display()
            )));
        }
        if let Some(directory) = socket.parent().filter(|d| !d.as_os_str().is_empty()) {
            std::fs::DirBuilder::new()
                .recursive(true)
                .mode(0o700)
                .create(directory)
                .map_err(|e| failure(format!("cannot create {}: {e}", directory.display())))?;
        }
        let mut log_path = socket.as_os_str().to_owned();
        log_path.push(".log");
        let log_path = PathBuf::from(log_path);
        let log = std::fs::File::create(&log_path)
            .map_err(|e| failure(format!("cannot create {}: {e}", log_path.display())))?;
        let mut child = Command::new(binary)
            .arg("--socket")
            .arg(socket)
            .arg("--exit-with-stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(log)
            .spawn()
            .map_err(|e| failure(format!("cannot run {}: {e}", binary.display())))?;
        // From here on, dropping `started` on any error stops the child.
        let mut started = Self {
            socket: socket.to_path_buf(),
            client: Mutex::new(None),
            process: Some(Owned {
                _stdin: child.stdin.take(),
                child,
                owner: std::process::id(),
            }),
        };
        let deadline = Instant::now() + STARTUP_TIMEOUT;
        loop {
            let child = &mut started.process.as_mut().expect("launched").child;
            if let Ok(Some(status)) = child.try_wait() {
                return Err(failure(format!(
                    "{} exited ({status}) before listening: {}",
                    binary.display(),
                    log_tail(&log_path)
                )));
            }
            match sidecar::Client::connect(socket) {
                Ok(client) => {
                    *started
                        .client
                        .get_mut()
                        .unwrap_or_else(PoisonError::into_inner) = Some(client);
                    return Ok(started);
                }
                Err(sidecar::SidecarError::Io(_)) if Instant::now() < deadline => {
                    std::thread::sleep(Duration::from_millis(100));
                }
                Err(error) => {
                    return Err(failure(format!(
                        "{error}; its log ends: {}",
                        log_tail(&log_path)
                    )))
                }
            }
        }
    }

    /// Proves raw signatures and child aggregates together as one aggregate.
    ///
    /// ```text
    ///     claims(result) = claims(children) + claims(raw inputs)
    ///                      sorted, one entry per (public key, message)
    /// ```
    ///
    /// - Raw signatures are verified first, so a bad one is named by its index.
    /// - Children are borrowed, and the proof re-verifies each one.
    ///
    /// # Errors
    ///
    /// - Fails when more than 16 children are given.
    /// - Fails when a raw signature does not verify, naming its list and index.
    /// - Fails when the sidecar rejects the input, for example when it is empty.
    /// - Fails when the sidecar cannot be reached.
    pub fn aggregate(
        &self,
        children: &[&Aggregate],
        xmss: &[(xmss::PublicKey, Message, xmss::Signature)],
        sphincs: &[(sphincs::PublicKey, Message, sphincs::Signature)],
    ) -> Result<Aggregate, Error> {
        if children.len() > MAX_CHILDREN {
            return Err(Error::TooManyChildren {
                count: children.len(),
                max: MAX_CHILDREN,
            });
        }
        // An invalid signature would otherwise surface as a failed proof; checking first names it.
        for (index, (public_key, message, signature)) in xmss.iter().enumerate() {
            public_key
                .verify(message, signature)
                .map_err(|_| Error::InvalidXmssInput {
                    index,
                    leaf_index: signature.leaf_index(),
                })?;
        }
        for (index, (public_key, message, signature)) in sphincs.iter().enumerate() {
            public_key
                .verify(message, signature)
                .map_err(|_| Error::InvalidSphincsInput { index })?;
        }
        self.prove(children, xmss, sphincs)
    }

    /// Verifies that a proof proves exactly these claims, and returns it as an aggregate.
    ///
    /// The claims may come in any order, and a repeated claim counts once.
    ///
    /// # Errors
    ///
    /// - Fails when the bytes are not a proof of exactly these claims.
    /// - Fails when the sidecar cannot be reached.
    pub fn verify(
        &self,
        bytes: &[u8],
        xmss_claims: &[(xmss::PublicKey, Message)],
        sphincs_claims: &[(sphincs::PublicKey, Message)],
    ) -> Result<Aggregate, Error> {
        let claims = AggregateClaims {
            lean_xmss: sorted_claims(xmss_claims.iter().map(|(key, message)| (key.0, *message))),
            lean_sphincs: sorted_claims(
                sphincs_claims
                    .iter()
                    .map(|(key, message)| (key.0, *message)),
            ),
            // These bindings neither make nor accept leanDA blob commitments.
            da_commitment: None,
        };
        if !self.check(&claims, bytes)? {
            return Err(Error::AggregateRejected);
        }
        Ok(Aggregate {
            claims,
            proof: bytes.to_vec(),
        })
    }

    #[cfg(unix)]
    fn prove(
        &self,
        children: &[&Aggregate],
        xmss: &[(xmss::PublicKey, Message, xmss::Signature)],
        sphincs: &[(sphincs::PublicKey, Message, sphincs::Signature)],
    ) -> Result<Aggregate, Error> {
        let children: Vec<_> = children
            .iter()
            .map(|child| (child.claims.clone(), child.proof.clone()))
            .collect();
        let xmss: Vec<_> = xmss
            .iter()
            .map(|(public_key, message, signature)| (public_key.0, *message, signature.0.clone()))
            .collect();
        let sphincs: Vec<_> = sphincs
            .iter()
            .map(|(public_key, message, signature)| (public_key.0, *message, signature.0.clone()))
            .collect();
        // No DA blobs, and keep every claim the inputs cover.
        let (claims, proof) = self.call(|client| {
            client.aggregate(
                &children,
                &xmss,
                &sphincs,
                &[],
                claims::OutputClaims::All,
                LOG_INV_RATE,
            )
        })?;
        Ok(Aggregate { claims, proof })
    }

    #[cfg(unix)]
    fn check(&self, claims: &AggregateClaims, proof: &[u8]) -> Result<bool, Error> {
        self.call(|client| client.verify(claims, proof))
    }

    /// Runs one request, connecting first if a broken connection was dropped.
    #[cfg(unix)]
    fn call<T>(
        &self,
        request: impl FnOnce(&mut sidecar::Client) -> Result<T, sidecar::SidecarError>,
    ) -> Result<T, Error> {
        let mut client = self.client.lock().unwrap_or_else(PoisonError::into_inner);
        let connected = match client.take() {
            Some(connected) => connected,
            None => sidecar::Client::connect(&self.socket).map_err(sidecar_error)?,
        };
        match request(client.insert(connected)) {
            Ok(value) => Ok(value),
            // A refused request leaves the connection usable.
            Err(sidecar::SidecarError::Rejected(_, reason)) => Err(Error::Aggregation { reason }),
            Err(error) => {
                *client = None;
                Err(sidecar_error(error))
            }
        }
    }

    #[cfg(not(unix))]
    #[allow(clippy::unused_self)]
    fn prove(
        &self,
        _: &[&Aggregate],
        _: &[(xmss::PublicKey, Message, xmss::Signature)],
        _: &[(sphincs::PublicKey, Message, sphincs::Signature)],
    ) -> Result<Aggregate, Error> {
        Err(Error::SidecarUnsupported)
    }

    #[cfg(not(unix))]
    #[allow(clippy::unused_self)]
    fn check(&self, _: &AggregateClaims, _: &[u8]) -> Result<bool, Error> {
        Err(Error::SidecarUnsupported)
    }
}

/// The end of a sidecar's log, to quote in an error.
#[cfg(unix)]
fn log_tail(path: &Path) -> String {
    let log = std::fs::read_to_string(path).unwrap_or_default();
    let start = log.len().saturating_sub(2000);
    let start = (start..log.len())
        .find(|&i| log.is_char_boundary(i))
        .unwrap_or(log.len());
    log[start..].trim().to_owned()
}

#[cfg(unix)]
#[allow(clippy::needless_pass_by_value)]
fn sidecar_error(error: sidecar::SidecarError) -> Error {
    Error::Sidecar {
        reason: error.to_string(),
    }
}

/// A verified recursive proof that each listed public key signed its message.
///
/// - Every value was either proven or verified by a sidecar against the claims it lists.
/// - A claim names a public key and a message, never the leaf index used.
/// - Its encoding is the proof alone: send the claims alongside, or let the receiver rebuild them.
#[derive(Clone)]
pub struct Aggregate {
    claims: AggregateClaims,
    proof: Vec<u8>,
}

impl Aggregate {
    /// Encodes the proof, without its claims.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        self.proof.clone()
    }

    /// Returns the proven leanXMSS claims, strictly sorted by public key then message.
    #[must_use]
    pub fn xmss_claims(&self) -> Vec<(xmss::PublicKey, Message)> {
        self.claims
            .lean_xmss
            .iter()
            .map(|&(key, message)| (xmss::PublicKey(key), message))
            .collect()
    }

    /// Returns the proven leanSPHINCS claims, strictly sorted by public key then message.
    #[must_use]
    pub fn sphincs_claims(&self) -> Vec<(sphincs::PublicKey, Message)> {
        self.claims
            .lean_sphincs
            .iter()
            .map(|&(key, message)| (sphincs::PublicKey(key), message))
            .collect()
    }
}

impl fmt::Debug for Aggregate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Claim counts identify an aggregate in a log.
        // The proof bytes would drown it.
        f.debug_struct("Aggregate")
            .field("xmss_claims", &self.claims.lean_xmss.len())
            .field("sphincs_claims", &self.claims.lean_sphincs.len())
            .finish_non_exhaustive()
    }
}

/// Claims strictly sorted, the order a proof's statement lists them in.
fn sorted_claims<K: Ord>(claims: impl Iterator<Item = (K, Message)>) -> Vec<(K, Message)> {
    let mut claims: Vec<_> = claims.collect();
    claims.sort_unstable();
    claims.dedup();
    claims
}
