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
use std::sync::atomic::{AtomicBool, Ordering};
#[cfg(unix)]
use std::sync::{Mutex, MutexGuard, PoisonError};
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
/// - Calls run one at a time. After the sidecar stops or the connection breaks, the next call
///   connects again; so does the first call in a forked child, which never shares its parent's.
/// - The sidecar serves at most 16 connections: share one `Sidecar` per process.
/// - Unix only: on other platforms [`Sidecar::connect`] and [`Sidecar::start`] fail.
#[derive(Debug)]
pub struct Sidecar {
    /// The absolute socket path.
    #[cfg_attr(not(unix), allow(dead_code))]
    socket: PathBuf,
    /// The prover the sidecar runs, as it says on connecting.
    #[cfg_attr(not(unix), allow(dead_code))]
    prover: String,
    #[cfg(unix)]
    connection: Mutex<Connection>,
    /// The sidecar [`Sidecar::start`] launched, stopped by [`Sidecar::close`] or on drop.
    #[cfg(unix)]
    process: Mutex<Option<Owned>>,
    closed: AtomicBool,
}

/// The current connection, and the process that opened it: a forked child must not share it.
#[cfg(unix)]
#[derive(Debug)]
struct Connection {
    client: Option<sidecar::Client>,
    pid: u32,
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

impl Drop for Sidecar {
    fn drop(&mut self) {
        self.close();
    }
}

#[cfg(unix)]
fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

impl Sidecar {
    /// Connects to the sidecar listening on `socket`.
    ///
    /// # Errors
    ///
    /// - Fails when nothing listens on `socket`, or when it is not a compatible leanVM sidecar.
    /// - Fails on platforms without Unix sockets.
    pub fn connect(socket: impl AsRef<Path>) -> Result<Self, Error> {
        #[cfg(unix)]
        {
            let socket = absolute(socket.as_ref(), "socket")?;
            let client = sidecar::Client::connect(&socket).map_err(sidecar_error)?;
            Ok(Self {
                socket,
                prover: client.prover().to_owned(),
                connection: Mutex::new(Connection {
                    client: Some(client),
                    pid: std::process::id(),
                }),
                process: Mutex::new(None),
                closed: AtomicBool::new(false),
            })
        }
        #[cfg(not(unix))]
        {
            let _ = socket;
            Err(Error::SidecarUnsupported)
        }
    }

    /// Launches the `leanvm-sidecar` executable at `binary` (looked up on `PATH` when it is a bare
    /// name) on `socket` with `threads` threads (0: one per core), waits until it has warmed up and
    /// listens, and connects to it. [`Sidecar::close`], dropping the value, or this process
    /// exiting stops the sidecar.
    ///
    /// - The socket's directory is created private (mode 0700) if missing, and must be private
    ///   otherwise: anyone who can write to it could put a fake sidecar there.
    /// - The sidecar's log is appended to the socket's path with `.log` appended.
    /// - The sidecar runs in a process group of its own, so a terminal's Ctrl-C does not reach it.
    ///
    /// # Errors
    ///
    /// - Fails when a sidecar already listens on `socket`: connect to it instead.
    /// - Fails when the socket's directory is not private.
    /// - Fails when `binary` cannot run, or when the sidecar exits or does not listen within ten
    ///   minutes; the error quotes the end of its log.
    /// - Fails on platforms without Unix sockets.
    pub fn start(
        binary: impl AsRef<Path>,
        socket: impl AsRef<Path>,
        threads: usize,
    ) -> Result<Self, Error> {
        #[cfg(unix)]
        {
            Self::launch(binary.as_ref(), socket.as_ref(), threads)
        }
        #[cfg(not(unix))]
        {
            let _ = (binary, socket, threads);
            Err(Error::SidecarUnsupported)
        }
    }

    /// The prover the sidecar runs, `experimental` or `stable`: they make the same proofs, the
    /// experimental one faster. It is chosen when the sidecar is built.
    #[must_use]
    pub fn prover(&self) -> &str {
        &self.prover
    }

    /// Stops the sidecar [`Sidecar::start`] launched, which fails a call in progress, then closes
    /// the connection, waiting for a call in progress on a sidecar this value did not launch.
    /// Later calls fail with [`Error::SidecarClosed`]. Closing twice does nothing.
    pub fn close(&self) {
        self.closed.store(true, Ordering::Release);
        #[cfg(unix)]
        {
            if let Some(mut owned) = lock(&self.process).take() {
                if owned.owner == std::process::id() {
                    let _ = owned.child.kill();
                    let _ = owned.child.wait();
                }
            }
            lock(&self.connection).client = None;
        }
    }

    #[cfg(unix)]
    fn launch(binary: &Path, socket: &Path, threads: usize) -> Result<Self, Error> {
        use std::os::unix::process::CommandExt;
        use std::process::{Command, Stdio};
        use std::time::Instant;

        let failure = |reason: String| Error::Sidecar { reason };
        let socket = absolute(socket, "socket")?;
        // A bare name is looked up on PATH; a path is made absolute.
        let binary = if binary.components().count() > 1 {
            absolute(binary, "binary")?
        } else {
            binary.to_path_buf()
        };
        if binary.as_os_str().is_empty() {
            return Err(failure("the binary path is empty".into()));
        }
        if sidecar::Client::connect(&socket).is_ok() {
            return Err(failure(format!(
                "a sidecar already listens on {}: connect to it instead",
                socket.display()
            )));
        }
        let (log_path, log) = open_log(&socket)?;
        let mut child = Command::new(&binary)
            .arg("--socket")
            .arg(&socket)
            .arg("--threads")
            .arg(threads.to_string())
            .arg("--exit-with-stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(log)
            .process_group(0)
            .spawn()
            .map_err(|e| failure(format!("cannot run {}: {e}", binary.display())))?;
        // From here on, dropping `started` on any error stops the child.
        let mut started = Self {
            socket,
            prover: String::new(),
            connection: Mutex::new(Connection {
                client: None,
                pid: std::process::id(),
            }),
            process: Mutex::new(Some(Owned {
                _stdin: child.stdin.take(),
                child,
                owner: std::process::id(),
            })),
            closed: AtomicBool::new(false),
        };
        let deadline = Instant::now() + STARTUP_TIMEOUT;
        let exited = |started: &mut Self| -> Option<String> {
            let owned = started
                .process
                .get_mut()
                .unwrap_or_else(PoisonError::into_inner);
            let child = &mut owned.as_mut().expect("launched").child;
            match child.try_wait() {
                Ok(None) => None,
                Ok(Some(status)) => Some(status.to_string()),
                Err(error) => Some(error.to_string()),
            }
        };
        loop {
            if let Some(status) = exited(&mut started) {
                return Err(failure(format!(
                    "{} exited ({status}) before listening: {}",
                    binary.display(),
                    log_tail(&log_path)
                )));
            }
            match sidecar::Client::connect(&started.socket) {
                Ok(client) => {
                    // Another sidecar may have taken the socket while ours failed to lock it.
                    std::thread::sleep(Duration::from_millis(100));
                    if let Some(status) = exited(&mut started) {
                        return Err(failure(format!(
                            "{} exited ({status}): another sidecar serves {}",
                            binary.display(),
                            started.socket.display()
                        )));
                    }
                    client.prover().clone_into(&mut started.prover);
                    lock(&started.connection).client = Some(client);
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
    /// - Fails when the sidecar cannot be reached, or after [`Sidecar::close`].
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
    /// - Fails when the sidecar cannot be reached, or after [`Sidecar::close`].
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
        let (claims, proof) = self.call(
            |client| {
                client.aggregate(
                    &children,
                    &xmss,
                    &sphincs,
                    &[],
                    claims::OutputClaims::All,
                    LOG_INV_RATE,
                )
            },
            |reason| Error::Aggregation { reason },
        )?;
        Ok(Aggregate { claims, proof })
    }

    #[cfg(unix)]
    fn check(&self, claims: &AggregateClaims, proof: &[u8]) -> Result<bool, Error> {
        // A refused verify request, such as one too long, proves nothing.
        self.call(
            |client| client.verify(claims, proof),
            |_| Error::AggregateRejected,
        )
    }

    /// Runs one request, connecting first if the connection broke, or was opened by another
    /// process (this one was forked from it). `rejected` names a request the sidecar refused.
    #[cfg(unix)]
    fn call<T>(
        &self,
        request: impl FnOnce(&mut sidecar::Client) -> Result<T, sidecar::SidecarError>,
        rejected: impl FnOnce(String) -> Error,
    ) -> Result<T, Error> {
        let mut connection = lock(&self.connection);
        if self.closed.load(Ordering::Acquire) {
            return Err(Error::SidecarClosed);
        }
        let pid = std::process::id();
        if connection.pid != pid {
            // Dropping it closes only this process's copy of the parent's socket.
            connection.client = None;
            connection.pid = pid;
        }
        let client = match connection.client.take() {
            Some(client) => client,
            None => sidecar::Client::connect(&self.socket).map_err(sidecar_error)?,
        };
        match request(connection.client.insert(client)) {
            Ok(value) => Ok(value),
            // A refused request leaves the connection usable.
            Err(sidecar::SidecarError::Rejected(_, reason)) => Err(rejected(reason)),
            Err(error) => {
                connection.client = None;
                Err(if self.closed.load(Ordering::Acquire) {
                    Error::SidecarClosed
                } else {
                    sidecar_error(error)
                })
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

/// Makes sure the socket's directory is private, creating it if missing, and opens the sidecar's
/// log next to the socket.
#[cfg(unix)]
fn open_log(socket: &Path) -> Result<(PathBuf, std::fs::File), Error> {
    use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt};

    let failure = |reason: String| Error::Sidecar { reason };
    let directory = socket.parent().unwrap_or(Path::new("/"));
    if !directory.exists() {
        std::fs::DirBuilder::new()
            .recursive(true)
            .mode(0o700)
            .create(directory)
            .map_err(|e| failure(format!("cannot create {}: {e}", directory.display())))?;
    }
    let mode = std::fs::metadata(directory)
        .map_err(|e| failure(format!("cannot read {}: {e}", directory.display())))?
        .permissions()
        .mode();
    if mode & 0o077 != 0 {
        return Err(failure(format!(
            "{} is open to other users (mode {:o}): make it private (chmod 700), or anyone \
         able to write to it could put a fake sidecar there",
            directory.display(),
            mode & 0o777
        )));
    }
    let mut log_path = socket.as_os_str().to_owned();
    log_path.push(".log");
    let log_path = PathBuf::from(log_path);
    let log = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .mode(0o600)
        .open(&log_path)
        .map_err(|e| failure(format!("cannot open {}: {e}", log_path.display())))?;
    Ok((log_path, log))
}

/// `path` made absolute, so a reconnection after the process changes directory finds the same
/// socket.
#[cfg(unix)]
fn absolute(path: &Path, what: &str) -> Result<PathBuf, Error> {
    if path.as_os_str().is_empty() {
        return Err(Error::Sidecar {
            reason: format!("the {what} path is empty"),
        });
    }
    std::path::absolute(path).map_err(|e| Error::Sidecar {
        reason: format!("cannot resolve {}: {e}", path.display()),
    })
}

/// The end of a sidecar's log, to quote in an error.
#[cfg(unix)]
fn log_tail(path: &Path) -> String {
    let log = std::fs::read(path).unwrap_or_default();
    let log = String::from_utf8_lossy(&log[log.len().saturating_sub(2000)..]);
    log.trim().to_owned()
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
